(in-package #:logic-protocol)

;;; Weak-constraint instances (since 0.2.0). Weak rules, (rule (weak COST
;;; TERM...) :- LIT...), are parsed by PARSE-RULE (rules.lisp has the grammar
;;; and the instance semantics). A backend runs them only when it has
;;; :WEAK-CONSTRAINTS (an ASP backend, L5); the Datalog backend refuses them
;;; in ADD-RULE with LOGIC-UNSUPPORTED-RULE. Programs can still be written
;;; ASP-shaped today: keep the weak rules out of the program and ground them
;;; against its model here, on any backend, because this only queries the
;;; model. A consumer compiles the result to a SAT objective (one soft literal
;;; per instance, true when one of its groundings holds, the levels as a
;;; lexicographic objective), and the same rules move to an ASP backend later
;;; unchanged.
;;;
;;; WEAK-INSTANCES program rules &key assume budget → (values INSTANCES GROUNDINGS)
;;;
;;;   Checks, before anything is evaluated, for each element of RULES in
;;;   order (a surface form or a RULE):
;;;     1. a form is parsed as by PARSE-RULE (LOGIC-SYNTAX-ERROR);
;;;     2. a rule whose kind is not :WEAK signals LOGIC-SYNTAX-ERROR (FORM =
;;;        its RULE-FORM, a non-empty REASON);
;;;     3. RULE-UNSAFE-VARIABLES non-NIL signals LOGIC-UNSAFE-RULE (RULE, FORM
;;;        = its RULE-FORM, VARIABLES), as ADD-RULE does.
;;;   Each condition carries PROGRAM and is signalled inside a DROP-RULE
;;;   restart around that element: leave the rule out, go on with the rest.
;;;   Then ASSUME is checked as QUERY checks it (LOGIC-SYNTAX-ERROR, no
;;;   restart). When no rule is left, the result is (values NIL NIL) and the
;;;   backend is not called.
;;;
;;;   Evaluation. RULES are never added to PROGRAM, and PROGRAM's own rules
;;;   are left alone. The facts of ASSUME that are not base facts hold for the
;;;   whole call: asserted once before the first body is evaluated, withdrawn
;;;   once after the last (also on a non-local exit), exactly as QUERY's
;;;   :ASSUME. The body of each remaining rule, in RULES order, is evaluated
;;;   over the model once, as QUERY evaluates the pattern (and . BODY): one
;;;   BACKEND-QUERY call per rule, given the body list, and its answers
;;;   projected, deduplicated and sorted as QUERY sorts them (by values in the
;;;   body's first-occurrence variable order, TERM<). Each answer A, in that
;;;   order, gives
;;;     the instance   (W' L . TERMS')    W', TERMS' = RULE-WEIGHT, RULE-TERMS
;;;                                       under A; L = RULE-LEVEL
;;;     a grounding    (SUBSTITUTE-BINDINGS BODY A): every body literal, in
;;;                    body order, negations and built-ins included.
;;;   When W' is not an integer (a variable weight bound to a string or a
;;;   symbol), LOGIC-SYNTAX-ERROR is signalled with FORM = that instance,
;;;   PROGRAM, and a REASON naming the weight, inside a CONTINUE restart: skip
;;;   that answer and go on (clingo drops such an instance). Declined, it
;;;   unwinds the call like any error (ASSUME is withdrawn).
;;;
;;;   INSTANCES: the distinct instances (EQUAL), sorted by FACT<: compared
;;;   element by element with TERM<, so by weight, then level, then terms. An
;;;   instance is one set element (rules.lisp): produced by several answers,
;;;   or by several rules, it is listed once.
;;;
;;;   GROUNDINGS: a list parallel to INSTANCES. Element I is the list of the
;;;   distinct (EQUAL) groundings that produced instance I, in the order they
;;;   were produced (rules in RULES order, then answers in QUERY order). For
;;;   a SAT compile: instance I costs its weight when at least one of its
;;;   groundings holds.
;;;
;;;   Budget: one meter for the whole call, operation :QUERY, under BUDGET (a
;;;   budget designator, budget.lisp), shared by every body query and by the
;;;   assertion of ASSUME (whose withdrawal is unmetered, as in QUERY). So the
;;;   steps of all rules add up. LOGIC-BUDGET-EXCEEDED offers CONTINUE
;;;   (CHARGE-BUDGET) and USE-VALUE: abandon the call, withdraw ASSUME, and
;;;   return VALUE from WEAK-INSTANCES. Its PARTIAL is the answers found so
;;;   far of the body being evaluated, sorted as QUERY sorts them.
;;;
;;; WEAK-COST instances → ((LEVEL . SUM) ...)
;;;
;;;   INSTANCES is a list of instances (W L . TERMS) as above, possibly with
;;;   duplicates. The result has one entry per level that occurs in
;;;   INSTANCES, highest level first; SUM is the sum of the weights of the
;;;   distinct (EQUAL) instances at that level, so a duplicate counts once and
;;;   a level whose weights cancel has SUM 0. NIL for no instances. An element
;;;   that is not a list whose first two elements are integers signals
;;;   TYPE-ERROR. This is clingo's optimization vector: two costs compare
;;;   level by level from the highest, a missing level counting as 0.

(defun weak-instances (program rules &key assume budget)
  "The instances of the weak RULES (forms or RULE objects of kind :WEAK) over
the model of PROGRAM, with ASSUME holding for the call: (values INSTANCES
GROUNDINGS), INSTANCES the distinct (WEIGHT LEVEL . TERMS) lists sorted by
FACT<, GROUNDINGS for each instance the ground bodies that produced it. See
the file header for the checks, restarts and budget."
  (with-use-value
    (let* ((rules (%weak-rules program rules))     ; every check, inside DROP-RULE
           (assume (%check-facts program assume))  ; as QUERY checks it
           (meter (%meter budget :query program))) ; one meter for the call
      (if (null rules)
          (values nil nil)                         ; no backend call at all
          ;; Inside WITH-USE-VALUE, so taking USE-VALUE withdraws ASSUME.
          (%call-with-assumptions
           program assume meter
           (lambda () (%weak-ground program rules meter)))))))

(defun %weak-rule (program item)
  "ITEM (a form or a RULE) checked for WEAK-INSTANCES: parsed, of kind :WEAK,
safe. Returns the RULE."
  (let ((rule (if (typep item 'rule) item (%parse-rule item nil nil program))))
    (unless (eq (rule-kind rule) :weak)
      (error 'logic-syntax-error
             :form (rule-form rule) :program program
             :reason (format nil "a ~(~S~) rule is not a weak constraint ~
                                  (rule (weak COST TERM...) :- LIT...)"
                             (rule-kind rule))))
    (let ((unsafe (rule-unsafe-variables rule)))
      (when unsafe
        (error 'logic-unsafe-rule :rule rule :form (rule-form rule) :variables unsafe
                                  :program program)))
    rule))

(defun %weak-rules (program rules)
  "The elements of RULES that pass %WEAK-RULE, as RULE objects in order. Each
check runs inside a DROP-RULE restart that leaves that element out."
  (let ((kept '()))
    (dolist (item rules (nreverse kept))
      (let ((outcome (restart-case (%weak-rule program item)
                       (drop-rule ()
                         :report "Leave this weak rule out and go on with the rest."
                         :drop))))
        (unless (eq outcome :drop)
          (push outcome kept))))))

(defun %weak-instance (program rule answer)
  "The instance (W' L . TERMS') of RULE under the binding alist ANSWER. When
W' is not an integer, signal LOGIC-SYNTAX-ERROR (FORM = the instance) with a
CONTINUE restart; taken, it returns NIL (skip this answer)."
  (let ((instance (list* (substitute-bindings (rule-weight rule) answer)
                         (rule-level rule)
                         (substitute-bindings (rule-terms rule) answer))))
    (if (integerp (first instance))
        instance
        ;; The form is the ERROR call itself, so CONTINUE is associated with
        ;; the condition (CLHS 9.1.4.2.2).
        (restart-case
            (error 'logic-syntax-error
                   :form instance :program program
                   :reason (format nil "the weight ~S of a weak constraint instance ~
                                        is not an integer"
                                   (first instance)))
          (continue ()
            :report "Skip this instance and go on with the next answer."
            nil)))))

(defun %weak-ground (program rules meter)
  "Evaluate the body of each of RULES (checked :WEAK rules) once over
PROGRAM's model under METER, in order, and return (values INSTANCES
GROUNDINGS) as the file header defines them."
  (let ((backend (program-backend program))
        (state (program-state program))
        (order '())                                 ; distinct instances, newest first
        (groundings (make-hash-table :test 'equal)) ; instance -> groundings, newest first
        (seen (make-hash-table :test 'equal)))      ; (instance . grounding) -> T
    (dolist (rule rules)
      (let* ((body (rule-body rule))
             (variables (atom-variables body)))
        ;; PARTIAL belongs to the body being evaluated.
        (setf (%meter-variables meter) variables
              (budget-meter-partial-function meter) nil)
        (dolist (answer (normalize-answers (backend-query backend state body meter)
                                           variables))
          (let ((instance (%weak-instance program rule answer)))
            (when instance
              (let* ((grounding (substitute-bindings body answer))
                     (key (cons instance grounding)))
                (unless (nth-value 1 (gethash instance groundings))
                  (push instance order))
                (unless (gethash key seen)
                  (setf (gethash key seen) t)
                  (push grounding (gethash instance groundings)))))))))
    ;; The order comes from first appearance plus a stable sort, never from
    ;; hash-table iteration.
    (let ((instances (stable-sort (nreverse order) #'fact<)))
      (values instances
              (mapcar (lambda (i) (reverse (gethash i groundings))) instances)))))

(defun weak-cost (instances)
  "The cost of INSTANCES ((WEIGHT LEVEL . TERMS) lists): ((LEVEL . SUM) ...),
one entry per level, highest level first, each distinct instance counted
once. NIL for none."
  (let ((sums '()))                     ; ((LEVEL . SUM) ...), one entry per level
    (dolist (instance (%dedupe (mapcar (lambda (x)
                                         (check-type x (cons integer (cons integer list))
                                                     "a weak-constraint instance (WEIGHT LEVEL . TERMS)")
                                         x)
                                       instances)))
      (let ((entry (assoc (second instance) sums)))
        (if entry
            (incf (cdr entry) (first instance))
            (push (cons (second instance) (first instance)) sums))))
    (sort sums #'> :key #'car)))         ; levels are distinct: a total order
