(in-package #:logic-protocol)

;;; Programs and the front functions. A PROGRAM is a backend, its opaque
;;; state, the accepted rules in order, and the time step. It is not
;;; thread-safe: callers serialize access to one program.
;;;
;;; Order guarantees (determinism): every list a front function returns is
;;; sorted. Facts and delta lists by FACT<; query answers by their values
;;; in variable order, compared left to right with TERM<; rules in the order
;;; they were added. Results never depend on hash-table order, evaluation
;;; order or the order facts were asserted in.
;;;
;;; Facts given to UPDATE, ASSERT-FACT, RETRACT-FACT and :ASSUME must be
;;; ground atoms; anything else signals LOGIC-SYNTAX-ERROR (FORM = that
;;; datum) before the backend is called.
;;;
;;; :ASSUME (QUERY, HOLDS-P, EXPLAIN): a list of facts that hold as extra
;;; base facts for this call only. The ones that are not base facts already
;;; are asserted, the call runs, and they are retracted again (also on a
;;; non-local exit). The program is unchanged afterwards. L1 evaluates a
;;; request this way: the request's facts are the assumption.

(defclass program ()
  ((backend :initarg :backend :accessor program-backend)
   (state :initarg :state :accessor program-state)
   (rules :initform '() :accessor program-rules
          :documentation "The accepted RULE objects, in the order added.")
   (time :initform 0 :accessor program-time
         :documentation "The time step: 0, then +1 per TICK.")))

(defmethod print-object ((p program) stream)
  (print-unreadable-object (p stream :type t :identity t)
    (format stream "~S, ~D rule~:P, t=~D"
            (ignore-errors (backend-name (program-backend p)))
            (length (program-rules p)) (program-time p))))

;;; Internal helpers

(defmacro with-use-value (&body body)
  "Run BODY with the USE-VALUE restart every budgeted front function offers
for LOGIC-BUDGET-EXCEEDED: abandon the call (backend GFs are transactional
and nothing is written to the program before they return) and return VALUE."
  `(restart-case (progn ,@body)
     (use-value (value)
       :report "Abandon the operation, leave the program as it was, and return VALUE."
       :test (lambda (c) (or (null c) (typep c 'logic-budget-exceeded)))
       :interactive (lambda ()
                      (format *query-io* "Value to return: ")
                      (force-output *query-io*)
                      (list (read *query-io*)))
       value)))

(defun %meter (budget operation program &optional variables)
  (let ((meter (make-budget-meter budget operation)))
    (setf (%meter-program meter) program
          (%meter-variables meter) variables)
    meter))

(defun %sorted-delta (delta)
  (make-delta :added (sort-facts (delta-added delta))
              :removed (sort-facts (delta-removed delta))))

(defun %check-facts (program facts)
  "Signal LOGIC-SYNTAX-ERROR unless FACTS is a list of ground atoms; return
them without duplicates."
  (unless (and (listp facts) (proper-list-p facts))
    (error 'logic-syntax-error :form facts :reason "expected a list of facts" :program program))
  (dolist (f facts)
    (unless (ground-atom-p f)
      (error 'logic-syntax-error :form f :reason "a fact is a ground atom" :program program)))
  (%dedupe facts))

(defun %rule-feature (backend rule)
  "The feature BACKEND lacks for RULE, or NIL. The kind's feature is checked
first (:WEAK needs :WEAK-CONSTRAINTS), then negation."
  (let ((features (backend-features backend)))
    (flet ((lacks (f) (not (member f features))))
      (or (ecase (rule-kind rule)
            (:normal nil)
            (:next (and (lacks :time-step) :time-step))
            (:choice (and (lacks :choice) :choice))
            (:constraint (and (lacks :constraint) :constraint))
            (:weak (and (lacks :weak-constraints) :weak-constraints)))
          (and (some #'not-literal-p (rule-body rule))
               (lacks :stratified-negation)
               (lacks :unstratified-negation)
               :stratified-negation)))))

(defun %check-rule (program backend item earlier)
  "Run ADD-RULES' checks on ITEM (a form or a RULE) in order; return the RULE.
EARLIER is the rules it is stratified with."
  (let ((rule (if (typep item 'rule) item (%parse-rule item nil nil program))))
    (let ((feature (%rule-feature backend rule)))
      (when feature
        (error 'logic-unsupported-rule :rule rule :feature feature :backend backend
                                       :program program)))
    (let ((unsafe (rule-unsafe-variables rule)))
      (when unsafe
        (error 'logic-unsafe-rule :rule rule :form (rule-form rule) :variables unsafe
                                  :program program)))
    (unless (member :unstratified-negation (backend-features backend))
      (multiple-value-bind (strata bad cycle) (%strata (append earlier (list rule)))
        (declare (ignore strata))
        (when bad
          (error 'logic-unstratifiable :rule rule :cycle cycle :program program))))
    rule))

(defun %migrate (program backend meter)
  "A state on BACKEND holding PROGRAM's committed rules and base facts.
Returns it; PROGRAM itself is not changed."
  (let ((state (backend-make-state backend))
        (base (backend-base-facts (program-backend program) (program-state program))))
    (when (program-rules program)
      (backend-add-rules backend state (program-rules program) meter))
    (when base
      (backend-update backend state (%dedupe base) '() meter))
    state))

(defun %pattern-body (program pattern)
  "PATTERN as a list of body literals; LOGIC-SYNTAX-ERROR when malformed,
LOGIC-UNSAFE-RULE when unsafe."
  (let ((body (cond ((body-literal-p pattern) (list pattern))
                    ((and (consp pattern) (proper-list-p pattern)
                          (named-p (car pattern) "AND")
                          (cdr pattern)
                          (every #'body-literal-p (cdr pattern)))
                     (copy-list (cdr pattern)))
                    (t (error 'logic-syntax-error
                              :form pattern :program program
                              :reason "a pattern is an atom, a built-in, (not …) or (and LIT...)")))))
    (let ((unsafe (rule-unsafe-variables body)))
      (when unsafe
        (error 'logic-unsafe-rule :rule nil :form pattern :variables unsafe :program program)))
    body))

(defun %call-with-assumptions (program facts meter thunk)
  "Call THUNK with FACTS (checked, distinct) holding as extra base facts;
withdraw them afterwards, also on a non-local exit."
  (if (null facts)
      (funcall thunk)
      (let* ((backend (program-backend program))
             (state (program-state program))
             (base (let ((h (make-hash-table :test 'equal)))
                     (dolist (f (backend-base-facts backend state) h)
                       (setf (gethash f h) t))))
             (new (remove-if (lambda (f) (gethash f base)) facts))
             (asserted nil))
        (if (null new)
            (funcall thunk)
            (unwind-protect
                 (progn
                   (backend-update backend state new '() meter)
                   (setf asserted t)
                   (funcall thunk))
              ;; The withdrawal runs on its own meter: the call's budget may
              ;; be the reason we are unwinding.
              (when asserted
                (backend-update backend state '() new
                                (%meter :unlimited :update program))))))))

(defun %query (program pattern limit budget assume)
  (let* ((body (%pattern-body program pattern))
         (assume (%check-facts program assume))
         (variables (atom-variables body))
         (meter (%meter budget :query program variables)))
    (%call-with-assumptions
     program assume meter
     (lambda ()
       (let ((answers (normalize-answers
                       (backend-query (program-backend program) (program-state program)
                                      body meter)
                       variables)))
         (if limit
             (subseq answers 0 (min limit (length answers)))
             answers))))))

;;; Front functions

(defun make-program (&key (backend *logic-backend*) rules facts budget)
  "A new program on BACKEND, then (ADD-RULES RULES) and (UPDATE :ASSERT FACTS)
under BUDGET. With no backend, signal LOGIC-NO-BACKEND with a USE-BACKEND
restart that takes the backend to use."
  (let* ((backend (or backend
                      (restart-case (error 'logic-no-backend)
                        (use-backend (backend)
                          :report "Use another backend for the new program."
                          :interactive (lambda ()
                                         (format *query-io* "Backend (evaluated): ")
                                         (force-output *query-io*)
                                         (list (eval (read *query-io*))))
                          backend))))
         (program (make-instance 'program :backend backend
                                          :state (backend-make-state backend))))
    (when rules (add-rules program rules :budget budget))
    (when facts (update program :assert facts :budget budget))
    program))

(defun add-rules (program rules &key budget)
  "Add RULES (surface forms or RULE objects) in order. For each rule:
PARSE-RULE when it is a form (LOGIC-SYNTAX-ERROR); a rule kind the backend
lacks (:NEXT needs :TIME-STEP, :CHOICE and :CONSTRAINT their own keyword,
:WEAK :WEAK-CONSTRAINTS, a (not …) literal :STRATIFIED-NEGATION or
:UNSTRATIFIED-NEGATION; the kind is checked before negation) signals
LOGIC-UNSUPPORTED-RULE; RULE-UNSAFE-VARIABLES non-NIL signals
LOGIC-UNSAFE-RULE; then, unless the backend has :UNSTRATIFIED-NEGATION,
STRATIFY over the accepted rules plus this one, which may signal
LOGIC-UNSTRATIFIABLE. Checks run in that order. Restarts per rule:
DROP-RULE for all four, USE-BACKEND for LOGIC-UNSUPPORTED-RULE and
LOGIC-UNSTRATIFIABLE (see conditions.lisp). The conditions name the rule
being added (and PROGRAM), also when STRATIFY would blame an earlier rule of
the same cycle. Rules accepted earlier in the same call count for the
stratification check and, after a USE-BACKEND, go to the new backend. The
accepted rules then go to BACKEND-ADD-RULES in one call (no call when none
was accepted), and only then join PROGRAM-RULES. Returns the DELTA."
  (let ((meter (%meter budget :add-rules program)))
    (with-use-value
      (let ((backend (program-backend program))
            (state (program-state program))
            (accepted '()))             ; newest first
        (dolist (item rules)
          (loop
            (let ((outcome
                    (restart-case
                        (%check-rule program backend item
                                     (append (program-rules program) (reverse accepted)))
                      (drop-rule ()
                        :report "Leave this rule out and go on with the rest."
                        :drop)
                      (use-backend (new-backend)
                        :report "Move the program to another backend and retry the rule."
                        :test (lambda (c)
                                (or (null c)
                                    (typep c '(or logic-unstratifiable logic-unsupported-rule))))
                        :interactive (lambda ()
                                       (format *query-io* "Backend (evaluated): ")
                                       (force-output *query-io*)
                                       (list (eval (read *query-io*))))
                        (setf state (%migrate program new-backend meter)
                              backend new-backend)
                        :retry))))
              (case outcome
                (:drop (return))
                (:retry)
                (t (push outcome accepted) (return))))))
        (let* ((new (reverse accepted))
               (delta (if new
                          (backend-add-rules backend state new meter)
                          (make-delta))))
          (setf (program-backend program) backend
                (program-state program) state
                (program-rules program) (append (program-rules program) new))
          (%sorted-delta delta))))))

(defun add-rule (program rule &key budget)
  "(ADD-RULES PROGRAM (LIST RULE)). Returns the DELTA."
  (add-rules program (list rule) :budget budget))

(defun update (program &key assert retract budget)
  "Retract the base facts RETRACT, assert the base facts ASSERT (retractions
first: a fact in both ends up asserted), bring the model up to date
incrementally. Returns the DELTA of the model."
  (let ((assert (%check-facts program assert))
        (retract (%check-facts program retract))
        (meter (%meter budget :update program)))
    (with-use-value
      (%sorted-delta (backend-update (program-backend program) (program-state program)
                                     assert retract meter)))))

(defun assert-fact (program fact &key budget)
  "(UPDATE PROGRAM :ASSERT (LIST FACT)). Returns the DELTA."
  (update program :assert (list fact) :budget budget))

(defun retract-fact (program fact &key budget)
  "(UPDATE PROGRAM :RETRACT (LIST FACT)). Returns the DELTA."
  (update program :retract (list fact) :budget budget))

(defun query (program pattern &key limit budget assume)
  "Solutions of PATTERN: an atom, a built-in, (not …), or (and LIT...) of
those. Returns a list of binding alists ((VAR . VALUE) ...), one entry per
variable of PATTERN in first-occurrence order, without duplicates, sorted
(see the header); a ground pattern that holds gives (NIL). At most LIMIT
answers (the first ones in that order). An unsafe pattern signals
LOGIC-UNSAFE-RULE with RULE NIL and FORM PATTERN; a malformed one
LOGIC-SYNTAX-ERROR."
  (with-use-value
    (%query program pattern limit budget assume)))

(defun holds-p (program pattern &key budget assume)
  "True when PATTERN has a solution."
  (with-use-value
    (and (%query program pattern nil budget assume) t)))

(defun explain (program fact &key assume)
  "A PROOF when FACT is in the model, else a WHY-NOT (model.lisp). FACT must
be a ground atom (LOGIC-SYNTAX-ERROR)."
  (unless (ground-atom-p fact)
    (error 'logic-syntax-error :form fact :reason "EXPLAIN takes a fact (a ground atom)"
                               :program program))
  (let ((assume (%check-facts program assume)))
    (%call-with-assumptions
     program assume (%meter :unlimited :update program)
     (lambda ()
       (backend-explain (program-backend program) (program-state program) fact)))))

(defun tick (program &key budget)
  "Advance one time step (BACKEND-TICK); increments PROGRAM-TIME. Needs
:TIME-STEP (else LOGIC-UNSUPPORTED-RULE with RULE NIL). Returns the DELTA."
  (let ((backend (program-backend program)))
    (unless (member :time-step (backend-features backend))
      (error 'logic-unsupported-rule :rule nil :feature :time-step :backend backend
                                     :program program))
    (let ((meter (%meter budget :tick program)))
      (with-use-value
        (prog1 (%sorted-delta (backend-tick backend (program-state program) meter))
          (incf (program-time program)))))))

(defun program-facts (program &key relation)
  "The facts in the model, sorted; only RELATION's unless it is NIL."
  (sort-facts (backend-facts (program-backend program) (program-state program) relation)))

(defun program-base-facts (program &key relation)
  "The base facts, sorted; only RELATION's unless it is NIL."
  (sort-facts (remove-if-not (lambda (f) (or (null relation) (eq (atom-relation f) relation)))
                             (backend-base-facts (program-backend program)
                                                 (program-state program)))))
