(in-package #:logic-protocol)

;;; Rules (brief: "Rules", "Negation", "Time-step rules", locked).
;;;
;;; Surface forms, read by PARSE-RULE. RULE and :- are matched by
;;; SYMBOL-NAME, so data read into any package works (:- is the keyword
;;; named "-").
;;;
;;;   (rule HEAD)                        kind :NORMAL, empty body
;;;   (rule HEAD :- LIT...)              kind :NORMAL
;;;   (rule (next ATOM) :- LIT...)       kind :NEXT   (time-step, Dedalus)
;;;   (rule :- LIT...)                   kind :CONSTRAINT (ASP integrity
;;;                                      constraint; head NIL; at least one LIT)
;;;   (rule (choice LO HI ATOM...) :- LIT...)
;;;                                      kind :CHOICE (ASP choice rule; LO and
;;;                                      HI are integers or NIL; one ATOM or more)
;;;   (rule (weak COST TERM...) :- LIT...)
;;;                                      kind :WEAK (ASP weak constraint; head
;;;                                      NIL; at least one LIT). See below.
;;;
;;; HEAD is an atom (LOGIC-ATOM-P). A body LIT is an atom, a built-in
;;; (BUILTIN-LITERAL-P), or (not X) where X is an atom or a built-in. NEXT,
;;; CHOICE and WEAK appear only in heads (WEAK is a reserved name, so (weak …)
;;; is never an atom). Anything else signals LOGIC-SYNTAX-ERROR with FORM = the
;;; whole rule form and a REASON string. The datalog backend supports :NORMAL
;;; and :NEXT; :CONSTRAINT, :CHOICE and :WEAK are parsed so that an ASP backend
;;; (L5) fits, and ADD-RULE signals LOGIC-UNSUPPORTED-RULE on a backend that
;;; lacks them.
;;;
;;; Weak constraints (since 0.2.0). (rule (weak COST TERM...) :- LIT...) is
;;; clingo's  :~ LIT, ... . [W@L, TERM, ...]  : every instance of the body
;;; that holds costs W at priority level L, and an optimal answer minimizes
;;; the costs level by level, highest level first. The grammar:
;;;
;;;   weak-head = (weak COST TERM*)        ; WEAK by SYMBOL-NAME, any package
;;;   COST      = W | (W L)
;;;   W         = an integer | a variable  ; the weight
;;;   L         = an integer               ; the level; 0 when COST is just W
;;;   TERM      = a term (LOGIC-TERM-P)    ; constant or variable, zero or more
;;;
;;; So (weak 3 ?x) is [3@0, X], (weak (?c 2) ?x ?y) is [C@2, X, Y], (weak
;;; (-1 1)) is [-1@1]; (weak 3 ?x) and (weak (3 0) ?x) parse to the same
;;; weight, level and terms.
;;; Weights and levels may be negative. A variable weight takes its value
;;; from the body; a level is always written as an integer. Each of these
;;; signals LOGIC-SYNTAX-ERROR (FORM = the whole rule form):
;;;   - no COST: (weak);
;;;   - a W that is not an integer or a variable: a string, a symbol
;;;     constant, NIL, a float or ratio, a list;
;;;   - a (W L) that is not a proper two-element list, or whose L is not an
;;;     integer (a variable level included);
;;;   - a TERM that is not a term (a list, NIL, a float), or an improper
;;;     (weak …) list;
;;;   - an empty body: (rule (weak 1)), (rule (weak 1) :-);
;;;   - (weak …) anywhere but the head: in the body, inside NEXT or CHOICE.
;;;
;;; The parsed rule: RULE-KIND :WEAK, RULE-HEAD NIL, RULE-HEAD-ATOMS NIL,
;;; RULE-BODY the literals, RULE-WEIGHT W, RULE-LEVEL L (0 when not written),
;;; RULE-TERMS the TERMs as a list (NIL when there are none), RULE-CHOICE-
;;; BOUNDS NIL, RULE-FORM the form as given. RULE-PROPERTIES is
;;;   (:WEIGHT W :LEVEL L :TERMS TERMS . P)
;;; where P is the caller's PROPERTIES plist with every :WEIGHT, :LEVEL and
;;; :TERMS entry removed: the form is the source of truth, and parsing a weak
;;; rule's RULE-FORM again with its own RULE-PROPERTIES gives the same
;;; properties. Rules of the other kinds keep PROPERTIES exactly as given, and
;;; their RULE-WEIGHT, RULE-LEVEL and RULE-TERMS are NIL.
;;;
;;; Instances (as defined here, and as WEAK-INSTANCES computes them against a
;;; model): an answer A of the body gives the instance (W' L . TERMS'), W'
;;; and TERMS' being W and TERMS under A. Instances are a set, as in clingo:
;;; the same (W L . TERMS) from two answers, or from two weak rules, is one
;;; instance and costs W once. Add a term to tell such cases apart.
;;;
;;; Safety (range restriction, RULE-UNSAFE-VARIABLES): start with the
;;; variables of the positive body atoms; then, repeatedly, for (= A B) in the
;;; body where one side is a constant or bound, the other side becomes bound.
;;; Every variable of the head (all head atoms of a choice rule, the inner
;;; atom of NEXT, the weight and the terms of a weak head), of a negated
;;; literal, and of a built-in other than = must end up bound, and both sides
;;; of every = too. The unbound ones, in first-occurrence order over the whole
;;; rule form, are the unsafe variables. So a weak rule is safe exactly when
;;; every variable of its weight and terms occurs in a positive body atom (or
;;; is bound through =), like any head variable: (rule (weak ?w ?x) :- (p ?x))
;;; is unsafe with (?W), and (rule (weak ?w ?x) :- (cost ?x ?w)) is safe.
;;;
;;; Stratification (STRATIFY): the dependency graph has an edge from each
;;; body relation to each head relation of the same rule, negative when the
;;; body literal is (not ATOM). Built-ins add no edges. Rules of kind :NEXT
;;; add no edges (time separates them: the body is read at t, the head is a
;;; fact at t+1). :CONSTRAINT and :WEAK rules have no head and add no edges
;;; (the relations of their body atoms are still nodes), so negation in a
;;; weak rule's body never makes a program unstratifiable. A negative edge
;;; inside a strongly connected component makes the program unstratifiable.

(defclass rule ()
  ((head :initarg :head :reader rule-head
         :documentation "An atom (:NORMAL), the inner atom (:NEXT), NIL
(:CONSTRAINT, :WEAK) or the list of atoms (:CHOICE).")
   (body :initarg :body :initform '() :reader rule-body
         :documentation "The literals as written (plain lists).")
   (kind :initarg :kind :initform :normal :reader rule-kind
         :documentation ":NORMAL, :NEXT, :CONSTRAINT, :CHOICE or :WEAK.")
   (choice-bounds :initarg :choice-bounds :initform nil :reader rule-choice-bounds
                  :documentation "(LO . HI) for :CHOICE, else NIL.")
   (weight :initarg :weight :initform nil :reader rule-weight
           :documentation "For :WEAK, the weight W of (weak COST TERM...): an
integer or a variable. NIL for the other kinds.")
   (level :initarg :level :initform nil :reader rule-level
          :documentation "For :WEAK, the level L of (weak (W L) TERM...), an
integer; 0 when COST is just W. NIL for the other kinds.")
   (terms :initarg :terms :initform nil :reader rule-terms
          :documentation "For :WEAK, the TERMs of (weak COST TERM...) as a list,
possibly empty. NIL for the other kinds.")
   (name :initarg :name :initform nil :reader rule-name)
   (properties :initarg :properties :initform '() :reader rule-properties
               :documentation "A plist the caller owns (L1 keeps the effect,
feedback and source rule here). The protocol never reads it. For a :WEAK
rule it starts with :WEIGHT W :LEVEL L :TERMS TERMS, followed by the
caller's plist without those keys (see the file header).")
   (form :initarg :form :reader rule-form
         :documentation "The surface form PARSE-RULE read.")))

(defmethod print-object ((r rule) stream)
  (print-unreadable-object (r stream :type t)
    (format stream "~S" (rule-form r))))

(defun rule-head-atoms (rule)
  "The atoms RULE derives: one for :NORMAL and :NEXT, the choice atoms for
:CHOICE, none for :CONSTRAINT and :WEAK."
  (ecase (rule-kind rule)
    ((:normal :next) (list (rule-head rule)))
    (:choice (rule-head rule))
    (:constraint '())
    (:weak (%weak-pending 'rule-head-atoms))))

(defun not-literal-p (x)
  "Is X a list headed by NOT (by symbol name)?"
  (and (consp x) (named-p (car x) "NOT")))

(defun body-literal-p (x)
  "Is X a body literal: an atom, a built-in, or (not X) of one of those?"
  (and (consp x)
       (proper-list-p x)
       (or (logic-atom-p x)
           (builtin-literal-p x)
           (and (not-literal-p x)
                (= (length x) 2)
                (let ((inner (second x)))
                  (and (consp inner)
                       (proper-list-p inner)
                       (or (logic-atom-p inner) (builtin-literal-p inner))))))))

(defun %parse-rule (form name properties program)
  (flet ((fail (reason)
           (error 'logic-syntax-error :form form :reason reason :program program)))
    (unless (and (consp form) (proper-list-p form) (named-p (car form) "RULE"))
      (fail "not a (rule …) form"))
    (let* ((parts (cdr form))
           (pos (position-if (lambda (x) (named-p x "-")) parts))
           head-form body)
      (when (null parts) (fail "a rule needs a head or :-"))
      (cond ((eql pos 0)
             (setf head-form nil body (cdr parts))
             (when (null body) (fail "a constraint needs at least one body literal")))
            ((eql pos 1)
             (setf head-form (car parts) body (cddr parts)))
            ((null pos)
             (unless (null (cdr parts)) (fail "body literals must follow :-"))
             (setf head-form (car parts) body '()))
            (t (fail "a rule has exactly one head before :-")))
      (dolist (lit body)
        (unless (body-literal-p lit)
          (fail (format nil "~S is not a body literal (atom, built-in or (not …))" lit))))
      (multiple-value-bind (kind head bounds)
          (cond ((null pos) (if (logic-atom-p head-form)
                                (values :normal head-form nil)
                                (values nil nil nil)))
                ((null head-form) (values :constraint nil nil))
                ((logic-atom-p head-form) (values :normal head-form nil))
                (t (values nil nil nil)))
        (unless kind
          (cond ((and (consp head-form) (proper-list-p head-form)
                      (named-p (car head-form) "NEXT"))
                 (unless (and (= (length head-form) 2) (logic-atom-p (second head-form)))
                   (fail "(next ATOM) takes exactly one atom"))
                 (setf kind :next head (second head-form)))
                ((and (consp head-form) (proper-list-p head-form)
                      (named-p (car head-form) "CHOICE"))
                 (destructuring-bind (&optional lo hi &rest atoms) (cdr head-form)
                   (unless (and (typep lo '(or null integer)) (typep hi '(or null integer)))
                     (fail "choice bounds must be integers or NIL"))
                   (unless (and atoms (every #'logic-atom-p atoms))
                     (fail "(choice LO HI ATOM...) needs at least one atom"))
                   (setf kind :choice head atoms bounds (cons lo hi))))
                ((and (consp head-form) (named-p (car head-form) "WEAK"))
                 (return-from %parse-rule
                   (%parse-weak-rule form head-form body name properties program)))
                (t (fail (format nil "~S is not a rule head" head-form)))))
        (make-instance 'rule :head head :body body :kind kind :choice-bounds bounds
                             :name name :properties properties :form form)))))

(defun %parse-weak-rule (form head-form body name properties program)
  "The :WEAK rule of FORM, whose head HEAD-FORM is a list headed by WEAK and
whose BODY literals %PARSE-RULE has already checked: validate HEAD-FORM and
BODY by the weak-constraint grammar (file header), then make the RULE with
kind :WEAK, head NIL, the weight, level and terms, NAME, the properties the
header defines from PROPERTIES, and FORM. Every violation signals
LOGIC-SYNTAX-ERROR with FORM, a non-empty REASON string and PROGRAM."
  (declare (ignorable form head-form body name properties program))
  (%weak-pending '%parse-weak-rule))

(defun parse-rule (form &key name properties)
  "Parse the surface FORM (see the file header) into a RULE with NAME and
PROPERTIES (for a :WEAK rule, RULE-PROPERTIES adds :WEIGHT, :LEVEL and
:TERMS in front). Signals LOGIC-SYNTAX-ERROR. Does not check safety."
  (%parse-rule form name properties nil))

(defmacro rule (&rest parts)
  "(rule HEAD :- LIT...) evaluates to the parsed RULE; the parts are not
evaluated."
  `(parse-rule '(rule ,@parts)))

(defun rule-unsafe-variables (rule-or-body)
  "The unsafe variables of a RULE (see the file header), or of a list of body
literals read as a headless query. NIL when safe."
  (multiple-value-bind (body form)
      (if (typep rule-or-body 'rule)
          (values (rule-body rule-or-body) (rule-form rule-or-body))
          (values rule-or-body rule-or-body))
    (let ((bound (bound-variables body)))
      (remove-if (lambda (v) (member v bound)) (atom-variables form)))))

(defun bound-variables (body)
  "The variables BODY binds: those of its positive atoms, then, to a
fixpoint, the other side of each un-negated (= A B) whose one side is a
constant or bound."
  (let ((bound (atom-variables (remove-if-not #'logic-atom-p body)))
        (equalities (remove-if-not (lambda (l) (and (builtin-literal-p l) (named-p (car l) "=")))
                                   body)))
    (flet ((known-p (x) (or (logic-constant-p x) (member x bound))))
      (loop
        (let ((changed nil))
          (dolist (e equalities)
            (destructuring-bind (a b) (cdr e)
              (cond ((and (logic-variable-p b) (not (member b bound)) (known-p a))
                     (push b bound) (setf changed t))
                    ((and (logic-variable-p a) (not (member a bound)) (known-p b))
                     (push a bound) (setf changed t)))))
          (unless changed (return bound)))))))

(defun stratify (rules)
  "Strata of RULES (a list of RULE objects): a list of lists of relation
symbols, lowest stratum first, each sorted by TERM<. Every relation that
occurs in a head or body atom appears exactly once. A relation's stratum is
the least S such that, over every edge Q -> R into it, S >= stratum(Q) for a
positive edge and S > stratum(Q) for a negative one; relations with no
incoming edge are in stratum 0. Empty strata are omitted, so the result has
no empty list.

Signals LOGIC-UNSTRATIFIABLE when a negative edge lies inside a strongly
connected component: RULE is the first rule in RULES that has such an edge,
CYCLE the relations of that component sorted by TERM<."
  (multiple-value-bind (strata bad-rule cycle) (%strata rules)
    (when bad-rule
      (error 'logic-unstratifiable :rule bad-rule :cycle cycle))
    strata))

(defun %literal-atom (lit)
  "The atom of a body literal and whether it is negated; NIL for built-ins."
  (cond ((logic-atom-p lit) (values lit nil))
        ((and (not-literal-p lit) (logic-atom-p (second lit))) (values (second lit) t))
        (t (values nil nil))))

(defun %strata (rules)
  "STRATIFY without signalling: (values STRATA BAD-RULE CYCLE). BAD-RULE is
NIL when RULES are stratifiable."
  (let ((nodes '())
        (edges '()))                    ; (FROM TO NEGATIVE RULE)
    (flet ((node (r) (pushnew r nodes)))
      (dolist (rule rules)
        (let ((heads (mapcar #'atom-relation (rule-head-atoms rule)))
              (edge-p (member (rule-kind rule) '(:normal :choice))))
          (mapc #'node heads)
          (dolist (lit (rule-body rule))
            (multiple-value-bind (atom negative) (%literal-atom lit)
              (when atom
                (node (atom-relation atom))
                (when edge-p
                  (dolist (h heads)
                    (push (list (atom-relation atom) h negative rule) edges)))))))))
    (setf nodes (sort nodes #'term<)
          edges (nreverse edges))
    (let ((succ (make-hash-table :test 'eq))
          (index (make-hash-table :test 'eq))
          (low (make-hash-table :test 'eq))
          (on-stack (make-hash-table :test 'eq))
          (component (make-hash-table :test 'eq))
          (stack '())
          (counter 0)
          (components '()))             ; Tarjan emits sinks first
      (dolist (e edges) (pushnew (second e) (gethash (first e) succ)))
      (labels ((visit (v)
                 (setf (gethash v index) counter (gethash v low) counter)
                 (incf counter)
                 (push v stack)
                 (setf (gethash v on-stack) t)
                 (dolist (w (gethash v succ))
                   (cond ((not (gethash w index))
                          (visit w)
                          (setf (gethash v low) (min (gethash v low) (gethash w low))))
                         ((gethash w on-stack)
                          (setf (gethash v low) (min (gethash v low) (gethash w index))))))
                 (when (= (gethash v low) (gethash v index))
                   (let ((members '()))
                     (loop (let ((w (pop stack)))
                             (setf (gethash w on-stack) nil)
                             (push w members)
                             (when (eq w v) (return))))
                     (let ((id (length components)))
                       (dolist (w members) (setf (gethash w component) id))
                       (push members components))))))
        (dolist (v nodes)
          (unless (gethash v index) (visit v))))
      ;; Negative edge inside a component: the first such rule in RULES.
      (dolist (rule rules)
        (dolist (e edges)
          (when (and (eq (fourth e) rule) (third e)
                     (eql (gethash (first e) component) (gethash (second e) component)))
            (return-from %strata
              (values nil rule
                      (sort (copy-list (nth (- (length components) 1 (gethash (first e) component))
                                            components))
                            #'term<))))))
      ;; Strata: components in topological order (reverse of emission).
      (let ((level (make-hash-table :test 'eq)) ; component id -> stratum
            (incoming (make-hash-table :test 'eq)))
        (dolist (e edges)
          (push e (gethash (gethash (second e) component) incoming)))
        ;; An edge A -> B puts B's component before A's in Tarjan's output, so
        ;; a component's predecessors have larger ids.
        (loop for id from (1- (length components)) downto 0
              do (let ((m 0))
                   (dolist (e (gethash id incoming))
                     (let ((from (gethash (first e) component)))
                       (unless (= from id)
                         (setf m (max m (+ (gethash from level) (if (third e) 1 0)))))))
                   (setf (gethash id level) m)))
        (let* ((count (let ((m -1))
                        (dolist (v nodes (1+ m))
                          (setf m (max m (gethash (gethash v component) level))))))
               (buckets (make-array count :initial-element '())))
          (dolist (v (reverse nodes))
            (push v (aref buckets (gethash (gethash v component) level))))
          (values (remove nil (coerce buckets 'list)) nil nil))))))
