(in-package #:logic-protocol)

;;; Conditions (CLHS 9). Root LOGIC-ERROR. Backends signal these types; they
;;; never define a parallel tree.
;;;
;;; Restarts, and who establishes them:
;;;
;;;   DROP-RULE    ADD-RULE / ADD-RULES, around each rule, for LOGIC-SYNTAX-ERROR,
;;;                LOGIC-UNSAFE-RULE, LOGIC-UNSTRATIFIABLE and
;;;                LOGIC-UNSUPPORTED-RULE: leave that rule out and go on with
;;;                the rest of the list.
;;;   USE-BACKEND  (backend) ADD-RULE / ADD-RULES for LOGIC-UNSTRATIFIABLE and
;;;                LOGIC-UNSUPPORTED-RULE: move the program to BACKEND (its
;;;                rules and base facts are re-added there), then retry the
;;;                rule. MAKE-PROGRAM for LOGIC-NO-BACKEND: use BACKEND.
;;;   CONTINUE     CHARGE-BUDGET, at the signal point, for LOGIC-BUDGET-EXCEEDED:
;;;                raise the limit once (one more full allowance of the
;;;                original budget) and keep computing.
;;;   USE-VALUE    (value) every budgeted front function (ADD-RULE(S), UPDATE,
;;;                ASSERT-FACT, RETRACT-FACT, QUERY, HOLDS-P, TICK), for
;;;                LOGIC-BUDGET-EXCEEDED: abandon the operation, leave the
;;;                program exactly as it was before the call, and return VALUE
;;;                from the front function. LOGIC-ERROR-PARTIAL is a ready
;;;                value for queries (the answers found so far).

(define-condition logic-error (error)
  ((program :initarg :program :initform nil :reader logic-error-program))
  (:report (lambda (c s)
             (declare (ignore c))
             (format s "Logic error"))))

(define-condition logic-syntax-error (logic-error)
  ((form :initarg :form :initform nil :reader logic-error-form)
   (reason :initarg :reason :initform "" :reader logic-error-reason))
  (:report (lambda (c s)
             (format s "Malformed logic form ~S: ~A"
                     (logic-error-form c) (logic-error-reason c)))))

(define-condition logic-unsafe-rule (logic-error)
  ((rule :initarg :rule :initform nil :reader logic-error-rule
         :documentation "The RULE, or NIL when FORM is a query pattern.")
   (form :initarg :form :initform nil :reader logic-error-form)
   (variables :initarg :variables :initform nil :reader logic-error-variables
              :documentation "The unbound variables, in first-occurrence order."))
  (:report (lambda (c s)
             (format s "Unsafe (not range-restricted) ~:[pattern~;rule~] ~S: ~{~S~^, ~} not bound by a positive literal"
                     (logic-error-rule c) (logic-error-form c) (logic-error-variables c)))))

(define-condition logic-unstratifiable (logic-error)
  ((rule :initarg :rule :initform nil :reader logic-error-rule)
   (cycle :initarg :cycle :initform nil :reader logic-error-cycle
          :documentation "Relations of the strongly connected component that holds
the negative edge, sorted by TERM<."))
  (:report (lambda (c s)
             (format s "Rule ~S closes a cycle through negation over ~{~S~^, ~}"
                     (and (logic-error-rule c) (rule-form (logic-error-rule c)))
                     (logic-error-cycle c)))))

(define-condition logic-unsupported-rule (logic-error)
  ((rule :initarg :rule :initform nil :reader logic-error-rule)
   (feature :initarg :feature :initform nil :reader logic-error-feature
            :documentation "The missing backend feature keyword, e.g. :CHOICE.")
   (backend :initarg :backend :initform nil :reader logic-error-backend))
  (:report (lambda (c s)
             (format s "Backend ~S lacks ~S, needed by rule ~S"
                     (logic-error-backend c) (logic-error-feature c)
                     (and (logic-error-rule c) (rule-form (logic-error-rule c)))))))

(define-condition logic-budget-exceeded (logic-error)
  ((budget :initarg :budget :initform nil :reader logic-error-budget)
   (steps :initarg :steps :initform 0 :reader logic-error-steps)
   (operation :initarg :operation :initform nil :reader logic-error-operation
              :documentation ":ADD-RULES, :UPDATE, :QUERY or :TICK.")
   (partial :initarg :partial :initform nil :reader logic-error-partial
            :documentation "For :QUERY, the bindings found so far, sorted as QUERY sorts
them. NIL otherwise."))
  (:report (lambda (c s)
             (format s "Logic budget ~S exceeded after ~D steps in ~S"
                     (logic-error-budget c) (logic-error-steps c) (logic-error-operation c)))))

(define-condition logic-no-backend (logic-error)
  ()
  (:report (lambda (c s)
             (declare (ignore c))
             (format s "No logic backend: bind *LOGIC-BACKEND* or pass :BACKEND (load logic-backend-datalog for the default)"))))

;;; Restart functions, in the style of CL:CONTINUE: invoke the restart when it
;;; is active (for CONDITION, if given), else return NIL.

(defun drop-rule (&optional condition)
  "Invoke the DROP-RULE restart: leave the offending rule out."
  (let ((r (find-restart 'drop-rule condition)))
    (when r (invoke-restart r))))

(defun use-backend (backend &optional condition)
  "Invoke the USE-BACKEND restart with BACKEND."
  (let ((r (find-restart 'use-backend condition)))
    (when r (invoke-restart r backend))))
