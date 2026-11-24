(defpackage #:logic-protocol
  (:use #:cl)
  (:nicknames #:stack-logic)
  (:export
   ;; terms (terms.lisp)
   #:logic-variable-p #:logic-constant-p #:logic-term-p
   #:logic-atom-p #:ground-atom-p #:atom-relation #:atom-args
   #:atom-variables #:substitute-bindings #:builtin-literal-p
   #:term< #:fact< #:sort-facts
   ;; rules (rules.lisp)
   #:rule #:parse-rule #:rule-head #:rule-body #:rule-kind
   #:rule-choice-bounds #:rule-name #:rule-properties #:rule-form
   #:rule-weight #:rule-level #:rule-terms
   #:rule-head-atoms #:rule-unsafe-variables #:stratify
   ;; model (model.lisp)
   #:delta #:make-delta #:delta-added #:delta-removed #:delta-empty-p #:delta-relations
   #:proof #:proof-fact #:proof-rule #:proof-premises #:proof-negated #:proof-builtins
   #:proof-bindings #:proof-base-p #:proof-height #:proof-base-facts
   #:why-not #:why-not-fact #:why-not-reasons
   #:why-not-reason #:reason-rule #:reason-literal #:reason-index
   ;; budgets (budget.lisp)
   #:logic-budget #:make-budget #:budget-steps #:budget-seconds #:*logic-budget*
   #:budget-meter #:make-budget-meter #:budget-meter-budget #:budget-meter-operation
   #:budget-meter-steps #:budget-meter-partial-function #:charge-budget
   ;; conditions (conditions.lisp)
   #:logic-error #:logic-error-program
   #:logic-syntax-error #:logic-error-form #:logic-error-reason
   #:logic-unsafe-rule #:logic-error-rule #:logic-error-variables
   #:logic-unstratifiable #:logic-error-cycle
   #:logic-unsupported-rule #:logic-error-feature #:logic-error-backend
   #:logic-budget-exceeded #:logic-error-budget #:logic-error-steps
   #:logic-error-operation #:logic-error-partial
   #:logic-no-backend
   ;; restarts (conditions.lisp); CONTINUE and USE-VALUE are CL's
   #:drop-rule #:use-backend
   ;; backends (backend.lisp)
   #:logic-backend #:*logic-backend* #:backend-name #:backend-features
   #:backend-make-state #:backend-add-rules #:backend-update #:backend-query
   #:backend-explain #:backend-tick #:backend-facts #:backend-base-facts
   ;; programs (program.lisp)
   #:program #:make-program #:program-backend #:program-state #:program-rules #:program-time
   #:add-rule #:add-rules #:assert-fact #:retract-fact #:update
   #:query #:holds-p #:explain #:tick #:program-facts #:program-base-facts
   ;; weak constraints (weak.lisp)
   #:weak-instances #:weak-cost))
