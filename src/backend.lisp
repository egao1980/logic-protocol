(in-package #:logic-protocol)

;;; Backends. The usual cl-stack shape: *LOGIC-BACKEND* plus a :BACKEND
;;; argument to MAKE-PROGRAM. A backend is a stateless object; the state of
;;; one program is an opaque object made by BACKEND-MAKE-STATE and held by
;;; the PROGRAM. Callers use the front functions (program.lisp), never these
;;; GFs. The protocol does all of the following before a backend GF runs, so
;;; backends do not:
;;;
;;; - parse, safety-check and (unless the backend has
;;;   :UNSTRATIFIED-NEGATION) stratification-check rules;
;;; - check rule kinds against BACKEND-FEATURES;
;;; - validate facts (ground atoms) and patterns, and drop duplicates;
;;; - handle :ASSUME (as an UPDATE, the call, and the reverse UPDATE);
;;; - sort and deduplicate everything returned to the caller, and apply
;;;   :LIMIT;
;;; - establish USE-VALUE for budgets.
;;;
;;; Transactions: when a mutating GF (BACKEND-ADD-RULES, BACKEND-UPDATE,
;;; BACKEND-TICK) exits non-locally (a USE-VALUE for a budget, any unwind),
;;; the state must be as it was before the call.
;;;
;;; Feature keywords (BACKEND-FEATURES):
;;;   :STRATIFIED-NEGATION   (not ATOM) in stratified programs
;;;   :UNSTRATIFIED-NEGATION any negation (stable models; ASP). The protocol
;;;                          then skips the stratification check
;;;   :TIME-STEP             :NEXT rules and TICK
;;;   :CHOICE, :CONSTRAINT   ASP rule kinds (L5)
;;;   :INCREMENTAL           UPDATE costs in proportion to the change, not
;;;                          to the whole model (informational)

(defclass logic-backend () ()
  (:documentation "Base class of logic backends."))

(defvar *logic-backend* nil
  "The backend MAKE-PROGRAM uses when no :BACKEND is given. Loading
logic-backend-datalog sets it when it is NIL.")

(defgeneric backend-name (backend)
  (:documentation "A keyword naming BACKEND, e.g. :DATALOG."))

(defgeneric backend-features (backend)
  (:documentation "The feature keywords BACKEND supports (see above).")
  (:method ((backend logic-backend)) '()))

(defgeneric backend-make-state (backend)
  (:documentation "A fresh, empty program state: no rules, no facts."))

(defgeneric backend-add-rules (backend state rules meter)
  (:documentation "Add RULES (checked RULE objects, in order) to STATE and
bring the model up to date. Returns a DELTA of the model change."))

(defgeneric backend-update (backend state assert retract meter)
  (:documentation "Remove the base facts RETRACT (facts that are not base facts
are ignored), then add the base facts ASSERT (already-base facts are
ignored), and bring the model up to date. Both are lists of distinct facts;
a fact may be in both, and then it ends up a base fact. Returns a DELTA of
the model change."))

(defgeneric backend-query (backend state pattern meter)
  (:documentation "The solutions of PATTERN (a list of body literals, already
checked safe) over the model of STATE: a list of binding alists, one entry
per variable of PATTERN. Any order; duplicates allowed. While working, set
(BUDGET-METER-PARTIAL-FUNCTION METER) so a budget condition can report the
answers found so far."))

(defgeneric backend-explain (backend state fact)
  (:documentation "A PROOF of FACT when it is in the model, else a WHY-NOT
(model.lisp has the exact choice of proof and of failing literals)."))

(defgeneric backend-tick (backend state meter)
  (:documentation "Advance one time step (Dedalus). Let M be the model at t.
The base facts at t+1 are exactly the head atoms of the :NEXT rules whose
bodies hold in M (all of them, read against M, not against facts made at
t+1); every base fact of t that no :NEXT rule carries over is gone. Then the
model at t+1 is computed. Returns the DELTA from M to the new model."))

(defgeneric backend-facts (backend state relation)
  (:documentation "The facts in the model of STATE, of RELATION only unless
RELATION is NIL. Any order."))

(defgeneric backend-base-facts (backend state)
  (:documentation "The base facts of STATE. Any order."))
