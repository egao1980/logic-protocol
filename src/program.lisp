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

(defun make-program (&key (backend *logic-backend*) rules facts budget)
  "A new program on BACKEND, then (ADD-RULES RULES) and (UPDATE :ASSERT FACTS)
under BUDGET. With no backend, signal LOGIC-NO-BACKEND with a USE-BACKEND
restart that takes the backend to use."
  (declare (ignore backend rules facts budget))
  (%logic0-pending 'make-program))

(defun add-rules (program rules &key budget)
  "Add RULES (surface forms or RULE objects) in order. For each rule:
PARSE-RULE when it is a form (LOGIC-SYNTAX-ERROR); a rule kind the backend
lacks (:NEXT needs :TIME-STEP, :CHOICE and :CONSTRAINT their own keyword, a
(not …) literal :STRATIFIED-NEGATION or :UNSTRATIFIED-NEGATION) signals
LOGIC-UNSUPPORTED-RULE; RULE-UNSAFE-VARIABLES non-NIL signals
LOGIC-UNSAFE-RULE; then, unless the backend has :UNSTRATIFIED-NEGATION,
STRATIFY over the accepted rules plus this one, which may signal
LOGIC-UNSTRATIFIABLE. Checks run in that order. Restarts per rule:
DROP-RULE for all four, USE-BACKEND for the last two only (see
conditions.lisp). The conditions name the rule being added (and PROGRAM),
also when STRATIFY would blame an earlier rule of the same cycle. Rules
accepted earlier in the same call count for the stratification check and,
after a USE-BACKEND, go to the new backend. The accepted rules then go to
BACKEND-ADD-RULES in one call (no call when none was accepted), and only
then join PROGRAM-RULES. Returns the DELTA."
  (declare (ignore program rules budget))
  (%logic0-pending 'add-rules))

(defun add-rule (program rule &key budget)
  "(ADD-RULES PROGRAM (LIST RULE)). Returns the DELTA."
  (declare (ignore program rule budget))
  (%logic0-pending 'add-rule))

(defun update (program &key assert retract budget)
  "Retract the base facts RETRACT, assert the base facts ASSERT (retractions
first: a fact in both ends up asserted), bring the model up to date
incrementally. Returns the DELTA of the model."
  (declare (ignore program assert retract budget))
  (%logic0-pending 'update))

(defun assert-fact (program fact &key budget)
  "(UPDATE PROGRAM :ASSERT (LIST FACT)). Returns the DELTA."
  (declare (ignore program fact budget))
  (%logic0-pending 'assert-fact))

(defun retract-fact (program fact &key budget)
  "(UPDATE PROGRAM :RETRACT (LIST FACT)). Returns the DELTA."
  (declare (ignore program fact budget))
  (%logic0-pending 'retract-fact))

(defun query (program pattern &key limit budget assume)
  "Solutions of PATTERN: an atom, a built-in, (not …), or (and LIT...) of
those. Returns a list of binding alists ((VAR . VALUE) ...), one entry per
variable of PATTERN in first-occurrence order, without duplicates, sorted
(see the header); a ground pattern that holds gives (NIL). At most LIMIT
answers (the first ones in that order). An unsafe pattern signals
LOGIC-UNSAFE-RULE with RULE NIL and FORM PATTERN; a malformed one
LOGIC-SYNTAX-ERROR."
  (declare (ignore program pattern limit budget assume))
  (%logic0-pending 'query))

(defun holds-p (program pattern &key budget assume)
  "True when PATTERN has a solution."
  (declare (ignore program pattern budget assume))
  (%logic0-pending 'holds-p))

(defun explain (program fact &key assume)
  "A PROOF when FACT is in the model, else a WHY-NOT (model.lisp). FACT must
be a ground atom (LOGIC-SYNTAX-ERROR)."
  (declare (ignore program fact assume))
  (%logic0-pending 'explain))

(defun tick (program &key budget)
  "Advance one time step (BACKEND-TICK); increments PROGRAM-TIME. Needs
:TIME-STEP (else LOGIC-UNSUPPORTED-RULE with RULE NIL). Returns the DELTA."
  (declare (ignore program budget))
  (%logic0-pending 'tick))

(defun program-facts (program &key relation)
  "The facts in the model, sorted; only RELATION's unless it is NIL."
  (declare (ignore program relation))
  (%logic0-pending 'program-facts))

(defun program-base-facts (program &key relation)
  "The base facts, sorted; only RELATION's unless it is NIL."
  (declare (ignore program relation))
  (%logic0-pending 'program-base-facts))
