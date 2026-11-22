(in-package #:logic-protocol)

;;; Results: deltas, proofs, why-not traces.
;;;
;;; THE MODEL of a program is the set of facts that hold: its base facts plus
;;; everything its rules derive (stratified semantics, :NEXT rules excluded).
;;; A base fact is the zero-step derivation of itself, so "derived facts" in
;;; the brief's sense are the whole model.
;;;
;;; DELTA: what one operation (ADD-RULE(S), UPDATE, ASSERT-FACT, RETRACT-FACT,
;;; TICK) changed in the model. ADDED = facts in the model after and not
;;; before, REMOVED = before and not after; both sorted by FACT<, no
;;; duplicates, disjoint. A fact that left and came back within one operation
;;; is in neither. This is exactly the difference of two from-scratch
;;; evaluations, which the conformance suite checks.
;;;
;;; PROOF (EXPLAIN on a fact that holds). Base fact: RULE NIL, no premises.
;;; Derived fact: RULE is the rule instance used; PREMISES one proof per
;;; positive body atom, in body order; NEGATED the instantiated atoms of the
;;; (not ATOM) literals, in body order; BUILTINS the instantiated built-in
;;; literals (including (not BUILTIN)), in body order; BINDINGS the alist
;;; of every rule variable to its value, first-occurrence order in the rule
;;; form.
;;;
;;; Which proof: a base fact always gets the base proof. Otherwise the proof
;;; of least height (base 0; derived 1 + the largest premise height, 1 when
;;; there are no premises), each premise again explained this way. Ties go to
;;; the rule that comes first in PROGRAM-RULES, then to the instance whose
;;; list of premise facts (body order) is smallest, comparing element by
;;; element with FACT<.
;;;
;;; WHY-NOT (EXPLAIN on a fact that does not hold). REASONS has one entry per
;;; candidate: each :NORMAL rule, in PROGRAM-RULES order, whose head unifies
;;; with the fact. For a candidate, let B be its body with the head
;;; unification applied. The failing literal is literal K of B for the
;;; smallest K such that the prefix B[0..K] has no solution, where literals
;;; of the prefix whose variables the prefix does not bind (negations and
;;; built-ins waiting for a later atom) are left out. REASON-LITERAL is B[K]
;;; (head bindings applied, nothing else), REASON-INDEX is K (0-based). A
;;; rule with an empty body never fails, so it is never a candidate of a fact
;;; that does not hold.

(defclass delta ()
  ((added :initarg :added :initform '() :reader delta-added)
   (removed :initarg :removed :initform '() :reader delta-removed)))

(defun make-delta (&key added removed)
  "A DELTA with the lists given as they are (backends return these; the
protocol sorts them before handing a delta to the caller)."
  (make-instance 'delta :added added :removed removed))

(defmethod print-object ((d delta) stream)
  (print-unreadable-object (d stream :type t)
    (format stream "+~D -~D" (length (delta-added d)) (length (delta-removed d)))))

(defun delta-empty-p (delta)
  (and (null (delta-added delta)) (null (delta-removed delta))))

(defun delta-relations (delta)
  "The relations of the facts in DELTA, each once, sorted by TERM<. L3 maps
them to the fragments it re-renders."
  (declare (ignore delta))
  (%logic0-pending 'delta-relations))

(defclass proof ()
  ((fact :initarg :fact :reader proof-fact)
   (rule :initarg :rule :initform nil :reader proof-rule)
   (premises :initarg :premises :initform '() :reader proof-premises)
   (negated :initarg :negated :initform '() :reader proof-negated)
   (builtins :initarg :builtins :initform '() :reader proof-builtins)
   (bindings :initarg :bindings :initform '() :reader proof-bindings)))

(defmethod print-object ((p proof) stream)
  (print-unreadable-object (p stream :type t)
    (format stream "~S~:[~; base~]" (proof-fact p) (proof-base-p p))))

(defun proof-base-p (proof)
  "Is PROOF a base fact's proof?"
  (null (proof-rule proof)))

(defun proof-height (proof)
  "0 for a base proof; else 1 + the largest premise height (1 with none)."
  (if (proof-base-p proof)
      0
      (1+ (reduce #'max (proof-premises proof) :key #'proof-height :initial-value 0))))

(defun proof-base-facts (proof)
  "The base facts at the leaves of PROOF, each once, sorted by FACT<."
  (declare (ignore proof))
  (%logic0-pending 'proof-base-facts))

(defclass why-not ()
  ((fact :initarg :fact :reader why-not-fact)
   (reasons :initarg :reasons :initform '() :reader why-not-reasons)))

(defmethod print-object ((w why-not) stream)
  (print-unreadable-object (w stream :type t)
    (format stream "~S (~D reason~:P)" (why-not-fact w) (length (why-not-reasons w)))))

(defclass why-not-reason ()
  ((rule :initarg :rule :reader reason-rule)
   (literal :initarg :literal :reader reason-literal)
   (index :initarg :index :reader reason-index)))
