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
;;;
;;; HEAD is an atom (LOGIC-ATOM-P). A body LIT is an atom, a built-in
;;; (BUILTIN-LITERAL-P), or (not X) where X is an atom or a built-in. NEXT
;;; and CHOICE appear only in heads. Anything else signals LOGIC-SYNTAX-ERROR
;;; with FORM = the whole rule form and a REASON string. The datalog backend
;;; supports :NORMAL and :NEXT; :CONSTRAINT and :CHOICE are parsed so that an
;;; ASP backend (L5) fits, and ADD-RULE signals LOGIC-UNSUPPORTED-RULE on a
;;; backend that lacks them.
;;;
;;; Safety (range restriction, RULE-UNSAFE-VARIABLES): start with the
;;; variables of the positive body atoms; then, repeatedly, for (= A B) in the
;;; body where one side is a constant or bound, the other side becomes bound.
;;; Every variable of the head (all head atoms of a choice rule, the inner
;;; atom of NEXT), of a negated literal, and of a built-in other than = must
;;; end up bound, and both sides of every = too. The unbound ones, in
;;; first-occurrence order over the whole rule form, are the unsafe
;;; variables.
;;;
;;; Stratification (STRATIFY): the dependency graph has an edge from each
;;; body relation to each head relation of the same rule, negative when the
;;; body literal is (not ATOM). Built-ins add no edges. Rules of kind :NEXT
;;; add no edges (time separates them: the body is read at t, the head is a
;;; fact at t+1). :CONSTRAINT rules have no head and add no edges. A
;;; negative edge inside a strongly connected component makes the program
;;; unstratifiable.

(defclass rule ()
  ((head :initarg :head :reader rule-head
         :documentation "An atom (:NORMAL), the inner atom (:NEXT), NIL
(:CONSTRAINT) or the list of atoms (:CHOICE).")
   (body :initarg :body :initform '() :reader rule-body
         :documentation "The literals as written (plain lists).")
   (kind :initarg :kind :initform :normal :reader rule-kind)
   (choice-bounds :initarg :choice-bounds :initform nil :reader rule-choice-bounds
                  :documentation "(LO . HI) for :CHOICE, else NIL.")
   (name :initarg :name :initform nil :reader rule-name)
   (properties :initarg :properties :initform '() :reader rule-properties
               :documentation "A plist the caller owns (L1 keeps the effect,
feedback and source rule here). The protocol never reads it.")
   (form :initarg :form :reader rule-form
         :documentation "The surface form PARSE-RULE read.")))

(defmethod print-object ((r rule) stream)
  (print-unreadable-object (r stream :type t)
    (format stream "~S" (rule-form r))))

(defun rule-head-atoms (rule)
  "The atoms RULE derives: one for :NORMAL and :NEXT, the choice atoms for
:CHOICE, none for :CONSTRAINT."
  (ecase (rule-kind rule)
    ((:normal :next) (list (rule-head rule)))
    (:choice (rule-head rule))
    (:constraint '())))

(defun parse-rule (form &key name properties)
  "Parse the surface FORM (see the file header) into a RULE with NAME and
PROPERTIES. Signals LOGIC-SYNTAX-ERROR. Does not check safety."
  (declare (ignore form name properties))
  (%logic0-pending 'parse-rule))

(defmacro rule (&rest parts)
  "(rule HEAD :- LIT...) evaluates to the parsed RULE; the parts are not
evaluated."
  `(parse-rule '(rule ,@parts)))

(defun rule-unsafe-variables (rule-or-body)
  "The unsafe variables of a RULE (see the file header), or of a list of body
literals read as a headless query. NIL when safe."
  (declare (ignore rule-or-body))
  (%logic0-pending 'rule-unsafe-variables))

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
  (declare (ignore rules))
  (%logic0-pending 'stratify))
