(in-package #:logic-protocol)

;;; Terms (brief: "Terms", locked).
;;;
;;; - A CONSTANT is a string, an integer, or a non-NIL symbol that is not a
;;;   variable. Keywords are constants. Constants compare with EQUAL (strings
;;;   case-sensitively).
;;; - A VARIABLE is a non-keyword symbol whose name starts with #\? and has at
;;;   least one more character: ?X, ?who. Variables are compared with EQ.
;;; - An ATOM is a proper list (RELATION ARG...) where RELATION is a non-NIL,
;;;   non-variable symbol and every ARG is a term. No function symbols: an
;;;   argument is never a list. Zero arguments are fine: (MOVED).
;;; - A FACT is a ground atom (no variables).
;;; - Relations are identified by the symbol (EQ). Atoms of one relation with
;;;   different argument counts never match each other.
;;; - Reserved names, by SYMBOL-NAME in any package: NOT, NEXT, CHOICE, AND,
;;;   RULE, =, /=, <, <=, >, >=, GLOB, PREFIX. They are never relations.
;;;
;;; Defined order (TERM<, FACT<), used for every list the protocol returns:
;;; integers < strings < symbols. Integers by <, strings by STRING<, symbols
;;; by SYMBOL-NAME (STRING<), then by package name ("" for an uninterned
;;; symbol). FACT< compares the relation as a term, then the arguments left to
;;; right; when one argument list is a prefix of the other, the shorter one is
;;; smaller.

(defparameter +reserved-names+
  '("NOT" "NEXT" "CHOICE" "AND" "RULE" "=" "/=" "<" "<=" ">" ">=" "GLOB" "PREFIX"))

(defparameter +builtin-names+
  '("=" "/=" "<" "<=" ">" ">=" "GLOB" "PREFIX"))

(defun named-p (x name)
  (and (symbolp x) x (string= (symbol-name x) name)))

(defun reserved-name-p (x)
  (and (symbolp x) x (member (symbol-name x) +reserved-names+ :test #'string=) t))

(defun proper-list-p (x)
  (loop for tail = x then (cdr tail)
        while (consp tail)
        finally (return (null tail))))

(defun logic-variable-p (x)
  "Is X a logic variable (a non-keyword symbol named ?…)?"
  (and (symbolp x)
       x
       (not (keywordp x))
       (let ((n (symbol-name x)))
         (and (> (length n) 1) (char= (char n 0) #\?)))))

(defun logic-constant-p (x)
  "Is X a constant: a string, an integer or a non-NIL non-variable symbol?"
  (or (stringp x)
      (integerp x)
      (and (symbolp x) x (not (logic-variable-p x)))))

(defun logic-term-p (x)
  (or (logic-variable-p x) (logic-constant-p x)))

(defun logic-atom-p (x)
  "Is X an atom (RELATION TERM...) with a non-reserved relation symbol?"
  (and (consp x)
       (symbolp (car x))
       (car x)
       (not (logic-variable-p (car x)))
       (not (reserved-name-p (car x)))
       (proper-list-p x)
       (every #'logic-term-p (cdr x))))

(defun ground-atom-p (x)
  "Is X a fact: an atom with no variables?"
  (and (logic-atom-p x) (notany #'logic-variable-p (cdr x))))

(defun atom-relation (atom) (car atom))
(defun atom-args (atom) (cdr atom))

(defun atom-variables (form)
  "The variables in FORM (an atom, literal or list of literals), first
occurrence first, each once."
  (let ((seen '()))
    (labels ((walk (x)
               (cond ((logic-variable-p x) (pushnew x seen))
                     ((consp x) (walk (car x)) (walk (cdr x))))))
      (walk form))
    (nreverse seen)))

(defun substitute-bindings (form bindings)
  "FORM with every variable bound in the alist BINDINGS replaced by its value."
  (cond ((logic-variable-p form)
         (let ((b (assoc form bindings)))
           (if b (cdr b) form)))
        ((consp form)
         (cons (substitute-bindings (car form) bindings)
               (substitute-bindings (cdr form) bindings)))
        (t form)))

(defun builtin-literal-p (x)
  "Is X a built-in literal: (= a b), (/= a b), (< a b), (<= a b), (> a b),
(>= a b), (glob PATTERN s) or (prefix PREFIX s)?

Semantics (all arguments bound when evaluated):
- = and /= compare with EQUAL. = may also bind: when one side is an unbound
  variable and the other is bound or a constant, the variable takes that value.
- <, <=, >, >= hold for two integers (numerically) or two strings (STRING<
  etc.); for any other pair they are false.
- (glob P S): P and S are strings; P matches the whole of S; * matches any run
  of characters (including / and the empty run), ? exactly one character;
  every other character matches itself. False when either is not a string.
- (prefix P S): P and S are strings and S starts with P."
  (and (consp x)
       (symbolp (car x))
       (member (symbol-name (car x)) +builtin-names+ :test #'string=)
       (= (length x) 3)
       (every #'logic-term-p (cdr x))))

(defun term< (a b)
  "The defined order on constants (see the file header)."
  (declare (ignore a b))
  (%logic0-pending 'term<))

(defun fact< (a b)
  "The defined order on facts (see the file header)."
  (declare (ignore a b))
  (%logic0-pending 'fact<))

(defun sort-facts (facts)
  "A fresh list of FACTS without EQUAL duplicates, sorted by FACT<."
  (declare (ignore facts))
  (%logic0-pending 'sort-facts))
