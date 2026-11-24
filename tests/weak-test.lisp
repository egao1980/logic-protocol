(in-package #:logic-protocol/tests)

;;; Weak constraints (issue #3, 0.2.0): parsing, validation, properties,
;;; feature checks, stratification, WEAK-INSTANCES and WEAK-COST.
;;;
;;; WEAK-INSTANCES only queries the model, so it is tested here on an
;;; evaluating mock: its BACKEND-QUERY answers the pattern over the base
;;; facts (the mock derives nothing, so a program is its facts). Rules with
;;; derived relations run in the conformance suite (conformance/weak-test).
;;; The expected instances, groundings and costs were worked out by hand and
;;; cross-checked against an independent reference evaluator (naive join,
;;; clingo's set semantics for instances); they agreed on every row.

;;; An evaluating mock ---------------------------------------------------------

(defclass eval-mock-backend (mock-backend) ()
  (:documentation "A mock backend whose BACKEND-QUERY evaluates the pattern
over its base facts, sorted by FACT<: positive atoms joined left to right,
then = binding to a fixpoint, then the other literals as filters. Supports
atoms, (not ATOM), (not BUILTIN), =, /=, <, <=, >, >=. One budget step per
answer, charged after the answer is recorded for the partial result."))

(defun make-eval-mock (&rest initargs)
  (apply #'make-instance 'eval-mock-backend initargs))

(defun eval-mock-program (&key facts (features '(:stratified-negation :time-step)))
  "A program on a fresh evaluating mock holding FACTS, its call log cleared."
  (let ((p (make-program :backend (make-eval-mock :features features))))
    (when facts (update p :assert facts :budget :unlimited))
    (setf (mock-calls (program-backend p)) '())
    p))

(defun %mock-unify (atom fact bindings)
  "BINDINGS extended so that ATOM matches FACT, or :FAIL."
  (if (and (eq (car atom) (car fact)) (= (length atom) (length fact)))
      (loop for a in (cdr atom)
            for f in (cdr fact)
            do (cond ((logic-variable-p a)
                      (let ((b (assoc a bindings)))
                        (cond ((null b) (push (cons a f) bindings))
                              ((not (equal (cdr b) f)) (return :fail)))))
                     ((not (equal a f)) (return :fail)))
            finally (return bindings))
      :fail))

(defun %mock-builtin-p (lit)
  (destructuring-bind (op a b) lit
    (let ((name (symbol-name op)))
      (flet ((compare (int-fn string-fn)
               (cond ((and (integerp a) (integerp b)) (funcall int-fn a b))
                     ((and (stringp a) (stringp b)) (and (funcall string-fn a b) t))
                     (t nil))))
        (cond ((string= name "=") (equal a b))
              ((string= name "/=") (not (equal a b)))
              ((string= name "<") (compare #'< #'string<))
              ((string= name "<=") (compare #'<= #'string<=))
              ((string= name ">") (compare #'> #'string>))
              ((string= name ">=") (compare #'>= #'string>=))
              (t (error "the evaluating mock does not support ~S" lit)))))))

(defun %mock-holds-p (lit facts)
  "Does the ground literal LIT hold over FACTS?"
  (cond ((logic-atom-p lit) (and (member lit facts :test #'equal) t))
        ((string= (symbol-name (car lit)) "NOT") (not (%mock-holds-p (second lit) facts)))
        (t (%mock-builtin-p lit))))

(defun %mock-bind-equalities (literals bindings)
  (flet ((known-p (x) (or (logic-constant-p x) (assoc x bindings))))
    (loop
      (let ((changed nil))
        (dolist (l literals)
          (when (and (builtin-literal-p l) (string= (symbol-name (car l)) "="))
            (destructuring-bind (a b) (cdr l)
              (cond ((and (logic-variable-p a) (not (assoc a bindings)) (known-p b))
                     (push (cons a (substitute-bindings b bindings)) bindings)
                     (setf changed t))
                    ((and (logic-variable-p b) (not (assoc b bindings)) (known-p a))
                     (push (cons b (substitute-bindings a bindings)) bindings)
                     (setf changed t))))))
        (unless changed (return bindings))))))

(defun eval-answers (body facts)
  "Every binding alist that satisfies BODY over FACTS."
  (let* ((facts (sort-facts facts))
         (others (remove-if #'logic-atom-p body))
         (rows (list '())))
    (dolist (a (remove-if-not #'logic-atom-p body))
      (setf rows (loop for row in rows
                       nconc (loop for f in facts
                                   for b = (%mock-unify a f row)
                                   unless (eq b :fail) collect b))))
    (loop for row in rows
          for b = (%mock-bind-equalities others row)
          when (every (lambda (l) (%mock-holds-p (substitute-bindings l b) facts)) others)
            collect b)))

(defmethod backend-query ((b eval-mock-backend) state pattern meter)
  (push (list :query pattern) (mock-calls b))
  (let ((found '()))
    (setf (budget-meter-partial-function meter) (lambda () found))
    (dolist (answer (eval-answers pattern (base-list state)) found)
      (push answer found)
      (charge-budget meter))))

(deftest eval-mock-sanity
  ;; The oracle itself (not under contract): QUERY through the evaluating mock.
  (let ((p (eval-mock-program :facts '((p 1) (p 2) (q 2) (r "a")))))
    (ok (equal (query p '(and (p ?x) (not (q ?x)))) '(((?x . 1)))))
    (ok (equal (query p '(and (p ?x) (q ?y) (< ?x ?y))) '(((?x . 1) (?y . 2)))))
    (ok (equal (query p '(and (r ?s) (= ?t ?s))) '(((?s . "a") (?t . "a")))))))

;;; Parsing --------------------------------------------------------------------

(deftest parse-weak-rule
  (let* ((form '(rule (weak 3 ?x) :- (p ?x) (not (q ?x))))
         (r (parse-rule form)))
    (ok (typep r 'rule))
    (ok (eq (rule-kind r) :weak))
    (ok (null (rule-head r)))
    (ok (null (rule-head-atoms r)))
    (ok (equal (rule-body r) '((p ?x) (not (q ?x)))))
    (ok (eql (rule-weight r) 3))
    (ok (eql (rule-level r) 0) "the level defaults to 0")
    (ok (equal (rule-terms r) '(?x)))
    (ok (null (rule-choice-bounds r)))
    (ok (eq (rule-form r) form))
    (ok (null (rule-name r))))
  (let ((r (parse-rule '(rule (weak (?c 2) ?x ?y) :- (cost ?x ?y ?c)))))
    (ok (eq (rule-weight r) '?c) "a variable weight")
    (ok (eql (rule-level r) 2))
    (ok (equal (rule-terms r) '(?x ?y))))
  (let ((r (parse-rule '(rule (weak (-1 -3)) :- (done ?t)))))
    (ok (eql (rule-weight r) -1) "negative weights")
    (ok (eql (rule-level r) -3) "negative levels")
    (ok (null (rule-terms r)) "no terms"))
  (let ((r (parse-rule '(rule (weak -4 :a "s" 7) :- (q 1)))))
    (ok (equal (rule-terms r) '(:a "s" 7)) "constant terms"))
  (let ((r (rule (weak 1 ?x) :- (p ?x))))
    (ok (eq (rule-kind r) :weak) "the RULE macro")
    (ok (equal (rule-form r) '(rule (weak 1 ?x) :- (p ?x)))))
  ;; Rules of the other kinds have no weak parts.
  (dolist (form '((rule (p ?x) :- (q ?x))
                  (rule (next (p ?x)) :- (q ?x))
                  (rule :- (q ?x))
                  (rule (choice 1 1 (p ?x)) :- (q ?x))))
    (let ((r (parse-rule form)))
      (ok (null (rule-weight r)))
      (ok (null (rule-level r)))
      (ok (null (rule-terms r))))))

(deftest parse-weak-by-symbol-name
  ;; Data read into another package: RULE, WEAK and NOT by name.
  (let ((r (parse-rule (list (intern "RULE" :keyword)
                             (list (intern "WEAK" :keyword) '(2 1) '?x)
                             :- '(:p ?x) (list (intern "NOT" :keyword) '(:q ?x))))))
    (ok (eq (rule-kind r) :weak))
    (ok (eql (rule-weight r) 2))
    (ok (eql (rule-level r) 1))
    (ok (equal (rule-terms r) '(?x)))
    (ok (equal (rule-body r) '((:p ?x) (:not (:q ?x)))))))

(deftest weak-is-reserved
  ;; WEAK is never a relation: not an atom, not a fact, not a pattern.
  (ok (not (logic-atom-p '(weak 1 2))))
  (ok (not (logic-atom-p '(:weak 1))))
  (let ((p (mock-program)))
    (ok (signals (assert-fact p '(weak 1)) 'logic-syntax-error))
    (ok (signals (query p '(weak ?x)) 'logic-syntax-error))))

(defun weak-form-of (r)
  "The canonical surface form of the weak rule R, built from its accessors:
the level is written only when it is not 0."
  `(rule (weak ,(if (zerop (rule-level r))
                    (rule-weight r)
                    (list (rule-weight r) (rule-level r)))
               ,@(rule-terms r))
         :- ,@(rule-body r)))

(defun weak-view (r)
  (list (rule-kind r) (rule-head r) (rule-weight r) (rule-level r) (rule-terms r)
        (rule-body r) (rule-properties r)))

(deftest-parametrize weak-round-trip
    ((form canonical)
     ('(rule (weak 3 ?x) :- (p ?x))
      '(rule (weak 3 ?x) :- (p ?x)))
     ('(rule (weak (3 0) ?x) :- (p ?x))
      '(rule (weak 3 ?x) :- (p ?x)))
     ('(rule (weak (?c 2) ?x ?y) :- (cost ?x ?y ?c))
      '(rule (weak (?c 2) ?x ?y) :- (cost ?x ?y ?c)))
     ('(rule (weak (-1 1)) :- (done ?t))
      '(rule (weak (-1 1)) :- (done ?t)))
     ('(rule (weak -4 :a "s" 7) :- (q 1) (not (r 2)) (< 1 2))
      '(rule (weak -4 :a "s" 7) :- (q 1) (not (r 2)) (< 1 2)))
     ('(rule (weak (0 -3) ?x) :- (p ?x) (= ?x 1))
      '(rule (weak (0 -3) ?x) :- (p ?x) (= ?x 1))))
  (let* ((r (parse-rule form))
         (again (parse-rule (weak-form-of r))))
    (ok (equal (weak-form-of r) canonical))
    (ok (equal (weak-view again) (weak-view r)) "accessors -> form -> parse is the identity")
    (ok (equal (weak-view (parse-rule (rule-form r))) (weak-view r)))))

(deftest weak-rule-properties
  (let ((r (parse-rule '(rule (weak (?c 2) ?x) :- (cost ?x ?c))
                       :name "w1"
                       :properties '(:source "s1" :weight 99 :level 5 :terms (1)
                                     :weight 98 :note :n))))
    (ok (equal (rule-properties r)
               '(:weight ?c :level 2 :terms (?x) :source "s1" :note :n))
        "the form's values first; the caller's :WEIGHT, :LEVEL and :TERMS removed")
    (ok (equal (rule-name r) "w1"))
    (ok (eql (getf (rule-properties r) :level) 2))
    (let ((again (parse-rule (rule-form r) :name (rule-name r)
                                           :properties (rule-properties r))))
      (ok (equal (rule-properties again) (rule-properties r)) "a fixpoint")))
  (ok (equal (rule-properties (parse-rule '(rule (weak 1) :- (q 1))))
             '(:weight 1 :level 0 :terms nil)))
  (ok (equal (rule-properties (parse-rule '(rule (weak (7 1) :a) :- (q 1)) :properties '(:x 1)))
             '(:weight 7 :level 1 :terms (:a) :x 1)))
  (ok (equal (rule-properties (parse-rule '(rule (p 1)) :properties '(:weight 9)))
             '(:weight 9))
      "other kinds keep the caller's plist as given"))

(deftest-parametrize parse-weak-syntax-errors
    ((form)
     ('(rule (weak) :- (q 1)))
     ('(rule (weak "a" ?x) :- (q ?x)))
     ('(rule (weak :high) :- (q 1)))
     ('(rule (weak nil) :- (q 1)))
     ('(rule (weak 1.5) :- (q 1)))
     ('(rule (weak 2/3) :- (q 1)))
     ('(rule (weak (1)) :- (q 1)))
     ('(rule (weak (1 2 3)) :- (q 1)))
     ('(rule (weak (1 ?l)) :- (q ?l)))
     ('(rule (weak (1 "a")) :- (q 1)))
     ('(rule (weak ((1 2) 0)) :- (q 1)))
     ('(rule (weak (?w . 2)) :- (q ?w)))
     ('(rule (weak 1 (f ?x)) :- (q ?x)))
     ('(rule (weak 1 . ?x) :- (q ?x)))
     ('(rule (weak 1 nil) :- (q 1)))
     ('(rule (weak 1 1.5) :- (q 1)))
     ('(rule (weak 1 ?x)))
     ('(rule (weak 1) :-))
     ('(rule (weak 1) (q 1)))
     ('(rule (p 1) :- (weak 1 2)))
     ('(rule (p ?x) :- (q ?x) (not (weak ?x))))
     ('(rule (next (weak 1)) :- (q 1)))
     ('(rule (choice 1 1 (weak 1)) :- (q 1))))
  (ok (signals (parse-rule form) 'logic-syntax-error))
  (ok (handler-case (progn (parse-rule form) nil)
        (logic-syntax-error (c)
          (and (eq (logic-error-form c) form)
               (stringp (logic-error-reason c))
               (plusp (length (logic-error-reason c))))))))

;;; Safety ---------------------------------------------------------------------

(deftest-parametrize weak-rule-safety
    ((form unsafe)
     ('(rule (weak 1 ?x) :- (p ?x)) nil)
     ('(rule (weak ?w ?x) :- (cost ?x ?w)) nil)
     ('(rule (weak 1 :a "s") :- (q 1)) nil)
     ('(rule (weak ?w ?x) :- (p ?x)) '(?w))
     ('(rule (weak 1 ?x ?y) :- (p ?x)) '(?y))
     ('(rule (weak (?w 1) ?x) :- (p ?y)) '(?w ?x))
     ('(rule (weak ?w) :- (p ?x) (= ?w 3)) nil)
     ('(rule (weak ?w ?x) :- (p ?x) (not (cost ?x ?w))) '(?w))
     ('(rule (weak 1 ?x) :- (p ?y) (< ?x ?y)) '(?x))
     ('(rule (weak 1) :- (not (p ?x))) '(?x))
     ('(rule (weak ?w ?z) :- (q ?y) (not (r ?z)) (= ?w ?y)) '(?z)))
  (ok (equal (rule-unsafe-variables (parse-rule form)) unsafe)))

;;; ADD-RULE: features, checks, restarts --------------------------------------

(deftest-parametrize weak-rule-unsupported
    ((features form)
     ;; the Datalog backend's features
     ('(:stratified-negation :time-step :incremental) '(rule (weak 1 ?x) :- (p ?x)))
     ;; unsupported is checked before safety
     ('(:stratified-negation :time-step :incremental) '(rule (weak ?w ?x) :- (p ?x)))
     ;; the kind is checked before negation
     ('() '(rule (weak 1 ?x) :- (p ?x) (not (q ?x))))
     ;; the other ASP kinds do not stand in for it
     ('(:stratified-negation :choice :constraint :unstratified-negation)
      '(rule (weak (2 1)) :- (p ?x))))
  (let* ((mock (make-mock :features features))
         (p (make-program :backend mock)))
    (ok (signals (add-rule p form) 'logic-unsupported-rule))
    (ok (handler-case (progn (add-rule p form) nil)
          (logic-unsupported-rule (c)
            (and (eq (logic-error-feature c) :weak-constraints)
                 (eq (logic-error-backend c) mock)
                 (eq (logic-error-program c) p)
                 (eq (rule-kind (logic-error-rule c)) :weak)
                 (equal (rule-form (logic-error-rule c)) form)))))
    (ok (signals-with-restarts (logic-unsupported-rule drop-rule use-backend)
          (add-rule p form)))
    (ok (null (program-rules p)))
    (ok (null (calls-of mock :add-rules)))))

(deftest weak-rule-drop-and-use-backend
  (let* ((full (make-mock :name :asp :features '(:stratified-negation :time-step
                                                 :weak-constraints)))
         (p (mock-program :features '(:stratified-negation :time-step :incremental))))
    (ok (handler-bind ((logic-unsupported-rule #'drop-rule))
          (add-rules p '((rule (a ?x) :- (b ?x))
                         (rule (weak 1 ?x) :- (a ?x))
                         (rule (c ?x) :- (a ?x))))
          t))
    (ok (equal (mapcar #'rule-form (program-rules p))
               '((rule (a ?x) :- (b ?x)) (rule (c ?x) :- (a ?x))))
        "DROP-RULE leaves the weak rule out and keeps the rest")
    (ok (handler-bind ((logic-unsupported-rule (lambda (c) (use-backend full c))))
          (add-rule p '(rule (weak (3 1) ?x) :- (c ?x) (not (b ?x))))
          t))
    (ok (eq (program-backend p) full) "USE-BACKEND moves the program")
    (ok (equal (mapcar #'rule-form (mock-state-rules (program-state p)))
               '((rule (a ?x) :- (b ?x)) (rule (c ?x) :- (a ?x))
                 (rule (weak (3 1) ?x) :- (c ?x) (not (b ?x))))))
    (ok (eq (rule-kind (third (program-rules p))) :weak))))

(deftest weak-rule-accepted-with-the-feature
  (let* ((mock (make-mock :features '(:stratified-negation :weak-constraints)))
         (p (make-program :backend mock)))
    ;; A weak rule adds no edge: no cycle through negation here.
    (ok (progn (add-rules p '((rule (p ?x) :- (d ?x) (not (q ?x)))
                              (rule (weak 1 ?x) :- (q ?x) (not (p ?x)))))
               t))
    (ok (equal (mapcar #'rule-kind (program-rules p)) '(:normal :weak)))
    (ok (equal (calls-of mock :add-rules)
               '((:add-rules ((rule (p ?x) :- (d ?x) (not (q ?x)))
                              (rule (weak 1 ?x) :- (q ?x) (not (p ?x))))))))
    (ok (signals (add-rule p '(rule (weak ?w ?x) :- (p ?x))) 'logic-unsafe-rule))
    (ok (handler-case (progn (add-rule p '(rule (weak ?w ?x) :- (p ?x))) nil)
          (logic-unsafe-rule (c)
            (and (equal (logic-error-variables c) '(?w))
                 (equal (logic-error-form c) '(rule (weak ?w ?x) :- (p ?x)))
                 (eq (logic-error-program c) p)))))
    (ok (signals-with-restarts (logic-unsafe-rule drop-rule)
          (add-rule p '(rule (weak ?w ?x) :- (p ?x)))))
    (ok (signals (add-rule p '(rule (weak "w") :- (p 1))) 'logic-syntax-error))
    (ok (signals-with-restarts (logic-syntax-error drop-rule)
          (add-rule p '(rule (weak "w") :- (p 1)))))
    (ok (= (length (program-rules p)) 2) "nothing else was added")))

(deftest weak-rule-stratify
  (ok (equal (stratify (mapcar #'parse-rule '((rule (p ?x) :- (q ?x))
                                              (rule (weak 1 ?x) :- (p ?x) (not (q ?x))))))
             '((p q))))
  (ok (equal (stratify (mapcar #'parse-rule '((rule (p ?x) :- (d ?x) (not (q ?x)))
                                              (rule (weak 1 ?x) :- (q ?x) (not (p ?x))))))
             '((d q) (p))))
  (ok (equal (stratify (list (parse-rule '(rule (weak 2 ?x) :- (r ?x) (not (s ?x))))))
             '((r s)))
      "the body relations are nodes")
  (ok (null (rule-head-atoms (parse-rule '(rule (weak 1) :- (q 1)))))))

;;; WEAK-INSTANCES on small programs -------------------------------------------

(deftest-parametrize weak-instances-programs
    ((facts rules instances groundings cost)
     :ids ("colour" "schedule" "cross-rule" "same-rule-twice" "equality" "constant-terms")
     ;; graph colouring: one instance per monochrome edge
     ('((edge 1 2) (edge 2 3) (edge 1 3) (edge 3 4)
        (color 1 :red) (color 2 :red) (color 3 :red) (color 4 :blue))
      '((rule (weak 1 ?x ?y) :- (edge ?x ?y) (color ?x ?c) (color ?y ?c)))
      '((1 0 1 2) (1 0 1 3) (1 0 2 3))
      '((((edge 1 2) (color 1 :red) (color 2 :red)))
        (((edge 1 3) (color 1 :red) (color 3 :red)))
        (((edge 2 3) (color 2 :red) (color 3 :red))))
      '((0 . 3)))
     ;; variable weights and levels, negation, a built-in; (-1 1) once
     ('((task :a) (task :b) (task :c) (due :a 2) (due :b 5) (due :c 1)
        (slot :a 3) (slot :b 6) (slot :c 1) (penalty :a 7) (penalty :b 2) (penalty :c 4)
        (done :b) (done :c))
      '((rule (weak (?p 2) ?t) :- (task ?t) (slot ?t ?s) (due ?t ?d) (> ?s ?d) (penalty ?t ?p))
        (rule (weak 1 ?t) :- (task ?t) (not (done ?t)))
        (rule (weak (-1 1)) :- (done ?t)))
      '((-1 1) (1 0 :a) (2 2 :b) (7 2 :a))
      '((((done :b)) ((done :c)))
        (((task :a) (not (done :a))))
        (((task :b) (slot :b 6) (due :b 5) (> 6 5) (penalty :b 2)))
        (((task :a) (slot :a 3) (due :a 2) (> 3 2) (penalty :a 7))))
      '((2 . 9) (1 . -1) (0 . 1)))
     ;; the same instance from two rules is one instance
     ('((p 1) (q 1) (q 2))
      '((rule (weak 5 ?x) :- (p ?x)) (rule (weak 5 ?x) :- (q ?x)))
      '((5 0 1) (5 0 2))
      '((((p 1)) ((q 1))) (((q 2))))
      '((0 . 10)))
     ;; equal groundings from two rules are listed once
     ('((p 1) (q 1) (q 2))
      '((rule (weak 5 ?x) :- (p ?x)) (rule (weak 5 ?x) :- (p ?x)))
      '((5 0 1))
      '((((p 1))))
      '((0 . 5)))
     ;; a weight bound through =; string terms
     ('((item "b") (item "a"))
      '((rule (weak ?w ?x) :- (item ?x) (= ?w 3)))
      '((3 0 "a") (3 0 "b"))
      '((((item "a") (= 3 3))) (((item "b") (= 3 3))))
      '((0 . 6)))
     ;; constant terms: one instance from two answers
     ('((q 1) (q 2))
      '((rule (weak (4 3) :tag "x") :- (q ?y)))
      '((4 3 :tag "x"))
      '((((q 1)) ((q 2))))
      '((3 . 4))))
  (let ((p (eval-mock-program :facts facts)))
    (multiple-value-bind (got-instances got-groundings) (weak-instances p rules)
      (ok (equal got-instances instances))
      (ok (equal got-groundings groundings))
      (ok (equal (weak-cost got-instances) cost)))
    (ok (equal (multiple-value-list (weak-instances p (mapcar #'parse-rule rules)))
               (list instances groundings))
        "RULE objects give the same result")
    (ok (null (program-rules p)) "the weak rules are not added")
    (ok (null (calls-of (program-backend p) :add-rules)))
    (ok (equal (program-base-facts p) (sort-facts facts)))))

(deftest weak-instances-queries-each-body
  (let* ((p (eval-mock-program :facts '((p 1) (q 1) (q 2))))
         (mock (program-backend p)))
    (weak-instances p '((rule (weak 5 ?x) :- (p ?x) (not (q 3)))
                        (rule (weak 1 ?x) :- (q ?x))))
    (ok (equal (calls-of mock :query :update :add-rules)
               '((:query ((p ?x) (not (q 3))))
                 (:query ((q ?x)))))
        "one BACKEND-QUERY per rule, given the body list, in RULES order")))

(deftest weak-instances-assume
  (let* ((facts '((task :a) (task :b) (task :c) (due :a 2) (due :b 5) (due :c 1)
                  (slot :a 3) (slot :b 6) (slot :c 1)
                  (penalty :a 7) (penalty :b 2) (penalty :c 4)
                  (done :b) (done :c)))
         (rules '((rule (weak (?p 2) ?t) :- (task ?t) (slot ?t ?s) (due ?t ?d) (> ?s ?d)
                   (penalty ?t ?p))
                  (rule (weak 1 ?t) :- (task ?t) (not (done ?t)))
                  (rule (weak (-1 1)) :- (done ?t))))
         (p (eval-mock-program :facts facts))
         (mock (program-backend p)))
    (multiple-value-bind (instances groundings)
        (weak-instances p rules :assume '((done :a) (done :b)))
      (ok (equal instances '((-1 1) (2 2 :b) (7 2 :a))))
      (ok (equal (first groundings) '(((done :a)) ((done :b)) ((done :c)))))
      (ok (equal (weak-cost instances) '((2 . 9) (1 . -1)))))
    (ok (equal (calls-of mock :update :query)
               '((:update ((done :a)) ())
                 (:query ((task ?t) (slot ?t ?s) (due ?t ?d) (> ?s ?d) (penalty ?t ?p)))
                 (:query ((task ?t) (not (done ?t))))
                 (:query ((done ?t)))
                 (:update () ((done :a)))))
        "only new facts are assumed, once for the call, then withdrawn")
    (ok (equal (program-base-facts p) (sort-facts facts)))
    (setf (mock-calls mock) '())
    (weak-instances p rules :assume '((done :b)))
    (ok (null (calls-of mock :update)) "an assumption that is a base fact changes nothing")))

(deftest weak-instances-non-integer-weight
  (let* ((facts '((cost :a 2) (cost :b "high") (cost :c :low) (cost :d 2)))
         (rules '((rule (weak ?w ?x) :- (cost ?x ?w))))
         (p (eval-mock-program :facts facts)))
    (ok (signals (weak-instances p rules) 'logic-syntax-error))
    (ok (handler-case (progn (weak-instances p rules) nil)
          (logic-syntax-error (c)
            (and (equal (logic-error-form c) '("high" 0 :b))
                 (eq (logic-error-program c) p)
                 (plusp (length (logic-error-reason c))))))
        "the first bad instance in answer order")
    (ok (signals-with-restarts (logic-syntax-error continue) (weak-instances p rules)))
    (let ((seen '()))
      (multiple-value-bind (instances groundings)
          (handler-bind ((logic-syntax-error (lambda (c)
                                               (push (logic-error-form c) seen)
                                               (continue c))))
            (weak-instances p rules))
        (ok (equal instances '((2 0 :a) (2 0 :d))) "CONTINUE skips the instance")
        (ok (equal groundings '((((cost :a 2))) (((cost :d 2)))))))
      (ok (equal (reverse seen) '(("high" 0 :b) (:low 0 :c)))))
    (ok (handler-case (progn (weak-instances p rules :assume '((extra 1))) nil)
          (logic-syntax-error () t)))
    (ok (equal (program-base-facts p) (sort-facts facts)) "ASSUME withdrawn on unwind")))

(deftest weak-instances-checks
  (let* ((p (eval-mock-program :facts '((p 1) (q 1))))
         (mock (program-backend p)))
    ;; not a weak rule: a form, or a RULE object
    (dolist (item (list '(rule (p ?x) :- (q ?x)) (parse-rule '(rule :- (q ?x)))))
      (ok (signals (weak-instances p (list item)) 'logic-syntax-error))
      (ok (handler-case (progn (weak-instances p (list item)) nil)
            (logic-syntax-error (c)
              (and (equal (logic-error-form c) (if (typep item 'rule) (rule-form item) item))
                   (eq (logic-error-program c) p)
                   (plusp (length (logic-error-reason c))))))))
    (ok (signals-with-restarts (logic-syntax-error drop-rule)
          (weak-instances p '((rule (p ?x) :- (q ?x))))))
    ;; malformed
    (ok (signals (weak-instances p '((rule (weak "x") :- (q 1)))) 'logic-syntax-error))
    (ok (signals-with-restarts (logic-syntax-error drop-rule)
          (weak-instances p '((rule (weak "x") :- (q 1))))))
    ;; unsafe
    (ok (handler-case (progn (weak-instances p '((rule (weak ?w ?x) :- (p ?x)))) nil)
          (logic-unsafe-rule (c)
            (and (equal (rule-form (logic-error-rule c)) '(rule (weak ?w ?x) :- (p ?x)))
                 (equal (logic-error-form c) '(rule (weak ?w ?x) :- (p ?x)))
                 (equal (logic-error-variables c) '(?w))
                 (eq (logic-error-program c) p)))))
    (ok (signals-with-restarts (logic-unsafe-rule drop-rule)
          (weak-instances p '((rule (weak ?w) :- (p ?x))))))
    ;; every rule is checked before the first query
    (ok (signals (weak-instances p '((rule (weak 1 ?x) :- (p ?x)) (rule (weak ?w) :- (p ?x))))
                 'logic-unsafe-rule))
    ;; ASSUME is checked as QUERY checks it
    (ok (signals (weak-instances p '((rule (weak 1 ?x) :- (p ?x))) :assume '((p ?y)))
                 'logic-syntax-error))
    (ok (null (calls-of mock :query :update)) "the backend never ran")))

(deftest weak-instances-drop-rule
  (let* ((p (eval-mock-program :facts '((p 1) (q 1) (q 2))))
         (mock (program-backend p)))
    (multiple-value-bind (instances groundings)
        (handler-bind ((logic-error #'drop-rule))
          (weak-instances p '((rule (weak 5 ?x) :- (p ?x))
                              (rule (p ?x) :- (q ?x))
                              (rule (weak ?w ?x) :- (q ?x))
                              (rule (weak "bad") :- (q 1))
                              (rule (weak 5 ?x) :- (q ?x)))))
      (ok (equal instances '((5 0 1) (5 0 2))))
      (ok (equal groundings '((((p 1)) ((q 1))) (((q 2)))))))
    (ok (equal (mapcar #'second (calls-of mock :query)) '(((p ?x)) ((q ?x)))))
    (setf (mock-calls mock) '())
    (ok (equal (multiple-value-list
                (handler-bind ((logic-error #'drop-rule))
                  (weak-instances p '((rule (p ?x) :- (q ?x))) :assume '((z 1)))))
               '(nil nil))
        "no rule left: (values NIL NIL)")
    (ok (equal (multiple-value-list (weak-instances p '())) '(nil nil)))
    (ok (null (calls-of mock :query :update)) "and the backend is not called")))

(deftest weak-instances-budget
  (let ((p (eval-mock-program :facts '((p 1) (q 1) (q 2))))
        (rules '((rule (weak 5 ?x) :- (p ?x)) (rule (weak 5 ?x) :- (q ?x)))))
    ;; Three answers in all, one step each, on one meter for the call.
    (ok (equal (weak-instances p rules :budget 3) '((5 0 1) (5 0 2))))
    (ok (signals (weak-instances p rules :budget 2) 'logic-budget-exceeded)
        "the steps of all rules add up")
    (ok (handler-case (progn (weak-instances p rules :budget 2) nil)
          (logic-budget-exceeded (c)
            (and (eq (logic-error-operation c) :query)
                 (eq (logic-error-program c) p)
                 (equal (logic-error-partial c) '(((?x . 1)) ((?x . 2))))))))
    (ok (signals-with-restarts (logic-budget-exceeded continue use-value)
          (weak-instances p rules :budget 2)))
    (ok (equal (handler-bind ((logic-budget-exceeded #'continue))
                 (multiple-value-list (weak-instances p rules :budget 2)))
               (multiple-value-list (weak-instances p rules :budget :unlimited)))
        "CONTINUE finishes the call")
    (ok (eq (handler-bind ((logic-budget-exceeded (lambda (c) (use-value :stopped c))))
              (weak-instances p rules :budget 1 :assume '((p 2))))
            :stopped)
        "USE-VALUE returns the value")
    (ok (equal (program-base-facts p) '((p 1) (q 1) (q 2))) "the assumption is withdrawn")))

(deftest weak-instances-partial-answers
  ;; PARTIAL: the answers of the body being evaluated, projected on its
  ;; variables in first-occurrence order and sorted, as QUERY reports them.
  (let ((p (eval-mock-program :facts '((edge 1 2) (edge 1 3) (edge 2 3)
                                       (color 1 :red) (color 2 :red) (color 3 :red)))))
    (ok (handler-case
            (progn (weak-instances p '((rule (weak 1 ?x ?y) :- (edge ?x ?y)
                                        (color ?x ?c) (color ?y ?c)))
                                   :budget 1)
                   nil)
          (logic-budget-exceeded (c)
            (equal (logic-error-partial c)
                   '(((?x . 1) (?y . 2) (?c . :red))
                     ((?x . 1) (?y . 3) (?c . :red)))))))))

;;; WEAK-COST ------------------------------------------------------------------

(deftest-parametrize weak-cost-levels
    ((instances cost)
     ('() '())
     ('((1 0 :a)) '((0 . 1)))
     ('((1 0 :a) (2 0 :b) (5 2) (-1 1 :x) (1 1 :y)) '((2 . 5) (1 . 0) (0 . 3)))
     ('((1 0 :a) (1 0 :a) (1 0 :b)) '((0 . 2)))
     ('((2 3) (1 -1) (4 -1 :z)) '((3 . 2) (-1 . 5)))
     ('((7 2 :a) (-1 1) (1 0 :a) (2 2 :b)) '((2 . 9) (1 . -1) (0 . 1))))
  (ok (equal (weak-cost instances) cost)))

(deftest weak-cost-type-errors
  (dolist (bad '((:a 0) (1) (1.5 0) (1 :high) 3 ("1" 0)))
    (ok (signals (weak-cost (list bad)) 'type-error) (format nil "~S" bad))))
