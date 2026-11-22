(in-package #:logic-protocol/tests)

(deftest parse-normal-rule
  (let* ((form '(rule (path ?x ?z) :- (edge ?x ?y) (path ?y ?z)))
         (r (parse-rule form)))
    (ok (typep r 'rule))
    (ok (eq (rule-kind r) :normal))
    (ok (equal (rule-head r) '(path ?x ?z)))
    (ok (equal (rule-body r) '((edge ?x ?y) (path ?y ?z))))
    (ok (equal (rule-head-atoms r) '((path ?x ?z))))
    (ok (eq (rule-form r) form))
    (ok (null (rule-name r)))
    (ok (null (rule-properties r)))
    (ok (null (rule-choice-bounds r)))))

(deftest rule-macro-is-parse-rule
  (let ((r (rule (enabled :submit) :- (valid :email) (checked :terms))))
    (ok (typep r 'rule))
    (ok (equal (rule-form r) '(rule (enabled :submit) :- (valid :email) (checked :terms))))
    (ok (equal (rule-body r) '((valid :email) (checked :terms))))))

(deftest parse-name-and-properties
  (let ((r (parse-rule '(rule (permitted) :- (action "read"))
                       :name "r1" :properties '(:effect :permit))))
    (ok (equal (rule-name r) "r1"))
    (ok (equal (rule-properties r) '(:effect :permit)))))

(deftest parse-empty-body
  (dolist (form '((rule (enabled :help)) (rule (enabled :help) :-)))
    (let ((r (parse-rule form)))
      (ok (eq (rule-kind r) :normal))
      (ok (equal (rule-head r) '(enabled :help)))
      (ok (null (rule-body r))))))

(deftest parse-negation-and-builtins
  (let ((r (parse-rule '(rule (ok ?x) :- (item ?x) (not (bad ?x)) (< ?x 10)
                         (not (glob "tmp*" ?x)) (= ?y ?x) (prefix "a" ?x)))))
    (ok (eq (rule-kind r) :normal))
    (ok (= (length (rule-body r)) 6))))

(deftest parse-next-rule
  (let ((r (parse-rule '(rule (next (state ?s2)) :- (state ?s1) (event ?e) (step ?s1 ?e ?s2)))))
    (ok (eq (rule-kind r) :next))
    (ok (equal (rule-head r) '(state ?s2)))
    (ok (equal (rule-head-atoms r) '((state ?s2))))))

(deftest parse-constraint
  (let ((r (parse-rule '(rule :- (color ?n ?c) (color ?m ?c) (edge ?n ?m)))))
    (ok (eq (rule-kind r) :constraint))
    (ok (null (rule-head r)))
    (ok (null (rule-head-atoms r)))
    (ok (= (length (rule-body r)) 3))))

(deftest parse-choice
  (let ((r (parse-rule '(rule (choice 1 1 (color ?n :red) (color ?n :green)) :- (node ?n)))))
    (ok (eq (rule-kind r) :choice))
    (ok (equal (rule-head r) '((color ?n :red) (color ?n :green))))
    (ok (equal (rule-head-atoms r) '((color ?n :red) (color ?n :green))))
    (ok (equal (rule-choice-bounds r) '(1 . 1))))
  (let ((r (parse-rule '(rule (choice nil 2 (pick ?x)) :- (item ?x)))))
    (ok (equal (rule-choice-bounds r) '(nil . 2)))))

(deftest parse-by-symbol-name
  ;; Data read into another package (L1 loads settings): RULE, NOT, NEXT and
  ;; the built-ins are recognised by name.
  (let* ((rule-sym (intern "RULE" :keyword))
         (not-sym (intern "NOT" :keyword))
         (r (parse-rule (list rule-sym '(:p ?x) :- '(:q ?x) (list not-sym '(:r ?x))))))
    (ok (eq (rule-kind r) :normal))
    (ok (equal (rule-head r) '(:p ?x)))))

(deftest-parametrize parse-syntax-errors
    ((form)
     ('(rule))
     ('(rule 3))
     ('(rules (p 1)))
     ('(rule (p (f 1)) :- (q 1)))
     ('(rule (p 1) (q 1)))
     ('(rule (p 1) :- (q (f))))
     ('(rule (p 1) :- 3))
     ('(rule (p 1) :- (q 1) . 3))
     ('(rule (p ?x) :- (next (q ?x))))
     ('(rule (not (p 1)) :- (q 1)))
     ('(rule (glob "a" "b")))
     ('(rule (?r 1) :- (q 1)))
     ('(rule :-))
     ('(rule (choice 1 2) :- (q 1)))
     ('(rule (choice "x" 2 (p 1)) :- (q 1)))
     ('(rule (p ?x) :- (not (not (q ?x)))))
     ('(rule (p 1) :- (< 1)))
     ('(rule (p 1) :- (choice 1 1 (q 1))))
     ('(rule (next (p 1) (q 1)) :- (r 1)))
     ("(rule (p 1))"))
  (ok (signals (parse-rule form) 'logic-syntax-error))
  (ok (handler-case (progn (parse-rule form) nil)
        (logic-syntax-error (c)
          (and (eq (logic-error-form c) form)
               (stringp (logic-error-reason c))
               (plusp (length (logic-error-reason c))))))))
