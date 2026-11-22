(in-package #:logic-protocol/tests)

(defun rules (&rest forms)
  (mapcar #'parse-rule forms))

(deftest stratify-positive-recursion
  (ok (equal (stratify (rules '(rule (path ?x ?y) :- (edge ?x ?y))
                              '(rule (path ?x ?z) :- (edge ?x ?y) (path ?y ?z))))
             '((edge path)))))

(deftest stratify-negation-layers
  (ok (equal (stratify (rules '(rule (p ?x) :- (q ?x))
                              '(rule (r ?x) :- (d ?x) (not (p ?x)))
                              '(rule (s ?x) :- (r ?x) (not (q ?x)))))
             '((d p q) (r s))))
  (ok (equal (stratify (rules '(rule (reach ?y) :- (start ?y))
                              '(rule (reach ?y) :- (reach ?x) (edge ?x ?y))
                              '(rule (unreach ?x) :- (node ?x) (not (reach ?x)))))
             '((edge node reach start) (unreach))))
  (ok (equal (stratify (rules '(rule (c ?x) :- (n ?x))
                              '(rule (b ?x) :- (n ?x) (not (c ?x)))
                              '(rule (a ?x) :- (n ?x) (not (b ?x)))))
             '((c n) (b) (a)))))

(deftest stratify-builtins-and-empty
  (ok (equal (stratify (rules '(rule (big ?x) :- (n ?x) (> ?x 10) (not (glob "a*" ?x)))))
             '((big n))))
  (ok (null (stratify '()))))

(deftest stratify-next-rules-add-no-edges
  (ok (equal (stratify (rules '(rule (next (p)) :- (not (p)))))
             '((p))))
  (ok (equal (stratify (rules '(rule (next (p ?x)) :- (d ?x) (not (p ?x)))
                              '(rule (q ?x) :- (p ?x))))
             '((d p q)))))

(deftest stratify-constraints-add-no-edges
  (ok (equal (stratify (rules '(rule :- (p ?x) (not (q ?x)))))
             '((p q)))))

(deftest-parametrize stratify-negative-cycles
    ((forms culprit cycle)
     ('((rule (p ?x) :- (d ?x) (not (q ?x)))
        (rule (q ?x) :- (d ?x) (not (p ?x))))
      0 '(p q))
     ('((rule (p ?x) :- (d ?x) (not (p ?x))))
      0 '(p))
     ('((rule (a ?x) :- (d ?x))
        (rule (win ?x) :- (move ?x ?y) (not (win ?y))))
      1 '(win))
     ('((rule (q ?x) :- (p ?x))
        (rule (r ?x) :- (q ?x))
        (rule (p ?x) :- (d ?x) (not (r ?x))))
      2 '(p q r)))
  (let ((rs (mapcar #'parse-rule forms)))
    (ok (signals (stratify rs) 'logic-unstratifiable))
    (ok (handler-case (progn (stratify rs) nil)
          (logic-unstratifiable (c)
            (and (eq (logic-error-rule c) (nth culprit rs))
                 (equal (logic-error-cycle c) cycle)))))))

(defparameter *two-player*
  '((rule (p ?x) :- (d ?x) (not (q ?x)))
    (rule (q ?x) :- (d ?x) (not (p ?x)))))

(deftest add-rules-unstratifiable-restarts
  (let ((p (mock-program)))
    (ok (signals (add-rules p *two-player*) 'logic-unstratifiable))
    (ok (null (program-rules p)))
    (ok (signals-with-restarts (logic-unstratifiable drop-rule use-backend)
          (add-rules p *two-player*)))))

(deftest add-rules-unstratifiable-drop-rule
  (let ((p (mock-program)))
    (handler-bind ((logic-unstratifiable #'drop-rule))
      (add-rules p (append *two-player* '((rule (r ?x) :- (p ?x))))))
    (ok (equal (mapcar #'rule-form (program-rules p))
               (list (first *two-player*) '(rule (r ?x) :- (p ?x))))
        "the rule that closes the cycle is the one dropped; later rules still go in")))

(deftest add-rules-unstratifiable-use-backend
  (let* ((asp (make-mock :name :asp :features '(:stratified-negation :unstratified-negation)))
         (p (mock-program)))
    (update p :assert '((d 1) (d 2)))
    (handler-bind ((logic-unstratifiable (lambda (c) (use-backend asp c))))
      (add-rules p *two-player*))
    (ok (eq (program-backend p) asp))
    (ok (equal (mapcar #'rule-form (program-rules p)) *two-player*))
    (ok (equal (program-base-facts p) '((d 1) (d 2))) "base facts moved to the new backend")
    (ok (equal (mapcar #'rule-form (mock-state-rules (program-state p))) *two-player*))))

(deftest unstratified-backend-skips-the-check
  (let ((p (mock-program :features '(:stratified-negation :unstratified-negation))))
    (add-rules p *two-player*)
    (ok (= (length (program-rules p)) 2))))

(deftest stratification-spans-calls
  (let ((p (mock-program)))
    (add-rule p (first *two-player*))
    (ok (signals (add-rule p (second *two-player*)) 'logic-unstratifiable))
    (ok (= (length (program-rules p)) 1))))
