(in-package #:logic-protocol/conformance)

;;; Determinism: every result has the protocol's defined order and does not
;;; depend on the order facts arrive in.

(deftest query-order-mixed-constants
  (let ((p (make-test-program :facts '((item "b") (item 3) (item :c) (item ann) (item 1)
                                       (item "a") (item -2) (item :b)))))
    (ok (equal (mapcar (lambda (b) (cdr (first b))) (query p '(item ?x)))
               '(-2 1 3 "a" "b" ann :b :c))
        "integers, then strings, then symbols by name (ANN < B < C)")
    (ok (equal (model p)
               '((item -2) (item 1) (item 3) (item "a") (item "b") (item ann) (item :b) (item :c))))))

(deftest query-order-tuples
  (let ((p (make-test-program :facts '((pair 2 1) (pair 1 2) (pair 1 1) (pair 1 "x") (pair 10 0)))))
    (ok (equal (query p '(pair ?a ?b))
               '(((?a . 1) (?b . 1)) ((?a . 1) (?b . 2)) ((?a . 1) (?b . "x"))
                 ((?a . 2) (?b . 1)) ((?a . 10) (?b . 0)))))
    (ok (equal (query p '(pair ?b ?a))
               '(((?b . 1) (?a . 1)) ((?b . 1) (?a . 2)) ((?b . 1) (?a . "x"))
                 ((?b . 2) (?a . 1)) ((?b . 10) (?a . 0))))
        "variables are named by the pattern, sorted by position")))

(deftest model-order-across-relations
  (let ((p (make-test-program :rules (closure-rules) :facts '((edge 2 3) (edge 1 2)))))
    (ok (equal (model p) '((edge 1 2) (edge 2 3) (path 1 2) (path 1 3) (path 2 3))))))

(deftest-parametrize order-independent
    ((seed) (51) (52) (53) (54))
  (requiring (:stratified-negation)
    (let* ((rng (make-rng seed))
           (facts (append (random-edges rng 8 14) (program-kind-fixed-facts :mixed 8)))
           (a (make-test-program :rules *mixed-rules* :facts facts))
           (b (make-test-program :rules *mixed-rules*)))
      ;; B gets the same facts shuffled, one at a time.
      (dolist (f (shuffle rng facts)) (assert-fact b f :budget :unlimited))
      (ok (equal (model a) (model b)))
      (ok (equal (query a '(and (path ?x ?y) (not (hub ?x)))) (query b '(and (path ?x ?y) (not (hub ?x))))))
      (ok (every (lambda (f) (equal (proof-sexp (explain a f)) (proof-sexp (explain b f))))
                 (model a))
          "the same proofs")
      (let ((extra (random-edges rng 8 3)))
        (let ((da (update a :assert extra))
              (db (update b :assert (reverse extra))))
          (ok (equal (delta-added da) (delta-added db)))
          (ok (equal (delta-removed da) (delta-removed db))))))))

(deftest repeated-calls-agree
  (let ((p (make-test-program :rules (closure-rules :nonlinear)
                              :facts (random-edges (make-rng 61) 9 15))))
    (ok (equal (query p '(path ?x ?y)) (query p '(path ?x ?y))))
    (ok (equal (model p) (model p)))))

(deftest rules-keep-their-order
  (let* ((forms '((rule (b ?x) :- (a ?x)) (rule (c ?x) :- (b ?x)) (rule (a ?x) :- (z ?x))))
         (p (make-test-program :rules forms)))
    (ok (equal (mapcar #'rule-form (program-rules p)) forms))))
