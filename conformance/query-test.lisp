(in-package #:logic-protocol/conformance)

(defun chain-program ()
  (make-test-program :rules (closure-rules)
                     :facts '((edge 1 2) (edge 2 3) (edge 3 4) (edge 4 4))))

(deftest query-single-atom
  (let ((p (chain-program)))
    (ok (equal (query p '(path 1 ?y))
               '(((?y . 2)) ((?y . 3)) ((?y . 4)))))
    (ok (equal (query p '(edge ?x ?x)) '(((?x . 4)))) "a repeated variable must match itself")
    (ok (equal (query p '(path ?x 2)) '(((?x . 1)))))))

(deftest query-join
  (let ((p (chain-program)))
    (ok (equal (query p '(and (edge ?x ?y) (edge ?y ?z)))
               '(((?x . 1) (?y . 2) (?z . 3))
                 ((?x . 2) (?y . 3) (?z . 4))
                 ((?x . 3) (?y . 4) (?z . 4))
                 ((?x . 4) (?y . 4) (?z . 4)))))))

(deftest query-variable-order
  (let ((p (chain-program)))
    (ok (equal (query p '(edge ?b ?a) :limit 2)
               '(((?b . 1) (?a . 2)) ((?b . 2) (?a . 3)))))))

(deftest query-negation-and-builtins
  (requiring (:stratified-negation)
    (let ((p (chain-program)))
      (ok (equal (query p '(and (path 1 ?y) (not (edge ?y 4))))
                 '(((?y . 2)))))
      (ok (equal (query p '(and (path ?x ?y) (> ?x 2)))
                 '(((?x . 3) (?y . 4)) ((?x . 4) (?y . 4)))))
      (ok (equal (query p '(and (edge 1 ?y) (= ?z ?y)))
                 '(((?y . 2) (?z . 2))))))))

(deftest query-ground-and-limit
  (let ((p (chain-program)))
    (ok (equal (query p '(path 1 4)) '(nil)))
    (ok (null (query p '(path 4 1))))
    (ok (holds-p p '(path 1 4)))
    (ok (holds-p p '(path ?x 4)))
    (ok (not (holds-p p '(path 4 ?x 1))) "another arity never matches")
    (ok (= (length (query p '(path ?x ?y))) 7))
    (ok (equal (query p '(path ?x ?y) :limit 1) '(((?x . 1) (?y . 2)))))))

(deftest query-unknown-relation
  (let ((p (chain-program)))
    (ok (null (query p '(nothing ?x))))
    (ok (not (holds-p p '(nothing 1))))))

(deftest query-leaves-program-alone
  (let* ((p (chain-program))
         (before (model p)))
    (query p '(and (path ?x ?y) (path ?y ?z)))
    (query p '(path ?x ?y) :assume '((edge 9 1)))
    (ok (equal (model p) before))
    (ok (equal (query p '(path 9 ?y) :assume '((edge 9 1)))
               '(((?y . 1)) ((?y . 2)) ((?y . 3)) ((?y . 4)))))
    (ok (null (query p '(path 9 ?y))))))

(deftest query-unsafe-pattern
  (let ((p (chain-program)))
    (ok (signals (query p '(and (edge ?x ?y) (not (path ?y ?w)))) 'logic-unsafe-rule))))
