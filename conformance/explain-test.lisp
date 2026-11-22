(in-package #:logic-protocol/conformance)

;;; Proof trees and why-not traces (model.lisp fixes which proof and which
;;; literal).

(defparameter *path-1* '(rule (path ?x ?y) :- (edge ?x ?y)))
(defparameter *path-2* '(rule (path ?x ?z) :- (edge ?x ?y) (path ?y ?z)))

(deftest explain-base-fact
  (let* ((p (closure-program '(edge 1 2)))
         (proof (explain p '(edge 1 2))))
    (ok (typep proof 'proof))
    (ok (proof-base-p proof))
    (ok (equal (proof-fact proof) '(edge 1 2)))
    (ok (= (proof-height proof) 0))
    (ok (null (proof-premises proof)))))

(deftest explain-derived-fact
  (let* ((p (closure-program '(edge 1 2) '(edge 2 3)))
         (proof (explain p '(path 1 3))))
    (ok (typep proof 'proof))
    (ok (equal (proof-sexp proof)
               `((path 1 3) ,*path-2*
                 (((edge 1 2) nil nil nil nil nil)
                  ((path 2 3) ,*path-1*
                   (((edge 2 3) nil nil nil nil nil))
                   nil nil ((?x . 2) (?y . 3))))
                 nil nil ((?x . 1) (?z . 3) (?y . 2)))))
    (ok (= (proof-height proof) 2))
    (ok (equal (proof-base-facts proof) '((edge 1 2) (edge 2 3))))))

(deftest explain-least-height
  (let* ((p (closure-program '(edge 1 2) '(edge 2 3) '(edge 3 4) '(edge 1 4)))
         (proof (explain p '(path 1 4))))
    (ok (equal (rule-form (proof-rule proof)) *path-1*))
    (ok (= (proof-height proof) 1))
    (ok (equal (proof-base-facts proof) '((edge 1 4))))))

(deftest explain-base-beats-derivation
  (let* ((p (closure-program '(edge 1 2) '(edge 2 3) '(path 1 3))))
    (ok (proof-base-p (explain p '(path 1 3))))))

(deftest explain-tie-breaks
  (let ((p (make-test-program
            :rules '((rule (ok ?x) :- (b ?x))
                     (rule (ok ?x) :- (a ?x))
                     (rule (has-friend ?x) :- (friend ?x ?y)))
            :facts '((a 1) (b 1) (friend :ann "zed") (friend :ann "bob") (friend :ann 7)))))
    (ok (equal (rule-form (proof-rule (explain p '(ok 1))))
               '(rule (ok ?x) :- (b ?x)))
        "same height: the rule added first")
    (ok (equal (mapcar #'proof-fact (proof-premises (explain p '(has-friend :ann))))
               '((friend :ann 7)))
        "same rule: the smallest premise list by FACT<")))

(deftest explain-negation-and-builtins
  (requiring (:stratified-negation)
    (let* ((p (make-test-program
               :rules (append *reach-rules*
                              '((rule (valid :email) :- (value :email ?v) (glob "*@*.*" ?v))))
               :facts '((start 1) (node 1) (node 4) (value :email "a@b.c"))))
           (unreach (explain p '(unreach 4)))
           (valid (explain p '(valid :email))))
      (ok (equal (mapcar #'proof-fact (proof-premises unreach)) '((node 4))))
      (ok (equal (proof-negated unreach) '((reach 4))))
      (ok (equal (proof-bindings unreach) '((?x . 4))))
      (ok (equal (proof-builtins valid) '((glob "*@*.*" "a@b.c"))))
      (ok (equal (proof-bindings valid) '((?v . "a@b.c")))))))

(deftest why-not-first-failing-literal
  (let* ((p (closure-program '(edge 1 2) '(edge 2 3)))
         (w (explain p '(path 1 9))))
    (ok (typep w 'why-not))
    (ok (equal (why-not-fact w) '(path 1 9)))
    (ok (equal (mapcar (lambda (r)
                         (list (rule-form (reason-rule r)) (reason-literal r) (reason-index r)))
                       (why-not-reasons w))
               `((,*path-1* (edge 1 9) 0)
                 (,*path-2* (path ?y 9) 1))))
    (let ((w3 (explain p '(path 3 1))))
      (ok (equal (mapcar #'reason-literal (why-not-reasons w3))
                 '((edge 3 1) (edge 3 ?y)))))))

(deftest why-not-no-candidates
  (let* ((p (closure-program '(edge 1 2)))
         (w (explain p '(edge 2 1))))
    (ok (typep w 'why-not))
    (ok (null (why-not-reasons w))))
  (let ((w (explain (make-test-program) '(anything))))
    (ok (null (why-not-reasons w)))))

(deftest why-not-head-must-unify
  (let* ((p (make-test-program :rules '((rule (same ?x ?x) :- (n ?x))) :facts '((n 1))))
         (w (explain p '(same 1 2))))
    (ok (null (why-not-reasons w)) "(same ?x ?x) does not unify with (same 1 2)")
    (ok (typep (explain p '(same 1 1)) 'proof))))

(deftest-parametrize proofs-bottom-out-in-base-facts
    ((seed) (31) (32) (33))
  (let* ((rng (make-rng seed))
         (edges (random-edges rng 8 12))
         (p (make-test-program :rules (closure-rules :nonlinear) :facts edges))
         (base (program-base-facts p)))
    (ok (every (lambda (f)
                 (let ((proof (explain p f)))
                   (and (typep proof 'proof)
                        (equal (proof-fact proof) f)
                        (proof-consistent-p proof base))))
               (model p)))
    (ok (every (lambda (f) (typep (explain p f) 'why-not))
               (loop for a from 1 to 8
                     nconc (loop for b from 1 to 8
                                 for f = (list 'path a b)
                                 unless (holds-p p f) collect f))))))

(deftest explain-with-assumption
  (let ((p (closure-program '(edge 1 2))))
    (let ((proof (explain p '(path 1 3) :assume '((edge 2 3)))))
      (ok (typep proof 'proof))
      (ok (equal (proof-base-facts proof) '((edge 1 2) (edge 2 3)))))
    (ok (typep (explain p '(path 1 3)) 'why-not))))
