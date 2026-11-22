(in-package #:logic-protocol/conformance)

;;; Exact delta contents (model.lisp: the change of the model, sorted).

(defun closure-program (&rest edges)
  (make-test-program :rules (closure-rules) :facts edges))

(defmacro delta-is (form added removed)
  (let ((d (gensym)))
    `(let ((,d ,form))
       (ok (typep ,d 'delta))
       (ok (equal (delta-added ,d) ,added))
       (ok (equal (delta-removed ,d) ,removed)))))

(deftest delta-assert-extends-chain
  (let ((p (closure-program '(edge 1 2) '(edge 2 3))))
    (delta-is (assert-fact p '(edge 3 4))
              '((edge 3 4) (path 1 4) (path 2 4) (path 3 4))
              '())))

(deftest delta-retract-cuts-chain
  (let ((p (closure-program '(edge 1 2) '(edge 2 3) '(edge 3 4))))
    (delta-is (retract-fact p '(edge 2 3))
              '()
              '((edge 2 3) (path 1 3) (path 1 4) (path 2 3) (path 2 4)))
    (ok (equal (program-facts p :relation 'path) '((path 1 2) (path 3 4))))))

(deftest delta-alternative-derivation-survives
  (let ((p (closure-program '(edge 1 2) '(edge 2 4) '(edge 1 3) '(edge 3 4))))
    (delta-is (retract-fact p '(edge 2 4))
              '()
              '((edge 2 4) (path 2 4)))
    (ok (holds-p p '(path 1 4)) "re-derived through 3")))

(deftest delta-cycle-retraction
  (let ((p (closure-program '(edge 1 2) '(edge 2 3) '(edge 3 1))))
    (delta-is (retract-fact p '(edge 3 1))
              '()
              '((edge 3 1) (path 1 1) (path 2 1) (path 2 2) (path 3 1) (path 3 2) (path 3 3)))))

(deftest delta-negation-flips
  (requiring (:stratified-negation)
    (let ((p (make-test-program :rules *reach-rules*
                                :facts '((start 1) (node 1) (node 2) (node 3)
                                         (edge 1 2) (edge 2 3)))))
      (delta-is (retract-fact p '(edge 2 3))
                '((unreach 3))
                '((edge 2 3) (reach 3)))
      (delta-is (assert-fact p '(edge 1 3))
                '((edge 1 3) (reach 3))
                '((unreach 3))))))

(deftest delta-no-ops
  (let ((p (closure-program '(edge 1 2) '(edge 2 3))))
    (ok (delta-empty-p (assert-fact p '(edge 1 2))) "already a base fact")
    (ok (delta-empty-p (retract-fact p '(edge 7 8))) "not a base fact")
    (ok (delta-empty-p (retract-fact p '(path 1 3))) "derived, not base: retract ignores it")
    (ok (holds-p p '(path 1 3)))
    (ok (delta-empty-p (assert-fact p '(path 1 3))) "already in the model")
    (delta-is (retract-fact p '(edge 2 3))
              '()
              '((edge 2 3) (path 2 3)))
    (ok (holds-p p '(path 1 3)) "still a base fact")))

(deftest delta-assert-and-retract-same-fact
  (let ((p (closure-program '(edge 1 2))))
    (ok (delta-empty-p (update p :assert '((edge 1 2)) :retract '((edge 1 2)))))
    (ok (equal (program-base-facts p) '((edge 1 2))))
    (delta-is (update p :assert '((edge 2 3)) :retract '((edge 2 3)))
              '((edge 2 3) (path 1 3) (path 2 3))
              '())))

(deftest delta-rewire-in-one-update
  (let ((p (closure-program '(edge 1 2) '(edge 2 3))))
    (delta-is (update p :retract '((edge 2 3)) :assert '((edge 2 5) (edge 5 3)))
              '((edge 2 5) (edge 5 3) (path 1 5) (path 2 5) (path 5 3))
              '((edge 2 3)))))

(deftest delta-of-add-rules
  (let ((p (make-test-program :facts '((edge 1 2) (edge 2 3)))))
    (delta-is (add-rules p (closure-rules))
              '((path 1 2) (path 1 3) (path 2 3))
              '())))

(deftest delta-of-add-rule-with-negation
  (requiring (:stratified-negation)
    (let ((p (make-test-program :rules '((rule (on) :- (switch :on)))
                                :facts '((switch :on)))))
      (delta-is (add-rule p '(rule (off) :- (not (on))))
                '()
                '())
      (delta-is (retract-fact p '(switch :on))
                '((off))
                '((on) (switch :on))))))
