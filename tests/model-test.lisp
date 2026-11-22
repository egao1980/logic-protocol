(in-package #:logic-protocol/tests)

(defun base (fact) (make-instance 'proof :fact fact))

(deftest proof-model
  (let* ((r1 (parse-rule '(rule (path ?x ?y) :- (edge ?x ?y))))
         (r2 (parse-rule '(rule (path ?x ?z) :- (edge ?x ?y) (path ?y ?z))))
         (p23 (make-instance 'proof :fact '(path 2 3) :rule r1
                                    :premises (list (base '(edge 2 3)))
                                    :bindings '((?x . 2) (?y . 3))))
         (p13 (make-instance 'proof :fact '(path 1 3) :rule r2
                                    :premises (list (base '(edge 1 2)) p23)
                                    :bindings '((?x . 1) (?z . 3) (?y . 2)))))
    (ok (proof-base-p (base '(edge 1 2))))
    (ok (not (proof-base-p p13)))
    (ok (= (proof-height (base '(edge 1 2))) 0))
    (ok (= (proof-height p23) 1))
    (ok (= (proof-height p13) 2))
    (ok (equal (proof-base-facts p13) '((edge 1 2) (edge 2 3))))
    (ok (equal (proof-base-facts (base '(edge 1 2))) '((edge 1 2))))
    (let ((twice (make-instance 'proof :fact '(both 1) :rule r1
                                       :premises (list (base '(z 1)) (base '(a 1)) (base '(z 1))))))
      (ok (equal (proof-base-facts twice) '((a 1) (z 1)))))))

(deftest delta-model
  (let ((d (make-delta :added '((value :email "a") (valid :email))
                       :removed '((enabled :submit) (valid :phone)))))
    (ok (not (delta-empty-p d)))
    (ok (equal (delta-relations d) '(enabled valid value))))
  (ok (delta-empty-p (make-delta)))
  (ok (null (delta-relations (make-delta)))))
