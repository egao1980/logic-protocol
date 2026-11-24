(in-package #:logic-protocol/conformance)

;;; Weak constraints (logic-protocol 0.2.0). A backend without
;;; :WEAK-CONSTRAINTS refuses weak rules in ADD-RULE with
;;; LOGIC-UNSUPPORTED-RULE; on every backend, WEAK-INSTANCES grounds weak
;;; rules against the model, here one with derived relations. The expected
;;; instances were worked out by hand and cross-checked against an
;;; independent reference evaluator (naive stratified fixpoint, clingo's set
;;; semantics for instances).

(defparameter *weak-graph-rules*
  '((rule (reach ?x ?y) :- (edge ?x ?y))
    (rule (reach ?x ?z) :- (edge ?x ?y) (reach ?y ?z))
    (rule (cyclic ?x) :- (reach ?x ?x))))

(defparameter *weak-graph-facts*
  '((node 1) (node 2) (node 3) (node 4) (node 5)
    (edge 1 2) (edge 2 3) (edge 3 1) (edge 3 4)
    (cost 1 5) (cost 4 2)))

(defparameter *weak-cyclic* '(rule (weak 1 ?x) :- (cyclic ?x)))
(defparameter *weak-reach-cost* '(rule (weak (?c 1) ?x ?y) :- (reach ?x ?y) (cost ?y ?c) (/= ?x ?y)))
(defparameter *weak-acyclic* '(rule (weak 3 ?x) :- (node ?x) (not (cyclic ?x))))

(defun weak-graph-program ()
  (make-test-program :rules *weak-graph-rules* :facts *weak-graph-facts*))

(deftest weak-rules-need-the-feature
  (let* ((p (weak-graph-program))
         (backend (program-backend p))
         (before (model p)))
    (if (member :weak-constraints (backend-features backend))
        (progn
          (add-rule p *weak-cyclic*)
          (ok (eq (rule-kind (car (last (program-rules p)))) :weak)))
        (progn
          (ok (signals (add-rule p *weak-cyclic*) 'logic-unsupported-rule))
          (ok (handler-case (progn (add-rule p *weak-cyclic*) nil)
                (logic-unsupported-rule (c)
                  (and (eq (logic-error-feature c) :weak-constraints)
                       (eq (logic-error-backend c) backend)
                       (equal (rule-form (logic-error-rule c)) *weak-cyclic*)))))
          (handler-bind ((logic-unsupported-rule #'drop-rule))
            (add-rules p (list *weak-cyclic* '(rule (marked ?x) :- (cyclic ?x)))))
          (ok (equal (mapcar #'rule-form (program-rules p))
                     (append *weak-graph-rules* '((rule (marked ?x) :- (cyclic ?x)))))
              "DROP-RULE leaves the weak rule out and keeps the rest")
          (ok (equal (program-facts p :relation 'marked) '((marked 1) (marked 2) (marked 3))))
          (ok (null (fact-difference before (model p))) "the model only grew")))))

(deftest weak-instances-over-the-model
  (let* ((p (weak-graph-program))
         (rules-before (program-rules p))
         (model-before (model p)))
    (multiple-value-bind (instances groundings)
        (weak-instances p (list *weak-cyclic* *weak-reach-cost*))
      (ok (equal instances '((1 0 1) (1 0 2) (1 0 3)
                             (2 1 1 4) (2 1 2 4) (2 1 3 4)
                             (5 1 2 1) (5 1 3 1))))
      (ok (equal groundings '((((cyclic 1))) (((cyclic 2))) (((cyclic 3)))
                              (((reach 1 4) (cost 4 2) (/= 1 4)))
                              (((reach 2 4) (cost 4 2) (/= 2 4)))
                              (((reach 3 4) (cost 4 2) (/= 3 4)))
                              (((reach 2 1) (cost 1 5) (/= 2 1)))
                              (((reach 3 1) (cost 1 5) (/= 3 1))))))
      (ok (equal (weak-cost instances) '((1 . 16) (0 . 3)))))
    (ok (equal (program-rules p) rules-before) "the weak rules are not added")
    (ok (equal (model p) model-before))))

(deftest weak-instances-with-negation
  (requiring (:stratified-negation)
    (let ((p (weak-graph-program)))
      (multiple-value-bind (instances groundings)
          (weak-instances p (list *weak-cyclic* *weak-reach-cost* *weak-acyclic*))
        (ok (equal instances '((1 0 1) (1 0 2) (1 0 3)
                               (2 1 1 4) (2 1 2 4) (2 1 3 4)
                               (3 0 4) (3 0 5)
                               (5 1 2 1) (5 1 3 1))))
        (ok (equal (nth 6 groundings) '(((node 4) (not (cyclic 4))))))
        (ok (equal (weak-cost instances) '((1 . 16) (0 . 9))))))))

(deftest weak-instances-assume
  (requiring (:stratified-negation)
    (let* ((p (weak-graph-program))
           (model-before (model p)))
      (multiple-value-bind (instances groundings)
          (weak-instances p (list *weak-cyclic* *weak-reach-cost* *weak-acyclic*)
                          :assume '((edge 4 1)))
        (ok (equal instances '((1 0 1) (1 0 2) (1 0 3) (1 0 4)
                               (2 1 1 4) (2 1 2 4) (2 1 3 4)
                               (3 0 5)
                               (5 1 2 1) (5 1 3 1) (5 1 4 1))))
        (ok (equal (car (last groundings)) '(((reach 4 1) (cost 1 5) (/= 4 1)))))
        (ok (equal (weak-cost instances) '((1 . 21) (0 . 7)))))
      (ok (equal (model p) model-before) "the assumption is withdrawn"))))
