(in-package #:logic-protocol/tests)

(deftest make-budget-checks
  (let ((b (make-budget :steps 5 :seconds 2)))
    (ok (= (budget-steps b) 5))
    (ok (= (budget-seconds b) 2)))
  (ok (null (budget-steps (make-budget))))
  (ok (signals (make-budget :steps -1) 'type-error))
  (ok (signals (make-budget :seconds -1) 'type-error))
  (ok (typep *logic-budget* 'logic-budget))
  (ok (integerp (budget-steps *logic-budget*)) "the default budget is finite"))

(deftest meter-designators
  (ok (eq (budget-meter-budget (make-budget-meter nil :query)) *logic-budget*))
  (let ((b (make-budget :steps 7)))
    (ok (eq (budget-meter-budget (make-budget-meter b :update)) b)))
  (ok (= (budget-steps (budget-meter-budget (make-budget-meter 5 :query))) 5))
  (let ((u (budget-meter-budget (make-budget-meter :unlimited :tick))))
    (ok (null (budget-steps u)))
    (ok (null (budget-seconds u))))
  (let ((m (make-budget-meter 5 :tick)))
    (ok (eq (budget-meter-operation m) :tick))
    (ok (= (budget-meter-steps m) 0))))

(deftest charge-within-budget
  (let ((m (make-budget-meter 3 :update)))
    (ok (null (charge-budget m)))
    (charge-budget m 2)
    (ok (= (budget-meter-steps m) 3))
    (ok (signals (charge-budget m) 'logic-budget-exceeded))))

(deftest charge-unlimited
  (let ((m (make-budget-meter :unlimited :update)))
    (charge-budget m 1000000)
    (ok (= (budget-meter-steps m) 1000000))))

(deftest exceeded-condition-slots
  (let ((m (make-budget-meter 3 :query)))
    (charge-budget m 3)
    (ok (handler-case (progn (charge-budget m) nil)
          (logic-budget-exceeded (c)
            (and (= (logic-error-steps c) 4)
                 (eq (logic-error-operation c) :query)
                 (eq (logic-error-budget c) (budget-meter-budget m))))))))

(deftest charge-continue-extends-once
  (let ((m (make-budget-meter 3 :update))
        (signalled 0))
    (handler-bind ((logic-budget-exceeded
                     (lambda (c) (incf signalled) (continue c))))
      (charge-budget m 3)
      (charge-budget m)                   ; 4 > 3: signalled, continued, limit 6
      (ok (= signalled 1))
      (charge-budget m 2)                 ; 6: within
      (ok (= signalled 1))
      (charge-budget m)                   ; 7 > 6: signalled again
      (ok (= signalled 2)))
    (ok (= (budget-meter-steps m) 7))))

(deftest charge-offers-continue
  (let ((m (make-budget-meter 0 :update)))
    (ok (signals-with-restarts (logic-budget-exceeded continue) (charge-budget m)))))

(deftest charge-deadline
  (let ((m (make-budget-meter (make-budget :seconds 0) :update)))
    (sleep 0.02)
    (ok (signals (charge-budget m) 'logic-budget-exceeded))))

(deftest charge-reports-partial
  (let ((m (make-budget-meter 0 :query)))
    (setf (budget-meter-partial-function m)
          (lambda () (list '((?x . 2)) '((?x . 1)) '((?x . 2)))))
    (ok (equal (handler-case (progn (charge-budget m) :none)
                 (logic-budget-exceeded (c) (logic-error-partial c)))
               '(((?x . 1)) ((?x . 2)))))))

(deftest front-use-value-rolls-back
  (let ((p (mock-program)))
    (update p :assert '((a 1)))
    (ok (eq (handler-bind ((logic-budget-exceeded (lambda (c) (use-value :stopped c))))
              (update p :assert '((b 1) (b 2) (b 3)) :budget 1))
            :stopped))
    (ok (equal (program-base-facts p) '((a 1))) "the update did not happen")
    (ok (eq (handler-bind ((logic-budget-exceeded (lambda (c) (use-value :stopped c))))
              (add-rules p '((rule (x ?v) :- (a ?v)) (rule (y ?v) :- (a ?v))) :budget 1))
            :stopped))
    (ok (null (program-rules p)) "no rule was added")))

(deftest front-continue-finishes
  (let ((p (mock-program)))
    (let ((d (handler-bind ((logic-budget-exceeded #'continue))
               (update p :assert '((b 1) (b 2) (b 3)) :budget 1))))
      (ok (equal (delta-added d) '((b 1) (b 2) (b 3)))))))

(deftest front-offers-use-value
  (let ((p (mock-program)))
    (ok (signals-with-restarts (logic-budget-exceeded continue use-value)
          (update p :assert '((b 1) (b 2)) :budget 1)))
    (ok (null (program-base-facts p)))))

(deftest query-budget-partial
  (let* ((mock (make-mock :answers '(((?x . 3)) ((?x . 1)) ((?x . 2))) :query-cost 1))
         (p (make-program :backend mock)))
    (let ((partial (handler-bind ((logic-budget-exceeded
                                    (lambda (c) (use-value (logic-error-partial c) c))))
                     (query p '(r ?x) :budget 2))))
      (ok (equal partial '(((?x . 1)) ((?x . 3))))
          "the answers found when the budget ran out, sorted"))))
