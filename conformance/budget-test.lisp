(in-package #:logic-protocol/conformance)

;;; Budgets: a large closure under a small budget signals
;;; LOGIC-BUDGET-EXCEEDED; CONTINUE finishes; USE-VALUE returns the value and
;;; leaves the program as it was.

(defun chain-edges (n)
  (loop for i from 1 below n collect (list 'edge i (1+ i))))

(defun chain-closure-size (n) (/ (* n (1- n)) 2))

(deftest budget-update-signals
  (let ((p (make-test-program :rules (closure-rules))))
    (ok (signals (update p :assert (chain-edges 60) :budget 100) 'logic-budget-exceeded))
    (ok (handler-case (progn (update p :assert (chain-edges 60) :budget 100) nil)
          (logic-budget-exceeded (c)
            (and (eq (logic-error-operation c) :update)
                 (> (logic-error-steps c) 100)
                 (eq (logic-error-program c) p)))))
    (ok (null (model p)) "an abandoned update leaves nothing behind")))

(deftest budget-update-offers-restarts
  (let ((p (make-test-program :rules (closure-rules))))
    (ok (catch 'restarts
          (handler-bind ((logic-budget-exceeded
                           (lambda (c)
                             (throw 'restarts
                               (and (find-restart 'continue c) (find-restart 'use-value c) t)))))
            (update p :assert (chain-edges 60) :budget 100)
            nil)))))

(deftest budget-continue-finishes
  (let* ((p (make-test-program :rules (closure-rules)))
         (signalled 0)
         (delta (handler-bind ((logic-budget-exceeded
                                 (lambda (c) (incf signalled) (continue c))))
                  (update p :assert (chain-edges 60) :budget 100))))
    (ok (> signalled 0))
    (ok (= (length (program-facts p :relation 'path)) (chain-closure-size 60)))
    (ok (equal (model p) (scratch-model p)))
    (ok (equal (delta-added delta) (model p)))))

(deftest budget-use-value-rolls-back
  (let ((p (make-test-program :rules (closure-rules) :facts '((edge 100 101)))))
    (let ((before (model p)))
      (ok (eq (handler-bind ((logic-budget-exceeded (lambda (c) (use-value :stopped c))))
                (update p :assert (chain-edges 60) :budget 100))
              :stopped))
      (ok (equal (model p) before))
      (ok (equal (program-base-facts p) '((edge 100 101)))))
    (ok (equal (delta-added (assert-fact p '(edge 101 102)))
               '((edge 101 102) (path 100 102) (path 101 102)))
        "the program still works incrementally afterwards")))

(deftest budget-add-rules
  (let ((p (make-test-program :facts (chain-edges 60))))
    (ok (signals (add-rules p (closure-rules) :budget 50) 'logic-budget-exceeded))
    (ok (eq (handler-bind ((logic-budget-exceeded (lambda (c) (use-value :stopped c))))
              (add-rules p (closure-rules) :budget 50))
            :stopped))
    (ok (null (program-rules p)))
    (ok (equal (model p) (sort-facts (chain-edges 60))))))

(deftest budget-query-partial
  (let* ((p (make-test-program :rules (closure-rules) :facts (chain-edges 30)))
         (full (query p '(path ?x ?y) :budget :unlimited)))
    (ok (= (length full) (chain-closure-size 30)))
    (ok (signals (query p '(path ?x ?y) :budget 10) 'logic-budget-exceeded))
    (let ((partial (handler-bind ((logic-budget-exceeded
                                    (lambda (c) (use-value (logic-error-partial c) c))))
                     (query p '(path ?x ?y) :budget 10))))
      (ok (listp partial))
      (ok (< (length partial) (length full)))
      (ok (every (lambda (b) (member b full :test #'equal)) partial) "a subset of the answer")
      (ok (equal partial (remove-if-not (lambda (b) (member b partial :test #'equal)) full))
          "in the answer's order"))
    (let ((answers (handler-bind ((logic-budget-exceeded #'continue))
                     (query p '(path ?x ?y) :budget 10))))
      (ok (equal answers full)))))

(deftest budget-small-program-fits
  (let ((p (make-test-program :rules (closure-rules))))
    (update p :assert (chain-edges 5) :budget 1000)
    (ok (= (length (program-facts p :relation 'path)) 10))
    (ok (holds-p p '(path 1 5) :budget 1000))))

(deftest budget-tick
  (requiring (:time-step)
    (let ((p (make-test-program
              :rules (append (closure-rules)
                             '((rule (next (edge ?x ?y)) :- (seed ?x ?y)))))))
      ;; the next state holds the whole chain, so its closure must be computed
      (update p :assert (mapcar (lambda (e) (cons 'seed (cdr e))) (chain-edges 40))
                :budget :unlimited)
      (ok (signals (tick p :budget 20) 'logic-budget-exceeded))
      (let ((before (model p)))
        (ok (eq (handler-bind ((logic-budget-exceeded (lambda (c) (use-value :stopped c))))
                  (tick p :budget 20))
                :stopped))
        (ok (= (program-time p) 0) "an abandoned tick does not advance time")
        (ok (equal (model p) before))))))
