(in-package #:logic-protocol/conformance)

;;; Property: incremental maintenance equals recomputation from scratch.
;;; Random assert / retract sequences; after every UPDATE the model equals a
;;; fresh program's model on the same rules and base facts, and the delta is
;;; exactly the difference of the models before and after.

(defparameter *mixed-rules*
  (append (closure-rules)
          '((rule (hub ?x) :- (path ?x ?y) (path ?y ?x) (/= ?x ?y))
            (rule (lonely ?x) :- (node ?x) (not (hub ?x)))
            (rule (far ?x ?y) :- (path ?x ?y) (not (edge ?x ?y)) (< ?x ?y)))))

(defun program-kind-rules (kind)
  (ecase kind
    (:closure (closure-rules :right))
    (:nonlinear (closure-rules :nonlinear))
    (:reach *reach-rules*)
    (:mixed *mixed-rules*)))

(defun program-kind-features (kind)
  (if (member kind '(:reach :mixed)) '(:stratified-negation) '()))

(defun program-kind-fixed-facts (kind nodes)
  (ecase kind
    ((:closure :nonlinear) '())
    (:reach (cons '(start 1) (loop for n from 1 to nodes collect (list 'node n))))
    (:mixed (loop for n from 1 to nodes collect (list 'node n)))))

(defun random-update (rng nodes base-edges)
  "Random ASSERT and RETRACT lists: 0-3 new edges, 0-2 current ones."
  (let ((assert (random-edges rng nodes (funcall rng 4)))
        (retract (loop repeat (funcall rng 3)
                       when base-edges
                         collect (nth (funcall rng (length base-edges)) base-edges))))
    (values assert retract)))

(defun check-incremental (kind seed &key (nodes 7) (steps 40))
  "Run the property; return NIL when it holds, else a description of the
first failing step."
  (let* ((rng (make-rng seed))
         (p (make-test-program :rules (program-kind-rules kind)
                               :facts (program-kind-fixed-facts kind nodes))))
    (loop for step from 1 to steps
          do (multiple-value-bind (assert retract)
                 (random-update rng nodes (program-facts p :relation 'edge))
               (let* ((before (model p))
                      (delta (update p :assert assert :retract retract :budget :unlimited))
                      (after (model p))
                      (scratch (scratch-model p)))
                 (unless (equal after scratch)
                   (return (list :step step :assert assert :retract retract
                                 :model-not-scratch
                                 :missing (fact-difference scratch after)
                                 :extra (fact-difference after scratch))))
                 (unless (and (equal (delta-added delta) (fact-difference after before))
                              (equal (delta-removed delta) (fact-difference before after)))
                   (return (list :step step :assert assert :retract retract
                                 :wrong-delta
                                 :added (delta-added delta) :want-added (fact-difference after before)
                                 :removed (delta-removed delta) :want-removed (fact-difference before after))))
                 (when (member kind '(:closure :nonlinear))
                   (unless (equal (program-facts p :relation 'path)
                                  (oracle-closure (program-facts p :relation 'edge)))
                     (return (list :step step :not-the-closure)))))))))

(deftest-parametrize incremental-equals-scratch
    ((kind seed)
     (:closure 101) (:closure 102) (:closure 103) (:closure 104)
     (:nonlinear 201) (:nonlinear 202) (:nonlinear 203)
     (:reach 301) (:reach 302) (:reach 303) (:reach 304)
     (:mixed 401) (:mixed 402) (:mixed 403) (:mixed 404) (:mixed 405))
  (if (missing-features (program-kind-features kind))
      (skip "backend lacks negation")
      (let ((failure (check-incremental kind seed)))
        (ok (null failure) (format nil "~S seed ~D: ~S" kind seed failure)))))

(deftest incremental-rules-then-facts-then-rules
  ;; Adding rules to a populated program is also an incremental change.
  (requiring (:stratified-negation)
    (let* ((rng (make-rng 7))
           (p (make-test-program :facts (append (random-edges rng 8 14)
                                                (program-kind-fixed-facts :mixed 8)))))
      (loop for form in *mixed-rules*
            do (let* ((before (model p))
                      (delta (add-rule p form :budget :unlimited))
                      (after (model p)))
                 (ok (equal after (scratch-model p)))
                 (ok (equal (delta-added delta) (fact-difference after before)))
                 (ok (equal (delta-removed delta) (fact-difference before after))))))))

(deftest incremental-big-batch
  ;; Everything retracted at once, then re-asserted.
  (let* ((rng (make-rng 9))
         (edges (sort-facts (random-edges rng 10 25)))
         (p (make-test-program :rules (closure-rules :left) :facts edges))
         (full (model p)))
    (let ((d (update p :retract edges)))
      (ok (null (model p)))
      (ok (equal (delta-removed d) full)))
    (let ((d (update p :assert edges)))
      (ok (equal (model p) full))
      (ok (equal (delta-added d) full)))))
