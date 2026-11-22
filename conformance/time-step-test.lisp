(in-package #:logic-protocol/conformance)

;;; Time-step rules (Dedalus): a sign-up wizard as a state machine.

(defparameter *wizard-rules*
  '((rule (next (state ?s2)) :- (state ?s1) (event ?e) (step ?s1 ?e ?s2))
    (rule (moved) :- (state ?s1) (event ?e) (step ?s1 ?e ?s2))
    (rule (next (state ?s)) :- (state ?s) (not (moved)))
    (rule (next (step ?a ?e ?b)) :- (step ?a ?e ?b))
    (rule (can-go ?e) :- (state ?s) (step ?s ?e ?s2))))

(defparameter *wizard-table*
  '((step :start :next :details)
    (step :details :next :confirm)
    (step :details :back :start)
    (step :confirm :next :done)
    (step :confirm :back :details)))

(defun wizard ()
  (make-test-program :rules *wizard-rules*
                     :facts (cons '(state :start) *wizard-table*)))

(defun current-state (p)
  (mapcar #'second (program-facts p :relation 'state)))

(deftest wizard-steps
  (requiring (:time-step :stratified-negation)
    (let ((p (wizard)))
      (ok (= (program-time p) 0))
      (ok (equal (current-state p) '(:start)))
      (tick p)
      (ok (= (program-time p) 1))
      (ok (equal (current-state p) '(:start)) "no event: the state persists by rule")
      (loop for event in '(:next :next :back :next :next :next)
            for want in '(:details :confirm :details :confirm :done :done)
            for time from 2
            do (assert-fact p (list 'event event))
               (tick p)
               (ok (equal (current-state p) (list want)) (format nil "after ~S" event))
               (ok (= (program-time p) time))
               (ok (null (program-facts p :relation 'event)) "events do not persist")
               (ok (equal (program-facts p :relation 'step) (sort-facts *wizard-table*))
                   "the table persists through its rule")))))

(deftest wizard-tick-delta
  (requiring (:time-step :stratified-negation)
    (let ((p (wizard)))
      (ok (equal (program-facts p :relation 'can-go) '((can-go :next))))
      (assert-fact p '(event :next))
      (ok (holds-p p '(moved)))
      (let ((d (tick p)))
        (ok (equal (delta-added d) '((can-go :back) (state :details))))
        (ok (equal (delta-removed d) '((event :next) (moved) (state :start))))))))

(deftest base-facts-need-persistence-rules
  (requiring (:time-step)
    (let ((p (make-test-program :rules '((rule (next (kept ?x)) :- (kept ?x)))
                                :facts '((kept 1) (note "hello")))))
      (let ((d (tick p)))
        (ok (equal (program-base-facts p) '((kept 1))))
        (ok (equal (delta-removed d) '((note "hello"))))
        (ok (null (delta-added d)))))
    (let ((p (make-test-program :facts '((a 1) (b 2)))))
      (tick p)
      (ok (null (model p)) "with no :NEXT rules nothing carries over"))))

(deftest next-rules-see-the-whole-state
  (requiring (:time-step)
    (let ((p (make-test-program
              :rules '((rule (next (count ?n)) :- (count ?m) (succ ?m ?n))
                       (rule (next (succ ?a ?b)) :- (succ ?a ?b)))
              :facts '((count 0) (succ 0 1) (succ 1 2) (succ 2 3)))))
      (tick p)
      (ok (equal (program-facts p :relation 'count) '((count 1))))
      (tick p)
      (tick p)
      (ok (equal (program-facts p :relation 'count) '((count 3))))
      (tick p)
      (ok (null (program-facts p :relation 'count)) "no successor: the count stops existing"))))

(deftest negation-across-time-is-stratified
  ;; (not (p)) in a :NEXT rule is no cycle: a toggle.
  (requiring (:time-step :stratified-negation)
    (let ((p (make-test-program :rules '((rule (next (p)) :- (not (p)))))))
      (ok (not (holds-p p '(p))))
      (tick p)
      (ok (holds-p p '(p)))
      (tick p)
      (ok (not (holds-p p '(p))))
      (tick p)
      (ok (holds-p p '(p))))))

(deftest next-facts-are-base-at-the-next-step
  (requiring (:time-step :stratified-negation)
    (let ((p (wizard)))
      (assert-fact p '(event :next))
      (tick p)
      (ok (proof-base-p (explain p '(state :details))))
      (ok (equal (rule-form (proof-rule (explain p '(can-go :back))))
                 '(rule (can-go ?e) :- (state ?s) (step ?s ?e ?s2)))))))

(deftest incremental-after-ticks
  (requiring (:time-step :stratified-negation)
    (let ((p (wizard)))
      (dolist (e '(:next :next :back))
        (assert-fact p (list 'event e))
        (tick p)
        (ok (equal (model p) (scratch-model p)) "the model after a tick equals a fresh evaluation")))))
