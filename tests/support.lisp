(in-package #:logic-protocol/tests)

;;; A mock backend: it stores rules and base facts, derives nothing, and
;;; records every GF call, so the protocol's own work (checks, restarts,
;;; migration, normalization, :ASSUME, budgets) is visible. Its model is its
;;; base facts. It returns lists unsorted on purpose.

(defclass mock-backend (logic-backend)
  ((name :initarg :name :initform :mock :reader mock-name)
   (features :initarg :features :initform '(:stratified-negation :time-step)
             :reader mock-features)
   (answers :initarg :answers :initform '() :accessor mock-answers
            :documentation "What BACKEND-QUERY returns, as given.")
   (query-cost :initarg :query-cost :initform 0 :accessor mock-query-cost)
   (calls :initform '() :accessor mock-calls)))

(defun make-mock (&rest initargs)
  (apply #'make-instance 'mock-backend initargs))

(defun calls (backend)
  "The calls recorded, oldest first."
  (reverse (mock-calls backend)))

(defun call-names (backend)
  (mapcar #'first (calls backend)))

(defstruct mock-state
  (rules '())
  (base (make-hash-table :test 'equal)))

(defmethod backend-name ((b mock-backend)) (mock-name b))
(defmethod backend-features ((b mock-backend)) (mock-features b))
(defmethod backend-make-state ((b mock-backend)) (make-mock-state))

(defun base-list (state)
  (loop for k being the hash-keys of (mock-state-base state) collect k))

(defmethod backend-add-rules ((b mock-backend) state rules meter)
  (push (list :add-rules (mapcar #'rule-form rules)) (mock-calls b))
  (dolist (r rules) (declare (ignore r)) (charge-budget meter))
  (setf (mock-state-rules state) (append (mock-state-rules state) rules))
  (make-delta))

(defmethod backend-update ((b mock-backend) state assert retract meter)
  (push (list :update assert retract) (mock-calls b))
  (let* ((table (mock-state-base state))
         (saved (let ((h (make-hash-table :test 'equal)))
                  (maphash (lambda (k v) (setf (gethash k h) v)) table)
                  h))
         (done nil))
    (unwind-protect
         (let ((before (base-list state)))
           (dolist (f retract) (charge-budget meter) (remhash f table))
           (dolist (f assert) (charge-budget meter) (setf (gethash f table) t))
           (let ((after (base-list state)))
             (prog1 (make-delta :added (reverse (set-difference after before :test #'equal))
                                :removed (reverse (set-difference before after :test #'equal)))
               (setf done t))))
      (unless done
        (setf (mock-state-base state) saved)))))

(defmethod backend-query ((b mock-backend) state pattern meter)
  (declare (ignore state))
  (push (list :query pattern) (mock-calls b))
  (let ((found '()))
    (setf (budget-meter-partial-function meter) (lambda () found))
    (dolist (a (mock-answers b))
      (dotimes (i (mock-query-cost b)) (charge-budget meter))
      (push a found))
    (mock-answers b)))

(defmethod backend-explain ((b mock-backend) state fact)
  (push (list :explain fact) (mock-calls b))
  (if (gethash fact (mock-state-base state))
      (make-instance 'proof :fact fact)
      (make-instance 'why-not :fact fact)))

(defmethod backend-tick ((b mock-backend) state meter)
  (declare (ignore meter))
  (push (list :tick) (mock-calls b))
  (let ((before (base-list state)))
    (clrhash (mock-state-base state))
    (make-delta :removed before)))

(defmethod backend-facts ((b mock-backend) state relation)
  (push (list :facts relation) (mock-calls b))
  (remove-if-not (lambda (f) (or (null relation) (eq (car f) relation)))
                 (base-list state)))

(defmethod backend-base-facts ((b mock-backend) state)
  (push (list :base-facts) (mock-calls b))
  (base-list state))

(defun mock-program (&rest initargs)
  (make-program :backend (apply #'make-mock initargs)))

(defmacro signals-with-restarts ((condition-type &rest restart-names) form)
  "Evaluate FORM inside OK's dynamic extent; return T when it signals
CONDITION-TYPE with every one of RESTART-NAMES active at that point.
Unwinds with a throw, so FORM never completes."
  (let ((c (gensym)) (tag (gensym)))
    `(catch ',tag
       (handler-bind ((,condition-type
                        (lambda (,c)
                          (throw ',tag
                            (and (every (lambda (n) (find-restart n ,c)) ',restart-names) t)))))
         ,form
         nil))))

(defun calls-of (backend &rest names)
  "The recorded calls named by NAMES (:update, :query, …), oldest first.
Lookups the protocol may make on its own (:facts, :base-facts) are not
part of what tests pin down."
  (remove-if-not (lambda (c) (member (first c) names)) (calls backend)))

(defun last-call (backend name)
  (car (last (calls-of backend name))))
