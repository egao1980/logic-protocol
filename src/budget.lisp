(in-package #:logic-protocol)

;;; Budgets (brief: "Budget", locked). Every budgeted operation runs under a
;;; LOGIC-BUDGET: a step limit, a wall-clock limit, or both (NIL = no limit of
;;; that kind). A budget designator, accepted by every :BUDGET argument:
;;;
;;;   NIL          *LOGIC-BUDGET*
;;;   an integer   (make-budget :steps N)
;;;   :UNLIMITED   no limit at all
;;;   a LOGIC-BUDGET
;;;
;;; The front function makes one BUDGET-METER per call and hands it to the
;;; backend GF. The backend calls CHARGE-BUDGET as it works. What a step is
;;; is the backend's, within these bounds: at least one step per fact added
;;; to or removed from the model (including DRed's over-deletions and
;;; re-derivations) and per answer a query produces, at most a constant
;;; number per rule-body match. So a small budget always stops a large
;;; closure, and a large one never stops a small program.

(defclass logic-budget ()
  ((steps :initarg :steps :initform nil :reader budget-steps)
   (seconds :initarg :seconds :initform nil :reader budget-seconds)))

(defmethod print-object ((b logic-budget) stream)
  (print-unreadable-object (b stream :type t)
    (format stream "steps ~S seconds ~S" (budget-steps b) (budget-seconds b))))

(defun make-budget (&key steps seconds)
  (check-type steps (or null (integer 0)))
  (check-type seconds (or null (real 0)))
  (make-instance 'logic-budget :steps steps :seconds seconds))

(defvar *logic-budget* (make-budget :steps 10000000)
  "The budget of an operation called with no :BUDGET (or :BUDGET NIL). Finite,
so that rules an agent writes always terminate.")

(defclass budget-meter ()
  ((budget :initarg :budget :reader budget-meter-budget
           :documentation "The LOGIC-BUDGET the designator resolved to.")
   (operation :initarg :operation :reader budget-meter-operation)
   (steps :initform 0 :accessor budget-meter-steps
          :documentation "Steps charged so far.")
   (partial-function :initform nil :accessor budget-meter-partial-function
                     :documentation "NIL, or a function of no arguments the backend
sets during a query: it returns the bindings found so far (any order,
duplicates allowed); CHARGE-BUDGET sorts them into LOGIC-ERROR-PARTIAL.")
   ;; Internal (not exported; the implementation may change these): the
   ;; current step limit and deadline (internal real time), the program
   ;; reported in the condition, and the query's variables, for sorting the
   ;; partial answers.
   (limit :initform nil :accessor %meter-limit)
   (deadline :initform nil :accessor %meter-deadline)
   (program :initform nil :accessor %meter-program)
   (variables :initform nil :accessor %meter-variables)))

(defun make-budget-meter (designator operation)
  "A fresh meter for one OPERATION (:ADD-RULES, :UPDATE, :QUERY or :TICK)
under the budget DESIGNATOR. The wall-clock limit starts now."
  (let* ((budget (resolve-budget designator))
         (meter (make-instance 'budget-meter :budget budget :operation operation)))
    (setf (%meter-limit meter) (budget-steps budget)
          (%meter-deadline meter) (%budget-deadline budget))
    meter))

(defun resolve-budget (designator)
  "The LOGIC-BUDGET a budget designator (see the file header) stands for."
  (etypecase designator
    (null *logic-budget*)
    (logic-budget designator)
    ((integer 0) (make-budget :steps designator))
    ((eql :unlimited) (make-budget))))

(defun %budget-deadline (budget)
  (let ((seconds (budget-seconds budget)))
    (and seconds
         (+ (get-internal-real-time)
            (round (* seconds internal-time-units-per-second))))))

(defun normalize-answers (answers variables)
  "ANSWERS (binding alists, any order, duplicates allowed) projected onto
VARIABLES, without duplicates, sorted by their values in VARIABLES order
with TERM<."
  (let ((projected (mapcar (lambda (a)
                             (mapcar (lambda (v) (cons v (cdr (assoc v a)))) variables))
                           answers)))
    (stable-sort (%dedupe projected) #'%terms< :key (lambda (a) (mapcar #'cdr a)))))

(defun %partial-answers (meter)
  (let ((fn (budget-meter-partial-function meter)))
    (when (and fn (eq (budget-meter-operation meter) :query))
      (let ((answers (funcall fn)))
        (normalize-answers answers (or (%meter-variables meter)
                                       (mapcar #'car (first answers))))))))

(defun charge-budget (meter &optional (steps 1))
  "Charge STEPS to METER. When the step count passes the limit, or the
deadline has passed, signal LOGIC-BUDGET-EXCEEDED (BUDGET, STEPS so far,
OPERATION, PARTIAL) with a CONTINUE restart established here: CONTINUE adds
one more full allowance of the original budget (steps and seconds, the new
deadline counted from now) and returns, and the work goes on. It may be
signalled again later. Returns NIL."
  (incf (budget-meter-steps meter) steps)
  (let ((limit (%meter-limit meter))
        (deadline (%meter-deadline meter)))
    (when (or (and limit (> (budget-meter-steps meter) limit))
              (and deadline (> (get-internal-real-time) deadline)))
      (restart-case
          (error 'logic-budget-exceeded
                 :budget (budget-meter-budget meter)
                 :steps (budget-meter-steps meter)
                 :operation (budget-meter-operation meter)
                 :program (%meter-program meter)
                 :partial (%partial-answers meter))
        (continue ()
          :report "Grant one more allowance of the budget and keep computing."
          (let ((budget (budget-meter-budget meter)))
            (when limit
              (setf (%meter-limit meter)
                    (max (+ limit (budget-steps budget)) (budget-meter-steps meter))))
            (setf (%meter-deadline meter) (%budget-deadline budget)))))))
  nil)
