(in-package #:logic-protocol/conformance)

;;; The L1 shape: permit / forbid with forbid-overrides, default no
;;; decision, plan mode tightening. The policy's rules are data (base facts);
;;; each request is evaluated with :ASSUME, so the program is reused for
;;; every tool call and never changes.

(defparameter *policy-rules*
  '((rule (applies :permit ?id) :- (action ?a) (permit-rule ?id ?a ?pat) (resource ?r) (glob ?pat ?r))
    (rule (applies :forbid ?id) :- (action ?a) (forbid-rule ?id ?a ?pat) (resource ?r) (glob ?pat ?r))
    (rule (applies :forbid "plan-bash") :- (action "bash") (mode :plan) (not (sandbox :confined)))
    (rule (forbidden) :- (applies :forbid ?id))
    (rule (permitted) :- (applies :permit ?id))
    (rule (decision :forbid) :- (forbidden))
    (rule (decision :permit) :- (permitted) (not (forbidden)))
    (rule (decision :no-decision) :- (not (permitted)) (not (forbidden)))))

(defparameter *policy-data*
  '((permit-rule "r1" "bash" "git *")
    (permit-rule "r2" "read" "*")
    (forbid-rule "f1" "bash" "git push*")
    (forbid-rule "f2" "read" "*.env")))

(defun policy ()
  (make-test-program :rules *policy-rules* :facts *policy-data*))

(defun request-facts (action resource context)
  (list* (list 'action action) (list 'resource resource) context))

(defun decide (p action resource &optional context)
  (let ((answers (query p '(decision ?e) :assume (request-facts action resource context))))
    (and (= (length answers) 1) (cdr (assoc '?e (first answers))))))

(deftest-parametrize policy-decisions
    ((action resource context effect)
     ("bash" "git status" '() :permit)
     ("bash" "git push origin main" '() :forbid)
     ("bash" "rm -rf /" '() :no-decision)
     ("read" "src/a.lisp" '() :permit)
     ("read" ".env" '() :forbid)
     ("read" "config/prod.env" '() :forbid)
     ("write" "x" '() :no-decision)
     ("bash" "git status" '((mode :plan)) :forbid)
     ("bash" "git status" '((mode :plan) (sandbox :confined)) :permit)
     ("bash" "git push" '((mode :plan) (sandbox :confined)) :forbid)
     ("read" "a.env" '((mode :plan)) :forbid))
  (requiring (:stratified-negation)
    (let ((p (policy)))
      (ok (eq (decide p action resource context) effect))
      (ok (equal (model p) (scratch-model p)))
      (ok (equal (program-base-facts p) (sort-facts *policy-data*)) "the request left no trace"))))

(defun deciding-rule (proof)
  "The id of the first APPLIES fact under PROOF."
  (if (eq (first (proof-fact proof)) 'applies)
      (third (proof-fact proof))
      (some #'deciding-rule (proof-premises proof))))

(deftest policy-explains-decision
  (requiring (:stratified-negation)
    (let ((p (policy)))
      (let ((proof (explain p '(decision :forbid)
                            :assume (request-facts "bash" "git push origin" '()))))
        (ok (typep proof 'proof))
        (ok (equal (deciding-rule proof) "f1"))
        (ok (member '(glob "git push*" "git push origin") (proof-builtins (first (proof-premises (first (proof-premises proof)))))
                    :test #'equal)))
      (let ((proof (explain p '(decision :permit)
                            :assume (request-facts "bash" "git status" '()))))
        (ok (equal (deciding-rule proof) "r1"))
        (ok (equal (proof-negated proof) '((forbidden)))))
      (let ((w (explain p '(decision :permit)
                        :assume (request-facts "bash" "git status" '((mode :plan))))))
        (ok (typep w 'why-not))
        (ok (equal (mapcar #'reason-literal (why-not-reasons w)) '((not (forbidden)))))))))

(deftest policy-many-requests
  ;; One program, many tool calls: answers stay right and the program is
  ;; unchanged.
  (requiring (:stratified-negation)
    (let ((p (policy))
          (rng (make-rng 77))
          (resources #("git status" "git push x" "a.env" "src/x.lisp" "rm x")))
      (dotimes (i 200)
        (let* ((action (if (zerop (funcall rng 2)) "bash" "read"))
               (resource (aref resources (funcall rng (length resources))))
               (plan (zerop (funcall rng 3)))
               (context (if plan '((mode :plan)) '()))
               (fresh (make-test-program :rules *policy-rules*
                                         :facts (append *policy-data*
                                                        (request-facts action resource context))))
               (want (cdr (assoc '?e (first (query fresh '(decision ?e)))))))
          (unless (eq (decide p action resource context) want)
            (ok nil (format nil "~S ~S ~S" action resource context)))))
      (ok (equal (program-base-facts p) (sort-facts *policy-data*))))))

(deftest policy-rule-changes-are-incremental
  (requiring (:stratified-negation)
    (let ((p (policy)))
      (ok (eq (decide p "write" "notes.md") :no-decision))
      (assert-fact p '(permit-rule "w1" "write" "*.md"))
      (ok (eq (decide p "write" "notes.md") :permit))
      (assert-fact p '(forbid-rule "w2" "write" "notes*"))
      (ok (eq (decide p "write" "notes.md") :forbid))
      (retract-fact p '(forbid-rule "w2" "write" "notes*"))
      (ok (eq (decide p "write" "notes.md") :permit)))))
