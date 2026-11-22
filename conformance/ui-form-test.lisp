(in-package #:logic-protocol/conformance)

;;; The L3 shape: a sign-up form. Field input is base facts; enabled,
;;; visible and required are derived; each UPDATE's delta is exactly what to
;;; re-render (hx-swap-oob).

(defparameter *form-rules*
  '((rule (valid :email) :- (value :email ?v) (glob "*@*.*" ?v))
    (rule (filled ?f) :- (value ?f ?v) (/= ?v ""))
    (rule (visible :company) :- (value :account-type "business"))
    (rule (required :company) :- (visible :company))
    (rule (required :vat) :- (visible :company) (value :country ?c) (/= ?c "US"))
    (rule (invalid ?f) :- (required ?f) (not (filled ?f)))
    (rule (blocked) :- (invalid ?f))
    (rule (enabled :submit) :- (valid :email) (checked :terms) (not (blocked)))))

(defun form ()
  (make-test-program :rules *form-rules*))

(deftest form-starts-disabled
  (requiring (:stratified-negation)
    (let* ((p (form))
           (w (explain p '(enabled :submit))))
      (ok (null (model p)))
      (ok (typep w 'why-not))
      (ok (equal (mapcar (lambda (r) (list (reason-literal r) (reason-index r))) (why-not-reasons w))
                 '(((valid :email) 0)))))))

(deftest form-deltas
  (requiring (:stratified-negation)
    (let ((p (form)))
      (delta-is (assert-fact p '(value :email "ann@example.com"))
                '((filled :email) (valid :email) (value :email "ann@example.com"))
                '())
      (let ((w (explain p '(enabled :submit))))
        (ok (equal (mapcar #'reason-literal (why-not-reasons w)) '((checked :terms)))
            "Submit is disabled because terms are not checked"))
      (delta-is (assert-fact p '(checked :terms))
                '((checked :terms) (enabled :submit))
                '())
      (let ((d (assert-fact p '(value :account-type "business"))))
        (ok (equal (delta-added d)
                   '((blocked) (filled :account-type) (invalid :company) (required :company)
                     (value :account-type "business") (visible :company))))
        (ok (equal (delta-removed d) '((enabled :submit))))
        (ok (equal (delta-relations d) '(blocked enabled filled invalid required value visible))))
      (delta-is (assert-fact p '(value :company "ACME"))
                '((enabled :submit) (filled :company) (value :company "ACME"))
                '((blocked) (invalid :company))))))

(deftest form-delta-sorted
  ;; The same as the last step above, as one sorted list.
  (requiring (:stratified-negation)
    (let ((p (form)))
      (update p :assert '((value :email "ann@example.com") (checked :terms)
                          (value :account-type "business") (value :company "ACME")))
      (let ((d (update p :assert '((value :country "DE")))))
        (ok (equal (delta-added d)
                   '((blocked) (filled :country) (invalid :vat) (required :vat) (value :country "DE"))))
        (ok (equal (delta-removed d) '((enabled :submit))))))))

(deftest form-edit-a-field
  (requiring (:stratified-negation)
    (let ((p (form)))
      (update p :assert '((value :email "ann@example.com") (checked :terms)))
      (ok (holds-p p '(enabled :submit)))
      (delta-is (update p :retract '((value :email "ann@example.com"))
                          :assert '((value :email "ann")))
                '((value :email "ann"))
                '((enabled :submit) (valid :email) (value :email "ann@example.com")))
      (delta-is (update p :retract '((value :email "ann")) :assert '((value :email "")))
                '((value :email ""))
                '((filled :email) (value :email "ann"))))))

(deftest form-explains-enabled
  (requiring (:stratified-negation)
    (let ((p (form)))
      (update p :assert '((value :email "ann@example.com") (checked :terms)))
      (let ((proof (explain p '(enabled :submit))))
        (ok (equal (mapcar #'proof-fact (proof-premises proof)) '((valid :email) (checked :terms))))
        (ok (equal (proof-negated proof) '((blocked))))
        (ok (equal (proof-base-facts proof) '((checked :terms) (value :email "ann@example.com"))))))))

(deftest form-hidden-field-not-required
  (requiring (:stratified-negation)
    (let ((p (form)))
      (update p :assert '((value :account-type "personal")))
      (ok (not (holds-p p '(visible :company))))
      (ok (not (holds-p p '(required ?f))))
      (ok (null (query p '(invalid ?f)))))))
