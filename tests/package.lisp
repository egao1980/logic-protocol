(defpackage #:logic-protocol/tests
  (:use #:cl #:rove))

(in-package #:logic-protocol/tests)

(deftest package-exists
  (ok (find-package :logic-protocol)))
