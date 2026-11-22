;;; Backend conformance suite for logic-protocol.
;;;
;;; Every test here runs against the backend in *LOGIC-BACKEND* at run time.
;;; A backend's own test system depends on "logic-protocol/conformance" and
;;; runs it with its backend bound, e.g. in its TEST-OP:
;;;
;;;   (let ((logic-protocol:*logic-backend* (make-my-backend)))
;;;     (rove:run "logic-protocol/conformance"))
;;;
;;; Tests that need a feature the backend lacks (BACKEND-FEATURES) are
;;; skipped, so an ASP (L5) or Prolog (L6) backend runs the subset it
;;; supports. Results are compared exactly: the protocol fixes the order of
;;; every list.

(defpackage #:logic-protocol/conformance
  (:use #:cl #:rove #:logic-protocol)
  (:export #:make-test-program #:model #:scratch-model))

(in-package #:logic-protocol/conformance)
