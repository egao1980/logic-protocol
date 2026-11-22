(defsystem "logic-protocol"
  :version "0.0.0"
  :description "CLOS logic protocol for cl-stack: facts, rules, queries, incremental update, proofs (Track L)"
  :author "egao1980"
  :license "MIT"
  :depends-on ()
  :serial t
  :pathname "src"
  :components ((:file "package"))
  :in-order-to ((test-op (test-op "logic-protocol/tests"))))

(defsystem "logic-protocol/tests"
  :depends-on ("logic-protocol" "rove")
  :pathname "tests"
  :serial t
  :components ((:file "package"))
  :perform (test-op (o c)
             (unless (symbol-call :rove :run c)
               (error "tests failed for ~A" (component-name c)))))
