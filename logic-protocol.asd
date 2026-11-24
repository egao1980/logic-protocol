(defsystem "logic-protocol"
  :version "0.2.0"
  :description "CLOS logic protocol for cl-stack: facts, rules, queries, incremental update, proofs (Track L)"
  :author "egao1980"
  :license "MIT"
  :depends-on ()
  :serial t
  :pathname "src"
  :components ((:file "package")
               (:file "terms")
               (:file "rules")
               (:file "conditions")
               (:file "model")
               (:file "budget")
               (:file "backend")
               (:file "program")
               (:file "weak"))
  :in-order-to ((test-op (test-op "logic-protocol/tests"))))

(defsystem "logic-protocol/tests"
  :description "Protocol tests: terms, rule syntax, safety, stratification, restarts, budgets, normalization, weak constraints (mock backend)"
  :depends-on ("logic-protocol" "rove")
  :pathname "tests"
  :serial t
  :components ((:file "package")
               (:file "support")
               (:file "term-test")
               (:file "rule-test")
               (:file "safety-test")
               (:file "stratify-test")
               (:file "backend-test")
               (:file "budget-test")
               (:file "model-test")
               (:file "weak-test"))
  :perform (test-op (o c)
             (unless (symbol-call :rove :run c)
               (error "tests failed for ~A" (component-name c)))))

(defsystem "logic-protocol/conformance"
  :description "Backend conformance suite: runs against *LOGIC-BACKEND* (see conformance/package.lisp)"
  :depends-on ("logic-protocol" "rove")
  :pathname "conformance"
  :serial t
  :components ((:file "package")
               (:file "support")
               (:file "eval-test")
               (:file "query-test")
               (:file "delta-test")
               (:file "incremental-test")
               (:file "explain-test")
               (:file "budget-test")
               (:file "time-step-test")
               (:file "ui-form-test")
               (:file "policy-test")
               (:file "determinism-test")
               (:file "weak-test")))
