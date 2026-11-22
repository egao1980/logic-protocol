(in-package #:logic-protocol/conformance)

;;; Evaluation: transitive closure, same generation, stratified negation,
;;; built-ins.

(deftest closure-chain
  (let ((p (make-test-program :rules (closure-rules)
                              :facts '((edge 1 2) (edge 2 3) (edge 3 4)))))
    (ok (equal (program-facts p :relation 'path)
               '((path 1 2) (path 1 3) (path 1 4) (path 2 3) (path 2 4) (path 3 4))))
    (ok (equal (model p)
               '((edge 1 2) (edge 2 3) (edge 3 4)
                 (path 1 2) (path 1 3) (path 1 4) (path 2 3) (path 2 4) (path 3 4))))))

(deftest closure-cycle
  (let ((p (make-test-program :rules (closure-rules)
                              :facts '((edge 1 2) (edge 2 3) (edge 3 1)))))
    (ok (equal (program-facts p :relation 'path)
               (loop for a from 1 to 3 nconc (loop for b from 1 to 3 collect (list 'path a b)))))))

(deftest-parametrize closure-random
    ((kind seed)
     (:right 1) (:right 2) (:right 3)
     (:left 4) (:left 5) (:left 6)
     (:nonlinear 7) (:nonlinear 8) (:nonlinear 9))
  (let* ((rng (make-rng seed))
         (edges (random-edges rng 12 20))
         (p (make-test-program :rules (closure-rules kind) :facts edges)))
    (ok (equal (program-facts p :relation 'path) (oracle-closure edges)))
    (ok (equal (program-facts p :relation 'edge) (sort-facts edges)))))

(defparameter *family*
  ;; (parent CHILD PARENT): a has b, c; b has d, e; c has f; f has g.
  '((person :a) (person :b) (person :c) (person :d) (person :e) (person :f) (person :g)
    (parent :b :a) (parent :c :a) (parent :d :b) (parent :e :b) (parent :f :c)
    (parent :g :f)))

(deftest same-generation
  (let ((p (make-test-program :rules *same-generation-rules* :facts *family*)))
    (ok (equal (program-facts p :relation 'sg)
               (sort-facts
                (append (mapcar (lambda (x) (list 'sg x x)) '(:a :b :c :d :e :f :g))
                        '((sg :b :c) (sg :c :b)
                          (sg :d :e) (sg :e :d) (sg :d :f) (sg :f :d) (sg :e :f) (sg :f :e))))))))

(deftest-parametrize same-generation-random
    ((seed) (11) (12) (13))
  ;; A random tree: node i > 1 gets a parent below it. Same generation in a
  ;; one-rooted tree = same depth.
  (let* ((rng (make-rng seed))
         (n 14)
         (parent (make-array (1+ n) :initial-element nil))
         (depth (make-array (1+ n) :initial-element 0))
         (facts (list '(person 1))))
    (loop for i from 2 to n
          do (let ((par (1+ (funcall rng (1- i)))))
               (setf (aref parent i) par
                     (aref depth i) (1+ (aref depth par)))
               (push (list 'person i) facts)
               (push (list 'parent i par) facts)))
    (let ((p (make-test-program :rules *same-generation-rules* :facts facts)))
      (ok (equal (program-facts p :relation 'sg)
                 (sort-facts (loop for a from 1 to n
                                   nconc (loop for b from 1 to n
                                               when (= (aref depth a) (aref depth b))
                                                 collect (list 'sg a b)))))))))

(deftest negation-unreachable
  (requiring (:stratified-negation)
    (let* ((edges '((edge 1 2) (edge 2 3) (edge 4 5)))
           (p (make-test-program
               :rules *reach-rules*
               :facts (append edges '((start 1)) (loop for n from 1 to 5 collect (list 'node n))))))
      (ok (equal (program-facts p :relation 'unreach) '((unreach 4) (unreach 5))))
      (ok (equal (program-facts p :relation 'reach) '((reach 1) (reach 2) (reach 3)))))))

(deftest-parametrize negation-random
    ((seed) (21) (22) (23) (24))
  (requiring (:stratified-negation)
    (let* ((rng (make-rng seed))
           (edges (random-edges rng 10 12))
           (nodes (loop for n from 1 to 10 collect n))
           (p (make-test-program
               :rules *reach-rules*
               :facts (append edges '((start 1)) (mapcar (lambda (n) (list 'node n)) nodes)))))
      (ok (equal (append (program-facts p :relation 'reach) (program-facts p :relation 'unreach))
                 (oracle-reach edges '(1) nodes))))))

(deftest negation-three-strata
  (requiring (:stratified-negation)
    (let ((p (make-test-program
              :rules '((rule (c ?x) :- (n ?x) (c0 ?x))
                       (rule (b ?x) :- (n ?x) (not (c ?x)))
                       (rule (a ?x) :- (n ?x) (not (b ?x))))
              :facts '((n 1) (n 2) (c0 1)))))
      (ok (equal (program-facts p :relation 'c) '((c 1))))
      (ok (equal (program-facts p :relation 'b) '((b 2))))
      (ok (equal (program-facts p :relation 'a) '((a 1)))))))

(deftest negation-of-derived-zero-arity
  (requiring (:stratified-negation)
    (let ((p (make-test-program
              :rules '((rule (alarm) :- (temp ?t) (> ?t 30))
                       (rule (calm) :- (not (alarm))))
              :facts '((temp 25)))))
      (ok (equal (model p) '((calm) (temp 25))))
      (update p :assert '((temp 31)))
      (ok (equal (model p) '((alarm) (temp 25) (temp 31)))))))

(deftest-parametrize builtins
    ((literal holds)
     ('(= 1 1) t) ('(= "a" "a") t) ('(= :a "a") nil) ('(= "A" "a") nil)
     ('(/= 1 2) t) ('(/= :a :a) nil)
     ('(< 1 2) t) ('(< 2 1) nil) ('(< 1 1) nil) ('(< "a" "b") t) ('(< 1 "b") nil) ('(< :a :b) nil)
     ('(<= 2 2) t) ('(<= "b" "a") nil)
     ('(> 3 2) t) ('(> "b" "a") t)
     ('(>= 2 3) nil) ('(>= 3 3) t)
     ('(glob "*.lisp" "src/a.lisp") t)
     ('(glob "a?c" "abc") t) ('(glob "a?c" "ac") nil)
     ('(glob "*" "") t) ('(glob "ab" "abc") nil) ('(glob "*b" "abc") nil)
     ('(glob "*@*.*" "x@y.z") t) ('(glob "*@*.*" "x@yz") nil)
     ('(glob "a[b" "a[b") t) ('(glob "git *" "git push origin") t)
     ('(glob "a*" :abc) nil)
     ('(prefix "src/" "src/a") t) ('(prefix "src/" "lib/a") nil)
     ('(prefix "" "x") t) ('(prefix "ab" "a") nil) ('(prefix "a" :a) nil))
  (let ((p (make-test-program)))
    (ok (eq (and (holds-p p literal) t) holds))
    (ok (eq (and (holds-p p (list 'and '(one) literal)
                          :assume '((one)))
                 t)
            holds))))

(deftest builtin-in-rule-body
  (let ((p (make-test-program
            :rules '((rule (source ?f) :- (file ?f) (glob "*.lisp" ?f) (not (prefix "tmp/" ?f)))
                     (rule (big ?f) :- (size ?f ?n) (>= ?n 100))
                     (rule (alias ?a ?f) :- (file ?f) (= ?a ?f)))
            :facts '((file "a.lisp") (file "tmp/b.lisp") (file "c.txt")
                     (size "a.lisp" 50) (size "c.txt" 100)))))
    (ok (equal (program-facts p :relation 'source) '((source "a.lisp"))))
    (ok (equal (program-facts p :relation 'big) '((big "c.txt"))))
    (ok (equal (program-facts p :relation 'alias)
               '((alias "a.lisp" "a.lisp") (alias "c.txt" "c.txt") (alias "tmp/b.lisp" "tmp/b.lisp"))))))

(deftest empty-body-rule
  (let ((p (make-test-program :rules '((rule (enabled :help))))))
    (ok (equal (model p) '((enabled :help))))
    (ok (holds-p p '(enabled :help)))))

(deftest constants-are-distinct
  (let ((p (make-test-program
            :rules '((rule (known ?u) :- (user ?u)))
            :facts '((user "Ann") (user "ann") (user :ann) (user ann) (user 1)))))
    (ok (= (length (program-facts p :relation 'known)) 5))
    (ok (holds-p p '(known "Ann")))
    (ok (not (holds-p p '(known "ANN"))))))

(deftest rules-added-after-facts
  (let ((p (make-test-program :facts '((edge 1 2) (edge 2 3)))))
    (add-rules p (closure-rules))
    (ok (equal (program-facts p :relation 'path) '((path 1 2) (path 1 3) (path 2 3))))
    (add-rule p '(rule (twice ?x ?z) :- (path ?x ?y) (path ?y ?z)))
    (ok (equal (program-facts p :relation 'twice) '((twice 1 3))))))
