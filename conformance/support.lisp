(in-package #:logic-protocol/conformance)

;;; Helpers: programs on the current backend, feature guards, a portable
;;; seeded generator, oracles computed without the backend.

(defun missing-features (features)
  (set-difference features (backend-features *logic-backend*)))

(defmacro requiring ((&rest features) &body body)
  "Run BODY when the backend has every one of FEATURES, else skip."
  (let ((missing (gensym)))
    `(let ((,missing (missing-features ',features)))
       (if ,missing
           (skip (format nil "backend ~S lacks ~{~S~^, ~}"
                         (backend-name *logic-backend*) ,missing))
           (progn ,@body)))))

(defun make-test-program (&key rules facts)
  (make-program :rules rules :facts facts :budget :unlimited))

(defun model (program)
  (program-facts program))

(defun scratch-model (program)
  "The model of a fresh program with PROGRAM's rules and base facts."
  (model (make-program :rules (program-rules program)
                       :facts (program-base-facts program)
                       :budget :unlimited)))

(defun fact-difference (a b)
  "Facts of A not in B, sorted."
  (sort-facts (set-difference a b :test #'equal)))

;;; Seeded generator: a 31-bit LCG (same numbers on every implementation).

(defun make-rng (seed)
  (let ((state (mod (+ (* seed 7919) 1) 2147483648)))
    (lambda (n)
      (setf state (mod (+ (* state 1103515245) 12345) 2147483648))
      (mod (ash state -8) n))))

(defun random-edges (rng nodes count)
  "COUNT random (edge A B) facts over 1..NODES, possibly with repeats."
  (loop repeat count
        collect (list 'edge (1+ (funcall rng nodes)) (1+ (funcall rng nodes)))))

(defun shuffle (rng list)
  (let ((v (coerce list 'vector)))
    (loop for i from (1- (length v)) downto 1
          do (rotatef (aref v i) (aref v (funcall rng (1+ i)))))
    (coerce v 'list)))

;;; Rule sets

(defparameter *closure-rules*
  '(:right ((rule (path ?x ?y) :- (edge ?x ?y))
            (rule (path ?x ?z) :- (edge ?x ?y) (path ?y ?z)))
    :left ((rule (path ?x ?y) :- (edge ?x ?y))
           (rule (path ?x ?z) :- (path ?x ?y) (edge ?y ?z)))
    :nonlinear ((rule (path ?x ?y) :- (edge ?x ?y))
                (rule (path ?x ?z) :- (path ?x ?y) (path ?y ?z)))))

(defun closure-rules (&optional (kind :right))
  (getf *closure-rules* kind))

(defparameter *reach-rules*
  '((rule (reach ?y) :- (start ?y))
    (rule (reach ?y) :- (reach ?x) (edge ?x ?y))
    (rule (unreach ?x) :- (node ?x) (not (reach ?x)))))

(defparameter *same-generation-rules*
  '((rule (sg ?x ?x) :- (person ?x))
    (rule (sg ?x ?y) :- (parent ?x ?xp) (sg ?xp ?yp) (parent ?y ?yp))))

;;; Oracles

(defun oracle-closure (edges)
  "The (path A B) facts of the transitive closure of EDGES, sorted."
  (let ((succ (make-hash-table)) (out '()))
    (dolist (e edges) (pushnew (third e) (gethash (second e) succ)))
    (loop for a being the hash-keys of succ
          do (let ((seen (make-hash-table)) (stack (copy-list (gethash a succ))))
               (loop while stack
                     do (let ((b (pop stack)))
                          (unless (gethash b seen)
                            (setf (gethash b seen) t)
                            (push (list 'path a b) out)
                            (dolist (c (gethash b succ)) (push c stack)))))))
    (sort-facts out)))

(defun oracle-reach (edges starts nodes)
  "(reach N) and (unreach N) for NODES, sorted."
  (let ((reached (make-hash-table)) (stack (copy-list starts)))
    (loop while stack
          do (let ((n (pop stack)))
               (unless (gethash n reached)
                 (setf (gethash n reached) t)
                 (dolist (e edges)
                   (when (eql (second e) n) (push (third e) stack))))))
    (sort-facts
     (append (loop for n being the hash-keys of reached collect (list 'reach n))
             (loop for n in nodes unless (gethash n reached) collect (list 'unreach n))))))

;;; Proof trees as plain data, for exact comparison.

(defun proof-sexp (proof)
  (list (proof-fact proof)
        (and (proof-rule proof) (rule-form (proof-rule proof)))
        (mapcar #'proof-sexp (proof-premises proof))
        (proof-negated proof)
        (proof-builtins proof)
        (proof-bindings proof)))

(defun proof-consistent-p (proof base-facts)
  "Every node's fact is its rule head under its bindings, its premises are
its positive body atoms under the bindings, and its leaves are base facts."
  (if (proof-base-p proof)
      (and (member (proof-fact proof) base-facts :test #'equal) t)
      (let* ((rule (proof-rule proof))
             (b (proof-bindings proof))
             (positive (remove-if-not #'logic-atom-p (rule-body rule))))
        (and (equal (substitute-bindings (rule-head rule) b) (proof-fact proof))
             (equal (mapcar (lambda (a) (substitute-bindings a b)) positive)
                    (mapcar #'proof-fact (proof-premises proof)))
             (every (lambda (p) (proof-consistent-p p base-facts)) (proof-premises proof))))))
