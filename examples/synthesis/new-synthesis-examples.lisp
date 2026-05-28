;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark-user -*-
;;; File: examples/synthesis/new-synthesis-examples.lisp
;;;
;;; New answer-extraction synthesis examples for SNARK.
;;;
;;; The examples in synthesis-examples.lisp deliberately follow classical
;;; Manna/Waldinger developments.  This file contains additional examples that
;;; exercise the same paradigm on algorithms that are useful stress tests for
;;; symbolic program extraction: recursive calls under constructors, paired
;;; outputs, prioritized rewrite rules, and functional state updates.

(in-package :snark-user)

(defun new-synthesis-setup ()
  (initialize)
  (use-resolution t)
  (use-conditional-answer-creation t)
  (print-options-when-starting nil)
  (print-rows-when-given nil)
  (print-rows-when-derived nil)
  (print-final-rows nil)
  (print-summary-when-finished nil)
  (print-clocks-when-finished nil))

(defun new-synthesis-answer ()
  (answer t))

(defun new-declare-list-synthesis-language ()
  (dolist (name '(x y xs ys))
    (declare-constant name))
  (dolist (entry '((new-cons 2)
                   (new-merge 2)
                   (new-partition 1)
                   (new-pair 2)
                   (new-left 1)
                   (new-right 1)))
    (apply #'declare-function entry))
  (dolist (entry '((new-le 2)
                   (new-keeps 1)
                   (new-merge-out 3)
                   (new-partition-out 2)))
    (apply #'declare-relation entry)))

(defun new-stable-merge-program ()
  ;; Merge two nonempty sorted lists while preserving stability.  The proof
  ;; extracts the recursive choice between the two list heads.
  (new-synthesis-setup)
  (new-declare-list-synthesis-language)
  (assert '(implies
            (new-le x y)
            (new-merge-out
             (new-cons x xs)
             (new-cons y ys)
             (new-cons x (new-merge xs (new-cons y ys)))))
          :name 'new-merge-take-left)
  (assert '(implies
            (not (new-le x y))
            (new-merge-out
             (new-cons x xs)
             (new-cons y ys)
             (new-cons y (new-merge (new-cons x xs) ys))))
          :name 'new-merge-take-right)
  (prove '(new-merge-out (new-cons x xs) (new-cons y ys) ?answer)
         :answer '(values ?answer))
  (new-synthesis-answer))

(defun new-stable-partition-program ()
  ;; Partition a list into values that satisfy a predicate and values that do
  ;; not.  The witness is a pair of recursively constructed lists.
  (new-synthesis-setup)
  (new-declare-list-synthesis-language)
  (assert '(implies
            (new-keeps x)
            (new-partition-out
             (new-cons x xs)
             (new-pair
              (new-cons x (new-left (new-partition xs)))
              (new-right (new-partition xs)))))
          :name 'new-partition-keep)
  (assert '(implies
            (not (new-keeps x))
            (new-partition-out
             (new-cons x xs)
             (new-pair
              (new-left (new-partition xs))
              (new-cons x (new-right (new-partition xs))))))
          :name 'new-partition-drop)
  (prove '(new-partition-out (new-cons x xs) ?answer)
         :answer '(values ?answer))
  (new-synthesis-answer))

(defun new-declare-expression-synthesis-language ()
  (dolist (name '(e1 e2))
    (declare-constant name))
  (dolist (entry '((new-plus 2)
                   (new-add-value 2)
                   (new-const 1)
                   (new-simplify 1)))
    (apply #'declare-function entry))
  (dolist (entry '((new-both-const 2)
                   (new-zero 1)
                   (new-simplify-out 2)))
    (apply #'declare-relation entry)))

(defun new-plus-simplifier-program ()
  ;; A prioritized simplifier for addition nodes:
  ;;   constant fold, then eliminate left zero, then eliminate right zero,
  ;;   otherwise rebuild with simplified children.
  (new-synthesis-setup)
  (new-declare-expression-synthesis-language)
  (assert '(implies
            (new-both-const e1 e2)
            (new-simplify-out
             (new-plus e1 e2)
             (new-const (new-add-value e1 e2))))
          :name 'new-plus-fold-constants)
  (assert '(implies
            (and (not (new-both-const e1 e2))
                 (new-zero e1))
            (new-simplify-out
             (new-plus e1 e2)
             (new-simplify e2)))
          :name 'new-plus-drop-left-zero)
  (assert '(implies
            (and (not (new-both-const e1 e2))
                 (not (new-zero e1))
                 (new-zero e2))
            (new-simplify-out
             (new-plus e1 e2)
             (new-simplify e1)))
          :name 'new-plus-drop-right-zero)
  (assert '(implies
            (and (not (new-both-const e1 e2))
                 (not (new-zero e1))
                 (not (new-zero e2)))
            (new-simplify-out
             (new-plus e1 e2)
             (new-plus (new-simplify e1) (new-simplify e2))))
          :name 'new-plus-rebuild)
  (prove '(new-simplify-out (new-plus e1 e2) ?answer)
         :answer '(values ?answer))
  (new-synthesis-answer))

(defun new-declare-graph-synthesis-language ()
  (dolist (name '(state u v w))
    (declare-constant name))
  (dolist (entry '((new-distance 2)
                   (new-plus 2)
                   (new-update-distance 3)
                   (new-update-predecessor 3)))
    (apply #'declare-function entry))
  (dolist (entry '((new-lt 2)
                   (new-relax-out 5)))
    (apply #'declare-relation entry)))

(defun new-shortest-path-relaxation-program ()
  ;; A Bellman-Ford/Dijkstra-style relaxation step in functional form.  If the
  ;; candidate path through U improves V, return an updated state; otherwise
  ;; return the original state.
  (new-synthesis-setup)
  (new-declare-graph-synthesis-language)
  (assert '(implies
            (new-lt (new-plus (new-distance u state) w)
                    (new-distance v state))
            (new-relax-out
             state
             u
             v
             w
             (new-update-predecessor
              (new-update-distance
               state
               v
               (new-plus (new-distance u state) w))
              v
              u)))
          :name 'new-relax-improves)
  (assert '(implies
            (not (new-lt (new-plus (new-distance u state) w)
                         (new-distance v state)))
            (new-relax-out state u v w state))
          :name 'new-relax-keeps-state)
  (prove '(new-relax-out state u v w ?answer)
         :answer '(values ?answer))
  (new-synthesis-answer))

(defun new-synthesis-examples ()
  (list
   (list 'stable-merge-program
         (new-stable-merge-program))
   (list 'stable-partition-program
         (new-stable-partition-program))
   (list 'plus-simplifier-program
         (new-plus-simplifier-program))
   (list 'shortest-path-relaxation-program
         (new-shortest-path-relaxation-program))))

;;; Executable interpretations of the new symbolic examples.

(defun new-run-stable-merge (xs ys &key (test #'<=))
  (cond
   ((null xs)
    ys)
   ((null ys)
    xs)
   ((funcall test (first xs) (first ys))
    (cons (first xs)
          (new-run-stable-merge (rest xs) ys :test test)))
   (t
    (cons (first ys)
          (new-run-stable-merge xs (rest ys) :test test)))))

(defun new-run-stable-partition (xs predicate)
  (labels ((partition* (remaining kept dropped)
             (cond
              ((null remaining)
               (list :kept (nreverse kept)
                     :dropped (nreverse dropped)))
              ((funcall predicate (first remaining))
               (partition* (rest remaining)
                           (cons (first remaining) kept)
                           dropped))
              (t
               (partition* (rest remaining)
                           kept
                           (cons (first remaining) dropped))))))
    (partition* xs nil nil)))

(defun new-run-const-p (expr)
  (and (consp expr) (eq 'new-const (first expr))))

(defun new-run-plus-p (expr)
  (and (consp expr) (eq 'new-plus (first expr))))

(defun new-run-zero-p (expr)
  (equal expr '(new-const 0)))

(defun new-run-simplify (expr)
  (if (new-run-plus-p expr)
      (let ((left (new-run-simplify (second expr)))
            (right (new-run-simplify (third expr))))
        (cond
         ((and (new-run-const-p left) (new-run-const-p right))
          `(new-const ,(+ (second left) (second right))))
         ((new-run-zero-p left)
          right)
         ((new-run-zero-p right)
          left)
         (t
          `(new-plus ,left ,right))))
      expr))

(defun new-run-lookup-distance (state node)
  (let ((entry (assoc node (getf state :distances) :test #'equal)))
    (if entry
        (cdr entry)
        (getf state :infinity most-positive-fixnum))))

(defun new-run-set-alist (alist key value)
  (let ((seen nil))
    (let ((updated
            (mapcar (lambda (entry)
                      (if (equal key (car entry))
                          (progn
                            (setf seen t)
                            (cons key value))
                          entry))
                    alist)))
      (if seen
          updated
          (acons key value updated)))))

(defun new-run-relax-edge (state u v w)
  (let* ((candidate (+ (new-run-lookup-distance state u) w))
         (current (new-run-lookup-distance state v)))
    (if (< candidate current)
        (list :distances
              (new-run-set-alist (getf state :distances) v candidate)
              :predecessors
              (new-run-set-alist (getf state :predecessors) v u)
              :infinity
              (getf state :infinity most-positive-fixnum))
        state)))

(defun new-run-stable-merge-demo ()
  (list :left '(1 3 5 7)
        :right '(2 3 4 9)
        :answer (new-run-stable-merge '(1 3 5 7) '(2 3 4 9))))

(defun new-run-stable-partition-demo ()
  (list :input '(1 2 3 4 5 6 7)
        :answer (new-run-stable-partition '(1 2 3 4 5 6 7) #'oddp)))

(defun new-run-plus-simplifier-demo ()
  (let ((expr '(new-plus
                (new-plus (new-const 0) (new-const 4))
                (new-plus (new-const 1) (new-const 2)))))
    (list :input expr
          :answer (new-run-simplify expr))))

(defun new-run-shortest-path-relaxation-demo ()
  (let ((state '(:distances ((a . 0) (b . 7))
                 :predecessors nil
                 :infinity 1000000)))
    (list :edge '(a b 3)
          :before state
          :after (new-run-relax-edge state 'a 'b 3))))

(defun new-executable-synthesis-demos ()
  (list
   (list 'stable-merge (new-run-stable-merge-demo))
   (list 'stable-partition (new-run-stable-partition-demo))
   (list 'plus-simplifier (new-run-plus-simplifier-demo))
   (list 'shortest-path-relaxation
         (new-run-shortest-path-relaxation-demo))))

;;; new-synthesis-examples.lisp EOF
