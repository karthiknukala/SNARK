;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark-user -*-
;;; File: examples/synthesis/new-synthesis-examples.lisp
;;;
;;; New answer-extraction synthesis examples for SNARK.
;;;
;;; The examples in synthesis-examples.lisp deliberately follow classical
;;; Manna/Waldinger developments.  This file contains additional examples that
;;; exercise the same paradigm on algorithms that are useful stress tests for
;;; symbolic program extraction: recursive calls under constructors, paired
;;; outputs, branch-local assumptions, and post-recursion redundancy checks.

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

(defun new-declare-if-synthesis-language ()
  (dolist (name '(expr env new-true new-false))
    (declare-constant name))
  (dolist (entry '((new-if 3)
                   (new-condition 1)
                   (new-then-branch 1)
                   (new-else-branch 1)
                   (new-simplify-if 2)
                   (new-extend-true 2)
                   (new-extend-false 2)))
    (apply #'declare-function entry))
  (dolist (entry '((new-true-expr 1)
                   (new-false-expr 1)
                   (new-var-expr 1)
                   (new-if-expr 1)
                   (new-assumed-true 2)
                   (new-assumed-false 2)
                   (new-same 2)
                   (new-if-simplify-out 3)))
    (apply #'declare-relation entry)))

(defun new-if-normal-form-simplifier-program ()
  ;; Boyer/Moore-style simplification of normal-form IF expressions.  The
  ;; simplifier carries path assumptions.  Repeated variables are replaced by
  ;; their assumed truth values, and recursively equal branches are collapsed.
  (new-synthesis-setup)
  (new-declare-if-synthesis-language)
  (assert '(new-if-expr expr)
          :name 'new-if-input-is-if-node)
  (assert '(not (and (new-assumed-true (new-condition expr) env)
                     (new-assumed-false (new-condition expr) env)))
          :name 'new-if-assumptions-consistent)
  (assert '(implies
            (and (new-if-expr expr)
                 (new-assumed-true (new-condition expr) env))
            (new-if-simplify-out
             expr
             env
             (new-simplify-if (new-then-branch expr) env)))
          :name 'new-if-condition-known-true)
  (assert '(implies
            (and (new-if-expr expr)
                 (not (new-assumed-true (new-condition expr) env))
                 (new-assumed-false (new-condition expr) env))
            (new-if-simplify-out
             expr
             env
             (new-simplify-if (new-else-branch expr) env)))
          :name 'new-if-condition-known-false)
  (assert '(implies
            (and (new-if-expr expr)
                 (not (new-assumed-true (new-condition expr) env))
                 (not (new-assumed-false (new-condition expr) env))
                 (new-same
                  (new-simplify-if
                   (new-then-branch expr)
                   (new-extend-true (new-condition expr) env))
                  (new-simplify-if
                   (new-else-branch expr)
                   (new-extend-false (new-condition expr) env))))
            (new-if-simplify-out
             expr
             env
             (new-simplify-if
              (new-then-branch expr)
              (new-extend-true (new-condition expr) env))))
          :name 'new-if-redundant-branches)
  (assert '(implies
            (and (new-if-expr expr)
                 (not (new-assumed-true (new-condition expr) env))
                 (not (new-assumed-false (new-condition expr) env))
                 (not
                  (new-same
                   (new-simplify-if
                    (new-then-branch expr)
                    (new-extend-true (new-condition expr) env))
                   (new-simplify-if
                    (new-else-branch expr)
                    (new-extend-false (new-condition expr) env)))))
            (new-if-simplify-out
             expr
             env
             (new-if
              (new-condition expr)
              (new-simplify-if
               (new-then-branch expr)
               (new-extend-true (new-condition expr) env))
              (new-simplify-if
               (new-else-branch expr)
               (new-extend-false (new-condition expr) env)))))
          :name 'new-if-rebuild)
  (prove '(new-if-simplify-out expr env ?answer)
         :answer '(values ?answer))
  (new-synthesis-answer))

(defun new-synthesis-examples ()
  (list
   (list 'stable-merge-program
         (new-stable-merge-program))
   (list 'stable-partition-program
         (new-stable-partition-program))
   (list 'if-normal-form-simplifier-program
         (new-if-normal-form-simplifier-program))))

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

(defun new-run-if-p (expr)
  (and (consp expr) (eq 'new-if (first expr))))

(defun new-run-var-p (expr)
  (and (consp expr) (eq 'new-var (first expr))))

(defun new-run-if-condition (expr)
  (second expr))

(defun new-run-if-then-branch (expr)
  (third expr))

(defun new-run-if-else-branch (expr)
  (fourth expr))

(defun new-run-if-simplify (expr &optional env)
  (cond
   ((eq expr 'new-true)
    'new-true)
   ((eq expr 'new-false)
    'new-false)
   ((new-run-var-p expr)
    (let ((known (assoc expr env :test #'equal)))
      (cond
       ((null known)
        expr)
       ((cdr known)
        'new-true)
       (t
        'new-false))))
   ((new-run-if-p expr)
    (let* ((condition (new-run-if-condition expr))
           (known (assoc condition env :test #'equal)))
      (cond
       ((and known (cdr known))
        (new-run-if-simplify (new-run-if-then-branch expr) env))
       (known
        (new-run-if-simplify (new-run-if-else-branch expr) env))
       (t
        (let* ((then-result
                 (new-run-if-simplify
                  (new-run-if-then-branch expr)
                  (acons condition t env)))
               (else-result
                 (new-run-if-simplify
                  (new-run-if-else-branch expr)
                  (acons condition nil env))))
          (if (equal then-result else-result)
              then-result
              `(new-if ,condition ,then-result ,else-result)))))))
   (t
    expr)))

(defun new-run-stable-merge-demo ()
  (list :left '(1 3 5 7)
        :right '(2 3 4 9)
        :answer (new-run-stable-merge '(1 3 5 7) '(2 3 4 9))))

(defun new-run-stable-partition-demo ()
  (list :input '(1 2 3 4 5 6 7)
        :answer (new-run-stable-partition '(1 2 3 4 5 6 7) #'oddp)))

(defun new-run-if-normal-form-simplifier-demo ()
  (let ((expr '(new-if
                (new-var x)
                (new-if
                 (new-var y)
                 (new-if (new-var x) new-true new-false)
                 (new-if (new-var z) (new-var y) (new-var y)))
                (new-if
                 (new-var y)
                 (new-if (new-var x) new-false new-true)
                 (new-if (new-var x) (new-var y) (new-var y))))))
    (list :input expr
          :answer (new-run-if-simplify expr))))

(defun new-executable-synthesis-demos ()
  (list
   (list 'stable-merge (new-run-stable-merge-demo))
   (list 'stable-partition (new-run-stable-partition-demo))
   (list 'if-normal-form-simplifier
         (new-run-if-normal-form-simplifier-demo))))

;;; new-synthesis-examples.lisp EOF
