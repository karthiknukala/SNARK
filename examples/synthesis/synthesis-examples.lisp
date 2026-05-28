;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark-user -*-
;;; File: examples/synthesis/synthesis-examples.lisp
;;;
;;; Manna/Waldinger-style program-synthesis examples for SNARK.
;;;
;;; The original papers derive programs from constructive existence proofs.
;;; These examples recast the central proof obligations in SNARK's ordinary
;;; resolution/answer-extraction interface, so the refutation answer is the
;;; synthesized program term.

(in-package :snark-user)

(defun mw-synthesis-setup ()
  (initialize)
  (use-resolution t)
  (use-conditional-answer-creation t)
  (print-options-when-starting nil)
  (print-rows-when-given nil)
  (print-rows-when-derived nil)
  (print-final-rows nil)
  (print-summary-when-finished nil)
  (print-clocks-when-finished nil))

(defun mw-synthesis-answer ()
  (answer t))

(defun mw-declare-unification-language ()
  (dolist (name '(mw-none mw-id v term c d m n m1 n1))
    (declare-constant name))
  (dolist (entry '((mw-var 1)
                   (mw-const 1)
                   (mw-app 2)
                   (mw-bind 2)
                   (mw-some 1)
                   (mw-compose 2)
                   (mw-unify 2)
                   (mw-subst 2)
                   (mw-subst-of 1)))
    (apply #'declare-function entry))
  (dolist (entry '((mw-occurs 2)
                   (mw-same-symbol 2)
                   (mw-fail 1)
                   (mw-unify-out 3)))
    (apply #'declare-relation entry)))

(defun mw-unification-variable-case ()
  ;; Variable/term case: synthesize the occurs-check branch.
  ;;
  ;; If the variable occurs in the term, unification fails.  Otherwise the
  ;; singleton binding is a unifier.  The extracted answer is:
  ;;
  ;;   if occurs(var(v), term) then none else some(bind(v, term))
  (mw-synthesis-setup)
  (mw-declare-unification-language)
  (assert '(implies (mw-occurs (mw-var v) term)
                    (mw-unify-out (mw-var v) term mw-none))
          :name 'mw-occurs-check-failure)
  (assert '(implies (not (mw-occurs (mw-var v) term))
                    (mw-unify-out (mw-var v) term (mw-some (mw-bind v term))))
          :name 'mw-variable-binding)
  (prove '(mw-unify-out (mw-var v) term ?result)
         :answer '(values ?result))
  (mw-synthesis-answer))

(defun mw-unification-constant-case ()
  ;; Constant/constant case: synthesize equality testing for atoms.
  (mw-synthesis-setup)
  (mw-declare-unification-language)
  (assert '(implies (mw-same-symbol c d)
                    (mw-unify-out (mw-const c) (mw-const d) (mw-some mw-id)))
          :name 'mw-identical-constants)
  (assert '(implies (not (mw-same-symbol c d))
                    (mw-unify-out (mw-const c) (mw-const d) mw-none))
          :name 'mw-distinct-constants)
  (prove '(mw-unify-out (mw-const c) (mw-const d) ?result)
         :answer '(values ?result))
  (mw-synthesis-answer))

(defun mw-unification-compound-case ()
  ;; Compound/compound case: synthesize the recursive composition skeleton.
  ;;
  ;; The synthesized result is the usual structure: first unify the heads; if
  ;; that succeeds, substitute the first result through the tails and unify
  ;; those; if both succeed, compose the two substitutions.
  (mw-synthesis-setup)
  (mw-declare-unification-language)
  (assert '(implies
            (mw-fail (mw-unify m m1))
            (mw-unify-out (mw-app m n) (mw-app m1 n1) mw-none))
          :name 'mw-compound-first-fails)
  (assert '(implies
            (and (not (mw-fail (mw-unify m m1)))
                 (mw-fail
                  (mw-unify
                   (mw-subst (mw-subst-of (mw-unify m m1)) n)
                   (mw-subst (mw-subst-of (mw-unify m m1)) n1))))
            (mw-unify-out (mw-app m n) (mw-app m1 n1) mw-none))
          :name 'mw-compound-second-fails)
  (assert '(implies
            (and (not (mw-fail (mw-unify m m1)))
                 (not
                  (mw-fail
                   (mw-unify
                    (mw-subst (mw-subst-of (mw-unify m m1)) n)
                    (mw-subst (mw-subst-of (mw-unify m m1)) n1)))))
            (mw-unify-out
             (mw-app m n)
             (mw-app m1 n1)
             (mw-some
              (mw-compose
               (mw-subst-of (mw-unify m m1))
               (mw-subst-of
                (mw-unify
                 (mw-subst (mw-subst-of (mw-unify m m1)) n)
                 (mw-subst (mw-subst-of (mw-unify m m1)) n1)))))))
          :name 'mw-compound-compose)
  (prove '(mw-unify-out (mw-app m n) (mw-app m1 n1) ?result)
         :answer '(values ?result))
  (mw-synthesis-answer))

(defun mw-declare-square-root-language ()
  (dolist (name '(r eps z zero))
    (declare-constant name))
  (dolist (entry '((mw-plus 2)
                   (mw-square 1)
                   (mw-double 1)
                   (mw-sqrt 2)))
    (apply #'declare-function entry))
  (dolist (entry '((mw-le 2)
                   (mw-sqrt-within 3)
                   (mw-large-tolerance 2)))
    (apply #'declare-relation entry)))

(defun mw-square-root-binary-search-step ()
  ;; The binary-search refinement step from the square-root derivation.
  ;;
  ;; If z + eps is still at or below sqrt(r), move right; otherwise keep z.
  ;; MW-LE is the abstract comparison corresponding to
  ;;   (z + eps)^2 <= r.
  (mw-synthesis-setup)
  (mw-declare-square-root-language)
  (assert '(implies
            (mw-le (mw-square (mw-plus z eps)) r)
            (mw-sqrt-within r (mw-plus z eps) eps))
          :name 'mw-square-root-right-half)
  (assert '(implies
            (not (mw-le (mw-square (mw-plus z eps)) r))
            (mw-sqrt-within r z eps))
          :name 'mw-square-root-left-half)
  (prove '(mw-sqrt-within r ?answer eps)
         :answer '(values ?answer))
  (mw-synthesis-answer))

(defun mw-square-root-binary-search-program ()
  ;; A recursive square-root skeleton in the style of Manna/Waldinger.
  ;;
  ;; MW-SQRT denotes the recursive call with a doubled tolerance.  The proof
  ;; extracts a base-case test followed by the binary-search refinement test.
  (mw-synthesis-setup)
  (mw-declare-square-root-language)
  (assert '(implies
            (mw-large-tolerance r eps)
            (mw-sqrt-within r zero eps))
          :name 'mw-square-root-base-case)
  (assert '(implies
            (and (not (mw-large-tolerance r eps))
                 (mw-le (mw-square (mw-plus (mw-sqrt r (mw-double eps)) eps)) r))
            (mw-sqrt-within r (mw-plus (mw-sqrt r (mw-double eps)) eps) eps))
          :name 'mw-square-root-recursive-right-half)
  (assert '(implies
            (and (not (mw-large-tolerance r eps))
                 (not (mw-le (mw-square (mw-plus (mw-sqrt r (mw-double eps)) eps)) r)))
            (mw-sqrt-within r (mw-sqrt r (mw-double eps)) eps))
          :name 'mw-square-root-recursive-left-half)
  (prove '(mw-sqrt-within r ?answer eps)
         :answer '(values ?answer))
  (mw-synthesis-answer))

(defun mw-synthesis-examples ()
  (list
   (list 'unification-variable-case
         (mw-unification-variable-case))
   (list 'unification-constant-case
         (mw-unification-constant-case))
   (list 'unification-compound-case
         (mw-unification-compound-case))
   (list 'square-root-binary-search-step
         (mw-square-root-binary-search-step))
   (list 'square-root-binary-search-program
         (mw-square-root-binary-search-program))))

;;; synthesis-examples.lisp EOF

