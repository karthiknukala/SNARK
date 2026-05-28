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

(defun mw-declare-arithmetic-synthesis-language ()
  (dolist (name '(a b n d zero))
    (declare-constant name))
  (dolist (entry '((mw-gcd 2)
                   (mw-minus 2)
                   (mw-qr 2)
                   (mw-pair 2)
                   (mw-succ 1)
                   (mw-quotient-of 1)
                   (mw-remainder-of 1)))
    (apply #'declare-function entry))
  (dolist (entry '((mw-eq 2)
                   (mw-gt 2)
                   (mw-lt 2)
                   (mw-gcd-out 3)
                   (mw-qr-out 3)))
    (apply #'declare-relation entry)))

(defun mw-gcd-subtractive-program ()
  ;; Subtractive GCD in the style of Manna/Waldinger's gcd correctness example:
  ;; equal arguments finish; otherwise recur on the larger argument minus the
  ;; smaller one.
  (mw-synthesis-setup)
  (mw-declare-arithmetic-synthesis-language)
  (assert '(or (mw-eq a b) (mw-gt a b) (mw-gt b a))
          :name 'mw-gcd-trichotomy)
  (assert '(implies
            (mw-eq a b)
            (mw-gcd-out a b a))
          :name 'mw-gcd-equal-case)
  (assert '(implies
            (mw-gt a b)
            (mw-gcd-out a b (mw-gcd (mw-minus a b) b)))
          :name 'mw-gcd-left-reduction)
  (assert '(implies
            (mw-gt b a)
            (mw-gcd-out a b (mw-gcd a (mw-minus b a))))
          :name 'mw-gcd-right-reduction)
  (prove '(mw-gcd-out a b ?answer)
         :answer '(values ?answer))
  (mw-synthesis-answer))

(defun mw-quotient-remainder-program ()
  ;; Quotient/remainder by recursive subtraction.  For natural N and positive D,
  ;; if N<D return (0,N); otherwise recurse on N-D and increment the quotient.
  (mw-synthesis-setup)
  (mw-declare-arithmetic-synthesis-language)
  (assert '(implies
            (mw-lt n d)
            (mw-qr-out n d (mw-pair zero n)))
          :name 'mw-qr-base-case)
  (assert '(implies
            (not (mw-lt n d))
            (mw-qr-out
             n
             d
             (mw-pair
              (mw-succ (mw-quotient-of (mw-qr (mw-minus n d) d)))
              (mw-remainder-of (mw-qr (mw-minus n d) d)))))
          :name 'mw-qr-recursive-case)
  (prove '(mw-qr-out n d ?answer)
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
         (mw-square-root-binary-search-program))
   (list 'gcd-subtractive-program
         (mw-gcd-subtractive-program))
   (list 'quotient-remainder-program
         (mw-quotient-remainder-program))))

;;; Executable interpretations of the extracted symbolic programs.
;;;
;;; SNARK returns proof answers such as ANSWER-IF terms over symbols like
;;; MW-OCCURS, MW-LE, and MW-COMPOSE.  The functions below make the gap explicit:
;;; they are ordinary Lisp interpretations of those symbols, so the extracted
;;; program shapes can be run on concrete inputs.

(defun mw-run-var-p (term)
  (and (consp term) (eq 'mw-var (first term))))

(defun mw-run-const-p (term)
  (and (consp term) (eq 'mw-const (first term))))

(defun mw-run-app-p (term)
  (and (consp term) (eq 'mw-app (first term))))

(defun mw-run-success-p (result)
  (and (consp result) (eq 'mw-some (first result))))

(defun mw-run-fail-p (result)
  (eq 'mw-none result))

(defun mw-run-subst-of (result)
  (and (mw-run-success-p result) (second result)))

(defun mw-run-occurs-p (var term)
  ;; Strict occurrence, matching the usual occurs check: a variable does not
  ;; occur in itself, but it occurs in a compound term containing it.
  (and (mw-run-app-p term)
       (or (equal var (second term))
           (equal var (third term))
           (mw-run-occurs-p var (second term))
           (mw-run-occurs-p var (third term)))))

(defun mw-run-apply-subst (subst term)
  (cond
   ((mw-run-var-p term)
    (let ((binding (assoc (second term) subst :test #'equal)))
      (if binding
          (mw-run-apply-subst subst (second binding))
          term)))
   ((mw-run-app-p term)
    `(mw-app ,(mw-run-apply-subst subst (second term))
             ,(mw-run-apply-subst subst (third term))))
   (t
    term)))

(defun mw-run-compose (subst1 subst2)
  (append
   (mapcar (lambda (binding)
             (list (first binding)
                   (mw-run-apply-subst subst2 (second binding))))
           subst1)
   subst2))

(defun mw-run-unify-var (var term)
  (if (mw-run-occurs-p `(mw-var ,var) term)
      'mw-none
      `(mw-some ((,var ,term)))))

(defun mw-run-unify (term1 term2)
  (cond
   ((equal term1 term2)
    '(mw-some nil))
   ((mw-run-var-p term1)
    (mw-run-unify-var (second term1) term2))
   ((mw-run-var-p term2)
    (mw-run-unify-var (second term2) term1))
   ((and (mw-run-const-p term1) (mw-run-const-p term2))
    (if (equal (second term1) (second term2))
        '(mw-some nil)
        'mw-none))
   ((and (mw-run-app-p term1) (mw-run-app-p term2))
    (let ((left-result (mw-run-unify (second term1) (second term2))))
      (if (mw-run-fail-p left-result)
          'mw-none
          (let* ((left-subst (mw-run-subst-of left-result))
                 (right-result
                   (mw-run-unify
                    (mw-run-apply-subst left-subst (third term1))
                    (mw-run-apply-subst left-subst (third term2)))))
            (if (mw-run-fail-p right-result)
                'mw-none
                `(mw-some
                  ,(mw-run-compose left-subst
                                   (mw-run-subst-of right-result))))))))
   (t
    'mw-none)))

(defun mw-run-sqrt-step (r eps z)
  (if (<= (* (+ z eps) (+ z eps)) r)
      (+ z eps)
      z))

(defun mw-run-sqrt (r eps)
  (unless (and (realp r) (not (minusp r)))
    (error "R must be a nonnegative real number, not ~S." r))
  (unless (and (realp eps) (plusp eps))
    (error "EPS must be a positive real number, not ~S." eps))
  (if (< (max r 1) eps)
      0
      (let ((z (mw-run-sqrt r (* 2 eps))))
        (mw-run-sqrt-step r eps z))))

(defun mw-run-sqrt-within-p (r eps z)
  (and (<= (* z z) r)
       (< r (* (+ z eps) (+ z eps)))))

(defun mw-run-gcd (a b)
  (unless (and (integerp a) (plusp a))
    (error "A must be a positive integer, not ~S." a))
  (unless (and (integerp b) (plusp b))
    (error "B must be a positive integer, not ~S." b))
  (cond
   ((= a b)
    a)
   ((> a b)
    (mw-run-gcd (- a b) b))
   (t
    (mw-run-gcd a (- b a)))))

(defun mw-run-quotient-remainder (n d)
  (unless (and (integerp n) (not (minusp n)))
    (error "N must be a natural number, not ~S." n))
  (unless (and (integerp d) (plusp d))
    (error "D must be a positive integer, not ~S." d))
  (if (< n d)
      (list :quotient 0 :remainder n)
      (let ((qr (mw-run-quotient-remainder (- n d) d)))
        (list :quotient (1+ (getf qr :quotient))
              :remainder (getf qr :remainder)))))

(defun mw-run-quotient-remainder-spec-p (n d qr)
  (and (= n (+ (* (getf qr :quotient) d) (getf qr :remainder)))
       (<= 0 (getf qr :remainder))
       (< (getf qr :remainder) d)))

(defun mw-run-square-root-demo (&optional (r 10) (eps 1/100))
  (let ((z (mw-run-sqrt r eps)))
    (list :r r
          :eps eps
          :answer z
          :within-spec (mw-run-sqrt-within-p r eps z))))

(defun mw-run-gcd-demo (&optional (a 84) (b 30))
  (list :a a
        :b b
        :answer (mw-run-gcd a b)
        :cl-gcd (gcd a b)))

(defun mw-run-quotient-remainder-demo (&optional (n 37) (d 5))
  (let ((qr (mw-run-quotient-remainder n d)))
    (list :n n
          :d d
          :answer qr
          :within-spec (mw-run-quotient-remainder-spec-p n d qr))))

(defun mw-run-unification-demo ()
  (list
   (list 'success
         (mw-run-unify
          '(mw-app (mw-const f) (mw-var x))
          '(mw-app (mw-const f) (mw-const a))))
   (list 'constant-clash
         (mw-run-unify
          '(mw-app (mw-var x) (mw-var x))
          '(mw-app (mw-const a) (mw-const b))))
   (list 'occurs-check
         (mw-run-unify
          '(mw-var x)
          '(mw-app (mw-var x) (mw-const a))))))

(defun mw-executable-synthesis-demos ()
  (list
   (list 'unification (mw-run-unification-demo))
   (list 'square-root (mw-run-square-root-demo))
   (list 'gcd (mw-run-gcd-demo))
   (list 'quotient-remainder (mw-run-quotient-remainder-demo))))

;;; synthesis-examples.lisp EOF
