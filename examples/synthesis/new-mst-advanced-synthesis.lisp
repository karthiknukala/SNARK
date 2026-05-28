;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark-user -*-
;;; File: examples/synthesis/new-mst-advanced-synthesis.lisp
;;;
;;; Advanced MST synthesis/refinement examples for SNARK.
;;;
;;; This file extends new-mst-synthesis.lisp with the standard algorithmic
;;; development moves from the MST literature: red-rule deletion,
;;; contract/delete reductions, Boruvka phases, Kruskal and Prim implementation
;;; policies, verification, replacement edges, Karger-Klein-Tarjan filtering,
;;; soft-heap abstraction, matroid greedy abstraction, and dynamic/distributed
;;; phase hooks.  The corresponding first-order object vocabulary and core
;;; lemma terms live in new-mst-prelude-synthesis.lisp; this file is the
;;; algorithm/refinement layer over that prelude.

(in-package :snark-user)

(defun new-mst-advanced-declare-language ()
  (dolist (name '(g tree forest edge cycle cut batch component policy queue
                  root sample sample-tree filtered random-source epsilon
                  matroid weight-order updates fragments messages replacement
                  replacements certificate))
    (declare-constant name))
  (dolist (entry '((new-mst-delete-edge 2)
                   (new-mst-contract-edge 2)
                   (new-mst-contract-set 2)
                   (new-mst-contract-forest 2)
                   (new-mst-lift 2)
                   (new-mst-reverse-delete 1)
                   (new-mst-sorted-scan 1)
                   (new-mst-union-find-scan 1)
                   (new-mst-filter-kruskal 1)
                   (new-mst-dense-prim 2)
                   (new-mst-heap-prim 3)
                   (new-mst-verify-tree 2)
                   (new-mst-record-replacement 2)
                   (new-mst-replacement-map 2)
                   (new-mst-second-best-from-replacements 2)
                   (new-mst-sample 2)
                   (new-mst-filter-heavy 2)
                   (new-mst-kkt 2)
                   (new-mst-soft-heap-candidates 2)
                   (new-mst-repair-corruptions 2)
                   (new-mst-matroid-greedy 2)
                   (new-mst-graphic-matroid 1)
                   (new-mst-dynamic-sequence 2)
                   (new-mst-ghs-phase 2)))
    (apply #'declare-function entry))
  (dolist (entry '((new-mst-red-rule-out 3)
                   (new-heaviest-on-cycle 3)
                   (new-mst-reverse-delete-out 3)
                   (new-still-spans-after-delete 2)
                   (new-mst-contract-delete-out 4)
                   (new-safe-edge 3)
                   (new-useless-edge 3)
                   (new-mst-boruvka-phase-out 3)
                   (new-components-cover 2)
                   (new-each-component-lightest-outgoing 3)
                   (new-mst-kruskal-variant-out 3)
                   (new-kruskal-policy-sorted 1)
                   (new-kruskal-policy-union-find 1)
                   (new-kruskal-policy-filter 1)
                   (new-mst-prim-variant-out 4)
                   (new-prim-policy-dense 1)
                   (new-prim-policy-binary-heap 1)
                   (new-prim-policy-fibonacci-heap 1)
                   (new-prim-policy-pairing-heap 1)
                   (new-mst-verifier-out 3)
                   (new-tree-spans 2)
                   (new-tree-acyclic 2)
                   (new-path-max-dominates-nontree-edges 2)
                   (new-mst-replacement-out 3)
                   (new-tree-edge 2)
                   (new-min-replacement-edge 4)
                   (new-all-replacements-certified 3)
                   (new-mst-kkt-out 3)
                   (new-random-sample 3)
                   (new-sample-mst 2)
                   (new-f-heavy-filtered 3)
                   (new-mst-soft-heap-out 4)
                   (new-soft-heap-candidate-set 3)
                   (new-corruption-repair-valid 3)
                   (new-mst-matroid-out 4)
                   (new-matroid 1)
                   (new-graphic-matroid-of 2)
                   (new-weight-order-for 2)
                   (new-mst-dynamic-out 3)
                   (new-offline-update-sequence 1)
                   (new-update-reductions-valid 2)
                   (new-mst-ghs-out 4)
                   (new-fragments-have-min-outgoing 3)
                   (new-ghs-messages-valid 3)))
    (apply #'declare-relation entry)))

(defun new-mst-advanced-setup ()
  (new-mst-synthesis-setup)
  (new-mst-advanced-declare-language))

(defun new-mst-red-rule-refinement ()
  ;; Red rule: a heaviest edge on a cycle may be deleted.
  (new-mst-advanced-setup)
  (assert '(new-heaviest-on-cycle g edge cycle)
          :name 'new-mst-red-cycle-premise)
  (assert '(implies
            (new-heaviest-on-cycle g edge cycle)
            (new-mst-red-rule-out
             g
             edge
             (new-mst-delete-edge edge g)))
          :name 'new-mst-red-rule)
  (prove '(new-mst-red-rule-out g edge ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-reverse-delete-refinement ()
  ;; Recursive reverse-delete skeleton: consider edges from high to low weight;
  ;; delete an edge exactly when spanning is preserved.
  (new-mst-advanced-setup)
  (assert '(or (new-still-spans-after-delete g edge)
               (not (new-still-spans-after-delete g edge)))
          :name 'new-mst-reverse-delete-cases)
  (assert '(implies
            (new-still-spans-after-delete g edge)
            (new-mst-reverse-delete-out
             g
             edge
             (new-mst-reverse-delete (new-mst-delete-edge edge g))))
          :name 'new-mst-reverse-delete-drop)
  (assert '(implies
            (not (new-still-spans-after-delete g edge))
            (new-mst-reverse-delete-out
             g
             edge
             (new-mst-reverse-delete g)))
          :name 'new-mst-reverse-delete-keep)
  (prove '(new-mst-reverse-delete-out g edge ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-contract-delete-refinement ()
  ;; Normalization theorem: contract safe edges, delete useless edges.
  (new-mst-advanced-setup)
  (assert '(or (new-safe-edge g forest edge)
               (new-useless-edge g forest edge))
          :name 'new-mst-contract-delete-cases)
  (assert '(implies
            (new-safe-edge g forest edge)
            (new-mst-contract-delete-out
             g
             forest
             edge
             (new-mst-contract-edge edge g)))
          :name 'new-mst-contract-safe-edge)
  (assert '(implies
            (and (not (new-safe-edge g forest edge))
                 (new-useless-edge g forest edge))
            (new-mst-contract-delete-out
             g
             forest
             edge
             (new-mst-delete-edge edge g)))
          :name 'new-mst-delete-useless-edge)
  (prove '(new-mst-contract-delete-out g forest edge ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-boruvka-phase-refinement ()
  ;; A full Boruvka phase: every component chooses a lightest outgoing edge;
  ;; the batch is safe, can be contracted, and the recursive result is lifted.
  (new-mst-advanced-setup)
  (assert '(new-components-cover g forest)
          :name 'new-mst-boruvka-components-premise)
  (assert '(new-each-component-lightest-outgoing g forest batch)
          :name 'new-mst-boruvka-lightest-premise)
  (assert '(implies
            (and (new-components-cover g forest)
                 (new-each-component-lightest-outgoing g forest batch))
            (new-mst-boruvka-phase-out
             g
             forest
             (new-mst-lift
              batch
              (new-mst-greedy
               (new-mst-contract-set g batch)
               (new-mst-contract-forest forest batch)))))
          :name 'new-mst-boruvka-phase)
  (prove '(new-mst-boruvka-phase-out g forest ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-kruskal-variants-refinement ()
  ;; Kruskal implementation policies: plain sorted scan, union-find scan, or
  ;; Filter-Kruskal.  The output relation hides the data-structure choice.
  (new-mst-advanced-setup)
  (assert '(or (new-kruskal-policy-sorted policy)
               (new-kruskal-policy-union-find policy)
               (new-kruskal-policy-filter policy))
          :name 'new-mst-kruskal-policy-cases)
  (assert '(not (and (new-kruskal-policy-sorted policy)
                     (new-kruskal-policy-union-find policy)))
          :name 'new-mst-kruskal-not-sorted-union-find)
  (assert '(not (and (new-kruskal-policy-sorted policy)
                     (new-kruskal-policy-filter policy)))
          :name 'new-mst-kruskal-not-sorted-filter)
  (assert '(not (and (new-kruskal-policy-union-find policy)
                     (new-kruskal-policy-filter policy)))
          :name 'new-mst-kruskal-not-union-find-filter)
  (assert '(implies
            (new-kruskal-policy-sorted policy)
            (new-mst-kruskal-variant-out
             g policy (new-mst-sorted-scan g)))
          :name 'new-mst-kruskal-sorted)
  (assert '(implies
            (and (not (new-kruskal-policy-sorted policy))
                 (new-kruskal-policy-union-find policy))
            (new-mst-kruskal-variant-out
             g policy (new-mst-union-find-scan g)))
          :name 'new-mst-kruskal-union-find)
  (assert '(implies
            (and (not (new-kruskal-policy-sorted policy))
                 (not (new-kruskal-policy-union-find policy))
                 (new-kruskal-policy-filter policy))
            (new-mst-kruskal-variant-out
             g policy (new-mst-filter-kruskal g)))
          :name 'new-mst-kruskal-filter)
  (prove '(new-mst-kruskal-variant-out g policy ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-prim-queue-refinement ()
  ;; Prim/Jarnik implementation policies: dense scan or several heap ADTs.
  (new-mst-advanced-setup)
  (assert '(or (new-prim-policy-dense policy)
               (new-prim-policy-binary-heap policy)
               (new-prim-policy-fibonacci-heap policy)
               (new-prim-policy-pairing-heap policy))
          :name 'new-mst-prim-policy-cases)
  (assert '(implies
            (new-prim-policy-dense policy)
            (new-mst-prim-variant-out
             g root policy (new-mst-dense-prim g root)))
          :name 'new-mst-prim-dense)
  (assert '(implies
            (and (not (new-prim-policy-dense policy))
                 (new-prim-policy-binary-heap policy))
            (new-mst-prim-variant-out
             g root policy (new-mst-heap-prim g root queue)))
          :name 'new-mst-prim-binary-heap)
  (assert '(implies
            (and (not (new-prim-policy-dense policy))
                 (not (new-prim-policy-binary-heap policy))
                 (new-prim-policy-fibonacci-heap policy))
            (new-mst-prim-variant-out
             g root policy (new-mst-heap-prim g root queue)))
          :name 'new-mst-prim-fibonacci-heap)
  (assert '(implies
            (and (not (new-prim-policy-dense policy))
                 (not (new-prim-policy-binary-heap policy))
                 (not (new-prim-policy-fibonacci-heap policy))
                 (new-prim-policy-pairing-heap policy))
            (new-mst-prim-variant-out
             g root policy (new-mst-heap-prim g root queue)))
          :name 'new-mst-prim-pairing-heap)
  (prove '(new-mst-prim-variant-out g root policy ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-verification-refinement ()
  ;; Verification theorem: a spanning acyclic tree is minimum if every
  ;; non-tree edge is no lighter than the maximum edge on its tree path.
  (new-mst-advanced-setup)
  (assert '(new-tree-spans g tree)
          :name 'new-mst-verify-spans-premise)
  (assert '(new-tree-acyclic g tree)
          :name 'new-mst-verify-acyclic-premise)
  (assert '(new-path-max-dominates-nontree-edges g tree)
          :name 'new-mst-verify-path-max-premise)
  (assert '(implies
            (and (new-tree-spans g tree)
                 (new-tree-acyclic g tree)
                 (new-path-max-dominates-nontree-edges g tree))
            (new-mst-verifier-out
             g
             tree
             (new-mst-verify-tree g tree)))
          :name 'new-mst-verification)
  (prove '(new-mst-verifier-out g tree ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-replacement-edge-refinement ()
  ;; Replacement-edge/sensitivity step: for a tree edge, record the cheapest
  ;; non-tree edge reconnecting the two components exposed by removing it.
  (new-mst-advanced-setup)
  (assert '(new-tree-edge tree edge)
          :name 'new-mst-replacement-tree-edge-premise)
  (assert '(new-min-replacement-edge g tree edge replacement)
          :name 'new-mst-replacement-min-premise)
  (assert '(implies
            (and (new-tree-edge tree edge)
                 (new-min-replacement-edge g tree edge replacement))
            (new-mst-replacement-out
             g
             tree
             (new-mst-record-replacement edge replacement)))
          :name 'new-mst-replacement-record)
  (prove '(new-mst-replacement-out g tree ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-second-best-refinement ()
  ;; Once all replacement edges are certified, choosing the least increase over
  ;; the MST gives a second-best/sensitivity witness.
  (new-mst-advanced-setup)
  (assert '(new-all-replacements-certified g tree replacements)
          :name 'new-mst-all-replacements-premise)
  (assert '(implies
            (new-all-replacements-certified g tree replacements)
            (new-mst-replacement-out
             g
             tree
             (new-mst-second-best-from-replacements tree replacements)))
          :name 'new-mst-second-best)
  (prove '(new-mst-replacement-out g tree ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-kkt-filter-refinement ()
  ;; Karger-Klein-Tarjan shape: sample, solve sample, remove F-heavy edges,
  ;; recurse on the filtered graph.
  (new-mst-advanced-setup)
  (assert '(new-random-sample g random-source sample)
          :name 'new-mst-kkt-sample-premise)
  (assert '(new-sample-mst sample sample-tree)
          :name 'new-mst-kkt-sample-tree-premise)
  (assert '(new-f-heavy-filtered g sample-tree filtered)
          :name 'new-mst-kkt-filtered-premise)
  (assert '(implies
            (and (new-random-sample g random-source sample)
                 (new-sample-mst sample sample-tree)
                 (new-f-heavy-filtered g sample-tree filtered))
            (new-mst-kkt-out
             g
             random-source
             (new-mst-kkt filtered random-source)))
          :name 'new-mst-kkt-filter)
  (prove '(new-mst-kkt-out g random-source ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-soft-heap-refinement ()
  ;; Chazelle-style soft-heap abstraction: cheap candidate selection may
  ;; corrupt keys, so the refinement explicitly repairs/filters candidates
  ;; before continuing with the greedy skeleton.
  (new-mst-advanced-setup)
  (assert '(new-soft-heap-candidate-set g epsilon batch)
          :name 'new-mst-soft-candidates-premise)
  (assert '(new-corruption-repair-valid g batch filtered)
          :name 'new-mst-soft-repair-premise)
  (assert '(implies
            (and (new-soft-heap-candidate-set g epsilon batch)
                 (new-corruption-repair-valid g batch filtered))
            (new-mst-soft-heap-out
             g
             epsilon
             forest
             (new-mst-greedy
              (new-mst-repair-corruptions g
                                          (new-mst-soft-heap-candidates
                                           g epsilon))
              forest)))
          :name 'new-mst-soft-heap)
  (prove '(new-mst-soft-heap-out g epsilon forest ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-matroid-greedy-refinement ()
  ;; Matroid abstraction: MST is minimum-weight basis in the graphic matroid.
  (new-mst-advanced-setup)
  (assert '(new-matroid matroid)
          :name 'new-mst-matroid-premise)
  (assert '(new-graphic-matroid-of g matroid)
          :name 'new-mst-graphic-matroid-premise)
  (assert '(new-weight-order-for matroid weight-order)
          :name 'new-mst-weight-order-premise)
  (assert '(implies
            (and (new-matroid matroid)
                 (new-graphic-matroid-of g matroid)
                 (new-weight-order-for matroid weight-order))
            (new-mst-matroid-out
             g
             matroid
             weight-order
             (new-mst-matroid-greedy matroid weight-order)))
          :name 'new-mst-matroid-greedy)
  (prove '(new-mst-matroid-out g matroid weight-order ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-offline-dynamic-refinement ()
  ;; Offline dynamic hook: if a known update sequence has valid reductions,
  ;; compute the sequence of reduced/lifted MSTs.
  (new-mst-advanced-setup)
  (assert '(new-offline-update-sequence updates)
          :name 'new-mst-offline-updates-premise)
  (assert '(new-update-reductions-valid g updates)
          :name 'new-mst-update-reductions-premise)
  (assert '(implies
            (and (new-offline-update-sequence updates)
                 (new-update-reductions-valid g updates))
            (new-mst-dynamic-out
             g
             updates
             (new-mst-dynamic-sequence g updates)))
          :name 'new-mst-offline-dynamic)
  (prove '(new-mst-dynamic-out g updates ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-ghs-distributed-refinement ()
  ;; Gallager-Humblet-Spira-style distributed phase hook: fragments exchange
  ;; messages to identify minimum outgoing edges, then merge fragments.
  (new-mst-advanced-setup)
  (assert '(new-fragments-have-min-outgoing g fragments batch)
          :name 'new-mst-ghs-min-outgoing-premise)
  (assert '(new-ghs-messages-valid g fragments messages)
          :name 'new-mst-ghs-messages-premise)
  (assert '(implies
            (and (new-fragments-have-min-outgoing g fragments batch)
                 (new-ghs-messages-valid g fragments messages))
            (new-mst-ghs-out
             g
             fragments
             messages
             (new-mst-ghs-phase g fragments)))
          :name 'new-mst-ghs-phase)
  (prove '(new-mst-ghs-out g fragments messages ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-advanced-synthesis-examples ()
  (list
   (list 'red-rule-refinement
         (new-mst-red-rule-refinement))
   (list 'reverse-delete-refinement
         (new-mst-reverse-delete-refinement))
   (list 'contract-delete-refinement
         (new-mst-contract-delete-refinement))
   (list 'boruvka-phase-refinement
         (new-mst-boruvka-phase-refinement))
   (list 'kruskal-variants-refinement
         (new-mst-kruskal-variants-refinement))
   (list 'prim-queue-refinement
         (new-mst-prim-queue-refinement))
   (list 'verification-refinement
         (new-mst-verification-refinement))
   (list 'replacement-edge-refinement
         (new-mst-replacement-edge-refinement))
   (list 'second-best-refinement
         (new-mst-second-best-refinement))
   (list 'kkt-filter-refinement
         (new-mst-kkt-filter-refinement))
   (list 'soft-heap-refinement
         (new-mst-soft-heap-refinement))
   (list 'matroid-greedy-refinement
         (new-mst-matroid-greedy-refinement))
   (list 'offline-dynamic-refinement
         (new-mst-offline-dynamic-refinement))
   (list 'ghs-distributed-refinement
         (new-mst-ghs-distributed-refinement))))

;;; Concrete finite-graph interpretations for the advanced refinement leaves.

(defun new-run-mst-graph-with-edges (graph edges)
  (list :vertices (new-run-mst-vertices graph)
        :edges edges))

(defun new-run-mst-edge-member-p (edge edges)
  (member (new-run-mst-edge-id edge)
          edges
          :key #'new-run-mst-edge-id
          :test #'equal))

(defun new-run-mst-descending-edges (graph)
  (sort (copy-list (new-run-mst-edges graph))
        #'>
        :key #'new-run-mst-edge-weight))

(defun new-run-mst-connected-p (graph &optional (edges (new-run-mst-edges graph)))
  (let* ((vertices (new-run-mst-vertices graph))
         (parent (new-run-mst-make-parent vertices)))
    (dolist (edge edges)
      (new-run-mst-union parent
                         (new-run-mst-edge-u edge)
                         (new-run-mst-edge-v edge)))
    (or (null vertices)
        (let ((root (new-run-mst-find parent (first vertices))))
          (every (lambda (vertex)
                   (equal root (new-run-mst-find parent vertex)))
                 vertices)))))

(defun new-run-mst-reverse-delete (graph)
  (let ((kept (copy-list (new-run-mst-edges graph))))
    (dolist (edge (new-run-mst-descending-edges graph))
      (let ((candidate (remove (new-run-mst-edge-id edge)
                               kept
                               :key #'new-run-mst-edge-id
                               :test #'equal)))
        (when (new-run-mst-connected-p graph candidate)
          (setf kept candidate))))
    kept))

(defun new-run-mst-adjacent-tree-edges (edges vertex)
  (remove-if-not
   (lambda (edge)
     (or (equal vertex (new-run-mst-edge-u edge))
         (equal vertex (new-run-mst-edge-v edge))))
   edges))

(defun new-run-mst-path (edges start goal)
  (labels ((walk (vertex seen)
             (if (equal vertex goal)
                 (values t nil)
                 (dolist (edge (new-run-mst-adjacent-tree-edges edges vertex)
                               (values nil nil))
                   (let ((next (new-run-mst-other-end edge vertex)))
                     (unless (member next seen :test #'equal)
                       (multiple-value-bind (found path)
                           (walk next (cons next seen))
                         (when found
                           (return (values t (cons edge path)))))))))))
    (multiple-value-bind (found path) (walk start (list start))
      (when found path))))

(defun new-run-mst-path-max-weight (edges u v)
  (let ((path (new-run-mst-path edges u v)))
    (when path
      (reduce #'max path :key #'new-run-mst-edge-weight))))

(defun new-run-mst-tree-p (graph tree)
  (and (= (length tree)
          (max 0 (1- (length (new-run-mst-vertices graph)))))
       (new-run-mst-connected-p graph tree)))

(defun new-run-mst-verify (graph tree)
  (let ((tree-ok (new-run-mst-tree-p graph tree))
        (path-ok t))
    (dolist (edge (new-run-mst-edges graph))
      (unless (new-run-mst-edge-member-p edge tree)
        (let ((path-max (new-run-mst-path-max-weight
                         tree
                         (new-run-mst-edge-u edge)
                         (new-run-mst-edge-v edge))))
          (unless (and path-max
                       (<= path-max (new-run-mst-edge-weight edge)))
            (setf path-ok nil)))))
    (list :tree-p tree-ok
          :path-max-condition path-ok
          :mst-p (and tree-ok path-ok))))

(defun new-run-mst-replacement-edges (graph tree)
  (let ((non-tree-edges
         (remove-if (lambda (edge)
                      (new-run-mst-edge-member-p edge tree))
                    (new-run-mst-edges graph))))
    (mapcar
     (lambda (tree-edge)
       (let ((parent (new-run-mst-make-parent (new-run-mst-vertices graph))))
         (dolist (edge tree)
           (unless (equal (new-run-mst-edge-id edge)
                          (new-run-mst-edge-id tree-edge))
             (new-run-mst-union parent
                                (new-run-mst-edge-u edge)
                                (new-run-mst-edge-v edge))))
         (let ((replacement
                (first
                 (sort
                  (remove-if-not
                   (lambda (edge)
                     (not (equal
                           (new-run-mst-find parent (new-run-mst-edge-u edge))
                           (new-run-mst-find parent (new-run-mst-edge-v edge)))))
                   non-tree-edges)
                  #'<
                  :key #'new-run-mst-edge-weight))))
           (list :tree-edge (new-run-mst-edge-id tree-edge)
                 :replacement (and replacement
                                   (new-run-mst-edge-id replacement))
                 :replacement-weight (and replacement
                                          (new-run-mst-edge-weight replacement))
                 :delta (and replacement
                             (- (new-run-mst-edge-weight replacement)
                                (new-run-mst-edge-weight tree-edge)))))))
     tree)))

(defun new-run-mst-second-best (tree replacements)
  (let ((base-weight (new-run-mst-total-weight tree))
        (best nil))
    (dolist (entry replacements)
      (let ((delta (getf entry :delta)))
        (when (and delta
                   (or (null best)
                       (< delta (getf best :delta))))
          (setf best entry))))
    (when best
      (append best
              (list :second-best-weight (+ base-weight (getf best :delta)))))))

(defun new-run-mst-boruvka-phases (graph)
  (let ((parent (new-run-mst-make-parent (new-run-mst-vertices graph)))
        (tree nil)
        (phases nil)
        (changed t))
    (loop
      while changed
      do (setf changed nil)
         (let ((added nil))
           (dolist (edge (new-run-mst-boruvka-cheapest graph parent))
             (when (new-run-mst-crosses-components-p parent edge)
               (push edge tree)
               (push edge added)
               (new-run-mst-union parent
                                  (new-run-mst-edge-u edge)
                                  (new-run-mst-edge-v edge))
               (setf changed t)))
           (when added
             (push (new-run-mst-edge-ids (nreverse added)) phases))))
    (let ((result (nreverse tree)))
      (list :phases (nreverse phases)
            :edges (new-run-mst-edge-ids result)
            :weight (new-run-mst-total-weight result)))))

(defun new-run-mst-f-heavy-p (forest edge)
  (let ((path-max (new-run-mst-path-max-weight
                   forest
                   (new-run-mst-edge-u edge)
                   (new-run-mst-edge-v edge))))
    (and path-max
         (< path-max (new-run-mst-edge-weight edge)))))

(defun new-run-mst-filter-heavy (graph forest)
  (remove-if (lambda (edge)
               (new-run-mst-f-heavy-p forest edge))
             (new-run-mst-edges graph)))

(defun new-run-mst-kkt-filter (graph)
  (let* ((sample-edges
          (loop for edge in (new-run-mst-edges graph)
                for index from 0
                when (evenp index)
                collect edge))
         (sample-graph (new-run-mst-graph-with-edges graph sample-edges))
         (sample-tree (new-run-mst-kruskal sample-graph))
         (filtered-edges (new-run-mst-filter-heavy graph sample-tree))
         (filtered-graph (new-run-mst-graph-with-edges graph filtered-edges))
         (tree (new-run-mst-kruskal filtered-graph)))
    (list :sample (new-run-mst-edge-ids sample-edges)
          :sample-tree (new-run-mst-edge-ids sample-tree)
          :filtered-out (set-difference
                         (new-run-mst-edge-ids (new-run-mst-edges graph))
                         (new-run-mst-edge-ids filtered-edges)
                         :test #'equal)
          :edges (new-run-mst-edge-ids tree)
          :weight (new-run-mst-total-weight tree))))

(defun new-run-mst-filter-kruskal (graph)
  (let* ((kkt (new-run-mst-kkt-filter graph))
         (tree (new-run-mst-kruskal graph)))
    (list :filter (getf kkt :filtered-out)
          :edges (new-run-mst-edge-ids tree)
          :weight (new-run-mst-total-weight tree))))

(defun new-run-mst-kruskal-variant (graph policy)
  (ecase policy
    (:sorted-scan
     (let ((tree (new-run-mst-kruskal graph)))
       (list :policy policy
             :edges (new-run-mst-edge-ids tree)
             :weight (new-run-mst-total-weight tree))))
    (:union-find
     (let ((tree (new-run-mst-kruskal graph)))
       (list :policy policy
             :edges (new-run-mst-edge-ids tree)
             :weight (new-run-mst-total-weight tree))))
    (:filter-kruskal
     (append (list :policy policy)
             (new-run-mst-filter-kruskal graph)))))

(defun new-run-mst-prim-variant (graph policy)
  (let ((tree (new-run-mst-prim graph)))
    (list :policy policy
          :queue (ecase policy
                   (:dense :array-scan)
                   (:binary-heap :binary-heap)
                   (:fibonacci-heap :fibonacci-heap)
                   (:pairing-heap :pairing-heap))
          :edges (new-run-mst-edge-ids tree)
          :weight (new-run-mst-total-weight tree))))

(defun new-run-mst-soft-heap-shape (graph)
  (let* ((kkt (new-run-mst-kkt-filter graph))
         (tree (new-run-mst-kruskal graph)))
    (list :candidate-filter (getf kkt :filtered-out)
          :repair :verify-after-corruption
          :edges (new-run-mst-edge-ids tree)
          :weight (new-run-mst-total-weight tree))))

(defun new-run-mst-matroid-greedy (graph)
  (let ((tree (new-run-mst-kruskal graph)))
    (list :matroid :graphic
          :basis (new-run-mst-edge-ids tree)
          :weight (new-run-mst-total-weight tree))))

(defun new-run-mst-apply-weight-update (graph update)
  (destructuring-bind (edge-id new-weight) update
    (new-run-mst-graph-with-edges
     graph
     (mapcar (lambda (edge)
               (if (equal edge-id (new-run-mst-edge-id edge))
                   (list (new-run-mst-edge-id edge)
                         (new-run-mst-edge-u edge)
                         (new-run-mst-edge-v edge)
                         new-weight)
                   edge))
             (new-run-mst-edges graph)))))

(defun new-run-mst-dynamic-sequence (graph updates)
  (let ((current graph)
        (answers nil))
    (dolist (update updates)
      (setf current (new-run-mst-apply-weight-update current update))
      (let ((tree (new-run-mst-kruskal current)))
        (push (list :update update
                    :edges (new-run-mst-edge-ids tree)
                    :weight (new-run-mst-total-weight tree))
              answers)))
    (nreverse answers)))

(defun new-run-mst-ghs-phase-shape (graph)
  (let ((phases (new-run-mst-boruvka-phases graph)))
    (list :message-rule :minimum-outgoing-edge
          :fragment-phases (getf phases :phases)
          :weight (getf phases :weight))))

(defun new-run-mst-advanced-demo ()
  (let* ((graph (new-run-mst-demo-graph))
         (kruskal (new-run-mst-kruskal graph))
         (reverse-delete (new-run-mst-reverse-delete graph))
         (replacements (new-run-mst-replacement-edges graph kruskal)))
    (list
     :reverse-delete (list :edges (new-run-mst-edge-ids reverse-delete)
                           :weight (new-run-mst-total-weight reverse-delete))
     :boruvka-phases (new-run-mst-boruvka-phases graph)
     :verification (new-run-mst-verify graph kruskal)
     :replacement-edges replacements
     :second-best (new-run-mst-second-best kruskal replacements)
     :kruskal-variants
     (mapcar (lambda (policy)
               (new-run-mst-kruskal-variant graph policy))
             '(:sorted-scan :union-find :filter-kruskal))
     :prim-variants
     (mapcar (lambda (policy)
               (new-run-mst-prim-variant graph policy))
             '(:dense :binary-heap :fibonacci-heap :pairing-heap))
     :kkt-filter (new-run-mst-kkt-filter graph)
     :soft-heap (new-run-mst-soft-heap-shape graph)
     :matroid-greedy (new-run-mst-matroid-greedy graph)
     :dynamic (new-run-mst-dynamic-sequence graph '((ab 1) (df 2)))
     :ghs (new-run-mst-ghs-phase-shape graph))))

;;; new-mst-advanced-synthesis.lisp EOF
