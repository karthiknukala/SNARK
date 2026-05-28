;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark-user -*-
;;; File: examples/synthesis/new-mst-prelude-synthesis.lisp
;;;
;;; Reified FOL prelude for MST synthesis/refinement examples.
;;;
;;; This file reifies the objects that pure first-order logic does not provide
;;; natively: paths, cycles, cuts, finite edge sets, exchange trees,
;;; contractions, weight comparisons, samples, heap states, matroids, update
;;; streams, and distributed message schedules.  The constants declared below
;;; are schematic objects, following the style of the existing SNARK synthesis
;;; examples: each proof is a first-order derivation over arbitrary reified
;;; objects named G, TREE, EDGE, and so on.
;;;
;;; The stricter finite-certificate layer for the ordinary non-probabilistic
;;; MST pipeline lives in new-mst-fol-synthesis.lisp.

(in-package :snark-user)

(defun new-mst-prelude-setup ()
  (initialize)
  (use-resolution t)
  (use-paramodulation t)
  (use-conditional-answer-creation t)
  (print-options-when-starting nil)
  (print-rows-when-given nil)
  (print-rows-when-derived nil)
  (print-final-rows nil)
  (print-summary-when-finished nil)
  (print-clocks-when-finished nil))

(defun new-mst-prelude-answer ()
  (answer t))

(defun new-mst-prelude-declare-language ()
  (dolist (name '(g tree tree2 other forest edge old replacement cut cycle path
                  batch sample sample-tree filtered random-source heap epsilon
                  matroid order updates messages fragments u v))
    (declare-constant name))
  (dolist (entry '((mstp-add-edge 2)
                   (mstp-delete-edge 2)
                   (mstp-contract-edge 2)
                   (mstp-contract-set 2)
                   (mstp-contract-forest 2)
                   (mstp-exchange 3)
                   (mstp-crossing-edge 2)
                   (mstp-cycle-replacement-edge 2)
                   (mstp-lift 2)
                   (mstp-verify-tree 2)
                   (mstp-record-replacement 2)
                   (mstp-second-best-from-replacements 2)
                   (mstp-filter-heavy 2)
                   (mstp-reverse-delete 1)
                   (mstp-kruskal-step 2)
                   (mstp-prim-step 3)
                   (mstp-boruvka-phase 2)
                   (mstp-filter-kruskal 1)
                   (mstp-kkt 2)
                   (mstp-soft-heap-candidates 2)
                   (mstp-repair-corruptions 2)
                   (mstp-matroid-greedy 2)
                   (mstp-dynamic-sequence 2)
                   (mstp-ghs-phase 2)))
    (apply #'declare-function entry))
  (dolist (entry '((mstp-all-input-edges 2)
                   (mstp-spans 2)
                   (mstp-acyclic 1)
                   (mstp-spanning-tree 2)
                   (mstp-total-weight-leq 2)
                   (mstp-competitor-no-lighter 3)
                   (mstp-mst 2)
                   (mstp-extends 2)
                   (mstp-edge-in-tree 2)
                   (mstp-edge-on-path 2)
                   (mstp-path-in-tree 4)
                   (mstp-path-crosses-cut 2)
                   (mstp-crosses-cut 2)
                   (mstp-cut-respects-forest 2)
                   (mstp-lightest-crossing 3)
                   (mstp-cycle-in-graph 2)
                   (mstp-edge-on-cycle 2)
                   (mstp-cycle-heaviest 2)
                   (mstp-safe-edge 3)
                   (mstp-safe-batch 3)
                   (mstp-useless-edge 3)
                   (mstp-tree-spans 2)
                   (mstp-tree-acyclic 2)
                   (mstp-path-max-dominates-nontree-edges 2)
                   (mstp-replacement-edge 4)
                   (mstp-all-replacements 3)
                   (mstp-sample 3)
                   (mstp-sample-mst 2)
                   (mstp-f-heavy-filtered 3)
                   (mstp-soft-heap-candidate-set 3)
                   (mstp-corruption-repair-valid 3)
                   (mstp-matroid 1)
                   (mstp-basis 2)
                   (mstp-graphic-matroid-of 2)
                   (mstp-weight-order-for 2)
                   (mstp-offline-update-sequence 1)
                   (mstp-update-reductions-valid 2)
                   (mstp-fragments-have-min-outgoing 3)
                   (mstp-ghs-messages-valid 3)
                   (mstp-spanning-tree-out 3)
                   (mstp-mst-out 3)
                   (mstp-crossing-witness-out 4)
                   (mstp-exchange-spanning-out 5)
                   (mstp-exchange-weight-out 5)
                   (mstp-blue-rule-out 4)
                   (mstp-red-rule-out 4)
                   (mstp-contract-safe-out 4)
                   (mstp-delete-useless-out 4)
                   (mstp-boruvka-batch-out 4)
                   (mstp-verifier-out 3)
                   (mstp-replacement-out 4)
                   (mstp-second-best-out 3)
                   (mstp-f-heavy-filter-out 4)
                   (mstp-kkt-out 3)
                   (mstp-soft-heap-out 4)
                   (mstp-matroid-greedy-out 4)
                   (mstp-dynamic-out 3)
                   (mstp-ghs-out 4)
                   (mstp-reverse-delete-algorithm-out 3)
                   (mstp-kruskal-algorithm-out 3)
                   (mstp-prim-algorithm-out 4)
                   (mstp-boruvka-algorithm-out 3)
                   (mstp-filter-kruskal-algorithm-out 3)))
    (apply #'declare-relation entry)))

(defun new-mst-prelude-spanning-tree-definition ()
  ;; SpanningTree(G,T) expands to input-edge, spanning, and acyclicity facts.
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-all-input-edges g tree)
          :name 'mstp-input-edges-premise)
  (assert '(mstp-spans g tree)
          :name 'mstp-spans-premise)
  (assert '(mstp-acyclic tree)
          :name 'mstp-acyclic-premise)
  (assert '(implies
            (and (mstp-all-input-edges g tree)
                 (mstp-spans g tree)
                 (mstp-acyclic tree))
            (mstp-spanning-tree g tree))
          :name 'mstp-spanning-tree-definition)
  (assert '(implies
            (mstp-spanning-tree g tree)
            (mstp-spanning-tree-out g tree tree))
          :name 'mstp-spanning-tree-witness)
  (prove '(mstp-spanning-tree-out g tree ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-mst-definition ()
  ;; MST(G,T) is a spanning tree that is no heavier than an arbitrary
  ;; competitor OTHER.  In the finite-set interpretation, OTHER ranges over
  ;; reified candidate spanning trees.
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-spanning-tree g tree)
          :name 'mstp-mst-spanning-premise)
  (assert '(mstp-competitor-no-lighter g tree other)
          :name 'mstp-mst-competitor-premise)
  (assert '(implies
            (and (mstp-spanning-tree g tree)
                 (mstp-competitor-no-lighter g tree other))
            (mstp-mst g tree))
          :name 'mstp-mst-definition)
  (assert '(implies
            (mstp-mst g tree)
            (mstp-mst-out g tree tree))
          :name 'mstp-mst-witness)
  (prove '(mstp-mst-out g tree ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-crossing-edge-witness ()
  ;; A reified tree path crossing a cut has a first crossing edge selected by
  ;; the function MSTP-CROSSING-EDGE.
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-path-in-tree tree u v path)
          :name 'mstp-path-premise)
  (assert '(mstp-path-crosses-cut path cut)
          :name 'mstp-path-crosses-premise)
  (assert '(implies
            (and (mstp-path-in-tree tree u v path)
                 (mstp-path-crosses-cut path cut))
            (mstp-edge-on-path (mstp-crossing-edge path cut) path))
          :name 'mstp-crossing-edge-on-path)
  (assert '(implies
            (and (mstp-path-in-tree tree u v path)
                 (mstp-path-crosses-cut path cut))
            (mstp-crosses-cut (mstp-crossing-edge path cut) cut))
          :name 'mstp-crossing-edge-crosses)
  (assert '(implies
            (and (mstp-path-in-tree tree u v path)
                 (mstp-path-crosses-cut path cut))
            (mstp-crossing-witness-out
             tree
             path
             cut
             (mstp-crossing-edge path cut)))
          :name 'mstp-crossing-witness)
  (prove '(mstp-crossing-witness-out tree path cut ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-exchange-spanning-lemma ()
  ;; Replacing OLD on the tree path by a crossing EDGE preserves the spanning
  ;; tree property.
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-spanning-tree g tree)
          :name 'mstp-exchange-tree-premise)
  (assert '(mstp-edge-on-path old path)
          :name 'mstp-exchange-old-on-path)
  (assert '(mstp-crosses-cut old cut)
          :name 'mstp-exchange-old-crosses)
  (assert '(mstp-crosses-cut edge cut)
          :name 'mstp-exchange-edge-crosses)
  (assert '(implies
            (and (mstp-spanning-tree g tree)
                 (mstp-edge-on-path old path)
                 (mstp-crosses-cut old cut)
                 (mstp-crosses-cut edge cut))
            (mstp-spanning-tree
             g
             (mstp-exchange tree old edge)))
          :name 'mstp-exchange-preserves-spanning-tree)
  (assert '(implies
            (and (mstp-spanning-tree g tree)
                 (mstp-edge-on-path old path)
                 (mstp-crosses-cut old cut)
                 (mstp-crosses-cut edge cut))
            (mstp-exchange-spanning-out
             g tree old edge (mstp-exchange tree old edge)))
          :name 'mstp-exchange-spanning-witness)
  (prove '(mstp-exchange-spanning-out g tree old edge ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-exchange-weight-lemma ()
  ;; A lightest crossing EDGE is no heavier than the OLD crossing edge it
  ;; replaces, so the exchange tree is no heavier.
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-lightest-crossing g edge cut)
          :name 'mstp-lightest-premise)
  (assert '(mstp-crosses-cut old cut)
          :name 'mstp-old-crosses-premise)
  (assert '(implies
            (and (mstp-lightest-crossing g edge cut)
                 (mstp-crosses-cut old cut))
            (mstp-total-weight-leq
             (mstp-exchange tree old edge)
             tree))
          :name 'mstp-exchange-nonheavier-definition)
  (assert '(implies
            (and (mstp-lightest-crossing g edge cut)
                 (mstp-crosses-cut old cut))
            (mstp-exchange-weight-out
             g tree old edge (mstp-exchange tree old edge)))
          :name 'mstp-exchange-weight-witness)
  (prove '(mstp-exchange-weight-out g tree old edge ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-blue-rule-lemma ()
  ;; Blue/cut rule assembled from the crossing witness and exchange lemmas.
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-mst g tree)
          :name 'mstp-blue-mst-premise)
  (assert '(mstp-spanning-tree g tree)
          :name 'mstp-blue-spanning-premise)
  (assert '(mstp-extends tree forest)
          :name 'mstp-blue-extends-premise)
  (assert '(mstp-cut-respects-forest forest cut)
          :name 'mstp-blue-respects-premise)
  (assert '(mstp-crosses-cut edge cut)
          :name 'mstp-blue-edge-crosses-premise)
  (assert '(mstp-lightest-crossing g edge cut)
          :name 'mstp-blue-lightest-premise)
  (assert '(mstp-path-in-tree tree u v path)
          :name 'mstp-blue-path-premise)
  (assert '(mstp-path-crosses-cut path cut)
          :name 'mstp-blue-path-crosses-premise)
  (assert '(implies
            (and (mstp-path-in-tree tree u v path)
                 (mstp-path-crosses-cut path cut))
            (mstp-edge-on-path (mstp-crossing-edge path cut) path))
          :name 'mstp-import-crossing-edge-on-path)
  (assert '(implies
            (and (mstp-path-in-tree tree u v path)
                 (mstp-path-crosses-cut path cut))
            (mstp-crosses-cut (mstp-crossing-edge path cut) cut))
          :name 'mstp-import-crossing-edge-crosses)
  (assert '(implies
            (and (mstp-spanning-tree g tree)
                 (mstp-edge-on-path (mstp-crossing-edge path cut) path)
                 (mstp-crosses-cut (mstp-crossing-edge path cut) cut)
                 (mstp-crosses-cut edge cut))
            (mstp-spanning-tree
             g
             (mstp-exchange tree (mstp-crossing-edge path cut) edge)))
          :name 'mstp-import-exchange-spanning)
  (assert '(implies
            (and (mstp-lightest-crossing g edge cut)
                 (mstp-crosses-cut (mstp-crossing-edge path cut) cut))
            (mstp-total-weight-leq
             (mstp-exchange tree (mstp-crossing-edge path cut) edge)
             tree))
          :name 'mstp-import-exchange-weight)
  (assert '(implies
            (and (mstp-mst g tree)
                 (mstp-spanning-tree
                  g
                  (mstp-exchange tree (mstp-crossing-edge path cut) edge))
                 (mstp-total-weight-leq
                  (mstp-exchange tree (mstp-crossing-edge path cut) edge)
                  tree))
            (mstp-mst
             g
             (mstp-exchange tree (mstp-crossing-edge path cut) edge)))
          :name 'mstp-nonheavier-spanning-tree-is-mst)
  (assert '(implies
            (and (mstp-extends tree forest)
                 (mstp-cut-respects-forest forest cut)
                 (mstp-crosses-cut edge cut))
            (mstp-extends
             (mstp-exchange tree (mstp-crossing-edge path cut) edge)
             (mstp-add-edge edge forest)))
          :name 'mstp-exchange-extends-forest-with-edge)
  (assert '(implies
            (and (mstp-mst
                  g
                  (mstp-exchange tree (mstp-crossing-edge path cut) edge))
                 (mstp-extends
                  (mstp-exchange tree (mstp-crossing-edge path cut) edge)
                  (mstp-add-edge edge forest)))
            (mstp-safe-edge g forest edge))
          :name 'mstp-safe-edge-definition)
  (assert '(implies
            (mstp-safe-edge g forest edge)
            (mstp-blue-rule-out
             g
             forest
             edge
             (mstp-exchange tree (mstp-crossing-edge path cut) edge)))
          :name 'mstp-blue-rule-program)
  (prove '(mstp-blue-rule-out g forest edge ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-red-rule-lemma ()
  ;; Red/cycle rule: exchange an MST that contains a heaviest cycle edge for a
  ;; no-heavier MST omitting it, yielding the delete-edge program.
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-cycle-in-graph g cycle)
          :name 'mstp-red-cycle-premise)
  (assert '(mstp-edge-on-cycle edge cycle)
          :name 'mstp-red-edge-on-cycle-premise)
  (assert '(mstp-cycle-heaviest edge cycle)
          :name 'mstp-red-heaviest-premise)
  (assert '(mstp-mst g tree)
          :name 'mstp-red-mst-premise)
  (assert '(mstp-edge-in-tree edge tree)
          :name 'mstp-red-edge-in-tree-premise)
  (assert '(implies
            (and (mstp-cycle-in-graph g cycle)
                 (mstp-edge-on-cycle edge cycle)
                 (mstp-cycle-heaviest edge cycle)
                 (mstp-mst g tree)
                 (mstp-edge-in-tree edge tree))
            (mstp-mst
             (mstp-delete-edge edge g)
             (mstp-exchange
              tree
              edge
              (mstp-cycle-replacement-edge cycle edge))))
          :name 'mstp-cycle-exchange-red-theorem)
  (assert '(implies
            (mstp-mst
             (mstp-delete-edge edge g)
             (mstp-exchange
              tree
              edge
              (mstp-cycle-replacement-edge cycle edge)))
            (mstp-red-rule-out
             g
             tree
             edge
             (mstp-delete-edge edge g)))
          :name 'mstp-red-rule-program)
  (prove '(mstp-red-rule-out g tree edge ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-contract-safe-lemma ()
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-safe-edge g forest edge)
          :name 'mstp-contract-safe-premise)
  (assert '(mstp-mst (mstp-contract-edge edge g) tree)
          :name 'mstp-contracted-mst-premise)
  (assert '(implies
            (and (mstp-safe-edge g forest edge)
                 (mstp-mst (mstp-contract-edge edge g) tree))
            (mstp-mst g (mstp-lift edge tree)))
          :name 'mstp-contract-safe-lift-theorem)
  (assert '(implies
            (mstp-mst g (mstp-lift edge tree))
            (mstp-contract-safe-out
             g forest edge (mstp-lift edge tree)))
          :name 'mstp-contract-safe-program)
  (prove '(mstp-contract-safe-out g forest edge ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-delete-useless-lemma ()
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-useless-edge g forest edge)
          :name 'mstp-delete-useless-premise)
  (assert '(mstp-mst (mstp-delete-edge edge g) tree)
          :name 'mstp-deleted-mst-premise)
  (assert '(implies
            (and (mstp-useless-edge g forest edge)
                 (mstp-mst (mstp-delete-edge edge g) tree))
            (mstp-mst g tree))
          :name 'mstp-delete-useless-theorem)
  (assert '(implies
            (mstp-mst g tree)
            (mstp-delete-useless-out
             g forest edge (mstp-delete-edge edge g)))
          :name 'mstp-delete-useless-program)
  (prove '(mstp-delete-useless-out g forest edge ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-boruvka-batch-lemma ()
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-safe-batch g forest batch)
          :name 'mstp-boruvka-safe-batch-premise)
  (assert '(mstp-mst (mstp-contract-set g batch) tree)
          :name 'mstp-boruvka-contracted-mst-premise)
  (assert '(implies
            (and (mstp-safe-batch g forest batch)
                 (mstp-mst (mstp-contract-set g batch) tree))
            (mstp-mst g (mstp-lift batch tree)))
          :name 'mstp-safe-batch-lift-theorem)
  (assert '(implies
            (mstp-mst g (mstp-lift batch tree))
            (mstp-boruvka-batch-out
             g forest batch (mstp-lift batch tree)))
          :name 'mstp-boruvka-batch-program)
  (prove '(mstp-boruvka-batch-out g forest batch ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-verification-lemma ()
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-tree-spans g tree)
          :name 'mstp-verifier-spans-premise)
  (assert '(mstp-tree-acyclic g tree)
          :name 'mstp-verifier-acyclic-premise)
  (assert '(mstp-path-max-dominates-nontree-edges g tree)
          :name 'mstp-verifier-path-max-premise)
  (assert '(implies
            (and (mstp-tree-spans g tree)
                 (mstp-tree-acyclic g tree)
                 (mstp-path-max-dominates-nontree-edges g tree))
            (mstp-mst g tree))
          :name 'mstp-path-max-verification-theorem)
  (assert '(implies
            (mstp-mst g tree)
            (mstp-verifier-out g tree (mstp-verify-tree g tree)))
          :name 'mstp-verifier-program)
  (prove '(mstp-verifier-out g tree ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-replacement-edge-lemma ()
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-replacement-edge g tree edge replacement)
          :name 'mstp-replacement-premise)
  (assert '(implies
            (mstp-replacement-edge g tree edge replacement)
            (mstp-replacement-out
             g
             tree
             edge
             (mstp-record-replacement edge replacement)))
          :name 'mstp-replacement-program)
  (prove '(mstp-replacement-out g tree edge ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-second-best-lemma ()
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-all-replacements g tree replacement)
          :name 'mstp-all-replacements-premise)
  (assert '(implies
            (mstp-all-replacements g tree replacement)
            (mstp-second-best-out
             g
             tree
             (mstp-second-best-from-replacements tree replacement)))
          :name 'mstp-second-best-program)
  (prove '(mstp-second-best-out g tree ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-f-heavy-filter-lemma ()
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-sample-mst sample sample-tree)
          :name 'mstp-f-heavy-sample-tree-premise)
  (assert '(mstp-f-heavy-filtered g sample-tree filtered)
          :name 'mstp-f-heavy-filtered-premise)
  (assert '(implies
            (and (mstp-sample-mst sample sample-tree)
                 (mstp-f-heavy-filtered g sample-tree filtered))
            (mstp-f-heavy-filter-out
             g
             sample-tree
             filtered
             (mstp-filter-heavy g sample-tree)))
          :name 'mstp-f-heavy-filter-program)
  (prove '(mstp-f-heavy-filter-out g sample-tree filtered ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-kkt-filter-lemma ()
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-sample g random-source sample)
          :name 'mstp-kkt-sample-premise)
  (assert '(mstp-sample-mst sample sample-tree)
          :name 'mstp-kkt-sample-mst-premise)
  (assert '(mstp-f-heavy-filtered g sample-tree filtered)
          :name 'mstp-kkt-filtered-premise)
  (assert '(implies
            (and (mstp-sample g random-source sample)
                 (mstp-sample-mst sample sample-tree)
                 (mstp-f-heavy-filtered g sample-tree filtered))
            (mstp-kkt-out
             g
             random-source
             (mstp-kkt filtered random-source)))
          :name 'mstp-kkt-program)
  (prove '(mstp-kkt-out g random-source ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-soft-heap-repair-lemma ()
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-soft-heap-candidate-set g epsilon heap)
          :name 'mstp-soft-heap-candidates-premise)
  (assert '(mstp-corruption-repair-valid g heap filtered)
          :name 'mstp-soft-heap-repair-premise)
  (assert '(implies
            (and (mstp-soft-heap-candidate-set g epsilon heap)
                 (mstp-corruption-repair-valid g heap filtered))
            (mstp-soft-heap-out
             g
             epsilon
             heap
             (mstp-repair-corruptions
              g
              (mstp-soft-heap-candidates g epsilon))))
          :name 'mstp-soft-heap-program)
  (prove '(mstp-soft-heap-out g epsilon heap ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-matroid-greedy-lemma ()
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-matroid matroid)
          :name 'mstp-matroid-premise)
  (assert '(mstp-weight-order-for matroid order)
          :name 'mstp-matroid-weight-order-premise)
  (assert '(implies
            (and (mstp-matroid matroid)
                 (mstp-weight-order-for matroid order))
            (mstp-basis matroid (mstp-matroid-greedy matroid order)))
          :name 'mstp-matroid-greedy-basis-theorem)
  (assert '(implies
            (mstp-basis matroid (mstp-matroid-greedy matroid order))
            (mstp-matroid-greedy-out
             g
             matroid
             order
             (mstp-matroid-greedy matroid order)))
          :name 'mstp-matroid-greedy-program)
  (prove '(mstp-matroid-greedy-out g matroid order ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-dynamic-lemma ()
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-offline-update-sequence updates)
          :name 'mstp-dynamic-updates-premise)
  (assert '(mstp-update-reductions-valid g updates)
          :name 'mstp-dynamic-reductions-premise)
  (assert '(implies
            (and (mstp-offline-update-sequence updates)
                 (mstp-update-reductions-valid g updates))
            (mstp-dynamic-out
             g
             updates
             (mstp-dynamic-sequence g updates)))
          :name 'mstp-dynamic-program)
  (prove '(mstp-dynamic-out g updates ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-ghs-lemma ()
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-fragments-have-min-outgoing g fragments batch)
          :name 'mstp-ghs-fragments-premise)
  (assert '(mstp-ghs-messages-valid g fragments messages)
          :name 'mstp-ghs-messages-premise)
  (assert '(implies
            (and (mstp-fragments-have-min-outgoing g fragments batch)
                 (mstp-ghs-messages-valid g fragments messages))
            (mstp-ghs-out
             g
             fragments
             messages
             (mstp-ghs-phase g fragments)))
          :name 'mstp-ghs-program)
  (prove '(mstp-ghs-out g fragments messages ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-reverse-delete-algorithm ()
  ;; Algorithm layer consuming the red-rule lemma term.
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-red-rule-out g tree edge (mstp-delete-edge edge g))
          :name 'mstp-import-red-rule)
  (assert '(implies
            (mstp-red-rule-out g tree edge (mstp-delete-edge edge g))
            (mstp-reverse-delete-algorithm-out
             g
             edge
             (mstp-reverse-delete (mstp-delete-edge edge g))))
          :name 'mstp-reverse-delete-algorithm)
  (prove '(mstp-reverse-delete-algorithm-out g edge ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-kruskal-algorithm ()
  ;; Kruskal consumes the blue-rule/safe-edge lemma by adding the chosen edge
  ;; to the current forest.
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-blue-rule-out
            g
            forest
            edge
            (mstp-exchange tree (mstp-crossing-edge path cut) edge))
          :name 'mstp-import-blue-rule)
  (assert '(implies
            (mstp-blue-rule-out
             g
             forest
             edge
             (mstp-exchange tree (mstp-crossing-edge path cut) edge))
            (mstp-kruskal-algorithm-out
             g
             forest
             (mstp-kruskal-step g (mstp-add-edge edge forest))))
          :name 'mstp-kruskal-algorithm)
  (prove '(mstp-kruskal-algorithm-out g forest ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-prim-algorithm ()
  ;; Prim/Jarnik uses the same blue-rule lemma but with a root/frontier policy.
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-blue-rule-out
            g
            forest
            edge
            (mstp-exchange tree (mstp-crossing-edge path cut) edge))
          :name 'mstp-import-blue-rule)
  (assert '(implies
            (mstp-blue-rule-out
             g
             forest
             edge
             (mstp-exchange tree (mstp-crossing-edge path cut) edge))
            (mstp-prim-algorithm-out
             g
             forest
             edge
             (mstp-prim-step g (mstp-add-edge edge forest) u)))
          :name 'mstp-prim-algorithm)
  (prove '(mstp-prim-algorithm-out g forest edge ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-boruvka-algorithm ()
  ;; Boruvka consumes the safe-batch/lift lemma.
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-boruvka-batch-out
            g
            forest
            batch
            (mstp-lift batch tree))
          :name 'mstp-import-boruvka-batch)
  (assert '(implies
            (mstp-boruvka-batch-out
             g
             forest
             batch
             (mstp-lift batch tree))
            (mstp-boruvka-algorithm-out
             g
             forest
             (mstp-boruvka-phase g (mstp-contract-set g batch))))
          :name 'mstp-boruvka-algorithm)
  (prove '(mstp-boruvka-algorithm-out g forest ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-filter-kruskal-algorithm ()
  ;; Filter-Kruskal consumes the F-heavy filter lemma before a Kruskal pass.
  (new-mst-prelude-setup)
  (new-mst-prelude-declare-language)
  (assert '(mstp-f-heavy-filter-out
            g
            sample-tree
            filtered
            (mstp-filter-heavy g sample-tree))
          :name 'mstp-import-f-heavy-filter)
  (assert '(implies
            (mstp-f-heavy-filter-out
             g
             sample-tree
             filtered
             (mstp-filter-heavy g sample-tree))
            (mstp-filter-kruskal-algorithm-out
             g
             filtered
             (mstp-filter-kruskal filtered)))
          :name 'mstp-filter-kruskal-algorithm)
  (prove '(mstp-filter-kruskal-algorithm-out g filtered ?answer)
         :answer '(values ?answer))
  (new-mst-prelude-answer))

(defun new-mst-prelude-synthesis-examples ()
  (list
   (list 'spanning-tree-definition
         (new-mst-prelude-spanning-tree-definition))
   (list 'mst-definition
         (new-mst-prelude-mst-definition))
   (list 'crossing-edge-witness
         (new-mst-prelude-crossing-edge-witness))
   (list 'exchange-spanning-lemma
         (new-mst-prelude-exchange-spanning-lemma))
   (list 'exchange-weight-lemma
         (new-mst-prelude-exchange-weight-lemma))
   (list 'blue-rule-lemma
         (new-mst-prelude-blue-rule-lemma))
   (list 'red-rule-lemma
         (new-mst-prelude-red-rule-lemma))
   (list 'contract-safe-lemma
         (new-mst-prelude-contract-safe-lemma))
   (list 'delete-useless-lemma
         (new-mst-prelude-delete-useless-lemma))
   (list 'boruvka-batch-lemma
         (new-mst-prelude-boruvka-batch-lemma))
   (list 'verification-lemma
         (new-mst-prelude-verification-lemma))
   (list 'replacement-edge-lemma
         (new-mst-prelude-replacement-edge-lemma))
   (list 'second-best-lemma
         (new-mst-prelude-second-best-lemma))
   (list 'f-heavy-filter-lemma
         (new-mst-prelude-f-heavy-filter-lemma))
   (list 'kkt-filter-lemma
         (new-mst-prelude-kkt-filter-lemma))
   (list 'soft-heap-repair-lemma
         (new-mst-prelude-soft-heap-repair-lemma))
   (list 'matroid-greedy-lemma
         (new-mst-prelude-matroid-greedy-lemma))
   (list 'dynamic-lemma
         (new-mst-prelude-dynamic-lemma))
   (list 'ghs-lemma
         (new-mst-prelude-ghs-lemma))
   (list 'reverse-delete-algorithm
         (new-mst-prelude-reverse-delete-algorithm))
   (list 'kruskal-algorithm
         (new-mst-prelude-kruskal-algorithm))
   (list 'prim-algorithm
         (new-mst-prelude-prim-algorithm))
   (list 'boruvka-algorithm
         (new-mst-prelude-boruvka-algorithm))
   (list 'filter-kruskal-algorithm
         (new-mst-prelude-filter-kruskal-algorithm))))

;;; new-mst-prelude-synthesis.lisp EOF
