;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark-user -*-
;;; File: examples/synthesis/new-mst-fol-synthesis.lisp
;;;
;;; Strict first-order MST layer for the non-probabilistic pipeline.
;;;
;;; The older MST prelude names obligations such as LIGHTEST-CROSSING and
;;; SAFE-BATCH directly.  This file pushes the ordinary MST spine down one
;;; level: finite edge lists, path certificates, cut-side certificates,
;;; component certificates, bridge certificates, and finite weight-comparison
;;; certificates are the premises.  The blue rule, red rule, batch safety, and
;;; Kruskal/Prim/Boruvka program terms are then derived by SNARK answer
;;; extraction from those first-order certificates.

(in-package :snark-user)

(defun new-mst-fol-setup ()
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

(defun new-mst-fol-answer ()
  (answer t))

(defun new-mst-fol-declare-language ()
  (dolist (name '(g vertices edges tree forest edge old replacement cut cycle
                  path batch component components root u v w w-old
                  crossing-edges bridge-certs span-certs compare-certs
                  component-certs batch-certs mstf-empty))
    (declare-constant name))
  (dolist (entry '((mstf-cons 2)
                   (mstf-add-edge 2)
                   (mstf-add-batch 2)
                   (mstf-delete-edge 2)
                   (mstf-contract-set 2)
                   (mstf-contract-forest 2)
                   (mstf-exchange 3)
                   (mstf-crossing-edge 2)
                   (mstf-cycle-replacement-edge 2)
                   (mstf-lift 2)
                   (mstf-kruskal-step 2)
                   (mstf-prim-step 3)
                   (mstf-boruvka-phase 2)
                   (mstf-component-cut 1)))
    (apply #'declare-function entry))
  (dolist (entry '((mstf-finite-list 1)
                   (mstf-member 2)
                   (mstf-subset 2)
                   (mstf-edges-of 2)
                   (mstf-vertices-of 2)
                   (mstf-inc 3)
                   (mstf-weight 2)
                   (mstf-leq 2)
                   (mstf-in-graph 2)
                   (mstf-edge-in-tree 2)
                   (mstf-path-list 1)
                   (mstf-path-connects 3)
                   (mstf-path-edge 2)
                   (mstf-path-edges-in-tree 2)
                   (mstf-reaches 4)
                   (mstf-cut-side 2)
                   (mstf-cut-outside 2)
                   (mstf-crosses-cut 2)
                   (mstf-path-crosses-cut 2)
                   (mstf-component-of 3)
                   (mstf-same-component 3)
                   (mstf-components-of 2)
                   (mstf-distinct-components 4)
                   (mstf-all-tree-edges-input 2)
                   (mstf-all-connected-pairs-have-tree-paths 3)
                   (mstf-spans 2)
                   (mstf-bridge-cut-for-edge 3)
                   (mstf-all-edges-have-bridge-cuts 2)
                   (mstf-acyclic 1)
                   (mstf-spanning-tree 2)
                   (mstf-total-weight-leq 2)
                   (mstf-no-heavier-edge 2)
                   (mstf-dominates-list 3)
                   (mstf-crossing-edges-for-cut 3)
                   (mstf-lightest-crossing 3)
                   (mstf-tree-extends-forest 2)
                   (mstf-mst 2)
                   (mstf-nonheavier-mst 3)
                   (mstf-cycle-list 1)
                   (mstf-cycle-edge 2)
                   (mstf-cycle-in-graph 2)
                   (mstf-heaviest-on-cycle 3)
                   (mstf-batch-of-component-minima 4)
                   (mstf-batch-edges-have-blue-cuts 4)
                   (mstf-safe-batch 3)
                   (mstf-kruskal-cross-component-minimum 4)
                   (mstf-prim-frontier-minimum 5)
                   (mstf-boruvka-component-minima 4)
                   (mstf-list-member-out 3)
                   (mstf-input-edge-out 3)
                   (mstf-tree-subset-out 3)
                   (mstf-path-out 5)
                   (mstf-cut-crossing-out 4)
                   (mstf-component-out 5)
                   (mstf-acyclic-out 3)
                   (mstf-weight-compare-out 4)
                   (mstf-lightest-crossing-out 4)
                   (mstf-spanning-tree-out 3)
                   (mstf-exchange-out 5)
                   (mstf-blue-rule-out 4)
                   (mstf-red-rule-out 4)
                   (mstf-batch-safety-out 4)
                   (mstf-kruskal-out 3)
                   (mstf-prim-out 4)
                   (mstf-boruvka-out 3)))
    (apply #'declare-relation entry)))

(defun new-mst-fol-finite-list-membership ()
  ;; Finite lists are first-order terms.  The head of a cons cell is a member.
  (new-mst-fol-setup)
  (new-mst-fol-declare-language)
  (assert '(mstf-finite-list edges)
          :name 'mstf-tail-list)
  (assert '(implies
            (mstf-finite-list edges)
            (mstf-finite-list (mstf-cons edge edges)))
          :name 'mstf-cons-is-list)
  (assert '(implies
            (mstf-finite-list edges)
            (mstf-member edge (mstf-cons edge edges)))
          :name 'mstf-cons-head-member)
  (assert '(implies
            (mstf-member edge (mstf-cons edge edges))
            (mstf-list-member-out edge (mstf-cons edge edges) edge))
          :name 'mstf-member-program)
  (prove '(mstf-list-member-out edge (mstf-cons edge edges) ?answer)
         :answer '(values ?answer))
  (new-mst-fol-answer))

(defun new-mst-fol-input-edge-from-finite-list ()
  ;; An edge is in the graph exactly by membership in the graph's finite edge
  ;; list.
  (new-mst-fol-setup)
  (new-mst-fol-declare-language)
  (assert '(mstf-edges-of g edges)
          :name 'mstf-graph-edge-list)
  (assert '(mstf-finite-list edges)
          :name 'mstf-finite-edge-list)
  (assert '(mstf-member edge edges)
          :name 'mstf-edge-member-certificate)
  (assert '(implies
            (and (mstf-edges-of g edges)
                 (mstf-finite-list edges)
                 (mstf-member edge edges))
            (mstf-in-graph g edge))
          :name 'mstf-input-edge-definition)
  (assert '(implies
            (mstf-in-graph g edge)
            (mstf-input-edge-out g edge edge))
          :name 'mstf-input-edge-program)
  (prove '(mstf-input-edge-out g edge ?answer)
         :answer '(values ?answer))
  (new-mst-fol-answer))

(defun new-mst-fol-tree-subset-from-finite-lists ()
  ;; A tree's edge set is graph-local when the finite tree list is a subset of
  ;; the finite graph edge list.
  (new-mst-fol-setup)
  (new-mst-fol-declare-language)
  (assert '(mstf-edges-of g edges)
          :name 'mstf-subset-graph-edge-list)
  (assert '(mstf-finite-list tree)
          :name 'mstf-tree-list)
  (assert '(mstf-finite-list edges)
          :name 'mstf-edge-list)
  (assert '(mstf-subset tree edges)
          :name 'mstf-subset-certificate)
  (assert '(implies
            (and (mstf-edges-of g edges)
                 (mstf-finite-list tree)
                 (mstf-finite-list edges)
                 (mstf-subset tree edges))
            (mstf-all-tree-edges-input g tree))
          :name 'mstf-all-tree-edges-input-definition)
  (assert '(implies
            (mstf-all-tree-edges-input g tree)
            (mstf-tree-subset-out g tree tree))
          :name 'mstf-tree-subset-program)
  (prove '(mstf-tree-subset-out g tree ?answer)
         :answer '(values ?answer))
  (new-mst-fol-answer))

(defun new-mst-fol-path-from-finite-list ()
  ;; Reachability is supplied by a finite path object whose edges are all tree
  ;; edges and whose endpoints are U and V.
  (new-mst-fol-setup)
  (new-mst-fol-declare-language)
  (assert '(mstf-path-list path)
          :name 'mstf-path-is-list)
  (assert '(mstf-path-connects path u v)
          :name 'mstf-path-endpoints)
  (assert '(mstf-path-edges-in-tree path tree)
          :name 'mstf-path-tree-certificate)
  (assert '(implies
            (and (mstf-path-list path)
                 (mstf-path-connects path u v)
                 (mstf-path-edges-in-tree path tree))
            (mstf-reaches tree u v path))
          :name 'mstf-reachability-definition)
  (assert '(implies
            (mstf-reaches tree u v path)
            (mstf-path-out tree u v path path))
          :name 'mstf-path-program)
  (prove '(mstf-path-out tree u v path ?answer)
         :answer '(values ?answer))
  (new-mst-fol-answer))

(defun new-mst-fol-cut-crossing-from-endpoints ()
  ;; Cut crossing is reduced to incidence plus opposite cut-side certificates.
  (new-mst-fol-setup)
  (new-mst-fol-declare-language)
  (assert '(mstf-inc edge u v)
          :name 'mstf-cut-incidence)
  (assert '(mstf-cut-side cut u)
          :name 'mstf-cut-left)
  (assert '(mstf-cut-outside cut v)
          :name 'mstf-cut-right)
  (assert '(implies
            (and (mstf-inc edge u v)
                 (mstf-cut-side cut u)
                 (mstf-cut-outside cut v))
            (mstf-crosses-cut edge cut))
          :name 'mstf-cut-crossing-definition)
  (assert '(implies
            (mstf-crosses-cut edge cut)
            (mstf-cut-crossing-out edge cut u edge))
          :name 'mstf-cut-crossing-program)
  (prove '(mstf-cut-crossing-out edge cut u ?answer)
         :answer '(values ?answer))
  (new-mst-fol-answer))

(defun new-mst-fol-component-from-path ()
  ;; Components are finite reachability equivalence classes, witnessed here by
  ;; an explicit tree/forest path.
  (new-mst-fol-setup)
  (new-mst-fol-declare-language)
  (assert '(mstf-reaches forest u v path)
          :name 'mstf-component-reachability)
  (assert '(mstf-component-of forest u component)
          :name 'mstf-component-root-certificate)
  (assert '(implies
            (and (mstf-reaches forest u v path)
                 (mstf-component-of forest u component))
            (mstf-component-of forest v component))
          :name 'mstf-component-closure)
  (assert '(implies
            (and (mstf-component-of forest u component)
                 (mstf-component-of forest v component))
            (mstf-same-component forest u v))
          :name 'mstf-same-component-definition)
  (assert '(implies
            (mstf-same-component forest u v)
            (mstf-component-out forest u v path component))
          :name 'mstf-component-program)
  (prove '(mstf-component-out forest u v path ?answer)
         :answer '(values ?answer))
  (new-mst-fol-answer))

(defun new-mst-fol-acyclic-from-bridge-cuts ()
  ;; A finite tree-edge list is acyclic when every listed edge has a bridge cut
  ;; certificate in the selected subgraph with that edge removed.
  (new-mst-fol-setup)
  (new-mst-fol-declare-language)
  (assert '(mstf-finite-list tree)
          :name 'mstf-acyclic-tree-list)
  (assert '(mstf-all-edges-have-bridge-cuts tree bridge-certs)
          :name 'mstf-bridge-certificate-list)
  (assert '(implies
            (and (mstf-finite-list tree)
                 (mstf-all-edges-have-bridge-cuts tree bridge-certs))
            (mstf-acyclic tree))
          :name 'mstf-bridge-definition-of-acyclicity)
  (assert '(implies
            (mstf-acyclic tree)
            (mstf-acyclic-out tree bridge-certs tree))
          :name 'mstf-acyclic-program)
  (prove '(mstf-acyclic-out tree bridge-certs ?answer)
         :answer '(values ?answer))
  (new-mst-fol-answer))

(defun new-mst-fol-weight-comparison ()
  ;; Finite weight comparison is first-order: the weight objects W and W-OLD
  ;; are related by LEQ.
  (new-mst-fol-setup)
  (new-mst-fol-declare-language)
  (assert '(mstf-weight edge w)
          :name 'mstf-edge-weight)
  (assert '(mstf-weight old w-old)
          :name 'mstf-old-weight)
  (assert '(mstf-leq w w-old)
          :name 'mstf-weight-order-certificate)
  (assert '(implies
            (and (mstf-weight edge w)
                 (mstf-weight old w-old)
                 (mstf-leq w w-old))
            (mstf-no-heavier-edge edge old))
          :name 'mstf-edge-comparison-definition)
  (assert '(implies
            (mstf-no-heavier-edge edge old)
            (mstf-weight-compare-out edge old w edge))
          :name 'mstf-weight-comparison-program)
  (prove '(mstf-weight-compare-out edge old w ?answer)
         :answer '(values ?answer))
  (new-mst-fol-answer))

(defun new-mst-fol-lightest-crossing-from-finite-comparisons ()
  ;; A lightest crossing edge is a finite-list member that dominates every
  ;; other crossing edge by the supplied comparison certificate list.
  (new-mst-fol-setup)
  (new-mst-fol-declare-language)
  (assert '(mstf-crossing-edges-for-cut g cut crossing-edges)
          :name 'mstf-crossing-edge-list)
  (assert '(mstf-finite-list crossing-edges)
          :name 'mstf-finite-crossing-list)
  (assert '(mstf-member edge crossing-edges)
          :name 'mstf-crossing-member)
  (assert '(mstf-dominates-list edge crossing-edges compare-certs)
          :name 'mstf-finite-domination-certificate)
  (assert '(implies
            (and (mstf-crossing-edges-for-cut g cut crossing-edges)
                 (mstf-finite-list crossing-edges)
                 (mstf-member edge crossing-edges)
                 (mstf-dominates-list edge crossing-edges compare-certs))
            (mstf-lightest-crossing g edge cut))
          :name 'mstf-lightest-crossing-definition)
  (assert '(implies
            (mstf-lightest-crossing g edge cut)
            (mstf-lightest-crossing-out g edge cut edge))
          :name 'mstf-lightest-crossing-program)
  (prove '(mstf-lightest-crossing-out g edge cut ?answer)
         :answer '(values ?answer))
  (new-mst-fol-answer))

(defun new-mst-fol-spanning-tree-from-certificates ()
  ;; Spanning tree is obtained from finite edge inclusion, finite path
  ;; certificates for all connected pairs, and bridge-cut certificates.
  (new-mst-fol-setup)
  (new-mst-fol-declare-language)
  (assert '(mstf-all-tree-edges-input g tree)
          :name 'mstf-spanning-input-certificate)
  (assert '(mstf-all-connected-pairs-have-tree-paths g tree span-certs)
          :name 'mstf-spanning-path-certificates)
  (assert '(mstf-all-edges-have-bridge-cuts tree bridge-certs)
          :name 'mstf-spanning-bridge-certificates)
  (assert '(implies
            (mstf-all-connected-pairs-have-tree-paths g tree span-certs)
            (mstf-spans g tree))
          :name 'mstf-spanning-definition)
  (assert '(implies
            (mstf-all-edges-have-bridge-cuts tree bridge-certs)
            (mstf-acyclic tree))
          :name 'mstf-spanning-acyclic-definition)
  (assert '(implies
            (and (mstf-all-tree-edges-input g tree)
                 (mstf-spans g tree)
                 (mstf-acyclic tree))
            (mstf-spanning-tree g tree))
          :name 'mstf-spanning-tree-definition)
  (assert '(implies
            (mstf-spanning-tree g tree)
            (mstf-spanning-tree-out g tree tree))
          :name 'mstf-spanning-tree-program)
  (prove '(mstf-spanning-tree-out g tree ?answer)
         :answer '(values ?answer))
  (new-mst-fol-answer))

(defun new-mst-fol-exchange-from-path-cut-weight ()
  ;; The exchange lemma now consumes only lower finite witnesses: a tree path,
  ;; two cut crossings, and a finite weight comparison.
  (new-mst-fol-setup)
  (new-mst-fol-declare-language)
  (assert '(mstf-spanning-tree g tree)
          :name 'mstf-exchange-tree)
  (assert '(mstf-path-list path)
          :name 'mstf-exchange-path-list)
  (assert '(mstf-path-edge old path)
          :name 'mstf-exchange-old-on-path)
  (assert '(mstf-crosses-cut old cut)
          :name 'mstf-exchange-old-crosses)
  (assert '(mstf-crosses-cut edge cut)
          :name 'mstf-exchange-new-crosses)
  (assert '(mstf-no-heavier-edge edge old)
          :name 'mstf-exchange-weight-comparison)
  (assert '(implies
            (and (mstf-spanning-tree g tree)
                 (mstf-path-list path)
                 (mstf-path-edge old path)
                 (mstf-crosses-cut old cut)
                 (mstf-crosses-cut edge cut))
            (mstf-spanning-tree g (mstf-exchange tree old edge)))
          :name 'mstf-exchange-preserves-spanning-tree)
  (assert '(implies
            (and (mstf-no-heavier-edge edge old)
                 (mstf-spanning-tree g (mstf-exchange tree old edge)))
            (mstf-total-weight-leq (mstf-exchange tree old edge) tree))
          :name 'mstf-exchange-preserves-weight-bound)
  (assert '(implies
            (and (mstf-spanning-tree g (mstf-exchange tree old edge))
                 (mstf-total-weight-leq (mstf-exchange tree old edge) tree))
            (mstf-exchange-out
             g tree old edge (mstf-exchange tree old edge)))
          :name 'mstf-exchange-program)
  (prove '(mstf-exchange-out g tree old edge ?answer)
         :answer '(values ?answer))
  (new-mst-fol-answer))

(defun new-mst-fol-blue-rule-from-exchange ()
  ;; The blue rule is derived from finite cut/path/weight witnesses and the
  ;; exchange lemma.  SAFE-EDGE is not a premise here.
  (new-mst-fol-setup)
  (new-mst-fol-declare-language)
  (assert '(mstf-mst g tree)
          :name 'mstf-blue-mst-tree)
  (assert '(mstf-tree-extends-forest tree forest)
          :name 'mstf-blue-extension-certificate)
  (assert '(mstf-path-list path)
          :name 'mstf-blue-path-list)
  (assert '(mstf-path-crosses-cut path cut)
          :name 'mstf-blue-path-crossing)
  (assert '(mstf-crosses-cut edge cut)
          :name 'mstf-blue-edge-crossing)
  (assert '(mstf-lightest-crossing g edge cut)
          :name 'mstf-blue-lightest-derived)
  (assert '(mstf-no-heavier-edge edge (mstf-crossing-edge path cut))
          :name 'mstf-blue-finite-weight-derived)
  (assert '(implies
            (and (mstf-path-list path)
                 (mstf-path-crosses-cut path cut))
            (mstf-path-edge (mstf-crossing-edge path cut) path))
          :name 'mstf-blue-first-crossing-on-path)
  (assert '(implies
            (and (mstf-path-list path)
                 (mstf-path-crosses-cut path cut))
            (mstf-crosses-cut (mstf-crossing-edge path cut) cut))
          :name 'mstf-blue-first-crossing-crosses)
  (assert '(implies
            (and (mstf-mst g tree)
                 (mstf-path-edge (mstf-crossing-edge path cut) path)
                 (mstf-crosses-cut (mstf-crossing-edge path cut) cut)
                 (mstf-crosses-cut edge cut)
                 (mstf-no-heavier-edge edge (mstf-crossing-edge path cut)))
            (mstf-mst
             g
             (mstf-exchange tree (mstf-crossing-edge path cut) edge)))
          :name 'mstf-blue-exchange-mst)
  (assert '(implies
            (and (mstf-tree-extends-forest tree forest)
                 (mstf-crosses-cut edge cut)
                 (mstf-mst
                  g
                  (mstf-exchange tree (mstf-crossing-edge path cut) edge)))
            (mstf-blue-rule-out
             g
             forest
             edge
             (mstf-exchange tree (mstf-crossing-edge path cut) edge)))
          :name 'mstf-blue-rule-program)
  (prove '(mstf-blue-rule-out g forest edge ?answer)
         :answer '(values ?answer))
  (new-mst-fol-answer))

(defun new-mst-fol-red-rule-from-cycle ()
  ;; The red rule is derived from a finite cycle and finite domination witness
  ;; for the heaviest edge on that cycle.
  (new-mst-fol-setup)
  (new-mst-fol-declare-language)
  (assert '(mstf-cycle-list cycle)
          :name 'mstf-red-cycle-list)
  (assert '(mstf-cycle-edge edge cycle)
          :name 'mstf-red-edge-on-cycle)
  (assert '(mstf-cycle-in-graph g cycle)
          :name 'mstf-red-cycle-in-graph)
  (assert '(mstf-heaviest-on-cycle edge cycle compare-certs)
          :name 'mstf-red-finite-weight-domination)
  (assert '(mstf-mst g tree)
          :name 'mstf-red-mst-tree)
  (assert '(mstf-edge-in-tree edge tree)
          :name 'mstf-red-edge-in-tree)
  (assert '(implies
            (and (mstf-cycle-list cycle)
                 (mstf-cycle-edge edge cycle)
                 (mstf-cycle-in-graph g cycle)
                 (mstf-heaviest-on-cycle edge cycle compare-certs)
                 (mstf-mst g tree)
                 (mstf-edge-in-tree edge tree))
            (mstf-mst
             (mstf-delete-edge edge g)
             (mstf-exchange
              tree
              edge
              (mstf-cycle-replacement-edge cycle edge))))
          :name 'mstf-red-cycle-exchange-theorem)
  (assert '(implies
            (mstf-mst
             (mstf-delete-edge edge g)
             (mstf-exchange
              tree
              edge
              (mstf-cycle-replacement-edge cycle edge)))
            (mstf-red-rule-out g tree edge (mstf-delete-edge edge g)))
          :name 'mstf-red-rule-program)
  (prove '(mstf-red-rule-out g tree edge ?answer)
         :answer '(values ?answer))
  (new-mst-fol-answer))

(defun new-mst-fol-batch-safety-from-component-cuts ()
  ;; Boruvka batch safety is derived by finitely certifying one blue-rule cut
  ;; for each current component.
  (new-mst-fol-setup)
  (new-mst-fol-declare-language)
  (assert '(mstf-components-of forest components)
          :name 'mstf-batch-components)
  (assert '(mstf-batch-of-component-minima
            g forest components batch)
          :name 'mstf-batch-component-minima)
  (assert '(mstf-batch-edges-have-blue-cuts
            g forest batch batch-certs)
          :name 'mstf-batch-blue-cut-certificates)
  (assert '(implies
            (and (mstf-components-of forest components)
                 (mstf-batch-of-component-minima
                  g forest components batch)
                 (mstf-batch-edges-have-blue-cuts
                  g forest batch batch-certs))
            (mstf-safe-batch g forest batch))
          :name 'mstf-batch-safety-definition)
  (assert '(implies
            (mstf-safe-batch g forest batch)
            (mstf-batch-safety-out
             g forest batch (mstf-add-batch batch forest)))
          :name 'mstf-batch-safety-program)
  (prove '(mstf-batch-safety-out g forest batch ?answer)
         :answer '(values ?answer))
  (new-mst-fol-answer))

(defun new-mst-fol-kruskal-from-blue-rule ()
  ;; Kruskal's globally lightest cross-component edge supplies the finite cut
  ;; and comparison certificates needed by the blue rule.
  (new-mst-fol-setup)
  (new-mst-fol-declare-language)
  (assert '(mstf-components-of forest components)
          :name 'mstf-kruskal-components)
  (assert '(mstf-kruskal-cross-component-minimum
            g forest edge compare-certs)
          :name 'mstf-kruskal-finite-minimum)
  (assert '(implies
            (and (mstf-components-of forest components)
                 (mstf-kruskal-cross-component-minimum
                  g forest edge compare-certs))
            (mstf-lightest-crossing
             g
             edge
             (mstf-component-cut component)))
          :name 'mstf-kruskal-gives-blue-cut)
  (assert '(implies
            (mstf-lightest-crossing
             g
             edge
             (mstf-component-cut component))
            (mstf-blue-rule-out
             g
             forest
             edge
             (mstf-exchange
              tree
              (mstf-crossing-edge path (mstf-component-cut component))
              edge)))
          :name 'mstf-kruskal-imports-blue-rule)
  (assert '(implies
            (mstf-blue-rule-out
             g
             forest
             edge
             (mstf-exchange
              tree
              (mstf-crossing-edge path (mstf-component-cut component))
              edge))
            (mstf-kruskal-out
             g
             forest
             (mstf-kruskal-step g (mstf-add-edge edge forest))))
          :name 'mstf-kruskal-program)
  (prove '(mstf-kruskal-out g forest ?answer)
         :answer '(values ?answer))
  (new-mst-fol-answer))

(defun new-mst-fol-prim-from-blue-rule ()
  ;; Prim/Jarnik's frontier minimum is the lightest edge crossing the current
  ;; root-component cut, so it consumes the same blue-rule theorem.
  (new-mst-fol-setup)
  (new-mst-fol-declare-language)
  (assert '(mstf-component-of forest root component)
          :name 'mstf-prim-root-component)
  (assert '(mstf-prim-frontier-minimum
            g forest root edge compare-certs)
          :name 'mstf-prim-finite-frontier-minimum)
  (assert '(implies
            (and (mstf-component-of forest root component)
                 (mstf-prim-frontier-minimum
                  g forest root edge compare-certs))
            (mstf-lightest-crossing
             g
             edge
             (mstf-component-cut component)))
          :name 'mstf-prim-gives-blue-cut)
  (assert '(implies
            (mstf-lightest-crossing
             g
             edge
             (mstf-component-cut component))
            (mstf-blue-rule-out
             g
             forest
             edge
             (mstf-exchange
              tree
              (mstf-crossing-edge path (mstf-component-cut component))
              edge)))
          :name 'mstf-prim-imports-blue-rule)
  (assert '(implies
            (mstf-blue-rule-out
             g
             forest
             edge
             (mstf-exchange
              tree
              (mstf-crossing-edge path (mstf-component-cut component))
              edge))
            (mstf-prim-out
             g
             forest
             root
             (mstf-prim-step g (mstf-add-edge edge forest) root)))
          :name 'mstf-prim-program)
  (prove '(mstf-prim-out g forest root ?answer)
         :answer '(values ?answer))
  (new-mst-fol-answer))

(defun new-mst-fol-boruvka-from-batch-safety ()
  ;; Boruvka chooses one finite minimum outgoing edge per component.  The
  ;; component cuts derive batch safety; batch safety derives contraction and
  ;; lifting.
  (new-mst-fol-setup)
  (new-mst-fol-declare-language)
  (assert '(mstf-components-of forest components)
          :name 'mstf-boruvka-components)
  (assert '(mstf-boruvka-component-minima
            g forest components batch)
          :name 'mstf-boruvka-component-minima)
  (assert '(implies
            (and (mstf-components-of forest components)
                 (mstf-boruvka-component-minima
                  g forest components batch))
            (mstf-safe-batch g forest batch))
          :name 'mstf-boruvka-minima-are-safe-batch)
  (assert '(implies
            (mstf-safe-batch g forest batch)
            (mstf-boruvka-out
             g
             forest
             (mstf-boruvka-phase g (mstf-contract-set g batch))))
          :name 'mstf-boruvka-program)
  (prove '(mstf-boruvka-out g forest ?answer)
         :answer '(values ?answer))
  (new-mst-fol-answer))

(defun new-mst-fol-synthesis-examples ()
  (list
   (list 'finite-list-membership
         (new-mst-fol-finite-list-membership))
   (list 'input-edge-from-finite-list
         (new-mst-fol-input-edge-from-finite-list))
   (list 'tree-subset-from-finite-lists
         (new-mst-fol-tree-subset-from-finite-lists))
   (list 'path-from-finite-list
         (new-mst-fol-path-from-finite-list))
   (list 'cut-crossing-from-endpoints
         (new-mst-fol-cut-crossing-from-endpoints))
   (list 'component-from-path
         (new-mst-fol-component-from-path))
   (list 'acyclic-from-bridge-cuts
         (new-mst-fol-acyclic-from-bridge-cuts))
   (list 'weight-comparison
         (new-mst-fol-weight-comparison))
   (list 'lightest-crossing-from-finite-comparisons
         (new-mst-fol-lightest-crossing-from-finite-comparisons))
   (list 'spanning-tree-from-certificates
         (new-mst-fol-spanning-tree-from-certificates))
   (list 'exchange-from-path-cut-weight
         (new-mst-fol-exchange-from-path-cut-weight))
   (list 'blue-rule-from-exchange
         (new-mst-fol-blue-rule-from-exchange))
   (list 'red-rule-from-cycle
         (new-mst-fol-red-rule-from-cycle))
   (list 'batch-safety-from-component-cuts
         (new-mst-fol-batch-safety-from-component-cuts))
   (list 'kruskal-from-blue-rule
         (new-mst-fol-kruskal-from-blue-rule))
   (list 'prim-from-blue-rule
         (new-mst-fol-prim-from-blue-rule))
   (list 'boruvka-from-batch-safety
         (new-mst-fol-boruvka-from-batch-safety))))

;;; new-mst-fol-synthesis.lisp EOF
