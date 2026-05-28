;;; -*- Mode: Lisp; Syntax: Common-Lisp; Package: snark-user -*-
;;; File: examples/synthesis/new-mst-synthesis.lisp
;;;
;;; Hierarchical MST synthesis/refinement examples for SNARK.
;;;
;;; This file treats the minimum-spanning-tree problem as a chain of logical
;;; refinements rather than as one preselected algorithm.  Sets, cuts, forests,
;;; batches, and strategies are first-order objects in the SNARK layer.  The
;;; executable layer interprets the extracted refinement shapes over finite
;;; Common Lisp graphs and supplies Kruskal, Prim/Jarnik, and Boruvka runners.

(in-package :snark-user)

(defun new-mst-synthesis-setup ()
  (initialize)
  (use-resolution t)
  (use-conditional-answer-creation t)
  (print-options-when-starting nil)
  (print-rows-when-given nil)
  (print-rows-when-derived nil)
  (print-final-rows nil)
  (print-summary-when-finished nil)
  (print-clocks-when-finished nil))

(defun new-mst-synthesis-answer ()
  (answer t))

(defun new-mst-declare-language ()
  (dolist (name '(g tree forest edge cut batch strategy root component))
    (declare-constant name))
  (dolist (entry '((new-mst-greedy 2)
                   (new-mst-extend 2)
                   (new-mst-add-edge 2)
                   (new-mst-add-batch 2)
                   (new-mst-kruskal-step 2)
                   (new-mst-prim-step 3)
                   (new-mst-boruvka-step 2)))
    (apply #'declare-function entry))
  (dolist (entry '((new-spanning-tree 2)
                   (new-minimum-total-weight 2)
                   (new-mst-out 3)
                   (new-mst-complete 2)
                   (new-safe-edge 3)
                   (new-safe-batch 3)
                   (new-mst-greedy-out 3)
                   (new-mst-extension-out 3)
                   (new-cut-respected 3)
                   (new-crosses-cut 2)
                   (new-lightest-crossing 3)
                   (new-kruskal-eligible 3)
                   (new-kruskal-lightest 3)
                   (new-prim-frontier 4)
                   (new-prim-lightest 4)
                   (new-boruvka-lightest-batch 3)
                   (new-strategy-kruskal 1)
                   (new-strategy-prim 1)
                   (new-strategy-boruvka 1)
                   (new-mst-strategy-out 4)))
    (apply #'declare-relation entry)))

(defun new-mst-abstract-specification ()
  ;; Abstract relational postcondition:
  ;;
  ;;   MST(G,T) := SpanningTree(G,T) and MinimumTotalWeight(G,T).
  ;;
  ;; The extracted answer is T itself.  This is the top of the refinement
  ;; ladder: it states the witness relation without choosing an algorithm.
  (new-mst-synthesis-setup)
  (new-mst-declare-language)
  (assert '(new-spanning-tree g tree)
          :name 'new-mst-spanning-tree-premise)
  (assert '(new-minimum-total-weight g tree)
          :name 'new-mst-minimality-premise)
  (assert '(implies
            (and (new-spanning-tree g tree)
                 (new-minimum-total-weight g tree))
            (new-mst-out g tree tree))
          :name 'new-mst-specification)
  (prove '(new-mst-out g tree ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-abstract-greedy-refinement ()
  ;; A generic greedy MST skeleton:
  ;;
  ;;   if the current forest spans, return it;
  ;;   otherwise apply an abstract safe extension and continue.
  (new-mst-synthesis-setup)
  (new-mst-declare-language)
  (assert '(implies
            (new-mst-complete g forest)
            (new-mst-greedy-out g forest forest))
          :name 'new-mst-greedy-finished)
  (assert '(implies
            (not (new-mst-complete g forest))
            (new-mst-greedy-out
             g
             forest
             (new-mst-greedy g (new-mst-extend g forest))))
          :name 'new-mst-greedy-continues)
  (prove '(new-mst-greedy-out g forest ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-safe-extension-refinement ()
  ;; Refine the abstract extension point.  A safe Boruvka-style batch can be
  ;; added in one step; otherwise a single safe edge is added.
  (new-mst-synthesis-setup)
  (new-mst-declare-language)
  (assert '(or (new-safe-batch g forest batch)
               (new-safe-edge g forest edge))
          :name 'new-mst-extension-kind)
  (assert '(implies
            (new-safe-batch g forest batch)
            (new-mst-extension-out
             g
             forest
             (new-mst-add-batch batch forest)))
          :name 'new-mst-safe-batch-extension)
  (assert '(implies
            (and (not (new-safe-batch g forest batch))
                 (new-safe-edge g forest edge))
            (new-mst-extension-out
             g
             forest
             (new-mst-add-edge edge forest)))
          :name 'new-mst-safe-edge-extension)
  (prove '(new-mst-extension-out g forest ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-cut-property-refinement ()
  ;; The cut property: a lightest input edge crossing a cut respected by the
  ;; current forest is safe to add.
  (new-mst-synthesis-setup)
  (new-mst-declare-language)
  (assert '(new-cut-respected g forest cut)
          :name 'new-mst-cut-respected-premise)
  (assert '(new-crosses-cut edge cut)
          :name 'new-mst-cut-crossing-premise)
  (assert '(new-lightest-crossing g edge cut)
          :name 'new-mst-cut-lightest-premise)
  (assert '(implies
            (and (new-cut-respected g forest cut)
                 (new-crosses-cut edge cut)
                 (new-lightest-crossing g edge cut))
            (new-mst-extension-out
             g
             forest
             (new-mst-add-edge edge forest)))
          :name 'new-mst-cut-property-extension)
  (prove '(new-mst-extension-out g forest ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-kruskal-refinement ()
  ;; Kruskal specialization: choose a globally lightest edge that connects two
  ;; different forest components.
  (new-mst-synthesis-setup)
  (new-mst-declare-language)
  (assert '(new-kruskal-eligible g forest edge)
          :name 'new-mst-kruskal-eligible-premise)
  (assert '(new-kruskal-lightest g forest edge)
          :name 'new-mst-kruskal-lightest-premise)
  (assert '(implies
            (and (new-kruskal-eligible g forest edge)
                 (new-kruskal-lightest g forest edge))
            (new-mst-extension-out
             g
             forest
             (new-mst-add-edge edge forest)))
          :name 'new-mst-kruskal-extension)
  (prove '(new-mst-extension-out g forest ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-prim-refinement ()
  ;; Jarnik/Prim specialization: maintain one growing component and add a
  ;; lightest frontier edge from that component.
  (new-mst-synthesis-setup)
  (new-mst-declare-language)
  (assert '(new-prim-frontier g forest root edge)
          :name 'new-mst-prim-frontier-premise)
  (assert '(new-prim-lightest g forest root edge)
          :name 'new-mst-prim-lightest-premise)
  (assert '(implies
            (and (new-prim-frontier g forest root edge)
                 (new-prim-lightest g forest root edge))
            (new-mst-extension-out
             g
             forest
             (new-mst-add-edge edge forest)))
          :name 'new-mst-prim-extension)
  (prove '(new-mst-extension-out g forest ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-boruvka-refinement ()
  ;; Boruvka specialization: add the batch of lightest outgoing edges, one for
  ;; each current component.
  (new-mst-synthesis-setup)
  (new-mst-declare-language)
  (assert '(new-boruvka-lightest-batch g forest batch)
          :name 'new-mst-boruvka-batch-premise)
  (assert '(implies
            (new-boruvka-lightest-batch g forest batch)
            (new-mst-extension-out
             g
             forest
             (new-mst-add-batch batch forest)))
          :name 'new-mst-boruvka-extension)
  (prove '(new-mst-extension-out g forest ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-strategy-dispatch-refinement ()
  ;; A final dispatcher shows the concrete algorithms as refinements of the
  ;; same abstract extension point.
  (new-mst-synthesis-setup)
  (new-mst-declare-language)
  (assert '(or (new-strategy-kruskal strategy)
               (new-strategy-prim strategy)
               (new-strategy-boruvka strategy))
          :name 'new-mst-strategy-cases)
  (assert '(not (and (new-strategy-kruskal strategy)
                     (new-strategy-prim strategy)))
          :name 'new-mst-not-both-kruskal-prim)
  (assert '(not (and (new-strategy-kruskal strategy)
                     (new-strategy-boruvka strategy)))
          :name 'new-mst-not-both-kruskal-boruvka)
  (assert '(not (and (new-strategy-prim strategy)
                     (new-strategy-boruvka strategy)))
          :name 'new-mst-not-both-prim-boruvka)
  (assert '(implies
            (new-strategy-kruskal strategy)
            (new-mst-strategy-out
             g forest strategy (new-mst-kruskal-step g forest)))
          :name 'new-mst-dispatch-kruskal)
  (assert '(implies
            (and (not (new-strategy-kruskal strategy))
                 (new-strategy-prim strategy))
            (new-mst-strategy-out
             g forest strategy (new-mst-prim-step g forest root)))
          :name 'new-mst-dispatch-prim)
  (assert '(implies
            (and (not (new-strategy-kruskal strategy))
                 (not (new-strategy-prim strategy))
                 (new-strategy-boruvka strategy))
            (new-mst-strategy-out
             g forest strategy (new-mst-boruvka-step g forest)))
          :name 'new-mst-dispatch-boruvka)
  (prove '(new-mst-strategy-out g forest strategy ?answer)
         :answer '(values ?answer))
  (new-mst-synthesis-answer))

(defun new-mst-synthesis-examples ()
  (list
   (list 'abstract-specification
         (new-mst-abstract-specification))
   (list 'abstract-greedy-refinement
         (new-mst-abstract-greedy-refinement))
   (list 'safe-extension-refinement
         (new-mst-safe-extension-refinement))
   (list 'cut-property-refinement
         (new-mst-cut-property-refinement))
   (list 'kruskal-refinement
         (new-mst-kruskal-refinement))
   (list 'prim-refinement
         (new-mst-prim-refinement))
   (list 'boruvka-refinement
         (new-mst-boruvka-refinement))
   (list 'strategy-dispatch-refinement
         (new-mst-strategy-dispatch-refinement))))

;;; Concrete finite-graph interpretations of the refinement leaves.

(defun new-run-mst-edge-id (edge)
  (first edge))

(defun new-run-mst-edge-u (edge)
  (second edge))

(defun new-run-mst-edge-v (edge)
  (third edge))

(defun new-run-mst-edge-weight (edge)
  (fourth edge))

(defun new-run-mst-vertices (graph)
  (getf graph :vertices))

(defun new-run-mst-edges (graph)
  (getf graph :edges))

(defun new-run-mst-total-weight (edges)
  (reduce #'+ edges :key #'new-run-mst-edge-weight :initial-value 0))

(defun new-run-mst-sorted-edges (graph)
  (sort (copy-list (new-run-mst-edges graph))
        #'<
        :key #'new-run-mst-edge-weight))

(defun new-run-mst-make-parent (vertices)
  (mapcar (lambda (vertex) (cons vertex vertex)) vertices))

(defun new-run-mst-find (parent vertex)
  (let ((entry (assoc vertex parent :test #'equal)))
    (if (or (null entry) (equal vertex (cdr entry)))
        vertex
        (new-run-mst-find parent (cdr entry)))))

(defun new-run-mst-union (parent u v)
  (let ((ru (new-run-mst-find parent u))
        (rv (new-run-mst-find parent v)))
    (unless (equal ru rv)
      (let ((entry (assoc rv parent :test #'equal)))
        (when entry
          (setf (cdr entry) ru)))))
  parent)

(defun new-run-mst-crosses-components-p (parent edge)
  (not (equal (new-run-mst-find parent (new-run-mst-edge-u edge))
              (new-run-mst-find parent (new-run-mst-edge-v edge)))))

(defun new-run-mst-kruskal (graph)
  (let ((parent (new-run-mst-make-parent (new-run-mst-vertices graph)))
        (tree nil))
    (dolist (edge (new-run-mst-sorted-edges graph))
      (when (new-run-mst-crosses-components-p parent edge)
        (push edge tree)
        (new-run-mst-union parent
                           (new-run-mst-edge-u edge)
                           (new-run-mst-edge-v edge))))
    (nreverse tree)))

(defun new-run-mst-frontier-edges (graph visited)
  (remove-if-not
   (lambda (edge)
     (let ((u-seen (member (new-run-mst-edge-u edge) visited :test #'equal))
           (v-seen (member (new-run-mst-edge-v edge) visited :test #'equal)))
       (or (and u-seen (not v-seen))
           (and v-seen (not u-seen)))))
   (new-run-mst-edges graph)))

(defun new-run-mst-other-end (edge vertex)
  (if (equal vertex (new-run-mst-edge-u edge))
      (new-run-mst-edge-v edge)
      (new-run-mst-edge-u edge)))

(defun new-run-mst-prim (graph)
  (let ((visited nil)
        (tree nil))
    (dolist (start (new-run-mst-vertices graph))
      (unless (member start visited :test #'equal)
        (push start visited)
        (loop
          for frontier = (new-run-mst-frontier-edges graph visited)
          while frontier
          for edge = (first (sort (copy-list frontier)
                                  #'<
                                  :key #'new-run-mst-edge-weight))
          for u = (new-run-mst-edge-u edge)
          for v = (new-run-mst-edge-v edge)
          for next = (if (member u visited :test #'equal) v u)
          do (push edge tree)
             (pushnew next visited :test #'equal))))
    (nreverse tree)))

(defun new-run-mst-component-representatives (parent vertices)
  (remove-duplicates
   (mapcar (lambda (vertex) (new-run-mst-find parent vertex)) vertices)
   :test #'equal))

(defun new-run-mst-boruvka-cheapest (graph parent)
  (let ((choices nil))
    (dolist (edge (new-run-mst-edges graph))
      (let ((ru (new-run-mst-find parent (new-run-mst-edge-u edge)))
            (rv (new-run-mst-find parent (new-run-mst-edge-v edge))))
        (unless (equal ru rv)
          (dolist (rep (list ru rv))
            (let ((entry (assoc rep choices :test #'equal)))
              (cond
               ((null entry)
                (push (cons rep edge) choices))
               ((< (new-run-mst-edge-weight edge)
                   (new-run-mst-edge-weight (cdr entry)))
                (setf (cdr entry) edge))))))))
    (remove-duplicates (mapcar #'cdr choices)
                       :key #'new-run-mst-edge-id
                       :test #'equal)))

(defun new-run-mst-boruvka (graph)
  (let ((parent (new-run-mst-make-parent (new-run-mst-vertices graph)))
        (tree nil)
        (changed t))
    (loop
      while changed
      do (setf changed nil)
         (dolist (edge (new-run-mst-boruvka-cheapest graph parent))
           (when (new-run-mst-crosses-components-p parent edge)
             (push edge tree)
             (new-run-mst-union parent
                                (new-run-mst-edge-u edge)
                                (new-run-mst-edge-v edge))
             (setf changed t))))
    (nreverse tree)))

(defun new-run-mst (graph &key (strategy :kruskal))
  (ecase strategy
    (:kruskal (new-run-mst-kruskal graph))
    (:prim (new-run-mst-prim graph))
    (:boruvka (new-run-mst-boruvka graph))))

(defun new-run-mst-edge-ids (edges)
  (mapcar #'new-run-mst-edge-id edges))

(defun new-run-mst-demo-graph ()
  '(:vertices (a b c d e f)
    :edges ((ab a b 4)
            (ac a c 3)
            (bc b c 1)
            (bd b d 2)
            (cd c d 4)
            (ce c e 5)
            (de d e 1)
            (df d f 6)
            (ef e f 2))))

(defun new-run-mst-demo ()
  (let* ((graph (new-run-mst-demo-graph))
         (kruskal (new-run-mst graph :strategy :kruskal))
         (prim (new-run-mst graph :strategy :prim))
         (boruvka (new-run-mst graph :strategy :boruvka))
         (weights (list (new-run-mst-total-weight kruskal)
                        (new-run-mst-total-weight prim)
                        (new-run-mst-total-weight boruvka))))
    (list
     :kruskal (list :edges (new-run-mst-edge-ids kruskal)
                    :weight (new-run-mst-total-weight kruskal))
     :prim (list :edges (new-run-mst-edge-ids prim)
                 :weight (new-run-mst-total-weight prim))
     :boruvka (list :edges (new-run-mst-edge-ids boruvka)
                    :weight (new-run-mst-total-weight boruvka))
     :weights-agree (apply #'= weights))))

;;; new-mst-synthesis.lisp EOF
