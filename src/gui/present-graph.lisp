(in-package :geb-gui)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Main graphing entry points
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun graph-dot (object pane)
  "Graphing using dot"
  (format-graph-from-roots
   (list object) #'present-object #'graph::children
   :stream      pane
   :arc-drawer  (dot-arc-drawer)
   :graph-type  :dot-digraph
   :orientation :vertical
   :center-nodes          t
   :merge-duplicates      t
   :maximize-generations  t
   :generation-separation 50
   :within-generation-separation 20))

(defun graph-node (object pane)
  "Graphing using the normal digraph"
  (format-graph-from-roots
   (list object) #'present-object #'graph::children
   :stream pane
   :maximize-generations t
   :center-nodes t
   :merge-duplicates t
   :generation-separation 50
   :within-generation-separation 20
   :arc-drawer #'digraph-arc-drawer
   :graph-type :digraph
   :arc-drawing-options (list :line-thickness 1.4 :head-width 5)))

(defun stick-graph (object pane)
  (format-graph-from-roots
   (list object)
   #'present-object
   #'visual-children
   :stream pane
   :maximize-generations t
   :center-nodes t
   ;; :orientation :vertical
   :generation-separation 20
   :within-generation-separation 20
   :arc-drawing-options (list :line-thickness 1.4 :head-width 5)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Arc Drawers for the graphs
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defun dot-arc-drawer ()
  (make-instance
   'mcclim-dot:dot-arc-drawer
   :edge-label-printer
   (lambda (drawer stream from to)
     (declare (ignore drawer))
     (let ((obj (graph:determine-text-and-object-from-node from to)))
       (with-output-as-presentation (stream (cadr obj) (type-of (cadr obj)))
         (format stream (car obj)))))))

(defun digraph-arc-drawer (pane from-node to-node x1 y1 x2 y2
                           &rest drawing-options
                           &key &allow-other-keys)
  (with-drawing-options (pane
                         :transform (clim:make-rotation-transformation
                                     (atan (- y2 y1) (- x2 x1)))
                         :text-style (make-text-style nil nil 12))
    (apply #'draw-arrow* pane x1 y1 x2 y2 drawing-options)
    (let ((obj (graph:determine-text-and-object-from-node
                (clim:graph-node-object from-node)
                (clim:graph-node-object to-node))))
      (with-output-as-presentation (pane (cadr obj) (type-of (cadr obj)))
        (draw-text* pane (car obj)
                    (/ (+ x1 x2) 2)
                    (/ (+ y1 y2) 2)
                    :toward-y (* 2 y2)
                    :toward-x (* 2 x2)
                    :align-y :top
                    :align-y :bottom
                    :align-x :center
                    :transform-glyphs t)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Children API
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgeneric visual-children (obj)
  (:documentation "The visual-children of the given node"))

(defmethod visual-children ((obj geb.mixins:pointwise-mixin))
  (mapcar #'cdr (geb.mixins:to-pointwise-list obj)))

;; we want to visualize it in the presentation not in the graph
(defmethod visual-children ((obj geb:prod))
  (geb:same-type-to-list obj 'geb:prod))

(defmethod visual-children ((obj t))
  nil)
