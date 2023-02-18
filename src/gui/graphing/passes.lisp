(in-package :geb-gui.graphing.passes)

(-> passes (node) node)
(defun passes (node)
  "Runs all the passes that simplify viewing the graph.
These simplifications should not change the semantics of the graph,
only display it in a more bearable way"
  (~> node
      fold-right-case-dists
      fold-right-cases))

(-> fold-right-cases (node) (values node &optional))
(defun fold-right-cases (node)
  (when (typep (representation node) 'case)
    (setf (children node) (linearize-right-case node))
    (notorize-children-with-index-schema "χ" node))
  (recurse node #'fold-right-cases))

(-> fold-right-case-dists (node) (values node &optional))
(defun fold-right-case-dists (node)
  (when (linear-distp node)
    (setf (children node) (linearize-right-dist-case node))
    (notorize-children-with-index-schema "δχ" node))
  (recurse node #'fold-right-case-dists))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pass helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-> recruse (node (-> (node) t)) node)
(defun recurse (node func)
  "Recuses on the child of the node given the pass function"
  (setf (children node)
        (mapcar func (children node)))
  node)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Linearize Helpers
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(-> linearize-right-case (node) list)
(defun linearize-right-case (node)
  "Lineraizes out all the right cases into a proper node list"
  (if (typep (representation node) 'case)
      (let ((children (children node)))
        (append (butlast children)
                (linearize-right-case (car (last children)))))
      (list node)))

(-> linear-distp (node) boolean)
(defun linear-distp (node)
  (let ((child (car (children node))))
    (and (typep (representation node)  'distribute)
         (typep (representation child) 'case)
         (= 1 (length (children node))))))

(-> linearize-right-dist-case (node) list)
(defun linearize-right-dist-case (node)
  (let ((grand-kids (children (car (children node)))))
    (if (linear-distp node)
        (append (butlast grand-kids)
                (linearize-right-dist-case (car (last grand-kids))))
        (list node))))
