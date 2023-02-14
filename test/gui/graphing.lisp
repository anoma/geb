(in-package :geb-test)

(define-test geb-gui-graphing :parent geb-gui)


(define-test goals-work :parent geb-gui-graphing
  (let (;; don't want to clutter the allocation globally, so we don't
        ;; define it globally.
        (node-merge-1
          (geb-gui.graphing:graphize
           geb-bool:bool
           (list (geb-gui.graphing:make-note
                  :value (geb-gui.graphing:graphize geb-bool:bool nil nil)
                  :from geb-bool:bool
                  :note "π₁")
                 (geb-gui.graphing:make-note
                  :value (geb-gui.graphing:graphize geb-bool:bool nil nil)
                  :from geb-bool:bool
                  :note "π₂"
                  :merge-p t))
           nil))
        (node-merge-all
          (geb-gui.graphing:graphize
           geb-bool:bool
           (list (geb-gui.graphing:make-note
                  :value (geb-gui.graphing:graphize geb-bool:bool nil nil)
                  :from geb-bool:bool
                  :note "π₂"
                  :merge-p t)
                 (geb-gui.graphing:make-note
                  :value (geb-gui.graphing:graphize geb-bool:bool nil nil)
                  :from geb-bool:bool
                  :note "π₂"
                  :merge-p t))
           nil))
        (population
          (hash-table-count (geb.mixins::meta (make-instance 'geb-gui.graphing:node))))
        (node
          (geb-gui.graphing:graphize
           geb-bool:bool
           (list (geb-gui.graphing:make-note
                  :value (geb-gui.graphing:graphize geb-bool:bool nil nil)
                  :from geb-bool:bool
                  :note "π₁")
                 (geb-gui.graphing:make-note
                  :value (geb-gui.graphing:graphize geb-bool:bool nil nil)
                  :from geb-bool:bool
                  :note "π₂"))
           nil)))
    (is =
        (+ 2 population)
        (hash-table-count (geb.mixins::meta node))
        "By inserting these nodes we should have increased the
         hashtable by two slots")

    (is equalp
        (~> node-merge-1
            geb-gui.graphing::children
            car geb-gui.graphing::children)
        nil
        "Merging should remove the extra indirection")

    (is equalp
        (~> node-merge-all geb-gui.graphing::children)
        nil
        "All should be merged into one")))

(define-test stack-works :parent geb-gui-graphing
  (let* ((term (comp (<-left so1 so1) (init geb-bool:bool)))
         (node
           (geb-gui.graphing:graphize term nil nil)))
    (is obj-equalp (dom term) (geb-gui.graphing::value node)
        "We should be displaying the dom of the first term")
    (is obj-equalp
        (~> node geb-gui.graphing::children car geb-gui.graphing::children car
            geb-gui.graphing::representation)
        so1
        "The stack should work and remove the redundant 1 + 1")))
