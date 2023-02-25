(in-package :geb-test)

(define-test geb-gui-graphing :parent geb-gui)


(define-test notes-work :parent geb-gui-graphing
  (let (;; don't want to clutter the allocation globally, so we don't
        ;; define it globally.
        (node-merge-1
          (graphize
           geb-bool:bool
           (cons-note (make-squash
                       :value (graphize geb-bool:bool nil))
                      (cons-note (make-note
                                  :value (graphize geb-bool:bool nil)
                                  :from geb-bool:bool
                                  :note "π₂")
                                 nil))))
        (node-merge-all
          (graphize
           geb-bool:bool
           (cons-note (make-squash
                       :value (graphize geb-bool:bool nil))
                      (cons-note (make-squash
                                  :value (graphize geb-bool:bool nil))
                                 nil))))
        (population
          (hash-table-count (geb.mixins::meta (make-instance 'node))))
        (node
          (graphize
           geb-bool:bool
           (cons-note (make-note
                       :value (graphize geb-bool:bool nil)
                       :from geb-bool:bool
                       :note "π₂")
                      (cons-note (make-note
                                  :value (graphize geb-bool:bool nil)
                                  :from geb-bool:bool
                                  :note "π₂")
                       nil)))))
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

(define-test composition-works :parent geb-gui-graphing
  (let* ((term (comp (<-left so1 so1) (init geb-bool:bool)))
         (node
           (graphize term nil)))
    (is obj-equalp (dom term) (geb-gui.graphing::value node)
        "We should be displaying the dom of the first term")
    (is obj-equalp
        (~> node geb-gui.graphing::children car
            geb-gui.graphing::children car
            geb-gui.graphing::representation)
        so1
        "The stack should work and remove the redundant 1 + 1")))

(define-test composition-with-notes-behaves :parent geb-gui-graphing
  (let* ((term (comp (<-left so1 so1) (init geb-bool:bool)))
         (node-merge-all
           (graphize
            term
            (cons-note (make-squash :value (graphize geb-bool:bool nil))
                       (cons-note (make-note
                                   :value (graphize geb-bool:bool nil)
                                   :from geb-bool:bool
                                   :note "π₂")
                                  nil)))))
    (is equalp
        (~> node-merge-all
            ;; so0
            geb-gui.graphing::children car
            ;; bool
            geb-gui.graphing::children car
            ;; so1
            geb-gui.graphing::children car
            ;; nil
            geb-gui.graphing::children)
        nil
        "The nodes should collapse")))
