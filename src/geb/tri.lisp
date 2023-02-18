(in-package :geb-tri)


(def yes   (alias yes   (so1)))
(def no    (alias no    (so1)))
(def maybe (alias maybe (so1)))

(def inj-maybe (alias inj-maybe (comp
                                 (->right yes (coprod no maybe))
                                 (->right no maybe))))
(def inj-no (alias inj-no (comp
                              (->right yes (coprod no maybe))
                              (->left no maybe))))

(def inj-yes (alias inj-yes (->left yes (coprod no maybe))))

(def decision
  (alias decision (coprod yes (coprod no maybe))))


;; for now
(defun distrib (obj1 obj2)
  (distribute obj1 (mcar obj2) (mcadr obj2)))

;; implement mega-case instead of working with mcase
;; (defun mega-case ())

;; make mega-distribute as well, it's a pain

(def demote
  (alias demote
         (mcase (const inj-maybe yes)
                (const inj-no    (coprod no maybe)))))

(def promote
  (alias promote
         (mcase inj-yes
                (mcase (const inj-maybe no)
                       (const inj-yes maybe)))))

(def merge-opinion
  (alias merge-opinion
         (comp
          (mcase (comp
                  (mcase inj-yes
                         (mcase (const inj-maybe no)
                                       (const inj-yes maybe)))
                  (<-left decision yes))
                 ;; no + maybe
                 (comp
                  (mcase (comp
                          (mcase (const inj-maybe yes)
                                 (const inj-no    (coprod no maybe)))
                          (<-left decision no))
                         (<-left decision maybe))
                  (distribute decision no maybe)))
          (distrib decision decision))))
