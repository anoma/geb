(in-package :geb-decision)

(def yes   (alias yes   (so1)) "The [YES] term")
(def no    (alias no    (so1)) "The [NO] term")
(def maybe (alias maybe (so1)) "The [MAYBE] term")

(def inj-maybe
  (alias inj-maybe (comp
                    (->right yes (coprod no maybe))
                    (->right no maybe)))
  "Injects [MAYBE] from [SO1]")
(def inj-no
  (alias inj-no (comp
                 (->right yes (coprod no maybe))
                 (->left no maybe)))
  "Injects [NO] from [SO1]")

(def inj-yes (alias inj-yes (->left yes (coprod no maybe)))
  "Injects [YES] from [SO1]")

(def decision
  (alias decision (coprod yes (coprod no maybe)))
  "The [DECISION] type")


;; for now
(defun distrib (obj1 obj2)
  (distribute obj1 (mcar obj2) (mcadr obj2)))

;; implement mega-case instead of working with mcase
;; (defun mega-case ())

;; make mega-distribute as well, it's a pain

(def demote
  (alias demote
         (mcase (const inj-maybe yes)
                (const inj-no    (coprod no maybe))))
  "Demotes a decision. Thus if the decision was [YES], now it's now
[MAYBE], if it was [MAYBE] it is now [NO]")

(def promote
  (alias promote
         (mcase inj-yes
                (mcase (const inj-maybe no)
                       (const inj-yes maybe))))
  "The inverse of demote. Promotes a decision so if the decision was
[NO] it is now [MAYBE], and if it was [MAYBE] it is now [YES]")

(def merge-opinion
  (alias merge-opinion
         (comp
          (mcase (comp promote
                       (<-left decision yes))
                 ;; no + maybe
                 (comp
                  (mcase (comp demote
                               (<-left decision no))
                         (<-left decision maybe))
                  (distribute decision no maybe)))
          (distrib decision decision)))
  "merges two [DECISION]S. Taking the average of the decisions.")
