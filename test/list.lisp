(in-package :geb-test)

(define-test geb-list :parent geb-test-suite)

(define-test cons-car-work
  :parent geb-list
  (is obj-equalp
      (gapply (comp list:*car* list:*cons*)
              (list (right bool:true-obj)
                    (left list:*nil*)))
      (right bool:true-obj)))


(def list-empty-check
  (comp
   (mcase bool:true
          (comp bool:false (terminal list:*cons-type*)))
   list:*cdr*
   list:*cons*))

(define-test cons-cdr-with-nil-gives-nil
  :parent geb-list
  (is obj-equalp
      (gapply list-empty-check
              (list (right bool:true-obj)
                    (left list:*nil*)))
      ;; we check for true!
      (right bool:true-obj)))

(define-test cons-cdr-with-cons-gives-non-empty
  :parent geb-list
  (is obj-equalp
      (gapply list-empty-check
              (list (right bool:true-obj)
                    (right (list (right bool:true-obj)
                                 (left list:*nil*)))))
      ;; we check for false
      (left bool:false-obj)))
