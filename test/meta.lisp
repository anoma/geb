(in-package :geb-test)

(define-test geb-meta :parent geb-test-suite)

(defclass mixin-test (meta-mixin) ())

(define-test insert-works :parent geb-meta
  (let ((obj (make-instance 'mixin-test)))
    (meta-insert obj :a 2)
    (is = (meta-lookup obj :a) 2)))

(define-test weak-pointers-work :parent geb-meta
  (tg:gc :full t)
  (let ((count (hash-table-count
                (geb.mixins::meta (make-instance 'mixin-test)))))
    ;; creates some garbage
    (meta-insert (make-instance 'mixin-test) :a 2)
    ;; collect it
    (tg:gc :full t)
    ;; did it work?
    (is =
        (hash-table-count (geb.mixins::meta (make-instance 'mixin-test)))
        count)))
