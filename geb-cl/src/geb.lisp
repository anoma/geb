(in-package :geb)

(-> pair-to-list (pair &optional list) list)
(defun pair-to-list (pair &optional acc)
  "converts excess pairs to a list format"
  (if (typep (mcdr pair) 'pair)
      (pair-to-list (mcdr pair)
                    (cons (mcar pair) acc))
      (reverse (list* (mcdr pair) (mcar pair) acc))))

(defun same-type-to-list (pair type &optional acc)
  "converts the given type to a list format"
  (if (typep (mcadr pair) type)
      (same-type-to-list (mcadr pair) type (cons (mcar pair) acc))
      (reverse (list* (mcadr pair) (mcar pair) acc))))

(-> mlist (substmorph &rest substmorph) pair)
(defun mlist (v1 &rest values)
  (if (null values)
      v1
      (mvfoldr #'pair (cons v1 (butlast values)) (car (last values)))))

(def prod16
  (let* ((prod4 (prod (alias bool (prod so0 so1)) (prod so0 so1)))
         (prod8 (prod prod4 prod4)))
    (prod prod8 prod8)))

;; Should this be in a geb.utils: package or does it deserve to be in
;; the main geb package?

(defun commutes (x y)
  (pair (<-right x y) (<-left x y)))

(defun !-> (a b)
  (etypecase-of substobj a
    (so0    so1)
    (so1    b)
    (alias  (!-> (obj a) b))
    (coprod (prod (!-> (mcar a)  b)
                  (!-> (mcadr a) b)))
    (prod   (!-> (mcar a)
                 (!-> (mcadr a) b)))))
