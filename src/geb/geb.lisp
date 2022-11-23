;; General Functions about geb

(in-package :geb)

(-> mlist (substmorph &rest substmorph) pair)
(defun mlist (v1 &rest values)
  (if (null values)
      v1
      (mvfoldr #'pair (cons v1 (butlast values)) (car (last values)))))

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

(defgeneric so-card-alg (obj)
  (:documentation "Gets the cardinality of the given object"))

(defmethod so-card-alg ((obj <substobj>))
  ;; we don't use the cata morphism so here we are. Doesn't give me
  ;; much extra
  (match-of geb:substobj obj
    (geb:alias        (so-card-alg (obj obj)))
    ((geb:prod a b)   (* (so-card-alg a)
                         (so-card-alg b)))
    ((geb:coprod a b) (+ (so-card-alg a)
                         (so-card-alg b)))
    (geb:so0          1)
    (geb:so1          1)))


(-> so-eval (substobj substobj) substmorph)
(defun so-eval (x y)
  (match-of substobj x
    (alias        (so-eval (obj x) y))
    (so0          (comp (init y) (<-right so1 so0)))
    (so1          (<-left y so1))
    ((coprod a b) (comp (mcase (comp (so-eval a y)
                                     (so-forget-middle (!-> a y) (!-> b y) a))
                               (comp (so-eval b y)
                                     (so-forget-first (!-> a y) (!-> b y) b)))
                        (distribute (prod (!-> a y) (!-> b y)) a b)))
    ((prod a b)   (let ((eyz   (so-eval b y))
                        (exhyz (so-eval a (so-hom-obj b y)))
                        (hom   (!-> a (so-hom-obj b y))))
                    (comp eyz
                          (pair (comp exhyz (so-forget-right hom a b))
                                (comp (<-right a b)
                                      (<-right hom (prod a b)))))))))

(defun so-hom-obj (x z)
  (match-of substobj x
    (so0          so1)
    (so1          z)
    (alias        (so-hom-obj (obj x) z))
    ((coprod x y) (prod (so-hom-obj x z)
                        (so-hom-obj y z)))
    ((prod x y)   (so-hom-obj x (so-hom-obj y z)))))

(-> so-forget-right (substobj substobj substobj) substmorph)
(defun so-forget-right (x y z)
  (pair (<-left x (prod y z))
        (comp (<-left y z)
              (<-right x (prod y z)))))

(-> so-forget-middle (substobj substobj substobj) substmorph)
(defun so-forget-middle (x y z)
  (pair (comp (<-left x y) (<-left (prod x y) z))
        (<-right (prod x y) z)))
(-> so-forget-first (substobj substobj substobj) substmorph)

(defun so-forget-first (x y z)
  (pair (comp (<-right x y) (<-left (prod x y) z))
        (<-right (prod x y) z)))
