;; General Functions about geb

(in-package :geb)

(-> const (<substmorph> <substobj>) (or alias comp))
(defun const (f x)
  "The constant morphism.

Takes a morphism from [SO1][type] to a desired value of type $B$,
along with a [\\<SUBSTOBJ\\>] that represents the input type say of
type $A$, giving us a morphism from $A$ to $B$.

Thus if:
F : [SO1][type] → a,
X : b

then: (const f x) : a → b

```
Γ, f : so1 → b, x : a
----------------------
(const f x) : a → b
```

Further, If the input `F` is an [ALIAS][type], then we wrap the output
in a new alias to denote it's a constant version of that value.


Example:

```lisp
(const true bool) ; bool -> bool
```"
  (if (typep f 'alias)
      (make-alias :name (intern (format nil "CONST-~A" (name f))) :obj (obj f))
      (comp f (terminal x))))

(-> cleave (substmorph &rest substmorph) pair)
(defun cleave (v1 &rest values)
  "Applies each morphism to the object in turn."
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

(defgeneric dom (substmorph)
  (:documentation "Grabs the domain of the morphism"))

(defgeneric codom (substmorph)
  (:documentation "Grabs the codomain of the morphism"))

(defmethod dom ((x <substmorph>))
  (if (not (typep x 'substmorph))
      (subclass-responsibility x)
      (match-of substmorph x
        ((alias _ x)         (dom x))
        (substobj            x)
        ((terminal x)        x)
        ((inject-left x _)   x)
        ((inject-right _ x)  x)
        ((init _)            so0)
        ((comp _ x)          (dom x))
        ((case x y)          (coprod (dom x) (dom y)))
        ((pair x _)          (dom x))
        ((distribute x y z)  (prod x (coprod y z)))
        ((project-left x y)  (prod x y))
        ((project-right x y) (prod x y)))))

(defmethod codom ((x <substmorph>))
  (if (not (typep x 'substmorph))
      (subclass-responsibility x)
      (match-of substmorph x
        ((alias _ x)         (codom x))
        ((terminal _)        so1)
        ((init x)            x)
        (substobj            x)
        ((project-left x _)  x)
        ((project-right _ x) x)
        ((comp x _)          (codom x))
        ((case x _)          (codom x))
        ((pair x y)          (prod (codom x) (codom y)))
        ((distribute x y z)  (coprod (prod x y) (prod x z)))
        ((inject-left x y)   (coprod x y))
        ((inject-right x y)  (coprod x y)))))
