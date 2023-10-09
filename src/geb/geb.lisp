;; General Functions about geb

(in-package :geb.main)

(defmethod curry-prod (fun fst (snd <substobj>))
  (match-of substobj snd
    (so0          (terminal fst))
    (so1          (comp fun (pair fst
                                  (terminal fst))))
    ((coprod x y) (pair (curry (left-morph  (comp fun (gather fst x y))))
                        (curry (right-morph (comp fun (gather fst x y))))))
    (prod         (curry (curry (prod-left-assoc fun))))))

(defmethod curry-prod (fun fst (snd <natobj>))
  (let ((num (num snd)))
    (if (= num 1)
        (pair
         ;; On the left, see what the morphism does at 0
         (curry (comp fun
                      (prod-mor fst
                                (nat-const 1 0))))
         ;; On the left, see what the morphism does at 0
         (curry (comp fun
                      (prod-mor fst
                                (nat-const 1 1)))))
        (curry (comp fun
                     (prod-mor fst
                               (nat-concat 1 (1- num))))))))

(defmethod dom ((x <substmorph>))
  (assure cat-obj
    (typecase-of substmorph x
      (init         so0)
      (terminal     (obj x))
      (substobj     x)
      (inject-left  (mcar x))
      (inject-right (mcadr x))
      (comp         (dom (mcadr x)))
      (pair         (dom (mcar x)))
      (distribute   (prod (mcar x) (coprod (mcadr x) (mcaddr x))))
      (case         (coprod (dom (mcar x)) (dom (mcadr x))))
      ((or project-right
           project-left)
       (prod (mcar x) (mcadr x)))
      (otherwise
       (subclass-responsibility x)))))

(defmethod dom ((x <natmorph>))
  (cond ((typep x 'nat-concat)      (prod (nat-width (num-left x))
                                          (nat-width (num-right x))))
        ((typep x 'nat-const)       so1)
        ((typep x 'nat-inj)         (nat-width (num x)))
        ((typep x 'one-bit-to-bool) (nat-width 1))
        ((typep x 'nat-decompose)   (nat-width (num x)))
        (t                          (let ((bit (nat-width (num x))))
                                     (prod bit bit)))))

(defmethod dom ((x <natobj>))
  x)

(defmethod dom ((ref reference))
  ref)

(defmethod codom ((ref reference))
  ref)

(defmethod codom ((x <substmorph>))
  (assure cat-obj
    (typecase-of substmorph x
      (terminal      so1)
      (init          (obj x))
      (substobj      x)
      (project-left  (mcar x))
      (project-right (mcadr x))
      (comp          (codom (mcar x)))
      (case          (codom (mcar x)))
      (pair          (prod (codom (mcar x))
                           (codom (mcdr x))))
      (distribute    (coprod (prod (mcar x) (mcadr x))
                             (prod (mcar x) (mcaddr x))))
      ((or inject-left
           inject-right)
       (coprod (mcar x) (mcadr x)))
      (otherwise
       (subclass-responsibility x)))))

(defmethod codom ((x <natmorph>))
  (typecase-of natmorph x
    (nat-inj         (nat-width (1+ (num x))))
    (nat-concat      (nat-width (+ (num-left x) (num-right x))))
    (one-bit-to-bool (coprod so1 so1))
    (nat-decompose   (prod (nat-width 1) (nat-width (1- (num x)))))
    ((or nat-eq
         nat-lt)
     (coprod so1 so1))
    ((or nat-add
         nat-sub
         nat-mult
         nat-div
         nat-const)
     (nat-width (num x)))
    (otherwise
     (subclass-responsibility x))))

(defmethod codom ((x <natobj>))
  x)


(-> const (cat-morph cat-obj) (or t comp))
(defun const (f x)
  "The constant morphism.

Takes a morphism from [SO1][class] to a desired value of type $B$,
along with a [\\<SUBSTOBJ\\>] that represents the input type say of
type $A$, giving us a morphism from $A$ to $B$.

Thus if:
F : [SO1][class] → a,
X : b

then: (const f x) : a → b

```
Γ, f : so1 → b, x : a
----------------------
(const f x) : a → b
```

Further, If the input `F` has an ALIAS, then we wrap the output
in a new alias to denote it's a constant version of that value.


Example:

```lisp
(const true bool) ; bool -> bool
```"
  (let ((obj (comp f (terminal x)))
        (alias (meta-lookup f :alias)))
    (if alias
        (make-alias :name (intern (format nil "CONST-~A" alias))
                    :obj obj)
        obj)))

(-> cleave (cat-morph &rest cat-morph) pair)
(defun cleave (v1 &rest values)
  "Applies each morphism to the object in turn."
  (if (null values)
      v1
      (mvfoldr #'pair (cons v1 (butlast values)) (car (last values)))))

;; Should this be in a geb.utils: package or does it deserve to be in
;; the main geb package?

(-> commutes (cat-obj cat-obj) pair)
(defun commutes (x y)
  (pair (<-right x y) (<-left x y)))


;; TODO easy tests to make for it, just do it!
(-> commutes-left (cat-morph) comp)
(defun commutes-left (morph)
  "swap the input [domain][DOM] of the given [cat-morph]

In order to swap the [domain][DOM] we expect the [cat-morph] to
be a [PROD][class]

Thus if: `(dom morph) ≡ (prod x y)`, for any `x`, `y` [CAT-OBJ]

then: `(commutes-left (dom morph)) ≡ (prod y x)`
u
```
Γ, f : x × y → a
------------------------------
(commutes-left f) : y × x → a
```
"
  (let ((dom (dom morph)))
    (if (not (typep dom 'prod))
        (error "object ~A need to be of a product type, however it is of ~A"
               morph dom)
        (comp morph (commutes (mcadr dom) (mcar dom))))))

(-> !-> (substobj substobj) substobj)
(defun !-> (a b)
  (etypecase-of substobj a
    (so0    so1)
    (so1    b)
    (coprod (prod (!-> (mcar a)  b)
                  (!-> (mcadr a) b)))
    (prod   (!-> (mcar a)
                 (!-> (mcadr a) b)))))

(defgeneric so-card-alg (obj)
  (:documentation "Gets the cardinality of the given object, returns a FIXNUM"))

;; (-> so-card-alg (<substobj>) fixnum)
(defmethod so-card-alg ((obj <substobj>))
  ;; we don't use the cata morphism so here we are. Doesn't give me
  ;; much extra
  (match-of geb:substobj obj
    ((geb:prod a b)   (* (so-card-alg a)
                         (so-card-alg b)))
    ((geb:coprod a b) (+ (so-card-alg a)
                         (so-card-alg b)))
    (geb:so0          1)
    (geb:so1          1)))

(defmethod so-eval ((x <substobj>) y)
  (match-of substobj x
    (so0          (comp (init y) (<-right so1 so0)))
    (so1          (<-left y so1))
    ((coprod a b) (comp (mcase (comp (so-eval a y)
                                     (so-forget-middle (so-hom-obj a y) (so-hom-obj b y) a))
                               (comp (so-eval b y)
                                     (so-forget-first (so-hom-obj a y) (so-hom-obj b y) b)))
                        (distribute (prod (so-hom-obj a y) (so-hom-obj b y)) a b)))
    ((prod a b)   (let ((eyz   (so-eval b y))
                        (exhyz (so-eval a (so-hom-obj b y)))
                        (hom   (so-hom-obj a (so-hom-obj b y))))
                    (comp eyz
                          (pair (comp exhyz (so-forget-right hom a b))
                                (comp (<-right a b)
                                      (<-right hom (prod a b)))))))))

(defmethod so-eval ((x <natobj>) y)
  (let ((num (num x)))
    (if (= num 1)
        (comp (so-eval (coprod so1 so1)
                       y)
              (prod-mor (so-hom-obj x y)
                        one-bit-to-bool))
        (comp (so-eval (prod (nat-width 1)
                             (nat-width (1- num)))
                       y)
              (prod-mor (so-hom-obj x y)
                        (nat-decompose num))))))

(defmethod so-hom-obj ((x <substobj>) z)
  (match-of substobj x
    (so0          so1)
    (so1          z)
    ((coprod x y) (prod (so-hom-obj x z)
                        (so-hom-obj y z)))
    ((prod x y)   (so-hom-obj x (so-hom-obj y z)))))

(defmethod so-hom-obj ((x <natobj>) z)
  (let ((num (num x))
        (bool (coprod so1 so1)))
    (if (= num 1)
        (so-hom-obj bool
                    z)
        ;; The left part of the product is associated with what the
        ;; function does on 0, right part of what it does on 1
        ;; using the choice of interpreting false as left and
        ;; true as right in bool
        (so-hom-obj  (prod  (nat-width 1)
                            (nat-width (1- num)))
                     z))))

(-> so-forget-right (cat-obj cat-obj cat-obj) substmorph)
(defun so-forget-right (x y z)
  (pair (<-left x (prod y z))
        (comp (<-left y z)
              (<-right x (prod y z)))))

(-> so-forget-middle (cat-obj cat-obj cat-obj) substmorph)
(defun so-forget-middle (x y z)
  (pair (comp (<-left x y) (<-left (prod x y) z))
        (<-right (prod x y) z)))

(-> so-forget-first (cat-obj cat-obj cat-obj) substmorph)
(defun so-forget-first (x y z)
  (pair (comp (<-right x y) (<-left (prod x y) z))
        (<-right (prod x y) z)))

(defun gather (x y z)
  (pair (mcase (<-left x y) (<-left x z))
        (mcase (comp (->left y z) (<-right x y))
               (comp (->right y z) (<-right x z)))))

(defun prod-left-assoc (f)
  (trivia:match (dom f)
    ((prod w (prod x y))
     (comp f (pair (comp (<-left w x) (<-left (prod w x) y))
                   (pair (comp (<-right w x) (<-left (prod w x) y))
                         (<-right (prod w x) y)))))
    (_ (error "object ~A need to be of a double product type, however it is of ~A" f (dom f)))))

(defun right-morph (f)
  (trivia:match (dom f)
    ((coprod x y)
     (comp f (->right x y)))
    (_ (error "object ~A need to be of a coproduct type, however it is of ~A"
              f (dom f)))))

(defun left-morph (f)
  (trivia:match (dom f)
    ((coprod x y)
     (comp f (->left x y)))
    (_ (error "object ~A need to be of a coproduct type, however it is of ~A"
              f (dom f)))))

(defun coprod-mor (f g)
  "Given f : A  → B and g : C  → D gives appropriate morphism between
[COPROD][class] objects f x g : A + B  → C + D via the unversal property.
That is, the morphism part of the coproduct functor Geb x Geb → Geb"
  (mcase (comp (->left (codom f) (codom g))
               f)
         (comp (->right (codom f) (codom g))
               g)))

(defun prod-mor (f g)
   "Given f : A  → B and g : C  → D gives appropriate morphism between
[PROD][class] objects f x g : A x B  → C x D via the unversal property.
This is the morphism part of the product functor Geb x Geb → Geb"
  (pair (comp f
              (<-left (dom f) (dom g)))
        (comp g
              (<-right (dom f) (dom g)))))

(defgeneric text-name (morph)
  (:documentation
   "Gets the name of the moprhism"))

(defmethod text-name ((morph <substmorph>))
  (typecase-of substmorph morph
    (project-left  "π₁")
    (project-right "π₂")
    (inject-left   "ι₁")
    (inject-right  "ι₂")
    (terminal       "τ")
    (init           "Init")
    (distribute     "Dist")
    ((or case pair) "")
    (comp           "")
    (substobj       "Id")
    (otherwise (subclass-responsibility morph))))

(defmethod text-name ((morph opaque-morph))
  "")
(defmethod text-name ((morph cat-obj))
  "Id")

(defmethod maybe ((obj <substobj>))
  "I recursively add maybe terms to all [\\<SBUSTOBJ\\>][class] terms,
for what maybe means checkout [my generic function documentation][maybe].

turning [products][prod] of A x B into Maybe (Maybe A x Maybe B),

turning [coproducts][coprod] of A | B into Maybe (Maybe A | Maybe B),

turning [SO1] into Maybe [SO1]

and [SO0] into Maybe [SO0]"
  (coprod so1 obj))

(defmethod maybe ((obj <natobj>))
  (coprod so1 obj))

(defun curry (f)
  "Curries the given object, returns a [cat-morph]

The [cat-morph] given must have its DOM be of a PROD type, as [CURRY][function]
invokes the idea of

if f : ([PROD][class] a b) → c

for all `a`, `b`, and `c` being an element of [cat-morph]

then: (curry f): a → c^b

where c^b means c to the exponent of b (EXPT c b)


```
Γ, f : a × b → c,
--------------------
(curry f) : a → c^b
```

In category terms, `a → c^b` is isomorphic to `a → b → c`

"
  (if (not (typep (dom f) 'prod))
      (error "object ~A need to be of a product type, however it is of ~A" f (dom f))
      (let ((dom (dom f)))
        (curry-prod f (mcar dom) (mcadr dom)))))

(defun uncurry (y z f)
  "Given a morphism f : x → z^y and explicitly given y and z variables
produces an uncurried version f' : x × y → z of said morphism"
  (comp (so-eval y z)
        (pair (comp f (<-left (dom f) y)) (<-right (dom f) y))))

(defun morph-type (f)
  "Given a moprhism f : a → b gives a list (a, b) of the domain and
codomain respectively"
  (list (dom f) (codom f)))

(defmethod gapply ((morph <substmorph>) object)
  "My main documentation can be found on [GAPPLY][generic-function]

I am the [GAPPLY][generic-function] for [\\<SBUSTMORPH\\>][class], the
OBJECT that I expect is of type [REALIZED-OBJECT][type]. See the
documentation for [REALIZED-OBJECT][type] for the forms it can take.

Some examples of me are

```lisp
GEB> (gapply (comp
              (mcase geb-bool:true
                     geb-bool:not)
              (->right so1 geb-bool:bool))
             (left so1))
(right s-1)
GEB> (gapply (comp
              (mcase geb-bool:true
                     geb-bool:not)
              (->right so1 geb-bool:bool))
             (right so1))
(left s-1)
GEB> (gapply geb-bool:and
             (list (right so1)
                   (right so1)))
(right s-1)
GEB> (gapply geb-bool:and
             (list (left so1)
                   (right so1)))
(left s-1)
GEB> (gapply geb-bool:and
             (list (right so1)
                   (left so1)))
(left s-1)
GEB> (gapply geb-bool:and
             (list (left so1)
                   (left so1)))
(left s-1)
```
"
  (typecase-of substmorph morph
    ;; object should be a list here
    (project-left (car object))
    ;; object should be a list here
    (project-right (cadr object))
    ;; inject the left and rights
    (inject-left   (left object))
    (inject-right  (right object))
    (terminal      so1)
    ;; we could generate an arbitrary type for some subest of types,
    ;; and use this as a fuzzer, but alas
    (init          (error "Can't generate a type from void"))
    (case (etypecase-of realized-object object
            (left
             (gapply (mcar morph) (obj object)))
            (right
             (gapply (mcadr morph) (obj object)))
            ((or so0 so1 list)
             (error "invalid type application, trying to apply a
             function with a dom of type ~A to an object with value ~A"
                    (dom morph)
                    object))))
    (pair (list (gapply (mcar morph) object)
                (gapply (mcdr morph) object)))
    (comp (gapply (mcar morph)
                  (gapply (mcadr morph) object)))
    (distribute
     (etypecase-of realized-object (cadr object)
       (left
        (left (list (car object) (obj (cadr object)))))
       (right
        (right (list (car object) (obj (cadr object)))))
       ((or so1 so0 list)
        (error "invalid type application, trying to apply a
             function with a dom of type ~A to an object with value ~A"
               (dom morph)
               (cadr object)))))
    (substobj object)
    (otherwise (subclass-responsibility morph))))

(defmethod gapply ((morph <natmorph>) object)
  (typecase-of natmorph morph
    (nat-add   (+ (car object) (cadr object)))
    (nat-mult  (* (car object) (cadr object)))
    (nat-sub   (- (car object) (cadr object)))
    (nat-div   (multiple-value-bind (q)
                   (floor (car object) (cadr object)) q))
    (nat-const  (pos morph))
    (nat-inj    object)
    (nat-concat  (+ (* (expt 2 (num-right morph)) (car object)) (cadr object)))
    (one-bit-to-bool (if (= object 0)
                         (left so1)
                         (right so1)))
    (nat-decompose (if (>= object  (expt 2 (1- (num morph))))
                       (list 1 (- object (expt 2 (1- (num morph)))))
                       (list 0 object)))
    (nat-eq        (if (= (car object) (cadr object))
                       (left so1)
                       (right so1)))
    (nat-lt        (if (< (car object) (cadr object))
                       (left so1)
                       (right so1)))
    (otherwise (subclass-responsibility morph))))

;; I believe this is the correct way to use gapply for cat-obj
(defmethod gapply ((morph cat-obj) object)
  "My main documentation can be found on [GAPPLY][generic-function]

I am the [GAPPLY][generic-function] for a generic [CAT-OBJ][class]. I
simply return the object given to me"
  object)

(defmethod gapply ((morph opaque-morph) object)
  "My main documentation can be found on [GAPPLY][generic-function]

I am the [GAPPLY][generic-function] for a generic [OPAQUE-MOPRH][class]
I simply dispatch [GAPPLY][generic-function] on my interior code
```lisp
GEB> (gapply (comp geb-list:*car* geb-list:*cons*)
             (list (right geb-bool:true-obj) (left geb-list:*nil*)))
(right GEB-BOOL:TRUE)
```"
  (gapply (code morph) object))

(defmethod gapply ((morph opaque) object)
  "My main documentation can be found on [GAPPLY][generic-function]

I am the [GAPPLY][generic-function] for a generic [OPAQUE][class] I
simply dispatch [GAPPLY][generic-function] on my interior code, which
is likely just an object"
  (gapply (code morph) object))

(defmethod well-defp-cat ((morph <substmorph>))
  (etypecase-of substmorph morph
    (comp
     (let ((mcar (mcar morph))
           (mcadr (mcadr morph)))
       (if (and (well-defp-cat mcar)
                (well-defp-cat mcadr)
                (obj-equalp (dom mcar)
                            (codom mcadr)))
           t
           (error "(Co)Domains do not match for ~A" morph))))
    (case
        (let ((mcar (mcar morph))
              (mcadr (mcadr morph)))
          (if (and (well-defp-cat mcar)
                   (well-defp-cat mcadr)
                   (obj-equalp (codom mcar)
                               (codom mcadr)))
              t
              (error "Casing ill-defined for ~A" morph))))
    (pair
     (let ((mcar (mcar morph))
           (mcdr (mcdr morph)))
       (if (and (well-defp-cat mcar)
                (well-defp-cat mcdr)
                (obj-equalp (dom mcar)
                            (dom mcdr)))
           t
           (error "Pairing ill-defined for ~A" morph))))
    ((or substobj
         init
         terminal
         project-left
         project-right
         inject-left
         inject-right
         distribute)
     t)))

(defmethod well-defp-cat ((morph <natmorph>))
  t)

(defmethod well-defp-cat ((morph <natobj>))
  t)
