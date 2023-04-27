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

Further, If the input `F` is an [ALIAS][type], then we wrap the output
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
be a [PROD][type]

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


(-> so-eval (substobj substobj) substmorph)
(defun so-eval (x y)
  (match-of substobj x
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
    ((coprod x y) (prod (so-hom-obj x z)
                        (so-hom-obj y z)))
    ((prod x y)   (so-hom-obj x (so-hom-obj y z)))))

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

(defun curry (f)
  "Curries the given object, returns a [cat-morph]

The [cat-morph] given must have its DOM be of a PROD type, as [CURRY][generic-function]
invokes the idea of

if f : ([PROD][TYPE] a b) → c

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
