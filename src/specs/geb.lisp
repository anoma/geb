(in-package :geb.spec)

(defclass <substobj> (<substmorph> direct-pointwise-mixin cat-obj) ()
  (:documentation
   "the class corresponding to SUBSTOBJ. See GEB-DOCS/DOCS:@OPEN-CLOSED"))
(deftype substobj ()
  `(or alias prod coprod so0 so1))

;; we say that id doesn't exist, as we don't need the tag. If we find
;; that to ill typed (substobj is a substmorph as far as type checking
;; is concerned without an explicit id constrcutor), then we can
;; include it and remove it from the or type here.
(defclass <substmorph> (direct-pointwise-mixin cat-morph) ()
  (:documentation
   "the class type corresponding to SUBSTMORPH. See GEB-DOCS/DOCS:@OPEN-CLOSED"))
(deftype substmorph ()
  "The morphisms of the [SUBSTMORPH][type] category"
  `(or substobj
       alias
       comp init terminal case pair distribute
       inject-left inject-right
       project-left project-right))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Subst Constructor Objects
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass alias (<substobj>)
  ((name :initarg :name
         :accessor name
         :type     symbol
         :documentation "The name of the GEB object")
   (obj :initarg :obj
        :accessor obj
        :documentation "The underlying geb object"))
  (:documentation "an alias for a geb object"))

;; these could be keywords, but maybe in the future not?
(defclass so0 (<substobj>)
  ()
  (:documentation
   "The Initial Object. This is sometimes known as the
[VOID](https://en.wikipedia.org/wiki/Void_type) type.

the formal grammar of [SO0][type] is

```lisp
so0
```

where [SO0][type] is `THE` initial object.

Example

```lisp
```
"
   "The Initial/Void Object"))

(defclass so1 (<substobj>)
  ()
  (:documentation
   "The Terminal Object. This is sometimes referred to as the
[Unit](https://en.wikipedia.org/wiki/Unit_type) type.

the formal grammar or [SO1][type] is

```lisp
so1
```

where [SO1][type] is `THE` terminal object

Example

```lisp
(coprod so1 so1)
```

Here we construct [GEB-BOOL:BOOL] by simply stating that we have the
terminal object on either side, giving us two possible ways to fill
the type.

```lisp
(->left so1 so1)

(->right so1 so1)
```

where applying [->LEFT] gives us the left unit, while [->RIGHT] gives
us the right unit."))

;; please make better names and documentation strings!

(defclass prod (<substobj>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation
   "The [PRODUCT][PROD type] object. Takes two CAT-OBJ values that
get put into a pair.

The formal grammar of [PRODUCT][PROD type] is

```lisp
(prod mcar mcadr)
```

where [PROD][type] is the constructor, [MCAR] is the left value of the
product, and [MCADR] is the right value of the product.

Example:

```lisp
(geb-gui::visualize (prod geb-bool:bool geb-bool:bool))
```

Here we create a product of two [GEB-BOOL:BOOL] types."))

(defclass coprod (<substobj>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation
   "the [CO-PRODUCT][COPROD type] object. Takes CAT-OBJ values that
get put into a choice of either value.

The formal grammar of [PRODUCT][PROD type] is

```lisp
(coprod mcar mcadr)
```

Where [CORPOD][TYPE] is the constructor, [MCAR] is the left choice of
the sum, and [MCADR] is the right choice of the sum.

Example:

```lisp
(geb-gui::visualize (coprod so1 so1))
```

Here we create the boolean type, having a choice between two unit
values."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Subst Morphism Objects
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass functor (<substmorph>)
  ((obj :initarg :obj
        :accessor obj)
   (func :initarg :func
         :accessor func)))

(defclass comp (<substmorph>)
  ((mcar :initarg :mcar
         :accessor mcar
         :type cat-morph
         :documentation "The first composed morphism")
   (mcadr :initarg :mcadr
          :type cat-morph
          :accessor mcadr
          :documentation "the second morphism"))
  (:documentation
   "The composition morphism. Takes two CAT-MORPH values that get
applied in standard composition order.

The formal grammar of [COMP][type] is

```lisp
(comp mcar mcadr)
```

which may be more familiar as

```haskell
g 。f
```

Where [COMP][type]\\( 。\\) is the constructor, [MCAR]\\(g\\) is the second morphism
that gets applied, and [MCADR]\\(f\\) is the first morphism that gets
applied.

Example:

```lisp
(geb-gui::visualize
 (comp
  (<-right so1 geb-bool:bool)
  (pair (<-left so1 geb-bool:bool)
        (<-right so1 geb-bool:bool))))
```

In this example we are composing two morphisms. the first morphism
that gets applied ([PAIR] ...) is the identity function on the
type ([PROD][type] [SO1][type] [GEB-BOOL:BOOL]), where we pair the
[left projection](PROJECT-LEFT) and the [right
projection](PROJECT-RIGHT), followed by taking the [right
projection](PROJECT-RIGHT) of the type.

Since we know ([COMP][type] f id) is just f per the laws of category
theory, this expression just reduces to

```lisp
(<-right so1 geb-bool:bool)
```"))

(defclass init (<substmorph>)
  ((obj :initarg :obj
        :accessor obj
        :type cat-obj
        :documentation ""))
  (:documentation
   "The [INITIAL][INIT type] Morphism, takes any [CAT-OBJ] and
creates a moprhism from [SO0][type] (also known as void) to the object given.

The formal grammar of [INITIAL][INIT type] is

```lisp
(init obj)
```

where [INIT][type] is the constructor. [OBJ] is the type of object
that will be conjured up from [SO0][type], when the morphism is
applied onto an object.

Example:

```lisp
(init so1)
```

In this example we are creating a unit value out of void."))

(defclass terminal (<substmorph>)
  ((obj :initarg :obj
        :accessor obj
        :type cat-obj
        :documentation ""))
  (:documentation
   "The [TERMINAL][type] morphism, Takes any [CAT-OBJ] and creates a
morphism from that object to [SO1][type] (also known as unit).

The formal grammar of [TERMINAL][type] is

```lisp
(terminal obj)
```

where [TERMINAL][type] is the constructor. [OBJ] is the type of object that
will be mapped to [SO1][type], when the morphism is applied onto an
object.

Example:

```lisp
(terminal (coprod so1 so1))

(geb-gui::visualize (terminal (coprod so1 so1)))

(comp value (terminal (codomain value)))

(comp true (terminal bool))
```

In the first example, we make a morphism from the corpoduct of
[SO1][type] and [SO1][type] (essentially [GEB-BOOL:BOOL]) to
[SO1][type].

In the third example we can proclaim a constant function by ignoring
the input value and returning a morphism from unit to the desired type.

The fourth example is taking a [GEB-BOOL:BOOL] and returning [GEB-BOOL:TRUE]."))

;; Please name all of these better plz

(defclass inject-left (<substmorph>)
  ((mcar :initarg :mcar
         :accessor mcar
         :type cat-obj
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :type cat-obj
          :documentation ""))
  (:documentation
   "The left injection morphism. Takes two CAT-OBJ values. It is
the dual of INJECT-RIGHT

The formal grammar is

```lisp
(->left mcar mcadr)
```

Where [->LEFT] is the constructor, [MCAR] is the value being injected into
the coproduct of [MCAR] + [MCADR], and the [MCADR] is just the type for
the unused right constructor.

Example:

```lisp
(geb-gui::visualize (->left so1 geb-bool:bool))

(comp
 (mcase geb-bool:true
        geb-bool:not)
 (->left so1 geb-bool:bool))

```

In the second example, we inject a term with the shape SO1 into a pair
with the shape ([SO1][type] × [GEB-BOOL:BOOL]), then we use MCASE to denote a
morphism saying. `IF` the input is of the shape [SO1], then give us True,
otherwise flip the value of the boolean coming in."))

(defclass inject-right (<substmorph>)
  ((mcar :initarg :mcar
         :accessor mcar
         :type cat-obj
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :type cat-obj
          :documentation ""))
  (:documentation
   "The right injection morphism. Takes two CAT-OBJ values. It is
the dual of INJECT-LEFT

The formal grammar is

```lisp
(->right mcar mcadr)
```

Where ->RIGHT is the constructor, [MCADR] is the value being injected into
the coproduct of [MCAR] + [MCADR], and the [MCAR] is just the type for
the unused left constructor.

Example:

```lisp
(geb-gui::visualize (->right so1 geb-bool:bool))

(comp
 (mcase geb-bool:true
        geb-bool:not)
 (->right so1 geb-bool:bool))

```

In the second example, we inject a term with the shape [GEB-BOOL:BOOL]
into a pair with the shape ([SO1][type] × [GEB-BOOL:BOOL]), then we use
[MCASE] to denote a morphism saying. IF the input is of the shape [SO1],
then give us True, otherwise flip the value of the boolean coming in."))

(defclass case (<substmorph>)
  ((mcar :initarg :mcar
         :accessor mcar
         :type cat-morph
         :documentation "The morphism that gets applied on the left coproduct")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :type cat-morph
          :documentation "The morphism that gets applied on the right coproduct"))
  (:documentation
   "Eliminates coproducts. Namely Takes two CAT-MORPH values, one
gets applied on the left coproduct while the other gets applied on the
right coproduct. The result of each CAT-MORPH values must be
the same.

The formal grammar of [CASE][type] is:

```lisp
(mcase mcar mcadr)
```

Where [MCASE] is the constructor, [MCAR] is the morphism that gets
applied to the left coproduct, and [MCADR] is the morphism that gets
applied to the right coproduct.

Example:

```lisp
(comp
 (mcase geb-bool:true
        geb-bool:not)
 (->right so1 geb-bool:bool))
```

In the second example, we inject a term with the shape [GEB-BOOL:BOOL]
into a pair with the shape ([SO1][type] × [GEB-BOOL:BOOL]), then we use
[MCASE] to denote a morphism saying. IF the input is of the shape [SO1],
then give us True, otherwise flip the value of the boolean coming in."))

(defclass pair (<substmorph>)
  ((mcar :initarg :mcar
         :accessor mcar
         :type cat-morph
         :documentation "The left morphism")
   (mcdr :initarg :mcdr
         :accessor mcdr
         :type cat-morph
         :documentation "The right morphism"))
  (:documentation
   "Introduces products. Namely Takes two CAT-MORPH values. When
the PAIR morphism is applied on data, these two [CAT-MORPH]'s are
applied to the object, returning a pair of the results

The formal grammar of constructing an instance of pair is:

```
(pair mcar mcdr)
```

where PAIR is the constructor, MCAR is the left morphism, and MCDR is
the right morphism

Example:

```lisp
(pair (<-left so1 geb-bool:bool)
      (<-right so1 geb-bool:bool))

(geb-gui::visualize (pair (<-left so1 geb-bool:bool)
                          (<-right so1 geb-bool:bool)))
```

Here this pair morphism takes the pair SO1 × GEB-BOOL:BOOL, and
projects back the left field SO1 as the first value of the pair and
projects back the GEB-BOOL:BOOL field as the second values."))

(defclass project-left (<substmorph>)
  ((mcar :initarg :mcar
         :accessor mcar
         :type cat-obj
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :type cat-obj
          :documentation ""))
  (:documentation
   "The [LEFT PROJECTION][PROJECT-LEFT type]. Takes two
[CAT-MORPH] values. When the [LEFT PROJECTION][PROJECT-LEFT
type] morphism is then applied, it grabs the left value of a product,
with the type of the product being determined by the two
[CAT-MORPH] values given.

the formal grammar of a [PROJECT-LEFT][type] is:

```lisp
(<-left mcar mcadr)
```

Where [<-LEFT] is the constructor, [MCAR] is the left type of the
[PRODUCT][type] and [MCADR] is the right type of the [PRODUCT][type].

Example:

```lisp
(geb-gui::visualize
  (<-left geb-bool:bool (prod so1 geb-bool:bool)))
```

In this example, we are getting the left [GEB-BOOL:BOOL] from a
product with the shape

([GEB-BOOL:BOOL][] [×][PROD type] [SO1][type] [×][PROD type] [GEB-BOOL:BOOL])"))

(defclass project-right (<substmorph>)
  ((mcar :initarg :mcar
         :accessor mcar
         :type cat-obj
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :type cat-obj
          :documentation "Right projection (product elimination)"))
  (:documentation "The [RIGHT PROJECTION][PROJECT-RIGHT type]. Takes two
[CAT-MORPH] values. When the [RIGHT PROJECTION][PROJECT-RIGHT
type] morphism is then applied, it grabs the right value of a product,
with the type of the product being determined by the two
[CAT-MORPH] values given.


the formal grammar of a [PROJECT-RIGHT][type] is:

```lisp
(<-right mcar mcadr)
```

Where [<-RIGHT] is the constructor, [MCAR] is the right type of the
[PRODUCT][type] and [MCADR] is the right type of the [PRODUCT][type].

Example:

```lisp
(geb-gui::visualize
 (comp (<-right so1 geb-bool:bool)
       (<-right geb-bool:bool (prod so1 geb-bool:bool))))
```

In this example, we are getting the right [GEB-BOOL:BOOL] from a
product with the shape

([GEB-BOOL:BOOL][] [×][PROD type] [SO1][type] [×][PROD type] [GEB-BOOL:BOOL])"))

(defclass distribute (<substmorph>)
  ((mcar :initarg :mcar
         :accessor mcar
         :type cat-obj
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :type cat-obj
          :documentation "")
   (mcaddr :initarg :mcaddr
           :accessor mcaddr
           :type cat-obj
           :documentation ""))
  (:documentation "The distributive law"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructors for the base types
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; this is considered bad style, one should call their constructors
;; make, but it does not matter

(defparameter *so0* (make-instance 'so0)
  "The Initial Object")
(def so0 *so0*
  "The Initial Object")
(defparameter *so1* (make-instance 'so1)
  "The Terminal Object")
(def so1 *so1*
  "The Terminal Object")

(-> prod (t t) prod)
(defun prod (car cadr)
  (values
   (make-instance 'prod :mcar car :mcadr cadr)))

(-> coprod (t t) coprod)
(defun coprod (car cadr)
  (values
   (make-instance 'coprod :mcar car :mcadr cadr)))

(defmacro alias (name obj)
  `(make-alias :name ',name :obj ,obj))

(-> make-alias (&key (:name symbol) (:obj t)) alias)
(defun make-alias (&key name obj)
  (values
   (make-instance 'alias :name name :obj obj)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructors for the morphism constructors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; we could type the objects more if wanted

(-> comp (cat-morph cat-morph &rest cat-morph) comp)
(defun comp (car cadr &rest comps)
  (let ((list (list* car cadr comps)))
    (mvfoldr (lambda (x acc)
               (make-instance 'comp :mcar x :mcadr acc))
             (butlast list)
             (car (last list)))))

(-> init (cat-obj) init)
(defun init (obj)
  (values
   (make-instance 'init :obj obj)))

(-> terminal (cat-obj) terminal)
(defun terminal (obj)
  (values
   (make-instance 'terminal :obj obj)))

(-> ->left (cat-obj cat-obj) inject-left)
(defun ->left (mcar mcadr)
  "injects left constructor"
  (values
   (make-instance 'inject-left :mcar mcar :mcadr mcadr)))

(-> ->right (cat-obj cat-obj) inject-right)
(defun ->right (mcar mcadr)
  "injects right constructor"
  (values
   (make-instance 'inject-right :mcar mcar :mcadr mcadr)))

(-> <-left (cat-obj cat-obj) project-left)
(defun <-left (mcar mcadr)
  "projects left constructor"
  (values
   (make-instance 'project-left :mcar mcar :mcadr mcadr)))

(-> <-right (cat-obj cat-obj) project-right)
(defun <-right (mcar mcadr)
  "projects right constructor"
  (values
   (make-instance 'project-right :mcar mcar :mcadr mcadr)))

(-> mcase (cat-morph cat-morph) case)
(defun mcase (mcar mcadr)
  (values
   (make-instance 'case :mcar mcar :mcadr mcadr)))

(-> pair (cat-morph cat-morph) pair)
(defun pair (mcar mcdr)
  (values
   (make-instance 'pair :mcar mcar :mcdr mcdr)))

(-> distribute (cat-obj cat-obj cat-obj) distribute)
(defun distribute (mcar mcadr mcaddr)
  (values
   (make-instance 'distribute :mcar mcar :mcadr mcadr :mcaddr mcaddr)))

(defun make-functor (&key obj func)
  (make-instance 'functor :func func :obj obj))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Extra Accessors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod mcar ((obj terminal))
  (obj obj))

(defmethod mcar ((obj init))
  (obj obj))

(defmethod mcar ((alias alias))
  (mcar (obj alias)))

(defmethod mcadr ((alias alias))
  (mcadr (obj alias)))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pattern Matching conveniences
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; less safe than I wanted due to the names can be out of sync, but
;; w/e I can fix it with a better defclass macro
(make-pattern alias  name obj)
(make-pattern prod   mcar mcadr)
(make-pattern so1    mcar mcadr)
(make-pattern so0    mcar mcadr)
(make-pattern coprod mcar mcadr)
(make-pattern init          obj)
(make-pattern terminal      obj)
(make-pattern comp          mcar mcadr)
(make-pattern inject-left   mcar mcadr)
(make-pattern inject-right  mcar mcadr)
(make-pattern case          mcar mcadr)
(make-pattern pair          mcar mcdr)
(make-pattern project-left  mcar mcadr)
(make-pattern project-right mcar mcadr)
(make-pattern distribute    mcar mcadr mcaddr)
