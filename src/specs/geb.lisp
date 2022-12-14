(in-package :geb.spec)

(defclass <substobj> (direct-pointwise-mixin) ()
  (:documentation
   "the class corresponding to SUBSTOBJ. See GEB-DOCS/DOCS:@OPEN-CLOSED"))
(deftype substobj ()
  `(or alias prod coprod so0 so1))

;; we say that id doesn't exist, as we don't need the tag. If we find
;; that to ill typed (substobj is a substmorph as far as type checking
;; is concerned without an explicit id constrcutor), then we can
;; include it and remove it from the or type here.
(defclass <substmorph> (direct-pointwise-mixin) ()
  (:documentation
   "the class type corresponding to SUBSTMORPH. See GEB-DOCS/DOCS:@OPEN-CLOSED"))
(deftype substmorph ()
  `(or substobj
       alias
       comp init terminal case pair distribute
       inject-left inject-right
       project-left project-right))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Subst Constructor Objects
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass alias (<substmorph> <substobj>)
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
  (:documentation "The Initial/Void Object"))

(defclass so1 (<substobj>)
  ()
  (:documentation "The Terminal/Unit Object"))

;; please make better names and documentation strings!

(defclass prod (<substobj>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation "the product"))

(defclass coprod (<substobj>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation "the coproduct"))


;; please make better names

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
         :type substmorph
         :documentation "The first composed morphism")
   (mcadr :initarg :mcadr
          :type substmorph
          :accessor mcadr
          :documentation "the second morphism"))
  (:documentation
   "The composition morphism. Takes two \\<SUBSTMORPH\\> values that get
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
[left injection](INJECT-LEFT) and the [right
projection](INJECT-RIGHT), followed by taking the [right
projection](INJECT-RIGHT) of the type.

Since we know ([COMP][type] f id) is just f per the laws of category
theory, this expression just reduces to

```lisp
(<-right so1 geb-bool:bool)
```"))

(defclass init (<substmorph>)
  ((obj :initarg :obj
        :accessor obj
        :type substobj
        :documentation ""))
  (:documentation "The initial Morphism"))

(defclass terminal (<substmorph>)
  ((obj :initarg :obj
        :accessor obj
        :type substobj
        :documentation ""))
  (:documentation "The terminal Morhpism"))

;; Please name all of these better plz

(defclass inject-left (<substmorph>)
  ((mcar :initarg :mcar
         :accessor mcar
         :type <substobj>
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :type <substobj>
          :documentation ""))
  (:documentation
   "The left injection morphism. Takes two \\<SUBSTOBJ\\> values. It is
the dual of INJECT-RIGHT

The formal grammar is

```lisp
(left-> mcar mcadr)
```

Where LEFT-> is the constructor, [MCAR] is the value being injected into
the coproduct of [MCAR] + [MCADR], and the [MCADR] is just the type for
the unused right constructor.

Example:

```lisp
(geb-gui::visualize (left-> so1 geb-bool:bool))

(comp
 (mcase geb-bool:true
        geb-bool:not)
 (left-> so1 geb-bool:bool))

```

In the second example, we inject a term with the shape SO1 into a pair
with the shape ([SO1][type] × [GEB-BOOL:BOOL]), then we use MCASE to denote a
morophism saying. `IF` the input is of the shape [SO1], then give us True,
otherwise flip the value of the boolean coming in."))

(defclass inject-right (<substmorph>)
  ((mcar :initarg :mcar
         :accessor mcar
         :type substobj
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :type substobj
          :documentation ""))
  (:documentation
   "The right injection morphism. Takes two \\<SUBSTOBJ\\> values. It is
the dual of INJECT-LEFT

The formal grammar is

```lisp
(right-> mcar mcadr)
```

Where RIGHT-> is the constructor, [MCADR] is the value being injected into
the coproduct of [MCAR] + [MCADR], and the [MCAR] is just the type for
the unused left constructor.

Example:

```lisp
(geb-gui::visualize (right-> so1 geb-bool:bool))

(comp
 (mcase geb-bool:true
        geb-bool:not)
 (right-> so1 geb-bool:bool))

```

In the second example, we inject a term with the shape [GEB-BOOL:BOOL]
into a pair with the shape ([SO1][type] × [GEB-BOOL:BOOL]), then we use
[MCASE] to denote a morophism saying. IF the input is of the shape [SO1],
then give us True, otherwise flip the value of the boolean coming in."))

(defclass case (<substmorph>)
  ((mcar :initarg :mcar
         :accessor mcar
         :type <substmorph>
         :documentation "The morphism that gets applied on the left coproduct")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :type <substmorph>
          :documentation "The morphism that gets applied on the right coproduct"))
  (:documentation
   "Eliminates coproducts. Namely Takes two \\<SUBSTMORPH\\> values, one
gets applied on the left coproduct while the other gets applied on the
right coproduct. The result of each \\<SUBSTMORPH\\> values must be
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
 (right-> so1 geb-bool:bool))
```

In the second example, we inject a term with the shape [GEB-BOOL:BOOL]
into a pair with the shape ([SO1][type] × [GEB-BOOL:BOOL]), then we use
[MCASE] to denote a morophism saying. IF the input is of the shape [SO1],
then give us True, otherwise flip the value of the boolean coming in."))

(defclass pair (<substmorph>)
  ((mcar :initarg :mcar
         :accessor mcar
         :type <substmorph>
         :documentation "The left morphism")
   (mcdr :initarg :mcdr
         :accessor mcdr
         :type <substmorph>
         :documentation "The right morphism"))
  (:documentation
   "Introduces products. Namely Takes two \\<SUBSTMORPH\\> values. When
the PAIR morphism is applied on data, these two [\\<SUBSTMORPH\\>]'s are
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
         :type substobj
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :type substobj
          :documentation ""))
  (:documentation "Left projection (product elimination)"))

(defclass project-right (<substmorph>)
  ((mcar :initarg :mcar
         :accessor mcar
         :type substobj
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :type substobj
          :documentation "Right projection (product elimination)"))
  (:documentation ""))

(defclass distribute (<substmorph>)
  ((mcar :initarg :mcar
         :accessor mcar
         :type substobj
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :type substobj
          :documentation "")
   (mcaddr :initarg :mcaddr
           :accessor mcaddr
           :type substobj
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

(-> comp (substmorph substmorph) comp)
(defun comp (car cadr)
  (values
   (make-instance 'comp :mcar car :mcadr cadr)))

(-> init (substobj) init)
(defun init (obj)
  (values
   (make-instance 'init :obj obj)))

(-> terminal (substobj) terminal)
(defun terminal (obj)
  (values
   (make-instance 'terminal :obj obj)))

(-> left-> (substobj substobj) inject-left)
(defun left-> (mcar mcadr)
  "injects left constructor"
  (values
   (make-instance 'inject-left :mcar mcar :mcadr mcadr)))

(-> right-> (substobj substobj) inject-right)
(defun right-> (mcar mcadr)
  "injects right constructor"
  (values
   (make-instance 'inject-right :mcar mcar :mcadr mcadr)))

(-> <-left (substobj substobj) project-left)
(defun <-left (mcar mcadr)
  "projects left constructor"
  (values
   (make-instance 'project-left :mcar mcar :mcadr mcadr)))

(-> <-right (substobj substobj) project-right)
(defun <-right (mcar mcadr)
  "projects right constructor"
  (values
   (make-instance 'project-right :mcar mcar :mcadr mcadr)))

(-> mcase (substmorph substmorph) case)
(defun mcase (mcar mcadr)
  (values
   (make-instance 'case :mcar mcar :mcadr mcadr)))

(-> pair (substmorph substmorph) pair)
(defun pair (mcar mcdr)
  (values
   (make-instance 'pair :mcar mcar :mcdr mcdr)))

(-> distribute (substobj substobj substobj) distribute)
(defun distribute (mcar mcadr mcaddr)
  (values
   (make-instance 'distribute :mcar mcar :mcadr mcadr :mcaddr mcaddr)))

(defun make-functor (&key obj func)
  (make-instance 'functor :func func :obj obj))
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
(make-pattern pair          mcar mcadr)
(make-pattern project-left  mcar mcadr)
(make-pattern project-right mcar mcadr)
(make-pattern distribute    mcar mcadr mcaddr)
