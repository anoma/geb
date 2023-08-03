(in-package :geb.generics)

(defgeneric gapply (morphism object)
  (:documentation "Applies a given Moprhism to a given object.

This is practically a naive interpreter for any category found
throughout the codebase.

Some example usages of GAPPLY are.

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
```"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Object Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(defgeneric maybe (object)
  (:documentation
   "Wraps the given OBJECT into a Maybe monad The Maybe monad in this
case is simply wrapping the term in a [coprod][geb.spec:coprod]
of [so1][geb.spec:so1]"))

(defgeneric so-eval (object1 object2)
  (:documentation
   "Takes in X and Y Geb objects and provides an evaluation morphism
(prod (so-hom-obj X Y) X) -> Y"))

(defgeneric so-eval (object1 object2)
  (:documentation
   "Takes in X and Y Geb objects and provides an evaluation morphism
(prod (so-hom-obj X Y) X) -> Y"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Conversion functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgeneric to-bitc (morphism)
  (:documentation
   "Turns a given MORPHISM into a [GEB.BITC.SPEC:BITC]"))

(defgeneric to-poly (morphism)
  (:documentation
   "Turns a given MORPHISM into a [GEB.POLY.SPEC:POLY]"))

(defgeneric to-seqn (morphism)
  (:documentation
   "Turns a given MORPHISM into a [GEB.SEQN.SPEC:SEQN]"))

(defgeneric to-circuit (morphism name)
  (:documentation
   "Turns a MORPHISM into a Vampir circuit. the NAME is the given name of
the output circuit."))

(defgeneric to-vampir (morphism values constraints)
  (:documentation
   "Turns a MORPHISM into a Vampir circuit, with concrete values.

The more natural interface is [TO-CIRCUIT], however this is a more low
level interface into what the polynomial categories actually
implement, and thus can be extended or changed.

The VALUES are likely vampir values in a list.

The CONSTRAINTS represent constraints that get creating"))

(defgeneric to-cat (context term)
  (:documentation
   "Turns a MORPHISM with a context into Geb's Core category"))
