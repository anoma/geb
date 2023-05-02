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
;; Conversion functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defgeneric to-bitc (morphism)
  (:documentation
   "Turns a given MORPHISM into a [GEB.BITC.SPEC:BITC]"))

(defgeneric to-poly (morphism)
  (:documentation
   "Turns a given MORPHISM into a [GEB.POLY.SPEC:POLY]"))

(defgeneric to-circuit (morphism name)
  (:documentation
   "Turns a MORPHISM into a Vampir circuit. the NAME is the given name of
the output circuit."))

(defgeneric to-vampir (morphism values)
  (:documentation
   "Turns a MORPHISM into a Vampir circuit, with concrete values.

The more natural interface is [TO-CIRCUIT], however this is a more low
level interface into what the polynomial categories actually
implement, and thus can be extended or changed.

The VALUES are likely vampir values in a list."))
