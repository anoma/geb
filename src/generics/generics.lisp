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
