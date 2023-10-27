(pax:define-package :geb.generics
  (:use #:common-lisp))

(in-package :geb.generics)

(pax:defsection @generics (:title "Geneircs")
  "These functions represent the generic functions that can be run on
many parts of the compiler, they are typically rexported on any
package that implements the given generic function.

You can view their documentation in their respective API sections.

The main documentation for the functionality is given here, with
examples often given in the specific methods"
  (gapply         pax::generic-function)
  (well-defp-cat  pax::generic-function)
  (maybe          pax::generic-function)
  (so-eval        pax::generic-function)
  (to-circuit     pax::generic-function)
  (to-bitc        pax::generic-function)
  (to-seqn        pax::generic-function)
  (to-poly        pax::generic-function)
  (to-cat         pax::generic-function)
  (to-vampir      pax::generic-function))
