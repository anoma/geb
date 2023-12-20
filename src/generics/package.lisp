(pax:define-package :geb.generics
  (:use #:common-lisp)
  (:export #:@generics))

(in-package :geb.generics)

(pax:defsection @generics (:title "Geneircs")
  "These functions represent the generic functions that can be run on
many parts of the compiler, they are typically rexported on any
package that implements the given generic function.

You can view their documentation in their respective API sections.

The main documentation for the functionality is given here, with
examples often given in the specific methods"
  (gapply         generic-function)
  (well-defp-cat  generic-function)
  (maybe          generic-function)
  (so-hom-obj     generic-function)
  (so-eval        generic-function)
  (width          generic-function)
  (to-circuit     generic-function)
  (to-bitc        generic-function)
  (to-seqn        generic-function)
  (to-poly        generic-function)
  (to-cat         generic-function)
  (to-vampir      generic-function))
