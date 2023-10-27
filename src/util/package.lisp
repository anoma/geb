(pax:define-package #:geb.utils
  (:documentation "provides the utility functions for the Geb project")
  (:use #:common-lisp #:serapeum))

(in-package :geb.utils)

(pax:defsection @geb-utils-manual (:title "Geb Utilities")
  "The Utilities package provides general utility functionality that is
used throughout the GEB codebase"
  (list-of                 pax::type)
  (symbol-to-keyword       pax::function)
  (muffle-package-variance pax:macro)
  (subclass-responsibility pax::function)
  (shallow-copy-object     pax::function)
  (copy-instance           pax::generic-function)
  (make-pattern            pax:macro)
  (number-to-digits        pax::function)
  (digit-to-under          pax::function)
  (number-to-under         pax::function)
  (apply-n                 pax::function)
  (@geb-accessors          pax::section))

(pax:defsection @geb-accessors (:title "Accessors")
  "These functions are generic lenses of the GEB codebase. If a class is
   defined, where the names are not known, then these accessors are
   likely to be used. They may even augment existing classes."
  (mcar      pax::generic-function)
  (mcadr     pax::generic-function)
  (mcaddr    pax::generic-function)
  (mcadddr   pax::generic-function)
  (mcdr      pax::generic-function)
  (obj       pax::generic-function)
  (name      pax::generic-function)
  (func      pax::generic-function)
  (predicate pax::generic-function)
  (then      pax::generic-function)
  (else      pax::generic-function)
  (code      pax::generic-function))
