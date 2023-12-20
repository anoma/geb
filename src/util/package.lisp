(pax:define-package #:geb.utils
  (:documentation "provides the utility functions for the Geb project")
  (:use #:common-lisp #:serapeum)
  (:export #:@geb-utils-manual #:@geb-accessors))

(in-package :geb.utils)

(pax:defsection @geb-utils-manual (:title "Geb Utilities")
  "The Utilities package provides general utility functionality that is
used throughout the GEB codebase"
  (list-of                 type)
  (symbol-to-keyword       function)
  (muffle-package-variance pax:macro)
  (subclass-responsibility function)
  (shallow-copy-object     function)
  (copy-instance           generic-function)
  (make-pattern            pax:macro)
  (number-to-digits        function)
  (digit-to-under          function)
  (number-to-under         function)
  (apply-n                 function)
  (@geb-accessors          pax:section))

(pax:defsection @geb-accessors (:title "Accessors")
  "These functions are generic lenses of the GEB codebase. If a class is
   defined, where the names are not known, then these accessors are
   likely to be used. They may even augment existing classes."
  (mcar      generic-function)
  (mcadr     generic-function)
  (mcaddr    generic-function)
  (mcadddr   generic-function)
  (mcdr      generic-function)
  (obj       generic-function)
  (name      generic-function)
  (func      generic-function)
  (predicate generic-function)
  (then      generic-function)
  (else      generic-function)
  (code      generic-function))
