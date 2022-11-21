(pax:define-package #:geb.utils
  (:documentation "provides the utility functions for the Geb project")
  (:shadow #:deftype)
  (:use #:common-lisp #:serapeum))

(in-package :geb.utils)

(pax:defsection @geb-utils-manual (:title "Geb Utilities")
  "The Utilities package provide general utility functionality that is
used throughout the GEB codebase"
  (symbol-to-keyword pax:function)
  (muffle-package-variance pax:macro))
