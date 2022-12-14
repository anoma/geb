(in-package :geb-test)

(define-test geb.lambda-conversion
  :parent geb-test-suite)

(def so-unit-type
  geb:so1)

(def stlc-unit-term
  geb.lambda.spec:unit)

(def so-unit-term
  (geb:terminal so-unit-type))

(define-test compile-checked-term :parent geb.lambda-conversion
  (is obj-equalp
      (conversion:compile-checked-term nil so-unit-type stlc-unit-term)
      so-unit-term
      "compile unit"))

(define-test stlc-ctx-to-mu :parent compile-checked-term
  (is equalp
      (conversion:stlc-ctx-to-mu nil)
      geb:so1
      "compile in a nil context"))
