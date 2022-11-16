(in-package :geb-test)

(def-suite geb.lambda-conversion
    :description "Tests the geb.lambda-conversion package")

(in-suite geb.lambda-conversion)

(def so-unit-type
  geb:so1)

(def stlc-unit-term
  geb.lambda.spec:unit)

(def so-unit-term
  (geb:terminal so-unit-type))

(test compile-unit
  (is (obj-equalp (conversion:compile-checked-term nil so-unit-type stlc-unit-term)
                  so-unit-term)))
