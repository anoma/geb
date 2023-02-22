(in-package :geb-test)

(define-test geb-poly :parent geb-test-suite)

(def test-circuit-1
  (poly:to-circuit (poly:+ 1 (poly:+ poly:ident (poly:* 3 poly:ident)))
    :tc_1))

(def test-circuit-2
  (poly:to-circuit (poly:if-lt (poly:+ 2 (poly:+ poly:ident (poly:* 3 poly:ident)))
                               (poly:+ 1 (poly:+ poly:ident (poly:* 3 poly:ident)))
                               5
                               8)
                   :foo))

(define-test vampir-converter
  :parent geb-poly
  (of-type geb.vampir.spec:alias test-circuit-1)
  (of-type geb.vampir.spec:alias test-circuit-2))
