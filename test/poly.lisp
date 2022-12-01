(in-package :geb-test)

(define-test geb-poly :parent geb-test-suite)

(define-test vampir-converter
  :parent geb-poly
  (of-type geb.vampir.spec:alias
           (poly::to-circuit (poly:+ 1 (poly:+ poly:ident (poly:* 3 poly:ident)))
                             :my-fun)))
