(in-package :geb-test)

(define-test geb-poly :parent geb-test-suite)

(define-test vampir-converter
  :parent geb-poly
  (of-type geb.vampir.spec:alias
           poly::(to-circuit (+ 1 (+ ident (* 3 ident))) :my-fun)))
