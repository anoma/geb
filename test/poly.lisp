(in-package :geb-test)

(define-test geb-poly :parent geb-test-suite)

(def test-circuit-1
  (to-circuit (poly:+ 1 (poly:+ poly:ident (poly:* 3 poly:ident)))
    :tc_1))

(def test-circuit-2
  (to-circuit (poly:if-lt (poly:+ 2 (poly:+ poly:ident (poly:* 3 poly:ident)))
                          (poly:+ 1 (poly:+ poly:ident (poly:* 3 poly:ident)))
                          5
                          8)
              :foo))

(define-test vampir-converter
  :parent geb-poly
  (of-type geb.vampir.spec:alias test-circuit-1)
  (of-type geb.vampir.spec:alias test-circuit-2))

(define-test poly-interpreter :parent geb-poly)

;; please add more tests
(define-test interpret-basic-poly :parent poly-interpreter
  (is
   =
   (gapply (geb.poly:if-zero (geb.poly:- geb.poly:ident geb.poly:ident 1)
                             10
                             geb.poly:ident)
           5)
   5)
  (is
   =
   (gapply (geb.poly:if-zero (geb.poly:- geb.poly:ident geb.poly:ident)
                             10
                             geb.poly:ident)
           5)
   10))
