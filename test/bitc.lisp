(in-package :geb-test)

(define-test geb-bitc :parent geb-test-suite)

(def test-circuit-1
  (to-circuit
   (bitc:compose (bitc:branch
                  (bitc:parallel (bitc:compose (bitc:parallel bitc:zero
                                                              (bitc:ident 0))
                                               (bitc:drop 1))
                                 (bitc:ident 0))
                  (bitc:parallel (bitc:parallel (bitc:ident 1)
                                                (bitc:drop 0))
                                 (bitc:ident 0)))
    (bitc:parallel (bitc:swap 1 1)
                   (bitc:ident 0)))
   :tc_1))

(define-test vampir-converter
  :parent geb-bitc
  (of-type geb.vampir.spec:alias test-circuit-1))
