(in-package :geb-test)

(define-test geb-bitc :parent geb-test-suite)

(def test-circuit-1
  (bitc:to-circuit 
    (bitc:comp 
      (bitc:branch
        (bitc:parallel (bitc:comp (bitc:parallel bitc:zero (bitc:identity 0))  (bitc:drop 1)) (bitc:identity 0))
        (bitc:parallel (bitc:parallel (bitc:identity 1) (bitc:drop 0)) (bitc:identity 0))) 
      (bitc:parallel (bitc:swap 1 1) (bitc:identity 0)))
    :tc_1))

(define-test vampir-converter
  :parent geb-bitc
  (of-type geb.vampir.spec:alias test-circuit-1))
