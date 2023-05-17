(in-package :geb-test)

(define-test geb-bitc :parent geb-test-suite)

(def bitc-circuit-1
  (bitc:compose (bitc:branch
                 (bitc:parallel (bitc:compose (bitc:parallel bitc:zero
                                                             (bitc:ident 0))
                                              (bitc:drop 1))
                                (bitc:ident 0))
                 (bitc:parallel (bitc:parallel (bitc:ident 1)
                                               (bitc:drop 0))
                                (bitc:ident 0)))
                (bitc:parallel (bitc:swap 1 1)
                               (bitc:ident 0))))

(def test-circuit-1
  (to-circuit bitc-circuit-1 :tc_1))

(define-test vampir-converter
  :parent geb-bitc
  (of-type geb.vampir.spec:alias test-circuit-1))


(define-test bitc-evaluates-and-correctly
  :parent geb-bitc
  (is equalp #*1 (gapply (to-bitc geb-bool:and) #*11))
  (is equalp #*0 (gapply (to-bitc geb-bool:and) #*10))
  (is equalp #*0 (gapply (to-bitc geb-bool:and) #*01))
  (is equalp #*0 (gapply (to-bitc geb-bool:and) #*00)))

(define-test bitc-swap-evaluation
  :parent geb-bitc
  (is equalp #*011 (gapply (bitc:swap 0 3) #*011))
  (is equalp #*011 (gapply (bitc:swap 3 0) #*011))
  (is equalp #*101 (gapply (bitc:swap 2 1) #*011))
  (is equalp #*110 (gapply (bitc:swap 2 1) #*101))
  (is equalp #*011 (gapply (bitc:swap 2 1) #*110))
  (is equalp #*01011 (gapply (bitc:swap 2 3) #*11010))
  (is equalp #*100110 (gapply (bitc:swap 3 3) #*110100)))
