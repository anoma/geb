(in-package :geb-test)

(define-test geb-pipeline :parent geb-test-suite)

(def test-compilation-eval-2
  (geb.lambda.spec:typed geb.lambda.spec:unit geb:so1))


(define-test pipeline-works-for-stlc-to-vampir
  :parent geb-pipeline
  (parachute:finish
   (geb.entry:compile-down :vampir t
                           :stlc t
                           :entry "geb-test::test-compilation-eval-2")))
