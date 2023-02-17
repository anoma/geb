(in-package :geb-test)

(define-test geb-pipeline :parent geb-test-suite)

(def test-compilation-eval-2
  (lambda:typed geb.lambda.spec:unit geb:so1))


(defparameter *entry*
  (lambda:typed
   (lambda:app (coprod so1 so1)
               (coprod so1 so1)
               (lambda:lamb (coprod so1 so1) (coprod so1 so1) (lambda:index 0))
               (lambda:left (coprod so1 so1) (coprod so1 so1) lambda:unit))
   (coprod so1 so1)))

(define-test pipeline-works-for-stlc-to-vampir
  :parent geb-pipeline
  (parachute:finish
   (geb.entry:compile-down :vampir t
                           :stlc t
                           :entry "geb-test::test-compilation-eval-2"))
  (parachute:finish
   (geb.entry:compile-down :stlc t
                           :entry "geb-test::*entry*")))
