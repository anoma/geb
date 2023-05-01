(in-package :geb-test)

(define-test geb-pipeline :parent geb-test-suite)

(def test-compilation-eval-2
  (geb.lambda.spec:unit))


(defparameter *entry*
   (lambda:app
    (lambda:lamb (list (coprod so1 so1)) (lambda:index 0))
    (list (lambda:left so1 (lambda:unit)))))

(define-test pipeline-works-for-stlc-to-vampir
  :parent geb-pipeline
  (parachute:finish
   (geb.entry:compile-down :vampir t
                           :stlc t
                           :entry "geb-test::test-compilation-eval-2"))
  (parachute:finish
   (geb.entry:compile-down :stlc t
                           :entry "geb-test::*entry*")))
