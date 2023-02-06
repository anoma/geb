(in-package :geb-test)

(define-test geb.lambda.experimental :parent geb-test-suite)

(def test-term '(lambda (x y z) (+ x y (lambda (a b c) (+ a b c z)))))

(def curried-term
  '(lambda x (lambda y (lambda z (+ x y (lambda a (lambda b (lambda c (+ a b c z)))))))))

(def nameless-term
  `(lambda nil
     (lambda nil
       (lambda nil
         (+ ,(geb.lambda.experimental:make-index :depth 2)
            ,(geb.lambda.experimental:make-index :depth 1)
            (lambda nil
              (lambda nil
                (lambda nil
                  (+ ,(geb.lambda.experimental:make-index :depth 2)
                     ,(geb.lambda.experimental:make-index :depth 1)
                     ,(geb.lambda.experimental:make-index :depth 0)
                     ,(geb.lambda.experimental:make-index :depth 3))))))))))

(define-test curry-expands-properly
  :parent geb.lambda.experimental
  (is equalp (geb.lambda.experimental:curry-lambda test-term)
              curried-term))

(define-test nameless-works-properly
  :parent geb.lambda.experimental
  (is equalp (geb.lambda.experimental:nameless curried-term) nameless-term))

(define-test mixin-works-well
  :parent geb.lambda.experimental
  (is obj-equalp
      (geb.lambda.spec:pair so1 so1 so1 so1)
      (geb.lambda.spec:pair so1 so1 so1 so1)))
