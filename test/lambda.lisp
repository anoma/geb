(in-package :geb-test)

(define-test geb.lambda :parent geb-test-suite)

(def test-term '(lambda (x y z) (+ x y (lambda (a b c) (+ a b c z)))))

(def curried-term
  '(lambda x (lambda y (lambda z (+ x y (lambda a (lambda b (lambda c (+ a b c z)))))))))

(def nameless-term
  `(lambda nil
     (lambda nil
       (lambda nil
         (+ ,(geb.lambda:make-index :depth 2)
            ,(geb.lambda:make-index :depth 1)
            (lambda nil
              (lambda nil
                (lambda nil
                  (+ ,(geb.lambda:make-index :depth 2)
                     ,(geb.lambda:make-index :depth 1)
                     ,(geb.lambda:make-index :depth 0)
                     ,(geb.lambda:make-index :depth 3))))))))))

(define-test curry-expands-properly
  :parent geb.lambda
  (is equalp (geb.lambda:curry-lambda test-term)
              curried-term))

(define-test nameless-works-properly
  :parent geb.lambda
  (is equalp (geb.lambda:nameless curried-term) nameless-term))
