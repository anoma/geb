(in-package :geb-test)

(def-suite geb.lambda
    :description "Tests the geb.lambda package")

(in-suite geb.lambda)


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

(test curry-expands-properly
  (is (equalp (geb.lambda:curry-lambda test-term)
              curried-term)))

(test nameless-works-properly
  (is (equalp nameless-term (geb.lambda:nameless curried-term))))

(test compile-nil-context
  (is (equalp (geb.lambda-conversion:stlc-ctx-to-mu nil)
              geb:so1)))
