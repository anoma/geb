(in-package :geb-test)

(define-test geb.lambda
  :parent geb-test-suite)

(def unit-term
  (lambda:unit))

(def pair-of-units-term
  (lambda:pair unit-term unit-term))

(def fst-pair-of-units-term
  (lambda:fst pair-of-units-term))

(def snd-pair-of-units-term
  (lambda:snd pair-of-units-term))

(def right-inj
  (lambda:right so0 unit-term))

(def left-inj
  (lambda:left so0 unit-term))

(def pair-of-injs
  (lambda:pair right-inj
               left-inj))

(def on-l-r-term
  (lambda:case-on left-inj right-inj right-inj))

(def so01-coprod
    (coprod so0 so1))

(def so10-coprod
  (coprod so1 so0))

(def so1-prod
  (prod so1 so1))

(def lambterm
  (lambda:lamb so1-prod unit-term))

(def appterm
  (lambda:app lambterm pair-of-units-term))

(def context-list
  (list so1 so0 so01-coprod (geb.lambda.main:fun-type so0 so1)))

(define-test type-of-unit-term-test
  :parent geb.lambda
  (is obj-equalp
      so1
      (lambda:type-of-term nil unit-term)
      "type of unit is so1"))

(define-test type-of-pair-terms-test
  :parent geb.lambda
  (is obj-equalp
      so1-prod
      (lambda:type-of-term nil pair-of-units-term)
      "type of product of units is product of so1's")
  (is obj-equalp
      so1
      (lambda:type-of-term nil
                           (lambda:ltm (lambda:annotated-term nil pair-of-units-term)))
      "type of the left unit term is so1")
  (is obj-equalp
      so1
      (lambda:type-of-term nil
                           (lambda:rtm (lambda:annotated-term nil pair-of-units-term)))))

(define-test fst-unit-term-test
  :parent geb.lambda
  (is obj-equalp
      so1
      (lambda:type-of-term nil fst-pair-of-units-term)
      "type of the projection from (prod so1 so1) is so1")
  (is obj-equalp
      so1-prod
      (lambda:type-of-term nil
                           (lambda:term (lambda:annotated-term nil fst-pair-of-units-term)))
      "type of the term being projected is (prod so1 so1)"))

(define-test snd-unit-term-test
  :parent geb.lambda
  (is obj-equalp
      so1
      (lambda:type-of-term nil snd-pair-of-units-term)
      "type of the projection from (prod so1 so1) is so1")
  (is obj-equalp
      so1-prod
      (lambda:type-of-term nil
                           (lambda:term (lambda:annotated-term nil snd-pair-of-units-term)))
      "type of the term being projected is (prod so1 so1)"))

(define-test proj-term-test
  :parent geb.lambda
  (is obj-equalp
      (prod so01-coprod so10-coprod)
      (lambda:type-of-term nil pair-of-injs)
      "type of a pair of injection is a product of coproducts")
  (is obj-equalp
      so01-coprod
      (lambda:type-of-term nil
                           (lambda:ltm
                            (lambda:annotated-term nil pair-of-injs)))
      "test type annotation for the left term")
  (is obj-equalp
      so10-coprod
      (lambda:type-of-term nil
                           (lambda:rtm
                            (lambda:annotated-term nil pair-of-injs)))
      "test type annotation for the right term"))


(define-test casing-test
  :parent geb.lambda
  (is obj-equalp
      so01-coprod
      (lambda:type-of-term nil on-l-r-term)
      "type of term gotten from the casing")
  (is obj-equalp
      so01-coprod
      (lambda:type-of-term nil
                           (lambda:ltm
                            (lambda:annotated-term nil
                                                   on-l-r-term)))
      "test type annotation for left term")
  (is obj-equalp
      so01-coprod
      (lambda:type-of-term nil
                           (lambda:rtm
                            (lambda:annotated-term nil
                                                   on-l-r-term)))
      "test type annotation for right term")
  (is obj-equalp
      so10-coprod
      (lambda:type-of-term nil
                           (lambda:on
                            (lambda:annotated-term nil
                                                   on-l-r-term)))
      "type of annotated term supplied for the start of casing is that of the supplied coproduct"))

(define-test inl-test
  :parent geb.lambda
  (is obj-equalp
      so01-coprod
      (lambda:type-of-term nil right-inj)
      "type of injection is a coproduct")
  (is obj-equalp
      so1
      (lambda:type-of-term nil
                           (lambda:term
                            (lambda:annotated-term nil right-inj)))
      "test of the type of the annotated right term"))

(define-test inr-test
  :parent geb.lambda
  (is obj-equalp
      so10-coprod
      (lambda:type-of-term nil left-inj)
      "type of injection is a coproduct")
  (is obj-equalp
      so1
      (lambda:type-of-term nil
                           (lambda:term
                            (lambda:annotated-term nil left-inj)))
      "test of the type of the annotated left term"))

(define-test lamb-test
  :parent geb.lambda
  (is obj-equalp
      (so-hom-obj so1-prod so1)
      (lambda:type-of-term nil
                           lambterm)
      "test type of lambda term")
  (is obj-equalp
      so1
      (lambda:type-of-term nil
                           (lambda:term
                            (lambda:annotated-term nil
                                                   lambterm)))
      "test type of annotated term for the lambda term"))

(define-test app-test
  :parent geb.lambda
  (is obj-equalp
      so1
      (lambda:type-of-term nil (lambda:app lambterm pair-of-units-term))
      "type of function application term")
  (is obj-equalp
      (so-hom-obj so1-prod so1)
      (lambda:type-of-term nil
                           (lambda:fun
                            (lambda:annotated-term nil
                                                   appterm)))
      "test annotated fun term")
  (is obj-equalp
      so1-prod
      (lambda:type-of-term nil
                           (lambda:term
                            (lambda:annotated-term nil
                                                   appterm)))))

(define-test index-tests
  :parent geb.lambda
  (is obj-equalp
      (so-hom-obj so0 so1)
      (lambda:type-of-term context-list (lambda:index 0)))
  (is obj-equalp
      so01-coprod
      (lambda:type-of-term context-list (lambda:index 1)))
  (is obj-equalp
      so0
      (lambda:type-of-term context-list (lambda:index 2)))
  (is obj-equalp
      so1
      (lambda:type-of-term context-list (lambda:index 3))))


(define-test absurd-index-test
  :parent geb.lambda
  (is obj-equalp
      so0
      (lambda:type-of-term
       context-list
       (lambda:term (lambda:annotated-term context-list
                                           (lambda:absurd so1 (lambda:index 2)))))))

(define-test exp-hom-test
  :parent geb.lambda
  (is obj-equalp
      (so-hom-obj (coprod so0 (so-hom-obj so1 so1))
                  (prod so1 (so-hom-obj so0 so1)))
      (lambda:type-of-term
       (list so0 so1)
       (lambda:fun
        (lambda:app (lambda:lamb
                     (coprod so0 (geb.lambda.main:fun-type so0 so1))
                     (lambda:pair
                      unit-term
                      (lambda:lamb so1
                                   (lambda:lamb so0
                                                (lambda:index 0)))))
                    (lambda:right so0
                                  (lambda:lamb so1 unit-term)))))))

