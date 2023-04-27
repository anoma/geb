(in-package :geb-test)

(define-test geb :parent geb-test-suite)

(def prod16
  (let* ((prod4 (prod (alias bool (prod so0 so1)) (prod so0 so1)))
         (prod8 (prod prod4 prod4)))
    (prod prod8 prod8)))

(def coprod16
  (let* ((coprod4 (coprod (alias bool (coprod so0 so1)) (coprod so0 so1)))
         (coprod8 (coprod coprod4 coprod4)))
    (coprod coprod8 coprod8)))


(def mixprod16
  (let* ((coprod4 (coprod (alias bool (coprod so0 so1)) (coprod so0 so1)))
         (prod8 (prod coprod4 coprod4)))
    (coprod prod8 prod8)))

(def prod32 (prod prod16 prod16))

(def coprod32 (coprod coprod16 coprod16))

(def mixprod32 (coprod mixprod16 mixprod16))

(def test-value
  (cleave (<-left so1 so1)
          (commutes so1 so1)
          (<-left so1 so1)
          (<-left so1 so1)
          (<-left so1 so1)
          (<-left so1 so1)
          (<-left so1 so1)
          (<-left so1 so1)
          (<-left so1 so1)
          (<-left so1 so1)
          (<-left so1 so1)
          (<-left so1 so1)
          (<-left so1 so1)
          (<-left so1 so1)
          (<-left so1 so1)
          (<-left so1 so1)
          (<-left so1 so1)
          (<-left so1 so1)
          (<-left so1 so1)
          (commutes so1 so1)))

(def test-value-expansion
  '((<-LEFT S-1 S-1) ((<-RIGHT S-1 S-1) (<-LEFT S-1 S-1)) (<-LEFT S-1 S-1)
    (<-LEFT S-1 S-1) (<-LEFT S-1 S-1) (<-LEFT S-1 S-1) (<-LEFT S-1 S-1)
    (<-LEFT S-1 S-1) (<-LEFT S-1 S-1) (<-LEFT S-1 S-1) (<-LEFT S-1 S-1)
    (<-LEFT S-1 S-1) (<-LEFT S-1 S-1) (<-LEFT S-1 S-1) (<-LEFT S-1 S-1)
    (<-LEFT S-1 S-1) (<-LEFT S-1 S-1) (<-LEFT S-1 S-1) (<-LEFT S-1 S-1)
    (<-RIGHT S-1 S-1) (<-LEFT S-1 S-1)))

(define-test printer-works-as-expected
  :parent geb
  (is equalp (read-from-string (format nil "~A" test-value)) test-value-expansion)
  (is equalp (read-from-string (format nil "~A" prod16))
      '(× (× (× BOOL S-0 S-1) BOOL S-0 S-1) (× BOOL S-0 S-1) BOOL S-0 S-1)))

(define-test dom-and-codom
  :parent geb
  (is obj-equalp so1 (dom (pair (->left so1 so1)
                                (->left so1 so1)))
      "Checking the dom of pair")
  (is obj-equalp
      (prod geb-bool:bool
            geb-bool:bool)
      (codom (pair (->left geb-bool:false-obj geb-bool:true-obj)
                   (->left geb-bool:false-obj geb-bool:true-obj)))
      "Checking the codom of pair")
  (is obj-equalp
      (dom (<-left so1 geb-bool:bool))
      (prod so1 geb-bool:bool)
      "checking dom of projection")
  (is obj-equalp
      (dom (distribute geb-bool:bool so1 so1))
      (prod geb-bool:bool (coprod so1 so1))
      "checking dom of distribution")
  (is obj-equalp
      (codom (distribute geb-bool:bool so1 so1))
      (coprod (prod geb-bool:bool so1)
              (prod geb-bool:bool so1))
      "checking codom of distribution"))


(define-test curry
  :parent geb
  (of-type substmorph (curry (<-left geb-bool:bool geb-bool:bool)))
  ;; may be typing this a bit too strictly
  (of-type comp (curry (<-left geb-bool:bool so1)))
  (is obj-equalp
      (dom (geb:curry geb-bool:and))
      geb-bool:bool))


(define-test geb-trans :parent geb)

(def test-morph-2 (<-left so1 geb-bool:bool))

(def test-poly-2 (geb:to-poly test-morph-2))

(def test-circuit-2 (geb:to-circuit test-morph-2 :tc_2))

(define-test vampir-test-2
  :parent geb-trans
  (of-type geb.vampir.spec:alias test-circuit-2))


(define-test geb-interpreter :parent geb)

;; PLEASE FUZZ THIS!
(define-test interpret-bool :parent geb-interpreter
  (is
   obj-equalp
   (gapply geb-bool:and
           (list (left so1)
                 (left so1)))
   (left so1))

  (is
   obj-equalp
   (gapply geb-bool:and
           (list (left so1)
                 (right so1)))
   (left so1))

  (is
   obj-equalp
   (gapply geb-bool:and
           (list (right so1)
                 (right so1)))
   (right so1))

  (is
   obj-equalp
   (gapply geb-bool:not
           (left so1))
   (right so1))

  (is
   obj-equalp
   (gapply geb-bool:not
           (right so1))
   (left so1)))

(define-test gapply-bool-id
  :parent geb-trans
  (is obj-equalp
      (right so1)
      (geb.generics:gapply
       (uncurry (coprod so1 so1) (coprod so1 so1)
                (geb.lambda.trans:compile-checked-term
                 (list (coprod so1 so1))
                 (geb.lambda:lamb (coprod so1 so1)
                                  (geb.lambda:index 0)) ))
       (list (left so1) (right so1))))
  (is obj-equalp
      (right so1)
      (geb.generics:gapply
       (uncurry (coprod so1 so1) (coprod so1 so1)
                (geb.lambda.trans:compile-checked-term
                 (list (coprod so1 so1))
                 (geb.lambda:lamb (coprod so1 so1)
                                  (geb.lambda:index 0)) ))
       (list (right so1) (right so1))))
  (is obj-equalp
      (left so1)
      (geb.generics:gapply
       (uncurry (coprod so1 so1) (coprod so1 so1)
                (geb.lambda.trans:compile-checked-term
                 (list (coprod so1 so1))
                 (geb.lambda:lamb (coprod so1 so1)
                                  (geb.lambda:index 0)) ))
       (list (left so1) (left so1))))
  (is obj-equalp
      (left so1)
      (geb.generics:gapply
       (uncurry (coprod so1 so1) (coprod so1 so1)
                (geb.lambda.trans:compile-checked-term
                 (list (coprod so1 so1))
                 (geb.lambda:lamb (coprod so1 so1)
                                  (geb.lambda:index 0)) ))
       (list (right so1) (left so1)))))
