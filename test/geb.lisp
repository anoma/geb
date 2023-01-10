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
      (prod (obj geb-bool:bool)
            (obj geb-bool:bool))
      (codom (pair (->left so1 so1)
                   (->left so1 so1)))
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
  (of-type comp (curry (<-left geb-bool:bool so1))))
