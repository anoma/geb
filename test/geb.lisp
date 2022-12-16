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
  (mlist (<-left so1 so1)
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
  (is obj-equalp so1 (dom (pair (left-> so1 so1)
                                (left-> so1 so1))))
  (is obj-equalp so1 (dom (pair (left-> so1 so1)
                                (left-> so1 so1)))))
