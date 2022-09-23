(in-package :geb-test)

(def-suite geb
    :description "Tests the geb package")

(in-suite geb)

(def prod16
  (let* ((prod4 (prod (alias bool (prod so0 so1)) (prod so0 so1)))
         (prod8 (prod prod4 prod4)))
    (prod prod8 prod8)))


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

(test printer-works-as-expected
  (is (equalp (read-from-string (format nil "~A" test-value))
              '((<-LEFT S-1 S-1) ((<-RIGHT S-1 S-1) (<-LEFT S-1 S-1)) (<-LEFT S-1 S-1)
                (<-LEFT S-1 S-1) (<-LEFT S-1 S-1) (<-LEFT S-1 S-1) (<-LEFT S-1 S-1)
                (<-LEFT S-1 S-1) (<-LEFT S-1 S-1) (<-LEFT S-1 S-1) (<-LEFT S-1 S-1)
                (<-LEFT S-1 S-1) (<-LEFT S-1 S-1) (<-LEFT S-1 S-1) (<-LEFT S-1 S-1)
                (<-LEFT S-1 S-1) (<-LEFT S-1 S-1) (<-LEFT S-1 S-1) (<-LEFT S-1 S-1)
                (<-RIGHT S-1 S-1) (<-LEFT S-1 S-1))))
  (is (equalp (read-from-string (format nil "~A" prod16))
              '(× (× (× BOOL (× s-0 s-1)) (× BOOL (× s-0 s-1)))
                  (× (× BOOL (× s-0 s-1)) (× BOOL (× s-0 s-1)))))))
