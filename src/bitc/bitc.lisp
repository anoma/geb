(in-package :geb.bitc.main)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Domain and codomain definitions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmethod dom ((x <bitc>))
  "Gives the length of the bit vector the [\\<BITC\\>] moprhism takes"
  (typecase-of bitc x
    (compose  (dom (mcadr x)))
    (fork     (mcar x))
    (parallel (+ (dom (mcar x)) (dom (mcadr x))))
    (swap     (+ (mcar x) (mcadr x)))
    (one      0)
    (zero     0)
    (ident    (mcar x))
    (drop     (mcar x))
    (branch   (+ 1 (dom (mcar x))))
    (otherwise
      (subclass-responsibility x))))

(defmethod codom ((x <bitc>))
  "Gives the length of the bit vector the [\\<BITC\\>] morphism returns"
  (typecase-of bitc x
    (compose  (codom (mcar x)))
    (fork     (* 2 (mcar x)))
    (parallel (+ (codom (mcar x)) (codom (mcadr x))))
    (swap     (+ (mcar x) (mcadr x)))
    (one      1)
    (zero     1)
    (ident    (mcar x))
    (drop     0)
    (branch   (codom (mcar x)))
    (otherwise
      (subclass-responsibility x))))


(defmethod gapply ((morphism <bitc>) (object bit-vector))
  "My My main documentation can be found on [GAPPLY][generic-function]

I am the [GAPPLY][generic-function] for [\\<BITC\\>][class], the
OBJECT that I expect is of type NUMBER. [GAPPLY][generic-function]
reduces down to ordinary common lisp expressions rather straight
forwardly

```lisp
;; figure out the number of bits the function takes
GEB-TEST> (dom (to-bitc geb-bool:and))
2 (2 bits, #x2, #o2, #b10)
GEB-TEST> (gapply (to-bitc geb-bool:and) #*11)
#*1
GEB-TEST> (gapply (to-bitc geb-bool:and) #*10)
#*0
GEB-TEST> (gapply (to-bitc geb-bool:and) #*01)
#*0
GEB-TEST> (gapply (to-bitc geb-bool:and) #*00)
#*0
```"
  ;; use a non copying version of subseq some time
  (etypecase-of bitc morphism
    (compose  (gapply (mcar morphism)
                      (gapply (mcadr morphism) object)))
    (fork     (concatenate 'bit-vector object object))
    (ident    object)
    (one      #*1)
    (zero     #*0)
    (drop     #*)
    (swap
     (let ((n (mcar morphism)))
       (concatenate 'bit-vector (subseq object n) (subseq object 0 n))))
    (parallel
     (let* ((cx (dom (mcar morphism)))
            (inp1 (subseq object 0 cx))
            (inp2 (subseq object cx)))
       (concatenate 'bit-vector
                    (gapply (mcar morphism) inp1)
                    (gapply (mcadr morphism) inp2))))
    (branch
     (let ((without-first-bit (subseq object 1)))
       (if (zerop (bit object 0))
           (gapply (mcar morphism)  without-first-bit)
           (gapply (mcadr morphism) without-first-bit))))))

(defmethod gapply ((morphism <bitc>) (object list))
  "I am a helper gapply function, where the second argument for
[\\<BITC\\>] is a list. See the docs for the BIT-VECTOR version for
the proper one. We do allow sending in a list like so

```lisp
;; figure out the number of bits the function takes
GEB-TEST> (dom (to-bitc geb-bool:and))
2 (2 bits, #x2, #o2, #b10)
GEB-TEST> (gapply (to-bitc geb-bool:and) (list 1 1))
#*1
GEB-TEST> (gapply (to-bitc geb-bool:and) (list 1 0))
#*0
GEB-TEST> (gapply (to-bitc geb-bool:and) (list 0 1))
#*0
GEB-TEST> (gapply (to-bitc geb-bool:and) (list 0 0))
#*0
```
"
  (gapply morphism (coerce object 'bit-vector)))
