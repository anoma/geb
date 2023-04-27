(in-package :geb.poly.main)

(defmethod gapply ((morphism poly:<poly>) object)
  "My main documentation can be found on [GAPPLY][generic-function]

I am the [GAPPLY][generic-function] for [POLY:\\<POLY\\>][class], the
OBJECT that I expect is of type NUMBER. [GAPPLY][generic-function] reduces down to
ordinary common lisp expressions rather straight forwardly


Some examples of me are

```lisp
(in-package :geb.poly)

POLY> (gapply (if-zero (- ident ident 1) 10 ident) 5)
5 (3 bits, #x5, #o5, #b101)

POLY> (gapply (if-zero (- ident ident) 10 ident) 5)
10 (4 bits, #xA, #o12, #b1010)

POLY> (gapply (- (* 2 ident ident) (* ident ident)) 5)
25 (5 bits, #x19, #o31, #b11001)
```
"
  (etypecase-of poly:poly morphism
    (poly:ident object)
    (integer    (error "never happens"))
    (poly:compose
     (gapply (mcar morphism)
             (gapply (mcadr morphism) object)))
    (poly:+
     (+ (gapply (mcar morphism) object)
        (gapply (mcadr morphism) object)))
    (poly:*
     (* (gapply (mcar morphism) object)
        (gapply (mcadr morphism) object)))
    (poly:/
     (/ (gapply (mcar morphism) object)
        (gapply (mcadr morphism) object)))
    (poly:-
     (- (gapply (mcar morphism) object)
        (gapply (mcadr morphism) object)))
    (poly:mod
     (mod  (gapply (mcar morphism) object)
           (gapply (mcadr morphism) object)))
    (poly:if-zero (if (zerop (gapply (predicate morphism) object))
                      (gapply (then morphism) object)
                      (gapply (else morphism) object)))
    (poly:if-lt
     (if (< (gapply (mcar morphism) object)
            (gapply (mcadr morphism) object))
         (gapply (then morphism) object)
         (gapply (else morphism) object)))))

(defmethod gapply ((morphism integer) object)
"My main documentation can be found on [GAPPLY][generic-function]

I am the [GAPPLY][generic-function] for INTEGERs, the
OBJECT that I expect is of type NUMBER. I simply return myself.

Some examples of me are

```lisp
(in-package :geb.poly)

POLY> (gapply 10 5)
10 (4 bits, #xA, #o12, #b1010)
```"
  (declare (ignore object))
  morphism)
