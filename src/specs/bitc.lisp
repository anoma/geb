(in-package #:geb.bitc.spec)

(deftype bitc ()
  `(or compose fork parallel swap one zero ident drop branch))

(defclass <bitc> (geb.mixins:direct-pointwise-mixin cat-morph) ())

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructor Morphisms for Bits (Objects are just natural numbers)
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass compose (<bitc>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation "composes the MCAR and the MCADR"))

(defclass fork (<bitc>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation ""))
  (:documentation "Copies the MCAR of length n onto length 2*n by copying its
inputs (MCAR)."))

(defclass parallel (<bitc>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation
   "
```lisp
(parallel x y)
```

constructs a [PARALLEL][class] term where the [MCAR] is `x` and the
[MCADR] is `y`,

where if

```
x : a → b,          y : c → d
-------------------------------
(parallel x y) : a + c → b + d
```

then the [PARALLEL][class] will return a function from a and c to b
and d where the [MCAR] and [MCADR] run on subvectors of the input."))

(defclass swap (<bitc>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation
   "
```lisp
(swap n m)
```

binds the [MCAR] to n and [MCADR] to m, where if the input
vector is of length `n + m`, then it swaps the bits, algebraically we
view it as

```lisp
(swap n m) : #*b₁...bₙbₙ₊₁...bₙ₊ₘ → #*bₙ₊₁...bₘ₊ₙb₁...bₙ
```"))

(defclass one (<bitc>)
  ()
  (:documentation
   "[ONE][class] represents the map from 0 onto 1 producing a vector
   with only 1 in it."))

(defclass zero (<bitc>)
  ()
  (:documentation
   "[ZERO] map from 0 onto 1 producing a vector with only 0 in
   it."))

(defclass ident (<bitc>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation ""))
  (:documentation
   "[IDENT] represents the identity"))

(defclass drop (<bitc>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation ""))
  (:documentation
   "[DROP] represents the unique morphism from n to 0."))

(defclass branch (<bitc>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation
   "
```lisp
(branch x y)
```

constructs a [BRANCH][class] term where the [MCAR] is `x` and the
[MCADR] is `y`,

where if

```
x : a → b,          y : a → b
-------------------------------
(branch x y) : 1+a → b
```

then the [BRANCH] will return a function on the type `1 + a`, where the
1 represents a bit to branch on. If the first bit is `0`, then the
[MCAR] is ran, however if the bit is `1`, then the [MCADR] is ran."))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructors
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defmacro make-multi (constructor)
  `(defun ,constructor (mcar mcadr &rest args)
     ,(format nil "Creates a multiway constructor for [~A]" constructor)
     (reduce (lambda (x y)
               (make-instance ',constructor :mcar x :mcadr y))
             (list* mcar mcadr args)
             :from-end t)))

(make-multi parallel)
(make-multi compose)

(defun fork (mcar)
  "FORK ARG1"
  (make-instance 'fork :mcar mcar))

(defun swap (mcar mcadr)
  "swap ARG1 and ARG2"
  (make-instance 'swap :mcar mcar :mcadr mcadr))

(serapeum:def one
  (make-instance 'one))

(serapeum:def zero
  (make-instance 'zero))

(defun ident (mcar)
  "ident ARG1"
  (make-instance 'ident :mcar mcar))

(defun drop (mcar)
  "drop ARG1"
  (make-instance 'drop :mcar mcar))

(defun branch (mcar mcadr)
  "branch with ARG1 or ARG2"
  (make-instance 'branch :mcar mcar :mcadr mcadr))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Pattern Matching
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Ι don't do multi way pattern matching yet :(
(make-pattern compose  mcar mcadr)
(make-pattern fork     mcar)
(make-pattern parallel mcar mcadr)
(make-pattern swap     mcar mcadr)
(make-pattern ident    mcar)
(make-pattern drop     mcar)
(make-pattern branch   mcar mcadr)
(make-pattern one)
(make-pattern zero)
