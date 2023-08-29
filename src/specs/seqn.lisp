(in-package #:geb.seqn.spec)

(deftype seqn ()
  '(or composition id fork-seq drop-nil remove-right remove-left drop-width
    inj-length-left inj-length-right inj-size branch-seq shift-front zero-bit
    one-bit parallel-seq seqn-add seqn-subtract seqn-multiply seqn-divide
    seqn-nat seqn-concat seqn-decompose seqn-lt seqn-eq))

(defclass <seqn> (geb.mixins:direct-pointwise-mixin cat-morph) ()
  (:documentation "Seqn is a category whose objects are finite sequences of natural numbers.
The n-th natural number in the sequence represents the bitwidth of the n-th
entry of the corresponding polynomial circuit

Entries are to be read as (x_1,..., x_n) and x_i is the ith entry
So car of a such a list will be the first entry, this is the dissimilarity
with the bit notation where newer entries come first in the list

We interpret pairs as actual pairs if entry is of width above 0
and drop it otherwise in the Vamp-Ir setup so that
ident bool x bool goes to
name x1 = x1
as (seqwidth bool) = (1, max(0, 0)) "))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Constructor Morphisms for Seqn
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(defclass composition (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation "composes the MCAR and MCADR morphisms
f : (a1,...,an) -> (b1,..., bm), g : (b1,...,bm) -> (c1, ..., ck)
compose g f : (a1,...,an) -> (c1,...,cn)"))

(defclass fork-seq (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation ""))
  (:documentation "Copies the MCAR of length n onto length 2*n by copying its
inputs (MCAR). fork (a1, ...., an) -> (a1,...,an, a1,..., an)"))

(defclass parallel-seq (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation "For f : (a1,..., an) -> (x1,...,xk), g : (b1,..., bm) -> (y1,...,yl)
parallel f g : (a1,...,an, b1,...bm) -> (x1,...,xk,y1,...,yl)"))

(defclass id (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation ""))
  (:documentation "For (x1,...,xn),
id (x1,...,xn) : (x1,....,xn) -> (x1,...,xn)"))

(defclass drop-nil (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation ""))
  (:documentation "Drops everything onto a 0 vector,
the terminal object drop-nil (x1, ..., xn) : (x1,...,xn) -> (0)"))

(defclass remove-right (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation ""))
  (:documentation "Removes an extra 0 entry from MCAR on the right
remove (x1,...,xn) : (x1,...,xn, 0) -> (x1,...,xn)"))

(defclass remove-left (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation ""))
  (:documentation "Removes an extra 0 entry from MCAR on the left
remove (x1,...,xn) : (0, x1,...,xn) -> (x1,...,xn)"))

(defclass drop-width (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation "Given two vectors of same length
but with the first ones of padded width, simply project the
core bits without worrying about extra zeroes at the end if they
are not doing any work
drop-width (x1,...,xn) (y1,...,yn) : (x1,...,xn) -> (y1,...,yn)
where xi > yi for each i and entries need to be in the image of the
evident injection map

In other words the constraints here are that on the enput ei corresponding to
xi bit entry the constraint is that range yi ei is true alongside
the usual (isrange xi ei) constraint

Another implementation goes through manual removal of extra bits (specifically
xi-yi bits) to the left after the decomposition by range xi"))

(defclass inj-length-left (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation "Taken an MCAR vector appends to it
MCADR list of vectors with arbitrary bit length by doing
nothing on the extra entries, i.e. just putting 0es there.
inj-lengh-left (x1,...,xn) (y1,...,ym): (x1,...,xn) -> (x1,...,xn, y1,...,yn)
Where 0es go in the place of ys or nothing if the injection is into
0-bits

So what gets injected is the left part"))

(defclass inj-length-right (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation "Taken an MCADR vector appends to it
MCAR list of vectors with arbitrary bit length by doing
nothing on the extra entries, i.e. just putting 0es there.
inj-lengh-right (x1,...,xn) (y1,...,ym): (y1,...,ym) -> (x1,...,xn, y1,...,yn)
Where 0es go in the place of xs. If any of yi's are 0-bit vectors, the injection
goes to nil entry on those parts

What gets injected is the right part"))


(defclass inj-size (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation "Taken an MCAR 1-long and injects it to
MCADR-wide slot wider than the original one by padding it with
0es on the left.
inj-size x1 m: (x1) -> (m)

Just a special case of drop-width"))

(defclass branch-seq (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation "Takes an
f: (x1,...,xn) -> c, g : (x1,...,xn) ->c and
produces branch-seq f g (1, x1,...,xn) -> c acting as
f on 0 entry and g on 1"))

(defclass zero-bit (<seqn>)
  ()
  (:documentation "Zero choice of a bit
zero: (0) -> (1)"))


(defclass one-bit (<seqn>)
  ()
  (:documentation "1 choice of a bit
one: (0) -> (1)"))

(defclass shift-front (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation "Takes an MCAR sequence of length at least
MCADR and shifts the MCADR-entry to the front
shift-front (x1,...,xn) k : (x1,...,xk,...,xn) -> (xk, x1,..., x_k-1, x_k+1,...,xn)"))

(defclass seqn-add (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation ""))
  (:documentation "Compiles to range-checked addition of natural numbers
of MCAR width. seqn-add n : (n, n) -> (n)"))

(defclass seqn-subtract (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation ""))
  (:documentation "Compiles to negative-checked subtraction of natural numbers
of MCAR width. seqn-subtract n : (n, n) -> (n)"))

(defclass seqn-multiply (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation ""))
  (:documentation "Compiles to range-checked multiplication of natural numbers
of MCAR width. seqn-multiply n : (n, n) -> (n)"))

(defclass seqn-divide (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation ""))
  (:documentation "Compiles to usual Vamp-IR floored multiplication of natural
numbers of MCAR width. seqn-divide n : (n, n) -> (n)"))

(defclass seqn-nat (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation "Produces a MCAR-wide representation of MCADR natural number
seqn-nat n m = (0) -> (n)"))

(defclass seqn-concat (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation "")
   (mcadr :initarg :mcadr
          :accessor mcadr
          :documentation ""))
  (:documentation "Takes a number of MCAR and MCADR width and produces a number
of MCAR + MCADR width by concatenating the bit representations. Using field
elements, this translates to multiplying the first input by 2 to the power of
MCADR and summing with the second entry
seqn-concat n m = (n, m) -> (n+m)"))

(defclass seqn-decompose (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation ""))
  (:documentation " The type signature of the morphism is
seqn-docompose n : (n) -> (1, (n - 1)) with the intended semantics being
that the morphism takes an n-bit integer and splits it, taking the leftmost
bit to the left part of the codomain and the rest of the bits to the righ"))

(defclass seqn-eq (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation ""))
  (:documentation " The type signature of the morphism is
seqn-eq n : (n, n) -> (1, 0) with the intended semantics being
that the morphism takes two n-bit integers and produces 1 iff they are
equal"))

(defclass seqn-lt (<seqn>)
  ((mcar :initarg :mcar
         :accessor mcar
         :documentation ""))
  (:documentation " The type signature of the morphism is
seqn-eq n : (n, n) -> (1, 0) with the intended semantics being
that the morphism takes two n-bit integers and produces 1 iff the first
one is less than the second"))

(serapeum:-> composition (<seqn> <seqn>) composition)
(defun composition (mcar mcadr)
  (values
   (make-instance 'composition :mcar mcar :mcadr mcadr)))

(serapeum:-> fork-seq (list) fork-seq)
(defun fork-seq (mcar)
  (values
   (make-instance 'fork-seq :mcar mcar)))

(serapeum:-> parallel-seq (<seqn> <seqn>) parallel-seq)
(defun parallel-seq (mcar mcadr)
  (values
   (make-instance 'parallel-seq :mcar mcar :mcadr mcadr)))

(serapeum:-> id (list) id)
(defun id (mcar)
  (values
   (make-instance 'id :mcar mcar)))

(serapeum:-> drop-nil (list) drop-nil)
(defun drop-nil (mcar)
  (values
   (make-instance 'drop-nil :mcar mcar)))

(serapeum:-> remove-right (list) remove-right)
(defun remove-right (mcar)
  (values
   (make-instance 'remove-right :mcar mcar)))

(serapeum:-> remove-left (list) remove-left)
(defun remove-left (mcar)
  (values
   (make-instance 'remove-left :mcar mcar)))

(serapeum:-> drop-width (list list) drop-width)
(defun drop-width (mcar mcadr)
  (values
   (make-instance 'drop-width :mcar mcar :mcadr mcadr)))

(serapeum:-> inj-length-left (list list) inj-length-left)
(defun inj-length-left (mcar mcadr)
  (values
   (make-instance 'inj-length-left :mcar mcar :mcadr mcadr)))

(serapeum:-> inj-length-right (list list) inj-length-right)
(defun inj-length-right (mcar mcadr)
  (values
   (make-instance 'inj-length-right :mcar mcar :mcadr mcadr)))

(serapeum:-> inj-size (fixnum fixnum) inj-size)
(defun inj-size (mcar mcadr)
  (values
   (make-instance 'inj-size :mcar mcar :mcadr mcadr)))

(serapeum:-> branch-seq (<seqn> <seqn>) branch-seq)
(defun branch-seq (mcar mcadr)
  (values
   (make-instance 'branch-seq :mcar mcar :mcadr mcadr)))

(serapeum:-> shift-front (list fixnum) shift-front)
(defun shift-front (mcar mcadr)
  (values
   (make-instance 'shift-front :mcar mcar :mcadr mcadr)))

(serapeum:def zero-bit
  (make-instance 'zero-bit))

(serapeum:def one-bit
  (make-instance 'one-bit))

(serapeum:-> seqn-add (fixnum) seqn-add)
(defun seqn-add (mcar)
  (values
   (make-instance 'seqn-add :mcar mcar)))

(serapeum:-> seqn-subtract (fixnum) seqn-subtract)
(defun seqn-subtract (mcar)
  (values
   (make-instance 'seqn-subtract :mcar mcar)))

(serapeum:-> seqn-multiply (fixnum) seqn-multiply)
(defun seqn-multiply (mcar)
  (values
   (make-instance 'seqn-multiply :mcar mcar)))

(serapeum:-> seqn-divide (fixnum) seqn-divide)
(defun seqn-divide (mcar)
  (values
   (make-instance 'seqn-divide :mcar mcar)))

(serapeum:-> seqn-nat (fixnum fixnum) seqn-nat)
(defun seqn-nat (mcar mcadr)
  (values
   (make-instance 'seqn-nat :mcar mcar :mcadr mcadr)))

(serapeum:-> seqn-concat (fixnum fixnum) seqn-concat)
(defun seqn-concat (mcar mcadr)
  (values
   (make-instance 'seqn-concat :mcar mcar :mcadr mcadr)))

(serapeum:-> seqn-decompose (fixnum) seqn-decompose)
(defun seqn-decompose (mcar)
  (values
   (make-instance 'seqn-decompose :mcar mcar)))

(serapeum:-> seqn-eq (fixnum) seqn-eq)
(defun seqn-eq (mcar)
  (values
   (make-instance 'seqn-eq :mcar mcar)))

(serapeum:-> seqn-lt (fixnum) seqn-lt)
(defun seqn-lt (mcar)
  (values
   (make-instance 'seqn-lt :mcar mcar)))

(make-pattern composition mcar mcadr)
(make-pattern id mcar)
(make-pattern fork-seq mcar)
(make-pattern drop-nil mcar)
(make-pattern parallel-seq mcar mcadr)
(make-pattern remove-right mcar)
(make-pattern remove-left mcar)
(make-pattern drop-width mcar mcadr)
(make-pattern inj-length-left mcar mcadr)
(make-pattern inj-length-right mcar mcadr)
(make-pattern inj-size mcar mcadr)
(make-pattern branch-seq mcar mcadr)
(make-pattern shift-front mcar mcadr)
(make-pattern zero-bit)
(make-pattern one-bit)
(make-pattern seqn-add)
(make-pattern seqn-subtract)
(make-pattern seqn-multiply)
(make-pattern seqn-divide)
(make-pattern seqn-nat)
(make-pattern seqn-concat)
(make-pattern seqn-decompose)
(make-pattern seqn-eq)
(make-pattern seqn-lt)

