(in-package :geb.extension.spec)

;; Sadly no polynomial category to extend ☹
(defclass common-sub-expression (direct-pointwise-mixin meta-mixin cat-morph)
  ((obj :initarg :obj
        :accessor obj)
   (name :initarg :name
         :accessor name))
  (:documentation
   "I represent common sub-expressions found throughout the code.

I implement a few categorical extensions. I am a valid
[CAT-MORPH][class] along with fulling the interface for the
[GEB.POLY.SPEC:<POLY>] category.

The name should come from an algorithm that automatically fines common
sub-expressions and places the appropriate names."))


(defclass opaque (cat-obj meta-mixin)
  ((name :initarg :name :accessor name)
   (code :initarg :code :accessor code))
  (:documentation
   "I represent an object where we want to hide the implementation
details of what kind of [GEB:SUBSTOBJ][type] I am."))

(defclass reference (cat-obj cat-morph direct-pointwise-mixin meta-mixin)
  ((name :initarg :name :accessor name))
  (:documentation
   "I represent a reference to an [OPAQUE][class] identifier."))

(defclass opaque-morph (cat-morph meta-mixin)
  ((code :initarg :code
         :accessor code
         :documentation "the code that represents the underlying morphsism")
   (dom :initarg :dom
        :accessor dom
        :documentation "The dom of the opaque morph")
   (codom :initarg :codom
          :accessor codom
          :documentation "The codom of the opaque morph"))
  (:documentation
   "This represents a morphsim where we want to deal with an
[OPAQUE][class] that we know intimate details of"))

(defun make-common-sub-expression (&key obj name)
  (make-instance 'common-sub-expression :obj obj :name name))

(defun reference (name)
  (make-instance 'reference :name name))

(defun opaque-morph (code &key (dom (dom code)) (codom (codom code)))
  (make-instance 'opaque-morph :code code :dom dom :codom codom))

(defun opaque (name code)
  (make-instance 'opaque :name name :code code))

(defclass <natobj> (direct-pointwise-mixin meta-mixin cat-obj cat-morph) ()
  (:documentation "the class corresponding to [NATOBJ], the extension of
[SUBSTOBJ][class] adding to Geb bit representation of natural numbers." ))

(deftype natobj ()
  '(or nat-width))

(defclass <natmorph> (direct-pointwise-mixin meta-mixin cat-morph) ()
  (:documentation "the class corresponding to [NATMORPH], the extension of
[SUBSTMORPH][class] adding to Geb basic operations on bit representations
of natural numbers"))

(deftype natmorph ()
  '(or nat-add nat-inj nat-mult nat-sub nat-div nat-const nat-concat
       one-bit-to-bool nat-decompose nat-eq nat-lt nat-mod))

(defclass nat-width (<natobj>)
  ((num :initarg :num
        :accessor num
        :documentation ""))
  (:documentation
   "the [NAT-WIDTH][class] object. Takes a non-zero natural
number [NUM] and produces an object standing for cardinality
2^([NUM]) corresponding to [NUM]-wide bit number.

The formal grammar of [NAT-WIDTH][NAT-WIDTH class] is

```lisp
(nat-width num)
```

where [NAT-WIDTH][class] is the constructor, [NUM] the choice
of a natural number we want to be the width of the bits we
are to consder."))

(-> nat-width (fixnum) nat-width)
(defun nat-width (num)
  (values
   (make-instance 'nat-width :num num)))

(defclass nat-add (<natmorph>)
  ((num :initarg :num
        :accessor num
        :documentation ""))
  (:documentation "Given a natural number [NAT] greater than 0, gives a morphsm
(nat-add num) : (nat-mod num) x (nat-mod num) -> (nat-mod num) representing
floored addition of two bits of length n.

The formal grammar of [NAT-ADD][class] is

```lisp
(nat-add num)
``` "))

(defclass nat-mult (<natmorph>)
  ((num :initarg :num
        :accessor num
        :documentation ""))
  (:documentation "Given a natural number [NAT] greater than 0, gives a morphsm
(nat-mult num) : (nat-mod num) x (nat-mod num) -> (nat-mod n) representing floored
multiplication in natural numbers modulo n.

The formal grammar of [NAT-MULT][class] is

```lisp
(nat-mult num)
``` "))

(defclass nat-sub (<natmorph>)
  ((num :initarg :num
        :accessor num
        :documentation ""))
  (:documentation "Given a natural number [NAT] greater than 0, gives a morphsm
(nat-sub sum) : (nat-mod num) x (nat-mod num) -> (nat-mod num) representing
floored subtraction of two bits of length n.

The formal grammar of [NAT-SUB][class] isy

```lisp
(nat-sub num)
``` "))

(defclass nat-div (<natmorph>)
  ((num :initarg :num
        :accessor num
        :documentation ""))
  (:documentation "Given a natural number [NAT] greater than 0, gives a morphsm
(nat-div num) : (nat-mod num) x (nat-mod num) -> (nat-mod num) representing
floored division in natural numbers modulo n.

The formal grammar of [NAT-DIV][class] is

```lisp
(nat-div num)
``` "))

(defclass nat-const (<natmorph>)
  ((num :initarg :num
        :accessor num
        :documentation "")
   (pos :initarg :pos
        :accessor pos
        :documentation ""))
  (:documentation "Given a NUM natural number, gives a morphsm
(nat-const num pos) : so1 -> (nat-width num).

That is, chooses the POS natural number as a NUM-wide bit number

The formal grammar of [NAT-ADD][class] is

```lisp
(nat-const num pos)
``` "))

(defclass nat-inj (<natmorph>)
  ((num :initarg :num
        :accessor num
        :documentation ""))
  (:documentation "Given a nutural number [NAT] presents a [NAT]-wide bit number
as a ([NAT] + 1)-wide bit number via injecting.

The formal grammar of [NAT-INJ][class] is

```lisp
(nat-inj num)
```

In Geb, the injection presents itself as a morphism
(nat-width num) -> (nat-width (1 + num))"))

(defclass nat-concat (<natmorph>)
  ((num-left :initarg :num-left
             :accessor num-left
             :documentation "")
   (num-right :initarg :num-right
              :accessor num-right
              :documentation ""))
  (:documentation "Given two natural numbers of bit length n and m, concatenates
them in that order giving a bit of length n + m.

The formal grammar of [NAT-CONCAT][class] is

```lisp
(nat-concat num-left num-right)
```

In Geb this corresponds to a morphism
(nat-width num-left) x (nat-width num-right) -> (nat-width (n + m))

For a translation to SeqN simply take x of n width and y of m with and
take x^m + y"))

(defclass one-bit-to-bool (<natmorph>)
  ()
  (:documentation "A map nat-width 1 -> bool sending #*0 to
false and #*1 to true"))

(defclass nat-decompose (<natmorph>)
  ((num :initarg :num
        :accessor num
        :documentation ""))
  (:documentation "Morphism nat-width n -> (nat-width 1) x (nat-width (1- n))
splitting a natural number into the last and all but last collection of bits"))

(defclass nat-eq (<natmorph>)
  ((num :initarg :num
        :accessor num
        :documentation ""))
  (:documentation "Morphism nat-width n x nat-width n -> bool
which evaluated to true iff both inputs are the same"))

(defclass nat-lt (<natmorph>)
  ((num :initarg :num
        :accessor num
        :documentation ""))
  (:documentation "Morphism nat-width n x nat-width n -> bool
which evaluated to true iff the first input is less than the second"))

(defclass nat-mod (<natmorph>)
  ((num :initarg :num
        :accessor num
        :documentation ""))
  (:documentation "Morphism nat-width n x nat-width n -> nat-width n
which takes a modulo of the left projection of a pair by the second
projection of a pari"))

(defun nat-add (num)
  (values
   (make-instance 'nat-add :num num)))


(defun nat-mult (num)
  (values
   (make-instance 'nat-mult :num num)))


(defun nat-sub (num)
  (values
   (make-instance 'nat-sub :num num)))


(defun nat-div (num)
  (values
   (make-instance 'nat-div :num num)))


(defun nat-const (num pos)
  (values
   (make-instance 'nat-const :num num :pos pos)))


(defun nat-inj (num)
  (values
   (make-instance 'nat-inj :num num)))


(defun nat-concat (num-left num-right)
  (values
   (make-instance 'nat-concat :num-left num-left :num-right num-right)))

(defun one-bit-to-bool ()
  (make-instance 'one-bit-to-bool))

(defparameter *one-bit-to-bool*
  (make-instance 'one-bit-to-bool))

(def one-bit-to-bool *one-bit-to-bool*)

(defun nat-decompose (num)
  (make-instance 'nat-decompose :num num))

(defun nat-eq (num)
  (make-instance 'nat-eq :num num))

(defun nat-lt (num)
  (make-instance 'nat-lt :num num))

(defun nat-mod (num)
  (make-instance 'nat-mod :num num))






