(in-package #:geb.lambda.spec)

(defclass <stlc> (geb.mixins:direct-pointwise-mixin geb.mixins:meta-mixin geb.mixins:cat-obj) ()
  (:documentation
   "Class of untyped terms of simply typed lambda claculus. Given our
presentation, we look at the latter as a type theory spanned by empty,
unit types as well as coproduct, product, and function types."))

(deftype stlc ()
  "Type of untyped terms of [STLC][type]. Each class of a term has a slot for a type,
which can be filled by auxillary functions or by user. Types are
represented as [SUBSTOBJ][GEB.SPEC:SUBSTOBJ]."
  '(or absurd unit left right case-on pair fst snd lamb app index err
    plus times minus divide bit-choice lamb-eq lamb-lt))

;; New defgenerics

(defgeneric term (obj))
(defgeneric tdom (obj))
(defgeneric tcod (obj))
(defgeneric ttype (obj))
(defgeneric rty (obj))
(defgeneric lty (obj))
(defgeneric ltm (obj))
(defgeneric rtm (obj))
(defgeneric on (obj))
(defgeneric fun (obj))
(defgeneric pos (obj))
(defgeneric bitv (obj))


(defclass absurd (<stlc>)
  ((tcod :initarg :tcod
         :accessor tcod
         :documentation "An arbitrary type")
   (term :initarg :term
         :accessor term
         :documentation "A term of the empty type")
   (ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation
   "The [ABSURD][class] term provides an element of an arbitrary type
given a term of the empty type, denoted by [SO0][GEB.SPEC:SO0 class].
The formal grammar of [ABSURD][class] is

```lisp
(absurd tcod term)
```

where we possibly can include type information by

```lisp
(absurd tcod term :ttype ttype)
```

The intended semantics are: [TCOD] is a type whose term we want to
get (and hence a [SUBSTOBJ] [GEB.SPEC:SUBSTOBJ]) and [TERM] is a term
of the empty type (and hence an [STLC][type].

This corresponds to the elimination rule of the empty type. Namely,
given
$$\\Gamma \\vdash \\text{tcod : Type}$$ and
$$\\Gamma \\vdash \\text{term : so0}$$ one deduces
$$\\Gamma \\vdash \\text{(absurd tcod term) : tcod}$$"))

(-> absurd (cat-obj <stlc> &key (:ttype t)) absurd)
(defun absurd (tcod term &key (ttype nil))
  (values
   (make-instance 'absurd :tcod tcod :term term :ttype ttype)))

(defclass unit (<stlc>)
  ((ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation
   "The unique term of the unit type, the latter represented by
[SO1][GEB.SPEC:SO1 class]. The formal grammar of [UNIT][class] is

```lisp
(unit)
```

where we can optionally include type information by

```lisp
(unit :ttype ttype)
```

Clearly the type of [UNIT][class] is [SO1][GEB.SPEC:SO1 class] but here
we provide all terms untyped.

This grammar corresponds to the introduction rule of the unit type. Namely
$$\\Gamma \\dashv \\text{(unit) : so1}$$"))

(-> unit (&key (:ttype t)) unit)
(defun unit (&key (ttype nil))
  (values
   (make-instance 'unit :ttype ttype)))

(defclass left (<stlc>)
  ((rty :initarg :rty
        :accessor rty
        :documentation "Right argument of coproduct type")
   (term :initarg :term
         :accessor term
         :documentation "Term of the left argument of coproduct type")
   (ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation
   "Term of a coproduct type gotten by injecting into the left type of the coproduct. The formal grammar of
[LEFT][class] is

```lisp
(left rty term)
```

where we can include optional type information by

```lisp
(left rty term :ttype ttype)
```

The indended semantics are as follows: [RTY][generic-function] should
be a type (and hence a [SUBSTOBJ][GEB.SPEC:SUBSTOBJ]) and specify the
right part of the coproduct of the type [TTYPE][generic-function] of
the entire term. The term (and hence an [STLC][type]) we are injecting
is [TERM][generic-function].

This corresponds to the introduction rule of the coproduct type. Namely, given
$$\\Gamma \\dashv \\text{(ttype term) : Type}$$ and
$$\\Gamma \\dashv \\text{rty : Type}$$
with
$$\\Gamma \\dashv \\text{term : (ttype term)}$$ we deduce
$$\\Gamma \\dashv \\text{(left rty term) : (coprod (ttype term) rty)}$$
"))

(-> left (cat-obj <stlc> &key (:ttype t)) left)
(defun left (rty term &key (ttype nil))
  (values
   (make-instance 'left :rty rty :term term :ttype ttype)))

(defclass right (<stlc>)
  ((lty :initarg :lty
        :accessor lty
        :documentation "Left argument of coproduct type")
   (term :initarg :term
         :accessor term
         :documentation "Term of the right argument of coproduct type")
   (ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation
   "Term of a coproduct type gotten by injecting into the right type of
the coproduct. The formal grammar of [RIGHT][class] is

```lisp
(right lty term)
```

where we can include optional type information by

```lisp
(right lty term :ttype ttype)
```

The indended semantics are as follows: [LTY] should be a type (and
hence a [SUBSTOBJ][GEB.SPEC:SUBSTOBJ]) and specify the left part of
the coproduct of the type [TTYPE] of the entire term. The term (and
hence an [STLC][type]) we are injecting is [TERM].

This corresponds to the introduction rule of the coproduct type. Namely, given
$$\\Gamma \\dashv \\text{(ttype term) : Type}$$ and
$$\\Gamma \\dashv \\text{lty : Type}$$
with
$$\\Gamma \\dashv \\text{term : (ttype term)}$$ we deduce
$$\\Gamma \\dashv \\text{(right lty term) : (coprod lty (ttype term))}$$
"))

(-> right (cat-obj <stlc> &key (:ttype t)) right)
(defun right (lty term &key (ttype nil))
  (values
   (make-instance 'right :lty lty :term term :ttype ttype)))

(defclass case-on (<stlc>)
  ((on :initarg :on
       :accessor on
       :documentation "Term of coproduct type")
   (ltm :initarg :ltm
        :accessor ltm
        :documentation "Term in context of left argument of coproduct type")
   (rtm :initarg :rtm
        :accessor rtm
        :documentation "Term in context of right argument of coproduct type")
   (ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation
   "A term of an arbutrary type provided by casing on a coproduct term. The
formal grammar of [CASE-ON][class] is

```lisp
(case-on on ltm rtm)
```

where we can possibly include type information by

```lisp
(case-on on ltm rtm :ttype ttype)
```

The intended semantics are as follows: [ON] is a term (and hence an
[STLC][type]) of a coproduct type, and [LTM] and [RTM] terms (hence
also [STLC][type]) of the same type in the context of - appropriately
- (mcar (ttype on)) and (mcadr (ttype on)).

This corresponds to the elimination rule of the coprodut type. Namely, given
$$\\Gamma \\vdash \\text{on : (coprod (mcar (ttype on)) (mcadr (ttype on)))}$$
and
$$\\text{(mcar (ttype on))} , \\Gamma \\vdash \\text{ltm : (ttype ltm)}$$
, $$\\text{(mcadr (ttype on))} , \\Gamma \\vdash \\text{rtm : (ttype ltm)}$$
we get
$$\\Gamma \\vdash \\text{(case-on on ltm rtm) : (ttype ltm)}$$
Note that in practice we append contexts on the left as computation of
[INDEX][class] is done from the left. Otherwise, the rules are the same as in
usual type theory if context was read from right to left."))

(-> case-on (<stlc> <stlc> <stlc> &key (:ttype t)) case-on)
(defun case-on (on ltm rtm &key (ttype nil))
  (values
   (make-instance 'case-on :on on :ltm ltm :rtm rtm :ttype ttype)))

(defclass pair (<stlc>)
  ((ltm :initarg :ltm
        :accessor ltm
        :documentation "Term of left argument of the product type")
   (rtm :initarg :rtm
        :accessor rtm
        :documentation "Term of right argument of the product type")
   (ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation
   "A term of the product type gotten by pairing a terms of a left and right
parts of the product. The formal grammar of [PAIR][class] is

```lisp
(pair ltm rtm)
```

where we can possibly include type information by

```lisp
(pair ltm rtm :ttype ttype)
```

The intended semantics are as follows: [LTM] is a term (and hence an
[STLC][type]) of a left part of the product type whose terms we are
producing. [RTM] is a term (hence also [STLC][type])of the right part
of the product.

The grammar corresponds to the introdcution rule of the pair type. Given
$$\\Gamma \\vdash \\text{ltm : (mcar (ttype (pair ltm rtm)))}$$ and
$$\\Gamma \\vdash \\text{rtm : (mcadr (ttype (pair ltm rtm)))}$$ we have
$$\\Gamma \\vdash \\text{(pair ltm rtm) : (ttype (pair ltm rtm))}$$
"))

(-> pair (<stlc> <stlc> &key (:ttype t)) pair)
(defun pair (ltm rtm &key (ttype nil))
  (values
   (make-instance 'pair :ltm ltm :rtm rtm :ttype ttype)))

(defclass fst (<stlc>)
  ((term :initarg :term
         :accessor term
         :documentation "Term of product type")
   (ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation
   "The first projection of a term of a product type.
The formal grammar of [FST][class] is:

```lisp
(fst term)
```

where we can possibly include type information by

```lisp
(fst term :ttype ttype)
```

The indended semantics are as follows: [TERM][generic-function] is a
term (and hence an [STLC][type]) of a product type, to whose left part
we are projecting to.

This corresponds to the first projection function gotten by induction
on a term of a product type."))

(-> fst (<stlc> &key (:ttype t)) fst)
(defun fst (term &key (ttype nil))
  (values
   (make-instance 'fst :term term :ttype ttype)))

(defclass snd (<stlc>)
  ((term :initarg :term
         :accessor term
         :documentation "Term of product type")
   (ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
   (:documentation
    "The second projection of a term of a product type.
The formal grammar of [SND][class] is:

```lisp
(snd term)
```

where we can possibly include type information by

```lisp
(snd term :ttype ttype)
```

The indended semantics are as follows: [TERM][generic-function] is a
term (and hence an [STLC][type]) of a product type, to whose right
part we are projecting to.

This corresponds to the second projection function gotten by induction
on a term of a product type."))

(-> snd (<stlc> &key (:ttype t)) snd)
(defun snd (term &key (ttype nil))
  (values
   (make-instance 'snd :term term :ttype ttype)))

(defclass lamb (<stlc>)
  ((tdom :initarg :tdom
         :accessor tdom
         :type     list
         :documentation "Domain of the lambda term")
   (term :initarg :term
         :accessor term
         :documentation "Term of the codomain mapped to given a variable of tdom")
   (ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation
   "A term of a function type gotten by providing a term in the codomain
of the function type by assuming one is given variables in the
specified list of types. [LAMB][class] takes in the [TDOM][generic-function]
accessor a list of types - and hence of [SUBSTOBJ][class] - and in the
[TERM][generic-function] a term - and hence an [STLC][type]. The formal grammar
of [LAMB][class] is:

```lisp
(lamb tdom term)
```

where we can possibly include type information by

```lisp
(lamb tdom term :ttype ttype)
```

The intended semnatics are: [TDOM][generic-function] is a list of types (and
hence a list of [SUBSTOBJ][GEB.SPEC:SUBSTOBJ]) whose iterative product of
components form the domain of the function type. [TERM][generic-function]
is a term (and hence an [STLC][type]) of the codomain of the function type
gotten in the context to whom we append the list of the domains.

For a list of length 1, corresponds to the introduction rule of the function
type. Namely, given
$$\\Gamma \\vdash \\text{tdom : Type}$$ and
$$\\Gamma, \\text{tdom} \\vdash \\text{term : (ttype term)}$$ we have
$$\\Gamma \\vdash \\text{(lamb tdom term) : (so-hom-obj tdom (ttype term))}$$

For a list of length n, this coreesponds to the iterated lambda type, e.g.

```lisp
(lamb (list so1 so0) (index 0))
```

is a term of

```lisp
(so-hom-obj (prod so1 so0) so0)
```

or equivalently

```lisp
(so-hom-obj so1 (so-hom-obj so0 so0))
```

due to Geb's computational definition of the function type.

Note that [INDEX][class] 0 in the above code is of type [SO1][class].
So that after annotating the term, one gets

```lisp
LAMBDA> (ttype (term (lamb (list so1 so0)) (index 0)))
s-1
```

So the counting of indeces starts with the leftmost argument for
computational reasons. In practice, typing of [LAMB][class] corresponds with
taking a list of arguments provided to a lambda term, making it a context
in that order and then counting the index of the varibale. Type-theoretically,

$$\\Gamma \\vdash \\lambda \\Delta (index i)$$
$$\\Delta, \\Gamma \\vdash (index i)$$

So that by the operational semantics of [INDEX][class], the type of (index i)
in the above context will be the i'th element of the Delta context counted from
the left. Note that in practice we append contexts on the left as computation of
[INDEX][class] is done from the left. Otherwise, the rules are the same as in
usual type theory if context was read from right to left."))

(-> lamb (list <stlc> &key (:ttype t)) lamb)
(defun lamb (tdom term &key (ttype nil))
  (values
   (make-instance 'lamb :tdom tdom :term term :ttype ttype)))

(defclass app (<stlc>)
  ((fun :initarg :fun
        :accessor fun
        :documentation "Term of exponential type")
   (term :initarg :term
         :accessor term
         :type list
         :documentation "List of Terms of the domain")
   (ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation
   "A term of an arbitrary type gotten by applying a function of an iterated
function type with a corresponding codomain iteratively to terms in the
domains. [APP][class] takes as argument for the [FUN][generic-function] accessor
a function - and hence an [STLC][type] - whose function type has domain an
iterated [GEB:PROD][class] of [SUBSTOBJ][clas] and for the [TERM][generic-function]
a list of terms - and hence of [STLC][type] - matching the types of the
product. The formal grammar of [APP][class] is

```lisp
(app fun term)
```

where we can possibly include type information by

```lisp
(app fun term :ttype ttype)
```

The intended semantics are as follows:
[FUN][generic-function] is a term (and hence an [STLC][type]) of a coproduct
 type - say of (so-hom-obj (ttype term) y) - and [TERM][generic-function] is a
list of terms (hence also of [STLC][type]) with nth term in the list having the
n-th part of the function type.

For a one-argument term list, this corresponds to the elimination rule of the
function type. Given
$$\\Gamma \\vdash \\text{fun : (so-hom-obj (ttype term) y)}$$ and
$$\\Gamma \\vdash \\text{term : (ttype term)}$$ we get
$$\\Gamma \\vdash \\text{(app fun term) : y}$$

For several arguments, this corresponds to successive function application.
Using currying, this corresponds to, given

```
G ⊢ (so-hom-obj (A₁ × ··· × Aₙ₋₁) Aₙ)
G ⊢ f : (so-hom-obj (A₁ × ··· × Aₙ₋₁)
G ⊢ tᵢ : Aᵢ
```

then for each `i` less than `n` gets us

```lisp
G ⊢ (app f t₁ ··· tₙ₋₁) : Aₙ
```

Note again that i'th term should correspond to the ith element of the product
in the codomain counted from the left."))

(-> app (<stlc> list &key (:ttype t)) app)
(defun app (fun term &key (ttype nil))
  (values
    (make-instance 'app :fun fun :term term :ttype ttype)))

(defclass index (<stlc>)
  ((pos :initarg :pos
        :accessor pos
        :documentation "Position of type")
   (ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation
   "The variable term of an arbitrary type in a context. The formal
grammar of [INDEX][class] is

```lisp
(index pos)
```

where we can possibly include type information by

```lisp
(index pos :ttype ttype)
```

The intended semantics are as follows: [POS][generic-function] is a
natural number indicating the position of a type in a context.

This corresponds to the variable rule. Namely given a context
$$\\Gamma_1 , \\ldots , \\Gamma_{pos} , \\ldots , \\Gamma_k $$ we have

$$\\Gamma_1 , \\ldots , \\Gamma_k \\vdash \\text{(index pos) :} \\Gamma_{pos}$$

Note that we add contexts on the left rather than on the right contra classical
type-theoretic notation."))

(-> index (fixnum &key (:ttype t)) index)
(defun index (pos &key (ttype nil))
  (values
   (make-instance 'index :pos pos :ttype ttype)))

(defclass err (<stlc>)
  ((ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation
   "An error term of a type supplied by the user. The formal grammar of
[ERR][class] is

```lisp
(err ttype)
```

The intended semantics are as follows: [ERR][class] represents an error node
currently having no particular feedback but with functionality to be of an
arbitrary type. Note that this is the only STLC term class which does not
have [TTYPE][generic-function] a possibly empty accessor."))

(-> err (cat-obj) err)
(defun err (ttype)
  (values
   (make-instance 'err :ttype ttype)))

(defclass plus (<stlc>)
  ((ltm :initarg :ltm
        :accessor ltm
        :documentation "")
   (rtm :initarg :rtm
        :accessor rtm
        :documentation "")
   (ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation "A term representing syntactic summation of two bits
of the same width. The formal grammar of [PLUS] is

```lisp
(plus ltm rtm)
```

where we can possibly supply typing info by

```lisp
(plus ltm rtm :ttype ttype)
```

Note that the summation is ranged, so if the operation goes
above the bit-size of supplied inputs, the corresponding
Vamp-IR code will not verify."))

(defun plus (ltm rtm &key (ttype nil))
  (values
   (make-instance 'plus :ltm ltm :rtm rtm :ttype ttype)))

(defclass times (<stlc>)
  ((ltm :initarg :ltm
        :accessor ltm
        :documentation "")
   (rtm :initarg :rtm
        :accessor rtm
        :documentation "")
   (ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation "A term representing syntactic multiplication of two bits
of the same width. The formal grammar of [TIMES] is

```lisp
(times ltm rtm)
```

where we can possibly supply typing info by

```lisp
(times ltm rtm :ttype ttype)
```

Note that the multiplication is ranged, so if the operation goes
above the bit-size of supplied inputs, the corresponding
Vamp-IR code will not verify."))

(defun times (ltm rtm &key (ttype nil))
  (values
   (make-instance 'times :ltm ltm :rtm rtm :ttype ttype)))

(defclass minus (<stlc>)
  ((ltm :initarg :ltm
        :accessor ltm
        :documentation "")
   (rtm :initarg :rtm
        :accessor rtm
        :documentation "")
   (ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation "A term representing syntactic subtraction of two bits
of the same width. The formal grammar of [MINUS] is

```lisp
(minus ltm rtm)
```

where we can possibly supply typing info by

```lisp
(minus ltm rtm :ttype ttype)
```

Note that the subtraction is ranged, so if the operation goes
below zero, the corresponding Vamp-IR code will not verify."))

(defun minus (ltm rtm &key (ttype nil))
  (values
   (make-instance 'minus :ltm ltm :rtm rtm :ttype ttype)))

(defclass divide (<stlc>)
  ((ltm :initarg :ltm
        :accessor ltm
        :documentation "")
   (rtm :initarg :rtm
        :accessor rtm
        :documentation "")
   (ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation "A term representing syntactic division (floored)
of two bits of the same width. The formal grammar of [DIVIDE] is

```lisp
(minus ltm rtm)
```

where we can possibly supply typing info by

```lisp
(minus ltm rtm :ttype ttype)
```

"))

(defun divide (ltm rtm &key (ttype nil))
  (values
   (make-instance 'divide :ltm ltm :rtm rtm :ttype ttype)))

(defclass bit-choice (<stlc>)
  ((bitv :initarg :bitv
         :accessor bitv
         :documentation "")
   (ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation "A term representing a choice of a bit. The formal
grammar of [BIT-CHOICE] is

```lisp
(bit-choice bitv)
```

where we can possibly supply typing info by

```lisp
(bit-choice bitv :ttype ttype)
```

Note that the size of bits matter for the operations one supplies them
to. E.g. (plus (bit-choice #*1) (bit-choice #*00)) is not going to pass
our type-check, as both numbers ought to be of exact same bit-width."))

(defun bit-choice (bitv &key (ttype nil))
  (values
   (make-instance 'bit-choice :bitv bitv :ttype ttype)))

(defclass lamb-eq (<stlc>)
  ((ltm :initarg :ltm
        :accessor ltm
        :documentation "")
   (rtm :initarg :rtm
        :accessor rtm
        :documentation "")
   (ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation "lamb-eq predicate takes in two bit inputs of same bit-width
and gives true if they are equal and false otherwise. Note that for the usual
Vamp-IR code interpretations, that means that we associate true with left input
into bool and false with the right. Appropriately, in Vamp-IR the first branch
will be associated with the 0 input and teh second branch with 1."))

(defun lamb-eq (ltm rtm &key (ttype nil))
  (values
   (make-instance 'lamb-eq :ltm ltm :rtm rtm :ttype ttype)))

(defclass lamb-lt (<stlc>)
  ((ltm :initarg :ltm
        :accessor ltm
        :documentation "")
   (rtm :initarg :rtm
        :accessor rtm
        :documentation "")
   (ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation "lamb-lt predicate takes in two bit inputs of same bit-width
and gives true if ltm is less than rtm and false otherwise. Note that for the usual
Vamp-IR code interpretations, that means that we associate true with left input
into bool and false with the right. Appropriately, in Vamp-IR the first branch
will be associated with the 0 input and teh second branch with 1."))

(defun lamb-lt (ltm rtm &key (ttype nil))
  (values
   (make-instance 'lamb-lt :ltm ltm :rtm rtm :ttype ttype)))
