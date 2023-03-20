(in-package #:geb.lambda.spec)

(defclass <stlc> (geb.mixins:direct-pointwise-mixin geb.mixins:meta-mixin geb.mixins:cat-obj) ()
  (:documentation
   "Class of untyped terms of simply typed lambda claculus. Given our presentation, we look at the latter as a
type theory spanned by empty, unit types as well as coproduct, product, and function types."))

(deftype stlc ()
  "Type of untyped terms of [STLC][type]. Each class of a term has a slot for a type,
which can be filled by auxillary functions or by user. Types are represented
as [SUBSTOBJ][GEB.SPEC:SUBSTOBJ]."
  '(or absurd unit left right case-on pair fst snd lamb app index))

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
given a term of the empty type, denoted by [SO0][GEB.SPEC:SO0 type].
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

(defun absurd (tcod term &key (ttype nil))
  (make-instance 'absurd :tcod tcod :term term :ttype ttype))

(defclass unit (<stlc>)
  ((ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation
   "The unique term of the unit type, the latter represented by
[SO1][GEB.SPEC:SO1 type]. The formal grammar of [UNIT][class] is

```lisp
(unit)
```

where we can optionally include type information by

```lisp
(unit :ttype ttype)
```

Clearly the type of [UNIT][class] is [SO1][GEB.SPEC:SO1 type] but here
we provide all terms untyped.

This grammar corresponds to the introduction rule of the unit type. Namely
$$\\Gamma \\dashv \\text{(unit) : so1}$$"))

(defun unit (&key (ttype nil))
  (make-instance 'unit :ttype ttype))

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

(defun left (rty term &key (ttype nil))
  (make-instance 'left :rty rty :term term :ttype ttype))

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

(defun right (lty term &key (ttype nil))
  (make-instance 'right :lty lty :term term :ttype ttype))

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
   "A term of an arbutrary type provided by casing on a coproduct term. The formal grammar of
[CASE-ON][class] is

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
$$\\Gamma \\vdash \\text{on : (coprod (mcar (ttype on)) (mcadr (ttype on)))}$$ and
$$\\Gamma, \\text{(mcar (ttype on))} \\vdash \\text{ltm : (ttype ltm)}$$
, $$\\Gamma, \\text{(mcadr (ttype on))} \\vdash \\text{rtm : (ttype ltm)}$$ we get
$$\\Gamma \\vdash \\text{(case-on on ltm rtm) : (ttype ltm)}$$
"))

(defun case-on (on ltm rtm &key (ttype nil))
  (make-instance 'case-on :on on :ltm ltm :rtm rtm :ttype ttype))

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
   "A term of the product type gotten by pairing a terms of a left and right parts of the product.
The formal grammar of [PAIR][class] is

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

(defun pair (ltm rtm &key (ttype nil))
  (make-instance 'pair :ltm ltm :rtm rtm :ttype ttype))

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

(defun fst (term &key (ttype nil))
  (make-instance 'fst :term term :ttype ttype))

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

(defun snd (term &key (ttype nil))
  (make-instance 'snd :term term :ttype ttype))

(defclass lamb (<stlc>)
  ((tdom :initarg :tdom
         :accessor tdom
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
of the function type by assuming one is given a variable in the
domain. The formal grammar of [LAMB][class] is:

```lisp
(lamb tdom term)
```

where we can possibly include type information by

```lisp
(lamb tdom term :ttype ttype)
```

THe intended semnatics are: [TDOM][generic-function] is the type (and
hence a [SUBSTOBJ][GEB.SPEC:SUBSTOBJ]) which is the domain of the
function type. [TERM][generic-function] is a term (and hence an
[STLC][type]) of the codomain of the function type gotten in the
context of the domain.

This corresponds to the introduction rule of the function type. Namely, given
$$\\Gamma \\vdash \\text{tdom : Type}$$ and
$$\\Gamma, \\text{tdom} \\vdash \\text{term : (ttype term)}$$ we have
$$\\Gamma \\vdash \\text{(lamb tdom term) : (so-hom-obj tdom (ttype term))}$$"))

(defun lamb (tdom term &key (ttype nil))
  (make-instance 'lamb :tdom tdom :term term :ttype ttype))

(defclass app (<stlc>)
  ((fun :initarg :fun
        :accessor fun
        :documentation "Term of exponential type")
   (term :initarg :term
         :accessor term
         :documentation "Term of the domain")
   (ttype :initarg :ttype
          :initform nil
          :accessor ttype
          :documentation ""))
  (:documentation
   "A term of an arbitrary type gotten by applying a function of a
function type with a corresponding codomain to a term in the
domain. The formal grammar of [APP][class] is

```lisp
(app fun term)
```

where we can possibly include type information by

```lisp
(app fun term :ttype ttype)
```

The intended semantics are as follows: [FUN][generic-function] is a
term (and hence an [STLC][type]) of a coproduct type - say of
(so-hom-obj (ttype term) y) - and [TERM][generic-function] is a
term (hence also [STLC][type]) of the domain.

This corresponds to the elimination rule of the function type. Given
$$\\Gamma \\vdash \\text{fun : (so-hom-obj (ttype term) y)}$$ and
$$\\Gamma \\vdash \\text{term : (ttype term)}$$ we get
$$\\Gamma \\vdash \\text{(app fun term) : y}$$
"))

(defun app (fun term &key (ttype nil))
  (make-instance 'app :fun fun :term term :ttype ttype))

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
"))

(defun index (pos &key (ttype nil))
  (make-instance 'index :pos pos :ttype ttype))


