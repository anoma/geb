module Library.IdrisCategories

import Library.IdrisUtils

%default total

%hide Prelude.(|>)

-------------------------------
-------------------------------
---- Equivalence relations ----
-------------------------------
-------------------------------

public export
RelationOn : Type -> Type
RelationOn a = a -> a -> Type

public export
IsReflexive : {a : Type} -> RelationOn a -> Type
IsReflexive {a} r = (x : a) -> r x x

public export
IsSymmetric : {a : Type} -> RelationOn a -> Type
IsSymmetric {a} r = {x, y : a} -> r x y -> r y x

public export
IsTransitive : {a : Type} -> RelationOn a -> Type
IsTransitive {a} r = {x, y, z : a} -> r x y -> r y z -> r x z

public export
record IsEquivalence {a : Type} (r : RelationOn a) where
  constructor MkEquivalence
  EquivRefl : IsReflexive r
  EquivSym : IsSymmetric r
  EquivTrans : IsTransitive r

public export
record EqRel (a : Type) where
  constructor MkEq
  eqRel : RelationOn a
  eqCorrect : IsEquivalence eqRel

public export
data EquivClosure : {a : Type} -> RelationOn a -> RelationOn a where
  EqClGen : {a : Type} -> {r : RelationOn a} -> {x, x' : a} ->
    r x x' -> EquivClosure {a} r x x'
  EqClRefl : {a : Type} -> {r : RelationOn a} -> {x : a} ->
    EquivClosure {a} r x x
  EqClSym : {a : Type} -> {r : RelationOn a} -> {x, y : a} ->
    EquivClosure {a} r x y -> EquivClosure {a} r y x
  EqClTrans : {a : Type} -> {r : RelationOn a} -> {x, y, z : a} ->
    EquivClosure {a} r x y -> EquivClosure {a} r y z -> EquivClosure {a} r x z

public export
IsDecidable : {a : Type} -> (r : RelationOn a) -> Type
IsDecidable {a} r = (x, y : a) -> Dec (r x y)

public export
record IsDecEquiv {a : Type} (r : RelationOn a) where
  constructor MkDecEquiv
  DecEquivEquiv : IsEquivalence r
  DecEquivDec : IsDecidable r

public export
InverseUpTo : {a, b : Type} -> RelationOn a -> (a -> b) -> (b -> a) -> Type
InverseUpTo r f g = (x : a) -> r (g (f x)) x

public export
data FreeEqF : {0 a : Type} -> RelationOn a -> RelationOn a where
  FErefl : {0 a : Type} -> {0 rel : RelationOn a} ->
    (0 x : a) -> FreeEqF {a} rel x x
  FEsym : {0 a : Type} -> {0 rel : RelationOn a} ->
    (0 x, y : a) -> rel x y -> FreeEqF {a} rel y x
  FEtrans : {0 a : Type} -> {0 rel : RelationOn a} ->
    (0 x, y, z : a) -> rel y z -> rel x y -> FreeEqF {a} rel x z

-----------------------------------
-----------------------------------
---- Functional extensionality ----
-----------------------------------
-----------------------------------

-- When interpreting category theory into Idris's type system, we could
-- axiomatize functional extensionality, but instead we'll quotient over
-- it explicitly.  This is because we will quotient over a weaker notion
-- than that of functional extensionality:  decidable first-order
-- extensional equality.

public export
ExtEq : {a, b : Type} -> (a -> b) -> (a -> b) -> Type
ExtEq {a} f g = (el : a) -> f el = g el

public export
ExtEqRefl : {a, b : Type} -> (f : a -> b) -> ExtEq f f
ExtEqRefl _ _ = Refl

public export
ExtEqSym : {a, b : Type} -> {f, g : a -> b} -> ExtEq f g -> ExtEq g f
ExtEqSym eq x = sym (eq x)

public export
ExtEqTrans : {a, b : Type} ->
  {f, g, h: a -> b} -> ExtEq f g -> ExtEq g h -> ExtEq f h
ExtEqTrans eq eq' x = trans (eq x) (eq' x)

public export
ExtEqEquiv : {a, b : Type} -> IsEquivalence {a=(a -> b)} (ExtEq {a} {b})
ExtEqEquiv = MkEquivalence ExtEqRefl ExtEqSym ExtEqTrans

public export
EqFunctionExt : {a, b : Type} -> {f, g: a -> b} -> f = g -> ExtEq f g
EqFunctionExt Refl _ = Refl

public export
ExtInverse : {a, b : Type} -> (a -> b) -> (b -> a) -> Type
ExtInverse f g = (ExtEq (f . g) id, ExtEq (g . f) id)

public export
ExtInversePair : {a, b : Type} -> (a -> b, b -> a) -> Type
ExtInversePair = uncurry ExtInverse

-- Another way in which we use functional extensionality is to describe
-- the relationship between two terms that they are equal _under_
-- the assumption of functional extensionality.  Extensionally equal
-- functions do satisfy this relationship, but so do some functions which are
-- not extensionally equal -- in particular, higher-order functions whose
-- equality depends upon the functional extensionality of their _parameters_.
-- So this is a strictly larger relation than the relation of extensional
-- equality.  It might be thought of as "recursive" or "deep" extensional
-- equality.

public export
FunExtEq : {0 a, b : Type} -> a -> b -> Type
FunExtEq ea eb = FunExt -> ea ~=~ eb

public export
FunExtEqRefl : {0 a : Type} -> (ea : a) -> FunExtEq ea ea
FunExtEqRefl {a} _ _ = Refl

public export
FunExtEqSym : FunExtEq f g -> FunExtEq g f
FunExtEqSym eq x = sym (eq x)

public export
FunExtEqTrans : {0 a, a', a'' : Type} ->
  {f : a} -> {g : a'}  -> {h : a''} ->
  FunExtEq f g -> FunExtEq g h -> FunExtEq f h
FunExtEqTrans {a} {a'} {a''} eq eq' fext with (eq fext, eq' fext)
  FunExtEqTrans {a} {a'=a} {a''=a} eq eq' fext |
    (Refl, Refl) = Refl

public export
FunExtEqEquiv : IsEquivalence FunExtEq
FunExtEqEquiv = MkEquivalence FunExtEqRefl FunExtEqSym FunExtEqTrans

public export
EqFunctionFunExt : f = g -> FunExtEq f g
EqFunctionFunExt Refl _ = Refl

public export
ExtEqFunctionFunExt : {0 a, b : Type} -> {0 f, g : a -> b} ->
  ExtEq f g -> FunExtEq {a=(a -> b)} {b=(a -> b)} f g
ExtEqFunctionFunExt exteq fext = funExt $ \x => exteq x

public export
FunExtInverse : {0 a, b : Type} -> (a -> b) -> (b -> a) -> Type
FunExtInverse {a} {b} f g =
  (FunExtEq {a=(b -> b)} {b=(b -> b)} (f . g) id,
   FunExtEq {a=(a -> a)} {b=(a -> a)} (g . f) id)

public export
FunExtInverseId :
  (0 a : Type) -> FunExtInverse {a} {b=a} Prelude.id Prelude.id
FunExtInverseId a = (\_ => Refl, \_ => Refl)

public export
FunExtInversePair : {0 a, b : Type} -> (a -> b, b -> a) -> Type
FunExtInversePair {a} {b} = uncurry $ FunExtInverse {a} {b}

-- The claim that `g` is (up to functional extensionality) a left inverse
-- of `f`.
public export
0 IsExtLeftInverse : {a, b : Type} -> (f : a -> b) -> (g : b -> a) -> Type
IsExtLeftInverse {a} {b} f g =
  FunExtEq {a=(a -> a)} {b=(a -> a)} (g . f) (Prelude.id {a})

-- The claim that `g` is (up to functional extensionality) a right inverse
-- of `f`.
public export
0 IsExtRightInverse : {a, b : Type} -> (f : a -> b) -> (g : b -> a) -> Type
IsExtRightInverse {a} {b} = flip $ IsExtLeftInverse {a=b} {b=a}

-- A left inverse (up to functional extensionality) of the given function.
public export
ExtLeftInverse : {a, b : Type} -> (a -> b) -> Type
ExtLeftInverse {a} {b} f =
  Subset0 (b -> a) (IsExtLeftInverse f)

-- A right inverse (up to functional extensionality) of the given function.
public export
ExtRightInverse : {a, b : Type} -> (a -> b) -> Type
ExtRightInverse {a} {b} f = Subset0 (b -> a) (IsExtRightInverse f)

-- A factorization of the identity on `a` through `b`.
--
-- The first component is the _left_ inverse (and is therefore epi,
-- because it _has_ a right inverse); the second component is the _right_
-- inverse (and is therefore mono, because it _has_ a left inverse).
public export
IdFactThrough : (a, b : Type) -> Type
IdFactThrough a b = DPair (a -> b) $ ExtRightInverse {a} {b}

public export
idFactEpi : {0 a, b : Type} -> IdFactThrough a b -> a -> b
idFactEpi {a} {b} = DPair.fst

public export
idFactMono : {0 a, b : Type} -> IdFactThrough a b -> b -> a
idFactMono {a} {b} fact = Subset0.fst0 $ DPair.snd fact

public export
0 idFactIsRightInv : {0 a, b : Type} -> (fact : IdFactThrough a b) ->
  IsExtRightInverse {a} {b} (idFactEpi fact) (idFactMono fact)
idFactIsRightInv {a} {b} fact = Subset0.snd0 $ DPair.snd fact

public export
0 idFactIsLeftInv : {0 a, b : Type} -> (fact : IdFactThrough a b) ->
  IsExtLeftInverse {a=b} {b=a} (idFactMono fact) (idFactEpi fact)
idFactIsLeftInv = idFactIsRightInv

-- A factorization of the identity on `a` through any type.
-- (In particular, it could be the factorization through `a` itself
-- into `id . id`!)
public export
IdFact : Type -> Type
IdFact a = Exists {type=Type} (IdFactThrough a)

---------------------------------------------------------------
---------------------------------------------------------------
---- Standard (Mac Lane / Eilenberg) internal categories ----
---------------------------------------------------------------
---------------------------------------------------------------

public export
record SCat where
  constructor SC
  scObj : Type
  scHom : (scObj, scObj) -> Type
  scId : (a : scObj) -> scHom (a, a)
  scComp : {a, b, c : scObj} -> scHom (b, c) -> scHom (a, b) -> scHom (a, c)
  scEq : (sig : (scObj, scObj)) -> EqRel (scHom sig)
  0 scIdL : {0 a, b : scObj} -> (f : scHom (a, b)) ->
    (scEq (a, b)).eqRel f (scComp {a} {b} {c=b} (scId b) f)
  0 scIdR : {0 a, b : scObj} -> (f : scHom (a, b)) ->
    (scEq (a, b)).eqRel f (scComp {a} {b=a} {c=b} f (scId a))
  0 scIdAssoc : {0 a, b, c, d : scObj} ->
    (f : scHom (a, b)) -> (g : scHom (b, c)) -> (h : scHom (c, d)) ->
    (scEq (a, d)).eqRel
      (scComp {a} {b=c} {c=d} h (scComp {a} {b} {c} g f))
      (scComp {a} {b} {c=d} (scComp {a=b} {b=c} {c=d} h g) f)

-------------------------------------
-------------------------------------
---- Slice objects and morphisms ----
-------------------------------------
-------------------------------------

-- Objects of the slice category `Type` over `a`.
-- If we treat `a` as a discrete category, then we could also view
-- a slice object over `a` as a functor from `a` to `Type`.
public export
SliceObj : Type -> Type
SliceObj a = a -> Type

public export
Contravariant SliceObj where
  contramap = (|>)

public export
biapp : {0 a, b, c, d : Type} -> (b -> c -> d) -> (a -> b) -> (a -> c) -> a -> d
biapp h f g x = h (f x) (g x)

public export
SliceHom : {0 a : Type} -> SliceObj a -> SliceObj a -> SliceObj a
SliceHom = biapp $ \x, y => x -> y

-- A special case of `DepProdF` where `b` is the terminal object and
-- `f` is the unique morphism into it.  A slice object over the terminal
-- object is isomorphic to its domain, so the slice category of a category
-- over its terminal object is isomorphic to the category itself.
-- That is, `SliceObj ()` is effectively just `Type`.
--
-- Note that another way of looking at this type is as a natural transformation
-- from the polynomial endofunctor which represents the slice object to the
-- identity endofunctor.
public export
Pi : {a : Type} -> SliceObj a -> Type
Pi {a} p = (x : a) -> p x

-- We can view this as the total space of a bundle represented by
-- a slice object.  It is a special case of `DepCoprodF` where `b` is
-- the terminal object and `f` is the unique morphism into it.
public export
Sigma : {a : Type} -> SliceObj a -> Type
Sigma {a} p = (x : a ** p x)

-- If we view `a` as a discrete category, and slice objects of it as
-- functors from `a` to `Type`, then this type can also be viewed as
-- a natural transformation.
public export
SliceMorphism : {a : Type} -> SliceObj a -> SliceObj a -> Type
SliceMorphism {a} s s' = Pi {a} $ SliceHom {a} s s'

public export
sliceId : {a : Type} -> (sl : SliceObj a) -> SliceMorphism {a} sl sl
sliceId {a} sl = \_, x => x

public export
sliceComp : {a : Type} -> {x, y, z : SliceObj a} ->
  SliceMorphism {a} y z ->
  SliceMorphism {a} x y ->
  SliceMorphism {a} x z
sliceComp {a} {x} {y} {z} g f = \ela, elx => g ela $ f ela elx

public export
SliceExtEq : {a : Type} -> {s, s' : SliceObj a} ->
  (f, g : SliceMorphism {a} s s') -> Type
SliceExtEq {a} {s} {s'} f g = (e : a) -> ExtEq (f e) (g e)

public export
SliceFunExtEq : {a : Type} -> {s, s' : SliceObj a} ->
  (f, g : SliceMorphism {a} s s') -> Type
SliceFunExtEq {a} {s} {s'} f g = (e : a) -> FunExtEq (f e) (g e)

-- A slice over a type together with a `Pi` of that slice.  This amounts
-- to a type family indexed by `a` together with a section of that family
-- (i.e., a single term from each type).
--
-- Another way of viewing it is as a function out of `a` with a
-- heterogeneous, client-specified codomain:  the client chooses not
-- only the codomain, but potentially a different codomain for each
-- output value.
--
-- There is another way of looking at it as well, whence the name:
-- as a factorization of the identity on `a` into two morphisms.
-- Here is why we can view it this way:
--  - A function from `Unit` to a given type `b` can be viewed as simply a
--    term of `b`
--  - Hence, for a given `x : SliceObj a`, we may view `Pi {a} x` as a
--    slice morphism in the slice category over `a` from `const Unit` to `x`
--  - `const Unit`, as a slice object over `a` (specifically, it is the
--    terminal object in that category), is, in the category-theoretic
--    view, the slice object with total space `a` and projection `id(a)`
--  - Hence, the constraint on a slice morphism that the variable part of
--    the morphism commutes with the projections is the statement that
--    the composition of the projection of the slice object `x` after the
--    variable component of the slice morphism represented by a `Pi {a} x`
--    is equal to the identity
-- So we can in general view `Pi {a} x` as a factorization of the identity
-- on `a` _through_ (the total space of) `x`.  Because it's specifically
-- the identity that we're factoring, we may also view it as a function
-- out of `a` with a left inverse (which of course points back to `a`).
--
-- We call this `IdFactW` because it is a factorization of the identity
-- using W-types.
public export
IdFactW : Type -> Type
IdFactW a = Sigma {a=(SliceObj a)} (Pi {a})

--------------------
--------------------
---- Signatures ----
--------------------
--------------------

public export
SignatureT : Type -> Type
SignatureT x = (x, x)

public export
HomSlice : Type -> Type
HomSlice = SliceObj . SignatureT

--------------------------------------
--------------------------------------
---- Hom-objects and hom-functors ----
--------------------------------------
--------------------------------------

public export
InternalCovarHom : HomSlice obj -> obj -> SliceObj obj
InternalCovarHom hom = hom .* MkPair

public export
InternalContravarHom : HomSlice obj -> obj -> SliceObj obj
InternalContravarHom = flip . InternalCovarHom

public export
HomUncurry : (obj -> obj -> Type) -> HomSlice obj
HomUncurry hom (x, y) = hom x y

public export
InternalNTFromCovarHom : {obj : Type} ->
  (hom : HomSlice obj) -> obj -> SliceObj obj -> Type
InternalNTFromCovarHom {obj} hom =
  SliceMorphism {a=obj} . InternalCovarHom hom

public export
InternalNTFromContravarHom : {obj : Type} ->
  (hom : HomSlice obj) -> obj -> SliceObj obj -> Type
InternalNTFromContravarHom {obj} hom =
  SliceMorphism {a=obj} . InternalContravarHom hom

public export
InternalCopresheaf : Type -> Type
InternalCopresheaf = SliceObj

public export
InternalCopresheafNT : {obj : Type} -> SliceObj obj -> SliceObj obj -> Type
InternalCopresheafNT {obj} = SliceMorphism {a=obj}

public export
CopresheafNTExtEq : {obj : Type} -> {f, g : InternalCopresheaf obj} ->
  (alpha, beta : InternalCopresheafNT f g) -> Type
CopresheafNTExtEq {obj} {f} {g} = SliceExtEq {a=obj} {s=f} {s'=g}

------------------------------------------------------------
------------------------------------------------------------
---- Yoneda-lemma forms in standard categories (`SCat`) ----
------------------------------------------------------------
------------------------------------------------------------

----------------------------------------
---- Standard-category Yoneda lemma ----
----------------------------------------

public export
SCCovarHomYonedaR :
  (sc : SCat) -> (a : sc.scObj) -> (f : SliceObj sc.scObj) ->
  InternalNTFromCovarHom {obj=sc.scObj} sc.scHom a f -> f a
SCCovarHomYonedaR sc a f alpha = alpha a $ sc.scId a

public export
SCCovarHomYonedaL : (sc : SCat) -> (a : sc.scObj) -> (f : SliceObj sc.scObj) ->
  (fmap : (a, b : sc.scObj) -> sc.scHom (a, b) -> f a -> f b) ->
  f a -> InternalNTFromCovarHom {obj=sc.scObj} sc.scHom a f
SCCovarHomYonedaL sc a f fmap fa b mab = fmap a b mab fa

public export
SCContravarHomYonedaR :
  (sc : SCat) -> (a : sc.scObj) -> (f : SliceObj sc.scObj) ->
  InternalNTFromContravarHom {obj=sc.scObj} sc.scHom a f -> f a
SCContravarHomYonedaR sc a f alpha = alpha a $ sc.scId a

public export
SCContravarHomYonedaL :
  (sc : SCat) -> (a : sc.scObj) -> (f : SliceObj sc.scObj) ->
  -- f is contravariant
  (fmap : (a, b : sc.scObj) -> sc.scHom (a, b) -> f b -> f a) ->
  f a -> InternalNTFromContravarHom {obj=sc.scObj} sc.scHom a f
SCContravarHomYonedaL sc a f fmap fa b mba = fmap b a mba fa

-----------------------
-----------------------
---- Pointed types ----
-----------------------
-----------------------

-- A type plus a distinguished single term.  Isomorphic to `Either () a`.
public export
data PointedT : Type -> Type where
  Pt : {0 a : Type} -> a -> PointedT a
  Pp : {0 a : Type} -> PointedT a

-- The type whose terms represent objects of the subcategory of `Fin`, the
-- category of finite sets, composed of the pointed finite sets -- the non-empty
-- finite sets with one distinguished term each.
--
-- `PointedFin n` is `Fin n` plus a distinguished term, which isomorphic to
-- `Fin (S n)` (as well as `Either () (Fin n)`).
public export
PointedFin : Nat -> Type
PointedFin = PointedT . Fin

-----------------------------------------------
-----------------------------------------------
---- Categories internal to Idris's `Type` ----
-----------------------------------------------
-----------------------------------------------

public export
record CatSig where
  constructor MkCatSig
  catObj : Type
  catMorph : catObj -> catObj -> Type
  catMorphEq : (a, b  : catObj) -> RelationOn (catMorph a b)
  catId : (a : catObj) -> catMorph a a
  catComp : {a, b, c : catObj} -> catMorph b c -> catMorph a b -> catMorph a c

public export
record CatSigCorrect (cat : CatSig) where
  constructor MkCatSigCorrect
  catMorphEqEquiv : (a, b : catObj cat) -> IsEquivalence (catMorphEq cat a b)
  catLeftId : {a, b : catObj cat} ->
    (m : catMorph cat a b) ->
    catMorphEq cat a b (catComp cat {a} {b} {c=b} (catId cat b) m) m
  catRightId : {a, b : catObj cat} ->
    (m : catMorph cat a b) ->
    catMorphEq cat a b (catComp cat {a} {b=a} {c=b} m (catId cat a)) m
  catAssoc : {a, b, c, d : catObj cat} ->
    (h : catMorph cat c d) ->
    (g : catMorph cat b c) ->
    (f : catMorph cat a b) ->
    catMorphEq cat a d
      (catComp cat {a} {b=c} {c=d} h (catComp cat {a} {b} {c} g f))
      (catComp cat {a} {b} {c=d} (catComp cat {a=b} {b=c} {c=d} h g) f)

public export
CorrectCatSig : Type
CorrectCatSig = Subset0 CatSig CatSigCorrect

-- Idris's `Type` itself.
public export
TypeCat : CatSig
TypeCat =
  MkCatSig
    Type
    (\x, y => x -> y)
    (\x, y => ExtEq)
    (\x => Prelude.id)
    (\g, f => g . f)

Type2Obj : Type
Type2Obj = (Type, Type)

Type2Sig : Type
Type2Sig = (Type2Obj, Type2Obj)

Type2Morph : Type2Sig -> Type
Type2Morph ab = (fst (fst ab) -> fst (snd ab), snd (fst ab) -> snd (snd ab))

------------------------
------------------------
---- Arrow category ----
------------------------
------------------------

public export
0 ArrObj : Type
ArrObj = (ab : (Type, Type) ** fst ab -> snd ab)

public export
0 ArrMorphBase : ArrObj -> ArrObj -> Type
ArrMorphBase ((a, b) ** mab) ((c, d) ** mcd) = (a -> c, b -> d)

public export
0 ArrMorphComm : (0 arr, arr' : ArrObj) ->
  ArrMorphBase arr arr' -> Type
ArrMorphComm ((a, b) ** mab) ((c, d) ** mcd) (mac, mbd) =
  ExtEq (mbd . mab) (mcd . mac)

public export
0 ArrMorph : ArrObj -> ArrObj -> Type
ArrMorph arr arr' =
  Subset0 (ArrMorphBase arr arr') (ArrMorphComm arr arr')

--------------------------------
--------------------------------
---- Twisted-arrow category ----
--------------------------------
--------------------------------

public export
0 TwistArrObj : Type
TwistArrObj = ArrObj

public export
0 TwistArrMorphBase : TwistArrObj -> TwistArrObj -> Type
TwistArrMorphBase ((a, b) ** mab) ((c, d) ** mcd) = (c -> a, b -> d)

public export
0 TwistArrMorphComm : (0 tw, tw' : TwistArrObj) ->
  TwistArrMorphBase tw tw' -> Type
TwistArrMorphComm ((a, b) ** mab) ((c, d) ** mcd) (mca, mbd) =
  ExtEq mcd (mbd . mab . mca)

public export
0 TwistArrMorph : TwistArrObj -> TwistArrObj -> Type
TwistArrMorph tw tw' =
  Subset0 (TwistArrMorphBase tw tw') (TwistArrMorphComm tw tw')

---------------------------------------
---------------------------------------
---- Dependent types, categorially ----
---------------------------------------
---------------------------------------

-- The hom-object in `Type`.
public export
TypeHomObj : Type -> Type -> Type
TypeHomObj a b = a -> b

public export
sliceObjSigmaFMap : {a, b : Type} -> (a -> b) -> SliceObj a -> SliceObj b
sliceObjSigmaFMap {a} {b} f sla eb =
  (preb : Subset0 a (\ea => f ea = eb) ** sla $ fst0 preb)

public export
sliceObjPiFMap : {a, b : Type} -> (a -> b) -> SliceObj a -> SliceObj b
sliceObjPiFMap {a} {b} f sla eb =
  (preb : Subset0 a (\ea => f ea = eb)) -> sla $ fst0 preb

public export
Functor SliceObj where
  -- Like `sliceObjSigmaFMap`, but with zero usages on `a` and `b`.
  map {a} {b} f sla eb = Exists0 a $ \ea => (sla ea, f ea = eb)

public export
FinSliceObj : Nat -> Type
FinSliceObj = SliceObj . Fin

-- An object of some slice category of `Type`.
public export
Slice : Type
Slice = DPair Type SliceObj

public export
SliceFunctor : Type -> Type -> Type
SliceFunctor a b = SliceObj a -> SliceObj b

public export
FinSliceFunctor : Nat -> Nat -> Type
FinSliceFunctor m n = FinSliceObj m -> FinSliceObj n

public export
SliceEndofunctor : Type -> Type
SliceEndofunctor a = SliceFunctor a a

public export
SliceIdF : (a : Type) -> SliceEndofunctor a
SliceIdF a = Prelude.id

public export
FinSliceEndofunctor : Nat -> Type
FinSliceEndofunctor n = FinSliceFunctor n n

-- The base change functor induced by the given morphism.
-- Also sometimes called the pullback functor.
public export
BaseChangeF : {a, b : Type} -> (b -> a) -> SliceFunctor a b
BaseChangeF f sla = sla . f

public export
Equalizer : {a : Type} -> {0 b : Type} -> (0 f, g : a -> b) -> Type
Equalizer {a} {b} f g = Subset0 a (\x : a => f x = g x)

public export
equalizerInj : {a : Type} -> {0 b : Type} -> (0 f, g : a -> b) ->
  Equalizer f g -> a
equalizerInj f g = fst0

public export
PreImage : {a : Type} -> {0 b : Type} -> (0 _ : a -> b) -> (0 _ : b) -> Type
PreImage {a} {b} f elemb = Equalizer {a} {b} f (const elemb)

public export
WideEqualizer3 : {a : Type} -> {0 b : Type} -> (0 f, g, h : a -> b) -> Type
WideEqualizer3 {a} {b} f g h =
  Subset0 a (\ela => (f ela = g ela, g ela = h ela))

public export
Pullback : {a, b : Type} -> {0 c : Type} ->
  (0 _ : a -> c) -> (0 _ : b -> c) -> Type
Pullback {a} {b} {c} f g = Equalizer {a=(Pair a b)} {b=c} (f . fst) (g . snd)

public export
PullbackDec : {a, b : Type} -> (0 _ : (a, b) -> Bool) -> Type
PullbackDec {a} {b} p = PreImage {a=(Pair a b)} {b=Bool} p True

public export
pbProj1 : {a, b : Type} -> {0 c : Type} -> {0 f : a -> c} -> {0 g : b -> c} ->
  Pullback f g -> a
pbProj1 {a} {b} {c} {f} {g} = fst . fst0

public export
pbProj2 : {a, b : Type} -> {0 c : Type} -> {0 f : a -> c} -> {0 g : b -> c} ->
  Pullback f g -> b
pbProj2 {a} {b} {c} {f} {g} = snd . fst0

public export
WidePullback3 : {a, b, c : Type} -> {0 d : Type} ->
  (0 _ : a -> d) -> (0 _ : b -> d) -> (0 _ : c -> d) -> Type
WidePullback3 {a} {b} {c} {d} f g h =
  WideEqualizer3 {a=(a, b, c)} {b=d} (f . fst) (g . fst . snd) (h . snd . snd)

public export
Slice2Obj : {a : Type} -> SliceObj a -> Type
Slice2Obj {a} sl = Pi {a} (SliceObj . sl)

public export
SigmaToPair : {0 a, b : Type} -> (Sigma {a} (const b)) -> (a, b)
SigmaToPair (x ** y) = (x, y)

public export
PairToSigma : {0 a, b : Type} -> (a, b) -> (Sigma {a} (const b))
PairToSigma (x, y) = (x ** y)

public export
SliceFunctorMap : {x, y : Type} -> (f : SliceFunctor x y) -> Type
SliceFunctorMap {x} {y} f =
  {sa, sb : SliceObj x} -> SliceMorphism sa sb -> SliceMorphism (f sa) (f sb)

public export
SliceToPi : {a : Type} -> {p : SliceObj a} -> SliceMorphism (const ()) p -> Pi p
SliceToPi m x = m x ()

public export
PiToSlice : {a : Type} -> {p : SliceObj a} -> Pi p -> SliceMorphism (const ()) p
PiToSlice pi x () = pi x

public export
smApp : {0 a : Type} -> {0 s, s' : SliceObj a} ->
  SliceMorphism s s' -> Sigma s -> Sigma s'
smApp m (i ** d) = (i ** m i d)

public export
smMap : {0 a : Type} -> {0 s, s' : SliceObj a} ->
  SliceMorphism s s' -> List (Sigma s) -> List (Sigma s')
smMap m = map (smApp m)

public export
smMapFstEq : {0 a : Type} -> {0 s, s' : SliceObj a} ->
  (m : SliceMorphism s s') -> (l : List (Sigma s)) ->
  map DPair.fst (smMap m l) = map DPair.fst l
smMapFstEq m [] = Refl
smMapFstEq m ((i ** d) :: l') = cong ((::) i) $ smMapFstEq m l'

public export
SliceFMorphism : {a : Type} -> SliceObj a -> (a -> a) -> Type
SliceFMorphism s f = SliceMorphism s (BaseChangeF f s)

public export
ArrowObj : Type
ArrowObj = (sig : (Type, Type) ** (fst sig -> snd sig))

public export
SliceFMap : {c, d : Type} -> SliceFunctor c d -> Type
SliceFMap {c} {d} f =
  (x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)

public export
SliceNatTrans : {x, y : Type} -> (f, g : SliceFunctor x y) -> Type
SliceNatTrans {x} {y} f g = (s : SliceObj x) -> SliceMorphism (f s) (g s)

public export
SliceNTid : {c, d : Type} -> (f : SliceFunctor c d) -> SliceNatTrans f f
SliceNTid {c} {d} f a = sliceId (f a)

public export
SliceNTvcomp : {c, d : Type} -> {f, g, h : SliceFunctor c d} ->
  SliceNatTrans g h -> SliceNatTrans f g -> SliceNatTrans f h
SliceNTvcomp {c} {d} {f} {g} {h} beta alpha a =
  sliceComp {x=(f a)} {y=(g a)} {z=(h a)} (beta a) (alpha a)

public export
SliceWhiskerLeft : {0 c, d, e : Type} ->
  {0 g, h : SliceFunctor d e} ->
  (nu : SliceNatTrans {x=d} {y=e} g h) -> (f : SliceFunctor c d) ->
  SliceNatTrans {x=c} {y=e} (g . f) (h . f)
SliceWhiskerLeft {c} {d} {e} {g} {h} nu f a = nu (f a)

public export
SliceWhiskerRight : {0 c, d, e : Type} ->
  {f, g : SliceFunctor c d} ->
  {h : SliceFunctor d e} ->
  SliceFMap {c=d} {d=e} h -> (nu : SliceNatTrans {x=c} {y=d} f g) ->
  SliceNatTrans {x=c} {y=e} (h . f) (h . g)
SliceWhiskerRight {c} {d} {e} {f} {g} {h} hm nu a = hm (f a) (g a) (nu a)

public export
SliceNThcomp : {c, d, e : Type} ->
  {f, f' : SliceFunctor c d} -> {g, g' : SliceFunctor d e} ->
  SliceFMap {c=d} {d=e} g ->
  SliceNatTrans {x=d} {y=e} g g' -> SliceNatTrans {x=c} {y=d} f f' ->
  SliceNatTrans {x=c} {y=e} (g . f) (g' . f')
SliceNThcomp {c} {d} {e} {f} {f'} {g} {g'} gm beta alpha a =
  sliceComp {a=e} {x=(g (f a))} {y=(g (f' a))} {z=(g' (f' a))}
    (SliceWhiskerLeft {c} {d} {e} {g} {h=g'} beta f' a)
    (SliceWhiskerRight {c} {d} {e} {f} {g=f'} {h=g} gm alpha a)

public export
SliceProduct : {0 a : Type} -> SliceObj a -> SliceObj a -> SliceObj a
SliceProduct = biapp Pair

public export
SlProdBaseChange : {a, b, c : Type} -> (b -> a) -> SliceFunctor (a, c) (b, c)
SlProdBaseChange = BaseChangeF . mapFst

public export
SliceCoproduct : {0 a : Type} -> SliceObj a -> SliceObj a -> SliceObj a
SliceCoproduct = biapp Either

public export
sliceFlip : {0 c : Type} -> {x, y, z : SliceObj c} ->
  SliceMorphism x (SliceHom y z) ->
  SliceMorphism y (SliceHom x z)
sliceFlip {c} {x} {y} {z} f ec ey ex = f ec ex ey

public export
SliceDepPair : {0 a : Type} -> (x : SliceObj a) -> SliceObj (Sigma {a} x) ->
  SliceObj a
SliceDepPair {a} x sl ea = Sigma {a=(x ea)} (sl . MkDPair ea)

public export
piMap : {0 c : Type} -> {0 x, y : SliceObj c} ->
  SliceMorphism x y -> Pi x -> Pi y
piMap {c} {x} {y} g f ec = g ec $ f ec

public export
sliceApp : {0 c : Type} -> {0 x, y, z : SliceObj c} ->
  SliceMorphism x (SliceHom y z) -> SliceMorphism x y ->
  SliceMorphism x z
sliceApp {c} {x} {y} {z} g f ec ex = g ec ex $ f ec ex

public export
sliceFiberByMor : {0 c : Type} ->
  {a, b : SliceObj c} -> (i : SliceMorphism {a=c} b a) ->
  (ec : c) -> SliceObj (a ec)
sliceFiberByMor {c} {a} {b} i ec ea = PreImage {a=(b ec)} {b=(a ec)} (i ec) ea

public export
resliceByMor : {0 c : Type} ->
  {a, b : SliceObj c} -> (i : SliceMorphism {a=c} b a) ->
  SliceObj (Sigma {a=c} a)
resliceByMor {c} {a} {b} i ecp = sliceFiberByMor i (fst ecp) (snd ecp)

public export
SlSliceToSlice : {0 c : Type} -> {a : SliceObj c} ->
  SliceObj (Sigma {a=c} a) -> SliceObj c
SlSliceToSlice {c} {a} sl ec = Sigma {a=(a ec)} (curry sl ec)

public export
slSliceToMor : {0 c : Type} -> {a : SliceObj c} ->
  (sl : SliceObj (Sigma {a=c} a)) ->
  SliceMorphism {a=c} (SlSliceToSlice {a} {c} sl) a
slSliceToMor {c} {a} sl ec = DPair.fst

public export
CSliceOfSlice : {c : Type} -> SliceObj c -> Type
CSliceOfSlice {c} sl = (tot : SliceObj c ** SliceMorphism {a=c} tot sl)

public export
CSliceOfSliceToSliceOfSigma : {c : Type} -> {sl : SliceObj c} ->
  CSliceOfSlice {c} sl -> SliceObj (Sigma {a=c} sl)
CSliceOfSliceToSliceOfSigma {c} {sl} csl =
  resliceByMor {c} {a=sl} {b=(fst csl)} (snd csl)

public export
SliceOfSigmaToCSliceOfSlice : {c : Type} -> {sl : SliceObj c} ->
  SliceObj (Sigma {a=c} sl) -> CSliceOfSlice {c} sl
SliceOfSigmaToCSliceOfSlice {c} {sl} ssl =
  (SlSliceToSlice ssl ** slSliceToMor ssl)

---------------------------------------------------------------

---------------------------------------------------------------
---------------------------------------------------------------
---- Applicatives and monads in slice categories of `Type` ----
---------------------------------------------------------------
---------------------------------------------------------------

public export
SlicePure : {c : Type} -> SliceEndofunctor c -> Type
SlicePure {c} = SliceNatTrans {x=c} {y=c} (SliceIdF c)

public export
SliceApply : {c, d : Type} -> SliceFunctor c d -> Type
SliceApply {c} {d} f = (x, y : SliceObj c) ->
  SliceMorphism {a=d} (f (SliceHom x y)) (SliceHom (f x) (f y))

-- The signature of the `bind` morphism of a slice monad.
public export
SliceBind : {c : Type} -> SliceEndofunctor c -> Type
SliceBind {c} m = (x, y : SliceObj c) ->
  SliceMorphism x (m y) -> SliceMorphism (m x) (m y)

-- The signature of the `bind` morphism of a slice monad.
public export
SliceInternalBind : {c : Type} -> SliceEndofunctor c -> Type
SliceInternalBind {c} m = (x, y : SliceObj c) ->
  SliceMorphism (SliceHom x (m y)) (SliceHom (m x) (m y))

public export
sliceBindFromInternalBind : {c : Type} -> (f : SliceEndofunctor c) ->
  SliceInternalBind f -> SliceBind f
sliceBindFromInternalBind {c} f bi x y fxy ec = bi x y ec (fxy ec)

public export
SliceJoin : {c : Type} -> SliceEndofunctor c -> Type
SliceJoin {c} f = SliceNatTrans {x=c} {y=c} (f . f) f

public export
sliceBindFromMapAndJoin : {c : Type} ->
  (f : SliceEndofunctor c) -> (fm : SliceFMap f) ->
  SliceJoin f -> SliceBind f
sliceBindFromMapAndJoin {c} f fm j x y = sliceComp (j y) . fm x (f y)

public export
sliceJoinFromBind : {c : Type} -> (f : SliceEndofunctor c) ->
  SliceBind f -> SliceJoin f
sliceJoinFromBind {c} f b a = b (f a) a $ sliceId (f a)

public export
sliceJoinFromInternalBind : {c : Type} -> (f : SliceEndofunctor c) ->
  SliceInternalBind f -> SliceJoin f
sliceJoinFromInternalBind {c} f =
  sliceJoinFromBind f . sliceBindFromInternalBind f

public export
sliceMapFromPureAndBind : {c : Type} -> (f : SliceEndofunctor c) ->
  SlicePure {c} f -> SliceBind {c} f ->
  SliceFMap {c} {d=c} f
sliceMapFromPureAndBind {c} f pu bi x y = bi x y . sliceComp (pu y)

public export
sliceMapFromPureAndInternalBind : {c : Type} -> (f : SliceEndofunctor c) ->
  SlicePure {c} f -> SliceInternalBind {c} f ->
  SliceFMap {c} {d=c} f
sliceMapFromPureAndInternalBind {c} f pu bi =
  sliceMapFromPureAndBind f pu (sliceBindFromInternalBind f bi)

public export
sliceApplyFromPureAndInternalBind : {c : Type} -> (f : SliceEndofunctor c) ->
  SlicePure {c} f -> SliceInternalBind {c} f ->
  SliceApply {c} {d=c} f
sliceApplyFromPureAndInternalBind {c} f pu bi x y ec ffxy fxc =
  bi (SliceHom x y) y ec (\fxyc => bi x y ec (pu y ec . fxyc) fxc) ffxy

public export
applyFromBindHelper : {0 a, b, c : Type} ->
  (b -> c) -> (((a -> b) -> c) -> c) -> a -> c
applyFromBindHelper =
  (|>) {a} {b=((a -> b) -> c)} {c} .
  preCompFlipApp {a} {b} {c=((a -> b) -> c)} .
  (.) {a=(a -> b)} {b} {c}

-- An alternative version of `sliceApplyFromPureAndInternalBind`
-- which makes it explicit how to recast it into category-theoretic style.
public export
sliceApplyFromPureAndInternalBind' : {c : Type} -> (f : SliceEndofunctor c) ->
  SlicePure {c} f -> SliceInternalBind {c} f ->
  SliceApply {c} {d=c} f
sliceApplyFromPureAndInternalBind' {c} f pu bi x y =
  sliceComp
    {x=(f (SliceHom x y))}
    {y=(SliceHom (SliceHom (SliceHom x y) (f y)) (f y))}
    {z=(SliceHom (f x) (f y))}
    (sliceComp
      (bi x y)
      (piMap {c}
        {x=(SliceHom y (f y))}
        {y=(
          SliceHom
            (SliceHom (SliceHom (SliceHom x y) (f y)) (f y))
            (SliceHom x (f y)))}
        (\ec' : c => applyFromBindHelper {a=(x ec')} {b=(y ec')} {c=(f y ec')})
        (pu y)))
    (sliceFlip {x=(SliceHom (SliceHom x y) (f y))} {y=(f (SliceHom x y))} $
      bi (SliceHom x y) y)

-------------------------------------------------------------
-------------------------------------------------------------
---- Universal objects and morphisms in slice categories ----
-------------------------------------------------------------
-------------------------------------------------------------

---------------------------------
---- Within a slice category ----
---------------------------------

public export
SliceObjInitial : (a : Type) -> SliceObj a
SliceObjInitial a = const Void

public export
sliceFromInitial : (sl : SliceObj a) -> SliceMorphism {a} (SliceObjInitial a) sl
sliceFromInitial {a} sl = \_, v => void v

public export
SliceObjTerminal : (a : Type) -> SliceObj a
SliceObjTerminal a = const Unit

public export
sliceToTerminal : (sl : SliceObj a) -> SliceMorphism {a} sl (SliceObjTerminal a)
sliceToTerminal {a} sl = \_, _ => ()

public export
SliceObjCoproduct : SliceObj a -> SliceObj a -> SliceObj a
SliceObjCoproduct sa sa' ea = Either (sa ea) (sa' ea)

public export
sliceObjInjL : (sa, sa' : SliceObj a) ->
  SliceMorphism {a} sa (SliceObjCoproduct sa sa')
sliceObjInjL sa sa' ea sea = Left sea

public export
sliceObjInjR : (sa, sa' : SliceObj a) ->
  SliceMorphism {a} sa' (SliceObjCoproduct sa sa')
sliceObjInjR sa sa' ea sea = Right sea

public export
sliceObjCase : {sa, sa', sa'' : SliceObj a} ->
  SliceMorphism {a} sa sa'' -> SliceMorphism {a} sa' sa'' ->
  SliceMorphism {a} (SliceObjCoproduct sa sa') sa''
sliceObjCase m m' ea (Left sea) = m ea sea
sliceObjCase m m' ea (Right sea') = m' ea sea'

public export
SliceObjProduct : SliceObj a -> SliceObj a -> SliceObj a
SliceObjProduct sa sa' ea = (sa ea, sa' ea)

public export
sliceObjProjL : (sa, sa' : SliceObj a) ->
  SliceMorphism {a} (SliceObjProduct sa sa') sa
sliceObjProjL sa sa' ea = fst

public export
sliceObjProjR : (sa, sa' : SliceObj a) ->
  SliceMorphism {a} (SliceObjProduct sa sa') sa'
sliceObjProjR sa sa' ea = snd

public export
sliceObjPair : {sa, sa', sa'' : SliceObj a} ->
  SliceMorphism {a} sa sa' -> SliceMorphism {a} sa sa'' ->
  SliceMorphism {a} sa (SliceObjProduct sa' sa'')
sliceObjPair m m' ea sea = (m ea sea, m' ea sea)

public export
SliceObjHom : SliceObj a -> SliceObj a -> SliceObj a
SliceObjHom sa sa' ea = sa ea -> sa' ea

public export
sliceObjEval : (sa, sa' : SliceObj a) ->
  SliceMorphism {a} (SliceProduct (SliceObjHom sa sa') sa) sa'
sliceObjEval sa sa' ea (f, sea) = f sea

public export
sliceObjCurry : {sa, sa', sa'' : SliceObj a} ->
  SliceMorphism {a} (SliceObjProduct sa sa') sa'' ->
  SliceMorphism {a} sa (SliceObjHom sa' sa'')
sliceObjCurry f ea sea sea' = f ea (sea, sea')

public export
sliceObjId : (sl : SliceObj a) -> SliceMorphism {a} sl sl
sliceObjId sl ea = id

-------------------------------------------------
---- In the two-category of slice categories ----
-------------------------------------------------

public export
SlicePolyCoprod : SliceObj a -> SliceObj b -> SliceObj (Either a b)
SlicePolyCoprod sa sb (Left ea) = sa ea
SlicePolyCoprod sa sb (Right eb) = sb eb

public export
SlicePolyProd : SliceObj a -> SliceObj b -> SliceObj (a, b)
SlicePolyProd sa sb (ea, eb) = (sa ea, sb eb)

public export
sliceMorphCoproduct : {sa, sa' : SliceObj a} -> {sb, sb' : SliceObj b} ->
  SliceMorphism {a} sa sa' -> SliceMorphism {a=b} sb sb' ->
  SliceMorphism {a=(Either a b)}
    (SlicePolyCoprod sa sb) (SlicePolyCoprod sa' sb')
sliceMorphCoproduct ma mb (Left ea) sea = ma ea sea
sliceMorphCoproduct ma mb (Right eb) seb = mb eb seb

public export
sliceMorphProduct : {sa, sa' : SliceObj a} -> {sb, sb' : SliceObj b} ->
  SliceMorphism {a} sa sa' -> SliceMorphism {a=b} sb sb' ->
  SliceMorphism {a=(a, b)}
    (SlicePolyProd sa sb) (SlicePolyProd sa' sb')
sliceMorphProduct ma mb (ea, eb) (sea, seb) = (ma ea sea, mb eb seb)

---------------------------------------------------------
---------------------------------------------------------
---- Some specific dependent applicatives and monads ----
---------------------------------------------------------
---------------------------------------------------------

public export
sliceEitherInternalBind : {c : Type} ->
  (e : SliceObj c) -> SliceInternalBind {c} (SliceObjCoproduct e)
sliceEitherInternalBind {c} e x y ec =
  eitherElim {a=(e ec)} {b=(x ec)} {c=(Either (e ec) (y ec))} Left

----------------------------------------
----------------------------------------
---- Subobject classifier in `Type` ----
----------------------------------------
----------------------------------------

-- Subobject classifier in what I think is the style of the HoTT book with
-- an `isProp` as in https://ncatlab.org/nlab/show/mere+proposition.

public export
IsHProp : Type -> Type
IsHProp a = (x, y : a) -> x = y

public export
SubCFromHProp : Type
SubCFromHProp = Subset0 Type IsHProp

public export
SubCType : Type
SubCType = SubCFromHProp

public export
PowerObjFromProp : Type -> Type
PowerObjFromProp a = a -> SubCFromHProp

public export
PowObjType : Type -> Type
PowObjType = PowerObjFromProp

public export
TrueForHProp : () -> SubCFromHProp
TrueForHProp () = Element0 Unit $ \(), () => Refl

public export
TrueType : () -> SubCFromHProp
TrueType = TrueForHProp

public export
ChiForHProp : {0 a, b : Type} ->
  (f : a -> b) -> ((x, y : a) -> f x = f y -> x = y) ->
  b -> SubCFromHProp
ChiForHProp {a} {b} f isMonic eb =
  Element0
    (Exists0 a $ \x => f x = eb)
    $ \(Evidence0 x eqx), (Evidence0 y eqy) =>
      case isMonic x y (trans eqx (sym eqy)) of
        Refl => case uip {eq=eqx} {eq'=eqy} of
          Refl => Refl

public export
ChiType : {0 a, b : Type} ->
  (f : a -> b) -> ((x, y : a) -> f x = f y -> x = y) ->
  b -> SubCFromHProp
ChiType = ChiForHProp

public export
0 ChiForHPropPbToDom : {0 a, b : Type} ->
  (f : a -> b) -> (isMonic : (x, y : a) -> f x = f y -> x = y) ->
  Pullback {a=b} {b=Unit} {c=SubCFromHProp}
    (ChiForHProp f isMonic) TrueForHProp ->
  a
ChiForHPropPbToDom {a} {b} f isMonic (Element0 (eb, ()) eq) =
  fst0 $ replace {p=id} (sym $ elementInjectiveFst eq) ()

public export
0 ChiPbToDomType : {0 a, b : Type} ->
  (f : a -> b) -> (isMonic : (x, y : a) -> f x = f y -> x = y) ->
  Pullback {a=b} {b=Unit} {c=SubCFromHProp}
    (ChiForHProp f isMonic) TrueForHProp ->
  a
ChiPbToDomType = ChiForHPropPbToDom

public export
0 ChiForHPropDomToPbBase : {0 a, b : Type} ->
  (f : a -> b) -> (isMonic : (x, y : a) -> f x = f y -> x = y) ->
  a -> (a, b)
ChiForHPropDomToPbBase {a} {b} f isMonic ela = (ela, f ela)

----------------------------------------------------
----------------------------------------------------
---- Natural transformations and their algebras ----
----------------------------------------------------
----------------------------------------------------

public export
AppFunctor : (f, g : Type -> Type) -> Type -> Type
AppFunctor f g a = f a -> g a

public export
NaturalTransformation : (Type -> Type) -> (Type -> Type) -> Type
NaturalTransformation f g = Pi (AppFunctor f g)

public export
NaturalityCondition : {f, g : Type -> Type} ->
  (fmap : (0 a, b : Type) -> (a -> b) -> f a -> f b) ->
  (gmap : (0 a, b : Type) -> (a -> b) -> g a -> g b) ->
  NaturalTransformation f g -> Type
NaturalityCondition {f} {g} fm gm alpha =
  (a, b : Type) -> (m : a -> b) ->
  ExtEq {a=(f a)} {b=(g b)}
    (alpha b . fm a b m)
    (gm a b m . alpha a)

public export
IdNT : (f : Type -> Type) -> NaturalTransformation f f
IdNT f a = id {a=(f a)}

public export
vcompNT : {f, g, h : Type -> Type} ->
  NaturalTransformation g h -> NaturalTransformation f g ->
  NaturalTransformation f h
vcompNT {f} {g} {h} beta alpha x = beta x . alpha x

public export
hcompNT : {f, f', g, g' : Type -> Type} ->
  ({a, b : Type} -> (a -> b) -> g a -> g b) ->
  NaturalTransformation g g' -> NaturalTransformation f f' ->
  NaturalTransformation (g . f) (g' . f')
hcompNT {f} {f'} {g} {g'} gmap beta alpha x = beta (f' x) . gmap (alpha x)

public export
whiskerLeft : {f, g : Type -> Type} ->
  NaturalTransformation f g -> (k : Type -> Type) ->
  NaturalTransformation (f . k) (g . k)
whiskerLeft {f} {g} alpha k x = alpha (k x)

public export
whiskerRight : {f, g : Type -> Type} ->
  (h : Type -> Type) -> ({a, b : Type} -> (a -> b) -> h a -> h b) ->
  NaturalTransformation f g ->
  NaturalTransformation (h . f) (h . g)
whiskerRight {f} {g} h hmap alpha x = hmap (alpha x)

public export
ExtEqNT : {f, g : Type -> Type} ->
  NaturalTransformation f g -> NaturalTransformation f g -> Type
ExtEqNT alpha beta = (x : Type) -> ExtEq (alpha x) (beta x)

public export
AdjUnit : (Type -> Type) -> Type
AdjUnit f = NaturalTransformation id f

public export
AdjCounit : (Type -> Type) -> Type
AdjCounit f = NaturalTransformation f id

---------------------
---------------------
---- Profunctors ----
---------------------
---------------------

---------------------------------------------------
---- Profunctor interface and core definitions ----
---------------------------------------------------

public export
0 ProfunctorSig : Type
ProfunctorSig = Type -> Type -> Type

public export
0 DimapSig : ProfunctorSig -> Type
DimapSig p = {0 a, b, c, d : Type} -> (c -> a) -> (b -> d) -> p a b -> p c d

public export
interface Profunctor f where
  constructor MkProfunctor

  total
  dimap : DimapSig f

public export
total
lmap : Profunctor f => {0 a, b, c : Type} -> (c -> a) -> f a b -> f c b
lmap {a} {b} {c} = flip (dimap {a} {b} {c} {d=b}) id

public export
total
rmap : Profunctor f => {0 a, b, d : Type} -> (b -> d) -> f a b -> f a d
rmap {a} {b} {d} = dimap {a} {b} {c=a} {d} id

-- A contravariant profunctor is a functor from `(Type, op(Type))` to
-- `Type`.  Because `(Type, op(Type))` and `(op(Type), op)` are equivalent --
-- unlike `op(Type)` and `Type`! -- we can also view a contravariant
-- profunctor as simply a covariant profunctor with its arguments flipped.
public export
ContraProfunctor : ProfunctorSig -> Type
ContraProfunctor p = Profunctor (flip p)

public export
0 ContraDimapSig : ProfunctorSig -> Type
ContraDimapSig p = {0 a, b, c, d : Type} ->
  (a -> c) -> (d -> b) -> p a b -> p c d

public export
contraDimap : {0 f : ProfunctorSig} -> ContraProfunctor f => ContraDimapSig f
contraDimap {f} {a} {b} {c} {d} =
  flip (dimap {f=(flip f)} {a=b} {b=a} {c=d} {d=c})

public export
ProfunctorDP : Type
ProfunctorDP = DPair (Type -> Type -> Type) Profunctor

public export
PfSliceObj : Type
PfSliceObj = SliceObj ProfunctorDP

public export
PfCatObj : PfSliceObj
PfCatObj = const Unit

public export
EndBase : (p : Type -> Type -> Type) -> Type
EndBase p = (b : Type) -> p b b

-- See for example "ends as equalizers" at
-- https://bartoszmilewski.com/2017/03/29/ends-and-coends/ .

public export
PolyProdP : (Type -> Type -> Type) -> Type
PolyProdP p = (a, b : Type) -> (a -> b) -> p a b

public export
wedgeLeft : {p : Type -> Type -> Type} -> Profunctor p =>
  EndBase p -> PolyProdP p
wedgeLeft {p} i a b f = lmap {f=p} {a=b} {b} {c=a} f (i b)

public export
wedgeRight : {p : Type -> Type -> Type} -> Profunctor p =>
  EndBase p -> PolyProdP p
wedgeRight {p} i a b f = rmap {f=p} {a} {b=a} {d=b} f (i a)

public export
End : (p : Type -> Type -> Type) -> {isP : Profunctor p} -> Type
End p {isP} =
  Equalizer {a=(EndBase p)} {b=(PolyProdP p)} (wedgeLeft {p}) (wedgeRight {p})

-- Given two functors, we can define a profunctor whose end is the object
-- of natural transformations between the given functors.
public export
NatTransProf : (Type -> Type) -> (Type -> Type) -> ProfunctorSig
NatTransProf f g a b = (f a -> g b)

public export
[NatTransProfProf] (Functor f, Functor g) => Profunctor (NatTransProf f g) where
  dimap mca mbd nuab =
    map {f=g} {a=b} {b=d} mbd . nuab . map {f} {a=c} {b=a} mca

public export
NatTransAsEnd : (f, g : Type -> Type) ->
  {auto funcf : Functor f} -> {auto funcg : Functor g} -> Type
NatTransAsEnd f g {funcf} {funcg} =
  End (NatTransProf f g) {isP=NatTransProfProf}

public export
CoendBase : (p : Type -> Type -> Type) -> Type
CoendBase p = (b : Type ** p b b)

-- See for example the "coends" section at
-- https://bartoszmilewski.com/2017/03/29/ends-and-coends/ .

public export
PolySumP : (Type -> Type -> Type) -> Type
PolySumP p = (ab : (Type, Type) ** (snd ab -> fst ab, p (fst ab) (snd ab)))

public export
cowedgeLeft : {p : Type -> Type -> Type} -> Profunctor p =>
  PolySumP p -> CoendBase p
cowedgeLeft {p} ((a, b) ** (fba, pab)) =
  (b ** lmap {f=p} {a} {b} {c=b} fba pab)

public export
cowedgeRight : {p : Type -> Type -> Type} -> Profunctor p =>
  PolySumP p -> CoendBase p
cowedgeRight {p} ((a, b) ** (fba, pab)) =
  (a ** rmap {f=p} {a} {b} {d=a} fba pab)

public export
ProfDiNT : (p, q : Type -> Type -> Type) -> Type
ProfDiNT p q = (a : Type) -> p a a -> q a a

public export
ProfNT : (p, q : Type -> Type -> Type) -> Type
ProfNT p q = {a, b : Type} -> p a b -> q a b

public export
ProfNTid : (p : Type -> Type -> Type) -> ProfNT p p
ProfNTid p = id

public export
ProfNTcomp : {p, q, r : Type -> Type -> Type} ->
  ProfNT q r -> ProfNT p q -> ProfNT p r
ProfNTcomp {p} {q} {r} alpha beta = (.) alpha beta

-- Called 'HFunProf` by Milewski.
public export
ProfPreshfMap : ((Type -> Type -> Type) -> Type) -> Type
ProfPreshfMap pi = {p, q : Type -> Type -> Type} -> ProfNT p q -> pi p -> pi q

-- Called 'HNatProf` by Milewski.
public export
ProfPreshfNT : (pi, rho : ((Type -> Type -> Type) -> Type)) -> Type
ProfPreshfNT pi rho = {p : Type -> Type -> Type} -> Profunctor p -> pi p -> rho p

-------------------------------------
---- Hom-functors as profunctors ----
-------------------------------------

public export
CovarHomAsPro : Type -> Type -> Type -> Type
CovarHomAsPro s c d = s -> d

public export
covarHomDimap : {0 s, a, b, c, d : Type} ->
  (c -> a) -> (b -> d) -> CovarHomAsPro s a b -> CovarHomAsPro s c d
covarHomDimap {s} {a} {b} {c} {d} fca fbd fsb = fbd . fsb

public export
[CovarHomPro] Profunctor (CovarHomAsPro s) where
  dimap = covarHomDimap {s}

public export
ContravarHomAsPro : Type -> Type -> Type -> Type
ContravarHomAsPro t c d = c -> t

public export
contravarHomDimap : {0 t, a, b, c, d : Type} ->
  (c -> a) -> (b -> d) -> ContravarHomAsPro t a b -> ContravarHomAsPro t c d
contravarHomDimap {t} {a} {b} {c} {d} fca fbd fat = fat . fca

public export
[ContravarHomPro] Profunctor (ContravarHomAsPro t) where
  dimap {t} = contravarHomDimap {t}

public export
HomProf : Type -> Type -> Type
HomProf a b = a -> b

public export
[HomProfProfunctor] Profunctor HomProf where
  dimap fca fbd fab = fbd . fab . fca

public export
OpHomProf : Type -> Type -> Type
OpHomProf = flip HomProf

-------------------------------------------------------------
---- Pre-/post-composition pairs and isos as profunctors ----
-------------------------------------------------------------

-- `PrePostPair s t a b` is a morphism from `(s, t)` to `(a, b)` in
-- `(op(Type), Type)`.
--
-- `PrePostPair` embeds the object `(s, t)` of `(op(Type), Type)` into
-- the category whose objects are profunctors `(op(Type), Type) -> Type)` and
-- whose morphisms are natural transformations.  For more context, see
-- `DualYonedaEmbed`, which is simply an alias for `PrePostPair`, but to
-- emphasize the similarities and differences between `PrePostPair` and
-- its paranatural-category-theoretic analogue `DiYonedaEmbed`.
public export
PrePostPair : Type -> Type -> ProfunctorSig
PrePostPair s t a b = (a -> s, t -> b)

public export
[PrePostPairProf] Profunctor (PrePostPair s t) where
  dimap mca mbd (mas, mtb) = (mas . mca, mbd . mtb)

-- `Iso s t a b` is a morphism from `(s, t)` to `(a, b)` in
-- `(Type, op(Type))`.
public export
Iso : Type -> Type -> Type -> Type -> Type
Iso s t a b = PrePostPair a b s t

public export
IsoContraProf : {0 s, t : Type} -> ContraProfunctor (Iso s t)
IsoContraProf {s} {t} =
  let _ = PrePostPairProf {s=t} {t=s} in
  MkProfunctor $
    \mca, mbd, msbat => swap $ dimap {f=(PrePostPair t s)} mca mbd $ swap msbat

-----------------------------------------------
---- Category of endoprofunctors on `Type` ----
-----------------------------------------------

-- We may view endoprofunctors on `Type` as forming a one-object category
-- whose only object is `Type`, whose morphisms are the endo-profunctors,
-- whose identity is the hom-profunctor, and which has a composition given by
-- the coend below.  (Furthermore, this forms a bicategory when we add as
-- two-cells the natural transformations between endo-profunctors.)

public export
EndoProfMorph : Type
EndoProfMorph = Type -> Type -> Type

public export
EndoProfId : EndoProfMorph
EndoProfId = HomProf

-- The profunctor whose coend is the composition of two endo-profunctors.
public export
EndoProfComposeProf :
  EndoProfMorph -> EndoProfMorph -> Type -> Type -> EndoProfMorph
EndoProfComposeProf q p e c d d' = (q e d, p d' c)

public export
EndoProfCompose : EndoProfMorph -> EndoProfMorph -> EndoProfMorph
EndoProfCompose q p e c = CoendBase $ EndoProfComposeProf q p e c

public export
EndoProfLeftId : (p : EndoProfMorph) -> {auto isP : Profunctor p} ->
  ProfNT (EndoProfCompose HomProf p) p
EndoProfLeftId p {isP} {a} {b} (c ** (mac, pcb)) = lmap mac pcb

public export
EndoProfRightId : (p : EndoProfMorph) ->
  ProfNT p (EndoProfCompose HomProf p)
EndoProfRightId p {a} {b} pab = (a ** (id, pab))

public export
EndoProfAssocLeft : (p, q, r : EndoProfMorph) ->
  ProfNT
    (EndoProfCompose p (EndoProfCompose q r))
    (EndoProfCompose (EndoProfCompose p q) r)
EndoProfAssocLeft p q r (c ** (pac, (d ** (qcd, rdb)))) =
  (d ** ((c ** (pac, qcd)), rdb))

public export
EndoProfAssocRight : (p, q, r : EndoProfMorph) ->
  ProfNT
    (EndoProfCompose (EndoProfCompose p q) r)
    (EndoProfCompose p (EndoProfCompose q r))
EndoProfAssocRight p q r (c ** ((d ** (pad, qdc)), rcb)) =
  (d ** (pad, (c ** (qdc, rcb))))

--------------------------------------
---- Endo-pro(co)monads on `Type` ----
--------------------------------------

public export
0 ProReturnSig : ProfunctorSig -> Type
ProReturnSig p = ProfNT EndoProfId p

public export
0 ProJoinSig : ProfunctorSig -> Type
ProJoinSig p = ProfNT (EndoProfCompose p p) p

interface Profunctor p => ProMonad p where
  proReturn : ProReturnSig p
  proJoin : ProJoinSig p

public export
0 ProEraseSig : ProfunctorSig -> Type
ProEraseSig p = ProfNT p EndoProfId

public export
0 ProDuplicateSig : ProfunctorSig -> Type
ProDuplicateSig p = ProfNT p (EndoProfCompose p p)

interface Profunctor p => ProComonad p where
  proErase : ProEraseSig p
  proDuplicate : ProDuplicateSig p

--------------------------------------------------
---- Bicategory of endo-profunctors on `Type` ----
--------------------------------------------------

public export
EndoProfVMorph : Type
EndoProfVMorph = EndoProfMorph

public export
EndoProfHMorph : EndoProfVMorph -> EndoProfVMorph -> Type
EndoProfHMorph = ProfNT

public export
EndoProfHId : (p : EndoProfVMorph) -> EndoProfHMorph p p
EndoProfHId = ProfNTid

public export
EndoProfHComp : {p, q, r : EndoProfVMorph} ->
  EndoProfHMorph q r -> EndoProfHMorph p q -> EndoProfHMorph p r
EndoProfHComp = ProfNTcomp

------------------------------------------------------------------
---- Functors in the bicategory of endo-profunctors on `Type` ----
------------------------------------------------------------------

public export
ProfBicatObj : Type
ProfBicatObj = EndoProfVMorph

public export
ProfBicatMorph : ProfBicatObj -> ProfBicatObj -> Type
ProfBicatMorph = EndoProfHMorph

public export
ProfBicatId : (p : ProfBicatObj) -> ProfBicatMorph p p
ProfBicatId = ProfNTid

public export
ProfBicatComp : {p, q, r : ProfBicatObj} ->
  ProfBicatMorph q r -> ProfBicatMorph p q -> ProfBicatMorph p r
ProfBicatComp = ProfNTcomp

-- The signature of the morphism-map component of a functor in the bicategory
-- of profunctors (i.e. the category whose objects are profunctors and whose
-- morphisms are natural transformations).
public export
ProfBicatMap : (ProfBicatObj -> ProfBicatObj) -> Type
ProfBicatMap pf = {p, q : Type -> Type -> Type} ->
  ProfNT p q -> ProfNT (pf p) (pf q)

-- The signature of the "return"/"unit" natural transformation of a monad in the
-- bicategory of profunctors.
public export
ProfBicatReturn : (ProfBicatObj -> ProfBicatObj) -> Type
ProfBicatReturn pf = (p : Type -> Type -> Type) -> ProfNT p (pf p)

-- The signature of the "join"/"multiply" natural transformation of a monad in
-- the bicategory of profunctors.
public export
ProfBicatJoin : (ProfBicatObj -> ProfBicatObj) -> Type
ProfBicatJoin pf = (p : Type -> Type -> Type) -> ProfNT (pf (pf p)) (pf p)

-- The signature of the "extract"/"erase"/"counit" natural transformation of a
-- comonad in the bicategory of profunctors.
public export
ProfBicatExtract : (ProfBicatObj -> ProfBicatObj) -> Type
ProfBicatExtract pf = (p : Type -> Type -> Type) -> ProfNT (pf p) p

-- The signature of the "duplicate"/"comultiply" natural transformation of a
-- comonad in the bicategory of profunctors.
public export
ProfBicatDuplicate : (ProfBicatObj -> ProfBicatObj) -> Type
ProfBicatDuplicate pf = (p : Type -> Type -> Type) -> ProfNT (pf p) (pf (pf p))

----------------------------
---- Profunctor algebra ----
----------------------------

public export
ProfCoalg : (Type -> Type) -> ProfunctorSig
ProfCoalg f a b = a -> f b

public export
ProfDialg : (Type -> Type) -> (Type -> Type) -> ProfunctorSig
ProfDialg = NatTransProf

public export
ProfAlg : ProfunctorSig -> (Type -> Type) -> Type
ProfAlg p f = ProfNT (ProfCoalg f) (EndoProfCompose p $ ProfCoalg f)

public export
ProfConstAlg : ProfunctorSig -> Type -> Type
ProfConstAlg p x = p x x

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
---- (`Type`-enriched) copresheaves on the twisted-arrow category of `Type` ----
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

public export
TwArrCoprSig : Type
TwArrCoprSig = (x, y : Type) -> (x -> y) -> Type

-- A presheaf on a category `C` (enriched over `Type`) is a functor
-- from `op(C)` to `Type`.  A presheaf on the twisted-arrow category
-- of a category `C` is therefore a functor from `op(Tw(C))` to `Type`.
--
-- However, we have `op(Tw(C)) ~=~ Tw(op(C))`, so a presheaf on the
-- twisted-arrow category of `C` may equivalently be viewed as a copresheaf
-- on the twisted-arrow category of `op(C)`.
--
-- Thus we express the signature of a presheaf on the twisted-arrow category
-- of `Type` as a copresheaf on the twisted-arrow category of `op(Type)`.
public export
TwArrPreshfSig : Type
TwArrPreshfSig = (x, y : Type) -> (y -> x) -> Type

public export
TwArrCoprDimapSig : TwArrCoprSig -> Type
TwArrCoprDimapSig p =
  (s, t, a, b : Type) -> (mst : s -> t) -> (mas : a -> s) -> (mtb : t -> b) ->
  p s t mst -> p a b (mtb . mst . mas)

public export
TwArrPreshfContraDimapSig : TwArrPreshfSig -> Type
TwArrPreshfContraDimapSig p =
  (s, t, a, b : Type) -> (mts : t -> s) -> (msa : s -> a) -> (mbt : b -> t) ->
  p s t mts -> p a b (msa . mts . mbt)

public export
TwArrCoprCompose : TwArrCoprSig -> TwArrCoprSig -> TwArrCoprSig
TwArrCoprCompose q p x z mxz =
  (y : Type ** mp : (x -> y, y -> z) **
   (FunExtEq (snd mp . fst mp) mxz, q x y (fst mp), p y z (snd mp)))

public export
TwArrPreshfCompose : TwArrPreshfSig -> TwArrPreshfSig -> TwArrPreshfSig
TwArrPreshfCompose q p x z mzx =
  (y : Type ** mp : (y -> x, z -> y) **
   (FunExtEq (fst mp . snd mp) mzx, q x y (fst mp), p y z (snd mp)))

public export
TwArrCoprComposeDimap : (q, p : TwArrCoprSig) ->
  TwArrCoprDimapSig q -> TwArrCoprDimapSig p ->
  TwArrCoprDimapSig (TwArrCoprCompose q p)
TwArrCoprComposeDimap q p qdm pdm s t a b mst mas mtb
  (y ** (msy, myt) ** (comm, qsy, pyt)) =
    (y ** (msy . mas, mtb . myt) **
     (\fext => funExt $ \ea => cong mtb $ fcong {x=(mas ea)} $ comm fext,
      qdm s y a y msy mas id qsy,
      pdm y t y b myt id mtb pyt))

public export
TwArrPreshfComposeContraDimap : (q, p : TwArrPreshfSig) ->
  TwArrPreshfContraDimapSig q -> TwArrPreshfContraDimapSig p ->
  TwArrPreshfContraDimapSig (TwArrPreshfCompose q p)
TwArrPreshfComposeContraDimap q p qdm pdm s t a b mts msa mbt
  (y ** (mys, mty) ** (comm, qsy, pyt)) =
    (y ** (msa . mys, mty . mbt) **
     (\fext => funExt $ \eb => cong msa $ fcong {x=(mbt eb)} $ comm fext,
      qdm s y a y mys msa id qsy,
      pdm y t y b mty id mbt pyt))

public export
TwArrCoprNatTrans : TwArrCoprSig -> TwArrCoprSig -> Type
TwArrCoprNatTrans p q =
  (x, y : Type) -> (mxy : x -> y) -> p x y mxy -> q x y mxy

public export
TwArrPreshfNatTrans : TwArrPreshfSig -> TwArrPreshfSig -> Type
TwArrPreshfNatTrans p q =
  (x, y : Type) -> (myx : y -> x) -> p x y myx -> q x y myx

public export
TwArrCoprNatTransId : (p : TwArrCoprSig) -> TwArrCoprNatTrans p p
TwArrCoprNatTransId p x y mxy = Prelude.id

public export
TwArrPreshfNatTransId : (p : TwArrPreshfSig) -> TwArrPreshfNatTrans p p
TwArrPreshfNatTransId p x y myx = Prelude.id

public export
TwArrCoprNatTransVcomp : (p, q, r : TwArrCoprSig) ->
  TwArrCoprNatTrans q r -> TwArrCoprNatTrans p q -> TwArrCoprNatTrans p r
TwArrCoprNatTransVcomp p q r beta alpha x y mxy = beta x y mxy . alpha x y mxy

public export
TwArrCoprNatTransHcomp : (p, p', q, q' : TwArrCoprSig) ->
  TwArrCoprNatTrans q q' -> TwArrCoprNatTrans p p' ->
  TwArrCoprNatTrans (TwArrCoprCompose q p) (TwArrCoprCompose q' p')
TwArrCoprNatTransHcomp p p' q q' beta alpha x z mxz
  (y ** (mxy, myz) ** (comm, qxy, pyz)) =
    (y ** (mxy, myz) ** (comm, beta x y mxy qxy, alpha y z myz pyz))

public export
TwArrPreshfNatTransVcomp : (p, q, r : TwArrPreshfSig) ->
  TwArrPreshfNatTrans q r -> TwArrPreshfNatTrans p q -> TwArrPreshfNatTrans p r
TwArrPreshfNatTransVcomp p q r beta alpha x y myx = beta x y myx . alpha x y myx

public export
TwArrPreshfNatTransHcomp : (p, p', q, q' : TwArrPreshfSig) ->
  TwArrPreshfNatTrans q q' -> TwArrPreshfNatTrans p p' ->
  TwArrPreshfNatTrans (TwArrPreshfCompose q p) (TwArrPreshfCompose q' p')
TwArrPreshfNatTransHcomp p p' q q' beta alpha x z mzx
  (y ** (myx, mzy) ** (comm, qxy, pyz)) =
    (y ** (myx, mzy) ** (comm, beta x y myx qxy, alpha y z mzy pyz))

public export
TwArrCoprEmbedCopreshf : (Type -> Type) -> TwArrCoprSig
TwArrCoprEmbedCopreshf f x y mxy = f y

-- Embed a copresheaf on `Type` into the category of presheaves on the
-- twisted-arrow category of `Type`.
public export
TwArrPreshfEmbedCopreshf : (Type -> Type) -> TwArrPreshfSig
TwArrPreshfEmbedCopreshf f x y myx = f x

public export
TwArrCoprEmbedCopreshfMap : (f : Type -> Type) -> Functor f ->
  TwArrCoprDimapSig (TwArrCoprEmbedCopreshf f)
TwArrCoprEmbedCopreshfMap f fm s t a b mst mas mtb = map {f} mtb

public export
TwArrCoprEmbedCopreshfFMap : (f, g : Type -> Type) ->
  Functor f -> Functor g ->
  NaturalTransformation f g ->
  TwArrCoprNatTrans
    (TwArrCoprEmbedCopreshf f)
    (TwArrCoprEmbedCopreshf g)
TwArrCoprEmbedCopreshfFMap f g fm gm alpha a b mab efb = alpha b efb

public export
TwArrPreshfEmbedCopreshfMap : (f : Type -> Type) -> Functor f ->
  TwArrPreshfContraDimapSig (TwArrPreshfEmbedCopreshf f)
TwArrPreshfEmbedCopreshfMap f fm s t a b mts msa mbt = map {f} msa

public export
TwArrCoprEmbedPreshf : (Type -> Type) -> TwArrCoprSig
TwArrCoprEmbedPreshf f x y mxy = f x

-- Embed a presheaf on `Type` into the category of presheaves on the
-- twisted-arrow category of `Type`.
public export
TwArrPreshfEmbedPreshf : (Type -> Type) -> TwArrPreshfSig
TwArrPreshfEmbedPreshf f x y myx = f y

public export
TwArrPreshfEmbedCopreshfFMap : (f, g : Type -> Type) ->
  Functor f -> Functor g ->
  NaturalTransformation f g ->
  TwArrPreshfNatTrans
    (TwArrPreshfEmbedPreshf f)
    (TwArrPreshfEmbedPreshf g)
TwArrPreshfEmbedCopreshfFMap f g fm gm alpha a b mba efb = alpha b efb

public export
TwArrCoprEmbedPreshfMap : (f : Type -> Type) -> Contravariant f ->
  TwArrCoprDimapSig (TwArrCoprEmbedPreshf f)
TwArrCoprEmbedPreshfMap f fm s t a b mst mas mtb = contramap {f} mas

public export
TwArrCoprEmbedPreshfFMap : (f, g : Type -> Type) ->
  Contravariant f -> Contravariant g ->
  NaturalTransformation f g ->
  TwArrCoprNatTrans
    (TwArrCoprEmbedCopreshf f)
    (TwArrCoprEmbedCopreshf g)
TwArrCoprEmbedPreshfFMap f g fcm gcm alpha a b mab efb = alpha b efb

public export
TwArrPreshfEmbedPreshfMap : (f : Type -> Type) -> Contravariant f ->
  TwArrPreshfContraDimapSig (TwArrPreshfEmbedPreshf f)
TwArrPreshfEmbedPreshfMap f fm s t a b mts msa mbt = contramap {f} mbt

public export
TwArrPreshfEmbedPreshfFMap : (f, g : Type -> Type) ->
  Contravariant f -> Contravariant g ->
  NaturalTransformation f g ->
  TwArrPreshfNatTrans
    (TwArrPreshfEmbedPreshf f)
    (TwArrPreshfEmbedPreshf g)
TwArrPreshfEmbedPreshfFMap f g fcm gcm alpha a b mba efb = alpha b efb

public export
TwArrCoprEmbedProf : (Type -> Type -> Type) -> TwArrCoprSig
TwArrCoprEmbedProf p x y mxy = p x y

-- Embed an endoprofunctor (AKA difunctor) on `Type` into the category of
-- presheaves on the twisted-arrow category of `Type`.
public export
TwArrPreshfEmbedProf : (Type -> Type -> Type) -> TwArrPreshfSig
TwArrPreshfEmbedProf p x y myx = p y x

public export
TwArrCoprEmbedDimap : (p : Type -> Type -> Type) -> Profunctor p ->
  TwArrCoprDimapSig (TwArrCoprEmbedProf p)
TwArrCoprEmbedDimap p pdm s t a b mst =
  dimap {f=p} {a=s} {b=t} {c=a} {d=b}

public export
TwArrPreshfEmbedDimap : (p : Type -> Type -> Type) -> Profunctor p ->
  TwArrPreshfContraDimapSig (TwArrPreshfEmbedProf p)
TwArrPreshfEmbedDimap p pdm s t a b mts =
  flip $ dimap {f=p} {a=t} {b=s} {c=b} {d=a}

public export
TwArrCoprEmbedProfFMap : (p, q : Type -> Type -> Type) ->
  Profunctor p -> Profunctor q ->
  ProfNT p q ->
  TwArrCoprNatTrans
    (TwArrCoprEmbedProf p)
    (TwArrCoprEmbedProf q)
TwArrCoprEmbedProfFMap p q pdm qdm alpha x y mxy epxy = alpha epxy

public export
TwArrPreshfEmbedProfFMap : (p, q : Type -> Type -> Type) ->
  Profunctor p -> Profunctor q ->
  ProfNT p q ->
  TwArrPreshfNatTrans
    (TwArrPreshfEmbedProf p)
    (TwArrPreshfEmbedProf q)
TwArrPreshfEmbedProfFMap p q pdm qdm alpha x y myx epyx = alpha epyx

public export
TwArrCoprId : TwArrCoprSig
TwArrCoprId = TwArrCoprEmbedProf HomProf

public export
TwArrPreshfId : TwArrPreshfSig
TwArrPreshfId = TwArrPreshfEmbedProf HomProf

public export
TwArrCoprIdMap : TwArrCoprDimapSig TwArrCoprId
TwArrCoprIdMap = TwArrCoprEmbedDimap HomProf HomProfProfunctor

public export
TwArrPreshfIdMap : TwArrPreshfContraDimapSig TwArrPreshfId
TwArrPreshfIdMap = TwArrPreshfEmbedDimap HomProf HomProfProfunctor

-- Embed an object of `Type` into the category of copresheaves on
-- the twisted-arrow category of `Type`.  This is the object-map component
-- of the object-map component of the embedding functor from `Type` to
-- the category of copresheaves on the twisted-arrow category of `Type`,
-- which composes the embedding of presheaves on `Type` into copresheaves
-- on the twisted-arrow category of `Type` after the (contravariant)
-- Yoneda embedding of `Type` into presheaves on `Type`.
public export
TwCoprEmbedObjOmap : Type -> TwArrCoprSig
TwCoprEmbedObjOmap x a b mab = a -> x

-- The object-map component of the embedding of an object of `op(Type)` into
-- the category of copresheaves on the twisted-arrow category of `Type`,
-- which composes the embedding of copresheaves on `Type` into copresheaves
-- on the twisted-arrow category of `Type` after the Yoneda embedding of
-- `op(Type)` into copresheaves on `Type`.
public export
TwCoprEmbedOpObjOmap : Type -> TwArrCoprSig
TwCoprEmbedOpObjOmap x a b mab = x -> b

-- This is the morphism-map component of the object-map component of the
-- embedding functor from `Type` to the category of copresheaves on the
-- twisted-arrow category of `Type`.
public export
TwCoprEmbedObjDimap :
  (x : Type) -> TwArrCoprDimapSig (TwCoprEmbedObjOmap x)
TwCoprEmbedObjDimap x s t a b mst mas mtb msx = msx . mas

-- This is the morphism-map component of the object-map component of the
-- embedding functor from `op(Type)` to the category of copresheaves on the
-- twisted-arrow category of `Type`.
public export
TwCoprEmbedOpObjDimap :
  (x : Type) -> TwArrCoprDimapSig (TwCoprEmbedOpObjOmap x)
TwCoprEmbedOpObjDimap x s t a b mst mas mtb mxt = mtb . mxt

-- The morphism-map component of the embedding functor from `Type` to the
-- category of copresheaves on the twisted-arrow category of `Type` (whose
-- object-map component is `TwCoprEmbedObjOmap` /
-- `TwCoprEmbedObjDimap`).
public export
TwCoprEmbedMor :
  (x, y : Type) -> (mxy : x -> y) ->
  TwArrCoprNatTrans (TwCoprEmbedObjOmap x) (TwCoprEmbedObjOmap y)
TwCoprEmbedMor x y mxy a b mab max = mxy . max

-- The morphism-map component of the embedding functor from `op(Type)` to the
-- category of copresheaves on the twisted-arrow category of `Type` (whose
-- object-map component is `TwCoprEmbedOpObjOmap` /
-- `TwCoprEmbedOpObjDimap`).
public export
TwCoprEmbedOpMor :
  (x, y : Type) -> (mxy : y -> x) ->
  TwArrCoprNatTrans (TwCoprEmbedOpObjOmap x) (TwCoprEmbedOpObjOmap y)
TwCoprEmbedOpMor x y myx a b mab mxb = mxb . myx

-- Embed an object of `Type` into the category of presheaves on
-- the twisted-arrow category of `Type`.  This is the object-map component
-- of the object-map component of the embedding functor from `Type` to
-- the category of presheaves on the twisted-arrow category of `Type`,
-- which composes the embedding of presheaves on `Type` into presheaves
-- on the twisted-arrow category of `Type` after the Yoneda embedding of
-- `Type` into presheaves on `Type`.
public export
TwPreshfEmbedObjOmap : Type -> TwArrPreshfSig
TwPreshfEmbedObjOmap x a b mba = b -> x

-- The object-map component of the embedding of an object of `op(Type)` into
-- the category of presheaves on the twisted-arrow category of `Type`,
-- which composes the embedding of copresheaves on `Type` into presheaves
-- on the twisted-arrow category of `Type` after the Yoneda embedding of
-- `op(Type)` into copresheaves on `Type`.
public export
TwPreshfEmbedOpObjOmap : Type -> TwArrPreshfSig
TwPreshfEmbedOpObjOmap x a b mba = x -> a

-- This is the morphism-map component of the object-map component of the
-- embedding functor from `Type` to the category of presheaves on the
-- twisted-arrow category of `Type`.
public export
TwPreshfEmbedObjContraDimap :
  (x : Type) -> TwArrPreshfContraDimapSig (TwPreshfEmbedObjOmap x)
TwPreshfEmbedObjContraDimap x s t a b mts msa mbt mtx = mtx . mbt

-- This is the morphism-map component of the object-map component of the
-- embedding functor from `op(Type)` to the category of presheaves on the
-- twisted-arrow category of `Type`.
public export
TwPreshfEmbedOpObjContraDimap :
  (x : Type) -> TwArrPreshfContraDimapSig (TwPreshfEmbedOpObjOmap x)
TwPreshfEmbedOpObjContraDimap x s t a b mts msa mbt mxs = msa . mxs

-- The morphism-map component of the embedding functor from `Type` to the
-- category of presheaves on the twisted-arrow category of `Type` (whose
-- object-map component is `TwPreshfEmbedObjOmap` /
-- `TwPreshfEmbedObjContraDimap`).
public export
TwPreshfEmbedMor :
  (x, y : Type) -> (mxy : x -> y) ->
  TwArrPreshfNatTrans (TwPreshfEmbedObjOmap x) (TwPreshfEmbedObjOmap y)
TwPreshfEmbedMor x y mxy a b mba mbx = mxy . mbx

-- The morphism-map component of the embedding functor from `op(Type)` to the
-- category of presheaves on the twisted-arrow category of `Type` (whose
-- object-map component is `TwPreshfEmbedOpObjOmap` /
-- `TwPreshfEmbedOpObjContraDimap`).
public export
TwPreshfEmbedOpMor :
  (x, y : Type) -> (myx : y -> x) ->
  TwArrPreshfNatTrans (TwPreshfEmbedOpObjOmap x) (TwPreshfEmbedOpObjOmap y)
TwPreshfEmbedOpMor x y myx a b mba mxa = mxa . myx

-- Embed an object of the twisted-arrow category of `Type` into the category
-- of presheaves on the twisted-arrow category of `Type`.  This is the simply
-- the object-map component of the object-map component of the Yoneda embedding
-- of the twisted-arrow category of `Type` into its category of presheaves.
public export
TwPreshfEmbedArrOmap : (x, y : Type) -> (x -> y) -> TwArrPreshfSig
TwPreshfEmbedArrOmap x y mxy a b mba =
  -- A twisted-arrow morphism from mxy to mba.
  (mp : (b -> x, y -> a) ** FunExtEq (snd mp . mxy . fst mp) mba)

-- The morphism-map component of the object-map component of the Yoneda
-- embedding of the twisted-arrow category of `Type`.
public export
TwPreshfEmbedArrContraDimap : (x, y : Type) -> (mxy : x -> y) ->
  TwArrPreshfContraDimapSig (TwPreshfEmbedArrOmap x y mxy)
TwPreshfEmbedArrContraDimap x y mxy s t a b mts msa mbt ((mtx, mys) ** comm) =
  ((mtx . mbt, msa . mys) **
   \fext => funExt $ \eb => cong msa $ fcong {x=(mbt eb)} $ comm fext)

-- The morphism-map component of the Yoneda embedding of the twisted-arrow
-- category of `Type`.
public export
TwPreshfEmbedArrFmap : (x, y, x', y' : Type) ->
  (mxy : x -> y) -> (mxy' : x' -> y') ->
  (twmx : x -> x') -> (twmy : y' -> y) ->
  (twmcomm : ExtEq (twmy . mxy' . twmx) mxy) ->
  TwArrPreshfNatTrans
    (TwPreshfEmbedArrOmap x y mxy)
    (TwPreshfEmbedArrOmap x' y' mxy')
TwPreshfEmbedArrFmap x y x' y' mxy mxy' twmx twmy twmcomm a b mba
  ((mbx, mya) ** mcomm) =
    ((twmx . mbx, mya . twmy) **
     \fext => funExt $
      \eb => rewrite (twmcomm $ mbx eb) in fcong {x=eb} $ mcomm fext)

-- Embed an object of the opposite of the twisted-arrow category of `Type` into
-- the category of copresheaves on the twisted-arrow category of `Type`.  This
-- is the simply the object-map component of the object-map component of the
-- Yoneda embedding of the opposite of the twisted-arrow category of `Type`
-- into the category of copresheaves on the twisted-arrow category of `Type`.
public export
TwCoprEmbedOpArrOmap : (x, y : Type) -> (x -> y) -> TwArrCoprSig
TwCoprEmbedOpArrOmap x y mxy a b mab =
  -- A twisted-arrow morphism from mxy to mab (i.e. an op-twisted-arrow
  -- morphism from mxy to mab).
  (mp : (a -> x, y -> b) ** FunExtEq (snd mp . mxy . fst mp) mab)

-- The morphism-map component of the object-map component of the Yoneda
-- embedding of the opposite of the twisted-arrow category of `Type`.
public export
TwCoprEmbedOpArrDimap : (x, y : Type) -> (mxy : x -> y) ->
  TwArrCoprDimapSig (TwCoprEmbedOpArrOmap x y mxy)
TwCoprEmbedOpArrDimap x y mxy s t a b mst mas mtb ((msx, myt) ** comm) =
  ((msx . mas, mtb . myt) **
   \fext => funExt $ \ea => cong mtb $ fcong {x=(mas ea)} $ comm fext)

-- The morphism-map component of the Yoneda embedding of the opposite
-- of the twisted-arrow category of `Type`.
public export
TwCoprEmbedOpArrFmap : (x, y, x', y' : Type) ->
  (mxy : x -> y) -> (mxy' : x' -> y') ->
  (twmx : x -> x') -> (twmy : y' -> y) ->
  (twmcomm : ExtEq (twmy . mxy' . twmx) mxy) ->
  TwArrCoprNatTrans
    (TwCoprEmbedOpArrOmap x y mxy)
    (TwCoprEmbedOpArrOmap x' y' mxy')
TwCoprEmbedOpArrFmap x y x' y' mxy mxy' twmx twmy twmcomm a b mab
  ((max, myb) ** mcomm) =
    ((twmx . max, myb . twmy) **
     \fext => funExt $
      \ea => rewrite (twmcomm $ max ea) in fcong {x=ea} $ mcomm fext)

-------------------------------------------
-------------------------------------------
---- Dependent polynomial endofunctors ----
-------------------------------------------
-------------------------------------------

-- The dependent product functor induced by the given morphism.
-- Right adjoint to the base change functor.
public export
DepProdF : {a, b : Type} -> (a -> b) -> SliceFunctor a b
DepProdF {a} {b} f sla elemb =
  Pi {a=(PreImage f elemb)} (BaseChangeF fst0 sla)

-- The dependent coproduct functor induced by the given morphism.
-- Left adjoint to the base change functor.
public export
DepCoprodF : {a, b : Type} -> (a -> b) -> SliceFunctor a b
DepCoprodF {a} {b} f sla elemb =
  Sigma {a=(PreImage f elemb)} (BaseChangeF fst0 sla)

-- A dependent polynomial functor can be defined as a composition of
-- a base change followed by a dependent product followed by a dependent
-- coproduct.
public export
DepPolyF : {w, x, y, z : Type} ->
  (x -> w) -> (x -> y) -> (y -> z) -> SliceFunctor w z
DepPolyF {w} {x} {y} {z} fxw predyx predzy =
  DepCoprodF {a=y} {b=z} predzy
  . DepProdF {a=x} {b=y} predyx
  . BaseChangeF fxw

------------------------------------------------------------------------------
---- Dependent polynomial functors using predicates rather than morphisms ----
------------------------------------------------------------------------------

-- These are Idris `SliceFunctor` versions of the "General Theory of
-- Interaction" style which defines polynomial functors using dependent
-- sets ("positions" and "directions"), extended to the dependent
-- (slice-category) case, whereas the ones in the previous section (`DepPolyF`)
-- correspond to a W-type-style definition.

-- Dependent product in terms of a predicate instead of a morphism.
public export
PredDepProdF : {a : Type} -> (p : SliceObj a) -> SliceFunctor (Sigma {a} p) a
PredDepProdF {a} p slp elema =
  Pi {a=(p elema)} (BaseChangeF (MkDPair elema) slp)

-- Dependent coproduct in terms of a predicate instead of a morphism.
public export
PredDepCoprodF : {a : Type} -> (p : SliceObj a) -> SliceFunctor (Sigma {a} p) a
PredDepCoprodF {a} p slp elema =
  Sigma {a=(p elema)} (BaseChangeF (MkDPair elema) slp)

-- A dependent polynomial functor in terms of predicates instead of morphisms.
public export
PredDepPolyF : {parambase, posbase : Type} ->
  (posdep : SliceObj posbase) ->
  (dirdep : SliceObj (Sigma posdep)) ->
  (assign : Sigma dirdep -> parambase) ->
  SliceFunctor parambase posbase
PredDepPolyF {parambase} {posbase} posdep dirdep assign =
  PredDepCoprodF {a=posbase} posdep
  . PredDepProdF {a=(Sigma posdep)} dirdep
  . BaseChangeF assign

-- The same function as `PredDepPolyF`, but compressed into a single computation
-- purely as documentation for cases in which this might be more clear.
public export
PredDepPolyF' : {parambase, posbase : Type} ->
  (posdep : SliceObj posbase) ->
  (dirdep : SliceObj (Sigma posdep)) ->
  (assign : Sigma dirdep -> parambase) ->
  SliceFunctor parambase posbase
PredDepPolyF' posdep dirdep assign parampred posi =
  (pos : posdep posi **
   ((dir : dirdep (posi ** pos)) -> parampred (assign ((posi ** pos) ** dir))))

public export
PredDepPolyF'_correct : {parambase, posbase : Type} ->
  (posdep : SliceObj posbase) ->
  (dirdep : SliceObj (Sigma posdep)) ->
  (assign : Sigma dirdep -> parambase) ->
  (parampred : SliceObj parambase) ->
  (posi : posbase) ->
  PredDepPolyF posdep dirdep assign parampred posi =
    PredDepPolyF' posdep dirdep assign parampred posi
PredDepPolyF'_correct posdep dirdep assign parampred posi = Refl

-- The morphism-map component of the functor induced by a `PredDepPolyF`.
public export
PredDepPolyFMap : {parambase, posbase : Type} ->
  (posdep : SliceObj posbase) ->
  (dirdep : SliceObj (Sigma posdep)) ->
  (assign : Sigma dirdep -> parambase) ->
  (p, p' : SliceObj parambase) ->
  SliceMorphism p p' ->
  SliceMorphism
    (PredDepPolyF posdep dirdep assign p)
    (PredDepPolyF posdep dirdep assign p')
PredDepPolyFMap posdep dirdep assign p p' m posi (pos ** dir) =
  (pos ** \di => m (assign ((posi ** pos) ** di)) (dir di))

public export
PredDepPolyEndoF : {base : Type} ->
  (posdep : SliceObj base) ->
  (dirdep : SliceObj (Sigma posdep)) ->
  (assign : Sigma dirdep -> base) ->
  SliceFunctor base base
PredDepPolyEndoF {base} = PredDepPolyF {parambase=base} {posbase=base}

-------------------------------
---- Dependent (co)algebra ----
-------------------------------

public export
SliceAlg : {a : Type} -> SliceEndofunctor a -> SliceObj a -> Type
SliceAlg sf sa = SliceMorphism (sf sa) sa

public export
SliceInitFromUniv : {a : Type} -> (sf : SliceEndofunctor a) -> SliceObj a
SliceInitFromUniv {a} sf x = (sa : SliceObj a) -> SliceAlg sf sa -> sa x

public export
SliceCoalg : {a : Type} -> SliceEndofunctor a -> SliceObj a -> Type
SliceCoalg sf sa = SliceMorphism sa (sf sa)

public export
SliceTermFromUniv : {a : Type} -> (sf : SliceEndofunctor a) -> SliceObj a
SliceTermFromUniv {a} sf x = (sa : SliceObj a ** (SliceCoalg sf sa, sa x))

-- The slice-category version of `TranslateFunctor`.
public export
data SliceTranslateF : {a : Type} ->
    SliceEndofunctor a -> SliceObj a -> SliceEndofunctor a where
  InSlV : {a : Type} -> {f : SliceEndofunctor a} -> {0 sv, sa : SliceObj a} ->
    {ea : a} -> sv ea -> SliceTranslateF {a} f sv sa ea
  InSlC : {a : Type} -> {f : SliceEndofunctor a} -> {0 sv, sa : SliceObj a} ->
    {ea : a} -> f sa ea -> SliceTranslateF {a} f sv sa ea

public export
SliceTrEitherF : {a : Type} -> SliceEndofunctor a -> SliceEndofunctor a
SliceTrEitherF {a} f sa = SliceTranslateF {a} f sa sa

-- The slice-category version of `ScaleFunctor`.
public export
data SliceScaleF : {0 a : Type} ->
    SliceEndofunctor a -> SliceObj a -> SliceEndofunctor a where
  InSlS : {0 a : Type} -> {f : SliceEndofunctor a} -> {0 sv, sa : SliceObj a} ->
    {ea : a} -> sv ea -> f sa ea -> SliceScaleF {a} f sv sa ea

-- The free monad in a slice category.
public export
data SliceFreeM : {a : Type} -> SliceEndofunctor a -> SliceEndofunctor a where
  InSlF : {a : Type} -> {f : SliceEndofunctor a} -> {sa : SliceObj a} ->
    SliceAlg {a} (SliceTranslateF {a} f sa) (SliceFreeM {a} f sa)

public export
InSlFv : {a : Type} -> {f : SliceEndofunctor a} -> {sa : SliceObj a} ->
  {ea : a} -> sa ea -> SliceFreeM {a} f sa ea
InSlFv {a} {f} {sa} {ea} sea =
  InSlF {a} {f} {sa} ea
    (InSlV {a} {f} {sv=sa} {sa=(SliceFreeM {a} f sa)} {ea} sea)

public export
InSlFc : {a : Type} -> {f : SliceEndofunctor a} -> {sa : SliceObj a} ->
  {ea : a} -> f (SliceFreeM {a} f sa) ea -> SliceFreeM {a} f sa ea
InSlFc {a} {f} {sa} {ea} fsea =
  InSlF {a} {f} {sa} ea
    (InSlC {a} {f} {sv=sa} {sa=(SliceFreeM {a} f sa)} {ea} fsea)

-- The signature of the "eval" universal morphism for "SliceFreeM f".
public export
SliceFreeFEval : {a : Type} -> SliceEndofunctor a -> Type
SliceFreeFEval {a} f =
  (sv, sa : SliceObj a) -> SliceMorphism {a} sv sa -> SliceAlg f sa ->
  SliceMorphism {a} (SliceFreeM f sv) sa

public export
SliceFreeFEvalF : {a : Type} -> SliceEndofunctor a -> Type
SliceFreeFEvalF {a} f =
  (sv, sa : SliceObj a) -> SliceMorphism {a} sv sa -> SliceAlg f sa ->
  SliceMorphism {a} (f $ SliceFreeM f sv) sa

-- The type of the slice-category free monad's return.
public export
SliceFreeReturn : {a : Type} -> SliceEndofunctor a -> Type
SliceFreeReturn {a} f =
  SliceNatTrans {x=a} {y=a}
    (SliceIdF a)
    (SliceFreeM f)

-- The type of the slice-category free monad's join.
public export
SliceFreeJoin : {a : Type} -> SliceEndofunctor a -> Type
SliceFreeJoin {a} f =
  SliceNatTrans {x=a} {y=a}
    (SliceFreeM f . SliceFreeM f)
    (SliceFreeM f)

public export
sliceFreeReturn : {a : Type} -> {f : SliceEndofunctor a} -> SliceFreeReturn f
sliceFreeReturn {a} {f} sl ea = InSlFv {ea}

-- If we can define a catamorphism, then we can define join.
public export
sliceFreeJoin : {a : Type} -> {f : SliceEndofunctor a} ->
  SliceFreeFEval f -> SliceFreeJoin f
sliceFreeJoin {a} {f} cata sl =
  cata (SliceFreeM f sl) (SliceFreeM f sl) (\_ => id) (\_ => InSlFc)

public export
sliceFreeBindFromEval : {c : Type} ->
  (f : SliceEndofunctor c) -> (eval : SliceFreeFEval f) ->
  SliceBind (SliceFreeM f)
sliceFreeBindFromEval {c} f eval x y mxfy =
  eval x (SliceFreeM f y) mxfy (\ea => InSlFc {sa=y} {ea})

public export
SliceMu : {a : Type} -> SliceEndofunctor a -> SliceObj a
SliceMu {a} f = SliceFreeM {a} f (const Void)

public export
outSlMu : {a : Type} -> (f : SliceEndofunctor a) -> SliceCoalg f (SliceMu f)
outSlMu {a} f ea (InSlF ea $ InSlV v) = void v
outSlMu {a} f ea (InSlF ea $ InSlC t) = t

-- The type of catamorphisms in slice categories.
public export
SliceCata : {a : Type} -> SliceEndofunctor a -> Type
SliceCata {a} f =
  (sa : SliceObj a) -> SliceAlg f sa -> SliceMorphism {a} (SliceMu f) sa

-- The cofree comonad in a slice category.
public export
data SliceCofreeCM : {a : Type} -> SliceEndofunctor a -> SliceEndofunctor a
    where
  InSlCF : {a : Type} -> {f : SliceEndofunctor a} -> {sa : SliceObj a} ->
    -- "Inf (SliceAlg {a} (SliceScaleF {a} f sa) (SliceCofreeCM {a} f sa))"
    (ea : a) ->
    Inf (SliceScaleF {a} f sa (SliceCofreeCM {a} f sa) ea) ->
    SliceCofreeCM {a} f sa ea

-- The type of cofree anamorphisms in slice categories.
public export
SliceCofreeFTrace : {a : Type} -> SliceEndofunctor a -> Type
SliceCofreeFTrace {a} f =
  (sl, sa : SliceObj a) -> SliceMorphism {a} sa sl -> SliceCoalg f sa ->
  SliceMorphism {a} sa (SliceCofreeCM f sl)

public export
SliceCofreeFTraceF : {a : Type} -> SliceEndofunctor a -> Type
SliceCofreeFTraceF {a} f =
  (sl, sa : SliceObj a) -> SliceMorphism {a} sa sl -> SliceCoalg f sa ->
  SliceMorphism {a} sa (f $ SliceCofreeCM f sl)

-- The type of the slice-category cofree comonad's erase.
public export
SliceCofreeErase : {a : Type} -> SliceEndofunctor a -> Type
SliceCofreeErase {a} f =
  SliceNatTrans {x=a} {y=a}
    (SliceCofreeCM f)
    (SliceIdF a)

-- The type of the slice-category cofree comonad's duplicate.
public export
SliceCofreeDuplicate : {a : Type} -> SliceEndofunctor a -> Type
SliceCofreeDuplicate {a} f =
  SliceNatTrans {x=a} {y=a}
    (SliceCofreeCM f)
    (SliceCofreeCM f . SliceCofreeCM f)

public export
sliceCofreeErase : {a : Type} -> {f : SliceEndofunctor a} -> SliceCofreeErase f
sliceCofreeErase {a} {f} sl ea (InSlCF ea (InSlS sea fea)) = sea

public export
SliceNu : {a : Type} -> SliceEndofunctor a -> SliceObj a
SliceNu {a} f = SliceCofreeCM {a} f (const Unit)

public export
InSliceNu : {a : Type} -> (sf : SliceEndofunctor a) ->
  SliceMorphism {a} (sf (SliceNu {a} sf)) (SliceNu {a} sf)
InSliceNu {a} sf ea sfn =
  InSlCF {a} {f=sf} {sa=(const Unit)} ea $
    InSlS {a} {f=sf} {sv=(const Unit)} {sa=(SliceNu {a} sf)} () sfn

-- The type of anamorphisms in slice categories.
public export
SliceAna : {a : Type} -> SliceEndofunctor a -> Type
SliceAna {a} f =
  (sa : SliceObj a) -> SliceCoalg f sa -> SliceMorphism {a} sa (SliceNu f)

-----------------------------
---- (Co)algebra objects ----
-----------------------------

export
SliceAlgObj : {0 c : Type} -> SliceEndofunctor c -> SliceEndofunctor c
SliceAlgObj {c} f sa = SliceHom (f sa) sa

export
SliceCoalgObj : {0 c : Type} -> SliceEndofunctor c -> SliceEndofunctor c
SliceCoalgObj {c} f sa = SliceHom sa (f sa)

--------------------------------
--------------------------------
---- Pointed slice functors ----
--------------------------------
--------------------------------

public export
SlPointedF : {0 c, d : Type} ->
  SliceFunctor c d -> SliceObj d -> SliceFunctor c d
SlPointedF f sl sa = SliceCoproduct sl (f sa)

export
inSlPv : {0 c, d : Type} -> {f : SliceFunctor c d} ->
  {0 sl : SliceObj d} -> {0 sa: SliceObj c} ->
  SliceMorphism {a=d} sl (SlPointedF f sl sa)
inSlPv {c} {d} {f} {sl} {sa} ed esl = Left esl

export
inSlPc : {0 c, d : Type} -> {f : SliceFunctor c d} ->
  {0 sl : SliceObj d} -> {0 sa: SliceObj c} ->
  SliceMorphism {a=d} (f sa) (SlPointedF f sl sa)
inSlPc {c} {d} {f} {sl} {sa} ed efa = Right efa

export
outSlPc : {0 c, d : Type} -> {f : SliceFunctor c d} ->
  {0 sl, sb : SliceObj d} ->
  {0 sa : SliceObj c} ->
  SliceMorphism {a=d} sl sb -> SliceMorphism {a=d} (f sa) sb ->
  SliceMorphism {a=d} (SlPointedF f sl sa) sb
outSlPc {c} {d} {f} {sl} {sa} {sb} mlb mab ec (Left esl) = mlb ec esl
outSlPc {c} {d} {f} {sl} {sa} {sb} mlb mab ec (Right efa) = mab ec efa

export
mapSlP : {0 c, d : Type} -> {0 f : SliceFunctor c d} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  (sl : SliceObj d) ->
  (0 sa, sb : SliceObj c) -> SliceMorphism {a=c} sa sb ->
  SliceMorphism {a=d} (SlPointedF f sl sa) (SlPointedF f sl sb)
mapSlP {c} {d} {f} fm sl sa sb m ec (Left esl) = Left esl
mapSlP {c} {d} {f} fm sl sa sb m ec (Right efa) = Right $ fm sa sb m ec efa

public export
SlPointedAlg : {c : Type} ->
  (f : SliceEndofunctor c) -> SliceObj c -> SliceObj c -> Type
SlPointedAlg {c} f sa = SliceAlg (SlPointedF f {d=c} sa)

public export
SlPointedCoalg : {c : Type} ->
  (f : SliceEndofunctor c) -> SliceObj c -> SliceObj c -> Type
SlPointedCoalg {c} f sa = SliceCoalg (SlPointedF {d=c} f sa)

----------------------------------
----------------------------------
---- Copointed slice functors ----
----------------------------------
----------------------------------

public export
SlCopointedF : {0 c, d : Type} ->
  SliceFunctor c d -> SliceObj d -> SliceFunctor c d
SlCopointedF f sl sa = SliceProduct sl (f sa)

export
inSlCP : {0 c, d : Type} -> {f : SliceFunctor c d} ->
  {0 sl, sa : SliceObj d} -> {0 sb : SliceObj c} ->
  SliceMorphism {a=d} sa sl -> SliceMorphism {a=d} sa (f sb) ->
  SliceMorphism {a=d} sa (SlCopointedF f sl sb)
inSlCP {c} {f} {sl} {sa} {sb} label coalg ec esa = (label ec esa, coalg ec esa)

export
mapSlCP : {0 c, d : Type} -> {0 f : SliceFunctor c d} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  (sl : SliceObj d) ->
  (0 sa, sb : SliceObj c) -> SliceMorphism {a=c} sa sb ->
  SliceMorphism {a=d} (SlCopointedF f sl sa) (SlCopointedF f sl sb)
mapSlCP {c} {d} {f} fm sl sa sb m ec (el, efa) = (el, fm sa sb m ec efa)

public export
cpSlPoint : {0 c, d : Type} -> {0 f : SliceFunctor c d} ->
  {0 sl : SliceObj d} -> {0 sa : SliceObj c} ->
  SliceMorphism {a=d} (SlCopointedF f sl sa) sl
cpSlPoint {c} {d} {f} {sl} {sa} ec (el, efa) = el

public export
cpSlTerm : {0 c, d : Type} -> {0 f : SliceFunctor c d} ->
  {0 sl : SliceObj d} -> {0 sa : SliceObj c} ->
  SliceMorphism {a=d} (SlCopointedF f sl sa) (f sa)
cpSlTerm {c} {d} {f} {sl} {sa} ec (el, efa) = efa

public export
SlCopointedAlg : {c : Type} ->
  (f : SliceEndofunctor c) -> SliceObj c -> SliceObj c -> Type
SlCopointedAlg {c} f sa = SliceAlg (SlCopointedF {d=c} f sa)

public export
SlCopointedCoalg : {c : Type} ->
  (f : SliceEndofunctor c) -> SliceObj c -> SliceObj c -> Type
SlCopointedCoalg {c} f sa = SliceCoalg (SlCopointedF {d=c} f sa)

------------------------------------------------------------------------------
------------------------------------------------------------------------------
---- Slice categories in category-theoretic (versus dependent-type) style ----
------------------------------------------------------------------------------
------------------------------------------------------------------------------

----------------------------------------------------------
---- General slice-category definitions and utilities ----
----------------------------------------------------------

-- The category-theoretic style of defining slice objects (which is
-- sort of dual to, or backwards from, the style of dependent types
-- with universes, i.e. where an object of `Type/c` is a predicate
-- `c -> Type`).

public export
CSliceObj : Type -> Type
CSliceObj c = DPair Type (OpHomProf c)

public export
CSliceObjDomain : {0 c : Type} -> CSliceObj c -> Type
CSliceObjDomain = fst

public export
CSliceObjMap : {0 c : Type} -> (x : CSliceObj c) -> (CSliceObjDomain x -> c)
CSliceObjMap = snd

public export
CSliceMorphism : {0 c : Type} -> CSliceObj c -> CSliceObj c -> Type
CSliceMorphism x y =
  Subset0
    (CSliceObjDomain x -> CSliceObjDomain y)
    (ExtEq (CSliceObjMap x) . (.) (CSliceObjMap y))

public export
CSliceMorphismMap : {0 c : Type} -> {0 x, y : CSliceObj c} ->
  CSliceMorphism x y -> CSliceObjDomain x -> CSliceObjDomain y
CSliceMorphismMap = fst0

public export
0 CSliceMorphismEq : {0 c : Type} -> {0 x, y : CSliceObj c} ->
  (f : CSliceMorphism x y) ->
  ExtEq (CSliceObjMap x) (CSliceObjMap y . CSliceMorphismMap {x} {y} f)
CSliceMorphismEq = snd0

public export
CSliceFromSlice : {c : Type} -> SliceObj c -> CSliceObj c
CSliceFromSlice {c} sl = (Sigma {a=c} sl ** fst)

public export
SliceFromCSlice : {0 c : Type} -> CSliceObj c -> SliceObj c
SliceFromCSlice {c} x elc =
  PreImage {a=(CSliceObjDomain x)} {b=c} (CSliceObjMap x) elc

public export
CSliceFromSliceMorph : {0 c : Type} -> (x, y : SliceObj c) ->
  SliceMorphism {a=c} x y ->
  CSliceMorphism {c} (CSliceFromSlice {c} x) (CSliceFromSlice {c} y)
CSliceFromSliceMorph {c} x y m =
  Element0 (\(ec ** ex) => (ec ** m ec ex)) $ \(ec ** ex) => Refl

public export
SliceFromCSliceMorph : {0 c : Type} -> (x, y : CSliceObj c) ->
  CSliceMorphism {c} x y ->
  SliceMorphism {a=c} (SliceFromCSlice {c} x) (SliceFromCSlice {c} y)
SliceFromCSliceMorph {c} x y (Element0 mxy eqmxy) ec (Element0 ex eqxc) =
  Element0 (mxy ex) $ trans (sym $ eqmxy ex) eqxc

public export
SlCSInv : {0 c : Type} -> (0 sl : SliceObj c) ->
  SliceMorphism {a=c} (SliceFromCSlice {c} (CSliceFromSlice {c} sl)) sl
SlCSInv {c} sl elc (Element0 (elc' ** els) eq) = replace {p=sl} eq els

public export
CSSlInv : {0 c : Type} -> (0 sl : CSliceObj c) ->
  CSliceMorphism {c} (CSliceFromSlice {c} (SliceFromCSlice {c} sl)) sl
CSSlInv {c} (x ** px) =
  Element0
    (\(elc ** Element0 elx eq) => elx)
    (\(elc ** Element0 elx eq) => sym eq)

public export
CSliceId : {0 c : Type} -> (0 w : CSliceObj c) -> CSliceMorphism w w
CSliceId (a ** x) = Element0 id (\_ => Refl)

public export
CSliceCompose : {0 c : Type} -> {0 u, v, w : CSliceObj c} ->
  CSliceMorphism v w -> CSliceMorphism u v -> CSliceMorphism u w
CSliceCompose {c} {u} {v} {w} g f =
  Element0
    (CSliceMorphismMap g . CSliceMorphismMap f)
    (\elem =>
      trans
        (CSliceMorphismEq f elem)
        (CSliceMorphismEq g (CSliceMorphismMap f elem)))

public export
CSlicePipe : {0 c : Type} -> {0 u, v, w : CSliceObj c} ->
  CSliceMorphism u v -> CSliceMorphism v w -> CSliceMorphism u w
CSlicePipe = flip CSliceCompose

-- (The object-map component of a) functor between slice categories.
public export
CSliceFunctor : Type -> Type -> Type
CSliceFunctor c d = CSliceObj c -> CSliceObj d

public export
CSliceEndofunctor : Type -> Type
CSliceEndofunctor c = CSliceFunctor c c

public export
CSIdF : (c : Type) -> CSliceEndofunctor c
CSIdF c = Prelude.id {a=(CSliceObj c)}

-- The morphism-map component of a functor between slice categories.
public export
CSliceFMap : {c, d : Type} -> CSliceFunctor c d -> Type
CSliceFMap {c} {d} f =
  (x, y : CSliceObj c) -> CSliceMorphism x y -> CSliceMorphism (f x) (f y)

public export
CSliceFMapCompose : {c, d, e : Type} ->
  (g : CSliceFunctor d e) -> (f : CSliceFunctor c d) ->
  CSliceFMap g -> CSliceFMap f ->
  CSliceFMap (g . f)
CSliceFMapCompose {c} {d} {e} g f mg mf x y = mg (f x) (f y) . mf x y

-- The morphism-map component of a contravariant functor between slice
-- categories.
public export
CSliceFContramap : {c, d : Type} -> CSliceFunctor c d -> Type
CSliceFContramap {c} {d} f =
  (x, y : CSliceObj c) -> CSliceMorphism x y -> CSliceMorphism (f y) (f x)

public export
CSliceFContramapCompose : {c, d, e : Type} ->
  (g : CSliceFunctor d e) -> (f : CSliceFunctor c d) ->
  CSliceFContramap g -> CSliceFContramap f ->
  CSliceFMap (g . f)
CSliceFContramapCompose {c} {d} {e} g f mg mf x y = mg (f y) (f x) . mf x y

public export
CSliceNatTrans : {c, d : Type} ->
  CSliceFunctor c d -> CSliceFunctor c d -> Type
CSliceNatTrans {c} {d} f g =
  (a : CSliceObj c) -> CSliceMorphism {c=d} (f a) (g a)

public export
CSliceNTid : {c, d : Type} -> (f : CSliceFunctor c d) -> CSliceNatTrans f f
CSliceNTid {c} {d} f a = CSliceId (f a)

public export
CSNTvcomp : {0 c, d : Type} -> {0 f, g, h : CSliceFunctor c d} ->
  CSliceNatTrans g h -> CSliceNatTrans f g -> CSliceNatTrans f h
CSNTvcomp {c} {d} {f} {g} {h} beta alpha a =
  CSliceCompose {c=d} (beta a) (alpha a)

public export
CSWhiskerLeft : {0 c, d, e : Type} ->
  {0 g, h : CSliceFunctor d e} ->
  (nu : CSliceNatTrans {c=d} {d=e} g h) -> (f : CSliceFunctor c d) ->
  CSliceNatTrans {c} {d=e} (g . f) (h . f)
CSWhiskerLeft {c} {d} {e} {g} {h} nu f a = nu (f a)

public export
CSWhiskerRight : {0 c, d, e : Type} ->
  {f, g : CSliceFunctor c d} ->
  {h : CSliceFunctor d e} ->
  CSliceFMap {c=d} {d=e} h -> (nu : CSliceNatTrans {c} {d} f g) ->
  CSliceNatTrans {c} {d=e} (h . f) (h . g)
CSWhiskerRight {c} {d} {e} {f} {g} {h} hm nu a = hm (f a) (g a) (nu a)

public export
CSNThcomp : {0 c, d, e : Type} ->
  {f, f' : CSliceFunctor c d} -> {g, g' : CSliceFunctor d e} ->
  CSliceFMap {c=d} {d=e} g ->
  CSliceNatTrans {c=d} {d=e} g g' -> CSliceNatTrans {c} {d} f f' ->
  CSliceNatTrans {c} {d=e} (g . f) (g' . f')
CSNThcomp {c} {d} {e} {f} {f'} {g} {g'} gm beta alpha a =
  CSliceCompose {c=e} {u=(g (f a))} {w=(g' (f' a))}
    (CSWhiskerLeft {c} {d} {e} {g} {h=g'} beta f' a)
    (CSWhiskerRight {c} {d} {e} {f} {g=f'} {h=g} gm alpha a)

-- (The object-map component of a) bifunctor on slice categories.
public export
CSliceBifunctor : Type -> Type -> Type -> Type
CSliceBifunctor c d e = CSliceObj c -> CSliceObj d -> CSliceObj e

-- The morphism-map component of a bifunctor on slice categories.
public export
CSliceBimap : {c, d, e : Type} -> CSliceBifunctor c d e -> Type
CSliceBimap {c} {d} f =
  {w, y : CSliceObj c} -> {x, z : CSliceObj d} ->
  CSliceMorphism {c} w y -> CSliceMorphism {c=d} x z ->
  CSliceMorphism {c=e} (f w x) (f y z)

-- (The object-map component of a) profunctor on slice categories.
public export
CSliceProfunctor : Type -> Type -> Type -> Type
CSliceProfunctor = CSliceBifunctor

-- The morphism-map component of a profunctor on slice categories.
public export
CSliceDimap : {c, d, e : Type} -> CSliceProfunctor c d e -> Type
CSliceDimap {c} {d} f =
  {w, y : CSliceObj c} -> {x, z : CSliceObj d} ->
  CSliceMorphism {c} w y -> CSliceMorphism {c=d} x z ->
  CSliceMorphism {c=e} (f y x) (f w z)

public export
CSliceMapFst : {c, d, e : Type} -> CSliceBifunctor c d e -> Type
CSliceMapFst {c} {d} {e} f =
  {w, y : CSliceObj c} -> {x : CSliceObj d} ->
  CSliceMorphism {c} w y -> CSliceMorphism {c=e} (f w x) (f y x)

public export
CSliceMapSnd : {c, d, e : Type} -> CSliceBifunctor c d e -> Type
CSliceMapSnd {c} {d} {e} f =
  {w : CSliceObj c} -> {x, z : CSliceObj d} ->
  CSliceMorphism {c=d} x z -> CSliceMorphism {c=e} (f w x) (f w z)

public export
CSliceMapHom : {c, e : Type} -> CSliceBifunctor c c e -> Type
CSliceMapHom {c} {e} f =
  {w, y : CSliceObj c} ->
  CSliceMorphism {c} w y -> CSliceMorphism {c=e} (f w w) (f y y)

public export
csMapFstFromBimap : {c, d, e : Type} -> {f : CSliceBifunctor c d e} ->
  CSliceBimap f -> CSliceMapFst f
csMapFstFromBimap bi = flip bi (CSliceId _)

public export
csMapSndFromBimap : {c, d, e : Type} -> {f : CSliceBifunctor c d e} ->
  CSliceBimap f -> CSliceMapSnd f
csMapSndFromBimap bi = bi (CSliceId _)

public export
csMapHomFromBimap : {c, e : Type} -> {f : CSliceBifunctor c c e} ->
  CSliceBimap f -> CSliceMapHom f
csMapHomFromBimap bi g = bi g g

public export
csBimapFromMapFstAndSnd : {c, d, e : Type} -> {f : CSliceBifunctor c d e} ->
  CSliceMapFst f -> CSliceMapSnd f -> CSliceBimap f
csBimapFromMapFstAndSnd mfst msnd fwy fxz = CSliceCompose (mfst fwy) (msnd fxz)

public export
CSExtEq : {0 c : Type} -> {x, y : CSliceObj c} ->
  (f, g : CSliceMorphism x y) -> Type
CSExtEq {c} {x=(x ** px)} {y=(y ** py)} (Element0 f eqf) (Element0 g eqg) =
  ExtEq f g

-- An object of `Type/c` from a global element (term) of `c`.
public export
CSGObj : {0 c : Type} -> c -> CSliceObj c
CSGObj {c} elc = (Unit ** \() => elc)

public export
CSliceFAlgMap : {0 c : Type} -> CSliceEndofunctor c -> CSliceObj c -> Type
CSliceFAlgMap {c} f a = CSliceMorphism {c} (f a) a

public export
CSliceFAlg : {c : Type} -> CSliceEndofunctor c -> Type
CSliceFAlg {c} f = DPair (CSliceObj c) (CSliceFAlgMap {c} f)

public export
CSliceFCoalgMap : {0 c : Type} -> CSliceEndofunctor c -> CSliceObj c -> Type
CSliceFCoalgMap {c} f a = CSliceMorphism {c} a (f a)

public export
CSliceFCoalg : {c : Type} -> CSliceEndofunctor c -> Type
CSliceFCoalg {c} f = DPair (CSliceObj c) (CSliceFCoalgMap {c} f)

public export
SliceFunctorFromCSlice : {c, d : Type} -> CSliceFunctor c d -> SliceFunctor c d
SliceFunctorFromCSlice {c} {d} f =
  SliceFromCSlice {c=d} . f . CSliceFromSlice {c}

public export
CSMorphFromSlice : {c : Type} -> {x, y : SliceObj c} ->
  SliceMorphism x y ->
  CSliceMorphism {c} (CSliceFromSlice {c} x) (CSliceFromSlice {c} y)
CSMorphFromSlice {c} {x} {y} m =
  Element0 (\(elc ** elx) => (elc ** m elc elx)) $ \(elc ** elx) => Refl

-------------------------------------------------------------------------
---- Yoneda-lemma forms for functors from slice categories to `Type` ----
-------------------------------------------------------------------------

public export
CSTypeFunctor : Type -> Type
CSTypeFunctor c = CSliceObj c -> Type

public export
CSTypeNT : {c : Type} -> CSTypeFunctor c -> CSTypeFunctor c -> Type
CSTypeNT {c} f g = SliceMorphism {a=(CSliceObj c)} f g

public export
CSCovarHomTypeNT : {c : Type} -> CSliceObj c -> CSTypeFunctor c -> Type
CSCovarHomTypeNT {c} = CSTypeNT {c} . CSliceMorphism

public export
CSCovarHomHomTypeNT : {c : Type} -> CSliceObj c -> CSliceObj c -> Type
CSCovarHomHomTypeNT {c} a = CSCovarHomTypeNT {c} a . CSliceMorphism

public export
CSContravarHomTypeNT : {c : Type} -> CSliceObj c -> CSTypeFunctor c -> Type
CSContravarHomTypeNT {c} = CSTypeNT {c} . flip CSliceMorphism

public export
CSContravarHomHomTypeNT : {c : Type} -> CSliceObj c -> CSliceObj c -> Type
CSContravarHomHomTypeNT {c} a = CSContravarHomTypeNT {c} a . flip CSliceMorphism

public export
csCovarYonedaToNT :
  {c : Type} -> {f : CSTypeFunctor c} ->
  -- Morphism map for a covariant functor from `CSliceObj c` to `Type`.
  (fm : {0 v, w : CSliceObj c} -> CSliceMorphism v w -> f v -> f w) ->
  {a : CSliceObj c} ->
  f a -> CSCovarHomTypeNT a f
csCovarYonedaToNT {c} {f} fm {a} fa b mab = fm {v=a} {w=b} mab fa

public export
csCovarYonedaToNTHom :
  {c : Type} -> {a, b : CSliceObj c} ->
  CSliceMorphism b a -> CSCovarHomHomTypeNT a b
csCovarYonedaToNTHom {a} {b} =
  csCovarYonedaToNT {c} {f=(CSliceMorphism b)} {a} $ CSliceCompose {u=b}

public export
csCovarYonedaFromNT :
  {c : Type} -> {f : CSliceObj c -> Type} ->
  {a : CSliceObj c} ->
  CSCovarHomTypeNT a f -> f a
csCovarYonedaFromNT {c} {f} {a} alpha = alpha a (CSliceId a)

public export
csCovarYonedaFromNTHom :
  {c : Type} -> {a, b : CSliceObj c} ->
  CSCovarHomHomTypeNT a b -> CSliceMorphism b a
csCovarYonedaFromNTHom {b} =
  csCovarYonedaFromNT {f=(CSliceMorphism b)}

public export
csContravarYonedaToNT :
  {c : Type} -> {f : CSliceObj c -> Type} ->
  -- Morphism map for a contravariant functor from `CSliceObj c` to `Type`
  -- (that is to say, a functor from `op(CSliceObj c)` to `Type`).
  (fcm : {u, v : CSliceObj c} -> flip CSliceMorphism v u -> f v -> f u) ->
  {a : CSliceObj c} ->
  f a -> CSContravarHomTypeNT a f
csContravarYonedaToNT {c} {f} fcm {a} fa b mba = fcm {u=b} {v=a} mba fa

public export
csContravarYonedaToNTHom :
  {c : Type} -> {a, b : CSliceObj c} ->
  flip CSliceMorphism b a -> CSContravarHomHomTypeNT a b
csContravarYonedaToNTHom {a} {b} =
  csContravarYonedaToNT {f=(flip CSliceMorphism b)} {a} $ CSlicePipe {w=b}

public export
csContravarYonedaFromNT :
  {c : Type} -> {f : CSliceObj c -> Type} ->
  {a : CSliceObj c} ->
  CSContravarHomTypeNT a f -> f a
csContravarYonedaFromNT {c} {f} {a} alpha = alpha a (CSliceId a)

public export
csContravarYonedaFromNTHom :
  {c : Type} -> {a, b : CSliceObj c} ->
  CSContravarHomHomTypeNT a b -> flip CSliceMorphism b a
csContravarYonedaFromNTHom {b} =
  csContravarYonedaFromNT {f=(flip CSliceMorphism b)}

-----------------------------------------------------------------------
---- Universal morphisms and derived utilities in slice categories ----
-----------------------------------------------------------------------

------------------------
---- Initial object ----
------------------------

public export
CSInitObj : (c : Type) -> CSliceObj c
CSInitObj c = (Void ** voidF c)

public export
csInitMorph : {0 c : Type} ->
  (so : CSliceObj c) -> CSliceMorphism (CSInitObj c) so
csInitMorph {c} (a ** pa) = Element0 (voidF a) (\el => void el)

-- A morphism into the initial object may be interpreted logically as
-- showing that the domain represents a (global, within the slice category)
-- contradiction.
public export
CSGContra : {c : Type} -> CSliceObj c -> Type
CSGContra {c} = flip CSliceMorphism (CSInitObj c)

public export
csExFalso : {c : Type} -> {x, y : CSliceObj c} ->
  CSGContra y -> CSliceMorphism y x
csExFalso {c} {x} {y} = CSliceCompose {v=(CSInitObj c)} (csInitMorph x)

-------------------------
---- Terminal object ----
-------------------------

public export
CSTermObj : (c : Type) -> CSliceObj c
CSTermObj c = (c ** id)

public export
csTermMorph : {0 c : Type} ->
  (so : CSliceObj c) -> CSliceMorphism so (CSTermObj c)
csTermMorph {c} (a ** pa) = Element0 pa (\_ => Refl)

-- A global element of an object of the slice category of `Type` over `c`.
-- This is also precisely what a dependent-type system usually calls a
-- pi type -- `CSGElem x` for `x` a `CSliceObj` is the analogue of
-- `Pi x` for `x` a `SliceObj`.
public export
CSGElem : {c : Type} -> CSliceObj c -> Type
CSGElem {c} = CSliceMorphism (CSTermObj c)

public export
csConst : {c : Type} -> {x, y : CSliceObj c} -> CSGElem y -> CSliceMorphism x y
csConst {c} {x} {y} = CSlicePipe {v=(CSTermObj c)} (csTermMorph x)

public export
csgApp : {c : Type} -> {0 x, y : CSliceObj c} ->
  CSliceMorphism x y -> CSGElem x -> CSGElem y
csgApp {c} {x} {y} = CSliceCompose {u=(CSTermObj c)} {v=x} {w=y}

--------------------
---- Coproducts ----
--------------------

public export
CSCopObj : {0 c : Type} -> CSliceObj c -> CSliceObj c -> CSliceObj c
CSCopObj {c} a b =
  (Either (fst a) (fst b) **
   eitherElim {a=(fst a)} {b=(fst b)} {c} (snd a) (snd b))

public export
csInjL : {0 c : Type} -> (l, r : CSliceObj c) -> CSliceMorphism l (CSCopObj l r)
csInjL {c} (x ** px) (y ** py) = Element0 Left $ \_ => Refl

public export
csInjR : {0 c : Type} -> (l, r : CSliceObj c) -> CSliceMorphism r (CSCopObj l r)
csInjR {c} (x ** px) (y ** py) = Element0 Right $ \_ => Refl

public export
csCase : {0 c : Type} -> {0 x, y, z : CSliceObj c} ->
  CSliceMorphism x z -> CSliceMorphism y z -> CSliceMorphism (CSCopObj x y) z
csCase {c} {x=(x ** px)} {y=(y ** py)} {z=(z ** pz)}
  (Element0 f eqf) (Element0 g eqg) =
    Element0 (eitherElim {a=x} {b=y} {c=z} f g) $
      \el => case el of
        Left ex => eqf ex
        Right ey => eqg ey

public export
csInjLL : {0 c : Type} -> (ll, lr, r : CSliceObj c) ->
  CSliceMorphism ll (CSCopObj (CSCopObj ll lr) r)
csInjLL {c} ll lr r =
  CSliceCompose {u=ll} {v=(CSCopObj ll lr)} {w=(CSCopObj (CSCopObj ll lr) r)}
    (csInjL (CSCopObj ll lr) r)
    (csInjL ll lr)

public export
csInjLR : {0 c : Type} -> (ll, lr, r : CSliceObj c) ->
  CSliceMorphism lr (CSCopObj (CSCopObj ll lr) r)
csInjLR {c} ll lr r =
  CSliceCompose {u=lr} {v=(CSCopObj ll lr)} {w=(CSCopObj (CSCopObj ll lr) r)}
    (csInjL (CSCopObj ll lr) r)
    (csInjR ll lr)

public export
csInjRL : {0 c : Type} -> (l, rl, rr : CSliceObj c) ->
  CSliceMorphism rl (CSCopObj l (CSCopObj rl rr))
csInjRL {c} l rl rr =
  CSliceCompose {u=rl} {v=(CSCopObj rl rr)} {w=(CSCopObj l (CSCopObj rl rr))}
    (csInjR l (CSCopObj rl rr))
    (csInjL rl rr)

public export
csInjRR : {0 c : Type} -> (l, rl, rr : CSliceObj c) ->
  CSliceMorphism rr (CSCopObj l (CSCopObj rl rr))
csInjRR {c} l rl rr =
  CSliceCompose {u=rr} {v=(CSCopObj rl rr)} {w=(CSCopObj l (CSCopObj rl rr))}
    (csInjR l (CSCopObj rl rr))
    (csInjR rl rr)

public export
csCodiag : {c : Type} -> (x : CSliceObj c) -> CSliceMorphism (CSCopObj x x) x
csCodiag {c} x = csCase {c} {x=x} {y=x} {z=x} (CSliceId x) (CSliceId x)

public export
csCop1LeftElim : {c : Type} -> {x, y : CSliceObj c} ->
  CSliceMorphism x (CSCopObj (CSInitObj c) y) -> CSliceMorphism x y
csCop1LeftElim {y} =
  CSliceCompose {v=(CSCopObj (CSInitObj c) y)}
    (csCase {x=(CSInitObj c)} (csInitMorph y) (CSliceId y))

public export
csCopLeftIntro : {c : Type} -> {x, y, z : CSliceObj c} ->
  CSliceMorphism x z -> CSliceMorphism x (CSCopObj y z)
csCopLeftIntro = CSliceCompose {w=(CSCopObj y z)} (csInjR y z)

public export
csCopComm : {0 c : Type} -> (x, y : CSliceObj c) ->
  CSliceMorphism (CSCopObj x y) (CSCopObj y x)
csCopComm x y = csCase {x} {y} {z=(CSCopObj y x)} (csInjR y x) (csInjL y x)

public export
csCopFlip : {0 c : Type} -> {x, y, z : CSliceObj c} ->
  CSliceMorphism (CSCopObj x y) z ->
  CSliceMorphism (CSCopObj y x) z
csCopFlip {x} {y} {z} =
  CSlicePipe {u=(CSCopObj y x)} {v=(CSCopObj x y)} $ csCopComm y x

public export
csEitherBimap : {c : Type} -> CSliceBimap {c} {d=c} {e=c} (CSCopObj {c})
csEitherBimap {c} {w} {x} {y} {z} f g =
  csCase {x=w} {y=x} {z=(CSCopObj y z)}
    (CSliceCompose {u=w} {v=y} {w=(CSCopObj y z)} (csInjL y z) f)
    (CSliceCompose {u=x} {v=z} {w=(CSCopObj y z)} (csInjR y z) g)

public export
csEitherMapFst : {c : Type} -> CSliceMapFst {c} {d=c} {e=c} (CSCopObj {c})
csEitherMapFst = csMapFstFromBimap {f=CSCopObj} csEitherBimap

public export
csEitherMapSnd : {c : Type} -> CSliceMapSnd {c} {d=c} {e=c} (CSCopObj {c})
csEitherMapSnd = csMapSndFromBimap {f=CSCopObj} csEitherBimap

public export
csEitherMapHom : {c : Type} -> CSliceMapHom {c} {e=c} (CSCopObj {c})
csEitherMapHom = csMapHomFromBimap {f=CSCopObj} csEitherBimap

public export
csCopAssocL : {0 c : Type} -> (x, y, z : CSliceObj c) ->
  CSliceMorphism (CSCopObj x (CSCopObj y z)) (CSCopObj (CSCopObj x y) z)
csCopAssocL x y z =
  csCase {x} {y=(CSCopObj y z)} {z=(CSCopObj (CSCopObj x y) z)}
    (csInjLL x y z)
    (csCase {x=y} {y=z} {z=(CSCopObj (CSCopObj x y) z)}
      (csInjLR x y z)
      (csInjR (CSCopObj x y) z))

public export
csCopAssocR : {0 c : Type} -> (x, y, z : CSliceObj c) ->
  CSliceMorphism (CSCopObj (CSCopObj x y) z) (CSCopObj x (CSCopObj y z))
csCopAssocR x y z =
  csCase {x=(CSCopObj x y)} {y=z} {z=(CSCopObj x (CSCopObj y z))}
    (csCase {x} {y} {z=(CSCopObj x (CSCopObj y z))}
      (csInjL x (CSCopObj y z))
      (csInjRL x y z))
    (csInjRR x y z)

------------------
---- Products ----
------------------

public export
CSProdObj : {0 c : Type} -> CSliceObj c -> CSliceObj c -> CSliceObj c
CSProdObj {c} a b =
    (Pullback {a=(fst a)} {b=(fst b)} {c} (snd a) (snd b) **
     \(Element0 (x, y) eq) => snd a x {- `eq` ensures this is also `snd b y` -})

public export
csProj1 : {0 c : Type} -> (l, r : CSliceObj c) ->
  CSliceMorphism (CSProdObj l r) l
csProj1 {c} (a ** pa) (b ** pb) =
  Element0 (fst . fst0) $ \(Element0 (x, y) eq) => Refl

public export
csProj2 : {0 c : Type} -> (l, r : CSliceObj c) ->
  CSliceMorphism (CSProdObj l r) r
csProj2 {c} (a ** pa) (b ** pb) =
  Element0 (snd . fst0) $ \(Element0 (x, y) eq) => eq

public export
csPair : {0 c : Type} -> {0 x, y, z : CSliceObj c} ->
  CSliceMorphism {c} x y -> CSliceMorphism {c} x z ->
  CSliceMorphism {c} x (CSProdObj y z)
csPair {c} {x=(x ** px)} {y=(y ** py)} {z=(z ** pz)}
  (Element0 f eqf) (Element0 g eqg) =
    Element0 (\el => Element0 (f el, g el) $ trans (sym $ eqf el) $ eqg el) eqf

public export
csProj11 : {0 c : Type} -> (l1, l2, r : CSliceObj c) ->
  CSliceMorphism (CSProdObj (CSProdObj l1 l2) r) l1
csProj11 {c} l1 l2 r =
  CSliceCompose {u=(CSProdObj (CSProdObj l1 l2) r)} {v=(CSProdObj l1 l2)} {w=l1}
    (csProj1 l1 l2)
    (csProj1 (CSProdObj l1 l2) r)

public export
csProj12 : {0 c : Type} -> (l1, l2, r : CSliceObj c) ->
  CSliceMorphism (CSProdObj (CSProdObj l1 l2) r) l2
csProj12 {c} l1 l2 r =
  CSliceCompose {u=(CSProdObj (CSProdObj l1 l2) r)} {v=(CSProdObj l1 l2)} {w=l2}
    (csProj2 l1 l2)
    (csProj1 (CSProdObj l1 l2) r)

public export
csProj21 : {0 c : Type} -> (l, r1, r2 : CSliceObj c) ->
  CSliceMorphism (CSProdObj l (CSProdObj r1 r2)) r1
csProj21 {c} l r1 r2 =
  CSliceCompose {u=(CSProdObj l (CSProdObj r1 r2))} {v=(CSProdObj r1 r2)} {w=r1}
    (csProj1 r1 r2)
    (csProj2 l (CSProdObj r1 r2))

public export
csProj22 : {0 c : Type} -> (l, r1, r2 : CSliceObj c) ->
  CSliceMorphism (CSProdObj l (CSProdObj r1 r2)) r2
csProj22 {c} l r1 r2 =
  CSliceCompose {u=(CSProdObj l (CSProdObj r1 r2))} {v=(CSProdObj r1 r2)} {w=r2}
    (csProj2 r1 r2)
    (csProj2 l (CSProdObj r1 r2))

public export
csDiag : {c : Type} -> (x : CSliceObj c) -> CSliceMorphism x (CSProdObj x x)
csDiag {c} x = csPair {c} {x=x} {y=x} {z=x} (CSliceId x) (CSliceId x)

public export
csProd1LeftElim : {c : Type} -> {x, y : CSliceObj c} ->
  CSliceMorphism (CSProdObj (CSTermObj c) x) y -> CSliceMorphism x y
csProd1LeftElim {x} =
  CSlicePipe {v=(CSProdObj (CSTermObj c) x)}
    (csPair (csTermMorph x) (CSliceId x))

public export
csProdLeftIntro : {c : Type} -> {x, y, z : CSliceObj c} ->
  CSliceMorphism y z -> CSliceMorphism (CSProdObj x y) z
csProdLeftIntro f = CSliceCompose {u=(CSProdObj x y)} f (csProj2 x y)

public export
csProdComm : {0 c : Type} -> (x, y : CSliceObj c) ->
  CSliceMorphism (CSProdObj x y) (CSProdObj y x)
csProdComm x y = csPair {x=(CSProdObj x y)} (csProj2 x y) (csProj1 x y)

public export
csProdFlip : {0 c : Type} -> {x, y, z : CSliceObj c} ->
  CSliceMorphism (CSProdObj x y) z ->
  CSliceMorphism (CSProdObj y x) z
csProdFlip {x} {y} {z} =
  CSlicePipe {u=(CSProdObj y x)} {v=(CSProdObj x y)} $ csProdComm y x

public export
csPairBimap : {c : Type} -> CSliceBimap {c} {d=c} {e=c} (CSProdObj {c})
csPairBimap {c} {w} {x} {y} {z} f g =
  csPair {x=(CSProdObj w x)} {y} {z}
    (CSliceCompose {u=(CSProdObj w x)} {v=w} {w=y} f (csProj1 w x))
    (CSliceCompose {u=(CSProdObj w x)} {v=x} {w=z} g (csProj2 w x))

public export
csPairMapFst : {c : Type} -> CSliceMapFst {c} {d=c} {e=c} (CSProdObj {c})
csPairMapFst = csMapFstFromBimap {f=CSProdObj} csPairBimap

public export
csPairMapSnd : {c : Type} -> CSliceMapSnd {c} {d=c} {e=c} (CSProdObj {c})
csPairMapSnd = csMapSndFromBimap {f=CSProdObj} csPairBimap

public export
csPairMapHom : {c : Type} -> CSliceMapHom {c} {e=c} (CSProdObj {c})
csPairMapHom = csMapHomFromBimap {f=CSProdObj} csPairBimap

public export
csProdAssocL : {0 c : Type} -> (x, y, z : CSliceObj c) ->
  CSliceMorphism (CSProdObj x (CSProdObj y z)) (CSProdObj (CSProdObj x y) z)
csProdAssocL x y z =
  csPair {x=(CSProdObj x (CSProdObj y z))} {y=(CSProdObj x y)} {z}
    (csPair {x=(CSProdObj x (CSProdObj y z))}
      (csProj1 x (CSProdObj y z))
      (csProj21 x y z))
    (csProj22 x y z)

public export
csProdAssocR : {0 c : Type} -> (x, y, z : CSliceObj c) ->
  CSliceMorphism (CSProdObj (CSProdObj x y) z) (CSProdObj x (CSProdObj y z))
csProdAssocR x y z =
  csPair {x=(CSProdObj (CSProdObj x y) z)} {y=x} {z=(CSProdObj y z)}
    (csProj11 x y z)
    (csPair {x=(CSProdObj (CSProdObj x y) z)} {y} {z}
      (csProj12 x y z)
      (csProj2 (CSProdObj x y) z))

-----------------------------------------------------------------------------
---- Combining products and coproducts (without assuming distributivity) ----
-----------------------------------------------------------------------------

public export
csGather : {c : Type} -> (x, y, z : CSliceObj c) ->
  CSliceMorphism
    (CSCopObj (CSProdObj x y) (CSProdObj x z))
    (CSProdObj x (CSCopObj y z))
csGather {c} x y z =
  csPair {x=(CSCopObj (CSProdObj x y) (CSProdObj x z))} {y=x} {z=(CSCopObj y z)}
    (csCase {x=(CSProdObj x y)} {y=(CSProdObj x z)} {z=x}
      (csProj1 x y)
      (csProj1 x z))
    (csEitherBimap {w=(CSProdObj x y)} {x=(CSProdObj x z)} {y} {z}
      (csProj2 x y)
      (csProj2 x z))

----------------------------------------------------
---- Distributivity of products over coproducts ----
----------------------------------------------------

public export
csDistrib : {c : Type} -> (x, y, z : CSliceObj c) ->
  CSliceMorphism
    (CSProdObj x (CSCopObj y z))
    (CSCopObj (CSProdObj x y) (CSProdObj x z))
csDistrib {c} (x ** px) (y ** py) (z ** pz) =
  Element0
    (\(Element0 (elx, eleyz) pxeyz) => case eleyz of
      Left ely => Left $ Element0 (elx, ely) pxeyz
      Right elz => Right $ Element0 (elx, elz) pxeyz)
    (\(Element0 (elx, eleyz) pxeyz) => case eleyz of
      Left ely => Refl
      Right elz => Refl)

------------------------------------
---- Hom-objects (exponentials) ----
------------------------------------

public export
CSHomObj : {c : Type} -> CSliceObj c -> CSliceObj c -> CSliceObj c
CSHomObj {c} x y =
  ((el : c ** (PreImage (snd x) el -> PreImage (snd y) el)) ** fst)

public export
CSExpObj : {c : Type} -> CSliceObj c -> CSliceObj c -> CSliceObj c
CSExpObj = flip CSHomObj

public export
csCurry : {0 c : Type} -> {x, y, z : CSliceObj c} ->
  CSliceMorphism {c} (CSProdObj x y) z ->
  CSliceMorphism {c} x (CSHomObj {c} y z)
csCurry {c} {x=(x ** px)} {y=(y ** py)} {z=(z ** pz)} (Element0 f eqf) =
  Element0
    (\elx =>
      (px elx ** \(Element0 ely eqxy) =>
        Element0
          (f $ Element0 (elx, ely) $ sym eqxy)
          (sym $ eqf (Element0 (elx, ely) (sym eqxy)))))
    $ \_ => Refl

public export
csEval : {0 c : Type} -> (x, y : CSliceObj c) ->
  CSliceMorphism {c} (CSProdObj {c} (CSHomObj {c} x y) x) y
csEval {c} (x ** px) (y ** py) =
  Element0
    (\(Element0 ((elc ** f), elx) eq) => fst0 $ f $ Element0 elx $ sym eq)
    $ \(Element0 ((elc ** f), elx) eq) => sym $ snd0 $ f $ Element0 elx $ sym eq

public export
csComposeBeforeEval : {c : Type} -> {x, y, z : CSliceObj c} ->
  CSliceMorphism x (CSProdObj (CSHomObj y z) y) ->
  CSliceMorphism x z
csComposeBeforeEval {c} {x} {y} {z} =
  CSliceCompose {v=(CSProdObj (CSHomObj y z) y)} (csEval y z)

public export
csComposeAfterEval : {c : Type} -> {x, y, z : CSliceObj c} ->
  CSliceMorphism y z ->
  CSliceMorphism (CSProdObj (CSHomObj x y) x) z
csComposeAfterEval {c} {x} {y} {z} =
  CSlicePipe {u=(CSProdObj (CSHomObj x y) x)} (csEval x y)

public export
csUncurry : {c : Type} -> {x, y, z : CSliceObj c} ->
  CSliceMorphism {c} x (CSHomObj {c} y z) ->
  CSliceMorphism {c} (CSProdObj x y) z
csUncurry {c} {x} {y} {z} f =
  csComposeBeforeEval {c} {x=(CSProdObj x y)} {y} {z} (csPairMapFst f)

public export
csFlip : {c : Type} -> {x, y, z : CSliceObj c} ->
  CSliceMorphism x (CSHomObj y z) ->
  CSliceMorphism y (CSHomObj x z)
csFlip {c} {x} {y} {z} = csCurry . csProdFlip . csUncurry

public export
csEvalSnd : {c : Type} -> {x : CSliceObj c} -> (y, z : CSliceObj c) ->
  CSliceMorphism (CSProdObj x (CSProdObj (CSHomObj y z) y)) (CSProdObj x z)
csEvalSnd {x} y z = csPairMapSnd $ csEval y z

public export
csEvalTwice : {c : Type} -> (x, y, z : CSliceObj c) ->
  CSliceMorphism (CSProdObj (CSHomObj y z) (CSProdObj (CSHomObj x y) x)) z
csEvalTwice {c} x y z =
  CSliceCompose
    {u=(CSProdObj (CSHomObj y z) (CSProdObj (CSHomObj x y) x))}
    {v=(CSProdObj (CSHomObj y z) y)}
    {w=z}
    (csEval y z)
    (csEvalSnd x y)

public export
CSHomGElem : {c : Type} -> CSliceObj c -> CSliceObj c -> Type
CSHomGElem = CSGElem .* CSHomObj

public export
csRightApp : {c : Type} -> {x, y, z : CSliceObj c} ->
  CSliceMorphism x (CSHomObj y z) -> CSliceMorphism x y ->
  CSliceMorphism x z
csRightApp {c} {x} {y} {z} = csComposeBeforeEval .* csPair

public export
csHomGElemToMorph : {c : Type} -> {x, y : CSliceObj c} ->
  CSHomGElem x y -> CSliceMorphism x y
csHomGElemToMorph {c} {x} {y} el =
  csProd1LeftElim $ csUncurry {x=(CSTermObj c)} el

public export
csMorphToHomGElem : {c : Type} -> {x, y : CSliceObj c} ->
  CSliceMorphism x y -> CSHomGElem x y
csMorphToHomGElem {c} {x} {y} el =
  csCurry {x=(CSTermObj c)} $ csProdLeftIntro {x=(CSTermObj c)} {y=x} {z=y} el

public export
csPartialApp : {c : Type} -> {w, x, y, z : CSliceObj c} ->
  CSliceMorphism (CSProdObj x y) z -> CSliceMorphism w x ->
  CSliceMorphism (CSProdObj w y) z
csPartialApp g f = csUncurry $ CSliceCompose {w=(CSHomObj y z)} (csCurry g) f

public export
csPartialAppGElem : {c : Type} -> {w, x, y, z : CSliceObj c} ->
  CSliceMorphism (CSProdObj x y) z -> CSGElem x -> CSliceMorphism y z
csPartialAppGElem g t = csProd1LeftElim $ csPartialApp {w=(CSTermObj c)} g t

public export
csAppMorphGElem : {c : Type} -> {w, x, y : CSliceObj c} ->
  CSliceMorphism (CSHomObj w x) y ->
  CSliceMorphism w x -> CSGElem y
csAppMorphGElem {c} {w} {x} {y} g f =
  CSliceCompose {u=(CSTermObj c)} {v=(CSHomObj w x)} {w=y}
    g (csMorphToHomGElem f)

public export
csHomMorphToMeta : {c : Type} -> {w, x, y, z : CSliceObj c} ->
  CSliceMorphism (CSHomObj w x) (CSHomObj y z) ->
  CSliceMorphism w x -> CSliceMorphism y z
csHomMorphToMeta {c} {w} {x} {y} {z} =
  csHomGElemToMorph .* csAppMorphGElem {y=(CSHomObj y z)}

public export
csConstMorph : {c : Type} -> {x, y, z : CSliceObj c} ->
  CSliceMorphism y z -> CSliceMorphism x (CSHomObj y z)
csConstMorph {c} {x} {y} {z} =
  csConst {c} {x} {y=(CSHomObj y z)} . csMorphToHomGElem {x=y} {y=z}

public export
csConstId : {c : Type} ->
  {x, y : CSliceObj c} -> CSliceMorphism x (CSHomObj y y)
csConstId {c} {x} {y} = csConstMorph {c} {x} {y} {z=y} (CSliceId y)

--------------------
---- Equalizers ----
--------------------

public export
CSEqObj : {0 c : Type} -> {x : CSliceObj c} -> {0 y : CSliceObj c} ->
  (f, g : CSliceMorphism x y) -> CSliceObj c
CSEqObj {c} {x} {y} (Element0 f eqf) (Element0 g eqg) =
  (Equalizer {a=(fst x)} {b=(fst y)} f g **
   \(Element0 el eqel) => (snd x) el
    {- also ensured by `eqf`, `eqg`, and `eqel` to be equal to `snd y (f el)`
     - and to `snd y (g el)` -})

public export
csEqInj : {0 c : Type} -> {x : CSliceObj c} -> {0 y : CSliceObj c} ->
  (f, g : CSliceMorphism {c} x y) -> CSliceMorphism (CSEqObj {c} {x} {y} f g) x
csEqInj {c} {x=(x ** px)} {y=(y ** py)} (Element0 f eqf) (Element0 g eqg) =
  Element0 fst0 $ \(Element0 el eqel) => Refl

public export
0 csEqInjEq : {0 c : Type} -> {x : CSliceObj c} -> {0 y : CSliceObj c} ->
  (f, g : CSliceMorphism {c} x y) ->
  CSExtEq {x=(CSEqObj {c} {x} {y} f g)} {y}
    (CSliceCompose {u=(CSEqObj {c} {x} {y} f g)} {v=x} {w=y}
      f (csEqInj {c} {x} {y} f g))
    (CSliceCompose {u=(CSEqObj {c} {x} {y} f g)} {v=x} {w=y}
      g (csEqInj {c} {x} {y} f g))
csEqInjEq {c} {x=(x ** px)} {y=(y ** py)} (Element0 f eqf) (Element0 g eqg) =
  \(Element0 elx eqfgx) => eqfgx

public export
csEqIntro : {0 c : Type} -> {x : CSliceObj c} -> {0 w, y : CSliceObj c} ->
  (f, g : CSliceMorphism {c} x y) ->
  (h : CSliceMorphism {c} w x) ->
  CSExtEq {x=w} {y}
    (CSliceCompose {u=w} {v=x} {w=y} f h)
    (CSliceCompose {u=w} {v=x} {w=y} g h) ->
  CSliceMorphism w (CSEqObj {c} {x} {y} f g)
csEqIntro {c} {x=(x ** px)} {w=(w ** pw)} {y=(y ** py)}
  (Element0 f eqf) (Element0 g eqg) (Element0 h eqh) fgheq =
    Element0 (\elw => Element0 (h elw) (fgheq elw)) $
      \elw => trans (eqh elw) Refl

---------------------------------------------------------------------------
---- Equivalence of equalizers of products with products of equalizers ----
---------------------------------------------------------------------------

public export
csProdEqToEqProd : {c : Type} -> {w, x, y, z : CSliceObj c} ->
  (f, g : CSliceMorphism {c} w y) ->
  (f', g' : CSliceMorphism {c} x z) ->
  CSliceMorphism
    (CSProdObj {c}
      (CSEqObj {c} {x=w} {y} f g)
      (CSEqObj {c} {x} {y=z} f' g'))
    (CSEqObj {c} {x=(CSProdObj w x)} {y=(CSProdObj y z)}
      (csPairBimap {c} {w} {x} {y} {z} f f')
      (csPairBimap {c} {w} {x} {y} {z} g g'))
csProdEqToEqProd {c} {w=(w ** pw)} {x=(x ** px)} {y=(y ** py)} {z=(z ** pz)}
  (Element0 f feq) (Element0 g geq) (Element0 f' feq') (Element0 g' geq') =
    Element0
      (\(Element0 (Element0 elw fgeq, Element0 elx fgeq') wxeq) =>
        Element0 (Element0 (elw, elx) wxeq) $
          rewrite fgeq in rewrite fgeq' in s0Eq12 Refl uip)
      (\(Element0 (Element0 elw fgeq, Element0 elx fgeq') wxeq) =>
        Refl)

public export
csEqProdToProdEq : {c : Type} -> {w, x, y, z : CSliceObj c} ->
  (f, g : CSliceMorphism {c} w y) ->
  (f', g' : CSliceMorphism {c} x z) ->
  CSliceMorphism
    (CSEqObj {c} {x=(CSProdObj w x)} {y=(CSProdObj y z)}
      (csPairBimap {c} {w} {x} {y} {z} f f')
      (csPairBimap {c} {w} {x} {y} {z} g g'))
    (CSProdObj {c}
      (CSEqObj {c} {x=w} {y} f g)
      (CSEqObj {c} {x} {y=z} f' g'))
csEqProdToProdEq {c} {w=(w ** pw)} {x=(x ** px)} {y=(y ** py)} {z=(z ** pz)}
  (Element0 f feq) (Element0 g geq) (Element0 f' feq') (Element0 g' geq') =
    Element0
      (\(Element0 (Element0 (elw, elx) wxeq) fgeq) =>
        Element0
          (Element0 elw $ pairInj1 $ elementInjectiveFst fgeq,
          (Element0 elx $ pairInj2 $ elementInjectiveFst fgeq))
          wxeq)
      (\(Element0 (Element0 (elw, elx) wxeq) fgeq) => Refl)

------------------------------------------------------
---- Distributivity of equalizers over coproducts ----
------------------------------------------------------

public export
csEqDistrib : {c : Type} -> {x, y, z : CSliceObj c} ->
  (f, g : CSliceMorphism {c} (CSCopObj x y) z) ->
  CSliceMorphism
    (CSEqObj {c} {x=(CSCopObj x y)} {y=z} f g)
    (CSCopObj
      (CSEqObj {c} {x} {y=z}
        (CSliceCompose {u=x} {v=(CSCopObj x y)} {w=z} f (csInjL x y))
        (CSliceCompose {u=x} {v=(CSCopObj x y)} {w=z} g (csInjL x y)))
      (CSEqObj {c} {x=y} {y=z}
        (CSliceCompose {u=y} {v=(CSCopObj x y)} {w=z} f (csInjR x y))
        (CSliceCompose {u=y} {v=(CSCopObj x y)} {w=z} g (csInjR x y))))
csEqDistrib {c} {x=(x ** px)} {y=(y ** py)} {z=(z ** pz)}
  (Element0 f fcomm) (Element0 g gcomm) =
    Element0
      (\(Element0 exy fgeq) => case exy of
        Left elx => Left $ Element0 elx fgeq
        Right ely => Right $ Element0 ely fgeq)
      (\(Element0 exy fgeq) => case exy of
        Left elx => Refl
        Right ely => Refl)

----------------------------------------------------------
---- Pullbacks (derived from products and equalizers) ----
----------------------------------------------------------

public export
csPullbackEq1 : {0 c : Type} -> {x, y : CSliceObj c} -> (z : CSliceObj c) ->
  CSliceMorphism {c} x z -> CSliceMorphism {c} (CSProdObj x y) z
csPullbackEq1 {c} {x} {y} z f =
  CSliceCompose f {u=(CSProdObj x y)} (csProj1 x y)

public export
csPullbackEq2 : {0 c : Type} -> {x, y : CSliceObj c} -> (z : CSliceObj c) ->
  CSliceMorphism {c} y z -> CSliceMorphism {c} (CSProdObj x y) z
csPullbackEq2 {c} {x} {y} z g =
  CSliceCompose g {u=(CSProdObj x y)} (csProj2 x y)

public export
CSPullback : {0 c : Type} -> {x, y, z : CSliceObj c} ->
  CSliceMorphism {c} x z -> CSliceMorphism {c} y z -> CSliceObj c
CSPullback {c} {x} {y} {z} f g =
  CSEqObj {c} {x=(CSProdObj {c} x y)} {y=z}
    (csPullbackEq1 z f) (csPullbackEq2 z g)

public export
csPBproj1 : {0 c : Type} -> {x, y, z : CSliceObj c} ->
  (f : CSliceMorphism {c} x z) -> (g : CSliceMorphism {c} y z) ->
  CSliceMorphism {c} (CSPullback {c} {x} {y} {z} f g) x
csPBproj1 {x} {y} {z} f g =
  CSliceCompose {u=(CSPullback f g)} {v=(CSProdObj x y)}
    (csProj1 x y)
    (csEqInj {x=(CSProdObj x y)} (csPullbackEq1 z f) (csPullbackEq2 z g))

public export
csPBproj2 : {0 c : Type} -> {x, y, z : CSliceObj c} ->
  (f : CSliceMorphism {c} x z) -> (g : CSliceMorphism {c} y z) ->
  CSliceMorphism {c} (CSPullback {c} {x} {y} {z} f g) y
csPBproj2 {x} {y} {z} f g =
  CSliceCompose {u=(CSPullback f g)} {v=(CSProdObj x y)}
    (csProj2 x y)
    (csEqInj {x=(CSProdObj x y)} (csPullbackEq1 z f) (csPullbackEq2 z g))

-- Pullback introduction in `Type` using slice morphisms.
public export
pbIntro : {0 a, b, b', c : Type} -> {0 p : a -> c} ->
  {0 g : b -> c} -> {0 g' : b' -> c} ->
  (f : CSliceMorphism {c} (a ** p) (CSProdObj {c} (b ** g) (b' ** g'))) ->
  CSliceMorphism {c=(b, b')}
    (a ** \ela => fst0 (fst0 f ela))
    (Pullback {a=b} {b=b'} {c} g g' **
     \el => (pbProj1 {f=g} {g=g'} el, pbProj2 {f=g} {g=g'} el))
pbIntro {a} {b} {b'} {c} {p} {g} {g'} (Element0 f eqf) =
  Element0 f $ \ela => pairFstSnd (fst0 $ f ela)

------------------------------------------------------
---- Distributivity of pullbacks over coproducts -----
------------------------------------------------------

public export
csPullbackDistrib : {c : Type} -> {w, x, y, z : CSliceObj c} ->
  (f : CSliceMorphism {c} w z) ->
  (g : CSliceMorphism {c} (CSCopObj x y) z) ->
  CSliceMorphism
    (CSPullback {c} {x=w} {y=(CSCopObj x y)} {z} f g)
    (CSCopObj {c}
      (CSPullback {c} {x=w} {y=x} {z}
        f
        (CSliceCompose {u=x} {v=(CSCopObj x y)} {w=z} g (csInjL x y)))
      (CSPullback {c} {x=w} {y} {z} f
        (CSliceCompose {u=y} {v=(CSCopObj x y)} {w=z} g (csInjR x y))))
csPullbackDistrib {c} {w=(w ** pw)} {x=(x ** px)} {y=(y ** py)} {z=(z ** pz)}
  (Element0 f fcomm) (Element0 g gcomm) =
    Element0
      (\(Element0 (Element0 (elw, exy) wxyeq) fgeq) =>
        case exy of
          Left elx => Left $ Element0 (Element0 (elw, elx) wxyeq) fgeq
          Right ely => Right $ Element0 (Element0 (elw, ely) wxyeq) fgeq)
      (\(Element0 (Element0 (elw, exy) wxyeq) fgeq) =>
        case exy of
          Left elx => Refl
          Right ely => Refl)

---------------------------------------------------------
---- Yoneda-lemma forms internal to slice categories ----
---------------------------------------------------------

public export
CSNTCovarFunctor : {c : Type} -> CSliceObj c -> CSliceObj c -> Type
CSNTCovarFunctor {c} a b =
  CSliceNatTrans {c} {d=c} (CSHomObj a) (CSHomObj b)

public export
CSNTContravarFunctor : {c : Type} -> CSliceObj c -> CSliceObj c -> Type
CSNTContravarFunctor {c} a b =
  CSliceNatTrans {c} {d=c} (CSExpObj a) (CSExpObj b)

public export
csCovarInternalYonedaToNTHom : {c : Type} -> {a, b : CSliceObj c} ->
  flip CSliceMorphism a b -> CSNTCovarFunctor a b
csCovarInternalYonedaToNTHom {c} {a} {b} f x =
  csCurry $
    csComposeBeforeEval {x=(CSProdObj (CSHomObj a x) b)} $ csPairMapSnd f

public export
csCovarInternalYonedaFromNTHom : {c : Type} -> {a, b : CSliceObj c} ->
  CSNTCovarFunctor a b -> flip CSliceMorphism a b
csCovarInternalYonedaFromNTHom {c} {a} {b} alpha =
  csHomMorphToMeta (alpha a) (CSliceId a)

public export
csContravarInternalYonedaToNTHom : {c : Type} -> {a, b : CSliceObj c} ->
  CSliceMorphism a b -> CSNTContravarFunctor a b
csContravarInternalYonedaToNTHom {c} {a} {b} f x =
  csCurry $ csComposeAfterEval f

public export
csContravarInternalYonedaFromNTHom : {c : Type} -> {a, b : CSliceObj c} ->
  CSNTContravarFunctor a b -> CSliceMorphism a b
csContravarInternalYonedaFromNTHom {c} {a} {b} alpha =
  csHomMorphToMeta (alpha a) (CSliceId a)

---------------------------------------
---- Slice-category hom-profunctor ----
---------------------------------------

public export
csHomContramapFst : {c : Type} -> {a, b : CSliceObj c} ->
  CSliceMorphism a b -> CSNTContravarFunctor a b
csHomContramapFst = csContravarInternalYonedaToNTHom

public export
csHomMapSnd : {c : Type} -> {a, b : CSliceObj c} ->
  flip CSliceMorphism a b -> CSNTCovarFunctor a b
csHomMapSnd = csCovarInternalYonedaToNTHom

-- The hom-profunctor, defined as a composition of components of
-- natural transformations derived from the Yoneda lemma.
public export
csHomDimap : {c : Type} -> CSliceDimap {c} {d=c} {e=c} (CSHomObj {c})
csHomDimap {c} {w} {x} {y} {z} f g =
  CSliceCompose
    {u=(CSHomObj y x)} {v=(CSHomObj w x)} {w=(CSHomObj w z)}
    (csHomContramapFst g w)
    (csHomMapSnd f x)

-------------------------------------------------------------------------
---- Internal reflections of slice morphisms within slice categories ----
-------------------------------------------------------------------------

public export
csInternalId : {c : Type} -> (x: CSliceObj c) -> CSHomGElem x x
csInternalId {c} x = csMorphToHomGElem (CSliceId x)

public export
csInternalApply : {c : Type} -> (x, y : CSliceObj c) ->
  CSliceMorphism (CSHomObj x y) (CSHomObj x y)
csInternalApply {c} x y = CSliceId {c} (CSHomObj x y)

public export
csInternalFlipApply : {c : Type} -> (x, y : CSliceObj c) ->
  CSliceMorphism x (CSHomObj (CSHomObj x y) y)
csInternalFlipApply {c} x y =
  csFlip {c} {x=(CSHomObj x y)} {y=x} {z=y} $ csInternalApply {c} x y

public export
csInternalComposePair : {c : Type} -> (x, y, z : CSliceObj c) ->
  CSliceMorphism (CSProdObj (CSHomObj y z) (CSHomObj x y)) (CSHomObj x z)
csInternalComposePair {c} x y z =
  csCurry {x=(CSProdObj (CSHomObj y z) (CSHomObj x y))} {y=x} {z} $
  CSlicePipe
    {u=(CSProdObj (CSProdObj (CSHomObj y z) (CSHomObj x y)) x)}
    {v=(CSProdObj (CSHomObj y z) (CSProdObj (CSHomObj x y) x))}
    {w=z}
    (csProdAssocR (CSHomObj y z) (CSHomObj x y) x) $
    (csEvalTwice {c} x y z)

public export
csInternalCompose : {c : Type} -> (x, y, z : CSliceObj c) ->
  CSliceMorphism (CSHomObj y z) (CSHomObj (CSHomObj x y) (CSHomObj x z))
csInternalCompose {c} x y z =
  csCurry {x=(CSHomObj y z)} {y=(CSHomObj x y)} {z=(CSHomObj x z)} $
  csInternalComposePair {c} x y z

public export
csInternalPipe : {c : Type} -> (x, y, z : CSliceObj c) ->
  CSliceMorphism (CSHomObj x y) (CSHomObj (CSHomObj y z) (CSHomObj x z))
csInternalPipe {c} x y z =
  csFlip {c} {x=(CSHomObj y z)} {y=(CSHomObj x y)} {z=(CSHomObj x z)} $
    csInternalCompose {c} x y z

public export
csInternalPreCompFlipApp : {c : Type} -> (x, y, z : CSliceObj c) ->
  CSliceMorphism (CSHomObj (CSHomObj (CSHomObj x y) y) z) (CSHomObj x z)
csInternalPreCompFlipApp {c} x y z =
  csHomMorphToMeta
    {x=(CSHomObj (CSHomObj x y) y)}
    {y=(CSHomObj (CSHomObj (CSHomObj x y) y) z)}
    {z=(CSHomObj x z)}
    (csInternalPipe {c} x (CSHomObj (CSHomObj x y) y) z)
    (csInternalFlipApply {c} x y)

public export
csInternalUncurry : {c : Type} -> (x, y, z : CSliceObj c) ->
  CSliceMorphism {c}
    (CSHomObj x (CSHomObj {c} y z)) (CSHomObj (CSProdObj x y) z)
csInternalUncurry {c} x y z =
  csCurry {x=(CSHomObj x (CSHomObj y z))} {y=(CSProdObj x y)}
  $ CSlicePipe
  {u=(CSProdObj (CSHomObj x (CSHomObj y z)) (CSProdObj x y))}
  -- {v=(CSProdObj (CSHomObj y z) (CSProdObj (CSHomObj x y) x))}
  {v=(CSProdObj (CSProdObj (CSHomObj x (CSHomObj y z)) x) y)}
  {w=z}
  (csProdAssocL (CSHomObj x (CSHomObj y z)) x y)
  $ csUncurry
  $ csEval x (CSHomObj y z)

---------------------------------
---- Internal slice functors ----
---------------------------------

public export
CSliceInternalFMap : {c : Type} -> CSliceEndofunctor c -> Type
CSliceInternalFMap {c} f =
  (x, y : CSliceObj c) -> CSliceMorphism (CSHomObj x y) (CSHomObj (f x) (f y))

public export
CSliceInternalFMapCompose : {c : Type} ->
  (g, f : CSliceEndofunctor c) ->
  CSliceInternalFMap g -> CSliceInternalFMap f ->
  CSliceInternalFMap (g . f)
CSliceInternalFMapCompose {c} g f mg mf x y =
  CSliceCompose
    {u=(CSHomObj x y)}
    {v=(CSHomObj (f x) (f y))}
    {w=(CSHomObj (g (f x)) (g (f y)))}
    (mg (f x) (f y))
    (mf x y)

public export
CSliceFMapFromInternalFMap : {c : Type} ->
  (f : CSliceEndofunctor c) -> CSliceInternalFMap f -> CSliceFMap f
CSliceFMapFromInternalFMap {c} f mf x y = csHomMorphToMeta $ mf x y

public export
CSliceInternalFContramap : {c : Type} -> CSliceEndofunctor c -> Type
CSliceInternalFContramap {c} f =
  (x, y : CSliceObj c) -> CSliceMorphism (CSHomObj x y) (CSHomObj (f y) (f x))

-----------------------------------------------------------------------------
---- Dependent universal functors (adjunctions between slice categories) ----
-----------------------------------------------------------------------------

-- These may be viewed as (universal) morphisms in the two-category of
-- slice categories and slice functors.

public export
CSBaseChange : {0 c : Type} -> {d : Type} -> (d -> c) -> CSliceFunctor c d
CSBaseChange {c} {d} f (x ** px) =
  (Pullback {a=d} {b=x} {c} f px ** pbProj1 {f} {g=px})

public export
csBaseChangeMap : {0 c, d : Type} -> {0 f : d -> c} ->
  CSliceFMap {c} {d} (CSBaseChange {c} {d} f)
csBaseChangeMap {c} {d} {f} (a ** pa) (b ** pb) (Element0 g eqg) =
  Element0
    (\(Element0 (eld, ela) eqfpa) =>
      Element0 (eld, g ela) $ trans eqfpa $ eqg ela)
    (\(Element0 (eld, ela) eqfpa) => Refl)

public export
CSPreImage : {0 c : Type} -> {d : Type} ->
  (d -> c) -> c -> CSliceObj d
CSPreImage {c} {d} = (|>) (CSGObj {c}) . CSBaseChange {c} {d}

-- Sigma, also known as dependent sum.
public export
CSSigma : {0 c, d : Type} -> (c -> d) -> CSliceFunctor c d
CSSigma {c} {d} f csl = (fst csl ** f . snd csl)

public export
CSGSigma : {0 c : Type} -> CSliceObj c -> Type
CSGSigma {c} = CSliceObjDomain . CSSigma {c} {d=()} (const ())

public export
CSGSigmaIsDom : {0 c : Type} -> (x : CSliceObj c) ->
  CSGSigma {c} x -> CSliceObjDomain {c} x
CSGSigmaIsDom {c} x = Prelude.id {a=(CSliceObjDomain x)}

public export
CSGDomToCSGSigma : {0 c : Type} -> (x : CSliceObj c) ->
  CSliceObjDomain {c} x -> CSGSigma {c} x
CSGDomToCSGSigma {c} x = Prelude.id {a=(CSliceObjDomain x)}

-- Sigma is also known as pushforward.
public export
CSPushF : {0 c, d : Type} -> (c -> d) -> CSliceObj c -> CSliceObj d
CSPushF = CSSigma

public export
csSigmaMap : {0 c, d : Type} -> {0 f : c -> d} ->
  CSliceFMap {c} {d} (CSSigma {c} {d} f)
csSigmaMap {c} {d} {f} (a ** pa) (b ** pb) (Element0 g eqg) =
  Element0 g $ \ela => cong f $ eqg ela

-- Pullback is the right adjoint of postcomposition, AKA pushfoward, AKA Sigma.
--
-- Adjunction details:
--  - C a category
--  - X, Y : objects of C
--  - f : a morphism, Y -> X
--  - Category on the left: C/X; category on the right: C/Y
--  - `L(f)` is postcomposition with `f` (AKA "Sigma"/"pushforward"), C/Y -> C/X
--  - `R(f)` is pullback along `f`, C/X -> C/Y
--  - Adjuncts: (C/X)(L(A), B) === (C/Y)(A, R(B)) (for A : C/Y; B : C/X)

-- Left adjunct of postcomposition/pullback adjunction.
-- This is the introduction rule for pullbacks (since the domain
-- component of a base change is a pullback).

-- Introduction rule for base change / pullback (in terms of Sigma).
public export
csSigmaLeftAdjunct : {0 c, d : Type} -> (f : c -> d) ->
  {x : CSliceObj c} -> {y : CSliceObj d} ->
  CSliceMorphism {c=d} (CSSigma {c} {d} f x) y ->
  CSliceMorphism {c} x (CSBaseChange {c=d} {d=c} f y)
csSigmaLeftAdjunct {c} {d} f {x=(x ** px)} {y=(y ** py)} (Element0 g eqg) =
  Element0 (\elx => Element0 (px elx, g elx) $ eqg elx) (\_ => Refl)

-- Introduction rule for sigma.
public export
csSigmaUnit : {0 c, d : Type} -> (f : c -> d) -> (x : CSliceObj c) ->
  CSliceMorphism {c} x (CSBaseChange {c=d} {d=c} f (CSSigma {c} {d} f x))
csSigmaUnit {c} {d} f x =
  csSigmaLeftAdjunct {c} {d} f {x} {y=(CSSigma {c} {d} f x)}
    (CSliceId {c=d} $ CSSigma {c} {d} f x)

-- Elimination rule for sigma.
public export
csSigmaRightAdjunct : {0 c, d : Type} -> (f : c -> d) ->
  {x : CSliceObj c} -> {y : CSliceObj d} ->
  CSliceMorphism {c} x (CSBaseChange {c=d} {d=c} f y) ->
  CSliceMorphism {c=d} (CSSigma {c} {d} f x) y
csSigmaRightAdjunct {c} {d} f {x=(x ** px)} {y=(y ** py)} (Element0 g eqg) =
  Element0 (snd . fst0 . g) $ \elx => trans (cong f $ eqg elx) (snd0 $ g elx)

-- Elimination rule for base change / pullback (in terms of Sigma).
public export
csSigmaCounit : {c, d : Type} -> (f : c -> d) -> (y : CSliceObj d) ->
  CSliceMorphism {c=d} (CSSigma {c} {d} f (CSBaseChange {c=d} {d=c} f y)) y
csSigmaCounit {c} {d} f y =
  csSigmaRightAdjunct {c} {d} f {x=(CSBaseChange {c=d} {d=c} f y)} {y}
    (CSliceId {c} $ CSBaseChange {c=d} {d=c} f y)

public export
CSGBCMorph : {c : Type} -> {0 d : Type} -> (c -> d) -> CSliceObj c -> SliceObj d
CSGBCMorph {c} {d} f x =
  flip (CSliceMorphism {c}) x . CSPreImage {c=d} {d=c} f

public export
CSGBCMorphOp : {c : Type} -> {0 d : Type} -> (c -> d) ->
  CSliceObj c -> SliceObj d
CSGBCMorphOp {c} {d} f x =
  CSliceMorphism {c} x . CSPreImage {c=d} {d=c} f

-- The covariant dependent hom-functor.
public export
CSPi : {c, d : Type} -> (c -> d) -> CSliceFunctor c d
CSPi {c} {d} = CSliceFromSlice {c=d} .* CSGBCMorph {c} {d}

public export
csPiMap : {0 c, d : Type} -> {0 f : c -> d} ->
  CSliceFMap {c} {d} (CSPi {c} {d} f)
csPiMap {c} {d} {f} (a ** pa) (b ** pb) (Element0 g eqg) =
  Element0
    (\(eld ** Element0 pi eqpi) =>
      (eld ** Element0 (g . pi) (\elc => trans (eqpi elc) $ eqg $ pi elc)))
    (\(eld ** Element0 pi eqpi) => Refl)

-- Introduction rule for pi.
public export
csPiLeftAdjunct : {0 c, d : Type} -> (f : c -> d) ->
  {x : CSliceObj c} -> {y : CSliceObj d} ->
  CSliceMorphism {c} (CSBaseChange {c=d} {d=c} f y) x ->
  CSliceMorphism {c=d} y (CSPi {c} {d} f x)
csPiLeftAdjunct {c} {d} f {x=(x ** px)} {y=(y ** py)} (Element0 g eqg) =
  Element0
    (\ely =>
      (py ely **
       Element0
        (\(Element0 (elc, ()) eq) => g $ Element0 (elc, ely) eq)
        (\(Element0 (elc, ()) eq) => eqg $ Element0 (elc, ely) eq)))
    (\_ => Refl)

-- Introduction rule for pullback (in terms of Pi).
public export
csPiUnit : {c, d : Type} -> (f : c -> d) -> (y : CSliceObj d) ->
  CSliceMorphism {c=d} y (CSPi {c} {d} f (CSBaseChange {c=d} {d=c} f y))
csPiUnit {c} {d} f y =
  csPiLeftAdjunct {c} {d} f {x=(CSBaseChange {c=d} {d=c} f y)} {y}
    (CSliceId {c} $ CSBaseChange {c=d} {d=c} f y)

-- Elimination rule for pullback (in terms of Pi).
public export
csPiRightAdjunct : {0 c, d : Type} -> (f : c -> d) ->
  {x : CSliceObj c} -> {y : CSliceObj d} ->
  CSliceMorphism {c=d} y (CSPi {c} {d} f x) ->
  CSliceMorphism {c} (CSBaseChange {c=d} {d=c} f y) x
csPiRightAdjunct {c} {d} f {x=(x ** px)} {y=(y ** py)} (Element0 g eqg) =
  Element0
    (\(Element0 (elc, ely) eq) =>
      fst0 (snd $ g ely) $ Element0 (elc, ()) $ trans eq $ eqg ely)
    (\(Element0 (elc, ely) eq) =>
      snd0 (snd $ g ely) $ Element0 (elc, ()) $ trans eq $ eqg ely)

-- Elimination rule for pi.
public export
csPiCounit : {c, d : Type} -> (f : c -> d) -> (x : CSliceObj c) ->
  CSliceMorphism {c} (CSBaseChange {c=d} {d=c} f (CSPi {c} {d} f x)) x
csPiCounit {c} {d} f x =
  csPiRightAdjunct {c} {d} f {x} {y=(CSPi {c} {d} f x)}
    (CSliceId {c=d} $ CSPi {c} {d} f x)

-- The dependent exponential functor, which is the contravariant dual of
-- the (covariant) CSPi.
public export
CSDepExp : {c, d : Type} -> (c -> d) -> CSliceFunctor c d
CSDepExp {c} {d} = CSliceFromSlice {c=d} .* CSGBCMorphOp {c} {d}

-- `CSDepExp` is contravariant.
public export
csDepExpMap : {0 c, d : Type} -> {0 f : c -> d} ->
  CSliceFContramap {c} {d} (CSDepExp {c} {d} f)
csDepExpMap {c} {d} {f} (a ** pa) (b ** pb) (Element0 m eqm) =
  Element0
    (\(eld ** Element0 exp eqexp) =>
     (eld **
      Element0
        (\ela => Element0 (pa ela, snd (fst0 (exp (m ela)))) $
          trans (cong f $ trans (eqm ela) $ eqexp (m ela)) $ snd0 $ exp $ m ela)
        (\_ => Refl))) $
    \(eld ** Element0 exp eqexp) => Refl

-- Polynomial functors are compositions of base changes, dependent sums
-- (`CSSigma`), and dependent products (`CSPi`).
public export
CSPolyF : {dom, dir, pos, cod : Type} ->
  (dir -> dom) -> (dir -> pos) -> (pos -> cod) ->
  CSliceObj dom -> CSliceObj cod
CSPolyF {dom} {dir} {pos} {cod} f g h =
  CSSigma h . CSPi g . CSBaseChange f

-- Polynomial functors are covariant.
public export
csPolyMap : {dom, dir, pos, cod : Type} ->
  {f : dir -> dom} -> {g : dir -> pos} -> {h : pos -> cod} ->
  CSliceFMap {c=dom} {d=cod} (CSPolyF f g h)
csPolyMap {dom} {dir} {pos} {cod} {f} {g} {h} a b m =
  csSigmaMap {f=h}
    (CSPi g (CSBaseChange f a)) (CSPi g (CSBaseChange f b)) $
    csPiMap {f=g} (CSBaseChange f a) (CSBaseChange f b) $
    csBaseChangeMap {f} a b m

-- Dirichlet functors are compositions of base changes, dependent sums
-- (`CSSigma`), and dependent exponentials (`CSDepExp`).
public export
CSDirichF : {dom, dir, pos, cod : Type} ->
  (dir -> dom) -> (dir -> pos) -> (pos -> cod) ->
  CSliceObj dom -> CSliceObj cod
CSDirichF {dom} {dir} {pos} {cod} f g h =
  CSSigma h . CSDepExp g . CSBaseChange f

-- Dirichlet functors are contravariant.
public export
csDirichMap : {dom, dir, pos, cod : Type} ->
  {f : dir -> dom} -> {g : dir -> pos} -> {h : pos -> cod} ->
  CSliceFContramap {c=dom} {d=cod} (CSDirichF f g h)
csDirichMap {dom} {dir} {pos} {cod} {f} {g} {h} a b m =
  csSigmaMap {f=h}
    (CSDepExp g (CSBaseChange f b)) (CSDepExp g (CSBaseChange f a)) $
    csDepExpMap {f=g} (CSBaseChange f a) (CSBaseChange f b) $
    csBaseChangeMap {f} a b m

-------------------------------------
---- Product-of-slice categories ----
-------------------------------------

-- The product of the slice category of `Type` over `c` with the slice
-- category of `Type` over `d` is equivalent to the slice category of
-- `Type` over `Either c d`.
public export
CProdSliceObj : Type -> Type -> Type
CProdSliceObj = CSliceObj .* Either

public export
CProdSlObjPair : {c, d : Type} ->
  CSliceObj c -> CSliceObj d -> CProdSliceObj c d
CProdSlObjPair {c} {d} (x ** px) (y ** py) =
  (Either x y ** bimap {f=Either} px py)

public export
CProdSlObj1 : {c, d : Type} -> CProdSliceObj c d -> CSliceObj c
CProdSlObj1 {c} {d} (x ** px) =
  (Subset0 x (IsLeftTrue . px) ** \(Element0 ex isl) => fromIsLeft isl)

public export
CProdSlObj2 : {c, d : Type} -> CProdSliceObj c d -> CSliceObj d
CProdSlObj2 {c} {d} (x ** px) =
  (Subset0 x (IsRightTrue . px) ** \(Element0 ex isl) => fromIsRight isl)

public export
CSqSliceObj : Type -> Type
CSqSliceObj c = CProdSliceObj c c

----------------------------------------------
---- Slice categories of slice categories ----
----------------------------------------------

-- As with a slice category of `Type`, an object of a slice category of a
-- slice category of `Type` is an object together with a morphism to the
-- object over which we are slicing the base category; in this case, a
-- _slice_ object together with a _slice_ morphism to the _slice_ object
-- over which we are slicing the slice category.
public export
CSliceObjOfSliceCat : {c : Type} -> CSliceObj c -> Type
CSliceObjOfSliceCat {c} sl = (sl' : CSliceObj c ** CSliceMorphism {c} sl' sl)

-- We shall show below that there is a second way of viewing a slice object
-- of a slice category:  as a slice category of `Type`, over a sigma object
-- (in `Type`) -- the sigma object being the result of applying the sigma
-- functor from the slice category to `Type` to the object over which we are
-- slicing the slice category.  When taking a dependent-type perspective and
-- viewing the slice category as the category of types depending on the object
-- over which we are slicing, the result of applying the sigma-to-`Type`
-- functor to an object of that category is the dependent sum (pair) of that
-- object viewed as a predicate (i.e. a function from the type corresponding
-- to the object over which we are slicing to `Type` itself).
public export
CSliceObjOverSigma : {0 c : Type} -> CSliceObj c -> Type
CSliceObjOverSigma {c} sl = CSliceObj (CSGSigma {c} sl)

-- This shows how given a slice object over a sigma type (which we have noted
-- above and shall show below is equivalent to an object of a slice category
-- of a slice category) can be viewed as a slice object of the base type
-- (the base type, from the dependent-type perspective, being the first,
-- non-dependent component of the dependent sum/pair).
public export
CSliceObjOverSigmaToBaseSlice : {0 c : Type} -> {sl : CSliceObj c} ->
  CSliceObjOverSigma {c} sl -> CSliceObj c
CSliceObjOverSigmaToBaseSlice {c} {sl=(x ** px)} (y ** py) =
  (CSGSigma {c=x} (y ** py) ** px . py)

-- There is also a second way of viewing an object of a slice category of a
-- slice category as a slice object of `Type` itself (i.e. a third way of
-- viewing such objects), as an object of a _full subcategory_ of a slice
-- category over a product, where the objects of the full subcategory are
-- selected by an additional commutativity condition.
public export
CSliceOverProdSubcatObj : {c : Type} -> CSliceObj c -> Type
CSliceOverProdSubcatObj {c} (x ** px) =
  Subset0 (CSliceObj (c, x)) $ \(y ** py) => ExtEq (fst . py) (px . snd . py)

-- Here we show the equivalence of the three ways of viewing objects of
-- slice categories of slice categories, by converting them amongst each
-- other in a loop.
public export
CSliceObjOfSliceCatToSliceObjOverSigma : {c : Type} -> {x : CSliceObj c} ->
  CSliceObjOfSliceCat {c} x -> CSliceObjOverSigma {c} x
CSliceObjOfSliceCatToSliceObjOverSigma {c} {x} csl =
  (fst (fst csl) ** fst0 (snd csl))

public export
CSliceObjOverSigmaToSliceOverProdSubcatObj : {c : Type} -> {x : CSliceObj c} ->
  CSliceObjOverSigma {c} x -> CSliceOverProdSubcatObj {c} x
CSliceObjOverSigmaToSliceOverProdSubcatObj {c} {x=(x ** px)} (y ** py) =
  Element0 (y ** \ely => (px $ py ely, py ely)) $ \_ => Refl

public export
CSliceOverProdSubcatToSliceObjOfSliceCat : {c : Type} -> {x : CSliceObj c} ->
  CSliceOverProdSubcatObj {c} x -> CSliceObjOfSliceCat {c} x
CSliceOverProdSubcatToSliceObjOfSliceCat {c} {x=(x ** px)}
  (Element0 (y ** py) ycomm) =
    ((y ** fst . py) ** Element0 (snd . py) ycomm)

public export
CSliceObjOverSigmaToObjOfSliceCat : {c : Type} -> {x : CSliceObj c} ->
  CSliceObjOverSigma {c} x ->
  CSliceObjOfSliceCat {c} x
CSliceObjOverSigmaToObjOfSliceCat =
  CSliceOverProdSubcatToSliceObjOfSliceCat
  .  CSliceObjOverSigmaToSliceOverProdSubcatObj

public export
CSliceObjOverProdSubcatObjToObjOverSigma : {c : Type} -> {x : CSliceObj c} ->
  CSliceOverProdSubcatObj {c} x ->
  CSliceObjOverSigma {c} x
CSliceObjOverProdSubcatObjToObjOverSigma =
  CSliceObjOfSliceCatToSliceObjOverSigma
  . CSliceOverProdSubcatToSliceObjOfSliceCat

public export
CSliceOfSliceCatToSliceOverProdSubcat : {c : Type} -> {x : CSliceObj c} ->
  CSliceObjOfSliceCat {c} x -> CSliceOverProdSubcatObj {c} x
CSliceOfSliceCatToSliceOverProdSubcat =
  CSliceObjOverSigmaToSliceOverProdSubcatObj
  .  CSliceObjOfSliceCatToSliceObjOverSigma

-- Relatedly, there is also an alternative way of looking at pullbacks: a
-- pullback in a slice category (including a slice category over the terminal
-- object, which is equivalent to simply `Type` itself) may be viewed as
-- a product in a slice category over the sigma object of the object over which
-- `Type` is being sliced.  Because of the equivalence above, this means that
-- a pullback constitutes a _fourth_ way of viewing an object of a slice
-- category of a slice category.
public export
CSPullbackAsSigmaSliceProd : {c : Type} -> {x, y, z : CSliceObj c} ->
  (f : CSliceMorphism {c} x z) -> (g : CSliceMorphism {c} y z) ->
  CSliceObjOverSigma {c} z
CSPullbackAsSigmaSliceProd {c} {x=(x ** px)} {y=(y ** py)} {z=z@(zb ** pz)}
  (Element0 f fcomm) (Element0 g gcomm) =
    CSProdObj {c=(CSGSigma {c} z)} (x ** f) (y ** g)

-- Here we show the equivalence of the definition of pullback as a slice
-- object over a sigma type with the earlier definition of pullback as an
-- equalizer of products (which is also equivalent to the direct
-- universal-morphism definition of pullbacks).
public export
CSPullbackToSigmaSliceProd : {c : Type} -> {x, y, z : CSliceObj c} ->
  (f : CSliceMorphism {c} x z) -> (g : CSliceMorphism {c} y z) ->
  CSliceMorphism {c}
    (CSPullback {c} {x} {y} {z} f g)
    (CSliceObjOverSigmaToBaseSlice {c} {sl=z} $
      CSPullbackAsSigmaSliceProd {c} {x} {y} {z} f g)
CSPullbackToSigmaSliceProd {c} {x=(x ** px)} {y=(y ** py)} {z=(z ** pz)}
  (Element0 f fcomm) (Element0 g gcomm) =
    Element0
      (\(Element0 (Element0 (elx, ely) pxyeq) fgeq) => Element0 (elx, ely) fgeq)
      (\(Element0 (Element0 (elx, ely) pxyeq) fgeq) => fcomm elx)

public export
CSPullbackFromSigmaSliceProd : {c : Type} -> {x, y, z : CSliceObj c} ->
  (f : CSliceMorphism {c} x z) -> (g : CSliceMorphism {c} y z) ->
  CSliceMorphism {c}
    (CSliceObjOverSigmaToBaseSlice {c} {sl=z} $
      CSPullbackAsSigmaSliceProd {c} {x} {y} {z} f g)
    (CSPullback {c} {x} {y} {z} f g)
CSPullbackFromSigmaSliceProd {c} {x=(x ** px)} {y=(y ** py)} {z=(z ** pz)}
  (Element0 f fcomm) (Element0 g gcomm) =
    Element0
      (\(Element0 (elx, ely) fgcomm) =>
        Element0
          (Element0 (elx, ely) $
            trans (fcomm elx) $ rewrite fgcomm in sym $ gcomm ely)
          fgcomm)
      (\(Element0 (elx, ely) fgcomm) =>
        sym $ fcomm elx)

public export
CSliceOfSliceCatToSliceOverSigma : {c : Type} -> {x : SliceObj c} ->
  CSliceObjOfSliceCat {c} (CSliceFromSlice x) -> SliceObj (Sigma {a=c} x)
CSliceOfSliceCatToSliceOverSigma {c} {x} =
  SliceFromCSlice {c=(Sigma {a=c} x)}
  . CSliceObjOfSliceCatToSliceObjOverSigma {c} {x=(CSliceFromSlice x)}

public export
SliceObjOverSigmaToObjOfSliceCat : {c : Type} -> {x : SliceObj c} ->
  SliceObj (Sigma {a=c} x) -> CSliceObjOfSliceCat {c} (CSliceFromSlice x)
SliceObjOverSigmaToObjOfSliceCat {c} {x} =
  CSliceObjOverSigmaToObjOfSliceCat {x=(CSliceFromSlice x)}
  . CSliceFromSlice {c=(Sigma {a=c} x)}

public export
CSliceOfSliceToCSliceOfSliceCat : {c : Type} -> {x : SliceObj c} ->
  CSliceOfSlice {c} x -> CSliceObjOfSliceCat {c} (CSliceFromSlice x)
CSliceOfSliceToCSliceOfSliceCat {c} {x} =
  SliceObjOverSigmaToObjOfSliceCat {c} {x}
  . CSliceOfSliceToSliceOfSigma {c} {sl=x}

public export
CSliceOfSliceCatToCSliceOfSlice : {c : Type} -> {x : SliceObj c} ->
  CSliceObjOfSliceCat {c} (CSliceFromSlice x) -> CSliceOfSlice {c} x
CSliceOfSliceCatToCSliceOfSlice {c} {x} =
  SliceOfSigmaToCSliceOfSlice {c} {sl=x}
  . CSliceOfSliceCatToSliceOverSigma {c} {x}

-----------------------------------------------
---- Higher categories of slice categories ----
-----------------------------------------------

-- The slices of `Type` themselves form a (two-)category (which is internal to
-- `Type`), where the morphisms, as usual in a two-category, are the functors
-- (between slice categories, in this case).
public export
Slice2CatObj : Type
Slice2CatObj = DPair Type CSliceObj

-- The object-map component of a functor which comprises a morphism
-- in the two-category of slices of `Type`.
public export
Slice2CatMorphObj : Slice2CatObj -> Slice2CatObj -> Type
Slice2CatMorphObj sx sy = CSliceFunctor (fst sx) (fst sy)

-- The morphism-map component of a functor which comprises a morphism
-- in the two-category of slices of `Type`.
public export
Slice2CatMorphMap : {sx, sy : Slice2CatObj} -> Slice2CatMorphObj sx sy -> Type
Slice2CatMorphMap {sx} {sy} = CSliceFMap {c=(fst sx)} {d=(fst sy)}

-- Lift an endofunctor on `Type` to a functor between slice categories.
-- Note that _which_ two slice categories the lifted functor goes between is
-- polymorphic in the base type of the slice, with the codomain category
-- computed from the domain category by the application of the endofunctor
-- on `Type`.  Consequently, `CSliceLift f` _itself_, without providing a
-- base-type parameter, is a natural transformation in `Type` from
-- `CSliceObj` _viewed_ as a functor to `BaseChangeF f CSliceObj`.
--
-- When we view `CSliceObj` itself as a functor, it goes from `Type` to
-- the two-category of slices of `Type` (where, as usual in a two-category,
-- the morphisms are the functors between (in this case, slice) categories),
-- taking an object `c` to the slice category `C/c`.
-- In this view, we have the following type signature:
--
-- CSliceFLift : {f : Type -> Type} ->
--   (fm : {0 a, b : Type} -> (a -> b) -> f a -> f b) ->
--   NaturalTransformation CSliceObj (BaseChangeF f CSliceObj)
--
-- But note now that _this_ is furthermore functorial in `f`.  So we could now
-- view `CSliceLift` (without either a base-type _or_ a function parameter)
-- as a _functor_ from the category of endofunctors on `Type`
-- (i.e., `Type -> Type`) to the category of _natural transformations_
-- on endofunctors of `Type`.  However, this viewpoint loses the information
-- that all of the output natural transformations are between functors which
-- have been pre-composed with `CSliceObj` viewed as an _internal_ functor
-- from `Type` to the internal two-category of slices of `Type`.
public export
CSliceFLift : {f : Type -> Type} ->
  (fm : {0 a, b : Type} -> (a -> b) -> f a -> f b) ->
  (c : Type) -> CSliceFunctor c (f c)
CSliceFLift {f} fm c (x ** px) = (f x ** fm {a=x} {b=c} px)

-- `CSliceFLift` using Idris's typeclass inference (on `Functor`).
public export
CSliceFLift' : {f : Type -> Type} -> Functor f =>
  (c : Type) -> CSliceFunctor c (f c)
CSliceFLift' {f} = CSliceFLift {f} (map {f})

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---- Dependent (slice) applicatives (lax monoidal functors) and monads ----
---------------------------------------------------------------------------
---------------------------------------------------------------------------

----------------------------
---- General operations ----
----------------------------

-- The signature of the `pure` or `unit` natural transformation of an
-- applicative slice endofunctor (such as any slice monad).
public export
CSlicePure : {c : Type} -> CSliceEndofunctor c -> Type
CSlicePure {c} = CSliceNatTrans {c} {d=c} (CSIdF c)

public export
CSlicePureCompose : {c : Type} ->
  (g, f : CSliceEndofunctor c) ->
  CSlicePure g -> CSlicePure f ->
  CSlicePure (g . f)
CSlicePureCompose {c} g f pg pf a = CSliceCompose (pg (f a)) (pf a)

-- The signature of the `apply` morphism of an applicative slice functor.
public export
CSliceApply : {c, d : Type} -> CSliceFunctor c d -> Type
CSliceApply {c} {d} f = (x, y : CSliceObj c) ->
  CSliceMorphism {c=d} (f (CSHomObj x y)) (CSHomObj (f x) (f y))

public export
CSliceApplyCompose : {c, d, e : Type} ->
  (g : CSliceFunctor d e) -> (f : CSliceFunctor c d) ->
  CSliceFMap g ->
  CSliceApply g -> CSliceApply f ->
  CSliceApply (g . f)
CSliceApplyCompose {c} {d} {e} g f gm ag af x y =
  CSliceCompose {u=(g (f (CSHomObj x y)))} {w=(CSHomObj (g (f x)) (g (f y)))}
    (ag (f x) (f y))
    (gm (f (CSHomObj x y)) (CSHomObj (f x) (f y)) (af x y))

-- The signature of the `bind` operation of a slice monad as a
-- natural transformation between functors from a slice category
-- to the base category (`Type`).
public export
CSliceBind : {c : Type} -> CSliceEndofunctor c -> Type
CSliceBind {c} m = (x, y : CSliceObj c) ->
  CSliceMorphism x (m y) -> CSliceMorphism (m x) (m y)

-- The signature of the `bind` morphism of a slice monad as a
-- natural transformation between slice endofunctors.
public export
CSliceInternalBind : {c : Type} -> CSliceEndofunctor c -> Type
CSliceInternalBind {c} m = (x, y : CSliceObj c) ->
  CSliceMorphism (CSHomObj x (m y)) (CSHomObj (m x) (m y))

-- The "internal" bind (a natural transformation between slice
-- endofunctors) is (strictly) stronger than the earlier bind
-- in `Type`.  (In particular, we can derive `CSliceApply` from it.)
public export
csBindFromInternalBind : {c : Type} -> (f : CSliceEndofunctor c) ->
  CSliceInternalBind f -> CSliceBind f
csBindFromInternalBind {c} f bi x y = csHomMorphToMeta (bi x y)

-- The domain of the internal-bind natural transformation takes `(a, b)` to
-- `a -> f b`.
public export
BindAsNTdom : {c : Type} -> CSliceEndofunctor c -> CSliceFunctor (Either c c) c
BindAsNTdom {c} f x = CSHomObj (CProdSlObj1 x) (f $ CProdSlObj2 x)

-- The codomain of the internal-bind natural transformation takes `(a, b)` to
-- `f a -> f b`.
public export
BindAsNTcod : {c : Type} -> CSliceEndofunctor c -> CSliceFunctor (Either c c) c
BindAsNTcod {c} f x = CSHomObj (f $ CProdSlObj1 x) (f $ CProdSlObj2 x)

public export
CSliceInternalBindAsNT : {c : Type} -> CSliceEndofunctor c -> Type
CSliceInternalBindAsNT {c} f =
  CSliceNatTrans {c=(Either c c)} {d=c} (BindAsNTdom f) (BindAsNTcod f)

-- The signature of the `join` or `multiplication` natural transformation of a
-- slice monad.
public export
CSliceJoin : {c : Type} -> CSliceEndofunctor c -> Type
CSliceJoin {c} f = CSliceNatTrans {c} {d=c} (f . f) f

public export
CSliceDistributor : {c : Type} ->
  CSliceEndofunctor c -> CSliceEndofunctor c -> Type
CSliceDistributor {c} g f = CSliceNatTrans {c} {d=c} (f . g) (g . f)

public export
CSliceJoinDistribCompose : {c : Type} ->
  (g, f : CSliceEndofunctor c) ->
  CSliceFMap {c} {d=c} g ->
  CSliceJoin g -> CSliceJoin f ->
  CSliceDistributor g f ->
  CSliceJoin (g . f)
CSliceJoinDistribCompose {c} g f mg jg jf dist =
  CSNTvcomp
    (CSWhiskerRight mg jf)
    (CSWhiskerLeft (CSNTvcomp (CSWhiskerLeft jg f) (CSWhiskerRight mg dist)) f)

public export
csBindFromMapAndJoin : {c : Type} ->
  (f : CSliceEndofunctor c) -> (fm : CSliceFMap f) ->
  CSliceJoin f -> CSliceBind f
csBindFromMapAndJoin {c} f fm j x y = CSliceCompose (j y) . fm x (f y)

public export
csJoinFromBind : {c : Type} -> (f : CSliceEndofunctor c) ->
  CSliceBind f -> CSliceJoin f
csJoinFromBind {c} f b a = b (f a) a $ CSliceId (f a)

public export
csJoinFromInternalBind : {c : Type} -> (f : CSliceEndofunctor c) ->
  CSliceInternalBind f -> CSliceJoin f
csJoinFromInternalBind {c} f =
  csJoinFromBind f . csBindFromInternalBind f

public export
csMapFromPureAndBind : {c : Type} -> (f : CSliceEndofunctor c) ->
  CSlicePure {c} f -> CSliceBind {c} f ->
  CSliceFMap {c} {d=c} f
csMapFromPureAndBind {c} f pu bi x y = bi x y . CSliceCompose (pu y)

public export
csMapFromPureAndInternalBind : {c : Type} -> (f : CSliceEndofunctor c) ->
  CSlicePure {c} f -> CSliceInternalBind {c} f ->
  CSliceFMap {c} {d=c} f
csMapFromPureAndInternalBind {c} f pu bi =
  csMapFromPureAndBind f pu (csBindFromInternalBind f bi)

public export
csInternalMapFromPureAndInternalBind : {c : Type} ->
  (f : CSliceEndofunctor c) ->
  CSlicePure {c} f -> CSliceInternalBind {c} f ->
  CSliceInternalFMap {c} f
csInternalMapFromPureAndInternalBind {c} f pu bi x y =
  CSliceCompose
    {u=(CSHomObj x y)}
    {v=(CSHomObj x (f y))}
    {w=(CSHomObj (f x) (f y))}
    (bi x y)
    (csContravarInternalYonedaToNTHom (pu y) x)

public export
csInternalBindFromMapAndJoin : {c : Type} ->
  (f : CSliceEndofunctor c) ->
  (fm : CSliceInternalFMap f) -> CSliceJoin f -> CSliceInternalBind f
csInternalBindFromMapAndJoin {c} f fm j x y =
  CSliceCompose
    {u=(CSHomObj x (f y))}
    {v=(CSHomObj (f x) (f (f y)))}
    {w=(CSHomObj (f x) (f y))}
    (csContravarInternalYonedaToNTHom (j y) (f x))
    (fm x (f y))

-- To see this and the following function as they would be written in
-- Haskell, see the definition of `apply` in terms of `pure` and `bind` at
-- https://www.cis.upenn.edu/~cis1940/fall16/lectures/08-functor-applicative.html
-- (under "Monad < Applicative < Functor").
public export
csApplyFromBindHelper : {c : Type} -> (x, y, z : CSliceObj c) ->
  CSliceMorphism
    (CSHomObj y z)
    (CSHomObj (CSHomObj (CSHomObj (CSHomObj x y) z) z) (CSHomObj x z))
csApplyFromBindHelper {c} x y z =
  CSliceCompose
    {u=(CSHomObj y z)}
    {v=(CSHomObj x (CSHomObj (CSHomObj x y) z))}
    {w=(CSHomObj (CSHomObj (CSHomObj (CSHomObj x y) z) z) (CSHomObj x z))}
    (csInternalPipe x (CSHomObj (CSHomObj x y) z) z) $
  CSliceCompose
    {u=(CSHomObj y z)}
    {v=(CSHomObj (CSHomObj (CSHomObj x y) y) (CSHomObj (CSHomObj x y) z))}
    {w=(CSHomObj x (CSHomObj (CSHomObj x y) z))}
    (csInternalPreCompFlipApp {c} x y (CSHomObj (CSHomObj x y) z))
    (csInternalCompose (CSHomObj x y) y z)

public export
csApplyFromPureAndInternalBind : {c : Type} -> (f : CSliceEndofunctor c) ->
  CSlicePure {c} f -> CSliceInternalBind {c} f ->
  CSliceApply {c} {d=c} f
csApplyFromPureAndInternalBind {c} f pu bi x y =
  CSliceCompose
    {u=(f (CSHomObj x y))}
    {v=(CSHomObj (CSHomObj (CSHomObj x y) (f y)) (f y))}
    {w=(CSHomObj (f x) (f y))}
    (CSliceCompose
      {u=(CSHomObj (CSHomObj (CSHomObj x y) (f y)) (f y))}
      {v=(CSHomObj x (f y))}
      {w=(CSHomObj (f x) (f y))}
      (bi x y)
      (csHomMorphToMeta
        {c}
        {w=y}
        {x=(f y)}
        {y=(CSHomObj (CSHomObj (CSHomObj x y) (f y)) (f y))}
        {z=(CSHomObj x (f y))}
        (csApplyFromBindHelper x y (f y)) (pu y)))
    (csFlip {x=(CSHomObj (CSHomObj x y) (f y))} {y=(f (CSHomObj x y))} $
      bi (CSHomObj x y) y)

----------------------------
---- Dependent `Either` ----
----------------------------

public export
csEitherPure : {c : Type} -> (e : CSliceObj c) -> CSlicePure {c} (CSCopObj e)
csEitherPure {c} = csInjR

public export
csEitherInternalFMap : {c : Type} ->
  (e : CSliceObj c) -> CSliceInternalFMap (CSCopObj {c} e)
csEitherInternalFMap {c} e x y =
  csCurry {x=(CSHomObj x y)} {y=(CSCopObj e x)} {z=(CSCopObj e y)}
  $ CSliceCompose
    {u=(CSProdObj (CSHomObj x y) (CSCopObj e x))}
    {v=(CSCopObj (CSProdObj (CSHomObj x y) e) (CSProdObj (CSHomObj x y) x))}
    {w=(CSCopObj e y)}
    (csEitherBimap
      {w=(CSProdObj (CSHomObj x y) e)}
      {x=(CSProdObj (CSHomObj x y) x)}
      (csProj2 (CSHomObj x y) e)
      (csEval x y))
    $ csDistrib (CSHomObj x y) e x

public export
csEitherJoin : {c : Type} -> (e : CSliceObj c) -> CSliceJoin {c} (CSCopObj e)
csEitherJoin {c} e a =
  csCase {x=e} {y=(CSCopObj e a)} {z=(CSCopObj e a)}
    (csInjL e a)
    (CSliceId (CSCopObj e a))

public export
csEitherInternalBind : {c : Type} ->
  (e : CSliceObj c) -> CSliceInternalBind {c} (CSCopObj e)
csEitherInternalBind {c} e =
  csInternalBindFromMapAndJoin {c} (CSCopObj e)
    (csEitherInternalFMap e) (csEitherJoin e)

public export
csEitherMap : {c : Type} -> (e : CSliceObj c) ->
  CSliceFMap {c} {d=c} (CSCopObj e)
csEitherMap {c} e =
  CSliceFMapFromInternalFMap {c} (CSCopObj e) (csEitherInternalFMap e)

public export
csEitherApply : {c : Type} ->
  (e : CSliceObj c) -> CSliceApply {c} {d=c} (CSCopObj e)
csEitherApply {c} e =
  csApplyFromPureAndInternalBind {c} (CSCopObj e)
    (csEitherPure e) (csEitherInternalBind e)

public export
csEitherBind : {c : Type} -> (e : CSliceObj c) -> CSliceBind {c} (CSCopObj e)
csEitherBind {c} e =
  csBindFromInternalBind (CSCopObj e) (csEitherInternalBind e)

------------------------------------
---- Dependent `Reader` (`Hom`) ----
------------------------------------

public export
csHomInternalFMap : {c : Type} ->
  (a : CSliceObj c) -> CSliceInternalFMap (CSHomObj {c} a)
csHomInternalFMap = csInternalCompose

public export
csHomPure : {c : Type} -> (a : CSliceObj c) -> CSlicePure {c} (CSHomObj a)
csHomPure {c} (a ** pa) (b ** pb) =
  Element0 (\eb => (pb eb ** \_ => Element0 eb Refl)) (\_ => Refl)

public export
csHomJoin : {c : Type} -> (a : CSliceObj c) -> CSliceJoin {c} (CSHomObj a)
csHomJoin {c} a x =
  csFlip {y=(CSHomObj a (CSHomObj a x))}
  $ CSlicePipe
  {u=a} {v=(CSProdObj a a)} {w=(CSHomObj (CSHomObj a (CSHomObj a x)) x)}
  (csDiag a)
  $ csFlip {x=(CSHomObj a (CSHomObj a x))} {y=(CSProdObj a a)}
  $ csInternalUncurry a a x

public export
csHomInternalBind : {c : Type} ->
  (a : CSliceObj c) -> CSliceInternalBind {c} (CSHomObj a)
csHomInternalBind {c} a =
  csInternalBindFromMapAndJoin {c} (CSHomObj a)
    (csHomInternalFMap a) (csHomJoin a)

public export
csHomMap : {c : Type} -> (a : CSliceObj c) ->
  CSliceFMap {c} {d=c} (CSHomObj a)
csHomMap {c} a =
  csMapFromPureAndInternalBind {c} (CSHomObj a)
    (csHomPure a) (csHomInternalBind a)

public export
csHomApply : {c : Type} ->
  (a : CSliceObj c) -> CSliceApply {c} {d=c} (CSHomObj a)
csHomApply {c} a =
  csApplyFromPureAndInternalBind {c} (CSHomObj a)
    (csHomPure a) (csHomInternalBind a)

public export
csHomBind : {c : Type} -> (a : CSliceObj c) -> CSliceBind {c} (CSHomObj a)
csHomBind {c} a =
  csBindFromInternalBind {c} (CSHomObj a) (csHomInternalBind a)

--------------------------------------------------------
---- Dependent combined `Reader` (`Hom`) + `Either` ----
--------------------------------------------------------

public export
CSHomEither : {c : Type} ->
  CSliceObj c -> CSliceObj c -> CSliceEndofunctor c
CSHomEither {c} a e = CSHomObj {c} a . CSCopObj {c} e

public export
csHomEitherPure : {c : Type} -> (a, e : CSliceObj c) ->
  CSlicePure {c} (CSHomEither a e)
csHomEitherPure {c} a e =
  CSlicePureCompose {c} (CSHomObj {c} a) (CSCopObj {c} e)
    (csHomPure {c} a) (csEitherPure {c} e)

public export
csHomEitherInternalMap : {c : Type} -> (a, e : CSliceObj c) ->
  CSliceInternalFMap {c} (CSHomEither a e)
csHomEitherInternalMap {c} a e =
  CSliceInternalFMapCompose (CSHomObj a) (CSCopObj e)
    (csHomInternalFMap {c} a) (csEitherInternalFMap {c} e)

public export
csHomEitherMap : {c : Type} -> (a, e : CSliceObj c) ->
  CSliceFMap {c} {d=c} (CSHomEither a e)
csHomEitherMap {c} a e =
  CSliceFMapFromInternalFMap (CSHomEither a e) (csHomEitherInternalMap {c} a e)

public export
csHomEitherApply : {c : Type} -> (a, e : CSliceObj c) ->
  CSliceApply {c} (CSHomEither a e)
csHomEitherApply {c} a e =
  CSliceApplyCompose {c} {d=c} {e=c} (CSHomObj {c} a) (CSCopObj {c} e)
    (csHomMap {c} a) (csHomApply {c} a) (csEitherApply {c} e)

public export
csHomEitherDistrib : {c : Type} -> (a, e : CSliceObj c) ->
  CSliceDistributor {c} (CSHomObj a) (CSCopObj e)
csHomEitherDistrib {c} a e x =
  csCase {x=e} {y=(CSHomObj a x)} {z=(CSHomObj a (CSCopObj e x))}
    (csFlip {z=(CSCopObj e x)} $
      csConstMorph {x=a} {y=e} {z=(CSCopObj e x)} $ csInjL e x)
    (csHomMap a x (CSCopObj e x) $ csInjR e x)

public export
csHomEitherJoin : {c : Type} -> (a, e : CSliceObj c) ->
  CSliceJoin {c} (CSHomEither a e)
csHomEitherJoin {c} a e =
  CSliceJoinDistribCompose {c}
    (CSHomObj a) (CSCopObj e)
    (csHomMap a) (csHomJoin a) (csEitherJoin e) (csHomEitherDistrib a e)

public export
csHomEitherInternalBind : {c : Type} -> (a, e : CSliceObj c) ->
  CSliceInternalBind {c} (CSHomEither a e)
csHomEitherInternalBind a e =
  csInternalBindFromMapAndJoin (CSHomEither a e)
    (csHomEitherInternalMap {c} a e) (csHomEitherJoin {c} a e)

public export
csHomEitherBind : {c : Type} -> (a, e : CSliceObj c) ->
  CSliceBind {c} (CSHomEither a e)
csHomEitherBind {c} a e =
  csBindFromInternalBind (CSHomEither a e)
    (csHomEitherInternalBind {c} a e)

------------------------------------------------------
------------------------------------------------------
---- Dependent polynomial endofunctors as W-types ----
------------------------------------------------------
------------------------------------------------------

--------------------------------------------------
---- Definition and interpretation of W-types ----
--------------------------------------------------

public export
record WTypeFunc (dom, cod : Type) where
  constructor MkWTF
  wtPos : Type
  wtDir : Type
  wtAssign : wtDir -> dom
  wtDirSlice : wtDir -> wtPos
  wtPosSlice : wtPos -> cod

public export
WTypeEndoFunc : Type -> Type
WTypeEndoFunc base = WTypeFunc base base

public export
CSPolyWTF : {dom, cod : Type} -> WTypeFunc dom cod -> CSliceFunctor dom cod
CSPolyWTF {dom} {cod} wtf =
  CSPolyF {dom} {dir=(wtDir wtf)} {pos=(wtPos wtf)} {cod}
    (wtAssign wtf) (wtDirSlice wtf) (wtPosSlice wtf)

public export
csPolyMapWTF : {dom, cod : Type} -> (wtf : WTypeFunc dom cod) ->
  CSliceFMap {c=dom} {d=cod} (CSPolyWTF {dom} {cod} wtf)
csPolyMapWTF {dom} {cod} wtf =
  csPolyMap {dom} {dir=(wtDir wtf)} {pos=(wtPos wtf)} {cod}
    {f=(wtAssign wtf)} {g=(wtDirSlice wtf)} {h=(wtPosSlice wtf)}

public export
CSDirichWTF : {dom, cod : Type} -> WTypeFunc dom cod -> CSliceFunctor dom cod
CSDirichWTF {dom} {cod} wtf =
  CSDirichF {dom} {dir=(wtDir wtf)} {pos=(wtPos wtf)} {cod}
    (wtAssign wtf) (wtDirSlice wtf) (wtPosSlice wtf)

public export
csDirichMapWTF : {dom, cod : Type} -> (wtf : WTypeFunc dom cod) ->
  CSliceFContramap {c=dom} {d=cod} (CSDirichWTF {dom} {cod} wtf)
csDirichMapWTF {dom} {cod} wtf =
  csDirichMap {dom} {dir=(wtDir wtf)} {pos=(wtPos wtf)} {cod}
    {f=(wtAssign wtf)} {g=(wtDirSlice wtf)} {h=(wtPosSlice wtf)}

public export
InterpWTF : {parambase, posbase : Type} ->
  WTypeFunc parambase posbase -> SliceFunctor parambase posbase
InterpWTF {parambase} {posbase} wtf sl ib =
  (i : PreImage {a=(wtPos wtf)} {b=posbase} (wtPosSlice wtf) ib **
   (d : PreImage {a=(wtDir wtf)} {b=(wtPos wtf)} (wtDirSlice wtf) (fst0 i)) ->
   sl $ wtAssign wtf $ fst0 d)

-----------------------------
---- Algebras of W-types ----
-----------------------------

public export
WTFAlg : {a : Type} -> WTypeEndoFunc a -> SliceObj a -> Type
WTFAlg {a} wtf sa = SliceMorphism {a} (InterpWTF wtf sa) sa

public export
CSWPolyAlgMap : {c : Type} -> WTypeEndoFunc c -> CSliceObj c -> Type
CSWPolyAlgMap {c} wtf = CSliceFAlgMap {c} (CSPolyWTF {dom=c} {cod=c} wtf)

-------------------------------------
---- Initial algebras of W-types ----
-------------------------------------

public export
data SliceWTFMu : {0 c : Type} -> WTypeEndoFunc c -> SliceObj c where
  InWM : {0 c : Type} -> {0 wtf : WTypeEndoFunc c} ->
    SliceAlg {a=c}
      (SliceFunctorFromCSlice {c} $ CSPolyWTF {dom=c} {cod=c} wtf)
      (SliceWTFMu {c} wtf)

public export
CSWTFMu : {c : Type} -> WTypeEndoFunc c -> CSliceObj c
CSWTFMu {c} wtf = CSliceFromSlice {c} (SliceWTFMu {c} wtf)

mutual
  public export
  0 cswCataTot :
    {0 c : Type} -> {0 wtf : WTypeEndoFunc c} -> {x : CSliceObj c} ->
    CSWPolyAlgMap {c} wtf x -> fst (CSWTFMu {c} wtf) -> fst x
  cswCataTot {c = c} {wtf=(MkWTF pos dir f g h)} {x=(x ** px)}
    (Element0 alg algeq) (elc ** (InWM elc (Element0 (i ** d) eq))) =
      alg (i ** Element0 ?cswCataTot_hole_1 ?cswCataTot_hole_2)

  public export
  0 cswCataEq :
    {0 c : Type} -> {0 wtf : WTypeEndoFunc c} -> {x : CSliceObj c} ->
    (alg : CSWPolyAlgMap {c} wtf x) ->
    ExtEq (snd $ CSWTFMu {c} wtf) (snd x . cswCataTot {c} {wtf} {x} alg)
  cswCataEq {c} {wtf=(MkWTF pos dir f g h)} {x=(x ** px)}
    (Element0 alg algeq) (elc ** (InWM elc (Element0 (i ** d) eq))) =
      ?cswCataEq_hole

public export
0 cswCata : {0 c : Type} -> {0 wtf : WTypeEndoFunc c} -> {x : CSliceObj c} ->
  CSWPolyAlgMap {c} wtf x -> CSliceMorphism {c} (CSWTFMu {c} wtf) x
cswCata {c} {wtf} {x} alg =
  Element0 (cswCataTot {c} {wtf} {x} alg) (cswCataEq {c} {wtf} {x} alg)

public export
data WTFMu : {a : Type} -> WTypeEndoFunc a -> SliceObj a where
  InWTFM : {a : Type} -> {wtf : WTypeEndoFunc a} ->
    (i : (dc : a ** PreImage {a=(wtPos wtf)} {b=a} (wtPosSlice wtf) dc)) ->
    ((d :
        PreImage {a=(wtDir wtf)} {b=(wtPos wtf)}
          (wtDirSlice wtf) (fst0 (snd i))) ->
      WTFMu {a} wtf (wtAssign wtf (fst0 d))) ->
    WTFMu {a} wtf (fst i)

public export
wtfCata : {0 a : Type} -> {wtf : WTypeEndoFunc a} -> {sa : SliceObj a} ->
  WTFAlg wtf sa -> SliceMorphism {a} (WTFMu wtf) sa
wtfCata {a} {wtf} {sa} alg _ (InWTFM (dc ** i) dm) =
  alg dc (i ** \d => wtfCata {a} {wtf} {sa} alg (wtAssign wtf (fst0 d)) $ dm d)

------------------------------------------
------------------------------------------
---- Bundles, refinements, and fibers ----
------------------------------------------
------------------------------------------

public export
Bundle : Type
Bundle = DPair Type CSliceObj

public export
BundleBase : Bundle -> Type
BundleBase = fst

public export
BundleTotal : Bundle -> Type
BundleTotal (_ ** so) = fst so

public export
0 BundleProj :
  (bundle : Bundle) -> (BundleTotal bundle) -> (BundleBase bundle)
BundleProj (_ ** so) = snd so

public export
BundleFiber : (bundle : Bundle) -> (baseElem : BundleBase bundle) -> Type
BundleFiber bundle baseElem =
  Subset0 (BundleTotal bundle) (Equal baseElem . BundleProj bundle)

public export
CRefinementBy : Type -> Type
CRefinementBy = CSliceObj . Maybe

public export
CRefinement : Type
CRefinement = DPair Type CRefinementBy

public export
CRefinementBundle : CRefinement -> Bundle
CRefinementBundle (base ** slice) = (Maybe base ** slice)

public export
CRefinementBase : CRefinement -> Type
CRefinementBase (base ** _) = base

public export
CRefinementTotal : CRefinement -> Type
CRefinementTotal = BundleTotal . CRefinementBundle

public export
0 CRefinementProj :
  (r : CRefinement) -> (CRefinementTotal r) -> Maybe (CRefinementBase r)
CRefinementProj (_ ** so) = snd so

public export
CRefinementFiber :
  (r : CRefinement) -> (baseElem : Maybe (CRefinementBase r)) -> Type
CRefinementFiber (base ** so) baseElem = BundleFiber (Maybe base ** so) baseElem

public export
JustFiber : (r : CRefinement) -> (baseElem : CRefinementBase r) -> Type
JustFiber (base ** so) baseElem = BundleFiber (Maybe base ** so) (Just baseElem)

public export
NothingFiber : (r : CRefinement) -> Type
NothingFiber (base ** so) = BundleFiber (Maybe base ** so) Nothing

-----------------------------------------------------------
-----------------------------------------------------------
---- Fixed points in arbitrary subcategories of `Type` ----
-----------------------------------------------------------
-----------------------------------------------------------

-----------------------------
-----------------------------
---- Dependent relations ----
-----------------------------
-----------------------------

-- The domain of the type of dependent relations between two slice objects
-- in the same (slice) category.
public export
DepRelObj : {a : Type} -> SliceObj (SliceObj a, SliceObj a)
DepRelObj {a} (sl, sl') = (x : a ** (sl x, sl' x))

-- The type of dependent relations between two slice objects over
-- the same object (i.e. two slice objects in the same (slice) category),
-- where the dependent relation respects the slicing (only terms with the
-- same signature can be related).
public export
DepRelOn : {a : Type} -> SliceObj (SliceObj a, SliceObj a)
DepRelOn {a} sls = SliceObj (DepRelObj {a} sls)

public export
data DepFreeEqF : {0 a : Type} -> {sl : SliceObj a} ->
    SliceEndofunctor (DepRelObj {a} (sl, sl)) where
  DFErefl :
    {0 a : Type} -> {0 sl : SliceObj a} -> {0 rel : DepRelOn {a} (sl, sl)} ->
    {0 x : a} -> (sx : sl x) -> DepFreeEqF {a} {sl} rel (x ** (sx, sx))
  DFEsym :
    {0 a : Type} -> {0 sl : SliceObj a} -> {0 rel : DepRelOn {a} (sl, sl)} ->
    {0 x : a} -> {sx, sx' : sl x} ->
    rel (x ** (sx, sx')) ->
    DepFreeEqF {a} {sl} rel (x ** (sx', sx))
  DFEtrans :
    {0 a : Type} -> {0 sl : SliceObj a} -> {0 rel : DepRelOn {a} (sl, sl)} ->
    {0 x : a} -> {sx, sx', sx'' : sl x} ->
    rel (x ** (sx', sx'')) ->
    rel (x ** (sx, sx')) ->
    DepFreeEqF {a} {sl} rel (x ** (sx, sx''))

public export
depFreeEqMap : {a : Type} -> {sl : SliceObj a} ->
  {rs, rs' : SliceObj (DepRelObj {a} (sl, sl))} ->
  SliceMorphism {a=(DepRelObj (sl, sl))} rs rs' ->
  SliceMorphism {a=(DepRelObj {a} (sl, sl))} (DepFreeEqF rs) (DepFreeEqF rs')
depFreeEqMap {a} {sl} {rs} {rs'} m _ feq =
  case feq of
    DFErefl sx => DFErefl sx
    DFEsym {x} {sx} {sx'} eq => DFEsym $ m (x ** (sx, sx')) eq
    DFEtrans {x} {sx} {sx'} {sx''} eq eq' =>
      DFEtrans (m (x ** (sx', sx'')) eq) (m (x ** (sx, sx')) eq')

public export
DepFreeEqCata : {a : Type} -> SliceObj a -> Type
DepFreeEqCata {a} sl =
  SliceFreeFEval {a=(DepRelObj {a} (sl, sl))} (DepFreeEqF {a} {sl})

public export
DepFreeEqCataF : {a : Type} -> SliceObj a -> Type
DepFreeEqCataF {a} sl =
  SliceFreeFEvalF {a=(DepRelObj {a} (sl, sl))} (DepFreeEqF {a} {sl})

mutual
  public export
  depFreeEqCataF : {a : Type} -> {sl : SliceObj a} -> DepFreeEqCataF {a} sl
  depFreeEqCataF {a} {sl} sv sa subst alg m eq =
    alg m $ case eq of
      DFErefl f => DFErefl f
      DFEsym {x} {sx} {sx'} eq =>
        DFEsym $ depFreeEqCata {a} {sl} sv sa subst alg (x ** (sx, sx')) eq
      DFEtrans {x} {sx} {sx'} {sx''} eq eq' =>
        DFEtrans
          (depFreeEqCata {a} {sl} sv sa subst alg (x ** (sx', sx'')) eq)
          (depFreeEqCata {a} {sl} sv sa subst alg (x ** (sx, sx')) eq')

  public export
  depFreeEqCata : {a : Type} -> {sl : SliceObj a} -> DepFreeEqCata {a} sl
  depFreeEqCata {a} {sl} sv sa subst alg m (InSlF m (InSlV v)) =
    subst m v
  depFreeEqCata {a} {sl} sv sa subst alg m (InSlF m (InSlC eq)) =
    depFreeEqCataF {a} {sl} sv sa subst alg m eq

--------------------
--------------------
---- Bifunctors ----
--------------------
--------------------

-- A bifunctor applied to a type is a functor.  This is simply the
-- currying adjunction in the category of functors -- the functor
-- categories `[C, [D, E]]` and `[C × D, E]` are equivalent.
public export
[BifunctorToFunctor] Bifunctor f => Functor (f a) where
  map = mapSnd

-- A bifunctor with its arguments flipped is a bifunctor.  This
-- reflects the symmetry of the product.
public export
Bifunctor f => Bifunctor (flip f) where
  bimap f g = bimap g f

--------------------------------------------------------------
--------------------------------------------------------------
---- Idris categories: `[Type]`, product, and endofunctor ----
--------------------------------------------------------------
--------------------------------------------------------------

---------------------------------------------------------------
---- Objects/morphisms in `[Type]` (Idris's base category) ----
---------------------------------------------------------------

public export
ObjectT : Type
ObjectT = Type

public export
MorphismT : ObjectT -> ObjectT -> Type
MorphismT a b = a -> b

----------------------------------------------------------------------------
---- Objects/morphisms in `[Type x Type]` (the base's product category) ----
----------------------------------------------------------------------------

public export
ObjectP : Type
ObjectP = (Type, Type)

public export
MorphismP : ObjectP -> ObjectP -> Type
MorphismP (a, b) (c, d) = (MorphismT a c, MorphismT b d)

-------------------------------------------------------------------------------
---- Objects/morphisms in `[Type, Type]` (the base's endofunctor category) ----
-------------------------------------------------------------------------------

public export
ObjectF : Type
ObjectF = Type -> Type

-- Morphisms in the endofunctor category are natural transformations in
-- the base category.
public export
MorphismF : ObjectF -> ObjectF -> Type
MorphismF f g = (a : Type) -> MorphismT (f a) (g a)

------------------------------------------
---- Identity/composition in `[Type]` ----
------------------------------------------

public export
IdT : (a : ObjectT) -> MorphismT a a
IdT a = Prelude.Basics.id {a}

public export
ComposeT : {a, b, c : ObjectT} ->
  MorphismT b c -> MorphismT a b -> MorphismT a c
ComposeT = (.)

-------------------------------------------------
---- Identity/composition in `[Type x Type]` ----
-------------------------------------------------

public export
IdP : (a : ObjectP) -> MorphismP a a
IdP (a, b) = (IdT a, IdT b)

public export
ComposeP : {a, b, c : ObjectP} ->
  MorphismP b c -> MorphismP a b -> MorphismP a c
ComposeP {a=(a, a')} {b=(b, b')} {c=(c, c')} (g, g') (f, f') =
  (ComposeT {a} {b} {c} g f, ComposeT {a=a'} {b=b'} {c=c'} g' f')

------------------------------------------------
---- Identity/composition in `[Type, Type]` ----
------------------------------------------------

-- The identity in the functor category `[Type, Type]`.
public export
IdF : (f : ObjectF) -> MorphismF f f
IdF f a = Prelude.Basics.id {a=(f a)}

-- Composition in the functor category `[Type, Type]`.
-- This is vertical composition of natural transformations.
public export
ComposeF : {f, g, h : ObjectF} ->
  MorphismF g h -> MorphismF f g -> MorphismF f h
ComposeF beta alpha a = ComposeT (beta a) (alpha a)

-- The functor category also has composition of _objects_.
public export
ComposeFObj : ObjectF -> ObjectF -> ObjectF
ComposeFObj = (.)

-- The functor category also has horizonal composition.
public export
ComposeFH : {f, g, h, j : ObjectF} -> Functor g =>
  MorphismF g j -> MorphismF f h -> MorphismF (ComposeT g f) (ComposeT j h)
ComposeFH {g} beta alpha a = (beta (h a) . map {f=g} (alpha a))

---------------------------------------
---------------------------------------
---- Polynomial functors on `Type` ----
---------------------------------------
---------------------------------------

-------------------
---- Constants ----
-------------------

-- Given an object `a`, `Const a` is an endofunctor which takes all objects
-- to `a`.
public export
ConstF : Type -> Type -> Type
ConstF a _ = a

public export
Functor (ConstF a) where
  map = const id

--------------------------------------
---- Terminal and initial objects ----
--------------------------------------

public export
TerminalMonad : Type -> Type
TerminalMonad = ConstF Unit

public export
Functor TerminalMonad where
  map _ () = ()

public export
TerminalNTUnit : (a : Type) -> a -> TerminalMonad a
TerminalNTUnit _ = const ()

public export
TerminalNaturality : {a, b : Type} -> (m : a -> b) ->
  map {f=TerminalMonad} m . TerminalNTUnit a = TerminalNTUnit b . m
TerminalNaturality _ = Refl

public export
InitialComonad : Type -> Type
InitialComonad = ConstF Void

public export
Functor InitialComonad where
  map _ v = v

public export
InitialNTCounit : (0 a : Type) -> InitialComonad a -> a
InitialNTCounit = voidF

public export
InitialNaturality : {a, b : Type} -> (m : a -> b) ->
  ExtEq (InitialNTCounit b . map {f=InitialComonad} m) (m . InitialNTCounit a)
InitialNaturality _ v = void v

------------------
---- Products ----
------------------

public export
MkPairF : {0 a, b, c : Type} -> (a -> b) -> (a -> c) -> a -> (b, c)
MkPairF = biapp MkPair

-- `ProductF` is an operator on endofunctors which takes two endofunctors
-- to their product.  `ProductF` is therefore not itself an endofunctor; it
-- is a higher-order functor.  (If `Poly[C]` is the category of polynomial
-- endofunctors on some category `C` -- if all of `C`'s endofunctors are
-- polynomial, then `Poly[C]` is `[C,C]` -- then `ProductF` is an object of
-- [Poly[C] x Poly[C], Poly[C].  That is, it is a bifunctor on `Poly[C]`.)
public export
ProductF : (Type -> Type) -> (Type -> Type) -> Type -> Type
ProductF f g a = (f a, g a)

public export
ProdFunctor : {0 f, g : Type -> Type} ->
  Functor f -> Functor g -> Functor (ProductF f g)
ProdFunctor (MkFunctor mapf) (MkFunctor mapg) =
  MkFunctor (\m, p => (mapf m (fst p), mapg m (snd p)))

public export
[ProdFunctorI] (l : Functor f) => (r : Functor g) => Functor (ProductF f g)
    where
  map = case ProdFunctor l r of MkFunctor mp => mp

public export
ProdApplicative : {0 f, g : Type -> Type} ->
  {funcf : Functor f} -> {funcg : Functor g} ->
  Applicative f -> Applicative g -> Applicative (ProductF f g)
ProdApplicative {funcf} {funcg} applf applg =
  let _ = ProdFunctor funcf funcg in
  MkApplicative
    (\elem => (pure elem, pure elem))
    (\fp, ep => (fst fp <*> fst ep, snd fp <*> snd ep))

public export
[ProdApplicativeI] (funcf : Functor f) => (funcg : Functor g) =>
    (Functor (ProductF f g)) =>
    (l : Applicative f) => (r : Applicative g) =>
    Applicative (ProductF f g) where
  pure = case ProdApplicative {funcf} {funcg} l r of MkApplicative pp _ => pp
  (<*>) = case ProdApplicative {funcf} {funcg} l r of MkApplicative _ ap => ap

public export
ProdMonad : {0 f, g : Type -> Type} ->
  {funcf : Functor f} -> {funcg : Functor g} ->
  {applf : Applicative f} -> {applg : Applicative g} ->
  Monad f -> Monad g -> Monad (ProductF f g)
ProdMonad {f} {g} {funcf} {funcg} {applf} {applg} monf mong =
  let _ = ProdFunctor funcf funcg in
  let _ = ProdApplicative {funcf} {funcg} applf applg in
  MkMonad
    (\ep, fp => (fst ep >>= fst . fp, snd ep >>= snd . fp))
    (\ep => (fst ep >>= fst, snd ep >>= snd))

public export
[ProdMonadI] (funcf : Functor f) => (funcg : Functor g) =>
    (applf : Applicative f) => (applg : Applicative g) =>
    (Functor (ProductF f g)) =>
    (Applicative (ProductF f g)) =>
    (l : Monad f) => (r : Monad g) =>
    Monad (ProductF f g) where
  (>>=) = case ProdMonad {funcf} {funcg} {applf} {applg} l r of
    MkMonad bp _ => bp
  join = case ProdMonad {funcf} {funcg} {applf} {applg} l r of
    MkMonad _ jp => jp

-- The diagonal functor from `Type` to `Type, Type`.
public export
DiagonalF : Type -> (Type, Type)
DiagonalF a = (a, a)

-- The right adjoint to the diagonal functor from the Idris type system
-- (`Type`).
public export
ProductRAdjoint : (Type, Type) -> Type
ProductRAdjoint (t, t') = Pair t t'

public export
ProductMonad : Type -> Type
ProductMonad = ProductRAdjoint . DiagonalF

public export
Functor ProductMonad where
  map = mapHom

public export
Applicative ProductMonad where
  pure ea = (ea, ea)
  (f, g) <*> (ea, ea') = (f ea, g ea')

public export
Monad ProductMonad where
  (ea, ea') >>= f = (fst $ f ea, snd $ f ea')

public export
Foldable ProductMonad where
  foldr op a (x, y) = op x $ op y a

public export
Traversable ProductMonad where
  traverse m (x, y) = map {f} MkPair (m x) <*> m y

public export
applyHom : {0 a, b : Type} -> ProductMonad (a -> b) -> a -> ProductMonad b
applyHom = applyPure {f=ProductMonad}

public export
ProductNTUnit : {0 a : Type} -> a -> ProductMonad a
ProductNTUnit x = (x, x)

-- The right adjoint to the diagonal functor from the category of Idris
-- functors (`Type -> Type`).
public export
ProductAdjunctFCat : ((Type -> Type), (Type -> Type)) -> Type -> Type
ProductAdjunctFCat p = ProductF (fst p) (snd p)

-- L a -> b => a -> R b (`L a` and `b` are in the product category)
-- R f . nu a
public export
prodLeftAdjunct : (a, b, b' : Type) -> (a -> b, a -> b') -> (a -> (b, b'))
prodLeftAdjunct a b b' (f, f') ea = (f ea, f' ea)

-- a -> R b => L a -> b
-- ep b . L g
public export
prodRightAdjunct : (a, b, b' : Type) -> (a -> (b, b')) -> (a -> b, a -> b')
prodRightAdjunct a b b' g = (fst . g, snd . g)

--------------------
---- Coproducts ----
--------------------

-- `CoproductF` is in `[PolyC x PolyC, PolyC]`, and takes two
-- endofunctors to their coproduct.
public export
CoproductF : (Type -> Type) -> (Type -> Type) -> Type -> Type
CoproductF f g a = Either (f a) (g a)

public export
CoproductFComonad : (Type -> Type) -> Type -> Type
CoproductFComonad f = CoproductF f f

public export
(Functor f, Functor g) => Functor (CoproductF f g) where
  map m (Left x) = Left $ map m x
  map m (Right y) = Right $ map m y

-- The left adjoint to the diagonal functor, in the Idris type system.
public export
CoproductLAdjoint : (Type, Type) -> Type
CoproductLAdjoint (t, t') = Either t t'

public export
CoproductComonad : Type -> Type
CoproductComonad = CoproductLAdjoint . DiagonalF

public export
CoproductNTCounit : {a : Type} -> CoproductComonad a -> a
CoproductNTCounit (Left x) = x
CoproductNTCounit (Right x) = x

-- The left adjoint to the diagonal functor from the category of Idris
-- functors (`Type -> Type`).
public export
CoproductAdjunctFCat : ((Type -> Type), (Type -> Type)) -> Type -> Type
CoproductAdjunctFCat p = CoproductF (fst p) (snd p)

public export
CoproductFAlg : (Type -> Type) -> (Type -> Type) -> Type -> Type
CoproductFAlg f g a = (f a -> a, g a -> a)

---------------------------------------
---- Higher-order utility functors ----
---------------------------------------

public export
IdTF : Type -> Type
IdTF = Prelude.Basics.id {a=Type}

public export
Functor IdTF where
  map = id

public export
PairWithF : Type -> Type -> Type
PairWithF a = ProductF (ConstF a) IdTF

public export
ChoiceBetweenF : Type -> Type -> Type
ChoiceBetweenF a = CoproductF (ConstF a) IdTF

public export
MaybeF : Type -> Type
MaybeF = ChoiceBetweenF ()

public export
CoproductFLNE : (Type -> Type) -> List (Type -> Type) -> Type -> Type
CoproductFLNE f [] = f
CoproductFLNE f (f' :: fs) = CoproductF f (CoproductFLNE f' fs)

public export
CoproductFL : List (Type -> Type) -> Type -> Type
CoproductFL [] = InitialComonad
CoproductFL (f :: fs) = CoproductFLNE f fs

--------------------------------------------------------------
---- Slice categories and more on natural transformations ----
--------------------------------------------------------------

public export
SliceO : Type -> Type
SliceO x = (a : Type ** a -> x)

public export
SliceF : (Type -> Type) -> Type -> Type
SliceF f = SliceO . f

public export
NMSliceCar : Type -> Type
NMSliceCar = SliceF ProductMonad

public export
SliceNT : (Type -> Type) -> (Type -> Type) -> Type
SliceNT f g = NaturalTransformation (SliceF f) (SliceF g)

public export
SliceNTToPreComp : (Type -> Type) -> (Type -> Type) -> Type
SliceNTToPreComp f g = SliceNT f (f . g)

public export
FPred : (Type -> Type) -> Type -> Type
FPred f ty = f ty -> Type

public export
FNatTrans : (Type -> Type) -> (Type -> Type) -> Type
FNatTrans f g = NaturalTransformation (FPred f) (FPred g)

public export
FNatTransDep : (Type -> Type) -> (Type -> Type) -> Type
FNatTransDep f g = FNatTrans f (f . g)

public export
MorphCarrier : Type -> Type
MorphCarrier = FPred ProductMonad

public export
MorphFunctor : (Type -> Type) -> Type
MorphFunctor = FNatTransDep ProductMonad

----------------------------------------------------
----------------------------------------------------
---- Equivalence relations using slice functors ----
----------------------------------------------------
----------------------------------------------------

-- The type of proof-relevant relations between two types.
public export
PrRelP : (Type, Type) -> Type
PrRelP = SliceObj . ProductRAdjoint

public export
PrRel : Type -> Type -> Type
PrRel = curry PrRelP

-- The type of proof-relevant (endo-)relations on a type.
public export
PrERel : Type -> Type
PrERel = PrRelP . DiagonalF

-- Equality is a relation.
public export
EqPrRel : {0 a, b : Type} -> PrRel a b
EqPrRel {a} {b} = uncurry $ Equal {a} {b}

-- A type which represents the claim that the images of any pair of elements
-- related in some given way in `(a, a')` under some given morphism from
-- (`a, a'` to `b, b'`) and -- are related in some given way in `(b, b')`.
public export
PrRelPres : {a, a', b, b' : Type} ->
  ((a, a') -> (b, b')) -> PrRel a a' -> PrRel b b' -> Type
PrRelPres {a} {a'} {b} {b'} f ra rb =
  (ea : a) -> (ea' : a') -> ra (ea, ea') -> rb $ f (ea, ea')

-- Like `PrRelPres`, but where we are given separate morphisms from
-- `a -> b` and `a' -> b'` -- in other words, the morphism passed to
-- `PrRelPres` can be factored through two such morphisms with no
-- "cross-dependencies" (between unprimed and primed objects).
public export
PrRelBiPres : {a, a', b, b' : Type} ->
  (a -> b) -> (a' -> b') -> PrRel a a' -> PrRel b b' -> Type
PrRelBiPres {a} {a'} {b} {b'} f f' =
  PrRelPres {a} {a'} {b} {b'} (bimap {f=Pair} f f')

public export
PrERelBiPres : {a, b : Type} ->
  (a -> b) -> (a -> b) -> PrERel a -> PrERel b -> Type
PrERelBiPres {a} {b} = PrRelBiPres {a} {a'=a} {b} {b'=b}

-- This type represents that two morphisms map intensionally equal
-- elements to extensionally equal elements.
public export
PrERelIntExt : {a, b : Type} -> (a -> b) -> (a -> b) -> PrERel b -> Type
PrERelIntExt {a} {b} f g =
  PrRelBiPres {a} {a'=a} {b} {b'=b} f g $ EqPrRel {a} {b=a}

-- A type which represents the claim that the images of any pair of elements
-- related in some given way in `a` under some given morphism from `a` to `b`
-- are related in some given way in `b`.
public export
PrERelPres : {a, b : Type} -> (a -> b) -> PrERel a -> PrERel b -> Type
PrERelPres {a} {b} f = PrERelBiPres {a} {b} f f

-- The statement that `r` implies `r'`.
--
-- Note that if we view a `PrRel` as a presheaf on `Type` with three
-- vertices `a, b, r` and arrows from `a` and `b` to `r` (or the other
-- way around if we view it as a copresheaf), then a `PrRelImp` is a morphism
-- in the category of such presheaves.
public export
PrRelImp : {a, b : Type} -> (r, r' : PrRel a b) -> Type
PrRelImp {a} {b} = PrRelBiPres {a} {a'=b} {b=a} {b'=b} id id

-- The statement that `r` and `r'` imply each other.
public export
PrRelBiImp : {a, b : Type} -> (r, r' : PrRel a b) -> Type
PrRelBiImp r r' = (PrRelImp r r', PrRelImp r' r)

-- An endofunctor on a proof-relevant relation.
public export
PrRelFP : (Type, Type) -> Type
PrRelFP = SliceEndofunctor . ProductRAdjoint

public export
PrRelF : Type -> Type -> Type
PrRelF = curry PrRelFP

-- An endofunctor on a proof-relevant endo-relation.
public export
PrERelF : Type -> Type
PrERelF = PrRelFP . DiagonalF

-- The functor whose algebras are the equivalence relations.
public export
data PrEquivF : {0 a : Type} -> PrERelF a where
  PrErefl : {0 a : Type} -> {0 r : PrERel a} ->
    (ea : a) -> PrEquivF {a} r (ea, ea)
  PrEsym : {0 a : Type} -> {0 r : PrERel a} ->
    (ea, ea' : a) -> r (ea, ea') -> PrEquivF {a} r (ea', ea)
  PrEtrans : {0 a : Type} -> {0 r : PrERel a} ->
    (ea, ea', ea'' : a) -> r (ea', ea'') -> r (ea, ea') ->
    PrEquivF {a} r (ea, ea'')

public export
prEquivMapHom : {0 a, b : Type} -> {0 r : PrERel b} -> {f : a -> b} ->
  (pa : (a, a)) -> PrEquivF {a} (r . mapHom {f=Pair} f) pa ->
  PrEquivF {a=b} r (mapHom {f=Pair} f pa)
prEquivMapHom {a} {b} {r} {f} (ea, ea) (PrErefl ea) =
  PrErefl (f ea)
prEquivMapHom {a} {b} {r} {f} (ea', ea) (PrEsym ea ea' rb) =
  PrEsym (f ea) (f ea') rb
prEquivMapHom {a} {b} {r} {f} (ea, ea'') (PrEtrans ea ea' ea'' rb rb') =
  PrEtrans (f ea) (f ea') (f ea'') rb rb'

public export
prEquivFMap : {0 a : Type} -> SliceFMap {c=(a, a)} {d=(a, a)} (PrEquivF {a})
prEquivFMap r r' m (ea, ea) (PrErefl ea) =
  PrErefl ea
prEquivFMap r r' m (ea, ea') (PrEsym ea' ea rx) =
  PrEsym ea' ea (m (ea', ea) rx)
prEquivFMap r r' m (ea, ea'') (PrEtrans ea ea' ea'' rx rx') =
  PrEtrans ea ea' ea'' (m (ea', ea'') rx) (m (ea, ea') rx')

-- The interface of an equivalence relation.
public export
PrEquivRelI : (a : Type) -> SliceObj (PrERel a)
PrEquivRelI a = SliceAlg (PrEquivF {a})

-- An equivalence relation.
public export
PrEquivRel : Type -> Type
PrEquivRel a = DPair (PrERel a) (PrEquivRelI a)

public export
PrEquivRefl : {a : Type} -> (r : PrEquivRel a) -> (ea : a) -> fst r (ea, ea)
PrEquivRefl {a} r ea = snd r (ea, ea) $ PrErefl ea

public export
PrEquivSym : {a : Type} -> (r : PrEquivRel a) -> {ea, ea' : a} ->
  fst r (ea, ea') -> fst r (ea', ea)
PrEquivSym {a} r {ea} {ea'} = snd r (ea', ea) . PrEsym ea ea'

public export
PrEquivTrans : {a : Type} -> (r : PrEquivRel a) -> {ea, ea', ea'' : a} ->
  fst r (ea', ea'') -> fst r (ea, ea') -> fst r (ea, ea'')
PrEquivTrans {a} r {ea} {ea'} {ea''} = snd r (ea, ea'') .* PrEtrans ea ea' ea''

-- This shows the compatibility of the algebra-defined interface of an
-- equivalence relation with another version using explicit universal
-- quantifiers.
public export
EquivItoIsEquiv : {0 a : Type} ->
  (0 r : PrERel a) -> PrEquivRelI a r -> IsEquivalence (curry r)
EquivItoIsEquiv {a} r eq =
  MkEquivalence
    (\ea => eq (ea, ea) $ PrErefl ea)
    (\rxy => eq (_, _) $ PrEsym _ _ rxy)
    (\rxy, ryz => eq (_, _) $ PrEtrans _ _ _ ryz rxy)

-- Equality is an equivalence relation.
public export
EqPrEquivRelI : (0 a : Type) -> PrEquivRelI a (EqPrRel {a} {b=a})
EqPrEquivRelI a (ea, ea) (PrErefl ea) = Refl
EqPrEquivRelI a (ea', ea) (PrEsym ea ea' eq) = sym eq
EqPrEquivRelI a (ea, ea'') (PrEtrans ea ea' ea'' eq eq') = trans eq' eq

public export
EqPrEquivRel : (0 a : Type) -> PrEquivRel a
EqPrEquivRel a = (EqPrRel {a} {b=a} ** EqPrEquivRelI a)

-- Equality together with first-order extensional equality is a relation.
public export
data ExtEqPrRel : {0 a, b : Type} -> PrRel a b where
  ExtEqEq : {0 a, b : Type} -> {ea : a} -> {eb : b} ->
    EqPrRel {a} {b} (ea, eb) -> ExtEqPrRel {a} {b} (ea, eb)
  ExtEqExtEq : {0 a, b, b' : Type} -> {f : a -> b} -> {f' : a -> b'} ->
    ((ea : a) -> Equal (f ea) (f' ea)) ->
    ExtEqPrRel {a=(a -> b)} {b=(a -> b')} (f, f')

-- Equality together with first-order extensional equality is an equivalence
-- relation.
public export
ExtEqPrEquivRelI : (0 a, b : Type) ->
  PrEquivRelI (a -> b) (ExtEqPrRel {a=(a -> b)} {b=(a -> b)})
ExtEqPrEquivRelI a b (fa, fa) (PrErefl fa) =
  ExtEqEq $ EqPrEquivRelI (a -> b) (fa, fa) (PrErefl fa)
ExtEqPrEquivRelI a b (fa', fa) (PrEsym fa fa' (ExtEqEq eq)) =
  ExtEqExtEq $ \ea => case eq of Refl => Refl
ExtEqPrEquivRelI a b (fa', fa) (PrEsym fa fa' (ExtEqExtEq eq)) =
  ExtEqExtEq $ \ea => sym $ eq ea
ExtEqPrEquivRelI a b (fa, fa'')
  (PrEtrans fa fa' fa'' (ExtEqEq eq) (ExtEqEq eq')) =
    ExtEqExtEq $ \ea => case eq of Refl => case eq' of Refl => Refl
ExtEqPrEquivRelI a b (fa, fa'')
  (PrEtrans fa fa' fa'' (ExtEqEq eq) (ExtEqExtEq eq')) =
    ExtEqExtEq $ \ea => case eq of Refl => eq' ea
ExtEqPrEquivRelI a b (fa, fa'')
  (PrEtrans fa fa' fa'' (ExtEqExtEq eq) (ExtEqEq eq')) =
    ExtEqExtEq $ \ea => case eq' of Refl => eq ea
ExtEqPrEquivRelI a b (fa, fa'')
  (PrEtrans fa fa' fa'' (ExtEqExtEq eq) (ExtEqExtEq eq')) =
    ExtEqExtEq $ \ea => trans (eq' ea) (eq ea)

public export
ExtEqPrEquivRel : (0 a, b : Type) -> PrEquivRel (a -> b)
ExtEqPrEquivRel a b =
  (ExtEqPrRel {a=(a -> b)} {b=(a -> b)} ** ExtEqPrEquivRelI a b)

-- Bi-implication is an equivalence relation on relations.
public export
BiImpEquivRelI : (0 a, b : Type) ->
  PrEquivRelI (PrRel a b) (Prelude.uncurry $ PrRelBiImp {a} {b})
BiImpEquivRelI a b (r, r) (PrErefl r) =
  (\_, _ => id, \_, _ => id)
BiImpEquivRelI a b (r', r) (PrEsym r r' (impl, impr)) =
  (impr, impl)
BiImpEquivRelI a b (r, r'') (PrEtrans r r' r'' (impl, impr) (impl', impr')) =
  (\ea, eb => impl ea eb . impl' ea eb, \ea, eb => impr' ea eb . impr ea eb)

public export
BiImpEquivRel : (a, b : Type) -> PrEquivRel (PrRel a b)
BiImpEquivRel a b = (Prelude.uncurry (PrRelBiImp {a} {b}) ** BiImpEquivRelI a b)

public export
BiImpEquivERelI : (0 a : Type) ->
  PrEquivRelI (PrERel a) (Prelude.uncurry $ PrRelBiImp {a} {b=a})
BiImpEquivERelI a = BiImpEquivRelI a a

public export
BiImpEquivERel : (a : Type) -> PrEquivRel (PrERel a)
BiImpEquivERel a = BiImpEquivRel a a

-- The free (dependent) monad of `PrEquivF`.
public export
FreePrEquivF : {a : Type} -> PrERelF a
FreePrEquivF {a} = SliceFreeM (PrEquivF {a})

-- The free equivalence monad of any relation satisfies the interface of an
-- equivalence relation.
public export
FreePrEquivI : {a : Type} -> (r : PrERel a) ->
  PrEquivRelI a (FreePrEquivF {a} r)
FreePrEquivI {a} r pa =
  InSlFc {f=(PrEquivF {a})} {a=(ProductMonad a)} {sa=r} {ea=pa}

public export
FreePrEquivRel : {a : Type} -> PrERel a -> PrEquivRel a
FreePrEquivRel {a} r = (FreePrEquivF {a} r ** FreePrEquivI {a} r)

public export
FrPrErefl : {a : Type} -> {r : PrERel a} -> (ea : a) -> FreePrEquivF r (ea, ea)
FrPrErefl {a} {r} = PrEquivRefl (FreePrEquivRel r)

public export
FrPrEsym : {a : Type} -> {r : PrERel a} ->
  {ea, ea' : a} -> FreePrEquivF r (ea, ea') -> FreePrEquivF r (ea', ea)
FrPrEsym {a} {r} = PrEquivSym (FreePrEquivRel r)

public export
FrPrEtrans : {a : Type} -> {r : PrERel a} ->
  {ea, ea', ea'' : a} ->
  FreePrEquivF r (ea', ea'') -> FreePrEquivF r (ea, ea') ->
  FreePrEquivF r (ea, ea'')
FrPrEtrans {a} {r} = PrEquivTrans (FreePrEquivRel r)

-- The free equivalence monad has the universal `eval` morphism of a free monad.
public export
freePrEquivEval : {a : Type} -> SliceFreeFEval (PrEquivF {a})
freePrEquivEval {a} sv sa subst alg pa (InSlF pa (InSlV ev)) = subst pa ev
freePrEquivEval {a} sv sa subst alg pa (InSlF pa (InSlC x)) = case x of
  PrErefl ea =>
    alg (ea, ea) (PrErefl ea)
  PrEsym ea ea' r =>
    alg (ea', ea) $ PrEsym ea ea'
      (freePrEquivEval {a} sv sa subst alg (ea, ea') r)
  PrEtrans ea ea' ea'' r r' =>
    alg (ea, ea'') $ PrEtrans ea ea' ea''
      (freePrEquivEval {a} sv sa subst alg (ea', ea'') r)
      (freePrEquivEval {a} sv sa subst alg (ea, ea') r')

public export
freePrEquivBind : {a : Type} -> SliceBind (FreePrEquivF {a})
freePrEquivBind = sliceFreeBindFromEval PrEquivF freePrEquivEval

public export
prEquivBimap : {a, b : Type} -> {rb : PrERel b} ->
  {f, g : a -> b} ->
  PrERelIntExt f g (FreePrEquivF rb) ->
  (pa : (a, a)) -> PrEquivF {a} (FreePrEquivF rb . bimap {f=Pair} f g) pa ->
  FreePrEquivF {a=b} rb (bimap {f=Pair} f g pa)
prEquivBimap {rb} {f} {g} ext (ea, ea) (PrErefl ea) =
  ext ea ea Refl
prEquivBimap {rb} {f} {g} ext (ea', ea) (PrEsym ea ea' rfa) =
  FrPrEtrans (ext ea ea Refl)
  $ FrPrEtrans (FrPrEsym {ea=(f ea)} {ea'=(g ea')} rfa)
  $ ext ea' ea' Refl
prEquivBimap {rb} {f} {g} ext (ea, ea'') (PrEtrans ea ea' ea'' rfa rfa') =
  FrPrEtrans rfa $ FrPrEtrans (FrPrEsym $ ext ea' ea' Refl) rfa'

public export
freeEquivBindBiPres : {a, b : Type} -> {ra : PrERel a} -> {rb : PrERel b} ->
  {f, g : a -> b} ->
  PrERelIntExt f g (FreePrEquivF rb) ->
  PrERelBiPres {a} {b} f g ra (FreePrEquivF rb) ->
  PrERelBiPres {a} {b} f g (FreePrEquivF ra) (FreePrEquivF rb)
freeEquivBindBiPres {a} {b} {ra} {rb} {f} {g} ext pres ea ea' =
  freePrEquivEval ra (FreePrEquivF rb . bimap {f=Pair} f g)
    (\(x1, x2) => pres x1 x2)
    (\px, fgx => prEquivBimap ext px fgx)
    (ea, ea')

-- To show that a morphism respects equivalence relations generated by
-- closing arbitrary relations on its domain and codomain, it suffices to show
-- that it maps directly related elements of the domain to
-- equivalence-closure-related elements of the codomain.
public export
freeEquivBindPres : {a, b : Type} -> {ra : PrERel a} -> {rb : PrERel b} ->
  {f : a -> b} ->
  PrERelPres {a} {b} f ra (FreePrEquivF rb) ->
  PrERelPres {a} {b} f (FreePrEquivF ra) (FreePrEquivF rb)
freeEquivBindPres {a} {b} {ra} {rb} {f} =
  freeEquivBindBiPres {a} {b} {ra} {rb} {f} {g=f} $
    \ea, ea, Refl => FrPrErefl $ f ea

-- If an equivalence-preserving morphism agrees (up to codomain equivalence)
-- with another morphism on _intensionally_ equal elements of the domain, then
-- the two morphisms agree (up to codomain equivalence) on all _equivalent_
-- elements of the domain (i.e. the morphisms are extensionally equal).
public export
PresEqRel : {a, b : Type} ->
  {f, g : a -> b} -> {ra : PrERel a} -> {rb : PrEquivRel b} ->
  PrERelPres {a} {b} g ra (fst rb) ->
  PrERelIntExt f g (fst rb) ->
  PrERelBiPres f g ra (fst rb)
PresEqRel {a} {b} {f} {g} {ra} {rb} gpres bipres ea ea' eqa =
  PrEquivTrans rb (gpres ea ea' eqa) (bipres ea ea Refl)

-- If an equivalence-closure-preserving morphism agrees (up to the equivalence
-- closure of a relation on the codomain) with another morphism on
-- _intensionally_ equal -- elements of the domain, then the two morphisms
-- agree (up to the equivalence closure of the domain relationship) on all
-- _equivalent_ elements of the domain (i.e. the morphisms are extensionally
-- equal).
public export
PresFrEqRel : {a, b : Type} ->
  {f, g : a -> b} -> {ra : PrERel a} -> {rb : PrERel b} ->
  PrERelPres {a} {b} g ra (FreePrEquivF rb) ->
  PrERelIntExt f g (FreePrEquivF rb) ->
  PrERelBiPres f g (FreePrEquivF ra) (FreePrEquivF rb)
PresFrEqRel {a} {b} {f} {g} {ra} {rb} gpres bipres ea ea' eqa =
  FrPrEtrans {r=rb}
    (freeEquivBindPres {a} {b} {ra} {rb} {f=g} gpres ea ea' eqa)
    (bipres ea ea Refl)

--------------------------------------------------
---- Coequalization as (equivalence) relation ----
--------------------------------------------------

public export
0 CoeqRelExtF : {0 x, y : Type} -> (0 f, g : x -> y) -> PrERel x -> PrERel y
CoeqRelExtF {x} {y} f g rx (ey, ey') =
  Exists0 (x, x) $ \(ex, ex') => (rx (ex, ex'), f ex = ey, g ex' = ey')

public export
0 CoeqRelF : {0 x, y : Type} -> (0 f, g : x -> y) -> PrERel x -> PrERelF y
CoeqRelF {x} {y} f g = SliceCoproduct . CoeqRelExtF {x} {y} f g

public export
0 CoeqFreeEquivRelF : {0 x, y : Type} -> (0 f, g : x -> y) -> PrERel x ->
  PrERelF y
CoeqFreeEquivRelF {x} {y} f g rx = FreePrEquivF {a=y} . CoeqRelF {x} {y} f g rx

public export
0 CoeqFreeEquivRelI : {0 x, y : Type} -> (0 f, g : x -> y) ->
  (rx : PrERel x) -> (ry : PrERel y) ->
  PrEquivRelI y (CoeqFreeEquivRelF {x} {y} f g rx ry)
CoeqFreeEquivRelI {x} {y} f g rx ry =
  FreePrEquivI {a=y} (CoeqRelF {x} {y} f g rx ry)

---------------------------------------------
---- Closures of some universal relations ----
---------------------------------------------

public export
EmptyRel : (t : Type) -> RelationOn t
EmptyRel t el el' = Void

public export
VoidRel : RelationOn Void
VoidRel v _ = void v

public export
FullRel : (t : Type) -> RelationOn t
FullRel t el el' = ()

public export
UnitRel : RelationOn Unit
UnitRel = FullRel ()

public export
0 ClosureOfEmptyRelImpliesEq : (0 a : Type) ->
  PrRelImp (FreePrEquivF $ uncurry $ EmptyRel a) (EqPrRel {a} {b=a})
ClosureOfEmptyRelImpliesEq a ea ea' =
  freePrEquivEval {a} (uncurry $ EmptyRel a) (\(x, y) => x = y)
    (\(ea, ea'), v => void v)
    (\(ea, ea'), eqa => case eqa of
      PrErefl _ => Refl
      PrEsym _ _ Refl => Refl
      PrEtrans _ _ _ Refl Refl => Refl)
    (ea, ea')

public export
0 EqImpliesClosureOfEmptyRel : (0 a : Type) ->
  PrRelImp (EqPrRel {a} {b=a}) (FreePrEquivF $ uncurry $ EmptyRel a)
EqImpliesClosureOfEmptyRel a ea _ Refl = FrPrErefl ea

public export
0 ClosureOfEmptyRelIsEq : (0 a : Type) ->
  PrRelBiImp (FreePrEquivF $ uncurry $ EmptyRel a) (EqPrRel {a} {b=a})
ClosureOfEmptyRelIsEq a =
  (ClosureOfEmptyRelImpliesEq a, EqImpliesClosureOfEmptyRel a)

public export
0 ClosureOfEqRelImpliesEq : (0 a : Type) ->
  PrRelImp (FreePrEquivF $ EqPrRel {a} {b=a}) (EqPrRel {a} {b=a})
ClosureOfEqRelImpliesEq a ea ea' =
  freePrEquivEval {a} (EqPrRel {a} {b=a}) (\(x, y) => x = y)
    (\(ea, ea'), Refl => Refl)
    (\(ea, ea'), eqa => case eqa of
      PrErefl _ => Refl
      PrEsym _ _ Refl => Refl
      PrEtrans _ _ _ Refl Refl => Refl)
    (ea, ea')

public export
0 EqImpliesClosureOfEqRel : (0 a : Type) ->
  PrRelImp (EqPrRel {a} {b=a}) (FreePrEquivF $ EqPrRel {a} {b=a})
EqImpliesClosureOfEqRel a ea _ Refl = FrPrErefl ea

public export
0 ClosureOfEqRelIsEq : (0 a : Type) ->
  PrRelBiImp (FreePrEquivF $ EqPrRel {a} {b=a}) (EqPrRel {a} {b=a})
ClosureOfEqRelIsEq a =
  (ClosureOfEqRelImpliesEq a, EqImpliesClosureOfEqRel a)

-----------------------
-----------------------
---- Refined types ----
-----------------------
-----------------------

public export
DecPred : Type -> Type
DecPred a = a -> Bool

public export
TruePred : (a : Type) -> DecPred a
TruePred a = const True

public export
FalsePred : (a : Type) -> DecPred a
FalsePred a = const False

public export
NotPred : {0 a : Type} -> DecPred a -> DecPred a
NotPred pred = not . pred

public export
AndPred : {0 a : Type} -> DecPred a -> DecPred a -> DecPred a
AndPred p q = \x => p x && q x

public export
OrPred : {0 a : Type} -> DecPred a -> DecPred a -> DecPred a
OrPred p q = \x => p x || q x

public export
ImpliesPred : {0 a : Type} -> DecPred a -> DecPred a -> DecPred a
ImpliesPred p q = \x => not (p x) || q x

public export
AndNotPred : {0 a : Type} -> DecPred a -> DecPred a -> DecPred a
AndNotPred p q = \x => p x && not (q x)

public export
Satisfies : {0 a : Type} -> DecPred a -> a -> Type
Satisfies p x = p x = True

public export
Refinement : {a : Type} -> (0 pred : DecPred a) -> Type
Refinement {a} p = Equalizer {a} {b=Bool} p (const True)

public export
refinementFstEq : {0 a : Type} -> {0 pred : DecPred a} ->
  {r, r' : Refinement pred} -> fst0 r = fst0 r' -> r = r'
refinementFstEq {r=(Element0 _ s)} {r'=(Element0 _ s')} Refl =
  rewrite uip {eq=s} {eq'=s'} in Refl

public export
TrueRefinement : Type -> Type
TrueRefinement a = Refinement (TruePred a)

public export
FalseRefinement : Type -> Type
FalseRefinement a = Refinement (FalsePred a)

public export
NotRefinement : {a : Type} -> DecPred a -> Type
NotRefinement p = Refinement (NotPred p)

public export
AndRefinement : {a : Type} -> DecPred a -> DecPred a -> Type
AndRefinement p q = Refinement (AndPred p q)

public export
OrRefinement : {a : Type} -> DecPred a -> DecPred a -> Type
OrRefinement p q = Refinement (OrPred p q)

public export
ImpliesRefinement : {a : Type} -> DecPred a -> DecPred a -> Type
ImpliesRefinement p q = Refinement (ImpliesPred p q)

public export
AndNotRefinement : {a : Type} -> DecPred a -> DecPred a -> Type
AndNotRefinement p q = Refinement (AndNotPred p q)

public export
MkRefinement : {0 a : Type} -> {0 p : DecPred a} ->
  (x : a) -> {auto 0 satisfies : Satisfies p x} ->
  Refinement {a} p
MkRefinement x {satisfies} = Element0 x satisfies

public export
shape : {0 a : Type} -> {0 p : DecPred a} -> Refinement {a} p -> a
shape = fst0

public export
VoidRefinement : DecPred Void
VoidRefinement = voidF Bool

public export
Refined : Type
Refined = Subset0 Type DecPred

public export
ErasedType : Refined -> Type
ErasedType = fst0

public export
0 RefinedPred : (r : Refined) -> DecPred (ErasedType r)
RefinedPred = snd0

public export
RefinedType : Refined -> Type
RefinedType r = Refinement {a=(ErasedType r)} (RefinedPred r)

public export
RefinedSlice : Refined -> Type
RefinedSlice a = RefinedType a -> Refined

public export
RefinedSliceFunctor : Refined -> Refined -> Type
RefinedSliceFunctor a b = RefinedSlice a -> RefinedSlice b

public export
RefinedSliceFunctorType : Refined -> Refined -> Type
RefinedSliceFunctorType a b = SliceFunctor (RefinedType a) (RefinedType b)

public export
RefinedSliceMorphism : {a : Refined} -> RefinedSlice a -> RefinedSlice a -> Type
RefinedSliceMorphism {a} s s' =
  SliceMorphism {a=(RefinedType a)} (RefinedType . s) (RefinedType . s')

public export
RefinedDPair : {a : Refined} -> RefinedSlice a -> Type
RefinedDPair {a} p = Sigma {a=(RefinedType a)} (RefinedType . p)

public export
ErasedDPair : {a : Refined} -> RefinedSlice a -> Type
ErasedDPair {a} p = Sigma {a=(RefinedType a)} (ErasedType . p)

public export
0 ErasedPred : {a : Refined} ->
  (p : RefinedSlice a) -> ErasedDPair {a} p -> Bool
ErasedPred {a} p dp = RefinedPred (p (fst dp)) (snd dp)

public export
RefinedSigma : {a : Refined} -> RefinedSlice a -> Refined
RefinedSigma {a} p = Element0 (ErasedDPair {a} p) (ErasedPred {a} p)

public export
RefinedSigmaType : {a : Refined} -> RefinedSlice a -> Type
RefinedSigmaType {a} p = RefinedType (RefinedSigma {a} p)

public export
RefinedDPairToSigma : {a : Refined} -> {p : RefinedSlice a} ->
  RefinedDPair {a} p -> RefinedSigmaType {a} p
RefinedDPairToSigma r = Element0 (fst r ** fst0 (snd r)) (snd0 (snd r))

public export
RefinedSigmaToDPair : {a : Refined} -> {p : RefinedSlice a} ->
  RefinedSigmaType {a} p -> RefinedDPair {a} p
RefinedSigmaToDPair r = (fst (fst0 r) ** Element0 (snd (fst0 r)) (snd0 r))

public export
RefinedPi : {a : Refined} -> RefinedSlice a -> Type
RefinedPi {a} p = Pi {a=(RefinedType a)} (RefinedType . p)

public export
DecSlice : {a : Type} -> SliceObj a -> Type
DecSlice {a} = Pi {a} . (.) Dec

public export
0 SliceInhabited : {0 a : Type} -> {0 sl : SliceObj a} ->
  DecSlice {a} sl -> SliceObj a
SliceInhabited {a} {sl} p x = IsYesTrue {a=(sl x)} $ p x

public export
0 SliceDecPred : {0 a : Type} -> {0 sl : SliceObj a} ->
  DecSlice {a} sl -> DecPred a
SliceDecPred {a} {sl} p x = isYes {a=(sl x)} $ p x

-- A decidable predicate on `a` -- that is, a predicate on `a` together with
-- a decision procedure for that predicate for any term of `a`.
public export
DecProp : Type -> Type
DecProp a = Subset0 (SliceObj a) (DecSlice {a})

public export
0 PropHolds : {0 a : Type} -> DecProp a -> SliceObj a
PropHolds {a} p = SliceInhabited {a} {sl=(fst0 p)} (snd0 p)

public export
RefinementP : {a : Type} -> (0 p : DecProp a) -> Type
RefinementP {a} p = Subset0 a (PropHolds {a} p)

public export
0 DecPropToPred : {0 a : Type} -> DecProp a -> DecPred a
DecPropToPred {a} p = SliceDecPred {a} {sl=(fst0 p)} (snd0 p)

public export
0 RefinementPIsRefinement : {0 a : Type} -> {0 sl : SliceObj a} ->
  (0 p : DecSlice {a} sl) ->
  RefinementP {a} (Element0 sl p) = Refinement {a} (SliceDecPred p)
RefinementPIsRefinement {a} p = Refl

public export
0 RefinementPIsRefinementP : {0 a : Type} -> (0 p : DecProp a) ->
  RefinementP {a} p = Refinement {a} (DecPropToPred p)
RefinementPIsRefinementP {a} p = Refl

public export
0 DecPredToProp : {0 a : Type} -> DecPred a -> DecProp a
DecPredToProp {a} p =
  Element0 (Satisfies {a} p) $ \x => decEq {t=Bool} (p x) True

public export
RefinementAsRefinementP : {0 a : Type} -> (0 p : DecPred a) ->
  Refinement {a} p -> RefinementP {a} (DecPredToProp p)
RefinementAsRefinementP {a} p x = Element0 (fst0 x) $ rewrite snd0 x in Refl

public export
RARPpresFst : {0 a : Type} -> {0 p : DecPred a} ->
  (0 x : Refinement {a} p) ->
  fst0 (RefinementAsRefinementP {a} p x) = fst0 x
RARPpresFst {a} {p} x = Refl

public export
RefinementPAsRefinement : {0 a : Type} -> (p : DecPred a) ->
  RefinementP {a} (DecPredToProp p) -> Refinement {a} p
RefinementPAsRefinement {a} p x = Element0 (fst0 x) (fromIsYes $ snd0 x)

public export
RPARpresFst : {0 a : Type} -> {p : DecPred a} ->
  (x : RefinementP {a} $ DecPredToProp p) ->
  fst0 (RefinementPAsRefinement {a} p x) = fst0 x
RPARpresFst {a} {p} x = Refl

--------------------------
---- Refined functors ----
--------------------------

public export
DecPredF : (Type -> Type) -> Type
DecPredF f = NaturalTransformation DecPred (DecPred . f)

public export
RefinedF : {f : Type -> Type} -> DecPredF f -> Refined -> Refined
RefinedF {f} pf (Element0 a pred) = Element0 (f a) (pf a pred)

----------------------------------
---- Bicomplete refined types ----
----------------------------------

public export
DecPredPair : Type -> Type
DecPredPair = ProductMonad . DecPred

public export
CoeqPred : Type -> Type
CoeqPred = DecPredPair

public export
0 coeqBase : {0 a : Type} -> (0 pred : CoeqPred a) -> DecPred a
coeqBase (pred, _) = pred

public export
0 coeqNormalized : {0 a : Type} -> (0 pred : CoeqPred a) -> DecPred a
coeqNormalized (_, norm) = norm

public export
CoeqPredF : (Type -> Type) -> Type
CoeqPredF f = (DecPredF f, DecPredF f)

public export
0 coeqFBase : {0 f : Type -> Type} -> (0 pred : CoeqPredF f) -> DecPredF f
coeqFBase (pred, _) = pred

public export
0 coeqFNormalized : {0 f : Type -> Type} -> (0 pred : CoeqPredF f) -> DecPredF f
coeqFNormalized (_, norm) = norm

public export
coeqPredF : {0 f : Type -> Type} -> {x : Type} ->
  CoeqPredF f -> CoeqPred x -> CoeqPred (f x)
coeqPredF {f} {x} (predf, normf) (pred, norm) = (predf x pred, normf x norm)

public export
0 normalized : {0 a : Type} -> (0 pred : CoeqPred a) -> DecPred a
normalized (pred, norm) = AndPred pred norm

public export
Normalized : {a : Type} -> (0 pred : CoeqPred a) -> Type
Normalized pred = Refinement (normalized pred)

public export
0 nonNormalized : {0 a : Type} -> (0 pred : CoeqPred a) -> DecPred a
nonNormalized (pred, norm) = AndNotPred pred norm

public export
NonNormalized : {a : Type} -> (0 pred : CoeqPred a) -> Type
NonNormalized pred = Refinement (nonNormalized pred)

public export
Normalizer : {a : Type} -> (0 pred : CoeqPred a) -> Type
Normalizer pred = NonNormalized pred -> Normalized pred

public export
Coequalizable : Type
Coequalizable = Subset0 Type CoeqPred

public export
coRefBase : Coequalizable -> Type
coRefBase (Element0 a _) = a

public export
0 coRefPred : (cr : Coequalizable) -> CoeqPred (coRefBase cr)
coRefPred (Element0 _ p) = p

public export
CoeqNormalizer : Coequalizable -> Type
CoeqNormalizer cr = Normalizer (coRefPred cr)

public export
Coequalized : Type
Coequalized = DPair Coequalizable CoeqNormalizer

public export
normalizedCompose :
  {0 a, b, c : Type} ->
  {pred : CoeqPred b} ->
  {fn : Normalizer pred} ->
  (g : Normalized {a=b} pred -> c) ->
  (f : a -> Refinement {a=b} (coeqBase pred)) ->
  a -> c
normalizedCompose {pred=(_, norm)} {fn} g f x = g $ case f x of
  Element0 x' satisfies => case decEq (norm x') True of
    Yes normalized => Element0 x' $ rewrite satisfies in normalized
    No nonNormalized => fn $ Element0 x' $
      rewrite satisfies in rewrite notTrueIsFalse nonNormalized in Refl

public export
coeqInject : {0 a : Type} -> {0 pred : CoeqPred b} ->
  Refinement (normalized pred) -> Refinement (coeqBase pred)
coeqInject {a} {pred=(pred, _)} (Element0 e n) = (Element0 e $ andLeft n)

public export
coeqForgetfulCompose :
  {0 a, b, c : Type} ->
  {pred : CoeqPred b} ->
  {fn : Normalizer pred} ->
  (g : Refinement {a=b} (coeqBase pred) -> c) ->
  (f : a -> Normalized {a=b} pred) ->
  a -> c
coeqForgetfulCompose g f = g . coeqInject {a=b} {pred} . f

public export
CoequalizableF : {f : Type -> Type} -> (0 _ : CoeqPredF f) ->
  Coequalizable -> Coequalizable
CoequalizableF {f} predf (Element0 x pred) =
  (Element0 (f x) $ coeqPredF {f} {x} predf pred)

public export
NormalizerF : {f : Type -> Type} -> (0 predf : CoeqPredF f) -> Type
NormalizerF predf = (a : Coequalizable) ->
  CoeqNormalizer a -> CoeqNormalizer (CoequalizableF {f} predf a)

public export
CoequalizedF :
  {f : Type -> Type} ->
  {predf : CoeqPredF f} ->
  (normalizerf : NormalizerF {f} predf) ->
  Coequalized -> Coequalized
CoequalizedF {f} {predf} normalizerf (a ** fn) =
  (CoequalizableF {f} predf a ** normalizerf a fn)

--------------------------------------
---- Algebras of refined functors ----
--------------------------------------

public export
0 PreservesRefinement : {a, b : Type} ->
  (0 pa : DecPred a) -> (0 pb : DecPred b) -> (a -> b) -> Type
PreservesRefinement {a} {b} pa pb m =
  (e : a) -> (0 satisfies : Satisfies pa e) -> Satisfies pb (m e)

public export
RefinedMorphism : Refined -> Refined -> Type
RefinedMorphism (Element0 a pa) (Element0 b pb) =
  Subset0 (a -> b) (PreservesRefinement pa pb)

public export
0 IsRefinedFunctor :
  {0 f : Type -> Type} -> {0 isF : Functor f} -> (0 pf : DecPredF f) -> Type
IsRefinedFunctor {f} {isF} pf =
  (0 a, b : Type) -> (0 pa : DecPred a) -> (0 pb : DecPred b) ->
  (0 m : a -> b) -> (0 _ : PreservesRefinement pa pb m) ->
  PreservesRefinement (pf a pa) (pf b pb) (map {f} m)

public export
RefinedFMap : {0 f : Type -> Type} -> {isF : Functor f} ->
  (0 pf : DecPredF f) ->
  {auto 0 isRF : IsRefinedFunctor {f} {isF} pf} ->
  {0 a, b : Refined} ->
  RefinedMorphism a b ->
  RefinedMorphism (RefinedF pf a) (RefinedF pf b)
RefinedFMap
  {f} {isF} {isRF} pf {a=(Element0 a pa)} {b=(Element0 b pb)} (Element0 m pr) =
    (Element0 (map {f} m) $ isRF a b pa pb m pr)

public export
RefinedAlg : {f : Type -> Type} -> DecPredF f -> Refined -> Type
RefinedAlg {f} pf x = RefinedMorphism (RefinedF pf x) x

public export
RefinedCoalg : {f : Type -> Type} -> DecPredF f -> Refined -> Type
RefinedCoalg {f} pf x = RefinedMorphism x (RefinedF pf x)

public export
CoequalizableMorphism : Coequalizable -> Coequalizable -> Type
CoequalizableMorphism (Element0 a apred) (Element0 b bpred) =
  Subset0 (a -> b) (PreservesRefinement (coeqNormalized apred) (coeqBase bpred))

public export
CoequalizedMorphism : Coequalized -> Coequalized -> Type
CoequalizedMorphism (a ** _) (b ** _) = CoequalizableMorphism a b

public export
0 PreservesCoeqPred : {a, b : Type} ->
  (0 pa : CoeqPred a) -> (0 pb : CoeqPred b) ->
  (a -> b) -> Type
PreservesCoeqPred pa pb = PreservesRefinement (coeqNormalized pa) (coeqBase pb)

public export
0 PreservesNormalization : {a : Type} ->
  (0 pa : CoeqPred a) -> (a -> a) -> Type
PreservesNormalization {a} pa =
  PreservesRefinement (coeqNormalized pa) (coeqNormalized pa)

public export
0 IsCoequalizedFunctor :
  {0 f : Type -> Type} -> {0 isF : Functor f} ->
  (0 predf : CoeqPredF f) -> Type
IsCoequalizedFunctor {f} {isF} predf =
  ((0 a, b : Type) -> (0 pa : CoeqPred a) -> (0 pb : CoeqPred b) ->
   (0 m : a -> b) -> (0 _ : PreservesCoeqPred pa pb m) ->
    PreservesCoeqPred (coeqPredF predf pa) (coeqPredF predf pb) (map {f} m),
   (0 a : Type) -> (0 pa : CoeqPred a) ->
   (0 m : a -> a) -> (0 _ : PreservesNormalization pa m) ->
    PreservesNormalization (coeqPredF predf pa) (map {f} m))

public export
CoequalizableFMap : {0 f : Type -> Type} ->
  {auto isF : Functor f} ->
  (0 predf : CoeqPredF f) ->
  {auto 0 isCF : IsCoequalizedFunctor {f} {isF} predf} ->
  {0 a, b : Coequalizable} ->
  CoeqNormalizer a ->
  CoequalizableMorphism a b ->
  CoequalizableMorphism (CoequalizableF predf a) (CoequalizableF predf b)
CoequalizableFMap
  {f} {isF} {isCF} predf {a=(Element0 a pa)} {b=(Element0 b pb)} fn m =
    (Element0 (map {f} (fst0 m)) $ fst isCF a b pa pb (fst0 m) (snd0 m))

public export
CoequalizedFMap : {0 f : Type -> Type} ->
  {auto isF : Functor f} ->
  {0 predf : CoeqPredF f} ->
  {auto 0 isCF : IsCoequalizedFunctor {f} {isF} predf} ->
  (nf : NormalizerF predf) ->
  {a, b : Coequalized} ->
  CoequalizedMorphism a b ->
  CoequalizedMorphism (CoequalizedF {predf} nf a) (CoequalizedF {predf} nf b)
CoequalizedFMap
  {f} {isF} {isCF} {predf} nf {a=(a ** na)} {b=(b ** nb)} =
    CoequalizableFMap {f} {isF} predf {isCF} {a} {b} na

public export
CoeqAlg : {f : Type -> Type} -> {pf : CoeqPredF f} ->
  NormalizerF pf -> Coequalized -> Type
CoeqAlg nf x = CoequalizedMorphism (CoequalizedF nf x) x

public export
CoeqCoalg : {f : Type -> Type} -> {pf : CoeqPredF f} ->
  NormalizerF pf -> Coequalized -> Type
CoeqCoalg nf x = CoequalizedMorphism x (CoequalizedF nf x)

---------------------------------------------
---------------------------------------------
---- Refined polynomial (slice) functors ----
---------------------------------------------
---------------------------------------------

-- The dependent product functor induced by the given subtype family.
-- Right adjoint to the base change functor.
public export
RefinedProdF : {a, b : Type} -> (b -> DecPred a) -> SliceFunctor a b
RefinedProdF {a} {b} pred sla elemb =
  Pi {a=(Refinement {a} (pred elemb))} (BaseChangeF shape sla)

-- The dependent product functor induced by the given subtype family.
-- Left adjoint to the base change functor.
public export
RefinedCoprodF : {a, b : Type} -> (b -> DecPred a) -> SliceFunctor a b
RefinedCoprodF {a} {b} pred sla elemb =
  Sigma {a=(Refinement {a} (pred elemb))} (BaseChangeF shape sla)

-- A dependent polynomial functor can be defined as a composition of
-- a base change followed by a dependent product followed by a dependent
-- coproduct.
public export
RefinedPolyF : {w, x, y, z : Type} ->
  (x -> w) -> (y -> DecPred x) -> (z -> DecPred y) -> SliceFunctor w z
RefinedPolyF {w} {x} {y} {z} fxw predyx predzy =
  RefinedCoprodF {a=y} {b=z} predzy
  . RefinedProdF {a=x} {b=y} predyx
  . BaseChangeF fxw

public export
0 RefinedPolyFPred : {w, x, y, z : Type} ->
  (fxw : x -> w) -> (predyx : y -> DecPred x) -> (predzy : z -> DecPred y) ->
  (p : SliceObj w) -> (q : SliceObj z) -> (f : w -> z) -> DecPred z
RefinedPolyFPred {w} {x} {y} {z} fxw predyx predzy p q f ez =
  ?RefinedPolyFPred_hole

public export
RefinedPolyFSignature : {w, x, y, z : Type} ->
  (fxw : x -> w) -> (predyx : y -> DecPred x) -> (predzy : z -> DecPred y) ->
  (p : SliceObj w) -> (q : SliceObj z) -> (f : w -> z) -> Type
RefinedPolyFSignature {w} {x} {y} {z} fxw predyx predzy p q f =
  Refinement {a=z} $ RefinedPolyFPred {w} {x} {y} {z} fxw predyx predzy p q f

public export
0 SigmaSigmaRefinedPolyF : {w, x, y, z : Type} ->
  (fxw : x -> w) -> (predyx : y -> DecPred x) -> (predzy : z -> DecPred y) ->
  (p : SliceObj w) -> (q : SliceObj z) -> (f : w -> z) ->
  Sigma p -> Sigma (q . f)
SigmaSigmaRefinedPolyF {w} {x} {y} {z} fxw predyx predzy p q f (ew ** ep) =
  (?SigmaSigmaRefinedPolyF_hole_ew **
   ?SigmaSigmaRefinedPolyF_hole_eq)

public export
0 SigmaPiRefinedPolyF : {w, x, y, z : Type} ->
  (fxw : x -> w) -> (predyx : y -> DecPred x) -> (predzy : z -> DecPred y) ->
  (p : SliceObj w) -> (q : SliceObj z) -> (f : w -> z) ->
  Sigma p -> Pi (q . f)
SigmaPiRefinedPolyF {w} {x} {y} {z} fxw predyx predzy p q f (ew ** ep) ew' =
  ?SigmaPiRefinedPolyF_hole_eq

public export
0 PiSigmaRefinedPolyF : {w, x, y, z : Type} ->
  (fxw : x -> w) -> (predyx : y -> DecPred x) -> (predzy : z -> DecPred y) ->
  (p : SliceObj w) -> (q : SliceObj z) -> (f : w -> z) ->
  Pi p -> Sigma (q . f)
PiSigmaRefinedPolyF {w} {x} {y} {z} fxw predyx predzy p q f pip =
  (?PiSigmaRefinedPolyF_hole_ew **
   ?PiSigmaRefinedPolyF_hole_eq)

public export
0 PiPiRefinedPolyF : {w, x, y, z : Type} ->
  (fxw : x -> w) -> (predyx : y -> DecPred x) -> (predzy : z -> DecPred y) ->
  (p : SliceObj w) -> (q : SliceObj z) -> (f : w -> z) ->
  Pi p -> Pi (q . f)
PiPiRefinedPolyF {w} {x} {y} {z} fxw predyx predzy p q f pip ew =
  ?PiPiRefinedPolyF_hole_eq

--------------------------------------------------
--------------------------------------------------
---- Natural number induction and coinduction ----
--------------------------------------------------
--------------------------------------------------

-------------------------------------------------------
---- Dependent (slice) category of natural numbers ----
-------------------------------------------------------

public export
NatSliceObj : Type
NatSliceObj = SliceObj Nat

public export
NatPi : NatSliceObj -> Type
NatPi = Pi {a=Nat}

public export
NatSigma : NatSliceObj -> Type
NatSigma = Sigma {a=Nat}

public export
NatSliceMorphism : NatSliceObj -> NatSliceObj -> Type
NatSliceMorphism = SliceMorphism {a=Nat}

public export
NatSliceFMorphism : NatSliceObj -> (Nat -> Nat) -> Type
NatSliceFMorphism = SliceFMorphism {a=Nat}

public export
NatDepAlgebra : NatSliceObj -> Type
NatDepAlgebra p = (p Z, NatSliceFMorphism p S)

public export
natNonTailRecursiveIter : {0 p : Nat -> Type} ->
  NatSliceFMorphism p S -> (n, i : Nat) -> p i -> p (n + i)
natNonTailRecursiveIter {p} op Z i acc = acc
natNonTailRecursiveIter {p} op (S n) i acc =
  op (n + i) $ natNonTailRecursiveIter op n i acc

public export
natNonTailRecursiveCata : {0 p : NatSliceObj} ->
  NatDepAlgebra p -> NatPi p
natNonTailRecursiveCata (z, s) n = replace {p} (plusZeroRightNeutral n) $
  natNonTailRecursiveIter {p} s n 0 z

public export
natDepFoldIdx : {0 p : Nat -> Type} ->
  NatSliceFMorphism p S -> (n, i : Nat) -> p i -> p (n + i)
natDepFoldIdx op Z i acc = acc
natDepFoldIdx op (S n) i acc = replace {p} (sym (plusSuccRightSucc n i)) $
  natDepFoldIdx op n (S i) (op i acc)

public export
natDepCata : {0 p : NatSliceObj} ->
  NatDepAlgebra p -> NatPi p
natDepCata (z, s) n = replace {p} (plusZeroRightNeutral n) $
  natDepFoldIdx s n 0 z

public export
natDepCataZ : {0 p : NatSliceObj} ->
  {0 alg : NatDepAlgebra p} ->
  natDepCata {p} alg Z = fst alg
natDepCataZ {p} {alg=(_, _)} = Refl

public export
NatDepCoalgebra : NatSliceObj -> Type
NatDepCoalgebra p = NatSliceMorphism p (Maybe . p . S)

public export
natDepAna : {0 p : NatSliceObj} ->
  NatDepCoalgebra p -> NatSigma p -> Inf (Maybe (NatSigma p))
natDepAna coalg (n ** x) with (coalg n x)
  natDepAna coalg (n ** x) | Nothing = Nothing
  natDepAna coalg (n ** x) | Just x' = Delay (natDepAna coalg (S n ** x'))

public export
NatDepGenAlgebra : NatSliceObj -> Type
NatDepGenAlgebra p =
  (p Z, (n : Nat) -> ((m : Nat) -> LTE m n -> p m) -> p (S n))

public export
natDepGenIndStrengthened : {0 p : NatSliceObj} ->
  NatDepGenAlgebra p ->
  (x : Nat) -> (y : Nat) -> LTE y x -> p y
natDepGenIndStrengthened {p} (p0, pS) =
  natDepCata
    {p=(\x => (y : Nat) -> LTE y x -> p y)}
    (\n, lte => replace {p} (lteZeroIsZero lte) p0,
     \n, hyp, y, lteySn => case lteSuccEitherEqLte lteySn of
      Left eq => replace {p} (sym eq) $ pS n hyp
      Right lteyn => hyp y lteyn)

public export
natDepGenInd : {0 p : NatSliceObj} ->
  NatDepGenAlgebra p ->
  NatPi p
natDepGenInd alg k = natDepGenIndStrengthened alg k k reflexive

-----------------------
---- Non-dependent ----
-----------------------

public export
NatAlgebra : Type -> Type
NatAlgebra a = (a, Nat -> a -> a)

public export
natCata : {0 a : Type} -> NatAlgebra a -> Nat -> a
natCata = natDepCata {p=(const a)}

public export
NatCoalgebra : Type -> Type
NatCoalgebra a = Nat -> a -> Maybe a

public export
natAna : {0 a : Type} -> NatCoalgebra a -> (Nat, a) -> Inf (Maybe (Nat, a))
natAna coalg nx =
  map {f=Maybe} SigmaToPair $ natDepAna {p=(const a)} coalg $ PairToSigma nx

public export
NatGenAlgebra : Type -> Type
NatGenAlgebra a = (a, (n : Nat) -> ((m : Nat) -> LTE m n -> a) -> a)

public export
natGenInd : {0 a : Type} -> NatGenAlgebra a -> Nat -> a
natGenInd = natDepGenInd {p=(const a)}

--------------------------------------
--------------------------------------
---- Categorial algebra on `Type` ----
--------------------------------------
--------------------------------------

-- The categorial definition of an F-algebra.
public export
Algebra : (Type -> Type) -> Type -> Type
Algebra f a = f a -> a

-- The objects of the category formed by the F-algebras of a given functor.
public export
FAlgObj : (Type -> Type) -> Type
FAlgObj f = DPair Type (Algebra f)

public export
FAlgCommutes : {f : Type -> Type} ->
  {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  (g, h : FAlgObj f) -> (fst g -> fst h) -> Type
FAlgCommutes {f} {fm} (a ** g) (b ** h) j = ExtEq (j . g) (h . fm j)

-- The morphisms of the category formed by the F-algebras of a given functor.
public export
FAlgMorph : {f : Type -> Type} ->
  {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  (g, h : FAlgObj f) -> Type
FAlgMorph {f} {fm} g h = Subset0 (fst g -> fst h) (FAlgCommutes {f} {fm} g h)

-- Objects of the category of F-algebras for a given functor may also
-- be viewed as interfaces.
public export
FIFace : (Type -> Type) -> Type
FIFace = FAlgObj

-- Morphisms of the category of F-algebras for a given functor may be
-- viewed as implementations of an interface in terms of another.
public export
FIFaceMorph :
  {f : Type -> Type} ->
  {fm : {0 x, y : Type} -> (x -> y) -> f x -> f y} ->
  FIFace f -> FIFace f -> Type
FIFaceMorph {fm} = FAlgMorph {fm}

public export
Contravariant f => Functor (Algebra f) where
  map m alg = m . alg . contramap {f} m

-- The dual of an F-algebra: an F-coalgebra.
public export
Coalgebra : (Type -> Type) -> Type -> Type
Coalgebra f a = a -> f a

public export
Contravariant f => Contravariant (Coalgebra f) where
  contramap m coalg = contramap {f} m . coalg . m

-- A proalgebra of a pair of functors is a type together with a coalgebra
-- of one and an algebra of the other.
public export
ProAlgebra : (Type -> Type) -> (Type -> Type) -> Type -> Type
ProAlgebra f g a = (Algebra f a, Coalgebra g a)

public export
EndoProAlgebra : (Type -> Type) -> Type -> Type
EndoProAlgebra f = ProAlgebra f f

-- A dialgebra of a pair of functors is a type together with a morphism
-- between applications of the functor to it.
public export
Dialgebra : (Type -> Type) -> (Type -> Type) -> Type -> Type
Dialgebra f g a = f a -> g a

public export
EndoDialgebra : (Type -> Type) -> Type -> Type
EndoDialgebra f = Dialgebra f f

public export
(Contravariant f, Functor g) => Functor (Dialgebra f g) where
  map {f} {g} {a} {b} m alg = map {f=g} m . alg . contramap {f} m

-- We can always derive a dialgebra from a proalgebra, simply by composition.
-- We may not be able to go the other direction, however, so a proalgebra is
-- in that sense more powerful.  By the same token, the _notion_ of proalgebra
-- is in a sense less general -- there are strictly fewer proalgebras than
-- dialgebras.
public export
ProToDiAlg : {0 f, g : Type -> Type} -> {0 a : Type} ->
  ProAlgebra f g a -> Dialgebra f g a
ProToDiAlg {f} {g} {a} (alg, coalg) = coalg . alg

public export
EndoProToDiAlg : {0 f : Type -> Type} -> {0 a : Type} ->
  EndoProAlgebra f a -> EndoDialgebra f a
EndoProToDiAlg {f} = ProToDiAlg {f} {g=f}

-- For a given functor `F` and object `v`, form the functor `Fv` defined by
-- `Fv[x] = v + F[x]`.  We call it `TranslateFunctor` because it adds
-- a constant functor (in effect, a type) to a given functor.
-- This functor can be used to turn an endofunctor which we can interpret as
-- representing a datatype into one which we can interpret as representing
-- open terms of that datatype with variables drawn from type `v`.
-- It is the dual of `ScaleFunctor`.
public export
data TranslateFunctor : (Type -> Type) -> Type -> (Type -> Type) where
  TFV : {f : Type -> Type} -> {0 v, a : Type} ->
    v -> TranslateFunctor f v a
  TFC : {f : Type -> Type} -> {0 v, a : Type} ->
    f a -> TranslateFunctor f v a

public export
trElim : {0 f : Type -> Type} -> {0 v, a, x : Type} ->
  (v -> x) -> (f a -> x) -> TranslateFunctor f v a -> x
trElim {f} {v} {a} {x} fv ff (TFV ev) = fv ev
trElim {f} {v} {a} {x} fv ff (TFC efa) = ff efa

public export
Functor f => Bifunctor (TranslateFunctor f) where
  bimap f' g' (TFV x) = TFV $ f' x
  bimap f' g' (TFC x) = TFC $ map g' x

public export
TrEitherF : (Type -> Type) -> (Type -> Type)
TrEitherF f a = TranslateFunctor f a a

public export
sliceTrLift : {a : Type} -> {f : Type -> Type} ->
  (SliceObj a -> SliceObj (f a)) ->
  SliceObj a -> SliceObj (TrEitherF f a)
sliceTrLift {a} {f} m sa = trElim {f} {v=a} {a} {x=Type} sa (m sa)

-- For a given functor `F`, form the functor `Fa` defined by
-- `Fa[x] = a * F[x]`.  We call it `ScaleFunctor` because it multiplies
-- This functor can be used to turn an endofunctor which we can interpret as
-- representing a datatype into one which we can interpret as representing
-- potentially infinite trees of that datatype with labels drawn from type `v`.
-- It is the dual of `TranslateFunctor`.
public export
data ScaleFunctor : (Type -> Type) -> Type -> (Type -> Type) where
  SFN : {f : Type -> Type} -> {0 l, a : Type} ->
    l -> f a -> ScaleFunctor f l a

export
Functor f => Bifunctor (ScaleFunctor f) where
  bimap f' g' (SFN x fx) = SFN (f' x) (map g' fx)

public export
ScalePairF : (Type -> Type) -> (Type -> Type)
ScalePairF f a = ScaleFunctor f a a

export
treeLabel : {f : Type -> Type} -> {l, a : Type} -> ScaleFunctor f l a -> l
treeLabel (SFN a' _) = a'

export
treeSubtree : {f : Type -> Type} -> {l, a : Type} -> ScaleFunctor f l a -> f a
treeSubtree (SFN _ fx) = fx

-- An algebra on a functor representing a type of open terms (as generated
-- by `TranslateFunctor` above) may be viewed as a polymorphic algebra, because
-- for each object `v` it generates an `F[v]`-algebra on an any given carrier
-- object.  When `v` is the initial object (`Void`), it specializes to
-- generating `F`-algebras.
public export
TrAlgebra : (Type -> Type) -> Type -> Type -> Type
TrAlgebra f v = Algebra (TranslateFunctor f v)

public export
voidAlg : {f : Type -> Type} -> {a : Type} ->
  Algebra f a -> TrAlgebra f Void a
voidAlg alg (TFV {v=Void} _) impossible
voidAlg alg (TFC x) = alg x

public export
TermCoalgebra : (Type -> Type) -> Type -> Type -> Type
TermCoalgebra f v = Coalgebra (TranslateFunctor f v)

-- A coalgebra on a functor representing a type of labeled trees (as generated
-- by `ScaleFunctor` above) may be viewed as a polymorphic coalgebra, because
-- for each object `v` it generates an `F[v]`-coalgebra on an any given carrier
-- object.  When `v` is the terminal object (`Unit`), it specializes to
-- generating `F`-coalgebras.
public export
TreeCoalgebra : (Type -> Type) -> Type -> Type -> Type
TreeCoalgebra f v a = Coalgebra (ScaleFunctor f v) a

public export
unitCoalg : {f : Type -> Type} -> {a : Type} ->
  Coalgebra f a -> TreeCoalgebra f Unit a
unitCoalg alg x = SFN {l=()} () $ alg x

public export
TreeAlgebra : (Type -> Type) -> Type -> Type -> Type
TreeAlgebra f v a = Algebra (ScaleFunctor f v) a

--------------------------------------------------
---- Initial algebras and terminal coalgebras ----
--------------------------------------------------

-- If `F` has an initial algebra, then for every object `a`, the functor
-- `Fa` defined above also has an initial algebra, which is isomorphic
-- to `FreeMonad[F, a]`.  Thus `FreeMonad` allows us to create initial
-- `Fa`-algebras parameterized over arbitrary objects `a`, with the initial
-- algebra of `F` itself being the special case where `a` is the initial object
-- (`Void`).  `FreeMonad` is sometimes written `F*`.
--
-- Note that `FreeMonad` itself is a composition, but one which leaves
-- the category in which the endofunctors live before returning:  it is
-- the monad induced by the free-forgetful adjunction between the category
-- of endofunctors and the category of their F-algebras.  (The comonad
-- induced by the dual forgetful-cofree adjunction is `CofreeComonad`.)
public export
data FreeMonad : (Type -> Type) -> (Type -> Type) where
  InFree : {f : Type -> Type} -> {0 a : Type} ->
    TrAlgebra f a (FreeMonad f a)

public export
FreeAlgSig : (Type -> Type) -> Type -> Type
FreeAlgSig f a = Algebra f (FreeMonad f a)

public export
FreeMAlgSig : (Type -> Type) -> Type -> Type
FreeMAlgSig = Algebra . FreeMonad

public export
InitAlgSig : (Type -> Type) -> Type
InitAlgSig f = FreeAlgSig f Void

-- If `F` has a terminal coalgebra, then for every object `a`, the functor
-- `Fa` defined above also has a terminal coalgebra, which is isomorphic
-- to `CofreeComonad[F, a]`.  Thus `CofreeComonad` allows us to create terminal
-- `Fa`-coalgebras parameterized over arbitrary objects `a`, with the terminal
-- coalgebra of `F` itself being the special case where `a` is the terminal
-- object (`Unit`).  `CofreeComonad` is sometimes written `F_inf`.
public export
data CofreeComonad : (Type -> Type) -> (Type -> Type) where
  InCofree :
    {f : Type -> Type} -> {a : Type} ->
    Inf (ScaleFunctor f a (CofreeComonad f a)) -> CofreeComonad f a

public export
CofreeCoalgSig : (Type -> Type) -> Type -> Type
CofreeCoalgSig f a = Coalgebra f (CofreeComonad f a)

public export
CofreeCMCoalgSig : (Type -> Type) -> Type -> Type
CofreeCMCoalgSig f a = Coalgebra (CofreeComonad f) a

public export
TerminalCoalgSig : (Type -> Type) -> Type
TerminalCoalgSig f = CofreeCoalgSig f Unit

public export
CFCMerase : {0 f : Type -> Type} -> {0 a : Type} -> Algebra (CofreeComonad f) a
CFCMerase {a} (InCofree $ SFN ea _) = ea

-- The unit of the free monad.
public export
inFV : {f : Type -> Type} -> Coalgebra (FreeMonad f) a
inFV = InFree . TFV

public export
freeMunit : (f : Type -> Type) ->
  NaturalTransformation (Prelude.id {a=Type}) (FreeMonad f)
freeMunit f a = inFV {f} {a}

-- The free algebra of a functor.
public export
inFC : {f : Type -> Type} -> {0 a : Type} -> FreeAlgSig f a
inFC = InFree . TFC

public export
outFree : TermCoalgebra f a (FreeMonad f a)
outFree (InFree x) = x

public export
inCN : {a : Type} -> {f : Type -> Type} ->
  a -> Algebra f (CofreeComonad f a)
inCN x fx = InCofree $ SFN x fx

public export
outCofree : {f : Type -> Type} -> {a : Type} ->
  TreeCoalgebra f a (CofreeComonad f a)
outCofree (InCofree x) = x

public export
outCFC : {f : Type -> Type} -> {a : Type} -> Coalgebra f (CofreeComonad f a)
outCFC {f} (InCofree x) = case x of SFN _ fa => fa

-- Special case of `FreeMonad` where `v` is `Void`.
-- This is the fixpoint (least fixed point) of an endofunctor
-- (if it exists).
public export
Mu : (Type -> Type) -> Type
Mu f = FreeMonad f Void

-- The initial algebra of a functor.
public export
InitAlg : {f : Type -> Type} -> Algebra f (Mu f)
InitAlg {f} = inFC {f} {a=Void}

public export
InitAlgInv : {f : Type -> Type} -> Coalgebra f (Mu f)
InitAlgInv {f} (InFree (TFV v)) = void v
InitAlgInv {f} (InFree (TFC t)) = t

-- Special case of `CofreeComonad` where `v` is `Unit`.
-- This is the cofixpoint (greatest fixed point) of an endofunctor
-- (if it exists).
public export
Nu : (Type -> Type) -> Type
Nu f = CofreeComonad f Unit

-- The terminal coalgebra of a functor.
public export
outNu : {f : Type -> Type} -> TerminalCoalgSig f
outNu {f} = outCFC {f} {a=Unit}

public export
outNuInv : {f : Type -> Type} -> Algebra f (Nu f)
outNuInv {f} x = InCofree {f} {a=Unit} $ SFN () x

-- The signature of the "eval" universal morphism for "FreeMonad f".
-- (This is the right adjunct of the free/forgetful adjunction between
-- the category of F-algebras of `f` and `Type`.)
public export
FreeFEval : (Type -> Type) -> Type
FreeFEval f =
  (v, a : Type) -> (v -> a) -> Algebra f a -> FreeMonad f v -> a

-- This is the signature of the left adjunct of the free/forgetful adjunction
-- between the category of F-algebras of `f` and `Type`.
public export
FreeFLA : (Type -> Type) -> Type
FreeFLA f = (v, a : Type) -> (FreeMonad f v -> a) -> v -> a

-- The left adjunct itself.
public export
freeFLA : {f : Type -> Type} -> FreeFLA f
freeFLA {f} v a = (|>) inFV

-- Special induction.
public export
Catamorphism : (Type -> Type) -> Type
Catamorphism f = (a : Type) -> Algebra f a -> Mu f -> a

public export
cataFromEval : {f : Type -> Type} -> FreeFEval f -> Catamorphism f
cataFromEval pcata a = pcata Void a (voidF a)

{-
 - Note that the inverse of `cataFromEval`, which would be the following
 - (it would have to assume explicitly that `f` was a functor, i.e. that
 - it had a `map`), can not be guaranteed to be terminating without
 - stronger hypotheses:
 -
public export
freeEvalFromCata : Catamorphism f ->
  ({0 a, b : Type} -> (a -> b) -> f a -> f b) -> FreeFEval f
freeEvalFromCata {f} cata fm v a subst alg (InFree (TFV var)) = subst var
freeEvalFromCata {f} cata fm v a subst alg (InFree (TFC x)) = alg $
  fm {a=(FreeMonad f v)} {b=a} (freeEvalFromCata {f} cata fm v a subst alg) x
  -}

-- A form of general induction, which we could view as being able to
-- use the "eval" morphism of a free monad with arbitrary-depth rather
-- than single-depth pattern matching, since it requires only an algebra
-- of the free monad and not an algebra of the base functor.
public export
FreeFEvalGen : (Type -> Type) -> Type
FreeFEvalGen f =
  (v, a : Type) -> (v -> a) -> FreeMAlgSig f a -> FreeMonad f v -> a

public export
FAlgToFree : {a : Type} -> FreeFEval f -> Algebra f a -> FreeMAlgSig f a
FAlgToFree {f} {a} eval = eval a a id

public export
FAlgFromFree :
  {f : Type -> Type} -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  FreeMAlgSig f a -> Algebra f a
FAlgFromFree {f} {fm} {a} m = m . inFC . fm inFV

public export
FAlgFromFreeObj :
  {f : Type -> Type} -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  (alg : FAlgObj $ FreeMonad f) -> Algebra f (fst alg)
FAlgFromFreeObj {f} {fm} (a ** m) = FAlgFromFree {f} {fm} {a} m

public export
FAlgObjFromFree :
  {f : Type -> Type} -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  FAlgObj (FreeMonad f) -> FAlgObj f
FAlgObjFromFree {f} {fm} (a ** m) = (a ** FAlgFromFree {f} {fm} {a} m)

public export
FAlgObjToFree : {f : Type -> Type} -> FreeFEval f ->
  (alg : FAlgObj f) -> FreeMAlgSig f (fst alg)
FAlgObjToFree {f} eval (a ** m) = FAlgToFree {a} eval m

public export
FAlgObjToFreeObj :
  {f : Type -> Type} -> FreeFEval f -> FAlgObj f -> FAlgObj (FreeMonad f)
FAlgObjToFreeObj {f} eval (a ** m) = (a ** FAlgToFree {a} eval m)

public export
FAlgFreeAlgOn : (f : Type -> Type) -> (eval : FreeFEval f) ->
  (a : Type) -> FAlgObj (FreeMonad f)
FAlgFreeAlgOn f eval a = (FreeMonad f a ** FAlgToFree eval inFC)

public export
freeBind : {f : Type -> Type} -> FreeFEval f -> {a, b : Type} ->
  (a -> FreeMonad f b) -> FreeMonad f a -> FreeMonad f b
freeBind {f} {a} {b} eval = flip (eval a (FreeMonad f b)) inFC

public export
freeMap : {f : Type -> Type} -> FreeFEval f -> {a, b : Type} ->
  (a -> b) -> FreeMonad f a -> FreeMonad f b
freeMap {f} {a} {b} eval m = freeBind {f} {a} {b} eval (inFV . m)

public export
freeFJoin : {f : Type -> Type} -> FreeFEval f ->
  {a : Type} -> FreeMonad f (FreeMonad f a) -> FreeMonad f a
freeFJoin {f} {a} eval = freeBind {f} {a=(FreeMonad f a)} {b=a} eval id

public export
freeMmult : {f : Type -> Type} -> FreeFEval f ->
  NaturalTransformation (FreeMonad f . FreeMonad f) (FreeMonad f)
freeMmult {f} eval a = freeFJoin {f} eval {a}

public export
freeFApp : {f : Type -> Type} -> FreeFEval f ->
  {a, b : Type} -> FreeMonad f (a -> b) -> FreeMonad f a -> FreeMonad f b
freeFApp {f} {a} {b} eval ftree x =
  freeBind {f} eval {a=(a -> b)} {b} (flip (freeMap {f} eval) x) ftree

public export
freeFTreeBind : {f : Type -> Type} -> FreeFEval f ->
  {a, b : Type} -> FreeMonad f (a -> b) -> a -> FreeMonad f b
freeFTreeBind {f} {a} {b} eval ftree = freeFApp {f} eval {a} {b} ftree . inFV

-- Pattern-matching of arbitrary depth, folding to a single value.
-- (the latter of which need not (necessarily) be a free algebra itself).
public export
freeAppFold : {f : Type -> Type} -> FreeFEval f -> {a, b : Type} ->
  FreeMonad f (a -> b) -> Algebra f b -> FreeMonad f a -> b
freeAppFold {f} eval {a} {b} ftree alg =
  FAlgToFree {f} {a=b} eval alg . freeFApp {f} eval {a} {b} ftree

-- Pattern-matching of arbitrary depth, folding to another free monad.
public export
freeAppJoin : {f : Type -> Type} -> FreeFEval f -> {a, b : Type} ->
  FreeMonad f (a -> FreeMonad f b) -> FreeMonad f a -> FreeMonad f b
freeAppJoin {f} {a} eval ftree =
  freeFJoin {f} eval {a=b} . freeFApp {f} eval {a} {b=(FreeMonad f b)} ftree

public export
freeEvalToGen : {f : Type -> Type} -> FreeFEval f -> FreeFEvalGen f
freeEvalToGen {f} eval v a subst = (|>) (freeMap {f} eval subst)

-- The unit property of an algebra over a free monad.
public export
FreeMonadAlgUnitP : {f : Type -> Type} ->
  FreeFEval f -> FAlgObj (FreeMonad f) -> Type
FreeMonadAlgUnitP {f} eval alg =
  ExtEq (snd alg . IdrisCategories.inFV) Prelude.id

-- The action property of an algebra over a free monad.
public export
FreeMonadAlgActP : {f : Type -> Type} ->
  FreeFEval f -> FAlgObj (FreeMonad f) -> Type
FreeMonadAlgActP {f} eval alg =
  ExtEq (snd alg . (freeMap eval $ snd alg)) (snd alg . freeFJoin eval)

-- The properties required to make an algebra over the underlying endofunctor
-- of a monad into an algebra over a monad.
public export
FreeMonadAlgP : {f : Type -> Type} ->
  FreeFEval f -> FAlgObj (FreeMonad f) -> Type
FreeMonadAlgP {f} eval alg =
  (FreeMonadAlgUnitP {f} eval alg, FreeMonadAlgActP {f} eval alg)

-- The signature of an algebra not only over the underlying endofunctor of
-- a free monad, but over the free monad _as_ a monad in the sense of "algebra
-- over a monad", which is an algebra over the underlying endofunctor together
-- with conditions that represent compatibility between that algebra and the
-- unit and multiplication of the monad.
public export
FreeMonadAlg : {f : Type -> Type} -> FreeFEval f -> Type
FreeMonadAlg {f} eval = (a : FAlgObj (FreeMonad f) ** FreeMonadAlgP {f} eval a)

-- A morphism in the Eilenberg-Moore category of a (free) monad.
public export
FreeMonadAlgMorph : {f : Type -> Type} -> {eval : FreeFEval f} ->
  FreeMonadAlg {f} eval -> FreeMonadAlg {f} eval -> Type
FreeMonadAlgMorph {f} {eval} ((a ** m) ** ap) ((b ** n) ** bp) =
  Subset0 (a -> b) $ \g => ExtEq (g . m) (n . freeMap {f} eval g)

-- Every morphism between _free_ algebras over a monad (such as the free monad
-- of a functor that has one, which includes all polynomial functors)
-- corresponds to a Kleisli morphism.
public export
klMorphToFreeAlgMorph :
  (f : Type -> Type) -> {fm : {0 a, b : Type} -> (a -> b) -> f a -> f b} ->
  (eval : FreeFEval f) ->
  {a, b : Type} -> (m : Algebra f a) -> (n : Algebra f b) ->
  (g : a -> FreeMonad f b) ->
  FAlgCommutes {fm=(freeMap eval)}
    (FAlgFreeAlgOn f eval a) (FAlgFreeAlgOn f eval b) (freeBind eval g) ->
  FAlgMorph {f=(FreeMonad f)} {fm=(freeMap eval)}
    (FAlgFreeAlgOn f eval a) (FAlgFreeAlgOn f eval b)
klMorphToFreeAlgMorph f {fm} eval {a} {b} m n g comm =
  Element0 (freeBind eval g) comm

-- Lift a natural transformation between functors to a natural transformation
-- between their free monads.
public export
freeNTlift :
  {f : Type -> Type} -> FreeFEval f ->
  {g : Type -> Type} -> NaturalTransformation f g ->
  NaturalTransformation (FreeMonad f) (FreeMonad g)
freeNTlift {f} feval {g} alpha a =
  feval a (FreeMonad g a) inFV (inFC . alpha (FreeMonad g a))

-- The signature of the "trace" universal morphism for "CofreeComonad f".
public export
CofreeFTrace : (Type -> Type) -> Type
CofreeFTrace f =
  (l, a : Type) -> (a -> l) -> Coalgebra f a -> a -> CofreeComonad f l

public export
Anamorphism : (Type -> Type) -> Type
Anamorphism f = (a : Type) -> Coalgebra f a -> a -> Nu f

public export
anaFromTrace : {f : Type -> Type} -> CofreeFTrace f -> Anamorphism f
anaFromTrace pana a = pana Unit a (const ())

public export
CofreeFTraceGen : (Type -> Type) -> Type
CofreeFTraceGen f =
  (l, a : Type) -> (a -> l) -> CofreeCMCoalgSig f a -> a -> CofreeComonad f l

public export
CofreeCMAna : (Type -> Type) -> Type
CofreeCMAna f =
  (a : Type) -> CofreeCMCoalgSig f a -> a -> Nu f

--------------------------------------------------------
---- Natural transformations on (co)free (co)monads ----
--------------------------------------------------------

public export
FreeNaturalTransformation :
  (Type -> Type) -> (Type -> Type) -> (Type -> Type) -> Type
FreeNaturalTransformation m f g =
  (x : Type) -> f (FreeMonad m x) -> g (FreeMonad m x)

public export
CofreeNaturalTransformation :
  (Type -> Type) -> (Type -> Type) -> (Type -> Type) -> Type
CofreeNaturalTransformation m f g =
  (x : Type) -> f (CofreeComonad m x) -> g (CofreeComonad m x)

public export
FreeMonadNatTrans : (Type -> Type) -> (Type -> Type) -> Type
FreeMonadNatTrans f g =
  NaturalTransformation (FreeMonad f) (FreeMonad g)

public export
CofreeComonadNatTrans : (Type -> Type) -> (Type -> Type) -> Type
CofreeComonadNatTrans f g =
  NaturalTransformation (CofreeComonad f) (CofreeComonad g)

public export
FreeAdjUnit : (f, g : Type -> Type) -> Type
FreeAdjUnit m f = FreeNaturalTransformation m id f

public export
FreeAdjCounit : (f, g : Type -> Type) -> Type
FreeAdjCounit m f = FreeNaturalTransformation m f id

public export
CofreeAdjUnit : (f, g : Type -> Type) -> Type
CofreeAdjUnit m f = CofreeNaturalTransformation m id f

public export
CofreeAdjCounit : (f, g : Type -> Type) -> Type
CofreeAdjCounit m f = CofreeNaturalTransformation m f id

public export
natTransFreeAlg : {f, g : Type -> Type} ->
  NaturalTransformation f g -> FreeAdjCounit g f
natTransFreeAlg {f} {g} nt a = InFree . TFC . nt (FreeMonad g a)

public export
natTransMapFree :
  {f, g : Type -> Type} ->
  FreeFEval f ->
  NaturalTransformation f g ->
  FreeMonadNatTrans f g
natTransMapFree {f} {g} cataF nt carrier =
  cataF carrier
    (FreeMonad g carrier) (InFree . TFV) (natTransFreeAlg nt carrier)

-----------------------------
---- Polynomial algebras ----
-----------------------------

public export
ProductFAlg : (Type -> Type) -> (Type -> Type) -> Type -> Type
ProductFAlg f g a = f a -> Algebra g a

public export
ProductFAlgToAlg : {f, g : Type -> Type} -> {a : Type} ->
  ProductFAlg f g a -> Algebra (ProductF f g) a
ProductFAlgToAlg {f} {g} {a} alg (fx, gx) = alg fx gx

public export
CoproductFAlgToAlg : {f, g : Type -> Type} -> {a : Type} ->
  CoproductFAlg f g a -> Algebra (CoproductF f g) a
CoproductFAlgToAlg (algf, algg) (Left fx) = algf fx
CoproductFAlgToAlg (algf, algg) (Right gx) = algg gx

public export
CoproductToCoproductFAlg :
  (Type -> Type) -> (Type -> Type) ->
  (Type -> Type) -> (Type -> Type) ->
  Type -> Type
-- An algebra for computing a morphism `(f + g) a -> (f' + g') a`.
CoproductToCoproductFAlg f g f' g' a =
  (f a -> CoproductF f' g' a, g a -> CoproductF f' g' a)

--------------------------------------
--------------------------------------
---- Impredicative cofree comonad ----
--------------------------------------
--------------------------------------

export
data ImNu : (Type -> Type) -> Type where
  ImN : {0 f : Type -> Type} -> {0 a : Type} -> Coalgebra f a -> a -> ImNu f

export
imUnfold : {0 f : Type -> Type} -> {0 a : Type} -> Coalgebra f a -> a -> ImNu f
imUnfold = ImN

export
imTermCoalg : (0 f : Type -> Type) ->
  (fm : (0 a, b : Type) -> (a -> b) -> f a -> f b) -> Coalgebra f (ImNu f)
imTermCoalg f fm (ImN {f} {a} coalg ea) =
  fm a (ImNu f) (imUnfold {f} {a} coalg) (coalg ea)

-- The inverse of `imTermCoalg`, which we know by Lambek's theorem should exist.
export
imTermCoalgInv : (0 f : Type -> Type) ->
  (fm : (0 a, b : Type) -> (a -> b) -> f a -> f b) -> Algebra f (ImNu f)
imTermCoalgInv f fm efn =
  ImN {f} {a=(f $ ImNu f)} (fm (ImNu f) (f $ ImNu f) $ imTermCoalg f fm) efn

public export
CopointedF : (Type -> Type) -> Type -> Type -> Type
CopointedF = ScaleFunctor

export
inCP : {f : Type -> Type} -> {0 l, a : Type} ->
  (a -> l) -> Coalgebra f a -> Coalgebra (CopointedF f l) a
inCP {f} {l} {a} label coalg ea = SFN {f} {l} {a} (label ea) (coalg ea)

export
mapCP : {0 f : Type -> Type} ->
  (fm : (0 a, b : Type) -> (a -> b) -> f a -> f b) ->
  (l : Type) ->
  (0 a, b : Type) -> (a -> b) -> CopointedF f l a -> CopointedF f l b
mapCP {f} fm l a b m (SFN {f} {l} {a} el efa) =
  SFN {f} {l} {a=b} el $ fm a b m efa

public export
cpPoint : {0 f : Type -> Type} -> {0 l, a : Type} ->
  Algebra (flip (CopointedF f) a) l
cpPoint {f} {l} {a} (SFN {f} {l} {a} el efa) = el

public export
cpTerm : {0 f : Type -> Type} -> {0 l, a : Type} -> CopointedF f l a -> f a
cpTerm {f} {l} {a} (SFN {f} {l} {a} el efa) = efa

public export
CopointedAlg : (f : Type -> Type) -> Type -> Type -> Type
CopointedAlg f a = Algebra (CopointedF f a)

public export
CopointedCoalg : (f : Type -> Type) -> Type -> Type -> Type
CopointedCoalg f a = Coalgebra (CopointedF f a)

export
ImCofree : (Type -> Type) -> Type -> Type
ImCofree f a = ImNu (CopointedF f a)

public export
inCF : {f : Type -> Type} -> {0 l, a : Type} ->
  (a -> l) -> Coalgebra f a ->
  a -> ImCofree f l
inCF {f} {l} {a} = ImN {f=(CopointedF f l)} {a} .* inCP {f} {l} {a}

export
imCofreeTermCoalg : (f : Type -> Type) ->
  (fm : (0 a, b : Type) -> (a -> b) -> f a -> f b) ->
  (l : Type) -> Coalgebra (CopointedF f l) (ImCofree f l)
imCofreeTermCoalg f fm l = imTermCoalg (CopointedF f l) $ mapCP {f} fm l

export
imCofreeTermCoalgInv : (0 f : Type -> Type) ->
  (fm : (0 a, b : Type) -> (a -> b) -> f a -> f b) ->
  (l : Type) -> Algebra (CopointedF f l) (ImCofree f l)
imCofreeTermCoalgInv f fm l = imTermCoalgInv (CopointedF f l) (mapCP {f} fm l)

-- `imLabel` is the counit of the (impredicative) cofree-comonad adjunction.
-- That means it is also the counit of the comonad arising from the adjunction;
-- as such it is also sometimes called "erase" or "extract".
export
imLabel : (f : Type -> Type) ->
  (fm : (0 a, b : Type) -> (a -> b) -> f a -> f b) ->
  NaturalTransformation (ImCofree f) Prelude.id
imLabel f fm l = cpPoint {f} {l} {a=(ImCofree f l)} . imCofreeTermCoalg f fm l

export
imSubtrees : (f : Type -> Type) ->
  (fm : (0 a, b : Type) -> (a -> b) -> f a -> f b) ->
  (l : Type) -> Coalgebra f (ImCofree f l)
imSubtrees f fm l = cpTerm {f} {l} {a=(ImCofree f l)} . imCofreeTermCoalg f fm l

-- `Trace` is a universal morphism of the cofree comonad.  Specifically, it is
-- the left adjunct:  given an object `sl : SliceObj c` and a coalgebra
-- `sa : SliceObj c`/`coalg : SSCoalg {c} f sa`, the left adjunct takes a
-- slice morphism `label : SliceMorphism {a=c} sa sl` and returns a
-- coalgebra morphism `SliceSigmaTrace coalg label :
-- SliceMorphism {a=c} sa (SliceSigmaCM f sl)`.
imTrace : {f : Type -> Type} ->
  {0 a, l : Type} ->
  Coalgebra f a -> (a -> l) -> a -> ImCofree f l
imTrace {f} {a} {l} = flip $ inCF {f} {l} {a}

-- The unit of the cofree comonad adjunction -- a natural transformation
-- between endofunctors on the category of F-coalgebras, from the identity
-- endofunctor to the cofree comonad.
imUnit : {f : Type -> Type} ->
  {0 a : Type} -> Coalgebra f a -> Coalgebra (ImCofree f) a
imUnit {f} {a} coalg = imTrace {f} {a} {l=a} coalg id

-- The right adjunct of the cofree comonad, given an object
-- `sl : SliceObj c` and a coalgebra `sa : SliceObj c`/`coalg : SSCoalg f sa`,
-- takes a coalgebra morphism to the cofree coalgebra `SliceSigmaCM f sl` from
-- `sa`, i.e. a morphism of type `SliceMorphism {a=c} sa (SliceSigmaCM f sl)`,
-- and returns a slice morphism `label : SliceMorphism {a=c} sa sl`.
--
-- The implementation does not use the morphism component of the coalgebra,
-- so we omit it from the signature.  The reason for this is that this is the
-- right adjunct of a free-forgetful adjunction, and the only use of the
-- input to the right adjunct in the formula that expresses the right adjunct in
-- terms of the counit (`imLabel`, in this case) is to apply the left adjoint to
-- it, and the left adjoint just forgets the morphism component.
export
imRAdj : {f : Type -> Type} ->
  (fm : (0 a, b : Type) -> (a -> b) -> f a -> f b) ->
  {a, l : Type} ->
  (a -> ImCofree f l) -> a -> l
imRAdj {f} fm {a} {l} = (.) $ imLabel f fm l

-- `imJoin` is the multiplication of the (impredicative) cofree-comonad
-- adjunction.  That means it is also the multiplication of the monad
-- arising from the adjunction; as such it is also sometimes called "join".
--
-- The multiplication comes from whiskering the counit between the adjuncts.
imJoin : {f : Type -> Type} ->
  (fm : (0 a, b : Type) -> (a -> b) -> f a -> f b) ->
  NaturalTransformation (ImCofree f . ImCofree f) (ImCofree f)
imJoin {f} fm a = imLabel f fm (ImCofree f a)

-- `imDup` is the comultiplication of the (impredicative) cofree-comonad
-- adjunction.  That means it is also the comultiplication of the comonad
-- arising from the adjunction; as such it is also sometimes called "duplicate".
--
-- The comultiplication comes from whiskering the unit between the adjuncts.
export
imDup : (f : Type -> Type) ->
  (fm : (0 a, b : Type) -> (a -> b) -> f a -> f b) ->
  NaturalTransformation (ImCofree f) (ImCofree f . ImCofree f)
imDup f fm a = imUnit {f} {a=(ImCofree f a)} (imSubtrees f fm a)

-----------------------------------------------------------
-----------------------------------------------------------
---- Adjoint (un)folds, conjugate (para-)hylomorphisms ----
-----------------------------------------------------------
-----------------------------------------------------------

-----------------------------------
---- Adjoint folds and unfolds ----
-----------------------------------

-- See:
-- https://www.researchgate.net/publication/221440236_Adjoint_Folds_and_Unfolds
-- https://www.semanticscholar.org/paper/Adjoint-folds-and-unfolds-An-extended-study-Hinze/ab88bbc168e2f3a26ac67adb221e89080c9746c3

public export
partial
muFree : Functor f => TrAlgebra f v a -> FreeMonad f v -> a
muFree alg (InFree x) = alg $ case x of
  TFV x => TFV x
  TFC x => TFC $ map (muFree alg) x

public export
voidalg : Algebra f a -> Algebra (TranslateFunctor f Void) a
voidalg alg (TFV _) impossible
voidalg alg (TFC x) = alg x

public export
partial
mu : {f : Type -> Type} -> Functor f => Algebra f a -> Mu f -> a
mu = muFree . voidalg

export
partial
adjointFoldFree : {f : Type -> Type} -> (Functor f, Functor l, Functor r) =>
  (counit : (a : Type) -> l (r a) -> a) ->
  {v, a : Type} ->
  Algebra (TranslateFunctor f v) (r a) -> l (FreeMonad f v) -> a
adjointFoldFree counit {a} alg = counit a . map {f=l} (muFree alg)

export
partial
adjointFold : {f : Type -> Type} -> (Functor f, Functor l, Functor r) =>
  (counit : (a : Type) -> l (r a) -> a) ->
  {a : Type} -> Algebra f (r a) -> l (Mu f) -> a
adjointFold counit {a} alg = counit a . map {f=l} (mu alg)

public export
partial
nuFree : {f : Type -> Type} -> Functor f => {v, a : Type} ->
  Coalgebra (ScaleFunctor f v) a -> a -> CofreeComonad f v
nuFree coalg x with (coalg x)
  nuFree coalg x | SFN x' v' =
    InCofree $ SFN x' $ map (nuFree coalg) v'

export
partial
adjointUnfoldFree : {f, l, r : Type -> Type} ->
  (Functor f, Functor l, Functor r) =>
  (unit : (a : Type) -> a -> r (l a)) ->
  {v, a : Type} ->
  Coalgebra (ScaleFunctor f v) (l a) -> a -> r (CofreeComonad f v)
adjointUnfoldFree unit {a} coalg = map {f=r} (nuFree coalg) . unit a

public export
unitcoalg : {f : Type -> Type} -> {a : Type} ->
  Coalgebra f a -> Coalgebra (ScaleFunctor f ()) a
unitcoalg coalg = SFN () . coalg

export
partial
adjointUnfold : {f, l, r : Type -> Type} -> (Functor f, Functor l, Functor r) =>
  (unit : (a : Type) -> a -> r (l a)) ->
  {a : Type} -> Coalgebra f (l a) -> a -> r (Nu f)
adjointUnfold unit = adjointUnfoldFree unit . unitcoalg

--------------------------------------
---- Conjugate para-hylomorphisms ----
--------------------------------------

-- See:
-- https://www.semanticscholar.org/paper/Conjugate-Hylomorphisms-Or%3A-The-Mother-of-All-Hinze-Wu/248e7e6143bbd346f88b766d2afc71439da2c26b

-- Uses a data structure represented by a "data functor" `d` internally to
-- compute a function from `c` to `a`.  An adjunction `l` |- `r` transforms
-- `d` into a "control functor" which specifies the recursion scheme.
export
partial
hyloFree : {v, c, a : Type} ->
  {d, l, r : Type -> Type} -> (Functor d, Functor l, Functor r) =>
  (unit : (ty : Type) -> ty -> r (l ty)) ->
  (coalg : c -> (ScaleFunctor d v) c) ->
  (alg : (l c, (l . (ScaleFunctor d v) . r) a) -> a) ->
  l c -> a
hyloFree unit coalg alg x =
  let
    transport =
      map {f=l} . map @{BifunctorToFunctor} {f=(ScaleFunctor d v)} . map {f=r}
    hylo_trans = transport $ hyloFree unit coalg alg
    unfolded = map {f=l} coalg x
    unfolded_trans =
      map (map @{BifunctorToFunctor} {f=(ScaleFunctor d v)} (unit c)) unfolded
  in
  alg (x, hylo_trans unfolded_trans)

export
partial
hylomorphism : {c, a : Type} ->
  {d, l, r : Type -> Type} -> (Functor d, Functor l, Functor r) =>
  (unit : (ty : Type) -> ty -> r (l ty)) ->
  (coalg : c -> d c) ->
  (alg : (l c, (l . d . r) a) -> a) ->
  l c -> a
hylomorphism {d} {l} {r} unit coalg alg =
  hyloFree {v=()} {d} {l} {r} unit (unitcoalg coalg) unitalg
    where
    unitalg : (l c, (l . ScaleFunctor d () . r) a) -> a
    unitalg (x, x') = alg (x, map treeSubtree x')

----------------------------------------
----------------------------------------
---- Representables and polynomials ----
----------------------------------------
----------------------------------------

public export
ProductN : Nat -> Type -> Type
ProductN 0 _ = ()
ProductN (S n) a = (a, ProductN n a)

public export
mapProductN : (n : Nat) -> {0 a, b : Type} ->
  (f : a -> b) -> ProductN n a -> ProductN n b
mapProductN Z f () = ()
mapProductN (S n) f (x, p) = (f x, mapProductN n f p)

public export
(n : Nat) => Functor (ProductN n) where
  map {n} = mapProductN n

public export
CovarHomFunc : Type -> (Type -> Type)
CovarHomFunc a = \ty => a -> ty

public export
Functor (CovarHomFunc a) where
  map = (.)

public export
Applicative (CovarHomFunc a) where
  pure = const
  (g <*> f) x = g x (f x)

public export
Monad (CovarHomFunc a) where
  (f >>= g) x = g (f x) x

public export
FinCovarHomFunc : Nat -> (Type -> Type)
FinCovarHomFunc = ProductN

public export
CovarHomAlg : Type -> Type -> Type
CovarHomAlg a b = (a -> b) -> b

public export
FinCovarHomAlg : Nat -> Type -> Type
FinCovarHomAlg Z b = b
FinCovarHomAlg (S n) b = b -> FinCovarHomAlg n b

CovarHomAlgCorrect : (a, b : Type) ->
  CovarHomAlg a b = Algebra (CovarHomFunc a) b
CovarHomAlgCorrect a b = Refl

public export
CovarHomCoalg : Type -> Type -> Type
CovarHomCoalg a b = b -> (a -> b)

public export
FinCovarHomCoalg : Nat -> Type -> Type
FinCovarHomCoalg n b = ProductN n (b -> b)

CovarHomCoalgCorrect : (a, b : Type) ->
  CovarHomCoalg a b = Coalgebra (CovarHomFunc a) b
CovarHomCoalgCorrect a b = Refl

public export
ContravarHomFunc : Type -> (Type -> Type)
ContravarHomFunc a = \ty => ty -> a

public export
[ContravarHomFuncContravar] Contravariant (ContravarHomFunc a) where
  contramap = (|>)

public export
FinContravarHomFunc : Nat -> (Type -> Type)
FinContravarHomFunc n = \ty => ty -> Fin n

public export
ContravarHomAlg : Type -> Type -> Type
ContravarHomAlg a b = (b -> a) -> b

public export
HomEither : Type -> Type -> Type -> Type
HomEither a e = CovarHomFunc a . Either e

public export
Functor (HomEither a e) where
  map = map {f=(CovarHomFunc a)} . map {f=(Either e)}

public export
Applicative (HomEither a e) where
  pure = pure {f=(CovarHomFunc a)} . pure {f=(Either e)}
  (g <*> f) x = g x <*> f x

public export
Monad (HomEither a e) where
  (f >>= g) x = f x >>= flip g x

public export
EitherHom : Type -> Type -> Type -> Type
EitherHom = flip HomEither

public export
FinContravarHomAlg : Nat -> Type -> Type
FinContravarHomAlg n b = (b -> Fin n) -> b

public export
ContravarHomAlgCorrect : (a, b : Type) ->
  ContravarHomAlg a b = Algebra (ContravarHomFunc a) b
ContravarHomAlgCorrect a b = Refl

public export
ContravarHomCoalg : Type -> Type -> Type
ContravarHomCoalg a b = b -> (b -> a)

public export
FinContravarHomCoalg : Nat -> Type -> Type
FinContravarHomCoalg n b = b -> b -> Fin n

public export
ContravarHomCoalgCorrect : (a, b : Type) ->
  ContravarHomCoalg a b = Coalgebra (ContravarHomFunc a) b
ContravarHomCoalgCorrect a b = Refl

public export
FreeCovar : Type -> Type -> Type
FreeCovar = FreeMonad . CovarHomFunc

public export
FreeFinCovar : Nat -> Type -> Type
FreeFinCovar = FreeMonad . FinCovarHomFunc

public export
MuFinCovar : Nat -> Type
MuFinCovar = Mu . FinCovarHomFunc

public export
FinCovarHomAlgToAlg : {n : Nat} -> {b : Type} ->
  FinCovarHomAlg n b -> Algebra (FinCovarHomFunc n) b
FinCovarHomAlgToAlg {n=0} alg x = alg
FinCovarHomAlgToAlg {n=(S n)} alg (x, p) = FinCovarHomAlgToAlg (alg x) p

public export
finCovarFreeAlgebra : (n : Nat) -> (0 a : Type) ->
  FreeAlgSig (FinCovarHomFunc n) a
finCovarFreeAlgebra Z a x = InFree $ TFC ()
finCovarFreeAlgebra (S n) a (x, p) = InFree $ TFC (x, p)

public export
FinCovarInitialAlgebra : (n : Nat) -> InitAlgSig (FinCovarHomFunc n)
FinCovarInitialAlgebra n = finCovarFreeAlgebra n Void

mutual
  public export
  cataFinCovar : (n : Nat) -> FreeFEval (FinCovarHomFunc n)
  cataFinCovar n v a subst alg (InFree x) = case x of
    TFV var => subst var
    TFC com => alg $ case n of
      Z => com
      S n' => case com of
        (x', com') =>
          (cataFinCovar (S n') v a subst alg x',
           cataFinCovarN n' (S n') v a subst alg com')

  public export
  cataFinCovarN : (n, n' : Nat) -> (v, a : Type) ->
    (v -> a) -> Algebra (FinCovarHomFunc n') a ->
    ProductN n (FreeFinCovar n' v) -> ProductN n a
  cataFinCovarN Z n' v a subst alg () = ()
  cataFinCovarN (S n) n' v a subst alg (x, p) =
    (cataFinCovar n' v a subst alg x,
     cataFinCovarN n n' v a subst alg p)

public export
finCovarMap : {n : Nat} -> {a, b : Type} ->
  (a -> b) -> FreeFinCovar n a -> FreeFinCovar n b
finCovarMap {n} {a} {b} f =
  cataFinCovar n a (FreeFinCovar n b)
    (InFree . TFV . f)
    (InFree . TFC)

public export
finCovarMapN : {n, n' : Nat} -> {a, b : Type} ->
    (a -> b) -> ProductN n (FreeFinCovar n' a) -> ProductN n (FreeFinCovar n' b)
finCovarMapN {n} {n'} f =
  cataFinCovarN n n' a (FreeFinCovar n' b)
    (InFree . TFV . f)
    (InFree . TFC)

public export
finCovarReturn : {n : Nat} -> {0 a : Type} -> a -> FreeFinCovar n a
finCovarReturn x = InFree $ TFV x

public export
finCovarFreeMCata : {n : Nat} -> FreeFEvalGen (FinCovarHomFunc n)
finCovarFreeMCata {n} v a subst alg (InFree x) = case x of
  TFV var => subst var
  TFC com => alg $ InFree $ TFC $
    mapProductN n (finCovarMap subst) com

public export
finCovarFreeMCataN : (n, n' : Nat) -> (v, a : Type) ->
  (v -> a) -> Algebra (FreeFinCovar n') a ->
  ProductN n (FreeFinCovar n' v) ->
  ProductN n a
finCovarFreeMCataN n n' v a subst alg =
  mapProductN n (finCovarFreeMCata v a subst alg)

mutual
  public export
  partial
  finCovarApply : {n : Nat} -> {a, b : Type} ->
    FreeFinCovar n (a -> b) ->
    FreeFinCovar n a ->
    FreeFinCovar n b
  finCovarApply (InFree f) (InFree x) = InFree $ case (f, x) of
    (TFV fv, TFV xv) =>
      TFV $ fv xv
    (TFV fv, TFC xc) =>
      TFC $ finCovarMapN fv xc
    (TFC fc, TFV xv) =>
      TFC $ finCovarApplyN1 fc xv
    (TFC fc, TFC xc) =>
      TFC $ finCovarApplyNN fc xc

  public export
  partial
  finCovarApply11 : {n : Nat} -> {0 a, b : Type} ->
    FreeFinCovar n (a -> b) ->
    a ->
    FreeFinCovar n b
  finCovarApply11 {n=Z} (InFree f) x = InFree $ TFC ()
  finCovarApply11 {n=(S n)} (InFree f) x = InFree $ case f of
    TFV fv => TFV $ fv x
    TFC (f, fp) => TFC $
      (finCovarApply11 f x, finCovarApplyN1 fp x)

  public export
  partial
  finCovarApplyN1 : {n, n' : Nat} -> {0 a, b : Type} ->
    ProductN n (FreeFinCovar n' (a -> b)) ->
    a ->
    ProductN n (FreeFinCovar n' b)
  finCovarApplyN1 {n=Z} () x = ()
  finCovarApplyN1 {n=(S n)} (f, fp) x =
    (finCovarApply11 f x, finCovarApplyN1 fp x)

  public export
  partial
  finCovarApplyNN : {n, n' : Nat} -> {a, b : Type} ->
    ProductN n (FreeFinCovar n' (a -> b)) ->
    ProductN n (FreeFinCovar n' a) ->
    ProductN n (FreeFinCovar n' b)
  finCovarApplyNN {n=Z} () () = ()
  finCovarApplyNN {n=(S n)} (InFree f, fp) (InFree x, xp) =
    let
      recnn = finCovarApplyNN fp xp
      recapply = InFree $ case (f, x) of
        (TFV fv, TFV xv) =>
          TFV $ fv xv
        (TFV fv, TFC xc) =>
          TFC $ finCovarMapN fv xc
        (TFC fc, TFV xv) =>
          TFC $ finCovarApplyN1 fc xv
        (TFC fc, TFC xc) =>
          TFC $ finCovarApplyNN fc xc
    in
    (recapply, recnn)

mutual
  public export
  finCovarJoin : {n : Nat} -> {0 a : Type} ->
    FreeFinCovar n (FreeFinCovar n a) -> FreeFinCovar n a
  finCovarJoin (InFree x) = case x of
    TFV var => var
    TFC com => finCovarFreeAlgebra n a $ finCovarJoinN com

  public export
  finCovarJoinN : {n, n' : Nat} -> {0 a : Type} ->
    ProductN n (FreeFinCovar n' (FreeFinCovar n' a)) ->
    ProductN n (FreeFinCovar n' a)
  finCovarJoinN {n=Z} () = ()
  finCovarJoinN {n=(S n)} (x, p) = (finCovarJoin x, finCovarJoinN p)

{-
 -
public export
[FinCovarFunctor] (n : Nat) => Functor (FreeFinCovar n) where
  map = finCovarMap {n}
 -
 - Idris for some reason can't find the Functor or Applicative instances in
 - the Applicative or Monad declarations respectively.
 -
public export
[FinCovarApplicative] (n : Nat) =>
    Applicative (FreeFinCovar n) using FinCovarFunctor where
  pure = finCovarReturn {n}
  (<*>) = finCovarApply {n}

public export
[FinCovarMonad] (n : Nat) =>
    Monad (FreeFinCovar n) using FinCovarApplicative where
  join = finCovarJoin {n}
 -
 -}

public export
FinPolyData : Type
FinPolyData = List (Type, Nat)

public export
FinPolyFunc : FinPolyData -> (Type -> Type)
FinPolyFunc [] _ = Void
FinPolyFunc ((coeff, pow) :: l) ty =
  Either (coeff -> FinCovarHomFunc pow ty) (FinPolyFunc l ty)

public export
FinPolyAlg : FinPolyData -> Type -> Type
FinPolyAlg [] _ = ()
FinPolyAlg ((coeff, pow) :: l) ty =
  ((coeff -> FinCovarHomFunc pow ty) -> ty, FinPolyAlg l ty)

public export
FinPolyAlgToAlg : {fpd : FinPolyData} -> {a : Type} ->
  FinPolyAlg fpd a -> Algebra (FinPolyFunc fpd) a
FinPolyAlgToAlg {fpd=[]} {a} alg x = void x
FinPolyAlgToAlg {fpd=((coeff, pow) :: fpd')} {a} (leftAlg, rightAlg) x =
  case x of
    Left fields => leftAlg fields
    Right records => FinPolyAlgToAlg {fpd=fpd'} rightAlg records

public export
FreeFinPoly : FinPolyData -> Type -> Type
FreeFinPoly = FreeMonad . FinPolyFunc

public export
MuFinPoly : FinPolyData -> Type
MuFinPoly = Mu . FinPolyFunc

public export
finPolyFreeAlgebra : (fpd : FinPolyData) -> (0 a : Type) ->
  FreeAlgSig (FinPolyFunc fpd) a
finPolyFreeAlgebra [] a v = void v
finPolyFreeAlgebra fpd a x = InFree $ TFC x

public export
FinPolyInitialAlgebra : (fpd : FinPolyData) -> InitAlgSig (FinPolyFunc fpd)
FinPolyInitialAlgebra fpd = finPolyFreeAlgebra fpd Void

mutual
  public export
  cataFinPoly : (fpd : FinPolyData) -> FreeFEval (FinPolyFunc fpd)
  cataFinPoly fpd v a subst alg (InFree poly) = case poly of
    TFV var => subst var
    TFC com => alg $ case fpd of
      [] => void com
      ((coeff, pow) :: terms) => case com of
        Left fields => Left $ cataFinPolyFuncN subst alg . fields -- (c, cataFinPolyFuncN subst alg p)
        Right poly => Right $
          cataFinPolyFunc
            {fpd=terms} {fpd'=((coeff, pow) :: terms)} {v} {a} subst alg poly

  public export
  cataFinPolyFunc : {fpd, fpd' : FinPolyData} -> {v, a : Type} ->
    (v -> a) -> Algebra (FinPolyFunc fpd') a ->
    FinPolyFunc fpd (FreeFinPoly fpd' v) -> FinPolyFunc fpd a
  cataFinPolyFunc {fpd=[]} {fpd'} {a} subst alg poly = void poly
  cataFinPolyFunc {fpd=((_, pow) :: terms)} {fpd'} {v} {a} subst alg poly =
    case poly of
      Left fields => Left $ cataFinPolyFuncN {fpd=fpd'} {pow} subst alg . fields
      Right poly' => Right $ cataFinPolyFunc {fpd=terms} {fpd'} subst alg poly'

  public export
  cataFinPolyFuncN : {fpd : FinPolyData} -> {v, a : Type} -> {pow : Nat} ->
    (v -> a) -> Algebra (FinPolyFunc fpd) a ->
    ProductN pow (FreeFinPoly fpd v) ->
    ProductN pow a
  cataFinPolyFuncN {pow=Z} subst alg () = ()
  cataFinPolyFuncN {pow=(S pow)} subst alg (x, p) =
    (cataFinPoly fpd v a subst alg x, cataFinPolyFuncN {pow} subst alg p)

public export
finPolyMap : {fpd : FinPolyData} -> {a, b : Type} ->
  (a -> b) -> FinPolyFunc fpd a -> FinPolyFunc fpd b
finPolyMap {fpd=[]} {a} {b} f poly = void poly
finPolyMap {fpd=((coeff, pow) :: terms)} {a} {b} f poly = case poly of
  Left fields => Left $ mapProductN pow f . fields
  Right poly' => Right $ finPolyMap f poly'

public export
freeFinPolyMap : {fpd : FinPolyData} -> {a, b : Type} ->
  (a -> b) -> FreeFinPoly fpd a -> FreeFinPoly fpd b
freeFinPolyMap {fpd} {a} {b} f =
  cataFinPoly fpd
    a (FreeFinPoly fpd b) (InFree . TFV . f) (InFree . TFC)

public export
finPolyFuncMap : {fpd, fpd' : FinPolyData} -> {a, b : Type} ->
  (a -> b) ->
  FinPolyFunc fpd (FreeFinPoly fpd' a) -> FinPolyFunc fpd (FreeFinPoly fpd' b)
finPolyFuncMap {a} {b} f =
  cataFinPolyFunc
    {v=a} {a=(FreeFinPoly fpd' b)}
    (InFree . TFV . f) (InFree . TFC)

public export
freeFinPolyMapN : {pow : Nat} -> {fpd : FinPolyData} -> {a, b : Type} ->
  (a -> b) ->
  ProductN pow (FreeFinPoly fpd a) -> ProductN pow (FreeFinPoly fpd b)
freeFinPolyMapN {pow} {fpd} {a} {b} f =
  cataFinPolyFuncN {fpd} {v=a} {a=(FreeFinPoly fpd b)}
    (InFree . TFV . f) (InFree . TFC)

public export
finPolyReturn : {fpd : FinPolyData} -> {0 a : Type} -> a -> FreeFinPoly fpd a
finPolyReturn x = InFree $ TFV x

public export
finPolyFreeMCata : {fpd : FinPolyData} ->
  FreeFEvalGen (FinPolyFunc fpd)
finPolyFreeMCata {fpd} v a subst alg (InFree x) = case x of
  TFV var => subst var
  TFC com => alg $ InFree $ TFC $ finPolyFuncMap subst com

public export
finPolyFreeMCataFunc : (fpd, fpd' : FinPolyData) -> (v, a : Type) ->
  (v -> a) -> Algebra (FreeFinPoly fpd') a ->
  FinPolyFunc fpd (FreeFinPoly fpd' v) ->
  FinPolyFunc fpd a
finPolyFreeMCataFunc fpd fpd' v a subst alg =
  finPolyMap {fpd} {a=(FreeFinPoly fpd' v)} {b=a}
    (finPolyFreeMCata {fpd=fpd'} v a subst alg)

public export
finPolyFreeMCataN : (fpd : FinPolyData) -> (n : Nat) -> (v, a : Type) ->
  (v -> a) -> Algebra (FreeFinPoly fpd) a ->
  ProductN n (FreeFinPoly fpd v) ->
  ProductN n a
finPolyFreeMCataN fpd n v a subst alg =
  mapProductN n (finPolyFreeMCata {fpd} v a subst alg)

{-
 - This won't work until the specification for polynomial endofunctors
 - becomes narrower.
mutual
  public export
  finPolyApply : {fpd : FinPolyData} -> {a, b : Type} ->
    FreeFinPoly fpd (a -> b) ->
    FreeFinPoly fpd a ->
    FreeFinPoly fpd b
  finPolyApply {fpd} (InFree f) (InFree x) = InFree $ case fpd of
    [] => case f of
      TFV fvar => TFV $ case x of
        TFV xvar => fvar xvar
        TFC xcom => void xcom
      TFC fcom => void fcom
    ((coeff, pow) :: terms) => case (f, x) of
      (TFV fv, TFV xv) => TFV $ fv xv
      (TFV fv, TFC xc) => TFC $ case xc of
        Left fields => Left $ freeFinPolyMapN fv . fields
        Right xcr => Right $ finPolyFuncMap fv xcr
      (TFC fc, TFV xv) => TFC $ case fc of
        Left fields => Left $ mapProductN pow (finPolyApply11 xv) . fields
        Right terms => Right $ finPolyApplyF1 xv terms
      (TFC fc, TFC xc) => TFC $ case (fc, xc) of
        (Left ffields, Left xfields) =>
          Left $ \c => finPolyApplyNN (ffields c) (xfields c)
        (Left ffields, Right xterms) =>
          Left $ \c => finPolyApplyNF (ffields c) xterms
        (Right fterm, Left xfields) =>
          Left $ \c => finPolyApplyFN fterm (xfields c)
        (Right fterm, Right xterms) =>
          Right $ finPolyApplyFF fterm xterms

  public export
  finPolyApply11 : {fpd : FinPolyData} -> {a, b : Type} ->
    a -> FreeFinPoly fpd (a -> b) -> FreeFinPoly fpd b
  finPolyApply11 ax (InFree fx) = InFree $ case fx of
    TFV fv => TFV $ fv ax
    TFC fcom => TFC $ finPolyApplyF1 ax fcom

  public export
  finPolyApplyNF : {pow : Nat} -> {fpd, fpd' : FinPolyData} -> {a, b : Type} ->
    ProductN pow (FreeFinPoly fpd' (a -> b)) ->
    FinPolyFunc fpd (FreeFinPoly fpd' a) ->
    ProductN pow (FreeFinPoly fpd' b)
  finPolyApplyNF {pow=Z} () ap = ()
  finPolyApplyNF {pow=(S pow)} (fp, fn) ap =
    (finPolyApplyFP fp ap, finPolyApplyNF fn ap)

  public export
  finPolyApplyFP : {fpd, fpd' : FinPolyData} -> {a, b : Type} ->
    FreeFinPoly fpd' (a -> b) ->
    FinPolyFunc fpd (FreeFinPoly fpd' a) ->
    FreeFinPoly fpd' b
  finPolyApplyFP {fpd=[]} (InFree fx) v = void v
  finPolyApplyFP {fpd=((coeff, pow) :: terms)} (InFree fx) xp = case (fx, xp) of
    (TFV fv, Left xfields) =>
      InFree $ TFC $ finPolyApplyFP_hole_fvxf
    (TFC fc, Left xfields) =>
      finPolyApplyFP_hole_fcxf
    (TFV fv, Right xterms) =>
      finPolyApplyFP_hole_fvxt
    (TFC fc, Right xterms) =>
      finPolyApplyFP_hole_fcxt

  public export
  finPolyApplyFN : {pow : Nat} -> {fpd, fpd' : FinPolyData} -> {a, b : Type} ->
    FinPolyFunc fpd (FreeFinPoly fpd' (a -> b)) ->
    ProductN pow (FreeFinPoly fpd' a) ->
    ProductN pow (FreeFinPoly fpd' b)
  finPolyApplyFN = finPolyApplyFN_hole

  public export
  finPolyApplyF1 : {fpd, fpd' : FinPolyData} -> {a, b : Type} ->
    a ->
    FinPolyFunc fpd (FreeFinPoly fpd' (a -> b)) ->
    FinPolyFunc fpd (FreeFinPoly fpd' b)
  finPolyApplyF1 = finPolyApply1F_hole

  public export
  finPolyApply1N : {pow : Nat} -> {fpd : FinPolyData} -> {a, b : Type} ->
    a ->
    ProductN pow (FreeFinPoly fpd (a -> b)) ->
    ProductN pow (FreeFinPoly fpd b)
  finPolyApply1N = finPolyApplyN_hole

  public export
  finPolyApplyNN : {pow : Nat} -> {fpd : FinPolyData} -> {a, b : Type} ->
    ProductN pow (FreeFinPoly fpd (a -> b)) ->
    ProductN pow (FreeFinPoly fpd a) ->
    ProductN pow (FreeFinPoly fpd b)
  finPolyApplyNN = finPolyApplyNN_hole

  public export
  finPolyApplyFF : {fpd, fpd' : FinPolyData} -> {a, b : Type} ->
    FinPolyFunc fpd (FreeFinPoly fpd' (a -> b)) ->
    FinPolyFunc fpd (FreeFinPoly fpd' a) ->
    FinPolyFunc fpd (FreeFinPoly fpd' b)
  finPolyApplyFF {fpd=[]} _ v = void v
  finPolyApplyFF {fpd=((coeff, pow) :: terms)} f x = finPolyApplyFF_hole

mutual
  public export
  finPolyJoin : {fpd : FinPolyData} -> {0 a : Type} ->
    FreeFinPoly fpd (FreeFinPoly fpd a) -> FreeFinPoly fpd a
  finPolyJoin {fpd} {a} (InFree x) = case x of
    TFV var => var
    TFC com => finPolyFreeAlgebra fpd a $ finPolyJoinFunc com

  public export
  finPolyJoinN : {pow : Nat} -> {fpd : FinPolyData} -> {0 a : Type} ->
    ProductN pow (FreeFinPoly fpd (FreeFinPoly fpd a)) ->
    ProductN pow (FreeFinPoly fpd a)
  finPolyJoinN {pow=Z} () = ()
  finPolyJoinN {pow=(S pow)} (x, p) = (finPolyJoin x, finPolyJoinN {pow} p)

  public export
  finPolyJoinFunc : {fpd, fpd' : FinPolyData} -> {0 a : Type} ->
    FinPolyFunc fpd (FreeFinPoly fpd' (FreeFinPoly fpd' a)) ->
    FinPolyFunc fpd (FreeFinPoly fpd' a)
  finPolyJoinFunc {fpd=[]} {fpd'} v = void v
  finPolyJoinFunc {fpd=((coeff, pow) :: terms)} {fpd'} poly = case poly of
    Left fields => Left $ finPolyJoinN . fields
    Right poly' => Right $ finPolyJoinFunc poly'
 -}

------------------------------------------
---- Potentially-infinite polynomials ----
------------------------------------------

public export
PolyData : Type
PolyData = List (Type, Type)

public export
PolyDFunc : PolyData -> (Type -> Type)
PolyDFunc [] _ = Void
PolyDFunc ((coeff, rep) :: l) ty =
  Either (coeff, CovarHomFunc rep ty) (PolyDFunc l ty)

public export
DirichFunc : PolyData -> (Type -> Type)
DirichFunc [] _ = Void
DirichFunc ((coeff, rep) :: l) ty =
  Either (coeff, ContravarHomFunc rep ty) (DirichFunc l ty)

-------------------------
-------------------------
----- Kan extensions ----
-------------------------
-------------------------

-- `FunctorExp j a` is sometimes written `j ^ a`.
-- Note that `FunctorExp j a` can be read as
-- `CovarHomFunc a . j`.
public export
FunctorExp : (Type -> Type) -> Type -> Type -> Type
FunctorExp = (|>) CovarHomFunc . (|>)

public export
Functor f => Profunctor (FunctorExp f) where
  dimap mca mbd coalg = map {f} mbd . coalg . mca

-- The right Kan extension of `g` along `j` (sometimes written `g/j`).
-- (Note that `RKanExt j g a` can be read as the set of natural transformations
-- from `FunctorExp j a` to `g`.)
public export
RKanExt : (j, g : Type -> Type) -> Type -> Type
RKanExt j g = flip NaturalTransformation g . FunctorExp j

-- Note that `ExpFunctor j a` can be read as
-- `ContravarHomFunc a . j`.
public export
ExpFunctor : (Type -> Type) -> Type -> Type -> Type
ExpFunctor j a b = j b -> a

public export
Functor f => Profunctor (flip $ ExpFunctor f) where
  dimap mca mbd alg = mbd . alg . map {f} mca

-- The left Kan extension of `g` along `j`.
public export
LKanExt : (j, g : Type -> Type) -> Type -> Type
LKanExt j g a = (b : Type ** (ExpFunctor j a b, g b))

---------------------------------------
---------------------------------------
---- Yoneda variants / corollaries ----
---------------------------------------
---------------------------------------

-- For this and the following optics, see "What You Needa Know About Yoneda"
-- by Boisseau and Gibbons (I have added one or two duals that they didn't
-- explicitly mention).

public export
record Yo (f : Type -> Type) (a : Type) where
  constructor MkYo
  YoEmbed : RKanExt Prelude.id f a

public export
fromYo : {f : Type -> Type} -> {a : Type} -> Yo f a -> f a
fromYo {f} {a} (MkYo y) = y a id

public export
toYo : Functor f => {a : Type} -> f a -> Yo f a
toYo {f} {a} x = MkYo $ \ty, maty => map {f} maty x

public export
Functor (Yo f) where
  map mab (MkYo y) = MkYo $ \ty, mbty => y ty $ mbty . mab

public export
record ContraYo (f : Type -> Type) (a : Type) where
  constructor MkContraYo
  ContraYoEmbed : NaturalTransformation (ContravarHomFunc a) f

public export
fromContraYo : {f : Type -> Type} -> {a : Type} -> ContraYo f a -> f a
fromContraYo {f} {a} (MkContraYo y) = y a id

public export
toContraYo : Contravariant f => {a : Type} -> f a -> ContraYo f a
toContraYo {f} {a} x = MkContraYo $ \ty, mtya => contramap {f} mtya x

public export
Contravariant (ContraYo f) where
  contramap mba (MkContraYo y) = MkContraYo $ \ty, mtyb => y ty $ mba . mtyb

public export
record CoYo (f : Type -> Type) (r : Type) where
  constructor MkCoYo
  CoYoEmbed : LKanExt Prelude.id f r -- `f` covariant
           -- LKanExt j g a = (b : Type ** (j b -> a, g b))
           -- LKanExt Prelude.id f r = (b : Type ** (b -> r, f b))

public export
fromCoYo : Functor f => CoYo f b -> f b
fromCoYo (MkCoYo (ty ** (h, x))) = map {f} h x

public export
toCoYo : Functor f => {b : Type} -> f b -> CoYo f b
toCoYo {b} y = MkCoYo (b ** (id, y))

public export
Functor (CoYo f) where
  map g (MkCoYo (ty ** (h, x))) = MkCoYo (ty ** (g . h, x))

public export
record ContraCoYo (f : Type -> Type) (r : Type) where
  constructor MkContraCoYo
  ContraCoYoEmbed : (b : Type ** (f b, r -> b)) -- `f` contravariant
 -- compare CoYo ~= (b : Type ** (f b, b -> r)) with `f` covariant

public export
fromContraCoYo : Contravariant f => ContraCoYo f b -> f b
fromContraCoYo (MkContraCoYo (ty ** (x, g))) = contramap {f} g x

public export
toContraCoYo : Contravariant f => {b : Type} -> f b -> ContraCoYo f b
toContraCoYo {b} y = MkContraCoYo (b ** (y, id))

public export
Contravariant (ContraCoYo f) where
  contramap g (MkContraCoYo (ty ** (x, h))) = MkContraCoYo (ty ** (x, h . g))

public export
record YoCopreshf (f : (Type -> Type) -> Type) (r : Type -> Type) where
  constructor MkYoC
  YoCEmbed : (b : Type -> Type) -> NaturalTransformation r b -> f b

public export
toYoC : (f : (Type -> Type) -> Type) ->
  {auto isF :
    (g, h : Type -> Type) -> NaturalTransformation g h -> f g -> f h} ->
  {r : Type -> Type} -> f r -> YoCopreshf f r
toYoC f {isF} {r} x = MkYoC $ \b, alpha => isF r b alpha x

public export
fromYoC : (f : (Type -> Type) -> Type) -> {r : Type -> Type} ->
  YoCopreshf f r -> f r
fromYoC f {r} (MkYoC y) = y r $ \_ => id

public export
record CoYoCopreshf (f : (Type -> Type) -> Type) (r : Type -> Type) where
  constructor MkCoYoC
  CoYoCEmbed : (b : Type -> Type ** (NaturalTransformation b r, f b))

public export
toCoYoC : (f : (Type -> Type) -> Type) ->
  {r : Type -> Type} -> f r -> CoYoCopreshf f r
toCoYoC f {r} x = MkCoYoC (r ** ((\_ => id), x))

public export
fromCoYoC : (f : (Type -> Type) -> Type) ->
  {isF : (g, h : Type -> Type) -> NaturalTransformation g h -> f g -> f h} ->
  {r : Type -> Type} ->
  CoYoCopreshf f r -> f r
fromCoYoC f {isF} {r} (MkCoYoC (b ** (alpha, x))) = isF b r alpha x

public export
ProYoEmbedding : ProfunctorSig -> ProfunctorSig
ProYoEmbedding p c d = ProfNT (PrePostPair c d) p

public export
record ProYo (p : ProfunctorSig) (c, d : Type) where
  constructor MkProYo
  -- An equivalent structure is called `Yoneda/runYoneda` in some Haskell
  -- libraries; this formulation makes the Yoneda-lemma instantiation more
  -- explicit, and in particular factors out the `PrePostPair` notion.
  ProYoEmbed : ProYoEmbedding p c d

public export
fromProYo : {p : ProfunctorSig} -> ProfNT (ProYo p) p
fromProYo {p} (MkProYo py) = py (id, id)

public export
toProYo : {p : ProfunctorSig} -> {isP : Profunctor p} -> ProfNT p (ProYo p)
toProYo {p} {isP} pxy = MkProYo $ \(con, cov) => dimap {f=p} con cov pxy

public export
Profunctor (ProYo p) where
  dimap mca mbd (MkProYo py) =
    MkProYo $ \(con, cov) => py (mca . con, cov . mbd)

public export
CoProYoEmbedding : ProfunctorSig -> Type -> Type -> (Type, Type) -> Type
CoProYoEmbedding p c d ab =
  (PrePostPair (fst ab) (snd ab) c d, p (fst ab) (snd ab))

public export
record CoProYo (p : ProfunctorSig) (c, d : Type) where
  constructor MkCoProYo
  -- An equivalent structure is called `CoYoneda` in some Haskell
  -- libraries; this formulation makes the (co-)Yoneda-lemma instantiation more
  -- explicit, and in particular factors out the `PrePostPair` notion.
  CoProYoEmbed : Exists {type=(Type, Type)} $ CoProYoEmbedding p c d

public export
fromCoProYo : {p : ProfunctorSig} -> {isP : Profunctor p} ->
  ProfNT (CoProYo p) p
fromCoProYo {p} {a} {b}
  (MkCoProYo (Evidence ab ((ca, bd), pab))) = dimap {f=p} ca bd pab

public export
toCoProYo : {p : ProfunctorSig} ->
  ProfNT p (CoProYo p)
toCoProYo {p} {a} {b} pab = MkCoProYo (Evidence (a, b) ((id, id), pab))

public export
Profunctor (CoProYo p) where
  dimap {a} {b} {c} {d} mca mbd (MkCoProYo (Evidence xy ((ax, yb), pxy))) =
    MkCoProYo (Evidence xy ((ax . mca, mbd . yb), pxy))

-- Profunctor-profunctor polymorphism:  the Yoneda lemma in the category
-- of profunctors on `Type`.
public export
record ProYoPreshf
    (pp : (ProfunctorSig) -> Type) (p : ProfunctorSig) where
  constructor MkProYoP
  ProYoPEmbed : (q : ProfunctorSig) ->
    {auto 0 _ : Profunctor q} -> ProfNT p q -> pp q

public export
toProYoP : (f : (ProfunctorSig) -> Type) ->
  {auto isF : ProfPreshfMap f} ->
  {r : ProfunctorSig} -> f r -> ProYoPreshf f r
toProYoP f {isF} {r} fr = MkProYoP $ \q, alpha => isF alpha fr

public export
fromProYoP : (f : (ProfunctorSig) -> Type) ->
  {r : ProfunctorSig} -> {auto isP : Profunctor r} ->
  ProYoPreshf f r -> f r
fromProYoP f {r} {isP} (MkProYoP py) = py r id

-- The existential dual of the preceding universal.
public export
record ProCoYoPreshf
    (pp : (ProfunctorSig) -> Type) (p : ProfunctorSig) where
  constructor MkProCoYoP
  ProCoYoPEmbed : (q : ProfunctorSig ** (Profunctor q, ProfNT q p, pp q))

public export
toProCoYoP :
  (f : (ProfunctorSig) -> Type) ->
  {r : ProfunctorSig} -> {auto isP : Profunctor r} ->
  f r -> ProCoYoPreshf f r
toProCoYoP f {r} {isP} fr = MkProCoYoP (r ** (isP, id, fr))

public export
fromProCoYoP :
  (f : (ProfunctorSig) -> Type) -> {auto isF : ProfPreshfMap f} ->
  {r : ProfunctorSig} ->
  ProCoYoPreshf f r -> f r
fromProCoYoP f {isF} {r} (MkProCoYoP (q ** (isPq, alpha, fq))) =
  isF alpha fq

public export
record DoubleYo (a, b : Type) where
  constructor MkDoubleYo
  DoubleYoEmbed : (f : Type -> Type) -> Functor f -> f a -> f b

public export
Profunctor DoubleYo where
  dimap mca mbd (MkDoubleYo y) =
    MkDoubleYo $ \f, isF, x => map {f} mbd $ y f isF $ map {f} mca x

public export
toDoubleYo : ProfNT HomProf DoubleYo
toDoubleYo m = MkDoubleYo $ \f, isF, x => map {f} m x

public export
fromDoubleYo : ProfNT DoubleYo HomProf
fromDoubleYo (MkDoubleYo y) = y id (MkFunctor id)

public export
record ContraDoubleYo (a, b : Type) where
  constructor MkContraDoubleYo
  ContraDoubleYoEmbed : (f : Type -> Type) -> Contravariant f -> f b -> f a

public export
Profunctor ContraDoubleYo where
  dimap mca mbd (MkContraDoubleYo y) =
    MkContraDoubleYo $
      \f, isCF, x => contramap {f} mca $ y f isCF $ contramap {f} mbd x

public export
toContraDoubleYo : ProfNT HomProf ContraDoubleYo
toContraDoubleYo m = MkContraDoubleYo $ \f, isCF, x => contramap {f} m x

public export
fromContraDoubleYo : ProfNT ContraDoubleYo HomProf
fromContraDoubleYo {a} {b} (MkContraDoubleYo y) =
  y (ContravarHomFunc b) (ContravarHomFuncContravar {a=b}) id

public export
record CoDoubleYo (a, b : Type) where
  constructor MkCoDoubleYo
  CoDoubleYoEmbed :
    (f : Type -> Type ** isF : Functor f **
    (NaturalTransformation f (CovarHomFunc a), f b))

public export
Profunctor CoDoubleYo where
  dimap mca mbd (MkCoDoubleYo (f ** MkFunctor fm ** (alpha, x))) =
    MkCoDoubleYo
      (f ** MkFunctor fm **
      (
      -- This is the vertical composition of the Yoneda embedding of `mca`
      -- after `alpha`.
      \x => (|>) mca . alpha x,
      fm mbd x))

public export
fromCoDoubleYo : ProfNT CoDoubleYo HomProf
fromCoDoubleYo {a} {b} (MkCoDoubleYo (f ** isF ** (alpha, x))) = alpha b x

public export
toCoDoubleYo : ProfNT HomProf CoDoubleYo
toCoDoubleYo {a} {b} m =
  MkCoDoubleYo
    (CovarHomFunc a **
     MkFunctor (map {f=(CovarHomFunc a)}) **
     ((\_ => id), m))

public export
record ContraCoDoubleYo (a, b : Type) where
  constructor MkContraCoDoubleYo
  ContraCoDoubleYoEmbed :
    (f : Type -> Type ** isF : Contravariant f **
    (NaturalTransformation f (ContravarHomFunc b), f a))

public export
Profunctor ContraCoDoubleYo where
  dimap mca mbd (MkContraCoDoubleYo (f ** fcontra ** (alpha, x))) =
    MkContraCoDoubleYo
      (f ** fcontra ** (\x => mbd .* alpha x, contramap {f} mca x))

public export
fromContraCoDoubleYo : ProfNT ContraCoDoubleYo HomProf
fromContraCoDoubleYo {a} {b} (MkContraCoDoubleYo (f ** isF ** (alpha, x))) =
  alpha a x

public export
toContraCoDoubleYo : ProfNT HomProf ContraCoDoubleYo
toContraCoDoubleYo {a} {b} m =
  MkContraCoDoubleYo
    (ContravarHomFunc b **
     ContravarHomFuncContravar {a=b} **
     ((\_ => id), m))

public export
record DoubleProYo (s, t, a, b : Type) where
  constructor MkDoubleProYo
  DoubleProYoEmbed : (0 p : ProfunctorSig) ->
    Profunctor p -> p s t -> p a b

public export
Profunctor (DoubleProYo s t) where
  dimap mca mbd (MkDoubleProYo y) =
    MkDoubleProYo $ \p, isP => dimap mca mbd . y p isP

public export
toDoubleProYo : {0 s, t : Type} ->
  ProfNT (PrePostPair s t) (DoubleProYo s t)
toDoubleProYo m = MkDoubleProYo $ \p, isP => dimap {f=p} (fst m) (snd m)

public export
fromDoubleProYo : {0 s, t : Type} ->
  ProfNT (DoubleProYo s t) (PrePostPair s t)
fromDoubleProYo {s} {t} {a} {b} (MkDoubleProYo py) =
  (py (ContravarHomAsPro s) ContravarHomPro id,
   py (CovarHomAsPro t) CovarHomPro id)

public export
record CoDoubleProYo (s, t, a, b : Type) where
  constructor MkCoDoubleProYo
  CoDoubleProYoEmbed :
    (p : ProfunctorSig ** isP : Profunctor p **
     (ProfNT p (PrePostPair s t), p a b))

public export
Profunctor (CoDoubleProYo s t) where
  dimap mca mbd (MkCoDoubleProYo (p ** MkProfunctor dm ** (alpha, pab))) =
    MkCoDoubleProYo (p ** MkProfunctor dm ** (alpha, dm mca mbd pab))

public export
fromCoDoubleProYo : {s, t : Type} ->
  ProfNT (CoDoubleProYo s t) (PrePostPair s t)
fromCoDoubleProYo (MkCoDoubleProYo (p ** isP ** (alpha, pab))) = alpha pab

public export
toCoDoubleProYo : {s, t : Type} ->
  ProfNT (PrePostPair s t) (CoDoubleProYo s t)
toCoDoubleProYo {s} {t} {a} {b} fp =
  MkCoDoubleProYo (PrePostPair s t ** PrePostPairProf ** (id, fp))

---------------------------
---------------------------
---- Profunctor optics ----
---------------------------
---------------------------

public export
ProfShape : Type
ProfShape = PfSliceObj

public export
record ProfOptic (sl : ProfShape) (a, b, s, t : Type) where
  constructor MkProfOptic
  opticP : (p : ProfunctorDP) -> sl p -> DPair.fst p a b -> DPair.fst p s t

public export
ConjoinShapes : ProfShape -> ProfShape -> ProfShape
ConjoinShapes s s' p = Pair (s p) (s' p)

public export
ProfOpticCompose : {sh, sh' : ProfShape} -> {a, b, c, d, s, t : Type} ->
  ProfOptic sh c d s t -> ProfOptic sh' a b c d ->
  ProfOptic (ConjoinShapes sh sh') a b s t
ProfOpticCompose (MkProfOptic pg) (MkProfOptic pf) =
  MkProfOptic $ \dp, sldp => pg dp (fst sldp) . pf dp (snd sldp)

public export
OpticSig : Type
OpticSig = Type -> Type -> Type -> Type -> Type

public export
ProfOpticDP : OpticSig
ProfOpticDP a b s t = (sl : PfSliceObj ** ProfOptic sl a b s t)

public export
FunctorDP : Type
FunctorDP = (f : Type -> Type ** Functor f)

public export
FShape : Type
FShape = SliceObj FunctorDP

public export
FShaped : FShape -> Type
FShaped fs = DPair FunctorDP fs

public export
ConcreteExOptic : FShape -> OpticSig
ConcreteExOptic fs a b s t =
  (f : Type -> Type ** isF : Functor f **
   isShaped : fs (f ** isF) ** Pair (s -> f a) (f b -> t))

public export
PFShaped : ProfShape -> Type
PFShaped pfs = DPair ProfunctorDP pfs

public export
ProfRespectsShape : FShape -> ProfShape
ProfRespectsShape fs (pf ** isP) =
  (f : Type -> Type) -> (isF : Functor f) -> fs (f ** isF) ->
  (a, b : Type) -> pf a b -> pf (f a) (f b)

public export
ExOpticP : FShape -> OpticSig
ExOpticP fs = ProfOptic (ProfRespectsShape fs)

public export
record ConcreteAdapter (a, b, s, t : Type) where
  constructor MkAdapter
  adaptFrom : s -> a
  adaptTo : b -> t

-- Profunctor version of adapter.
public export
PfAdapter : PfSliceObj
PfAdapter = PfCatObj

public export
AdapterP : OpticSig
AdapterP = ProfOptic PfAdapter

public export
record ConcreteLens (a, b, s, t : Type) where
  constructor MkLens
  lensview : s -> a
  lensupdate : Pair s b -> t

public export
CartesianP : PfSliceObj
CartesianP (p ** isP) =
  (a, b, c : Type) -> p a b -> p (Pair c a) (Pair c b)

public export
LensP : OpticSig
LensP = ProfOptic CartesianP

public export
record ConcretePrism (a, b, s, t : Type) where
  constructor MkPrism
  lensmatch : s -> Either t a
  lensbuild : b -> t

public export
CocartesianP : PfSliceObj
CocartesianP (p ** isP) =
  (a, b, c : Type) -> p a b -> p (Either c a) (Either c b)

public export
PrismP : OpticSig
PrismP = ProfOptic CocartesianP

public export
TraversalShape : FShape
TraversalShape (f ** isF) = Traversable f

public export
ConcreteTraversal : OpticSig
ConcreteTraversal = ConcreteExOptic TraversalShape

public export
TraversalP : OpticSig
TraversalP = ExOpticP TraversalShape

-----------------------
-----------------------
---- Continuations ----
-----------------------
-----------------------

-- Drawn from:
--  https://www.austinseipp.com/hs-asai/doc/Control-Delimited.html
--  https://hackage.haskell.org/package/kan-extensions-5.2.5/docs/Control-Monad-Codensity.html
--  https://www.semanticscholar.org/paper/Asymptotic-Improvement-of-Computations-over-Free-Voigtl%C3%A4nder/f25608a741652a4448afc6164856231f3565d517

public export
Continuation : Type -> Type
Continuation = Yo id

public export
CPSSig : (a, b : Type) -> Type
CPSSig a b = a -> Continuation b

public export
CPSTransformSig : (a, b : Type) -> Type
CPSTransformSig a b = (a -> b) -> CPSSig a b

public export
CPSTransform : {a, b : Type} -> CPSTransformSig a b
CPSTransform = (.) toYo

public export
record Delim (s, t, b : Type) where
  constructor MkDelim
  unDelim : (b -> s) -> t

public export
DelimNoAnsTypeMod : ProfunctorSig
DelimNoAnsTypeMod s b = Delim s s b

public export
PolyDelim : Type -> Type
PolyDelim b = (r : Type) -> DelimNoAnsTypeMod r b

-- PolyDelim is another way of getting to `Continuation`.
public export
PolyDelimToCont : {a : Type} -> PolyDelim a -> Continuation a
PolyDelimToCont f = MkYo $ \r => unDelim (f r)

public export
ContToPolyDelim : {a : Type} -> Continuation a -> PolyDelim a
ContToPolyDelim (MkYo f) r = MkDelim $ f r

public export
DelimEndo : ProfunctorSig
DelimEndo s t = Delim s t s

public export
DelimTrans : ProfunctorSig
DelimTrans a b =
  NaturalTransformation (flip DelimNoAnsTypeMod a) (flip DelimNoAnsTypeMod b)

public export
resetDelim : {s, t : Type} -> DelimEndo s t -> PolyDelim t
resetDelim {s} {t} (MkDelim {b=s} {s} {t} f) s' =
  MkDelim {s=s'} {t=s'} {b=t} $ \k : (t -> s') => k (f id)

public export
shift0 : {s, t, b : Type} -> ((b -> s) -> t) -> Delim s t b
shift0 = MkDelim

public export
shift1 : {a, b, s, t : Type} -> ((b -> s) -> Delim a t a) -> Delim s t b
shift1 f = shift0 (\k => unDelim (f k) id)

public export
DelimReturnI : {b, s : Type} -> b -> DelimNoAnsTypeMod s b
DelimReturnI x = MkDelim (\k : (b -> s) => k x)

public export
shift2 : {a, b, s, t : Type} ->
  ((b -> PolyDelim s) -> DelimEndo a t) -> Delim s t b
shift2 {a} {b} {s} {t} f =
  shift1 $
    \k : (b -> s) => f $ \x : b, r : Type => DelimReturnI {b=s} {s=r} $ k x

public export
callCC : {a, b, s, t, u : Type} ->
  ((b -> Delim u s a) -> Delim s t b) -> Delim s t b
callCC f = shift0 (\k => unDelim (f (\a => shift0 $ \_ => k a)) k)

public export
runDelim : {t : Type} -> Delim t t t -> t
runDelim (MkDelim f) = f id

-- One way of viewing the Codensity monad is that if `m` maps a type `a`
-- to a data structure containing free variables drawn from `a` -- for
-- example, if `m` is a free monad -- then a term of type `Codensity m a`
-- represents a term of type `m a` as a polymorphic function which substitutes
-- terms of type `m b` for some arbitrary type `b` into the free variables
-- of the term of type `m a`.
public export
record Codensity (m : Type -> Type) (a : Type) where
  constructor MkCodensity
  -- Codensity m a = (b : Type) -> (a -> m b) -> m b
  runCodensity : RKanExt m m a

-- `Codensity id` is the same as `Continuation`.
public export
CodensityIdToCont : {a : Type} -> Codensity Prelude.id a -> Continuation a
CodensityIdToCont (MkCodensity f) = MkYo f

public export
ContToCodensity : {a : Type} -> Continuation a -> Codensity Prelude.id a
ContToCodensity (MkYo f) = MkCodensity f

public export
CodensityFunctor : (f : Type -> Type) -> Functor (Codensity f)
CodensityFunctor f =
  MkFunctor
    (\fab, c => MkCodensity $ \ty, fbty => runCodensity c ty $ fbty . fab)

public export
CodensityApplicative : (f : Type -> Type) -> Applicative (Codensity f)
CodensityApplicative f =
  let _ = CodensityFunctor f in
  MkApplicative
    (\x => MkCodensity $ \ty, faty => faty x)
    (\cab, ca => MkCodensity $ \ty, fbty =>
      runCodensity cab ty $ \fab => runCodensity ca ty $ fbty . fab)

public export
CodensityMonad : (f : Type -> Type) -> Monad (Codensity f)
CodensityMonad f =
  let cda = CodensityApplicative f in
  MkMonad cmbind cmjoin
  where
    public export
    cmbind : Codensity f a -> (a -> Codensity f b) -> Codensity f b
    cmbind ca acb = MkCodensity $
      \ty, fbty => runCodensity ca ty $ \x => runCodensity (acb x) ty fbty

    public export
    cmjoin : Codensity f (Codensity f a) -> Codensity f a
    cmjoin = flip cmbind id

-- Also known as `rep`.
public export
MonadTrans Codensity where
  lift {m} {a} ma = MkCodensity $ \ty => (>>=) {m} {a} {b=ty} ma

public export
liftCodensity : Monad m => {a : Type} -> m a -> Codensity m a
liftCodensity {m} {a} = lift {t=Codensity} {m} {a}

-- Also known as `abs`.
public export
lowerCodensity : Applicative f => {a : Type} -> Codensity f a -> f a
lowerCodensity {f} {a} ca = runCodensity ca a $ pure {f}

public export
wrapCodensity :
  {m : Type -> Type} -> (NaturalTransformation m m) -> Codensity m ()
wrapCodensity f = MkCodensity $ \ty, k => f ty (k ())

public export
reset : Monad m => {a : Type} -> Codensity m a -> Codensity m a
reset = lift {m} {t=Codensity} . lowerCodensity {f=m}

public export
shift : Monad m => {a : Type} -> RKanExt m (Codensity m) a -> Codensity m a
shift {a} f = MkCodensity $ \y => lowerCodensity . f y

public export
interface (Functor f, Monad m) => FreeLike f m where
  constructor MkFreeLike
  total
  wrap : (a : Type) -> f (m a) -> m a

public export
FreeMonadFreeLike : {f : Type -> Type} -> Functor f ->
  {auto isM : Monad (FreeMonad f)} -> FreeLike f (FreeMonad f)
FreeMonadFreeLike isF {isM} = MkFreeLike $ \a, x => InFree $ TFC x

public export
CodensityFreeLike : {f, m : Type -> Type} ->
  FreeLike f m -> FreeLike f (Codensity m)
CodensityFreeLike {f} {m} (MkFreeLike wrapm) =
  let _ = CodensityFunctor f in
  let _ = CodensityMonad m in
  MkFreeLike $ \a, fca => MkCodensity $ \ty, maty =>
      wrapm ty $ map {f} {a=(Codensity m a)} {b=(m ty)}
        (\ca => runCodensity ca ty maty) fca

public export
improve : {f : Type -> Type} -> Functor f ->
  {a : Type} -> ((m : Type -> Type) -> FreeLike f m -> m a) ->
  {auto isM : Monad (FreeMonad f)} -> FreeMonad f a
improve {f} isF allWrap {isM} =
  lowerCodensity $ lift $ allWrap (FreeMonad f) (FreeMonadFreeLike isF)

-------------------------
-------------------------
---- Density comonad ----
-------------------------
-------------------------

public export
record Density (m : Type -> Type) (a : Type) where
  constructor MkDensity
  -- Density m a = (b : Type ** Pair (m b -> a) (m b))
  runDensity : LKanExt m m a

public export
mapDensity : (0 f : Type -> Type) -> {0 isF : Functor f} -> {0 a, b : Type} ->
  (m : a -> b) -> Density f a -> Density f b
mapDensity f {isF} m (MkDensity (b' ** (k, x))) = MkDensity (b' ** (m . k, x))

public export
DensityFunctor : (0 f : Type -> Type) -> {0 isF : Functor f} ->
  Functor (Density f)
DensityFunctor f {isF} = MkFunctor $ mapDensity f {isF}

public export
(isF : Functor f) => Functor (Density f) where
  map {f} {isF} = mapDensity f {isF}

public export
eraseDensity : (0 f : Type -> Type) -> {0 a : Type} -> Density f a -> a
eraseDensity f {a} (MkDensity (b' ** (k, x))) = k x

public export
duplicateDensity : (0 f : Type -> Type) -> {0 a : Type} ->
  Density f a -> Density f (Density f a)
duplicateDensity f {a} (MkDensity (b ** (k, x))) =
  MkDensity (b ** (MkDensity . MkDPair b . MkPair k, x))

public export
extendDensity : (0 f : Type -> Type) -> {isF : Functor f} -> {0 a, b : Type} ->
  (Density f a -> b) -> Density f a -> Density f b
extendDensity f {isF} {a} m = map {f=(Density f)} m . duplicateDensity f

public export
joinDensity : (0 f : Type -> Type) -> {0 isF : Functor f} -> {0 a : Type} ->
  Density f (Density f a) -> Density f a
joinDensity f {isF} {a} =
  let _ = DensityFunctor f {isF} in
  map {f=(Density f)} (eraseDensity f {a})

----------------------------
----------------------------
---- Closure conversion ----
----------------------------
----------------------------

-- This closure-conversion algorithm uses the contravariant co-Yoneda
-- lemma with a particular contravariant functor (presheaf); see
-- https://prl.ccs.neu.edu/blog/2017/08/28/closure-conversion-as-coyoneda/

public export
Closure : ProfunctorSig
Closure a b = (r : Type ** Pair r (Pair r a -> b))

public export
ClosureConversionSig : (a, b : Type) -> Type
ClosureConversionSig a b = (a -> b) -> Closure a b

public export
ClosureConversionF : Type -> ProfunctorSig
ClosureConversionF a b d = Pair d a -> b

public export
[ClosureConversionContravariant] Contravariant (ClosureConversionF a b) where
  contramap fab fbdb (x', x) = fbdb (fab x', x)

public export
ClosureConversionContra :
  (a, b : Type) -> Contravariant (ClosureConversionF a b)
ClosureConversionContra a b = ClosureConversionContravariant

public export
closureConvert : {a, b : Type} -> ClosureConversionSig a b
closureConvert {a} {b} m =
  let isC = ClosureConversionContra a b in
  let y = toContraCoYo {f=(ClosureConversionF a b)} {b=Unit} (m . snd) in
  let (r ** (f, c)) = ContraCoYoEmbed y in
  (r ** (c (), f))

--------------------
--------------------
---- Core types ----
--------------------
--------------------

------------------------------------------------------------
---- Non-terminating attempt at Nat-indexed hom-functor ----
------------------------------------------------------------

public export
NatCovarHomFunc : Type -> Type
NatCovarHomFunc = CovarHomFunc Nat

public export
FreeNatCovar : Type -> Type
FreeNatCovar = FreeMonad NatCovarHomFunc

{-
mutual
  public export
  cataNatCovar : FreeFEval NatCovarHomFunc
  cataNatCovar v a subst alg (InFree x) = case x of
    TFV var => subst var
    TFC com => alg $ (cataNatCovar v a subst alg) . com
    -}

public export
FinRepHomFunc : Nat -> Type -> Type
FinRepHomFunc n = \ty => MuFinCovar n -> ty

-------------------------
---- Natural numbers ----
-------------------------

public export
data NatF : Type -> Type where
  ZeroF : NatF carrier
  SuccF : carrier -> NatF carrier

public export
Functor NatF where
  map _ ZeroF = ZeroF
  map f (SuccF n) = SuccF $ f n

public export
Show carrier => Show (NatF carrier) where
  show ZeroF = "0"
  show (SuccF n) = "S(" ++ show n ++ ")"

public export
NatAlg : Type -> Type
NatAlg = Algebra NatF

public export
FreeNat : Type -> Type
FreeNat = FreeMonad NatF

public export
MuNat : Type
MuNat = Mu NatF

public export
NatCoalg : Type -> Type
NatCoalg = Coalgebra NatF

public export
CofreeNat : Type -> Type
CofreeNat = CofreeComonad NatF

public export
NuNat : Type
NuNat = Nu NatF

public export
freeEvalNatF : FreeFEval NatF
freeEvalNatF v a subst alg (InFree x) = case x of
  TFV var => subst var
  TFC n => alg $ case n of
    ZeroF => ZeroF
    SuccF n' => SuccF $ freeEvalNatF v a subst alg n'

public export
interpNatFAlg : NatAlg Nat
interpNatFAlg ZeroF = Z
interpNatFAlg (SuccF n) = S n

public export
interpFreeNatF : {v : Type} -> (subst : v -> Nat) -> FreeNat v -> Nat
interpFreeNatF {v} subst = freeEvalNatF v Nat subst interpNatFAlg

public export
interpMuNatF : MuNat -> Nat
interpMuNatF = interpFreeNatF {v=Void} (voidF Nat)

public export
showNatFAlg : NatAlg String
showNatFAlg = show

public export
showFreeNatF : {v : Type} -> (subst : v -> String) -> FreeNat v -> String
showFreeNatF {v} subst = freeEvalNatF v String subst showNatFAlg

public export
showMuNatF : MuNat -> String
showMuNatF = show . interpMuNatF

public export
NatFZ : FreeMonad NatF a
NatFZ = InFree $ TFC ZeroF

public export
NatFS : FreeMonad NatF a -> FreeMonad NatF a
NatFS = InFree . TFC . SuccF

public export
cataNatF : Catamorphism NatF
cataNatF = cataFromEval freeEvalNatF

public export
natJoin : {a : Type} -> FreeNat (FreeNat a) -> FreeNat a
natJoin = freeFJoin freeEvalNatF

public export
natEvalGen : FreeFEvalGen NatF
natEvalGen = freeEvalToGen {f=NatF} freeEvalNatF

public export
parseMuNatF : Nat -> MuNat
parseMuNatF Z = NatFZ
parseMuNatF (S n) = NatFS $ parseMuNatF n

---------------------------------------
---- Natural numbers as a category ----
---------------------------------------

public export
ProductMNatF : Type -> Type
ProductMNatF = ProductMonad . NatF

public export
NTToProductMNatF : (Type -> Type) -> Type
NTToProductMNatF f = NaturalTransformation f ProductMNatF

public export
pairZero : NTToProductMNatF NatF
pairZero ty = MkPair {a=(NatF ty)} {b=(NatF ty)} ZeroF

public export
pairSucc : NTToProductMNatF ProductMonad
pairSucc ty = map {f=ProductMonad} {a=ty} {b=(NatF ty)} SuccF

public export
data NatLTMorphF : MorphFunctor NatF where
  NatLTZ :
    {natCarrier : Type} -> {morphCarrier : MorphCarrier natCarrier} ->
    (n : NatF natCarrier) ->
    NatLTMorphF natCarrier morphCarrier (pairZero natCarrier n)
  NatLTS :
    {natCarrier : Type} -> {morphCarrier : MorphCarrier natCarrier} ->
    (mn : ProductMonad natCarrier) -> morphCarrier mn ->
    NatLTMorphF natCarrier morphCarrier (pairSucc natCarrier mn)

public export
data NatObj : Type where
  InNat : NatF NatObj -> NatObj

public export
NatOZ : NatObj
NatOZ = InNat ZeroF

public export
NatOS : NatObj -> NatObj
NatOS = InNat . SuccF

public export
NatO1 : NatObj
NatO1 = NatOS NatOZ

public export
NatO2 : NatObj
NatO2 = NatOS NatO1

public export
ProductMNatFObj : Type
ProductMNatFObj = ProductMNatF NatObj

public export
ProductMNatObj : Type
ProductMNatObj = ProductMonad NatObj

-- A natural transformation in the product category.
public export
inFreePN : ProductMonad (NatF NatObj) -> ProductMonad NatObj
inFreePN = map {f=ProductMonad} InNat

-------------------
---- Induction ----
-------------------

public export
NatObjIndBaseCase : (NatObj -> Type) -> Type
NatObjIndBaseCase p = p NatOZ

public export
NatObjInductionStep : (NatObj -> Type) -> Type
NatObjInductionStep p = (n' : NatObj) -> p n' -> p (NatOS n')

public export
NatObjInd :
  (0 p : NatObj -> Type) ->
  NatObjIndBaseCase p ->
  NatObjInductionStep p ->
  (n : NatObj) -> p n
NatObjInd p z s (InNat n) = case n of
  ZeroF => z
  SuccF n' => s n' $ NatObjInd p z s n'

public export
NatObjDepIndBaseCase :
  {p : NatObj -> Type} ->
  (dp : (n : NatObj) -> p n -> Type) ->
  (zp : NatObjIndBaseCase p) ->
  Type
NatObjDepIndBaseCase dp zp = dp NatOZ zp

public export
NatObjDepInductionStep :
  {p : NatObj -> Type} ->
  (dp : (n : NatObj) -> p n -> Type) ->
  (sp : NatObjInductionStep p) ->
  Type
NatObjDepInductionStep {p} dp sp =
  (n' : NatObj) -> (pn : p n') -> dp n' pn -> dp (NatOS n') (sp n' pn)

public export
NatObjDepInd :
  {p : NatObj -> Type} ->
  (dp : (n : NatObj) -> p n -> Type) ->
  {zp : NatObjIndBaseCase p} ->
  {sp : NatObjInductionStep p} ->
  NatObjDepIndBaseCase dp zp ->
  NatObjDepInductionStep dp sp ->
  (n : NatObj) -> dp n (NatObjInd p zp sp n)
NatObjDepInd {p} dp {zp} {sp} dzp dsp =
  NatObjInd (\n => dp n (NatObjInd p zp sp n))
    dzp (\n', dpn => dsp n' (NatObjInd p zp sp n') dpn)

public export
NatObjToMeta : NatObj -> Nat
NatObjToMeta = NatObjInd (const Nat) Z (const S)

public export
MetaToNatObj : Nat -> NatObj
MetaToNatObj Z = NatOZ
MetaToNatObj (S n) = NatOS (MetaToNatObj n)

public export
NatToMetaId : (n : NatObj) -> MetaToNatObj (NatObjToMeta n) = n
NatToMetaId = NatObjInd _ Refl $ \n, eq => rewrite eq in Refl

public export
MetaToNatId : (n : Nat) -> (NatObjToMeta (MetaToNatObj n)) = n
MetaToNatId Z = Refl
MetaToNatId (S n) = cong S $ MetaToNatId n

public export
NatObjToMetaInj : (m, n : NatObj) -> NatObjToMeta m = NatObjToMeta n -> m = n
NatObjToMetaInj m n eq =
  rewrite sym (NatToMetaId m) in
  rewrite sym (NatToMetaId n) in
  cong MetaToNatObj eq

public export
MetaToNatObjInj : (m, n : Nat) -> MetaToNatObj m = MetaToNatObj n -> m = n
MetaToNatObjInj m n eq =
  rewrite sym (MetaToNatId m) in
  rewrite sym (MetaToNatId n) in
  cong NatObjToMeta eq

public export
NatObjPredToNat : (NatObj -> Type) -> Nat -> Type
NatObjPredToNat p = p . MetaToNatObj

public export
NatPredToNatObj : (Nat -> Type) -> NatObj -> Type
NatPredToNatObj p = p . NatObjToMeta

public export
NatObjIndFromNat :
  (p : NatObj -> Type) ->
  (NatObjPredToNat p (NatObjToMeta NatOZ)) ->
  ((n' : NatObj) ->
   NatObjPredToNat p (NatObjToMeta n') ->
   NatObjPredToNat p (NatObjToMeta (NatOS n'))) ->
  (n : NatObj) -> p n
NatObjIndFromNat p z s (InNat n) = case n of
  ZeroF => z
  SuccF n' =>
    rewrite sym (NatToMetaId n') in
    s n' $ rewrite NatToMetaId n' in NatObjIndFromNat p z s n'

public export
NatIndFromNatObj :
  (p : Nat -> Type) ->
  (NatPredToNatObj p (MetaToNatObj Z)) ->
  ((n' : Nat) ->
   NatPredToNatObj p (MetaToNatObj n') ->
   NatPredToNatObj p (MetaToNatObj (S n'))) ->
  (n : Nat) -> p n
NatIndFromNatObj p z s n = case n of
  Z => z
  S n' =>
    rewrite sym (MetaToNatId n') in
    s n' $ rewrite MetaToNatId n' in NatIndFromNatObj p z s n'

public export
Show NatObj where
  show = show . NatObjToMeta

public export
NatObjPair : Type
NatObjPair = ProductMonad NatObj

public export
NatPair : Type
NatPair = ProductMonad Nat

public export
NatObjPairIndCurried :
  (p : NatObjPair -> Type) ->
  (p (NatOZ, NatOZ)) ->
  ((n' : NatObj) -> p (NatOZ, n') -> p (NatOZ, NatOS n')) ->
  ((n' : NatObj) -> p (n', NatOZ) -> p (NatOS n', NatOZ)) ->
  ((m', n' : NatObj) -> p (m', n') -> p (NatOS m', NatOS n')) ->
  (m, n : NatObj) -> p (m, n)
NatObjPairIndCurried p zz zs sz ss (InNat ZeroF) (InNat ZeroF) = zz
NatObjPairIndCurried p zz zs sz ss (InNat ZeroF) (InNat (SuccF n')) =
  zs n' $ NatObjPairIndCurried p zz zs sz ss (InNat ZeroF) n'
NatObjPairIndCurried p zz zs sz ss (InNat (SuccF m')) (InNat ZeroF) =
  sz m' $ NatObjPairIndCurried p zz zs sz ss m' (InNat ZeroF)
NatObjPairIndCurried p zz zs sz ss (InNat (SuccF m')) (InNat (SuccF n')) =
  ss m' n' $ NatObjPairIndCurried p zz zs sz ss m' n'

public export
NatObjPairIndZeroZeroCase : (NatObjPair -> Type) -> Type
NatObjPairIndZeroZeroCase p = p (NatOZ, NatOZ)

public export
NatObjPairIndZeroSuccCase : (NatObjPair -> Type) -> Type
NatObjPairIndZeroSuccCase p =
  (n' : NatObj) -> p (NatOZ, n') -> p (NatOZ, NatOS n')

public export
NatObjPairIndSuccZeroCase : (NatObjPair -> Type) -> Type
NatObjPairIndSuccZeroCase p =
  (n' : NatObj) -> p (n', NatOZ) -> p (NatOS n', NatOZ)

public export
NatObjPairIndSuccSuccCase : (NatObjPair -> Type) -> Type
NatObjPairIndSuccSuccCase p =
  (m', n' : NatObj) -> p (m', n') -> p (NatOS m', NatOS n')

public export
NatObjPairInd :
  (p : NatObjPair -> Type) ->
  NatObjPairIndZeroZeroCase p ->
  NatObjPairIndZeroSuccCase p ->
  NatObjPairIndSuccZeroCase p ->
  NatObjPairIndSuccSuccCase p ->
  (mn : NatObjPair) -> p mn
NatObjPairInd p zz zs sz ss (m, n) = NatObjPairIndCurried p zz zs sz ss m n

public export
NatObjPairDepZeroZeroCase :
  {p : NatObjPair -> Type} -> (dp : (np : NatObjPair) -> p np -> Type) ->
  (zzp : NatObjPairIndZeroZeroCase p) -> Type
NatObjPairDepZeroZeroCase dp zzp = dp (NatOZ, NatOZ) zzp

public export
NatObjPairDepZeroSuccCase :
  {p : NatObjPair -> Type} -> (dp : (np : NatObjPair) -> p np -> Type) ->
  NatObjPairIndZeroSuccCase p -> Type
NatObjPairDepZeroSuccCase {p} dp zsp =
  (n' : NatObj) -> (pzn : p (NatOZ, n')) -> dp (NatOZ, n') pzn ->
  dp (NatOZ, NatOS n') $ zsp n' pzn

public export
NatObjPairDepSuccZeroCase :
  {p : NatObjPair -> Type} -> (dp : (np : NatObjPair) -> p np -> Type) ->
  NatObjPairIndSuccZeroCase p -> Type
NatObjPairDepSuccZeroCase {p} dp szp =
  (n' : NatObj) -> (pnz : p (n', NatOZ)) -> dp (n', NatOZ) pnz ->
  dp (NatOS n', NatOZ) $ szp n' pnz

public export
NatObjPairDepSuccSuccCase :
  {p : NatObjPair -> Type} -> (dp : (np : NatObjPair) -> p np -> Type) ->
  NatObjPairIndSuccSuccCase p -> Type
NatObjPairDepSuccSuccCase {p} dp ssp =
  (n, n' : NatObj) -> (pnn : p (n, n')) -> dp (n, n') pnn ->
  dp (NatOS n, NatOS n') $ ssp n n' pnn

public export
NatObjPairDepInd :
  {p : NatObjPair -> Type} ->
  (dp : (np : NatObjPair) -> p np -> Type) ->
  {zzp : NatObjPairIndZeroZeroCase p} ->
  {zsp : NatObjPairIndZeroSuccCase p} ->
  {szp : NatObjPairIndSuccZeroCase p} ->
  {ssp : NatObjPairIndSuccSuccCase p} ->
  NatObjPairDepZeroZeroCase dp zzp ->
  NatObjPairDepZeroSuccCase dp zsp ->
  NatObjPairDepSuccZeroCase dp szp ->
  NatObjPairDepSuccSuccCase dp ssp ->
  (mn : NatObjPair) -> dp mn (NatObjPairInd p zzp zsp szp ssp mn)
NatObjPairDepInd {p} dp {zzp} {zsp} {szp} {ssp} dzzp dzsp dszp dssp =
  NatObjPairInd (\mn => dp mn (NatObjPairInd p zzp zsp szp ssp mn))
    dzzp
    (\n', dpzn => dzsp n' (NatObjPairInd p zzp zsp szp ssp (NatOZ, n')) dpzn)
    (\n', dpnz => dszp n' (NatObjPairInd p zzp zsp szp ssp (n', NatOZ)) dpnz)
    (\n, n', dpnn => dssp n n' (NatObjPairInd p zzp zsp szp ssp (n, n')) dpnn)

public export
NatObjPairToMeta : NatObjPair -> NatPair
NatObjPairToMeta = map {f=ProductMonad} NatObjToMeta

public export
NatMetaPairToObj : NatPair -> NatObjPair
NatMetaPairToObj = map {f=ProductMonad} MetaToNatObj

public export
NatPairToMetaId :
  (mn : NatObjPair) -> NatMetaPairToObj (NatObjPairToMeta mn) = mn
NatPairToMetaId (m, n) =
  rewrite NatToMetaId m in
  rewrite NatToMetaId n in
  Refl

public export
MetaToNatPairId :
  (mn : NatPair) -> NatObjPairToMeta (NatMetaPairToObj mn) = mn
MetaToNatPairId (m, n) =
  rewrite MetaToNatId m in
  rewrite MetaToNatId n in
  Refl

public export
NatObjPairPredToNat : (NatObjPair -> Type) -> NatPair -> Type
NatObjPairPredToNat p = p . NatMetaPairToObj

public export
NatPairPredToNatObj : (NatPair -> Type) -> NatObjPair -> Type
NatPairPredToNatObj p = p . NatObjPairToMeta

public export
DecEq NatObj where
  decEq m n with (decEq (NatObjToMeta m) (NatObjToMeta n))
    decEq m n | Yes eq = Yes $
      rewrite sym (NatToMetaId m) in
      rewrite sym (NatToMetaId n) in
      cong MetaToNatObj eq
    decEq m n | No neq = No $ \eq => case eq of Refl => neq Refl

public export
Eq NatObj where
  m == m' = case decEq m m' of
    Yes _ => True
    No _ => False

public export
NatObjPairIndFromNat :
  (p : NatObjPair -> Type) ->
  (NatObjPairPredToNat p (NatObjPairToMeta (NatOZ, NatOZ))) ->
  ((n' : NatObj) ->
   NatObjPairPredToNat p (NatObjPairToMeta (NatOZ, n')) ->
   NatObjPairPredToNat p (NatObjPairToMeta (NatOZ, NatOS n'))) ->
  ((n' : NatObj) ->
   NatObjPairPredToNat p (NatObjPairToMeta (n', NatOZ)) ->
   NatObjPairPredToNat p (NatObjPairToMeta (NatOS n', NatOZ))) ->
  ((m', n' : NatObj) ->
   NatObjPairPredToNat p (NatObjPairToMeta (m', n')) ->
   NatObjPairPredToNat p (NatObjPairToMeta (NatOS m', NatOS n'))) ->
  (m, n : NatObj) -> p (m, n)
NatObjPairIndFromNat p zz zs sz ss (InNat ZeroF) (InNat ZeroF) =
  zz
NatObjPairIndFromNat p zz zs sz ss (InNat ZeroF) (InNat $ SuccF n') =
  rewrite sym (NatPairToMetaId (NatOZ, InNat $ SuccF n')) in
  zs n' $
    rewrite NatPairToMetaId (NatOZ, n') in
    NatObjPairIndFromNat p zz zs sz ss (InNat ZeroF) n'
NatObjPairIndFromNat p zz zs sz ss (InNat $ SuccF m') (InNat ZeroF) =
  rewrite sym (NatPairToMetaId (InNat $ SuccF m', NatOZ)) in
  sz m' $
    rewrite NatPairToMetaId (m', NatOZ) in
    NatObjPairIndFromNat p zz zs sz ss m' (InNat ZeroF)
NatObjPairIndFromNat p zz zs sz ss (InNat $ SuccF m') (InNat $ SuccF n') =
  rewrite sym (NatPairToMetaId (InNat $ SuccF m', InNat $ SuccF n')) in
  ss m' n' $
    rewrite NatPairToMetaId (m', n') in
    NatObjPairIndFromNat p zz zs sz ss m' n'

public export
NatPairIndFromNatObj :
  (p : NatPair -> Type) ->
  (NatPairPredToNatObj p (NatMetaPairToObj (Z, Z))) ->
  ((n' : Nat) ->
   NatPairPredToNatObj p (NatMetaPairToObj (Z, n')) ->
   NatPairPredToNatObj p (NatMetaPairToObj (Z, S n'))) ->
  ((n' : Nat) ->
   NatPairPredToNatObj p (NatMetaPairToObj (n', Z)) ->
   NatPairPredToNatObj p (NatMetaPairToObj (S n', Z))) ->
  ((m', n' : Nat) ->
   NatPairPredToNatObj p (NatMetaPairToObj (m', n')) ->
   NatPairPredToNatObj p (NatMetaPairToObj (S m', S n'))) ->
  (m, n : Nat) -> p (m, n)
NatPairIndFromNatObj p zz zs sz ss Z Z =
  zz
NatPairIndFromNatObj p zz zs sz ss Z (S n') =
  rewrite sym (MetaToNatPairId (Z, S n')) in
  zs n' $
    rewrite MetaToNatPairId (Z, n') in
    NatPairIndFromNatObj p zz zs sz ss Z n'
NatPairIndFromNatObj p zz zs sz ss (S m') Z =
  rewrite sym (MetaToNatPairId (S m', Z)) in
  sz m' $
    rewrite MetaToNatPairId (m', Z) in
    NatPairIndFromNatObj p zz zs sz ss m' Z
NatPairIndFromNatObj p zz zs sz ss (S m') (S n') =
  rewrite sym (MetaToNatPairId (S m', S n')) in
  ss m' n' $
    rewrite MetaToNatPairId (m', n') in
    NatPairIndFromNatObj p zz zs sz ss m' n'

public export
MapAlg : (Type -> Type) -> ProfunctorSig
MapAlg f x v = (v -> x) -> f v -> x

public export
mapAlg : {0 f : Type -> Type} -> Functor f => {0 x, v : Type} ->
  Algebra f x ->
  MapAlg f x v
mapAlg alg m = alg . map {f} m

public export
MapAlgF : (Type -> Type) -> Type -> Type
MapAlgF f x = (v : Type) -> MapAlg f x v

public export
mapAlgF : {0 f : Type -> Type} -> Functor f => {0 x : Type} ->
  Algebra f x ->
  MapAlgF f x
mapAlgF alg v = mapAlg {v} alg

public export
FunctorIter : (Type -> Type) -> NatObj -> Type -> Type
FunctorIter f n a = NatObjInd (const Type) a (const f) n

public export
FunctorIterIndBaseCase : {f : Type -> Type} -> {a : Type} ->
  (p : (n' : NatObj) -> FunctorIter f n' a -> Type) -> Type
FunctorIterIndBaseCase {a} p = (z : a) -> p NatOZ z

public export
FunctorIterInductionStep : {f : Type -> Type} -> {a : Type} ->
  (p : (n' : NatObj) -> FunctorIter f n' a -> Type) -> Type
FunctorIterInductionStep {f} {a} p =
  (n' : NatObj) ->
   ((ty : FunctorIter f n' a) -> p n' ty) ->
   ((ty : f (FunctorIter f n' a)) -> p (NatOS n') ty)

public export
FunctorIterInd : {0 f : Type -> Type} -> {0 a : Type} ->
  (0 p : (n' : NatObj) -> FunctorIter f n' a -> Type) ->
  FunctorIterIndBaseCase {f} {a} p ->
  FunctorIterInductionStep {f} {a} p ->
  (n : NatObj) -> (ty : FunctorIter f n a) -> p n ty
FunctorIterInd {f} {a} p =
  NatObjInd (\n' => (ty : FunctorIter f n' a) -> p n' ty)

public export
FunctorIterMapAlg : (Type -> Type) -> ProfunctorSig
FunctorIterMapAlg f x v = (v -> x) -> (n : NatObj) -> FunctorIter f n v -> x

public export
functorIterMapAlg :
  {0 f : Type -> Type} -> Functor f => {0 v, x : Type} ->
  Algebra f x ->
  FunctorIterMapAlg f x v
functorIterMapAlg {f} {x} {v} alg m =
  FunctorIterInd (\_, _ => x) m $ \n => mapAlg alg

public export
FunctorIterMapAlgF : (Type -> Type) -> Type -> Type
FunctorIterMapAlgF f x = (v : Type) -> FunctorIterMapAlg f x v

public export
functorIterMapAlgF :
  {0 f : Type -> Type} -> Functor f => {0 x : Type} ->
  Algebra f x ->
  FunctorIterMapAlgF f x
functorIterMapAlgF alg v = functorIterMapAlg {v} alg

public export
FunctorIterAlg : (Type -> Type) -> Type -> Type
FunctorIterAlg f a = (n : NatObj) -> Algebra (FunctorIter f n) a

public export
FunctorIterAlgF : (Type -> Type) -> Type
FunctorIterAlgF f = (a : Type) -> FunctorIterAlg f a

public export
functorIterAlg :
  {0 f : Type -> Type} -> Functor f => {0 x : Type} ->
  Algebra f x ->
  FunctorIterAlg f x
functorIterAlg {f} {x} alg = functorIterMapAlg {v=x} alg id

public export
functorIterMap :
  {0 f : Type -> Type} -> Functor f =>
  {0 a, b : Type} ->
  (n : NatObj) -> (a -> b) -> FunctorIter f n a -> FunctorIter f n b
functorIterMap {f} {b} n m =
    FunctorIterInd (\n', _ => FunctorIter f n' b) m (\n' => map {f}) n

public export
(n : NatObj) => Functor f => Functor (FunctorIter f n) where
  map m {n} = functorIterMap n m

public export
functorIterShow : {0 f : Type -> Type} -> {0 a : Type} -> Functor f => Show a =>
  (sf : Algebra f String) -> (n : NatObj) -> (ty : FunctorIter f n a) -> String
functorIterShow {f} {a} sf = functorIterMapAlg {v=a} {x=String} sf show

public export
Functor f => Show a => Show (f String) => (n : NatObj) =>
    Show (FunctorIter f n a) where
  show {f} {a} {n} = functorIterShow {f} {a} show n

public export
FunctorIterDepIndBaseCase : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> FunctorIter f n' a -> Type} ->
  ((n' : NatObj) -> (it : FunctorIter f n' a) -> p n' it -> Type) ->
  FunctorIterIndBaseCase {f} {a} p ->
  Type
FunctorIterDepIndBaseCase {f} {a} {p} dp zp =
  (z : a) -> dp NatOZ z (zp z)

public export
FunctorIterDepInductionStep : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> FunctorIter f n' a -> Type} ->
  ((n' : NatObj) -> (it : FunctorIter f n' a) -> p n' it -> Type) ->
  FunctorIterInductionStep {f} {a} p ->
  Type
FunctorIterDepInductionStep {f} {a} {p} dp sp =
  (n' : NatObj) ->
   (pty : ((ty : FunctorIter f n' a) -> p n' ty)) ->
   (dephyp : (ty : FunctorIter f n' a) -> dp n' ty (pty ty)) ->
   ((ty : f (FunctorIter f n' a)) -> dp (NatOS n') ty (sp n' pty ty))

public export
FunctorIterDepInd : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> FunctorIter f n' a -> Type} ->
  (dp : (n' : NatObj) -> (it : FunctorIter f n' a) -> p n' it -> Type) ->
  {zp : FunctorIterIndBaseCase {f} {a} p} ->
  {sp : FunctorIterInductionStep {f} {a} p} ->
  FunctorIterDepIndBaseCase {f} {a} {p} dp zp ->
  FunctorIterDepInductionStep {f} {a} {p} dp sp ->
  (n : NatObj) -> (ty : FunctorIter f n a) ->
  dp n ty (FunctorIterInd {f} {a} p zp sp n ty)
FunctorIterDepInd {f} {a} {p} dp {zp} {sp} dzp dsp =
  FunctorIterInd {f} {a}
    (\n', ty => dp n' ty (FunctorIterInd {f} {a} p zp sp n' ty))
    dzp
    (\n => dsp n (FunctorIterInd {f} {a} p zp sp n))

public export
data OmegaStep : (Type -> Type) -> Type -> Type where
  OmegaInj : carrier -> OmegaStep f carrier
  OmegaIter : f carrier -> OmegaStep f carrier

public export
omegaStepElim :
  {0 f : Type -> Type} -> {0 a : Type} -> {0 b : OmegaStep f a -> Type} ->
  ((x : a) -> b (OmegaInj x)) ->
  ((fx : f a) -> b (OmegaIter fx)) ->
  (x : OmegaStep f a) -> b x
omegaStepElim {f} {a} {b} elimInj elimIter (OmegaInj x) = elimInj x
omegaStepElim {f} {a} {b} elimInj elimIter (OmegaIter fx) = elimIter fx

public export
OmegaMapAlg : (Type -> Type) -> ProfunctorSig
OmegaMapAlg f x v = (v -> x) -> OmegaStep f v -> x

public export
omegaMapAlg :
  {0 f : Type -> Type} -> Functor f => {0 x, v : Type} ->
  (f x -> x) ->
  OmegaMapAlg f x v
omegaMapAlg alg carrier = omegaStepElim carrier $ mapAlg alg carrier

public export
OmegaMapAlgF : (Type -> Type) -> Type -> Type
OmegaMapAlgF f x = (v : Type) -> OmegaMapAlg f x v

public export
omegaMapAlgF :
  {0 f : Type -> Type} -> Functor f => {0 x : Type} ->
  (f x -> x) ->
  OmegaMapAlgF f x
omegaMapAlgF alg v = omegaMapAlg {v} alg

public export
OmegaAlg : (Type -> Type) -> Type -> Type
OmegaAlg f a = Algebra (OmegaStep f) a

public export
omegaAlg :
  {0 f : Type -> Type} -> Functor f => {0 x : Type} ->
  Algebra f x ->
  OmegaAlg f x
omegaAlg {f} {x} alg = omegaMapAlg {v=x} alg id

public export
omegaStepMap :
  {0 f : Type -> Type} -> Functor f =>
  {0 a, b : Type} ->
  (a -> b) -> OmegaStep f a -> OmegaStep f b
omegaStepMap m = omegaStepElim (OmegaInj . m) (OmegaIter . map m)

public export
Functor f => Functor (OmegaStep f) where
  map = omegaStepMap

public export
omegaStepShow : {0 f : Type -> Type} -> {0 a : Type} -> Functor f => Show a =>
  Algebra f String -> OmegaStep f a -> String
omegaStepShow {f} {a} fAlg = omegaMapAlg {f} {x=String} {v=a} fAlg show

public export
Functor f => Show a => Show (f String) => Show (OmegaStep f a) where
  show = omegaStepShow show

public export
OmegaChain : (Type -> Type) -> NatObj -> Type -> Type
OmegaChain = FunctorIter . OmegaStep

public export
ChainIndBaseCase : {f : Type -> Type} -> {a : Type} ->
  (p : (n' : NatObj) -> OmegaChain f n' a -> Type) -> Type
ChainIndBaseCase {f} = FunctorIterIndBaseCase {f=(OmegaStep f)}

public export
ChainInductionStep : {f : Type -> Type} -> {a : Type} ->
  (p : (n' : NatObj) -> OmegaChain f n' a -> Type) -> Type
ChainInductionStep {f} = FunctorIterInductionStep {f=(OmegaStep f)}

public export
ChainInduction : {0 f : Type -> Type} -> {0 a : Type} ->
  (0 p : (n' : NatObj) -> OmegaChain f n' a -> Type) ->
  ChainIndBaseCase {f} {a} p ->
  ChainInductionStep {f} {a} p ->
  (n : NatObj) -> (ty : OmegaChain f n a) -> p n ty
ChainInduction {f} = FunctorIterInd {f=(OmegaStep f)}

public export
ChainMapAlg : (Type -> Type) -> ProfunctorSig
ChainMapAlg f x v = (v -> x) -> (n : NatObj) -> OmegaChain f n v -> x

public export
chainMapAlg :
  {0 f : Type -> Type} -> Functor f => {0 x, v : Type} ->
  Algebra f x ->
  ChainMapAlg f x v
chainMapAlg {f} {x} alg m =
  ChainInduction (\_, _ => x) m $ \_ => omegaMapAlg alg

public export
ChainMapAlgF : (Type -> Type) -> Type -> Type
ChainMapAlgF f x = (v : Type) -> ChainMapAlg f x v

public export
chainMapAlgF :
  {0 f : Type -> Type} -> Functor f => {0 x : Type} ->
  Algebra f x ->
  ChainMapAlgF f x
chainMapAlgF alg v = chainMapAlg {v} alg

public export
ChainAlg : (Type -> Type) -> Type -> Type
ChainAlg f a = (n : NatObj) -> Algebra (OmegaChain f n) a

public export
ChainAlgF : (Type -> Type) -> Type
ChainAlgF f = (a : Type) -> ChainAlg f a

public export
chainAlg :
  {0 f : Type -> Type} -> Functor f => {0 x : Type} ->
  Algebra f x ->
  ChainAlg f x
chainAlg {f} {x} alg = chainMapAlg {v=x} alg id

public export
omegaChainMap : {0 f : Type -> Type} -> Functor f => {0 a, b : Type} ->
  (m : a -> b) -> (n : NatObj) -> OmegaChain f n a -> OmegaChain f n b
omegaChainMap {f} m =
  ChainInduction (\n', _ => OmegaChain f n' b) m (\n' => map {f=(OmegaStep f)})

public export
(n : NatObj) => Functor f => Functor (OmegaChain f n) where
  map {n} {f} m = omegaChainMap {f} m n

public export
omegaChainShow : {0 f : Type -> Type} -> {0 a : Type} -> Functor f => Show a =>
  (sf : Algebra f String) -> (n : NatObj) -> (ty : OmegaChain f n a) -> String
omegaChainShow {f} {a} sf = chainMapAlg {v=a} {x=String} sf show

public export
Functor f => Show a => Show (f String) => (n : NatObj) =>
    Show (OmegaChain f n a) where
  show {f} {a} {n} = omegaChainShow {f} {a} show n

public export
ChainDepIndBaseCase : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> OmegaChain f n' a -> Type} ->
  ((n' : NatObj) -> (it : OmegaChain f n' a) -> p n' it -> Type) ->
  ChainIndBaseCase {f} {a} p ->
  Type
ChainDepIndBaseCase {f} = FunctorIterDepIndBaseCase {f=(OmegaStep f)}

public export
ChainDepInductionStep : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> OmegaChain f n' a -> Type} ->
  ((n' : NatObj) -> (it : OmegaChain f n' a) -> p n' it -> Type) ->
  ChainInductionStep {f} {a} p ->
  Type
ChainDepInductionStep {f} = FunctorIterDepInductionStep {f=(OmegaStep f)}

public export
ChainDepInd : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> OmegaChain f n' a -> Type} ->
  (dp : (n' : NatObj) -> (it : OmegaChain f n' a) -> p n' it -> Type) ->
  {zp : ChainIndBaseCase {f} {a} p} ->
  {sp : ChainInductionStep {f} {a} p} ->
  ChainDepIndBaseCase {f} {a} {p} dp zp ->
  ChainDepInductionStep {f} {a} {p} dp sp ->
  (n : NatObj) -> (ty : OmegaChain f n a) ->
  dp n ty (ChainInduction {f} {a} p zp sp n ty)
ChainDepInd {f} = FunctorIterDepInd {f=(OmegaStep f)}

public export
OmegaInjN : {f : Type -> Type} -> {a : Type} ->
  (n : NatObj) -> (x : a) -> OmegaChain f n a
OmegaInjN {f} {a} n x =
  NatObjInd (\n' => OmegaChain f n' a) x (\_ => OmegaInj) n

public export
OmegaN : {f : Type -> Type} -> Functor f => {a : Type} ->
  {n : NatObj} -> FunctorIter f n a -> OmegaChain f n a
OmegaN {f} {a} {n} =
  NatObjInd (\n' => FunctorIter f n' a -> OmegaChain f n' a)
    id
    (\n', hyp => OmegaIter . map {f} hyp)
    n

-- AKA free monad.
public export
OmegaColimit : (Type -> Type) -> Type -> Type
OmegaColimit f a = (n : NatObj ** OmegaChain f n a)

public export
PredColimitToChain : {f : Type -> Type} -> {a : Type} ->
  (OmegaColimit f a -> Type) ->
  ((n : NatObj) -> OmegaChain f n a -> Type)
PredColimitToChain p n ty = p (n ** ty)

public export
PredChainToColimit : {f : Type -> Type} -> {a : Type} ->
  ((n : NatObj) -> OmegaChain f n a -> Type) ->
  (OmegaColimit f a -> Type)
PredChainToColimit p (n ** ty) = p n ty

public export
ColimitIndBaseCase : {f : Type -> Type} -> {a : Type} ->
  (p : OmegaColimit f a -> Type) -> Type
ColimitIndBaseCase = ChainIndBaseCase . PredColimitToChain

public export
ColimitInductionStep : {f : Type -> Type} -> {a : Type} ->
  (p : OmegaColimit f a -> Type) -> Type
ColimitInductionStep = ChainInductionStep . PredColimitToChain

public export
ColimitInduction : {0 f : Type -> Type} -> {0 a : Type} ->
  (0 p : OmegaColimit f a -> Type) ->
  ColimitIndBaseCase {f} {a} p ->
  ColimitInductionStep {f} {a} p ->
  (ty : OmegaColimit f a) -> p ty
ColimitInduction p z s (n ** ty) =
  ChainInduction (PredColimitToChain p) z s n ty

-- AKA parameterized catamorphism.
public export
ColimitMapAlg : (Type -> Type) -> ProfunctorSig
ColimitMapAlg f x v = (v -> x) -> OmegaColimit f v -> x

public export
colimitMapAlg :
  {0 f : Type -> Type} -> {isF : Functor f} -> {0 x, v : Type} ->
  Algebra f x ->
  ColimitMapAlg f x v
colimitMapAlg alg m (n ** c) = chainMapAlg alg m n c

public export
ColimitMapAlgF : (Type -> Type) -> Type -> Type
ColimitMapAlgF f x = (v : Type) -> ColimitMapAlg f x v

public export
colimitMapAlgF :
  {0 f : Type -> Type} -> {isF : Functor f} -> {0 x : Type} ->
  Algebra f x ->
  ColimitMapAlgF f x
colimitMapAlgF {isF} alg v = colimitMapAlg {isF} {v} alg

public export
ColimitAlg : (Type -> Type) -> Type -> Type
ColimitAlg f a = Algebra (OmegaColimit f) a

public export
ColimitAlgF : (Type -> Type) -> Type
ColimitAlgF f = (a : Type) -> Algebra (OmegaColimit f) a

public export
colimitAlg :
  {0 f : Type -> Type} -> {isF : Functor f} -> {0 x : Type} ->
  Algebra f x ->
  ColimitAlg f x
colimitAlg {f} {isF} {x} alg = colimitMapAlg {isF} {v=x} alg id

public export
omegaColimitMap : {0 f : Type -> Type} -> Functor f => {0 a, b : Type} ->
  (a -> b) -> OmegaColimit f a -> OmegaColimit f b
omegaColimitMap {f} {a} {b} m (n ** c) = (n ** omegaChainMap {f} m n c)

public export
Functor f => Functor (OmegaColimit f) where
  map = omegaColimitMap

public export
omegaColimitShow :
  {0 f : Type -> Type} -> {0 a : Type} -> Functor f => Show a =>
  Algebra f String -> OmegaColimit f a -> String
omegaColimitShow {f} {a} sf (n ** c) =
  "(" ++ show n ++ ":" ++ omegaChainShow {f} {a} sf n c ++ ")"

public export
Functor f => Show a => Show (f String) => Show (OmegaColimit f a) where
  show {f} {a} = omegaColimitShow {f} {a} show

public export
DepPredColimitToChain : {f : Type -> Type} -> {a : Type} ->
  {p : OmegaColimit f a -> Type} ->
  ((c : OmegaColimit f a) -> p c -> Type) ->
  ((n : NatObj) ->
   (c : OmegaChain f n a) ->
   PredColimitToChain {f} {a} p n c ->
   Type)
DepPredColimitToChain dp n c pc = dp (n ** c) pc

public export
DepPredChainToColimit : {f : Type -> Type} -> {a : Type} ->
  {p : (n : NatObj) -> OmegaChain f n a -> Type} ->
  ((n : NatObj) -> (c : OmegaChain f n a) -> p n c -> Type) ->
  ((c : OmegaColimit f a) -> PredChainToColimit {f} {a} p c -> Type)
DepPredChainToColimit dp (n ** c) pc = dp n c pc

public export
ColimitDepIndBaseCase : {f : Type -> Type} -> {a : Type} ->
  {p : OmegaColimit f a -> Type} ->
  ((c : OmegaColimit f a) -> p c -> Type) ->
  ColimitIndBaseCase {f} {a} p ->
  Type
ColimitDepIndBaseCase = ChainDepIndBaseCase . DepPredColimitToChain

public export
ColimitDepInductionStep : {f : Type -> Type} -> {a : Type} ->
  {p : OmegaColimit f a -> Type} ->
  ((c : OmegaColimit f a) -> p c -> Type) ->
  ColimitInductionStep {f} {a} p ->
  Type
ColimitDepInductionStep = ChainDepInductionStep . DepPredColimitToChain

public export
ColimitDepInd : {f : Type -> Type} -> {a : Type} ->
  {p : OmegaColimit f a -> Type} ->
  (dp : (c : OmegaColimit f a) -> p c -> Type) ->
  {zp : ColimitIndBaseCase {f} {a} p} ->
  {sp : ColimitInductionStep {f} {a} p} ->
  ColimitDepIndBaseCase {f} {a} {p} dp zp ->
  ColimitDepInductionStep {f} {a} {p} dp sp ->
  (c : OmegaColimit f a) ->
  dp c (ColimitInduction {f} {a} p zp sp c)
ColimitDepInd {p} dp {zp} {sp} dzp dsp (n ** c) =
  ChainDepInd
    {p=(PredColimitToChain p)}
    (DepPredColimitToChain dp)
    {zp} {sp} dzp dsp n c

public export
InitialIter : (Type -> Type) -> NatObj -> Type
InitialIter f n = FunctorIter f n Void

public export
InitialChain : (Type -> Type) -> NatObj -> Type
InitialChain f n = OmegaChain f n Void

public export
InitialColimit : (Type -> Type) -> Type
InitialColimit f = OmegaColimit f Void

-- AKA parameterized catamorphism.
public export
InitialColimitMapAlg : (Type -> Type) -> Type -> Type
InitialColimitMapAlg f x = Algebra f x -> InitialColimit f -> x

public export
ColimitCata : (Type -> Type) -> Type
ColimitCata f = (x : Type) -> InitialColimitMapAlg f x

public export
colimitCata : {0 f : Type -> Type} -> {isF : Functor f} -> ColimitCata f
colimitCata {f} {isF} x alg =
  colimitMapAlg {f} {isF} {x} {v=Void} alg (voidF _)

-----------------------------------
---- Product functor iteration ----
-----------------------------------

public export
ProductFunctor : Type -> Type
ProductFunctor t = (t -> Type) -> t -> Type

public export
ProductFunctorIter : {t : Type} ->
  ProductFunctor t -> NatObj -> ProductFunctor t
ProductFunctorIter {t} f n a = NatObjInd (const $ t -> Type) a (const f) n

public export
ProductFunctorIterIndBaseCase :
  {t : Type} -> {f : ProductFunctor t} -> {a : t -> Type} ->
  (p : (n : NatObj) -> (x : t) -> ProductFunctorIter f n a x -> Type) -> Type
ProductFunctorIterIndBaseCase {t} {a} p = (x : t) -> (z : a x) -> p NatOZ x z

public export
ProductFunctorIterInductionStep :
  {t : Type} -> {f : ProductFunctor t} -> {a : t -> Type} ->
  (p : (n : NatObj) -> (x : t) -> ProductFunctorIter f n a x -> Type) -> Type
ProductFunctorIterInductionStep {t} {f} {a} p =
  (n : NatObj) ->
  ((x : t) -> (it : ProductFunctorIter f n a x) -> p n x it) ->
  ((x : t) -> (it : f (ProductFunctorIter f n a) x) -> p (NatOS n) x it)

public export
ProductFunctorIterInd :
  {0 t : Type} -> {0 f : ProductFunctor t} -> {0 a : t -> Type} ->
  (0 p : (n : NatObj) -> (x : t) -> ProductFunctorIter f n a x -> Type) ->
  ProductFunctorIterIndBaseCase {f} {a} p ->
  ProductFunctorIterInductionStep {f} {a} p ->
  (n : NatObj) -> (x : t) -> (it : ProductFunctorIter f n a x) -> p n x it
ProductFunctorIterInd {t} {f} {a} p =
  NatObjInd (\n => (x : t) -> (it : ProductFunctorIter f n a x) -> p n x it)

public export
ProductFunctorIterMapAlg : {t : Type} ->
  ProductFunctor t -> (t -> Type) -> (t -> Type) -> Type
ProductFunctorIterMapAlg {t} f x v =
  ((elem : t) -> v elem -> x elem) ->
  (n : NatObj) -> (elem : t) -> ProductFunctorIter f n v elem -> x elem

--------------------------
---- Initial algebras ----
--------------------------

public export
FInitAlg : (Type -> Type) -> Type
FInitAlg f = Algebra f (InitialColimit f)

public export
FInitAlgLift : (Type -> Type) -> Type
FInitAlgLift f = Algebra f (f (InitialColimit f))

public export
FInitAlgInv : (Type -> Type) -> Type
FInitAlgInv f = Coalgebra f (InitialColimit f)

public export
fInitAlgInv : {f : Type -> Type} -> {isF : Functor f} ->
  FInitAlg f -> FInitAlgInv f
fInitAlgInv {f} {isF} alg =
  colimitCata {f} {isF} (f (InitialColimit f)) (map {f} alg)

public export
InitAlgCorrect : {f : Type -> Type} -> {isF : Functor f} -> FInitAlg f -> Type
InitAlgCorrect {f} {isF} alg =
  ExtEq
    (fInitAlgInv {isF} alg . alg)
    (map {f} alg . map {f} (fInitAlgInv {isF} alg))

-----------------------------------------------------------------
---- Slices of natural number category as functor iterations ----
-----------------------------------------------------------------

public export
NatStrictPrefix : NatObj -> Type
NatStrictPrefix = InitialIter Maybe

public export
NatLTSlice : NatObj -> Type
NatLTSlice n = FunctorIter (Either ()) n ()

public export
NatLTSliceZ : (n : NatObj) -> NatLTSlice n
NatLTSliceZ (InNat ZeroF) = ()
NatLTSliceZ (InNat $ SuccF _) = Left ()

public export
ltSliceObjToNatStep :
  (n : NatObj) -> (NatLTSlice n -> NatObj) -> NatLTSlice (NatOS n) -> NatObj
ltSliceObjToNatStep n step (Left ()) = NatOZ
ltSliceObjToNatStep n step (Right n') = NatOS $ step n'

public export
ltSliceObjToNat : {n : NatObj} -> NatLTSlice n -> NatObj
ltSliceObjToNat {n} =
  FunctorIterInd (\_, _ => NatObj) (const NatOZ) ltSliceObjToNatStep n

public export
ltSliceOfSliceObjStep : (n : NatObj) ->
  ((slice : NatLTSlice n) ->
   (slice' : NatLTSlice (ltSliceObjToNat {n} slice)) ->
   NatLTSlice n) ->
  (slice : NatLTSlice (NatOS n)) ->
  (slice' : NatLTSlice (ltSliceObjToNat {n=(NatOS n)} slice)) ->
  NatLTSlice (NatOS n)
ltSliceOfSliceObjStep n hyp (Left ()) slice' = Left ()
ltSliceOfSliceObjStep n hyp (Right slice) slice' =
  case slice' of
    Left () => Left ()
    Right slice'' => Right $ hyp slice slice''

public export
ltSliceOfSliceObj : {n : NatObj} ->
  (slice : NatLTSlice n) ->
  (slice' : NatLTSlice (ltSliceObjToNat {n} slice)) ->
  NatLTSlice n
ltSliceOfSliceObj {n} =
  NatObjInd
    (\n' =>
      (slice : NatLTSlice n') ->
      (slice' : NatLTSlice (ltSliceObjToNat {n=n'} slice)) ->
      NatLTSlice n')
    (\_, _ => ())
    ltSliceOfSliceObjStep
    n

public export
ltSliceOfSliceObjCorrectStep : (n : NatObj) ->
  ((slice : NatLTSlice n) ->
   (slice' : NatLTSlice (ltSliceObjToNat {n} slice)) ->
    ltSliceObjToNat {n=(ltSliceObjToNat {n} slice)} slice' =
    ltSliceObjToNat {n} (ltSliceOfSliceObj {n} slice slice')) ->
  (slice : NatLTSlice (NatOS n)) ->
  (slice' : NatLTSlice (ltSliceObjToNat {n=(NatOS n)} slice)) ->
    ltSliceObjToNat {n=(ltSliceObjToNat {n=(NatOS n)} slice)} slice' =
    ltSliceObjToNat {n=(NatOS n)} (ltSliceOfSliceObj {n=(NatOS n)} slice slice')
ltSliceOfSliceObjCorrectStep n hyp (Left ()) slice' =
  Refl
ltSliceOfSliceObjCorrectStep n hyp (Right slice) slice' =
  case slice' of
    Left () => Refl
    Right slice'' => cong (InNat . SuccF) $ hyp slice slice''

public export
ltSliceOfSliceObjCorrect : {n : NatObj} ->
  (slice : NatLTSlice n) ->
  (slice' : NatLTSlice (ltSliceObjToNat {n} slice)) ->
    ltSliceObjToNat {n=(ltSliceObjToNat {n} slice)} slice' =
    ltSliceObjToNat {n} (ltSliceOfSliceObj {n} slice slice')
ltSliceOfSliceObjCorrect {n} =
  NatObjInd
    (\n' =>
      (slice : NatLTSlice n') ->
      (slice' : NatLTSlice (ltSliceObjToNat {n=n'} slice)) ->
        ltSliceObjToNat {n=(ltSliceObjToNat {n=n'} slice)} slice' =
        ltSliceObjToNat {n=n'} (ltSliceOfSliceObj {n=n'} slice slice'))
    (\_, _ => Refl)
    ltSliceOfSliceObjCorrectStep
    n

public export
ltSliceMax : (n : NatObj) -> NatLTSlice n
ltSliceMax = NatObjInd NatLTSlice () (\_ => Right)

public export
ltSliceMaxCorrect : (n : NatObj) -> ltSliceObjToNat {n} (ltSliceMax n) = n
ltSliceMaxCorrect =
  NatObjInd
    (\m => ltSliceObjToNat {n=m} (ltSliceMax m) = m)
    Refl
    (\m, eq => cong (InNat . SuccF) eq)

public export
NatLTGenInductionStep : (NatObj -> Type) -> Type
NatLTGenInductionStep p =
  (n' : NatObj) ->
  ((sl : NatLTSlice n') -> p (ltSliceObjToNat sl)) ->
  p (NatOS n')

public export
ltSubSlice : {n : NatObj} ->
  (p : NatObj -> Type) ->
  ((slice : NatLTSlice n) -> p (ltSliceObjToNat {n} slice)) ->
  (slice : NatLTSlice n) ->
  (slice' : NatLTSlice (ltSliceObjToNat {n} slice)) ->
  p (ltSliceObjToNat {n=(ltSliceObjToNat {n} slice)} slice')
ltSubSlice {n} p hyp slice slice' =
  replace {p} (sym $ ltSliceOfSliceObjCorrect slice slice') $
    hyp $ ltSliceOfSliceObj slice slice'

public export
NatLTGenIndStrengthedDefinitionStep :
  (p : NatObj -> Type) ->
  NatObjIndBaseCase p ->
  NatLTGenInductionStep p ->
  (n : NatObj) -> ((slice : NatLTSlice n) -> p (ltSliceObjToNat {n} slice)) ->
  (slice : NatLTSlice (NatOS n)) -> p (ltSliceObjToNat {n=(NatOS n)} slice)
NatLTGenIndStrengthedDefinitionStep p z s n step (Left ()) = z
NatLTGenIndStrengthedDefinitionStep p z s n step (Right slice) =
  s (ltSliceObjToNat slice) $ \slice' => ltSubSlice p step slice slice'

public export
NatLTGenIndStrengthened :
  (p : NatObj -> Type) ->
  NatObjIndBaseCase p ->
  NatLTGenInductionStep p ->
  (n : NatObj) -> ((sl : NatLTSlice n) -> p (ltSliceObjToNat {n} sl))
NatLTGenIndStrengthened p z s =
  FunctorIterInd _ (const z) (NatLTGenIndStrengthedDefinitionStep p z s)

public export
NatLTGenInd :
  (p : NatObj -> Type) ->
  NatObjIndBaseCase p ->
  NatLTGenInductionStep p ->
  (n : NatObj) -> p n
NatLTGenInd p z s n =
  rewrite sym (ltSliceMaxCorrect n) in
  NatLTGenIndStrengthened p z s n (ltSliceMax n)

----------------------------------------------------------
---- Natural number morphisms (in less-than category) ----
----------------------------------------------------------

public export
ProductMNatPred : Type
ProductMNatPred = MorphCarrier NatObj

public export
data NatLTMorph : ProductMNatPred where
  InNatLT :
    (mn : ProductMNatF NatObj) ->
    NatLTMorphF NatObj NatLTMorph mn ->
    NatLTMorph (Library.IdrisCategories.inFreePN mn)

public export
isLTZ : {mn : NatObjPair} -> NatLTMorph mn -> Bool
isLTZ (InNatLT _ (NatLTZ _)) = True
isLTZ (InNatLT _ (NatLTS _ _)) = False

public export
NatLTMorphToSucc : {m, n : NatObj} ->
  NatLTMorph (m, n) -> NatLTMorph (NatOS m, NatOS n)
NatLTMorphToSucc morph = InNatLT _ (NatLTS _ morph)

public export
NatMorphIndCurried :
  (p : (mn : NatObjPair) -> NatLTMorph mn -> Type) ->
  ((n : NatF NatObj) -> p (NatOZ, InNat n) $ InNatLT (ZeroF, n) $ NatLTZ n) ->
  ((m, n : NatObj) ->
   (morph : NatLTMorph (m, n)) ->
   p (m, n) morph ->
   p (InNat $ SuccF m, InNat $ SuccF n) $
    InNatLT (SuccF m, SuccF n) $ NatLTS (m, n) morph) ->
  (m, n : NatObj) -> (morph : NatLTMorph (m, n)) -> p (m, n) morph
NatMorphIndCurried p zn ss (InNat ZeroF) _ (InNatLT _ (NatLTZ $ n'')) =
  zn n''
NatMorphIndCurried p zn ss (InNat ZeroF) _ (InNatLT _ (NatLTS (_, _) _))
  impossible
NatMorphIndCurried p zn ss (InNat $ SuccF n) _ (InNatLT _ (NatLTZ $ n'))
  impossible
NatMorphIndCurried p zn ss (InNat $ SuccF n) (InNat ZeroF)
  (InNatLT (SuccF d, SuccF m) (NatLTS (d, m) lte))
    impossible
NatMorphIndCurried p zn ss (InNat $ SuccF n) (InNat $ SuccF n')
  (InNatLT (SuccF n, SuccF n') (NatLTS (n, n') lte)) =
    ss n n' lte $ NatMorphIndCurried p zn ss n n' lte
NatMorphIndCurried p zn ss (InNat $ SuccF n) (InNat $ SuccF n')
  (InNatLT (ZeroF, SuccF n') (NatLTS (n, n') lte))
    impossible
NatMorphIndCurried p zn ss (InNat $ SuccF n) (InNat $ SuccF n')
  (InNatLT (SuccF n, ZeroF) (NatLTS (n, n') lte))
    impossible
NatMorphIndCurried p zn ss (InNat $ SuccF n) (InNat $ SuccF n')
  (InNatLT (ZeroF, ZeroF) (NatLTS (n, n') lte))
    impossible

public export
NatMorphIndZCase : (p : (mn : NatObjPair) -> NatLTMorph mn -> Type) -> Type
NatMorphIndZCase p =
  (n : NatF NatObj) -> p (NatOZ, InNat n) $ InNatLT (ZeroF, n) $ NatLTZ n

public export
NatMorphIndSCase : (p : (mn : NatObjPair) -> NatLTMorph mn -> Type) -> Type
NatMorphIndSCase p =
  (m, n : NatObj) ->
  (morph : NatLTMorph (m, n)) ->
  p (m, n) morph ->
  p (InNat $ SuccF m, InNat $ SuccF n) $
    InNatLT (SuccF m, SuccF n) $ NatLTS (m, n) morph

public export
NatMorphInd :
  (p : (mn : NatObjPair) -> NatLTMorph mn -> Type) ->
  NatMorphIndZCase p ->
  NatMorphIndSCase p ->
  (mn : NatObjPair) -> (morph : NatLTMorph mn) -> p mn morph
NatMorphInd p zn ss (m, n) = NatMorphIndCurried p zn ss m n

public export
NatMorphDepIndZCase :
  {p : (mn : NatObjPair) -> NatLTMorph mn -> Type} ->
  (dp : (mn : NatObjPair) -> (morph : NatLTMorph mn) -> p mn morph -> Type) ->
  (zp : NatMorphIndZCase p) ->
  Type
NatMorphDepIndZCase {p} dp zp =
  (n : NatF NatObj) ->
  dp (NatOZ, InNat n) (InNatLT (ZeroF, n) (NatLTZ n)) (zp n)

public export
NatMorphDepIndSCase :
  {p : (mn : NatObjPair) -> NatLTMorph mn -> Type} ->
  (dp : (mn : NatObjPair) -> (morph : NatLTMorph mn) -> p mn morph -> Type) ->
  (sp : NatMorphIndSCase p) ->
  Type
NatMorphDepIndSCase {p} dp sp =
  (m, n : NatObj) ->
  (morph : NatLTMorph (m, n)) ->
  (pmn : p (m, n) morph) ->
  dp (m, n) morph pmn ->
  dp
    (InNat $ SuccF m, InNat $ SuccF n)
    (InNatLT (SuccF m, SuccF n) $ NatLTS (m, n) morph)
    (sp m n morph pmn)

public export
NatMorphDepInd :
  {p : (mn : NatObjPair) -> NatLTMorph mn -> Type} ->
  (dp : (mn : NatObjPair) -> (morph : NatLTMorph mn) -> p mn morph -> Type) ->
  {zp : NatMorphIndZCase p} ->
  {sp : NatMorphIndSCase p} ->
  (dzp : NatMorphDepIndZCase dp zp) ->
  (dsp : NatMorphDepIndSCase dp sp) ->
  (mn : NatObjPair) -> (morph : NatLTMorph mn) ->
  dp mn morph (NatMorphInd p zp sp mn morph)
NatMorphDepInd {p} dp {zp} {sp} dzp dsp =
  NatMorphInd
    (\mn', morph' => dp mn' morph' (NatMorphInd p zp sp mn' morph'))
    dzp
    (\m', n', morph', dpmn' =>
      dsp m' n' morph' (NatMorphInd p zp sp (m', n') morph') dpmn')

public export
NatMorphZThin : (n : NatF NatObj) ->
  (morph : NatLTMorph (InNat ZeroF, InNat n)) ->
  InNatLT (ZeroF, n) (NatLTZ n) = morph
NatMorphZThin ZeroF (InNatLT _ (NatLTZ $ ZeroF)) = Refl
NatMorphZThin ZeroF (InNatLT _ (NatLTS (m', n') morph')) impossible
NatMorphZThin (SuccF n') (InNatLT _ (NatLTZ $ ZeroF)) impossible
NatMorphZThin (SuccF n') (InNatLT _ (NatLTZ $ SuccF _)) = Refl
NatMorphZThin (SuccF n') (InNatLT _ (NatLTS (m', n') morph')) impossible

public export
0 NatMorphSThin :
  (m, n : NatObj) ->
  (morph : NatLTMorph (m, n)) ->
  ((morph' : NatLTMorph (m, n)) -> morph = morph') ->
  (morph' : NatLTMorph (InNat (SuccF m), InNat (SuccF n))) ->
  InNatLT (SuccF m, SuccF n) (NatLTS (m, n) morph) = morph'
NatMorphSThin (InNat ZeroF) (InNat ZeroF) =
  \x, y, z => ?NatMorphSThin_hole_1
NatMorphSThin (InNat ZeroF) (InNat $ SuccF n) =
  \x, y, z => ?NatMorphSThin_hole_2
NatMorphSThin (InNat (SuccF m)) (InNat ZeroF) =
  \x, y, z => ?NatMorphSThin_hole_3
NatMorphSThin (InNat (SuccF m)) (InNat $ SuccF n) =
  \x, y, z => ?NatMorphSThin_hole_4

public export
0 NatCatThin : (mn : NatObjPair) ->
  (morph, morph' : NatLTMorph mn) -> morph = morph'
NatCatThin =
  NatMorphInd
    (\mn, morph => (morph' : NatLTMorph mn) -> morph = morph')
    NatMorphZThin
    NatMorphSThin

public export
LTEThin : {m, n : Nat} -> (l, l' : LTE m n) -> l = l'
LTEThin LTEZero LTEZero = Refl
LTEThin LTEZero (LTESucc l) impossible
LTEThin (LTESucc l) LTEZero impossible
LTEThin (LTESucc l) (LTESucc l') = cong LTESucc (LTEThin l l')

public export
NatMorphToLTE : {mn : NatObjPair} ->
  NatLTMorph mn -> LTE (NatObjToMeta (fst mn)) (NatObjToMeta (snd mn))
NatMorphToLTE {mn=mn'} =
  NatMorphInd
    (\mn, morph => LTE (NatObjToMeta (fst mn)) (NatObjToMeta (snd mn)))
    (\n => LTEZero {right=(NatObjToMeta $ InNat n)})
    (\m, n, morph, lt => LTESucc lt)
    mn'

public export
LTEToNatMorph : {mn : NatPair} ->
  LTE (fst mn) (snd mn) -> NatLTMorph (NatMetaPairToObj mn)
LTEToNatMorph {mn=(Z, Z)} LTEZero =
  InNatLT (ZeroF, ZeroF) $ NatLTZ ZeroF
LTEToNatMorph {mn=(Z, Z)} (LTESucc _) impossible
LTEToNatMorph {mn=(Z, S n)} LTEZero =
  InNatLT (ZeroF, SuccF $ MetaToNatObj n) $ NatLTZ $ SuccF $ MetaToNatObj n
LTEToNatMorph {mn=(Z, S n)} (LTESucc _) impossible
LTEToNatMorph {mn=(S m, Z)} LTEZero impossible
LTEToNatMorph {mn=(S m, Z)} (LTESucc _) impossible
LTEToNatMorph {mn=(S m, S n)} LTEZero impossible
LTEToNatMorph {mn=(S m, S n)} (LTESucc lt) =
  InNatLT (SuccF $ MetaToNatObj m, SuccF $ MetaToNatObj n) $
    NatLTS (MetaToNatObj m, MetaToNatObj n) $
      LTEToNatMorph {mn=(m, n)} lt

public export
NatMorphCompose : {m, n, p : NatObj} ->
  NatLTMorph (n, p) ->
  NatLTMorph (m, n) ->
  NatLTMorph (m, p)
NatMorphCompose {m} {n} {p} g f =
  rewrite sym (NatToMetaId m) in
  rewrite sym (NatToMetaId p) in
  LTEToNatMorph {mn=(NatObjToMeta m, NatObjToMeta p)} $
    transitive (NatMorphToLTE f) (NatMorphToLTE g)

public export
NatLTOZ : (n : NatObj) -> NatLTMorph (NatOZ, n)
NatLTOZ (InNat n) = InNatLT (ZeroF, n) (NatLTZ n)

public export
NatLTOZ1 : NatLTMorph (NatOZ, NatO1)
NatLTOZ1 = NatLTOZ NatO1

public export
NatLTStrict : NatObj -> NatObj -> Type
NatLTStrict m n = NatLTMorph (NatOS m, n)

public export
OnlyZLtZ : (n : NatObj) -> NatLTMorph (n, NatOZ) -> n = NatOZ
OnlyZLtZ (InNat n) (InNatLT (n, ZeroF) m) = case n of
  ZeroF => Refl
  SuccF n' => let _ = OnlyZLtZ n' in case m of
    NatLTZ ZeroF impossible
    NatLTS (s, z) m' impossible

public export
OnlyZLtZMorph : (n : NatObj) -> (morph : NatLTMorph (n, NatOZ)) ->
  morph = NatLTOZ NatOZ
OnlyZLtZMorph n morph =
  rewrite OnlyZLtZ n morph in
  case morph of
    InNatLT _ (NatLTZ _) => Refl
    InNatLT _ (NatLTS (_, _) _) impossible

public export
NatMorphId : (n : NatObj) -> NatLTMorph (n, n)
NatMorphId (InNat n) = case n of
  ZeroF => InNatLT (ZeroF, ZeroF) $ NatLTZ ZeroF
  SuccF n' => InNatLT (SuccF n', SuccF n') $ NatLTS (n', n') $ NatMorphId n'

public export
NatLTSucc : (n : NatObj) -> NatLTMorph (n, NatOS n)
NatLTSucc = NatObjInd _ NatLTOZ1 $
  \n', morph => InNatLT _ $ NatLTS (n', InNat $ SuccF n') morph

public export
NatLTInc : {m, n : NatObj} -> NatLTMorph (m, n) -> NatLTMorph (m, NatOS n)
NatLTInc {n} = NatMorphCompose (NatLTSucc n)

public export
NatLTDec : {n, n' : NatObj} -> NatLTMorph (NatOS n, n') -> NatLTMorph (n, n')
NatLTDec {n} morph = NatMorphCompose morph $ NatLTSucc n

public export
NatMorphIdZ : NatLTMorph (NatOZ, NatOZ)
NatMorphIdZ = NatMorphId NatOZ

public export
NatMorphCompare : (m, n : NatObj) ->
  Either (m = n) $ Either (NatLTStrict m n) (NatLTStrict n m)
NatMorphCompare m n with (decEq (NatObjToMeta m) (NatObjToMeta n))
  NatMorphCompare m n | Yes eq = Left $ NatObjToMetaInj m n eq
  NatMorphCompare m n | No neq = Right $ case connex {rel=LTE} neq of
    Left lte => Left $
      let
        lt = lteTolt lte neq
        morph = LTEToNatMorph {mn=(S $ NatObjToMeta m, NatObjToMeta n)} lt
      in
      rewrite sym (NatToMetaId m) in
      rewrite sym (NatToMetaId n) in
      morph
    Right gte => Right $
      let
        lt = lteTolt gte $ \eq => neq $ sym eq
        morph = LTEToNatMorph {mn=(S $ NatObjToMeta n, NatObjToMeta m)} lt
      in
      rewrite sym (NatToMetaId m) in
      rewrite sym (NatToMetaId n) in
      morph

public export
NatLTFromSucc : (m, n : NatObj) -> NatLTMorph (NatOS m, NatOS n) ->
  NatLTMorph (m, n)
NatLTFromSucc (InNat m) = case m of
  ZeroF => \n => case n of
    InNat ZeroF => \lte => case lte of
      InNatLT (ZeroF, ZeroF) (NatLTZ $ SuccF $ InNat ZeroF) impossible
      InNatLT (ZeroF, SuccF $ InNat ZeroF) _ impossible
      InNatLT (SuccF k, ZeroF) _ impossible
      InNatLT
        (SuccF $ InNat ZeroF, SuccF $ InNat ZeroF)
        (NatLTS (InNat ZeroF, InNat ZeroF) z) =>
          z
    InNat (SuccF n') => \lte => case lte of
      InNatLT (SuccF $ InNat ZeroF, SuccF $ InNat $ SuccF p) lte' =>
        InNatLT (ZeroF, SuccF p) (NatLTZ $ SuccF p)
  SuccF m' => \n => case n of
    InNat ZeroF => \lte => case lte of
      InNatLT (SuccF $ InNat $ SuccF p, SuccF $ InNat ZeroF) lte' =>
        case lte' of
          NatLTZ _ impossible
          NatLTS (InNat ZeroF, InNat ZeroF) y impossible
          NatLTS (InNat $ SuccF p, InNat ZeroF) y => y
          NatLTS (InNat ZeroF, InNat $ SuccF _) y impossible
          NatLTS (InNat $ SuccF _, InNat $ SuccF _) y impossible
    InNat (SuccF n') => \lte => case lte of
      InNatLT (SuccF $ InNat $ SuccF p, SuccF $ InNat $ SuccF p') lte' =>
        case lte' of
          NatLTZ _ impossible
          NatLTS (InNat ZeroF, InNat ZeroF) y impossible
          NatLTS (InNat $ SuccF q, InNat ZeroF) y impossible
          NatLTS (InNat ZeroF, InNat $ SuccF q') y impossible
          NatLTS (InNat $ SuccF q, InNat $ SuccF q') y => y

public export
FromLTZeroContra : (n : NatObj) -> NatLTMorph (NatOS n, NatOZ) -> Void
FromLTZeroContra _ = succNotLTEzero . NatMorphToLTE

public export
FromSuccContra : (n : NatObj) -> NatLTMorph (NatOS n, n) -> Void
FromSuccContra _ = succNotLTEpred . NatMorphToLTE

public export
LTcontraGTE : {m, n : NatObj} -> NatLTStrict m n -> NatLTMorph (n, m) -> Void
LTcontraGTE lt gte = FromSuccContra _ $ NatMorphCompose gte lt

public export
MorphToStrict : {m, n : NatObj} ->
  NatLTMorph (m, n) -> Either (m = n) (NatLTStrict m n)
MorphToStrict {m} {n} morph with (NatMorphCompare m n)
  MorphToStrict {m} {n} morph | Left eq = Left eq
  MorphToStrict {m} {n} morph | Right (Left lt) = Right lt
  MorphToStrict {m} {n} morph | Right (Right gt) = void $ LTcontraGTE gt morph

public export
NatMorphDec : (m, n : NatObj) ->
  Either (m = n) $ Either (NatLTMorph (m, n)) (NatLTMorph (n, m))
NatMorphDec m n = case NatMorphCompare m n of
  Left eq => Left eq
  Right morph => Right $ bimap {f=Either} NatLTDec NatLTDec morph

public export
NatMorphMaybe : (m, n : NatObj) -> Maybe (NatLTMorph (m, n))
NatMorphMaybe m n = case NatMorphDec m n of
  Left _ => Nothing
  Right e => case e of
    Left morph => Just morph
    Right _ => Nothing

public export
NatLTEDec : (m, n : NatObj) -> Either (NatLTMorph (m, n)) (NatLTStrict n m)
NatLTEDec m n = case NatMorphCompare m n of
  Left eq => rewrite eq in Left $ NatMorphId _
  Right morph => case morph of
    Left lt => Left $ NatLTDec lt
    Right gt => Right gt

public export
NatStrictLTDec : (m, n : NatObj) -> Either (NatLTStrict m n) (NatLTMorph (n, m))
NatStrictLTDec m n = case NatMorphCompare m n of
  Left eq => rewrite eq in Right $ NatMorphId _
  Right morph => case morph of
    Left lt => Left lt
    Right gt => Right $ NatLTDec gt

public export
NatLTStrictMaybe : (m, n : NatObj) -> Maybe (NatLTStrict m n)
NatLTStrictMaybe m n = case NatStrictLTDec m n of
  Left morph => Just morph
  Right _ => Nothing

public export
NatMorphDecSucc : (m, n : NatObj) ->
  Either (m = n) $
    Either (NatLTMorph (NatOS m, NatOS n)) (NatLTMorph (NatOS n, NatOS m))
NatMorphDecSucc m n = case NatMorphDec m n of
  Left eq =>
    Left eq
  Right morph =>
    Right $ bimap {f=Either} NatLTMorphToSucc NatLTMorphToSucc morph

public export
NatMorphSucc : (m, n : NatObj) -> NatLTMorph (m, NatOS n) ->
  Either (NatLTMorph (m, n)) (m = NatOS n)
NatMorphSucc m n morph =
  case NatMorphCompare m (NatOS n) of
    Left eq => Right eq
    Right (Left lt) => Left $ NatLTFromSucc m n lt
    Right (Right gt) =>
      void $ FromSuccContra n $ NatLTFromSucc _ _ $ NatMorphCompose morph gt

---------------------------------------------------
---- Colimit/initial algebra utility functions ----
---------------------------------------------------

public export
colimitInj :
  {f : Type -> Type} -> Functor f =>
  InitialColimit f -> InitialColimit f
colimitInj (n ** f') = (NatOS n ** OmegaInj f')

public export
colimitConst : {f : Type -> Type} -> Functor f =>
  (one : f Void) -> InitialColimit f
colimitConst one = (NatO1 ** OmegaIter one)

public export
colimitOne :
  {f : Type -> Type} -> Functor f =>
  (succ : {n : NatObj} -> InitialChain f n -> f (InitialChain f n)) ->
  InitialColimit f -> InitialColimit f
colimitOne succ (n ** f') = (NatOS n ** OmegaIter $ succ f')

public export
OmegaChainCompose : {f : Type -> Type} -> {a : Type} -> {n, n' : NatObj} ->
  Functor f => NatLTMorph (n, n') -> OmegaChain f n a -> OmegaChain f n' a
OmegaChainCompose {f} {n} {n'} =
  NatMorphInd
    (\mn, _ => OmegaChain f (fst mn) a -> OmegaChain f (snd mn) a)
    (\k => OmegaInjN {f} {a} (InNat k))
    (\_, _, _ => map {f=(OmegaStep f)})
    (n, n')

public export
colimitPair :
  {f : Type -> Type} -> Functor f =>
  (combine : {n : NatObj} ->
    InitialChain f n -> InitialChain f n -> f (InitialChain f n)) ->
  InitialColimit f -> InitialColimit f -> InitialColimit f
colimitPair combine (m ** f') (n ** g') =
  case NatMorphDec m n of
    Left eq => (NatOS m ** case eq of Refl => OmegaIter $ combine f' g')
    Right morph => case morph of
      Left ltmn =>
        (NatOS n ** OmegaIter $ combine (OmegaChainCompose ltmn f') g')
      Right ltnm =>
        (NatOS m ** OmegaIter $ combine f' (OmegaChainCompose ltnm g'))

------------------------------
---- Slices and morphisms ----
------------------------------

public export
ltSliceObjToNatMorphStep :
  (n : NatObj) ->
  ((slice : NatLTSlice n) -> NatLTMorph (ltSliceObjToNat {n} slice, n)) ->
  (slice : NatLTSlice (NatOS n)) ->
  NatLTMorph (ltSliceObjToNat {n=(NatOS n)} slice, NatOS n)
ltSliceObjToNatMorphStep n step (Left ()) = NatLTOZ $ NatOS n
ltSliceObjToNatMorphStep n step (Right n') = NatLTMorphToSucc $ step n'

public export
ltSliceObjToNatMorph : (n : NatObj) ->
  (slice : NatLTSlice n) -> NatLTMorph (ltSliceObjToNat {n} slice, n)
ltSliceObjToNatMorph =
  FunctorIterInd _ (const NatMorphIdZ) ltSliceObjToNatMorphStep

public export
natMorphToLTSlice : {m, n : NatObj} -> NatLTMorph (m, n) -> NatLTSlice n
natMorphToLTSlice {m} {n} =
  NatMorphInd
    (\mn, _ => NatLTSlice (snd mn))
    (\n' => case n' of
      ZeroF => ()
      SuccF n'' => Left ())
    (\m', n', morph, slice => if isLTZ morph then Left () else Right slice)
    (m, n)

----------------------------------------------
---- Slices (prefixes) of natural numbers ----
----------------------------------------------

public export
NatOPrefix : NatObj -> Type
NatOPrefix n = (m : NatObj ** NatLTStrict m n)

public export
NatOPrefixMaybe : {n : NatObj} -> NatObj -> Maybe (NatOPrefix n)
NatOPrefixMaybe {n} m = case NatLTStrictMaybe m n of
  Just lt => Just (m ** lt)
  Nothing => Nothing

public export
InitNatOPrefix :
  {n : NatObj} -> (m : NatObj) ->
  {auto ok : IsJustTrue (NatOPrefixMaybe {n} m)} ->
  NatOPrefix n
InitNatOPrefix _ {ok} = fromIsJust ok

public export
NatOPrefixZ : (n : NatObj) -> NatOPrefix (NatOS n)
NatOPrefixZ n = (NatOZ ** NatLTMorphToSucc $ NatLTOZ n)

public export
NatOSlice : NatObj -> Type
NatOSlice n = (m : NatObj ** NatLTMorph (m, n))

public export
NatOSliceMaybe : {n : NatObj} -> NatObj -> Maybe (NatOSlice n)
NatOSliceMaybe {n} m = case NatMorphMaybe m n of
  Just lt => Just (m ** lt)
  Nothing => Nothing

public export
InitNatOSlice :
  {n : NatObj} -> (m : NatObj) ->
  {auto ok : isJust (NatOSliceMaybe {n} m) = True} ->
  NatOSlice n
InitNatOSlice _ {ok} = fromIsJust ok

public export
NatZSlice : Type
NatZSlice = NatOSlice NatOZ

public export
NatOSliceZ : (n : NatObj) -> NatOSlice n
NatOSliceZ n = (NatOZ ** NatLTOZ n)

public export
NatOSliceMax : (n : NatObj) -> NatOSlice n
NatOSliceMax n = (n ** NatMorphId n)

public export
NatZSliceSingleton : (sl : NatZSlice) -> sl = NatOSliceZ NatOZ
NatZSliceSingleton (m ** morph) =
  case OnlyZLtZ m morph of Refl => rewrite OnlyZLtZMorph m morph in Refl

public export
NatOSliceIndBaseCase : ((n : NatObj) -> NatOSlice n -> Type) -> Type
NatOSliceIndBaseCase p = p NatOZ (NatOSliceZ NatOZ)

public export
NatOSliceInductionStep : ((n : NatObj) -> NatOSlice n -> Type) -> Type
NatOSliceInductionStep p =
  (n : NatObj) ->
  ((sl : NatOSlice n) -> p n sl) ->
  (sl : NatOSlice (NatOS n)) -> p (NatOS n) sl

public export
NatOSliceInduction :
  (p : (n : NatObj) -> NatOSlice n -> Type) ->
  NatOSliceIndBaseCase p ->
  NatOSliceInductionStep p ->
  (n : NatObj) -> (sl : NatOSlice n) -> p n sl
NatOSliceInduction p z =
  NatObjInd
    (\n => (sl : NatOSlice n) -> p n sl)
    (\sl => replace {p=(p NatOZ)} (sym (NatZSliceSingleton sl)) z)

public export
NatOSliceDepIndBaseCase :
  {p : (n : NatObj) -> NatOSlice n -> Type} ->
  ((n : NatObj) -> (sl : NatOSlice n) -> p n sl -> Type) ->
  NatOSliceIndBaseCase p ->
  Type
NatOSliceDepIndBaseCase {p} dp z = dp NatOZ (NatOSliceZ NatOZ) z

public export
NatOSliceDepInductionStep :
  {p : (n : NatObj) -> NatOSlice n -> Type} ->
  ((n : NatObj) -> (sl : NatOSlice n) -> p n sl -> Type) ->
  NatOSliceInductionStep p ->
  Type
NatOSliceDepInductionStep {p} dp s =
  (n : NatObj) ->
  (hyp : (sl : NatOSlice n) -> p n sl) ->
  (dephyp : (sl : NatOSlice n) -> dp n sl (hyp sl)) ->
  (sl : NatOSlice (NatOS n)) ->
  dp (NatOS n) sl (s n hyp sl)

public export
NatOSliceDepInduction :
  {p : (n : NatObj) -> NatOSlice n -> Type} ->
  (dp : (n : NatObj) -> (sl : NatOSlice n) -> p n sl -> Type) ->
  {z : NatOSliceIndBaseCase p} ->
  {s : NatOSliceInductionStep p} ->
  NatOSliceDepIndBaseCase dp z ->
  NatOSliceDepInductionStep dp s ->
  (n : NatObj) -> (sl : NatOSlice n) -> dp n sl (NatOSliceInduction p z s n sl)
NatOSliceDepInduction {p} dp {z} {s} dz ds =
  NatOSliceInduction
    (\n, sl => dp n sl (NatOSliceInduction p z s n sl))
    dz
    (\n => ds n (NatOSliceInduction p z s n))

public export
(n : NatObj) => DecEq (NatOSlice n) where
  decEq {n} (m ** morph) (m' ** morph') with (decEq m m')
    decEq {n} (m ** morph) (m' ** morph') | Yes eq = Yes $
      case eq of Refl => rewrite NatCatThin _ morph morph' in Refl
    decEq {n} (m ** morph) (m' ** morph') | No neq = No $ \eq =>
      case eq of Refl => neq Refl

public export
(n : NatObj) => Eq (NatOSlice n) where
  m == m' = case decEq m m' of
    Yes _ => True
    No _ => False

public export
NatObjBoundedGenIndMorph : {n : NatObj} -> {0 a : NatOSlice n -> Type} ->
  a (NatOSliceZ n) ->
  ((m : NatObj) -> (morph : NatLTStrict m n) -> a (m ** NatLTDec morph) ->
    a (NatOS m ** morph)) ->
  (n' : NatObj) -> (morph : NatLTMorph (n', n)) -> a (n' ** morph)
NatObjBoundedGenIndMorph {n} {a} i f =
  NatObjInd
    (\n' => (morph : NatLTMorph (n', n)) -> a (n' ** morph))
    (\morph' => rewrite NatCatThin _ morph' (NatLTOZ n) in i)
    (\n', hyp, morph => f n' morph $ hyp $ NatLTDec morph)

public export
NatObjBoundedGenInd : {n : NatObj} -> {0 a : NatOSlice n -> Type} ->
  a (NatOSliceZ n) ->
  ((m : NatObj) -> (morph : NatLTStrict m n) -> a (m ** NatLTDec morph) ->
    a (NatOS m ** morph)) ->
  (m : NatOSlice n) -> a m
NatObjBoundedGenInd {a} i f (n' ** morph) =
  NatObjBoundedGenIndMorph {a} i f n' morph

public export
NatObjBoundedInd : {n : NatObj} -> {a : NatOSlice n -> Type} ->
  a (NatOSliceZ n) ->
  ((m : NatObj) -> (morph : NatLTStrict m n) -> a (m ** NatLTDec morph) ->
    a (NatOS m ** morph)) ->
  a (NatOSliceMax n)
NatObjBoundedInd {n} {a} i f = NatObjBoundedGenInd {a} i f (NatOSliceMax n)

public export
NatOSliceFromSucc : {n : NatObj} ->
  (m : NatObj ** NatLTMorph (NatOS m, NatOS n)) -> NatOSlice n
NatOSliceFromSucc {n} (m ** morph) = (m ** NatLTFromSucc m n morph)

public export
NatOSliceSuccElimMorph : {n : NatObj} ->
  {a : NatOSlice n -> Type} ->
  ((sl : (m : NatObj ** NatLTMorph (NatOS m, NatOS n))) ->
    a (fst sl ** NatLTFromSucc _ _ $ snd sl)) ->
  (m : NatObj) -> (morph : NatLTMorph (m, n)) -> a (m ** morph)
NatOSliceSuccElimMorph {n} {a} f
  (InNat ZeroF) = \lte => case lte of
    (InNatLT (ZeroF, ZeroF) (NatLTZ ZeroF)) =>
      f (NatOZ ** InNatLT (SuccF NatOZ, SuccF NatOZ) $
        NatLTS _ $ InNatLT (ZeroF, ZeroF) (NatLTZ ZeroF))
    (InNatLT (SuccF _, ZeroF) (NatLTS (_, _) _)) impossible
    (InNatLT (ZeroF, SuccF _) (NatLTS (_, _) _)) impossible
    (InNatLT (SuccF _, ZeroF) (NatLTZ _)) impossible
    (InNatLT (ZeroF, SuccF p) (NatLTZ $ SuccF p)) =>
      f (NatOZ ** InNatLT (SuccF NatOZ, SuccF $ InNat $ SuccF p) $
        NatLTS _ $ InNatLT (ZeroF, SuccF p) (NatLTZ $ SuccF p))
    (InNatLT (SuccF k, SuccF p) (NatLTS (_, _) lte)) impossible
NatOSliceSuccElimMorph {n} {a} f
  (InNat $ SuccF b) = \lte => case lte of
    (InNatLT (ZeroF, ZeroF) (NatLTZ ZeroF)) impossible
    (InNatLT (SuccF _, ZeroF) (NatLTS (_, _) _)) impossible
    (InNatLT (ZeroF, SuccF _) (NatLTS (_, _) _)) impossible
    (InNatLT (SuccF _, ZeroF) (NatLTZ _)) impossible
    (InNatLT (ZeroF, SuccF _) (NatLTZ _)) impossible
    (InNatLT (SuccF b, SuccF c) (NatLTS (b, c) d)) =>
      f (InNat (SuccF b) **
        InNatLT (SuccF $ NatOS b, SuccF $ NatOS c) $
          NatLTS _ $ InNatLT (SuccF b, SuccF c) (NatLTS (b, c) d))

public export
NatOSliceSuccElim : {n : NatObj} ->
  {a : NatOSlice n -> Type} ->
  ((sl : (m : NatObj ** NatLTMorph (NatOS m, NatOS n))) ->
    a (fst sl ** NatLTFromSucc _ _ $ snd sl)) ->
  (m : NatOSlice n) -> a m
NatOSliceSuccElim {a} f (m ** morph) = NatOSliceSuccElimMorph {a} f m morph

public export
NatObjBoundedGenMap :
  {n : NatObj} ->
  {a, b : NatOSlice n -> Type} ->
  (m : ((sl : NatOSlice n) -> a sl -> b sl)) ->
  ((sl : NatOSlice n) -> a sl) ->
  ((sl : NatOSlice n) -> b sl)
NatObjBoundedGenMap {n} m g sl = m sl $ g sl

public export
NatObjBoundedMap :
  {n : NatObj} ->
  {a, b : NatOSlice n -> Type} ->
  (m : ((sl : NatOSlice n) -> a sl -> b sl)) ->
  ((sl : NatOSlice n) -> a sl) ->
  b (NatOSliceMax n)
NatObjBoundedMap {a} {b} {n} m g =
  NatObjBoundedGenMap {a} {b} {n} m g $ NatOSliceMax n

public export
NatObjBoundedGenFold :
  {n : NatObj} ->
  {a : NatOSlice n -> Type} ->
  {b : NatOSlice (NatOS n) -> Type} ->
  ((sl : NatOSlice n) -> a sl) ->
  b (NatOSliceZ $ NatOS n) ->
  ((m : NatObj) -> (morph : NatLTMorph (m, n)) ->
   a (m ** morph) ->
   b (m ** NatLTInc morph) ->
   b (NatOS m ** NatLTMorphToSucc morph)) ->
  (m : NatOSlice (NatOS n)) -> b m
NatObjBoundedGenFold {a} {b} {n} ga z s =
  NatObjBoundedGenInd {a=b}
    z
    (\n', morph, b' =>
      let morph' = NatLTFromSucc _ _ morph in
      rewrite NatCatThin _ morph (NatLTMorphToSucc morph') in
      s n' morph'
        (ga (n' ** morph'))
        (rewrite NatCatThin (n', NatOS n) (NatLTInc morph') _ in b'))

public export
NatObjBoundedFold :
  {n : NatObj} ->
  {a : NatOSlice n -> Type} ->
  {b : NatOSlice (NatOS n) -> Type} ->
  ((sl : NatOSlice n) -> a sl) ->
  b (NatOSliceZ $ NatOS n) ->
  ((m : NatObj) -> (morph : NatLTMorph (m, n)) ->
   a (m ** morph) ->
   b (m ** NatLTInc morph) ->
   b (NatOS m ** NatLTMorphToSucc morph)) ->
  b (NatOSliceMax (NatOS n))
NatObjBoundedFold {n} {a} {b} ga z s =
  NatObjBoundedGenFold {a} {b} ga z s (NatOSliceMax (NatOS n))

public export
NatObjBoundedGenMapFold :
  {n : NatObj} ->
  {a, b : NatOSlice n -> Type} ->
  {c : NatOSlice (NatOS n) -> Type} ->
  (m : ((sl : NatOSlice n) -> a sl -> b sl)) ->
  ((sl : NatOSlice n) -> a sl) ->
  c (NatOSliceZ $ NatOS n) ->
  ((m : NatObj) -> (morph : NatLTMorph (m, n)) ->
   b (m ** morph) ->
   c (m ** NatLTInc morph) ->
   c (NatOS m ** NatLTMorphToSucc morph)) ->
  (m : NatOSlice (NatOS n)) -> c m
NatObjBoundedGenMapFold {a} {b} {c} {n} mab ga =
  NatObjBoundedGenFold {a=b} {b=c} $ NatObjBoundedGenMap {a} {b} mab ga

public export
NatObjBoundedMapFold :
  {n : NatObj} ->
  {a, b : NatOSlice n -> Type} ->
  {c : NatOSlice (NatOS n) -> Type} ->
  (m : ((sl : NatOSlice n) -> a sl -> b sl)) ->
  ((sl : NatOSlice n) -> a sl) ->
  c (NatOSliceZ $ NatOS n) ->
  ((m : NatObj) -> (morph : NatLTMorph (m, n)) ->
   b (m ** morph) ->
   c (m ** NatLTInc morph) ->
   c (NatOS m ** NatLTMorphToSucc morph)) ->
  c (NatOSliceMax (NatOS n))
NatObjBoundedMapFold {a} {b} {c} {n} mab ga z s =
  NatObjBoundedGenMapFold {a} {b} {c} {n} mab ga z s (NatOSliceMax (NatOS n))

public export
NatObjPrefixGenMap :
  {n : NatObj} ->
  {0 a, b : NatOPrefix n -> Type} ->
  (m : ((sl : NatOPrefix n) -> a sl -> b sl)) ->
  ((sl : NatOPrefix n) -> a sl) ->
  ((sl : NatOPrefix n) -> b sl)
NatObjPrefixGenMap {n} m g sl = m sl $ g sl

public export
NatObjPrefixGenFold :
  {n : NatObj} ->
  {0 a : NatOPrefix n -> Type} ->
  {0 b : NatOSlice n -> Type} ->
  ((sl : NatOPrefix n) -> a sl) ->
  b (NatOSliceZ n) ->
  ((m : NatObj) -> (morph : NatLTStrict m n) ->
   a (m ** morph) -> b (m ** NatLTDec morph) -> b ((NatOS m) ** morph)) ->
  (sl : NatOSlice n) -> b sl
NatObjPrefixGenFold {a} {b} {n} ga z s =
  NatObjBoundedGenInd {a=b}
    z
    (\n', morph, b' => s n' morph (ga (n' ** morph)) b')

public export
NatObjPrefixFold :
  {n : NatObj} ->
  {0 a : NatOPrefix n -> Type} ->
  {0 b : NatOSlice n -> Type} ->
  ((sl : NatOPrefix n) -> a sl) ->
  b (NatOSliceZ n) ->
  ((m : NatObj) -> (morph : NatLTStrict m n) ->
   a (m ** morph) -> b (m ** NatLTDec morph) -> b ((NatOS m) ** morph)) ->
  b (NatOSliceMax n)
NatObjPrefixFold {a} {b} {n} ga z s =
  NatObjPrefixGenFold {a} {b} {n} ga z s (NatOSliceMax n)

public export
NatObjPrefixGenMapFold :
  {n : NatObj} ->
  {0 a, b : NatOPrefix n -> Type} ->
  {0 c : NatOSlice n -> Type} ->
  (m : ((sl : NatOPrefix n) -> a sl -> b sl)) ->
  ((sl : NatOPrefix n) -> a sl) ->
  c (NatOSliceZ n) ->
  ((m : NatObj) -> (morph : NatLTStrict m n) ->
   b (m ** morph) -> c (m ** NatLTDec morph) -> c ((NatOS m) ** morph)) ->
  (sl : NatOSlice n) -> c sl
NatObjPrefixGenMapFold {a} {b} {c} {n} m ga =
  NatObjPrefixGenFold {a=b} {b=c} $ NatObjPrefixGenMap {a} {b} m ga

public export
NatObjPrefixMapFold :
  {n : NatObj} ->
  {0 a, b : NatOPrefix n -> Type} ->
  {0 c : NatOSlice n -> Type} ->
  (m : ((sl : NatOPrefix n) -> a sl -> b sl)) ->
  ((sl : NatOPrefix n) -> a sl) ->
  c (NatOSliceZ n) ->
  ((m : NatObj) -> (morph : NatLTStrict m n) ->
   b (m ** morph) -> c (m ** NatLTDec morph) -> c ((NatOS m) ** morph)) ->
  c (NatOSliceMax n)
NatObjPrefixMapFold {a} {b} {c} {n} mab ga z s =
  NatObjPrefixGenMapFold {a} {b} {c} {n} mab ga z s (NatOSliceMax n)

---------------------------
---- General induction ----
---------------------------

public export
ForallLTE : (NatObj -> Type) -> NatObj -> Type
ForallLTE p n = (sl : NatOSlice n) -> p (fst sl)

public export
NatObjGenInductionStep : (NatObj -> Type) -> Type
NatObjGenInductionStep p = (n' : NatObj) -> ForallLTE p n' -> p (NatOS n')

public export
NatObjGenIndStrengthenedStep :
  (p : NatObj -> Type) ->
  NatObjGenInductionStep p ->
  (n : NatObj) ->
  ForallLTE p n ->
  ForallLTE p (NatOS n)
NatObjGenIndStrengthenedStep p s n hyp (n' ** m) =
  case NatMorphSucc n' n m of
    Left m' => hyp (n' ** m')
    Right eqn => rewrite eqn in s n hyp

public export
NatObjGenIndStrengthened :
  (p : NatObj -> Type) ->
  NatObjIndBaseCase p ->
  NatObjGenInductionStep p ->
  (n : NatObj) -> ForallLTE p n
NatObjGenIndStrengthened p z s =
  NatOSliceInduction
    (\n, sl => p (fst sl))
    z
    (NatObjGenIndStrengthenedStep p s)

public export
NatObjGenInd :
  (p : NatObj -> Type) ->
  NatObjIndBaseCase p ->
  NatObjGenInductionStep p ->
  (n : NatObj) -> p n
NatObjGenInd p z s n = NatObjGenIndStrengthened p z s n (NatOSliceMax n)

public export
ForallLTEDep : {p : NatObj -> Type} ->
  ((n : NatObj) -> p n -> Type) ->
  (n : NatObj) -> ForallLTE p n -> Type
ForallLTEDep {p} dp n ps = (sl : NatOSlice n) -> dp (fst sl) (ps sl)

public export
NatObjDepGenInductionStep :
  {p : NatObj -> Type} ->
  (dp : (n : NatObj) -> p n -> Type) ->
  (sp : NatObjGenInductionStep p) ->
  Type
NatObjDepGenInductionStep {p} dp sp =
  (n' : NatObj) -> (pn : ForallLTE p n') -> ForallLTEDep dp n' pn ->
  dp (NatOS n') (sp n' pn)

public export
NatObjDepGenIndStrengthenedStep :
  (p : NatObj -> Type) ->
  (dp : (n : NatObj) -> p n -> Type) ->
  (sp : NatObjGenInductionStep p) ->
  NatObjDepGenInductionStep dp sp ->
  (n : NatObj) ->
  (hyp : ForallLTE p n) ->
  (dh : ForallLTEDep dp n hyp) ->
  (sl : NatOSlice (NatOS n)) ->
  dp (fst sl) (NatObjGenIndStrengthenedStep p sp n hyp sl)
NatObjDepGenIndStrengthenedStep p dp sp dsp n hyp dh (n' ** m)
  with (NatMorphSucc n' n m)
    NatObjDepGenIndStrengthenedStep p dp sp dsp n hyp dh (n' ** m) | Left m' =
      dh (n' ** m')
    NatObjDepGenIndStrengthenedStep p dp sp dsp n hyp dh (n' ** m) | Right eqn =
      rewrite eqn in
      dsp n hyp dh

public export
NatObjDepGenIndStrengthened :
  {p : NatObj -> Type} ->
  (dp : (n : NatObj) -> p n -> Type) ->
  {zp : NatObjIndBaseCase p} ->
  {sp : NatObjGenInductionStep p} ->
  NatObjDepIndBaseCase dp zp ->
  NatObjDepGenInductionStep dp sp ->
  (n : NatObj) -> ForallLTEDep dp n (NatObjGenIndStrengthened p zp sp n)
NatObjDepGenIndStrengthened {p} dp {zp} {sp} dzp dsp =
  NatOSliceDepInduction
    {p=(\n, sl => p (fst sl))}
    (\n, sl, ps => dp (fst sl) ps)
    {z=zp}
    {s=(NatObjGenIndStrengthenedStep p sp)}
    dzp
    (NatObjDepGenIndStrengthenedStep p dp sp dsp)

public export
NatObjDepGenInd :
  {p : NatObj -> Type} ->
  (dp : (n : NatObj) -> p n -> Type) ->
  {zp : NatObjIndBaseCase p} ->
  {sp : NatObjGenInductionStep p} ->
  NatObjDepIndBaseCase dp zp ->
  NatObjDepGenInductionStep dp sp ->
  (n : NatObj) -> dp n (NatObjGenInd p zp sp n)
NatObjDepGenInd {p} dp {zp} {sp} dzp dsp n =
  NatObjDepGenIndStrengthened {p} dp {zp} {sp} dzp dsp n (NatOSliceMax n)

public export
FunctorIterLTE : {f : Type -> Type} -> {a : Type} ->
  ((n : NatObj) -> FunctorIter f n a -> Type) -> NatObj -> Type
FunctorIterLTE {f} {a} p n =
  (sl : NatOSlice n) -> (ty : FunctorIter f (fst sl) a) -> p (fst sl) ty

public export
FunctorIterGenIndStep : {f : Type -> Type} -> {a : Type} ->
  (p : (n' : NatObj) -> FunctorIter f n' a -> Type) -> Type
FunctorIterGenIndStep {f} {a} p =
  (n' : NatObj) ->
  FunctorIterLTE p n' ->
  (ty : FunctorIter f (NatOS n') a) ->
  p (NatOS n') ty

public export
FunctorIterGenInd : {f : Type -> Type} -> {a : Type} ->
  (p : (n' : NatObj) -> FunctorIter f n' a -> Type) ->
  FunctorIterIndBaseCase {f} {a} p ->
  FunctorIterGenIndStep {f} {a} p ->
  (n : NatObj) -> (ty : FunctorIter f n a) -> p n ty
FunctorIterGenInd {f} {a} p =
  NatObjGenInd (\n' => (ty : FunctorIter f n' a) -> p n' ty)

public export
FunctorIterLTEDep : {f : Type -> Type} -> {a : Type} ->
  {p : (n : NatObj) -> FunctorIter f n a -> Type} ->
  (dp : (n : NatObj) -> (ty : FunctorIter f n a) -> p n ty -> Type) ->
  (n : NatObj) -> FunctorIterLTE {f} {a} p n -> Type
FunctorIterLTEDep {f} {a} {p} dp n lte =
  (sl : NatOSlice n) ->
  (ty : FunctorIter f (fst sl) a) ->
  dp (fst sl) ty (lte sl ty)

public export
FunctorIterDepGenInductionStep : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> FunctorIter f n' a -> Type} ->
  ((n' : NatObj) -> (it : FunctorIter f n' a) -> p n' it -> Type) ->
  FunctorIterGenIndStep {f} {a} p ->
  Type
FunctorIterDepGenInductionStep {f} {a} {p} dp sp =
  (n' : NatObj) ->
  (pty : FunctorIterLTE p n') ->
  (dephyp : FunctorIterLTEDep dp n' pty) ->
  ((ty : f (FunctorIter f n' a)) -> dp (NatOS n') ty (sp n' pty ty))

public export
FunctorIterDepGenInd : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> FunctorIter f n' a -> Type} ->
  (dp : (n' : NatObj) -> (it : FunctorIter f n' a) -> p n' it -> Type) ->
  {zp : FunctorIterIndBaseCase {f} {a} p} ->
  {sp : FunctorIterGenIndStep {f} {a} p} ->
  FunctorIterDepIndBaseCase {f} {a} {p} dp zp ->
  FunctorIterDepGenInductionStep {f} {a} {p} dp sp ->
  (n : NatObj) -> (ty : FunctorIter f n a) ->
  dp n ty (FunctorIterGenInd {f} {a} p zp sp n ty)
FunctorIterDepGenInd {f} {a} {p} dp =
  NatObjDepGenInd
    {p=(\n' => (ty : FunctorIter f n' a) -> p n' ty)}
    (\n', hyp' => (ty : FunctorIter f n' a) -> dp n' ty (hyp' ty))

public export
ChainLTE : {f : Type -> Type} -> {a : Type} ->
  ((n : NatObj) -> OmegaChain f n a -> Type) -> NatObj -> Type
ChainLTE {f} {a} p n =
  (sl : NatOSlice n) -> (ty : OmegaChain f (fst sl) a) -> p (fst sl) ty

public export
ChainGenIndStep : {f : Type -> Type} -> {a : Type} ->
  (p : (n' : NatObj) -> OmegaChain f n' a -> Type) -> Type
ChainGenIndStep {f} = FunctorIterGenIndStep {f=(OmegaStep f)}

public export
ChainGenInd : {f : Type -> Type} -> {a : Type} ->
  (p : (n' : NatObj) -> OmegaChain f n' a -> Type) ->
  ChainIndBaseCase {f} {a} p ->
  ChainGenIndStep {f} {a} p ->
  (n : NatObj) -> (ty : OmegaChain f n a) -> p n ty
ChainGenInd {f} = FunctorIterGenInd {f=(OmegaStep f)}

public export
ChainLTEDep : {f : Type -> Type} -> {a : Type} ->
  {p : (n : NatObj) -> OmegaChain f n a -> Type} ->
  (dp : (n : NatObj) -> (ty : OmegaChain f n a) -> p n ty -> Type) ->
  (n : NatObj) -> ChainLTE {f} {a} p n -> Type
ChainLTEDep {f} {a} {p} dp n lte =
  (sl : NatOSlice n) ->
  (ty : OmegaChain f (fst sl) a) ->
  dp (fst sl) ty (lte sl ty)

public export
ChainDepGenInductionStep : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> OmegaChain f n' a -> Type} ->
  ((n' : NatObj) -> (it : OmegaChain f n' a) -> p n' it -> Type) ->
  ChainGenIndStep {f} {a} p ->
  Type
ChainDepGenInductionStep {f} {a} {p} dp sp =
  (n' : NatObj) ->
  (pty : ChainLTE p n') ->
  (dephyp : ChainLTEDep dp n' pty) ->
  ((ty : OmegaStep f (OmegaChain f n' a)) -> dp (NatOS n') ty (sp n' pty ty))

public export
ChainDepGenInd : {f : Type -> Type} -> {a : Type} ->
  {p : (n' : NatObj) -> OmegaChain f n' a -> Type} ->
  (dp : (n' : NatObj) -> (it : OmegaChain f n' a) -> p n' it -> Type) ->
  {zp : ChainIndBaseCase {f} {a} p} ->
  {sp : ChainGenIndStep {f} {a} p} ->
  ChainDepIndBaseCase {f} {a} {p} dp zp ->
  ChainDepGenInductionStep {f} {a} {p} dp sp ->
  (n : NatObj) -> (ty : OmegaChain f n a) ->
  dp n ty (ChainGenInd {f} {a} p zp sp n ty)
ChainDepGenInd {f} = FunctorIterDepGenInd {f=(OmegaStep f)}

public export
ColimitGenIndStep : {f : Type -> Type} -> {a : Type} ->
  (p : OmegaColimit f a -> Type) -> Type
ColimitGenIndStep = ChainGenIndStep . PredColimitToChain

public export
ColimitGenInd : {f : Type -> Type} -> {a : Type} ->
  (p : OmegaColimit f a -> Type) ->
  ColimitIndBaseCase {f} {a} p ->
  ColimitGenIndStep {f} {a} p ->
  (c : OmegaColimit f a) -> p c
ColimitGenInd p zp sp (n ** c) = ChainGenInd (PredColimitToChain p) zp sp n c

public export
ColimitDepGenInductionStep : {f : Type -> Type} -> {a : Type} ->
  {p : OmegaColimit f a -> Type} ->
  ((c : OmegaColimit f a) -> p c -> Type) ->
  ColimitGenIndStep {f} {a} p ->
  Type
ColimitDepGenInductionStep = ChainDepGenInductionStep . DepPredColimitToChain

public export
ColimitDepGenInd : {f : Type -> Type} -> {a : Type} ->
  {p : OmegaColimit f a -> Type} ->
  (dp : (c : OmegaColimit f a) -> p c -> Type) ->
  {zp : ColimitIndBaseCase {f} {a} p} ->
  {sp : ColimitGenIndStep {f} {a} p} ->
  ColimitDepIndBaseCase {f} {a} {p} dp zp ->
  ColimitDepGenInductionStep {f} {a} {p} dp sp ->
  (c : OmegaColimit f a) ->
  dp c (ColimitGenInd {f} {a} p zp sp c)
ColimitDepGenInd {p} dp {zp} {sp} dzp dsp (n ** c) =
  ChainDepGenInd
    {p=(PredColimitToChain p)}
    (DepPredColimitToChain dp)
    {zp} {sp} dzp dsp n c

--------------------
---- Arithmetic ----
--------------------

public export
PrefixArray : NatObj -> Type -> Type
PrefixArray n ty = NatOPrefix n -> ty

public export
SliceArray : NatObj -> Type -> Type
SliceArray n ty = NatOSlice n -> ty

public export
prefixArrayFromSlice : {a : Type} -> {n : NatObj} ->
  SliceArray n a -> PrefixArray (NatOS n) a
prefixArrayFromSlice {n} v (m ** morph) = v (m ** NatLTFromSucc m n morph)

public export
prefixArrayFromList : {a : Type} ->
  (l : List a) -> PrefixArray (MetaToNatObj (length l)) a
prefixArrayFromList [] (m ** morph) = void $ FromLTZeroContra m morph
prefixArrayFromList (x :: xs) (m ** morph) = case m of
  InNat ZeroF => x
  InNat (SuccF m') => prefixArrayFromList xs (m' ** NatLTFromSucc _ _ morph)

public export
sliceArrayFromList : {a : Type} ->
  (i : a) -> (l : List a) -> SliceArray (MetaToNatObj (length l)) a
sliceArrayFromList i l (m ** morph) = case m of
  InNat ZeroF => i
  InNat (SuccF m') => prefixArrayFromList l (m' ** morph)

public export
prefixArrayStringFold : {n : NatObj} -> {0 a : Type} ->
  (a -> String) -> PrefixArray n a -> String
prefixArrayStringFold {n} {a} sa v =
  NatObjPrefixMapFold {a=(const a)} {b=(const String)} {c=(const String)}
    (const sa)
    v
    "[empty]"
    (\n', morph, ss, sc =>
      let sc' = if n' == NatOZ then "" else sc ++ "; " in
      sc' ++ "val[" ++ show n' ++ "]=" ++ ss)

public export
showPrefixArrayArray : {m, n : NatObj} -> {0 a : Type} ->
  (a -> String) -> PrefixArray m (PrefixArray n a) -> String
showPrefixArrayArray = prefixArrayStringFold . prefixArrayStringFold

public export
PrefixArrayTruncate : {m : NatObj} -> {0 a : Type} ->
  PrefixArray (NatOS m) a -> PrefixArray m a
PrefixArrayTruncate arr (m ** morph) = arr (m ** NatLTInc morph)

public export
PrefixArrayTruncateEq : {m : NatObj} -> {0 a : Type} ->
  (arr : PrefixArray (NatOS m) a) ->
  (n : NatObj) ->
  (morph : NatLTStrict n m) ->
  (morph' : NatLTStrict n (NatOS m)) ->
  PrefixArrayTruncate arr (n ** morph) = arr (n ** morph')
PrefixArrayTruncateEq arr n morph morph' =
  rewrite NatCatThin _ morph' _ in Refl

public export
PrefixMap : NatObj -> NatObj -> Type
PrefixMap m n = NatOPrefix m -> NatOPrefix n

public export
MetaPrefixMap : Nat -> Nat -> Type
MetaPrefixMap m n = PrefixMap (MetaToNatObj m) (MetaToNatObj n)

public export
showPrefixMap : {m, n : NatObj} ->
  (NatOPrefix m -> NatOPrefix n) -> String
showPrefixMap = prefixArrayStringFold (show . fst)

public export
PrefixMapTruncate : {m, n : NatObj} ->
  PrefixMap (NatOS m) n -> PrefixMap m n
PrefixMapTruncate arr (m ** morph) = arr (m ** NatLTInc morph)

public export
PrefixMapTruncateEq : {m, n : NatObj} ->
  (pm : PrefixMap (NatOS m) n) ->
  (k : NatObj) ->
  (morph : NatLTStrict k m) ->
  (morph' : NatLTStrict k (NatOS m)) ->
  PrefixMapTruncate pm (k ** morph) = pm (k ** morph')
PrefixMapTruncateEq pm k morph morph' =
  rewrite NatCatThin _ morph' _ in Refl

public export
sliceArrayStringFold : {n : NatObj} -> {a : Type} ->
  (a -> String) -> SliceArray n a -> String
sliceArrayStringFold {n} {a} sa v =
  prefixArrayStringFold sa $ prefixArrayFromSlice {n} v

public export
(n : NatObj) => (a : Type) => Show a => Show (PrefixArray n a) where
  show {n} {a} = prefixArrayStringFold show

public export
(n : NatObj) => (a : Type) => Show a => Show (SliceArray n a) where
  show {n} {a} = sliceArrayStringFold show

public export
PrefixArrayConst : {n : NatObj} -> {a : Type} -> (x : a) -> PrefixArray n a
PrefixArrayConst x _ = x

public export
SliceArrayConst : {n : NatObj} -> {a : Type} -> (x : a) -> SliceArray n a
SliceArrayConst x _ = x

public export
natObjSum : NatObj -> NatObj -> NatObj
natObjSum =
  NatObjInd
    (const $ NatObj -> NatObj)
    id
    (const $ (.) NatOS)

public export
natObjMinus : {m, n : NatObj} -> NatLTMorph (n, m) -> NatObj
natObjMinus {m} {n} =
  NatMorphInd
    (\_, _ => NatObj)
    InNat
    (\_, _, _ => id)
    (n, m)

public export
natObjMinusLt : {m, n, k : NatObj} ->
  (lte : NatLTMorph (m, k)) ->
  NatLTStrict k (natObjSum m n) -> NatLTStrict (natObjMinus lte) n
natObjMinusLt {m} {n} {k} =
  NatMorphInd
    (\mk, morph => case mk of
      (m', k') =>
        NatLTStrict k' (natObjSum m' n) ->
        NatLTStrict (natObjMinus {m=k'} {n=m'} morph) n)
    (\n', morph' => morph')
    (\m', n', morph', hyp, lte' => hyp $ NatLTFromSucc _ _ lte')
    (m, k)

public export
natObjMul : NatObj -> NatObj -> NatObj
natObjMul =
  NatObjInd
    (const $ NatObj -> NatObj)
    (const NatOZ)
    (\pred, mulbypred, n => natObjSum (mulbypred n) n)

public export
natObjRaiseTo : NatObj -> NatObj -> NatObj
natObjRaiseTo =
  NatObjInd
    (const $ NatObj -> NatObj)
    (const NatO1)
    (\pred, raisetopred, n => natObjMul (raisetopred n) n)

public export
natObjPow : NatObj -> NatObj -> NatObj
natObjPow = flip natObjRaiseTo

public export
NatPrefixReplicate : {a : Type} -> (n : NatObj) -> (x : a) -> PrefixArray n a
NatPrefixReplicate n x sl = x

public export
NatPrefixAppend : {a : Type} -> {m, n : NatObj} ->
  PrefixArray m a -> PrefixArray n a -> PrefixArray (natObjSum m n) a
NatPrefixAppend {a} {m} {n} f g (k ** morph) with (NatStrictLTDec k m)
  NatPrefixAppend {a} {m} {n} f g (k ** morph) | Left lt =
    f (k ** lt)
  NatPrefixAppend {a} {m} {n} f g (k ** morph) | Right gte =
    g (natObjMinus gte ** natObjMinusLt gte morph)

public export
natSliceRunningSum : {n : NatObj} ->
  SliceArray n NatObj -> SliceArray (NatOS n) NatObj
natSliceRunningSum {n} v =
  NatObjBoundedGenFold {n} {a=(const NatObj)} {b=(const NatObj)}
    v NatOZ (\_, _ => natObjSum)

public export
natSliceSum : {n : NatObj} -> SliceArray n NatObj -> NatObj
natSliceSum {n} v = natSliceRunningSum v (NatOSliceMax (NatOS n))

public export
NatSliceTruncate : {a : Type} -> {n : NatObj} ->
  SliceArray (NatOS n) a -> SliceArray n a
NatSliceTruncate arr (m ** morph) = arr (m ** NatLTInc morph)

public export
NatPrefixTruncate : {a : Type} -> {n : NatObj} ->
  PrefixArray (NatOS n) a -> PrefixArray n a
NatPrefixTruncate arr (m ** morph) = arr (m ** NatLTInc morph)

public export
NatPrefixFoldAppendStepSumMorph : {a : Type} -> {n : NatObj} ->
  (lengths : SliceArray n NatObj) ->
  (m : NatObj) ->
  (morph : NatLTMorph (m, n)) ->
  (morph' : NatLTMorph (m, NatOS n)) ->
  (morph'' : NatLTMorph (NatOS m, NatOS n)) ->
  natObjSum
    (lengths (m ** morph))
    (natSliceRunningSum lengths (m ** morph')) =
  natSliceRunningSum lengths (NatOS m ** morph'')
NatPrefixFoldAppendStepSumMorph {a} {n} lengths m morph morph' morph'' =
  rewrite NatCatThin _ (NatLTFromSucc m n morph'') morph in
  rewrite NatCatThin _ morph' _ in
  Refl

public export
NatPrefixFoldAppendStepSum : {a : Type} -> {n : NatObj} ->
  (lengths : SliceArray n NatObj) ->
  (m : NatObj) ->
  (morph : NatLTMorph (m, n)) ->
  natObjSum
    (lengths (m ** morph))
    (natSliceRunningSum lengths (m ** NatLTInc morph)) =
  natSliceRunningSum lengths (NatOS m ** NatLTMorphToSucc morph)
NatPrefixFoldAppendStepSum {a} {n} lengths m morph =
  NatPrefixFoldAppendStepSumMorph {a} {n} lengths m morph
    (NatLTInc morph) (NatLTMorphToSucc morph)

public export
NatPrefixFoldAppendStep : {a : Type} -> {n : NatObj} ->
  (lengths : SliceArray n NatObj) ->
  (m : NatObj) -> (morph : NatLTMorph (m, n)) ->
  PrefixArray (lengths (m ** morph)) a ->
  PrefixArray (natSliceRunningSum lengths (m ** NatLTInc morph)) a ->
  PrefixArray (natSliceRunningSum lengths (NatOS m ** NatLTMorphToSucc morph)) a
NatPrefixFoldAppendStep {a} {n} lengths m morph sc ss =
  rewrite sym (NatPrefixFoldAppendStepSum {a} {n} lengths m morph) in
  NatPrefixAppend sc ss

public export
NatPrefixFoldAppend : {a : Type} -> {n : NatObj} ->
  (lengths : SliceArray n NatObj) ->
  (prefixes : (sl : NatOSlice n) -> PrefixArray (lengths sl) a) ->
  PrefixArray (natSliceSum lengths) a
NatPrefixFoldAppend {a} {n} lengths prefixes =
  NatObjBoundedFold
    {a=(\sl => PrefixArray (lengths sl) a)}
    {b=(\sl => PrefixArray (natSliceRunningSum lengths sl) a)}
    prefixes
    (\sl => void $ FromLTZeroContra _ $ snd sl)
    (NatPrefixFoldAppendStep {a} {n} lengths)

public export
prefixMapFromListRev : (n : Nat) -> (l : List Nat) ->
  Maybe (NatOPrefix (MetaToNatObj (length l)) -> NatOPrefix (MetaToNatObj n))
prefixMapFromListRev n [] =
  Just $ \sl => void $ FromLTZeroContra (fst sl) (snd sl)
prefixMapFromListRev n (x :: xs) = case prefixMapFromListRev n xs of
  Just f => case NatOPrefixMaybe {n=(MetaToNatObj n)} (MetaToNatObj x) of
    Just sl =>
      Just $ \sl' => case sl' of
          (m ** morph) =>
            case MorphToStrict (NatLTFromSucc _ _ morph) of
              Left eq => sl
              Right lt => f (m ** lt)
    Nothing => Nothing
  Nothing => Nothing

public export
prefixMapFromList : (n : Nat) -> (l : List Nat) ->
  Maybe (NatOPrefix (MetaToNatObj (length l)) -> NatOPrefix (MetaToNatObj n))
prefixMapFromList n l =
  rewrite sym (reverseLength l) in prefixMapFromListRev n (reverse l)

public export
InitPrefixMap : (n : Nat) ->
  (l : List Nat) -> {auto ok : IsJustTrue (prefixMapFromList n l)} ->
  MetaPrefixMap (length l) n
InitPrefixMap _ _ {ok} = fromIsJust ok

public export
DepPrefixContraMap :
  {domPos, codPos : NatObj} ->
  (domDir : PrefixArray domPos NatObj) ->
  (codDir : PrefixArray codPos NatObj) ->
  (posMap : PrefixMap domPos codPos) ->
  Type
DepPrefixContraMap {domPos} {codPos} domDir codDir posMap =
  (pos : NatOPrefix domPos) -> PrefixMap (codDir (posMap pos)) (domDir pos)

public export
showDepPrefixContraMap :
  {domPos, codPos : NatObj} ->
  (domDir : PrefixArray domPos NatObj) ->
  (codDir : PrefixArray codPos NatObj) ->
  (posMap : PrefixMap domPos codPos) ->
  DepPrefixContraMap domDir codDir posMap ->
  String
showDepPrefixContraMap {domPos} {codPos} domDir codDir posMap dpm =
  NatObjPrefixFold
    {n=domPos}
    {a=(\pos => PrefixMap (codDir (posMap pos)) (domDir pos))}
    {b=(const String)}
    dpm
    "[empty domain]"
    (\m, morph, dirmap, ss =>
      let ss' = if m == NatOZ then "" else ss ++ "; " in
      ss' ++ "codomain[" ++ show (fst (posMap (m ** morph))) ++
      "] -> domain[" ++ show m ++ "]: " ++
      prefixArrayStringFold (show . fst) dirmap)

public export
depPrefixContraMapFromListsRev :
  {domPos, codPos : NatObj} ->
  (domDir : PrefixArray domPos NatObj) ->
  (codDir : PrefixArray codPos NatObj) ->
  (posMap : PrefixMap domPos codPos) ->
  List (List Nat) ->
  Maybe (DepPrefixContraMap {domPos} {codPos} domDir codDir posMap)
depPrefixContraMapFromListsRev {domPos} {codPos} domDir codDir posMap [] =
  case domPos of
    InNat ZeroF => Just $ \sl => void $ FromLTZeroContra _ (snd sl)
    InNat (SuccF _) => Nothing
depPrefixContraMapFromListsRev {domPos} {codPos} domDir codDir posMap (l :: ls) =
  case domPos of
    InNat ZeroF => Nothing
    InNat (SuccF domPos') =>
      case
        depPrefixContraMapFromListsRev
          {domPos=domPos'}
          {codPos}
          (PrefixArrayTruncate domDir)
          codDir
          (PrefixMapTruncate posMap)
          ls of
        Just tlmap =>
          case decEq (length l) (NatObjToMeta $ codDir $ posMap (domPos' ** NatLTMorphToSucc $ NatMorphId domPos')) of
            Yes lenEq =>
              case prefixMapFromList (NatObjToMeta $ domDir (domPos' ** NatLTMorphToSucc $ NatMorphId domPos')) l of
                Just hdmap =>
                  Just $ \pos, coddir => case pos of
                    (posn ** poslt) =>
                      case MorphToStrict (NatLTFromSucc _ _ poslt) of
                        Left Refl => case coddir of
                          (codn ** codlt) =>
                            let
                              0 morphEq = NatCatThin _ (NatLTMorphToSucc $ NatMorphId posn) poslt
                              codMetaId = NatToMetaId (codDir $ posMap (posn ** NatLTMorphToSucc $ NatMorphId posn))
                              hdmapc = hdmap (codn ** rewrite lenEq in rewrite codMetaId in rewrite morphEq in codlt)
                              domMetaId = NatToMetaId (domDir (posn ** NatLTMorphToSucc $ NatMorphId posn))
                            in
                            replace
                              {p=(\morph' => (m : NatObj ** NatLTStrict m (domDir (posn ** morph'))))}
                              morphEq $
                                replace {p=NatOPrefix} domMetaId hdmapc
                        Right lt =>
                          let teq = PrefixArrayTruncateEq domDir posn lt poslt in
                          let meq = PrefixMapTruncateEq posMap posn lt poslt in
                          rewrite sym teq in
                          tlmap (posn ** lt) $ case coddir of
                            (codn ** codlt) => (codn ** rewrite meq in codlt)
                Nothing => Nothing
            No _ => Nothing
        Nothing => Nothing

public export
depPrefixContraMapFromLists :
  {domPos, codPos : NatObj} ->
  (domDir : PrefixArray domPos NatObj) ->
  (codDir : PrefixArray codPos NatObj) ->
  (posMap : PrefixMap domPos codPos) ->
  List (List Nat) ->
  Maybe (DepPrefixContraMap {domPos} {codPos} domDir codDir posMap)
depPrefixContraMapFromLists domDir codDir posMap =
  depPrefixContraMapFromListsRev domDir codDir posMap . reverse

------------------------------------------
------------------------------------------
---- Types founded in natural numbers ----
------------------------------------------
------------------------------------------

public export
natFoldIdx : {0 x : Type} -> (Nat -> x -> x) -> x -> Nat -> Nat -> x
natFoldIdx op acc idx Z = acc
natFoldIdx op acc idx (S n) = natFoldIdx op (op idx acc) (S idx) n

public export
record NatFoldAlg (0 x : Type) where
  constructor MkNatFold
  nfOp : Nat -> x -> x
  nfZero : x

public export
natFold : {0 x : Type} -> NatFoldAlg x -> Nat -> x
natFold {x} (MkNatFold op z) = natFoldIdx op z Z

--------------------------------
---- Dependent endofunctors ----
--------------------------------

public export
NatDepPredF : (NatObj -> Type) -> NatObj -> Type
NatDepPredF a n = a n -> Type

public export
NatDepPred : (NatObj -> Type) -> Type
NatDepPred a = (n : NatObj) -> NatDepPredF a n

public export
NatDepFunctorStep : (NatObj -> Type) -> Type
NatDepFunctorStep = NatObjInductionStep . NatDepPredF

public export
NatDepFunctorF : (NatObj -> Type) -> NatObj -> Type
NatDepFunctorF a n = NatDepPredF a NatOZ -> NatDepPredF a n

public export
NatDepFunctor : (NatObj -> Type) -> Type
NatDepFunctor a = (n : NatObj) -> NatDepFunctorF a n

public export
DepFunctorIter : {a : NatObj -> Type} ->
  NatDepFunctorStep a -> NatDepFunctor a
DepFunctorIter {a} f n b = NatObjInd (NatDepPredF a) b f n

---------------
---- Lists ----
---------------

public export
data ListF : Type -> Type -> Type where
  NilF : ListF atom carrier
  ConsF : atom -> carrier -> ListF atom carrier

public export
Bifunctor ListF where
  bimap f g NilF = NilF
  bimap f g (ConsF x l) = ConsF (f x) (g l)

public export
showListF : {0 atom, carrier : Type} ->
  (atom -> String) -> (carrier -> String) ->
  ListF atom carrier -> String
showListF sa sc NilF = "[]"
showListF sa sc (ConsF x l) = "(" ++ sa x ++ " :: " ++ sc l ++ ")"

public export
(Show atom, Show carrier) => Show (ListF atom carrier) where
  show = showListF show show

public export
ListAlg : Type -> Type -> Type
ListAlg = Algebra . ListF

public export
FreeList : Type -> Type -> Type
FreeList = FreeMonad . ListF

public export
MuList : Type -> Type
MuList = Mu . ListF

public export
ListCoalg : Type -> Type -> Type
ListCoalg = Coalgebra . ListF

public export
CofreeList : Type -> Type -> Type
CofreeList = CofreeComonad . ListF

public export
NuList : Type -> Type
NuList = Nu . ListF

public export
cataListF : {atom : Type} -> FreeFEval $ ListF atom
cataListF v a subst alg (InFree x) = case x of
  TFV var => subst var
  TFC l => alg $ case l of
    NilF => NilF
    ConsF x l' => ConsF x $ cataListF v a subst alg l'

public export
interpListFAlg : {atom : Type} -> ListAlg atom $ List atom
interpListFAlg NilF = []
interpListFAlg (ConsF x l') = x :: l'

public export
interpFreeListF : {atom : Type} -> {v : Type} ->
  (subst : v -> List atom) -> FreeList atom v -> List atom
interpFreeListF {atom} {v} subst = cataListF v (List atom) subst interpListFAlg

public export
interpMuListF : {atom : Type} -> MuList atom -> List atom
interpMuListF {atom} = interpFreeListF {v=Void} (voidF $ List atom)

public export
(atom : Type) => Show atom => Show (MuList atom) where
  show = show . interpMuListF

public export
lengthAlg : {atom : Type} -> NaturalTransformation (ListF atom) NatF
lengthAlg _ NilF = ZeroF
lengthAlg _ (ConsF _ l) = SuccF l

public export
freeLengthAlg : {atom : Type} -> FreeAdjCounit NatF (ListF atom)
freeLengthAlg = natTransFreeAlg lengthAlg

public export
lengthLF : {atom : Type} -> NaturalTransformation (FreeList atom) FreeNat
lengthLF = natTransMapFree cataListF lengthAlg

public export
ListMuSlice : Type -> Type
ListMuSlice = SliceObj . MuList

public export
ListF1 : Type -> Type -> Type
ListF1 = ListF

public export
ListFPos : Type -> Type
ListFPos = Either Unit

public export
ListFDir : {atom : Type} -> ListFPos atom -> Type
ListFDir {atom} (Left ()) = Void
ListFDir {atom} (Right x) = Unit

public export
ListFIndAlg : Type -> Type -> Type
ListFIndAlg = ListAlg

public export
ListF2 : Type -> Type
ListF2 atom = (pos : Type) -> (pos -> Type) ->
  ListFIndAlg atom pos -> ListF atom pos -> Type

public export
ListTypeAlg : Type -> Type
ListTypeAlg atom = ListAlg atom Type

public export
ListTypeMuSlice : {atom : Type} -> ListTypeAlg atom -> ListMuSlice atom
ListTypeMuSlice {atom} = cataListF {atom} Void Type (voidF Type)

public export
listMuPi : {atom : Type} -> (tyalg : ListTypeAlg atom) ->
  tyalg NilF ->
  ((x : atom) -> (ty : Type) -> ty -> tyalg (ConsF x ty)) ->
  Pi {a=(MuList atom)} $ ListTypeMuSlice {atom} tyalg
listMuPi {atom} tyalg nalg calg (InFree (TFV v)) = void v
listMuPi {atom} tyalg nalg calg (InFree (TFC l)) = case l of
  NilF => nalg
  ConsF x l' =>
    calg x (ListTypeMuSlice tyalg l') $ listMuPi tyalg nalg calg l'

--------------------------------------------
---- Fixed-width binary natural numbers ----
--------------------------------------------

public export
BinNatF : Type -> Type
BinNatF = ListF Bool

public export
BinNatAlg : Type -> Type
BinNatAlg = Algebra BinNatF

public export
FreeBinNat : Type -> Type
FreeBinNat = FreeMonad BinNatF

public export
MuBinNat : Type
MuBinNat = Mu BinNatF

public export
BinNatCoalg : Type -> Type
BinNatCoalg = Coalgebra BinNatF

public export
CofreeBinNat : Type -> Type
CofreeBinNat = CofreeComonad BinNatF

public export
NuBinNat : Type
NuBinNat = Nu BinNatF

public export
evalBinNatF : FreeFEval BinNatF
evalBinNatF = cataListF {atom=Bool}

public export
cataBinNatF : {a : Type} -> BinNatAlg a -> FreeMAlgSig BinNatF a
cataBinNatF = FAlgToFree evalBinNatF

public export
Show MuBinNat

public export
interpBinNatFListBoolAlg : BinNatAlg $ List Bool
interpBinNatFListBoolAlg = interpListFAlg {atom=Bool}

public export
interpFreeBinNatListBoolF : {v : Type} ->
  (subst : v -> List Bool) -> FreeBinNat v -> List Bool
interpFreeBinNatListBoolF = interpFreeListF {atom=Bool}

public export
interpMuBinNatListBoolF : MuBinNat -> List Bool
interpMuBinNatListBoolF = interpMuListF {atom=Bool}

public export
interpBinNatFBinAlg : BinNatAlg Bin
interpBinNatFBinAlg NilF = []
interpBinNatFBinAlg (ConsF b n) = boolToDigit b :: n

public export
interpMuBinNatBin : MuBinNat -> Bin
interpMuBinNatBin = evalBinNatF Void Bin (voidF Bin) interpBinNatFBinAlg

public export
muBinNatToNat : MuBinNat -> Nat
muBinNatToNat = toNat . interpMuBinNatBin

public export
binNatLengthAlg : NaturalTransformation BinNatF NatF
binNatLengthAlg = lengthAlg {atom=Bool}

public export
binNatLength : FreeMonadNatTrans BinNatF NatF
binNatLength = natTransMapFree evalBinNatF binNatLengthAlg

-----------------------------------------------------
---- Pairs of fixed-width binary natural numbers ----
-----------------------------------------------------

public export
data BinPairF : Type -> Type where
  BinPair : ProductF BinNatF BinNatF carrier -> BinPairF carrier

------------------------------------------------------
------------------------------------------------------
---- Idris sigma, product, and functor categories ----
------------------------------------------------------
------------------------------------------------------

public export
SigmaObject : {a : Type} -> (a -> Type) -> Type
SigmaObject {a} b = DPair a b

public export
SigmaMorphism : {a, a' : Type} ->
  (a -> Type) -> (a' -> Type) -> (a -> a') -> Type
SigmaMorphism {a} b b' f = (x : a) -> b x -> b' (f x)

public export
sigmaCompose : {a, a', a'' : Type} ->
  {b : a -> Type} -> {b' : a' -> Type} -> {b'' : a'' -> Type} ->
  {f' : a' -> a''} -> {f : a -> a'} ->
  SigmaMorphism b' b'' f' ->
  SigmaMorphism b b' f ->
  SigmaMorphism b b'' (f' . f)
sigmaCompose {f} m' m x y = m' (f x) $ m x y

-- The objects of a product category, where the product is represented by
-- a function from an index type (as opposed to by a pair or a list -- the
-- function type allows the assignment of names from a user-selected domain,
-- and the definition of the category of endofunctors on Idris's `Type`
-- by specializing the index to `Type`).
public export
ProductCatObject : Type -> Type
ProductCatObject = SliceObj

public export
FunctorCatObject : Type
FunctorCatObject = ProductCatObject Type

public export
ProductCatMorphism : {idx : Type} ->
  ProductCatObject idx -> ProductCatObject idx -> Type
ProductCatMorphism {idx} = SliceMorphism {a=idx}

public export
FunctorCatMorphism : FunctorCatObject -> FunctorCatObject -> Type
FunctorCatMorphism = ProductCatMorphism {idx=Type}

public export
ProductCatObjectMap : Type -> Type -> Type
ProductCatObjectMap = SliceFunctor

public export
FunctorCatObjectMap : Type
FunctorCatObjectMap = ProductCatObjectMap Type Type

public export
ProductCatObjectEndoMap : Type -> Type
ProductCatObjectEndoMap idx = ProductCatObjectMap idx idx

public export
FunctorCatObjectEndoMap : Type
FunctorCatObjectEndoMap = ProductCatObjectEndoMap Type

public export
ProductCatMorphismMap :
  {idx, idx' : Type} -> ProductCatObjectMap idx idx' -> Type
ProductCatMorphismMap {idx} {idx'} = SliceFunctorMap {x=idx} {y=idx'}

public export
FunctorCatMorphismMap : FunctorCatObjectMap -> Type
FunctorCatMorphismMap = ProductCatMorphismMap {idx=Type} {idx'=Type}

public export
ProductCatMorphismEndoMap : {idx : Type} -> ProductCatObjectEndoMap idx -> Type
ProductCatMorphismEndoMap = ProductCatMorphismMap

public export
FunctorCatMorphismEndoMap : FunctorCatObjectEndoMap -> Type
FunctorCatMorphismEndoMap = ProductCatMorphismEndoMap {idx=Type}

public export
ProductCatFunctor : Type -> Type -> Type
ProductCatFunctor idx idx' =
  DPair (ProductCatObjectMap idx idx') ProductCatMorphismMap

public export
FunctorCatFunctor : Type
FunctorCatFunctor = ProductCatFunctor Type Type

public export
ProductCatEndofunctor : Type -> Type
ProductCatEndofunctor idx = ProductCatFunctor idx idx

public export
FunctorCatEndofunctor : Type
FunctorCatEndofunctor = ProductCatEndofunctor Type

----------------------------------------------------------------------
----------------------------------------------------------------------
---- Categorial algebra on sigma, product, and functor categories ----
----------------------------------------------------------------------
----------------------------------------------------------------------

-- The version of `Algebra` for an Idris product category.
public export
ProductCatAlgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> Type
ProductCatAlgebra f a = ProductCatMorphism (f a) a

-- The version of `Coalgebra` for an Idris product category.
public export
ProductCatCoalgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> Type
ProductCatCoalgebra f a = ProductCatMorphism a (f a)

-- The product-category version of `TranslateFunctor`.  In the case of just two
-- categories, for example, if `F` and `G` are the components of the input
-- functor, each going from the product category to one of the components,
-- and `v` and `w` are the components of the variable type, then this
-- expression becomes:
--
--  `FGvw[x,y] = (v + F[x,y], w + G[x,y])`
public export
data ProductCatTermFunctor : {idx : Type} ->
    ProductCatObjectEndoMap idx ->
    ProductCatObject idx ->
    ProductCatObjectEndoMap idx where
  ProductCatTermVar : {idx : Type} ->
    {f : ProductCatObjectEndoMap idx} ->
    {0 v, a : ProductCatObject idx} ->
    {i : idx} ->
    v i -> ProductCatTermFunctor f v a i
  ProductCatTermComposite : {idx : Type} ->
    {f : ProductCatObjectEndoMap idx} ->
    {0 v, a : ProductCatObject idx} ->
    {i : idx} ->
    f a i -> ProductCatTermFunctor f v a i

-- The dual of `ProductCatTermFunctor`, also known as the product-category
-- version of `ScaleFunctor`.
public export
data ProductCatTreeFunctor : {idx : Type} ->
    ProductCatObjectEndoMap idx ->
    ProductCatObject idx ->
    ProductCatObjectEndoMap idx where
  ProductCatTreeNode : {idx : Type} ->
    {f : ProductCatObjectEndoMap idx} ->
    {0 l, a : ProductCatObject idx} ->
    {i : idx} ->
    l i -> f a i -> ProductCatTreeFunctor f l a i

public export
ProductCatTermCoalgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> ProductCatObject idx ->
  Type
ProductCatTermCoalgebra f v a =
  ProductCatCoalgebra (ProductCatTermFunctor f v) a

export
treeLabelProduct : ProductCatTreeFunctor f l a i -> l i
treeLabelProduct (ProductCatTreeNode a' _) = a'

export
treeSubtreeProduct : ProductCatTreeFunctor f l a i -> f a i
treeSubtreeProduct (ProductCatTreeNode _ fx) = fx

public export
ProductCatTrAlgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> ProductCatObject idx ->
  Type
ProductCatTrAlgebra f v a =
  ProductCatAlgebra (ProductCatTermFunctor f v) a

public export
ProductCatTreeCoalgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> ProductCatObject idx ->
  Type
ProductCatTreeCoalgebra f v a =
  ProductCatCoalgebra (ProductCatTreeFunctor f v) a

public export
ProductCatTreeAlgebra : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx -> ProductCatObject idx ->
  Type
ProductCatTreeAlgebra f v a =
  ProductCatAlgebra (ProductCatTreeFunctor f v) a

-- The product-category version of `FreeMonad`.
public export
data ProductCatFreeMonad : {idx : Type} ->
    ProductCatObjectEndoMap idx -> ProductCatObjectEndoMap idx where
  InFreeProduct : {idx : Type} ->
    {f : ProductCatObjectEndoMap idx} -> {0 a : ProductCatObject idx} ->
    ProductCatTrAlgebra f a (ProductCatFreeMonad f a)

public export
data ProductCatCofreeComonad : {idx : Type} ->
    ProductCatObjectEndoMap idx -> ProductCatObjectEndoMap idx where
  InCofreeProduct : {idx : Type} ->
    {f : ProductCatObjectEndoMap idx} -> {l : ProductCatObject idx} ->
    {i : idx} ->
    Inf (ProductCatTreeFunctor f l (ProductCatCofreeComonad f l) i) ->
    ProductCatCofreeComonad f l i

public export
inFreeVarProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} -> {0 a : ProductCatObject idx} ->
  ProductCatCoalgebra (ProductCatFreeMonad f) a
inFreeVarProduct i = InFreeProduct i . ProductCatTermVar

public export
inFreeCompositeProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} -> {a : ProductCatObject idx} ->
  ProductCatAlgebra f (ProductCatFreeMonad f a)
inFreeCompositeProduct i = InFreeProduct i . ProductCatTermComposite

public export
outFreeProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} -> {a : ProductCatObject idx} ->
  ProductCatTermCoalgebra f a (ProductCatFreeMonad f a)
outFreeProduct i (InFreeProduct i x) = x

public export
inCofreeTreeProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} ->
  {l : ProductCatObject idx} ->
  {i : idx} ->
  l i ->
  f (ProductCatCofreeComonad f l) i ->
  ProductCatCofreeComonad f l i
inCofreeTreeProduct x fx = InCofreeProduct $ ProductCatTreeNode x fx

public export
outCofreeProduct : {idx : Type} ->
  {f : ProductCatObjectEndoMap idx} -> {l : ProductCatObject idx} ->
  {i : idx} ->
  ProductCatCofreeComonad f l i ->
  ProductCatTreeFunctor f l (ProductCatCofreeComonad f l) i
outCofreeProduct (InCofreeProduct x) = x

public export
MuProduct : {idx : Type} -> ProductCatObjectEndoMap idx -> ProductCatObject idx
MuProduct f = ProductCatFreeMonad f (const Void)

public export
NuProduct : {idx : Type} ->
  ProductCatObjectEndoMap idx -> ProductCatObject idx
NuProduct f = ProductCatCofreeComonad f (const ())

public export
ProductCatFreeFEval : {idx : Type} -> ProductCatObjectEndoMap idx -> Type
ProductCatFreeFEval f =
  (v, a : ProductCatObject idx) ->
  ProductCatTrAlgebra f v a ->
  ProductCatMorphism (ProductCatFreeMonad f v) a

public export
ProductCatParamAna : {idx : Type} ->
  ProductCatObjectEndoMap idx ->
  Type
ProductCatParamAna f =
  (v, l : ProductCatObject idx) ->
  ProductCatTreeCoalgebra f v l ->
  ProductCatMorphism (ProductCatCofreeComonad f v) l

public export
ProductCatamorphism : {idx : Type} -> ProductCatObjectEndoMap idx -> Type
ProductCatamorphism {idx} f =
  (a : ProductCatObject idx) ->
  ProductCatAlgebra f a ->
  ProductCatMorphism (MuProduct f) a

public export
ProductAnamorphism : {idx : Type} -> ProductCatObjectEndoMap idx -> Type
ProductAnamorphism {idx} f =
  (a : ProductCatObject idx) ->
  ProductCatCoalgebra f a ->
  ProductCatMorphism a (NuProduct f)

---------------------------------
---------------------------------
---- Finite bicomplete types ----
---------------------------------
---------------------------------

public export
data FiniteTypeF : Type -> Type where
  FinVoidF : FiniteTypeF carrier
  FinUnitF : FiniteTypeF carrier
  FinProductF :
    (FiniteTypeF carrier, FiniteTypeF carrier) -> FiniteTypeF carrier
  FinCoproductF :
    (FiniteTypeF carrier, FiniteTypeF carrier) -> FiniteTypeF carrier

public export
data FiniteType : Type -> Type where
  FinVoid : FiniteType Void
  FinUnit : FiniteType Unit
  FinProduct : {erasedFst, erasedSnd : Type} ->
    FiniteType erasedFst -> FiniteType erasedSnd ->
    FiniteType (erasedFst, erasedSnd)
  FinCoproduct : {erasedL, erasedR : Type} ->
    FiniteType erasedL -> FiniteType erasedR ->
    FiniteType (Either erasedL erasedR)

public export
data FiniteBicompleteType :
    {metaType : Type} -> FiniteType metaType -> Type where
  InFinite : {metaType : Type} ->
    (erased : FiniteType metaType) -> FiniteBicompleteType {metaType} erased

----------------------------------------------------------
----------------------------------------------------------
---- Categories represented by metalanguage functions ----
----------------------------------------------------------
----------------------------------------------------------

-- We define a notion of a type which can be represented by a metalanguage
-- function.

public export
ObjRepresentation : Type -> Type -> Type
ObjRepresentation represented representing =
  represented -> (representing -> representing)

public export
ObjRepresenting : Type -> Type
ObjRepresenting = DPair Type . ObjRepresentation

public export
ObjRepresentedBy : Type -> Type
ObjRepresentedBy = DPair Type . flip ObjRepresentation

-- We may represent functions between function-represented types as
-- ways of translating back and forth between the types underlying
-- the representations of the domain and codomain.  This type
-- defines the representation of one particular function.  Note that
-- this is still non-trivial even if `domRep` and `codRep` are the
-- same -- in that case we might not call it "translating", but it can
-- still be "rearranging".
public export
FunctionRepresentation : (domRep, codRep : Type) -> Type
FunctionRepresentation domRep codRep = (codRep -> domRep, domRep -> codRep)

public export
transformRep : {domain, domRep, codomain, codRep : Type} ->
  (domain -> codomain) ->
  FunctionRepresentation domRep codRep ->
  ObjRepresentation domain domRep ->
  ObjRepresentation domain codRep
transformRep f (codToDom, domToCod) domRepFunc x =
  domToCod . domRepFunc x . codToDom

-- Define a notion of consistency of the representation of a particular function
-- with the representations of its domain and codomain.
public export
FuncRepCommutes : {domain, domRep, codomain, codRep : Type} ->
  (domRepFunc : ObjRepresentation domain domRep) ->
  (codRepFunc : ObjRepresentation codomain codRep) ->
  (domain -> codomain) ->
  FunctionRepresentation domRep codRep -> Type
FuncRepCommutes {domRep} {codRep} domRepFunc codRepFunc f funcRep =
  ExtEq (codRepFunc . f) (transformRep f funcRep domRepFunc)

public export
CommutingFuncRep : {domain, domRep, codomain, codRep : Type} ->
  (domRepFunc : ObjRepresentation domain domRep) ->
  (codRepFunc : ObjRepresentation codomain codRep) ->
  (domain -> codomain) -> Type
CommutingFuncRep domRepFunc codRepFunc f =
  DPair
    (FunctionRepresentation domRep codRep)
    (FuncRepCommutes domRepFunc codRepFunc f)

public export
HomObjRep : {domain, domRep, codomain, codRep : Type} ->
  (domRepFunc : ObjRepresentation domain domRep) ->
  (codRepFunc : ObjRepresentation codomain codRep) ->
  Type
HomObjRep domRepFunc codRepFunc =
  (f : domain -> codomain) -> CommutingFuncRep domRepFunc codRepFunc f

-- We now define a notion of a category with the following properties
-- (together with the standard axioms of category theory):
--  - Every object and morphism has a representation as a metalanguage function
--    (the objects all share a representation, but representations of morphisms
--    with one signature are allowed to differ from those with other signatures)
--  - All of those representations satisfy `FuncRepCommutes` above
--  - All of the representation functions have decidable extensional equalities
--    (this does not only mean that there is a decidable equality for each
--    input value, but rather the stronger condition that we can decide the
--    extensional equality of entire functions)
--  - Equality on objects and morphisms is given by extensional equality of
--    their metalanguage representations
-- We shall call such a category "decidably representable".
public export
record DecRepCat (obj, morph : Type) where
  constructor MkDecRepCat

  -- Each object is represented by an endomorphism on a type
  -- which we call `DecRepObjRepType`.
  DecRepObjRepType : Type
  DecRepObjRep : ObjRepresentation obj DecRepObjRepType

  -- We allow each hom-set to use a different representation.
  -- (The _object_ representation functions for the domain and
  -- codomain are the same, however, because the whole category
  -- shares one object representation function.  The reason for that
  -- is that it creates a monoid on objects, allowing them to be
  -- composed.)
  DecRepMorphRep : obj -> obj -> HomObjRep DecRepObjRep DecRepObjRep

  -- We represent the relationship of objects and morphisms by fibrations,
  -- rather than by dependent types.  That's partly convenient in that it's
  -- more in the style of category theory, but the more fundmental reason is
  -- that we are treating equality of objects and morphisms as quotiented
  -- over the extensional equivalence of the representations.
  -- So we might, for example, be able to compose `g : c -> d` after
  -- `f : a -> b` even if we can't prove that `b = c`, because the
  -- functions which _represent_ `b` and `c` might be extensionally equal.
  DecRepId : obj -> morph
  DecRepCompose : morph -> morph -> morph
  DecRepSignature : morph -> (obj, obj)

-----------------------------------------------------------
-----------------------------------------------------------
---- Interpretations and representations of categories ----
-----------------------------------------------------------
-----------------------------------------------------------

-- First, we define the notion of a category which is interpreted into
-- functions of the metalanguage.
--
-- Interpretation means mapping morphisms of the category into metalanguage
-- functions which correspond to their _meaning_.  A category which can be
-- interpreted into the metalanguage must be no stronger as a logic than the
-- metalanguage.
public export
record MetaCat where
  constructor MkMetaCat
  -- The types of `Type` which represent the objects and morphisms of the
  -- interpreted category.
  MetaObj : Type
  MetaMorphism : MetaObj -> MetaObj -> Type

  -- Identity and composition.
  MetaId : (a : MetaObj) -> MetaMorphism a a
  MetaCompose : (a, b, c : MetaObj) ->
    MetaMorphism b c -> MetaMorphism a b -> MetaMorphism a c

  -- The interpretations of the objects and morphisms of the category.
  MetaObjInterp : MetaObj -> Type
  MetaMorphismInterp : (a, b : MetaObj) ->
    MetaMorphism a b -> MetaObjInterp a -> MetaObjInterp b

public export
record MetaCatCorrect (cat : MetaCat) where
  constructor MkMetaCatCorrect
  -- Correctness conditions (the axioms of category theory), with
  -- equality up to first-order (non-recursive) extensional equality of the
  -- of the morphisms as metalanguage functions.
  MetaLeftId : {a, b : MetaObj cat} ->
    (f : MetaMorphism cat a b) ->
    ExtEq
      (MetaMorphismInterp cat a b (MetaCompose cat a b b (MetaId cat b) f))
      (MetaMorphismInterp cat a b f)
  MetaRightId : {a, b : MetaObj cat} ->
    (f : MetaMorphism cat a b) ->
    ExtEq
      (MetaMorphismInterp cat a b f)
      (MetaMorphismInterp cat a b (MetaCompose cat a a b f (MetaId cat a)))
  MetaAssoc : {a, b, c, d : MetaObj cat} ->
    (h : MetaMorphism cat c d) ->
    (g : MetaMorphism cat b c) ->
    (f : MetaMorphism cat a b) ->
    ExtEq
      (MetaMorphismInterp cat a d
        (MetaCompose cat a c d h (MetaCompose cat a b c g f)))
      (MetaMorphismInterp cat a d
        (MetaCompose cat a b d (MetaCompose cat b c d h g) f))

public export
MorphismEq : {cat : MetaCat} -> {a, b : MetaObj cat} ->
  MetaMorphism cat a b -> MetaMorphism cat a b -> Type
MorphismEq m m' =
  ExtEq (MetaMorphismInterp cat a b m) (MetaMorphismInterp cat a b m')

public export
TypeTensorProd : Type
TypeTensorProd = Type -> Type -> Type

-- Because we are going to enrich further categories over
-- `MetaCat`s, we define a version of `MetaCat` that has a tensor product, whose
-- properties we ensure by requiring that it be interpreted as the
-- product in `Type` (known as `Pair`).
record MonoidalCat (typeProd : TypeTensorProd) (underlying : MetaCat) where
  constructor MkMonoidalCat
  MetaTensorObj : MetaObj underlying -> MetaObj underlying -> MetaObj underlying
  MetaTensorId : MetaObj underlying
  MetaTensorObjInterp : (a, b : MetaObj underlying) ->
    MetaObjInterp underlying (MetaTensorObj a b) ->
    typeProd (MetaObjInterp underlying a) (MetaObjInterp underlying b)
  MetaTensorObjInterpInv : (a, b : MetaObj underlying) ->
    typeProd (MetaObjInterp underlying a) (MetaObjInterp underlying b) ->
    MetaObjInterp underlying (MetaTensorObj a b)
  MetaTensorMorph : {a, b, c, d : MetaObj underlying} ->
    MetaMorphism underlying a c -> MetaMorphism underlying b d ->
    MetaMorphism underlying (MetaTensorObj a b) (MetaTensorObj c d)

public export
record MonoidalCatCorrect
    (typeProd : TypeTensorProd)
    (underlying : MetaCat)
    (monCat : MonoidalCat typeProd underlying) where
  constructor MkMonoidalCatCorrect
  MetaTensorObjInterpCorrect : (a, b : MetaObj underlying) ->
    ExtInverse
      (MetaTensorObjInterpInv monCat a b)
      (MetaTensorObjInterp monCat a b)

public export
CartesianCat : MetaCat -> Type
CartesianCat = MonoidalCat Pair

public export
BiCartesianCat : MetaCat -> Type
BiCartesianCat underlying =
  (CartesianCat underlying, MonoidalCat Either underlying)

public export
HomObj : TypeTensorProd
HomObj a b = a -> b

public export
ExponentialClosedCat : MetaCat -> Type
ExponentialClosedCat = MonoidalCat HomObj

public export
CartesianClosedCat : MetaCat -> Type
CartesianClosedCat underlying =
  (CartesianCat underlying, ExponentialClosedCat underlying)

public export
BicartesianClosedCat : MetaCat -> Type
BicartesianClosedCat underlying =
  (CartesianClosedCat underlying, MonoidalCat Either underlying)

public export
record MetaFunctor (catC, catD : MetaCat) where
  constructor MkMetaFunctor
  MetaFunctorObjMap : MetaObj catC -> MetaObj catD
  MetaFunctorMorphMap : {a, b : MetaObj catC} ->
      MetaMorphism catC a b ->
      MetaMorphism catD (MetaFunctorObjMap a) (MetaFunctorObjMap b)

public export
record MetaFunctorCorrect
    {catC, catD : MetaCat} (functor : MetaFunctor catC catD) where
  -- Correctness conditions.
  MetaFunctorId : (a : MetaObj catC) ->
    MorphismEq
      {cat=catD}
      {a=(MetaFunctorObjMap functor a)} {b=(MetaFunctorObjMap functor a)}
      (MetaFunctorMorphMap functor {a} {b=a} (MetaId catC a))
      (MetaId catD (MetaFunctorObjMap functor a))
  MetaFunctorCompose : {a, b, c : MetaObj catC} ->
    (g : MetaMorphism catC b c) ->
    (f : MetaMorphism catC a b) ->
    MorphismEq
      {cat=catD}
      {a=(MetaFunctorObjMap functor a)} {b=(MetaFunctorObjMap functor c)}
      (MetaFunctorMorphMap functor {a} {b=c} (MetaCompose catC a b c g f))
      (MetaCompose catD
        (MetaFunctorObjMap functor a)
        (MetaFunctorObjMap functor b)
        (MetaFunctorObjMap functor c)
        (MetaFunctorMorphMap functor {a=b} {b=c} g)
        (MetaFunctorMorphMap functor {a} {b} f))

public export
record FunctorEq {catC, catD : MetaCat} (f, g : MetaFunctor catC catD) where
  constructor MkFunctorEq
  ObjMapEq : (a : MetaObj catC) -> MetaFunctorObjMap f a = MetaFunctorObjMap g a
  MorphMapEq : {a, b : MetaObj catC} -> (m : MetaMorphism catC a b) ->
    MorphismEq
      {cat=catD}
      {a=(MetaFunctorObjMap f a)} {b=(MetaFunctorObjMap f b)}
      (MetaFunctorMorphMap f {a} {b} m)
      (replace
        {p=(\a' : MetaObj catD => MetaMorphism catD a' (MetaFunctorObjMap f b))}
        (sym (ObjMapEq a)) $
       replace
        {p=(\b' : MetaObj catD => MetaMorphism catD (MetaFunctorObjMap g a) b')}
        (sym (ObjMapEq b))
        (MetaFunctorMorphMap g {a} {b} m))

public export
IdFunctor : (cat : MetaCat) -> MetaFunctor cat cat
IdFunctor cat = MkMetaFunctor id id

public export
0 IdFunctorCorrect : (cat : MetaCat) -> MetaFunctorCorrect (IdFunctor cat)
IdFunctorCorrect cat = ?IdFunctorCorrect_hole

public export
ComposeFunctor : {catC, catD, catE : MetaCat} ->
  MetaFunctor catD catE -> MetaFunctor catC catD ->
  MetaFunctor catC catE
ComposeFunctor g f = MkMetaFunctor
  (MetaFunctorObjMap g . MetaFunctorObjMap f)
  (MetaFunctorMorphMap g . MetaFunctorMorphMap f)

public export
0 ComposeFunctorCorrect : {catC, catD, catE : MetaCat} ->
  (g : MetaFunctor catD catE) -> (f : MetaFunctor catC catD) ->
  MetaFunctorCorrect (ComposeFunctor g f)
ComposeFunctorCorrect g f = ?ComposeFunctorCorrect_hole

public export
MetaFunctorInterp : {catC, catD : MetaCat} -> MetaFunctor catC catD -> Type
MetaFunctorInterp {catC} {catD} f =
  (a : MetaObj catC) ->
  MetaObjInterp catC a ->
  MetaObjInterp catD (MetaFunctorObjMap f a)

public export
MetaEndoFunctor : MetaCat -> Type
MetaEndoFunctor cat = MetaFunctor cat cat

public export
record MetaNatTrans {catC, catD : MetaCat} (f, g : MetaFunctor catC catD) where
  constructor MkMetaNatTrans
  -- Components of the natural transformation.
  MetaNTComponent : (a : MetaObj catC) ->
    MetaMorphism catD (MetaFunctorObjMap f a) (MetaFunctorObjMap g a)

public export
record MetaNatTransCorrect {catC, catD : MetaCat} {f, g : MetaFunctor catC catD}
    (natTrans : MetaNatTrans f g) where
  constructor MkMetaNatTransCorrect
  -- Correctness conditions.
  MetaNTNaturality : (a, b : MetaObj catC) -> (m : MetaMorphism catC a b) ->
    MorphismEq
      {cat=catD} {a=(MetaFunctorObjMap f a)} {b=(MetaFunctorObjMap g b)}
      (MetaCompose catD
        (MetaFunctorObjMap f a)
        (MetaFunctorObjMap f b)
        (MetaFunctorObjMap g b)
        (MetaNTComponent natTrans b)
        (MetaFunctorMorphMap {catC} {catD} {a} {b} f m))
      (MetaCompose catD
        (MetaFunctorObjMap f a)
        (MetaFunctorObjMap g a)
        (MetaFunctorObjMap g b)
        (MetaFunctorMorphMap {catC} {catD} {a} {b} g m)
        (MetaNTComponent natTrans a))

public export
record NatTransEq {catC, catD : MetaCat} {f, f', g, g' : MetaFunctor catC catD}
    (alpha : MetaNatTrans f g) (beta : MetaNatTrans f' g') where
  constructor MkNatTransEq
  ntEqF : FunctorEq f f'
  ntEqG : FunctorEq g g'
  ntEqComponent : (a : MetaObj catC) ->
    MorphismEq
      {cat=catD}
      {a=(MetaFunctorObjMap f a)} {b=(MetaFunctorObjMap g a)}
      (MetaNTComponent alpha a)
      (replace
        {p=(\a' => MetaMorphism catD a' (MetaFunctorObjMap g a))}
        (sym (ObjMapEq ntEqF a)) $
       replace
        {p=(\a' => MetaMorphism catD (MetaFunctorObjMap f' a) a')}
        (sym (ObjMapEq ntEqG a))
        (MetaNTComponent beta a))

public export
IdNatTrans : {catC, catD : MetaCat} -> (f : MetaFunctor catC catD) ->
  MetaNatTrans f f
IdNatTrans {catC} f = MkMetaNatTrans $
  \a => MetaFunctorMorphMap f (MetaId catC a)

public export
0 IdNatTransCorrect : {catC, catD : MetaCat} -> (f : MetaFunctor catC catD) ->
  MetaNatTransCorrect (IdNatTrans f)
IdNatTransCorrect = ?IdNatTransCorrect_hole

public export
IdNatTransIdF : (c : MetaCat) -> MetaNatTrans (IdFunctor c) (IdFunctor c)
IdNatTransIdF c = MkMetaNatTrans $ \a => MetaId c a

public export
VerticalCompose : {catC, catD : MetaCat} -> {f, g, h : MetaFunctor catC catD} ->
  MetaNatTrans g h -> MetaNatTrans f g -> MetaNatTrans f h
VerticalCompose {catC} {catD} {f} {g} {h} beta alpha = MkMetaNatTrans $
  \a => MetaCompose catD
    (MetaFunctorObjMap f a)
    (MetaFunctorObjMap g a)
    (MetaFunctorObjMap h a)
    (MetaNTComponent beta a)
    (MetaNTComponent alpha a)

public export
0 VerticalComposeCorrect :
  {catC, catD : MetaCat} ->
  {f, g, h : MetaFunctor catC catD} ->
  (beta : MetaNatTrans g h) -> (alpha : MetaNatTrans f g) ->
  MetaNatTransCorrect (VerticalCompose beta alpha)
VerticalComposeCorrect = ?VerticalComposeCorrect_hole

public export
HorizontalCompose : {catC, catD, catE : MetaCat} ->
  {f, f' : MetaFunctor catC catD} -> {g, g' : MetaFunctor catD catE} ->
  MetaNatTrans g g' ->
  MetaNatTrans f f' ->
  MetaNatTrans (ComposeFunctor g f) (ComposeFunctor g' f')
HorizontalCompose {catC} {catD} {f} {f'} {g} {g'} beta alpha = MkMetaNatTrans $
  \a => MetaCompose catE
    (MetaFunctorObjMap (ComposeFunctor g f) a)
    (MetaFunctorObjMap (ComposeFunctor g f') a)
    (MetaFunctorObjMap (ComposeFunctor g' f') a)
    (MetaNTComponent beta (MetaFunctorObjMap f' a))
    (MetaFunctorMorphMap
      {a=(MetaFunctorObjMap f a)}
      {b=(MetaFunctorObjMap f' a)}
      g
      (MetaNTComponent alpha a))

public export
0 HorizontalComposeCorrect : {catC, catD, catE : MetaCat} ->
  {f, f' : MetaFunctor catC catD} -> {g, g' : MetaFunctor catD catE} ->
  (beta : MetaNatTrans g g') -> (alpha : MetaNatTrans f f') ->
  MetaNatTransCorrect (HorizontalCompose beta alpha)
HorizontalComposeCorrect = ?HorizontalComposeCorrect_hole

public export
0 HorizontalComposeConsistent : {catC, catD, catE : MetaCat} ->
  {f, f' : MetaFunctor catC catD} -> {g, g' : MetaFunctor catD catE} ->
  (beta : MetaNatTrans g g') ->
  (alpha : MetaNatTrans f f') ->
  MetaNatTransCorrect beta ->
  MetaNatTransCorrect alpha ->
  (a : MetaObj catC) ->
    MorphismEq
      {cat=catE}
      {a=(MetaFunctorObjMap (ComposeFunctor g f) a)}
      {b=(MetaFunctorObjMap (ComposeFunctor g' f') a)}
      (MetaNTComponent (HorizontalCompose beta alpha) a)
      (MetaCompose catE
        (MetaFunctorObjMap (ComposeFunctor g f) a)
        (MetaFunctorObjMap (ComposeFunctor g' f) a)
        (MetaFunctorObjMap (ComposeFunctor g' f') a)
        (MetaFunctorMorphMap
          {a=(MetaFunctorObjMap f a)}
          {b=(MetaFunctorObjMap f' a)}
          g'
          (MetaNTComponent alpha a))
        (MetaNTComponent beta (MetaFunctorObjMap f a)))
HorizontalComposeConsistent = ?HorizontalComposeConsistent_hole

public export
MetaNatTransInterp : {catC, catD : MetaCat} -> (f, g : MetaFunctor catC catD) ->
  MetaNatTrans f g -> MetaFunctorInterp f -> MetaFunctorInterp g
MetaNatTransInterp _ _ alpha finterp a =
  (MetaMorphismInterp _ _ _ (MetaNTComponent alpha a)) . (finterp a)

public export
WhiskerLeft : {catB, catC, catD : MetaCat} -> {f, g : MetaFunctor catC catD} ->
  (nu : MetaNatTrans f g) -> (k : MetaFunctor catB catC) ->
  MetaNatTrans (ComposeFunctor f k) (ComposeFunctor g k)
WhiskerLeft {catB} {catC} {catD} {f} {g} nu k = MkMetaNatTrans $
  \a => MetaNTComponent nu $ MetaFunctorObjMap k a

public export
0 WhiskerLeftCorrect :
  {catB, catC, catD : MetaCat} ->
  {f, g : MetaFunctor catC catD} ->
  (nu : MetaNatTrans f g) -> (k : MetaFunctor catB catC) ->
  MetaNatTransCorrect (WhiskerLeft nu k)
WhiskerLeftCorrect = ?WhiskerLeftCorrect_hole

public export
WhiskerRight : {catC, catD, catE : MetaCat} -> {f, g : MetaFunctor catC catD} ->
  (h : MetaFunctor catD catE) -> (nu : MetaNatTrans f g) ->
  MetaNatTrans (ComposeFunctor h f) (ComposeFunctor h g)
WhiskerRight h nu = MkMetaNatTrans $
  \a => MetaFunctorMorphMap h $ MetaNTComponent nu a

public export
0 WhiskerRightCorrect :
  {catC, catD, catE : MetaCat} ->
  {f, g : MetaFunctor catC catD} ->
  (h : MetaFunctor catD catE) -> (nu : MetaNatTrans f g) ->
  MetaNatTransCorrect (WhiskerRight h nu)
WhiskerRightCorrect = ?WhiskerRightCorrect_hole

public export
record Adjunction (catC, catD : MetaCat) where
  constructor MkAdjunction
  leftAdjoint : MetaFunctor catD catC
  rightAdjoint : MetaFunctor catC catD
  adjUnit :
    MetaNatTrans (IdFunctor catD) (ComposeFunctor rightAdjoint leftAdjoint)
  adjCounit :
    MetaNatTrans (ComposeFunctor leftAdjoint rightAdjoint) (IdFunctor catC)

public export
record AdjunctionCorrect
    {catC, catD : MetaCat} (adj : Adjunction catC catD) where
  constructor MkAdjunctionCorrect
  triangleLeft :
    NatTransEq
      (VerticalCompose
        (WhiskerLeft (adjCounit adj) (leftAdjoint adj))
        (WhiskerRight (leftAdjoint adj) (adjUnit adj)))
      (IdNatTrans (leftAdjoint adj))
  triangleRight :
    NatTransEq
      (VerticalCompose
        (WhiskerRight (rightAdjoint adj) (adjCounit adj))
        (WhiskerLeft (adjUnit adj) (rightAdjoint adj)))
      (IdNatTrans (rightAdjoint adj))

public export
record AdjunctionEq
    {catC, catD : MetaCat} (adj, adj' : Adjunction catC catD) where
  constructor MkAdjunctionEq
  leftAdjointEq : FunctorEq (leftAdjoint adj) (leftAdjoint adj')
  rightAdjointEq : FunctorEq (rightAdjoint adj) (rightAdjoint adj')
  unitEq : NatTransEq (adjUnit adj) (adjUnit adj')
  counitEq : NatTransEq (adjCounit adj) (adjCounit adj')

public export
IdAdjunction : (c : MetaCat) -> Adjunction c c
IdAdjunction c = MkAdjunction
  (IdFunctor c)
  (IdFunctor c)
  (IdNatTransIdF c)
  (IdNatTransIdF c)

public export
0 IdAdjunctionCorrect : (c : MetaCat) -> AdjunctionCorrect (IdAdjunction c)
IdAdjunctionCorrect = ?IdAdjunctionCorrect_hole

public export
ComposeAdjunction : {catC, catD, catE : MetaCat} ->
  Adjunction catD catE -> Adjunction catC catD -> Adjunction catC catE
ComposeAdjunction {catC} {catD} {catE} adjr adjl = MkAdjunction
  (ComposeFunctor (leftAdjoint adjl) (leftAdjoint adjr))
  (ComposeFunctor (rightAdjoint adjr) (rightAdjoint adjl))
  (VerticalCompose
    (WhiskerRight
      (rightAdjoint adjr) (WhiskerLeft (adjUnit adjl) (leftAdjoint adjr)))
    (adjUnit adjr))
  (VerticalCompose
    (adjCounit adjl)
    (WhiskerLeft
      (WhiskerRight (leftAdjoint adjl) (adjCounit adjr)) (rightAdjoint adjl)))

public export
0 ComposeAdjunctionCorrect : {c, d, e : MetaCat} ->
  (adjr : Adjunction d e) -> (adjl : Adjunction c d) ->
  AdjunctionCorrect (ComposeAdjunction adjr adjl)
ComposeAdjunctionCorrect {c} {d} {e} adjr adjl = ?ComposeAdjunctionCorrect_hole

public export
LeftAdjunct : {catC, catD : MetaCat} -> (adj : Adjunction catC catD) ->
  {a : MetaObj catD} -> {b : MetaObj catC} ->
  MetaMorphism catC (MetaFunctorObjMap (leftAdjoint adj) a) b ->
  MetaMorphism catD a (MetaFunctorObjMap (rightAdjoint adj) b)
LeftAdjunct {catC} {catD} adj {a} {b} f =
  MetaCompose catD
    a
    (MetaFunctorObjMap
      (rightAdjoint adj) (MetaFunctorObjMap (leftAdjoint adj) a))
    (MetaFunctorObjMap (rightAdjoint adj) b)
    (MetaFunctorMorphMap (rightAdjoint adj) f)
    (MetaNTComponent (adjUnit adj) a)

public export
RightAdjunct : {catC, catD : MetaCat} -> (adj : Adjunction catC catD) ->
  {a : MetaObj catD} -> {b : MetaObj catC} ->
  MetaMorphism catD a (MetaFunctorObjMap (rightAdjoint adj) b) ->
  MetaMorphism catC (MetaFunctorObjMap (leftAdjoint adj) a) b
RightAdjunct {catC} {catD} adj {a} {b} g =
  MetaCompose catC
    (MetaFunctorObjMap (leftAdjoint adj) a)
    (MetaFunctorObjMap
      (leftAdjoint adj) (MetaFunctorObjMap (rightAdjoint adj) b))
    b
    (MetaNTComponent (adjCounit adj) b)
    (MetaFunctorMorphMap (leftAdjoint adj) g)

public export
MetaFunctorCat : MetaCat -> MetaCat -> MetaCat
MetaFunctorCat catC catD =
  MkMetaCat
    (MetaFunctor catC catD)
    MetaNatTrans
    IdNatTrans
    (\f, g, h => VerticalCompose {f} {g} {h})
    MetaFunctorInterp
    MetaNatTransInterp

public export
0 FunctorCatCorrect : {catC, catD : MetaCat} ->
  MetaCatCorrect catC -> MetaCatCorrect catD ->
  MetaCatCorrect (MetaFunctorCat catC catD)
FunctorCatCorrect {catC} {catD} cC cD = ?FunctorCatCorrect_hole

-- tensor product interpreted as "Either" (in particular for directed colimits)
-- distributive category (with Pair _and_ Either tensor products)
-- functor cat
-- nat trans cat
-- adjunction cat
-- comma cat

-- diagrams

-- A 2-category (or higher) enriched over the metalanguage's `Type`, together
-- with an interpretation into `Type`, with morphism equality defined by
-- (non-recursive) extensional equality of functions.
-- more to it (nat transes, adjunctions)

---------------------------
---------------------------
---- Directed colimits ----
---------------------------
---------------------------

public export
CFunctorIter : {cat : MetaCat} ->
  MetaEndoFunctor cat -> NatObj -> MetaEndoFunctor cat
CFunctorIter f =
  NatObjInd
    (\_ => MetaEndoFunctor cat)
    (IdFunctor cat)
    (\_, f' => ComposeFunctor f f')

public export
CFunctorIterIndBaseCase : {cat : MetaCat} ->
  (MetaEndoFunctor cat -> Type) -> Type
CFunctorIterIndBaseCase {cat} p = p (IdFunctor cat)

public export
CFunctorIterInductionStep : {cat : MetaCat} ->
  (MetaEndoFunctor cat -> Type) -> MetaEndoFunctor cat -> Type
CFunctorIterInductionStep {cat} p f =
  (n : NatObj) ->
  p (CFunctorIter f n) ->
  p (ComposeFunctor f $ CFunctorIter f n)

public export
CFunctorIterInd : {cat : MetaCat} ->
  (0 p : MetaEndoFunctor cat -> Type) ->
  (0 f : MetaEndoFunctor cat) ->
  CFunctorIterIndBaseCase p ->
  CFunctorIterInductionStep p f ->
  (n : NatObj) -> p (CFunctorIter f n)
CFunctorIterInd p f = NatObjInd (p . CFunctorIter f)

public export
MetaFuncInterpPred : {catC, catD : MetaCat} ->
  MetaFunctor catC catD -> MetaObj catC -> Type
MetaFuncInterpPred {catD} f a =
  MetaObjInterp catD (MetaFunctorObjMap f a) -> Type

public export
CFunctorIterInterpPred : {cat : MetaCat} ->
  MetaEndoFunctor cat -> MetaObj cat -> Type
CFunctorIterInterpPred {cat} f a =
  (n : NatObj) -> MetaFuncInterpPred {catC=cat} {catD=cat} (CFunctorIter f n) a

---------------------------------------------------------
---- Coalgebras and coproducts for directed colimits ----
---------------------------------------------------------

----------------------------------------------
----------------------------------------------
---- Polynomial-functor algebra on `Type` ----
----------------------------------------------
----------------------------------------------

--------------------------------------
---- Open terms and labeled trees ----
--------------------------------------

-- For a given functor `F` and object `v`, form the functor `Fv` defined by
-- `Fv[x] = v + F[x]`.  We call it `TranslateFunctor` because it turns
-- an endofunctor which we can interpret as representing a datatype
-- into one which we can interpret as representing open terms of
-- that datatype with variables drawn from type `v`.
public export
TranslateFunctor' : (Type -> Type) -> Type -> (Type -> Type)
TranslateFunctor' f a = CoproductF (ConstF a) f

public export
Functor f => Bifunctor (TranslateFunctor' f) where
  bimap f' g' (Left x) = Left $ f' x
  bimap f' g' (Right x) = Right $ map g' x

-- For a given functor `F`, form the functor `Fa` defined by
-- `Fa[x] = a * F[x]`.  We call it `ScaleFunctor` because it turns
-- an endofunctor which we can interpret as representing a datatype
-- into one which we can interpret as representing potentially infinite
-- trees of that datatype with labels drawn from type `v`.
-- This is the dual of `TranslateFunctor`.
public export
ScaleFunctor' : (Type -> Type) -> Type -> (Type -> Type)
ScaleFunctor' f a = ProductF (ConstF a) f

export
Functor f => Bifunctor (ScaleFunctor' f) where
  bimap f' g' (x, fx) = (f' x, map g' fx)

-- The free monad of the identity functor.
public export
data FreeMId : Type -> Type where
  InIdVar : {a : Type} -> a -> FreeMId a
  InIdComposite : IdTF (FreeMId a) -> FreeMId a

public export
CoproductAlgTypeNE : (Type -> Type) -> List (Type -> Type) -> Type -> Type
CoproductAlgTypeNE f [] a = Algebra f a
CoproductAlgTypeNE f (f' :: fs) a = (Algebra f a, CoproductAlgTypeNE f' fs a)

public export
CoproductAlgType : List (Type -> Type) -> Type -> Type
CoproductAlgType [] a = Algebra InitialComonad a
CoproductAlgType (f :: fs) a = CoproductAlgTypeNE f fs a

public export
CoproductAlgLNE :
  {f : Type -> Type} -> {l : List (Type -> Type)} -> {a : Type} ->
  CoproductAlgTypeNE f l a -> Algebra (CoproductFLNE f l) a
CoproductAlgLNE {f} {l=[]} alg x = alg x
CoproductAlgLNE {f} {l=(f' :: fs)} (alg, algs) x = case x of
  Left x' => alg x'
  Right x' => CoproductAlgLNE {f=f'} {l=fs} algs x'

public export
CoproductAlgL : {l : List (Type -> Type)} -> {a : Type} ->
  CoproductAlgType l a -> Algebra (CoproductFL l) a
CoproductAlgL {l=[]} algl = \x => void x
CoproductAlgL {l=(f :: fs)} algl = CoproductAlgLNE {f} {l=fs} algl

-----------------------------------
-----------------------------------
---- Godel-numbered categories ----
-----------------------------------
-----------------------------------

--------------------------------
--------------------------------
---- Arrow-category algebra ----
--------------------------------
--------------------------------

-- The components of an object of Idris's arrow category, which is simply a
-- pair of `Type`s with a morphism between them.
public export
record Arrow where
  constructor MkArrow
  arrowTot : Type
  arrowBase : Type
  arrowProj : arrowTot -> arrowBase

-- The components of a morphism in Idris's arrow category.
public export
record ArrowMorphism (a, b : Arrow) where
  constructor MkArrowMorphism
  arrowTotMorphism : arrowTot a -> arrowTot b
  arrowBaseMorphism : arrowBase a -> arrowBase b
  arrowMorphismCommutes :
    ExtEq (arrowProj b . arrowTotMorphism) (arrowBaseMorphism . arrowProj a)

-- The type signature of an arrow functor, which can generate an arrow
-- object from an initial algebra.
public export
record ArrowFunctor where
  constructor ArrowFGen
  arrowBaseChange : Arrow ->
    Type -- change base space
  arrowCobaseChangeOnly : Arrow ->
    Type -- change total space only
  arrowCobaseChangeProj : (a : Arrow) ->
    arrowCobaseChangeOnly a -> arrowBase a
  arrowCobaseChangeDep : (a : Arrow) ->
    (newBase : arrowBaseChange a) -> Type
  arrowProjChange : (a : Arrow) ->
    (newBase : arrowBaseChange a) -> arrowCobaseChangeDep a newBase -> Type

public export
data ArrowTermFunctor : (f : ArrowFunctor) ->
    (v, a : Arrow) -> Type where
  InArrowVar : {f : ArrowFunctor} -> {v, a : Arrow} ->
    (x : arrowTot v) -> ArrowTermFunctor f v a
  InArrowBase : {f : ArrowFunctor} -> {v, a : Arrow} ->
    (base : arrowBaseChange f a) ->
    ArrowTermFunctor f v a
  InArrowCobase : {f : ArrowFunctor} -> {v, a : Arrow} ->
    (tot : arrowCobaseChangeOnly f a) ->
    ArrowTermFunctor f v a
  InArrowBoth : {f : ArrowFunctor} -> {v, a : Arrow} ->
    (newBase : arrowBaseChange f a) ->
    arrowCobaseChangeDep f a newBase ->
    ArrowTermFunctor f v a

{-
mutual
  public export
  FreeArrowTot : (f : ArrowFunctor) -> (a : Arrow) -> Type
  FreeArrowTot f a = FreeArrowTot_hole

  public export
  FreeArrowBase : (f : ArrowFunctor) -> (a : Arrow) -> Type
  FreeArrowBase f a = FreeArrowBase_hole

  public export
  freeArrowProj : (f : ArrowFunctor) -> (a : Arrow) ->
    FreeArrowTot f a -> FreeArrowBase f a
  freeArrowProj f a tot = freeArrowProj_hole

  public export
  data FreeArrowType : ArrowFunctor -> Arrow -> Type where
    InFreeArrow : {f : ArrowFunctor} -> {a : Arrow} ->
      ArrowTermFunctor f a (FreeArrowMonad f a) ->
      FreeArrowType f a

  public export
  FreeArrowMonad : ArrowFunctor -> Arrow -> Arrow
  FreeArrowMonad f a = let type = FreeArrowType f a in FreeArrowMonad_hole
  -}

------------------------------------------
------------------------------------------
---- Polynomial endofunctors in Idris ----
------------------------------------------
------------------------------------------

public export
mapId : {a : Type} -> (x : a) -> map {f=IdTF} (Prelude.Basics.id {a}) x = x
mapId x = Refl

public export
mapIdTFRefl : (a : Type) ->
  map {f=IdTF} (Prelude.Basics.id {a}) = Prelude.Basics.id {a}
mapIdTFRefl _ = Refl

public export
mapIdTFExtEq : (a : Type) ->
  ExtEq (map {f=IdTF} (Prelude.Basics.id {a})) (Prelude.Basics.id {a})
mapIdTFExtEq a = EqFunctionExt (mapIdTFRefl a)

public export
mapIdTFIdem : (a : Type) ->
  map (map {f=IdTF} (Prelude.Basics.id {a})) =
    map {f=IdTF} (Prelude.Basics.id {a})
mapIdTFIdem _ = Refl

public export
mapIdTFExtIdem : (a : Type) ->
  ExtEq
    (map (map {f=IdTF} (Prelude.Basics.id {a})))
    (map {f=IdTF} (Prelude.Basics.id {a}))
mapIdTFExtIdem a = EqFunctionExt (mapIdTFIdem a)

public export
mapMapIdTFRefl : (a : Type) ->
  map (map {f=IdTF} (Prelude.Basics.id {a})) = Prelude.Basics.id {a}
mapMapIdTFRefl _ = Refl

public export
mapMapIdTFExtEq : (a : Type) ->
  ExtEq (map (map {f=IdTF} (Prelude.Basics.id {a}))) (Prelude.Basics.id {a})
mapMapIdTFExtEq a = EqFunctionExt (mapMapIdTFRefl a)

-- `IdTF` follows the functor laws; this shows that `IdTF` is a
-- functor in the category of the Idris type system.

public export
IdTFunctorialityId : (a : Type) ->
  ExtEq
    (map {f=IdTF} $ Prelude.Basics.id {a})
    (Prelude.Basics.id {a=(IdTF a)})
IdTFunctorialityId _ _ = Refl

public export
IdTFunctorialityCompose : {a, b, c : Type} -> (m : a -> b) -> (m' : b -> c) ->
  ExtEq
    (map {f=IdTF} (m' . m))
    (map {f=IdTF} m' . map {f=IdTF} m)
IdTFunctorialityCompose _ _ _ = Refl

----------------
---- Tuples ----
----------------

public export
TupleF : (natCarrier : Type) -> NatF natCarrier ->
  (carrier : natCarrier -> Type) -> (atom : Type) -> Type
TupleF natCarrier ZeroF carrier = TerminalMonad
TupleF natCarrier (SuccF n) carrier = flip Pair (carrier n)

public export
Tuple : Nat -> Type -> Type
Tuple Z atom = ()
Tuple (S n) atom = PairWithF atom (Tuple n atom)

public export
toTuple : {atom : Type} -> (l : List atom) -> Tuple (length l) atom
toTuple [] = ()
toTuple (x :: xs) = (x, toTuple xs)

public export
foldTuple : {n : Nat} -> {0 a : Type} ->
  (f : b -> a -> b) -> b -> Tuple n a -> b
foldTuple {n} f x t = case n of
  Z => x
  S n' => case t of
    (x', t') => foldTuple f (f x x') t'

public export
sumNTuple : {n : Nat} -> Tuple n Nat -> Nat
sumNTuple = foldTuple (+) 0

public export
TupleProductType : {n : Nat} -> Tuple n Type -> Type
TupleProductType = foldTuple Pair Unit

public export
tupleSumType : {n : Nat} -> Tuple n Type -> Type
tupleSumType = foldTuple Either Void

public export
mapTuple : {n : Nat} -> {0 a : Type} -> (f : a -> b) -> Tuple n a -> Tuple n b
mapTuple {n=Z} f () = ()
mapTuple {n=(S n)} f (x, t) = (f x, mapTuple f {n} t)

public export
(n : Nat) => Functor (Tuple n) where
  map = mapTuple

public export
tupleProj : {n : Nat} -> {atom : Type} -> (i : Nat) -> {auto ok : LT i n} ->
  Tuple n atom -> atom
tupleProj {n=Z} Z {ok} () = void $ succNotLTEzero ok
tupleProj {n=(S n)} Z {ok} (a, t) = a
tupleProj {n=(S n)} (S i) {ok} (a, t) = tupleProj i t {ok=(fromLteSucc ok)}

public export
TupleP : Type -> Type
TupleP = DPair Nat . flip Tuple

public export
TupleIndex : {atom : Type} -> TupleP atom -> Type
TupleIndex (n ** _) = Fin n

public export
TupleElem : {atom : Type} -> (t : TupleP atom) -> TupleIndex {atom} t -> atom
TupleElem {atom} (Z ** _) _ impossible
TupleElem {atom} (S Z ** (x, ())) (FS _) = x
TupleElem {atom} (S (S n) ** (_, _, xs)) (FS (FS i)) = TupleElem (n ** xs) i

public export
mapTupleP : (f : a -> b) -> TupleP a -> TupleP b
mapTupleP f (n ** t) = (n ** mapTuple f t)

-----------------
---- Choices ----
-----------------

public export
ChoiceF : (natCarrier : Type) -> NatF natCarrier ->
  (carrier : natCarrier -> Type) -> (atom : Type) -> Type
ChoiceF natCarrier ZeroF carrier = InitialComonad
ChoiceF natCarrier (SuccF n) carrier = flip Either (carrier n)

public export
Choice : Nat -> Type -> Type
Choice Z atom = Void
Choice (S n) atom = ChoiceBetweenF atom (Choice n atom)

public export
mapChoice : {n : Nat} -> (f : a -> b) -> Choice n a -> Choice n b
mapChoice {n=Z} f v = void v
mapChoice {n=(S n)} f (Left x) = Left (f x)
mapChoice {n=(S n)} f (Right t) = Right (mapChoice f {n} t)

public export
(n : Nat) => Functor (Choice n) where
  map = mapChoice

public export
choiceInj : {n : Nat} -> {atom : Type} -> (i : Nat) -> {auto ok : LT i n} ->
  atom -> Choice n atom
choiceInj {n=Z} Z {ok} a = void $ succNotLTEzero ok
choiceInj {n=(S n)} Z {ok} a = Left a
choiceInj {n=(S n)} (S i) {ok} t = Right $ choiceInj i t {ok=(fromLteSucc ok)}

public export
ChoiceP : Type -> Type
ChoiceP = DPair Nat . flip Choice

-------------------------
---- Lists of tuples ----
-------------------------

public export
TList : Nat -> Type -> Type
TList n atom = Tuple n (TupleP atom)

------------------------------------------
---- S-expressions with fixed arities ----
------------------------------------------

public export
data STuple : {atom : Type} -> (arity : atom -> Nat) -> Type where

-------------------------------------
---- The substitution-0 category ----
-------------------------------------

-- We refer to the category of zeroth-order (non-recursive) non-dependent
-- datatypes as the "substitution-0 category".

public export
Subst0TypeFCases : List (Type -> Type)
Subst0TypeFCases =
  [
    TerminalMonad, -- Unit
    TerminalMonad, -- Void
    ProductMonad, -- Product
    ProductMonad -- Coproduct
  ]

public export
Subst0TypeF : Type -> Type
Subst0TypeF = CoproductFL Subst0TypeFCases

public export
Subst0TypeLimitIter : Type -> Type
Subst0TypeLimitIter = TrEitherF Subst0TypeF

public export
Subst0TypeColimitIter : Type -> Type
Subst0TypeColimitIter = ScalePairF Subst0TypeF

public export
Subst0TypeAlg : Type -> Type
Subst0TypeAlg = Algebra Subst0TypeF

public export
Subst0TypeCoalg : Type -> Type
Subst0TypeCoalg = Coalgebra Subst0TypeF

public export
MuSubst0Type : Type
MuSubst0Type = Mu Subst0TypeF

public export
NuSubst0Type : Type
NuSubst0Type = Nu Subst0TypeF

public export
FreeSubst0Type : Type -> Type
FreeSubst0Type = FreeMonad Subst0TypeF

public export
CofreeSubst0Type : Type -> Type
CofreeSubst0Type = CofreeComonad Subst0TypeF

-- Parameterized special induction.
public export
subst0TypeCata : FreeFEval Subst0TypeF
subst0TypeCata v a subst alg (InFree x) = case x of
  TFV var => subst var
  TFC com => alg $ case com of
    -- Unit
    Left () => Left ()
    Right com' => Right $ case com' of
      -- Void
      Left () => Left ()
      Right com'' => Right $ case com'' of
        -- Product
        Left (p1, p2) =>
          Left
            (subst0TypeCata v a subst alg p1,
             subst0TypeCata v a subst alg p2)
        -- Coproduct
        Right (c1, c2) =>
          Right
            (subst0TypeCata v a subst alg c1,
             subst0TypeCata v a subst alg c2)

-- This algebra interprets the constructors of the substitution-0 category
-- as types in the Idris type system.  This is possible because those
-- types themselves form a category, and there is a faithful functor
-- from the substitution-0 category to that category.  (In other
-- words, the Idris type system contains an initial object, a terminal object,
-- and all products and coproducts, which together inductively comprise all
-- of the objects of the substitution-0 category.)
public export
interpretSubst0Alg : Subst0TypeAlg Type
interpretSubst0Alg = CoproductAlgL {l=Subst0TypeFCases}
  (const (), const Void, ProductRAdjoint, CoproductLAdjoint)

public export
Subst0Unit : FreeSubst0Type carrier
Subst0Unit = inFC $ Left ()

public export
Subst0Void : FreeSubst0Type carrier
Subst0Void = inFC $ Right $ Left ()

public export
Subst0Product :
  FreeSubst0Type carrier -> FreeSubst0Type carrier -> FreeSubst0Type carrier
Subst0Product a b = inFC $ Right $ Right $ Left (a, b)

public export
Subst0Coproduct :
  FreeSubst0Type carrier -> FreeSubst0Type carrier -> FreeSubst0Type carrier
Subst0Coproduct a b = inFC $ Right $ Right $ Right (a, b)

public export
data Subst0MorphismF :
    {objCarrier : Type} ->
    (morphCarrier :
      FreeSubst0Type objCarrier -> FreeSubst0Type objCarrier -> Type) ->
    FreeSubst0Type objCarrier -> FreeSubst0Type objCarrier ->
    Type where
  Subst0Id :
    Subst0MorphismF morphCarrier obj obj
  Subst0ToUnit :
    Subst0MorphismF morphCarrier domain Subst0Unit
  Subst0FromVoid :
    Subst0MorphismF morphCarrier Subst0Void codomain
  Subst0TermLeft :
    {objCarrier : Type} -> {a, b, c : FreeSubst0Type objCarrier} ->
    (morphCarrier :
      FreeSubst0Type objCarrier -> FreeSubst0Type objCarrier -> Type) ->
    morphCarrier Subst0Unit a ->
    morphCarrier (Subst0Coproduct a b) c ->
    Subst0MorphismF morphCarrier Subst0Unit c
  Subst0TermRight :
    {objCarrier : Type} -> {a, b, c : FreeSubst0Type objCarrier} ->
    (morphCarrier :
      FreeSubst0Type objCarrier -> FreeSubst0Type objCarrier -> Type) ->
    morphCarrier Subst0Unit b ->
    morphCarrier (Subst0Coproduct a b) c ->
    Subst0MorphismF morphCarrier Subst0Unit c
  Subst0TermPair :
    {objCarrier : Type} -> {a, b, c : FreeSubst0Type objCarrier} ->
    (morphCarrier :
      FreeSubst0Type objCarrier -> FreeSubst0Type objCarrier -> Type) ->
    morphCarrier Subst0Unit a ->
    morphCarrier Subst0Unit b ->
    morphCarrier (Subst0Product a b) c ->
    Subst0MorphismF morphCarrier Subst0Unit c

----------------------------------------
---- The 2x-substitution-0 category ----
----------------------------------------

-- Now we define the types of the product category of the substitution-0
-- category with itself.

----------------------------
---- Refined categories ----
----------------------------

-- 

-- This algebra -- which together with `interpretSubst0Alg` induces
-- a functor in the arrow (sigma) category of the substitution-0 category --
-- generates, for each type generated by `interpretSubst0Alg`, a type
-- of new constraints on those types.
public export
subst0NewConstraintAlg : Subst0TypeAlg Type
subst0NewConstraintAlg = CoproductAlgL {l=Subst0TypeFCases}
  (
    -- The unit type is already as constrained as it can get --
    -- it must have exactly one term.
    const Void,

    -- The void type is already as constrained as it can get --
    -- it must have no terms.
    const Void,

    -- The product type can have either of two constraints:  "must
    -- be equal" and "must be different".
    CoproductLAdjoint,

    -- The coproduct type can have either of two constraints:  "must
    -- be left" and "must be right".
    CoproductLAdjoint
  )

-- This algebra, given a type of constraints, generates a new
-- type representing compositions of constraints.  Since our constraints
-- are just Boolean predicates, their compositions comprise simply `true`,
-- `false`, `and`, and `or` -- which are isomorphic to the types of
-- the substitution-0 category.  So we can reuse the algebra which
-- _interprets_ objects of the substitution-0 category to _generate_
-- constraint types.  However, we give it a new name because the contexts
-- will be different, and we would like it to be visible in which context
-- this algebra is being used.
subst0ComposeConstraintAlg : Subst0TypeAlg Type
subst0ComposeConstraintAlg = interpretSubst0Alg

public export
record Subst0TypeArrow where
  constructor Subst0Types
  ErasedType : Type
  RefinedType : ErasedType -> Type

public export
data ErasedSubst0TypeF : Subst0TypeArrow -> Type where

public export
data RefinedSubst0TypeF : Subst0TypeArrow -> Type where

--------------------------------------------------------------------
---- The category of zeroth-order Idris polynomial endofunctors ----
--------------------------------------------------------------------

-- This algebra interprets the constructors of the substitution-0 category
-- as functors in the Idris type system.  This is posible because those
-- functors themselves form a category, and there is a faithful functor
-- from the substitution-0 category to that functor category.  (In other
-- words, the functor category contains an initial object, a terminal object,
-- and all products and coproducts, which together inductively comprise all
-- of the objects of the substitution-0 category.)
public export
subst0FunctorAlg : Subst0TypeAlg (Type -> Type)
subst0FunctorAlg = CoproductAlgL {l=Subst0TypeFCases}
  (const TerminalMonad,
   const InitialComonad,
   ProductAdjunctFCat,
   CoproductAdjunctFCat
  )

-- This dependent algebra combines `interpretSubst0Alg` and `Subst0ConstraintF`
-- to create a functor in an arrow category.  (The arrow category is a
-- sub-category of the category of endofunctors on the substitution-0 category.
-- Consequently, it has an initial object in the category of the F-algebras of
-- the functor generated by this dependent algebra, and we will use that initial
-- algebra to define, within the category of all initial algebras of
-- endofunctors of the substitution-0 category, the the object which represents
-- the type of all types of the _refined_ substitution-0 category.)
-- 

-- The functor analogue of `subst0NewConstraintAlg`, as
-- `subst0FunctorAlg` is the functor analogue of `interpretSubst0Alg`.
public export
subst0NewConstraintFunctorAlg : Subst0TypeAlg (Type -> Type)
subst0NewConstraintFunctorAlg = CoproductAlgL {l=Subst0TypeFCases}
  (
    -- The (already-fully-constrained) unit type
    const InitialComonad,

    -- The (already-fully-constrained) void type
    const InitialComonad,

    -- The product type ("must be equal" or "must be different")
    CoproductAdjunctFCat,

    -- The coproduct type ("must be left" or "must be right")
    CoproductAdjunctFCat
  )

----------------------------------------------
---- Category of first-order refined ADTs ----
----------------------------------------------

------------------------------------------------------
------------------------------------------------------
---- Predicates, relations, equivalences in Idris ----
------------------------------------------------------
------------------------------------------------------

--------------------
---- Predicates ----
--------------------

PredicateOn : Type -> Type
PredicateOn = SliceObj

InitialSliceObj : (t : Type) -> PredicateOn t
InitialSliceObj t el = Void

VoidPred : PredicateOn Void
VoidPred v = void v

TerminalSliceObj : (t : Type) -> PredicateOn t
TerminalSliceObj t el = ()

UnitPred : PredicateOn Unit
UnitPred = TerminalSliceObj ()

ProductPred : PredicateOn a -> PredicateOn b -> PredicateOn (a, b)
ProductPred p p' (el, el') = (p el, p' el')

CoproductPred : PredicateOn a -> PredicateOn b -> PredicateOn (Either a b)
CoproductPred p p' (Left el) = p el
CoproductPred p p' (Right el') = p' el'

SubPredicate : {a : Type} -> (sub, super : PredicateOn a) -> Type
SubPredicate {a} sub super = (el : a) -> sub el -> super el

PredEquiv : {a : Type} -> (p, p' : PredicateOn a) -> Type
PredEquiv {a} p p' = (SubPredicate p p', SubPredicate p' p)

PreservesPredicates : {a, b : Type} -> PredicateOn a -> PredicateOn b ->
  (a -> b) -> Type
PreservesPredicates p p' f = (el : a) -> p el -> p' (f el)

PredMorphism : {a, b : Type} -> PredicateOn a -> PredicateOn b -> Type
PredMorphism p p' = DPair (a -> b) (PreservesPredicates p p')

PredFunctor : Type -> Type
PredFunctor t = PredicateOn t -> PredicateOn t

data PredicateTermF : {t: Type} ->
    (f : PredFunctor t) -> (v : PredicateOn t) -> PredFunctor t where
  PredicateVar :
    {t : Type} -> {f : PredFunctor t} ->
    {v, carrier : PredicateOn t} -> {el : t} ->
    v el -> PredicateTermF f {t} v carrier el
  PredicateComposite :
    {t : Type} -> {f : PredFunctor t} ->
    {v, carrier : PredicateOn t} -> {el : t} ->
    f carrier el -> PredicateTermF f v carrier el

data FreeMPredicate :
    {t : Type} -> PredFunctor t -> PredFunctor t where
  InFreePredicate :
    {t : Type} -> {f : PredFunctor t} -> {rel : PredicateOn t} -> {el : t} ->
    PredicateTermF f rel (FreeMPredicate f rel) el ->
    FreeMPredicate f rel el

PredicateMu : {t: Type} -> PredFunctor t -> PredicateOn t
PredicateMu {t} f = FreeMPredicate f $ InitialSliceObj t

data PredicateTreeF : {t: Type} ->
    (f : PredFunctor t) -> (v : PredicateOn t) -> PredFunctor t where
  PredicateNode :
    {t : Type} -> {f : PredFunctor t} ->
    {v, carrier : PredicateOn t} -> {el : t} ->
    v el -> f carrier el -> PredicateTreeF f v carrier el

data CofreeCMPredicate :
    {t : Type} -> PredFunctor t -> PredFunctor t where
  InCofreePredicate :
    {t : Type} -> {f : PredFunctor t} -> {rel : PredicateOn t} -> {el : t} ->
    Inf (PredicateTreeF f rel (CofreeCMPredicate f rel) el) ->
    CofreeCMPredicate f rel el

PredicateNu : {t: Type} -> PredFunctor t -> PredicateOn t
PredicateNu {t} f = CofreeCMPredicate f $ TerminalSliceObj t

-------------------
---- Relations ----
-------------------

public export
ProductRelation : RelationOn a -> RelationOn b -> RelationOn (a, b)
ProductRelation rel rel' (el1, el1') (el2, el2') = (rel el1 el2, rel' el1' el2')

public export
CoproductRelation : RelationOn a -> RelationOn b -> RelationOn (Either a b)
CoproductRelation rel rel' (Left el1) (Left el2) = rel el1 el2
CoproductRelation rel rel' (Left el1) (Right el2') = Void
CoproductRelation rel rel' (Right el1') (Left el2) = Void
CoproductRelation rel rel' (Right el1') (Right el2') = rel' el1' el2'

public export
SubRelation : {a : Type} -> (sub, super : RelationOn a) -> Type
SubRelation {a} sub super = (el1, el2 : a) -> sub el1 el2 -> super el1 el2

public export
RelationEquiv : {a : Type} -> (r, r' : RelationOn a) -> Type
RelationEquiv r r' = (SubRelation r r', SubRelation r' r)

public export
EqualOverRelations : {a, b : Type} ->
  RelationOn a -> RelationOn b -> (f, g : a -> b) -> Type
EqualOverRelations rel rel' f g =
  (el, el' : a) -> rel el el' -> rel' (f el) (g el')

public export
PreservesRelations : {a, b : Type} ->
  RelationOn a -> RelationOn b -> (a -> b) -> Type
PreservesRelations rel rel' f = EqualOverRelations rel rel' f f

public export
RelMorphism : {a, b : Type} -> RelationOn a -> RelationOn b -> Type
RelMorphism rel rel' = Subset0 (a -> b) (PreservesRelations rel rel')

public export
RelFunctor : Type -> Type
RelFunctor t = RelationOn t -> RelationOn t

data RelationTermF : {t: Type} ->
    (f : RelFunctor t) -> (v : RelationOn t) -> RelFunctor t where
  RelationVar :
    {t : Type} -> {f : RelFunctor t} ->
    {v, carrier : RelationOn t} -> {el, el' : t} ->
    v el el' -> RelationTermF f {t} v carrier el el'
  RelationComposite :
    {t : Type} -> {f : RelFunctor t} ->
    {v, carrier : RelationOn t} -> {el, el' : t} ->
    f carrier el el' -> RelationTermF f v carrier el el'

data FreeMRelation :
    {t : Type} -> RelFunctor t -> RelFunctor t where
  InFreeRelation :
    {t : Type} -> {f : RelFunctor t} -> {rel : RelationOn t} -> {el, el' : t} ->
    RelationTermF f rel (FreeMRelation f rel) el el' ->
    FreeMRelation f rel el el'

RelationMu : {t: Type} -> RelFunctor t -> RelationOn t
RelationMu {t} f = FreeMRelation f $ EmptyRel t

data RelationTreeF : {t: Type} ->
    (f : RelFunctor t) -> (v : RelationOn t) -> RelFunctor t where
  RelationNode :
    {t : Type} -> {f : RelFunctor t} ->
    {v, carrier : RelationOn t} -> {el, el' : t} ->
    v el el' -> f carrier el el' -> RelationTreeF f v carrier el el'

data CofreeCMRelation :
    {t : Type} -> RelFunctor t -> RelFunctor t where
  InCofreeRelation :
    {t : Type} -> {f : RelFunctor t} -> {rel : RelationOn t} -> {el, el' : t} ->
    Inf (RelationTreeF f rel (CofreeCMRelation f rel) el el') ->
    CofreeCMRelation f rel el el'

RelationNu : {t: Type} -> RelFunctor t -> RelationOn t
RelationNu {t} f = CofreeCMRelation f $ FullRel t

-- Category theory's equalizer, parameterized over a relation on
-- the codomain (which serves as equality on the codomain, allowing
-- the representation of equalizers on types whose equality is not
-- that of the metalanguage (Idris)).
EqualizerRelationGenF : (f, g : a -> b) -> RelationOn b -> RelationOn a
EqualizerRelationGenF f g rel el el' = rel (f el) (g el')

-- Category theory's coequalizer, parameterized over a relation on
-- the domain (which serves as equality on the domain, allowing
-- the representation of coequalizers on types whose equality is not
-- that of the metalanguage (Idris)).
CoequalizerRelationGenF : {a, b: _} ->
  (f, g : a -> b) -> RelationOn a -> RelationOn b
CoequalizerRelationGenF {a} f g rel el el' =
  (elas : (a, a) **
   (rel (fst elas) (snd elas), f (fst elas) = el, g (snd elas) = el'))

----------------------
---- Equivalences ----
----------------------

data EquivGenF : {t : Type} -> RelFunctor t where
  EquivRefl : {t : Type} -> {carrier : RelationOn t} ->
    {el, el' : t} -> el = el' -> EquivGenF carrier el el
  EquivSym : {t : Type} -> {carrier : RelationOn t} -> {el, el' : t} ->
    carrier el el' -> EquivGenF carrier el' el
  EquivTrans : {t : Type} -> {carrier : RelationOn t} ->
    {el, el', el'' : t} ->
    carrier el el' -> carrier el' el'' -> EquivGenF carrier el el''

FreeMEquiv : {t : Type} -> RelFunctor t
FreeMEquiv = FreeMRelation EquivGenF

CofreeCMEquiv : {t : Type} -> RelFunctor t
CofreeCMEquiv = CofreeCMRelation EquivGenF
