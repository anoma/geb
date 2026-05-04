module LanguageDef.FinCatPRA

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.BinTree
import LanguageDef.GenPolyFunc

%hide Library.IdrisCategories.BaseChangeF

%default total

----------------------------------------------------
----------------------------------------------------
---- S-expression representation of finite sets ----
----------------------------------------------------
----------------------------------------------------

-- Atom type for S-expression representation of finite sets
public export
data FinSetAtom : Type where
  -- Product constructor - can have any number of components
  FSAProd : FinSetAtom
  -- Coproduct constructor - tagged union
  FSACoprod : FinSetAtom
  -- Natural number - represents an element of Fin n
  FSANat : Nat -> FinSetAtom

-- Type synonym for S-expressions with our atom type
public export
FinSetSExpr : Type
FinSetSExpr = SLSFmu FinSetAtom

-- Type checking predicate for finite set S-expressions
mutual
  public export
  data FinSetSExprValid : FinSetSExpr -> Type where
    -- A natural number must be a leaf
    ValidNat : (n : Nat) -> FinSetSExprValid (InFree (TFC (FSANat n, Lin)))
    -- A product can have any list of valid children
    ValidProd : {xs : SnocList FinSetSExpr} ->
                FinSetSExprValidList xs ->
                FinSetSExprValid (InFree (TFC (FSAProd, xs)))
    -- A coproduct must have exactly two children: a nat index and a term
    ValidCoprod : {n : Nat} -> {t : FinSetSExpr} ->
                  FinSetSExprValid t ->
                  FinSetSExprValid (InFree (TFC (FSACoprod,
                    Lin :< InFree (TFC (FSANat n, Lin)) :< t)))

  public export
  data FinSetSExprValidList : SnocList FinSetSExpr -> Type where
    ValidNil : FinSetSExprValidList Lin
    ValidSnoc : {xs : SnocList FinSetSExpr} -> {x : FinSetSExpr} ->
                FinSetSExprValidList xs ->
                FinSetSExprValid x ->
                FinSetSExprValidList (xs :< x)

-- Helper functions for constructing S-expressions
public export
fsNat : Nat -> FinSetSExpr
fsNat n = inFC (FSANat n, Lin)

public export
fsProd : SnocList FinSetSExpr -> FinSetSExpr
fsProd xs = inFC (FSAProd, xs)

public export
fsCoprod : Nat -> FinSetSExpr -> FinSetSExpr
fsCoprod n t = inFC (FSACoprod, Lin :< fsNat n :< t)

-- Helper to extract the underlying SLSF data from a FinSetSExpr
public export
unFinSetSExpr : FinSetSExpr -> SLSF FinSetAtom FinSetSExpr
unFinSetSExpr (InFree (TFC x)) = x
unFinSetSExpr (InFree (TFV _)) impossible

-- Decidable type checker for finite set S-expressions
mutual
  public export
  finSetSExprValidDec : (s : FinSetSExpr) -> Dec (FinSetSExprValid s)
  finSetSExprValidDec (InFree (TFV x)) = void x
  finSetSExprValidDec (InFree (TFC (FSANat n, Lin))) = Yes (ValidNat n)
  finSetSExprValidDec (InFree (TFC (FSANat n, xs :< x))) =
    No $ \case ValidNat _ impossible
  finSetSExprValidDec (InFree (TFC (FSAProd, xs))) =
    case finSetSExprValidListDec xs of
      Yes prf => Yes (ValidProd prf)
      No contra => No $ \case
        ValidProd prf => contra prf
  finSetSExprValidDec (InFree (TFC (FSACoprod, Lin))) =
    No $ \case ValidCoprod _ impossible
  finSetSExprValidDec (InFree (TFC (FSACoprod, Lin :< x))) =
    No $ \case ValidCoprod _ impossible
  finSetSExprValidDec (InFree (TFC (FSACoprod, Lin :< InFree (TFV x) :< t))) =
    void x
  finSetSExprValidDec
    (InFree (TFC (FSACoprod, Lin :< InFree (TFC (FSANat n, Lin)) :< t))) =
    case finSetSExprValidDec t of
      Yes prf => Yes (ValidCoprod prf)
      No contra => No $ \case
        ValidCoprod prf => contra prf
  finSetSExprValidDec
    (InFree (TFC (FSACoprod, Lin :< InFree (TFC (FSANat n, _ :< _)) :< t))) =
    No $ \case ValidCoprod _ impossible
  finSetSExprValidDec
    (InFree (TFC (FSACoprod, Lin :< InFree (TFC (FSAProd, _)) :< t))) =
    No $ \case ValidCoprod _ impossible
  finSetSExprValidDec
    (InFree (TFC (FSACoprod, Lin :< InFree (TFC (FSACoprod, _)) :< t))) =
    No $ \case ValidCoprod _ impossible
  finSetSExprValidDec (InFree (TFC (FSACoprod, xs :< _ :< _ :< _))) =
    No $ \case ValidCoprod _ impossible

  public export
  finSetSExprValidListDec : (xs : SnocList FinSetSExpr) ->
                            Dec (FinSetSExprValidList xs)
  finSetSExprValidListDec Lin = Yes ValidNil
  finSetSExprValidListDec (xs :< x) =
    case finSetSExprValidListDec xs of
      No contra => No $ \case
        (ValidSnoc xsPrf _) => contra xsPrf
      Yes xsPrf => case finSetSExprValidDec x of
        No contra => No $ \case
          (ValidSnoc _ xPrf) => contra xPrf
        Yes xPrf => Yes (ValidSnoc xsPrf xPrf)

-------------------------------------------------------
-------------------------------------------------------
---- Index categories for finite two-level forests ----
-------------------------------------------------------
-------------------------------------------------------

-- A finite two-level forest is represented as a list of natural numbers.
-- Each dependent type has exactly one parent (base type).
-- The length of the list is the number of base types.
-- Each element specifies how many dependent types depend on that base type.
public export
Fin2Forest : Type
Fin2Forest = List Nat

-- Example: [2, 0, 3] represents:
-- - 3 base types (indexed 0, 1, 2)
-- - Base type 0 has 2 dependent types
-- - Base type 1 has 0 dependent types
-- - Base type 2 has 3 dependent types

-- Get the number of base types in a forest
public export
f2fNumBase : Fin2Forest -> Nat
f2fNumBase = length

-- Get the number of dependent types for a specific base type
public export
f2fNumDep : (forest : Fin2Forest) -> Fin (f2fNumBase forest) -> Nat
f2fNumDep forest i = index' forest i

-- Total number of dependent types across all base types
public export
f2fTotalDep : Fin2Forest -> Nat
f2fTotalDep = sum

-- An object in the index category is either a base type or a dependent type
public export
data F2FObj : Fin2Forest -> Type where
  BaseObj : (i : Fin (f2fNumBase forest)) -> F2FObj forest
  DepObj : (base : Fin (f2fNumBase forest)) ->
           (dep : Fin (f2fNumDep forest base)) ->
           F2FObj forest

-- Morphisms in a two-level forest: identities and dependent-to-base
public export
data F2FMor : {forest : Fin2Forest} ->
    F2FObj forest -> F2FObj forest -> Type where
  IdMor : {forest : Fin2Forest} -> {obj : F2FObj forest} ->
          F2FMor obj obj
  DepToBase : {forest : Fin2Forest} ->
              {base : Fin (f2fNumBase forest)} ->
              {dep : Fin (f2fNumDep forest base)} ->
              F2FMor {forest} (DepObj base dep) (BaseObj base)

-- The walking arrow is a special case: [1]
public export
WalkingArrow : Fin2Forest
WalkingArrow = [1]

-- Show that our forest representation generalizes the walking arrow
public export
WalkingArrowBase : F2FObj WalkingArrow
WalkingArrowBase = BaseObj FZ

public export
WalkingArrowDep : F2FObj WalkingArrow
WalkingArrowDep = DepObj FZ FZ

public export
WalkingArrowMor : F2FMor WalkingArrowDep WalkingArrowBase
WalkingArrowMor = DepToBase

-- Composition of morphisms in the forest category
public export
f2fComposeMor : {forest : Fin2Forest} -> {a, b, c : F2FObj forest} ->
                   F2FMor b c -> F2FMor a b -> F2FMor a c
f2fComposeMor IdMor g = g
f2fComposeMor f IdMor = f
f2fComposeMor DepToBase DepToBase impossible

-- Left identity law for forest morphisms
public export
f2fComposeIdLeft : {forest : Fin2Forest} -> {a, b : F2FObj forest} ->
  (f : F2FMor a b) -> f2fComposeMor IdMor f = f
f2fComposeIdLeft _ = Refl

-- Right identity law for forest morphisms
public export
f2fComposeIdRight : {forest : Fin2Forest} -> {a, b : F2FObj forest} ->
  (f : F2FMor a b) -> f2fComposeMor f IdMor = f
f2fComposeIdRight IdMor = Refl
f2fComposeIdRight DepToBase = Refl

-- Associativity of forest morphism composition
public export
f2fComposeAssoc : {forest : Fin2Forest} ->
  {a, b, c, d : F2FObj forest} ->
  (h : F2FMor c d) -> (g : F2FMor b c) -> (f : F2FMor a b) ->
  f2fComposeMor (f2fComposeMor h g) f = f2fComposeMor h (f2fComposeMor g f)
f2fComposeAssoc IdMor g f = Refl
f2fComposeAssoc DepToBase IdMor f = Refl
f2fComposeAssoc DepToBase DepToBase _ impossible

----------------------------------------------
---- Morphisms between forests (functors) ----
----------------------------------------------

-- Object mapping for a functor between forests
public export
F2FFunctorObjMap : Fin2Forest -> Fin2Forest -> Type
F2FFunctorObjMap src tgt = F2FObj src -> F2FObj tgt

-- Morphism mapping for a functor between forests
public export
F2FFunctorMorMap : (src, tgt : Fin2Forest) -> F2FFunctorObjMap src tgt -> Type
F2FFunctorMorMap src tgt objMap =
  (a, b : F2FObj src) -> F2FMor a b -> F2FMor (objMap a) (objMap b)

-- Functor preserves identities condition
public export
F2FFunctorPresId : (src, tgt : Fin2Forest) ->
  (objMap : F2FFunctorObjMap src tgt) ->
  F2FFunctorMorMap src tgt objMap -> Type
F2FFunctorPresId src tgt objMap morMap =
  (a : F2FObj src) -> morMap a a IdMor = IdMor

-- Functor preserves composition condition
public export
F2FFunctorPresComp : (src, tgt : Fin2Forest) ->
  (objMap : F2FFunctorObjMap src tgt) ->
  F2FFunctorMorMap src tgt objMap -> Type
F2FFunctorPresComp src tgt objMap morMap =
  (a, b, c : F2FObj src) -> (g : F2FMor b c) -> (f : F2FMor a b) ->
  morMap a c (f2fComposeMor g f) = f2fComposeMor (morMap b c g) (morMap a b f)

-- A functor between forests with its laws
public export
F2FFunctor : Fin2Forest -> Fin2Forest -> Type
F2FFunctor src tgt =
  DPair (F2FFunctorObjMap src tgt) $ \objMap =>
  DPair (F2FFunctorMorMap src tgt objMap) $ \morMap =>
  (F2FFunctorPresId src tgt objMap morMap,
   F2FFunctorPresComp src tgt objMap morMap)

-- Get the object mapping of a functor
public export
f2fFunctorObjMap : {src, tgt : Fin2Forest} ->
  F2FFunctor src tgt -> F2FFunctorObjMap src tgt
f2fFunctorObjMap = fst

-- Get the morphism mapping of a functor
public export
f2fFunctorMorMap : {src, tgt : Fin2Forest} -> (f : F2FFunctor src tgt) ->
  F2FFunctorMorMap src tgt (f2fFunctorObjMap f)
f2fFunctorMorMap f = fst (snd f)

-- Get the identity preservation law of a functor
public export
f2fFunctorPresId : {src, tgt : Fin2Forest} -> (f : F2FFunctor src tgt) ->
  F2FFunctorPresId src tgt (f2fFunctorObjMap f) (f2fFunctorMorMap f)
f2fFunctorPresId f = fst (snd (snd f))

-- Get the composition preservation law of a functor
public export
f2fFunctorPresComp : {src, tgt : Fin2Forest} -> (f : F2FFunctor src tgt) ->
  F2FFunctorPresComp src tgt (f2fFunctorObjMap f) (f2fFunctorMorMap f)
f2fFunctorPresComp f = snd (snd (snd f))

-- Identity functor on a forest
public export
f2fIdFunctor : (forest : Fin2Forest) -> F2FFunctor forest forest
f2fIdFunctor forest =
  (id ** (\a, b => id) ** (\a => Refl, \a, b, c, g, f => Refl))

-- Composition of forest functors
public export
f2fComposeFunctors : {a, b, c : Fin2Forest} ->
  F2FFunctor b c -> F2FFunctor a b -> F2FFunctor a c
f2fComposeFunctors {a} {b} {c} g f =
  let morMapComp : (x, y : F2FObj a) -> F2FMor x y ->
                   F2FMor (f2fFunctorObjMap g (f2fFunctorObjMap f x))
                          (f2fFunctorObjMap g (f2fFunctorObjMap f y))
      morMapComp x y mor = f2fFunctorMorMap g
                             (f2fFunctorObjMap f x)
                             (f2fFunctorObjMap f y)
                             (f2fFunctorMorMap f x y mor)
      -- Proof that composition preserves identities
      compPresId : (x : F2FObj a) -> morMapComp x x IdMor = IdMor
      compPresId x =
        rewrite f2fFunctorPresId f x in
        f2fFunctorPresId g (f2fFunctorObjMap f x)
      -- Proof that composition preserves composition
      compPresComp : (x, y, z : F2FObj a) -> (mor1 : F2FMor y z) ->
                     (mor2 : F2FMor x y) ->
                     morMapComp x z (f2fComposeMor mor1 mor2) =
                     f2fComposeMor (morMapComp y z mor1) (morMapComp x y mor2)
      compPresComp x y z mor1 mor2 =
        rewrite f2fFunctorPresComp f x y z mor1 mor2 in
        f2fFunctorPresComp g
          (f2fFunctorObjMap f x)
          (f2fFunctorObjMap f y)
          (f2fFunctorObjMap f z)
          (f2fFunctorMorMap f y z mor1)
          (f2fFunctorMorMap f x y mor2)
  in (f2fFunctorObjMap g . f2fFunctorObjMap f ** morMapComp **
      (compPresId, compPresComp))

--------------------------------------------------
---- Natural transformations between functors ----
--------------------------------------------------

-- A natural transformation between forest functors
public export
F2FNatTrans : {src, tgt : Fin2Forest} ->
  F2FFunctor src tgt -> F2FFunctor src tgt -> Type
F2FNatTrans {src} {tgt} f g =
  (obj : F2FObj src) ->
  F2FMor (f2fFunctorObjMap f obj) (f2fFunctorObjMap g obj)

-- The naturality condition for forest functors
public export
F2FNatCond : {src, tgt : Fin2Forest} -> (f, g : F2FFunctor src tgt) ->
  F2FNatTrans {src} {tgt} f g -> Type
F2FNatCond {src} {tgt} f g trans =
  (a, b : F2FObj src) -> (mor : F2FMor a b) ->
  f2fComposeMor (trans b) (f2fFunctorMorMap f a b mor) =
  f2fComposeMor (f2fFunctorMorMap g a b mor) (trans a)

-- A natural transformation with its naturality proof
public export
F2FNat : {src, tgt : Fin2Forest} ->
  F2FFunctor src tgt -> F2FFunctor src tgt -> Type
F2FNat {src} {tgt} f g =
  DPair (F2FNatTrans {src} {tgt} f g) (F2FNatCond {src} {tgt} f g)

-- Get the transformation component of a natural transformation
public export
f2fNatTransform : {src, tgt : Fin2Forest} -> {f, g : F2FFunctor src tgt} ->
  F2FNat {src} {tgt} f g -> F2FNatTrans {src} {tgt} f g
f2fNatTransform = DPair.fst

-- Get the naturality condition of a natural transformation
public export
f2fNatCond : {src, tgt : Fin2Forest} -> {f, g : F2FFunctor src tgt} ->
  (nat : F2FNat {src} {tgt} f g) ->
  F2FNatCond {src} {tgt} f g (f2fNatTransform {f} {g} nat)
f2fNatCond = DPair.snd

-- Identity natural transformation
public export
f2fIdNat : {src, tgt : Fin2Forest} -> (f : F2FFunctor src tgt) ->
  F2FNat {src} {tgt} f f
f2fIdNat f = ((\obj => IdMor) ** \a, b, mor =>
  sym (f2fComposeIdRight (f2fFunctorMorMap f a b mor)))

-- Composition of natural transformations
public export
f2fComposeNats : {src, tgt : Fin2Forest} -> {f, g, h : F2FFunctor src tgt} ->
  F2FNat {src} {tgt} g h -> F2FNat {src} {tgt} f g -> F2FNat {src} {tgt} f h
f2fComposeNats {src} {tgt} {f} {g} {h} (beta ** betaCond) (alpha ** alphaCond) =
  let natCompCond : (a, b : F2FObj src) -> (mor : F2FMor a b) ->
        f2fComposeMor (f2fComposeMor (beta b) (alpha b))
                      (f2fFunctorMorMap f a b mor) =
        f2fComposeMor (f2fFunctorMorMap h a b mor)
                      (f2fComposeMor (beta a) (alpha a))
      natCompCond a b mor =
        rewrite f2fComposeAssoc (beta b) (alpha b)
                                (f2fFunctorMorMap f a b mor) in
        rewrite alphaCond a b mor in
        rewrite sym (f2fComposeAssoc (beta b)
                                     (f2fFunctorMorMap g a b mor)
                                     (alpha a)) in
        rewrite betaCond a b mor in
        f2fComposeAssoc (f2fFunctorMorMap h a b mor) (beta a) (alpha a)
  in ((\obj => f2fComposeMor (beta obj) (alpha obj)) ** natCompCond)

----------------------------------------------------
----------------------------------------------------
---- Copresheaves over finite two-level forests ----
----------------------------------------------------
----------------------------------------------------

-- A copresheaf assigns:
-- - A type to each base object
-- - A dependent type to each dependent object over its base's type

-- A copresheaf assigns a type to each object
public export
F2FCoprObjMap : Fin2Forest -> Type
F2FCoprObjMap forest = F2FObj forest -> Type

-- A copresheaf assigns a function to each morphism
public export
F2FCoprMorMap : {forest : Fin2Forest} -> F2FCoprObjMap forest -> Type
F2FCoprMorMap {forest} objMap =
  {a, b : F2FObj forest} -> F2FMor a b -> objMap a -> objMap b

-- A copresheaf is an object mapping together with a morphism mapping
public export
F2FCopr : Fin2Forest -> Type
F2FCopr forest = Sigma {a=(F2FCoprObjMap forest)} F2FCoprMorMap

----------------------------------------------------
---- Finite copresheaves (enriched over FinSet) ----
----------------------------------------------------

-- A finite copresheaf assigns a natural number to each object
public export
F2FFinCoprObjMap : Fin2Forest -> Type
F2FFinCoprObjMap forest = F2FObj forest -> Nat

-- A finite copresheaf assigns a function between Fins to each morphism
public export
F2FFinCoprMorMap : {forest : Fin2Forest} -> F2FFinCoprObjMap forest -> Type
F2FFinCoprMorMap {forest} objMap =
  {a, b : F2FObj forest} -> F2FMor a b -> Fin (objMap a) -> Fin (objMap b)

-- A finite copresheaf is an object mapping together with a morphism mapping
public export
F2FFinCopr : Fin2Forest -> Type
F2FFinCopr forest = Sigma {a=(F2FFinCoprObjMap forest)} F2FFinCoprMorMap

-- Get the object mapping of a finite copresheaf
public export
f2fFinCoprObjMap : {forest : Fin2Forest} ->
  F2FFinCopr forest -> F2FFinCoprObjMap forest
f2fFinCoprObjMap = DPair.fst

-- Get the morphism mapping of a finite copresheaf
public export
f2fFinCoprMorMap : {forest : Fin2Forest} -> (copr : F2FFinCopr forest) ->
  F2FFinCoprMorMap {forest} (f2fFinCoprObjMap {forest} copr)
f2fFinCoprMorMap = DPair.snd

-- Convert a finite copresheaf to a general copresheaf
public export
f2fFinCoprToCopr : {forest : Fin2Forest} -> F2FFinCopr forest -> F2FCopr forest
f2fFinCoprToCopr finCopr =
  (Fin . f2fFinCoprObjMap finCopr ** f2fFinCoprMorMap finCopr)

-- Get the object mapping of a copresheaf
public export
f2fCoprObjMap : {forest : Fin2Forest} -> F2FCopr forest -> F2FCoprObjMap forest
f2fCoprObjMap = DPair.fst

-- Get the morphism mapping of a copresheaf
public export
f2fCoprMorMap : {forest : Fin2Forest} -> (copr : F2FCopr forest) ->
          F2FCoprMorMap {forest} (f2fCoprObjMap {forest} copr)
f2fCoprMorMap = DPair.snd

------------------------------------------------------
------------------------------------------------------
---- Natural transformations between copresheaves ----
------------------------------------------------------
------------------------------------------------------

-- A natural transformation is a family of functions that commute with morphisms
public export
F2FCoprNatTrans : {forest : Fin2Forest} ->
  F2FCopr forest -> F2FCopr forest -> Type
F2FCoprNatTrans {forest} p q =
  (obj : F2FObj forest) -> f2fCoprObjMap p obj -> f2fCoprObjMap q obj

-- The naturality condition: the transformation commutes with morphisms
public export
F2FCoprNatCond : {forest : Fin2Forest} -> (p, q : F2FCopr forest) ->
  F2FCoprNatTrans {forest} p q -> Type
F2FCoprNatCond {forest} p q trans =
  (a, b : F2FObj forest) -> (mor : F2FMor a b) ->
  ExtEq {a=(f2fCoprObjMap p a)} {b=(f2fCoprObjMap q b)}
    (trans b . f2fCoprMorMap p mor) (f2fCoprMorMap q mor . trans a)

-- A morphism between copresheaves is a natural transformation satisfying
-- naturality.
--
-- This generalizes MLDirichCatMor to arbitrary finite two-level forests.
-- When forest = WalkingArrow = [1], this is equivalent to MLDirichCatMor.
public export
F2FCoprMor : {forest : Fin2Forest} ->
  F2FCopr forest -> F2FCopr forest -> Type
F2FCoprMor {forest} p q =
  DPair (F2FCoprNatTrans {forest} p q) (F2FCoprNatCond {forest} p q)

-- Get the natural transformation component of a copresheaf morphism
public export
f2fCoprMorTrans : {forest : Fin2Forest} -> {p, q : F2FCopr forest} ->
  F2FCoprMor {forest} p q -> F2FCoprNatTrans {forest} p q
f2fCoprMorTrans = DPair.fst

-- Get the naturality condition of a copresheaf morphism
public export
f2fCoprMorCond : {forest : Fin2Forest} -> {p, q : F2FCopr forest} ->
  (mor : F2FCoprMor {forest} p q) ->
  F2FCoprNatCond {forest} p q (f2fCoprMorTrans {forest} {p} {q} mor)
f2fCoprMorCond = DPair.snd

-- Identity copresheaf morphism
public export
f2fCoprIdMor : {forest : Fin2Forest} -> (p : F2FCopr forest) ->
  F2FCoprMor {forest} p p
f2fCoprIdMor p = ((\obj => id) ** \a, b, mor, x => Refl)

-- Composition of copresheaf morphisms
public export
f2fCoprComposeMor : {forest : Fin2Forest} -> {p, q, r : F2FCopr forest} ->
  F2FCoprMor {forest} q r -> F2FCoprMor {forest} p q ->
  F2FCoprMor {forest} p r
f2fCoprComposeMor {forest} {p} {q} {r} (g ** gCond) (f ** fCond) =
  ((\obj => g obj . f obj) ** \a, b, mor, x =>
    rewrite fCond a b mor x in
    gCond a b mor (f a x))

-- Left identity law for copresheaf morphisms
public export
f2fCoprComposeIdLeft : (fext : FunExt) -> {forest : Fin2Forest} ->
  {p, q : F2FCopr forest} -> (f : F2FCoprMor {forest} p q) ->
  f2fCoprComposeMor {p} {q} {r=q} (f2fCoprIdMor q) f = f
f2fCoprComposeIdLeft fext {forest} {p} {q} (trans ** cond) =
  dpEq12 Refl (funExt $ \a => funExt $ \b => funExt $ \mor => funExt $ \x =>
    uip)

-- Right identity law for copresheaf morphisms
public export
f2fCoprComposeIdRight : {forest : Fin2Forest} -> {p, q : F2FCopr forest} ->
  (f : F2FCoprMor {forest} p q) ->
  f2fCoprComposeMor {p} {q=p} {r=q} f (f2fCoprIdMor p) = f
f2fCoprComposeIdRight {forest} {p} {q} (trans ** cond) = Refl

-- Associativity of copresheaf morphism composition
public export
f2fCoprComposeAssoc : {forest : Fin2Forest} ->
  {p, q, r, s : F2FCopr forest} ->
  (h : F2FCoprMor {forest} r s) -> (g : F2FCoprMor {forest} q r) ->
  (f : F2FCoprMor {forest} p q) ->
  f2fCoprComposeMor {p} {q} {r=s} (f2fCoprComposeMor {p=q} {q=r} {r=s} h g) f =
  f2fCoprComposeMor {p} {q=r} {r=s} h (f2fCoprComposeMor {p} {q} {r} g f)
f2fCoprComposeAssoc (h ** hCond) (g ** gCond) (f ** fCond) = Refl

-------------------------------------------------------------
---- Natural transformations between finite copresheaves ----
-------------------------------------------------------------

-- A natural transformation between finite copresheaves
public export
F2FFinCoprNatTrans : {forest : Fin2Forest} ->
  F2FFinCopr forest -> F2FFinCopr forest -> Type
F2FFinCoprNatTrans {forest} p q =
  (obj : F2FObj forest) ->
  Fin (f2fFinCoprObjMap p obj) -> Fin (f2fFinCoprObjMap q obj)

-- The naturality condition for finite copresheaves
public export
F2FFinCoprNatCond : {forest : Fin2Forest} -> (p, q : F2FFinCopr forest) ->
  F2FFinCoprNatTrans {forest} p q -> Type
F2FFinCoprNatCond {forest} p q trans =
  (a, b : F2FObj forest) -> (mor : F2FMor a b) ->
  ExtEq {a=(Fin (f2fFinCoprObjMap p a))} {b=(Fin (f2fFinCoprObjMap q b))}
    (trans b . f2fFinCoprMorMap p mor) (f2fFinCoprMorMap q mor . trans a)

-- A morphism between finite copresheaves
public export
F2FFinCoprMor : {forest : Fin2Forest} ->
  F2FFinCopr forest -> F2FFinCopr forest -> Type
F2FFinCoprMor {forest} p q =
  DPair (F2FFinCoprNatTrans {forest} p q) (F2FFinCoprNatCond {forest} p q)

-- Get the natural transformation component of a finite copresheaf morphism
public export
f2fFinCoprMorTrans : {forest : Fin2Forest} -> {p, q : F2FFinCopr forest} ->
  F2FFinCoprMor {forest} p q -> F2FFinCoprNatTrans {forest} p q
f2fFinCoprMorTrans = DPair.fst

-- Get the naturality condition of a finite copresheaf morphism
public export
f2fFinCoprMorCond : {forest : Fin2Forest} -> {p, q : F2FFinCopr forest} ->
  (mor : F2FFinCoprMor {forest} p q) ->
  F2FFinCoprNatCond {forest} p q (f2fFinCoprMorTrans {forest} {p} {q} mor)
f2fFinCoprMorCond = DPair.snd

-- Identity finite copresheaf morphism
public export
f2fFinCoprIdMor : {forest : Fin2Forest} -> (p : F2FFinCopr forest) ->
  F2FFinCoprMor {forest} p p
f2fFinCoprIdMor p = ((\obj => id) ** \a, b, mor, x => Refl)

-- Composition of finite copresheaf morphisms
public export
f2fFinCoprComposeMor : {forest : Fin2Forest} -> {p, q, r : F2FFinCopr forest} ->
  F2FFinCoprMor {forest} q r -> F2FFinCoprMor {forest} p q ->
  F2FFinCoprMor {forest} p r
f2fFinCoprComposeMor {forest} {p} {q} {r} g f =
  ((\obj => fst g obj . fst f obj) ** \a, b, mor, x =>
    rewrite snd f a b mor x in
    snd g a b mor (fst f a x))

-- Left identity law for finite copresheaf morphisms
public export
f2fFinCoprComposeIdLeft : (fext : FunExt) -> {forest : Fin2Forest} ->
  {p, q : F2FFinCopr forest} -> (f : F2FFinCoprMor {forest} p q) ->
  f2fFinCoprComposeMor {p} {q} {r=q} (f2fFinCoprIdMor q) f = f
f2fFinCoprComposeIdLeft fext {forest} {p} {q} (trans ** cond) =
  dpEq12 Refl (funExt $ \a => funExt $ \b => funExt $ \mor => funExt $ \x =>
    uip)

-- Right identity law for finite copresheaf morphisms
public export
f2fFinCoprComposeIdRight : {forest : Fin2Forest} ->
  {p, q : F2FFinCopr forest} ->
  (f : F2FFinCoprMor {forest} p q) ->
  f2fFinCoprComposeMor {p} {q=p} {r=q} f (f2fFinCoprIdMor p) = f
f2fFinCoprComposeIdRight {forest} {p} {q} (trans ** cond) = Refl

-- Associativity of finite copresheaf morphism composition
public export
f2fFinCoprComposeAssoc : {forest : Fin2Forest} ->
  {p, q, r, s : F2FFinCopr forest} ->
  (h : F2FFinCoprMor {forest} r s) -> (g : F2FFinCoprMor {forest} q r) ->
  (f : F2FFinCoprMor {forest} p q) ->
  f2fFinCoprComposeMor {p} {q} {r=s}
    (f2fFinCoprComposeMor {p=q} {q=r} {r=s} h g)
    f =
  f2fFinCoprComposeMor {p} {q=r} {r=s}
    h
    (f2fFinCoprComposeMor {p} {q} {r} g f)
f2fFinCoprComposeAssoc (h ** hCond) (g ** gCond) (f ** fCond) = Refl

-- Convert a finite copresheaf morphism to a general copresheaf morphism
public export
f2fFinCoprMorToCoprMor : {forest : Fin2Forest} -> {p, q : F2FFinCopr forest} ->
  F2FFinCoprMor {forest} p q ->
  F2FCoprMor {forest} (f2fFinCoprToCopr p) (f2fFinCoprToCopr q)
f2fFinCoprMorToCoprMor {forest} {p} {q} finMor =
  (f2fFinCoprMorTrans finMor ** f2fFinCoprMorCond finMor)

----------------------------------------------
----------------------------------------------
---- Category of elements of a copresheaf ----
----------------------------------------------
----------------------------------------------

-- Objects in the category of elements
public export
F2FCoprElem : {forest : Fin2Forest} -> F2FCopr forest -> Type
F2FCoprElem {forest} copr =
  DPair (F2FObj forest) (f2fCoprObjMap copr)

-- Morphisms in the category of elements: just the underlying morphism
-- in the base category. The element in the codomain is determined by
-- applying the copresheaf's morphism map.
public export
F2FCoprElemMor : {forest : Fin2Forest} -> {copr : F2FCopr forest} ->
  F2FCoprElem copr -> F2FCoprElem copr -> Type
F2FCoprElemMor {forest} {copr} a b =
  (f : F2FMor (fst a) (fst b) ** f2fCoprMorMap copr f (snd a) = (snd b))

-- Simplified morphism: since y is determined by f and x, we only need f
public export
F2FCoprElemMorSimple : {forest : Fin2Forest} -> {copr : F2FCopr forest} ->
  F2FCoprElem copr -> F2FCoprElem copr -> Type
F2FCoprElemMorSimple {forest} {copr} a b = F2FMor (fst a) (fst b)

-- Get the codomain element from a simplified morphism
public export
f2fCoprElemMorCod : {forest : Fin2Forest} -> {copr : F2FCopr forest} ->
  {src, tgt : F2FCoprElem copr} ->
  F2FCoprElemMorSimple {copr} src tgt ->
  f2fCoprObjMap copr (fst tgt)
f2fCoprElemMorCod {copr} {src=(a ** x)} {tgt=(b ** _)} f =
  f2fCoprMorMap copr f x

-- Identity morphism in the category of elements
public export
f2fCoprElemIdMor : {forest : Fin2Forest} -> {copr : F2FCopr forest} ->
  (elem : F2FCoprElem copr) -> F2FCoprElemMorSimple {copr} elem elem
f2fCoprElemIdMor {forest} {copr} (obj ** _) = IdMor

-- Composition of morphisms in the category of elements
public export
f2fCoprElemComposeMor : {forest : Fin2Forest} -> {copr : F2FCopr forest} ->
  {a, b, c : F2FCoprElem copr} ->
  F2FCoprElemMorSimple {copr} b c -> F2FCoprElemMorSimple {copr} a b ->
  F2FCoprElemMorSimple {copr} a c
f2fCoprElemComposeMor {forest} {copr} {a} {b} {c} g f = f2fComposeMor g f

-- Convert a simplified morphism to a standard morphism with proof
public export
f2fCoprElemMorSimpleToMor : {forest : Fin2Forest} -> {copr : F2FCopr forest} ->
  {src : F2FCoprElem copr} ->
  {tgt : F2FCoprElem copr} ->
  (f : F2FCoprElemMorSimple {copr} src tgt) ->
  F2FCoprElemMor {copr} src
    (fst tgt ** f2fCoprElemMorCod {copr} {src} {tgt} f)
f2fCoprElemMorSimpleToMor {copr} {src=(a ** x)} {tgt=(b ** y)} f =
  (f ** Refl)

---- Finite version of category of elements --------

-- Objects in the category of elements of a finite copresheaf
public export
F2FFinCoprElem : {forest : Fin2Forest} -> F2FFinCopr forest -> Type
F2FFinCoprElem {forest} copr =
  DPair (F2FObj forest) (Fin . f2fFinCoprObjMap copr)

-- Convert a finite category of elements to a general category of elements
public export
f2fFinCoprElemToCoprElem : {forest : Fin2Forest} ->
  (copr : F2FFinCopr forest) ->
  F2FFinCoprElem {forest} copr -> F2FCoprElem {forest} (f2fFinCoprToCopr copr)
f2fFinCoprElemToCoprElem copr = id

-- Morphisms in the category of elements of a finite copresheaf (simplified)
public export
F2FFinCoprElemMorSimple : {forest : Fin2Forest} -> {copr : F2FFinCopr forest} ->
  F2FFinCoprElem copr -> F2FFinCoprElem copr -> Type
F2FFinCoprElemMorSimple {forest} {copr} a b = F2FMor {forest} (fst a) (fst b)

-- Get the codomain element from a simplified morphism
public export
f2fFinCoprElemMorCod : {forest : Fin2Forest} -> {copr : F2FFinCopr forest} ->
  {src, tgt : F2FFinCoprElem copr} ->
  F2FFinCoprElemMorSimple {copr} src tgt ->
  Fin (f2fFinCoprObjMap copr (fst tgt))
f2fFinCoprElemMorCod {copr} {src=(a ** x)} {tgt=(b ** _)} f =
  f2fFinCoprMorMap copr f x

-- Identity morphism in the finite category of elements
public export
f2fFinCoprElemIdMor : {forest : Fin2Forest} -> {copr : F2FFinCopr forest} ->
  (elem : F2FFinCoprElem copr) -> F2FFinCoprElemMorSimple {copr} elem elem
f2fFinCoprElemIdMor {forest} {copr} (obj ** _) = IdMor

-- Composition of morphisms in the finite category of elements
public export
f2fFinCoprElemComposeMor : {forest : Fin2Forest} ->
  {copr : F2FFinCopr forest} -> {a, b, c : F2FFinCoprElem copr} ->
  F2FFinCoprElemMorSimple {copr} b c -> F2FFinCoprElemMorSimple {copr} a b ->
  F2FFinCoprElemMorSimple {copr} a c
f2fFinCoprElemComposeMor {forest} {copr} {a} {b} {c} g f = f2fComposeMor g f

-- Convert a simplified finite morphism to a standard morphism with proof
public export
f2fFinCoprElemMorSimpleToMor : {forest : Fin2Forest} ->
  {copr : F2FFinCopr forest} ->
  {src : F2FFinCoprElem copr} ->
  {tgt : F2FFinCoprElem copr} ->
  (f : F2FFinCoprElemMorSimple {copr} src tgt) ->
  F2FCoprElemMor {copr = f2fFinCoprToCopr copr}
    (f2fFinCoprElemToCoprElem copr src)
    (fst tgt ** f2fFinCoprElemMorCod {copr} {src} {tgt} f)
f2fFinCoprElemMorSimpleToMor {copr} {src=(a ** x)} {tgt=(b ** y)} f =
  (f ** Refl)

----------------------------------------------------------------
----------------------------------------------------------------
---- Parametric right adjoint functors on two-level forests ----
----------------------------------------------------------------
----------------------------------------------------------------

-- Following
-- https://ncatlab.org/nlab/show/parametric+right+adjoint#generic_morphisms,
-- A p.r.a. functor T : [I^op, Set] → [J^op, Set] is determined by:
-- 1. An object T1 ∈ [J^op, Set]
-- 2. A functor E_T : el(T1)^op → [I^op, Set]

-- Object mapping of a functor from el(copr)^op to copresheaves on srcForest
-- Maps each element to a copresheaf on srcForest
public export
F2FElemToCoprsObjMap : {tgtForest : Fin2Forest} ->
  F2FCopr tgtForest -> Fin2Forest -> Type
F2FElemToCoprsObjMap {tgtForest} copr srcForest =
  F2FCoprElem {forest=tgtForest} copr -> F2FCopr srcForest

-- Morphism mapping of a functor from el(copr)^op to copresheaves on srcForest
-- Since we're mapping from the opposite category, a morphism f : b -> a in
-- el(copr) maps to a morphism from objMap(a) to objMap(b)
public export
F2FElemToCoprsMorMap : (tgtForest : Fin2Forest) ->
  (copr : F2FCopr tgtForest) -> (srcForest : Fin2Forest) ->
  F2FElemToCoprsObjMap {tgtForest} copr srcForest -> Type
F2FElemToCoprsMorMap tgtForest copr srcForest objMap =
  (a, b : F2FCoprElem {forest=tgtForest} copr) ->
  F2FCoprElemMorSimple {copr} b a ->
  F2FCoprMor {forest=srcForest} (objMap a) (objMap b)

-- Extensional equality of copresheaf morphisms
-- Two morphisms are equivalent if their computational parts are extensionally
-- equal, ignoring the naturality proofs
public export
F2FCoprMorExtEq : {forest : Fin2Forest} -> {p, q : F2FCopr forest} ->
  F2FCoprMor {forest} p q -> F2FCoprMor {forest} p q -> Type
F2FCoprMorExtEq {forest} {p} {q} trans1 trans2 =
  (obj : F2FObj forest) ->
  ExtEq {a=(f2fCoprObjMap p obj)} {b=(f2fCoprObjMap q obj)}
    (fst trans1 obj) (fst trans2 obj)

-- Functor law: preservation of identity
-- For any element a, mapping the identity morphism gives the identity morphism
-- (up to extensional equality)
public export
F2FElemToCoprsPresId : (tgtForest : Fin2Forest) ->
  (copr : F2FCopr tgtForest) -> (srcForest : Fin2Forest) ->
  (objMap : F2FElemToCoprsObjMap {tgtForest} copr srcForest) ->
  F2FElemToCoprsMorMap tgtForest copr srcForest objMap -> Type
F2FElemToCoprsPresId tgtForest copr srcForest objMap morMap =
  (a : F2FCoprElem {forest=tgtForest} copr) ->
  F2FCoprMorExtEq (morMap a a (f2fCoprElemIdMor a)) (f2fCoprIdMor (objMap a))

-- Functor law: preservation of composition
-- For morphisms f : c -> b and g : b -> a in el(copr), we have
-- morMap(g ∘ f) = morMap(f) ∘ morMap(g) (note the reversal)
-- (up to extensional equality)
public export
F2FElemToCoprsPresComp : (tgtForest : Fin2Forest) ->
  (copr : F2FCopr tgtForest) -> (srcForest : Fin2Forest) ->
  (objMap : F2FElemToCoprsObjMap {tgtForest} copr srcForest) ->
  F2FElemToCoprsMorMap tgtForest copr srcForest objMap -> Type
F2FElemToCoprsPresComp tgtForest copr srcForest objMap morMap =
  (a, b, c : F2FCoprElem {forest=tgtForest} copr) ->
  (g : F2FCoprElemMorSimple {copr} b a) ->
  (f : F2FCoprElemMorSimple {copr} c b) ->
  F2FCoprMorExtEq
    (morMap a c (f2fCoprElemComposeMor g f))
    (f2fCoprComposeMor (morMap b c f) (morMap a b g))

-- Complete specification of a functor E_T : el(copr)^op → [srcForest^op, Set]
-- Includes object map, morphism map, and functor laws
public export
F2FElemToCoprsFunctor : (tgtForest : Fin2Forest) ->
  (copr : F2FCopr tgtForest) -> (srcForest : Fin2Forest) -> Type
F2FElemToCoprsFunctor tgtForest copr srcForest =
  DPair (F2FElemToCoprsObjMap {tgtForest} copr srcForest) $ \objMap =>
  DPair (F2FElemToCoprsMorMap tgtForest copr srcForest objMap) $ \morMap =>
  (F2FElemToCoprsPresId tgtForest copr srcForest objMap morMap,
   F2FElemToCoprsPresComp tgtForest copr srcForest objMap morMap)

-- Get the object mapping of an element-to-copresheaves functor
public export
f2fElemToCoprsFunctorObjMap : {tgtForest : Fin2Forest} ->
  {copr : F2FCopr tgtForest} -> {srcForest : Fin2Forest} ->
  F2FElemToCoprsFunctor tgtForest copr srcForest ->
  F2FElemToCoprsObjMap {tgtForest} copr srcForest
f2fElemToCoprsFunctorObjMap = DPair.fst

-- Get the morphism mapping of an element-to-copresheaves functor
public export
f2fElemToCoprsFunctorMorMap : {tgtForest : Fin2Forest} ->
  {copr : F2FCopr tgtForest} -> {srcForest : Fin2Forest} ->
  (f : F2FElemToCoprsFunctor tgtForest copr srcForest) ->
  F2FElemToCoprsMorMap tgtForest copr srcForest
    (f2fElemToCoprsFunctorObjMap {tgtForest} {copr} {srcForest} f)
f2fElemToCoprsFunctorMorMap {tgtForest} {copr} {srcForest} f =
  DPair.fst (DPair.snd f)

-- Get the identity preservation proof of an element-to-copresheaves functor
public export
f2fElemToCoprsFunctorPresId : {tgtForest : Fin2Forest} ->
  {copr : F2FCopr tgtForest} -> {srcForest : Fin2Forest} ->
  (f : F2FElemToCoprsFunctor tgtForest copr srcForest) ->
  F2FElemToCoprsPresId tgtForest copr srcForest
    (f2fElemToCoprsFunctorObjMap {tgtForest} {copr} {srcForest} f)
    (f2fElemToCoprsFunctorMorMap {tgtForest} {copr} {srcForest} f)
f2fElemToCoprsFunctorPresId {tgtForest} {copr} {srcForest} f =
  fst (DPair.snd (DPair.snd f))

-- Get the composition preservation proof of an element-to-copresheaves functor
public export
f2fElemToCoprsFunctorPresComp : {tgtForest : Fin2Forest} ->
  {copr : F2FCopr tgtForest} -> {srcForest : Fin2Forest} ->
  (f : F2FElemToCoprsFunctor tgtForest copr srcForest) ->
  F2FElemToCoprsPresComp tgtForest copr srcForest
    (f2fElemToCoprsFunctorObjMap {tgtForest} {copr} {srcForest} f)
    (f2fElemToCoprsFunctorMorMap {tgtForest} {copr} {srcForest} f)
f2fElemToCoprsFunctorPresComp {tgtForest} {copr} {srcForest} f =
  snd (DPair.snd (DPair.snd f))

-- A PRA functor from copresheaves on srcForest to copresheaves on tgtForest
public export
F2FPRA : Fin2Forest -> Fin2Forest -> Type
F2FPRA srcForest tgtForest =
  DPair (F2FCopr tgtForest)
    (\t1 => F2FElemToCoprsFunctor tgtForest t1 srcForest)

-- Get the T1 component of a PRA functor
public export
f2fPRA_T1 : {srcForest, tgtForest : Fin2Forest} ->
  F2FPRA srcForest tgtForest -> F2FCopr tgtForest
f2fPRA_T1 = fst

-- Get the E_T functor component of a PRA functor
public export
f2fPRA_ET : {srcForest, tgtForest : Fin2Forest} ->
  (f : F2FPRA srcForest tgtForest) ->
  F2FElemToCoprsFunctor tgtForest
    (f2fPRA_T1 {srcForest} {tgtForest} f)
    srcForest
f2fPRA_ET = snd

---- Finite versions of PRA functors -----

-- Object mapping of a functor from el(copr)^op to finite copresheaves
-- on srcForest. Maps each element to a finite copresheaf on srcForest
public export
F2FFinElemToFinCoprsObjMap : {tgtForest : Fin2Forest} ->
  F2FFinCopr tgtForest -> Fin2Forest -> Type
F2FFinElemToFinCoprsObjMap {tgtForest} copr srcForest =
  F2FFinCoprElem {forest=tgtForest} copr -> F2FFinCopr srcForest

-- Morphism mapping of a functor from el(copr)^op to finite copresheaves
-- on srcForest. Since we're mapping from the opposite category, a morphism
-- f : b -> a in el(copr) maps to a morphism from objMap(a) to objMap(b)
public export
F2FFinElemToFinCoprsMorMap : (tgtForest : Fin2Forest) ->
  (copr : F2FFinCopr tgtForest) -> (srcForest : Fin2Forest) ->
  F2FFinElemToFinCoprsObjMap {tgtForest} copr srcForest -> Type
F2FFinElemToFinCoprsMorMap tgtForest copr srcForest objMap =
  (a, b : F2FFinCoprElem {forest=tgtForest} copr) ->
  F2FFinCoprElemMorSimple {copr} b a ->
  F2FFinCoprMor {forest=srcForest} (objMap a) (objMap b)

-- Extensional equality of finite copresheaf morphisms
-- Two morphisms are equivalent if their computational parts are extensionally
-- equal, ignoring the naturality proofs
public export
F2FFinCoprMorExtEq : {forest : Fin2Forest} -> {p, q : F2FFinCopr forest} ->
  F2FFinCoprMor {forest} p q -> F2FFinCoprMor {forest} p q -> Type
F2FFinCoprMorExtEq {forest} {p} {q} trans1 trans2 =
  (obj : F2FObj forest) ->
  ExtEq {a=(Fin (f2fFinCoprObjMap p obj))} {b=(Fin (f2fFinCoprObjMap q obj))}
    (fst trans1 obj) (fst trans2 obj)

-- Functor law: preservation of identity (finite version)
public export
F2FFinElemToFinCoprsPresId : (tgtForest : Fin2Forest) ->
  (copr : F2FFinCopr tgtForest) -> (srcForest : Fin2Forest) ->
  (objMap : F2FFinElemToFinCoprsObjMap {tgtForest} copr srcForest) ->
  F2FFinElemToFinCoprsMorMap tgtForest copr srcForest objMap -> Type
F2FFinElemToFinCoprsPresId tgtForest copr srcForest objMap morMap =
  (a : F2FFinCoprElem {forest=tgtForest} copr) ->
  F2FFinCoprMorExtEq
    (morMap a a (f2fFinCoprElemIdMor a))
    (f2fFinCoprIdMor (objMap a))

-- Functor law: preservation of composition (finite version)
public export
F2FFinElemToFinCoprsPresComp : (tgtForest : Fin2Forest) ->
  (copr : F2FFinCopr tgtForest) -> (srcForest : Fin2Forest) ->
  (objMap : F2FFinElemToFinCoprsObjMap {tgtForest} copr srcForest) ->
  F2FFinElemToFinCoprsMorMap tgtForest copr srcForest objMap -> Type
F2FFinElemToFinCoprsPresComp tgtForest copr srcForest objMap morMap =
  (a, b, c : F2FFinCoprElem {forest=tgtForest} copr) ->
  (g : F2FFinCoprElemMorSimple {copr} b a) ->
  (f : F2FFinCoprElemMorSimple {copr} c b) ->
  F2FFinCoprMorExtEq
    (morMap a c (f2fFinCoprElemComposeMor g f))
    (f2fFinCoprComposeMor (morMap b c f) (morMap a b g))

-- Complete specification of a finite functor E_T : el(copr)^op →
-- [srcForest^op, FinSet]
public export
F2FFinElemToFinCoprsFunctor : (tgtForest : Fin2Forest) ->
  (copr : F2FFinCopr tgtForest) -> (srcForest : Fin2Forest) -> Type
F2FFinElemToFinCoprsFunctor tgtForest copr srcForest =
  DPair (F2FFinElemToFinCoprsObjMap {tgtForest} copr srcForest) $ \objMap =>
  DPair (F2FFinElemToFinCoprsMorMap tgtForest copr srcForest objMap) $
    \morMap =>
  (F2FFinElemToFinCoprsPresId tgtForest copr srcForest objMap morMap,
   F2FFinElemToFinCoprsPresComp tgtForest copr srcForest objMap morMap)

-- A finite PRA functor from finite copresheaves on srcForest to finite
-- copresheaves on tgtForest
public export
F2FFinPRA : Fin2Forest -> Fin2Forest -> Type
F2FFinPRA srcForest tgtForest =
  DPair (F2FFinCopr tgtForest)
    (\t1 => F2FFinElemToFinCoprsFunctor tgtForest t1 srcForest)

-- Get the T1 component of a finite PRA functor
public export
f2fFinPRA_T1 : {srcForest, tgtForest : Fin2Forest} ->
  F2FFinPRA srcForest tgtForest -> F2FFinCopr tgtForest
f2fFinPRA_T1 = fst

-- Get the E_T functor component of a finite PRA functor
public export
f2fFinPRA_ET : {srcForest, tgtForest : Fin2Forest} ->
  (f : F2FFinPRA srcForest tgtForest) ->
  F2FFinElemToFinCoprsFunctor tgtForest
    (f2fFinPRA_T1 {srcForest} {tgtForest} f)
    srcForest
f2fFinPRA_ET = snd

---- Translation from finite to general PRA functors -----

-- Convert a finite element-to-copresheaves object map to a general one
public export
f2fFinElemToFinCoprsObjMapToElemToCoprsObjMap : {tgtForest : Fin2Forest} ->
  (copr : F2FFinCopr tgtForest) -> {srcForest : Fin2Forest} ->
  F2FFinElemToFinCoprsObjMap {tgtForest} copr srcForest ->
  F2FElemToCoprsObjMap {tgtForest} (f2fFinCoprToCopr copr) srcForest
f2fFinElemToFinCoprsObjMapToElemToCoprsObjMap copr finFunc elem =
  f2fFinCoprToCopr (finFunc elem)

-- Convert a finite element-to-copresheaves functor to a general one
public export
f2fFinElemToFinCoprsFunctorToElemToCoprsFunctor : {tgtForest : Fin2Forest} ->
  (copr : F2FFinCopr tgtForest) -> {srcForest : Fin2Forest} ->
  F2FFinElemToFinCoprsFunctor tgtForest copr srcForest ->
  F2FElemToCoprsFunctor tgtForest (f2fFinCoprToCopr copr) srcForest
f2fFinElemToFinCoprsFunctorToElemToCoprsFunctor {tgtForest} {srcForest} copr
  (finObjMap ** finMorMap ** (finPresId, finPresComp)) =
  let
    -- Convert the object mapping
    objMap : F2FElemToCoprsObjMap {tgtForest} (f2fFinCoprToCopr copr) srcForest
    objMap elem = f2fFinCoprToCopr (finObjMap elem)

    -- Convert the morphism mapping
    morMap : F2FElemToCoprsMorMap tgtForest (f2fFinCoprToCopr copr) srcForest
             objMap
    morMap a b f =
      f2fFinCoprMorToCoprMor (finMorMap a b f)

    -- Convert the identity preservation proof
    presId : F2FElemToCoprsPresId tgtForest (f2fFinCoprToCopr copr) srcForest
             objMap morMap
    presId (x ** i) = \y, j => finPresId (x ** i) y j

    -- Convert the composition preservation proof
    presComp : F2FElemToCoprsPresComp tgtForest (f2fFinCoprToCopr copr)
               srcForest objMap morMap
    presComp a b c g f x i = finPresComp a b c g f x i
  in (objMap ** morMap ** (presId, presComp))

-- Convert a finite PRA functor to a general PRA functor
public export
f2fFinPRAToPRA : {srcForest, tgtForest : Fin2Forest} ->
  F2FFinPRA srcForest tgtForest -> F2FPRA srcForest tgtForest
f2fFinPRAToPRA {srcForest} {tgtForest} finF =
  (f2fFinCoprToCopr (f2fFinPRA_T1 finF) **
   f2fFinElemToFinCoprsFunctorToElemToCoprsFunctor
     (f2fFinPRA_T1 finF)
     (f2fFinPRA_ET finF))

-----------------------------------------------------------------------
-----------------------------------------------------------------------
---- Interpretation of PRA functors as functors between copresheaves --
-----------------------------------------------------------------------
-----------------------------------------------------------------------

-- The key theorem: a PRA functor (T1, E_T) induces a functor
-- T : [C^op, Set] → [D^op, Set] via the dependent sum formula:
--
-- T(Z)(j) = Σ_{i ∈ T1(j)} Hom[C^op, Set](E_T(j,i), Z)
--
-- In concrete terms, T(Z)(j) is a dependent pair consisting of:
-- 1. An element i ∈ T1(j) (where T1 is a copresheaf on D)
-- 2. A natural transformation α : E_T(j,i) ⇒ Z
--
-- Note: This is the standard PRA formula. There is a generalization using
-- coends/ends called "Generalized Polynomial Functors" (Fiore et al.) which
-- we may explore in future work.

-- Object mapping for the PRA functor interpretation
-- Given a copresheaf Z on srcForest, produces an object mapping on tgtForest
-- where T(Z)(j) = Σ_{i ∈ T1(j)} Hom(E_T(j,i), Z)
public export
f2fPRAObjMapObj : {srcForest, tgtForest : Fin2Forest} ->
  F2FPRA srcForest tgtForest ->
  F2FCopr srcForest -> F2FCoprObjMap tgtForest
f2fPRAObjMapObj {srcForest} {tgtForest} pra z j =
  DPair (f2fCoprObjMap (f2fPRA_T1 pra) j) $ \i =>
  -- The type of natural transformations from E_T(j,i) to Z
  F2FCoprMor {forest=srcForest}
    (f2fElemToCoprsFunctorObjMap (f2fPRA_ET pra) (j ** i)) z

-- Morphism mapping for the PRA functor interpretation
public export
f2fPRAObjMapMor : {srcForest, tgtForest : Fin2Forest} ->
  (pra : F2FPRA srcForest tgtForest) ->
  (z : F2FCopr srcForest) ->
  F2FCoprMorMap {forest=tgtForest} (f2fPRAObjMapObj pra z)
f2fPRAObjMapMor {srcForest} {tgtForest} pra z {a=j} {b=k} f (i ** alpha) =
  -- The morphism f : j -> k acts on the element i via T1's morphism map
  -- In el(T1), we have a morphism from (j,i) to (k, T1(f)(i))
  -- E_T being contravariant gives us E_T(k, T1(f)(i)) -> E_T(j,i)
  -- We then compose: E_T(k,i') -> E_T(j,i) -> z
  (f2fCoprMorMap (f2fPRA_T1 pra) f i **
   f2fCoprComposeMor {forest=srcForest}
     alpha
     (f2fElemToCoprsFunctorMorMap (f2fPRA_ET pra)
       (k ** f2fCoprMorMap (f2fPRA_T1 pra) f i)
       (j ** i)
       f))

-- Complete object mapping: combines object and morphism mappings into a
-- copresheaf
public export
f2fPRAObjMap : {srcForest, tgtForest : Fin2Forest} ->
  F2FPRA srcForest tgtForest ->
  F2FCopr srcForest -> F2FCopr tgtForest
f2fPRAObjMap {srcForest} {tgtForest} pra z =
  (f2fPRAObjMapObj pra z ** f2fPRAObjMapMor pra z)

-- Natural transformation component of the morphism mapping
public export
f2fPRAMorMapTrans : {srcForest, tgtForest : Fin2Forest} ->
  (pra : F2FPRA srcForest tgtForest) ->
  (z, z' : F2FCopr srcForest) ->
  F2FCoprMor {forest=srcForest} z z' ->
  F2FCoprNatTrans {forest=tgtForest} (f2fPRAObjMap pra z) (f2fPRAObjMap pra z')
f2fPRAMorMapTrans {srcForest} {tgtForest} pra z z' natTrans j (i ** alpha) =
  -- For each (i, alpha) in T(Z)(j), we get (i, natTrans ∘ alpha) in T(Z')(j)
  -- The index i stays the same, we just compose the natural transformation
  (i ** f2fCoprComposeMor {forest=srcForest} natTrans alpha)

-- Naturality condition for the morphism mapping
public export
f2fPRAMorMapNatCond : {srcForest, tgtForest : Fin2Forest} ->
  (pra : F2FPRA srcForest tgtForest) ->
  (z, z' : F2FCopr srcForest) ->
  (natTrans : F2FCoprMor {forest=srcForest} z z') ->
  F2FCoprNatCond {forest=tgtForest} (f2fPRAObjMap pra z) (f2fPRAObjMap pra z')
    (f2fPRAMorMapTrans pra z z' natTrans)
f2fPRAMorMapNatCond {srcForest} {tgtForest} pra z z' natTrans a b mor
  (i ** alpha) =
  -- The naturality condition reduces to proving equality of dependent pairs.
  -- The first components are equal by definition, and the second components
  -- differ only by associativity of composition.
  dpEq12 Refl (sym (f2fCoprComposeAssoc {forest=srcForest}
                      natTrans
                      alpha
                      (f2fElemToCoprsFunctorMorMap (f2fPRA_ET pra)
                        (b ** f2fCoprMorMap (f2fPRA_T1 pra) mor i)
                        (a ** i)
                        mor)))

-- Morphism mapping for the PRA functor interpretation
-- Maps natural transformations between copresheaves on srcForest to
-- natural transformations between copresheaves on tgtForest
public export
f2fPRAMorMap : {srcForest, tgtForest : Fin2Forest} ->
  (pra : F2FPRA srcForest tgtForest) ->
  (z, z' : F2FCopr srcForest) ->
  F2FCoprMor {forest=srcForest} z z' ->
  F2FCoprMor {forest=tgtForest} (f2fPRAObjMap pra z) (f2fPRAObjMap pra z')
f2fPRAMorMap {srcForest} {tgtForest} pra z z' natTrans =
  (f2fPRAMorMapTrans pra z z' natTrans ** f2fPRAMorMapNatCond pra z z' natTrans)
