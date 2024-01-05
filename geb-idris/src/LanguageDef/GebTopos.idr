module LanguageDef.GebTopos

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.ProgFinSet
import public LanguageDef.PolyCat
import public LanguageDef.Syntax
import public LanguageDef.DiagramCat
import public LanguageDef.Adjunctions

%default total

--------------------------------
--------------------------------
---- Yoneda lemma utilities ----
--------------------------------
--------------------------------

------------------------------------------
---- Internal natural transformations ----
------------------------------------------

public export
CovarToCovarHomRep : {obj : Type} -> HomEndofunctor obj
CovarToCovarHomRep {obj} hom (a, b) =
  InternalNTFromCovarHom {obj} hom b (InternalCovarHom hom a)

public export
CovarToContravarHomRep : {obj : Type} -> HomEndofunctor obj
CovarToContravarHomRep {obj} hom (a, b) =
  InternalNTFromCovarHom {obj} hom a (InternalContravarHom hom b)

public export
ContravarToContravarHomRep : {obj : Type} -> HomEndofunctor obj
ContravarToContravarHomRep {obj} hom (a, b) =
  InternalNTFromContravarHom {obj} hom a (InternalContravarHom hom b)

public export
ContravarToCovarHomRep : {obj : Type} -> HomEndofunctor obj
ContravarToCovarHomRep {obj} hom (a, b) =
  InternalNTFromContravarHom {obj} hom b (InternalCovarHom hom a)

public export
data HomRep : {0 obj : Type} -> HomEndofunctor obj where
  HRCovarToCovar :
    CovarToCovarHomRep hom (a, b) -> HomRep hom (a, b)
  HRCovarToContravar :
    CovarToContravarHomRep hom (a, b) -> HomRep hom (a, b)
  HRContravarToContravar :
    ContravarToContravarHomRep hom (a, b) -> HomRep hom (a, b)
  HRContravarToCovar :
    ContravarToCovarHomRep hom (a, b) -> HomRep hom (a, b)

public export
CovarToCovarHomRepExtEq :
  {obj : Type} -> {hom : HomSlice obj} -> {a, b : obj} ->
  (alpha, beta : CovarToCovarHomRep hom (a, b)) -> Type
CovarToCovarHomRepExtEq {obj} {hom} {a} {b} =
  CopresheafNTExtEq {obj}
    {f=(InternalCovarHom hom b)} {g=(InternalCovarHom hom a)}

public export
CovarToContravarHomRepExtEq :
  {obj : Type} -> {hom : HomSlice obj} -> {a, b : obj} ->
  (alpha, beta : CovarToContravarHomRep hom (a, b)) -> Type
CovarToContravarHomRepExtEq {obj} {hom} {a} {b} =
  CopresheafNTExtEq {obj}
    {f=(InternalCovarHom hom a)} {g=(InternalContravarHom hom b)}

public export
ContravarToContravarHomRepExtEq :
  {obj : Type} -> {hom : HomSlice obj} -> {a, b : obj} ->
  (alpha, beta : ContravarToContravarHomRep hom (a, b)) -> Type
ContravarToContravarHomRepExtEq {obj} {hom} {a} {b} =
  CopresheafNTExtEq {obj}
    {f=(InternalContravarHom hom a)} {g=(InternalContravarHom hom b)}

public export
ContravarToCovarHomRepExtEq :
  {obj : Type} -> {hom : HomSlice obj} -> {a, b : obj} ->
  (alpha, beta : ContravarToCovarHomRep hom (a, b)) -> Type
ContravarToCovarHomRepExtEq {obj} {hom} {a} {b} =
  CopresheafNTExtEq {obj}
    {f=(InternalContravarHom hom b)} {g=(InternalCovarHom hom a)}

public export
CovarToCovarHomSetRep : (obj : Type) -> HomEndofunctor obj
CovarToCovarHomSetRep obj hom (a, b) =
  hom (a, b) -> CovarToCovarHomRep hom (a, b)

public export
CovarToCovarCatRep : {obj : Type} -> HomSlice obj -> Type
CovarToCovarCatRep {obj} hom =
  (a, b : obj) -> CovarToCovarHomSetRep obj hom (a, b)

public export
CovarToContravarHomSetRep : (obj : Type) -> HomEndofunctor obj
CovarToContravarHomSetRep obj hom (a, b) =
  hom (a, b) -> CovarToContravarHomRep hom (a, b)

public export
ContravarToContravarHomSetRep : (obj : Type) -> HomEndofunctor obj
ContravarToContravarHomSetRep obj hom (a, b) =
  hom (a, b) -> ContravarToContravarHomRep hom (a, b)

public export
ContravarToContravarCatRep : {obj : Type} -> HomSlice obj -> Type
ContravarToContravarCatRep {obj} hom =
  (a, b : obj) -> ContravarToContravarHomSetRep obj hom (a, b)

public export
ContravarToCovarHomSetRep : (obj : Type) -> HomEndofunctor obj
ContravarToCovarHomSetRep obj hom (a, b) =
  hom (a, b) -> ContravarToCovarHomRep hom (a, b)

public export
data HomSetRep : (obj : Type) -> HomEndofunctor obj where
  HSRCovarToCovar :
    CovarToCovarHomSetRep obj hom (a, b) -> HomSetRep obj hom (a, b)
  HSRCovarToContravar :
    CovarToContravarHomSetRep obj hom (a, b) -> HomSetRep obj hom (a, b)
  HSRContravarToContravar :
    ContravarToContravarHomSetRep obj hom (a, b) -> HomSetRep obj hom (a, b)
  HSRContravarToCovar :
    ContravarToCovarHomSetRep obj hom (a, b) -> HomSetRep obj hom (a, b)

public export
CovarHomHomRep :
  (obj : Type) -> (hom : HomSlice obj) -> obj -> SliceObj obj
CovarHomHomRep obj hom = CovarToCovarHomSetRep obj hom .* MkPair

public export
CovarHomHomSetRep : (obj : Type) -> (hom : HomSlice obj) -> obj -> Type
CovarHomHomSetRep obj hom =
  Pi {a=obj} . CovarHomHomRep obj hom

public export
CovarHomCatRep : (obj : Type) -> (hom : HomSlice obj) -> Type
CovarHomCatRep obj hom =
  Pi {a=obj} $ CovarHomHomSetRep obj hom

public export
CovarToContravarCatRep : (obj : Type) -> (hom : HomSlice obj) -> Type
CovarToContravarCatRep obj hom =
  (a, b : obj) -> CovarToContravarHomSetRep obj hom (a, b)

public export
ContravarHomHomRep :
  (obj : Type) -> (hom : HomSlice obj) -> obj -> SliceObj obj
ContravarHomHomRep obj hom = ContravarToContravarHomSetRep obj hom .* MkPair

public export
ContravarHomHomSetRep : (obj : Type) -> (hom : HomSlice obj) -> obj -> Type
ContravarHomHomSetRep obj hom =
  Pi {a=obj} . ContravarHomHomRep obj hom

public export
ContravarHomCatRep : (obj : Type) -> HomSlice obj -> Type
ContravarHomCatRep obj hom =
  Pi {a=obj} $ ContravarHomHomSetRep obj hom

public export
ContravarToCovarCatRep : (obj : Type) -> HomSlice obj -> Type
ContravarToCovarCatRep obj hom =
  (a, b : obj) -> ContravarToCovarHomSetRep obj hom (a, b)

public export
data YonedaHomSetRep : {obj : Type} -> HomSlice obj -> SliceObj obj where
  YHSRCovar : CovarHomHomSetRep obj hom a -> YonedaHomSetRep {obj} hom a
  YHSRContravar : ContravarHomHomSetRep obj hom a -> YonedaHomSetRep {obj} hom a

public export
YonedaCatRep : {obj : Type} -> HomSlice obj -> Type
YonedaCatRep {obj} hom = Pi {a=obj} (YonedaHomSetRep {obj} hom)

public export
CovarToCovarIdRep : {obj : Type} -> {hom : HomSlice obj} ->
  (a : obj) -> CovarToCovarHomRep {obj} hom (a, a)
CovarToCovarIdRep {obj} {hom} a c = id {a=(hom (a, c))}

public export
CovarToCovarComposeRep : {obj : Type} -> {hom : HomSlice obj} ->
  {a, b, c : obj} ->
  CovarToCovarHomRep {obj} hom (b, c) ->
  CovarToCovarHomRep {obj} hom (a, b) ->
  CovarToCovarHomRep {obj} hom (a, c)
CovarToCovarComposeRep {obj} {hom} {a} {b} {c} g f d = f d . g d

public export
ContravarToContravarIdRep : {obj : Type} -> {hom : HomSlice obj} ->
  (a : obj) -> ContravarToContravarHomRep {obj} hom (a, a)
ContravarToContravarIdRep {obj} {hom} a c = id {a=(hom (c, a))}

public export
ContravarToContravarComposeRep : {obj : Type} -> {hom : HomSlice obj} ->
  {a, b, c : obj} ->
  ContravarToContravarHomRep {obj} hom (b, c) ->
  ContravarToContravarHomRep {obj} hom (a, b) ->
  ContravarToContravarHomRep {obj} hom (a, c)
ContravarToContravarComposeRep {obj} {hom} {a} {b} {c} g f d = g d . f d

public export
CovarEqImpliesContravar : {obj : Type} -> {hom : HomSlice obj} ->
  CovarHomCatRep obj hom -> ContravarHomCatRep obj hom -> Type
CovarEqImpliesContravar {obj} {hom} covar contravar =
  {a, b : obj} -> (f, g : hom (a, b)) ->
  CovarToCovarHomRepExtEq
    {a} {b} {hom} (covar a b f) (covar a b g) ->
  ContravarToContravarHomRepExtEq
    {a} {b} {hom} (contravar a b f) (contravar a b g)

public export
ContravarEqImpliesCovar : {obj : Type} -> {hom : HomSlice obj} ->
  CovarHomCatRep obj hom -> ContravarHomCatRep obj hom -> Type
ContravarEqImpliesCovar {obj} {hom} covar contravar =
  {a, b : obj} -> (f, g : hom (a, b)) ->
  ContravarToContravarHomRepExtEq
    {a} {b} {hom} (contravar a b f) (contravar a b g) ->
  CovarToCovarHomRepExtEq
    {a} {b} {hom} (covar a b f) (covar a b g)

------------------------------------
---- Free-category Yoneda lemma ----
------------------------------------

public export
FreeCovarHomYonedaR : {obj : Type} -> {hom : HomSlice obj} ->
  (a : obj) -> (f : SliceObj obj) ->
  InternalNTFromCovarHom {obj} (FreeHomM obj hom) a f -> f a
FreeCovarHomYonedaR {obj} {hom} a f alpha =
  alpha a $ chId {obj} hom a

public export
FreeCovarHomYonedaL : {obj : Type} -> {hom : HomSlice obj} ->
  (a : obj) -> (f : SliceObj obj) ->
  (fmap : (a, b : obj) -> hom (a, b) -> f a -> f b) ->
  f a -> InternalNTFromCovarHom {obj} (FreeHomM obj hom) a f
FreeCovarHomYonedaL {obj} {hom} a f fmap fa b mab =
  chFreeFMap fmap a b mab fa

public export
FreeContravarHomYonedaR : {obj : Type} -> {hom : HomSlice obj} ->
  (a : obj) -> (f : SliceObj obj) ->
  InternalNTFromContravarHom {obj} (FreeHomM obj hom) a f -> f a
FreeContravarHomYonedaR {obj} {hom} a f alpha =
  alpha a $ chId {obj} hom a

public export
FreeContravarHomYonedaL : {obj : Type} -> {hom : HomSlice obj} ->
  (a : obj) -> (f : SliceObj obj) ->
  -- f is contravariant
  (fmap : (a, b : obj) -> hom (a, b) -> f b -> f a) ->
  f a -> InternalNTFromContravarHom {obj} (FreeHomM obj hom) a f
FreeContravarHomYonedaL {obj} {hom} a f fmap fa b mba =
  chFreeFContramap fmap b a mba fa

--------------------------------------------
--------------------------------------------
---- Category-spec-style Geb definition ----
--------------------------------------------
--------------------------------------------

---------------------------
---- General utilities ----
---------------------------

public export
data EMorphEitherF :
    {obj : Type} -> {f : Type -> Type} ->
    HomSlice obj ->
    HomEndofunctor (TrEitherF f obj) where
  MEV : {x, y : obj} ->
    homv (x, y) -> EMorphEitherF {obj} {f} homv hom (TFV x, TFV y)
  MEU : {x, y : TrEitherF f obj} ->
    hom (x, y) -> EMorphEitherF {obj} {f} homv hom (x, y)

public export
data EMorphTranslateF :
    {obj : Type} -> {f : Type -> Type} ->
    HomSlice obj -> HomSlice (TrEitherF f obj) ->
    HomEndofunctor (TrEitherF f obj) where
  MTE :
    EMorphEitherF {obj} {f} homv hom (x, y) ->
    EMorphTranslateF {obj} {f} homv hom carrier (x, y)
  MTI :
    (x : TrEitherF f obj) ->
    EMorphTranslateF {obj} {f} homv hom carrier (x, x)
  MTC : {x, y, z : TrEitherF f obj} ->
    carrier (y, z) -> carrier (x, y) ->
    EMorphTranslateF {obj} {f} homv hom carrier (x, z)

public export
data EFreeMorphF :
    {obj : Type} -> {f : Type -> Type} ->
    HomSlice obj ->
    HomEndofunctor (TrEitherF f obj) where
  InM :
    {x, y : TrEitherF f obj} ->
    EMorphTranslateF {obj} {f} homv hom
      (EFreeMorphF {obj} {f} homv hom) (x, y) ->
    EFreeMorphF {obj} {f} homv hom (x, y)

public export
FMI :
  {obj : Type} -> {f : Type -> Type} ->
  {homv : HomSlice obj} ->
  {hom : HomSlice (TrEitherF f obj)} ->
  (x : TrEitherF f obj) ->
  EFreeMorphF homv hom (x, x)
FMI x = InM (MTI x)

public export
FMC :
  {obj : Type} -> {f : Type -> Type} ->
  {homv : HomSlice obj} ->
  {hom : HomSlice (TrEitherF f obj)} ->
  {x, y, z : TrEitherF f obj} ->
  EFreeMorphF homv hom (y, z) ->
  EFreeMorphF homv hom (x, y) ->
  EFreeMorphF homv hom (x, z)
FMC g f = InM (MTC g f)

public export
FME :
  {obj : Type} -> {f : Type -> Type} ->
  {homv : HomSlice obj} ->
  {hom : HomSlice (TrEitherF f obj)} ->
  {x, y : TrEitherF f obj} ->
  EMorphEitherF homv hom (x, y) ->
  EFreeMorphF homv hom (x, y)
FME m = InM (MTE m)

public export
FMV :
  {obj : Type} -> {f : Type -> Type} ->
  {homv : HomSlice obj} ->
  {hom : HomSlice (TrEitherF f obj)} ->
  {x, y : obj} ->
  homv (x, y) ->
  EFreeMorphF homv hom (TFV x, TFV y)
FMV m = FME (MEV m)

public export
FMU :
  {obj : Type} -> {f : Type -> Type} ->
  {homv : HomSlice obj} ->
  {hom : HomSlice (TrEitherF f obj)} ->
  {x, y : TrEitherF f obj} ->
  hom (x, y) ->
  EFreeMorphF homv hom (x, y)
FMU m = FME (MEU m)

public export
MorphDenoteExtendCovar :
  (obj : Type) ->
  (f : Type -> Type) ->
  (homv : HomSlice obj) ->
  (hom : HomSlice (TrEitherF f obj)) ->
  Type
MorphDenoteExtendCovar obj f homv hom =
  CovarHomCatRep obj homv ->
  (a, b : TrEitherF f obj) -> hom (a, b) ->
  ((c : TrEitherF f obj) ->
   EMorphEitherF {obj} {f} homv hom (b, c) ->
   EFreeMorphF {obj} {f} homv hom (a, c))

public export
MorphDenoteExtendContravar :
  (obj : Type) ->
  (f : Type -> Type) ->
  (homv : HomSlice obj) ->
  (hom : HomSlice (TrEitherF f obj)) ->
  Type
MorphDenoteExtendContravar obj f homv hom =
  ContravarHomCatRep obj homv ->
  (a, b : TrEitherF f obj) -> hom (a, b) ->
  ((c : TrEitherF f obj) ->
   EMorphEitherF {obj} {f} homv hom (c, a) ->
   EFreeMorphF {obj} {f} homv hom (c, b))

-----------------------------------------------
-----------------------------------------------
---- Specific free universal constructions ----
-----------------------------------------------
-----------------------------------------------

------------------------
---- Initial object ----
------------------------

-- The adjunction which can be used to define the initial object has the
-- following data:
--
--  - Left category C: category being freely generated
--  - Right category D: terminal category
--  - Left functor L: constant functor to initial object (and identity
--    morphism on initial object)
--  - Right functor R: unique functor to terminal category
--  - R . L (D -> D): identity functor (on terminal category -- this is the
--    _only_ endofunctor on the terminal category)
--  - L . R (C -> C): constant functor which takes any object to initial object,
--    and any morphism to identity on initial object
--  - Unit (id -> R . L): identity natural transformation (the only
--    natural transformation on the only endofunctor on the terminal category)
--  - Counit (L . R -> id): component at B is unique morphism from initial
--    object to B
--  - Adjuncts: (Hom(L A, B) == Hom(A, R B), for A : D and B : C):
--    for all B : C, fromVoid(Void, B) is in bijection with Hom(1 : D, 1 : D),
--    which is (isomorphic to) Unit
--  - Left triangle identity: (counit . L) . (L . unit) = id(L):
--    expanded, for all A : D, counit(L(A)) . L(unit(A)) = id(L(A))
--    (which goes from L(A) to L(A) in C via L(R(L(A)))):
--      fromVoid(Void, L(A)) . L(id(A)) = id(L(A))
--    -- this reduces to fromVoid(Void, Void) . id(Void) = id(Void),
--    and from there to fromVoid(Void, Void) = id(Void)
--  - Right triangle identity: (R . counit) . (unit . R) = id(R):
--    expanded, for all B : C, R(counit(B)) . unit(R(B)) = id(R(B))
--    (which goes from R(B) to R(B) in D via R(L(R(B)))):
--      id(1) . id(1) = id(1)
--    -- this reduces to id(1) = id(1), so it's not telling us anything new
--    (we could have concluded that from the category laws alone, or indeed by
--    reflexivity on the unique morphism in the terminal category)

-- The functor which freely generates an initial object simply
-- generates one new object.
public export
data InitialObjF : (obj : Type) -> Type where
  Obj0 : InitialObjF obj

-- The initial object's universal morphisms come from the unit in the terminal
-- category -- which is to say, there aren't any!
public export
data InitialUnitF : {obj : Type} -> (hom : HomSlice obj) ->
    SliceObj (obj, InitialObjF obj) where

-- The right adjunct, which takes an object from the base category
-- (the only morphism in the other category, which is the terminal
-- category, is the identity morphism on its only object, so it is
-- an ignored parameter) and produces a unique morphism to it from
-- the initial object.
public export
data InitialRightAdj : {0 obj, obj' : Type} -> (hom : SliceObj (obj, obj')) ->
    SliceObj (InitialObjF obj, obj') where
  InRAFrom0 : {obj, obj' : Type} -> {hom : SliceObj (obj, obj')} ->
    (a : obj') -> InitialRightAdj {obj} {obj'} hom (Obj0, a)

-- Extend a profunctor H : (Cop, C) -> Type.
public export
InitialExtendHom : {obj : Type} -> (hom : HomSlice obj) ->
  HomSlice (TrEitherF InitialObjF obj)
InitialExtendHom {obj} hom (TFV x, TFV y) =
  hom (x, y)
InitialExtendHom {obj} hom (TFV x, TFC yz) =
  InitialUnitF {obj} hom (x, yz)
InitialExtendHom {obj} hom (TFC xy, TFV z) =
  InitialRightAdj {obj} {obj'=obj} hom (xy, z)
InitialExtendHom {obj} hom (TFC xy, TFC xy') =
  InitialRightAdj {obj} {obj'=(InitialObjF obj)}
    (InitialUnitF {obj} hom) (xy, xy')

public export
initialRAAfterUnit : {obj : Type} -> {hom : HomSlice obj} ->
  (a : obj) -> (b : InitialObjF obj) -> (c : obj) ->
  (mbc : InitialRightAdj {obj} {obj'=obj} hom (b, c)) ->
  InitialUnitF {obj} hom (a, b) ->
  hom (a, c)
initialRAAfterUnit a Obj0 b (InRAFrom0 b) ma0 = case ma0 of _ impossible

public export
initialPreCompRAA : {0 obj : Type} -> (hom : HomSlice obj) ->
  (comp : {0 a, b, c : obj} -> hom (b, c) -> hom (a, b) -> hom (a, c)) ->
  (b, c : obj) ->
  hom (b, c) ->
  InitialRightAdj {obj} {obj'=obj} hom (Obj0, b) ->
  InitialRightAdj {obj} {obj'=obj} hom (Obj0, c)
initialPreCompRAA hom comp b c mbc (InRAFrom0 b) = InRAFrom0 c

public export
initialUnitExtendEq : {obj : Type} -> {hom : HomSlice obj} ->
  (eq : (0 a, b : obj) -> RelationOn (hom (a, b))) ->
  (a : obj) -> (b : InitialObjF obj) ->
  RelationOn (InitialUnitF hom (a, b))
initialUnitExtendEq eq a b mab mab' = case mab of _ impossible

public export
initialRightAdjExtendEq : {obj : Type} -> {hom : HomSlice obj} ->
  (eq : (0 a, b : obj) -> RelationOn (hom (a, b))) ->
  (a : InitialObjF obj) -> (b : obj) ->
  RelationOn (InitialRightAdj hom (a, b))
initialRightAdjExtendEq eq Obj0 b (InRAFrom0 b) (InRAFrom0 b) = Unit

public export
initialRightAdjUnitExtendEq : {obj : Type} -> {hom : HomSlice obj} ->
  (eq : (0 a, b : obj) -> RelationOn (hom (a, b))) ->
  (a, b : InitialObjF obj) ->
  RelationOn (InitialRightAdj {obj} {obj'=(InitialObjF obj)}
    (InitialUnitF hom) (a, b))
initialRightAdjUnitExtendEq eq Obj0 Obj0 (InRAFrom0 Obj0) g =
  case g of InRAFrom0 Obj0 => Unit

-- Extend equality.
public export
initialExtendEq : {obj : Type} -> {hom : HomSlice obj} ->
  (eq : (0 a, b : obj) -> RelationOn (hom (a, b))) ->
  (a, b : TrEitherF InitialObjF obj) ->
  RelationOn (InitialExtendHom hom (a, b))
initialExtendEq eq (TFV a) (TFV b) f g =
  eq a b f g
initialExtendEq eq (TFV a) (TFC b) f g =
  initialUnitExtendEq eq a b f g
initialExtendEq {hom} eq (TFC a) (TFV b) f g =
  initialRightAdjExtendEq {hom} eq a b f g
initialExtendEq eq (TFC a) (TFC b) f g =
  initialRightAdjUnitExtendEq {obj} {hom} eq a b f g

-- Extend reduction.  Returns Nothing if irreducible.
public export
initialExtendReduce : {obj : Type} -> {hom : HomSlice obj} ->
  (comp : {0 a, b, c : obj} -> hom (b, c) -> hom (a, b) -> hom (a, c)) ->
  (a, b, c : TrEitherF InitialObjF obj) ->
  InitialExtendHom hom (b, c) ->
  InitialExtendHom hom (a, b) ->
  Maybe (InitialExtendHom hom (a, c))
initialExtendReduce comp (TFV a) (TFV b) (TFV c) mbc mab =
  Just $ comp mbc mab
initialExtendReduce comp a b (TFC c) mbc mab =
  Nothing
initialExtendReduce comp (TFV a) (TFC b) (TFV c) mbc mab =
  Just $ initialRAAfterUnit {hom} a b c mbc mab
initialExtendReduce comp (TFC Obj0) (TFC Obj0) (TFV c)
  (InRAFrom0 c) (InRAFrom0 Obj0) = Just $ InRAFrom0 c
initialExtendReduce {hom} comp (TFC Obj0) (TFV b) (TFV c) mbc mab =
  Just $ initialPreCompRAA hom comp b c mbc mab

-- Extend composition.  Returns CHComp if irreducible.
public export
initialExtendCompose : {obj : Type} -> {hom : HomSlice obj} ->
  (comp : {0 a, b, c : obj} -> hom (b, c) -> hom (a, b) -> hom (a, c)) ->
  (a, b, c : TrEitherF InitialObjF obj) ->
  InitialExtendHom hom (b, c) ->
  InitialExtendHom hom (a, b) ->
  CatEitherF (InitialExtendHom hom) (a, c)
initialExtendCompose comp a b c mbc mab with
  (initialExtendReduce comp a b c mbc mab)
    initialExtendCompose comp a b c mbc mab | Just mac = InSlV mac
    initialExtendCompose comp a b c mbc mab | Nothing = CEcomp mbc mab

-- Extend object interpretation.
public export
InitialInterpObj : {obj : Type} -> SliceObj obj -> SliceObj (InitialObjF obj)
InitialInterpObj interp Obj0 = Void

public export
ExtendInitialInterpObj : {obj : Type} ->
  SliceObj obj -> SliceObj (TrEitherF InitialObjF obj)
ExtendInitialInterpObj = sliceTrMap InitialInterpObj

public export
initialInterpUnit : {obj : Type} -> (hom : HomSlice obj) ->
  (ointerp : SliceObj obj) ->
  (minterp : (a, b : obj) -> hom (a, b) -> ointerp a -> ointerp b) ->
  (a : obj) -> (b : InitialObjF obj) ->
  InitialUnitF hom (a, b) ->
  ointerp a -> InitialInterpObj {obj} ointerp b
initialInterpUnit hom ointerp minterp a Obj0 f = case f of _ impossible

public export
initialInterpRightAdj : {obj, obj' : Type} -> (hom : SliceObj (obj, obj')) ->
  (ointerp : SliceObj obj) ->
  (ointerp' : SliceObj obj') ->
  (minterp :
    (a : obj) -> (b : obj') -> hom (a, b) -> ointerp a -> ointerp' b) ->
  (a : InitialObjF obj) -> (b : obj') ->
  InitialRightAdj {obj} {obj'} hom (a, b) ->
  InitialInterpObj {obj} ointerp a ->
  ointerp' b
initialInterpRightAdj hom ointerp ointerp' minterp Obj0 b f = voidF (ointerp' b)

public export
ExtendInitialInterpMorph : {obj : Type} -> (hom : HomSlice obj) ->
  (ointerp : SliceObj obj) ->
  (minterp : (a, b : obj) -> hom (a, b) -> ointerp a -> ointerp b) ->
  (a, b : TrEitherF InitialObjF obj) ->
  InitialExtendHom {obj} hom (a, b) ->
  ExtendInitialInterpObj {obj} ointerp a ->
  ExtendInitialInterpObj {obj} ointerp b
ExtendInitialInterpMorph hom ointerp minterp (TFV a) (TFV b)
  f = minterp a b f
ExtendInitialInterpMorph hom ointerp minterp (TFV a) (TFC b) mab =
  initialInterpUnit hom ointerp minterp a b mab
ExtendInitialInterpMorph {obj} hom ointerp minterp (TFC a) (TFV b) adj =
  initialInterpRightAdj {obj} {obj'=obj}
    hom
    ointerp
    ointerp
    minterp
    a
    b
    adj
ExtendInitialInterpMorph {obj} hom ointerp minterp (TFC a) (TFC b) adj =
  initialInterpRightAdj {obj} {obj'=(InitialObjF obj)}
    (InitialUnitF hom)
    ointerp
    (InitialInterpObj ointerp)
    (initialInterpUnit hom ointerp minterp)
    a
    b
    adj

-------------------------
---- Terminal object ----
-------------------------

public export
data TerminalObjF : (obj : Type) -> Type where
  Obj1 : TerminalObjF obj

-- The terminal object's universal morphisms come from the counit in the
-- terminal category -- which is to say, there aren't any!
public export
data TerminalCounitF : {obj : Type} -> (hom : HomSlice obj) ->
    SliceObj (obj, TerminalObjF obj) where

-- The left adjunct, which takes an object from the base category
-- (the only morphism in the other category, which is the terminal
-- category, is the identity morphism on its only object, so it is
-- an ignored parameter) and produces a unique morphism from it from
-- the terminal object.
public export
data TerminalLeftAdj : {0 obj, obj' : Type} -> (hom : SliceObj (obj, obj')) ->
    SliceObj (obj, TerminalObjF obj') where
  InLATo1 : {obj, obj' : Type} -> {hom : SliceObj (obj, obj')} ->
    (a : obj) -> TerminalLeftAdj {obj} {obj'} hom (a, Obj1)

--------------------
---- Coproducts ----
--------------------

-- The adjunction which can be used to define the coproduct has the
-- following data:
--
--  - Left category C: category being freely generated
--  - Right category D: product category of category being freely generated
--  - Left functor L: functor from (A, A') to A + A'
--  - Right functor R: diagonal functor (A to (A, A))
--  - R . L (D -> D): (A, A') -> (A + A', A + A')
--  - L . R (C -> C): A -> A + A
--  - Unit (id -> R . L): (A, A') -> (A + A', A + A'): injections
--    (A -> A + A' and A' -> A + A'), which are the introduction rules
--  - Counit (L . R -> id): A + A -> A:  codiagonal
--    (`Left x` and `Right x` both go to `x`)
--  - Adjuncts: (Hom(L A, B) == Hom(A, R B), for A : D and B : C):
--    for all (A, A', B) : C, Hom(A + A', B) == Hom((A, A'), (B, B)):
--    that is, a morphism A + A' -> B is equivalent to a pair of morphisms
--    A -> B and A' -> B (the right adjunct is therefore the elimination rule,
--    AKA a case statement)
--  - Left triangle identity: (counit . L) . (L . unit) = id(L):
--    expanded, for all A : D, counit(L(A)) . L(unit(A)) = id(L(A))
--    (which goes from L(A) to L(A) in C via L(R(L(A)))):
--    this becomes:
--      forall A, A' : C,
--        ((A + A') + (A + A') -> (A + A')) . (A + A' -> (A + A') + (A + A')) ==
--        id(A + A') -- so if we start at A + A', inject to each side of the
--        coproduct with itself, and then take the codiagonal, we get the
--        same thing back that we started with
--  - Right triangle identity: (R . counit) . (unit . R) = id(R):
--    expanded, for all B : C, R(counit(B)) . unit(R(B)) = id(R(B))
--    (which goes from R(B) to R(B) in D via R(L(R(B)))):
--    this becomes:
--      forall B : C,
--        ((B + B) -> B, (B + B) -> B) . (B -> B + B, B -> B + B) == id(B, B)
--    this ends up implying two identities:
--      codiag . linj(B -> B + B) = id
--      codiag . rinj(B -> B + B) = id
--    The left triangle identity appears to me to be just a more convoluted
--    version of this, so this right identity is the "useful" one for this
--    adjunction.
--      Is it the case that we can conclude from this by using bimap in
--      the diagonal category that:
--        elim(f : A -> C, g : B -> C) . linj(A, B) = f
--        elim(f : A -> C, g : B -> C) . rinj(A, B) = g
--
--    -- Laws from _Generic Programming With Adjunctions_ (see Table 1):
--
--  - Adjuncts viewed from the left :
--      Hom (A + A', B) <-> Hom((A, A'), (B, B))
--    gives an elimination rule for coproducts
--  - Universal property:
--      for all (A, A') : D (equivalently, all A, A' : D), B : C,
--      f : C((A + A') -> B), g : D((A, A') -> (B, B)) (equivalently,
--      all g1 : A -> B, g2 : A' -> B):
--    f = radj(g) <=> ladj(f) = g
--      With signatures spelled out, that's:
--    f : (A + A') -> B = radj(g) <=>
--    ladj(f) : (A, A') -> (B, B) = g <=>
--    ((morph1(ladj(f)) : A -> B == g1) && (morph2(ladj(f)) : A' -> B == g2))
--  - reflection law / simple computation law (eta/beta reductions, or
--    (co)unit/adjunct correspondence):
--      counit = radj(id) : spelled out, for all A : C,
--        codiag(A) : A + A -> A = radj(id(A), id(A))
--      unit = ladj(id) : spelled out, for all A, A' : C,
--        inj : (A, A') -> (A + A', A + A') = ladj(id(A + A'))
--  - Computation (from left, eta reduction rule):
--      f = radj(ladj(f)) : spelled out, for all A, A', B : C,
--      f : A + A' -> B == radj(morph1(ladj(f)), morph2(ladj(f)))
--  - Computation (from right, beta reduction rule):
--      g = ladj(radj(g)) : spelled out, for all A, A', B : C,
--      (g : A -> B, g' : A' -> B) == ladj(radj(g, g')) <=>
--        (g = morph1(ladj(radj(g, g')))) && (g' = morph2(ladj(radj(g, g'))))
--  - Functor fusion law from left:
--    radj(g) . L h == radj(g . h)
--  - Fusion law from right:
--    ladj(f) . h == ladj(f . L h)
--  - Fusion law from left:
--    k . radj(g) == radj(R k . g)
--  - Functor fusion law from right:
--    R k . ladj(f) == ladj(k . f)
--  - Counit naturality:
--    k . counit == counit . (L(R(k)))
--  - Unit naturality:
--    R(L(h)) . unit == unit . h

public export
data CoprodObjF : (obj : Type) -> Type where
  ObjCp : obj -> obj -> CoprodObjF obj

-- The coproduct's universal morphisms come from the unit in the product
-- category.
public export
data CoprodUnitF : {obj : Type} -> (hom : HomSlice obj) ->
    SliceObj (obj, CoprodObjF obj) where
  CpUnInjL : (x, y : obj) ->
    CoprodUnitF {obj} hom (x, ObjCp x y)
  CpUnInjR : (x, y : obj) ->
    CoprodUnitF {obj} hom (y, ObjCp x y)

-- The right adjunct, which takes two morphisms -- i.e., a morphism in
-- the product category -- and produces one in the base category.
public export
data CoprodRightAdj : {0 obj, obj' : Type} -> (hom : SliceObj (obj, obj')) ->
    SliceObj (CoprodObjF obj, obj') where
  CpRACase : {0 obj, obj' : Type} -> {0 a, b : obj} -> {0 c : obj'} ->
    {hom : (obj, obj') -> Type} ->
    hom (a, c) -> hom (b, c) ->
    CoprodRightAdj {obj} {obj'} hom (ObjCp a b, c)

-- Extend a profunctor H : (Cop, C) -> Type.
public export
CoprodExtendHom : {obj : Type} -> (hom : HomSlice obj) ->
  HomSlice (TrEitherF CoprodObjF obj)
CoprodExtendHom {obj} hom (TFV x, TFV y) =
  hom (x, y)
CoprodExtendHom {obj} hom (TFV x, TFC yz) =
  CoprodUnitF {obj} hom (x, yz)
CoprodExtendHom {obj} hom (TFC xy, TFV z) =
  CoprodRightAdj {obj} {obj'=obj} hom (xy, z)
CoprodExtendHom {obj} hom (TFC xy, TFC xy') =
  CoprodRightAdj {obj} {obj'=(CoprodObjF obj)} (CoprodUnitF {obj} hom) (xy, xy')

public export
coprodRAAfterUnit : {obj : Type} -> {hom : HomSlice obj} ->
  (a : obj) -> (b : CoprodObjF obj) -> (c : obj) ->
  (mbc : CoprodRightAdj {obj} {obj'=obj} hom (b, c)) ->
  CoprodUnitF {obj} hom (a, b) ->
  hom (a, c)
coprodRAAfterUnit a (ObjCp a b) c (CpRACase f g) (CpUnInjL a b) = f
coprodRAAfterUnit b (ObjCp a b) c (CpRACase f g) (CpUnInjR a b) = g

public export
coprodPreCompRAA : {0 obj : Type} -> (hom : HomSlice obj) ->
  (comp : {0 a, b, c : obj} -> hom (b, c) -> hom (a, b) -> hom (a, c)) ->
  (a, a', b, c : obj) ->
  hom (b, c) ->
  CoprodRightAdj {obj} {obj'=obj} hom (ObjCp a a', b) ->
  CoprodRightAdj {obj} {obj'=obj} hom (ObjCp a a', c)
coprodPreCompRAA {obj} hom comp a a' b c mbc (CpRACase mab ma'b) =
  CpRACase {obj} {obj'=obj} {a} {b=a'} {c}
    (comp {a} {b} {c} mbc mab)
    (comp {a=a'} {b} {c} mbc ma'b)

public export
coprodPostCompUnit : {obj : Type} -> (hom : HomSlice obj) ->
  (a, a', b, b', c : obj) ->
  CoprodRightAdj hom (ObjCp b b', c) ->
  CoprodUnitF {obj} hom (a, ObjCp b b') ->
  CoprodUnitF {obj} hom (a', ObjCp b b') ->
  CoprodRightAdj {obj} {obj'=obj} hom (ObjCp a a', c)
coprodPostCompUnit {obj} hom a a' b b' c mbc mab ma'b =
  CpRACase {obj} {obj'=obj} {a} {b=a'} {c}
    (coprodRAAfterUnit a (ObjCp b b') c mbc mab)
    (coprodRAAfterUnit a' (ObjCp b b') c mbc ma'b)

public export
coprodUnitExtendEq : {obj : Type} -> {hom : HomSlice obj} ->
  (eq : (0 a, b : obj) -> RelationOn (hom (a, b))) ->
  (a : obj) -> (b : CoprodObjF obj) ->
  RelationOn (CoprodUnitF hom (a, b))
coprodUnitExtendEq eq a (ObjCp a b) (CpUnInjL a b) (CpUnInjL a b) = Unit
coprodUnitExtendEq eq a (ObjCp a a) (CpUnInjL a a) (CpUnInjR a a) = Void
coprodUnitExtendEq eq a (ObjCp a a) (CpUnInjR a a) (CpUnInjL a a) = Void
coprodUnitExtendEq eq b (ObjCp a b) (CpUnInjR a b) (CpUnInjR a b) = Unit

public export
coprodRightAdjExtendEq : {obj : Type} -> {hom : HomSlice obj} ->
  (eq : (0 a, b : obj) -> RelationOn (hom (a, b))) ->
  (a : CoprodObjF obj) -> (b : obj) ->
  RelationOn (CoprodRightAdj hom (a, b))
coprodRightAdjExtendEq eq (ObjCp a a') b (CpRACase f g) (CpRACase f' g') =
  Pair (eq a b f f') (eq a' b g g')

public export
coprodRightAdjUnitExtendEq : {obj : Type} -> {hom : HomSlice obj} ->
  (eq : (0 a, b : obj) -> RelationOn (hom (a, b))) ->
  (a, b : CoprodObjF obj) ->
  RelationOn (CoprodRightAdj {obj} {obj'=(CoprodObjF obj)}
    (CoprodUnitF hom) (a, b))
coprodRightAdjUnitExtendEq eq (ObjCp a a') b (CpRACase f g) (CpRACase f' g') =
  Pair
    (coprodUnitExtendEq {hom} eq a b f f')
    (coprodUnitExtendEq {hom} eq a' b g g')

-- Extend equality.
public export
coprodExtendEq : {obj : Type} -> {hom : HomSlice obj} ->
  (eq : (0 a, b : obj) -> RelationOn (hom (a, b))) ->
  (a, b : TrEitherF CoprodObjF obj) ->
  RelationOn (CoprodExtendHom hom (a, b))
coprodExtendEq eq (TFV a) (TFV b) f g =
  eq a b f g
coprodExtendEq eq (TFV a) (TFC b) f g =
  coprodUnitExtendEq eq a b f g
coprodExtendEq {hom} eq (TFC a) (TFV b) f g =
  coprodRightAdjExtendEq {hom} eq a b f g
coprodExtendEq eq (TFC a) (TFC b) f g =
  coprodRightAdjUnitExtendEq {obj} {hom} eq a b f g

-- Extend reduction.  Returns Nothing if irreducible.
public export
coprodExtendReduce : {obj : Type} -> {hom : HomSlice obj} ->
  (comp : {0 a, b, c : obj} -> hom (b, c) -> hom (a, b) -> hom (a, c)) ->
  (a, b, c : TrEitherF CoprodObjF obj) ->
  CoprodExtendHom hom (b, c) ->
  CoprodExtendHom hom (a, b) ->
  Maybe (CoprodExtendHom hom (a, c))
coprodExtendReduce comp (TFV a) (TFV b) (TFV c) mbc mab =
  Just $ comp mbc mab
coprodExtendReduce comp a b (TFC c) mbc mab =
  Nothing
coprodExtendReduce comp (TFV a) (TFC b) (TFV c) mbc mab =
  Just $ coprodRAAfterUnit {hom} a b c mbc mab
coprodExtendReduce comp (TFC (ObjCp a a')) (TFC (ObjCp b b')) (TFV c)
  mbb'c (CpRACase {a} {b=a'} {c=(ObjCp b b')} mabb' ma'bb') =
    Just $ coprodPostCompUnit hom a a' b b' c mbb'c mabb' ma'bb'
coprodExtendReduce {hom} comp (TFC (ObjCp a a')) (TFV b) (TFV c) mbc mab =
  Just $ coprodPreCompRAA hom comp a a' b c mbc mab

-- Extend composition.  Returns CHComp if irreducible.
public export
coprodExtendCompose : {obj : Type} -> {hom : HomSlice obj} ->
  (comp : {0 a, b, c : obj} -> hom (b, c) -> hom (a, b) -> hom (a, c)) ->
  (a, b, c : TrEitherF CoprodObjF obj) ->
  CoprodExtendHom hom (b, c) ->
  CoprodExtendHom hom (a, b) ->
  CatEitherF (CoprodExtendHom hom) (a, c)
coprodExtendCompose comp a b c mbc mab with
  (coprodExtendReduce comp a b c mbc mab)
    coprodExtendCompose comp a b c mbc mab | Just mac = InSlV mac
    coprodExtendCompose comp a b c mbc mab | Nothing = CEcomp mbc mab

-- Extend object interpretation.
public export
CoprodInterpObj : {obj : Type} -> SliceObj obj -> SliceObj (CoprodObjF obj)
CoprodInterpObj interp (ObjCp x y) = Either (interp x) (interp y)

public export
ExtendCoprodInterpObj : {obj : Type} ->
  SliceObj obj -> SliceObj (TrEitherF CoprodObjF obj)
ExtendCoprodInterpObj = sliceTrMap CoprodInterpObj

public export
coprodInterpUnit : {obj : Type} -> (hom : HomSlice obj) ->
  (ointerp : SliceObj obj) ->
  (minterp : (a, b : obj) -> hom (a, b) -> ointerp a -> ointerp b) ->
  (a : obj) -> (b : CoprodObjF obj) ->
  CoprodUnitF hom (a, b) ->
  ointerp a -> CoprodInterpObj {obj} ointerp b
coprodInterpUnit hom ointerp minterp a (ObjCp a b) (CpUnInjL a b) = Left
coprodInterpUnit hom ointerp minterp b (ObjCp a b) (CpUnInjR a b) = Right

public export
coprodInterpRightAdj : {obj, obj' : Type} -> (hom : SliceObj (obj, obj')) ->
  (ointerp : SliceObj obj) ->
  (ointerp' : SliceObj obj') ->
  (minterp :
    (a : obj) -> (b : obj') -> hom (a, b) -> ointerp a -> ointerp' b) ->
  (a : CoprodObjF obj) -> (b : obj') ->
  CoprodRightAdj {obj} {obj'} hom (a, b) ->
  CoprodInterpObj {obj} ointerp a ->
  ointerp' b
coprodInterpRightAdj hom ointerp ointerp' minterp
  (ObjCp a a') b (CpRACase f g) =
    eitherElim (minterp a b f) (minterp a' b g)

public export
ExtendCoprodInterpMorph : {obj : Type} -> (hom : HomSlice obj) ->
  (ointerp : SliceObj obj) ->
  (minterp : (a, b : obj) -> hom (a, b) -> ointerp a -> ointerp b) ->
  (a, b : TrEitherF CoprodObjF obj) ->
  CoprodExtendHom {obj} hom (a, b) ->
  ExtendCoprodInterpObj {obj} ointerp a ->
  ExtendCoprodInterpObj {obj} ointerp b
ExtendCoprodInterpMorph hom ointerp minterp (TFV a) (TFV b)
  f = minterp a b f
ExtendCoprodInterpMorph hom ointerp minterp (TFV a) (TFC b) mab =
  coprodInterpUnit hom ointerp minterp a b mab
ExtendCoprodInterpMorph {obj} hom ointerp minterp (TFC a) (TFV b) adj =
  coprodInterpRightAdj {obj} {obj'=obj}
    hom
    ointerp
    ointerp
    minterp
    a
    b
    adj
ExtendCoprodInterpMorph {obj} hom ointerp minterp (TFC a) (TFC b) adj =
  coprodInterpRightAdj {obj} {obj'=(CoprodObjF obj)}
    (CoprodUnitF hom)
    ointerp
    (CoprodInterpObj ointerp)
    (coprodInterpUnit hom ointerp minterp)
    a
    b
    adj

------------------
---- Products ----
------------------

public export
data ProdObjF : (obj : Type) -> Type where
  ObjPr : obj -> obj -> ProdObjF obj

-- The product's universal morphisms come from the counit in the product
-- category.
public export
data ProdCounitF : {obj : Type} -> (hom : HomSlice obj) ->
    SliceObj (ProdObjF obj, obj) where
  PrCoProjL : (x, y : obj) ->
    ProdCounitF {obj} hom (ObjPr x y, x)
  PrCoProjR : (x, y : obj) ->
    ProdCounitF {obj} hom (ObjPr x y, y)

-- The left adjunct, which takes two morphisms -- i.e., a morphism in
-- the product category -- and produces one in the base category.
public export
data ProdLeftAdj : {0 obj, obj' : Type} -> (hom : SliceObj (obj, obj')) ->
    SliceObj (obj, ProdObjF obj') where
  PrLABi : {0 obj, obj' : Type} -> {0 a, b : obj'} -> {0 c : obj} ->
    {hom : (obj, obj') -> Type} ->
    hom (c, a) -> hom (c, b) ->
    ProdLeftAdj {obj} {obj'} hom (c, ObjPr a b)

---------------------------------------------------
---------------------------------------------------
---- Yoneda categories with explicit coherence ----
---------------------------------------------------
---------------------------------------------------

public export
record YCat where
  constructor YC
  ycObj : Type
  ycHom : HomSlice ycObj
  0 ycDenoteCovar : CovarHomCatRep ycObj ycHom
  0 ycDenoteContravar : ContravarHomCatRep ycObj ycHom

public export
YCHomSlice : YCat -> Type
YCHomSlice yc = HomSlice (ycObj yc)

public export
YCovarNT : (yc : YCat) -> YCHomSlice yc
YCovarNT yc = CovarToCovarHomRep {obj=(ycObj yc)} (ycHom yc)

public export
YContravarNT : (yc : YCat) -> YCHomSlice yc
YContravarNT yc = ContravarToContravarHomRep {obj=(ycObj yc)} (ycHom yc)

public export
yIdCovar : (yc : YCat) -> (x : ycObj yc) -> YCovarNT yc (x, x)
yIdCovar yc = CovarToCovarIdRep {obj=(ycObj yc)} {hom=(ycHom yc)}

public export
yIdContravar : (yc : YCat) -> (x : ycObj yc) -> YContravarNT yc (x, x)
yIdContravar yc = ContravarToContravarIdRep {obj=(ycObj yc)} {hom=(ycHom yc)}

public export
yComposeCovar : {yc : YCat} -> {a, b, c: ycObj yc} ->
  YCovarNT yc (b, c) -> YCovarNT yc (a, b) -> YCovarNT yc (a, c)
yComposeCovar {yc} =
  CovarToCovarComposeRep {obj=(ycObj yc)} {hom=(ycHom yc)}

public export
yComposeContravar : {yc : YCat} -> {a, b, c: ycObj yc} ->
  YContravarNT yc (b, c) -> YContravarNT yc (a, b) -> YContravarNT yc (a, c)
yComposeContravar {yc} =
  ContravarToContravarComposeRep {obj=(ycObj yc)} {hom=(ycHom yc)}

public export
YExtendObjF : Type
YExtendObjF = YCat -> Type

-- Just an explicit name for `Coprod(ycObj, oext)`.
public export
data YExtendedObj : YCat -> YExtendObjF -> Type where
  EOV : ycObj yc -> YExtendedObj yc oext
  EOU : oext yc -> YExtendedObj yc oext

public export
YExtendMorphF : YExtendObjF -> Type
YExtendMorphF oext = (yc : YCat) -> HomSlice (YExtendedObj yc oext)

public export
YExtendMorphCovarDenote : {oext : YExtendObjF} -> YExtendMorphF oext -> Type
YExtendMorphCovarDenote {oext} mext =
  (yc : YCat) -> (x, y : YExtendedObj yc oext) -> mext yc (x, y) ->
  CovarToCovarHomSetRep (YExtendedObj yc oext) (mext yc) (x, y)

public export
YExtendMorphContravarDenote : {oext : YExtendObjF} -> YExtendMorphF oext -> Type
YExtendMorphContravarDenote {oext} mext =
  (yc : YCat) -> (x, y : YExtendedObj yc oext) -> mext yc (x, y) ->
  ContravarToContravarHomSetRep (YExtendedObj yc oext) (mext yc) (x, y)

public export
data YExtendedMorph :
    YCat -> (oext : YExtendObjF) -> YExtendMorphF oext ->
    HomSlice (YExtendedObj yc oext) where
  EMV : {0 oext : YExtendObjF} -> {0 mext : YExtendMorphF oext} ->
    {0 x, y : ycObj yc} ->
    ycHom yc (x, y) -> YExtendedMorph yc oext mext (EOV {yc} x, EOV {yc} y)
  EMU : {0 oext : YExtendObjF} -> {0 mext : YExtendMorphF oext} ->
    {0 x, y : YExtendedObj yc oext} ->
    mext yc (x, y) -> YExtendedMorph yc oext mext (x, y)

public export
YExtendCovarDenotation : {oext : YExtendObjF} -> YExtendMorphF oext -> Type
YExtendCovarDenotation {oext} mext =
  (yc : YCat) -> (x, y : YExtendedObj yc oext) ->
  YExtendedMorph yc oext mext (x, y) ->
  CovarToCovarHomSetRep
    (YExtendedObj yc oext) (YExtendedMorph yc oext mext) (x, y)

public export
YExtendContravarDenotation : {oext : YExtendObjF} -> YExtendMorphF oext -> Type
YExtendContravarDenotation {oext} mext =
  (yc : YCat) -> (x, y : YExtendedObj yc oext) ->
  YExtendedMorph yc oext mext (x, y) ->
  ContravarToContravarHomSetRep
    (YExtendedObj yc oext) (YExtendedMorph yc oext mext) (x, y)

------------------------------------------------
---- Free categories from Yoneda categories ----
------------------------------------------------

public export
YObjHomSlice : (yc : YCat) -> Type
YObjHomSlice yc = HomSlice yc.ycObj

public export
YCatFreeHomSlice : (yc : YCat) -> YObjHomSlice yc
YCatFreeHomSlice yc = FreeHomM yc.ycObj yc.ycHom

public export
ycId : (yc : YCat) -> (a : yc.ycObj) -> YCatFreeHomSlice yc (a, a)
ycId yc a = chId (yc.ycHom) a

public export
ycComp : (yc : YCat) -> {a, b, c : yc.ycObj} ->
  YCatFreeHomSlice yc (b, c) -> YCatFreeHomSlice yc (a, b) ->
  YCatFreeHomSlice yc (a, c)
ycComp yc {a} {b} {c} g f = chComp g f

public export
YCHomSliceCata : YCat -> Type
YCHomSliceCata yc = HomSliceCata yc.ycObj

public export
ycHomSliceCata : (yc : YCat) -> (sa : HomSlice yc.ycObj) ->
  SliceMorphism yc.ycHom sa -> SliceAlg CatHomF sa ->
  SliceMorphism (SliceFreeM CatHomF yc.ycHom) sa
ycHomSliceCata yc = homSliceCata {obj=yc.ycObj} yc.ycHom

-------------------------------------------
---- Free-Yoneda-category Yoneda lemma ----
-------------------------------------------

public export
ycFreeFMap : {yc : YCat} -> {f : SliceObj yc.ycObj} ->
  ((a, b : yc.ycObj) -> yc.ycHom (a, b) -> f a -> f b) ->
  ((a, b : yc.ycObj) -> YCatFreeHomSlice yc (a, b) -> f a -> f b)
ycFreeFMap {yc} {f} = chFreeFMap {obj=yc.ycObj} {hom=yc.ycHom} {f}

public export
ycFreeFContramap : {yc : YCat} -> {f : SliceObj yc.ycObj} ->
  ((a, b : yc.ycObj) -> yc.ycHom (a, b) -> f b -> f a) ->
  ((a, b : yc.ycObj) -> YCatFreeHomSlice yc (a, b) -> f b -> f a)
ycFreeFContramap {yc} {f} = chFreeFContramap {obj=yc.ycObj} {hom=yc.ycHom} {f}

public export
YCCovarHomYonedaR :
  (yc : YCat) -> (a : yc.ycObj) -> (f : SliceObj yc.ycObj) ->
  InternalNTFromCovarHom {obj=yc.ycObj} (YCatFreeHomSlice yc) a f -> f a
YCCovarHomYonedaR yc = FreeCovarHomYonedaR {obj=yc.ycObj} {hom=yc.ycHom}

public export
YCCovarHomYonedaL : (yc : YCat) -> (a : yc.ycObj) -> (f : SliceObj yc.ycObj) ->
  (fmap : (a, b : yc.ycObj) -> yc.ycHom (a, b) -> f a -> f b) ->
  f a -> InternalNTFromCovarHom {obj=yc.ycObj} (YCatFreeHomSlice yc) a f
YCCovarHomYonedaL yc = FreeCovarHomYonedaL {obj=yc.ycObj} {hom=yc.ycHom}

public export
YCContravarHomYonedaR :
  (yc : YCat) -> (a : yc.ycObj) -> (f : SliceObj yc.ycObj) ->
  InternalNTFromContravarHom {obj=yc.ycObj} (YCatFreeHomSlice yc) a f -> f a
YCContravarHomYonedaR yc = FreeContravarHomYonedaR {obj=yc.ycObj} {hom=yc.ycHom}

public export
YCContravarHomYonedaL :
  (yc : YCat) -> (a : yc.ycObj) -> (f : SliceObj yc.ycObj) ->
  -- f is contravariant
  (fmap : (a, b : yc.ycObj) -> yc.ycHom (a, b) -> f b -> f a) ->
  f a -> InternalNTFromContravarHom {obj=yc.ycObj} (YCatFreeHomSlice yc) a f
YCContravarHomYonedaL yc = FreeContravarHomYonedaL {obj=yc.ycObj} {hom=yc.ycHom}

--------------------------------------------------------
---- Free Yoneda categories are standard categories ----
--------------------------------------------------------

public export
ycEqRel : (yc : YCat) -> (0 a, b : yc.ycObj) ->
  RelationOn (YCatFreeHomSlice yc (a, b))
ycEqRel yc a b (InSlF (a, b) (InSlV v)) (InSlF (a, b) (InSlV v')) =
  ?ycEqRel_hole_vv
ycEqRel yc a b (InSlF (a, b) (InSlV v)) (InSlF (a, b) (InSlC m')) =
  ?ycEqRel_hole_vc
ycEqRel yc a b (InSlF (a, b) (InSlC m)) (InSlF (a, b) (InSlV v')) =
  ?ycEqRel_hole_cv
ycEqRel yc a b (InSlF (a, b) (InSlC m)) (InSlF (a, b) (InSlC m')) =
  ?ycEqRel_hole_cc

public export
ycEqRelRefl : (yc : YCat) -> (0 a, b : yc.ycObj) ->
  IsReflexive (ycEqRel yc a b)
ycEqRelRefl yc a b = ?ycEqRelRefl_hole

public export
ycEqRelSym : (yc : YCat) -> (0 a, b : yc.ycObj) ->
  IsSymmetric (ycEqRel yc a b)
ycEqRelSym yc a b = ?ycEqRelSym_hole

public export
ycEqRelTrans : (yc : YCat) -> (0 a, b : yc.ycObj) ->
  IsTransitive (ycEqRel yc a b)
ycEqRelTrans yc a b = ?ycEqRelTrans_hole

public export
ycEqRelEquiv : (yc : YCat) -> (0 a, b : yc.ycObj) ->
  IsEquivalence (ycEqRel yc a b)
ycEqRelEquiv yc a b =
  MkEquivalence
    ?ycEqRelRefl_equiv_hole
    ?ycEqRelSym_equiv_hole
    ?ycEqRelTrans_equiv_hole

public export
ycEq : (yc : YCat) -> (sig : SignatureT yc.ycObj) ->
  EqRel (YCatFreeHomSlice yc sig)
ycEq yc (a, b) = MkEq (ycEqRel yc a b) (ycEqRelEquiv yc a b)

public export
0 ycIdL : (yc : YCat) -> {0 a, b : yc.ycObj} ->
  (f : YCatFreeHomSlice yc (a, b)) ->
  (ycEq yc (a, b)).eqRel f (ycComp yc {a} {b} {c=b} (ycId yc b) f)
ycIdL yc {a} {b} f = ?ycIdL_hole

public export
0 ycIdR : (yc : YCat) -> {0 a, b : yc.ycObj} ->
  (f : YCatFreeHomSlice yc (a, b)) ->
  (ycEq yc (a, b)).eqRel f (ycComp yc {a} {b=a} {c=b} f (ycId yc a))
ycIdR yc {a} {b} f = ?ycIdR_hole

public export
0 ycAssoc : (yc : YCat) -> {0 a, b, c, d : yc.ycObj} ->
  (f : YCatFreeHomSlice yc (a, b)) -> (g : YCatFreeHomSlice yc (b, c)) ->
  (h : YCatFreeHomSlice yc (c, d)) ->
  (ycEq yc (a, d)).eqRel
    (ycComp yc {a} {b=c} {c=d} h (ycComp yc {a} {b} {c} g f))
    (ycComp yc {a} {b} {c=d} (ycComp yc {a=b} {b=c} {c=d} h g) f)
ycAssoc yc {a} {b} {c} {d} f g h = ?ycAssoc_hole

public export
YCatToSCat : YCat -> SCat
YCatToSCat yc =
  SC
    yc.ycObj
    (YCatFreeHomSlice yc)
    (ycId yc)
    (ycComp yc)
    (ycEq yc)
    (ycIdL yc)
    (ycIdR yc)
    (ycAssoc yc)

---------------------------------------------------
---- Standard categories are Yoneda categories ----
---------------------------------------------------

public export
SCatCovarDenotation : (sc : SCat) -> CovarHomCatRep sc.scObj sc.scHom
SCatCovarDenotation sc a b mab c mbc = sc.scComp mbc mab

public export
SCatContravarDenotation : (sc : SCat) -> ContravarHomCatRep sc.scObj sc.scHom
SCatContravarDenotation sc a b mab c mca = sc.scComp mab mca

public export
SCatToYCat : SCat -> YCat
SCatToYCat sc =
  YC
    sc.scObj
    sc.scHom
    (SCatCovarDenotation sc)
    (SCatContravarDenotation sc)

----------------------------------------------------------------------------
---- Yoneda <-> standard formulations of category theory are equivalent ----
----------------------------------------------------------------------------

-- This still needs to be proven.  It will depend upon the slice-category
-- free monad's properties, such as its being Cartesian and idempotent.
-- The claim of the equivalence is that YCatToSCat |- SCatToYCatCovar
-- and YCatToSCat |- SCatToYCatContravar are both adjunctions (so in particular
-- SCatToYCatCovar and SCatToYCatContravar are naturally isomorphic) between
-- the category of Yoneda categories and the category of standard categories,
-- and the counit (in the category of standard categories) is a natural
-- isomorphism (up to categorical equivalence).
--
-- Note that this is an enhancement of the free-forgetful adjunction between
-- the category of diagrams and the category of (standard) categories.
-- The "Yoneda category" extends the notion of a diagram with an embedding
-- of the edges into internal natural transformations of the metalanguage,
-- which amount to a way of assigning free equalities to paths in the diagram
-- without having explicitly to introduce identity or composition.

---------------------------------------
---- Coproducts as Yoneda category ----
---------------------------------------

public export
YCoprodObj : YCat -> Type
YCoprodObj yc = ?YCoprodObj_hole

public export
YCoprodHom : (yc : YCat) -> HomSlice (YCoprodObj yc)
YCoprodHom yc = ?YCoprodHom_hole

public export
YCoprodCovarDenotation : (yc : YCat) ->
  CovarHomCatRep (YCoprodObj yc) (YCoprodHom yc)
YCoprodCovarDenotation yc = ?YCoprodCovarDenotation_hole

public export
YCoprodContravarDenotation : (yc : YCat) ->
  ContravarHomCatRep (YCoprodObj yc) (YCoprodHom yc)
YCoprodContravarDenotation yc = ?YCoprodContravarDenotation_hole

public export
YCoprodCovarEqImpliesContravar : (yc : YCat) ->
  CovarEqImpliesContravar {obj=(YCoprodObj yc)} {hom=(YCoprodHom yc)}
    (YCoprodCovarDenotation yc) (YCoprodContravarDenotation yc)
YCoprodCovarEqImpliesContravar yc = ?YCoprodCovarEqImpliesContravar_hole

public export
YCoprodContravarEqImpliesCovar : (yc : YCat) ->
  ContravarEqImpliesCovar {obj=(YCoprodObj yc)} {hom=(YCoprodHom yc)}
    (YCoprodCovarDenotation yc) (YCoprodContravarDenotation yc)
YCoprodContravarEqImpliesCovar yc = ?YCoprodContravarEqImpliesCovar_hole

public export
YCoprod : YCat -> YCat
YCoprod yc =
  YC
    (YCoprodObj yc)
    (YCoprodHom yc)
    (YCoprodCovarDenotation yc)
    (YCoprodContravarDenotation yc)

---------------------
---------------------
---- Experiments ----
---------------------
---------------------

public export
data XTypeF : (a : Type) -> (term : a -> Type) -> Type where
  XT0 : XTypeF a term
  XT1 : XTypeF a term
  XTC : a -> a -> XTypeF a term
  XTP : a -> a -> XTypeF a term
  XTSig : (ty : a) -> (term ty -> a) -> XTypeF a term

public export
XTermF : {a : Type} -> (term : a -> Type) -> XTypeF a term -> Type
XTermF term XT0 = Void
XTermF term XT1 = Unit
XTermF term (XTC ty ty') = Either (term ty) (term ty')
XTermF term (XTP ty ty') = Pair (term ty) (term ty')
XTermF term (XTSig ty pred) = DPair (term ty) (term . pred)

mutual
  public export
  partial
  data XType : Type where
    InXT : XTypeF XType XTerm -> XType

  public export
  partial
  data XTerm : XType -> Type where
    InXt : XTermF {a=XType} XTerm ty -> XTerm (InXT ty)

mutual
  public export
  data XObj : Type where
    XO1 : XObj
    XOB : XObj
    XOP : XObj -> XObj -> XObj
    XOEq : {a, b : XObj} -> XMorph a b -> XMorph a b -> XObj

  public export
  data XMorph : XObj -> XObj -> Type where
    XMid : (a : XObj) -> XMorph a a
    XMcomp : {a, b, c : XObj} -> XMorph b c -> XMorph a b
    XM1 : (a : XObj) -> XMorph a XO1
    XMt : XMorph XO1 XOB
    XMf : XMorph XO1 XOB
    XMb : {a : XObj} -> XMorph XO1 a -> XMorph XO1 a -> XMorph XOB a
    XOPp : (a, b, c : XObj) -> XMorph a b -> XMorph a c -> XMorph a (XOP b c)
    XOPl : (a, b : XObj) -> XMorph (XOP a b) a
    XOPr : (a, b : XObj) -> XMorph (XOP a b) b
    XOEi1 : {a, b : XObj} -> (f, g : XMorph a b) -> XMorph (XOEq {a} {b} f g) a
    XOEi2 : {a, b : XObj} -> (f, g : XMorph a b) -> XMorph (XOEq {a} {b} f g) b
    XMchi : {a, b : XObj} -> XMorph a b -> XMorph a b -> XMorph a XOB

--------------------------------------------------------
--------------------------------------------------------
---- Index type (used for positions and directions) ----
--------------------------------------------------------
--------------------------------------------------------

public export
data IdxObj : Type where
  I0 : IdxObj
  I1 : IdxObj
  IC : IdxObj -> IdxObj -> IdxObj
  IP : IdxObj -> IdxObj -> IdxObj
  IH : IdxObj -> IdxObj -> IdxObj
  IN : (n : Nat) -> {auto 0 ok : Not (n = 0)} -> IdxObj -- arithmetic modulo n

mutual
  public export
  data IdxTerm : IdxObj -> Type where
    TU : IdxTerm I1
    TL : IdxTerm a -> (b : IdxObj) -> IdxTerm (IC a b)
    TR : (a : IdxObj) -> IdxTerm b -> IdxTerm (IC a b)
    TP : IdxTerm a -> IdxTerm b -> IdxTerm (IP a b)
    TQ : IdxMorph a b -> IdxTerm (IH a b) -- quote
    TN : (m, n : Nat) ->
      {auto 0 m_ok : Not (m = 0)} ->
      {auto 0 n_ok : LT n m} ->
      IdxTerm (IN {ok=m_ok} m)

  public export
  data IdxMorph : IdxObj -> IdxObj -> Type where
    MId : (a : IdxObj) -> IdxMorph a a
    MComp : IdxMorph b c -> IdxMorph a b -> IdxMorph a c
    M0 : (a : IdxObj) -> IdxMorph I0 a -- right adjunct (and counit in idx cat)
    M1 : (a : IdxObj) -> IdxMorph a I1 -- left adjunct (and unit in idx cat)
    MCil : (a, b : IdxObj) -> IdxMorph a (IC a b) -- from unit in product cat
    MCir : (a, b : IdxObj) -> IdxMorph b (IC a b) -- from unit in product cat
    MCe : IdxMorph a c -> IdxMorph b c -> IdxMorph (IC a b) c -- right adjunct
    MPi : IdxMorph a b -> IdxMorph a c -> IdxMorph a (IP b c) -- left adjunct
    MPel : (a, b : IdxObj) -> IdxMorph (IP a b) a -- from counit in product cat
    MPer : (a, b : IdxObj) -> IdxMorph (IP a b) b -- from counit in product cat
    MDist : (a, b, c : IdxObj) ->
      IdxMorph (IP a (IC b c)) (IC (IP a b) (IP a c))
    MU : IdxTerm (IH a b) -> IdxMorph a b -- unquote
    Mev : (a, b : IdxObj) -> IdxMorph (IP (IH a b) a) b -- counit
    Mcu : IdxMorph (IP a b) c -> IdxMorph a (IH b c) -- left adjunct

    -- Polynomial modular arithmetic
    Mninj : (m, n : Nat) ->
      {auto 0 m_ok : Not (m = 0)} -> {auto 0 n_ok : Not (n = 0)} ->
      IdxMorph (IN m) (IN n)
    Mconst : (m, n : Nat) -> {auto 0 ok : Not (m = 0)} -> IdxMorph I1 (IN m)
    Madd : {n : Nat} -> {auto 0 ok : Not (n = 0)} ->
      IdxMorph (IN n) (IN n) -> IdxMorph (IN n) (IN n) -> IdxMorph (IN n) (IN n)
    Msub : {n : Nat} -> {auto 0 ok : Not (n = 0)} ->
      IdxMorph (IN n) (IN n) -> IdxMorph (IN n) (IN n) -> IdxMorph (IN n) (IN n)
    Mmult : {n : Nat} -> {auto 0 ok : Not (n = 0)} ->
      IdxMorph (IN n) (IN n) -> IdxMorph (IN n) (IN n) -> IdxMorph (IN n) (IN n)
    Mdiv : {n : Nat} -> {auto 0 ok : Not (n = 0)} ->
      IdxMorph (IN n) (IN n) -> IdxMorph (IN n) (IN n) -> IdxMorph (IN n) (IN n)
    Mmod : {n : Nat} -> {auto 0 ok : Not (n = 0)} ->
      IdxMorph (IN n) (IN n) -> IdxMorph (IN n) (IN n) -> IdxMorph (IN n) (IN n)
    Mlt : {m, n : Nat} ->
      {auto 0 m_ok : Not (m = 0)} -> {auto 0 n_ok : Not (n = 0)} ->
      IdxMorph (IN m) (IN m) -> IdxMorph (IN m) (IN m) ->
      IdxMorph (IN m) (IC I1 I1)

---------------------------------------------------------------------
---------------------------------------------------------------------
---- Simple S-expression type that can itself be used as an atom ----
---------------------------------------------------------------------
---------------------------------------------------------------------

----------------------
---- Simple types ----
----------------------

public export
OExp : Type
OExp = SExp BCDOPos

public export
OExpBoolAlg : Type
OExpBoolAlg = SExpBoolAlg BCDOPos

public export
checkAsBCDOAlg : OExpBoolAlg
checkAsBCDOAlg _ (_ :: _) = Nothing
checkAsBCDOAlg BCDO_0 [] = Just 0
checkAsBCDOAlg BCDO_1 [] = Just 0
checkAsBCDOAlg BCDO_C [] = Just 2
checkAsBCDOAlg BCDO_P [] = Just 2

public export
checkAsBCDO : OExp -> Bool
checkAsBCDO = sexpBoolCata checkAsBCDOAlg

public export
ORExp : Type
ORExp = SExpRefined checkAsBCDOAlg

public export
OCExp : Type
OCExp = SExpConstrained checkAsBCDOAlg

------------------------------
---- Simple untyped terms ----
------------------------------

public export
TExp : Type
TExp = SExp BCDTPos

public export
TExpBoolAlg : Type
TExpBoolAlg = SExpBoolAlg BCDTPos

public export
checkAsBCDTAlg : TExpBoolAlg
checkAsBCDTAlg _ (_ :: _) = Nothing
checkAsBCDTAlg BCDT_U [] = Just 0
checkAsBCDTAlg BCDT_L [] = Just 1
checkAsBCDTAlg BCDT_R [] = Just 1
checkAsBCDTAlg BCDT_P [] = Just 2

public export
checkAsBCDT : TExp -> Bool
checkAsBCDT = sexpBoolCata checkAsBCDTAlg

public export
TRExp : Type
TRExp = SExpRefined checkAsBCDTAlg

public export
TCExp : Type
TCExp = SExpConstrained checkAsBCDTAlg

----------------------------
---- Simple typed terms ----
----------------------------

-----------------------------------------------------------
-----------------------------------------------------------
---- Type-checking of S-expression as minimal Geb term ----
-----------------------------------------------------------
-----------------------------------------------------------

-- Check whether a term represents a type comprised of finite products
-- and coproducts (which are spanned by an initial object, a terminal
-- object, binary coproducts, and binary products).
public export
checkAsFinPCAlg : GExpBoolAlg
checkAsFinPCAlg FBT_INITIAL [] = Just 0
checkAsFinPCAlg FBT_TERMINAL [] = Just 0
checkAsFinPCAlg FBT_COPRODUCT [] = Just 2
checkAsFinPCAlg FBT_PRODUCT [] = Just 2
checkAsFinPCAlg _ _ = Nothing

public export
checkAsFinPC : GExp -> Bool
checkAsFinPC = sexpBoolCata checkAsFinPCAlg

public export
FinPCGExp : Type
FinPCGExp = Refinement {a=GExp} checkAsFinPC

-- Check whether a term represents a term of a type comprised of finite products
-- and coproducts.
public export
checkAsFinTAlg : GExpBoolAlg
checkAsFinTAlg TERM_U [] = Just 0
checkAsFinTAlg TERM_L [] = Just 1
checkAsFinTAlg TERM_R [] = Just 1
checkAsFinTAlg TERM_P [] = Just 2
checkAsFinTAlg _ _ = Nothing

public export
checkAsFinT : GExp -> Bool
checkAsFinT = sexpBoolCata checkAsFinTAlg

public export
FinTGExp : Type
FinTGExp = Refinement {a=GExp} checkAsFinT

-- Check whether a term represents a term of a _given_ type.
public export
checkAsFinTypedAlg : GExpMaybeCtxAlg FinTGExp Unit
checkAsFinTypedAlg = ?checkAsFinTypedAlg_hole

--------------------------------------------
--------------------------------------------
---- Sigma types in programmer's FinSet ----
--------------------------------------------
--------------------------------------------

public export
data PFSTermF : Type -> Type where
  -- Orders
  PTO0 : PFSTermF a
  PTO1 : PFSTermF a
  PTO2 : PFSTermF a

  -- Classes
  PTCterm : PFSTermF a
  PTCtyped : PFSTermF a -- pair of type and term

  -- A typed term -- a pair of type and term
  PTT : a -> a -> PFSTermF a

  -- Non-dependent-type-forming terms
  PT0 : PFSTermF a -- Initial/Void
  PT1 : PFSTermF a -- Terminal/Unit
  PTC : a -> a -> PFSTermF a  -- Coproduct/Either
  PTP : a -> a -> PFSTermF a -- Product/Pair

  -- Term-forming terms
  PTu : PFSTermF a -- !/()
  PTl : a -> PFSTermF a -- inl/Left
  PTr : a -> PFSTermF a -- inr/Right
  PTp : a -> a -> PFSTermF a -- inp/MkPair

  -- Dependent-type-forming terms

  -- An nth-order predicate:  meaning, an order-n type which depends upon on
  -- order-n type.  This predicate is itself a term of an order-(n+1) type.
  --
  -- Another way of viewing this is as an order-(n+1) morphism
  -- from some order-n type (as injected into order n+1) to the order-(n+1)
  -- representation of the type of order-n types.  The first parameter is the
  -- order, and the second parameter is the order-n type (as injected into
  -- order (n+1)) constituting the domain.
  PTpr : a -> a -> PFSTermF a

  -- An nth-order sigma type; the parameter is an nth-order predicate.
  -- (Note that the nth-order predicate may be viewed as a term of an
  -- order-(n+1) type, or a morphism between order-(n+1) types.)
  PTsig : a -> PFSTermF a

  -- An nth-order pi type; the parameter is an nth-order predicate.
  PTpi : a -> PFSTermF a

public export
data PFSTermFM : Type -> Type where
  PTVar : a -> PFSTermFM a
  PTCom : PFSTermF (PFSTermFM a) -> PFSTermFM a

public export
PFSTAlg : Type -> Type
PFSTAlg a = PFSTermF a -> a

public export
pfstFreeCata : {0 a, b : Type} -> (a -> b) -> PFSTAlg b -> PFSTermFM a -> b
pfstFreeCata subst alg (PTVar v) = subst v
pfstFreeCata subst alg (PTCom t) = alg $ case t of
  PTO0 => PTO0
  PTO1 => PTO1
  PTO2 => PTO2
  PTCterm => PTCterm
  PTCtyped => PTCtyped
  PTT x y => PTT (pfstFreeCata subst alg x) (pfstFreeCata subst alg y)
  PT0 => PT0
  PT1 => PT1
  PTC x y => PTC (pfstFreeCata subst alg x) (pfstFreeCata subst alg y)
  PTP x y => PTP (pfstFreeCata subst alg x) (pfstFreeCata subst alg y)
  PTu => PTu
  PTl x => PTl (pfstFreeCata subst alg x)
  PTr x => PTr (pfstFreeCata subst alg x)
  PTp x y => PTp (pfstFreeCata subst alg x) (pfstFreeCata subst alg y)
  PTpr x y => PTpr (pfstFreeCata subst alg x) (pfstFreeCata subst alg y)
  PTsig x => PTsig (pfstFreeCata subst alg x)
  PTpi x => PTpi (pfstFreeCata subst alg x)

public export
PFSTShowAlg : PFSTAlg String
PFSTShowAlg PTO0 = "O(0)"
PFSTShowAlg PTO1 = "O(1)"
PFSTShowAlg PTO2 = "O(2)"
PFSTShowAlg PTCterm = "term"
PFSTShowAlg PTCtyped = "typed"
PFSTShowAlg (PTT type term) = "(" ++ term ++ ": " ++ type ++ ")"
PFSTShowAlg PT0 = "Void"
PFSTShowAlg PT1 = "Unit"
PFSTShowAlg (PTC x y) = "(" ++ x ++ " + " ++ y ++ ")"
PFSTShowAlg (PTP x y) = "(" ++ x ++ " * " ++ y ++ ")"
PFSTShowAlg PTu = "!"
PFSTShowAlg (PTl x) = "<(" ++ x ++ ")"
PFSTShowAlg (PTr x) = ">(" ++ x ++ ")"
PFSTShowAlg (PTp x y) = "(" ++ x ++ "," ++ y ++ ")"
PFSTShowAlg (PTpr x y) = "(" ++ x ++ ":" ++ y ++ ")"
PFSTShowAlg (PTsig x) = "Sig(" ++ x ++ ")"
PFSTShowAlg (PTpi x) = "Pi(" ++ x ++ ")"

public export
pfstShow : {0 a : Type} -> (a -> String) -> PFSTermFM a -> String
pfstShow sh = pfstFreeCata sh PFSTShowAlg

public export
Show a => Show (PFSTermFM a) where
  show = pfstShow show

public export
PFSTerm : Type
PFSTerm = PFSTermFM Void

public export
pfstCata : {0 a : Type} -> PFSTAlg a -> PFSTerm -> a
pfstCata {a} = pfstFreeCata {a=Void} {b=a} (voidF a)

public export
data PFSClass : Type where
  PCTerm : PFSClass
  PCType : PFSClass
  PCTyped : PFSClass

public export
data PFSDepClassType : Type where
  PDCTTyped : PFSDepClassType

public export
PFSDepClass : PFSClass -> Type
PFSDepClass PCTerm = Void
PFSDepClass PCType = PFSDepClassType
PFSDepClass PCTyped = Void

public export
PFSDepMorph : Type -> Type -> Type
PFSDepMorph a b = PFSClass -> a -> b

public export
PFSDepMorphCtx : Type -> Type -> Type -> Type
PFSDepMorphCtx ctx a b = Sigma {a=PFSClass} PFSDepClass -> a -> ctx -> b

public export
PFSSlicePred : Type -> Type
PFSSlicePred a =
  (PFSDepMorph a (Maybe (PFSTermFM a)),
   PFSDepMorphCtx (PFSTermFM a) a (Maybe (PFSTermFM a)))

mutual
  public export
  checkPFSTermSl : {0 a : Type} -> PFSSlicePred a ->
    PFSClass -> DecPred (PFSTermFM a)
  checkPFSTermSl pred c (PTVar v) = isJust $ fst pred c v
  checkPFSTermSl pred PCTyped (PTCom t) = case t of
    PTT type term => checkPFSTypedTerm pred type term
    _ => False
  checkPFSTermSl pred c t = ?checkPFSTermSl_hole

  public export
  checkPFSTypedTerm : {0 a : Type} -> PFSSlicePred a ->
    PFSTermFM a -> PFSTermFM a -> Bool
  checkPFSTypedTerm {a} pred (PTVar ty) (PTVar v) =
    isJust $ fst pred PCType ty >>= snd pred (PCType ** PDCTTyped) v
  checkPFSTypedTerm {a} pred (PTVar ty) (PTCom term) =
    let ty' = fst pred PCType ty in
    ?checkPFSTypedTerm_hole_1
  checkPFSTypedTerm {a} pred (PTCom ty) (PTVar v) = ?checkPFSTypedTerm_hole_2
  checkPFSTypedTerm {a} pred (PTCom ty) (PTCom term) = ?checkPFSTypedTerm_hole_3

public export
checkPFSTerm : {0 a : Type} -> PFSSlicePred a -> DecPred (PFSTermFM a)
checkPFSTerm pred = checkPFSTermSl pred PCTyped

-------------------
-------------------
---- Relations ----
-------------------
-------------------

public export
data CatMorphPos : Type where
  CSId : CatMorphPos
  CSComp : CatMorphPos

public export
data CatMorphDir : CatMorphPos -> Type where
  CSObj : CatMorphDir CSId
  CSLeft : CatMorphDir CSComp
  CSRight : CatMorphDir CSComp

public export
CatMorphF : PolyFunc
CatMorphF = (CatMorphPos ** CatMorphDir)

public export
data CatMorphDom : Type where
  CSDObj : CatMorphDom
  CSDMorph : CatMorphDom

public export
CatMorphAssign : Sigma CatMorphDir -> CatMorphDom
CatMorphAssign (CSId ** CSObj) = CSDObj
CatMorphAssign (CSComp ** d) = CSDMorph

public export
CatMorphSPF : SlicePolyFunc CatMorphDom Unit
CatMorphSPF = pfSlice CatMorphF CatMorphAssign

public export
data SymRelPos : Type where
  SRPSym : SymRelPos

public export
data SymRelDir : SymRelPos -> Type where
  SRDSym : SymRelDir SRPSym

public export
SymRelAssign : Sigma SymRelDir -> CatMorphDom
SymRelAssign (SRPSym ** SRDSym) = CSDMorph

public export
SymRelSPF : SlicePolyFunc CatMorphDom Unit
SymRelSPF =
  (const SymRelPos **
   SymRelDir . snd **
   \((() ** i) ** d) => SymRelAssign (i ** d))

public export
EqRelSPF : SlicePolyFunc CatMorphDom Unit
EqRelSPF = SPFSliceCoproduct CatMorphSPF SymRelSPF

public export
EqRelPos : Type
EqRelPos = spfPos EqRelSPF ()

public export
EqRelDir : EqRelPos -> Type
EqRelDir i = spfDir EqRelSPF (() ** i)

public export
data DeqRelPosExt : Type where
  DRPDec : DeqRelPosExt

public export
data DeqRelDirExt : DeqRelPosExt -> Type where
  DRDLeft : DeqRelDirExt DRPDec
  DRDRight : DeqRelDirExt DRPDec

public export
DeqRelAssignExt : Sigma DeqRelDirExt -> CatMorphDom
DeqRelAssignExt (DRPDec ** d) = CSDObj

public export
DeqRelExtF : SlicePolyFunc CatMorphDom Unit
DeqRelExtF =
  (const DeqRelPosExt **
   DeqRelDirExt . snd **
   \((() ** i) ** d) => DeqRelAssignExt (i ** d))

------------------------------------------------------
------------------------------------------------------
---- Dependent polynomial endofunctors as W-types ----
------------------------------------------------------
------------------------------------------------------

--------------------------------------------------
---- Definition and interpretation of W-types ----
--------------------------------------------------

public export
record WTypeFunc (parambase, posbase : Type) where
  constructor MkWTF
  wtPos : Type
  wtDir : Type
  wtAssign : wtDir -> parambase
  wtDirSlice : wtDir -> wtPos
  wtPosSlice : wtPos -> posbase

public export
WTypeEndoFunc : Type -> Type
WTypeEndoFunc base = WTypeFunc base base

public export
InterpWTF : {parambase, posbase : Type} ->
  WTypeFunc parambase posbase -> SliceFunctor parambase posbase
InterpWTF {parambase} {posbase} wtf sl ib =
  (i : PreImage {a=(wtPos wtf)} {b=posbase} (wtPosSlice wtf) ib **
   (d : PreImage {a=(wtDir wtf)} {b=(wtPos wtf)} (wtDirSlice wtf) (fst0 i)) ->
   sl $ wtAssign wtf $ fst0 d)

public export
WTFtoSPF : {parambase, posbase : Type} ->
  WTypeFunc parambase posbase -> SlicePolyFunc parambase posbase
WTFtoSPF {parambase} {posbase} (MkWTF pos dir assign dsl psl) =
  (\i => PreImage {a=pos} {b=posbase} psl i **
   \x => PreImage {a=dir} {b=pos} dsl $ fst0 $ snd x **
   \d => assign $ fst0 $ snd d)

public export
SPFtoWTF : {parambase, posbase : Type} ->
  SlicePolyFunc parambase posbase -> WTypeFunc parambase posbase
SPFtoWTF (posdep ** dirdep ** assign) =
  MkWTF
    (Sigma {a=posbase} posdep)
    (Sigma {a=(Sigma {a=posbase} posdep)} dirdep)
    assign
    fst
    fst

public export
InterpWTFtoSPF : {parambase, posbase : Type} ->
  (wtf : WTypeFunc parambase posbase) ->
  (sl : SliceObj parambase) -> (ib : posbase) ->
  InterpSPFunc {a=parambase} {b=posbase}
    (WTFtoSPF {parambase} {posbase} wtf) sl ib ->
  InterpWTF {parambase} {posbase} wtf sl ib
InterpWTFtoSPF (MkWTF pos dir assign dsl psl) sl ib = id

public export
InterpWTFtoSPFInv : {parambase, posbase : Type} ->
  (wtf : WTypeFunc parambase posbase) ->
  (sl : SliceObj parambase) -> (ib : posbase) ->
  InterpWTF {parambase} {posbase} wtf sl ib ->
  InterpSPFunc {a=parambase} {b=posbase}
    (WTFtoSPF {parambase} {posbase} wtf) sl ib
InterpWTFtoSPFInv (MkWTF pos dir assign dsl psl) sl ib = id

public export
InterpSPFtoWTF : {parambase, posbase : Type} ->
  (spf : SlicePolyFunc parambase posbase) ->
  (sl : SliceObj parambase) -> (ib : posbase) ->
  InterpWTF {parambase} {posbase} (SPFtoWTF {parambase} {posbase} spf) sl ib ->
  InterpSPFunc {a=parambase} {b=posbase} spf sl ib
InterpSPFtoWTF {parambase} {posbase} (posdep ** dirdep ** assign) sl ib
  (Element0 {type=(Sigma {a=posbase} posdep)} (ib' ** i) eq ** p) =
    (rewrite sym eq in i **
     \d => p $
      Element0 ((ib ** rewrite sym eq in i) ** d) (rewrite sym eq in Refl))

public export
InterpSPFtoWTFInv : {parambase, posbase : Type} ->
  (spf : SlicePolyFunc parambase posbase) ->
  (sl : SliceObj parambase) -> (ib : posbase) ->
  InterpSPFunc {a=parambase} {b=posbase} spf sl ib ->
  InterpWTF {parambase} {posbase} (SPFtoWTF {parambase} {posbase} spf) sl ib
InterpSPFtoWTFInv {parambase} {posbase} (posdep ** dirdep ** assign) sl ib
  (i ** d) =
    (Element0 (ib ** i) Refl **
     \(Element0 (i' ** di) deq) => rewrite deq in d $ rewrite sym deq in di)

-----------------------------
---- Algebras of W-types ----
-----------------------------

public export
WTFAlg : {a : Type} -> WTypeEndoFunc a -> SliceObj a -> Type
WTFAlg {a} wtf sa = SliceMorphism {a} (InterpWTF wtf sa) sa

-------------------------------------
---- Initial algebras of W-types ----
-------------------------------------

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

------------------------------------------------------------------
------------------------------------------------------------------
---- "Interpretation" of morphisms as natural transformations ----
------------------------------------------------------------------
------------------------------------------------------------------

public export
record DiagSig (obj, morph : Type) where
  constructor DSig
  dsigDom : morph -> obj
  dsigCod : morph -> obj

-- Data which determine a polynomial functor which takes (dependent) diagrams
-- to (dependent) objects.
public export
record DPDiagramObjF (0 paramdom, paramcod : Type) where
  constructor DPDF
  dpdfObjPos : paramcod -> Type
  dpdfObjDirObj : Sigma {a=paramcod} dpdfObjPos -> Type
  dpdfObjDirMorph : Sigma {a=paramcod} dpdfObjPos -> Type
  0 dpdfObjConstraint :
    (dp : paramdom) -> (dc : paramcod) -> (i : dpdfObjPos dc) ->
    (obj : Type) ->
    (dpdfObjDirObj (dc ** i) -> obj) ->
    (dom : dpdfObjDirMorph (dc ** i) -> obj) ->
    (cod : dpdfObjDirMorph (dc ** i) -> obj) ->
    Type

-- Interpret the data of a `DPDiagramObjF` to produce a dependent polynomial
-- functor which, given types of (dependent) objects and (dependent) morphisms,
-- returns a type of (dependent) objects.
public export
record InterpDPDF {0 paramdom, paramcod : Type}
    (0 dpdf : DPDiagramObjF paramdom paramcod)
    (0 obj : paramdom -> Type) (0 morph : paramdom -> Type)
    (0 dom : (dp : paramdom) -> morph dp -> obj dp)
    (0 cod : (dp : paramdom) -> morph dp -> obj dp)
    (0 dc : paramcod) where
  constructor IDPDF
  idpdfParam : paramdom
  idpdfPos : dpdf.dpdfObjPos dc
  idpdfObj : dpdf.dpdfObjDirObj (dc ** idpdfPos) -> obj idpdfParam
  idpdfMorph : dpdf.dpdfObjDirMorph (dc ** idpdfPos) -> morph idpdfParam
  0 idpdfObjConstraint :
    dpdf.dpdfObjConstraint
      idpdfParam
      dc
      idpdfPos
      (obj idpdfParam)
      idpdfObj
      (dom idpdfParam . idpdfMorph)
      (cod idpdfParam . idpdfMorph)

-----------------------------------------------------------------
-----------------------------------------------------------------
---- Dependent polynomial functors generating compound types ----
-----------------------------------------------------------------
-----------------------------------------------------------------

---------------
---- Maybe ----
---------------

public export
MaybeSPF : Type -> Type
MaybeSPF = Maybe

--------------
---- Pair ----
--------------

public export
PairSPF : (Type, Type) -> Type
PairSPF = uncurry Pair

--------------
---- Diag ----
--------------

public export
DiagF : Type -> Type
DiagF a = PairSPF (a, a)

----------------
---- Either ----
----------------

public export
EitherSPF: (Type, Type) -> Type
EitherSPF = uncurry Either

---------------
---- Split ----
---------------

public export
SplitF : Type -> Type
SplitF a = EitherSPF (a, a)

--------------
---- List ----
--------------

public export
ListSPF : (Type, Type) -> Type
ListSPF = MaybeSPF . PairSPF

-------------
---- Nat ----
-------------

public export
NatSPF : Type -> Type
NatSPF = MaybeSPF

---------------
---- Const ----
---------------

public export
ConstSPF : Type -> Type -> Type
ConstSPF = const

--------------------------------
---- Fin as refinement type ----
--------------------------------

public export
FinR : Nat -> Type
FinR n = Subset0 Nat (flip LT n)

---------------------------------
---- Fin as constant functor ----
---------------------------------

public export
FinRF : Nat -> Type -> Type
FinRF = ConstSPF . FinR

-------------------------------------
---- GebAtom as constant functor ----
-------------------------------------

public export
GebAtomF : Type -> Type
GebAtomF = const GebAtom

----------------------------------------
----------------------------------------
---- Finite product/coproduct types ----
----------------------------------------
----------------------------------------

-- The following functors operate on the product category `Type x Type x Type`;
-- they assume that the first type in the product is a type of types, the
-- second type is a type of pairs of types, and the third type is a type of
-- lists of types.

-- A type is either an atom (reserved opcode), `FinR`, or a product or a
-- coproduct of either a pair or a list of types.
-- (The coproduct of an empty list of types is an initial
-- object; the product of an empty list of types is a
-- terminal object.)
public export
FinBCTF : (Type, Type, Type) -> Type
FinBCTF (a, b, c) = MaybeSPF (EitherSPF (Nat, SplitF (EitherSPF (b, c))))

-- The first type in the product is the type of types,  so `DiagF` of that
-- first type is the type of pairs of types.
public export
FinBCTPF : (Type, Type, Type) -> Type
FinBCTPF (a, b, c) = DiagF a

-- The type of lists of types is the type of either nothing or pairs of
-- types and lists of types.
public export
FinBCTLF : (Type, Type, Type) -> Type
FinBCTLF (a, b, c) = ListSPF (a, c)

-- Here we put together the three `Type x Type x Type -> Type` functors into
-- a single `Type x Type x Type -> Type x Type x Type` endofunctor.

public export
FinBCSlF : (Type, Type, Type) -> (Type, Type, Type)
FinBCSlF (a, b, c) = (FinBCTF (a, b, c), FinBCTPF (a, b, c), FinBCTLF (a, b, c))

public export
FinBCSPF : (FS3CP -> Type) -> FS3CP -> Type
FinBCSPF f (Left ()) = FinBCTF (f FS3CP0, f FS3CP1, f FS3CP2)
FinBCSPF f (Right (Left ())) = FinBCTPF (f FS3CP0, f FS3CP1, f FS3CP2)
FinBCSPF f (Right (Right ())) = FinBCTLF (f FS3CP0, f FS3CP1, f FS3CP2)

public export
data FinBCSl : FS3CP -> Type where
  -- This is the equivalent of the following:
  --    InFBC : (sl : FS3CP) -> FinBCSPF FinBCSl sl -> FinBCSl sl
  -- But Idris doesn't realize that that's total.
  --    InFBC : (sl : FS3CP) -> FinBCSPF FinBCSl sl -> FinBCSl sl
  InFBT :
    FinBCTF (FinBCSl FS3CP0, FinBCSl FS3CP1, FinBCSl FS3CP2) -> FinBCSl FS3CP0
  InFBTP :
    FinBCTPF (FinBCSl FS3CP0, FinBCSl FS3CP1, FinBCSl FS3CP2) -> FinBCSl FS3CP1
  InFBTL :
    FinBCTLF (FinBCSl FS3CP0, FinBCSl FS3CP1, FinBCSl FS3CP2) -> FinBCSl FS3CP2

-- Finite product/coproduct types.
public export
FinBCT : Type
FinBCT = FinBCSl FS3CP0

-- Pairs of product/coproduct types.
public export
FinBCTP : Type
FinBCTP = FinBCSl FS3CP1

-- Lists of product/coproduct types.
public export
FinBCTL : Type
FinBCTL = FinBCSl FS3CP2

-- Make a term of type "pair of types" from a metalanguage pair of types.
public export
FTp : FinBCT -> FinBCT -> FinBCTP
FTp = InFBTP .* MkPair

-- Make an atom type.
public export
FTA : FinBCT
FTA = InFBT Nothing

-- Make a `FinR` type.
public export
FTN : Nat -> FinBCT
FTN = InFBT . Just . Left

-- Form a coproduct type from a pair of types.
public export
FTCP : FinBCTP -> FinBCT
FTCP = InFBT . Just . Right . Left . Left

-- Form a coproduct type from a list of types.
public export
FTCL : FinBCTL -> FinBCT
FTCL = InFBT . Just . Right . Left . Right

-- Form a product type from a pair of types.
public export
FTPP : FinBCTP -> FinBCT
FTPP = InFBT . Just . Right . Right . Left

-- Form a product type from a list of types.
public export
FTPL : FinBCTL -> FinBCT
FTPL = InFBT . Just . Right . Right . Right

-- An empty list of types.
public export
FTn : FinBCTL
FTn = InFBTL Nothing

-- Cons a type and a list of types to form another list of types.
public export
FTc : FinBCT -> FinBCTL -> FinBCTL
FTc = InFBTL . Just .* MkPair

-- Cons a type and a list of types, then take the product of the
-- resulting list of types.
public export
FTcp : FinBCT -> FinBCTL -> FinBCT
FTcp = FTPL .* FTc

-- Cons a type and a list of types, then take the coproduct of the
-- resulting list of types.
public export
FTcc : FinBCT -> FinBCTL -> FinBCT
FTcc = FTCL .* FTc

-- Make a term of type "list of types" from a metalanguage list of types.
public export
FTl : List FinBCT -> FinBCTL
FTl = foldr FTc FTn

------------------------------------------
------------------------------------------
---- S-expressions representing types ----
------------------------------------------
------------------------------------------

public export
FTypeAlg : (FS3CP -> Type) -> Type
FTypeAlg sa = SliceMorphism {a=FS3CP} (FinBCSPF sa) sa

public export
ftypeCata : FTypeAlg sa -> SliceMorphism FinBCSl sa
ftypeCata alg (Left ()) (InFBT Nothing) = alg FS3CP0 Nothing
ftypeCata alg (Left ()) (InFBT (Just (Left k))) = alg FS3CP0 $ Just $ Left k
ftypeCata alg (Left ()) (InFBT (Just (Right (Left (Left typ))))) =
  alg FS3CP0 $ Just $ Right $ Left $ Left $ ftypeCata alg FS3CP1 typ
ftypeCata alg (Left ()) (InFBT (Just (Right (Left (Right tyl))))) =
  alg FS3CP0 $ Just $ Right $ Left $ Right $ ftypeCata alg FS3CP2 tyl
ftypeCata alg (Left ()) (InFBT (Just (Right (Right (Left typ))))) =
  alg FS3CP0 $ Just $ Right $ Right $ Left $ ftypeCata alg FS3CP1 typ
ftypeCata alg (Left ()) (InFBT (Just (Right (Right (Right tyl))))) =
  alg FS3CP0 $ Just $ Right $ Right $ Right $ ftypeCata alg FS3CP2 tyl
ftypeCata alg (Right (Left ())) (InFBTP (ty, ty')) =
  alg FS3CP1 (ftypeCata alg FS3CP0 ty, ftypeCata alg FS3CP0 ty')
ftypeCata alg (Right (Right ())) (InFBTL Nothing) =
  alg FS3CP2 Nothing
ftypeCata alg (Right (Right ())) (InFBTL (Just (ty, tys))) =
  alg FS3CP2 $ Just (ftypeCata alg FS3CP0 ty, ftypeCata alg FS3CP2 tys)

public export
FTypeToGExpSl : FS3CP -> Type
FTypeToGExpSl (Left ()) = GExp
FTypeToGExpSl (Right (Left ())) = (GExp, GExp)
FTypeToGExpSl (Right (Right ())) = List GExp

public export
FTypeToGExpAlg : FTypeAlg FTypeToGExpSl
FTypeToGExpAlg (Left ()) Nothing = InSA FBT_ATOM
FTypeToGExpAlg (Left ()) (Just (Left k)) = InS FBT_BNAT [k] []
FTypeToGExpAlg (Left ()) (Just (Right (Left (Left (MkPair x y))))) = InS FBT_COPRODUCT [] [x, y]
FTypeToGExpAlg (Left ()) (Just (Right (Left (Right l)))) = InS FBT_COPRODUCT_L [] l
FTypeToGExpAlg (Left ()) (Just (Right (Right (Left (MkPair x y))))) = InS FBT_PRODUCT [] [x, y]
FTypeToGExpAlg (Left ()) (Just (Right (Right (Right l)))) = InS FBT_PRODUCT_L [] l
FTypeToGExpAlg (Right (Left ())) (x, y) = (x, y)
FTypeToGExpAlg (Right (Right ())) Nothing = []
FTypeToGExpAlg (Right (Right ())) (Just (x, xs)) = x :: xs

public export
ftypeToGExp : SliceMorphism {a=FS3CP} FinBCSl FTypeToGExpSl
ftypeToGExp = ftypeCata FTypeToGExpAlg

public export
BNatFromSExpAlg : GebAtom -> Pi {a=Nat} (GExpMaybeAlg . FinR)
BNatFromSExpAlg ea n (SXF a ns xs) = case decEq ea a of
  Yes Refl => case (ns, xs) of
    ([n'], []) => case isLT n' n of
      Yes nlt => Just $ Element0 n' nlt
      No _ => Nothing
    _ => Nothing
  No _ => Nothing

public export
bnatFromSExp : SliceMorphism {a=Nat} (const GExp) (Maybe . FinR)
bnatFromSExp n = sexpMaybeCata $ BNatFromSExpAlg FBT_BNAT n

public export
fs3FromFinR3 : FinR 3 -> FS3CP
fs3FromFinR3 (Element0 0 lt3) = FS3CP0
fs3FromFinR3 (Element0 1 lt3) = FS3CP1
fs3FromFinR3 (Element0 2 lt3) = FS3CP2
fs3FromFinR3 (Element0 (S (S (S k))) lt3) = void $ case lt3 of
  LTEZero impossible
  LTESucc lt2 => case lt2 of
    LTEZero impossible
    LTESucc lt1 => case lt1 of
      LTEZero impossible
      LTESucc lt0 => case lt0 of
        LTEZero impossible
        LTESucc _ impossible

public export
ftSliceFromGExp : GExp -> Maybe FS3CP
ftSliceFromGExp = map fs3FromFinR3 . bnatFromSExp 3

-------------------------------------------------
-------------------------------------------------
---- Terms of finite product/coproduct types ----
-------------------------------------------------
-------------------------------------------------

public export
ProdTermF : (a -> Type, b -> Type) -> PairSPF (a, b) -> Type
ProdTermF f x = ((fst f) (fst x), (snd f) (snd x))

public export
CoprodTermF : (a -> Type, b -> Type) -> EitherSPF (a, b) -> Type
CoprodTermF f x = case x of Left ea => fst f ea ; Right eb => snd f eb

public export
ListTermF : (a -> Type, b -> Type) -> ListSPF (a, b) -> Type
ListTermF f x = case x of Nothing => Unit ; Just p => ProdTermF f p -- nil/cons

public export
data FTSlice : Type where
  -- A term of the given type
  FTTerm : FinBCT -> FTSlice
  -- A pair of terms, one of each of the two given types
  FTProdP : FinBCTP -> FTSlice
  -- A term from one or the other of the two given types
  FTCopP : FinBCTP -> FTSlice
  -- A list of terms, one of each of the given types
  FTProdL : FinBCTL -> FTSlice
  -- A term from one of the given types
  FTCopL : FinBCTL -> FTSlice

-- The slice representing terms of an atom type
public export
FTSlA : FTSlice
FTSlA = FTTerm FTA

-- The slice representing terms of a bounded-natural-number type
public export
FTSlN : Nat -> FTSlice
FTSlN = FTTerm . FTN

-- The slice representing terms of a coproduct of a pair of types
public export
FTSlCP : FinBCTP -> FTSlice
FTSlCP = FTTerm . FTCP

-- The slice representing terms of a coproduct of a list of types
public export
FTSlCL : FinBCTL -> FTSlice
FTSlCL = FTTerm . FTCL

-- The slice representing terms of a product of a pair of types
public export
FTSlPP : FinBCTP -> FTSlice
FTSlPP = FTTerm . FTPP

-- The slice representing terms of a product of a list of types
public export
FTSlPL : FinBCTL -> FTSlice
FTSlPL = FTTerm . FTPL

-- The slice representing terms of either of a pair of types
public export
FTSlCopP : FinBCT -> FinBCT -> FTSlice
FTSlCopP = FTCopP .* FTp

-- The slice representing terms of either a type or a list of types
public export
FTSlCopL : FinBCT -> FinBCTL -> FTSlice
FTSlCopL = FTCopL .* FTc

-- The slice representing terms of unit type
public export
FTSlUnit : FTSlice
FTSlUnit = FTProdL FTn

-- The slice representing terms of each of a pair of types
public export
FTSlProdP : FinBCT -> FinBCT -> FTSlice
FTSlProdP = FTProdP .* FTp

-- The slice representing terms of a type together with terms of
-- each of a list of types
public export
FTSlProdL : FinBCT -> FinBCTL -> FTSlice
FTSlProdL = FTProdL .* FTc

public export
data FinTermSl : FTSlice -> Type where
  -- A term of an atom type is an atom
  InFTA : GebAtom -> FinTermSl FTSlA
  -- A term of a bounded-natural-number type is a number which obeys the bounds.
  InFTN : {0 n : Nat} -> FinR n -> FinTermSl $ FTSlN n
  -- A term of a coproduct type is a term from one of the component types.
  InFTCP : {0 typ : FinBCTP} ->
    FinTermSl (FTCopP typ) -> FinTermSl $ FTSlCP typ
  InFTCL : {0 tys : FinBCTL} ->
    FinTermSl (FTCopL tys) -> FinTermSl $ FTSlCL tys
  -- A term of a product type is a term from each of the component types.
  InFTPP : {0 tys : FinBCTP} ->
    FinTermSl (FTProdP tys) -> FinTermSl $ FTSlPP tys
  InFTPL : {0 tys : FinBCTL} ->
    FinTermSl (FTProdL tys) -> FinTermSl $ FTSlPL tys
  -- There are no terms whose type is the coproduct of an empty list
  -- (that type is `Void`, the initial object).  A term of a coproduct
  -- of a non-empty list is either a term of the head type or a term
  -- from one of the tail types.
  InFTL : {0 tyl, tyr : FinBCT} ->
    FinTermSl (FTTerm tyl) -> FinTermSl $ FTSlCopP tyl tyr
  InFTR : {0 tyl, tyr : FinBCT} ->
    FinTermSl (FTTerm tyr) -> FinTermSl $ FTSlCopP tyl tyr
  InFTH : {0 ty : FinBCT} -> {0 tys : FinBCTL} ->
    FinTermSl (FTTerm ty) -> FinTermSl $ FTSlCopL ty tys
  InFTTL : {0 ty : FinBCT} -> {0 tys : FinBCTL} ->
    FinTermSl (FTCopL tys) -> FinTermSl $ FTSlCopL ty tys
  -- A term of the product of an empty list is unit.
  InFTU : FinTermSl $ FTSlUnit
  -- A term of a type of pairs of types is a term of the first type
  -- together with a term of the second type.
  InFPair : {0 tyl, tyr : FinBCT} ->
    FinTermSl (FTTerm tyl) -> FinTermSl (FTTerm tyr) ->
    FinTermSl $ FTSlProdP tyl tyr
  -- A term of the product of a non-empty list is a term of the head type
  -- together with a list of terms from each of the tail types.
  InFList : {0 ty : FinBCT} -> {0 tys : FinBCTL} ->
    FinTermSl (FTTerm ty) -> FinTermSl (FTProdL tys) ->
    FinTermSl $ FTSlProdL ty tys

public export
FinTermA : Type
FinTermA = FinTermSl FTSlA

public export
FinTermN : Nat -> Type
FinTermN = FinTermSl . FTSlN

public export
TA : GebAtom -> FinTermA
TA = InFTA

--------------------------------------------
--------------------------------------------
---- Vectors of bounded natural numbers ----
--------------------------------------------
--------------------------------------------

public export
FinV : {0 len : Nat} -> SliceObj (Vect len Nat)
FinV [] = ()
FinV [n] = BoundedNat n
FinV (n :: ns@(_ :: _)) = (BoundedNat n, FinV ns)

public export
finVToNatL : {0 len : Nat} -> {v : Vect len Nat} -> FinV v -> List Nat
finVToNatL {len=0} {v=[]} () = []
finVToNatL {len=1} {v=([n])} (Element0 m sat) = [m]
finVToNatL {len=(S (S len))} {v=(n :: ns@(_ :: _))} (Element0 m sat, ms) =
  m :: finVToNatL {len=(S len)} {v=ns} ms

public export
showFinV : {0 len : Nat} -> {v : Vect len Nat} -> FinV v -> String
showFinV = show . finVToNatL

public export
(v : Vect len Nat) => Show (FinV v) where
  show = showFinV

public export
finVEq : {0 len : Nat} -> {v : Vect len Nat} -> (l, l' : FinV v) -> Dec (l = l')
finVEq {len=0} {v=[]} () () = Yes Refl
finVEq {len=1} {v=([n])} (Element0 m sat) (Element0 m' sat') =
  case decEq m m' of
    Yes Refl => rewrite uip {eq=sat} {eq'=sat'} in Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl
finVEq {len=(S (S len))} {v=(n :: n' :: ns')}
  (Element0 m sat, ms) (Element0 m' sat', ms') =
    case decEq m m' of
      Yes Refl => case finVEq {len=(S len)} {v=(n' :: ns')} ms ms' of
        Yes Refl => rewrite uip {eq=sat} {eq'=sat'} in Yes Refl
        No neq => No $ \eq => case eq of Refl => neq Refl
      No neq => No $ \eq => case eq of Refl => neq Refl

public export
(v : Vect len Nat) => DecEq (FinV v) where
  decEq = finVEq

public export
record Constructor (0 nty : Nat) where
  constructor Ctor
  numConst : Nat
  cconst : Vect numConst Nat
  numDir : Nat
  cdir : Vect numDir (Fin nty)

public export
showConstr : {0 nty : Nat} -> Constructor nty -> String
showConstr {nty} (Ctor nc cc nd cd) =
  "(" ++ show (map finToNat cd) ++ "," ++ show cc ++ ")"

public export
Show (Constructor nty) where
  show = showConstr

public export
constrEq : {0 nty : Nat} -> (c, c' : Constructor nty) -> Dec (c = c')
constrEq {nty} (Ctor nc cc nd cd) (Ctor nc' cc' nd' cd') =
  case decEq nc nc' of
    Yes Refl => case decEq cc cc' of
      Yes Refl => case decEq nd nd' of
        Yes Refl => case decEq cd cd' of
          Yes Refl => Yes Refl
          No neq => No $ \eq => case eq of Refl => neq Refl
        No neq => No $ \eq => case eq of Refl => neq Refl
      No neq => No $ \eq => case eq of Refl => neq Refl
    No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq (Constructor nty) where
  decEq = constrEq

public export
record RecType (0 nty : Nat) where
  constructor RType
  numCtor : Nat
  ctor : Vect numCtor (Constructor nty)

public export
showRecType : {0 nty : Nat} -> RecType nty -> String
showRecType {nty} (RType nc cs) = show cs

public export
Show (RecType nty) where
  show = showRecType

public export
recTypeEq : {0 nty : Nat} -> (ty, ty' : RecType nty) -> Dec (ty = ty')
recTypeEq {nty} (RType nc cs) (RType nc' cs') =
  case decEq nc nc' of
    Yes Refl => case decEq cs cs' of
      Yes Refl => Yes Refl
      No neq => No $ \eq => case eq of Refl => neq Refl
    No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq (RecType nty) where
  decEq = recTypeEq

public export
record TypeFamily (0 nty : Nat) where
  constructor TFamily
  rtype : Vect nty (RecType nty)

public export
showTypeFam : {0 nty : Nat} -> TypeFamily nty -> String
showTypeFam {nty} (TFamily rtype) = show rtype

public export
Show (TypeFamily nty) where
  show = showTypeFam

public export
typeFamEq : {0 nty : Nat} -> (tf, tf' : TypeFamily nty) -> Dec (tf = tf')
typeFamEq {nty} (TFamily rt) (TFamily rt') =
  case decEq rt rt' of
    Yes Refl => Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq (TypeFamily nty) where
  decEq = typeFamEq

public export
tfRtype : {0 nty : Nat} -> TypeFamily nty -> Fin nty -> RecType nty
tfRtype tf i = index i tf.rtype

public export
tfnumCtor : {0 nty : Nat} -> TypeFamily nty -> Fin nty -> Nat
tfnumCtor tf i = (tfRtype tf i).numCtor

public export
tfCtorV : {0 nty : Nat} -> (tf : TypeFamily nty) -> (i : Fin nty) ->
  Vect (tfnumCtor tf i) (Constructor nty)
tfCtorV tf i = (tfRtype tf i).ctor

public export
tfCtor : {0 nty : Nat} -> (tf : TypeFamily nty) -> (i : Fin nty) ->
  Fin (tfnumCtor tf i) -> Constructor nty
tfCtor tf i j = index j (tfCtorV tf i)

public export
tfnumDir : {0 nty : Nat} -> (tf : TypeFamily nty) -> (i : Fin nty) ->
  Fin (tfnumCtor tf i) -> Nat
tfnumDir tf i j = (tfCtor tf i j).numDir

public export
tfDirV : {0 nty : Nat} -> (tf : TypeFamily nty) -> (i : Fin nty) ->
  (j : Fin (tfnumCtor tf i)) -> Vect (tfnumDir tf i j) (Fin nty)
tfDirV tf i j = (tfCtor tf i j).cdir

public export
tfnumConst : {0 nty : Nat} -> (tf : TypeFamily nty) -> (i : Fin nty) ->
  Fin (tfnumCtor tf i) -> Nat
tfnumConst tf i j = (tfCtor tf i j).numConst

public export
tfConstV : {0 nty : Nat} -> (tf : TypeFamily nty) -> (i : Fin nty) ->
  (j : Fin (tfnumCtor tf i)) -> Vect (tfnumConst tf i j) Nat
tfConstV tf i j = (tfCtor tf i j).cconst

public export
InterpTF : {0 nty : Nat} -> TypeFamily nty -> FinSliceEndofunctor nty
InterpTF {nty} tf sl ity =
  (i : Fin (tfnumCtor tf ity) **
   let ct = tfCtor tf ity i in
   (FinV {len=ct.numConst} ct.cconst,
    HVect {k=ct.numDir} $ map sl ct.cdir))

public export
showITF : {0 nty : Nat} ->
  (tf : TypeFamily nty) -> (sl : FinSliceObj nty) ->
  (sh : (i' : Fin nty) -> sl i' -> String) ->
  (i : Fin nty) ->
  InterpTF {nty} tf sl i -> String
showITF {nty} tf sl sh i (j ** (fv, hv)) =
  "(" ++ show j ++ " ** " ++ "(" ++ showFinV fv ++ "," ++
    showHV sl sh (index j (index i tf.rtype).ctor).cdir hv ++ "))"

public export
itfEq : {0 nty : Nat} ->
  (tf : TypeFamily nty) -> (sl : FinSliceObj nty) ->
  (deq : (i' : Fin nty) -> DecEqPred (sl i')) ->
  (i : Fin nty) ->
  (x, x' : InterpTF {nty} tf sl i) -> Dec (x = x')
itfEq {nty} tf sl deq i (j ** (fv, hv)) (j' ** (fv', hv')) =
  case decEq j j' of
    Yes Refl => case finVEq fv fv' of
      Yes eq =>
        case hvDecEq sl deq (tfDirV tf i j') hv hv' of
          Yes Refl => Yes $
            replace
              {p=(\fv'' =>
                (MkDPair j' (fv, hv')) =
                (MkDPair j'
                  {p=(\j'' =>
                    (FinV (tfConstV tf i j''),
                     HVect
                      (map sl ((tfDirV tf i j'')))))}
                      (fv'', hv')))}
              eq Refl
          No neq => No $ \eq => case eq of Refl => neq Refl
      No neq => No $ \eq => case eq of Refl => neq Refl
    No neq => No $ \eq => case eq of Refl => neq Refl

public export
data MuTF : {0 nty : Nat} -> TypeFamily nty -> FinSliceObj nty where
  InTF : {0 nty : Nat} -> {tf : TypeFamily nty} ->
    (i : Fin nty) -> InterpTF {nty} tf (MuTF tf) i -> MuTF tf i

public export
TFAlg : {nty : Nat} -> TypeFamily nty -> FinSliceObj nty -> Type
TFAlg {nty} tf sl = SliceMorphism (InterpTF {nty} tf sl) sl

mutual
  public export
  tfCata : {0 nty : Nat} -> {tf : TypeFamily nty} -> {sl : FinSliceObj nty} ->
    TFAlg tf sl -> SliceMorphism {a=(Fin nty)} (MuTF tf) sl
  tfCata {nty} {tf} {sl} alg i (InTF i (j ** (fv, hv))) =
    alg i
      (j **
       (fv, tfCataV {nty} {tf} {sl} alg (tfnumDir tf i j) (tfDirV tf i j) hv))

  public export
  tfCataV : {0 nty : Nat} -> {tf : TypeFamily nty} -> {sl : FinSliceObj nty} ->
    TFAlg tf sl -> (n : Nat) -> (v : Vect n (Fin nty)) ->
    HVect (map (MuTF tf) v) -> HVect (map sl v)
  tfCataV {nty} {tf} {sl} alg Z [] [] = []
  tfCataV {nty} {tf} {sl} alg (S n) (i :: v) (x :: hv) =
    tfCata {nty} {tf} {sl} alg i x :: tfCataV {nty} {tf} {sl} alg n v hv

public export
ShowMuTFAlg : {nty : Nat} -> (tf : TypeFamily nty) -> TFAlg tf (const String)
ShowMuTFAlg {nty} tf = showITF {nty} tf (const String) (const id)

public export
showMuTF : {nty : Nat} ->
  (tf : TypeFamily nty) -> (i : Fin nty) -> MuTF {nty} tf i -> String
showMuTF {nty} tf = tfCata {nty} {tf} (ShowMuTFAlg {nty} tf)

public export
record Position where
  constructor Pos
  pDirTy : Type
  pDir : List pDirTy

public export
record Arena where
  constructor Ar
  aTy : Type
  aPosIdx : Type
  aPos : aPosIdx -> Position
  aPosTyMap : (i : aPosIdx) -> (aPos i).pDirTy -> aTy
  aAssign : aPosIdx -> aTy

public export
APDirType : (ar : Arena) -> ar.aPosIdx -> Type
APDirType ar i = (ar.aPos i).pDirTy

public export
record SliceArena (domSlice, codSlice : Type) where
  constructor ProdAr
  saTy : codSlice -> Arena
  saAssign : (i : codSlice) -> (saTy i).aTy -> domSlice

public export
SliceEndoArena : Type -> Type
SliceEndoArena base = SliceArena base base

public export
saAr : SliceArena domSlice codSlice -> codSlice -> Arena
saAr sa ci = sa.saTy ci

public export
saPosIdx : SliceArena domSlice codSlice -> codSlice -> Type
saPosIdx sa ci = (saAr sa ci).aPosIdx

public export
saPos : (sa : SliceArena domSlice codSlice) ->
  (ci : codSlice) -> saPosIdx sa ci -> Position
saPos sa ci pi = (saAr sa ci).aPos pi

public export
saDirTy : (sa : SliceArena domSlice codSlice) ->
  (ci : codSlice) -> saPosIdx sa ci -> Type
saDirTy sa ci pi = (saPos sa ci pi).pDirTy

public export
saDir :
  (sa : SliceArena domSlice codSlice) -> (ci : codSlice) ->
  (pi : saPosIdx sa ci) -> List (saDirTy sa ci pi)
saDir sa ci pi = (saPos sa ci pi).pDir

public export
saDirIdx :
  (sa : SliceArena domSlice codSlice) -> (ci : codSlice) ->
  (pi : saPosIdx sa ci) -> Type
saDirIdx sa ci pi = (i : Nat ** InBounds i (saDir sa ci pi))

public export
sapAssign : (sa : SliceArena domSlice codSlice) -> (ci : codSlice) ->
  (pi : saPosIdx sa ci) -> saDirTy sa ci pi -> domSlice
sapAssign sa ci pi = sa.saAssign ci . (saTy sa ci).aPosTyMap pi

public export
SAInterpPoly : {domSlice : Type} -> {0 codSlice : Type} ->
  SliceArena domSlice codSlice -> SliceFunctor domSlice codSlice
SAInterpPoly sa ds ci =
  (pi : saPosIdx sa ci ** piDir : List (Sigma {a=domSlice} ds) **
   map fst piDir = map (sapAssign sa ci pi) (saDir sa ci pi))

public export
saInterpPolyMap : {domSlice : Type} -> {0 codSlice : Type} ->
  (sa : SliceArena domSlice codSlice) ->
  {ds, ds' : SliceObj domSlice} ->
  SliceMorphism ds ds' ->
  SliceMorphism (SAInterpPoly sa ds) (SAInterpPoly sa ds')
saInterpPolyMap {domSlice} {codSlice} sa {ds} {ds'} m ci (pi ** piDir ** eq) =
  (pi ** smMap m piDir ** trans (smMapFstEq m piDir) eq)

public export
SAInterpDirich : {domSlice : Type} -> {codSlice : Type} ->
  SliceArena domSlice codSlice -> SliceFunctor domSlice codSlice
SAInterpDirich {domSlice} {codSlice} sa ds ci =
  (pi : saPosIdx sa ci **
   piDir : Sigma {a=domSlice} ds -> saDirIdx sa ci pi **
   (di : domSlice) -> (dd : ds di) ->
    sapAssign
      sa ci pi (index (fst (piDir (di ** dd))) {ok=(snd (piDir (di ** dd)))}
      (saDir sa ci pi)) =
    di)

public export
saInterpDirichMap : {domSlice : Type} -> {0 codSlice : Type} ->
  (sa : SliceArena domSlice codSlice) ->
  {ds, ds' : SliceObj domSlice} ->
  SliceMorphism ds ds' ->
  SliceMorphism (SAInterpDirich sa ds') (SAInterpDirich sa ds)
saInterpDirichMap {domSlice} {codSlice} sa {ds} {ds'} m ci (pi ** piDir ** eq) =
  (pi ** piDir . smApp m ** \di, dd => eq di (m di dd))

public export
SAAlg : {base : Type} -> SliceEndoArena base -> SliceObj base -> Type
SAAlg {base} sa s = SliceMorphism {a=base} (SAInterpPoly sa s) s

public export
data SAInterpMu : {0 base : Type} -> SliceEndoArena base -> SliceObj base where
  InSAM :
    {0 base : Type} -> {0 sa : SliceEndoArena base} ->
    SAAlg {base} sa (SAInterpMu sa)

------------------------------------------------------------------
------------------------------------------------------------------
---- Experiments with subobject classifiers and power objects ----
------------------------------------------------------------------
------------------------------------------------------------------

-- Subobject classifier in what I think is the style of the HoTT book with
-- an `isProp` as in https://ncatlab.org/nlab/show/mere+proposition.

public export
IsHProp : Type -> Type
IsHProp a = (x, y : a) -> x = y

public export
SubCFromHProp : Type
SubCFromHProp = Subset0 Type IsHProp

public export
PowerObjFromProp : Type -> Type
PowerObjFromProp a = a -> SubCFromHProp

public export
TrueForHProp : () -> SubCFromHProp
TrueForHProp () = Element0 Unit $ \(), () => Refl

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
0 ChiForHPropPbToDom : {0 a, b : Type} ->
  (f : a -> b) -> (isMonic : (x, y : a) -> f x = f y -> x = y) ->
  Pullback {a=b} {b=Unit} {c=SubCFromHProp}
    (ChiForHProp f isMonic) TrueForHProp ->
  a
ChiForHPropPbToDom {a} {b} f isMonic (Element0 (eb, ()) eq) =
  fst0 $ replace {p=id} (sym $ elementInjectiveFst eq) ()

-- `Type` itself as a subobject classifier -- treating it like `Prop`.
public export
SubCFromTypeAsSubC : Type
SubCFromTypeAsSubC = Type

public export
PowerObjFromTypeAsSubC : Type -> Type
PowerObjFromTypeAsSubC = SliceObj

public export
CharToPowerFromTypeAsSubC : {0 a : Type} ->
  (a -> SubCFromTypeAsSubC) -> PowerObjFromTypeAsSubC a
CharToPowerFromTypeAsSubC {a} chi = chi

public export
PowerToCharFromTypeAsSubC : {0 a : Type} ->
  PowerObjFromTypeAsSubC a -> (a -> SubCFromTypeAsSubC)
PowerToCharFromTypeAsSubC {a} po e = po e

public export
TrueFromTypeAsSubC : () -> SubCFromTypeAsSubC
TrueFromTypeAsSubC () = ()

public export
ChiForTypeAsSubC : {0 a, b : Type} -> (a -> b) -> b -> SubCFromTypeAsSubC
ChiForTypeAsSubC {a} {b} m eb = Exists0 a $ \ea => m ea = eb

public export
ChiForTypeAsSubCToPb :
  (subCmereProp : {p, p' : SubCFromTypeAsSubC} -> p = p') ->
  {0 a, b : Type} -> (f, g : a -> b) ->
  (ee : Equalizer f g) ->
  Pullback {a} {b=Unit} {c=SubCFromTypeAsSubC}
    (ChiForTypeAsSubC (equalizerInj f g)) TrueFromTypeAsSubC
ChiForTypeAsSubCToPb subCmereProp {a} {b} f g (Element0 eeq eq) =
  Element0 (eeq, ()) subCmereProp

-- A type together with a term of that type.
public export
SubCFromType : Type
SubCFromType = Exists0 Type (\ty => ty)

public export
PowerObjFromType : Type -> Type
PowerObjFromType a = Exists0 (SliceObj a) (\sl => (x : a) -> sl x)

public export
CharToPowerFromType : {0 a : Type} -> (a -> SubCFromType) -> PowerObjFromType a
CharToPowerFromType chi = Evidence0 (fst0 . chi) (\x => snd0 (chi x))

public export
PowerToCharFromType : {0 a : Type} -> PowerObjFromType a -> (a -> SubCFromType)
PowerToCharFromType po e = Evidence0 (fst0 po e) (snd0 po e)

public export
TrueFromType : () -> SubCFromType
TrueFromType () = Evidence0 (Unit, Unit) ((), ())

-- Produce the characteristic function of `Equalizer f g`.
public export
ChiForType : {0 a, b : Type} -> (f, g : a -> b) -> (a -> SubCFromType)
ChiForType {a} {b} f g ea = Evidence0 (b, b) (f ea, g ea)

public export
ChiForTypeToPb :
  (subCmereProp : {p, p' : SubCFromType} -> p = p') ->
  {0 a, b : Type} -> (f, g : a -> b) ->
  Equalizer f g ->
  Pullback {a} {b=Unit} {c=SubCFromType} (ChiForType f g) TrueFromType
ChiForTypeToPb subCmereProp {a} {b} f g (Element0 eeq eq) =
  Element0 (eeq, ()) subCmereProp

public export
ChiForTypeFromPb : {0 a, b : Type} -> (f, g : a -> b) ->
  Pullback {a} {b=Unit} {c=SubCFromType} (ChiForType f g) TrueFromType ->
  Equalizer f g
ChiForTypeFromPb {a} {b} f g (Element0 (ea, ()) eq) =
  Element0 ea $ case exists0inj1 eq of
    Refl =>
      let eq2 = exists0inj2 eq in
      rewrite fstEq eq2 in
      rewrite sndEq eq2 in
      Refl

public export
SubCFromBoolPred : Type
SubCFromBoolPred = Exists0 Type (\ty => ty -> Bool)

public export
PowerObjFromBoolPred : Type -> Type
PowerObjFromBoolPred a = Exists0 (SliceObj a) (\ty => Sigma {a} ty -> Bool)

public export
CharToPowerFromBoolPred : {0 a : Type} ->
  (a -> SubCFromBoolPred) -> PowerObjFromBoolPred a
CharToPowerFromBoolPred chi =
  Evidence0 (fst0 . chi) (\x => snd0 (chi (fst x)) (snd x))

public export
PowerToCharFromBoolPred : {0 a : Type} -> PowerObjFromBoolPred a ->
  (a -> SubCFromBoolPred)
PowerToCharFromBoolPred po e =
  Evidence0 (fst0 po e) (\edp => snd0 po (e ** edp))

public export
TrueFromBoolPred : () -> SubCFromBoolPred
TrueFromBoolPred () =
  Evidence0 ((Bool, Bool) -> Bool) (\decrel => decrel (True, True))

-- Produce the characteristic function of `Equalizer f g`.
public export
ChiForBoolPred : {0 a, b : Type} -> (f, g : a -> b) -> (a -> SubCFromBoolPred)
ChiForBoolPred {a} {b} f g ea =
  Evidence0 ((b, b) -> Bool) (\decrel => decrel (f ea, g ea))

public export
ChiForBoolPredToPb :
  (subCmereProp : (ty, ty' : Type) -> (x : ty) -> (x' : ty') ->
    Evidence0 {type=Type} {this=(\ty'' => ty'' -> Bool)}
      ((ty, ty) -> Bool)
      (\decrel : ((ty, ty) -> Bool) => decrel (x, x))
    ~=~
    Evidence0 {type=Type} {this=(\ty'' => ty'' -> Bool)}
      ((ty', ty') -> Bool)
      (\decrel : ((ty', ty') -> Bool) => decrel (x', x'))) ->
  {0 a, b : Type} -> (f, g : a -> b) ->
  Equalizer f g ->
  Pullback
    {a} {b=Unit} {c=SubCFromBoolPred} (ChiForBoolPred f g) TrueFromBoolPred
ChiForBoolPredToPb subCmereProp {a} {b} f g (Element0 ea eq) =
  Element0 (ea, ()) $ rewrite eq in subCmereProp b Bool _ True

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
---- Subobject classifiers for monics only (and those from equalizers only) ----
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

public export
0 SubCFromEq : Type
SubCFromEq = Exists0 Type (\ty => (ty, ty))

public export
0 PowerObjFromEq : Type -> Type
PowerObjFromEq a = Exists0 (SliceObj a) (\sl => (Pi sl, Pi sl))

public export
CharToPowerFromEq : {0 a : Type} -> (a -> SubCFromEq) -> PowerObjFromEq a
CharToPowerFromEq chi =
  Evidence0 (fst0 . chi) (\x => fst (snd0 (chi x)), \x => snd (snd0 (chi x)))

public export
PowerToCharFromEq : {0 a : Type} -> PowerObjFromEq a -> (a -> SubCFromEq)
PowerToCharFromEq {a} po ea =
  Evidence0 (fst0 po ea) (fst (snd0 po) ea, snd (snd0 po) ea)

public export
TrueFromEq : () -> SubCFromEq
TrueFromEq () = Evidence0 Unit ((), ())

-- Produce the characteristic function of `Equalizer f g`.
public export
ChiForEq : {0 a, b : Type} -> (f, g : a -> b) -> (a -> SubCFromEq)
ChiForEq {a} {b} f g ea = Evidence0 b (f ea, g ea)

public export
ChiForEqToPb :
  (subCmereProp :
    {p, p' : SubCFromEq} ->
    fst (snd0 p) = snd (snd0 p) ->
    fst (snd0 p') = snd (snd0 p') ->
    p = p') ->
  {0 a, b : Type} -> (f, g : a -> b) ->
  Equalizer f g ->
  Pullback {a} {b=Unit} {c=SubCFromEq} (ChiForEq f g) TrueFromEq
ChiForEqToPb subCmereProp {a} {b} f g (Element0 eeq eq) =
  Element0 (eeq, ()) (subCmereProp eq Refl)

public export
ChiForEqFromPb : {0 a, b : Type} -> (f, g : a -> b) ->
  Pullback {a} {b=Unit} {c=SubCFromEq} (ChiForEq f g) TrueFromEq ->
  Equalizer f g
ChiForEqFromPb {a} {b} f g (Element0 (ea, ()) eq) =
  Element0 ea $ case exists0inj1 eq of
    Refl =>
      let eq2 = exists0inj2 eq in
      rewrite fstEq eq2 in
      rewrite sndEq eq2 in
      Refl

public export
ChiForEqTrueCorrect :
  (subCmereProp :
    {p, p' : SubCFromEq} ->
    fst (snd0 p) = snd (snd0 p) ->
    fst (snd0 p') = snd (snd0 p') ->
    p = p') ->
  {0 a, b : Type} -> (f, g : a -> b) ->
  (x : a) -> (eq : f x = g x) ->
  ChiForEq f g x = TrueFromEq ()
ChiForEqTrueCorrect subCmereProp f g x eq = subCmereProp eq Refl

public export
ChiForEqFalseCorrect :
  {a, b : Type} -> (f, g : a -> b) ->
  (x : a) -> Not (f x = g x) ->
  Not (ChiForEq f g x = TrueFromEq ())
ChiForEqFalseCorrect f g x neq eq with (exists0inj1 eq)
  ChiForEqFalseCorrect f g x neq eq | Refl =
      neq $
        let eq2 = exists0inj2 eq in
        rewrite fstEq eq2 in
        rewrite sndEq eq2 in
        Refl

---------------------------------------------------------------
---------------------------------------------------------------
---- Categories internal to 'Type' as a well-pointed topos ----
---------------------------------------------------------------
---------------------------------------------------------------

public export
record TCatSig where
  constructor TCat
  tcObj : Type
  0 tcObjEq : tcObj -> tcObj -> Type
  0 tcObjEqRefl : (0 a : tcObj) -> tcObjEq a a
  0 tcObjEqSym : {0 a, b : tcObj} ->
    (0 _ : tcObjEq a b) -> tcObjEq b a
  0 tcObjEqTrans : {0 a, b, c : tcObj} ->
    (0 _ : tcObjEq b c) -> (0 _ : tcObjEq a b) -> tcObjEq a c
  tcMorph : tcObj -> tcObj -> Type
  0 tcMorphEq : {0 dom, cod, dom', cod' : tcObj} ->
    (0 _ : tcObjEq dom dom') -> (0 _ : tcObjEq cod cod') ->
    (0 _ : tcMorph dom cod) -> (0 _ : tcMorph dom' cod') -> Type
  0 tcMorphEqRefl : {0 dom, cod : tcObj} ->
    (0 domeq : tcObjEq dom dom) -> (0 codeq : tcObjEq cod cod) ->
    (0 m : tcMorph dom cod) -> tcMorphEq domeq codeq m m
  0 tcMorphEqSym : {0 dom, cod, dom', cod' : tcObj} ->
    {0 domeq : tcObjEq dom dom'} -> {0 codeq : tcObjEq cod cod'} ->
    {0 domeqsym : tcObjEq dom' dom} -> {0 codeqsym : tcObjEq cod' cod} ->
    (0 m : tcMorph dom cod) -> (0 m' : tcMorph dom' cod') ->
    (0 _ : tcMorphEq domeq codeq m m') -> tcMorphEq domeqsym codeqsym m' m
  0 tcMorphEqTrans : {0 dom, cod, dom', cod', dom'', cod'' : tcObj} ->
    {0 domeq : tcObjEq dom dom'} -> {0 codeq : tcObjEq cod cod'} ->
    {0 domeq' : tcObjEq dom' dom''} -> {0 codeq' : tcObjEq cod' cod''} ->
    {0 domeq'' : tcObjEq dom dom''} -> {0 codeq'' : tcObjEq cod cod''} ->
    (0 m : tcMorph dom cod) -> (0 m' : tcMorph dom' cod') ->
    (0 m'' : tcMorph dom'' cod'') ->
    (0 m''' : tcMorph dom'' cod'') ->
    (0 _ : tcMorphEq domeq' codeq' m' m'') ->
    (0 _ : tcMorphEq domeq codeq m m') ->
    tcMorphEq domeq'' codeq'' m m''
  tcId : (obj : tcObj) -> tcMorph obj obj
  tcCompose : {0 a, b, b', c : tcObj} ->
    (0 _ : tcObjEq b b') ->
    tcMorph b' c -> tcMorph a b -> tcMorph a c
  0 tcIdLeft : {0 a, b, b' : tcObj} ->
    {0 domeq : tcObjEq a a} -> {0 codeq, codeq' : tcObjEq b b'} ->
    (0 m : tcMorph a b) ->
    tcMorphEq {dom=a} {cod=b} {dom'=a} {cod'=b'}
      domeq codeq m (tcCompose {a} {b} {b'} {c=b'} codeq' (tcId b') m)
  0 tcIdRight : {0 a, a', b : tcObj} ->
    {0 domeq, domeq' : tcObjEq a a'} -> {0 codeq : tcObjEq b b} ->
    (0 m : tcMorph a' b) ->
    tcMorphEq {dom=a} {cod=b} {dom'=a'} {cod'=b}
      domeq codeq (tcCompose {a} {b=a} {b'=a'} {c=b} domeq' m (tcId a)) m
  0 tcComposeAssoc : {0 a, b, b', c, c', d : tcObj} ->
    {0 domeq : tcObjEq a a} -> {0 codeq : tcObjEq d d} ->
    {0 beq, beq' : tcObjEq b b'} -> {0 ceq, ceq' : tcObjEq c c'} ->
    (0 h : tcMorph c' d) -> (0 g : tcMorph b' c) -> (0 f : tcMorph a b) ->
    tcMorphEq {dom=a} {cod=d}
      domeq codeq
      (tcCompose ceq h (tcCompose beq' g f))
      (tcCompose beq (tcCompose ceq' h g) f)

public export
record TFunctorSig (c, d : TCatSig) where
  constructor TFunctor
  tfObjMap : c.tcObj -> d.tcObj
  0 tfObjMapCorrect : {0 a, b : c.tcObj} ->
    (0 _ : c.tcObjEq a b) -> d.tcObjEq (tfObjMap a) (tfObjMap b)
  tfMorphMap : {0 a, b : c.tcObj} ->
    c.tcMorph a b -> d.tcMorph (tfObjMap a) (tfObjMap b)
  0 tfMorphMapCorrect : {0 a, b, a', b' : c.tcObj} ->
    {0 m : c.tcMorph a b} -> {0 m' : c.tcMorph a' b'} ->
    (0 domeq : c.tcObjEq a a') -> (0 codeq : c.tcObjEq b b') ->
    (0 domMapEq : d.tcObjEq (tfObjMap a) (tfObjMap a')) ->
    (0 codMapEq : d.tcObjEq (tfObjMap b) (tfObjMap b')) ->
    (0 _ : c.tcMorphEq {dom=a} {dom'=a'} {cod=b} {cod'=b'} domeq codeq m m') ->
    d.tcMorphEq
      {dom=(tfObjMap a)} {cod=(tfObjMap b)}
      {dom'=(tfObjMap a')} {cod'=(tfObjMap b')}
      domMapEq codMapEq
      (tfMorphMap {a} {b} m) (tfMorphMap {a=a'} {b=b'} m')
  -- The laws for the application of functors to identities and
  -- compositions must still be written.

-------------------------
-------------------------
---- Terminal object ----
-------------------------
-------------------------

-------------------------
-------------------------
---- Finite products ----
-------------------------
-------------------------

--------------------------------
--------------------------------
---- Natural-numbers object ----
--------------------------------
--------------------------------

-------------------------------------------------
-------------------------------------------------
---- Geb s-expressions as polynomial functor ----
-------------------------------------------------
-------------------------------------------------

public export
data GExpSlice : Type where
  GSATOM : GExpSlice
  GSNAT : GExpSlice
  GSNATL : GExpSlice
  GSEXP : GExpSlice
  GSEXPL : GExpSlice

public export
gSliceAtom : GExpSlice -> GebAtom
gSliceAtom GSATOM = SL_ATOM
gSliceAtom GSNAT = SL_NAT
gSliceAtom GSNATL = SL_NATL
gSliceAtom GSEXP = SL_EXP
gSliceAtom GSEXPL = SL_EXPL

public export
Show GExpSlice where
  show = show . gSliceAtom

public export
GSliceSz : Nat
GSliceSz = 5

public export
GSliceFinDecoder : FinDecoder GExpSlice GSliceSz
GSliceFinDecoder FZ = GSATOM
GSliceFinDecoder (FS FZ) = GSNAT
GSliceFinDecoder (FS (FS FZ)) = GSNATL
GSliceFinDecoder (FS (FS (FS FZ))) = GSEXP
GSliceFinDecoder (FS (FS (FS (FS FZ)))) = GSEXPL

public export
GSliceNatEncoder : NatEncoder GSliceFinDecoder
GSliceNatEncoder GSATOM = (0 ** Refl ** Refl)
GSliceNatEncoder GSNAT =  (1 ** Refl ** Refl)
GSliceNatEncoder GSNATL = (2 ** Refl ** Refl)
GSliceNatEncoder GSEXP = (3 ** Refl ** Refl)
GSliceNatEncoder GSEXPL = (4 ** Refl ** Refl)

public export
GSliceFinDecEncoding : FinDecEncoding GExpSlice GSliceSz
GSliceFinDecEncoding = NatDecEncoding GSliceFinDecoder GSliceNatEncoder

public export
DecEq GExpSlice where
  decEq = fdeDecEq GSliceFinDecEncoding

public export
data GWExpNonAtomPos : Type where
  GPNAZ : GWExpNonAtomPos -- zero
  GPNAS : GWExpNonAtomPos -- successor
  GPNAX : GWExpNonAtomPos -- SExp
  GPNANN : GWExpNonAtomPos -- empty list of Nat
  GPNANC : GWExpNonAtomPos -- cons list of Nat
  GPNAXN : GWExpNonAtomPos -- empty list of SExp
  GPNAXC : GWExpNonAtomPos -- cons list of SExp

public export
data GWExpPos : Type where
  GPA : GebAtom -> GWExpPos
  GPNAP : GWExpNonAtomPos -> GWExpPos

public export
GPZ : GWExpPos
GPZ = GPNAP GPNAZ

public export
GPS : GWExpPos
GPS = GPNAP GPNAS

public export
GPX : GWExpPos
GPX = GPNAP GPNAX

public export
GPNN : GWExpPos
GPNN = GPNAP GPNANN

public export
GPNC : GWExpPos
GPNC = GPNAP GPNANC

public export
GPXN : GWExpPos
GPXN = GPNAP GPNAXN

public export
GPXC : GWExpPos
GPXC = GPNAP GPNAXC

public export
gNonAtomPosAtom : GWExpNonAtomPos -> GebAtom
gNonAtomPosAtom GPNAZ = POS_Z
gNonAtomPosAtom GPNAS = POS_S
gNonAtomPosAtom GPNAX = POS_X
gNonAtomPosAtom GPNANN = POS_NN
gNonAtomPosAtom GPNANC = POS_NC
gNonAtomPosAtom GPNAXN = POS_XN
gNonAtomPosAtom GPNAXC = POS_XC

public export
gPosAtom : GWExpPos -> GebAtom
gPosAtom (GPA a) = a
gPosAtom (GPNAP i) = gNonAtomPosAtom i

public export
Show GWExpPos where
  show = show . gPosAtom

public export
GPosSz : Nat
GPosSz = 7

public export
GPosFinDecoder : FinDecoder GWExpNonAtomPos GPosSz
GPosFinDecoder FZ = GPNAZ
GPosFinDecoder (FS FZ) = GPNAS
GPosFinDecoder (FS (FS FZ)) = GPNAX
GPosFinDecoder (FS (FS (FS FZ))) = GPNANN
GPosFinDecoder (FS (FS (FS (FS FZ)))) = GPNANC
GPosFinDecoder (FS (FS (FS (FS (FS FZ))))) = GPNAXN
GPosFinDecoder (FS (FS (FS (FS (FS (FS FZ)))))) = GPNAXC

public export
GPosNatEncoder : NatEncoder GPosFinDecoder
GPosNatEncoder GPNAZ = (0 ** Refl ** Refl)
GPosNatEncoder GPNAS = (1 ** Refl ** Refl)
GPosNatEncoder GPNAX = (2 ** Refl ** Refl)
GPosNatEncoder GPNANN = (3 ** Refl ** Refl)
GPosNatEncoder GPNANC = (4 ** Refl ** Refl)
GPosNatEncoder GPNAXN = (5 ** Refl ** Refl)
GPosNatEncoder GPNAXC = (6 ** Refl ** Refl)

public export
GPosFinDecEncoding : FinDecEncoding GWExpNonAtomPos GPosSz
GPosFinDecEncoding = NatDecEncoding GPosFinDecoder GPosNatEncoder

public export
DecEq GWExpNonAtomPos where
  decEq = fdeDecEq GPosFinDecEncoding

public export
DecEq GWExpPos where
  decEq (GPA a) (GPA a') = case decEq a a' of
    Yes Refl => Yes Refl
    No neq => No $ \Refl => neq Refl
  decEq (GPA _) (GPNAP _) = No $ \eq => case eq of Refl impossible
  decEq (GPNAP _) (GPA _) = No $ \eq => case eq of Refl impossible
  decEq (GPNAP i) (GPNAP i') = case decEq i i' of
    Yes Refl => Yes Refl
    No neq => No $ \Refl => neq Refl

public export
data GWExpDir : Type where
  GDS : GWExpDir
  GDXA : GWExpDir
  GDXNL : GWExpDir
  GDXXL : GWExpDir
  GDNCHD : GWExpDir
  GDNCTL : GWExpDir
  GDXCHD : GWExpDir
  GDXCTL : GWExpDir

public export
gDirAtom : GWExpDir -> GebAtom
gDirAtom GDS = DIR_S
gDirAtom GDXA = DIR_XA
gDirAtom GDXNL = DIR_XNL
gDirAtom GDXXL = DIR_XXL
gDirAtom GDNCHD = DIR_NCHD
gDirAtom GDNCTL = DIR_NCTL
gDirAtom GDXCHD = DIR_XCHD
gDirAtom GDXCTL = DIR_XCTL

public export
Show GWExpDir where
  show = show . gDirAtom

public export
GDirSz : Nat
GDirSz = 8

public export
GDirFinDecoder : FinDecoder GWExpDir GDirSz
GDirFinDecoder FZ = GDS
GDirFinDecoder (FS FZ) = GDXA
GDirFinDecoder (FS (FS FZ)) = GDXNL
GDirFinDecoder (FS (FS (FS FZ))) = GDXXL
GDirFinDecoder (FS (FS (FS (FS FZ)))) = GDNCHD
GDirFinDecoder (FS (FS (FS (FS (FS FZ))))) = GDNCTL
GDirFinDecoder (FS (FS (FS (FS (FS (FS FZ)))))) = GDXCHD
GDirFinDecoder (FS (FS (FS (FS (FS (FS (FS FZ))))))) = GDXCTL

public export
GDirNatEncoder : NatEncoder GDirFinDecoder
GDirNatEncoder GDS = (0 ** Refl ** Refl)
GDirNatEncoder GDXA = (1 ** Refl ** Refl)
GDirNatEncoder GDXNL = (2 ** Refl ** Refl)
GDirNatEncoder GDXXL = (3 ** Refl ** Refl)
GDirNatEncoder GDNCHD = (4 ** Refl ** Refl)
GDirNatEncoder GDNCTL = (5 ** Refl ** Refl)
GDirNatEncoder GDXCHD = (6 ** Refl ** Refl)
GDirNatEncoder GDXCTL = (7 ** Refl ** Refl)

public export
GDirFinDecEncoding : FinDecEncoding GWExpDir GDirSz
GDirFinDecEncoding = NatDecEncoding GDirFinDecoder GDirNatEncoder

public export
DecEq GWExpDir where
  decEq = fdeDecEq GDirFinDecEncoding

public export
gAssign : GWExpDir -> GExpSlice
gAssign GDS = GSNAT
gAssign GDXA = GSATOM
gAssign GDXNL = GSNATL
gAssign GDXXL = GSEXPL
gAssign GDNCHD = GSNAT
gAssign GDNCTL = GSNATL
gAssign GDXCHD = GSEXP
gAssign GDXCTL = GSEXPL

public export
gDirSlice : GWExpDir -> GWExpPos
gDirSlice GDS = GPS
gDirSlice GDXA = GPX
gDirSlice GDXNL = GPX
gDirSlice GDXXL = GPX
gDirSlice GDNCHD = GPNC
gDirSlice GDNCTL = GPNC
gDirSlice GDXCHD = GPXC
gDirSlice GDXCTL = GPXC

public export
gNonAtomPosSlice : GWExpNonAtomPos -> GExpSlice
gNonAtomPosSlice GPNAZ = GSNAT
gNonAtomPosSlice GPNAS = GSNAT
gNonAtomPosSlice GPNAX = GSEXP
gNonAtomPosSlice GPNANN = GSNATL
gNonAtomPosSlice GPNANC = GSNATL
gNonAtomPosSlice GPNAXN = GSEXPL
gNonAtomPosSlice GPNAXC = GSEXPL

public export
gPosSlice : GWExpPos -> GExpSlice
gPosSlice (GPA _) = GSATOM
gPosSlice (GPNAP i) = gNonAtomPosSlice i

public export
GWExpWTF : WTypeEndoFunc GExpSlice
GWExpWTF = MkWTF GWExpPos GWExpDir gAssign gDirSlice gPosSlice

public export
GWExpWT : SliceObj GExpSlice
GWExpWT = WTFMu GWExpWTF

public export
GWExpSigma : Type
GWExpSigma = Sigma {a=GExpSlice} GWExpWT

public export
GWExpA : Type
GWExpA = GWExpWT GSATOM

public export
GWExpN : Type
GWExpN = GWExpWT GSNAT

public export
GWExpNL : Type
GWExpNL = GWExpWT GSNATL

public export
GWExpX : Type
GWExpX = GWExpWT GSEXP

public export
GWExpXL : Type
GWExpXL = GWExpWT GSEXPL

public export
record GWExpAlg (sa : GExpSlice -> Type) where
  constructor GAlg
  galgA : GebAtom -> sa GSATOM
  galgZ : sa GSNAT
  galgS : sa GSNAT -> sa GSNAT
  galgNN : sa GSNATL
  galgNC : sa GSNAT -> sa GSNATL -> sa GSNATL
  galgEXP : sa GSATOM -> sa GSNATL -> sa GSEXPL -> sa GSEXP
  galgXN : sa GSEXPL
  galgXC : sa GSEXP -> sa GSEXPL -> sa GSEXPL

public export
GAlgToSPF : {sa : GExpSlice -> Type} -> GWExpAlg sa -> WTFAlg GWExpWTF sa
GAlgToSPF alg GSATOM (Element0 (GPA a) isl ** d) =
  alg.galgA a
GAlgToSPF alg GSATOM (Element0 (GPNAP GPNAZ) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSATOM (Element0 (GPNAP GPNAS) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSATOM (Element0 (GPNAP GPNAX) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSATOM (Element0 (GPNAP GPNANN) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSATOM (Element0 (GPNAP GPNANC) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSATOM (Element0 (GPNAP GPNAXN) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSATOM (Element0 (GPNAP GPNAXC) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNAT (Element0 (GPA a) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNAT (Element0 (GPNAP GPNAZ) isl ** d) =
  alg.galgZ
GAlgToSPF alg GSNAT (Element0 (GPNAP GPNAS) isl ** d) =
  alg.galgS $ d (Element0 GDS Refl)
GAlgToSPF alg GSNAT (Element0 (GPNAP GPNAX) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNAT (Element0 (GPNAP GPNANN) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNAT (Element0 (GPNAP GPNANC) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNAT (Element0 (GPNAP GPNAXN) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNAT (Element0 (GPNAP GPNAXC) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNATL (Element0 (GPA a) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNATL (Element0 (GPNAP GPNAZ) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNATL (Element0 (GPNAP GPNAS) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNATL (Element0 (GPNAP GPNAX) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNATL (Element0 (GPNAP GPNANN) isl ** d) =
  alg.galgNN
GAlgToSPF alg GSNATL (Element0 (GPNAP GPNANC) isl ** d) =
  alg.galgNC (d $ Element0 GDNCHD Refl) (d $ Element0 GDNCTL Refl)
GAlgToSPF alg GSNATL (Element0 (GPNAP GPNAXN) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSNATL (Element0 (GPNAP GPNAXC) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXP (Element0 (GPA a) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXP (Element0 (GPNAP GPNAZ) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXP (Element0 (GPNAP GPNAS) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXP (Element0 (GPNAP GPNAX) isl ** d) =
  alg.galgEXP
    (d $ Element0 GDXA Refl) (d $ Element0 GDXNL Refl) (d $ Element0 GDXXL Refl)
GAlgToSPF alg GSEXP (Element0 (GPNAP GPNANN) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXP (Element0 (GPNAP GPNANC) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXP (Element0 (GPNAP GPNAXN) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXP (Element0 (GPNAP GPNAXC) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXPL (Element0 (GPA a) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXPL (Element0 (GPNAP GPNAZ) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXPL (Element0 (GPNAP GPNAS) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXPL (Element0 (GPNAP GPNAX) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXPL (Element0 (GPNAP GPNANN) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXPL (Element0 (GPNAP GPNANC) isl ** d) =
  void $ case isl of Refl impossible
GAlgToSPF alg GSEXPL (Element0 (GPNAP GPNAXN) isl ** d) =
  alg.galgXN
GAlgToSPF alg GSEXPL (Element0 (GPNAP GPNAXC) isl ** d) =
  alg.galgXC (d $ Element0 GDXCHD Refl) (d $ Element0 GDXCTL Refl)

public export
gwexpCata : {sa : GExpSlice -> Type} ->
  GWExpAlg sa -> SliceMorphism {a=GExpSlice} GWExpWT sa
gwexpCata {sa} alg = wtfCata {wtf=GWExpWTF} {sa} (GAlgToSPF {sa} alg)

public export
GWExpWTtoGExpAlgSl : SliceObj GExpSlice
GWExpWTtoGExpAlgSl GSATOM = GebAtom
GWExpWTtoGExpAlgSl GSNAT = Nat
GWExpWTtoGExpAlgSl GSNATL = List Nat
GWExpWTtoGExpAlgSl GSEXP = GExp
GWExpWTtoGExpAlgSl GSEXPL = GList

public export
GWExpWTtoGExpAlg : GWExpAlg GWExpWTtoGExpAlgSl
GWExpWTtoGExpAlg = GAlg id 0 S [] (::) InS [] (::)

public export
gwexpWTtoGExpSl : SliceMorphism {a=GExpSlice} GWExpWT GWExpWTtoGExpAlgSl
gwexpWTtoGExpSl = gwexpCata GWExpWTtoGExpAlg

public export
gwexpWTtoGExp : GWExpX -> GExp
gwexpWTtoGExp = gwexpWTtoGExpSl GSEXP

public export
InGA : GebAtom -> GWExpA
InGA a = InWTFM (GSATOM ** Element0 (GPA a) Refl) $ \(Element0 d dsl) =>
  case d of
    GDS => void $ case dsl of Refl impossible
    GDXA => void $ case dsl of Refl impossible
    GDXNL => void $ case dsl of Refl impossible
    GDXXL => void $ case dsl of Refl impossible
    GDNCHD => void $ case dsl of Refl impossible
    GDNCTL => void $ case dsl of Refl impossible
    GDXCHD => void $ case dsl of Refl impossible
    GDXCTL => void $ case dsl of Refl impossible

public export
InGZ : GWExpN
InGZ = InWTFM (GSNAT ** Element0 GPZ Refl) $ \(Element0 d dsl) =>
  case d of
    GDS => void $ case dsl of Refl impossible
    GDXA => void $ case dsl of Refl impossible
    GDXNL => void $ case dsl of Refl impossible
    GDXXL => void $ case dsl of Refl impossible
    GDNCHD => void $ case dsl of Refl impossible
    GDNCTL => void $ case dsl of Refl impossible
    GDXCHD => void $ case dsl of Refl impossible
    GDXCTL => void $ case dsl of Refl impossible

public export
InGS : GWExpN -> GWExpN
InGS n = InWTFM (GSNAT ** Element0 GPS Refl) $ \(Element0 d dsl) =>
  case d of
    GDS => n
    GDXA => void $ case dsl of Refl impossible
    GDXNL => void $ case dsl of Refl impossible
    GDXXL => void $ case dsl of Refl impossible
    GDNCHD => void $ case dsl of Refl impossible
    GDNCTL => void $ case dsl of Refl impossible
    GDXCHD => void $ case dsl of Refl impossible
    GDXCTL => void $ case dsl of Refl impossible

public export
InGNat : Nat -> GWExpN
InGNat Z = InGZ
InGNat (S n) = InGS (InGNat n)

public export
InGNN : GWExpNL
InGNN = InWTFM (GSNATL ** Element0 GPNN Refl) $ \(Element0 d dsl) =>
  case d of
    GDS => void $ case dsl of Refl impossible
    GDXA => void $ case dsl of Refl impossible
    GDXNL => void $ case dsl of Refl impossible
    GDXXL => void $ case dsl of Refl impossible
    GDNCHD => void $ case dsl of Refl impossible
    GDNCTL => void $ case dsl of Refl impossible
    GDXCHD => void $ case dsl of Refl impossible
    GDXCTL => void $ case dsl of Refl impossible

public export
InGNC : GWExpN -> GWExpNL -> GWExpNL
InGNC n ns = InWTFM (GSNATL ** Element0 GPNC Refl) $ \(Element0 d dsl) =>
  case d of
    GDS => void $ case dsl of Refl impossible
    GDXA => void $ case dsl of Refl impossible
    GDXNL => void $ case dsl of Refl impossible
    GDXXL => void $ case dsl of Refl impossible
    GDNCHD => n
    GDNCTL => ns
    GDXCHD => void $ case dsl of Refl impossible
    GDXCTL => void $ case dsl of Refl impossible

public export
InGNatC : Nat -> GWExpNL -> GWExpNL
InGNatC n ns = InGNC (InGNat n) ns

public export
InGNatList : List Nat -> GWExpNL
InGNatList = foldr InGNatC InGNN

public export
InGXN : GWExpXL
InGXN = InWTFM (GSEXPL ** Element0 GPXN Refl) $ \(Element0 d dsl) =>
  case d of
    GDS => void $ case dsl of Refl impossible
    GDXA => void $ case dsl of Refl impossible
    GDXNL => void $ case dsl of Refl impossible
    GDXXL => void $ case dsl of Refl impossible
    GDNCHD => void $ case dsl of Refl impossible
    GDNCTL => void $ case dsl of Refl impossible
    GDXCHD => void $ case dsl of Refl impossible
    GDXCTL => void $ case dsl of Refl impossible

public export
InGXC : GWExpX -> GWExpXL -> GWExpXL
InGXC x xs = InWTFM (GSEXPL ** Element0 GPXC Refl) $ \(Element0 d dsl) =>
  case d of
    GDS => void $ case dsl of Refl impossible
    GDXA => void $ case dsl of Refl impossible
    GDXNL => void $ case dsl of Refl impossible
    GDXXL => void $ case dsl of Refl impossible
    GDNCHD => void $ case dsl of Refl impossible
    GDNCTL => void $ case dsl of Refl impossible
    GDXCHD => x
    GDXCTL => xs

public export
InGX : GebAtom -> GWExpNL -> GWExpXL -> GWExpX
InGX a ns xs = InWTFM (GSEXP ** Element0 GPX Refl) $ \(Element0 d dsl) =>
  case d of
    GDS => void $ case dsl of Refl impossible
    GDXA => InGA a
    GDXNL => ns
    GDXXL => xs
    GDNCHD => void $ case dsl of Refl impossible
    GDNCTL => void $ case dsl of Refl impossible
    GDXCHD => void $ case dsl of Refl impossible
    GDXCTL => void $ case dsl of Refl impossible

public export
InGNatX : GebAtom -> List Nat -> GWExpXL -> GWExpX
InGNatX a ns = InGX a (InGNatList ns)

public export
InGWExpList : List GWExpX -> GWExpXL
InGWExpList = foldr InGXC InGXN

public export
GExpToWTAlg : SXLAlg GebAtom GWExpX GWExpXL
GExpToWTAlg = SXA InGNatX InGXN InGXC

public export
gexpToWT : GExp -> GWExpX
gexpToWT = sxCata GExpToWTAlg

------------------------------------------------------------------------
------------------------------------------------------------------------
---- Geb S-expression as inductive dependent polynomial endofunctor ----
------------------------------------------------------------------------
------------------------------------------------------------------------

-- Equivalent to GExp, but using the inductive representation of
-- dependent polynomial endofunctors, rather than the W-type
-- representation.  This is largely for comparison of the resulting
-- code.

--------------------------
---- Atom endofunctor ----
--------------------------

public export
GAtomF : PolyFunc
GAtomF = PFConstArena GebAtom

public export
GAtomPos : Type
GAtomPos = pfPos GAtomF

public export
GAtomDir : SliceObj GAtomPos
GAtomDir = pfDir {p=GAtomF}

public export
GAtomSPF : (0 x : Type) -> SlicePolyFunc x ()
GAtomSPF _ = pfSlice GAtomF $ \(a ** v) => void v

------------------------------------------
---- List (parameterized) endofunctor ----
------------------------------------------

public export
GListPosL : Type
GListPosL = BoolCP  -- Left = nil; Right = cons

public export
GListDirL : SliceObj GListPosL
GListDirL (Left ()) = Void -- nil has no directions
GListDirL (Right ()) = BoolCP -- cons has two (Left = head; Right = tail)

public export
GListSlice : Type
GListSlice = BoolCP  -- Left = input PolyFunc; Right = list of input PolyFunc

public export
GListLAssign : Sigma {a=GListPosL} GListDirL -> GListSlice
GListLAssign (Left () ** d) = void d -- nil has no directions
GListLAssign (Right () ** Left ()) = Left () -- head is one input type
GListLAssign (Right () ** Right ()) = Right () -- tail is the other input type
  -- (which can be list itself, if we take a fixed point of the functor)

public export
GListPos : PolyFunc -> SliceObj GListSlice
GListPos p (Left ()) = pfPos p
GListPos p (Right ()) = GListPosL

public export
GListDir : (p : PolyFunc) -> Pi (SliceObj . GListPos p)
GListDir p (Left ()) = pfDir {p}
GListDir p (Right ()) = GListDirL

public export
GListAssign : (p : PolyFunc) -> (sl : GListSlice) -> (i : GListPos p sl) ->
  GListDir p sl i -> GListSlice
GListAssign p (Left ()) i d = (Left ()) -- 'p' dirs are all in PolyFunc slice
GListAssign p (Right ()) i d = GListLAssign (i ** d)

-- Given two types, returns one:  a type with two positions, one of which
-- is the empty list and one of which is a cons cell of the two types.
-- (Thus, if one input type is some fixed type `a` and the output type is
-- recursively fed back into the other input type, this becomes `List a`.)
public export
GListSPF : SlicePolyFunc GListSlice ()
GListSPF =
  (\() => GListPosL **
   \(() ** i) => GListDirL i **
   \((() ** i) ** d) => GListLAssign (i ** d))

-- An endofunctor on `Type x Type`.  If we take a fixed point, then we
-- obtain a type which produces pairs of the fixed point of `PolyFunc` and
-- lists of the fixed point of `PolyFunc`.
public export
GListESPF : PolyFunc -> SlicePolyEndoFunc GListSlice
GListESPF p =
  (GListPos p **
   \(sl ** i) => GListDir p sl i **
   \((sl ** i) ** d) => GListAssign p sl i d)

------------------------------------
---- Natural number endofunctor ----
------------------------------------

public export
GNatF : PolyFunc
GNatF = pfMaybeArena

public export
GNatPos : Type
GNatPos = pfPos GNatF

public export
GNatDir : SliceObj GNatPos
GNatDir = pfDir {p=GNatF}

public export
gNatPosAtom : GNatPos -> GebAtom
gNatPosAtom (Left ()) = POS_S
gNatPosAtom (Right ()) = POS_Z

public export
gNatDirAtom : Sigma {a=GNatPos} GNatDir -> GebAtom
gNatDirAtom ((Left ()) ** ()) = DIR_S
gNatDirAtom ((Right ()) ** v) = void v

public export
GNatSPF : SlicePolyFunc () ()
GNatSPF = UnitUnitSPFFromPolyFunc GNatF

------------------------------------------
---- Expression-component endofunctor ----
------------------------------------------

-- An expression has only one position, with three directions:  an atom,
-- a natural number list, and an expression list.
public export
GExpXNumDir : Nat
GExpXNumDir = 3

public export
GExpXSlice : Type
GExpXSlice = Fin GExpXNumDir

public export
GExpF : PolyFunc
GExpF = PFHomArena GExpXSlice

public export
GExpPos : Type
GExpPos = pfPos GExpF

public export
GExpDir : SliceObj GExpPos
GExpDir = pfDir {p=GExpF}

public export
GExpPosAtom : GExpPos -> GebAtom
GExpPosAtom () = POS_X

public export
GExpDirAtom : Sigma {a=GExpPos} GExpDir -> GebAtom
GExpDirAtom (() ** FZ) = DIR_XA
GExpDirAtom (() ** FS FZ) = DIR_XNL
GExpDirAtom (() ** FS (FS FZ)) = DIR_XXL

public export
GExpXSPF : SlicePolyFunc GExpXSlice ()
GExpXSPF = SliceFuncDimap (pfSliceAll GExpF) (\(() ** d) => d) id

-----------------------------------------
---- Natural number list endofunctor ----
-----------------------------------------

public export
GNatLSPF : SlicePolyFunc GListSlice Unit
GNatLSPF = GListSPF

public export
GNatExpLAssign : GListSlice -> GExpSlice
GNatExpLAssign (Left ()) = GSNAT
GNatExpLAssign (Right ()) = GSNATL

public export
GNatLExpSPF : SlicePolyFunc GExpSlice Unit
GNatLExpSPF = SliceFuncLmap GListSPF GNatExpLAssign

public export
GNatLFPos : Type
GNatLFPos = spfPos GNatLSPF ()

public export
GNatLFDir : SliceObj GNatLFPos
GNatLFDir = spfSliceDir GNatLSPF ()

public export
GNatLFPosAtom : GNatLFPos -> GebAtom
GNatLFPosAtom (Left ()) = POS_NN
GNatLFPosAtom (Right ()) = POS_NC

public export
GNatLFDirAtom : Sigma {a=GNatLFPos} GNatLFDir -> GebAtom
GNatLFDirAtom ((Left ()) ** d) = void d
GNatLFDirAtom (Right () ** (Left ())) = DIR_NCHD
GNatLFDirAtom (Right () ** Right ()) = DIR_NCTL

-------------------------------------
---- Expression list endofunctor ----
-------------------------------------

public export
GExpLSPF : SlicePolyFunc GListSlice Unit
GExpLSPF = GListSPF

public export
GXExpLAssign : GListSlice -> GExpSlice
GXExpLAssign (Left ()) = GSEXP
GXExpLAssign (Right ()) = GSEXPL

public export
GExpLExpSPF : SlicePolyFunc GExpSlice Unit
GExpLExpSPF = SliceFuncLmap GListSPF GXExpLAssign

public export
GExpLFPos : Type
GExpLFPos = spfPos GExpLSPF ()

public export
GExpLFDir : SliceObj GExpLFPos
GExpLFDir = spfSliceDir GExpLSPF ()

public export
GExpLFPosAtom : GExpLFPos -> GebAtom
GExpLFPosAtom (Left ()) = POS_XN
GExpLFPosAtom (Right ()) = POS_XC

public export
GExpLFDirAtom : Sigma {a=GExpLFPos} GExpLFDir -> GebAtom
GExpLFDirAtom ((Left ()) ** d) = void d
GExpLFDirAtom (Right () ** (Left ())) = DIR_XCHD
GExpLFDirAtom (Right () ** Right ()) = DIR_XCTL

----------------------------------------
---- Overall expression endofunctor ----
----------------------------------------

public export
GAtomExpSPF : SlicePolyFunc GExpSlice Unit
GAtomExpSPF = GAtomSPF GExpSlice

public export
GNatExpAssign : Unit -> GExpSlice
GNatExpAssign () = GSNAT

public export
GNatExpSPF : SlicePolyFunc GExpSlice Unit
GNatExpSPF = SliceFuncLmap GNatSPF GNatExpAssign

public export
GXExpAssign : GExpXSlice -> GExpSlice
GXExpAssign FZ = GSATOM
GXExpAssign (FS FZ) = GSNATL
GXExpAssign (FS (FS FZ)) = GSEXPL

public export
GXExpSPF : SlicePolyFunc GExpSlice Unit
GXExpSPF = SliceFuncLmap GExpXSPF GXExpAssign

public export
GSExpCombinedSlice : Type
GSExpCombinedSlice = Either Unit (Either Unit (Either Unit (Either Unit Unit)))

public export
GSExpCombined : SlicePolyFunc GExpSlice GSExpCombinedSlice
GSExpCombined =
  spfCoprodCod GAtomExpSPF (spfCoprodCod GNatExpSPF
    (spfCoprodCod GNatLExpSPF (spfCoprodCod GXExpSPF GExpLExpSPF)))

public export
GSExpSPFAssign : GExpSlice -> GSExpCombinedSlice
GSExpSPFAssign GSATOM = Left ()
GSExpSPFAssign GSNAT = Right (Left ())
GSExpSPFAssign GSNATL = Right (Right (Left ()))
GSExpSPFAssign GSEXP = Right (Right (Right (Left ())))
GSExpSPFAssign GSEXPL = Right (Right (Right (Right ())))

public export
GSExpSPF : SlicePolyEndoFunc GExpSlice
GSExpSPF = SliceFuncRmap GSExpCombined GSExpSPFAssign

public export
GSExp : SliceObj GExpSlice
GSExp = SPFMu GSExpSPF

public export
GSExpSigma : Type
GSExpSigma = Sigma {a=GExpSlice} GSExp

public export
GSExpA : Type
GSExpA = GSExp GSATOM

public export
GSExpN : Type
GSExpN = GSExp GSNAT

public export
GSExpNL : Type
GSExpNL = GSExp GSNATL

public export
GSExpX : Type
GSExpX = GSExp GSEXP

public export
GSExpXL : Type
GSExpXL = GSExp GSEXPL

public export
GSExpAlg : SliceObj GExpSlice -> Type
GSExpAlg = SPFAlg GSExpSPF

public export
gsexpCata : {sa : GExpSlice -> Type} ->
  GSExpAlg sa -> SliceMorphism {a=GExpSlice} GSExp sa
gsexpCata {sa} = spfCata {spf=GSExpSPF} {sa}

public export
GSExptoGExpAlgSl : SliceObj GExpSlice
GSExptoGExpAlgSl GSATOM = GebAtom
GSExptoGExpAlgSl GSNAT = Nat
GSExptoGExpAlgSl GSNATL = List Nat
GSExptoGExpAlgSl GSEXP = GExp
GSExptoGExpAlgSl GSEXPL = GList

public export
GSExptoGExpAlg : GSExpAlg GSExptoGExpAlgSl
GSExptoGExpAlg GSATOM = \(i ** d) => i
GSExptoGExpAlg GSNAT = \(i ** d) =>
  case i of (Left ()) => d () ; (Right ()) => Z
GSExptoGExpAlg GSNATL = \(i ** d) =>
  case i of (Left ()) => [] ; (Right ()) => d BCPFalse :: d BCPTrue
GSExptoGExpAlg GSEXP = \(i ** d) => case i of
  () => InS (d FZ) (d (FS FZ)) (d (FS (FS FZ)))
GSExptoGExpAlg GSEXPL = \(i ** d) =>
  case i of (Left ()) => [] ; (Right ()) => d BCPFalse :: d BCPTrue

public export
gsexptoGExpSl : SliceMorphism {a=GExpSlice} GSExp GSExptoGExpAlgSl
gsexptoGExpSl = gsexpCata GSExptoGExpAlg

public export
gsexptoGExp : GSExpX -> GExp
gsexptoGExp = gsexptoGExpSl GSEXP

public export
Show GSExpX where
  show = show . gsexptoGExp

--------------------------------------------------
--------------------------------------------------
---- Concepts as refinements of S-expressions ----
--------------------------------------------------
--------------------------------------------------

public export
data RAtom : Type where
  -- Objects representing ADTs
  RA_OBJ_0 : RAtom
  RA_OBJ_1 : RAtom
  RA_OBJ_C : RAtom
  RA_OBJ_P : RAtom
  RA_OBJ_EQ : RAtom

  -- Morphisms among ADTs
  RA_FROM_0 : RAtom
  RA_TO_1 : RAtom
  RA_INJ_L : RAtom
  RA_INJ_R : RAtom
  RA_CASE : RAtom
  RA_PROJ_L : RAtom
  RA_PROJ_R : RAtom
  RA_PAIR : RAtom
  RA_DISTRIB : RAtom

public export
RASize : Nat
RASize = 14

public export
RAFin : Type
RAFin = Fin RASize

public export
RADecoder : FinDecoder RAtom RASize
RADecoder FZ = RA_OBJ_0
RADecoder (FS FZ) = RA_OBJ_1
RADecoder (FS (FS FZ)) = RA_OBJ_C
RADecoder (FS (FS (FS FZ))) = RA_OBJ_P
RADecoder (FS (FS (FS (FS FZ)))) = RA_OBJ_EQ
RADecoder (FS (FS (FS (FS (FS FZ))))) = RA_FROM_0
RADecoder (FS (FS (FS (FS (FS (FS FZ)))))) = RA_TO_1
RADecoder (FS (FS (FS (FS (FS (FS (FS FZ))))))) = RA_INJ_L
RADecoder (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))) = RA_INJ_R
RADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ))))))))) = RA_CASE
RADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))) = RA_PROJ_L
RADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ))))))))))) = RA_PROJ_R
RADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ)))))))))))) =
  RA_PAIR
RADecoder (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS (FS FZ))))))))))))) =
  RA_DISTRIB

public export
RAEncoder : NatEncoder RADecoder
RAEncoder RA_OBJ_0 = (0 ** Refl ** Refl)
RAEncoder RA_OBJ_1 = (1 ** Refl ** Refl)
RAEncoder RA_OBJ_C = (2 ** Refl ** Refl)
RAEncoder RA_OBJ_P = (3 ** Refl ** Refl)
RAEncoder RA_OBJ_EQ = (4 ** Refl ** Refl)
RAEncoder RA_FROM_0 = (5 ** Refl ** Refl)
RAEncoder RA_TO_1 = (6 ** Refl ** Refl)
RAEncoder RA_INJ_L = (7 ** Refl ** Refl)
RAEncoder RA_INJ_R = (8 ** Refl ** Refl)
RAEncoder RA_CASE = (9 ** Refl ** Refl)
RAEncoder RA_PROJ_L = (10 ** Refl ** Refl)
RAEncoder RA_PROJ_R = (11 ** Refl ** Refl)
RAEncoder RA_PAIR = (12 ** Refl ** Refl)
RAEncoder RA_DISTRIB = (13 ** Refl ** Refl)

public export
RAtomEncoding : FinDecEncoding RAtom RASize
RAtomEncoding = NatDecEncoding RADecoder RAEncoder

public export
raToString : RAtom -> String
raToString RA_OBJ_0 = "RA_OBJ_0"
raToString RA_OBJ_1 = "RA_OBJ_1"
raToString RA_OBJ_C = "RA_OBJ_C"
raToString RA_OBJ_P = "RA_OBJ_P"
raToString RA_OBJ_EQ = "RA_OBJ_EQ"
raToString RA_FROM_0 = "RA_FROM_0"
raToString RA_TO_1 = "RA_TO_1"
raToString RA_INJ_L = "RA_INJ_L"
raToString RA_INJ_R = "RA_INJ_R"
raToString RA_CASE = "RA_CASE"
raToString RA_PROJ_L = "RA_PROJ_L"
raToString RA_PROJ_R = "RA_PROJ_R"
raToString RA_PAIR = "RA_PAIR"
raToString RA_DISTRIB = "RA_DISTRIB"

public export
Show RAtom where
  show a = raToString a

public export
Eq RAtom where
  (==) = fdeEq RAtomEncoding

public export
Ord RAtom where
  (<) = fdeLt RAtomEncoding

public export
DecEq RAtom where
  decEq = fdeDecEq RAtomEncoding

public export
FRExp : Type -> Type
FRExp = FrSExpM RAtom

public export
FRList : Type -> Type
FRList = FrSListM RAtom

public export
RExp : Type
RExp = SExp RAtom

public export
RList : Type
RList = SList RAtom

------------------------------------
------------------------------------
---- Quiver-functor experiments ----
------------------------------------
------------------------------------

public export
data RObjF : (obj, morph : Type) -> Type where
  RObj1 : RObjF obj morph
  RObjPr : (a, b : obj) -> RObjF obj morph
  RObjEq : (a, b : obj) -> (f, g : morph) -> RObjF obj morph

public export
data RObjTrF : (obj, morph : Type) -> Type -> Type where
  ROVar : var -> RObjTrF obj morph var
  ROCom : RObjF obj morph -> RObjTrF obj morph var

public export
data RMorphF : (obj, morph : Type) -> Type where
  RMorphId : obj -> RMorphF obj morph
  RMorphComp : (g, f : morph) -> RMorphF obj morph
  RMorphTo1 : obj -> RMorphF obj morph
  RMorphPairing : (f, g : morph) -> RMorphF obj morph
  RMorphProjL : (a, b : obj) -> RMorphF obj morph
  RMorphProjR : (a, b : obj) -> RMorphF obj morph
  RMorphEqInjDom : (a, b : obj) -> (f, g : morph) -> RMorphF obj morph
  RMorphEqInjCod : (a, b : obj) -> (f, g : morph) -> RMorphF obj morph

public export
data RMorphTrF : (obj, morph : Type) -> Type -> Type where
  RMVar : var -> RMorphTrF obj morph var
  RMCom : RMorphF obj morph -> RMorphTrF obj morph var

mutual
  public export
  data RObjFM : (ovar, mvar : Type) -> Type where
    InFRO :
      RObjTrF (RObjFM ovar mvar) (RMorphFM ovar mvar) ovar ->
      RObjFM ovar mvar

  public export
  data RMorphFM : (ovar, mvar : Type) -> Type where
    InFRM :
      RMorphTrF (RObjFM ovar mvar) (RMorphFM ovar mvar) mvar ->
      RMorphFM ovar mvar

public export
RObj : Type
RObj = RObjFM Void Void

public export
RMorph : Type
RMorph = RMorphFM Void Void

{-
public export
data RHasDomF : (obj, morph, hasDom, hasCod : Type) -> Type where
  RHDId : (a : obj) -> RHasDomF obj morph hasDom hasCod
  RHDComp : (g, f : morph) -> (a : obj) -> (ga : hasDom) -> (fa : hasCod) ->
    RHasDomF obj morph hasDom hasCod

  {-
public export
rdomF :
  (obj : Type) -> (morph : Type) ->
  (dom : morph -> obj) -> (cod : morph -> obj) ->
  RMorphF obj morph dom cod -> RObjTrF obj morph dom cod obj
rdomF obj morph dom cod (RMorphId a) = ROVar a
rdomF obj morph dom cod (RMorphComp g f prf) = ROVar $ dom f
rdomF obj morph dom cod (RMorphTo1 a) = ROVar a
rdomF obj morph dom cod (RMorphPairing f g prf) = ROVar $ dom f
rdomF obj morph dom cod (RMorphProjL a b) = ROCom $ RObjPr a b
rdomF obj morph dom cod (RMorphProjR a b) = ROCom $ RObjPr a b
rdomF obj morph dom cod (RMorphEqInjDom a b f g prf prf1 prf2 prf3) =
  ROCom $ RObjEq a b f g prf prf1 prf2 prf3
rdomF obj morph dom cod (RMorphEqInjCod a b f g prf prf1 prf2 prf3) =
  ROCom $ RObjEq a b f g prf prf1 prf2 prf3
  -}

public export
rhdomObjAlg : (obj, morph, hasDom, hasCod : Type) ->
  RHasDomF obj morph hasDom hasCod ->
  RObjTrF obj morph dom cod obj
rhdomObjAlg obj morph hasDom hasCod (RHDId a) = ROVar a
rhdomObjAlg obj morph hasDom hasCod (RHDComp g f a ga fa) = ?rhdomObjAlg_hole

public export
rhdomMorphAlg : (obj, morph, hasDom, hasCod : Type) ->
  RHasDomF obj morph hasDom hasCod ->
  RMorphF obj morph dom cod
rhdomMorphAlg obj morph hasDom hasCod (RHDId a) = RMorphId a
rhdomMorphAlg obj morph hasDom hasCod (RHDComp g f a ga fa) = ?rhdomMorphAlg_hole

public export
data RHasCodF : (obj, morph, hasDom, hasCod : Type) -> Type where
  RHCId : (a : obj) -> RHasCodF obj morph hasDom hasCod

{-
public export
rcodF :
  (obj : Type) -> (morph : Type) ->
  (dom : morph -> obj) -> (cod : morph -> obj) ->
  RMorphF obj morph dom cod -> RObjTrF obj morph dom cod obj
rcodF obj morph dom cod (RMorphId a) = ROVar a
rcodF obj morph dom cod (RMorphComp g f prf) = ROVar $ cod g
rcodF obj morph dom cod (RMorphTo1 a) = ROCom RObj1
rcodF obj morph dom cod (RMorphPairing f g prf) = ROCom $ RObjPr (cod f) (cod g)
rcodF obj morph dom cod (RMorphProjL a b) = ROVar a
rcodF obj morph dom cod (RMorphProjR a b) = ROVar b
rcodF obj morph dom cod (RMorphEqInjDom a b f g prf prf1 prf2 prf3) = ROVar a
rcodF obj morph dom cod (RMorphEqInjCod a b f g prf prf1 prf2 prf3) = ROVar b
-}

public export
rhcodObjAlg : (obj, morph, hasDom, hasCod : Type) ->
  RHasCodF obj morph hasDom hasCod ->
  RObjTrF obj morph dom cod obj
rhcodObjAlg obj morph hasDom hasCod (RHCId a) = ROVar a

public export
rhcodMorphAlg : (obj, morph, hasDom, hasCod : Type) ->
  RHasCodF obj morph hasDom hasCod ->
  RMorphF obj morph dom cod
rhcodMorphAlg obj morph hasDom hasCod (RHCId a) = RMorphId a

mutual
  public export
  data RObj : Type where
    InRO : RObjF RObj RMorph RHasDom RHasCod -> RObj

  public export
  data RMorph : Type where
    InRM : RMorphF RObj RMorph RHasDom RHasCod -> RMorph

  public export
  data RHasDom : Type where
    InRDV :
      (f : RMorphF RObj RMorph RHasDom RHasCod) -> (a : RObj) ->
      RHasDomF RObj RMorph RHasDom RHasCod ->
      RHasDom
    InRDC :
      (f : RMorphF RObj RMorph RHasDom RHasCod) ->
      (a : RObjF RObj RMorph RHasDom RHasCod) ->
      RHasDomF RObj RMorph RHasDom RHasCod ->
      RHasDom

  public export
  data RHasCod : Type where
    InRCV :
      (f : RMorphF RObj RMorph RHasDom RHasCod) -> (a : RObj) ->
      RHasCodF RObj RMorph RHasDom RHasCod ->
      RHasCod
    InRCC :
      (f : RMorphF RObj RMorph RHasDom RHasCod) ->
      (a : RObjF RObj RMorph RHasDom RHasCod) ->
      RHasCodF RObj RMorph RHasDom RHasCod ->
      RHasCod

{-
  public export
  rdom : RMorph -> RObj
  rdom (InRM f) with (rdomF RObj RMorph rdom rcod f)
    rdom (InRM f) | ROCom dom = InRO dom
    rdom (InRM f) | ROVar dom = dom

  public export
  rcod : RMorph -> RObj
  rcod (InRM f) with (rcodF RObj RMorph rdom rcod f)
    rcod (InRM f) | ROCom cod = InRO cod
    rcod (InRM f) | ROVar cod = cod
    -}
    -}

----------------------------
---- Generic generators ----
----------------------------

-- Given two types (for example, one of objects and one of morphisms),
-- generate a (new) type of objects.
public export
data FinLimSl : Type where
  FLSObj : FinLimSl
  FLSMorph : FinLimSl

public export
ObjGenSigDom : Type
ObjGenSigDom = FinLimSl

public export
ObjGenSigCod : Type
ObjGenSigCod = Unit

public export
ObjGenSig : Type
ObjGenSig = SlicePolyFunc ObjGenSigDom ObjGenSigCod

-- Given a type (of objects) and a type (of morphisms), generate a type
-- (of morphisms).
public export
MorphGenSigDom : Type
MorphGenSigDom = FinLimSl

public export
MorphGenSigCod : Type
MorphGenSigCod = Unit

public export
MorphGenSig : Type
MorphGenSig = SlicePolyFunc MorphGenSigDom MorphGenSigCod

---------------------------------
---- Example : finite limits ----
---------------------------------

-- An example object generator with a terminal object, pairwise products,
-- and equalizers.
public export
data FinLimObjPos : ObjGenSigCod -> Type where
  FLOP1 : FinLimObjPos ()
  FLOPProd : FinLimObjPos ()
  FLOPEq : FinLimObjPos ()

public export
FinLimObjDir : Sigma FinLimObjPos -> Type
-- The terminal object has no directions
FinLimObjDir (() ** FLOP1) = Void
-- A pairwise product has two directions (false is the left object;
-- true is the right object)
FinLimObjDir (() ** FLOPProd) = BoolCP
-- An equalizer has two directions, two objects and two morphisms:  we'll
-- use pairs, where the left pair is the pair of objects and the right pair
-- is the pair of morphisms.
FinLimObjDir (() ** FLOPEq) = ProductMonad BoolCP

public export
FinLimObjAssign : Sigma FinLimObjDir -> ObjGenSigDom
FinLimObjAssign ((() ** FLOP1) ** v) = void v
FinLimObjAssign ((() ** FLOPProd) ** od) =
  -- Both directions of a pairwise product are objects.
  FLSObj
FinLimObjAssign ((() ** FLOPEq) ** ((Left u), md)) =
  -- The left two directions of an equalizer are objects.
  case u of () => FLSObj
FinLimObjAssign ((() ** FLOPEq) ** ((Right u), md)) =
  -- The right two directions of an equalizer are morphisms.
  case u of () => FLSMorph

public export
FinLimObjF : ObjGenSig
FinLimObjF = (FinLimObjPos ** FinLimObjDir ** FinLimObjAssign)

-- The morphisms of this category have the following positions:
--  - The unique morphism to the terminal object
--  - One product introduction rule (pairing)
--  - Two product elimination rule (projections)
--  - Two equalizer elimination rules (the injection to the domain,
--    which forgets the equalization, and the injection to the codomain,
--    which equalization guarantees is equal to the composition of
--    either of the equalized morphisms after the injection to the
--    domain -- note that this means that the injection to the codomain
--    includes a guarantee of a particular equalization, which means that
--    it is _also_ an equalizer introduction rule)
public export
data FinLimMorph : Type where
  FLMId : FinLimMorph
  FLMCompose : FinLimMorph
  FLMTo1 : FinLimMorph
  FLMPairing : FinLimMorph
  FLMProjL : FinLimMorph
  FLMProjR : FinLimMorph
  FLMEqInjDom : FinLimMorph -- equalizer elimination (forgetful)
  FLMEqInjCod : FinLimMorph -- equalizer elimination _and_ introduction

public export
FinLimMorphPos : MorphGenSigCod -> Type
FinLimMorphPos () = FinLimMorph

public export
FinLimMorphDir : Sigma FinLimMorphPos -> Type
-- The id morphism to the terminal object has one direction:
-- an object, which is both its domain and its codomain
FinLimMorphDir (() ** FLMId) = Unit
-- The compose morphism has two directions:  the two morphisms
-- being composed (false is the left side, which is the following
-- morphism; true is the right side, which is the preceding morphism)
FinLimMorphDir (() ** FLMCompose) = BoolCP
-- The unique morphism to the terminal object has one direction:
-- an object, which is its domain
FinLimMorphDir (() ** FLMTo1) = Unit
-- The pairing morphism has two directions:  the two morphisms
-- which generate each side of the codomain
FinLimMorphDir (() ** FLMPairing) = BoolCP
-- The left projection has two directions:  both objects, which
-- are the left and right sides of the domain
FinLimMorphDir (() ** FLMProjL) = BoolCP
-- The right projection has two directions:  both objects, which
-- are the left and right sides of the domain
FinLimMorphDir (() ** FLMProjR) = BoolCP
-- The injection to the domain of an equalizer has one direction:
-- the object which is the equalizer itself
FinLimMorphDir (() ** FLMEqInjDom) = Unit
-- The injection to the domain of an equalizer has one direction:
-- the object which is the equalizer itself
FinLimMorphDir (() ** FLMEqInjCod) = Unit

public export
FinLimMorphAssign : Sigma FinLimMorphDir -> MorphGenSigDom
-- The id morphism's one direction is an object
FinLimMorphAssign ((() ** FLMId) ** d) = FLSObj
-- The compose morphism's two directions are both morphisms
FinLimMorphAssign ((() ** FLMCompose) ** d) = FLSMorph
-- The unique morphism to the terminal object's one direction is an object
FinLimMorphAssign ((() ** FLMTo1) ** ()) = FLSObj
-- Both of the pairing morphism's directions are morphisms
FinLimMorphAssign ((() ** FLMPairing) ** d) = FLSMorph
-- Both of the projection morphisms' directions are objects
FinLimMorphAssign ((() ** FLMProjL) ** d) = FLSObj
FinLimMorphAssign ((() ** FLMProjR) ** d) = FLSObj
-- The one direction of each morphism from an equalizer is an object
-- (the equalizer itself)
FinLimMorphAssign ((() ** FLMEqInjDom) ** ()) = FLSObj
FinLimMorphAssign ((() ** FLMEqInjCod) ** ()) = FLSObj

public export
FinLimMorphF : MorphGenSig
FinLimMorphF = (FinLimMorphPos ** FinLimMorphDir ** FinLimMorphAssign)

public export
FinCatSigGenPos : FinLimSl -> Type
FinCatSigGenPos FLSObj = FinLimObjPos ()
FinCatSigGenPos FLSMorph = FinLimMorphPos ()

public export
FinCatSigGenDir : Sigma {a=FinLimSl} FinCatSigGenPos -> Type
FinCatSigGenDir (FLSObj ** d) = FinLimObjDir (() ** d)
FinCatSigGenDir (FLSMorph ** d) = FinLimMorphDir (() ** d)

public export
FinCatSigGenAssign : Sigma FinCatSigGenDir -> FinLimSl
FinCatSigGenAssign ((FLSObj ** i) ** d) = FinLimObjAssign ((() ** i) ** d)
FinCatSigGenAssign ((FLSMorph ** i) ** d) = FinLimMorphAssign ((() ** i) ** d)

public export
FinCatSigGenF : SlicePolyEndoFunc FinLimSl
FinCatSigGenF = (FinCatSigGenPos ** FinCatSigGenDir ** FinCatSigGenAssign)

public export
FinCatSig : SliceObj FinLimSl
FinCatSig = SPFMu FinCatSigGenF

public export
FinCatObjSig : Type
FinCatObjSig = FinCatSig FLSObj

public export
FinCatMorphSig : Type
FinCatMorphSig = FinCatSig FLSMorph

-------------------------------
---- Second-order versions ----
-------------------------------

-- Slices of second-order finite-limit-category expressions.
public export
data FinLimSl2 : Type where
  FLS2f : FinLimSl -> FinLimSl2 -- first-order (unchecked) slices
  FLS2u : FinLimSl -> FinLimSl2 -- second-order (unchecked) slices

public export
FinLimCat2Pos : FinLimSl2 -> Type
FinLimCat2Pos (FLS2f sl) = FinCatSigGenPos sl
FinLimCat2Pos (FLS2u x) = ?FinLimCat2Pos_hole_1

public export
FinLimMorphParamDir : Type
FinLimMorphParamDir = (FinCatObjSig, FinCatObjSig)

public export
FinLimCheckableMorphDir : Sigma FinLimMorphPos -> Type
FinLimCheckableMorphDir i = Either FinLimMorphParamDir (FinLimMorphDir i)

public export
FinLimCheckableMorphAssign : Sigma FinLimCheckableMorphDir -> MorphGenSigDom
FinLimCheckableMorphAssign ((() ** i) ** (Left x)) = ?FinLimCheckableMorphAssign_hole_0
FinLimCheckableMorphAssign ((() ** i) ** (Right x)) = ?FinLimCheckableMorphAssign_hole_1

public export
FinLimCheckableMorphF : MorphGenSig
FinLimCheckableMorphF =
  (FinLimMorphPos ** FinLimCheckableMorphDir ** FinLimCheckableMorphAssign)

public export
FinCatSigAlg : SliceObj FinLimSl -> Type
FinCatSigAlg = SPFAlg FinCatSigGenF

public export
FinCatSigCheckSlice : SliceObj FinLimSl
FinCatSigCheckSlice FLSObj = Bool
FinCatSigCheckSlice FLSMorph = FinCatObjSig -> Bool

public export
FinCatSigCheckAlg : FinCatSigAlg FinCatSigCheckSlice
-- The expression consisting just of the representation of the terminal
-- object is always valid (and always represents the terminal object).
FinCatSigCheckAlg FLSObj (FLOP1 ** d) = True
-- An expression representing the product of two objects is valid if and
-- only if both of the expressions representing the subobjects are valid.
FinCatSigCheckAlg FLSObj (FLOPProd ** d) = d (Left ()) && d (Right ())
-- An expression representing an equalizer is valid if and only if:
--  - The expressions representing the two subobjects are valid
--  - The expressions representing the two morphisms are valid
--  - The two morphisms both have the first subobject as their domain
--    and the second subobject as their codomain
FinCatSigCheckAlg FLSObj (FLOPEq ** d) = ?FinCatSigCheckAlg_hole_prodr
-- An expression representing an identity morphism is valid if and
-- only if the object which represents both its domain and its codomain
-- is valid.
FinCatSigCheckAlg FLSMorph (FLMId ** d) = ?FinCatSigCheckAlg_hole_id
FinCatSigCheckAlg FLSMorph (FLMCompose ** d) = ?FinCatSigCheckAlg_hole_compose
FinCatSigCheckAlg FLSMorph (FLMTo1 ** d) = ?FinCatSigCheckAlg_hole_to1
FinCatSigCheckAlg FLSMorph (FLMPairing ** d) = ?FinCatSigCheckAlg_hole_mkpair
FinCatSigCheckAlg FLSMorph (FLMProjL ** d) = ?FinCatSigCheckAlg_hole_projl
FinCatSigCheckAlg FLSMorph (FLMProjR ** d) = ?FinCatSigCheckAlg_hole_projr
FinCatSigCheckAlg FLSMorph (FLMEqInjDom ** d) = ?FinCatSigCheckAlg_hole_injd
FinCatSigCheckAlg FLSMorph (FLMEqInjCod ** d) = ?FinCatSigCheckAlg_hole_injc

public export
finCatSigCheck : SliceMorphism FinCatSig FinCatSigCheckSlice
finCatSigCheck = spfCata FinCatSigCheckAlg

public export
finCatSigCheckObj : FinCatObjSig -> Bool
finCatSigCheckObj = finCatSigCheck FLSObj

public export
finCatSigCheckMorph : FinCatObjSig -> FinCatMorphSig -> Bool
finCatSigCheckMorph = flip $ finCatSigCheck FLSMorph

-------------------------------------------
-------------------------------------------
---- Geb as double category (or more?) ----
-------------------------------------------
-------------------------------------------

public export
BoolF : Type -> Type
BoolF = const Bool

----------------------------
----------------------------
---- Product categories ----
----------------------------
----------------------------

-- Given an object of objects of a category, produce the object of
-- objects of its product category (with itself).
public export
PCatObj : PolyFunc
PCatObj = PFHomArena BoolCP

public export
PCatMorphFPos : Type
PCatMorphFPos = Unit

public export
PCatMorph : PolyFunc
PCatMorph = PFHomArena BoolCP

public export
PCatDom : (obj : Type) -> (morph : Type) ->
  (dom : morph -> obj) -> (cod : morph -> obj) ->
  InterpPolyFunc PCatMorph morph -> InterpPolyFunc PCatObj obj
PCatDom obj morph dom cod (() ** x) = (() ** dom . x)

public export
PCatCod : (obj : Type) -> (morph : Type) ->
  (dom : morph -> obj) -> (cod : morph -> obj) ->
  InterpPolyFunc PCatMorph morph -> InterpPolyFunc PCatObj obj
PCatCod obj morph dom cod (() ** x) = (() ** cod . x)

public export
PCatSig : (obj : Type) -> (morph : Type) ->
  (dom : morph -> obj) -> (cod : morph -> obj) ->
  InterpPolyFunc PCatMorph morph ->
  (InterpPolyFunc PCatObj obj, InterpPolyFunc PCatObj obj)
PCatSig obj morph dom cod x =
  (PCatDom obj morph dom cod x, PCatCod obj morph dom cod x)
