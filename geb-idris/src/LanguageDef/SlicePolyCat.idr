module LanguageDef.SlicePolyCat

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.PolyCat
import public LanguageDef.SliceFuncCat
import public LanguageDef.InternalCat
import public LanguageDef.IntArena
import public LanguageDef.IntUFamCat
import public LanguageDef.IntUCofamCat
import public LanguageDef.IntEFamCat
import public LanguageDef.IntECofamCat

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

--------------------------------------------------
--------------------------------------------------
--- Identity endofunctor category of elements ----
--------------------------------------------------
--------------------------------------------------

-- A type together with an element of that type.
-- This is an object of the category of elements of the identity
-- endofunctor on `Type`.
public export
TyElObj : Type
TyElObj = Sigma {a=Type} Prelude.id

public export
TyElMor : IntMorSig TyElObj
TyElMor e e' =
  Sigma {a=(fst e -> fst e')} $
    flip (WEqualizes {a=(fst e)} {b=(fst e')} (\_ => snd e')) (snd e)

------------------------------------------------------
------------------------------------------------------
---- Polynomial functors between slice categories ----
------------------------------------------------------
------------------------------------------------------

-------------------------------------------
-------------------------------------------
---- General slice polynomial functors ----
-------------------------------------------
-------------------------------------------

--------------------
---- Definition ----
--------------------

-- At https://ncatlab.org/nlab/show/parametric+right+adjoint#generic_morphisms
-- in the proposition about the "especially nice form" of PRA functors between
-- presheaf categories, this `SPFdirType` corresponds to what is called the
-- functor `E_T`, while the `SliceObj cod` which it depends on is the object
-- `T1`.
--
-- Note that this is equivalent to `SliceObj (Sigma {a=cod} pos, dom)`.
public export
0 SPFdirType : (0 dom, cod : Type) -> (0 _ : SliceObj cod) -> Type
SPFdirType dom cod pos = (ec : cod) -> pos ec -> SliceObj dom

-- A polynomial functor on slice categories may be described as a parametric
-- right adjoint whose right-adjoint component is a form of `SliceSigmaPiFR`
-- (which has the left adjoint `SliceSigmaPiFL`) and whose following
-- dependent-sum component is a form of `SliceSigmaF`.  `dir and `pos`, the
-- parameters to those two functors,  must be such that the functors can be
-- composed.
--
-- See for example:
--  - https://ncatlab.org/nlab/show/parametric+right+adjoint
--
-- (Recall that `SliceSigmaPiFR` is a base change followed by a `SlicePiF`,
-- while `SliceSigmaPiFL` is a base change followed by a `SliceSigmaF`.)

-- This is the dependent (slice) analogue of an arena in `Type` (where
-- the latter is a `PolyFunc`, AKA `MLArena`).
public export
record SPFData (dom, cod : Type) where
  constructor SPFD
  spfdPos : SliceObj cod
  spfdDir : SPFdirType dom cod spfdPos

-- Category-theory-style `spfdPos`.
public export
spfdCPos : {dom, cod : Type} -> SPFData dom cod -> CSliceObj cod
spfdCPos {dom} {cod} spfd = CSliceFromSlice {c=cod} (spfdPos spfd)

-- Category-theory-style slice object in the slice category of
-- `Type` over `spfdPos spfd`.
public export
spfdCPosSl : {dom, cod : Type} -> SPFData dom cod -> Type
spfdCPosSl {dom} {cod} spfd = CSliceObjOfSliceCat {c=cod} (spfdCPos spfd)

-- The total directions of a slice polynomial functor at a given
-- point in the domain and codomain.
public export
SPFDtot : {dom, cod : Type} -> SPFData dom cod -> dom -> cod -> Type
SPFDtot {dom} {cod} spfd ed ec = (i : spfdPos spfd ec ** spfdDir spfd ec i ed)

-- The total directions of a slice polynomial functor at a given
-- point in the domain.
public export
SPFDtotDom : {dom, cod : Type} -> SPFData dom cod -> dom -> Type
SPFDtotDom {dom} {cod} spfd ed = (ec : cod ** SPFDtot {dom} {cod} spfd ed ec)

-- The total directions of a slice polynomial functor at a given
-- point in the codomain.
public export
SPFDtotCod : {dom, cod : Type} -> SPFData dom cod -> cod -> Type
SPFDtotCod {dom} {cod} spfd ec = (ed : dom ** SPFDtot {dom} {cod} spfd ed ec)

-- The internal (that is, as a slice endofunctor, i.e. an endofunctor
-- in the "object language") covariant representable functor on the domain of
-- a slice polynomial functor represented by its object of directions
-- at a given position.
public export
SPFDintCovarDirRep : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (ec : cod) -> spfdPos spfd ec -> SliceEndofunctor dom
SPFDintCovarDirRep {dom} {cod} spfd ec ep =
  SliceHom {a=dom} (spfdDir spfd ec ep)

public export
SPFDintCovarDirRepMap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (ec : cod) -> (ep : spfdPos spfd ec) ->
  SliceFMap (SPFDintCovarDirRep {dom} {cod} spfd ec ep)
SPFDintCovarDirRepMap {dom} {cod} spfd ec ep x y mab ed = (.) (mab ed)

-- The external (that is, as a copresheaf) covariant representable functor
-- on the domain of a slice polynomial functor represented by its object
-- of directions at a given position.
public export
SPFDextCovarDirRep : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (ec : cod) -> spfdPos spfd ec -> SliceObj dom -> Type
SPFDextCovarDirRep {dom} {cod} spfd ec ep sd =
  -- Equivalent to:
  --  SliceMorphism {a=dom} (spfdDir spfd ec ep) sd
  Pi {a=dom} (SPFDintCovarDirRep {dom} {cod} spfd ec ep sd)

public export
SPFDextCovarDirRepMap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (ec : cod) -> (ep : spfdPos spfd ec) ->
  (0 a, b : SliceObj dom) -> SliceMorphism {a=dom} a b ->
  SPFDextCovarDirRep {dom} {cod} spfd ec ep a ->
  SPFDextCovarDirRep {dom} {cod} spfd ec ep b
SPFDextCovarDirRepMap {dom} {cod} spfd ec ep a b mab dm ed = mab ed . dm ed

-- The base object of the intermediate slice category in the factorization
-- of a (slice) polynomial functor as a parametric right adjoint.
-- This is `T1` in the ncat page on parametric right adjoints.
public export
SPFDbase : {dom, cod : Type} -> SPFData dom cod -> Type
SPFDbase {dom} {cod} = Sigma {a=cod} . spfdPos

public export
SPFDbaseSl : {dom, cod : Type} -> SPFData dom cod -> Type
SPFDbaseSl {dom} {cod} = SliceObj . SPFDbase {dom} {cod}

-- This is the contravariant representable functor on `SliceObj cod`
-- represented by `spfdPos spfd`.
public export
SPFDposContraRep : {dom, cod : Type} -> SPFData dom cod -> SliceObj cod -> Type
SPFDposContraRep {dom} {cod} spfd = flip (SliceMorphism {a=cod}) (spfdPos spfd)

public export
SPFDposContraRepContramap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (x, y : SliceObj cod) ->
  SliceMorphism {a=cod} y x ->
  SPFDposContraRep {dom} {cod} spfd x ->
  SPFDposContraRep {dom} {cod} spfd y
SPFDposContraRepContramap {dom} {cod} spfd x y =
  flip $ sliceComp {x=y} {y=x} {z=(spfdPos spfd)}

public export
SPFDcsPos : {dom, cod : Type} -> SPFData dom cod -> Type
SPFDcsPos {dom} {cod} spfd = CSliceOfSlice {c=cod} (spfdPos spfd)

-- Here we define translations amongst `SPFDbaseSl` (a dependent-type-style
-- slice of `SPFDbase spfd`), `SPFDcsPos` (a combination of dependent-type
-- style and category-theory style, comprising a slice of the codomain
-- together with a slice morphism from that slice to `spfdPos spfd`), and
-- `spfdCPosSl` (a category-theory-style slice object in the slice category of
-- `Type` over `spfdPos spfd`.

-- Translate from a category-theory-style slice of `spfdPos spfd` --
-- which is to say, an object of `SliceObj cod` together with a morphism
-- from that object to `spfdPos spfd` -- to a dependent-type-style slice
-- of `SPFDbase spfd`.
public export
SPFDposCSlToBaseSl : {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  SPFDcsPos {dom} {cod} spfd ->
  SPFDbaseSl {dom} {cod} spfd
SPFDposCSlToBaseSl {dom} {cod} {spfd} =
  CSliceOfSliceToSliceOfSigma {c=cod} {sl=(spfdPos spfd)}

public export
SPFDbaseSlToPosCSl : {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  SPFDbaseSl {dom} {cod} spfd ->
  SPFDcsPos {dom} {cod} spfd
SPFDbaseSlToPosCSl {spfd} =
  SliceOfSigmaToCSliceOfSlice {c=cod} {sl=(spfdPos spfd)}

public export
SPFDcPosSlToBaseSl : {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  spfdCPosSl spfd -> SPFDbaseSl {dom} {cod} spfd
SPFDcPosSlToBaseSl {dom} {cod} {spfd} =
  CSliceOfSliceCatToSliceOverSigma {c=cod} {x=(spfdPos spfd)}

-- Translate from a dependent-type-style slice of `SPFDbase spfd` to a
-- category-theory-style slice of `spfdPos spfd`.
public export
SPFDbaseSlToCPosSl : {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  SPFDbaseSl {dom} {cod} spfd -> spfdCPosSl spfd
SPFDbaseSlToCPosSl = SliceObjOverSigmaToObjOfSliceCat

public export
SPFDcPosSlToPosCSl : {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  spfdCPosSl spfd -> SPFDcsPos {dom} {cod} spfd
SPFDcPosSlToPosCSl = CSliceOfSliceCatToCSliceOfSlice

public export
SPFDposCSlToCPosSl : {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  SPFDcsPos {dom} {cod} spfd -> spfdCPosSl spfd
SPFDposCSlToCPosSl = CSliceOfSliceToCSliceOfSliceCat

-- The right-adjoint factor of a polynomial functor expressed as
-- a parametric right adjoint.
public export
SPFDradjFact : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceFunctor dom (SPFDbase {dom} {cod} spfd)
SPFDradjFact {dom} {cod} spfd sd ecp =
  SPFDextCovarDirRep spfd (fst ecp) (snd ecp) sd

public export
SPFDradjFactMap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceFMap (SPFDradjFact {dom} {cod} spfd)
SPFDradjFactMap {dom} {cod} spfd x y m ecp =
  SPFDextCovarDirRepMap spfd (fst ecp) (snd ecp) x y m

-- We show that the right-adjoint factor of a polynomial functor
-- expressed as a parametric right adjoint is equivalent to `SliceSigmaPiFR`
-- with particular parameters.
public export
SPFDtoSSPR : {0 dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceObj (dom, SPFDbase {dom} {cod} spfd)
SPFDtoSSPR {dom} {cod} spfd edcp =
  spfdDir spfd (fst $ snd edcp) (snd $ snd edcp) (fst edcp)

public export
SPFDradjFactToSSPR : {0 dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceNatTrans {x=dom} {y=(SPFDbase spfd)}
    (SPFDradjFact {dom} {cod} spfd)
    (SliceSigmaPiFR {c=dom} {e=(SPFDbase spfd)} $ SPFDtoSSPR spfd)
SPFDradjFactToSSPR {dom} {cod} (SPFD pos dir) sd (ec ** ep) radj (ed ** dd) =
  radj ed dd

public export
SPFDradjFactFromSSPR : {0 dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceNatTrans {x=dom} {y=(SPFDbase spfd)}
    (SliceSigmaPiFR {c=dom} {e=(SPFDbase spfd)} $ SPFDtoSSPR spfd)
    (SPFDradjFact {dom} {cod} spfd)
SPFDradjFactFromSSPR {dom} {cod} (SPFD pos dir) sd (ec ** ep) radj ed dd =
  radj (ed ** dd)

-- Fibrate the right-adjoint factor of a polynomial functor by a
-- dependent-type-style slice object over the position object.
public export
SPFDradjFactSl : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (sl : SliceObj $ SPFDbase spfd) ->
  SliceFunctor dom (Sigma {a=(SPFDbase spfd)} sl)
SPFDradjFactSl {dom} {cod} spfd sl = SliceBCF sl . SPFDradjFact {dom} {cod} spfd

-- Fibrate the right-adjoint factor of a polynomial functor by a
-- category-theory-style slice object over the position object.
public export
SPFDRadjFactCSl : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (sl : SPFDcsPos spfd) ->
  SliceFunctor
    dom
    (Sigma {a=(SPFDbase spfd)} $ SPFDposCSlToBaseSl {spfd} sl)
SPFDRadjFactCSl {dom} {cod} spfd sl =
  SPFDradjFactSl {dom} {cod} spfd (SPFDposCSlToBaseSl sl)

-- The left adjoint of the right-adjoint factor of a polynomial functor.
public export
SPFDladjFact : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceFunctor (SPFDbase {dom} {cod} spfd) dom
SPFDladjFact {dom} {cod} spfd =
  SliceSigmaPiFL {c=dom} {e=(SPFDbase spfd)} $ SPFDtoSSPR spfd

public export
SPFDladjFactMap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceFMap (SPFDladjFact {dom} {cod} spfd)
SPFDladjFactMap {dom} {cod} spfd =
  ssplMap {c=dom} {e=(SPFDbase {dom} {cod} spfd)} $ SPFDtoSSPR spfd

-- The dependent-sum factor of a polynomial functor expressed as
-- a codomain-parameterized copresheaf on slice objects over positions.
public export
SPFDsigmaDep : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (ec : cod) -> SliceObj (spfdPos spfd ec) -> Type
SPFDsigmaDep {dom} {cod} spfd ec = Sigma {a=(spfdPos spfd ec)}

public export
SPFDsigmaDepMap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (ec : cod) -> {0 a, b : SliceObj $ spfdPos spfd ec} ->
  SliceMorphism {a=(spfdPos spfd ec)} a b ->
  SPFDsigmaDep {dom} {cod} spfd ec a ->
  SPFDsigmaDep {dom} {cod} spfd ec b
SPFDsigmaDepMap {dom} {cod} spfd ec {a} {b} = dpMapSnd {p=a} {q=b}

-- The dependent-sum factor of a polynomial functor.
public export
SPFDsigmaFact : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceFunctor (SPFDbase {dom} {cod} spfd) cod
SPFDsigmaFact {dom} {cod} spfd bsl ec =
  -- This is equivalent to:
  --  SliceSigmaF {c=cod} (spfdPos spfd) bsl ec
  SPFDsigmaDep {dom} {cod} spfd ec (curry bsl ec)

public export
SPFDsigmaMap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceFMap (SPFDsigmaFact {dom} {cod} spfd)
SPFDsigmaMap {dom} {cod} spfd a b m ec =
  -- This is equivalent to:
  --  ssMap {c=cod} {sl=(spfdPos spfd)} a b m ec
  SPFDsigmaDepMap {dom} {cod} spfd ec {a=(curry a ec)} {b=(curry b ec)}
    $ \ep => m (ec ** ep)

-- We show explicitly that `SPFDsigmaFact` is equivalent to
-- `SliceSigmaF` (this is trivial).
public export
SPFDsigmaAsSS : {0 dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceNatTrans {x=(SPFDbase spfd)} {y=cod}
    (SPFDsigmaFact {dom} {cod} spfd)
    (SliceSigmaF {c=cod} $ spfdPos spfd)
SPFDsigmaAsSS {dom} {cod} (SPFD pos dir) scp ec = id

public export
SSasSPFDsigma : {0 cod : Type} -> (ss : SliceObj cod) ->
  SliceNatTrans {x=(Sigma {a=cod} ss)} {y=cod}
    (SliceSigmaF {c=cod} ss)
    (SPFDsigmaFact {dom=(Sigma {a=cod} ss)} {cod}
     $ SPFD ss $ \ec, ess, ecs => ss ec)
SSasSPFDsigma {cod} ss scs ec = id

-- The dependent-sum factor of a polynomial functor is itself a _left_
-- adjoint, to a base change.  This is that base change, the right
-- adjoint to `SPFDsigmaFact`.
public export
SPFDdepSumFactR : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceFunctor cod (SPFDbase {dom} {cod} spfd)
SPFDdepSumFactR {dom} {cod} spfd = SliceBCF {c=cod} (spfdPos spfd)

public export
SPFDdepSumFactRmap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceFMap (SPFDdepSumFactR {dom} {cod} spfd)
SPFDdepSumFactRmap {dom} {cod} spfd = sbcMap {c=cod} {sl=(spfdPos spfd)}

-- The composition of the dependent-sum factor after the right-adjoint
-- factor yields the interpretation of a polynomial functor (explicitly
-- as a parametric right adjoint).
--
-- We call the interpretation of an `SPFData` as a slice polynomial functor
-- `SPFDmultiR` because, as we shall see below, the slice polynomial functor may
-- be viewed as a right multi-adjoint.  Hence the `SPFData` may be viewed
-- as defining a multi-adjunction.
--
-- Note that this constitutes the composition of a _left_ adjoint after
-- a _right_ adjoint, so while it is comprised of adjoints, they go in
-- opposite directions, so the composite is not (necessarily) itself an
-- adjoint.  (But it is a parametric right adjoint, hence a multi-adjoint.)
public export
SPFDmultiR : {dom, cod : Type} -> SPFData dom cod -> SliceFunctor dom cod
SPFDmultiR {dom} {cod} spfd = SPFDsigmaFact spfd . SPFDradjFact spfd

-- `SPFDmultiR` is the "standard" form of interpretation of a dependent (slice)
-- polynomial functor (W-type), so we give it an alias which reflects that.
public export
InterpSPFData : {dom, cod : Type} -> SPFData dom cod -> SliceFunctor dom cod
InterpSPFData = SPFDmultiR

-- The signature of the first component of a (slice) morphism into an
-- `SPFDmultiR {dom} {cod} spfd a` (for some `dom, cod : Type` and
-- `a : SliceObj dom`) is independent of the codomain of the morphism as
-- a whole; it depends only on morphism's domain -- and only on the _positions_
-- of the functor, not its directions, meaning the it is even independent of
-- the domain of the _functor_ (which is a (slice) category), not only of the
-- codomain of the morphism (which, like the domain of the morphism, is an
-- object in the category which comprises the codomain of the functor).
public export
SPFDmultiR1 : {cod : Type} -> (pos : SliceObj cod) -> (b : SliceObj cod) -> Type
SPFDmultiR1 {cod} pos b = SliceMorphism {a=cod} b pos

-- Given a first component of a morphism into an `SPFDmultiR spfd`, this
-- is the signature required to specify the second component.
-- Note that for a fixed `SPFDmultiR1`, this is a presheaf on `SliceObj dom`.
public export
SPFDmultiR2 :
  {dom, cod : Type} -> (spfd : SPFData dom cod) -> {b : SliceObj cod} ->
  (m1 : SPFDmultiR1 {cod} (spfdPos spfd) b) -> (a : SliceObj dom) -> Type
SPFDmultiR2 {dom} {cod} spfd {b} m1 a =
  (ec : cod) -> (eb : b ec) ->
  SliceMorphism {a=dom} (spfdDir spfd ec $ m1 ec eb) a

-- The two components above together constitute a way of specifying a
-- morphism `b -> SPFDmultiR a` into an `SPFDmultiR`.
public export
SPFDmultiR12 :
  {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (b : SliceObj cod) -> (a : SliceObj dom) -> Type
SPFDmultiR12 {dom} {cod} spfd b =
  Sigma {a=(SPFDmultiR1 {cod} (spfdPos spfd) b)}
  . flip (SPFDmultiR2 {dom} {cod} {b} spfd)

-- We show that separate definitions of `SPFDmultiR1` and `SPFDmultiR2`
-- are equivalent to the definition of a morphism `b -> SPFDmultiR a`.
public export
SPFDmultiR1from12 :
  {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  {b : SliceObj cod} -> {a : SliceObj dom} ->
  SPFDmultiR12 {dom} {cod} spfd b a ->
  (ec : cod) -> (eb : b ec) -> spfdPos spfd ec
SPFDmultiR1from12 {dom} {cod} {spfd} {b} {a} = DPair.fst

public export
SPFDmultiR2from12 :
  {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  {b : SliceObj cod} -> {a : SliceObj dom} ->
  (m12 : SPFDmultiR12 {dom} {cod} spfd b a) ->
  (ec : cod) -> (eb : b ec) -> (ed : dom) ->
  spfdDir spfd ec (SPFDmultiR1from12 {spfd} m12 ec eb) ed -> a ed
SPFDmultiR2from12 {dom} {cod} {spfd} {b} {a} = DPair.snd

public export
SPFDmultiRfrom12 :
  {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  {b : SliceObj cod} -> {a : SliceObj dom} ->
  SPFDmultiR12 {dom} {cod} spfd b a ->
  SliceMorphism {a=cod} b (SPFDmultiR spfd a)
SPFDmultiRfrom12 {dom} {cod} {spfd} {b} {a} m12 ec eb =
  (SPFDmultiR1from12 {dom} {cod} {spfd} {b} {a} m12 ec eb **
   SPFDmultiR2from12 {dom} {cod} {spfd} {b} {a} m12 ec eb)

public export
SPFDmultiRto1 :
  {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  {b : SliceObj cod} -> {a : SliceObj dom} ->
  SliceMorphism {a=cod} b (SPFDmultiR spfd a) ->
  SPFDmultiR1 {cod} (spfdPos spfd) b
SPFDmultiRto1 {dom} {cod} {spfd} {b} {a} m ec eb = fst (m ec eb)

public export
SPFDmultiRto2 :
  {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  {b : SliceObj cod} -> {a : SliceObj dom} ->
  (m : SliceMorphism {a=cod} b (SPFDmultiR spfd a)) ->
  SPFDmultiR2 {dom} {cod} spfd {b}
    (SPFDmultiRto1 {dom} {cod} {spfd} {b} {a} m) a
SPFDmultiRto2 {dom} {cod} {spfd} {b} {a} m ec eb = snd (m ec eb)

public export
SPFDmultiRto12 :
  {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  {b : SliceObj cod} -> {a : SliceObj dom} ->
  SliceMorphism {a=cod} b (SPFDmultiR spfd a) ->
  SPFDmultiR12 {dom} {cod} spfd b a
SPFDmultiRto12 {dom} {cod} {spfd} {b} {a} m =
  (SPFDmultiRto1 {dom} {cod} {spfd} {b} {a} m **
   SPFDmultiRto2 {dom} {cod} {spfd} {b} {a} m)

public export
SPFDmultiRfrom12idL : FunExt ->
  {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  {b : SliceObj cod} -> {a : SliceObj dom} ->
  (m : SliceMorphism {a=cod} b (SPFDmultiR spfd a)) ->
  SPFDmultiRfrom12 {dom} {cod} {spfd} (SPFDmultiRto12 {dom} {cod} {spfd} m) = m
SPFDmultiRfrom12idL fext {dom} {cod} {spfd} {b} {a} m =
  funExt $ \ec => funExt $ \eb => sym dpEqPat

public export
SPFDmultiRfrom12idR : FunExt ->
  {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  {b : SliceObj cod} -> {a : SliceObj dom} ->
  (m : SPFDmultiR12 spfd b a) ->
  SPFDmultiRto12 {dom} {cod} {spfd} (SPFDmultiRfrom12 {dom} {cod} {spfd} m) = m
SPFDmultiRfrom12idR fext {dom} {cod} {spfd} {b} {a} (m1 ** m2) =
  dpEq12
    (funExt $ \ec => funExt $ \eb => Refl)
    (funExt $ \ec => funExt $ \ep => funExt $ \ed => funExt $ \dd => Refl)

public export
SPFDmultiRmap : {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> SliceFMap (SPFDmultiR {dom} {cod} spfd)
SPFDmultiRmap {dom} {cod} spfd a b =
  SPFDsigmaMap spfd (SPFDradjFact spfd a) (SPFDradjFact spfd b)
  . SPFDradjFactMap spfd a b

public export
InterpSPFDataMap : {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> SliceFMap (InterpSPFData {dom} {cod} spfd)
InterpSPFDataMap = SPFDmultiRmap

-- Utility functions for composing the equivalence between `Type` and
-- `SliceObj Unit` with interpretations of `SPFData`.

public export
InterpSPFDataUdom : {cod : Type} -> SPFData Unit cod -> Type -> SliceObj cod
InterpSPFDataUdom {cod} spfd x = InterpSPFData {dom=Unit} {cod} spfd (\_ => x)

public export
InterpSPFDataUdomMap : {cod : Type} -> (spfd : SPFData Unit cod) ->
  (x, y : Type) -> (x -> y) ->
  SliceMorphism {a=cod}
    (InterpSPFDataUdom {cod} spfd x)
    (InterpSPFDataUdom {cod} spfd y)
InterpSPFDataUdomMap {cod} spfd x y f =
  InterpSPFDataMap {dom=Unit} {cod} spfd (\_ => x) (\_ => y) (\_ => f)

public export
InterpSPFDataUcod : {dom : Type} -> SPFData dom Unit -> SliceObj dom -> Type
InterpSPFDataUcod {dom} spfd x = InterpSPFData {dom} {cod=Unit} spfd x ()

public export
InterpSPFDataUcodMap : {dom : Type} -> (spfd : SPFData dom Unit) ->
  (x, y : SliceObj dom) -> SliceMorphism {a=dom} x y ->
  InterpSPFDataUcod {dom} spfd x -> InterpSPFDataUcod {dom} spfd y
InterpSPFDataUcodMap {dom} spfd x y f =
  InterpSPFDataMap {dom} {cod=Unit} spfd x y f ()

public export
InterpSPFDataU : SPFData Unit Unit -> Type -> Type
InterpSPFDataU spfd x = InterpSPFData {dom=Unit} {cod=Unit} spfd (\_ => x) ()

public export
InterpSPFDataUMap : (spfd : SPFData Unit Unit) ->
  (x, y : Type) -> (x -> y) -> InterpSPFDataU spfd x -> InterpSPFDataU spfd y
InterpSPFDataUMap spfd x y f =
  InterpSPFDataMap {dom=Unit} {cod=Unit} spfd (\_ => x) (\_ => y) (\_ => f) ()

public export
InterpSPFDataMapId : FunExt -> {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> (x : SliceObj dom) ->
    (InterpSPFDataMap {dom} {cod} spfd x x $ SliceId dom x) =
    (SliceId cod $ InterpSPFData {dom} {cod} spfd x)
InterpSPFDataMapId fext {dom} {cod} spfd x =
  funExt $ \ec => funExt $ \(ep ** dm) => dpEq12 Refl $ funExt $ \ed => Refl

public export
SPFDmultiRflip : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (ec : cod) -> SliceObj dom -> Type
SPFDmultiRflip {dom} {cod} spfd ec sd =
  SPFDmultiR {dom} {cod} spfd sd ec

public export
SPFDmultiRflipMap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (ec : cod) -> {a, b : SliceObj dom} ->
  SliceMorphism {a=dom} a b ->
  SPFDmultiR {dom} {cod} spfd a ec ->
  SPFDmultiR {dom} {cod} spfd b ec
SPFDmultiRflipMap {dom} {cod} spfd ec {a} {b} mab =
  SPFDmultiRmap {dom} {cod} spfd a b mab ec

-- We can define a functor in the opposite direction to `SPFDmultiR` by
-- composition of the adjoints of its factors.
--
-- Like `SPFDmultiR` itself, this functor is the composition of a left adjoint
-- after a right adjoint.
--
-- Note that this functor is comprised of base changes
-- (`SliceBCF`/`BaseChangeF`) and dependent sums (`SliceSigmaF`)
-- only (in particular, `SlicePiF` is not involved).
public export
SPFDL : {dom, cod : Type} -> SPFData dom cod -> SliceFunctor cod dom
SPFDL {dom} {cod} spfd = SPFDladjFact spfd . SPFDdepSumFactR spfd

public export
SPFDLmap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceFMap (SPFDL spfd)
SPFDLmap {dom} {cod} spfd x y =
  SPFDladjFactMap spfd (SPFDdepSumFactR spfd x) (SPFDdepSumFactR spfd y)
  . SPFDdepSumFactRmap spfd x y

-- For a multi-adjunction induced by a polynomial functor,
-- `SPFDposContraRep` is the functor is referred to as `I` in theorem 2.4 of
-- https://ncatlab.org/nlab/show/multi-adjoint#definition (for the
-- multi-adjunction defined by a slice polynomial functor).  It is
-- referred to as the "index" (in particular, it indexes the
-- family of units of the multi-adjunction) part of a left multi-adjoint
-- (the functor part is `SPFDmultiL`).  Hence we give it an alias reflecting
-- its role as an index.
--
-- This functor is simply the contravariant representable functor of the
-- position, so the index of a unit for a particular slice of the codomain
-- is a (slice) morphism from that slice to the slice object of positions.
public export
SPFDmultiIdx : {dom, cod : Type} -> SPFData dom cod -> SliceObj cod -> Type
SPFDmultiIdx = SPFDposContraRep

public export
SPFDmultiIdxContramap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (x, y : SliceObj cod) ->
  SliceMorphism {a=cod} y x ->
  SPFDmultiIdx {dom} {cod} spfd x ->
  SPFDmultiIdx {dom} {cod} spfd y
SPFDmultiIdxContramap = SPFDposContraRepContramap

-- Convert the index of one of the units of the multi-adjoint defined by
-- a polynomial functor from category-theoretic style
-- (`SPFDmultiIdx`) to dependent-type style (`SliceObj SPFDbase`).
--
-- Note that this has a signature like that of `SPFDdepSumFactR` (the right
-- adjoint of the dependent-sum component of the polynomial functor)
-- but with the addition of the `i : SPFDmultiIdx spfd b`
-- component.  `SPFDdepSumFactR` is the depedent-sum factor of the polynomial
-- functor, so this may be viewed as a fibered/dependent version of the
-- dependent-sum factor.
public export
SPFDunitIdxToSl : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (b : SliceObj cod) -> (i : SPFDmultiIdx spfd b) ->
  SliceObj (SPFDbase {dom} {cod} spfd)
SPFDunitIdxToSl {dom} {cod} spfd b i =
  SPFDposCSlToBaseSl {dom} {cod} {spfd} (b ** i)

-- This is the left multi-adjoint of `SPFDmultiR`.  It is the functor which
-- is called `L` both in the "in particular has a left-multi-adjoint"
-- "Property" under
--  https://ncatlab.org/nlab/show/parametric+right+adjoint#properties
-- and in the definition of a multi-adjunction in Definition 2.1 at
-- https://ncatlab.org/nlab/show/multi-adjoint#definition
-- (and also in Theorem 2.4 in that same section).  (The index component
-- of the left multi-adjoint, called `I` on the ncatlab page, is here
-- called `SPFDmultiIdx`.)
--
-- Note that this is the composition of the left adjoint of the right-adjoint
-- factor of a polynomial functor after the index functor of the family of
-- units, which may be viewed as a fibered/dependent version of the
-- dependent-sum factor of the polynomial functor.
public export
SPFDmultiL : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (b : SliceObj cod) -> (i : SPFDmultiIdx spfd b) ->
  SliceObj dom
SPFDmultiL {dom} {cod} spfd b i =
  SPFDladjFact {dom} {cod} spfd $ SPFDunitIdxToSl {dom} {cod} spfd b i

public export
SPFDmultiLmap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (b : SliceObj cod) -> (i : SPFDmultiIdx spfd b) ->
  (b' : SliceObj cod) -> (i' : SPFDmultiIdx spfd b') ->
  SliceMorphism {a=(SPFDbase spfd)}
    (SPFDposCSlToBaseSl {spfd} (b ** i))
    (SPFDposCSlToBaseSl {spfd} (b' ** i')) ->
  SliceMorphism {a=dom}
    (SPFDmultiL spfd b i)
    (SPFDmultiL spfd b' i')
SPFDmultiLmap {dom} {cod} spfd b i b' i' =
  SPFDladjFactMap spfd
    (SPFDposCSlToBaseSl (b ** i))
    (SPFDposCSlToBaseSl (b' ** i'))

public export
SPFDmultiLmapEl : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (x : SliceObj cod) -> (y : SliceObj cod) ->
  (efy : SPFDmultiIdx spfd y) -> (mxy : SliceMorphism {a=cod} x y) ->
  SliceMorphism {a=dom}
    (SPFDmultiL spfd x $ SPFDmultiIdxContramap spfd y x mxy efy)
    (SPFDmultiL spfd y efy)
SPFDmultiLmapEl {dom} {cod} spfd x y efy mxy =
  SPFDmultiLmap spfd x (SPFDmultiIdxContramap spfd y x mxy efy) y efy
    $ \(ec ** ep) => s0Bimap (mxy ec) $ \ex, Refl => Refl

public export
SPFDmultiRL : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (b : SliceObj cod) -> (i : SPFDmultiIdx spfd b) -> SliceObj cod
SPFDmultiRL {dom} {cod} spfd b =
  SPFDmultiR {dom} {cod} spfd . SPFDmultiL {dom} {cod} spfd b

public export
SPFDmultiRLmap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (b : SliceObj cod) -> (i : SPFDmultiIdx spfd b) ->
  (b' : SliceObj cod) -> (i' : SPFDmultiIdx spfd b') ->
  SliceMorphism {a=(SPFDbase spfd)}
    (SPFDposCSlToBaseSl {spfd} (b ** i))
    (SPFDposCSlToBaseSl {spfd} (b' ** i')) ->
  SliceMorphism {a=cod}
    (SPFDmultiRL spfd b i)
    (SPFDmultiRL spfd b' i')
SPFDmultiRLmap {dom} {cod} spfd b i b' i' =
  SPFDmultiRmap spfd (SPFDmultiL spfd b i) (SPFDmultiL spfd b' i')
  . SPFDmultiLmap spfd b i b' i'

public export
SPFDpraUnitPos : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (b : SliceObj cod) -> (i : SPFDmultiIdx spfd b) ->
  (ec : cod) -> b ec -> spfdPos spfd ec
SPFDpraUnitPos {dom} {cod} spfd b i ec eb = i ec eb

-- This messy type signature represents nothing more than a
-- rearrangement of parameters, factored out simply to allow
-- for a type signature to show what's going on.
public export
SPFDpraUnitDir : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (b : SliceObj cod) -> (i : SPFDmultiIdx spfd b) ->
  (ec : cod) -> (eb : b ec) -> (ed : dom) ->
  (dd : spfdDir spfd ec (SPFDpraUnitPos spfd b i ec eb) ed) ->
  Sigma
    {a=(Sigma {a=(SPFDbase spfd)}
      (\ecp' => spfdDir spfd (fst ecp') (snd ecp') ed))}
    (\ecpd' => Subset0 (b (fst (fst ecpd')))
      $ \eb' => SPFDpraUnitPos spfd b i (fst (fst ecpd')) eb' = snd (fst ecpd'))
SPFDpraUnitDir {dom} {cod} spfd b i ec eb ed dd =
  (((ec ** SPFDpraUnitPos spfd b i ec eb) ** dd) ** Element0 eb Refl)

public export
SPFDpraUnit : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (b : SliceObj cod) -> (i : SPFDmultiIdx spfd b) ->
  SliceMorphism {a=cod} b (SPFDmultiRL spfd b i)
SPFDpraUnit {dom} {cod} spfd b i ec eb =
  (SPFDpraUnitPos spfd b i ec eb ** SPFDpraUnitDir spfd b i ec eb)

-- The type of the two components of a left multi-adjoint together --
-- index and (dependent) functor.
--
-- (Note that, on the ncatlab "multi-adjoint" page, this is the
-- "Theorem 2.4" version of the definition.)
--
-- One viewpoint on this structure is that it consists of:
--  - A presheaf on `SliceObj cod` (the index)
--  - A functor from the category of elements of the index to
--    `SliceObj dom` (or equivalently, a copresheaf on the product category
--    of the category of elements of the index with `dom` viewed as
--    a discrete category)
-- Note that those comprise precisely the inputs to `IntElemUFamOMap`/
-- `IntElemUFamFMap`.
public export
MultiLpair : (dom, cod : Type) -> Type
MultiLpair dom cod =
  (i : SliceObj cod -> Type ** (x : SliceObj cod) -> i x -> SliceObj dom)

-- The two components of the left multi-adjoint of the multi-adjunction
-- defined by a polynomial functor.
public export
SPFDmultiLpair : {dom, cod : Type} -> SPFData dom cod -> MultiLpair dom cod
SPFDmultiLpair {dom} {cod} spfd =
  (SPFDmultiIdx {dom} {cod} spfd ** SPFDmultiL {dom} {cod} spfd)

-- A slice object over `cod` together with an accompanying index of
-- the family of units of the multi-adjunction defined by a polynomial
-- functor comprises the domain of the uncurried form of the functor
-- component (`L`) of a multi-adjunction, below called `SPFDmultiLunc`.
-- As such, it may be considered as a form of the right-hand category
-- of the adjunction (an enhanced version of `SliceObj cod`).  Again,
-- this refers specifically to `L` as defined in Theorem 2.4 on the
-- ncatlab "multi-adjoint" page.
public export
SPFDmultiLdom : {dom, cod : Type} -> SPFData dom cod -> Type
SPFDmultiLdom = SPFDcsPos

-- But we may take another view of the structure (`SPFDcsPos`) that
-- we have dubbed `SPFDmultiLdom`: as we have seen above, it is
-- equivalent to a slice of `SPFDbase`.  In some cases, that view
-- gives the morphisms a simpler, dependent-type-style form.
public export
SPFDmultiLdomSl : {dom, cod : Type} -> SPFData dom cod -> Type
SPFDmultiLdomSl = SPFDbaseSl

-- The inverse of `SPFDunitIdxToSl`, converting a slice of the
-- base object to a unit index.
public export
SPFDbaseSlToUnitIdx : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFDmultiLdomSl spfd -> SPFDmultiLdom spfd
SPFDbaseSlToUnitIdx spfd = SPFDbaseSlToPosCSl {spfd}

public export
SPFDmultiLdomMor : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFDmultiLdom {dom} {cod} spfd -> SPFDmultiLdom {dom} {cod} spfd -> Type
SPFDmultiLdomMor {dom} {cod} spfd rx ry =
  SliceMorphism {a=(SPFDbase spfd)}
    (SPFDposCSlToBaseSl {spfd} rx)
    (SPFDposCSlToBaseSl {spfd} ry)

public export
SPFDmultiLdomSlMor : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFDmultiLdomSl {dom} {cod} spfd -> SPFDmultiLdomSl {dom} {cod} spfd -> Type
SPFDmultiLdomSlMor {dom} {cod} spfd = SliceMorphism {a=(SPFDbase spfd)}

public export
SPFDmultiLdomToBaseSl : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFDmultiLdom spfd -> SPFDmultiLdomSl spfd
SPFDmultiLdomToBaseSl spfd robj = SPFDunitIdxToSl spfd (fst robj) (snd robj)

-- The uncurried form of `SPFDmultiL`.
public export
SPFDmultiLunc : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFDmultiLdom spfd -> SliceObj dom
SPFDmultiLunc {dom} {cod} spfd = DPair.uncurry (SPFDmultiL {dom} {cod} spfd)

public export
SPFDmultiLuncMap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (m, m' : SPFDmultiLdom spfd) ->
  SliceMorphism {a=(SPFDbase spfd)}
    (SPFDposCSlToBaseSl {spfd} m)
    (SPFDposCSlToBaseSl {spfd} m') ->
  SliceMorphism {a=dom}
    (SPFDmultiLunc spfd m)
    (SPFDmultiLunc spfd m')
SPFDmultiLuncMap {dom} {cod} spfd m m' =
  SPFDmultiLmap {dom} {cod} spfd (fst m) (snd m) (fst m') (snd m')

-- Another way of viewing a multi-adjunction is as an enhanced form
-- of hom-set isomorphism using the (parameterized) category of families
-- (`IntFamObj`/`IntUFamMor`) of the left-hand-side category of the
-- multi-adjunction.  It uses the same right multi-adjoint (`SPFDmultiR`,
-- in this case), but a different left multi-adjoint whose codomain is
-- that category of families.  This is the characterization described in
-- Theorem 2.5 at https://ncatlab.org/nlab/show/multi-adjoint#definition .
public export
SPFDmultiFamLCatObj : Type -> Type
SPFDmultiFamLCatObj = SliceUFamObj

public export
0 SPFDmultiFamLCatMor : {lcat : Type} ->
  SPFDmultiFamLCatObj lcat -> SPFDmultiFamLCatObj lcat -> Type
SPFDmultiFamLCatMor {lcat} = SliceUFamMor

-- The left adjoint of the multi-adjunction using the category-of-families
-- formulation.
public export
SPFDmultiFamL : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceObj cod -> SPFDmultiFamLCatObj dom
SPFDmultiFamL {dom} {cod} spfd =
  IntElemUFamOMap {c=(SliceObj cod)} {d=(SliceObj dom)}
    (SPFDmultiIdx spfd) (SPFDmultiL spfd)

public export
0 SPFDmultiFamLmap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (x, y : SliceObj cod) ->
  SliceMorphism {a=cod} x y ->
  SPFDmultiFamLCatMor {lcat=dom}
    (SPFDmultiFamL {dom} {cod} spfd x)
    (SPFDmultiFamL {dom} {cod} spfd y)
SPFDmultiFamLmap {dom} {cod} spfd =
  IntElemUFamFMap {c=(SliceObj cod)} {d=(SliceObj dom)}
    (SliceMorphism {a=cod})
    (SliceMorphism {a=dom})
    (SPFDmultiIdx spfd)
    (\x, y => SPFDmultiIdxContramap spfd x y)
    (SPFDmultiL spfd)
    (SPFDmultiLmapEl spfd)

-- The codomain of the unit of the left multi-adjoint of a slice
-- polynomial functor.  It may be viewed as the first projection
-- of the multi-monad of the multi-adjunction induced by a slice
-- polynomial functor.
--
-- It comprises the composition called `TL(b, i)` under
-- https://ncatlab.org/nlab/show/parametric+right+adjoint#properties
-- (so the unit itself has type `b -> TL(b, i)`).
public export
SPFDmultiMfst : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFDmultiLdom {dom} {cod} spfd -> SliceObj cod
SPFDmultiMfst {dom} {cod} spfd =
  SPFDmultiR {dom} {cod} spfd . SPFDmultiLunc {dom} {cod} spfd

public export
SPFDmultiMfstMap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (m, m' : SPFDmultiLdom {dom} {cod} spfd) ->
  SliceMorphism {a=(SPFDbase spfd)}
    (SPFDposCSlToBaseSl {spfd} m)
    (SPFDposCSlToBaseSl {spfd} m') ->
  SliceMorphism {a=cod}
    (SPFDmultiMfst spfd m)
    (SPFDmultiMfst spfd m')
SPFDmultiMfstMap {dom} {cod} spfd m m' =
  SPFDmultiRmap {dom} {cod} spfd (SPFDmultiLunc spfd m) (SPFDmultiLunc spfd m')
  . SPFDmultiLuncMap {dom} {cod} spfd m m'

public export
SPFDmultiMsnd : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (robj : SPFDmultiLdom {dom} {cod} spfd) ->
  SPFDmultiIdx spfd (SPFDmultiMfst spfd robj)
SPFDmultiMsnd {dom} {cod} spfd robj ec = DPair.fst

public export
SPFDmultiMpair : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFDmultiLdom {dom} {cod} spfd -> SPFDmultiLdom {dom} {cod} spfd
SPFDmultiMpair {dom} {cod} spfd robj =
  (SPFDmultiMfst spfd robj ** SPFDmultiMsnd spfd robj)

public export
SPFDmultiMpairMap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (x, y : SPFDmultiLdom {dom} {cod} spfd) ->
  SPFDmultiLdomMor spfd x y ->
  SPFDmultiLdomMor spfd (SPFDmultiMpair spfd x) (SPFDmultiMpair spfd y)
SPFDmultiMpairMap {dom} {cod} spfd rx ry mxy ecp =
  s0Bimap
    (dpMapSnd $
      \ep, dm => snd $ SPFDmultiMfstMap spfd rx ry mxy (fst ecp) (ep ** dm))
    (\_ => id)

-- The second part of the "unique composite" `b -> SPFDmultiR a -> SPFDmultiR 1`
-- (see below) -- that is, the part with the signature
-- `SPFDmultiR a -> SPFDmultiR 1`.  `SPFDmultiR 1` is simply `spfdPos spfd`.
public export
SPFDgenFactIdxSndFact : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  SPFDmultiIdx spfd (SPFDmultiR {dom} {cod} spfd a)
SPFDgenFactIdxSndFact {dom} {cod} spfd a b ec = DPair.fst

-- The "unique composite" `b -> SPFDmultiR a -> SPFDmultiR 1` induced by a given
-- morphism `b -> SPFDmultiR a`, as described at
-- https://ncatlab.org/nlab/show/parametric+right+adjoint#properties .
-- Because `SPFDmultiR 1` is effectively `spfdPos spfd`, this amounts to
-- a morphism `b -> spfdPos spfd`, which is the index of a unit of the
-- multi-adjunction.  We call it `factIdx` because it is the index of the
-- particular unit which we use in factorizing this specific given
-- `i : b -> SPFDmultiR a`.
public export
SPFDgenFactIdx : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (i : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  SPFDmultiIdx spfd b
SPFDgenFactIdx {dom} {cod} spfd a b =
  sliceComp {a=cod} (SPFDgenFactIdxSndFact {dom} {cod} spfd a b)

-- Simply for documentation, we spell out what `SPFDgenFactIdx` is:
-- a term of an `SPFDmultiR spfd a ec eb` is a dependent pair of a
-- position and a direction-map, so any morphism into an `SPFDmultiR`
-- must be a constructor of a dependent pair -- a position-valued
-- morphism into the `SPFDmultiR`, and a direction-valued morphism
-- which depends on the position-valued one.  `SPGenFactIdx` is simply
-- the first projection, which constitutes the position-valued part.
-- This is the type that we have already called `SPFDmultiR1`.
public export
SPFDgenFactIdxEq : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (i : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  (ec : cod) -> (eb : b ec) ->
  SPFDgenFactIdx {dom} {cod} spfd a b i ec eb =
    SPFDmultiRto1 {spfd} {b} {a} i ec eb
SPFDgenFactIdxEq {dom} {cod} spfd a b i ec eb = Refl

-- This is the object of `SliceObj dom` which underlies the intermediate
-- object of the generic factorization of a morphism with the signature
-- `b -> SPFDmultiR spfd a`.  It is called `D` at
-- https://ncatlab.org/nlab/show/parametric+right+adjoint#generic_morphisms .
-- Lifting this via `SPFDmultiR` gives the object of `SliceObj cod` which
-- comprises the intermediate object of the generic factorization (called
-- `T D` at the ncatlab page, since in the case of the slice polynomial
-- multi-adjunction, `T` is `SPFDmultiR`).
public export
SPFDgenFactDomObj : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (i : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  SliceObj dom
SPFDgenFactDomObj {dom} {cod} spfd a b =
  SPFDmultiL {dom} {cod} spfd b . SPFDgenFactIdx {dom} {cod} spfd a b

-- For documentation and convenience, we also define an explicit formula
-- equivalent to `SPFDgenFactDomObj`.  We see that for each term of the
-- domain, it is the object of all directions of the functor, for all
-- terms of the codomain, at positions selected by the given morphism.
-- Note that we do not require a full morphism `b -> SPFDmultiR a` to
-- determine this object -- we only require the first component, which
-- returns a position, and thereby selects one of the units of the
-- multi-adjunction.  In other words, the intermediate object of the
-- generic factorization of a morphism is independent of the codomain
-- of the morphism; it depends only on the first projection, to the
-- position-set of the functor, without reference to the codomain of
-- the full morphism.
public export
SPFDgenFactDomObjForm : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (b : SliceObj cod) -> (i : SPFDmultiR1 {cod} (spfdPos spfd) b) -> SliceObj dom
SPFDgenFactDomObjForm {dom} {cod} spfd b i ed =
  (ec : cod ** eb : b ec ** spfdDir spfd ec (i ec eb) ed)

public export
SPFDgenFactDomObjFromForm : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (i : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  SliceMorphism {a=dom}
    (SPFDgenFactDomObjForm {dom} {cod} spfd b $ SPFDmultiRto1 {spfd} {b} {a} i)
    (SPFDgenFactDomObj {dom} {cod} spfd a b i)
SPFDgenFactDomObjFromForm {dom} {cod} spfd a b i ed (ec ** eb ** dd) =
  (((ec ** fst $ i ec eb) ** dd) ** Element0 eb Refl)

public export
SPFDgenFactDomObjToForm : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (i : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  SliceMorphism {a=dom}
    (SPFDgenFactDomObj {dom} {cod} spfd a b i)
    (SPFDgenFactDomObjForm {dom} {cod} spfd b $ SPFDmultiRto1 {spfd} {b} {a} i)
SPFDgenFactDomObjToForm {dom} {cod} spfd a b i ed
  (((ec ** ep) ** dd) ** Element0 eb epeq) =
    (ec ** eb ** rewrite epeq in dd)

-- This is the intermediate object of the generic factorization of the
-- given morphism `i` (see the comment to `SPFDgenFactDomObj` above).
public export
SPFDgenFactCodObj : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (i : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  SliceObj cod
SPFDgenFactCodObj {dom} {cod} spfd a b i =
  SPFDmultiR {dom} {cod} spfd $ SPFDgenFactDomObj {dom} {cod} spfd a b i

-- For documentation and convenience, we also define an explicit formula
-- equivalent to `SPFDgenFactCodObj`.
--
-- A term of this type is a pair of a position of the functor and an
-- assignment of the directions at that position to directions in
-- the range of `i`.
--
-- Note that this object does not depend on a full morphism `b -> SPFDmultiR a`,
-- but only on the first projection of one (an `SPFDmultiR1`).
public export
SPFDgenFactCodObjForm : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (b : SliceObj cod) -> (i : SPFDmultiR1 {cod} (spfdPos spfd) b) -> SliceObj cod
SPFDgenFactCodObjForm {dom} {cod} spfd b i ec =
  (ep : spfd .spfdPos ec **
   SliceMorphism {a=dom}
    (spfdDir spfd ec ep)
    (SPFDgenFactDomObjForm {dom} {cod} spfd b i))

public export
SPFDgenFactCodObjFromForm : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (i : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  SliceMorphism {a=cod}
    (SPFDgenFactCodObjForm {dom} {cod} spfd b $ SPFDmultiRto1 {spfd} {b} {a} i)
    (SPFDgenFactCodObj {dom} {cod} spfd a b i)
SPFDgenFactCodObjFromForm {dom} {cod} spfd a b i ec (ep ** dm) =
  (ep ** \ed, dd => case dm ed dd of
    (ec' ** eb' ** dd') =>
      (((ec' ** fst $ i ec' eb') ** dd') ** Element0 eb' Refl))

public export
SPFDgenFactCodObjToForm : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (i : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  SliceMorphism {a=cod}
    (SPFDgenFactCodObj {dom} {cod} spfd a b i)
    (SPFDgenFactCodObjForm {dom} {cod} spfd b $ SPFDmultiRto1 {spfd} {b} {a} i)
SPFDgenFactCodObjToForm {dom} {cod} spfd a b i ec (ep ** dm) =
  (ep **
   \ed, dd =>
    case dm ed dd of
      (((ec' ** ep') ** dd') ** Element0 eb beq) =>
        (ec' ** eb ** rewrite beq in dd'))

-- The first component of the generic factorization of a morphism through
-- a slice polynomial functor (which always exists for any parametric right
-- adjoint).
public export
SPFDgenFactFst : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (m : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  SliceMorphism {a=cod} b (SPFDgenFactCodObj {dom} {cod} spfd a b m)
SPFDgenFactFst {dom} {cod} spfd a b m =
  SPFDpraUnit spfd b $ SPFDgenFactIdx {dom} {cod} spfd a b m

-- Again, for convenience and documentation, we define an explicit formula
-- equivalent to `SPFDgenFactFst`.
--
-- Note that this depends only on the first projection of a morphism
-- `b -> SPFDmultiR a`, not on the second projection.
public export
SPFDgenFactFstForm : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (b : SliceObj cod) -> (m : SPFDmultiR1 {cod} (spfdPos spfd) b) ->
  SliceMorphism {a=cod} b (SPFDgenFactCodObjForm {dom} {cod} spfd b m)
SPFDgenFactFstForm {dom} {cod} spfd b m ec eb =
  (m ec eb ** \ed, dd => (ec ** eb ** dd))

public export
SPFDgenFactFstFormEq :
  {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (m : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  (ec : cod) -> (eb : b ec) ->
  SPFDgenFactFstForm {dom} {cod} spfd b (SPFDmultiRto1 {spfd} {b} {a} m) ec eb =
  SPFDgenFactCodObjToForm spfd a b m ec
    (SPFDgenFactFst {dom} {cod} spfd a b m ec eb)
SPFDgenFactFstFormEq {dom} {cod} spfd a b m ec eb = Refl

-- The morphism underlying the second component of the generic factorization of
-- a morphism through a slice polynomial functor.  By "underlying the second
-- component" we mean that lifting this morphism via `SPFDmultiR` produces
-- the second component.  This morphism lies in the domain category
-- (`SliceObj dom`); the lifted version lies in the codomain category
-- (`SliceObj cod`).
public export
SPFDgenFactSndDomCat : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (i : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  SliceMorphism {a=dom} (SPFDgenFactDomObj {dom} {cod} spfd a b i) a
SPFDgenFactSndDomCat {dom} {cod} spfd a b i ed ecdb =
  case ecdb of
    (((ec ** ep) ** dd) ** Element0 eb eqp) =>
      snd (i ec eb) ed $ rewrite eqp in dd

public export
SPFDgenFactSndDomCatFormDom : {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> {b : SliceObj cod} ->
  SPFDmultiR1 {cod} (spfdPos spfd) b -> (a : SliceObj dom) -> Type
SPFDgenFactSndDomCatFormDom {dom} {cod} spfd {b} i a =
  SliceMorphism {a=dom} (SPFDgenFactDomObjForm {dom} {cod} spfd b i) a

-- A version of `SPFDgenFactSndDomCat` which operates on the "explicit
-- formula" version of the domain object.
public export
SPFDgenFactSndDomCatFormSig : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (i : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  Type
SPFDgenFactSndDomCatFormSig {dom} {cod} spfd a b i =
  SPFDgenFactSndDomCatFormDom {dom} {cod} spfd {b}
    (SPFDmultiRto1 {spfd} {b} {a} i)
    a

public export
SPFDgenFactSndDomCatForm : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (i : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  SPFDgenFactSndDomCatFormSig {dom} {cod} spfd a b i
SPFDgenFactSndDomCatForm {dom} {cod} spfd a b i ed (ec ** eb ** dd) =
  snd (i ec eb) ed dd

-- We now note that any morphism with the same signature as an
-- `SPFDgenFactSndDomCatForm` is simply a rearrangement of parameters
-- of a signature we have already defined:  `SPFDmultiR2`.
public export
SPFDgenFactSndDomCatFormSigToR2 : {dom, cod : Type} ->
  {spfd : SPFData dom cod} ->
  {a : SliceObj dom} -> {b : SliceObj cod} ->
  {i : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)} ->
  (m : SPFDgenFactSndDomCatFormSig {dom} {cod} spfd a b i) ->
  SPFDmultiR2 {dom} {cod} spfd {b} (SPFDmultiRto1 {spfd} {b} {a} i) a
SPFDgenFactSndDomCatFormSigToR2 {dom} {cod} {spfd} {a} {b} {i} m ec eb ed dd =
  m ed (ec ** eb ** dd)

public export
SPFDgenFactSndDomCatFormSigFromR2 : {dom, cod : Type} ->
  {spfd : SPFData dom cod} ->
  {a : SliceObj dom} -> {b : SliceObj cod} ->
  {i1 : SPFDmultiR1 {cod} (spfdPos spfd) b} ->
  (i2 : SPFDmultiR2 {dom} {cod} spfd {b} i1 a) ->
  SPFDgenFactSndDomCatFormSig {dom} {cod} spfd a b
    (SPFDmultiRfrom12 {spfd} {b} {a} (i1 ** i2))
SPFDgenFactSndDomCatFormSigFromR2 {dom} {cod} {spfd} {a} {b} {i1} i2
  ed (ec ** eb ** dd) =
    i2 ec eb ed dd

public export
SPFDgenFactSndDomCatFormEq : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (i : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  (ed : dom) ->
  (ef :
    SPFDgenFactDomObjForm {dom} {cod} spfd b
      (SPFDmultiRto1 {spfd} {b} {a} i)
      ed) ->
  SPFDgenFactSndDomCatForm {dom} {cod} spfd a b i ed ef =
  SPFDgenFactSndDomCat {dom} {cod} spfd a b i ed
    (SPFDgenFactDomObjFromForm spfd a b i ed ef)
SPFDgenFactSndDomCatFormEq {dom} {cod} spfd a b i ed (ec ** eb ** dd) = Refl

-- The second component of the generic factorization of a morphism through
-- a slice polynomial functor.
public export
SPFDgenFactSnd : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (i : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  SliceMorphism {a=cod}
    (SPFDgenFactCodObj {dom} {cod} spfd a b i)
    (SPFDmultiR {dom} {cod} spfd a)
SPFDgenFactSnd {dom} {cod} spfd a b i =
  SPFDmultiRmap spfd
    (SPFDgenFactDomObj {dom} {cod} spfd a b i)
    a
    (SPFDgenFactSndDomCat {dom} {cod} spfd a b i)

-- Again, for convenience and documentation, we define an explicit formula
-- equivalent to `SPFDgenFactSnd`.
public export
SPFDgenFactSndForm : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (m : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  SliceMorphism {a=cod}
    (SPFDgenFactCodObjForm {dom} {cod} spfd b $ SPFDmultiRto1 {spfd} {b} {a} m)
    (SPFDmultiR {dom} {cod} spfd a)
SPFDgenFactSndForm {dom} {cod} spfd a b m ec (ep ** dm) =
  (ep ** \ed, dd =>
    case dm ed dd of (ec' ** eb' ** dd') => snd (m ec' eb') ed dd')

public export
SPFDgenFactSndFormSndFromForm :
  {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (m : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  (ec : cod) -> (eb : b ec) ->
  (ef : SPFDgenFactCodObjForm spfd b (SPFDmultiRto1 {spfd} {b} {a} m) ec) ->
  (ed : dom) ->
  spfdDir spfd ec (fst $ SPFDgenFactSndForm spfd a b m ec ef) ed ->
  spfdDir spfd ec (fst $ SPFDgenFactCodObjFromForm spfd a b m ec ef) ed
SPFDgenFactSndFormSndFromForm {dom} {cod} spfd a b m ec eb (ep ** dm) ed = id

public export
SPFDgenFactSndFormEqSndExt :
  {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (m : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  (ec : cod) -> (eb : b ec) ->
  (ef : SPFDgenFactCodObjForm spfd b (SPFDmultiRto1 {spfd} {b} {a} m) ec) ->
  (ed : dom) ->
  (dd : spfdDir spfd ec (fst (SPFDgenFactSndForm spfd a b m ec ef)) ed) ->
  snd (SPFDgenFactSndForm {dom} {cod} spfd a b m ec ef) ed dd =
    snd
      (SPFDgenFactSnd {dom} {cod} spfd a b m ec
        (SPFDgenFactCodObjFromForm {dom} {cod} spfd a b m ec ef))
      ed (SPFDgenFactSndFormSndFromForm spfd a b m ec eb ef ed dd)
SPFDgenFactSndFormEqSndExt {dom} {cod} spfd a b m ec eb (ep ** dm) ed dd
    with (dm ed dd)
  SPFDgenFactSndFormEqSndExt {dom} {cod} spfd a b m ec eb (ep ** dm) ed dd
    | (ec' ** eb' ** dd') = Refl

public export
SPFDgenFactSndFormEqSnd : FunExt ->
  {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (m : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  (ec : cod) -> (eb : b ec) ->
  (ef : SPFDgenFactCodObjForm spfd b (SPFDmultiRto1 {spfd} {b} {a} m) ec) ->
  snd (SPFDgenFactSndForm {dom} {cod} spfd a b m ec ef) ~=~
    snd (SPFDgenFactSnd {dom} {cod} spfd a b m ec
      (SPFDgenFactCodObjFromForm {dom} {cod} spfd a b m ec ef))
SPFDgenFactSndFormEqSnd fext {dom} {cod} spfd a b m ec eb (ep ** dm) =
  funExt $ \ed => funExt $ \dd =>
    SPFDgenFactSndFormEqSndExt spfd a b m ec eb (ep ** dm) ed dd

public export
SPFDgenFactSndFormEq : FunExt ->
  {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (m : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  (ec : cod) -> (eb : b ec) ->
  (ef : SPFDgenFactCodObjForm spfd b (SPFDmultiRto1 {spfd} {b} {a} m) ec) ->
  SPFDgenFactSndForm {dom} {cod} spfd a b m ec ef =
    SPFDgenFactSnd {dom} {cod} spfd a b m ec
      (SPFDgenFactCodObjFromForm {dom} {cod} spfd a b m ec ef)
SPFDgenFactSndFormEq fext {dom} {cod} spfd a b m ec eb (ep ** dm) =
  dpEq12
    Refl
    (SPFDgenFactSndFormEqSnd fext {dom} {cod} spfd a b m ec eb (ep ** dm))

public export
SPFDfactCorrect : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (i : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  FunExt ->
  (sliceComp
    (SPFDgenFactSnd {dom} {cod} spfd a b i)
    (SPFDgenFactFst {dom} {cod} spfd a b i)) =
  i
SPFDfactCorrect {dom} {cod} spfd a b i fext =
  funExt $ \ec => funExt $ \eb =>
    trans (dpEq12 Refl $ funExt $ \ed => funExt $ \dd => Refl) $ sym dpEqPat

-- Correctness of factorization using the simpler `SPFDmultiR12` form
-- which we have shown is equivalent to the standard one defined in
-- terms of applications of adjuncts.
public export
SPFDfactCorrectFormExt : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (i : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  (ec : cod) -> (eb : b ec) ->
  (SPFDgenFactSndForm {dom} {cod} spfd a b i ec $
    SPFDgenFactFstForm {dom} {cod} spfd b
      (SPFDmultiRto1 {spfd} {b} {a} i) ec eb) =
  i ec eb
SPFDfactCorrectFormExt {dom} {cod} spfd a b i ec eb with (i ec eb)
  SPFDfactCorrectFormExt {dom} {cod} spfd a b i ec eb | (ep ** dm) =
    Refl

public export
SPFDfactCorrectForm : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (i : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  FunExt ->
  (sliceComp
    (SPFDgenFactSndForm {dom} {cod} spfd a b i)
    (SPFDgenFactFstForm {dom} {cod} spfd b $ SPFDmultiRto1 {spfd} {b} {a} i)) =
  i
SPFDfactCorrectForm {dom} {cod} spfd a b i fext =
  funExt $ \ec => funExt $ \eb =>
    SPFDfactCorrectFormExt {dom} {cod} spfd a b i ec eb

-- Having shown that a factorization exists and is correct, and is
-- equivalent to specifying an `SPFDmultiR12`, we can conclude, in light
-- of the uniqueness of the factorization noted at
-- https://ncatlab.org/nlab/show/parametric+right+adjoint#generic_morphisms ,
-- that the specification of a morphism `b -> SPFDmultiR a` is equivalent to
-- a specification of an `SPFDmultiR12`.
--
-- With `SPFDmultiR1` being the generic component of that factorization
-- (the left class) and `SPFDmultiR2` being expressible as a lift by
-- `SPFDmultiR` of a morphism in `a : SliceObj dom` (the right class),
-- which as nlab also notes induces a factorization into generic and free
-- maps when `SPFDmultiR` is a monad, we now show that the first component
-- of the factorization which is induced by any `SPFDmultiR1` _is_ generic
-- in the sense of having fillers for diagrams of the shape shown in that
-- section of the nlab page.  With respect to that page, what they call
-- `a` and `f` we call `a'` and `f'`, while our `a` and `f` are the
-- intermediate object and first component of the generic factorization of
-- `f'`, because it is that component's genericity which we are demonstrating.
-- `f'` itself is not necessarily generic, of course, because it is simply
-- an arbitrary morphism into `SPFDmultiR a'`.
public export
SFPDfiller : {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  {a' : SliceObj dom} -> {b : SliceObj cod} ->
  (f' : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a')) ->
  {x, z : SliceObj dom} ->
  (alpha : SliceMorphism {a=cod} b (SPFDmultiR spfd x)) ->
  (beta :
    SliceMorphism {a=dom}
      (SPFDgenFactDomObjForm spfd b $ SPFDmultiRto1 {spfd} {b} {a=a'} f')
      z) ->
  (gamma : SliceMorphism {a=dom} x z) ->
  (comm : (ec : cod) -> (eb : b ec) ->
    SPFDmultiRmap spfd x z
      gamma
      ec
      (alpha ec eb) =
    SPFDmultiRmap spfd
      (SPFDgenFactDomObjForm spfd b $ SPFDmultiRto1 {spfd} {b} {a=a'} f')
      z
      beta
      ec
      (SPFDgenFactFstForm spfd b (SPFDmultiRto1 {spfd} {b} {a=a'} f') ec eb)) ->
  SliceMorphism {a=dom}
    (SPFDgenFactDomObjForm spfd b $ SPFDmultiRto1 {spfd} {b} {a=a'} f')
    x
SFPDfiller {dom} {cod} {spfd} {a'} {b} f' {x} {z} alpha beta gamma comm
  ed (ec ** eb ** dd) =
    snd (alpha ec eb) ed (rewrite dpeq1 (comm ec eb) in dd)

-- Because any morphism `b -> T(a)` induces a unique `b -> spfdPos spfd`,
-- we can use the demonstration of the generic factorization to allow a
-- new way of defining morphisms `b -> T(a)` without loss of generality.
-- We consider the first part to be defining the unique `b -> spfdPos spfd`,
-- and in light of this we can say that we can treat any domain of any
-- morphism `b -> T(a)` as sliced over `spfdPos spfd`.  Thus we may without
-- loss of generality define morphisms into `T(a)` as coming from domain
-- `SPFDbase`.
--
-- The choice of the slice object determines the intermediate object and the
-- first morphism component of the factorization:
public export
SPFDmorphDomFromBaseSl : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFDbaseSl spfd -> SliceObj cod
SPFDmorphDomFromBaseSl {dom} {cod} spfd i ec =
  Sigma {a=(spfdPos spfd ec)} $ curry i ec

public export
SPFDunitIdxFromBaseSl : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (i : SPFDbaseSl spfd) ->
  SPFDmultiIdx spfd (SPFDmorphDomFromBaseSl spfd i)
SPFDunitIdxFromBaseSl {dom} {cod} spfd i ec = DPair.fst

public export
SPFDgenFactIntDomObjFromBaseSl : {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> (i : SPFDbaseSl spfd) -> SliceObj dom
SPFDgenFactIntDomObjFromBaseSl {dom} {cod} spfd i =
  SPFDmultiL spfd
    (SPFDmorphDomFromBaseSl spfd i)
    (SPFDunitIdxFromBaseSl spfd i)

public export
SPFDgenFactIntCodObjFromBaseSl : {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> (i : SPFDbaseSl spfd) -> SliceObj cod
SPFDgenFactIntCodObjFromBaseSl {dom} {cod} spfd =
  SPFDmultiR {dom} {cod} spfd . SPFDgenFactIntDomObjFromBaseSl spfd

-- The first component of the generic factorization when specified by
-- a slice of `SPFDbase`.
--
-- Note that when we specify a morphism this way, we do not need to have
-- chosen a `SliceObj dom` yet -- our choice can be made independently of
-- the `a` in `b -> T(a)`, and therefore one such choice can be reused by
-- morphisms with different codomains.
public export
SPFDgenFactFstFromBaseSl : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (i : SPFDbaseSl spfd) ->
  SliceMorphism {a=cod}
    (SPFDmorphDomFromBaseSl spfd i)
    (SPFDgenFactIntCodObjFromBaseSl spfd i)
SPFDgenFactFstFromBaseSl {dom} {cod} spfd i =
  SPFDpraUnit spfd
    (SPFDmorphDomFromBaseSl spfd i)
    (SPFDunitIdxFromBaseSl spfd i)

-- If we have specified an intermediate object and first component of a
-- generic factorization via a slice of the base, we can then specify
-- the second component (again, without loss of generality) by a morphism
-- of `SliceObj dom`.  When doing it this way, because we have not yet
-- at this point specified the entire morphism, we are, instead of
-- factorizing an existing morphism, _building_ one out of what will
-- become its factorization.  So here we are specifying only the type
-- signature that is required to specify a second component.
public export
SPFDgenFactSndSigFromBaseSl : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (i : SPFDbaseSl spfd) -> (a : SliceObj dom) -> Type
SPFDgenFactSndSigFromBaseSl {dom} {cod} spfd i a =
  (ec : cod) -> (ep : spfdPos spfd ec) -> i (ec ** ep) ->
  SliceMorphism {a=dom} (spfdDir spfd ec ep) a

-- This is the form to which we can convert an `SPFDgenFactSndSigFromBaseSl`
-- from which it can be passed to `SPFDmultiRmap`.
public export
SPFDgenFactSndSigFromBaseSlrmap : {dom, cod : Type} ->
  (spfd : SPFData dom cod) ->
  (i : SPFDbaseSl spfd) -> (a : SliceObj dom) -> Type
SPFDgenFactSndSigFromBaseSlrmap {dom} {cod} spfd i a =
  SliceMorphism {a=dom} (SPFDgenFactIntDomObjFromBaseSl {dom} {cod} spfd i) a

-- This is the form to which we can convert an `SPFDgenFactSndSigFromBaseSl`
-- from which it can be passed to `SPFDmultiRmap`.
public export
SPFDgenFactSndSigFromBaseSlToRmap : {dom, cod : Type} ->
  {spfd : SPFData dom cod} -> {i : SPFDbaseSl spfd} -> {a : SliceObj dom} ->
  SPFDgenFactSndSigFromBaseSl {dom} {cod} spfd i a ->
  SPFDgenFactSndSigFromBaseSlrmap {dom} {cod} spfd i a
SPFDgenFactSndSigFromBaseSlToRmap {dom} {cod} {spfd=(SPFD pos dir)} {i} {a} m
  ed (((ec ** ep) ** dd) ** Element0 (ep' ** esl) epeq) =
    m ec ep (rewrite sym epeq in esl) ed dd

-- Given a domain-category morphism of the above signature, we can lift
-- it via the polynomial functor to the codomain category:
public export
SPFDgenFactSndFromBaseSl : {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  {i : SPFDbaseSl spfd} -> {a : SliceObj dom} ->
  SPFDgenFactSndSigFromBaseSl {dom} {cod} spfd i a ->
  SliceMorphism {a=cod}
    (SPFDgenFactIntCodObjFromBaseSl spfd i)
    (SPFDmultiR {dom} {cod} spfd a)
SPFDgenFactSndFromBaseSl {dom} {cod} {spfd} {i} {a} =
  SPFDmultiRmap spfd (SPFDgenFactIntDomObjFromBaseSl {dom} {cod} spfd i) a
  .  SPFDgenFactSndSigFromBaseSlToRmap {dom} {cod} {spfd} {i} {a}

-- If we are given a slice of the base (i.e. of the positions) and a
-- (domain-category) morphism of the above signature, we can compute a
-- (codomain-category) morphism:
public export
SPFDmorphFromBaseSlSig : {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  {i : SPFDbaseSl spfd} -> {a : SliceObj dom} ->
  SPFDgenFactSndSigFromBaseSl {dom} {cod} spfd i a ->
  SliceMorphism {a=cod}
    (SPFDmorphDomFromBaseSl spfd i)
    (SPFDmultiR {dom} {cod} spfd a)
SPFDmorphFromBaseSlSig {dom} {cod} {spfd} {i} {a} m =
  sliceComp {a=cod}
    (SPFDgenFactSndFromBaseSl {dom} {cod} {spfd} {i} {a} m)
    (SPFDgenFactFstFromBaseSl {dom} {cod} spfd i)

-- If we want to write a morphism `b -> T(a)` which is not explicitly
-- a sigma type, but do want to use the base-slice form of factorization,
-- then we can do that with a further factorization -- the choice of
-- a base slice and a corresponding domain-category morphism plus a
-- morphism from `b` to the chosen sigma type, which in turn factors
-- into two (a morphism to the first component and a dependent morphism
-- to the second component).
--
-- That yields the following full structure as a way of specifying
-- any morphism `b -> T(a)`:
public export
record MorphToSPFD {dom, cod : Type}
    (spfd : SPFData dom cod) (b : SliceObj cod) (a : SliceObj dom)
    where
  constructor MtoSPFD
  m2sInj1 : SliceMorphism {a=cod} b (spfdPos spfd)
  m2sBaseSl : SPFDbaseSl spfd
  m2sInj2 : (ec : cod) -> (eb : b ec) -> m2sBaseSl (ec ** m2sInj1 ec eb)
  m2sSndFact : SPFDgenFactSndSigFromBaseSl {dom} {cod} spfd m2sBaseSl a

public export
MorphToSPFDdom : {dom, cod : Type} ->
  {spfd : SPFData dom cod} -> {b : SliceObj cod} -> {a : SliceObj dom} ->
  (m : MorphToSPFD {dom} {cod} spfd b a) ->
  SliceMorphism {a=cod} b (SPFDmorphDomFromBaseSl spfd $ m2sBaseSl m)
MorphToSPFDdom {dom} {cod} {spfd} {b} {a} m ec eb =
  (m2sInj1 m ec eb ** m2sInj2 m ec eb)

public export
MorphToSPFDsigma : {dom, cod : Type} ->
  {spfd : SPFData dom cod} -> {b : SliceObj cod} -> {a : SliceObj dom} ->
  (m : MorphToSPFD {dom} {cod} spfd b a) ->
  SliceMorphism {a=cod}
    (SPFDmorphDomFromBaseSl spfd $ m2sBaseSl m)
    (SPFDmultiR spfd a)
MorphToSPFDsigma {dom} {cod} {spfd} {b} {a} m =
  SPFDmorphFromBaseSlSig {dom} {cod} {spfd} {i=(m2sBaseSl m)} {a} (m2sSndFact m)

public export
morphToSPFD : {dom, cod : Type} ->
  {spfd : SPFData dom cod} -> {b : SliceObj cod} -> {a : SliceObj dom} ->
  MorphToSPFD {dom} {cod} spfd b a ->
  SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)
morphToSPFD {dom} {cod} {spfd} {b} {a} m =
  sliceComp {a=cod}
    (MorphToSPFDsigma {dom} {cod} {spfd} {b} {a} m)
    (MorphToSPFDdom m)

-- As a parametric right adjoint, a polynomial functor has a left multi-adjoint
-- (so it is itself a right multi-adjoint).  This is the unit of the
-- slice-polynomial-functor multi-adjunction; its existence is listed as the
-- "Property" of a parametric right adjoint that it has a left multi-adjoint
-- at https://ncatlab.org/nlab/show/parametric+right+adjoint#properties .
-- We define it here in the generic way in which the unit of an adjunction
-- can be defined as the left adjunct applied to the identity morphism.
public export
SPFDmultiUnitFst : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (b : SPFDmultiLdom {dom} {cod} spfd) ->
  SliceMorphism {a=cod} (fst b) (SPFDmultiMfst {dom} {cod} spfd b)
SPFDmultiUnitFst {dom} {cod} spfd b = SPFDpraUnit spfd (fst b) (snd b)

-- The left side of the isomorphism which defines the hom-set description of
-- a multi-adjunction, as formulated in Theorem 2.4 at
-- at https://ncatlab.org/nlab/show/multi-adjoint#definition .
-- As such, it is the domain of the left multi-adjunct, and the
-- codomain of the right multi-adjunct.
public export
SPFDmultiAdjHSL : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceObj cod -> SliceObj dom -> Type
SPFDmultiAdjHSL {dom} {cod} spfd x y =
  (i : SPFDmultiIdx spfd x **
   SliceMorphism {a=dom} (SPFDmultiL {dom} {cod} spfd x i) y)

-- The right side of the isomorphism which defines the hom-set description of
-- a multi-adjunction, as formulated in Theorem 2.4 at
-- at https://ncatlab.org/nlab/show/multi-adjoint#definition .
-- As such, it is the domain of the right multi-adjunct, and the
-- codomain of the left multi-adjunct.
public export
SPFDmultiAdjHSR : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceObj cod -> SliceObj dom -> Type
SPFDmultiAdjHSR {dom} {cod} spfd x y =
  SliceMorphism {a=cod} x (SPFDmultiR {dom} {cod} spfd y)

-- This corresponds to the left-to-right direction of the isomorphism
-- which defines the hom-set description of a multi-adjunction as formulated
-- in Theorem 2.4 at https://ncatlab.org/nlab/show/multi-adjoint#definition .
--
-- It is the analogue of the left adjunct of a slice polynomial functor
-- viewed as a multi-adjoint (which it is by virtue of being a parametric
-- right adjoint, and of every slice category of `Type` having a terminal
-- object, namely the identity morphism in the category-theoretic view, or
-- `const Unit` in the dependent-type view).  So we might call it the
-- "left multi-adjunct" of the multi-adjunction defined by a slice polynomial
-- functor.
public export
SPFDmultiLAdj : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (x : SliceObj cod) -> (y : SliceObj dom) ->
  SPFDmultiAdjHSL spfd x y -> SPFDmultiAdjHSR spfd x y
SPFDmultiLAdj {dom} {cod} spfd x y m ec =
  dpMapSnd (\ep => sliceComp {a=dom} (snd m)) . SPFDpraUnit spfd x (fst m) ec

-- An uncurried form of `SPFDmultiLAdj`.
public export
SPFDmultiLAdjUnc : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (x : SPFDmultiLdom {dom} {cod} spfd) -> (y : SliceObj dom) ->
  SliceMorphism {a=dom} (SPFDmultiLunc {dom} {cod} spfd x) y ->
  SliceMorphism {a=cod} (fst x) (SPFDmultiR {dom} {cod} spfd y)
SPFDmultiLAdjUnc {dom} {cod} spfd x y m =
  SPFDmultiLAdj {dom} {cod} spfd (fst x) y (snd x ** m)

-- This is the right multi-adjunct of the multi-adjunction defined by a slice
-- polynomial functor (the inverse of `SPFDmultiLAdj` above.)
public export
SPFDmultiRAdj : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (x : SliceObj cod) -> (y : SliceObj dom) ->
  SPFDmultiAdjHSR spfd x y -> SPFDmultiAdjHSL spfd x y
SPFDmultiRAdj {dom} {cod} spfd x y m =
  (SPFDgenFactIdx {dom} {cod} spfd y x m **
   SPFDgenFactSndDomCat {dom} {cod} spfd y x m)

-- The left adjunct of the multi-adjunction defined by a polynomial functor
-- using the category-of-families formulation.
public export
SPFDmultiFamLAdj : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj cod) -> (b : SliceObj dom) ->
  SPFDmultiFamLCatMor {lcat=dom} (SPFDmultiFamL spfd a) (slUFamUnit b) ->
  SPFDmultiAdjHSR spfd a b
SPFDmultiFamLAdj {dom} {cod} spfd a b (midx ** mobj) =
  SPFDmultiLAdj {dom} {cod} spfd a b (midx () ** mobj ())

-- The right adjunct of the multi-adjunction defined by a polynomial functor
-- using the category-of-families formulation.
public export
SPFDmultiFamRAdj : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj cod) -> (b : SliceObj dom) ->
  SPFDmultiAdjHSR spfd a b ->
  SPFDmultiFamLCatMor {lcat=dom} (SPFDmultiFamL spfd a) (slUFamUnit b)
SPFDmultiFamRAdj {dom} {cod} spfd a b m =
  let (midx ** mobj) = SPFDmultiRAdj spfd a b m in
  IFUM
    {c=(SliceObj dom)}
    {mor=(SliceMorphism {a=dom})}
    {dom=(SPFDmultiFamL spfd a)}
    {cod=(slUFamUnit b)}
    (\() => midx)
    (\() => mobj)

-- This is `R . L` for the polynomial-functor multi-adjunction,
-- but note that these `R` and `L` are _multi_-adjoints, not
-- ordinary adjoints, so this is not necessarily a monad.
public export
SPFDrl : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceEndofunctor cod
SPFDrl {dom} {cod} spfd =
  SPFDmultiR {dom} {cod} spfd . SPFDL {dom} {cod} spfd

public export
SPFDrlMap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceFMap (SPFDrl {dom} {cod} spfd)
SPFDrlMap {dom} {cod} spfd x y =
  SPFDmultiRmap spfd (SPFDL spfd x) (SPFDL spfd y)
  . SPFDLmap spfd x y

-- This is `L . R` for the polynomial-functor multi-adjunction,
-- but note that these `L` and `R` are _multi_-adjoints, not
-- ordinary adjoints, so this is not necessarily a comonad.
public export
SPFDlr : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceEndofunctor dom
SPFDlr {dom} {cod} spfd =
  SPFDL {dom} {cod} spfd . SPFDmultiR {dom} {cod} spfd

public export
SPFDlrMap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceFMap (SPFDlr {dom} {cod} spfd)
SPFDlrMap {dom} {cod} spfd x y =
  SPFDLmap spfd (SPFDmultiR spfd x) (SPFDmultiR spfd y)
  . SPFDmultiRmap spfd x y

-- `SPFDladjFact` and `SPFDradjFact` are (ordinary, not multi-)
-- adjoints, so they induce a monad on `SliceObj (SPFDbase spfd)`.
public export
SPFDadjFactMonad : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceEndofunctor (SPFDbase spfd)
SPFDadjFactMonad spfd = SPFDradjFact spfd . SPFDladjFact spfd

public export
SPFDadjFactMonadMap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceFMap (SPFDadjFactMonad spfd)
SPFDadjFactMonadMap spfd x y =
  SPFDradjFactMap spfd (SPFDladjFact spfd x) (SPFDladjFact spfd y)
  . SPFDladjFactMap spfd x y

-- `SPFDladjFact` and `SPFDradjFact` are (ordinary, not multi-)
-- adjoints, so they induce a comonad on `SliceObj (SPFDbase spfd)`.
public export
SPFDadjFactComonad : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceEndofunctor dom
SPFDadjFactComonad spfd = SPFDladjFact spfd . SPFDradjFact spfd

public export
SPFDadjFactComonadMap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceFMap (SPFDadjFactComonad spfd)
SPFDadjFactComonadMap spfd x y =
  SPFDladjFactMap spfd (SPFDradjFact spfd x) (SPFDradjFact spfd y)
  . SPFDradjFactMap spfd x y

-- This is called the "spectrum" of `SPFDmultiR spfd` by Diers in
-- https://www.sciencedirect.com/science/article/pii/0022404981900827 and
-- https://core.ac.uk/download/pdf/82552386.pdf .  It is a presheaf
-- on `SliceObj cod`.
public export
SPFDspectrum : {dom, cod : Type} -> SPFData dom cod -> SliceObj cod -> Type
SPFDspectrum = SPFDmultiIdx

public export
SPFDspectrumMap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (x, y : SliceObj cod) ->
  SliceMorphism {a=cod} y x ->
  SPFDspectrum spfd x -> SPFDspectrum spfd y
SPFDspectrumMap = SPFDmultiIdxContramap

-- The category of elements of the spectrum of a polynomial functor.
public export
SPFDspecCatElemObj : {dom, cod : Type} -> SPFData dom cod -> Type
SPFDspecCatElemObj = SPFDmultiLdom

public export
SPFDspecCatElemMor : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFDspecCatElemObj spfd -> SPFDspecCatElemObj spfd -> Type
SPFDspecCatElemMor {dom} {cod} spfd x y =
  Subset0
    (SliceMorphism {a=cod} (fst x) (fst y))
    (\mxy => FunExt -> SPFDspectrumMap spfd (fst y) (fst x) mxy (snd y) = snd x)

-- Next we show that `SPFDspecCatElemObj`/`SPFDspecCatElemMor` is equivalent
-- to `SPFDmultiDomSl`/`SPFDmultiDomSlMor`.

public export
SPFDspecCEobjToSl : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFDspecCatElemObj {dom} {cod} spfd ->
  SPFDmultiLdomSl spfd
SPFDspecCEobjToSl = SPFDmultiLdomToBaseSl

public export
SPFDspecCEobjFromSl : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFDmultiLdomSl spfd ->
  SPFDspecCatElemObj {dom} {cod} spfd
SPFDspecCEobjFromSl = SPFDbaseSlToUnitIdx

public export
SPFDspecCEmorToSl : FunExt -> {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (x, y : SPFDspecCatElemObj {dom} {cod} spfd) ->
  SPFDspecCatElemMor {dom} {cod} spfd x y ->
  SPFDmultiLdomSlMor {dom} {cod} spfd
    (SPFDspecCEobjToSl spfd x)
    (SPFDspecCEobjToSl spfd y)
SPFDspecCEmorToSl fext spfd (_ ** _) (_ ** _) m ecp =
  s0Bimap
    (fst0 m $ fst ecp)
    $ \ex, xeq => trans (rewrite sym (snd0 m fext) in Refl) xeq

public export
SPFDspecCEmorFromSl : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (x, y : SPFDspecCatElemObj {dom} {cod} spfd) ->
  SPFDmultiLdomSlMor {dom} {cod} spfd
    (SPFDspecCEobjToSl spfd x)
    (SPFDspecCEobjToSl spfd y) ->
  SPFDspecCatElemMor {dom} {cod} spfd x y
SPFDspecCEmorFromSl spfd (slx ** px) (sly ** py) m =
  Element0
    (\ec, ex => fst0 $ m (ec ** px ec ex) $ Element0 ex Refl)
    (\fext => funExt $ \ec => funExt $ \ex =>
      snd0 $ m (ec ** px ec ex) $ Element0 ex Refl)

public export
SPFDslToSpecCEmor : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (x, y : SPFDmultiLdomSl {dom} {cod} spfd) ->
  SPFDmultiLdomSlMor {dom} {cod} spfd x y ->
  SPFDspecCatElemMor {dom} {cod} spfd
    (SPFDspecCEobjFromSl spfd x)
    (SPFDspecCEobjFromSl spfd y)
SPFDslToSpecCEmor {dom} {cod} spfd x y m =
  Element0
    (\ec, (ep ** ex) => (ep ** m (ec ** ep) ex))
    (\fext => funExt $ \ec => funExt $ \(ep ** ex) => Refl)

public export
SPFDslFromSpecCEmor : FunExt -> {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (x, y : SPFDmultiLdomSl {dom} {cod} spfd) ->
  SPFDspecCatElemMor {dom} {cod} spfd
    (SPFDspecCEobjFromSl spfd x)
    (SPFDspecCEobjFromSl spfd y) ->
  SPFDmultiLdomSlMor {dom} {cod} spfd x y
SPFDslFromSpecCEmor fext {dom} {cod} spfd x y (Element0 m meq) (ec ** ep) ex =
  rewrite sym (fcongdep {x=(ep ** ex)} (fcongdep {x=ec} (meq fext))) in
  snd $ m ec (ep ** ex)

-- Because `multiLdomSl` is `SliceObj (SPFDbase)`, we now know that
-- the monad `SPFDadjFactMonad` is a multi-monad -- that is, a monad
-- on the category of elements of a presheaf, with the presheaf in this
-- case being `SPFDspectrum`.

public export
SPFDspecUnit : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (bsl : SPFDbaseSl spfd) ->
  SliceMorphism {a=(SPFDbase spfd)}
    bsl
    (SPFDadjFactMonad spfd bsl)
SPFDspecUnit {dom} {cod} spfd bsl ecp ex ed dd = ((ecp ** dd) ** ex)

public export
SPFDspecJoin : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (bsl : SPFDbaseSl spfd) ->
  SliceMorphism {a=(SPFDbase spfd)}
    (SPFDadjFactMonad spfd $ SPFDadjFactMonad spfd bsl)
    (SPFDadjFactMonad spfd bsl)
SPFDspecJoin {dom} {cod} spfd bsl ecp dm ed dd with (dm ed dd)
  SPFDspecJoin {dom} {cod} spfd bsl ecp dm ed dd | dm' =
    snd dm' ed $ snd $ fst dm'

public export
SPFDspecCounit : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (x : SliceObj dom) ->
  SliceMorphism {a=dom}
    (SPFDadjFactComonad spfd x)
    x
SPFDspecCounit {dom} {cod} spfd x ed ecdm = snd ecdm ed $ snd $ fst ecdm

public export
SPFDspecDup : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (x : SliceObj dom) ->
  SliceMorphism {a=dom}
    (SPFDadjFactComonad spfd x)
    (SPFDadjFactComonad spfd $ SPFDadjFactComonad spfd x)
SPFDspecDup {dom} {cod} spfd x ed ecpdm =
  case ecpdm of
    ((ecp ** dd) ** dm) => ((ecp ** dd) ** \ed', dd' => ((ecp ** dd') ** dm))

-----------------------------------------------------------
---- Slice polynomials (in PRA formulation) as W-types ----
-----------------------------------------------------------

public export
SPFDdirBase : {dom, cod : Type} -> SPFData dom cod -> Type
SPFDdirBase {dom} {cod} spfd = (dom, SPFDbase spfd)

-- The total space of the domain of the dependent-product component
-- of the factorization of a polynomial functor into a base change
-- followed by a dependent product followed by a dependent sum.
-- (The domain of the dependent-product component is therefore also the
-- codomain of the base-change component.)
public export
SPFDdirTot : {dom, cod : Type} -> SPFData dom cod -> Type
SPFDdirTot {dom} {cod} spfd =
  (edcp : SPFDdirBase spfd **
   spfdDir spfd (fst $ snd edcp) (snd $ snd edcp) (fst edcp))

0 SPFDasWTF : {0 dom, cod : Type} -> SPFData dom cod -> WTypeFunc dom cod
SPFDasWTF {dom} {cod} spfd =
  MkWTF {dom} {cod}
    (SPFDbase spfd)
    (SPFDdirTot spfd)
    (fst . fst)
    (snd . fst)
    fst

0 spfdToWTF : {0 dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceNatTrans (InterpSPFData spfd) (InterpWTF $ SPFDasWTF spfd)
spfdToWTF {dom} {cod} spfd sd ec (ep ** dm) =
  (Element0 (ec ** ep) Refl **
   \(Element0 ((ed, (ec ** ep)) ** dp) Refl) => dm ed dp)

0 spfdFromWTF : {0 dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceNatTrans (InterpWTF $ SPFDasWTF spfd) (InterpSPFData spfd)
spfdFromWTF {dom} {cod} spfd sd ec
  (Element0 (ec ** ep) Refl ** dm) =
    (ep ** \ed, dp => dm (Element0 ((ed, (ec ** ep)) ** dp) Refl))

------------------------------------------------
---- W-types as PRA-style slice polynomials ----
------------------------------------------------

-- Above we showed that any `SPFData` can be converted to a W-type;
-- now we show the converse, thus completing the demonstration that PRA-style
-- slice polynomials are equivalent to W-types.
--
-- In particular, because we have also already showed that `SliceBCF`,
-- `SliceSigmaF`, and `SlicePiF` can all be interpreted as W-types, this
-- shows that all of those three functors, for all parameters, are subsumed
-- by PRA-style slice polynomials.
--
-- Also, because we have exhibited the functor in the opposite direction
-- (composed of the opposing adjuncts) of a slice polynomial functor as a
-- composition of a combination of `SliceSigmaF` and `SliceBCF` (`SlicePiF` is
-- not required), this also allows us to conclude that the functor in the
-- opposite direction is a slice polynomial functor.

0 WTFasSPFD : {0 dom, cod : Type} -> WTypeFunc dom cod -> SPFData dom cod
WTFasSPFD {dom} {cod} (MkWTF pos dir f g h) =
  SPFD
    (\ec => Subset0 pos $ \ep => h ep = ec)
    (\ec, (Element0 ep ecpeq), ed =>
      Subset0 dir $ \dd => (f dd = ed, g dd = ep))

0 wtfToSPFD : {0 dom, cod : Type} -> (wtf : WTypeFunc dom cod) ->
  SliceNatTrans (InterpWTF wtf) (InterpSPFData $ WTFasSPFD wtf)
wtfToSPFD {dom} {cod} (MkWTF pos dir f g h) sd ec (Element0 ep codeq ** dm) =
  (Element0 ep codeq **
   \ed, (Element0 dd (domeq, poseq)) =>
    rewrite sym domeq in dm $ Element0 dd poseq)

0 wtfFromSPFD : {0 dom, cod : Type} -> (wtf : WTypeFunc dom cod) ->
  SliceNatTrans (InterpSPFData $ WTFasSPFD wtf) (InterpWTF wtf)
wtfFromSPFD {dom} {cod} (MkWTF pos dir f g h) sd ec
  (Element0 ep codeq ** dm) =
    (Element0 ep codeq **
     \(Element0 dd poseq) => dm (f dd) $ Element0 dd (Refl, poseq))

--------------------------------------------------
--------------------------------------------------
---- Composition of slice polynomial functors ----
--------------------------------------------------
-------------------------------------------------

-- The category whose objects are those of `Type` and whose
-- morphisms are polynomial functors between the slice categories over
-- the corresponding objects.  (This may be seen as a two-category whose
-- objects are slice categories and whose 1-cells are slice polynomial
-- functors; the 2-cells are the natural transformations defined below.)

public export
SPFDidPos : (x : Type) -> SliceObj x
SPFDidPos x ex = Unit

public export
SPFDidDir : (x : Type) -> SPFdirType x x (SPFDidPos x)
SPFDidDir x ex eu ex' = case eu of () => ex = ex'

public export
SPFDid : (x : Type) -> SPFData x x
SPFDid x = SPFD (SPFDidPos x) (SPFDidDir x)

public export
SPFDcompPosFst : {x, y, z : Type} ->
  SPFData y z -> SPFData x y -> SliceObj z
SPFDcompPosFst {x} {y} {z} g f = spfdPos g

public export
SPFDcompPosSnd : {x, y, z : Type} ->
  (g : SPFData y z) -> (f : SPFData x y) ->
  (ez : z) -> SPFDcompPosFst g f ez -> Type
SPFDcompPosSnd {x} {y} {z} g f ez egp =
  SliceMorphism {a=y} (spfdDir g ez egp) (spfdPos f)

public export
SPFDcompPos : {x, y, z : Type} ->
  SPFData y z -> SPFData x y -> SliceObj z
SPFDcompPos {x} {y} {z} g f ez =
  Sigma {a=(SPFDcompPosFst g f ez)} $ SPFDcompPosSnd g f ez

public export
SPFDcompDirFst : {x, y, z : Type} ->
  (g : SPFData y z) -> (f : SPFData x y) ->
  SPFdirType x z (SPFDcompPos {x} {y} {z} g f)
SPFDcompDirFst {x} {y} {z} g f ez ep ex =
  Sigma {a=y} $ spfdDir g ez (fst ep)

public export
SPFDcompDirSnd : {x, y, z : Type} ->
  (g : SPFData y z) -> (f : SPFData x y) ->
  (ez : z) -> (ep : SPFDcompPos g f ez) -> (ex : x) ->
  SPFDcompDirFst g f ez ep ex -> Type
SPFDcompDirSnd {x} {y} {z} g f ez ep ex ecd =
  spfdDir f (fst ecd) (snd ep (fst ecd) (snd ecd)) ex

public export
SPFDcompDir : {x, y, z : Type} ->
  (g : SPFData y z) -> (f : SPFData x y) ->
  SPFdirType x z (SPFDcompPos {x} {y} {z} g f)
SPFDcompDir {x} {y} {z} g f ez ep ex =
  Sigma {a=(SPFDcompDirFst g f ez ep ex)} $ SPFDcompDirSnd g f ez ep ex

public export
SPFDcomp : (x, y, z : Type) ->
  SPFData y z -> SPFData x y -> SPFData x z
SPFDcomp x y z g f =
  SPFD (SPFDcompPos {x} {y} {z} g f) (SPFDcompDir {x} {y} {z} g f)

public export
SPFDfmics : MorIdCompSig Type
SPFDfmics = MICS SPFData $ ICS SPFDid SPFDcomp

public export
SPFDfcat : IntCatSig
SPFDfcat = ICat Type SPFDfmics

----------------------------------------------------
---- Interpretation of identity and composition ----
----------------------------------------------------

public export
InterpSPFtoId : (x : Type) ->
  SliceNatTrans (InterpSPFData $ SPFDid x) (Prelude.id {a=(SliceObj x)})
InterpSPFtoId x sx ex ei = case ei of (() ** d) => d ex Refl

public export
InterpSPFfromId : (x : Type) ->
  SliceNatTrans (Prelude.id {a=(SliceObj x)}) (InterpSPFData $ SPFDid x)
InterpSPFfromId x sx ex ei = (() ** \ex', xeq => replace {p=sx} xeq ei)

public export
InterpSPFtoComp : {x, y, z : Type} ->
  (g : SPFData y z) -> (f : SPFData x y) ->
  SliceNatTrans
    (InterpSPFData $ SPFDcomp x y z g f)
    (InterpSPFData g . InterpSPFData f)
InterpSPFtoComp {x} {y} {z} g f sx ez ei =
  (fst (fst ei) **
   \ey, egd =>
    (snd (fst ei) ey egd **
     \ex, efd => snd ei ex ((ey ** egd) ** efd)))

public export
InterpSPFfromComp : {x, y, z : Type} ->
  (g : SPFData y z) -> (f : SPFData x y) ->
  SliceNatTrans
    (InterpSPFData g . InterpSPFData f)
    (InterpSPFData $ SPFDcomp x y z g f)
InterpSPFfromComp {x} {y} {z} g f sx ez ei =
  ((fst ei **
    \ey, egd => fst $ snd ei ey egd) **
   \ex, dd => snd (snd ei (fst $ fst dd) (snd $ fst dd)) ex $ snd dd)

--------------------------------------------------------------------------
--------------------------------------------------------------------------
---- Slice polynomial functor pullbacks along base-category morphisms ----
--------------------------------------------------------------------------
--------------------------------------------------------------------------

public export
spfPullbackPos : {x, y, z : Type} ->
  (z -> y) -> SPFData x y -> SPFData x z
spfPullbackPos {x} {y} {z} mzy f =
  SPFD (BaseChangeF mzy $ spfdPos f) (\ez => spfdDir f (mzy ez))

public export
spfPullbackDir : {w, x, z : Type} ->
  (w -> x) -> SPFData x z -> SPFData w z
spfPullbackDir {w} {x} {z} mwx f =
  SPFD (spfdPos f) (\ez => BaseChangeF mwx . spfdDir f ez)

public export
spfPullback : {w, x, y, z : Type} ->
  (w -> x) -> (z -> y) -> SPFData x y -> SPFData w z
spfPullback {w} {x} {y} {z} mwx mzy =
  spfPullbackDir {w} {x} {z} mwx . spfPullbackPos {x} {y} {z} mzy

public export
spfPushoutPos : {x, y, z : Type} ->
  (z -> y) -> SPFData x z -> SPFData x y
spfPushoutPos {x} {y} {z} mzy f =
  SPFD
    (SliceFibSigmaF mzy $ spfdPos f)
    (\ey, ep => spfdDir f (sfsFst ep) (sfsSnd ep))

public export
spfPushoutDir : {w, x, z : Type} ->
  (w -> x) -> SPFData w z -> SPFData x z
spfPushoutDir {w} {x} {z} mwx f =
  SPFD (spfdPos f) (\ez, ep => SliceFibSigmaF mwx (spfdDir f ez ep))

public export
spfPushout : {w, x, y, z : Type} ->
  (w -> x) -> (z -> y) -> SPFData w z -> SPFData x y
spfPushout {w} {x} {y} {z} mwx mzy =
  spfPushoutPos {x} {y} {z} mzy . spfPushoutDir {w} {x} {z} mwx

public export
spfPiPos : {x, y, z : Type} ->
  (z -> y) -> SPFData x z -> SPFData x y
spfPiPos {x} {y} {z} mzy f =
  SPFD
    (SliceFibPiF mzy $ spfdPos f)
    (\ey, ep, ex =>
      (ez : WPreImage {a=z} {b=y} mzy ey ** spfdDir f (sfsFst ez) (ep ez) ex))

public export
spfPiDir : {w, x, z : Type} ->
  (w -> x) -> SPFData w z -> SPFData x z
spfPiDir {w} {x} {z} mwx f =
  SPFD (spfdPos f) (\ez, ep => SliceFibPiF mwx (spfdDir f ez ep))

public export
spfPi : {w, x, y, z : Type} ->
  (w -> x) -> (z -> y) -> SPFData w z -> SPFData x y
spfPi {w} {x} {y} {z} mwx mzy =
  spfPiPos {x} {y} {z} mzy . spfPiDir {w} {x} {z} mwx

public export
spfBaseChange : {w, x, y, z : Type} ->
  (w -> x) -> (z -> y) -> SPFData x z -> SPFData w y
spfBaseChange {w} {x} {y} {z} mwx mzy =
  spfPullbackDir {w} {x} {z=y} mwx . spfPushoutPos {x} {y} {z} mzy

--------------------------------------------------
-------------------------------------------------
---- Categories of slice polynomial functors ----
-------------------------------------------------
-------------------------------------------------

----------------------------------------------
---- Natural transformations as morphisms ----
----------------------------------------------

public export
SPFntCodPos : (tyel : TyElObj) ->
  (dom : Type) -> IntMorSig (SPFData dom $ fst tyel)
SPFntCodPos tyel dom f g = spfdPos f (snd tyel) -> spfdPos g (snd tyel)

public export
SPFntCodDirPos : (tyel : TyElObj) ->
  (dom : Type) -> (f, g : SPFData dom $ fst tyel) ->
  (onpos : SPFntCodPos tyel dom f g) -> spfdPos f (snd tyel) -> Type
SPFntCodDirPos tyel dom f g onpos ep =
  SliceMorphism {a=dom}
    (spfdDir g (snd tyel) $ onpos ep)
    (spfdDir f (snd tyel) ep)

public export
SPFntCodDir : (tyel : TyElObj) ->
  (dom : Type) -> (f, g : SPFData dom $ fst tyel) ->
  SPFntCodPos tyel dom f g -> Type
SPFntCodDir tyel dom f g =
  Pi {a=(spfdPos f $ snd tyel)} . SPFntCodDirPos tyel dom f g

public export
record SPFntEl
    (tyel : TyElObj) {dom : Type} (f, g : SPFData dom $ fst tyel) where
  constructor SPFntc
  speOnPos : SPFntCodPos tyel dom f g
  speOnDir : SPFntCodDir tyel dom f g speOnPos

-- An indexed family of natural transformations.
public export
SPFntef : {dom, cod : Type} -> IntMorSig (SPFData dom cod)
SPFntef {dom} {cod} f g = Pi {a=cod} $ \ec => SPFntEl (cod ** ec) {dom} f g

public export
SPFntPos : {dom, cod : Type} -> IntMorSig (SPFData dom cod)
SPFntPos {dom} {cod} f g = Pi {a=cod} $ \ec => SPFntCodPos (cod ** ec) dom f g

public export
SPFntDir : {dom, cod : Type} ->
  (f, g : SPFData dom cod) -> SPFntPos f g -> Type
SPFntDir {dom} {cod} f g onpos =
  Pi {a=cod} $ \ec => SPFntCodDir (cod ** ec) dom f g (onpos ec)

public export
record SPFnt {dom, cod : Type} (f, g : SPFData dom cod) where
  constructor SPFDm
  spOnPos : SPFntPos {dom} {cod} f g
  spOnDir : SPFntDir {dom} {cod} f g spOnPos

public export
SPNTidPos : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFntPos {dom} {cod} spfd spfd
SPNTidPos spfd = sliceId {a=cod} (spfdPos spfd)

public export
SPNTidDir : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFntDir {dom} {cod} spfd spfd (SPNTidPos spfd)
SPNTidDir spfd ec ep = sliceId {a=dom} (spfdDir spfd ec ep)

public export
SPNTid : {dom, cod : Type} -> IntIdSig (SPFData dom cod) (SPFnt {dom} {cod})
SPNTid spfd = SPFDm (SPNTidPos spfd) (SPNTidDir spfd)

public export
SPNTvcompPos : {dom, cod : Type} ->
  (f, g, h : SPFData dom cod) ->
  SPFntPos {dom} {cod} g h ->
  SPFntPos {dom} {cod} f g ->
  SPFntPos {dom} {cod} f h
SPNTvcompPos f g h = sliceComp {a=cod}

public export
SPNTvcompDir : {dom, cod : Type} ->
  (f, g, h : SPFData dom cod) ->
  (beta : SPFnt {dom} {cod} g h) ->
  (alpha : SPFnt {dom} {cod} f g) ->
  SPFntDir {dom} {cod} f h
    (SPNTvcompPos f g h (spOnPos beta) (spOnPos alpha))
SPNTvcompDir f g h beta alpha ec ep =
  sliceComp {a=dom}
    (spOnDir alpha ec ep)
    (spOnDir beta ec $ spOnPos alpha ec ep)

public export
SPNTvcomp : {dom, cod : Type} ->
  IntCompSig (SPFData dom cod) (SPFnt {dom} {cod})
SPNTvcomp {dom} {cod} f g h beta alpha =
  SPFDm
    (SPNTvcompPos f g h (spOnPos beta) (spOnPos alpha))
    (SPNTvcompDir f g h beta alpha)

public export
SPFDhs : GlobalHomStruct SPFDfcat
SPFDhs dom cod =
  MICS (SPFnt {dom} {cod}) $ ICS (SPNTid {dom} {cod}) (SPNTvcomp {dom} {cod})

public export
SPFDcat : Type -> Type -> IntCatSig
SPFDcat dom cod = ICat (SPFData dom cod) (SPFDhs dom cod)

public export
SPFfromIdL : {dom, cod : Type} ->
  (f : SPFData dom cod) ->
  SPFnt {dom} {cod} (SPFDcomp dom cod cod (SPFDid cod) f) f
SPFfromIdL {dom} {cod} spfd =
  SPFDm
    (\ec, uep => case uep of (() ** ep) => ep ec Refl)
    (\ec, uep, ed, efd => case uep of (() ** ep) => ((ec ** Refl) ** efd))

public export
SPFtoIdL : {dom, cod : Type} ->
  (f : SPFData dom cod) ->
  SPFnt {dom} {cod} f (SPFDcomp dom cod cod (SPFDid cod) f)
SPFtoIdL {dom} {cod} spfd =
  SPFDm
    (\ec, ep =>
      (() ** \ec', eq => case eq of Refl => ep))
    (\ec, ep, ed, ecfd =>
      case ecfd of ((ec' ** eq) ** efd) => case eq of Refl => efd)

public export
SPFfromIdR : {dom, cod : Type} ->
  (f : SPFData dom cod) ->
  SPFnt {dom} {cod} (SPFDcomp dom dom cod f (SPFDid dom)) f
SPFfromIdR {dom} {cod} spfd =
  SPFDm
    (\ec, epu =>
      fst epu)
    (\ec, epu, ed, efd =>
      ((ed ** efd) ** rewrite unitUnique (snd epu ed efd) () in Refl))

public export
SPFtoIdR : {dom, cod : Type} ->
  (f : SPFData dom cod) ->
  SPFnt {dom} {cod} f (SPFDcomp dom dom cod f (SPFDid dom))
SPFtoIdR {dom} {cod} spfd =
  SPFDm
    (\ec, efp => (efp ** \_, _ => ()))
    (\ec, efp, ed, efd => rewrite sym (snd efd) in snd $ fst efd)

--------------------------------------------------------------------
---- Interpretation of slice polynomial natural transformations ----
--------------------------------------------------------------------

public export
InterpSPFntOnPos : {dom, cod : Type} -> (f, g : SPFData dom cod) ->
  SPFnt f g -> SliceMorphism {a=cod} (spfdPos f) (spfdPos g)
InterpSPFntOnPos f g = spOnPos {f} {g}

public export
InterpSPFntOnDir : {dom, cod : Type} -> (f, g : SPFData dom cod) ->
  (alpha : SPFnt f g) ->
  (sd : SliceObj dom) -> (ec : cod) -> (ep : spfdPos f ec) ->
  SliceMorphism {a=dom} (spfdDir f ec ep) sd ->
  SliceMorphism {a=dom} (spfdDir g ec $ spOnPos alpha ec ep) sd
InterpSPFntOnDir f g alpha sd ec ep = flip sliceComp (spOnDir alpha ec ep)

public export
InterpSPFnt : {dom, cod : Type} -> (f, g : SPFData dom cod) ->
  SPFnt f g ->
  SliceNatTrans {x=dom} {y=cod} (InterpSPFData f) (InterpSPFData g)
InterpSPFnt {dom} {cod} f g alpha sd ec =
  dpBimap
    (spOnPos alpha ec)
    (InterpSPFntOnDir f g alpha sd ec)

public export
InterpSPFntId : {dom, cod : Type} ->
  (f : SPFData dom cod) -> (x : SliceObj dom) ->
  SliceExtEq {a=cod} {s=(InterpSPFData f x)} {s'=(InterpSPFData f x)}
    (InterpSPFnt f f (SPNTid f) x)
    (SliceId cod $ InterpSPFData f x)
InterpSPFntId {dom} {cod} f sd ec epdm = case epdm of (ep ** dm) => Refl

public export
InterpSPFntComp : {dom, cod : Type} ->
  (f, g, h : SPFData dom cod) ->
  (beta : SPFnt {dom} {cod} g h) ->
  (alpha : SPFnt {dom} {cod} f g) ->
  (x : SliceObj dom) ->
  SliceExtEq {a=cod} {s=(InterpSPFData f x)} {s'=(InterpSPFData h x)}
    (InterpSPFnt f h (SPNTvcomp f g h beta alpha) x)
    (sliceComp (InterpSPFnt g h beta x) (InterpSPFnt f g alpha x))
InterpSPFntComp {dom} {cod} f g h beta alpha x ec epdm =
  case epdm of (ep ** dm) => Refl

----------------------------------------------------------------
----------------------------------------------------------------
---- Slice polynomial whiskering and horizontal composition ----
----------------------------------------------------------------
----------------------------------------------------------------

public export
SPNTwhiskerL : {c, d, e : Type} ->
  {g, h : SPFData d e} ->
  SPFnt {dom=d} {cod=e} g h -> (f : SPFData c d) ->
  SPFnt {dom=c} {cod=e} (SPFDcomp c d e g f) (SPFDcomp c d e h f)
SPNTwhiskerL {c} {d} {e} {g} {h} spfd f =
  SPFDm
    (\ee, epdm =>
      (spOnPos spfd ee (fst epdm) **
       sliceComp {a=d} (snd epdm) (spOnDir spfd ee $ fst epdm)))
    (\ee, epdm, ec, fd =>
      ((fst (fst fd) **
       spOnDir spfd ee (fst epdm) (fst $ fst fd) (snd $ fst fd)) ** snd fd))

public export
SPNTwhiskerR : {c, d, e : Type} ->
  {f, g : SPFData c d} ->
  (h : SPFData d e) ->
  SPFnt {dom=c} {cod=d} f g ->
  SPFnt {dom=c} {cod=e} (SPFDcomp c d e h f) (SPFDcomp c d e h g)
SPNTwhiskerR {c} {d} {e} {f} {g} h spfd =
  SPFDm
    (\ee, epdm => (fst epdm ** sliceComp (spOnPos spfd) $ snd epdm))
    (\ee, epdm, ec, gd =>
      (fst gd **
       spOnDir spfd (fst $ fst gd) (snd epdm (fst $ fst gd) (snd $ fst gd)) ec
        (snd gd)))

public export
SPNThcomp : {c, d, e : Type} ->
  {f, f' : SPFData c d} ->
  {g, g' : SPFData d e} ->
  SPFnt {dom=d} {cod=e} g g' -> SPFnt {dom=c} {cod=d} f f' ->
  SPFnt {dom=c} {cod=e} (SPFDcomp c d e g f) (SPFDcomp c d e g' f')
SPNThcomp {c} {d} {e} {f} {f'} {g} {g'} beta alpha =
  SPNTvcomp (SPFDcomp c d e g f) (SPFDcomp c d e g f') (SPFDcomp c d e g' f')
    (SPNTwhiskerL {g} {h=g'} beta f')
    (SPNTwhiskerR {f} {g=f'} g alpha)

public export
SPFDwls : GlobalLeftWhiskerHomStruct SPFDfcat SPFDhs
SPFDwls c d e f g h nu = SPNTwhiskerL {g} {h} nu f

public export
SPFDwrs : GlobalRightWhiskerHomStruct SPFDfcat SPFDhs
SPFDwrs c d e h f g nu = SPNTwhiskerR {f} {g} h nu

public export
SPFDwps : GlobalWhiskerPairHomStruct SPFDfcat SPFDhs
SPFDwps = MkGlobalWhiskerPairHomStruct SPFDfcat SPFDhs SPFDwls SPFDwrs

public export
SPFDhcs : GlobalHcompHomStruct SPFDfcat SPFDhs
SPFDhcs = GlobalHcompFromWhiskers SPFDfcat SPFDhs SPFDwps

public export
SPFD2cat : Int2CatSig
SPFD2cat = I2Cat SPFDfcat $ I2CS SPFDhs SPFDwls SPFDwrs

-------------------------------------
---- Interpretation of whiskering ---
-------------------------------------

public export
InterpSPFntWhiskerL : FunExt ->
  {c, d, e : Type} ->
  (g, h : SPFData d e) ->
  (nu : SPFnt {dom=d} {cod=e} g h) -> (f : SPFData c d) ->
  (x : SliceObj c) ->
  SliceExtEq {a=e}
    {s=(InterpSPFData g $ InterpSPFData f x)}
    {s'=(InterpSPFData h $ InterpSPFData f x)}
    (sliceComp
      (sliceComp
        (InterpSPFtoComp h f x)
        (InterpSPFnt {dom=c} {cod=e} (SPFDcomp c d e g f) (SPFDcomp c d e h f)
          (SPNTwhiskerL {g} {h} nu f) x))
     $ InterpSPFfromComp g f x)
    (SliceWhiskerLeft {c} {d} {e}
      {g=(InterpSPFData {dom=d} {cod=e} g)}
      {h=(InterpSPFData {dom=d} {cod=e} h)}
      (InterpSPFnt {dom=d} {cod=e} g h nu)
      (InterpSPFData {dom=c} {cod=d} f)
      x)
InterpSPFntWhiskerL fext {c} {d} {e} g h nu f x ee epdm =
  dpEq12 Refl $ funExt $ \ed => funExt $ \hd =>
    sym $ dpEqPat {dp=(snd epdm ed (spOnDir nu ee (fst epdm) ed hd))}

public export
InterpSPFntWhiskerR : FunExt ->
  {c, d, e : Type} ->
  (f, g : SPFData c d) ->
  (h : SPFData d e) ->
  (nu : SPFnt {dom=c} {cod=d} f g) ->
  (x : SliceObj c) ->
  SliceExtEq {a=e}
    {s=(InterpSPFData h $ InterpSPFData f x)}
    {s'=(InterpSPFData h $ InterpSPFData g x)}
    (sliceComp
      (sliceComp
        (InterpSPFtoComp h g x)
        (InterpSPFnt {dom=c} {cod=e} (SPFDcomp c d e h f) (SPFDcomp c d e h g)
          (SPNTwhiskerR {f} {g} h nu) x))
     $ InterpSPFfromComp h f x)
    (SliceWhiskerRight {c} {d} {e}
      {f=(InterpSPFData {dom=c} {cod=d} f)}
      {g=(InterpSPFData {dom=c} {cod=d} g)}
      {h=(InterpSPFData {dom=d} {cod=e} h)}
      (InterpSPFDataMap {dom=d} {cod=e} h)
      (InterpSPFnt {dom=c} {cod=d} f g nu)
      x)
InterpSPFntWhiskerR fext {c} {d} {e} f g h nu x ee epdm =
  dpEq12 Refl $ funExt $ \ed => funExt $ \hd => Refl

-----------------------------------------------------------------------------
-----------------------------------------------------------------------------
---- Components of slice polynomials (base change, sigma, pi) as SPFData ----
-----------------------------------------------------------------------------
-----------------------------------------------------------------------------

---------------------
---- Base change ----
---------------------

public export
SPFDbc : {x, y : Type} -> (y -> x) -> SPFData x y
SPFDbc {x} {y} f = SPFD (\_ => Unit) (\ey, eunit, ex => f ey = ex)

public export
InterpSPFDtoBC : {x, y : Type} -> (f : y -> x) ->
  SliceNatTrans {x} {y} (InterpSPFData $ SPFDbc f) (BaseChangeF f)
InterpSPFDtoBC {x} {y} f sx ey ei = case ei of (() ** dm) => dm (f ey) Refl

public export
InterpSPFDfromBC : {x, y : Type} -> (f : y -> x) ->
  SliceNatTrans {x} {y} (BaseChangeF f) (InterpSPFData $ SPFDbc f)
InterpSPFDfromBC {x} {y} f sx ey ei = (() ** \ex, eq => replace {p=sx} eq ei)

---------------
---- Sigma ----
---------------

public export
SPFDsigma : {x, y : Type} -> (x -> y) -> SPFData x y
SPFDsigma {x} {y} f =
  SPFD (\ey => WPreImage {a=x} {b=y} f ey) (\ey, ep, ex => sfsFst ep = ex)

public export
InterpSPFDtoSigma : {x, y : Type} -> (f : x -> y) ->
  SliceNatTrans {x} {y} (InterpSPFData $ SPFDsigma f) (SliceFibSigmaF f)
InterpSPFDtoSigma {x} {y} f sx ey ei =
  rewrite sym $ sfsEq $ fst ei in
  SFS {sc=sx} (sfsFst $ fst ei) (snd ei (sfsFst $ fst ei) Refl)

public export
InterpSPFDfromSigma : {x, y : Type} -> (f : x -> y) ->
  SliceNatTrans {x} {y} (SliceFibSigmaF f) (InterpSPFData $ SPFDsigma f)
InterpSPFDfromSigma {x} {y} f sx ey ei =
  rewrite sym (sfsEq ei) in
  (SFS (sfsFst ei) () ** \ex, eq => rewrite sym eq in sfsSnd ei)

------------
---- Pi ----
------------

public export
SPFDpi : {x, y : Type} -> (x -> y) -> SPFData x y
SPFDpi {x} {y} f = SPFD (\_ => Unit) (\ey, eunit, ex => f ex = ey)

public export
0 InterpSPFDtoPi : {x, y : Type} -> (f : x -> y) ->
  SliceNatTrans {x} {y} (InterpSPFData $ SPFDpi f) (SliceFibPiF f)
InterpSPFDtoPi {x} {y} f sx ey ei ex =
  case ei of (() ** dm) => dm (sfsFst ex) (sfsEq ex)

public export
InterpSPFDfromPi : {x, y : Type} -> (f : x -> y) ->
  SliceNatTrans {x} {y} (SliceFibPiF f) (InterpSPFData $ SPFDpi f)
InterpSPFDfromPi {x} {y} f sx ey pix =
  (() ** \ex, eq => pix $ rewrite sym eq in SFS ex ())

------------------------------
------------------------------
---- Pre/post-composition ----
------------------------------
------------------------------

-- Precompose a base change before a slice polynomial.
public export
spfdPrecompBC : {x, y, z : Type} -> (y -> x) -> SPFData y z -> SPFData x z
spfdPrecompBC {x} {y} {z} f = flip (SPFDcomp x y z) (SPFDbc f)

-- Postcompose a base change after a slice polynomial.
public export
spfdPostcompBC : {x, y, z : Type} -> (z -> y) -> SPFData x y -> SPFData x z
spfdPostcompBC {x} {y} {z} f = (SPFDcomp x y z) (SPFDbc f)

-- "Dichange" -- pre- and post- compose a slice polynomial with base changes.
public export
spfdDichange : {s, t, a, b : Type} ->
  (a -> s) -> (t -> b) -> SPFData a b -> SPFData s t
spfdDichange {s} {t} {a} {b} mas mtb =
  spfdPrecompBC {x=s} {y=a} {z=t} mas . spfdPostcompBC {x=a} {y=b} {z=t} mtb

-- Precompose a sigma before a slice polynomial.
public export
spfdPrecompSigma : {x, y, z : Type} -> (x -> y) -> SPFData y z -> SPFData x z
spfdPrecompSigma {x} {y} {z} f = flip (SPFDcomp x y z) (SPFDsigma f)

-- Postcompose a sigma after a slice polynomial.
public export
spfdPostcompSigma : {x, y, z : Type} -> (y -> z) -> SPFData x y -> SPFData x z
spfdPostcompSigma {x} {y} {z} f = (SPFDcomp x y z) (SPFDsigma f)

-- Precompose a pi before a slice polynomial.
public export
spfdPrecompPi : {x, y, z : Type} -> (x -> y) -> SPFData y z -> SPFData x z
spfdPrecompPi {x} {y} {z} f = flip (SPFDcomp x y z) (SPFDpi f)

-- Postcompose a pi after a slice polynomial.
public export
spfdPostcompPi : {x, y, z : Type} -> (y -> z) -> SPFData x y -> SPFData x z
spfdPostcompPi {x} {y} {z} f = (SPFDcomp x y z) (SPFDpi f)

-- Postcomposition with sigma is the same as what we have
-- called pushing out along position.

public export
0 spfdPostcompSigmaToPushoutPos : {x, y, z : Type} ->
  (myz : y -> z) -> (f : SPFData x y) ->
  SPFnt {dom=x} {cod=z} (spfdPostcompSigma myz f) (spfPushoutPos myz f)
spfdPostcompSigmaToPushoutPos {x} {y} {z} myz f =
  SPFDm
    (\ez, epdm =>
      rewrite sym $ sfsEq $ fst epdm in
      SFS (sfsFst $ fst epdm) (snd epdm (sfsFst $ fst epdm) Refl))
    (\ez, epdm, ex, efd => ((sfsFst (fst epdm) ** Refl) ** efd))

public export
spfdPostcompSigmaFromPushoutPos : {x, y, z : Type} ->
  (myz : y -> z) -> (f : SPFData x y) ->
  SPFnt {dom=x} {cod=z} (spfPushoutPos myz f) (spfdPostcompSigma myz f)
spfdPostcompSigmaFromPushoutPos {x} {y} {z} myz f =
  SPFDm
    (\ez, ep =>
      rewrite sym (sfsEq ep) in
      (SFS (sfsFst ep) () **
       \ey, xeq => rewrite sym xeq in sfsSnd ep))
    (\ez, ep, ex, efd => rewrite snd (fst efd) in snd efd)

-- Postcomposition with base change is the same as what we have
-- called pulling back along position.

public export
spfdPostcompBCtoPullbackPos : {x, y, z : Type} ->
  (mzy : z -> y) -> (f : SPFData x y) ->
  SPFnt {dom=x} {cod=z} (spfdPostcompBC mzy f) (spfPullbackPos mzy f)
spfdPostcompBCtoPullbackPos {x} {y} {z} mzy f =
  SPFDm
    (\ez, epdm => snd epdm (mzy ez) Refl)
    (\ez, epdm, ex, efd => ((mzy ez ** Refl) ** efd))

public export
spfdPostcompBCfromPullbackPos : {x, y, z : Type} ->
  (mzy : z -> y) -> (f : SPFData x y) ->
  SPFnt {dom=x} {cod=z} (spfPullbackPos mzy f) (spfdPostcompBC mzy f)
spfdPostcompBCfromPullbackPos {x} {y} {z} mzy f =
  SPFDm
    (\ez, ep => (() ** \ey, eq => replace {p=(spfdPos f)} eq ep))
    (\ez, ep, ex, efd => rewrite (snd $ fst efd) in snd efd)

-- Postcomposition with pi is the same as what we have
-- called pi along position.

public export
0 spfdPostcompPiToPiPos : {x, y, z : Type} ->
  (myz : y -> z) -> (f : SPFData x y) ->
  SPFnt {dom=x} {cod=z} (spfdPostcompPi myz f) (spfPiPos myz f)
spfdPostcompPiToPiPos {x} {y} {z} myz f =
  SPFDm
    (\ez, efp, ey => snd efp (sfsFst ey) (sfsEq ey))
    (\ez, efp, ex, efd => ((sfsFst (fst efd) ** sfsEq (fst efd)) ** snd efd))

public export
spfdPostcompPiFromPiPos : {x, y, z : Type} ->
  (myz : y -> z) -> (f : SPFData x y) ->
  SPFnt {dom=x} {cod=z} (spfPiPos myz f) (spfdPostcompPi myz f)
spfdPostcompPiFromPiPos {x} {y} {z} myz f =
  SPFDm
    (\ez, efp => (() ** \ey, ezeq => efp $ rewrite sym ezeq in SFS ey ()))
    (\ez, efp, ex, efd =>
      rewrite sym $ snd (fst efd) in (SFS (fst $ fst efd) () ** snd efd))

-- Precomposition with base change is the same as what we have
-- called pushing out along direction.

public export
0 spfdPrecompBCToPushoutDir : {x, y, z : Type} ->
  (myx : y -> x) -> (f : SPFData y z) ->
  SPFnt {dom=x} {cod=z} (spfdPrecompBC myx f) (spfPushoutDir myx f)
spfdPrecompBCToPushoutDir {x} {y} {z} myx f =
  SPFDm
    (\ez, epTermMorph => fst epTermMorph)
    (\ez, ep, ex, efd => ((sfsFst efd ** sfsSnd efd) ** sfsEq efd))

public export
spfdPrecompBCFromPushoutDir : {x, y, z : Type} ->
  (myx : y -> x) -> (f : SPFData y z) ->
  SPFnt {dom=x} {cod=z} (spfPushoutDir myx f) (spfdPrecompBC myx f)
spfdPrecompBCFromPushoutDir {x} {y} {z} my f =
  SPFDm
    (\ez, ep => (ep ** \_, _ => ()))
    (\ez, ep, ex, efd =>
      rewrite sym (snd efd) in SFS (fst $ fst efd) $ snd $ fst efd)

-- Precomposition with pi is the same as what we have
-- called pulling back along direction.

public export
0 spfdPrecompPiToPullbackDir : {x, y, z : Type} ->
  (mxy : x -> y) -> (f : SPFData y z) ->
  SPFnt {dom=x} {cod=z} (spfdPrecompPi mxy f) (spfPullbackDir mxy f)
spfdPrecompPiToPullbackDir {x} {y} {z} mxy f =
  SPFDm
    (\ez, ep => fst ep)
    (\ez, ep, ex, efd => ((mxy ex ** efd) ** Refl))

public export
0 spfdPrecompPiFromPullbackDir : {x, y, z : Type} ->
  (mxy : x -> y) -> (f : SPFData y z) ->
  SPFnt {dom=x} {cod=z} (spfPullbackDir mxy f) (spfdPrecompPi mxy f)
spfdPrecompPiFromPullbackDir {x} {y} {z} mxy f =
  SPFDm
    (\ez, efd => (efd ** \_, _ => ()))
    (\ez, ep, ex, efd => rewrite snd efd in snd (fst efd))

---------------------------------------------------------------
---------------------------------------------------------------
---- Slice polynomial double-categorical structure (cells) ----
---------------------------------------------------------------
---------------------------------------------------------------

---------------------------
---- Via `spfPullback` ----
---------------------------

-- `spfPullback bcl bcr g` is `BaseChange bcr . g . Pi bcl`, so this
-- could be seen as a "relaxed" twisted-arrow morphism from `g` to `f`
-- (equivalently, a relaxed morphism of the opposite of the twisted-arrow
-- category from `f` to `g`), with `Pi bcl` and `BaseChange bcr` as the
-- arrows, and the natural transformation taking the place of strict equality.
public export
SPFpbCell : {w, w', z, z' : Type} ->
  (bcl : w -> w') -> (bcr : z -> z') ->
  (f : SPFData w z) -> (g : SPFData w' z') ->
  Type
SPFpbCell {w} {w'} {z} {z'} bcl bcr f g =
  SPFnt {dom=w} {cod=z} (spfPullback bcl bcr g) f

public export
spbcVid : {w, z : Type} -> (f : SPFData w z) ->
  SPFpbCell {w} {w'=w} {z} {z'=z} Prelude.id Prelude.id f f
spbcVid {w} {z} f =
  SPFDm
    (\ez, ep => ep)
    (\ez, ep, ew, efd => efd)

public export
spbcHid : {w, w' : Type} -> (bcw : w -> w') ->
  SPFpbCell {w} {w'} {z=w} {z'=w'} bcw bcw (SPFDid w) (SPFDid w')
spbcHid {w} {w'} bcw =
  SPFDm
    (\_, _ => ())
    (\ew, ep, ew', eweq => case ep of () => cong bcw eweq)

public export
spbcVcomp : {w, w', w'', z, z', z'' : Type} ->
  {bcl : w -> w'} -> {bcl' : w' -> w''} ->
  {bcr : z -> z'} -> {bcr' : z' -> z''} ->
  {f : SPFData w z} -> {g : SPFData w' z'} -> {h : SPFData w'' z''} ->
  SPFpbCell {w=w'} {w'=w''} {z=z'} {z'=z''} bcl' bcr' g h ->
  SPFpbCell {w} {w'} {z} {z'} bcl bcr f g ->
  SPFpbCell {w} {w'=w''} {z} {z'=z''} (bcl' . bcl) (bcr' . bcr) f h
spbcVcomp {w} {w'} {w''} {z} {z'} {z''} {bcl} {bcl'} {bcr} {bcr'} {f} {g} {h}
  beta alpha =
    SPFDm
      (\ez =>
        spOnPos alpha ez . spOnPos beta (bcr ez))
      (\ez, ep, ew, epdm =>
        spOnDir beta (bcr ez) ep (bcl ew)
        $ spOnDir alpha ez (spOnPos beta (bcr ez) ep) ew epdm)

public export
spbcHcompPos : {w, w', x, x', z, z' : Type} ->
  {bcw : w -> w'} -> {bcx : x -> x'} -> {bcz : z -> z'} ->
  {f : SPFData w x} -> {f' : SPFData x z} ->
  {g : SPFData w' x'} -> {g' : SPFData x' z'} ->
  SPFpbCell {w=x} {w'=x'} {z} {z'} bcx bcz f' g' ->
  SPFpbCell {w} {w'} {z=x} {z'=x'} bcw bcx f g ->
  SPFntPos {dom=w} {cod=z}
    (spfPullback bcw bcz $ SPFDcomp w' x' z' g' g)
    (SPFDcomp w x z f' f)
spbcHcompPos {w} {w'} {x} {x'} {z} {z'} {bcw} {bcx} {bcz} {f} {f'} {g} {g'}
  beta alpha ez ep =
    (spOnPos beta ez (fst ep) **
     \ex, ef' =>
      spOnPos alpha ex $ snd ep (bcx ex) $ spOnDir beta ez (fst ep) ex ef')

public export
spbcHcompDir : {w, w', x, x', z, z' : Type} ->
  {bcw : w -> w'} -> {bcx : x -> x'} -> {bcz : z -> z'} ->
  {f : SPFData w x} -> {f' : SPFData x z} ->
  {g : SPFData w' x'} -> {g' : SPFData x' z'} ->
  (beta : SPFpbCell {w=x} {w'=x'} {z} {z'} bcx bcz f' g') ->
  (alpha : SPFpbCell {w} {w'} {z=x} {z'=x'} bcw bcx f g) ->
  SPFntDir {dom=w} {cod=z}
    (spfPullback bcw bcz $ SPFDcomp w' x' z' g' g)
    (SPFDcomp w x z f' f)
    (spbcHcompPos {bcw} {bcx} {bcz} {f} {f'} {g} {g'} beta alpha)
spbcHcompDir {w} {w'} {x} {x'} {z} {z'} {bcw} {bcx} {bcz} {f} {f'} {g} {g'}
    beta alpha ez ep ew efd with
      (spOnDir beta ez (fst ep) (fst $ fst efd) (snd $ fst efd)) proof egeq
  spbcHcompDir {w} {w'} {x} {x'} {z} {z'} {bcw} {bcx} {bcz} {f} {f'} {g} {g'}
    beta alpha ez ep ew efd | egd' =
      ((bcx (fst $ fst efd) ** egd') **
       spOnDir alpha
        (fst $ fst efd)
        (snd ep (bcx $ fst $ fst efd) egd')
        ew
        (rewrite sym egeq in snd efd))

public export
spbcHcomp : {w, w', x, x', z, z' : Type} ->
  {bcw : w -> w'} -> {bcx : x -> x'} -> {bcz : z -> z'} ->
  {f : SPFData w x} -> {f' : SPFData x z} ->
  {g : SPFData w' x'} -> {g' : SPFData x' z'} ->
  SPFpbCell {w=x} {w'=x'} {z} {z'} bcx bcz f' g' ->
  SPFpbCell {w} {w'} {z=x} {z'=x'} bcw bcx f g ->
  SPFpbCell {w} {w'} {z} {z'}
    bcw
    bcz
    (SPFDcomp w x z f' f)
    (SPFDcomp w' x' z' g' g)
spbcHcomp {w} {w'} {x} {x'} {z} {z'} {bcw} {bcx} {bcz} {f} {f'} {g} {g'}
  beta alpha =
    SPFDm
      (spbcHcompPos beta alpha)
      (spbcHcompDir beta alpha)

public export
SPFpbDblCatCell : IntCellSig Type TypeMor SPFData
SPFpbDblCatCell x0 x1 y0 y1 = SPFpbCell {w=x0} {w'=y0} {z=x1} {z'=y1}

public export
SPFpbDblCatVId : IntCellVIdSig InternalCat.typeId SPFpbDblCatCell
SPFpbDblCatVId x y = spbcVid {w=x} {z=y}

public export
SPFpbDblCatHId : IntCellHIdSig SPFDid SPFpbDblCatCell
SPFpbDblCatHId x y = spbcHid {w=x} {w'=y}

public export
SPFpbDblCatVcomp : IntCellVCompSig InternalCat.typeComp SPFpbDblCatCell
SPFpbDblCatVcomp vmxy0 vmxy1 vmyz0 vmyz1 hmx hmy hmz =
  spbcVcomp
    {bcl=vmxy0} {bcl'=vmyz0} {bcr=vmxy1} {bcr'=vmyz1}
    {f=hmx} {g=hmy} {h=hmz}

public export
SPFpbDblCatHcomp : IntCellHCompSig SPFDcomp SPFpbDblCatCell
SPFpbDblCatHcomp vmxy0 vmxy1 vmxy2 hmx01 hmx12 hmy01 hmy12 =
  spbcHcomp
    {bcw=vmxy0} {bcx=vmxy1} {bcz=vmxy2}
    {f=hmx01} {f'=hmx12} {g=hmy01} {g'=hmy12}

public export
SPFpbDblCatCellTo2Mor :
  IntCellTo2MorSig InternalCat.typeComp SPFpbDblCatCell InternalCat.typeId
SPFpbDblCatCellTo2Mor x y f g = Prelude.id

public export
SPFpbDoubleCat : IntDblCatSig
SPFpbDoubleCat =
  IDCat
    Type
    TypeMICS
    SPFDfmics
    SPFpbDblCatCell
    SPFpbDblCatVId
    SPFpbDblCatHId
    SPFpbDblCatVcomp
    SPFpbDblCatHcomp
    SPFpbDblCatCellTo2Mor

--------------------------
---- Via `spfPushout` ----
--------------------------

-- `spfPushout bcl bcr f` is `Sigma bcr . f . BaseChange bcl`, so this
-- could be seen as a "relaxed" twisted-arrow morphism from `f` to `g`,
-- with `BaseChange bcl` and `Sigma bcr` as arrows, and the natural
-- transformation taking the place of strict equality.
public export
SPFpoCell : {w, w', z, z' : Type} ->
  (bcl : w -> w') -> (bcr : z -> z') ->
  (f : SPFData w z) -> (g : SPFData w' z') ->
  Type
SPFpoCell {w} {w'} {z} {z'} bcl bcr f g =
  SPFnt {dom=w'} {cod=z'} (spfPushout bcl bcr f) g

-- A pushout cell determines a commutative diagram of the double-category form
-- in https://ncatlab.org/nlab/show/polynomial+functor#the_2category_of_polynomial_functors .

public export
0 SPFpoCellToWTypePos : {w, w', z, z' : Type} ->
  (bcl : w -> w') -> (bcr : z -> z') ->
  (f : SPFData w z) -> (g : SPFData w' z') ->
  SPFpoCell {w} {w'} {z} {z'} bcl bcr f g ->
  wtPos (SPFDasWTF f) -> wtPos (SPFDasWTF g)
SPFpoCellToWTypePos {w} {w'} {z} {z'} bcl bcr f g spfc (ez ** efp) =
  (bcr ez ** spOnPos spfc (bcr ez) $ SFS ez efp)

public export
0 SPFpoCellToWTypeDir : {w, w', z, z' : Type} ->
  (bcl : w -> w') -> (bcr : z -> z') ->
  (f : SPFData w z) -> (g : SPFData w' z') ->
  (spfc : SPFpoCell {w} {w'} {z} {z'} bcl bcr f g) ->
  Pullback
    {a=(wtDir $ SPFDasWTF g)}
    {b=(wtPos $ SPFDasWTF f)}
    {c=(wtPos $ SPFDasWTF g)}
    (wtDirSlice $ SPFDasWTF g)
    (SPFpoCellToWTypePos {w} {w'} {z} {z'} bcl bcr f g spfc) ->
    wtDir (SPFDasWTF f)
SPFpoCellToWTypeDir {w} {w'} {z} {z'} bcl bcr f g spfc
    (Element0 (((ew', (_ ** _)) ** egd), (ez ** efp)) Refl)
    with (spOnDir spfc (bcr ez) (SFS ez efp) ew' egd)
  SPFpoCellToWTypeDir {w} {w'} {z} {z'} bcl bcr f g spfc
    (Element0 (((_, (_ ** _)) ** egd), (ez ** efp)) Refl) | (SFS ew efd) =
      ((ew, (ez ** efp)) ** efd)

public export
0 SPFpoCellToWTypeCommPos : {w, w', z, z' : Type} ->
  (bcl : w -> w') -> (bcr : z -> z') ->
  (f : SPFData w z) -> (g : SPFData w' z') ->
  (spfc : SPFpoCell {w} {w'} {z} {z'} bcl bcr f g) ->
  ExtEq
    (bcr . wtPosSlice (SPFDasWTF f))
    (wtPosSlice (SPFDasWTF g) . SPFpoCellToWTypePos bcl bcr f g spfc)
SPFpoCellToWTypeCommPos {w} {w'} {z} {z'} bcl bcr f g spfc (ez ** efp) = Refl

public export
0 SPFpoCellToWTypeCommDir : {w, w', z, z' : Type} ->
  (bcl : w -> w') -> (bcr : z -> z') ->
  (f : SPFData w z) -> (g : SPFData w' z') ->
  (spfc : SPFpoCell {w} {w'} {z} {z'} bcl bcr f g) ->
  ExtEq
    (wtDirSlice (SPFDasWTF f) . SPFpoCellToWTypeDir bcl bcr f g spfc)
    (pbProj2
      {f=(wtDirSlice $ SPFDasWTF g)}
      {g=(SPFpoCellToWTypePos bcl bcr f g spfc)})
SPFpoCellToWTypeCommDir {w} {w'} {z} {z'} bcl bcr f g spfc
    (Element0 (((ew', (_ ** _)) ** egd), (ez ** efp)) Refl)
    with (spOnDir spfc (bcr ez) (SFS ez efp) ew' egd)
  SPFpoCellToWTypeCommDir {w} {w'} {z} {z'} bcl bcr f g spfc
    (Element0 (((_, (_ ** _)) ** egd), (ez ** efp)) Refl) | SFS ew efd =
      Refl

public export
0 SPFpoCellToWTypeCommAssign : {w, w', z, z' : Type} ->
  (bcl : w -> w') -> (bcr : z -> z') ->
  (f : SPFData w z) -> (g : SPFData w' z') ->
  (spfc : SPFpoCell {w} {w'} {z} {z'} bcl bcr f g) ->
  ExtEq
    (bcl . wtAssign (SPFDasWTF f) . SPFpoCellToWTypeDir bcl bcr f g spfc)
    (wtAssign (SPFDasWTF g) .
      pbProj1
        {f=(wtDirSlice $ SPFDasWTF g)}
        {g=(SPFpoCellToWTypePos bcl bcr f g spfc)})
SPFpoCellToWTypeCommAssign {w} {w'} {z} {z'} bcl bcr f g spfc
    (Element0 (((ew', (_ ** _)) ** egd), (ez ** efp)) Refl)
    with (spOnDir spfc (bcr ez) (SFS ez efp) ew' egd)
  SPFpoCellToWTypeCommAssign {w} {w'} {z} {z'} bcl bcr f g spfc
    (Element0 (((_, (_ ** _)) ** egd), (ez ** efp)) Refl) | SFS ew efd =
      Refl

public export
0 SPFpoCellToWType : {w, w', z, z' : Type} ->
  (bcl : w -> w') -> (bcr : z -> z') ->
  (f : SPFData w z) -> (g : SPFData w' z') ->
  SPFpoCell {w} {w'} {z} {z'} bcl bcr f g ->
  WTypeCell {w} {w'} {z} {z'} bcl bcr (SPFDasWTF f) (SPFDasWTF g)
SPFpoCellToWType {w} {w'} {z} {z'} bcl bcr f g spfc =
  WTCell
    (SPFpoCellToWTypePos bcl bcr f g spfc)
    (SPFpoCellToWTypeDir bcl bcr f g spfc)
    (SPFpoCellToWTypeCommPos bcl bcr f g spfc)
    (SPFpoCellToWTypeCommDir bcl bcr f g spfc)
    (SPFpoCellToWTypeCommAssign bcl bcr f g spfc)

public export
0 SPFntToWType : {w, z : Type} ->
  {f, g : SPFData w z} ->
  SPFnt {dom=w} {cod=z} f g ->
  WTypeNT {w} {z} (SPFDasWTF f) (SPFDasWTF g)
SPFntToWType {w} {z} {f} {g} spnt =
  SPFpoCellToWType {w} {w'=w} {z} {z'=z} Prelude.id Prelude.id f g $
    SPFDm
      (\ez, (SFS ez ep) => spOnPos spnt ez ep)
      (\ez, (SFS ez ep), ew, egd => SFS ew $ spOnDir spnt ez ep ew egd)

public export
spocVid : {w, z : Type} -> (f : SPFData w z) ->
  SPFpoCell {w} {w'=w} {z} {z'=z} Prelude.id Prelude.id f f
spocVid {w} {z} f =
  SPFDm
    (\ez, ep => rewrite sym (sfsEq ep) in sfsSnd ep)
    (\ez, ep, ew, efd => SFS ew $ rewrite sfsEq ep in efd)

public export
spocHid : {w, w' : Type} -> (bcw : w -> w') ->
  SPFpoCell {w} {w'} {z=w} {z'=w'} bcw bcw (SPFDid w) (SPFDid w')
spocHid {w} {w'} bcw =
  SPFDm
    (\_, _ => ())
    (\ew', ep, ew'', ew'eq =>
      case ep of SFS ew () => rewrite sym ew'eq in SFS ew Refl)

public export
spocVcomp : {w, w', w'', z, z', z'' : Type} ->
  {bcl : w -> w'} -> {bcl' : w' -> w''} ->
  {bcr : z -> z'} -> {bcr' : z' -> z''} ->
  {f : SPFData w z} -> {g : SPFData w' z'} -> {h : SPFData w'' z''} ->
  SPFpoCell {w=w'} {w'=w''} {z=z'} {z'=z''} bcl' bcr' g h ->
  SPFpoCell {w} {w'} {z} {z'} bcl bcr f g ->
  SPFpoCell {w} {w'=w''} {z} {z'=z''} (bcl' . bcl) (bcr' . bcr) f h
spocVcomp {w} {w'} {w''} {z} {z'} {z''} {bcl} {bcl'} {bcr} {bcr'} {f} {g} {h}
  beta alpha =
    SPFDm
      (\ez'', (SFS ez efp) =>
        spOnPos beta ez'' $ SFS (bcr ez) $ spOnPos alpha (bcr ez) $ SFS ez efp)
      (\ez'', (SFS ez efp), ew'', ehd =>
        let
          (SFS ew' egd) =
            spOnDir beta ez''
              (SFS (bcr ez) (spOnPos alpha (bcr ez) (SFS ez efp))) ew'' ehd
          (SFS ew efd) =
            spOnDir alpha (bcr ez)
              (SFS ez efp) ew' egd
        in
        SFS {sc=(spfdDir f ez efp)} {f=(bcl' . bcl)} ew efd)

public export
spocHcompPos : {w, w', x, x', z, z' : Type} ->
  {bcw : w -> w'} -> {bcx : x -> x'} -> {bcz : z -> z'} ->
  {f : SPFData w x} -> {f' : SPFData x z} ->
  {g : SPFData w' x'} -> {g' : SPFData x' z'} ->
  SPFpoCell {w=x} {w'=x'} {z} {z'} bcx bcz f' g' ->
  SPFpoCell {w} {w'} {z=x} {z'=x'} bcw bcx f g ->
  SPFntPos {dom=w'} {cod=z'}
    (spfPushout bcw bcz $ SPFDcomp w x z f' f)
    (SPFDcomp w' x' z' g' g)
spocHcompPos {w} {w'} {x} {x'} {z} {z'} {bcw} {bcx} {bcz} {f} {f'} {g} {g'}
  beta alpha _ (SFS ez (efp' ** efpdm)) =
    (spOnPos beta (bcz ez) (SFS ez efp') **
     \ex' =>
      spOnPos alpha ex'
      . sfsMap (spfdDir f' ez efp') (spfdPos f) efpdm ex'
      . spOnDir beta (bcz ez) (SFS ez efp') ex')

public export
spocHcompDir : {w, w', x, x', z, z' : Type} ->
  {bcw : w -> w'} -> {bcx : x -> x'} -> {bcz : z -> z'} ->
  {f : SPFData w x} -> {f' : SPFData x z} ->
  {g : SPFData w' x'} -> {g' : SPFData x' z'} ->
  (beta : SPFpoCell {w=x} {w'=x'} {z} {z'} bcx bcz f' g') ->
  (alpha : SPFpoCell {w} {w'} {z=x} {z'=x'} bcw bcx f g) ->
  SPFntDir {dom=w'} {cod=z'}
    (spfPushout bcw bcz $ SPFDcomp w x z f' f)
    (SPFDcomp w' x' z' g' g)
    (spocHcompPos {bcw} {bcx} {bcz} {f} {f'} {g} {g'} beta alpha)
spocHcompDir {w} {w'} {x} {x'} {z} {z'} {bcw} {bcx} {bcz} {f} {f'} {g} {g'}
    beta alpha _ (SFS ez (efp' ** efpdm)) ew' ((_ ** egd') ** egd)
    with (spOnDir beta (bcz ez) (SFS ez efp') _ egd') proof direq
  spocHcompDir {w} {w'} {x} {x'} {z} {z'} {bcw} {bcx} {bcz} {f} {f'} {g} {g'}
    beta alpha _ (SFS ez (efp' ** efpdm)) ew' ((_ ** egd') ** egd)
    | (SFS ex efd') =
      case spOnDir alpha (bcx ex) (SFS ex $ efpdm ex efd') ew' egd of
        (SFS ew efd) => SFS ew ((ex ** efd') ** efd)

public export
spocHcomp : {w, w', x, x', z, z' : Type} ->
  {bcw : w -> w'} -> {bcx : x -> x'} -> {bcz : z -> z'} ->
  {f : SPFData w x} -> {f' : SPFData x z} ->
  {g : SPFData w' x'} -> {g' : SPFData x' z'} ->
  SPFpoCell {w=x} {w'=x'} {z} {z'} bcx bcz f' g' ->
  SPFpoCell {w} {w'} {z=x} {z'=x'} bcw bcx f g ->
  SPFpoCell {w} {w'} {z} {z'}
    bcw
    bcz
    (SPFDcomp w x z f' f)
    (SPFDcomp w' x' z' g' g)
spocHcomp {w} {w'} {x} {x'} {z} {z'} {bcw} {bcx} {bcz} {f} {f'} {g} {g'}
  beta alpha =
    SPFDm
      (spocHcompPos beta alpha)
      (spocHcompDir beta alpha)

public export
SPFpoDblCatCell : IntCellSig Type TypeMor SPFData
SPFpoDblCatCell x0 x1 y0 y1 = SPFpoCell {w=x0} {w'=y0} {z=x1} {z'=y1}

public export
SPFpoDblCatVId : IntCellVIdSig InternalCat.typeId SPFpoDblCatCell
SPFpoDblCatVId x y = spocVid {w=x} {z=y}

public export
SPFpoDblCatHId : IntCellHIdSig SPFDid SPFpoDblCatCell
SPFpoDblCatHId x y = spocHid {w=x} {w'=y}

public export
SPFpoDblCatVcomp : IntCellVCompSig InternalCat.typeComp SPFpoDblCatCell
SPFpoDblCatVcomp vmxy0 vmxy1 vmyz0 vmyz1 hmx hmy hmz =
  spocVcomp
    {bcl=vmxy0} {bcl'=vmyz0} {bcr=vmxy1} {bcr'=vmyz1}
    {f=hmx} {g=hmy} {h=hmz}

public export
SPFpoDblCatHcomp : IntCellHCompSig SPFDcomp SPFpoDblCatCell
SPFpoDblCatHcomp vmxy0 vmxy1 vmxy2 hmx01 hmx12 hmy01 hmy12 =
  spocHcomp
    {bcw=vmxy0} {bcx=vmxy1} {bcz=vmxy2}
    {f=hmx01} {f'=hmx12} {g=hmy01} {g'=hmy12}

public export
SPFpoDblCatCellTo2Mor :
  IntCellTo2MorSig InternalCat.typeComp SPFpoDblCatCell InternalCat.typeId
SPFpoDblCatCellTo2Mor x y f g = Prelude.id

public export
SPFpoDoubleCat : IntDblCatSig
SPFpoDoubleCat =
  IDCat
    Type
    TypeMICS
    SPFDfmics
    SPFpoDblCatCell
    SPFpoDblCatVId
    SPFpoDblCatHId
    SPFpoDblCatVcomp
    SPFpoDblCatHcomp
    SPFpoDblCatCellTo2Mor

-------------------------------------------------
-------------------------------------------------
---- Slice-polynomial categories of elements ----
-------------------------------------------------
-------------------------------------------------

public export
SPFelem : {dom, cod : Type} -> SPFData dom cod -> SliceObj dom -> Type
SPFelem {dom} {cod} spfd = Pi {a=cod} . InterpSPFData spfd

public export
SPFelemCatObj : {dom, cod : Type} -> SliceObj (SPFData dom cod)
SPFelemCatObj {dom} {cod} = Sigma {a=(SliceObj dom)} . SPFelem {dom} {cod}

public export
record SPFelemCatMor {dom, cod : Type}
    (f : SPFData dom cod) (elx, ely : SPFelemCatObj {dom} {cod} f) where
  constructor SPelM
  spelM : SliceMorphism {a=dom} (fst elx) (fst ely)
  spelEq : FunExt ->
    (snd ely) =
    (\ec => InterpSPFDataMap f (fst elx) (fst ely) spelM ec (DPair.snd elx ec))

public export
SPelMc : {dom, cod : Type} -> {f : SPFData dom cod} -> {x, y : SliceObj dom} ->
  (el : SPFelem {dom} {cod} f x) -> (m : SliceMorphism {a=dom} x y) ->
  SPFelemCatMor {dom} {cod}
    f (x ** el) (y ** \ec => InterpSPFDataMap f x y m ec (el ec))
SPelMc {dom} {cod} {f} {x} {y} el m = SPelM m $ \fext => funExt $ \ec => Refl

public export
SPFelemCatId : {dom, cod : Type} -> (f : SPFData dom cod) ->
  IntIdSig (SPFelemCatObj {dom} {cod} f) (SPFelemCatMor {dom} {cod} f)
SPFelemCatId {dom} {cod} f el =
  case el of
    (x ** e) =>
      SPelM (SliceId dom x) $ \fext =>
        funExt $ \ec => rewrite (dpEqPat {dp=(e ec)}) in
          dpEq12 Refl $ funExt $ \ed => Refl

public export
SPFelemCatComp : {dom, cod : Type} -> (f : SPFData dom cod) ->
  IntCompSig (SPFelemCatObj {dom} {cod} f) (SPFelemCatMor {dom} {cod} f)
SPFelemCatComp {dom} {cod} f (sx ** elx) (sy ** ely) (sz ** elz)
  (SPelM m' meq') (SPelM m meq) =
    SPelM
      (sliceComp {a=dom} m' m)
      (\fext => funExt $ \ez => rewrite (dpEqPat {dp=(elz ez)}) in
        dpEq12
          (rewrite fcongdep {x=ez} (meq' fext) in
           rewrite fcongdep {x=ez} (meq fext) in
           Refl)
          (rewrite fcongdep {x=ez} (meq' fext) in
           rewrite fcongdep {x=ez} (meq fext) in
           funExt $ \ed => Refl))

public export
SPFelemCatICS : {dom, cod : Type} -> (f : SPFData dom cod) ->
  IdCompSig (SPFelemCatObj f) (SPFelemCatMor f)
SPFelemCatICS f = ICS (SPFelemCatId f) (SPFelemCatComp f)

public export
SPFelemCatMICS : {dom, cod : Type} -> (f : SPFData dom cod) ->
  MorIdCompSig (SPFelemCatObj f)
SPFelemCatMICS f = MICS (SPFelemCatMor f) (SPFelemCatICS f)

public export
SPFelemCat : {dom, cod : Type} -> (f : SPFData dom cod) -> IntCatSig
SPFelemCat f = ICat (SPFelemCatObj f) (SPFelemCatMICS f)

--------------------------------------
--------------------------------------
---- Vertical-Cartesian factoring ----
--------------------------------------
--------------------------------------

-- The positions of the intermediate object of the vertical-Cartesian
-- factoring of a natural transformation between slice polynomial functors.
-- Note that this is independent of the specific natural transformation,
-- because the first part of the factorization is a vertical transformation,
-- whose on-positions function is an isomorphism, so the positions of the
-- intermediate functor must be the same as the positions of the first
-- functor.
public export
SPFDvcFactPos : {dom, cod : Type} -> {p, q : SPFData dom cod} ->
  SPFnt {dom} {cod} p q -> SliceObj cod
SPFDvcFactPos {dom} {cod} {p} {q} nt = spfdPos p

-- Given a polynomial functor, a slice of a codomain, and a morphism
-- from that slice to the functor's positions, we can produce a new
-- functor whose positions are the given slice and whose directions
-- are inherited from the given functor via the given morphism.
public export
SPFDposChangeDir : {dom, cod : Type} ->
  (p : SPFData dom cod) -> {pos : SliceObj cod} ->
  SliceMorphism {a=cod} pos (spfdPos p) -> SPFdirType dom cod pos
SPFDposChangeDir {dom} {cod} p {pos} m ec = spfdDir p ec . m ec

public export
SPFDposChange : {dom, cod : Type} ->
  (p : SPFData dom cod) -> {pos : SliceObj cod} ->
  SliceMorphism {a=cod} pos (spfdPos p) -> SPFData dom cod
SPFDposChange {dom} {cod} p {pos} m = SPFD pos (SPFDposChangeDir p {pos} m)

-- Given a natural transformation between slice polynomial functors,
-- this is the intermediate object of its vertical-Cartesian factoring.
-- Note that this is independent of the on-directions function of the
-- natural transformation -- that comes into play only to compute the
-- on-directions function of the vertical component of the factorization,
-- not to compute the intermediate object itself.
public export
SPFDvcFactIntObj : {dom, cod : Type} -> {p, q : SPFData dom cod} ->
  (nt : SPFnt {dom} {cod} p q) -> SPFData dom cod
SPFDvcFactIntObj {dom} {cod} {p} {q} nt =
  SPFDposChange {dom} {cod} q {pos=(spfdPos p)} (spOnPos nt)

public export
SPFDvcFactIntDir : {dom, cod : Type} -> {p, q : SPFData dom cod} ->
  (nt : SPFnt {dom} {cod} p q) ->
  SPFdirType dom cod (SPFDvcFactPos {dom} {cod} {p} {q} nt)
SPFDvcFactIntDir {dom} {cod} {p} {q} nt =
  spfdDir (SPFDvcFactIntObj {dom} {cod} {p} {q} nt)

-- The total directions of the intermediate object of the factorization
-- of a natural transformation.
public export
SPFDvcFactIntTot : {dom, cod : Type} -> {p, q : SPFData dom cod} ->
  SPFnt {dom} {cod} p q -> dom -> cod -> Type
SPFDvcFactIntTot {dom} {cod} {p} {q} nt = SPFDtot (SPFDvcFactIntObj nt)

public export
SPFDvcFactIntTotDom : {dom, cod : Type} -> {p, q : SPFData dom cod} ->
  SPFnt {dom} {cod} p q -> dom -> Type
SPFDvcFactIntTotDom {dom} {cod} {p} {q} nt = SPFDtotDom (SPFDvcFactIntObj nt)

public export
SPFDvcFactIntTotCod : {dom, cod : Type} -> {p, q : SPFData dom cod} ->
  SPFnt {dom} {cod} p q -> cod -> Type
SPFDvcFactIntTotCod {dom} {cod} {p} {q} nt = SPFDtotCod (SPFDvcFactIntObj nt)

-- The first (vertical) component of the factorization of a slice polynomial
-- natural transformation.
--
-- A vertical transformation is characterized by its on-positions function
-- being an isomorphism.
public export
0 SPFDvertNTcod : {dom, cod : Type} -> SPFData dom cod -> Type
SPFDvertNTcod {dom} {cod} p = SPFdirType dom cod (spfdPos p)

public export
SPFDfromVertNTcod : {dom, cod : Type} -> (p : SPFData dom cod) ->
  SPFDvertNTcod p -> SPFData dom cod
SPFDfromVertNTcod {dom} {cod} p = SPFD (spfdPos p)

public export
SPFDvertNT : {dom, cod : Type} ->
  (p : SPFData dom cod) -> SPFDvertNTcod {dom} {cod} p -> Type
SPFDvertNT {dom} {cod} p dir =
  SPFntDir p (SPFDfromVertNTcod p dir) (sliceId {a=cod} $ spfdPos p)

public export
SPFntFromVert : {dom, cod : Type} ->
  {p : SPFData dom cod} -> {dir : SPFdirType dom cod (spfdPos p)} ->
  SPFDvertNT {dom} {cod} p dir -> SPFnt {dom} {cod} p (SPFDfromVertNTcod p dir)
SPFntFromVert {dom} {cod} {p} {dir} vnt =
  SPFDm (sliceId {a=cod} $ spfdPos p) vnt

public export
SPFDvertFact : {dom, cod : Type} -> {p, q : SPFData dom cod} ->
  (nt : SPFnt {dom} {cod} p q) ->
  SPFnt {dom} {cod} p (SPFDvcFactIntObj {dom} {cod} {p} {q} nt)
SPFDvertFact {dom} {cod} {p} {q} nt =
  SPFntFromVert {dom} {cod} {p} {dir=(SPFDvcFactIntDir nt)} (spOnDir nt)

-- The second (Cartesian) component of the factorization of a slice polynomial
-- natural transformation.
--
-- A Cartesian transformation is characterized by its on-directions functions
-- all being isomorphisms.
public export
SPFDcartNT : {dom, cod : Type} -> SliceObj cod -> SPFData dom cod -> Type
SPFDcartNT {dom} {cod} pos q = SliceMorphism {a=cod} pos (spfdPos q)

public export
SPFntCartFactDir : {dom, cod : Type} ->
  {p : SliceObj cod} -> {q : SPFData dom cod} ->
  (cnt : SPFDcartNT {dom} {cod} p q) ->
  SPFntDir {dom} {cod} (SPFDposChange {dom} {cod} {pos=p} q cnt) q cnt
SPFntCartFactDir {dom} {cod} {p} {q} cnt ec ep =
  sliceId {a=dom} $ spfdDir q ec (cnt ec ep)

public export
SPFntFromCart : {dom, cod : Type} ->
  {p : SliceObj cod} -> {q : SPFData dom cod} ->
  (cnt : SPFDcartNT {dom} {cod} p q) ->
  SPFnt {dom} {cod} (SPFDposChange {dom} {cod} {pos=p} q cnt) q
SPFntFromCart {dom} {cod} {p} {q} cnt =
  SPFDm cnt (SPFntCartFactDir {dom} {cod} {p} {q} cnt)

public export
SPFDcartFact : {dom, cod : Type} -> {p, q : SPFData dom cod} ->
  (nt : SPFnt {dom} {cod} p q) ->
  SPFnt {dom} {cod} (SPFDvcFactIntObj {dom} {cod} {p} {q} nt) q
SPFDcartFact {dom} {cod} {p} {q} nt =
  SPFntFromCart {dom} {cod} {p=(spfdPos p)} {q} (spOnPos nt)

----------------------------------------------
---- Natural transformations from factors ----
----------------------------------------------

-- Because any natural transformation can be factored into a vertical
-- followed by a Cartesian transformation, we can also _define_ any
-- natural transformation as a composite of a vertical one followed
-- by a Cartesian one.  Indeed, as shown here, that is effectively
-- what `SPFnt` does.
public export
SPFDfact : {dom, cod : Type} -> IntMorSig (SPFData dom cod)
SPFDfact {dom} {cod} f g =
  DPair (SPFDcartNT (spfdPos f) g) (SPFDvertNT f . SPFDposChangeDir g)

public export
SPntFromFact : {dom, cod : Type} -> {p, q : SPFData dom cod} ->
  SPFDfact {dom} {cod} p q -> SPFnt {dom} {cod} p q
SPntFromFact {dom} {cod} {p} {q} (cart ** vert) = SPFDm cart vert

--------------------------
---- Cartesian slices ----
--------------------------

-- For a given functor `p`, an object of its Cartesian-slice category is a
-- functor with a Cartesian transformation to it.
--
-- The constraint that the transformation must be Cartesian means
-- that the on-directions function is determined completely by an
-- on-positions function.  Furthermore, in this formulation, we
-- specify the on-positions function as a projection of a slice
-- object of the positions.  Hence, a Cartesian slice is determined
-- simply by a slice object of the positions.  This can be seen from
-- the type signature of `SPFDcartNT` -- a Cartesian transformation
-- _into_ an `SPFData` is determined by a slice of the codomain and a
-- morphism from that to the positions of the `SPFData`, which is
-- the definition of a slice object of the positions.
public export
SPFDcartSl : {dom, cod : Type} -> SPFData dom cod -> Type
SPFDcartSl = SPFDbaseSl

public export
SPFDcartSlPos : {dom, cod : Type} ->
  (p : SPFData dom cod) -> SPFDcartSl p ->
  SliceObj cod
SPFDcartSlPos {dom} {cod} p csl ec = Sigma {a=(spfdPos p ec)} (curry csl ec)

public export
SPFDcartSltoNT : {dom, cod : Type} ->
  (p : SPFData dom cod) -> (sl : SPFDcartSl {dom} {cod} p) ->
  SPFDcartNT {dom} {cod} (SPFDcartSlPos {dom} {cod} p sl) p
SPFDcartSltoNT p sl ec = DPair.fst

public export
SPFDcartSlTot : {dom, cod : Type} ->
  (p : SPFData dom cod) -> SPFDcartSl p ->
  SPFData dom cod
SPFDcartSlTot {dom} {cod} p csl =
  SPFD
    (SPFDcartSlPos {dom} {cod} p csl)
    (\ec, ep, ed => spfdDir p ec (fst ep) ed)

public export
SPFDcartSlProjOnPos : {dom, cod : Type} ->
  (p : SPFData dom cod) -> (csl : SPFDcartSl p) ->
  SPFntPos (SPFDcartSlTot p csl) p
SPFDcartSlProjOnPos {dom} {cod} p csl ec = DPair.fst

public export
SPFDcartSlProj : {dom, cod : Type} ->
  (p : SPFData dom cod) -> (csl : SPFDcartSl p) ->
  SPFnt (SPFDcartSlTot p csl) p
SPFDcartSlProj {dom} {cod} p csl =
  SPFDm
    (SPFDcartSlProjOnPos p csl)
    (\ec, ep => sliceId {a=dom} $ spfdDir p ec (fst ep))

---------------------------
---- Vertical coslices ----
---------------------------

-- For a given functor `p`, an object of its vertical-coslice category is a
-- functor with a vertical transformation from it.
--
-- The constraint that the transformation must be vertical means
-- that it can be determined purely by a slice of the directions
-- of the domain functor.

public export
SPFDvertCosl : {dom, cod : Type} -> SPFData dom cod -> Type
SPFDvertCosl {dom} {cod} p = SliceObj (SPFDdirTot p)

public export
SPFDvertCoslDir : {dom, cod : Type} ->
  (p : SPFData dom cod) -> SPFDvertCosl p -> SPFDvertNTcod {dom} {cod} p
SPFDvertCoslDir {dom} {cod} p csl ec ep ed =
  (dd : spfdDir p ec ep ed ** csl ((ed, (ec ** ep)) ** dd))

public export
SPFDvertCoslToNT : {dom, cod : Type} ->
  (p : SPFData dom cod) -> (csl : SPFDvertCosl {dom} {cod} p) ->
  SPFDvertNT {dom} {cod} p (SPFDvertCoslDir {dom} {cod} p csl)
SPFDvertCoslToNT p csl ec ep ed = DPair.fst

public export
SPFDvertCoslCod : {dom, cod : Type} ->
  (p : SPFData dom cod) -> SPFDvertCosl {dom} {cod} p -> SPFData dom cod
SPFDvertCoslCod {dom} {cod} p csl =
  SPFD (spfdPos p) (SPFDvertCoslDir {dom} {cod} p csl)

public export
SPFDvertCoslInj : {dom, cod : Type} ->
  (p : SPFData dom cod) -> (dir : SPFDvertCosl {dom} {cod} p) ->
  SPFnt p (SPFDvertCoslCod {dom} {cod} p dir)
SPFDvertCoslInj {dom} {cod} p dir =
  SPFDm (sliceId {a=cod} $ spfdPos p) (SPFDvertCoslToNT {dom} {cod} p dir)

---------------------------------------------------
---- Vertical-Cartesian factorization of cells ----
---------------------------------------------------

public export
SPFDvertPoCell : {w, w', z : Type} ->
  (bcl : w -> w') -> (f : SPFData w z) ->
  SPFdirType w' z (spfdPos f) -> Type
SPFDvertPoCell {w} {w'} {z} bcl f =
  SPFDvertNT (spfPushoutDir {w} {x=w'} {z} bcl f)

public export
SPFDcartPbCell : {w, z, z' : Type} ->
  (bcr : z -> z') -> (g : SPFData w z') -> (f : SliceObj z) -> Type
SPFDcartPbCell {w} {z} {z'} bcr g f =
  SPFDcartNT {dom=w} {cod=z} f (spfPullbackPos bcr g)

public export
SPFDcartPoCell : {w, z, z' : Type} ->
  (bcr : z -> z') -> (g : SPFData w z') -> (f : SliceObj z) -> Type
SPFDcartPoCell {w} {z} {z'} bcr g f =
  SPFDcartNT {dom=w} {cod=z'} (SliceFibSigmaF bcr f) g

public export
SPFDcartCellPbToPo : {w, z, z' : Type} ->
  {bcr : z -> z'} -> {g : SPFData w z'} -> {f : SliceObj z} ->
  SPFDcartPbCell {w} {z} {z'} bcr g f ->
  SPFDcartPoCell {w} {z} {z'} bcr g f
SPFDcartCellPbToPo {w} {z} {z'} {bcr} {g} {f} pbc _ (SFS ez efz) =
  pbc ez efz

public export
SPFDcartCellPoToPb : {w, z, z' : Type} ->
  {bcr : z -> z'} -> {g : SPFData w z'} -> {f : SliceObj z} ->
  SPFDcartPoCell {w} {z} {z'} bcr g f ->
  SPFDcartPbCell {w} {z} {z'} bcr g f
SPFDcartCellPoToPb {w} {z} {z'} {bcr} {g} {f} poc ez efz =
  poc (bcr ez) $ SFS ez efz

public export
SPFCposChangeDirPB : {w, z, z' : Type} ->
  {bcr : z -> z'} -> {g : SPFData w z'} -> {f : SliceObj z} ->
  SPFDcartPbCell {w} {z} {z'} bcr g f -> SPFdirType w z f
SPFCposChangeDirPB {w} {z} {z'} {bcr} {g} {f} =
  SPFDposChangeDir {dom=w} {cod=z} (spfPullbackPos bcr g) {pos=f}

public export
SPFCposChangeDir : {w, z, z' : Type} ->
  {bcr : z -> z'} -> {g : SPFData w z'} -> {f : SliceObj z} ->
  SPFDcartPoCell {w} {z} {z'} bcr g f -> SPFdirType w z f
SPFCposChangeDir {w} {z} {z'} {bcr} {g} {f} onpos =
  SPFCposChangeDirPB {w} {z} {z'} {bcr} {g} {f} $
    \ez, efz => onpos (bcr ez) (SFS ez efz)

public export
SPFCposChangePB : {w, z, z' : Type} ->
  {bcr : z -> z'} -> {g : SPFData w z'} -> {f : SliceObj z} ->
  SPFDcartPbCell {w} {z} {z'} bcr g f -> SPFData w z
SPFCposChangePB {w} {z} {z'} {bcr} {g} {f} onpos =
  SPFD f (SPFCposChangeDirPB {w} {z} {z'} {bcr} {g} {f} onpos)

public export
SPFCposChange : {w, z, z' : Type} ->
  {bcr : z -> z'} -> {g : SPFData w z'} -> {f : SliceObj z} ->
  SPFDcartPoCell {w} {z} {z'} bcr g f -> SPFData w z
SPFCposChange {w} {z} {z'} {bcr} {g} {f} onpos =
  SPFD f (SPFCposChangeDir {w} {z} {z'} {bcr} {g} {f} onpos)

-- We can also factorize a _cell_, first changing the domain together with
-- the directions (a vertical transformation) and then the codomain together
-- with the positions (a Cartesian transformation).
public export
SPFpoCellIntObj : {w, w', z, z' : Type} ->
  {bcl : w -> w'} -> {bcr : z -> z'} ->
  {f : SPFData w z} -> {g : SPFData w' z'} ->
  SPFpoCell {w} {w'} {z} {z'} bcl bcr f g ->
  SPFData w' z
SPFpoCellIntObj {w} {w'} {z} {z'} {bcl} {bcr} {f} {g} nt =
  SPFCposChange {w=w'} {z} {z'} {bcr} {g} {f=(spfdPos f)} (spOnPos nt)

public export
SPFpoCellVertFactPos : {w, w', z, z' : Type} ->
  {bcl : w -> w'} -> {bcr : z -> z'} ->
  {f : SPFData w z} -> {g : SPFData w' z'} ->
  (spfc : SPFpoCell {w} {w'} {z} {z'} bcl bcr f g) ->
  SPFntPos {dom=w'} {cod=z}
    (spfPushout bcl Prelude.id f)
    (SPFpoCellIntObj {w} {w'} {z} {z'} {bcl} {bcr} {f} {g} spfc)
SPFpoCellVertFactPos {w} {w'} {z} {z'} {bcl} {f} {g} spfc ez ep =
  case ep of SFS ez efp => efp

public export
SPFpoCellVertFactDir : {w, w', z, z' : Type} ->
  {bcl : w -> w'} -> {bcr : z -> z'} ->
  {f : SPFData w z} -> {g : SPFData w' z'} ->
  (spfc : SPFpoCell {w} {w'} {z} {z'} bcl bcr f g) ->
  SPFntDir {dom=w'} {cod=z}
    (spfPushout bcl Prelude.id f)
    (SPFpoCellIntObj {w} {w'} {z} {z'} {bcl} {bcr} {f} {g} spfc)
    (SPFpoCellVertFactPos {w} {w'} {z} {z'} {bcl} {f} {g} spfc)
SPFpoCellVertFactDir {w} {w'} {z} {z'} {bcl} {f} {g} spfc ez ep =
  case ep of SFS ez efp => spOnDir spfc (bcr ez) (SFS ez efp)

public export
SPFpoCellVertFact : {w, w', z, z' : Type} ->
  {bcl : w -> w'} -> {bcr : z -> z'} ->
  {f : SPFData w z} -> {g : SPFData w' z'} ->
  (spfc : SPFpoCell {w} {w'} {z} {z'} bcl bcr f g) ->
  SPFpoCell {w} {w'} {z} {z'=z} bcl Prelude.id f (SPFpoCellIntObj {f} {g} spfc)
SPFpoCellVertFact {w} {w'} {z} {z'} {bcl} {bcr} {f} {g} spfc =
  SPFDm
    (SPFpoCellVertFactPos {w} {w'} {z} {z'} {bcl} {bcr} {f} {g} spfc)
    (SPFpoCellVertFactDir {w} {w'} {z} {z'} {bcl} {bcr} {f} {g} spfc)

public export
SPFpoCellCartFactPos : {w, w', z, z' : Type} ->
  {bcl : w -> w'} -> {bcr : z -> z'} ->
  {f : SPFData w z} -> {g : SPFData w' z'} ->
  (spfc : SPFpoCell {w} {w'} {z} {z'} bcl bcr f g) ->
  SPFntPos {dom=w'} {cod=z'}
    (spfPushout Prelude.id bcr $
      SPFpoCellIntObj {w} {w'} {z} {z'} {bcl} {bcr} {f} {g} spfc)
    g
SPFpoCellCartFactPos {w} {w'} {z} {z'} {bcl} {f} {g} spfc = spOnPos spfc

public export
SPFpoCellCartFactDir : {w, w', z, z' : Type} ->
  {bcl : w -> w'} -> {bcr : z -> z'} ->
  {f : SPFData w z} -> {g : SPFData w' z'} ->
  (spfc : SPFpoCell {w} {w'} {z} {z'} bcl bcr f g) ->
  SPFntDir {dom=w'} {cod=z'}
    (spfPushout Prelude.id bcr $
      SPFpoCellIntObj {w} {w'} {z} {z'} {bcl} {bcr} {f} {g} spfc)
    g
    (SPFpoCellCartFactPos {w} {w'} {z} {z'} {bcl} {f} {g} spfc)
SPFpoCellCartFactDir {w} {w'} {z} {z'} {bcl} {f} {g} spfc ez' ep ew' egd =
  case ep of SFS ez efp => SFS ew' egd

public export
SPFpoCellCartFact : {w, w', z, z' : Type} ->
  {bcl : w -> w'} -> {bcr : z -> z'} ->
  {f : SPFData w z} -> {g : SPFData w' z'} ->
  (spfc : SPFpoCell {w} {w'} {z} {z'} bcl bcr f g) ->
  SPFpoCell {w=w'} {w'} {z} {z'} Prelude.id bcr (SPFpoCellIntObj {f} {g} spfc) g
SPFpoCellCartFact {w} {w'} {z} {z'} {bcl} {bcr} {f} {g} spfc =
  SPFDm
    (SPFpoCellCartFactPos {w} {w'} {z} {z'} {bcl} {bcr} {f} {g} spfc)
    (SPFpoCellCartFactDir {w} {w'} {z} {z'} {bcl} {bcr} {f} {g} spfc)

public export
SPFpoCellFactCorrectPos : FunExt -> {w, w', z, z' : Type} ->
  {bcl : w -> w'} -> {bcr : z -> z'} ->
  {f : SPFData w z} -> {g : SPFData w' z'} ->
  (spfc : SPFpoCell {w} {w'} {z} {z'} bcl bcr f g) ->
  (ez' : z') -> (efp : spfdPos (spfPushout bcl bcr f) ez') ->
  spOnPos
    (spocVcomp {f} {g=(SPFpoCellIntObj {f} {g} spfc)} {h=g}
      (SPFpoCellCartFact {f} {g} spfc)
      (SPFpoCellVertFact {f} {g} spfc))
    ez' efp
  = spOnPos spfc ez' efp
SPFpoCellFactCorrectPos fext {w} {w'} {z} {z'} {bcl} {bcr}
  {f=(SPFD fpos fdir)} {g=(SPFD gpos gdir)}
  (SPFDm onpos ondir) _ (SFS ez efp) =
    Refl

-----------------------------------------------------
-----------------------------------------------------
---- Two-slices of dependent polynomial functors ----
-----------------------------------------------------
-----------------------------------------------------

-- A cell is a two-morphism, so we can define a slice category over
-- a dependent polynomial functor as any other dependent polynomial
-- functor (the total space), which need not have the same domain or
-- codomain as the base functor, with a cell (the projection) to the
-- base functor.

-- A dependent-type-style cell, where we treat the natural transformation
-- as the projection of a slice object.
public export
record SPFpoCellDP {w', z' : Type} {w : SliceObj w'} {z : SliceObj z'}
    (f : SPFData (Sigma {a=w'} w) (Sigma {a=z'} z)) (g : SPFData w' z')
    where
  constructor SPDC
  spdcCart :
    SPFDcartPoCell {w=w'} {z=(Sigma {a=z'} z)} {z'}
      DPair.fst
      g
      (spfdPos f)
  spdcVert :
    SPFDvertPoCell {w=(Sigma {a=w'} w)} {w'} {z=(Sigma {a=z'} z)}
      DPair.fst
      f
      (SPFCposChangeDir
        {w=w'} {z=(Sigma {a=z'} z)} {z'}
        {bcr=(DPair.fst)} {g} {f=(spfdPos f)}
        spdcCart)

public export
SPFpoCellFromDP : {w', z' : Type} -> {w : SliceObj w'} -> {z : SliceObj z'} ->
  {f : SPFData (Sigma {a=w'} w) (Sigma {a=z'} z)} -> {g : SPFData w' z'} ->
  SPFpoCellDP {w'} {z'} {w} {z} f g ->
  SPFpoCell {w=(Sigma {a=w'} w)} {w'} {z=(Sigma {a=z'} z)} {z'}
    DPair.fst DPair.fst f g
SPFpoCellFromDP {w'} {z'} {w} {z} {f} {g} spfc =
  SPFDm
    (\ez', (SFS (ez' ** ez) efp) => spdcCart spfc ez' (SFS (ez' ** ez) efp))
    (\ez', (SFS (ez' ** ez) efp) => spdcVert spfc (ez' ** ez) efp)

----------------------------
---- Cartesian 2-slices ----
----------------------------

public export
SPFDcart2Sl : {w, z' : Type} -> SPFData w z' -> Type
SPFDcart2Sl {w} {z'} spfd =
  (csl : SliceObj z' ** (ez' : z') -> spfdPos spfd ez' -> SliceObj (csl ez'))

public export
SPFDcart2SlCod : {w, z' : Type} ->
  (spfd : SPFData w z') -> SPFDcart2Sl spfd -> Type
SPFDcart2SlCod {w} {z'} spfd sl = Sigma {a=z'} (fst sl)

public export
SPFDcart2SlTot : {w, z' : Type} ->
  (spfd : SPFData w z') -> (sl : SPFDcart2Sl {w} {z'} spfd) ->
  SPFData w (SPFDcart2SlCod {w} {z'} spfd sl)
SPFDcart2SlTot {w} {z'} spfd sl =
  SPFD
    (\ez => (ep : spfdPos spfd (fst ez) ** snd sl (fst ez) ep (snd ez)))
    (\ez, ep => spfdDir spfd (fst ez) (fst ep))

public export
SPFDcart2SlProj : {w, z' : Type} ->
  (spfd : SPFData w z') -> (sl : SPFDcart2Sl {w} {z'} spfd) ->
  SPFpoCell {w} {z=(SPFDcart2SlCod {w} {z'} spfd sl)} {w'=w} {z'}
    Prelude.id DPair.fst
    (SPFDcart2SlTot {w} {z'} spfd sl) spfd
SPFDcart2SlProj {w} {z'} spfd sl =
  SPFDm
    (\ez', ec => rewrite sym (sfsEq ec) in fst $ sfsSnd ec)
    (\ez', ep, ew, dd => rewrite sfsEq ep in SFS ew dd)

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---- Internal language of double-category of slice polynomial functors ----
---------------------------------------------------------------------------
---------------------------------------------------------------------------

------------------------------------------------------------------------------
---- Definitions of dependent families of `SPFData`, `SPFnt`, `SPFpoCell` ----
------------------------------------------------------------------------------

public export
SPFParamData : {b : Type} -> SliceObj b -> SliceObj b -> SliceObj b
SPFParamData {b} dom cod eb = SPFData (dom eb) (cod eb)

public export
SPFDataFam : {b : Type} -> (dom, cod : SliceObj b) -> Type
SPFDataFam {b} dom cod = Pi {a=b} $ SPFParamData {b} dom cod

-- Alias for non-dependent version of `SPFDataFam`.
public export
SPFndDataFam : Type -> Type -> Type -> Type
SPFndDataFam b dom cod = SPFDataFam {b} (\_ => dom) (\_ => cod)

public export
SPFamData : {b : Type} -> (dom, cod : SliceObj b) -> Type
SPFamData {b} dom cod = SPFData (Sigma {a=b} dom) (Sigma {a=b} cod)

public export
SPFDataFamPos : {b : Type} -> {dom, cod : SliceObj b} ->
  SPFDataFam {b} dom cod -> (eb : b) -> SliceObj (cod eb)
SPFDataFamPos {b} {dom} {cod} sf i = spfdPos (sf i)

public export
SPFDataFamDir : {b : Type} -> {dom, cod : SliceObj b} ->
  (sf : SPFDataFam {b} dom cod) -> (eb : b) ->
  SPFdirType (dom eb) (cod eb) (SPFDataFamPos sf eb)
SPFDataFamDir {b} {dom} {cod} sf i = spfdDir (sf i)

public export
SPFdepNTfam : {b : Type} -> {dom, cod : SliceObj b} ->
  (f, g : SPFDataFam {b} dom cod) -> Type
SPFdepNTfam {b} {dom} {cod} f g =
  Pi {a=b} (\eb => SPFnt {dom=(dom eb)} {cod=(cod eb)} (f eb) (g eb))

public export
SPFpoCellFam : {b : Type} -> {w, w', z, z' : SliceObj b} ->
  (bcl : SliceMorphism {a=b} w w') -> (bcr : SliceMorphism {a=b} z z') ->
  (f : SPFDataFam w z) -> (g : SPFDataFam w' z') ->
  Type
SPFpoCellFam {b} {w} {w'} {z} {z'} bcl bcr f g =
  Pi {a=b} $
    \eb =>
      SPFpoCell
        {w=(w eb)} {w'=(w' eb)} {z=(z eb)} {z'=(z' eb)}
        (bcl eb) (bcr eb) (f eb) (g eb)

----------------------------------
---- Embedding into `SPFData` ----
----------------------------------

public export
SPFCtot : {b : Type} -> {dom, cod : SliceObj b} ->
  SPFDataFam {b} dom cod -> SPFamData {b} dom cod
SPFCtot {b} {dom} {cod} sf =
  SPFD
    (\ebc =>
      (spfdPos (sf $ fst ebc) (snd ebc)))
    (\ebc, ep, ebd =>
      (eqb : fst ebc = fst ebd **
       spfdDir (sf $ fst ebc) (snd ebc) ep (rewrite eqb in snd ebd)))

public export
SPFCslice : {b : Type} -> {dom, cod : SliceObj b} ->
  SPFamData {b} dom cod -> SPFDataFam {b} dom cod
SPFCslice {b} {dom} {cod} sf eb =
  SPFD
    (\ec => spfdPos sf (eb ** ec))
    (\ec, ep, ed => spfdDir sf (eb ** ec) ep (eb ** ed))

-- This adjunction exhibits `SPFDataFam {b} dom cod` as a subcategory of
-- `SPFamData {b} dom cod`, which is simply a name for the category
-- `SPFData (Sigma {a=b} dom) (Sigma {a=b} cod)`.

public export
SPFCsliceTotCounit : {b : Type} -> {dom, cod : SliceObj b} ->
  (sf : SPFDataFam {b} dom cod) ->
  SPFdepNTfam {b} {dom} {cod} (SPFCslice $ SPFCtot sf) sf
SPFCsliceTotCounit {b} {dom} {cod} sf eb =
  SPFDm (\_ => id) (\ec, ep, ed, dd => (Refl ** dd))

public export
SPFCsliceTotUnit : {b : Type} -> {dom, cod : SliceObj b} ->
  (spfd : SPFamData {b} dom cod) ->
  SPFnt spfd (SPFCtot $ SPFCslice spfd)
SPFCsliceTotUnit {b} {dom} {cod} spfd =
  SPFDm
    (\(eb ** ec), ep => ep)
    (\(eb ** ec), ep, (eb ** ed), (Refl ** dd) => dd)

---------------------
---- Quantifiers ----
---------------------

-------------------------------------
---- Non-dependent special cases ----
-------------------------------------

-- A `b`-way family of `SPFData dom cod`s is equivalent to a single
-- `SPFData dom (b, cod)`.

public export
SPFDataFamToProd : {b, dom, cod : Type} ->
  (SPFndDataFam b dom cod) -> SPFData dom (b, cod)
SPFDataFamToProd {b} {dom} {cod} sf =
  SPFD
    (uncurry (spfdPos . sf))
    (\ebc => case ebc of (eb, ec) => spfdDir (sf eb) ec)

public export
SPFDataProdToFam : {b, dom, cod : Type} ->
  SPFData dom (b, cod) -> (SPFndDataFam b dom cod)
SPFDataProdToFam {b} {dom} {cod} spfd eb =
  SPFD
    (curry (spfdPos spfd) eb)
    (\ec => spfdDir spfd (eb, ec))

public export
SPFDataFamToProdUnit : {dom, cod : Type} ->
  (cod -> SPFData dom Unit) -> SPFData dom cod
SPFDataFamToProdUnit {dom} {cod} sf with
    (SPFDataFamToProd {b=cod} {dom} {cod=Unit} sf)
  SPFDataFamToProdUnit {dom} {cod} sf | (SPFD pos dir) =
    SPFD (pos . flip MkPair ()) (\ec => dir (ec, ()))

public export
SPFDataFamToProdUnitNT : {dom, cod : Type} ->
  (sf, sf' : cod -> SPFData dom Unit) ->
  ((ec : cod) -> SPFnt (sf ec) (sf' ec)) ->
  SPFnt (SPFDataFamToProdUnit sf) (SPFDataFamToProdUnit sf')
SPFDataFamToProdUnitNT {dom} {cod} sf sf' ntf =
  SPFDm (\ec => spOnPos (ntf ec) ()) (\ec => spOnDir (ntf ec) ())

public export
SPFDataProdToFamUnit : {dom, cod : Type} ->
  SPFData dom cod -> (cod -> SPFData dom Unit)
SPFDataProdToFamUnit {dom} {cod} sf =
  SPFDataProdToFam {b=cod} {dom} {cod=Unit} $
    SPFD (spfdPos sf . fst) (\ec => spfdDir sf (fst ec))

public export
SPFDataProdToFamUnitNT : {dom, cod : Type} ->
  (sf, sf' : SPFData dom cod) -> SPFnt sf sf' ->
  (ec : cod) ->
  SPFnt {dom} {cod=Unit}
    (SPFDataProdToFamUnit sf ec)
    (SPFDataProdToFamUnit sf' ec)
SPFDataProdToFamUnitNT {dom} {cod} sf sf' nt ec =
  SPFDm (\_ => spOnPos nt ec) (\_ => spOnDir nt ec)

public export
SPFDataFamForall : {b, dom, cod : Type} ->
  (SPFndDataFam b dom cod) -> SPFData dom cod
SPFDataFamForall {b} {dom} {cod} =
  spfdPostcompPi {x=dom} {y=(b, cod)} {z=cod} snd
  . SPFDataFamToProd {b} {dom} {cod}

public export
SPFDataFamForallToInterp : {b, dom, cod : Type} ->
  (sf : SPFndDataFam b dom cod) ->
  SliceNatTrans {x=dom} {y=cod}
    (InterpSPFData {dom} {cod} $ SPFDataFamForall {b} {dom} {cod} sf)
    (\sd, ec => Pi {a=b} $ \eb => InterpSPFData {dom} {cod} (sf eb) sd ec)
SPFDataFamForallToInterp {b} {dom} {cod} sf sd ec ((() ** pm) ** dm) eb =
  (pm (eb, ec) Refl ** \ed, fd => dm ed (((eb, ec) ** Refl) ** fd))

public export
SPFDataFamForallFromInterp : {b, dom, cod : Type} ->
  (sf : SPFndDataFam b dom cod) ->
  SliceNatTrans {x=dom} {y=cod}
    (\sd, ec => Pi {a=b} $ \eb => InterpSPFData {dom} {cod} (sf eb) sd ec)
    (InterpSPFData {dom} {cod} $ SPFDataFamForall {b} {dom} {cod} sf)
SPFDataFamForallFromInterp {b} {dom} {cod} sf sd ec pdm =
  ((() ** \(eb, ec), Refl => fst $ pdm eb) **
   \ed, (((eb, ec) ** Refl) ** fd) => snd (pdm eb) ed fd)

public export
SPFDataFamExists : {b, dom, cod : Type} ->
  (SPFndDataFam b dom cod) -> SPFData dom cod
SPFDataFamExists {b} {dom} {cod} =
  spfdPostcompSigma {x=dom} {y=(b, cod)} {z=cod} snd
  . SPFDataFamToProd {b} {dom} {cod}

public export
SPFDataFamExistsToInterp : {b, dom, cod : Type} ->
  (sf : SPFndDataFam b dom cod) ->
  SliceNatTrans {x=dom} {y=cod}
    (InterpSPFData {dom} {cod} $ SPFDataFamExists {b} {dom} {cod} sf)
    (\sd, ec => Sigma {a=b} $ \eb => InterpSPFData {dom} {cod} (sf eb) sd ec)
SPFDataFamExistsToInterp {b} {dom} {cod} sf sd ec
  ((SFS (eb, ec) () ** pm) ** dm) =
    (eb ** (pm (eb, ec) Refl ** \ed, fd => dm ed (((eb, ec) ** Refl) ** fd)))

public export
SPFDataFamExistsFromInterp : {b, dom, cod : Type} ->
  (sf : SPFndDataFam b dom cod) ->
  SliceNatTrans {x=dom} {y=cod}
    (\sd, ec => Sigma {a=b} $ \eb => InterpSPFData {dom} {cod} (sf eb) sd ec)
    (InterpSPFData {dom} {cod} $ SPFDataFamExists {b} {dom} {cod} sf)
SPFDataFamExistsFromInterp {b} {dom} {cod} sf sd ec (eb ** ep ** dm) =
  ((SFS (eb, ec) () ** \(eb, ec), Refl => ep) **
   (\ed, (((eb, ec) ** Refl) ** fd) => dm ed fd))

------------------------------------------------
---- Slice-of-slice version of `SPFdirType` ----
------------------------------------------------

-- Suppose the following:
--
--   - `b : Type`
--   - `domsl : SliceObj b` where `dom ~=~ Sigma {a=b} domsl`
--   - `codr : SliceObj b` where `cod ~=~ Sigma {a=b} codr`
--   - `pos : SliceObj cod`
--     (~=~ `SliceObj (Sigma {a=b} codr)` ~=~ `(eb : b) -> codr eb -> Type`)
--
-- (Note that all `(dom, cod)` pairs can be put in this form:  we can take
-- `b := Unit`, `domsl := \() => dom`; codr := \() => cod.)
--
-- Then we can provide the following interface to `SPFdirType`:
public export
0 SPFdepDirType : {0 b : Type} ->
  (0 domsl, codr : SliceObj b) -> (0 pos : (eb : b) -> codr eb -> Type) -> Type
SPFdepDirType {b} domsl codr pos =
  (eb : b) -> (ec : codr eb) -> pos eb ec -> SliceObj (domsl eb)

-- We can convert an `SPFdepDirType` to an `SPFdirType`:
public export
data SPFdirFromDep : {0 b : Type} ->
    {0 domsl, codr : SliceObj b} -> {0 pos : (eb : b) -> codr eb -> Type} ->
    SPFdepDirType {b} domsl codr pos ->
    SPFdirType (Sigma {a=b} domsl) (Sigma {a=b} codr) (uncurry pos) where
  SPFdd : {0 b : Type} ->
    {0 domsl, codr : SliceObj b} -> {0 pos : (eb : b) -> codr eb -> Type} ->
    {0 dir : SPFdepDirType {b} domsl codr pos} ->
    (eb : b) -> (ec : codr eb) -> (ep : pos eb ec) -> (ed : domsl eb) ->
    dir eb ec ep ed ->
    SPFdirFromDep {b} {domsl} {codr} {pos} dir (eb ** ec) ep (eb ** ed)

-- The signature of `SPFdepDirType` allows us to define for each type `b`
-- a double category of slice polynomial functors whose objects are slice
-- objects of `Type` over `b`, whose vertical morphisms are slice morphisms
-- in `Type` over `b`, and whose horizontal morphisms are slice polynomial
-- functors using the dependent signature.  The cells are defined below as
-- `SPFdepPoCell`.
public export
record SPFdepData {0 b : Type} (dom, cod : SliceObj b) where
  constructor SPFDD
  spfddPos : (eb : b) -> cod eb -> Type
  spfddDir : SPFdepDirType {b} dom cod spfddPos

-- Now we see that an `SPFdepData` is simply a `b`-indexed dependent family
-- of `SPFData`s.

public export
SPFDataFamFromDep : {0 b : Type} -> {0 dom, cod : SliceObj b} ->
  SPFdepData {b} dom cod -> SPFDataFam {b} dom cod
SPFDataFamFromDep {b} {dom} {cod} spfdd eb =
  SPFD (spfddPos spfdd eb) (spfddDir spfdd eb)

public export
SPFDepFromDataFam : {0 b : Type} -> {0 dom, cod : SliceObj b} ->
  SPFDataFam {b} dom cod -> SPFdepData {b} dom cod
SPFDepFromDataFam {b} {dom} {cod} fam =
  SPFDD (\eb => spfdPos (fam eb)) (\eb => spfdDir (fam eb))

-- An `SPFdepData` can be compressed to an `SPFData`, although this loses
-- information compared to the `SPFdepData`/`SPFData`-family formulation
-- in that it erases the `b`-dependent connection between `dom` and `cod`.
public export
SPFDataFromDep : {0 b : Type} -> {0 dom, cod : SliceObj b} ->
  SPFdepData {b} dom cod -> SPFamData {b} dom cod
SPFDataFromDep {b} {dom} {cod} spfdd =
  SPFD (uncurry $ spfddPos spfdd) (SPFdirFromDep $ spfddDir spfdd)

-- The signature that this form of SPFD allows us to write makes the domain
-- and codomain themselves both dependent on a common type (`b`), thus allowing
-- us to express a _relationship_ between the dependent types of the domain
-- and codomain.
--
-- `InterpSPFdepData` and `InterpSPFdepDataMap` together may be viewed as
-- the object-map and morphism-map components of a functor from the discrete
-- category whose objects are the terms of `b` to the category of slice
-- polynomial functors whose domain and codomain are slices of `dom eb`
-- and `cod eb` respectively for each `eb : b`.
--
-- This is forgetful, compared to `InterpSPFdepDataEl`.
public export
InterpSPFdepData : {b : Type} -> {dom, cod : SliceObj b} ->
  SPFdepData {b} dom cod ->
  SliceFunctor (Sigma {a=b} dom) (Sigma {a=b} cod)
InterpSPFdepData {b} {dom} {cod} spfdd =
  InterpSPFData {dom=(Sigma {a=b} dom)} {cod=(Sigma {a=b} cod)}
    (SPFDataFromDep spfdd)

public export
InterpSPFdepDataEl : {b : Type} -> {dom, cod : SliceObj b} ->
  SPFdepData {b} dom cod ->
  (eb : b) -> SliceFunctor (dom eb) (cod eb)
InterpSPFdepDataEl {b} {dom} {cod} spfdd =
  piMap
    (\eb => InterpSPFData {dom=(dom eb)} {cod=(cod eb)})
    (SPFDataFamFromDep spfdd)

-- This is forgetful, compared to `InterpSPFdepDataMapEl`.
public export
InterpSPFdepDataMap : {b : Type} -> {dom, cod : SliceObj b} ->
  (spfdd : SPFdepData {b} dom cod) ->
  SliceFMap (InterpSPFdepData {b} {dom} {cod} spfdd)
InterpSPFdepDataMap {b} {dom} {cod} spfdd =
  InterpSPFDataMap {dom=(Sigma {a=b} dom)} {cod=(Sigma {a=b} cod)}
    (SPFDataFromDep spfdd)

public export
InterpSPFdepDataMapEl : {b : Type} -> {dom, cod : SliceObj b} ->
  (spfdd : SPFdepData {b} dom cod) ->
  (eb : b) -> SliceFMap (InterpSPFdepDataEl {b} {dom} {cod} spfdd eb)
InterpSPFdepDataMapEl {b} {dom} {cod} spfdd eb =
  InterpSPFDataMap {dom=(dom eb)} {cod=(cod eb)} (SPFDataFamFromDep spfdd eb)

public export
record SPFdepNT {0 b : Type} {dom, cod : SliceObj b}
    (f, g : SPFdepData {b} dom cod) where
  constructor SPFdnt
  spdOnPos :
    (eb : b) -> SliceMorphism {a=(cod eb)} (spfddPos f eb) (spfddPos g eb)
  spdOnDir : (eb : b) -> (ec : cod eb) ->
    (ep : spfddPos f eb ec) -> (ed : dom eb) ->
    spfddDir g eb ec (spdOnPos eb ec ep) ed ->
    spfddDir f eb ec ep ed

-- This is forgetful, using the forgetful `SPFdataFromDep`.
public export
SPFntFromDep : {0 b : Type} -> {0 dom, cod : SliceObj b} ->
  {0 f, g : SPFdepData {b} dom cod} ->
  SPFdepNT {b} f g -> SPFnt (SPFDataFromDep f) (SPFDataFromDep g)
SPFntFromDep {b} {dom} {cod} {f} {g} alpha =
  SPFDm
    (\ebc, efp => spdOnPos alpha (fst ebc) (snd ebc) efp)
    (\(eb ** ec), efp, (_ ** ed), (SPFdd _ _ _ _ dd) =>
      SPFdd eb ec efp ed $ spdOnDir alpha eb ec efp ed dd)

-- This is forgetful, compared to `InterpSPFdepNTel`.
public export
InterpSPFdepNT : {b : Type} -> {dom, cod : SliceObj b} ->
  (f, g : SPFdepData {b} dom cod) ->
  SPFdepNT f g ->
  SliceNatTrans {x=(Sigma {a=b} dom)} {y=(Sigma {a=b} cod)}
    (InterpSPFdepData f)
    (InterpSPFdepData g)
InterpSPFdepNT {b} {dom} {cod} f g alpha =
  InterpSPFnt (SPFDataFromDep f) (SPFDataFromDep g) (SPFntFromDep alpha)

-- Now we show that a `b`-dependent slice polynomial natural transformation
-- is just a `b`-indexed dependent family of slice polynomial natural
-- transformations.

public export
SPFntFamFromDep : {0 b : Type} -> {0 dom, cod : SliceObj b} ->
  {f, g : SPFdepData {b} dom cod} ->
  SPFdepNT {b} {dom} {cod} f g ->
  SPFdepNTfam {b} {dom} {cod} (SPFDataFamFromDep f) (SPFDataFamFromDep g)
SPFntFamFromDep {b} {dom} {cod} {f} {g} alpha eb =
  SPFDm (spdOnPos alpha eb) (spdOnDir alpha eb)

public export
SPFntDepFromFam : {0 b : Type} -> {0 dom, cod : SliceObj b} ->
  {f, g : SPFdepData {b} dom cod} ->
  SPFdepNTfam {b} {dom} {cod} (SPFDataFamFromDep f) (SPFDataFamFromDep g) ->
  SPFdepNT {b} {dom} {cod} f g
SPFntDepFromFam {b} {dom} {cod} {f} {g} fam =
  SPFdnt (\eb => spOnPos (fam eb)) (\eb => spOnDir (fam eb))

public export
InterpSPFdepNTel : {b : Type} -> {dom, cod : SliceObj b} ->
  (f, g : SPFdepData {b} dom cod) ->
  SPFdepNT f g ->
  (eb : b) ->
  SliceNatTrans {x=(dom eb)} {y=(cod eb)}
    (InterpSPFdepDataEl f eb)
    (InterpSPFdepDataEl g eb)
InterpSPFdepNTel {b} {dom} {cod} f g alpha eb =
  InterpSPFnt {dom=(dom eb)} {cod=(cod eb)}
    (SPFDataFamFromDep f eb) (SPFDataFamFromDep g eb)
    (SPFntFamFromDep alpha eb)

public export
spfDepPushoutPos : {b : Type} -> {x, y, z : SliceObj b} ->
  (SliceMorphism {a=b} z y) -> SPFdepData x z -> SPFdepData x y
spfDepPushoutPos {b} {x} {y} {z} mzy f =
  SPFDD
    (\eb => SliceFibSigmaF (mzy eb) $ spfddPos f eb)
    (\eb, ey, ep => spfddDir f eb (sfsFst ep) (sfsSnd ep))

public export
spfDepPushoutDir : {b : Type} -> {w, x, z : SliceObj b} ->
  (SliceMorphism {a=b} w x) -> SPFdepData w z -> SPFdepData x z
spfDepPushoutDir {b} {w} {x} {z} mwx f =
  SPFDD (spfddPos f) (\eb, ez => SliceFibSigmaF (mwx eb) . spfddDir f eb ez)

public export
spfDepPushout : {b : Type} -> {w, x, y, z : SliceObj b} ->
  (SliceMorphism {a=b} w x) -> (SliceMorphism {a=b} z y) ->
  SPFdepData w z -> SPFdepData x y
spfDepPushout {b} {w} {x} {y} {z} mwx mzy =
  spfDepPushoutPos {x} {y} {z} mzy . spfDepPushoutDir {w} {x} {z} mwx

-- The cells of the double category of slice polynomial functors whose domain
-- and codomain are slices of `dom eb` and `cod eb` respectively for each
-- `eb : b`.
public export
SPFdepPoCell : {b : Type} -> {w, w', z, z' : SliceObj b} ->
  (bcl : SliceMorphism {a=b} w w') -> (bcr : SliceMorphism {a=b} z z') ->
  (f : SPFdepData w z) -> (g : SPFdepData w' z') ->
  Type
SPFdepPoCell {w} {w'} {z} {z'} bcl bcr f g =
  SPFdepNT {dom=w'} {cod=z'} (spfDepPushout bcl bcr f) g

-- This is forgetful, like `SPFDataFromDep`, which it uses,
-- compared to `SPFpoCellDepFromFam`.
public export
SPFpoCellFromDep : {b : Type} -> {w, w', z, z' : SliceObj b} ->
  (bcl : SliceMorphism {a=b} w w') -> (bcr : SliceMorphism {a=b} z z') ->
  (f : SPFdepData w z) -> (g : SPFdepData w' z') ->
  SPFdepPoCell {w} {w'} {z} {z'} bcl bcr f g ->
  SPFpoCell
    {w=(Sigma {a=b} w)}
    {w'=(Sigma {a=b} w')}
    {z=(Sigma {a=b} z)}
    {z'=(Sigma {a=b} z')}
    (dpMapSnd bcl)
    (dpMapSnd bcr)
    (SPFDataFromDep f)
    (SPFDataFromDep g)
SPFpoCellFromDep {w} {w'} {z} {z'} bcl bcr f g spfc =
  SPFDm
    (\(eb ** ez'), (SFS (eb ** ez) efp) => spdOnPos spfc eb ez' $ SFS ez efp)
    (\(eb ** ez'), (SFS (eb' ** ez) efp), (eb'' ** ew'), (SPFdd _ _ _ _ egd) =>
      let (SFS ew efd) = spdOnDir spfc eb' (bcr eb' ez) (SFS ez efp) ew' egd in
      SFS (eb' ** ew) $ SPFdd eb' ez efp ew efd)

-- As with functors and natural transformations, the dependent cells are
-- simply `b`-indexed dependent families of cells.

public export
SPFpoCellDepFromFam : {b : Type} -> {w, w', z, z' : SliceObj b} ->
  (bcl : SliceMorphism {a=b} w w') -> (bcr : SliceMorphism {a=b} z z') ->
  (f : SPFdepData w z) -> (g : SPFdepData w' z') ->
  SPFdepPoCell bcl bcr f g ->
  SPFpoCellFam {b} {w} {w'} {z} {z'} bcl bcr
    (SPFDataFamFromDep f) (SPFDataFamFromDep g)
SPFpoCellDepFromFam {b} {w} {w'} {z} {z'} bcl bcr f g = SPFntFamFromDep

public export
SPFpoCellFamFromDep : {b : Type} -> {w, w', z, z' : SliceObj b} ->
  (bcl : SliceMorphism {a=b} w w') -> (bcr : SliceMorphism {a=b} z z') ->
  (f : SPFdepData w z) -> (g : SPFdepData w' z') ->
  SPFpoCellFam {b} {w} {w'} {z} {z'} bcl bcr
    (SPFDataFamFromDep f) (SPFDataFamFromDep g) ->
  SPFdepPoCell bcl bcr f g
SPFpoCellFamFromDep {b} {w} {w'} {z} {z'} bcl bcr f g = SPFntDepFromFam

------------------------------------------
------------------------------------------
---- Morphisms between direction-sets ----
------------------------------------------
------------------------------------------

-- In some cases (see for example the density comonad), we will treat
-- positions of a polynomial functor as if they were objects of a category,
-- and directions as if they were incoming or outgoing hom-sets, as in
-- Ahman and Uustalu's equivalence of polynomial comonads (on `Set`/`Type`)
-- and categories.  Thus we introduce some definitions which encode this notion.

-- A morphism between the direction-sets of the two given positions
-- of a polynomial functor.  This may be viewed as either a generalized
-- quantity of the domain or a generalized element of the codomain.
public export
spfdDirMor : {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> IntMorSig (SPFDbase spfd)
spfdDirMor {dom} {cod} spfd domp codp =
  SliceMorphism {a=dom}
    (spfdDir spfd (fst domp) (snd domp))
    (spfdDir spfd (fst codp) (snd codp))

-- A generalized element of the given position, where the source
-- position has the given codomain.
public export
spfdDirGenElCod : {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> SPFDbase spfd -> SliceObj cod
spfdDirGenElCod {dom} {cod} spfd ep ec' =
  (ep' : spfdPos spfd ec' ** spfdDirMor {dom} {cod} spfd (ec' ** ep') ep)

-- A generalized element of the given position, where the source
-- position's codomain matches that of the given position.
public export
spfdDirGenEndoEl : {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> SliceObj (SPFDbase spfd)
spfdDirGenEndoEl {dom} {cod} spfd ep =
  spfdDirGenElCod {dom} {cod} spfd ep (fst ep)

-- A generalized element of the given position, where the source
-- position has any codomain.
public export
spfdDirGenEl : {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> SliceObj (SPFDbase spfd)
spfdDirGenEl {dom} {cod} spfd ep =
  (ec' : cod ** spfdDirGenElCod {dom} {cod} spfd ep ec')

-- A generalized quantity of the given position, where the target
-- position has the given codomain.
public export
spfdDirGenQuantCod : {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> SPFDbase spfd -> SliceObj cod
spfdDirGenQuantCod {dom} {cod} spfd ep ec' =
  (ep' : spfdPos spfd ec' ** spfdDirMor {dom} {cod} spfd ep (ec' ** ep'))

-- A generalized quantity of the given position, where the target
-- position's codomain matches that of the given position.
public export
spfdDirGenEndoQuant : {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> SliceObj (SPFDbase spfd)
spfdDirGenEndoQuant {dom} {cod} spfd ep =
  spfdDirGenQuantCod {dom} {cod} spfd ep (fst ep)

-- A generalized quantity of the given position, where the target
-- position has any codomain.
public export
spfdDirGenQuant : {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> SliceObj (SPFDbase spfd)
spfdDirGenQuant {dom} {cod} spfd ep =
  (ec' : cod ** spfdDirGenQuantCod {dom} {cod} spfd ep ec')
