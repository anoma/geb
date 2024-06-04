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
import public LanguageDef.MLBundleCat

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

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
SPFDposCSlice : {dom, cod : Type} -> SPFData dom cod -> Type
SPFDposCSlice {dom} {cod} spfd = CSliceOfSlice {c=cod} (spfdPos spfd)

-- Here we define translations amongst `SPFDbaseSl` (a dependent-type-style
-- slice of `SPFDbase spfd`), `SPFDposCSlice` (a combination of dependent-type
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
  SPFDposCSlice {dom} {cod} spfd ->
  SPFDbaseSl {dom} {cod} spfd
SPFDposCSlToBaseSl {dom} {cod} {spfd} =
  CSliceOfSliceToSliceOfSigma {c=cod} {sl=(spfdPos spfd)}

public export
SPFDbaseSlToPosCSl : {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  SPFDbaseSl {dom} {cod} spfd ->
  SPFDposCSlice {dom} {cod} spfd
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
  spfdCPosSl spfd -> SPFDposCSlice {dom} {cod} spfd
SPFDcPosSlToPosCSl = CSliceOfSliceCatToCSliceOfSlice

public export
SPFDposCSlToCPosSl : {dom, cod : Type} -> {spfd : SPFData dom cod} ->
  SPFDposCSlice {dom} {cod} spfd -> spfdCPosSl spfd
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
SSPRtoSPFD : {dom, cod : Type} -> SliceObj (dom, cod) -> SPFData dom cod
SSPRtoSPFD {dom} {cod} sspr = SPFD (const Unit) $ \ec, (), ed => sspr (ed, ec)

public export
SPFDasSSPR : {0 dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceNatTrans {x=dom} {y=(SPFDbase spfd)}
    (SPFDradjFact {dom} {cod} spfd)
    (SliceSigmaPiFR {c=dom} {e=(SPFDbase spfd)} $ SPFDtoSSPR spfd)
SPFDasSSPR {dom} {cod} (SPFD pos dir) sd (ec ** ep) radj (ed ** dd) = radj ed dd

public export
SSPRasSPFD : {0 dom, cod : Type} -> (sspr : SliceObj (dom, cod)) ->
  SliceNatTrans {x=dom} {y=cod}
    (SliceSigmaPiFR {c=dom} {e=cod} sspr)
    ((\sc, ec => sc (ec ** ()))
     . SPFDradjFact {dom} {cod} (SSPRtoSPFD {dom} {cod} sspr))
SSPRasSPFD {dom} {cod} sspr sd ec sdc ed esdc = sdc (ed ** esdc)

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
  (sl : SPFDposCSlice spfd) ->
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
  SliceSigmaPiFL {c=dom} {e=(SPFDbase {dom} {cod} spfd)}
    $ Prelude.uncurry (DPair.uncurry $ spfdDir spfd) . swap

public export
SPFDladjFactMap : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceFMap (SPFDladjFact {dom} {cod} spfd)
SPFDladjFactMap {dom} {cod} spfd =
  ssplMap {c=dom} {e=(SPFDbase {dom} {cod} spfd)}
    $ Prelude.uncurry (DPair.uncurry $ spfdDir spfd) . swap

-- We show that the left adjoint of the right-adjoint factor of a
-- polynomial functor is equivalent to `SliceSigmaPiFL` with particular
-- parameters.  (Of course, we _defined_ it as such, so this is trivial.)
public export
SPFDasSSPL : {0 dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SliceNatTrans {x=(SPFDbase spfd)} {y=dom}
    (SPFDladjFact {dom} {cod} spfd)
    (SliceSigmaPiFL {c=dom} {e=(SPFDbase spfd)} $ SPFDtoSSPR spfd)
SPFDasSSPL {dom} {cod} (SPFD pos dir) sd ed (((ec ** ep) ** dd) ** sdd) =
  (((ec ** ep) ** dd) ** sdd)

public export
SSPLasSPFD : {0 dom, cod : Type} -> (sspl : SliceObj (dom, cod)) ->
  SliceNatTrans {x=cod} {y=dom}
    (SliceSigmaPiFL {c=dom} {e=cod} sspl)
    (SPFDladjFact {dom} {cod} (SSPRtoSPFD {dom} {cod} sspl)
     . (\sc, (ec ** ()) => sc ec))
SSPLasSPFD {dom} {cod} sspl sc ed ((ec ** esdc) ** esc) =
  (((ec ** ()) ** esdc) ** esc)

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
SPFDmultiLdom = SPFDposCSlice

-- But we may take another view of the structure (`SPFDposCSlice`) that
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

-- This is the intermediate object of the generic factorization of the
-- given morphism `i` (see the comment to `SPFDgenFactDomObj` above).
public export
SPFDgenFactCodObj : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  (a : SliceObj dom) -> (b : SliceObj cod) ->
  (i : SliceMorphism {a=cod} b (SPFDmultiR {dom} {cod} spfd a)) ->
  SliceObj cod
SPFDgenFactCodObj {dom} {cod} spfd a b i =
  SPFDmultiR {dom} {cod} spfd $ SPFDgenFactDomObj {dom} {cod} spfd a b i

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
SPFDfcat : IntCatSig
SPFDfcat =
  ICat
    Type
  $ MICS
    SPFData
  $ ICS
    SPFDid
    SPFDcomp

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
spfPullbackDir : {w, x, y : Type} ->
  (w -> x) -> SPFData x y -> SPFData w y
spfPullbackDir {w} {x} {y} mwx f =
  SPFD (spfdPos f) (\ez, ep => spfdDir f ez ep . mwx)

public export
spfPullback : {w, x, y, z : Type} ->
  (w -> x) -> (z -> y) -> SPFData x y -> SPFData w z
spfPullback {w} {x} {y} {z} mwx mzy =
  spfPullbackDir {w} {x} {y=z} mwx . spfPullbackPos {x} {y} {z} mzy

public export
spfPushoutPos : {x, y, z : Type} ->
  (y -> z) -> SPFData x y -> SPFData x z
spfPushoutPos {x} {y} {z} myz f =
  SPFD
    (\ez => (ey : y ** (myz ey = ez, spfdPos f ey)))
    (\ez, ep, ex => spfdDir f (fst ep) (snd $ snd ep) ex)

public export
spfPushoutDir : {w, x, y : Type} ->
  (x -> w) -> SPFData x y -> SPFData w y
spfPushoutDir {w} {x} {y} mxw f =
  SPFD
    (spfdPos f)
    (\ey, ep, ew => (ex : x ** (mxw ex = ew, spfdDir f ey ep ex)))

public export
spfPushout : {w, x, y, z : Type} ->
  (x -> w) -> (y -> z) -> SPFData x y -> SPFData w z
spfPushout {w} {x} {y} {z} mxw myz =
  spfPushoutDir {w} {x} {y=z} mxw . spfPushoutPos {x} {y} {z} myz

--------------------------------------------------
-------------------------------------------------
---- Categories of slice polynomial functors ----
-------------------------------------------------
-------------------------------------------------

----------------------------------------------
---- Natural transformations as morphisms ----
----------------------------------------------

public export
SPFntPos : {dom, cod : Type} -> IntMorSig (SPFData dom cod)
SPFntPos {dom} {cod} f g = SliceMorphism {a=cod} (spfdPos f) (spfdPos g)

public export
SPFntDir : {dom, cod : Type} ->
  (f, g : SPFData dom cod) -> SPFntPos f g -> Type
SPFntDir {dom} {cod} f g onpos =
  (ec : cod) -> (ep : spfdPos f ec) ->
  SliceMorphism {a=dom} (spfdDir g ec $ onpos ec ep) (spfdDir f ec ep)

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
SPFDcat : Type -> Type -> IntCatSig
SPFDcat dom cod =
  ICat
    (SPFData dom cod)
  $ MICS
    (SPFnt {dom} {cod})
  $ ICS
    (SPNTid {dom} {cod})
    (SPNTvcomp {dom} {cod})

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
  SPFD (\ey => PreImage {a=x} {b=y} f ey) (\ey, ep, ex => fst0 ep = ex)

public export
InterpSPFDtoSigma : {x, y : Type} -> (f : x -> y) ->
  SliceNatTrans {x} {y} (InterpSPFData $ SPFDsigma f) (SliceFibSigmaF f)
InterpSPFDtoSigma {x} {y} f sx ey ei = (fst ei ** snd ei (fst0 $ fst ei) Refl)

public export
InterpSPFDfromSigma : {x, y : Type} -> (f : x -> y) ->
  SliceNatTrans {x} {y} (SliceFibSigmaF f) (InterpSPFData $ SPFDsigma f)
InterpSPFDfromSigma {x} {y} f sx ey ei =
  (fst ei ** \ex, eq => replace {p=sx} eq $ snd ei)

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
  case ei of (() ** dm) => dm (fst0 ex) (snd0 ex)

public export
InterpSPFDfromPi : {x, y : Type} -> (f : x -> y) ->
  SliceNatTrans {x} {y} (SliceFibPiF f) (InterpSPFData $ SPFDpi f)
InterpSPFDfromPi {x} {y} f sx ey pix = (() ** \ex, eq => pix $ Element0 ex eq)

----------------------------------------
----------------------------------------
---- Compositions with base changes ----
----------------------------------------
----------------------------------------

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

-- Postcompose a sigma after a slice polynomial.
public export
spfdPostcompSigma : {x, y, z : Type} -> (y -> z) -> SPFData x y -> SPFData x z
spfdPostcompSigma {x} {y} {z} f = (SPFDcomp x y z) (SPFDsigma f)

-- Postcompose a pi after a slice polynomial.
public export
spfdPostcompPi : {x, y, z : Type} -> (y -> z) -> SPFData x y -> SPFData x z
spfdPostcompPi {x} {y} {z} f = (SPFDcomp x y z) (SPFDpi f)

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

-- Postcomposition with sigma is the same as what we have
-- called pushing out along position.

public export
0 spfdPostcompSigmaToPushoutPos : {x, y, z : Type} ->
  (myz : y -> z) -> (f : SPFData x y) ->
  SPFnt {dom=x} {cod=z} (spfdPostcompSigma myz f) (spfPushoutPos myz f)
spfdPostcompSigmaToPushoutPos {x} {y} {z} myz f =
  SPFDm
    (\ez, epdm =>
      (fst0 (fst epdm) ** (snd0 (fst epdm), snd epdm (fst0 $ fst epdm) Refl)))
    (\ez, epdm, ex, efd => ((fst0 (fst epdm) ** Refl) ** efd))

public export
spfdPostcompSigmaFromPushoutPos : {x, y, z : Type} ->
  (myz : y -> z) -> (f : SPFData x y) ->
  SPFnt {dom=x} {cod=z} (spfPushoutPos myz f) (spfdPostcompSigma myz f)
spfdPostcompSigmaFromPushoutPos {x} {y} {z} myz f =
  SPFDm
    (\ez, ep =>
      (Element0 (fst ep) (fst $ snd ep) **
       \ey', eq => replace {p=(spfdPos f)} eq $ snd $ snd ep))
    (\ez, ep, ex, efd => rewrite snd (fst efd) in snd efd)

-- Precomposition with base change is the same as what we have
-- called pushing out along direction.

public export
0 spfdPrecompBCToPushoutDir : {x, y, z : Type} ->
  (myx : y -> x) -> (f : SPFData y z) ->
  SPFnt {dom=x} {cod=z} (spfdPrecompBC myx f) (spfPushoutDir myx f)
spfdPrecompBCToPushoutDir {x} {y} {z} myx f =
  SPFDm
    (\ez, epTermMorph => fst epTermMorph)
    (\ez, ep, ex, eyeqef =>
      ((fst eyeqef ** snd $ snd eyeqef) ** fst $ snd eyeqef))

public export
spfdPrecompBCFromPushoutDir : {x, y, z : Type} ->
  (myx : y -> x) -> (f : SPFData y z) ->
  SPFnt {dom=x} {cod=z} (spfPushoutDir myx f) (spfdPrecompBC myx f)
spfdPrecompBCFromPushoutDir {x} {y} {z} my f =
  SPFDm
    (\ez, ep => (ep ** \_, _ => ()))
    (\ez, ep, ex, efd => (fst (fst efd) ** (snd efd, snd (fst efd))))

---------------------------------------------------------------
---------------------------------------------------------------
---- Slice polynomial double-categorical structure (cells) ----
---------------------------------------------------------------
---------------------------------------------------------------

public export
SPFcell : {w, w', z, z' : Type} ->
  (bcl : w -> w') -> (bcr : z -> z') ->
  (f : SPFData w z) -> (g : SPFData w' z') ->
  Type
SPFcell {w} {w'} {z} {z'} bcl bcr f g =
  SPFnt {dom=w'} {cod=z'} (spfPushout bcl bcr f) g

public export
spfcId : {w, z : Type} -> (f : SPFData w z) ->
  SPFcell {w} {w'=w} {z} {z'=z} Prelude.id Prelude.id f f
spfcId {w} {z} f =
  SPFDm
    (\ez, ep => replace {p=(spfdPos f)} (fst $ snd ep) $ snd $ snd ep)
    (\ez, ep, ew, efd => (ew ** (Refl, rewrite fst (snd ep) in efd)))

public export
spfcVcomp : {w, w', w'', z, z', z'' : Type} ->
  {bcl : w -> w'} -> {bcl' : w' -> w''} ->
  {bcr : z -> z'} -> {bcr' : z' -> z''} ->
  {f : SPFData w z} -> {g : SPFData w' z'} -> {h : SPFData w'' z''} ->
  SPFcell {w=w'} {w'=w''} {z=z'} {z'=z''} bcl' bcr' g h ->
  SPFcell {w} {w'} {z} {z'} bcl bcr f g ->
  SPFcell {w} {w'=w''} {z} {z'=z''} (bcl' . bcl) (bcr' . bcr) f h
spfcVcomp {w} {w'} {w''} {z} {z'} {z''} {bcl} {bcl'} {bcr} {bcr'} {f} {g} {h}
  beta alpha =
    SPFDm
      (\ez'', ep =>
        spOnPos beta ez''
          (bcr (fst ep) **
           (fst (snd ep),
            spOnPos alpha (bcr $ fst ep) (fst ep ** (Refl, snd $ snd ep)))))
      (\ez'', ep, ew'', epdm =>
        let
          (ew' ** (eweq', egd)) = spOnDir beta ez''
            (bcr (fst ep) **
             (fst (snd ep),
              spOnPos alpha (bcr $ fst ep) (fst ep ** (Refl, snd $ snd ep))))
             ew''
             epdm
          (ew ** (eweq, efd)) =
            spOnDir alpha (bcr $ fst ep)
              (fst ep ** (Refl, snd $ snd ep)) ew' egd
        in
        (ew ** (trans (cong bcl' $ eweq) eweq', efd)))

public export
spfcHcomp : {w, w', x, x', z, z' : Type} ->
  {bcw : w -> w'} -> {bcx : x -> x'} -> {bcz : z -> z'} ->
  {f : SPFData w x} -> {f' : SPFData x z} ->
  {g : SPFData w' x'} -> {g' : SPFData x' z'} ->
  SPFcell {w=x} {w'=x'} {z} {z'} bcx bcz f' g' ->
  SPFcell {w} {w'} {z=x} {z'=x'} bcw bcx f g ->
  SPFcell {w} {w'} {z} {z'}
    bcw
    bcz
    (SPFDcomp w x z f' f)
    (SPFDcomp w' x' z' g' g)
spfcHcomp {w} {w'} {x} {x'} {z} {z'} {bcw} {bcx} {bcz} {f} {f'} {g} {g'}
  beta alpha =
    SPFDm
      (\ez', epdm => case epdm of
        (ez ** (ezeq, (ep ** dm))) =>
          (spOnPos beta ez' (ez ** (ezeq, ep)) **
           \ex', egd' =>
            let
              (ex ** (exeq, efd')) =
                spOnDir beta ez' (ez ** (ezeq, ep)) ex' egd'
            in
            spOnPos alpha ex' (ex ** (exeq, dm ex efd'))))
      ?spfcHcomp_ondir
