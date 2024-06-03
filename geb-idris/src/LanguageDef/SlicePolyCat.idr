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
record SPFData (0 dom, cod : Type) where
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

-------------------------------------------------
-------------------------------------------------
---- Categories of slice polynomial functors ----
-------------------------------------------------
-------------------------------------------------

public export
SPFDposMor : {dom, cod : Type} -> IntMorSig (SPFData dom cod)
SPFDposMor {dom} {cod} f g = SliceMorphism {a=cod} (spfdPos f) (spfdPos g)

public export
SPFDdirMor : {dom, cod : Type} ->
  (f, g : SPFData dom cod) -> SPFDposMor f g -> Type
SPFDdirMor {dom} {cod} f g onpos =
  (ec : cod) -> (ep : spfdPos f ec) ->
  SliceMorphism {a=dom} (spfdDir g ec $ onpos ec ep) (spfdDir f ec ep)

public export
record SPFDmor {dom, cod : Type} (f, g : SPFData dom cod) where
  constructor SPFDm
  spmOnPos : SPFDposMor {dom} {cod} f g
  spmOnDir : SPFDdirMor {dom} {cod} f g spmOnPos

public export
SPFDidPos : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFDposMor {dom} {cod} spfd spfd
SPFDidPos spfd = sliceId {a=cod} (spfdPos spfd)

public export
SPFDidDir : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFDdirMor {dom} {cod} spfd spfd (SPFDidPos spfd)
SPFDidDir spfd ec ep = sliceId {a=dom} (spfdDir spfd ec ep)

public export
SPFDid : {dom, cod : Type} -> IntIdSig (SPFData dom cod) (SPFDmor {dom} {cod})
SPFDid spfd = SPFDm (SPFDidPos spfd) (SPFDidDir spfd)

public export
SPFDcompPos : {dom, cod : Type} ->
  (f, g, h : SPFData dom cod) ->
  SPFDposMor {dom} {cod} g h ->
  SPFDposMor {dom} {cod} f g ->
  SPFDposMor {dom} {cod} f h
SPFDcompPos f g h opgh opfg = sliceComp {a=cod} opgh opfg

public export
SPFDcompDir : {dom, cod : Type} ->
  (f, g, h : SPFData dom cod) ->
  (beta : SPFDmor {dom} {cod} g h) ->
  (alpha : SPFDmor {dom} {cod} f g) ->
  SPFDdirMor {dom} {cod} f h
    (SPFDcompPos f g h (spmOnPos beta) (spmOnPos alpha))
SPFDcompDir f g h beta alpha ec ep =
  sliceComp {a=dom}
    (spmOnDir alpha ec ep)
    (spmOnDir beta ec $ spmOnPos alpha ec ep)

public export
SPFDcomp : {dom, cod : Type} ->
  IntCompSig (SPFData dom cod) (SPFDmor {dom} {cod})
SPFDcomp {dom} {cod} f g h beta alpha =
  SPFDm
    (SPFDcompPos f g h (spmOnPos beta) (spmOnPos alpha))
    (SPFDcompDir f g h beta alpha)

--------------------------------
--------------------------------
---- Initial slice algebras ----
--------------------------------
--------------------------------

-- The impredicative initial algebra of an endofunctor on `SliceObj c`.
public export
ImSliceMu : {c : Type} -> SliceEndofunctor c -> SliceObj c
ImSliceMu {c} f ec =
  SliceNatTrans {x=c} {y=Unit} (\sc, () => SliceAlg f sc) (\sc, () => sc ec)

public export
imSlCata : {0 c : Type} -> {0 f : SliceEndofunctor c} ->
  {sa : SliceObj c} ->
  SliceAlg f sa -> SliceMorphism {a=c} (ImSliceMu {c} f) sa
imSlCata {c} {f} {sa} alg ec mu = mu sa () alg

public export
slMuFromIm : {c : Type} -> (f : SliceEndofunctor c) ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceMorphism (ImSliceMu f) (SliceMu f)
slMuFromIm {c} f fm ec mu =
  InSlFc {a=c} {f} {ea=ec} $ mu (f $ SliceMu f) ()
  $ fm (f $ SliceMu f) (SliceMu f) $ \ec => InSlFc {ea=ec}

public export
slMuToIm : {c : Type} -> (f : SliceEndofunctor c) ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceCata f ->
  SliceMorphism (SliceMu f) (ImSliceMu f)
slMuToIm {c} f fm fcata ec (InSlF {f} {sa=(const Void)} ec $ InSlV v) = void v
slMuToIm {c} f fm fcata ec (InSlF {f} {sa=(const Void)} ec $ InSlC t) =
  \sa, (), alg => sliceComp alg (fm (SliceMu f) sa (fcata sa alg)) ec t

public export
imSlInitAlg : {c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceCata f ->
  SliceAlg f (ImSliceMu f)
imSlInitAlg {f} fm fcata =
  sliceComp (slMuToIm f fm fcata) $ sliceComp (\ec => InSlFc {ea=ec})
  $ fm (ImSliceMu f) (SliceMu f) (slMuFromIm f fm)

public export
imSlInitAlgInv : {c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceCata f ->
  SliceCoalg f (ImSliceMu f)
imSlInitAlgInv {f} fm fcata =
  sliceComp (fm (SliceMu f) (ImSliceMu f) (slMuToIm f fm fcata))
  $ sliceComp (outSlMu f) (slMuFromIm f fm)

--------------------------------------
--------------------------------------
---- Free monad on dependent sums ----
--------------------------------------
--------------------------------------

--------------------------------
---- Pointed dependent sums ----
--------------------------------

SlicePointedSigmaF : {c, d : Type} -> (f : c -> d) ->
  SliceObj d -> SliceFunctor c d
SlicePointedSigmaF {c} {d} f = SlPointedF {c} {d} (SliceFibSigmaF {c} {d} f)

SPIAlg : {c : Type} -> (f : c -> c) -> (sv, sc : SliceObj c) -> Type
SPIAlg {c} f = SlPointedAlg {c} (SliceFibSigmaF {c} {d=c} f)

SPICoalg : {c : Type} -> (f : c -> c) -> (sv, sc : SliceObj c) -> Type
SPICoalg {c} f = SlPointedCoalg {c} (SliceFibSigmaF {c} {d=c} f)

-------------------------
---- Adjunction data ----
-------------------------

-- The free monad comes from a free-forgetful adjunction between `SliceObj c`
-- (on the right) and the category of `SliceSigmaF f`-algebras on that
-- category (on the left).
--
-- (The category of `SliceSigmaF f`-algebras on `SliceObj c` can be seen
-- as the category of elements of `SSAlg f`.)
--
-- The left adjoint takes `sc : SliceObj c` to the algebra whose object
-- component is `SliceSigmaFM f sc` and whose morphism component is
-- `SSin`.  The adjoints are part of the public interface of a universal
-- property, so we use `public export` here.
--
-- The right adjoint is the forgetful functor which simply throws away the
-- morphism component of the algebra, leaving a `SliceObj c`.
public export
data SliceSigmaFM : {0 c : Type} ->
    (0 f : c -> c) -> SliceEndofunctor c where
  SSin : {0 c : Type} -> {0 f : c -> c} -> {0 sc : SliceObj c} ->
    SPIAlg {c} f sc (SliceSigmaFM {c} f sc)

public export
SSFMAlg : {c : Type} -> (0 f : c -> c) -> (sc : SliceObj c) -> Type
SSFMAlg {c} f = SliceAlg {a=c} (SliceSigmaFM {c} f)

public export
SSFMCoalg : {c : Type} -> (0 f : c -> c) -> (sc : SliceObj c) -> Type
SSFMCoalg {c} f = SliceCoalg {a=c} (SliceSigmaFM {c} f)

-- `SSin` is an isomorphism (by Lambek's theorem); this is its inverse.
public export
SSout : {0 c : Type} -> {0 f : c -> c} -> {0 sc : SliceObj c} ->
  SPICoalg {c} f sc (SliceSigmaFM {c} f sc)
SSout {c} {f} {sc} ec (SSin ec esp) = esp

-- The (morphism component of the) free `SliceSigmaF`-algebra of
-- `SliceSigmaFM f sc`.
public export
SScom : {c : Type} -> {f : c -> c} -> {0 sc : SliceObj c} ->
  SSAlg {c} f (SliceSigmaFM {c} f sc)
SScom {c} {f} {sc} ec =
  SSin {c} {f} {sc} ec
  . inSlPc {f=(SliceFibSigmaF f)} {sl=sc} {sa=(SliceSigmaFM f sc)} ec

-- The unit of the free-monad adjunction -- a natural transformation of
-- endofunctors on `SliceObj a`, from the identity endofunctor to
-- `SliceSigmaFM f`.
public export
SSvar : {c : Type} -> {f : c -> c} ->
  SliceNatTrans (SliceIdF c) (SliceSigmaFM {c} f)
SSvar {c} {f} sc ec t =
  SSin {c} {f} {sc} ec
  $ inSlPv {f=(SliceFibSigmaF f)} {sl=sc} {sa=(SliceSigmaFM f sc)} ec t

-- The counit of the free-monad adjunction -- a natural transformation of
-- endofunctors on algebras of `SliceSigmaF f`, from `SSFMAlg` to the
-- identity endofunctor.
public export
SSFcounit : {c : Type} -> {f : c -> c} ->
  SliceMorphism {a=(SliceObj c)} (SSFMAlg {c} f) (SSAlg {c} f)
SSFcounit {c} {f} sc alg =
  sliceComp alg $ sliceComp (SScom {c} {f} {sc})
  $ sfsMap sc (SliceSigmaFM f sc)
  $ SSvar {c} {f} sc

-- `Eval` is a universal morphism of the free monad.  Specifically, it is
-- the right adjunct:  given an object `sa : SliceObj c` and an algebra
-- `sb : SliceObj c`/`alg : SSAlg f sb`, the right adjunct takes a
-- slice morphism `subst : SliceMorphism {a=c} sa sb` and returns an
-- F-algebra morphism `SliceSigmaEval sa sb alg subst :
-- SliceMorphism {a=c} (SliceSigmaFM f sa) sb`.
public export
SliceSigmaEval : {0 c : Type} -> {f : c -> c} -> (sb : SliceObj c) ->
  (alg : SSAlg f sb) ->
  SliceMorphism {a=(SliceObj c)}
    (flip (SliceMorphism {a=c}) sb)
    (flip (SliceMorphism {a=c}) sb . SliceSigmaFM {c} f)
SliceSigmaEval {c} {f} sb alg sa subst ec (SSin ec (Left v)) =
  subst ec v
SliceSigmaEval {c} {f} sb alg sa subst ec (SSin ec (Right t)) =
  alg ec $ case t of
    (Element0 ec' eqc ** fmec) =>
      (Element0 ec' eqc ** SliceSigmaEval sb alg sa subst ec' fmec)

-- The left adjunct of the free monad, given an object `sa : SliceObj c` and
-- an algebra `sb : SliceObj c`/`alg : SSAlg f sb`, takes an algebra morphism
-- from the free algebra `SliceSigmaFM f sa` to `sb`, i.e. a morphism of type
-- `SliceMorphism {a=c} (SliceSigmaFM f sa) sb`, and returns a morphism
-- `subst : SliceMorphism {a=c} sa sb`.
--
-- The implementation does not use the morphism component of the algebra,
-- so we omit it from the signature.  The reason for this is that this is the
-- left adjunct of a free-forgetful adjunction, and the only use of the
-- input to the left adjunct in the formula that expresses the left adjunct in
-- terms of the unit (`SSvar`, in this case) is to apply the right adjoint to
-- it, and the right adjoint just forgets the morphism component.
public export
SliceSigmaFMLAdj : {c : Type} -> {f : c -> c} -> (sa, sb : SliceObj c) ->
  SliceMorphism {a=c} (SliceSigmaFM {c} f sa) sb ->
  SliceMorphism {a=c} sa sb
SliceSigmaFMLAdj {c} {f} sa sb eval ec = eval ec . SSvar {c} {f} sa ec

-- We show that the initial algebra of `SliceSigmaF f` is the initial object
-- of `SliceObj a`.
public export
SSMuInitial : {c : Type} -> (f : c -> c) ->
  SliceMorphism {a=c} (SliceSigmaFM {c} f $ const Void) (const Void)
SSMuInitial {c} f =
  SliceSigmaEval {c} {f} (const Void) (SSVoidAlg {c} f) (const Void) (\_ => id)

public export
ssfmMap : {c : Type} -> {f : c -> c} -> SliceFMap (SliceSigmaFM {c} f)
ssfmMap {c} {f} sa sb m =
  SliceSigmaEval {c} {f} (SliceSigmaFM {c} f sb) SScom sa
    (sliceComp (SSvar sb) m)

-- The multiplication of the free-monad adjunction, often called "join" --
-- a natural transformation of endofunctors on `SliceObj a`, from
-- `SliceSigmaFM f . SliceSigmaFM f` to `SliceSigmaFM f`.
--
-- The multiplication comes from whiskering the counit between the adjuncts.
public export
ssfJoin : {c : Type} -> {f : c -> c} ->
  SliceNatTrans
    (SliceSigmaFM {c} f . SliceSigmaFM {c} f)
    (SliceSigmaFM {c} f)
ssfJoin {c} {f} sc =
  SliceSigmaEval {c} {f} (SliceSigmaFM f sc)
    (SScom {f} {sc}) (SliceSigmaFM f sc) (sliceId $ SliceSigmaFM f sc)

-- The comultiplication (or "duplicate") of the free-monad adjunction -- a
-- natural transformation of endofunctors on algebras of `SliceSigmaF f`,
-- from `SSFMAlg` to `SSFMAlg . SliceSigmaFM`.
--
-- The comultiplication comes from whiskering the unit between the adjuncts.
-- The algebra parameter is unused because the adjunct forgets the input
-- algebra.
public export
ssfDup : {c : Type} -> {f : c -> c} ->
  SliceMorphism {a=(SliceObj c)}
    (SSFMAlg {c} f)
    (SSFMAlg {c} f . SliceSigmaFM f)
ssfDup {c} {f} sc falg = ssfJoin {c} {f} sc

-----------------------------------
-----------------------------------
---- Terminal slice coalgebras ----
-----------------------------------
-----------------------------------

-- The dependent version of `ImNu`, the impredicative terminal coalgebra
-- of an endofunctor on `SliceObj c`.
public export
data ImSliceNu : {0 c : Type} -> SliceEndofunctor c -> SliceObj c where
  ImSlN : {0 c : Type} -> {0 f : SliceEndofunctor c} ->
    {0 sa : SliceObj c} -> SliceCoalg f sa -> (ec : c) -> sa ec ->
    ImSliceNu {c} f ec

public export
imSlAna : {0 c : Type} -> {0 f : SliceEndofunctor c} ->
  {0 sa : SliceObj c} ->
  SliceCoalg f sa -> SliceMorphism {a=c} sa (ImSliceNu {c} f)
imSlAna = ImSlN

public export
imSlTermCoalg : {0 c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceCoalg f (ImSliceNu f)
imSlTermCoalg {f} fm ec (ImSlN {c} {f} {sa} coalg ec esa) =
  fm sa (ImSliceNu {c} f) (imSlAna {c} {f} {sa} coalg) ec (coalg ec esa)

-- The inverse of `imSlTermCoalg`, which we know by Lambek's theorem should
-- exist.
public export
imSlTermCoalgInv : {0 c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceAlg f (ImSliceNu f)
imSlTermCoalgInv {c} {f} fm =
  ImSlN {c} {f} {sa=(f $ ImSliceNu f)}
  $ fm (ImSliceNu f) (f $ ImSliceNu f) $ imSlTermCoalg {c} {f} fm

------------------------
------------------------
---- Cofree comonad ----
------------------------
------------------------

----------------------------------
---- Copointed dependent sums ----
----------------------------------

SliceCopointedSigmaF : {c, d : Type} -> (f : c -> d) ->
  SliceObj d -> SliceFunctor c d
SliceCopointedSigmaF {c} {d} f = SlCopointedF {c} {d} (SliceFibSigmaF {c} {d} f)

SCPIAlg : {c : Type} -> (f : c -> c) -> (sv, sc : SliceObj c) -> Type
SCPIAlg {c} f = SlCopointedAlg {c} (SliceFibSigmaF {c} {d=c} f)

SCPICoalg : {c : Type} -> (f : c -> c) -> (sv, sc : SliceObj c) -> Type
SCPICoalg {c} f = SlCopointedCoalg {c} (SliceFibSigmaF {c} {d=c} f)

-------------------------
---- Adjunction data ----
-------------------------

-- The cofree comonad comes from a forgetful-cofree adjunction between
-- `SliceObj c` (on the left) and the category of
-- `SliceSigmaF f`-coalgebras on that category (on the right).
--
-- (The category of `SliceSigmaF f`-coalgebras on `SliceObj c` can be seen
-- as the category of elements of `SSCoalg {c} f`.)
--
-- The right adjoint takes `sl : SliceObj c` to the coalgebra whose object
-- component is `(Slice)ImCofree f sl` and whose morphism component is
-- `imSlSubtrees`.
--
-- The left adjoint is the forgetful functor which simply throws away the
-- morphism component of the coalgebra, leaving a `SliceObj c`.
--
-- This is an impredicative implementation which stashes a coalgebra and a
-- labeling morphism rather than building on the metalanguage's coinductive
-- (infinite) data types, if it even has them -- thus we do not require a
-- metalanguage to have them, but instead show how coinductive types (M-types)
-- can be implemented in terms of inductive types (W-types) and higher-order
-- functions.
public export
ImSliceCofree : {0 c : Type} -> SliceEndofunctor c -> SliceEndofunctor c
ImSliceCofree {c} f sa = ImSliceNu (SlCopointedF f sa)

public export
ImSlCMAlg : {c : Type} -> (f : SliceEndofunctor c) -> SliceObj c -> Type
ImSlCMAlg {c} f = SliceAlg {a=c} (ImSliceCofree {c} f)

public export
ImSlCMCoalg : {c : Type} -> (f : SliceEndofunctor c) -> SliceObj c -> Type
ImSlCMCoalg {c} f = SliceCoalg {a=c} (ImSliceCofree {c} f)

public export
inSlCF : {0 c : Type} -> {f : SliceEndofunctor c} -> {0 sl, sa : SliceObj c} ->
  SliceMorphism {a=c} sa sl -> SliceCoalg f sa ->
  SliceMorphism {a=c} sa (ImSliceCofree f sl)
inSlCF label coalg = ImSlN {f=(SlCopointedF f sl)} $ inSlCP {f} label coalg

public export
imSlCofreeTermCoalg : {0 c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  {sl : SliceObj c} -> SlCopointedCoalg {c} f sl (ImSliceCofree {c} f sl)
imSlCofreeTermCoalg fm {sl} =
  imSlTermCoalg {f=(SlCopointedF f sl)} (mapSlCP {f} fm sl)

public export
imSlCofreeTermCoalgInv : {0 c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  {sl : SliceObj c} -> SlCopointedAlg {c} f sl (ImSliceCofree {c} f sl)
imSlCofreeTermCoalgInv fm {sl} =
  imSlTermCoalgInv {f=(SlCopointedF f sl)} (mapSlCP {f} fm sl)

-- `imSlLabel` is the counit of the (impredicative) slice cofree-comonad
-- adjunction.  That means it is also the counit of the comonad arising from
-- the adjunction; as such it is also sometimes called "erase" or "extract".
public export
imSlLabel : {c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceNatTrans {x=c} {y=c} (ImSliceCofree f) (SliceIdF c)
imSlLabel {c} {f} fm sl =
  sliceComp
    (cpSlPoint {f} {sl} {sa=(ImSliceCofree f sl)})
    (imSlCofreeTermCoalg fm {sl})

-- `imSlSubtrees` is the morphism component of the right adjoint of
-- the slice cofree-comonad adjunction.
public export
imSlSubtrees : {c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  {sl : SliceObj c} -> SliceCoalg {a=c} f (ImSliceCofree {c} f sl)
imSlSubtrees {c} {f} fm {sl} =
  sliceComp
    (cpSlTerm {f} {sl} {sa=(ImSliceCofree f sl)})
    (imSlCofreeTermCoalg fm {sl})

-- `Trace` is a universal morphism of the cofree comonad.  Specifically, it is
-- the left adjunct:  given an object `sl : SliceObj c` and a coalgebra
-- `sa : SliceObj c`/`coalg : SSCoalg {c} f sa`, the left adjunct takes a
-- slice morphism `label : SliceMorphism {a=c} sa sl` and returns a
-- coalgebra morphism `SliceSigmaTrace coalg label :
-- SliceMorphism {a=c} sa (SliceSigmaCM f sl)`.
imSlTrace : {0 c : Type} -> {f : SliceEndofunctor c} ->
  {0 sa, sl : SliceObj c} ->
  SliceCoalg f sa -> SliceMorphism sa sl ->
  SliceMorphism sa (ImSliceCofree f sl)
imSlTrace {c} {f} {sa} {sl} = flip $ inSlCF {f} {sl} {sa}

-- The unit of the cofree comonad adjunction -- a natural transformation
-- between endofunctors on the category of F-coalgebras, from the identity
-- endofunctor to the cofree comonad.
imSlUnit : {c : Type} -> {f : SliceEndofunctor c} ->
  {sa : SliceObj c} -> SliceCoalg f sa -> SliceCoalg (ImSliceCofree f) sa
imSlUnit {c} {f} {sa} coalg = imSlTrace {f} {sa} {sl=sa} coalg (sliceId sa)

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
-- terms of the counit (`imSlLabel`, in this case) is to apply the left adjoint
-- to it, and the left adjoint just forgets the morphism component.
public export
imSlRAdj : {c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  {sa, sl : SliceObj c} ->
  SliceMorphism sa (ImSliceCofree f sl) -> SliceMorphism sa sl
imSlRAdj {c} {f} fm {sa} {sl} = sliceComp $ imSlLabel fm sl

-- `imSlJoin` is the multiplication of the (impredicative) slice cofree-comonad
-- adjunction.  That means it is also the multiplication of the monad
-- arising from the adjunction; as such it is also sometimes called "join".
--
-- The multiplication comes from whiskering the counit between the adjuncts.
imSlJoin : {c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceNatTrans (ImSliceCofree f . ImSliceCofree f) (ImSliceCofree f)
imSlJoin {f} fm sa = imSlLabel {f} fm (ImSliceCofree f sa)

-- `imSlDup` is the comultiplication of the (impredicative) slice cofree-comonad
-- adjunction.  That means it is also the comultiplication of the comonad
-- arising from the adjunction; as such it is also sometimes called "duplicate".
--
-- The comultiplication comes from whiskering the unit between the adjuncts.
public export
imSlDup : {c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceNatTrans (ImSliceCofree f) (ImSliceCofree f . ImSliceCofree f)
imSlDup {f} fm sa =
  imSlUnit {f} {sa=(ImSliceCofree f sa)} (imSlSubtrees {f} {sl=sa} fm)

----------------------------------------
----------------------------------------
---- Covariant slice representables ----
----------------------------------------
----------------------------------------

--------------------
---- Definition ----
--------------------

-- The slice functor from `c` to `Type` which is covariantly represented
-- by the given `SliceObj c`.  (`Type` is isomorphic to `SliceObj Unit`.)
public export
SliceCovarRepF : {c : Type} -> (sc : SliceObj c) -> SliceFunctor c Unit
SliceCovarRepF sa sb () = SliceMorphism sa sb

--------------------------------------------
----- Covariant representable as W-type ----
--------------------------------------------

0 SCovRasWTF : {c : Type} -> (sc : SliceObj c) -> WTypeFunc c Unit
SCovRasWTF {c} sc =
  MkWTF {dom=c} {cod=Unit}
    Unit
    (Sigma {a=c} sc)
    fst
    (const ())
    (id {a=Unit})

scovrToWTF : {c, d : Type} -> (sa : SliceObj c) ->
  SliceNatTrans (SliceCovarRepF {c} sa) (InterpWTF $ SCovRasWTF sa)
scovrToWTF {c} {d} sa sb () mfsa =
  (Element0 () Refl ** \(Element0 (ec ** sea) eq) => mfsa ec sea)

scovrFromWTF : {c, d : Type} -> (sa : SliceObj c) ->
  SliceNatTrans (InterpWTF $ SCovRasWTF sa) (SliceCovarRepF {c} sa)
scovrFromWTF {c} {d} sa sb () (Element0 () eq ** sbd) =
  \ec, sea => sbd $ Element0 (ec ** sea) Refl

---------------------------
---------------------------
---- Dependent product ----
---------------------------
---------------------------

---------------------------------------------
---- Dependent product from slice object ----
---------------------------------------------

-- The slice functor from `c` to `d` which consists of a product of `d`
-- representable functors from `SliceObj c`.  Products of representables
-- are themselves representable (products of covariant representables are
-- represented by sums, and products of contravariant representables are
-- represented by products).
public export
SliceDepPiF : {c : Type} -> (d -> c -> Type) -> SliceFunctor c d
SliceDepPiF sdc sc ed = SliceCovarRepF (sdc ed) {c} sc ()

--------------------------------------
----- Dependent product as W-type ----
--------------------------------------

0 SDPasWTF : {c, d : Type} -> (p : d -> c -> Type) -> WTypeFunc c d
SDPasWTF {c} {d} p =
  MkWTF {dom=c} {cod=d}
    d
    (Sigma {a=(d, c)} (uncurry p))
    (snd . fst)
    (fst . fst)
    (id {a=d})

spdToWTF : {c, d : Type} -> (0 p : d -> c -> Type)->
  SliceNatTrans (SliceDepPiF {c} {d} p) (InterpWTF $ SDPasWTF p)
spdToWTF {c} {d} p sc ed mpsc =
  (Element0 ed Refl **
   \(Element0 ((ed', ec') ** pdc) eq) =>
    mpsc ec' $ replace {p=(flip p ec')} eq pdc)

spdFromWTF : {c, d : Type} -> (0 p : d -> c -> Type)->
  SliceNatTrans (InterpWTF $ SDPasWTF p) (SliceDepPiF {c} {d} p)
spdFromWTF {c} {d} p sc ed (Element0 ed' eq ** mpsc) =
  \ec, pdc => mpsc (Element0 ((ed, ec) ** pdc) $ sym eq)

-----------------------------------------------------------------------
-----------------------------------------------------------------------
---- Slice categories of polynomial functors (in categorial style) ----
-----------------------------------------------------------------------
-----------------------------------------------------------------------

CPFSliceObj : MLPolyCatObj -> Type
CPFSliceObj p = (q : MLPolyCatObj ** PolyNatTrans q p)

public export
0 CPFNatTransEq :
  (p, q : MLPolyCatObj) -> (alpha, beta : PolyNatTrans p q) -> Type
CPFNatTransEq (ppos ** pdir) (qpos ** qdir)
  (aonpos ** aondir) (bonpos ** bondir) =
    Exists0
      (ExtEq {a=ppos} {b=qpos} aonpos bonpos)
      $ \onposeq =>
        (i : ppos) -> (d : qdir (aonpos i)) ->
        bondir i (replace {p=qdir} (onposeq i) d) = aondir i d

CPFSliceMorph : (p : MLPolyCatObj) -> CPFSliceObj p -> CPFSliceObj p -> Type
CPFSliceMorph p (q ** qp) (r ** rp) =
  Subset0 (PolyNatTrans q r) (\qr => CPFNatTransEq q p qp (pntVCatComp rp qr))

-- In any slice category, we can infer a slice morphism from a slice object
-- and a morphism from any object of the base category to the domain of the
-- slice object, by taking the codomain of the slice morphism to be the given
-- slice object, the domain of the domain of the slice morphism to be the
-- given object of the base category, and the projection of the domain of the
-- slice morphism to be composition of the given morphism followed by the
-- projection of the codomain of the slice morphism.  All slice morphisms
-- take this form, so that can function as an alternate definition of slice
-- morphism, which does not require any explicit proof content (of
-- commutativity).
PFSliceMorph : {0 p : PolyFunc} -> CPFSliceObj p -> Type
PFSliceMorph {p} (ctot ** alpha) = (dtot : PolyFunc ** PolyNatTrans dtot ctot)

PFSliceMorphDom : {0 p : PolyFunc} -> {cod : CPFSliceObj p} ->
  PFSliceMorph {p} cod -> CPFSliceObj p
PFSliceMorphDom {p} {cod=(ctot ** alpha)} (dtot ** beta) =
  (dtot ** pntVCatComp alpha beta)

public export
data PFSliceMorphDep : {0 p : PolyFunc} -> CPFSliceObj p -> CPFSliceObj p ->
    Type where
  PSMD : {0 p : PolyFunc} -> {0 dom, cod : CPFSliceObj p} ->
    (mor : PFSliceMorph {p} cod) ->
    PFSliceMorphDep {p} (PFSliceMorphDom {p} {cod} mor) cod

PFSliceMorphToC : {0 p : PolyFunc} -> {cod : CPFSliceObj p} ->
  (mor : PFSliceMorph {p} cod) ->
  CPFSliceMorph p (PFSliceMorphDom {p} {cod} mor) cod
PFSliceMorphToC {p=(ppos ** pdir)} {cod=((ctot ** cproj) ** (conpos ** condir))}
  ((dtot ** dproj) ** (donpos ** dondir)) =
    Element0
      (donpos ** dondir)
      (Evidence0
        (\_ => Refl)
        (\_, _ => Refl))

PFSliceMorphFromC : {0 p : PolyFunc} -> {dom, cod : CPFSliceObj p} ->
  CPFSliceMorph p dom cod -> PFSliceMorph {p} cod
PFSliceMorphFromC {p=(ppos ** pdir)} {dom=(dtot ** dproj)} {cod=(ctot ** cproj)}
  (Element0 alpha nteq) =
    (dtot ** alpha)

PFSliceMorphFromCDomObjEq : {0 p : PolyFunc} -> {dom, cod : CPFSliceObj p} ->
  (mor : CPFSliceMorph p dom cod) ->
  fst (PFSliceMorphDom {p} {cod} (PFSliceMorphFromC {p} {dom} {cod} mor)) =
  fst dom
PFSliceMorphFromCDomObjEq {p=(ppos ** pdir)}
  {dom=(dtot ** dproj)} {cod=(ctot ** cproj)} (Element0 alpha nteq) =
    Refl

0 PFSliceMorphFromCDomMorEq : {0 p : PolyFunc} ->
  {dtot, ctot : PolyFunc} ->
  {dproj : PolyNatTrans dtot p} ->
  {cproj : PolyNatTrans ctot p} ->
  (mor : CPFSliceMorph p (dtot ** dproj) (ctot ** cproj)) ->
  CPFNatTransEq
    dtot p
    dproj
    (replace {p=(flip PolyNatTrans p)}
      (PFSliceMorphFromCDomObjEq {p} {dom=(dtot ** dproj)} {cod=(ctot ** cproj)}
       mor)
     $ snd $ PFSliceMorphDom {p} {cod=(ctot ** cproj)}
     $ PFSliceMorphFromC {p} {dom=(dtot ** dproj)} {cod=(ctot ** cproj)} mor)
PFSliceMorphFromCDomMorEq {p=(ppos ** pdir)}
  {dtot} {dproj} {ctot} {cproj} (Element0 alpha nteq) =
    nteq

----------------------------------------------------------------------
----------------------------------------------------------------------
---- Slice categories of Dirichlet functors (in categorial style) ----
----------------------------------------------------------------------
----------------------------------------------------------------------

CDFSliceObj : MLDirichCatObj -> Type
CDFSliceObj p = (q : MLDirichCatObj ** DirichNatTrans q p)

0 CDFNatTransEq :
  (p, q : MLDirichCatObj) -> (alpha, beta : DirichNatTrans p q) -> Type
CDFNatTransEq (ppos ** pdir) (qpos ** qdir)
  (aonpos ** aondir) (bonpos ** bondir) =
    Exists0
      (ExtEq {a=ppos} {b=qpos} aonpos bonpos)
      $ \onposeq =>
        (i : ppos) -> (d : pdir i) ->
        bondir i d = replace {p=qdir} (onposeq i) (aondir i d)

CDFSliceMorph : (p : MLDirichCatObj) -> CDFSliceObj p -> CDFSliceObj p -> Type
CDFSliceMorph p (q ** qp) (r ** rp) =
  Subset0 (DirichNatTrans q r) (\qr => CDFNatTransEq q p qp (dntVCatComp rp qr))

-- A convenient (free of proof content) form of `CDFSliceMorph`; see
-- the comment to `PFSliceMorph` above.
DFSliceMorph : {0 p : PolyFunc} -> CDFSliceObj p -> Type
DFSliceMorph {p} (ctot ** alpha) = (dtot : PolyFunc ** DirichNatTrans dtot ctot)

DFSliceMorphDom : {0 p : PolyFunc} -> {cod : CDFSliceObj p} ->
  DFSliceMorph {p} cod -> CDFSliceObj p
DFSliceMorphDom {p} {cod=(ctot ** alpha)} (dtot ** beta) =
  (dtot ** dntVCatComp alpha beta)

public export
data DFSliceMorphDep : {0 p : PolyFunc} -> CDFSliceObj p -> CDFSliceObj p ->
    Type where
  DSMD : {0 p : PolyFunc} -> {0 dom, cod : CDFSliceObj p} ->
    (mor : DFSliceMorph {p} cod) ->
    DFSliceMorphDep {p} (DFSliceMorphDom {p} {cod} mor) cod

DFSliceMorphToC : {0 p : PolyFunc} -> {cod : CDFSliceObj p} ->
  (mor : DFSliceMorph {p} cod) ->
  CDFSliceMorph p (DFSliceMorphDom {p} {cod} mor) cod
DFSliceMorphToC {p=(ppos ** pdir)} {cod=((ctot ** cproj) ** (conpos ** condir))}
  ((dtot ** dproj) ** (donpos ** dondir)) =
    Element0
      (donpos ** dondir)
      (Evidence0
        (\_ => Refl)
        (\_, _ => Refl))

DFSliceMorphFromC : {0 p : PolyFunc} -> {dom, cod : CDFSliceObj p} ->
  CDFSliceMorph p dom cod -> DFSliceMorph {p} cod
DFSliceMorphFromC {p=(ppos ** pdir)} {dom=(dtot ** dproj)} {cod=(ctot ** cproj)}
  (Element0 alpha nteq) =
    (dtot ** alpha)

DFSliceMorphFromCDomObjEq : {0 p : PolyFunc} -> {dom, cod : CDFSliceObj p} ->
  (mor : CDFSliceMorph p dom cod) ->
  fst (DFSliceMorphDom {p} {cod} (DFSliceMorphFromC {p} {dom} {cod} mor)) =
  fst dom
DFSliceMorphFromCDomObjEq {p=(ppos ** pdir)}
  {dom=(dtot ** dproj)} {cod=(ctot ** cproj)} (Element0 alpha nteq) =
    Refl

0 DFSliceMorphFromCDomMorEq : {0 p : PolyFunc} ->
  {dtot, ctot : PolyFunc} ->
  {dproj : DirichNatTrans dtot p} ->
  {cproj : DirichNatTrans ctot p} ->
  (mor : CDFSliceMorph p (dtot ** dproj) (ctot ** cproj)) ->
  CDFNatTransEq
    dtot p
    dproj
    (replace {p=(flip DirichNatTrans p)}
      (DFSliceMorphFromCDomObjEq {p} {dom=(dtot ** dproj)} {cod=(ctot ** cproj)}
       mor)
     $ snd $ DFSliceMorphDom {p} {cod=(ctot ** cproj)}
     $ DFSliceMorphFromC {p} {dom=(dtot ** dproj)} {cod=(ctot ** cproj)} mor)
DFSliceMorphFromCDomMorEq {p=(ppos ** pdir)}
  {dtot} {dproj} {ctot} {cproj} (Element0 alpha nteq) =
    nteq

------------------------------------------------------
------------------------------------------------------
---- Slices over arenas (in dependent-type style) ----
------------------------------------------------------
------------------------------------------------------

---------------------------------
---- Slice object definition ----
---------------------------------

-- The natural transformations of both polynomial and Dirichlet functors have
-- on-positions functions from the domain to the codomain.  Thus, the
-- on-positions function of a natural transformation between either of those
-- types of objects (functors) may be viewed as a fibration of the arena
-- being sliced over.
public export
MlSlArProjOnPos : MLArena -> Type
MlSlArProjOnPos = SliceObj . pfPos

-- Thus, the positions of the slice object's domain can be viewed as
-- the sum of all the fibers.
public export
MlSlArTotPos : {ar : MLArena} -> MlSlArProjOnPos ar -> Type
MlSlArTotPos {ar} onpos = Sigma {a=(pfPos ar)} onpos

-- Consequently, the directions of the slice object's domain are a slice
-- of the sum of the fibers.
--
-- However, the on-directions part of the projection component of the slice
-- object will, in the case of Dirichlet functors, also go from the domain
-- to the object being sliced over.  Thus that too may be viewed as a fibration,
-- of pairs of the positions of the domain and the directions of the codomain,
-- where those two share the same position of the codomain.
--
-- That view only makes sense in the case of Dirichlet functors, not of
-- polynomials, because the on-directions part of the projection component of
-- an object in a polynomial-functor slice category goes in the opposite
-- direction.
public export
MlDirichSlDir : (ar : MLArena) -> MlSlArProjOnPos ar -> Type
MlDirichSlDir ar onpos = (i : pfPos ar) -> onpos i -> pfDir {p=ar} i -> Type

public export
record MlDirichSlObj (ar : MLArena) where
  constructor MDSobj
  mdsOnPos : MlSlArProjOnPos ar
  mdsDir : MlDirichSlDir ar mdsOnPos

-- In the case of polynomial functors, the directions of the slice object's
-- domain are slices of its positions only, since its on-directions function
-- can not be viewed as a fibration of them, and we therefore require an
-- explicit on-directions function (rather than making it implicit as a
-- fibration in the definition of the type of directions).
public export
MlPolySlDir : (ar : MLArena) -> MlSlArProjOnPos ar -> Type
MlPolySlDir ar onpos = (i : pfPos ar) -> onpos i -> Type

public export
MlPolySlOnDir : {ar : MLArena} ->
  (onpos : MlSlArProjOnPos ar) -> MlPolySlDir ar onpos -> Type
MlPolySlOnDir {ar} onpos dir =
  (i : pfPos ar) -> (j : onpos i) -> pfDir {p=ar} i -> dir i j

public export
record MlPolySlObj (ar : MLArena) where
  constructor MPSobj
  mpsOnPos : MlSlArProjOnPos ar
  mpsDir : MlPolySlDir ar mpsOnPos
  mpsOnDir : MlPolySlOnDir {ar} mpsOnPos mpsDir

--------------------------------------------------------------------
---- Equivalence of dependent-type and categorial-style objects ----
--------------------------------------------------------------------

public export
mlDirichSlObjTotPos : {ar : MLArena} -> MlDirichSlObj ar -> Type
mlDirichSlObjTotPos {ar} sl = MlSlArTotPos {ar} $ mdsOnPos sl

public export
mlDirichSlObjTotDir : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  mlDirichSlObjTotPos {ar} sl -> Type
mlDirichSlObjTotDir {ar} sl ij =
  Sigma {a=(pfDir {p=ar} $ fst ij)} $ mdsDir sl (fst ij) (snd ij)

public export
mlDirichSlObjTot : {ar : MLArena} -> MlDirichSlObj ar -> MLArena
mlDirichSlObjTot {ar} sl =
  (mlDirichSlObjTotPos {ar} sl ** mlDirichSlObjTotDir {ar} sl)

public export
mlDirichSlObjProjOnPos : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  mlDirichSlObjTotPos sl -> pfPos ar
mlDirichSlObjProjOnPos {ar} sl = DPair.fst

public export
mlDirichSlObjProjOnDir : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  (i : mlDirichSlObjTotPos sl) ->
  mlDirichSlObjTotDir {ar} sl i -> pfDir {p=ar} (mlDirichSlObjProjOnPos sl i)
mlDirichSlObjProjOnDir {ar} sl _ = DPair.fst

public export
mlDirichSlObjProj : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  DirichNatTrans (mlDirichSlObjTot {ar} sl) ar
mlDirichSlObjProj {ar} sl =
  (mlDirichSlObjProjOnPos {ar} sl ** mlDirichSlObjProjOnDir {ar} sl)

public export
mlDirichSlObjToC : {ar : MLArena} -> MlDirichSlObj ar -> CDFSliceObj ar
mlDirichSlObjToC {ar} sl =
  (mlDirichSlObjTot {ar} sl ** mlDirichSlObjProj {ar} sl)

public export
mlDirichSlOnPosFromC : {ar : MLArena} -> CDFSliceObj ar -> MlSlArProjOnPos ar
mlDirichSlOnPosFromC {ar} sl i = PreImage (fst $ snd sl) i

public export
mlDirichSlDirFromCBase : {ar : MLArena} -> (sl : CDFSliceObj ar) ->
  MlDirichSlDir ar (mlDirichSlOnPosFromC {ar} sl)
mlDirichSlDirFromCBase {ar} sl i j bd = snd (fst sl) (fst0 j)

public export
mlDirichSlDirFromCProp : {ar : MLArena} -> (sl : CDFSliceObj ar) ->
  (i : pfPos ar) -> (j : mlDirichSlOnPosFromC {ar} sl i) ->
  (bd : pfDir {p=ar} i) -> SliceObj (mlDirichSlDirFromCBase {ar} sl i j bd)
mlDirichSlDirFromCProp {ar} sl i j bd sld =
  snd (snd sl) (fst0 j) sld = replace {p=(pfDir {p=ar})} (sym $ snd0 j) bd

public export
mlDirichSlDirFromC : {ar : MLArena} -> (sl : CDFSliceObj ar) ->
  MlDirichSlDir ar (mlDirichSlOnPosFromC {ar} sl)
mlDirichSlDirFromC {ar} sl i j bd =
  Subset0
    (mlDirichSlDirFromCBase {ar} sl i j bd)
    (mlDirichSlDirFromCProp {ar} sl i j bd)

public export
mlDirichSlObjFromC : {ar : MLArena} -> CDFSliceObj ar -> MlDirichSlObj ar
mlDirichSlObjFromC {ar} sl =
  MDSobj (mlDirichSlOnPosFromC {ar} sl) (mlDirichSlDirFromC {ar} sl)

public export
mlPolySlObjTotPos : {ar : MLArena} -> MlPolySlObj ar -> Type
mlPolySlObjTotPos {ar} p = MlSlArTotPos {ar} $ mpsOnPos p

public export
mlPolySlObjTotDir : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  mlPolySlObjTotPos {ar} sl -> Type
mlPolySlObjTotDir {ar} sl ij = mpsDir sl (fst ij) (snd ij)

public export
mlPolySlObjTot : {ar : MLArena} -> MlPolySlObj ar -> MLArena
mlPolySlObjTot {ar} sl =
  (mlPolySlObjTotPos {ar} sl ** mlPolySlObjTotDir {ar} sl)

public export
mlPolySlObjProjOnPos : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  mlPolySlObjTotPos sl -> pfPos ar
mlPolySlObjProjOnPos {ar} sl = DPair.fst

public export
mlPolySlObjProjOnDir : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  (i : mlPolySlObjTotPos sl) ->
  pfDir {p=ar} (mlPolySlObjProjOnPos sl i) -> mlPolySlObjTotDir {ar} sl i
mlPolySlObjProjOnDir {ar} sl ij d = mpsOnDir sl (fst ij) (snd ij) d

public export
mlPolySlObjProj : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  PolyNatTrans (mlPolySlObjTot {ar} sl) ar
mlPolySlObjProj {ar} sl =
  (mlPolySlObjProjOnPos {ar} sl ** mlPolySlObjProjOnDir {ar} sl)

public export
mlPolySlObjToC : (ar : PolyFunc) -> MlPolySlObj ar -> CPFSliceObj ar
mlPolySlObjToC ar sl@(MPSobj onpos dir ondir) =
  (mlPolySlObjTot {ar} sl ** mlPolySlObjProj {ar} sl)

public export
mlPolySlOnPosFromC : {ar : MLArena} -> CPFSliceObj ar -> MlSlArProjOnPos ar
mlPolySlOnPosFromC {ar} sl i = PreImage (fst $ snd sl) i

public export
mlPolySlDirFromC : {ar : MLArena} -> (sl : CPFSliceObj ar) ->
  MlPolySlDir ar (mlPolySlOnPosFromC {ar} sl)
mlPolySlDirFromC {ar} sl i j = snd (fst sl) $ fst0 j

public export
mlPolySlOnDirFromC : {ar : MLArena} -> (sl : CPFSliceObj ar) ->
  MlPolySlOnDir {ar} (mlPolySlOnPosFromC {ar} sl) (mlPolySlDirFromC {ar} sl)
mlPolySlOnDirFromC {ar} sl i j d = snd (snd sl) (fst0 j) $ rewrite (snd0 j) in d

public export
mlPolySlObjFromC : (p : PolyFunc) -> CPFSliceObj p -> MlPolySlObj p
mlPolySlObjFromC ar sl =
  MPSobj
    (mlPolySlOnPosFromC {ar} sl)
    (mlPolySlDirFromC {ar} sl)
    (mlPolySlOnDirFromC {ar} sl)

-------------------------------------------------
---- Slices of slices of polynomial functors ----
-------------------------------------------------

public export
MlPolySlOfSl : {ar : MLArena} -> MlPolySlObj ar -> Type
MlPolySlOfSl {ar} sl = MlPolySlObj $ mlPolySlObjTot {ar} sl

public export
MlPolySlPosFromSlOfSl : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  MlPolySlOfSl {ar} sl -> MlSlArProjOnPos ar
MlPolySlPosFromSlOfSl {ar} sl slsl i =
  DPair (mpsOnPos sl i) $ DPair.curry (mpsOnPos slsl) i

public export
MlPolySlDirFromSlOfSl : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  (slsl : MlPolySlOfSl {ar} sl) ->
  MlPolySlDir ar (MlPolySlPosFromSlOfSl {ar} sl slsl)
MlPolySlDirFromSlOfSl {ar} sl slsl i jk =
  (mpsDir sl i (fst jk), mpsDir slsl (i ** fst jk) (snd jk))

public export
MlPolySlOnDirFromSlOfSl : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  (slsl : MlPolySlOfSl {ar} sl) ->
  MlPolySlOnDir {ar}
    (MlPolySlPosFromSlOfSl {ar} sl slsl)
    (MlPolySlDirFromSlOfSl {ar} sl slsl)
MlPolySlOnDirFromSlOfSl {ar} sl slsl i jk bd =
  let sldir = mpsOnDir sl i (fst jk) bd in
  (sldir, mpsOnDir slsl (i ** fst jk) (snd jk) sldir)

public export
MlPolySlFromSlOfSl : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  MlPolySlOfSl {ar} sl -> MlPolySlObj ar
MlPolySlFromSlOfSl {ar} sl slsl =
  MPSobj
    (MlPolySlPosFromSlOfSl {ar} sl slsl)
    (MlPolySlDirFromSlOfSl {ar} sl slsl)
    (MlPolySlOnDirFromSlOfSl {ar} sl slsl)

public export
mlPolySlOfSlFromP : {ar : MLArena} -> {cod : MlPolySlObj ar} ->
  PFSliceMorph {p=ar} (mlPolySlObjToC ar cod) -> MlPolySlOfSl {ar} cod
mlPolySlOfSlFromP {ar} {cod=cod@(MPSobj _ _ _)} m =
  mlPolySlObjFromC (mlPolySlObjTot {ar} cod) m

---------------------------------------------------------------------
---- Slice objects in terms of parameterized polynomial functors ----
---------------------------------------------------------------------

-- The dependent-type view of slices in the category of polynomial functors,
-- which turns the arrows backwards (an object of a slice category "depends"
-- on the functor being sliced over, rather than being a functor with a
-- natural transformation to the functor being sliced over), induces a mapping
-- of positions of the functor being sliced over to polynomial functors.
-- Furthermore, for each such position, it induces a mapping of the directions
-- of the functor being sliced over at that position to directions of the
-- dependent polynomial functors for _each_ position of those functors.
--
-- Thus, the dependent polynomial functors may be viewed as pointed -- each
-- of them, at each of its own positions, must have directions available to
-- which to map the directions of the functor being sliced over (unless that
-- functor has no directions at the corresponding position).

-- To summarize, one way of viewing a polynomial-functor slice object is as a
-- family of polynomial functors parameterized over the positions of the functor
-- being sliced over, together with a section of each functor in the family
-- for each direction of the corresponding position of the functor being
-- sliced over.

public export
PosParamPolyFunc : PolyFunc -> Type
PosParamPolyFunc = ParamPolyFunc . pfPos

public export
mlDirichSlObjToPPF : {ar : MLArena} -> MlDirichSlObj ar -> PosParamPolyFunc ar
mlDirichSlObjToPPF {ar=(bpos ** bdir)} (MDSobj slpos sldir) i =
  ((bdir i, slpos i) ** \(bd, j) => sldir i j bd)

public export
mlDirichSlObjFromPPF : {ar : MLArena} -> PosParamPolyFunc ar -> MlDirichSlObj ar
mlDirichSlObjFromPPF {ar=(bpos ** bdir)} ppf =
  MDSobj (\i => bdir i -> fst $ ppf i) (\i, sld, bd => snd (ppf i) $ sld bd)

public export
mlPolySlObjToPPF : {ar : MLArena} -> MlPolySlObj ar -> PosParamPolyFunc ar
mlPolySlObjToPPF {ar} sl i = (mpsOnPos sl i ** mpsDir sl i)

public export
ParamPFSection : (p : PolyFunc) -> PosParamPolyFunc p -> Type
ParamPFSection p spf = SliceMorphism {a=(pfPos p)} (pfDir {p}) (PFSection . spf)

public export
mlPolySlObjToPPFsect : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  ParamPFSection ar (mlPolySlObjToPPF {ar} sl)
mlPolySlObjToPPFsect {ar} sl i bd j = mpsOnDir sl i j bd

public export
mlPolySlObjFromPPFandSections : {ar : MLArena} ->
  (ppf : PosParamPolyFunc ar) -> ParamPFSection ar ppf -> MlPolySlObj ar
mlPolySlObjFromPPFandSections {ar=(bpos ** bdir)} ppf sect =
  MPSobj (fst . ppf) (\i => snd $ ppf i) (\i, j, bd => sect i bd j)

-- Using this formulation, we can characterize a polynomial-functor slice
-- object as represented by the directions of a particular polynomial functor.

PFSliceObjPF : PolyFunc -> PolyFunc
PFSliceObjPF p = (PosParamPolyFunc p ** ParamPFSection p)

PFSliceObj : PolyFunc -> Type
PFSliceObj p = pfPDir $ PFSliceObjPF p

-----------------------------------
---- Slice morphism definition ----
-----------------------------------

-- The morphisms of slice categories correspond to morphisms of the
-- base category which commute with the projections.

-- When we take the dependent-type view in the Dirichlet-functor category, the
-- commutativity conditions are hidden in the type-checking of dependent
-- functions.

public export
MlDirichSlMorOnPos : {ar : MLArena} ->
  MlDirichSlObj ar -> MlDirichSlObj ar -> Type
MlDirichSlMorOnPos {ar} dom cod =
  SliceMorphism {a=(pfPos ar)} (mdsOnPos dom) (mdsOnPos cod)

public export
MlDirichSlMorOnDir : {ar : MLArena} -> (dom, cod : MlDirichSlObj ar) ->
  MlDirichSlMorOnPos {ar} dom cod -> Type
MlDirichSlMorOnDir {ar} dom cod onpos =
  (i : pfPos ar) -> (j : mdsOnPos dom i) ->
    SliceMorphism {a=(pfDir {p=ar} i)}
      (mdsDir dom i j)
      (mdsDir cod i $ onpos i j)

public export
record MlDirichSlMor {ar : MLArena} (dom, cod : MlDirichSlObj ar) where
  constructor MDSM
  mdsmOnPos : MlDirichSlMorOnPos {ar} dom cod
  mdsmOnDir : MlDirichSlMorOnDir {ar} dom cod mdsmOnPos

public export
MlPolySlMorOnPos : {ar : MLArena} ->
  MlPolySlObj ar -> MlPolySlObj ar -> Type
MlPolySlMorOnPos {ar} dom cod =
  SliceMorphism {a=(pfPos ar)} (mpsOnPos dom) (mpsOnPos cod)

public export
MlPolySlMorOnDir : {ar : MLArena} -> (dom, cod : MlPolySlObj ar) ->
  MlPolySlMorOnPos {ar} dom cod -> Type
MlPolySlMorOnDir {ar} dom cod monpos =
  (i : pfPos ar) -> (j : mpsOnPos dom i) ->
  mpsDir cod i (monpos i j) -> mpsDir dom i j

public export
0 MlPolySlMorOnDirCommutes : {ar : MLArena} -> (dom, cod : MlPolySlObj ar) ->
  (onpos : MlPolySlMorOnPos {ar} dom cod) ->
  MlPolySlMorOnDir {ar} dom cod onpos -> Type
MlPolySlMorOnDirCommutes {ar} dom cod monpos mdir =
  (i : pfPos ar) -> (j : mpsOnPos dom i) -> (bd : pfDir {p=ar} i) ->
  mdir i j (mpsOnDir cod i (monpos i j) bd) = mpsOnDir dom i j bd

public export
record MlPolySlMor {ar : MLArena} (dom, cod : MlPolySlObj ar) where
  constructor MPSM
  mpsmOnPos : MlPolySlMorOnPos {ar} dom cod
  mpsmOnDir : MlPolySlMorOnDir {ar} dom cod mpsmOnPos
  mpsmOnDirCommutes : MlPolySlMorOnDirCommutes {ar} dom cod mpsmOnPos mpsmOnDir

------------------------------------------------------------------------
---- Categorial operations in polynomial/Dirichlet slice categories ----
------------------------------------------------------------------------

public export
mlDirichSlMorId : {ar : MLArena} -> (p : MlDirichSlObj ar) ->
  MlDirichSlMor {ar} p p
mlDirichSlMorId {ar} p =
  MDSM
    (sliceId $ mdsOnPos p)
    (\i, j => sliceId $ mdsDir p i j)

public export
mlDirichSlMorComp : {ar : MLArena} -> {p, q, r : MlDirichSlObj ar} ->
  MlDirichSlMor {ar} q r -> MlDirichSlMor {ar} p q -> MlDirichSlMor {ar} p r
mlDirichSlMorComp {ar} {p} {q} {r} m' m =
  MDSM
    (sliceComp (mdsmOnPos m') (mdsmOnPos m))
    (\i, j, bd, md =>
      mdsmOnDir m' i (mdsmOnPos m i j) bd $ mdsmOnDir m i j bd md)

public export
mlPolySlMorId : {ar : MLArena} -> (p : MlPolySlObj ar) ->
  MlPolySlMor {ar} p p
mlPolySlMorId {ar} p =
  MPSM
    (sliceId {a=(pfPos ar)} $ mpsOnPos p)
    (\i => sliceId {a=(mpsOnPos p i)} (mpsDir p i))
    (\i, j, bd => Refl)

public export
mlPolySlMorComp : {ar : MLArena} -> {p, q, r : MlPolySlObj ar} ->
  MlPolySlMor {ar} q r -> MlPolySlMor {ar} p q -> MlPolySlMor {ar} p r
mlPolySlMorComp {ar} {p} {q} {r} m' m =
  MPSM
    (sliceComp (mpsmOnPos m') (mpsmOnPos m))
    (\i, j, rd => mpsmOnDir m i j $ mpsmOnDir m' i (mpsmOnPos m i j) rd)
    (\i, j, bd =>
      trans
        (cong (mpsmOnDir m i j) $ mpsmOnDirCommutes m' i (mpsmOnPos m i j) bd)
        (mpsmOnDirCommutes m i j bd))

----------------------------------------------------------------------
---- Equivalence of dependent-type and categorial-style morphisms ----
----------------------------------------------------------------------

public export
mlDirichSlMorToCBase : {ar : MLArena} -> {dom, cod : MlDirichSlObj ar} ->
  MlDirichSlMor dom cod ->
  DirichNatTrans (fst (mlDirichSlObjToC dom)) (fst (mlDirichSlObjToC cod))
mlDirichSlMorToCBase {ar=(bpos ** bdir)}
  {dom=(MDSobj donpos ddir)} {cod=(MDSobj conpos cdir)} (MDSM onpos ondir) =
    (\ij => (fst ij ** onpos (fst ij) (snd ij)) **
     \(i ** j), (d ** dd) => (d ** ondir i j d dd))

public export
mlDirichSlMorToD : {ar : MLArena} -> {dom, cod : MlDirichSlObj ar} ->
  MlDirichSlMor dom cod -> DFSliceMorph {p=ar} (mlDirichSlObjToC cod)
mlDirichSlMorToD {ar=ar@(bpos ** bdir)}
  {dom=dom@(MDSobj donpos ddir)} {cod=cod@(MDSobj conpos cdir)}
  mor@(MDSM onpos ondir) =
    (fst (mlDirichSlObjToC dom) ** mlDirichSlMorToCBase {ar} {dom} {cod} mor)

public export
0 mlDirichSlMorToCD : {ar : MLArena} -> {dom, cod : MlDirichSlObj ar} ->
  MlDirichSlMor dom cod ->
  CDFSliceMorph ar (mlDirichSlObjToC dom) (mlDirichSlObjToC cod)
mlDirichSlMorToCD {ar=(ppos ** pdir)}
  {dom=dom@(MDSobj donpos ddir)} {cod=cod@(MDSobj conpos cdir)}
  mor@(MDSM monpos mondir)
      with
        (DFSliceMorphToC {p=(ppos ** pdir)} {cod=(mlDirichSlObjToC cod)}
          (mlDirichSlMorToD {dom} {cod} mor))
  mlDirichSlMorToCD {ar=(ppos ** pdir)}
    {dom=dom@(MDSobj donpos ddir)} {cod=cod@(MDSobj conpos cdir)}
    mor@(MDSM monpos mondir)
      | Element0 dmnt@(dmonpos ** dmondir) (Evidence0 opeq odeq) =
        Element0
         dmnt
         (Evidence0
            opeq
            $ \i : (DPair ppos donpos),
               d : (DPair (pdir (fst i)) (ddir (fst i) (snd i))) =>
                trans (odeq i d)
                $ case i of (i' ** j') => case d of (d' ** dd') => Refl)

public export
mlDirichSlMorFromD : {ar : MLArena} -> {cod : CDFSliceObj ar} ->
  (mor : DFSliceMorph {p=ar} cod) ->
  MlDirichSlMor
    (mlDirichSlObjFromC {ar} $ DFSliceMorphDom {p=ar} {cod} mor)
    (mlDirichSlObjFromC cod)
mlDirichSlMorFromD {ar=(ppos ** pdir)}
  {cod=((ctot ** cproj) ** (conpos ** condir))}
  ((mpos ** mdir) ** (monpos ** mondir)) =
    MDSM
      (\i, (Element0 j peq) => Element0 (monpos j) peq)
      (\i, (Element0 j peq), pd, (Element0 md deq) =>
        Element0 (mondir j md) deq)

public export
0 mlDirichSlMorFromCD : {ar : MLArena} -> {dom, cod : CDFSliceObj ar} ->
  (mor : CDFSliceMorph ar dom cod) ->
  MlDirichSlMor (mlDirichSlObjFromC {ar} dom) (mlDirichSlObjFromC {ar} cod)
mlDirichSlMorFromCD {ar=(ppos ** pdir)}
  {dom=((dtot ** dproj) ** (donpos ** dondir))}
  {cod=((ctot ** cproj) ** (conpos ** condir))}
  (Element0 (monpos ** mondir) (Evidence0 opeq odeq)) =
    MDSM
      (\i, (Element0 j peq) => Element0 (monpos j) $ trans (sym $ opeq j) peq)
      (\i, (Element0 j peq), pd, (Element0 md deq) =>
        Element0 (mondir j md) $
          trans (odeq j md) $ rewrite sym (opeq j) in deq)

public export
mlPolySlMorOnPos : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod ->
  mlPolySlObjTotPos {ar} dom -> mlPolySlObjTotPos {ar} cod
mlPolySlMorOnPos {ar} {dom} {cod} m i = (fst i ** mpsmOnPos m (fst i) (snd i))

public export
mlPolySlMorOnDir : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  (m : MlPolySlMor {ar} dom cod) ->
  (i : mlPolySlObjTotPos {ar} dom) ->
  mlPolySlObjTotDir {ar} cod (mlPolySlMorOnPos {ar} {dom} {cod} m i) ->
  mlPolySlObjTotDir {ar} dom i
mlPolySlMorOnDir {ar} {dom} {cod} m i = mpsmOnDir m (fst i) (snd i)

public export
mlPolySlMorNT : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod ->
  PolyNatTrans (mlPolySlObjTot {ar} dom) (mlPolySlObjTot {ar} cod)
mlPolySlMorNT {ar} {dom} {cod} m =
  (mlPolySlMorOnPos {ar} {dom} {cod} m ** mlPolySlMorOnDir {ar} {dom} {cod} m)

public export
0 mlPolySlMorToCP : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod ->
  CPFSliceMorph ar (mlPolySlObjToC ar dom) (mlPolySlObjToC ar cod)
mlPolySlMorToCP {ar=ar@(bpos ** bdir)}
  {dom=dom@(MPSobj dpos ddir dondir)} {cod=cod@(MPSobj cpos cdir condir)}
  m@(MPSM monpos mondir mondirc) =
    Element0
      (mlPolySlMorNT {ar} {dom} {cod} m)
      (Evidence0
        (\_ => Refl)
        (\ij, bd => mondirc (fst ij) (snd ij) bd))

public export
0 mlPolySlMorFromCP : {ar : MLArena} -> {dom, cod : CPFSliceObj ar} ->
  CPFSliceMorph ar dom cod ->
  MlPolySlMor {ar} (mlPolySlObjFromC ar dom) (mlPolySlObjFromC ar cod)
mlPolySlMorFromCP {ar=(bpos ** bdir)}
  {dom=dom@((dpos ** ddir) ** (donpos ** dondir))}
  {cod=cod@((cpos ** cdir) ** (conpos ** condir))}
  m@(Element0 (monpos ** mondir) (Evidence0 opeq odeq)) =
    MPSM
      (\i, (Element0 j poseq) =>
        Element0 (monpos j) $ trans (sym (opeq j)) poseq)
      (\i, (Element0 j poseq), cd => mondir j cd)
      (\i, (Element0 j poseq), bd => odeq j $ rewrite poseq in bd)

public export
0 mlPolySlMorToP : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod ->
  PFSliceMorph {p=ar} (mlPolySlObjToC ar cod)
mlPolySlMorToP {ar} {dom} {cod} =
  PFSliceMorphFromC {p=ar}
    {dom=(mlPolySlObjToC ar dom)} {cod=(mlPolySlObjToC ar cod)}
  . mlPolySlMorToCP {ar} {dom} {cod}

public export
0 mlPolySlMorFromP : {ar : MLArena} -> {cod : CPFSliceObj ar} ->
  (m : PFSliceMorph {p=ar} cod) ->
  MlPolySlMor {ar}
    (mlPolySlObjFromC ar $ PFSliceMorphDom {p=ar} {cod} m)
    (mlPolySlObjFromC ar cod)
mlPolySlMorFromP {ar} {cod} m =
  mlPolySlMorFromCP {ar} {dom=(PFSliceMorphDom {p=ar} m)} {cod}
  $ PFSliceMorphToC {p=ar} {cod} m

------------------------------------------------------------------
---- Translation between slice morphisms and slices-of-slices ----
------------------------------------------------------------------

public export
MlPolySlMorFromSlOfSl : {ar : MLArena} ->
  (cod : MlPolySlObj ar) -> (slsl : MlPolySlOfSl {ar} cod) ->
  MlPolySlMor {ar} (MlPolySlFromSlOfSl {ar} cod slsl) cod
MlPolySlMorFromSlOfSl {ar=(_ ** _)} (MPSobj _ _ _) slsl =
  MPSM
    (\i, jk => fst jk)
    (\i, jk, cd => (cd, mpsOnDir slsl (i ** fst jk) (snd jk) cd))
    (\i, jk, cd => Refl)

public export
MlPolySlMorToSlOfSl : {ar : MLArena} ->
  {dom, cod : MlPolySlObj ar} -> MlPolySlMor {ar} dom cod ->
  MlPolySlOfSl {ar} cod
MlPolySlMorToSlOfSl {ar} {dom} {cod} m =
  mlPolySlObjFromC
    (mlPolySlObjTot {ar} cod)
    (mlPolySlObjTot {ar} dom ** mlPolySlMorNT m)

public export
mlPolySlMorToObj : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod -> MlPolySlObj ar
mlPolySlMorToObj {ar} {dom} {cod} =
  MlPolySlFromSlOfSl {ar} cod . MlPolySlMorToSlOfSl {ar}

public export
mlPolySlMorTot : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod -> PolyFunc
mlPolySlMorTot {ar} {dom} {cod} =
  mlPolySlObjTot {ar=(mlPolySlObjTot {ar} cod)}
  . MlPolySlMorToSlOfSl {dom} {ar}

------------------------------------------------------------------------
------------------------------------------------------------------------
---- Interpretation of polynomial/Dirichlet slice objects/morphisms ----
------------------------------------------------------------------------
------------------------------------------------------------------------

-- This interprets an object in a slice category of Dirichlet functors
-- as an object in the category of presheaves over the category of elements
-- of the base functor.
public export
InterpMlDirichSlObj : {ar : PolyFunc} ->
  MlDirichSlObj ar -> (ty : Type) -> SliceObj $ InterpDirichFunc ar ty
InterpMlDirichSlObj {ar=(_ ** _)} (MDSobj slpos sldir) ty (i ** bd) =
  (j : slpos i ** Pi {a=ty} $ sldir i j . bd)

public export
InterpMlDirichSlObjF : {ar : PolyFunc} ->
  MlDirichSlObj ar -> MLDirichCatElemObj ar -> Type
InterpMlDirichSlObjF {ar=ar@(_ ** _)} sl (ty ** el) =
  InterpMlDirichSlObj {ar} sl ty el

public export
InterpMlDirichSlObjFMap : {bpos : Type} -> {bdir : bpos -> Type} ->
  (sl : MlDirichSlObj (bpos ** bdir)) ->
  (dom, cod : MLDirichCatElemObj (bpos ** bdir)) ->
  -- The functor is contravariant, hence the `cod dom` rather than `dom cod`.
  MLDirichCatElemMor (bpos ** bdir) cod dom ->
  InterpMlDirichSlObjF {ar=(bpos ** bdir)} sl dom ->
  InterpMlDirichSlObjF {ar=(bpos ** bdir)} sl cod
InterpMlDirichSlObjFMap {bpos} {bdir} (MDSobj slpos sldir)
  (dty ** i ** sldty) (cty ** _ ** _) (DCEM _ _ _ _ _ _ _ mm) =
    \(j ** sld) => (j ** \ec => sld $ mm ec)

public export
InterpMlDirichSlObjFMapAr : {ar : PolyFunc} ->
  (sl : MlDirichSlObj ar) ->
  (dom, cod : MLDirichCatElemObj ar) ->
  MLDirichCatElemMor ar cod dom ->
  InterpMlDirichSlObjF {ar} sl dom ->
  InterpMlDirichSlObjF {ar} sl cod
InterpMlDirichSlObjFMapAr {ar=(bpos ** bdir)} =
  InterpMlDirichSlObjFMap {bpos} {bdir}

-- This interprets a morphism in a slice category of Dirichlet functors
-- as a morphism in the category of presheaves over the category of elements
-- of the base functor (the latter is a natural transformation).
--
-- This implements a proof, in the particular case of Dirichlet functors,
-- that a slice category over a presheaf `p` is a presheaf over the category
-- of elements of `p`.
--
-- We may view this as the morphism component of a functor, whose object
-- component is `InterpMlDirichSlObj`, from the slice category of Dirichlet
-- functors over `ar` to the category of presheaves over the category of
-- elements of `ar`.
public export
InterpMlDirichSlMor : {ar : PolyFunc} ->
  {dom, cod : MlDirichSlObj ar} -> MlDirichSlMor dom cod ->
  (ty : Type) -> (el : InterpDirichFunc ar ty) ->
  InterpMlDirichSlObj {ar} dom ty el ->
  InterpMlDirichSlObj {ar} cod ty el
InterpMlDirichSlMor {ar=(bpos ** bdir)}
  {dom=(MDSobj dpos ddir)} {cod=(MDSobj cpos cdir)}
  (MDSM monpos mondir) ty (i ** bd) dpd =
    (monpos i (fst dpd) **
     \elty => mondir i (fst dpd) (bd elty) $ snd dpd elty)

-- This interprets an object in a slice category of polynomial functors
-- as an object in the category of presheaves over the category of elements
-- of the base functor.
public export
InterpMlPolySlObj : {ar : PolyFunc} ->
  MlPolySlObj ar -> (ty : Type) -> SliceObj $ InterpPolyFunc ar ty
InterpMlPolySlObj {ar} sl ty el with (mlPolySlObjToC ar sl)
  InterpMlPolySlObj {ar} sl ty el | (q ** alpha) =
    PreImage {a=(InterpPolyFunc q ty)} {b=(InterpPolyFunc ar ty)}
      (InterpPolyNT alpha ty) el

public export
InterpMlPolySlObjF : {ar : PolyFunc} ->
  MlPolySlObj ar -> MLPolyCatElemObj ar -> Type
InterpMlPolySlObjF {ar=ar@(_ ** _)} sl (ty ** el) =
  InterpMlPolySlObj {ar} sl ty el

public export
InterpMlPolySlObjFMap : {bpos : Type} -> {bdir : bpos -> Type} ->
  (sl : MlPolySlObj (bpos ** bdir)) ->
  (dom, cod : MLPolyCatElemObj (bpos ** bdir)) ->
  MLPolyCatElemMor (bpos ** bdir) dom cod ->
  InterpMlPolySlObjF {ar=(bpos ** bdir)} sl dom ->
  InterpMlPolySlObjF {ar=(bpos ** bdir)} sl cod
InterpMlPolySlObjFMap {bpos} {bdir} (MPSobj slpos sldir slondir)
  (dty ** i ** sldty) (cty ** _ ** _) (PCEM _ _ _ _ _ _ _ mm) =
    \(Element0 ((j ** k) ** sldi) eq) =>
      Element0
        ((j ** k) ** mm . sldi)
        $ case eq of Refl => Refl

public export
InterpMlPolySlObjFMapAr : {ar : PolyFunc} ->
  (sl : MlPolySlObj ar) ->
  (dom, cod : MLPolyCatElemObj ar) ->
  MLPolyCatElemMor ar dom cod ->
  InterpMlPolySlObjF {ar} sl dom ->
  InterpMlPolySlObjF {ar} sl cod
InterpMlPolySlObjFMapAr {ar=(bpos ** bdir)} =
  InterpMlPolySlObjFMap {bpos} {bdir}

-- This interprets a morphism in a slice category of polynomial functors
-- as a morphism in the category of copresheaves over the category of elements
-- of the base functor (the latter is a natural transformation).
--
-- This implements a proof, in the particular case of polynomial functors,
-- that a slice category over a copresheaf `p` is a copresheaf over the category
-- of elements of `p`.
--
-- We may view this as the morphism component of a functor, whose object
-- component is `InterpMlPolySlObj`, from the slice category of polynomial
-- functors over `ar` to the category of copresheaves over the category of
-- elements of `ar`.
public export
InterpMlPolySlMor : FunExt -> {ar : PolyFunc} ->
  {dom, cod : MlPolySlObj ar} -> MlPolySlMor dom cod ->
  (ty : Type) -> (el : InterpPolyFunc ar ty) ->
  InterpMlPolySlObj {ar} dom ty el ->
  InterpMlPolySlObj {ar} cod ty el
InterpMlPolySlMor fext {ar=(bpos ** bdir)}
  {dom=(MPSobj dpos ddir dondir)} {cod=(MPSobj cpos cdir condir)}
  (MPSM monpos mondir mondircomm) ty el (Element0 (i ** dd) eleq) =
    Element0
      ((fst i ** monpos (fst i) (snd i)) **
       \cd => dd $ mondir (fst i) (snd i) cd)
      $ trans
        (dpEq12 Refl $ funExt $ \bd => cong dd $ mondircomm (fst i) (snd i) bd)
        eleq

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---- Slice categories of polynomial functors (in dependent-type style) ----
---------------------------------------------------------------------------
---------------------------------------------------------------------------

------------------------------------------------------
---- Polynomial-functor slice functor definitions ----
------------------------------------------------------

public export
0 MlDirichSlFunc : MLArena -> MLArena -> Type
MlDirichSlFunc p q = MlDirichSlObj p -> MlDirichSlObj q

public export
0 MlDirichSlFMap : {ar, ar' : MLArena} -> MlDirichSlFunc ar ar' -> Type
MlDirichSlFMap {ar} {ar'} f =
  (0 sl, sl' : MlDirichSlObj ar) ->
  MlDirichSlMor {ar} sl sl' -> MlDirichSlMor {ar=ar'} (f sl) (f sl')

public export
0 MlPolySlFunc : MLArena -> MLArena -> Type
MlPolySlFunc p q = MlPolySlObj p -> MlPolySlObj q

public export
0 MlPolySlFMap : {ar, ar' : MLArena} -> MlPolySlFunc ar ar' -> Type
MlPolySlFMap {ar} {ar'} f =
  (0 sl, sl' : MlPolySlObj ar) ->
  MlPolySlMor {ar} sl sl' -> MlPolySlMor {ar=ar'} (f sl) (f sl')

---------------------
---- Base change ----
---------------------

-- When we express slice objects over a polynomial functor as fibrations
-- rather than total-space objects with projection morphisms, we can perform
-- base changes by specifying the data not of a polynomial natural
-- transformation, but of a Dirichlet natural transformation.
public export
mlPolySlBaseChange : {p, q : PolyFunc} ->
  DirichNatTrans q p -> MlPolySlFunc p q
mlPolySlBaseChange {p} {q} (onpos ** ondir) (MPSobj slonpos sldir slondir) =
  MPSobj
    (slonpos . onpos)
    (\i => sldir $ onpos i)
    (\i, j, qd => slondir (onpos i) j $ ondir i qd)

public export
mlPolySlBaseChangeMap : {p, q : PolyFunc} -> (nt : DirichNatTrans q p) ->
  MlPolySlFMap {ar=p} {ar'=q} (mlPolySlBaseChange {p} {q} nt)
mlPolySlBaseChangeMap {p} {q} (ntonpos ** ntondir)
  (MPSobj dpos ddir dondir) (MPSobj cpos cdir condir) m =
    MPSM
      (\qp => mpsmOnPos m (ntonpos qp))
      (\qp, dp, cd => mpsmOnDir m (ntonpos qp) dp cd)
      (\qp, dp, bd => mpsmOnDirCommutes m (ntonpos qp) dp (ntondir qp bd))

public export
mlDirichSlBaseChange : {p, q : PolyFunc} ->
  DirichNatTrans q p -> MlDirichSlFunc p q
mlDirichSlBaseChange {p} {q} (onpos ** ondir) (MDSobj slpos sldir) =
  MDSobj (slpos . onpos) (\qp, sp, qd => sldir (onpos qp) sp $ ondir qp qd)

public export
mlDirichSlBaseChangeMap : {p, q : PolyFunc} -> (nt : DirichNatTrans q p) ->
  MlDirichSlFMap {ar=p} {ar'=q} (mlDirichSlBaseChange {p} {q} nt)
mlDirichSlBaseChangeMap {p} {q} (ntonpos ** ntondir)
  (MDSobj dpos ddir) (MDSobj cpos cdir) (MDSM monpos mondir) =
    MDSM
      (\qp, dp => monpos (ntonpos qp) dp)
      (\qp, dp, qd, dd => mondir (ntonpos qp) dp (ntondir qp qd) dd)

-------------------------------
---- Sigma (dependent sum) ----
-------------------------------

MLPolySlSigma : (q : PolyFunc) -> {p : PolyFunc} ->
  PolyNatTrans p q -> MlPolySlObj p -> MlPolySlObj q
MLPolySlSigma q {p} beta sl with (mlPolySlObjToC p sl)
  MLPolySlSigma q {p} beta sl | (r ** alpha) =
    let csigma = (r ** pntVCatComp beta alpha) in
    mlPolySlObjFromC q csigma

-------------------------------------------------------------
---- Polynomial-functor slice category utility functions ----
-------------------------------------------------------------

-- A slice object over a constant functor is effectively a polynomial
-- functor parameterized over terms of the output type of the constant functor.
mlPolySliceOverConst : {x : Type} -> MlPolySlObj (PFConstArena x) ->
  ParamPolyFunc x
mlPolySliceOverConst {x} (MPSobj onpos dir ondir) ex =
  -- The arguments of `ondir` include a term of type `Void`, so
  -- it is impossible to apply (unless we find such a term, and
  -- hence a contradiction in our metalanguage).  Thus we can and
  -- must ignore it.
  --
  -- Put another way, `ondir` gives us no information, because its type
  -- restricts it to being effectively just the unique morphism out
  -- of the initial object.
  (onpos ex ** \i => dir ex i)

-- A slice object over the terminal polynomial functor is effectively
-- just a polynomial functor, just as a slice of `Type` over `Unit` is
-- effectively just a type.
mlPolySliceOver1 : MlPolySlObj PFTerminalArena -> PolyFunc
mlPolySliceOver1 psl = mlPolySliceOverConst {x=Unit} psl ()

mlPolyAppI : {p : PolyFunc} ->
  {- these two parameters form an object of the category of elements of `p`
   - interpreted as a Dirichlet functor -}
  (ty : Type) -> (el : InterpDirichFunc p ty) ->
  MlPolySlObj p -> MlPolySlObj (PFHomArena ty)
mlPolyAppI {p=p@(_ ** _)} ty (i ** d) =
  mlPolySlBaseChange {p} {q=(PFHomArena ty)} (\() => i ** \() => d)

-- By analogy with the application of a `SliceObj x` in `Type` to a term
-- of `x`, `PFApp` is a base change from the slice category over `p` to
-- the slice category over the terminal polynomial functor, which is
-- effectively just the category of polynomial endofunctors on `Type`.
-- Such a base change requires a Dirichlet (not polynomial!) natural
-- transformation from the terminal polynomial functor (which is just
-- a single position with no directions) to the functor being sliced over.
-- That in turn amounts to simply a choice of position of the functor
-- being sliced over, which dictates which dependent polynomial functor
-- to select as the result.
mlPolyApp1 : {p : PolyFunc} -> pfPos p -> MlPolySlObj p -> PolyFunc
mlPolyApp1 {p=p@(pos ** dir)} i slp =
  mlPolySliceOver1 $ mlPolyAppI {p} Void (i ** \v => void v) slp

----------------------------
----------------------------
---- Generalized arenas ----
----------------------------
----------------------------

--------------------
---- Telescopes ----
--------------------

data MLTelFPos : (tl : Type) -> Type where
  MLUnitPos : {0 tl : Type} -> MLTelFPos tl
  MLDPairPos : {0 tl : Type} -> SliceObj tl -> MLTelFPos tl

MLTelFDir : Sigma {a=Type} MLTelFPos -> Type
MLTelFDir (tl ** MLUnitPos) = Void
MLTelFDir (tl ** (MLDPairPos {tl} sl)) = Unit

MLTelFAssign : Sigma {a=(Sigma {a=Type} MLTelFPos)} MLTelFDir -> Type
MLTelFAssign ((tl ** MLUnitPos) ** v) = void v
MLTelFAssign ((tl ** (MLDPairPos {tl} sl)) ** ()) = Sigma {a=tl} sl

MLTelF : SlicePolyEndoFunc Type
MLTelF = (MLTelFPos ** MLTelFDir ** MLTelFAssign)

MLTel : Type -> Type
MLTel = SPFMu MLTelF

MLFreeTel : SliceEndofunctor Type
MLFreeTel = SlicePolyFree MLTelF

----------------------------------------------
----------------------------------------------
---- Factorized slice polynomial functors ----
----------------------------------------------
----------------------------------------------

-- Because `Cat` has a factorization system -- all functors can be factored
-- into two, via a category of elements of a functor out of the codomain --
-- we could also choose to _define_ a functor as a composite of two functors
-- of that specific form.

-- So we begin with a definition of a polynomial (co)presheaf on a slice
-- category.
public export
SlPolyAr : Type -> Type
SlPolyAr c = IntArena (SliceObj c)

public export
SlIntComp : (c : Type) -> IntCompSig (SliceObj c) (SliceMorphism {a=c})
SlIntComp c x y z g f = \ela, elx => g ela $ f ela elx

public export
SlArInterp : {c : Type} -> SlPolyAr c -> SliceObj c -> Type
SlArInterp {c} = InterpIPFobj (SliceObj c) (SliceMorphism {a=c})

public export
0 SlPolyArMapSig : {c : Type} -> SlPolyAr c -> Type
SlPolyArMapSig {c} ar =
  IntCopreshfMapSig (SliceObj c) (SliceMorphism {a=c}) (SlArInterp {c} ar)

public export
SlArFMap : {c : Type} -> (ar : SlPolyAr c) -> SlPolyArMapSig {c} ar
SlArFMap {c} = InterpIPFmap (SliceObj c) (SliceMorphism {a=c}) (SlIntComp c)
