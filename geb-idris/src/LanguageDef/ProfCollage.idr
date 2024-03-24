module LanguageDef.ProfCollage

import Library.IdrisUtils
import Library.IdrisCategories

---------------------------------------------
---------------------------------------------
---- Metalanguage difunctors as collages ----
---------------------------------------------
---------------------------------------------

---------------------------------------------------------
---- Definition of metalanguage difunctor as collage ----
---------------------------------------------------------

public export
record MLCollage where
  constructor MLC
  mlcHetIdx : Type
  mlcDom : SliceObj mlcHetIdx
  mlcCod : SliceObj mlcHetIdx

export
InterpMLC : MLCollage -> ProfunctorSig
InterpMLC mlc x y =
  (i : mlcHetIdx mlc ** (x -> mlcDom mlc i, mlcCod mlc i -> y))

export
InterpMLClmap : (mlc : MLCollage) ->
  (0 s, t, a : Type) -> (a -> s) -> InterpMLC mlc s t -> InterpMLC mlc a t
InterpMLClmap mlc s t a mas pst =
  (fst pst ** (fst (snd pst) . mas, snd (snd pst)))

export
InterpMLCrmap : (mlc : MLCollage) ->
  (0 s, t, b : Type) -> (t -> b) -> InterpMLC mlc s t -> InterpMLC mlc s b
InterpMLCrmap mlc s t b mtb pst =
  (fst pst ** (fst (snd pst), mtb . snd (snd pst)))

export
InterpMLCdimap : (mlc : MLCollage) ->
  (0 s, t, a, b : Type) -> (a -> s) -> (t -> b) ->
    InterpMLC mlc s t -> InterpMLC mlc a b
InterpMLCdimap mlc s t a b mas mtb =
  InterpMLClmap mlc s b a mas . InterpMLCrmap mlc s t b mtb

-----------------------------------------------------------------
---- Natural transformations between metalanguage difunctors ----
-----------------------------------------------------------------

public export
record MLCNatTrans (p, q : MLCollage) where
  constructor MLNT
  mpOnIdx : mlcHetIdx p -> mlcHetIdx q
  mpOnDom :
    (i : mlcHetIdx p) -> mlcDom p i ->
      mlcDom q (mpOnIdx i)
  mpOnCod :
    (i : mlcHetIdx p) -> mlcCod q (mpOnIdx i) ->
      mlcCod p i

export
InterpMLCnt : {0 p, q : MLCollage} -> MLCNatTrans p q ->
  (0 x, y : Type) -> InterpMLC p x y -> InterpMLC q x y
InterpMLCnt {p} {q} (MLNT oni ond onc) x y (i ** (dd, dc)) =
  (oni i ** (ond i . dd, dc . onc i))

export
0 InterpMLCisNatural : {0 p, q : MLCollage} -> (mlnt : MLCNatTrans p q) ->
  (0 s, t, a, b : Type) ->
  (mas : a -> s) -> (mtb : t -> b) ->
  ExtEq {a=(InterpMLC p s t)} {b=(InterpMLC q a b)}
    (InterpMLCdimap q s t a b mas mtb . InterpMLCnt {p} {q} mlnt s t)
    (InterpMLCnt {p} {q} mlnt a b . InterpMLCdimap p s t a b mas mtb)
InterpMLCisNatural {p=(MLC ph pd pc)} {q=(MLC qh qd qc)}
  (MLNT onidx ondom oncod) s t a b mas mtb (pi ** (spd, pct)) =
    dpEq12 Refl $ pairEqCong Refl Refl

---------------------------------------------------------------------
---- Paranatural transformations between metalanguage difunctors ----
---------------------------------------------------------------------

public export
record MLCParaNT (p, q : MLCollage) where
  constructor MLPNT
  mpOnIdx : mlcHetIdx p -> mlcHetIdx q
  mpOnDom :
    (i : mlcHetIdx p) -> (mlcCod p i -> mlcDom p i) -> mlcDom p i ->
      mlcDom q (mpOnIdx i)
  mpOnCod :
    (i : mlcHetIdx p) -> (mlcCod p i -> mlcDom p i) -> mlcCod q (mpOnIdx i) ->
      mlcCod p i

export
InterpMLCpara : {0 p, q : MLCollage} -> MLCParaNT p q ->
  (0 x : Type) -> InterpMLC p x x -> InterpMLC q x x
InterpMLCpara {p} {q} (MLPNT oni ond onc) x (i ** (dd, dc)) =
  (oni i ** (ond i (dd . dc) . dd, dc . onc i (dd . dc)))

export
0 InterpMLCisPara : {0 p, q : MLCollage} -> (mlpnt : MLCParaNT p q) ->
  (i0, i1 : Type) -> (i2 : i0 -> i1) ->
  (d0 : InterpMLC p i0 i0) -> (d1 : InterpMLC p i1 i1) ->
  (InterpMLClmap p i1 i1 i0 i2 d1 = InterpMLCrmap p i0 i0 i1 i2 d0) ->
  (InterpMLClmap q i1 i1 i0 i2 (InterpMLCpara {p} {q} mlpnt i1 d1) =
   InterpMLCrmap q i0 i0 i1 i2 (InterpMLCpara {p} {q} mlpnt i0 d0))
InterpMLCisPara {p=(MLC ph pd pc)} {q=(MLC qh qd qc)} (MLPNT onidx ondom oncod)
  i0 i1 i2 (pi0 ** (i0d0, c0i0)) (pi1 ** (i1d1, c1i1)) cond =
    case mkDPairInjectiveFstHet cond of
      Refl => case mkDPairInjectiveSndHet cond of
        Refl => dpEq12 Refl
          $ pairEqCong Refl Refl

-------------------------------------------
---- Monoid of metalanguage difunctors ----
-------------------------------------------

-- Metalanguage difunctors form a monoid -- a one-object category, with
-- the difunctors as morphisms -- whose identity is the hom-profunctor, and
-- whose composition is the usual composition of profunctors.

-- We represent the hom-profunctor with simply one position (index) per
-- morphism.
export
MlcHomProfId : MLCollage
MlcHomProfId =
  MLC (dom : Type ** cod : Type ** dom -> cod) fst (\i => fst $ snd i)

InterpToIdMLC : (x, y : Type) -> (x -> y) -> InterpMLC MlcHomProfId x y
InterpToIdMLC x y m = ((x ** y ** m) ** (id, id))

InterpFromIdMLC : (x, y : Type) -> InterpMLC MlcHomProfId x y -> x -> y
InterpFromIdMLC x y ((i ** j ** mij) ** (mxi, mjy)) = mjy . mij . mxi

-- Composition of difunctors can be expressed in the form of a composition
-- of collages.
export
mlcComp : MLCollage -> MLCollage -> MLCollage
mlcComp (MLC qh qd qc) (MLC ph pd pc) =
  MLC
    (qi : qh ** pi : ph ** qc qi -> pd pi)
    (\(qi ** pi ** qcpd) => qd qi)
    (\(qi ** pi ** qcpd) => pc pi)

InterpToComposeMLC : (q, p : MLCollage) -> (x, y : Type) ->
  EndoProfCompose (InterpMLC q) (InterpMLC p) x y ->
  InterpMLC (mlcComp q p) x y
InterpToComposeMLC (MLC qh qd qc) (MLC ph pd pc) x y
  (b ** ((qi ** (xqd, qcb)), (pi ** (bpd, pcy)))) =
    ((qi ** pi ** bpd . qcb) ** (xqd, pcy))

InterpFromComposeMLC : (q, p : MLCollage) -> (x, y : Type) ->
  InterpMLC (mlcComp q p) x y ->
  EndoProfCompose (InterpMLC q) (InterpMLC p) x y
InterpFromComposeMLC (MLC qh qd qc) (MLC ph pd pc) x y
  ((qi ** pi ** qcpd) ** (xqd, pcy)) =
    (pd pi ** ((qi ** (xqd, qcpd)), (pi ** (id, pcy))))

--------------------------------------------------------------------------------
---- Category of metalanguage difunctors with (para)natural transformations ----
--------------------------------------------------------------------------------

-- In addition to the monoid of metalanguage difunctors, where the difunctors
-- are morphisms, there are also categories where the difunctors are objects.
-- In one such category, the natural transformations are the morphisms; in
-- another such category, the paranatural transformations are the morphisms.

export
mlcNTid : (mlc : MLCollage) -> MLCNatTrans mlc mlc
mlcNTid mlc = MLNT id (\_ => id) (\_ => id)

export
mlcPNTid : (mlc : MLCollage) -> MLCParaNT mlc mlc
mlcPNTid mlc = MLPNT id (\_, _ => id) (\_, _ => id)

export
mlcNTcomp : {0 r, q, p : MLCollage} -> MLCNatTrans q r -> MLCNatTrans p q ->
  MLCNatTrans p r
mlcNTcomp {r=(MLC rh rd rc)} {q=(MLC qh qd qc)} {p=(MLC ph pd pc)}
  (MLNT onidxqr ondomqr oncodqr) (MLNT onidxpq ondompq oncodpq) =
    MLNT
      (onidxqr . onidxpq)
      (\pi, pdi => ondomqr (onidxpq pi) (ondompq pi pdi))
      (\pi, rci => oncodpq pi (oncodqr (onidxpq pi) rci))

export
mlcPNTcomp : {0 r, q, p : MLCollage} -> MLCParaNT q r -> MLCParaNT p q ->
  MLCParaNT p r
mlcPNTcomp {r=(MLC rh rd rc)} {q=(MLC qh qd qc)} {p=(MLC ph pd pc)}
  (MLPNT onidxqr ondomqr oncodqr) (MLPNT onidxpq ondompq oncodpq) =
    let
      qcd :
        ((pi : ph) -> (pc pi -> pd pi) -> qc (onidxpq pi) -> qd (onidxpq pi)) =
          \pi, pcd, qci => ondompq pi pcd (pcd $ oncodpq pi pcd qci)
    in
    MLPNT
      (onidxqr . onidxpq)
      (\pi, pcd, pdi => ondomqr (onidxpq pi) (qcd pi pcd) (ondompq pi pcd pdi))
      (\pi, pcd, rci => oncodpq pi pcd (oncodqr (onidxpq pi) (qcd pi pcd) rci))

------------------------------------------------------------------------------
---- Two-categorical structure of (para)natural difunctor transformations ----
------------------------------------------------------------------------------

-- The (para)natural transformations of difunctors form a two-category:
-- (para)natural transformations have horizontal composition and whiskering.
