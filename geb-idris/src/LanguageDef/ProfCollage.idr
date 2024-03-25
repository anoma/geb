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
  mlcContra : SliceObj mlcHetIdx
  mlcCovar : SliceObj mlcHetIdx

export
InterpMLC : MLCollage -> ProfunctorSig
InterpMLC mlc x y =
  (i : mlcHetIdx mlc ** (x -> mlcContra mlc i, mlcCovar mlc i -> y))

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
    (\(qi ** pi ** qcpd) => qd qi) -- XXX note qcpd is never used anywhere!
    (\(qi ** pi ** qcpd) => pc pi) -- XXX note qcpd is never used anywhere!

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

-----------------------------------------------------------------
---- Natural transformations between metalanguage difunctors ----
-----------------------------------------------------------------

public export
record MLCNatTrans (p, q : MLCollage) where
  constructor MLNT
  mpOnIdx : mlcHetIdx p -> mlcHetIdx q
  mpOnContra :
    (i : mlcHetIdx p) -> mlcContra p i ->
      mlcContra q (mpOnIdx i)
  mpOnCovar :
    (i : mlcHetIdx p) -> mlcCovar q (mpOnIdx i) ->
      mlcCovar p i

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
  (MLNT onidx oncontra oncovar) s t a b mas mtb (pi ** (spd, pct)) =
    dpEq12 Refl $ pairEqCong Refl Refl

--------------------------------------------------------------------------
---- Category of metalanguage difunctors with natural transformations ----
--------------------------------------------------------------------------

-- In addition to the monoid of metalanguage difunctors, where the difunctors
-- are morphisms, there are also categories where the difunctors are objects.
-- In one such category, the natural transformations are the morphisms; in
-- another such category, the paranatural transformations are the morphisms.

export
mlcNTid : (mlc : MLCollage) -> MLCNatTrans mlc mlc
mlcNTid mlc = MLNT id (\_ => id) (\_ => id)

export
mlcNTvcomp : {0 r, q, p : MLCollage} -> MLCNatTrans q r -> MLCNatTrans p q ->
  MLCNatTrans p r
mlcNTvcomp {r=(MLC rh rd rc)} {q=(MLC qh qd qc)} {p=(MLC ph pd pc)}
  (MLNT onidxqr oncontraqr oncovarqr) (MLNT onidxpq oncontrapq oncovarpq) =
    MLNT
      (onidxqr . onidxpq)
      (\pi, pdi => oncontraqr (onidxpq pi) (oncontrapq pi pdi))
      (\pi, rci => oncovarpq pi (oncovarqr (onidxpq pi) rci))

------------------------------------------------------------------------
---- Two-categorical structure of natural difunctor transformations ----
------------------------------------------------------------------------

-- The natural transformations of difunctors form a two-category:
-- natural transformations have horizontal composition and whiskering.

export
mlcNTwhiskerL : {0 q, r : MLCollage} -> MLCNatTrans q r -> (0 p : MLCollage) ->
  MLCNatTrans (mlcComp q p) (mlcComp r p)
mlcNTwhiskerL {q=(MLC qh qd qc)} {r=(MLC rh rd rc)}
  (MLNT onidx oncontra oncovar) (MLC ph pd pc) =
    MLNT
      (\(qi ** pi ** qcpd) => (onidx qi ** pi ** qcpd . oncovar qi))
      (\(qi ** pi ** qcpd) => oncontra qi)
      (\(qi ** pi ** qcpd) => id)

export
mlcNTwhiskerR : {0 p, q : MLCollage} -> MLCNatTrans p q -> (0 r : MLCollage) ->
  MLCNatTrans (mlcComp r p) (mlcComp r q)
mlcNTwhiskerR {p=(MLC ph pd pc)} {q=(MLC qh qd qc)}
  (MLNT onidx oncontra oncovar) (MLC rh rd rc) =
    MLNT
      (\(ri ** pi ** rcpd) => (ri ** onidx pi ** oncontra pi . rcpd))
      (\(ri ** pi ** rcpd) => id)
      (\(ri ** pi ** rcpd) => oncovar pi)

export
mlcNThcomp : {0 p, p', q, q' : MLCollage} ->
  MLCNatTrans q q' ->
  MLCNatTrans p p' ->
  MLCNatTrans (mlcComp q p) (mlcComp q' p')
mlcNThcomp {p} {p'} {q} {q'} beta alpha =
  mlcNTvcomp
    (mlcNTwhiskerL {q} {r=q'} beta p')
    (mlcNTwhiskerR {p} {q=p'} alpha q)

-----------------------------------------------------------------
-----------------------------------------------------------------
---- Polydifunctors subject to polydinatural transformations ----
-----------------------------------------------------------------
-----------------------------------------------------------------

-------------------------------------
---- Arena form of polydifunctor ----
-------------------------------------

-- The positions of a polydifunctor map not to directions which are not
-- objects of `Type`, but morphisms (of `Type`).  In light of the
-- interpretation below, we can view these morphisms as objects of the
-- twisted arrow category of `Type`.
public export
record PolyDifunc where
  constructor PDF
  pdfPos : Type
  pdfDom : SliceObj pdfPos
  pdfCod : SliceObj pdfPos
  pdfMorph : (i : pdfPos) -> pdfDom i -> pdfCod i

-- The interpretation of a polydifunctor treats its inputs and outputs
-- as a domain and codomain, and comprises a choice of morphism from
-- domain and codomain, a choice of position of the polydifunctor, and
-- a twisted-arrow morphism from the chosen morphism to the corresponding
-- direction of the polydifunctor.
export
record InterpPDF (pdf : PolyDifunc) (x, y : Type) where
  constructor IPDF
  ipdfPos : pdfPos pdf
  ipdfDom : x -> pdfDom pdf ipdfPos
  ipdfCod : pdfCod pdf ipdfPos -> y
  ipdfMorph : x -> y
  0 ipdfComm : FunExt -> (ipdfCod . pdfMorph pdf ipdfPos . ipdfDom = ipdfMorph)

export
InterpPDFlmap : (pdf : PolyDifunc) ->
  (0 s, t, a : Type) -> (a -> s) -> InterpPDF pdf s t -> InterpPDF pdf a t
InterpPDFlmap (PDF pos dom cod morph) s t a mas (IPDF i msd mit mst comm) =
  IPDF
    i
    (msd . mas)
    mit
    (mst . mas)
    (\fext => funExt $ \_ => rewrite sym (comm fext) in Refl)

export
InterpPDFrmap : (pdf : PolyDifunc) ->
  (0 s, t, b : Type) -> (t -> b) -> InterpPDF pdf s t -> InterpPDF pdf s b
InterpPDFrmap (PDF pos dom cod morph) s t b mtb (IPDF i msd mct mst comm) =
  IPDF
    i
    msd
    (mtb . mct)
    (mtb . mst)
    (\fext => funExt $ \_ => rewrite sym (comm fext) in Refl)

export
InterpPDFdimap : (pdf : PolyDifunc) ->
  (0 s, t, a, b : Type) -> (a -> s) -> (t -> b) ->
    InterpPDF pdf s t -> InterpPDF pdf a b
InterpPDFdimap pdf s t a b mas mtb =
  InterpPDFlmap pdf s b a mas . InterpPDFrmap pdf s t b mtb

----------------------------------
---- Monoid of polydifunctors ----
----------------------------------

-- Polydifunctors form a monoid -- a one-object category, with
-- the polydifunctors as morphisms -- whose identity is the hom-profunctor,
-- and whose composition is the usual composition of profunctors.

-- We represent the hom-profunctor, which is the identity of the monoid of
-- polydifunctors, with one position per morphism of `Type`.

export
PdfHomProfId : PolyDifunc
PdfHomProfId =
  PDF
    (dom : Type ** cod : Type ** dom -> cod)
    fst
    (\i => fst $ snd i)
    (\i => snd $ snd i)

InterpToIdPDF : (x, y : Type) -> (x -> y) -> InterpPDF PdfHomProfId x y
InterpToIdPDF x y m = IPDF (x ** y ** m) id id m (\_ => Refl)

InterpFromIdPDF : (x, y : Type) -> InterpPDF PdfHomProfId x y -> x -> y
InterpFromIdPDF x y (IPDF (i ** j ** mij) mxi mjy mxy comm) =
  -- There are two ways of getting from `x` to `y` -- `mxy` and
  -- `mjy . mij . mxi`. But `comm` shows them to be equal.
  -- We make that explicit here to make sure, and to document, that
  -- `mjy`, `mij`, and `mxi` are not "unused", but rather are an
  -- alternative to the `mxy` which we do use.
  let 0 eqm : (FunExt -> mjy . mij . mxi = mxy) = comm in
  mxy

-- The arena form of polydifunctors is closed under composition.
export
pdfComp : PolyDifunc -> PolyDifunc -> PolyDifunc
pdfComp (PDF qp qd qc qm) (PDF pp pd pc pm) =
  PDF
    (qi : qp ** pi : pp ** qc qi -> pd pi)
    (\(qi ** pi ** qcpd) => qd qi)
    (\(qi ** pi ** qcpd) => pc pi)
    (\(qi ** pi ** qcpd), qdi => pm pi $ qcpd $ qm qi qdi)

InterpToComposePDF : (q, p : PolyDifunc) -> (x, y : Type) ->
  EndoProfCompose (InterpPDF q) (InterpPDF p) x y ->
  InterpPDF (pdfComp q p) x y
InterpToComposePDF (PDF qp qd qc qm) (PDF pp pd pc pm) x y
  (b ** (IPDF qi mxqd mqcb mxb qcomm, IPDF pi mbpd mpcy mby pcomm)) =
    IPDF
      (qi ** pi ** mbpd . mqcb)
      mxqd
      mpcy
      (mby . mxb)
      (\fext => rewrite sym (qcomm fext) in rewrite sym (pcomm fext) in Refl)

InterpFromComposePDF : (q, p : PolyDifunc) -> (x, y : Type) ->
  InterpPDF (pdfComp q p) x y ->
  EndoProfCompose (InterpPDF q) (InterpPDF p) x y
InterpFromComposePDF (PDF qp qd qc qm) (PDF pp pd pc pm) x y
  (IPDF (qi ** pi ** qcpd) mxqd mpcy mxy comm) =
    (pd pi **
      (IPDF qi mxqd qcpd (qcpd . qm qi . mxqd) $ \_ => Refl,
      (IPDF pi id mpcy (mpcy . pm pi) $ \_ => Refl)))

-----------------------------------------------------------------------
---- Polydinatural transformations between metalanguage difunctors ----
-----------------------------------------------------------------------

public export
record PolyDiNT (p, q : PolyDifunc) where
  constructor PDNT
  pdntOnIdx : pdfPos p -> pdfPos q
  pdntOnDom : (i : pdfPos p) -> pdfDom p i -> pdfDom q (pdntOnIdx i)
  pdntOnCod : (i : pdfPos p) -> pdfCod q (pdntOnIdx i) -> pdfCod p i
  pdntComm : (i : pdfPos p) -> FunExt ->
    (pdntOnCod i . pdfMorph q (pdntOnIdx i) . pdntOnDom i = pdfMorph p i)

export
InterpPDNT : {0 p, q : PolyDifunc} -> PolyDiNT p q ->
  (0 x : Type) -> InterpPDF p x x -> InterpPDF q x x
InterpPDNT {p=(PDF pp pd pc pm)} {q=(PDF qp qd qc qm)}
  (PDNT oni ond onc ntcomm) x (IPDF pi mxpd mpcx mxx pcomm) =
    IPDF
      (oni pi)
      (ond pi . mxpd)
      (mpcx . onc pi)
      mxx
      (\fext =>
        trans
          (funExt $ \ex =>
            cong mpcx $
              fcong
                {f=(onc pi . qm (oni pi) . ond pi)}
                {g=(pm pi)}
                {x=(mxpd ex)}
                $ ntcomm pi fext)
          $ pcomm fext)

export
0 InterpPDFisStrong : {0 p, q : PolyDifunc} -> (pdnt : PolyDiNT p q) ->
  (i0, i1 : Type) -> (i2 : i0 -> i1) ->
  (d0 : InterpPDF p i0 i0) -> (d1 : InterpPDF p i1 i1) ->
  (InterpPDFlmap p i1 i1 i0 i2 d1 = InterpPDFrmap p i0 i0 i1 i2 d0) ->
  (InterpPDFlmap q i1 i1 i0 i2 (InterpPDNT {p} {q} pdnt i1 d1) =
   InterpPDFrmap q i0 i0 i1 i2 (InterpPDNT {p} {q} pdnt i0 d0))
InterpPDFisStrong {p=(PDF pp pd pc pm)} {q=(PDF qp qd qc qm)}
  (PDNT onidx ondom oncod ntcomm) i0 i1 i2
  (IPDF pi0 mi0pd mpci0 mi0i0 pcomm) (IPDF pi1 mi1pd mpci1 mi1i1 qcomm) cond =
    ?InterpPDFisStrong_hole
  {- XXX
  (pi0 ** (i0d0, c0i0)) (pi1 ** (i1d1, c1i1)) cond =
    case mkDPairInjectiveFstHet cond of
      Refl => case mkDPairInjectiveSndHet cond of
        Refl => dpEq12 Refl
          $ pairEqCong Refl Refl
          -}

{- XXX
--------------------------------------------------------------------------------
---- Category of metalanguage difunctors with paranatural transformations ----
--------------------------------------------------------------------------------

export
pdfPNTid : (pdf : PolyDifunc) -> PolyDiNT pdf pdf
pdfPNTid pdf = PDNT id (\_, _ => id) (\_, _ => id)

export
pdfPNTvcomp : {0 r, q, p : PolyDifunc} -> PolyDiNT q r -> PolyDiNT p q ->
  PolyDiNT p r
pdfPNTvcomp {r=(PDF rh rd rc)} {q=(PDF qh qd qc)} {p=(PDF ph pd pc)}
  (PDNT onidxqr oncontraqr oncovarqr) (PDNT onidxpq oncontrapq oncovarpq) =
    let
      qcd :
        ((pi : ph) -> (pc pi -> pd pi) -> qc (onidxpq pi) -> qd (onidxpq pi)) =
          \pi, pcd, qci => oncontrapq pi pcd (pcd $ oncovarpq pi pcd qci)
    in
    PDNT
      (onidxqr . onidxpq)
      (\pi, pcd, pdi =>
        oncontraqr (onidxpq pi) (qcd pi pcd) (oncontrapq pi pcd pdi))
      (\pi, pcd, rci =>
        oncovarpq pi pcd (oncovarqr (onidxpq pi) (qcd pi pcd) rci))

----------------------------------------------------------------------------
---- Two-categorical structure of paranatural difunctor transformations ----
----------------------------------------------------------------------------

-- The paranatural transformations of difunctors form a two-category:
-- paranatural transformations have horizontal composition and whiskering.

export
pdfPNTwhiskerL : {0 q, r : PolyDifunc} -> PolyDiNT q r -> (0 p : PolyDifunc) ->
  PolyDiNT (pdfComp q p) (pdfComp r p)
pdfPNTwhiskerL {q=(PDF qh qd qc)} {r=(PDF rh rd rc)}
  (PDNT onidx oncontra oncovar) (PDF ph pd pc) =
    PDNT
      (\(qi ** pi ** qcpd) =>
        (onidx qi ** pi ** qcpd . oncovar qi pdfPNTwhiskerL_hole_onidx))
      (\(qi ** pi ** qcpd), pcqd, qdi =>
        oncontra qi pdfPNTwhiskerL_hole_oncontra qdi)
      (\(qi ** pi ** qcpd), pcqd =>
        id)

export
pdfPNTwhiskerR : {0 p, q : PolyDifunc} -> PolyDiNT p q -> (0 r : PolyDifunc) ->
  PolyDiNT (pdfComp r p) (pdfComp r q)
pdfPNTwhiskerR {p=(PDF ph pd pc)} {q=(PDF qh qd qc)}
  (PDNT onidx oncontra oncovar) (PDF rh rd rc) =
    PDNT
      (\(ri ** pi ** rcpd) =>
        (ri ** onidx pi ** oncontra pi pdfPNTwhiskerR_hole_onidx . rcpd))
      (\(ri ** pi ** rcpd), pcrd =>
        id)
      (\(ri ** pi ** rcpd), pcrd, qci =>
        oncovar pi pdfPNTwhiskerR_hole_oncovar qci)

export
pdfPNThcomp : {0 p, p', q, q' : PolyDifunc} ->
  PolyDiNT q q' ->
  PolyDiNT p p' ->
  PolyDiNT (pdfComp q p) (pdfComp q' p')
pdfPNThcomp {p} {p'} {q} {q'} beta alpha =
  pdfPNTvcomp
    (pdfPNTwhiskerL {q} {r=q'} beta p')
    (pdfPNTwhiskerR {p} {q=p'} alpha q)

  -}
