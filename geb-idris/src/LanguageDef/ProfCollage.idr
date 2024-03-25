module LanguageDef.ProfCollage

import Library.IdrisUtils
import Library.IdrisCategories

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

0 ipdfEqPos : {0 p, q : PolyDifunc} -> {0 x, y : Type} ->
  {ip : InterpPDF p x y} -> {iq : InterpPDF q x y} ->
  ip = iq -> ipdfPos ip ~=~ ipdfPos iq
ipdfEqPos {p} {q} {x} {y}
  {ip=(IPDF pi mxpd mpcy pmxy pm)} {iq=(IPDF qi mxqd mqcy qmxy qm)} eq =
    case eq of Refl => Refl

0 ipdfEqDom : {0 p, q : PolyDifunc} -> {0 x, y : Type} ->
  {ip : InterpPDF p x y} -> {iq : InterpPDF q x y} ->
  ip = iq -> ipdfDom ip ~=~ ipdfDom iq
ipdfEqDom {p} {q} {x} {y}
  {ip=(IPDF pi mxpd mpcy pmxy pm)} {iq=(IPDF qi mxqd mqcy qmxy qm)} eq =
    case eq of Refl => Refl

0 ipdfEqCod : {0 p, q : PolyDifunc} -> {0 x, y : Type} ->
  {ip : InterpPDF p x y} -> {iq : InterpPDF q x y} ->
  ip = iq -> ipdfCod ip ~=~ ipdfCod iq
ipdfEqCod {p} {q} {x} {y}
  {ip=(IPDF pi mxpd mpcy pmxy pm)} {iq=(IPDF qi mxqd mqcy qmxy qm)} eq =
    case eq of Refl => Refl

0 ipdfEqMorph : {0 p, q : PolyDifunc} -> {0 x, y : Type} ->
  {ip : InterpPDF p x y} -> {iq : InterpPDF q x y} ->
  ip = iq -> ipdfMorph ip ~=~ ipdfMorph iq
ipdfEqMorph {p} {q} {x} {y}
  {ip=(IPDF pi mxpd mpcy pmxy pm)} {iq=(IPDF qi mxqd mqcy qmxy qm)} eq =
    case eq of Refl => Refl

0 ipdfEqComm : {0 p, q : PolyDifunc} -> {0 x, y : Type} ->
  {ip : InterpPDF p x y} -> {iq : InterpPDF q x y} ->
  ip = iq -> ipdfComm ip ~=~ ipdfComm iq
ipdfEqComm {p} {q} {x} {y}
  {ip=(IPDF pi mxpd mpcy pmxy pm)} {iq=(IPDF qi mxqd mqcy qmxy qm)} eq =
    case eq of Refl => Refl

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
0 InterpPDFisPara : {0 p, q : PolyDifunc} -> (pdnt : PolyDiNT p q) ->
  (i0, i1 : Type) -> (i2 : i0 -> i1) ->
  (d0 : InterpPDF p i0 i0) -> (d1 : InterpPDF p i1 i1) ->
  (InterpPDFlmap p i1 i1 i0 i2 d1 = InterpPDFrmap p i0 i0 i1 i2 d0) ->
  (InterpPDFlmap q i1 i1 i0 i2 (InterpPDNT {p} {q} pdnt i1 d1) =
   InterpPDFrmap q i0 i0 i1 i2 (InterpPDNT {p} {q} pdnt i0 d0))
InterpPDFisPara {p=(PDF pp pd pc pm)} {q=(PDF qp qd qc qm)}
  (PDNT onidx ondom oncod ntcomm) i0 i1 i2
  (IPDF pi0 mi0pd mpci0 mi0i0 pcomm) (IPDF pi1 mi1pd mpci1 mi1i1 qcomm) cond =
    case ipdfEqPos cond of
      Refl => case ipdfEqDom cond of
        Refl => case ipdfEqCod cond of
          Refl => rewrite ipdfEqMorph cond in Refl

--------------------------------------------------------------------------------
---- Category of metalanguage difunctors with paranatural transformations ----
--------------------------------------------------------------------------------

export
pdNTid : (pdf : PolyDifunc) -> PolyDiNT pdf pdf
pdNTid pdf = PDNT id (\_ => id) (\_ => id) (\pi, fext => Refl)

export
pdNTvcomp : {0 r, q, p : PolyDifunc} -> PolyDiNT q r -> PolyDiNT p q ->
  PolyDiNT p r
pdNTvcomp {r=(PDF rp rd rc rm)} {q=(PDF qp qd qc qm)} {p=(PDF pp pd pc pm)}
  (PDNT oniqr ondomqr oncodqr qrcomm) (PDNT onipq ondompq oncodpq pqcomm) =
    PDNT
      (oniqr . onipq)
      (\pi, pdi => ondomqr (onipq pi) $ ondompq pi pdi)
      (\pi, rci => oncodpq pi $ oncodqr (onipq pi) rci)
      (\pi, fext =>
        trans
          (funExt $ \ex => cong (oncodpq pi) $ fcong (qrcomm (onipq pi) fext))
          (pqcomm pi fext))

--------------------------------------------------------------------
---- Two-categorical structure of polydinatural transformations ----
--------------------------------------------------------------------

-- The polydinatural transformations of difunctors form a two-category:
-- polydinatural transformations have horizontal composition and whiskering.

export
pdNTwhiskerL : {0 q, r : PolyDifunc} -> PolyDiNT q r -> (p : PolyDifunc) ->
  PolyDiNT (pdfComp q p) (pdfComp r p)
pdNTwhiskerL {q=(PDF qp qd qc qm)} {r=(PDF rp rd rc rm)}
  (PDNT oni ond onc comm) (PDF pp pd pc pm) =
    PDNT
      (\(qi ** pi ** qcpd) => (oni qi ** pi ** qcpd . onc qi))
      (\(qi ** pi ** qcpd) => ond qi)
      (\(qi ** pi ** qcpd) => id)
      (\(qi ** pi ** qcpd), fext =>
        funExt $ \ex => cong (pm pi) $ cong qcpd $ fcong (comm qi fext))

export
pdNTwhiskerR : {0 p, q : PolyDifunc} -> PolyDiNT p q -> (r : PolyDifunc) ->
  PolyDiNT (pdfComp r p) (pdfComp r q)
pdNTwhiskerR {p=(PDF pp pd pc pm)} {q=(PDF qp qd qc qm)}
  (PDNT oni ond onc comm) (PDF rp rd rc rm) =
    PDNT
      (\(ri ** pi ** rcpd) => (ri ** oni pi ** ond pi . rcpd))
      (\(ri ** pi ** rcpd) => id)
      (\(ri ** pi ** rcpd) => onc pi)
      (\(ri ** pi ** rcpd), fext =>
        funExt $ \ex => fcong (comm pi fext))

export
pdNThcomp : {0 p, q' : PolyDifunc} -> {p', q : PolyDifunc} ->
  PolyDiNT q q' -> PolyDiNT p p' -> PolyDiNT (pdfComp q p) (pdfComp q' p')
pdNThcomp {p} {p'} {q} {q'} beta alpha =
  pdNTvcomp (pdNTwhiskerL {q} {r=q'} beta p') (pdNTwhiskerR {p} {q=p'} alpha q)
