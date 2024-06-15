module LanguageDef.PolyDifunc

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.DisliceCat
import public LanguageDef.DislicePolyCat
import public LanguageDef.IntECofamCat

----------------------------------
----------------------------------
---- Polynomial apply functor ----
----------------------------------
----------------------------------

public export
PolyPolyCat : IntCatSig -> IntCatSig
PolyPolyCat cat = ECofamCatSig (ECofamCatSig cat)

public export
PolyPolyObj : IntCatSig -> Type
PolyPolyObj cat = icObj (PolyPolyCat cat)

public export
PolyPolyMor : (cat : IntCatSig) -> IntMorSig (PolyPolyObj cat)
PolyPolyMor cat = icMor (PolyPolyCat cat)

public export
PolyAppFunc : (cat : IntCatSig) -> icObj cat -> (PolyPolyObj cat)
PolyAppFunc cat a =
  ((b : icObj cat ** icMor cat b a) ** \ai => (() ** \() => fst ai))

public export
PolyAppToInterp : (cat : IntCatSig) ->
  (a : icObj cat) -> (p : IntECofamObj $ icObj cat) ->
  InterpECofamCopreshfOMap
    (IntECofamObj $ icObj cat)
    (IntECofamMor $ icMor cat)
    (PolyAppFunc cat a) p ->
  InterpECofamCopreshfOMap (icObj cat) (icMor cat) p a
PolyAppToInterp cat a (pos ** dir) (appPos ** onPos ** onDir) =
  (onPos () **
   icComp cat (dir $ onPos ()) (fst appPos) a (snd appPos) (onDir ()))

public export
PolyAppFromInterp : (cat : IntCatSig) ->
  (a : icObj cat) -> (p : IntECofamObj $ icObj cat) ->
  InterpECofamCopreshfOMap (icObj cat) (icMor cat) p a ->
  InterpECofamCopreshfOMap
    (IntECofamObj $ icObj cat)
    (IntECofamMor $ icMor cat)
    (PolyAppFunc cat a) p
PolyAppFromInterp cat a (pos ** dir) (i ** dm) =
  ((dir i ** dm) ** (const i ** \() => icId cat $ dir i))

----------------------------------
----------------------------------
---- Polynomial double-Yoneda ----
----------------------------------
----------------------------------

public export
ECofamType : IntCatSig
ECofamType = ECofamCatSig TypeCat

public export
ECofamPolyType : IntCatSig
ECofamPolyType = ECofamCatSig ECofamType

public export
record PolyDoubleYo (a, b : Type) where
  constructor MkPolyDoubleYo
  PolyDoubleYoEmbed :
    PolyPolyMor TypeCat (PolyAppFunc TypeCat a) (PolyAppFunc TypeCat b)

public export
PolyDoubleYoDimap : IntEndoDimapSig Type TypeMor PolyDoubleYo
PolyDoubleYoDimap s t a b mas mtb (MkPolyDoubleYo (onpos ** ondir)) =
  MkPolyDoubleYo
    (\(i ** mia) =>
      (fst (onpos (i ** mas . mia)) ** mtb . snd (onpos (i ** mas . mia))) **
     \(i ** mia) =>
      (\() => () **
       \(), ei =>
        snd (ondir (i ** mas . mia)) ()
          (rewrite unitUnique (fst (ondir (i ** mas . mia)) ()) () in ei)))

public export
toDoubleYo : ProfNT HomProf PolyDoubleYo
toDoubleYo mab =
  MkPolyDoubleYo
    (\(i ** mia) => (i ** mab . mia) ** \(i ** mia) => (\() => () ** \() => id))

public export
fromDoubleYo : ProfNT PolyDoubleYo HomProf
fromDoubleYo (MkPolyDoubleYo (onpos ** ondir)) ea =
  snd (onpos (a ** id))
  $ snd (ondir (a ** id)) ()
  $ rewrite unitUnique (fst (ondir (a ** id)) ()) () in ea

----------------------------------------------------------------------------
----------------------------------------------------------------------------
---- Dependent-type-style poly-difunctor ("twisted polynomial functor") ----
----------------------------------------------------------------------------
----------------------------------------------------------------------------

public export
TwistArrAr : Type
TwistArrAr = IntECofamObj Type

public export
twarCod : TwistArrAr -> Type
twarCod = DPair.fst

public export
twarDom : (twar : TwistArrAr) -> SliceObj (twarCod twar)
twarDom = DPair.snd

public export
TwistArrMor : IntMorSig TwistArrAr
TwistArrMor = IntECofamMor {c=TypeObj} TypeMor

public export
TwistPolyFunc : Type
TwistPolyFunc = IntEFamObj TwistArrAr

public export
tpfPos : TwistPolyFunc -> Type
tpfPos = DPair.fst

public export
tpfAr : (tpf : TwistPolyFunc) -> tpfPos tpf -> TwistArrAr
tpfAr = DPair.snd

public export
tpfCod : (tpf : TwistPolyFunc) -> SliceObj (tpfPos tpf)
tpfCod tpf = twarCod . tpfAr tpf

public export
tpfDom : (tpf : TwistPolyFunc) -> (i : tpfPos tpf) -> SliceObj (tpfCod tpf i)
tpfDom tpf i = twarDom (tpfAr tpf i)

public export
InterpTPF : TwistPolyFunc -> TwistArrAr -> Type
InterpTPF = InterpEFamPreshfOMap TwistArrAr TwistArrMor

public export
itpfPos : {tpf : TwistPolyFunc} -> {twar : TwistArrAr} ->
  InterpTPF tpf twar -> tpfPos tpf
itpfPos {tpf} {twar} = DPair.fst

public export
itpfDir : {tpf : TwistPolyFunc} -> {twar : TwistArrAr} ->
  (itpf : InterpTPF tpf twar) ->
  TwistArrMor twar (tpfAr tpf $ itpfPos {tpf} {twar} itpf)
itpfDir {tpf} {twar} itpf = DPair.snd itpf

public export
itpfBC : {tpf : TwistPolyFunc} -> {twar : TwistArrAr} ->
  (itpf : InterpTPF tpf twar) ->
  twarCod twar -> tpfCod tpf (itpfPos {tpf} {twar} itpf)
itpfBC {tpf} {twar} itpf = DPair.fst (itpfDir itpf)

public export
itpfSM : {tpf : TwistPolyFunc} -> {twar : TwistArrAr} ->
  (itpf : InterpTPF tpf twar) ->
  SliceMorphism {a=(twarCod twar)}
    (BaseChangeF
      (itpfBC {tpf} {twar} itpf)
      (tpfDom tpf $ itpfPos {tpf} {twar} itpf))
    (twarDom twar)
itpfSM {tpf} {twar} itpf = DPair.snd (itpfDir itpf)

public export
TwistNT : IntMorSig TwistPolyFunc
TwistNT = IntEFamMor {c=TwistArrAr} TwistArrMor

public export
twntOnPos : {p, q : TwistPolyFunc} -> TwistNT p q -> tpfPos p -> tpfPos q
twntOnPos {p} {q} = DPair.fst

public export
twntOnDir : {p, q : TwistPolyFunc} -> (twnt : TwistNT p q) ->
  (i : tpfPos p) -> TwistArrMor (tpfAr p i) (tpfAr q (twntOnPos {p} {q} twnt i))
twntOnDir {p} {q} = DPair.snd

public export
twntOnBase : {p, q : TwistPolyFunc} -> (twnt : TwistNT p q) ->
  SliceMorphism {a=(tpfPos p)}
    (tpfCod p)
    (BaseChangeF (twntOnPos {p} {q} twnt) (tpfCod q))
twntOnBase {p} {q} twnt i = DPair.fst (twntOnDir twnt i)

public export
twntOnTot : {p, q : TwistPolyFunc} -> (twnt : TwistNT p q) ->
  (i : tpfPos p) ->
    SliceMorphism {a=(tpfCod p i)}
      (BaseChangeF
        (twntOnBase {p} {q} twnt i)
        (tpfDom q (twntOnPos {p} {q} twnt i)))
      (tpfDom p i)
twntOnTot {p} {q} twnt i = DPair.snd (twntOnDir twnt i)

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
-- interpretation below, we can view these morphisms as the heteromorphisms
-- of a difunctor on `Type`, and also as the objects of the twisted-arrow
-- category on `Type`.  (Thus far they could also be objects of the arrow
-- category, but the interpretation below uses twisted-arrow morphisms,
-- not arrow morphisms.)
public export
record PolyDifunc where
  constructor PDF
  pdfPos : Type
  pdfCobase : SliceObj pdfPos
  pdfBase : SliceObj pdfPos
  pdfProj : SliceMorphism {a=pdfPos} pdfCobase pdfBase

-- The interpretation of a polydifunctor takes an object of the
-- twisted arrow category (of `Type`) and, as with polynomial
-- functors on other categories, comprises a choice of one of the
-- directions of the difunctor together with a (twisted-arrow)
-- morphism from that direction to the (twisted-arrow) object
-- that the functor is being applied to.
--
-- The difference between this and a general difunctor is the twisted-arrow
-- morphism:  without that, this would just determine a general profunctor
-- by its collage.  The twisted-arrow morphism constrains the profunctor
-- so that it only contains elements that can be "diagonalized" by the
-- morphism.
public export
record InterpPDF (pdf : PolyDifunc) (x, y : Type) (m : x -> y) where
  constructor IPDF
  ipdfPos : pdfPos pdf
  ipdfContraMor : x -> pdfCobase pdf ipdfPos
  ipdfCovarMor : pdfBase pdf ipdfPos -> y
  0 ipdfComm :
    FunExtEq (ipdfCovarMor . pdfProj pdf ipdfPos . ipdfContraMor) m

public export
IPDFc : {pdf : PolyDifunc} -> {x, y : Type} ->
  (i : pdfPos pdf) ->
  (cnm : x -> pdfCobase pdf i) -> (cvm : pdfBase pdf i -> y) ->
  InterpPDF pdf x y (cvm . pdfProj pdf i . cnm)
IPDFc {pdf} {x} {y} i cnm cvm = IPDF i cnm cvm $ \fext => Refl

export
0 ipdfEqPos : {0 p, q : PolyDifunc} -> {0 x, y : Type} -> {0 m : x -> y} ->
  {ip : InterpPDF p x y m} -> {iq : InterpPDF q x y m} ->
  ip ~=~ iq -> ipdfPos ip ~=~ ipdfPos iq
ipdfEqPos {p} {q} {x} {y} {m}
  {ip=(IPDF pi mxpd mpcy pcomm)} {iq=(IPDF qi mxqd mqcy qcomm)} eq =
    case eq of Refl => Refl

export
0 ipdfEqDom : {0 p, q : PolyDifunc} -> {0 x, y : Type} -> {0 m : x -> y} ->
  {ip : InterpPDF p x y m} -> {iq : InterpPDF q x y m} ->
  ip ~=~ iq -> ipdfContraMor ip ~=~ ipdfContraMor iq
ipdfEqDom {p} {q} {x} {y} {m}
  {ip=(IPDF pi mxpd mpcy pcomm)} {iq=(IPDF qi mxqd mqcy qcomm)} eq =
    case eq of Refl => Refl

export
0 ipdfEqCod : {0 p, q : PolyDifunc} -> {0 x, y : Type} -> {0 m : x -> y} ->
  {ip : InterpPDF p x y m} -> {iq : InterpPDF q x y m} ->
  ip ~=~ iq -> ipdfCovarMor ip ~=~ ipdfCovarMor iq
ipdfEqCod {p} {q} {x} {y} {m}
  {ip=(IPDF pi mxpd mpcy pcomm)} {iq=(IPDF qi mxqd mqcy qcomm)} eq =
    case eq of Refl => Refl

export
0 ipdfEqComm : {0 p, q : PolyDifunc} -> {0 x, y : Type} -> {0 m : x -> y} ->
  {ip : InterpPDF p x y m} -> {iq : InterpPDF q x y m} ->
  ip ~=~ iq -> ipdfComm ip ~=~ ipdfComm iq
ipdfEqComm {p} {q} {x} {y} {m}
  {ip=(IPDF pi mxpd mpcy pcomm)} {iq=(IPDF qi mxqd mqcy qcomm)} eq =
    case eq of Refl => Refl

export
0 ipdfUip : FunExt ->
  {0 p : PolyDifunc} ->
  {0 x, y : Type} -> {0 m : x -> y} ->
  {ip, iq : InterpPDF p x y m} ->
  ipdfPos ip ~=~ ipdfPos iq ->
  ipdfContraMor ip ~=~ ipdfContraMor iq ->
  ipdfCovarMor ip ~=~ ipdfCovarMor iq ->
  ip = iq
ipdfUip fext {p=(PDF pp pd pc pm)} {x} {y} {m}
  {ip=(IPDF pi mxpd mpcy pcomm)} {iq=(IPDF _ _ _ qcomm)}
    Refl Refl Refl =
      let eqComm : (pcomm = qcomm) = (funExt $ \fext' => uip) in
      case eqComm of Refl => Refl

public export
InterpPDFlmap : (pdf : PolyDifunc) ->
  (0 s, t, a : Type) -> (mst : s -> t) -> (mas : a -> s) ->
  InterpPDF pdf s t mst -> InterpPDF pdf a t (mst . mas)
InterpPDFlmap (PDF pos dom cod proj) s t a mst mas (IPDF i msi mit comm) =
  IPDF i (msi . mas) mit
    $ \fext => funExt $ \ea => fcong {x=(mas ea)} (comm fext)

public export
InterpPDFrmap : (pdf : PolyDifunc) ->
  (0 s, t, b : Type) -> (mst : s -> t) -> (mtb : t -> b) ->
  InterpPDF pdf s t mst -> InterpPDF pdf s b (mtb . mst)
InterpPDFrmap (PDF pos dom cod proj) s t b mst mtb (IPDF i msi mit comm) =
  IPDF i msi (mtb . mit)
    $ \fext => funExt $ \es => cong mtb $ fcong {x=es} (comm fext)

public export
InterpPDFdimap : (pdf : PolyDifunc) ->
  (0 s, t, a, b : Type) -> (mst : s -> t) -> (mas : a -> s) -> (mtb : t -> b) ->
  InterpPDF pdf s t mst -> InterpPDF pdf a b (mtb . mst . mas)
InterpPDFdimap pdf s t a b mst mas mtb =
  InterpPDFlmap pdf s b a (mtb . mst) mas . InterpPDFrmap pdf s t b mst mtb

----------------------------------
---- Monoid of polydifunctors ----
----------------------------------

-- Polydifunctors form a monoid -- a one-object category, with
-- the polydifunctors as morphisms -- whose identity is the hom-profunctor,
-- and whose composition resembles that of profunctors, but with the
-- additional morphism (since the objects are twisted arrows rather than
-- just objects of `op(Type) x Type`) to compose.

-- We represent the hom-profunctor, which is the identity of the monoid of
-- polydifunctors, with one position per morphism of `Type`.

public export
PdfHomProfId : PolyDifunc
PdfHomProfId =
  PDF
    (dom : Type ** cod : Type ** dom -> cod)
    (\i => fst i)
    (\i => fst $ snd i)
    (\i => snd $ snd i)

export
InterpToIdPDF : (x, y : Type) -> (m : x -> y) -> InterpPDF PdfHomProfId x y m
InterpToIdPDF x y m = IPDF (x ** y ** m) id id $ \fext => Refl

export
InterpFromIdPDF : (x, y : Type) -> (m : x -> y) ->
  InterpPDF PdfHomProfId x y m -> x -> y
InterpFromIdPDF x y mxy (IPDF (i ** j ** mij) mxi mjy comm) =
  -- There are two ways of getting from `x` to `y` -- `mxy` and
  -- `mjy . mij . mxi`. But `comm` shows them to be equal.
  -- We make that explicit here to make sure, and to document, that
  -- `mjy`, `mij`, and `mxi` are not "unused", but rather are an
  -- alternative to the `mxy` which we do use.
  let 0 eqm : (FunExtEq (mjy . mij . mxi) mxy) = comm in
  mxy

-- The arena form of polydifunctors is closed under composition.
public export
pdfComp : PolyDifunc -> PolyDifunc -> PolyDifunc
pdfComp (PDF qp qd qc qm) (PDF pp pd pc pm) =
  PDF
    (qi : qp ** pi : pp ** qc qi -> pd pi)
    (\(qi ** pi ** qcpd) => qd qi)
    (\(qi ** pi ** qcpd) => pc pi)
    (\(qi ** pi ** qcpd), qdi => pm pi $ qcpd $ qm qi qdi)

export
PDFcomposeInterpToInterpCompose :
  (q, p : PolyDifunc) -> (x, z : Type) -> (mxz : x -> z) ->
  TwArrCoprCompose (InterpPDF q) (InterpPDF p) x z mxz ->
  InterpPDF (pdfComp q p) x z mxz
PDFcomposeInterpToInterpCompose (PDF qp qd qc qm) (PDF pp pd pc pm) x z mxz
  (y **
   (mxy, myz) **
   (comm, IPDF qi mxqd mqcy qcomm, IPDF pi mypd mpcz pcomm)) =
    IPDF
      (qi ** pi ** mypd . mqcy)
      mxqd
      mpcz
      (\fext => funExt $ \ex =>
        trans
          (rewrite fcong {x=ex} (qcomm fext) in fcong {x=(mxy ex)} (pcomm fext))
          (fcong {x=ex} (comm fext)))

0 PDFinterpComposeToComposeInterp :
  (q, p : PolyDifunc) -> (x, z : Type) -> (mxz : x -> z) ->
  InterpPDF (pdfComp q p) x z mxz ->
  TwArrCoprCompose (InterpPDF q) (InterpPDF p) x z mxz
PDFinterpComposeToComposeInterp (PDF qp qd qc qm) (PDF pp pd pc pm) x z mxz
  (IPDF (qi ** pi ** mqcpd) mxqd mpcz comm) =
    (pd pi **
     (mqcpd . qm qi . mxqd, mpcz . pm pi) **
     (comm,
      IPDF qi mxqd mqcpd (\fext => Refl),
      IPDF pi Prelude.id mpcz (\fext => Refl)))

---------------------------------------
---- Polynomial/Dirichlet functors ----
---------------------------------------

-- Twisted polynomials subsume both polynomial and Dirichlet functors.

export
PdfFromPoly : PolyFunc -> PolyDifunc
PdfFromPoly p = PDF (pfPos p) (\_ => Void) (pfDir {p}) (\i, v => void v)

export
InterpPdfFromPoly : (p : PolyFunc) -> (y : Type) ->
  InterpPolyFunc p y -> InterpPDF (PdfFromPoly p) Void y (\v => void v)
InterpPdfFromPoly (pos ** dir) y (i ** dm) =
  IPDF i (\v => void v) dm $ \fext => funExt $ \v => void v

export
InterpPdfToPoly : (p : PolyFunc) -> (y : Type) ->
  InterpPDF (PdfFromPoly p) Void y (\v => void v) -> InterpPolyFunc p y
InterpPdfToPoly (pos ** dir) y (IPDF i mx my comm) = (i ** my)

export
PdfFromDirich : PolyFunc -> PolyDifunc
PdfFromDirich p = PDF (pfPos p) (pfDir {p}) (\_ => Unit) (\_, _ => ())

export
InterpPdfFromDirich : (p : PolyFunc) -> (x : Type) ->
  InterpDirichFunc p x -> InterpPDF (PdfFromDirich p) x Unit (\_ => ())
InterpPdfFromDirich (pos ** dir) x (i ** dm) =
  IPDF i dm (\_ => ()) $ \fext => funExt $ \_ => Refl

export
InterpPdfToDirich : (p : PolyFunc) -> (x : Type) ->
  InterpPDF (PdfFromDirich p) x Unit (\_ => ()) -> InterpDirichFunc p x
InterpPdfToDirich (pos ** dir) x (IPDF i mx my comm) = (i ** mx)

-----------------------------------------------------------------------
---- Polydinatural transformations between metalanguage difunctors ----
-----------------------------------------------------------------------

-- A polydinatural transformation comprises an on-positions function from
-- the positions (collage objects) of the domain polydifunctor to those of
-- the codomain polydifunctor, and for each position, a twisted-arrow
-- morphism between the collage objects from the one at the output of the
-- on-positions function in the codomain polydifunctor to the one at the
-- input of the on-positions in the domain polydifunctor.
public export
record PolyDiNT (p, q : PolyDifunc) where
  constructor PDNT
  pdntOnPos : pdfPos p -> pdfPos q
  pdntOnBase :
    (i : pdfPos p) -> pdfBase q (pdntOnPos i) -> pdfBase p i
  pdntOnCobase :
    (i : pdfPos p) ->
      CSliceMorphism {c=(pdfBase p i)}
        (pdfCobase p i ** pdfProj p i)
        (pdfCobase q (pdntOnPos i) ** pdntOnBase i . pdfProj q (pdntOnPos i))

export
InterpPDNTnat : {0 p, q : PolyDifunc} -> PolyDiNT p q ->
  (x, y : Type) -> (m : x -> y) -> InterpPDF p x y m -> InterpPDF q x y m
InterpPDNTnat {p=(PDF pp pd pc pm)} {q=(PDF qp qd qc qm)}
  (PDNT oni onb onc) x y m (IPDF pi mxpd mpcx pcomm) =
    IPDF
      (oni pi)
      (fst0 (onc pi) . mxpd)
      (mpcx . onb pi)
      (\fext => funExt $ \ex =>
        rewrite sym $ snd0 (onc pi) (mxpd ex) in fcong {x=ex} $ pcomm fext)

export
InterpPDNT : {0 p, q : PolyDifunc} -> PolyDiNT p q ->
  (x : Type) -> InterpPDF p x x Prelude.id -> InterpPDF q x x Prelude.id
InterpPDNT {p} {q} pdnt x = InterpPDNTnat {p} {q} pdnt x x Prelude.id

export
0 InterpPDFisPara : FunExt ->
  {0 p, q : PolyDifunc} -> (pdnt : PolyDiNT p q) ->
  (i0, i1 : Type) -> (i2 : i0 -> i1) ->
  (d0 : InterpPDF p i0 i0 Prelude.id) -> (d1 : InterpPDF p i1 i1 Prelude.id) ->
  (InterpPDFlmap p i1 i1 i0 Prelude.id i2 d1 ~=~
   InterpPDFrmap p i0 i0 i1 Prelude.id i2 d0) ->
  (InterpPDFlmap q i1 i1 i0 Prelude.id i2 (InterpPDNT {p} {q} pdnt i1 d1) ~=~
   InterpPDFrmap q i0 i0 i1 Prelude.id i2 (InterpPDNT {p} {q} pdnt i0 d0))
InterpPDFisPara fext {p=p@(PDF pp pd pc pm)} {q=q@(PDF qp qd qc qm)}
  pdnt@(PDNT onidx onb onc) i0 i1 i2
  ip@(IPDF pi0 mi0pd mpci0 pcomm) iq@(IPDF pi1 mi1pd mpci1 qcomm) cond =
    case ipdfEqPos cond of
      Refl => case ipdfEqDom cond of
        Refl => case ipdfEqCod cond of
          Refl =>
            ipdfUip fext Refl Refl Refl

--------------------------------------------------------------------------------
---- Category of metalanguage difunctors with paranatural transformations ----
--------------------------------------------------------------------------------

export
pdNTid : (pdf : PolyDifunc) -> PolyDiNT pdf pdf
pdNTid pdf =
  PDNT id (\_ => id) (\i => CSliceId (pdfCobase pdf i ** pdfProj pdf i))

export
pdNTvcomp : {0 r, q, p : PolyDifunc} -> PolyDiNT q r -> PolyDiNT p q ->
  PolyDiNT p r
pdNTvcomp {r=(PDF rp rd rc rm)} {q=(PDF qp qd qc qm)} {p=(PDF pp pd pc pm)}
  (PDNT oniqr onbqr oncqr) (PDNT onipq onbpq oncpq) =
    PDNT
      (oniqr . onipq)
      (\pi => onbpq pi . onbqr (onipq pi))
      (\pi =>
        Element0
          (fst0 (oncqr $ onipq pi) . fst0 (oncpq pi))
          (\pdi =>
            rewrite snd0 (oncpq pi) pdi in
            cong (onbpq pi) $ snd0 (oncqr $ onipq pi) (fst0 (oncpq pi) pdi)))

--------------------------------------------------------------------
---- Two-categorical structure of polydinatural transformations ----
--------------------------------------------------------------------

-- The polydinatural transformations of difunctors form a two-category:
-- polydinatural transformations have horizontal composition and whiskering.

export
pdNTwhiskerL : {0 q, r : PolyDifunc} -> PolyDiNT q r -> (p : PolyDifunc) ->
  PolyDiNT (pdfComp q p) (pdfComp r p)
pdNTwhiskerL {q=(PDF qp qd qc qm)} {r=(PDF rp rd rc rm)}
  (PDNT oni onb onc) (PDF pp pd pc pm) =
    PDNT
      (\(qi ** pi ** qcpd) => (oni qi ** pi ** qcpd . onb qi))
      (\(qi ** pi ** qcpd) => id)
      (\(qi ** pi ** qcpd) =>
        Element0
          (fst0 $ onc qi)
          (\qdi => cong (pm pi) $ cong qcpd $ snd0 (onc qi) qdi))

export
pdNTwhiskerR : {0 p, q : PolyDifunc} -> PolyDiNT p q -> (r : PolyDifunc) ->
  PolyDiNT (pdfComp r p) (pdfComp r q)
pdNTwhiskerR {p=(PDF pp pd pc pm)} {q=(PDF qp qd qc qm)}
  (PDNT oni onb onc) (PDF rp rd rc rm) =
    PDNT
      (\(ri ** pi ** rcpd) => (ri ** oni pi ** fst0 (onc pi) . rcpd))
      (\(ri ** pi ** rcpd) => onb pi)
      (\(ri ** pi ** rcpd) =>
        Element0 id $ \rdi => snd0 (onc pi) (rcpd (rm ri rdi)))

export
pdNThcomp : {0 p, q' : PolyDifunc} -> {p', q : PolyDifunc} ->
  PolyDiNT q q' -> PolyDiNT p p' -> PolyDiNT (pdfComp q p) (pdfComp q' p')
pdNThcomp {p} {p'} {q} {q'} beta alpha =
  pdNTvcomp (pdNTwhiskerL {q} {r=q'} beta p') (pdNTwhiskerR {p} {q=p'} alpha q)
