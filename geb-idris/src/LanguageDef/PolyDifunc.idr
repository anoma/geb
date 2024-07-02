module LanguageDef.PolyDifunc

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.DisliceCat
import public LanguageDef.DislicePolyCat
import public LanguageDef.IntECofamCat
import public LanguageDef.GenPolyFunc
import public LanguageDef.IntDisheafCat

%default total
%hide Library.IdrisCategories.BaseChangeF
%hide Prelude.Ops.infixl.(|>)

----------------------------------------------
----------------------------------------------
---- Universal families as twisted arrows ----
----------------------------------------------
----------------------------------------------

public export
TwistArrArType : Type
TwistArrArType = TwistArrAr TypeCat

public export
TwistArrMorType : IntMorSig TwistArrArType
TwistArrMorType = TwistArrMor TypeCat

public export
twarDomType : TwistArrArType -> Type
twarDomType = twarDom {cat=TypeCat}

public export
twarCodType : (twar : TwistArrArType) -> SliceObj (twarDomType twar)
twarCodType = twarCod {cat=TypeCat}

public export
TwistPolyFuncType : Type
TwistPolyFuncType = TwistPolyFunc TypeCat

public export
tpfPosType : TwistPolyFuncType -> Type
tpfPosType = tpfPos {cat=TypeCat}

public export
tpfArType : (tpf : TwistPolyFuncType) -> tpfPosType tpf -> TwistArrArType
tpfArType = tpfAr {cat=TypeCat}

public export
tpfDomType : (tpf : TwistPolyFuncType) -> SliceObj (tpfPosType tpf)
tpfDomType = tpfDom {cat=TypeCat}

public export
tpfCodType : (tpf : TwistPolyFuncType) ->
  (i : tpfPosType tpf) -> SliceObj (tpfDomType tpf i)
tpfCodType = tpfCod {cat=TypeCat}

public export
TwistNTType : IntMorSig TwistPolyFuncType
TwistNTType = TwistNT TypeCat

public export
InterpTPFType : TwistPolyFuncType -> TwistArrArType -> Type
InterpTPFType = InterpTPF {cat=TypeCat}

public export
itpfOnCod : {tpf : TwistPolyFuncType} -> {twar : TwistArrArType} ->
  (itpf : InterpTPFType tpf twar) ->
  SliceMorphism {a=(twarDomType twar)}
    (BaseChangeF
      (itpfOnDom {cat=TypeCat} {tpf} {twar} itpf)
      (tpfCodType tpf $ itpfPos {cat=TypeCat} {tpf} {twar} itpf))
    (twarCodType twar)
itpfOnCod {tpf} {twar} itpf = DPair.snd (itpfDir {cat=TypeCat} itpf)

public export
twntOnCovar : {p, q : TwistPolyFuncType} ->
  (twnt : TwistNTType p q) ->
  (i : tpfPosType p) ->
    SliceMorphism {a=(tpfDomType p i)}
      (BaseChangeF
        (twntOnContra {cat=TypeCat} {p} {q} twnt i)
          (tpfCodType q $ twntOnPos {cat=TypeCat} {p} {q} twnt i))
      (tpfCodType p i)
twntOnCovar {p} {q} twnt i = DPair.snd (twntOnDir {cat=TypeCat} twnt i)

--------------------------------------------------------------------------
--------------------------------------------------------------------------
---- Metalanguage twisted-arrow ("di") arenas and polynomial functors ----
--------------------------------------------------------------------------
--------------------------------------------------------------------------

public export
record MLDiArena where
  constructor MLDiAr
  mdaAr : MLArena
  mdaContra :
    Pi {a=(pfPos mdaAr)} (SliceObj . pfDir {p=mdaAr})
  mdaAssign :
    Pi {a=(pfPos mdaAr)} (\i => Pi {a=(pfDir {p=mdaAr} i)} $ mdaContra i)

public export
mdaPos : MLDiArena -> Type
mdaPos = pfPos . mdaAr

public export
mdaCovar : (mda : MLDiArena) -> SliceObj (mdaPos mda)
mdaCovar mda = pfDir {p=(mdaAr mda)}

public export
record InterpMDA (mda : MLDiArena) (covar : Type) (contra : SliceObj covar)
    where
  constructor IMDA
  imdaPos :
    mdaPos mda
  imdaCovar :
    covar -> mdaCovar mda imdaPos
  imdaContra :
    SliceMorphism {a=covar} (mdaContra mda imdaPos . imdaCovar) contra

public export
imdaAssign : {mda : MLDiArena} -> {covar : Type} -> {contra : SliceObj covar} ->
  (imda : InterpMDA mda covar contra) ->
  Pi {a=covar} contra
imdaAssign {mda} {covar} {contra} imda i =
  imdaContra imda i $ mdaAssign mda (imdaPos imda) (imdaCovar imda i)

public export
record MDACatElemObj (mda : MLDiArena) where
  constructor MDACEO
  mdaElPos :
    mdaPos mda
  mdaElCovar :
    SliceObj (mdaCovar mda mdaElPos)
  mdaElContra :
    SliceObj (Sigma {a=(mdaCovar mda mdaElPos)} mdaElCovar)

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
--
-- Note that when `y` is `x` and `m` is `id`, then this amounts to
-- a factorization of the identity on `x` through `pdfCobase` and
-- `pdfBase` via three morphisms.  If furthermore we choose a position
-- where `pdfCobase` is `pdfBase` and `pdfProj` is `id`, then this
-- interpretation becomes a factorization of the identity on `x` through
-- `pdfBase`, the type of directions at that position.  Such a factorization
-- is an epi (surjective) assignment of directions to `x`, together with
-- a mono (injective) assignment from `x` to the directions which effectively
-- constitutes a proof that `x` -- the type of variables -- contains no
-- "unused variables".
public export
record InterpPDF (pdf : PolyDifunc) (x, y : Type) (m : x -> y) where
  constructor IPDF
  ipdfPos : pdfPos pdf
  ipdfContraMor : x -> pdfCobase pdf ipdfPos
  ipdfCovarMor : pdfBase pdf ipdfPos -> y
  0 ipdfComm :
    FunExtEq (ipdfCovarMor . pdfProj pdf ipdfPos . ipdfContraMor) m

public export
InterpPDFdiag : (pdf : PolyDifunc) -> Type -> Type
InterpPDFdiag pdf x = InterpPDF pdf x x (Prelude.id {a=x})

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
  -- Per position, this is a twisted-arrow morphism from `q` to `p`.
  pdntOnBase :
    (i : pdfPos p) -> pdfBase q (pdntOnPos i) -> pdfBase p i
  pdntOnCobase :
    (i : pdfPos p) -> pdfCobase p i -> pdfCobase q (pdntOnPos i)
  pdntComm :
    (i : pdfPos p) ->
      FunExtEq
        (pdntOnBase i . pdfProj q (pdntOnPos i) . pdntOnCobase i)
        (pdfProj p i)

export
InterpPDNTnat : {0 p, q : PolyDifunc} -> PolyDiNT p q ->
  (x, y : Type) -> (m : x -> y) -> InterpPDF p x y m -> InterpPDF q x y m
InterpPDNTnat {p=(PDF pp pd pc pm)} {q=(PDF qp qd qc qm)}
  (PDNT oni onb onc ntcomm) x y m (IPDF pi mxpd mpcx pcomm) =
    IPDF
      (oni pi)
      (onc pi . mxpd)
      (mpcx . onb pi)
      (\fext => funExt $ \ex =>
        rewrite fcong {x=(mxpd ex)} $ ntcomm pi fext in
        fcong {x=ex} $ pcomm fext)

export
InterpPDNT : {0 p, q : PolyDifunc} -> PolyDiNT p q ->
  (x : Type) -> InterpPDFdiag p x -> InterpPDFdiag q x
InterpPDNT {p} {q} pdnt x = InterpPDNTnat {p} {q} pdnt x x Prelude.id

export
0 InterpPDFisPara : FunExt ->
  {0 p, q : PolyDifunc} -> (pdnt : PolyDiNT p q) ->
  (i0, i1 : Type) -> (i2 : i0 -> i1) ->
  (d0 : InterpPDFdiag p i0) -> (d1 : InterpPDFdiag p i1) ->
  (InterpPDFlmap p i1 i1 i0 Prelude.id i2 d1 ~=~
   InterpPDFrmap p i0 i0 i1 Prelude.id i2 d0) ->
  (InterpPDFlmap q i1 i1 i0 Prelude.id i2 (InterpPDNT {p} {q} pdnt i1 d1) ~=~
   InterpPDFrmap q i0 i0 i1 Prelude.id i2 (InterpPDNT {p} {q} pdnt i0 d0))
InterpPDFisPara fext {p=p@(PDF pp pd pc pm)} {q=q@(PDF qp qd qc qm)}
  pdnt@(PDNT onidx onb onc ntcomm) i0 i1 i2
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
  PDNT id (\_ => id) (\i => id) $ \i, fext => Refl

export
pdNTvcomp : {0 r, q, p : PolyDifunc} -> PolyDiNT q r -> PolyDiNT p q ->
  PolyDiNT p r
pdNTvcomp {r=(PDF rp rd rc rm)} {q=(PDF qp qd qc qm)} {p=(PDF pp pd pc pm)}
  (PDNT oniqr onbqr oncqr qrcomm) (PDNT onipq onbpq oncpq pqcomm) =
    PDNT
      (oniqr . onipq)
      (\pi => onbpq pi . onbqr (onipq pi))
      (\pi => (oncqr $ onipq pi) . oncpq pi)
      $ \pi, fext => funExt $ \pd =>
        trans
          (rewrite (fcong {x=(oncpq pi pd)} $ qrcomm (onipq pi) fext) in Refl)
          (fcong {x=pd} $ pqcomm pi fext)

--------------------------------------------------------------------
---- Two-categorical structure of polydinatural transformations ----
--------------------------------------------------------------------

-- The polydinatural transformations of difunctors form a two-category:
-- polydinatural transformations have horizontal composition and whiskering.

export
pdNTwhiskerL : {0 q, r : PolyDifunc} -> PolyDiNT q r -> (p : PolyDifunc) ->
  PolyDiNT (pdfComp q p) (pdfComp r p)
pdNTwhiskerL {q=(PDF qp qd qc qm)} {r=(PDF rp rd rc rm)}
  (PDNT oni onb onc ntcomm) (PDF pp pd pc pm) =
    PDNT
      (\(qi ** pi ** qcpd) => (oni qi ** pi ** qcpd . onb qi))
      (\(qi ** pi ** qcpd) => id)
      (\(qi ** pi ** qcpd) => onc qi)
      (\(qi ** pi ** qcpd), fext =>
        funExt $ \qd => rewrite fcong {x=qd} (ntcomm qi fext) in Refl)

export
pdNTwhiskerR : {0 p, q : PolyDifunc} -> PolyDiNT p q -> (r : PolyDifunc) ->
  PolyDiNT (pdfComp r p) (pdfComp r q)
pdNTwhiskerR {p=(PDF pp pd pc pm)} {q=(PDF qp qd qc qm)}
  (PDNT oni onb onc ntcomm) (PDF rp rd rc rm) =
    PDNT
      (\(ri ** pi ** rcpd) => (ri ** oni pi ** onc pi . rcpd))
      (\(ri ** pi ** rcpd) => onb pi)
      (\(ri ** pi ** rcpd) => id)
      (\(ri ** pi ** rcpd), fext =>
        funExt $ \rd => fcong $ ntcomm pi fext)

export
pdNThcomp : {0 p, q' : PolyDifunc} -> {p', q : PolyDifunc} ->
  PolyDiNT q q' -> PolyDiNT p p' -> PolyDiNT (pdfComp q p) (pdfComp q' p')
pdNThcomp {p} {p'} {q} {q'} beta alpha =
  pdNTvcomp (pdNTwhiskerL {q} {r=q'} beta p') (pdNTwhiskerR {p} {q=p'} alpha q)
