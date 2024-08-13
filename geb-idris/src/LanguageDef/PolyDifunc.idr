module LanguageDef.PolyDifunc

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.DisliceCat
import public LanguageDef.PolyCat
import public LanguageDef.DislicePolyCat
import public LanguageDef.IntECofamCat
import public LanguageDef.GenPolyFunc
import public LanguageDef.IntDisheafCat

%default total
%hide Library.IdrisCategories.BaseChangeF
%hide Prelude.Ops.infixl.(|>)

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
---- Category of pi types, viewed as a subcategory of the category of monos ----
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

public export
PiMonCatObj : Type
PiMonCatObj = (dom : Type ** cod : SliceObj dom ** Pi {a=dom} cod)

public export
PiMonCatMor : IntMorSig PiMonCatObj
PiMonCatMor (d ** c ** m) (d' ** c' ** m') =
  (l : d' -> d **
   r1 : (ed' : d') -> c' ed' -> d **
   comm1 : (ed' : d') -> r1 ed' (m' ed') = l ed' **
   r2 : (ed' : d') -> (ec' : c' ed') -> c (r1 ed' ec') **
   (ed' : d') -> m (l ed') = replace {p=c} (comm1 ed') (r2 ed' (m' ed')))

-------------------------------------------
-------------------------------------------
---- Polydifunctors as enriched arenas ----
-------------------------------------------
-------------------------------------------

-------------------------------
---- Polydifunctor objects ----
-------------------------------

{-
 - We might view a polydifunctor as a functor from
 - `Type` to `[op(Type), Type`]`.  As such, we could define it as a parametric
 - right adjoint from the category of presheaves (into `Type`) over the
 - terminal category -- which is equivalent to `Type` itself -- to the
 - category of presheaves over `Type`.  Examining the formula for PRA
 - functors between presheaf categories at
 - https://ncatlab.org/nlab/show/parametric+right+adjoint#generic_morphisms ,
 - we set `I := 1` and `J := Type`, and thus determine that the PRA functor
 - is determined by the following data:
 -
 -  - An object `T1` in `[op(J), Type]`, i.e. a presheaf over `Type`,
 -    which, because we are trying to define a polynomial _difunctor_,
 -    we treat as a Dirichlet functor
 -  - A functor `el_op(T1) -> [op(I), Type]`; since `I` is the terminal
 -    category, this reduces to a functor in `[el_op(T1), Type]`.
 -    And because that is a presheaf on a category of elements, it is
 -    equivalently a slice over `T1`.
 -}
public export
record PDiData where
  constructor PDiD
  pdiT1 : MLDirichCatObj
  pdiF : MlDirichSlObj pdiT1

public export
PDiPos1 : PDiData -> Type
PDiPos1 = dfPos . pdiT1

public export
PDiPos2 : (pdid : PDiData) -> PDiPos1 pdid -> Type
PDiPos2 pdid = mdsOnPos (pdiF pdid)

public export
PDiDir1 : (pdid : PDiData) -> PDiPos1 pdid -> Type
PDiDir1 pdid = dfDir (pdiT1 pdid)

public export
PDiDir2 : (pdid : PDiData) ->
  (i : PDiPos1 pdid) -> PDiPos2 pdid i -> PDiDir1 pdid i -> Type
PDiDir2 pdid = mdsDir (pdiF pdid)

public export
PDiTot1 : (pdid : PDiData) -> Type
PDiTot1 = dfTot . pdiT1

public export
PDiTot2 : (pdid : PDiData) -> Type
PDiTot2 pdid = mlDirichSlObjTotTot {ar=(pdiT1 pdid)} $ pdiF pdid

-----------------------------------------------------------------
---- Polydifunctors as families of slice polynomial functors ----
-----------------------------------------------------------------

public export
PDiToSPFdepData : (pdid : PDiData) ->
  SPFdepData {b=(PDiPos1 pdid)} (PDiDir1 pdid) (const Unit)
PDiToSPFdepData pdid = MlDirichSlToSPFDD {ar=(pdiT1 pdid)} $ pdiF pdid

-- For each position of `T1`, we have a dependent polynomial functor from
-- the slice category of that position's direction to `Type` (which is
-- equivalent to the slice category of `Type` over `Unit`).
public export
PDiToSPFData : (pdid : PDiData) ->
  (i : PDiPos1 pdid) -> SPFData (PDiDir1 pdid i) Unit
PDiToSPFData pdid = SPFDataFamFromDep (PDiToSPFdepData pdid)

------------------------------------------
---- Interpretation of polydifunctors ----
------------------------------------------

-- This is the interpretation of the above family of `SPFData`s.
public export
InterpPDiSPF : (pdid : PDiData) ->
  (i : PDiPos1 pdid) -> SliceObj (PDiDir1 pdid i) -> Type
InterpPDiSPF pdid i sl = InterpSPFdepDataEl (PDiToSPFdepData pdid) i sl ()

-- The interpretation of the application to the first parameter of the
-- curried form of the dependent profunctor (AKA presheaf on the
-- twisted-arrow category) specified by a `PDiData`, returning a
-- slice polynomial functor over the selected direction.
public export
InterpPDi1SPF : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  SPFData (idfDir {p=(pdiT1 pdid)} idf) Unit
InterpPDi1SPF pdid x idf = PDiToSPFData pdid (idfPos {p=(pdiT1 pdid)} idf)

public export
InterpPDi1 : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  idfDirSl {p=(pdiT1 pdid)} idf -> Type
InterpPDi1 pdid x idf = InterpPDiSPF pdid (idfPos {p=(pdiT1 pdid)} idf)

public export
InterpPDi2SPF : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  SPFData x Unit
InterpPDi2SPF pdid x idf = spfdPrecompSigma (snd idf) (InterpPDi1SPF pdid x idf)

public export
InterpPDi2u : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  SliceFunctor x Unit
InterpPDi2u pdid x idf = InterpSPFData $ InterpPDi2SPF pdid x idf

public export
InterpPDi2SPFmap : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  SliceFMap (InterpPDi2u pdid x idf)
InterpPDi2SPFmap pdid x idf = InterpSPFDataMap $ InterpPDi2SPF pdid x idf

public export
InterpPDi2 : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  SliceObj x -> Type
InterpPDi2 pdid x idf y = InterpPDi2u pdid x idf y ()

public export
InterpPDi2map : (pdid : PDiData) ->
  (x : Type) -> (idf : InterpDirichFunc (pdiT1 pdid) x) ->
  (y, y' : SliceObj x) ->
  SliceMorphism {a=x} y y' ->
  InterpPDi2 pdid x idf y -> InterpPDi2 pdid x idf y'
InterpPDi2map pdid x idf y y' m = InterpPDi2SPFmap pdid x idf y y' m ()

public export
InterpPDi : (pdid : PDiData) -> (x : Type) -> (y : SliceObj x) -> Type
InterpPDi pdid x =
  Sigma {a=(InterpDirichFunc (pdiT1 pdid) x)} . flip (InterpPDi2 pdid x)

public export
InterpPDiu : (pdid : PDiData) -> (x : Type) -> SliceFunctor x Unit
InterpPDiu pdid x y () = InterpPDi pdid x y

---------------------------------------------------
---- Morphism-map components of polydifunctors ----
---------------------------------------------------

public export
PDiLmapu : (pdid : PDiData) -> (x, x' : Type) -> (m : x' -> x) ->
  SliceNatTrans {x=x'} {y=Unit}
    (InterpPDiu pdid x . SliceFibSigmaF m)
    (InterpPDiu pdid x')
PDiLmapu pdid x x' m y' () =
  dpBimap (InterpDFMap (pdiT1 pdid) m)
  $ \(i1 ** i2), ((ep ** dm1) ** dm2) =>
    ((ep **
     \ex, d1 =>
        let sfs = dm2 (sfsFst $ dm1 ex d1) ((ex ** d1) ** Refl) in
        rewrite sym (sfsEq $ dm1 ex d1) in
        rewrite sym (sfsEq sfs) in
        SFS (sfsFst sfs) ()) **
     \ex', ((ex ** d1) ** xeq) =>
      rewrite sym xeq in
      sfsSnd $ dm2 (sfsFst $ dm1 ex d1) ((ex ** d1) ** Refl))

public export
PDiLmap : (pdid : PDiData) -> (x, x' : Type) -> (m : x' -> x) ->
  (y' : SliceObj x') ->
  InterpPDi pdid x (SliceFibSigmaF m y') -> InterpPDi pdid x' y'
PDiLmap pdid x x' m y' = PDiLmapu pdid x x' m y' ()

public export
PDiRmap : (pdid : PDiData) -> (x : Type) -> (y, y' : SliceObj x) ->
  SliceMorphism {a=x} y y' ->
  InterpPDi pdid x y -> InterpPDi pdid x y'
PDiRmap pdid x y y' m =
  dpMapSnd $ \i1 => dpMapSnd $ \p2, i2, d1, d2 => m d1 $ i2 d1 d2

public export
PDiDimap : (pdid : PDiData) ->
  (x, x' : Type) -> (y : SliceObj x) -> (y' : SliceObj x') ->
  (mx : x' -> x) -> (my : SliceMorphism {a=x} y (SliceFibSigmaF mx y')) ->
  InterpPDi pdid x y -> InterpPDi pdid x' y'
PDiDimap pdid x x' y y' mx my =
  PDiLmap pdid x x' mx y' . PDiRmap pdid x y (SliceFibSigmaF mx y') my

public export
PDiDimapDP : (pdid : PDiData) ->
  (x : Type) -> (y, x' : SliceObj x) ->
  (y' : SliceObj $ Sigma {a=x} x') ->
  (lm : (ex : x) -> y ex -> x' ex) ->
  (rm : (ex : x) -> (ey : y ex) -> y' (ex ** lm ex ey)) ->
  InterpPDi pdid x y -> InterpPDi pdid (Sigma {a=x} x') y'
PDiDimapDP pdid x y x' y' lm rm =
  PDiDimap pdid x (Sigma x') y y' DPair.fst $
    \ex, ey => SFS (ex ** lm ex ey) (rm ex ey)

-----------------------------------------------------------
---- Categories of diagonal elements of polydifunctors ----
-----------------------------------------------------------

-- Suppose we want to write a restricted version of `dimap` that is only
-- required to operate on diagonal elements.  Diagonal elements are those
-- where `x ~=~ y` and `x' ~=~ y'`, which may be represented either by
-- the `y`s being slices whose values are `const Unit` (the terminal objects
-- of the slice category over `x`, which is the `id` morphism on `x` in
-- categorial style), or, if we take a twisted-arrow viewpoint, the morphism
-- being the identity.
--
-- Note that the parameters `x`, `x'`, and `m` constitute a monomorphism
-- from `x` to `Sigma {a=x} x'`, where the proof that it is a monomorphism
-- is the exhibition of a left inverse, namely the projection from
-- `Sigma {a=x} x'` to `x`.
--
-- Note also that `Pi {a=x} x'` may equivalently be viewed as
-- `SliceMorphism {a=x} (SliceObjTerminal x) x'` -- that is, it is
-- a section, or global element (or "point"), of `x'`.  See
-- https://ncatlab.org/nlab/show/generalized+element#in_toposes.

public export
InterpPDiDiag : (pdid : PDiData) -> (x : Type) -> Type
InterpPDiDiag pdid x = InterpPDi pdid x (SliceObjTerminal x)

public export
PDiDiagMap : (pdid : PDiData) ->
  (x : Type) -> (x' : SliceObj x) -> Pi {a=x} x' ->
  InterpPDiDiag pdid x -> InterpPDiDiag pdid (Sigma {a=x} x')
PDiDiagMap pdid x x' m =
  PDiDimapDP pdid
    x (SliceObjTerminal x) x' (SliceObjTerminal $ Sigma {a=x} x')
    (\ex, u => m ex)
    (\_, _ => ())

public export
PDiDiagElemObj : PDiData -> Type
PDiDiagElemObj = Sigma {a=Type} . InterpPDiDiag

public export
data PDiDiagElemMor : (pdid : PDiData) -> IntMorSig (PDiDiagElemObj pdid) where
  PDEM : {pdid : PDiData} -> {x : Type} -> {x' : SliceObj x} ->
    (el : InterpPDiDiag pdid x) -> (m : Pi {a=x} x') ->
    PDiDiagElemMor pdid
      (x ** el)
      (Sigma {a=x} x' ** PDiDiagMap pdid x x' m el)

---------------------------------------------------
---------------------------------------------------
---- Self-representation of Dirichlet functors ----
---------------------------------------------------
---------------------------------------------------

-- We can define a functor from `Type` to the category of Dirichlet
-- functors by defining a slice functor between the Dirichlet-functor
-- slice categories over `dfRepVoid` and `dfRepUnit`, because, as explained
-- in the comments to their definitions, those functors' categories of
-- elements are (equivalent to) `Type` and the category of Dirichlet functors
-- on `Type`, respectively.
public export
TypeDirichData : Type
TypeDirichData = PRAData MLDirichCat.dfRepVoid MLDirichCat.dfRepUnit

public export
InterpPRAdataOmapFromPDi : TypeDirichData ->
  MlDirichSlFunc MLDirichCat.dfRepVoid MLDirichCat.dfRepUnit
InterpPRAdataOmapFromPDi = InterpPRAdataOmap

public export
InterpPDiPRAdataOmap : (tdd : TypeDirichData) -> Type -> MLDirichCatObj
InterpPDiPRAdataOmap tdd =
  dfSlRepUnitToDirich . InterpPRAdataOmapFromPDi tdd . dfTypeToSlRepVoid

public export
InterpPDiDataOmap : (tdd : TypeDirichData) -> Type -> Type -> Type
InterpPDiDataOmap tdd x y = InterpDirichFunc (InterpPDiPRAdataOmap tdd y) x

public export
InterpPDiDataDimap : (tdd : TypeDirichData) ->
  IntEndoDimapSig TypeObj TypeMor (InterpPDiDataOmap tdd)
InterpPDiDataDimap (PRAD (MDSobj x slx) (MDSobj slsx _)) s t a b mas mtb
  ((ex ** mxt) ** msx) =
    ((ex ** \(() ** eslx) => mtb $ mxt (() ** eslx)) **
     \ea => (fst (msx $ mas ea) ** \_, _, v => void v))

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
  mdaPred :
    Pi {a=(pfPos mdaAr)} (SliceObj . pfDir {p=mdaAr})

public export
mdaPos : MLDiArena -> Type
mdaPos = pfPos . mdaAr

public export
mdaStruct : (mda : MLDiArena) -> SliceObj (mdaPos mda)
mdaStruct mda = pfDir {p=(mdaAr mda)}

public export
MDAterm : (mda : MLDiArena) -> SliceObj (mdaPos mda)
MDAterm mda i = Sigma {a=(mdaStruct mda i)} (mdaPred mda i)

public export
record MLDiNatTrans (dom, cod : MLDiArena) where
  constructor MLDiNT
  mdntOnPos :
    mdaPos dom -> mdaPos cod
  mdntOnTerm :
    SliceMorphism {a=(mdaPos dom)} (MDAterm cod . mdntOnPos) (MDAterm dom)

public export
record InterpMDA (mda : MLDiArena) (struct : Type) (pred : SliceObj struct)
    where
  constructor IMDA
  imdaPos : mdaPos mda
  imdaAssign : MDAterm mda imdaPos -> Sigma {a=struct} pred

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

--------------------------------------------------
---- Categories of elements of polydifunctors ----
--------------------------------------------------

public export
record PDFelemCatObj (pdf : PolyDifunc) where
  constructor PDFElObj
  pdfElPos : pdfPos pdf
  pdfElPred : SliceObj (pdfCobase pdf pdfElPos)
  pdfElStruct : Type
  pdfElAssign : pdfBase pdf pdfElPos -> pdfElStruct

public export
pdfElProj : {pdf : PolyDifunc} -> (el : PDFelemCatObj pdf) ->
  Sigma {a=(pdfCobase pdf $ pdfElPos el)} (pdfElPred el) -> pdfElStruct el
pdfElProj {pdf} el = pdfElAssign el . pdfProj pdf (pdfElPos el) . DPair.fst

public export
data PDFelemCatMor : {pdf : PolyDifunc} -> (dom, cod : PDFelemCatObj pdf) ->
    Type where
  PDFElMor : {0 pdf : PolyDifunc} ->
    {i : pdfPos pdf} ->
    {dpred, cpred : SliceObj $ pdfCobase pdf i} ->
    {dstruct, cstruct : Type} ->
    {dassign : pdfBase pdf i -> dstruct} ->
    (contra : SliceMorphism {a=(pdfCobase pdf i)} dpred cpred) ->
    (covar : dstruct -> cstruct) ->
    PDFelemCatMor {pdf}
      (PDFElObj i dpred dstruct dassign)
      (PDFElObj i cpred cstruct (covar . dassign))

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

public export
PDiMonoidCat : IntCatSig
PDiMonoidCat =
  ICat
    Unit
  $ MICS
    (\_, _ => PolyDifunc)
  $ ICS
    (\_ => PdfHomProfId)
    (\_, _, _ => pdfComp)

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

public export
PolyDiCat : IntCatSig
PolyDiCat =
  ICat
    PolyDifunc
  $ MICS
    PolyDiNT
  $ ICS
    pdNTid
    (\p, q, r => pdNTvcomp {r} {q} {p})

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

---------------------------------------
---- Polynomial/Dirichlet functors ----
---------------------------------------

-- Twisted polynomials subsume both polynomial and Dirichlet functors.

export
PdfFromPoly : PolyFunc -> PolyDifunc
PdfFromPoly p = PDF (pfPos p) (\_ => Void) (pfDir {p}) (\i, v => void v)

export
PdfFromPolyNT : (p, q : PolyFunc) ->
  PolyNatTrans p q -> PolyDiNT (PdfFromPoly p) (PdfFromPoly q)
PdfFromPolyNT (ppos ** pdir) (qpos ** qdir) (onpos ** ondir) =
  PDNT
    onpos
    ondir
    (\_ => Prelude.id {a=Void})
    (\pi, fext => funExt $ \v => void v)

export
PdfToPolyNT : (p, q : PolyFunc) ->
  PolyDiNT (PdfFromPoly p) (PdfFromPoly q) -> PolyNatTrans p q
PdfToPolyNT (ppos ** pdir) (qpos ** qdir) (PDNT onpos onbase oncobase comm) =
  (onpos ** onbase)

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
PdfFromDirichNT : (p, q : MLDirichCatObj) ->
  DirichNatTrans p q -> PolyDiNT (PdfFromDirich p) (PdfFromDirich q)
PdfFromDirichNT (ppos ** pdir) (qpos ** qdir) (onpos ** ondir) =
  PDNT
    onpos
    (\_ => Prelude.id {a=Unit})
    ondir
    (\_, _ => Refl)

export
PdfToDirichNT : (p, q : MLDirichCatObj) ->
  PolyDiNT (PdfFromDirich p) (PdfFromDirich q) -> DirichNatTrans p q
PdfToDirichNT (ppos ** pdir) (qpos ** qdir) (PDNT onpos onbase oncobase comm) =
  (onpos ** oncobase)

export
InterpPdfFromDirich : (p : PolyFunc) -> (x : Type) ->
  InterpDirichFunc p x -> InterpPDF (PdfFromDirich p) x Unit (\_ => ())
InterpPdfFromDirich (pos ** dir) x (i ** dm) =
  IPDF i dm (\_ => ()) $ \fext => funExt $ \_ => Refl

export
InterpPdfToDirich : (p : PolyFunc) -> (x : Type) ->
  InterpPDF (PdfFromDirich p) x Unit (\_ => ()) -> InterpDirichFunc p x
InterpPdfToDirich (pos ** dir) x (IPDF i mx my comm) = (i ** mx)
