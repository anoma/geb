module LanguageDef.IntDisheafCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.IntECofamCat

----------------------------------------------------------------------------
----------------------------------------------------------------------------
---- Dependent-type-style poly-difunctor ("twisted polynomial functor") ----
----------------------------------------------------------------------------
----------------------------------------------------------------------------

public export
ECofamPolyCat : IntCatSig -> IntCatSig
ECofamPolyCat cat = ECofamCatSig (ECofamCatSig cat)

public export
TwistArrAr : IntCatSig -> Type
TwistArrAr cat = icObj (ECofamCatSig cat)

public export
twarCod : {cat : IntCatSig} -> TwistArrAr cat -> Type
twarCod = DPair.fst

public export
twarDom : {cat : IntCatSig} ->
  (twar : TwistArrAr cat) -> twarCod {cat} twar -> icObj cat
twarDom = DPair.snd

public export
TwistArrMor : (cat : IntCatSig) -> IntMorSig (TwistArrAr cat)
TwistArrMor cat = icMor (ECofamCatSig cat)

public export
TwistPolyFunc : IntCatSig -> Type
TwistPolyFunc cat = icObj (ECofamPolyCat cat)

public export
TwistNT : (cat : IntCatSig) -> IntMorSig (TwistPolyFunc cat)
TwistNT cat = icMor (ECofamPolyCat cat)

public export
tpfPos : {cat : IntCatSig} -> TwistPolyFunc cat -> Type
tpfPos = DPair.fst

public export
tpfAr : {cat : IntCatSig} ->
  (tpf : TwistPolyFunc cat) -> tpfPos {cat} tpf -> TwistArrAr cat
tpfAr = DPair.snd

public export
tpfCod : {cat : IntCatSig} -> (tpf : TwistPolyFunc cat) ->
  SliceObj (tpfPos {cat} tpf)
tpfCod {cat} tpf = twarCod {cat} . tpfAr {cat} tpf

public export
tpfDom : {cat : IntCatSig} -> (tpf : TwistPolyFunc cat) ->
  (i : tpfPos {cat} tpf) -> tpfCod {cat} tpf i -> icObj cat
tpfDom {cat} tpf i = twarDom {cat} (tpfAr {cat} tpf i)

public export
ECofamType : IntCatSig
ECofamType = ECofamCatSig TypeCat

public export
TwistArrArType : Type
TwistArrArType = TwistArrAr TypeCat

public export
TwistArrMorType : IntMorSig TwistArrArType
TwistArrMorType = TwistArrMor TypeCat

public export
twarCodType : TwistArrArType -> Type
twarCodType = twarCod {cat=TypeCat}

public export
twarDomType : (twar : TwistArrArType) -> SliceObj (twarCodType twar)
twarDomType = twarDom {cat=TypeCat}

public export
ECofamPolyType : IntCatSig
ECofamPolyType = ECofamPolyCat TypeCat

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
tpfCodType : (tpf : TwistPolyFuncType) -> SliceObj (tpfPosType tpf)
tpfCodType = tpfCod {cat=TypeCat}

public export
tpfDomType : (tpf : TwistPolyFuncType) ->
  (i : tpfPosType tpf) -> SliceObj (tpfCodType tpf i)
tpfDomType = tpfDom {cat=TypeCat}

public export
TwistNTType : IntMorSig TwistPolyFuncType
TwistNTType = TwistNT TypeCat

public export
InterpTPF : TwistPolyFuncType -> TwistArrArType -> Type
InterpTPF = InterpECofamCopreshfOMap TwistArrArType TwistArrMorType

public export
itpfPos : {tpf : TwistPolyFuncType} -> {twar : TwistArrArType} ->
  InterpTPF tpf twar -> tpfPosType tpf
itpfPos {tpf} {twar} = DPair.fst

public export
itpfDir : {tpf : TwistPolyFuncType} -> {twar : TwistArrArType} ->
  (itpf : InterpTPF tpf twar) ->
  TwistArrMorType (tpfArType tpf $ itpfPos {tpf} {twar} itpf) twar
itpfDir {tpf} {twar} itpf = DPair.snd itpf

public export
itpfBC : {tpf : TwistPolyFuncType} -> {twar : TwistArrArType} ->
  (itpf : InterpTPF tpf twar) ->
  tpfCodType tpf (itpfPos {tpf} {twar} itpf) -> twarCodType twar
itpfBC {tpf} {twar} itpf = DPair.fst (itpfDir itpf)

public export
itpfSM : {tpf : TwistPolyFuncType} -> {twar : TwistArrArType} ->
  (itpf : InterpTPF tpf twar) ->
  SliceMorphism {a=(tpfCodType tpf $ itpfPos {tpf} {twar} itpf)}
    (BaseChangeF (itpfBC {tpf} {twar} itpf) (twarDomType twar))
    (tpfDomType tpf $ itpfPos {tpf} {twar} itpf)
itpfSM {tpf} {twar} itpf = DPair.snd (itpfDir itpf)

public export
twntOnPos : {cat : IntCatSig} -> {p, q : TwistPolyFunc cat} ->
  TwistNT cat p q -> tpfPos {cat} p -> tpfPos {cat} q
twntOnPos {p} {q} = DPair.fst

public export
twntOnDir : {cat : IntCatSig} -> {p, q : TwistPolyFunc cat} ->
  (twnt : TwistNT cat p q) ->
  (i : tpfPos {cat} p) ->
  TwistArrMor cat
    (tpfAr {cat} q (twntOnPos {cat} {p} {q} twnt i))
    (tpfAr {cat} p i)
twntOnDir {p} {q} = DPair.snd

public export
twntOnBase : {cat : IntCatSig} -> {p, q : TwistPolyFunc cat} ->
  (twnt : TwistNT cat p q) ->
  SliceMorphism {a=(tpfPos {cat} p)}
    (BaseChangeF (twntOnPos {cat} {p} {q} twnt) (tpfCod {cat} q))
    (tpfCod {cat} p)
twntOnBase {p} {q} twnt i = DPair.fst (twntOnDir twnt i)

public export
twntOnTot : {p, q : TwistPolyFuncType} ->
  (twnt : TwistNTType p q) ->
  (i : tpfPosType p) ->
    SliceMorphism {a=(tpfCodType q $ twntOnPos {cat=TypeCat} {p} {q} twnt i)}
      (BaseChangeF (twntOnBase {cat=TypeCat} {p} {q} twnt i) (tpfDomType p i))
      (tpfDomType q $ twntOnPos {cat=TypeCat} {p} {q} twnt i)
twntOnTot {p} {q} twnt i = DPair.snd (twntOnDir {cat=TypeCat} twnt i)

-------------------------------------
-------------------------------------
---- Disheaf category definition ----
-------------------------------------
-------------------------------------

-- The disheaf category of a category is the category of existential
-- cofamilies (AKA polynomial functors) on its twisted-arrow category.

public export
IntDisheafCat : (c : IntCatSig) ->
  IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  IntCatSig
IntDisheafCat c mapId mapComp = ECofamCatSig $ TwArrCat c mapId mapComp

public export
IntDisheafObj : (c : IntCatSig) ->
  IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  Type
IntDisheafObj c mapId mapComp = icObj $ IntDisheafCat c mapId mapComp

public export
IntDisheafMor : (c : IntCatSig) ->
  (mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  (mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  IntMorSig (IntDisheafObj c mapId mapComp)
IntDisheafMor c mapId mapComp = icMor $ IntDisheafCat c mapId mapComp

public export
IntDisheafId : (c : IntCatSig) ->
  (mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  (mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  IntIdSig (IntDisheafObj c mapId mapComp) (IntDisheafMor c mapId mapComp)
IntDisheafId c mapId mapComp = icId $ IntDisheafCat c mapId mapComp

public export
IntDisheafComp : (c : IntCatSig) ->
  (mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  (mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  IntCompSig (IntDisheafObj c mapId mapComp) (IntDisheafMor c mapId mapComp)
IntDisheafComp c mapId mapComp = icComp $ IntDisheafCat c mapId mapComp

--------------------------------------------------------
--------------------------------------------------------
---- Interpretation of disheaf objects into `QType` ----
--------------------------------------------------------
--------------------------------------------------------

public export
IntDisheafSig : IntCatSig -> Type
IntDisheafSig c = (x, y : icObj c) -> icMor c x y -> QType

public export
IntDisheafFromProfunctorSig : {c : IntCatSig} ->
  (icObj c -> icObj c -> QType) -> IntDisheafSig c
IntDisheafFromProfunctorSig {c} p x y m = p x y

public export
IntDisheafMapBaseSig : {c : IntCatSig} -> IntDisheafSig c -> Type
IntDisheafMapBaseSig {c} p =
  (s, t : icObj c) -> (mst : icMor c s t) ->
  (a, b : icObj c) -> (mas : icMor c a s) -> (mtb : icMor c t b) ->
  fst0 (p s t mst) ->
  fst0
    (p a b $
      icComp c a t b
        mtb
      $ icComp c a s t
        mst
        mas)

public export
IntDisheafMapSig : {c : IntCatSig} -> IntDisheafSig c -> Type
IntDisheafMapSig {c} p =
  (s, t : icObj c) -> (mst : icMor c s t) ->
  (a, b : icObj c) -> (mas : icMor c a s) -> (mtb : icMor c t b) ->
  QMorph
    (p s t mst)
    (p a b $
      icComp c a t b
        mtb
      $ icComp c a s t
        mst
        mas)

public export
IntDisheafFromDimapSig : {c : IntCatSig} -> (p : icObj c -> icObj c -> QType) ->
  ((s, t, a, b : icObj c) -> icMor c a s -> icMor c t b ->
   QMorph (p s t) (p a b)) ->
  IntDisheafMapSig {c} (IntDisheafFromProfunctorSig {c} p)
IntDisheafFromDimapSig {c} p dm s t mst a b mas mtb = dm s t a b mas mtb

public export
IntDisheafInterp : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  IntDisheafObj c mapId mapComp ->
  IntDisheafSig c
IntDisheafInterp {c} {mapId} {mapComp} p x y f =
  QTypeFromType
  $ InterpECofamCopreshfOMap
    (TwArrObj c mapId mapComp) (TwArrMor c mapId mapComp)
    p ((x, y) ** f)

public export
IntDisheafInterpMapBase : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  (p : IntDisheafObj c mapId mapComp) ->
  IntDisheafMapBaseSig {c} (IntDisheafInterp {c} {mapId} {mapComp} p)
IntDisheafInterpMapBase {c} {mapId} {mapComp} p s t mst a b mas mtb =
  InterpECofamCopreshfFMap
    (TwArrObj c mapId mapComp)
    (TwArrMor c mapId mapComp)
    (TwArrComp c mapId mapComp)
    p
    ((s, t) ** mst)
    ((a, b) ** icComp c _ _ _ mtb $ icComp c _ _ _ mst mas)
    (CElMor (mas, mtb) Refl)

public export
IntDisheafInterpMap : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  (p : IntDisheafObj c mapId mapComp) ->
  IntDisheafMapSig {c} (IntDisheafInterp {c} {mapId} {mapComp} p)
IntDisheafInterpMap {c} {mapId} {mapComp} p s t mst a b mas mtb =
  QMorphFromMorph $
    IntDisheafInterpMapBase {c} {mapId} {mapComp} p s t mst a b mas mtb

-------------------------------------
-------------------------------------
---- Disheaf composition product ----
-------------------------------------
-------------------------------------

-- The identity of the composition product on disheaves, which is analogous
-- to that on profunctors.
public export
IntDisheafMonUnit : {c : IntCatSig} ->
  (mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  (mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)) ->
  IntDisheafObj c mapId mapComp
IntDisheafMonUnit {c} mapId mapComp = (TwArrObj c mapId mapComp ** id)

public export
IntDisheafMonProdPosMor : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  (q, p : IntDisheafObj c mapId mapComp) ->
  fst q -> fst p -> Type
IntDisheafMonProdPosMor {c} {mapId} {mapComp} q p qi pi =
   icMor c (snd $ fst $ snd q qi) (fst $ fst $ snd p pi)

public export
IntDisheafMonProdDir : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  (q, p : IntDisheafObj c mapId mapComp) ->
  (qi : fst q) -> (pi : fst p) ->
  IntDisheafMonProdPosMor {c} {mapId} {mapComp} q p qi pi ->
  TwArrObj c mapId mapComp
IntDisheafMonProdDir {c} {mapId} {mapComp} q p qi pi qcpd =
  ((fst $ fst $ snd q qi, snd $ fst $ snd p pi) **
   icComp c
    (fst $ fst $ snd q qi) (fst $ fst $ snd p pi) (snd $ fst $ snd p pi)
    (replace {p=(uncurry $ icMor c)}
      (pairFstSnd (DPair.fst $ DPair.snd p pi))
      (snd $ snd p pi)) $
   icComp c
    (fst $ fst $ snd q qi) (snd $ fst $ snd q qi) (fst $ fst $ snd p pi)
    qcpd
    (replace {p=(uncurry $ icMor c)}
      (pairFstSnd (DPair.fst $ DPair.snd q qi))
      (snd $ snd q qi)))

public export
IntDisheafMonProd : {c : IntCatSig} ->
  {mapId :
    IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  {mapComp :
    IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c)} ->
  IntDisheafObj c mapId mapComp ->
  IntDisheafObj c mapId mapComp ->
  IntDisheafObj c mapId mapComp
IntDisheafMonProd {c} {mapId} {mapComp} q p =
  ((qpi : (fst q, fst p) **
    IntDisheafMonProdPosMor {c} {mapId} {mapComp} q p (fst qpi) (snd qpi)) **
   \qpim =>
    IntDisheafMonProdDir {c} {mapId} {mapComp} q p
      (fst $ fst qpim) (snd $ fst qpim) (snd qpim))

-- The composition monoid on disheaves.
public export
IntDisheafCompMon : (c : IntCatSig) ->
  IntHomProfMapIdT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  IntHomProfMapCompT {c=(icObj c)} {mor=(icMor c)} (icId c) (icComp c) ->
  IntCatSig
IntDisheafCompMon c mapId mapComp =
  ICat
    Unit
  $ MICS
    (\_, _ => IntDisheafObj c mapId mapComp)
  $ ICS
    (\_ => IntDisheafMonUnit {c} mapId mapComp)
    (\_, _, _ => IntDisheafMonProd {c} {mapId} {mapComp})
