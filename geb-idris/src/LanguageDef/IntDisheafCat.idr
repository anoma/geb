module LanguageDef.IntDisheafCat

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.IntECofamCat

-----------------------------------------
-----------------------------------------
---- Polynomial double-Yoneda lemmas ----
-----------------------------------------
-----------------------------------------

----------------------------------------
---- Polynomial-polynomial category ----
----------------------------------------

public export
PolyPolyCat : IntCatSig -> IntCatSig
PolyPolyCat cat = ECofamCatSig (ECofamCatSig cat)

public export
PolyPolyObj : IntCatSig -> Type
PolyPolyObj cat = icObj (PolyPolyCat cat)

public export
PolyPolyMorOnIdx : (cat : IntCatSig) -> IntMorSig (PolyPolyObj cat)
PolyPolyMorOnIdx cat = IntECofamMorOnIdx (icMor $ ECofamCatSig cat)

public export
PolyPolyMorOnMor : (cat : IntCatSig) -> (dom, cod : PolyPolyObj cat) ->
  PolyPolyMorOnIdx cat dom cod -> Type
PolyPolyMorOnMor cat = IntECofamMorOnMor (icMor $ ECofamCatSig cat)

public export
PolyPolyMor : (cat : IntCatSig) -> IntMorSig (PolyPolyObj cat)
PolyPolyMor cat = icMor (PolyPolyCat cat)

--------------------------------------
---- Dirichlet-Dirichlet category ----
--------------------------------------

public export
DirichDirichCat : IntCatSig -> IntCatSig
DirichDirichCat cat = EFamCatSig (EFamCatSig cat)

public export
DirichDirichObj : IntCatSig -> Type
DirichDirichObj cat = icObj (DirichDirichCat cat)

public export
DirichDirichMorOnIdx : (cat : IntCatSig) -> IntMorSig (DirichDirichObj cat)
DirichDirichMorOnIdx cat = IntEFamMorOnIdx (icMor $ EFamCatSig cat)

public export
DirichDirichMorOnMor : (cat : IntCatSig) -> (dom, cod : DirichDirichObj cat) ->
  DirichDirichMorOnIdx cat dom cod -> Type
DirichDirichMorOnMor cat = IntEFamMorOnMor (icMor $ EFamCatSig cat)

public export
DirichDirichMor : (cat : IntCatSig) -> IntMorSig (DirichDirichObj cat)
DirichDirichMor cat = icMor (DirichDirichCat cat)

----------------------------------
---- Polynomial apply functor ----
----------------------------------

public export
PolyAppFunc : (cat : IntCatSig) -> icObj cat -> PolyPolyObj cat
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

--------------------------------------------------
---- Polynomial covariant double-Yoneda lemma ----
--------------------------------------------------

public export
record PolyDoubleYo (cat : IntCatSig) (a, b : icObj cat) where
  constructor MkPolyDoubleYo
  PolyDoubleYoEmbed :
    PolyPolyMor cat (PolyAppFunc cat a) (PolyAppFunc cat b)

public export
PolyDoubleYoOnIdx : {cat : IntCatSig} -> {a, b : icObj cat} ->
  PolyDoubleYo cat a b ->
  PolyPolyMorOnIdx cat (PolyAppFunc cat a) (PolyAppFunc cat b)
PolyDoubleYoOnIdx {cat} {a} {b} (MkPolyDoubleYo (onpos ** ondir)) = onpos

public export
PolyDoubleYoOnMor : {cat : IntCatSig} -> {a, b : icObj cat} ->
  (y : PolyDoubleYo cat a b) ->
  PolyPolyMorOnMor cat (PolyAppFunc cat a) (PolyAppFunc cat b)
    (PolyDoubleYoOnIdx {cat} {a} {b} y)
PolyDoubleYoOnMor {cat} {a} {b} (MkPolyDoubleYo (onpos ** ondir)) = ondir

public export
PolyDoubleYoDimapOnIdx : (cat : IntCatSig) ->
  (s, t, a, b : icObj cat) -> icMor cat a s -> icMor cat t b ->
  PolyDoubleYo cat s t ->
  PolyPolyMorOnIdx cat (PolyAppFunc cat a) (PolyAppFunc cat b)
PolyDoubleYoDimapOnIdx cat s t a b mas mtb (MkPolyDoubleYo (onpos ** ondir))
  (i ** mia) =
    case (onpos (i ** icComp cat i a s mas mia)) of
      (op1 ** op2) => (op1 ** icComp cat op1 t b mtb op2)

public export
PolyDoubleYoDimapOnMor : (cat : IntCatSig) ->
  (s, t, a, b : icObj cat) -> (mas : icMor cat a s) -> (mtb : icMor cat t b) ->
  (y : PolyDoubleYo cat s t) ->
  PolyPolyMorOnMor cat (PolyAppFunc cat a) (PolyAppFunc cat b)
    (PolyDoubleYoDimapOnIdx cat s t a b mas mtb y)
PolyDoubleYoDimapOnMor cat s t a b mas mtb (MkPolyDoubleYo (onpos ** ondir))
    (i ** mia) with
    (onpos (i ** icComp cat i a s mas mia),
     ondir (i ** icComp cat i a s mas mia)) proof odeq
  PolyDoubleYoDimapOnMor cat s t a b mas mtb (MkPolyDoubleYo (onpos ** ondir))
    (i ** mia) | ((op1 ** op2), (od1 ** od2)) with (od2 ()) proof ueq
      PolyDoubleYoDimapOnMor cat s t a b mas mtb
          (MkPolyDoubleYo (onpos ** ondir)) (i ** mia)
          | ((op1 ** op2), (od1 ** od2)) | od2u with (od1 ())
        PolyDoubleYoDimapOnMor cat s t a b mas mtb
          (MkPolyDoubleYo (onpos ** ondir)) (i ** mia)
          | ((op1 ** op2), (od1 ** od2)) | od2u | () =
            (\() => () **
             \() =>
              rewrite fstEq odeq in rewrite sym (dpeq1 (fstEq odeq)) in od2u)

public export
PolyDoubleYoDimap : (cat : IntCatSig) ->
  IntEndoDimapSig (icObj cat) (icMor cat) (PolyDoubleYo cat)
PolyDoubleYoDimap cat s t a b mas mtb y =
  MkPolyDoubleYo
    (PolyDoubleYoDimapOnIdx cat s t a b mas mtb y **
     PolyDoubleYoDimapOnMor cat s t a b mas mtb y)

public export
toDoubleYo : (cat : IntCatSig) ->
  IntEndoProfNTSig (icObj cat) (icMor cat) (PolyDoubleYo cat)
toDoubleYo cat x y mxy =
  MkPolyDoubleYo
    (\(i ** mix) => (i ** icComp cat i x y mxy mix) **
     \(i ** mix) => (\() => () ** \() => icId cat i))

public export
fromDoubleYo : (cat : IntCatSig) ->
  IntEndoProfNTSig (icObj cat) (PolyDoubleYo cat) (icMor cat)
fromDoubleYo cat x y (MkPolyDoubleYo (onpos ** ondir)) with
    (ondir (x ** icId cat x))
  fromDoubleYo cat x y (MkPolyDoubleYo (onpos ** ondir)) |
      ((od1 ** od2)) with (od2 ())
    fromDoubleYo cat x y (MkPolyDoubleYo (onpos ** ondir)) |
        ((od1 ** od2)) | od2u with (od1 ())
      fromDoubleYo cat x y (MkPolyDoubleYo (onpos ** ondir)) |
          ((od1 ** od2)) | od2u | () with (onpos (x ** icId cat x))
        fromDoubleYo cat x y (MkPolyDoubleYo (onpos ** ondir)) |
          (od1 ** od2) | od2u | () | (op1 ** op2) =
            icComp cat x op1 y op2 od2u

------------------------------------------------------------
---- Polynomial covariant double-Yoneda lemma in `Type` ----
------------------------------------------------------------

public export
PolyTypeDoubleYo : Type -> Type -> Type
PolyTypeDoubleYo = PolyDoubleYo TypeCat

public export
PolyTypeDoubleYoDimap : IntEndoDimapSig Type TypeMor PolyTypeDoubleYo
PolyTypeDoubleYoDimap = PolyDoubleYoDimap TypeCat

public export
toDoubleYoType : ProfNT HomProf PolyTypeDoubleYo
toDoubleYoType {a} {b} = toDoubleYo TypeCat a b

public export
fromDoubleYoType : ProfNT PolyTypeDoubleYo HomProf
fromDoubleYoType {a} {b} = fromDoubleYo TypeCat a b

----------------------------------------------------------------------------
----------------------------------------------------------------------------
---- Dependent-type-style poly-difunctor ("twisted polynomial functor") ----
----------------------------------------------------------------------------
----------------------------------------------------------------------------

public export
ECofamPolyCat : IntCatSig -> IntCatSig
ECofamPolyCat = PolyPolyCat

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
