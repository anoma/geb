module LanguageDef.GenPolyFunc

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.QType
import public LanguageDef.PolyCat
import public LanguageDef.SliceFuncCat
import public LanguageDef.SlicePolyCat
import public LanguageDef.InternalCat
import public LanguageDef.IntArena
import public LanguageDef.IntUFamCat
import public LanguageDef.IntUCofamCat
import public LanguageDef.IntEFamCat
import public LanguageDef.IntECofamCat

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

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

----------------------------------
---- Polynomial apply functor ----
----------------------------------

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

public export
ECofamType : IntCatSig
ECofamType = ECofamCatSig TypeCat

public export
ECofamPolyType : IntCatSig
ECofamPolyType = ECofamCatSig ECofamType

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
