module LanguageDef.Diprofunctor

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.QType
import public LanguageDef.InternalCat
import public LanguageDef.InternalProfunctor

%hide Library.IdrisCategories.BaseChangeF
%default total

-- The category of polynomial diprofunctors.

----------------------------
----------------------------
---- Objects (functors) ----
----------------------------
----------------------------

public export
DiProAr : Type
DiProAr = (pos : Type ** pos -> (Type, Type))

public export
dprPos : DiProAr -> Type
dprPos = fst

public export
dprDirs : (dpr : DiProAr) -> dprPos dpr -> (Type, Type)
dprDirs = snd

public export
dprContra : (dpr : DiProAr) -> dprPos dpr -> Type
dprContra dpr i = fst (dprDirs dpr i)

public export
dprCovar : (dpr : DiProAr) -> dprPos dpr -> Type
dprCovar dpr i = snd (dprDirs dpr i)

public export
InterpDPRcontra : (dpr : DiProAr) -> dprPos dpr -> Type -> Type
InterpDPRcontra dpr i x = x -> dprContra dpr i

public export
InterpDPRcovar : (dpr : DiProAr) -> dprPos dpr -> Type -> Type
InterpDPRcovar dpr i y = dprCovar dpr i -> y

public export
InterpDPRasns : (dpr : DiProAr) -> dprPos dpr -> Type -> Type -> Type
InterpDPRasns dpr i x y = (InterpDPRcontra dpr i x, InterpDPRcovar dpr i y)

public export
InterpDPRproj : (dpr : DiProAr) -> dprPos dpr -> Type
InterpDPRproj dpr i = dprCovar dpr i -> dprContra dpr i

public export
InterpDPRmors : (dpr : DiProAr) -> dprPos dpr -> Type -> Type -> Type
InterpDPRmors dpr i x y = (InterpDPRasns dpr i x y, InterpDPRproj dpr i)

public export
idprmAsns : {dpr : DiProAr} -> {i : dprPos dpr} -> {x, y : Type} ->
  InterpDPRmors dpr i x y -> InterpDPRasns dpr i x y
idprmAsns {dpr} {i} {x} {y} = fst

public export
idprmContra : {dpr : DiProAr} -> {i : dprPos dpr} -> {x, y : Type} ->
  InterpDPRmors dpr i x y -> x -> dprContra dpr i
idprmContra {dpr} {i} {x} {y} = fst . idprmAsns

public export
idprmCovar : {dpr : DiProAr} -> {i : dprPos dpr} -> {x, y : Type} ->
  InterpDPRmors dpr i x y -> dprCovar dpr i -> y
idprmCovar {dpr} {i} {x} {y} = snd . idprmAsns

public export
idprmProj : {dpr : DiProAr} -> {i : dprPos dpr} -> {x, y : Type} ->
  InterpDPRmors dpr i x y -> InterpDPRproj dpr i
idprmProj {dpr} {i} {x} {y} = snd

public export
InterpDPR : DiProAr -> Type -> Type -> Type
InterpDPR dpr x y = (i : dprPos dpr ** InterpDPRmors dpr i x y)

public export
idprPos : {dpr : DiProAr} -> {x, y : Type} -> InterpDPR dpr x y -> dprPos dpr
idprPos {dpr} {x} {y} = DPair.fst

public export
idprMors : {dpr : DiProAr} -> {x, y : Type} ->
  (el : InterpDPR dpr x y) -> InterpDPRmors dpr (idprPos {dpr} {x} {y} el) x y
idprMors {dpr} {x} {y} = DPair.snd

public export
idprAsns : {dpr : DiProAr} -> {x, y : Type} ->
  (el : InterpDPR dpr x y) -> InterpDPRasns dpr (idprPos {dpr} {x} {y} el) x y
idprAsns {dpr} {x} {y} el = fst (idprMors {dpr} {x} {y} el)

public export
idprContraAsn : {dpr : DiProAr} -> {x, y : Type} ->
  (el : InterpDPR dpr x y) -> (x -> dprContra dpr (idprPos {dpr} {x} {y} el))
idprContraAsn {dpr} {x} {y} el = fst (idprAsns {dpr} {x} {y} el)

public export
idprCovarAsn : {dpr : DiProAr} -> {x, y : Type} ->
  (el : InterpDPR dpr x y) -> (dprCovar dpr (idprPos {dpr} {x} {y} el) -> y)
idprCovarAsn {dpr} {x} {y} el = snd (idprAsns {dpr} {x} {y} el)

public export
idprProj : {dpr : DiProAr} -> {x, y : Type} ->
  (el : InterpDPR dpr x y) -> InterpDPRproj dpr (idprPos {dpr} {x} {y} el)
idprProj {dpr} {x} {y} el = snd (idprMors {dpr} {x} {y} el)

public export
idprPosProj : {dpr : DiProAr} -> {x, y : Type} ->
  (el : InterpDPR dpr x y) -> (y -> x) ->
  (dprCovar dpr (idprPos {dpr} {x} {y} el) ->
   dprContra dpr (idprPos {dpr} {x} {y} el))
idprPosProj {dpr} {x} {y} el myx =
  idprContraAsn {dpr} {x} {y} el . myx . idprCovarAsn {dpr} {x} {y} el

public export
InterpDPRcomm : {dpr : DiProAr} -> {x, y : Type} ->
  InterpDPR dpr x y -> (y -> x) -> Type
InterpDPRcomm {dpr} {x} {y} el myx =
  ExtEq
    {a=(dprCovar dpr $ idprPos {dpr} {x} {y} el)}
    {b=(dprContra dpr $ idprPos {dpr} {x} {y} el)}
    (idprPosProj {dpr} {x} {y} el myx)
    (idprProj {dpr} {x} {y} el)

public export
InterpDPRdimap : (dpr : DiProAr) -> TypeDimapSig (InterpDPR dpr)
InterpDPRdimap dpr s t a b mas mtb =
  dpMapSnd $ \i => mapFst (bimap ((|>) mas) ((.) mtb))

public export
InterpDPRtw : DiProAr -> TwArrPreshfOpSig
InterpDPRtw dpr x y myx =
  (el : InterpDPR dpr x y ** InterpDPRcomm {dpr}{x} {y} el myx)

public export
InterpDPRtwMap : (dpr : DiProAr) -> TwArrPreshfOpDimapSig (InterpDPRtw dpr)
InterpDPRtwMap dpr s t a b mba mas mtb
  (el@(i ** ((contra, covar), proj)) ** comm) =
    (InterpDPRdimap dpr s t a b mas mtb el ** comm)

public export
DiProArMonId' : DiProAr
DiProArMonId' = (Unit ** const (Unit, Void))

public export
DiProArIdToIdInterp' :
  TypeProfDiNT (InterpDPR DiProArMonId') HomProf
DiProArIdToIdInterp' x el = id {a=x}

public export
DiProArIdFromIdInterp' :
  TypeProfDiNT HomProf (InterpDPR DiProArMonId')
DiProArIdFromIdInterp' x mxx =
  (() ** ((const (), voidF x), voidF Unit))

public export
DiProArMonComp' : DiProAr -> DiProAr -> DiProAr
DiProArMonComp' (ppos ** pdir) (qpos ** qdir) =
  ((pi : ppos ** qi : qpos **
    (snd (pdir pi) -> fst (pdir pi),
     snd (pdir pi) -> fst (qdir qi),
     snd (qdir qi) -> fst (qdir qi))) **
   \(pi ** qi ** (pproj, pqproj, qproj)) =>
    (fst (pdir pi), snd (qdir qi)))

public export
DiProArInterpCompToCompInterp' : (q, p : DiProAr) ->
  TypeProfDiNT
    (InterpDPR (DiProArMonComp' q p))
    (EndoProfCompose (InterpDPR q) (InterpDPR p))
DiProArInterpCompToCompInterp' (ppos ** pdir) (qpos ** qdir) x
  ((pi ** qi ** (pproj, pqproj, qproj)) ** ((mxp, mqx), qpproj)) =
    (snd (pdir pi) **
     ((pi ** ((mxp, id), pproj)),
      (qi ** ((pqproj, mqx), qproj))))

public export
DiProArInterpCompFromCompInterp' : (q, p : DiProAr) ->
  TypeProfDiNT
    (EndoProfCompose (InterpDPR q) (InterpDPR p))
    (InterpDPR (DiProArMonComp' q p))
DiProArInterpCompFromCompInterp' (ppos ** pdir) (qpos ** qdir) x
  (b ** ((pi ** ((mxp, mpb), pproj)), (qi ** ((mbq, mqx), qproj)))) =
    ((pi ** qi ** (pproj, mbq . mpb, qproj)) **
     ((mxp, mqx), mxp . mqx))

--------------------------------------
---- Composition product (monoid) ----
--------------------------------------

public export
DiProArMonId : DiProAr
DiProArMonId = (Unit ** const (Unit, Void))

public export
DiProArIdToIdInterp :
  TwArrPreshfOpNatTrans (InterpDPRtw DiProArMonId) TwArrPreshfOpId
DiProArIdToIdInterp _ _ _ _ = ()

public export
DiProArIdFromIdInterp :
  TwArrPreshfOpNatTrans TwArrPreshfOpId (InterpDPRtw DiProArMonId)
DiProArIdFromIdInterp x y myx () =
  ((() ** ((const (), voidF y), voidF Unit)) ** \ev => void ev)

public export
DiProArMonComp : DiProAr -> DiProAr -> DiProAr
DiProArMonComp (ppos ** pdir) (qpos ** qdir) =
  ((ppos, qpos) **
   \(pi, qi) =>
    ((fst (pdir pi), fst (qdir qi)),
     Either (snd (pdir pi)) (snd (qdir qi))))

public export
DiProArInterpCompToCompInterp : (q, p : DiProAr) ->
  TwArrPreshfOpNatTrans
    (InterpDPRtw (DiProArMonComp q p))
    (TwArrPreshfOpCompose (InterpDPRtw q) (InterpDPRtw p))
DiProArInterpCompToCompInterp (ppos ** pdir) (qpos ** qdir) x y myx
  (((pi, qi) ** ((dcont, dcov), proj)) ** comm) =
    ((snd (qdir qi), x) **
     ((dcov . Right, id) **
      (((qi ** ((snd . dcont, id), snd . dcont . myx . dcov . Right)) **
        \qd => Refl),
       ((pi ** ((fst . dcont, dcov . Left), fst . dcont . myx . dcov . Left)) **
        \pd => Refl))))

public export
DiProArInterpCompFromCompInterp : (q, p : DiProAr) ->
  TwArrPreshfOpNatTrans
    (TwArrPreshfOpCompose (InterpDPRtw q) (InterpDPRtw p))
    (InterpDPRtw (DiProArMonComp q p))
DiProArInterpCompFromCompInterp (ppos ** pdir) (qpos ** qdir) x y myx
  ((a, b) **
   ((may, mxb) **
    (((qi ** ((mxq, mqa), qasn)) ** qcomm),
     ((pi ** ((mbp, mpy), pasn)) ** pcomm)))) =
      (((pi, qi) **
        ((\ex =>
          (mbp $ mxb ex, mxq ex), eitherElim mpy (may . mqa)),
           eitherElim
            (\pd => (pasn pd, mxq $ myx $ mpy pd))
            (\qd => (mbp $ mxb $ myx $ may $ mqa qd, qasn qd)))) **
       \dd => case dd of
        Left pd => rewrite pcomm pd in Refl
        Right qd => rewrite qcomm qd in Refl)
