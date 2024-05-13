module LanguageDef.QType

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra

------------------------
------------------------
---- Quotient types ----
------------------------
------------------------

---------------------
---- Definitions ----
---------------------

-- A quotient type is a type together with an equivalence relation.
public export
QType : Type
QType = Subset0 Type PrEquivRel

public export
QBase : QType -> Type
QBase = fst0

public export
0 QRel : (0 x : QType) -> PrEquivRel (QBase x)
QRel x = snd0 x

public export
0 QBaseRel : (0 x : QType) -> PrERel (QBase x)
QBaseRel x = fst (QRel x)

public export
0 QRelEquivI : (0 x : QType) -> PrEquivRelI (QBase x) (QBaseRel x)
QRelEquivI x = snd (QRel x)

public export
QTypeFromType : Type -> QType
QTypeFromType x = Element0 x (EqPrEquivRel x)

public export
QFunc : QType -> QType -> Type
QFunc x y = QBase x -> QBase y

public export
0 QPres : (0 x, y : QType) -> SliceObj (QFunc x y)
QPres x y f = PrERelPres {a=(QBase x)} {b=(QBase y)} f (QBaseRel x) (QBaseRel y)

public export
QMorph : QType -> QType -> Type
QMorph x y = Subset0 (QFunc x y) (QPres x y)

public export
QMorphBase : {0 x, y : QType} -> QMorph x y -> QBase x -> QBase y
QMorphBase = fst0

public export
0 QMorphPres : {0 x, y : QType} ->
  (f : QMorph x y) -> QPres x y (QMorphBase {x} {y} f)
QMorphPres = snd0

public export
QMorphFromMorph : {0 x, y : Type} ->
  (x -> y) -> QMorph (QTypeFromType x) (QTypeFromType y)
QMorphFromMorph {x} {y} f = Element0 f $ \ex, ex', xeq => cong f xeq

-----------------------------------------
---- Self-internalization of `QType` ----
-----------------------------------------

-- We can form an equivalence relation on `QType` itself which states that
-- two `QType`s are equivalent if they have the same underlying type and
-- their equivalence relations are equivalent.  This equivalence relation is
-- therefore using the notion of equivalence relation to "hide" the witnesses
-- of equivalence relations themselves.  (It is introducing a proof-irrelevant
-- layer on top of proof-relevant relations.)
public export
data QTEquiv : PrERel QType where
  QTE : {0 x : Type} -> {0 r, r' : PrEquivRel x} ->
    (0 _ : PrRelBiImp (fst r) (fst r')) -> QTEquiv (Element0 x r, Element0 x r')

-- `QTEquiv` is an equivalence relation.
public export
QTEquivEquivI : PrEquivRelI QType QTEquiv
QTEquivEquivI
  (Element0 x r, Element0 x r) (PrErefl _) =
    QTE $ PrEquivRefl (BiImpEquivERel x) (fst r)
QTEquivEquivI
  (Element0 x r, Element0 x r') (PrEsym _ _ (QTE eq)) =
    QTE $ PrEquivSym {ea=(fst r')} {ea'=(fst r)} (BiImpEquivERel x) eq
QTEquivEquivI
  (Element0 x r, Element0 x r')
  (PrEtrans (Element0 x r) (Element0 x r'') (Element0 x r')
    (QTE eq) (QTE eq')) =
      QTE $ PrEquivTrans {ea=(fst r)} {ea'=(fst r'')} {ea''=(fst r')}
        (BiImpEquivERel x) eq eq'

public export
QTEquivEquiv : PrEquivRel QType
QTEquivEquiv = (QTEquiv ** QTEquivEquivI)

-- Between any two `QTEquiv`-equivalent types, there is an isomorphism
-- whose underlying function is the identity.
public export
QTEqIso : {0 x, y : QType} -> QTEquiv (x, y) -> QMorph x y
QTEqIso (QTE imp) = Element0 id $ fst imp

-- Using `QTEquiv`, we can make `QType` itself a `QType`.
public export
QTypeQT : QType
QTypeQT = Element0 QType QTEquivEquiv

-- We can also define an extensional equality on morphisms of `QType`.
public export
0 QMExtEq : {0 x, y : QType} -> PrERel (QMorph x y)
QMExtEq {x} {y} (f, g) =
  PrERelBiPres {a=(QBase x)} {b=(QBase y)}
    (QMorphBase f) (QMorphBase g) (QBaseRel x) (QBaseRel y)

-- Simply a curried `QMExtEq`.
public export
0 QMExtEqC : {0 x, y : QType} -> RelationOn (QMorph x y)
QMExtEqC {x} {y} = curry (QMExtEq {x} {y})

-- `QMExtEq` is an equivalence relation.
public export
0 QMExtEqEquivI : {0 x, y : QType} -> PrEquivRelI (QMorph x y) (QMExtEq {x} {y})
QMExtEqEquivI {x=(Element0 x (rx ** eqx))} {y=(Element0 y (ry ** eqy))}
  (Element0 f fpres, Element0 f fpres) (PrErefl _) =
    fpres
QMExtEqEquivI {x=(Element0 x (rx ** eqx))} {y=(Element0 y (ry ** eqy))}
  (Element0 f fpres, Element0 g gpres) (PrEsym _ _ r) =
    \ex, ex', rex =>
      eqy (f ex, g ex') $ PrEtrans (f ex) (g ex) (g ex') (gpres ex ex' rex)
      $ eqy (f ex, g ex) $ PrEtrans (f ex) (f ex') (g ex)
      (eqy (f ex', g ex) $ PrEsym (g ex) (f ex') $ r ex ex' rex)
      $ fpres ex ex' rex
QMExtEqEquivI {x=(Element0 x (rx ** eqx))} {y=(Element0 y (ry ** eqy))}
  (Element0 f fpres, Element0 g gpres) (PrEtrans _ (Element0 h hpres) _ r r') =
    \ex, ex', rex =>
      eqy (f ex, g ex') $ PrEtrans (f ex) (g ex) (g ex') (gpres ex ex' rex)
      $ eqy (f ex, g ex) $ PrEtrans (f ex) (h ex') (g ex)
      (eqy (h ex', g ex) $ PrEtrans (h ex') (g ex') (g ex)
        (eqy (g ex', g ex) $ PrEsym (g ex) (g ex') $ gpres ex ex' rex)
        (eqy (h ex', g ex') $ PrEtrans (h ex') (h ex) (g ex')
          (r ex ex' rex)
          $ eqy (h ex', h ex) $ PrEsym (h ex) (h ex') $ hpres ex ex' rex))
      $ r' ex ex' rex

public export
0 QMExtEqEquiv : (0 x, y : QType) -> PrEquivRel (QMorph x y)
QMExtEqEquiv x y = (QMExtEq {x} {y} ** QMExtEqEquivI {x} {y})

-- This type represents that two `QType` morphisms agree (up to codomain
-- equivalence) on intensionally equal elements of the domain.
public export
0 QMIntExt : {0 x, y : QType} -> PrERel (QMorph x y)
QMIntExt {x} {y} (f, g) = PrERelIntExt {a=(QBase x)} {b=(QBase y)}
  (QMorphBase f) (QMorphBase g) (QBaseRel y)

-- To show that `QType` morphisms are extensionally equal, we only need to
-- show that they agree (up to codomain equivalence) on _intensionally_
-- equal elements of the domain.
public export
0 MkQMExtEq : {0 x, y : QType} -> {f, g : QMorph x y} ->
  QMIntExt {x} {y} (f, g) -> QMExtEq {x} {y} (f, g)
MkQMExtEq {x} {y} {f} {g} intext =
  PresEqRel
    {a=(QBase x)} {b=(QBase y)}
    {f=(QMorphBase f)} {g=(QMorphBase g)}
    {ra=(QBaseRel x)} {rb=(QRel y)}
    (QMorphPres g) intext

-- In particular, if two `QType` morphisms' base morphisms are extensionally
-- equal, then the `QType` morphisms are equivalent under `QMExtEq`.
public export
0 QMEqFromExt : {0 x, y : QType} -> {f, g : QMorph x y} ->
  ExtEq {a=(QBase x)} {b=(QBase y)}
    (QMorphBase {x} {y} f) (QMorphBase {x} {y} g) ->
  QMExtEq {x} {y} (f, g)
QMEqFromExt {x} {y} {f} {g} eq = MkQMExtEq {x} {y} {f} {g} $
  \_, ea, Refl => rewrite eq ea in PrEquivRefl (snd0 y) $ fst0 g ea

public export
qmId : (a : QType) -> QMorph a a
qmId a = Element0 (id {a=(QBase a)}) $ \_, _ => id

public export
qmComp : {a, b, c : QType} -> QMorph b c -> QMorph a b -> QMorph a c
qmComp {a} {b} {c} g f =
  Element0 (QMorphBase g . QMorphBase f) $ \ea, ea', aeq =>
    QMorphPres g (QMorphBase f ea) (QMorphBase f ea') $ QMorphPres f ea ea' aeq

public export
qmPipe : {a, b, c : QType} -> QMorph a b -> QMorph b c -> QMorph a c
qmPipe {a} {b} {c} = flip $ qmComp {a} {b} {c}

----------------------------------------------------------------------------
---- `QType` as category (with explicit equivalence) internal to `Type` ----
----------------------------------------------------------------------------

public export
0 QTFreeEqRel : (sig : SignatureT QType) -> EqRel (uncurry QMorph sig)
QTFreeEqRel (_, _) =
  MkEq (curry QMExtEq) $ EquivItoIsEquiv QMExtEq QMExtEqEquivI

public export
0 QTidL : {0 a, b : QType} -> (f : QMorph a b) ->
  eqRel (QTFreeEqRel (a, b)) f (qmComp {a} {b} {c=b} (qmId b) f)
QTidL = snd0

public export
0 QTidR : {0 a, b : QType} -> (f : QMorph a b) ->
  eqRel (QTFreeEqRel (a, b)) f (qmComp {a} {b=a} {c=b} f (qmId a))
QTidR = snd0

public export
0 QTassoc : {0 a, b, c, d : QType} ->
  (f : QMorph a b) -> (g : QMorph b c) -> (h : QMorph c d) ->
  eqRel (QTFreeEqRel (a, d))
    (qmComp {a} {b=c} {c=d} h $ qmComp {a} {b} {c} g f)
    (qmComp {a} {b} {c=d} (qmComp {a=b} {b=c} {c=d} h g) f)
QTassoc (Element0 f fpres) (Element0 g gpres) (Element0 h hpres) ea ea' =
  hpres (g $ f ea) (g $ f ea') . gpres (f ea) (f ea') . fpres ea ea'

-- This definition shows that the objects of `QType` with the morphisms
-- of `QMorph` quotiented by `QMExtEq` form a category, with identity and
-- composition given by `qmId` and `qmComp`.

public export
0 QTSCat : SCat
QTSCat = SC
  QType
  (uncurry QMorph)
  qmId
  qmComp
  QTFreeEqRel
  QTidL
  QTidR
  QTassoc

----------------------------------------------------
----------------------------------------------------
---- Universal objects and morphisms in `QType` ----
----------------------------------------------------
----------------------------------------------------

-----------------
---- Initial ----
-----------------

public export
QInitBase : Type
QInitBase = Void

public export
0 QInitBaseRel : PrERel QInitBase
QInitBaseRel (v, v') = void v

public export
0 QInitBaseRelEquivI : PrEquivRelI QInitBase QInitBaseRel
QInitBaseRelEquivI (v, v') _ = void v

public export
0 QInitRel : PrEquivRel QInitBase
QInitRel = (QInitBaseRel ** QInitBaseRelEquivI)

public export
QInit : QType
QInit = Element0 QInitBase QInitRel

public export
qInitBase : (x : QType) -> QInitBase -> QBase x
qInitBase x v = void v

public export
QInitPres : (x : QType) -> QPres QInit x (qInitBase x)
QInitPres x v = void v

public export
qInit : (x : QType) -> QMorph QInit x
qInit x = Element0 (qInitBase x) (QInitPres x)

------------------
---- Terminal ----
------------------

public export
QTermBase : Type
QTermBase = Unit

public export
0 QTermBaseRel : PrERel QTermBase
QTermBaseRel ((), ()) = Unit

public export
0 QTermBaseRelEquivI : PrEquivRelI QTermBase QTermBaseRel
QTermBaseRelEquivI ((), ()) eq = ()

public export
0 QTermRel : PrEquivRel QTermBase
QTermRel = (QTermBaseRel ** QTermBaseRelEquivI)

public export
QTerm : QType
QTerm = Element0 QTermBase QTermRel

public export
qTermBase : (x : QType) -> QBase x -> QTermBase
qTermBase x ex = ()

public export
0 QTermPres : (x : QType) -> QPres x QTerm (qTermBase x)
QTermPres x ex ex' eqx = ()

public export
qTerm : (x : QType) -> QMorph x QTerm
qTerm x = Element0 (qTermBase x) (QTermPres x)

-------------------
---- Coproduct ----
-------------------

public export
QCoproductBase : (x, y : QType) -> Type
QCoproductBase x y = Either (QBase x) (QBase y)

public export
0 QCoproductBaseRel : (x, y : QType) -> PrERel (QCoproductBase x y)
QCoproductBaseRel x y exy =
  case exy of
    (Left ex, Left ex') => QBaseRel x (ex, ex')
    (Right ey, Right ey') => QBaseRel y (ey, ey')
    _ => Void

public export
0 QCoproductBaseRelEquivI : (x, y : QType) ->
  PrEquivRelI (QCoproductBase x y) (QCoproductBaseRel x y)
QCoproductBaseRelEquivI (Element0 x xeq) (Element0 y yeq) exyp exypeq =
  case exyp of
    (Left ex, Left ex') => case exypeq of
      PrErefl _ => PrEquivRefl xeq ex
      PrEsym _ _ r => PrEquivSym xeq r
      PrEtrans _ (Left ex'') _ r r' => PrEquivTrans xeq r r'
      PrEtrans _ (Right ey) _ r r' => void r
    (Left ex, Right ey) => case exypeq of
      PrErefl _ impossible
      PrEsym _ _ r => void r
      PrEtrans _ (Left ex'') _ r r' => void r
      PrEtrans _ (Right ey) _ r r' => void r'
    (Right ey, Left ex) => case exypeq of
      PrErefl _ impossible
      PrEsym _ _ r => void r
      PrEtrans _ (Left ex'') _ r r' => void r'
      PrEtrans _ (Right ey) _ r r' => void r
    (Right ey, Right ey') => case exypeq of
      PrErefl _ => PrEquivRefl yeq ey
      PrEsym _ _ r => PrEquivSym yeq r
      PrEtrans _ (Left ex'') _ r r' => void r'
      PrEtrans _ (Right ey) _ r r' => PrEquivTrans yeq r r'

public export
0 QCoproductRel : (x, y : QType) -> PrEquivRel (QCoproductBase x y)
QCoproductRel x y = (QCoproductBaseRel x y ** QCoproductBaseRelEquivI x y)

public export
QCoproduct : QType -> QType -> QType
QCoproduct x y = Element0 (QCoproductBase x y) (QCoproductRel x y)

public export
qInjLBase : (0 x, y : QType) -> QBase x -> QCoproductBase x y
qInjLBase x y = Left

public export
0 QInjLPres : (0 x, y : QType) -> QPres x (QCoproduct x y) (qInjLBase x y)
QInjLPres x y _ _ = id

public export
qInjL : (0 x, y : QType) -> QMorph x (QCoproduct x y)
qInjL x y = Element0 (qInjLBase x y) (QInjLPres x y)

public export
qInjRBase : (0 x, y : QType) -> QBase y -> QCoproductBase x y
qInjRBase x y = Right

public export
0 QInjRPres : (0 x, y : QType) -> QPres y (QCoproduct x y) (qInjRBase x y)
QInjRPres x y _ _ = id

public export
qInjR : (0 x, y : QType) -> QMorph y (QCoproduct x y)
qInjR x y = Element0 (qInjRBase x y) (QInjRPres x y)

public export
qCaseBase : {0 x, y, z : QType} ->
   QMorph x z -> QMorph y z -> QCoproductBase x y -> QBase z
qCaseBase f g = eitherElim (QMorphBase f) (QMorphBase g)

public export
0 QCasePres : {0 x, y, z : QType} ->
   (f : QMorph x z) -> (g : QMorph y z) ->
   QPres (QCoproduct x y) z (qCaseBase {x} {y} {z} f g)
QCasePres f g (Left ex) (Left ex') = QMorphPres f ex ex'
QCasePres f g (Left ex) (Right ey) = \v => void v
QCasePres f g (Right ey) (Left ex) = \v => void v
QCasePres f g (Right ey) (Right ey') = QMorphPres g ey ey'

public export
qCase : {0 x, y, z : QType} ->
  QMorph x z -> QMorph y z -> QMorph (QCoproduct x y) z
qCase f g = Element0 (qCaseBase f g) (QCasePres f g)

public export
qCoproductBimap : {w, x, y, z : QType} ->
  QMorph w y -> QMorph x z -> QMorph (QCoproduct w x) (QCoproduct y z)
qCoproductBimap {w} {x} {y} {z} f g =
  qCase {x=w} {y=x} {z=(QCoproduct y z)}
    (qmComp (qInjL y z) f) (qmComp (qInjR y z) g)

public export
qCoproductMapFst : {w, x, y : QType} ->
  QMorph w y -> QMorph (QCoproduct w x) (QCoproduct y x)
qCoproductMapFst {w} {x} {y} = flip (qCoproductBimap {w} {x} {y} {z=x}) (qmId x)

public export
qCoproductMapSnd : {w, x, y : QType} ->
  QMorph w x -> QMorph (QCoproduct y w) (QCoproduct y x)
qCoproductMapSnd {w} {x} {y} = qCoproductBimap {w=y} {x=w} {y} {z=x} (qmId y)

-----------------
---- Product ----
-----------------

public export
QProductBase : (x, y : QType) -> Type
QProductBase x y = (QBase x, QBase y)

public export
0 QProductBaseRel : (x, y : QType) -> PrERel (QProductBase x y)
QProductBaseRel x y (pxy, pxy') =
  (QBaseRel x (fst pxy, fst pxy'), QBaseRel y (snd pxy, snd pxy'))

public export
0 QProductBaseRelEquivI : (x, y : QType) ->
  PrEquivRelI (QProductBase x y) (QProductBaseRel x y)
QProductBaseRelEquivI (Element0 x xeq) (Element0 y yeq) ((ex, ey), (ex, ey))
  (PrErefl _) =
    (PrEquivRefl xeq ex, PrEquivRefl yeq ey)
QProductBaseRelEquivI (Element0 x xeq) (Element0 y yeq) ((ex, ey), (ex', ey'))
  (PrEsym _ _ (rx, ry)) =
    (PrEquivSym xeq rx, PrEquivSym yeq ry)
QProductBaseRelEquivI (Element0 x xeq) (Element0 y yeq) ((ex, ey), (ex', ey'))
  (PrEtrans _ (ex'', ey'') _ (rx, ry) (rx', ry')) =
    (PrEquivTrans xeq rx rx', PrEquivTrans yeq ry ry')

public export
0 QProductRel : (x, y : QType) -> PrEquivRel (QProductBase x y)
QProductRel x y = (QProductBaseRel x y ** QProductBaseRelEquivI x y)

public export
QProduct : QType -> QType -> QType
QProduct x y = Element0 (QBase x, QBase y) (QProductRel x y)

public export
qProdIntroBase : {0 x, y, z : QType} ->
  QMorph x y -> QMorph x z -> QBase x -> QProductBase y z
qProdIntroBase {x} {y} {z} f g ex = (QMorphBase f ex, QMorphBase g ex)

public export
0 QProductIntroPres : {0 x, y, z : QType} ->
   (f : QMorph x y) -> (g : QMorph x z) ->
   QPres x (QProduct y z) (qProdIntroBase {x} {y} {z} f g)
QProductIntroPres {x} {y} {z} f g ea ea' rx =
  (snd0 f ea ea' rx, snd0 g ea ea' rx)

public export
qProdIntro : {0 x, y, z : QType} ->
  QMorph x y -> QMorph x z -> QMorph x (QProduct y z)
qProdIntro {x} {y} {z} f g =
  Element0 (qProdIntroBase f g) (QProductIntroPres f g)

public export
qProj1Base : (0 x, y : QType) -> QProductBase x y -> QBase x
qProj1Base x y = fst

public export
0 QProj1Pres : (0 x, y : QType) -> QPres (QProduct x y) x (qProj1Base x y)
QProj1Pres x y _ _ = fst

public export
qProj1 : (0 x, y : QType) -> QMorph (QProduct x y) x
qProj1 x y = Element0 (qProj1Base x y) (QProj1Pres x y)

public export
qProj2Base : (0 x, y : QType) -> QProductBase x y -> QBase y
qProj2Base x y = snd

public export
0 QProj2Pres : (0 x, y : QType) -> QPres (QProduct x y) y (qProj2Base x y)
QProj2Pres x y _ _ = snd

public export
qProj2 : (0 x, y : QType) -> QMorph (QProduct x y) y
qProj2 x y = Element0 (qProj2Base x y) (QProj2Pres x y)

public export
qProductBimap : {w, x, y, z : QType} ->
  QMorph w y -> QMorph x z -> QMorph (QProduct w x) (QProduct y z)
qProductBimap {w} {x} {y} {z} f g =
  qProdIntro (qmComp f (qProj1 w x)) (qmComp g (qProj2 w x))

public export
qProductMapFst : {w, x, y : QType} ->
  QMorph w y -> QMorph (QProduct w x) (QProduct y x)
qProductMapFst {w} {x} {y} = flip (qProductBimap {w} {x} {y} {z=x}) (qmId x)

public export
qProductMapSnd : {w, x, y : QType} ->
  QMorph w x -> QMorph (QProduct y w) (QProduct y x)
qProductMapSnd {w} {x} {y} = qProductBimap {w=y} {x=w} {y} {z=x} (qmId y)

------------------------------------
---- Hom-objects (exponentials) ----
------------------------------------

-- Using the notion of extensional equality on QType morphisms (up to the
-- equivalences embedded within the types), we can define the hom-set of
-- of any two `QType`s within `QType` itself, thus making `QType` Cartesian
-- closed.
public export
QHomBase : (x, y : QType) -> Type
QHomBase = QMorph

public export
0 QHomBaseRel : (x, y : QType) -> PrERel (QHomBase x y)
QHomBaseRel x y = QMExtEq {x} {y}

public export
0 QHomBaseRelEquivI : (x, y : QType) ->
  PrEquivRelI (QHomBase x y) (QHomBaseRel x y)
QHomBaseRelEquivI x y = QMExtEqEquivI {x} {y}

public export
0 QHomRel : (x, y : QType) -> PrEquivRel (QHomBase x y)
QHomRel x y = (QHomBaseRel x y ** QHomBaseRelEquivI x y)

public export
QHom : QType -> QType -> QType
QHom x y = Element0 (QHomBase x y) (QHomRel x y)

public export
QExp : QType -> QType -> QType
QExp = flip QHom

public export
qHomEvalBase : (x, y : QType) -> QBase (QProduct (QHom x y) x) -> QBase y
qHomEvalBase x y (Element0 f fpres, ex) = f ex

public export
0 QHomEvalPres : (x, y : QType) ->
  QPres (QProduct (QHom x y) x) y (qHomEvalBase x y)
QHomEvalPres (Element0 x xeq) (Element0 y yeq)
  (Element0 f fpres, ex) (Element0 g gpres, ex') (fgpres, rx) =
    fgpres ex ex' rx

public export
qHomEval : (x, y : QType) -> QMorph (QProduct (QHom x y) x) y
qHomEval x y = Element0 (qHomEvalBase x y) (QHomEvalPres x y)

public export
qHomCurryBase : {0 x, y, z : QType} ->
  QMorph (QProduct x y) z -> QBase x -> QBase (QHom y z)
qHomCurryBase {x=(Element0 x xeq)} {y=(Element0 y yeq)} {z=(Element0 z zeq)}
  (Element0 f fpres) ex =
    Element0
      (curry f ex)
      $ \ey, ey', ry => fpres (ex, ey) (ex, ey') (PrEquivRefl xeq ex, ry)

public export
0 QHomCurryPres : {0 x, y, z : QType} ->
  (f : QMorph (QProduct x y) z) ->
  QPres x (QHom y z) (qHomCurryBase {x} {y} {z} f)
QHomCurryPres {x=(Element0 x xeq)} {y=(Element0 y yeq)} {z=(Element0 z zeq)}
  (Element0 f fpres) ex ex' rx ey ey' ry =
    fpres (ex, ey) (ex', ey') (rx, ry)

public export
qHomCurry : {0 x, y, z : QType} ->
  QMorph (QProduct x y) z -> QMorph x (QHom y z)
qHomCurry {x} {y} {z} f = Element0 (qHomCurryBase f) (QHomCurryPres f)

public export
qHomUncurry : {x, y, z : QType} ->
  QMorph x (QHom y z) -> QMorph (QProduct x y) z
qHomUncurry {x} {y} {z} f = qmComp (qHomEval y z) (qProductMapFst f)

----------------------------------------------
---- Quotation (derived from hom-objects) ----
----------------------------------------------

-- A global element of a `QType` is a morphism from the terminal object.
public export
QGElem : QType -> Type
QGElem = QMorph QTerm

-- We shall refer to a global element of a hom-object as a "quotation".
public export
QQuotation : QType -> QType -> Type
QQuotation = QGElem .* QHom

public export
qQuote : {x, y : QType} -> QMorph x y -> QQuotation x y
qQuote {x} {y} = qHomCurry {x=QTerm} . flip qmComp (qProj2 QTerm x)

public export
qUnquote : {x, y : QType} -> QQuotation x y -> QMorph x y
qUnquote {x} {y} =
  qmPipe {b=(QProduct QTerm x)} (qProdIntro (qTerm x) (qmId x))
  .  qHomUncurry {x=QTerm}

--------------------
---- Equalizers ----
--------------------

public export
QEqualizerBase : {x : QType} -> {0 y : QType} ->
  QMorph x y -> QMorph x y -> Type
QEqualizerBase {x} {y} f g =
  Subset0 (QBase x) $ \ex => QBaseRel y (QMorphBase f ex, QMorphBase g ex)

public export
0 QEqualizerBaseRel : {0 x, y : QType} ->
  (f, g : QMorph x y) -> PrERel (QEqualizerBase {x} {y} f g)
QEqualizerBaseRel {x} {y} f g (Element0 ex fgeq, Element0 ex' fgeq') =
  QBaseRel x (ex, ex')

public export
0 QEqualizerBaseRelEquivI : {0 x, y : QType} ->
  (f, g : QMorph x y) ->
  PrEquivRelI (QEqualizerBase {x} {y} f g) (QEqualizerBaseRel {x} {y} f g)
QEqualizerBaseRelEquivI {x} {y} f g (Element0 ex fgeq, Element0 ex' fgeq') xeq =
  case xeq of
    PrErefl _ => PrEquivRefl (QRel x) ex
    PrEsym _ _ r => PrEquivSym (QRel x) r
    PrEtrans _ (Element0 ex'' rfg) _ r r' => PrEquivTrans (QRel x) r r'

public export
0 QEqualizerRel : {0 x, y : QType} ->
  (f, g : QMorph x y) -> PrEquivRel (QEqualizerBase {x} {y} f g)
QEqualizerRel {x} {y} f g =
  (QEqualizerBaseRel {x} {y} f g ** QEqualizerBaseRelEquivI {x} {y} f g)

public export
QEqualizer : {x : QType} -> {0 y : QType} ->
  QMorph x y -> QMorph x y -> QType
QEqualizer {x} {y} f g =
  Element0 (QEqualizerBase {x} {y} f g) (QEqualizerRel {x} {y} f g)

public export
qEqIntroBase : {0 w, x, y : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph w x) ->
  QMExtEq {x=w} {y}
    (qmComp {a=w} {b=x} {c=y} f h, qmComp {a=w} {b=x} {c=y} g h) ->
  QBase w -> QEqualizerBase {x} {y} f g
qEqIntroBase {w} {x} {y} {f} {g} h eq ew =
  Element0 (fst0 h ew) $ eq ew ew $ PrEquivRefl (QRel w) ew

public export
0 QEqIntroPres : {0 w, x, y : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph w x) ->
  (eq : QMExtEq {x=w} {y}
    (qmComp {a=w} {b=x} {c=y} f h, qmComp {a=w} {b=x} {c=y} g h)) ->
  QPres w (QEqualizer {x} {y} f g) (qEqIntroBase {w} {x} {y} {f} {g} h eq)
QEqIntroPres {w} {x} {y} {f} {g} h eq ew ew' rw = snd0 h ew ew' rw

public export
qEqIntro : {0 w, x, y : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph w x) ->
  QMExtEq {x=w} {y}
    (qmComp {a=w} {b=x} {c=y} f h, qmComp {a=w} {b=x} {c=y} g h) ->
  QMorph w (QEqualizer {x} {y} f g)
qEqIntro {f} {g} h eq =
  Element0 (qEqIntroBase {f} {g} h eq) (QEqIntroPres {f} {g} h eq)

public export
qEqElimBase : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QEqualizerBase {x} {y} f g -> QBase x
qEqElimBase {x} {y} f g = fst0

public export
0 QEqElimPres : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QPres (QEqualizer {x} {y} f g) x (qEqElimBase {x} {y} f g)
QEqElimPres f g (Element0 ex fgeq) (Element0 ex' fgeq') = id

public export
qEqElim : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QMorph (QEqualizer {x} {y} f g) x
qEqElim f g = Element0 (qEqElimBase f g) (QEqElimPres f g)

public export
0 QEqElimEq : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QMExtEq {x=(QEqualizer {x} {y} f g)} {y}
    (qmComp {a=(QEqualizer {x} {y} f g)} {b=x} {c=y} f (qEqElim {x} {y} f g),
     qmComp {a=(QEqualizer {x} {y} f g)} {b=x} {c=y} g (qEqElim {x} {y} f g))
QEqElimEq {x} {y} f g (Element0 ex fgeq) (Element0 ex' fgeq') rx =
  PrEquivTrans (snd0 y) fgeq' $ snd0 f ex ex' rx

----------------------
---- Coequalizers ----
----------------------

public export
QCoequalizerBase : {0 x : QType} -> {y : QType} ->
  QMorph x y -> QMorph x y -> Type
QCoequalizerBase {x} {y} f g = QBase y

public export
0 QCoequalizerBaseRel : {0 x, y : QType} ->
  (f, g : QMorph x y) -> PrERel (QCoequalizerBase {x} {y} f g)
QCoequalizerBaseRel {x} {y} f g =
  CoeqFreeEquivRelF {x=(QBase x)} {y=(QBase y)}
    (QMorphBase f) (QMorphBase g) (QBaseRel x) (QBaseRel y)

public export
0 QCoequalizerBaseRelEquivI : {0 x, y : QType} ->
  (f, g : QMorph x y) ->
  PrEquivRelI (QCoequalizerBase {x} {y} f g) (QCoequalizerBaseRel {x} {y} f g)
QCoequalizerBaseRelEquivI {x} {y} f g =
  CoeqFreeEquivRelI {x=(QBase x)} {y=(QBase y)}
    (QMorphBase f) (QMorphBase g) (QBaseRel x) (QBaseRel y)

public export
0 QCoequalizerRel : {0 x, y : QType} ->
  (f, g : QMorph x y) -> PrEquivRel (QCoequalizerBase {x} {y} f g)
QCoequalizerRel {x} {y} f g =
  (QCoequalizerBaseRel {x} {y} f g ** QCoequalizerBaseRelEquivI {x} {y} f g)

public export
QCoequalizer : {0 x : QType} -> {y : QType} ->
  QMorph x y -> QMorph x y -> QType
QCoequalizer {x} {y} f g =
  Element0 (QCoequalizerBase {x} {y} f g) (QCoequalizerRel {x} {y} f g)

public export
qCoeqIntroBase : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QBase y -> QCoequalizerBase {x} {y} f g
qCoeqIntroBase {x} {y} f g = id

public export
0 QCoeqIntroPres : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QPres y (QCoequalizer {x} {y} f g) (qCoeqIntroBase {x} {y} f g)
QCoeqIntroPres {x} {y} f g ew ew' = InSlFv . Right

public export
qCoeqIntro : {0 x, y : QType} -> (0 f, g : QMorph x y) ->
  QMorph y (QCoequalizer {x} {y} f g)
qCoeqIntro f g = Element0 (qCoeqIntroBase f g) (QCoeqIntroPres f g)

public export
qCoeqElimBase : {0 x, y, z : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph y z) ->
  QMExtEq {x} {y=z}
    (qmComp {a=x} {b=y} {c=z} h f, qmComp {a=x} {b=y} {c=z} h g) ->
  QCoequalizerBase {x} {y} f g -> QBase z
qCoeqElimBase {x} {y} {z} {f} {g} h eq ey = fst0 h ey

public export
0 QCoeqElimPresSubst : {0 x, y, z : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph y z) ->
  (eq : QMExtEq {x} {y=z}
    (qmComp {a=x} {b=y} {c=z} h f, qmComp {a=x} {b=y} {c=z} h g)) ->
  SliceMorphism {a=(ProductMonad $ QBase y)}
    (CoeqRelF
      (QMorphBase {x} {y} f) (QMorphBase {x} {y} g) (QBaseRel x) (QBaseRel y))
    (QBaseRel z . mapHom (QMorphBase {x=y} {y=z} h))
QCoeqElimPresSubst {x} {y} {z} {f} {g} h hcoeq (ey, ey')
  (Left (Evidence0 (ex, ex') (rx, feq, geq))) =
    rewrite sym feq in rewrite sym geq in
    hcoeq ex ex' rx
QCoeqElimPresSubst {x} {y} {z} {f} {g} h hcoeq (ey, ey')
  (Right yeq) =
    QMorphPres h ey ey' yeq

public export
0 QCoeqElimPresAlg : {0 x, y, z : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph y z) ->
  (eq : QMExtEq {x} {y=z}
    (qmComp {a=x} {b=y} {c=z} h f, qmComp {a=x} {b=y} {c=z} h g)) ->
  SliceAlg {a=(ProductMonad $ QBase y)} (PrEquivF {a=(QBase y)})
    (QBaseRel z . mapHom (QMorphBase {x=y} {y=z} h))
QCoeqElimPresAlg {x} {y} {z} {f} {g} h hcoeq (ey, ey') eqy =
  QRelEquivI z (mapHom (QMorphBase {x=y} {y=z} h) (ey, ey')) $
    prEquivMapHom {r=(QBaseRel z)} {f=(QMorphBase h)} (ey, ey') eqy

public export
0 QCoeqElimPres : {0 x, y, z : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph y z) ->
  (eq : QMExtEq {x} {y=z}
    (qmComp {a=x} {b=y} {c=z} h f, qmComp {a=x} {b=y} {c=z} h g)) ->
  QPres (QCoequalizer {x} {y} f g) z (qCoeqElimBase {x} {y} {z} {f} {g} h eq)
QCoeqElimPres {x} {y} {z} {f} {g} h hcoeq ey ey' =
  freePrEquivEval {a=(QBase y)}
    (CoeqRelF (QMorphBase f) (QMorphBase g) (QBaseRel x) (QBaseRel y))
    (QBaseRel z . mapHom (QMorphBase h))
    (QCoeqElimPresSubst h hcoeq)
    (QCoeqElimPresAlg h hcoeq)
    (ey, ey')

public export
qCoeqElim : {0 x, y, z : QType} -> {0 f, g : QMorph x y} ->
  (h : QMorph y z) ->
  QMExtEq {x} {y=z}
    (qmComp {a=x} {b=y} {c=z} h f, qmComp {a=x} {b=y} {c=z} h g) ->
  QMorph (QCoequalizer {x} {y} f g) z
qCoeqElim {x} {y} {z} {f} {g} h eq =
  Element0 (qCoeqElimBase {f} {g} h eq) (QCoeqElimPres {f} {g} h eq)

---------------------------------------------
---------------------------------------------
---- Predicates on and slices of `QType` ----
---------------------------------------------
---------------------------------------------

-----------------------------
---- In categorial style ----
-----------------------------

public export
QSliceObjBase : QType -> Type
QSliceObjBase a = Subset0 QType (flip QMorph a)

public export
0 QSliceTotRel : {a : QType} -> PrERel (QSliceObjBase a)
QSliceTotRel (sl, sl') = QTEquiv (fst0 sl, fst0 sl')

public export
0 QSliceProjRel : {a : QType} -> (sl, sl' : QSliceObjBase a) ->
  (0 _ : QSliceTotRel {a} (sl, sl')) -> Type
QSliceProjRel sl sl' qte = QMExtEq (snd0 sl, qmComp (snd0 sl') $ QTEqIso qte)

public export
0 QSliceObjRel : {a : QType} -> PrERel (QSliceObjBase a)
QSliceObjRel (sl, sl') = Exists0 (QSliceTotRel (sl, sl')) (QSliceProjRel sl sl')

public export
0 QSliceObjRelEquivI : {a : QType} ->
  PrEquivRelI (QSliceObjBase a) (QSliceObjRel {a})
QSliceObjRelEquivI {a=(Element0 a (aeq ** aequiv))}
  (Element0 (Element0 x (xeq ** xequiv)) (Element0 f fpres),
   Element0 (Element0 x' (xeq' ** xequiv')) (Element0 f' fpres'))
  eq =
    case eq of
      PrErefl _ =>
        Evidence0
          (QTE (\_, _ => id, \_, _ => id))
          fpres
      PrEsym _ _ (Evidence0 (QTE (impl, impr)) gpres) =>
        Evidence0
          (QTE (impr, impl))
          $ \ea, ea', eaeq =>
            aequiv (f ea, f' ea') $
              PrEtrans (f ea) (f' ea) (f' ea')
                (fpres' ea ea' $ impr ea ea' eaeq)
                $ aequiv (f ea, f' ea) $
                  PrEtrans (f ea) (f ea') (f' ea)
                    (aequiv (f ea', f' ea) $ PrEsym (f' ea) (f ea') $
                      gpres ea ea' $ impr ea ea' eaeq)
                    (fpres ea ea' eaeq)
      PrEtrans _ (Element0 (Element0 z (zeq ** zequiv)) (Element0 g gpres)) _
        (Evidence0 (QTE (impl, impr)) gfpres)
        (Evidence0 (QTE (impl', impr')) fgpres) =>
          Evidence0
            (QTE
              (\ea, ea' => impl ea ea' . impl' ea ea',
               \ea, ea' => impr' ea ea' . impr ea ea'))
            $ \ea, ea', eaeq =>
              aequiv (f ea, f' ea') $
                PrEtrans (f ea) (g ea) (f' ea')
                  (gfpres ea ea' $ impl' ea ea' eaeq)
                  $ aequiv (f ea, g ea) $
                    PrEtrans (f ea) (g ea') (g ea)
                      (aequiv (g ea', g ea) $ PrEsym (g ea) (g ea') $
                        gpres ea ea' $ impl' ea ea' eaeq)
                      $ fgpres ea ea' eaeq

public export
0 QSliceObjRelEquiv : {a : QType} -> PrEquivRel (QSliceObjBase a)
QSliceObjRelEquiv {a} = (QSliceObjRel {a} ** QSliceObjRelEquivI {a})

public export
QSliceObj : QType -> QType
QSliceObj a = Element0 (QSliceObjBase a) (QSliceObjRelEquiv {a})

---------------------------------
---- In dependent-type style ----
---------------------------------

-- A predicate is a dependent type in the type-theoretic view.  In the
-- categorial view, it is a discrete presheaf, which is the opposite category
-- of a discrete copresheaf, which is equivalent to a slice category.
-- So the category of predicates on a `QType` is equivalent to the opposite
-- of the slice category of `QType` over that `QType`.
public export
QPred : QType -> QType
QPred a = QHom a QTypeQT

----------------------------
----------------------------
---- Quivers in `QType` ----
----------------------------
----------------------------

-- A quiver in `QType` is a functor from the walking quiver -- a generic
-- figure with two objects and two parallel non-identity morphisms -- to
-- `QType`.  Such a functor is determined by a choice of two `QType`s and
-- two parallel `QMorph`s between them.
--
-- However, there is another way of looking at this:  when we view the
-- functor as contravariant, so that it is a presheaf rather than a
-- copresheaf -- a functor from the _opposite_ category of the walking quiver
-- to `QType` -- it is equivalent to a `QType` together with a `QType`
-- dependent on pairs of the first `QType`, or, to put it another way, a
-- `QType` together with a slice over its product.
public export
QQuivEdge : QType -> QType
QQuivEdge vert = QPred $ QProduct vert vert
