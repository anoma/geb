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
import public LanguageDef.PolySliceCat
import public LanguageDef.IntDisheafCat

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

--------------------------------------------------------
--------------------------------------------------------
---- Forms and characterizations of arrow morphisms ----
--------------------------------------------------------
--------------------------------------------------------

-- Given arrows `e -> b` and `e' -> b'`, there are several ways we
-- could interpret them and define morphisms between them.  Here we
-- illustrate a few, in some cases with multiple characterizations.

-- We have already shown that (covariant) bundles in `Type` are
-- equivalent to Dirichlet functors with their natural transformations.
-- Here we show another characterization using the adjunction between
-- dependent sum (sigma) and base change.
public export
DirichNTasBC : (p, q : MLDirichCatObj) ->
  MLDirichCatMor p q =
  (onpos : dfPos p -> dfPos q **
   SliceMorphism {a=(dfPos p)}
    (dfDir p)
    (SliceFuncCat.BaseChangeF onpos (dfDir q)))
DirichNTasBC p q = Refl

public export
DirichNTadj : IntMorSig MLDirichCatObj
DirichNTadj p q =
  (onpos : dfPos p -> dfPos q **
   SliceMorphism {a=(dfPos q)} (SliceFibSigmaF onpos (dfDir p)) (dfDir q))

public export
DirichNTfromAdj : (p, q : MLDirichCatObj) ->
  DirichNTadj p q -> MLDirichCatMor p q
DirichNTfromAdj p q alpha =
  (fst alpha ** \pi, pd => snd alpha (fst alpha pi) (SFS pi pd))

public export
DirichNTtoAdj : (p, q : MLDirichCatObj) ->
  MLDirichCatMor p q -> DirichNTadj p q
DirichNTtoAdj p q alpha =
  (fst alpha ** \qi, (SFS pi pd) => snd alpha pi pd)

-- We have seen that contravariant bundles in `Type` are equivalent to
-- polynomial functors with their natural transformations.
-- Here we show another characterization using the adjunction between
-- base change and dependent product (pi).
public export
PolyNTasBC : (p, q : MLPolyCatObj) ->
  MLPolyCatMor p q =
  (onpos : pfPos p -> pfPos q **
   SliceMorphism {a=(pfPos p)}
    (SliceFuncCat.BaseChangeF onpos (pfDir {p=q}))
    (pfDir {p}))
PolyNTasBC p q = Refl

public export
PolyNTadj : IntMorSig MLPolyCatObj
PolyNTadj p q =
  (onpos : pfPos p -> pfPos q **
   SliceMorphism {a=(pfPos q)} (pfDir {p=q}) (SliceFibPiF onpos (pfDir {p})))

public export
PolyNTfromAdj : (p, q : MLPolyCatObj) ->
  PolyNTadj p q -> MLPolyCatMor p q
PolyNTfromAdj p q alpha =
  (fst alpha ** \pi, qd => snd alpha (fst alpha pi) qd (SFS pi ()))

public export
PolyNTtoAdj : (p, q : MLPolyCatObj) ->
  MLPolyCatMor p q -> PolyNTadj p q
PolyNTtoAdj p q alpha =
  (fst alpha ** \qi, qd, (SFS pi ()) => snd alpha pi qd)

-- We can characterize a twisted-arrow morphism as a slice morphism
-- to a post-composition (i.e. a sigma type).
public export
TwArrM : {e, b, e', b' : Type} -> (e -> b) -> (e' -> b') -> Type
TwArrM {e} {b} {e'} {b'} m m' =
  (ms : (e' -> e, b -> b') ** ExtEq {a=e'} {b=b'} (snd ms . m . fst ms) m')

public export
TwArrMcsl : {e, b, e', b' : Type} -> (e -> b) -> (e' -> b') -> Type
TwArrMcsl {e} {b} {e'} {b'} m m' =
  (mb : b -> b' **
   CSliceMorphism {c=b'} (e' ** m') (CSSigma {c=b} {d=b'} mb (e ** m)))

public export
TwArrMtoCSl : {e, b, e', b' : Type} -> (m : e -> b) -> (m' : e' -> b') ->
  TwArrM {e} {b} {e'} {b'} m m' -> TwArrMcsl {e} {b} {e'} {b'} m m'
TwArrMtoCSl {e} {b} {e'} {b'} m m' ((me, mb) ** comm) =
  (mb ** Element0 me (\ele' => sym $ comm ele'))

public export
TwArrMfromCSl : {e, b, e', b' : Type} -> (m : e -> b) -> (m' : e' -> b') ->
  TwArrMcsl {e} {b} {e'} {b'} m m' -> TwArrM {e} {b} {e'} {b'} m m'
TwArrMfromCSl {e} {b} {e'} {b'} m m' (mb ** Element0 me comm) =
  ((me, mb) ** \ele' => sym $ comm ele')

-- A morphism into a sigma type may be factored into two components:
-- one morphism into the first component and a dependent morphism into
-- the second component.
public export
TwArrMsl : {b, b' : Type} -> SliceObj b -> SliceObj b' -> Type
TwArrMsl {b} {b'} sl sl' =
  (mb : b -> b' **
   m1 : (eb' : b') -> sl' eb' -> PreImage {a=b} {b=b'} mb eb' **
   (eb' : b') -> (esl' : sl' eb') -> sl (fst0 $ m1 eb' esl'))

public export
TwArrMtoSl : {e, b, e', b' : Type} -> (m : e -> b) -> (m' : e' -> b') ->
  TwArrM {e} {b} {e'} {b'} m m' ->
  TwArrMsl {b} {b'}
    (SliceFromCSlice {c=b} (e ** m))
    (SliceFromCSlice {c=b'} (e' ** m'))
TwArrMtoSl {e} {b} {e'} {b'} m m' ((me, mb) ** mcomm) =
  (mb **
   \eb', (Element0 ele' ecomm) =>
    Element0 (m $ me ele') (trans (mcomm ele') ecomm) **
   \eb', (Element0 ele' ecomm) => Element0 (me ele') Refl)

public export
TwArrMfromSl : {e, b, e', b' : Type} -> (m : e -> b) -> (m' : e' -> b') ->
  TwArrMsl {b} {b'}
    (SliceFromCSlice {c=b} (e ** m))
    (SliceFromCSlice {c=b'} (e' ** m')) ->
  TwArrM {e} {b} {e'} {b'} m m'
TwArrMfromSl {e} {b} {e'} {b'} m m' (mb ** m1 ** m2) =
  ((\ele' => fst0 $ m2 (m' ele') (Element0 ele' Refl), mb) **
   \ele' =>
    rewrite snd0 $ m2 (m' ele') (Element0 ele' Refl) in
    rewrite snd0 $ m1 (m' ele') (Element0 ele' Refl) in
    Refl)

public export
TwArrCSltoSl : {e, b, e', b' : Type} -> (m : e -> b) -> (m' : e' -> b') ->
  TwArrMcsl {e} {b} {e'} {b'} m m' ->
  TwArrMsl {b} {b'}
    (SliceFromCSlice {c=b} (e ** m))
    (SliceFromCSlice {c=b'} (e' ** m'))
TwArrCSltoSl {e} {b} {e'} {b'} m m' csl =
  TwArrMtoSl m m' (TwArrMfromCSl m m' csl)

public export
TwArrCSlfromSl : {e, b, e', b' : Type} -> (m : e -> b) -> (m' : e' -> b') ->
  TwArrMsl {b} {b'}
    (SliceFromCSlice {c=b} (e ** m))
    (SliceFromCSlice {c=b'} (e' ** m')) ->
  TwArrMcsl {e} {b} {e'} {b'} m m'
TwArrCSlfromSl {e} {b} {e'} {b'} m m' sl =
  TwArrMtoCSl m m' (TwArrMfromSl m m' sl)

------------------------------------------
------------------------------------------
---- PRA functors on `MLDirichCatObj` ----
------------------------------------------
------------------------------------------

public export
MLDirichF1_T1 : Type
MLDirichF1_T1 = Type

-- Equivalent to a mapping from positions of `T1` to `MLDirichCatObj`,
-- this determines the components of the `E_T` functor when evaluated
-- at the non-dependent object of the interval category (which we call
-- `ET1`).
public export
MLDirichF1_ET : SliceObj MLDirichF1_T1
MLDirichF1_ET t1pos =
  (et1pos : SliceObj t1pos ** (it1 : t1pos) -> SliceObj (et1pos it1))

public export
MLDirichF1 : Type
MLDirichF1 = DPair MLDirichF1_T1 MLDirichF1_ET

public export
mldPos1 : MLDirichF1 -> MLDirichF1_T1
mldPos1 = DPair.fst

public export
mldDir1 : (f1 : MLDirichF1) -> MLDirichF1_ET (mldPos1 f1)
mldDir1 = DPair.snd

public export
mldET1Pos : (f1 : MLDirichF1) -> mldPos1 f1 -> Type
mldET1Pos f1 = DPair.fst $ mldDir1 f1

public export
mldPF1 : MLDirichF1 -> PolyFunc
mldPF1 p = (mldPos1 p ** mldET1Pos p)

public export
mldET1Dir : (f1 : MLDirichF1) -> (i : mldPos1 f1) -> mldET1Pos f1 i -> Type
mldET1Dir f1 = DPair.snd $ mldDir1 f1

public export
mldET1 : (f1 : MLDirichF1) -> mldPos1 f1 -> MLDirichCatObj
mldET1 f1 it1 = (mldET1Pos f1 it1 ** mldET1Dir f1 it1)

public export
InterpMLDirichF1 : MLDirichF1 -> MLDirichCatObj -> Type
InterpMLDirichF1 f1 p = (i : mldPos1 f1 ** DirichNatTrans (mldET1 f1 i) p)

public export
0 MLF1elExtEq : {f1 : MLDirichF1} -> {p : MLDirichCatObj} ->
  IntMorSig (InterpMLDirichF1 f1 p)
MLF1elExtEq {f1} {p} el el' =
  (fsteq :
    fst el = fst el' **
   onposeq :
    (i : mldET1Pos f1 (fst el)) ->
      fst (snd el) i = fst (snd el') (rewrite sym fsteq in i) **
   (i : mldET1Pos f1 (fst el)) -> (d : mldET1Dir f1 (fst el) i) ->
    snd (snd el) i d =
    (rewrite onposeq i in
     snd (snd el') (rewrite sym fsteq in i) (rewrite sym fsteq in d)))

public export
InterpMLDirichF1map : (f1 : MLDirichF1) -> {p, q : MLDirichCatObj} ->
  DirichNatTrans p q -> InterpMLDirichF1 f1 p -> InterpMLDirichF1 f1 q
InterpMLDirichF1map f1 {p} {q} alpha =
  dpMapSnd $ \pi => dntVCatComp {p=(mldET1 f1 pi)} alpha

-- A natural transformation from a representable, i.e. an `MLDirichF1`
-- with only one position, to `q` corresponds by the Yoneda lemma to an
-- element of `q` applied to the representing functor.
--
-- `MLDirichF1` is a coproduct of representables.  A natural
-- transformation from a coproduct is a product of natural transformations
-- from the components of the coproduct.
--
-- Putting those two together we can obtain the following formula
-- for a natural transformation between `MLDirichF1`s:
--
--  MLDirichF1NT p q = (pi : mldPos1 p) -> InterpMLDirichF1 q (mldET1 p pi)
--
-- Because that is a function into a (dependent) pair, we can break it
-- up into two components.  Furthermore, because the second component of
-- `InterpMLDirichF1` is also a dependent pair, we can break that up and
-- curry `MLDirichF1NT` into _three_ components.
public export
MLDirichF1NT : IntMorSig MLDirichF1
MLDirichF1NT p q =
  (onpos1 : mldPos1 p -> mldPos1 q **
   onpos2 : (pi : mldPos1 p) -> mldET1Pos q (onpos1 pi) -> mldET1Pos p pi **
   (pi : mldPos1 p) -> (qi : mldET1Pos q (onpos1 pi)) ->
    mldET1Dir q (onpos1 pi) qi -> mldET1Dir p pi (onpos2 pi qi))

public export
mld1pnt : {p, q : MLDirichF1} ->
  MLDirichF1NT p q -> PolyNatTrans (mldPF1 p) (mldPF1 q)
mld1pnt {p} {q} alpha = (fst alpha ** fst (snd alpha))

public export
mld1dnt : {p, q : MLDirichF1} -> (alpha : MLDirichF1NT p q) ->
  (pi : mldPos1 p) -> DirichNatTrans (mldET1 q (fst alpha pi)) (mldET1 p pi)
mld1dnt {p} {q} alpha pi = (fst (snd alpha) pi ** snd (snd alpha) pi)

public export
InterpMLDirichF1NT : {p1, q1 : MLDirichF1} -> MLDirichF1NT p1 q1 ->
  (r : MLDirichCatObj) -> InterpMLDirichF1 p1 r -> InterpMLDirichF1 q1 r
InterpMLDirichF1NT {p1} {q1} alpha r =
  dpBimap (fst alpha) $
    \pi =>
      flip (dntVCatComp {p=(mldET1 q1 (fst alpha pi))} {q=(mldET1 p1 pi)})
        (mld1dnt alpha pi)

public export
0 MLDF1NTextEq : {p, q : MLDirichF1} -> IntMorSig (MLDirichF1NT p q)
MLDF1NTextEq {p} {q}
  (onpos1 ** onpos2 ** ondir)
  (onpos1' ** onpos2' ** ondir') =
    (pos1eq :
      ExtEq onpos1 onpos1' **
     pos2eq :
      (pi : mldPos1 p) -> (qi : mldET1Pos q (onpos1 pi)) ->
      onpos2 pi qi = onpos2' pi (rewrite sym (pos1eq pi) in qi) **
     (pi : mldPos1 p) -> (qi : mldET1Pos q (onpos1 pi)) ->
      (d : mldET1Dir q (onpos1 pi) qi) ->
      ondir pi qi d =
      (rewrite pos2eq pi qi in
       ondir'
        pi
        (rewrite sym (pos1eq pi) in qi)
        (rewrite sym (pos1eq pi) in d)))

public export
mldF1NTid : (p : MLDirichF1) -> MLDirichF1NT p p
mldF1NTid p = (id ** \_ => id ** \_, _ => id)

public export
mldF1NTvcomp : {p, q, r : MLDirichF1} ->
  MLDirichF1NT q r -> MLDirichF1NT p q -> MLDirichF1NT p r
mldF1NTvcomp {p} {q} {r} beta alpha =
  (fst beta . fst alpha **
   (\pi, rd1 =>
    fst (snd alpha) pi $ fst (snd beta) (fst alpha pi) rd1) **
   (\pi, rd1, rd2 =>
    snd (snd alpha) pi
      (fst (snd beta) (fst alpha pi) rd1)
      (snd (snd beta) (fst alpha pi) rd1 rd2)))

-- An `MLDirichF1` defines a copresheaf on `MLDirichCatObj`.
-- To define an endofunctor on `MLDirichCatObj`, we further
-- need to define a functor on `MLDirichCatObj` whose output
-- depends on the output of an `MLDirichF1` -- that will give
-- us for each `MLDirichCatObj` a type and a type dependent on
-- it, which in turn defines a new `MLDirichCatObj`.  A functor
-- dependent on the output of an `MLDirichF1` is a copresheaf
-- on the category of elements of the `MLDirichF1`.  And a
-- copresheaf on the category of elements is in turn equivalent
-- to a slice over the `MLDirichF1` (within the category of
-- copresheaves on `MLDirichCatObj`), which is defined as another
-- `MLDirichF1` together with a natural transformation from that
-- to the `MLDirichF1` being sliced over (on which we are trying
-- to define a copresheaf).

public export
MLDirichF1Sl : MLDirichF1 -> Type
MLDirichF1Sl base = (tot : MLDirichF1 ** MLDirichF1NT tot base)

public export
mldsTot : {base : MLDirichF1} -> MLDirichF1Sl base -> MLDirichF1
mldsTot {base} = DPair.fst

public export
interpMLDStot : {base : MLDirichF1} -> MLDirichF1Sl base ->
  MLDirichCatObj -> Type
interpMLDStot {base} sl = InterpMLDirichF1 (mldsTot {base} sl)

public export
mldsProj : {base : MLDirichF1} -> (sl : MLDirichF1Sl base) ->
  MLDirichF1NT (mldsTot {base} sl) base
mldsProj {base} = DPair.snd

public export
interpMLDSproj : {base : MLDirichF1} -> (sl : MLDirichF1Sl base) ->
  (p : MLDirichCatObj) -> interpMLDStot {base} sl p -> InterpMLDirichF1 base p
interpMLDSproj {base} sl =
  InterpMLDirichF1NT {p1=(mldsTot {base} sl)} {q1=base} (mldsProj {base} sl)

-- Now we can interpret a slice over an `MLDirichF1` as a copresheaf
-- over its category of elements.
public export
interpMLDSsl : {base : MLDirichF1} -> (sl : MLDirichF1Sl base) ->
  (p : MLDirichCatObj) -> InterpMLDirichF1 base p -> Type
interpMLDSsl {base} sl p el =
  Subset0
    (interpMLDStot {base} sl p)
    (\x => MLF1elExtEq {f1=base} {p} (interpMLDSproj {base} sl p x) el)

public export
interpMLDSslMapTot : {base : MLDirichF1} -> (sl : MLDirichF1Sl base) ->
  (p, q : MLDirichCatObj) -> (el : InterpMLDirichF1 base p) ->
  (alpha : DirichNatTrans p q) ->
  interpMLDSsl {base} sl p el ->
  interpMLDStot {base} sl q
interpMLDSslMapTot {base=(bpos ** bdir)}
  ((slpos ** sldir) ** (slonpos ** slondir))
  (ppos ** pdir) (qpos ** qdir) (bi ** bpm ** bdm) (aonpos ** aondir)
  (Element0 (sli ** slpm ** sldm) comm) =
    (sli ** aonpos . slpm ** \d1, d2 => aondir (slpm d1) (sldm d1 d2))

public export
0 interpMLDSslMapComm : {base : MLDirichF1} -> (sl : MLDirichF1Sl base) ->
  (p, q : MLDirichCatObj) -> (el : InterpMLDirichF1 base p) ->
  (alpha : DirichNatTrans p q) ->
  (iel : interpMLDSsl {base} sl p el) ->
  MLF1elExtEq {f1=base} {p=q}
    (interpMLDSproj {base}
      sl q
      (interpMLDSslMapTot {base} sl p q el alpha iel))
      (InterpMLDirichF1map base {p} {q} alpha el)
interpMLDSslMapComm {base=(bpos ** bdir)}
  ((slpos ** sldir) ** (slonpos ** slondir))
  (ppos ** pdir) (qpos ** qdir) (bi ** bpm ** bdm) (aonpos ** aondir)
  (Element0 (sli ** slpm ** sldm) (poseq ** onposeq ** ondireq)) =
    (poseq **
     (\bd => cong aonpos (onposeq bd)) **
     (\bd1, bd2 => rewrite onposeq bd1 in rewrite ondireq bd1 bd2 in Refl))

public export
interpMLDSslMap : {base : MLDirichF1} -> (sl : MLDirichF1Sl base) ->
  (p, q : MLDirichCatObj) -> (el : InterpMLDirichF1 base p) ->
  (alpha : DirichNatTrans p q) ->
  interpMLDSsl {base} sl p el ->
  interpMLDSsl {base} sl q (InterpMLDirichF1map base {p} {q} alpha el)
interpMLDSslMap {base} sl p q el alpha i =
  Element0
    (interpMLDSslMapTot {base} sl p q el alpha i)
    (interpMLDSslMapComm {base} sl p q el alpha i)

public export
MLDirichF1SlMor : {base : MLDirichF1} -> IntMorSig (MLDirichF1Sl base)
MLDirichF1SlMor {base} sl sl' =
  Subset0
    (MLDirichF1NT (mldsTot {base} sl) (mldsTot {base} sl'))
    (\alpha =>
      MLDF1NTextEq
        (mldF1NTvcomp {p=(mldsTot sl)} {q=(mldsTot sl')} {r=base}
          (mldsProj sl')
          alpha)
        (mldsProj sl))

-- Now we can interpret a slice morphism as a natural transformation
-- between `interpMLDSsl`s (which are copresheaves over categories
-- of elements of `MLDirichF1`s).
public export
interpMLDSslMor : {base : MLDirichF1} -> {sl, sl' : MLDirichF1Sl base} ->
  MLDirichF1SlMor {base} sl sl' ->
  (p : MLDirichCatObj) -> (el : InterpMLDirichF1 base p) ->
  interpMLDSsl {base} sl p el ->
  interpMLDSsl {base} sl' p el
interpMLDSslMor {base=(bi ** bdir)}
  {sl=((slpos ** sldir) ** slonpos1 ** slonpos2 ** slondir)}
  {sl'=((slpos' ** sldir') ** slonpos1' ** slonpos2' ** slondir')}
  (Element0 (monpos1 ** monpos2 ** mondir) mcomm)
  (ppos ** pdir) (eli ** elpm ** eldm)
  (Element0 (seli ** selonpos ** selondir) slcomm) =
    Element0
      (InterpMLDirichF1NT
        {p1=
          (mldsTot
            {base=(bi ** bdir)}
            ((slpos ** sldir) ** slonpos1 ** slonpos2 ** slondir))}
        {q1=
          (mldsTot
            {base=(bi ** bdir)}
            ((slpos' ** sldir') ** slonpos1' ** slonpos2' ** slondir'))}
        (monpos1 ** monpos2 ** mondir)
        (ppos ** pdir)
        (seli ** selonpos ** selondir))
      (trans (fst mcomm seli) (fst slcomm) **
       \bd1 =>
        rewrite fst (snd mcomm) seli bd1 in
        fst (snd slcomm) (rewrite sym (fst mcomm seli) in bd1) **
       \bd1, bd2 =>
        rewrite fst (snd mcomm) seli bd1 in
        rewrite (snd (snd mcomm) seli bd1 bd2) in
        snd (snd slcomm)
          (rewrite sym (fst mcomm seli) in bd1)
          (rewrite sym (fst mcomm seli) in bd2))

-- Dependent sum in the category of `MLDirichF1`.
public export
MLDF1sigma : {a, b : MLDirichF1} ->
  MLDirichF1NT a b -> MLDirichF1Sl a -> MLDirichF1Sl b
MLDF1sigma {a} {b} alpha f1 = (mldsTot f1 ** mldF1NTvcomp alpha (mldsProj f1))

-- And finally that allows us to use the slice to define an endofunctor.
public export
MLDirichF : Type
MLDirichF = DPair MLDirichF1 MLDirichF1Sl

public export
mdf1 : MLDirichF -> MLDirichF1
mdf1 = DPair.fst

public export
mdf2 : (mdf : MLDirichF) -> MLDirichF1Sl (mdf1 mdf)
mdf2 = DPair.snd

public export
mdfT1 : MLDirichF -> MLDirichF1_T1
mdfT1 mdf = mldPos1 (mdf1 mdf)

public export
mdfET1 : (mdf : MLDirichF) -> MLDirichF1_ET (mdfT1 mdf)
mdfET1 mdf = mldDir1 (mdf1 mdf)

public export
mdfET2tot : MLDirichF -> MLDirichF1
mdfET2tot mdf = mldsTot {base=(mdf1 mdf)} (mdf2 mdf)

public export
mdfET2proj : (mdf : MLDirichF) -> MLDirichF1NT (mdfET2tot mdf) (mdf1 mdf)
mdfET2proj mdf = mldsProj {base=(mdf1 mdf)} (mdf2 mdf)

public export
interpMLDirichF : MLDirichF -> MLDirichCatObj -> MLDirichCatObj
interpMLDirichF mdf p =
  (InterpMLDirichF1 (mdf1 mdf) p ** interpMLDSsl {base=(mdf1 mdf)} (mdf2 mdf) p)

public export
interpMLDirichFmapSnd : (f : MLDirichF) -> (p, q : MLDirichCatObj) ->
  (alpha : DirichNatTrans p q) ->
  (i : InterpMLDirichF1 (mdf1 f) p) ->
  interpMLDSsl {base=(mdf1 f)} (mdf2 f) p i ->
  interpMLDSsl {base=(mdf1 f)} (mdf2 f) q
    (InterpMLDirichF1map {p} {q} (mdf1 f) alpha i)
interpMLDirichFmapSnd f p q alpha i =
  interpMLDSslMap {base=(mdf1 f)} (mdf2 f) p q i alpha

public export
interpMLDirichFmap : (f : MLDirichF) -> (p, q : MLDirichCatObj) ->
  DirichNatTrans p q ->
  DirichNatTrans (interpMLDirichF f p) (interpMLDirichF f q)
interpMLDirichFmap f p q alpha =
  (InterpMLDirichF1map {p} {q} (mdf1 f) alpha **
   interpMLDirichFmapSnd f p q alpha)

-- Natural transformations, which are the morphisms in the (endo)functor
-- category, of `MLDirichF`.
--
-- Note that such a natural transformation is precisely a morphism
-- in the category of bundles in `MLDirichF1`, with the domains being the
-- total spaces, the codomains being the bases, and the arrows being the
-- projections.
--
-- Also note that a bundle morphism (in any category) may be expressed
-- using a slice morphism.
public export
MLDirichFNT : IntMorSig MLDirichF
MLDirichFNT f g =
  (basent : MLDirichF1NT (mdf1 f) (mdf1 g) **
   MLDirichF1SlMor {base=(mdf1 g)} (MLDF1sigma basent (mdf2 f)) (mdf2 g))

public export
InterpMLDirichFNTonpos : {f, g : MLDirichF} -> MLDirichFNT f g ->
  (p : MLDirichCatObj) ->
  dfPos (interpMLDirichF f p) -> dfPos (interpMLDirichF g p)
InterpMLDirichFNTonpos {f} {g} alpha p =
  InterpMLDirichF1NT {p1=(mdf1 f)} {q1=(mdf1 g)} (fst alpha) p

public export
InterpMLDirichFNTondir : {f, g : MLDirichF} -> (alpha : MLDirichFNT f g) ->
  (p : MLDirichCatObj) ->
  (i : dfPos (interpMLDirichF f p)) ->
  dfDir (interpMLDirichF f p) i ->
  dfDir (interpMLDirichF g p) (InterpMLDirichFNTonpos {f} {g} alpha p i)
InterpMLDirichFNTondir
  {f=((ft1pos ** fet1pos ** fet1dir) **
   ((fsltotT1pos ** fsltotET1pos ** fsltotET1dir) **
    (fslonpos1 ** fslonpos2 ** fslondir)))}
  {g=((gt1pos ** get1pos ** get1dir) **
   ((gsltotT1pos ** gsltotET1pos ** gsltotET1dir) **
    (gslonpos1 ** gslonpos2 ** gslondir)))} =
  \((a1onpos1 ** a1onpos2 ** a1ondir) **
    (Element0 (a2onpos1 ** a2etonpos ** a2etondir) acomm)),
   (ppos ** pdir),
   (ppi ** ppi2pos ** ppi2dm),
   (Element0 (pdelpos ** pdeldm1 ** pdeldm2) pdcomm) =>
    Element0
      (InterpMLDirichF1NT
        {p1=(fsltotT1pos ** fsltotET1pos ** fsltotET1dir)}
        {q1=(gsltotT1pos ** gsltotET1pos ** gsltotET1dir)}
        (a2onpos1 ** a2etonpos ** a2etondir)
        (ppos ** pdir)
        (pdelpos ** pdeldm1 ** pdeldm2))
      (rewrite sym (fst pdcomm) in fst acomm pdelpos **
       \gie1 =>
        case fst pdcomm of
          Refl =>
            trans
              (cong pdeldm1 $ fst (snd acomm) pdelpos gie1)
              (fst (snd pdcomm)
                (a1onpos2 ppi (replace {p=get1pos} (fst acomm pdelpos) gie1)))
              **
       \gie1, gde1 =>
        case fst pdcomm of
          Refl =>
            rewrite fst (snd acomm) pdelpos gie1 in
            trans
              (cong
                (pdeldm2
                  (fslonpos2 pdelpos (a1onpos2 (fslonpos1 pdelpos)
                    (replace {p=get1pos} (fst acomm pdelpos) gie1))))
                (rewrite sym (fst (snd acomm) pdelpos gie1) in
                 snd (snd acomm) pdelpos gie1 gde1))
              (snd (snd pdcomm)
                (a1onpos2 ppi (replace {p=get1pos} (fst acomm pdelpos) gie1))
                (a1ondir ppi
                  (replace {p=get1pos} (fst acomm pdelpos) gie1)
                  (rewrite sym (fst acomm pdelpos) in gde1))))

public export
InterpMLDirichFNT : {f, g : MLDirichF} -> MLDirichFNT f g ->
  (p : MLDirichCatObj) ->
  DirichNatTrans (interpMLDirichF f p) (interpMLDirichF g p)
InterpMLDirichFNT {f} {g} alpha p =
  (InterpMLDirichFNTonpos {f} {g} alpha p **
   InterpMLDirichFNTondir {f} {g} alpha p)

-------------------------------------------
-------------------------------------------
---- Dirichlet/polynomial interactions ----
-------------------------------------------
-------------------------------------------

-----------------------------
---- Left Kan extensions ----
-----------------------------

public export
pdfPrecomp : (q : MLDirichCatObj) -> MLPolyCatObj -> MLDirichCatObj
pdfPrecomp = flip pdfCompositionArena

public export
pdfLKanExtPos : (q : MLDirichCatObj) -> MLDirichCatObj -> Type
pdfLKanExtPos q p = dfPos p

public export
pdfLKanExtDir : (q, p : MLDirichCatObj) -> SliceObj (pdfLKanExtPos q p)
pdfLKanExtDir q p pi = InterpDirichFunc q (pfDir {p} pi)

public export
pdfLKanExt : (q : MLDirichCatObj) -> MLDirichCatObj -> MLPolyCatObj
pdfLKanExt q p = (pdfLKanExtPos q p ** pdfLKanExtDir q p)

public export
pdfLKanUnit : (q : MLDirichCatObj) ->
  (p : MLDirichCatObj) -> DirichNatTrans p (pdfPrecomp q $ pdfLKanExt q p)
pdfLKanUnit q p = (\pi => (pi ** fst) ** \pi, pd, pdqd => snd pdqd pd)

public export
pdfLKanCounit : (q : MLDirichCatObj) ->
  (p : MLPolyCatObj) -> PolyNatTrans (pdfLKanExt q $ pdfPrecomp q p) p
pdfLKanCounit q p = (fst ** \pdqp, qd => (snd pdqp qd ** \pdqd => pdqd qd))

-------------------------------------------------
-------------------------------------------------
---- Dirichlet slices as polynomial functors ----
-------------------------------------------------
-------------------------------------------------

-- We now show that `MlDirichSlObj` is a (special case of a) signature that
-- we have developed previously: `SPFdepDirType`.
public export
MlDirichSlToSPFDD : {ar : MLArena} ->
  MlDirichSlObj ar -> SPFdepData {b=(pfPos ar)} (snd ar) (const Unit)
MlDirichSlToSPFDD {ar} sl =
  SPFDD (\i, () => mdsOnPos sl i) (\ei, () => mdsDir sl ei)

public export
MlDirichSlFromSPFDD : (ar : MLArena) ->
  SPFdepData {b=(pfPos ar)} (pfDir {p=ar}) (const Unit) -> MlDirichSlObj ar
MlDirichSlFromSPFDD ar spfdd =
  MDSobj (flip (spfddPos spfdd) ()) $ \ep => spfddDir spfdd ep ()

-- From the above two translations, we can conclude that for `ar : MLArena`
-- representing a Dirichlet functor, an `MlDirichSlObj ar` -- an object in the
-- slice category of Dirichlet functors over `ar` -- is precisely a polynomial
-- (parametric right adjoint) functor from the slice category of `Type` over
-- the directions of `ar` to `Type` itself (which is equivalent to `Type`
-- sliced over `Unit`), or, put another way, a polynomial copresheaf on the
-- directions of `ar`.

--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
---- PRA functors between slice categories of Dirichlet/polynomial functors ----
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------

------------------------------------------------------
---- Polynomial-functor slice functor definitions ----
------------------------------------------------------

public export
0 MlDirichSlFunc : MLArena -> MLArena -> Type
MlDirichSlFunc p q = MlDirichSlObj p -> MlDirichSlObj q

public export
0 MlDirichSlFMap : {ar, ar' : MLArena} -> MlDirichSlFunc ar ar' -> Type
MlDirichSlFMap {ar} {ar'} f =
  (sl, sl' : MlDirichSlObj ar) ->
  MlDirichSlMor {ar} sl sl' -> MlDirichSlMor {ar=ar'} (f sl) (f sl')

public export
0 MlPolySlFunc : MLArena -> MLArena -> Type
MlPolySlFunc p q = MlPolySlObj p -> MlPolySlObj q

public export
0 MlPolySlFMap : {ar, ar' : MLArena} -> MlPolySlFunc ar ar' -> Type
MlPolySlFMap {ar} {ar'} f =
  (sl, sl' : MlPolySlObj ar) ->
  MlPolySlMor {ar} sl sl' -> MlPolySlMor {ar=ar'} (f sl) (f sl')

---------------------
---- Base change ----
---------------------

public export
mlDirichSlBaseChange : {p, q : PolyFunc} ->
  DirichNatTrans q p -> MlDirichSlFunc p q
mlDirichSlBaseChange {p} {q} (onpos ** ondir) (MDSobj slpos sldir) =
  MDSobj (slpos . onpos) (\qp, sp, qd => sldir (onpos qp) sp $ ondir qp qd)

public export
mlDirichSlBaseChangeMap : {p, q : PolyFunc} -> (nt : DirichNatTrans q p) ->
  MlDirichSlFMap {ar=p} {ar'=q} (mlDirichSlBaseChange {p} {q} nt)
mlDirichSlBaseChangeMap {p} {q} (ntonpos ** ntondir)
  (MDSobj dpos ddir) (MDSobj cpos cdir) (MDSM monpos mondir) =
    MDSM
      (\qp, dp => monpos (ntonpos qp) dp)
      (\qp, dp, qd, dd => mondir (ntonpos qp) dp (ntondir qp qd) dd)

-- When we express slice objects over a polynomial functor as fibrations
-- rather than total-space objects with projection morphisms, we can perform
-- base changes by specifying the data not of a polynomial natural
-- transformation, but of a Dirichlet natural transformation.
public export
mlPolySlBaseChange : {p, q : PolyFunc} ->
  DirichNatTrans q p -> MlPolySlFunc p q
mlPolySlBaseChange {p} {q} (onpos ** ondir) (MPSobj slonpos sldir slondir) =
  MPSobj
    (slonpos . onpos)
    (\i => sldir $ onpos i)
    (\i, j, qd => slondir (onpos i) j $ ondir i qd)

public export
mlPolySlBaseChangeMap : {p, q : PolyFunc} -> (nt : DirichNatTrans q p) ->
  MlPolySlFMap {ar=p} {ar'=q} (mlPolySlBaseChange {p} {q} nt)
mlPolySlBaseChangeMap {p} {q} (ntonpos ** ntondir)
  (MPSobj dpos ddir dondir) (MPSobj cpos cdir condir) m =
    MPSM
      (\qp => mpsmOnPos m (ntonpos qp))
      (\qp, dp, cd => mpsmOnDir m (ntonpos qp) dp cd)
      (\qp, dp, bd => mpsmOnDirCommutes m (ntonpos qp) dp (ntondir qp bd))

-------------------------------
---- Sigma (dependent sum) ----
-------------------------------

public export
MLPolySlFibSigma : (q : PolyFunc) -> {p : PolyFunc} ->
  PolyNatTrans p q -> MlPolySlObj p -> MlPolySlObj q
MLPolySlFibSigma q {p} beta sl with (mlPolySlObjToC p sl)
  MLPolySlFibSigma q {p} beta sl | (r ** alpha) =
    let csigma = (r ** pntVCatComp beta alpha) in
    mlPolySlObjFromC q csigma

public export
mlDirichSlSigma : {p : MLDirichCatObj} ->
  (sl : MlDirichSlObj p) -> MlDirichSlFunc (mlDirichSlObjTot {ar=p} sl) p
mlDirichSlSigma {p=(ppos ** pdir)} (MDSobj slpos sldir) (MDSobj totpos totdir) =
  MDSobj
    (\pi => Sigma {a=(slpos pi)} $ curry totpos pi)
    (\pi, pst, pd =>
      Sigma {a=(sldir pi (fst pst) pd)} $ \sld =>
        totdir (pi ** fst pst) (snd pst) (pd ** sld))

public export
mlDirichSlSigmaMap : {p : MLDirichCatObj} ->
  (sl : MlDirichSlObj p) ->
  MlDirichSlFMap {ar=(mlDirichSlObjTot {ar=p} sl)} {ar'=p}
    (mlDirichSlSigma {p} sl)
mlDirichSlSigmaMap {p=(ppos ** pdir)} (MDSobj slpos sldir)
  (MDSobj xpos xdir) (MDSobj ypos ydir) (MDSM monpos mdir) =
    MDSM
      (\pi, psx =>
        (fst psx ** monpos (pi ** fst psx) (snd psx)))
      (\pi, psx, pd, sxd =>
        (fst sxd ** mdir (pi ** fst psx) (snd psx) (pd ** fst sxd) (snd sxd)))

public export
mlDirichSlSigmaPiFL : {p, q : MLDirichCatObj} ->
  (d : MlDirichSlObj (dfParProductArena p q)) -> MlDirichSlFunc q p
mlDirichSlSigmaPiFL {p=(ppos ** pdir)} {q=(qpos ** qdir)}
  (MDSobj prodpos proddir) (MDSobj slpos sldir) =
    MDSobj
      (SliceSigmaPiFL prodpos slpos)
      (\pp, ((qp ** prodp) ** slp), pd =>
        (qd : qdir qp ** (sldir qp slp qd, proddir (pp, qp) prodp (pd, qd))))

public export
mlDirichSlSigmaPiFLMap : {p, q : MLDirichCatObj} ->
  (d : MlDirichSlObj (dfParProductArena p q)) ->
  MlDirichSlFMap {ar=q} {ar'=p} (mlDirichSlSigmaPiFL {p} {q} d)
mlDirichSlSigmaPiFLMap {p=(ppos ** pdir)} {q=(qpos ** qdir)}
  (MDSobj prodpos proddir) (MDSobj slpos sldir) (MDSobj slpos' sldir')
  (MDSM monpos mondir) =
    MDSM
      (ssplMap prodpos slpos slpos' monpos)
      (\pp, ((qp ** prodp) ** slp), pd, (qd ** (sld, prodd)) =>
        (qd ** (mondir qp slp qd sld, prodd)))

--------------------------------
---- Pi (dependent product) ----
--------------------------------

public export
mlDirichSlSigmaPiFR : {p, q : PolyFunc} ->
  (d : MlDirichSlObj (dfParProductArena p q)) -> MlDirichSlFunc p q
mlDirichSlSigmaPiFR {p=(ppos ** pdir)} {q=(qpos ** qdir)}
  (MDSobj prodpos proddir) (MDSobj slpos sldir) =
    MDSobj
      (SliceSigmaPiFR prodpos slpos)
      (\qp, slp, qd =>
        (pp : ppos) -> (prodp : prodpos (pp, qp)) -> (pd : pdir pp) ->
        (sldir pp (slp (pp ** prodp)) pd, proddir (pp, qp) prodp (pd, qd)))

public export
mlDirichSlSigmaPiFRMap : {p, q : PolyFunc} ->
  (d : MlDirichSlObj (dfParProductArena p q)) ->
  MlDirichSlFMap {ar=p} {ar'=q} (mlDirichSlSigmaPiFR {p} {q} d)
mlDirichSlSigmaPiFRMap {p=(ppos ** pdir)} {q=(qpos ** qdir)}
  (MDSobj prodpos proddir) (MDSobj slpos sldir) (MDSobj slpos' sldir')
  (MDSM monpos mondir) =
    MDSM
      (ssprMap prodpos slpos slpos' monpos)
      (\qp, slp, qd, dirs, pp, prodp, pd =>
        mapFst (mondir pp (slp (pp ** prodp)) pd) $ dirs pp prodp pd)

----------------------------
---- General polynomial ----
----------------------------

-- https://ncatlab.org/nlab/show/parametric+right+adjoint#generic_morphisms
-- describes how a PRA functor between presheaf categories is determined
-- by two pieces of data which it calls `T1` and `E_T`.  It refers to
-- general presheaf categories over categories it calls `I` and `J`.
--
-- Here we are considering PRA functors between slice categories of Dirichlet
-- functors.  The slice category of Dirichlet functors over a Dirichlet
-- functor `p` is equivalent to the category of presheaves over its category
-- of elements.  Hence, we can determine a PRA (polynomial) functor between
-- slice categories over Dirichlet functors `p` and `q` by specifying `T1`
-- and `E_T` where `I` is the category of elements of `p` and `J` is the
-- category of elements of `q`.
--
-- `T1` is simply an object of the codomain (specifically, the presheaf over
-- `J` to which we shall map the terminal presheaf over `I`), so it is an
-- object of the category of Dirichlet functors sliced over `q` (equivalently,
-- an object of the category of presheaves over the category of elements of
-- `q`).
--
-- `E_T`, given a `T1`, is a functor from the category of elements of `T1`
-- (which makes sense because `T1` is itself a presheaf) to the category of
-- presheaves over `I` (which is the domain of the PRA functor).
--
-- We can view this as the generalization of `SPFdirType` in `SlicePolyCat`
-- from slice categories to categories of elements of Dirichlet functors.
-- It is precisely the parameter that we pass to
-- `mlDirichSlSigmaPiFL`/`mlDirichSlSigmaPiFR` to produce the right-adjoint
-- component of the factorization of a PRA functor into a right adjoint
-- followed by a dependent sum.
public export
PRAbase : (cod : MLDirichCatObj) ->
  (pos : MlDirichSlObj cod) -> MLDirichCatObj
PRAbase cod = mlDirichSlObjTot {ar=cod}

public export
PRAdirDom : (dom, cod : MLDirichCatObj) ->
  (pos : MlDirichSlObj cod) -> MLDirichCatObj
PRAdirDom dom cod pos = dfParProductArena dom (PRAbase cod pos)

public export
0 PRAdirType : (0 dom, cod : MLDirichCatObj) ->
  (0 pos : MlDirichSlObj cod) -> Type
PRAdirType dom cod pos = MlDirichSlObj (PRAdirDom dom cod pos)

public export
record PRAData (dom, cod : MLDirichCatObj) where
  constructor PRAD
  pradT1 : MlDirichSlObj cod
  pradET : PRAdirType dom cod pradT1

public export
PRADbase : {dom, cod : MLDirichCatObj} -> PRAData dom cod -> MLDirichCatObj
PRADbase {dom} {cod} prad = PRAbase cod $ pradT1 prad

-- See the formula for `T` in the `Proposition 2.10` section of
-- https://ncatlab.org/nlab/show/parametric+right+adjoint#generic_morphisms .
public export
InterpPRAdataOmap : {dom, cod : MLDirichCatObj} ->
  PRAData dom cod -> MlDirichSlFunc dom cod
InterpPRAdataOmap {dom} {cod} prad =
  mlDirichSlSigma {p=cod} (pradT1 prad)
  . mlDirichSlSigmaPiFR {p=dom} {q=(PRADbase {dom} {cod} prad)} (pradET prad)

public export
InterpPRAdataFmap : {dom, cod : MLDirichCatObj} ->
  (prad : PRAData dom cod) ->
  MlDirichSlFMap {ar=dom} {ar'=cod} (InterpPRAdataOmap prad)
InterpPRAdataFmap {dom} {cod} prad x y =
  mlDirichSlSigmaMap {p=cod} (pradT1 prad)
    (mlDirichSlSigmaPiFR (pradET prad) x)
    (mlDirichSlSigmaPiFR (pradET prad) y)
  . mlDirichSlSigmaPiFRMap {p=dom} {q=(PRADbase {dom} {cod} prad)}
    (pradET prad)
    x
    y

-- As with `SPFdirType`, we can make a more dependent version of `PRAdirType`.

public export
PRAdepBase : {b : MLDirichCatObj} -> (codsl : MlDirichSlObj b) ->
  (pos : MlDirichSlOfSl {ar=b} codsl) -> MlDirichSlObj b
PRAdepBase {b} codsl pos = MlDirichBaseSlFromSlOfSl {ar=b} codsl pos

public export
PRAdepDirDom : {b : MLDirichCatObj} -> (domsl, codsl : MlDirichSlObj b) ->
  (pos : MlDirichSlOfSl {ar=b} codsl) -> MlDirichSlObj b
PRAdepDirDom {b} domsl codsl pos =
  dfSlParProduct domsl (PRAdepBase {b} codsl pos)

public export
0 PRAdepDirType : {0 b : MLDirichCatObj} ->
  (0 domsl, codsl : MlDirichSlObj b) -> (0 pos : MlDirichSlOfSl {ar=b} codsl) ->
  Type
PRAdepDirType {b} domsl codsl pos =
  MlDirichSlOfSl {ar=b} $ PRAdepDirDom {b} domsl codsl pos

public export
PRAdirFromDep : {0 b : MLDirichCatObj} ->
  {0 domsl, codsl : MlDirichSlObj b} -> {0 pos : MlDirichSlOfSl {ar=b} codsl} ->
  PRAdepDirType {b} domsl codsl pos ->
  PRAdirType (mlDirichSlObjTot {ar=b} domsl) (mlDirichSlObjTot {ar=b} codsl) pos
PRAdirFromDep {b=(bpos ** bdir)}
  {domsl=(MDSobj dompos domdir)} {codsl=(MDSobj codpos coddir)}
  {pos=(MDSobj pospos posdir)}
  (MDSobj deponpos depdir) =
    MDSobj
      (\((bi ** di), ((bi' ** ci) ** pi)) =>
        Exists {type=(WDiagElem (bi, bi'))} $ \eqb =>
          deponpos (bi ** (di, rewrite WDiagElemEqualizes eqb in (ci ** pi))))
      (\((bi ** di), ((bi' ** ci) ** pi)), (Evidence weqb cpi),
        ((bd ** dd), ((bd' ** cd) ** pd)) =>
          let 0 eqb = WDiagElemEqualizes weqb in
          Exists {type=(WDiagElem (bd, rewrite eqb in bd'))} $ \weqd =>
            let 0 eqd = WDiagElemEqualizes weqd in
            depdir
              (bi ** (di, rewrite eqb in (ci ** pi)))
              cpi
              (bd ** (dd, rewrite eqb in rewrite eqd in (cd ** pd))))

public export
record PRAdepData {b : MLDirichCatObj} (domsl, codsl : MlDirichSlObj b) where
  constructor PRADD
  praddPos : MlDirichSlOfSl {ar=b} codsl
  praddDir : PRAdepDirType {b} domsl codsl praddPos

public export
PRADdepBase : {b : MLDirichCatObj} -> {domsl, codsl : MlDirichSlObj b} ->
  PRAdepData {b} domsl codsl -> MlDirichSlObj b
PRADdepBase {b} {domsl} {codsl} pradd = PRAdepBase {b} codsl $ praddPos pradd

public export
PRAdataFromDep : {b : MLDirichCatObj} -> {domsl, codsl : MlDirichSlObj b} ->
  PRAdepData {b} domsl codsl ->
  PRAData (mlDirichSlObjTot {ar=b} domsl) (mlDirichSlObjTot {ar=b} codsl)
PRAdataFromDep {b} {domsl} {codsl} pradd =
  PRAD
    (praddPos pradd)
    (PRAdirFromDep {b} {domsl} {codsl} {pos=(praddPos pradd)} (praddDir pradd))

public export
InterpPRAdepDataOmap : {b : MLDirichCatObj} ->
  {domsl, codsl : MlDirichSlObj b} ->
  PRAdepData {b} domsl codsl ->
  MlDirichSlFunc (mlDirichSlObjTot {ar=b} domsl) (mlDirichSlObjTot {ar=b} codsl)
InterpPRAdepDataOmap {b} {domsl} {codsl} pradd =
  InterpPRAdataOmap
    {dom=(mlDirichSlObjTot {ar=b} domsl)}
    {cod=(mlDirichSlObjTot {ar=b} codsl)}
    $ PRAdataFromDep {b} {domsl} {codsl} pradd

public export
InterpPRAdepDataFmap : {b : MLDirichCatObj} ->
  {domsl, codsl : MlDirichSlObj b} ->
  (pradd : PRAdepData {b} domsl codsl) ->
  MlDirichSlFMap
    {ar=(mlDirichSlObjTot {ar=b} domsl)}
    {ar'=(mlDirichSlObjTot {ar=b} codsl)}
    (InterpPRAdepDataOmap {b} {domsl} {codsl} pradd)
InterpPRAdepDataFmap {b} {domsl} {codsl} pradd =
  InterpPRAdataFmap
    {dom=(mlDirichSlObjTot {ar=b} domsl)}
    {cod=(mlDirichSlObjTot {ar=b} codsl)}
    $ PRAdataFromDep {b} {domsl} {codsl} pradd
