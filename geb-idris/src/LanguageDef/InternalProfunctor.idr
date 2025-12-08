module LanguageDef.InternalProfunctor

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat
import public LanguageDef.IntArena

----------------------------------------------------------------------
----------------------------------------------------------------------
---- Internal pro-/di-functors and (para-)natural transformations ----
----------------------------------------------------------------------
----------------------------------------------------------------------

-----------------------------------------
---- Definitions of pro-/di-functors ----
-----------------------------------------

-- The convention we use is that the first parameter (here, `d`) is the
-- contravariant parameter, and the second parameter (`here, `c`) is
-- the covariant parameter.  This is sometimes written as `c -/-> d`,
-- and sometimes called a "correspondence from" `d` to `c`.
-- Since `Cat` is cartesian closed, it may be viewed as a functor
-- `c -> presheaves(d)`, or equivalently as a functor
-- `op(d) -> copresheaves(c)`.  See
-- https://en.wikipedia.org/wiki/Profunctor#Definition and
-- https://ncatlab.org/nlab/show/profunctor#definition.
public export
IntProfunctorSig : (d, c : Type) -> Type
IntProfunctorSig d c = d -> c -> Type

public export
IntDifunctorSig : (c : Type) -> Type
IntDifunctorSig c = IntProfunctorSig c c

public export
IntComp : (c : Type) -> (mor : IntDifunctorSig c) -> Type
IntComp c mor = (x, y, z : c) -> mor y z -> mor x y -> mor x z

public export
0 IntIdLSig : (0 c : Type) -> (0 mor : IntMorSig c) ->
  (comp : IntCompSig c mor) -> IntIdSig c mor -> Type
IntIdLSig c mor comp cid =
  (0 x, y : c) -> (m : mor x y) -> comp x x y m (cid x) = m

public export
typeIdL : IntIdLSig Type TypeMor InternalCat.typeComp InternalCat.typeId
typeIdL x y m = Refl

public export
0 IntIdRSig : (0 c : Type) -> (0 mor : IntMorSig c) ->
  (comp : IntCompSig c mor) -> IntIdSig c mor -> Type
IntIdRSig c mor comp cid =
  (0 x, y : c) -> (m : mor x y) -> comp x y y (cid y) m = m

public export
typeIdR : IntIdRSig Type TypeMor InternalCat.typeComp InternalCat.typeId
typeIdR x y m = Refl

public export
0 IntAssocSig : (0 c : Type) ->
  (mor : IntMorSig c) -> (comp : IntCompSig c mor) ->
  Type
IntAssocSig c mor comp =
  (w, x, y, z : c) ->
  (h : mor y z) -> (g : mor x y) -> (f : mor w x) ->
  comp w x z (comp x y z h g) f = comp w y z h (comp w x y g f)

public export
typeAssoc : IntAssocSig Type TypeMor InternalCat.typeComp
typeAssoc w x y z h g f = Refl

public export
0 IntDimapSig : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  IntProfunctorSig d c -> Type
IntDimapSig d c dmor cmor p =
  (s : d) -> (t : c) -> (a : d) -> (b : c) ->
  dmor a s -> cmor t b -> p s t -> p a b

public export
0 IntEndoDimapSig : (0 c : Type) -> (0 mor : IntDifunctorSig c) ->
  IntDifunctorSig c -> Type
IntEndoDimapSig c mor = IntDimapSig c c mor mor

public export
0 IntLmapSig : (d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  IntProfunctorSig d c -> Type
IntLmapSig d c dmor cmor p =
  (s : d) -> (t : c) -> (a : d) -> dmor a s -> p s t -> p a t

public export
0 IntEndoLmapSig : (c : Type) -> (cmor : IntDifunctorSig c) ->
  IntDifunctorSig c -> Type
IntEndoLmapSig c cmor = IntLmapSig c c cmor cmor

public export
0 IntLmapIdSig : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  (did : IntIdSig d dmor) ->
  (p : IntProfunctorSig d c) ->
  IntLmapSig d c dmor cmor p -> Type
IntLmapIdSig d c dmor cmor did p plm =
  (0 s : d) -> (0 t : c) -> (0 pst : p s t) -> plm s t s (did s) pst = pst

public export
0 IntEndoLmapIdSig : (0 c : Type) -> (0 cmor : IntDifunctorSig c) ->
  (cid : IntIdSig c cmor) -> (p : IntDifunctorSig c) ->
  IntEndoLmapSig c cmor p -> Type
IntEndoLmapIdSig c cmor = IntLmapIdSig c c cmor cmor

public export
0 IntRmapSig : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  IntProfunctorSig d c -> Type
IntRmapSig d c dmor cmor p =
  (s : d) -> (t : c) -> (b : c) -> cmor t b -> p s t -> p s b

public export
0 IntEndoRmapSig : (0 c : Type) -> (0 cmor : IntDifunctorSig c) ->
  IntDifunctorSig c -> Type
IntEndoRmapSig c cmor = IntRmapSig c c cmor cmor

public export
0 IntRmapIdSig : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  (cid : IntIdSig c cmor) ->
  (p : IntProfunctorSig d c) ->
  IntRmapSig d c dmor cmor p -> Type
IntRmapIdSig d c dmor cmor cid p prm =
  (0 s : d) -> (0 t : c) -> (0 pst : p s t) -> prm s t t (cid t) pst = pst

public export
0 IntEndoRmapIdSig : (0 c : Type) -> (0 cmor : IntDifunctorSig c) ->
  (cid : IntIdSig c cmor) -> (p : IntDifunctorSig c) ->
  IntEndoRmapSig c cmor p -> Type
IntEndoRmapIdSig c cmor = IntRmapIdSig c c cmor cmor

public export
IntLmapFromDimap : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  (cid : IntIdSig c cmor) ->
  (p : IntProfunctorSig d c) ->
  IntDimapSig d c dmor cmor p ->
  IntLmapSig d c dmor cmor p
IntLmapFromDimap d c dmor cmor cid p pdm s t a = flip (pdm s t a t) (cid t)

public export
IntEndoLmapFromDimap : (0 c : Type) -> (0 cmor : IntDifunctorSig c) ->
  (cid : IntIdSig c cmor) -> (p : IntDifunctorSig c) ->
  IntEndoDimapSig c cmor p -> IntEndoLmapSig c cmor p
IntEndoLmapFromDimap c cmor cid = IntLmapFromDimap c c cmor cmor cid

public export
IntRmapFromDimap : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  (did : IntIdSig d dmor) ->
  (p : IntProfunctorSig d c) ->
  IntDimapSig d c dmor cmor p ->
  IntRmapSig d c dmor cmor p
IntRmapFromDimap d c dmor cmor did p pdm s t b = pdm s t s b (did s)

public export
IntEndoRmapFromDimap : (0 c : Type) -> (0 cmor : IntDifunctorSig c) ->
  (cid : IntIdSig c cmor) -> (p : IntDifunctorSig c) ->
  IntEndoDimapSig c cmor p -> IntEndoRmapSig c cmor p
IntEndoRmapFromDimap c cmor cid = IntRmapFromDimap c c cmor cmor cid

public export
0 IntLRmapsCommute : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  (p : IntProfunctorSig d c) ->
  IntLmapSig d c dmor cmor p ->
  IntRmapSig d c dmor cmor p ->
  Type
IntLRmapsCommute d c dmor cmor p plm prm =
  (0 s : d) -> (0 t : c) -> (0 a : d) -> (0 b : c) ->
  (0 dmas : dmor a s) -> (0 cmtb : cmor t b) ->
  ExtEq {a=(p s t)} {b=(p a b)}
    (plm s b a dmas . prm s t b cmtb)
    (prm a t b cmtb . plm s t a dmas)

public export
0 IntEndoLRmapsCommute : (0 c : Type) -> (0 cmor : IntDifunctorSig c) ->
  (p : IntDifunctorSig c) ->
  IntEndoLmapSig c cmor p -> IntEndoRmapSig c cmor p ->
  Type
IntEndoLRmapsCommute c cmor p plm prm = IntLRmapsCommute c c cmor cmor p plm prm

public export
0 IntLmapComp : (0 c : Type) -> (0 cmor : IntDifunctorSig c) ->
  (0 ccomp : IntCompSig c cmor) ->
  (p : IntDifunctorSig c) ->
  IntEndoLmapSig c cmor p ->
  Type
IntLmapComp c cmor ccomp p plm =
  (0 s, t, a, a' : c) ->
  (0 cma's : cmor a' s) -> (0 cmaa' : cmor a a') ->
  ExtEq {a=(p s t)} {b=(p a t)}
    (plm a' t a cmaa' . plm s t a' cma's)
    (plm s t a (ccomp a a' s cma's cmaa'))

public export
0 IntRmapComp : (0 c : Type) -> (0 cmor : IntDifunctorSig c) ->
  (0 ccomp : IntCompSig c cmor) ->
  (p : IntDifunctorSig c) ->
  IntEndoRmapSig c cmor p ->
  Type
IntRmapComp c cmor ccomp p prm =
  (0 s, t, b, b' : c) ->
  (0 cmtb' : cmor t b') -> (0 cmb'b : cmor b' b) ->
  ExtEq {a=(p s t)} {b=(p s b)}
    (prm s b' b cmb'b . prm s t b' cmtb')
    (prm s t b (ccomp t b' b cmb'b cmtb'))

public export
IntDimapFromLRmaps : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  (p : IntProfunctorSig d c) ->
  IntLmapSig d c dmor cmor p ->
  IntRmapSig d c dmor cmor p ->
  IntDimapSig d c dmor cmor p
IntDimapFromLRmaps d c dmor cmor p plm prm s t a b dmas cmtb =
  plm s b a dmas . prm s t b cmtb

public export
IntEndoDimapFromLRmaps : (0 c : Type) -> (0 cmor : IntDifunctorSig c) ->
  (p : IntDifunctorSig c) ->
  IntEndoLmapSig c cmor p ->
  IntEndoRmapSig c cmor p ->
  IntEndoDimapSig c cmor p
IntEndoDimapFromLRmaps c cmor = IntDimapFromLRmaps c c cmor cmor

--------------------------------------------
---- (Di-/Para-)natural transformations ----
--------------------------------------------

-- The signature of a dinatural transformation, without the dinaturality
-- condition.
public export
IntDiNTSig : (c : Type) -> (p, q : IntDifunctorSig c) -> Type
IntDiNTSig c p q = (x : c) -> p x x -> q x x

-- The dinaturality condition.  For our purposes, we will only be interested
-- in _strong_ dinatural transformations, or "paranatural" transformations,
-- which have the same base signature, together with a condition defined below.
-- Therefore, our only use of this condition will be to prove that it follows
-- from the paranaturality condition (so all paranatural transformations are
-- dinatural, but not vice versa).
public export
0 IntDiNTCond : (c : Type) -> (cmor : IntDifunctorSig c) ->
  (p, q : IntDifunctorSig c) ->
  IntEndoLmapSig c cmor p -> IntEndoRmapSig c cmor p ->
  IntEndoLmapSig c cmor q -> IntEndoRmapSig c cmor q ->
  IntDiNTSig c p q -> Type
IntDiNTCond c cmor p q plm prm qlm qrm alpha =
  (i0, i1 : c) -> (i2 : cmor i0 i1) ->
  ExtEq {a=(p i1 i0)} {b=(q i0 i1)}
    (qlm i1 i1 i0 i2 . alpha i1 . prm i1 i0 i1 i2)
    (qrm i0 i0 i1 i2 . alpha i0 . plm i1 i0 i0 i2)

public export
IntDiNTcomp : (c : Type) -> (p, q, r : IntDifunctorSig c) ->
  IntDiNTSig c q r -> IntDiNTSig c p q -> IntDiNTSig c p r
IntDiNTcomp c p q r beta alpha x = beta x . alpha x

-- This could be read as "`alpha` preserves structure-homomorphisms", which
-- in turn means that each such paranatural transformation corresponds to
-- a functor between categories of diagonal elements.
public export
0 IntParaNTCond : (c : Type) -> (cmor : IntDifunctorSig c) ->
  (p, q : IntDifunctorSig c) ->
  IntEndoLmapSig c cmor p -> IntEndoRmapSig c cmor p ->
  IntEndoLmapSig c cmor q -> IntEndoRmapSig c cmor q ->
  IntDiNTSig c p q -> Type
IntParaNTCond c cmor p q plm prm qlm qrm alpha =
  (i0, i1 : c) -> (i2 : cmor i0 i1) -> (d0 : p i0 i0) -> (d1 : p i1 i1) ->
  (plm i1 i1 i0 i2 d1 = prm i0 i0 i1 i2 d0) ->
  (qlm i1 i1 i0 i2 (alpha i1 d1) = qrm i0 i0 i1 i2 (alpha i0 d0))

-- Paranaturality is a (strictly) stronger condition than dinaturality.
public export
0 IntParaNTimpliesDi : (c : Type) -> (cmor : IntDifunctorSig c) ->
  (p, q : IntDifunctorSig c) ->
  (plm : IntEndoLmapSig c cmor p) -> (prm : IntEndoRmapSig c cmor p) ->
  IntEndoLRmapsCommute c cmor p plm prm ->
  (qlm : IntEndoLmapSig c cmor q) -> (qrm : IntEndoRmapSig c cmor q) ->
  (alpha : IntDiNTSig c p q) ->
  IntParaNTCond c cmor p q plm prm qlm qrm alpha ->
  IntDiNTCond c cmor p q plm prm qlm qrm alpha
IntParaNTimpliesDi c cmor p q plm prm comm qlm qrm alpha para i0 i1 i2 pi1i0 =
  para i0 i1 i2 (plm i1 i0 i0 i2 pi1i0) (prm i1 i0 i1 i2 pi1i0) $
    comm i1 i0 i0 i1 i2 i2 pi1i0

-- Paranatural transformations compose (which dinatural transformations
-- do not in general).
public export
IntParaNTcomp : (c : Type) -> (mor : IntDifunctorSig c) ->
  (p, q, r : IntDifunctorSig c) ->
  (plm : IntEndoLmapSig c mor p) -> (prm : IntEndoRmapSig c mor p) ->
  (qlm : IntEndoLmapSig c mor q) -> (qrm : IntEndoRmapSig c mor q) ->
  (rlm : IntEndoLmapSig c mor r) -> (rrm : IntEndoRmapSig c mor r) ->
  (beta : IntDiNTSig c q r) ->
  IntParaNTCond c mor q r qlm qrm rlm rrm beta ->
  (alpha : IntDiNTSig c p q) ->
  IntParaNTCond c mor p q plm prm qlm qrm alpha ->
  IntParaNTCond c mor p r plm prm rlm rrm (IntDiNTcomp c p q r beta alpha)
IntParaNTcomp c mor p q r plm prm qlm qrm rlm rrm beta bcond alpha acond
  i0 i1 mi0i1 p00 p11 pcomm =
    bcond i0 i1 mi0i1 (alpha i0 p00) (alpha i1 p11) $
      acond i0 i1 mi0i1 p00 p11 pcomm

--------------------------------------------
---- Profunctor natural transformations ----
--------------------------------------------

public export
IntProfNTSig : (d, c : Type) ->
  (p, q : IntProfunctorSig d c) -> Type
IntProfNTSig d c p q = (x : d) -> (y : c) -> p x y -> q x y

public export
IntEndoProfNTSig : (c : Type) ->
  (p, q : IntDifunctorSig c) -> Type
IntEndoProfNTSig c = IntProfNTSig c c

public export
0 IntProfNTNaturality :
  (d, c : Type) -> (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  (p, q : IntProfunctorSig d c) ->
  IntDimapSig d c dmor cmor p -> IntDimapSig d c dmor cmor q ->
  IntProfNTSig d c p q -> Type
IntProfNTNaturality d c dmor cmor p q pdm qdm alpha =
  (0 s : d) -> (0 t : c) -> (0 a : d) -> (0 b : c) ->
  (0 dmas : dmor a s) -> (0 cmtb : cmor t b) ->
  ExtEq {a=(p s t)} {b=(q a b)}
    (qdm s t a b dmas cmtb . alpha s t)
    (alpha a b . pdm s t a b dmas cmtb)

public export
0 IntProfNTvComp : (0 d, c : Type) ->
  (0 p, q, r : IntProfunctorSig d c) ->
  IntProfNTSig d c q r -> IntProfNTSig d c p q -> IntProfNTSig d c p r
IntProfNTvComp d c p q r beta alpha x y = beta x y . alpha x y

-------------------------------------------------------------------------------
---- Restriction of natural transformations to paranatural transformations ----
-------------------------------------------------------------------------------

-- Here we show that given a natural transformation between profunctors,
-- its restriction to the diagonal is paranatural.

public export
IntProfNTRestrict : (0 c : Type) ->
  (0 p, q : IntDifunctorSig c) -> IntEndoProfNTSig c p q -> IntDiNTSig c p q
IntProfNTRestrict c p q alpha x = alpha x x

public export
0 IntProfNTRestrictPara :
  (0 c : Type) -> (0 cmor : IntDifunctorSig c) -> (0 cid : IntIdSig c cmor) ->
  (0 p, q : IntDifunctorSig c) ->
  (plm : IntEndoLmapSig c cmor p) -> (prm : IntEndoRmapSig c cmor p) ->
  (qlm : IntEndoLmapSig c cmor q) -> (qrm : IntEndoRmapSig c cmor q) ->
  (plid : IntEndoLmapIdSig c cmor cid p plm) ->
  (prid : IntEndoRmapIdSig c cmor cid p prm) ->
  (qlid : IntEndoLmapIdSig c cmor cid q qlm) ->
  (qrid : IntEndoRmapIdSig c cmor cid q qrm) ->
  (alpha : IntProfNTSig c c p q) ->
  IntProfNTNaturality c c cmor cmor p q
    (IntEndoDimapFromLRmaps c cmor p plm prm)
    (IntEndoDimapFromLRmaps c cmor q qlm qrm)
    alpha ->
  IntParaNTCond c cmor p q plm prm qlm qrm (IntProfNTRestrict c p q alpha)
IntProfNTRestrictPara c cmor cid p q plm prm qlm qrm plid prid qlid qrid
  alpha nat s t cmst pss ptt peq =
    let
      qlrew = qlid s t (qrm s s t cmst (alpha s s pss))
      qrrew = cong (qlm t t s cmst) $ qrid t t (alpha t t ptt)
      plrew = plid s t (prm s s t cmst pss)
      prrew = cong (plm t t s cmst) $ prid t t ptt
      congpeq = cong (alpha s t) $ trans prrew $ trans peq (sym plrew)
      nat_s = trans (sym $ nat s s s t (cid s) cmst pss) qlrew
      nat_t = trans (sym qrrew) $ nat t t s t cmst (cid t) ptt
    in
    trans (trans nat_t congpeq) nat_s

-----------------------------
---- Utility profunctors ----
-----------------------------

public export
constProf : (0 d, c : Type) -> Type -> IntProfunctorSig d c
constProf d c x _ _ = x

public export
constDimap : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  (0 x : Type) -> IntDimapSig d c dmor cmor (constProf d c x)
constDimap d c dmor cmor x s t a b dmas cmtb = id {a=x}

public export
terminalProf : (0 d, c : Type) -> IntProfunctorSig d c
terminalProf d c = constProf d c Unit

public export
terminalDimap : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  IntDimapSig d c dmor cmor (terminalProf d c)
terminalDimap d c dmor cmor = constDimap d c dmor cmor Unit

public export
constDi : (0 c : Type) -> (apex : Type) -> IntDifunctorSig c
constDi c = constProf c c

public export
constEndoDimap : (0 c : Type) -> (0 mor : IntDifunctorSig c) ->
  (0 x : Type) -> IntEndoDimapSig c mor (constDi c x)
constEndoDimap c mor = constDimap c c mor mor

-----------------------------
---- Wedges and cowedges ----
-----------------------------

public export
0 IntGenEndBase : (d, c : Type) -> (p : IntProfunctorSig d c) -> Type
IntGenEndBase d c = IntProfNTSig d c (terminalProf d c)

public export
0 IntGenEndBaseIsGenEnd :
  (d, c : Type) -> (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  (0 p : IntProfunctorSig d c) -> (pdm : IntDimapSig d c dmor cmor p) ->
  (endb : IntGenEndBase d c p) -> Type
IntGenEndBaseIsGenEnd d c dmor cmor p =
  IntProfNTNaturality d c dmor cmor
    (terminalProf d c) p (terminalDimap d c dmor cmor)

public export
0 IntEndBase : (c : Type) -> (p : IntDifunctorSig c) -> Type
-- Equivalent to `WedgeBase c Unit`.
-- An `IntGenEndBase c c` can be restricted to an `IntEndBase c p`.
IntEndBase c = IntDiNTSig c (terminalProf c c)

public export
0 WedgeBase :
  (0 c : Type) -> (0 apex : Type) -> (0 p : IntDifunctorSig c) -> Type
WedgeBase c apex p = IntDiNTSig c (constDi c apex) p

public export
0 CowedgeBase :
  (0 c : Type) -> (0 apex : Type) -> (0 p : IntDifunctorSig c) -> Type
CowedgeBase c apex p = IntDiNTSig c p (constDi c apex)

------------------------------------
---- Composition of profunctors ----
------------------------------------

-- The difunctor whose coend is the composition of two profunctors.
public export
IntProCompDi : (0 c, d, e : Type) ->
  (q : IntProfunctorSig e d) ->
  (p : IntProfunctorSig d c) ->
  (i : e) -> (j : c) ->
  IntDifunctorSig d
IntProCompDi c d e q p i j s t = (p s j, q i t)

public export
IntProCompDiDimap : (0 c, d, e : Type) ->
  (cmor : IntDifunctorSig c) ->
  (dmor : IntDifunctorSig d) ->
  (emor : IntDifunctorSig e) ->
  (q : IntProfunctorSig e d) -> (p : IntProfunctorSig d c) ->
  (qrm : IntRmapSig e d emor dmor q) -> (plm : IntLmapSig d c dmor cmor p) ->
  (i : e) -> (j : c) ->
  IntEndoDimapSig d dmor (IntProCompDi c d e q p i j)
IntProCompDiDimap c d e cmor dmor emor q p qrm plm i j s t a b
  dmas dmtb (psj, qit) = (plm s j a dmas psj, qrm i t b dmtb qit)

-- The difunctor whose coend is the composition of two difunctors.
public export
IntDiCompDi : (0 c : Type) -> (q, p : IntDifunctorSig c) -> (a, b : c) ->
  IntDifunctorSig c
IntDiCompDi c = IntProCompDi c c c

public export
IntDiCompDiDimap : (0 c : Type) -> (mor : IntDifunctorSig c) ->
  (q, p : IntDifunctorSig c) ->
  (qrm : IntEndoRmapSig c mor q) -> (plm : IntEndoLmapSig c mor p) ->
  (i, j : c) ->
  IntEndoDimapSig c mor (IntDiCompDi c q p i j)
IntDiCompDiDimap c mor = IntProCompDiDimap c c c mor mor mor

public export
IntProComp : (c, d, e : Type) ->
  (q : IntProfunctorSig e d) ->
  (p : IntProfunctorSig d c) ->
  IntProfunctorSig e c
IntProComp c d e q p i j =
  DPair d $ \x : d => IntProCompDi c d e q p i j x x

public export
IntProCompDimap : (c, d, e : Type) ->
  (cmor : IntDifunctorSig c) ->
  (dmor : IntDifunctorSig d) ->
  (emor : IntDifunctorSig e) ->
  (q : IntProfunctorSig e d) -> (p : IntProfunctorSig d c) ->
  (qlm : IntLmapSig e d emor dmor q) -> (prm : IntRmapSig d c dmor cmor p) ->
  IntDimapSig e c emor cmor (IntProComp c d e q p)
IntProCompDimap c d e cmor dmor emor q p qlm prm s t a b emas cmtb
  (i ** (pit, qsi)) =
    (i ** (prm i t b cmtb pit, qlm s i a emas qsi))

public export
IntDiComp : (c : Type) ->
  (q, p : IntDifunctorSig c) ->
  IntDifunctorSig c
IntDiComp c = IntProComp c c c

public export
IntDiCompDimap : (c : Type) ->
  (cmor : IntDifunctorSig c) ->
  (q, p : IntDifunctorSig c) ->
  (qlm : IntEndoLmapSig c cmor q) -> (prm : IntEndoRmapSig c cmor p) ->
  IntEndoDimapSig c cmor (IntDiComp c q p)
IntDiCompDimap c cmor = IntProCompDimap c c c cmor cmor cmor

-----------------------------------
---- Whiskering of profunctors ----
-----------------------------------

public export
0 IntProfNTwhiskerL : (0 e, d, c : Type) ->
  (0 q, r : IntProfunctorSig e d) ->
  IntProfNTSig e d q r ->
  (p : IntProfunctorSig d c) ->
  IntProfNTSig e c (IntProComp c d e q p) (IntProComp c d e r p)
IntProfNTwhiskerL e d c q r nu p s t (i ** (pit, qsi)) =
  (i ** (pit, nu s i qsi))

public export
0 IntProfNTwhiskerR : (0 e, d, c : Type) ->
  (0 p, q : IntProfunctorSig d c) ->
  (r : IntProfunctorSig e d) ->
  IntProfNTSig d c p q ->
  IntProfNTSig e c (IntProComp c d e r p) (IntProComp c d e r q)
IntProfNTwhiskerR e d c p q r nu s t (i ** (pit, rsi)) =
  (i ** (nu i t pit, rsi))

public export
0 IntProfNThComp : (0 e, d, c : Type) ->
  (0 p, p' : IntProfunctorSig d c) ->
  (0 q, q' : IntProfunctorSig e d) ->
  IntProfNTSig e d q q' ->
  IntProfNTSig d c p p' ->
  IntProfNTSig e c (IntProComp c d e q p) (IntProComp c d e q' p')
IntProfNThComp e d c p p' q q' beta alpha s t =
  IntProfNTwhiskerL e d c q q' beta p' s t .
  IntProfNTwhiskerR e d c p p' q alpha s t

--------------------------------------------------------
--------------------------------------------------------
---- Internal (di/pro-Yoneda) emebddings and lemmas ----
--------------------------------------------------------
--------------------------------------------------------

---------------------------------
---- di-Yoneda (paranatural) ----
---------------------------------

-- Suppose that `c` is a type of objects of a category internal to `Type`,
-- and `mor` is a type dependent on pairs of terms of `c` (we could also
-- express it dually as a `Type` together with morphisms `dom` and `cod` to
-- `c`), which we interpret as _some_ morphisms of the category but not
-- necessarily all.  Then `IntDiYonedaEmbedObj c mor` is the object-map
-- component of the diYoneda embedding (since that embedding is a (di)functor)
-- of the product of the opposite of the internal category and the internal
-- category itself (`op(Type) x Type`) into the category whose objects are
-- difunctors on the internal category -- that is, functors
-- `op(c) -> c -> Type` -- and whose morphisms are paranatural
-- transformations.
public export
IntDiYonedaEmbedObj : (c : Type) ->
  (mor : IntDifunctorSig c) -> c -> c -> IntDifunctorSig c
IntDiYonedaEmbedObj c mor i0 i1 j0 j1 = (mor j0 i1, mor i0 j1)
                       --  d  c  c' d'     c' -> c    d -> d'
                       --  i  j  x  y       x -> j    i -> y
                       --  i0 -> i1 / i -> j  &   j0 -> j1 / x -> y

public export
intDiYoEmbedRL : {c : Type} -> {mor : IntDifunctorSig c} ->
  {i0, i1, j0, j1 : c} -> IntDiYonedaEmbedObj c mor i0 i1 j0 j1 -> mor j0 i1
intDiYoEmbedRL {c} {mor} {i0} {i1} {j0} {j1} = fst

public export
intDiYoEmbedLR : {c : Type} -> {mor : IntDifunctorSig c} ->
  {i0, i1, j0, j1 : c} -> IntDiYonedaEmbedObj c mor i0 i1 j0 j1 -> mor i0 j1
intDiYoEmbedLR {c} {mor} {i0} {i1} {j0} {j1} = snd

---  i0/I/d  j0/x/c' j1/y/d'  i1/J/c
-- 1)  --------------------------> (part of graph object in arena)
-- 2)          ------->            (part of graph object in interpretation)
-- 3)          ------------------> (part of di-Yoneda embedding in interpretation)
-- 4)  --------------->            (part of di-Yoneda embedding in interpretation)
                       -- cob ba            x' : j0 -> j1 (x -> y)
-- When x==y, #2 becomes an automorphism, and it becomes possible to compose
-- #3 . #2 . #4 and assert that that equals #1.
-- This is not a graph because the objects have a d->c rather than a c->d
-- (together with a c'->d').  If we flipped the argument order, then the
-- di-Yoneda morphisms would become cross-category.  It's not a cograph either,
-- for the same reason (there are morphisms going in both directions).  That's
-- what makes it dependent on being a difunctor (an _endo_-profunctor as
-- opposed to just any profunctor).
--
-- To make general profunctors, we can use the existing stuff in `PolyDifunc`,
-- and to make difunctors suited to paranatural transformations, we can use
-- the arrangement of morphisms above.  That arrangement ensures that we can
-- always turn "x"s into "y"s, and thereby define difunctors such as that
-- of wild groups with the likes of associativity included.

-- We now show that for a given `(s, t)` in `opProd(c)`, the diYoneda
-- embedding `IntDiYonedaEmbedObj c mor s t` is a difunctor on `c`.
public export
IntDiYonedaEmbedLmap : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (s, t : c) -> IntEndoLmapSig c mor (IntDiYonedaEmbedObj c mor s t)
IntDiYonedaEmbedLmap c mor comp s t a b i cmia = mapFst $ flip (comp i a t) cmia

public export
IntDiYonedaEmbedRmap : (c : Type) -> (0 mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (s, t : c) -> IntEndoRmapSig c mor (IntDiYonedaEmbedObj c mor s t)
IntDiYonedaEmbedRmap c mor comp s t a b j cmbj = mapSnd $ (comp s b j cmbj)

public export
IntDiYonedaEmbedDimap : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (s, t : c) -> IntEndoDimapSig c mor (IntDiYonedaEmbedObj c mor s t)
IntDiYonedaEmbedDimap c mor comp s t =
  IntEndoDimapFromLRmaps c mor (IntDiYonedaEmbedObj c mor s t)
    (IntDiYonedaEmbedLmap c mor comp s t)
    (IntDiYonedaEmbedRmap c mor comp s t)

public export
IntDiYonedaEmbedMorphNT : (c : Type) ->
  (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (s, t, a, b : c) ->
  IntEndoOpProdCatMor c mor (s, t) (a, b) ->
  IntEndoProfNTSig c
    (IntDiYonedaEmbedObj c mor s t) (IntDiYonedaEmbedObj c mor a b)
IntDiYonedaEmbedMorphNT c mor comp s t a b (mas, mtb) i j (mit, msj) =
  (comp i t b mtb mit, comp a s j msj mas)

-- The morphism-map component of the diYoneda embedding.
-- The domain of that embedding is `opProd(c)`, and the codomain
-- is the category of difunctors on `c` with paranatural transformations,
-- so the morphism-map component takes morphisms of `opProd(c)` to
-- paranatural transformations.
public export
IntDiYonedaEmbedMorph : (c : Type) ->
  (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (s, t, a, b : c) ->
  IntEndoOpProdCatMor c mor (s, t) (a, b) ->
  IntDiNTSig c (IntDiYonedaEmbedObj c mor s t) (IntDiYonedaEmbedObj c mor a b)
IntDiYonedaEmbedMorph c mor comp s t a b (mas, mtb) =
  IntProfNTRestrict c
    (IntDiYonedaEmbedObj c mor s t) (IntDiYonedaEmbedObj c mor a b)
    (IntDiYonedaEmbedMorphNT c mor comp s t a b (mas, mtb))

-- The diYoneda embedding of any morphism of `opProd(c)` is a
-- natural transformation.
public export
0 IntDiYonedaEmbedMorphNatural : (0 c : Type) ->
  (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (assoc : IntAssocSig c mor comp) ->
  (s, t, a, b : c) ->
  (m : IntEndoOpProdCatMor c mor (s, t) (a, b)) ->
  IntProfNTNaturality c c mor mor
    (IntDiYonedaEmbedObj c mor s t) (IntDiYonedaEmbedObj c mor a b)
    (IntEndoDimapFromLRmaps c mor (IntDiYonedaEmbedObj c mor s t)
      (IntDiYonedaEmbedLmap c mor comp s t)
      (IntDiYonedaEmbedRmap c mor comp s t))
    (IntEndoDimapFromLRmaps c mor (IntDiYonedaEmbedObj c mor a b)
      (IntDiYonedaEmbedLmap c mor comp a b)
      (IntDiYonedaEmbedRmap c mor comp a b))
    (IntDiYonedaEmbedMorphNT c mor comp s t a b m)
IntDiYonedaEmbedMorphNatural c mor comp assoc s t a b (mas, mtb) i0 i1 j0 j1
  mj0i0 mi1j1 (mi0t, msi1) =
    pairEqCong
      (rewrite assoc j0 i0 t b mtb mi0t mj0i0 in Refl)
      (rewrite sym (assoc a s i1 j1 mi1j1 msi1 mas) in Refl)

-- The diYoneda embedding of any morphism of `opProd(c)` is a
-- paranatural transformation.
public export
0 IntDiYonedaEmbedMorphPara : (0 c : Type) ->
  (mor : IntDifunctorSig c) -> (0 cid : IntIdSig c mor) ->
  (comp : IntCompSig c mor) ->
  (idl : IntIdLSig c mor comp cid) -> (idr : IntIdRSig c mor comp cid) ->
  (assoc : IntAssocSig c mor comp) ->
  (s, t, a, b : c) ->
  (m : IntEndoOpProdCatMor c mor (s, t) (a, b)) ->
  IntParaNTCond c mor
    (IntDiYonedaEmbedObj c mor s t) (IntDiYonedaEmbedObj c mor a b)
    (IntDiYonedaEmbedLmap c mor comp s t)
    (IntDiYonedaEmbedRmap c mor comp s t)
    (IntDiYonedaEmbedLmap c mor comp a b)
    (IntDiYonedaEmbedRmap c mor comp a b)
    (IntDiYonedaEmbedMorph c mor comp s t a b m)
IntDiYonedaEmbedMorphPara c mor cid comp idl idr assoc s t a b (mas, mtb) =
  IntProfNTRestrictPara c mor cid
    (IntDiYonedaEmbedObj c mor s t) (IntDiYonedaEmbedObj c mor a b)
    (IntDiYonedaEmbedLmap c mor comp s t) (IntDiYonedaEmbedRmap c mor comp s t)
    (IntDiYonedaEmbedLmap c mor comp a b) (IntDiYonedaEmbedRmap c mor comp a b)
    (\i, j, (mit, msj) => pairEqCong (idl i t mit) Refl)
    (\i, j, (mit, msj) => pairEqCong Refl (idr s j msj))
    (\i, j, (mib, maj) => pairEqCong (idl i b mib) Refl)
    (\i, j, (mib, maj) => pairEqCong Refl (idr a j maj))
    (IntDiYonedaEmbedMorphNT c mor comp s t a b (mas, mtb))
    (IntDiYonedaEmbedMorphNatural c mor comp assoc s t a b (mas, mtb))

-- The diYoneda lemma asserts a paranatural isomorphism between two objects
-- of the enriching category, one of which is an object of paranatural
-- transformations.  This type is an explicit name for that object.
-- It is the analogue to the standard form of the Yoneda lemma's "set/object of
-- natural transformations from `Hom(_, a)` to `F`".
--
-- Like any object of natural transformations, this could be expressed
-- as an end.  The end form of this lemma is sometimes called
-- "Yoneda reduction".
public export
IntDiYonedaLemmaNT : (c : Type) -> (mor, p : IntDifunctorSig c) ->
  IntDifunctorSig c
IntDiYonedaLemmaNT c mor p i j =
  IntDiNTSig c (IntDiYonedaEmbedObj c mor j i) p

-- This shows that for a given difunctor `p` on `c`,
-- `IntDiYonedaLemmaNT c mor p` is itself a difunctor
-- (whose value for any `(s, t)` in `opProd(c)` is an object (in `Type`) of
-- paranatural transformations).  That makes it sensible to speak of paranatural
-- transformations between `IntDiYonedaLemmaNT c mor p` and `p`, and
-- the diYoneda lemma exhibits a specific pair of such paranatural
-- transformations, one in each direction, which are inverses to each other.
public export
IntDiYonedaLemmaNTDimap : (0 c : Type) ->
  (0 mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (0 p : IntDifunctorSig c) ->
  IntEndoDimapSig c mor (IntDiYonedaLemmaNT c mor p)
IntDiYonedaLemmaNTDimap c mor comp p s t a b mas mtb embed i (mia, mbi) =
  embed i (comp i a s mas mia, comp t b i mbi mtb)

-- One direction of the paranatural isomorphism asserted by the diYoneda lemma.
public export
IntDiYonedaLemmaL : (0 c : Type) -> (0 mor : IntDifunctorSig c) ->
  (0 p : IntDifunctorSig c) -> (pdm : IntEndoDimapSig c mor p) ->
  IntDiNTSig c p (IntDiYonedaLemmaNT c mor p)
IntDiYonedaLemmaL c mor p pdm i pii j (mji, mij) = pdm i i j j mji mij pii

-- The other direction of the paranatural isomorphism asserted by the
-- diYoneda lemma.
public export
IntDiYonedaLemmaR : (0 c : Type) ->
  (0 mor : IntDifunctorSig c) -> (cid : IntIdSig c mor) ->
  (0 p : IntDifunctorSig c) ->
  IntDiNTSig c (IntDiYonedaLemmaNT c mor p) p
IntDiYonedaLemmaR c mor cid p i embed = embed i (cid i, cid i)

-- The di-co-Yoneda lemma asserts a paranatural isomorphism between two objects
-- of the enriching category, one of which is a coend (existential type).
-- This type is an explicit name for that object.
-- It is the analogue to the standard form of the co-Yoneda lemma's
-- representation of the presheaf embedding of an object as a colimit
-- of representables (the density theorem asserts that such a representation
-- exists for every presheaf).
public export
IntDiCoYonedaLemmaCoendBase : (c : Type) -> (mor : IntDifunctorSig c) ->
  (p : IntDifunctorSig c) -> IntDifunctorSig c
IntDiCoYonedaLemmaCoendBase c mor p i j =
  DPair (c, c) $ \xy =>
    (IntDiYonedaEmbedObj c mor i j (fst xy) (snd xy), flip p (fst xy) (snd xy))

-- This shows that for a given difunctor `p` on `c`,
-- `IntDiCoYonedaLemmaCoendBase c mor p` is itself a difunctor (whose value
-- for any `(s, t)` in `opProd(c)` is a coend representation of a presheaf).
-- That makes it sensible to speak of paranatural transformations between
-- `IntDiCoYonedaLemmaCoendBase c mor p` and `p`, and the di-co-Yoneda lemma
-- exhibits a specific pair of such paranatural transformations, one in each
-- direction, which are inverses to each other.
public export
IntDiYonedaLemmaCoendBaseDimap : (0 c : Type) ->
  (0 mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (0 p : IntDifunctorSig c) ->
  IntEndoDimapSig c mor (IntDiCoYonedaLemmaCoendBase c mor p)
IntDiYonedaLemmaCoendBaseDimap c mor comp p s t a b mas mtb
  (ij ** ((mit, msj), pji)) =
    (ij ** ((comp (fst ij) t b mtb mit, comp a s (snd ij) msj mas), pji))

-- One direction of the paranatural isomorphism asserted by the
-- di-co-Yoneda lemma.
public export
IntDiCoYonedaLemmaL : (0 c : Type) ->
  (0 mor : IntDifunctorSig c) -> (cid : IntIdSig c mor) ->
  (0 p : IntDifunctorSig c) ->
  IntDiNTSig c p (IntDiCoYonedaLemmaCoendBase c mor p)
IntDiCoYonedaLemmaL c mor cid p i pii = ((i, i) ** ((cid i, cid i), pii))

-- The other direction of the paranatural isomorphism asserted by the
-- di-co-Yoneda lemma.
public export
IntDiCoYonedaLemmaR : (0 c : Type) ->
  (0 mor : IntDifunctorSig c) ->
  (0 p : IntDifunctorSig c) -> (pdm : IntEndoDimapSig c mor p) ->
  IntDiNTSig c (IntDiCoYonedaLemmaCoendBase c mor p) p
IntDiCoYonedaLemmaR c mor p pdm x (ij ** ((mix, mxj), pji)) =
  pdm (snd ij) (fst ij) x x mxj mix pji

--------------------------------------------
--------------------------------------------
---- Metalanguage profunctor signatures ----
--------------------------------------------
--------------------------------------------

public export
TypeDimap : {0 p : ProfunctorSig} ->
  DimapSig p -> IntEndoDimapSig TypeObj TypeMor p
TypeDimap {p} dm _ _ _ _ = dm

public export
TypeProfDimap : {0 p : ProfunctorSig} ->
  Profunctor p -> IntEndoDimapSig TypeObj TypeMor p
TypeProfDimap {p} isP = TypeDimap {p} (dimap {f=p})

--------------------------------------------------
--------------------------------------------------
---- (Para-)natural transformations on `Type` ----
--------------------------------------------------
--------------------------------------------------

-- The following categories are equivalent:
--
--  1) the splice category of `Type` over `(i, j)`
--  2) the category of profunctors `i -> j`, AKA functors `(op(j), i) -> Type`,
--    where `i` and `j` are viewed as discrete categories, and the morphisms
--    are paranatural transformations
--  3) the category of diagonal elements of the profunctor di-represented by
--    `(i, j)`, i.e. `DiYoneda i j`
--  4) the category of polynomial difunctors (endo-profunctors) on
--     `(op(Type), Type)` with position-set `(j, i)` (i.e. contravariant
--     position-set `j` and covariant position-set `i`), with paranatural
--     transformations as morphisms
--
-- (I expect, but have not proven, that the category of profunctors `j -> i`
-- (AKA functors `(op(i), j) -> Type` where `i` and `j` are viewed as
-- discrete categories) with _natural_ transformations, as opposed to the
-- more general _paranatural_ transformations, as morphisms is equivalent to
-- the category of _elements_, as opposed to the category of _diagonal_
-- elements, of the profunctor _represented_, as opposed to _direpresented_, by
-- `(i, j)`, i.e. `PrePostPair i j` (the (contravariant x covariant) Yoneda
-- embedding of `(i, j)`) or `Iso i j` (the (covariant x contravariant) Yoneda
-- embedding of `(i, j`)).  I further expect that it is probably equivalent to
-- the slice category of `Type` over `(i, j)`, and to the category
-- of polynomial difunctors (endo-profunctors) on `Type` with position-set
-- `(i, j)` with _natural_ (not just paranatural) transformations as morphisms.)
--
-- This is analogous to how the following are equivalent:
--
--  1) the slice category of `Type` over `j`
--  2) the category of presheaves over `j`, AKA functors `op(j) -> Type`,
--    where `j` is viewed as a discrete category, and the morphisms
--    are natural transformations
--  3) the category of elements of the presheaf represented by `j`,
--    i.e. the contravariant Yoneda embedding of `j`
--  4) the category of Dirichlet endofunctors on `Type` with position-set `j`
--  5) the opposite of the category of polynomial endofunctors on `Type` with
--     position-set `j`
--
-- And dually:
--
--  1) the coslice category of `Type` over `i`
--  2) the category of copresheaves over `i`, AKA functors `i -> Type`,
--    where `i` is viewed as a discrete category, and the morphisms
--    are natural transformations
--  3) the category of elements of the copresheaf represented by `i`,
--    i.e. the covariant Yoneda embedding of `i`
--  4) the category of Dirichlet endofunctors on `op(Type)` with
--     position-set `i`
--  5) the opposite of the category of polynomial endofunctors on `op(Type)`
--     with position-set `i`
--
-- The splice version unifies the two duals.
--
-- Given an object in a splice category over `(i, j)`, with intermediate
-- object `k`, injection `into : i -> k`, and projection `from : k -> j`,
-- where we shall refer to the composition `from . into : i -> j` as `comp`,
-- we can form objects of other splice categories in the following ways (which
-- are functorial, so we are saying that there are the following functors
-- between splice categories):
--
--  1) Given morphisms `f : x -> i` and `g : j -> y`, we can form an object
--     of the splice category over `(x, y)` with intermediate object `k` by
--     composing `f` before `into` and `g` after `from`.  Note that
--     `(f, g)` is a morphism from `(i, j)` to `(x, y)` in `(op(Type), Type)`.
--     This is the sigma functor between splice categories.  Note that `(f, g)`
--     may equivalently be seen as `DiYoneda x y j i`, or `PrePostPair i j x y`,
--     or `Iso x y i j`.  The intermediate object is still `k`.

-- See https://arxiv.org/abs/2307.09289 .

-- `DiYonedaEmbed` is sometimes written `yy(i0, i1)` .  It embeds
-- the object `(i0, i1)` of `(op(Type), Type)` into the category
-- whose objects are profunctors `(op(Type), Type) -> Type)` and whose
-- morphisms are _paranatural_ transformations (compare to `DualYonedaEmbed`,
-- where the codomain category's objects are the same, but the morphisms are
-- the more strict _natural_ transformations).
--
-- Note that `DiYonedaEmbed Void i1` is the profunctor which ignores its
-- second argument and acts as `ContravarHomFunc i1` on its first argument,
-- whereas `DiYonedaEmbed i0 Unit` is the profunctor which ignores its first
-- argument and acts as `CovarHomFunc i0` on its second argument.  So
-- `DiYonedaEmbed Void` is effectively the contravariant Yoneda embedding
-- on `Type`, while `flip DiYonedaEmbed Unit` is effectively the covariant
-- Yoneda embedding on `Type`.

---------------------------------
---- di-Yoneda (paranatural) ----
---------------------------------

-- `Type` itself is a category internal to `Type`, so we may define the
-- diYoneda embedding of `Type` as a specialization of the internal diYoneda
-- embedding with `Type` as `obj` and `HomProf` as `mor`.
public export
DiYonedaEmbed : Type -> Type -> ProfunctorSig
DiYonedaEmbed = IntDiYonedaEmbedObj Type HomProf

public export
0 DiYonedaEmbedProf : (i, j : Type) -> Profunctor (DiYonedaEmbed i j)
DiYonedaEmbedProf i j =
  MkProfunctor $ IntDiYonedaEmbedDimap Type HomProf typeComp _ _ _ _ _ _

-- The diYoneda lemma asserts a paranatural isomorphism between two objects
-- of the enriching category, one of which is an object of paranatural
-- transformations.  This type is an explicit name for that object on
-- the category `(op(Type), Type)`.
public export
DiYonedaLemmaNT : ProfunctorSig -> ProfunctorSig
DiYonedaLemmaNT = IntDiYonedaLemmaNT Type HomProf

{-
 - The current usages don't work out to define this.
public export
DiYonedaLemmaNTPro : Profunctor (flip $ DiYonedaLemmaNT p)
DiYonedaLemmaNTPro {p} = MkProfunctor $
  IntDiYonedaLemmaNTDimap Type HomProf typeComp p _ _ _ _
 -}

-- One direction of the paranatural isomorphism asserted by the
-- diYoneda lemma on `(op(Type), Type)`.
public export
DiYonedaLemmaL : (0 p : ProfunctorSig) -> {auto isP : Profunctor p} ->
  ProfDiNT p (DiYonedaLemmaNT p)
DiYonedaLemmaL p {isP} = IntDiYonedaLemmaL Type HomProf p (TypeProfDimap isP)

-- The other direction of the paranatural isomorphism asserted by the
-- diYoneda lemma on `(op(Type), Type)`.
public export
0 DiYonedaLemmaR : (0 p : ProfunctorSig) ->
  ProfDiNT (DiYonedaLemmaNT p) p
DiYonedaLemmaR = IntDiYonedaLemmaR Type HomProf typeId

-- The di-co-Yoneda lemma asserts a paranatural isomorphism between two objects
-- of the enriching category, one of which is a coend (existential type).
-- This type is an explicit name for that object on the category
-- `(op(Type), Type)`.
public export
DiCoYonedaLemmaCoend : ProfunctorSig -> ProfunctorSig
DiCoYonedaLemmaCoend = IntDiCoYonedaLemmaCoendBase Type HomProf

{-
 - The current usages don't work out to define this.
public export
Profunctor (DiCoYonedaLemmaCoend p) where
  dimap {p} = IntDiYonedaLemmaCoendBaseDimap Type HomProf typeComp p _ _ _ _
 -}

-- One direction of the paranatural isomorphism asserted by the
-- di-co-Yoneda lemma on `(op(Type), Type)`.
public export
0 DiCoYonedaLemmaL : (0 p : ProfunctorSig) ->
  ProfDiNT p (DiCoYonedaLemmaCoend p)
DiCoYonedaLemmaL = IntDiCoYonedaLemmaL Type HomProf typeId

-- The other direction of the paranatural isomorphism asserted by the
-- di-co-Yoneda lemma on `(op(Type), Type)`.
public export
DiCoYonedaLemmaR : (0 p : ProfunctorSig) -> {auto isP : Profunctor p} ->
  ProfDiNT (DiCoYonedaLemmaCoend p) p
DiCoYonedaLemmaR p {isP} =
  IntDiCoYonedaLemmaR Type HomProf p (TypeProfDimap isP)

-----------------------------------------------
-----------------------------------------------
---- Internal Yoneda emebddings and lemmas ----
-----------------------------------------------
-----------------------------------------------

-- The object-map component of the (contravariant) Yoneda embedding of
-- `op(c)` into the category of the (covariant) copresheaves on `c`.
IntCopreshfYonedaEmbedObj : (0 c : Type) -> (mor : IntMorSig c) ->
  c -> (IntCopreshfSig c)
IntCopreshfYonedaEmbedObj c mor = mor

-- The object-map component of the (covariant) Yoneda embedding of
-- `c` into the category of the (contravariant) presheaves on `c`.
IntPreshfYonedaEmbedObj : (0 c : Type) -> (mor : IntMorSig c) ->
  c -> (IntPreshfSig c)
IntPreshfYonedaEmbedObj c mor = flip mor

-- The morphism-map component of the (contravariant) Yoneda embedding of
-- an object of `op(c)` into the category of the (covariant) copresheaves on `c`
-- (since the embedding of that object is a functor, it has a morphism-map
-- component as well as an object-map component).
IntCopreshfYonedaEmbedObjFMap : (0 c : Type) -> (mor : IntMorSig c) ->
  (comp : IntCompSig c mor) ->
  (a : c) -> IntCopreshfMapSig c mor (IntCopreshfYonedaEmbedObj c mor a)
IntCopreshfYonedaEmbedObjFMap c mor comp a x y = comp a x y

-- The morphism-map component of the (covariant) Yoneda embedding of
-- an object of `c` into the category of the (contravariant) presheaves on `c`
-- (since the embedding of that object is a functor, it has a morphism-map
-- component as well as an object-map component).
IntPreshfYonedaEmbedObjFMap : (0 c : Type) -> (mor : IntMorSig c) ->
  (comp : IntCompSig c mor) ->
  (a : c) -> IntPreshfMapSig c mor (IntPreshfYonedaEmbedObj c mor a)
IntPreshfYonedaEmbedObjFMap c mor comp a x y = flip $ comp y x a

-- The morphism-map component of the (contravariant) Yoneda embedding itself --
-- that is, the embedding of a _morphism_ into the morphisms of the
-- (covariant) copresheaves on `c`, which are natural transformations.
IntCopreshfYonedaEmbedMor : (c : Type) -> (mor : IntMorSig c) ->
  (comp : IntCompSig c mor) ->
  (a, b : c) -> mor b a ->
  IntCopreshfNTSig c
    (IntCopreshfYonedaEmbedObj c mor a)
    (IntCopreshfYonedaEmbedObj c mor b)
IntCopreshfYonedaEmbedMor c mor comp a b mba x max = comp b a x max mba

-- The morphism-map component of the (covariant) Yoneda embedding itself --
-- that is, the embedding of a _morphism_ into the morphisms of the
-- (contravariant) presheaves on `c`, which are natural transformations.
IntPreshfYonedaEmbedMor : (c : Type) -> (mor : IntMorSig c) ->
  (comp : IntCompSig c mor) ->
  (a, b : c) -> mor a b ->
  IntPreshfNTSig c
    (IntPreshfYonedaEmbedObj c mor a)
    (IntPreshfYonedaEmbedObj c mor b)
IntPreshfYonedaEmbedMor c mor comp a b mab x mxa = comp x a b mab mxa

-- The inverse of the morphism-map component of the (contravariant) Yoneda
-- embedding.  The existence of this inverse shows that the embedding
-- is fully faithful.
IntCopreshfYonedaEmbedMorInv : (0 c : Type) -> (mor : IntMorSig c) ->
  (cid : IntIdSig c mor) ->
  (a, b : c) ->
  IntCopreshfNTSig c
    (IntCopreshfYonedaEmbedObj c mor a)
    (IntCopreshfYonedaEmbedObj c mor b) ->
  mor b a
IntCopreshfYonedaEmbedMorInv c mor cid a b alpha = alpha a (cid a)

-- The inverse of the morphism-map component of the (covariant) Yoneda
-- embedding.  The existence of this inverse shows that the embedding
-- is fully faithful.
IntPreshfYonedaEmbedMorInv : (0 c : Type) -> (mor : IntMorSig c) ->
  (cid : IntIdSig c mor) ->
  (a, b : c) ->
  IntPreshfNTSig c
    (IntPreshfYonedaEmbedObj c mor a)
    (IntPreshfYonedaEmbedObj c mor b) ->
  mor a b
IntPreshfYonedaEmbedMorInv c mor cid a b alpha = alpha a (cid a)

------------------------------------------------
------------------------------------------------
---- (Co)presheaves over various categories ----
------------------------------------------------
------------------------------------------------

---------------------------------------------------------------
---- Over a discrete category (equivalent to `SliceObj c`) ----
---------------------------------------------------------------

public export
0 DiscretePreshfSig : Type -> Type
DiscretePreshfSig obj = IntPreshfSig $ DiscreteCatObj obj

public export
0 DiscretePreshfMapSig : {0 obj : Type} -> DiscretePreshfSig obj -> Type
DiscretePreshfMapSig {obj} =
  IntPreshfMapSig (DiscreteCatObj obj) (DiscreteCatMor {obj})

public export
0 DiscretePreshfNTSig : {0 obj : Type} -> (f, g : DiscretePreshfSig obj) -> Type
DiscretePreshfNTSig {obj} = IntPreshfNTSig (DiscreteCatObj obj)

public export
0 DiscretePreshfNTNaturality : {0 obj : Type} ->
  (0 f, g : DiscretePreshfSig obj) ->
  (fcm : DiscretePreshfMapSig {obj} f) ->
  (gcm : DiscretePreshfMapSig {obj} g) ->
  (alpha : DiscretePreshfNTSig {obj} f g) -> Type
DiscretePreshfNTNaturality {obj} =
  IntPreshfNTNaturality (DiscreteCatObj obj) (DiscreteCatMor {obj})

-- The category of presheaves over a discrete category with objects
-- drawn from `c` is equivalent to `SliceObj c`.
public export
DiscPreToSl : {0 obj : Type} -> DiscretePreshfSig obj -> SliceObj obj
DiscPreToSl {obj} = id

public export
DiscPreFromSl : {0 obj : Type} -> SliceObj obj -> DiscretePreshfSig obj
DiscPreFromSl {obj} = id

public export
DiscPreUniqueMapSig : {0 obj : Type} -> (0 f : DiscretePreshfSig obj) ->
  DiscretePreshfMapSig {obj} f
DiscPreUniqueMapSig f x x (DCid x) = id

public export
DiscPreNTtoSl : {0 obj : Type} ->
  (0 f, g : DiscretePreshfSig obj) -> DiscretePreshfNTSig {obj} f g ->
  SliceMorphism {a=obj} (DiscPreToSl {obj} f) (DiscPreToSl {obj} g)
DiscPreNTtoSl {obj} f g = id

public export
SlToDiscPreNT : {0 obj : Type} -> (0 x, y : SliceObj obj) ->
  SliceMorphism {a=obj} x y ->
  DiscretePreshfNTSig {obj} (DiscPreFromSl {obj} x) (DiscPreFromSl {obj} y)
SlToDiscPreNT {obj} x y = id

public export
SlToDiscPreNTnaturality : {0 obj : Type} -> (0 x, y : SliceObj obj) ->
  (f : SliceMorphism {a=obj} x y) ->
  DiscretePreshfNTNaturality {obj}
    (DiscPreFromSl {obj} x) (DiscPreFromSl {obj} y)
    (DiscPreUniqueMapSig {obj} $ DiscPreFromSl {obj} x)
    (DiscPreUniqueMapSig {obj} $ DiscPreFromSl {obj} y)
    (SlToDiscPreNT {obj} x y f)
SlToDiscPreNTnaturality {obj} x y f a a (DCid a) ex = Refl

-----------------------------------------------------------
---- Over the terminal category (equivalent to `Type`) ----
-----------------------------------------------------------

public export
0 TerminalPreshfSig : Type
TerminalPreshfSig = IntPreshfSig TerminalCatObj

public export
0 TerminalPreshfMapSig : TerminalPreshfSig -> Type
TerminalPreshfMapSig = IntPreshfMapSig TerminalCatObj TerminalCatMor

public export
0 TerminalPreshfNTSig : (f, g : TerminalPreshfSig) -> Type
TerminalPreshfNTSig = IntPreshfNTSig TerminalCatObj

public export
0 TerminalPreshfNTNaturality : (0 f, g : TerminalPreshfSig) ->
  (fcm : TerminalPreshfMapSig f) -> (gcm : TerminalPreshfMapSig g) ->
  (alpha : TerminalPreshfNTSig f g) -> Type
TerminalPreshfNTNaturality = IntPreshfNTNaturality TerminalCatObj TerminalCatMor

-- The category of presheaves over the terminal category is equivalent to
-- simply `Type`.
public export
TPreToType : TerminalPreshfSig -> Type
TPreToType p = p ()

public export
TPreFromType : Type -> TerminalPreshfSig
TPreFromType ty = const ty

public export
TPreUniqueMapSig : (0 x : TerminalPreshfSig) -> TerminalPreshfMapSig x
TPreUniqueMapSig x () () (DCid ()) = id

public export
TPreNTtoType : (0 f, g : TerminalPreshfSig) -> TerminalPreshfNTSig f g ->
  TPreToType f -> TPreToType g
TPreNTtoType f g alpha = alpha ()

public export
TypeToTPreNT : (0 x, y : Type) -> (x -> y) ->
  TerminalPreshfNTSig (TPreFromType x) (TPreFromType y)
TypeToTPreNT x y f () = f

public export
TypeToTPreNTnaturality : (0 x, y : Type) -> (f : x -> y) ->
  TerminalPreshfNTNaturality
    (TPreFromType x) (TPreFromType y)
    (TPreUniqueMapSig $ TPreFromType x) (TPreUniqueMapSig $ TPreFromType y)
    (TypeToTPreNT x y f)
TypeToTPreNTnaturality x y f () () (DCid ()) ex = Refl

-----------------------------------------
-----------------------------------------
---- Internal polynomial profunctors ----
-----------------------------------------
-----------------------------------------

---------------------------
---- Profunctor arenas ----
---------------------------

public export
IntProAr : (d, c : Type) -> Type
IntProAr d c = (pos : Type ** (pos -> d, pos -> c))

public export
IntEndoProAr : (c : Type) -> Type
IntEndoProAr c = IntProAr c c

public export
ipaPos : {d, c : Type} -> IntProAr d c -> Type
ipaPos = DPair.fst

public export
ipaContra : {d, c : Type} -> (ar : IntProAr d c) -> ipaPos ar -> d
ipaContra ar = Builtin.fst $ DPair.snd ar

public export
ipaCovar : {d, c : Type} -> (ar : IntProAr d c) -> ipaPos ar -> c
ipaCovar ar = Builtin.snd $ DPair.snd ar

public export
ipaProj : {d, c : Type} -> (ar : IntProAr d c) -> ipaPos ar -> IntProAr d c
ipaProj ar i = (Unit ** (\_ => ipaContra ar i, \_ => ipaCovar ar i))

public export
ipaFlip : {d, c : Type} -> IntProAr d c -> IntProAr c d
ipaFlip {d} {c} ar = (ipaPos ar ** (ipaCovar ar, ipaContra ar))

public export
iepaFlip : {c : Type} -> IntEndoProAr c -> IntEndoProAr c
iepaFlip {c} = ipaFlip {c} {d=c}

public export
IEPAssignPos : {c : Type} ->
  IntDifunctorSig c -> (ar : IntEndoProAr c) -> ipaPos ar -> Type
IEPAssignPos {c} mor ar i =
  mor (ipaCovar {d=c} {c} ar i) (ipaContra {d=c} {c} ar i)

public export
IEPAssign : {c : Type} -> IntDifunctorSig c -> IntEndoProAr c -> Type
IEPAssign {c} mor ar = (i : ipaPos ar) -> IEPAssignPos {c} mor ar i

-----------------------------------------
---- Profunctor arena interpretation ----
-----------------------------------------

public export
InterpIPPobj : (d, c : Type) ->
  (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  IntProAr d c -> d -> c -> Type
InterpIPPobj d c dmor cmor p a b =
   (i : fst p ** (dmor a (fst (snd p) i), cmor (snd (snd p) i) b))

public export
InterpIEPPobj : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntEndoProAr c -> c -> c -> Type
InterpIEPPobj c mor = InterpIPPobj c c mor mor

public export
InterpIPPlmap : (d, c : Type) ->
  (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  (dcomp : IntCompSig d dmor) -> (ccomp : IntCompSig c cmor) ->
  (ar : IntProAr d c) ->
  IntLmapSig d c dmor cmor (InterpIPPobj d c dmor cmor ar)
InterpIPPlmap d c dmor cmor dcomp ccomp p s t a dmas el =
    (fst el **
     (dcomp a s (fst (snd p) (fst el)) (fst $ snd el) dmas,
      snd $ snd el))

public export
InterpIPPrmap : (d, c : Type) ->
  (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  (dcomp : IntCompSig d dmor) -> (ccomp : IntCompSig c cmor) ->
  (ar : IntProAr d c) ->
  IntRmapSig d c dmor cmor (InterpIPPobj d c dmor cmor ar)
InterpIPPrmap d c dmor cmor dcomp ccomp p s t b cmtb el =
    (fst el **
     (fst $ snd el,
      ccomp (snd (snd p) (fst el)) t b cmtb (snd $ snd el)))

public export
InterpIPPdimap : (d, c : Type) ->
  (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  (dcomp : IntCompSig d dmor) -> (ccomp : IntCompSig c cmor) ->
  (ar : IntProAr d c) ->
  IntDimapSig d c dmor cmor (InterpIPPobj d c dmor cmor ar)
InterpIPPdimap d c dmor cmor dcomp ccomp p s t a b dmas cmtb =
  InterpIPPlmap d c dmor cmor dcomp ccomp p s b a dmas
  . InterpIPPrmap d c dmor cmor dcomp ccomp p s t b cmtb

public export
InterpIEPPdimap : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (ar : IntEndoProAr c) ->
  IntEndoDimapSig c mor (InterpIEPPobj c mor ar)
InterpIEPPdimap c mor comp = InterpIPPdimap c c mor mor comp comp

public export
InterpIEPPlmap : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (ar : IntEndoProAr c) ->
  IntEndoLmapSig c mor (InterpIEPPobj c mor ar)
InterpIEPPlmap c mor comp = InterpIPPlmap c c mor mor comp comp

public export
InterpIEPPrmap : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (ar : IntEndoProAr c) ->
  IntEndoRmapSig c mor (InterpIEPPobj c mor ar)
InterpIEPPrmap c mor comp = InterpIPPrmap c c mor mor comp comp

-----------------------------------------
---- Profunctor arena id/composition ----
-----------------------------------------

public export
IntProArId : (c : Type) -> IntEndoProAr c
IntProArId c = (c ** (id, id))

public export
IntProArComp : (e, d, c : Type) -> (dmor : IntDifunctorSig d) ->
  IntProAr e d -> IntProAr d c -> IntProAr e c
IntProArComp e d c dmor q p =
  ((pi : ipaPos p ** qi : ipaPos q ** dmor (ipaCovar q qi) (ipaContra p pi)) **
   (\pqm => ipaContra q (fst $ snd pqm), \pqm => ipaCovar p (fst pqm)))

public export
IntEndoProArComp : (c : Type) -> (cmor : IntDifunctorSig c) ->
  IntEndoProAr c -> IntEndoProAr c -> IntEndoProAr c
IntEndoProArComp c cmor = IntProArComp c c c cmor

public export
IntDiArComp : (c : Type) -> (cmor : IntDifunctorSig c) ->
  IntEndoProAr c -> IntEndoProAr c -> IntEndoProAr c
IntDiArComp c = IntProArComp c c c

--------------------------------------------
---- Profunctor natural transformations ----
--------------------------------------------

public export
IntPPNTpos : {d, c : Type} ->
  {cmor : IntDifunctorSig c} -> {dmor : IntDifunctorSig d} ->
  (p, q : IntProAr d c) -> Type
IntPPNTpos {d} {c} {dmor} {cmor} p q = ipaPos p -> ipaPos q

public export
IntPPNTcontra : {d, c : Type} ->
  {dmor : IntDifunctorSig d} -> {cmor : IntDifunctorSig c} ->
  (p, q : IntProAr d c) -> IntPPNTpos {d} {c} {dmor} {cmor} p q -> Type
IntPPNTcontra {d} {c} {dmor} {cmor} p q onpos =
   (i : ipaPos p) -> dmor (ipaContra p i) (ipaContra q $ onpos i)

public export
IntPPNTcovar : {d, c : Type} ->
  {dmor : IntDifunctorSig d} -> {cmor : IntDifunctorSig c} ->
  (p, q : IntProAr d c) -> IntPPNTpos {d} {c} {dmor} {cmor} p q -> Type
IntPPNTcovar {d} {c} {dmor} {cmor} p q onpos =
   (i : ipaPos p) -> cmor (ipaCovar q $ onpos i) (ipaCovar p i)

public export
IntPPNTar : (d, c : Type) ->
  (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  IntProAr d c -> IntProAr d c -> Type
IntPPNTar d c dmor cmor p q =
  (onpos : IntPPNTpos {d} {c} {dmor} {cmor} p q **
   (IntPPNTcontra {d} {c} {dmor} {cmor} p q onpos,
    IntPPNTcovar {d} {c} {dmor} {cmor} p q onpos))

public export
intPPNTpos : {d, c : Type} ->
  {dmor : IntDifunctorSig d} -> {cmor : IntDifunctorSig c} ->
  {p, q : IntProAr d c} ->
  IntPPNTar d c dmor cmor p q -> IntPPNTpos {d} {c} {dmor} {cmor} p q
intPPNTpos {d} {c} {dmor} {cmor} {p} {q} = DPair.fst

public export
intPPNTcontra : {d, c : Type} ->
  {dmor : IntDifunctorSig d} -> {cmor : IntDifunctorSig c} ->
  {p, q : IntProAr d c} ->
  (ar : IntPPNTar d c dmor cmor p q) ->
  IntPPNTcontra {d} {c} {dmor} {cmor} p q $
    intPPNTpos {d} {c} {dmor} {cmor} {p} {q} ar
intPPNTcontra {d} {c} {dmor} {cmor} {p} {q} ar = Builtin.fst $ DPair.snd ar

public export
intPPNTcovar : {d, c : Type} ->
  {dmor : IntDifunctorSig d} -> {cmor : IntDifunctorSig c} ->
  {p, q : IntProAr d c} ->
  (ar : IntPPNTar d c dmor cmor p q) ->
  IntPPNTcovar {d} {c} {dmor} {cmor} p q $
    intPPNTpos {d} {c} {dmor} {cmor} {p} {q} ar
intPPNTcovar {d} {c} {dmor} {cmor} {p} {q} ar = Builtin.snd $ DPair.snd ar

public export
InterpIPPnt : (d, c : Type) ->
  (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  (dcomp : IntCompSig d dmor) -> (ccomp : IntCompSig c cmor) ->
  (p, q : IntProAr d c) -> IntPPNTar d c dmor cmor p q ->
  IntProfNTSig d c (InterpIPPobj d c dmor cmor p) (InterpIPPobj d c dmor cmor q)
InterpIPPnt d c dmor cmor dcomp ccomp
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar))
  (onpos ** (dcontra, dcovar)) a b (i ** (dmax, cmyb)) =
    (onpos i **
     (dcomp a (pcontra i) (qcontra (onpos i)) (dcontra i) dmax,
      ccomp (qcovar (onpos i)) (pcovar i) b cmyb (dcovar i)))

public export
0 InterpIPPntNatural : (d, c : Type) ->
  (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  (dcomp : IntCompSig d dmor) -> (ccomp : IntCompSig c cmor) ->
  (dassoc : IntAssocSig d dmor dcomp) ->
  (cassoc : IntAssocSig c cmor ccomp) ->
  (p, q : IntProAr d c) -> (ar : IntPPNTar d c dmor cmor p q) ->
  IntProfNTNaturality d c dmor cmor
    (InterpIPPobj d c dmor cmor p)
    (InterpIPPobj d c dmor cmor q)
    (InterpIPPdimap d c dmor cmor dcomp ccomp p)
    (InterpIPPdimap d c dmor cmor dcomp ccomp q)
    (InterpIPPnt d c dmor cmor dcomp ccomp p q ar)
InterpIPPntNatural d c dmor cmor dcomp ccomp dassoc cassoc
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar))
  (onpos ** (dcontra, dcovar)) s t a b dmas cmtb (i ** (dmsp, cmpt)) =
    dpEq12
      Refl
      $ pairEqCong
        (dassoc a s (pcontra i) (qcontra (onpos i)) (dcontra i) dmsp dmas)
        (sym $ cassoc (qcovar $ onpos i) (pcovar i) t b cmtb cmpt (dcovar i))

public export
IntEPPNTar : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntEndoProAr c -> IntEndoProAr c -> Type
IntEPPNTar c mor = IntPPNTar c c mor mor

public export
InterpIEPPnt : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (p, q : IntEndoProAr c) -> IntEPPNTar c mor p q ->
  IntEndoProfNTSig c (InterpIEPPobj c mor p) (InterpIEPPobj c mor q)
InterpIEPPnt c mor comp = InterpIPPnt c c mor mor comp comp

public export
intPPNTid :
  (d, c : Type) -> (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  (did : IntIdSig d dmor) -> (cid : IntIdSig c cmor) ->
  (p : IntProAr d c) -> IntPPNTar d c dmor cmor p p
intPPNTid d c dmor cmor did cid (ppos ** (pcontra, pcovar)) =
  (id ** (\i => did (pcontra i), \i => cid (pcovar i)))

public export
intPPNTvcomp : (d, c : Type) ->
  (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  (dcomp : IntCompSig d dmor) -> (ccomp : IntCompSig c cmor) ->
  (p, q, r : IntProAr d c) ->
  IntPPNTar d c dmor cmor q r ->
  IntPPNTar d c dmor cmor p q ->
  IntPPNTar d c dmor cmor p r
intPPNTvcomp d c dmor cmor dcomp ccomp
  (ppos ** (pcontra, pcovar))
  (qpos ** (qcontra, qcovar))
  (rpos ** (rcontra, rcovar))
  (bonpos ** (bcontra, bcovar))
  (aonpos ** (acontra, acovar)) =
    (bonpos . aonpos **
     (\i =>
        dcomp (pcontra i) (qcontra (aonpos i)) (rcontra (bonpos (aonpos i)))
          (bcontra (aonpos i))
          (acontra i),
      \i =>
        ccomp (rcovar (bonpos (aonpos i))) (qcovar (aonpos i)) (pcovar i)
          (acovar i)
          (bcovar (aonpos i))))

public export
intPPNThcomp :
  (e, d, c : Type) ->
  (emor : IntDifunctorSig e) ->
  (dmor : IntDifunctorSig d) ->
  (cmor : IntDifunctorSig c) ->
  (dcomp : IntCompSig d dmor) ->
  (p, p' : IntProAr d c) ->
  (q, q' : IntProAr e d) ->
  IntPPNTar e d emor dmor q q' ->
  IntPPNTar d c dmor cmor p p' ->
  IntPPNTar e c emor cmor
    (IntProArComp e d c dmor q p)
    (IntProArComp e d c dmor q' p')
intPPNThcomp e d c emor dmor cmor dcomp
  (ppos ** (pcont, pcovar))
  (p'pos ** (p'cont, p'covar))
  (qpos ** (qcont, qcovar))
  (q'pos ** (q'cont, q'covar))
  (bonpos ** (boncont, boncovar))
  (aonpos ** (aoncont, aoncovar)) =
    (\(pi ** qi ** m) =>
      (aonpos pi **
       bonpos qi **
       dcomp (q'covar $ bonpos qi) (pcont pi) (p'cont $ aonpos pi) (aoncont pi)
        $ dcomp (q'covar $ bonpos qi) (qcovar qi) (pcont pi) m (boncovar qi)) **
     (\(pi ** qi ** m) => boncont qi,
      \(pi ** qi ** m) => aoncovar pi))

----------------------------------------------------
---- Profunctor di/para-natural transformations ----
----------------------------------------------------

public export
IntPDiNTpos : {c : Type} -> {mor : IntDifunctorSig c} ->
  (p, q : IntEndoProAr c) -> Type
IntPDiNTpos {c} {mor} p q = (i : ipaPos p) -> IEPAssignPos mor p i -> ipaPos q

public export
IntPDiNTcontra : {c : Type} -> {mor : IntDifunctorSig c} ->
  (p, q : IntEndoProAr c) -> IntPDiNTpos {c} {mor} p q -> Type
IntPDiNTcontra {c} {mor} p q onpos =
   (i : ipaPos p) -> (asn : IEPAssignPos mor p i) ->
   mor (ipaContra p i) (ipaContra q $ onpos i asn)

public export
IntPDiNTcovar : {c : Type} -> {mor : IntDifunctorSig c} ->
  (p, q : IntEndoProAr c) -> IntPDiNTpos {c} {mor} p q -> Type
IntPDiNTcovar {c} {mor} p q onpos =
   (i : ipaPos p) -> (asn : IEPAssignPos mor p i) ->
   mor (ipaCovar q $ onpos i asn) (ipaCovar p i)

public export
IntPDiNTar : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntEndoProAr c -> IntEndoProAr c -> Type
IntPDiNTar c mor p q =
  (onpos : IntPDiNTpos {c} {mor} p q **
   (IntPDiNTcontra {c} {mor} p q onpos,
    IntPDiNTcovar {c} {mor} p q onpos))

public export
intPDiNTpos : {c : Type} -> {mor : IntDifunctorSig c} ->
  {p, q : IntEndoProAr c} ->
  IntPDiNTar c mor p q -> IntPDiNTpos {c} {mor} p q
intPDiNTpos {c} {mor} {p} {q} = DPair.fst

public export
intPDiNTcontra : {c : Type} -> {mor : IntDifunctorSig c} ->
  {p, q : IntEndoProAr c} ->
  (ar : IntPDiNTar c mor p q) ->
  IntPDiNTcontra {c} {mor} p q (intPDiNTpos {c} {mor} {p} {q} ar)
intPDiNTcontra {c} {mor} {p} {q} ar = Builtin.fst $ DPair.snd ar

public export
intPDiNTcovar : {c : Type} -> {mor : IntDifunctorSig c} ->
  {p, q : IntEndoProAr c} ->
  (ar : IntPDiNTar c mor p q) ->
  IntPDiNTcovar {c} {mor} p q (intPDiNTpos {c} {mor} {p} {q} ar)
intPDiNTcovar {c} {mor} {p} {q} ar = Builtin.snd $ DPair.snd ar

public export
InterpIEPPdint : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (p, q : IntEndoProAr c) -> IntPDiNTar c mor p q ->
  IntDiNTSig c (InterpIEPPobj c mor p) (InterpIEPPobj c mor q)
InterpIEPPdint c mor comp
  (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar))
  (onpos ** (dcontra, dcovar)) a (i ** (cmax, cmya)) =
    let
      passign : mor (pcovar i) (pcontra i) =
        comp (pcovar i) a (pcontra i) cmax cmya
    in
    (onpos i passign **
     (comp a (pcontra i) (qcontra $ onpos i passign) (dcontra i passign) cmax,
      comp (qcovar $ onpos i passign) (pcovar i) a cmya (dcovar i passign)))

public export
IntPDiNTPara : (c : Type) -> (mor : IntDifunctorSig c) ->
  (cid : IntIdSig c mor) -> (comp : IntCompSig c mor) ->
  (idl : IntIdLSig c mor comp cid) ->
  (idr : IntIdRSig c mor comp cid) ->
  (assoc : IntAssocSig c mor comp) ->
  (p, q : IntEndoProAr c) -> (ar : IntPDiNTar c mor p q) ->
  IntParaNTCond c mor
    (InterpIEPPobj c mor p)
    (InterpIEPPobj c mor q)
    (IntEndoLmapFromDimap c mor cid
      (InterpIEPPobj c mor p) (InterpIEPPdimap c mor comp p))
    (IntEndoRmapFromDimap c mor cid
      (InterpIEPPobj c mor p) (InterpIEPPdimap c mor comp p))
    (IntEndoLmapFromDimap c mor cid
      (InterpIEPPobj c mor q) (InterpIEPPdimap c mor comp q))
    (IntEndoRmapFromDimap c mor cid
      (InterpIEPPobj c mor q) (InterpIEPPdimap c mor comp q))
  (InterpIEPPdint c mor comp p q ar)
IntPDiNTPara c mor cid comp idl idr assoc
  (ppos ** (pcovar, pcontra)) (qpos ** (qcovar, qcontra))
  (onpos ** (dcontra, dcovar)) c0 c1 mc0c1
  (i0 ** (mcp0, mpc0)) (i1 ** (mcp1, mpc1)) cond =
    case mkDPairInjectiveFstHet cond of
      Refl =>
        let
          eq2 = mkDPairInjectiveSndHet cond
          eq21 = trans (fstEq eq2) $ idl c0 (pcovar i1) mcp0
          eq22 = trans (sym $ idr (pcontra i1) c1 mpc1) $ sndEq eq2
          contracomp :
            (comp (pcontra i1) c1 (pcovar i1) mcp1 mpc1 =
             comp (pcontra i1) c0 (pcovar i1) mcp0 mpc0) =
              rewrite sym eq21 in rewrite eq22 in
              rewrite assoc (pcontra i1) c0 c1 (pcovar i1) mcp1 mc0c1 mpc0
              in Refl
        in
        rewrite contracomp in
        dpEq12
          Refl
          $ pairEqCong
            (rewrite
              idl _ _ (comp _ _ _ (dcontra _ (comp _ _ _ mcp0 mpc0)) mcp0) in
             rewrite
              assoc _ _ _ _ (dcontra _ (comp _ _ _ mcp0 mpc0)) mcp1 mc0c1 in
             rewrite eq21 in Refl)
            (rewrite
              idr _ _ (comp _ _ _ mpc1 (dcovar _ (comp _ _ _ mcp0 mpc0))) in
             rewrite sym $
              assoc _ _ _ _ mc0c1 mpc0 (dcovar _ (comp _ _ _ mcp0 mpc0)) in
             rewrite eq22 in Refl)

public export
intPPNTrestrict :
  {c : Type} -> {cmor : IntDifunctorSig c} -> {p, q : IntEndoProAr c} ->
  IntPPNTar c c cmor cmor p q -> IntPDiNTar c cmor p q
intPPNTrestrict {c} {cmor} {p} {q} ar =
  (\i, _ => intPPNTpos {d=c} {c} {dmor=cmor} {cmor} ar i **
   (\i, _ => intPPNTcontra {d=c} {c} {dmor=cmor} {cmor} ar i,
    \i, _ => intPPNTcovar {d=c} {c} {dmor=cmor} {cmor} ar i))

public export
intPDiNTid :
  (c : Type) -> (mor : IntDifunctorSig c) -> (cid : IntIdSig c mor) ->
  (p : IntEndoProAr c) -> IntPDiNTar c mor p p
intPDiNTid c mor cid (ppos ** (pcontra, pcovar)) =
  (\i, _ => i ** (\i, _ => cid (pcontra i), \i, _ => cid (pcovar i)))

public export
intPDiNTvcomp :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (p, q, r : IntEndoProAr c) ->
  IntPDiNTar c mor q r -> IntPDiNTar c mor p q -> IntPDiNTar c mor p r
intPDiNTvcomp c mor comp p q r beta alpha =
    let
      qasn :
        ((i : ipaPos p) -> (asn : mor (ipaCovar p i) (ipaContra p i)) ->
          mor
            (ipaCovar q (intPDiNTpos {mor} {p} {q} alpha i asn))
            (ipaContra q (intPDiNTpos {mor} {p} {q} alpha i asn))) =
        \i, pasn =>
          comp (ipaCovar q (intPDiNTpos {mor} {p} {q} alpha i pasn))
               (ipaContra p i)
               (ipaContra q (intPDiNTpos {mor} {p} {q} alpha i pasn))
            (intPDiNTcontra {mor} {p} {q} alpha i pasn)
            (comp (ipaCovar q (intPDiNTpos {mor} {p} {q} alpha i pasn))
              (ipaCovar p i) (ipaContra p i)
              pasn
              (intPDiNTcovar {mor} {p} {q} alpha i pasn))
    in
    (\i, pasn => intPDiNTpos {mor} {p=q} {q=r} beta
        (intPDiNTpos {mor} {p} {q} alpha i pasn) (qasn i pasn) **
      (\i, pasn =>
        comp
          (ipaContra p i)
          (ipaContra q (intPDiNTpos {mor} {p} {q} alpha i pasn))
          (ipaContra r (intPDiNTpos {mor} {p=q} {q=r} beta
            (intPDiNTpos {mor} {p} {q} alpha i pasn) (qasn i pasn)))
          (intPDiNTcontra {mor} {p=q} {q=r} beta
            (intPDiNTpos {mor} {p} {q} alpha i pasn) (qasn i pasn))
          (intPDiNTcontra {mor} {p} {q} alpha i pasn),
       \i, pasn =>
         comp
          (ipaCovar r (intPDiNTpos {mor} {p=q} {q=r} beta
            (intPDiNTpos {mor} {p} {q} alpha i pasn) (qasn i pasn)))
          (ipaCovar q (intPDiNTpos {mor} {p} {q} alpha i pasn))
          (ipaCovar p i)
          (intPDiNTcovar {mor} {p} {q} alpha i pasn)
          (intPDiNTcovar {mor} {p=q} {q=r} beta
            (intPDiNTpos {mor} {p} {q} alpha i pasn) (qasn i pasn))))

--------------------------------------------------------
--------------------------------------------------------
---- Paranatural polynomials as natural polynomials ----
--------------------------------------------------------
--------------------------------------------------------

public export
IntParaDomFunc : {c : Type} -> (mor : IntMorSig c) ->
  IntEndoProAr c -> IntEndoProAr c
IntParaDomFunc {c} mor (pos ** (contra, covar)) =
  ((i : pos ** mor (covar i) (contra i)) **
   (contra . DPair.fst, covar . DPair.fst))

public export
IntParaAsNT : {c : Type} -> {mor : IntMorSig c} -> {p, q : IntEndoProAr c} ->
  IntPDiNTar c mor p q -> IntEPPNTar c mor (IntParaDomFunc mor p) q
IntParaAsNT {c} {mor}
  {p=(ppos ** (pcontra, pcovar))} {q=(qpos ** (qcontra, qcovar))}
  (onpos ** (oncontra, oncovar)) =
    (DPair.uncurry onpos **
     (\(pi ** pasn) => oncontra pi pasn,
      \(pi ** pasn) => oncovar pi pasn))

public export
IntParaFromNT : {c : Type} -> {mor : IntMorSig c} -> {p, q : IntEndoProAr c} ->
  IntEPPNTar c mor (IntParaDomFunc mor p) q -> IntPDiNTar c mor p q
IntParaFromNT {c} {mor}
  {p=(ppos ** (pcontra, pcovar))} {q=(qpos ** (qcontra, qcovar))}
  (onpos ** (oncontra, oncovar)) =
    (DPair.curry onpos **
     (\pi, asn => oncontra (pi ** asn),
      \pi, asn => oncovar (pi ** asn)))

public export
IntParaAsNTlift :
  {c : Type} -> {mor : IntMorSig c} -> {comp : IntCompSig c mor} ->
  {p, q : IntEndoProAr c} ->
  IntPDiNTar c mor p q ->
  IntEPPNTar c mor (IntParaDomFunc mor p) (IntParaDomFunc mor q)
IntParaAsNTlift {c} {mor}
  {p=(ppos ** (pcontra, pcovar))} {q=(qpos ** (qcontra, qcovar))}
  (onpos ** (oncontra, oncovar)) =
    (\(pi ** pasn) =>
      (onpos pi pasn **
        comp (qcovar (onpos pi pasn)) (pcontra pi) (qcontra (onpos pi pasn))
          (oncontra pi pasn)
        $ comp (qcovar (onpos pi pasn)) (pcovar pi) (pcontra pi)
          pasn
        (oncovar pi pasn)) **
     (\(pi ** pasn) => oncontra pi pasn,
      \(pi ** pasn) => oncovar pi pasn))

-----------------------------
-----------------------------
---- Partial application ----
-----------------------------
-----------------------------

-- Apply a profunctor to its contravariant parameter, yielding a covariant
-- polynomial functor.
public export
ipaAppContra : {d, c : Type} -> (dmor : IntDifunctorSig d) ->
  (ar : IntProAr d c) -> d -> IntArena c
ipaAppContra {d} {c} dmor ar ed =
  ((i : ipaPos ar ** dmor ed (ipaContra ar i)) **
   \(i ** dmcont) => ipaCovar ar i)

-- Apply a profunctor to its covariant parameter, yielding a contravariant
-- polynomial (Dirichlet) functor.
public export
ipaAppCovar : {d, c : Type} -> (cmor : IntDifunctorSig c) ->
  (ar : IntProAr d c) -> c -> IntArena d
ipaAppCovar {d} {c} cmor ar ec =
  ((i : ipaPos ar ** cmor (ipaCovar ar i) ec) **
   \(i ** dmcont) => ipaContra ar i)

------------------------------------------------------
------------------------------------------------------
---- Profunctor categories of (diagonal) elements ----
------------------------------------------------------
------------------------------------------------------

public export
PProfCatElemObj : (d, c : Type) ->
  (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  IntProAr d c -> Type
PProfCatElemObj d c dmor cmor p =
  (x : d ** y : c ** InterpIPPobj d c dmor cmor p x y)

public export
data PProfCatElemMor :
    (d, c : Type) ->
    (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
    (dcomp : IntCompSig d dmor) -> (ccomp : IntCompSig c cmor) ->
    (p : IntProAr d c) ->
    PProfCatElemObj d c dmor cmor p -> PProfCatElemObj d c dmor cmor p -> Type
    where
  PPCEM :
    {d, c : Type} ->
    {dmor : IntDifunctorSig d} -> {cmor : IntDifunctorSig c} ->
    {dcomp : IntCompSig d dmor} -> {ccomp : IntCompSig c cmor} ->
    -- `pos`, `contra`, and `covar` together form an `IntProAr d c`.
    (pos : Type) -> (contra : pos -> d) -> (covar : pos -> c) ->
    -- `i`, `ddm`, and `cdm` together comprise a term of
    -- `InterpIPPobj d c dmor cmor (pos ** (contra, covar)) x y`;
    -- `x` and `ddm` together comprise an object of the slice category
    -- of `contra i`; `y` and `cdm` together comprise an object of
    -- the coslice category of `covar i`.  `x`, `y`, `i`, `ddm`, and `cdm`
    -- all together comprise an object of the category of elements of
    -- `(pos ** (contra, covar))`.
    (x : d) -> (y : c) ->
    (i : pos) -> (ddm : dmor x (contra i)) -> (cdm : cmor (covar i) y) ->
    -- `a` and `dmax` together form an object of the slice category of `x`.
    (a : d) -> (dmax : dmor a x) ->
    -- `b` and `cmyb` together form an object of the coslice category of `y`.
    (b : c) -> (cmyb : cmor y b) ->
    PProfCatElemMor d c dmor cmor dcomp ccomp (pos ** (contra, covar))
      (x ** y ** i ** (ddm, cdm))
      (a ** b ** i **
       (dcomp a x (contra i) ddm dmax, ccomp (covar i) y b cmyb cdm))

-- The category of diagonal elements, as it is called in Neumann's
-- "Paranatural Category Theory", is also referred to as the "D is
-- the one-object category" case of an algebra for a profunctor at
-- https://ncatlab.org/nlab/show/algebra+for+a+profunctor#definition .

public export
PProfCatDiagElemObj : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntEndoProAr c -> Type
PProfCatDiagElemObj c mor p = (x : c ** InterpIEPPobj c mor p x x)

public export
data PProfCatDiagElemMor :
    (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
    (p : IntEndoProAr c) ->
    PProfCatDiagElemObj c mor p -> PProfCatDiagElemObj c mor p -> Type where
  PPCDEM :
    {c : Type} -> {mor : IntDifunctorSig c} -> {comp : IntCompSig c mor} ->
    -- `pos`, `contra`, and `covar` together form an `IntEndoProAr c`.
    {pos : Type} -> {contra : pos -> c} -> {covar : pos -> c} ->
    -- `mxy` is the morphism of the underlying category (`c`) which
    -- underlies the morphism of the category of elements.
    {x, y : c} -> (mxy : mor x y) ->
    -- `i`, `mcontra`, and `mcovar` together comprise a term of
    -- `InterpIEPPobj c mor (pos ** (contra, covar)) y x`; `y` and
    -- `mcontra` together comprise an object of the slice category of
    -- `contra i`; `x` and `mcovar` together comprise an object of the coslice
    -- category of `covar i`.
    (i : pos) -> (mcontra : mor y (contra i)) -> (mcovar : mor (covar i) x) ->
    PProfCatDiagElemMor c mor comp (pos ** (contra, covar))
      (x ** i ** (comp x y (contra i) mcontra mxy, mcovar))
      (y ** i ** (mcontra, comp (covar i) x y mxy mcovar))

-- Here we show the equivalence of our definition of `PProfCatDiagElemMor`
-- with the standard definition in terms of lmap/rmap equality.

public export
0 PProfCatDiagElemMorToCommutingEl :
    {c : Type} -> {mor : IntDifunctorSig c} -> {comp : IntCompSig c mor} ->
    {p : IntEndoProAr c} ->
    (x, y : PProfCatDiagElemObj c mor p) ->
    PProfCatDiagElemMor c mor comp p x y ->
    (mxy : mor (fst x) (fst y) **
     InterpIEPPlmap c mor comp p (fst y) (fst y) (fst x) mxy (snd y) =
     InterpIEPPrmap c mor comp p (fst x) (fst x) (fst y) mxy (snd x))
PProfCatDiagElemMorToCommutingEl {c} {mor} {comp} {p=(pos ** (contra, covar))}
  (x ** _) (y ** _) (PPCDEM mxy i mcontra mcovar) =
    (mxy ** Refl)

public export
0 PProfCatDiagElemMorFromCommutingEl :
    {c : Type} -> {mor : IntDifunctorSig c} -> {comp : IntCompSig c mor} ->
    {p : IntEndoProAr c} ->
    (x, y : PProfCatDiagElemObj c mor p) ->
    (mxy : mor (fst x) (fst y) **
     InterpIEPPlmap c mor comp p (fst y) (fst y) (fst x) mxy (snd y) =
     InterpIEPPrmap c mor comp p (fst x) (fst x) (fst y) mxy (snd x)) ->
    PProfCatDiagElemMor c mor comp p x y
PProfCatDiagElemMorFromCommutingEl {c} {mor} {comp} {p=(pos ** (contra, covar))}
  (x ** xi ** (xcont, xcovar)) (y ** yi ** (ycont, ycovar)) (mxy ** lmeq) =
    case dpeq1 lmeq of
      Refl =>
        rewrite sym $ fstEq (dpeq2 lmeq) in
        rewrite sndEq (dpeq2 lmeq) in
        PPCDEM {mor} {comp} {contra} {covar} {x} {y} mxy xi ycont xcovar

-------------------------------------------------------
-------------------------------------------------------
---- Profunctors on Idris's base category (`Type`) ----
-------------------------------------------------------
-------------------------------------------------------

public export
0 TypeProfNT : IntMorSig ProfunctorSig
TypeProfNT = IntEndoProfNTSig Type

public export
0 TypeProfDiNT : IntMorSig ProfunctorSig
TypeProfDiNT = IntDiNTSig Type

public export
0 TypeDimapSig : (0 _ : Type -> Type -> Type) -> Type
TypeDimapSig p = IntEndoDimapSig Type HomProf p

public export
0 TypeLmapSig : (0 _ : Type -> Type -> Type) -> Type
TypeLmapSig p = IntEndoLmapSig Type HomProf p

public export
0 TypeRmapSig : (0 _ : Type -> Type -> Type) -> Type
TypeRmapSig p = IntEndoRmapSig Type HomProf p

public export
TypeDimapFromLR : (p : ProfunctorSig) ->
  TypeLmapSig p -> TypeRmapSig p -> TypeDimapSig p
TypeDimapFromLR p plm prm s t a b mas mtb = plm s b a mas . prm s t b mtb

public export
0 MkProfunctorFromLR : (p : ProfunctorSig) ->
  TypeLmapSig p -> TypeRmapSig p -> Profunctor p
MkProfunctorFromLR p plm prm = MkProfunctor $ TypeDimapFromLR p plm prm _ _ _ _

public export
TypeLmapFromDimap : (p : ProfunctorSig) -> TypeDimapSig p -> TypeLmapSig p
TypeLmapFromDimap = IntEndoLmapFromDimap Type TypeMor typeId

public export
TypeRmapFromDimap : (p : ProfunctorSig) -> TypeDimapSig p -> TypeRmapSig p
TypeRmapFromDimap = IntEndoRmapFromDimap Type TypeMor typeId

public export
0 TypeLRmapsCommute : (p : Type -> Type -> Type) ->
  TypeLmapSig p -> TypeRmapSig p -> Type
TypeLRmapsCommute = IntLRmapsCommute Type Type HomProf HomProf

public export
0 TypeLmapComp : (p : Type -> Type -> Type) -> TypeLmapSig p -> Type
TypeLmapComp = IntLmapComp Type TypeMor typeComp

public export
0 TypeRmapComp : (p : Type -> Type -> Type) -> TypeRmapSig p -> Type
TypeRmapComp = IntRmapComp Type TypeMor typeComp

public export
0 TypeNTNaturality : (p, q : ProfunctorSig) ->
  TypeDimapSig p -> TypeDimapSig q -> TypeProfNT p q -> Type
TypeNTNaturality = IntProfNTNaturality Type Type TypeMor TypeMor

public export
0 TypeNTParanaturalityLR : (p, q : ProfunctorSig) ->
  TypeLmapSig p -> TypeRmapSig p -> TypeLmapSig q -> TypeRmapSig q ->
  TypeProfDiNT p q -> Type
TypeNTParanaturalityLR = IntParaNTCond Type TypeMor

public export
0 TypeNTParanaturality : (p, q : ProfunctorSig) ->
  TypeDimapSig p -> TypeDimapSig q -> TypeProfDiNT p q -> Type
TypeNTParanaturality p q pdm qdm =
  IntParaNTCond Type TypeMor p q
    (TypeLmapFromDimap p pdm) (TypeRmapFromDimap p pdm)
    (TypeLmapFromDimap q qdm) (TypeRmapFromDimap q qdm)

public export
TypeProfConst : Type -> ProfunctorSig
TypeProfConst w x y = w

public export
TypeProfConstLmap : (w : Type) -> TypeLmapSig (TypeProfConst w)
TypeProfConstLmap w _ _ _ _ = id

public export
TypeProfConstRmap : (w : Type) -> TypeRmapSig (TypeProfConst w)
TypeProfConstRmap w _ _ _ _ = id

public export
TypeProfConstDimap : (w : Type) -> TypeDimapSig (TypeProfConst w)
TypeProfConstDimap w _ _ _ _ _ _ = id

public export
TypeProfConstProfunctor : (w : Type) -> Profunctor (TypeProfConst w)
TypeProfConstProfunctor w = MkProfunctor $ \_, _ => id

public export
TypeDiYonedaEmbedLmap :
  (s, t : Type) -> TypeLmapSig (DiYonedaEmbed s t)
TypeDiYonedaEmbedLmap = IntDiYonedaEmbedLmap Type TypeMor typeComp

public export
TypeDiYonedaEmbedRmap :
  (s, t : Type) -> TypeRmapSig (DiYonedaEmbed s t)
TypeDiYonedaEmbedRmap = IntDiYonedaEmbedRmap Type TypeMor typeComp

public export
0 ProfNaturality : (0 p, q : ProfunctorSig) ->
  (0 pdm : TypeDimapSig p) -> (0 qdm : TypeDimapSig q) ->
  ProfNT p q -> Type
ProfNaturality p q pdm qdm alpha =
  IntProfNTNaturality Type Type HomProf HomProf p q pdm qdm $ \_, _ => alpha

public export
0 ProfDinaturality : (0 p, q : ProfunctorSig) ->
  (0 plm : TypeLmapSig p) -> (0 prm : TypeRmapSig p) ->
  (0 qlm : TypeLmapSig q) -> (0 qrm : TypeRmapSig q) ->
  ProfDiNT p q -> Type
ProfDinaturality p q plm prm qlm qrm =
  IntDiNTCond Type HomProf p q plm prm qlm qrm

public export
0 ProfParanaturality : (0 p, q : ProfunctorSig) ->
  (0 plm : TypeLmapSig p) -> (0 prm : TypeRmapSig p) ->
  (0 qlm : TypeLmapSig q) -> (0 qrm : TypeRmapSig q) ->
  ProfDiNT p q -> Type
ProfParanaturality p q plm prm qlm qrm =
  IntParaNTCond Type HomProf p q plm prm qlm qrm

public export
0 TypeLmapIdSig : (p : ProfunctorSig) -> TypeLmapSig p -> Type
TypeLmapIdSig = IntEndoLmapIdSig Type TypeMor typeId

public export
0 TypeRmapIdSig : (p : ProfunctorSig) -> TypeRmapSig p -> Type
TypeRmapIdSig = IntEndoRmapIdSig Type TypeMor typeId

public export
0 TwArrPreshfEmbeddingNTparanaturalConst :
  {w : Type} -> {q : ProfunctorSig} ->
  (0 qlm : TypeLmapSig q) -> (0 qrm : TypeRmapSig q) ->
  (0 qlid : TypeLmapIdSig q qlm) -> (0 qrid : TypeRmapIdSig q qrm) ->
  (0 lcomp : TypeLmapComp q qlm) -> (0 rcomp : TypeRmapComp q qrm) ->
  (0 lrcomm : TypeLRmapsCommute q qlm qrm) ->
  (gamma : TwArrPreshfEmbeddingNT (TypeProfConst w) q) ->
  TwArrPreshfNaturality
    {p=(TwArrPreshfEmbedProf $ TypeProfConst w)}
    {q=(TwArrPreshfEmbedProf q)}
    (TwArrPreshfEmbedProfMap (TypeProfConst w) (TypeProfConstProfunctor w))
    (TwArrPreshfEmbedProfMap q (MkProfunctorFromLR q qlm qrm))
    gamma ->
  ProfParanaturality (TypeProfConst w) q
    (TypeProfConstLmap w)
    (TypeProfConstRmap w)
    qlm
    qrm
    (TwArrPreshfEmbeddingNTtoProfParaNT {p=(TypeProfConst w)} {q} gamma)
TwArrPreshfEmbeddingNTparanaturalConst {w} {q}
  qlm qrm qlid qrid lcomp rcomp lrcomm
  gamma gnat i0 i1 i2 ew0 ew1 cond =
    rewrite sym $ gnat i0 i1 i0 i0 id id i2 ew0 in
    rewrite sym $ gnat i0 i1 i1 i1 id i2 id ew1 in
    rewrite qlid i1 i1 (qrm i1 i0 i1 i2 (gamma i0 i1 i2 ew1)) in
    rewrite qrid i1 i0 (gamma i0 i1 i2 ew0) in
    rewrite cond in
    lrcomm i1 i0 i0 i1 i2 i2 (gamma i0 i1 i2 ew0)

-- Here we show that the set of natural transformations from the
-- twisted-arrow-copresheaf embedding of a constant profunctor to the
-- twisted-arrow-copresheaf embedding of an arbitrary profunctor is the
-- same as the set of paranatural transformations from that constant
-- profunctor to that arbitrary profunctor.  This in particular means
-- that the paranatural transformations out of constant profunctors
-- are the same as the extranatural transformations out of
-- constant profunctors, which also means that paranaturals and extranaturals
-- classify wedges in the same way (and thus lead to the same
-- notions of ends and coends).

public export
0 TwArrCoprEmbeddingNTparanaturalConst :
  {w : Type} -> {q : ProfunctorSig} ->
  (0 qlm : TypeLmapSig q) -> (0 qrm : TypeRmapSig q) ->
  (0 qlid : TypeLmapIdSig q qlm) -> (0 qrid : TypeRmapIdSig q qrm) ->
  (0 lcomp : TypeLmapComp q qlm) -> (0 rcomp : TypeRmapComp q qrm) ->
  (0 lrcomm : TypeLRmapsCommute q qlm qrm) ->
  (gamma : TwArrCoprEmbeddingNT (TypeProfConst w) q) ->
  TwArrCoprNaturality
    {p=(TwArrCoprEmbedProf $ TypeProfConst w)}
    {q=(TwArrCoprEmbedProf q)}
    (TwArrCoprEmbedDimap (TypeProfConst w) (TypeProfConstProfunctor w))
    (TwArrCoprEmbedDimap q (MkProfunctorFromLR q qlm qrm))
    gamma ->
  ProfParanaturality (TypeProfConst w) q
    (TypeProfConstLmap w)
    (TypeProfConstRmap w)
    qlm
    qrm
    (TwArrCoprEmbeddingNTtoProfParaNT {p=(TypeProfConst w)} {q} gamma)
TwArrCoprEmbeddingNTparanaturalConst {w} {q}
  qlm qrm qlid qrid lcomp rcomp lrcomm
  gamma gnat i0 i1 i2 ew0 ew1 cond =
    rewrite sym $ qlid i0 i1 (qrm i0 i0 i1 i2 (gamma i0 i0 id ew0)) in
    rewrite sym $ qrid i1 i1 (gamma i1 i1 id ew1) in
    rewrite gnat i0 i0 i0 i1 id id i2 ew0 in
    rewrite gnat i1 i1 i0 i1 id i2 id ew1 in
    rewrite cond in
    Refl

public export
0 TwArrParanaturalFromConstToCoprEmbeddingNT :
  {w : Type} -> {q : ProfunctorSig} ->
  (0 qlm : TypeLmapSig q) -> (0 qrm : TypeRmapSig q) ->
  (0 qlid : TypeLmapIdSig q qlm) -> (0 qrid : TypeRmapIdSig q qrm) ->
  (0 lcomp : TypeLmapComp q qlm) -> (0 rcomp : TypeRmapComp q qrm) ->
  (0 lrcomm : TypeLRmapsCommute q qlm qrm) ->
  (gamma : TypeProfDiNT (TypeProfConst w) q) ->
  ProfParanaturality (TypeProfConst w) q
    (TypeProfConstLmap w)
    (TypeProfConstRmap w)
    qlm
    qrm
    gamma ->
  TwArrCoprEmbeddingNT (TypeProfConst w) q
TwArrParanaturalFromConstToCoprEmbeddingNT {w} {q}
  qlm qrm qlid qrid lcomp rcomp lrcomm
  gamma cond x y mxy ew =
    let
      -- There are two ways we might obtain an answer, so we show that
      -- they are the same.
      0 qxyeq : (qlm y y x mxy (gamma y ew) = qrm x x y mxy (gamma x ew)) =
        cond x y mxy ew ew Refl
    in
    qrm x x y mxy (gamma x ew)

public export
0 TwArrParanaturalFromConstToCoprEmbeddingNTisNatural :
  {w : Type} -> {q : ProfunctorSig} ->
  (0 qlm : TypeLmapSig q) -> (0 qrm : TypeRmapSig q) ->
  (0 qlid : TypeLmapIdSig q qlm) -> (0 qrid : TypeRmapIdSig q qrm) ->
  (0 lcomp : TypeLmapComp q qlm) -> (0 rcomp : TypeRmapComp q qrm) ->
  (0 lrcomm : TypeLRmapsCommute q qlm qrm) ->
  (gamma : TypeProfDiNT (TypeProfConst w) q) ->
  (cond : ProfParanaturality (TypeProfConst w) q
    (TypeProfConstLmap w)
    (TypeProfConstRmap w)
    qlm
    qrm
    gamma) ->
  TwArrCoprNaturality
    {p=(TwArrCoprEmbedProf $ TypeProfConst w)}
    {q=(TwArrCoprEmbedProf q)}
    (TwArrCoprEmbedDimap (TypeProfConst w) (TypeProfConstProfunctor w))
    (TwArrCoprEmbedDimap q (MkProfunctorFromLR q qlm qrm))
    (TwArrParanaturalFromConstToCoprEmbeddingNT
      {w} {q} qlm qrm qlid qrid lcomp rcomp lrcomm gamma cond)
TwArrParanaturalFromConstToCoprEmbeddingNTisNatural {w} {q}
  qlm qrm qlid qrid lcomp rcomp lrcomm
  gamma cond s t a b mst mas mtb ew =
    rewrite rcomp s s b t mst mtb (gamma s ew) in
    rewrite sym $ cond a b (mtb . mst . mas) ew ew Refl in
    rewrite sym $ cond s b (mtb . mst) ew ew Refl in
    lcomp b b a s (mtb . mst) mas (gamma b ew)

-- Here we show that a natural transformation from the twisted-arrow-copresheaf
-- embedding of a direpresentable profunctor to the twisted-arrow-copresheaf
-- embedding of an arbitrary profunctor is paranatural when viewed as a
-- transformation of the underlying profunctors.  The converse is not
-- necessarily true -- we can not necessarily derive a twisted-arrow-copresheaf
-- embedding from an arbitrary paranatural transformation out of a
-- direpresentable profunctor.  In that sense the set of paranatural
-- transformations out of direpresentables is strictly larger than the set of
-- natural transformations between twisted-arrow-copresheaf embeddings out of
-- direpresentables.
public export
0 TwArrCoprEmbeddingNTparanaturalDirep :
  {p, p' : Type} -> {q : ProfunctorSig} ->
  (0 qlm : TypeLmapSig q) -> (0 qrm : TypeRmapSig q) ->
  (0 qlid : TypeLmapIdSig q qlm) -> (0 qrid : TypeRmapIdSig q qrm) ->
  (0 lcomp : TypeLmapComp q qlm) -> (0 rcomp : TypeRmapComp q qrm) ->
  (0 lrcomm : TypeLRmapsCommute q qlm qrm) ->
  (gamma : TwArrCoprEmbeddingNT (DiYonedaEmbed p p') q) ->
  TwArrCoprNaturality
    {p=(TwArrCoprEmbedProf $ DiYonedaEmbed p p')}
    {q=(TwArrCoprEmbedProf q)}
    (TwArrCoprEmbedDimap (DiYonedaEmbed p p') (DiYonedaEmbedProf p p'))
    (TwArrCoprEmbedDimap q (MkProfunctorFromLR q qlm qrm))
    gamma ->
  ProfParanaturality (DiYonedaEmbed p p') q
    (TypeDiYonedaEmbedLmap p p')
    (TypeDiYonedaEmbedRmap p p')
    qlm
    qrm
    (TwArrCoprEmbeddingNTtoProfParaNT {p=(DiYonedaEmbed p p')} {q} gamma)
TwArrCoprEmbeddingNTparanaturalDirep {p} {p'} {q}
  qlm qrm qlid qrid lcomp rcomp lrcomm
  gamma gnat i0 i1 i2 (mi0p', mpi0) (mi1p', mpi1) cond =
    rewrite sym $ qlid i0 i1 (qrm i0 i0 i1 i2 (gamma i0 i0 id (mi0p', mpi0))) in
    rewrite sym $ qrid i1 i1 (gamma i1 i1 id (mi1p', mpi1)) in
    rewrite gnat i0 i0 i0 i1 id id i2 (mi0p', mpi0) in
    rewrite gnat i1 i1 i0 i1 id i2 id (mi1p', mpi1) in
    rewrite fstEq cond in
    rewrite sndEq cond in
    Refl

public export
0 TypeNatDiYonedaLemmaLnt :
  {p, p' : Type} -> {q : ProfunctorSig} ->
  (0 qlm : TypeLmapSig q) -> (0 qrm : TypeRmapSig q) ->
  (0 lcomp : TypeLmapComp q qlm) -> (0 rcomp : TypeRmapComp q qrm) ->
  (0 lrcomm : TypeLRmapsCommute q qlm qrm) ->
  ((p -> p') -> q p' p) ->
  ProfDiNT (DiYonedaEmbed p p') q
TypeNatDiYonedaLemmaLnt {p} {p'} {q} qlm qrm lcomp rcomp lrcomm
  mpq a (map', mpa) =
    qlm p' a a map' $ qrm p' p a mpa $ mpq (map' . mpa)

public export
0 TypeNatDiYonedaLemmaLisPara :
  {p, p' : Type} -> {q : ProfunctorSig} ->
  (0 qlm : TypeLmapSig q) -> (0 qrm : TypeRmapSig q) ->
  (0 lcomp : TypeLmapComp q qlm) -> (0 rcomp : TypeRmapComp q qrm) ->
  (0 lrcomm : TypeLRmapsCommute q qlm qrm) ->
  (mpq : (p -> p') -> q p' p) ->
  ProfParanaturality (DiYonedaEmbed p p') q
    (TypeDiYonedaEmbedLmap p p')
    (TypeDiYonedaEmbedRmap p p')
    qlm
    qrm
    (TypeNatDiYonedaLemmaLnt {p} {p'} {q} qlm qrm lcomp rcomp lrcomm mpq)
TypeNatDiYonedaLemmaLisPara {p} {p'} {q} qlm qrm lcomp rcomp lrcomm
  mpq i0 i1 i2 (mi0p', mpi0) (mi1p', mpi1) cond =
    rewrite sym (fstEq cond) in
    rewrite sndEq cond in
    trans
      (lcomp p' i1 i0 i1 mi1p' i2
        (qrm p' p i1 (i2 . mpi0) (mpq (mi1p' . i2 . mpi0))))
    $ trans
      (rewrite sym $ rcomp p' p i1 i0 mpi0 i2 (mpq (mi1p' . i2 . mpi0)) in Refl)
      (lrcomm p' i0 i0 i1 (mi1p' . i2) i2
        (qrm p' p i0 mpi0 (mpq (mi1p' . i2 . mpi0))))

public export
0 TypeNatDiYonedaLemmaR :
  {p, p' : Type} -> {q : ProfunctorSig} ->
  (0 qlm : TypeLmapSig q) -> (0 qrm : TypeRmapSig q) ->
  (0 lcomp : TypeLmapComp q qlm) -> (0 rcomp : TypeRmapComp q qrm) ->
  (0 lrcomm : TypeLRmapsCommute q qlm qrm) ->
  (gamma : ProfDiNT (DiYonedaEmbed p p') q) ->
  ProfParanaturality (DiYonedaEmbed p p') q
    (TypeDiYonedaEmbedLmap p p')
    (TypeDiYonedaEmbedRmap p p')
    qlm
    qrm
    gamma ->
  ((p -> p') -> q p p')
TypeNatDiYonedaLemmaR {p} {p'} {q} qlm qrm lcomp rcomp lrcomm
  gamma cond mpp' =
    let
      -- There are two ways we might obtain an answer, so we show that
      -- they are the same.
      0 lreq :
        (qrm p p p' mpp' (gamma p (mpp', id {a=p})) =
         qlm p' p' p mpp' (gamma p' (id {a=p'}, mpp'))) =
          sym $ cond p p' mpp' (mpp', id) (id, mpp') Refl
    in
    qrm p p p' mpp' (gamma p (mpp', id {a=p}))

public export
0 TwArrPreshfEmbeddingNTparanaturalRep :
  {p, p' : Type} -> {q : ProfunctorSig} ->
  (0 qlm : TypeLmapSig q) -> (0 qrm : TypeRmapSig q) ->
  (0 lcomp : TypeLmapComp q qlm) -> (0 rcomp : TypeRmapComp q qrm) ->
  (0 lrcomm : TypeLRmapsCommute q qlm qrm) ->
  (gamma : TwArrPreshfEmbeddingNT (opProdHom p p') q) ->
  TwArrPreshfNaturality
    {p=(TwArrPreshfEmbedProf $ opProdHom p p')}
    {q=(TwArrPreshfEmbedProf q)}
    (TwArrPreshfEmbedProfMap (opProdHom p p')
      (MkProfunctor $ opProdHomDimap Prelude.id Prelude.id))
    (TwArrPreshfEmbedProfMap q
      (MkProfunctor $ TypeDimapFromLR q qlm qrm _ _ _ _))
    gamma ->
  ProfParanaturality (opProdHom p p') q
    (\s, t, a, mas => opProdHomDimap Prelude.id Prelude.id mas Prelude.id)
    (\s, t, b => opProdHomDimap Prelude.id Prelude.id Prelude.id)
    qlm
    qrm
    (TwArrPreshfEmbeddingNTtoProfParaNT {p=(opProdHom p p')} {q} gamma)
TwArrPreshfEmbeddingNTparanaturalRep {p} {p'} {q} qlm qrm lcomp rcomp lrcomm
  gamma gnat i0 i1 i2 (mi0p, mp'i0) (mi1p, mp'i1) cond =
    rewrite sym $ gnat p' p i0 i0 id mp'i0 mi0p (id {a=p}, id {a=p'}) in
    rewrite sym $ gnat p' p i1 i1 id mp'i1 mi1p (id {a=p}, id {a=p'}) in
    trans
      (lcomp p i1 i0 i1 mi1p i2
        (qrm p p' i1 mp'i1 (gamma p' p (mi1p . mp'i1) (id, id))))
    $ rewrite
        lrcomm p p' i0 i0 mi0p mp'i0 (gamma p' p (mi0p . mp'i0) (id, id)) in
      rewrite rcomp i0 p' i1 i0 mp'i0 i2
        (qlm p p' i0 mi0p (gamma p' p (mi0p . mp'i0) (id, id))) in
    trans
      (lrcomm p p' i0 i1 (mi1p . i2) mp'i1 (gamma p' p (mi1p . mp'i1) (id, id)))
    $ rewrite sym $ fstEq cond in
      rewrite sndEq cond in
      Refl

-------------------------------
-------------------------------
---- Profunctor dialgebras ----
-------------------------------
-------------------------------

public export
ProfDialg : ProfunctorSig -> ProfunctorSig -> ProfunctorSig
ProfDialg p q x y = p y x -> q x y

public export
ProfDialgLmap : (p, q : ProfunctorSig) -> TypeRmapSig p -> TypeLmapSig q ->
  TypeLmapSig (ProfDialg p q)
ProfDialgLmap p q prm qlm s t a mas dialg =
  qlm s t a mas . dialg . prm t a s mas

public export
ProfDialgRmap : (p, q : ProfunctorSig) -> TypeLmapSig p -> TypeRmapSig q ->
  TypeRmapSig (ProfDialg p q)
ProfDialgRmap p q plm qrm s t b mtb dialg =
  qrm s t b mtb . dialg . plm b s t mtb

public export
ProfDialgDimap : (p, q : ProfunctorSig) ->
  TypeLmapSig p -> TypeRmapSig p -> TypeLmapSig q -> TypeRmapSig q ->
  TypeDimapSig (ProfDialg p q)
ProfDialgDimap p q plm prm qlm qrm =
  TypeDimapFromLR (ProfDialg p q)
    (ProfDialgLmap p q prm qlm)
    (ProfDialgRmap p q plm qrm)

-- See for example "ends as equalizers" at
-- https://bartoszmilewski.com/2017/03/29/ends-and-coends/ .

public export
typeWedgeLeft : {p : ProfunctorSig} -> TypeLmapSig p ->
  EndBase p -> PolyProdP p
typeWedgeLeft {p} plm i a b f = plm b b a f (i b)

public export
typeWedgeRight : {p : ProfunctorSig} -> TypeRmapSig p ->
  EndBase p -> PolyProdP p
typeWedgeRight {p} prm i a b f = prm a a b f (i a)

public export
TypeProfUnit : ProfunctorSig
TypeProfUnit _ _ = Unit

public export
TypeProfUnitLmap : TypeLmapSig TypeProfUnit
TypeProfUnitLmap _ _ _ _ _ = ()

public export
TypeProfUnitRmap : TypeRmapSig TypeProfUnit
TypeProfUnitRmap _ _ _ _ _ = ()

public export
TypeEnd : (p : Type -> Type -> Type) -> TypeLmapSig p -> TypeRmapSig p -> Type
TypeEnd p plm prm =
  Equalizer {a=(EndBase p)} {b=(PolyProdP p)}
    (typeWedgeLeft {p} plm)
    (typeWedgeRight {p} prm)

public export
TypeEndLAdj : Type -> ProfunctorSig
TypeEndLAdj y a b = (HomProf a b, y)

public export
TypeEndLAdjLmap : (y : Type) -> TypeLmapSig (TypeEndLAdj y)
TypeEndLAdjLmap y s t a = mapFst . (|>)

public export
TypeEndLAdjRmap : (y : Type) -> TypeRmapSig (TypeEndLAdj y)
TypeEndLAdjRmap y s t b = mapFst . (.)

public export
TypeEndLAdjDimap : (y : Type) -> TypeDimapSig (TypeEndLAdj y)
TypeEndLAdjDimap y =
  TypeDimapFromLR (TypeEndLAdj y) (TypeEndLAdjLmap y) (TypeEndLAdjRmap y)

public export
TypeEndUnit : FunExt -> (y : Type) ->
  y -> TypeEnd (TypeEndLAdj y) (TypeEndLAdjLmap y) (TypeEndLAdjRmap y)
TypeEndUnit fext y ey =
  Element0
    (\b => (id {a=b}, ey))
    (funExt $ \a => funExt $ \b => funExt $ \f => Refl)

public export
TypeEndCounit :
  (p : ProfunctorSig) -> (plm : TypeLmapSig p) -> (prm : TypeRmapSig p) ->
  TypeProfNT (TypeEndLAdj (TypeEnd p plm prm)) p
TypeEndCounit p plm prm x y (mxy, Element0 e wcond) =
  let
    -- There are two ways we might obtain an answer, so we show that
    -- they are the same.
    0 pxyeq : (plm y y x mxy (e y) = prm x x y mxy (e x)) =
      fcongdep {x=mxy} $ fcongdep {x=y} $ fcongdep {x=x} wcond
  in
  prm x x y mxy (e x)

-- Here we show that the end (in `Type`) of a profunctor is the same as
-- its set of paranatural transformations from the constant-`Unit` profunctor.

public export
ProfParaNTtoEnd : FunExt -> (q : ProfunctorSig) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  (gamma : ProfDiNT TypeProfUnit q) ->
  (0 _ : TypeNTParanaturalityLR
    TypeProfUnit q TypeProfUnitLmap TypeProfUnitRmap qlm qrm gamma) ->
  TypeEnd q qlm qrm
ProfParaNTtoEnd fext q qlm qrm gamma cond =
  Element0
    (\b => gamma b ())
    (funExt $ \i0 => funExt $ \i1 => funExt $ \i2 => cond i0 i1 i2 () () Refl)

public export
ProfParaNTfromEnd : FunExt -> (q : ProfunctorSig) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  TypeEnd q qlm qrm ->
  ProfDiNT TypeProfUnit q
ProfParaNTfromEnd fext q qlm qrm gamma a () = fst0 gamma a

public export
0 ProfParaNTfromEndisPara : (fext : FunExt) -> (q : ProfunctorSig) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  (e : TypeEnd q qlm qrm) ->
  TypeNTParanaturalityLR
    TypeProfUnit q TypeProfUnitLmap TypeProfUnitRmap qlm qrm
    (ProfParaNTfromEnd fext q qlm qrm e)
ProfParaNTfromEndisPara fext q qlm qrm
  (Element0 gamma wcond) i0 i1 i2 () () Refl =
    fcongdep {x=i2} $ fcongdep {x=i1} $ fcongdep {x=i0} wcond

-- A convenience function for the dialgebra special case of an end.
public export
ProfDialgParaNTtoEnd : FunExt -> (p, q : ProfunctorSig) ->
  (plm : TypeLmapSig p) -> (prm : TypeRmapSig p) ->
  TypeLRmapsCommute p plm prm ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  (gamma : ProfDiNT TypeProfUnit (ProfDialg p q)) ->
  (0 _ : TypeNTParanaturalityLR
    TypeProfUnit
    (ProfDialg p q)
    TypeProfUnitLmap
    TypeProfUnitRmap
    (ProfDialgLmap p q prm qlm)
    (ProfDialgRmap p q plm qrm)
    gamma) ->
  TypeEnd
    (ProfDialg p q)
    (ProfDialgLmap p q prm qlm)
    (ProfDialgRmap p q plm qrm)
ProfDialgParaNTtoEnd fext p q plm prm lrcomm qlm qrm =
  ProfParaNTtoEnd
    fext
    (ProfDialg p q)
    (ProfDialgLmap p q prm qlm)
    (ProfDialgRmap p q plm qrm)

-- Here we show that the end of a profunctor in `Type` is the same as
-- the set of natural transformations from the twisted-arrow-copresheaf
-- embedding of the constant-`Unit` profunctor to the twisted-arrow-copresheaf
-- embedding of the given profunctor.

public export
ProfCoprEmbedToEnd : FunExt -> (q : ProfunctorSig) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  (0 qlid : TypeLmapIdSig q qlm) -> (0 qrid : TypeRmapIdSig q qrm) ->
  (0 lcomp : TypeLmapComp q qlm) -> (0 rcomp : TypeRmapComp q qrm) ->
  (0 lrcomm : TypeLRmapsCommute q qlm qrm) ->
  (gamma : TwArrCoprEmbeddingNT (TypeProfConst Unit) q) ->
  TwArrCoprNaturality
    {p=(TwArrCoprEmbedProf $ TypeProfConst Unit)}
    {q=(TwArrCoprEmbedProf q)}
    (TwArrCoprEmbedDimap (TypeProfConst Unit) (TypeProfConstProfunctor Unit))
    (TwArrCoprEmbedDimap q (MkProfunctorFromLR q qlm qrm))
    gamma ->
  TypeEnd q qlm qrm
ProfCoprEmbedToEnd fext q qlm qrm qlid qrid lcomp rcomp lrcomm gamma isnat =
  ProfParaNTtoEnd fext q qlm qrm
    (TwArrCoprEmbeddingNTtoProfParaNT {p=(TypeProfConst Unit)} {q} gamma)
    (\i0, i1, i2, (), (), Refl =>
        TwArrCoprEmbeddingNTparanaturalConst {w=Unit} {q}
          qlm qrm qlid qrid lcomp rcomp lrcomm gamma isnat i0 i1 i2 () () Refl)

public export
0 ProfEndToCoprEmbed : FunExt -> (q : ProfunctorSig) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  (0 qlid : TypeLmapIdSig q qlm) -> (0 qrid : TypeRmapIdSig q qrm) ->
  (0 lcomp : TypeLmapComp q qlm) -> (0 rcomp : TypeRmapComp q qrm) ->
  (0 lrcomm : TypeLRmapsCommute q qlm qrm) ->
  TypeEnd q qlm qrm ->
  TwArrCoprEmbeddingNT (TypeProfConst Unit) q
ProfEndToCoprEmbed fext q qlm qrm qlid qrid lcomp rcomp lrcomm e =
  TwArrParanaturalFromConstToCoprEmbeddingNT {w=Unit} {q}
    qlm qrm qlid qrid lcomp rcomp lrcomm
    (ProfParaNTfromEnd fext q qlm qrm e)
    (\i0, i1, i2, (), (), Refl =>
      ProfParaNTfromEndisPara fext q qlm qrm e i0 i1 i2 () () Refl)

public export
0 ProfEndToCoprEmbedIsNatural : (fext : FunExt) -> (q : ProfunctorSig) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  (0 qlid : TypeLmapIdSig q qlm) -> (0 qrid : TypeRmapIdSig q qrm) ->
  (0 lcomp : TypeLmapComp q qlm) -> (0 rcomp : TypeRmapComp q qrm) ->
  (0 lrcomm : TypeLRmapsCommute q qlm qrm) ->
  (e : TypeEnd q qlm qrm) ->
  TwArrCoprNaturality
    {p=(TwArrCoprEmbedProf $ TypeProfConst Unit)}
    {q=(TwArrCoprEmbedProf q)}
    (TwArrCoprEmbedDimap (TypeProfConst Unit) (TypeProfConstProfunctor Unit))
    (TwArrCoprEmbedDimap q (MkProfunctorFromLR q qlm qrm))
    (ProfEndToCoprEmbed fext q qlm qrm qlid qrid lcomp rcomp lrcomm e)
ProfEndToCoprEmbedIsNatural fext q qlm qrm qlid qrid lcomp rcomp lrcomm e =
  TwArrParanaturalFromConstToCoprEmbeddingNTisNatural {w=Unit} {q}
    qlm qrm qlid qrid lcomp rcomp lrcomm
    (ProfParaNTfromEnd fext q qlm qrm e)
    (\i0, i1, i2, (), (), Refl =>
      ProfParaNTfromEndisPara fext q qlm qrm e i0 i1 i2 () () Refl)

--------------------------------------------------------------
--------------------------------------------------------------
---- Natural transformations from hom-profunctor and ends ----
--------------------------------------------------------------
--------------------------------------------------------------

public export
HomProfDimap : TypeDimapSig HomProf
HomProfDimap s t a b mas mtb mst = mtb . mst . mas

public export
HomProfNTtoEnd : FunExt -> (p : ProfunctorSig) ->
  (plm : TypeLmapSig p) -> (prm : TypeRmapSig p) ->
  (plid : TypeLmapIdSig p plm) -> (prid : TypeRmapIdSig p prm) ->
  (alpha : TypeProfNT HomProf p) ->
  TypeNTNaturality HomProf p HomProfDimap (TypeDimapFromLR p plm prm) alpha ->
  TypeEnd p plm prm
HomProfNTtoEnd fext p plm prm plid prid alpha isnat =
  Element0
    (\x => alpha x x id)
    (funExt $ \a => funExt $ \b => funExt $ \mab =>
      trans
        (cong (plm b b a mab) (sym $ prid b b (alpha b b id)))
      $ trans
        (trans
          (isnat b b a b mab id id)
          (sym $ isnat a a a b id mab id))
      $ plid a b (prm a a b mab (alpha a a id)))

--------------------------------------------
--------------------------------------------
---- Relative structural ends as limits ----
--------------------------------------------
--------------------------------------------

public export
ProfDiNTfromTwArrDialgLimitBase : (p, q : ProfunctorSig) ->
  (plm : TypeLmapSig p) -> (prm : TypeRmapSig p) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  TwArrDialgLimitApexBase (TwArrPreshfOpEmbedProf p) (TwArrCoprEmbedProf q) ->
  ProfDiNT p q
ProfDiNTfromTwArrDialgLimitBase p q plm prm qlm qrm cone x =
  cone x x (id {a=x}) ()

----------------------------
---- Twisted-arrow ends ----
----------------------------

public export
TwArrDialgP : TwArrPreshfOpSig -> TwArrCoprSig -> ProfunctorSig
TwArrDialgP p q x y = (mxy : x -> y) -> TwArrDialg p q x y mxy

public export
TwArrDialgEndBase : TwArrPreshfOpSig -> TwArrCoprSig -> Type
TwArrDialgEndBase p q = (x, y : Type) -> TwArrDialgP p q x y

public export
TwArrDialgDiNTbase : TwArrPreshfOpSig -> TwArrCoprSig -> Type
TwArrDialgDiNTbase p q = (x : Type) -> TwArrDialg p q x x id

public export
TwArrDialgEndBaseToDiNTbase : (p : TwArrPreshfOpSig) -> (q : TwArrCoprSig) ->
  (pdm : TwArrPreshfOpDimapSig p) -> (qdm : TwArrCoprDimapSig q) ->
  TwArrDialgEndBase p q -> TwArrDialgDiNTbase p q
TwArrDialgEndBaseToDiNTbase p q pdm qdm i x = i x x id

public export
TwArrDialgDiNTbaseToEndBaseL : (p : TwArrPreshfOpSig) -> (q : TwArrCoprSig) ->
  (pdm : TwArrPreshfOpDimapSig p) -> (qdm : TwArrCoprDimapSig q) ->
  TwArrDialgDiNTbase p q -> TwArrDialgEndBase p q
TwArrDialgDiNTbaseToEndBaseL p q pdm qdm i x y mxy =
  TwArrDialgLmap p q pdm qdm y y x Prelude.id mxy (i y)

public export
TwArrDialgDiNTbaseToEndBaseR : (p : TwArrPreshfOpSig) -> (q : TwArrCoprSig) ->
  (pdm : TwArrPreshfOpDimapSig p) -> (qdm : TwArrCoprDimapSig q) ->
  TwArrDialgDiNTbase p q -> TwArrDialgEndBase p q
TwArrDialgDiNTbaseToEndBaseR p q pdm qdm i x y mxy =
  TwArrDialgRmap p q pdm qdm x x y Prelude.id mxy (i x)

public export
TwArrDialgDiNTcond : (p : TwArrPreshfOpSig) -> (q : TwArrCoprSig) ->
  (pdm : TwArrPreshfOpDimapSig p) -> (qdm : TwArrCoprDimapSig q) ->
  TwArrDialgDiNTbase p q -> Type
TwArrDialgDiNTcond p q pdm qdm i =
  (x, y : Type) -> (mxy : x -> y) ->
  ExtEq {a=(p y x mxy)} {b=(q x y mxy)}
    (TwArrDialgDiNTbaseToEndBaseL p q pdm qdm i x y mxy)
    (TwArrDialgDiNTbaseToEndBaseR p q pdm qdm i x y mxy)

public export
TwArrDialgEndCond : (p : TwArrPreshfOpSig) -> (q : TwArrCoprSig) ->
  (pdm : TwArrPreshfOpDimapSig p) -> (qdm : TwArrCoprDimapSig q) ->
  TwArrDialgEndBase p q -> Type
TwArrDialgEndCond p q pdm qdm i =
  TwArrDialgDiNTcond p q pdm qdm (TwArrDialgEndBaseToDiNTbase p q pdm qdm i)

public export
ProfDiNTtoTwArrL : (p, q : ProfunctorSig) ->
  (plm : TypeLmapSig p) -> (prm : TypeRmapSig p) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  (plid : TypeLmapIdSig p plm) -> (prid : TypeRmapIdSig p prm) ->
  (qlid : TypeLmapIdSig q qlm) -> (qrid : TypeRmapIdSig q qrm) ->
  (0 plrcomm : TypeLRmapsCommute p plm prm) ->
  (0 qlrcomm : TypeLRmapsCommute q qlm qrm) ->
  (gamma : TypeProfDiNT p q) ->
  TwArrDialgEndBase (TwArrPreshfOpEmbedProf p) (TwArrCoprEmbedProf q)
ProfDiNTtoTwArrL p q plm prm qlm qrm plid prid qlid qrid plrcomm qlrcomm
  gamma x y mxy =
    TwArrDialgLmap
      (TwArrPreshfOpEmbedProf p) (TwArrCoprEmbedProf q)
      (\_, _, _, _, _ => TypeDimapFromLR p plm prm _ _ _ _)
      (\_, _, _, _, _ => TypeDimapFromLR q qlm qrm _ _ _ _)
      y y x id mxy (gamma y)

public export
ProfDiNTtoTwArrR : (p, q : ProfunctorSig) ->
  (plm : TypeLmapSig p) -> (prm : TypeRmapSig p) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  (plid : TypeLmapIdSig p plm) -> (prid : TypeRmapIdSig p prm) ->
  (qlid : TypeLmapIdSig q qlm) -> (qrid : TypeRmapIdSig q qrm) ->
  (0 plrcomm : TypeLRmapsCommute p plm prm) ->
  (0 qlrcomm : TypeLRmapsCommute q qlm qrm) ->
  (gamma : TypeProfDiNT p q) ->
  TwArrDialgEndBase (TwArrPreshfOpEmbedProf p) (TwArrCoprEmbedProf q)
ProfDiNTtoTwArrR p q plm prm qlm qrm plid prid qlid qrid plrcomm qlrcomm
  gamma x y mxy =
    TwArrDialgRmap
      (TwArrPreshfOpEmbedProf p) (TwArrCoprEmbedProf q)
      (\_, _, _, _, _ => TypeDimapFromLR p plm prm _ _ _ _)
      (\_, _, _, _, _ => TypeDimapFromLR q qlm qrm _ _ _ _)
      x x y id mxy (gamma x)

public export
ProfDiNTtoTwArr : (p, q : ProfunctorSig) ->
  (plm : TypeLmapSig p) -> (prm : TypeRmapSig p) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  (plid : TypeLmapIdSig p plm) -> (prid : TypeRmapIdSig p prm) ->
  (qlid : TypeLmapIdSig q qlm) -> (qrid : TypeRmapIdSig q qrm) ->
  (0 plrcomm : TypeLRmapsCommute p plm prm) ->
  (0 qlrcomm : TypeLRmapsCommute q qlm qrm) ->
  (gamma : TypeProfDiNT p q) ->
  TypeNTParanaturality
    p q (TypeDimapFromLR p plm prm) (TypeDimapFromLR q qlm qrm) gamma ->
  TwArrDialgEndBase (TwArrPreshfOpEmbedProf p) (TwArrCoprEmbedProf q)
ProfDiNTtoTwArr p q plm prm qlm qrm plid prid qlid qrid plrcomm qlrcomm
    gamma cond x y mxy pyx
    with
      (ProfDiNTtoTwArrR p q plm prm qlm qrm plid prid qlid qrid plrcomm qlrcomm
        gamma x y mxy pyx) proof qeq
  ProfDiNTtoTwArr p q plm prm qlm qrm plid prid qlid qrid plrcomm qlrcomm
    gamma cond x y mxy pyx
    | qxy =
      let
        -- There are two ways we could make a `qxy`, so we show that
        -- they are equivalent.
        0 eq :
          ((ProfDiNTtoTwArrL p q plm prm qlm qrm plid prid qlid qrid
            plrcomm qlrcomm gamma x y mxy pyx) =
           qxy) =
          rewrite sym qeq in
          rewrite plid y y (prm y x y mxy pyx) in
          rewrite prid y x pyx in
          cond x y mxy (plm y x x mxy pyx) (prm y x y mxy pyx)
            (rewrite prid y y (prm y x y mxy pyx) in
             rewrite plid x y (prm x x y mxy (plm y x x mxy pyx)) in
             plrcomm y x x y mxy mxy pyx)
      in
      qxy

public export
0 ProfDiNTtoTwArrCond : (p, q : ProfunctorSig) ->
  (plm : TypeLmapSig p) -> (prm : TypeRmapSig p) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  (plid : TypeLmapIdSig p plm) -> (prid : TypeRmapIdSig p prm) ->
  (qlid : TypeLmapIdSig q qlm) -> (qrid : TypeRmapIdSig q qrm) ->
  (0 plrcomm : TypeLRmapsCommute p plm prm) ->
  (0 qlrcomm : TypeLRmapsCommute q qlm qrm) ->
  (gamma : TypeProfDiNT p q) ->
  (cond : TypeNTParanaturality
    p q (TypeDimapFromLR p plm prm) (TypeDimapFromLR q qlm qrm) gamma) ->
  TwArrDialgEndCond
    (TwArrPreshfOpEmbedProf p) (TwArrCoprEmbedProf q)
    (TwArrPreshfOpEmbedProfMap p (MkProfunctorFromLR p plm prm))
    (TwArrCoprEmbedDimap q (MkProfunctorFromLR q qlm qrm))
    (ProfDiNTtoTwArr
      p q plm prm qlm qrm plid prid qlid qrid plrcomm qlrcomm gamma cond)
ProfDiNTtoTwArrCond p q plm prm qlm qrm plid prid qlid qrid plrcomm qlrcomm
  gamma cond x y mxy pyx =
    rewrite plid y y (prm y x y mxy pyx) in
    rewrite prid y y (prm y x y mxy pyx) in
    rewrite plid y y (prm y x y mxy pyx) in
    rewrite qrid y y (gamma y (prm y x y mxy pyx)) in
    rewrite qlid y y (gamma y (prm y x y mxy pyx)) in
    rewrite prid y x pyx in
    rewrite prid x x (plm y x x mxy pyx) in
    rewrite plid x x (plm y x x mxy pyx) in
    rewrite qrid x x (gamma x (plm y x x mxy pyx)) in
    rewrite qlid x x (gamma x (plm y x x mxy pyx)) in
    cond x y mxy
      (plm y x x mxy pyx)
      (prm y x y mxy pyx)
      (rewrite prid y y (prm y x y mxy pyx) in
       rewrite plid x y
        (prm x x y mxy (plm y x x mxy pyx)) in
       plrcomm y x x y mxy mxy pyx)

--------------------------
---- Coends in `Type` ----
--------------------------

public export
TypeCoendRAdj : Type -> ProfunctorSig
TypeCoendRAdj y a b = HomProf b a -> y

public export
TypeCoendRAdjLmap : (y : Type) -> TypeLmapSig (TypeCoendRAdj y)
TypeCoendRAdjLmap y s t a mas myst = myst . ((.) mas)

public export
TypeCoendRAdjRmap : (y : Type) -> TypeRmapSig (TypeCoendRAdj y)
TypeCoendRAdjRmap y s t b mtb myst = myst . ((|>) mtb)

public export
TypeCoendRAdjDimap : (y : Type) -> TypeDimapSig (TypeCoendRAdj y)
TypeCoendRAdjDimap y =
  TypeDimapFromLR (TypeCoendRAdj y) (TypeCoendRAdjLmap y) (TypeCoendRAdjRmap y)

public export
TypeCoendMap : (x, y : Type) -> (x -> y) ->
  TypeProfNT (TypeCoendRAdj x) (TypeCoendRAdj y)
TypeCoendMap x y mxy a b mbax mba = mxy (mbax mba)

public export
TypeCoendUnitBase : (p : ProfunctorSig) -> TypeRmapSig p ->
  TypeProfNT p (TypeCoendRAdj $ CoendBase p)
TypeCoendUnitBase p prm x y pxy myx = (x ** prm x y x myx pxy)

public export
TypeCoendCounit : (y : Type) -> CoendBase (TypeCoendRAdj y) -> y
TypeCoendCounit y (b ** mbby) = mbby id

------------------------------------------
---- Profunctor iterative application ----
------------------------------------------

public export
ProfToEndoF : ProfunctorSig -> FinSliceEndofunctor 2
ProfToEndoF p sl FZ = p (sl $ FS FZ) (sl FZ)
ProfToEndoF p sl (FS FZ) = p (sl FZ) (sl $ FS FZ)

public export
ProfEndoFMapNeg : FinSliceEndofunctor 2 -> Type
ProfEndoFMapNeg f =
  ((st, ab : FinSliceObj 2) ->
   (ab FZ -> st FZ) -> (st (FS FZ) -> ab (FS FZ)) ->
   f ab FZ -> f st FZ)

public export
ProfEndoFMapPos : FinSliceEndofunctor 2 -> Type
ProfEndoFMapPos f =
  ((st, ab : FinSliceObj 2) ->
   (ab FZ -> st FZ) -> (st (FS FZ) -> ab (FS FZ)) ->
   f st (FS FZ) -> f ab (FS FZ))

public export
ProfEndoFMap : FinSliceEndofunctor 2 -> Type
ProfEndoFMap f = (ProfEndoFMapNeg f, ProfEndoFMapPos f)

public export
p2efMapNeg : {p : ProfunctorSig} ->
  TypeDimapSig p -> ProfEndoFMapNeg (ProfToEndoF p)
p2efMapNeg {p} pdm st ab = flip $ pdm (ab (FS FZ)) (ab FZ) (st (FS FZ)) (st FZ)

public export
p2efMapPos : {p : ProfunctorSig} ->
  TypeDimapSig p -> ProfEndoFMapPos (ProfToEndoF p)
p2efMapPos {p} pdm st ab = pdm (st FZ) (st (FS FZ)) (ab FZ) (ab (FS FZ))

public export
p2efMap : {p : ProfunctorSig} ->
  TypeDimapSig p -> ProfEndoFMap (ProfToEndoF p)
p2efMap {p} pdm = (p2efMapNeg {p} pdm, p2efMapPos {p} pdm)

public export
OpProfFromEndoF : FinSliceEndofunctor 2 -> ProfunctorSig
OpProfFromEndoF f x y = f (flip index [x, y]) FZ

public export
opfeOpDimap : {f : FinSliceEndofunctor 2} -> ProfEndoFMapNeg f ->
  TypeDimapSig (flip $ OpProfFromEndoF f)
opfeOpDimap {f} fmn s t a b = flip $ fmn (flip index [b, a]) (flip index [t, s])

public export
ProfFromEndoF : FinSliceEndofunctor 2 -> ProfunctorSig
ProfFromEndoF f x y = f (flip index [x, y]) (FS FZ)

public export
pfeDimap : {f : FinSliceEndofunctor 2} -> ProfEndoFMapPos f ->
  TypeDimapSig (ProfFromEndoF f)
pfeDimap {f} fmp s t a b = fmp (flip index [s, t]) (flip index [a, b])

public export
HomEndoF : FinSliceEndofunctor 2
HomEndoF = ProfToEndoF HomProf

public export
HomEndoFMap : ProfEndoFMap HomEndoF
HomEndoFMap = p2efMap {p=HomProf} HomProfDimap

-- The "translate" functor which generates the free monad is a coproduct --
-- but coproducts in `op(Type)` are products in `Type`.
public export
data ProfTranslateF :
    FinSliceEndofunctor 2 -> FinSliceObj 2 -> FinSliceEndofunctor 2 where
  InPTn : {f : FinSliceEndofunctor 2} -> {0 sv, sa : FinSliceObj 2} ->
    sv FZ -> f sa FZ -> ProfTranslateF f sv sa FZ
  InPTv : {f : FinSliceEndofunctor 2} -> {0 sv, sa : FinSliceObj 2} ->
    sv (FS FZ) -> ProfTranslateF f sv sa (FS FZ)
  InPTc : {f : FinSliceEndofunctor 2} -> {0 sv, sa : FinSliceObj 2} ->
    f sa (FS FZ) -> ProfTranslateF f sv sa (FS FZ)

public export
ProfTranslateFMapNeg : {f : FinSliceEndofunctor 2} -> {sv : FinSliceObj 2} ->
  ProfEndoFMapNeg f -> ProfEndoFMapNeg (ProfTranslateF f sv)
ProfTranslateFMapNeg {f} {sv} fmn st ab mas mtb (InPTn esv efa) =
  InPTn esv $ fmn st ab mas mtb efa
ProfTranslateFMapNeg {f} {sv} fmn st ab mas mtb (InPTv esv) impossible
ProfTranslateFMapNeg {f} {sv} fmn st ab mas mtb (InPTc efa) impossible

public export
ProfTranslateFMapPos : {f : FinSliceEndofunctor 2} -> {sv : FinSliceObj 2} ->
  ProfEndoFMapPos f -> ProfEndoFMapPos (ProfTranslateF f sv)
ProfTranslateFMapPos {f} {sv} fmp st ab mas mtb (InPTn {f} {sv} {sa} ev eft)
  impossible
ProfTranslateFMapPos {f} {sv} fmp st ab mas mtb (InPTv ev) =
  InPTv ev
ProfTranslateFMapPos {f} {sv} fmp st ab mas mtb (InPTc eft) =
  InPTc $ fmp st ab mas mtb eft

public export
ProfTranslateFMap : {f : FinSliceEndofunctor 2} -> {sv : FinSliceObj 2} ->
  ProfEndoFMap f -> ProfEndoFMap (ProfTranslateF f sv)
ProfTranslateFMap {f} {sv} fmp =
  (ProfTranslateFMapNeg {f} {sv} (fst fmp),
   ProfTranslateFMapPos {f} {sv} (snd fmp))

public export
data ProfFreeM2 : FinSliceEndofunctor 2 -> FinSliceEndofunctor 2 where
  InPrF : {f : FinSliceEndofunctor 2} -> {sa : FinSliceObj 2} ->
    SliceAlg {a=(Fin 2)} (ProfTranslateF f sa) (ProfFreeM2 f sa)

public export
ProfFreeMPair : ProfunctorSig -> FinSliceEndofunctor 2
ProfFreeMPair = ProfFreeM2 . ProfToEndoF

public export
ProfOpFreeM : ProfunctorSig -> ProfunctorSig
ProfOpFreeM = OpProfFromEndoF . ProfFreeM2 . ProfToEndoF

public export
ProfFreeM : ProfunctorSig -> ProfunctorSig
ProfFreeM = ProfFromEndoF . ProfFreeM2 . ProfToEndoF

public export
inPFC : {p : ProfunctorSig} -> {x, y : Type} ->
  p (ProfOpFreeM p x y) (ProfFreeM p x y) -> ProfFreeM p x y
inPFC {p} {x} {y} el = InPrF (FS FZ) (InPTc el)

public export
ProfMuPair : ProfunctorSig -> FinSliceObj 2
ProfMuPair p = ProfFreeMPair p (flip index [Unit, Void])

public export
ProfOpMu : ProfunctorSig -> Type
ProfOpMu = flip ProfMuPair FZ

public export
ProfMu : ProfunctorSig -> Type
ProfMu = flip ProfMuPair (FS FZ)

public export
ProfFixF : ProfunctorSig -> Type -> Type
ProfFixF p = p (ProfOpMu p)

public export
profFixFmap : {p : ProfunctorSig} -> TypeRmapSig p ->
  (a, b : Type) -> (a -> b) -> ProfFixF p a -> ProfFixF p b
profFixFmap {p} prm = prm (ProfOpMu p)

public export
InPRm : {p : ProfunctorSig} -> ProfFixF p (ProfMu p) -> ProfMu p
InPRm {p} el = InPrF (FS FZ) (InPTc el)

public export
OutPRm : {p : ProfunctorSig} -> ProfMu p -> ProfFixF p (ProfMu p)
OutPRm {p} (InPrF (FS FZ) (InPTn () el)) impossible
OutPRm {p} (InPrF (FS FZ) (InPTv ev)) = void ev
OutPRm {p} (InPrF (FS FZ) (InPTc el)) = el

public export
ProfDiCata : ProfunctorSig -> Type
ProfDiCata p = (a, b : Type) ->
  (p b a -> a) -> (b -> p a b) -> (ProfMu p -> a, b -> ProfOpMu p)

----------------------------------------------------
----------------------------------------------------
---- (Co)free twisted-arrow(-op) (co)presheaves ----
----------------------------------------------------
----------------------------------------------------

-- The analogue of `CoProYo` for presheaves on the twisted-arrow category
-- of `Type`.  This is the object-map component of the object-map component
-- of an endofunctor on twisted-arrow presheaves.
public export
CoTwArrPreshfYo : TwArrPreshfSig -> TwArrPreshfSig
CoTwArrPreshfYo p x y mxy =
  (ab : (Type, Type) **
   mp : (fst ab -> x, y -> snd ab) **
   p (fst ab) (snd ab) (snd mp . mxy . fst mp))

-- The morphism-map component of the object-map component of `CoTwArrPreshfYo`.
public export
CoTwArrPreshfYoContraDimap : (p : TwArrPreshfSig) ->
  TwArrPreshfContraDimapSig (CoTwArrPreshfYo p)
CoTwArrPreshfYoContraDimap p s t a b mab msa mbt ((c, d) ** (mcs, mtd) ** pcd) =
  ((c, d) ** (msa . mcs, mtd . mbt) ** pcd)

-- The morphism-map component of `CoTwArrPreshfYo`.
public export
CoTwArrPreshfYoFMap : (p, q : TwArrPreshfSig) ->
  TwArrPreshfNatTrans p q ->
  TwArrPreshfNatTrans (CoTwArrPreshfYo p) (CoTwArrPreshfYo q)
CoTwArrPreshfYoFMap p q gamma x y mxy ((a, b) ** (max, myb) ** pab) =
  ((a, b) ** (max, myb) ** gamma a b (myb . mxy . max) pab)

-- The analogue of `CoProYo` for presheaves on the twisted-arrow category
-- of `op(Type)`.
public export
CoTwArrPreshfOpYo : TwArrPreshfOpSig -> TwArrPreshfOpSig
CoTwArrPreshfOpYo p x y myx =
  (ab : (Type, Type) **
   mp : (x -> fst ab, snd ab -> y) **
   p (fst ab) (snd ab) (fst mp . myx . snd mp))

public export
CoTwArrPreshfOpYoDimap : (p : TwArrPreshfOpSig) ->
  TwArrPreshfOpDimapSig (CoTwArrPreshfOpYo p)
CoTwArrPreshfOpYoDimap p s t a b mba mas mtb ((c, d) ** (msc, mdt) ** pcd) =
  ((c, d) ** (msc . mas, mtb . mdt) ** pcd)

public export
CoTwArrPreshfOpYoFMap : (p, q : TwArrPreshfOpSig) ->
  TwArrPreshfOpNatTrans p q ->
  TwArrPreshfOpNatTrans (CoTwArrPreshfOpYo p) (CoTwArrPreshfOpYo q)
CoTwArrPreshfOpYoFMap p q gamma x y myx ((a, b) ** (mxa, mby) ** pba) =
  ((a, b) ** (mxa, mby) ** gamma a b (mxa . myx . mby) pba)

------------------------------------------------------------
------------------------------------------------------------
---- (Co)free twisted-arrow(-op) paranatural embeddings ----
------------------------------------------------------------
------------------------------------------------------------

public export
TwArrPreshfParaEmbedProfBase : (p : Type -> Type -> Type) ->
  TypeLmapSig p -> TypeRmapSig p -> TwArrPreshfSig
TwArrPreshfParaEmbedProfBase p plm prm x y mxy =
  (pp : (p x x, p y y) ** prm x x y mxy (fst pp) = plm y y x mxy (snd pp))

public export
TwArrPreshfParaEmbedProfBaseNT : (p, q : Type -> Type -> Type) ->
  (plm : TypeLmapSig p) -> (prm : TypeRmapSig p) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  Type
TwArrPreshfParaEmbedProfBaseNT p q plm prm qlm qrm =
  TwArrPreshfNatTrans
    (TwArrPreshfParaEmbedProfBase p plm prm)
    (TwArrPreshfParaEmbedProfBase q qlm qrm)

public export
TwArrPreshfParaEmbedProfBaseFMap : (p, q : Type -> Type -> Type) ->
  (plm : TypeLmapSig p) -> (prm : TypeRmapSig p) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  TypeLmapIdSig p plm -> TypeRmapIdSig p prm ->
  TypeLmapIdSig q qlm -> TypeRmapIdSig q qrm ->
  (alpha : TypeProfDiNT p q) ->
  TypeNTParanaturality
    p q (TypeDimapFromLR p plm prm) (TypeDimapFromLR q qlm qrm) alpha ->
  TwArrPreshfParaEmbedProfBaseNT p q plm prm qlm qrm
TwArrPreshfParaEmbedProfBaseFMap p q plm prm qlm qrm plid prid qlid qrid
  alpha cond x y mxy ((pxx, pyy) ** eq) =
    ((alpha x pxx, alpha y pyy) **
     rewrite sym $ qrid y y $ alpha y pyy in
     rewrite sym $ qlid x y $ qrm x x y mxy $ alpha x pxx in
     sym $ cond x y mxy pxx pyy
      (rewrite eq in
       rewrite prid y y pyy in
       rewrite plid x y (plm y y x mxy pyy) in Refl))

public export
TwArrPreshfParaEmbedProf : (p : Type -> Type -> Type) ->
  TypeLmapSig p -> TypeRmapSig p -> TwArrPreshfSig
TwArrPreshfParaEmbedProf p plm prm =
  CoTwArrPreshfYo (TwArrPreshfParaEmbedProfBase p plm prm)

public export
TwArrPreshfParaEmbedProfMap : (p : Type -> Type -> Type) ->
  (plm : TypeLmapSig p) -> (prm : TypeRmapSig p) ->
  TwArrPreshfContraDimapSig (TwArrPreshfParaEmbedProf p plm prm)
TwArrPreshfParaEmbedProfMap p plm prm =
  CoTwArrPreshfYoContraDimap (TwArrPreshfParaEmbedProfBase p plm prm)

public export
TwArrPreshfParaEmbedProfNT : (p, q : Type -> Type -> Type) ->
  (plm : TypeLmapSig p) -> (prm : TypeRmapSig p) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  Type
TwArrPreshfParaEmbedProfNT p q plm prm qlm qrm =
  TwArrPreshfNatTrans
    (TwArrPreshfParaEmbedProf p plm prm)
    (TwArrPreshfParaEmbedProf q qlm qrm)

public export
TwArrPreshfParaEmbedProfFMap : (p, q : Type -> Type -> Type) ->
  (plm : TypeLmapSig p) -> (prm : TypeRmapSig p) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  TypeLmapIdSig p plm -> TypeRmapIdSig p prm ->
  TypeLmapIdSig q qlm -> TypeRmapIdSig q qrm ->
  (alpha : TypeProfDiNT p q) ->
  TypeNTParanaturality
    p q (TypeDimapFromLR p plm prm) (TypeDimapFromLR q qlm qrm) alpha ->
  TwArrPreshfParaEmbedProfNT p q plm prm qlm qrm
TwArrPreshfParaEmbedProfFMap p q plm prm qlm qrm plid prid qlid qrid
  alpha isnat =
    CoTwArrPreshfYoFMap
      (TwArrPreshfParaEmbedProfBase p plm prm)
      (TwArrPreshfParaEmbedProfBase q qlm qrm)
      (TwArrPreshfParaEmbedProfBaseFMap
        p q plm prm qlm qrm plid prid qlid qrid alpha isnat)

public export
TwArrPreshfOpParaEmbedProfBase : (p : Type -> Type -> Type) ->
  TypeLmapSig p -> TypeRmapSig p -> TwArrPreshfOpSig
TwArrPreshfOpParaEmbedProfBase p plm prm x y myx =
  (pp : (p x x, p y y) ** plm x x y myx (fst pp) = prm y y x myx (snd pp))

public export
TwArrPreshfOpParaEmbedProfBaseNT : (p, q : Type -> Type -> Type) ->
  (plm : TypeLmapSig p) -> (prm : TypeRmapSig p) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  Type
TwArrPreshfOpParaEmbedProfBaseNT p q plm prm qlm qrm =
  TwArrPreshfOpNatTrans
    (TwArrPreshfOpParaEmbedProfBase p plm prm)
    (TwArrPreshfOpParaEmbedProfBase q qlm qrm)

public export
TwArrPreshfOpParaEmbedProfBaseFMap : (p, q : Type -> Type -> Type) ->
  (plm : TypeLmapSig p) -> (prm : TypeRmapSig p) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  TypeLmapIdSig p plm -> TypeRmapIdSig p prm ->
  TypeLmapIdSig q qlm -> TypeRmapIdSig q qrm ->
  (alpha : TypeProfDiNT p q) ->
  TypeNTParanaturality
    p q (TypeDimapFromLR p plm prm) (TypeDimapFromLR q qlm qrm) alpha ->
  TwArrPreshfOpParaEmbedProfBaseNT p q plm prm qlm qrm
TwArrPreshfOpParaEmbedProfBaseFMap p q plm prm qlm qrm plid prid qlid qrid
  alpha cond x y myx ((pxx, pyy) ** eq) =
    ((alpha x pxx, alpha y pyy) **
     rewrite sym $ qrid x x $ alpha x pxx in
     rewrite sym $ qlid y x $ qrm y y x myx (alpha y pyy) in
     cond y x myx pyy pxx
      (rewrite sym eq in
       rewrite prid x x pxx in
       rewrite plid y x (plm x x y myx pxx) in Refl))

public export
TwArrPreshfOpParaEmbedProf : (p : Type -> Type -> Type) ->
  TypeLmapSig p -> TypeRmapSig p -> TwArrPreshfOpSig
TwArrPreshfOpParaEmbedProf p plm prm =
  CoTwArrPreshfOpYo (TwArrPreshfOpParaEmbedProfBase p plm prm)

public export
TwArrPreshfOpParaEmbedProfMap : (p : Type -> Type -> Type) ->
  (plm : TypeLmapSig p) -> (prm : TypeRmapSig p) ->
  TwArrPreshfOpDimapSig (TwArrPreshfOpParaEmbedProf p plm prm)
TwArrPreshfOpParaEmbedProfMap p plm prm =
  CoTwArrPreshfOpYoDimap (TwArrPreshfOpParaEmbedProfBase p plm prm)

public export
TwArrPreshfOpParaEmbedProfNT : (p, q : Type -> Type -> Type) ->
  (plm : TypeLmapSig p) -> (prm : TypeRmapSig p) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  Type
TwArrPreshfOpParaEmbedProfNT p q plm prm qlm qrm =
  TwArrPreshfOpNatTrans
    (TwArrPreshfOpParaEmbedProf p plm prm)
    (TwArrPreshfOpParaEmbedProf q qlm qrm)

public export
TwArrPreshfOpParaEmbedProfFMap : (p, q : Type -> Type -> Type) ->
  (plm : TypeLmapSig p) -> (prm : TypeRmapSig p) ->
  (qlm : TypeLmapSig q) -> (qrm : TypeRmapSig q) ->
  TypeLmapIdSig p plm -> TypeRmapIdSig p prm ->
  TypeLmapIdSig q qlm -> TypeRmapIdSig q qrm ->
  (alpha : TypeProfDiNT p q) ->
  TypeNTParanaturality
    p q (TypeDimapFromLR p plm prm) (TypeDimapFromLR q qlm qrm) alpha ->
  TwArrPreshfOpParaEmbedProfNT p q plm prm qlm qrm
TwArrPreshfOpParaEmbedProfFMap p q plm prm qlm qrm plid prid qlid qrid
  alpha isnat =
    CoTwArrPreshfOpYoFMap
      (TwArrPreshfOpParaEmbedProfBase p plm prm)
      (TwArrPreshfOpParaEmbedProfBase q qlm qrm)
      (TwArrPreshfOpParaEmbedProfBaseFMap
        p q plm prm qlm qrm plid prid qlid qrid alpha isnat)

---------------------------
---------------------------
---- Dinatural numbers ----
---------------------------
---------------------------

public export
0 EndoHomParaSig : Type
EndoHomParaSig = TypeProfDiNT HomProf HomProf

public export
0 EndoHomParaCond : EndoHomParaSig -> Type
EndoHomParaCond = TypeNTParanaturality HomProf HomProf HomProfDimap HomProfDimap

public export
EndoHomParaFromNat : Nat -> EndoHomParaSig
EndoHomParaFromNat = iterNpnt

public export
EndoHomParaFromNatCond : FunExt ->
  (n : Nat) -> EndoHomParaCond (EndoHomParaFromNat n)
EndoHomParaFromNatCond fext Z i0 i1 i2 d0 d1 cond = Refl
EndoHomParaFromNatCond fext (S n) i0 i1 i2 d0 d1 cond =
  funExt $ \ex =>
    rewrite fcong {x=ex} (EndoHomParaFromNatCond fext n i0 i1 i2 d0 d1 cond) in
    fcong {x=(EndoHomParaFromNat n i0 d0 ex)} cond

public export
EndoHomParaToNat : EndoHomParaSig -> Nat
EndoHomParaToNat gamma = gamma Nat S Z

public export
EndoHomParaToNatEqIter : FunExt ->
  (gamma : EndoHomParaSig) -> EndoHomParaCond gamma ->
  (x : Type) -> (f : x -> x) ->
  ExtEq (gamma x f) (iterNpnt (gamma Nat S 0) x f)
EndoHomParaToNatEqIter fext gamma cond x f ex =
  fcong {x=Z} $ cond Nat x (flip (iterNf x f) ex) S f Refl

public export
EndoHomParaToNatComplete : FunExt ->
  (gamma : EndoHomParaSig) -> EndoHomParaCond gamma ->
  (x : Type) -> (f : x -> x) ->
  ExtEq (gamma x f) (EndoHomParaFromNat (EndoHomParaToNat gamma) x f)
EndoHomParaToNatComplete = EndoHomParaToNatEqIter

------------------------------------------------------------
---- Dinatural numbers from twisted-arrow-op presheaves ----
------------------------------------------------------------

public export
0 HomProfPreshfOp : TwArrPreshfOpSig
HomProfPreshfOp = TwArrPreshfOpEmbedProf HomProf

public export
0 HomProfPreshfOpDimap : TwArrPreshfOpDimapSig HomProfPreshfOp
HomProfPreshfOpDimap =
  TwArrPreshfOpEmbedProfMap HomProf $
    MkProfunctor $ \mca, mbd => HomProfDimap _ _ _ _ mca mbd

public export
0 EndoHomTwArrPreshfOpNatSig : Type
EndoHomTwArrPreshfOpNatSig =
  TwArrPreshfOpNatTrans HomProfPreshfOp HomProfPreshfOp

public export
0 EndoHomTwArrPreshfOpNatCond : EndoHomTwArrPreshfOpNatSig -> Type
EndoHomTwArrPreshfOpNatCond =
  TwArrPreshfOpNaturality HomProfPreshfOpDimap HomProfPreshfOpDimap

public export
iterNnt : Nat -> (x, y : Type) -> (x -> y) -> (y -> x) -> (x -> y)
iterNnt n x y g f = g . iterNpnt n x (f . g)

public export
iterNntF : (x, y : Type) -> (x -> y) -> (y -> x) -> Nat -> (x -> y)
iterNntF x y g f n = iterNnt n x y g f

public export
EndoHomTwArrPreshfOpNatFromNat : Nat -> EndoHomTwArrPreshfOpNatSig
EndoHomTwArrPreshfOpNatFromNat n x y = flip $ iterNnt n x y

public export
EndoHomTwArrPreshfOpFromNatCond : FunExt ->
  (n : Nat) -> EndoHomTwArrPreshfOpNatCond (EndoHomTwArrPreshfOpNatFromNat n)
EndoHomTwArrPreshfOpFromNatCond fext Z s t a b mba mas mtb mst =
  Refl
EndoHomTwArrPreshfOpFromNatCond fext (S n) s t a b mba mas mtb mst =
  funExt $ \ea =>
    rewrite
      fcong {x=ea}
        (EndoHomTwArrPreshfOpFromNatCond fext n s t a b mba mas mtb mst)
    in
    Refl

public export
EndoHomTwArrPreshfOpToNat : EndoHomTwArrPreshfOpNatSig -> Nat
EndoHomTwArrPreshfOpToNat gamma = gamma Nat Nat id S Z

---------------------------------------------------------------------------
---- Categories of diagonal elements and functors from natural numbers ----
---------------------------------------------------------------------------

-- See
-- https://mathoverflow.net/questions/442566/is-there-a-name-for-this-variant-of-the-category-of-elements-of-a-profunctor,
-- including the replies and comments.

-- The object-map component of the object-map component of the functor
-- from the category of diagonal elements of the hom-profunctor on `Type`
-- to the category of functors from the natural numbers (viewed as a preorder,
-- i.e. a thin category) to `Type`.
public export
HomDiagToNatFunc : (x : Type) -> (x -> x) -> Nat -> Type
HomDiagToNatFunc x mxx n = x

-- The morphism-map component of the object-map component of `HomDiagToNatFunc`.
public export
HomDiagToNatFuncMap : (x : Type) -> (mxx : x -> x) -> (m, n : Nat) ->
  LTE m n -> HomDiagToNatFunc x mxx m -> HomDiagToNatFunc x mxx n
HomDiagToNatFuncMap x mxx 0 n LTEZero =
  id {a=x}
HomDiagToNatFuncMap x mxx (S m) (S n) (LTESucc mmn) =
  mxx . HomDiagToNatFuncMap x mxx m n mmn

-- The morphism-family component of the morphism-map component of
-- `HomDiagToNatFunc`.
public export
HomDiagToNatFuncMor : (x, y : Type) -> (mxx : x -> x) -> (myy : y -> y) ->
  (mxy : x -> y) -> ExtEq {a=x} {b=y} (myy . mxy) (mxy . mxx) ->
  (n : Nat) -> HomDiagToNatFunc x mxx n -> HomDiagToNatFunc y myy n
HomDiagToNatFuncMor x y mxx myy mxy comm n = mxy

-- The naturality-condition component of the morphism-map component of
-- `HomDiagToNatFunc`.
public export
HomDiagToNatFuncMorIsNat : (x, y : Type) -> (mxx : x -> x) -> (myy : y -> y) ->
  (mxy : x -> y) -> (comm : ExtEq {a=x} {b=y} (myy . mxy) (mxy . mxx)) ->
  (m, n : Nat) -> (mmn : LTE m n) ->
  ExtEq
    {a=(HomDiagToNatFunc x mxx m)}
    {b=(HomDiagToNatFunc y myy n)}
    (HomDiagToNatFuncMor x y mxx myy mxy comm n
     . HomDiagToNatFuncMap x mxx m n mmn)
    (HomDiagToNatFuncMap y myy m n mmn
     . HomDiagToNatFuncMor x y mxx myy mxy comm m)
HomDiagToNatFuncMorIsNat x y mxx myy mxy comm 0 n LTEZero ex =
  Refl
HomDiagToNatFuncMorIsNat x y mxx myy mxy comm (S m) (S n) (LTESucc lte) ex =
  rewrite sym $ HomDiagToNatFuncMorIsNat x y mxx myy mxy comm m n lte ex in
  sym $ comm $ HomDiagToNatFuncMap x mxx m n lte ex

-- The object-map component of the functor from _the category of functors
-- from the natural numbers (viewed as a preorder, i.e. a thin category)
-- to `Type`_ to the category of diagonal elements of the hom-profunctor
-- on `Type`.  This is an inverse up to natural isomorphism (as we shall
-- show) to `HomDiagToNatFunc`.

-- The type component of the object map.
public export
NatFuncToHomDiagFst :
  (f : Nat -> Type) -> (fm : (m, n : Nat) -> LTE m n -> f m -> f n) -> Type
NatFuncToHomDiagFst f fm = DPair Nat f

-- The element component of the object map.
public export
NatFuncToHomDiagSnd :
  (f : Nat -> Type) -> (fm : (m, n : Nat) -> LTE m n -> f m -> f n) ->
  NatFuncToHomDiagFst f fm -> NatFuncToHomDiagFst f fm
NatFuncToHomDiagSnd f fm =
  dpBimap S $ \m => fm m (S m) $ lteSuccRight {m} {n=m} reflexive

-- The full object map.
public export
NatFuncToHomDiag :
  (f : Nat -> Type) -> (fm : (m, n : Nat) -> LTE m n -> f m -> f n) ->
  (x : Type ** x -> x)
NatFuncToHomDiag f fm = (NatFuncToHomDiagFst f fm ** NatFuncToHomDiagSnd f fm)

-- The morphism component of the morphism-map component of `NatFuncToHomDiag`.
public export
NatFuncToHomDiagMapFst :
  (f : Nat -> Type) -> (fm : (m, n : Nat) -> LTE m n -> f m -> f n) ->
  (g : Nat -> Type) -> (gm : (m, n : Nat) -> LTE m n -> g m -> g n) ->
  ((n : Nat) -> f n -> g n) ->
  NatFuncToHomDiagFst f fm -> NatFuncToHomDiagFst g gm
NatFuncToHomDiagMapFst f fm g gm = dpMapSnd

-- The equality component of the morphism-map component of `NatFuncToHomDiag`.
public export
NatFuncToHomDiagMapSnd :
  (f : Nat -> Type) -> (fm : (m, n : Nat) -> LTE m n -> f m -> f n) ->
  (g : Nat -> Type) -> (gm : (m, n : Nat) -> LTE m n -> g m -> g n) ->
  (alpha : (n : Nat) -> f n -> g n) ->
  (isnat :
    (m, n : Nat) -> (lte : LTE m n) ->
    ExtEq {a=(f m)} {b=(g n)}
      (gm m n lte . alpha m)
      (alpha n . fm m n lte)) ->
  ExtEq
    {a=(NatFuncToHomDiagFst f fm)}
    {b=(NatFuncToHomDiagFst g gm)}
    (NatFuncToHomDiagMapFst f fm g gm alpha
     . NatFuncToHomDiagSnd f fm) -- rmap is postcomposition
    (NatFuncToHomDiagSnd g gm
     . NatFuncToHomDiagMapFst f fm g gm alpha) -- lmap is precomposition
NatFuncToHomDiagMapSnd f fm g gm alpha isnat el =
  dpEq12
    Refl
    (sym $ isnat (fst el) (S $ fst el) (lteSuccRight reflexive) (snd el))

-- Inverse relationships between functors.

public export
HomDiagToNatFuncToHomDiagToIdFst :
  (x : Type) -> (mxx : x -> x) ->
  NatFuncToHomDiagFst
    (HomDiagToNatFunc x mxx)
    (HomDiagToNatFuncMap x mxx) ->
  x
HomDiagToNatFuncToHomDiagToIdFst x mxx = DPair.snd

public export
HomDiagToNatFuncToHomDiagFromIdFst :
  (x : Type) -> (mxx : x -> x) ->
  x ->
  NatFuncToHomDiagFst
    (HomDiagToNatFunc x mxx)
    (HomDiagToNatFuncMap x mxx)
HomDiagToNatFuncToHomDiagFromIdFst x mxx ex = (Z ** ex)

public export
HomDiagToNatFuncToFromHomDiagFstId :
  (x : Type) -> (mxx : x -> x) ->
  (el : NatFuncToHomDiagFst
    (HomDiagToNatFunc x mxx)
    (HomDiagToNatFuncMap x mxx)) ->
  snd
    (HomDiagToNatFuncToHomDiagFromIdFst x mxx
      (HomDiagToNatFuncToHomDiagToIdFst x mxx el)) =
  snd el
HomDiagToNatFuncToFromHomDiagFstId x mxx (n ** ex) = Refl

public export
HomDiagToNatFuncFromToHomDiagFstId :
  (x : Type) -> (mxx : x -> x) -> (ex : x) ->
  HomDiagToNatFuncToHomDiagToIdFst x mxx
    (HomDiagToNatFuncToHomDiagFromIdFst x mxx ex) =
  ex
HomDiagToNatFuncFromToHomDiagFstId x mxx ex = Refl

------------------------------------------------------
------------------------------------------------------
---- Mendler-style mixed-variance inductive types ----
------------------------------------------------------
------------------------------------------------------

-- See Uustalu's "Mendler-style inductive types, categorically".

public export
ProfCov : (Type -> Type) -> ProfunctorSig
ProfCov f x y = f y

public export
ProfCovDimap : (f : Type -> Type) ->
  ((a, b : Type) -> (a -> b) -> f a -> f b) ->
  TypeDimapSig (ProfCov f)
ProfCovDimap f fm s t a b mas mtb = fm t b mtb

public export
ProfCovId : ProfunctorSig
ProfCovId = ProfCov (id {a=Type})

public export
ProfOver : ProfunctorSig -> Type -> ProfunctorSig
ProfOver g c x y = g y x -> c

public export
ProfOverDimap : (g : ProfunctorSig) -> (gdm : TypeDimapSig g) ->
  (c : Type) -> TypeDimapSig (ProfOver g c)
ProfOverDimap g gdm c s t a b mas mtb mgc = mgc . gdm b a t s mtb mas

public export
ProfContraHom : Type -> ProfunctorSig
ProfContraHom = ProfOver (ProfCov (id {a=Type}))

public export
ProfContraHomFormula : (c : Type) -> (x, y : Type) ->
  ProfContraHom c x y = (x -> c)
ProfContraHomFormula c x y = Refl

public export
RCowedgeF : ProfunctorSig -> ProfunctorSig -> Type -> Type
RCowedgeF h g c = (y : Type) -> h y y -> ProfOver g c y y

public export
RCowedgeMap : (h, g : ProfunctorSig) -> (c, d : Type) ->
  (c -> d) -> RCowedgeF h g c -> RCowedgeF h g d
RCowedgeMap h g c d mcd cow x elh elg = mcd $ cow x elh elg

public export
RCoendUniv : ProfunctorSig -> ProfunctorSig -> Type
RCoendUniv h g = NaturalTransformation (RCowedgeF h g) (id {a=Type})

public export
RCoendExt : ProfunctorSig -> ProfunctorSig -> Type
RCoendExt h g = (x : Type ** (h x x, g x x))

public export
RCoendExtToUniv : (h, g : ProfunctorSig) -> RCoendExt h g -> RCoendUniv h g
RCoendExtToUniv h g (x ** (hxx, gxx)) y gamma = gamma x hxx gxx

public export
RCoendUnivToExt : (h, g : ProfunctorSig) -> RCoendUniv h g -> RCoendExt h g
RCoendUnivToExt h g ce = ce (RCoendExt h g) (\y, hyy, gyy => (y ** (hyy, gyy)))

public export
ProfMendlerExt : ProfunctorSig -> Type -> Type
ProfMendlerExt g = \c : Type => RCoendExt (ProfContraHom c) g

public export
ProfMendlerUniv : ProfunctorSig -> Type -> Type
ProfMendlerUniv g = \c : Type => RCoendUniv (ProfContraHom c) g

public export
ProfMendlerExtFormula : (g : ProfunctorSig) -> (c : Type) ->
  ProfMendlerExt g c = (x : Type ** (x -> c, g x x))
ProfMendlerExtFormula g c = Refl

public export
ProfMendlerUnivFormula : (g : ProfunctorSig) -> (c : Type) ->
  ProfMendlerUniv g c =
  ((x : Type) -> ((y : Type) -> (y -> c) -> g y y -> x) -> x)
ProfMendlerUnivFormula g c = Refl

public export
ProfMendlerExtMap : (g : ProfunctorSig) ->
  (a, b : Type) -> (a -> b) -> ProfMendlerExt g a -> ProfMendlerExt g b
ProfMendlerExtMap g a b mab =
  dpMapSnd $ \x : Type => mapFst ((.) mab)

public export
ProfMendlerUnivMap : (g : ProfunctorSig) ->
  (a, b : Type) -> (a -> b) -> ProfMendlerUniv g a -> ProfMendlerUniv g b
ProfMendlerUnivMap g a b mab gamma x delta =
  gamma x $ \y, mya => delta y (mab . mya)

public export
MendlerAlg : ProfunctorSig -> Type -> Type
MendlerAlg g c = RCowedgeF (ProfContraHom c) g c

public export
MendlerAlgFormula : (g : ProfunctorSig) -> (c : Type) ->
  MendlerAlg g c = ((x : Type) -> (x -> c) -> g x x -> c)
MendlerAlgFormula g c = Refl

public export
MendlerAlgToFAlgExt : (g : ProfunctorSig) -> (c : Type) ->
  MendlerAlg g c -> Algebra (ProfMendlerExt g) c
MendlerAlgToFAlgExt g c malg (x ** (mxc, gxx)) = malg x mxc gxx

public export
FAlgToMendlerAlgExt : (g : ProfunctorSig) -> (c : Type) ->
  Algebra (ProfMendlerExt g) c -> MendlerAlg g c
FAlgToMendlerAlgExt g c alg x mxc gxx = alg (x ** (mxc, gxx))

public export
MendlerAlgToFAlgUniv : (g : ProfunctorSig) -> (c : Type) ->
  MendlerAlg g c -> Algebra (ProfMendlerUniv g) c
MendlerAlgToFAlgUniv g c malg gamma = gamma c malg

public export
FAlgToMendlerAlgUniv : (g : ProfunctorSig) -> (c : Type) ->
  Algebra (ProfMendlerUniv g) c -> MendlerAlg g c
FAlgToMendlerAlgUniv g c alg y myc gyy = alg $ \x, malg => malg y myc gyy
