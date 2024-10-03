module LanguageDef.InternalProfunctor

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat

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
0 IntIdRSig : (0 c : Type) -> (0 mor : IntMorSig c) ->
  (comp : IntCompSig c mor) -> IntIdSig c mor -> Type
IntIdRSig c mor comp cid =
  (0 x, y : c) -> (m : mor x y) -> comp x y y (cid y) m = m

public export
0 IntAssocSig : (0 c : Type) ->
  (mor : IntMorSig c) -> (comp : IntCompSig c mor) ->
  Type
IntAssocSig c mor comp =
  (w, x, y, z : c) ->
  (h : mor y z) -> (g : mor x y) -> (f : mor w x) ->
  comp w x z (comp x y z h g) f = comp w y z h (comp w x y g f)

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
0 IntLmapFromDimap : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  (0 cid : IntIdSig c cmor) ->
  (p : IntProfunctorSig d c) ->
  IntDimapSig d c dmor cmor p ->
  IntLmapSig d c dmor cmor p
IntLmapFromDimap d c dmor cmor cid p pdm s t a = flip (pdm s t a t) (cid t)

public export
0 IntEndoLmapFromDimap : (0 c : Type) -> (0 cmor : IntDifunctorSig c) ->
  (0 cid : IntIdSig c cmor) -> (p : IntDifunctorSig c) ->
  IntEndoDimapSig c cmor p -> IntEndoLmapSig c cmor p
IntEndoLmapFromDimap c cmor cid = IntLmapFromDimap c c cmor cmor cid

public export
0 IntRmapFromDimap : (0 d, c : Type) ->
  (0 dmor : IntDifunctorSig d) -> (0 cmor : IntDifunctorSig c) ->
  (0 did : IntIdSig d dmor) ->
  (p : IntProfunctorSig d c) ->
  IntDimapSig d c dmor cmor p ->
  IntRmapSig d c dmor cmor p
IntRmapFromDimap d c dmor cmor did p pdm s t b = pdm s t s b (did s)

public export
0 IntEndoRmapFromDimap : (0 c : Type) -> (0 cmor : IntDifunctorSig c) ->
  (0 cid : IntIdSig c cmor) -> (p : IntDifunctorSig c) ->
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
0 IntProfNTSig : (d, c : Type) ->
  (p, q : IntProfunctorSig d c) -> Type
IntProfNTSig d c p q = (x : d) -> (y : c) -> p x y -> q x y

public export
0 IntEndoProfNTSig : (c : Type) ->
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
IntDiYonedaEmbedLmap c mor comp s t a b i cmia (cmat, cmsb) =
  (comp i a t cmat cmia, cmsb)

public export
IntDiYonedaEmbedRmap : (c : Type) -> (0 mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (s, t : c) -> IntEndoRmapSig c mor (IntDiYonedaEmbedObj c mor s t)
IntDiYonedaEmbedRmap c mor comp s t a b j cmbj (cmat, cmsb) =
  (cmat, comp s b j cmbj cmsb)

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

------------------------------------------------------------------------
------------------------------------------------------------------------
---- Internal polynomial difunctors and paranatural transformations ----
------------------------------------------------------------------------
------------------------------------------------------------------------

-------------------------------
---- Polynomial difunctors ----
-------------------------------

public export
PolyDiSig : (c : Type) -> Type
PolyDiSig c = (pos : Type ** (pos -> c, pos -> c))

public export
InterpPolyDi : {c : Type} -> (mor : IntDifunctorSig c) -> PolyDiSig c ->
  IntDifunctorSig c
InterpPolyDi {c} mor (pos ** (contra, covar)) a b =
  (i : pos ** IntDiYonedaEmbedObj c mor (contra i) (covar i) a b)

public export
InterpPolyDimap : {c : Type} -> {mor : IntDifunctorSig c} ->
  IntCompSig c mor ->
  (p : PolyDiSig c) -> IntEndoDimapSig c mor (InterpPolyDi {c} mor p)
InterpPolyDimap {c} {mor} comp (pos ** (contra, covar)) s t a b mas mtb =
  dpMapSnd $
    \pi => bimap (flip (comp a s (covar pi)) mas) (comp (contra pi) t b mtb)

------------------------------------------------
---- Polynomial paranatural transformations ----
------------------------------------------------

-- The set of paranatural transformations from a direpresentable,
-- (IntDiYonedaEmbedObj i j), to an arbitrary difunctor `p`.
public export
ParaNTfromDirep : (0 c : Type) -> (0 mor : IntDifunctorSig c) ->
  (s, t : c) -> (p : IntDifunctorSig c) -> Type
ParaNTfromDirep c mor s t p = p t s

-- The set of paranatural transformations from a direpresentable,
-- (IntDiYonedaEmbedObj i j), to an arbitrary polynomial difunctor `p`.
public export
PolyParaNTfromDirep : (c : Type) -> (mor : IntDifunctorSig c) ->
  (s, t : c) -> (p : PolyDiSig c) -> Type
PolyParaNTfromDirep c mor s t p = ParaNTfromDirep c mor s t (InterpPolyDi mor p)

-- The set of paranatural transformations between arbitrary
-- polynomial difunctors.
public export
PolyParaNT : (c : Type) -> (mor : IntDifunctorSig c) -> IntMorSig (PolyDiSig c)
PolyParaNT c mor (ppos ** (pcontra, pcovar)) q =
  (pi : ppos) -> PolyParaNTfromDirep c mor (pcontra pi) (pcovar pi) q

-- Having defined the set of paranatural transformations between polynomial
-- difunctors via the Yoneda lemma, we now write it in a more explicit form
-- and show they are the same.
public export
PolyParaNT' : (c : Type) -> (mor : IntDifunctorSig c) -> IntMorSig (PolyDiSig c)
PolyParaNT' c mor (ppos ** (pcontra, pcovar)) (qpos ** (qcontra, qcovar)) =
  (onpos : ppos -> qpos **
   ((pi : ppos) -> mor (pcovar pi) (qcovar (onpos pi)),
    (pi : ppos) -> mor (qcontra (onpos pi)) (pcontra pi)))

public export
PolyParaNTisoL : {c : Type} -> {mor : IntDifunctorSig c} ->
  {p, q : PolyDiSig c} ->
  PolyParaNT c mor p q -> PolyParaNT' c mor p q
PolyParaNTisoL {c} {mor}
  {p=(ppos ** (pcontra, pcovar))} {q=(qpos ** (qcontra, qcovar))} gamma =
    (\pi => fst (gamma pi) **
     (\pi => fst (snd $ gamma pi),
      \pi => snd (snd $ gamma pi)))

public export
PolyParaNTisoR : {c : Type} -> {mor : IntDifunctorSig c} ->
  {p, q : PolyDiSig c} ->
  PolyParaNT' c mor p q -> PolyParaNT c mor p q
PolyParaNTisoR {c} {mor}
  {p=(ppos ** (pcontra, pcovar))} {q=(qpos ** (qcontra, qcovar))}
  (onpos ** (oncovar, oncontra)) =
    \pi : ppos => (onpos pi ** (oncovar pi, oncontra pi))

public export
InterpPolyParaNT :
  {c : Type} -> {mor : IntDifunctorSig c} -> (comp : IntCompSig c mor) ->
  {p, q : PolyDiSig c} ->
  PolyParaNT' c mor p q ->
  IntDiNTSig c (InterpPolyDi {c} mor p) (InterpPolyDi {c} mor q)
InterpPolyParaNT {c} {mor} comp
  {p=(ppos ** (pcontra, pcovar))} {q=(qpos ** (qcontra, qcovar))}
  (onpos ** (oncovar, oncontra)) x (pi ** (mxcov, mcontx)) =
    (onpos pi **
     (comp x (pcovar pi) (qcovar (onpos pi)) (oncovar pi) mxcov,
      comp (qcontra (onpos pi)) (pcontra pi) x mcontx (oncontra pi)))

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
InterpIPPdimap : (d, c : Type) ->
  (dmor : IntDifunctorSig d) -> (cmor : IntDifunctorSig c) ->
  (dcomp : IntCompSig d dmor) -> (ccomp : IntCompSig c cmor) ->
  (ar : IntProAr d c) ->
  IntDimapSig d c dmor cmor (InterpIPPobj d c dmor cmor ar)
InterpIPPdimap d c dmor cmor dcomp ccomp p s t a b dmas cmtb el =
    (fst el **
     (dcomp a s (fst (snd p) (fst el)) (fst $ snd el) dmas,
      ccomp (snd (snd p) (fst el)) t b cmtb (snd $ snd el)))

public export
InterpIEPPdimap : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (ar : IntEndoProAr c) ->
  IntEndoDimapSig c mor (InterpIEPPobj c mor ar)
InterpIEPPdimap c mor comp = InterpIPPdimap c c mor mor comp comp

-----------------------------------------
---- Profunctor arena id/composition ----
-----------------------------------------

public export
IntProArId : (c : Type) -> IntEndoProAr c
IntProArId c = (c ** (id, id))

public export
IntProArComp : (e, d, c : Type) -> (dmor : IntDifunctorSig d) ->
  IntProAr e d -> IntProAr d c -> IntProAr e c
IntProArComp e d c dmor
  (qpos ** (qcont, qcovar)) (ppos ** (pcont, pcovar)) =
    ((pi : ppos ** qi : qpos ** dmor (qcovar qi) (pcont pi)) **
     (\(pi ** qi ** m) => qcont qi,
      \(pi ** qi ** m) => pcovar pi))

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
