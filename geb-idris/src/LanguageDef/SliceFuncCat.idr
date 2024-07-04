module LanguageDef.SliceFuncCat

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.InternalCat

%default total

%hide Prelude.(|>)
%hide Prelude.Ops.infixl.(|>)

---------------------
---------------------
---- Base change ----
---------------------
---------------------

-- This definition of `BaseChangeF` is the same as the one in `IdrisCategories`.
-- I'm duplicating it here just to make it explicit in the same module as the
-- adjunctions on either side of it.
%hide Library.IdrisCategories.BaseChangeF
public export
BaseChangeF : {c, d : Type} -> (d -> c) -> SliceFunctor c d
BaseChangeF {c} {d} f slc = slc . f

-- Because base change is in the middle of an adjoint triple between
-- dependent sum and dependent product, it can introduced and eliminated
-- from either side, by the adjuncts defined below with `Sigma` and `Pi`.

public export
bcMap : {0 c, d : Type} -> {f : d -> c} -> SliceFMap (BaseChangeF {c} {d} f)
bcMap {c} {d} {f} sa sb m ec = m (f ec)

-- This version of `BaseChangeF` uses a slice object rather than a morphism
-- between base objects, like the dependent-type-style definitions of
-- `SliceFibSigmaF` and `SlicePiF` below.
--
-- It could be viewed as pairing up each type of a type family with a type
-- family dependent upon _that_ type.
public export
SliceBCF : {c : Type} -> (sl : SliceObj c) -> SliceFunctor c (Sigma {a=c} sl)
SliceBCF {c} sl = BaseChangeF {c} {d=(Sigma {a=c} sl)} DPair.fst

public export
sbcMap : {0 c : Type} -> {sl : SliceObj c} -> SliceFMap (SliceBCF {c} sl)
sbcMap {c} {sl} sa sb = bcMap {c} {d=(Sigma {a=c} sl)} {f=DPair.fst} sa sb

--------------------------------
----- Base change as W-type ----
--------------------------------

public export
0 BCasWTF : {c, d : Type} -> (f : d -> c) -> WTypeFunc c d
BCasWTF {c} {d} f = MkWTF {dom=c} {cod=d} d d f id id

bcToWTF : {c, d : Type} -> (0 f : d -> c) ->
  SliceNatTrans (BaseChangeF {c} {d} f) (InterpWTF $ BCasWTF f)
bcToWTF {c} {d} f sc ed efd =
  (Element0 ed Refl **
   \(Element0 ed' eq) => replace {p=(BaseChangeF f sc)} (sym eq) efd)

bcFromWTF : {c, d : Type} -> (0 f : d -> c) ->
  SliceNatTrans (InterpWTF $ BCasWTF f) (BaseChangeF {c} {d} f)
bcFromWTF {c} {d} f sc ed (Element0 ed' eq ** scfd) =
  replace {p=(BaseChangeF f sc)} eq $ scfd $ Element0 ed' Refl

-----------------------
-----------------------
---- Dependent sum ----
-----------------------
-----------------------

--------------------
---- Definition ----
--------------------

-- This is the left adjoint of the dependent-sum/base-change adjunction.
-- (The right adjoint is base change.)
--
-- For convenient expression within a dependently-typed metalanguage, we
-- express this by default in terms of dependent types rather than fibrations,
-- which are the more category-theoretic style.
public export
SliceSigmaF : {c : Type} ->
  (sl : SliceObj c) -> SliceFunctor (Sigma {a=c} sl) c
SliceSigmaF {c} sl sls ec =
  -- An explicit way of spelling this out would be:
  --  (esc : sl ec ** sls $ (ec ** esc))
  Sigma {a=(sl ec)} (BaseChangeF (MkDPair ec) sls)

public export
ssMap : {c : Type} -> {0 sl : SliceObj c} -> SliceFMap (SliceSigmaF {c} sl)
ssMap {c} {sl} slsa slsb mab ec esla =
  (fst esla ** mab (ec ** fst esla) $ snd esla)

-- This is the category-theory-style version of `SliceSigmaF`, based on
-- fibrations.
--
-- One way of viewing it is as the slice functor from `c` to `d` which takes a
-- subobject of `c` to the subobject of `d` whose terms consist of single
-- applications of `f` to terms of the given subobject.
--
-- When it is an endofunctor (i.e. `d` is `c`), its initial algebra
-- (least fixed point) is simply the initial object of `SliceObj c`
-- (`const Void`); that initial algebra (as with any functor that has a
-- free monad) is isomorphic to the application of its free monad to the
-- initial object of `SliceObj c`, which is hence also `const Void`.
public export
data SliceFibSigmaF : {0 c, d : Type} ->
    (0 f : c -> d) -> SliceFunctor c d where
  -- An explicit way of spelling this out would be:
  -- \sc : SliceObj c, ed : d =>
  --  (ep : PreImage {a=c} {b=d} f ed ** sc $ fst0 ep)
  SFS : {0 c, d : Type} -> {0 f : c -> d} ->
    {0 sc : SliceObj c} ->
    (ec : c) -> sc ec -> SliceFibSigmaF {c} {d} f sc (f ec)

public export
sfsFst : {0 c, d : Type} -> {0 f : c -> d} -> {0 sc : SliceObj c} ->
  {ed : d} -> SliceFibSigmaF {c} {d} f sc ed -> c
sfsFst {c} {d} {f} {sc} {ed} ssc = case ssc of SFS ec _ => ec

public export
sfsSnd : {0 c, d : Type} -> {0 f : c -> d} -> {0 sc : SliceObj c} ->
  {ed : d} -> (ssc : SliceFibSigmaF {c} {d} f sc ed) -> sc (sfsFst ssc)
sfsSnd {c} {d} {f} {sc} {ed} ssc = case ssc of SFS _ esc => esc

public export
sfsEq : {0 c, d : Type} -> {0 f : c -> d} -> {0 sc : SliceObj c} ->
  {ed : d} -> (ssc : SliceFibSigmaF {c} {d} f sc ed) -> f (sfsFst ssc) = ed
sfsEq {c} {d} {f} {sc} {ed} ssc = case ssc of SFS ec esc => Refl

public export
sfsMap : {c, d : Type} -> {0 f : c -> d} ->
  SliceFMap (SliceFibSigmaF {c} {d} f)
sfsMap {c} {d} {f} sca scb mab eb ssa =
  case ssa of SFS ea esa => SFS {c} {d} {f} {sc=scb} ea $ mab ea esa

--------------------------
----- Sigma as W-type ----
--------------------------

public export
0 SFSasWTF : {c, d : Type} -> (f : c -> d) -> WTypeFunc c d
SFSasWTF {c} {d} f = MkWTF {dom=c} {cod=d} c c id id f

sfsToWTF : {c, d : Type} -> (0 f : c -> d) ->
  SliceNatTrans (SliceFibSigmaF {c} {d} f) (InterpWTF $ SFSasWTF f)
sfsToWTF {c} {d} f sc ed esc =
  (Element0 (sfsFst esc) (sfsEq esc) **
   \ec' => replace {p=sc} (sym $ snd0 ec') $ sfsSnd esc)

sfsFromWTF : {c, d : Type} -> (0 f : c -> d) ->
  SliceNatTrans (InterpWTF $ SFSasWTF f) (SliceFibSigmaF {c} {d} f)
sfsFromWTF {c} {d} f sc ed (Element0 ec eq ** scd) =
  replace {p=(SliceFibSigmaF f sc)} eq $ SFS ec $ scd $ Element0 ec Refl

0 SSasWTF : {c : Type} -> (sl : SliceObj c) -> WTypeFunc (Sigma sl) c
SSasWTF {c} sl = SFSasWTF {c=(Sigma sl)} {d=c} DPair.fst

ssToWTF : {c : Type} -> (sl : SliceObj c) ->
  SliceNatTrans (SliceSigmaF {c} sl) (InterpWTF $ SSasWTF sl)
ssToWTF {c} sl sc ec esc =
  (Element0 (ec ** fst esc) Refl **
   \ec' => replace {p=sc} (sym $ snd0 ec') $ snd esc)

ssFromWTF : {c : Type} -> (sl : SliceObj c) ->
  SliceNatTrans (InterpWTF $ SSasWTF sl) (SliceSigmaF {c} sl)
ssFromWTF {c} sc ssc ec (Element0 esc eq ** pisc) =
  rewrite sym eq in
  (snd esc ** replace {p=ssc} dpEqPat $ pisc $ Element0 esc Refl)

-------------------------
---- Adjunction data ----
-------------------------

-- The monad of the dependent-sum/base-change adjunction.
public export
SSMonad : {c : Type} -> (sl : SliceObj c) -> SliceEndofunctor (Sigma sl)
SSMonad {c} sl = SliceBCF {c} sl . SliceSigmaF {c} sl

public export
ssMonadMap : {c : Type} -> (sl : SliceObj c) -> SliceFMap (SSMonad {c} sl)
ssMonadMap {c} sl x y =
  sbcMap (SliceSigmaF sl x) (SliceSigmaF sl y) . ssMap {c} {sl} x y

-- The comonad of the dependent-sum/base-change adjunction.
public export
SSComonad : {c : Type} -> (sl : SliceObj c) -> SliceEndofunctor c
SSComonad {c} sl = SliceSigmaF {c} sl . SliceBCF sl

public export
ssComonadMap : {c : Type} -> (sl : SliceObj c) -> SliceFMap (SSComonad {c} sl)
ssComonadMap {c} sl x y =
  ssMap {c} {sl} (SliceBCF sl x) (SliceBCF sl y) . sbcMap {c} {sl} x y

-- Rather than making the constructor `SS` explicit, we export an
-- alias for it viewed as a natural transformation.
--
-- This is the unit (AKA "pure" or "return") of the dependent-sum/base-change
-- adjunction.
public export
sSin : {0 c : Type} -> {0 sl : SliceObj c} ->
  SliceNatTrans {x=(Sigma sl)} {y=(Sigma sl)}
    (SliceIdF $ Sigma sl)
    (SSMonad {c} sl)
sSin {c} {sl} sc ecsl esc = case ecsl of (ec ** esl) => (esl ** esc)

-- The counit (AKA "erase" or "extract") of the dependent-sum/base-change
-- adjunction.
public export
sSout : {0 c : Type} -> {0 sl : SliceObj c} ->
  SliceNatTrans {x=c} {y=c} (SSComonad {c} sl) (SliceIdF c)
sSout {c} {sl} sc ec esc = snd esc

-- This is the right adjunct of the dependent-sum/base-change adjunction.
--
-- It constitutes the destructor for `SliceSigmaF f sc`.  As an adjunction,
-- it is parametrically polymorphic:  rather than receiving a witness to a
-- given `ec : c` being in the image of `f` applied to a given slice over
-- `c`, it passes in a handler for _any_ such witness.
public export
ssElim : {c : Type} -> {sl : SliceObj c} ->
  {sa : SliceObj (Sigma sl)} -> {sb : SliceObj c} ->
  SliceMorphism {a=(Sigma sl)} sa (SliceBCF sl sb) ->
  SliceMorphism {a=c} (SliceSigmaF {c} sl sa) sb
ssElim {c} {sl} {sa} {sb} m =
  sliceComp (sSout sb) (ssMap sa (SliceBCF {c} sl sb) m)

-- This is the left adjunct of the dependent-sum/base-change adjunction.
public export
ssLAdj : {c : Type} -> {sl : SliceObj c} ->
  {sa : SliceObj (Sigma sl)} -> {sb : SliceObj c} ->
  SliceMorphism {a=c} (SliceSigmaF {c} sl sa) sb ->
  SliceMorphism {a=(Sigma sl)} sa (SliceBCF sl sb)
ssLAdj {c} {sl} {sa} {sb} m =
  sliceComp (sbcMap (SliceSigmaF {c} sl sa) sb m) (sSin sa)

-- This is the multiplication (AKA "join") of the dependent-sum/base-change
-- adjunction.
--
-- The multiplication comes from whiskering the counit between the adjuncts.
public export
sSjoin : {c : Type} -> {sl : SliceObj c} ->
  SliceNatTrans {x=(Sigma sl)} {y=(Sigma sl)}
    (SSMonad {c} sl . SSMonad {c} sl)
    (SSMonad {c} sl)
sSjoin {c} {sl} =
  SliceWhiskerRight
    {f=(SSComonad sl . SliceSigmaF sl)}
    {g=(SliceSigmaF sl)}
    {h=(SliceBCF sl)}
    (sbcMap {sl})
  $ SliceWhiskerLeft
    {g=(SSComonad sl)}
    {h=(SliceIdF c)}
    (sSout {sl})
    (SliceSigmaF sl)

-- This is the comultiplication (AKA "duplicate") of the
-- dependent-sum/base-change adjunction.
--
-- The comultiplication comes from whiskering the unit between the adjuncts.
public export
sSdup : {c : Type} -> {sl : SliceObj c} ->
  SliceNatTrans {x=c} {y=c}
    (SSComonad {c} sl)
    (SSComonad {c} sl . SSComonad {c} sl)
sSdup {c} {sl} =
  SliceWhiskerRight
    {f=(SliceBCF sl)}
    {g=(SliceBCF sl . SSComonad sl)}
    {h=(SliceSigmaF sl)}
    (ssMap {sl})
  $ SliceWhiskerLeft
    {g=(SliceIdF $ Sigma sl)}
    {h=(SSMonad sl)}
    sSin
    (SliceBCF sl)

public export
SSAlg : {c : Type} -> (0 f : c -> c) -> (sc : SliceObj c) -> Type
SSAlg {c} {f} = SliceAlg {a=c} (SliceFibSigmaF {c} {d=c} f)

public export
SSVoidAlg : {c : Type} -> (0 f : c -> c) -> SSAlg {c} f (const Void)
SSVoidAlg {c} f ec evc = void $ sfsSnd evc

public export
SSCoalg : {c : Type} -> (0 f : c -> c) -> (sc : SliceObj c) -> Type
SSCoalg {c} {f} = SliceCoalg {a=c} (SliceFibSigmaF {c} {d=c} f)

--------------------------------------------------------
---- Equalizers as W-types (using `SliceFibSigmaF`) ----
--------------------------------------------------------

public export
WDiagElem : {a : Type} -> SliceObj (a, a)
WDiagElem {a} =
  SliceFibSigmaF {c=a} {d=(a, a)} (ProductNTUnit {a}) (SliceObjTerminal a)

public export
0 WDiagElemEqualizes : {a : Type} -> {ea, ea' : a} ->
  WDiagElem {a} (ea, ea') -> ea = ea'
WDiagElemEqualizes {a} {ea} {ea'=ea} (SFS ea ()) = Refl

public export
0 WEqualizes : {a : Type} -> {0 b : Type} -> (0 f, g : a -> b) -> SliceObj a
WEqualizes {a} {b} f g ea = WDiagElem {a=b} (f ea, g ea)

public export
0 WEqualizesCorrect : {a : Type} -> {0 b : Type} -> {0 f, g : a -> b} ->
  (ea : a) -> WEqualizes {a} {b} f g ea -> f ea = g ea
WEqualizesCorrect {a} {b} {f} {g} ea =
  WDiagElemEqualizes {a=b} {ea=(f ea)} {ea'=(g ea)}

public export
WEqualizer : {a : Type} -> {0 b : Type} -> (0 f, g : a -> b) -> Type
WEqualizer {a} {b} f g = Subset0 a (WEqualizes {a} {b} f g)

public export
EqualizerFromW : {a : Type} -> {0 b : Type} -> {0 f, g : a -> b} ->
  WEqualizer {a} {b} f g -> Equalizer {a} {b} f g
EqualizerFromW {a} {b} {f} {g} = s0MapSnd $ WEqualizesCorrect {a} {b} {f} {g}

---------------------------
---------------------------
---- Dependent product ----
---------------------------
---------------------------

--------------------
---- Definition ----
--------------------

-- This is the right adjoint of the dependent-product/base-change adjunction.
-- (The left adjoint is base change.)
--
-- For convenient expression within a dependently-typed metalanguage, we
-- express this by default in terms of dependent types rather than fibrations,
-- which are the more category-theoretic style.
public export
SlicePiF : {c : Type} -> (sl : SliceObj c) -> SliceFunctor (Sigma {a=c} sl) c
SlicePiF {c} sl sls ec =
  -- An explicit way of spelling this out would be:
  --  (esc : sl ec) -> sls $ (ec ** esc)
  Pi {a=(sl ec)} (BaseChangeF (MkDPair ec) sls)

public export
spMap : {c : Type} -> {0 sl : SliceObj c} -> SliceFMap (SlicePiF {c} sl)
spMap {c} {sl} slsa slsb mab ec pia eslc = mab (ec ** eslc) $ pia eslc

-- The slice functor from `c` to `d` which takes a type family indexed by `c`
-- to a type of sections indexed by `d`, where the type at a given term
-- of `d` is the type of sections indexed by terms of `c` in the preimage of
-- that term of `d` under the given morphism.
--
-- In particular, if `d` is `Unit`, then this takes a type family indexed by `c`
-- to the type of its sections indexed by `c` -- that is, a slice object `sc`
-- over `c` is mapped by this functor to the type of `Type` (equivalent to a
-- slice over `Unit`) of choices of terms, for each `ec : c`, of `sc ec`.
--
-- This is the category-theory-style version of `SlicePiF`, based on
-- fibrations.
public export
SliceFibPiF : {c, d : Type} -> (0 f : c -> d) -> SliceFunctor c d
SliceFibPiF {c} {d} f =
  -- An explicit way of spelling this out would be:
  -- \sc : SliceObj c, ed : d =>
  --  (ep : PreImage {a=c} {b=d} f ed) -> sc $ fst0 ep
  SlicePiF {c=d} (\ed => PreImage {a=c} {b=d} f ed)
  . BaseChangeF
      {c}
      {d=(Sigma {a=d} $ \ed => PreImage {a=c} {b=d} f ed)}
      (\ed => fst0 $ snd ed)

public export
sfpMap : {c, d : Type} -> {0 f : c -> d} ->
  SliceFMap (SliceFibPiF {c} {d} f)
sfpMap {c} {d} {f} sca scb =
  spMap {c=d} {sl=(\ed => PreImage {a=c} {b=d} f ed)}
    (\edc => sca $ fst0 $ snd edc)
    (\edc => scb $ fst0 $ snd edc)
  . bcMap
    {c}
    {d=(Sigma {a=d} $ \ed => PreImage {a=c} {b=d} f ed)}
    {f=(\ed => fst0 $ snd ed)}
    sca
    scb

-----------------------
----- Pi as W-type ----
-----------------------

public export
0 SFPasWTF : {c, d : Type} -> (f : c -> d) -> WTypeFunc c d
SFPasWTF {c} {d} f = MkWTF {dom=c} {cod=d} d c id f id

sfpToWTF : {c, d : Type} -> (0 f : c -> d) ->
  SliceNatTrans (SliceFibPiF {c} {d} f) (InterpWTF $ SFPasWTF f)
sfpToWTF {c} {d} f sc ed pisc = (Element0 ed Refl ** pisc)

sfpFromWTF : {c, d : Type} -> (0 f : c -> d) ->
  SliceNatTrans (InterpWTF $ SFPasWTF f) (SliceFibPiF {c} {d} f)
sfpFromWTF {c} {d} f sc ed (Element0 ec eq ** scd) =
  replace {p=(SliceFibPiF f sc)} eq scd

0 SPasWTF : {c : Type} -> (sl : SliceObj c) -> WTypeFunc (Sigma sl) c
SPasWTF {c} sl = SFPasWTF {c=(Sigma sl)} {d=c} DPair.fst

spToWTF : {c : Type} -> (sl : SliceObj c) ->
  SliceNatTrans (SlicePiF {c} sl) (InterpWTF $ SPasWTF sl)
spToWTF {c} sc ssc ec pisc =
  (Element0 ec Refl **
   \(Element0 (ec' ** esc') eqc) =>
    rewrite eqc in pisc $ rewrite sym eqc in esc')

spFromWTF : {c : Type} -> (sl : SliceObj c) ->
  SliceNatTrans (InterpWTF $ SPasWTF sl) (SlicePiF {c} sl)
spFromWTF {c} sc ssc ec (Element0 ec' eqc ** pisc) esc =
  pisc $ Element0 (ec ** esc) $ sym eqc

-------------------------
---- Adjunction data ----
-------------------------

-- The monad of the dependent-product/base-change adjunction.
public export
SPMonad : {c : Type} -> (sl : SliceObj c) -> SliceEndofunctor c
SPMonad {c} sl = SlicePiF {c} sl . SliceBCF {c} sl

public export
spMonadMap : {c : Type} -> (sl : SliceObj c) -> SliceFMap (SPMonad {c} sl)
spMonadMap {c} sl x y =
  spMap {c} {sl} (SliceBCF sl x) (SliceBCF sl y) . sbcMap {c} {sl} x y

-- The comonad of the dependent-product/base-change adjunction.
public export
SPComonad : {c : Type} -> (sl : SliceObj c) -> SliceEndofunctor (Sigma sl)
SPComonad {c} sl = SliceBCF {c} sl . SlicePiF {c} sl

public export
spComonadMap : {c : Type} -> (sl : SliceObj c) -> SliceFMap (SPComonad {c} sl)
spComonadMap {c} sl x y =
  sbcMap (SlicePiF sl x) (SlicePiF sl y) . spMap {c} {sl} x y

-- This is the unit (AKA "pure" or "return") of the
-- dependent-product/base-change adjunction.
public export
spUnit : {0 c : Type} -> {0 sl : SliceObj c} ->
  SliceNatTrans {x=c} {y=c} (SliceIdF c) (SPMonad {c} sl)
spUnit {c} {sl} sc ec esc esl = esc

-- This is the counit (AKA "erase" or "extract") of the
-- dependent-product/base-change adjunction.
public export
spCounit : {0 c : Type} -> {0 sl : SliceObj c} ->
  SliceNatTrans {x=(Sigma sl)} {y=(Sigma sl)}
    (SPComonad {c} sl)
    (SliceIdF $ Sigma sl)
spCounit {c} {sl} sc ecsl pisc = case ecsl of (ec ** esl) => pisc esl

-- This is the left adjunct of the dependent-product/base-change adjunction.
--
-- It constitutes the constructor for `SlicePiF f sc`.  As an adjunction,
-- it is parametrically polymorphic:  rather than receiving a witness to a
-- given `ec : c` being in the image of `f` applied to a given slice over
-- `c`, it passes in a handler for _any_ such witness.
public export
spIntro : {c : Type} -> {sl : SliceObj c} ->
  {sa : SliceObj c} -> {sb : SliceObj (Sigma sl)} ->
  SliceMorphism {a=(Sigma sl)} (SliceBCF sl sa) sb ->
  SliceMorphism {a=c} sa (SlicePiF sl sb)
spIntro {c} {sl} {sa} {sb} m =
  sliceComp (spMap (SliceBCF sl sa) sb m) (spUnit sa)

-- This is the right adjunct of the dependent-product/base-change adjunction.
public export
spRAdj : {c : Type} -> {sl : SliceObj c} ->
  {sa : SliceObj c} -> {sb : SliceObj (Sigma sl)} ->
  SliceMorphism {a=c} sa (SlicePiF sl sb) ->
  SliceMorphism {a=(Sigma sl)} (SliceBCF sl sa) sb
spRAdj {c} {sl} {sa} {sb} m =
  sliceComp (spCounit sb) (sbcMap sa (SlicePiF sl sb) m)

-- This is the multiplication (AKA "join") of the dependent-product/base-change
-- adjunction.
--
-- The multiplication comes from whiskering the counit between the adjuncts.
public export
sPjoin : {c : Type} -> {sl : SliceObj c} ->
  SliceNatTrans {x=c} {y=c}
    (SPMonad {c} sl . SPMonad {c} sl)
    (SPMonad {c} sl)
sPjoin {c} {sl} =
  SliceWhiskerRight
    {f=(SPComonad sl . SliceBCF sl)}
    {g=(SliceBCF sl)}
    {h=(SlicePiF sl)}
    (spMap {sl})
  $ SliceWhiskerLeft
    {g=(SPComonad sl)}
    {h=(SliceIdF $ Sigma sl)}
    (spCounit {sl})
    (SliceBCF sl)

-- This is the comultiplication (AKA "duplicate") of the
-- dependent-product/base-change adjunction.
--
-- The comultiplication comes from whiskering the unit between the adjuncts.
public export
sPdup : {c : Type} -> {sl : SliceObj c} ->
  SliceNatTrans {x=(Sigma sl)} {y=(Sigma sl)}
    (SPComonad {c} sl)
    (SPComonad {c} sl . SPComonad {c} sl)
sPdup {c} {sl} =
  SliceWhiskerRight
    {f=(SlicePiF sl)}
    {g=(SlicePiF sl . SPComonad sl)}
    {h=(SliceBCF sl)}
    (sbcMap {sl})
  $ SliceWhiskerLeft
    {g=(SliceIdF c)}
    {h=(SPMonad sl)}
    spUnit
    (SlicePiF sl)

---------------------------------------------
---------------------------------------------
---- Sigma/base-change/pi adjoint triple ----
---------------------------------------------
---------------------------------------------

-- Dependent sum (sigma), base change, and dependent product (pi) form
-- an adjoint triple.  See for example:
--
--  - https://ncatlab.org/nlab/show/adjoint+triple
--
-- In the dependent-type formulation, the category on the right (the codomain
-- of the two outer adjoints, hence the domain of base change) is `SliceObj c`
-- for some `c : Type`, and the category on the left (the domain of the two
-- outer adjoints, hence the codomain of base change) is
-- `SliceObject (Sigma {a=c} sl)` for some `sl : SliceObj c`.
--
-- The adjoints of the left induced adjoint pair are therefore endofunctors on
-- `SliceObject (Sigma {a=c} sl)`, while the adjoints of the right induced
-- adjoint pair are endofunctors on `SliceObj c`.

-- This is the left adjoint of the left induced adjoint pair of the
-- dependent-sum/base-change/dependent-product adjoint triple.
public export
SliceSBCPlL : {c : Type} -> {sl : SliceObj c} ->
  SliceEndofunctor (Sigma {a=c} sl)
SliceSBCPlL {c} {sl} = SSMonad {c} sl

public export
sliceSBCPlLmap : {c : Type} -> {sl : SliceObj c} ->
  SliceFMap (SliceSBCPlL {c} {sl})
sliceSBCPlLmap {c} {sl} = ssMonadMap sl

-- This is the right adjoint of the left induced adjoint pair of the
-- dependent-sum/base-change/dependent-product adjoint triple.
public export
SliceSBCPlR : {c : Type} -> {sl : SliceObj c} ->
  SliceEndofunctor (Sigma {a=c} sl)
SliceSBCPlR {c} {sl} = SPComonad {c} sl

public export
sliceSBCPlRmap : {c : Type} -> {sl : SliceObj c} ->
  SliceFMap (SliceSBCPlR {c} {sl})
sliceSBCPlRmap {c} {sl} = spComonadMap sl

-- This is the left adjoint of the right induced adjoint pair of the
-- dependent-sum/base-change/dependent-product adjoint triple.
public export
SliceSBCPrL : {c : Type} -> {sl : SliceObj c} ->
  SliceEndofunctor c
SliceSBCPrL {c} {sl} = SSComonad {c} sl

public export
sliceSBCPrLmap : {c : Type} -> {sl : SliceObj c} ->
  SliceFMap (SliceSBCPrL {c} {sl})
sliceSBCPrLmap {c} {sl} = ssComonadMap sl

-- This is the right adjoint of the right induced adjoint pair of the
-- dependent-sum/base-change/dependent-product adjoint triple.
public export
SliceSBCPrR : {c : Type} -> {sl : SliceObj c} ->
  SliceEndofunctor c
SliceSBCPrR {c} {sl} = SPMonad {c} sl

public export
sliceSBCPrRmap : {c : Type} -> {sl : SliceObj c} ->
  SliceFMap (SliceSBCPrR {c} {sl})
sliceSBCPrRmap {c} {sl} = spMonadMap sl

-- This is the monad of the left induced adjoint pair of the
-- dependent-sum/base-change/dependent-product adjoint triple.
public export
SliceSBCPlMonad : {c : Type} -> {sl : SliceObj c} ->
  SliceEndofunctor (Sigma {a=c} sl)
SliceSBCPlMonad {c} {sl} = SliceSBCPlR {c} {sl} . SliceSBCPlL {c} {sl}

public export
sliceSBCPlMonadMap : {c : Type} -> {sl : SliceObj c} ->
  SliceFMap (SliceSBCPlMonad {c} {sl})
sliceSBCPlMonadMap {c} {sl} x y =
  spComonadMap sl (SSMonad sl x) (SSMonad sl y) . ssMonadMap sl x y

-- This is the comonad of the left induced adjoint pair of the
-- dependent-sum/base-change/dependent-product adjoint triple.
public export
SliceSBCPlComonad : {c : Type} -> {sl : SliceObj c} ->
  SliceEndofunctor (Sigma {a=c} sl)
SliceSBCPlComonad {c} {sl} = SliceSBCPlL {c} {sl} . SliceSBCPlR {c} {sl}

public export
sliceSBCPlComonadMap : {c : Type} -> {sl : SliceObj c} ->
  SliceFMap (SliceSBCPlComonad {c} {sl})
sliceSBCPlComonadMap {c} {sl} x y =
  ssMonadMap sl (SPComonad sl x) (SPComonad sl y) . spComonadMap sl x y

-- This is the monad of the right induced adjoint pair of the
-- dependent-sum/base-change/dependent-product adjoint triple.
public export
SliceSBCPrMonad : {c : Type} -> {sl : SliceObj c} ->
  SliceEndofunctor c
SliceSBCPrMonad {c} {sl} = SliceSBCPrR {c} {sl} . SliceSBCPrL {c} {sl}

public export
sliceSBCPrMonadMap : {c : Type} -> {sl : SliceObj c} ->
  SliceFMap (SliceSBCPrMonad {c} {sl})
sliceSBCPrMonadMap {c} {sl} x y =
  spMonadMap sl (SSComonad sl x) (SSComonad sl y) . ssComonadMap sl x y

-- This is the comonad of the right induced adjoint pair of the
-- dependent-sum/base-change/dependent-product adjoint triple.
public export
SliceSBCPrComonad : {c : Type} -> {sl : SliceObj c} ->
  SliceEndofunctor c
SliceSBCPrComonad {c} {sl} = SliceSBCPrL {c} {sl} . SliceSBCPrR {c} {sl}

public export
sliceSBCPrComonadMap : {c : Type} -> {sl : SliceObj c} ->
  SliceFMap (SliceSBCPrComonad {c} {sl})
sliceSBCPrComonadMap {c} {sl} x y =
  ssComonadMap sl (SPMonad sl x) (SPMonad sl y) . spMonadMap sl x y

-- This is the left adjunct of the left induced adjoint pair of the
-- dependent-sum/base-change/dependent-product adjoint triple.
--
-- The adjuncts of an adjoint pair which is induced by an adjoint triple can
-- be computed as a composition of adjuncts of the two separate
-- adjunctions which form the adjoint triple.
--
-- To spell out the hom-set isomorphism, of which the adjuncts are the
-- two directions, in this particular instance:
--
--     lL sa -> sb == (BC . Sigma) a -> sb
--  == BC (Sigma sa) -> sb
--  == Sigma sa -> Pi sb (BC/Pi left adjunct)
--  == sa -> BC (Pi sb) (Sigma/Pi left adjunct)
--  == sa -> (BC . Pi) sb == sa -> lR sb
public export
SliceSBCPlLAdj : {c : Type} -> {sl : SliceObj c} ->
  (sa, sb : SliceObj $ Sigma {a=c} sl) ->
  SliceMorphism {a=(Sigma {a=c} sl)} (SliceSBCPlL {c} {sl} sa) sb ->
  SliceMorphism {a=(Sigma {a=c} sl)} sa (SliceSBCPlR {c} {sl} sb)
SliceSBCPlLAdj {c} {sl} sa sb =
  ssLAdj {sl} {sa} {sb=(SlicePiF sl sb)}
  . spIntro {sl} {sa=(SliceSigmaF sl sa)} {sb}

-- This is the right adjunct of the left induced adjoint pair of the
-- dependent-sum/base-change/dependent-product adjoint triple.
public export
SliceSBCPlRAdj : {c : Type} -> {sl : SliceObj c} ->
  (sa, sb : SliceObj $ Sigma {a=c} sl) ->
  SliceMorphism {a=(Sigma {a=c} sl)} sa (SliceSBCPlR {c} {sl} sb) ->
  SliceMorphism {a=(Sigma {a=c} sl)} (SliceSBCPlL {c} {sl} sa) sb
SliceSBCPlRAdj {c} {sl} sa sb =
  spRAdj {sl} {sa=(SliceSigmaF sl sa)} {sb}
  . ssElim {sl} {sa} {sb=(SlicePiF sl sb)}

-- This is the left adjunct of the right induced adjoint pair of the
-- dependent-sum/base-change/dependent-product adjoint triple.
public export
SliceSBCPrLAdj : {c : Type} -> {sl : SliceObj c} ->
  (sa, sb : SliceObj c) ->
  SliceMorphism {a=c} (SliceSBCPrL {c} {sl} sa) sb ->
  SliceMorphism {a=c} sa (SliceSBCPrR {c} {sl} sb)
SliceSBCPrLAdj {c} {sl} sa sb =
  spIntro {sl} {sa} {sb=(SliceBCF sl sb)}
  . ssLAdj {sl} {sa=(SliceBCF sl sa)} {sb}

-- This is the right adjunct of the right induced adjoint pair of the
-- dependent-sum/base-change/dependent-product adjoint triple.
public export
SliceSBCPrRAdj : {c : Type} -> {sl : SliceObj c} ->
  (sa, sb : SliceObj c) ->
  SliceMorphism {a=c} sa (SliceSBCPrR {c} {sl} sb) ->
  SliceMorphism {a=c} (SliceSBCPrL {c} {sl} sa) sb
SliceSBCPrRAdj {c} {sl} sa sb =
  ssElim {sl} {sa=(SliceBCF sl sa)} {sb}
  . spRAdj {sl} {sa} {sb=(SliceBCF sl sb)}

-- This is the unit (AKA "pure" or "return") of the left induced adjoint pair
-- of the dependent-sum/base-change/dependent-product adjoint triple.
--
-- The unit can be computed by applying the left adjunct to the
-- identity morphism.
public export
SliceSBCPlUnit : {c : Type} -> {sl : SliceObj c} ->
  SliceNatTrans {x=(Sigma {a=c} sl)} {y=(Sigma {a=c} sl)}
    (SliceIdF $ Sigma {a=c} sl)
    (SliceSBCPlMonad {c} {sl})
SliceSBCPlUnit {c} {sl} sla =
  SliceSBCPlLAdj {c} {sl} sla (SliceSBCPlL {c} {sl} sla)
    (sliceId $ SliceSBCPlL {c} {sl} sla)

-- This is the counit (AKA "erase" or "extract") of the left induced adjoint
-- pair of the dependent-sum/base-change/dependent-product adjoint triple.
--
-- The counit can be computed by applying the right adjunct to the
-- identity morphism.
public export
SliceSBCPlCounit : {c : Type} -> {sl : SliceObj c} ->
  SliceNatTrans {x=(Sigma {a=c} sl)} {y=(Sigma {a=c} sl)}
    (SliceSBCPlComonad {c} {sl})
    (SliceIdF $ Sigma {a=c} sl)
SliceSBCPlCounit {c} {sl} sla =
  SliceSBCPlRAdj {c} {sl} (SliceSBCPlR {c} {sl} sla) sla
    (sliceId $ SliceSBCPlR {c} {sl} sla)

-- This is the unit (AKA "pure" or "return") of the right induced adjoint pair
-- of the dependent-sum/base-change/dependent-product adjoint triple.
public export
SliceSBCPrUnit : {c : Type} -> {sl : SliceObj c} ->
  SliceNatTrans {x=c} {y=c}
    (SliceIdF c)
    (SliceSBCPrMonad {c} {sl})
SliceSBCPrUnit {c} {sl} sla =
  SliceSBCPrLAdj {c} {sl} sla (SliceSBCPrL {c} {sl} sla)
    (sliceId $ SliceSBCPrL {c} {sl} sla)

-- This is the counit (AKA "erase" or "extract") of the right induced adjoint
-- pair of the dependent-sum/base-change/dependent-product adjoint triple.
public export
SliceSBCPrCounit : {c : Type} -> {sl : SliceObj c} ->
  SliceNatTrans {x=c} {y=c}
    (SliceSBCPrComonad {c} {sl})
    (SliceIdF c)
SliceSBCPrCounit {c} {sl} sla =
  SliceSBCPrRAdj {c} {sl} (SliceSBCPrR {c} {sl} sla) sla
    (sliceId $ SliceSBCPrR {c} {sl} sla)

-- This is the multiplication (AKA "join") of the left induced adjoint pair
-- of the dependent-sum/base-change/dependent-product adjoint triple.
public export
SliceSBCPlJoin : {c : Type} -> {sl : SliceObj c} ->
  SliceNatTrans {x=(Sigma {a=c} sl)} {y=(Sigma {a=c} sl)}
    (SliceSBCPlMonad {c} {sl} . SliceSBCPlMonad {c} {sl})
    (SliceSBCPlMonad {c} {sl})
SliceSBCPlJoin {c} {sl} =
  SliceWhiskerRight
    {f=(SliceSBCPlComonad {sl} . SliceSBCPlL {sl})}
    {g=(SliceSBCPlL {sl})}
    {h=(SliceSBCPlR {sl})}
    (sliceSBCPlRmap {c} {sl})
  $ SliceWhiskerLeft
    {g=(SliceSBCPlComonad {sl})}
    {h=(SliceIdF $ Sigma sl)}
    (SliceSBCPlCounit {c} {sl})
    (SliceSBCPlL {sl})

-- This is the comultiplication (AKA "duplicate") of the left induced adjoint
-- pair of the dependent-sum/base-change/dependent-product adjoint triple.
public export
SliceSBCPlDup : {c : Type} -> {sl : SliceObj c} ->
  SliceNatTrans {x=(Sigma {a=c} sl)} {y=(Sigma {a=c} sl)}
    (SliceSBCPlComonad {c} {sl})
    (SliceSBCPlComonad {c} {sl} . SliceSBCPlComonad {c} {sl})
SliceSBCPlDup {c} {sl} =
  SliceWhiskerRight
    {f=(SliceSBCPlR {sl})}
    {g=(SliceSBCPlR {sl} . SliceSBCPlComonad {sl})}
    {h=(SliceSBCPlL {sl})}
    (sliceSBCPlLmap {c} {sl})
  $ SliceWhiskerLeft
    {g=(SliceIdF $ Sigma sl)}
    {h=(SliceSBCPlMonad {sl})}
    (SliceSBCPlUnit {c} {sl})
    (SliceSBCPlR {sl})

-- This is the multiplication (AKA "join") of the right induced adjoint pair
-- of the dependent-sum/base-change/dependent-product adjoint triple.
public export
SliceSBCPrJoin : {c : Type} -> {sl : SliceObj c} ->
  SliceNatTrans {x=c} {y=c}
    (SliceSBCPrMonad {c} {sl} . SliceSBCPrMonad {c} {sl})
    (SliceSBCPrMonad {c} {sl})
SliceSBCPrJoin {c} {sl} =
  SliceWhiskerRight
    {f=(SliceSBCPrComonad {sl} . SliceSBCPrL {sl})}
    {g=(SliceSBCPrL {sl})}
    {h=(SliceSBCPrR {sl})}
    (sliceSBCPrRmap {c} {sl})
  $ SliceWhiskerLeft
    {g=(SliceSBCPrComonad {sl})}
    {h=(SliceIdF c)}
    (SliceSBCPrCounit {c} {sl})
    (SliceSBCPrL {sl})

-- This is the comultiplication (AKA "duplicate") of the right induced adjoint
-- pair of the dependent-sum/base-change/dependent-product adjoint triple.
public export
SliceSBCPrDup : {c : Type} -> {sl : SliceObj c} ->
  SliceNatTrans {x=c} {y=c}
    (SliceSBCPrComonad {c} {sl})
    (SliceSBCPrComonad {c} {sl} . SliceSBCPrComonad {c} {sl})
SliceSBCPrDup {c} {sl} =
  SliceWhiskerRight
    {f=(SliceSBCPrR {sl})}
    {g=(SliceSBCPrR {sl} . SliceSBCPrComonad {sl})}
    {h=(SliceSBCPrL {sl})}
    (sliceSBCPrLmap {c} {sl})
  $ SliceWhiskerLeft
    {g=(SliceIdF c)}
    {h=(SliceSBCPrMonad {sl})}
    (SliceSBCPrUnit {c} {sl})
    (SliceSBCPrR {sl})

------------------------------------------------------------------------
---- (Co)algebras of dependent-sum/dependent-product adjoint triple ----
------------------------------------------------------------------------

-- Adjoint (co)monads, such as those induced by adjoint triples (such as
-- the dependent-sum/base-change/dependent-product adjoint triple, which is
-- implemented in the previous section), have additional properties relating
-- their (co)algebras.  See for example:
--
--  - https://ncatlab.org/nlab/show/adjoint+monad

-- Specifically, the ("Eilenberg-Moore") category of algebras over the
-- monad is equivalent to the category of coalgebras over the comonad.

public export
SBCPlAlgToCoalg : {c : Type} -> {sl : SliceObj c} ->
  (sa : SliceObj $ Sigma {a=c} sl) ->
  SliceAlg (SliceSBCPlL {c} {sl}) sa -> -- `SliceSBCPlL` is `SSMonad`
  SliceCoalg (SliceSBCPlR {c} {sl}) sa -- `SliceSBCPlR` is `SPComonad`
SBCPlAlgToCoalg {c} {sl} sa = SliceSBCPlLAdj {c} {sl} sa sa

public export
SBCPlCoalgToAlg : {c : Type} -> {sl : SliceObj c} ->
  (sa : SliceObj $ Sigma {a=c} sl) ->
  SliceCoalg (SliceSBCPlR {c} {sl}) sa -> -- `SliceSBCPlR` is `SPComonad`
  SliceAlg (SliceSBCPlL {c} {sl}) sa -- `SliceSBCPlL` is `SSMonad`
SBCPlCoalgToAlg {c} {sl} sa = SliceSBCPlRAdj {c} {sl} sa sa

public export
SBCPrAlgToCoalg : {c : Type} -> {sl : SliceObj c} ->
  (sa : SliceObj c) ->
  SliceAlg (SliceSBCPrL {c} {sl}) sa -> -- `SliceSBCPrL` is `SSComonad`
  SliceCoalg (SliceSBCPrR {c} {sl}) sa -- `SliceSBCPrR` is `SPMonad`
SBCPrAlgToCoalg {c} {sl} sa = SliceSBCPrLAdj {c} {sl} sa sa

public export
SBCPrCoalgToAlg : {c : Type} -> {sl : SliceObj c} ->
  (sa : SliceObj c) ->
  SliceCoalg (SliceSBCPrR {c} {sl}) sa -> -- `SliceSBCPrR` is `SPMonad`
  SliceAlg (SliceSBCPrL {c} {sl}) sa -- `SliceSBCPrL` is `SSComonad`
SBCPrCoalgToAlg {c} {sl} sa = SliceSBCPrRAdj {c} {sl} sa sa

--------------------------------------------------
--------------------------------------------------
---- Sigma/base-change/pi composed adjunction ----
--------------------------------------------------
--------------------------------------------------

-- Besides forming an adjoint triple, dependent-sum/base-change and
-- base-change/dependent-product can be composed across three (potentially)
-- different slice categories.  See for example:
--
--  - https://en.wikipedia.org/wiki/Adjoint_functors#Composition

-- This is the left adjoint of the composed
-- dependent-sum/dependent-product adjunction, in category-theoretic style.
public export
SliceFibSigmaPiFL : {c, d, e : Type} -> (d -> c) -> (d -> e) ->
  SliceFunctor e c
SliceFibSigmaPiFL {c} {d} {e} g f =
  SliceFibSigmaF {c=d} {d=c} g . BaseChangeF {c=e} {d} f

public export
sfsplMap : {c, d, e : Type} -> (g : d -> c) -> (f : d -> e) ->
  SliceFMap (SliceFibSigmaPiFL {c} {d} {e} g f)
sfsplMap {c} {d} {e} g f x y =
  sfsMap {c=d} {d=c} {f=g} (BaseChangeF f x) (BaseChangeF f y)
  . bcMap {c=e} {d} {f} x y

-- This is the left adjoint of the composed
-- dependent-sum/dependent-product adjunction, in dependent-type style.
public export
SliceSigmaPiFL : {c, e : Type} ->
  (d : SliceObj (c, e)) -> SliceFunctor e c
SliceSigmaPiFL {c} {e} d =
  SliceSigmaF (Sigma {a=e} . curry d)
  . BaseChangeF {c=e} {d=(Sigma {a=c} $ Sigma {a=e} . curry d)}
    (\eced => fst $ snd eced)

public export
ssplMap : {c, e : Type} ->
  (d : SliceObj (c, e)) -> SliceFMap (SliceSigmaPiFL {c} {e} d)
ssplMap {c} {e} d x y =
  ssMap {sl=(Sigma {a=e} . curry d)}
    (\eced => x $ fst $ snd $ eced)
    (\eced => y $ fst $ snd $ eced)
  . bcMap x y

-- Here we illustrate a corollary of the adjoint functor theorem:  the
-- left adjoint (`SliceSigmaPiFL`) of a covariant representable
-- (`SliceSigmaPiFR`) takes a family of `e` singletons to the existential
-- family of `e` represented objects (which in this case are of type
-- `SliceObj c`).  So `SliceCat e` is functioning as an enriching category
-- here, and `SliceCat c` is functioning as the domain of an enriched
-- copresheaf.
public export
ssplSingletonsToRepresented : {c, e : Type} -> (d : e -> SliceObj c) ->
  SliceMorphism {a=c}
    (SliceSigmaPiFL {c} {e} (uncurry $ flip d) (\ee => Unit))
    (Sigma {a=e} . flip d)
ssplSingletonsToRepresented {c} {e} d ec = DPair.fst

-- This is the right adjoint of the composed
-- dependent-sum/dependent-product adjunction, in category-theoretic style.
public export
SliceFibSigmaPiFR : {c, d, e : Type} -> (d -> e) -> (d -> c) ->
  SliceFunctor c e
SliceFibSigmaPiFR {c} {d} {e} g f =
  SliceFibPiF {c=d} {d=e} g . BaseChangeF {c} {d} f

public export
sfsprMap : {c, d, e : Type} -> (g : d -> e) -> (f : d -> c) ->
  SliceFMap (SliceFibSigmaPiFR {c} {d} {e} g f)
sfsprMap {c} {d} {e} g f x y =
  sfpMap {c=d} {d=e} {f=g} (BaseChangeF f x) (BaseChangeF f y)
  . bcMap {c} {d} {f} x y

-- This is the right adjoint of the composed
-- dependent-sum/dependent-product adjunction, in dependent-type style.
public export
SliceSigmaPiFR : {c, e : Type} ->
  (d : SliceObj (c, e)) -> SliceFunctor c e
SliceSigmaPiFR {c} {e} d =
  SlicePiF (Sigma {a=c} . flip (curry d))
  . BaseChangeF {c} {d=(Sigma {a=e} $ Sigma {a=c} . flip (curry d))}
    (\eecd => fst $ snd eecd)

public export
ssprMap : {c, e : Type} ->
  (d : SliceObj (c, e)) -> SliceFMap (SliceSigmaPiFR {c} {e} d)
ssprMap {c} {e} d x y =
  spMap {sl=(Sigma {a=c} . flip (curry d))}
    (\eecd => x $ fst $ snd $ eecd)
    (\eecd => y $ fst $ snd $ eecd)
  . bcMap x y

-- The monad of the composed dependent-sum/dependent-product adjunction.
public export
SSPMonad : {c, e : Type} -> (d : SliceObj (c, e)) -> SliceEndofunctor e
SSPMonad {c} {e} d = SliceSigmaPiFR {c} {e} d . SliceSigmaPiFL {c} {e} d

public export
sspMonadMap : {c, e : Type} -> (d : SliceObj (c, e)) ->
  SliceFMap (SSPMonad {c} {e} d)
sspMonadMap {c} {e} d x y =
  ssprMap {c} {e} d (SliceSigmaPiFL d x) (SliceSigmaPiFL d y)
  . ssplMap {c} {e} d x y

-- The comonad of the composed dependent-sum/dependent-product adjunction.
public export
SSPComonad : {c, e : Type} -> (d : SliceObj (c, e)) -> SliceEndofunctor c
SSPComonad {c} {e} d = SliceSigmaPiFL {c} {e} d . SliceSigmaPiFR {c} {e} d

public export
sspComonadMap : {c, e : Type} -> (d : SliceObj (c, e)) ->
  SliceFMap (SSPComonad {c} {e} d)
sspComonadMap {c} {e} d x y =
  ssplMap {c} {e} d (SliceSigmaPiFR d x) (SliceSigmaPiFR d y)
  . ssprMap {c} {e} d x y

-- The unit of the composed dependent-sum/dependent-product adjunction.
public export
sspUnit : {c, e : Type} -> (d : SliceObj (c, e)) ->
  SliceNatTrans {x=e} {y=e} (SliceIdF e) (SSPMonad {c} {e} d)
sspUnit {c} {e} d sc ee esc ecd = ((ee ** snd ecd) ** esc)

-- The counit of the composed dependent-sum/dependent-product adjunction.
public export
sspCounit : {c, e : Type} -> (d : SliceObj (c, e)) ->
  SliceNatTrans {x=c} {y=c} (SSPComonad {c} {e} d) (SliceIdF c)
sspCounit {c} {e} d sc ec pisc = snd pisc (ec ** snd $ fst pisc)

-- The left adjunct of the composed dependent-sum/dependent-product adjunction.
--
-- To spell out the hom-set isomorphism, of which the adjuncts are the
-- two directions, in this particular instance:
--
--     L sa -> sb == (Sigma . BC) a -> sb
--  == Sigma (BC sa) -> sb
--  == BC sa -> BC sb (Sigma/BC left adjunct)
--  == sa -> Pi (BC sb) (BC/Pi left adjunct)
--  == sa -> (Pi . BC) sb == sa -> R sb
public export
SliceSigmaPiFLAdj : {c, e : Type} -> (d : SliceObj (c, e)) ->
  (sa : SliceObj e) -> (sb : SliceObj c) ->
  SliceMorphism {a=c} (SliceSigmaPiFL d sa) sb ->
  SliceMorphism {a=e} sa (SliceSigmaPiFR d sb)
SliceSigmaPiFLAdj {c} {e} d sa sb m =
  sliceComp
    (ssprMap {c} {e} d (SliceSigmaPiFL {c} {e} d sa) sb m)
    (sspUnit {c} {e} d sa)

-- The right adjunct of the composed dependent-sum/dependent-product adjunction.
--
-- To spell out the hom-set isomorphism, of which the adjuncts are the
-- two directions, in this particular instance:
--
--     sa -> R sb == sa -> (Pi . BC)
--  == sa -> Pi (BC sb)
--  == BC sa -> BC sb (BC/Pi right adjunct)
--  == Sigma (BC sa) -> sb (Sigma/BC left adjunct)
--  == (Sigma . BC) sa -> sb == L sa -> sb
public export
SliceSigmaPiFRAdj : {c, e : Type} -> (d : SliceObj (c, e)) ->
  (sa : SliceObj e) -> (sb : SliceObj c) ->
  SliceMorphism {a=e} sa (SliceSigmaPiFR d sb) ->
  SliceMorphism {a=c} (SliceSigmaPiFL d sa) sb
SliceSigmaPiFRAdj {c} {e} d sa sb m =
  sliceComp
    (sspCounit {c} {e} d sb)
    (ssplMap {c} {e} d sa (SliceSigmaPiFR {c} {e} d sb) m)

-- The multiplication (AKA "join") of the composed
-- dependent-sum/dependent-product adjunction.
public export
SliceSigmaPiFJoin : {c, e : Type} -> {d : SliceObj (c, e)} ->
  SliceNatTrans {x=e} {y=e}
    (SSPMonad {c} {e} d . SSPMonad {c} {e} d)
    (SSPMonad {c} {e} d)
SliceSigmaPiFJoin {c} {e} {d} =
  SliceWhiskerRight
    {f=(SSPComonad {c} {e} d . SliceSigmaPiFL {c} {e} d)}
    {g=(SliceSigmaPiFL {c} {e} d)}
    {h=(SliceSigmaPiFR {c} {e} d)}
    (ssprMap {c} {e} d)
  $ SliceWhiskerLeft
    {g=(SSPComonad {c} {e} d)}
    {h=(SliceIdF c)}
    (sspCounit {c} {e} d)
    (SliceSigmaPiFL {c} {e} d)

-- The comultiplication (AKA "duplicate") of the composed
-- dependent-sum/dependent-product adjunction.
public export
SliceSigmaPiFDup : {c, e : Type} -> {d : SliceObj (c, e)} ->
  SliceNatTrans {x=c} {y=c}
    (SSPComonad {c} {e} d)
    (SSPComonad {c} {e} d . SSPComonad {c} {e} d)
SliceSigmaPiFDup {c} {e} {d} =
  SliceWhiskerRight
    {f=(SliceSigmaPiFR {c} {e} d)}
    {g=(SliceSigmaPiFR {c} {e} d . SSPComonad {c} {e} d)}
    {h=(SliceSigmaPiFL {c} {e} d)}
    (ssplMap {c} {e} d)
  $ SliceWhiskerLeft
    {g=(SliceIdF e)}
    {h=(SSPMonad {c} {e} d)}
    (sspUnit {c} {e} d)
    (SliceSigmaPiFR {c} {e} d)

----------------------------------
----------------------------------
---- Slice-functor (co)limits ----
----------------------------------
----------------------------------

------------------------------------------------
---- Definitions of triply-adjoint functors ----
------------------------------------------------

-- The diagonal slice functor, from the slice category over `b` to the functor
-- category from the slice category over `a` to the slice catgory over `b`.
-- This is in particular the functor whose adjoints generate limits and
-- colimits in the slice category over `b` of diagrams indexed by the slice
-- category over `a` (AKA limits and colimits of functors from the slice
-- category over `a` to the slice category over `b`).  This means that it is
-- the intermediate functor in the triple adjunction of
-- colimit |- diagonal |- limit.
public export
SliceDiagF : {a, b : Type} -> SliceObj b -> SliceFunctor a b
SliceDiagF {a} {b} sb sa = sb

-- This is the morphism component of the diagonal functor.
public export
SliceDiagFmor : {a, b : Type} -> (sb : SliceObj b) -> SliceFMap (SliceDiagF sb)
SliceDiagFmor {a} {b} sb x y mxy = SliceId b sb

public export
SliceDiagFSigOmap : (a, b : Type) -> SliceObj b -> icObj (SliceFuncCat a b)
SliceDiagFSigOmap a b sb =
  IFunctor (SliceDiagF {a} {b} sb) (SliceDiagFmor {a} {b} sb)

public export
sliceDiagFmap : {a, b : Type} ->
  IntFMapSig
    (icMor $ SliceCat b)
    (icMor $ SliceFuncCat a b)
    (SliceDiagFSigOmap a b)
sliceDiagFmap {a} {b} sb sb' m sa = m

public export
SliceDiagFSig : (a, b : Type) ->
  icObj (IntFunctorCatSig (SliceCat b) (SliceFuncCat a b))
SliceDiagFSig a b = IFunctor (SliceDiagFSigOmap a b) (sliceDiagFmap {a} {b})

-- Equating `SliceObj Void` with the terminal category, we can use and
-- simplify the left-Kan-extension formula to define the colimit of a
-- slice functor.
public export
SliceFColimit : {a, b : Type} -> SliceFunctor a b -> SliceObj b
SliceFColimit {a} {b} f = Sigma {a=(SliceObj a)} . flip f

public export
sliceFColimitMap : {a, b : Type} -> (f, g : SliceFunctor a b) ->
  SliceNatTrans {x=a} {y=b} f g ->
  SliceMorphism {a=b} (SliceFColimit f) (SliceFColimit g)
sliceFColimitMap {a} {b} f g alpha eb = dpMapSnd $ \sa => alpha sa eb

public export
SliceFColimitFSig : (a, b : Type) ->
  icObj (IntFunctorCatSig (SliceFuncCat a b) (SliceCat b))
SliceFColimitFSig a b =
  IFunctor
    (SliceFColimit {a} {b} . ifOmap)
    (\f, g => sliceFColimitMap {a} {b} (ifOmap f) (ifOmap g))

-- Again equating `SliceObj Void` with the terminal category, we can use and
-- simplify the right-Kan-extension formula to define the limit of a
-- slice functor.
public export
SliceFLimit : {a, b : Type} -> SliceFunctor a b -> SliceObj b
SliceFLimit {a} {b} f = Pi {a=(SliceObj a)} . flip f

public export
sliceFLimitMap : {a, b : Type} -> (f, g : SliceFunctor a b) ->
  SliceNatTrans {x=a} {y=b} f g ->
  SliceMorphism {a=b} (SliceFLimit f) (SliceFLimit g)
sliceFLimitMap {a} {b} f g alpha eb pi sa = alpha sa eb $ pi sa

public export
SliceFLimitFSig : (a, b : Type) ->
  icObj (IntFunctorCatSig (SliceFuncCat a b) (SliceCat b))
SliceFLimitFSig a b =
  IFunctor
    (SliceFLimit {a} {b} . ifOmap)
    (\f, g => sliceFLimitMap {a} {b} (ifOmap f) (ifOmap g))

---------------------
---- Adjunctions ----
---------------------

public export
SliceFColimitAdjL : (a, b : Type) -> SliceFunctor a b -> SliceObj b
SliceFColimitAdjL a b = SliceFColimit {a} {b}

public export
SliceFColimitAdjLMap : (a, b : Type) ->
  IntAdjLMapSig {c=(SliceFunctor a b)} {d=(SliceObj b)}
    (SliceMor b) (SliceNatTrans {x=a} {y=b}) (SliceFColimitAdjL a b)
SliceFColimitAdjLMap a b = sliceFColimitMap {a} {b}

public export
SliceFColimitAdjLFSig : (a, b : Type) ->
  IntFunctorSig (SliceFuncCat a b) (SliceCat b)
SliceFColimitAdjLFSig = SliceFColimitFSig

public export
SliceFColimitAdjR : (a, b : Type) -> SliceObj b -> SliceFunctor a b
SliceFColimitAdjR a b = SliceDiagF {a} {b}

public export
SliceFColimitAdjRMap : (a, b : Type) ->
  IntAdjRMapSig {c=(SliceFunctor a b)} {d=(SliceObj b)}
    (SliceMor b) (SliceNatTrans {x=a} {y=b}) (SliceFColimitAdjR a b)
SliceFColimitAdjRMap a b = sliceDiagFmap {a} {b}

public export
SliceFColimitAdjRFSig : (a, b : Type) ->
  IntFunctorSig (SliceCat b) (SliceFuncCat a b)
SliceFColimitAdjRFSig = SliceDiagFSig

public export
SliceFLimitAdjL : (a, b : Type) -> SliceObj b -> SliceFunctor a b
SliceFLimitAdjL a b = SliceDiagF {a} {b}

public export
SliceFLimitAdjLMap : (a, b : Type) ->
  IntAdjLMapSig {c=(SliceObj b)} {d=(SliceFunctor a b)}
    (SliceNatTrans {x=a} {y=b}) (SliceMor b) (SliceFLimitAdjL a b)
SliceFLimitAdjLMap a b = sliceDiagFmap {a} {b}

public export
SliceFLimitAdjLFSig : (a, b : Type) ->
  IntFunctorSig (SliceCat b) (SliceFuncCat a b)
SliceFLimitAdjLFSig = SliceDiagFSig

public export
SliceFLimitAdjR : (a, b : Type) -> SliceFunctor a b -> SliceObj b
SliceFLimitAdjR a b = SliceFLimit {a} {b}

public export
SliceFLimitAdjRMap : (a, b : Type) ->
  IntAdjRMapSig {c=(SliceObj b)} {d=(SliceFunctor a b)}
    (SliceNatTrans {x=a} {y=b}) (SliceMor b) (SliceFLimitAdjR a b)
SliceFLimitAdjRMap a b = sliceFLimitMap {a} {b}

public export
SliceFLimitAdjRFSig : (a, b : Type) ->
  IntFunctorSig (SliceFuncCat a b) (SliceCat b)
SliceFLimitAdjRFSig = SliceFLimitFSig

public export
SliceFColimitMonad : (a, b : Type) -> SliceFunctor a b -> SliceFunctor a b
SliceFColimitMonad a b = IntAdjMonad {c=(SliceFunctor a b)} {d=(SliceObj b)}
  (SliceFColimitAdjL a b) (SliceFColimitAdjR a b)

public export
SliceFColimitComonad : (a, b : Type) -> SliceEndofunctor b
SliceFColimitComonad a b = IntAdjComonad {c=(SliceFunctor a b)} {d=(SliceObj b)}
  (SliceFColimitAdjL a b) (SliceFColimitAdjR a b)

public export
SliceFLimitMonad : (a, b : Type) -> SliceEndofunctor b
SliceFLimitMonad a b = IntAdjMonad {c=(SliceObj b)} {d=(SliceFunctor a b)}
  (SliceFLimitAdjL a b) (SliceFLimitAdjR a b)

public export
SliceFLimitComonad : (a, b : Type) -> SliceFunctor a b -> SliceFunctor a b
SliceFLimitComonad a b = IntAdjComonad {c=(SliceObj b)} {d=(SliceFunctor a b)}
  (SliceFLimitAdjL a b) (SliceFLimitAdjR a b)

public export
SliceFColimitUnit : (a, b : Type) ->
  IntAdjUnitSig {c=(SliceFunctor a b)} {d=(SliceObj b)}
    (SliceNatTrans {x=a} {y=b}) (SliceFColimitAdjL a b) (SliceFColimitAdjR a b)
SliceFColimitUnit a b fab sa eb ef = (sa ** ef)

public export
SliceFColimitCounit : (a, b : Type) ->
  IntAdjCounitSig {c=(SliceFunctor a b)} {d=(SliceObj b)}
    (SliceMor b) (SliceFColimitAdjL a b) (SliceFColimitAdjR a b)
SliceFColimitCounit a b sb eb = DPair.snd

public export
SliceFLimitUnit : (a, b : Type) ->
  IntAdjUnitSig {c=(SliceObj b)} {d=(SliceFunctor a b)}
    (SliceMor b) (SliceFLimitAdjL a b) (SliceFLimitAdjR a b)
SliceFLimitUnit a b sb eb esx sa = esx

public export
SliceFLimitCounit : (a, b : Type) ->
  IntAdjCounitSig {c=(SliceObj b)} {d=(SliceFunctor a b)}
    (SliceNatTrans {x=a} {y=b}) (SliceFLimitAdjL a b) (SliceFLimitAdjR a b)
SliceFLimitCounit a b fab sa eb fpi = fpi sa

public export
SliceFColimitAdjoints : (a, b : Type) ->
  IntAdjointsSig (SliceCat b) (SliceFuncCat a b)
SliceFColimitAdjoints a b =
  IAdjoints (SliceFColimitAdjLFSig a b) (SliceFColimitAdjRFSig a b)

public export
SliceFLimitAdjoints : (a, b : Type) ->
  IntAdjointsSig (SliceFuncCat a b) (SliceCat b)
SliceFLimitAdjoints a b =
  IAdjoints (SliceFLimitAdjLFSig a b) (SliceFLimitAdjRFSig a b)

public export
SliceFColimitUnits : (a, b : Type) ->
  IntUnitsSig (SliceFColimitAdjoints a b)
SliceFColimitUnits a b =
  IUnits
    (\f => SliceFColimitUnit a b $ ifOmap f)
    (SliceFColimitCounit a b)

public export
SliceFLimitUnits : (a, b : Type) ->
  IntUnitsSig (SliceFLimitAdjoints a b)
SliceFLimitUnits a b =
  IUnits
    (SliceFLimitUnit a b)
    (\f => SliceFLimitCounit a b $ ifOmap f)

public export
SliceFColimitAdj : (a, b : Type) ->
  IntAdjunctionSig (SliceCat b) (SliceFuncCat a b)
SliceFColimitAdj a b =
  IntAdjunctionFromUnits (SliceFColimitAdjoints a b) (SliceFColimitUnits a b)

public export
SliceFLimitAdj : (a, b : Type) ->
  IntAdjunctionSig (SliceFuncCat a b) (SliceCat b)
SliceFLimitAdj a b =
  IntAdjunctionFromUnits (SliceFLimitAdjoints a b) (SliceFLimitUnits a b)

public export
SliceFLimitColimitTripleAdjoints : (a, b : Type) ->
  IntTripleAdjointsSig (SliceFuncCat a b) (SliceCat b)
SliceFLimitColimitTripleAdjoints a b =
  ITripleAdjoints
    (SliceFColimitFSig a b)
    (SliceDiagFSig a b)
    (SliceFLimitFSig a b)

public export
SliceFLimitTripleUnitsSig : (a, b : Type) ->
  ITAUnitsSig (SliceFLimitColimitTripleAdjoints a b)
SliceFLimitTripleUnitsSig a b =
  ITUnits
    (SliceFColimitUnits a b)
    (SliceFLimitUnits a b)

public export
SliceFLimitTripleAdjunctionSig : (a, b : Type) ->
  ITASig (SliceFuncCat a b) (SliceCat b)
SliceFLimitTripleAdjunctionSig a b =
  ITAFromUnits
    (SliceFLimitColimitTripleAdjoints a b)
    (SliceFLimitTripleUnitsSig a b)

-------------------------------------------------------------------
---- Computed adjunction data (introduction/elimination rules) ----
-------------------------------------------------------------------

public export
sliceFColimitAdjLAdj : {a, b : Type} ->
  (fa : SliceFunctor a b) -> (fm : SliceFMap fa) -> (sb : SliceObj b) ->
  SliceMor b (SliceFColimit fa) sb ->
  SliceNatTrans {x=a} {y=b} fa (SliceDiagF {a} {b} sb)
sliceFColimitAdjLAdj {a} {b} fa fm =
  iasLAdj (SliceFColimitAdj a b) (IFunctor fa fm)

public export
sliceFColimitAdjRAdj : {a, b : Type} ->
  (fa : SliceFunctor a b) -> (fm : SliceFMap fa) -> (sb : SliceObj b) ->
  SliceNatTrans {x=a} {y=b} fa (SliceDiagF {a} {b} sb) ->
  SliceMor b (SliceFColimit fa) sb
sliceFColimitAdjRAdj {a} {b} fa fm =
  iasRAdj (SliceFColimitAdj a b) (IFunctor fa fm)

public export
sliceFColimitAdjMult : {a, b : Type} ->
  (fa : SliceFunctor a b) -> (fm : SliceFMap fa) ->
  SliceNatTrans {x=a} {y=b}
    (SliceFColimitMonad a b (SliceFColimitMonad a b fa))
    (SliceFColimitMonad a b fa)
sliceFColimitAdjMult {a} {b} fa fm =
  iasMult (SliceFColimitAdj a b) (IFunctor fa fm)

public export
sliceFColimitAdjComult : {a, b : Type} ->
  (sb : SliceObj b) ->
  SliceMorphism {a=b}
    (SliceFColimitComonad a b sb)
    (SliceFColimitComonad a b (SliceFColimitComonad a b sb))
sliceFColimitAdjComult {a} {b} =
  iasComult (SliceFColimitAdj a b)

public export
sliceFLimitAdjLAdj : {a, b : Type} ->
  (sa : SliceObj b) -> (fb : SliceFunctor a b) -> (fm : SliceFMap fb) ->
  SliceNatTrans {x=a} {y=b} (SliceDiagF {a} {b} sa) fb ->
  SliceMor b sa (SliceFLimit fb)
sliceFLimitAdjLAdj {a} {b} sa fb fm =
  iasLAdj (SliceFLimitAdj a b) sa (IFunctor fb fm)

public export
sliceFLimitAdjRAdj : {a, b : Type} ->
  (sa : SliceObj b) -> (fb : SliceFunctor a b) -> (fm : SliceFMap fb) ->
  SliceMor b sa (SliceFLimit fb) ->
  SliceNatTrans {x=a} {y=b} (SliceDiagF {a} {b} sa) fb
sliceFLimitAdjRAdj {a} {b} sa fb fm =
  iasRAdj (SliceFLimitAdj a b) sa (IFunctor fb fm)

public export
sliceFLimitAdjMult : {a, b : Type} ->
  SliceNatTrans {x=b} {y=b}
    (SliceFLimitMonad a b . SliceFLimitMonad a b)
    (SliceFLimitMonad a b)
sliceFLimitAdjMult {a} {b} =
  iasMult (SliceFLimitAdj a b)

public export
sliceFLimitAdjComult : {a, b : Type} ->
  (fb : SliceFunctor a b) -> (fm : SliceFMap fb) ->
  SliceNatTrans {x=a} {y=b}
    (SliceFLimitComonad a b fb)
    (SliceFLimitComonad a b (SliceFLimitComonad a b fb))
sliceFLimitAdjComult {a} {b} fb fm =
  iasComult (SliceFLimitAdj a b) (IFunctor fb fm)

---------------------------------
---------------------------------
----- (Slice) Kan extensions ----
---------------------------------
---------------------------------

------------------------------------------------
---- Definitions of triply-adjoint functors ----
------------------------------------------------

-- An explicit name for the precomposition functors across slice categories,
-- partly for use as the intermediate functor in the triple adjunction of
-- left-Kan-extension |- precomposition |- right-Kan-extension.
public export
SlicePrecompF : {a, b, c : Type} ->
  SliceFunctor a c -> SliceFunctor c b -> SliceFunctor a b
SlicePrecompF {a} {b} {c} =
  flip $ (.) {a=(SliceObj a)} {b=(SliceObj c)} {c=(SliceObj b)}

public export
SlicePrecompFmor : {a, b, c : Type} ->
  (g : SliceFunctor a c) -> (f : SliceFunctor c b) ->
  (gm : SliceFMap g) -> (fm : SliceFMap f) ->
  SliceFMap (SlicePrecompF g f)
SlicePrecompFmor {a} {b} {c} g f gm fm x y = fm (g x) (g y) . gm x y

public export
SlicePrecompFSigOmap : (a, b, c : Type) ->
  (f : SliceFunctor a c) -> (fm : SliceFMap f) ->
  icObj (SliceFuncCat c b) -> icObj (SliceFuncCat a b)
SlicePrecompFSigOmap a b c f fm g =
  IFunctor
    (SlicePrecompF f (ifOmap g))
    (SlicePrecompFmor f (ifOmap g) fm (ifMmap g))

public export
slicePrecompFmap : {a, b, c : Type} -> (f : SliceFunctor a c) ->
  {g, h : SliceFunctor c b} ->
  SliceNatTrans {x=c} {y=b} g h ->
  SliceNatTrans {x=a} {y=b} (SlicePrecompF f g) (SlicePrecompF f h)
slicePrecompFmap {a} {b} {c} f {g} {h} alpha = SliceWhiskerLeft {g} {h} alpha f

public export
SlicePrecompFSig : (a, b, c : Type) ->
  (f : SliceFunctor a c) -> (fm : SliceFMap f) ->
  IntFunctorSig (SliceFuncCat c b) (SliceFuncCat a b)
SlicePrecompFSig a b c f fm =
  IFunctor
    (SlicePrecompFSigOmap a b c f fm)
    (\g, h => slicePrecompFmap {a} {b} f {g=(ifOmap g)} {h=(ifOmap h)})

-- The left Kan extension of `f` (the second parameter) along
-- `g` (the first parameter).
public export
SliceLKanExt : {a, b, c : Type} ->
  SliceFunctor a c -> SliceFunctor a b -> SliceFunctor c b
SliceLKanExt {a} {b} {c} g f sc eb =
  (sa : SliceObj a ** (Pi {a=c} $ SliceHom (g sa) sc, f sa eb))

public export
SliceLKanExtMor : {a, b, c : Type} ->
  (g : SliceFunctor a c) -> (f : SliceFunctor a b) ->
  SliceFMap (SliceLKanExt g f)
SliceLKanExtMor {a} {b} {c} g f x y mxy eb =
  dpMapSnd $ \sa => mapFst $ sliceComp {a=c} mxy

public export
SliceLKanExtSigOmap : (a, b, c : Type) ->
  (g : SliceFunctor a c) ->
  icObj (SliceFuncCat a b) -> icObj (SliceFuncCat c b)
SliceLKanExtSigOmap a b c g f =
  IFunctor (SliceLKanExt g (ifOmap f)) (SliceLKanExtMor g (ifOmap f))

public export
sliceLKanExtFmap : {a, b, c : Type} ->
  (g : SliceFunctor a c) ->
  {f, h : SliceFunctor a b} ->
  SliceNatTrans {x=a} {y=b} f h ->
  SliceNatTrans {x=c} {y=b} (SliceLKanExt g f) (SliceLKanExt g h)
sliceLKanExtFmap {a} {b} {c} g {f} {h} alpha sc eb =
  dpMapSnd $ \sa => mapSnd $ alpha sa eb

public export
SliceLKanExtSig : (a, b, c : Type) ->
  (g : SliceFunctor a c) ->
  IntFunctorSig (SliceFuncCat a b) (SliceFuncCat c b)
SliceLKanExtSig a b c g =
  IFunctor
    (SliceLKanExtSigOmap a b c g)
    (\f, h => sliceLKanExtFmap g {f=(ifOmap f)} {h=(ifOmap h)})

public export
SliceLKanExtAdjoints : (a, b, c : Type) ->
  (g : SliceFunctor a c) -> (gm : SliceFMap g) ->
  IntAdjointsSig (SliceFuncCat c b) (SliceFuncCat a b)
SliceLKanExtAdjoints a b c g gm =
  IAdjoints
    (SliceLKanExtSig a b c g)
    (SlicePrecompFSig a b c g gm)

public export
SliceLKanExtAdjUnits : (a, b, c : Type) ->
  (g : SliceFunctor a c) -> (gm : SliceFMap g) ->
  IntUnitsSig (SliceLKanExtAdjoints a b c g gm)
SliceLKanExtAdjUnits a b c g gm =
  IUnits
    (\f, sa, eb, efb => (sa ** (SliceId c (g sa), efb)))
    (\f, sc, eb, lk =>
      ifMmap f (g $ fst lk) sc (fst $ snd lk) eb $ snd $ snd lk)

public export
SliceLKanExtAdjUnitInputs : (a, b, c : Type) ->
  (g : SliceFunctor a c) -> (gm : SliceFMap g) ->
  IntAdjUnitInputs (SliceFuncCat c b) (SliceFuncCat a b)
SliceLKanExtAdjUnitInputs a b c g gm =
  IAdjUIn
    (SliceLKanExtAdjoints a b c g gm)
    (SliceLKanExtAdjUnits a b c g gm)

public export
SliceLKanExtAdjunctionSig : (a, b, c : Type) ->
  (g : SliceFunctor a c) -> (gm : SliceFMap g) ->
  IntAdjunctionSig (SliceFuncCat c b) (SliceFuncCat a b)
SliceLKanExtAdjunctionSig a b c g gm =
  IntAdjunctionFromUnitInputs
    {d=(SliceFuncCat c b)}
    {c=(SliceFuncCat a b)}
    (SliceLKanExtAdjUnitInputs a b c g gm)

-- The right Kan extension of `f` (the second parameter) along
-- `g` (the first parameter).
public export
SliceRKanExt : {a, b, c : Type} ->
  SliceFunctor a c -> SliceFunctor a b -> SliceFunctor c b
SliceRKanExt {a} {b} {c} g f sc eb =
  -- Conceptually the definition below is equivalent to:
  --  SliceNatTrans {x=a} {y=Unit}
  --    (flip $ \_ => SliceMorphism sc . g)
  --    (flip $ \_ => flip f eb)
  (sa : SliceObj a) -> Pi {a=c} (SliceHom sc (g sa)) -> f sa eb

public export
SliceRKanExtMor : {a, b, c : Type} ->
  (g : SliceFunctor a c) -> (f : SliceFunctor a b) ->
  SliceFMap (SliceRKanExt g f)
SliceRKanExtMor {a} {b} {c} g f sc y mxy eb rk sa =
  flip (sliceComp {a=c}) mxy |> rk sa

public export
SliceRKanExtSigOmap : (a, b, c : Type) ->
  (g : SliceFunctor a c) ->
  icObj (SliceFuncCat a b) -> icObj (SliceFuncCat c b)
SliceRKanExtSigOmap a b c g f =
  IFunctor (SliceRKanExt g (ifOmap f)) (SliceRKanExtMor g (ifOmap f))

public export
sliceRKanExtFmap : {a, b, c : Type} ->
  (g : SliceFunctor a c) ->
  {f, h : SliceFunctor a b} ->
  SliceNatTrans {x=a} {y=b} f h ->
  SliceNatTrans {x=c} {y=b} (SliceRKanExt g f) (SliceRKanExt g h)
sliceRKanExtFmap {a} {b} {c} g {f} {h} alpha sc eb pi sa =
  alpha sa eb . pi sa

public export
SliceRKanExtSig : (a, b, c : Type) ->
  (g : SliceFunctor a c) ->
  IntFunctorSig (SliceFuncCat a b) (SliceFuncCat c b)
SliceRKanExtSig a b c g =
  IFunctor
    (SliceRKanExtSigOmap a b c g)
    (\f, h => sliceRKanExtFmap g {f=(ifOmap f)} {h=(ifOmap h)})

public export
SliceRKanExtAdjoints : (a, b, c : Type) ->
  (g : SliceFunctor a c) -> (gm : SliceFMap g) ->
  IntAdjointsSig (SliceFuncCat a b) (SliceFuncCat c b)
SliceRKanExtAdjoints a b c g gm =
  IAdjoints
    (SlicePrecompFSig a b c g gm)
    (SliceRKanExtSig a b c g)

public export
SliceRKanExtAdjUnits : (a, b, c : Type) ->
  (g : SliceFunctor a c) -> (gm : SliceFMap g) ->
  IntUnitsSig (SliceRKanExtAdjoints a b c g gm)
SliceRKanExtAdjUnits a b c g gm =
  IUnits
    (\f, sc, eb, efb, sa, rk => ifMmap f sc (g sa) rk eb efb)
    (\f, sa, eb, rk => rk sa $ SliceId c $ g sa)

public export
SliceRKanExtAdjUnitInputs : (a, b, c : Type) ->
  (g : SliceFunctor a c) -> (gm : SliceFMap g) ->
  IntAdjUnitInputs (SliceFuncCat a b) (SliceFuncCat c b)
SliceRKanExtAdjUnitInputs a b c g gm =
  IAdjUIn
    (SliceRKanExtAdjoints a b c g gm)
    (SliceRKanExtAdjUnits a b c g gm)

public export
SliceRKanExtAdjunctionSig : (a, b, c : Type) ->
  (g : SliceFunctor a c) -> (gm : SliceFMap g) ->
  IntAdjunctionSig (SliceFuncCat a b) (SliceFuncCat c b)
SliceRKanExtAdjunctionSig a b c g gm =
  IntAdjunctionFromUnitInputs
    {d=(SliceFuncCat a b)}
    {c=(SliceFuncCat c b)}
    (SliceRKanExtAdjUnitInputs a b c g gm)

public export
SliceKanExtTripleAdjoints : (a, b, c : Type) ->
  (g : SliceFunctor a c) -> (gm : SliceFMap g) ->
  IntTripleAdjointsSig (SliceFuncCat a b) (SliceFuncCat c b)
SliceKanExtTripleAdjoints a b c g gm =
  ITripleAdjoints
    (SliceLKanExtSig a b c g)
    (SlicePrecompFSig a b c g gm)
    (SliceRKanExtSig a b c g)

public export
SliceKanExtTripleUnitsSig : (a, b, c : Type) ->
  (g : SliceFunctor a c) -> (gm : SliceFMap g) ->
  ITAUnitsSig (SliceKanExtTripleAdjoints a b c g gm)
SliceKanExtTripleUnitsSig a b c g gm =
  ITUnits
    (SliceLKanExtAdjUnits a b c g gm)
    (SliceRKanExtAdjUnits a b c g gm)

public export
SliceKanExtTripleAdjunctionSig : (a, b, c : Type) ->
  (g : SliceFunctor a c) -> (gm : SliceFMap g) ->
  ITASig (SliceFuncCat a b) (SliceFuncCat c b)
SliceKanExtTripleAdjunctionSig a b c g gm=
  ITAFromUnits
    (SliceKanExtTripleAdjoints a b c g gm)
    (SliceKanExtTripleUnitsSig a b c g gm)

----------------------------
----------------------------
----- (Slice) Kan lifts ----
----------------------------
----------------------------

------------------------------------------------
---- Definitions of triply-adjoint functors ----
------------------------------------------------

-- An explicit name for the postcomposition functors across slice categories,
-- partly for use as the intermediate functor in the triple adjunction of
-- left-Kan-lift |- postcomposition |- right-Kan-lift.
public export
SlicePostcompF : {a, b, c : Type} ->
  SliceFunctor c a -> SliceFunctor b c -> SliceFunctor b a
SlicePostcompF {a} {b} {c} =
  (.) {a=(SliceObj b)} {b=(SliceObj c)} {c=(SliceObj a)}

public export
SlicePostcompFmor : {a, b, c : Type} ->
  (g : SliceFunctor c a) -> (f : SliceFunctor b c) ->
  (gm : SliceFMap g) -> (fm : SliceFMap f) ->
  SliceFMap (SlicePostcompF g f)
SlicePostcompFmor {a} {b} {c} g f gm fm x y = gm (f x) (f y) . fm x y

public export
SlicePostcompFSigOmap : (a, b, c : Type) ->
  (f : SliceFunctor c a) -> (fm : SliceFMap f) ->
  icObj (SliceFuncCat b c) -> icObj (SliceFuncCat b a)
SlicePostcompFSigOmap a b c f fm g =
  IFunctor
    (SlicePostcompF f (ifOmap g))
    (SlicePostcompFmor f (ifOmap g) fm (ifMmap g))

public export
slicePostcompFmap : {a, b, c : Type} ->
  {f : SliceFunctor c a} -> (fm : SliceFMap f) ->
  {g, h : SliceFunctor b c} ->
  SliceNatTrans {x=b} {y=c} g h ->
  SliceNatTrans {x=b} {y=a} (SlicePostcompF f g) (SlicePostcompF f h)
slicePostcompFmap {a} {b} {c} {f} fm {g} {h} =
  SliceWhiskerRight {f=g} {g=h} {h=f} fm

public export
SlicePostcompFSig : (a, b, c : Type) ->
  (f : SliceFunctor c a) -> (fm : SliceFMap f) ->
  IntFunctorSig (SliceFuncCat b c) (SliceFuncCat b a)
SlicePostcompFSig a b c f fm =
  IFunctor
    (SlicePostcompFSigOmap a b c f fm)
    (\g, h => slicePostcompFmap {a} {b} {f} fm {g=(ifOmap g)} {h=(ifOmap h)})

-- The left Kan lift of `f` (the second parameter) along
-- `g` (the first parameter).
public export
SliceLKanLift : {a, b, c : Type} ->
  SliceFunctor c a -> SliceFunctor b a -> SliceFunctor b c
SliceLKanLift {a} {b} {c} g f sb ec =
  (h : SliceFunctor b c) -> (hm : SliceFMap h) ->
  SliceNatTrans {x=b} {y=a} f (g . h) -> h sb ec

public export
SliceLKanLiftMor : {a, b, c : Type} ->
  (g : SliceFunctor c a) -> (f : SliceFunctor b a) ->
  SliceFMap (SliceLKanLift g f)
SliceLKanLiftMor {a} {b} {c} g f x y mxy ec lkl h hm alpha =
  hm x y mxy ec $ lkl h hm alpha

public export
SliceLKanLiftSigOmap : (a, b, c : Type) ->
  (g : SliceFunctor c a) ->
  icObj (SliceFuncCat b a) -> icObj (SliceFuncCat b c)
SliceLKanLiftSigOmap a b c g f =
  IFunctor (SliceLKanLift g (ifOmap f)) (SliceLKanLiftMor g (ifOmap f))

public export
sliceLKanLiftFmap : {a, b, c : Type} ->
  (g : SliceFunctor c a) ->
  {f, h : SliceFunctor b a} ->
  SliceNatTrans {x=b} {y=a} f h ->
  SliceNatTrans {x=b} {y=c} (SliceLKanLift g f) (SliceLKanLift g h)
sliceLKanLiftFmap {a} {b} {c} g {f} {h} alpha sb ec lkl j jm beta =
  lkl j jm $ SliceNTvcomp beta alpha

public export
SliceLKanLiftSig : (a, b, c : Type) ->
  (g : SliceFunctor c a) ->
  IntFunctorSig (SliceFuncCat b a) (SliceFuncCat b c)
SliceLKanLiftSig a b c g =
  IFunctor
    (SliceLKanLiftSigOmap a b c g)
    (\f, h => sliceLKanLiftFmap g {f=(ifOmap f)} {h=(ifOmap h)})

-- The right Kan lift (AKA "rift") of `f` (the second parameter) along
-- `g` (the first parameter).
public export
SliceRKanLift : {a, b, c : Type} ->
  SliceFunctor c a -> SliceFunctor b a -> SliceFunctor b c
SliceRKanLift {a} {b} {c} g f sb ec =
  (h : SliceFunctor b c ** hm : SliceFMap h **
   (SliceNatTrans {x=b} {y=a} (g . h) f, h sb ec))

public export
SliceRKanLiftMor : {a, b, c : Type} ->
  (g : SliceFunctor c a) -> (f : SliceFunctor b a) ->
  SliceFMap (SliceRKanLift g f)
SliceRKanLiftMor {a} {b} {c} g f x y mxy ec =
  dpMapSnd (\h => dpMapSnd $ \hm => mapSnd $ hm x y mxy ec)

public export
SliceRKanLiftSigOmap : (a, b, c : Type) ->
  (g : SliceFunctor c a) ->
  icObj (SliceFuncCat b a) -> icObj (SliceFuncCat b c)
SliceRKanLiftSigOmap a b c g f =
  IFunctor (SliceRKanLift g (ifOmap f)) (SliceRKanLiftMor g (ifOmap f))

public export
sliceRKanLiftFmap : {a, b, c : Type} ->
  (g : SliceFunctor c a) ->
  {f, h : SliceFunctor b a} ->
  SliceNatTrans {x=b} {y=a} f h ->
  SliceNatTrans {x=b} {y=c} (SliceRKanLift g f) (SliceRKanLift g h)
sliceRKanLiftFmap {a} {b} {c} g {f} {h} alpha sb ec =
  dpMapSnd $ \j => dpMapSnd $ \jm => mapFst $ SliceNTvcomp alpha

public export
SliceRKanLiftSig : (a, b, c : Type) ->
  (g : SliceFunctor c a) ->
  IntFunctorSig (SliceFuncCat b a) (SliceFuncCat b c)
SliceRKanLiftSig a b c g =
  IFunctor
    (SliceRKanLiftSigOmap a b c g)
    (\f, h => sliceRKanLiftFmap g {f=(ifOmap f)} {h=(ifOmap h)})

--------------------------------
--------------------------------
---- Initial slice algebras ----
--------------------------------
--------------------------------

-- The impredicative initial algebra of an endofunctor on `SliceObj c`.
public export
ImSliceMu : {c : Type} -> SliceEndofunctor c -> SliceObj c
ImSliceMu {c} f ec =
  SliceNatTrans {x=c} {y=Unit} (\sc, () => SliceAlg f sc) (\sc, () => sc ec)

public export
imSlCata : {0 c : Type} -> {0 f : SliceEndofunctor c} ->
  {sa : SliceObj c} ->
  SliceAlg f sa -> SliceMorphism {a=c} (ImSliceMu {c} f) sa
imSlCata {c} {f} {sa} alg ec mu = mu sa () alg

public export
slMuFromIm : {c : Type} -> (f : SliceEndofunctor c) ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceMorphism (ImSliceMu f) (SliceMu f)
slMuFromIm {c} f fm ec mu =
  InSlFc {a=c} {f} {ea=ec} $ mu (f $ SliceMu f) ()
  $ fm (f $ SliceMu f) (SliceMu f) $ \ec => InSlFc {ea=ec}

public export
slMuToIm : {c : Type} -> (f : SliceEndofunctor c) ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceCata f ->
  SliceMorphism (SliceMu f) (ImSliceMu f)
slMuToIm {c} f fm fcata ec (InSlF {f} {sa=(const Void)} ec $ InSlV v) = void v
slMuToIm {c} f fm fcata ec (InSlF {f} {sa=(const Void)} ec $ InSlC t) =
  \sa, (), alg => sliceComp alg (fm (SliceMu f) sa (fcata sa alg)) ec t

public export
imSlInitAlg : {c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceCata f ->
  SliceAlg f (ImSliceMu f)
imSlInitAlg {f} fm fcata =
  sliceComp (slMuToIm f fm fcata) $ sliceComp (\ec => InSlFc {ea=ec})
  $ fm (ImSliceMu f) (SliceMu f) (slMuFromIm f fm)

public export
imSlInitAlgInv : {c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceCata f ->
  SliceCoalg f (ImSliceMu f)
imSlInitAlgInv {f} fm fcata =
  sliceComp (fm (SliceMu f) (ImSliceMu f) (slMuToIm f fm fcata))
  $ sliceComp (outSlMu f) (slMuFromIm f fm)

--------------------------------------
--------------------------------------
---- Free monad on dependent sums ----
--------------------------------------
--------------------------------------

--------------------------------
---- Pointed dependent sums ----
--------------------------------

SlicePointedSigmaF : {c, d : Type} -> (f : c -> d) ->
  SliceObj d -> SliceFunctor c d
SlicePointedSigmaF {c} {d} f = SlPointedF {c} {d} (SliceFibSigmaF {c} {d} f)

SPIAlg : {c : Type} -> (f : c -> c) -> (sv, sc : SliceObj c) -> Type
SPIAlg {c} f = SlPointedAlg {c} (SliceFibSigmaF {c} {d=c} f)

SPICoalg : {c : Type} -> (f : c -> c) -> (sv, sc : SliceObj c) -> Type
SPICoalg {c} f = SlPointedCoalg {c} (SliceFibSigmaF {c} {d=c} f)

-------------------------
---- Adjunction data ----
-------------------------

-- The free monad comes from a free-forgetful adjunction between `SliceObj c`
-- (on the right) and the category of `SliceSigmaF f`-algebras on that
-- category (on the left).
--
-- (The category of `SliceSigmaF f`-algebras on `SliceObj c` can be seen
-- as the category of elements of `SSAlg f`.)
--
-- The left adjoint takes `sc : SliceObj c` to the algebra whose object
-- component is `SliceSigmaFM f sc` and whose morphism component is
-- `SSin`.  The adjoints are part of the public interface of a universal
-- property, so we use `public export` here.
--
-- The right adjoint is the forgetful functor which simply throws away the
-- morphism component of the algebra, leaving a `SliceObj c`.
public export
data SliceSigmaFM : {0 c : Type} ->
    (0 f : c -> c) -> SliceEndofunctor c where
  SSin : {0 c : Type} -> {0 f : c -> c} -> {0 sc : SliceObj c} ->
    SPIAlg {c} f sc (SliceSigmaFM {c} f sc)

public export
SSFMAlg : {c : Type} -> (0 f : c -> c) -> (sc : SliceObj c) -> Type
SSFMAlg {c} f = SliceAlg {a=c} (SliceSigmaFM {c} f)

public export
SSFMCoalg : {c : Type} -> (0 f : c -> c) -> (sc : SliceObj c) -> Type
SSFMCoalg {c} f = SliceCoalg {a=c} (SliceSigmaFM {c} f)

-- `SSin` is an isomorphism (by Lambek's theorem); this is its inverse.
public export
SSout : {0 c : Type} -> {0 f : c -> c} -> {0 sc : SliceObj c} ->
  SPICoalg {c} f sc (SliceSigmaFM {c} f sc)
SSout {c} {f} {sc} ec (SSin ec esp) = esp

-- The (morphism component of the) free `SliceSigmaF`-algebra of
-- `SliceSigmaFM f sc`.
public export
SScom : {c : Type} -> {f : c -> c} -> {0 sc : SliceObj c} ->
  SSAlg {c} f (SliceSigmaFM {c} f sc)
SScom {c} {f} {sc} ec =
  SSin {c} {f} {sc} ec
  . inSlPc {f=(SliceFibSigmaF f)} {sl=sc} {sa=(SliceSigmaFM f sc)} ec

-- The unit of the free-monad adjunction -- a natural transformation of
-- endofunctors on `SliceObj a`, from the identity endofunctor to
-- `SliceSigmaFM f`.
public export
SSvar : {c : Type} -> {f : c -> c} ->
  SliceNatTrans (SliceIdF c) (SliceSigmaFM {c} f)
SSvar {c} {f} sc ec t =
  SSin {c} {f} {sc} ec
  $ inSlPv {f=(SliceFibSigmaF f)} {sl=sc} {sa=(SliceSigmaFM f sc)} ec t

-- The counit of the free-monad adjunction -- a natural transformation of
-- endofunctors on algebras of `SliceSigmaF f`, from `SSFMAlg` to the
-- identity endofunctor.
public export
SSFcounit : {c : Type} -> {f : c -> c} ->
  SliceMorphism {a=(SliceObj c)} (SSFMAlg {c} f) (SSAlg {c} f)
SSFcounit {c} {f} sc alg =
  sliceComp alg $ sliceComp (SScom {c} {f} {sc})
  $ sfsMap sc (SliceSigmaFM f sc)
  $ SSvar {c} {f} sc

-- `Eval` is a universal morphism of the free monad.  Specifically, it is
-- the right adjunct:  given an object `sa : SliceObj c` and an algebra
-- `sb : SliceObj c`/`alg : SSAlg f sb`, the right adjunct takes a
-- slice morphism `subst : SliceMorphism {a=c} sa sb` and returns an
-- F-algebra morphism `SliceSigmaEval sa sb alg subst :
-- SliceMorphism {a=c} (SliceSigmaFM f sa) sb`.
public export
SliceSigmaEval : {0 c : Type} -> {f : c -> c} -> (sb : SliceObj c) ->
  (alg : SSAlg f sb) ->
  SliceMorphism {a=(SliceObj c)}
    (flip (SliceMorphism {a=c}) sb)
    (flip (SliceMorphism {a=c}) sb . SliceSigmaFM {c} f)
SliceSigmaEval {c} {f} sb alg sa subst ec (SSin ec (Left v)) =
  subst ec v
SliceSigmaEval {c} {f} sb alg sa subst ec (SSin ec (Right t)) =
  alg ec $ case t of
    SFS ec' fmec => SFS ec' $ SliceSigmaEval sb alg sa subst ec' fmec

-- The left adjunct of the free monad, given an object `sa : SliceObj c` and
-- an algebra `sb : SliceObj c`/`alg : SSAlg f sb`, takes an algebra morphism
-- from the free algebra `SliceSigmaFM f sa` to `sb`, i.e. a morphism of type
-- `SliceMorphism {a=c} (SliceSigmaFM f sa) sb`, and returns a morphism
-- `subst : SliceMorphism {a=c} sa sb`.
--
-- The implementation does not use the morphism component of the algebra,
-- so we omit it from the signature.  The reason for this is that this is the
-- left adjunct of a free-forgetful adjunction, and the only use of the
-- input to the left adjunct in the formula that expresses the left adjunct in
-- terms of the unit (`SSvar`, in this case) is to apply the right adjoint to
-- it, and the right adjoint just forgets the morphism component.
public export
SliceSigmaFMLAdj : {c : Type} -> {f : c -> c} -> (sa, sb : SliceObj c) ->
  SliceMorphism {a=c} (SliceSigmaFM {c} f sa) sb ->
  SliceMorphism {a=c} sa sb
SliceSigmaFMLAdj {c} {f} sa sb eval ec = eval ec . SSvar {c} {f} sa ec

-- We show that the initial algebra of `SliceSigmaF f` is the initial object
-- of `SliceObj a`.
public export
SSMuInitial : {c : Type} -> (f : c -> c) ->
  SliceMorphism {a=c} (SliceSigmaFM {c} f $ const Void) (const Void)
SSMuInitial {c} f =
  SliceSigmaEval {c} {f} (const Void) (SSVoidAlg {c} f) (const Void) (\_ => id)

public export
ssfmMap : {c : Type} -> {f : c -> c} -> SliceFMap (SliceSigmaFM {c} f)
ssfmMap {c} {f} sa sb m =
  SliceSigmaEval {c} {f} (SliceSigmaFM {c} f sb) SScom sa
    (sliceComp (SSvar sb) m)

-- The multiplication of the free-monad adjunction, often called "join" --
-- a natural transformation of endofunctors on `SliceObj a`, from
-- `SliceSigmaFM f . SliceSigmaFM f` to `SliceSigmaFM f`.
--
-- The multiplication comes from whiskering the counit between the adjuncts.
public export
ssfJoin : {c : Type} -> {f : c -> c} ->
  SliceNatTrans
    (SliceSigmaFM {c} f . SliceSigmaFM {c} f)
    (SliceSigmaFM {c} f)
ssfJoin {c} {f} sc =
  SliceSigmaEval {c} {f} (SliceSigmaFM f sc)
    (SScom {f} {sc}) (SliceSigmaFM f sc) (sliceId $ SliceSigmaFM f sc)

-- The comultiplication (or "duplicate") of the free-monad adjunction -- a
-- natural transformation of endofunctors on algebras of `SliceSigmaF f`,
-- from `SSFMAlg` to `SSFMAlg . SliceSigmaFM`.
--
-- The comultiplication comes from whiskering the unit between the adjuncts.
-- The algebra parameter is unused because the adjunct forgets the input
-- algebra.
public export
ssfDup : {c : Type} -> {f : c -> c} ->
  SliceMorphism {a=(SliceObj c)}
    (SSFMAlg {c} f)
    (SSFMAlg {c} f . SliceSigmaFM f)
ssfDup {c} {f} sc falg = ssfJoin {c} {f} sc

-----------------------------------
-----------------------------------
---- Terminal slice coalgebras ----
-----------------------------------
-----------------------------------

-- The dependent version of `ImNu`, the impredicative terminal coalgebra
-- of an endofunctor on `SliceObj c`.
public export
data ImSliceNu : {0 c : Type} -> SliceEndofunctor c -> SliceObj c where
  ImSlN : {0 c : Type} -> {0 f : SliceEndofunctor c} ->
    {0 sa : SliceObj c} -> SliceCoalg f sa -> (ec : c) -> sa ec ->
    ImSliceNu {c} f ec

public export
imSlAna : {0 c : Type} -> {0 f : SliceEndofunctor c} ->
  {0 sa : SliceObj c} ->
  SliceCoalg f sa -> SliceMorphism {a=c} sa (ImSliceNu {c} f)
imSlAna = ImSlN

public export
imSlTermCoalg : {0 c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceCoalg f (ImSliceNu f)
imSlTermCoalg {f} fm ec (ImSlN {c} {f} {sa} coalg ec esa) =
  fm sa (ImSliceNu {c} f) (imSlAna {c} {f} {sa} coalg) ec (coalg ec esa)

-- The inverse of `imSlTermCoalg`, which we know by Lambek's theorem should
-- exist.
public export
imSlTermCoalgInv : {0 c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceAlg f (ImSliceNu f)
imSlTermCoalgInv {c} {f} fm =
  ImSlN {c} {f} {sa=(f $ ImSliceNu f)}
  $ fm (ImSliceNu f) (f $ ImSliceNu f) $ imSlTermCoalg {c} {f} fm

------------------------
------------------------
---- Cofree comonad ----
------------------------
------------------------

----------------------------------
---- Copointed dependent sums ----
----------------------------------

SliceCopointedSigmaF : {c, d : Type} -> (f : c -> d) ->
  SliceObj d -> SliceFunctor c d
SliceCopointedSigmaF {c} {d} f = SlCopointedF {c} {d} (SliceFibSigmaF {c} {d} f)

SCPIAlg : {c : Type} -> (f : c -> c) -> (sv, sc : SliceObj c) -> Type
SCPIAlg {c} f = SlCopointedAlg {c} (SliceFibSigmaF {c} {d=c} f)

SCPICoalg : {c : Type} -> (f : c -> c) -> (sv, sc : SliceObj c) -> Type
SCPICoalg {c} f = SlCopointedCoalg {c} (SliceFibSigmaF {c} {d=c} f)

-------------------------
---- Adjunction data ----
-------------------------

-- The cofree comonad comes from a forgetful-cofree adjunction between
-- `SliceObj c` (on the left) and the category of
-- `SliceSigmaF f`-coalgebras on that category (on the right).
--
-- (The category of `SliceSigmaF f`-coalgebras on `SliceObj c` can be seen
-- as the category of elements of `SSCoalg {c} f`.)
--
-- The right adjoint takes `sl : SliceObj c` to the coalgebra whose object
-- component is `(Slice)ImCofree f sl` and whose morphism component is
-- `imSlSubtrees`.
--
-- The left adjoint is the forgetful functor which simply throws away the
-- morphism component of the coalgebra, leaving a `SliceObj c`.
--
-- This is an impredicative implementation which stashes a coalgebra and a
-- labeling morphism rather than building on the metalanguage's coinductive
-- (infinite) data types, if it even has them -- thus we do not require a
-- metalanguage to have them, but instead show how coinductive types (M-types)
-- can be implemented in terms of inductive types (W-types) and higher-order
-- functions.
public export
ImSliceCofree : {0 c : Type} -> SliceEndofunctor c -> SliceEndofunctor c
ImSliceCofree {c} f sa = ImSliceNu (SlCopointedF f sa)

public export
ImSlCMAlg : {c : Type} -> (f : SliceEndofunctor c) -> SliceObj c -> Type
ImSlCMAlg {c} f = SliceAlg {a=c} (ImSliceCofree {c} f)

public export
ImSlCMCoalg : {c : Type} -> (f : SliceEndofunctor c) -> SliceObj c -> Type
ImSlCMCoalg {c} f = SliceCoalg {a=c} (ImSliceCofree {c} f)

public export
inSlCF : {0 c : Type} -> {f : SliceEndofunctor c} -> {0 sl, sa : SliceObj c} ->
  SliceMorphism {a=c} sa sl -> SliceCoalg f sa ->
  SliceMorphism {a=c} sa (ImSliceCofree f sl)
inSlCF label coalg = ImSlN {f=(SlCopointedF f sl)} $ inSlCP {f} label coalg

public export
imSlCofreeTermCoalg : {0 c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  {sl : SliceObj c} -> SlCopointedCoalg {c} f sl (ImSliceCofree {c} f sl)
imSlCofreeTermCoalg fm {sl} =
  imSlTermCoalg {f=(SlCopointedF f sl)} (mapSlCP {f} fm sl)

public export
imSlCofreeTermCoalgInv : {0 c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  {sl : SliceObj c} -> SlCopointedAlg {c} f sl (ImSliceCofree {c} f sl)
imSlCofreeTermCoalgInv fm {sl} =
  imSlTermCoalgInv {f=(SlCopointedF f sl)} (mapSlCP {f} fm sl)

-- `imSlLabel` is the counit of the (impredicative) slice cofree-comonad
-- adjunction.  That means it is also the counit of the comonad arising from
-- the adjunction; as such it is also sometimes called "erase" or "extract".
public export
imSlLabel : {c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceNatTrans {x=c} {y=c} (ImSliceCofree f) (SliceIdF c)
imSlLabel {c} {f} fm sl =
  sliceComp
    (cpSlPoint {f} {sl} {sa=(ImSliceCofree f sl)})
    (imSlCofreeTermCoalg fm {sl})

-- `imSlSubtrees` is the morphism component of the right adjoint of
-- the slice cofree-comonad adjunction.
public export
imSlSubtrees : {c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  {sl : SliceObj c} -> SliceCoalg {a=c} f (ImSliceCofree {c} f sl)
imSlSubtrees {c} {f} fm {sl} =
  sliceComp
    (cpSlTerm {f} {sl} {sa=(ImSliceCofree f sl)})
    (imSlCofreeTermCoalg fm {sl})

-- `Trace` is a universal morphism of the cofree comonad.  Specifically, it is
-- the left adjunct:  given an object `sl : SliceObj c` and a coalgebra
-- `sa : SliceObj c`/`coalg : SSCoalg {c} f sa`, the left adjunct takes a
-- slice morphism `label : SliceMorphism {a=c} sa sl` and returns a
-- coalgebra morphism `SliceSigmaTrace coalg label :
-- SliceMorphism {a=c} sa (SliceSigmaCM f sl)`.
imSlTrace : {0 c : Type} -> {f : SliceEndofunctor c} ->
  {0 sa, sl : SliceObj c} ->
  SliceCoalg f sa -> SliceMorphism sa sl ->
  SliceMorphism sa (ImSliceCofree f sl)
imSlTrace {c} {f} {sa} {sl} = flip $ inSlCF {f} {sl} {sa}

-- The unit of the cofree comonad adjunction -- a natural transformation
-- between endofunctors on the category of F-coalgebras, from the identity
-- endofunctor to the cofree comonad.
imSlUnit : {c : Type} -> {f : SliceEndofunctor c} ->
  {sa : SliceObj c} -> SliceCoalg f sa -> SliceCoalg (ImSliceCofree f) sa
imSlUnit {c} {f} {sa} coalg = imSlTrace {f} {sa} {sl=sa} coalg (sliceId sa)

-- The right adjunct of the cofree comonad, given an object
-- `sl : SliceObj c` and a coalgebra `sa : SliceObj c`/`coalg : SSCoalg f sa`,
-- takes a coalgebra morphism to the cofree coalgebra `SliceSigmaCM f sl` from
-- `sa`, i.e. a morphism of type `SliceMorphism {a=c} sa (SliceSigmaCM f sl)`,
-- and returns a slice morphism `label : SliceMorphism {a=c} sa sl`.
--
-- The implementation does not use the morphism component of the coalgebra,
-- so we omit it from the signature.  The reason for this is that this is the
-- right adjunct of a free-forgetful adjunction, and the only use of the
-- input to the right adjunct in the formula that expresses the right adjunct in
-- terms of the counit (`imSlLabel`, in this case) is to apply the left adjoint
-- to it, and the left adjoint just forgets the morphism component.
public export
imSlRAdj : {c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  {sa, sl : SliceObj c} ->
  SliceMorphism sa (ImSliceCofree f sl) -> SliceMorphism sa sl
imSlRAdj {c} {f} fm {sa} {sl} = sliceComp $ imSlLabel fm sl

-- `imSlJoin` is the multiplication of the (impredicative) slice cofree-comonad
-- adjunction.  That means it is also the multiplication of the monad
-- arising from the adjunction; as such it is also sometimes called "join".
--
-- The multiplication comes from whiskering the counit between the adjuncts.
imSlJoin : {c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceNatTrans (ImSliceCofree f . ImSliceCofree f) (ImSliceCofree f)
imSlJoin {f} fm sa = imSlLabel {f} fm (ImSliceCofree f sa)

-- `imSlDup` is the comultiplication of the (impredicative) slice cofree-comonad
-- adjunction.  That means it is also the comultiplication of the comonad
-- arising from the adjunction; as such it is also sometimes called "duplicate".
--
-- The comultiplication comes from whiskering the unit between the adjuncts.
public export
imSlDup : {c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceNatTrans (ImSliceCofree f) (ImSliceCofree f . ImSliceCofree f)
imSlDup {f} fm sa =
  imSlUnit {f} {sa=(ImSliceCofree f sa)} (imSlSubtrees {f} {sl=sa} fm)
