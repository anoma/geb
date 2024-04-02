module LanguageDef.SlicePolyCat

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.PolyCat
import public LanguageDef.InternalCat

-------------------------------------------------
-------------------------------------------------
---- Inductive dependent polynomial functors ----
-------------------------------------------------
-------------------------------------------------

---------------------
---------------------
---- Base change ----
---------------------
---------------------

-- This definition of `BaseChangeF` is the same as the one in `IdrisCategories`.
-- I'm duplicating it here just to make it explicit in the same module as the
-- adjunctions on either side of it.
%hide Library.IdrisCategories.BaseChangeF
export
BaseChangeF : {c, d : Type} -> (d -> c) -> SliceFunctor c d
BaseChangeF {c} {d} f slc = slc . f

-- Because base change is in the middle of an adjoint triple between
-- dependent sum and dependent product, it can introduced and eliminated
-- from either side, by the adjuncts defined below with `Sigma` and `Pi`.

export
bcMap : {0 c, d : Type} -> {f : d -> c} -> SliceFMap (BaseChangeF {c} {d} f)
bcMap {c} {d} {f} sa sb m ec = m (f ec)

-- This version of `BaseChangeF` uses a slice object rather than a morphism
-- between base objects, like the dependent-type-style definitions of
-- `SliceFibSigmaF` and `SlicePiF` below.
--
-- It could be viewed as pairing up each type of a type family with a type
-- family dependent upon _that_ type.
export
SliceBCF : {c : Type} -> (sl : SliceObj c) -> SliceFunctor c (Sigma {a=c} sl)
SliceBCF {c} sl = BaseChangeF {c} {d=(Sigma {a=c} sl)} DPair.fst

export
sbcMap : {0 c : Type} -> {sl : SliceObj c} -> SliceFMap (SliceBCF {c} sl)
sbcMap {c} {sl} sa sb = bcMap {c} {d=(Sigma {a=c} sl)} {f=DPair.fst} sa sb

--------------------------------
----- Base change as W-type ----
--------------------------------

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
export
SliceSigmaF : {c : Type} ->
  (sl : SliceObj c) -> SliceFunctor (Sigma {a=c} sl) c
SliceSigmaF {c} sl sls ec =
  -- An explicit way of spelling this out would be:
  --  (esc : sl ec ** sls $ (ec ** esc))
  Sigma {a=(sl ec)} (BaseChangeF (MkDPair ec) sls)

export
ssMap : {c : Type} -> {0 sl : SliceObj c} -> SliceFMap (SliceSigmaF {c} sl)
ssMap {c} {sl} slsa slsb mab ec esla =
  (fst esla ** mab (ec ** fst esla) $ snd esla)

-- This is the category-theory-style version of `SliceFibSigmaF`, based on
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
export
SliceFibSigmaF : {c, d : Type} -> (0 f : c -> d) -> SliceFunctor c d
SliceFibSigmaF {c} {d} f =
  -- An explicit way of spelling this out would be:
  -- \sc : SliceObj c, ed : d => (ep : PreImage {a=c} {b=d} f ed ** sc $ fst0 ep)
  SliceSigmaF {c=d} (\ed => PreImage {a=c} {b=d} f ed)
  . BaseChangeF
      {c}
      {d=(Sigma {a=d} $ \ed => PreImage {a=c} {b=d} f ed)}
      (\ed => fst0 $ snd ed)

export
sfsMap : {c, d : Type} -> {0 f : c -> d} ->
  SliceFMap (SliceFibSigmaF {c} {d} f)
sfsMap {c} {d} {f} sca scb =
  ssMap {c=d} {sl=(\ed => PreImage {a=c} {b=d} f ed)}
    (\edc => sca $ fst0 $ snd edc)
    (\edc => scb $ fst0 $ snd edc)
  . bcMap
    {c}
    {d=(Sigma {a=d} $ \ed => PreImage {a=c} {b=d} f ed)}
    {f=(\ed => fst0 $ snd ed)}
    sca
    scb

--------------------------
----- Sigma as W-type ----
--------------------------

0 SFSasWTF : {c, d : Type} -> (f : c -> d) -> WTypeFunc c d
SFSasWTF {c} {d} f = MkWTF {dom=c} {cod=d} c c id id f

sfsToWTF : {c, d : Type} -> (0 f : c -> d) ->
  SliceNatTrans (SliceFibSigmaF {c} {d} f) (InterpWTF $ SFSasWTF f)
sfsToWTF {c} {d} f sc ed esc =
  (fst esc ** \ec' => replace {p=sc} (sym $ snd0 ec') $ snd esc)

sfsFromWTF : {c, d : Type} -> (0 f : c -> d) ->
  SliceNatTrans (InterpWTF $ SFSasWTF f) (SliceFibSigmaF {c} {d} f)
sfsFromWTF {c} {d} f sc ed (Element0 ec eq ** scd) =
  replace {p=(SliceFibSigmaF f sc)} eq
  $ (Element0 ec Refl ** scd $ Element0 ec Refl)

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

-- This is the right adjunct of the dependent-sum/base-change adjunction.
--
-- It constitutes the destructor for `SliceSigmaF f sc`.  As an adjunction,
-- it is parametrically polymorphic:  rather than receiving a witness to a
-- given `ec : c` being in the image of `f` applied to a given slice over
-- `c`, it passes in a handler for _any_ such witness.
export
ssElim : {0 c : Type} -> {0 sl : SliceObj c} ->
  {0 sa : SliceObj (Sigma sl)} -> {sb : SliceObj c} ->
  SliceMorphism {a=(Sigma sl)} sa (SliceBCF sl sb) ->
  SliceMorphism {a=c} (SliceSigmaF {c} sl sa) sb
ssElim {c} {sl} {sa} {sb} m ec esa = m (ec ** fst esa) $ snd esa

-- This is the left adjunct of the dependent-sum/base-change adjunction.
export
ssLAdj : {0 c : Type} -> {sl : SliceObj c} ->
  {0 sa : SliceObj (Sigma sl)} -> {sb : SliceObj c} ->
  SliceMorphism {a=c} (SliceSigmaF {c} sl sa) sb ->
  SliceMorphism {a=(Sigma sl)} sa (SliceBCF sl sb)
ssLAdj {c} {sl} {sa} {sb} m ec esa =
  m (fst ec) (snd ec ** replace {p=sa} dpEqPat esa)

-- The monad of the dependent-sum/base-change adjunction.
export
SSMonad : {c : Type} -> (sl : SliceObj c) -> SliceEndofunctor (Sigma sl)
SSMonad {c} sl = SliceBCF sl . SliceSigmaF {c} sl

export
ssMonadMap : {c : Type} -> (sl : SliceObj c) -> SliceFMap (SSMonad {c} sl)
ssMonadMap {c} sl x y =
  sbcMap (SliceSigmaF sl x) (SliceSigmaF sl y) . ssMap {c} {sl} x y

-- The comonad of the dependent-sum/base-change adjunction.
export
SSComonad : {c : Type} -> (sl : SliceObj c) -> SliceEndofunctor c
SSComonad {c} sl = SliceSigmaF {c} sl . SliceBCF sl

export
ssComonadMap : {c : Type} -> (sl : SliceObj c) -> SliceFMap (SSComonad {c} sl)
ssComonadMap {c} sl x y =
  ssMap {c} {sl} (SliceBCF sl x) (SliceBCF sl y) . sbcMap {c} {sl} x y

-- Rather than making the constructor `SS` explicit, we export an
-- alias for it viewed as a natural transformation.
--
-- This is the unit (AKA "pure" or "return") of the dependent-sum/base-change
-- adjunction.
export
sSin : {0 c : Type} -> {0 sl : SliceObj c} ->
  SliceNatTrans {x=(Sigma sl)} {y=(Sigma sl)}
    (SliceIdF $ Sigma sl)
    (SSMonad {c} sl)
sSin {c} {sl} sc ec esc = (snd ec ** replace {p=sc} dpEqPat esc)

-- The counit (AKA "erase" or "extract") of the dependent-sum/base-change
-- adjunction.
export
sSout : {0 c : Type} -> {0 sl : SliceObj c} ->
  SliceNatTrans {x=c} {y=c} (SSComonad {c} sl) (SliceIdF c)
sSout {c} {sl} sc ec esc = snd esc

-- This is the multiplication (AKA "join") of the dependent-sum/base-change
-- adjunction.
--
-- The multiplication comes from whiskering the counit between the adjuncts.
export
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
export
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

export
SSAlg : {c : Type} -> (0 f : c -> c) -> (sc : SliceObj c) -> Type
SSAlg {c} {f} = SliceAlg {a=c} (SliceFibSigmaF {c} {d=c} f)

export
SSVoidAlg : {c : Type} -> (0 f : c -> c) -> SSAlg {c} f (const Void)
SSVoidAlg {c} f ec evc = void $ snd evc

export
SSCoalg : {c : Type} -> (0 f : c -> c) -> (sc : SliceObj c) -> Type
SSCoalg {c} {f} = SliceCoalg {a=c} (SliceFibSigmaF {c} {d=c} f)

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
export
SlicePiF : {c : Type} -> (sl : SliceObj c) -> SliceFunctor (Sigma {a=c} sl) c
SlicePiF {c} sl sls ec =
  -- An explicit way of spelling this out would be:
  --  (esc : sl ec) -> sls $ (ec ** esc)
  Pi {a=(sl ec)} (BaseChangeF (MkDPair ec) sls)

export
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
export
SliceFibPiF : {c, d : Type} -> (0 f : c -> d) -> SliceFunctor c d
SliceFibPiF {c} {d} f =
  -- An explicit way of spelling this out would be:
  --  (ep : PreImage {a=c} {b=d} f ed) -> sc $ fst0 ep
  SlicePiF {c=d} (\ed => PreImage {a=c} {b=d} f ed)
  . BaseChangeF
      {c}
      {d=(Sigma {a=d} $ \ed => PreImage {a=c} {b=d} f ed)}
      (\ed => fst0 $ snd ed)

export
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

0 SPSasWTF : {c, d : Type} -> (f : c -> d) -> WTypeFunc c d
SPSasWTF {c} {d} f = MkWTF {dom=c} {cod=d} d c id f id

spsToWTF : {c, d : Type} -> (0 f : c -> d) ->
  SliceNatTrans (SliceFibPiF {c} {d} f) (InterpWTF $ SPSasWTF f)
spsToWTF {c} {d} f sc ed pisc = (Element0 ed Refl ** pisc)

spsFromWTF : {c, d : Type} -> (0 f : c -> d) ->
  SliceNatTrans (InterpWTF $ SPSasWTF f) (SliceFibPiF {c} {d} f)
spsFromWTF {c} {d} f sc ed (Element0 ec eq ** scd) =
  replace {p=(SliceFibPiF f sc)} eq scd

0 SPasWTF : {c : Type} -> (sl : SliceObj c) -> WTypeFunc (Sigma sl) c
SPasWTF {c} sl = SPSasWTF {c=(Sigma sl)} {d=c} DPair.fst

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

-- This is the left adjunct of the dependent-product/base-change adjunction.
--
-- It constitutes the constructor for `SlicePiF f sc`.  As an adjunction,
-- it is parametrically polymorphic:  rather than receiving a witness to a
-- given `ec : c` being in the image of `f` applied to a given slice over
-- `c`, it passes in a handler for _any_ such witness.
export
spIntro : {0 c : Type} -> {0 sl : SliceObj c} ->
  {0 sa : SliceObj c} -> {sb : SliceObj (Sigma sl)} ->
  SliceMorphism {a=(Sigma sl)} (SliceBCF sl sa) sb ->
  SliceMorphism {a=c} sa (SlicePiF sl sb)
spIntro {c} {sl} {sa} {sb} m ec esa esl = m (ec ** esl) esa

-- This is the right adjunct of the dependent-product/base-change adjunction.
export
spRAdj : {0 c : Type} -> {0 sl : SliceObj c} ->
  {0 sa : SliceObj c} -> {sb : SliceObj (Sigma sl)} ->
  SliceMorphism {a=c} sa (SlicePiF sl sb) ->
  SliceMorphism {a=(Sigma sl)} (SliceBCF sl sa) sb
spRAdj {c} {sl} {sa} {sb} m esl esa =
  replace {p=sb} (sym dpEqPat) $ m (fst esl) esa (snd esl)

-- The monad of the dependent-product/base-change adjunction.
export
SPMonad : {c : Type} -> (sl : SliceObj c) -> SliceEndofunctor c
SPMonad {c} sl = SlicePiF {c} sl . SliceBCF {c} sl

export
spMonadMap : {c : Type} -> (sl : SliceObj c) -> SliceFMap (SPMonad {c} sl)
spMonadMap {c} sl x y =
  spMap {c} {sl} (SliceBCF sl x) (SliceBCF sl y) . sbcMap {c} {sl} x y

-- The comonad of the dependent-product/base-change adjunction.
export
SPComonad : {c : Type} -> (sl : SliceObj c) -> SliceEndofunctor (Sigma sl)
SPComonad {c} sl = SliceBCF {c} sl . SlicePiF {c} sl

export
spComonadMap : {c : Type} -> (sl : SliceObj c) -> SliceFMap (SPComonad {c} sl)
spComonadMap {c} sl x y =
  sbcMap (SlicePiF sl x) (SlicePiF sl y) . spMap {c} {sl} x y

-- This is the unit (AKA "pure" or "return") of the
-- dependent-product/base-change adjunction.
export
spUnit : {0 c : Type} -> {0 sl : SliceObj c} ->
  SliceNatTrans {x=c} {y=c} (SliceIdF c) (SPMonad {c} sl)
spUnit {c} {sl} sc ec esc esl = esc

-- This is the counit (AKA "erase" or "extract") of the
-- dependent-product/base-change adjunction.
export
spCounit : {0 c : Type} -> {0 sl : SliceObj c} ->
  SliceNatTrans {x=(Sigma sl)} {y=(Sigma sl)}
    (SPComonad {c} sl)
    (SliceIdF $ Sigma sl)
spCounit {c} {sl} sc esl pisc = replace {p=sc} (sym dpEqPat) $ pisc $ snd esl

-- This is the multiplication (AKA "join") of the dependent-product/base-change
-- adjunction.
--
-- The multiplication comes from whiskering the counit between the adjuncts.
export
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
export
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

------------------------------------------------
------------------------------------------------
---- Sigma/base-change/pi triple adjunction ----
------------------------------------------------
------------------------------------------------

-- The adjunctions between dependent sum and base change (Sigma) and
-- base change and dependent product (Pi) can be composed.

-- This is the left adjoint of the dependent-sum/dependent-product adjunction,
-- in category-theoretic style.
export
SliceFibSigmaPiFL : {c, d, e : Type} -> (d -> e) -> (d -> c) ->
  SliceFunctor c e
SliceFibSigmaPiFL {c} {d} {e} g f =
  SliceFibSigmaF {c=d} {d=e} g . BaseChangeF {c} {d} f

-- This is the left adjoint of the dependent-sum/dependent-product adjunction,
-- in dependent-type style.
export
SliceSigmaPiFL : {c : Type} -> {e : SliceObj c} ->
  (d : SliceObj (Sigma {a=c} e)) -> SliceFunctor c (Sigma {a=c} e)
SliceSigmaPiFL {c} {e} d =
  SliceSigmaF {c=(Sigma {a=c} e)} d
  . SliceBCF {c=(Sigma {a=c} e)} d . SliceBCF {c} e

--------------------------------
--------------------------------
---- Initial slice algebras ----
--------------------------------
--------------------------------

-- The impredicative initial algebra of an endofunctor on `SliceObj c`.
export
ImSliceMu : {c : Type} -> SliceEndofunctor c -> SliceObj c
ImSliceMu {c} f ec =
  SliceNatTrans {x=c} {y=Unit} (\sc, () => SliceAlg f sc) (\sc, () => sc ec)

export
imSlCata : {0 c : Type} -> {0 f : SliceEndofunctor c} ->
  {sa : SliceObj c} ->
  SliceAlg f sa -> SliceMorphism {a=c} (ImSliceMu {c} f) sa
imSlCata {c} {f} {sa} alg ec mu = mu sa () alg

export
slMuFromIm : {c : Type} -> (f : SliceEndofunctor c) ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceMorphism (ImSliceMu f) (SliceMu f)
slMuFromIm {c} f fm ec mu =
  InSlFc {a=c} {f} {ea=ec} $ mu (f $ SliceMu f) ()
  $ fm (f $ SliceMu f) (SliceMu f) $ \ec => InSlFc {ea=ec}

export
slMuToIm : {c : Type} -> (f : SliceEndofunctor c) ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceCata f ->
  SliceMorphism (SliceMu f) (ImSliceMu f)
slMuToIm {c} f fm fcata ec (InSlF {f} {sa=(const Void)} ec $ InSlV v) = void v
slMuToIm {c} f fm fcata ec (InSlF {f} {sa=(const Void)} ec $ InSlC t) =
  \sa, (), alg => sliceComp alg (fm (SliceMu f) sa (fcata sa alg)) ec t

export
imSlInitAlg : {c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceCata f ->
  SliceAlg f (ImSliceMu f)
imSlInitAlg {f} fm fcata =
  sliceComp (slMuToIm f fm fcata) $ sliceComp (\ec => InSlFc {ea=ec})
  $ fm (ImSliceMu f) (SliceMu f) (slMuFromIm f fm)

export
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

export
SSFMAlg : {c : Type} -> (0 f : c -> c) -> (sc : SliceObj c) -> Type
SSFMAlg {c} f = SliceAlg {a=c} (SliceSigmaFM {c} f)

export
SSFMCoalg : {c : Type} -> (0 f : c -> c) -> (sc : SliceObj c) -> Type
SSFMCoalg {c} f = SliceCoalg {a=c} (SliceSigmaFM {c} f)

-- `SSin` is an isomorphism (by Lambek's theorem); this is its inverse.
export
SSout : {0 c : Type} -> {0 f : c -> c} -> {0 sc : SliceObj c} ->
  SPICoalg {c} f sc (SliceSigmaFM {c} f sc)
SSout {c} {f} {sc} ec (SSin ec esp) = esp

-- The (morphism component of the) free `SliceSigmaF`-algebra of
-- `SliceSigmaFM f sc`.
export
SScom : {c : Type} -> {f : c -> c} -> {0 sc : SliceObj c} ->
  SSAlg {c} f (SliceSigmaFM {c} f sc)
SScom {c} {f} {sc} ec =
  SSin {c} {f} {sc} ec
  . inSlPc {f=(SliceFibSigmaF f)} {sl=sc} {sa=(SliceSigmaFM f sc)} ec

-- The unit of the free-monad adjunction -- a natural transformation of
-- endofunctors on `SliceObj a`, from the identity endofunctor to
-- `SliceSigmaFM f`.
export
SSvar : {c : Type} -> {f : c -> c} ->
  SliceNatTrans (SliceIdF c) (SliceSigmaFM {c} f)
SSvar {c} {f} sc ec t =
  SSin {c} {f} {sc} ec
  $ inSlPv {f=(SliceFibSigmaF f)} {sl=sc} {sa=(SliceSigmaFM f sc)} ec t

-- The counit of the free-monad adjunction -- a natural transformation of
-- endofunctors on algebras of `SliceSigmaF f`, from `SSFMAlg` to the
-- identity endofunctor.
export
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
export
SliceSigmaEval : {0 c : Type} -> {f : c -> c} -> (sb : SliceObj c) ->
  (alg : SSAlg f sb) ->
  SliceMorphism {a=(SliceObj c)}
    (flip (SliceMorphism {a=c}) sb)
    (flip (SliceMorphism {a=c}) sb . SliceSigmaFM {c} f)
SliceSigmaEval {c} {f} sb alg sa subst ec (SSin ec (Left v)) =
  subst ec v
SliceSigmaEval {c} {f} sb alg sa subst ec (SSin ec (Right t)) =
  alg ec $ case t of
    (Element0 ec' eqc ** fmec) =>
      (Element0 ec' eqc ** SliceSigmaEval sb alg sa subst ec' fmec)

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
export
SliceSigmaFMLAdj : {c : Type} -> {f : c -> c} -> (sa, sb : SliceObj c) ->
  SliceMorphism {a=c} (SliceSigmaFM {c} f sa) sb ->
  SliceMorphism {a=c} sa sb
SliceSigmaFMLAdj {c} {f} sa sb eval ec = eval ec . SSvar {c} {f} sa ec

-- We show that the initial algebra of `SliceSigmaF f` is the initial object
-- of `SliceObj a`.
export
SSMuInitial : {c : Type} -> (f : c -> c) ->
  SliceMorphism {a=c} (SliceSigmaFM {c} f $ const Void) (const Void)
SSMuInitial {c} f =
  SliceSigmaEval {c} {f} (const Void) (SSVoidAlg {c} f) (const Void) (\_ => id)

export
ssfmMap : {c : Type} -> {f : c -> c} -> SliceFMap (SliceSigmaFM {c} f)
ssfmMap {c} {f} sa sb m =
  SliceSigmaEval {c} {f} (SliceSigmaFM {c} f sb) SScom sa
    (sliceComp (SSvar sb) m)

-- The multiplication of the free-monad adjunction, often called "join" --
-- a natural transformation of endofunctors on `SliceObj a`, from
-- `SliceSigmaFM f . SliceSigmaFM f` to `SliceSigmaFM f`.
--
-- The multiplication comes from whiskering the counit between the adjuncts.
export
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
export
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
export
data ImSliceNu : {0 c : Type} -> SliceEndofunctor c -> SliceObj c where
  ImSlN : {0 c : Type} -> {0 f : SliceEndofunctor c} ->
    {0 sa : SliceObj c} -> SliceCoalg f sa -> (ec : c) -> sa ec ->
    ImSliceNu {c} f ec

export
imSlAna : {0 c : Type} -> {0 f : SliceEndofunctor c} ->
  {0 sa : SliceObj c} ->
  SliceCoalg f sa -> SliceMorphism {a=c} sa (ImSliceNu {c} f)
imSlAna = ImSlN

export
imSlTermCoalg : {0 c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceCoalg f (ImSliceNu f)
imSlTermCoalg {f} fm ec (ImSlN {c} {f} {sa} coalg ec esa) =
  fm sa (ImSliceNu {c} f) (imSlAna {c} {f} {sa} coalg) ec (coalg ec esa)

-- The inverse of `imSlTermCoalg`, which we know by Lambek's theorem should
-- exist.
export
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
export
ImSliceCofree : {0 c : Type} -> SliceEndofunctor c -> SliceEndofunctor c
ImSliceCofree {c} f sa = ImSliceNu (SlCopointedF f sa)

export
ImSlCMAlg : {c : Type} -> (f : SliceEndofunctor c) -> SliceObj c -> Type
ImSlCMAlg {c} f = SliceAlg {a=c} (ImSliceCofree {c} f)

export
ImSlCMCoalg : {c : Type} -> (f : SliceEndofunctor c) -> SliceObj c -> Type
ImSlCMCoalg {c} f = SliceCoalg {a=c} (ImSliceCofree {c} f)

public export
inSlCF : {0 c : Type} -> {f : SliceEndofunctor c} -> {0 sl, sa : SliceObj c} ->
  SliceMorphism {a=c} sa sl -> SliceCoalg f sa ->
  SliceMorphism {a=c} sa (ImSliceCofree f sl)
inSlCF label coalg = ImSlN {f=(SlCopointedF f sl)} $ inSlCP {f} label coalg

export
imSlCofreeTermCoalg : {0 c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  {sl : SliceObj c} -> SlCopointedCoalg {c} f sl (ImSliceCofree {c} f sl)
imSlCofreeTermCoalg fm {sl} =
  imSlTermCoalg {f=(SlCopointedF f sl)} (mapSlCP {f} fm sl)

export
imSlCofreeTermCoalgInv : {0 c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  {sl : SliceObj c} -> SlCopointedAlg {c} f sl (ImSliceCofree {c} f sl)
imSlCofreeTermCoalgInv fm {sl} =
  imSlTermCoalgInv {f=(SlCopointedF f sl)} (mapSlCP {f} fm sl)

-- `imSlLabel` is the counit of the (impredicative) slice cofree-comonad
-- adjunction.  That means it is also the counit of the comonad arising from
-- the adjunction; as such it is also sometimes called "erase" or "extract".
export
imSlLabel : {c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceNatTrans {x=c} {y=c} (ImSliceCofree f) (SliceIdF c)
imSlLabel {c} {f} fm sl =
  sliceComp
    (cpSlPoint {f} {sl} {sa=(ImSliceCofree f sl)})
    (imSlCofreeTermCoalg fm {sl})

-- `imSlSubtrees` is the morphism component of the right adjoint of
-- the slice cofree-comonad adjunction.
export
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
export
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
export
imSlDup : {c : Type} -> {f : SliceEndofunctor c} ->
  ((0 x, y : SliceObj c) -> SliceMorphism x y -> SliceMorphism (f x) (f y)) ->
  SliceNatTrans (ImSliceCofree f) (ImSliceCofree f . ImSliceCofree f)
imSlDup {f} fm sa =
  imSlUnit {f} {sa=(ImSliceCofree f sa)} (imSlSubtrees {f} {sl=sa} fm)

----------------------------------------
----------------------------------------
---- Covariant slice representables ----
----------------------------------------
----------------------------------------

--------------------
---- Definition ----
--------------------

-- The slice functor from `c` to `Type` which is covariantly represented
-- by the given `SliceObj c`.  (`Type` is isomorphic to `SliceObj Unit`.)
export
SliceCovarRepF : {c : Type} -> (sc : SliceObj c) -> SliceFunctor c Unit
SliceCovarRepF sa sb () = SliceMorphism sa sb

--------------------------------------------
----- Covariant representable as W-type ----
--------------------------------------------

0 SCovRasWTF : {c : Type} -> (sc : SliceObj c) -> WTypeFunc c Unit
SCovRasWTF {c} sc =
  MkWTF {dom=c} {cod=Unit}
    Unit
    (Sigma {a=c} sc)
    fst
    (const ())
    (id {a=Unit})

scovrToWTF : {c, d : Type} -> (sa : SliceObj c) ->
  SliceNatTrans (SliceCovarRepF {c} sa) (InterpWTF $ SCovRasWTF sa)
scovrToWTF {c} {d} sa sb () mfsa =
  (Element0 () Refl ** \(Element0 (ec ** sea) eq) => mfsa ec sea)

scovrFromWTF : {c, d : Type} -> (sa : SliceObj c) ->
  SliceNatTrans (InterpWTF $ SCovRasWTF sa) (SliceCovarRepF {c} sa)
scovrFromWTF {c} {d} sa sb () (Element0 () eq ** sbd) =
  \ec, sea => sbd $ Element0 (ec ** sea) Refl

---------------------------
---------------------------
---- Dependent product ----
---------------------------
---------------------------

---------------------------------------------
---- Dependent product from slice object ----
---------------------------------------------

-- The slice functor from `c` to `d` which consists of a product of `d`
-- representable functors from `SliceObj c`.  Products of representables
-- are themselves representable (products of covariant representables are
-- represented by sums, and products of contravariant representables are
-- represented by products).
export
SliceDepPiF : {c : Type} -> (d -> c -> Type) -> SliceFunctor c d
SliceDepPiF sdc sc ed = SliceCovarRepF (sdc ed) {c} sc ()

--------------------------------------
----- Dependent product as W-type ----
--------------------------------------

0 SDPasWTF : {c, d : Type} -> (p : d -> c -> Type) -> WTypeFunc c d
SDPasWTF {c} {d} p =
  MkWTF {dom=c} {cod=d}
    d
    (Sigma {a=(d, c)} (uncurry p))
    (snd . fst)
    (fst . fst)
    (id {a=d})

spdToWTF : {c, d : Type} -> (0 p : d -> c -> Type)->
  SliceNatTrans (SliceDepPiF {c} {d} p) (InterpWTF $ SDPasWTF p)
spdToWTF {c} {d} p sc ed mpsc =
  (Element0 ed Refl **
   \(Element0 ((ed', ec') ** pdc) eq) =>
    mpsc ec' $ replace {p=(flip p ec')} eq pdc)

spdFromWTF : {c, d : Type} -> (0 p : d -> c -> Type)->
  SliceNatTrans (InterpWTF $ SDPasWTF p) (SliceDepPiF {c} {d} p)
spdFromWTF {c} {d} p sc ed (Element0 ed' eq ** mpsc) =
  \ec, pdc => mpsc (Element0 ((ed, ec) ** pdc) $ sym eq)

-----------------------------
-----------------------------
---- Utility definitions ----
-----------------------------
-----------------------------

public export
MLArena : Type
MLArena = IntArena Type

-----------------------------------------------------------------------
-----------------------------------------------------------------------
---- Slice categories of polynomial functors (in categorial style) ----
-----------------------------------------------------------------------
-----------------------------------------------------------------------

CPFSliceObj : MLPolyCatObj -> Type
CPFSliceObj p = (q : MLPolyCatObj ** PolyNatTrans q p)

public export
0 CPFNatTransEq :
  (p, q : MLPolyCatObj) -> (alpha, beta : PolyNatTrans p q) -> Type
CPFNatTransEq (ppos ** pdir) (qpos ** qdir)
  (aonpos ** aondir) (bonpos ** bondir) =
    Exists0
      (ExtEq {a=ppos} {b=qpos} aonpos bonpos)
      $ \onposeq =>
        (i : ppos) -> (d : qdir (aonpos i)) ->
        bondir i (replace {p=qdir} (onposeq i) d) = aondir i d

CPFSliceMorph : (p : MLPolyCatObj) -> CPFSliceObj p -> CPFSliceObj p -> Type
CPFSliceMorph p (q ** qp) (r ** rp) =
  Subset0 (PolyNatTrans q r) (\qr => CPFNatTransEq q p qp (pntVCatComp rp qr))

-- In any slice category, we can infer a slice morphism from a slice object
-- and a morphism from any object of the base category to the domain of the
-- slice object, by taking the codomain of the slice morphism to be the given
-- slice object, the domain of the domain of the slice morphism to be the
-- given object of the base category, and the projection of the domain of the
-- slice morphism to be composition of the given morphism followed by the
-- projection of the codomain of the slice morphism.  All slice morphisms
-- take this form, so that can function as an alternate definition of slice
-- morphism, which does not require any explicit proof content (of
-- commutativity).
PFSliceMorph : {0 p : PolyFunc} -> CPFSliceObj p -> Type
PFSliceMorph {p} (ctot ** alpha) = (dtot : PolyFunc ** PolyNatTrans dtot ctot)

PFSliceMorphDom : {0 p : PolyFunc} -> {cod : CPFSliceObj p} ->
  PFSliceMorph {p} cod -> CPFSliceObj p
PFSliceMorphDom {p} {cod=(ctot ** alpha)} (dtot ** beta) =
  (dtot ** pntVCatComp alpha beta)

public export
data PFSliceMorphDep : {0 p : PolyFunc} -> CPFSliceObj p -> CPFSliceObj p ->
    Type where
  PSMD : {0 p : PolyFunc} -> {0 dom, cod : CPFSliceObj p} ->
    (mor : PFSliceMorph {p} cod) ->
    PFSliceMorphDep {p} (PFSliceMorphDom {p} {cod} mor) cod

PFSliceMorphToC : {0 p : PolyFunc} -> {cod : CPFSliceObj p} ->
  (mor : PFSliceMorph {p} cod) ->
  CPFSliceMorph p (PFSliceMorphDom {p} {cod} mor) cod
PFSliceMorphToC {p=(ppos ** pdir)} {cod=((ctot ** cproj) ** (conpos ** condir))}
  ((dtot ** dproj) ** (donpos ** dondir)) =
    Element0
      (donpos ** dondir)
      (Evidence0
        (\_ => Refl)
        (\_, _ => Refl))

PFSliceMorphFromC : {0 p : PolyFunc} -> {dom, cod : CPFSliceObj p} ->
  CPFSliceMorph p dom cod -> PFSliceMorph {p} cod
PFSliceMorphFromC {p=(ppos ** pdir)} {dom=(dtot ** dproj)} {cod=(ctot ** cproj)}
  (Element0 alpha nteq) =
    (dtot ** alpha)

PFSliceMorphFromCDomObjEq : {0 p : PolyFunc} -> {dom, cod : CPFSliceObj p} ->
  (mor : CPFSliceMorph p dom cod) ->
  fst (PFSliceMorphDom {p} {cod} (PFSliceMorphFromC {p} {dom} {cod} mor)) =
  fst dom
PFSliceMorphFromCDomObjEq {p=(ppos ** pdir)}
  {dom=(dtot ** dproj)} {cod=(ctot ** cproj)} (Element0 alpha nteq) =
    Refl

0 PFSliceMorphFromCDomMorEq : {0 p : PolyFunc} ->
  {dtot, ctot : PolyFunc} ->
  {dproj : PolyNatTrans dtot p} ->
  {cproj : PolyNatTrans ctot p} ->
  (mor : CPFSliceMorph p (dtot ** dproj) (ctot ** cproj)) ->
  CPFNatTransEq
    dtot p
    dproj
    (replace {p=(flip PolyNatTrans p)}
      (PFSliceMorphFromCDomObjEq {p} {dom=(dtot ** dproj)} {cod=(ctot ** cproj)}
       mor)
     $ snd $ PFSliceMorphDom {p} {cod=(ctot ** cproj)}
     $ PFSliceMorphFromC {p} {dom=(dtot ** dproj)} {cod=(ctot ** cproj)} mor)
PFSliceMorphFromCDomMorEq {p=(ppos ** pdir)}
  {dtot} {dproj} {ctot} {cproj} (Element0 alpha nteq) =
    nteq

----------------------------------------------------------------------
----------------------------------------------------------------------
---- Slice categories of Dirichlet functors (in categorial style) ----
----------------------------------------------------------------------
----------------------------------------------------------------------

CDFSliceObj : MLDirichCatObj -> Type
CDFSliceObj p = (q : MLDirichCatObj ** DirichNatTrans q p)

0 CDFNatTransEq :
  (p, q : MLDirichCatObj) -> (alpha, beta : DirichNatTrans p q) -> Type
CDFNatTransEq (ppos ** pdir) (qpos ** qdir)
  (aonpos ** aondir) (bonpos ** bondir) =
    Exists0
      (ExtEq {a=ppos} {b=qpos} aonpos bonpos)
      $ \onposeq =>
        (i : ppos) -> (d : pdir i) ->
        bondir i d = replace {p=qdir} (onposeq i) (aondir i d)

CDFSliceMorph : (p : MLDirichCatObj) -> CDFSliceObj p -> CDFSliceObj p -> Type
CDFSliceMorph p (q ** qp) (r ** rp) =
  Subset0 (DirichNatTrans q r) (\qr => CDFNatTransEq q p qp (dntVCatComp rp qr))

-- A convenient (free of proof content) form of `CDFSliceMorph`; see
-- the comment to `PFSliceMorph` above.
DFSliceMorph : {0 p : PolyFunc} -> CDFSliceObj p -> Type
DFSliceMorph {p} (ctot ** alpha) = (dtot : PolyFunc ** DirichNatTrans dtot ctot)

DFSliceMorphDom : {0 p : PolyFunc} -> {cod : CDFSliceObj p} ->
  DFSliceMorph {p} cod -> CDFSliceObj p
DFSliceMorphDom {p} {cod=(ctot ** alpha)} (dtot ** beta) =
  (dtot ** dntVCatComp alpha beta)

public export
data DFSliceMorphDep : {0 p : PolyFunc} -> CDFSliceObj p -> CDFSliceObj p ->
    Type where
  DSMD : {0 p : PolyFunc} -> {0 dom, cod : CDFSliceObj p} ->
    (mor : DFSliceMorph {p} cod) ->
    DFSliceMorphDep {p} (DFSliceMorphDom {p} {cod} mor) cod

DFSliceMorphToC : {0 p : PolyFunc} -> {cod : CDFSliceObj p} ->
  (mor : DFSliceMorph {p} cod) ->
  CDFSliceMorph p (DFSliceMorphDom {p} {cod} mor) cod
DFSliceMorphToC {p=(ppos ** pdir)} {cod=((ctot ** cproj) ** (conpos ** condir))}
  ((dtot ** dproj) ** (donpos ** dondir)) =
    Element0
      (donpos ** dondir)
      (Evidence0
        (\_ => Refl)
        (\_, _ => Refl))

DFSliceMorphFromC : {0 p : PolyFunc} -> {dom, cod : CDFSliceObj p} ->
  CDFSliceMorph p dom cod -> DFSliceMorph {p} cod
DFSliceMorphFromC {p=(ppos ** pdir)} {dom=(dtot ** dproj)} {cod=(ctot ** cproj)}
  (Element0 alpha nteq) =
    (dtot ** alpha)

DFSliceMorphFromCDomObjEq : {0 p : PolyFunc} -> {dom, cod : CDFSliceObj p} ->
  (mor : CDFSliceMorph p dom cod) ->
  fst (DFSliceMorphDom {p} {cod} (DFSliceMorphFromC {p} {dom} {cod} mor)) =
  fst dom
DFSliceMorphFromCDomObjEq {p=(ppos ** pdir)}
  {dom=(dtot ** dproj)} {cod=(ctot ** cproj)} (Element0 alpha nteq) =
    Refl

0 DFSliceMorphFromCDomMorEq : {0 p : PolyFunc} ->
  {dtot, ctot : PolyFunc} ->
  {dproj : DirichNatTrans dtot p} ->
  {cproj : DirichNatTrans ctot p} ->
  (mor : CDFSliceMorph p (dtot ** dproj) (ctot ** cproj)) ->
  CDFNatTransEq
    dtot p
    dproj
    (replace {p=(flip DirichNatTrans p)}
      (DFSliceMorphFromCDomObjEq {p} {dom=(dtot ** dproj)} {cod=(ctot ** cproj)}
       mor)
     $ snd $ DFSliceMorphDom {p} {cod=(ctot ** cproj)}
     $ DFSliceMorphFromC {p} {dom=(dtot ** dproj)} {cod=(ctot ** cproj)} mor)
DFSliceMorphFromCDomMorEq {p=(ppos ** pdir)}
  {dtot} {dproj} {ctot} {cproj} (Element0 alpha nteq) =
    nteq

------------------------------------------------------
------------------------------------------------------
---- Slices over arenas (in dependent-type style) ----
------------------------------------------------------
------------------------------------------------------

---------------------------------
---- Slice object definition ----
---------------------------------

-- The natural transformations of both polynomial and Dirichlet functors have
-- on-positions functions from the domain to the codomain.  Thus, the
-- on-positions function of a natural transformation between either of those
-- types of objects (functors) may be viewed as a fibration of the arena
-- being sliced over.
public export
MlSlArProjOnPos : MLArena -> Type
MlSlArProjOnPos = SliceObj . pfPos

-- Thus, the positions of the slice object's domain can be viewed as
-- the sum of all the fibers.
public export
MlSlArTotPos : {ar : MLArena} -> MlSlArProjOnPos ar -> Type
MlSlArTotPos {ar} onpos = Sigma {a=(pfPos ar)} onpos

-- Consequently, the directions of the slice object's domain are a slice
-- of the sum of the fibers.
--
-- However, the on-directions part of the projection component of the slice
-- object will, in the case of Dirichlet functors, also go from the domain
-- to the object being sliced over.  Thus that too may be viewed as a fibration,
-- of pairs of the positions of the domain and the directions of the codomain,
-- where those two share the same position of the codomain.
--
-- That view only makes sense in the case of Dirichlet functors, not of
-- polynomials, because the on-directions part of the projection component of
-- an object in a polynomial-functor slice category goes in the opposite
-- direction.
public export
MlDirichSlDir : (ar : MLArena) -> MlSlArProjOnPos ar -> Type
MlDirichSlDir ar onpos = (i : pfPos ar) -> onpos i -> pfDir {p=ar} i -> Type

public export
record MlDirichSlObj (ar : MLArena) where
  constructor MDSobj
  mdsOnPos : MlSlArProjOnPos ar
  mdsDir : MlDirichSlDir ar mdsOnPos

-- In the case of polynomial functors, the directions of the slice object's
-- domain are slices of its positions only, since its on-directions function
-- can not be viewed as a fibration of them, and we therefore require an
-- explicit on-directions function (rather than making it implicit as a
-- fibration in the definition of the type of directions).
public export
MlPolySlDir : (ar : MLArena) -> MlSlArProjOnPos ar -> Type
MlPolySlDir ar onpos = (i : pfPos ar) -> onpos i -> Type

public export
MlPolySlOnDir : {ar : MLArena} ->
  (onpos : MlSlArProjOnPos ar) -> MlPolySlDir ar onpos -> Type
MlPolySlOnDir {ar} onpos dir =
  (i : pfPos ar) -> (j : onpos i) -> pfDir {p=ar} i -> dir i j

public export
record MlPolySlObj (ar : MLArena) where
  constructor MPSobj
  mpsOnPos : MlSlArProjOnPos ar
  mpsDir : MlPolySlDir ar mpsOnPos
  mpsOnDir : MlPolySlOnDir {ar} mpsOnPos mpsDir

--------------------------------------------------------------------
---- Equivalence of dependent-type and categorial-style objects ----
--------------------------------------------------------------------

public export
mlDirichSlObjTotPos : {ar : MLArena} -> MlDirichSlObj ar -> Type
mlDirichSlObjTotPos {ar} sl = MlSlArTotPos {ar} $ mdsOnPos sl

public export
mlDirichSlObjTotDir : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  mlDirichSlObjTotPos {ar} sl -> Type
mlDirichSlObjTotDir {ar} sl ij =
  Sigma {a=(pfDir {p=ar} $ fst ij)} $ mdsDir sl (fst ij) (snd ij)

public export
mlDirichSlObjTot : {ar : MLArena} -> MlDirichSlObj ar -> MLArena
mlDirichSlObjTot {ar} sl =
  (mlDirichSlObjTotPos {ar} sl ** mlDirichSlObjTotDir {ar} sl)

public export
mlDirichSlObjProjOnPos : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  mlDirichSlObjTotPos sl -> pfPos ar
mlDirichSlObjProjOnPos {ar} sl = DPair.fst

public export
mlDirichSlObjProjOnDir : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  (i : mlDirichSlObjTotPos sl) ->
  mlDirichSlObjTotDir {ar} sl i -> pfDir {p=ar} (mlDirichSlObjProjOnPos sl i)
mlDirichSlObjProjOnDir {ar} sl _ = DPair.fst

public export
mlDirichSlObjProj : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  DirichNatTrans (mlDirichSlObjTot {ar} sl) ar
mlDirichSlObjProj {ar} sl =
  (mlDirichSlObjProjOnPos {ar} sl ** mlDirichSlObjProjOnDir {ar} sl)

public export
mlDirichSlObjToC : {ar : MLArena} -> MlDirichSlObj ar -> CDFSliceObj ar
mlDirichSlObjToC {ar} sl =
  (mlDirichSlObjTot {ar} sl ** mlDirichSlObjProj {ar} sl)

public export
mlDirichSlOnPosFromC : {ar : MLArena} -> CDFSliceObj ar -> MlSlArProjOnPos ar
mlDirichSlOnPosFromC {ar} sl i = PreImage (fst $ snd sl) i

public export
mlDirichSlDirFromCBase : {ar : MLArena} -> (sl : CDFSliceObj ar) ->
  MlDirichSlDir ar (mlDirichSlOnPosFromC {ar} sl)
mlDirichSlDirFromCBase {ar} sl i j bd = snd (fst sl) (fst0 j)

public export
mlDirichSlDirFromCProp : {ar : MLArena} -> (sl : CDFSliceObj ar) ->
  (i : pfPos ar) -> (j : mlDirichSlOnPosFromC {ar} sl i) ->
  (bd : pfDir {p=ar} i) -> SliceObj (mlDirichSlDirFromCBase {ar} sl i j bd)
mlDirichSlDirFromCProp {ar} sl i j bd sld =
  snd (snd sl) (fst0 j) sld = replace {p=(pfDir {p=ar})} (sym $ snd0 j) bd

public export
mlDirichSlDirFromC : {ar : MLArena} -> (sl : CDFSliceObj ar) ->
  MlDirichSlDir ar (mlDirichSlOnPosFromC {ar} sl)
mlDirichSlDirFromC {ar} sl i j bd =
  Subset0
    (mlDirichSlDirFromCBase {ar} sl i j bd)
    (mlDirichSlDirFromCProp {ar} sl i j bd)

public export
mlDirichSlObjFromC : {ar : MLArena} -> CDFSliceObj ar -> MlDirichSlObj ar
mlDirichSlObjFromC {ar} sl =
  MDSobj (mlDirichSlOnPosFromC {ar} sl) (mlDirichSlDirFromC {ar} sl)

public export
mlPolySlObjTotPos : {ar : MLArena} -> MlPolySlObj ar -> Type
mlPolySlObjTotPos {ar} p = MlSlArTotPos {ar} $ mpsOnPos p

public export
mlPolySlObjTotDir : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  mlPolySlObjTotPos {ar} sl -> Type
mlPolySlObjTotDir {ar} sl ij = mpsDir sl (fst ij) (snd ij)

public export
mlPolySlObjTot : {ar : MLArena} -> MlPolySlObj ar -> MLArena
mlPolySlObjTot {ar} sl =
  (mlPolySlObjTotPos {ar} sl ** mlPolySlObjTotDir {ar} sl)

public export
mlPolySlObjProjOnPos : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  mlPolySlObjTotPos sl -> pfPos ar
mlPolySlObjProjOnPos {ar} sl = DPair.fst

public export
mlPolySlObjProjOnDir : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  (i : mlPolySlObjTotPos sl) ->
  pfDir {p=ar} (mlPolySlObjProjOnPos sl i) -> mlPolySlObjTotDir {ar} sl i
mlPolySlObjProjOnDir {ar} sl ij d = mpsOnDir sl (fst ij) (snd ij) d

public export
mlPolySlObjProj : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  PolyNatTrans (mlPolySlObjTot {ar} sl) ar
mlPolySlObjProj {ar} sl =
  (mlPolySlObjProjOnPos {ar} sl ** mlPolySlObjProjOnDir {ar} sl)

public export
mlPolySlObjToC : (ar : PolyFunc) -> MlPolySlObj ar -> CPFSliceObj ar
mlPolySlObjToC ar sl@(MPSobj onpos dir ondir) =
  (mlPolySlObjTot {ar} sl ** mlPolySlObjProj {ar} sl)

public export
mlPolySlOnPosFromC : {ar : MLArena} -> CPFSliceObj ar -> MlSlArProjOnPos ar
mlPolySlOnPosFromC {ar} sl i = PreImage (fst $ snd sl) i

public export
mlPolySlDirFromC : {ar : MLArena} -> (sl : CPFSliceObj ar) ->
  MlPolySlDir ar (mlPolySlOnPosFromC {ar} sl)
mlPolySlDirFromC {ar} sl i j = snd (fst sl) $ fst0 j

public export
mlPolySlOnDirFromC : {ar : MLArena} -> (sl : CPFSliceObj ar) ->
  MlPolySlOnDir {ar} (mlPolySlOnPosFromC {ar} sl) (mlPolySlDirFromC {ar} sl)
mlPolySlOnDirFromC {ar} sl i j d = snd (snd sl) (fst0 j) $ rewrite (snd0 j) in d

public export
mlPolySlObjFromC : (p : PolyFunc) -> CPFSliceObj p -> MlPolySlObj p
mlPolySlObjFromC ar sl =
  MPSobj
    (mlPolySlOnPosFromC {ar} sl)
    (mlPolySlDirFromC {ar} sl)
    (mlPolySlOnDirFromC {ar} sl)

-------------------------------------------------
---- Slices of slices of polynomial functors ----
-------------------------------------------------

public export
MlPolySlOfSl : {ar : MLArena} -> MlPolySlObj ar -> Type
MlPolySlOfSl {ar} sl = MlPolySlObj $ mlPolySlObjTot {ar} sl

public export
MlPolySlPosFromSlOfSl : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  MlPolySlOfSl {ar} sl -> MlSlArProjOnPos ar
MlPolySlPosFromSlOfSl {ar} sl slsl i =
  DPair (mpsOnPos sl i) $ DPair.curry (mpsOnPos slsl) i

public export
MlPolySlDirFromSlOfSl : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  (slsl : MlPolySlOfSl {ar} sl) ->
  MlPolySlDir ar (MlPolySlPosFromSlOfSl {ar} sl slsl)
MlPolySlDirFromSlOfSl {ar} sl slsl i jk =
  (mpsDir sl i (fst jk), mpsDir slsl (i ** fst jk) (snd jk))

public export
MlPolySlOnDirFromSlOfSl : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  (slsl : MlPolySlOfSl {ar} sl) ->
  MlPolySlOnDir {ar}
    (MlPolySlPosFromSlOfSl {ar} sl slsl)
    (MlPolySlDirFromSlOfSl {ar} sl slsl)
MlPolySlOnDirFromSlOfSl {ar} sl slsl i jk bd =
  let sldir = mpsOnDir sl i (fst jk) bd in
  (sldir, mpsOnDir slsl (i ** fst jk) (snd jk) sldir)

public export
MlPolySlFromSlOfSl : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  MlPolySlOfSl {ar} sl -> MlPolySlObj ar
MlPolySlFromSlOfSl {ar} sl slsl =
  MPSobj
    (MlPolySlPosFromSlOfSl {ar} sl slsl)
    (MlPolySlDirFromSlOfSl {ar} sl slsl)
    (MlPolySlOnDirFromSlOfSl {ar} sl slsl)

public export
mlPolySlOfSlFromP : {ar : MLArena} -> {cod : MlPolySlObj ar} ->
  PFSliceMorph {p=ar} (mlPolySlObjToC ar cod) -> MlPolySlOfSl {ar} cod
mlPolySlOfSlFromP {ar} {cod=cod@(MPSobj _ _ _)} m =
  mlPolySlObjFromC (mlPolySlObjTot {ar} cod) m

---------------------------------------------------------------------
---- Slice objects in terms of parameterized polynomial functors ----
---------------------------------------------------------------------

-- The dependent-type view of slices in the category of polynomial functors,
-- which turns the arrows backwards (an object of a slice category "depends"
-- on the functor being sliced over, rather than being a functor with a
-- natural transformation to the functor being sliced over), induces a mapping
-- of positions of the functor being sliced over to polynomial functors.
-- Furthermore, for each such position, it induces a mapping of the directions
-- of the functor being sliced over at that position to directions of the
-- dependent polynomial functors for _each_ position of those functors.
--
-- Thus, the dependent polynomial functors may be viewed as pointed -- each
-- of them, at each of its own positions, must have directions available to
-- which to map the directions of the functor being sliced over (unless that
-- functor has no directions at the corresponding position).

-- To summarize, one way of viewing a polynomial-functor slice object is as a
-- family of polynomial functors parameterized over the positions of the functor
-- being sliced over, together with a section of each functor in the family
-- for each direction of the corresponding position of the functor being
-- sliced over.

public export
PosParamPolyFunc : PolyFunc -> Type
PosParamPolyFunc = ParamPolyFunc . pfPos

export
mlDirichSlObjToPPF : {ar : MLArena} -> MlDirichSlObj ar -> PosParamPolyFunc ar
mlDirichSlObjToPPF {ar=(bpos ** bdir)} (MDSobj slpos sldir) i =
  ((bdir i, slpos i) ** \(bd, j) => sldir i j bd)

export
mlDirichSlObjFromPPF : {ar : MLArena} -> PosParamPolyFunc ar -> MlDirichSlObj ar
mlDirichSlObjFromPPF {ar=(bpos ** bdir)} ppf =
  MDSobj (\i => bdir i -> fst $ ppf i) (\i, sld, bd => snd (ppf i) $ sld bd)

export
mlPolySlObjToPPF : {ar : MLArena} -> MlPolySlObj ar -> PosParamPolyFunc ar
mlPolySlObjToPPF {ar} sl i = (mpsOnPos sl i ** mpsDir sl i)

public export
ParamPFSection : (p : PolyFunc) -> PosParamPolyFunc p -> Type
ParamPFSection p spf = SliceMorphism {a=(pfPos p)} (pfDir {p}) (PFSection . spf)

export
mlPolySlObjToPPFsect : {ar : MLArena} -> (sl : MlPolySlObj ar) ->
  ParamPFSection ar (mlPolySlObjToPPF {ar} sl)
mlPolySlObjToPPFsect {ar} sl i bd j = mpsOnDir sl i j bd

export
mlPolySlObjFromPPFandSections : {ar : MLArena} ->
  (ppf : PosParamPolyFunc ar) -> ParamPFSection ar ppf -> MlPolySlObj ar
mlPolySlObjFromPPFandSections {ar=(bpos ** bdir)} ppf sect =
  MPSobj (fst . ppf) (\i => snd $ ppf i) (\i, j, bd => sect i bd j)

-- Using this formulation, we can characterize a polynomial-functor slice
-- object as represented by the directions of a particular polynomial functor.

PFSliceObjPF : PolyFunc -> PolyFunc
PFSliceObjPF p = (PosParamPolyFunc p ** ParamPFSection p)

PFSliceObj : PolyFunc -> Type
PFSliceObj p = pfPDir $ PFSliceObjPF p

-----------------------------------
---- Slice morphism definition ----
-----------------------------------

-- The morphisms of slice categories correspond to morphisms of the
-- base category which commute with the projections.

-- When we take the dependent-type view in the Dirichlet-functor category, the
-- commutativity conditions are hidden in the type-checking of dependent
-- functions.

public export
MlDirichSlMorOnPos : {ar : MLArena} ->
  MlDirichSlObj ar -> MlDirichSlObj ar -> Type
MlDirichSlMorOnPos {ar} dom cod =
  SliceMorphism {a=(pfPos ar)} (mdsOnPos dom) (mdsOnPos cod)

public export
MlDirichSlMorOnDir : {ar : MLArena} -> (dom, cod : MlDirichSlObj ar) ->
  MlDirichSlMorOnPos {ar} dom cod -> Type
MlDirichSlMorOnDir {ar} dom cod onpos =
  (i : pfPos ar) -> (j : mdsOnPos dom i) ->
    SliceMorphism {a=(pfDir {p=ar} i)}
      (mdsDir dom i j)
      (mdsDir cod i $ onpos i j)

public export
record MlDirichSlMor {ar : MLArena} (dom, cod : MlDirichSlObj ar) where
  constructor MDSM
  mdsmOnPos : MlDirichSlMorOnPos {ar} dom cod
  mdsmOnDir : MlDirichSlMorOnDir {ar} dom cod mdsmOnPos

public export
MlPolySlMorOnPos : {ar : MLArena} ->
  MlPolySlObj ar -> MlPolySlObj ar -> Type
MlPolySlMorOnPos {ar} dom cod =
  SliceMorphism {a=(pfPos ar)} (mpsOnPos dom) (mpsOnPos cod)

public export
MlPolySlMorOnDir : {ar : MLArena} -> (dom, cod : MlPolySlObj ar) ->
  MlPolySlMorOnPos {ar} dom cod -> Type
MlPolySlMorOnDir {ar} dom cod monpos =
  (i : pfPos ar) -> (j : mpsOnPos dom i) ->
  mpsDir cod i (monpos i j) -> mpsDir dom i j

public export
0 MlPolySlMorOnDirCommutes : {ar : MLArena} -> (dom, cod : MlPolySlObj ar) ->
  (onpos : MlPolySlMorOnPos {ar} dom cod) ->
  MlPolySlMorOnDir {ar} dom cod onpos -> Type
MlPolySlMorOnDirCommutes {ar} dom cod monpos mdir =
  (i : pfPos ar) -> (j : mpsOnPos dom i) -> (bd : pfDir {p=ar} i) ->
  mdir i j (mpsOnDir cod i (monpos i j) bd) = mpsOnDir dom i j bd

public export
record MlPolySlMor {ar : MLArena} (dom, cod : MlPolySlObj ar) where
  constructor MPSM
  mpsmOnPos : MlPolySlMorOnPos {ar} dom cod
  mpsmOnDir : MlPolySlMorOnDir {ar} dom cod mpsmOnPos
  mpsmOnDirCommutes : MlPolySlMorOnDirCommutes {ar} dom cod mpsmOnPos mpsmOnDir

------------------------------------------------------------------------
---- Categorial operations in polynomial/Dirichlet slice categories ----
------------------------------------------------------------------------

export
mlDirichSlMorId : {ar : MLArena} -> (p : MlDirichSlObj ar) ->
  MlDirichSlMor {ar} p p
mlDirichSlMorId {ar} p =
  MDSM
    (sliceId $ mdsOnPos p)
    (\i, j => sliceId $ mdsDir p i j)

export
mlDirichSlMorComp : {ar : MLArena} -> {p, q, r : MlDirichSlObj ar} ->
  MlDirichSlMor {ar} q r -> MlDirichSlMor {ar} p q -> MlDirichSlMor {ar} p r
mlDirichSlMorComp {ar} {p} {q} {r} m' m =
  MDSM
    (sliceComp (mdsmOnPos m') (mdsmOnPos m))
    (\i, j, bd, md =>
      mdsmOnDir m' i (mdsmOnPos m i j) bd $ mdsmOnDir m i j bd md)

export
mlPolySlMorId : {ar : MLArena} -> (p : MlPolySlObj ar) ->
  MlPolySlMor {ar} p p
mlPolySlMorId {ar} p =
  MPSM
    (sliceId {a=(pfPos ar)} $ mpsOnPos p)
    (\i => sliceId {a=(mpsOnPos p i)} (mpsDir p i))
    (\i, j, bd => Refl)

export
mlPolySlMorComp : {ar : MLArena} -> {p, q, r : MlPolySlObj ar} ->
  MlPolySlMor {ar} q r -> MlPolySlMor {ar} p q -> MlPolySlMor {ar} p r
mlPolySlMorComp {ar} {p} {q} {r} m' m =
  MPSM
    (sliceComp (mpsmOnPos m') (mpsmOnPos m))
    (\i, j, rd => mpsmOnDir m i j $ mpsmOnDir m' i (mpsmOnPos m i j) rd)
    (\i, j, bd =>
      trans
        (cong (mpsmOnDir m i j) $ mpsmOnDirCommutes m' i (mpsmOnPos m i j) bd)
        (mpsmOnDirCommutes m i j bd))

----------------------------------------------------------------------
---- Equivalence of dependent-type and categorial-style morphisms ----
----------------------------------------------------------------------

public export
mlDirichSlMorToCBase : {ar : MLArena} -> {dom, cod : MlDirichSlObj ar} ->
  MlDirichSlMor dom cod ->
  DirichNatTrans (fst (mlDirichSlObjToC dom)) (fst (mlDirichSlObjToC cod))
mlDirichSlMorToCBase {ar=(bpos ** bdir)}
  {dom=(MDSobj donpos ddir)} {cod=(MDSobj conpos cdir)} (MDSM onpos ondir) =
    (\ij => (fst ij ** onpos (fst ij) (snd ij)) **
     \(i ** j), (d ** dd) => (d ** ondir i j d dd))

public export
mlDirichSlMorToD : {ar : MLArena} -> {dom, cod : MlDirichSlObj ar} ->
  MlDirichSlMor dom cod -> DFSliceMorph {p=ar} (mlDirichSlObjToC cod)
mlDirichSlMorToD {ar=ar@(bpos ** bdir)}
  {dom=dom@(MDSobj donpos ddir)} {cod=cod@(MDSobj conpos cdir)}
  mor@(MDSM onpos ondir) =
    (fst (mlDirichSlObjToC dom) ** mlDirichSlMorToCBase {ar} {dom} {cod} mor)

public export
0 mlDirichSlMorToCD : {ar : MLArena} -> {dom, cod : MlDirichSlObj ar} ->
  MlDirichSlMor dom cod ->
  CDFSliceMorph ar (mlDirichSlObjToC dom) (mlDirichSlObjToC cod)
mlDirichSlMorToCD {ar=(ppos ** pdir)}
  {dom=dom@(MDSobj donpos ddir)} {cod=cod@(MDSobj conpos cdir)}
  mor@(MDSM monpos mondir)
      with
        (DFSliceMorphToC {p=(ppos ** pdir)} {cod=(mlDirichSlObjToC cod)}
          (mlDirichSlMorToD {dom} {cod} mor))
  mlDirichSlMorToCD {ar=(ppos ** pdir)}
    {dom=dom@(MDSobj donpos ddir)} {cod=cod@(MDSobj conpos cdir)}
    mor@(MDSM monpos mondir)
      | Element0 dmnt@(dmonpos ** dmondir) (Evidence0 opeq odeq) =
        Element0
         dmnt
         (Evidence0
            opeq
            $ \i : (DPair ppos donpos),
               d : (DPair (pdir (fst i)) (ddir (fst i) (snd i))) =>
                trans (odeq i d)
                $ case i of (i' ** j') => case d of (d' ** dd') => Refl)

public export
mlDirichSlMorFromD : {ar : MLArena} -> {cod : CDFSliceObj ar} ->
  (mor : DFSliceMorph {p=ar} cod) ->
  MlDirichSlMor
    (mlDirichSlObjFromC {ar} $ DFSliceMorphDom {p=ar} {cod} mor)
    (mlDirichSlObjFromC cod)
mlDirichSlMorFromD {ar=(ppos ** pdir)}
  {cod=((ctot ** cproj) ** (conpos ** condir))}
  ((mpos ** mdir) ** (monpos ** mondir)) =
    MDSM
      (\i, (Element0 j peq) => Element0 (monpos j) peq)
      (\i, (Element0 j peq), pd, (Element0 md deq) =>
        Element0 (mondir j md) deq)

public export
0 mlDirichSlMorFromCD : {ar : MLArena} -> {dom, cod : CDFSliceObj ar} ->
  (mor : CDFSliceMorph ar dom cod) ->
  MlDirichSlMor (mlDirichSlObjFromC {ar} dom) (mlDirichSlObjFromC {ar} cod)
mlDirichSlMorFromCD {ar=(ppos ** pdir)}
  {dom=((dtot ** dproj) ** (donpos ** dondir))}
  {cod=((ctot ** cproj) ** (conpos ** condir))}
  (Element0 (monpos ** mondir) (Evidence0 opeq odeq)) =
    MDSM
      (\i, (Element0 j peq) => Element0 (monpos j) $ trans (sym $ opeq j) peq)
      (\i, (Element0 j peq), pd, (Element0 md deq) =>
        Element0 (mondir j md) $
          trans (odeq j md) $ rewrite sym (opeq j) in deq)

public export
mlPolySlMorOnPos : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod ->
  mlPolySlObjTotPos {ar} dom -> mlPolySlObjTotPos {ar} cod
mlPolySlMorOnPos {ar} {dom} {cod} m i = (fst i ** mpsmOnPos m (fst i) (snd i))

public export
mlPolySlMorOnDir : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  (m : MlPolySlMor {ar} dom cod) ->
  (i : mlPolySlObjTotPos {ar} dom) ->
  mlPolySlObjTotDir {ar} cod (mlPolySlMorOnPos {ar} {dom} {cod} m i) ->
  mlPolySlObjTotDir {ar} dom i
mlPolySlMorOnDir {ar} {dom} {cod} m i = mpsmOnDir m (fst i) (snd i)

public export
mlPolySlMorNT : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod ->
  PolyNatTrans (mlPolySlObjTot {ar} dom) (mlPolySlObjTot {ar} cod)
mlPolySlMorNT {ar} {dom} {cod} m =
  (mlPolySlMorOnPos {ar} {dom} {cod} m ** mlPolySlMorOnDir {ar} {dom} {cod} m)

public export
0 mlPolySlMorToCP : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod ->
  CPFSliceMorph ar (mlPolySlObjToC ar dom) (mlPolySlObjToC ar cod)
mlPolySlMorToCP {ar=ar@(bpos ** bdir)}
  {dom=dom@(MPSobj dpos ddir dondir)} {cod=cod@(MPSobj cpos cdir condir)}
  m@(MPSM monpos mondir mondirc) =
    Element0
      (mlPolySlMorNT {ar} {dom} {cod} m)
      (Evidence0
        (\_ => Refl)
        (\ij, bd => mondirc (fst ij) (snd ij) bd))

public export
0 mlPolySlMorFromCP : {ar : MLArena} -> {dom, cod : CPFSliceObj ar} ->
  CPFSliceMorph ar dom cod ->
  MlPolySlMor {ar} (mlPolySlObjFromC ar dom) (mlPolySlObjFromC ar cod)
mlPolySlMorFromCP {ar=(bpos ** bdir)}
  {dom=dom@((dpos ** ddir) ** (donpos ** dondir))}
  {cod=cod@((cpos ** cdir) ** (conpos ** condir))}
  m@(Element0 (monpos ** mondir) (Evidence0 opeq odeq)) =
    MPSM
      (\i, (Element0 j poseq) =>
        Element0 (monpos j) $ trans (sym (opeq j)) poseq)
      (\i, (Element0 j poseq), cd => mondir j cd)
      (\i, (Element0 j poseq), bd => odeq j $ rewrite poseq in bd)

public export
0 mlPolySlMorToP : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod ->
  PFSliceMorph {p=ar} (mlPolySlObjToC ar cod)
mlPolySlMorToP {ar} {dom} {cod} =
  PFSliceMorphFromC {p=ar}
    {dom=(mlPolySlObjToC ar dom)} {cod=(mlPolySlObjToC ar cod)}
  . mlPolySlMorToCP {ar} {dom} {cod}

public export
0 mlPolySlMorFromP : {ar : MLArena} -> {cod : CPFSliceObj ar} ->
  (m : PFSliceMorph {p=ar} cod) ->
  MlPolySlMor {ar}
    (mlPolySlObjFromC ar $ PFSliceMorphDom {p=ar} {cod} m)
    (mlPolySlObjFromC ar cod)
mlPolySlMorFromP {ar} {cod} m =
  mlPolySlMorFromCP {ar} {dom=(PFSliceMorphDom {p=ar} m)} {cod}
  $ PFSliceMorphToC {p=ar} {cod} m

------------------------------------------------------------------
---- Translation between slice morphisms and slices-of-slices ----
------------------------------------------------------------------

export
MlPolySlMorFromSlOfSl : {ar : MLArena} ->
  (cod : MlPolySlObj ar) -> (slsl : MlPolySlOfSl {ar} cod) ->
  MlPolySlMor {ar} (MlPolySlFromSlOfSl {ar} cod slsl) cod
MlPolySlMorFromSlOfSl {ar=(_ ** _)} (MPSobj _ _ _) slsl =
  MPSM
    (\i, jk => fst jk)
    (\i, jk, cd => (cd, mpsOnDir slsl (i ** fst jk) (snd jk) cd))
    (\i, jk, cd => Refl)

export
MlPolySlMorToSlOfSl : {ar : MLArena} ->
  {dom, cod : MlPolySlObj ar} -> MlPolySlMor {ar} dom cod ->
  MlPolySlOfSl {ar} cod
MlPolySlMorToSlOfSl {ar} {dom} {cod} m =
  mlPolySlObjFromC
    (mlPolySlObjTot {ar} cod)
    (mlPolySlObjTot {ar} dom ** mlPolySlMorNT m)

public export
mlPolySlMorToObj : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod -> MlPolySlObj ar
mlPolySlMorToObj {ar} {dom} {cod} =
  MlPolySlFromSlOfSl {ar} cod . MlPolySlMorToSlOfSl {ar}

public export
mlPolySlMorTot : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod -> PolyFunc
mlPolySlMorTot {ar} {dom} {cod} =
  mlPolySlObjTot {ar=(mlPolySlObjTot {ar} cod)}
  . MlPolySlMorToSlOfSl {dom} {ar}

------------------------------------------------------------------------
------------------------------------------------------------------------
---- Interpretation of polynomial/Dirichlet slice objects/morphisms ----
------------------------------------------------------------------------
------------------------------------------------------------------------

-- This interprets an object in a slice category of Dirichlet functors
-- as an object in the category of presheaves over the category of elements
-- of the base functor.
export
InterpMlDirichSlObj : {ar : PolyFunc} ->
  MlDirichSlObj ar -> (ty : Type) -> SliceObj $ InterpDirichFunc ar ty
InterpMlDirichSlObj {ar=(_ ** _)} (MDSobj slpos sldir) ty (i ** bd) =
  (j : slpos i ** Pi {a=ty} $ sldir i j . bd)

export
InterpMlDirichSlObjF : {ar : PolyFunc} ->
  MlDirichSlObj ar -> MLDirichCatElemObj ar -> Type
InterpMlDirichSlObjF {ar=ar@(_ ** _)} sl (ty ** el) =
  InterpMlDirichSlObj {ar} sl ty el

export
InterpMlDirichSlObjFMap : {bpos : Type} -> {bdir : bpos -> Type} ->
  (sl : MlDirichSlObj (bpos ** bdir)) ->
  (dom, cod : MLDirichCatElemObj (bpos ** bdir)) ->
  -- The functor is contravariant, hence the `cod dom` rather than `dom cod`.
  MLDirichCatElemMor (bpos ** bdir) cod dom ->
  InterpMlDirichSlObjF {ar=(bpos ** bdir)} sl dom ->
  InterpMlDirichSlObjF {ar=(bpos ** bdir)} sl cod
InterpMlDirichSlObjFMap {bpos} {bdir} (MDSobj slpos sldir)
  (dty ** i ** sldty) (cty ** _ ** _) (DCEM _ _ _ _ _ _ _ mm) =
    \(j ** sld) => (j ** \ec => sld $ mm ec)

export
InterpMlDirichSlObjFMapAr : {ar : PolyFunc} ->
  (sl : MlDirichSlObj ar) ->
  (dom, cod : MLDirichCatElemObj ar) ->
  MLDirichCatElemMor ar cod dom ->
  InterpMlDirichSlObjF {ar} sl dom ->
  InterpMlDirichSlObjF {ar} sl cod
InterpMlDirichSlObjFMapAr {ar=(bpos ** bdir)} =
  InterpMlDirichSlObjFMap {bpos} {bdir}

-- This interprets a morphism in a slice category of Dirichlet functors
-- as a morphism in the category of presheaves over the category of elements
-- of the base functor (the latter is a natural transformation).
--
-- This implements a proof, in the particular case of Dirichlet functors,
-- that a slice category over a presheaf `p` is a presheaf over the category
-- of elements of `p`.
--
-- We may view this as the morphism component of a functor, whose object
-- component is `InterpMlDirichSlObj`, from the slice category of Dirichlet
-- functors over `ar` to the category of presheaves over the category of
-- elements of `ar`.
export
InterpMlDirichSlMor : {ar : PolyFunc} ->
  {dom, cod : MlDirichSlObj ar} -> MlDirichSlMor dom cod ->
  (ty : Type) -> (el : InterpDirichFunc ar ty) ->
  InterpMlDirichSlObj {ar} dom ty el ->
  InterpMlDirichSlObj {ar} cod ty el
InterpMlDirichSlMor {ar=(bpos ** bdir)}
  {dom=(MDSobj dpos ddir)} {cod=(MDSobj cpos cdir)}
  (MDSM monpos mondir) ty (i ** bd) dpd =
    (monpos i (fst dpd) **
     \elty => mondir i (fst dpd) (bd elty) $ snd dpd elty)

-- This interprets an object in a slice category of polynomial functors
-- as an object in the category of presheaves over the category of elements
-- of the base functor.
export
InterpMlPolySlObj : {ar : PolyFunc} ->
  MlPolySlObj ar -> (ty : Type) -> SliceObj $ InterpPolyFunc ar ty
InterpMlPolySlObj {ar} sl ty el with (mlPolySlObjToC ar sl)
  InterpMlPolySlObj {ar} sl ty el | (q ** alpha) =
    PreImage {a=(InterpPolyFunc q ty)} {b=(InterpPolyFunc ar ty)}
      (InterpPolyNT alpha ty) el

export
InterpMlPolySlObjF : {ar : PolyFunc} ->
  MlPolySlObj ar -> MLPolyCatElemObj ar -> Type
InterpMlPolySlObjF {ar=ar@(_ ** _)} sl (ty ** el) =
  InterpMlPolySlObj {ar} sl ty el

export
InterpMlPolySlObjFMap : {bpos : Type} -> {bdir : bpos -> Type} ->
  (sl : MlPolySlObj (bpos ** bdir)) ->
  (dom, cod : MLPolyCatElemObj (bpos ** bdir)) ->
  MLPolyCatElemMor (bpos ** bdir) dom cod ->
  InterpMlPolySlObjF {ar=(bpos ** bdir)} sl dom ->
  InterpMlPolySlObjF {ar=(bpos ** bdir)} sl cod
InterpMlPolySlObjFMap {bpos} {bdir} (MPSobj slpos sldir slondir)
  (dty ** i ** sldty) (cty ** _ ** _) (PCEM _ _ _ _ _ _ _ mm) =
    \(Element0 ((j ** k) ** sldi) eq) =>
      Element0
        ((j ** k) ** mm . sldi)
        $ case eq of Refl => Refl

export
InterpMlPolySlObjFMapAr : {ar : PolyFunc} ->
  (sl : MlPolySlObj ar) ->
  (dom, cod : MLPolyCatElemObj ar) ->
  MLPolyCatElemMor ar dom cod ->
  InterpMlPolySlObjF {ar} sl dom ->
  InterpMlPolySlObjF {ar} sl cod
InterpMlPolySlObjFMapAr {ar=(bpos ** bdir)} =
  InterpMlPolySlObjFMap {bpos} {bdir}

-- This interprets a morphism in a slice category of polynomial functors
-- as a morphism in the category of copresheaves over the category of elements
-- of the base functor (the latter is a natural transformation).
--
-- This implements a proof, in the particular case of polynomial functors,
-- that a slice category over a copresheaf `p` is a copresheaf over the category
-- of elements of `p`.
--
-- We may view this as the morphism component of a functor, whose object
-- component is `InterpMlPolySlObj`, from the slice category of polynomial
-- functors over `ar` to the category of copresheaves over the category of
-- elements of `ar`.
export
InterpMlPolySlMor : FunExt -> {ar : PolyFunc} ->
  {dom, cod : MlPolySlObj ar} -> MlPolySlMor dom cod ->
  (ty : Type) -> (el : InterpPolyFunc ar ty) ->
  InterpMlPolySlObj {ar} dom ty el ->
  InterpMlPolySlObj {ar} cod ty el
InterpMlPolySlMor fext {ar=(bpos ** bdir)}
  {dom=(MPSobj dpos ddir dondir)} {cod=(MPSobj cpos cdir condir)}
  (MPSM monpos mondir mondircomm) ty el (Element0 (i ** dd) eleq) =
    Element0
      ((fst i ** monpos (fst i) (snd i)) **
       \cd => dd $ mondir (fst i) (snd i) cd)
      $ trans
        (dpEq12 Refl $ funExt $ \bd => cong dd $ mondircomm (fst i) (snd i) bd)
        eleq

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---- Slice categories of polynomial functors (in dependent-type style) ----
---------------------------------------------------------------------------
---------------------------------------------------------------------------

------------------------------------------------------
---- Polynomial-functor slice functor definitions ----
------------------------------------------------------

export
0 MlDirichSlFunc : MLArena -> MLArena -> Type
MlDirichSlFunc p q = MlDirichSlObj p -> MlDirichSlObj q

export
0 MlDirichSlFMap : {ar, ar' : MLArena} -> MlDirichSlFunc ar ar' -> Type
MlDirichSlFMap {ar} {ar'} f =
  (0 sl, sl' : MlDirichSlObj ar) ->
  MlDirichSlMor {ar} sl sl' -> MlDirichSlMor {ar=ar'} (f sl) (f sl')

export
0 MlPolySlFunc : MLArena -> MLArena -> Type
MlPolySlFunc p q = MlPolySlObj p -> MlPolySlObj q

export
0 MlPolySlFMap : {ar, ar' : MLArena} -> MlPolySlFunc ar ar' -> Type
MlPolySlFMap {ar} {ar'} f =
  (0 sl, sl' : MlPolySlObj ar) ->
  MlPolySlMor {ar} sl sl' -> MlPolySlMor {ar=ar'} (f sl) (f sl')

---------------------
---- Base change ----
---------------------

-- When we express slice objects over a polynomial functor as fibrations
-- rather than total-space objects with projection morphisms, we can perform
-- base changes by specifying the data not of a polynomial natural
-- transformation, but of a Dirichlet natural transformation.
export
mlPolySlBaseChange : {p, q : PolyFunc} ->
  DirichNatTrans q p -> MlPolySlFunc p q
mlPolySlBaseChange {p} {q} (onpos ** ondir) (MPSobj slonpos sldir slondir) =
  MPSobj
    (slonpos . onpos)
    (\i => sldir $ onpos i)
    (\i, j, qd => slondir (onpos i) j $ ondir i qd)

export
mlPolySlBaseChangeMap : {p, q : PolyFunc} -> (nt : DirichNatTrans q p) ->
  MlPolySlFMap {ar=p} {ar'=q} (mlPolySlBaseChange {p} {q} nt)
mlPolySlBaseChangeMap {p} {q} (ntonpos ** ntondir)
  (MPSobj dpos ddir dondir) (MPSobj cpos cdir condir) m =
    MPSM
      (\qp => mpsmOnPos m (ntonpos qp))
      (\qp, dp, cd => mpsmOnDir m (ntonpos qp) dp cd)
      (\qp, dp, bd => mpsmOnDirCommutes m (ntonpos qp) dp (ntondir qp bd))

export
mlDirichSlBaseChange : {p, q : PolyFunc} ->
  DirichNatTrans q p -> MlDirichSlFunc p q
mlDirichSlBaseChange {p} {q} (onpos ** ondir) (MDSobj slpos sldir) =
  MDSobj (slpos . onpos) (\qp, sp, qd => sldir (onpos qp) sp $ ondir qp qd)

export
mlDirichSlBaseChangeMap : {p, q : PolyFunc} -> (nt : DirichNatTrans q p) ->
  MlDirichSlFMap {ar=p} {ar'=q} (mlDirichSlBaseChange {p} {q} nt)
mlDirichSlBaseChangeMap {p} {q} (ntonpos ** ntondir)
  (MDSobj dpos ddir) (MDSobj cpos cdir) (MDSM monpos mondir) =
    MDSM
      (\qp, dp => monpos (ntonpos qp) dp)
      (\qp, dp, qd, dd => mondir (ntonpos qp) dp (ntondir qp qd) dd)

-------------------------------
---- Sigma (dependent sum) ----
-------------------------------

MLPolySlSigma : (q : PolyFunc) -> {p : PolyFunc} ->
  PolyNatTrans p q -> MlPolySlObj p -> MlPolySlObj q
MLPolySlSigma q {p} beta sl with (mlPolySlObjToC p sl)
  MLPolySlSigma q {p} beta sl | (r ** alpha) =
    let csigma = (r ** pntVCatComp beta alpha) in
    mlPolySlObjFromC q csigma

-------------------------------------------------------------
---- Polynomial-functor slice category utility functions ----
-------------------------------------------------------------

-- A slice object over a constant functor is effectively a polynomial
-- functor parameterized over terms of the output type of the constant functor.
mlPolySliceOverConst : {x : Type} -> MlPolySlObj (PFConstArena x) ->
  ParamPolyFunc x
mlPolySliceOverConst {x} (MPSobj onpos dir ondir) ex =
  -- The arguments of `ondir` include a term of type `Void`, so
  -- it is impossible to apply (unless we find such a term, and
  -- hence a contradiction in our metalanguage).  Thus we can and
  -- must ignore it.
  --
  -- Put another way, `ondir` gives us no information, because its type
  -- restricts it to being effectively just the unique morphism out
  -- of the initial object.
  (onpos ex ** \i => dir ex i)

-- A slice object over the terminal polynomial functor is effectively
-- just a polynomial functor, just as a slice of `Type` over `Unit` is
-- effectively just a type.
mlPolySliceOver1 : MlPolySlObj PFTerminalArena -> PolyFunc
mlPolySliceOver1 psl = mlPolySliceOverConst {x=Unit} psl ()

mlPolyAppI : {p : PolyFunc} ->
  {- these two parameters form an object of the category of elements of `p`
   - interpreted as a Dirichlet functor -}
  (ty : Type) -> (el : InterpDirichFunc p ty) ->
  MlPolySlObj p -> MlPolySlObj (PFHomArena ty)
mlPolyAppI {p=p@(_ ** _)} ty (i ** d) =
  mlPolySlBaseChange {p} {q=(PFHomArena ty)} (\() => i ** \() => d)

-- By analogy with the application of a `SliceObj x` in `Type` to a term
-- of `x`, `PFApp` is a base change from the slice category over `p` to
-- the slice category over the terminal polynomial functor, which is
-- effectively just the category of polynomial endofunctors on `Type`.
-- Such a base change requires a Dirichlet (not polynomial!) natural
-- transformation from the terminal polynomial functor (which is just
-- a single position with no directions) to the functor being sliced over.
-- That in turn amounts to simply a choice of position of the functor
-- being sliced over, which dictates which dependent polynomial functor
-- to select as the result.
mlPolyApp1 : {p : PolyFunc} -> pfPos p -> MlPolySlObj p -> PolyFunc
mlPolyApp1 {p=p@(pos ** dir)} i slp =
  mlPolySliceOver1 $ mlPolyAppI {p} Void (i ** \v => void v) slp

----------------------------
----------------------------
---- Generalized arenas ----
----------------------------
----------------------------

--------------------
---- Telescopes ----
--------------------

data MLTelFPos : (tl : Type) -> Type where
  MLUnitPos : {0 tl : Type} -> MLTelFPos tl
  MLDPairPos : {0 tl : Type} -> SliceObj tl -> MLTelFPos tl

MLTelFDir : Sigma {a=Type} MLTelFPos -> Type
MLTelFDir (tl ** MLUnitPos) = Void
MLTelFDir (tl ** (MLDPairPos {tl} sl)) = Unit

MLTelFAssign : Sigma {a=(Sigma {a=Type} MLTelFPos)} MLTelFDir -> Type
MLTelFAssign ((tl ** MLUnitPos) ** v) = void v
MLTelFAssign ((tl ** (MLDPairPos {tl} sl)) ** ()) = Sigma {a=tl} sl

MLTelF : SlicePolyEndoFunc Type
MLTelF = (MLTelFPos ** MLTelFDir ** MLTelFAssign)

MLTel : Type -> Type
MLTel = SPFMu MLTelF

MLFreeTel : SliceEndofunctor Type
MLFreeTel = SlicePolyFree MLTelF

----------------------------------------------
----------------------------------------------
---- Factorized slice polynomial functors ----
----------------------------------------------
----------------------------------------------

-- Because `Cat` has a factorization system -- all functors can be factored
-- into two, via a category of elements of a functor out of the codomain --
-- we could also choose to _define_ a functor as a composite of two functors
-- of that specific form.

-- So we begin with a definition of a polynomial (co)presheaf on a slice
-- category.
public export
SlPolyAr : Type -> Type
SlPolyAr c = IntArena (SliceObj c)

public export
SlIntComp : (c : Type) -> IntCompSig (SliceObj c) (SliceMorphism {a=c})
SlIntComp c x y z g f = \ela, elx => g ela $ f ela elx

public export
SlArInterp : {c : Type} -> SlPolyAr c -> SliceObj c -> Type
SlArInterp {c} = InterpIPFobj (SliceObj c) (SliceMorphism {a=c})

public export
0 SlPolyArMapSig : {c : Type} -> SlPolyAr c -> Type
SlPolyArMapSig {c} ar =
  IntCopreshfMapSig (SliceObj c) (SliceMorphism {a=c}) (SlArInterp {c} ar)

public export
SlArFMap : {c : Type} -> (ar : SlPolyAr c) -> SlPolyArMapSig {c} ar
SlArFMap {c} = InterpIPFmap (SliceObj c) (SliceMorphism {a=c}) (SlIntComp c)
