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

-- Because base change is in the middle of an adjoint triple between
-- dependent sum and dependent product, it can introduced and eliminated
-- from either side, by the adjuncts defined below with `Sigma` and `Pi`.

export
bcMap : {0 c, d : Type} -> {f : c -> d} -> SliceFMap (BaseChangeF {a=d} {b=c} f)
bcMap {c} {d} {f} sa sb m ec = m (f ec)

--------------------------------
----- Base change as W-type ----
--------------------------------

0 BCasWTF : {c, d : Type} -> (f : d -> c) -> WTypeFunc c d
BCasWTF {c} {d} f = MkWTF {dom=c} {cod=d} d d f id id

bcToWTF : {c, d : Type} -> (0 f : d -> c) ->
  SliceNatTrans (BaseChangeF {a=c} {b=d} f) (InterpWTF $ BCasWTF f)
bcToWTF {c} {d} f sc ed efd =
  (Element0 ed Refl **
   \(Element0 ed' eq) => replace {p=(BaseChangeF f sc)} (sym eq) efd)

bcFromWTF : {c, d : Type} -> (0 f : d -> c) ->
  SliceNatTrans (InterpWTF $ BCasWTF f) (BaseChangeF {a=c} {b=d} f)
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

-- The slice functor from `c` to `d` which takes a subobject of `c` to
-- the subobject of `d` whose terms consist of single applications
-- of `f` to terms of the given subobject.
--
-- When it is an endofunctor (i.e. `d` is `c`), Its initial algebra
-- (least fixed point) is simply the initial object of `SliceObj c`
-- (`const Void`); that initial algebra (as with any functor that has a
-- free monad) is isomorphic to the application of its free monad to the
-- initial object of `SliceObj c`, which is hence also `const Void`.
export
data SliceSigmaF : {0 c, d : Type} -> (0 f : c -> d) -> SliceFunctor c d where
  SS : {0 c, d : Type} -> {0 f : c -> d} -> {0 sc : SliceObj c} ->
    {ec : c} -> sc ec -> SliceSigmaF {c} {d} f sc (f ec)

--------------------------
----- Sigma as W-type ----
--------------------------

0 SSasWTF : {c, d : Type} -> (f : c -> d) -> WTypeFunc c d
SSasWTF {c} {d} f = MkWTF {dom=c} {cod=d} c c id id f

ssToWTF : {c, d : Type} -> (0 f : c -> d) ->
  SliceNatTrans (SliceSigmaF {c} {d} f) (InterpWTF $ SSasWTF f)
ssToWTF {c} {d} f sc (f ec) (SS {c} {d} {f} {sc} {ec} sec) =
  (Element0 ec Refl ** \(Element0 ec' eq) => replace {p=sc} (sym eq) sec)

ssFromWTF : {c, d : Type} -> (0 f : c -> d) ->
  SliceNatTrans (InterpWTF $ SSasWTF f) (SliceSigmaF {c} {d} f)
ssFromWTF {c} {d} f sc ed (Element0 ec eq ** scd) =
  replace {p=(SliceSigmaF f sc)} eq
  $ SS {c} {d} {f} {sc} {ec} $ scd (Element0 ec Refl)

-------------------------
---- Adjunction data ----
-------------------------

-- The monad of the dependent-sum/base-change adjunction.
export
SSMonad : {c, d : Type} -> (f : c -> d) -> SliceEndofunctor c
SSMonad {c} {d} f = BaseChangeF f . SliceSigmaF {c} {d} f

-- The comonad of the dependent-sum/base-change adjunction.
export
SSComonad : {c, d : Type} -> (f : c -> d) -> SliceEndofunctor d
SSComonad {c} {d} f = SliceSigmaF {c} {d} f . BaseChangeF f

-- Rather than making the constructor `SS` explicit, we export an
-- alias for it viewed as a natural transformation.
--
-- This is the unit (AKA "pure" or "return") of the dependent-sum/base-change
-- adjunction.
export
sSin : {0 c, d : Type} -> {0 f : c -> d} ->
  SliceNatTrans {x=c} {y=c} (SliceIdF c) (SSMonad {c} {d} f)
sSin {c} {d} {f} sc ec = SS {c} {d} {f} {sc} {ec}

-- The counit (AKA "erase" or "extract") of the dependent-sum/base-change
-- adjunction.
export
sSout : {0 c, d : Type} -> {0 f : c -> d} ->
  SliceNatTrans {x=d} {y=d} (SSComonad {c} {d} f) (SliceIdF d)
sSout {c} {d} {f} sd (f ec) (SS {sc=(BaseChangeF f sd)} {ec} sec) = sec

-- This is the right adjunct of the dependent-sum/base-change adjunction.
--
-- It constitutes the destructor for `SliceSigmaF f sc`.  As an adjunction,
-- it is parametrically polymorphic:  rather than receiving a witness to a
-- given `ec : c` being in the image of `f` applied to a given slice over
-- `c`, it passes in a handler for _any_ such witness.
export
ssElim : {0 c, d : Type} -> {0 f : c -> d} ->
  {0 sa : SliceObj c} -> {sb : SliceObj d} ->
  SliceMorphism {a=c} sa (BaseChangeF f sb) ->
  SliceMorphism {a=d} (SliceSigmaF {c} {d} f sa) sb
ssElim {c} {d} {f} {sa} {sb} m (f ec) (SS {ec} sea) = m ec sea

-- This is the left adjunct of the dependent-sum/base-change adjunction.
export
ssLAdj : {0 c, d : Type} -> {f : c -> d} ->
  {0 sa : SliceObj c} -> {sb : SliceObj d} ->
  SliceMorphism {a=d} (SliceSigmaF {c} {d} f sa) sb ->
  SliceMorphism {a=c} sa (BaseChangeF f sb)
ssLAdj {c} {d} {f} {sa} {sb} m ec esa = m (f ec) $ SS {ec} esa

export
ssMap : {0 c, d : Type} -> {0 f : c -> d} -> SliceFMap (SliceSigmaF {c} {d} f)
ssMap {c} {d} {f} sa sb m (f ec) (SS {ec} esc) = SS {ec} $ m ec esc

export
ssmMap : {0 c, d : Type} -> {f : c -> d} -> SliceFMap (SSMonad {c} {d} f)
ssmMap {c} {d} {f} sa sb =
  bcMap (SliceSigmaF f sa) (SliceSigmaF f sb) {f}
  . ssMap sa sb {f}

export
sscmMap : {c, d : Type} -> {f : c -> d} -> SliceFMap (SSComonad {c} {d} f)
sscmMap {c} {d} {f} sa sb =
  ssMap {f} (BaseChangeF f sa) (BaseChangeF f sb) . bcMap sa sb {f}

-- This is the multiplication (AKA "join") of the dependent-sum/base-change
-- adjunction.
--
-- The multiplication comes from whiskering the counit between the adjuncts.
export
sSjoin : {c, d : Type} -> {f : c -> d} ->
  SliceNatTrans {x=c} {y=c}
    (SSMonad {c} {d} f . SSMonad {c} {d} f)
    (SSMonad {c} {d} f)
sSjoin {c} {d} {f} =
  SliceWhiskerRight
    {f=(SSComonad f . SliceSigmaF f)}
    {g=(SliceSigmaF f)}
    {h=(BaseChangeF f)}
    (bcMap {f})
  $ SliceWhiskerLeft
    {g=(SSComonad f)}
    {h=(SliceIdF d)}
    (sSout {f})
    (SliceSigmaF f)

-- This is the comultiplication (AKA "duplicate") of the
-- dependent-sum/base-change adjunction.
--
-- The comultiplication comes from whiskering the unit between the adjuncts.
export
sSdup : {c, d : Type} -> {f : c -> d} ->
  SliceNatTrans {x=d} {y=d}
    (SSComonad {c} {d} f)
    (SSComonad {c} {d} f . SSComonad {c} {d} f)
sSdup {c} {d} {f} =
  SliceWhiskerRight
    {f=(BaseChangeF f)}
    {g=(BaseChangeF f . SSComonad f)}
    {h=(SliceSigmaF f)}
    (ssMap {f})
  $ SliceWhiskerLeft
    {g=(SliceIdF c)}
    {h=(SSMonad f)}
    sSin
    (BaseChangeF f)

export
SSAlg : {c : Type} -> (0 f : c -> c) -> (sc : SliceObj c) -> Type
SSAlg {c} {f} = SliceAlg {a=c} (SliceSigmaF {c} {d=c} f)

export
SSVoidAlg : {c : Type} -> (0 f : c -> c) -> SSAlg {c} f (const Void)
SSVoidAlg {c} f (f ec) (SS {ec} v) = v

export
SSCoalg : {c : Type} -> (0 f : c -> c) -> (sc : SliceObj c) -> Type
SSCoalg {c} {f} = SliceCoalg {a=c} (SliceSigmaF {c} {d=c} f)

--------------------------------
---- Pointed dependent sums ----
--------------------------------

SlicePointedSigmaF : {c, d : Type} -> (f : c -> d) ->
  SliceObj d -> SliceFunctor c d
SlicePointedSigmaF {c} {d} f = SlPointedF {c} {d} (SliceSigmaF {c} {d} f)

SPIAlg : {c : Type} -> (f : c -> c) -> (sv, sc : SliceObj c) -> Type
SPIAlg {c} f = SlPointedAlg {c} (SliceSigmaF {c} {d=c} f)

SPICoalg : {c : Type} -> (f : c -> c) -> (sv, sc : SliceObj c) -> Type
SPICoalg {c} f = SlPointedCoalg {c} (SliceSigmaF {c} {d=c} f)

----------------------------------
---- Copointed dependent sums ----
----------------------------------

SliceCopointedSigmaF : {c, d : Type} -> (f : c -> d) ->
  SliceObj d -> SliceFunctor c d
SliceCopointedSigmaF {c} {d} f = SlCopointedF {c} {d} (SliceSigmaF {c} {d} f)

SCPIAlg : {c : Type} -> (f : c -> c) -> (sv, sc : SliceObj c) -> Type
SCPIAlg {c} f = SlCopointedAlg {c} (SliceSigmaF {c} {d=c} f)

SCPICoalg : {c : Type} -> (f : c -> c) -> (sv, sc : SliceObj c) -> Type
SCPICoalg {c} f = SlCopointedCoalg {c} (SliceSigmaF {c} {d=c} f)

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

--------------------
---- Definition ----
--------------------

-- The slice functor from `c` to `d` which consists of a product of `d`
-- representable functors from `SliceObj c`.  Products of representables
-- are themselves representable (products of covariant representables are
-- represented by sums, and products of contravariant representables are
-- represented by products).
export
SlicePiF : {c : Type} -> (d -> c -> Type) -> SliceFunctor c d
SlicePiF sdc sc ed = SliceCovarRepF (sdc ed) {c} sc ()

--------------------------------------
----- Dependent product as W-type ----
--------------------------------------

0 SPasWTF : {c, d : Type} -> (p : d -> c -> Type) -> WTypeFunc c d
SPasWTF {c} {d} p =
  MkWTF {dom=c} {cod=d}
    d
    (Sigma {a=(d, c)} (uncurry p))
    (snd . fst)
    (fst . fst)
    (id {a=d})

spToWTF : {c, d : Type} -> (0 p : d -> c -> Type)->
  SliceNatTrans (SlicePiF {c} {d} p) (InterpWTF $ SPasWTF p)
spToWTF {c} {d} p sc ed mpsc =
  (Element0 ed Refl **
   \(Element0 ((ed', ec') ** pdc) eq) =>
    mpsc ec' $ replace {p=(flip p ec')} eq pdc)

spFromWTF : {c, d : Type} -> (0 p : d -> c -> Type)->
  SliceNatTrans (InterpWTF $ SPasWTF p) (SlicePiF {c} {d} p)
spFromWTF {c} {d} p sc ed (Element0 ed' eq ** mpsc) =
  \ec, pdc => mpsc (Element0 ((ed, ec) ** pdc) $ sym eq)

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

--------------------------------------
--------------------------------------
---- Free monad on dependent sums ----
--------------------------------------
--------------------------------------

-- The free monad comes from a free-forgetful adjunction between `SliceObj c`
-- (on the right) and the category of `SliceSigmaF f`-algebras on that category
-- (on the left).
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
data SliceSigmaFM : {0 c : Type} -> (0 f : c -> c) -> SliceEndofunctor c where
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
SScom : {0 c : Type} -> {f : c -> c} -> {0 sc : SliceObj c} ->
  SSAlg {c} f (SliceSigmaFM {c} f sc)
SScom {c} {f} {sc} ec =
  SSin {c} {f} {sc} ec
  . inSlPc {f=(SliceSigmaF f)} {sl=sc} {sa=(SliceSigmaFM f sc)} ec

-- The unit of the free-monad adjunction -- a natural transformation of
-- endofunctors on `SliceObj a`, from the identity endofunctor to
-- `SliceSigmaFM f`.
export
SSvar : {0 c : Type} -> {f : c -> c} ->
  SliceNatTrans (SliceIdF c) (SliceSigmaFM {c} f)
SSvar {c} {f} sc ec t =
  SSin {c} {f} {sc} ec
  $ inSlPv {f=(SliceSigmaF f)} {sl=sc} {sa=(SliceSigmaFM f sc)} ec t

-- The counit of the free-monad adjunction -- a natural transformation of
-- endofunctors on algebras of `SliceSigmaF f`, from `SSFMAlg` to the identity
-- endofunctor.
export
SSFcounit : {c : Type} -> {f : c -> c} ->
  SliceMorphism {a=(SliceObj c)} (SSFMAlg {c} f) (SSAlg {c} f)
SSFcounit {c} {f} sc alg =
  sliceComp alg $ sliceComp (SScom {c} {f} {sc})
  $ ssMap sc (SliceSigmaFM f sc)
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
    SS {ec=ec'} sec => SS {ec=ec'} $ SliceSigmaEval sb alg sa subst ec' sec

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
SliceSigmaFMLAdj : {0 c : Type} -> {f : c -> c} -> (sa, sb : SliceObj c) ->
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
  SliceNatTrans (SliceSigmaFM {c} f . SliceSigmaFM {c} f) (SliceSigmaFM {c} f)
ssfJoin {c} {f} sc =
  SliceSigmaEval {c} {f} (SliceSigmaFM f sc)
    (SScom {f} {sc}) (SliceSigmaFM f sc) (sliceId $ SliceSigmaFM f sc)

-- The comultiplication (or "duplicate") of the free-monad adjunction -- a
-- natural transformation of endofunctors on algebras of `SliceSigmaF f`, from
-- `SSFMAlg` to `SSFMAlg . SliceSigmaFM`.
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
mlDirSlObjTotPos : {ar : MLArena} -> MlDirichSlObj ar -> Type
mlDirSlObjTotPos {ar} sl = MlSlArTotPos {ar} $ mdsOnPos sl

public export
mlDirSlObjTotDir : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  mlDirSlObjTotPos {ar} sl -> Type
mlDirSlObjTotDir {ar} sl ij = Sigma $ mdsDir sl (fst ij) (snd ij)

public export
mlDirSlObjTot : {ar : MLArena} -> MlDirichSlObj ar -> MLArena
mlDirSlObjTot {ar} sl = (mlDirSlObjTotPos {ar} sl ** mlDirSlObjTotDir {ar} sl)

public export
mlDirSlObjProjOnPos : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  mlDirSlObjTotPos sl -> pfPos ar
mlDirSlObjProjOnPos {ar} sl = DPair.fst

public export
mlDirSlObjProjOnDir : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  (i : mlDirSlObjTotPos sl) ->
  mlDirSlObjTotDir {ar} sl i -> pfDir {p=ar} (mlDirSlObjProjOnPos sl i)
mlDirSlObjProjOnDir {ar} sl _ = DPair.fst

public export
mlDirSlObjProj : {ar : MLArena} -> (sl : MlDirichSlObj ar) ->
  DirichNatTrans (mlDirSlObjTot {ar} sl) ar
mlDirSlObjProj {ar} sl =
  (mlDirSlObjProjOnPos {ar} sl ** mlDirSlObjProjOnDir {ar} sl)

public export
mlDirSlObjToC : {ar : MLArena} -> MlDirichSlObj ar -> CDFSliceObj ar
mlDirSlObjToC {ar} sl = (mlDirSlObjTot {ar} sl ** mlDirSlObjProj {ar} sl)

public export
mlDirSlOnPosFromC : {ar : MLArena} -> CDFSliceObj ar -> MlSlArProjOnPos ar
mlDirSlOnPosFromC {ar} sl i = PreImage (fst $ snd sl) i

public export
mlDirSlDirFromCBase : {ar : MLArena} -> (sl : CDFSliceObj ar) ->
  MlDirichSlDir ar (mlDirSlOnPosFromC {ar} sl)
mlDirSlDirFromCBase {ar} sl i j bd = snd (fst sl) (fst0 j)

public export
mlDirSlDirFromCProp : {ar : MLArena} -> (sl : CDFSliceObj ar) ->
  (i : pfPos ar) -> (j : mlDirSlOnPosFromC {ar} sl i) ->
  (bd : pfDir {p=ar} i) -> SliceObj (mlDirSlDirFromCBase {ar} sl i j bd)
mlDirSlDirFromCProp {ar} sl i j bd sld =
  snd (snd sl) (fst0 j) sld = replace {p=(pfDir {p=ar})} (sym $ snd0 j) bd

public export
mlDirSlDirFromC : {ar : MLArena} -> (sl : CDFSliceObj ar) ->
  MlDirichSlDir ar (mlDirSlOnPosFromC {ar} sl)
mlDirSlDirFromC {ar} sl i j bd =
  Subset0
    (mlDirSlDirFromCBase {ar} sl i j bd)
    (mlDirSlDirFromCProp {ar} sl i j bd)

public export
mlDirSlObjFromC : {ar : MLArena} -> CDFSliceObj ar -> MlDirichSlObj ar
mlDirSlObjFromC {ar} sl =
  MDSobj (mlDirSlOnPosFromC {ar} sl) (mlDirSlDirFromC {ar} sl)

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
data MlPolySlMor :
    {ar : MLArena} -> (dom, cod : MlPolySlObj ar) -> Type where
  MPSM : {ar : MLArena} -> {cod : MlPolySlObj ar} ->
    (slsl : MlPolySlOfSl {ar} cod) ->
    MlPolySlMor {ar} (MlPolySlFromSlOfSl {ar} cod slsl) cod

public export
mlPolySlMorToSlOfSl : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod -> MlPolySlOfSl {ar} cod
mlPolySlMorToSlOfSl {ar} {cod} (MPSM {ar} {cod} slsl) = slsl

----------------------------------------------------------------------
---- Equivalence of dependent-type and categorial-style morphisms ----
----------------------------------------------------------------------

public export
mlDirSlMorToCBase : {ar : MLArena} -> {dom, cod : MlDirichSlObj ar} ->
  MlDirichSlMor dom cod ->
  DirichNatTrans (fst (mlDirSlObjToC dom)) (fst (mlDirSlObjToC cod))
mlDirSlMorToCBase {ar=(bpos ** bdir)}
  {dom=(MDSobj donpos ddir)} {cod=(MDSobj conpos cdir)} (MDSM onpos ondir) =
    (\ij => (fst ij ** onpos (fst ij) (snd ij)) **
     \(i ** j), (d ** dd) => (d ** ondir i j d dd))

public export
mlDirSlMorToD : {ar : MLArena} -> {dom, cod : MlDirichSlObj ar} ->
  MlDirichSlMor dom cod -> DFSliceMorph {p=ar} (mlDirSlObjToC cod)
mlDirSlMorToD {ar=ar@(bpos ** bdir)}
  {dom=dom@(MDSobj donpos ddir)} {cod=cod@(MDSobj conpos cdir)}
  mor@(MDSM onpos ondir) =
    (fst (mlDirSlObjToC dom) ** mlDirSlMorToCBase {ar} {dom} {cod} mor)

public export
0 mlDirSlMorToC : {ar : MLArena} -> {dom, cod : MlDirichSlObj ar} ->
  MlDirichSlMor dom cod ->
  CDFSliceMorph ar (mlDirSlObjToC dom) (mlDirSlObjToC cod)
mlDirSlMorToC {ar=(ppos ** pdir)}
  {dom=dom@(MDSobj donpos ddir)} {cod=cod@(MDSobj conpos cdir)}
  mor@(MDSM monpos mondir)
      with
        (DFSliceMorphToC {p=(ppos ** pdir)} {cod=(mlDirSlObjToC cod)}
          (mlDirSlMorToD {dom} {cod} mor))
  mlDirSlMorToC {ar=(ppos ** pdir)}
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
mlDirSlMorFromD : {ar : MLArena} -> {cod : CDFSliceObj ar} ->
  (mor : DFSliceMorph {p=ar} cod) ->
  MlDirichSlMor
    (mlDirSlObjFromC {ar} $ DFSliceMorphDom {p=ar} {cod} mor)
    (mlDirSlObjFromC cod)
mlDirSlMorFromD {ar=(ppos ** pdir)}
  {cod=((ctot ** cproj) ** (conpos ** condir))}
  ((mpos ** mdir) ** (monpos ** mondir)) =
    MDSM
      (\i, (Element0 j peq) => Element0 (monpos j) peq)
      (\i, (Element0 j peq), pd, (Element0 md deq) =>
        Element0 (mondir j md) deq)

public export
0 mlDirSlMorFromC : {ar : MLArena} -> {dom, cod : CDFSliceObj ar} ->
  (mor : CDFSliceMorph ar dom cod) ->
  MlDirichSlMor (mlDirSlObjFromC {ar} dom) (mlDirSlObjFromC {ar} cod)
mlDirSlMorFromC {ar=(ppos ** pdir)}
  {dom=((dtot ** dproj) ** (donpos ** dondir))}
  {cod=((ctot ** cproj) ** (conpos ** condir))}
  (Element0 (monpos ** mondir) (Evidence0 opeq odeq)) =
    MDSM
      (\i, (Element0 j peq) => Element0 (monpos j) $ trans (sym $ opeq j) peq)
      (\i, (Element0 j peq), pd, (Element0 md deq) =>
        Element0 (mondir j md) $
          trans (odeq j md) $ rewrite sym (opeq j) in deq)

public export
mlPolySlMorToObj : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod -> MlPolySlObj ar
mlPolySlMorToObj {ar} {dom} {cod} =
  MlPolySlFromSlOfSl {ar} cod . mlPolySlMorToSlOfSl {ar}

public export
mlPolySlMorTot : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor {ar} dom cod -> PolyFunc
mlPolySlMorTot {ar} {dom} {cod} =
  mlPolySlObjTot {ar=(mlPolySlObjTot {ar} cod)} . mlPolySlMorToSlOfSl {ar}

public export
mlPolySlMorProj : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  (m : MlPolySlMor {ar} dom cod) ->
  PolyNatTrans (mlPolySlMorTot {ar} {dom} {cod} m) (mlPolySlObjTot {ar} cod)
mlPolySlMorProj {ar} {dom} {cod} m =
  mlPolySlObjProj {ar=(mlPolySlObjTot {ar} cod)} $ mlPolySlMorToSlOfSl {ar} m

public export
mlPolySlMorToP : {ar : MLArena} -> {dom, cod : MlPolySlObj ar} ->
  MlPolySlMor dom cod -> PFSliceMorph {p=ar} (mlPolySlObjToC ar cod)
mlPolySlMorToP {ar} {cod=cod@(MPSobj cpos cdir condir)} m =
  (mlPolySlMorTot {ar} {dom} {cod} m ** mlPolySlMorProj {ar} {dom} {cod} m)

public export
mlPolySlOfSlFromP : {ar : MLArena} -> {cod : MlPolySlObj ar} ->
  PFSliceMorph {p=ar} (mlPolySlObjToC ar cod) -> MlPolySlOfSl {ar} cod
mlPolySlOfSlFromP {ar} {cod=cod@(MPSobj _ _ _)} m =
  MPSobj
    (mlPolySlOnPosFromC {ar=(mlPolySlObjTot {ar} cod)} m)
    (mlPolySlDirFromC {ar=(mlPolySlObjTot {ar} cod)} m)
    (mlPolySlOnDirFromC {ar=(mlPolySlObjTot {ar} cod)} m)

public export
mlPolySlMorFromP : {ar : MLArena} -> {cod : MlPolySlObj ar} ->
  (m : PFSliceMorph {p=ar} (mlPolySlObjToC ar cod)) ->
  MlPolySlMor {ar}
    (MlPolySlFromSlOfSl {ar} cod $ mlPolySlOfSlFromP {ar} {cod} m)
    cod
mlPolySlMorFromP {ar} {cod} m = MPSM {ar} {cod} $ mlPolySlOfSlFromP {ar} {cod} m

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---- Slice categories of polynomial functors (in dependent-type style) ----
---------------------------------------------------------------------------
---------------------------------------------------------------------------

-- `PFCovarRepSliceObj x` is an object of the category of polynomial
-- functors sliced over the covariant representable represented by
-- `x`, i.e. `CovarHom x`, in a dependent-type (arena) style.
--
-- The position-set of a representable functor is the terminal object, so the
-- morphism component of a slice object (which in this case is a polynomial
-- natural transformation) is determined by a dependent on-directions function,
-- which for each position of the polynomial functor which comprises the object
-- component of the slice object (i.e. the domain of the morphism component)
-- maps the represented object to the direction-set at that position.
PFCovarRepSliceObj : Type -> Type
PFCovarRepSliceObj x = (p : PolyFunc ** (i : pfPos p) -> x -> pfDir {p} i)

-- A Dirichlet functor sliced over a contravariant representable
-- functor is a Dirichlet functor together with a Dirichlet natural
-- transformation from that functor to the arena whose position-set is
-- `Unit` and whose direction-set at its one position is the represented object.
DFContravarRepSliceObj : Type -> Type
DFContravarRepSliceObj x = (p : PolyFunc ** (i : pfPos p) -> pfDir {p} i -> x)

-- A slice over a coproduct is a product of slices.  So a slice object over
-- a polynomial functor is a product of slices over covariant representable
-- functors.
PFSliceObj'' : PolyFunc -> Type
PFSliceObj'' s = (si : pfPos s) -> PFCovarRepSliceObj (pfDir {p=s} si)

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
-- functor has no directions at the corresponding position).  In the
-- dependent-type view, therefore, we can separate the directions of the
-- dependent functors into two:  those which are mapped to by directions of
-- the functor being sliced over, whose targets within slice morphisms
-- (which are natural transformations between dependent polynomial functors)
-- are constrained by the commutativity requirement on directions of the
-- functor being sliced over to specific targets in the codomain of the
-- natural transformation underlying the slice morphism, and those whose
-- mappings under that natural transformation are unconstrained.  A practical
-- value of this split is that it avoids having to include an explicit
-- equality in the definition of the natural transformation underlying a
-- slice morphism -- the parts of it constrained by the equality are simply
-- not defined; we _define_ only the unconstrained part of the transformation.
--
-- There is also an intuitive interpretation of this split:  the pointed
-- (constrained) directions are _parameters_ to the dependent functors, while
-- the unconstrained directions are _arguments_.
PFSliceObjPos : PolyFunc -> Type
PFSliceObjPos (pos ** dir) = pos -> PolyFunc

PFSliceObjDir : (p : PolyFunc) -> PFSliceObjPos p -> Type
PFSliceObjDir (pos ** dir) spf = SliceMorphism {a=pos} dir (PFSection . spf)

PFSliceObjPF : PolyFunc -> PolyFunc
PFSliceObjPF p = (PFSliceObjPos p ** PFSliceObjDir p)

PFSliceObj : PolyFunc -> Type
PFSliceObj p = pfPDir $ PFSliceObjPF p

CPFSliceObjToPFS : (p : PolyFunc) -> CPFSliceObj p -> PFSliceObj p
CPFSliceObjToPFS (ppos ** pdir) ((qpos ** qdir) ** (onpos ** ondir)) =
  (\i : ppos => (PreImage onpos i ** \(Element0 j inpre) => qdir j) **
   \i : ppos, d : pdir i, (Element0 j inpre) => ondir j $ rewrite inpre in d)

CPFSliceObjFromPFS : (p : PolyFunc) -> PFSliceObj p -> CPFSliceObj p
CPFSliceObjFromPFS (ppos ** pdir) (psl ** m) =
  (((i : ppos ** fst (psl i)) ** \(i ** j) => snd (psl i) j) **
   (fst ** \(i ** j), d => m i d j))

PFBaseChange : {p, q : PolyFunc} ->
  DirichNatTrans q p -> PFSliceObj p -> PFSliceObj q
PFBaseChange {p=(ppos ** pdir)} {q=(qpos ** qdir)} (onpos ** ondir) (psl ** m) =
  (psl . onpos ** \qi, qd, pslp => m (onpos qi) (ondir qi qd) pslp)

PFBaseChange' : {p, q : PolyFunc} ->
  DirichNatTrans q p -> MlPolySlObj p -> MlPolySlObj q
PFBaseChange' {p=(ppos ** pdir)} {q=(qpos ** qdir)} (onpos ** ondir)
  (MPSobj slonpos sldir slondir) =
    MPSobj
      (slonpos . onpos)
      (\i, j => sldir (onpos i) j)
      (\i, j, qd => slondir (onpos i) j $ ondir i qd)

PFSliceSigma : (q : PolyFunc) -> {p : PolyFunc} ->
  PolyNatTrans p q -> PFSliceObj p -> PFSliceObj q
PFSliceSigma q {p} beta sl with (CPFSliceObjFromPFS p sl)
  PFSliceSigma q {p} beta sl | (r ** alpha) =
    let csigma = (r ** pntVCatComp beta alpha) in
    CPFSliceObjToPFS q csigma

PFSliceSigma' : (q : PolyFunc) -> {p : PolyFunc} ->
  PolyNatTrans p q -> MlPolySlObj p -> MlPolySlObj q
PFSliceSigma' q {p} beta sl with (mlPolySlObjToC p sl)
  PFSliceSigma' q {p} beta sl | (r ** alpha) =
    let csigma = (r ** pntVCatComp beta alpha) in
    mlPolySlObjFromC q csigma

-- A slice object over a constant functor is effectively a polynomial
-- functor parameterized over terms of the output type of the constant functor.
PFSliceOverConst : {x : Type} -> PFSliceObj (PFConstArena x) -> x -> PolyFunc
PFSliceOverConst {x} (psl ** m) ex =
  -- The arguments of `m` include a term of type `Void`, so
  -- it is impossible to apply (unless we find such a term, and
  -- hence a contradiction in our metalanguage).  Thus we can and
  -- must ignore it.
  --
  -- Put another way, `m` gives us no information, because its type
  -- restricts it to being effectively just the unique morphism out
  -- of the initial object.
  psl ex

-- A slice object over a constant functor is effectively a polynomial
-- functor parameterized over terms of the output type of the constant functor.
PFSliceOverConst' : {x : Type} -> MlPolySlObj (PFConstArena x) -> x -> PolyFunc
PFSliceOverConst' {x} (MPSobj onpos dir ondir) ex =
  -- The arguments of `m` include a term of type `Void`, so
  -- it is impossible to apply (unless we find such a term, and
  -- hence a contradiction in our metalanguage).  Thus we can and
  -- must ignore it.
  --
  -- Put another way, `m` gives us no information, because its type
  -- restricts it to being effectively just the unique morphism out
  -- of the initial object.
  (onpos ex ** \i => dir ex i)

-- A slice object over the terminal polynomial functor is effectively
-- just a polynomial functor, just as a slice of `Type` over `Unit` is
-- effectively just a type.
PFSliceOver1 : PFSliceObj PFTerminalArena -> PolyFunc
PFSliceOver1 psl = PFSliceOverConst {x=Unit} psl ()

-- A slice object over the terminal polynomial functor is effectively
-- just a polynomial functor, just as a slice of `Type` over `Unit` is
-- effectively just a type.
PFSliceOver1' : MlPolySlObj PFTerminalArena -> PolyFunc
PFSliceOver1' psl = PFSliceOverConst' {x=Unit} psl ()

PFAppI : {p : PolyFunc} ->
  {- these two parameters form an object of the category of elements of `p`
   - interpreted as a Dirichlet functor -}
  (ty : Type) -> (el : InterpDirichFunc p ty) ->
  PFSliceObj p -> PFSliceObj (PFHomArena ty)
PFAppI {p=p@(_ ** _)} ty (i ** d) =
  PFBaseChange {p} {q=(PFHomArena ty)} (\() => i ** \() => d)

PFAppI' : {p : PolyFunc} ->
  {- these two parameters form an object of the category of elements of `p`
   - interpreted as a Dirichlet functor -}
  (ty : Type) -> (el : InterpDirichFunc p ty) ->
  MlPolySlObj p -> MlPolySlObj (PFHomArena ty)
PFAppI' {p=p@(_ ** _)} ty (i ** d) =
  PFBaseChange' {p} {q=(PFHomArena ty)} (\() => i ** \() => d)

InterpPFSliceObj : {p : PolyFunc} ->
  MlPolySlObj p -> (ty : Type) -> SliceObj $ InterpPolyFunc p ty
InterpPFSliceObj {p} sl ty el with (mlPolySlObjToC p sl)
  InterpPFSliceObj {p} sl ty el | (q ** alpha) =
    PreImage {a=(InterpPolyFunc q ty)} {b=(InterpPolyFunc p ty)}
      (InterpPolyNT alpha ty) el

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
PFApp1 : {p : PolyFunc} -> pfPos p -> PFSliceObj p -> PolyFunc
PFApp1 {p=p@(pos ** dir)} i slp =
  PFSliceOver1 $ PFAppI {p} Void (i ** \v => void v) slp

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
PFApp1' : {p : PolyFunc} -> pfPos p -> MlPolySlObj p -> PolyFunc
PFApp1' {p=p@(pos ** dir)} i slp =
  PFSliceOver1' $ PFAppI' {p} Void (i ** \v => void v) slp

PNTFam : {pos : Type} -> {dir : pos -> Type} ->
  PFSliceObjPos (pos ** dir) -> PFSliceObj (pos ** dir) -> Type
PNTFam {pos} {dir} dom cod = (i : pos) -> PolyNatTrans (dom i) (fst cod i)

PFSliceMorphDomDir : {pos : Type} -> {dir : pos -> Type} ->
  (dom : PFSliceObjPos (pos ** dir)) -> (cod : PFSliceObj (pos ** dir)) ->
  PNTFam {pos} {dir} dom cod ->
  PFSliceObjDir (pos ** dir) dom
PFSliceMorphDomDir {pos} {dir} dom (codonpos ** codondir) ntfam i d j =
   let (onpos ** ondir) = ntfam i in ondir j $ codondir i d $ onpos j

data PFSliceMorph' : {pos : Type} -> {dir : pos -> Type} ->
    PFSliceObj (pos ** dir) -> PFSliceObj (pos ** dir) -> Type where
  PFSM' : {pos : Type} -> {dir : pos -> Type} ->
    (dom : PFSliceObjPos (pos ** dir)) -> (cod : PFSliceObj (pos ** dir)) ->
    (ntfam : PNTFam {pos} {dir} dom cod) ->
    PFSliceMorph' {pos} {dir}
      (dom ** PFSliceMorphDomDir {pos} {dir} dom cod ntfam) cod

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
