module LanguageDef.SlicePolyUMorph

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.InternalCat
import public LanguageDef.SlicePolyCat

------------------------------------------------
------------------------------------------------
---- Limits/colimits of polynomial functors ----
------------------------------------------------
------------------------------------------------

-- Limits and colimits are right and left adjoints respectively to
-- diagonal functors, forming an adjoint triple.
--
-- The following are not limits and colimits within categories of
-- polynomial functors.  Rather, they are limits and colimits within
-- slice categories, but specifically of slice-polynomial _diagrams_
-- (recall that diagrams are simply functors).

public export
SPFDdiagF : (a, b : Type) -> SliceObj b -> SPFData a b
SPFDdiagF a b sb = SPFD sb (\_, _, _ => Void)

public export
InterpSPFDdiagF : (a, b : Type) -> SliceObj b -> SliceFunctor a b
InterpSPFDdiagF a b sb = InterpSPFData $ SPFDdiagF a b sb

public export
InterpSPFDdiagFmap : {a, b : Type} ->
  (sb : SliceObj b) -> SliceFMap (InterpSPFDdiagF a b sb)
InterpSPFDdiagFmap {a} {b} sb = InterpSPFDataMap $ SPFDdiagF a b sb

public export
SPFDdiagToSDF : {a, b : Type} -> (sb : SliceObj b) -> (sa : SliceObj a) ->
  SliceMorphism {a=b} (InterpSPFDdiagF a b sb sa) (SliceDiagF {a} {b} sb sa)
SPFDdiagToSDF {a} {b} sb sa eb = DPair.fst

public export
SPFDdiagFromSDF : {a, b : Type} -> (sb : SliceObj b) -> (sa : SliceObj a) ->
  SliceMorphism {a=b} (SliceDiagF {a} {b} sb sa) (InterpSPFDdiagF a b sb sa)
SPFDdiagFromSDF {a} {b} sb sa eb esb = (esb ** \_, v => void v)

public export
spfdDiagFmap : {a, b : Type} ->
  IntFMapSig (SliceMor b) (SPFnt {dom=a} {cod=b}) (SPFDdiagF a b)
spfdDiagFmap {a} {b} sb sb' m = SPFDm m (\_, _, _, v => void v)

public export
SPFDdiagFSig : (a, b : Type) -> IntFunctorSig (SliceCat b) (SPFDcat a b)
SPFDdiagFSig a b = IFunctor (SPFDdiagF a b) (spfdDiagFmap {a} {b})

public export
SPFDColimit : {a, b : Type} -> SPFData a b -> SliceObj b
SPFDColimit {a} {b} = SliceFColimit {a} {b} . InterpSPFData {dom=a} {cod=b}

public export
spfdColimitMap : {a, b : Type} -> (f, g : SPFData a b) ->
  SPFnt {dom=a} {cod=b} f g ->
  SliceMorphism {a=b} (SPFDColimit f) (SPFDColimit g)
spfdColimitMap {a} {b} f g alpha =
  sliceFColimitMap {a} {b}
    (InterpSPFData f)
    (InterpSPFData g)
    (InterpSPFnt f g alpha)

public export
SPFDColimitFSig : (a, b : Type) -> IntFunctorSig (SPFDcat a b) (SliceCat b)
SPFDColimitFSig a b = IFunctor (SPFDColimit {a} {b}) (spfdColimitMap {a} {b})

public export
SPFDLimit : {a, b : Type} -> SPFData a b -> SliceObj b
SPFDLimit {a} {b} = SliceFLimit {a} {b} . InterpSPFData {dom=a} {cod=b}

public export
spfdLimitMap : {a, b : Type} -> (f, g : SPFData a b) ->
  SPFnt {dom=a} {cod=b} f g ->
  SliceMorphism {a=b} (SPFDLimit f) (SPFDLimit g)
spfdLimitMap {a} {b} f g alpha =
  sliceFLimitMap {a} {b}
    (InterpSPFData f)
    (InterpSPFData g)
    (InterpSPFnt f g alpha)

public export
SPFDLimitFSig : (a, b : Type) -> IntFunctorSig (SPFDcat a b) (SliceCat b)
SPFDLimitFSig a b = IFunctor (SPFDLimit {a} {b}) (spfdLimitMap {a} {b})

public export
SPFDColimitMonad : (a, b : Type) -> SPFData a b -> SPFData a b
SPFDColimitMonad a b = IntAdjMonad {c=(SPFData a b)} {d=(SliceObj b)}
  (SPFDColimit {a} {b}) (SPFDdiagF a b)

public export
SPFDColimitComonad : (a, b : Type) -> SliceEndofunctor b
SPFDColimitComonad a b = IntAdjComonad {c=(SPFData a b)} {d=(SliceObj b)}
  (SPFDColimit {a} {b}) (SPFDdiagF a b)

public export
SPFDLimitMonad : (a, b : Type) -> SliceEndofunctor b
SPFDLimitMonad a b = IntAdjMonad {c=(SliceObj b)} {d=(SPFData a b)}
  (SPFDdiagF a b) (SPFDLimit {a} {b})

public export
SPFDLimitComonad : (a, b : Type) -> SPFData a b -> SPFData a b
SPFDLimitComonad a b = IntAdjComonad {c=(SliceObj b)} {d=(SPFData a b)}
  (SPFDdiagF a b) (SPFDLimit {a} {b})

public export
SPFDColimitUnit : (a, b : Type) ->
  IntAdjUnitSig {c=(SPFData a b)} {d=(SliceObj b)}
    (SPFnt {dom=a} {cod=b}) (SPFDColimit {a} {b}) (SPFDdiagF a b)
SPFDColimitUnit a b f =
  SPFDm
    (\eb, ep => (spfdDir f eb ep ** ep ** \ea, efd => efd))
    (\_, _, _, v => void v)

public export
SPFDColimitCounit : (a, b : Type) ->
  IntAdjCounitSig {c=(SPFData a b)} {d=(SliceObj b)}
    (SliceMor b) (SPFDColimit {a} {b}) (SPFDdiagF a b)
SPFDColimitCounit a b x eb ex = DPair.fst $ DPair.snd ex

public export
SPFDLimitUnit : (a, b : Type) ->
  IntAdjUnitSig {c=(SliceObj b)} {d=(SPFData a b)}
    (SliceMor b) (SPFDdiagF a b) (SPFDLimit {a} {b})
SPFDLimitUnit a b sb eb esb sa = (esb ** \_, v => void v)

public export
SPFDLimitCounit : (a, b : Type) ->
  IntAdjCounitSig {c=(SliceObj b)} {d=(SPFData a b)}
    (SPFnt {dom=a} {cod=b}) (SPFDdiagF a b) (SPFDLimit {a} {b})
SPFDLimitCounit a b (SPFD pos dir) =
  SPFDm
    (\eb, sa => fst $ sa $ \ea => Void)
    (\eb, ep => snd $ ep $ \ea => Void)

public export
SPFDColimitAdjoints : (a, b : Type) ->
  IntAdjointsSig (SliceCat b) (SPFDcat a b)
SPFDColimitAdjoints a b =
  IAdjoints (SPFDColimitFSig a b) (SPFDdiagFSig a b)

public export
SPFDLimitAdjoints : (a, b : Type) ->
  IntAdjointsSig (SPFDcat a b) (SliceCat b)
SPFDLimitAdjoints a b =
  IAdjoints (SPFDdiagFSig a b) (SPFDLimitFSig a b)

public export
SPFDColimitUnits : (a, b : Type) ->
  IntUnitsSig (SPFDColimitAdjoints a b)
SPFDColimitUnits a b = IUnits (SPFDColimitUnit a b) (SPFDColimitCounit a b)

public export
SPFDLimitUnits : (a, b : Type) ->
  IntUnitsSig (SPFDLimitAdjoints a b)
SPFDLimitUnits a b = IUnits (SPFDLimitUnit a b) (SPFDLimitCounit a b)

public export
SPFDColimitAdj : (a, b : Type) ->
  IntAdjunctionSig (SliceCat b) (SPFDcat a b)
SPFDColimitAdj a b =
  IntAdjunctionFromUnits (SPFDColimitAdjoints a b) (SPFDColimitUnits a b)

public export
SPFDLimitAdj : (a, b : Type) ->
  IntAdjunctionSig (SPFDcat a b) (SliceCat b)
SPFDLimitAdj a b =
  IntAdjunctionFromUnits (SPFDLimitAdjoints a b) (SPFDLimitUnits a b)

public export
SPFDLimitColimitTripleAdjoints : (a, b : Type) ->
  IntTripleAdjointsSig (SPFDcat a b) (SliceCat b)
SPFDLimitColimitTripleAdjoints a b =
  ITripleAdjoints
    (SPFDColimitFSig a b)
    (SPFDdiagFSig a b)
    (SPFDLimitFSig a b)

public export
SPFDLimitTripleUnitsSig : (a, b : Type) ->
  ITAUnitsSig (SPFDLimitColimitTripleAdjoints a b)
SPFDLimitTripleUnitsSig a b =
  ITUnits
    (SPFDColimitUnits a b)
    (SPFDLimitUnits a b)

public export
SPFDLimitTripleAdjunctionSig : (a, b : Type) ->
  ITASig (SPFDcat a b) (SliceCat b)
SPFDLimitTripleAdjunctionSig a b =
  ITAFromUnits
    (SPFDLimitColimitTripleAdjoints a b)
    (SPFDLimitTripleUnitsSig a b)

------------------------
------------------------
---- Representables ----
------------------------
------------------------

-- An `SPFData dom cod` whose position is `const Unit` and whose direction
-- is `const x` for some `x : SliceObj dom` is the `cod`-way product of the
-- covariant representable hom-functor of `x`.
public export
SPFDataRep : {dom : Type} -> SliceObj dom -> (cod : Type) -> SPFData dom cod
SPFDataRep {dom} x cod = SPFD (\_ => Unit) (\_, _ => x)

public export
sliceCovarHom : {dom : Type} ->
  SliceObj dom -> (cod : Type) -> SliceFunctor dom cod
sliceCovarHom {dom} x cod y ec = SliceMorphism {a=dom} x y

public export
spfdRepToHom : {dom, cod : Type} -> {x : SliceObj dom} ->
  SliceNatTrans {x=dom} {y=cod}
    (InterpSPFData {dom} {cod} $ SPFDataRep {dom} x cod)
    (sliceCovarHom {dom} x cod)
spfdRepToHom {dom} {cod} {x} y ec = snd

public export
spfdRepFromHom : {dom, cod : Type} -> {x : SliceObj dom} ->
  SliceNatTrans {x=dom} {y=cod}
    (sliceCovarHom {dom} x cod)
    (InterpSPFData {dom} {cod} $ SPFDataRep {dom} x cod)
spfdRepFromHom {dom} {cod} {x} y ec = MkDPair ()

-- The slice polynomial functor represented by the terminal object is
-- a generalization of the (non-dependent) identity in the sense that it
-- coincides with the identity when `dom` and `cod` are `Unit`.
-- (See `SPFDPiFRtoId` below for the full dependent generalization of the
-- identity.)

public export
SPFDRepTerminal : (dom, cod : Type) -> SPFData dom cod
SPFDRepTerminal dom cod = SPFDataRep {dom} (SliceObjTerminal dom) cod

public export
SPFDRepTerminalToId :
  SPFnt {dom=Unit} {cod=Unit} (SPFDRepTerminal Unit Unit) (SPFDid Unit)
SPFDRepTerminalToId = SPFDm (\_ => id) (\_, _, _, _ => ())

public export
SPFDRepTerminalFromId :
  SPFnt {dom=Unit} {cod=Unit} (SPFDid Unit) (SPFDRepTerminal Unit Unit)
SPFDRepTerminalFromId = SPFDm (\_ => id) (\(), (), (), () => Refl)

-- More generally, a slice polynomial functor whose position is `const Unit`
-- is equivalent to a `SliceSigmaPiFR` -- that is, a base change followed
-- by a pi, with no sigma involved.  In that sense, it is a generalization
-- of representables.
public export
spfdPiFR : {x, y : Type} -> SliceObj (x, y) -> SPFData x y
spfdPiFR {x} {y} sl = SPFD (\_ => Unit) (\ec, u, ed => sl (ed, ec))

public export
SPFDuPosToPiFR : {x, y : Type} -> (sl : SliceObj (x, y)) ->
  SliceNatTrans {x} {y}
    (InterpSPFData {dom=x} {cod=y} $ spfdPiFR {x} {y} sl)
    (SliceSigmaPiFR {c=x} {e=y} sl)
SPFDuPosToPiFR {x} {y} sl sd ec m ex = snd m (fst ex) (snd ex)

public export
SPFDuPosFromPiFR : {x, y : Type} -> (sl : SliceObj (x, y)) ->
  SliceNatTrans {x} {y}
    (SliceSigmaPiFR {c=x} {e=y} sl)
    (InterpSPFData {dom=x} {cod=y} $ spfdPiFR {x} {y} sl)
SPFDuPosFromPiFR {x} {y} sl sd ey m = (() ** \ex, esl => m (ex ** esl))

-- `SliceSigmaPiFR` of `WDiagElem` is the identity.
public export
SPFDPiFRtoId : (x : Type) ->
  SPFnt {dom=x} {cod=x} (spfdPiFR {x} {y=x} $ WDiagElem {a=x}) (SPFDid x)
SPFDPiFRtoId x = SPFDm (\_, _ => ()) (\ex, u, ex', Refl => SFS ex ())

public export
SPFDPiFRfromId : (x : Type) ->
  SPFnt {dom=x} {cod=x} (SPFDid x) (spfdPiFR {x} {y=x} $ WDiagElem {a=x})
SPFDPiFRfromId x = SPFDm (\_, _ => ()) (\ex, (), ex', (SFS ex ()) => Refl)

-- Dually, a slice polynomial functor whose direction is just a diagonalization
-- (an identity type) is equivalent to a `SliceSigmaPiFL` -- that is, a base
-- change followed by a sigma, with no pi involved.  In that sense, it is a
-- sum of products, with no function types.  It is left adjoint to `spfdPiFR`.
public export
spfdPiFL : {x, y : Type} -> SliceObj (x, y) -> SPFData y x
spfdPiFL {x} {y} sl =
  SPFD
    (\ex => (ey : y ** sl (ex, ey)))
    (\ex, ep, ey => fst ep = ey)

public export
SPFDuPosToPiFL : {x, y : Type} -> (sl : SliceObj (x, y)) ->
  SliceNatTrans {x=y} {y=x}
    (InterpSPFData {dom=y} {cod=x} $ spfdPiFL {x} {y} sl)
    (SliceSigmaPiFL {c=x} {e=y} sl)
SPFDuPosToPiFL {x} {y} sl sd ec =
  dpMapSnd $ \esl, m => m (fst esl) Refl

public export
SPFDuPosFromPiFL : {x, y : Type} -> (sl : SliceObj (x, y)) ->
  SliceNatTrans {x=y} {y=x}
    (SliceSigmaPiFL {c=x} {e=y} sl)
    (InterpSPFData {dom=y} {cod=x} $ spfdPiFL {x} {y} sl)
SPFDuPosFromPiFL {x} {y} sl sd ec =
  dpMapSnd $ \esl, esd, ey, eqy => rewrite sym eqy in esd

-------------------
-------------------
---- Constants ----
-------------------
-------------------

-- An `SPFData` with no directions is a constant.

public export
SPFDataConst : (dom : Type) -> {cod : Type} -> SliceObj cod -> SPFData dom cod
SPFDataConst dom {cod} x = SPFD x (\_, _, _ => Void)

public export
spfdConstToConst : (dom : Type) -> {cod : Type} -> (x : SliceObj cod) ->
  SliceNatTrans {x=dom} {y=cod}
    (InterpSPFData {dom} {cod} $ SPFDataConst dom {cod} x)
    (const x)
spfdConstToConst dom {cod} x sd ec = fst

public export
spfdConstFromConst : (dom : Type) -> {cod : Type} -> (x : SliceObj cod) ->
  SliceNatTrans {x=dom} {y=cod}
    (const x)
    (InterpSPFData {dom} {cod} $ SPFDataConst dom {cod} x)
spfdConstFromConst dom {cod} x sd ec ex = (ex ** \_, v => void v)

---------------------
---------------------
---- Set product ----
---------------------
---------------------

-- We can take a set product _within_ a single polynomial-functor category
-- by multiplying the output of the cross-category (family) product.
public export
spfdSetProduct : {b, dom, cod : Type} ->
  (b -> SPFData dom cod) -> SPFData dom cod
spfdSetProduct {b} {dom} {cod} =
  spfdPostcompPi snd . SPFDataFamToProd {b} {dom} {cod}

public export
spfdSetProductIntro : {b, dom, cod : Type} ->
  {x : SPFData dom cod} -> {y : b -> SPFData dom cod} ->
  ((eb : b) -> SPFnt {dom} {cod} x (y eb)) ->
  SPFnt {dom} {cod} x (spfdSetProduct {b} {dom} {cod} y)
spfdSetProductIntro {b} {dom} {cod} {x} {y} ntf =
  SPFDm
    (\ec, ep =>
      (() **
       \ebc, eceq => case ebc of
        (eb, ec') => case eceq of Refl => spOnPos (ntf eb) ec ep))
    (\ec, ep, ed, ebdm => case ebdm of
      (((eb, ec') ** eceq) ** dm) =>
        case eceq of Refl => spOnDir (ntf eb) ec ep ed dm)

public export
spfdSetProductProj : {b, dom, cod : Type} ->
  (sf : b -> SPFData dom cod) -> (eb : b) ->
  SPFnt {dom} {cod} (spfdSetProduct {b} {dom} {cod} sf) (sf eb)
spfdSetProductProj {b} {dom} {cod} sf eb =
  SPFDm
    (\ec, ebc => snd ebc (eb, ec) Refl)
    (\ec, dm, ed, efd => (((eb, ec) ** Refl) ** efd))

-----------------------
-----------------------
---- Set coproduct ----
-----------------------
-----------------------

-- We can take a set coproduct _within_ a single polynomial-functor category
-- by summing the output of the cross-category (family) product.
public export
spfdSetCoproduct : {b, dom, cod : Type} ->
  (b -> SPFData dom cod) -> SPFData dom cod
spfdSetCoproduct {b} {dom} {cod} =
  spfdPostcompSigma snd . SPFDataFamToProd {b} {dom} {cod}

public export
spfdSetCoproductInj : {b, dom, cod : Type} ->
  (sf : b -> SPFData dom cod) -> (eb : b) ->
  SPFnt {dom} {cod} (sf eb) (spfdSetCoproduct {b} {dom} {cod} sf)
spfdSetCoproductInj {b} {dom} {cod} sf eb =
  SPFDm
    (\ec, ep =>
      (SFS (eb, ec) () **
       \ebc, eceq => case ebc of (eb, ec') => case eceq of Refl => ep))
    (\ec, ep, ed, ebcd => case ebcd of
      (((eb, ec) ** Refl) ** efd) => efd)

public export
spfdSetCoproductElim : {b, dom, cod : Type} ->
  {x : b -> SPFData dom cod} -> {y : SPFData dom cod} ->
  ((eb : b) -> SPFnt {dom} {cod} (x eb) y) ->
  SPFnt {dom} {cod} (spfdSetCoproduct {b} {dom} {cod} x) y
spfdSetCoproductElim {b} {dom} {cod} {x} {y} ntf =
  SPFDm
    (\ec, ep => case ep of
      (SFS (eb, ec) () ** epm) => spOnPos (ntf eb) ec $ epm (eb, ec) Refl)
    (\ec, ep, ed, efd => case ep of
      (SFS (eb, ec) () ** epm) =>
        (((eb, ec) ** Refl) ** spOnDir (ntf eb) ec (epm (eb, ec) Refl) ed efd))

------------------------------
------------------------------
---- Set parallel product ----
------------------------------
------------------------------

public export
spfdSetParProductPos : {b, dom, cod : Type} ->
  (b -> SPFData dom cod) -> SliceObj cod
spfdSetParProductPos {b} {dom} {cod} sf ec =
  Pi {a=b} $ \eb => spfdPos (sf eb) ec

public export
spfdSetParProductDir : {b, dom, cod : Type} ->
  (sf : b -> SPFData dom cod) ->
  SPFdirType dom cod (spfdSetParProductPos {b} {dom} {cod} sf)
spfdSetParProductDir {b} {dom} {cod} sf ec ep ed =
  Pi {a=b} $ \eb => spfdDir (sf eb) ec (ep eb) ed

public export
spfdSetParProduct : {b, dom, cod : Type} ->
  (b -> SPFData dom cod) -> SPFData dom cod
spfdSetParProduct {b} {dom} {cod} sf =
  SPFD
    (spfdSetParProductPos {b} {dom} {cod} sf)
    (spfdSetParProductDir {b} {dom} {cod} sf)

public export
spfdSetParProductNT : {b, dom, cod : Type} ->
  {sf, sf' : b -> SPFData dom cod} ->
  ((eb : b) -> SPFnt {dom} {cod} (sf eb) (sf' eb)) ->
  SPFnt {dom} {cod}
    (spfdSetParProduct {b} {dom} {cod} sf)
    (spfdSetParProduct {b} {dom} {cod} sf')
spfdSetParProductNT {b} {dom} {cod} {sf} {sf'} ntf =
  SPFDm
    (\ec, ep, eb => spOnPos (ntf eb) ec (ep eb))
    (\ec, ep, ed, efd', eb => spOnDir (ntf eb) ec (ep eb) ed (efd' eb))

-------------------------
-------------------------
---- Terminal object ----
-------------------------
-------------------------

-- A zero-way product is a terminal object.
public export
spfdTerminal : (dom, cod : Type) -> SPFData dom cod
spfdTerminal dom cod = spfdSetProduct {b=Void} {dom} {cod} $ \v => void v

public export
spfdToTerminal : {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> SPFnt {dom} {cod} spfd (spfdTerminal dom cod)
spfdToTerminal {dom} {cod} spfd =
  spfdSetProductIntro {b=Void} {dom} {cod} {x=spfd} {y=(\v => void v)} $
    \v => void v

------------------------
------------------------
---- Initial object ----
------------------------
------------------------

-- A zero-way coproduct is an initial object.
public export
spfdInitial : (dom, cod : Type) -> SPFData dom cod
spfdInitial dom cod = spfdSetCoproduct {b=Void} {dom} {cod} $ \v => void v

public export
spfdFromInitial : {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> SPFnt {dom} {cod} (spfdInitial dom cod) spfd
spfdFromInitial {dom} {cod} spfd =
  spfdSetCoproductElim {b=Void} {dom} {cod} {x=(\v => void v)} {y=spfd} $
    \v => void v

-----------------------------------------------
-----------------------------------------------
---- `SPFDRepTerminal` as parallel product ----
-----------------------------------------------
-----------------------------------------------

-- A zero-way parallel product is an `SPFDRepTerminal`.
public export
spfdEmptyParProductToRepTerminal : (dom, cod : Type) ->
  SPFnt {dom} {cod}
    (spfdSetParProduct {b=Void} {dom} {cod} $ \v => void v)
    (SPFDRepTerminal dom cod)
spfdEmptyParProductToRepTerminal dom cod =
  SPFDm (\_, _ => ()) (\ec, ep, ed, esl, v => void v)

public export
spfdEmptyParProductFromRepTerminal : (dom, cod : Type) ->
  SPFnt {dom} {cod}
    (SPFDRepTerminal dom cod)
    (spfdSetParProduct {b=Void} {dom} {cod} $ \v => void v)
spfdEmptyParProductFromRepTerminal dom cod =
  SPFDm (\_, _, v => void v) (\ec, u, ed, efd => ())

-------------------------
-------------------------
---- Binary products ----
-------------------------
-------------------------

-- A binary product is a set product indexed by a type of cardinality two.

public export
spfdProduct : {dom, cod : Type} ->
  SPFData dom cod -> SPFData dom cod -> SPFData dom cod
spfdProduct {dom} {cod} x y =
  spfdSetProduct {b=(Fin 2)} {dom} {cod} $ flip index [x, y]

public export
spfdProductIntro : {dom, cod : Type} ->
  {x, y, z : SPFData dom cod} ->
  SPFnt {dom} {cod} x y ->
  SPFnt {dom} {cod} x z ->
  SPFnt {dom} {cod} x (spfdProduct {dom} {cod} y z)
spfdProductIntro {dom} {cod} {x} {y} f g =
  spfdSetProductIntro {b=(Fin 2)} {dom} {cod} {x} {y=(flip index [y, z])} $
    \i => case i of FZ => f ; FS FZ => g

public export
spfdProductProj1 : {dom, cod : Type} -> (x, y : SPFData dom cod) ->
  SPFnt {dom} {cod} (spfdProduct {dom} {cod} x y) x
spfdProductProj1 {dom} {cod} x y =
  spfdSetProductProj {b=(Fin 2)} {dom} {cod} (flip index [x, y]) FZ

public export
spfdProductProj2 : {dom, cod : Type} -> (x, y : SPFData dom cod) ->
  SPFnt {dom} {cod} (spfdProduct {dom} {cod} x y) y
spfdProductProj2 {dom} {cod} x y =
  spfdSetProductProj {b=(Fin 2)} {dom} {cod} (flip index [x, y]) (FS FZ)

-- `spfdTerminal` (the zero-way product) is a unit for the product.

public export
spfdProductToUnitL : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    spfd
    (spfdProduct {dom} {cod} (spfdTerminal dom cod) spfd)
spfdProductToUnitL {dom} {cod} spfd =
  SPFDm
    (\ec, ep =>
      (() ** \(i, ec), Refl => case i of
        FZ => (() ** \(v, _) => void v)
        FS FZ => ep))
    (\ec, ep, ed, (((i, ec) ** Refl) ** efd) => case i of
      FZ => void $ fst $ fst $ fst efd
      FS FZ => efd)

public export
spfdProductToUnitR : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    spfd
    (spfdProduct {dom} {cod} spfd (spfdTerminal dom cod))
spfdProductToUnitR {dom} {cod} spfd =
  SPFDm
    (\ec, ep =>
      (() ** \(i, ec), Refl => case i of
        FZ => ep
        FS FZ => (() ** \(v, _) => void v)))
    (\ec, ep, ed, (((i, ec) ** Refl) ** efd) => case i of
      FZ => efd
      FS FZ => void $ fst $ fst $ fst efd)

public export
spfdProductFromUnitL : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    (spfdProduct {dom} {cod} (spfdTerminal dom cod) spfd)
    spfd
spfdProductFromUnitL {dom} {cod} spfd =
  SPFDm
    (\ec, (() ** m) => m (FS FZ, ec) Refl)
    (\ec, (() ** m), ed, efd => (((FS FZ, ec) ** Refl) ** efd))

public export
spfdProductFromUnitR : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    (spfdProduct {dom} {cod} spfd (spfdTerminal dom cod))
    spfd
spfdProductFromUnitR {dom} {cod} spfd =
  SPFDm
    (\ec, (() ** m) => m (FZ, ec) Refl)
    (\ec, (() ** m), ed, efd => (((FZ, ec) ** Refl) ** efd))

---------------------------
---------------------------
---- Binary coproducts ----
---------------------------
---------------------------

-- A binary coproduct is a set coproduct indexed by a type of cardinality two.

public export
spfdCoproduct : {dom, cod : Type} ->
  SPFData dom cod -> SPFData dom cod -> SPFData dom cod
spfdCoproduct {dom} {cod} x y =
  spfdSetCoproduct {b=(Fin 2)} {dom} {cod} $ flip index [x, y]

public export
spfdCoproductInjL : {dom, cod : Type} -> (x, y : SPFData dom cod) ->
  SPFnt {dom} {cod} x (spfdCoproduct {dom} {cod} x y)
spfdCoproductInjL {dom} {cod} x y =
  spfdSetCoproductInj {b=(Fin 2)} {dom} {cod} (flip index [x, y]) FZ

public export
spfdCoproductInjR : {dom, cod : Type} -> (x, y : SPFData dom cod) ->
  SPFnt {dom} {cod} y (spfdCoproduct {dom} {cod} x y)
spfdCoproductInjR {dom} {cod} x y =
  spfdSetCoproductInj {b=(Fin 2)} {dom} {cod} (flip index [x, y]) (FS FZ)

public export
spfdCoproductElim : {dom, cod : Type} ->
  {x, y, z : SPFData dom cod} ->
  SPFnt {dom} {cod} x z ->
  SPFnt {dom} {cod} y z ->
  SPFnt {dom} {cod} (spfdCoproduct {dom} {cod} x y) z
spfdCoproductElim {dom} {cod} {x} {y} f g =
  spfdSetCoproductElim {b=(Fin 2)} {dom} {cod} {x=(flip index [x, y])} {y=z} $
    \i => case i of FZ => f ; FS FZ => g

-- `spfdInitial` (the zero-way coproduct) is a unit for the coproduct.

public export
spfdCoproductToUnitL : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    spfd
    (spfdCoproduct {dom} {cod} (spfdInitial dom cod) spfd)
spfdCoproductToUnitL {dom} {cod} spfd =
  SPFDm
    (\ec, ep =>
      (SFS (FS FZ, ec) () **
       \iec', eqc => case iec' of (i, ec') => case eqc of Refl => ep))
    (\ec, ep, ed, (((FS FZ, ec) ** Refl) ** efd) => efd)

public export
spfdCoproductToUnitR : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    spfd
    (spfdCoproduct {dom} {cod} spfd (spfdInitial dom cod))
spfdCoproductToUnitR {dom} {cod} spfd =
  SPFDm
    (\ec, ep =>
      (SFS (FZ, ec) () **
       \iec', eqc => case iec' of (i, ec') => case eqc of Refl => ep))
    (\ec, ep, ed, (((FZ, ec) ** Refl) ** efd) => efd)

public export
spfdCoproductFromUnitL : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    (spfdCoproduct {dom} {cod} (spfdInitial dom cod) spfd)
    spfd
spfdCoproductFromUnitL {dom} {cod} spfd =
  SPFDm
    (\ec, (SFS (i, ec) () ** dm) =>
      let efd = dm (i, ec) Refl in
      case i of
        FZ => case efd of (SFS (v, ec') () ** ep) => void v
        FS FZ => efd)
    (\ec, (SFS (i, ec) () ** dm), ed, efd =>
      (((i, ec) ** Refl) **
       case i of
        FZ => case (dm (i, ec) Refl) of (SFS (v, ec') () ** ep) => void v
        FS FZ => efd))

public export
spfdCoproductFromUnitR : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    (spfdCoproduct {dom} {cod} spfd (spfdInitial dom cod))
    spfd
spfdCoproductFromUnitR {dom} {cod} spfd =
  SPFDm
    (\ec, (SFS (i, ec) () ** dm) =>
      let efd = dm (i, ec) Refl in
      case i of
        FZ => efd
        FS FZ => case efd of (SFS (v, ec') () ** ep) => void v)
    (\ec, (SFS (i, ec) () ** dm), ed, efd =>
      (((i, ec) ** Refl) **
       case i of
        FZ => efd
        FS FZ => case (dm (i, ec) Refl) of (SFS (v, ec') () ** ep) => void v))

----------------------------------
----------------------------------
---- Binary parallel products ----
----------------------------------
----------------------------------

-- A binary parallel product is a set parallel product indexed by a type of
-- cardinality two.

public export
spfdParProduct : {dom, cod : Type} ->
  SPFData dom cod -> SPFData dom cod -> SPFData dom cod
spfdParProduct {dom} {cod} x y =
  spfdSetParProduct {b=(Fin 2)} {dom} {cod} $ flip index [x, y]

public export
spfdParProductNT : {dom, cod : Type} ->
  {p, p', q, q' : SPFData dom cod} ->
  SPFnt {dom} {cod} p p' ->
  SPFnt {dom} {cod} q q' ->
  SPFnt {dom} {cod}
    (spfdParProduct {dom} {cod} p q)
    (spfdParProduct {dom} {cod} p' q')
spfdParProductNT {dom} {cod} {p} {p'} {q} {q'} f g =
  spfdSetParProductNT {b=(Fin 2)} {dom} {cod}
    {sf=(flip index [p, q])} {sf'=(flip index [p', q'])} $
    \i => case i of FZ => f ; FS FZ => g

-- `SPFDRepTerminal` (the zero-way parallel product) is a unit for
-- the parallel product.

public export
spfdParProductToUnitL : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    spfd
    (spfdParProduct {dom} {cod} (SPFDRepTerminal dom cod) spfd)
spfdParProductToUnitL {dom} {cod} spfd =
  SPFDm
    (\ec, ep, i => case i of FZ => () ; FS FZ => ep)
    (\ec, ep, d, efd => efd (FS FZ))

public export
spfdParProductToUnitR : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    spfd
    (spfdParProduct {dom} {cod} spfd (SPFDRepTerminal dom cod))
spfdParProductToUnitR {dom} {cod} spfd =
  SPFDm
    (\ec, ep, i => case i of FZ => ep ; FS FZ => ())
    (\ec, ep, d, efd => efd FZ)

public export
spfdParProductFromUnitL : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    (spfdParProduct {dom} {cod} (SPFDRepTerminal dom cod) spfd)
    spfd
spfdParProductFromUnitL {dom} {cod} spfd =
  SPFDm
    (\ec, ep => ep (FS FZ))
    (\ec, ep, ed, efd, i => case i of FZ => () ; FS FZ => efd)

public export
spfdParProductFromUnitR : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    (spfdParProduct {dom} {cod} spfd (SPFDRepTerminal dom cod))
    spfd
spfdParProductFromUnitR {dom} {cod} spfd =
  SPFDm
    (\ec, ep => ep FZ)
    (\ec, ep, ed, efd, i => case i of FZ => efd ; FS FZ => ())

---------------------------------------
---------------------------------------
---- Utility (composite) morphisms ----
---------------------------------------
---------------------------------------

-- This section consists not of universal morphisms but of composites of
-- them which may be frequently useful.

-- Given an object `A`, this functor takes `Y -> Either A Y`.
public export
spfdEither : {w : Type} -> SliceObj w -> SPFData w w
spfdEither {w} a = spfdCoproduct {dom=w} {cod=w} (SPFDataConst w a) (SPFDid w)

-- Given an object `A`, this functor takes `Y -> Pair A Y`.
public export
spfdPair : {w : Type} -> SliceObj w -> SPFData w w
spfdPair {w} a = spfdProduct {dom=w} {cod=w} (SPFDataConst w a) (SPFDid w)

public export
spfdMaybe : (w : Type) -> SPFData w w
spfdMaybe w = spfdEither {w} (SliceObjTerminal w)

----------------------------
----------------------------
---- Left Kan extension ----
----------------------------
----------------------------

-- Left Kan extension is left adjoint to precomposition.  As such
-- we may also call it a "left coclosure" operation for the composition
-- product.

public export
spfdLKanExtPos : {a, b, c : Type} ->
  SPFData a c -> SPFData a b -> SliceObj b
spfdLKanExtPos {a} {b} {c} q p = spfdPos p

public export
spfdLKanExtDir : {a, b, c : Type} ->
  (q : SPFData a c) -> (p : SPFData a b) ->
  SPFdirType c b (spfdLKanExtPos {a} {b} {c} q p)
spfdLKanExtDir {a} {b} {c} q p eb ep =
  InterpSPFData {dom=a} {cod=c} q $ spfdDir {dom=a} {cod=b} p eb ep

public export
spfdLKanExt : {a, b, c : Type} ->
  SPFData a c -> SPFData a b -> SPFData c b
spfdLKanExt {a} {b} {c} q p =
  SPFD (spfdLKanExtPos {a} {b} {c} q p) (spfdLKanExtDir {a} {b} {c} q p)

public export
spfdLKanExtL : {a, b, c : Type} -> (q : SPFData a c) ->
  SPFData a b -> SPFData c b
spfdLKanExtL = spfdLKanExt

public export
spfdLKanExtR : {a, b, c : Type} -> (q : SPFData a c) ->
  SPFData c b -> SPFData a b
spfdLKanExtR {a} {b} {c} = flip $ SPFDcomp a c b

public export
spfdLKanExtLAdjPos : {a, b, c : Type} ->
  (p : SPFData a b) -> (q : SPFData a c) -> (r : SPFData c b) ->
  SPFnt {dom=c} {cod=b} (spfdLKanExtL q p) r ->
  SPFntPos {dom=a} {cod=b} p (spfdLKanExtR q r)
spfdLKanExtLAdjPos {a} {b} {c} p q r alpha eb ep =
  (spOnPos alpha eb ep ** \ec => DPair.fst . spOnDir alpha eb ep ec)

public export
spfdLKanExtLAdjDir : {a, b, c : Type} ->
  (p : SPFData a b) -> (q : SPFData a c) -> (r : SPFData c b) ->
  (alpha : SPFnt {dom=c} {cod=b} (spfdLKanExtL q p) r) ->
  SPFntDir {dom=a} {cod=b}
    p
    (spfdLKanExtR q r)
    (spfdLKanExtLAdjPos p q r alpha)
spfdLKanExtLAdjDir {a} {b} {c} p q r alpha eb ep ea rqd =
  snd (spOnDir alpha eb ep (fst $ fst rqd) (snd $ fst rqd)) ea (snd rqd)

public export
spfdLKanExtLAdj : {a, b, c : Type} ->
  (p : SPFData a b) -> (q : SPFData a c) -> (r : SPFData c b) ->
  SPFnt {dom=c} {cod=b} (spfdLKanExtL q p) r ->
  SPFnt {dom=a} {cod=b} p (spfdLKanExtR q r)
spfdLKanExtLAdj {a} {b} {c} p q r alpha =
  SPFDm
    (spfdLKanExtLAdjPos {a} {b} {c} p q r alpha)
    (spfdLKanExtLAdjDir {a} {b} {c} p q r alpha)

public export
spfdLKanExtRAdjPos : {a, b, c : Type} ->
  (p : SPFData a b) -> (q : SPFData a c) -> (r : SPFData c b) ->
  SPFnt {dom=a} {cod=b} p (spfdLKanExtR q r) ->
  SPFntPos {dom=c} {cod=b} (spfdLKanExtL q p) r
spfdLKanExtRAdjPos {a} {b} {c} p q r alpha eb ep = fst $ spOnPos alpha eb ep

public export
spfdLKanExtRAdjDir : {a, b, c : Type} ->
  (p : SPFData a b) -> (q : SPFData a c) -> (r : SPFData c b) ->
  (alpha : SPFnt {dom=a} {cod=b} p (spfdLKanExtR q r)) ->
  SPFntDir {dom=c} {cod=b}
    (spfdLKanExtL q p)
    r
    (spfdLKanExtRAdjPos p q r alpha)
spfdLKanExtRAdjDir {a} {b} {c} p q r alpha eb ep ec rd =
  (snd (spOnPos alpha eb ep) ec rd **
   \ea, qd =>
    spOnDir alpha eb ep ea ((ec ** rd) ** qd))

public export
spfdLKanExtRAdj : {a, b, c : Type} ->
  (p : SPFData a b) -> (q : SPFData a c) -> (r : SPFData c b) ->
  SPFnt {dom=a} {cod=b} p (spfdLKanExtR q r) ->
  SPFnt {dom=c} {cod=b} (spfdLKanExtL q p) r
spfdLKanExtRAdj {a} {b} {c} p q r alpha =
  SPFDm
    (spfdLKanExtRAdjPos {a} {b} {c} p q r alpha)
    (spfdLKanExtRAdjDir {a} {b} {c} p q r alpha)

---------------------
---------------------
---- Hom-objects ----
---------------------
---------------------

public export
spfdHomObj : {dom, cod : Type} ->
  SPFData dom cod -> SPFData dom cod -> SPFData dom cod
spfdHomObj {dom} {cod} q r =
  spfdSetProduct {b=(Sigma {a=cod} $ spfdPos q)} {dom} {cod} $
    \ep => SPFDcomp dom dom cod r $
      spfdCoproduct {dom} {cod=dom}
        (SPFDid dom)
        (SPFDataConst dom {cod=dom} $ uncurry (spfdDir q) ep)

public export
spfdHomObjPos : {dom, cod : Type} ->
  SPFData dom cod -> SPFData dom cod -> SliceObj cod
spfdHomObjPos {dom} {cod} p q = spfdPos (spfdHomObj {dom} {cod} p q)

public export
spfdHomObjDir : {dom, cod : Type} ->
  (p, q : SPFData dom cod) ->
  SPFdirType dom cod (spfdHomObjPos {dom} {cod} p q)
spfdHomObjDir {dom} {cod} p q = spfdDir (spfdHomObj {dom} {cod} p q)

----------------------------------
----------------------------------
---- Parallel product closure ----
----------------------------------
----------------------------------

-- We call this the "parallel closure" since it is a closure of the
-- parallel product in the same way (i.e. with the same universal-morphism
-- signatures) that the exponential object is a closure of the product.
public export
spfdParClosureObj : {dom, cod : Type} ->
  SPFData dom cod -> SPFData dom cod -> SPFData dom cod
spfdParClosureObj {dom} {cod} q r =
  spfdSetProduct {b=(Sigma {a=cod} $ spfdPos q)} {dom} {cod} $
    \ep => SPFDcomp dom dom cod r $
      spfdProduct {dom} {cod=dom}
        (SPFDid dom)
        (SPFDataConst dom {cod=dom} $ uncurry (spfdDir q) ep)

public export
spfdParClosureObjPos : {dom, cod : Type} ->
  SPFData dom cod -> SPFData dom cod -> SliceObj cod
spfdParClosureObjPos {dom} {cod} p q =
  spfdPos (spfdParClosureObj {dom} {cod} p q)

public export
spfdParClosureObjDir : {dom, cod : Type} ->
  (p, q : SPFData dom cod) ->
  SPFdirType dom cod (spfdParClosureObjPos {dom} {cod} p q)
spfdParClosureObjDir {dom} {cod} p q =
  spfdDir (spfdParClosureObj {dom} {cod} p q)

------------------------------------------------
------------------------------------------------
---- Universal slice polynomial 2-morphisms ----
------------------------------------------------
------------------------------------------------

-- Here we define universal objects in the category of all slice
-- polynomial functors, where the universal morphisms are
-- 2-morphisms, also known as cells.
--
-- Note that a universal object in the category of slice polynomial
-- functors between some fixed domain and codomain slice categories
-- is a special case of a universal object in the category of all
-- slice polynomial functors, where the vertical sides of the cell
-- are both identities.
