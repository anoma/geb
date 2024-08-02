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
spfdCoprPiFR : {x : Type} -> SliceObj x -> SPFData x Unit
spfdCoprPiFR {x} sl = spfdPiFR {x} {y=Unit} (sl . fst)

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
spfdCoprPiFL : {x : Type} -> SliceObj x -> SPFData x Unit
spfdCoprPiFL {x} sl = spfdPiFL {x=Unit} {y=x} (sl . snd)

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

public export
spfdLKanFromPoly : {a, b, c : Type} ->
  (q : SPFData a c) -> (p : SPFData a b) ->
  SliceNatTrans {x=c} {y=b}
    (InterpSPFData {dom=c} {cod=b} $ spfdLKanExt q p)
    (SliceLKanExt {a} {b} {c}
      (InterpSPFData {dom=a} {cod=c} q)
      (InterpSPFData {dom=a} {cod=b} p))
spfdLKanFromPoly {a} {b} {c} q p sc eb ppdm =
  (spfdDir p eb (fst ppdm) **
   (\ec, qpdm => snd ppdm ec qpdm, (fst ppdm ** \_ => id)))

public export
spfdLKanToPoly : {a, b, c : Type} ->
  (q : SPFData a c) -> (p : SPFData a b) ->
  SliceNatTrans {x=c} {y=b}
    (SliceLKanExt {a} {b} {c}
      (InterpSPFData {dom=a} {cod=c} q)
      (InterpSPFData {dom=a} {cod=b} p))
    (InterpSPFData {dom=c} {cod=b} $ spfdLKanExt q p)
spfdLKanToPoly {a} {b} {c} q p sc eb ppdm =
  (fst (snd $ snd $ ppdm) **
   \ec =>
    fst (snd ppdm) ec
    . dpMapSnd (\qp, dm => sliceComp (snd $ snd $ snd ppdm) dm))

-----------------------------------------
-----------------------------------------
---- Symmetric n-way Day convolution ----
-----------------------------------------
-----------------------------------------

-- An n-way symmetric monoidal structure on `Type` induces an n-way
-- symmetric monoidal structure on slice polynomial functors via the Day
-- convolution.

public export
spfdSetDayConvPos : {n, dom, cod : Type} ->
  (n -> SPFData dom cod) -> SliceObj cod
spfdSetDayConvPos {n} {dom} {cod} sf =
  Pi {a=n} . flip (spfdPos . sf)

public export
spfdSetDayConvDir : {n, dom, cod : Type} ->
  (m : (n -> Type) -> Type) ->
  (sf : n -> SPFData dom cod) ->
  SPFdirType dom cod (spfdSetDayConvPos {n} {dom} {cod} sf)
spfdSetDayConvDir {n} {dom} {cod} m sf ec ep ed =
  m $ \i => spfdDir (sf i) ec (ep i) ed

public export
spfdSetDayConv : {n, dom, cod : Type} ->
  ((n -> Type) -> Type) ->
  (n -> SPFData dom cod) -> SPFData dom cod
spfdSetDayConv {n} {dom} {cod} m sf =
  SPFD
    (spfdSetDayConvPos {n} {dom} {cod} sf)
    (spfdSetDayConvDir {n} {dom} {cod} m sf)

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

public export
spfdTerminal : (dom, cod : Type) -> SPFData dom cod
spfdTerminal dom cod = SPFD (\_ => Unit) (\_, _, _ => Void)

-- A zero-way product is a terminal object.
public export
spfdTerminalFromSet : (dom, cod : Type) ->
  SPFnt {dom} {cod}
    (spfdSetProduct {b=Void} {dom} {cod} $ \v => void v)
    (spfdTerminal dom cod)
spfdTerminalFromSet dom cod = SPFDm (\_, _ => ()) (\_, _, _, v => void v)

public export
spfdTerminalToSet : (dom, cod : Type) ->
  SPFnt {dom} {cod}
    (spfdTerminal dom cod)
    (spfdSetProduct {b=Void} {dom} {cod} $ \v => void v)
spfdTerminalToSet dom cod =
  SPFDm
    (\_, _ => (() ** \vc => void $ fst vc))
    (\_, _, _, vd => fst $ fst $ fst vd)

public export
spfdToTerminal : {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> SPFnt {dom} {cod} spfd (spfdTerminal dom cod)
spfdToTerminal {dom} {cod} spfd =
  SPFDm (\_, _ => ()) (\_, _, _, v => void v)

------------------------
------------------------
---- Initial object ----
------------------------
------------------------

public export
spfdInitial : (dom, cod : Type) -> SPFData dom cod
spfdInitial dom cod = SPFD (\_ => Void) (\_, v, _ => void v)

-- A zero-way coproduct is an initial object.
public export
spfdInitialFromSet : (dom, cod : Type) ->
  SPFnt {dom} {cod}
    (spfdSetCoproduct {b=Void} {dom} {cod} $ \v => void v)
    (spfdInitial dom cod)
spfdInitialFromSet dom cod =
  SPFDm
    (\ec, sfs => void $ fst $ sfsFst $ fst sfs)
    (\ec, sfs, ed => void $ fst $ sfsFst $ fst sfs)

public export
spfdInitialToSet : (dom, cod : Type) ->
  SPFnt {dom} {cod}
    (spfdInitial dom cod)
    (spfdSetCoproduct {b=Void} {dom} {cod} $ \v => void v)
spfdInitialToSet dom cod =
  SPFDm (\ec, v => void v) (\ec, v => void v)

public export
spfdFromInitial : {dom, cod : Type} ->
  (spfd : SPFData dom cod) -> SPFnt {dom} {cod} (spfdInitial dom cod) spfd
spfdFromInitial {dom} {cod} spfd =
  SPFDm (\ec, v => void v) (\ec, v => void v)

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

public export
spfdProduct : {dom, cod : Type} ->
  SPFData dom cod -> SPFData dom cod -> SPFData dom cod
spfdProduct {dom} {cod} f g =
  SPFD
    (\ec =>
      Pair (spfdPos f ec) (spfdPos g ec))
    (\ec, ep, ed =>
      Either
        (flip (spfdDir f ec) ed (fst ep))
        (flip (spfdDir g ec) ed (snd ep)))

-- A binary product is a set product indexed by a type of cardinality two.

public export
spfdProductToSet : {dom, cod : Type} ->
  (f, g : SPFData dom cod) ->
  SPFnt
    (spfdProduct {dom} {cod} f g)
    (spfdSetProduct {b=(Fin 2)} {dom} {cod} $ flip Vect.index [f, g])
spfdProductToSet {dom} {cod} f g =
  SPFDm
    (\ec, ep =>
      (() ** \(i, ec), Refl => case i of FZ => fst ep ; FS FZ => snd ep))
    (\ec, ep, ed, (((i, ed) ** Refl) ** dd) =>
      case i of FZ => Left dd ; FS FZ => Right dd)

public export
spfdProductFromSet : {dom, cod : Type} ->
  (f, g : SPFData dom cod) ->
  SPFnt
    (spfdSetProduct {b=(Fin 2)} {dom} {cod} $ flip Vect.index [f, g])
    (spfdProduct {dom} {cod} f g)
spfdProductFromSet {dom} {cod} f g =
  SPFDm
    (\ec, (() ** dm) => (dm (FZ, ec) Refl, dm (FS FZ, ec) Refl))
    (\ec, (() ** dm), ed, dd => case dd of
      Left fd => (((FZ, ec) ** Refl) ** fd)
      Right gd => (((FS FZ, ec) ** Refl) ** gd))

public export
spfdProductIntro : {dom, cod : Type} ->
  {x, y, z : SPFData dom cod} ->
  SPFnt {dom} {cod} x y ->
  SPFnt {dom} {cod} x z ->
  SPFnt {dom} {cod} x (spfdProduct {dom} {cod} y z)
spfdProductIntro {dom} {cod} {x} {y} f g =
  SPFDm
    (\ec, ep => (spOnPos f ec ep, spOnPos g ec ep))
    (\ec, ep, ed, dd => case dd of
      Left fd => spOnDir f ec ep ed fd
      Right gd => spOnDir g ec ep ed gd)

public export
spfdProductProj1 : {dom, cod : Type} -> (x, y : SPFData dom cod) ->
  SPFnt {dom} {cod} (spfdProduct {dom} {cod} x y) x
spfdProductProj1 {dom} {cod} x y =
  SPFDm (\_ => fst) (\ec, ep, ed => Left)

public export
spfdProductProj2 : {dom, cod : Type} -> (x, y : SPFData dom cod) ->
  SPFnt {dom} {cod} (spfdProduct {dom} {cod} x y) y
spfdProductProj2 {dom} {cod} x y =
  SPFDm (\_ => snd) (\ec, ep, ed => Right)

-- `spfdTerminal` (the zero-way product) is a unit for the product.

public export
spfdProductToUnitL : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    spfd
    (spfdProduct {dom} {cod} (spfdTerminal dom cod) spfd)
spfdProductToUnitL {dom} {cod} spfd =
  SPFDm (\ec => MkPair ()) (\ec, ep, ed => eitherElim (\v => void v) id)

public export
spfdProductToUnitR : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    spfd
    (spfdProduct {dom} {cod} spfd (spfdTerminal dom cod))
spfdProductToUnitR {dom} {cod} spfd =
  SPFDm (\ec => flip MkPair ()) (\ec, ep, ed => eitherElim id (\v => void v))

public export
spfdProductFromUnitL : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    (spfdProduct {dom} {cod} (spfdTerminal dom cod) spfd)
    spfd
spfdProductFromUnitL {dom} {cod} spfd =
  SPFDm (\_ => snd) (\_, _, _ => Right)

public export
spfdProductFromUnitR : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    (spfdProduct {dom} {cod} spfd (spfdTerminal dom cod))
    spfd
spfdProductFromUnitR {dom} {cod} spfd =
  SPFDm (\_ => fst) (\_, _, _ => Left)

---------------------------
---------------------------
---- Binary coproducts ----
---------------------------
---------------------------

public export
spfdCoproduct : {dom, cod : Type} ->
  SPFData dom cod -> SPFData dom cod -> SPFData dom cod
spfdCoproduct {dom} {cod} f g =
  SPFD
    (\ec =>
      Either (spfdPos f ec) (spfdPos g ec))
    (\ec, ep, ed =>
      eitherElim (flip (spfdDir f ec) ed) (flip (spfdDir g ec) ed) ep)

-- A binary coproduct is a set coproduct indexed by a type of cardinality two.

public export
spfdCoproductToSet : {dom, cod : Type} ->
  (f, g : SPFData dom cod) ->
  SPFnt
    (spfdCoproduct {dom} {cod} f g)
    (spfdSetCoproduct {b=(Fin 2)} {dom} {cod} $ flip Vect.index [f, g])
spfdCoproductToSet {dom} {cod} f g =
  SPFDm
    (\ec, ep => case ep of
      Left efp => (SFS (FZ, ec) () ** \(i, ec), Refl => efp)
      Right egp => (SFS (FS FZ, ec) () ** \(i, ec), Refl => egp))
    (\ec, ep, ed =>
      case ep of
        Left efp => \(((FZ, ec) ** Refl) ** efd) => efd
        Right egp => \(((FS FZ, ec) ** Refl) ** egd) => egd)

public export
spfdCoproductFromSet : {dom, cod : Type} ->
  (f, g : SPFData dom cod) ->
  SPFnt
    (spfdSetCoproduct {b=(Fin 2)} {dom} {cod} $ flip Vect.index [f, g])
    (spfdCoproduct {dom} {cod} f g)
spfdCoproductFromSet {dom} {cod} f g =
  SPFDm
    (\ec, (SFS (i, ec) () ** dm) => case i of
      FZ => Left $ dm (FZ, ec) Refl
      FS FZ => Right $ dm (FS FZ, ec) Refl)
    (\ec, (SFS (i, ec) () ** dm), ed, dd => case i of
      FZ => (((FZ, ec) ** Refl) ** dd)
      FS FZ => (((FS FZ, ec) ** Refl) ** dd))

public export
spfdCoproductInjL : {dom, cod : Type} -> (x, y : SPFData dom cod) ->
  SPFnt {dom} {cod} x (spfdCoproduct {dom} {cod} x y)
spfdCoproductInjL {dom} {cod} x y =
  SPFDm (\ec => Left) (\ec, ep, ed => id)

public export
spfdCoproductInjR : {dom, cod : Type} -> (x, y : SPFData dom cod) ->
  SPFnt {dom} {cod} y (spfdCoproduct {dom} {cod} x y)
spfdCoproductInjR {dom} {cod} x y =
  SPFDm (\ec => Right) (\ec, ep, ed => id)

public export
spfdCoproductElim : {dom, cod : Type} ->
  {x, y, z : SPFData dom cod} ->
  SPFnt {dom} {cod} x z ->
  SPFnt {dom} {cod} y z ->
  SPFnt {dom} {cod} (spfdCoproduct {dom} {cod} x y) z
spfdCoproductElim {dom} {cod} {x} {y} f g =
  SPFDm
    (\ec => eitherElim (spOnPos f ec) (spOnPos g ec))
    (\ec, ep, ed, dd => case ep of
      Left xp => spOnDir f ec xp ed dd
      Right yp => spOnDir g ec yp ed dd)

-- `spfdInitial` (the zero-way coproduct) is a unit for the coproduct.

public export
spfdCoproductToUnitL : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    spfd
    (spfdCoproduct {dom} {cod} (spfdInitial dom cod) spfd)
spfdCoproductToUnitL {dom} {cod} spfd =
  SPFDm (\ec => Right) (\ec, ep, ed => id)

public export
spfdCoproductToUnitR : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    spfd
    (spfdCoproduct {dom} {cod} spfd (spfdInitial dom cod))
spfdCoproductToUnitR {dom} {cod} spfd =
  SPFDm (\ec => Left) (\ec, ep, ed => id)

public export
spfdCoproductFromUnitL : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    (spfdCoproduct {dom} {cod} (spfdInitial dom cod) spfd)
    spfd
spfdCoproductFromUnitL {dom} {cod} spfd =
  SPFDm
    (\ec => eitherElim (\v => void v) id)
    (\ec, ep, ed, dd => case ep of
      Left v => void v
      Right sp => dd)

public export
spfdCoproductFromUnitR : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    (spfdCoproduct {dom} {cod} spfd (spfdInitial dom cod))
    spfd
spfdCoproductFromUnitR {dom} {cod} spfd =
  SPFDm
    (\ec => eitherElim id (\v => void v))
    (\ec, ep, ed, dd => case ep of
      Left sp => dd
      Right v => void v)

----------------------------------
----------------------------------
---- Binary parallel products ----
----------------------------------
----------------------------------

public export
spfdParProduct : {dom, cod : Type} ->
  SPFData dom cod -> SPFData dom cod -> SPFData dom cod
spfdParProduct {dom} {cod} f g =
  SPFD
    (\ec =>
      Pair (spfdPos f ec) (spfdPos g ec))
    (\ec, ep, ed =>
      Pair
        (flip (spfdDir f ec) ed (fst ep))
        (flip (spfdDir g ec) ed (snd ep)))

-- A binary parallel product is a set parallel product indexed by a type of
-- cardinality two.

public export
spfdParProductToSet : {dom, cod : Type} ->
  (f, g : SPFData dom cod) ->
  SPFnt
    (spfdParProduct {dom} {cod} f g)
    (spfdSetParProduct {b=(Fin 2)} {dom} {cod} $ flip Vect.index [f, g])
spfdParProductToSet {dom} {cod} f g =
  SPFDm
    (\ec, ep, i => case i of FZ => fst ep ; FS FZ => snd ep)
    (\ec, ep, ed, dm => (dm FZ, dm $ FS FZ))

public export
spfdParProductFromSet : {dom, cod : Type} ->
  (f, g : SPFData dom cod) ->
  SPFnt
    (spfdSetParProduct {b=(Fin 2)} {dom} {cod} $ flip Vect.index [f, g])
    (spfdParProduct {dom} {cod} f g)
spfdParProductFromSet {dom} {cod} f g =
  SPFDm
    (\ec, dm => (dm FZ, dm $ FS FZ))
    (\ec, dm, ed, dd, i => case i of FZ => fst dd ; FS FZ => snd dd)

public export
spfdParProductNT : {dom, cod : Type} ->
  {p, p', q, q' : SPFData dom cod} ->
  SPFnt {dom} {cod} p p' ->
  SPFnt {dom} {cod} q q' ->
  SPFnt {dom} {cod}
    (spfdParProduct {dom} {cod} p q)
    (spfdParProduct {dom} {cod} p' q')
spfdParProductNT {dom} {cod} {p} {p'} {q} {q'} f g =
  SPFDm
    (\ec =>
      bimap (spOnPos f ec) (spOnPos g ec))
    (\ec, (fp, gp), ed, (fd, gd) =>
      (spOnDir f ec fp ed fd, spOnDir g ec gp ed gd))

-- `SPFDRepTerminal` (the zero-way parallel product) is a unit for
-- the parallel product.

public export
spfdParProductToUnitL : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    spfd
    (spfdParProduct {dom} {cod} (SPFDRepTerminal dom cod) spfd)
spfdParProductToUnitL {dom} {cod} spfd =
  SPFDm (\ec => MkPair ()) (\ec, ep, d => snd)

public export
spfdParProductToUnitR : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    spfd
    (spfdParProduct {dom} {cod} spfd (SPFDRepTerminal dom cod))
spfdParProductToUnitR {dom} {cod} spfd =
  SPFDm (\ec => flip MkPair ()) (\ec, ep, d => fst)

public export
spfdParProductFromUnitL : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    (spfdParProduct {dom} {cod} (SPFDRepTerminal dom cod) spfd)
    spfd
spfdParProductFromUnitL {dom} {cod} spfd =
  SPFDm (\ec => snd) (\ec, ep, ed => MkPair ())

public export
spfdParProductFromUnitR : {dom, cod : Type} -> (spfd : SPFData dom cod) ->
  SPFnt {dom} {cod}
    (spfdParProduct {dom} {cod} spfd (SPFDRepTerminal dom cod))
    spfd
spfdParProductFromUnitR {dom} {cod} spfd =
  SPFDm (\ec => fst) (\ec, ep, ed => flip MkPair ())

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

public export
spfdFlipEither : {w : Type} -> SliceObj w -> SPFData w w
spfdFlipEither {w} a =
  spfdCoproduct {dom=w} {cod=w} (SPFDid w) (SPFDataConst w a)

-- Given an object `A`, this functor takes `Y -> Pair A Y`.
public export
spfdPair : {w : Type} -> SliceObj w -> SPFData w w
spfdPair {w} a = spfdProduct {dom=w} {cod=w} (SPFDataConst w a) (SPFDid w)

public export
spfdFlipPair : {w : Type} -> SliceObj w -> SPFData w w
spfdFlipPair {w} a = spfdProduct {dom=w} {cod=w} (SPFDid w) (SPFDataConst w a)

public export
spfdMaybe : (w : Type) -> SPFData w w
spfdMaybe w = spfdEither {w} (SliceObjTerminal w)

-- Compose the given functor after the terminal functor.
public export
spfdCompTerm : {x, y, z : Type} -> SPFData y z -> SPFData x z
spfdCompTerm {x} {y} {z} q = SPFDcomp x y z q (spfdTerminal x y)

-- Any composite polynomial functor `q . r` has a natural transformation
-- to `q . 1`.  This in particular means that any composite `q . r` may be
-- viewed in a canonical way as a slice object in the slice category over
-- `q . 1` -- i.e., over the constant functor whose value everywhere is the
-- position-set of `q`.
--
-- See proposition 6.73 in _Polynomial Functors: A Mathematical Theory
-- of Interaction_.
public export
spfdCompToPosNT : {x, y, z : Type} -> (q : SPFData y z) -> (r : SPFData x y) ->
  SPFnt {dom=x} {cod=z}
    (SPFDcomp x y z q r)
    (spfdCompTerm {x} {y} {z} q)
spfdCompToPosNT {x} {y} {z} (SPFD qpos qdir) (SPFD rpos rdir) =
  SPFDm (\ez, qp => (fst qp ** \_, _ => ())) (\ez, qp, ex, qd => void $ snd qd)

---------------------
---------------------
---- Hom-objects ----
---------------------
---------------------

-- We compute slice polynomial hom-objects in three steps:
--  1) Hom-objects on copresheaves on slices (i.e. slice polynomials where
--     the codomain is `SliceObj Unit`, i.e. `Type`) where the
--     domain `SPFData` is representable
--  2) Hom-objects on copresheaves with any domain (and codomain) `SPFData`
--  3) Hom-objects between any slice categories with any domain (and codomain)
--     `SPFData` -- i.e. the general case

-------------------------------------------------------
---- Representable copresheaves on `SliceObj dom`) ----
-------------------------------------------------------

-- See formula 5.27 in "Polynomial Functors: A Mathematical Theory
-- of Interaction".
public export
spfdRepHomObj : {dom : Type} ->
  SliceObj dom -> SPFData dom Unit -> SPFData dom Unit
spfdRepHomObj {dom} q r = SPFDcomp dom dom Unit r (spfdFlipEither {w=dom} q)

public export
spfdRepHomToPoly : {dom : Type} ->
  (p : SliceObj dom) -> (q : SPFData dom Unit) ->
  (x : SliceObj dom) ->
  InterpSPFData {dom} {cod=Unit} (spfdRepHomObj {dom} p q) x () ->
  (InterpSPFData {dom} {cod=Unit} (spfdCoprPiFR p) x () ->
   InterpSPFData {dom} {cod=Unit} q x ())
spfdRepHomToPoly {dom} p (SPFD qpos qdir) x ((qp ** mqp) ** qdm) (() ** mpx) =
  (qp ** xed) where
    xed : (ed : dom) -> qdir () qp ed -> x ed
    xed ed qd with (mqp ed qd) proof eq
      xed ed' qd | Left () = qdm ed' ((ed' ** qd) ** rewrite eq in Refl)
      xed ed' qd | Right pd = mpx ed' pd

public export
spfdRepHomObjPos : {dom : Type} ->
  SliceObj dom -> SPFData dom Unit -> SliceObj Unit
spfdRepHomObjPos {dom} p q = spfdPos (spfdRepHomObj {dom} p q)

public export
spfdRepHomObjDir : {dom : Type} ->
  (p : SliceObj dom) -> (q : SPFData dom Unit) ->
  SPFdirType dom Unit (spfdRepHomObjPos {dom} p q)
spfdRepHomObjDir {dom} p q = spfdDir (spfdRepHomObj {dom} p q)

public export
spfdRepEvalPos : {dom : Type} ->
  (p : SliceObj dom) -> (q : SPFData dom Unit) ->
  SPFntPos {dom} {cod=Unit}
    (spfdProduct {dom} {cod=Unit} (spfdRepHomObj {dom} p q) (spfdCoprPiFR p))
    q
spfdRepEvalPos {dom} p q u = fst . fst

public export
spfdRepEvalDir : {dom : Type} ->
  (p : SliceObj dom) -> (q : SPFData dom Unit) ->
  SPFntDir {dom}
    (spfdProduct {dom} {cod=Unit} (spfdRepHomObj {dom} p q) (spfdCoprPiFR p))
    q
    (spfdRepEvalPos {dom} p q)
spfdRepEvalDir {dom} p (SPFD qpos qdir) () (qpdm, ()) ed qd
    with (snd qpdm ed qd) proof eq
  spfdRepEvalDir {dom} p (SPFD qpos qdir) () (qpdm, ()) ed qd | Left () =
    Left ((ed ** qd) ** rewrite eq in Refl)
  spfdRepEvalDir {dom} p (SPFD qpos qdir) () (qpdm, ()) ed qd | Right pd =
    Right pd

public export
spfdRepEval : {dom : Type} ->
  (p : SliceObj dom) -> (q : SPFData dom Unit) ->
  SPFnt {dom} {cod=Unit}
    (spfdProduct {dom} {cod=Unit} (spfdRepHomObj {dom} p q) (spfdCoprPiFR p))
    q
spfdRepEval {dom} p q =
  SPFDm (spfdRepEvalPos {dom} p q) (spfdRepEvalDir {dom} p q)

public export
spfdRepCurryPos : {dom : Type} ->
  {q : SliceObj dom} -> {p, r : SPFData dom Unit} ->
  SPFnt {dom} {cod=Unit} (spfdProduct {dom} {cod=Unit} p (spfdCoprPiFR q)) r ->
  SPFntPos {dom} {cod=Unit} p (spfdRepHomObj {dom} q r)
spfdRepCurryPos {dom} {p=(SPFD ppos pdir)} {q} {r=(SPFD rpos rdir)}
  (SPFDm onpos ondir) () pp =
    (onpos () (pp, ()) **
     \ed, rd => case ondir () (pp, ()) ed rd of
      Left pd => Left ()
      Right qd => Right qd)

public export
spfdRepCurryDir : {dom : Type} ->
  {q : SliceObj dom} -> {p, r : SPFData dom Unit} ->
  (f : SPFnt {dom} {cod=Unit}
    (spfdProduct {dom} {cod=Unit} p (spfdCoprPiFR q))
    r) ->
  SPFntDir {dom} {cod=Unit}
    p
    (spfdRepHomObj {dom} q r)
    (spfdRepCurryPos {dom} {p} {q} {r} f)
spfdRepCurryDir {dom} {p=(SPFD ppos pdir)} {q} {r=(SPFD rpos rdir)}
  (SPFDm onpos ondir) () pp ed ((ed' ** rd) ** dd) with
      (ondir () (pp, ()) ed' rd) proof eq
  spfdRepCurryDir {dom} {p=(SPFD ppos pdir)} {q} {r=(SPFD rpos rdir)}
    (SPFDm onpos ondir) () pp ed ((ed ** rd) ** Refl) | Left pd =
      pd
  spfdRepCurryDir {dom} {p=(SPFD ppos pdir)} {q} {r=(SPFD rpos rdir)}
    (SPFDm onpos ondir) () pp ed ((ed' ** rd) ** v) | Right qd =
      void v

public export
spfdRepCurry : {dom : Type} ->
  {q : SliceObj dom} -> {p, r : SPFData dom Unit} ->
  SPFnt {dom} {cod=Unit} (spfdProduct {dom} {cod=Unit} p (spfdCoprPiFR q)) r ->
  SPFnt {dom} {cod=Unit} p (spfdRepHomObj {dom} q r)
spfdRepCurry {dom} {p} {q} {r} m =
  SPFDm
    (spfdRepCurryPos {dom} {p} {q} {r} m)
    (spfdRepCurryDir {dom} {p} {q} {r} m)

-----------------------------------------
---- Copresheaves on `SliceObj dom`) ----
-----------------------------------------

public export
spfdCoprHomObj : {dom : Type} ->
  SPFData dom Unit -> SPFData dom Unit -> SPFData dom Unit
spfdCoprHomObj {dom} q r =
  spfdSetProduct {b=(spfdPos q ())} {dom} {cod=Unit} $
    \ep => spfdRepHomObj {dom} (spfdDir q () ep) r

public export
spfdCoprHomToPoly : {dom : Type} ->
  (p, q : SPFData dom Unit) ->
  (x : SliceObj dom) ->
  InterpSPFData {dom} {cod=Unit} (spfdCoprHomObj {dom} p q) x () ->
  (InterpSPFData {dom} {cod=Unit} p x () ->
   InterpSPFData {dom} {cod=Unit} q x ())
spfdCoprHomToPoly {dom} p@(SPFD ppos pdir) q x ((() ** ep) ** dm) (pp ** pdm) =
  spfdRepHomToPoly {dom} (pdir () pp) q x
    (ep (pp, ()) Refl ** \ed, qd => dm ed (((pp, ()) ** Refl) ** qd))
    (() ** pdm)

public export
spfdCoprHomObjPos : {dom : Type} ->
  SPFData dom Unit -> SPFData dom Unit -> SliceObj Unit
spfdCoprHomObjPos {dom} p q = spfdPos (spfdCoprHomObj {dom} p q)

public export
spfdCoprHomObjDir : {dom : Type} ->
  (p, q : SPFData dom Unit) ->
  SPFdirType dom Unit (spfdCoprHomObjPos {dom} p q)
spfdCoprHomObjDir {dom} p q = spfdDir (spfdCoprHomObj {dom} p q)

public export
spfdCoprEvalPos : {dom : Type} ->
  (p, q : SPFData dom Unit) ->
  SPFntPos {dom} {cod=Unit}
    (spfdProduct {dom} {cod=Unit} (spfdCoprHomObj {dom} p q) p)
    q
spfdCoprEvalPos {dom} p q () ((() ** ep), pp) =
  spfdRepEvalPos {dom} (spfdDir p () pp) q () (ep (pp, ()) Refl, ())

public export
spfdCoprEvalDir : {dom : Type} ->
  (p, q : SPFData dom Unit) ->
  SPFntDir {dom}
    (spfdProduct {dom} {cod=Unit} (spfdCoprHomObj {dom} p q) p)
    q
    (spfdCoprEvalPos {dom} p q)
spfdCoprEvalDir {dom} p q () ((() ** ep), pp) ed qd =
  mapFst
    (MkDPair ((pp, ()) ** Refl))
    (spfdRepEvalDir {dom} (spfdDir p () pp) q () (ep (pp, ()) Refl, ()) ed qd)

public export
spfdCoprEval : {dom : Type} ->
  (p, q : SPFData dom Unit) ->
  SPFnt {dom} {cod=Unit}
    (spfdProduct {dom} {cod=Unit} (spfdCoprHomObj {dom} p q) p)
    q
spfdCoprEval {dom} p q =
  SPFDm (spfdCoprEvalPos {dom} p q) (spfdCoprEvalDir {dom} p q)

public export
spfdCoprCurryPos : {dom : Type} ->
  {p, q, r : SPFData dom Unit} ->
  SPFnt {dom} {cod=Unit} (spfdProduct {dom} {cod=Unit} p q) r ->
  SPFntPos {dom} {cod=Unit} p (spfdCoprHomObj {dom} q r)
spfdCoprCurryPos {dom} {p} {q} {r} nt () pp =
  (() **
   \(qp, ()), Refl =>
    spfdRepCurryPos {p} {q=(spfdDir q () qp)} {r}
      (SPFDm
        (\(), (pp', ()) => spOnPos nt () (pp', qp))
        (\(), (pp', ()), ed => spOnDir nt () (pp', qp) ed))
        ()
        pp)

public export
spfdCoprCurryDir : {dom : Type} ->
  {p, q, r : SPFData dom Unit} ->
  (f : SPFnt {dom} {cod=Unit} (spfdProduct {dom} {cod=Unit} p q) r) ->
  SPFntDir {dom} {cod=Unit}
    p
    (spfdCoprHomObj {dom} q r)
    (spfdCoprCurryPos {dom} {p} {q} {r} f)
spfdCoprCurryDir {dom} {p} {q} {r} nt () pp ed
  (((qp, ()) ** Refl) ** ((ed' ** rd) ** qd)) =
    spfdRepCurryDir {p} {q=(spfdDir q () qp)} {r}
      _
      ()
      pp
      ed
      ((ed' ** rd) ** qd)

public export
spfdCoprCurry : {dom : Type} ->
  {p, q, r : SPFData dom Unit} ->
  SPFnt {dom} {cod=Unit} (spfdProduct {dom} {cod=Unit} p q) r ->
  SPFnt {dom} {cod=Unit} p (spfdCoprHomObj {dom} q r)
spfdCoprCurry {dom} {p} {q} {r} m =
  SPFDm
    (spfdCoprCurryPos {dom} {p} {q} {r} m)
    (spfdCoprCurryDir {dom} {p} {q} {r} m)

----------------------------
---- General `SPFData`s ----
----------------------------

public export
spfdHomObj : {dom, cod : Type} ->
  SPFData dom cod -> SPFData dom cod -> SPFData dom cod
spfdHomObj {dom} {cod} q r =
  SPFDataFamToProdUnit $ \ec =>
    spfdCoprHomObj (SPFDataProdToFamUnit q ec) (SPFDataProdToFamUnit r ec)

public export
spfdHomToPoly : {dom, cod : Type} ->
  (p, q : SPFData dom cod) ->
  (x : SliceObj dom) -> (ec : cod) ->
  InterpSPFData {dom} {cod} (spfdHomObj {dom} {cod} p q) x ec ->
  (InterpSPFData {dom} {cod} p x ec -> InterpSPFData {dom} {cod} q x ec)
spfdHomToPoly {dom} {cod} p q x ec =
  spfdCoprHomToPoly {dom}
    (SPFDataProdToFamUnit p ec)
    (SPFDataProdToFamUnit q ec)
    x

public export
spfdHomObjPos : {dom, cod : Type} ->
  SPFData dom cod -> SPFData dom cod -> SliceObj cod
spfdHomObjPos {dom} {cod} p q = spfdPos (spfdHomObj {dom} {cod} p q)

public export
spfdHomObjDir : {dom, cod : Type} ->
  (p, q : SPFData dom cod) ->
  SPFdirType dom cod (spfdHomObjPos {dom} {cod} p q)
spfdHomObjDir {dom} {cod} p q = spfdDir (spfdHomObj {dom} {cod} p q)

public export
spfdEvalPos : {dom, cod : Type} ->
  (p, q : SPFData dom cod) ->
  SPFntPos {dom} {cod}
    (spfdProduct {dom} {cod} (spfdHomObj {dom} {cod} p q) p)
    q
spfdEvalPos {dom} {cod} p q ec =
  spfdCoprEvalPos {dom}
    (SPFDataProdToFamUnit p ec)
    (SPFDataProdToFamUnit q ec) ()

public export
spfdEvalDir : {dom, cod : Type} ->
  (p, q : SPFData dom cod) ->
  SPFntDir {dom} {cod}
    (spfdProduct {dom} {cod} (spfdHomObj {dom} {cod} p q) p)
    q
    (spfdEvalPos {dom} {cod} p q)
spfdEvalDir {dom} {cod} p q ec ((() ** epm), pp) ed qd =
  mapFst
    (dpMapSnd $ \((pp', ()) ** Refl) => id)
    (spfdCoprEvalDir {dom}
      (SPFDataProdToFamUnit p ec)
      (SPFDataProdToFamUnit q ec)
      ()
      ((() ** \(pp', ()), Refl => epm (pp', ()) Refl), pp)
      ed
      qd)

public export
spfdEval : {dom, cod : Type} ->
  (p, q : SPFData dom cod) ->
  SPFnt {dom} {cod} (spfdProduct {dom} {cod} (spfdHomObj {dom} {cod} p q) p) q
spfdEval {dom} {cod} p q =
  SPFDm (spfdEvalPos {dom} {cod} p q) (spfdEvalDir {dom} {cod} p q)

public export
spfdCurryPos : {dom, cod : Type} ->
  {p, q, r : SPFData dom cod} ->
  SPFnt {dom} {cod} (spfdProduct {dom} {cod} p q) r ->
  SPFntPos {dom} {cod} p (spfdHomObj {dom} {cod} q r)
spfdCurryPos {dom} {cod} {p} {q} {r} m ec =
  spfdCoprCurryPos {dom}
    {p=(SPFDataProdToFamUnit p ec)}
    {q=(SPFDataProdToFamUnit q ec)}
    {r=(SPFDataProdToFamUnit r ec)}
    (SPFDataProdToFamUnitNT (spfdProduct p q) r m ec)
    ()

public export
spfdCurryDir : {dom, cod : Type} ->
  {p, q, r : SPFData dom cod} ->
  (f : SPFnt {dom} {cod} (spfdProduct {dom} {cod} p q) r) ->
  SPFntDir {dom} {cod}
    p
    (spfdHomObj {dom} {cod} q r)
    (spfdCurryPos {dom} {cod} {p} {q} {r} f)
spfdCurryDir {dom} {cod} {p} {q} {r} m ec  =
  spfdCoprCurryDir {dom}
    {p=(SPFDataProdToFamUnit p ec)}
    {q=(SPFDataProdToFamUnit q ec)}
    {r=(SPFDataProdToFamUnit r ec)}
    (SPFDataProdToFamUnitNT (spfdProduct p q) r m ec)
    ()

public export
spfdCurry : {dom, cod : Type} ->
  {p, q, r : SPFData dom cod} ->
  SPFnt {dom} {cod} (spfdProduct {dom} {cod} p q) r ->
  SPFnt {dom} {cod} p (spfdHomObj {dom} {cod} q r)
spfdCurry {dom} {cod} {p} {q} {r} m =
  SPFDm
    (spfdCurryPos {dom} {cod} {p} {q} {r} m)
    (spfdCurryDir {dom} {cod} {p} {q} {r} m)

----------------------------------
----------------------------------
---- Parallel product closure ----
----------------------------------
----------------------------------

-- As with hom-objects, we compute the parallel-product closure
-- in three steps.

-------------------------------------------------------
---- Representable copresheaves on `SliceObj dom`) ----
-------------------------------------------------------

-- See formula 4.75 in "Polynomial Functors: A Mathematical Theory
-- of Interaction".
public export
spfdParRepHomObj : {dom : Type} ->
  SliceObj dom -> SPFData dom Unit -> SPFData dom Unit
spfdParRepHomObj {dom} q r = SPFDcomp dom dom Unit r (spfdFlipPair {w=dom} q)

public export
spfdParRepHomObjPos : {dom : Type} ->
  SliceObj dom -> SPFData dom Unit -> SliceObj Unit
spfdParRepHomObjPos {dom} p q = spfdPos (spfdParRepHomObj {dom} p q)

public export
spfdParRepHomObjDir : {dom : Type} ->
  (p : SliceObj dom) -> (q : SPFData dom Unit) ->
  SPFdirType dom Unit (spfdParRepHomObjPos {dom} p q)
spfdParRepHomObjDir {dom} p q = spfdDir (spfdParRepHomObj {dom} p q)

public export
spfdParRepEvalPos : {dom : Type} ->
  (p : SliceObj dom) -> (q : SPFData dom Unit) ->
  SPFntPos {dom} {cod=Unit}
    (spfdParProduct {dom} {cod=Unit}
      (spfdParRepHomObj {dom} p q)
      (spfdCoprPiFR p))
    q
spfdParRepEvalPos {dom} p q u = fst . fst

public export
spfdParRepEvalDir : {dom : Type} ->
  (p : SliceObj dom) -> (q : SPFData dom Unit) ->
  SPFntDir {dom}
    (spfdParProduct {dom} {cod=Unit}
      (spfdParRepHomObj {dom} p q)
      (spfdCoprPiFR p))
    q
    (spfdParRepEvalPos {dom} p q)
spfdParRepEvalDir {dom} p q () (qpdm, ()) ed qd
    with (snd qpdm ed qd) proof eq
  spfdParRepEvalDir {dom} p q () ((qp ** dm), ()) ed qd | ((), pd) =
    (((ed ** qd) ** Left $ rewrite fstEq eq in Refl), pd)

public export
spfdParRepEval : {dom : Type} ->
  (p : SliceObj dom) -> (q : SPFData dom Unit) ->
  SPFnt {dom} {cod=Unit}
    (spfdParProduct {dom} {cod=Unit}
      (spfdParRepHomObj {dom} p q)
      (spfdCoprPiFR p))
    q
spfdParRepEval {dom} p q =
  SPFDm (spfdParRepEvalPos {dom} p q) (spfdParRepEvalDir {dom} p q)

public export
spfdParRepCurryPos : {dom : Type} ->
  {q : SliceObj dom} -> {p, r : SPFData dom Unit} ->
  SPFnt {dom} {cod=Unit}
    (spfdParProduct {dom} {cod=Unit} p (spfdCoprPiFR q))
    r ->
  SPFntPos {dom} {cod=Unit} p (spfdParRepHomObj {dom} q r)
spfdParRepCurryPos {dom} {p=(SPFD ppos pdir)} {q} {r=(SPFD rpos rdir)}
  (SPFDm onpos ondir) () pp =
    (onpos () (pp, ()) ** \ed, rd => ((), snd $ ondir () (pp, ()) ed rd))

public export
spfdParRepCurryDir : {dom : Type} ->
  {q : SliceObj dom} -> {p, r : SPFData dom Unit} ->
  (f : SPFnt {dom} {cod=Unit}
    (spfdParProduct {dom} {cod=Unit} p (spfdCoprPiFR q))
    r) ->
  SPFntDir {dom} {cod=Unit}
    p
    (spfdParRepHomObj {dom} q r)
    (spfdParRepCurryPos {dom} {p} {q} {r} f)
spfdParRepCurryDir {dom} {p=(SPFD ppos pdir)} {q} {r=(SPFD rpos rdir)}
  (SPFDm onpos ondir) () pp ed ((ed' ** rd) ** dd) with
      (ondir () (pp, ()) ed' rd) proof eq
  spfdParRepCurryDir {dom} {p=(SPFD ppos pdir)} {q} {r=(SPFD rpos rdir)}
    (SPFDm onpos ondir) () pp ed ((ed' ** rd) ** dd) | pd =
      case dd of
        Left Refl => fst pd
        Right v => void v

public export
spfdParRepCurry : {dom : Type} ->
  {q : SliceObj dom} -> {p, r : SPFData dom Unit} ->
  SPFnt {dom} {cod=Unit}
    (spfdParProduct {dom} {cod=Unit} p (spfdCoprPiFR q))
    r ->
  SPFnt {dom} {cod=Unit} p (spfdParRepHomObj {dom} q r)
spfdParRepCurry {dom} {p} {q} {r} m =
  SPFDm
    (spfdParRepCurryPos {dom} {p} {q} {r} m)
    (spfdParRepCurryDir {dom} {p} {q} {r} m)

-----------------------------------------
---- Copresheaves on `SliceObj dom`) ----
-----------------------------------------

public export
spfdParCoprHomObj : {dom : Type} ->
  SPFData dom Unit -> SPFData dom Unit -> SPFData dom Unit
spfdParCoprHomObj {dom} q r =
  spfdSetProduct {b=(spfdPos q ())} {dom} {cod=Unit} $
    \ep => spfdParRepHomObj {dom} (spfdDir q () ep) r

public export
spfdParCoprHomObjPos : {dom : Type} ->
  SPFData dom Unit -> SPFData dom Unit -> SliceObj Unit
spfdParCoprHomObjPos {dom} p q = spfdPos (spfdParCoprHomObj {dom} p q)

public export
spfdParCoprHomObjDir : {dom : Type} ->
  (p, q : SPFData dom Unit) ->
  SPFdirType dom Unit (spfdParCoprHomObjPos {dom} p q)
spfdParCoprHomObjDir {dom} p q = spfdDir (spfdParCoprHomObj {dom} p q)

public export
spfdParCoprEvalPos : {dom : Type} ->
  (p, q : SPFData dom Unit) ->
  SPFntPos {dom} {cod=Unit}
    (spfdParProduct {dom} {cod=Unit} (spfdParCoprHomObj {dom} p q) p)
    q
spfdParCoprEvalPos {dom} p q () ((() ** ep), pp) with (ep (pp, ()) Refl)
  spfdParCoprEvalPos {dom} p q () ((() ** ep), pp) | (qp ** dm) =
    spfdRepEvalPos {dom}
      (spfdDir p () pp) q () ((qp ** \ed => Right . snd . dm ed), ())

public export
spfdParCoprEvalDir : {dom : Type} ->
  (p, q : SPFData dom Unit) ->
  SPFntDir {dom}
    (spfdParProduct {dom} {cod=Unit} (spfdParCoprHomObj {dom} p q) p)
    q
    (spfdParCoprEvalPos {dom} p q)
spfdParCoprEvalDir {dom} p q () ((() ** ep), pp) ed qd
    with (ep (pp, ()) Refl) proof epeq
  spfdParCoprEvalDir {dom} p q () ((() ** ep), pp) ed qd | (qp ** dm) =
    case
      spfdRepEvalDir {dom}
        (spfdDir p () pp)
        q
        ()
        ((qp ** \ed => Right . snd . dm ed), ())
        ed
        qd of
      Left v => void $ snd v
      Right pd =>
        ((((pp, ()) ** Refl) **
           rewrite epeq in
           ((ed ** qd) **
            Left $ rewrite unitUnique (fst $ dm ed qd) () in Refl)), pd)

public export
spfdParCoprEval : {dom : Type} ->
  (p, q : SPFData dom Unit) ->
  SPFnt {dom} {cod=Unit}
    (spfdParProduct {dom} {cod=Unit} (spfdParCoprHomObj {dom} p q) p)
    q
spfdParCoprEval {dom} p q =
  SPFDm (spfdParCoprEvalPos {dom} p q) (spfdParCoprEvalDir {dom} p q)

public export
spfdParCoprCurryPos : {dom : Type} ->
  {p, q, r : SPFData dom Unit} ->
  SPFnt {dom} {cod=Unit} (spfdParProduct {dom} {cod=Unit} p q) r ->
  SPFntPos {dom} {cod=Unit} p (spfdParCoprHomObj {dom} q r)
spfdParCoprCurryPos {dom} {p} {q} {r} nt () pp =
  (() **
   \(qp, ()), Refl =>
    spfdParRepCurryPos {p} {q=(spfdDir q () qp)} {r}
      (SPFDm
        (\(), (pp', ()) => spOnPos nt () (pp', qp))
        (\(), (pp', ()), ed => spOnDir nt () (pp', qp) ed))
        ()
        pp)

public export
spfdParCoprCurryDir : {dom : Type} ->
  {p, q, r : SPFData dom Unit} ->
  (f : SPFnt {dom} {cod=Unit} (spfdParProduct {dom} {cod=Unit} p q) r) ->
  SPFntDir {dom} {cod=Unit}
    p
    (spfdParCoprHomObj {dom} q r)
    (spfdParCoprCurryPos {dom} {p} {q} {r} f)
spfdParCoprCurryDir {dom} {p} {q} {r} nt () pp ed
  (((qp, ()) ** Refl) ** ((ed' ** rd) ** qd)) =
    spfdParRepCurryDir {p} {q=(spfdDir q () qp)} {r}
      _
      ()
      pp
      ed
      ((ed' ** rd) ** qd)

public export
spfdParCoprCurry : {dom : Type} ->
  {p, q, r : SPFData dom Unit} ->
  SPFnt {dom} {cod=Unit} (spfdParProduct {dom} {cod=Unit} p q) r ->
  SPFnt {dom} {cod=Unit} p (spfdParCoprHomObj {dom} q r)
spfdParCoprCurry {dom} {p} {q} {r} m =
  SPFDm
    (spfdParCoprCurryPos {dom} {p} {q} {r} m)
    (spfdParCoprCurryDir {dom} {p} {q} {r} m)

----------------------------
---- General `SPFData`s ----
----------------------------

-- We call this the "parallel closure" since it is a closure of the
-- parallel product in the same way (i.e. with the same universal-morphism
-- signatures) that the exponential object is a closure of the product.
public export
spfdParClosureObj : {dom, cod : Type} ->
  SPFData dom cod -> SPFData dom cod -> SPFData dom cod
spfdParClosureObj {dom} {cod} q r =
  SPFDataFamToProdUnit $ \ec =>
    spfdParCoprHomObj (SPFDataProdToFamUnit q ec) (SPFDataProdToFamUnit r ec)

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

public export
spfdParEvalPos : {dom, cod : Type} ->
  (p, q : SPFData dom cod) ->
  SPFntPos {dom} {cod}
    (spfdParProduct {dom} {cod} (spfdParClosureObj {dom} {cod} p q) p)
    q
spfdParEvalPos {dom} {cod} p q ec =
  spfdParCoprEvalPos {dom}
    (SPFDataProdToFamUnit p ec)
    (SPFDataProdToFamUnit q ec)
    ()

public export
spfdParEvalDir : {dom, cod : Type} ->
  (p, q : SPFData dom cod) ->
  SPFntDir {dom} {cod}
    (spfdParProduct {dom} {cod} (spfdParClosureObj {dom} {cod} p q) p)
    q
    (spfdParEvalPos {dom} {cod} p q)
spfdParEvalDir {dom} {cod} p q ec =
  spfdParCoprEvalDir {dom}
    (SPFDataProdToFamUnit p ec)
    (SPFDataProdToFamUnit q ec)
    ()

public export
spfdParEval : {dom, cod : Type} ->
  (p, q : SPFData dom cod) ->
  SPFnt {dom} {cod}
    (spfdParProduct {dom} {cod} (spfdParClosureObj {dom} {cod} p q) p)
    q
spfdParEval {dom} {cod} p q =
  SPFDm (spfdParEvalPos {dom} {cod} p q) (spfdParEvalDir {dom} {cod} p q)

public export
spfdParCurryPos : {dom, cod : Type} ->
  {p, q, r : SPFData dom cod} ->
  SPFnt {dom} {cod} (spfdParProduct {dom} {cod} p q) r ->
  SPFntPos {dom} {cod} p (spfdParClosureObj {dom} {cod} q r)
spfdParCurryPos {dom} {cod} {p} {q} {r} m ec =
  spfdParCoprCurryPos {dom}
    {p=(SPFDataProdToFamUnit p ec)}
    {q=(SPFDataProdToFamUnit q ec)}
    {r=(SPFDataProdToFamUnit r ec)}
    (SPFDataProdToFamUnitNT (spfdParProduct p q) r m ec)
    ()

public export
spfdParCurryDir : {dom, cod : Type} ->
  {p, q, r : SPFData dom cod} ->
  (f : SPFnt {dom} {cod} (spfdParProduct {dom} {cod} p q) r) ->
  SPFntDir {dom} {cod}
    p
    (spfdParClosureObj {dom} {cod} q r)
    (spfdParCurryPos {dom} {cod} {p} {q} {r} f)
spfdParCurryDir {dom} {cod} {p} {q} {r} m ec =
  spfdParCoprCurryDir {dom}
    {p=(SPFDataProdToFamUnit p ec)}
    {q=(SPFDataProdToFamUnit q ec)}
    {r=(SPFDataProdToFamUnit r ec)}
    (SPFDataProdToFamUnitNT (spfdParProduct p q) r m ec)
    ()

public export
spfdParCurry : {dom, cod : Type} ->
  {p, q, r : SPFData dom cod} ->
  SPFnt {dom} {cod} (spfdParProduct {dom} {cod} p q) r ->
  SPFnt {dom} {cod} p (spfdParClosureObj {dom} {cod} q r)
spfdParCurry {dom} {cod} {p} {q} {r} m =
  SPFDm
    (spfdParCurryPos {dom} {cod} {p} {q} {r} m)
    (spfdParCurryDir {dom} {cod} {p} {q} {r} m)

----------------------------------------------
----------------------------------------------
---- Cartesian transformations and slices ----
----------------------------------------------
----------------------------------------------

-----------------------------------
---- Category-theoretic slices ----
-----------------------------------

public export
record SPFDcs {dom, cod : Type} (q : SPFData dom cod) where
  constructor SPDcs
  spdcsTot : SPFData dom cod
  spdcsProj : SPFnt {dom} {cod} spdcsTot q

--------------------------------------------
---- Category-theoretic position-slices ----
--------------------------------------------

-- For a polynomial functor `q : SPFData y z` and object `x : Type`,
-- we will refer to the slice category of `SPFData x z` over `q . 1(x,y)`
-- as `q`'s "`x`-position-slice category".
public export
SPFDposCS : {x, y, z : Type} -> SPFData y z -> Type
SPFDposCS {x} {y} {z} q = SPFDcs {dom=x} {cod=z} (spfdCompTerm {x} {y} {z} q)

-- Any composite polynomial functor `q . r` may be viewed in a canonical
-- way as an object of `q`'s position-slice category (i.e. the slice category
-- over `q . 1`).
public export
spfdCompPosCS : {x, y, z : Type} -> (q : SPFData y z) ->
  (r : SPFData x y) -> SPFDposCS {x} {y} {z} q
spfdCompPosCS {x} {y} {z} q r =
  SPDcs {dom=x} {cod=z} (SPFDcomp x y z q r) $ spfdCompToPosNT {x} {y} {z} q r

-- A utility function for a natural transformation whose codomain
-- is a functor composed after a terminal object.  Because an object
-- together with a natural transformation to it is an object of
-- the slice category over that object, and because a composition
-- after a terminal object has no directions, we call this a slice over
-- positions, or simply a position-slice.  We write "CSlice" here to
-- indicate that this is a category-theory-style slice (as opposed
-- to a dependent-type-style slice).
public export
spfdPosCSproj : {y, z : Type} -> SPFData y z -> SPFData y z -> Type
spfdPosCSproj {y} {z} q p =
  SPFnt {dom=y} {cod=z} p (spfdCompTerm {x=y} {y} {z} q)

public export
record SPFDposCSlice {y, z : Type} (q : SPFData y z) where
  constructor SPcs
  spcsTot : SPFData y z
  spcsProj : spfdPosCSproj {y} {z} q spcsTot

-- See formula 6.75 from the "General Theory of Interaction" book.
-- What is called `p` there is `spcsTot`, and what is called `f` there
-- is `spcsProj`.
--
-- An on-positions function induces an adjunction with the position-slice
-- category of the codomain.  Here we compute the total space of the
-- induced position-slice object.
public export
spfdInducedPosCSliceTotPos : {y, z : Type} ->
  (q : SPFData y z) -> (p : SPFDposCSlice {y} {z} q) ->
  SliceObj (y, z)
spfdInducedPosCSliceTotPos {y} {z} q p eyz =
  (i : spfdPos (spcsTot p) (snd eyz) **
   spfdDir q (snd eyz) (fst $ spOnPos (spcsProj p) (snd eyz) i) (fst eyz))

public export
spfdInducedPosCSliceTotDir : {y, z : Type} ->
  (q : SPFData y z) -> (p : SPFDposCSlice {y} {z} q) ->
  SPFdirType y (y, z) (spfdInducedPosCSliceTotPos {y} {z} q p)
spfdInducedPosCSliceTotDir {y} {z} q p eyz ppqd =
  spfdDir (spcsTot p) (snd eyz) (fst ppqd)

public export
spfdInducedPosCSliceTot : {y, z : Type} ->
  (q : SPFData y z) -> (p : SPFDposCSlice {y} {z} q) ->
  SPFData y (y, z)
spfdInducedPosCSliceTot {y} {z} q p =
  SPFD
     (spfdInducedPosCSliceTotPos {y} {z} q p)
     (spfdInducedPosCSliceTotDir {y} {z} q p)

-- This is the projection component of the slice object over
-- `q . 1` derived from `p`.  Note that we can express it as
-- a pushout cell (where the left-side vertical morphism is
-- `id`).
public export
spfdInducedPosCSliceProj : {y, z : Type} ->
  (q : SPFData y z) -> (p : SPFDposCSlice {y} {z} q) ->
  SPFpoCell {w=y} {w'=y} {z=(y, z)} {z'=z}
    Prelude.id Builtin.snd
    (spfdInducedPosCSliceTot {y} {z} q p)
    (spfdCompTerm {x=y} {y} {z} q)
spfdInducedPosCSliceProj {y} {z} q p =
  SPFDm
    (\ez, ppqd =>
      spOnPos (spcsProj p) ez $ rewrite sym (sfsEq ppqd) in fst $ sfsSnd ppqd)
    (\ez, ppqd, ey, pd =>
      void $ snd pd)

-- The adjoints of the position-slice adjunction induced by a
-- slice polynomial endofunctor `q : SPFData x x`.  The adjunction is between
-- `SPFDcat x x` on the left and the slice category of
-- `SPFDcat x x` over `spfdCompTerm q` (which we are calling the
-- "position-slice" category) on the right.  Below, `p` is an object of the
-- right (position-slice) category, and `r` an object of the left (base)
-- category.

public export
spfdPosSliceAdjL : {x, y, z : Type} -> (q : SPFData x x) ->
  (p : SPFDposCSlice {y=x} {z=x} q) -> SPFData x x
spfdPosSliceAdjL {x} q = spcsTot {y=x} {z=x} {q}

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
