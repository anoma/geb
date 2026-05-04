module LanguageDef.SlicePolyUMorph

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.InternalCat
import public LanguageDef.SlicePolyCat

%hide Library.IdrisCategories.BaseChangeF

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

public export
SPFDuPosToPiFRidL : FunExt -> {x, y : Type} -> (sl : SliceObj (x, y)) ->
  (sx : SliceObj x) ->
  SliceExtEq {a=y}
    {s=(SliceSigmaPiFR {c=x} {e=y} sl sx)}
    {s'=(SliceSigmaPiFR {c=x} {e=y} sl sx)}
    (sliceComp
      (SPFDuPosToPiFR {x}{y} sl sx)
      (SPFDuPosFromPiFR {x}{y} sl sx))
    (sliceId {a=y} (SliceSigmaPiFR {c=x} {e=y} sl sx))
SPFDuPosToPiFRidL fext {x} {y} sl sx ey eslx = funExt $ \(ex ** esl) => Refl

public export
SPFDuPosToPiFRidR : {x, y : Type} -> (sl : SliceObj (x, y)) ->
  (sx : SliceObj x) ->
  SliceExtEq {a=y}
    {s=(InterpSPFData {dom=x} {cod=y} (spfdPiFR {x} {y} sl) sx)}
    {s'=(InterpSPFData {dom=x} {cod=y} (spfdPiFR {x} {y} sl) sx)}
    (sliceComp
      (SPFDuPosFromPiFR {x}{y} sl sx)
      (SPFDuPosToPiFR {x}{y} sl sx))
    (sliceId {a=y} (InterpSPFData {dom=x} {cod=y} (spfdPiFR {x} {y} sl) sx))
SPFDuPosToPiFRidR {x} {y} sl sx ey (() ** esx) = Refl

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
SPFDdiagDirToPiFL : {x, y : Type} -> (sl : SliceObj (x, y)) ->
  SliceNatTrans {x=y} {y=x}
    (InterpSPFData {dom=y} {cod=x} $ spfdPiFL {x} {y} sl)
    (SliceSigmaPiFL {c=x} {e=y} sl)
SPFDdiagDirToPiFL {x} {y} sl sd ec =
  dpMapSnd $ \esl, m => m (fst esl) Refl

public export
SPFDdiagDirFromPiFL : {x, y : Type} -> (sl : SliceObj (x, y)) ->
  SliceNatTrans {x=y} {y=x}
    (SliceSigmaPiFL {c=x} {e=y} sl)
    (InterpSPFData {dom=y} {cod=x} $ spfdPiFL {x} {y} sl)
SPFDdiagDirFromPiFL {x} {y} sl sd ec =
  dpMapSnd $ \esl, esd, ey, eqy => rewrite sym eqy in esd

public export
SPFDdiagDirToPiFLidL : {x, y : Type} -> (sl : SliceObj (x, y)) ->
  (sy : SliceObj y) ->
  SliceExtEq {a=x}
    {s=(SliceSigmaPiFL {c=x} {e=y} sl sy)}
    {s'=(SliceSigmaPiFL {c=x} {e=y} sl sy)}
    (sliceComp
      (SPFDdiagDirToPiFL {x}{y} sl sy)
      (SPFDdiagDirFromPiFL {x}{y} sl sy))
    (sliceId {a=x} (SliceSigmaPiFL {c=x} {e=y} sl sy))
SPFDdiagDirToPiFLidL {x} {y} sl sy ex (esl ** esy) = Refl

public export
SPFDdiagDirToPiFLidR : FunExt -> {x, y : Type} -> (sl : SliceObj (x, y)) ->
  (sy : SliceObj y) ->
  SliceExtEq {a=x}
    {s=(InterpSPFData {dom=y} {cod=x} (spfdPiFL {x} {y} sl) sy)}
    {s'=(InterpSPFData {dom=y} {cod=x} (spfdPiFL {x} {y} sl) sy)}
    (sliceComp
      (SPFDdiagDirFromPiFL {x}{y} sl sy)
      (SPFDdiagDirToPiFL {x}{y} sl sy))
    (sliceId {a=x} (InterpSPFData {dom=y} {cod=x} (spfdPiFL {x} {y} sl) sy))
SPFDdiagDirToPiFLidR fext {x} {y} sl sy ex ((ey ** esl) ** esy) =
  dpEq12 Refl $ funExt $ \ey' => funExt $ \Refl => Refl

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
spfdPrecomp : {a, b, c : Type} -> (q : SPFData a c) ->
  SPFData c b -> SPFData a b
spfdPrecomp {a} {b} {c} = flip $ SPFDcomp a c b

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
spfdLKanExtR = spfdPrecomp

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

-------------------------
-------------------------
---- Density comonad ----
-------------------------
-------------------------

------------------------------------------
---- Definition as left Kan extension ----
------------------------------------------

public export
spfdDensityComonad : {a, b : Type} -> SPFData a b -> SPFData b b
spfdDensityComonad {a} {b} p = spfdLKanExt {a} {b} {c=b} p p

public export
spfdDensityComonadPos : {a, b : Type} -> SPFData a b -> SliceObj b
spfdDensityComonadPos {a} {b} p = spfdPos (spfdDensityComonad {a} {b} p)

public export
spfdDensityComonadDir : {a, b : Type} -> (p : SPFData a b) ->
  (eb : b) -> (i : spfdDensityComonadPos {a} {b} p eb) -> SliceObj b
spfdDensityComonadDir {a} {b} p = spfdDir (spfdDensityComonad {a} {b} p)

public export
spfdDensityComonadLAdj : {a, b : Type} ->
  {p : SPFData a b} -> {r : SPFData b b} ->
  SPFnt {dom=b} {cod=b} (spfdDensityComonad {a} {b} p) r ->
  SPFnt {dom=a} {cod=b} p (SPFDcomp a b b r p)
spfdDensityComonadLAdj {a} {b} {p} {r} = spfdLKanExtLAdj {a} {b} {c=b} p p r

public export
spfdDensityComonadRAdj : {a, b : Type} ->
  {p : SPFData a b} -> {r : SPFData b b} ->
  SPFnt {dom=a} {cod=b} p (SPFDcomp a b b r p) ->
  SPFnt {dom=b} {cod=b} (spfdDensityComonad {a} {b} p) r
spfdDensityComonadRAdj {a} {b} {p} {r} = spfdLKanExtRAdj {a} {b} {c=b} p p r

------------------------------------------
---- Compositions of density comonads ----
------------------------------------------

-- Convenience routines for two ways of iterating the density comonad:
-- composing it with itself, and taking the density comonad _of_ the
-- density comonad.  The former is a composition within the category
-- of slice polynomial functors, while the second is a composition in
-- the metalanguage (`Type`).
public export
spfdDensityComonadSelfComposed : {a, b : Type} -> (p : SPFData a b) ->
  SPFData b b
spfdDensityComonadSelfComposed {a} {b} p =
  (SPFDcomp b b b
    (spfdDensityComonad {a} {b} p)
    (spfdDensityComonad {a} {b} p))

public export
spfdDensityComonadOfDensityComonad : {a, b : Type} -> (p : SPFData a b) ->
  SPFData b b
spfdDensityComonadOfDensityComonad {a} {b} =
  spfdDensityComonad {a=b} {b} . spfdDensityComonad {a} {b}

----------------------------
---- Comonad operations ----
----------------------------

public export
spfdDensityComonadErase : {a, b : Type} -> (p : SPFData a b) ->
  SPFnt {dom=b} {cod=b} (spfdDensityComonad {a} {b} p) (SPFDid b)
spfdDensityComonadErase {a} {b} p =
  SPFDm
    (\_, _ => ())
    (\eb, ep, eb', beq =>
      rewrite sym beq in
      (ep ** sliceId {a} $ spfdDir p eb ep))

public export
spfdDensityComonadDuplicate : {a, b : Type} -> (p : SPFData a b) ->
  SPFnt {dom=b} {cod=b}
    (spfdDensityComonad {a} {b} p)
    (spfdDensityComonadSelfComposed {a} {b} p)
spfdDensityComonadDuplicate {a} {b} p =
  SPFDm
    (\eb, ep =>
      (ep ** (\eb', ep'dm => fst ep'dm)))
    (\eb, ep, eb', dm =>
      (fst (snd dm) ** \ea, pd' => snd (snd $ fst dm) ea $ snd (snd dm) ea pd'))

----------------------------------------
---- Adjuncts of comonad operations ----
----------------------------------------

-- Applying the adjuncts of the left-Kan-extension adjunction to the
-- comonad operations of the density comonad yields two more natural
-- transformations, one an endo-natural-transformation on `p`, which we
-- shall see below is the identity, and one from the density comonad of
-- the density comonad of `p` back to the density comonad of `p`.

public export
spfdDensityComonadEraseAdj : {a, b : Type} ->
  (p : SPFData a b) ->
  SPFnt {dom=a} {cod=b} p p
spfdDensityComonadEraseAdj {a} {b} p =
  SPNTvcomp p (SPFDcomp a b b (SPFDid b) p) p
    (SPFfromIdL p)
    (spfdDensityComonadLAdj {a} {b} {p} {r=(SPFDid b)}
      (spfdDensityComonadErase {a} {b} p))

public export
spfdDensityComonadDuplicateAdj : {a, b : Type} ->
  (p : SPFData a b) ->
  SPFnt {dom=b} {cod=b}
    (spfdDensityComonadOfDensityComonad {a} {b} p)
    (spfdDensityComonad {a} {b} p)
spfdDensityComonadDuplicateAdj {a} {b} p =
  spfdDensityComonadRAdj {a=b} {b}
    {p=(spfdDensityComonad {a} {b} p)} {r=(spfdDensityComonad {a} {b} p)}
    (spfdDensityComonadDuplicate {a} {b} p)

----------------------------------------------------------
---- Explicit formulas for density comonad operations ----
----------------------------------------------------------

-- Here we show that the adjunct of the `erase` of the codensity monad is
-- simply the identity.

public export
0 spfdDensityComonadEraseAdjIdPos : {a, b : Type} ->
  (p : SPFData a b) ->
  spOnPos (spfdDensityComonadEraseAdj {a} {b} p) = spOnPos (SPNTid p)
spfdDensityComonadEraseAdjIdPos {a} {b} p = Refl

public export
0 spfdDensityComonadEraseAdjIdDir : FunExt -> {a, b : Type} ->
  (p : SPFData a b) ->
  spOnDir (spfdDensityComonadEraseAdj {a} {b} p) = spOnDir (SPNTid p)
spfdDensityComonadEraseAdjIdDir fext {a} {b} (SPFD ppos pdir) =
  funExt $ \eb => funExt $ \ep => Refl

public export
0 spfdDensityComonadEraseAdjInterpId : FunExt -> {a, b : Type} ->
  (p : SPFData a b) -> (x : SliceObj a) ->
  InterpSPFnt {dom=a} {cod=b} p p (spfdDensityComonadEraseAdj {a} {b} p) x =
  sliceId {a=b} (InterpSPFData {dom=a} {cod=b} p x)
spfdDensityComonadEraseAdjInterpId fext {a} {b} (SPFD ppos pdir) x =
  funExt $ \eb => funExt $ \(ep ** dm) => Refl

-- To clarify how we will use the density comonad, we exhibit explicit
-- formulas for some forms in which it will appear.

-- The positions of a density comonad are those of the original functor.
public export
0 spfdDensityComonadPosIsFPos : {a, b : Type} -> (p : SPFData a b) ->
  spfdDensityComonadPos {a} {b} p = spfdPos p
spfdDensityComonadPosIsFPos {a} {b} p = Refl

-- A direction of a density comonad at a given position comprises a choice
-- of another position together with a morphism from the direction-set of the
-- the original functor at the chosen position back to the direction-set of the
-- original functor at the given position.  That is precisely what we have
-- called a generalized element of the given position.
public export
0 spfdDensityComonadDirIsFDirMorph : {a, b : Type} -> (p : SPFData a b) ->
  (eb : b) -> (ep : spfdPos p eb) -> (eb' : b) ->
  spfdDensityComonadDir {a} {b} p eb ep eb' =
    spfdDirGenElCod {dom=a} {cod=b} p (eb ** ep) eb'
spfdDensityComonadDirIsFDirMorph {a} {b} p eb ep eb' = Refl

-- The positions of the composition of the density comonad of a functor
-- composed with itself (i.e. the multiplication in the composition monoid on
-- `SPFData b b`).
public export
0 spfdDensityComonadSelfComposedDensityComonadPosIsFPos : {a, b : Type} ->
  (p : SPFData a b) -> (eb : b) ->
  spfdPos (spfdDensityComonadSelfComposed {a} {b} p) eb =
    (ep : spfdPos p eb **
     SliceMorphism {a=b}
      (spfdDirGenElCod {dom=a} {cod=b} p (eb ** ep))
      (spfdPos p))
spfdDensityComonadSelfComposedDensityComonadPosIsFPos {a} {b} p eb =
  Refl

-- The directions of the composition of the density comonad of a functor
-- composed with itself.
public export
0 spfdDensityComonadSelfComposedDir : {a, b : Type} ->
  (p : SPFData a b) ->
  (eb : b) -> (ep : spfdPos p eb) ->
  (mep :
    SliceMorphism {a=b}
      (spfdDirGenElCod {dom=a} {cod=b} p (eb ** ep))
      (spfdPos p)) ->
  (eb' : b) ->
  spfdDir (spfdDensityComonadSelfComposed {a} {b} p) eb (ep ** mep) eb' =
    (d1 : spfdDirGenEl {dom=a} {cod=b} p (eb ** ep) **
     spfdDirGenElCod {dom=a} {cod=b} p (fst d1 ** mep (fst d1) (snd d1)) eb')
spfdDensityComonadSelfComposedDir {a} {b} p eb ep mep eb' = Refl

-- The positions of the density comonad of a codensity monad of
-- a functor are those of the original functor.
public export
0 spfdDensityComonadOfDensityComonadPosIsFPos : {a, b : Type} ->
  (p : SPFData a b) ->
  spfdPos (spfdDensityComonadOfDensityComonad {a} {b} p) = spfdPos p
spfdDensityComonadOfDensityComonadPosIsFPos {a} {b} p = Refl

-- The directions of the density comonad of a codensity monad.
-- A position is simply a position of the original functor,
-- and the direction-set at that position is a choice of another
-- position together with a morphism (in the codomain slice category)
-- from the set of all generalized elements of the chosen position
-- back to the set of all generalized elements of the given position.
-- In other words, it is a function on generalized elements (where
-- generalized elements are themselves functions, between direction-sets).
public export
0 spfdDensityComonadOfDensityComonadDir : {a, b : Type} ->
  (p : SPFData a b) ->
  (eb : b) -> (ep : spfdPos p eb) -> (eb' : b) ->
  spfdDir (spfdDensityComonadOfDensityComonad {a} {b} p) eb ep eb' =
  (ep' : spfdPos p eb' **
   SliceMorphism {a=b}
    (spfdDirGenElCod {dom=a} {cod=b} p (eb' ** ep'))
    (spfdDirGenElCod {dom=a} {cod=b} p (eb ** ep)))
spfdDensityComonadOfDensityComonadDir {a} {b} p eb ep eb' = Refl

-- Another way of expressing the directions of the codensity monad of a
-- codensity monad is that a direction-set comprises a generalized element
-- of the codensity monad of the original functor.
public export
0 spfdDensityComonadOfDensityComonadDirAsGenEl : {a, b : Type} ->
  (p : SPFData a b) ->
  (eb : b) -> (ep : spfdPos p eb) -> (eb' : b) ->
  spfdDir (spfdDensityComonadOfDensityComonad {a} {b} p) eb ep eb' =
  spfdDirGenElCod {dom=b} {cod=b} (spfdDensityComonad {a} {b} p) (eb ** ep) eb'
spfdDensityComonadOfDensityComonadDirAsGenEl {a} {b} p eb ep eb' = Refl

-- Now we characterize the adjunct of "duplicate" (which has the same
-- signature as a "join").  First, we show that it is vertical:  its
-- on-positions function is the identity (on positions of the original functor).
-- This means that for each position of the original functor, the
-- on-directions function maps a generalized element of that position
-- to a function on generalized elements whose codomain is the set of
-- all generalized elements of that position.
public export
0 spfdDensityComonadDuplicateAdjIdPos : {a, b : Type} -> (p : SPFData a b) ->
  SliceExtEq {a=b}
    (spOnPos $ spfdDensityComonadDuplicateAdj {a} {b} p)
    (sliceId $ spfdPos p)
spfdDensityComonadDuplicateAdjIdPos {a} {b} (SPFD ppos pdir) eb ep = Refl

-- Now, we see that the input parameters to the on-directions function of
-- the adjunct of "duplicate" at a given position comprise precisely what we
-- have called a generalized element of that position.  (This is because the
-- input comes from a direction-set of the codensity monad of the original
-- functor.)
--
-- The _output_ of the adjunct of "duplicate", which is in a direction-set of
-- the codensity monad of the codensity monad, is a function _on_ generalized
-- elements.  Thus, it takes generalized elements to functions on generalized
-- elements -- and hence we could view it as the curried form of a function
-- which takes pairs of generalized elements to single generalized elements.
-- We now attempt to characterize the behavior of this function.
--
-- First, we observe that the source position chosen by the adjunct is
-- always simply the same as the source position of the input generalized
-- element.
public export
0 spfdDensityComonadDuplicateAdjDirFstId :
  {a, b : Type} -> (p : SPFData a b) ->
  (eb : b) -> (ep : spfdPos p eb) ->
  (eb' : b) -> (el : spfdDirGenElCod {dom=a} {cod=b} p (eb ** ep) eb') ->
  fst (spOnDir (spfdDensityComonadDuplicateAdj {a} {b} p) eb ep eb' el) =
    fst el
spfdDensityComonadDuplicateAdjDirFstId {a} {b} p eb ep eb' el = Refl

-- Next, we observe that the source position of the output of the function
-- on generalized elements chosen by the adjunct is always the same as the
-- source position of _its_ input generalized element (which is not necessarily
-- the same as that of the generalized element which was input to the
-- on-directions function itself, which returned the function on generalized
-- elements).
public export
0 spfdDensityComonadDuplicateAdjDirSndId :
  {a, b : Type} -> (p : SPFData a b) ->
  (eb : b) -> (ep : spfdPos p eb) ->
  (eb' : b) ->
  (el : spfdDirGenElCod {dom=a} {cod=b} p (eb ** ep) eb') ->
  (eb'' : b) ->
  (el' : spfdDirGenElCod {dom=a} {cod=b} p (eb' ** fst el) eb'') ->
  fst
    (snd (spOnDir (spfdDensityComonadDuplicateAdj {a} {b} p) eb ep eb' el)
      eb'' el') =
  fst el'
spfdDensityComonadDuplicateAdjDirSndId {a} {b} p eb ep eb' el eb'' el' = Refl

-- Finally, we observe that the action of the function on generalized
-- elements chosen by the adjunct is to compose the two functions contained
-- within the two generalized elements that comprise the parameters of
-- its uncurried form.
public export
0 spfdDensityComonadDuplicateAdjDirIsComp :
  {a, b : Type} -> (p : SPFData a b) ->
  (eb : b) -> (ep : spfdPos p eb) ->
  (eb' : b) ->
  (el : spfdDirGenElCod {dom=a} {cod=b} p (eb ** ep) eb') ->
  (eb'' : b) ->
  (el' : spfdDirGenElCod {dom=a} {cod=b} p (eb' ** fst el) eb'') ->
  snd
    (snd (spOnDir (spfdDensityComonadDuplicateAdj {a} {b} p) eb ep eb' el)
      eb'' el') =
  sliceComp {a}
    {x=(spfdDir p eb'' (fst el'))}
    {y=(spfdDir p eb' (fst el))}
    {z=(spfdDir p eb ep)}
    (snd el)
    (snd el')
spfdDensityComonadDuplicateAdjDirIsComp {a} {b} p eb ep eb' el eb'' el' = Refl

-- Thus, we can summarize the action of the adjunct of the "duplicate" of
-- the polynomial density comonad as follows:

-- 1) The on-positions function is simply the identity on the position-set
--    of the original functor, so for each position, we have one on-directions
--    function, from the direction-set of the density comonad at that
--    position to the direction-set of the density comonad of the density
--    comonad at that position.
-- 2) For a given position `i`, the on-directions function is effectively
--    the curried form of an argument which takes a generalized element `el`
--    of `i` -- that is, another position `j` and a function from the
--    direction-set of `j` to the direction-set of `i` -- and a generalized
--    element `el'` of `j` -- that is, another position `k` and a function
--    from the direction-set of `k` to the direction-set of `j` -- and
--    returns the composed function from the direction-set of `k` to the
--    direction-set of `i` (which we therefore also call a generalized
--    element of `i`).

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
  (SPFndDataFam b dom cod) -> SPFData dom cod
spfdSetProduct {b} {dom} {cod} =
  spfdPostcompPi snd . SPFDataFamToProd {b} {dom} {cod}

public export
spfdSetProductIntro : {b, dom, cod : Type} ->
  {x : SPFData dom cod} -> {y : SPFndDataFam b dom cod} ->
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
  (sf : SPFndDataFam b dom cod) -> (eb : b) ->
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
  (SPFndDataFam b dom cod) -> SPFData dom cod
spfdSetCoproduct {b} {dom} {cod} =
  spfdPostcompSigma snd . SPFDataFamToProd {b} {dom} {cod}

public export
spfdSetCoproductInj : {b, dom, cod : Type} ->
  (sf : SPFndDataFam b dom cod) -> (eb : b) ->
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
  {x : SPFndDataFam b dom cod} -> {y : SPFData dom cod} ->
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
  (SPFndDataFam b dom cod) -> SliceObj cod
spfdSetParProductPos {b} {dom} {cod} sf ec =
  Pi {a=b} $ \eb => spfdPos (sf eb) ec

public export
spfdSetParProductDir : {b, dom, cod : Type} ->
  (sf : SPFndDataFam b dom cod) ->
  SPFdirType dom cod (spfdSetParProductPos {b} {dom} {cod} sf)
spfdSetParProductDir {b} {dom} {cod} sf ec ep ed =
  Pi {a=b} $ \eb => spfdDir (sf eb) ec (ep eb) ed

public export
spfdSetParProduct : {b, dom, cod : Type} ->
  (SPFndDataFam b dom cod) -> SPFData dom cod
spfdSetParProduct {b} {dom} {cod} sf =
  SPFD
    (spfdSetParProductPos {b} {dom} {cod} sf)
    (spfdSetParProductDir {b} {dom} {cod} sf)

public export
spfdSetParProductIntro : {b, dom, cod : Type} ->
  {sf, sf' : SPFndDataFam b dom cod} ->
  ((eb : b) -> SPFnt {dom} {cod} (sf eb) (sf' eb)) ->
  SPFnt {dom} {cod}
    (spfdSetParProduct {b} {dom} {cod} sf)
    (spfdSetParProduct {b} {dom} {cod} sf')
spfdSetParProductIntro {b} {dom} {cod} {sf} {sf'} ntf =
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
spfdParProductIntro : {dom, cod : Type} ->
  {p, p', q, q' : SPFData dom cod} ->
  SPFnt {dom} {cod} p p' ->
  SPFnt {dom} {cod} q q' ->
  SPFnt {dom} {cod}
    (spfdParProduct {dom} {cod} p q)
    (spfdParProduct {dom} {cod} p' q')
spfdParProductIntro {dom} {cod} {p} {p'} {q} {q'} f g =
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

-- See formula 5.28 in "Polynomial Functors: A Mathematical Theory
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
    with (snd qpdm ed qd)
  spfdParRepEvalDir {dom} p q () ((qp ** dm), ()) ed qd | ((), pd) =
    (((ed ** qd) ** Left $ rewrite unitUnique (fst $ dm ed qd) () in Refl), pd)

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

--------------------------------------------------------------------------
--------------------------------------------------------------------------
---- Parallel product closure as generator of natural transformations ----
--------------------------------------------------------------------------
--------------------------------------------------------------------------

-- For two slice polynomials `SPFData : dom Unit`, the position-set of the
-- parallel closure object is the the set of natural transformations between
-- the two functors.  See formula 4.79 in _Polynomial Functors:  A Mathematical
-- Theory of Interaction_.

-- We begin with the copresheaf case.

public export
spfdParCoprHomObjPosToNT : {dom : Type} ->
  (q, r : SPFData dom Unit) ->
  spfdParCoprHomObjPos {dom} q r () -> SPFnt {dom} {cod=Unit} q r
spfdParCoprHomObjPosToNT {dom} q r (() ** pm) =
  SPFDm
    (\(), qi => fst $ pm (qi, ()) Refl)
    (\(), qi, ed, rd => snd $ snd (pm (qi, ()) Refl) ed rd)

public export
spfdParCoprHomObjPosFromNT : {dom : Type} ->
  (q, r : SPFData dom Unit) ->
  SPFnt {dom} {cod=Unit} q r -> spfdParCoprHomObjPos {dom} q r ()
spfdParCoprHomObjPosFromNT {dom} q r nt =
  (() **
   \(qi, ()), Refl =>
    (spOnPos nt () qi ** \ed, rd => ((), spOnDir nt () qi ed rd)))

-- Now we show the general case.

public export
spfdParClosureObjPosToNT : {dom, cod : Type} ->
  (q, r : SPFData dom cod) ->
  (ec : cod) ->
  spfdParClosureObjPos {dom} q r ec ->
  SPFnt {dom} {cod=Unit}
    (SPFDataProdToFamUnit q ec)
    (SPFDataProdToFamUnit r ec)
spfdParClosureObjPosToNT {dom} q r ec =
  spfdParCoprHomObjPosToNT {dom}
    (SPFDataProdToFamUnit q ec)
    (SPFDataProdToFamUnit r ec)

public export
spfdParClosureObjPiPosToNT : {dom, cod : Type} ->
  (q, r : SPFData dom cod) ->
  Pi {a=cod} (spfdParClosureObjPos {dom} q r) ->
  SPFnt {dom} {cod} q r
spfdParClosureObjPiPosToNT {dom} q@(SPFD qpos qdir) r@(SPFD rpos rdir) ifam =
  SPFDataFamToProdUnitNT
    (SPFDataProdToFamUnit q)
    (SPFDataProdToFamUnit r)
    (\ec => spfdParClosureObjPosToNT {dom} {cod} q r ec (ifam ec))

public export
spfdParClosureObjSpfPiPosToNT : {dom, cod : Type} ->
  (q, r : SPFData dom cod) ->
  spfdPos
    (spfPiPos {x=dom} {y=Unit} {z=cod}
      (\_ => ())
      (spfdParClosureObj {dom} {cod} q r))
    () ->
  SPFnt {dom} {cod} q r
spfdParClosureObjSpfPiPosToNT {dom} {cod} q r pip =
  spfdParClosureObjPiPosToNT {dom} {cod} q r $
    \ec => (() ** \(qp, ()), Refl => snd (pip $ SFS ec ()) (qp, ()) Refl)

public export
spfdParClosureObjPosFromNT : {dom, cod : Type} ->
  (q, r : SPFData dom cod) ->
  (ec : cod) ->
  SPFnt {dom} {cod=Unit}
    (SPFDataProdToFamUnit q ec)
    (SPFDataProdToFamUnit r ec) ->
  spfdParClosureObjPos {dom} q r ec
spfdParClosureObjPosFromNT {dom} q r ec =
  spfdParCoprHomObjPosFromNT {dom}
    (SPFDataProdToFamUnit q ec)
    (SPFDataProdToFamUnit r ec)

public export
spfdParClosureObjPiPosFromNT : {dom, cod : Type} ->
  (q, r : SPFData dom cod) ->
  SPFnt {dom} {cod} q r ->
  Pi {a=cod} (spfdParClosureObjPos {dom} q r)
spfdParClosureObjPiPosFromNT {dom} q r nt ec =
  spfdParClosureObjPosFromNT q r ec $ SPFDataProdToFamUnitNT q r nt ec

public export
spfdParClosureObjSpfPiPosFromNT : {dom, cod : Type} ->
  (q, r : SPFData dom cod) ->
  SPFnt {dom} {cod} q r ->
  spfdPos
    (spfPiPos {x=dom} {y=Unit} {z=cod}
      (\_ => ())
      (spfdParClosureObj {dom} {cod} q r))
    ()
spfdParClosureObjSpfPiPosFromNT {dom} {cod} q r nt (SFS ec ()) =
  spfdParClosureObjPiPosFromNT {dom} {cod} q r nt ec

-- Now we show that the direction-set of the parallel closure at a given
-- position is the direction-set of the intermediate object of the
-- vertical-Cartesian factorization of the corresponding natural transformation.

public export
spfdParClosureObjDirToIntDir : {dom, cod : Type} ->
  (q, r : SPFData dom cod) ->
  (ed : dom) -> (ec : cod) ->
  (i : spfdParClosureObjPos {dom} q r ec) ->
  spfdParClosureObjDir {dom} q r ec i ed ->
  SPFDvcFactIntTot {dom} {cod=Unit}
    {p=(SPFDataProdToFamUnit q ec)}
    {q=(SPFDataProdToFamUnit r ec)}
    (spfdParClosureObjPosToNT {dom} {cod} q r ec i) ed ()
spfdParClosureObjDirToIntDir {dom} {cod} q r ed ec
    (() ** dm) (((qp, ()) ** Refl) ** ((ed' ** rd) ** dd))
    with (fst (snd (dm (qp, ()) Refl) ed' rd))
  spfdParClosureObjDirToIntDir {dom} {cod} q r ed ec
    (() ** dm) (((qp, ()) ** Refl) ** ((ed' ** rd) ** dd)) | () =
      case dd of
        Left Refl => (qp ** rd)
        Right v => void v

public export
spfdParClosureObjDirFromIntDir : {dom, cod : Type} ->
  (q, r : SPFData dom cod) ->
  (ed : dom) -> (ec : cod) ->
  (i : spfdParClosureObjPos {dom} q r ec) ->
  SPFDvcFactIntTot {dom} {cod=Unit}
    {p=(SPFDataProdToFamUnit q ec)}
    {q=(SPFDataProdToFamUnit r ec)}
    (spfdParClosureObjPosToNT {dom} {cod} q r ec i) ed () ->
  spfdParClosureObjDir {dom} q r ec i ed
spfdParClosureObjDirFromIntDir {dom} {cod} q r ed ec (() ** dm) (qp ** rd)
    with (dm (qp, ()) Refl) proof eq
  spfdParClosureObjDirFromIntDir {dom} {cod} q r ed ec (() ** dm) (qp ** rd)
    | (rp ** rqd) =
      (((qp, ()) ** Refl) **
       rewrite eq in
       ((ed ** rd) ** Left $ rewrite unitUnique (fst (rqd ed rd)) () in Refl))

------------------------------------------
------------------------------------------
---- Translation and scaling functors ----
------------------------------------------
------------------------------------------

-- We call this functor "translate" since it adds a constant to the
-- input functor.
public export
spfdTranslate : {dom, cod : Type} ->
  SPFData dom cod -> SliceObj cod -> SPFData dom cod
spfdTranslate {dom} {cod} f a =
  spfdCoproduct {dom} {cod} (SPFDataConst {cod} dom a) f

public export
spfdTranslateTerminal : {dom, cod : Type} ->
  SPFData dom cod -> SPFData dom cod
spfdTranslateTerminal {dom} {cod} f =
  spfdTranslate {dom} {cod} f (SliceObjTerminal cod)

-- We call this functor "scale" since it multiplies a constant by the
-- input functor.
public export
spfdScale : {dom, cod : Type} ->
  SPFData dom cod -> SliceObj cod -> SPFData dom cod
spfdScale {dom} {cod} f a =
  spfdProduct {dom} {cod} (SPFDataConst {cod} dom a) f

----------------------------------------
----------------------------------------
---- Pointed and copointed functors ----
----------------------------------------
----------------------------------------

-- We may call this the "free pointed" endofunctor of a given endofunctor, since
-- we are adjoining to it a natural transformation from the identity functor.
-- (See https://ncatlab.org/nlab/show/pointed+endofunctor .)
public export
spfdFreePointed : {x : Type} -> (f : SPFData x x) -> SPFData x x
spfdFreePointed {x} = spfdCoproduct {dom=x} {cod=x} (SPFDid x)

public export
spfdFreePointedUnit : {x : Type} ->
  (f : SPFData x x) ->
  SPFnt {dom=x} {cod=x} (SPFDid x) (spfdFreePointed {x} f)
spfdFreePointedUnit {x} f = SPFDm (\_, _ => Left ()) (\_, (), _ => id)

-- We may this the "cofree copointed" functor of a given endofunctor, since
-- we are adjoining to it a natural transformation to the identity functor.
-- (See https://ncatlab.org/nlab/show/copointed+endofunctor .)
public export
spfdCofreeCopointed : {x : Type} -> (f : SPFData x x) -> SPFData x x
spfdCofreeCopointed {x} = spfdProduct {dom=x} {cod=x} (SPFDid x)

public export
spfdCofreeCopointedCounit : {x : Type} ->
  (f : SPFData x x) ->
  SPFnt {dom=x} {cod=x} (spfdCofreeCopointed {x} f) (SPFDid x)
spfdCofreeCopointedCounit {x} f =
  SPFDm (\_, _ => ()) (\ex, ((), ep), ex, Refl => Left Refl)

-----------------------------
-----------------------------
---- Horizontal products ----
-----------------------------
-----------------------------

-- Products in the horizontal category of the double category of slice
-- polynomial functors (i.e. the one where the objects are the slice polynomial
-- functors, the morphisms are the cells, and the composition is cell
-- vertical composition).

public export
spfdHProdProj1 : (a, b : Type) -> SPFData (a, b) a
spfdHProdProj1 a b = SPFDsigma fst

public export
spfdHProdProj2 : (a, b : Type) -> SPFData (a, b) b
spfdHProdProj2 a b = SPFDsigma snd

public export
spfdHProdIntro : {a, b, b' : Type} ->
  SPFData a b -> SPFData a b' -> SPFData a (b, b')
spfdHProdIntro {a} {b} {b'} f g =
  SPFD
    (\(eb, eb') => (spfdPos f eb, spfdPos g eb'))
    (\(eb, eb'), (efp, egp), ea => (spfdDir f eb efp ea, spfdDir g eb' egp ea))

-------------------------
-------------------------
---- Higher products ----
-------------------------
-------------------------

-- `SliceObj (Either a b)` is equivalent to `(SliceObj a, SliceObj b)`,
-- so we can postcompose projections after functors whose codomains
-- are of `Either` types.

public export
spfdPostProj1 : {x, y, z : Type} -> SPFData x (Either y z) -> SPFData x y
spfdPostProj1 {x} {y} f = SPFD (spfdPos f . Left) (\ey => spfdDir f (Left ey))

public export
spfdPostProj2 : {x, y, z : Type} -> SPFData x (Either y z) -> SPFData x z
spfdPostProj2 {x} {y} f = SPFD (spfdPos f . Right) (\ez => spfdDir f (Right ez))

public export
spfdProdIntroCod : {x, y, z : Type} ->
  SPFData x y -> SPFData x z -> SPFData x (Either y z)
spfdProdIntroCod {x} {y} {z} f g =
  SPFD
    (eitherElim (spfdPos f) (spfdPos g))
    (\eyz => case eyz of Left ey => spfdDir f ey ; Right ez => spfdDir g ez)

---------------------------------------------------------
---------------------------------------------------------
---- Higher-order postcomposition polynomial functor ----
---------------------------------------------------------
---------------------------------------------------------

-- A wrapper around `SPFDcompDir` which operates on the pre-composed
-- functor's direction-type in its alternate `SPFdirSl` form (rather
-- than `SPFdirType`).
public export
SPFDcompDirSl : {x, y, z : Type} -> (f : SPFData y z) ->
  (fmpos : SliceObj y) ->
  SPFdirSl x y fmpos ->
  SPFdirSl x z (SPFDcompPosSl f fmpos)
SPFDcompDirSl {x} {y} {z} f fmpos dir =
  SPFdirToSl $ SPFDcompDir f (SPFD fmpos (SPFdirFromSl dir))

-- Next we internalize `SPFDcompDirSl` -- meaning,
-- given that `SPFDcompDirSl` maps slice objects to
-- slice objects (specifically, slices over `SPFdirSlBase x y fmpos`
-- to slices over `SPFdirSlBase x z (SPFDcompPosSl f fmpos)`),
-- we exhibit an `SPFData` whose interpretation is precisely
-- `SPFDcompDirSl`.  (Note that the internalization of `SPFDcompPosSl f`,
-- as a functor between slice objects representing position-types, is
-- simply `f` itself!  This makes sense because for any polynomial functor
-- `p`, the position-type of `f . p` depends only on the position-type
-- of `p`, not on its direction-type.  It does depend on both the position-type
-- and the direction-type of `f`.)
--
-- This is the position-type of the polynomial internalization of
-- `SPFDcompDirSl`.
public export
SPFDcompDirSPFDpos : {x : Type} -> (f : SPFData x x) ->
  (fmpos : SliceObj x) ->
  SPFdirSl x x (SPFDcompPosSl f fmpos)
SPFDcompDirSPFDpos {x} (SPFD fpos fdir) fmpos ((ec ** ep ** dm), ed) =
  (ex : x ** fdir ec ep ex)

-- This is the direction-type of the polynomial internalization of
-- `SPFDcompDirSl`.
public export
SPFDcompDirSPFDdir : {x : Type} -> (f : SPFData x x) ->
  (fmpos : SliceObj x) ->
  SPFdirType
    (SPFdirSlBase x x fmpos)
    (SPFdirSlBase x x (SPFDcompPosSl f fmpos))
    (SPFDcompDirSPFDpos {x} f fmpos)
SPFDcompDirSPFDdir {x} (SPFD fpos fdir) fmpos
  ((ec ** ep ** dm), ed) (ex ** fd) ((ec' ** efmp), ed') =
    (eceq : ec' = ex ** edeq : ed' = ed ** dm ex fd = efmp)

-- Now that we have defined both position and the direction types, we
-- can define the polynomial internalization of `SPFDcompDirSl`.
public export
SPFDcompDirSPFD : {x : Type} -> (f : SPFData x x) ->
  (fmpos : SliceObj x) ->
  SPFData
    (SPFdirSlBase x x fmpos)
    (SPFdirSlBase x x (SPFDcompPosSl f fmpos))
SPFDcompDirSPFD {x} f fmpos =
  SPFD
    (SPFDcompDirSPFDpos {x} f fmpos)
    (SPFDcompDirSPFDdir {x} f fmpos)

-- Next we demonstrate that `SPFDcompDirSPFD` _is_ a correct
-- internalization of `SPFDcompDirSl`, by showing inverse natural
-- transformations between the latter and the interpetation of the
-- former.

public export
InterpSPFDcompDirSPFD : {x : Type} -> (f : SPFData x x) ->
  (fmpos : SliceObj x) ->
  SPFdirSl x x fmpos ->
  SPFdirSl x x (SPFDcompPosSl f fmpos)
InterpSPFDcompDirSPFD {x} f fmpos =
  InterpSPFData (SPFDcompDirSPFD f fmpos)

public export
SPFDcompDirSPFDtoF : {x : Type} -> (f : SPFData x x) ->
  (fmpos : SliceObj x) ->
  SliceNatTrans
    {x=(SPFdirSlBase x x fmpos)}
    {y=(SPFdirSlBase x x (SPFDcompPosSl f fmpos))}
    (InterpSPFDcompDirSPFD {x} f fmpos)
    (SPFDcompDirSl {x} f fmpos)
SPFDcompDirSPFDtoF {x} (SPFD fpos fdir) fmpos sl
  ((ec ** ep ** fdmp), ed) ((ex ** efd) ** sldm) =
    ((ex ** efd) ** sldm ((ex ** fdmp ex efd), ed) (Refl ** Refl ** Refl))

public export
SPFDcompDirSPFDfromF : {x : Type} -> (f : SPFData x x) ->
  (fmpos : SliceObj x) ->
  SliceNatTrans
    {x=(SPFdirSlBase x x fmpos)}
    {y=(SPFdirSlBase x x (SPFDcompPosSl f fmpos))}
    (SPFDcompDirSl {x} f fmpos)
    (InterpSPFDcompDirSPFD {x} f fmpos)
SPFDcompDirSPFDfromF {x} (SPFD fpos fdir) fmpos sl
  ((ec ** ep ** dm), ed) ((ex ** dd) ** esl) =
    ((ex ** dd) **
     \((ec ** ep), ed), (Refl ** Refl ** Refl) => esl)

-- Given an endofunctor `f` and a position-type `fmpos`, this produces the
-- type of positions of the free pointed functor of the functor resulting
-- from composing `f` after a functor with positions `fmpos`.
public export
SPFDcompPosPointedSl : {x : Type} ->
  SPFData x x -> SliceObj x -> SliceObj x
SPFDcompPosPointedSl g fmpos ec =
  Either (SPFDidPos x ec) (SPFDcompPosSl {y=x} {z=x} g fmpos ec)

-- Now we show that `spfdTranslateTerminal f` is an internalization
-- of `SPFDcompPosPointedSl`:  that is, the interpretation of the
-- former is naturally isomorphic to the latter.

public export
SPFDfmDirAlgBaseFdirPosBaseAlgPointed : {x : Type} -> {f : SPFData x x} ->
  {pos : SliceObj x} ->
  SliceMorphism {a=x} (SPFDcompPosPointedSl {x} f pos) pos ->
  SliceMorphism {a=x}
    (InterpSPFData (spfdTranslateTerminal {dom=x} {cod=x} f) pos)
    pos
SPFDfmDirAlgBaseFdirPosBaseAlgPointed {x} {f} {pos} m ex (Left () ** dm) =
  m ex (Left ())
SPFDfmDirAlgBaseFdirPosBaseAlgPointed {x} {f} {pos} m ex (Right ep ** dm) =
  m ex (Right (ep ** dm))

public export
SPFDcompPosPointedSPFDtoF : {x : Type} -> (f : SPFData x x) ->
  SliceNatTrans {x} {y=x}
    (InterpSPFData (spfdTranslateTerminal f))
    (SPFDcompPosPointedSl f)
SPFDcompPosPointedSPFDtoF {x} (SPFD fpos fdir) fmpos ex (Left () ** dmv_) =
  Left ()
SPFDcompPosPointedSPFDtoF {x} (SPFD fpos fdir) fmpos ex (Right ep ** dm) =
  Right (ep ** dm)

public export
SPFDcompPosPointedSPFDfromF : {x : Type} -> (f : SPFData x x) ->
  SliceNatTrans {x} {y=x}
    (SPFDcompPosPointedSl f)
    (InterpSPFData (spfdTranslateTerminal f))
SPFDcompPosPointedSPFDfromF {x} (SPFD fpos fdir) fmpos ex (Left ()) =
  (Left () ** \_ => voidF _)
SPFDcompPosPointedSPFDfromF {x} (SPFD fpos fdir) fmpos ex (Right (ep ** dm)) =
  (Right ep ** dm)

-- Given an endofunctor `f`, this produces the type of directions of the
-- free pointed functor of the functor resulting from composing `f` after a
-- functor with positions `fmpos` and directions `fmdir`.
public export
SPFDcompDirPointedSl : {x : Type} -> (f : SPFData x x) ->
  (fmpos : SliceObj x) ->
  SPFdirSl x x fmpos ->
  SPFdirSl x x (SPFDcompPosPointedSl f fmpos)
SPFDcompDirPointedSl {x} f fmpos fmdir ((ec ** Left ()), ed) =
  SPFDidDir x ec () ed
SPFDcompDirPointedSl {x} f fmpos fmdir ((ec ** Right epdm), ed) =
  SPFDcompDirSl {x} f fmpos fmdir ((ec ** epdm), ed)

-- Next we internalize `SPFDcompDirPointedSl` -- meaning,
-- given that `SPFDcompDirPointedSl` maps slice objects to
-- slice objects (specifically, slices over `SPFdirSlBase x x fmpos`
-- to slices over `SPFdirSlBase x x (SPFDcompPosPointedSl f fmpos)`),
-- we exhibit it as a functor, and specifically as a _polynomial_
-- functor, by building an `SPFData` whose interpretation is precisely
-- `SPFDcompDirPointedSl`.
--
-- This is the position-type of the polynomial internalization of
-- `SPFDcompDirPointedSl`.
public export
SPFDcompDirPointedSPFDpos : {x : Type} -> (f : SPFData x x) ->
  (fmpos : SliceObj x) ->
  SPFdirSl x x (SPFDcompPosPointedSl f fmpos)
SPFDcompDirPointedSPFDpos {x} (SPFD fpos fdir) fmpos
  ((ec ** Left ()), ed) =
    ec = ed
SPFDcompDirPointedSPFDpos {x} (SPFD fpos fdir) fmpos
  ((ec ** Right (ep ** dm)), ed) =
    SPFDcompDirSPFDpos {x} (SPFD fpos fdir) fmpos
      ((ec ** ep ** dm), ed)

-- This is the direction-type of the polynomial internalization of
-- `SPFDcompDirPointedSl`.
public export
SPFDcompDirPointedSPFDdir : {x : Type} -> (f : SPFData x x) ->
  (fmpos : SliceObj x) ->
  SPFdirType
    (SPFdirSlBase x x fmpos)
    (SPFdirSlBase x x (SPFDcompPosPointedSl f fmpos))
    (SPFDcompDirPointedSPFDpos {x} f fmpos)
SPFDcompDirPointedSPFDdir {x} (SPFD fpos fdir) fmpos
  ((ex ** Left ()), ex) Refl ((ec' ** efmp), ed') =
    Void
SPFDcompDirPointedSPFDdir {x} (SPFD fpos fdir) fmpos
  ((ec ** Right (ep ** dm)), ed) (ex ** fd) ((ec' ** efmp), ed') =
    SPFDcompDirSPFDdir {x} (SPFD fpos fdir) fmpos
      ((ec ** ep ** dm), ed) (ex ** fd) ((ec' ** efmp), ed')

-- Now that we have defined both position and the direction types, we
-- can define the polynomial internalization of `SPFDcompDirPointedSl`.
public export
SPFDcompDirPointedSPFD : {x : Type} -> (f : SPFData x x) ->
  (fmpos : SliceObj x) ->
  SPFData
    (SPFdirSlBase x x fmpos)
    (SPFdirSlBase x x (SPFDcompPosPointedSl f fmpos))
SPFDcompDirPointedSPFD {x} f fmpos =
  SPFD
    (SPFDcompDirPointedSPFDpos {x} f fmpos)
    (SPFDcompDirPointedSPFDdir {x} f fmpos)

-- Next we demonstrate that `SPFDcompDirPointedSPFD` _is_ a correct
-- internalization of `SPFDcompDirPointedSl`, by showing inverse natural
-- transformations between the latter and the interpetation of the
-- former.

public export
InterpSPFDcompDirPointedSPFD : {x : Type} -> (f : SPFData x x) ->
  (fmpos : SliceObj x) ->
  SPFdirSl x x fmpos ->
  SPFdirSl x x (SPFDcompPosPointedSl f fmpos)
InterpSPFDcompDirPointedSPFD {x} f fmpos =
  InterpSPFData (SPFDcompDirPointedSPFD f fmpos)

public export
SPFDcompDirPointedSPFDtoF : {x : Type} -> (f : SPFData x x) ->
  (fmpos : SliceObj x) ->
  SliceNatTrans
    {x=(SPFdirSlBase x x fmpos)}
    {y=(SPFdirSlBase x x (SPFDcompPosPointedSl f fmpos))}
    (InterpSPFDcompDirPointedSPFD {x} f fmpos)
    (SPFDcompDirPointedSl {x} f fmpos)
SPFDcompDirPointedSPFDtoF {x} (SPFD fpos fdir) fmpos sl
  ((ex ** Left ()), ex) (Refl ** dm') =
    Refl
SPFDcompDirPointedSPFDtoF {x} (SPFD fpos fdir) fmpos sl
  ((ec ** Right (ep ** fdmp)), ed) ((ex ** efd) ** sldm) =
    SPFDcompDirSPFDtoF {x} (SPFD fpos fdir) fmpos sl
      ((ec ** ep ** fdmp), ed)
      ((ex ** efd) ** \((ec ** ep), ed) => sldm ((ec ** ep), ed))

public export
SPFDcompDirPointedSPFDfromF : {x : Type} -> (f : SPFData x x) ->
  (fmpos : SliceObj x) ->
  SliceNatTrans
    {x=(SPFdirSlBase x x fmpos)}
    {y=(SPFdirSlBase x x (SPFDcompPosPointedSl f fmpos))}
    (SPFDcompDirPointedSl {x} f fmpos)
    (InterpSPFDcompDirPointedSPFD {x} f fmpos)
SPFDcompDirPointedSPFDfromF {x} (SPFD fpos fdir) fmpos sl
  ((ex ** Left ()), ex) Refl =
    (Refl ** \((ec ** ep), ed), dd => void dd)
SPFDcompDirPointedSPFDfromF {x} (SPFD fpos fdir) fmpos sl
  ((ec ** Right (ep ** dm)), ed) ((ex ** dd) ** esl) =
    ((ex ** dd) **
     \((ec ** ep), ed), (Refl ** Refl ** Refl) => esl)

------------------------------------------------------------------
------------------------------------------------------------------
---- Algebras and coalgebras of slice polynomial endofunctors ----
------------------------------------------------------------------
------------------------------------------------------------------

---------------------------
---- Convenience types ----
---------------------------

public export
SliceAlgSPFD : {x : Type} -> SPFData x x -> SliceObj x -> Type
SliceAlgSPFD {x} f = SliceAlg {a=x} (InterpSPFData {dom=x} {cod=x} f)

public export
SliceCoalgSPFD : {x : Type} -> SPFData x x -> SliceObj x -> Type
SliceCoalgSPFD {x} f = SliceCoalg {a=x} (InterpSPFData {dom=x} {cod=x} f)

------------------------------
---- Type-valued algebras ----
------------------------------

-- The slice-polynomial version of the reflective `PolyFuncDirIsAlg`:
-- the direction type of a slice polynomial endofunctor (on `SliceObj x` for
-- some `x : Type`) whose position type is itself given by the application of
-- a slice polynomial functor is equivalently an algebra of the latter
-- polynomial functor with carrier `const (SliceObj x)` (the object of
-- `SliceObj x` whose value at every term of `x` is itself `SliceObj x`).
--
-- `const (SliceObj x)` may be viewed as a reflection of the slice
-- category over `x` within `SliceObj y`, analogously to (and as a
-- generalization of) how `Type` is a reflection of the category `Type`
-- within itself.
public export
SPFfposType : {x, y : Type} -> SPFData x y -> SliceObj y
SPFfposType {x} {y} f = InterpSPFData f (const $ SliceObj x)

-- Now we note that the reflection `SPFfposType` is precisely the
-- position-type of post-composition.
public export
0 SPFfposTypeIsComp : {x, y : Type} -> (g : SPFData x y) ->
  ExtEq {a=y} {b=Type}
    (SPFfposType {x} {y} g)
    (SPFDcompPosSl {y=x} {z=y} g (const $ SliceObj x))
SPFfposTypeIsComp {x} {y} (SPFD gpos gdir) ex = Refl

-- Now we note that an algebra of the type of types is the direction-type
-- of a polynomial functor whose position-type is the position-type of
-- post-composition.

public export
SPFDtypeAlg : {x : Type} -> SPFData x x -> Type
SPFDtypeAlg {x} f = SliceAlgSPFD {x} f (const $ SliceObj x)

public export
SPFDdirIsAlg : {x : Type} -> (f : SPFData x x) ->
  (SPFdirType x x (SPFfposType {x} f) = SPFDtypeAlg {x} f)
SPFDdirIsAlg {x} f = Refl

-- Therefore, specifying an algebra of `f` whose carrier is the type of types
-- is equivalent to specifying a polynomial functor whose position-type is the
-- position-type of post-composition with `f`.  (Given a fixed position-type,
-- specifying a polynomial functor means specifying a direction-type, and
-- when the position-type is the position-type of post-composition with `f`,
-- the direction-type, we have just noted, is the same as the type of
-- type-valued algebras of `f`.)
public export
SPFDdepSPFD : {x : Type} -> {f : SPFData x x} ->
  SPFDtypeAlg {x} f -> SPFData x x
SPFDdepSPFD {x} {f} = SPFD (SPFfposType {x} f)

-- An algebra which collapses an SPFD-shaped tree of types into the coproduct
-- of all those types.
public export
SPFDcoprodTypeAlg : {x : Type} -> (f : SPFData x x) -> SPFDtypeAlg {x} f
SPFDcoprodTypeAlg {x} f =
  SPFDcompDir f (SPFD (const $ SliceObj x) (sliceId (const $ SliceObj x)))

-- Since `SPFDcoprodTypeAlg` is a type-algebra, it must be, we have just
-- established, the direction-type of post-composition with some polynomial
-- functor.  Here we exhibit that polynomial functor and show that
-- `SPFDcoprodTypeAlg` is the direction-type of post-composition with it.
--
-- The position-type of the polynomial functor that we exhibit is itself
-- the type of types.
public export
SPFDtypeIdPos : (x, y : Type) -> SliceObj y
SPFDtypeIdPos x y = const $ SliceObj x

-- The direction-type of the polynomial functor of which we show
-- `SPFDcoprodTypeAlg` to be the direction-type of post-composition
-- is the identity -- which makes sense only because the positions
-- are themselves types (the position-type is the type of types).
public export
SPFDtypeIdDir : (x, y : Type) -> SPFdirType x y (SPFDtypeIdPos x y)
SPFDtypeIdDir x y = sliceId {a=y} (const $ SliceObj x)

public export
SPFDtypeId : (x, y : Type) -> SPFData x y
SPFDtypeId x y = SPFD (SPFDtypeIdPos x y) (SPFDtypeIdDir x y)

-- To characterize `SPFDtypeId`: applying it to a type `a` produces
-- a choice of type `d` together with a morphism from `d` to `a`.
-- One way of looking at that is as a generic container type:  choose
-- an index type (`d`) and then a collection of values of `a` indexed
-- by `d`.  A morphism of the category of elements of `SPFDtypeId` is
-- a map over a collection -- it leaves the index type unchanged, while
-- transforming the contents via the morphism of the underlying category.
--
-- Another thing of note about this functor is that if we were to replace
-- the coproduct with a _coend_, it would become the density formula for
-- the identity functor.
public export
0 SPFDtypeIdCharacterization : (x, y : Type) ->
  (a : SliceObj x) -> (ey : y) ->
  InterpSPFData {dom=x} {cod=y} (SPFDtypeId x y) a ey =
  (d : SliceObj x ** SliceMorphism {a=x} d a)
SPFDtypeIdCharacterization x y a ey = Refl

-- Now we confirm that `SPFDcoprodTypeAlg f` is indeed the direction-type
-- of `f .  SPFDtypeId`.

public export
0 SPFDcoprodTypeAlgToComp : {x : Type} -> (f : SPFData x x) ->
  (ec : x) ->
  (ep : spfdPos f ec) ->
  (dir : (ex : x) -> spfdDir f ec ep ex -> SliceObj x) ->
  SliceMorphism {a=x}
    (SPFDcoprodTypeAlg {x} f ec (ep ** dir))
    (SPFDcompDir {x} {y=x} {z=x} f (SPFDtypeId x x) ec (ep ** dir))
SPFDcoprodTypeAlgToComp {x} f ec ep dir = sliceId _

public export
0 SPFDcoprodTypeAlgFromComp : {x : Type} -> (f : SPFData x x) ->
  (ec : x) ->
  (ep : spfdPos f ec) ->
  (dir : (ex : x) -> spfdDir f ec ep ex -> SliceObj x) ->
  SliceMorphism {a=x}
    (SPFDcompDir {x} {y=x} {z=x} f (SPFDtypeId x x) ec (ep ** dir))
    (SPFDcoprodTypeAlg {x} f ec (ep ** dir))
SPFDcoprodTypeAlgFromComp {x} f ec ep dir = sliceId _

-- Now we confirm that `f . SPFDtypeId` is indeed
-- `SPFDdepSPFD {f} (SPFDcoprodTypeAlg f)`.

public export
SPFDtypeIdCompToDepCoprod : {x : Type} -> (f : SPFData x x) ->
  SPFnt {dom=x} {cod=x}
    (SPFDcomp x x x f $ SPFDtypeId x x)
    (SPFDdepSPFD {f} $ SPFDcoprodTypeAlg f)
SPFDtypeIdCompToDepCoprod {x} f =
  SPFDm
    (sliceId _)
    (\ex, (ep ** dm), ed, ((ex'' ** fd'') ** dd'') => ((ex'' ** fd'') ** dd''))

public export
SPFDdepCoprodTotypeIdComp : {x : Type} -> (f : SPFData x x) ->
  SPFnt {dom=x} {cod=x}
    (SPFDdepSPFD {f} $ SPFDcoprodTypeAlg f)
    (SPFDcomp x x x f $ SPFDtypeId x x)
SPFDdepCoprodTotypeIdComp {x} f =
  SPFDm
    (sliceId _)
    (\ex, (ep ** dm), ed, ((ex'' ** fd'') ** dd'') => ((ex'' ** fd'') ** dd''))

-----------------------------------------------------------
-----------------------------------------------------------
---- Initial algebras of slice polynomial endofunctors ----
-----------------------------------------------------------
-----------------------------------------------------------

--------------------------------------------
---- Least fixed point and catamorphism ----
--------------------------------------------

-- `SPFDmu` is the carrier, and `InSPFm` the action, of the initial
-- algebra of `spfd`.  (As such, it is the algebra picked out by the
-- left adjoint of the adjunction between the category of `spfd`-algebras
-- and the terminal category.)
public export
data SPFDmu : {0 x : Type} -> SPFData x x -> SliceObj x where
  InSPFm : {0 spfd : SPFData x x} -> SliceAlgSPFD {x} spfd (SPFDmu {x} spfd)

-- This coalgebra is the inverse of `InSPFm`.
public export
OutSPFm: {0 x : Type} -> {0 spfd : SPFData x x} ->
  SliceCoalgSPFD {x} spfd (SPFDmu {x} spfd)
OutSPFm {x} {spfd} ex em = case em of InSPFm ex emx => emx

-- `spfdCata` is the unique algebra morphism from `(SPFDmu spfd, InSPFm)`
-- to `(a, alg)`.  (As such, it is the algebra morphism picked out by the right
-- adjunct of the adjunction between the category of `spfd`-algebras and
-- the terminal category.  It is also the counit of the adjunction, since
-- the adjunction is with the terminal category -- the counit is the right
-- adjunct applied to the identity, which is the only morphism in the terminal
-- category.)
mutual
  public export
  spfdCata : {0 x : Type} -> {0 spfd : SPFData x x} -> {0 a : SliceObj x} ->
    SliceAlgSPFD {x} spfd a -> SliceMorphism {a=x} (SPFDmu {x} spfd) a
  spfdCata {x} {spfd} {a} alg ex em =
    case em of
      InSPFm ex (emp ** emdm) =>
        alg ex (emp ** spfdCataDir {x} {spfd} {a} alg ex emp emdm)

  public export
  spfdCataDir : {0 x : Type} -> {0 spfd : SPFData x x} -> {0 a : SliceObj x} ->
    SliceAlgSPFD {x} spfd a ->
    (ec : x) -> (emp : spfdPos spfd ec) ->
    (emdm : SliceMorphism {a=x} (spfdDir spfd ec emp) (SPFDmu spfd)) ->
    SliceMorphism {a=x} (spfdDir spfd ec emp) a
  -- If Idris recognized it as terminating, this could be written as:
  --  spfdCataDir {x} {spfd} {a} alg ec emp =
  --    sliceComp {x=(spfdDir spfd ec emp)} {y=(SPFDmu {x} spfd)} {z=a}
  --    (spfdCata {x} {spfd} {a} alg)
  spfdCataDir {x} {spfd} {a} alg ec emp emdm ed =
    spfdCata {x} {spfd} {a} alg ed . emdm ed

public export
0 SPFDcataRewrite :
  {0 x : Type} -> {0 spfd : SPFData x x} -> {0 a : SliceObj x} ->
  (alg : SliceAlgSPFD {x} spfd a) ->
  (ex : x) -> (emp : spfdPos spfd ex) ->
  (emdm : SliceMorphism {a=x} (spfdDir spfd ex emp) (SPFDmu {x} spfd)) ->
    spfdCata {x} {spfd} {a} alg ex (InSPFm ex (emp ** emdm)) =
    alg ex (emp ** spfdCataDir {x} {spfd} {a} alg ex emp emdm)
SPFDcataRewrite {x} {spfd} {a} alg ex emp emdm = Refl

public export
0 SPFDcataDirRewrite :
  {0 x : Type} -> {0 spfd : SPFData x x} -> {0 a : SliceObj x} ->
  (alg : SliceAlgSPFD {x} spfd a) ->
  (ex : x) -> (emp : spfdPos spfd ex) ->
  (emdm : SliceMorphism {a=x} (spfdDir spfd ex emp) (SPFDmu {x} spfd)) ->
    spfdCataDir {x} {spfd} {a} alg ex emp emdm =
    sliceComp {x=(spfdDir spfd ex emp)} {y=(SPFDmu {x} spfd)} {z=a}
      (spfdCata {x} {spfd} {a} alg) emdm
SPFDcataDirRewrite {x} {spfd} {a} alg ex emp emdm = Refl

-- Because `SPFDmu` is left adjoint to the terminal category, the
-- comonad of the adjunction -- which takes any algebra to `InSPFm` --
-- is idempotent.  Thus the comultiplication of the comonad is simply
-- the identity.

-- `SPFDmu` itself is a functor, from `SPFData x x` to `SliceObj x`.
public export
spfdMuMapAlg : {x : Type} -> {p, q : SPFData x x} ->
  SPFnt p q -> SliceAlgSPFD {x} p (SPFDmu {x} q)
spfdMuMapAlg {x} {p} {q} (SPFDm onpos ondir) ex (ep ** dm) =
  InSPFm ex (onpos ex ep ** sliceComp dm $ ondir ex ep)

public export
spfdMuMap : {x : Type} -> {p, q : SPFData x x} ->
  SPFnt p q -> SliceMorphism (SPFDmu {x} p) (SPFDmu {x} q)
spfdMuMap {x} {p} {q} =
  spfdCata {x} {spfd=p} {a=(SPFDmu {x} q)} . spfdMuMapAlg {x} {p} {q}

-- An algebra for a composite of a polynomial functor with itself
-- also produces a catamorphism (for the original functor).
public export
spfdCataCompMutAlg :
  {x : Type} -> {spfd : SPFData x x} -> {a : SliceObj x} ->
  SliceMorphism {a=x} (InterpSPFData spfd (InterpSPFData spfd a)) a ->
  SliceAlgSPFD spfd (SliceProduct {a=x} a (InterpSPFData spfd a))
spfdCataCompMutAlg {x} {spfd} {a} alg ex (ep ** dm) =
  (alg ex (ep ** sliceComp (sliceProj2 a (InterpSPFData spfd a)) dm),
   (ep ** sliceComp (sliceProj1 a (InterpSPFData spfd a)) dm))

public export
spfdCataCompMut :
  {x : Type} -> {spfd : SPFData x x} -> {a : SliceObj x} ->
  SliceMorphism {a=x} (InterpSPFData spfd (InterpSPFData spfd a)) a ->
  SliceMorphism {a=x}
    (SPFDmu {x} spfd)
    (SliceProduct {a=x} a (InterpSPFData spfd a))
spfdCataCompMut {x} {spfd} {a} = spfdCata . spfdCataCompMutAlg {x} {spfd} {a}

public export
spfdCataComp :
  {x : Type} -> {spfd : SPFData x x} -> {a : SliceObj x} ->
  SliceMorphism {a=x} (InterpSPFData spfd (InterpSPFData spfd a)) a ->
  SliceMorphism {a=x} (SPFDmu {x} spfd) a
spfdCataComp {x} {spfd} {a} alg =
  sliceComp
    (sliceProj1 a (InterpSPFData spfd a))
    (spfdCataCompMut {x} {spfd} {a} alg)

public export
spfdCataCompApp :
  {x : Type} -> {spfd : SPFData x x} -> {a : SliceObj x} ->
  SliceMorphism {a=x} (InterpSPFData spfd (InterpSPFData spfd a)) a ->
  SliceMorphism {a=x} (SPFDmu {x} spfd) (InterpSPFData spfd a)
spfdCataCompApp {x} {spfd} {a} alg =
  sliceComp
    (sliceProj2 a (InterpSPFData spfd a))
    (spfdCataCompMut {x} {spfd} {a} alg)

public export
spfdCataSPFDcomp :
  {x : Type} -> {spfd : SPFData x x} -> {a : SliceObj x} ->
  SliceAlgSPFD {x} (SPFDcomp x x x spfd spfd) a ->
  SliceMorphism {a=x} (SPFDmu {x} spfd) a
spfdCataSPFDcomp {x} {spfd} {a} alg =
  spfdCataComp (sliceComp alg (InterpSPFfromComp spfd spfd a))

public export
spfdMuCompToMuAlg : {x : Type} -> (p : SPFData x x) ->
  SliceAlgSPFD {x} (SPFDcomp x x x p p) (SPFDmu {x} p)
spfdMuCompToMuAlg {x} p =
  sliceComp
    (sliceComp
      (InSPFm {spfd=p})
      (InterpSPFDataMap p (InterpSPFData p $ SPFDmu p) (SPFDmu p)
        (InSPFm {spfd=p})))
    (InterpSPFtoComp p p (SPFDmu p))

public export
spfdMuCompToMu : {x : Type} -> (p : SPFData x x) ->
  SliceMorphism {a=x} (SPFDmu {x} (SPFDcomp x x x p p)) (SPFDmu {x} p)
spfdMuCompToMu {x} p =
  spfdCata {x} {spfd=(SPFDcomp x x x p p)} {a=SPFDmu {x} p}
    (spfdMuCompToMuAlg {x} p)

public export
spfdMuToMuComp : {x : Type} -> (p : SPFData x x) ->
  SliceMorphism {a=x} (SPFDmu {x} p) (SPFDmu {x} (SPFDcomp x x x p p))
spfdMuToMuComp {x} p =
  spfdCataComp
    (sliceComp
      (InSPFm {spfd=(SPFDcomp x x x p p)})
      (InterpSPFfromComp p p (SPFDmu {x} $ SPFDcomp x x x p p)))

---------------------------------
---- `SPFData` adjoint folds ----
---------------------------------

-- An adjoint fold on an `SPFData` using the dependent-sum/base-change
-- adjunction between `SliceObj x` and `SliceObj (Sigma {a=x} slx)`.
export
spfdSigmaFold : {x : Type} -> {slx : SliceObj x} ->
  (f : SPFData (Sigma {a=x} slx) (Sigma {a=x} slx)) ->
  (a : SliceObj x) ->
  SliceAlgSPFD f (SliceBCF {c=x} slx a) ->
  SliceMorphism {a=x} (SliceSigmaF {c=x} slx $ SPFDmu {x=(Sigma {a=x} slx)} f) a
spfdSigmaFold {x} {slx} f a alg =
  sliceComp {a=x}
    (sSout {c=x} {sl=slx} a)
    (ssMap {c=x} {sl=slx}
      (SPFDmu f)
      (SliceBCF {c=x} slx a)
      (spfdCata {spfd=f} {a=(SliceBCF {c=x} slx a)} alg))

-- An adjoint fold on an `SPFData` using the base-change/dependent-product
-- adjunction between `SliceObj (Sigma {a=x} slx)` and `SliceObj x`.
export
spfdBCFold : {x : Type} -> {slx : SliceObj x} ->
  (f : SPFData x x) ->
  (a : SliceObj (Sigma {a=x} slx)) ->
  SliceAlgSPFD f (SlicePiF {c=x} slx a) ->
  SliceMorphism {a=(Sigma {a=x} slx)} (SliceBCF {c=x} slx $ SPFDmu {x} f) a
spfdBCFold {x} {slx} f a alg =
  sliceComp {a=(Sigma {a=x} slx)}
    (spCounit {c=x} {sl=slx} a)
    (sbcMap {c=x} {sl=slx}
      (SPFDmu f)
      (SlicePiF {c=x} slx a)
      (spfdCata {spfd=f} {a=(SlicePiF {c=x} slx a)} alg))

-- A convenience function for producing terms dependent on an initial algebra.
public export
SPFDmuBCalg : {x : Type} -> {spfd : SPFData x x} ->
  ((ex : x) -> SliceObj (SPFDmu {x} spfd ex)) ->
  Type
SPFDmuBCalg {x} {spfd} a =
  SliceAlgSPFD {x} spfd (SlicePiF {c=x} (SPFDmu {x} spfd) (DPair.uncurry a))

public export
spfdMuBCfold : {x : Type} -> {spfd : SPFData x x} ->
  {a : (ex : x) -> SliceObj (SPFDmu {x} spfd ex)} ->
  SPFDmuBCalg {x} {spfd} a ->
  (ex : x) -> Pi {a=(SPFDmu {x} spfd ex)} (a ex)
spfdMuBCfold {x} {spfd} {a} alg ex em =
  spfdBCFold {x} {slx=(SPFDmu {x} spfd)} spfd
    (DPair.uncurry a) alg (ex ** em) em

-- A convenience function for producing terms dependent on terms of an
-- `spfdMuBCfold` (i.e. terms which are themselves dependent on an initial
-- algebra).  Since this is itself an `spfdMuBCfold`, we do not need a
-- further hierarchy; we can produce arbitrary-depth dependencies just by
-- specializing the parameters of `spfdMuBCfold`.  This reflects the theorem
-- that the slice categories of a locally Cartesian closed category (such
-- as `Type`) are themselves locally Cartesian closed.
public export
SPFDmuBCdepFoldSl : {x : Type} -> {spfd : SPFData x x} ->
  {a : (ex : x) -> SliceObj (SPFDmu {x} spfd ex)} ->
  (adep : (ex : x) -> (em : SPFDmu {x} spfd ex) -> SliceObj (a ex em)) ->
  (ex : x) -> SliceObj (SPFDmu {x} spfd ex)
SPFDmuBCdepFoldSl {x} {spfd} {a} adep ex em = Pi {a=(a ex em)} (adep ex em)

public export
SPFDmuBCdepFoldAlg : {x : Type} -> {spfd : SPFData x x} ->
  {a : (ex : x) -> SliceObj (SPFDmu {x} spfd ex)} ->
  (adep : (ex : x) -> (em : SPFDmu {x} spfd ex) -> SliceObj (a ex em)) ->
  Type
SPFDmuBCdepFoldAlg {x} {spfd} {a} adep =
  SPFDmuBCalg {x} {spfd} (SPFDmuBCdepFoldSl {x} {spfd} {a} adep)

public export
spfdMuBCdepFold : {x : Type} -> {spfd : SPFData x x} ->
  {a : (ex : x) -> SliceObj (SPFDmu {x} spfd ex)} ->
  {adep : (ex : x) -> (em : SPFDmu {x} spfd ex) -> SliceObj (a ex em)} ->
  SPFDmuBCdepFoldAlg {x} {spfd} {a} adep ->
  (ex : x) -> (em : SPFDmu {x} spfd ex) -> Pi {a=(a ex em)} (adep ex em)
spfdMuBCdepFold {x} {spfd} {a} {adep} =
  spfdMuBCfold {x} {spfd} {a=(SPFDmuBCdepFoldSl {x} {spfd} {a} adep)}

export
spfdSPFDsigmaFold : {dom, cod : Type} ->
  (f : SPFData (SPFDataAsSigma dom cod) (SPFDataAsSigma dom cod)) ->
  (a : SliceObj (SliceObj cod)) ->
  SliceAlgSPFD f (SliceBCF {c=(SliceObj cod)} (SPFDataToSigmaSl dom cod) a) ->
  SliceMorphism {a=(SliceObj cod)}
    (SliceSigmaF {c=(SliceObj cod)} (SPFDataToSigmaSl dom cod) $ SPFDmu f)
    a
spfdSPFDsigmaFold {dom} {cod} =
  spfdSigmaFold {x=(SliceObj cod)} {slx=(SPFDataToSigmaSl dom cod)}

-- A specialization of `spfdBCFold` which produces a morphism in the
-- slice category of `Sigma {a=(SliceObj cod)} (SPFDataToSigmaSl dom cod)`.
-- Such a sigma type is precisely an `SPFData dom cod`, so a morphism in that
-- slice category can be interpreted as a mapping between predicates on
-- slice polynomial functors (from the slice category over `dom` to the
-- slice category over `cod`), quantified over all such functors.
-- The domain of the morphism in this specialization is (a base change of)
-- the initial algebra of a polynomial endofunctor on the slice category
-- over `SliceObj cod` (not just the slice category over `cod`, but the
-- category whose objects are of type `SliceObj (SliceObj cod)`), which
-- is in particular the type of position-types of slice polynomial functors
-- with domain `cod`.
export
spfdSPFDbcFold : {dom, cod : Type} ->
  (f : SPFData (SliceObj cod) (SliceObj cod)) ->
  (a : SliceObj (Sigma {a=(SliceObj cod)} (SPFDataToSigmaSl dom cod))) ->
  SliceAlgSPFD f (SlicePiF {c=(SliceObj cod)} (SPFDataToSigmaSl dom cod) a) ->
  SliceMorphism {a=(Sigma {a=(SliceObj cod)} (SPFDataToSigmaSl dom cod))}
    (SliceBCF (SPFDataToSigmaSl dom cod) $ SPFDmu {x=(SliceObj cod)} f)
    a
spfdSPFDbcFold {dom} {cod} =
  spfdBCFold {x=(SliceObj cod)} {slx=(SPFDataToSigmaSl dom cod)}

------------------------------------------------------
---- `SPFDmu` as least fixed point of composition ----
------------------------------------------------------

public export
SPFDsnat : (x : Type) -> SliceObj x
SPFDsnat x = SPFDmu {x} (spfdMaybe x)

public export
spfdMaybeAlg : {x : Type} -> {a : SliceObj x} ->
  SliceMorphism {a=x} (SliceObjTerminal x) a ->
  SliceMorphism {a=x} a a ->
  SliceAlgSPFD {x} (spfdMaybe x) a
spfdMaybeAlg {x} {a} z s ex (Left () ** m) = z ex ()
spfdMaybeAlg {x} {a} z s ex (Right () ** m) = s ex $ m ex Refl

public export
spfdMaybeU : SPFData Unit Unit
spfdMaybeU = spfdMaybe Unit

public export
SPFDunat : SliceObj Unit
SPFDunat = SPFDsnat Unit

public export
SPFDnat : Type
SPFDnat = SPFDunat ()

public export
spfdMaybeAlgU : {a : Type} ->
  a -> (a -> a) ->
  SliceAlgSPFD {x=Unit} SlicePolyUMorph.spfdMaybeU (const a)
spfdMaybeAlgU {a} z s () =
  spfdMaybeAlg {x=Unit} {a=(const a)} (const $ const z) (const s) ()

public export
spfdNatCata : {x : Type} -> {a : SliceObj x} ->
  SliceMorphism {a=x} (SliceObjTerminal x) a ->
  SliceMorphism {a=x} a a ->
  SliceMorphism {a=x} (SPFDsnat x) a
spfdNatCata {a} z s =
  spfdCata {x} {spfd=(spfdMaybe x)} {a} (spfdMaybeAlg {a} z s)

public export
spfdNatCataU : {a : Type} -> a -> (a -> a) -> SPFDnat -> a
spfdNatCataU {a} z s =
  spfdNatCata {x=Unit} {a=(const a)} (const $ const z) (const s) ()

public export
SPFDmuRn : {x : Type} -> SPFData x x -> SPFDnat -> SliceObj x
SPFDmuRn {x} f =
  spfdNatCataU {a=(SliceObj x)}
    (SliceObjInitial x)
    (InterpSPFData {dom=x} {cod=x} f)

-- There are injections from each `SPFDmuRn` to `SPFDmu`.

public export
spfdNinj : {x : Type} -> {f : SPFData x x} ->
  (n : SPFDnat) -> SliceMorphism {a=x} (SPFDmuRn {x} f n) (SPFDmu f)
spfdNinj {x} {f} (InSPFm () (Left () ** n)) ex el =
  void el
spfdNinj {x} {f} (InSPFm () (Right () ** n)) ex el =
  InSPFm ex (fst el ** \ex' => spfdNinj {x} {f} (n () Refl) ex' . snd el ex')

public export
SPFDiter : {x : Type} -> SPFData x x -> SPFDnat -> SPFData x x
SPFDiter {x} f = spfdNatCataU {a=(SPFData x x)} (SPFDid x) (SPFDcomp x x x f)

-----------------------------------------------------------
---- Positions and directions from polynomial functors ----
-----------------------------------------------------------

-- Given a type-algebra of a polynomial functor, produce a type dependent on
-- the least fixed point (initial algebra) of that functor.  Note that such
-- a dependent type has the same type signature as the direction type of a
-- polynomial functor whose position-type is the initial algebra of the
-- given functor.  We might think of `SPFDmu` as generating inductive types
-- and `spfdDirMu` as generating recursive types.
public export
spfdDirMu : {x : Type} -> {f : SPFData x x} ->
  SPFDtypeAlg {x} f -> SPFdirType x x (SPFDmu {x} f)
spfdDirMu {x} {f} = spfdCata {spfd=f} {a=(const $ SliceObj x)}

public export
spfdDirMuSl : {x : Type} -> {f : SPFData x x} ->
  SPFDtypeAlg {x} f -> SPFdirSl x x (SPFDmu {x} f)
spfdDirMuSl {x} {f} = SPFdirToSl . spfdDirMu {x} {f}

-- Compilable documentation to spell out what `spfdDirMu` becomes.

public export
0 spfdDirMuInterpDir : {x : Type} -> {f : SPFData x x} ->
  (tyalg : SPFDtypeAlg {x} f) ->
  (ex : x) ->
  (efp : spfdPos f ex) ->
  (efdm : SliceMorphism {a=x} (spfdDir f ex efp) (SPFDmu f)) ->
    spfdCataDir tyalg ex efp efdm = spfdDirComp (spfdDirMu {x} {f} tyalg) efdm
spfdDirMuInterpDir {x} {f} =
  SPFDcataDirRewrite {x} {spfd=f} {a=(const $ SliceObj x)}

public export
0 spfdDirMuInterp : {x : Type} -> {f : SPFData x x} ->
  (tyalg : SPFDtypeAlg {x} f) ->
  (ex : x) ->
  (efp : spfdPos f ex) ->
  (efdm : SliceMorphism {a=x} (spfdDir f ex efp) (SPFDmu f)) ->
  (ex' : x) ->
    spfdDirMu {x} {f} tyalg ex (InSPFm ex (efp ** efdm)) ex' =
    tyalg ex (efp ** spfdDirComp (spfdDirMu {x} {f} tyalg) efdm) ex'
spfdDirMuInterp {x} {f} tyalg ex efp efdm ex' =
  rewrite spfdDirMuInterpDir {x} {f} tyalg ex efp efdm in Refl

-- Given a type-algebra of a polynomial functor, produce another
-- polynomial functor whose positions are the initial algebra of the
-- given functor and whose directions are given by the type-algebra
-- (via `spfdDirMu`).
public export
spfdDepSPFD : {x : Type} -> {f : SPFData x x} ->
  SPFDtypeAlg {x} f -> SPFData x x
spfdDepSPFD {x} {f} tyalg = SPFD (SPFDmu {x} f) (spfdDirMu {x} {f} tyalg)

--------------------------------------------------
---- Paranatural initial-algebra Yoneda forms ----
--------------------------------------------------

-- A paranatural (also called "strong dinatural") Yoneda lemma for
-- initial algebras -- this is "Proposition 1" of Uustalu's "A note on
-- strong dinaturality, initial algebras and uniform parameterized
-- fixpoint operators".
--
-- The lemma asserts an isomorphism between, on one side, the set of paranatural
-- transformations from the algebras of a polynomial functor to a particular
-- copresheaf (treated as a difunctor) and, on the other side, the application
-- of the copresheaf to the initial algebra of the polynomial functor.

-- The following isomorphism is a universal, covariant form.

public export
spfdAlgParaNTtoMuCovar : {x : Type} ->
  (f : SPFData x x) -> (k : SliceObj x -> Type) ->
  ((a : SliceObj x) -> SliceAlgSPFD {x} f a -> k a) -> k (SPFDmu {x} f)
spfdAlgParaNTtoMuCovar {x} f k pnt =
  pnt (SPFDmu {x} f) $ InSPFm {x} {spfd=f}

public export
spfdMuToAlgParaNTcovar : {x : Type} ->
  (f : SPFData x x) -> (k : SliceObj x -> Type) ->
  (kmap : (y, z : SliceObj x) -> SliceMorphism {a=x} y z -> k y -> k z) ->
  k (SPFDmu {x} f) -> ((a : SliceObj x) -> SliceAlgSPFD {x} f a -> k a)
spfdMuToAlgParaNTcovar {x} f k kmap kmu a alg =
  kmap (SPFDmu {x} f) a (spfdCata {x} {spfd=f} {a} alg) kmu

-- The above in a form with the copresheaf `k : SliceObj x -> Type`
-- generalized to a slice functor.

public export
spfdAlgParaNTtoMuCovarSl : {x, w : Type} ->
  (f : SPFData x x) -> (k : SliceFunctor x w) ->
  ((a : SliceObj x) -> SliceAlgSPFD {x} f a -> Pi {a=w} (k a)) ->
  Pi {a=w} (k (SPFDmu {x} f))
spfdAlgParaNTtoMuCovarSl {x} {w} f k =
  spfdAlgParaNTtoMuCovar {x} f (Pi {a=w} . k)

public export
spfdAlgParaNTtoMuCovarSlSigma : {x, w : Type} ->
  (f : SPFData x x) -> (k : SliceFunctor x w) ->
  ((a : SliceObj x) -> SliceAlgSPFD {x} f a -> Sigma {a=w} (k a)) ->
  Sigma {a=w} (k (SPFDmu {x} f))
spfdAlgParaNTtoMuCovarSlSigma {x} {w} f k =
  spfdAlgParaNTtoMuCovar {x} f (Sigma {a=w} . k)

public export
spfdMuToAlgParaNTcovarSl : {x, w : Type} ->
  (f : SPFData x x) -> (k : SliceFunctor x w) ->
  (kmap : (y, z : SliceObj x) ->
    SliceMorphism {a=x} y z -> SliceMorphism {a=w} (k y) (k z)) ->
  Pi {a=w} (k (SPFDmu {x} f)) ->
  ((a : SliceObj x) -> SliceAlgSPFD {x} f a -> Pi {a=w} (k a))
spfdMuToAlgParaNTcovarSl {x} {w} f k kmap =
  spfdMuToAlgParaNTcovar {x} f
    (Pi {a=w} . k) (piMapComp {c=x} {d=w} {k} kmap)

public export
spfdMuToAlgParaNTcovarSlSigma : {x, w : Type} ->
  (f : SPFData x x) -> (k : SliceFunctor x w) ->
  (kmap : (y, z : SliceObj x) ->
    SliceMorphism {a=x} y z -> SliceMorphism {a=w} (k y) (k z)) ->
  Sigma {a=w} (k (SPFDmu {x} f)) ->
  ((a : SliceObj x) -> SliceAlgSPFD {x} f a -> Sigma {a=w} (k a))
spfdMuToAlgParaNTcovarSlSigma {x} {w} f k kmap =
  spfdMuToAlgParaNTcovar {x} f
    (Sigma {a=w} . k) (sigmaMapComp {c=x} {d=w} {k} kmap)

-- The following isomorphism is an existential, contravariant form.

public export
spfdAlgToMuContra :
  {x : Type} -> (f : SPFData x x) -> (k : SliceObj x -> Type) ->
  (kcontramap : (y, z : SliceObj x) -> SliceMorphism {a=x} z y -> k y -> k z) ->
  (a : SliceObj x ** (SliceAlgSPFD {x} f a, k a)) -> k (SPFDmu {x} f)
spfdAlgToMuContra {x} f k kcm (a ** (alg, eka)) =
  kcm a (SPFDmu {x} f) (spfdCata {x} {spfd=f} {a} alg) eka

public export
spfdMuToAlgContra :
  {x : Type} -> (f : SPFData x x) -> (k : SliceObj x -> Type) ->
  k (SPFDmu {x} f) -> (a : SliceObj x ** (SliceAlgSPFD {x} f a, k a))
spfdMuToAlgContra {x} f k kmu =
  (SPFDmu {x} f ** (InSPFm {x} {spfd=f}, kmu))

-- The above in a form with the presheaf `k : SliceObj x -> Type`
-- generalized to a (contravariant) slice functor.

public export
spfdAlgToMuContraSl :
  {x, w : Type} -> (f : SPFData x x) -> (k : SliceFunctor x w) ->
  (kcontramap : (y, z : SliceObj x) ->
    SliceMorphism {a=x} z y -> SliceMorphism {a=w} (k y) (k z)) ->
  (a : SliceObj x ** (SliceAlgSPFD {x} f a, Sigma {a=w} (k a))) ->
  Sigma {a=w} (k (SPFDmu {x} f))
spfdAlgToMuContraSl {x} {w} f k kcm =
  spfdAlgToMuContra {x} f (Sigma {a=w} . k)
    (sigmaContramapComp {c=x} {d=w} {k} kcm)

public export
spfdMuToAlgContraSl :
  {x, w : Type} -> (f : SPFData x x) -> (k : SliceFunctor x w) ->
  Sigma {a=w} (k (SPFDmu {x} f)) ->
  (a : SliceObj x ** (SliceAlgSPFD {x} f a, Sigma {a=w} (k a)))
spfdMuToAlgContraSl {x} {w} f k = spfdMuToAlgContra {x} f (Sigma {a=w} . k)

---------------------
---------------------
---- Free monads ----
---------------------
---------------------

----------------------
---- Base functor ----
----------------------

-- The free monad of a polynomial functor `f` can be defined pointwise
-- at each object `a` as the initial algebra of the polynomial functor
-- `x -> a + f x`.  From the pointwise definition, we can then extract
-- the position-set (as the functor applied to the terminal object) and
-- then the direction-sets.
--
-- There is also another way of looking at the free monad, as a higher-order
-- fixed point of repeated post-composition of the free pointed endofunctor.
-- We have shown above that `spfdTranslateTerminal f` is an internalization
-- of the position-type of post-composition of `spfdFreePointed f`, so
-- the fixed point of `spfdTranslateTerminal f` should be the position-type
-- of the free monad, and that does agree with the conclusion drawn from
-- the pointwise definition.
public export
spfdFMbase : {x : Type} -> SPFData x x -> SliceObj x -> SPFData x x
spfdFMbase {x} = spfdTranslate {dom=x} {cod=x}

-- This is the carrier component of the object-map component of the left
-- adjoint of the the free/forgetful adjunction between the category of
-- algebras of the free monad of `f` (on the left) and `SliceObj x` (on the
-- right).  It takes a slice object to the carrier of the free algebra of
-- the free monad of `f` applied at that object.
public export
spfdGenFree : {x : Type} -> SPFData x x -> SliceEndofunctor x
spfdGenFree {x} f = SPFDmu {x} . spfdFMbase {x} f

-- This is the algebra component of the object-map component of the left
-- adjoint of the the free/forgetful adjunction between the category of
-- algebras of the free monad of `f` (on the left) and `SliceObj x` (on
-- the right).  It takes a slice object to the morphism component of the free
-- algebra of the free monad of `f` applied at that object.
public export
InSPFfgen : {x : Type} -> {f : SPFData x x} -> {slv : SliceObj x} ->
  SliceAlgSPFD {x} f (spfdGenFree {x} f slv)
InSPFfgen {x} {f} {slv} ex (ep ** dm) = InSPFm ex (Right ep ** dm)

-- This is the unit of the adjunction.
public export
InSPFvgen : {x : Type} -> {f : SPFData x x} -> {slv : SliceObj x} ->
  SliceMorphism {a=x} slv (spfdGenFree {x} f slv)
InSPFvgen {x} {f} {slv} ex ev = InSPFm ex (Left ev ** \_ => voidF _)

public export
InSPFg : {x : Type} -> {f : SPFData x x} ->
  SliceNatTrans {x} {y=x}
    (InterpSPFData (SlicePolyUMorph.spfdFreePointed f) . spfdGenFree {x} f)
    (spfdGenFree {x} f)
InSPFg {x} {f} slv ec (Left () ** dm) = dm ec Refl
InSPFg {x} {f} slv ec (Right ep ** dm) = InSPFfgen ec (ep ** dm)

-- This is the morphism-map component of the left adjoint of the the
-- free/forgetful adjunction between the category of algebras of the
-- free monad of `f` (on the left) and `SliceObj x` (on the right).  It takes
-- a slice morphism to an algebra morphism between the free algebras of
-- the free monad of `f` applied to the domain and codomain.

public export
spfdGenFreeMorAlg : {x : Type} -> (f : SPFData x x) ->
  (sa, sb : SliceObj x) -> SliceMorphism {a=x} sa sb ->
  SliceAlgSPFD {x} (spfdFMbase {x} f sa) (spfdGenFree {x} f sb)
spfdGenFreeMorAlg {x} f sa sb mab ex (Left esa ** dm) =
  InSPFm ex (Left (mab ex esa) ** \ex, ev => void ev)
spfdGenFreeMorAlg {x} f sa sb mab ex (Right ep ** dm) =
  InSPFm ex (Right ep ** dm)

public export
spfdGenFreeMor : {x : Type} -> (f : SPFData x x) ->
  (sa, sb : SliceObj x) -> SliceMorphism {a=x} sa sb ->
  SliceMorphism {a=x} (spfdGenFree {x} f sa) (spfdGenFree {x} f sb)
spfdGenFreeMor {x} f sa sb mab =
  spfdCata {spfd=(spfdFMbase {x} f sa)} {a=(spfdGenFree {x} f sb)} $
    spfdGenFreeMorAlg {x} f sa sb mab

-- The "eval" universal morphism for `f : SPFData x x` is the right adjunct
-- of the the free/forgetful adjunction between the category of algebras of
-- the free monad of `f` (on the left) and `SliceObj x` (on the right).
-- Among the parameters, `slv` is an object of `SliceObj x`, `(sla, alg)` is an
-- algebra of `f`, `subst` is a morphism of `SliceObj x` (from `slv` to `sla`,
-- where the latter is the application of the forgetful functor to
-- `(sla, alg)`), and the result is a morphism from the free algebra of
-- `SPFDfreeM` applied at `slv` to `sla`.  Hence, in terms of the adjunction,
-- it is a mapping `(A, RB) -> (LA, B)`.
public export
spfdFMeval : {x : Type} -> (f : SPFData x x) -> (slv, sla : SliceObj x) ->
  SliceAlgSPFD f sla -> SliceMorphism {a=x} slv sla ->
  SliceMorphism {a=x} (spfdGenFree {x} f slv) sla
spfdFMeval {x} f slv sla alg subst =
  spfdCata {x} {spfd=(spfdFMbase {x} f slv)} {a=sla} $
    \ex, el => case el of
      (i ** dm) => case i of
        Left ev => subst ex ev
        Right ep => alg ex (ep ** dm)

-- The left adjunct of the the free/forgetful adjunction between the category
-- of algebras of the free monad of `f` (on the left) and `SliceObj x` (on the
-- right).  The parameters are as `spfdFMeval` except:
--  - We swap the last parameter (`subst`) and the result, since here we are
--    taking `(LA, B) -> (A, RB)`
--  - We omit the parameter `alg : SliceAlgSPFD f sla`, because we do not
--    use it -- the codomain of the output morphism is `RB` and `R` is the
--    functor that forgets the algebra component, leaving only the carrier,
--    so we have no need for the algebra component among the inputs
public export
spfdFMladj : {x : Type} -> (f : SPFData x x) -> (slv, sla : SliceObj x) ->
  SliceMorphism {a=x} (spfdGenFree {x} f slv) sla ->
  SliceMorphism {a=x} slv sla
spfdFMladj {x} f slv sla fmalg ex eslvx =
  fmalg ex (InSPFm ex (Left eslvx ** \ex', ev => void ev))

-------------------------------------
---- Positions of the free monad ----
-------------------------------------

-- Here we generate the positions and directions of the free monad,
-- thereby representing it as a polynomial functor.

public export
SPFDfmPos : {x : Type} -> SPFData x x -> SliceObj x
SPFDfmPos {x} spfd = spfdGenFree {x} spfd (SliceObjTerminal x)

public export
SPFDfmSigmaPos : {x : Type} -> SPFData x x -> Type
SPFDfmSigmaPos {x} = Sigma {a=x} . SPFDfmPos {x}

-- Documentation of another (intensionally equal) way of writing `SPFDfmPos`.
public export
spfdFMposBase : {x : Type} -> SPFData x x -> SPFData x x
spfdFMposBase {x} =
  -- Equivalently `flip (spfdFMbase {x}) (SliceObjTerminal x)`.
  spfdTranslateTerminal {dom=x} {cod=x}

public export
SPFDfmPosAlt : {x : Type} -> (f : SPFData x x) ->
  SPFDfmPos {x} f = SPFDmu {x} (spfdFMposBase {x} f)
SPFDfmPosAlt {x} f = Refl

public export
SPFDfmPosLeaf : {x : Type} -> (f : SPFData x x) ->
  (ex : x) -> SPFDfmPos {x} f ex
SPFDfmPosLeaf {x} f ex = InSPFm ex (Left () ** \_ => voidF _)

public export
SPFDfmPosPath : {x : Type} -> (f : SPFData x x) ->
  (ex : x) -> (ep : InterpSPFData f (SPFDfmPos {x} f) ex) ->
  SPFDfmPos {x} f ex
SPFDfmPosPath {x} f ex ep = InSPFm ex (Right (fst ep) ** snd ep)

------------------------------------------
---- Free monad from mutual recursion ----
------------------------------------------

-- Having generated the positions of the free monad in the usual
-- way for a polynomial functor whose interpretation we know --
-- by applying its interpretation to the terminal object -- we now
-- generate them in a different way, by mutual recursion with the
-- directions.  The point of using mutual recursion even though
-- the positions do not depend on the directions (because of the
-- insensitivity of post-composition to the direction-type of the
-- pre-composed functor) is that this enables each direction to be
-- expressed in terms of a _finite_ type (if each direction-type
-- is finite), whereas the overall position-type can be infinite
-- (even if each direction-type is finite).  This makes sense because
-- the positions are well-founded `f`-shaped trees, and the directions
-- at a given position are the leaves.
--
-- Because we are using mutual recursion to generate more than one
-- (dependent) type simultaneously, some of the functors that we use to generate
-- them will not be sliced simply over position-types and direction-types
-- for `SPFData x x`, but over larger slice categories representing
-- collections of interdependent dependent types.

-- Note that, in general, because the direction-types are also sliced
-- over position-types, we would need some form of inductive-inductive
-- type to generate them together with the position-types, and we have
-- not yet defined any form of inductive-inductive type.  However, in
-- the specific case of this generation of positions and directions of
-- the free monad, it will turn out that we do not need that, because
-- we will set up the recursion so that for any direction, we can
-- compute exactly one position of which it must be a direction.
--
-- We will use the `SlicePolyFunc` variant of `SPFData`, as it is
-- more convenient for this purpose than `SPFData` itself.
-- We will also compose the functor that we finally recurse over
-- from several smaller functors.

-- There is only one position representing a one-node tree,
-- because a one-node tree has no further characteristics!
-- (Any two one-node trees are equal.)  Note that this means
-- that we do not even need to provide a functor parameter;
-- one-node trees even of different functor shapes are
-- indistinguishable.
public export
SPFDfmMutGenTree1pos : (x : Type) -> SliceObj x
SPFDfmMutGenTree1pos = SliceObjTerminal

-- A one-node tree has no directions, because it has no children.
public export
SPFDfmMutGenTree1dir : (x : Type) ->
  SliceObj (Sigma $ SPFDfmMutGenTree1pos x)
SPFDfmMutGenTree1dir x _ = Void

-- Because a one-node tree has no directions, it may as well have a trivial
-- domain, namely the terminal category -- which is equivalent to the slice
-- category over `Void`.
public export
SPFDfmMutGenTree1asn : (x : Type) ->
  Sigma (SPFDfmMutGenTree1dir x) -> Void
SPFDfmMutGenTree1asn x = DPair.snd

public export
SPFDfmMutGenTree1SPF : (x : Type) -> SlicePolyFunc Void x
SPFDfmMutGenTree1SPF x =
  (SPFDfmMutGenTree1pos x ** SPFDfmMutGenTree1dir x ** SPFDfmMutGenTree1asn x)

-- A (potentially) multi-node tree simply has precisely the shape of `f` itself.
public export
SPFDfmMutGenTreeM : {x : Type} -> SlicePolyFunc x x -> SlicePolyFunc x x
SPFDfmMutGenTreeM {x} = id {a=(SlicePolyFunc x x)}

public export
SPFDfmMutGenTreeMpos : {x : Type} -> SlicePolyFunc x x -> SliceObj x
SPFDfmMutGenTreeMpos {x} = spfPos

public export
SPFDfmMutGenTreeMdir : {x : Type} -> (f : SlicePolyFunc x x) ->
  SliceObj (Sigma $ SPFDfmMutGenTreeMpos {x} f)
SPFDfmMutGenTreeMdir {x} = spfDir

public export
SPFDfmMutGenTreeMasn : {x : Type} -> (f : SlicePolyFunc x x) ->
  Sigma (SPFDfmMutGenTreeMdir {x} f) -> x
SPFDfmMutGenTreeMasn {x} = spfAssign

-- A tree is either a one-node tree or a multi-node (`f`-shaped) tree.
-- Thus we give it two positions, and we will use the corresponding
-- tree types as directions.  Note that since we are operating only
-- on tree types, without any dependency on specific shapes, this functor
-- does not require a functor parameter.

public export
SPFDfmTreeTypeSl : Type -> Type
SPFDfmTreeTypeSl x = Either x x

public export
SPFDfmTreeType1Sl : {x : Type} -> x -> SPFDfmTreeTypeSl x
SPFDfmTreeType1Sl {x} = Left

public export
SPFDfmTreeTypeMSl : {x : Type} -> x -> SPFDfmTreeTypeSl x
SPFDfmTreeTypeMSl {x} = Right

public export
SPFDfmMutGenTreeTypePos : (x : Type) -> SliceObj x
SPFDfmMutGenTreeTypePos x ex = Either Unit Unit

-- Each position has one direction (a tree).  The assignment will
-- determine which type of tree.
public export
SPFDfmMutGenTreeTypeDir : (x : Type) ->
  SliceObj (Sigma $ SPFDfmMutGenTreeTypePos x)
SPFDfmMutGenTreeTypeDir x _ = Unit

public export
SPFDfmMutGenTreeTypeAsn : (x : Type) ->
  Sigma (SPFDfmMutGenTreeTypeDir x) -> SPFDfmTreeTypeSl x
SPFDfmMutGenTreeTypeAsn x ((ex ** Left ()) ** ()) = Left ex
SPFDfmMutGenTreeTypeAsn x ((ex ** Right ()) ** ()) = Right ex

public export
SPFDfmMutGenTreeTypeSPF : (x : Type) -> SlicePolyFunc (SPFDfmTreeTypeSl x) x
SPFDfmMutGenTreeTypeSPF x =
  (SPFDfmMutGenTreeTypePos x **
   SPFDfmMutGenTreeTypeDir x **
   SPFDfmMutGenTreeTypeAsn x)

-- We can now build a functor which suffices to construct the
-- positions (not yet the directions) of the free monad of `f`.

-- The functor that generates trees (which are the positions of
-- the free monad) uses three slices (per term of the codomain) --
-- one for each of the two tree forms (so that we generate a type
-- of one-node trees and a type of `f`-shaped, potentially multi-node
-- trees), and one for the type of any tree of either form.

public export
SPFDfmTreeGenSl : Type -> Type
SPFDfmTreeGenSl x = Either x (SPFDfmTreeTypeSl x)

public export
SPFDfmTreeGenAnyTree : {x : Type} -> x -> SPFDfmTreeGenSl x
SPFDfmTreeGenAnyTree {x} = Left

public export
SPFDfmTreeGenSpecificTree : {x : Type} ->
  SPFDfmTreeTypeSl x -> SPFDfmTreeGenSl x
SPFDfmTreeGenSpecificTree {x} = Right

-- Every `SPFDfmTreeGenSl x` contains precisely one `x`; this extracts it.
public export
SPFDfmPosCodiag : NaturalTransformation SPFDfmTreeGenSl Prelude.id
SPFDfmPosCodiag x (Left ex) = ex
SPFDfmPosCodiag x (Right $ Left ex) = ex
SPFDfmPosCodiag x (Right $ Right ex) = ex

public export
SPFDfmTreeMutGenTreePos : {x : Type} ->
  SlicePolyEndoFunc x -> SliceObj (SPFDfmTreeGenSl x)
SPFDfmTreeMutGenTreePos {x} f (Left ex) = SPFDfmMutGenTreeTypePos x ex
SPFDfmTreeMutGenTreePos {x} f (Right $ Left ex) = SPFDfmMutGenTree1pos x ex
SPFDfmTreeMutGenTreePos {x} f (Right $ Right ex) = SPFDfmMutGenTreeMpos {x} f ex

public export
SPFDfmTreeMutGenTreeDir : {x : Type} ->
  (f : SlicePolyEndoFunc x) -> SliceObj (Sigma $ SPFDfmTreeMutGenTreePos {x} f)
SPFDfmTreeMutGenTreeDir {x} f (Left ex ** ep) =
  SPFDfmMutGenTreeTypeDir x (ex ** ep)
SPFDfmTreeMutGenTreeDir {x} f (Right (Left ex) ** ep) =
  SPFDfmMutGenTree1dir x (ex ** ep)
SPFDfmTreeMutGenTreeDir {x} f (Right (Right ex) ** ep) =
  SPFDfmMutGenTreeMdir {x} f (ex ** ep)

public export
SPFDfmTreeMutGenTreeAsn : {x : Type} ->
  (f : SlicePolyEndoFunc x) ->
  Sigma (SPFDfmTreeMutGenTreeDir {x} f) -> SPFDfmTreeGenSl x
SPFDfmTreeMutGenTreeAsn {x} f ((Left ec ** ep) ** dd) =
  -- A tree consists of either a one-node tree or a multi-node tree.
  -- `SPFDfmMutGenTreeTypeAsn` tells us which, and then we inject
  -- the answer into the part of the domain which represents specific
  -- tree types.
  SPFDfmTreeGenSpecificTree $ SPFDfmMutGenTreeTypeAsn x ((ec ** ep) ** dd)
SPFDfmTreeMutGenTreeAsn {x} f ((Right (Left ec) ** ep) ** dd) =
  -- A one-node tree has no directions, hence a trivial assignment.
  void $ SPFDfmMutGenTree1asn x ((ec ** ep) ** dd)
SPFDfmTreeMutGenTreeAsn {x} f ((Right (Right ec) ** efp) ** efd) =
  -- A multi-node tree's directions are themselves trees of _either_
  -- type, so we inject the return value of `SPFDfmMutGenTreeMasn`
  -- into the part of the domain which represents any type of tree.
  SPFDfmTreeGenAnyTree $ SPFDfmMutGenTreeMasn f ((ec ** efp) ** efd)

public export
SPFDfmTreeMutGenTree : {x : Type} ->
  SlicePolyEndoFunc x -> SlicePolyEndoFunc (SPFDfmTreeGenSl x)
SPFDfmTreeMutGenTree {x} f =
  (SPFDfmTreeMutGenTreePos {x} f **
   SPFDfmTreeMutGenTreeDir {x} f **
   SPFDfmTreeMutGenTreeAsn {x} f)

public export
SPFDfmTreeMutGenTreeSPFD : {x : Type} ->
  SlicePolyEndoFunc x -> SPFData (SPFDfmTreeGenSl x) (SPFDfmTreeGenSl x)
SPFDfmTreeMutGenTreeSPFD = SPFtoSPFD . SPFDfmTreeMutGenTree

public export
SPFDfmTreeMut : {x : Type} ->
  SlicePolyEndoFunc x -> SliceObj (SPFDfmTreeGenSl x)
SPFDfmTreeMut {x} = SPFDmu {x=(SPFDfmTreeGenSl x)} . SPFDfmTreeMutGenTreeSPFD

public export
SPFDfmPosMutSPF : {x : Type} -> SlicePolyEndoFunc x -> SliceObj x
SPFDfmPosMutSPF {x} f = SPFDfmTreeMut {x} f . Left

public export
SPFDfmPosMut : {x : Type} -> SPFData x x -> SliceObj x
SPFDfmPosMut {x} f = SPFDfmPosMutSPF {x} (SPFDtoSPF f)

-- Now we show that we can translate back and forth between free-monad
-- positions (AKA well-founded `f`-shaped trees) as generated by the
-- mutual recursion and by the usual least fixed point of `spfdFMposBase f`.

public export
SPFDfmPosToMutAlg : {x : Type} -> (f : SPFData x x) ->
  SliceAlgSPFD (spfdFMposBase {x} f) (SPFDfmPosMutSPF {x} (SPFDtoSPF f))
SPFDfmPosToMutAlg {x} f ex (Left () ** dmv_) =
  InSPFm
    (Left ex)
    (Left () **
     \esl, (Element0 () cond) =>
      rewrite sym cond in
      InSPFm (Right $ Left ex) (() ** \esl, (Element0 ev _) => void ev))
SPFDfmPosToMutAlg {x} f ex (Right ep ** dm) =
  InSPFm
    (Left ex)
    (Right () **
     \esl, (Element0 () cond) =>
      rewrite sym cond in
      InSPFm
        (Right $ Right ex)
        (ep **
         \esl', (Element0 (ex' ** fd') cond') =>
          rewrite sym cond' in dm ex' fd'))

public export
SPFDfmPosToMut : {x : Type} -> (f : SPFData x x) ->
  SliceMorphism {a=x} (SPFDfmPos {x} f) (SPFDfmPosMutSPF {x} (SPFDtoSPF f))
SPFDfmPosToMut {x} f =
  spfdCata {spfd=(spfdFMposBase f)} $ SPFDfmPosToMutAlg {x} f

-- To convert from the mutual-recursion-generated version of the
-- position-type to the translate-generated one, we can generate
-- a larger slice morphism from the whole set of mutual-recursion-generated
-- position-types (one-node form, `f`-shaped form, and either-form) to
-- the type of translate-generated positions.  This makes sense because
-- all the mutual-recursion-generated position-types do represent
-- free-monad-position types -- the extra components of the slice simply
-- generate more _specific_ types as well, allowing a type-level distinction
-- between one-node and `f`-shaped positions.

public export
SPFDfmPosFromMutCod : {x : Type} -> SPFData x x -> SliceObj (SPFDfmTreeGenSl x)
SPFDfmPosFromMutCod {x} f esl = SPFDfmPos {x} f (SPFDfmPosCodiag x esl)

public export
SPFDfmPosFromMutGenAlg : {x : Type} -> (f : SPFData x x) ->
  SliceAlgSPFD {x=(SPFDfmTreeGenSl x)}
    (SPFDfmTreeMutGenTreeSPFD {x} $ SPFDtoSPF f)
    (SPFDfmPosFromMutCod {x} f)
SPFDfmPosFromMutGenAlg {x} f (Left ex) (Left () ** dm) =
  dm (Right $ Left ex) (Element0 () Refl)
SPFDfmPosFromMutGenAlg {x} f (Left ex) (Right () ** dm) =
  dm (Right $ Right ex) (Element0 () Refl)
SPFDfmPosFromMutGenAlg {x} f (Right $ Left ex) (() ** dm) =
  InSPFm ex (Left () ** \_ => voidF _)
SPFDfmPosFromMutGenAlg {x} f (Right $ Right ex) (efp ** dm) =
  InSPFm
    ex
    (Right efp **
     \ex', efd' => dm (Left ex') (Element0 (ex' ** efd') Refl))

public export
SPFDfmPosFromMutGen : {x : Type} -> (f : SPFData x x) ->
  SliceMorphism {a=(SPFDfmTreeGenSl x)}
    (SPFDfmTreeMut {x} $ SPFDtoSPF f)
    (SPFDfmPosFromMutCod {x} f)
SPFDfmPosFromMutGen {x} f =
  spfdCata
    {a=(SPFDfmPosFromMutCod {x} f)}
    {spfd=(SPFDfmTreeMutGenTreeSPFD {x} $ SPFDtoSPF f)}
    (SPFDfmPosFromMutGenAlg {x} f)

public export
SPFDfmPosFromMut : {x : Type} -> (f : SPFData x x) ->
  SliceMorphism {a=x} (SPFDfmPosMutSPF {x} $ SPFDtoSPF f) (SPFDfmPos {x} f)
SPFDfmPosFromMut {x} f ex = SPFDfmPosFromMutGen {x} f (Left ex)

-- Now that we have defined the positions using mutual recursion, and
-- exhibited a correspondence between that definition and the standard
-- one in terms of the translate functor, we extend the mutual recursion
-- to include directions.

---------------------------------------------------------
---- Free monad from fixed point of post-composition ----
---------------------------------------------------------

-- We have noted above that the free monad may be viewed as a higher-order
-- fixed point of repeated post-composition of the free pointed endofunctor.
-- Let us now consider how to represent that particular post-composition
-- as a polynomial functor.  If we were to write it as an explicit mutual
-- recursion, it could look like this:
--
{-
mutual
  public export
  data SPFDfmmPos : {x : Type} ->
      SPFData x x -> SliceObj x where
    SFMPid : {x : Type} -> (f : SPFData x x) ->
      (ex : x) -> SPFDidPos x ex ->
      SPFDfmmPos {x} f ex
    SFMPcomp : {x : Type} -> (f : SPFData x x) ->
      (ex : x) -> SPFDcompPos {x} {y=x} {z=x} f (SPFDfmm {x} f) ex ->
      SPFDfmmPos {x} f ex

  public export
  data SPFDfmmDir : {x : Type} ->
      (f : SPFData x x) -> SPFdirType x x (SPFDfmmPos f) where
    SFMDid : {x : Type} -> {f : SPFData x x} ->
      {ex : x} -> {ep : SPFDidPos x ex} -> (ex' : x) -> SPFDidDir x ex ep ex' ->
      SPFDfmmDir {x} f ex (SFMPid {x} f ex ep) ex'
    SFMDcomp : {x : Type} -> {f : SPFData x x} ->
      {ex : x} -> {ep : SPFDcompPos {x} {y=x} {z=x} f (SPFDfmm {x} f) ex} ->
      (ex' : x) -> SPFDcompDir {x} {y=x} {z=x} f (SPFDfmm {x} f) ex ep ex' ->
      SPFDfmmDir {x} f ex (SFMPcomp {x} f ex ep) ex'

  public export
  SPFDfmm : {x : Type} ->
      SPFData x x -> SPFData x x
  SPFDfmm {x} f = SPFD (SPFDfmmPos {x} f) (SPFDfmmDir {x} f)
-}
--
-- But we can note that because of the insensitivity of `SPDcompPos`
-- to the direction-type of the pre-composed functor, the
-- `SPFDcompPos . SPFDfmm` part of `SFMPcomp` can be replaced with
-- simply `SPFDfmmPos`.  That breaks the mutual recursion, and
-- allows `SPFDfmmPos` to be defined first, independently of `SPFDfmmDir`
-- (and thus independently of the full `SPFDfmm`).  And what we are left
-- with is precisely what we have already defined as `SPFDfmPos`.
-- Therefore, we can continue to `SPFDfmmDir`, substitute `SPFDfmPos`
-- for `SPFDfmmPos`, and obtain the following (still explicitly-recursive)
-- definition for `SPFDfmmDir`:
--
{-
public export
data SPFDfmmDir : {x : Type} ->
    (f : SPFData x x) -> SPFdirType x x (SPFDfmPos {x} f) where
  SFMDid : {x : Type} -> {f : SPFData x x} ->
    (ex : x) ->
    -- `SPFDidPos x ex` is just `Unit` and `SPFDidDir x ex () ex'` is
    -- just `ex = ex`', so we can reduce the parameters to the `id`
    -- case to just `ex : x`.  This is how the `id` case amounts to just
    -- adding a single position with a single direction -- that is,
    -- taking the free pointed endofunctor.
    SPFDfmmDir {x} f ex (SPFDfmPosLeaf {x} f ex) ex
  SFMDcomp : {x : Type} -> {f : SPFData x x} ->
    {ex : x} ->
    {ep : SPFDcompPos {x} {y=x} {z=x}
      f (SPFD (SPFDfmPos {x} f) (SPFDfmmDir {x} f)) ex} ->
    (ex' : x) ->
    SPFDcompDir {x} {y=x} {z=x}
      f (SPFD (SPFDfmPos {x} f) (SPFDfmmDir {x} f)) ex ep ex' ->
    SPFDfmmDir {x} f ex (SPFDfmPosPath {x} f ex ep) ex'
-}
--
-- Next, we can substitute in the definitions of `SPFDcompPos` and
-- `SPFDcompDir` to simplify the definition:
--
{-
public export
data SPFDfmmDir : {x : Type} ->
    (f : SPFData x x) -> SPFdirType x x (SPFDfmPos {x} f) where
  SFMDid : {x : Type} -> {f : SPFData x x} ->
    (ex : x) ->
    -- `SPFDidPos x ex` is just `Unit` and `SPFDidDir x ex () ex'` is
    -- just `ex = ex`', so we can reduce the parameters to the `id`
    -- case to just `ex : x`.  This is how the `id` case amounts to just
    -- adding a single position with a single direction -- that is,
    -- taking the free pointed endofunctor.
    SPFDfmmDir {x} f ex (SPFDfmPosLeaf {x} f ex) ex
  SFMDcomp : {x : Type} -> {f : SPFData x x} ->
    {ec : x} ->
    {efp : spfdPos f ec} ->
    {fdmp : SliceMorphism {a=x} (spfdDir f ec efp) (SPFDfmPos {x} f)} ->
    (ex : x) ->
    (efd : spfdDir f ec efp ex) ->
    (ed : x) ->
    SPFDfmmDir {x} f ex (fdmp ex efd) ed ->
    SPFDfmmDir {x} f ec (SPFDfmPosPath {x} f ec (efp ** fdmp)) ed
-}
--
-- Now we convert from using `SPFdirType` to using `SPFdirSl`, and
-- turn the explicitly-recursive definition into the definition of
-- an endofunctor on `SPFdirSl` whose initial algebra will be
-- equivalent to the explicitly-recursive definition.
public export
data SPFDfmmDirF : {x : Type} ->
    (f : SPFData x x) ->
    SPFdirSl x x (SPFDfmPos {x} f) ->
    SPFdirSl x x (SPFDfmPos {x} f)
    where
  SFMDid : {x : Type} -> {f : SPFData x x} ->
    {dir : SPFdirSl x x (SPFDfmPos {x} f)} ->
    (ex : x) ->
    -- `SPFDidPos x ex` is just `Unit` and `SPFDidDir x ex () ex'` is
    -- just `ex = ex`', so we can reduce the parameters to the `id`
    -- case to just `ex : x`.  This is how the `id` case amounts to just
    -- adding a single position with a single direction -- that is,
    -- taking the free pointed endofunctor.
    SPFDfmmDirF {x} f dir ((ex ** SPFDfmPosLeaf {x} f ex), ex)
  SFMDcomp : {x : Type} -> {f : SPFData x x} ->
    {dir : SPFdirSl x x (SPFDfmPos {x} f)} ->
    {ec : x} ->
    {efp : spfdPos f ec} ->
    {fdmp : SliceMorphism {a=x} (spfdDir f ec efp) (SPFDfmPos {x} f)} ->
    (ex : x) ->
    (efd : spfdDir f ec efp ex) ->
    (ed : x) ->
    (dd : dir ((ex ** fdmp ex efd), ed)) ->
    SPFDfmmDirF {x} f dir ((ec ** SPFDfmPosPath {x} f ec (efp ** fdmp)), ed)
--
-- Now, finally, we can read off the positions and directions of the
-- polynomial representation of `SPFDfmmDir` as an endofunctor on
-- `SPFdirSl x x (SPFDfPos {x} f)`:
--
public export
SPFDfmmDirPos : {x : Type} -> (f : SPFData x x) ->
  SPFdirSl x x (SPFDfmPos {x} f)
SPFDfmmDirPos {x} f ((ec ** InSPFm ec (Left () ** fdmp)), ed) =
  ec = ed
SPFDfmmDirPos {x} f ((ec ** InSPFm ec (Right efp ** fdmp)), ed) =
  (ei : x ** spfdDir f ec efp ei)

public export
SPFDfmmDirDir : {x : Type} -> (f : SPFData x x) ->
  SPFdirType
    (SPFdirSlBase x x (SPFDfmPos {x} f))
    (SPFdirSlBase x x (SPFDfmPos {x} f))
    (SPFDfmmDirPos {x} f)
SPFDfmmDirDir {x} f
  ((ex ** InSPFm ex (Left () ** fdmp)), ex)
  Refl
  _ =
    Void
SPFDfmmDirDir {x} f
  ((ec ** InSPFm ec (Right efp ** fdmp)), ed)
  (ei ** efd)
  ((ec' ** ep'), ed') =
    ((eieq : ec' = ei ** ep' = (rewrite eieq in fdmp ei efd)),
     ed' = ed)

public export
spfdFMMdirDirPosNotLeft : {x : Type} -> {f : SPFData x x} ->
  {ec : x} -> {ep : SPFDfmPos {x} f ec} -> {ed : x} ->
  {dp : SPFDfmmDirPos {x} f ((ec ** ep), ed)} ->
  {sld : SPFdirSlBase x x (SPFDfmPos {x} f)} ->
  SPFDfmmDirDir {x} f ((ec ** ep), ed) dp sld ->
  fst (OutSPFm {spfd=(spfdFMposBase {x} f)} ec ep) = Left () ->
  Void
spfdFMMdirDirPosNotLeft {x} {f} {ep=(InSPFm ec (Left () ** fdmp))} {dp=Refl}
  dd Refl = dd
spfdFMMdirDirPosNotLeft {x} {f} {ep=(InSPFm ec (Right efp ** fdmp))}
  dd eq = voidRightLeft eq

public export
SPFDnoLeafDirs : {x : Type} -> {f : SPFData x x} ->
  {ex : x} -> {ec : x} -> {ep : SPFDfmPos {x} f ec} -> {ed : x} ->
  SPFDfmmDirDir {x} f
    ((ex ** SPFDfmPosLeaf {x} f ex), ex)
    Refl
    ((ec ** ep), ed) ->
  Void
SPFDnoLeafDirs {x} {f} dd = dd

-- And now we can take the fixed point of `SPFDfmmDirDir` to generate the
-- directions of the free monad, and put them together with `SPFDfmPos`
-- to obtain the full free monad as an `SPFData`.
public export
SPFDfmmDirSPFD : {x : Type} -> (f : SPFData x x) ->
  SPFData
    (SPFdirSlBase x x (SPFDfmPos {x} f))
    (SPFdirSlBase x x (SPFDfmPos {x} f))
SPFDfmmDirSPFD {x} f = SPFD (SPFDfmmDirPos {x} f) (SPFDfmmDirDir {x} f)

public export
SPFDfmmDirSl : {x : Type} -> (f : SPFData x x) -> SPFdirSl x x (SPFDfmPos {x} f)
SPFDfmmDirSl {x} f =
  SPFDmu {x=(SPFdirSlBase x x (SPFDfmPos {x} f))} (SPFDfmmDirSPFD {x} f)

public export
SPFDfmmDir : {x : Type} -> (f : SPFData x x) -> SPFdirType x x (SPFDfmPos {x} f)
SPFDfmmDir {x} f = SPFdirFromSl (SPFDfmmDirSl {x} f)

public export
SPFDfmm : {x : Type} -> SPFData x x -> SPFData x x
SPFDfmm {x} f = SPFD (SPFDfmPos {x} f) (SPFDfmmDir {x} f)

public export
SPFDfmmLeaf : {x : Type} -> {f : SPFData x x} ->
  (ex : x) ->
  SPFDfmmDir {x} f ex (SPFDfmPosLeaf {x} f ex) ex
SPFDfmmLeaf {x} {f} ex =
  InSPFm
    ((ex ** SPFDfmPosLeaf {x} f ex), ex)
    (Refl ** \((ec ** ep), ed), dd =>
      void $ SPFDnoLeafDirs {ex} {ec} {ep} {ed} dd)

-- As a position of the free monad represents a tree with variables
-- at the leaves, its direction-type is that of all the leaves below
-- it.  A direction of a tree which is an internal node (i.e. not itself
-- a leaf) is a path to a leaf below it.
public export
SPFDfmmPath : {x : Type} -> {f : SPFData x x} ->
  (ec : x) -> (el : InterpSPFData {dom=x} {cod=x} f (SPFDfmPos {x} f) ec) ->
  (ei : x) -> (fd : spfdDir f ec (fst el) ei) ->
  (ed : x) -> SPFDfmmDir {x} f ei (snd el ei fd) ed ->
  SPFDfmmDir {x} f ec (SPFDfmPosPath {x} f ec el) ed
SPFDfmmPath {x} {f} ec (efp ** fdmp) ei fd ed dd =
  InSPFm
    ((ec ** SPFDfmPosPath {x} f ec (efp ** fdmp)), ed)
    ((ei ** fd) **
     \((ei ** InSPFm ei ep'), ed), ((Refl ** fdmpeq), Refl) =>
      rewrite fdmpeq in dd)

-- The elimination rule for the directions of the free monad at
-- a given position.
public export
SPFDfmmDirEvalAlg : {x : Type} -> {f : SPFData x x} ->
  (a : SliceObj x) ->
  ((ex : x) -> SPFDfmmDir f ex (SPFDfmPosLeaf {x} f ex) ex -> a ex) ->
  SliceAlgSPFD
    {x=(SPFdirSlBase x x (SPFDfmPos {x} f))}
    (SPFDfmmDirSPFD {x} f)
    (a . Builtin.snd)
SPFDfmmDirEvalAlg {x} {f} a lelim
  ((ex ** InSPFm ex (Left () ** fdmp)), ex) (Refl ** ddmv_) =
    lelim ex (SPFDfmmLeaf {x} {f} ex)
SPFDfmmDirEvalAlg {x} {f} a lelim
  ((ec ** InSPFm ec (Right efp ** fdmp)), ed) ((ei ** efd) ** ddm) =
    ddm ((ei ** fdmp ei efd), ed) ((Refl ** Refl), Refl)

public export
SPFDfmmDirEval : {x : Type} -> {f : SPFData x x} ->
  (a : SliceObj x) ->
  ((ex : x) -> SPFDfmmDir f ex (SPFDfmPosLeaf {x} f ex) ex -> a ex) ->
  {ec : x} -> (ep : SPFDfmPos {x} f ec) ->
  SliceMorphism {a=x} (SPFDfmmDir {x} f ec ep) a
SPFDfmmDirEval {x} {f} a lelim {ec} ep ed dd =
  spfdCata
    {x=(SPFdirSlBase x x (SPFDfmPos {x} f))}
    {spfd=(SPFDfmmDirSPFD {x} f)}
    {a=(a . Builtin.snd)}
    (SPFDfmmDirEvalAlg {x} {f} a lelim)
    ((ec ** ep), ed)
    dd

------------------------------------------------------------
---- Free monad from mutually-recursive inductive types ----
------------------------------------------------------------

-- We have shown above that for any polynomial functor `f`, there is a
-- polynomial-functor internalization of the direction-type of post-composition
-- with `spfdFreePointed f`, and we have noted that the higher-order fixed
-- point of repeating that composition produces the free monad of a polynomial
-- functor, so we may conclude that the direction-type of the free monad
-- is the fixed point of that composition's internalization, which we have
-- called `SPFDcompDirPointedSPFD`.
--
-- Thus we can specialize the internalization of post-composition to define
-- the directions of the free monad.  Firstly, the non-recursive
-- post-composition -- the operation which we will iterate -- can be
-- specialized to take slices of the free monad's position-type to
-- slices of the application of the base functor of the free monad's
-- position-type.
public export
SPFDfmDirBasePos : {x : Type} -> (f : SPFData x x) ->
  SPFdirSl x x (SPFDcompPosPointedSl f $ SPFDfmPos {x} f)
SPFDfmDirBasePos {x} f = SPFDcompDirPointedSPFDpos {x} f (SPFDfmPos {x} f)

public export
SPFDfmDirBaseDir : {x : Type} -> (f : SPFData x x) ->
  SPFdirType
    (SPFdirSlBase x x $ SPFDfmPos {x} f)
    (SPFdirSlBase x x (SPFDcompPosPointedSl f $ SPFDfmPos {x} f))
    (SPFDfmDirBasePos {x} f)
SPFDfmDirBaseDir {x} f = SPFDcompDirPointedSPFDdir {x} f (SPFDfmPos {x} f)

public export
SPFDfmDirBase : {x : Type} -> (f : SPFData x x) ->
  SPFData
    (SPFdirSlBase x x $ SPFDfmPos {x} f)
    (SPFdirSlBase x x (SPFDcompPosPointedSl f $ SPFDfmPos {x} f))
SPFDfmDirBase {x} f = SPFDcompDirPointedSPFD {x} f (SPFDfmPos {x} f)

-- Now we note that, although `SPFDfmDirBase` is not an endofunctor,
-- we can inject its domain into its codomain, in this specific
-- case where the position-type is that of the free monad.
public export
SPFDfmDirBaseInj : {x : Type} -> (f : SPFData x x) ->
  SliceMorphism {a=x}
    (SPFDfmPos {x} f)
    (SPFDcompPosPointedSl f $ SPFDfmPos {x} f)
SPFDfmDirBaseInj {x} f ex (InSPFm ex (Left () ** dmv_)) = Left ()
SPFDfmDirBaseInj {x} f ex (InSPFm ex (Right ep ** dm)) = Right (ep ** dm)

-- We furthermore note that `SPFDfmDirBaseInj` is an isomorphism.
-- This is its inverse.
public export
SPFDfmDirBaseInjInv : {x : Type} -> (f : SPFData x x) ->
  SliceMorphism {a=x}
    (SPFDcompPosPointedSl f $ SPFDfmPos {x} f)
    (SPFDfmPos {x} f)
SPFDfmDirBaseInjInv {x} f ex (Left ()) = InSPFm ex (Left () ** \_ => voidF _)
SPFDfmDirBaseInjInv {x} f ex (Right (ep ** dm)) = InSPFm ex (Right ep ** dm)

public export
SPFDfmDirAlgBaseFdir : {x : Type} -> {f : SPFData x x} -> {pos : SliceObj x} ->
  SliceAlgSPFD {x} (spfdFMposBase {x} f) pos ->
  SPFdirType x x pos ->
  SPFdirType x x (InterpSPFData (spfdFMposBase {x} f) pos)
SPFDfmDirAlgBaseFdir {x} {f} {pos} alg dir ex (Left () ** pmv_) ex' =
  (ex = ex', dir ex (alg ex (Left () ** pmv_)) ex)
SPFDfmDirAlgBaseFdir {x} {f} {pos} alg dir ex (Right efp ** fdmp) ex' =
  SPFDcompDir {x} {y=x} {z=x} f (SPFD pos dir) ex (efp ** fdmp) ex'

public export
SPFDfmDirAlgBaseFdirPointed : {x : Type} -> {f : SPFData x x} ->
  {pos : SliceObj x} ->
  SliceMorphism {a=x} (SPFDcompPosPointedSl {x} f pos) pos ->
  SPFdirType x x pos ->
  SPFdirType x x (SPFDcompPosPointedSl f pos)
SPFDfmDirAlgBaseFdirPointed {x} {f} {pos} alg dir =
  spfdDirComp
    (SPFDfmDirAlgBaseFdir {x} {f} {pos}
      (SPFDfmDirAlgBaseFdirPosBaseAlgPointed {x} {f} {pos} alg)
      dir)
    (SPFDcompPosPointedSPFDfromF {x} f pos)

public export
SPFDfmDirAlgBaseEndoFdir : {x : Type} ->
  {f : SPFData x x} -> {pos : SliceObj x} ->
  SliceAlgSPFD {x} (spfdFMposBase {x} f) pos ->
  SliceCoalgSPFD {x} (spfdFMposBase {x} f) pos ->
  SPFdirType x x pos ->
  SPFdirType x x pos
SPFDfmDirAlgBaseEndoFdir {x} {f} {pos} alg coalg dir =
  spfdDirComp (SPFDfmDirAlgBaseFdir {x} {f} {pos} alg dir) coalg

public export
SPFDfmDirBaseEndoFdir : {x : Type} -> {f : SPFData x x} ->
  SPFdirType x x (SPFDfmPos {x} f) ->
  SPFdirType x x (SPFDfmPos {x} f)
SPFDfmDirBaseEndoFdir {x} {f} =
  SPFDfmDirAlgBaseEndoFdir {x} {f} {pos=(SPFDfmPos {x} f)} InSPFm OutSPFm

-----------------------------------------
---- Free monad from recursive types ----
-----------------------------------------

public export
SPFDtranslateTypeAlg : {x : Type} -> (f : SPFData x x) -> SliceObj x ->
  SPFDtypeAlg {x} (spfdFMposBase {x} f)
SPFDtranslateTypeAlg {x} f v =
  SPFDfmDirAlgBaseFdir
    {x}
    {f}
    {pos=(const $ SliceObj x)}
    (\_, _ => v)
    (sliceId $ const $ SliceObj x)

-- The type-algebra which generates the type of leaves of an `f`-shaped
-- tree -- which is the type of directions of the free monad.
public export
SPFDfmDirAlg : {x : Type} -> (f : SPFData x x) ->
  SPFDtypeAlg {x} (spfdFMposBase {x} f)
SPFDfmDirAlg {x} f = SPFDtranslateTypeAlg {x} f (SliceObjTerminal x)

public export
SPFDfmDir : {x : Type} -> (f : SPFData x x) ->
  SPFdirType x x (SPFDfmPos {x} f)
SPFDfmDir {x} f = spfdDirMu {x} {f=(spfdFMposBase {x} f)} (SPFDfmDirAlg {x} f)

-- For documentation, we show a property of the above type signature.
public export
0 SPFDfmDirIsCataAlg : {x : Type} -> (f : SPFData x x) ->
  (ex : x) -> (ep : spfdPos f ex) ->
  (pm : SliceMorphism {a=x} (spfdDir f ex ep) (SPFDfmPos {x} f)) ->
  (ex' : x) ->
    SPFDfmDir {x} f ex (InSPFm ex (Right ep ** pm)) ex' =
    SPFDcoprodTypeAlg f ex (ep ** sliceComp (SPFDfmDir f) pm) ex'
SPFDfmDirIsCataAlg {x} f ex ep pm ex' = Refl

-- Introduction and elimination rules for directions of the free monad.

-- For any functor, the tree consisting of a single leaf -- effectively,
-- a pure pattern variable -- is a position of the free monad, and it
-- has one direction, which represents filling in that pattern variable.
-- Put another way, it's an open term consisting simply of a metavariable.
public export
SPFDfmLeaf : {x : Type} -> {f : SPFData x x} ->
  (ex : x) ->
  SPFDfmDir {x} f ex (SPFDfmPosLeaf {x} f ex) ex
SPFDfmLeaf {x} {f} ex = (Refl, ())

-- As a position of the free monad represents a tree with variables
-- at the leaves, its direction-type is that of all the leaves below
-- it.  A direction of a tree which is an internal node (i.e. not itself
-- a leaf) is a path to a leaf below it.
public export
SPFDfmPath : {x : Type} -> {f : SPFData x x} ->
  (ec : x) -> (el : InterpSPFData {dom=x} {cod=x} f (SPFDfmPos {x} f) ec) ->
  (ei : x) -> (fd : spfdDir f ec (fst el) ei) ->
  (ed : x) -> SPFDfmDir {x} f ei (snd el ei fd) ed ->
  SPFDfmDir {x} f ec (SPFDfmPosPath {x} f ec el) ed
SPFDfmPath {x} {f} ec el ei fd ed dd = ((ei ** fd) ** dd)

-- The elimination rule for the directions of the free monad at
-- a given position.
public export
SPFDfmDirEval : {x : Type} -> {f : SPFData x x} ->
  (a : SliceObj x) ->
  ((ex : x) -> SPFDfmDir f ex (SPFDfmPosLeaf {x} f ex) ex -> a ex) ->
  {ec : x} -> (ep : SPFDfmPos {x} f ec) ->
  SliceMorphism {a=x} (SPFDfmDir {x} f ec ep) a
SPFDfmDirEval {x} {f} a lelim
  {ec} (InSPFm ec (Left () ** fdmpv_)) ec (Refl, ()) =
    lelim ec (Refl, ())
SPFDfmDirEval {x} {f} a lelim
    {ec} (InSPFm ec (Right efp ** fdmp)) ed ((ex ** dd) ** dm)
    with (fdmp ex dd) proof fdmpeq
  SPFDfmDirEval {x} {f} a lelim
    {ec} (InSPFm ec (Right efp ** fdmp)) ed ((ex ** dd) ** dm)
    | InSPFm ex (fdmp' ** dm') =
      SPFDfmDirEval {x} {f} a lelim {ec=ex} (fdmp ex dd) ed $
        rewrite fdmpeq in dm

public export
SPFDfreeM : {x : Type} -> SPFData x x -> SPFData x x
SPFDfreeM {x} f = spfdDepSPFD {x} {f=(spfdFMposBase {x} f)} (SPFDfmDirAlg {x} f)

--------------------------------------
---- Interpretation of free monad ----
--------------------------------------

public export
SPFDfreeMAlg : {x : Type} -> SPFData x x -> SliceObj x -> Type
SPFDfreeMAlg {x} f = SliceAlgSPFD {x} (SPFDfreeM {x} f)

-- The free monad of `f` comes from a ("free-forgetful") adjunction between
-- the category of algebras of `f` (on the left) and the base (slice)
-- category (on the right).
--
-- The right adjoint is the forgetful one -- it simply forgets the action
-- of the algebra, leaving only the carrier.
--
-- The left adjoint is the free monad -- it takes a slice object and
-- produces its free algebra.  This is the carrier component of the
-- object-map component of the left adjoint.
public export
InterpSPFDfreeM : {x : Type} -> SPFData x x -> SliceEndofunctor x
InterpSPFDfreeM {x} f = InterpSPFData {dom=x} {cod=x} (SPFDfreeM {x} f)

-- This is the action component of the object-map component of the left adjoint.
public export
InSPFfc : {x : Type} -> {f : SPFData x x} -> {slv : SliceObj x} ->
  SliceAlgSPFD {x} f (InterpSPFDfreeM {x} f slv)
InSPFfc {x} {f} {slv} ex (ep ** dm) =
  (InSPFm ex (Right ep ** \ex', dd => fst (dm ex' dd)) **
   \ex', ((ex'' ** dd) ** alg) => snd (dm ex'' dd) ex' alg)

-- This is the morphism-map component of the left adjoint.
public export
InterpSPFDfreeMmap : {x : Type} -> {f : SPFData x x} -> {a, b : SliceObj x} ->
  SliceMorphism {a=x} a b ->
  SliceMorphism {a=x} (InterpSPFDfreeM {x} f a) (InterpSPFDfreeM {x} f b)
InterpSPFDfreeMmap {x} {f} {a} {b} =
  InterpSPFDataMap {dom=x} {cod=x} (SPFDfreeM {x} f) a b

-- This is the unit of the free-monad adjunction.
public export
InSPFfmv : {x : Type} -> (f : SPFData x x) ->
  SPFnt (SPFDid x) (SPFDfreeM {x} f)
InSPFfmv {x} f =
  SPFDm
    (\ex, () => InSPFm ex (Left () ** \_ => voidF _))
    (\ex, (), ex', (Refl, ()) => Refl)

public export
InSPFfv : {x : Type} -> {f : SPFData x x} -> {slv : SliceObj x} ->
  SliceMorphism {a=x} slv (InterpSPFDfreeM {x} f slv)
InSPFfv {x} {f} {slv} ex eslv =
  InterpSPFnt {dom=x} {cod=x} (SPFDid x) (SPFDfreeM {x} f) (InSPFfmv f) slv ex
    (() ** \ex, Refl => eslv)

public export
SPFDfmDirMap : {x : Type} -> (f : SPFData x x) ->
  (slv : SliceObj x) -> (ex : x) -> SliceObj (SPFDfmPos {x} f ex)
SPFDfmDirMap {x} f slv ex epp = SliceMorphism {a=x} (SPFDfmDir {x} f ex epp) slv

-- This is the counit of the free-monad adjunction.
public export
spfdFreeCounitCurried : {x : Type} -> (f : SPFData x x) ->
  (sla : SliceObj x) -> SliceAlgSPFD f sla ->
  (ex : x) -> (epp : SPFDfmPos {x} f ex) ->
  SPFDfmDirMap {x} f sla ex epp ->
  sla ex
spfdFreeCounitCurried {x} f sla alg ex (InSPFm ex (Left () ** pm)) dm =
  dm ex (Refl, ())
spfdFreeCounitCurried {x} f sla alg ex (InSPFm ex (Right ep ** pm)) dm =
  alg
    ex
    (ep **
     \ex', fd' =>
      spfdFreeCounitCurried {x} f sla alg ex' (pm ex' fd') $
        \ex'', dd' => dm ex'' ((ex' ** fd') ** dd'))

public export
spfdFreeCounit : {x : Type} -> (f : SPFData x x) ->
  (sla : SliceObj x) -> SliceAlgSPFD f sla ->
  SliceMorphism {a=x} (InterpSPFDfreeM {x} f sla) sla
spfdFreeCounit {x} f sla alg ex (ep ** dm) =
  spfdFreeCounitCurried {x} f sla alg ex ep dm

-- This is the right adjunct of the free-monad adjunction.
public export
spfdFreeEval : {x : Type} -> (f : SPFData x x) -> (slv, sla : SliceObj x) ->
  SliceAlgSPFD f sla -> SliceMorphism {a=x} slv sla ->
  SliceMorphism {a=x} (InterpSPFDfreeM {x} f slv) sla
spfdFreeEval {x} f slv sla alg subst =
  sliceComp
    (spfdFreeCounit {x} f sla alg)
    (InterpSPFDfreeMmap {f} subst)

-- This is the left adjunct of the free-monad adjunction.
public export
spfdFreeLAdj : {x : Type} -> (f : SPFData x x) -> (slv, sla : SliceObj x) ->
  SliceMorphism {a=x} (InterpSPFDfreeM {x} f slv) sla ->
  SliceMorphism {a=x} slv sla
spfdFreeLAdj {x} f slv sla alg = sliceComp alg InSPFfv

-- This is the comultiplication of the free-monad adjunction.

public export
spfdFreeComultOnPos : {x : Type} -> (f : SPFData x x) ->
  SPFntPos
    (SPFDfreeM {x} f)
    (SPFDcomp x x x (SPFDfreeM {x} f) (SPFDfreeM {x} f))
spfdFreeComultOnPos {x} f ex em =
  (InSPFm ex (Left () ** \_ => voidF _) ** \ex, (Refl, ()) => em)

public export
spfdFreeComultOnDir : {x : Type} -> (f : SPFData x x) ->
  SPFntDir
    (SPFDfreeM {x} f)
    (SPFDcomp x x x (SPFDfreeM {x} f) (SPFDfreeM {x} f))
    (spfdFreeComultOnPos {x} f)
spfdFreeComultOnDir {x} f ex em ex' ((ex ** (Refl, ())) ** em') = em'

public export
spfdFreeComult : {x : Type} -> (f : SPFData x x) ->
  SPFnt (SPFDfreeM {x} f) (SPFDcomp x x x (SPFDfreeM {x} f) (SPFDfreeM {x} f))
spfdFreeComult {x} f =
  SPFDm (spfdFreeComultOnPos {x} f) (spfdFreeComultOnDir {x} f)

--------------------------------------------------------------------
---- Equivalence of free monad with fixed point of base functor ----
--------------------------------------------------------------------

-- Here we show how to translate between the representation of the free
-- monad that we used to generate the polynomial representation and the
-- interpretation (by `InterpSPFData`) of the resulting polynomial
-- representation.

public export
spfdGenToFree : {x : Type} -> (f : SPFData x x) ->
  SliceNatTrans {x=x} {y=x} (spfdGenFree {x} f) (InterpSPFDfreeM {x} f)
spfdGenToFree {x} f sx =
  spfdFMeval {x} f sx (InterpSPFDfreeM {x} f sx)
    (InSPFfc {x} {f} {slv=sx})
    (InSPFfv {x} {f} {slv=sx})

public export
spfdFreeToGenAlg : {x : Type} -> (f : SPFData x x) -> (sx : SliceObj x) ->
  SliceAlgSPFD f (spfdGenFree {x} f sx)
spfdFreeToGenAlg {x} f sx ex (ep ** dm) = InSPFm ex (Right ep ** dm)

public export
spfdGenUnit : {x : Type} -> (f : SPFData x x) ->
  SlicePure {c=x} (spfdGenFree {x} f)
spfdGenUnit {x} f sx ex esx = InSPFm ex (Left esx ** \_, ev => void ev)

public export
spfdFreeToGen : {x : Type} -> (f : SPFData x x) ->
  SliceNatTrans {x=x} {y=x} (InterpSPFDfreeM {x} f) (spfdGenFree {x} f)
spfdFreeToGen {x} f sx =
  spfdFreeEval {x} f sx
    (spfdGenFree {x} f sx)
    (spfdFreeToGenAlg {x} f sx)
    (spfdGenUnit {x} f sx)

------------------------------
------------------------------
---- M-types from W-types ----
------------------------------
------------------------------

-- We follow the construction (of M-types from W-types) in section 4
-- of Abbott, Altenkirch, and Ghani's "Containers: Constructing
-- strictly positive types".

-- The base functor of the object which the paper calls `M-hat`.
public export
MHbasePos : {x : Type} -> (f : SPFData x x) -> SliceObj x
MHbasePos {x} f = spfdPos (spfdTranslateTerminal f)

-- What the paper writes as "bottom" -- "points where the tree has been
-- cut off".
public export
mhpCut : {0 x : Type} -> (f : SPFData x x) -> (ex : x) -> MHbasePos {x} f ex
mhpCut {x} f ex = Left ()

public export
mhpSup : {0 x : Type} -> (f : SPFData x x) ->
  {ex : x} -> spfdPos f ex -> MHbasePos {x} f ex
mhpSup {x} f {ex} = Right

public export
MHbaseDir : {x : Type} ->
  (f : SPFData x x) -> SPFdirType x x (MHbasePos {x} f)
MHbaseDir {x} f = spfdDir (spfdTranslateTerminal f)

public export
mhdSup : {0 x : Type} -> {f : SPFData x x} ->
  {exc : x} -> {efp : spfdPos f exc} -> {exd : x} ->
  spfdDir f exc efp exd -> MHbaseDir {x} f exc (mhpSup {x} f {ex=exc} efp) exd
mhdSup {x} {f} {exc} {efp} {exd} = id

public export
MHbaseF : {x : Type} -> SPFData x x -> SPFData x x
MHbaseF {x} f = SPFD (MHbasePos {x} f) (MHbaseDir {x} f)

public export
MH : {x : Type} -> SPFData x x -> SliceObj x
MH = SPFDfmPos

-- The base functor of the object which the paper calls `M-bar`.
public export
MBbasePos : {x : Type} -> (f : SPFData x x) -> SliceObj x
MBbasePos {x} f ex = Either (MHbasePos {x} f ex) Unit

-- What the paper writes as "bottom" -- "points where the tree has been
-- cut off".
public export
mbpCut : {0 x : Type} -> (f : SPFData x x) -> (ex : x) -> MBbasePos {x} f ex
mbpCut {x} f ex = Left $ mhpCut {x} f ex

public export
mbpSup : {0 x : Type} -> (f : SPFData x x) ->
  {ex : x} -> spfdPos f ex -> MBbasePos {x} f ex
mbpSup {x} f {ex} ep = Left $ mhpSup {x} f {ex} ep

-- What the paper writes as "star".
public export
mbpStar : {0 x : Type} -> (f : SPFData x x) -> (ex : x) -> MBbasePos {x} f ex
mbpStar {x} f ex = Right ()

public export
MBbaseDir : {x : Type} ->
  (f : SPFData x x) -> SPFdirType x x (MBbasePos {x} f)
MBbaseDir {x} f exc ep exd = case ep of
  Left epl => MHbaseDir {x} f exc epl exd
  Right () => Void

public export
mbdSup : {0 x : Type} -> {f : SPFData x x} ->
  {exc : x} -> {efp : spfdPos f exc} -> {exd : x} ->
  spfdDir f exc efp exd -> MBbaseDir {x} f exc (mbpSup {x} f {ex=exc} efp) exd
mbdSup {x} {f} {exc} {efp} {exd} = id

public export
MBbaseF : {x : Type} -> SPFData x x -> SPFData x x
MBbaseF {x} f = SPFD (MBbasePos {x} f) (MBbaseDir {x} f)

public export
MB : {x : Type} -> SPFData x x -> SliceObj x
MB {x} f = SPFDmu {x} (MBbaseF {x} f)

public export
mbTruncAlg : {x : Type} -> {f : SPFData x x} ->
  Nat -> SliceAlgSPFD {x} (MBbaseF {x} f) (MB {x} f)
mbTruncAlg {x} {f} Z ex epdm = InSPFm ex (mbpCut {x} f ex ** \_, v => void v)
mbTruncAlg {x} {f} (S n) ex epdm = case epdm of
  (Left (Left ()) ** _) => InSPFm ex (mbpStar {x} f ex ** \_, v => void v)
  (Left (Right efp) ** dm) =>
    spfdCata {spfd=(MBbaseF {x} f)} {a=(MB {x} f)}
      (mbTruncAlg {x} {f} n)
      ex
      (InSPFm ex epdm)
  (Right () ** _) => InSPFm ex (mbpStar {x} f ex ** \_, v => void v)

public export
mbTrunc : {x : Type} -> {f : SPFData x x} ->
  Nat -> SliceMorphism {a=x} (MB {x} f) (MB {x} f)
mbTrunc {x} {f} =
  spfdCata {a=(MB {x} f)} {spfd=(MBbaseF {x} f)} . mbTruncAlg {x} {f}

public export
mbIncl : {x : Type} -> (f : SPFData x x) ->
  SliceMorphism {a=x} (MH {x} f) (MB {x} f)
mbIncl {x} f =
  spfdCata {a=(MB {x} f)} {spfd=(MHbaseF {x} f)} $
    \ex, (ep ** dm) => InSPFm ex (Left ep ** dm)

public export
mhTrunc : {x : Type} -> {f : SPFData x x} ->
  Nat -> SliceMorphism {a=x} (MH {x} f) (MB {x} f)
mhTrunc {x} {f} n = sliceComp {a=x} (mbTrunc {x} {f} n) (mbIncl {x} f)

-- Called simply `M` in the paper, this is the terminal (or "final")
-- coalgebra of the given polynomial functor.
public export
SPFDnuM : {x : Type} -> SPFData x x -> SliceObj x
SPFDnuM {x} f ex =
  (m : Nat -> MH {x} f ex **
   (n : Nat) -> mbIncl {x} f ex (m n) = mhTrunc {x} {f} n ex (m $ S n))

--------------------------------------------------------------
--------------------------------------------------------------
---- Terminal coalgebras of slice polynomial endofunctors ----
--------------------------------------------------------------
--------------------------------------------------------------

--------------------------------------
--- `SPFData` terminal coalgebras ----
--------------------------------------

public export
SPFDnu : {x : Type} -> SPFData x x -> SliceObj x
SPFDnu {x} f = ImSliceNu {c=x} (InterpSPFData {dom=x} {cod=x} f)

public export
spfdAna : {0 x : Type} -> {0 spfd : SPFData x x} -> {a : SliceObj x} ->
  SliceCoalgSPFD spfd a -> SliceMorphism {a=x} a (SPFDnu {x} spfd)
spfdAna {x} {spfd} {a} =
  imSlAna {c=x} {f=(InterpSPFData {dom=x} {cod=x} spfd)} {sa=a}

public export
InSPFn : {x : Type} -> {spfd : SPFData x x} ->
  SliceCoalgSPFD {x} spfd (SPFDnu {x} spfd)
InSPFn {x} {spfd} =
  imSlTermCoalg {c=x} {f=(InterpSPFData {dom=x} {cod=x} spfd)}
  $ InterpSPFDataMap {dom=x} {cod=x} spfd

-- The inverse of `InSPFn`, which we know by Lambek's theorem should
-- exist.
public export
OutSPFn : {x : Type} -> {spfd : SPFData x x} ->
  SliceAlgSPFD {x} spfd (SPFDnu {x} spfd)
OutSPFn {x} {spfd} =
  imSlTermCoalgInv {c=x} {f=(InterpSPFData {dom=x} {cod=x} spfd)}
  $ InterpSPFDataMap {dom=x} {cod=x} spfd

-----------------------------------------------------
---- Paranatural terminal-coalgebra Yoneda forms ----
-----------------------------------------------------

-- Paranatural (also called "strong dinatural") Yoneda lemmas for
-- terminal coalgebras -- these (or at least one of them, I'm not sure
-- which -- maybe both) are alluded to after "Proposition 1" of Uustalu's
-- "A note on strong dinaturality, initial algebras and uniform parameterized
-- fixpoint operators", but not explicitly formulated there (let alone proven).

-- The following isomorphism is a universal, contravariant form.

public export
spfdCoalgParaNTtoNuContra : {x : Type} ->
  (f : SPFData x x) -> (k : SliceObj x -> Type) ->
  ((a : SliceObj x) -> SliceCoalgSPFD {x} f a -> k a) -> k (SPFDnu {x} f)
spfdCoalgParaNTtoNuContra {x} f k pnt =
  pnt (SPFDnu {x} f) $ InSPFn {x} {spfd=f}

public export
spfdNuToCoalgParaNTcontra : {x : Type} ->
  (f : SPFData x x) -> (k : SliceObj x -> Type) ->
  (kcontramap : (y, z : SliceObj x) -> SliceMorphism {a=x} z y -> k y -> k z) ->
  k (SPFDnu {x} f) -> ((a : SliceObj x) -> SliceCoalgSPFD {x} f a -> k a)
spfdNuToCoalgParaNTcontra {x} f k kcm knu a coalg =
  kcm (SPFDnu {x} f) a (spfdAna {x} {spfd=f} {a} coalg) knu

-- The above in a form with the presheaf `k : SliceObj x -> Type`
-- generalized to a (contravariant) slice functor.

public export
spfdCoalgParaNTtoNuContraSl : {x, w : Type} ->
  (f : SPFData x x) -> (k : SliceFunctor x w) ->
  ((a : SliceObj x) -> SliceCoalgSPFD {x} f a -> Pi {a=w} (k a)) ->
  Pi {a=w} (k (SPFDnu {x} f))
spfdCoalgParaNTtoNuContraSl {x} {w} f k =
  spfdCoalgParaNTtoNuContra {x} f (Pi {a=w} . k)

public export
spfdNuToCoalgParaNTcontraSl : {x, w : Type} ->
  (f : SPFData x x) -> (k : SliceFunctor x w) ->
  (kcontramap : (y, z : SliceObj x) ->
    SliceMorphism {a=x} z y -> SliceMorphism {a=w} (k y) (k z)) ->
  Pi {a=w} (k (SPFDnu {x} f)) ->
  ((a : SliceObj x) -> SliceCoalgSPFD {x} f a -> Pi {a=w} (k a))
spfdNuToCoalgParaNTcontraSl {x} {w} f k kcm =
  spfdNuToCoalgParaNTcontra {x} f (Pi {a=w} . k)
    (piContramapComp {c=x} {d=w} {k} kcm)

-- The following isomorphism is an existential, covariant form.

public export
spfdCoalgToNuCovar :
  {x : Type} -> (f : SPFData x x) -> (k : SliceObj x -> Type) ->
  (kmap : (y, z : SliceObj x) -> SliceMorphism {a=x} y z -> k y -> k z) ->
  (a : SliceObj x ** (SliceCoalgSPFD {x} f a, k a)) -> k (SPFDnu {x} f)
spfdCoalgToNuCovar {x} f k kmap (a ** (coalg, eka)) =
  kmap a (SPFDnu {x} f) (spfdAna {x} {spfd=f} {a} coalg) eka

public export
spfdNuToCoalgCovar : {x : Type} ->
  (f : SPFData x x) -> (k : SliceObj x -> Type) ->
  k (SPFDnu {x} f) -> (a : SliceObj x ** (SliceCoalgSPFD {x} f a, k a))
spfdNuToCoalgCovar {x} f k knu =
  (SPFDnu {x} f ** (InSPFn {x} {spfd=f}, knu))

-- The above in a form with the copresheaf `k : SliceObj x -> Type`
-- generalized to a slice functor.

public export
spfdCoalgToNuCovarSl :
  {x, w : Type} -> (f : SPFData x x) -> (k : SliceFunctor x w) ->
  (kmap : (y, z : SliceObj x) ->
    SliceMorphism {a=x} y z -> SliceMorphism {a=w} (k y) (k z)) ->
  (a : SliceObj x ** (SliceCoalgSPFD {x} f a, Sigma {a=w} (k a))) ->
  Sigma {a=w} (k (SPFDnu {x} f))
spfdCoalgToNuCovarSl {x} {w} f k kmap =
  spfdCoalgToNuCovar {x} f (Sigma {a=w} . k) (sigmaMapComp {c=x} {d=w} {k} kmap)

public export
spfdNuToCoalgCovarSl :
  {x, w : Type} -> (f : SPFData x x) -> (k : SliceFunctor x w) ->
  Sigma {a=w} (k (SPFDnu {x} f)) ->
  (a : SliceObj x ** (SliceCoalgSPFD {x} f a, Sigma {a=w} (k a)))
spfdNuToCoalgCovarSl {x} {w} f k =
  spfdNuToCoalgCovar {x} f (Sigma {a=w} . k)

--------------------------------------
--------------------------------------
---- Products of initial algebras ----
--------------------------------------
--------------------------------------

public export
pfProdToSl : PolyFunc -> PolyFunc -> SPFData (Fin 3) (Fin 3)
pfProdToSl p q =
  SPFD
    (flip index [pfPos p, pfPos q, Unit])
    (\ec, ep, ed => case ec of
      FZ => (ed = FZ, pfDir {p} ep)
      FS FZ => (ed = FS FZ, pfDir {p=q} ep)
      FS (FS FZ) => case ep of
        () => case ed of
          FZ => Unit
          FS FZ => Unit
          FS (FS FZ) => Void)

public export
pfProdSlMu : PolyFunc -> PolyFunc -> FinSliceObj 3
pfProdSlMu p q = SPFDmu (pfProdToSl p q)

public export
PFProdMu : PolyFunc -> PolyFunc -> Type
PFProdMu p q = pfProdSlMu p q (FS $ FS FZ)

public export
PFprodSlAlg : PolyFunc -> PolyFunc -> FinSliceObj 3 -> Type
PFprodSlAlg p q = SliceAlgSPFD {x=(Fin 3)} (pfProdToSl p q)

public export
pfProdSlCata : {p, q : PolyFunc} -> {sl : FinSliceObj 3} ->
  PFprodSlAlg p q sl -> SliceMorphism (pfProdSlMu p q) sl
pfProdSlCata {p} {q} {sl} = spfdCata {spfd=(pfProdToSl p q)} {a=sl}

public export
pfProdMuFromSlObj : PolyFunc -> PolyFunc -> FinSliceObj 3
pfProdMuFromSlObj p q FZ = PolyFuncMu p
pfProdMuFromSlObj p q (FS FZ) = PolyFuncMu q
pfProdMuFromSlObj p q (FS $ FS FZ) = (PolyFuncMu p, PolyFuncMu q)

public export
pfProdMuFromSlAlg : (p, q : PolyFunc) -> PFprodSlAlg p q (pfProdMuFromSlObj p q)
pfProdMuFromSlAlg p q FZ (ep ** dm) = InPFM ep (\d => dm FZ (Refl, d))
pfProdMuFromSlAlg p q (FS FZ) (ep ** dm) = InPFM ep (\d => dm (FS FZ) (Refl, d))
pfProdMuFromSlAlg p q (FS $ FS FZ) (() ** dm) = (dm FZ (), dm (FS FZ) ())

public export
pfProdSlToProdMu : (p, q : PolyFunc) ->
  PFProdMu p q -> (PolyFuncMu p, PolyFuncMu q)
pfProdSlToProdMu p q =
  spfdCata {spfd=(pfProdToSl p q)} (pfProdMuFromSlAlg p q) (FS $ FS FZ)

public export
pfProdSlFromProdMuSlCurried0 : (p, q : PolyFunc) ->
  PolyFuncMu p -> pfProdSlMu p q FZ
pfProdSlFromProdMuSlCurried0 p q (InPFM pi pdm) =
  InSPFm
    FZ
    (pi **
     \idx, (eq, pd) =>
      case eq of Refl => pfProdSlFromProdMuSlCurried0 p q $ pdm pd)

public export
pfProdSlFromProdMuSlCurried1 : (p, q : PolyFunc) ->
  PolyFuncMu q -> pfProdSlMu p q (FS FZ)
pfProdSlFromProdMuSlCurried1 p q (InPFM qi qdm) =
  InSPFm
    (FS FZ)
    (qi **
     \idx, (eq, qd) =>
      case eq of Refl => pfProdSlFromProdMuSlCurried1 p q $ qdm qd)

public export
pfProdSlFromProdMuSlCurried2 : (p, q : PolyFunc) ->
  PolyFuncMu p -> PolyFuncMu q -> pfProdSlMu p q (FS $ FS FZ)
pfProdSlFromProdMuSlCurried2 p q elp elq =
  InSPFm
    (FS $ FS FZ)
    (() ** \idx, ep => case idx of
      FZ => case ep of () => pfProdSlFromProdMuSlCurried0 p q elp
      FS FZ => case ep of () => pfProdSlFromProdMuSlCurried1 p q elq
      FS (FS FZ) => void ep)

public export
pfProdSlFromProdMu : (p, q : PolyFunc) ->
  (PolyFuncMu p, PolyFuncMu q) -> PFProdMu p q
pfProdSlFromProdMu p q = uncurry $ pfProdSlFromProdMuSlCurried2 p q

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
-- positions, or simply a position-slice.  We write "CS(lice)" here to
-- indicate that this is a category-theory-style slice (as opposed
-- to a dependent-type-style slice).
public export
spfdPosCSproj : {x, y, z : Type} -> SPFData y z -> SPFData x z -> Type
spfdPosCSproj {x} {y} {z} q p =
  SPFnt {dom=x} {cod=z} p (spfdCompTerm {x} {y} {z} q)

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
