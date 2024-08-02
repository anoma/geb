module LanguageDef.PolyCat

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.NatPrefixCat
import public LanguageDef.MLDirichCat
import public LanguageDef.IntArena

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

-----------------------------
-----------------------------
---- Polynomial functors ----
-----------------------------
-----------------------------

-----------------------------------------------------
---- Polynomial functors as dependent sets/types ----
-----------------------------------------------------

-- A polynomial endofunctor may be viewed as a dependent type,
-- with a type family of directions dependent on a set of positions.
public export
PolyFuncDir : Type -> Type
PolyFuncDir pos = pos -> Type

public export
PolyFunc : Type
PolyFunc = DPair Type PolyFuncDir

public export
pfPos : PolyFunc -> Type
pfPos = fst

public export
pfDir : {p : PolyFunc} -> pfPos p -> Type
pfDir {p} i = snd p i

public export
pfPDir : PolyFunc -> Type
pfPDir p = DPair (pfPos p) (pfDir {p})

public export
InterpPolyFunc : PolyFunc -> Type -> Type
InterpPolyFunc p x = (i : pfPos p ** (pfDir {p} i -> x))

public export
InterpPFMap : (p : PolyFunc) -> {0 a, b : Type} ->
  (a -> b) -> InterpPolyFunc p a -> InterpPolyFunc p b
InterpPFMap (_ ** _) m (i ** d) = (i ** m . d)

public export
(p : PolyFunc) => Functor (InterpPolyFunc p) where
  map {p} = InterpPFMap p

-- A polynomial functor may also be viewed as a slice object
-- (in the slice category of its type of positions).
-- (Similarly, it may also be viewed as an object of the
-- arrow category.)
public export
PolyFuncToSlice : (p : PolyFunc) -> SliceObj (pfPos p)
PolyFuncToSlice (pos ** dir) = dir

public export
SliceToPolyFunc : {a : Type} -> SliceObj a -> PolyFunc
SliceToPolyFunc {a} sl = (a ** sl)

--------------------------------------------------------
---- Polynomial functors with finite direction-sets ----
--------------------------------------------------------

-- A version of PolyFunc where all direction-sets are finite.
public export
PolyFuncNDir : Type -> Type
PolyFuncNDir pos = pos -> Nat

public export
PolyFuncDirFromN : {0 pos : Type} -> PolyFuncNDir pos -> PolyFuncDir pos
PolyFuncDirFromN dir = Fin . dir

public export
PolyFuncN : Type
PolyFuncN = DPair Type PolyFuncNDir

public export
pfnPos : PolyFuncN -> Type
pfnPos = fst

public export
pfnDir : (p : PolyFuncN) -> pfnPos p -> Nat
pfnDir = snd

public export
pfnDirFromN : (p : PolyFuncN) -> pfnPos p -> Type
pfnDirFromN p = PolyFuncDirFromN $ pfnDir p

public export
pfnFunc : PolyFuncN -> PolyFunc
pfnFunc p = (pfnPos p ** pfnDirFromN p)

------------------------------------------------------------
---- Natural transformations on polynomial endofunctors ----
------------------------------------------------------------

public export
PolyNatTrans : PolyFunc -> PolyFunc -> Type
PolyNatTrans p q =
  (onPos : pfPos p -> pfPos q **
   SliceMorphism (pfDir {p=q} . onPos) (pfDir {p}))

public export
pntOnPos : {0 p, q : PolyFunc} -> PolyNatTrans p q ->
  pfPos p -> pfPos q
pntOnPos {p=(_ ** _)} {q=(_ ** _)} (onPos ** onDir) = onPos

public export
pntOnDir : {0 p, q : PolyFunc} -> (alpha : PolyNatTrans p q) ->
  (i : pfPos p) -> pfDir {p=q} (pntOnPos {p} {q} alpha i) -> pfDir {p} i
pntOnDir {p=(_ ** _)} {q=(_ ** _)} (onPos ** onDir) = onDir

-- A natural transformation may be viewed as a morphism in the
-- slice category of `Type` over `Type`.
public export
InterpPolyNT : {0 p, q : PolyFunc} -> PolyNatTrans p q ->
  SliceMorphism {a=Type} (InterpPolyFunc p) (InterpPolyFunc q)
InterpPolyNT {p=(_ ** _)} {q=(_ ** _)} (onPos ** onDir) a (pi ** pd) =
  (onPos pi ** (pd . onDir pi))

-- A slice morphism can be viewed as a special case of a natural transformation
-- between the polynomial endofunctors as which the codomain and domain slices
-- may be viewed.  (The special case is that the on-positions function is the
-- identity, so the natural transformation is vertical.)

public export
SliceMorphismToPolyNatTrans : {0 a : Type} -> {0 s, s' : SliceObj a} ->
  SliceMorphism s s' -> PolyNatTrans (SliceToPolyFunc s') (SliceToPolyFunc s)
SliceMorphismToPolyNatTrans {a} m = (id {a} ** m)

public export
PolyNatTransToSliceMorphism : {0 p, q : PolyFunc} ->
  {eqpos : pfPos p = pfPos q} ->
  (alpha : PolyNatTrans p q) ->
  ((i : pfPos p) -> pntOnPos {p} {q} alpha i = replace {p=(\t => t)} eqpos i) ->
  SliceMorphism
    {a=(pfPos p)}
    (replace {p=(\type => type -> Type)} (sym eqpos) (PolyFuncToSlice q))
    (PolyFuncToSlice p)
PolyNatTransToSliceMorphism {p=(_ ** _)} {q=(_ ** qdir)}
  (_ ** ondir) onPosId i sp = ondir i $ replace {p=qdir} (sym (onPosId i)) sp

----------------------------------------------------------------------------
---- Vertical-Cartesian factoring of polynomial natural transformations ----
----------------------------------------------------------------------------

public export
pfBaseChangePos : (p : PolyFunc) -> {a : Type} -> (a -> pfPos p) -> Type
pfBaseChangePos = arBaseChangePos

public export
pfBaseChangeDir : (p : PolyFunc) -> {a : Type} -> (f : a -> pfPos p) ->
  pfBaseChangePos p {a} f -> Type
pfBaseChangeDir = arBaseChangeDir

public export
pfBaseChangeArena : (p : PolyFunc) -> {a : Type} -> (a -> pfPos p) -> PolyFunc
pfBaseChangeArena = arBaseChangeArena

-- The intermediate polynomial functor in the vertical-Cartesian
-- factoring of a natural transformation.
public export
VertCartFactFunc : {p, q : PolyFunc} -> PolyNatTrans p q -> PolyFunc
VertCartFactFunc {p} {q} alpha =
  pfBaseChangeArena q {a=(pfPos p)} (pntOnPos alpha)

public export
VertCartFactPos : {p, q : PolyFunc} -> PolyNatTrans p q -> Type
VertCartFactPos {p} {q} alpha = pfPos (VertCartFactFunc {p} {q} alpha)

public export
VertCartFactDir : {p, q : PolyFunc} -> (alpha : PolyNatTrans p q) ->
  VertCartFactPos {p} {q} alpha -> Type
VertCartFactDir {p} {q} alpha = pfDir {p=(VertCartFactFunc {p} {q} alpha)}

public export
VertFactOnPos : {0 p, q : PolyFunc} -> (alpha : PolyNatTrans p q) ->
  pfPos p -> VertCartFactPos {p} {q} alpha
VertFactOnPos {p=(ppos ** pdir)} {q=(qpos ** qdir)} (onPos ** onDir) i = i

public export
VertFactOnDir :
  {0 p, q : PolyFunc} -> (alpha : PolyNatTrans p q) -> (i : pfPos p) ->
  VertCartFactDir {p} {q} alpha (VertFactOnPos {p} {q} alpha i) -> pfDir {p} i
VertFactOnDir {p=p@(ppos ** pdir)} {q=q@(qpos ** qdir)} (onPos ** onDir) i j =
  onDir i j

public export
VertFactNatTrans : {0 p, q : PolyFunc} -> (alpha : PolyNatTrans p q) ->
  PolyNatTrans p (VertCartFactFunc {p} {q} alpha)
VertFactNatTrans {p=p@(ppos ** pdir)} {q=q@(qpos ** qdir)} alpha =
  (VertFactOnPos {p} {q} alpha ** VertFactOnDir {p} {q} alpha)

public export
CartFactOnPos : {0 p, q : PolyFunc} -> (alpha : PolyNatTrans p q) ->
  VertCartFactPos {p} {q} alpha -> pfPos q
CartFactOnPos {p=(ppos ** pdir)} {q=(qpos ** qdir)} (onPos ** onDir) i =
  onPos i

public export
CartFactOnDir :
  {0 p, q : PolyFunc} -> (alpha : PolyNatTrans p q) ->
  (i : VertCartFactPos {p} {q} alpha) ->
  pfDir {p=q} (CartFactOnPos {p} {q} alpha i) ->
  VertCartFactDir {p} {q} alpha i
CartFactOnDir {p=p@(ppos ** pdir)} {q=q@(qpos ** qdir)} (onPos ** onDir) i j =
  j

public export
CartFactNatTrans : {0 p, q : PolyFunc} -> (alpha : PolyNatTrans p q) ->
  PolyNatTrans (VertCartFactFunc {p} {q} alpha) q
CartFactNatTrans {p=p@(ppos ** pdir)} {q=q@(qpos ** qdir)} alpha =
  (CartFactOnPos {p} {q} alpha ** CartFactOnDir {p} {q} alpha)

-------------------------------------------------
-------------------------------------------------
---- Polynomial-functor universal properties ----
-------------------------------------------------
-------------------------------------------------

public export
PFInitialPos : Type
PFInitialPos = Void

public export
PFInitialDir : PFInitialPos -> Type
PFInitialDir = voidF Type

public export
PFInitialArena : PolyFunc
PFInitialArena = (PFInitialPos ** PFInitialDir)

public export
PFTerminalPos : Type
PFTerminalPos = Unit

public export
PFTerminalDir : PFTerminalPos -> Type
PFTerminalDir = const Void

public export
PFTerminalArena : PolyFunc
PFTerminalArena = (PFTerminalPos ** PFTerminalDir)

public export
PFIdentityPos : Type
PFIdentityPos = Unit

public export
PFIdentityDir : PFIdentityPos -> Type
PFIdentityDir = const Unit

public export
PFIdentityArena : PolyFunc
PFIdentityArena = (PFIdentityPos ** PFIdentityDir)

public export
PolyElimId : (x : Type) -> InterpPolyFunc PFIdentityArena x -> x
PolyElimId x (i ** d) = d ()

public export
PFHomPos : Type -> Type
PFHomPos _ = Unit

public export
PFHomDir : (a : Type) -> PFHomPos a -> Type
PFHomDir a _ = a

public export
PFHomArena : Type -> PolyFunc
PFHomArena a = (PFHomPos a ** PFHomDir a)

public export
PFConstPos : Type -> Type
PFConstPos a = a

public export
PFConstDir : {0 a : Type} -> PFConstPos a -> Type
PFConstDir i = Void

public export
PFConstArena : Type -> PolyFunc
PFConstArena a = (PFConstPos a ** PFConstDir {a})

public export
pfCoproductPos : PolyFunc -> PolyFunc -> Type
pfCoproductPos (ppos ** pdir) (qpos ** qdir) = Either ppos qpos

public export
pfCoproductDir : (p, q : PolyFunc) -> pfCoproductPos p q -> Type
pfCoproductDir (ppos ** pdir) (qpos ** qdir) (Left pi) = pdir pi
pfCoproductDir (ppos ** pdir) (qpos ** qdir) (Right qi) = qdir qi

public export
pfCoproductArena : PolyFunc -> PolyFunc -> PolyFunc
pfCoproductArena p q = (pfCoproductPos p q ** pfCoproductDir p q)

public export
pfProductPos : PolyFunc -> PolyFunc -> Type
pfProductPos (ppos ** pdir) (qpos ** qdir) = Pair ppos qpos

public export
pfProductDir : (p, q : PolyFunc) -> pfProductPos p q -> Type
pfProductDir (ppos ** pdir) (qpos ** qdir) (pi, qi) = Either (pdir pi) (qdir qi)

public export
pfProductArena : PolyFunc -> PolyFunc -> PolyFunc
pfProductArena p q = (pfProductPos p q ** pfProductDir p q)

public export
pfDoubleArena : PolyFunc -> PolyFunc
pfDoubleArena p = pfCoproductArena p p

public export
pfDoublePos : PolyFunc -> Type
pfDoublePos = pfPos . pfDoubleArena

public export
pfDoubleDir : (p : PolyFunc) -> pfDoublePos p -> Type
pfDoubleDir p = pfDir {p=(pfDoubleArena p)}

public export
pfSquareArena : PolyFunc -> PolyFunc
pfSquareArena p = pfProductArena p p

public export
pfSquarePos : PolyFunc -> Type
pfSquarePos = pfPos . pfSquareArena

public export
pfSquareDir : (p : PolyFunc) -> pfSquarePos p -> Type
pfSquareDir p = pfDir {p=(pfSquareArena p)}

public export
pfIdSquaredArena : PolyFunc
pfIdSquaredArena = pfSquareArena PFIdentityArena

public export
PFIdSquaredPos : Type
PFIdSquaredPos = pfPos pfIdSquaredArena

public export
pfIdSquaredDir : PFIdSquaredPos -> Type
pfIdSquaredDir = pfDir {p=pfIdSquaredArena}

public export
pfEitherArena : Type -> PolyFunc
pfEitherArena a = pfCoproductArena PFIdentityArena (PFConstArena a)

public export
pfEitherPos : Type -> Type
pfEitherPos = pfPos . pfEitherArena

public export
pfEitherDir : (a : Type) -> pfEitherPos a -> Type
pfEitherDir a = pfDir {p=(pfEitherArena a)}

public export
pfPairArena : Type -> PolyFunc
pfPairArena a = pfProductArena PFIdentityArena (PFConstArena a)

public export
pfPairPos : Type -> Type
pfPairPos = pfPos . pfPairArena

public export
pfPairDir : (a : Type) -> pfPairPos a -> Type
pfPairDir a = pfDir {p=(pfPairArena a)}

public export
pfMaybeArena : PolyFunc
pfMaybeArena = pfEitherArena Unit

public export
pfMaybePos : Type
pfMaybePos = pfPos pfMaybeArena

public export
pfMaybeDir : PolyCat.pfMaybePos -> Type
pfMaybeDir = pfDir {p=pfMaybeArena}

public export
pfParProductPos : PolyFunc -> PolyFunc -> Type
pfParProductPos = dfParProductPos

public export
pfParProductDir : (p, q : PolyFunc) -> pfParProductPos p q -> Type
pfParProductDir = dfParProductDir

public export
pfParProductArena : PolyFunc -> PolyFunc -> PolyFunc
pfParProductArena = dfParProductArena

public export
pfCompositionPos : PolyFunc -> PolyFunc -> Type
pfCompositionPos q p = (i : pfPos q ** (pfDir {p=q} i -> pfPos p))

public export
pfCompositionDir : (p, q : PolyFunc) -> pfCompositionPos p q -> Type
pfCompositionDir q p qppos =
  (qdir : pfDir {p=q} (fst qppos) ** pfDir {p} $ snd qppos qdir)

public export
pfCompositionArena : PolyFunc -> PolyFunc -> PolyFunc
pfCompositionArena p q = (pfCompositionPos p q ** pfCompositionDir p q)

public export
pfComposeInterp : {q, p : PolyFunc} -> {x : Type} ->
  InterpPolyFunc q (InterpPolyFunc p x) ->
  InterpPolyFunc (pfCompositionArena q p) x
pfComposeInterp {q=(qpos ** qdir)} {p=(ppos ** pdir)} {x} (i ** d) =
  ((i ** fst . d) ** \(i' ** d') => snd (d i') d')

public export
pfComposeInterpInv : {q, p : PolyFunc} -> {x : Type} ->
  InterpPolyFunc (pfCompositionArena q p) x ->
  InterpPolyFunc q (InterpPolyFunc p x)
pfComposeInterpInv {q=(qpos ** qdir)} {p=(ppos ** pdir)} {x} ((qi ** qd) ** d) =
  (qi ** \qdi => (qd qdi ** \pdi => d (qdi ** pdi)))

-- Composing a polynomial functor after a Dirichlet functor yields
-- a Dirichlet functor.

public export
pdfCompositionPos : PolyFunc -> MLDirichCatObj -> Type
pdfCompositionPos q p = (qi : pfPos q ** pfDir {p=q} qi -> pfPos p)

public export
pdfCompositionDir : (q : PolyFunc) -> (p : MLDirichCatObj) ->
  pdfCompositionPos q p -> Type
pdfCompositionDir q p i = (qd : pfDir {p=q} $ fst i) -> pfDir {p} $ snd i qd

public export
pdfCompositionArena : PolyFunc -> MLDirichCatObj -> PolyFunc
pdfCompositionArena q p = (pdfCompositionPos q p ** pdfCompositionDir q p)

public export
pdfComposeInterp : {q : PolyFunc} -> {p : MLDirichCatObj} -> {x : Type} ->
  InterpPolyFunc q (InterpDirichFunc p x) ->
  InterpDirichFunc (pdfCompositionArena q p) x
pdfComposeInterp {q} {p} {x} qidm =
  ((fst qidm ** fst . snd qidm) ** \ex, qd => snd (snd qidm qd) ex)

public export
pdfComposeInterpInv : {q : PolyFunc} -> {p : MLDirichCatObj} -> {x : Type} ->
  InterpDirichFunc (pdfCompositionArena q p) x ->
  InterpPolyFunc q (InterpDirichFunc p x)
pdfComposeInterpInv {q} {p} {x} el =
  (fst $ fst el ** \qd => (snd (fst el) qd ** \ex => snd el ex qd))

public export
pfDuplicateArena : PolyFunc -> PolyFunc
pfDuplicateArena p = pfCompositionArena p p

public export
pfDuplicatePos : PolyFunc -> Type
pfDuplicatePos = pfPos . pfDuplicateArena

public export
pfDuplicateDir : (p : PolyFunc) -> pfPos (pfDuplicateArena p) -> Type
pfDuplicateDir p = pfDir {p=(pfDuplicateArena p)}

public export
pfTriplicateArenaLeft : PolyFunc -> PolyFunc
pfTriplicateArenaLeft p = pfCompositionArena (pfDuplicateArena p) p

public export
pfTriplicatePosLeft : PolyFunc -> Type
pfTriplicatePosLeft = pfPos . pfTriplicateArenaLeft

public export
pfTriplicateDirLeft :
  (p : PolyFunc) -> pfPos (pfTriplicateArenaLeft p) -> Type
pfTriplicateDirLeft p = pfDir {p=(pfTriplicateArenaLeft p)}

public export
pfTriplicateArenaRight : PolyFunc -> PolyFunc
pfTriplicateArenaRight p = pfCompositionArena p (pfDuplicateArena p)

public export
pfTriplicatePosRight : PolyFunc -> Type
pfTriplicatePosRight = pfPos . pfTriplicateArenaRight

public export
pfTriplicateDirRight :
  (p : PolyFunc) -> pfPos (pfTriplicateArenaRight p) -> Type
pfTriplicateDirRight p = pfDir {p=(pfTriplicateArenaRight p)}

public export
pfCompositionPowerArenaS : PolyFunc -> Nat -> PolyFunc
pfCompositionPowerArenaS p Z = p
pfCompositionPowerArenaS p (S n) =
  pfCompositionArena p (pfCompositionPowerArenaS p n)

public export
pfCompositionPowerSPos : PolyFunc -> Nat -> Type
pfCompositionPowerSPos p n = pfPos (pfCompositionPowerArenaS p n)

public export
pfCompositionPowerSDir : (p : PolyFunc) -> (n : Nat) ->
  pfCompositionPowerSPos p n -> Type
pfCompositionPowerSDir p n = pfDir {p=(pfCompositionPowerArenaS p n)}

public export
pfCompositionPowerArena : PolyFunc -> Nat -> PolyFunc
pfCompositionPowerArena p Z = PFIdentityArena
pfCompositionPowerArena p (S n) = pfCompositionPowerArenaS p n

public export
pfCompositionPowerPos : PolyFunc -> Nat -> Type
pfCompositionPowerPos p n = pfPos (pfCompositionPowerArena p n)

public export
pfCompositionPowerDir : (p : PolyFunc) -> (n : Nat) ->
  pfCompositionPowerPos p n -> Type
pfCompositionPowerDir p n = pfDir {p=(pfCompositionPowerArena p n)}

public export
pfSetCoproductPos : {a : Type} -> (a -> PolyFunc) -> Type
pfSetCoproductPos = dfSetCoproductPos

public export
pfSetCoproductDir : {a : Type} ->
  (ps : a -> PolyFunc) -> pfSetCoproductPos ps -> Type
pfSetCoproductDir = dfSetCoproductDir

public export
pfSetCoproductArena : {a : Type} -> (a -> PolyFunc) -> PolyFunc
pfSetCoproductArena = dfSetCoproductArena

public export
pfSetProductPos : {a : Type} -> (a -> PolyFunc) -> Type
pfSetProductPos = dfSetParProductPos

public export
pfSetProductDir : {a : Type} ->
  (ps : a -> PolyFunc) -> pfSetProductPos ps -> Type
pfSetProductDir {a} ps fpos = (x : a ** snd (ps x) $ fpos x)

public export
pfSetProductArena : {a : Type} -> (a -> PolyFunc) -> PolyFunc
pfSetProductArena {a} ps = (pfSetProductPos ps ** pfSetProductDir ps)

public export
pfSetParProductPos : {a : Type} -> (a -> PolyFunc) -> Type
pfSetParProductPos = dfSetParProductPos

public export
pfSetParProductDir : {a : Type} ->
  (ps : a -> PolyFunc) -> pfSetParProductPos ps -> Type
pfSetParProductDir = dfSetParProductDir

public export
pfSetParProductArena : {a : Type} -> (a -> PolyFunc) -> PolyFunc
pfSetParProductArena = dfSetParProductArena

-- Formula 5.27 from "Polynomial Functors: A General Theory of Interaction".
public export
pfHomObj : PolyFunc -> PolyFunc -> PolyFunc
pfHomObj q r =
  pfSetProductArena {a=(pfPos q)} $
    pfCompositionArena r .
    pfCoproductArena PFIdentityArena .
    PFConstArena . pfDir {p=q}

public export
pfHomObjPos : PolyFunc -> PolyFunc -> Type
pfHomObjPos = pfPos .* pfHomObj

public export
pfHomObjDir : (p, q : PolyFunc) -> pfHomObjPos p q -> Type
pfHomObjDir p q = pfDir {p=(pfHomObj p q)}

public export
pfExpObj : PolyFunc -> PolyFunc -> PolyFunc
pfExpObj = flip pfHomObj

public export
pfExpObjPos : PolyFunc -> PolyFunc -> Type
pfExpObjPos = pfPos .* pfExpObj

public export
pfExpObjDir : (p, q : PolyFunc) -> pfExpObjPos p q -> Type
pfExpObjDir p q = pfDir {p=(pfExpObj p q)}

-- Formula 4.75 from "Polynomial Functors: A General Theory of Interaction".
-- See also the section on formula 3.82 below.
public export
pfParProdClosure : PolyFunc -> PolyFunc -> PolyFunc
pfParProdClosure q r =
  pfSetProductArena {a=(pfPos q)} $
    pfCompositionArena r .
    pfProductArena PFIdentityArena .
    PFConstArena . pfDir {p=q}

public export
pfParProdClosurePos : PolyFunc -> PolyFunc -> Type
pfParProdClosurePos = pfPos .* pfParProdClosure

public export
pfParProdClosureDir : (p, q : PolyFunc) -> pfParProdClosurePos p q -> Type
pfParProdClosureDir p q = pfDir {p=(pfParProdClosure p q)}

-- Formula 4.79 from "Polynomial Functors: A General Theory of Interaction":
-- this is isomorphic to `pfParProdClosure` (that isomorphism shows that
-- `pfParProdClosure` can be used as a way of computing the natural
-- transformations between polynomial functors as the positions of a polynomial
-- functor).  See the section on formula 4.75 above.
public export
pfParProdClosurePosNT : PolyFunc -> PolyFunc -> Type
pfParProdClosurePosNT = PolyNatTrans

public export
pfParProdClosureDirPolyFunc :
  (q, r : PolyFunc) -> pfParProdClosurePosNT q r -> PolyFunc
pfParProdClosureDirPolyFunc q r alpha = VertCartFactFunc {p=q} {q=r} alpha

public export
pfParProdClosureDirNT :
  (q, r : PolyFunc) -> pfParProdClosurePosNT q r -> Type
pfParProdClosureDirNT q r alpha = pfPDir (pfParProdClosureDirPolyFunc q r alpha)

public export
pfParProdClosureNT : PolyFunc -> PolyFunc -> PolyFunc
pfParProdClosureNT q r =
  (pfParProdClosurePosNT q r ** pfParProdClosureDirNT q r)

public export
pfLeftCoclosurePos : (q, p : PolyFunc) -> Type
pfLeftCoclosurePos q p = pfPos p

public export
pfLeftCoclosureDir : (q, p : PolyFunc) -> pfLeftCoclosurePos q p -> Type
pfLeftCoclosureDir q p = InterpPolyFunc q . pfDir {p}

public export
pfLeftCoclosure : (q, p : PolyFunc) -> PolyFunc
pfLeftCoclosure q p = (pfLeftCoclosurePos q p ** pfLeftCoclosureDir q p)

public export
PolyLKanExt : (j, g : PolyFunc) -> PolyFunc
PolyLKanExt = pfLeftCoclosure

public export
PolyDensityComonad : PolyFunc -> PolyFunc
PolyDensityComonad f = PolyLKanExt f f

public export
pfHomComposePos : Type -> Type -> Type
pfHomComposePos a b = pfCompositionPos (PFHomArena a) (PFHomArena b)

public export
pfHomComposeDir : (a, b : Type) -> pfHomComposePos a b -> Type
pfHomComposeDir a b = pfCompositionDir (PFHomArena a) (PFHomArena b)

public export
pfHomComposeArena : Type -> Type -> PolyFunc
pfHomComposeArena a b = pfCompositionArena (PFHomArena a) (PFHomArena b)

public export
pfEitherComposePos : Type -> Type -> Type
pfEitherComposePos a b = pfCompositionPos (pfEitherArena a) (pfEitherArena b)

public export
pfEitherComposeDir : (a, b : Type) -> pfEitherComposePos a b -> Type
pfEitherComposeDir a b = pfCompositionDir (pfEitherArena a) (pfEitherArena b)

public export
pfEitherComposeArena : Type -> Type -> PolyFunc
pfEitherComposeArena a b =
  pfCompositionArena (pfEitherArena a) (pfEitherArena b)

public export
pfDayConvPos : PolyFunc -> PolyFunc -> Type
pfDayConvPos p q = Pair (pfPos p) (pfPos q)

public export
pfDayConvDir : (m : Type -> Type -> Type) ->
  (p, q : PolyFunc) -> pfDayConvPos p q -> Type
pfDayConvDir m p q (pi, qi) = m (pfDir {p} pi) (pfDir {p=q} qi)

public export
pfDayConvArena : (m : Type -> Type -> Type) -> PolyFunc -> PolyFunc -> PolyFunc
pfDayConvArena m p q = (pfDayConvPos p q ** pfDayConvDir m p q)

-- Formula 6.75 from the "General Theory of Interaction" book.
public export
pfPosChangePos : (p, q : PolyFunc) -> (pfPos p -> pfPos q) -> Type
pfPosChangePos p q f = (i : pfPos p ** pfDir {p=q} $ f i)

public export
pfPosChangeDir : (p, q : PolyFunc) -> (f : pfPos p -> pfPos q) ->
  (i : pfPosChangePos p q f) -> Type
pfPosChangeDir p q f (pi ** qdfpi) = pfDir {p} pi

public export
pfPosChangeArena : (p, q : PolyFunc) -> (pfPos p -> pfPos q) -> PolyFunc
pfPosChangeArena p q f = (pfPosChangePos p q f ** pfPosChangeDir p q f)

-- Formula 6.78 from the "General Theory of Interaction" book (I think).
-- If I'm reading exercise 6.77 correctly, this states that for any
-- polynomial functor `q`, the functor defined by postcomposition with `q`
-- has a left multiadjoint.  And if I'm further understanding ncatlab's
-- https://ncatlab.org/nlab/show/parametric+right+adjoint correctly, that
-- in turn also means that that postcomposition functor is itself a
-- parametric right adjoint (i.e., is polynomial).
public export
pfHomToCompArena : PolyFunc -> PolyFunc -> PolyFunc -> PolyFunc
pfHomToCompArena p q r =
  pfSetCoproductArena {a=(pfPos p -> pfPos q)} $
    \f => pfHomObj (pfPosChangeArena p q f) r

public export
pfDerivativePos : PolyFunc -> Type
pfDerivativePos p = DPair (pfPos p) (pfDir {p})

public export
pfDerivativeDir : (p : PolyFunc) -> pfDerivativePos p -> Type
pfDerivativeDir p (i ** di) = DPair (pfDir {p} i) (Not . Equal di)

public export
pfDerivativeArena : PolyFunc -> Type
pfDerivativeArena p = DPair (pfDerivativePos p) (pfDerivativeDir p)

public export
pfMonomialPos : Type -> Type -> Type
pfMonomialPos a b = a

public export
pfMonomialDir : (a, b : Type) -> pfMonomialPos a b -> Type
pfMonomialDir a b i = b

public export
pfMonomialArena : Type -> Type -> PolyFunc
pfMonomialArena a b = (pfMonomialPos a b ** pfMonomialDir a b)

-- A functor whose category of elements is the two-category of slice
-- categories of `Type` whose morphisms are the `Sigma` functors.
public export
PolySliceObj : PolyFunc
PolySliceObj = (Type ** id)

public export
PolySliceObjFromInterp :
  (a : Type) -> InterpPolyFunc PolySliceObj a -> CSliceObj a
PolySliceObjFromInterp a = id

public export
PolySliceObjToInterp :
  (a : Type) -> CSliceObj a -> InterpPolyFunc PolySliceObj a
PolySliceObjToInterp a = id

public export
PolySliceObjFromInterpMap :
  {a, b : Type} -> (m : a -> b) ->
  CSliceNatTrans {c=a} {d=b}
    (InterpPFMap PolySliceObj {a} {b} m)
    (CSSigma {c=a} {d=b} m)
PolySliceObjFromInterpMap {a} {b} m (x ** xp) = Element0 id (\_ => Refl)

public export
PolySliceObjToInterpMap :
  {a, b : Type} -> (m : a -> b) ->
  CSliceNatTrans {c=a} {d=b}
    (CSSigma {c=a} {d=b} m)
    (InterpPFMap PolySliceObj {a} {b} m)
PolySliceObjToInterpMap {a} {b} m (x ** xp) = Element0 id (\_ => Refl)

-- Applying a polynomial functor to a type `a` yields the set of natural
-- transformations from the covariant representable represented by `a` to
-- that functor.  Indeed, this is true of any functor -- that's just one
-- form of the Yoneda lemma.
--
-- Thus, the category of elements of a (polynomial, or otherwise) functor is
-- the category of natural transformations from covariant representables
-- to that polynomial functor.
public export
PolyRepNT : (p : PolyFunc) ->
  (a : Type) -> InterpPolyFunc p a -> PolyNatTrans (PFHomArena a) p
PolyRepNT (pos ** dir) a (i ** d) = (\() => i ** \() => d)

-- Equivalent to a natural transformation to the identity functor.
public export
PFSection : PolyFunc -> Type
PFSection p = Pi {a=(pfPos p)} $ pfDir {p}

-- A natural transformation out of a sum is a product of natural
-- transformations.  Therefore, a natural transformation out of a
-- polynomial functor is a product of natural transformations out of
-- covariant representables.
public export
PolyRepNTProd : (p, q : PolyFunc) ->
  PFSection (PolyLKanExt q p) -> PolyNatTrans p q
PolyRepNTProd (ppos ** pdir) q alpha =
  (\i => fst (alpha i) ** \i, d => snd (alpha i) d)

---------------------------------------
---------------------------------------
---- Universal morphisms in `Poly` ----
---------------------------------------
---------------------------------------

public export
polyFromInitOnPos : (p : PolyFunc) -> pfPos PFInitialArena -> pfPos p
polyFromInitOnPos p v = void v

public export
polyFromInitOnDir : (p : PolyFunc) ->
  (i : pfPos PFInitialArena) ->
  pfDir {p} (polyFromInitOnPos p i) -> pfDir {p=PFInitialArena} i
polyFromInitOnDir p v = void v

public export
polyFromInit : (p : PolyFunc) -> PolyNatTrans PFInitialArena p
polyFromInit p = (polyFromInitOnPos p ** polyFromInitOnDir p)

public export
polyToTermOnPos : (p : PolyFunc) -> pfPos p -> pfPos PFTerminalArena
polyToTermOnPos p _ = ()

public export
polyToTermOnDir : (p : PolyFunc) ->
  (i : pfPos p) ->
  pfDir {p=PFTerminalArena} (polyToTermOnPos p i) -> pfDir {p} i
polyToTermOnDir p _ v = void v

public export
polyToTerm : (p : PolyFunc) -> PolyNatTrans p PFTerminalArena
polyToTerm p = (polyToTermOnPos p ** polyToTermOnDir p)

public export
polyInjLOnPos : (p, q : PolyFunc) -> pfPos p -> pfPos (pfCoproductArena p q)
polyInjLOnPos (ppos ** pdir) (qpos ** qdir) i = Left i

public export
polyInjLOnDir : (p, q : PolyFunc) ->
  (i : pfPos p) ->
  pfDir {p=(pfCoproductArena p q)} (polyInjLOnPos p q i) -> pfDir {p} i
polyInjLOnDir (ppos ** pdir) (qpos ** qdir) i d = d

public export
polyInjL : (p, q : PolyFunc) -> PolyNatTrans p (pfCoproductArena p q)
polyInjL p q = (polyInjLOnPos p q ** polyInjLOnDir p q)

public export
polyInjROnPos : (p, q : PolyFunc) -> pfPos q -> pfPos (pfCoproductArena p q)
polyInjROnPos (ppos ** pdir) (qpos ** qdir) i = Right i

public export
polyInjROnDir : (p, q : PolyFunc) ->
  (i : pfPos q) ->
  pfDir {p=(pfCoproductArena p q)} (polyInjROnPos p q i) -> pfDir {p=q} i
polyInjROnDir (ppos ** pdir) (qpos ** qdir) i d = d

public export
polyInjR : (p, q : PolyFunc) -> PolyNatTrans q (pfCoproductArena p q)
polyInjR p q = (polyInjROnPos p q ** polyInjROnDir p q)

public export
polyCaseOnPos : (p, q, r : PolyFunc) ->
  PolyNatTrans p r -> PolyNatTrans q r ->
  pfPos (pfCoproductArena p q) -> pfPos r
polyCaseOnPos (ppos ** pdir) (qpos ** qdir) (rpos ** rdir)
  (pronpos ** prondir) (qronpos ** qrondir) pqi =
    case pqi of
      Left pqi => pronpos pqi
      Right pqi => qronpos pqi

public export
polyCaseOnDir : (p, q, r : PolyFunc) ->
  (f : PolyNatTrans p r) -> (g : PolyNatTrans q r) ->
  (i : pfPos (pfCoproductArena p q)) ->
  pfDir {p=r} (polyCaseOnPos p q r f g i) -> pfDir {p=(pfCoproductArena p q)} i
polyCaseOnDir (ppos ** pdir) (qpos ** qdir) (rpos ** rdir)
  (pronpos ** prondir) (qronpos ** qrondir) (Left pi) rd =
    prondir pi rd
polyCaseOnDir (ppos ** pdir) (qpos ** qdir) (rpos ** rdir)
  (pronpos ** prondir) (qronpos ** qrondir) (Right qi) rd =
    qrondir qi rd

public export
polyCase : {p, q, r : PolyFunc} ->
  PolyNatTrans p r -> PolyNatTrans q r -> PolyNatTrans (pfCoproductArena p q) r
polyCase {p} {q} {r} f g = (polyCaseOnPos p q r f g ** polyCaseOnDir p q r f g)

public export
polyProj1OnPos : (p, q : PolyFunc) -> pfPos (pfProductArena p q) -> pfPos p
polyProj1OnPos (ppos ** pdir) (qpos ** qdir) (pi, qi) = pi

public export
polyProj1OnDir : (p, q : PolyFunc) ->
  (i : pfPos (pfProductArena p q)) ->
  pfDir {p} (polyProj1OnPos p q i) ->
  pfDir {p=(pfProductArena p q)} i
polyProj1OnDir (ppos ** pdir) (qpos ** qdir) (pi, qi) d = Left d

public export
polyProj1 : (p, q : PolyFunc) -> PolyNatTrans (pfProductArena p q) p
polyProj1 p q = (polyProj1OnPos p q ** polyProj1OnDir p q)

public export
polyProj2OnPos : (p, q : PolyFunc) -> pfPos (pfProductArena p q) -> pfPos q
polyProj2OnPos (ppos ** pdir) (qpos ** qdir) (pi, qi) = qi

public export
polyProj2OnDir : (p, q : PolyFunc) ->
  (i : pfPos (pfProductArena p q)) ->
  pfDir {p=q} (polyProj2OnPos p q i) ->
  pfDir {p=(pfProductArena p q)} i
polyProj2OnDir (ppos ** pdir) (qpos ** qdir) (pi, qi) d = Right d

public export
polyProj2 : (p, q : PolyFunc) -> PolyNatTrans (pfProductArena p q) q
polyProj2 p q = (polyProj2OnPos p q ** polyProj2OnDir p q)

public export
polyPairOnPos : (p, q, r : PolyFunc) ->
  PolyNatTrans p q -> PolyNatTrans p r ->
  pfPos p ->
  pfPos (pfProductArena q r)
polyPairOnPos (ppos ** pdir) (qpos ** qdir) (rpos ** rdir)
  (pqonpos ** pqondir) (pronpos ** prondir) pi =
    (pqonpos pi, pronpos pi)

public export
polyPairOnDir : (p, q, r : PolyFunc) ->
  (f : PolyNatTrans p q) -> (g : PolyNatTrans p r) ->
  (pi : pfPos p) ->
  pfDir {p=(pfProductArena q r)} (polyPairOnPos p q r f g pi) ->
  pfDir {p} pi
polyPairOnDir (ppos ** pdir) (qpos ** qdir) (rpos ** rdir)
  (pqonpos ** pqondir) (pronpos ** prondir) pi qrd =
    case qrd of
      Left qd => pqondir pi qd
      Right rd => prondir pi rd

public export
polyPair : {p, q, r : PolyFunc} ->
  PolyNatTrans p q -> PolyNatTrans p r -> PolyNatTrans p (pfProductArena q r)
polyPair {p} {q} {r} f g = (polyPairOnPos p q r f g ** polyPairOnDir p q r f g)

public export
pfEvalOnPos :
  (p, q : PolyFunc) ->
  pfPos (pfProductArena (pfHomObj p q) p) -> pfPos q
pfEvalOnPos (ppos ** pdir) (qpos ** qdir) (qpi, pi) = fst $ qpi pi

public export
pfEvalOnDir : (p, q : PolyFunc) ->
  (i : pfPos (pfProductArena (pfHomObj p q) p)) ->
  pfDir {p=q} (pfEvalOnPos p q i) ->
  pfDir {p=(pfProductArena (pfHomObj p q) p)} i
pfEvalOnDir (ppos ** pdir) (qpos ** qdir) (qpd, pi) qd with
    (pfEvalOnPos (ppos ** pdir) (qpos ** qdir) (qpd, pi)) proof eqq
  pfEvalOnDir (ppos ** pdir) (qpos ** qdir) (qpd, pi) qd | qi with
      (snd (qpd pi) (replace {p=qdir} (sym eqq) qd)) proof eqp
    pfEvalOnDir (ppos ** pdir) (qpos ** qdir) (qpd, pi) qd | qi | Left () =
      Left (pi ** replace {p=qdir} (sym eqq) qd ** rewrite eqp in ())
    pfEvalOnDir (ppos ** pdir) (qpos ** qdir) (qpd, pi) qd | qi | Right pd =
      Right pd

public export
pfEval : (p, q : PolyFunc) -> PolyNatTrans (pfProductArena (pfHomObj p q) p) q
pfEval p q = (pfEvalOnPos p q ** pfEvalOnDir p q)

public export
pfCurryOnPos1 :
  (ppos, qpos, rpos : Type) ->
  (pdir : ppos -> Type) ->
  (qdir : qpos -> Type) ->
  (rdir : rpos -> Type) ->
  (alpha : PolyNatTrans
    (pfProductArena (ppos ** pdir) (qpos ** qdir)) (rpos ** rdir)) ->
  ppos -> qpos -> rpos
pfCurryOnPos1 ppos qpos rpos pdir qdir rdir (onpos ** ondir) pi qi =
  onpos (pi, qi)

public export
pfCurryOnPos2 :
  (ppos, qpos, rpos : Type) ->
  (pdir : ppos -> Type) ->
  (qdir : qpos -> Type) ->
  (rdir : rpos -> Type) ->
  (alpha : PolyNatTrans
    (pfProductArena (ppos ** pdir) (qpos ** qdir)) (rpos ** rdir)) ->
  (pi : ppos) -> (qi : qpos) ->
  rdir (pfCurryOnPos1 ppos qpos rpos pdir qdir rdir alpha pi qi) ->
  Either () (qdir qi)
pfCurryOnPos2 ppos qpos rpos pdir qdir rdir (onpos ** ondir) pi qi rd
    with (ondir (pi, qi) rd)
  pfCurryOnPos2 ppos qpos rpos pdir qdir rdir (onpos ** ondir) pi qi rd |
    Left pd = Left ()
  pfCurryOnPos2 ppos qpos rpos pdir qdir rdir (onpos ** ondir) pi qi rd |
    Right qd = Right qd

public export
pfCurryOnPos :
  (ppos, qpos, rpos : Type) ->
  (pdir : ppos -> Type) ->
  (qdir : qpos -> Type) ->
  (rdir : rpos -> Type) ->
  (alpha : PolyNatTrans
    (pfProductArena (ppos ** pdir) (qpos ** qdir)) (rpos ** rdir)) ->
  ppos -> pfPos (pfHomObj (qpos ** qdir) (rpos ** rdir))
pfCurryOnPos ppos qpos rpos pdir qdir rdir alpha pi qi =
  (pfCurryOnPos1 ppos qpos rpos pdir qdir rdir alpha pi qi **
   pfCurryOnPos2 ppos qpos rpos pdir qdir rdir alpha pi qi)

public export
pfCurryOnDir :
  (ppos, qpos, rpos : Type) ->
  (pdir : ppos -> Type) ->
  (qdir : qpos -> Type) ->
  (rdir : rpos -> Type) ->
  (alpha : PolyNatTrans
    (pfProductArena (ppos ** pdir) (qpos ** qdir)) (rpos ** rdir)) ->
  (pi : ppos) ->
  pfDir {p=(pfHomObj (qpos ** qdir) (rpos ** rdir))}
    (pfCurryOnPos ppos qpos rpos pdir qdir rdir alpha pi) ->
  pfDir {p=(ppos ** pdir)} pi
pfCurryOnDir ppos qpos rpos pdir qdir rdir (onpos ** ondir)
  pi (qi ** rd ** cd) with (ondir (pi, qi) rd) proof eq
    pfCurryOnDir ppos qpos rpos pdir qdir rdir (onpos ** ondir)
      pi (qi ** rd ** ()) | Left pd =
        pd
    pfCurryOnDir ppos qpos rpos pdir qdir rdir (onpos ** ondir)
      pi (qi ** rd ** v) | Right qd =
        void v

public export
pfCurry : {p, q, r : PolyFunc} ->
  PolyNatTrans (pfProductArena p q) r ->
  PolyNatTrans p (pfHomObj q r)
pfCurry {p=(ppos ** pdir)} {q=(qpos ** qdir)} {r=(rpos ** rdir)} alpha =
  (pfCurryOnPos ppos qpos rpos pdir qdir rdir alpha **
   pfCurryOnDir ppos qpos rpos pdir qdir rdir alpha)

public export
pfParEvalOnPos :
  (p, q : PolyFunc) ->
  pfPos (pfParProductArena (pfParProdClosure p q) p) -> pfPos q
pfParEvalOnPos (ppos ** pdir) (qpos ** qdir) (qpi, pi) = fst $ qpi pi

public export
pfParEvalOnDir : (p, q : PolyFunc) ->
  (i : pfPos (pfParProductArena (pfParProdClosure p q) p)) ->
  pfDir {p=q} (pfParEvalOnPos p q i) ->
  pfDir {p=(pfParProductArena (pfParProdClosure p q) p)} i
pfParEvalOnDir (ppos ** pdir) (qpos ** qdir) (qpd, pi) qd with
    (pfParEvalOnPos (ppos ** pdir) (qpos ** qdir) (qpd, pi)) proof eqq
  pfParEvalOnDir (ppos ** pdir) (qpos ** qdir) (qpd, pi) qd | qi with
      (snd (qpd pi) (replace {p=qdir} (sym eqq) qd)) proof eqp
    pfParEvalOnDir (ppos ** pdir) (qpos ** qdir) (qpd, pi) qd | qi | ((), pd) =
      ((pi ** rewrite eqq in qd ** rewrite eqp in Left ()), pd)

public export
pfParEval : (p, q : PolyFunc) ->
  PolyNatTrans (pfParProductArena (pfParProdClosure p q) p) q
pfParEval p q = (pfParEvalOnPos p q ** pfParEvalOnDir p q)

public export
pfParCurryOnPos1 :
  (ppos, qpos, rpos : Type) ->
  (pdir : ppos -> Type) ->
  (qdir : qpos -> Type) ->
  (rdir : rpos -> Type) ->
  (alpha : PolyNatTrans
    (pfParProductArena (ppos ** pdir) (qpos ** qdir)) (rpos ** rdir)) ->
  ppos -> qpos -> rpos
pfParCurryOnPos1 ppos qpos rpos pdir qdir rdir (onpos ** ondir) pi qi =
  onpos (pi, qi)

public export
pfParCurryOnPos2 :
  (ppos, qpos, rpos : Type) ->
  (pdir : ppos -> Type) ->
  (qdir : qpos -> Type) ->
  (rdir : rpos -> Type) ->
  (alpha : PolyNatTrans
    (pfParProductArena (ppos ** pdir) (qpos ** qdir)) (rpos ** rdir)) ->
  (pi : ppos) -> (qi : qpos) ->
  rdir (pfParCurryOnPos1 ppos qpos rpos pdir qdir rdir alpha pi qi) ->
  ((), qdir qi)
pfParCurryOnPos2 ppos qpos rpos pdir qdir rdir (onpos ** ondir) pi qi rd
    with (ondir (pi, qi) rd)
  pfParCurryOnPos2 ppos qpos rpos pdir qdir rdir (onpos ** ondir) pi qi rd |
    (pd, qd) = ((), qd)

public export
pfParCurryOnPos :
  (ppos, qpos, rpos : Type) ->
  (pdir : ppos -> Type) ->
  (qdir : qpos -> Type) ->
  (rdir : rpos -> Type) ->
  (alpha : PolyNatTrans
    (pfParProductArena (ppos ** pdir) (qpos ** qdir)) (rpos ** rdir)) ->
  ppos -> pfPos (pfParProdClosure (qpos ** qdir) (rpos ** rdir))
pfParCurryOnPos ppos qpos rpos pdir qdir rdir alpha pi qi =
  (pfParCurryOnPos1 ppos qpos rpos pdir qdir rdir alpha pi qi **
   pfParCurryOnPos2 ppos qpos rpos pdir qdir rdir alpha pi qi)

public export
pfParCurryOnDir :
  (ppos, qpos, rpos : Type) ->
  (pdir : ppos -> Type) ->
  (qdir : qpos -> Type) ->
  (rdir : rpos -> Type) ->
  (alpha : PolyNatTrans
    (pfParProductArena (ppos ** pdir) (qpos ** qdir)) (rpos ** rdir)) ->
  (pi : ppos) ->
  pfDir {p=(pfParProdClosure (qpos ** qdir) (rpos ** rdir))}
    (pfParCurryOnPos ppos qpos rpos pdir qdir rdir alpha pi) ->
  pfDir {p=(ppos ** pdir)} pi
pfParCurryOnDir ppos qpos rpos pdir qdir rdir (onpos ** ondir)
  pi (qi ** rd ** cd) with (ondir (pi, qi) rd) proof eq
    pfParCurryOnDir ppos qpos rpos pdir qdir rdir (onpos ** ondir)
      pi (qi ** rd ** uv) | (pd, qd) =
        pd

public export
pfParCurry : {p, q, r : PolyFunc} ->
  PolyNatTrans (pfParProductArena p q) r ->
  PolyNatTrans p (pfParProdClosure q r)
pfParCurry {p=(ppos ** pdir)} {q=(qpos ** qdir)} {r=(rpos ** rdir)} alpha =
  (pfParCurryOnPos ppos qpos rpos pdir qdir rdir alpha **
   pfParCurryOnDir ppos qpos rpos pdir qdir rdir alpha)

public export
PolyLKnt : (g, j : PolyFunc) ->
  PolyNatTrans g (pfCompositionArena (PolyLKanExt j g) j)
PolyLKnt (gpos ** gdir) (jpos ** jdir) =
  (\gi => (gi ** \(ji ** jgd) => ji) ** \gi, ((ji ** jgd) ** jd) => jgd jd)

------------------------------------------------
------------------------------------------------
---- Composition of natural transformations ----
------------------------------------------------
------------------------------------------------

public export
pntId : (p : PolyFunc) -> PolyNatTrans p p
pntId (pos ** dir) = (id ** \_ => id)

-- Vertical composition of natural transformations, which is the categorial
-- composition in the category of polynomial functors.
public export
pntVCatComp : {0 p, q, r : PolyFunc} ->
  PolyNatTrans q r -> PolyNatTrans p q -> PolyNatTrans p r
pntVCatComp {p=(ppos ** pdir)} {q=(qpos ** qdir)} {r=(rpos ** rdir)}
  (gOnPos ** gOnDir) (fOnPos ** fOnDir) =
    (gOnPos . fOnPos ** \pi, rd => fOnDir pi $ gOnDir (fOnPos pi) rd)

-- Horizontal composition of natural transformations, also known as
-- the monoidal product or composition product.
public export
pntHProdComp : {0 p, q, p', q' : PolyFunc} ->
  PolyNatTrans p p' -> PolyNatTrans q q' ->
  PolyNatTrans (pfCompositionArena p q) (pfCompositionArena p' q')
pntHProdComp
  {p=(ppos ** pdir)} {q=(qpos ** qdir)}
  {p'=(ppos' ** pdir')} {q'=(qpos' ** qdir')}
  (fOnPos ** fOnDir) (gOnPos ** gOnDir) =
    (\qpi => (fOnPos (fst qpi) ** gOnPos . snd qpi . fOnDir (fst qpi)) **
     \qpi, qdi' =>
      (fOnDir (fst qpi) (fst qdi') **
       gOnDir (snd qpi (fOnDir (fst qpi) (fst qdi'))) (snd qdi')))

public export
polyWhiskerLeft : {p, q : PolyFunc} ->
  (nu : PolyNatTrans p q) -> (r : PolyFunc) ->
  PolyNatTrans (pfCompositionArena p r) (pfCompositionArena q r)
polyWhiskerLeft {p=(ppos ** pdir)} {q=(qpos ** qdir)}
  (onPos ** onDir) (rpos ** rdir) =
    (\pri => (onPos (fst pri) ** snd pri . onDir (fst pri)) **
     \pri, qd => (onDir (fst pri) (fst qd) ** snd qd))

public export
polyWhiskerRight : {p, q : PolyFunc} ->
  (r : PolyFunc) -> (nu : PolyNatTrans p q) ->
  PolyNatTrans (pfCompositionArena r p) (pfCompositionArena r q)
polyWhiskerRight {p=(ppos ** pdir)} {q=(qpos ** qdir)}
  (rpos ** rdir) (onPos ** onDir) =
    (\rpi => (fst rpi ** onPos . snd rpi) **
     \rpi, qd => (fst qd ** onDir (snd rpi (fst qd)) (snd qd)))

public export
pntToIdLeft : (p : PolyFunc) ->
  PolyNatTrans p (pfCompositionArena PFIdentityArena p)
pntToIdLeft (pos ** dir) = (\i => (() ** const i) ** \_, qd => snd qd)

public export
pntToIdRight : (p : PolyFunc) ->
  PolyNatTrans p (pfCompositionArena p PFIdentityArena)
pntToIdRight (pos ** dir) = (\i => (i ** const ()) ** \_, qd => fst qd)

public export
pntFromIdLeft : (p : PolyFunc) ->
  PolyNatTrans (pfCompositionArena PFIdentityArena p) p
pntFromIdLeft (pos ** dir) =
  (\(() ** p) => p () ** \(() ** d), di => (() ** di))

public export
pntFromIdRight : (p : PolyFunc) ->
  PolyNatTrans (pfCompositionArena p PFIdentityArena) p
pntFromIdRight (pos ** dir) = (fst ** \(i ** d), di => (di ** ()))

public export
pntAssociateR : (p, q, r : PolyFunc) ->
  PolyNatTrans
    (pfCompositionArena (pfCompositionArena p q) r)
    (pfCompositionArena p (pfCompositionArena q r))
pntAssociateR (ppos ** pdir) (qpos ** qdir) (rpos ** rdir) =
  (\pqi =>
    (fst (fst pqi) **
     \pd => (snd (fst pqi) pd ** \qd => snd pqi (pd ** qd))) **
   \pqi, qd => ((fst qd ** fst (snd qd)) ** snd (snd qd)))

public export
pntAssociateL : (p, q, r : PolyFunc) ->
  PolyNatTrans
    (pfCompositionArena p (pfCompositionArena q r))
    (pfCompositionArena (pfCompositionArena p q) r)
pntAssociateL (ppos ** pdir) (qpos ** qdir) (rpos ** rdir) =
  (\(i ** d) => ((i ** fst . d) ** \(pd ** qd) => snd (d pd) qd) **
   \(pi ** pd), ((pd' ** qd) ** rd) => (pd' ** (qd ** rd)))

public export
pntAssociateComposeL : {p, q, r, s : PolyFunc} ->
  PolyNatTrans
    (pfCompositionArena (pfCompositionArena p q) r)
    s ->
  PolyNatTrans
    (pfCompositionArena p (pfCompositionArena q r))
    s
pntAssociateComposeL {p} {q} {r} {s} alpha =
  pntVCatComp
    {p=(pfCompositionArena p (pfCompositionArena q r))}
    {q=(pfCompositionArena (pfCompositionArena p q) r)}
    {r=s}
    alpha
    (pntAssociateL p q r)

public export
VertCartFactIsCorrect : {0 p, q : PolyFunc} ->
  (alpha : PolyNatTrans p q) ->
  (pntVCatComp {p} {q=(VertCartFactFunc {p} {q} alpha)} {r=q}
    (CartFactNatTrans {p} {q} alpha) (VertFactNatTrans {p} {q} alpha))
  = alpha
VertCartFactIsCorrect {p=(ppos ** pdir)} {q=(qpos ** qdir)} (onPos ** onDir) =
  Refl

-----------------------------------------------------------
-----------------------------------------------------------
---- Combinators on polynomial natural transformations ----
-----------------------------------------------------------
-----------------------------------------------------------

public export
polyNTConst : (p, q : PolyFunc) -> (qi : pfPos q) -> (pfDir {p=q} qi -> Void) ->
  PolyNatTrans p q
polyNTConst (ppos ** pdir) (qpos ** qdir) qi qdv =
  (const qi ** \pi, qd => void $ qdv qd)

---------------------------------------
---------------------------------------
---- Derived morphisms in PolyFunc ----
---------------------------------------
---------------------------------------

public export
pfUncurry : {p, q, r : PolyFunc} ->
  PolyNatTrans p (pfHomObj q r) -> PolyNatTrans (pfProductArena p q) r
pfUncurry {p} {q} {r} f =
  pntVCatComp {p=(pfProductArena p q)} {q=(pfProductArena (pfHomObj q r) q)}
    (pfEval q r)
    (polyPair {p=(pfProductArena p q)}
      (pntVCatComp {p=(pfProductArena p q)} f (polyProj1 p q))
      (polyProj2 p q))

public export
pfProd1LeftElim : {p, q : PolyFunc} ->
  PolyNatTrans (pfProductArena PFTerminalArena p) q -> PolyNatTrans p q
pfProd1LeftElim {p=(ppos ** pdir)} {q=(qpos ** qdir)} (onpos ** ondir) =
  (onpos . MkPair () **
   \pi, qd => case ondir ((), pi) qd of Left v => void v ; Right pd => pd)

public export
pfProdLeftIntro : {p, q, r : PolyFunc} ->
  PolyNatTrans q r -> PolyNatTrans (pfProductArena p q) r
pfProdLeftIntro {p=(ppos ** pdir)} {q=(qpos ** qdir)} {r=(rpos ** rdir)}
  (onpos ** ondir) =
    (onpos . snd ** \(pi, qi), rd => Right $ ondir qi rd)

----------------------------------------------------------------
----------------------------------------------------------------
---- Reflections of natural transformations into `PolyFunc` ----
----------------------------------------------------------------
----------------------------------------------------------------

public export
PFHomTerm : PolyFunc -> PolyFunc -> Type
PFHomTerm p q = PolyNatTrans PFTerminalArena (pfHomObj p q)

public export
PFtermAsNT : {p, q : PolyFunc} -> PFHomTerm p q -> PolyNatTrans p q
PFtermAsNT {p} {q} t =
  pfProd1LeftElim $ pfUncurry {p=PFTerminalArena} {q=p} {r=q} t

public export
NTasPFterm : {p, q : PolyFunc} -> PolyNatTrans p q -> PFHomTerm p q
NTasPFterm {p} {q} f =
  pfCurry {p=PFTerminalArena} {q=p} {r=q} $ pfProdLeftIntro f

------------------------------
------------------------------
---- Trees on polynomials ----
------------------------------
------------------------------

public export
StageNPreTree : PolyFunc -> Nat -> Type
StageNPreTree = pfCompositionPowerPos

public export
HeightNLeaf : (p : PolyFunc) -> (n : Nat) -> StageNPreTree p n -> Type
HeightNLeaf = pfCompositionPowerDir

------------------------------------
------------------------------------
---- Polynomial-functor algebra ----
------------------------------------
------------------------------------

-----------------------------------------
---- Algebras of polynomial functors ----
-----------------------------------------

public export
PFAlg : PolyFunc -> Type -> Type
PFAlg p a = (i : pfPos p) -> (pfDir {p} i -> a) -> a

public export
InterpPFAlg : {0 p : PolyFunc} -> {0 a : Type} ->
  PFAlg p a -> Algebra (InterpPolyFunc p) a
InterpPFAlg {p} {a} alg (i ** d) = alg i d

public export
PFAlgFromAlg : {0 p : PolyFunc} -> {0 a : Type} ->
  Algebra (InterpPolyFunc p) a -> PFAlg p a
PFAlgFromAlg {p} {a} alg i d = alg (i ** d)

public export
PFAlgCPS : PolyFunc -> Type -> Type
PFAlgCPS p = PFAlg p . Continuation

public export
0 PolyAlgCommutes : (0 p : PolyFunc) -> {0 a, b : Type} -> (0 j : a -> b) ->
  (g : Algebra (InterpPolyFunc p) a) -> (h : Algebra (InterpPolyFunc p) b) ->
  Type
PolyAlgCommutes p {a} {b} j g h = ExtEq (j . g) (h . InterpPFMap p j)

public export
PolyContinuation : Type -> Type
PolyContinuation a = PolyNatTrans (PFHomArena a) PFIdentityArena

public export
ContinuationFromPoly : {a : Type} -> PolyContinuation a -> Continuation a
ContinuationFromPoly {a} (unitId ** d) = toYo $ d () ()

public export
ContinuationToPoly : {a : Type} -> Continuation a -> PolyContinuation a
ContinuationToPoly {a} cont = (id {a=Unit} ** \(), () => fromYo cont)

-- This is equivalent to `Codensity (InterpPolyFunc p)`.
public export
PolyValuedContinuation : PolyFunc -> Type -> Type
PolyValuedContinuation p = PolyContinuation . InterpPolyFunc p

public export
PolyContNT : PolyFunc -> PolyFunc -> Type
PolyContNT p q =
  NaturalTransformation (PolyValuedContinuation p) (PolyValuedContinuation q)

public export
PFBaseF : PolyFunc -> Type -> Type
PFBaseF p a =
  NaturalTransformation (ContravarHomFunc a) (ExpFunctor (InterpPolyFunc p) a)

public export
PFBaseFToAlg : {p : PolyFunc} -> {a : Type} -> PFBaseF p a -> PFAlg p a
PFBaseFToAlg {p=(pos ** dir)} {a} f = \i, d => f a id (i ** d)

public export
PFAlgToBaseF : {p : PolyFunc} -> {a : Type} -> PFAlg p a -> PFBaseF p a
PFAlgToBaseF {p=(pos ** dir)} {a} alg b f (i ** d) = alg i $ \di => f $ d di

public export
PFNAlg : PolyFuncN -> Type -> Type
PFNAlg (pos ** dir) a = (i : pos) -> Vect (dir i) a -> a

public export
PFAlgFromN : {0 a : Type} -> {p : PolyFuncN} ->
  PFNAlg p a -> PFAlg (pfnFunc p) a
PFAlgFromN {a} {p=(pos ** dir)} alg i = alg i . finFToVect

public export
PFCoprodAlg : {p, q : PolyFunc} -> {a : Type} ->
  PFAlg p a -> PFAlg q a -> PFAlg (pfCoproductArena p q) a
PFCoprodAlg {p=(ppos ** pdir)} {q=(qpos ** qdir)} {a} algp algq (Left i) d =
  algp i d
PFCoprodAlg {p=(ppos ** pdir)} {q=(qpos ** qdir)} {a} algp algq (Right i) d =
  algq i d

-------------------------------------------------
---- Initial algebras of polynomial functors ----
-------------------------------------------------

public export
data PolyFuncMu : PolyFunc -> Type where
  InPFM : {0 p : PolyFunc} ->
    (i : pfPos p) -> (pfDir {p} i -> PolyFuncMu p) -> PolyFuncMu p

public export
PolyFuncNMu : PolyFuncN -> Type
PolyFuncNMu p = PolyFuncMu (pfnFunc p)

public export
InPFMN : {0 p : PolyFuncN} ->
  (i : pfnPos p) -> Vect (pfnDir p i) (PolyFuncNMu p) -> PolyFuncNMu p
InPFMN {p=(pos ** dir)} i = InPFM i . flip index

public export
pfmPos : {p : PolyFunc} -> PolyFuncMu p -> pfPos p
pfmPos (InPFM i d) = i

public export
pfmDir : {p : PolyFunc} ->
  (e : PolyFuncMu p) -> pfDir {p} (pfmPos e) -> PolyFuncMu p
pfmDir (InPFM i d) = d

public export
PolyMuIdAlg : {p : PolyFunc} -> PFAlg p (PolyFuncMu p)
PolyMuIdAlg = InPFM

----------------------------------------------
---- Catamorphisms of polynomial functors ----
----------------------------------------------

public export
pfCata : {0 p : PolyFunc} -> {0 a : Type} -> PFAlg p a -> PolyFuncMu p -> a
pfCata {p=p@(pos ** dir)} {a} alg (InPFM i da) =
  alg i $ \d : dir i => pfCata {p} alg $ da d

public export
PolyInFree : (p : PolyFunc) -> InterpPolyFunc p (PolyFuncMu p) -> PolyFuncMu p
PolyInFree p (i ** d) = InPFM i d

public export
PolyFuncCataIsAlgHomomorphism :
  (p : PolyFunc) -> (b : Type) -> (alg : PFAlg p b) ->
  (x : InterpPolyFunc p (PolyFuncMu p)) ->
  pfCata alg (PolyInFree p x) =
    InterpPFAlg {p} alg (InterpPFMap p (pfCata alg) x)
PolyFuncCataIsAlgHomomorphism (pos ** dir) b alg (i ** d) = Refl

public export
pfnCata : {p : PolyFuncN} -> {0 a : Type} -> PFNAlg p a -> PolyFuncNMu p -> a
pfnCata = pfCata . PFAlgFromN

public export
partial
pfnFold : {p : PolyFuncN} -> {0 a : Type} -> PFNAlg p a -> PolyFuncNMu p -> a
pfnFold {p=p@(pos ** dir)} {a} alg = pfnFold' id where
  mutual
    pfnFold' : (a -> a) -> PolyFuncNMu p -> a
    pfnFold' cont (InPFM i da) =
      pfnFoldMap (dir i) (\v => cont $ alg i v) da

    pfnFoldMap : (n : Nat) -> (Vect n a -> a) -> (Fin n -> PolyFuncNMu p) -> a
    pfnFoldMap Z cont _ = cont []
    pfnFoldMap (S n) cont v =
      pfnFoldMap n (\v' => cont $ (pfnFold' id $ v FZ) :: v') $ v . FS

--------------------------------------------------------------------------
---- Variants of polynomial-functor catamorphism (recursion schemes ) ----
--------------------------------------------------------------------------

-- Catamorphism with an extra parameter of some given type.
public export
PFParamAlg : PolyFunc -> Type -> Type -> Type
PFParamAlg p x a = PFAlg p (x -> a)

public export
pfFreeFEval : {0 p : PolyFunc} -> {0 x, a : Type} ->
  PFParamAlg p x a -> x -> PolyFuncMu p -> a
pfFreeFEval alg = flip $ pfCata alg

-- Catamorphism which passes not only the output of the previous
-- induction steps but also the original `PolyFuncMu` to the algebra.
public export
PFArgAlg : PolyFunc -> Type -> Type
PFArgAlg p a = PolyFuncMu p -> PFAlg p a

public export
pfArgCata : {0 p : PolyFunc} -> {0 a : Type} ->
  PFArgAlg p a -> PolyFuncMu p -> a
pfArgCata {p=p@(_ ** _)} {a} alg elem =
  pfCata {p} {a=(PolyFuncMu p -> a)}
    (\i, d, e' => alg e' i $ flip d e') elem elem

-- Catamorphism with both the original `PolyFuncMu` available as an
-- argument to the algebra and an extra parameter of a given type.
public export
PFParamArgAlg : PolyFunc -> Type -> Type -> Type
PFParamArgAlg p@(pos ** dir) x a =
  PolyFuncMu p -> (i : pos) -> (dir i -> PolyFuncMu p -> a) -> x -> a

public export
pfParamArgCata : {0 p : PolyFunc} -> {0 x, a : Type} ->
  PFArgAlg p a -> x -> PolyFuncMu p -> a
pfParamArgCata {p=p@(_ ** _)} {x} {a} alg =
  flip $ pfArgCata {p} {a=(x -> a)} $ \e, i, d => alg e i . flip d

public export
PFProductAlg : PolyFunc -> PolyFunc -> Type -> Type
PFProductAlg p q = PFAlg (pfParProductArena p q)

-- Catamorphism on a pair of `PolyFuncMu`s giving all combinations of cases
-- to the algebra.
public export
pfProductCata : {0 p, q : PolyFunc} -> {0 a : Type} ->
  PFProductAlg p q a -> PolyFuncMu p -> PolyFuncMu q -> a
pfProductCata {p=(ppos ** pdir)} {q=(qpos ** qdir)} alg =
  pfCata {p=(ppos ** pdir)} {a=(PolyFuncMu (qpos ** qdir) -> a)} $
    \pi, pd, (InPFM qi qd) => alg (pi, qi) $ \(pdi, qdi) => pd pdi $ qd qdi

-- Product catamorphism using the product-hom adjunction.
public export
PFProductHomAlg : PolyFunc -> PolyFunc -> Type -> Type
PFProductHomAlg p q a = PFAlg p (PFAlg q a)

public export
pfProductHomCata : {0 p, q : PolyFunc} -> {0 a : Type} ->
  PFProductHomAlg p q a -> PolyFuncMu p -> PolyFuncMu q -> a
pfProductHomCata {p=(ppos ** pdir)} {q=(qpos ** qdir)} =
  pfCata {p=(qpos ** qdir)} {a} .*
    pfCata {p=(ppos ** pdir)} {a=(PFAlg (qpos ** qdir) a)}

-- Boolean-valued algebra derived from lists of valid combinations.
public export
PFPosList : List PolyFunc -> Type
PFPosList [] = Unit
PFPosList [p] = pfPos p
PFPosList (p :: ps@(_ :: _)) = (pfPos p, PFPosList ps)

public export
PFDirList : {ps : List PolyFunc} -> PFPosList ps -> Type
PFDirList {ps=[]} () = Unit
PFDirList {ps=[p]} i = pfDir {p} i
PFDirList {ps=(p :: ps@(_ :: _))} (i, is) = (pfDir {p} i, PFDirList {ps} is)

-- Boolean-valued algebra derived from lists of valid combinations.
public export
PFListProductBoolAlg : List PolyFunc -> Type
PFListProductBoolAlg ps =
  List (DPair (PFPosList ps) (List . PFDirList {ps}))

-- Boolean-valued algebra derived from lists of valid combinations.
public export
PFProductBoolAlg : PolyFunc -> PolyFunc -> Type
PFProductBoolAlg p q = PFListProductBoolAlg [p, q]

public export
PFProductAlgFromBool : {p, q : PolyFunc} ->
  DecEqPred (pfPos p) -> DecEqPred (pfPos q) ->
  PFProductBoolAlg p q -> PFProductAlg p q Bool
PFProductAlgFromBool {p=(_ ** _)} {q=(_ ** _)} peq qeq l (pi, qi) d =
  any
    (\((pi', qi') ** l') => case (peq pi pi', qeq qi qi') of
      (Yes Refl, Yes Refl) => all d l'
      _ => False)
    l

public export
pfProductBoolCata : {p, q : PolyFunc} ->
  DecEqPred (pfPos p) -> DecEqPred (pfPos q) ->
  PFProductBoolAlg p q -> PolyFuncMu p -> PolyFuncMu q -> Bool
pfProductBoolCata peq qeq = pfProductCata . PFProductAlgFromBool peq qeq

----------------------------------
---- Polynomial (free) monads ----
----------------------------------

public export
data PFTranslatePos : PolyFunc -> Type -> Type where
  PFVar : {0 p : PolyFunc} -> {0 a : Type} -> a -> PFTranslatePos p a
  PFCom : {0 p : PolyFunc} -> {0 a : Type} -> pfPos p -> PFTranslatePos p a

public export
(p : PolyFunc) => Functor (PFTranslatePos p) where
  map m (PFVar x) = PFVar (m x)
  map m (PFCom i) = PFCom i

public export
PFTranslateDir : (p : PolyFunc) -> (a : Type) -> PFTranslatePos p a -> Type
PFTranslateDir (pos ** dir) a (PFVar ea) = Void
PFTranslateDir (pos ** dir) a (PFCom i) = dir i

public export
PFTranslate : PolyFunc -> Type -> PolyFunc
PFTranslate p a = (PFTranslatePos p a ** PFTranslateDir p a)

public export
PFTranslate1 : PolyFunc -> PolyFunc
PFTranslate1 p = PFTranslate p ()

public export
PolyFuncFreeMPos : PolyFunc -> Type
PolyFuncFreeMPos p = PolyFuncMu $ PFTranslate1 p

public export
PolyFuncFreeMDirAlg : (p : PolyFunc) -> PFAlg (PFTranslate1 p) Type
PolyFuncFreeMDirAlg (pos ** dir) (PFVar ()) d = Unit
PolyFuncFreeMDirAlg (pos ** dir) (PFCom i) d = DPair (dir i) d

public export
PolyFuncFreeMDir : (p : PolyFunc) -> PolyFuncFreeMPos p -> Type
PolyFuncFreeMDir p = pfCata {p=(PFTranslate1 p)} $ PolyFuncFreeMDirAlg p

public export
PolyFuncFreeM : PolyFunc -> PolyFunc
PolyFuncFreeM p = (PolyFuncFreeMPos p ** PolyFuncFreeMDir p)

public export
PolyNTvar : (p : PolyFunc) -> PolyNatTrans PFIdentityArena (PolyFuncFreeM p)
PolyNTvar (pos ** dir) = (\_ => InPFM (PFVar ()) (\v => void v) ** \_, _ => ())

public export
InterpPolyFuncFreeM : PolyFunc -> Type -> Type
InterpPolyFuncFreeM = InterpPolyFunc . PolyFuncFreeM

public export
pfFreeComposePos : PolyFunc -> PolyFunc -> Type
pfFreeComposePos q p = pfCompositionPos (PolyFuncFreeM q) (PolyFuncFreeM p)

public export
pfFreeComposeDir : (q, p : PolyFunc) -> pfFreeComposePos q p -> Type
pfFreeComposeDir q p = pfCompositionDir (PolyFuncFreeM q) (PolyFuncFreeM p)

public export
pfFreeComposeArena : PolyFunc -> PolyFunc -> PolyFunc
pfFreeComposeArena q p =
  pfCompositionArena (PolyFuncFreeM q) (PolyFuncFreeM p)

public export
PolyFuncFreeMFromMuTranslate : PolyFunc -> Type -> Type
PolyFuncFreeMFromMuTranslate = PolyFuncMu .* PFTranslate

public export
InPVar : {0 p : PolyFunc} -> {0 a : Type} ->
  a -> PolyFuncFreeMFromMuTranslate p a
InPVar {p=(_ ** _)} {a} x = InPFM (PFVar x) (voidF _)

public export
InPCom : {0 p : PolyFunc} -> {0 a : Type} ->
  (i : pfPos p) -> (pfDir {p} i -> PolyFuncFreeMFromMuTranslate p a) ->
  PolyFuncFreeMFromMuTranslate p a
InPCom {p=(pos ** dir)} {a} i d = InPFM (PFCom i) d

public export
PolyFMInterpToMuTranslateCurried : (p : PolyFunc) -> (a : Type) ->
  (mpos : PolyFuncFreeMPos p) -> (PolyFuncFreeMDir p mpos -> a) ->
  PolyFuncFreeMFromMuTranslate p a
PolyFMInterpToMuTranslateCurried (pos ** dir) a (InPFM (PFVar ()) f) dircat =
  InPFM (PFVar $ dircat ()) (voidF _)
PolyFMInterpToMuTranslateCurried (pos ** dir) a (InPFM (PFCom i) f) dircat =
  InPFM (PFCom i) $
    \di : dir i =>
      PolyFMInterpToMuTranslateCurried (pos ** dir) a (f di) $
        (\d => dircat (di ** d))

public export
PolyFMInterpToMuTranslate : (p : PolyFunc) -> (a : Type) ->
  InterpPolyFuncFreeM p a -> PolyFuncFreeMFromMuTranslate p a
PolyFMInterpToMuTranslate p a (em ** d) =
  PolyFMInterpToMuTranslateCurried p a em d

public export
PolyFMMuTranslateToInterpAlg : (p : PolyFunc) -> (a : Type) ->
  (i : PFTranslatePos p a) ->
  (PFTranslateDir p a i -> InterpPolyFuncFreeM p a) ->
  InterpPolyFuncFreeM p a
PolyFMMuTranslateToInterpAlg (pos ** dir) a (PFVar ea) hyp =
  (InPFM (PFVar ()) (voidF _) ** const ea)
PolyFMMuTranslateToInterpAlg (pos ** dir) a (PFCom i) hyp =
  (InPFM (PFCom i) (fst . hyp) ** \dp => case dp of (d ** c) => snd (hyp d) c)

public export
PolyFMMuTranslateToInterp : (p : PolyFunc) -> (a : Type) ->
  PolyFuncFreeMFromMuTranslate p a -> InterpPolyFuncFreeM p a
PolyFMMuTranslateToInterp p a = pfCata $ PolyFMMuTranslateToInterpAlg p a

public export
PFTranslateAlg : PolyFunc -> Type -> Type -> Type
PFTranslateAlg p a b = PFAlg (PFTranslate p a) b

public export
PFAlgToTranslate : {p : PolyFunc} -> {a, b : Type} ->
  (a -> b) -> PFAlg p b -> PFTranslateAlg p a b
PFAlgToTranslate {p=(pos ** dir)} {a} {b} subst alg (PFVar v) d = subst v
PFAlgToTranslate {p=(pos ** dir)} {a} {b} subst alg (PFCom t) d = alg t d

public export
pfFreeCata : {p : PolyFunc} -> {a, b : Type} ->
  PFTranslateAlg p a b -> InterpPolyFuncFreeM p a -> b
pfFreeCata {p} {a} {b} alg =
  pfCata {p=(PFTranslate p a)} {a=b} alg . PolyFMInterpToMuTranslate p a

public export
pfSubstCata : {p : PolyFunc} -> {a, b : Type} ->
  (a -> b) -> PFAlg p b -> InterpPolyFuncFreeM p a -> b
pfSubstCata {p} {a} {b} subst alg = pfFreeCata (PFAlgToTranslate subst alg)

public export
PFFreeVoidToMuAlg : (p : PolyFunc) -> PFTranslateAlg p Void (PolyFuncMu p)
PFFreeVoidToMuAlg (pos ** dir) (PFVar v) d = void v
PFFreeVoidToMuAlg (pos ** dir) (PFCom c) d = InPFM c d

public export
pfFreeMVoidToMu : {p : PolyFunc} -> InterpPolyFuncFreeM p Void -> PolyFuncMu p
pfFreeMVoidToMu {p} =
  pfFreeCata {p} {a=Void} {b=(PolyFuncMu p)} $ PFFreeVoidToMuAlg p

-- Another name for an algebra just to emphasize when we think of it
-- as the implementation of an interface represented by a polynomial.
public export
PolyIFace : PolyFunc -> Type -> Type
PolyIFace = Algebra . InterpPolyFunc

public export
PolyFreeAlgF : (p : PolyFunc) -> (a : Type) ->
  PolyIFace p (InterpPolyFuncFreeM p a)
PolyFreeAlgF (pos ** dir) a (i ** d) =
  (InPFM (PFCom {p=(pos ** dir)} i) (fst . d) ** \(di ** dd) => snd (d di) dd)

public export
PFMuToFreeMVoidAlg : (p : PolyFunc) -> PFAlg p (InterpPolyFuncFreeM p Void)
PFMuToFreeMVoidAlg p = PFAlgFromAlg $ PolyFreeAlgF p Void

public export
pfMuToFreeMVoid : {p : PolyFunc} -> PolyFuncMu p -> InterpPolyFuncFreeM p Void
pfMuToFreeMVoid {p} =
  pfCata {p} {a=(InterpPolyFuncFreeM p Void)} (PFMuToFreeMVoidAlg p)

public export
InFMVar : {p : PolyFunc} -> {a : Type} ->
  a -> InterpPolyFuncFreeM p a
InFMVar {p} {a} x = PolyFMMuTranslateToInterp p a $ InPVar x

public export
InFMCom : {p : PolyFunc} -> {a : Type} ->
  (i : pfPos p) -> (pfDir {p} i -> InterpPolyFuncFreeM p a) ->
  InterpPolyFuncFreeM p a
InFMCom {p=p@(pos ** dir)} {a} i d =
  PolyFMMuTranslateToInterp p a (InPCom i $ PolyFMInterpToMuTranslate p a . d)

public export
pfPolyCata : {p, q : PolyFunc} ->
  PolyNatTrans p q -> PolyFuncMu p -> PolyFuncMu q
pfPolyCata {p=p@(ppos ** pdir)} {q=q@(qpos ** qdir)} (onPos ** onDir) =
  pfCata {p} {a=(PolyFuncMu q)} $ \i, d => InPFM (onPos i) (d . onDir i)

public export
pfTranslatePosBimap : {p, q : PolyFunc} -> {a, b : Type} ->
  (posmap : pfPos p -> pfPos q) -> (typemap : a -> b) ->
  PFTranslatePos p a -> PFTranslatePos q b
pfTranslatePosBimap posmap typemap (PFVar v) = PFVar (typemap v)
pfTranslatePosBimap posmap typemap (PFCom i) = PFCom (posmap i)

public export
pfTranslateDirBimap : {p, q : PolyFunc} -> {a, b : Type} ->
  (posmap : pfPos p -> pfPos q) -> (typemap : a -> b) ->
  (dirmap : (i : pfPos p) -> pfDir {p=q} (posmap i) -> pfDir {p} i) ->
  (i : PFTranslatePos p a) ->
  PFTranslateDir q b (pfTranslatePosBimap posmap typemap i) ->
  PFTranslateDir p a i
pfTranslateDirBimap {p=(ppos ** pdir)} {q=(qpos ** qdir)} posmap typemap dirmap
  (PFVar v) d = void d
pfTranslateDirBimap {p=(ppos ** pdir)} {q=(qpos ** qdir)} posmap typemap dirmap
  (PFCom i) d = dirmap i d

public export
pfTranslateNT : {p, q : PolyFunc} ->
  PolyNatTrans p q -> PolyNatTrans (PFTranslate p ()) (PFTranslate q ())
pfTranslateNT {p=p@(ppos ** pdir)} {q=q@(qpos ** qdir)} (onPos ** onDir) =
  (pfTranslatePosBimap {p} {q} {a=()} {b=()} onPos id **
   pfTranslateDirBimap {p} {q} {a=()} {b=()} onPos id onDir)

public export
pfFreePolyCataOnPos : {p, q : PolyFunc} ->
  PolyNatTrans p q -> PolyFuncFreeMPos p -> PolyFuncFreeMPos q
pfFreePolyCataOnPos {p=p@(ppos ** pdir)} {q=q@(qpos ** qdir)} (onPos ** onDir) =
  pfPolyCata (pfTranslateNT {p} {q} (onPos ** onDir))

public export
pfFreePolyCataOnDir : {p, q : PolyFunc} ->
  (alpha : PolyNatTrans p q) ->
  (i : PolyFuncFreeMPos p) ->
  PolyFuncFreeMDir q (pfFreePolyCataOnPos {p} {q} alpha i) ->
  PolyFuncFreeMDir p i
pfFreePolyCataOnDir {p=p@(ppos ** pdir)} {q=q@(qpos ** qdir)} (onPos ** onDir)
  (InPFM (PFVar ()) d) e =
    ()
pfFreePolyCataOnDir {p=(ppos ** pdir)} {q=(qpos ** qdir)} (onPos ** onDir)
  (InPFM {p=(PFTranslate (ppos ** pdir) ())} (PFCom x) d)
  (MkDPair qd qdi) =
    (onDir x qd **
     pfFreePolyCataOnDir {p=(ppos ** pdir)} {q=(qpos ** qdir)}
      (onPos ** onDir) (d (onDir x qd)) qdi)

public export
pfFreePolyCata : {p, q : PolyFunc} ->
  PolyNatTrans p q -> PolyNatTrans (PolyFuncFreeM p) (PolyFuncFreeM q)
pfFreePolyCata {p=p@(ppos ** pdir)} {q=q@(qpos ** qdir)} (onPos ** onDir) =
  (pfFreePolyCataOnPos {p} {q} (onPos ** onDir) **
   pfFreePolyCataOnDir {p} {q} (onPos ** onDir))

-- Product catamorphism using the product-hom adjunction and a natural
-- transformation to produce an output which also comes from an initial
-- algebra.
public export
PFProductHomAlgNT : PolyFunc -> PolyFunc -> PolyFunc -> Type
PFProductHomAlgNT p q r = PFAlg p (PolyNatTrans q r)

public export
pfProductHomCataNT : {p, q, r : PolyFunc} -> PFProductHomAlgNT p q r ->
  PolyFuncMu p -> PolyFuncMu q -> PolyFuncMu r
pfProductHomCataNT {p} {q} {r} =
  pfPolyCata {p=q} {q=r} .* pfCata {p} {a=(PolyNatTrans q r)}

--------------------------------------
--------------------------------------
---- Polynomial-functor coalgebra ----
--------------------------------------
--------------------------------------

-------------------------------------------
---- Coalgebras of polynomial functors ----
-------------------------------------------

public export
PFCoalg : PolyFunc -> Type -> Type
PFCoalg p a = a -> InterpPolyFunc p a

public export
PFCoalgCPS : PolyFunc -> Type -> Type
PFCoalgCPS p a = a -> Continuation $ InterpPolyFunc p a

public export
PFCobaseF : PolyFunc -> Type -> Type
PFCobaseF p a =
  NaturalTransformation (CovarHomFunc a) (FunctorExp (InterpPolyFunc p) a)

public export
PFCobaseFToCoalg : {p : PolyFunc} -> {a : Type} -> PFCobaseF p a -> PFCoalg p a
PFCobaseFToCoalg {p=(pos ** dir)} {a} = \f, x => f a id x

public export
PFCoalgToCobaseF : {p : PolyFunc} -> {a : Type} -> PFCoalg p a -> PFCobaseF p a
PFCoalgToCobaseF {p=(pos ** dir)} {a} coalg b f x =
  let (i ** d) = coalg x in (i ** f . d)

{- One direction of 6.65 from "A General Theory of Interaction". -}
public export
PFMonoToCofunc : {p : PolyFunc} -> {a, b : Type} ->
  PolyNatTrans (pfMonomialArena a b) p -> a -> InterpPolyFunc p b
PFMonoToCofunc {p=(pos ** dir)} {a} {b} (onPos ** onDir) x =
  (onPos x ** onDir x)

public export
PFMonoToCoalg : {p : PolyFunc} -> {a : Type} ->
  PolyNatTrans (pfMonomialArena a a) p -> PFCoalg p a
PFMonoToCoalg {p=(pos ** dir)} {a} = PFMonoToCofunc {p=(pos ** dir)} {a} {b=a}

{- The other direction of 6.65 from "A General Theory of Interaction". -}
public export
PFCofuncToMono : {p : PolyFunc} -> {a, b : Type} ->
  (a -> InterpPolyFunc p b) -> PolyNatTrans (pfMonomialArena a b) p
PFCofuncToMono {p=(pos ** dir)} {a} {b} f = (fst . f ** \x => snd (f x))

public export
PFCoalgToMono : {p : PolyFunc} -> {a : Type} ->
  PFCoalg p a -> PolyNatTrans (pfMonomialArena a a) p
PFCoalgToMono {p=(pos ** dir)} {a} = PFCofuncToMono {p=(pos ** dir)} {a} {b=a}

----------------------------------------------------
---- Terminal coalgebras of polynomial functors ----
----------------------------------------------------

public export
data PolyFuncNu : PolyFunc -> Type where
  InPFN : {0 p : PolyFunc} ->
    (i : pfPos p) -> (pfDir {p} i -> Inf (PolyFuncNu p)) -> PolyFuncNu p

---------------------------------------------
---- Anamorphisms of polynomial functors ----
---------------------------------------------

public export
pfAna : {0 p : PolyFunc} -> {0 a : Type} -> PFCoalg p a -> a -> PolyFuncNu p
pfAna {p=p@(pos ** dir)} {a} coalg e = case coalg e of
  (i ** da) => InPFN i $ \d : dir i => pfAna coalg $ da d

public export
partial
pfNuCata : {0 p : PolyFunc} -> {0 a : Type} -> PFAlg p a -> PolyFuncNu p -> a
pfNuCata {p=p@(pos ** dir)} {a} alg (InPFN i da) =
  alg i $ \d : dir i => pfNuCata {p} alg $ da d

-----------------
---- P-trees ----
-----------------

-- A path through a p-tree whose last vertex is labeled with the given position.
public export
data PPathPos : (p : PolyFunc) -> pfPos p -> Type where
  PPRoot : {p : PolyFunc} -> (i : pfPos p) -> PPathPos p i
  PPPath : {p : PolyFunc} -> {i : pfPos p} ->
    PPathPos p i -> pfDir {p} i -> (j : pfPos p) -> PPathPos p j

public export
PPath : PolyFunc -> Type
PPath p = DPair (pfPos p) (PPathPos p)

public export
PPathPred : PolyFunc -> Type
PPathPred p = (i : pfPos p) -> PPathPos p i -> pfDir {p} i -> Maybe (pfPos p)

public export
PPathPredGenPosT : {p : PolyFunc} ->
  PPathPred p -> (i : pfPos p) -> PPathPos p i -> Type
PPathPredGenPosT pred i (PPRoot i) = ()
PPathPredGenPosT pred j (PPPath {i} pp di j) =
  Pair (PPathPredGenPosT pred i pp) (pred i pp di = Just j)

public export
0 PPathPredGenPosDec : {p : PolyFunc} ->
  (dirDec : (i' : pfPos p) -> (di', di'' : pfDir {p} i') -> Dec (di' = di'')) ->
  (pred : PPathPred p) -> (i : pfPos p) -> (pp : PPathPos p i) ->
  Dec (PPathPredGenPosT {p} pred i pp)
PPathPredGenPosDec {p} dirDec pred i (PPRoot i) =
  ?PPathPredGenPosDec_hole_root
PPathPredGenPosDec {p} dirDec pred j (PPPath {i} pp di j) =
  let r = PPathPredGenPosDec {p} dirDec pred i pp in
  ?PPathPredGenPosDec_hole_path

public export
0 PPathPredGenPosDecPred : {p : PolyFunc} ->
  (dirDec : (i' : pfPos p) -> (di', di'' : pfDir {p} i') -> Dec (di' = di'')) ->
  (pred : PPathPred p) -> (i : pfPos p) -> (pp : PPathPos p i) ->
  Bool
PPathPredGenPosDecPred {p} dirDec pred i pp =
  isYes $ PPathPredGenPosDec {p} dirDec pred i pp

-- A proof that the given predicate can generate the given path.
public export
data PPathPredGenPos : {p : PolyFunc} ->
    PPathPred p -> (i : pfPos p) -> PPathPos p i -> Type where
  PPGRoot : {p : PolyFunc} -> (pred : PPathPred p) ->
    (i : pfPos p) -> PPathPredGenPos pred i (PPRoot i)
  PPGPath : {p : PolyFunc} -> {pred : PPathPred p} ->
    {i : pfPos p} -> {ppi : PPathPos p i} ->
    PPathPredGenPos {p} pred i ppi ->
    (di : pfDir {p} i) -> (j : pfPos p) -> pred i ppi di = Just j ->
    PPathPredGenPos {p} pred j (PPPath {p} {i} ppi di j)

public export
PPathPredNotGenPos : {p : PolyFunc} ->
  PPathPred p -> (i : pfPos p) -> PPathPos p i -> Type
PPathPredNotGenPos {p} pp i ppi = Not $ PPathPredGenPos pp i ppi

public export
PPathPredGen : {p : PolyFunc} -> PPathPred p -> PPath p -> Type
PPathPredGen {p} pred (i ** ppi) = PPathPredGenPos {p} pred i ppi

public export
PPathPredNotGen : {p : PolyFunc} -> PPathPred p -> PPath p -> Type
PPathPredNotGen {p} pred pp = Not $ PPathPredGen {p} pred pp

public export
0 PPathPredGenCorrect : {p : PolyFunc} -> PPathPred p -> Type
PPathPredGenCorrect {p} pred =
  (i : pfPos p) -> (ppi : PPathPos p i) ->
  PPathPredGenPos {p} pred i ppi -> (di : pfDir {p} i) ->
  IsJustTrue (pred i ppi di)

public export
0 PPathPredNotGenCorrect : {p : PolyFunc} -> PPathPred p -> Type
PPathPredNotGenCorrect {p} pred =
  (i : pfPos p) -> (ppi : PPathPos p i) ->
  PPathPredNotGenPos {p} pred i ppi -> (di : pfDir {p} i) ->
  IsNothingTrue (pred i ppi di)

public export
0 PPathPredCorrect : {p : PolyFunc} -> PPathPred p -> Type
PPathPredCorrect {p} pred =
  (PPathPredGenCorrect {p} pred, PPathPredNotGenCorrect {p} pred)

public export
PTree : PolyFunc -> Type
PTree p = Subset0 (PPathPred p) (PPathPredCorrect {p})

public export
PVertex : {p : PolyFunc} -> PTree p -> Type
PVertex {p} pt = Subset0 (PPath p) (PPathPredGen {p} $ fst0 pt)

--------------------------------------
---- Polynomial (cofree) comonads ----
--------------------------------------

public export
data PFScalePos : PolyFunc -> Type -> Type where
  PFNode : {0 p : PolyFunc} -> {0 a : Type} -> a -> pfPos p -> PFScalePos p a

public export
PFScaleDir : (p : PolyFunc) -> (a : Type) -> PFScalePos p a -> Type
PFScaleDir (pos ** dir) a (PFNode _ i) = dir i

public export
PFScale : PolyFunc -> Type -> PolyFunc
PFScale p a = (PFScalePos p a ** PFScaleDir p a)

-- Uses Mu instead of Nu -- the type is a closure.
public export
PolyFuncCofreeCMPos : PolyFunc -> Type
PolyFuncCofreeCMPos p = PolyFuncMu $ PFScale p ()

public export
PolyFuncCofreeCMDirAlg : (p : PolyFunc) -> PFAlg (PFScale p ()) Type
PolyFuncCofreeCMDirAlg (pos ** dir) (PFNode () i) d =
  Either Unit (DPair (dir i) d)

public export
PolyFuncCofreeCMDir : (p : PolyFunc) -> PolyFuncCofreeCMPos p -> Type
PolyFuncCofreeCMDir p = pfCata {p=(PFScale p ())} $ PolyFuncCofreeCMDirAlg p

public export
PolyFuncCofreeCM: PolyFunc -> PolyFunc
PolyFuncCofreeCM p = (PolyFuncCofreeCMPos p ** PolyFuncCofreeCMDir p)

public export
InterpPolyFuncCofreeCM : PolyFunc -> Type -> Type
InterpPolyFuncCofreeCM = InterpPolyFunc . PolyFuncCofreeCM

public export
PolyFuncCofreeCMFromNuScale : PolyFunc -> Type -> Type
PolyFuncCofreeCMFromNuScale = PolyFuncNu .* PFScale

public export
PolyFuncCofreeCMPosFromNuScale : PolyFunc -> Type
PolyFuncCofreeCMPosFromNuScale p = PolyFuncCofreeCMFromNuScale p ()

public export
partial
PolyFuncCofreeCMDirFromNuScale :
  (p : PolyFunc) -> PolyFuncCofreeCMPosFromNuScale p -> Type
PolyFuncCofreeCMDirFromNuScale p =
  pfNuCata {p=(PFScale p ())} $ PolyFuncCofreeCMDirAlg p

public export
partial
PolyFuncCofreeCMArenaFromNuScale : PolyFunc -> PolyFunc
PolyFuncCofreeCMArenaFromNuScale p =
  (PolyFuncCofreeCMPosFromNuScale p ** PolyFuncCofreeCMDirFromNuScale p)

public export
InPNode : {0 p : PolyFunc} -> {0 a : Type} ->
  a -> (i : pfPos p) ->
  (pfDir {p} i -> Inf (PolyFuncCofreeCMFromNuScale p a)) ->
  PolyFuncCofreeCMFromNuScale p a
InPNode {p=(_ ** _)} {a} i d = InPFN (PFNode i d)

public export
partial
PolyFuncCofreeCMPosScaleToFunc : {p : PolyFunc} ->
  PolyFuncCofreeCMPosFromNuScale p -> PolyFuncCofreeCMPos p
PolyFuncCofreeCMPosScaleToFunc {p=p@(pos ** dir)} (InPFN (PFNode () i) d) =
  InPFM (PFNode () i) $ \di : dir i => PolyFuncCofreeCMPosScaleToFunc (d di)

public export
PolyFuncCofreeCMPosFuncToNuScale : {p : PolyFunc} ->
  PolyFuncCofreeCMPos p -> PolyFuncCofreeCMPosFromNuScale p
PolyFuncCofreeCMPosFuncToNuScale {p=p@(pos ** dir)} (InPFM (PFNode () i) d) =
  InPFN (PFNode () i) $ \di : dir i => PolyFuncCofreeCMPosFuncToNuScale (d di)

public export
PolyCFCMInterpToNuScaleCurried : (p : PolyFunc) -> (a : Type) ->
  (mpos : PolyFuncCofreeCMPos p) -> (PolyFuncCofreeCMDir p mpos -> a) ->
  PolyFuncCofreeCMFromNuScale p a
PolyCFCMInterpToNuScaleCurried p@(pos ** dir) a (InPFM (PFNode () i) f) dircat =
  InPFN (PFNode (dircat $ Left ()) i) $
    \di : dir i =>
      PolyCFCMInterpToNuScaleCurried p a (f di) $
        \d => dircat $ Right (di ** d)

public export
PolyCFCMInterpToNuScale : (p : PolyFunc) -> (a : Type) ->
  InterpPolyFuncCofreeCM p a -> PolyFuncCofreeCMFromNuScale p a
PolyCFCMInterpToNuScale p a (em ** d) = PolyCFCMInterpToNuScaleCurried p a em d

public export
PolyCFCMScaleToInterpAlg : (p : PolyFunc) -> (a : Type) ->
  (i : PFScalePos p a) ->
  (PFScaleDir p a i -> InterpPolyFuncCofreeCM p a) ->
  InterpPolyFuncCofreeCM p a
PolyCFCMScaleToInterpAlg (pos ** dir) a (PFNode x i) hyp =
  (InPFM (PFNode () i) (fst . hyp) **
   \dp => case dp of
    Left () => x
    Right (di ** cmdi) => snd (hyp di) cmdi)

public export
partial
PolyCFCMScaleToInterp : (p : PolyFunc) -> (a : Type) ->
  PolyFuncCofreeCMFromNuScale p a -> InterpPolyFuncCofreeCM p a
PolyCFCMScaleToInterp p a = pfNuCata $ PolyCFCMScaleToInterpAlg p a

public export
PFScaleCoalg : PolyFunc -> Type -> Type -> Type
PFScaleCoalg p a b = PFCoalg (PFScale p a) b

public export
pfCofreeAnaScale : {p : PolyFunc} -> {a, b : Type} ->
  PFScaleCoalg p a b -> b -> PolyFuncCofreeCMFromNuScale p a
pfCofreeAnaScale {p} = pfAna {p=(PFScale p a)}

public export
partial
pfCofreeAna : {p : PolyFunc} -> {a, b : Type} ->
  PFScaleCoalg p a b -> b -> InterpPolyFuncCofreeCM p a
pfCofreeAna {p} {a} {b} =
  PolyCFCMScaleToInterp p a .* pfCofreeAnaScale {p} {a} {b}

public export
PolyFuncCofreeCMFromPTreePos : PolyFunc -> Type
PolyFuncCofreeCMFromPTreePos = PTree

public export
PolyFuncCofreeCMFromPTreeDir :
  (p : PolyFunc) -> PolyFuncCofreeCMFromPTreePos p -> Type
PolyFuncCofreeCMFromPTreeDir p = PVertex {p}

public export
PolyFuncCofreeCMFromPTreeArena : PolyFunc -> PolyFunc
PolyFuncCofreeCMFromPTreeArena p =
  (PolyFuncCofreeCMFromPTreePos p ** PolyFuncCofreeCMFromPTreeDir p)

public export
InterpPolyFuncCofreeCMFromPTree : PolyFunc -> Type -> Type
InterpPolyFuncCofreeCMFromPTree =
  InterpPolyFunc . PolyFuncCofreeCMFromPTreeArena

public export
0 PolyFuncCofreeCMPosNuScaleToPTree : {p : PolyFunc} ->
  PolyFuncCofreeCMPosFromNuScale p -> PolyFuncCofreeCMFromPTreePos p
PolyFuncCofreeCMPosNuScaleToPTree {p=p@(pos ** dir)} (InPFN (PFNode () i) d) =
  ?PolyFuncCofreeCMPosNuScaleToPTree_hole

public export
0 PolyFuncCofreeCMPosPTreeToNuScale : {p : PolyFunc} ->
  PolyFuncCofreeCMFromPTreePos p -> PolyFuncCofreeCMPosFromNuScale p
PolyFuncCofreeCMPosPTreeToNuScale {p=p@(pos ** dir)} =
  ?PolyFuncCofreeCMPosPTreeToNuScale_hole

public export
0 PolyFuncCofreeCMDirNuScaleToPTree : {p : PolyFunc} ->
  (i : PolyFuncCofreeCMPosFromNuScale p) ->
  PolyFuncCofreeCMDirFromNuScale p i ->
  PolyFuncCofreeCMFromPTreeDir p (PolyFuncCofreeCMPosNuScaleToPTree i)
PolyFuncCofreeCMDirNuScaleToPTree {p=(pos ** dir)} i di =
  ?PolyFuncCofreeCMDirNuScaleToPTree_hole

public export
0 PolyFuncCofreeCMDirPTreeToNuScale : {p : PolyFunc} ->
  (i : PolyFuncCofreeCMFromPTreePos p) ->
  PolyFuncCofreeCMFromPTreeDir p i ->
  PolyFuncCofreeCMDirFromNuScale p (PolyFuncCofreeCMPosPTreeToNuScale i)
PolyFuncCofreeCMDirPTreeToNuScale {p=(pos ** dir)} i di =
  ?PolyFuncCofreeCMDPTreeToNuScale_hole

-------------------------------
-------------------------------
---- Polynomial interfaces ----
-------------------------------
-------------------------------

-- The free monad of a coproduct of polynomial functors implements each of the
-- interfaces induced by the two functors.

public export
PolyCoprodFreeAlgFl : (p, q : PolyFunc) -> (a : Type) ->
  PolyIFace p (InterpPolyFuncFreeM (pfCoproductArena p q) a)
PolyCoprodFreeAlgFl (ppos ** pdir) (qpos ** qdir) a (i ** d) =
  (InPFM (PFCom $ Left i) (fst . d) ** \(di ** dd) => snd (d di) dd)

public export
PolyCoprodFreeAlgFr : (p, q : PolyFunc) -> (a : Type) ->
  PolyIFace q (InterpPolyFuncFreeM (pfCoproductArena p q) a)
PolyCoprodFreeAlgFr (ppos ** pdir) (qpos ** qdir) a (i ** d) =
  (InPFM (PFCom $ Right i) (fst . d) ** \(di ** dd) => snd (d di) dd)

----------------------------------------------
----------------------------------------------
---- General polynomial monoids/comonoids ----
----------------------------------------------
----------------------------------------------

--------------------
---- Definition ----
--------------------

public export
record PFMonoid (p : PolyFunc) where
  constructor MkPFMonoid
  pmonReturn : PolyNatTrans PFIdentityArena p
  pmonJoin : PolyNatTrans (pfDuplicateArena p) p

public export
PFMonad : Type
PFMonad = DPair PolyFunc PFMonoid

public export
record PFMonoidCorrect (p : PolyFunc) (m : PFMonoid p) where
  constructor MkPFMonoidCorrect
  leftIdentity :
    pntVCatComp
      {p} {q=(pfDuplicateArena p)} {r=p}
      (pmonJoin m)
      (pntVCatComp
        {p} {q=(pfCompositionArena PFIdentityArena p)} {r=(pfDuplicateArena p)}
        (polyWhiskerLeft {p=PFIdentityArena} {q=p} (pmonReturn m) p)
        (pntToIdLeft p)) =
    pntId p
  rightIdentity :
    pntVCatComp
      {p} {q=(pfDuplicateArena p)} {r=p}
      (pmonJoin m)
      (pntVCatComp
        {p} {q=(pfCompositionArena p PFIdentityArena)} {r=(pfDuplicateArena p)}
        (polyWhiskerRight {p=PFIdentityArena} {q=p} p (pmonReturn m))
        (pntToIdRight p)) =
    pntId p
  mAssociative :
    (pntVCatComp
      {p=(pfTriplicateArenaLeft p)} {q=(pfDuplicateArena p)} {r=p}
      (pmonJoin m)
      (polyWhiskerLeft {p=(pfDuplicateArena p)} {q=p} (pmonJoin m) p)) =
    pntVCatComp
      {p=(pfTriplicateArenaLeft p)} {q=(pfTriplicateArenaRight p)} {r=p}
      (pntVCatComp
        {p=(pfTriplicateArenaRight p)} {q=(pfDuplicateArena p)} {r=p}
        (pmonJoin m)
        (polyWhiskerRight {p=(pfDuplicateArena p)} {q=p} p (pmonJoin m)))
      (pntAssociateR p p p)

public export
PFCorrectMonad : Type
PFCorrectMonad = (p : PolyFunc ** m : PFMonoid p ** PFMonoidCorrect p m)

record PFComonoid (p : PolyFunc) where
  constructor MkPFComonoid
  pcomErase : PolyNatTrans p PFIdentityArena
  pcomDup : PolyNatTrans p (pfDuplicateArena p)

public export
PFComonad : Type
PFComonad = DPair PolyFunc PFComonoid

public export
record PFComonoidCorrect (p : PolyFunc) (c : PFComonoid p) where
  constructor MkPFComonoidCorrect
  leftErasure :
    pntVCatComp
      {p} {q=(pfDuplicateArena p)} {r=(pfCompositionArena PFIdentityArena p)}
      (polyWhiskerLeft {p} {q=PFIdentityArena} (pcomErase c) p)
      (pcomDup c) =
    pntToIdLeft p
  rightErasure :
    pntVCatComp
      {p} {q=(pfDuplicateArena p)} {r=(pfCompositionArena p PFIdentityArena)}
      (polyWhiskerRight {p} {q=PFIdentityArena} p (pcomErase c))
      (pcomDup c) =
    pntToIdRight p
  cmCoassociative :
    pntVCatComp
      {p} {q=(pfTriplicateArenaLeft p)} {r=(pfTriplicateArenaRight p)}
      (pntAssociateR p p p)
      (pntVCatComp
        {p} {q=(pfDuplicateArena p)} {r=(pfTriplicateArenaLeft p)}
        (polyWhiskerLeft {p} {q=(pfDuplicateArena p)} (pcomDup c) p)
        (pcomDup c)) =
      pntVCatComp
        {p} {q=(pfDuplicateArena p)} {r=(pfTriplicateArenaRight p)}
        (polyWhiskerRight {p} {q=(pfDuplicateArena p)} p (pcomDup c))
        (pcomDup c)

public export
PFCorrectComonad : Type
PFCorrectComonad = (p : PolyFunc ** c : PFComonoid p ** PFComonoidCorrect p c)

public export
ComonoidDupOnPosId : {p : PolyFunc} -> (c : PFComonoid p) ->
  (holds : PFComonoidCorrect p c) -> (i : pfPos p) ->
  DPair.fst (pntOnPos {p} {q=(pfDuplicateArena p)} (pcomDup c) i) = i
ComonoidDupOnPosId {p=(pos ** dir)}
  (MkPFComonoid (eOnPos ** eOnDir) (dOnPos ** dOnDir)) holds i =
    mkDPairInjectiveFst $ fcong $ mkDPairInjectiveFst $ rightErasure holds

public export
0 ComonoidDupOnDirPosId : {p : PolyFunc} -> (c : PFComonoid p) ->
  (holds : PFComonoidCorrect p c) -> (i : pfPos p) ->
  DPair.snd (pntOnPos {p} {q=(pfDuplicateArena p)} (pcomDup {p} c) i)
    (rewrite ComonoidDupOnPosId {p} c holds i in
      (pntOnDir {p} {q=PFIdentityArena} (pcomErase {p} c) i) ())
    = i
ComonoidDupOnDirPosId {p=(pos ** dir)}
  c@(MkPFComonoid (eOnPos ** eOnDir) (dOnPos ** dOnDir)) holds i =
  let
    le = leftErasure holds
    re = rightErasure holds
    onPosId = ComonoidDupOnPosId c holds i
    zigZagIdF = mkDPairInjectiveSndHet $ fcong {x=i} $ mkDPairInjectiveFst le
    zigZagId = fcong {x=()} zigZagIdF
  in
  {-
  replace {p=
    (\i' => (.) (snd (dOnPos i')) (eOnDir (fst (dOnPos i'))) () = const i' ())}
  -}
  ?ComonoidDupOnDirPosId_hole

------------------------------------------------------------
------------------------------------------------------------
---- Polynomial comonads as categories (and vice versa) ----
------------------------------------------------------------
------------------------------------------------------------

public export
CatToPolyPos : CatSig -> Type
CatToPolyPos (MkCatSig o m eq i comp) = o

public export
CatToPolyDir : (c : CatSig) -> CatToPolyPos c -> Type
CatToPolyDir (MkCatSig o m eq i comp) = Sigma {a=o} . m

public export
CatToPoly : CatSig -> PolyFunc
CatToPoly c = (CatToPolyPos c ** CatToPolyDir c)

public export
CatToComonoidErase : (c : CatSig) -> PolyNatTrans (CatToPoly c) PFIdentityArena
CatToComonoidErase (MkCatSig o m eq i comp) = (const () ** \a, _ => (a ** i a))

public export
CatToComonoidDup : (c : CatSig) ->
  PolyNatTrans (CatToPoly c) (pfDuplicateArena (CatToPoly c))
CatToComonoidDup (MkCatSig o m eq i comp) =
  (\a => (a ** \d => fst d) **
   \a, qd => let ((b ** f) ** (c ** g)) = qd in (c ** comp g f))

public export
CatToComonoid : (c : CatSig) -> PFComonoid (CatToPoly c)
CatToComonoid c = MkPFComonoid (CatToComonoidErase c) (CatToComonoidDup c)

public export
CatToComonad : CatSig -> PFComonad
CatToComonad c = (CatToPoly c ** CatToComonoid c)

public export
ComonoidToCatObj : {p : PolyFunc} -> PFComonoid p -> Type
ComonoidToCatObj {p} com = pfPos p

public export
ComonoidToCatEmanate : {p : PolyFunc} ->
  (c : PFComonoid p) -> ComonoidToCatObj c -> Type
ComonoidToCatEmanate {p} com a = pfDir {p} a

public export
ComonoidToCatCodom : {p : PolyFunc} -> (c : PFComonoid p) ->
  (holds : PFComonoidCorrect p c) ->
  (a : ComonoidToCatObj c) -> ComonoidToCatEmanate c a -> ComonoidToCatObj c
ComonoidToCatCodom {p=(pos ** dir)}
  c@(MkPFComonoid (eOnPos ** eOnDir) (dOnPos ** dOnDir)) holds a di =
    snd (dOnPos a) $ replace {p=dir} (sym $ ComonoidDupOnPosId c holds a) di

public export
ComonoidToCatMorph : {p : PolyFunc} ->
  (c : PFComonoid p) -> (holds : PFComonoidCorrect p c) ->
  ComonoidToCatObj c -> ComonoidToCatObj c -> Type
ComonoidToCatMorph {p=p@(pos ** dir)} com@(MkPFComonoid e d) holds a b =
  Subset0 (ComonoidToCatEmanate {p} com a)
    (\m => ComonoidToCatCodom {p} com holds a m = b)

public export
ComonoidToCatId : {p : PolyFunc} ->
  (c : PFComonoid p) -> (holds : PFComonoidCorrect p c) ->
  (a : ComonoidToCatObj c) -> ComonoidToCatMorph c holds a a
ComonoidToCatId {p=(pos ** dir)}
  c@(MkPFComonoid (eOnPos ** eOnDir) (dOnPos ** dOnDir)) holds a =
    Element0 (eOnDir a ()) (ComonoidDupOnDirPosId c holds a)

public export
0 ComonoidToCatComp : {p : PolyFunc} ->
  (com : PFComonoid p) -> (holds : PFComonoidCorrect p com) ->
  {a, b, c : ComonoidToCatObj com} ->
  ComonoidToCatMorph com holds b c ->
  ComonoidToCatMorph com holds a b ->
  ComonoidToCatMorph com holds a c
ComonoidToCatComp {p=(pos ** dir)}
  (MkPFComonoid (eOnPos ** eOnDir) (dOnPos ** dOnDir)) holds {a} {b} {c}
  (Element0 gm gcod) (Element0 fm fcod) =
    let onPosId = ComonoidDupOnPosId _ holds in
    Element0
      (dOnDir a
        (replace {p=dir} (sym (onPosId a)) fm **
         replace {p=dir} (sym fcod) gm))
      (trans (?ComonoidToCatComp_hole_codomain_correct) gcod)

public export
0 ComonoidToCat : {p : PolyFunc} ->
  (c : PFComonoid p) -> PFComonoidCorrect p c -> CatSig
ComonoidToCat c holds =
  MkCatSig
    (ComonoidToCatObj c)
    (ComonoidToCatMorph c holds)
    (\a, b => ?ComonoidToCat_eq_hole)
    (ComonoidToCatId c holds)
    (ComonoidToCatComp c holds)

public export
0 ComonadToCat : (com : PFComonad) ->
  PFComonoidCorrect (fst com) (snd com) -> CatSig
ComonadToCat (p ** c) holds = ComonoidToCat {p} c holds

----------------------------------------------------
----------------------------------------------------
---- Density comonad (specifically) as category ----
----------------------------------------------------
----------------------------------------------------

public export
DensityToCatObj : PolyFunc -> Type
DensityToCatObj p = pfPos (PolyDensityComonad p)

public export
DensityToCatEmanate : (p : PolyFunc) -> DensityToCatObj p -> Type
DensityToCatEmanate p = pfDir {p=(PolyDensityComonad p)}

public export
DensityToCatCodom : (p : PolyFunc) -> (a : DensityToCatObj p) ->
  DensityToCatEmanate p a -> DensityToCatObj p
DensityToCatCodom (pos ** dir) i (j ** d) = j

public export
DensityToCatMorph : (p : PolyFunc) ->
  DensityToCatObj p -> DensityToCatObj p -> Type
DensityToCatMorph (pos ** dir) i j = dir j -> dir i

public export
DensityToCatId : (p : PolyFunc) ->
  (a : DensityToCatObj p) -> DensityToCatMorph p a a
DensityToCatId (pos ** dir) i = id {a=(dir i)}

public export
DensityToCatComp : (p : PolyFunc) ->
  {a, b, c : DensityToCatObj p} ->
  DensityToCatMorph p b c -> DensityToCatMorph p a b -> DensityToCatMorph p a c
DensityToCatComp (pos ** dir) {a} {b} {c} = (|>)

public export
DensityToCat : PolyFunc -> CatSig
DensityToCat p@(pos ** dir) =
  MkCatSig
    (DensityToCatObj p)
    (DensityToCatMorph p)
    (\a, b => ExtEq)
    (DensityToCatId p)
    (DensityToCatComp p)

------------------------------------
------------------------------------
---- Specific monoids/comonoids ----
------------------------------------
------------------------------------

----------------------
---- Reader monad ----
----------------------

public export
PFReaderReturnOnPos : (env : Type) -> PFIdentityPos -> PFHomPos env
PFReaderReturnOnPos env () = ()

public export
PFReaderReturnOnDir : (env : Type) -> (i : PFIdentityPos) ->
  PFHomDir env (PFReaderReturnOnPos env i) -> PFIdentityDir i
PFReaderReturnOnDir env () i = ()

public export
PFReaderReturn : (env : Type) -> PolyNatTrans PFIdentityArena (PFHomArena env)
PFReaderReturn env = (PFReaderReturnOnPos env ** PFReaderReturnOnDir env)

public export
PFReaderJoinOnPos : (env : Type) -> pfHomComposePos env env -> PFHomPos env
PFReaderJoinOnPos env (() ** _) = ()

public export
PFReaderJoinOnDir : (env : Type) -> (i : pfHomComposePos env env) ->
  PFHomDir env (PFReaderJoinOnPos env i) -> pfHomComposeDir env env i
PFReaderJoinOnDir env (() ** i) d with (i d)
  PFReaderJoinOnDir env (() ** i) d | () = (d ** d)

public export
PFReaderJoin : (env : Type) ->
  PolyNatTrans (pfHomComposeArena env env) (PFHomArena env)
PFReaderJoin env = (PFReaderJoinOnPos env ** PFReaderJoinOnDir env)

public export
PFReaderMonoid : (env : Type) -> PFMonoid (PFHomArena env)
PFReaderMonoid env = MkPFMonoid (PFReaderReturn env) (PFReaderJoin env)

public export
PFReaderMonad : Type -> PFMonad
PFReaderMonad env = (PFHomArena env ** PFReaderMonoid env)

----------------------
---- Either monad ----
----------------------

public export
PFEitherReturnOnPos : (a : Type) -> PFIdentityPos -> pfEitherPos a
PFEitherReturnOnPos a () = Left ()

public export
PFEitherReturnOnDir : (a : Type) -> (i : PFIdentityPos) ->
  pfEitherDir a (PFEitherReturnOnPos a i) -> PFIdentityDir i
PFEitherReturnOnDir a () () = ()

public export
PFEitherReturn : (a : Type) -> PolyNatTrans PFIdentityArena (pfEitherArena a)
PFEitherReturn a = (PFEitherReturnOnPos a ** PFEitherReturnOnDir a)

public export
PFEitherJoinOnPos : (a : Type) -> pfEitherComposePos a a -> pfEitherPos a
PFEitherJoinOnPos a (Left () ** d) = d ()
PFEitherJoinOnPos a (Right x ** d) = Right x

public export
PFEitherJoinOnDir : (a : Type) -> (i : pfEitherComposePos a a) ->
  pfEitherDir a (PFEitherJoinOnPos a i) -> pfEitherComposeDir a a i
PFEitherJoinOnDir a (Left () ** d) i with (d ()) proof deq
  PFEitherJoinOnDir a (Left () ** d) i | Left () = (() ** rewrite deq in ())
  PFEitherJoinOnDir a (Left () ** d) i | Right x = void i
PFEitherJoinOnDir a (Right x ** _) d = void d

public export
PFEitherJoin : (a : Type) ->
  PolyNatTrans (pfEitherComposeArena a a) (pfEitherArena a)
PFEitherJoin a = (PFEitherJoinOnPos a ** PFEitherJoinOnDir a)

public export
PFEitherMonoid : (a : Type) -> PFMonoid (pfEitherArena a)
PFEitherMonoid a = MkPFMonoid (PFEitherReturn a) (PFEitherJoin a)

public export
PFEitherMonad : Type -> PFMonad
PFEitherMonad a = (pfEitherArena a ** PFEitherMonoid a)

-----------------------
---- Product monad ----
-----------------------

public export
PFProductReturnOnPos : {p, q : PolyFunc} -> PFMonoid p -> PFMonoid q ->
  PFIdentityPos -> pfProductPos p q
PFProductReturnOnPos {p=(ppos ** pdir)} {q=(qpos ** qdir)}
  (MkPFMonoid (prOnPos ** prOnDir) (pjOnPos ** pjOnDir))
  (MkPFMonoid (qrOnPos ** qrOnDir) (qjOnPos ** qjOnDir)) () =
    (prOnPos (), qrOnPos ())

public export
PFProductReturnOnDir : {p, q : PolyFunc} ->
  (pmon : PFMonoid p) -> (qmon : PFMonoid q) ->
  (i : PFIdentityPos) ->
  pfProductDir p q (PFProductReturnOnPos pmon qmon i) -> PFIdentityDir i
PFProductReturnOnDir {p=(ppos ** pdir)} {q=(qpos ** qdir)}
  (MkPFMonoid (prOnPos ** prOnDir) (pjOnPos ** pjOnDir))
  (MkPFMonoid (qrOnPos ** qrOnDir) (qjOnPos ** qjOnDir)) () d =
    ()

public export
PFProductReturn : {p, q : PolyFunc} ->
  (pmon : PFMonoid p) -> (qmon : PFMonoid q) ->
  PolyNatTrans PFIdentityArena (pfProductArena p q)
PFProductReturn pmon qmon =
  (PFProductReturnOnPos pmon qmon ** PFProductReturnOnDir pmon qmon)

public export
PFProductJoinOnPos : {p, q : PolyFunc} -> PFMonoid p -> PFMonoid q ->
  pfCompositionPos (pfProductArena p q) (pfProductArena p q) ->
  pfProductPos p q
PFProductJoinOnPos {p=(ppos ** pdir)} {q=(qpos ** qdir)}
  (MkPFMonoid (prOnPos ** prOnDir) (pjOnPos ** pjOnDir))
  (MkPFMonoid (qrOnPos ** qrOnDir) (qjOnPos ** qjOnDir))
  ((pi, qi) ** d) =
    (pjOnPos (pi ** fst . d . Left),
     qjOnPos (qi ** snd . d . Right))

public export
PFProductJoinOnDir : {p, q : PolyFunc} ->
  (pmon : PFMonoid p) -> (qmon : PFMonoid q) ->
  (i : pfCompositionPos (pfProductArena p q) (pfProductArena p q)) ->
  pfProductDir p q (PFProductJoinOnPos pmon qmon i) ->
  pfCompositionDir (pfProductArena p q) (pfProductArena p q) i
PFProductJoinOnDir {p=(ppos ** pdir)} {q=(qpos ** qdir)}
  (MkPFMonoid (prOnPos ** prOnDir) (pjOnPos ** pjOnDir))
  (MkPFMonoid (qrOnPos ** qrOnDir) (qjOnPos ** qjOnDir))
  ((pi, qi) ** di) (Left dl)
    with (di $ Left $ fst $ pjOnDir (pi ** fst . di . Left) dl) proof prf
      PFProductJoinOnDir {p=(ppos ** pdir)} {q=(qpos ** qdir)}
        (MkPFMonoid (prOnPos ** prOnDir) (pjOnPos ** pjOnDir))
        (MkPFMonoid (qrOnPos ** qrOnDir) (qjOnPos ** qjOnDir))
        ((pi, qi) ** di) (Left dl) | (pil, qil) =
          (Left (fst (pjOnDir (pi ** fst . di . Left) dl)) **
           rewrite prf in
           rewrite sym (cong fst prf) in
           Left $ snd $ pjOnDir (pi ** fst . di . Left) dl)
PFProductJoinOnDir {p=(ppos ** pdir)} {q=(qpos ** qdir)}
  (MkPFMonoid (prOnPos ** prOnDir) (pjOnPos ** pjOnDir))
  (MkPFMonoid (qrOnPos ** qrOnDir) (qjOnPos ** qjOnDir))
  ((pi, qi) ** di) (Right dr)
    with (di $ Right $ fst $ qjOnDir (qi ** snd . di . Right) dr) proof prf
      PFProductJoinOnDir {p=(ppos ** pdir)} {q=(qpos ** qdir)}
        (MkPFMonoid (prOnPos ** prOnDir) (pjOnPos ** pjOnDir))
        (MkPFMonoid (qrOnPos ** qrOnDir) (qjOnPos ** qjOnDir))
        ((pi, qi) ** di) (Right dr) | (pir, qir) =
          (Right (fst (qjOnDir (qi ** snd . di . Right) dr)) **
           rewrite prf in
           rewrite sym (cong snd prf) in
           Right $ snd $ qjOnDir (qi ** snd . di . Right) dr)

public export
PFProductJoin : {p, q : PolyFunc} ->
  (pmon : PFMonoid p) -> (qmon : PFMonoid q) ->
  PolyNatTrans
    (pfCompositionArena (pfProductArena p q) (pfProductArena p q))
    (pfProductArena p q)
PFProductJoin pmon qmon =
  (PFProductJoinOnPos pmon qmon ** PFProductJoinOnDir pmon qmon)

--------------------
---- Free monad ----
--------------------

public export
PFFreeReturnOnPos : (p : PolyFunc) -> PFIdentityPos -> PolyFuncFreeMPos p
PFFreeReturnOnPos (pos ** dir) () = InPFM (PFVar ()) (voidF _)

public export
PFFreeReturnOnDir : (p : PolyFunc) -> (i : PFIdentityPos) ->
  PolyFuncFreeMDir p (PFFreeReturnOnPos p i) -> PFIdentityDir i
PFFreeReturnOnDir (pos ** dir) () () = ()

public export
PFFreeReturn : (p : PolyFunc) -> PolyNatTrans PFIdentityArena (PolyFuncFreeM p)
PFFreeReturn p = (PFFreeReturnOnPos p ** PFFreeReturnOnDir p)

public export PolyFuncFreeMJoinOnPosCurried : (p : PolyFunc) ->
  (i : PolyFuncFreeMPos p) -> (PolyFuncFreeMDir p i -> PolyFuncFreeMPos p) ->
  PolyFuncFreeMPos p
PolyFuncFreeMJoinOnPosCurried (pos ** dir) (InPFM (PFVar ()) d) f = f ()
PolyFuncFreeMJoinOnPosCurried (pos ** dir) (InPFM (PFCom i) d) f =
  InPFM (PFCom i) $
    \di =>
      PolyFuncFreeMJoinOnPosCurried (pos ** dir) (d di) $
        \dirc => f (di ** dirc)

public export
PFFreeJoinOnPos : (p : PolyFunc) -> pfFreeComposePos p p -> PolyFuncFreeMPos p
PFFreeJoinOnPos p (i ** f) = PolyFuncFreeMJoinOnPosCurried p i f

public export
PFFreeJoinOnDir : (p : PolyFunc) -> (i : pfFreeComposePos p p) ->
  PolyFuncFreeMDir p (PFFreeJoinOnPos p i) -> pfFreeComposeDir p p i
PFFreeJoinOnDir p@(_ ** _) ((InPFM (PFVar ()) d') ** f) di = (() ** di)
PFFreeJoinOnDir p@(_ ** _) ((InPFM (PFCom i') d') ** f) (di ** pfc) =
  let r = PFFreeJoinOnDir p ((d' di) ** \pfcf => (f (di ** pfcf))) pfc in
  ((di ** (fst r)) ** snd r)

public export
PFFreeJoin : (p : PolyFunc) ->
  PolyNatTrans (pfFreeComposeArena p p) (PolyFuncFreeM p)
PFFreeJoin p = (PFFreeJoinOnPos p ** PFFreeJoinOnDir p)

public export
PFFreeMonoid : (p : PolyFunc) -> PFMonoid (PolyFuncFreeM p)
PFFreeMonoid p = MkPFMonoid (PFFreeReturn p) (PFFreeJoin p)

public export
PFFreeMonad : PolyFunc -> PFMonad
PFFreeMonad p = (PolyFuncFreeM p ** PFFreeMonoid p)

public export
interpFreeMJoin : {p : PolyFunc} ->
  NaturalTransformation
    (InterpPolyFunc (PolyFuncFreeM p) . InterpPolyFunc (PolyFuncFreeM p))
    (InterpPolyFunc (PolyFuncFreeM p))
interpFreeMJoin {p} x =
  InterpPolyNT
    {p=(pfFreeComposeArena p p)} {q=(PolyFuncFreeM p)}
    (PFFreeJoin p)
    x .
  pfComposeInterp {q=(PolyFuncFreeM p)} {p=(PolyFuncFreeM p)} {x}

public export
pfFreeToComposeN : (p : PolyFunc) -> (n : Nat) ->
  PolyNatTrans
    (PolyFuncFreeM p)
    (pfCompositionPowerArenaS (PolyFuncFreeM p) n)
pfFreeToComposeN (pos ** dir) Z = pntId (PolyFuncFreeM (pos ** dir))
pfFreeToComposeN (pos ** dir) (S n) =
  let
    retn =
      pntVCatComp
        {p=(PolyFuncFreeM (pos ** dir))}
        {q=(pfCompositionPowerArenaS (PolyFuncFreeM (pos ** dir)) n)}
        {r=(pfCompositionArena
          PFIdentityArena
          (pfCompositionPowerArenaS (PolyFuncFreeM (pos ** dir)) n))}
        (pntToIdLeft
          (pfCompositionPowerArenaS (PolyFuncFreeM (pos ** dir)) n))
        (pfFreeToComposeN (pos ** dir) n)
    n2S = polyWhiskerLeft
      {p=PFIdentityArena}
      {q=(PolyFuncFreeM (pos ** dir))}
      (PFFreeReturn (pos ** dir))
      (pfCompositionPowerArenaS (PolyFuncFreeM (pos ** dir)) n)
    ret = pntVCatComp
      {p=(PolyFuncFreeM (pos ** dir))}
      {q=(pfCompositionArena
        PFIdentityArena
        (pfCompositionPowerArenaS (PolyFuncFreeM (pos ** dir)) n))}
      {r=(pfCompositionArena
        (PolyFuncFreeM (pos ** dir))
        (pfCompositionPowerArenaS (PolyFuncFreeM (pos ** dir)) n))}
      n2S
      retn
    in
    ret

public export
0 pfFreeFromComposeN : (p : PolyFunc) -> (n : Nat) ->
  PolyNatTrans
    (pfCompositionPowerArenaS (PolyFuncFreeM p) n)
    (PolyFuncFreeM p)
pfFreeFromComposeN (pos ** dir) Z = pntId $ PolyFuncFreeM (pos ** dir)
pfFreeFromComposeN (pos ** dir) (S n) =
  let
    sS2S = polyWhiskerLeft
      {p=(pfFreeComposeArena (pos ** dir) (pos ** dir))}
      {q=(PolyFuncFreeM (pos ** dir))}
      (PFFreeJoin (pos ** dir))
      (pfCompositionPowerArena (PolyFuncFreeM (pos ** dir)) n)
    ret = pntVCatComp
      {p=(pfCompositionPowerArenaS (PolyFuncFreeM (pos ** dir)) (S n))}
      {q=(pfCompositionPowerArenaS (PolyFuncFreeM (pos ** dir)) n)}
      {r=(PolyFuncFreeM (pos ** dir))}
      (pfFreeFromComposeN (pos ** dir) n)
      ?from_compose_sS2S_hole
      {-
      (pntAssociateComposeL
        {p=(PolyFuncFreeM (pos ** dir))}
        {q=(PolyFuncFreeM (pos ** dir))}
        {r=(pfCompositionPowerArena (PolyFuncFreeM (pos ** dir)) n)}
        {s=(pfCompositionPowerArenaS (PolyFuncFreeM (pos ** dir)) n)}
        from_compose_sS2S_hole
      -}
  in
  ret

public export
0 pfFreePolyReturnN : (p : PolyFunc) -> (n : Nat) ->
  PolyNatTrans
    (PolyFuncFreeM p)
    (PolyFuncFreeM (pfCompositionPowerArenaS p n))
pfFreePolyReturnN p Z = pntId $ PolyFuncFreeM p
pfFreePolyReturnN p (S n) = ?pfFreePolyReturnN_hole_1

public export
0 pfFreePolyJoinN : (p : PolyFunc) -> (n : Nat) ->
  PolyNatTrans
    (PolyFuncFreeM (pfCompositionPowerArenaS p n))
    (PolyFuncFreeM p)
pfFreePolyJoinN p Z = pntId $ PolyFuncFreeM p
pfFreePolyJoinN p (S n) = ?pfFreePolyJoinN_hole_1

public export
pfNatTransMN : PolyFunc -> PolyFunc -> Nat -> Nat -> Type
pfNatTransMN p q m n =
  PolyNatTrans (pfCompositionPowerArenaS p m) (pfCompositionPowerArenaS q n)

public export
0 pfFreePolyCataN : {p, q : PolyFunc} -> {n : Nat} ->
  pfNatTransMN p q n n ->
  PolyNatTrans (PolyFuncFreeM p) (PolyFuncFreeM q)
pfFreePolyCataN {p} {q} {n} alpha =
  pntVCatComp
    {p=(PolyFuncFreeM p)}
    {q=(PolyFuncFreeM (pfCompositionPowerArenaS q n))}
    {r=(PolyFuncFreeM q)}
    (pfFreePolyJoinN q n)
    (pntVCatComp
      {p=(PolyFuncFreeM p)}
      {q=(PolyFuncFreeM (pfCompositionPowerArenaS p n))}
      {r=(PolyFuncFreeM (pfCompositionPowerArenaS q n))}
      (pfFreePolyCata alpha)
      (pfFreePolyReturnN p n))

public export
0 pfPolyCataN : {p, q : PolyFunc} -> {n : Nat} ->
  PolyNatTrans
    (pfCompositionPowerArenaS p n)
    (pfCompositionPowerArenaS q n) ->
  PolyFuncMu p -> PolyFuncMu q
pfPolyCataN {p} {q} {n} alpha =
  let
    alphaN = pfFreePolyCataN {p} {q} {n} alpha
    alphaNint =
      InterpPolyNT {p=(PolyFuncFreeM p)} {q=(PolyFuncFreeM q)} alphaN Void
  in
  pfFreeMVoidToMu {p=q} . alphaNint . pfMuToFreeMVoid {p}

public export
0 pfFreeContCata : {p, q : PolyFunc} ->
  PolyContNT p q ->
  PolyContNT (PolyFuncFreeM p) (PolyFuncFreeM q)
pfFreeContCata {p=p@(ppos ** pdir)} {q=q@(qpos ** qdir)} cont x =
  ?pfFreeContCata_hole

-------------------------
---- Codensity monad ----
-------------------------

------------------------
---- Cofree comonad ----
------------------------

------------------------------------
---- Writer Nat (Free Identity) ----
------------------------------------

public export
pfFreeId : PolyFunc
pfFreeId = PolyFuncFreeM PFIdentityArena

public export
pfFreeIdF : Type -> Type
pfFreeIdF = InterpPolyFunc pfFreeId

-------------------------------------------
---- Infinite stream (Cofree Identity) ----
-------------------------------------------

public export
pfCofreeId : PolyFunc
pfCofreeId = PolyFuncCofreeCM PFIdentityArena

public export
pfCofreeIdF : Type -> Type
pfCofreeIdF = InterpPolyFunc pfCofreeId

-------------------------
---- Density comonad ----
-------------------------

public export
0 PFDensityComonoid : (p : PolyFunc) -> PFComonoid (PolyDensityComonad p)
PFDensityComonoid p = ?PFDensityComonoid_hole

public export
0 PFDensityComonad : PolyFunc -> PFComonad
PFDensityComonad p = (PolyDensityComonad p ** PFDensityComonoid p)

public export
0 PFDensityComonadCorrect : (p : PolyFunc) ->
  PFComonoidCorrect (PolyDensityComonad p) (PFDensityComonoid p)
PFDensityComonadCorrect p = ?PFDensityComonadCorrect_hole

-------------------------------------
-------------------------------------
---- Density comonad as category ----
-------------------------------------
-------------------------------------

public export
pfToCat : PolyFunc -> CatSig
pfToCat (ppos ** pdir) =
  MkCatSig
    ppos
    (\x, y => pdir y -> pdir x)
    (\a, b => ExtEq)
    (\_ => id)
    (\f, g => g . f)

public export
0 densityToCat : PolyFunc -> CatSig
densityToCat p = ComonadToCat (PFDensityComonad p) (PFDensityComonadCorrect p)

public export
0 pfDensityToCatConsistent : (p : PolyFunc) -> FunExt ->
  pfToCat p = densityToCat p
pfDensityToCatConsistent (ppos ** pdir) funext with
  (PolyDensityComonad (ppos ** pdir)) proof prf
    pfDensityToCatConsistent (ppos ** pdir) funext | (dcpos ** dcdir) =
      let
        fsteq = mkDPairInjectiveFst prf
        sndeq = mkDPairInjectiveSndHet prf
      in
      ?pfDensityToCatConsistent_hole

-----------------------------------
-----------------------------------
---- Polynomial Kan extensions ----
-----------------------------------
-----------------------------------

public export
InterpPolyLKan : (p, q : PolyFunc) -> (a : Type) ->
  InterpPolyFunc (PolyLKanExt q p) a ->
  LKanExt (InterpPolyFunc q) (InterpPolyFunc p) a
InterpPolyLKan (ppos ** pdir) (qpos ** qdir) a (i ** f) =
  (pdir i ** (f, (i ** id)))

public export
InterpLKanPoly : (p, q : PolyFunc) -> (a : Type) ->
  LKanExt (InterpPolyFunc q) (InterpPolyFunc p) a ->
  InterpPolyFunc (PolyLKanExt q p) a
InterpLKanPoly (ppos ** pdir) (qpos ** qdir) a (b ** (f, (i ** d))) =
  (i ** \(qi ** qpd) => f (qi ** d . qpd))

---------------------------------------
---------------------------------------
---- Dependent polynomial functors ----
---------------------------------------
---------------------------------------

-----------------------------------------------------------
---- Refined versions of dependent polynomial functors ----
-----------------------------------------------------------

public export
RefinedDepProdF : {a : Refined} ->
  (p : RefinedSlice a) -> SliceFunctor (RefinedSigmaType {a} p) (RefinedType a)
RefinedDepProdF {a} p =
  PredDepProdF {a=(RefinedType a)} (RefinedType . p) .
    BaseChangeF RefinedDPairToSigma

public export
RefinedDepCoprodF : {a : Refined} ->
  (p : RefinedSlice a) -> SliceFunctor (RefinedSigmaType {a} p) (RefinedType a)
RefinedDepCoprodF {a} p =
  PredDepCoprodF {a=(RefinedType a)} (RefinedType . p) .
    BaseChangeF RefinedDPairToSigma

public export
RefinedDepPolyF : {parambase, posbase : Refined} ->
  (posdep : RefinedSlice posbase) ->
  (dirdep : RefinedSlice (RefinedSigma {a=posbase} posdep)) ->
  (assign :
    RefinedSigmaType {a=(RefinedSigma {a=posbase} posdep)} dirdep ->
    RefinedType parambase) ->
  RefinedSliceFunctorType parambase posbase
RefinedDepPolyF {parambase} {posbase} posdep dirdep assign =
  RefinedDepCoprodF {a=posbase} posdep
  . RefinedDepProdF {a=(RefinedSigma {a=posbase} posdep)} dirdep
  . BaseChangeF assign

public export
RefinedDepPolyEndoF : {base : Refined} ->
  (posdep : RefinedSlice base) ->
  (dirdep : RefinedSlice (RefinedSigma {a=base} posdep)) ->
  (assign :
    RefinedSigmaType {a=(RefinedSigma {a=base} posdep)} dirdep ->
    RefinedType base) ->
  RefinedSliceFunctorType base base
RefinedDepPolyEndoF {base} = RefinedDepPolyF {parambase=base} {posbase=base}

--------------------------------------------------------------------
---- Dependent polynomials as functors between slice categories ----
--------------------------------------------------------------------

public export
SlicePolyFunc : Type -> Type -> Type
SlicePolyFunc parambase posbase =
  (posdep : SliceObj posbase **
   dirdep : SliceObj (Sigma posdep) **
   Sigma dirdep -> parambase)

-- An equivalent way of specifying a `SlicePolyFunc`.
public export
SlicePolyFunc' : Type -> Type -> Type
SlicePolyFunc' parambase posbase =
  (posdep : SliceObj posbase **
   Sigma posdep -> (dirdep : Type ** dirdep -> parambase))

public export
SPFFromPrime : {parambase, posbase : Type} ->
  SlicePolyFunc' parambase posbase -> SlicePolyFunc parambase posbase
SPFFromPrime (posdep ** dirdep) =
  (posdep ** fst . dirdep ** \(i ** d) => snd (dirdep i) d)

public export
SPFToPrime : {parambase, posbase : Type} ->
  SlicePolyFunc parambase posbase -> SlicePolyFunc' parambase posbase
SPFToPrime (posdep ** dirdep ** assign) =
  (posdep ** \i => (dirdep i ** \d => assign (i ** d)))

-- Another equivalent way of specifying a `SlicePolyFunc`.
public export
SlicePolyFunc'' : Type -> Type -> Type
SlicePolyFunc'' parambase posbase =
  (posdep : SliceObj posbase ** Sigma posdep -> SliceObj parambase)

public export
SlicePolyEndoFunc'' : Type -> Type
SlicePolyEndoFunc'' base = SlicePolyFunc'' base base

public export
SPFFromPrimes : {parambase, posbase : Type} ->
  SlicePolyFunc'' parambase posbase -> SlicePolyFunc parambase posbase
SPFFromPrimes (posdep ** dirdep) =
  (posdep ** Sigma {a=parambase} . dirdep ** \i => DPair.fst $ DPair.snd i)

public export
SPFToPrimes : {parambase, posbase : Type} ->
  (spf : SlicePolyFunc parambase posbase) ->
  SlicePolyFunc'' (SliceObj parambase) (Sigma (fst spf))
SPFToPrimes (posdep ** dirdep ** assign) =
  (dirdep ** \ipos, paramslice => paramslice $ assign ipos)

public export
SPFToPrimes' : {dom, cod : Type} ->
  SlicePolyFunc dom cod -> SlicePolyFunc'' dom cod
SPFToPrimes' (pos ** dir ** assign) =
  (pos ** \p, eld => Subset0 (dir p) (\d => Equal (assign (p ** d)) eld))

-- Yet another equivalent way of specifying a SlicePolyFunc.
public export
DepParamPolyFunc : Type -> Type -> Type
DepParamPolyFunc parambase posbase =
  Sigma {a=(SliceObj posbase)}
    (\posslice => Sigma posslice -> (parambase, Type))

public export
SPFFromDPPF : {parambase, posbase : Type} ->
  DepParamPolyFunc parambase posbase -> SlicePolyFunc parambase posbase
SPFFromDPPF {parambase} {posbase} (posslice ** assign) =
  (posslice ** snd . assign ** fst . assign . fst)

public export
SlicePolyEndoFunc : Type -> Type
SlicePolyEndoFunc base = SlicePolyFunc base base

public export
SlicePolyEndoFuncId : Type -> Type
SlicePolyEndoFuncId base = DPair (SliceObj base) (SliceObj . Sigma)

public export
SlicePolyIdAlternates : {base : Type} ->
  SlicePolyEndoFuncId base -> SlicePolyEndoFunc'' base
SlicePolyIdAlternates {base} (posdep ** dirdep) =
  (posdep ** \d, _ => dirdep d)

public export
SlicePolyIdAlternates' : {base : Type} ->
  SlicePolyEndoFunc'' base -> SlicePolyEndoFuncId base
SlicePolyIdAlternates' {base} (posdep ** dirdep) =
  (posdep ** \(i ** d) => dirdep (i ** d) i)

public export
SlicePolyEndoFuncFromId : {base : Type} ->
  SlicePolyEndoFuncId base -> SlicePolyEndoFunc base
SlicePolyEndoFuncFromId {base} (posdep ** dirdep) =
  (posdep ** dirdep ** fst . fst)

-- Another way of looking at the `EndoFuncId` special case of `SlicePolyFunc`
-- is that it represents a parameterized polynomial functor.  The type of
-- the parameter becomes the object whose slice category the dependent
-- polynomial functor is an endofunctor on.
public export
ParamPolyFunc : Type -> Type
ParamPolyFunc x = x -> PolyFunc

public export
ParamPolyFuncToSliceEndoId : {base : Type} ->
  ParamPolyFunc base -> SlicePolyEndoFuncId base
ParamPolyFuncToSliceEndoId {base} p =
  (DPair.fst . p ** \(i ** j) => snd (p i) j)

public export
SlicePolyEndoFuncIdToPolyFunc : {base : Type} ->
  SlicePolyEndoFuncId base -> PolyFunc
SlicePolyEndoFuncIdToPolyFunc {base} (posdep ** dirdep) =
  (Sigma {a=base} posdep ** dirdep)

-- A polynomial endofunctor in the product category `Type^n`.
public export
ProductPolyEndoFuncId : Nat -> Type
ProductPolyEndoFuncId = SlicePolyEndoFuncId . Fin

public export
ParamPolyFuncToPolyFunc : {base : Type} -> ParamPolyFunc base -> PolyFunc
ParamPolyFuncToPolyFunc {base} ppf =
  ((i : base ** fst (ppf i)) ** \(i ** j) => snd (ppf i) j)

public export
ParamPolyFuncFromSliceEndoId : {base : Type} ->
  SlicePolyEndoFuncId base -> ParamPolyFunc base
ParamPolyFuncFromSliceEndoId {base} (posdep ** dirdep) i =
  (posdep i ** \pi => dirdep (i ** pi))

public export
RefinedPolyFunc : Refined -> Refined -> Type
RefinedPolyFunc parambase posbase =
  (posdep : RefinedSlice posbase **
   dirdep : RefinedSlice (RefinedSigma {a=posbase} posdep) **
   RefinedSigmaType {a=(RefinedSigma {a=posbase} posdep)} dirdep ->
    RefinedType parambase)

public export
RPFToSPF : {parambase, posbase : Refined} ->
  RefinedPolyFunc parambase posbase ->
  SlicePolyFunc (RefinedType parambase) (RefinedType posbase)
RPFToSPF {parambase} {posbase} (posdep ** dirdep ** assign) =
  (RefinedType . posdep **
   BaseChangeF RefinedDPairToSigma (RefinedType . dirdep) **
   assign .
    (\x =>
      Element0
        (RefinedDPairToSigma (fst x) ** (fst0 (snd x)))
        (Subset0.snd0 (snd x))))

public export
RefinedPolyEndoFunc : Refined -> Type
RefinedPolyEndoFunc base = RefinedPolyFunc base base

public export
spfPos : {0 a, b : Type} -> SlicePolyFunc a b -> SliceObj b
spfPos = fst

public export
spfDir : {0 a, b : Type} ->
  (spf : SlicePolyFunc a b) -> SliceObj (Sigma (spfPos spf))
spfDir spf = fst (snd spf)

public export
spfSliceDir : {0 a, b : Type} ->
  (spf : SlicePolyFunc a b) -> (eb : b) -> spfPos spf eb -> Type
spfSliceDir spf eb i = spfDir spf (eb ** i)

public export
spfAssign : {0 a, b : Type} ->
  (spf : SlicePolyFunc a b) -> Sigma (spfDir spf) -> a
spfAssign spf = snd (snd spf)

public export
rpfPos : {0 a, b : Refined} -> RefinedPolyFunc a b -> RefinedSlice b
rpfPos = fst

public export
rpfDir : {0 a, b : Refined} ->
  (rpf : RefinedPolyFunc a b) ->
  RefinedSlice (RefinedSigma {a=b} (rpfPos {a} {b} rpf))
rpfDir rpf = fst (snd rpf)

public export
rpfAssign : {0 a, b : Refined} ->
  (rpf : RefinedPolyFunc a b) ->
  RefinedSigmaType
    {a=(RefinedSigma {a=b} (rpfPos {a} {b} rpf))}
    (rpfDir {a} {b} rpf) ->
  RefinedType a
rpfAssign rpf = snd (snd rpf)

public export
InterpSPFunc : {a, b : Type} ->
  SlicePolyFunc a b -> SliceFunctor a b
InterpSPFunc spf = PredDepPolyF (spfPos spf) (spfDir spf) (spfAssign spf)

public export
InterpRPFunc : {a, b : Refined} ->
  RefinedPolyFunc a b -> RefinedSliceFunctorType a b
InterpRPFunc rpf = RefinedDepPolyF (rpfPos rpf) (rpfDir rpf) (rpfAssign rpf)

public export
InterpSPFMap : {a, b : Type} -> (spf : SlicePolyFunc a b) ->
  {sa, sa' : SliceObj a} ->
  SliceMorphism sa sa' ->
  SliceMorphism (InterpSPFunc spf sa) (InterpSPFunc spf sa')
InterpSPFMap {a} {b} spf {sa} {sa'} =
  PredDepPolyFMap
    {parambase=a} {posbase=b} (spfPos spf) (spfDir spf) (spfAssign spf) sa sa'

-- Yet another formulation of dependent polynomial functors.
public export
SliceGenPF : Type -> Type -> Type
SliceGenPF dom cod = (pos : SliceObj cod ** SliceObj (dom, Sigma pos))

public export
SGPFtoSPF : {dom, cod : Type} -> SliceGenPF dom cod -> SlicePolyFunc dom cod
SGPFtoSPF {dom} {cod} (pos ** dir) =
  (pos ** Sigma {a=dom} . flip (curry dir) ** \i => fst $ snd $ i)

public export
SPFtoSGPF : {dom, cod : Type} -> SlicePolyFunc dom cod -> SliceGenPF dom cod
SPFtoSGPF {dom} {cod} (pos ** dir ** assign) =
  (pos ** \(i, j) => Subset0 (dir j) $ \d => Equal (assign (j ** d)) i)

------------------------------------------------------------------------
------------------------------------------------------------------------
---- Generalized-polynomial-functor-style slice polynomial functors ----
------------------------------------------------------------------------
------------------------------------------------------------------------

-- `SlicePolyFunc''`, but with field names.
public export
record SliceArena (dom, cod : Type) where
  constructor SlAr
  SLApos : SliceObj cod
  SLAdir : Sigma {a=cod} SLApos -> SliceObj dom

public export
SliceEndoArena : Type -> Type
SliceEndoArena base = SliceArena base base

public export
SLAPomap : {dom : Type} -> {0 cod : Type} ->
  SliceArena dom cod -> SliceFunctor dom cod
SLAPomap {dom} {cod} ar sl j =
  (p : SLApos ar j ** SliceMorphism {a=dom} (SLAdir ar (j ** p)) sl)

public export
SLAPfmap : {dom : Type} -> {0 cod : Type} ->
  (ar : SliceArena dom cod) ->
  {a, b : SliceObj dom} ->
  SliceMorphism {a=dom} a b ->
  SliceMorphism {a=cod} (SLAPomap {dom} {cod} ar a) (SLAPomap {dom} {cod} ar b)
SLAPfmap {dom} {cod} ar {a} {b} m elcod elmap =
  (fst elmap ** sliceComp m $ snd elmap)

public export
SlArToPrimes : {0 dom, cod : Type} ->
  SliceArena dom cod -> SlicePolyFunc'' dom cod
SlArToPrimes {dom} {cod} ar = (SLApos ar ** SLAdir ar)

public export
SlArFromPrimes : {0 dom, cod : Type} ->
  SlicePolyFunc'' dom cod -> SliceArena dom cod
SlArFromPrimes {dom} {cod} spf = SlAr (fst spf) (snd spf)

public export
SlArToSPF : {dom, cod : Type} ->
  SliceArena dom cod -> SlicePolyFunc dom cod
SlArToSPF = SPFFromPrimes . SlArToPrimes

public export
SlArFromSPF : {dom, cod : Type} ->
  SlicePolyFunc dom cod -> SliceArena dom cod
SlArFromSPF = SlArFromPrimes . SPFToPrimes'

-----------------------------------------------------
-----------------------------------------------------
---- Parameterized dependent polynomial functors ----
-----------------------------------------------------
-----------------------------------------------------

public export
ParamSPF : {a : Type} -> (x, y : SliceObj a) -> Type
ParamSPF {a} x y = (ea : a) -> SlicePolyFunc (x ea) (y ea)

public export
SPFFromParam : {0 a : Type} -> {0 x, y : SliceObj a} ->
  ParamSPF {a} x y -> SlicePolyFunc (Sigma {a} x) (Sigma {a} y)
SPFFromParam {a} {x} {y} pspf =
  (\iy => fst (pspf (fst iy)) (snd iy) **
   \dp => fst (snd (pspf (fst (fst dp)))) (snd (fst dp) ** (snd dp)) **
   \dd =>
    (fst (fst (fst dd)) **
     snd
      (snd (pspf (DPair.fst (fst (fst dd)))))
      ((snd (fst (fst dd)) ** snd (fst dd)) ** snd dd)))

public export
SPFToParam : {0 a : Type} -> {0 x, y : SliceObj a} ->
  SlicePolyFunc (Sigma {a} x) (Sigma {a} y) ->
  ParamSPF {a} x y
SPFToParam {a} {x} {y} (posdep ** dirdep ** assign) ea =
  (posdep . MkDPair ea **
   \pd =>
    (dd : dirdep ((ea ** fst pd) ** snd pd) **
     fst (assign (((ea ** fst pd) ** snd pd) ** dd)) = ea) **
   \((yea ** pd) ** (dd ** eq)) =>
    replace {p=x} eq $ snd $ assign (((ea ** yea) ** pd) ** dd))

-- Given a parameterized dependent polynomial functor, we can extend its
-- domain and codomain slices by pairing them with a third slice.
public export
ParamSPFProd : {a : Type} -> {x, y, z : SliceObj a} ->
  ParamSPF {a} x y -> ParamSPF {a} (SliceProduct x z) (SliceProduct y z)
ParamSPFProd {a} {x} {y} {z} pspf ea =
  (fst (pspf ea) . fst **
   \((yea, zea) ** pyea) => fst (snd (pspf ea)) (yea ** pyea) **
   \(((yea, zea) ** pyea) ** ppyea) =>
    (snd (snd (pspf ea)) ((yea ** pyea) ** ppyea), zea))

---------------------------------------------------------------
---------------------------------------------------------------
---- Various categories of (dependent) polynomial functors ----
---------------------------------------------------------------
---------------------------------------------------------------

-------------------
---- As `Poly` ----
-------------------

-- We may view dependent polynomial functors as non-dependent endofunctors
-- in the category `Poly` on `(Fin)ADT`.  In this view, the domain slice
-- is the object of positions of the corresponding non-dependent functor,
-- and the codomain slice is erased.

-- The initial object of `Poly`, viewed as a dependent endofunctor.
-- Equivalently, this is the unique morphism out of the initial object
-- in the category of slice categories (i.e., the two-category whose objects
-- are slice categories of `(Fin)ADT` and whose morphisms are dependent
-- polynomial endofunctors).
public export
SPFPolyInitial : (z : Type) -> SlicePolyFunc Void z
SPFPolyInitial z = (const Void ** const Void ** \x => void $ snd x)

-- The terminal object of `Poly`, viewed as a dependent endofunctor.
-- Equivalently, this is the unique morphism into the terminal object
-- in the category of slice categories (i.e., the two-category whose objects
-- are slice categories of `(Fin)ADT` and whose morphisms are dependent
-- polynomial endofunctors).
public export
SPFPolyTerminal : (y : Type) -> SlicePolyFunc y ()
SPFPolyTerminal y = (const Unit ** const Void ** \x => void $ snd x)

-- A coproduct in `Poly`, which produces, given two dependent functors,
-- a functor whose domain and codomain are the coproducts of the domains
-- and codomains of the given functors.
public export
SPFPolyCoprod : {0 w, x, y, z : Type} ->
  SlicePolyFunc w x -> SlicePolyFunc y z ->
  SlicePolyFunc (Either w y) (Either x z)
SPFPolyCoprod {w} {x} {y} {z} (wxp ** wxd ** wxa) (yzp ** yzd ** yza) =
  (\ixz => (case ixz of Left ix => wxp ix ; Right iz => yzp iz) **
   \(ixz ** wxyzi) => (case ixz of
      Left ix => wxd (ix ** wxyzi)
      Right iz => yzd (iz ** wxyzi)) **
   \((ixz ** wxyzi) ** wxyzdi) => (case ixz of
      Left ix => Left $ wxa ((ix ** wxyzi) ** wxyzdi)
      Right iz => Right $ yza ((iz ** wxyzi) ** wxyzdi)))

-- A product in `Poly`, which produces, given two dependent functors,
-- a functor whose domain is the coproduct of the domains of the given functors,
-- and whose codomain is the product of the codomains of the given functors.
public export
SPFPolyProd : {0 w, x, y, z : Type} ->
  SlicePolyFunc w x -> SlicePolyFunc y z -> SlicePolyFunc (Either w y) (x, z)
SPFPolyProd {w} {x} {y} {z} (wxp ** wxd ** wxa) (yzp ** yzd ** yza) =
  (\(ix, iz) => (wxp ix, yzp iz) **
   \((ix, iz) ** (wxi, yzi)) => Either (wxd (ix ** wxi)) (yzd (iz ** yzi)) **
   \(((ix, iz) ** (wxi, yzi)) ** wxyzdi) => (case wxyzdi of
      Left wxdi => Left $ wxa ((ix ** wxi) ** wxdi)
      Right yzdi => Right $ yza ((iz ** yzi) ** yzdi)))

-- A parallel product in `Poly`, which produces, given two dependent functors,
-- a functor whose domain and codomain are the products of the domains
-- and codomains of the given functors.
public export
SPFPolyParProd : {0 w, x, y, z : Type} ->
  SlicePolyFunc w x -> SlicePolyFunc y z -> SlicePolyFunc (w, y) (x, z)
SPFPolyParProd {w} {x} {y} {z} (wxp ** wxd ** wxa) (yzp ** yzd ** yza) =
  (\(ix, iz) => (wxp ix, yzp iz) **
   \((ix, iz) ** (wxi, yzi)) => (wxd (ix ** wxi), (yzd (iz ** yzi))) **
   \(((ix, iz) ** (wxi, yzi)) ** (wxdi, yzdi)) =>
      (wxa ((ix ** wxi) ** wxdi), yza ((iz ** yzi) ** yzdi)))

-- The identity endofunctor in `Poly`, which may also be viewed as the identity
-- endofunctor in any slice category (`spfId y` for any `y`).
public export
SPFPolyId : (y : Type) -> SlicePolyFunc y y
SPFPolyId y = (const Unit ** const Unit ** fst . fst)

public export
SPFConst : {y : Type} -> SliceObj y -> SlicePolyFunc y y
SPFConst {y} sl = (sl ** const Void ** \(_ ** v) => void v)

-- A (covariant) hom-functor in `Poly`, which may also be viewed as the same
-- hom-functor in any slice category (by precomposition).
public export
SPFPolyHom : (x, y : Type) -> SlicePolyFunc y y
SPFPolyHom x y = (const Unit ** const x ** fst . fst)

-- The diagonal functor which makes `y` copies of its input (and assigns
-- them all the parameter `ex`).
public export
SPFPolyDiag : (x, y : Type) -> x -> SlicePolyFunc x y
SPFPolyDiag x y ex = (const Unit ** const Unit ** const ex)

----------------------------------------------
---- As functors between slice categories ----
----------------------------------------------

-- Special dependent polynomial functors include base change, dependent
-- product, and dependent coproduct.  Also, pre- and post-composition of
-- base changes induce a profunctor structure (`dimap`).

public export
SPFBaseChange : {x, y : Type} -> (x -> y) -> SlicePolyFunc y x
SPFBaseChange {x} {y} f = (const () ** const () ** \ix => f (fst (fst ix)))

-- Right adjoint to `SPFBaseChange`.
public export
SPFDepProd : {a, b : Type} -> (0 _ : a -> b) -> SlicePolyFunc a b
SPFDepProd {a} {b} f =
  (const Unit ** \eb => PreImage f (fst eb) ** \dp => fst0 $ snd dp)

-- Left adjoint to `SPFBaseChange`.
public export
SPFDepCoprod : {a, b : Type} -> (0 _ : a -> b) -> SlicePolyFunc a b
SPFDepCoprod {a} {b} f =
  (\eb => PreImage f eb ** const Unit ** \dp => fst0 (snd (fst dp)))

-- A special case of `SPFDepProd` where `b` is `Unit` -- so that the
-- codomain of the functor is (isomorphic to) `Type`.
public export
SPFPi : (a : Type) -> SlicePolyFunc a ()
SPFPi a = (const Unit ** const a ** DPair.snd)

-- A special case of `SPFDepCoprod` where `b` is `Unit` -- so that the
-- codomain of the functor is (isomorphic to) `Type`.
public export
SPFSigma : (a : Type) -> SlicePolyFunc a ()
SPFSigma a = (const a ** const Unit ** DPair.snd . DPair.fst)

-- Precomposition and postcomposition by base change give `flip SlicePolyFunc`
-- itself a profunctor structure (`dimap`).
public export
SliceFuncDimap : {0 w, x, y, z : Type} ->
  flip SlicePolyFunc x w -> (z -> x) -> (w -> y) -> flip SlicePolyFunc z y
SliceFuncDimap {w} {x} {y} {z} (wxp ** wxd ** wxa) fzx fwy =
  (wxp . fzx **
   \izwxi => wxd (fzx (fst izwxi) ** snd izwxi) **
   \dd => fwy (wxa ((fzx (fst (fst dd)) ** snd (fst dd)) ** snd dd)))

public export
SliceFuncRmap : {0 w, x, y : Type} ->
  flip SlicePolyFunc x w -> (w -> y) -> flip SlicePolyFunc x y
SliceFuncRmap spf = SliceFuncDimap spf id

public export
SliceFuncLmap : {0 w, x, z : Type} ->
  flip SlicePolyFunc x w -> (z -> x) -> flip SlicePolyFunc z w
SliceFuncLmap spf = flip (SliceFuncDimap spf) id

public export
spfWeaken : {0 x, y : Type} -> SlicePolyFunc x Unit -> SlicePolyFunc x y
spfWeaken {x} {y} spf = SliceFuncLmap spf (const ())

--------------------------------------------------------------
---- As morphisms in the two-category of slice categories ----
--------------------------------------------------------------

public export
spfCoprodDom : {0 x, y, z : Type} ->
  SlicePolyFunc x z -> SlicePolyFunc y z ->
  SlicePolyFunc (Either x y) z
spfCoprodDom {x} {y} {z} (pd ** dd ** asn) (pd' ** dd' ** asn') =
  (\ez => Either (pd ez) (pd' ez) **
   \(ez ** pz) => (case pz of
    Left pz' => dd (ez ** pz')
    Right pz' => dd' (ez ** pz')) **
   \((ez ** pz) ** dz) => (case pz of
    Left pz' => Left (asn ((ez ** pz') ** dz))
    Right pz' => Right (asn' ((ez ** pz') ** dz))))

public export
spfCoprodCod : {0 x, y, z : Type} ->
  SlicePolyFunc x y -> SlicePolyFunc x z ->
  SlicePolyFunc x (Either y z)
spfCoprodCod {x} {y} {z} (pd ** dd ** asn) (pd' ** dd' ** asn') =
  (\e => case e of Left ey => pd ey ; Right ez => pd' ez **
   \(e ** i) => case e of Left ey => dd (ey ** i); Right ez => dd' (ez ** i) **
   \((e ** i) ** d) => case e of
    Left ey => asn ((ey ** i) ** d)
    Right ez => asn' ((ez ** i) ** d))

---------------------------------------------
---- As endofunctors on slice categories ----
---------------------------------------------

-- For a given `x`, the endofunctor category `SlicePolyEndoFunc x` is
-- a topos, so in particular it has the same structure of finite products
-- and coproducts as `Poly`.

-- The initial object in the category of polynomial endofunctors on
-- the slice category `Type/x`.
public export
SPFSliceInitial : (x : Type) -> SlicePolyEndoFunc x
SPFSliceInitial x =
  (const Void ** \x => void (snd x) ** \x => void $ snd $ fst x)

-- The terminal object in the category of polynomial endofunctors on
-- the slice category `Type/x`.
public export
SPFSliceTerminal : (x : Type) -> SlicePolyEndoFunc x
SPFSliceTerminal x = (const Unit ** const Void ** \d => void $ snd d)

public export
SPFSliceCoproduct : {x, y : Type} ->
  SlicePolyFunc x y -> SlicePolyFunc x y -> SlicePolyFunc x y
SPFSliceCoproduct {x} {y} (pd ** dd ** asn) (pd' ** dd' ** asn') =
  (\i => Either (pd i) (pd' i) **
   \(i ** d) => (case d of
    Left d' => dd (i ** d')
    Right d' => dd' (i ** d')) **
   \((i ** d) ** dd) => (case d of
    Left d' => asn ((i ** d') ** dd)
    Right d' => asn' ((i ** d') ** dd)))

public export
SPFSliceProduct : {x, y, z : Type} ->
  SlicePolyFunc x z -> SlicePolyFunc y z -> SlicePolyFunc (x, y) z
SPFSliceProduct {x} (pd ** dd ** asn) (pd' ** dd' ** asn') =
  (\i => (pd i, pd' i) **
   \(i ** (d, d')) => (dd (i ** d), dd' (i ** d')) **
   \((i ** (d, d')) ** (dd, dd')) =>
    (asn ((i ** d) ** dd), asn' ((i ** d') ** dd')))

------------------------------------------------------------------------
------------------------------------------------------------------------
---- Direct interpretation of DepParamPolyFunc form of SliceFunctor ----
------------------------------------------------------------------------
------------------------------------------------------------------------

public export
InterpDPPF : {a, b : Type} ->
  DepParamPolyFunc a b -> SliceFunctor a b
InterpDPPF {a} {b} dppf paramslice posfst =
  (possnd : fst dppf posfst **
   snd (snd dppf (posfst ** possnd)) ->
    paramslice (fst (snd dppf (posfst ** possnd))))

public export
InterpDPPFMap : {a, b : Type} -> (dppf : DepParamPolyFunc a b) ->
  {sa, sa' : SliceObj a} ->
  SliceMorphism sa sa' ->
  SliceMorphism (InterpDPPF dppf sa) (InterpDPPF dppf sa')
InterpDPPFMap {a} {b} dppf {sa} {sa'} m eb (pos ** dir) =
  (pos ** \di => m (fst (snd dppf (eb ** pos))) (dir di))

------------------------------
---- Slices over PolyFunc ----
------------------------------

-- A way of specifying a `SlicePolyFunc` in terms of `PolyFunc`.
public export
PolySliceFunctor : PolyFunc -> PolyFunc -> Type
PolySliceFunctor parambase posbase =
  (depObjAlg : PFAlg posbase PolyFunc **
   Sigma {a=(PolyFuncMu posbase)} (PolyFuncMu . pfCata {p=posbase} depObjAlg) ->
   PFAlg parambase PolyFunc)

public export
PolySliceToPrimes : {parambase, posbase : PolyFunc} ->
  PolySliceFunctor parambase posbase ->
  SlicePolyFunc'' (PolyFuncMu parambase) (PolyFuncMu posbase)
PolySliceToPrimes {parambase} {posbase} (depObjAlg ** depDirAlg) =
  (PolyFuncMu . pfCata {p=posbase} depObjAlg **
   \pos, param => PolyFuncMu $ pfCata {p=parambase} (depDirAlg pos) param)

public export
PolySliceToSPF : {parambase, posbase : PolyFunc} ->
  PolySliceFunctor parambase posbase ->
  SlicePolyFunc (PolyFuncMu parambase) (PolyFuncMu posbase)
PolySliceToSPF func = SPFFromPrimes (PolySliceToPrimes func)

-----------------------------------------------------------------------
---- Natural transformations on dependent polynomial endofunctors ----
-----------------------------------------------------------------------

public export
SPNatTrans : {w, z : Type} -> SlicePolyFunc w z -> SlicePolyFunc w z -> Type
SPNatTrans {w} {z} f g =
  (onPos : SliceMorphism {a=z} (spfPos f) (spfPos g) **
   (pos : Sigma (spfPos f)) ->
    (dirg : spfDir g (fst pos ** (onPos (fst pos) (snd pos)))) ->
    (dirf : spfDir f pos **
     Equal
      (spfAssign f (pos ** dirf))
      (spfAssign g ((fst pos ** onPos (fst pos) (snd pos)) ** dirg))))

public export
spntOnPos : {w, z : Type} -> {f, g : SlicePolyFunc w z} ->
  SPNatTrans f g -> SliceMorphism {a=z} (spfPos f) (spfPos g)
spntOnPos = fst

public export
spntOnDir : {w, z : Type} -> {f, g : SlicePolyFunc w z} ->
  (alpha : SPNatTrans {w} {z} f g) ->
  (pos : Sigma {a=z} (spfPos f)) ->
  (dirg :
    spfDir g
      (fst pos ** (spntOnPos {w} {z} {f} {g} alpha (fst pos) (snd pos)))) ->
  (dirf : spfDir f pos **
   Equal
    (spfAssign f
      (pos ** dirf))
    (spfAssign g
      ((fst pos ** spntOnPos {f} {g} alpha (fst pos) (snd pos)) ** dirg)))
spntOnDir = snd

public export
InterpSPNTDir : {w, z : Type} -> {f, g : SlicePolyFunc w z} ->
  (alpha : SPNatTrans f g) -> (slw : SliceObj w) ->
  (posfi : z) -> (posf : spfPos f posfi) ->
  (dirsf :
    (d : spfDir f (posfi ** posf)) ->
    slw $ spfAssign f ((posfi ** posf) ** d)) ->
  (dirsg : spfDir g (posfi ** spntOnPos {f} {g} alpha posfi posf)) ->
  slw (spfAssign g ((posfi ** spntOnPos {f} {g} alpha posfi posf) ** dirsg))
InterpSPNTDir {w} {z} alpha slw posfi posf dirsf dirsg
  with (spntOnDir alpha (posfi ** posf) dirsg)
    InterpSPNTDir {w} {z} alpha slw posfi posf dirsf dirsg | (dirf ** eq) =
      rewrite sym eq in dirsf dirf

public export
InterpSPNT : {w, z : Type} -> {f, g : SlicePolyFunc w z} ->
  SPNatTrans f g -> SliceNatTrans {x=w} {y=z} (InterpSPFunc f) (InterpSPFunc g)
InterpSPNT {w} {z} {f} {g} alpha slw posfi (posf ** dirsf) =
  (spntOnPos alpha posfi posf ** InterpSPNTDir alpha slw posfi posf dirsf)

public export
SPNatTrans'' : {w, z : Type} ->
  SlicePolyFunc'' w z -> SlicePolyFunc'' w z -> Type
SPNatTrans'' {w} {z} (fpos ** fdir) (gpos ** gdir) =
  (onPos : SliceMorphism {a=z} fpos gpos **
   (ez : z) -> (i : fpos ez) ->
   SliceMorphism {a=w} (gdir (ez ** onPos ez i)) (fdir (ez ** i)))

------------------------------------------------------
------------------------------------------------------
---- Composition of dependent polynomial functors ----
------------------------------------------------------
------------------------------------------------------

public export
spfId : (base : Type) -> SlicePolyFunc base base
spfId base = (const Unit ** const Unit ** fst . fst)

public export
spfCompose : {x, y, z : Type} ->
  SlicePolyFunc y z -> SlicePolyFunc x y -> SlicePolyFunc x z
spfCompose {x} {y} {z} (qpd ** qdd ** qa) (ppd ** pdd ** pa) =
  (\qi =>
    (qdi : qpd qi **
     (qddi : qdd (qi ** qdi)) -> ppd $ qa ((qi ** qdi) ** qddi)) **
   \qiqpm =>
     (qddi : qdd (fst qiqpm ** fst (snd qiqpm)) **
     pdd
      (qa ((fst qiqpm ** fst (snd qiqpm)) ** qddi) ** snd (snd qiqpm) qddi)) **
   \dd =>
     pa
      ((qa ((fst (fst dd) ** fst (snd (fst dd))) ** fst (snd dd)) **
        snd (snd (fst dd)) (fst (snd dd))) **
       snd (snd dd)))

public export
PolyFuncFromUnitUnitSPF : SlicePolyFunc () () -> PolyFunc
PolyFuncFromUnitUnitSPF (posdep ** dirdep ** assign) =
  (posdep () ** dirdep . MkDPair ())

public export
spfDimapFromBaseChange : {0 w, x, y, z : Type} ->
  (spf : SlicePolyFunc w x) -> (f : w -> y) -> (g : z -> x) ->
  (sy : SliceObj y) -> (ez : z) ->
  InterpSPFunc
    (spfCompose (SPFBaseChange g) (spfCompose spf (SPFBaseChange f))) sy ez ->
  InterpSPFunc
    (SliceFuncDimap spf g f) sy ez
spfDimapFromBaseChange (posdep ** dirdep ** assign) f g sy ez
  ((() ** d) ** di) with (d ()) proof prf
    spfDimapFromBaseChange (posdep ** dirdep ** assign) f g sy ez
      ((() ** d) ** di) | qdi =
        (fst qdi ** \qdd => case di (() ** (rewrite prf in qdd ** ())) of
          syf => rewrite sym prf in syf)

public export
spfDimapToBaseChange : {0 w, x, y, z : Type} ->
  (spf : SlicePolyFunc w x) -> (f : w -> y) -> (g : z -> x) ->
  (sy : SliceObj y) -> (ez : z) ->
  InterpSPFunc
    (SliceFuncDimap spf g f) sy ez ->
  InterpSPFunc
    (spfCompose (SPFBaseChange g) (spfCompose spf (SPFBaseChange f))) sy ez
spfDimapToBaseChange {w} {x} {y} {z} (posdep ** dirdep ** assign) f g sy ez
  (i ** d) =
    ((() ** const (i ** const ())) ** \(() ** (qddi ** ())) => d qddi)

public export
UnitUnitSPFFromPolyFunc : PolyFunc -> SlicePolyFunc () ()
UnitUnitSPFFromPolyFunc (pos ** dir) = (const pos ** dir . snd ** const ())

public export
spfForgetParam : SlicePolyFunc x y -> SlicePolyFunc () y
spfForgetParam (posdep ** dirdep ** assign) = (posdep ** dirdep ** const ())

public export
spfApplyPos : SlicePolyFunc x y -> y -> SlicePolyFunc x ()
spfApplyPos (posdep ** dirdep ** assign) ey =
  -- Equivalent to `SliceFuncDimap spf (const ey) id`.
  (const (posdep ey) **
   \pd => dirdep (ey ** snd pd) **
   \dd => assign ((ey ** snd (fst dd)) ** snd dd))

public export
spfTopf : SlicePolyFunc x y -> y -> PolyFunc
spfTopf spf ey = PolyFuncFromUnitUnitSPF (spfForgetParam (spfApplyPos spf ey))

-- Turn a polynomial functor into a dependent polynomial functor by
-- slicing its directions.
public export
pfSlice : {0 x : Type} ->
  (p : PolyFunc) -> (pfPDir p -> x) -> SlicePolyFunc x ()
pfSlice {x} (pos ** dir) assign =
  (const pos ** dir . snd ** \dd => assign (snd (fst dd) ** snd dd))

-- Turn a polynomial functor into a dependent polynomial functor by
-- slicing its directions completely.
public export
pfSliceAll : (p : PolyFunc) -> SlicePolyFunc (pfPDir p) ()
pfSliceAll p = pfSlice p id

-- Produce a dependent polynomial functor from a non-dependent polynomial
-- functor by assigning the output's codomain to the input's positions
-- and the input's directions to the output's domain.
public export
pfAssign : {0 x, y : Type} ->
  (p : PolyFunc) ->
  (ap : y -> pfPos p) ->
  (ad : (i : y) -> pfDir {p} (ap i) -> x) ->
  SlicePolyFunc x y
pfAssign p ap ad =
  (const Unit ** pfDir {p} . ap . fst ** \dd => ad (fst (fst dd)) (snd dd))

-- Give a polynomial functor the most flexible possible dependent type
-- by distinguishing all of its directions in its domain and all of its
-- positions in its codomain.
public export
pfAssignAll :
  (p : PolyFunc) ->
  (ap : y -> pfPos p) ->
  (ad : (i : y) -> pfDir {p} (ap i) -> x) ->
  SlicePolyFunc (pfPDir p) (pfPos p)
pfAssignAll p ap ad = pfAssign p id MkDPair

--------------------------------------------------------------------
---- Composition of parameterized dependent polynomial functors ----
--------------------------------------------------------------------

public export
spfParamId : {a : Type} -> (x : SliceObj a) -> ParamSPF {a} x x
spfParamId {a} x ea = spfId (x ea)

public export
spfParamCompose : {a : Type} -> {x, y, z : SliceObj a} ->
  ParamSPF {a} y z -> ParamSPF {a} x y -> ParamSPF {a} x z
spfParamCompose pspf' pspf ea = spfCompose (pspf' ea) (pspf ea)

--------------------------------------------------------------------
---- Parameterized dependent polynomial natural transformations ----
--------------------------------------------------------------------

public export
ParamSPNatTrans : {a : Type} -> {w, z : SliceObj a} ->
  ParamSPF {a} w z -> ParamSPF {a} w z -> Type
ParamSPNatTrans {a} {w} {z} pspf pspf' =
  (ea : a) -> SPNatTrans (pspf ea) (pspf' ea)

-------------------------------------------------------------------------
-------------------------------------------------------------------------
---- Dependent polynomial endofunctors as cells of a double category ----
-------------------------------------------------------------------------
-------------------------------------------------------------------------

-- There is a double category whose vertical arrows are morphisms of `Type`
-- (i.e. functions `x -> y`) and whose horizontal arrows are dependent
-- polynomial functors (i.e. terms of `SlicePolyFunc x y`).  In that double
-- category, if we have vertical morphisms (functions) `w -> w'` and `z -> z'`,
-- and horizontal morphisms (dependent polynomial endofunctors)
-- `SlicePolyFunc w z` and `SlicePolyFunc w' z'`, then this is the type
-- of a cell.  See
-- https://ncatlab.org/nlab/show/polynomial+functor#the_2category_of_polynomial_functors
public export
SPFCell : {w, w', z, z' : Type} ->
  (w -> w') -> (z -> z') -> SlicePolyFunc w z -> SlicePolyFunc w' z' -> Type
SPFCell {w} {w'} {z} {z'} f g spf spf' =
  SPNatTrans (SliceFuncRmap spf f) (SliceFuncLmap spf' g)

---------------------------------------------------------------------------
---------------------------------------------------------------------------
---- Conversion between morphism and dependent-set polynomial functors ----
---------------------------------------------------------------------------
---------------------------------------------------------------------------

public export
DepPolyFToSPF : {w, x, y, z : Type} ->
  (x -> w) -> (x -> y) -> (y -> z) ->
  SlicePolyFunc w z
DepPolyFToSPF {w} {x} {y} {z} f g h =
  (\i => PreImage h i **
   \ey => Subset0 x (\x' => Equal (fst0 (snd ey)) $ g x') **
   \ex => f (fst0 (snd ex)))

public export
SPFToDepPolyF : {w, z : Type} -> SlicePolyFunc w z ->
  (wxyz : (Type, Type, Type, Type) **
   (fst (snd wxyz) -> fst wxyz,
    fst (snd wxyz) -> fst (snd (snd wxyz)),
    fst (snd (snd wxyz)) -> snd (snd (snd wxyz))))
SPFToDepPolyF {w} {z} (posdep ** dirdep ** assign) =
  ((w, Sigma {a=(Sigma {a=z} posdep)} dirdep, Sigma {a=z} posdep, z) **
   (assign, DPair.fst, DPair.fst))

-------------------------------------------------------
-------------------------------------------------------
---- Conversions between SlicePolyFunc and W-types ----
-------------------------------------------------------
-------------------------------------------------------

public export
WTFtoSPF : {parambase, posbase : Type} ->
  WTypeFunc parambase posbase -> SlicePolyFunc parambase posbase
WTFtoSPF {parambase} {posbase} (MkWTF pos dir assign dsl psl) =
  (\i => PreImage {a=pos} {b=posbase} psl i **
   \x => PreImage {a=dir} {b=pos} dsl $ fst0 $ snd x **
   \d => assign $ fst0 $ snd d)

public export
SPFtoWTF : {parambase, posbase : Type} ->
  SlicePolyFunc parambase posbase -> WTypeFunc parambase posbase
SPFtoWTF (posdep ** dirdep ** assign) =
  MkWTF
    (Sigma {a=posbase} posdep)
    (Sigma {a=(Sigma {a=posbase} posdep)} dirdep)
    assign
    fst
    fst

public export
InterpWTFtoSPF : {parambase, posbase : Type} ->
  (wtf : WTypeFunc parambase posbase) ->
  (sl : SliceObj parambase) -> (ib : posbase) ->
  InterpSPFunc {a=parambase} {b=posbase}
    (WTFtoSPF {parambase} {posbase} wtf) sl ib ->
  InterpWTF {parambase} {posbase} wtf sl ib
InterpWTFtoSPF (MkWTF pos dir assign dsl psl) sl ib = id

public export
InterpWTFtoSPFInv : {parambase, posbase : Type} ->
  (wtf : WTypeFunc parambase posbase) ->
  (sl : SliceObj parambase) -> (ib : posbase) ->
  InterpWTF {parambase} {posbase} wtf sl ib ->
  InterpSPFunc {a=parambase} {b=posbase}
    (WTFtoSPF {parambase} {posbase} wtf) sl ib
InterpWTFtoSPFInv (MkWTF pos dir assign dsl psl) sl ib = id

public export
InterpSPFtoWTF : {parambase, posbase : Type} ->
  (spf : SlicePolyFunc parambase posbase) ->
  (sl : SliceObj parambase) -> (ib : posbase) ->
  InterpWTF {parambase} {posbase} (SPFtoWTF {parambase} {posbase} spf) sl ib ->
  InterpSPFunc {a=parambase} {b=posbase} spf sl ib
InterpSPFtoWTF {parambase} {posbase} (posdep ** dirdep ** assign) sl ib
  (Element0 {type=(Sigma {a=posbase} posdep)} (ib' ** i) eq ** p) =
    (rewrite sym eq in i **
     \d => p $
      Element0 ((ib ** rewrite sym eq in i) ** d) (rewrite sym eq in Refl))

public export
InterpSPFtoWTFInv : {parambase, posbase : Type} ->
  (spf : SlicePolyFunc parambase posbase) ->
  (sl : SliceObj parambase) -> (ib : posbase) ->
  InterpSPFunc {a=parambase} {b=posbase} spf sl ib ->
  InterpWTF {parambase} {posbase} (SPFtoWTF {parambase} {posbase} spf) sl ib
InterpSPFtoWTFInv {parambase} {posbase} (posdep ** dirdep ** assign) sl ib
  (i ** d) =
    (Element0 (ib ** i) Refl **
     \(Element0 (i' ** di) deq) => rewrite deq in d $ rewrite sym deq in di)

------------------------------------------------
------------------------------------------------
----- Polynomial bifunctors and profunctors ----
------------------------------------------------
------------------------------------------------

--------------------------------------------------
---- Data determining a polynomial profunctor ----
--------------------------------------------------

public export
RepProFromParam : {pos : Type} -> ParamPolyFunc pos -> Type -> PolyFunc
RepProFromParam {pos} p x = (pos ** flip InterpPolyFunc x . p)

public export
InterpCovarRepProFunc : {pos : Type} ->
  ParamPolyFunc pos -> Type -> Type -> Type
InterpCovarRepProFunc {pos} p = InterpPolyFunc . RepProFromParam {pos} p

public export
InterpContravarRepProFunc : {pos : Type} ->
  ParamPolyFunc pos -> Type -> Type -> Type
InterpContravarRepProFunc {pos} p = InterpDirichFunc . RepProFromParam {pos} p

public export
record PolyProFunc where
  constructor MkPolyProFunc
  contravarPos : Type
  covarPos : Type
  contravarDir : ParamPolyFunc contravarPos
  covarDir : ParamPolyFunc covarPos

public export
InterpPolyProFunc : PolyProFunc -> Type -> Type -> Type
InterpPolyProFunc ppf x y =
  Either
    (InterpContravarRepProFunc ppf.contravarDir y x)
    (InterpCovarRepProFunc ppf.covarDir x y)

public export
InterpPFDimap : (ppf : PolyProFunc) -> {0 a, b, c, d: Type} ->
  (c -> a) -> (b -> d) -> InterpPolyProFunc ppf a b -> InterpPolyProFunc ppf c d
InterpPFDimap ppf f g (Left (i ** m)) =
  Left (i ** InterpPFMap (ppf.contravarDir i) g . m . f)
InterpPFDimap ppf f g (Right (i ** m)) =
  Right (i ** g . m . InterpPFMap (ppf.covarDir i) f)

public export
(ppf : PolyProFunc) => Profunctor (InterpPolyProFunc ppf) where
  dimap {ppf} = InterpPFDimap ppf

------------------------------------------------------------
---- Data determining a polynomial bifunctor/profunctor ----
------------------------------------------------------------

public export
PolyBiFunc : Type
PolyBiFunc = (pos : Type ** pos -> (Type, Type))

public export
PolyBiPos : PolyBiFunc -> Type
PolyBiPos = fst

public export
PolyBiDirPairs : (pbf : PolyBiFunc) -> PolyBiPos pbf -> (Type, Type)
PolyBiDirPairs = snd

public export
PolyBiContraDir : (pbf : PolyBiFunc) -> PolyBiPos pbf -> Type
PolyBiContraDir pbf = fst . PolyBiDirPairs pbf

public export
PolyBiCovarDir : (pbf : PolyBiFunc) -> PolyBiPos pbf -> Type
PolyBiCovarDir pbf = snd . PolyBiDirPairs pbf

public export
PolyBiTotDir : (pbf : PolyBiFunc) -> PolyBiPos pbf -> Type
PolyBiTotDir pbf = uncurry Either . PolyBiDirPairs pbf

public export
PolyBiTotPF : PolyBiFunc -> PolyFunc
PolyBiTotPF pbf = (PolyBiPos pbf ** PolyBiTotDir pbf)

public export
PolyBiContraPart : PolyBiFunc -> PolyFunc
PolyBiContraPart pbf = (PolyBiPos pbf ** PolyBiContraDir pbf)

public export
PolyBiCovarPart : PolyBiFunc -> PolyFunc
PolyBiCovarPart pbf = (PolyBiPos pbf ** PolyBiCovarDir pbf)

public export
PolyBiDirTot : PolyBiFunc -> Type
PolyBiDirTot = pfPDir . PolyBiTotPF

public export
PolyBiDirIsCovar : (pbf : PolyBiFunc) -> PolyBiDirTot pbf -> Bool
PolyBiDirIsCovar (pos ** dir) (i ** di) with (dir i)
  PolyBiDirIsCovar (pos ** dir) (i ** di) | (contra, covar) = isRight di

public export
PolyBiPosDep : PolyBiFunc -> SliceObj Unit
PolyBiPosDep pbf () = PolyBiPos pbf

public export
PolyBiDirDep : (pbf : PolyBiFunc) -> SliceObj (Sigma (PolyBiPosDep pbf))
PolyBiDirDep pbf (() ** i) = PolyBiTotDir pbf i

public export
PolyBiDirAssign : (pbf : PolyBiFunc) -> Sigma (PolyBiDirDep pbf) -> Bool
PolyBiDirAssign (pos ** dir) ((() ** i) ** di) =
  PolyBiDirIsCovar (pos ** dir) (i ** di)

public export
PolyBiToSliceFunc : PolyBiFunc -> SlicePolyFunc Bool Unit
PolyBiToSliceFunc pbf =
  (PolyBiPosDep pbf ** PolyBiDirDep pbf ** PolyBiDirAssign pbf)

--------------------------------------------------
---- Interpretation of bifunctors/profunctors ----
--------------------------------------------------

public export
InterpPolyBiFunc : PolyBiFunc -> Type -> Type -> Type
InterpPolyBiFunc pbf x y =
  (i : PolyBiPos pbf ** (PolyBiContraDir pbf i -> x, PolyBiCovarDir pbf i -> y))

public export
InterpPFBimap : (pbf : PolyBiFunc) -> {0 a, b, c, d: Type} ->
  (a -> c) -> (b -> d) -> InterpPolyBiFunc p a b -> InterpPolyBiFunc p c d
InterpPFBimap pbf f g (i ** (contra, covar)) = (i ** (f . contra, g . covar))

public export
(pbf : PolyBiFunc) => Bifunctor (InterpPolyBiFunc pbf) where
  bimap {pbf} = InterpPFBimap pbf

public export
InterpPolyProFunc' : PolyBiFunc -> Type -> Type -> Type
InterpPolyProFunc' pbf x y =
  (i : PolyBiPos pbf ** (x -> PolyBiContraDir pbf i, PolyBiCovarDir pbf i -> y))

public export
InterpPFDimap' : (pbf : PolyBiFunc) -> {0 a, b, c, d: Type} ->
  (c -> a) -> (b -> d) -> InterpPolyProFunc' p a b -> InterpPolyProFunc' p c d
InterpPFDimap' pbf f g (i ** (contra, covar)) = (i ** (contra . f, g . covar))

public export
(pbf : PolyBiFunc) => Profunctor (InterpPolyProFunc' pbf) where
  dimap {pbf} = InterpPFDimap' pbf

-------------------------------------------
-------------------------------------------
---- Polynomial profunctor as category ----
-------------------------------------------
-------------------------------------------

public export
profToCat : PolyBiFunc -> CatSig
profToCat pbf =
  MkCatSig
    (PolyBiPos pbf)
    (\x, y =>
      (PolyBiCovarDir pbf y -> PolyBiCovarDir pbf x,
       PolyBiContraDir pbf x -> PolyBiContraDir pbf y))
    (\x, y, (f, g), (f', g') => (ExtEq f f', ExtEq g g'))
    (\x' => (id, id))
    (\f, g => (fst g . fst f, snd f . snd g))

-----------------------------------------------
-----------------------------------------------
---- Dependent-polynomial-functors algebra ----
-----------------------------------------------
-----------------------------------------------

---------------------------------------------------
---- Algebras of dependent polynomial functors ----
---------------------------------------------------

public export
SPFAlg : {a : Type} -> SlicePolyEndoFunc a -> SliceObj a -> Type
SPFAlg spf sa = SliceMorphism (InterpSPFunc spf sa) sa

---------------------------------------------------
---- Initial algebras of dependent polynomials ----
---------------------------------------------------

public export
data SPFMu : {a : Type} -> SlicePolyEndoFunc a -> SliceObj a where
  InSPFM :
    {a : Type} -> {spf : SlicePolyEndoFunc a} ->
    (pos : Sigma (spfPos spf)) ->
    ((dir : spfDir spf pos) -> SPFMu spf (spfAssign spf (pos ** dir))) ->
    SPFMu spf (fst pos)

public export
SPFMuPoly : {a : Type} -> SlicePolyEndoFunc a -> PolyFunc
SPFMuPoly {a} spf = (a ** SPFMu {a} spf)

public export
SPFMuSigma : {a : Type} -> SlicePolyEndoFunc a -> Type
SPFMuSigma {a} spf = Sigma {a} (SPFMu {a} spf)

public export
SlArMu : {a : Type} -> SliceEndoArena a -> SliceObj a
SlArMu {a} = SPFMu {a} . SlArToSPF {dom=a} {cod=a}

--------------------------------------------------------
---- Catamorphisms of dependent polynomial functors ----
--------------------------------------------------------

public export
spfCata : {a : Type} -> {spf : SlicePolyEndoFunc a} -> {sa : SliceObj a} ->
  SPFAlg spf sa -> SliceMorphism {a} (SPFMu spf) sa
spfCata {spf} alg _ (InSPFM (posi ** pos) dir) =
  alg posi
    (pos ** \d => spfCata alg (spfAssign spf ((posi ** pos) ** d)) (dir d))

--------------------------------------------
---- Dependent polynomial (free) monads ----
--------------------------------------------

-- Another name for an algebra just to emphasize when we think of it
-- as the implementation of an interface represented by a polynomial.
public export
SliceIFace : {a : Type} -> SlicePolyEndoFunc a -> SliceObj a -> Type
SliceIFace = SPFAlg

public export
SPFFreeAlg : {a : Type} -> (sf : SlicePolyEndoFunc a) -> (sl : SliceObj a) ->
  SPFAlg sf (SliceFreeM (InterpSPFunc sf) sl)
SPFFreeAlg {a} (posdep ** dirdep ** assign) sl ea (i ** d) =
  InSlFc {f=(InterpSPFunc (posdep ** dirdep ** assign))} {sa=sl} {ea} (i ** d)

public export
SPFTranslate : {a : Type} ->
  SlicePolyEndoFunc a -> SliceObj a -> SlicePolyEndoFunc a
SPFTranslate {a} spf sl = SPFSliceCoproduct {x=a} {y=a} (SPFConst {y=a} sl) spf

public export
SPFTranslateUnit : {a : Type} -> SlicePolyEndoFunc a -> SlicePolyEndoFunc a
SPFTranslateUnit {a} spf = SPFTranslate {a} spf (const Unit)

public export
SlArTranslateUnit : {a : Type} -> SliceEndoArena a -> SlicePolyEndoFunc a
SlArTranslateUnit {a} = SPFTranslateUnit {a} . SlArToSPF

public export
SlicePolyFree : {a : Type} -> SlicePolyEndoFunc a -> SliceEndofunctor a
SlicePolyFree {a} = SPFMu {a} .* SPFTranslate {a}

public export
SliceArenaFree : {a : Type} -> SliceEndoArena a -> SliceEndofunctor a
SliceArenaFree {a} = SlicePolyFree {a} . SlArToSPF

-- The signature of the "eval" universal morphism for "SPFFreeM spf".
-- (This is the right adjunct of the free/forgetful adjunction between
-- the category of F-algebras of `spf` and `Type/a`.)
public export
SPFMeval : {a : Type} -> SlicePolyEndoFunc a -> Type
SPFMeval {a} spf = (slv, sla : SliceObj a) ->
  SliceMorphism {a} slv sla -> SPFAlg spf sla ->
  SliceMorphism {a} (SlicePolyFree {a} spf slv) sla

-- All polynomial functors have universal eval morphisms.
public export
spfmEval : {a : Type} -> (spf : SlicePolyEndoFunc a) -> SPFMeval spf
spfmEval {a} (pos ** dir ** assign) slv sla subst alg =
  spfCata {a} {spf=(SPFTranslate {a} (pos ** dir ** assign) slv)} {sa=sla} $
    \ela, (p ** d) => case p of
      Left elv => subst ela elv
      Right elp => alg ela (elp ** d)

public export
SlArFMeval : {a : Type} -> SliceEndoArena a -> Type
SlArFMeval {a} ar = (slv, sla : SliceObj a) ->
  SliceMorphism {a} slv sla -> SPFAlg (SlArToSPF ar) sla ->
  SliceMorphism {a} (SliceArenaFree {a} ar slv) sla

public export
slarEval : {a : Type} -> (ar : SliceEndoArena a) -> SlArFMeval ar
slarEval {a} ar = spfmEval {a} (SlArToSPF ar)

public export
SlArFreeMPos : {a : Type} -> SliceEndoArena a -> SliceObj a
SlArFreeMPos {a} ar = SliceArenaFree {a} ar (const Unit)

public export
SlArFreeMDirAlg : {a : Type} -> (ar : SliceEndoArena a) ->
  SPFAlg {a} (SlArTranslateUnit {a} ar) (const $ SliceObj a)
SlArFreeMDirAlg {a} ar ela (Left () ** d) ela' =
  ela = ela'
SlArFreeMDirAlg {a} ar ela (Right p ** d) ela' =
  Sigma {a=(Sigma {a} (SLAdir ar (ela ** p)))} $ flip d ela'

public export
SlArFreeMDir : {a : Type} -> (ar : SliceEndoArena a) ->
  Sigma (SlArFreeMPos {a} ar) -> SliceObj a
SlArFreeMDir {a} ar (ela ** i) =
  spfCata {a}
    {spf=(SlArTranslateUnit {a} ar)} {sa=(const $ SliceObj a)}
    (SlArFreeMDirAlg {a} ar) ela i

public export
SlArFreeM : {a : Type} -> SliceEndoArena a -> SliceEndoArena a
SlArFreeM {a} ar = SlAr (SlArFreeMPos {a} ar) (SlArFreeMDir {a} ar)

public export
InterpSlArFree : {a : Type} -> SliceEndoArena a -> SliceEndofunctor a
InterpSlArFree {a} = SLAPomap {dom=a} {cod=a} . SlArFreeM {a}

public export
SlArFreeToInterp : {a : Type} ->
  (ar : SliceEndoArena a) -> (sa : SliceObj a) ->
  SliceMorphism (SliceArenaFree ar sa) (InterpSlArFree ar sa)
SlArFreeToInterp {a} ar sa =
  slarEval {a} ar sa (InterpSlArFree ar sa)
    (\ela, elsa => (InSPFM (ela ** Left ()) (\v => void v) ** \_, Refl => elsa))
    (\ela, (p ** d) =>
      (InSPFM (ela ** Right p) (\di => fst $ d di) **
       \ela', ((ela'' ** d'') ** d''') => snd (d (ela'' ** d'')) ela' d'''))

public export
SlArInterpToFreeCurried : {a : Type} ->
  (ar : SliceEndoArena a) -> (sa : SliceObj a) ->
  (ela : a) -> (p : SlArFreeMPos ar ela) ->
  SliceMorphism {a} (SLAdir (SlArFreeM ar) (ela ** p)) sa ->
  SliceArenaFree ar sa ela
SlArInterpToFreeCurried {a} ar sa ela (InSPFM (ela ** (Left ())) d) m =
  InSPFM (ela ** Left $ m ela Refl) $ \v => void v
SlArInterpToFreeCurried {a} ar sa ela (InSPFM (ela ** (Right p)) d) m =
  InSPFM (ela ** Right p) $ \(ela' ** d') =>
    SlArInterpToFreeCurried {a} ar sa ela' (d (ela' ** d')) $
      \ela'', d'' => m ela'' ((ela' ** d') ** d'')

public export
SlArInterpToFree : {a : Type} ->
  (ar : SliceEndoArena a) -> (sa : SliceObj a) ->
  SliceMorphism (InterpSlArFree ar sa) (SliceArenaFree ar sa)
SlArInterpToFree {a} ar sa ela (p ** m) =
  SlArInterpToFreeCurried {a} ar sa ela p m

public export
SPFFreeM : {a : Type} -> SlicePolyEndoFunc a -> SlicePolyEndoFunc a
SPFFreeM {a} spf = SlArToSPF (SlArFreeM (SlArFromSPF spf))

public export
SPFFreeMPos : {a : Type} -> SlicePolyEndoFunc a -> SliceObj a
SPFFreeMPos spf = spfPos (SPFFreeM spf)

public export
SPFFreeMDir : {a : Type} -> (spf : SlicePolyEndoFunc a) ->
  Sigma (SPFFreeMPos {a} spf) -> Type
SPFFreeMDir spf = spfDir (SPFFreeM spf)

public export
SPFFreeMAssign : {a : Type} -> (spf : SlicePolyEndoFunc a) ->
  Sigma (SPFFreeMDir {a} spf) -> a
SPFFreeMAssign spf = spfAssign (SPFFreeM spf)

public export
InterpSPFFree : {a : Type} -> SlicePolyEndoFunc a -> SliceEndofunctor a
InterpSPFFree {a} = InterpSPFunc {a} . SPFFreeM {a}

public export
SPFMAlg : {a : Type} -> SlicePolyEndoFunc a -> SliceObj a -> Type
SPFMAlg spf sa = SliceMorphism (InterpSPFFree spf sa) sa

-------------------------------------------------
-------------------------------------------------
---- Dependent-polynomial-functors coalgebra ----
-------------------------------------------------
-------------------------------------------------

-----------------------------------------------------
---- Coalgebras of dependent polynomial functors ----
-----------------------------------------------------

public export
SPFCoalg : {a : Type} -> SlicePolyEndoFunc a -> SliceObj a -> Type
SPFCoalg spf sa = SliceMorphism sa (InterpSPFunc spf sa)

------------------------------------------------------
---- Terminal coalgebras of dependent polynomials ----
------------------------------------------------------

public export
data SPFNu : {a : Type} -> SlicePolyEndoFunc a -> SliceObj a where
  InSPFN :
    {a : Type} -> {spf : SlicePolyEndoFunc a} ->
    (pos : Sigma (spfPos spf)) ->
    ((dir : spfDir spf pos) -> Inf (SPFNu spf (spfAssign spf (pos ** dir)))) ->
    SPFNu spf (fst pos)

-------------------------------------------------------
---- Anamorphisms of dependent polynomial functors ----
-------------------------------------------------------

public export
spfAna : {a : Type} -> {spf : SlicePolyEndoFunc a} -> {sa : SliceObj a} ->
  SPFCoalg spf sa -> SliceMorphism {a} sa (SPFNu spf)
spfAna {a} {spf} {sa} coalg elema elemsa =
  case coalg elema elemsa of
    (pos ** dir) =>
      InSPFN {a} {spf} (elema ** pos) $
        \di => spfAna coalg (spfAssign spf ((elema ** pos) ** di)) (dir di)

------------------------------------------------
---- Dependent polynomial (cofree) comonads ----
------------------------------------------------

{-
public export
SPFScalePos : {0 x, y : Type} -> SlicePolyFunc x y -> Type -> Type
SPFScalePos = PFScalePos . spfFunc

public export
SPFScaleDir : {x, y : Type} -> (spf : SlicePolyFunc x y) -> (a : Type) ->
  SPFScalePos spf a -> Type
SPFScaleDir spf a = PFScaleDir (spfFunc spf) a

public export
SPFScaleFunc : {x, y : Type} -> (spf : SlicePolyFunc x y) -> (a : Type) ->
  PolyFunc
SPFScaleFunc spf a = (SPFScalePos spf a ** SPFScaleDir spf a)

public export
SPFScaleIdx : {0 x, y : Type} -> (spf : SlicePolyFunc x y) -> (a : Type) ->
  (a -> y -> y) -> SliceIdx (SPFScaleFunc spf a) x y
SPFScaleIdx {x} {y} ((pos ** dir) ** idx) a f (PFNode l i) di = f l (idx i di)

public export
SPFScale : {x, y : Type} -> SlicePolyFunc x y -> (a : Type) ->
  (a -> y -> y) -> SlicePolyFunc x y
SPFScale spf a f = (SPFScaleFunc spf a ** SPFScaleIdx spf a f)

public export
SPFCofreeCMFromNu : {x : Type} -> SlicePolyEndoF x -> SliceObj x -> SliceObj x
SPFCofreeCMFromNu spf sx =
  SPFNu {a=-x} (SPFScale {x} {y=x} spf (Sigma sx) (const id))
  -}

-----------------------------------------
-----------------------------------------
---- Dependent polynomial interfaces ----
-----------------------------------------
-----------------------------------------

-- The free monad of a coproduct of dependent polynomial functors implements
-- each of the interfaces induced by the two functors.

public export
SPFCoprodFreeAlgFl : {a : Type} -> (sf, sf' : SlicePolyEndoFunc a) ->
  (sl : SliceObj a) ->
  SPFAlg sf (SliceFreeM (InterpSPFunc (SPFSliceCoproduct sf sf')) sl)
SPFCoprodFreeAlgFl {a}
  (posdep ** dirdep ** assign) (posdep' ** dirdep' ** assign') sl ea (i ** d) =
    InSlFc (Left i ** d)

public export
SPFCoprodFreeAlgFr : {a : Type} -> (sf, sf' : SlicePolyEndoFunc a) ->
  (sl : SliceObj a) ->
  SPFAlg sf' (SliceFreeM (InterpSPFunc (SPFSliceCoproduct sf sf')) sl)
SPFCoprodFreeAlgFr {a}
  (posdep ** dirdep ** assign) (posdep' ** dirdep' ** assign') sl ea (i ** d) =
    InSlFc (Right i ** d)

--------------------------------------------
--------------------------------------------
---- `PolyFunc` dependent on `PolyFunc` ----
--------------------------------------------
--------------------------------------------

public export
PFPolyAlgToSlicePosDep : {p : PolyFunc} ->
  PFAlg p PolyFunc -> PolyFuncMu p -> Type
PFPolyAlgToSlicePosDep {p=(pos ** dir)} alg = PolyFuncMu . pfCata alg

public export
PFPolyAlgToSliceDirDepAlg : {p : PolyFunc} ->
  (alg : PFAlg p PolyFunc) ->
  (i : pfPos p) ->
  (d : pfDir {p} i -> PolyFuncMu p) ->
  (i' : pfPos (alg i (pfCata alg . d))) ->
  (d' : pfDir {p=(alg i (pfCata alg . d))} i' -> Type) ->
  Type
PFPolyAlgToSliceDirDepAlg {p=(pos ** dir)} alg i d i' d' =
  Sigma {a=(pfDir i')} d'

public export
PFPolyAlgToSliceDirDepCurried : {p : PolyFunc} ->
  (alg : PFAlg p PolyFunc) ->
  (i : PolyFuncMu p) -> PFPolyAlgToSlicePosDep alg i -> Type
PFPolyAlgToSliceDirDepCurried {p=p@(pos ** dir)} alg (InPFM i d) =
  pfCata $ PFPolyAlgToSliceDirDepAlg {p} alg i d

public export
PFPolyAlgToSliceDirDep : {p : PolyFunc} ->
  (alg : PFAlg p PolyFunc) ->
  Sigma {a=(PolyFuncMu p)} (PFPolyAlgToSlicePosDep alg) -> Type
PFPolyAlgToSliceDirDep {p=(pos ** dir)} alg (i ** d) =
  PFPolyAlgToSliceDirDepCurried alg i d

public export
PFPolyAlgToSliceId : {p : PolyFunc} ->
  PFAlg p PolyFunc -> SlicePolyEndoFuncId (PolyFuncMu p)
PFPolyAlgToSliceId {p=(pos ** dir)} alg =
  (PFPolyAlgToSlicePosDep alg ** PFPolyAlgToSliceDirDep alg)

public export
PFPolyAlgToSliceFunc : {p : PolyFunc} ->
  PFAlg p PolyFunc -> SlicePolyEndoFunc (PolyFuncMu p)
PFPolyAlgToSliceFunc = SlicePolyEndoFuncFromId . PFPolyAlgToSliceId

------------------------------------------------
------------------------------------------------
---- `Poly` as the arrow category of `Type` ----
------------------------------------------------
------------------------------------------------

----------------------------------------------------------------
----------------------------------------------------------------
---- Polynomial types with functors separated for iteration ----
----------------------------------------------------------------
----------------------------------------------------------------

-- The positions (constructors with parameters) of the polynomial endofunctor
-- which generates finite object-language types.
public export
data FinTPos : Type where
  FTPInitial : FinTPos
  FTPTerminal : FinTPos
  FTPCoproduct : FinTPos
  FTPProduct : FinTPos

-- The directions (or powers, or recursive fields) of the constructors of the
-- polynomial endofunctor which generates finite object-language types.
public export
data FinTDir : FinTPos -> Type where
  FTDLeft : FinTDir FTPCoproduct
  FTDRight : FinTDir FTPCoproduct
  FTDFst : FinTDir FTPProduct
  FTDSnd : FinTDir FTPProduct

public export
FTDirInitial : {0 a : FinTDir FTPInitial -> Type} ->
  (d : FinTDir FTPInitial) -> a d
FTDirInitial _ impossible

public export
FTDirTerminal : {0 a : FinTDir FTPTerminal -> Type} ->
  (d : FinTDir FTPTerminal) -> a d
FTDirTerminal _ impossible

public export
FTDirCoproduct : {0 a : FinTDir FTPCoproduct -> Type} ->
  a FTDLeft -> a FTDRight -> (d : FinTDir FTPCoproduct) -> a d
FTDirCoproduct l r FTDLeft = l
FTDirCoproduct l r FTDRight = r

public export
FTDirProduct : {0 a : FinTDir FTPProduct -> Type} ->
  a FTDFst -> a FTDSnd -> (d : FinTDir FTPProduct) -> a d
FTDirProduct f s FTDFst = f
FTDirProduct f s FTDSnd = s

-- The polynomial endofunctor which generates finite object-language types.
public export
FinTPolyF : PolyFunc
FinTPolyF = (FinTPos ** FinTDir)

-- The metalanguage form of the above functor.
public export
FinTObjF : Type -> Type
FinTObjF = InterpPolyFunc FinTPolyF

-- The type of finite object-language types, generated as a fixed point
-- of `FinTObjF`.
public export
FinTObj : Type
FinTObj = PolyFuncMu FinTPolyF

{-
-- Compute the depth index of a type generated by `FinTPolyF`.
public export
FinTPolyIdx : SliceIdx FinTPolyF Nat Nat
FinTPolyIdx FTPInitial di = 1
FinTPolyIdx FTPTerminal di = 1
FinTPolyIdx FTPCoproduct di = smax (di FTDLeft) (di FTDRight)
FinTPolyIdx FTPProduct di = smax (di FTDFst) (di FTDSnd)

-- The dependent (indexed) polynomial endofunctor (on the slice category of
-- `Type` over `Nat`) which generates depth-indexed finite object-language
-- types.
public export
FinTSPF : SlicePolyFunc Nat Nat
FinTSPF = (FinTPolyF ** FinTPolyIdx)

-- The metalanguage form of the above functor.
public export
FinTObjSF : SliceFunctor Nat Nat
FinTObjSF = InterpSPFunc FinTSPF

-- The type of depth-indexed finite object-language types, generated as a
-- fixed point of `FinTObjSF`.
public export
FinTFNew : SliceObj Nat
FinTFNew = SPFMu FinTSPF

-- Utility functions for producing terms of type `FinTFNew`.
public export
FTFNInitial : FinTFNew 1
FTFNInitial = (InPFM FTPInitial FTDirInitial ** \_ => Refl)

public export
FTFNTerminal : FinTFNew 1
FTFNTerminal = (InPFM FTPTerminal FTDirTerminal ** \_ => Refl)

public export
FTFNCoproduct : {m, n : Nat} ->
  FinTFNew m -> FinTFNew n -> FinTFNew (smax m n)
FTFNCoproduct {m} {n} (x ** xeq) (y ** yeq) =
  (InPFM FTPCoproduct (FTDirCoproduct x y) **
   \funext => cong S $ rewrite xeq funext in rewrite yeq funext in Refl)

public export
FTFNProduct : {m, n : Nat} ->
  FinTFNew m -> FinTFNew n -> FinTFNew (smax m n)
FTFNProduct {m} {n} (x ** xeq) (y ** yeq) =
  (InPFM FTPProduct (FTDirProduct x y) **
   \funext => cong S $ rewrite xeq funext in rewrite yeq funext in Refl)

-- The type of types generated by any of up to `N` iterations of
-- the object-language-type-generating metalanguage functor.
public export
FinTFDepth : Nat -> Type
FinTFDepth n = (m : Nat ** (LTE m n, FinTFNew m))

public export
minDepth : {0 n : Nat} -> FinTFDepth n -> Nat
minDepth (m ** _) = m

public export
depthLTE : {0 n : Nat} -> (type : FinTFDepth n) -> LTE (minDepth type) n
depthLTE (_ ** (lte, _)) = lte

public export
FinType : {0 n : Nat} -> (type : FinTFDepth n) -> FinTFNew (minDepth type)
FinType (_ ** (_, type)) = type

-- A type that can be generated at a given depth can also be generated
-- at any greater depth.
public export
FinTFPromote : {n, m : Nat} -> FinTFDepth n -> LTE n m -> FinTFDepth m
FinTFPromote {n} {m} (m' ** (ltem'n, type)) ltenm =
  (m' ** (transitive ltem'n ltenm, type))

public export
FinTFPromoteMax : {n, m : Nat} -> FinTFDepth n -> FinTFDepth (maximum n m)
FinTFPromoteMax {n} {m} dtype =
  FinTFPromote {n} {m=(maximum n m)} dtype $ maxLTELeft n m

public export
FinPromoteLeft : {m, n : Nat} -> FinTFNew m -> FinTFDepth (maximum m n)
FinPromoteLeft type = (m ** (maxLTELeft m n, type))

public export
FinPromoteRight : {m, n : Nat} -> FinTFNew n -> FinTFDepth (maximum m n)
FinPromoteRight type = (n ** (maxLTERight m n, type))

public export
depthNotZero : {0 n : Nat} -> {funext : FunExt} -> FinTFNew n -> Not (n = 0)
depthNotZero {n} {funext} ((InPFM FTPInitial f) ** sleq) =
  \eq => case sleq funext of Refl => case eq of Refl impossible
depthNotZero {n} {funext} ((InPFM FTPTerminal f) ** sleq) =
  \eq => case sleq funext of Refl => case eq of Refl impossible
depthNotZero {n} {funext} ((InPFM FTPCoproduct f) ** sleq) =
  \eq => case sleq funext of Refl => case eq of Refl impossible
depthNotZero {n} {funext} ((InPFM FTPProduct f) ** sleq) =
  \eq => case sleq funext of Refl => case eq of Refl impossible

public export
depth0Void : {funext : FunExt} -> FinTFNew 0 -> Void
depth0Void {funext} em = depthNotZero {funext} em Refl

public export
depth0ExFalso : {funext : FunExt} -> {0 a : Type} -> FinTFNew 0 -> a
depth0ExFalso {funext} type = void (depth0Void {funext} type)

-- The signature of the induction principle for `FinTFNew`.
public export
FinTFNewIndAlg : ((n : Nat) -> FinTFNew n -> Type) -> Type
FinTFNewIndAlg a =
  (n : Nat) ->
  ((type : FinTFDepth n) -> a (minDepth type) (FinType type)) ->
  (type : FinTFNew (S n)) ->
  a (S n) type

public export
FinTFNewIndAlgStrengthened :
  {0 a : (n : Nat) -> FinTFNew n -> Type} ->
  FinTFNewIndAlg a ->
  (n : Nat) ->
  ((m : Nat) -> LTE m n -> (type : FinTFNew m) -> a m type) ->
  (type : FinTFNew (S n)) ->
  a (S n) type
FinTFNewIndAlgStrengthened alg n hyp =
  alg n $ \dtype => hyp (minDepth dtype) (depthLTE dtype) (FinType dtype)

-- Induction on `FinTFNew`.
public export
finTFNewInd : {funext : FunExt} -> {0 a : (n : Nat) -> FinTFNew n -> Type} ->
  FinTFNewIndAlg a -> (n : Nat) -> (type : FinTFNew n) -> a n type
finTFNewInd {funext} {a} alg =
  natDepGenInd
    (\type => depth0ExFalso {funext} type, FinTFNewIndAlgStrengthened alg)

-- The directed colimit of the metalanguage functor that generates
-- depth-indexed object-language types.  (The directed colimit is also known
-- as the initial algebra.)
public export
MuFinTF : Type
MuFinTF = DPair Nat FinTFNew

-- Every `FinTFDepth` is a `MuFinTF`.
public export
TFDepthToMu : {n : Nat} -> FinTFDepth n -> MuFinTF
TFDepthToMu {n} (m ** (lte, type)) = (m ** type)

-- Morphisms from the terminal object to a given object.  This
-- hom-set is isomorphic to the object itself.  From the perspective
-- of (dependent) types, these are the terms of the object/type.
public export
data FinTFNewTrAlg : FinTFNewIndAlg (\_, _ => Type) where
  FTTUnit :
    {0 hyp : FinTFDepth Z -> Type} ->
    FinTFNewTrAlg Z hyp FTFNTerminal
  FTTLeft :
    {0 m, n : Nat} -> {0 hyp : FinTFDepth (maximum m n) -> Type} ->
    {0 x : FinTFNew m} -> {0 y : FinTFNew n} ->
    hyp (FinPromoteLeft {n} x) ->
    FinTFNewTrAlg (maximum m n) hyp (FTFNCoproduct x y)
  FTTRight :
    {0 m, n : Nat} -> {0 hyp : FinTFDepth (maximum m n) -> Type} ->
    {0 x : FinTFNew m} -> {0 y : FinTFNew n} ->
    hyp (FinPromoteRight {m} y) ->
    FinTFNewTrAlg (maximum m n) hyp (FTFNCoproduct x y)
  FTTPair :
    {0 m, n : Nat} -> {0 hyp : FinTFDepth (maximum m n) -> Type} ->
    {0 x : FinTFNew m} -> {0 y : FinTFNew n} ->
    hyp (FinPromoteLeft {n} x) ->
    hyp (FinPromoteRight {m} y) ->
    FinTFNewTrAlg (maximum m n) hyp (FTFNProduct x y)

public export
FinTFNewTerm : {funext : FunExt} -> (n : Nat) -> FinTFNew n -> Type
FinTFNewTerm {funext} = finTFNewInd {funext} FinTFNewTrAlg

-- Generate the exponential object of a pair of finite unrefined objects.
public export
FinExpObjF : (n : Nat) ->
  (FinTFDepth n -> MuFinTF -> MuFinTF) -> FinTFNew (S n) -> MuFinTF -> MuFinTF
FinExpObjF n morph type cod = FinExpObjF_hole

public export
FinNewExpObj : {funext : FunExt} ->
  {m, n : Nat} -> FinTFNew m -> FinTFNew n -> MuFinTF
FinNewExpObj {funext} {m} {n} tm tn =
  finTFNewInd
    {funext} {a=(\_, _ => MuFinTF -> MuFinTF)} FinExpObjF m tm (n ** tn)

public export
FinDepthExpObj : {funext : FunExt} ->
  {m, n : Nat} -> FinTFDepth m -> FinTFDepth n -> MuFinTF
FinDepthExpObj {funext} (m ** (_, tm)) (n ** (_, tn)) =
  FinNewExpObj {funext} tm tn

public export
MuFinExpObj : {funext : FunExt} -> MuFinTF -> MuFinTF -> MuFinTF
MuFinExpObj {funext} (m ** tm) (n ** tn) = FinNewExpObj {funext} tm tn

-- Generate the morphisms out of a given finite unrefined type of
-- a given depth, given the morphisms out of all unrefined types of
-- lesser depths.
public export
FinNewMorphF : (n : Nat) ->
  (FinTFDepth n -> MuFinTF -> Type) -> FinTFNew (S n) -> MuFinTF -> Type
FinNewMorphF n morph type cod = FinNewMorphF_hole

public export
FinNewMorph : {funext : FunExt} ->
  {m, n : Nat} -> FinTFNew m -> FinTFNew n -> Type
FinNewMorph {funext} {m} {n} tm tn =
  finTFNewInd
    {funext} {a=(\_, _ => MuFinTF -> Type)} FinNewMorphF m tm (n ** tn)

public export
FinDepthMorph : {funext : FunExt} ->
  {m, n : Nat} -> FinTFDepth m -> FinTFDepth n -> Type
FinDepthMorph {funext} (m ** (_, tm)) (n ** (_, tn)) =
  FinNewMorph {funext} tm tn

public export
MuFinMorph : {funext : FunExt} -> MuFinTF -> MuFinTF -> Type
MuFinMorph {funext} (m ** tm) (n ** tn) = FinNewMorph {funext} tm tn
-}

------------------------
------------------------
---- F-(co)algebras ----
------------------------
------------------------

public export
data TranslateF : (0 f : Type -> Type) -> (0 a, x : Type) -> Type where
  InVar : {0 f : Type -> Type} -> {0 a, x : Type} ->
    a -> TranslateF f a x
  InCom : {0 f : Type -> Type} -> {0 a, x : Type} ->
    f x -> TranslateF f a x

public export
data LinearF : (0 f : Type -> Type) -> (0 a, x : Type) -> Type where
  InNode : {0 f : Type -> Type} -> {0 a, x : Type} ->
    a -> f x -> LinearF f a x

public export
data FreeM : (0 f : Type -> Type) -> (0 x : Type) -> Type where
  InFreeM : {0 f : Type -> Type} -> {0 x : Type} ->
    TranslateF f x (FreeM f x) -> FreeM f x

public export
InFVar : {0 f : Type -> Type} -> {0 x : Type} -> x -> FreeM f x
InFVar = InFreeM . InVar

public export
InFCom : {0 f : Type -> Type} -> {0 x : Type} -> f (FreeM f x) -> FreeM f x
InFCom = InFreeM . InCom

public export
data CofreeCM : (0 f : Type -> Type) -> (0 x : Type) -> Type where
  InCofreeCM : {0 f : Type -> Type} -> {0 x : Type} ->
    Inf (LinearF f x (CofreeCM f a)) -> CofreeCM f x

public export
InCFNode : {0 f : Type -> Type} -> {0 x : Type} ->
  x -> f (CofreeCM f x) -> CofreeCM f x
InCFNode ex efx = InCofreeCM $ InNode ex efx

public export
MuF : (0 f : Type -> Type) -> Type
MuF f = FreeM f Void

public export
NuF : (0 f : Type -> Type) -> Type
NuF f = CofreeCM f Unit

public export
FAlg : (Type -> Type) -> Type -> Type
FAlg f a = f a -> a

public export
FCoalg : (Type -> Type) -> Type -> Type
FCoalg f a = a -> f a

public export
MuCata : (Type -> Type) -> Type -> Type
MuCata f x = Algebra f x -> MuF f -> x

public export
FromInitialFAlg : (Type -> Type) -> Type
FromInitialFAlg f = (x : Type) -> MuCata f x

public export
NuAna : (Type -> Type) -> Type -> Type
NuAna f x = Coalgebra f x -> x -> NuF f

public export
ToTerminalFCoalg : (Type -> Type) -> Type
ToTerminalFCoalg f = (x : Type) -> NuAna f x

--------------------------
---- Product algebras ----
--------------------------

public export
PairFAlg : (Type -> Type) -> (Type -> Type) -> Type -> Type
PairFAlg f g x = FAlg f (FAlg g x)

public export
DiagFAlg : (Type -> Type) -> Type -> Type
DiagFAlg f = PairFAlg f f

public export
MuPairCata : (Type -> Type) -> (Type -> Type) -> Type -> Type
MuPairCata f g x = PairFAlg f g x -> MuF f -> MuF g -> x

public export
MuDiagCata : (Type -> Type) -> Type -> Type
MuDiagCata f = MuPairCata f f

public export
FromInitialPairFAlg : (Type -> Type) -> (Type -> Type) -> Type
FromInitialPairFAlg f g = (x : Type) -> MuPairCata f g x

public export
FromInitialDiagFAlg : (Type -> Type) -> Type
FromInitialDiagFAlg f = FromInitialPairFAlg f f

public export
muPairCata : {f, g : Type -> Type} ->
  FromInitialFAlg f -> FromInitialFAlg g -> FromInitialPairFAlg f g
muPairCata {f} {g} cataf catag x alg ef eg =
  catag x (cataf (FAlg g x) alg ef) eg

public export
muDiagCata : {f : Type -> Type} -> FromInitialFAlg f -> FromInitialDiagFAlg f
muDiagCata {f} cata = muPairCata {f} {g=f} cata cata

----------------------------
---- Coproduct algebras ----
----------------------------

public export
EitherFAlg : (Type -> Type) -> (Type -> Type) -> Type -> Type
EitherFAlg f g x = (FAlg f x, FAlg g x)

public export
MuEitherCata : (Type -> Type) -> (Type -> Type) -> Type -> Type
MuEitherCata f g x = EitherFAlg f g x -> Either (MuF f) (MuF g) -> x

public export
FromInitialEitherFAlg : (Type -> Type) -> (Type -> Type) -> Type
FromInitialEitherFAlg f g = (x : Type) -> MuEitherCata f g x

public export
muEitherCata : {f, g : Type -> Type} ->
  FromInitialFAlg f -> FromInitialFAlg g -> FromInitialEitherFAlg f g
muEitherCata {f} {g} cataf catag x (algf, _) (Left ef) = cataf x algf ef
muEitherCata {f} {g} cataf catag x (_, algg) (Right eg) = catag x algg eg

-------------------------------------
---- Types dependent on algebras ----
-------------------------------------

-- A slice of a `MuF` type over some type `x` for which we have a
-- catamorphism and an algebra.
public export
MuSlice : {0 f : Type -> Type} -> {0 x : Type} ->
  MuCata f x -> FAlg f x -> x -> Type
MuSlice {f} {x} cata alg elemX = Subset0 (MuF f) (Equal elemX . cata alg)

public export
MuSlicePred : {0 f : Type -> Type} -> {x : Type} ->
  (cata : MuCata f x) -> (alg : FAlg f x) -> Type
MuSlicePred {f} {x} cata alg =
  (ex : x) -> MuSlice {f} {x} cata alg ex -> Type

-------------------------------
-------------------------------
---- Substitution category ----
-------------------------------
-------------------------------

--------------------------------------------------------------------
---- Inhabited types from fixed point of (metalanguage) functor ----
--------------------------------------------------------------------

-- Inhabited types only
public export
ISubstObjF : Type -> Type
ISubstObjF =
  CoproductF
    -- const Unit
  (const Unit) $
  CoproductF
  -- Coproduct
  ProductMonad
  -- Product
  ProductMonad

public export
ISOTerminalF : {0 x : Type} -> ISubstObjF x
ISOTerminalF = Left ()

public export
ISOCoproductF : {0 x : Type} -> x -> x -> ISubstObjF x
ISOCoproductF t t' = Right $ Left (t, t')

public export
ISOProductF : {0 x : Type} -> x -> x -> ISubstObjF x
ISOProductF t t' = Right $ Right (t, t')

public export
ISubstOAlg : Type -> Type
ISubstOAlg = FAlg ISubstObjF

public export
ISubstODiagAlg : Type -> Type
ISubstODiagAlg = DiagFAlg ISubstObjF

public export
FreeISubstO : (0 _ : Type) -> Type
FreeISubstO = FreeM ISubstObjF

public export
MuISubstO : Type
MuISubstO = MuF ISubstObjF

public export
ISOTerminal : {0 x : Type} -> FreeISubstO x
ISOTerminal = InFCom $ ISOTerminalF

public export
ISOCoproduct : {0 x : Type} -> FreeISubstO x -> FreeISubstO x -> FreeISubstO x
ISOCoproduct = InFCom .* ISOCoproductF

public export
ISOProduct : {0 x : Type} -> FreeISubstO x -> FreeISubstO x -> FreeISubstO x
ISOProduct = InFCom .* ISOProductF

public export
isubstOCata : FromInitialFAlg ISubstObjF
isubstOCata x alg (InFreeM (InVar v)) = void v
isubstOCata x alg (InFreeM (InCom c)) = alg $ case c of
  Left () => Left ()
  Right t => Right $ case t of
    Left (y, z) => Left (isubstOCata x alg y, isubstOCata x alg z)
    Right (y, z) => Right (isubstOCata x alg y, isubstOCata x alg z)

public export
isubstODiagCata : FromInitialDiagFAlg ISubstObjF
isubstODiagCata = muDiagCata isubstOCata

public export
ISubstOSlice : {x : Type} -> ISubstOAlg x -> x -> Type
ISubstOSlice {x} = MuSlice (isubstOCata x)

public export
ISubstOSlicePred : {x : Type} -> ISubstOAlg x -> Type
ISubstOSlicePred {x} = MuSlicePred (isubstOCata x)

---------------------------------------------------------------
---- Substitution category including initial object (Void) ----
---------------------------------------------------------------

public export
SubstObj : Type
SubstObj =
  -- Void
  Either ()
  -- Inhabited type
  MuISubstO

public export
SOInitial : SubstObj
SOInitial = Left ()

public export
SOTerminal : SubstObj
SOTerminal = Right ISOTerminal

public export
SOCoproduct : SubstObj -> SubstObj -> SubstObj
SOCoproduct (Left ()) (Left ()) = Left ()
SOCoproduct (Left ()) (Right t) = Right t
SOCoproduct (Right t) (Left ()) = Right t
SOCoproduct (Right t) (Right t') = Right $ ISOCoproduct t t'

public export
SOProduct : SubstObj -> SubstObj -> SubstObj
SOProduct (Left ()) (Left ()) = Left ()
SOProduct (Left ()) (Right _) = Left ()
SOProduct (Right _) (Left ()) = Left ()
SOProduct (Right t) (Right t') = Right $ ISOProduct t t'

---------------------------------------------
---- Properties of substitution category ----
---------------------------------------------

public export
isubstOShowAlg : ISubstOAlg String
isubstOShowAlg (Left ()) = show 1
isubstOShowAlg (Right (Left (m, n))) = "(" ++ m ++ " + " ++ n ++ ")"
isubstOShowAlg (Right (Right (m, n))) = "(" ++ m ++ " * " ++ n ++ ")"

public export
Show MuISubstO where
  show = isubstOCata String isubstOShowAlg

-- Depths of inhabited types begin at 1 -- depth 0 is the initial
-- object, before any iterations of SubstObjF have been applied,
-- and the initial object is uninhabited (it's Void).
public export
isubstODepthAlg : ISubstOAlg Nat
isubstODepthAlg (Left ()) = 1
isubstODepthAlg (Right (Left (m, n))) = S $ max m n
isubstODepthAlg (Right (Right (m, n))) = S $ max m n

public export
isubstODepth : MuISubstO -> Nat
isubstODepth = isubstOCata Nat isubstODepthAlg

public export
substODepth : SubstObj -> Nat
substODepth = eitherElim (const 1) isubstODepth

public export
isubstOCardAlg : ISubstOAlg Nat
isubstOCardAlg (Left ()) = 1
isubstOCardAlg (Right (Left (m, n))) = m + n
isubstOCardAlg (Right (Right (m, n))) = m * n

public export
isubstOCard : MuISubstO -> Nat
isubstOCard = isubstOCata Nat isubstOCardAlg

public export
substOCard : SubstObj -> Nat
substOCard = eitherElim (const 0) isubstOCard

-------------------------------------------------
---- Interpretation of substitution category ----
-------------------------------------------------

public export
isubstOToMetaAlg : ISubstOAlg Type
isubstOToMetaAlg (Left ()) = ()
isubstOToMetaAlg (Right (Left (x, y))) = Either x y
isubstOToMetaAlg (Right (Right (x, y))) = Pair x y

public export
isubstOToMeta : MuISubstO -> Type
isubstOToMeta = isubstOCata Type isubstOToMetaAlg

public export
substOToMeta : SubstObj -> Type
substOToMeta (Left ()) = Void
substOToMeta (Right t) = isubstOToMeta t

-----------------------------------------------
---- Exponentials in substitution category ----
-----------------------------------------------

public export
isubstOHomObjAlg : ISubstODiagAlg MuISubstO
-- 1 -> x == x
isubstOHomObjAlg (Left ()) x = InFCom x
-- (x + y) -> z == (x -> z) * (y -> z)
isubstOHomObjAlg (Right (Left (x, y))) z = ISOProduct (x z) (y z)
-- (x * y) -> z == x -> y -> z
isubstOHomObjAlg (Right (Right (x, y))) z with (y z)
  isubstOHomObjAlg (Right (Right (x, y))) z | InFreeM (InVar v) = void v
  isubstOHomObjAlg (Right (Right (x, y))) z | InFreeM (InCom yz) = x yz

public export
isubstOHomObj : MuISubstO -> MuISubstO -> MuISubstO
isubstOHomObj = isubstODiagCata MuISubstO isubstOHomObjAlg

public export
substOHomObj : SubstObj -> SubstObj -> SubstObj
-- 0 -> x == 1
substOHomObj (Left ()) _ = SOTerminal
-- x /= 0 => x -> 0 == 0
substOHomObj (Right _) (Left ()) = SOInitial
-- x /= 0, y /= 0
substOHomObj (Right x) (Right y) = Right $ isubstOHomObj x y

--------------------------------------------
---- Morphisms in substitution category ----
--------------------------------------------

public export
isubstOMorphism : MuISubstO -> MuISubstO -> Type
isubstOMorphism = isubstOToMeta .* isubstOHomObj

public export
0 isubstOEval : (x, y : MuISubstO) ->
  isubstOMorphism (ISOProduct (isubstOHomObj x y) x) y
isubstOEval x y = ?isubstOEval_hole

public export
0 isubstOCurry : {x, y, z : MuISubstO} ->
  isubstOMorphism (ISOProduct x y) z -> isubstOMorphism x (isubstOHomObj y z)
isubstOCurry {x} {y} {z} f = ?isubstOCurry_hole

--------------------------------------------------------------------
---- Interpretation of substitution endofunctors as polynomials ----
--------------------------------------------------------------------

public export
ISubstEndoFunctorF : Type -> Type
ISubstEndoFunctorF x =
  -- Identity
  Either () $
  -- Composition
  Either (x, x) $
  -- const unit, coproduct, product
  ISubstObjF x

public export
ISOEFIdF : {0 x : Type} -> ISubstEndoFunctorF x
ISOEFIdF = Left ()

public export
ISOEFComposeF : {0 x : Type} -> x -> x -> ISubstEndoFunctorF x
ISOEFComposeF = Right . Left .* MkPair

public export
ISOEFTerminalF : {0 x : Type} -> ISubstEndoFunctorF x
ISOEFTerminalF = Right $ Right $ ISOTerminalF

public export
ISOEFCoproductF : {0 x : Type} -> x -> x -> ISubstEndoFunctorF x
ISOEFCoproductF = Right . Right .* ISOCoproductF

public export
ISOEFProductF : {0 x : Type} -> x -> x -> ISubstEndoFunctorF x
ISOEFProductF = Right . Right .* ISOProductF

public export
ISOEFAlg : Type -> Type
ISOEFAlg = FAlg ISubstEndoFunctorF

public export
ISOEFDiagAlg : Type -> Type
ISOEFDiagAlg = DiagFAlg ISubstEndoFunctorF

public export
FreeISOEF : (0 _ : Type) -> Type
FreeISOEF = FreeM ISubstEndoFunctorF

public export
ISubstEndo : Type
ISubstEndo = MuF ISubstEndoFunctorF

public export
ISOEFId : {0 x : Type} -> FreeISOEF x
ISOEFId = InFCom $ ISOEFIdF

public export
ISOEFCompose : {0 x : Type} -> FreeISOEF x -> FreeISOEF x -> FreeISOEF x
ISOEFCompose = InFCom .* ISOEFComposeF

public export
ISOEFTerminal : {0 x : Type} -> FreeISOEF x
ISOEFTerminal = InFCom $ ISOEFTerminalF

public export
ISOEFCoproduct : {0 x : Type} -> FreeISOEF x -> FreeISOEF x -> FreeISOEF x
ISOEFCoproduct = InFCom .* ISOEFCoproductF

public export
ISOEFProduct : {0 x : Type} -> FreeISOEF x -> FreeISOEF x -> FreeISOEF x
ISOEFProduct = InFCom .* ISOEFProductF

public export
isubstEndoCata : FromInitialFAlg ISubstEndoFunctorF
isubstEndoCata x alg (InFreeM (InVar v)) = void v
isubstEndoCata x alg (InFreeM (InCom c)) = alg $ case c of
  Left () => Left ()
  Right c' => Right $ case c' of
    Left (l, r) => Left (isubstEndoCata x alg l, isubstEndoCata x alg r)
    Right c'' => Right $ case c'' of
      Left () => Left ()
      Right c''' => Right $ case c''' of
        Left (l, r) => Left (isubstEndoCata x alg l, isubstEndoCata x alg r)
        Right (l, r) => Right (isubstEndoCata x alg l, isubstEndoCata x alg r)

public export
iSubstEndoDiagCata : FromInitialDiagFAlg ISubstEndoFunctorF
iSubstEndoDiagCata = muDiagCata isubstEndoCata

public export
isoFunctorAlg : ISOEFAlg (Type -> Type)
isoFunctorAlg (Left ()) = id
isoFunctorAlg (Right (Left (g, f))) = g . f
isoFunctorAlg (Right (Right (Left ()))) = const Unit
isoFunctorAlg (Right (Right (Right (Left (f, g))))) = CoproductF f g
isoFunctorAlg (Right (Right (Right (Right (f, g))))) = ProductF f g

public export
isoFunctor : ISubstEndo -> Type -> Type
isoFunctor = isubstEndoCata (Type -> Type) isoFunctorAlg

-- Computes the endofunctor which results from pre-composing the
-- endofunctor `Const Void` with the given endofunctor.  If the
-- result is `Const Void`, it returns `Nothing`, since `FreeISOEF` does
-- not contain `Const Void` (it contains only the non-zero polynomials).
-- (Viewing an endofunctor `f` as a polynomial `p`, this computes
-- `p(0)` and then interprets the resulting polynomial as an endofunctor --
-- which must be constant.)
public export
isoAppVoidAlg : {0 x : Type} -> ISOEFAlg $ Maybe $ FreeISOEF x
-- 1 . 0 = Void
isoAppVoidAlg (Left ()) = Nothing
-- 0 . f = 0
isoAppVoidAlg (Right (Left (Nothing, _))) = Nothing
-- f(0) . 0 = f(0)
isoAppVoidAlg (Right (Left ((Just g), Nothing))) = Just g
-- g(0) . f(0) = (g + f)(0)
isoAppVoidAlg (Right (Left ((Just g), (Just f)))) = Just $ ISOEFCoproduct g f
-- 1(1) = 1
isoAppVoidAlg (Right (Right (Left ()))) = Just ISOEFTerminal
-- 0 + f(0) = f(0)
isoAppVoidAlg (Right (Right (Right (Left (Nothing, f))))) = f
-- f(0) + 0 = f(0)
isoAppVoidAlg (Right (Right (Right (Left (f, Nothing))))) = f
-- f(0) + g(0) = (f + g)(0)
isoAppVoidAlg (Right (Right (Right (Left ((Just f), (Just g)))))) =
  Just $ ISOEFCoproduct g f
-- 0 * g(0) = 0
isoAppVoidAlg (Right (Right (Right (Right (Nothing, g))))) = Nothing
-- f(0) * 0 = 0
isoAppVoidAlg (Right (Right (Right (Right ((Just f), Nothing))))) = Nothing
-- f(0) * g(0) = (f * g)(0)
isoAppVoidAlg (Right (Right (Right (Right ((Just f), (Just g)))))) =
  Just $ ISOEFProduct g f

public export
isoAppVoid : ISubstEndo -> Maybe ISubstEndo
isoAppVoid = isubstEndoCata _ isoAppVoidAlg

public export
ISOEFCoproductM : ISubstEndo -> ISubstEndo -> ISubstEndo
ISOEFCoproductM f g = ISOEFCoproduct f g

public export
ISOEFCodiag : ISubstEndo
ISOEFCodiag = ISOEFCoproductM ISOEFId ISOEFId

public export
ISOEFProductM : ISubstEndo -> ISubstEndo -> ISubstEndo
ISOEFProductM f g = ISOEFProduct f g

public export
ISOEFDiag : ISubstEndo
ISOEFDiag = ISOEFProductM ISOEFId ISOEFId

public export
repISubstObjF : ISubstEndo
repISubstObjF =
  ISOEFCoproduct ISOEFTerminal (ISOEFCoproduct ISOEFCodiag ISOEFCodiag)

public export
FreeSubstEndo : Type -> Type
FreeSubstEndo x =
  -- const Void
  Either ()
  -- Non-void endofunctor (which takes all inhabited types to inhabited types)
  (FreeISOEF x)

public export
SubstEndo : Type
SubstEndo = FreeSubstEndo Void

public export
SOEFInitial : {0 x : Type} -> FreeSubstEndo x
SOEFInitial = Left ()

public export
SOEFTerminal : {0 x : Type} -> FreeSubstEndo x
SOEFTerminal = Right ISOEFTerminal

public export
SOEFId : {0 x : Type} -> FreeSubstEndo x
SOEFId = Right ISOEFId

public export
isoAppVoidSO : ISubstEndo -> SubstEndo
isoAppVoidSO f = case isoAppVoid f of
  Just f' => Right f'
  Nothing => Left ()

public export
soAppVoid : SubstEndo -> SubstEndo
soAppVoid (Left ()) = Left ()
soAppVoid (Right f) = isoAppVoidSO f

public export
SOEFCompose : SubstEndo -> SubstEndo -> SubstEndo
SOEFCompose (Left ()) _ = Left ()
SOEFCompose (Right f) (Left ()) = isoAppVoidSO f
SOEFCompose (Right f) (Right g) = Right $ ISOEFCompose f g

public export
SOEFCoproduct : SubstEndo -> SubstEndo -> SubstEndo
SOEFCoproduct (Left ()) (Left ()) = Left ()
SOEFCoproduct (Left ()) (Right g) = Right g
SOEFCoproduct (Right f) (Left ()) = Right f
SOEFCoproduct (Right f) (Right g) = Right $ ISOEFCoproduct f g

public export
SOEFProduct : SubstEndo -> SubstEndo -> SubstEndo
SOEFProduct (Left ()) (Left ()) = Left ()
SOEFProduct (Left ()) (Right _) = Left ()
SOEFProduct (Right _) (Left ()) = Left ()
SOEFProduct (Right f) (Right g) = Right $ ISOEFProduct f g

public export
soFunctor : SubstEndo -> Type -> Type
soFunctor (Left ()) = const Void
soFunctor (Right f) = isoFunctor f

---------------------------------------------
---------------------------------------------
---- Natural numbers as directed colimit ----
---------------------------------------------
---------------------------------------------

public export
MaybeEUF : Type -> Type
MaybeEUF = Either Unit

public export
NatOF : Type -> Type
NatOF = MaybeEUF

public export
NatOAlg : Type -> Type
NatOAlg = FAlg NatOF

public export
NatOAlgC : Type -> Type
NatOAlgC a = (a, a -> a)

public export
NatOAlgCToAlg : {a : Type} -> NatOAlgC a -> NatOAlg a
NatOAlgCToAlg {a} (z, s) e = case e of
  Left () => z
  Right n => s n

public export
NatOCoalg : Type -> Type
NatOCoalg = FCoalg NatOF

public export
FreeNatO : Type -> Type
FreeNatO x = FreeM NatOF x

public export
MuNatO : Type
MuNatO = MuF NatOF

public export
NatO0 : {0 x : Type} -> FreeNatO x
NatO0 = InFCom $ Left ()

public export
NatOS : {0 x : Type} -> FreeNatO x -> FreeNatO x
NatOS = InFCom . Right

public export
NatO1 : {0 x : Type} -> FreeNatO x
NatO1 = NatOS NatO0

public export
natOFoldFreeIdx : {0 x, v : Type} ->
  (v -> x) -> (FreeNatO v -> x -> x) -> FreeNatO v -> x -> FreeNatO v -> x
natOFoldFreeIdx subst op idx e (InFreeM $ InVar var) =
  subst var
natOFoldFreeIdx subst op idx e (InFreeM $ InCom $ Left ()) =
  e
natOFoldFreeIdx subst op idx e (InFreeM $ InCom $ Right n) =
  natOFoldFreeIdx subst op (NatOS idx) (op idx e) n

public export
natOFoldFree : {0 x, v : Type} ->
  (v -> x) -> (FreeNatO v -> x -> x) -> x -> FreeNatO v -> x
natOFoldFree subst op = natOFoldFreeIdx subst op NatO0

public export
natOFoldIdx : {0 x : Type} -> (MuNatO -> x -> x) -> MuNatO -> x -> MuNatO -> x
natOFoldIdx {x} = natOFoldFreeIdx {x} {v=Void} (voidF x)

public export
natOFold : {0 x : Type} -> (MuNatO -> x -> x) -> x -> MuNatO -> x
natOFold {x} = natOFoldFree {x} {v=Void} (voidF x)

public export
natOCata : FromInitialFAlg NatOF
natOCata x alg (InFreeM $ InVar v) = void v
natOCata x alg (InFreeM $ InCom c) = alg $ case c of
  Left () => Left ()
  Right n => Right $ natOCata x alg n

public export
natOCataC : {x : Type} -> NatOAlgC x -> MuNatO -> x
natOCataC {x} alg = natOCata x (NatOAlgCToAlg alg)

public export
CofreeNatO : Type -> Type
CofreeNatO x = CofreeCM NatOF x

public export
NuNatO : Type
NuNatO = NuF NatOF

public export
natOAna : ToTerminalFCoalg NatOF
natOAna x coalg e = InCofreeCM $ InNode () $ case coalg e of
  Left () => Left ()
  Right n => Right $ natOAna x coalg n

public export
muToNatAlg : NatOAlgC Nat
muToNatAlg = (Z, S)

public export
muToNat : MuNatO -> Nat
muToNat = natOCataC muToNatAlg

public export
natToMu : Nat -> MuNatO
natToMu Z = NatO0
natToMu (S n) = NatOS $ natToMu n

public export
Show MuNatO where
  show = show . muToNat

public export
MuNatIdAlg : NatOAlgC MuNatO
MuNatIdAlg = (NatO0, NatOS)

public export
mapNatAlg : {0 x : Type} -> (x -> x) -> NatOAlgC x -> NatOAlgC x
mapNatAlg f (z, s) = (f z, f . s)

----------------------------------
---- Pairs of natural numbers ----
----------------------------------

public export
NatOPairF : Type -> Type
NatOPairF = ProductMonad . NatOF

public export
NatOPairAlg : Type -> Type
NatOPairAlg = FAlg NatOPairF

public export
NatOPairAlgC : Type -> Type
NatOPairAlgC x = (x, x -> x, x -> x, (x, x) -> x)

public export
NatOPairAlgCToAlg : {a : Type} -> NatOPairAlgC a -> NatOPairAlg a
NatOPairAlgCToAlg (zz, zs, sz, ss) e = case e of
  (Left (), Left ()) => zz
  (Left (), Right n) => zs n
  (Right n, Left ()) => sz n
  (Right m, Right n) => ss (m, n)

public export
NatOAlgToPairL0Alg : {0 x : Type} -> NatOAlgC x -> NatOPairAlgC x
NatOAlgToPairL0Alg (z, sl) = (z, const z, sl, sl . fst)

public export
NatAlgToPair0RAlg : {0 x : Type} -> NatOAlgC x -> NatOPairAlgC x
NatAlgToPair0RAlg (z, sr) = (z, sr, const z, sr . snd)

public export
NatOPairCoalg : Type -> Type
NatOPairCoalg = FCoalg NatOPairF

public export
natSumAlg : NatOAlgC (MuNatO -> MuNatO)
natSumAlg = (id, (.) NatOS)

public export
natSum : MuNatO -> MuNatO -> MuNatO
natSum = natOCataC natSumAlg

public export
natMulAlg : NatOAlgC (MuNatO -> MuNatO)
natMulAlg = (const NatO0, (\alg, n => natSum (alg n) n))

public export
natMul : MuNatO -> MuNatO -> MuNatO
natMul = natOCataC natMulAlg

public export
natHomObjAlg : NatOAlgC (MuNatO -> MuNatO)
natHomObjAlg = (const NatO1, (\alg, n => natMul (alg n) n))

public export
natHomObj : MuNatO -> MuNatO -> MuNatO
natHomObj = natOCataC natHomObjAlg

public export
natPow : MuNatO -> MuNatO -> MuNatO
natPow = flip natHomObj

--------------------------------------------------------
---- Bounded natural numbers from directed colimits ----
--------------------------------------------------------

public export
NatPreAlgC : NatOAlgC Type
NatPreAlgC = (Void, NatOF)

-- The type of natural numbers strictly less than the given natural number.
public export
NatPre : MuNatO -> Type
NatPre = natOCataC NatPreAlgC

public export
NatPreAlg : Type -> Type
NatPreAlg x = MuNatO -> NatOAlgC x

public export
natPreCata : {0 x : Type} -> NatPreAlg x -> {n : MuNatO} -> NatPre n -> x
natPreCata {x} alg {n=(InFreeM $ InVar v)} m = void v
natPreCata {x} alg {n=(InFreeM $ InCom $ Left ())} m = void m
natPreCata {x} alg {n=(InFreeM $ InCom $ Right n)} m =
  let (z, s) = alg n in
  case m of
    (Left ()) => z
    (Right m') => s $ natPreCata {x} alg {n} m'

{-
public export
NatPreAlgAlg : Type -> Type
NatPreAlgAlg x = NatPreAlgAlg_hole

public export
natPreAlgAlgToAlg : {0 x : Type} -> NatPreAlgAlg x -> NatPreAlg x
natPreAlgAlgToAlg {x} algalg = natPreAlgAlgToAlg_hole

public export
natPreAlgCata : {0 x : Type} -> NatPreAlgAlg x -> {n : MuNatO} -> NatPre n -> x
natPreAlgCata {x} algalg = natPreCata {x} (natPreAlgAlgToAlg {x} algalg)
-}

public export
NatPreMeta : Nat -> Type
NatPreMeta = NatPre . natToMu

public export
preToMetaAlg : NatPreAlg Nat
preToMetaAlg = const muToNatAlg

public export
preToMeta : {n : Nat} -> NatPreMeta n -> Nat
preToMeta {n} = natPreCata {x=Nat} preToMetaAlg {n=(natToMu n)}

public export
metaToPre : (m : Nat) -> (0 n : Nat) -> {auto 0 lt : LT m n} -> NatPreMeta n
metaToPre Z (S n) {lt=(LTESucc _)} = Left ()
metaToPre (S m) (S n) {lt=(LTESucc lt')} = Right $ metaToPre m {n} {lt=lt'}

public export
InitPre : (m : Nat) -> (0 n : Nat) -> {auto 0 lt : IsYesTrue (isLT m n)} ->
  NatPreMeta n
InitPre m n {lt} = metaToPre m n {lt=(fromIsYes lt)}

public export
showPreMeta : (n : Nat) -> NatPreMeta n -> String
showPreMeta n m = show (preToMeta m) ++ "/" ++ show n

--------------------------
---- Tuples and lists ----
--------------------------

public export
TupleAlgC : Type -> NatOAlgC Type
TupleAlgC x = ((), Pair x)

-- The type of tuples of the given length.
public export
Tuple : Type -> MuNatO -> Type
Tuple = natOCataC . TupleAlgC

public export
ListNAlgC : Type -> NatOAlgC Type
ListNAlgC x = ((), CoproductF Prelude.id (Pair x))

-- The type of tuples of less than or equal to the given length.
public export
ListN : Type -> MuNatO -> Type
ListN = natOCataC . ListNAlgC

----------------------------------
---- Trees of natural numbers ----
----------------------------------

public export
MuNatOT : Type
MuNatOT = MuF NatOPairF

public export
natOTCata : FromInitialFAlg NatOPairF
natOTCata x alg (InFreeM $ InVar v) = void v
natOTCata x alg (InFreeM $ InCom c) = alg $ case c of
  (Left (), Left ()) => (Left (), Left ())
  (Left (), Right n) => (Left (), Right $ natOTCata x alg n)
  (Right n, Left ()) => (Right $ natOTCata x alg n, Left ())
  (Right m, Right n) => (Right $ natOTCata x alg m, Right $ natOTCata x alg n)

----------------------------------------------------
----------------------------------------------------
---- Idris representation of polynomial circuit ----
----------------------------------------------------
----------------------------------------------------

------------------------------------------------------
------------------------------------------------------
---- Zeroth-order unrefined substitutive category ----
------------------------------------------------------
------------------------------------------------------

public export
data S0ObjF : Type -> Type where
  S0InitialF : {0 carrier : Type} -> S0ObjF carrier
  S0TerminalF : {0 carrier : Type} -> S0ObjF carrier
  S0CoproductF : {0 carrier : Type} -> carrier -> carrier -> S0ObjF carrier
  S0ProductF : {0 carrier : Type} -> carrier -> carrier -> S0ObjF carrier

public export
FreeS0Obj : (0 _ : Type) -> Type
FreeS0Obj = FreeM S0ObjF

public export
CofreeS0Obj : (0 _ : Type) -> Type
CofreeS0Obj = CofreeCM S0ObjF

public export
S0Obj : Type
S0Obj = MuF S0ObjF

public export
InfS0Obj : Type
InfS0Obj = NuF S0ObjF

public export
S0ObjInitial : {0 carrier : Type} -> FreeS0Obj carrier
S0ObjInitial = InFCom S0InitialF

public export
S0ObjTerminal : {0 carrier : Type} -> FreeS0Obj carrier
S0ObjTerminal = InFCom S0TerminalF

public export
S0ObjCoproduct : {0 carrier : Type} ->
  FreeS0Obj carrier -> FreeS0Obj carrier -> FreeS0Obj carrier
S0ObjCoproduct = InFCom .* S0CoproductF

public export
S0ObjProduct : {0 carrier : Type} ->
  FreeS0Obj carrier -> FreeS0Obj carrier -> FreeS0Obj carrier
S0ObjProduct = InFCom .* S0ProductF

public export
record S0ObjAlg (a : Type) where
  constructor MkS0ObjAlg
  soAlgInitial : a
  soAlgTerminal : a
  soAlgCoproduct : a -> a -> a
  soAlgProduct : a -> a -> a

public export
S0ObjDiagAlg : Type -> Type
S0ObjDiagAlg a = S0ObjAlg (S0ObjAlg a)

-- The slice category of `FreeS0Obj v` within `Type`.
public export
FreeS0Slice : (0 _ : Type) -> Type
FreeS0Slice v = FreeS0Obj v -> Type

-- The slice category of `(FreeS0Obj v) x (FreeS0Obj v)` within `Type`.
public export
FreeS0PairSlice : (0 _, _ : Type) -> Type
FreeS0PairSlice v v' = FreeS0Obj v -> FreeS0Obj v' -> Type

public export
FreeS0SliceAlg : Type
FreeS0SliceAlg = S0ObjAlg Type

public export
s0ObjFreeCata : {0 v, a : Type} ->
  S0ObjAlg a -> (v -> a) -> FreeS0Obj v -> a
s0ObjFreeCata alg subst (InFreeM e) = case e of
  InVar var => subst var
  InCom S0InitialF => soAlgInitial alg
  InCom S0TerminalF => soAlgTerminal alg
  InCom (S0CoproductF x y) =>
    soAlgCoproduct alg
      (s0ObjFreeCata alg subst x)
      (s0ObjFreeCata alg subst y)
  InCom (S0ProductF x y) =>
    soAlgProduct alg
      (s0ObjFreeCata alg subst x)
      (s0ObjFreeCata alg subst y)

public export
s0ObjFreeDiagCata : {0 algv, v, a : Type} ->
  S0ObjDiagAlg a -> (algv -> S0ObjAlg a) -> (v -> a) ->
  FreeS0Obj algv -> FreeS0Obj v -> a
s0ObjFreeDiagCata {v} {a} alg algsubst subst x y =
  s0ObjFreeCata (s0ObjFreeCata alg algsubst x) subst y

public export
s0ObjCata : {0 a : Type} -> S0ObjAlg a -> S0Obj -> a
s0ObjCata {a} alg = s0ObjFreeCata {a} {v=Void} alg (voidF a)

public export
s0ObjDiagCata : {0 a : Type} -> S0ObjDiagAlg a -> S0Obj -> S0Obj -> a
s0ObjDiagCata {a} alg =
  s0ObjFreeDiagCata {a} {v=Void} {algv=Void} alg (voidF (S0ObjAlg a)) (voidF a)

-- Generate a type family indexed by the type of objects of the
-- zeroth-order substitution category -- in other words, an object
-- of the slice category of the zeroth-order substitution category
-- within `Type`.
--
-- It might be more fruitful and analogous to dependent type theory,
-- however, to view it categorially instead as a functor from the
-- term category of `FreeS0Obj v` to `Type`.
public export
s0slice : FreeS0SliceAlg -> {0 v : Type} -> (v -> Type) -> FreeS0Slice v
s0slice alg = s0ObjFreeCata {a=Type} alg

public export
s0ObjDepthAlg : S0ObjAlg Nat
s0ObjDepthAlg = MkS0ObjAlg Z Z (S .* max) (S .* max)

public export
s0ObjDepth : {0 v : Type} -> (v -> Nat) -> FreeS0Obj v -> Nat
s0ObjDepth = s0ObjFreeCata s0ObjDepthAlg

public export
s0ObjCardAlg : S0ObjAlg Nat
s0ObjCardAlg = MkS0ObjAlg Z (S Z) (+) (*)

public export
s0ObjCard : {0 v : Type} -> (v -> Nat) -> FreeS0Obj v -> Nat
s0ObjCard = s0ObjFreeCata s0ObjCardAlg

-- Interpret `FreeS0Obj v` into `Type`.  In other words, generate a type
-- family indexed by terms of `FreeS0Obj v` where the type at each index
-- is an inpretation within `Type` of the index (which is a term of
-- `FreeS0Obj v`).
public export
s0ObjTrAlg : FreeS0SliceAlg
s0ObjTrAlg = MkS0ObjAlg Void Unit Either Pair

public export
s0ObjTerm : {0 v : Type} -> (v -> Type) -> FreeS0Slice v
s0ObjTerm = s0slice s0ObjTrAlg

-- For any object `x` of the zeroth-order substitution category, a
-- `FreeS0DepSet x` is a type which depends on `x`.  In dependent
-- type theory, it's a function which takes terms of `x` to types -- that
-- is, a term of the type of functions from `x` to `Type`.  In category
-- theory, it's an object of the slice category of `x` -- category theory
-- turns the dependent-type view backwards, by viewing the whole type
-- family as a single object, with a morphism from that object to `x`
-- which can be viewed as indicating, for each term of the whole type
-- family, which term of `x` that particular term's type came from.
--
-- The term-category view is that `FreeS0DepSet x` is a functor from the
-- term category of our interpretation of `x` into `Type` to `Type` itself.
public export
FreeS0DepSet : {0 v : Type} -> (v -> Type) -> FreeS0Slice v
FreeS0DepSet {v} subst x = s0ObjTerm {v} subst x -> Type

-- For any objects `x` and `y` of the zeroth-order substitution category, a
-- `FreeS0PairDepSet x y` is a type which depends on `x` and `y`.  In dependent
-- type theory, it's a function which takes terms of `(x, y)` to types -- that
-- is, a term of the type of functions from `(x, y)` to `Type`.  In category
-- theory, it's an object of the slice category of `(x, y)`, or, in the
-- term-category interpretation, a functor from the term category of
-- our interpretation of `(x, y)` to `Type`.  Our interpretation of `(x, y)`
-- is simply the product of our interpretations of `x` and `y`, so the term
-- category of our interpretation of `(x, y)` is just the term category of
-- the product of the term categories of our interpretations.
public export
FreeS0PairDepSet : {0 v, v' : Type} ->
  (v -> Type) -> (v' -> Type) -> FreeS0PairSlice v v'
FreeS0PairDepSet {v} {v'} subst subst' x y =
  s0ObjTerm {v} subst x -> s0ObjTerm {v=v'} subst' y -> Type

-- An algebra which produces a `FreeS0DepSet` for every object of
-- the zeroth-order substitution category.
--
-- This algebra can therefore be viewed as a generator of a
-- dependent functor -- a functor which takes each object `x` of
-- the zero-order substitution category not to an object of just
-- one other given category but to an object of the slice category
-- of that particular `x`.  (We will specifically use it to generate
-- dependent _polynomial_ functors.)
--
-- In the term-category view, this algebra generates a dependent functor
-- which takes an object of the zeroth-order substitution category to the
-- category of functors from that object's term category to `Type`.
-- A dependent functor may in turn be viewed as a dependent product in a
-- higher category.
public export
record FreeS0DepAlg where
  constructor MkFreeS0DepAlg
  fs0unit : Type
  fs0left : Type -> Type
  fs0right : Type -> Type
  fs0pair : Type -> Type -> Type

-- Returns a `FreeDep0Set x` for every object `x` of the zeroth-order
-- substitution category.
--
-- See the comment to `FreeS0DepAlg` for an interpretation of this function.
public export
freeS0DepSet : FreeS0DepAlg ->
  {0 v : Type} -> (subst : v -> Type) ->
  (depsubst : (var : v) -> subst var -> Type) ->
  (x : FreeS0Obj v) -> FreeS0DepSet subst x
freeS0DepSet alg subst depsubst (InFreeM (InVar var)) =
  depsubst var
freeS0DepSet alg subst depsubst (InFreeM (InCom S0InitialF)) =
  voidF Type
freeS0DepSet alg subst depsubst (InFreeM (InCom S0TerminalF)) =
  \u => case u of () => fs0unit alg
freeS0DepSet alg subst depsubst (InFreeM (InCom (S0CoproductF x y))) =
  \e => case e of
    Left l => fs0left alg (freeS0DepSet alg subst depsubst x l)
    Right r => fs0right alg (freeS0DepSet alg subst depsubst y r)
freeS0DepSet alg subst depsubst (InFreeM (InCom (S0ProductF x y))) =
  \p => case p of
    (l, r) =>
      fs0pair alg
        (freeS0DepSet alg subst depsubst x l)
        (freeS0DepSet alg subst depsubst y r)

------------------------
------------------------
---- List utilities ----
------------------------
------------------------

public export
listFoldTailRec : {0 a, b : Type} -> (a -> b -> b) -> b -> List a -> b
listFoldTailRec op x [] = x
listFoldTailRec op x (x' :: xs) = listFoldTailRec op (op x' x) xs

---------------------
---------------------
---- Polynomials ----
---------------------
---------------------

public export
PolyTerm : Type
PolyTerm = (Nat, Nat)

public export
ptPow : PolyTerm -> Nat
ptPow = fst

public export
ptCoeff : PolyTerm -> Nat
ptCoeff = snd

-- A list of (power, coefficient) pairs.
public export
PolyShape : Type
PolyShape = List PolyTerm

public export
validPT : DecPred (Nat, Nat)
validPT t = ptCoeff t /= 0

-- We define a valid (normalized) polynomial shape as follows:
--   - The shape of the polynomial is a list of pairs of natural numbers,
--     where each list element represents a term (monomial), and the
--     pair represents (power, coefficient)
--   - Entries are sorted by strictly descending power
--   - There are no entries for powers with zero coefficients
-- Consequences of these rules include:
--  - Equality of valid polynomials is equality of underlying shapes
--  - The tail of a valid polynomial is always valid
--  - The meaning of an entry (a term) is independent of which list
--    it appears in, and thus can be determined by looking at the term
--    in isolation
--  - The degree of the polynomial is the left element of the head of the
--    list (or zero if the list is empty)
public export
validPoly : DecPred PolyShape
validPoly (t :: ts@(t' :: _)) =
  if (validPT t && ptPow t > ptPow t') then validPoly ts else False
validPoly [t] = validPT t
validPoly [] = True

public export
Polynomial : Type
Polynomial = Refinement {a=PolyShape} validPoly

public export
ValidPoly : PolyShape -> Type
ValidPoly = Satisfies validPoly

public export
MkPolynomial :
  (shape : PolyShape) -> {auto 0 valid : validPoly shape = True} -> Polynomial
MkPolynomial shape {valid} = MkRefinement {a=PolyShape} shape {satisfies=valid}

public export
headPow : PolyShape -> Nat
headPow (t :: ts) = ptPow t
headPow [] = 0

public export
degree : Polynomial -> Nat
degree = headPow . shape

public export
accumPTCoeff : Nat -> PolyShape -> Nat
accumPTCoeff = foldl ((|>) ptCoeff . (+))

public export
sumPTCoeff : PolyShape -> Nat
sumPTCoeff = accumPTCoeff 0

public export
sumCoeff : Polynomial -> Nat
sumCoeff = sumPTCoeff . shape

public export
psIdx : PolyShape -> Nat -> Nat
psIdx [] _ = 0
psIdx ((_, Z) :: ts) n = psIdx ts n
psIdx ((p, S c) :: ts) Z = p
psIdx ((p, S c) :: ts) (S n) = psIdx ((p, c) :: ts) n

public export
pIdx : Polynomial -> Nat -> Nat
pIdx = psIdx . shape

public export
psPosFoldStartingAt : {0 x : Type} ->
  ((pos, pow : Nat) -> x -> x) -> x -> (pos : Nat) -> PolyShape -> x
psPosFoldStartingAt f acc pos [] = acc
psPosFoldStartingAt f acc pos ((pow, c) :: ts) =
  psPosFoldStartingAt f (repeatIdx (flip f pow) c pos acc) (pos + c) ts

public export
psPosFold : {0 x : Type} -> ((pos, pow : Nat) -> x -> x) -> x -> PolyShape -> x
psPosFold f acc = psPosFoldStartingAt f acc 0

-- For each position, show the number of directions at that position
-- (that is, the power).
public export
psPosShow : PolyShape -> String
psPosShow =
  psPosFold
    (\pos, pow, str =>
      let pre = if (pos == 0) then "" else str ++ "; " in
      pre ++ "pos[" ++ show pos ++ "] = " ++ show pow)
    ""

public export
pIdxFold : {0 x : Type} -> ((pos, pow : Nat) -> x -> x) -> x -> Polynomial -> x
pIdxFold f acc = psPosFold f acc . shape

public export
sumPSDir : PolyShape -> Nat
sumPSDir = psPosFold (const (+)) 0

public export
sumPolyDir : Polynomial -> Nat
sumPolyDir = sumPSDir . shape

public export
numTerms : Polynomial -> Nat
numTerms = length . shape

-- Parameters: (accumulator, power, input).
-- Performs exponentiation by breaking it down into individual multiplications.
public export
ptInterpNatAccum : Nat -> Nat -> Nat -> Nat
ptInterpNatAccum acc (S p) n = ptInterpNatAccum (n * acc) p n
ptInterpNatAccum acc Z n = acc

public export
ptInterpNatByMults : PolyTerm -> Nat -> Nat
ptInterpNatByMults t = ptInterpNatAccum (ptCoeff t) (ptPow t) -- acc == coeff

-- Performs exponentiation using built-in power function.
public export
ptInterpNat : PolyTerm -> Nat -> Nat
ptInterpNat t n = (ptCoeff t) * power n (ptPow t)

public export
psInterpNatAccum : Nat -> PolyShape -> Nat -> Nat
psInterpNatAccum acc (t :: ts) n = psInterpNatAccum (ptInterpNat t n + acc) ts n
psInterpNatAccum acc [] n = acc

public export
psInterpNat : PolyShape -> Nat -> Nat
psInterpNat = psInterpNatAccum 0

public export
psMin : PolyShape -> Nat
psMin = flip psInterpNat 0

public export
psMax : PolyShape -> Nat -> Nat
psMax = psInterpNat

public export
polyInterpNat : Polynomial -> Nat -> Nat
polyInterpNat = psInterpNat . shape

public export
polyMin : Polynomial -> Nat
polyMin = psMin . shape

public export
polyMax : Polynomial -> Nat -> Nat
polyMax = psMax . shape

-- Possible future developments:
  -- arenas w/bijections (unless I can implement all formulas without this)
  -- lenses / natural transformations w/bijections
  -- horizontal & vertical composition of NTs
  -- eval (i.e. for exponential)
  -- equalizer
  -- coequalizer
  -- eval for parallel product
  -- derivative (as one-hole context)
  -- plugging in (to one-hole context)
  -- p-p0, and iteration of it

-----------------------------------
---- Arithmetic on polynomials ----
-----------------------------------

public export
initialPolyShape : PolyShape
initialPolyShape = []

public export
initialPoly : Polynomial
initialPoly = MkPolynomial initialPolyShape

public export
terminalPolyShape : PolyShape
terminalPolyShape = [(0, 1)]

public export
terminalPoly : Polynomial
terminalPoly = MkPolynomial terminalPolyShape

public export
idPolyShape : PolyShape
idPolyShape = [(1, 1)]

public export
idPoly : Polynomial
idPoly = MkPolynomial idPolyShape

public export
homNPolyShape : Nat -> PolyShape
homNPolyShape n = [(n, 1)]

public export
homNPoly : Nat -> Polynomial
homNPoly n = Element0 (homNPolyShape n) Refl

public export
constPolyShape : Nat -> PolyShape
constPolyShape Z = []
constPolyShape n@(S _) = [(0, n)]

public export
constPoly : Nat -> Polynomial
constPoly n = Element0 (constPolyShape n) ?constPolyCorrect_hole

public export
prodIdPolyShape : Nat -> PolyShape
prodIdPolyShape Z = []
prodIdPolyShape n@(S _) = [(1, n)]

public export
prodIdPoly : Nat -> Polynomial
prodIdPoly n = Element0 (prodIdPolyShape n) ?prodIdPolyCorrect_hole

-- Multiply by a monomial.
public export
scaleMonPolyRevAcc : PolyTerm -> PolyShape -> PolyShape -> PolyShape
scaleMonPolyRevAcc (_, Z) acc _ = []
scaleMonPolyRevAcc (pm, n@(S _)) acc [] = acc
scaleMonPolyRevAcc (pm, n@(S _)) acc ((p, c) :: ts) =
  scaleMonPolyRevAcc (pm, n) ((pm + p, n * c) :: acc) ts

public export
scaleMonPolyRev : PolyTerm -> PolyShape -> PolyShape
scaleMonPolyRev pt = scaleMonPolyRevAcc pt []

public export
scaleMonPolyShape : PolyTerm -> PolyShape -> PolyShape
scaleMonPolyShape pt = reverse . scaleMonPolyRev pt

public export
0 scalePreservesValid : {0 pt : PolyTerm} -> {0 poly : PolyShape} ->
  ValidPoly poly -> ValidPoly (scaleMonPolyShape pt poly)
scalePreservesValid {pt} {poly} valid = ?scaleMonPolyShapeCorrect_hole

public export
scaleMonPoly : PolyTerm -> Polynomial -> Polynomial
scaleMonPoly pt (Element0 poly valid) =
  Element0 (scaleMonPolyShape pt poly) (scalePreservesValid valid)

public export
scaleNatPolyShape : Nat -> PolyShape -> PolyShape
scaleNatPolyShape n = scaleMonPolyShape (0, n)

public export
scaleNatPoly : Nat -> Polynomial -> Polynomial
scaleNatPoly n = scaleMonPoly (0, n)

public export
parProdMonPolyRevAcc : PolyTerm -> PolyShape -> PolyShape -> PolyShape
parProdMonPolyRevAcc (_, Z) acc _ = []
parProdMonPolyRevAcc (pm, n@(S _)) acc [] = acc
parProdMonPolyRevAcc (pm, n@(S _)) acc ((p, c) :: ts) =
  parProdMonPolyRevAcc (pm, n) ((pm * p, n * c) :: acc) ts

public export
parProdMonPolyRev : PolyTerm -> PolyShape -> PolyShape
parProdMonPolyRev pt = parProdMonPolyRevAcc pt []

public export
parProdMonPolyShape : PolyTerm -> PolyShape -> PolyShape
parProdMonPolyShape (Z, c) poly = [(0, c * sumPTCoeff poly)]
parProdMonPolyShape pt@(S _, _) poly = reverse (parProdMonPolyRev pt poly)

public export
0 parProdMonPreservesValid : {0 pt : PolyTerm} -> {0 poly : PolyShape} ->
  ValidPoly poly -> ValidPoly (parProdMonPolyShape pt poly)
parProdMonPreservesValid {pt} {poly} valid = ?parProdMonPolyShapeCorrect_hole

public export
parProdMonPoly : PolyTerm -> Polynomial -> Polynomial
parProdMonPoly pt (Element0 poly valid) =
  Element0 (parProdMonPolyShape pt poly) (parProdMonPreservesValid valid)

public export
polyShapeBinOpRevAccN :
  (rOnly, lOnly : PolyTerm -> Maybe PolyTerm) ->
  (rGTl, lGTr : PolyTerm -> PolyTerm -> Maybe PolyTerm) ->
  (rEQl : (pow, coeffL, coeffR : Nat) -> Maybe PolyTerm) ->
  Nat -> PolyShape -> PolyShape -> PolyShape -> PolyShape
polyShapeBinOpRevAccN rOnly lOnly rGTl lGTr rEQl n acc polyL polyR =
  polyShapeBinOpRevAccNInternal n acc polyL polyR where
    polyShapeBinOpRevAccNInternal :
      Nat -> PolyShape -> PolyShape -> PolyShape -> PolyShape
    polyShapeBinOpRevAccNInternal Z acc _ _ = acc
    polyShapeBinOpRevAccNInternal (S n) acc [] [] = acc
    polyShapeBinOpRevAccNInternal (S n) acc [] (t@(p, c) :: ts) =
      case rOnly t of
        Just rt => polyShapeBinOpRevAccNInternal n (rt :: acc) [] ts
        Nothing => polyShapeBinOpRevAccNInternal n acc [] ts
    polyShapeBinOpRevAccNInternal (S n) acc (t@(p, c) :: ts) [] =
      case lOnly t of
        Just lt => polyShapeBinOpRevAccNInternal n (lt :: acc) ts []
        Nothing => polyShapeBinOpRevAccNInternal n acc ts []
    polyShapeBinOpRevAccNInternal (S n) acc
      q@(t@(p, c) :: ts) r@(t'@(p', c') :: ts') =
        case compare p p' of
          EQ =>
            case rEQl p c c' of
              Just eqt => polyShapeBinOpRevAccNInternal n (eqt :: acc) ts ts'
              Nothing => polyShapeBinOpRevAccNInternal n acc ts ts'
          LT =>
            case rGTl t t' of
              Just rt => polyShapeBinOpRevAccNInternal n (rt :: acc) q ts'
              Nothing => polyShapeBinOpRevAccNInternal n acc q ts'
          GT =>
            case lGTr t t' of
              Just lt => polyShapeBinOpRevAccNInternal n (lt :: acc) ts r
              Nothing => polyShapeBinOpRevAccNInternal n acc ts r

public export
polyShapeBinOpRevAcc :
  (rOnly, lOnly : PolyTerm -> Maybe PolyTerm) ->
  (rGTl, lGTr : PolyTerm -> PolyTerm -> Maybe PolyTerm) ->
  (rEQl : (pow, coeffL, coeffR : Nat) -> Maybe PolyTerm) ->
  PolyShape -> PolyShape -> PolyShape -> PolyShape
polyShapeBinOpRevAcc rOnly lOnly rGTl lGTr rEQl acc p q =
  polyShapeBinOpRevAccN rOnly lOnly rGTl lGTr rEQl (length p + length q) acc p q

public export
addPolyShapeRevAcc : PolyShape -> PolyShape -> PolyShape -> PolyShape
addPolyShapeRevAcc =
  polyShapeBinOpRevAcc
    Just
    Just
    (\t, t' => Just t')
    (\t, t' => Just t)
    (\p, c, c' => Just (p, c + c'))

public export
addPolyShapeRev : PolyShape -> PolyShape -> PolyShape
addPolyShapeRev = addPolyShapeRevAcc []

public export
addPolyShape : PolyShape -> PolyShape -> PolyShape
addPolyShape p q = reverse (addPolyShapeRev p q)

public export
0 addPreservesValid : {0 p, q : PolyShape} ->
  ValidPoly p -> ValidPoly q -> ValidPoly (addPolyShape p q)
addPreservesValid {p} {q} pvalid qvalid = ?addPolyShapeCorrect_hole

public export
addPoly : Polynomial -> Polynomial -> Polynomial
addPoly (Element0 p pvalid) (Element0 q qvalid) =
  Element0 (addPolyShape p q) (addPreservesValid pvalid qvalid)

public export
addPolyShapeList : List PolyShape -> PolyShape
addPolyShapeList = listFoldTailRec addPolyShape initialPolyShape

public export
addMapPolyShapeList :
  (PolyTerm -> PolyShape -> PolyShape) -> PolyShape -> PolyShape -> PolyShape
addMapPolyShapeList op p =
  listFoldTailRec (addPolyShape . flip op p) initialPolyShape

public export
mulPolyShape : PolyShape -> PolyShape -> PolyShape
mulPolyShape = addMapPolyShapeList scaleMonPolyShape

public export
0 mulPreservesValid : {0 p, q : PolyShape} ->
  ValidPoly p -> ValidPoly q -> ValidPoly (mulPolyShape p q)
mulPreservesValid {p} {q} pvalid qvalid = ?mulPolyShapeCorrect_hole

public export
mulPoly : Polynomial -> Polynomial -> Polynomial
mulPoly (Element0 p pvalid) (Element0 q qvalid) =
  Element0 (mulPolyShape p q) (mulPreservesValid pvalid qvalid)

public export
mulPolyShapeList : List PolyShape -> PolyShape
mulPolyShapeList = listFoldTailRec mulPolyShape terminalPolyShape

public export
parProdPolyShape : PolyShape -> PolyShape -> PolyShape
parProdPolyShape = addMapPolyShapeList parProdMonPolyShape

public export
0 parProdPreservesValid : {0 p, q : PolyShape} ->
  ValidPoly p -> ValidPoly q -> ValidPoly (parProdPolyShape p q)
parProdPreservesValid {p} {q} pvalid qvalid = ?parProdPolyShapeCorrect_hole

public export
parProdPoly : Polynomial -> Polynomial -> Polynomial
parProdPoly (Element0 p pvalid) (Element0 q qvalid) =
  Element0 (parProdPolyShape p q) (parProdPreservesValid pvalid qvalid)

public export
parProdPolyShapeList : List PolyShape -> PolyShape
parProdPolyShapeList = listFoldTailRec parProdPolyShape idPolyShape

public export
expNPolyShape : Nat -> PolyShape -> PolyShape
expNPolyShape Z _ = terminalPolyShape
expNPolyShape (S n) p = mulPolyShape p (expNPolyShape n p)

public export
0 expNPreservesValid : {0 n : Nat} -> {0 poly : PolyShape} ->
  ValidPoly poly -> ValidPoly (expNPolyShape n poly)
expNPreservesValid {n} {poly} valid = ?expNPolyShapeCorrect_hole

public export
expNPoly : Nat -> Polynomial -> Polynomial
expNPoly n (Element0 poly valid) =
  Element0 (expNPolyShape n poly) (expNPreservesValid valid)

public export
composeMonPoly : PolyTerm -> PolyShape -> PolyShape
composeMonPoly (p, c) poly = scaleNatPolyShape c $ expNPolyShape p poly

public export
composePolyShape : PolyShape -> PolyShape -> PolyShape
composePolyShape = flip (addMapPolyShapeList composeMonPoly)

public export
0 composePreservesValid : {0 p, q : PolyShape} ->
  ValidPoly q -> ValidPoly p -> ValidPoly (composePolyShape q p)
composePreservesValid {p} {q} pvalid qvalid = ?composePolyShapeCorrect_hole

public export
composePoly : Polynomial -> Polynomial -> Polynomial
composePoly (Element0 q qvalid) (Element0 p pvalid) =
  Element0 (composePolyShape q p) (composePreservesValid qvalid pvalid)

export infixr 1 <|
public export
(<|) : Polynomial -> Polynomial -> Polynomial
(<|) = composePoly

export infixr 1 |>
public export
(|>) : Polynomial -> Polynomial -> Polynomial
(|>) = flip (<|)

public export
iterNPolyShape : Nat -> PolyShape -> PolyShape
iterNPolyShape n p = foldrNat (composePolyShape p) terminalPolyShape n

public export
0 iterNPreservesValid : {0 n : Nat} -> {0 poly : PolyShape} ->
  ValidPoly poly -> ValidPoly (iterNPolyShape n poly)
iterNPreservesValid {n} {poly} valid = ?iterNPolyShapeCorrect_hole

public export
iterNPoly : Nat -> Polynomial -> Polynomial
iterNPoly n (Element0 poly valid) =
  Element0 (iterNPolyShape n poly) (iterNPreservesValid valid)

public export
psSumOverIdx : (Nat -> PolyShape) -> PolyShape -> PolyShape
psSumOverIdx f = psPosFold (const $ addPolyShape . f) initialPolyShape

public export
psProductOverIdx : (Nat -> PolyShape) -> PolyShape -> PolyShape
psProductOverIdx f = psPosFold (const $ mulPolyShape . f) terminalPolyShape

public export
polyShapeClosure :
  (PolyShape -> PolyShape -> PolyShape) -> PolyShape -> PolyShape -> PolyShape
polyShapeClosure f q r =
  psProductOverIdx (composePolyShape r . f idPolyShape . constPolyShape) q

public export
polyShapeHomObj : PolyShape -> PolyShape -> PolyShape
polyShapeHomObj = polyShapeClosure addPolyShape

public export
polyShapeExponential : PolyShape -> PolyShape -> PolyShape
polyShapeExponential = flip polyShapeHomObj

public export
parProdClosureShape : PolyShape -> PolyShape -> PolyShape
parProdClosureShape = polyShapeClosure mulPolyShape

public export
leftCoclosureShape : PolyShape -> PolyShape -> PolyShape
leftCoclosureShape r p = psSumOverIdx (homNPolyShape . psInterpNat r) p

--------------------------
--------------------------
---- Polynomial types ----
--------------------------
--------------------------

public export
NatRange : Type
NatRange = (Nat, Nat)

public export
validRange : DecPred NatRange
validRange (m, n) = m <= n

public export
betweenPred : Nat -> Nat -> DecPred Nat
betweenPred min max n = (min <= n) && (n <= max)

public export
BetweenTrue : Nat -> Nat -> Nat -> Type
BetweenTrue min max n = IsTrue (betweenPred min max n)

-- All natural numbers between `min` and `max` inclusive.
public export
RangedNat : Nat -> Nat -> Type
RangedNat min max = Refinement (betweenPred min max)

public export
MkRangedNat : {0 min, max : Nat} ->
  (m : Nat) -> {auto 0 between : BetweenTrue min max m} -> RangedNat min max
MkRangedNat m {between} = MkRefinement m {satisfies=between}

public export
psInterpRange : PolyShape -> NatRange -> NatRange
psInterpRange = mapHom {f=Pair} . psInterpNat

public export
polyInterpRange : Polynomial -> NatRange -> NatRange
polyInterpRange = psInterpRange . shape

public export
0 idPSCorrect : (0 range : NatRange) ->
  psInterpRange PolyCat.idPolyShape range = range
idPSCorrect (min, max) = ?idPsCorrect_hole

--------------------------------
---- Morphisms on RangedNat ----
--------------------------------

public export
data RangedNatMorphF : Type -> Type where
  RNMComposeF : {0 carrier : Type} ->
    carrier -> carrier -> RangedNatMorphF carrier
  RNMPolyF : {0 carrier : Type} ->
    NatRange -> PolyShape -> RangedNatMorphF carrier
  RNMSwitchF : {0 carrier : Type} ->
    Nat -> carrier -> carrier -> RangedNatMorphF carrier
  RNMDivF : {0 carrier : Type} ->
    NatRange -> Nat -> RangedNatMorphF carrier
  RNMModF : {0 carrier : Type} ->
    NatRange -> Nat -> RangedNatMorphF carrier
  RNMExtendCodBelowF : {0 carrier : Type} ->
    carrier -> Nat -> RangedNatMorphF carrier
  RNMExtendCodAboveF : {0 carrier : Type} ->
    carrier -> Nat -> RangedNatMorphF carrier
  RNMRestrictDomBelowF : {0 carrier : Type} ->
    carrier -> Nat -> RangedNatMorphF carrier
  RNMRestrictDomAboveF : {0 carrier : Type} ->
    carrier -> Nat -> RangedNatMorphF carrier

public export
Functor RangedNatMorphF where
  map m (RNMComposeF g f) = RNMComposeF (m g) (m f)
  map m (RNMPolyF dom ps) = RNMPolyF dom ps
  map m (RNMSwitchF n l r) = RNMSwitchF n (m l) (m r)
  map m (RNMDivF dom n) = RNMDivF dom n
  map m (RNMModF dom n) = RNMModF dom n
  map m (RNMExtendCodBelowF f n) = RNMExtendCodBelowF (m f) n
  map m (RNMExtendCodAboveF f n) = RNMExtendCodAboveF (m f) n
  map m (RNMRestrictDomBelowF f n) = RNMRestrictDomBelowF (m f) n
  map m (RNMRestrictDomAboveF f n) = RNMRestrictDomAboveF (m f) n

public export
RNMSig : Type
RNMSig = (NatRange, NatRange)

public export
RNMAlg : Type -> Type
RNMAlg = FAlg RangedNatMorphF

public export
RNMDiagAlg : Type -> Type
RNMDiagAlg = DiagFAlg RangedNatMorphF

public export
rnmShowAlg : RNMAlg String
rnmShowAlg (RNMComposeF g f) = "(" ++ g ++ " . " ++ f ++ ")"
rnmShowAlg (RNMPolyF dom ps) =
  show ps ++ " : (" ++ show dom ++ " -> " ++ show (psInterpRange ps dom) ++ ")"
rnmShowAlg (RNMSwitchF n left right) =
  left ++ " | < " ++ show n ++ "<= | " ++ right
rnmShowAlg (RNMDivF range n) = show range ++ " / " ++ show n
rnmShowAlg (RNMModF range n) = show range ++ " % " ++ show n
rnmShowAlg (RNMExtendCodBelowF rnm n) = rnm ++ " < " ++ show n
rnmShowAlg (RNMExtendCodAboveF rnm n) = rnm ++ " > " ++ show n
rnmShowAlg (RNMRestrictDomBelowF rnm n) = show n ++ " > " ++ rnm
rnmShowAlg (RNMRestrictDomAboveF rnm n) = show n ++ " < " ++ rnm

public export
showRNMF : {0 x : Type} -> (shx : x -> String) -> RangedNatMorphF x -> String
showRNMF = (.) rnmShowAlg . map

public export
Show carrier => Show (RangedNatMorphF carrier) where
  show = showRNMF show

public export
MuRNM : Type
MuRNM = MuF RangedNatMorphF

public export
rnmCata : FromInitialFAlg RangedNatMorphF
rnmCata x alg (InFreeM $ InVar v) = void v
rnmCata x alg (InFreeM $ InCom c) = alg $ case c of
  RNMComposeF g f => RNMComposeF (rnmCata x alg g) (rnmCata x alg f)
  RNMPolyF dom ps => RNMPolyF dom ps
  RNMSwitchF n l r => RNMSwitchF n (rnmCata x alg l) (rnmCata x alg r)
  RNMDivF dom n => RNMDivF dom n
  RNMModF dom n => RNMModF dom n
  RNMExtendCodBelowF f n => RNMExtendCodBelowF (rnmCata x alg f) n
  RNMExtendCodAboveF f n => RNMExtendCodAboveF (rnmCata x alg f) n
  RNMRestrictDomBelowF f n => RNMRestrictDomBelowF (rnmCata x alg f) n
  RNMRestrictDomAboveF f n => RNMRestrictDomAboveF (rnmCata x alg f) n

public export
rnmDiagCata : FromInitialDiagFAlg RangedNatMorphF
rnmDiagCata = muDiagCata rnmCata

public export
rnmCheckAlg : RNMAlg (Maybe RNMSig)
rnmCheckAlg (RNMComposeF g f) = case (g, f) of
  (Just (domg, codg), Just (domf, codf)) =>
    if codf == domg then
      Just (domf, codg)
    else
      Nothing
  _ => Nothing
rnmCheckAlg (RNMPolyF dom ps) =
  if validRange dom && validPoly ps then
    Just $ (dom, psInterpRange ps dom)
  else
    Nothing
rnmCheckAlg (RNMSwitchF n left right) = case (left, right) of
  (Just ((domLeftMin, domLeftMax), codLeft),
   Just ((domRightMin, domRightMax), codRight)) =>
    if (S domLeftMax == n) && (domRightMin == n) && (codLeft == codRight) then
      Just ((domLeftMin, domRightMax), codLeft)
    else
      Nothing
  _ => Nothing
rnmCheckAlg (RNMDivF dom@(min, max) n) =
  case (validRange dom, divMaybe min n, divMaybe max n) of
    (True, Just min', Just max') =>
      Just (dom, (min', max'))
    _ => Nothing
rnmCheckAlg (RNMModF dom@(min, max) n) =
  if (validRange dom) && (n /= 0) && (n < max) then
    Just (dom, (0, pred n))
  else
    Nothing
rnmCheckAlg (RNMExtendCodBelowF f n) = case f of
  Just (dom, (min, max)) => if n < min then Just (dom, (n, max)) else Nothing
  Nothing => Nothing
rnmCheckAlg (RNMExtendCodAboveF f n) = case f of
  Just (dom, (min, max)) => if max < n then Just (dom, (min, n)) else Nothing
  Nothing => Nothing
rnmCheckAlg (RNMRestrictDomBelowF f n) = case f of
  Just ((min, max), cod) =>
    if (min < n) && (n < max) then Just ((n, max), cod) else Nothing
  Nothing => Nothing
rnmCheckAlg (RNMRestrictDomAboveF f n) = case f of
  Just ((min, max), cod) =>
    if (min < n) && (n < max) then Just ((min, n), cod) else Nothing
  Nothing => Nothing

public export
rnmCheck : MuRNM -> Maybe RNMSig
rnmCheck = rnmCata _ rnmCheckAlg

public export
Show MuRNM where
  show = rnmCata _ rnmShowAlg

public export
validRNM : DecPred MuRNM
validRNM = isJust . rnmCheck

public export
ValidRNM : MuRNM -> Type
ValidRNM = IsTrue . validRNM

public export
RefRNM : Type
RefRNM = Refinement validRNM

public export
MkRefRNM : (rnm : MuRNM) -> {auto 0 valid : ValidRNM rnm} -> RefRNM
MkRefRNM rnm {valid} = MkRefinement rnm {satisfies=valid}

public export
rnmRange : RefRNM -> RNMSig
rnmRange (Element0 rnm valid) with (rnmCheck rnm)
  rnmRange (Element0 rnm Refl) | Just range = range
  rnmRange (Element0 rnm Refl) | Nothing impossible

public export
RNMCompose : MuRNM -> MuRNM -> MuRNM
RNMCompose = InFCom .* RNMComposeF

public export
RNMPoly : NatRange -> PolyShape -> MuRNM
RNMPoly = InFCom .* RNMPolyF

public export
RNMSwitch : Nat -> MuRNM -> MuRNM -> MuRNM
RNMSwitch = InFCom .** RNMSwitchF

public export
RNMDiv : NatRange -> Nat -> MuRNM
RNMDiv = InFCom .* RNMDivF

public export
RNMMod : NatRange -> Nat -> MuRNM
RNMMod = InFCom .* RNMModF

public export
RNMExtendCodBelow : MuRNM -> Nat -> MuRNM
RNMExtendCodBelow = InFCom .* RNMExtendCodBelowF

public export
RNMExtendCodAbove : MuRNM -> Nat -> MuRNM
RNMExtendCodAbove = InFCom .* RNMExtendCodAboveF

public export
RNMRestrictDomBelow : MuRNM -> Nat -> MuRNM
RNMRestrictDomBelow = InFCom .* RNMRestrictDomBelowF

public export
RNMRestrictDomAbove : MuRNM -> Nat -> MuRNM
RNMRestrictDomAbove = InFCom .* RNMRestrictDomAboveF

public export
rnmId : NatRange -> MuRNM
rnmId range = RNMPoly range idPolyShape

public export
interpRNMAlg : RNMAlg (Nat -> Nat)
interpRNMAlg (RNMComposeF g f) = g . f
interpRNMAlg (RNMPolyF dom ps) = psInterpNat ps
interpRNMAlg (RNMSwitchF n left right) = \m => if m < n then left m else right m
interpRNMAlg (RNMDivF dom n) =
  \m => case divMaybe m n of
    Just p => p
    Nothing => 0
interpRNMAlg (RNMModF dom n) =
  \m => case modMaybe m n of
    Just p => p
    Nothing => 0
interpRNMAlg (RNMExtendCodBelowF f n) = f
interpRNMAlg (RNMExtendCodAboveF f n) = f
interpRNMAlg (RNMRestrictDomBelowF f n) = f
interpRNMAlg (RNMRestrictDomAboveF f n) = f

public export
interpRNM : MuRNM -> Nat -> Nat
interpRNM = rnmCata _ interpRNMAlg

---------------------------------------------
---- Possibly-empty ("augmented") ranges ----
---------------------------------------------

-- `Nothing` means an empty range (Void).
public export
AugNatRange : Type
AugNatRange = Maybe NatRange

-- `Left` means the unique morphism from Void to the given (augmented) range.
public export
AugRNM : Type
AugRNM = Either AugNatRange MuRNM

public export
AugRNMSig : Type
AugRNMSig = (AugNatRange, AugNatRange)

public export
arnmCheck : AugRNM -> Maybe AugRNMSig
arnmCheck (Left range) = Just (Nothing, range)
arnmCheck (Right rnm) = map {f=Maybe} (mapHom {f=Pair} Just) (rnmCheck rnm)

public export
arnmId : AugNatRange -> AugRNM
arnmId Nothing = Left Nothing
arnmId (Just range) = Right (rnmId range)

public export
arnmUnvalidatedCompose : AugRNM -> AugRNM -> AugRNM
arnmUnvalidatedCompose (Left r) _ = Left r -- right morphism must be id on Void
arnmUnvalidatedCompose (Right g) (Left r) = case rnmCheck g of
  Just (domg, codg) => Left $ Just codg
  Nothing => Left Nothing
arnmUnvalidatedCompose (Right g) (Right f) = Right $ RNMCompose g f

-- This function witnesses that a polynomial may be viewed as a functor
-- in the category whose objects are augmented ranges (terms of `AugNatRange`)
-- and whose morphisms are augmented range morphisms (terms of `AugRNM`).
public export
psApplyAugRange : PolyShape -> AugNatRange -> AugNatRange
psApplyAugRange = map {f=Maybe} . psInterpRange

-- This is the morphism map for the functor represented by a polynomial
-- (whose object map is given by `psApplyARNM` above).
public export
psApplyARNM : PolyShape -> AugRNM -> AugRNM
psApplyARNM ps rnm =
  case arnmCheck rnm of
    Just (Nothing, cod) =>
      Left $ psApplyAugRange ps cod
    Just (Just r, _) =>
      arnmUnvalidatedCompose (Right (RNMPoly r ps)) rnm
    Nothing =>
      Left Nothing

-------------------------------------
-------------------------------------
---- Bounded (finite) data types ----
-------------------------------------
-------------------------------------

---------------------------------
---- Bounded natural numbers ----
---------------------------------

public export
ltTrue : Nat -> Nat -> Type
ltTrue m n = (m < n) = True

public export
lteTrue : Nat -> Nat -> Type
lteTrue m n = (m <= n) = True

public export
gtTrue : Nat -> Nat -> Type
gtTrue m n = (m > n) = True

public export
gteTrue : Nat -> Nat -> Type
gteTrue m n = (m >= n) = True

-- All natural numbers less than or equal to `n`.
public export
BoundedNat : Nat -> Type
BoundedNat n = Refinement {a=Nat} ((>) n)

public export
MkBoundedNat : {0 n : Nat} ->
  (m : Nat) -> {auto 0 gt : gtTrue n m} -> BoundedNat n
MkBoundedNat m {gt} = MkRefinement m {satisfies=gt}

----------------------------------------
---- Tuples (fixed-length products) ----
----------------------------------------

public export
NTuple : Type -> Nat -> Type
NTuple a n = Refinement {a=(List a)} ((==) n . length)

public export
MkNTuple : {0 a : Type} -> (l : List a) -> NTuple a (length l)
MkNTuple l = MkRefinement l {satisfies=(equalNatCorrect {m=(length l)})}

--------------------------------------------
---- Fixed-width binary natural numbers ----
--------------------------------------------

public export
FixedNat : Nat -> Type
FixedNat = NTuple Digit

public export
toNat : {0 bits : Nat} -> FixedNat bits -> Nat
toNat = toNat . shape

-----------------------
---- Bounded lists ----
-----------------------

public export
BoundedList : Type -> Nat -> Type
BoundedList a n = Refinement {a=(List a)} ((>=) n . length)

public export
MkBoundedList : {0 a : Type} -> {0 n : Nat} ->
  (l : List a) -> {auto 0 gte : gteTrue n (length l)} -> BoundedList a n
MkBoundedList l {gte} = MkRefinement l {satisfies=gte}

-------------------------------------------
---- Natural transformations in `Poly` ----
-------------------------------------------

public export
psCoeffSet : PolyShape -> AugNatRange
psCoeffSet ps with (sumPTCoeff ps)
  psCoeffSet ps | Z = Nothing
  psCoeffSet ps | (S n) = Just (0, n)

public export
pCoeffSet : Polynomial -> AugNatRange
pCoeffSet = psCoeffSet . shape

public export
record PolyNTShape where
  constructor MkPNT
  psOnPos : AugRNM

public export
0 validPNTS : Polynomial -> Polynomial -> DecPred PolyNTShape
validPNTS p q nt = ?validate_PNTS_is_correct_hole

public export
PolyNT : Polynomial -> Polynomial -> Type
PolyNT p q = Refinement {a=PolyNTShape} (validPNTS p q)

-- Polynomials may be viewed as endofunctors in the category of ranges of
-- natural numbers, or of augmented ranges of natural numbers.  A
-- natural transformation between polynomials `p` and `q` therefore has one
-- component `m` for each augmented range `r`, where that `m` is a morphism --
-- hence a term of `AugRNM` -- from `p(r)` to `q(r)`.  (`p(r)` and `q(r)` are
-- the ranges computed by `psApplyAugRange`.)
public export
0 pntsComponent : PolyShape -> PolyShape -> PolyNTShape -> AugNatRange -> AugRNM
pntsComponent p q alpha range = ?pntsComponent_hole

--------------------------------------
--------------------------------------
---- Natural-number-indexed types ----
--------------------------------------
--------------------------------------

-----------------
---- Aliases ----
-----------------

-- Endomorphisms on a given object in the category `Type`.
public export
EndoM : Type -> Type
EndoM a = a -> a

-- Endomorphisms on `Nat` (within the category `Type`).
public export
NatEM : Type
NatEM = EndoM Nat

-- The identity on `Nat`.
public export
NatId : NatEM
NatId = Prelude.id {a=Nat}

-- Endomorphisms on `NatPair` (within the category `Type`).
public export
NPEM : Type
NPEM = EndoM NatPair

-- The identity on `NatPair`.
public export
NPId : NPEM
NPId = Prelude.id {a=NatPair}

--------------------------------------------------
---- Category of natural-number-indexed types ----
--------------------------------------------------

-- Objects of the category of natural-number-indexed types.
-- The index is erased -- it's used only for compiling proofs in
-- the metalanguage (which in this case is Idris-2).
public export
NITObj : Type
NITObj = CExists0 Nat Type

-- Morphisms of the category of natural-number-indexed types.
public export
NITMorph : Type
NITMorph = EndoM NITObj

-------------------------------------------
-------------------------------------------
---- Bounded-natural-number operations ----
-------------------------------------------
-------------------------------------------

-- The operations that form single-variable polynomials.
public export
data PolyOpF : Type -> Type where
  PolyIdF : PolyOpF carrier
  PolyConstF : Nat -> PolyOpF carrier
  PolyAddF : carrier -> carrier -> PolyOpF carrier
  PolyMulF : carrier -> carrier -> PolyOpF carrier

public export
Functor PolyOpF where
  map m PolyIdF = PolyIdF
  map m (PolyConstF n) = PolyConstF n
  map m (PolyAddF p q) = PolyAddF (m p) (m q)
  map m (PolyMulF p q) = PolyMulF (m p) (m q)

public export
POShowAlg : Algebra PolyOpF String
POShowAlg PolyIdF = "id"
POShowAlg (PolyConstF n) = show n
POShowAlg (PolyAddF p q) = "(" ++ p ++ ") + (" ++ q ++ ")"
POShowAlg (PolyMulF p q) = "(" ++ p ++ ") * (" ++ q ++ ")"

public export
FreePolyOpN : NatObj -> Type -> Type
FreePolyOpN = OmegaChain PolyOpF

public export
FreePolyOp : Type -> Type
FreePolyOp = OmegaColimit PolyOpF

public export
PolyOp : Type
PolyOp = InitialColimit PolyOpF

--------------------------------------------------------------
--------------------------------------------------------------
---- Inductive definition of substitutive types (objects) ----
--------------------------------------------------------------
--------------------------------------------------------------

export infixr 8 !!+
export infixr 9 !!*

public export
data SubstObjF : Type -> Type where
  -- Initial
  SO0 : SubstObjF carrier

  -- Terminal
  SO1 : SubstObjF carrier

  -- Coproduct
  (!!+) : carrier -> carrier -> SubstObjF carrier

  -- Product
  (!!*) : carrier -> carrier -> SubstObjF carrier

  -- Fin(n)
  SOn : (n : Nat) -> {auto 0 nz : NonZero n} -> SubstObjF carrier

public export
Functor SubstObjF where
  map m SO0 = SO0
  map m SO1 = SO1
  map m (x !!+ y) = m x !!+ m y
  map m (x !!* y) = m x !!* m y
  map m (SOn n {nz}) = SOn n {nz}

public export
MetaSOAlg : Type -> Type
MetaSOAlg x = SubstObjF x -> x

public export
MetaSOCoalg : Type -> Type
MetaSOCoalg x = x -> SubstObjF x

------------------------------------------------------------------------
---- Substitutive objects as least fixed point of generator functor ----
------------------------------------------------------------------------

public export
data SubstObjMu : Type where
  InSO : SubstObjF SubstObjMu -> SubstObjMu

export infixr 8 !+
export infixr 9 !*

public export
Subst0 : SubstObjMu
Subst0 = InSO SO0

public export
Subst1 : SubstObjMu
Subst1 = InSO SO1

public export
(!+) : SubstObjMu -> SubstObjMu -> SubstObjMu
(!+) = InSO .* (!!+)

public export
(!*) : SubstObjMu -> SubstObjMu -> SubstObjMu
(!*) = InSO .* (!!*)

public export
SubstN : (n : Nat) -> {auto 0 nz : NonZero n} -> SubstObjMu
SubstN n {nz} = InSO (SOn n {nz})

public export
SubstN1 : SubstObjMu
SubstN1 = SubstN 1 {nz=SIsNonZero}

public export
SubstBool : SubstObjMu
SubstBool = Subst1 !+ Subst1

public export
SubstMaybe : SubstObjMu -> SubstObjMu
SubstMaybe x = Subst1 !+ x

public export
substObjCata : MetaSOAlg x -> SubstObjMu -> x
substObjCata alg = substObjFold id where
  mutual
    substObjCataCont : (x -> x -> SubstObjF x) ->
      (x -> x) -> SubstObjMu -> SubstObjMu -> x
    substObjCataCont op cont p q =
      substObjFold
        (\p' => substObjFold (\q' => cont $ alg $ op p' q') q) p

    substObjFold : (x -> x) -> SubstObjMu -> x
    substObjFold cont (InSO p) = case p of
      SO0 => cont (alg SO0)
      SO1 => cont (alg SO1)
      p !!+ q => substObjCataCont (!!+) cont p q
      p !!* q => substObjCataCont (!!*) cont p q
      SOn n {nz} => cont (alg $ SOn n {nz})

public export
data SubstObjNu : Type where
  InSOLabel : Inf (SubstObjF SubstObjNu) -> SubstObjNu

public export
substObjAna : MetaSOCoalg x -> x -> Inf SubstObjNu
substObjAna coalg = substObjUnfold id where
  mutual
    substObjAnaCont : (SubstObjNu -> SubstObjNu -> SubstObjF SubstObjNu) ->
      (SubstObjNu -> SubstObjNu) -> x -> x -> SubstObjNu
    substObjAnaCont op cont x y =
      substObjUnfold
        (\x' => substObjUnfold (\y' => cont $ InSOLabel $ op x' y') y) x

    substObjUnfold : (SubstObjNu -> SubstObjNu) -> x -> Inf SubstObjNu
    substObjUnfold cont t = case coalg t of
      SO0 => cont (InSOLabel SO0)
      SO1 => cont (InSOLabel SO1)
      p !!+ q => substObjAnaCont (!!+) cont p q
      p !!* q => substObjAnaCont (!!*) cont p q
      SOn n {nz} => cont (InSOLabel $ SOn n {nz})

public export
SubstObjPairAlg : Type -> Type
SubstObjPairAlg x = MetaSOAlg (SubstObjMu -> x)

public export
substObjPairCata : SubstObjPairAlg x -> SubstObjMu -> SubstObjMu -> x
substObjPairCata = substObjCata

-------------------
---- Utilities ----
-------------------

public export
SOSizeAlg : MetaSOAlg Nat
SOSizeAlg SO0 = 1
SOSizeAlg SO1 = 1
SOSizeAlg (p !!+ q) = p + q
SOSizeAlg (p !!* q) = p + q
SOSizeAlg (SOn n) = 1

public export
substObjSize : SubstObjMu -> Nat
substObjSize = substObjCata SOSizeAlg

public export
SODepthAlg : MetaSOAlg Nat
SODepthAlg SO0 = 0
SODepthAlg SO1 = 0
SODepthAlg (p !!+ q) = smax p q
SODepthAlg (p !!* q) = smax p q
SODepthAlg (SOn n) = 0

public export
substObjDepth : SubstObjMu -> Nat
substObjDepth = substObjCata SODepthAlg

-- The cardinality of the type that would result from applying
-- the given substObjnomial to a type of the given cardinality.
public export
SOCardAlg : MetaSOAlg Nat
SOCardAlg SO0 = 0
SOCardAlg SO1 = 1
SOCardAlg (p !!+ q) = p + q
SOCardAlg (p !!* q) = p * q
SOCardAlg (SOn n) = n

public export
substObjCard : SubstObjMu -> Nat
substObjCard = substObjCata SOCardAlg

-----------------------------------------
---- Displaying substitutive objects ----
-----------------------------------------

public export
SOShowAlg : MetaSOAlg String
SOShowAlg SO0 = "0"
SOShowAlg SO1 = "1"
SOShowAlg (x !!+ y) = "(" ++ x ++ " + " ++ y ++ ")"
SOShowAlg (x !!* y) = x ++ " * " ++ y
SOShowAlg (SOn n) = "Fin(" ++ show n ++ ")"

public export
Show SubstObjMu where
  show = substObjCata SOShowAlg

------------------------------------------
---- Equality on substitutive objects ----
------------------------------------------

public export
SubstObjMuEqAlg : SubstObjPairAlg Bool
SubstObjMuEqAlg SO0 (InSO SO0) = True
SubstObjMuEqAlg SO0 _ = False
SubstObjMuEqAlg SO1 (InSO SO1) = True
SubstObjMuEqAlg SO1 _ = False
SubstObjMuEqAlg (p !!+ q) (InSO (r !!+ s)) = p r && q s
SubstObjMuEqAlg (p !!+ q) _ = False
SubstObjMuEqAlg (p !!* q) (InSO (r !!* s)) = p r && q s
SubstObjMuEqAlg (p !!* q) _ = False
SubstObjMuEqAlg (SOn m) (InSO (SOn n)) = m == n
SubstObjMuEqAlg (SOn m) _ = False

public export
Eq SubstObjMu where
  (==) = substObjPairCata SubstObjMuEqAlg

public export
substObjMuDecEq : (x, y : SubstObjMu) -> Dec (x = y)
substObjMuDecEq (InSO SO0) (InSO SO0) = Yes Refl
substObjMuDecEq (InSO SO0) (InSO SO1) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO SO0) (InSO (_ !!+ _)) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO SO0) (InSO (_ !!* _)) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO SO0) (InSO (SOn _)) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO SO1) (InSO SO0) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO SO1) (InSO SO1) = Yes Refl
substObjMuDecEq (InSO SO1) (InSO (_ !!+ _)) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO SO1) (InSO (_ !!* _)) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO SO1) (InSO (SOn _)) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO (_ !!+ _)) (InSO SO0) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO (_ !!+ _)) (InSO SO1) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO (w !!+ x)) (InSO (y !!+ z)) =
  case (substObjMuDecEq w y, substObjMuDecEq x z) of
    (Yes Refl, Yes Refl) => Yes Refl
    (Yes Refl, No neq) => No $ \eq => case eq of Refl => neq Refl
    (No neq, _) => No $ \eq => case eq of Refl => neq Refl
substObjMuDecEq (InSO (_ !!+ _)) (InSO (_ !!* _)) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO (_ !!+ _)) (InSO (SOn _)) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO (_ !!* _)) (InSO SO0) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO (_ !!* _)) (InSO SO1) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO (_ !!* _)) (InSO (y !!+ w)) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO (w !!* x)) (InSO (y !!* z)) =
  case (substObjMuDecEq w y, substObjMuDecEq x z) of
    (Yes Refl, Yes Refl) => Yes Refl
    (Yes Refl, No neq) => No $ \eq => case eq of Refl => neq Refl
    (No neq, _) => No $ \eq => case eq of Refl => neq Refl
substObjMuDecEq (InSO (_ !!* _)) (InSO (SOn _)) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO (SOn m)) (InSO SO0) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO (SOn m)) (InSO SO1) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO (SOn m)) (InSO (_ !!+ _)) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO (SOn m)) (InSO (_ !!* _)) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO (SOn m {nz=nzm})) (InSO (SOn n {nz=nzn})) =
  case decEq m n of
    Yes Refl => rewrite nzUnique nzm nzn in Yes Refl
    No neq => No $ \eq => case eq of Refl => neq Refl

public export
DecEq SubstObjMu where
  decEq = substObjMuDecEq

-----------------------------------------------
---- Normalization of substitutive objects ----
-----------------------------------------------

public export
SORemoveZeroAlg : MetaSOAlg SubstObjMu
SORemoveZeroAlg SO0 = Subst0
SORemoveZeroAlg SO1 = Subst1
SORemoveZeroAlg (p !!+ q) = case p of
  InSO p' => case p' of
    SO0 => q
    _ => case q of
      InSO q' => case q' of
        SO0 => p
        _ => p !+ q
SORemoveZeroAlg (p !!* q) = case p of
  InSO p' => case p' of
    SO0 => Subst0
    _ => case q of
      InSO q' => case q' of
        SO0 => Subst0
        _ => p !* q
SORemoveZeroAlg (SOn n) = InSO (SOn n)

public export
substObjRemoveZero : SubstObjMu -> SubstObjMu
substObjRemoveZero = substObjCata SORemoveZeroAlg

public export
SORemoveOneAlg : MetaSOAlg SubstObjMu
SORemoveOneAlg SO0 = Subst0
SORemoveOneAlg SO1 = Subst1
SORemoveOneAlg (p !!+ q) = p !+ q
SORemoveOneAlg (p !!* q) = case p of
  InSO p' => case p' of
    SO1 => q
    _ => case q of
      InSO q' => case q' of
        SO1 => p
        _ => p !* q
SORemoveOneAlg (SOn n) = InSO (SOn n)

public export
substObjRemoveOne : SubstObjMu -> SubstObjMu
substObjRemoveOne = substObjCata SORemoveOneAlg

public export
substObjNormalize : SubstObjMu -> SubstObjMu
substObjNormalize = substObjRemoveOne . substObjRemoveZero

-----------------------------------------------------
---- Multiplication by a constant (via addition) ----
-----------------------------------------------------

export infix 10 !:*
public export
(!:*) : Nat -> SubstObjMu -> SubstObjMu
n !:* p = foldrNatNoUnit ((!+) p) Subst0 p n

---------------------------------------
---- Multiplicative exponentiation ----
---------------------------------------

export infix 10 !*^
public export
(!*^) : SubstObjMu -> Nat -> SubstObjMu
p !*^ n = foldrNatNoUnit ((!*) p) Subst1 p n

----------------------------------------
---- Terms of substitutive category ----
----------------------------------------

public export
SubstTrAlg : MetaSOAlg Type
SubstTrAlg SO0 = Void
SubstTrAlg SO1 = ()
SubstTrAlg (x !!+ y) = Either x y
SubstTrAlg (x !!* y) = Pair x y
SubstTrAlg (SOn n) = Fin n

-- Variant from an algebra rather than explicit recursion
public export
SubstTerm' : SubstObjMu -> Type
SubstTerm' = substObjCata SubstTrAlg

-- Variant using explicit recursion
public export
SubstTerm : SubstObjMu -> Type
SubstTerm (InSO SO0) = Void
SubstTerm (InSO SO1) = ()
SubstTerm (InSO (x !!+ y)) = Either (SubstTerm x) (SubstTerm y)
SubstTerm (InSO (x !!* y)) = Pair (SubstTerm x) (SubstTerm y)
SubstTerm (InSO (SOn n)) = Fin n

public export
showSubstTerm : {x : SubstObjMu} -> SubstTerm x -> String
showSubstTerm {x=(InSO SO0)} t =
  void t
showSubstTerm {x=(InSO SO1)} t =
  "!"
showSubstTerm {x=(InSO (x !!+ y))} (Left t) =
  "L[" ++ showSubstTerm t ++ "]"
showSubstTerm {x=(InSO (x !!+ y))} (Right t) =
  "R[" ++ showSubstTerm t ++ "]"
showSubstTerm {x=(InSO (x !!* y))} (t, t') =
  "(" ++ showSubstTerm t ++ "," ++ showSubstTerm t' ++ ")"
showSubstTerm {x=(InSO (SOn n))} m =
  "(" ++ show m ++ "/" ++ show n ++ ")"

public export
(x : SubstObjMu) => Show (SubstTerm x) where
  show = showSubstTerm

public export
SubstContradictionAlg : MetaSOAlg Type
SubstContradictionAlg SO0 = ()
SubstContradictionAlg SO1 = Void
SubstContradictionAlg (x !!+ y) = Pair x y
SubstContradictionAlg (x !!* y) = Either x y
SubstContradictionAlg (SOn n) = Void

-- `SubstContradiction x` is inhabited if and only if `x` is uninhabited;
-- it is the dual of `SubstTerm x` (reflecting that a type is contradictory
-- if and only if it has no terms)
public export
SubstContradiction : SubstObjMu -> Type
SubstContradiction = substObjCata SubstContradictionAlg

-------------------------------------
---- Hom-objects from an algebra ----
-------------------------------------

public export
SubstHomObjAlgN : (n : Nat) -> (0 _ : NonZero n) -> SubstObjMu -> SubstObjMu
SubstHomObjAlgN Z SIsNonZero q impossible
SubstHomObjAlgN (S Z) SIsNonZero q = q
SubstHomObjAlgN (S (S n)) SIsNonZero q = q !* SubstHomObjAlgN (S n) SIsNonZero q

public export
SubstHomObjAlg : MetaSOAlg (SubstObjMu -> SubstObjMu)
-- 0 -> x == 1
SubstHomObjAlg SO0 _ = Subst1
-- 1 -> x == x
SubstHomObjAlg SO1 q = q
-- (p + q) -> r == (p -> r) * (q -> r)
SubstHomObjAlg (p !!+ q) r = p r !* q r
-- (p * q) -> r == p -> q -> r
SubstHomObjAlg (p !!* q) r = p $ q r
SubstHomObjAlg (SOn n {nz}) q = SubstHomObjAlgN n nz q

public export
SubstHomObj' : SubstObjMu -> SubstObjMu -> SubstObjMu
SubstHomObj' = substObjCata SubstHomObjAlg

---------------------------------------------
---- Morphisms from terms of hom-objects ----
---------------------------------------------

public export
SubstMorph' : SubstObjMu -> SubstObjMu -> Type
SubstMorph' = SubstTerm .* SubstHomObj'

-----------------------------
---- Universal morphisms ----
-----------------------------

export infixr 1 <!
public export
data SubstMorph : SubstObjMu -> SubstObjMu -> Type where
  SMId : (x : SubstObjMu) -> SubstMorph x x
  (<!) : {x, y, z : SubstObjMu} ->
    SubstMorph y z -> SubstMorph x y -> SubstMorph x z
  SMFromInit : (x : SubstObjMu) -> SubstMorph Subst0 x
  SMToTerminal : (x : SubstObjMu) -> SubstMorph x Subst1
  SMInjLeft : (x, y : SubstObjMu) -> SubstMorph x (x !+ y)
  SMInjRight : (x, y : SubstObjMu) -> SubstMorph y (x !+ y)
  SMCase : {x, y, z : SubstObjMu} ->
    SubstMorph x z -> SubstMorph y z -> SubstMorph (x !+ y) z
  SMPair : {x, y, z : SubstObjMu} ->
    SubstMorph x y -> SubstMorph x z -> SubstMorph x (y !* z)
  SMProjLeft : (x, y : SubstObjMu) -> SubstMorph (x !* y) x
  SMProjRight : (x, y : SubstObjMu) -> SubstMorph (x !* y) y
  SMDistrib : (x, y, z : SubstObjMu) ->
    SubstMorph (x !* (y !+ z)) ((x !* y) !+ (x !* z))
  SMNInj : (m, n : Nat) ->
    {auto 0 m_nz : NonZero m} -> {auto 0 n_nz : NonZero n} ->
    SubstMorph (SubstN m {nz=m_nz}) (SubstN n {nz=n_nz})
  SMNConst : (n : Nat) -> {auto 0 nz : NonZero n} ->
    Nat -> SubstMorph Subst1 (SubstN n {nz})
  SMNAdd : (n : Nat) -> {auto 0 nz : NonZero n} ->
    SubstMorph (SubstN n !* SubstN n) (SubstN n)
  SMNMult : (n : Nat) -> {auto 0 nz : NonZero n} ->
    SubstMorph (SubstN n !* SubstN n) (SubstN n)
  SMNSub : (n : Nat) -> {auto 0 nz : NonZero n} ->
    SubstMorph (SubstN n !* SubstN n) (SubstN n)
  SMNDiv : (n : Nat) -> {auto 0 nz : NonZero n} ->
    SubstMorph (SubstN n !* SubstN n) (SubstN n)
  SMNMod : (n : Nat) -> {auto 0 nz : NonZero n} ->
    SubstMorph (SubstN n !* SubstN n) (SubstN n)
  SMNEq : (n : Nat) -> {auto 0 nz : NonZero n} ->
    SubstMorph (SubstN n !* SubstN n) SubstBool
  SMNLt : (n : Nat) -> {auto 0 nz : NonZero n} ->
    SubstMorph (SubstN n !* SubstN n) SubstBool

public export
showSubstMorph : {x, y : SubstObjMu} -> SubstMorph x y -> String
showSubstMorph (SMId x) = "id{" ++ show x ++ "}"
showSubstMorph (g <! f) = showSubstMorph g ++ " . " ++ showSubstMorph f
showSubstMorph (SMFromInit x) = "{0 -> " ++ show x ++ "}"
showSubstMorph (SMToTerminal x) = "{" ++ show x ++ " -> 1}"
showSubstMorph (SMInjLeft x y) = "->Left<" ++ show x ++ " | " ++ show y ++ ">"
showSubstMorph (SMInjRight x y) = "->Right<" ++ show x ++ " | " ++ show y ++ ">"
showSubstMorph (SMCase f g) =
  "[" ++ showSubstMorph f ++ " | " ++ showSubstMorph g ++ "]"
showSubstMorph (SMPair f g) =
  "(" ++ showSubstMorph f ++ ", " ++ showSubstMorph g ++ ")"
showSubstMorph (SMProjLeft x y) = "<-Left<" ++ show x ++ ", " ++ show y ++ ">"
showSubstMorph (SMProjRight x y) = "<-Right<" ++ show x ++ ", " ++ show y ++ ">"
showSubstMorph (SMDistrib x y z) =
  "distrib{" ++ show x ++ ", " ++ show y ++ ", " ++ show z ++ "}"
showSubstMorph (SMNInj m n) = "inj{" ++ show m ++ ", " ++ show n ++ "}"
showSubstMorph (SMNConst n k) = "const{" ++ show k ++ " -> " ++ show n ++ "}"
showSubstMorph (SMNAdd n) = "+[%" ++ show n ++ "]"
showSubstMorph (SMNMult n) = "*[%" ++ show n ++ "]"
showSubstMorph (SMNSub n) = "-[%" ++ show n ++ "]"
showSubstMorph (SMNDiv n) = "/[%" ++ show n ++ "]"
showSubstMorph (SMNMod n) = "%[%" ++ show n ++ "]"
showSubstMorph (SMNEq n) = "?=[" ++ show n ++ "]"
showSubstMorph (SMNLt n) = "?<[" ++ show n ++ "]"

public export
SMParallel : {w, x, y, z : SubstObjMu} ->
  SubstMorph w y -> SubstMorph x z -> SubstMorph (w !* x) (y !* z)
SMParallel {w} {x} {y} {z} f g =
  SMPair (f <! SMProjLeft w x) (g <! SMProjRight w x)

public export
soProdCommutes : (x, y : SubstObjMu) -> SubstMorph (x !* y) (y !* x)
soProdCommutes x y = SMPair (SMProjRight x y) (SMProjLeft x y)

public export
soProdCommutesLeft : {x, y, z : SubstObjMu} ->
  SubstMorph (x !* y) z -> SubstMorph (y !* x) z
soProdCommutesLeft f = f <! soProdCommutes y x

public export
soProdDistribRight :
  (x, y, z : SubstObjMu) -> SubstMorph ((y !+ z) !* x) ((y !* x) !+ (z !* x))
soProdDistribRight x y z =
  soProdCommutesLeft
    (SMCase
      (soProdCommutesLeft (SMInjLeft _ _))
      (soProdCommutesLeft (SMInjRight _ _))
     <! SMDistrib _ _ _)

public export
soProdCommutesRight : {x, y, z : SubstObjMu} ->
  SubstMorph x (y !* z) -> SubstMorph x (z !* y)
soProdCommutesRight f = soProdCommutes y z <! f

public export
soCopCommutes : (x, y : SubstObjMu) -> SubstMorph (x !+ y) (y !+ x)
soCopCommutes x y = SMCase (SMInjRight y x) (SMInjLeft y x)

public export
soCopCommutesLeft : {x, y, z : SubstObjMu} ->
  SubstMorph (x !+ y) z -> SubstMorph (y !+ x) z
soCopCommutesLeft f = f <! soCopCommutes y x

public export
soCopCommutesRight : {x, y, z : SubstObjMu} ->
  SubstMorph x (y !+ z) -> SubstMorph x (z !+ y)
soCopCommutesRight f = soCopCommutes y z <! f

public export
soLeft : {x, y, z : SubstObjMu} -> SubstMorph (x !+ y) z -> SubstMorph x z
soLeft {x} {y} f = f <! SMInjLeft x y

public export
soRight : {x, y, z : SubstObjMu} -> SubstMorph (x !+ y) z -> SubstMorph y z
soRight f {x} {y} = f <! SMInjRight x y

public export
soProdLeft : {x, y, z : SubstObjMu} ->
  SubstMorph y z -> SubstMorph (x !* y) z
soProdLeft f = f <! SMProjRight _ _

public export
soProdRight : {x, y, z : SubstObjMu} ->
  SubstMorph y z -> SubstMorph (y !* x) z
soProdRight f = f <! SMProjLeft _ _

public export
soForgetFirst : (x, y, z : SubstObjMu) -> SubstMorph ((x !* y) !* z) (y !* z)
soForgetFirst x y z =
  SMPair (SMProjRight _ _ <! SMProjLeft _ _) (SMProjRight _ _)

public export
soForgetMiddle : (x, y, z : SubstObjMu) -> SubstMorph ((x !* y) !* z) (x !* z)
soForgetMiddle x y z =
  SMPair (SMProjLeft _ _ <! SMProjLeft _ _) (SMProjRight _ _)

public export
soForgetRight : (x, y, z : SubstObjMu) -> SubstMorph (x !* (y !* z)) (x !* y)
soForgetRight x y z =
  SMPair (SMProjLeft _ _) (SMProjLeft _ _ <! SMProjRight _ _)

public export
soProd1LeftElim : {x, y : SubstObjMu} ->
  SubstMorph (Subst1 !* x) y -> SubstMorph x y
soProd1LeftElim {x} f = f <! SMPair (SMToTerminal x) (SMId x)

public export
soProdLeftIntro : {x, y, z : SubstObjMu} ->
  SubstMorph y z -> SubstMorph (x !* y) z
soProdLeftIntro f = f <! SMProjRight _ _

public export
soProdLeftApply : {x, y, z : SubstObjMu} ->
  SubstMorph y z -> SubstMorph (x !* y) (x !* z)
soProdLeftApply f = SMPair (SMProjLeft _ _) (soProdLeftIntro f)

public export
soFlip : {x, y, z : SubstObjMu} ->
  SubstMorph (x !* y) z -> SubstMorph (y !* x) z
soFlip f = f <! SMPair (SMProjRight _ _) (SMProjLeft _ _)

public export
soProdLeftAssoc : {w, x, y, z : SubstObjMu} ->
  SubstMorph (w !* (x !* y)) z -> SubstMorph ((w !* x) !* y) z
soProdLeftAssoc {w} {x} {y} {z} f =
  f <!
    SMPair
      (SMProjLeft _ _ <! SMProjLeft _ _)
      (SMPair (SMProjRight _ _ <! SMProjLeft _ _) (SMProjRight _ _))

public export
soProdRightAssoc : {w, x, y, z : SubstObjMu} ->
  SubstMorph ((w !* x) !* y) z -> SubstMorph (w !* (x !* y)) z
soProdRightAssoc {w} {x} {y} {z} f =
  f <!
    SMPair
      (SMPair (SMProjLeft _ _) (SMProjLeft _ _ <! SMProjRight _ _))
      (SMProjRight _ _ <! SMProjRight _ _)

-- The inverse of SMDistrib.
public export
soGather : (x, y, z : SubstObjMu) ->
  SubstMorph ((x !* y) !+ (x !* z)) (x !* (y !+ z))
soGather x y z =
  SMPair
    (SMCase (SMProjLeft _ _) (SMProjLeft _ _))
    (SMCase
      (SMInjLeft _ _ <! SMProjRight _ _)
      (SMInjRight _ _ <! SMProjRight _ _))

public export
SOTerm : SubstObjMu -> Type
SOTerm = SubstMorph Subst1

public export
soConst : {x, y : SubstObjMu} -> SOTerm y -> SubstMorph x y
soConst {x} {y} f = f <! SMToTerminal _

--------------------------------------------------------------
---- Exponentiation (hom-objects) of substitutive objects ----
--------------------------------------------------------------

public export
SubstHomObj : SubstObjMu -> SubstObjMu -> SubstObjMu
-- 0 -> y == 1
SubstHomObj (InSO SO0) _ = Subst1
-- 1 -> y == y
SubstHomObj (InSO SO1) y = y
-- (x + y) -> z == (x -> z) * (y -> z)
SubstHomObj (InSO (x !!+ y)) z = SubstHomObj x z !* SubstHomObj y z
-- (x * y) -> z == x -> y -> z
SubstHomObj (InSO (x !!* y)) z = SubstHomObj x (SubstHomObj y z)
SubstHomObj (InSO (SOn n {nz})) z = SubstHomObjAlgN n nz z

export infixr 10 !->
public export
(!->) : SubstObjMu -> SubstObjMu -> SubstObjMu
(!->) = SubstHomObj

export infix 10 !^
public export
(!^) : SubstObjMu -> SubstObjMu -> SubstObjMu
(!^) = flip SubstHomObj

public export
SubstNIsZero : (n : Nat) -> SubstMorph (SubstN (S n)) SubstBool
SubstNIsZero n =
  SMNEq (S n) <! SMPair (SMId (SubstN (S n))) (soConst $ SMNConst (S n) 0)

public export
SubstNSucc : (n : Nat) -> SubstMorph (SubstN (S n)) (SubstN (S (S n)))
SubstNSucc n =
  SMNAdd (S (S n)) <!
  (SMPair (SMId (SubstN (S (S n)))) (soConst $ SMNConst (S (S n)) 1)) <!
  SMNInj (S n) (S (S n))

public export
SubstNPred : (n : Nat) -> SubstMorph (SubstN (S (S n))) (SubstN (S n))
SubstNPred n =
  SMNInj (S (S n)) (S n) <!
  SMNSub (S (S n)) <!
    SMPair (SMId (SubstN (S (S n)))) (soConst $ SMNConst (S (S n)) 1)

public export
substNIf0 : (n : Nat) -> SubstMorph (SubstN (S (S n))) (Subst1 !+ SubstN (S n))
substNIf0 n =
  SMCase
    (SMInjLeft Subst1 (SubstN (S n)) <! SMToTerminal (SubstN (S n) !* Subst1))
    (SMInjRight Subst1 (SubstN (S n)) <! SMProjLeft (SubstN (S n)) Subst1)
  <! (SMDistrib (SubstN (S n)) Subst1 Subst1)
  <! (SMPair (SubstNPred n) (SubstNIsZero (S n)))

public export
soEval0 : (y : SubstObjMu) ->
  SubstMorph ((SubstN (S Z) !-> y) !* SubstN (S Z)) y
soEval0 y = SMProjLeft y (SubstN (S Z))

public export
soEvalN : (n : Nat) -> (y : SubstObjMu) ->
  SubstMorph ((SubstN (S n) !-> y) !* SubstN (S n)) y
soEvalN Z y = soEval0 y
soEvalN (S n) y =
  let evN = soEvalN n y in
  SMCase
    (SMProjLeft y (SubstN (S n) !-> y)
     <! SMProjLeft (y !* (SubstN (S n) !-> y)) Subst1)
    (soEvalN n y <! soForgetFirst y (SubstN (S n) !-> y) (SubstN (S n)))
  <! SMDistrib (y !* (SubstN (S n) !-> y)) Subst1 (SubstN (S n))
  <! SMParallel (SMId (y !* (SubstN (S n) !-> y))) (substNIf0 n)

public export
soEval : (x, y : SubstObjMu) ->
  SubstMorph ((x !-> y) !* x) y
soEval (InSO SO0) y = SMFromInit y <! SMProjRight Subst1 Subst0
soEval (InSO SO1) y = SMProjLeft y Subst1
soEval (InSO (x !!+ y)) z =
  SMCase
    (soEval x z <! soForgetMiddle _ _ _)
    (soEval y z <! soForgetFirst _ _ _)
  <! SMDistrib _ _ _
soEval (InSO (x !!* y)) z =
  let
    eyz = soEval y z
    exhyz = soEval x (SubstHomObj y z)
  in
  eyz <!
    SMPair
      (exhyz <! soForgetRight _ _ _)
      (SMProjRight _ _ <! SMProjRight _ _)
soEval (InSO (SOn Z {nz=SIsNonZero})) z impossible
soEval (InSO (SOn (S n) {nz=SIsNonZero})) z = soEvalN n z

public export
soCurry0 : {x, z : SubstObjMu} ->
  SubstMorph (x !* SubstN (S Z)) z -> SubstMorph x (SubstN (S Z) !-> z)
soCurry0 {x} {z} f = f <! SMPair (SMId x) (soConst $ SMNConst 1 0)

public export
soCurryN : {x, z : SubstObjMu} -> {n : Nat} ->
  SubstMorph (x !* SubstN (S n)) z -> SubstMorph x (SubstN (S n) !-> z)
soCurryN {x} {z} {n=Z} f = soCurry0 {x} {z} f
soCurryN {x} {z} {n=(S n)} f =
  SMPair
    (f <! SMPair (SMId x) (soConst $ SMNConst (S (S n)) 0))
    (soCurryN {x} {z} {n} $ f <! SMPair
      (SMProjLeft x (SubstN (S n)))
      (SubstNSucc n <! SMProjRight x (SubstN (S n))))

public export
soCurry : {x, y, z : SubstObjMu} ->
  SubstMorph (x !* y) z -> SubstMorph x (y !-> z)
soCurry {x} {y=(InSO SO0)} f = SMToTerminal x
soCurry {x} {y=(InSO SO1)} {z} f = f <! SMPair (SMId x) (SMToTerminal x)
soCurry {x} {y=(InSO (y !!+ y'))} {z} f =
  let fg = f <! soGather x y y' in
  SMPair (soCurry $ soLeft fg) (soCurry $ soRight fg)
soCurry {x} {y=(InSO (y !!* y'))} {z} f =
  let
    cxyz = soCurry {x=(x !* y)} {y=y'} {z}
    cxhyz = soCurry {x} {y} {z=(SubstHomObj y' z)}
  in
  cxhyz $ cxyz $ soProdLeftAssoc f
soCurry {x} {y=(InSO (SOn Z {nz=SIsNonZero}))} {z} f impossible
soCurry {x} {y=(InSO (SOn (S n) {nz=SIsNonZero}))} {z} f =
  soCurryN {x} {z} {n} f

public export
soUncurry : {x, y, z : SubstObjMu} ->
  SubstMorph x (y !-> z) -> SubstMorph (x !* y) z
soUncurry {x} {y} {z} f =
  soEval y z <! SMPair (f <! SMProjLeft x y) (SMProjRight x y)

public export
soPartialApp : {w, x, y, z : SubstObjMu} ->
  SubstMorph (x !* y) z -> SubstMorph w x -> SubstMorph (w !* y) z
soPartialApp g f = soUncurry $ soCurry g <! f

public export
soPartialAppTerm : {w, x, y, z : SubstObjMu} ->
  SubstMorph (x !* y) z -> SOTerm x -> SubstMorph y z
soPartialAppTerm g t = soProd1LeftElim $ soPartialApp {w=Subst1} g t

public export
covarYonedaEmbed : {a, b : SubstObjMu} ->
  SubstMorph b a -> (x : SubstObjMu) -> SubstMorph (a !-> x) (b !-> x)
covarYonedaEmbed {a} {b} f x =
  soCurry (soEval a x <! SMPair (SMProjLeft _ _) (f <! SMProjRight _ _))

public export
contravarYonedaEmbed : {a, b : SubstObjMu} ->
  SubstMorph a b -> (x : SubstObjMu) -> SubstMorph (x !-> a) (x !-> b)
contravarYonedaEmbed {a} {b} f x =
  soCurry (f <! soEval x a)

public export
soSubst : {x, y, z : SubstObjMu} ->
  SubstMorph y z -> SubstMorph x y -> SubstMorph x z
soSubst (SMId y) f = f
soSubst g (SMId _) = g
soSubst (h <! g) f = h <! soSubst g f
soSubst h (g <! f) = soSubst h g <! f
soSubst {y=Subst0} {z} (SMFromInit _) (g <! f) = SMFromInit z <! soSubst g f
soSubst {z} (SMFromInit _) (SMCase f g) =
  SMCase (soSubst (SMFromInit z) f) (soSubst (SMFromInit z) g)
soSubst (SMFromInit _) (SMProjLeft _ _) = SMFromInit _ <! SMProjLeft _ _
soSubst (SMFromInit _) (SMProjRight _ _) = SMFromInit _ <! SMProjRight _ _
soSubst _ (SMFromInit _) = SMFromInit _
soSubst (SMToTerminal _) _ = SMToTerminal _
soSubst (SMInjLeft _ _) f = SMInjLeft _ _ <! f
soSubst (SMInjRight _ _) f = SMInjRight _ _ <! f
soSubst (SMCase g h) (SMInjLeft _ _) = g
soSubst (SMCase g h) (SMInjRight _ _) = h
soSubst (SMCase g h) (SMProjLeft _ _) = SMCase g h <! SMProjLeft _ _
soSubst (SMCase g h) (SMProjRight _ _) = SMCase g h <! SMProjRight _ _
soSubst (SMCase h j) (SMCase f g) =
  SMCase (soSubst (SMCase h j) f) (soSubst (SMCase h j) g)
soSubst (SMCase g h) (SMDistrib _ _ _) = SMCase g h <! SMDistrib _ _ _
soSubst (SMCase g h) (SMNEq m) = SMCase g h <! SMNEq m
soSubst (SMCase g h) (SMNLt m) = SMCase g h <! SMNLt m
soSubst (SMPair g h) f = SMPair (soSubst g f) (soSubst h f)
soSubst (SMProjLeft _ _) (SMProjLeft _ _) = SMProjLeft _ _ <! SMProjLeft _ _
soSubst (SMProjLeft _ _) (SMProjRight _ _) = SMProjLeft _ _ <! SMProjRight _ _
soSubst (SMProjLeft _ _) (SMCase f g) =
  SMCase (soSubst (SMProjLeft _ _) f) (soSubst (SMProjLeft _ _) g)
soSubst (SMProjLeft _ _) (SMPair f g) = f
soSubst (SMProjRight _ _) (SMProjLeft _ _) = SMProjRight _ _ <! SMProjLeft _ _
soSubst (SMProjRight _ _) (SMProjRight _ _) = SMProjRight _ _ <! SMProjRight _ _
soSubst (SMProjRight _ _) (SMCase f g) =
  SMCase (soSubst (SMProjRight _ _) f) (soSubst (SMProjRight _ _) g)
soSubst (SMProjRight _ _) (SMPair f g) = g
soSubst (SMDistrib _ _ _) (SMProjLeft _ _) = SMDistrib _ _ _ <! SMProjLeft _ _
soSubst (SMDistrib _ _ _) (SMProjRight _ _) = SMDistrib _ _ _ <! SMProjRight _ _
soSubst (SMDistrib _ _ _) (SMCase f g) = SMDistrib _ _ _ <! SMCase f g
soSubst (SMDistrib _ _ _) (SMPair f g) = SMDistrib _ _ _ <! SMPair f g
soSubst (SMNInj m n) f = SMNInj m n <! f
soSubst (SMNConst m n) f = SMNConst m n <! f
soSubst (SMNAdd n) f = SMNAdd n <! f
soSubst (SMNMult n) f = SMNMult n <! f
soSubst (SMNSub n) f = SMNSub n <! f
soSubst (SMNDiv n) f = SMNDiv n <! f
soSubst (SMNMod n) f = SMNMod n <! f
soSubst (SMNEq n) f = SMNEq n <! f
soSubst (SMNLt n) f = SMNLt n <! f

public export
soReduce : {x, y : SubstObjMu} -> SubstMorph x y -> SubstMorph x y
soReduce (SMId _) = SMId _
soReduce (g <! f) = soSubst (soReduce g) (soReduce f)
soReduce (SMFromInit _) = SMFromInit _
soReduce (SMToTerminal x) = SMToTerminal _
soReduce (SMInjLeft _ _) = SMInjLeft _ _
soReduce (SMInjRight _ _) = SMInjRight _ _
soReduce (SMCase f g) = SMCase (soReduce f) (soReduce g)
soReduce (SMPair f g) = SMPair (soReduce f) (soReduce g)
soReduce (SMProjLeft _ _) = SMProjLeft _ _
soReduce (SMProjRight _ _) = SMProjRight _ _
soReduce (SMDistrib _ _ _) = SMDistrib _ _ _
soReduce (SMNInj m n) = SMNInj m n
soReduce (SMNConst m n) = SMNConst m n
soReduce (SMNAdd n) = SMNAdd n
soReduce (SMNMult n) = SMNMult n
soReduce (SMNSub n) = SMNSub n
soReduce (SMNDiv n) = SMNDiv n
soReduce (SMNMod n) = SMNMod n
soReduce (SMNEq n) = SMNEq n
soReduce (SMNLt n) = SMNLt n

-------------------------------------------
---- Morphisms as terms of hom-objects ----
-------------------------------------------

public export
HomTerm : SubstObjMu -> SubstObjMu -> Type
HomTerm = SOTerm .* SubstHomObj

public export
TermAsMorph : {x, y : SubstObjMu} -> HomTerm x y -> SubstMorph x y
TermAsMorph {x} {y} t = soProd1LeftElim $ soUncurry {x=Subst1} {y=x} {z=y} t

public export
MorphAsTerm : {x, y : SubstObjMu} -> SubstMorph x y -> HomTerm x y
MorphAsTerm {x} {y} f = soCurry {x=Subst1} {y=x} {z=y} $ soProdLeftIntro f

----------------------------------------------------------------------------
---- Homoiconicity: SubstMorph reflected into the substitutive category ----
----------------------------------------------------------------------------

public export
soReflectedConst : (x, y : SubstObjMu) -> SubstMorph y (x !-> y)
soReflectedConst x y = soCurry $ SMProjLeft _ _

public export
soReflectedId : {x, y : SubstObjMu} -> SubstMorph x (y !-> y)
soReflectedId {x} {y} = soCurry (SMProjRight _ _)

public export
IdTerm : (x : SubstObjMu) -> HomTerm x x
IdTerm x = soReflectedId {x=Subst1} {y=x}

public export
soReflectedFromInit : (x, y : SubstObjMu) -> SubstMorph x (Subst0 !-> y)
soReflectedFromInit x y = soConst $ SMId Subst1

public export
soReflectedToTerminal : (x, y : SubstObjMu) -> SubstMorph x (y !-> Subst1)
soReflectedToTerminal x y = soConst (soCurry $ SMToTerminal _)

public export
soReflectedEval : (x, y : SubstObjMu) -> HomTerm ((x !-> y) !* x) y
soReflectedEval x y = MorphAsTerm $ SMId (x !-> y)

public export
soReflectedCurry : (x, y, z : SubstObjMu) ->
  SubstMorph ((x !* y) !-> z) (x !-> (y !-> z))
soReflectedCurry x y z = SMId (x !-> (y !-> z))

public export
soReflectedUncurry : (x, y, z : SubstObjMu) ->
  SubstMorph (x !-> (y !-> z)) ((x !* y) !-> z)
soReflectedUncurry x y z = SMId (x !-> (y !-> z))

public export
soReflectedCase : (x, y, z : SubstObjMu) ->
  SubstMorph ((x !-> z) !* (y !-> z)) ((x !+ y) !-> z)
soReflectedCase x y z = SMId (SubstHomObj x z !* SubstHomObj y z)

public export
soReflectedPair0 : (y, z : SubstObjMu) ->
  SubstMorph
    ((SubstN (S Z) !-> y) !* (SubstN (S Z) !-> z)) (SubstN (S Z) !-> (y !* z))
soReflectedPair0 y z = SMId (y !* z)

public export
soReflectedPairN : (n : Nat) -> (y, z : SubstObjMu) ->
  SubstMorph
    ((SubstN (S n) !-> y) !* (SubstN (S n) !-> z)) (SubstN (S n) !-> (y !* z))
soReflectedPairN Z y z = soReflectedPair0 y z
soReflectedPairN (S n) y z =
  let
    szyz = soReflectedPair0 y z
    nyz = soReflectedPairN n y z
  in
  SMPair
    (szyz <!
      SMPair
        (SMProjLeft y (SubstHomObjAlgN (S n) SIsNonZero y) <!
          SMProjLeft
            (y !* SubstHomObjAlgN (S n) SIsNonZero y)
            (z !* SubstHomObjAlgN (S n) SIsNonZero z))
        (SMProjLeft z (SubstHomObjAlgN (S n) SIsNonZero z) <!
          SMProjRight
            (y !* SubstHomObjAlgN (S n) SIsNonZero y)
            (z !* SubstHomObjAlgN (S n) SIsNonZero z)))
    (nyz <!
      SMPair
        (SMProjRight y (SubstHomObjAlgN (S n) SIsNonZero y) <!
          SMProjLeft
            (y !* SubstHomObjAlgN (S n) SIsNonZero y)
            (z !* SubstHomObjAlgN (S n) SIsNonZero z))
        (SMProjRight z (SubstHomObjAlgN (S n) SIsNonZero z) <!
          SMProjRight
            (y !* SubstHomObjAlgN (S n) SIsNonZero y)
            (z !* SubstHomObjAlgN (S n) SIsNonZero z)))

public export
soReflectedPair : (x, y, z : SubstObjMu) ->
  SubstMorph ((x !-> y) !* (x !-> z)) (x !-> (y !* z))
soReflectedPair (InSO SO0) _ _ = SMToTerminal _
soReflectedPair (InSO SO1) _ _ = SMId _
soReflectedPair (InSO (w !!+ x)) y z =
  let
    wyz = soReflectedPair w y z
    xyz = soReflectedPair x y z
  in
  SMPair
    (wyz <!
      SMPair
        (SMProjLeft _ _ <! SMProjLeft _ _)
        (SMProjLeft _ _ <! SMProjRight _ _))
    (xyz <!
      SMPair
        (SMProjRight _ _ <! SMProjLeft _ _)
        (SMProjRight _ _ <! SMProjRight _ _))
soReflectedPair (InSO (w !!* x)) y z =
  let
    xyz = soReflectedPair x y z
    wxyz = soReflectedPair w (x !-> y) (x !-> z)
  in
  contravarYonedaEmbed xyz w <! wxyz
soReflectedPair (InSO (SOn (S n) {nz=SIsNonZero})) y z = soReflectedPairN n y z

public export
soReflectedCompose0 : (y, z : SubstObjMu) ->
  SubstMorph ((y !-> z) !* (SubstN (S Z) !-> y)) (SubstN (S Z) !-> z)
soReflectedCompose0 y z = soEval y z

public export
soReflectedComposeN : (n : Nat) -> (y, z : SubstObjMu) ->
  SubstMorph ((y !-> z) !* (SubstN (S n) !-> y)) (SubstN (S n) !-> z)
soReflectedComposeN Z y z = soReflectedCompose0 y z
soReflectedComposeN (S n) y z =
  let
    czyz = soReflectedCompose0 y z
    csyz = soReflectedComposeN n y z
  in
  SMPair
    (czyz <!
      SMPair
        (SMProjLeft (y !-> z) (y !* SubstHomObjAlgN (S n) SIsNonZero y))
        (SMProjLeft y (SubstHomObjAlgN (S n) SIsNonZero y) <!
         SMProjRight (y !-> z) (y !* SubstHomObjAlgN (S n) SIsNonZero y)))
    (csyz <!
      SMPair
        (SMProjLeft (y !-> z) (y !* SubstHomObjAlgN (S n) SIsNonZero y))
        (SMProjRight y (SubstHomObjAlgN (S n) SIsNonZero y) <!
         SMProjRight (y !-> z) (y !* SubstHomObjAlgN (S n) SIsNonZero y)))

public export
soReflectedCompose : (x, y, z : SubstObjMu) ->
  SubstMorph ((y !-> z) !* (x !-> y)) (x !-> z)
soReflectedCompose (InSO SO0) y z = SMToTerminal _
soReflectedCompose (InSO SO1) y z = soEval y z
soReflectedCompose (InSO (w !!+ x)) y z =
  let
    cwyz = soReflectedCompose w y z
    cxyz = soReflectedCompose x y z
  in
  SMPair
    (cwyz <! SMPair (SMProjLeft _ _) (SMProjLeft _ _ <! SMProjRight _ _))
    (cxyz <! SMPair (SMProjLeft _ _) (SMProjRight _ _ <! SMProjRight _ _))
soReflectedCompose (InSO (w !!* x)) y z =
  soCurry $ soCurry $
    soEval y z <! SMPair
      (SMProjLeft _ _ <! SMProjLeft _ _ <! SMProjLeft _ _)
      (soEval x y <! SMPair
        (soEval w (x !-> y) <! SMPair
          (SMProjRight _ _ <! SMProjLeft _ _ <! SMProjLeft _ _)
          (SMProjRight _ _ <! SMProjLeft _ _))
        (SMProjRight _ _))
soReflectedCompose (InSO (SOn (S n) {nz=SIsNonZero})) y z =
  soReflectedComposeN n y z

public export
soReflectedPartialApp : (w, x, y, z : SubstObjMu) ->
  SubstMorph (((x !* y) !-> z) !* (w !-> x)) ((w !* y) !-> z)
soReflectedPartialApp w x y z =
  soReflectedCurry w y z <! (soReflectedCompose w x (y !-> z))

public export
soReflectedFlip : {x, y, z : SubstObjMu} ->
  SubstMorph ((x !* y) !-> z) ((y !* x) !-> z)
soReflectedFlip =
  soCurry (soCurry (soUncurry (soEval x (y !-> z)) <!
    SMPair
      (SMPair
        (SMProjLeft _ _ <! SMProjLeft _ _)
        (SMProjRight _ _))
      (SMProjRight _ _ <! SMProjLeft _ _)))

public export
ctxCompose : {w, x, y, z : SubstObjMu} ->
  SubstMorph w (y !-> z) -> SubstMorph w (x !-> y) -> SubstMorph w (x !-> z)
ctxCompose {w} {x} {y} {z} g f = soReflectedCompose x y z <! SMPair g f

public export
removeImpl : {x, y : SubstObjMu} -> SubstMorph x (x !-> y) -> SubstMorph x y
removeImpl {x} {y} f = soEval x y <! SMPair f (SMId x)

public export
soCaseAbstract : {w, x, y, z : SubstObjMu} ->
  SubstMorph (w !-> (x !+ y)) ((x !-> z) !-> (y !-> z) !-> (w !-> z))
soCaseAbstract {w} {x} {y} {z} =
  soCurry $ soCurry $ soCurry $ soProdCommutesLeft $ soProdRightAssoc $
    soUncurry $ soProdRightAssoc $ soUncurry $ soProdCommutesLeft $
    SMCase
      (soCurry $ soCurry $ soEval x z <! soProdCommutes _ _ <!
        SMProjLeft _ _)
      (soCurry $ soCurry $ soEval y z <! soProdCommutes _ _ <!
        soForgetMiddle _ _ _)
    <! soEval w (x !+ y)

--------------------------------------------
--------------------------------------------
---- SubstTerm / SubstMorph equivalence ----
--------------------------------------------
--------------------------------------------

public export
SubstHomTerm : SubstObjMu -> SubstObjMu -> Type
SubstHomTerm x y = SubstTerm (x !-> y)

public export
showSubstHomTerm : {x, y : SubstObjMu} -> SubstHomTerm x y -> String
showSubstHomTerm {x} {y} = showSubstTerm {x=(x !-> y)}

public export
substHomTermToFuncN : {n : Nat} -> {y : SubstObjMu} ->
  SubstHomTerm (SubstN (S n)) y -> (SubstTerm (SubstN (S n)) -> SubstTerm y)
substHomTermToFuncN {n=Z} {y} t FZ = t
substHomTermToFuncN {n=(S n)} {y} (tz, ts) FZ = tz
substHomTermToFuncN {n=(S n)} {y} (tz, ts) (FS k) =
  substHomTermToFuncN {n} {y} ts k

public export
substHomTermToFunc : {x, y : SubstObjMu} ->
  SubstHomTerm x y -> (SubstTerm x -> SubstTerm y)
substHomTermToFunc {x=(InSO SO0)} f t =
  void t
substHomTermToFunc {x=(InSO SO1)} f () =
  f
substHomTermToFunc {x=(InSO (x !!+ x'))} (f, f') (Left t) =
  substHomTermToFunc f t
substHomTermToFunc {x=(InSO (x !!+ x'))} (f, f') (Right t) =
  substHomTermToFunc f' t
substHomTermToFunc {x=(InSO (x !!* x'))} f (t, t') =
  substHomTermToFunc {x=x'} {y} (substHomTermToFunc {x} {y=(x' !-> y)} f t) t'
substHomTermToFunc {x=(InSO (SOn (S n) {nz=SIsNonZero}))} {y} f t =
  substHomTermToFuncN {n} {y} f t

public export
substFuncToHomTermN : {n : Nat} -> {y : SubstObjMu} ->
  (SubstTerm (SubstN (S n)) -> SubstTerm y) -> SubstHomTerm (SubstN (S n)) y
substFuncToHomTermN {n=Z} {y} f = f FZ
substFuncToHomTermN {n=(S n)} {y} f =
  (f FZ, substFuncToHomTermN {n} {y} $ f . FS)

public export
substFuncToHomTerm : {x, y : SubstObjMu} ->
  (SubstTerm x -> SubstTerm y) -> SubstHomTerm x y
substFuncToHomTerm {x=(InSO SO0)} f =
  ()
substFuncToHomTerm {x=(InSO SO1)} f =
  f ()
substFuncToHomTerm {x=(InSO (x !!+ x'))} f =
  (substFuncToHomTerm $ f . Left, substFuncToHomTerm $ f . Right)
substFuncToHomTerm {x=(InSO (x !!* x'))} f =
  substFuncToHomTerm {x} {y=(x' !-> y)} $
    \t => substFuncToHomTerm {x=x'} {y} $ \t' => f (t, t')
substFuncToHomTerm {x=(InSO (SOn (S n) {nz=SIsNonZero}))} f =
  substFuncToHomTermN {n} {y} f

public export
SubstIdTerm : (x : SubstObjMu) -> SubstHomTerm x x
SubstIdTerm x = substFuncToHomTerm (id {a=(SubstTerm x)})

public export
SubstTermComp : {x, y, z : SubstObjMu} ->
  SubstHomTerm y z -> SubstHomTerm x y -> SubstHomTerm x z
SubstTermComp g f =
  substFuncToHomTerm (substHomTermToFunc g . substHomTermToFunc f)

public export
SubstExFalsoTerm : (x : SubstObjMu) -> SubstHomTerm Subst0 x
SubstExFalsoTerm x = ()

public export
SubstConstTerm : {x, y : SubstObjMu} -> SubstTerm y -> SubstHomTerm x y
SubstConstTerm = substFuncToHomTerm . const

public export
SubstUnitTerm : (x : SubstObjMu) -> SubstHomTerm x Subst1
SubstUnitTerm x = SubstConstTerm ()

public export
SubstInjLeftTerm : (x, y : SubstObjMu) -> SubstHomTerm x (x !+ y)
SubstInjLeftTerm x y =
  substFuncToHomTerm (Left {a=(SubstTerm x)} {b=(SubstTerm y)})

public export
SubstInjRightTerm : (x, y : SubstObjMu) -> SubstHomTerm y (x !+ y)
SubstInjRightTerm x y =
  substFuncToHomTerm (Right {a=(SubstTerm x)} {b=(SubstTerm y)})

public export
SubstCaseTerm : {x, y, z : SubstObjMu} ->
  SubstHomTerm x z -> SubstHomTerm y z -> SubstHomTerm (x !+ y) z
SubstCaseTerm f g =
  substFuncToHomTerm {x=(x !+ y)} {y=z} $ eitherElim
    (substHomTermToFunc f) (substHomTermToFunc g)

public export
SubstPairTerm : {x, y, z : SubstObjMu} ->
  SubstHomTerm x y -> SubstHomTerm x z -> SubstHomTerm x (y !* z)
SubstPairTerm f g =
  substFuncToHomTerm {x} {y=(y !* z)} $ \t =>
    (substHomTermToFunc f t, substHomTermToFunc g t)

public export
SubstProjLeftTerm : (x, y : SubstObjMu) -> SubstHomTerm (x !* y) x
SubstProjLeftTerm x y = substFuncToHomTerm {x=(x !* y)} {y=x} fst

public export
SubstProjRightTerm : (x, y : SubstObjMu) -> SubstHomTerm (x !* y) y
SubstProjRightTerm x y = substFuncToHomTerm {x=(x !* y)} {y} snd

public export
SubstEval : (x, y : SubstObjMu) -> SubstHomTerm ((x !-> y) !* x) y
SubstEval x y = substFuncToHomTerm (id {a=(SubstHomTerm x y)})

public export
SubstCurry : {x, y, z : SubstObjMu} ->
  SubstHomTerm (x !* y) z -> SubstHomTerm x (y !-> z)
SubstCurry = id

public export
SubstUncurry : {x, y, z : SubstObjMu} ->
  SubstHomTerm x (y !-> z) -> SubstHomTerm (x !* y) z
SubstUncurry = id

public export
SubstPartialApp : {w, x, y, z : SubstObjMu} ->
  SubstHomTerm (x !* y) z -> SubstHomTerm w x -> SubstHomTerm (w !* y) z
SubstPartialApp = SubstTermComp

public export
SubstDistribTerm : (x, y, z : SubstObjMu) ->
  SubstHomTerm (x !* (y !+ z)) ((x !* y) !+ (x !* z))
SubstDistribTerm x y z = substFuncToHomTerm $ \tx =>
  (substFuncToHomTerm $ \ty => Left (tx, ty),
   substFuncToHomTerm $ \tz => Right (tx, tz))

public export
SubstTermToSOTerm : (x : SubstObjMu) -> SubstTerm x -> SOTerm x
SubstTermToSOTerm (InSO SO0) t impossible
SubstTermToSOTerm (InSO SO1) () = SMId Subst1
SubstTermToSOTerm (InSO (x !!+ y)) (Left t) =
  SMInjLeft x y <! SubstTermToSOTerm x t
SubstTermToSOTerm (InSO (x !!+ y)) (Right t) =
  SMInjRight x y <! SubstTermToSOTerm y t
SubstTermToSOTerm (InSO (x !!* y)) (t1, t2) =
  SMPair (SubstTermToSOTerm x t1) (SubstTermToSOTerm y t2)
SubstTermToSOTerm (InSO (SOn n {nz})) k = SMNConst n {nz} (finToNat k)

public export
SubstTermToSubstMorph0 : {y : SubstObjMu} ->
  SubstHomTerm (SubstN (S Z)) y -> SubstMorph (SubstN (S Z)) y
SubstTermToSubstMorph0 {y} t = soConst $ SubstTermToSOTerm y t

public export
SubstNCase0 : {n : Nat} -> {y : SubstObjMu} ->
  -- Zero case
  SubstTerm y ->
  -- Non-zero case
  SubstMorph (SubstN (S n)) y ->
  -- Result
  SubstMorph (SubstN (S (S n))) y
SubstNCase0 {n} {y} t f =
  SMCase
    (SMProjLeft y y <! SMProjLeft (y !* y) Subst1)
    (SMProjRight y y <! SMProjLeft (y !* y) Subst1)
  <! SMDistrib (y !* y) Subst1 Subst1
  <!
  SMPair
    (SMPair
      (soConst {x=(SubstN (S (S n)))} (SubstTermToSOTerm y t))
      (f <! SubstNPred n))
    (SubstNIsZero (S n))

public export
SubstTermToSubstMorphN : {n : Nat} -> {y : SubstObjMu} ->
  SubstHomTerm (SubstN (S n)) y -> SubstMorph (SubstN (S n)) y
SubstTermToSubstMorphN {n=Z} {y} t = SubstTermToSubstMorph0 {y} t
SubstTermToSubstMorphN {n=(S n)} {y} (ty, ts) =
  SubstNCase0 ty $ SubstTermToSubstMorphN {n} {y} ts

public export
SubstTermToSubstMorph : {x, y : SubstObjMu} ->
  SubstHomTerm x y -> SubstMorph x y
SubstTermToSubstMorph {x=(InSO SO0)} {y} () =
  SMFromInit y
SubstTermToSubstMorph {x=(InSO SO1)} {y} t =
  SubstTermToSOTerm y t
SubstTermToSubstMorph {x=(InSO (x !!+ x'))} {y} (t, t') =
  SMCase (SubstTermToSubstMorph t) (SubstTermToSubstMorph t')
SubstTermToSubstMorph {x=(InSO (x !!* x'))} {y} t =
  soUncurry $ SubstTermToSubstMorph {x} {y=(x' !-> y)} t
SubstTermToSubstMorph {x=(InSO (SOn (S n) {nz=SIsNonZero}))} {y} t =
  SubstTermToSubstMorphN {n} {y} t

public export
finBinOpMod : (Nat -> Nat -> Nat) ->
  {n : Nat} -> {nz : NonZero n} -> (m, k : Fin n) -> Fin n
finBinOpMod op {n=(S n)} {nz=SIsNonZero} m k =
  let
    res = op (finToNat m) (finToNat k)
    _ = modLTDivisor res n
  in
  natToFinLT $ modNatNZ res (S n) SIsNonZero

public export
SubstMorphToSubstTerm : {x, y : SubstObjMu} ->
  SubstMorph x y -> SubstHomTerm x y
SubstMorphToSubstTerm (SMId x) = SubstIdTerm x
SubstMorphToSubstTerm (g <! f) =
  SubstTermComp (SubstMorphToSubstTerm g) (SubstMorphToSubstTerm f)
SubstMorphToSubstTerm (SMFromInit y) = SubstExFalsoTerm x
SubstMorphToSubstTerm (SMToTerminal x) = SubstUnitTerm x
SubstMorphToSubstTerm (SMInjLeft x y) = SubstInjLeftTerm x y
SubstMorphToSubstTerm (SMInjRight x y) = SubstInjRightTerm x y
SubstMorphToSubstTerm (SMCase f g) =
  SubstCaseTerm (SubstMorphToSubstTerm f) (SubstMorphToSubstTerm g)
SubstMorphToSubstTerm (SMPair f g) =
  SubstPairTerm (SubstMorphToSubstTerm f) (SubstMorphToSubstTerm g)
SubstMorphToSubstTerm (SMProjLeft x y) = SubstProjLeftTerm x y
SubstMorphToSubstTerm (SMProjRight x y) = SubstProjRightTerm x y
SubstMorphToSubstTerm (SMDistrib x y z) = SubstDistribTerm x y z
SubstMorphToSubstTerm (SMNInj (S m) (S n)
  {m_nz=SIsNonZero} {n_nz=SIsNonZero}) =
    substFuncToHomTerm {x=(SubstN (S m))} {y=(SubstN (S n))} $
      \k =>
        let
          k' = finToNat k
          _ = modLTDivisor k' n
        in
        natToFinLT $ modNatNZ k' (S n) SIsNonZero
SubstMorphToSubstTerm (SMNConst (S n) k {nz=SIsNonZero}) =
  substFuncToHomTerm {x=(SubstN 1)} {y=(SubstN (S n))} $
    \FZ => let _ = modLTDivisor k n in natToFinLT $ modNatNZ k (S n) SIsNonZero
SubstMorphToSubstTerm (SMNAdd (S n) {nz=SIsNonZero}) =
  substFuncToHomTerm {x=(SubstN (S n) !* (SubstN (S n)))} {y=(SubstN (S n))} $
    \(k, p) => finBinOpMod {n=(S n)} {nz=SIsNonZero} (+) k p
SubstMorphToSubstTerm (SMNMult (S n) {nz=SIsNonZero}) =
  substFuncToHomTerm {x=(SubstN (S n) !* (SubstN (S n)))} {y=(SubstN (S n))} $
    \(k, p) => finBinOpMod {n=(S n)} {nz=SIsNonZero} (*) k p
SubstMorphToSubstTerm (SMNSub (S n) {nz=SIsNonZero}) =
  substFuncToHomTerm {x=(SubstN (S n) !* (SubstN (S n)))} {y=(SubstN (S n))} $
    \(k, p) => finBinOpMod {n=(S n)} {nz=SIsNonZero} minus k p
SubstMorphToSubstTerm (SMNDiv (S n) {nz=SIsNonZero}) =
  substFuncToHomTerm {x=(SubstN (S n) !* (SubstN (S n)))} {y=(SubstN (S n))} $
    \(k, p) => finBinOpMod {n=(S n)} {nz=SIsNonZero} div k p
SubstMorphToSubstTerm (SMNMod (S n) {nz=SIsNonZero}) =
  substFuncToHomTerm {x=(SubstN (S n) !* (SubstN (S n)))} {y=(SubstN (S n))} $
    \(k, p) => finBinOpMod {n=(S n)} {nz=SIsNonZero} mod k p
SubstMorphToSubstTerm (SMNEq (S n) {nz=SIsNonZero}) =
  substFuncToHomTerm {x=(SubstN (S n) !* (SubstN (S n)))} {y=SubstBool} $
    \(k, p) => case k == p of False => Left () ; True => Right ()
SubstMorphToSubstTerm (SMNLt (S n) {nz=SIsNonZero}) =
  substFuncToHomTerm {x=(SubstN (S n) !* (SubstN (S n)))} {y=SubstBool} $
    \(k, p) => case k < p of False => Left () ; True => Right ()

public export
SOTermToSubstTerm : (x : SubstObjMu) -> SOTerm x -> SubstTerm x
SOTermToSubstTerm x t = SubstMorphToSubstTerm {x=Subst1} {y=x} t

public export
SubstMorphReduce : {x, y : SubstObjMu} -> SubstMorph x y -> SubstMorph x y
SubstMorphReduce f = (SubstTermToSubstMorph (SubstMorphToSubstTerm f))

-------------------------------------------------------
-------------------------------------------------------
---- Utility functions for SubstObjMu / SubstMorph ----
-------------------------------------------------------
-------------------------------------------------------

---------------------------------
---- Products and coproducts ----
---------------------------------

public export
soSwap : (x, y : SubstObjMu) -> SubstMorph (x !* y) (y !* x)
soSwap _ _ = SMPair (SMProjRight _ _) (SMProjLeft _ _)

public export
SOCoproductN : {n : Nat} -> Vect n SubstObjMu -> SubstObjMu
SOCoproductN [] = Subst0
SOCoproductN [x] = x
SOCoproductN (x :: xs@(_ :: _)) = x !+ SOCoproductN xs

public export
soConstruct : {n : Nat} -> {x : SubstObjMu} -> {v : Vect n SubstObjMu} ->
  (m : Nat) -> {auto ok : IsYesTrue (isLT m n)} ->
  SubstMorph x (indexNL m {ok} v) -> SubstMorph x (SOCoproductN v)
soConstruct {n=Z} {x} {v=[]} m {ok=Refl} f impossible
soConstruct {n=(S Z)} {x} {v=[y]} Z {ok=Refl} f = f
soConstruct {n=(S Z)} {x} {v=[y]} (S m) {ok=Refl} f impossible
soConstruct {n=(S (S n))} {x} {v=(y :: (y' :: ys))} Z {ok=Refl} f =
  SMInjLeft _ _ <! f
soConstruct {n=(S (S n))} {x} {v=(y :: v'@(y' :: ys))} (S m) {ok} f =
  SMInjRight _ _ <!
    soConstruct {n=(S n)} {x} {v=v'} m {ok=(fromLteSuccYes ok)}
      (replace {p=(SubstMorph x)}
        (indexToFinLTS {ok=(fromLteSuccYes ok)} {okS=ok} {x=y} {v=v'})
        f)

public export
SOProductN : {n : Nat} -> Vect n SubstObjMu -> SubstObjMu
SOProductN [] = Subst1
SOProductN [x] = x
SOProductN (x :: xs@(_ :: _)) = x !* SOProductN xs

public export
SOMorphN : {n : Nat} -> SubstObjMu -> Vect n SubstObjMu -> Vect n Type
SOMorphN x v = map (SubstMorph x) v

public export
SOMorphHV : {n : Nat} -> SubstObjMu -> Vect n SubstObjMu -> Type
SOMorphHV {n} x v = HVect (SOMorphN x v)

public export
soTuple : {n : Nat} -> {x : SubstObjMu} -> {v : Vect n SubstObjMu} ->
  SOMorphHV {n} x v -> SubstMorph x (SOProductN v)
soTuple {n=Z} {x} {v=[]} [] = SMToTerminal x
soTuple {n=(S Z)} {x} {v=[y]} [m] = m
soTuple {n=(S (S n))} {x} {v=(y :: (y' :: ys))} (m :: (m' :: ms)) =
  SMPair m $ soTuple {x} {v=(y' :: ys)} (m' :: ms)

------------------
---- Booleans ----
------------------

public export
SFalse : SOTerm SubstBool
SFalse = SMInjLeft _ _

public export
STrue : SOTerm SubstBool
STrue = SMInjRight _ _

public export
SNot : SubstMorph SubstBool SubstBool
SNot = SMCase (SMInjRight _ _) (SMInjLeft _ _)

public export
SHigherAnd : SubstMorph SubstBool (SubstBool !-> SubstBool)
SHigherAnd = SMPair (soConst SFalse) (SMId SubstBool)

public export
SHigherOr : SubstMorph SubstBool (SubstBool !-> SubstBool)
SHigherOr = SMPair (SMId SubstBool) (soConst STrue)

public export
SAnd : SubstMorph (SubstBool !* SubstBool) SubstBool
SAnd = soUncurry SHigherAnd

public export
SOr : SubstMorph (SubstBool !* SubstBool) SubstBool
SOr = soUncurry SHigherOr

public export
SIfElse : {x : SubstObjMu} ->
  SOTerm SubstBool -> SOTerm x -> SOTerm x -> SOTerm x
SIfElse {x} b t f =
  SMCase {x=Subst1} {y=Subst1} {z=x} t f <! b

public export
SHigherIfElse : {x, y : SubstObjMu} ->
  SubstMorph x SubstBool -> SubstMorph x y -> SubstMorph x y -> SubstMorph x y
SHigherIfElse {x} {y} b t f =
  soEval x y <! SMPair (SMCase (MorphAsTerm f) (MorphAsTerm t) <! b) (SMId x)

public export
SEqual : (x : SubstObjMu) -> SubstMorph (x !* x) SubstBool
SEqual (InSO SO0) = SMFromInit _ <! SMProjLeft _ _
SEqual (InSO SO1) = soConst $ SMInjLeft _ _
SEqual (InSO (x !!+ y)) =
  SMCase
    (SMCase (SEqual x) (soConst $ SMInjRight _ _) <! soProdDistribRight _ _ _)
    (SMCase (soConst $ SMInjRight _ _) (SEqual y) <! soProdDistribRight _ _ _)
  <! SMDistrib _ _ _
SEqual (InSO (x !!* y)) =
  SAnd <!
    SMPair
      (SEqual x <! SMPair
        (SMProjLeft _ _ <! SMProjLeft _ _)
        (SMProjLeft _ _ <! SMProjRight _ _))
      (SEqual y <! SMPair
        (SMProjRight _ _ <! SMProjLeft _ _)
        (SMProjRight _ _ <! SMProjRight _ _))
SEqual (InSO (SOn (S n) {nz})) = SMNEq (S n) {nz}

public export
SEqualF : {x, y : SubstObjMu} -> (f, g : SubstMorph x y) ->
  SubstMorph x SubstBool
SEqualF {x} {y} f g = SEqual y <! SMPair f g

public export
SIfEqual : {x, y, z : SubstObjMu} ->
  (test, test' : SubstMorph x y) -> (ftrue, ffalse : SubstMorph x z) ->
  SubstMorph x z
SIfEqual {x} {y} {z} test test' ftrue ffalse =
  SHigherIfElse {x} {y=z} (SEqualF {x} {y} test test') ftrue ffalse

---------------
---- Maybe ----
---------------

public export
SMaybe : SubstObjMu -> SubstObjMu
SMaybe x = Subst1 !+ x

-------------------------------
---- Unary natural numbers ----
-------------------------------

-- Unary natural numbers less than the input.
public export
SUNat : Nat -> SubstObjMu
SUNat Z = Subst0
SUNat (S Z) = Subst1
SUNat (S (S n)) = SMaybe $ SUNat (S n)

public export
MkSUNat : {m : Nat} -> (n : Nat) -> {x : SubstObjMu} ->
  {auto lt : IsYesTrue (isLT n m)} ->
  SubstMorph x (SUNat m)
MkSUNat {m=Z} Z {lt=Refl} impossible
MkSUNat {m=(S Z)} Z {lt} = SMToTerminal _
MkSUNat {m=(S (S m))} Z {lt} = SMInjLeft _ _ <! SMToTerminal _
MkSUNat {m=Z} (S n) {lt=Refl} impossible
MkSUNat {m=(S Z)} (S n) {lt=Refl} impossible
MkSUNat {m=(S (S m))} (S n) {lt} =
  SMInjRight _ _ <! MkSUNat {m=(S m)} n {lt=(fromLteSuccYes lt)}

public export
suNatFold : {n : Nat} -> {x : SubstObjMu} ->
  SubstMorph x x -> SubstMorph (x !* SUNat (S n)) x
suNatFold {n=Z} {x} op = SMProjLeft _ _
suNatFold {n=(S n)} {x} op =
  SMCase
    (SMProjLeft _ _)
    (op <! suNatFold {n} {x} op)
  <! SMDistrib _ _ _

-- Catamorphism on unary natural numbers.
public export
suNatCata : (n : Nat) -> (x : SubstObjMu) ->
  SubstMorph ((Subst1 !+ x) !-> x) (SUNat (S n) !-> x)
suNatCata Z x = SMProjLeft _ _
suNatCata (S n) x = soCurry {y=(SUNat (S (S n)))} {z=x} $
  SMCase
    (SMProjLeft _ _ <! SMProjLeft _ _)
    (soEval x x <!
      SMPair
        (SMProjRight _ _ <! SMProjLeft _ _)
        (soUncurry $ suNatCata n x))
    <! SMDistrib _ _ _

public export
suZ : {n : Nat} -> {x : SubstObjMu} -> SubstMorph x (SUNat (S n))
suZ {n=Z} {x} = SMToTerminal x
suZ {n=(S n)} {x} = SMInjLeft _ _ <! SMToTerminal x

public export
suPromote : {n : Nat} -> SubstMorph (SUNat n) (SUNat (S n))
suPromote {n=Z} = SMFromInit Subst1
suPromote {n=(S Z)} = SMInjLeft _ _
suPromote {n=(S (S n))} =
  SMCase (SMInjLeft _ _) (SMInjRight _ _ <! suPromote {n=(S n)})

public export
suPromoteN : {m, n : Nat} -> {auto ok : LTE m n} ->
  SubstMorph (SUNat m) (SUNat n)
suPromoteN {m=Z} {n} {ok=LTEZero} = SMFromInit _
suPromoteN {m=(S Z)} {n=(S Z)} {ok=(LTESucc ok)} = SMId Subst1
suPromoteN {m=(S Z)} {n=(S (S n))} {ok=(LTESucc ok)} = SMInjLeft _ _
suPromoteN {m=(S (S m))} {n=(S Z)} {ok=(LTESucc ok)} = void $ succNotLTEzero ok
suPromoteN {m=(S (S m))} {n=(S (S n))} {ok=(LTESucc ok)} =
  SMCase
    (SMInjLeft _ _)
    (SMInjRight _ _ <! suPromoteN {m=(S m)} {n=(S n)} {ok})

public export
suSucc : {n : Nat} -> SubstMorph (SUNat n) (SUNat (S n))
suSucc {n=Z} = SMFromInit Subst1
suSucc {n=(S n)} = SMInjRight _ _

public export
su1 : {n : Nat} -> {x : SubstObjMu} -> SubstMorph x (SUNat (S n))
su1 {n=Z} {x} = SMToTerminal x
su1 {n=(S Z)} {x} = SMInjRight _ _ <! SMToTerminal _
su1 {n=(S (S n))} {x} = SMInjRight _ _ <! SMInjLeft _ _ <! SMToTerminal _

-- Successor, which returns `Nothing` (`Left`) if the input is the
-- maximum value of `SUNat n`.
public export
suSuccMax : {n : Nat} -> SubstMorph (SUNat n) (SMaybe (SUNat n))
suSuccMax {n=Z} = SMFromInit _
suSuccMax {n=(S Z)} = SMInjLeft _ _ <! SMToTerminal _
suSuccMax {n=(S (S n))} =
  let r = suSuccMax {n=(S n)} in
  SMCase
    (SMInjRight _ _ <! su1 {n=(S n)})
    (SMCase
      (SMInjLeft _ _)
      (SMInjRight _ _ <! SMInjRight _ _)
     <! r)

-- Successor modulo `n`.
public export
suSuccMod : {n : Nat} -> SubstMorph (SUNat n) (SUNat n)
suSuccMod {n=Z} = SMFromInit Subst0
suSuccMod {n=(S n)} =
  SMCase
    suZ -- overflow
    (SMId _) -- no overflow
  <! suSuccMax {n=(S n)}

public export
suAdd : {n : Nat} -> SubstMorph (SUNat n !* SUNat n) (SUNat n)
suAdd {n=Z} = SMFromInit _ <! SMProjLeft _ _
suAdd {n=(S n)} = soUncurry $ suNatCata _ _ <!
  SMPair (SMId _) (soConst $ MorphAsTerm $ suSuccMod {n=(S n)})

public export
suAddUnrolled : {k : Nat} ->
  SubstMorph (SUNat k !* SUNat k) (SUNat k)
suAddUnrolled {k=Z} = SMProjLeft _ _
suAddUnrolled {k=(S k)} = suNatFold {n=k} (suSuccMod {n=(S k)})

public export
suAddN : (k : Nat) -> (n : Nat) -> {auto lt : IsYesTrue (isLT n k)} ->
  SubstMorph (SUNat k) (SUNat k)
suAddN k n {lt} =
  soPartialAppTerm {w=Subst1} {x=(SUNat k)}
    (suAddUnrolled {k}) (MkSUNat {m=k} {x=Subst1} n {lt})

public export
suMul : {n : Nat} -> SubstMorph (SUNat n !* SUNat n) (SUNat n)
suMul {n=Z} = SMFromInit _ <! SMProjLeft _ _
suMul {n=(S n)} = soUncurry $ suNatCata _ _ <! SMPair suZ (soCurry suAdd)

public export
suRaiseTo : {n : Nat} -> SubstMorph (SUNat n !* SUNat n) (SUNat n)
suRaiseTo {n=Z} = SMFromInit _ <! SMProjLeft _ _
suRaiseTo {n=(S n)} = soUncurry $ suNatCata _ _ <! SMPair su1 (soCurry suMul)

public export
suPow : {n : Nat} -> SubstMorph (SUNat n !* SUNat n) (SUNat n)
suPow = soFlip suRaiseTo

--------------------------------
---- Binary natural numbers ----
--------------------------------

-- `n`-bit natural numbers.
public export
SBNat : Nat -> SubstObjMu
SBNat Z = Subst1
SBNat (S Z) = SubstBool
SBNat (S (S n)) = SubstBool !* SBNat (S n)

---------------
---- Lists ----
---------------

public export
SList : Nat -> SubstObjMu -> SubstObjMu
SList Z x = Subst1
SList (S n) x = SList n x !+ (x !* SList n x)

public export
sListNil : {n : Nat} -> {x : SubstObjMu} -> SOTerm (SList n x)
sListNil {n=Z} {x} = SMId Subst1
sListNil {n=(S n)} {x} = SMInjLeft _ _ <! sListNil {n} {x}

public export
sListPromote : {n : Nat} -> {x : SubstObjMu} ->
  SubstMorph (SList n x) (SList (S n) x)
sListPromote {n} = SMInjLeft _ _

public export
sListPromoteN : {m, n : Nat} -> {x : SubstObjMu} ->
  {auto ok : LTE m n} -> SubstMorph (SList m x) (SList n x)
sListPromoteN {m=Z} {n=Z} {x} {ok=LTEZero} = SMId Subst1
sListPromoteN {m=Z} {n=(S n)} {x} {ok=LTEZero} =
  SMInjLeft _ _ <! sListPromoteN {m=Z} {n} {x} {ok=LTEZero}
sListPromoteN {m=(S m)} {n=(S n)} {x} {ok=(LTESucc ok)} =
  SMInjLeft _ _ <! SMCase
    (sListPromoteN {m} {n} {x} {ok})
    (sListPromoteN {m} {n} {x} {ok} <! SMProjRight _ _)

public export
sListCons : {n : Nat} -> {x : SubstObjMu} ->
  SubstMorph (x !* SList n x) (SList (S n) x)
sListCons {n} {x} = SMInjRight _ _

public export
sListEvalCons : {n : Nat} -> {x : SubstObjMu} ->
  SOTerm x -> SOTerm (SList n x) -> SOTerm (SList (S n) x)
sListEvalCons {n} {x} a l = sListCons {n} {x} <! SMPair a l

public export
sListFoldUnrolled : {k : Nat} -> {a, x : SubstObjMu} ->
  SOTerm x -> SubstMorph (a !* x) x -> SubstMorph (SList k a) x
sListFoldUnrolled {k=Z} {a} {x} n c = n
sListFoldUnrolled {k=(S k)} {a} {x} n c =
  SMCase (soConst n)
    (c <!
      SMPair (SMProjLeft _ _) (sListFoldUnrolled {k} n c <! SMProjRight _ _))

-- Catamorphism on lists.
public export
sListCata : (n : Nat) -> (a, x : SubstObjMu) ->
  SubstMorph ((Subst1 !+ (a !* x)) !-> x) (SList n a !-> x)
sListCata Z a x = SMProjLeft _ _
sListCata (S n) a x =
  let cataN = sListCata n a x in
  SMPair
    cataN
    (soCurry $ soCurry $ soEval x x <! SMPair
      (soEval a (SubstHomObj x x) <! SMPair
        (SMProjRight _ _ <! SMProjLeft _ _ <! SMProjLeft _ _)
        (SMProjRight _ _ <! SMProjLeft _ _))
      (soEval (SList n a) x <!
        SMPair
          (cataN <! SMProjLeft _ _ <! SMProjLeft _ _)
          (SMProjRight _ _)))

public export
sListEvalCata : {n : Nat} -> {a, x : SubstObjMu} ->
  SOTerm x -> SubstMorph (a !* x) x -> SOTerm (SList n a) -> SOTerm x
sListEvalCata {n} {a} {x} z s t = sListFoldUnrolled z s <! t

----------------------
---- Binary trees ----
----------------------

public export
SBinTree : Nat -> SubstObjMu -> SubstObjMu
SBinTree Z x = Subst0
SBinTree (S n) x = SMaybe (x !* SBinTree n x !* SBinTree n x)

-----------------------
---- S-expressions ----
-----------------------

public export
SSExp : Nat -> SubstObjMu -> SubstObjMu
SSExp Z x = Subst0
SSExp (S Z) x = x -- atom
SSExp (S (S n)) x = SSExp (S n) x !+ (SSExp (S n) x !* (SSExp (S n) x))

----------------------------------------------------------------------
----------------------------------------------------------------------
---- Interpretation of substitutive objects as metalanguage types ----
----------------------------------------------------------------------
----------------------------------------------------------------------

public export
MetaSOTypeAlg : MetaSOAlg Type
MetaSOTypeAlg SO0 = Void
MetaSOTypeAlg SO1 = Unit
MetaSOTypeAlg (p !!+ q) = Either p q
MetaSOTypeAlg (p !!* q) = Pair p q
MetaSOTypeAlg (SOn (S n) {nz}) = Fin (S n)

public export
MetaSOType : SubstObjMu -> Type
MetaSOType = substObjCata MetaSOTypeAlg

public export
MetaSOShowTypeAlg : MetaSOAlg String
MetaSOShowTypeAlg SO0 = "Void"
MetaSOShowTypeAlg SO1 = "Unit"
MetaSOShowTypeAlg (p !!+ q) = "Either (" ++ p ++ ") (" ++ q ++ ")"
MetaSOShowTypeAlg (p !!* q) = "Pair (" ++ p ++ ") (" ++ q ++ ")"
MetaSOShowTypeAlg (SOn n {nz}) = "Fin (" ++ show n ++ ")"

public export
metaSOShowType : SubstObjMu -> String
metaSOShowType = substObjCata MetaSOShowTypeAlg

-------------------------------------------------------------------
-------------------------------------------------------------------
---- Explicitly-polynomial-functor version of above definition ----
-------------------------------------------------------------------
-------------------------------------------------------------------

public export
data SubstMorphADTPos : Type where
  SMAPFrom0 : SubstObjMu -> SubstMorphADTPos
  SMAPCopTo1 : SubstObjMu -> SubstObjMu -> SubstMorphADTPos
  SMAPProdTo1 : SubstObjMu -> SubstObjMu -> SubstMorphADTPos
  SMAPId1 : SubstMorphADTPos
  SMAPTermLeft : SubstObjMu -> SubstMorphADTPos
  SMAPTermRight : SubstObjMu -> SubstMorphADTPos
  SMAPTermPair : SubstMorphADTPos
  SMAPCase : SubstMorphADTPos
  SMAP0PLeft : SubstObjMu -> SubstObjMu -> SubstMorphADTPos
  SMAP1PLeft : SubstMorphADTPos
  SMAPDistrib : SubstObjMu -> SubstObjMu -> SubstObjMu -> SubstMorphADTPos
  SMAPAssoc : SubstObjMu -> SubstObjMu -> SubstObjMu -> SubstMorphADTPos

public export
SubstMorphADTNDir : SubstMorphADTPos -> Nat
SubstMorphADTNDir (SMAPFrom0 _) = 0
SubstMorphADTNDir (SMAPCopTo1 _ _) = 0
SubstMorphADTNDir (SMAPProdTo1 _ _) = 0
SubstMorphADTNDir SMAPId1 = 0
SubstMorphADTNDir (SMAPTermLeft _) = 1
SubstMorphADTNDir (SMAPTermRight _) = 1
SubstMorphADTNDir SMAPTermPair = 2
SubstMorphADTNDir SMAPCase = 2
SubstMorphADTNDir (SMAP0PLeft _ _) = 0
SubstMorphADTNDir SMAP1PLeft = 1
SubstMorphADTNDir (SMAPDistrib _ _ _) = 1
SubstMorphADTNDir (SMAPAssoc _ _ _) = 1

public export
SubstMorphADTDir : SubstMorphADTPos -> Type
SubstMorphADTDir = Fin . SubstMorphADTNDir

public export
SubstMorphADTPoly : PolyFunc
SubstMorphADTPoly = (SubstMorphADTPos ** SubstMorphADTDir)

public export
SubstMorphADTPFAlg : Type -> Type
SubstMorphADTPFAlg = PFAlg SubstMorphADTPoly

public export
SubstMorphADTSig : Type
SubstMorphADTSig = (SubstObjMu, SubstObjMu)

public export
0 SubstMorphADTPFAlgCheckSig : SubstMorphADTPFAlg (Maybe SubstMorphADTSig)
SubstMorphADTPFAlgCheckSig (SMAPFrom0 x) d = Just (Subst0, x)
SubstMorphADTPFAlgCheckSig SMAPId1 d = Just (Subst1, Subst1)
SubstMorphADTPFAlgCheckSig (SMAPCopTo1 x y) d = Just (x !+ y, Subst1)
SubstMorphADTPFAlgCheckSig (SMAPProdTo1 x y) d = Just (x !* y, Subst1)
SubstMorphADTPFAlgCheckSig (SMAPTermLeft x) d = case d FZ of
  Just (y, z) => if y == Subst1 then Just (Subst1, z !+ x) else Nothing
  Nothing => Nothing
SubstMorphADTPFAlgCheckSig (SMAPTermRight x) d = ?SubstMorphADTPFAlgCheckSig_hole_5
SubstMorphADTPFAlgCheckSig SMAPTermPair d = ?SubstMorphADTPFAlgCheckSig_hole_6
SubstMorphADTPFAlgCheckSig SMAPCase d = ?SubstMorphADTPFAlgCheckSig_hole_7
SubstMorphADTPFAlgCheckSig (SMAP0PLeft x y) d = ?SubstMorphADTPFAlgCheckSig_hole_8
SubstMorphADTPFAlgCheckSig SMAP1PLeft d = ?SubstMorphADTPFAlgCheckSig_hole_9
SubstMorphADTPFAlgCheckSig (SMAPDistrib x y z) d = ?SubstMorphADTPFAlgCheckSig_hole_10
SubstMorphADTPFAlgCheckSig (SMAPAssoc x y z) d = ?SubstMorphADTPFAlgCheckSig_hole_11

public export
data SubstMorphADTF : Type -> Type where
  SMAFrom0 : SubstObjMu -> SubstMorphADTF carrier
  SMACopTo1 : SubstObjMu -> SubstObjMu -> SubstMorphADTF carrier
  SMAProdTo1 : SubstObjMu -> SubstObjMu -> SubstMorphADTF carrier
  SMAId1 : SubstMorphADTF carrier
  SMATermLeft : carrier -> SubstObjMu -> SubstMorphADTF carrier
  SMATermRight : SubstObjMu -> carrier -> SubstMorphADTF carrier
  SMATermPair : carrier -> carrier -> SubstMorphADTF carrier
  SMACase : carrier -> carrier -> SubstMorphADTF carrier
  SMA0PLeft : SubstObjMu -> SubstObjMu -> SubstMorphADTF carrier
  SMA1PLeft : carrier -> SubstMorphADTF carrier
  SMADistrib : SubstObjMu -> SubstObjMu -> SubstObjMu ->
    carrier -> SubstMorphADTF carrier
  SMAAssoc : SubstObjMu -> SubstObjMu -> SubstObjMu ->
    carrier -> SubstMorphADTF carrier

public export
Functor SubstMorphADTF where
  map f (SMAFrom0 x) = SMAFrom0 x
  map f (SMACopTo1 x y) = SMACopTo1 x y
  map f (SMAProdTo1 x y) = SMAProdTo1 x y
  map f SMAId1 = SMAId1
  map f (SMATermLeft x y) = SMATermLeft (f x) y
  map f (SMATermRight x y) = SMATermRight x (f y)
  map f (SMATermPair x y) = SMATermPair (f x) (f y)
  map f (SMACase x y) = SMACase (f x) (f y)
  map f (SMA0PLeft x y) = SMA0PLeft x y
  map f (SMA1PLeft x) = SMA1PLeft (f x)
  map f (SMADistrib x y z w) = SMADistrib x y z (f w)
  map f (SMAAssoc x y z w) = SMAAssoc x y z (f w)

public export
data SubstMorphADT : Type where
  InSM : SubstMorphADTF SubstMorphADT -> SubstMorphADT

public export
SubstMorphADTAlg : Type -> Type
SubstMorphADTAlg x = SubstMorphADTF x -> Maybe x

public export
0 substMorphADTCata : SubstMorphADTAlg x -> SubstMorphADT -> Maybe x
substMorphADTCata alg (InSM x) = ?substMorphADTCata_hole

public export
SMADTCheckSigAlg :
  SubstMorphADTF (SubstObjMu, SubstObjMu) -> Maybe (SubstObjMu, SubstObjMu)
SMADTCheckSigAlg (SMAFrom0 x) = Just (Subst0, x)
SMADTCheckSigAlg SMAId1 = Just (Subst1, Subst1)
SMADTCheckSigAlg (SMACopTo1 x y) = Just (x !+ y, Subst1)
SMADTCheckSigAlg (SMAProdTo1 x y) = Just (x !* y, Subst1)
SMADTCheckSigAlg (SMATermLeft (d, c) y) =
  if d == Subst1 then Just (Subst1, c !+ y) else Nothing
SMADTCheckSigAlg (SMATermRight x (d, c)) =
  if d == Subst1 then Just (Subst1, x !+ c) else Nothing
SMADTCheckSigAlg (SMATermPair (d, c) (d', c')) =
  if d == Subst1 && d' == Subst1 then Just (Subst1, c !* c') else Nothing
SMADTCheckSigAlg (SMACase (d, c) (d', c')) =
  if c == c' then Just (d !+ d', c) else Nothing
SMADTCheckSigAlg (SMA0PLeft x y) = Just (Subst0 !* x, y)
SMADTCheckSigAlg (SMA1PLeft (d, c)) = Just (Subst1 !* d, c)
SMADTCheckSigAlg (SMADistrib x y z (d, c)) =
  if d == (x !+ y) !* z then Just ((x !* z) !+ (y !* z), c) else Nothing
SMADTCheckSigAlg (SMAAssoc x y z (d, c)) =
  if d == (x !* y) !* z then Just (x !* (y !* z), c) else Nothing

public export
0 smadtCheckSig : SubstMorphADT -> Maybe (SubstObjMu, SubstObjMu)
smadtCheckSig = substMorphADTCata SMADTCheckSigAlg

----------------------------------------------------------------------
----------------------------------------------------------------------
---- Compilation of finite polynomial types to circuit operations ----
----------------------------------------------------------------------
----------------------------------------------------------------------

public export
substObjToNat : SubstObjMu -> Nat
substObjToNat = substObjCard

-- Given a binary operation and a non-zero natural number size, produce
-- a binary operation on an input which is assumed to be a product.
--
-- We implement this by applying the operation to the left and right
-- projections.
public export
substMorphBinOpToBNC : (BNCPolyM -> BNCPolyM -> BNCPolyM) ->
  (n : Nat) -> (0 _ : NonZero n) -> BNCPolyM
substMorphBinOpToBNC op (S n) SIsNonZero = op (PI #/ #| (S n)) (PI #% #| (S n))

public export
substMorphToBNC : {x, y : SubstObjMu} -> SubstMorph x y -> BNCPolyM
substMorphToBNC {y=x} (SMId x) = PI
substMorphToBNC ((<!) {x} {y} {z} g f) = substMorphToBNC g #. substMorphToBNC f
substMorphToBNC {x=Subst0} (SMFromInit y) = #| 0
substMorphToBNC {y=Subst1} (SMToTerminal x) = #| 0
substMorphToBNC (SMInjLeft x y) = PI
substMorphToBNC (SMInjRight x y) = #| (substObjToNat x) #+ PI
substMorphToBNC (SMCase {x} {y} {z} f g) with (substObjToNat x)
  substMorphToBNC (SMCase {x} {y} {z} f g) | cx =
    if cx == 0 then
      substMorphToBNC g
    else
      IfLT PI (#| cx)
        (substMorphToBNC f)
        (substMorphToBNC g #. (PI #- #| cx))
substMorphToBNC (SMPair {x} {y} {z} f g) with (substObjToNat y, substObjToNat z)
  substMorphToBNC (SMPair {x} {y} {z} f g) | (cy, cz) =
    #| cz #* substMorphToBNC f #+ substMorphToBNC g
substMorphToBNC (SMProjLeft x y) with (substObjToNat y)
  substMorphToBNC (SMProjLeft x y) | cy =
    if cy == 0 then
      #| 0
    else
      PI #/ #| cy
substMorphToBNC (SMProjRight x y) with (substObjToNat y)
  substMorphToBNC (SMProjRight x y) | cy =
    if cy == 0 then
      #| 0
    else
      PI #% #| cy
substMorphToBNC {x=(x' !* (y' !+ z'))} {y=((x' !* y') !+ (x' !* z'))}
  (SMDistrib x' y' z') =
    let
      cx = substObjToNat x'
      cy = substObjToNat y'
      cz = substObjToNat z'
    in
    if cy == 0 && cz == 0 then
      #| 0
    else
      let
        yz = cy + cz
        xin = PI #/ #| yz
        yzin = PI #% #| yz
      in
      IfLT yzin (#| cy)
        (#| cy #* xin #+ yzin)
        (#| cz #* xin #+ (yzin #- #| cy) #+ #| (cx * cy))
substMorphToBNC (SMNInj m n {m_nz} {n_nz}) = PI #% #| n
substMorphToBNC (SMNConst n k {nz}) = #| (modNatNZ k n nz)
substMorphToBNC (SMNAdd n {nz}) = substMorphBinOpToBNC (#+) n nz
substMorphToBNC (SMNMult n {nz}) = substMorphBinOpToBNC (#*) n nz
substMorphToBNC (SMNSub n {nz}) = substMorphBinOpToBNC (#-) n nz
substMorphToBNC (SMNDiv n {nz}) = substMorphBinOpToBNC (#/) n nz
substMorphToBNC (SMNMod n {nz}) = substMorphBinOpToBNC (#%) n nz
substMorphToBNC (SMNEq n {nz}) =
  -- We implement testing `f = g` as `if (isZero (f - g))`.
  -- The return value is just a boolean (true is 1; false is 0).
  substMorphBinOpToBNC (\f, g => IfZero (f #- g) (#| 1) (#| 0)) n nz
substMorphToBNC (SMNLt n {nz}) =
  substMorphBinOpToBNC (\f, g => IfLT f g (#| 1) (#| 0)) n nz

public export
substMorphToFunc : {a, b : SubstObjMu} -> SubstMorph a b -> Integer -> Integer
substMorphToFunc {a} {b} f =
  metaBNCPolyM (natToInteger $ pred $ substObjToNat b) (substMorphToBNC f)

public export
substTermToNat : {a : SubstObjMu} -> SOTerm a -> Nat
substTermToNat t = integerToNat (substMorphToFunc t 0)

public export
natToSubstTerm : (a : SubstObjMu) -> Nat -> Maybe (SOTerm a)
natToSubstTerm (InSO SO0) n = Nothing
natToSubstTerm (InSO SO1) n = if n == 0 then Just (SMId Subst1) else Nothing
natToSubstTerm a@(InSO (x !!+ y)) n =
  if n < substObjCard x then do
    t <- natToSubstTerm x n
    Just $ SMInjLeft x y <! t
  else if n < substObjCard x + substObjCard y then do
    t <- natToSubstTerm y (minus n (substObjCard x))
    Just $ SMInjRight x y <! t
  else
    Nothing
natToSubstTerm (InSO (x !!* y)) n = do
  xn <- divMaybe n (substObjCard y)
  yn <- modMaybe n (substObjCard y)
  xt <- natToSubstTerm x xn
  yt <- natToSubstTerm y yn
  Just $ SMPair xt yt
natToSubstTerm (InSO (SOn n {nz})) m = Just $ SMNConst n {nz} m

public export
NatToSubstTerm : (a : SubstObjMu) -> (n : Nat) ->
  {auto ok : IsJustTrue (natToSubstTerm a n)} -> SOTerm a
NatToSubstTerm a n {ok} = fromIsJust ok

public export
substMorphToGNum : {a, b : SubstObjMu} -> SubstMorph a b -> Nat
substMorphToGNum = substTermToNat . MorphAsTerm

public export
substGNumToMorph : (a, b : SubstObjMu) -> Nat -> Maybe (SubstMorph a b)
substGNumToMorph a b n =
  map {f=Maybe} TermAsMorph (natToSubstTerm (SubstHomObj a b) n)

public export
SubstGNumToMorph : (a, b : SubstObjMu) -> (n : Nat) ->
  {auto ok : IsJustTrue (substGNumToMorph a b n)} -> SubstMorph a b
SubstGNumToMorph a b n {ok} = fromIsJust ok

public export
showMaybeSubstMorph : {x, y : SubstObjMu} -> Maybe (SubstMorph x y) -> String
showMaybeSubstMorph = maybeElim showSubstMorph (show (Nothing {ty=()}))

public export
SignedBNCMorph : Type
SignedBNCMorph = (Nat, Nat, BNCPolyM)

public export
Show SignedBNCMorph where
  show (dom, cod, m) =
    "(" ++ show dom ++ " -> " ++ show cod ++ " : " ++ show m ++ ")"

--------------------------------
---- Test utility functions ----
--------------------------------

public export
MorphToTermAndBack : {x, y : SubstObjMu} -> SubstMorph x y -> SubstMorph x y
MorphToTermAndBack = TermAsMorph . MorphAsTerm

public export
evalByGN : (x, y : SubstObjMu) -> Nat -> Nat -> Maybe Nat
evalByGN x y m n with (substGNumToMorph x y m, natToSubstTerm x n)
  evalByGN x y m n | (Just f, Just t) = Just $ substTermToNat {a=y} (f <! t)
  evalByGN x y m n | _ = Nothing

---------------------------------------
---------------------------------------
---- STLC-to-SubstObjMu/SubstMorph ----
---------------------------------------
---------------------------------------

public export
SOMu_Context : Type
SOMu_Context = List SubstObjMu

-- Indexed by the context and the type of the term within that context
-- to which the term compiles. (Thus, the type of the term abstracted over
-- the context is `ctx -> ty`.)
public export
data Checked_STLC_Term : SOMu_Context -> SubstObjMu -> Type where
  -- The "void" or "absurd" function, which takes a term of type Void
  -- to any type; there's no explicit constructor for terms of type Void,
  -- but a lambda could introduce one.  The SubstObjMu is the type of the
  -- resulting term (since we can get any type from a term of Void).
  Checked_STLC_Absurd : {ctx : SOMu_Context} -> {cod : SubstObjMu} ->
    Checked_STLC_Term ctx Subst0 -> Checked_STLC_Term ctx cod

  -- The only term of type Unit.
  Checked_STLC_Unit : {ctx : SOMu_Context} ->
    Checked_STLC_Term ctx Subst1

  -- Construct coproducts.  In each case, the type of the injected term
  -- tells us the type of one side of the coproduct, so we provide a
  -- SubstObjMu to tell us the type of the other side.
  Checked_STLC_Left :
    {ctx : SOMu_Context} -> {lty, rty : SubstObjMu} ->
      Checked_STLC_Term ctx lty -> Checked_STLC_Term ctx (lty !+ rty)
  Checked_STLC_Right :
    {ctx : SOMu_Context} -> {lty, rty : SubstObjMu} ->
      Checked_STLC_Term ctx rty -> Checked_STLC_Term ctx (lty !+ rty)

  -- Case statement : parameters are expression to case on, which must be
  -- a coproduct, and then left and right case, which must be of the same
  -- type, which becomes the type of the overall term.  The cases receive
  -- the the result of the coproduct elimination in their contexts.
  Checked_STLC_Case :
    {ctx : SOMu_Context} -> {lty, rty, cod : SubstObjMu} ->
    Checked_STLC_Term ctx (lty !+ rty) ->
    Checked_STLC_Term (lty :: ctx) cod -> Checked_STLC_Term (rty :: ctx) cod ->
    Checked_STLC_Term ctx cod

  -- Construct a term of a pair type
  Checked_STLC_Pair : {ctx : SOMu_Context} -> {lty, rty : SubstObjMu} ->
    Checked_STLC_Term ctx lty -> Checked_STLC_Term ctx rty ->
    Checked_STLC_Term ctx (lty !* rty)

  -- Projections; in each case, the given term must be of a product type
  Checked_STLC_Fst : {ctx : SOMu_Context} -> {lty, rty : SubstObjMu} ->
    Checked_STLC_Term ctx (lty !* rty) -> Checked_STLC_Term ctx lty
  Checked_STLC_Snd : {ctx : SOMu_Context} -> {lty, rty : SubstObjMu} ->
    Checked_STLC_Term ctx (lty !* rty) -> Checked_STLC_Term ctx rty

  -- Lambda abstraction:  introduce into the context a (de Bruijn-indexed)
  -- variable of the given type.
  Checked_STLC_Lambda :
    {ctx : SOMu_Context} -> {vty, tty : SubstObjMu} ->
    Checked_STLC_Term (vty :: ctx) tty -> Checked_STLC_Term ctx (vty !-> tty)

  -- Function application
  Checked_STLC_App : {ctx : SOMu_Context} -> {dom, cod : SubstObjMu} ->
    Checked_STLC_Term ctx (dom !-> cod) -> Checked_STLC_Term ctx dom ->
    Checked_STLC_Term ctx cod

  -- The variable at the given de Bruijn index
  Checked_STLC_Var :
    {ctx : SOMu_Context} -> {i : Nat} -> {auto ok : InBounds i ctx} ->
    Checked_STLC_Term ctx (index i ctx {ok})

  -- Cast (Fin m) to (Fin n)
  Checked_STLC_NInj :
    {ctx : SOMu_Context} -> {m, n : Nat} ->
    {auto 0 m_nz : NonZero m} ->
    {auto 0 n_nz : NonZero n} ->
    Checked_STLC_Term ctx (SubstN m) ->
    Checked_STLC_Term ctx (SubstN n)

  Checked_STLC_NConst :
    {ctx : SOMu_Context} -> {n : Nat} ->
    {auto 0 nz : NonZero n} ->
    Checked_STLC_Term ctx (SubstN n) ->
    Checked_STLC_Term ctx (SubstN n)

  Checked_STLC_NAdd :
    {ctx : SOMu_Context} -> {n : Nat} ->
    {auto 0 nz : NonZero n} ->
    Checked_STLC_Term ctx (SubstN n) ->
    Checked_STLC_Term ctx (SubstN n) ->
    Checked_STLC_Term ctx (SubstN n)

  Checked_STLC_NMult :
    {ctx : SOMu_Context} -> {n : Nat} ->
    {auto 0 nz : NonZero n} ->
    Checked_STLC_Term ctx (SubstN n) ->
    Checked_STLC_Term ctx (SubstN n) ->
    Checked_STLC_Term ctx (SubstN n)

  Checked_STLC_NSub :
    {ctx : SOMu_Context} -> {n : Nat} ->
    {auto 0 nz : NonZero n} ->
    Checked_STLC_Term ctx (SubstN n) ->
    Checked_STLC_Term ctx (SubstN n) ->
    Checked_STLC_Term ctx (SubstN n)

  Checked_STLC_NDiv :
    {ctx : SOMu_Context} -> {n : Nat} ->
    {auto 0 nz : NonZero n} ->
    Checked_STLC_Term ctx (SubstN n) ->
    Checked_STLC_Term ctx (SubstN n) ->
    Checked_STLC_Term ctx (SubstN n)

  Checked_STLC_NMod :
    {ctx : SOMu_Context} -> {n : Nat} ->
    {auto 0 nz : NonZero n} ->
    Checked_STLC_Term ctx (SubstN n) ->
    Checked_STLC_Term ctx (SubstN n) ->
    Checked_STLC_Term ctx (SubstN n)

  Checked_STLC_NEq :
    {ctx : SOMu_Context} -> {n : Nat} ->
    {auto 0 nz : NonZero n} ->
    Checked_STLC_Term ctx (SubstN n) ->
    Checked_STLC_Term ctx (SubstN n) ->
    Checked_STLC_Term ctx SubstBool

  Checked_STLC_NLt :
    {ctx : SOMu_Context} -> {n : Nat} ->
    {auto 0 nz : NonZero n} ->
    Checked_STLC_Term ctx (SubstN n) ->
    Checked_STLC_Term ctx (SubstN n) ->
    Checked_STLC_Term ctx SubstBool

public export
Checked_Closed_STLC_Function : SubstObjMu -> SubstObjMu -> Type
Checked_Closed_STLC_Function x y = Checked_STLC_Term [] (x !-> y)

public export
stlcCtxToSOMu : SOMu_Context -> SubstObjMu
stlcCtxToSOMu = foldr (!*) Subst1

public export
stlcCtxProj :
  (ctx : SOMu_Context) -> (n : Nat) -> {auto 0 ok : InBounds n ctx} ->
  SubstMorph (stlcCtxToSOMu ctx) (index n ctx {ok})
stlcCtxProj (ty :: ctx) Z {ok=InFirst} =
  SMProjLeft ty (stlcCtxToSOMu ctx)
stlcCtxProj (ty :: ctx) Z {ok=InLater} impossible
stlcCtxProj (ty :: ctx) (S n) {ok=InFirst} impossible
stlcCtxProj (ty :: ctx) (S n) {ok=(InLater ok)} =
  stlcCtxProj ctx n {ok} <! SMProjRight ty (stlcCtxToSOMu ctx)

public export
compileCheckedTerm : {ctx : SOMu_Context} -> {ty : SubstObjMu} ->
  Checked_STLC_Term ctx ty -> SubstMorph (stlcCtxToSOMu ctx) ty
compileCheckedTerm {ctx} {ty} (Checked_STLC_Absurd v) =
  SMFromInit ty <! compileCheckedTerm {ctx} {ty=Subst0} v
compileCheckedTerm {ctx} {ty=Subst1} Checked_STLC_Unit =
  SMToTerminal (stlcCtxToSOMu ctx)
compileCheckedTerm {ctx} {ty=(lty !+ rty)} (Checked_STLC_Left t) =
  SMInjLeft lty rty <! compileCheckedTerm {ctx} {ty=lty} t
compileCheckedTerm {ctx} {ty=(lty !+ rty)} (Checked_STLC_Right t) =
  SMInjRight lty rty <! compileCheckedTerm {ctx} {ty=rty} t
compileCheckedTerm {ctx} {ty} (Checked_STLC_Case {lty} {rty} {cod=ty} t l r) =
  let
    t' = compileCheckedTerm {ctx} {ty=(lty !+ rty)} t
    l' = soCurry $ compileCheckedTerm {ctx=(lty :: ctx)} {ty} l
    r' = soCurry $ compileCheckedTerm {ctx=(rty :: ctx)} {ty} r
    lr' = SMCase l' r'
    lrt' = lr' <! t'
  in
  removeImpl lrt'
compileCheckedTerm {ctx} {ty=(lty !* rty)} (Checked_STLC_Pair {lty} {rty} l r) =
  SMPair
    (compileCheckedTerm {ctx} {ty=lty} l)
    (compileCheckedTerm {ctx} {ty=rty} r)
compileCheckedTerm {ctx} {ty=lty} (Checked_STLC_Fst {lty} {rty} p) =
  SMProjLeft lty rty <! compileCheckedTerm {ctx} {ty=(lty !* rty)} p
compileCheckedTerm {ctx} {ty=rty} (Checked_STLC_Snd {lty} {rty} p) =
  SMProjRight lty rty <! compileCheckedTerm {ctx} {ty=(lty !* rty)} p
compileCheckedTerm
  {ctx} {ty=(vty !-> tty)} (Checked_STLC_Lambda {ctx} {vty} {tty} t) =
    soCurry {x=(stlcCtxToSOMu ctx)} {y=vty} {z=tty} $
    soProdCommutesLeft {x=vty} {y=(stlcCtxToSOMu ctx)} {z=tty} $
    compileCheckedTerm {ctx=(vty :: ctx)} {ty=tty} t
compileCheckedTerm {ctx} {ty=cod} (Checked_STLC_App {dom} {cod} f x) =
  soEval dom cod <! SMPair (compileCheckedTerm f) (compileCheckedTerm x)
compileCheckedTerm
  {ctx} {ty=(index i ctx {ok})} (Checked_STLC_Var {ctx} {i} {ok}) =
    stlcCtxProj ctx i {ok}
compileCheckedTerm {ctx} {ty=(InSO (SOn n {nz=n_nz}))}
  (Checked_STLC_NInj {ctx} {m} {n} {m_nz} {n_nz} k) =
    SMNInj m n <! (compileCheckedTerm {ctx} {ty=(SubstN m {nz=m_nz})} k)
compileCheckedTerm {ctx} {ty=(InSO (SOn n {nz}))}
  (Checked_STLC_NConst {ctx} {n} {nz} k) =
    compileCheckedTerm {ctx} {ty=(SubstN n {nz})} k
compileCheckedTerm {ctx} {ty=(InSO (SOn n {nz}))}
  (Checked_STLC_NAdd {ctx} {n} {nz} m k) =
    SMNAdd n {nz} <! SMPair
      (compileCheckedTerm {ctx} {ty=(SubstN n {nz=nz})} k)
      (compileCheckedTerm {ctx} {ty=(SubstN n {nz=nz})} m)
compileCheckedTerm {ctx} {ty=(InSO (SOn n {nz}))}
  (Checked_STLC_NMult {ctx} {n} {nz} m k) =
    SMNMult n {nz} <! SMPair
      (compileCheckedTerm {ctx} {ty=(SubstN n {nz=nz})} k)
      (compileCheckedTerm {ctx} {ty=(SubstN n {nz=nz})} m)
compileCheckedTerm {ctx} {ty=(InSO (SOn n {nz}))}
  (Checked_STLC_NSub {ctx} {n} {nz} m k) =
    SMNSub n {nz} <! SMPair
      (compileCheckedTerm {ctx} {ty=(SubstN n {nz=nz})} k)
      (compileCheckedTerm {ctx} {ty=(SubstN n {nz=nz})} m)
compileCheckedTerm {ctx} {ty=(InSO (SOn n {nz}))}
  (Checked_STLC_NDiv {ctx} {n} {nz} m k) =
    SMNDiv n {nz} <! SMPair
      (compileCheckedTerm {ctx} {ty=(SubstN n {nz=nz})} k)
      (compileCheckedTerm {ctx} {ty=(SubstN n {nz=nz})} m)
compileCheckedTerm {ctx} {ty=(InSO (SOn n {nz}))}
  (Checked_STLC_NMod {ctx} {n} {nz} m k) =
    SMNMod n {nz} <! SMPair
      (compileCheckedTerm {ctx} {ty=(SubstN n {nz=nz})} k)
      (compileCheckedTerm {ctx} {ty=(SubstN n {nz=nz})} m)
compileCheckedTerm {ctx} {ty=SubstBool}
  (Checked_STLC_NEq {ctx} {n} {nz} m k) =
    SMNEq n {nz} <! SMPair
      (compileCheckedTerm {ctx} {ty=(SubstN n {nz=nz})} k)
      (compileCheckedTerm {ctx} {ty=(SubstN n {nz=nz})} m)
compileCheckedTerm {ctx} {ty=SubstBool}
  (Checked_STLC_NLt {ctx} {n} {nz} m k) =
    SMNLt n {nz} <! SMPair
      (compileCheckedTerm {ctx} {ty=(SubstN n {nz=nz})} k)
      (compileCheckedTerm {ctx} {ty=(SubstN n {nz=nz})} m)

public export
data STLC_Term : Type where
  -- The "void" or "absurd" function, which takes a term of type Void
  -- to any type; there's no explicit constructor for terms of type Void,
  -- but a lambda could introduce one.  The SubstObjMu is the type of the
  -- resulting term (since we can get any type from a term of Void).
  STLC_Absurd : STLC_Term -> SubstObjMu -> STLC_Term

  -- The only term of type Unit.
  STLC_Unit : STLC_Term

  -- Construct coproducts.  In each case, the type of the injected term
  -- tells us the type of one side of the coproduct, so we provide a
  -- SubstObjMu to tell us the type of the other side.
  STLC_Left : STLC_Term -> SubstObjMu -> STLC_Term
  STLC_Right : SubstObjMu -> STLC_Term -> STLC_Term

  -- Case statement : parameters are expression to case on, which must be
  -- a coproduct, and then left and right case, which must be of the same
  -- type, which becomes the type of the overall term.
  STLC_Case : STLC_Term -> STLC_Term -> STLC_Term -> STLC_Term

  -- Construct a term of a pair type
  STLC_Pair : STLC_Term -> STLC_Term -> STLC_Term

  -- Projections; in each case, the given term must be of a product type
  STLC_Fst : STLC_Term -> STLC_Term
  STLC_Snd : STLC_Term -> STLC_Term

  -- Lambda abstraction:  introduce into the context a (de Bruijn-indexed)
  -- variable of the given type, and produce a term with that extended context.
  STLC_Lambda : SubstObjMu -> STLC_Term -> STLC_Term

  -- Function application; the first parameter is the function's codomain
  -- (and hence the type of the overall term)
  STLC_App : SubstObjMu -> STLC_Term -> STLC_Term -> STLC_Term

  -- The variable at the given de Bruijn index
  STLC_Var : Nat -> STLC_Term

public export
Show STLC_Term where
  show (STLC_Absurd t ty) = "absurd(" ++ show t ++ ")"
  show STLC_Unit = "()"
  show (STLC_Left t ty) = "inl(" ++ show t ++ ")"
  show (STLC_Right ty t) = "inr(" ++ show t ++ ")"
  show (STLC_Case x l r) =
    "(" ++ show x ++ " ? " ++ show l ++ " | " ++ show r ++ ")"
  show (STLC_Pair x y) = "(" ++ show x ++ ", " ++ show y ++ ")"
  show (STLC_Fst x) = "fst(" ++ show x ++ ")"
  show (STLC_Snd x) = "snd(" ++ show x ++ ")"
  show (STLC_Lambda ty x) = "\\" ++ show ty ++ ".[" ++ show x ++ "]"
  show (STLC_App ty x y) =
    "app(" ++ show ty ++ ": " ++ show x ++ ", " ++ show y ++ ")"
  show (STLC_Var k) = "v" ++ show k

public export
SignedCheckedSTLCTerm : SOMu_Context -> Type
SignedCheckedSTLCTerm ctx = DPair SubstObjMu (Checked_STLC_Term ctx)

public export
SignedSubstCtxMorph : SOMu_Context -> Type
SignedSubstCtxMorph ctx = DPair SubstObjMu (SubstMorph $ stlcCtxToSOMu ctx)

public export
SignedSubstMorph : Type
SignedSubstMorph = (ty : SubstObjMu ** SubstMorph Subst1 ty)

public export
checkSTLC :
  (ctx : SOMu_Context) -> STLC_Term -> Maybe (SignedCheckedSTLCTerm ctx)
checkSTLC ctx (STLC_Absurd t ty) = do
  (ty' ** t') <- checkSTLC ctx t
  case ty' of
    InSO SO0 => Just (ty ** Checked_STLC_Absurd {cod=ty} t')
    _ => Nothing
checkSTLC ctx STLC_Unit = Just (Subst1 ** Checked_STLC_Unit {ctx})
checkSTLC ctx (STLC_Left t ty) = do
  (ty' ** t') <- checkSTLC ctx t
  Just (ty' !+ ty ** Checked_STLC_Left {ctx} {lty=ty'} {rty=ty} t')
checkSTLC ctx (STLC_Right ty t) = do
  (ty' ** t') <- checkSTLC ctx t
  Just (ty !+ ty' ** Checked_STLC_Right {ctx} {lty=ty} {rty=ty'} t')
checkSTLC ctx (STLC_Case t l r) = do
  (ty ** t') <- checkSTLC ctx t
  case ty of
    InSO (lty !!+ rty) => do
      (lcod ** l') <- checkSTLC (lty :: ctx) l
      (rcod ** r') <- checkSTLC (rty :: ctx) r
      case decEq lcod rcod of
        Yes Refl =>
          Just (rcod ** Checked_STLC_Case {ctx} {lty} {rty} {cod=rcod} t' l' r')
        No _ => Nothing
    _ => Nothing
checkSTLC ctx (STLC_Pair l r) = do
  (lty ** l') <- checkSTLC ctx l
  (rty ** r') <- checkSTLC ctx r
  Just (lty !* rty ** Checked_STLC_Pair l' r')
checkSTLC ctx (STLC_Fst p) = do
  (pty ** p') <- checkSTLC ctx p
  case pty of
    InSO (lty !!* rty) => Just (lty ** Checked_STLC_Fst {ctx} {lty} {rty} p')
    _ => Nothing
checkSTLC ctx (STLC_Snd p) = do
  (pty ** p') <- checkSTLC ctx p
  case pty of
    InSO (lty !!* rty) => Just (rty ** Checked_STLC_Snd {ctx} {lty} {rty} p')
    _ => Nothing
checkSTLC ctx (STLC_Lambda vty t) = do
  (tty ** t') <- checkSTLC (vty :: ctx) t
  Just (vty !-> tty ** Checked_STLC_Lambda {ctx} {vty} {tty} t')
checkSTLC ctx (STLC_App ty f x) = do
  (fty ** f') <- checkSTLC ctx f
  (xty ** x') <- checkSTLC ctx x
  case decEq fty (xty !-> ty) of
    Yes Refl => Just (ty ** Checked_STLC_App {ctx} {dom=xty} {cod=ty} f' x')
    No _ => Nothing
checkSTLC ctx (STLC_Var i) = case inBounds i ctx of
  Yes ok => Just (index i ctx {ok} ** Checked_STLC_Var {ok})
  No _ => Nothing

public export
checkSTLC_valid :
  (ctx : SOMu_Context) -> (t : STLC_Term) ->
  {auto isValid : IsJustTrue (checkSTLC ctx t)} ->
  SignedCheckedSTLCTerm ctx
checkSTLC_valid ctx t {isValid} = fromIsJust isValid

public export
checkSTLC_closed_function_valid :
  (dom, cod : SubstObjMu) -> (t : STLC_Term) ->
  {auto isValid : IsJustTrue (checkSTLC [] t)} ->
  {auto expectedSig :
    DPair.fst (fromIsJust {x=(checkSTLC [] t)} isValid) = (dom !-> cod)} ->
  Checked_Closed_STLC_Function dom cod
checkSTLC_closed_function_valid dom cod t {isValid} {expectedSig}
  with (fromIsJust isValid)
    checkSTLC_closed_function_valid dom cod t {isValid} {expectedSig}
      | (ty ** m) =
        replace {p=(Checked_STLC_Term [])} expectedSig m

public export
stlcToCCC_ctx :
  (ctx : SOMu_Context) ->
  STLC_Term ->
  Maybe (SignedSubstCtxMorph ctx)
stlcToCCC_ctx ctx t = do
  (ty ** t') <- checkSTLC ctx t
  Just $ (ty ** compileCheckedTerm {ty} t')

public export
stlcToCCC_ctx_valid :
  (ctx : SOMu_Context) ->
  (t : STLC_Term) ->
  {auto isValid : IsJustTrue (stlcToCCC_ctx ctx t)} ->
  SignedSubstCtxMorph ctx
stlcToCCC_ctx_valid ctx t {isValid} = fromIsJust isValid

public export
compile_closed_function_valid :
  (dom, cod : SubstObjMu) -> (t : STLC_Term) ->
  {auto isValid : IsJustTrue (checkSTLC [] t)} ->
  {auto expectedSig :
    DPair.fst (fromIsJust {x=(checkSTLC [] t)} isValid) = (dom !-> cod)} ->
  SubstMorph dom cod
compile_closed_function_valid dom cod t {isValid} {expectedSig} =
  TermAsMorph $
    compileCheckedTerm {ctx=[]} {ty=(dom !-> cod)} $
    checkSTLC_closed_function_valid dom cod t {isValid} {expectedSig}

public export
stlcToCCC : STLC_Term -> Maybe SignedSubstMorph
stlcToCCC t = stlcToCCC_ctx [] t

public export
stlcToCCC_valid :
  (t : STLC_Term) ->
  {auto isValid : IsJustTrue (stlcToCCC t)} ->
  SignedSubstMorph
stlcToCCC_valid t {isValid} = fromIsJust isValid

public export
Show SignedSubstMorph where
  show (ty ** m) =
    "(" ++ show ty ++ " : " ++ showSubstMorph m ++ ")"

public export
stlcToBNC :
  (t : STLC_Term) ->
  {auto isValid : IsJustTrue (stlcToCCC t)} ->
  SignedBNCMorph
stlcToBNC t {isValid} =
  let (ty ** m) = stlcToCCC_valid t {isValid} in
  (substObjToNat Subst1, substObjToNat ty, substMorphToBNC m)

-------------------------------------------------------------------------------
---- Typed STLC terms (for possible future use in dividing passes further) ----
-------------------------------------------------------------------------------

public export
data STLC_Type : Type where
  STLC_Void : STLC_Type
  STLC_UnitTy : STLC_Type
  STLC_Either : STLC_Type -> STLC_Type -> STLC_Type
  STLC_PairTy : STLC_Type -> STLC_Type -> STLC_Type
  STLC_Function : STLC_Type -> STLC_Type -> STLC_Type

public export
Show STLC_Type where
  show STLC_Void = "void"
  show STLC_UnitTy = "unit"
  show (STLC_Either x y) = "(" ++ show x ++ " | " ++ show y ++ ")"
  show (STLC_PairTy x y) = "(" ++ show x ++ " , " ++ show y ++ ")"
  show (STLC_Function x y) = "(" ++ show x ++ " -> " ++ show y ++ ")"

public export
STLC_Context : Type
STLC_Context = List STLC_Type

public export
data TSTLC_Term : STLC_Context -> STLC_Type -> Type where
  -- The "void" or "absurd" function, which takes a term of type Void
  -- to any type; there's no explicit constructor for terms of type Void,
  -- but a lambda could introduce one.  The SubstObjMu is the type of the
  -- resulting term (since we can get any type from a term of Void).
  TSTLC_Absurd : {ctx : STLC_Context} -> {ty : STLC_Type} ->
    TSTLC_Term ctx STLC_Void -> TSTLC_Term ctx ty

  -- The only term of type Unit.
  TSTLC_Unit : {ctx : STLC_Context} -> TSTLC_Term ctx STLC_UnitTy

  -- Construct coproducts
  TSTLC_Left : {ctx : STLC_Context} -> {lty, rty : STLC_Type} ->
    TSTLC_Term ctx lty -> TSTLC_Term ctx (STLC_Either lty rty)
  TSTLC_Right : {ctx : STLC_Context} -> {lty, rty : STLC_Type} ->
    TSTLC_Term ctx rty -> TSTLC_Term ctx (STLC_Either lty rty)

  -- Case statement : parameters are expression to case on, which must be
  -- a coproduct, and then left and right case, which must be of the same
  -- type, which becomes the type of the overall term.
  TSTLC_Case : {ctx : STLC_Context} -> {lty, rty, cod : STLC_Type} ->
    TSTLC_Term ctx (STLC_Either lty rty) ->
    TSTLC_Term (lty :: ctx) cod -> TSTLC_Term (rty :: ctx) cod ->
    TSTLC_Term ctx cod

  -- Construct a term of a pair type
  TSTLC_Pair : {ctx : STLC_Context} -> {lty, rty : STLC_Type} ->
    TSTLC_Term ctx lty -> TSTLC_Term ctx rty ->
    TSTLC_Term ctx (STLC_PairTy lty rty)

  -- Projections; in each case, the given term must be of a product type
  TSTLC_Fst : {ctx : STLC_Context} -> {lty, rty : STLC_Type} ->
    TSTLC_Term ctx (STLC_PairTy lty rty) -> TSTLC_Term ctx lty
  TSTLC_Snd : {ctx : STLC_Context} -> {lty, rty : STLC_Type} ->
    TSTLC_Term ctx (STLC_PairTy lty rty) -> TSTLC_Term ctx rty

  -- Lambda abstraction:  introduce into the context a (de Bruijn-indexed)
  -- variable of the given type, and produce a term with that extended context.
  TSTLC_Lambda : {ctx : STLC_Context} -> {dom, cod : STLC_Type} ->
    TSTLC_Term (dom :: ctx) cod -> TSTLC_Term ctx (STLC_Function dom cod)

  -- Function application; the first parameter is the function's domain
  TSTLC_App : {ctx : STLC_Context} -> {dom, cod : STLC_Type} ->
    TSTLC_Term ctx (STLC_Function dom cod) -> TSTLC_Term ctx dom ->
    TSTLC_Term ctx cod

  -- The variable at the given de Bruijn index
  TSTLC_Var : (ctx : STLC_Context) -> (i : Nat) -> {auto ok : InBounds n ctx} ->
    TSTLC_Term ctx (index n ctx {ok})

---------------------------------------------------
---------------------------------------------------
---- Older version of polynomial-type category ----
---------------------------------------------------
---------------------------------------------------

public export
partial
MetaSOMorph : SubstObjMu -> SubstObjMu -> Type
-- The unique morphism from the initial object to a given object
MetaSOMorph (InSO SO0) _ = ()
-- There are no morphisms from the terminal object to the initial object
MetaSOMorph (InSO SO1) (InSO SO0) = Void
-- The unique morphism from a given object to the terminal object
-- (in this case, the given object is also the terminal object)
MetaSOMorph (InSO SO1) (InSO SO1) = Unit
-- To form a morphism from the terminal object to a coproduct,
-- we choose a morphism from the terminal object to either the left
-- or the right object of the coproduct
MetaSOMorph (InSO SO1) (InSO (y !!+ z)) =
  Either (MetaSOMorph Subst1 y) (MetaSOMorph Subst1 z)
-- To form a morphism from the terminal object to a product,
-- we choose morphisms from the terminal object to both the left
-- and the right object of the product
MetaSOMorph (InSO SO1) (InSO (y !!* z)) =
  Pair (MetaSOMorph Subst1 y) (MetaSOMorph Subst1 z)
-- The unique morphism from a coproduct to the terminal object
MetaSOMorph (InSO (_ !!+ _)) (InSO SO1) = ()
-- Coproducts are eliminated by cases
MetaSOMorph (InSO (x !!+ y)) z = Pair (MetaSOMorph x z) (MetaSOMorph y z)
-- The unique morphism from a product to the terminal object
MetaSOMorph (InSO (_ !!* _)) (InSO SO1) = ()
-- 0 * y === 0
MetaSOMorph (InSO ((InSO SO0) !!* y)) z = ()
-- 1 * y === y
MetaSOMorph (InSO ((InSO SO1) !!* y)) z = MetaSOMorph y z
-- Distributivity of products over coproducts
MetaSOMorph (InSO ((InSO (x !!+ x')) !!* y)) z =
  MetaSOMorph ((x !* y) !+ (x' !* y)) z
-- Associativity of products
MetaSOMorph (InSO ((InSO (x !!* x')) !!* y)) z = MetaSOMorph (x !* (x' !* y)) z

-----------------------------------------------------------
-----------------------------------------------------------
---- Idris representation of substitutive finite topos ----
-----------------------------------------------------------
-----------------------------------------------------------

-- A finite type, generated only from initial and terminal objects
-- and coproducts and products, which is indexed by a natural-number size
-- (which is the cardinality of the set of the type's elements).
public export
data FinSubstT : (0 cardinality, depth : Nat) -> Type where
  FinInitial : FinSubstT 0 0
  FinTerminal : FinSubstT 1 0
  FinCoproduct : {0 cx, dx, cy, dy : Nat} ->
    FinSubstT cx dx -> FinSubstT cy dy -> FinSubstT (cx + cy) (smax dx dy)
  FinProduct : {0 cx, dx, cy, dy : Nat} ->
    FinSubstT cx dx -> FinSubstT cy dy -> FinSubstT (cx * cy) (smax dx dy)

public export
record FSAlg (0 a : (0 c, d : Nat) -> FinSubstT c d -> Type) where
  constructor MkFSAlg
  fsInitialAlg : a 0 0 FinInitial
  fsTerminalAlg : a 1 0 FinTerminal
  fsCoproductAlg : {0 cx, dx, cy, dy : Nat} ->
    (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
    a cx dx x -> a cy dy y -> a (cx + cy) (smax dx dy) (FinCoproduct x y)
  fsProductAlg : {0 cx, dx, cy, dy : Nat} ->
    (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
    a cx dx x -> a cy dy y -> a (cx * cy) (smax dx dy) (FinProduct x y)

public export
finSubstCata :
  {0 a : (0 c, d : Nat) -> FinSubstT c d -> Type} ->
  FSAlg a ->
  {0 cardinality, depth : Nat} ->
  (x : FinSubstT cardinality depth) -> a cardinality depth x
finSubstCata alg FinInitial = alg.fsInitialAlg
finSubstCata alg FinTerminal = alg.fsTerminalAlg
finSubstCata alg (FinCoproduct x y) =
  alg.fsCoproductAlg x y (finSubstCata alg x) (finSubstCata alg y)
finSubstCata alg (FinProduct x y) =
  alg.fsProductAlg x y (finSubstCata alg x) (finSubstCata alg y)

public export
data FinSubstTerm : {0 c, d : Nat} -> FinSubstT c d -> Type where
  FinUnit : FinSubstTerm FinTerminal
  FinLeft :
    {0 cx, dx, cy, dy : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
    FinSubstTerm x -> FinSubstTerm (FinCoproduct x y)
  FinRight :
    {0 cx, dx, cy, dy : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
    FinSubstTerm y -> FinSubstTerm (FinCoproduct x y)
  FinPair :
    {0 cx, dx, cy, dy : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
    FinSubstTerm x -> FinSubstTerm y -> FinSubstTerm (FinProduct x y)

public export
record FSTAlg
    (0 a : (0 c, d : Nat) -> (x : FinSubstT c d) -> FinSubstTerm x -> Type)
    where
  constructor MkFSTAlg
  fstUnit : a 1 0 FinTerminal FinUnit
  fstLeft : {0 cx, dx, cy, dy : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
    (t : FinSubstTerm x) ->
    a cx dx x t ->
    a (cx + cy) (smax dx dy) (FinCoproduct x y) (FinLeft t)
  fstRight : {0 cx, dx, cy, dy : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
    (t : FinSubstTerm y) ->
    a cy dy y t ->
    a (cx + cy) (smax dx dy) (FinCoproduct x y) (FinRight t)
  fstPair : {0 cx, dx, cy, dy : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
    (t : FinSubstTerm x) -> (t' : FinSubstTerm y) ->
    a cx dx x t -> a cy dy y t' ->
    a (cx * cy) (smax dx dy) (FinProduct x y) (FinPair t t')

mutual
  public export
  fstCata :
    {0 a : (0 c, d : Nat) -> (x : FinSubstT c d) -> FinSubstTerm x -> Type} ->
    FSTAlg a ->
    {0 c, d : Nat} -> {x : FinSubstT c d} ->
    (t : FinSubstTerm x) -> a c d x t
  fstCata {a} alg {x=FinInitial} = fstCataInitial {a}
  fstCata {a} alg {x=FinTerminal} = fstCataTerminal {a} alg
  fstCata {a} alg {x=(FinCoproduct x y)} = fstCataCoproduct {a} alg {x} {y}
  fstCata {a} alg {x=(FinProduct x y)} = fstCataProduct {a} alg {x} {y}

  public export
  fstCataInitial :
    {0 a : (0 c, d : Nat) -> (x : FinSubstT c d) -> FinSubstTerm x -> Type} ->
    (t : FinSubstTerm FinInitial) -> a _ _ FinInitial t
  fstCataInitial FinUnit impossible
  fstCataInitial (FinLeft x) impossible
  fstCataInitial (FinRight x) impossible
  fstCataInitial (FinPair x y) impossible

  public export
  fstCataTerminal :
    {0 a : (0 c, d : Nat) -> (x : FinSubstT c d) -> FinSubstTerm x -> Type} ->
    FSTAlg a ->
    (t : FinSubstTerm FinTerminal) -> a _ _ FinTerminal t
  fstCataTerminal alg FinUnit = alg.fstUnit

  public export
  fstCataCoproduct :
    {0 a : (0 c, d : Nat) -> (x : FinSubstT c d) -> FinSubstTerm x -> Type} ->
    FSTAlg a ->
    {0 cx, dx, cy, dy : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
    (t : FinSubstTerm (FinCoproduct x y)) ->
    a _ _ (FinCoproduct x y) t
  fstCataCoproduct alg (FinLeft t) = alg.fstLeft t $ fstCata alg t
  fstCataCoproduct alg (FinRight t) = alg.fstRight t $ fstCata alg t

  public export
  fstCataProduct :
    {0 a : (0 c, d : Nat) -> (x : FinSubstT c d) -> FinSubstTerm x -> Type} ->
    FSTAlg a ->
    {0 cx, dx, cy, dy : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
    (t : FinSubstTerm (FinProduct x y)) ->
    a _  _ (FinProduct x y) t
  fstCataProduct alg (FinPair t t') =
    alg.fstPair t t' (fstCata alg t) (fstCata alg t')

public export
data FinSubstMorph : {0 cx, dx, cy, dy : Nat} ->
    (0 depth : Nat) -> FinSubstT cx dx -> FinSubstT cy dy -> Type where
  FinId : {0 cx, dx : Nat} ->
    (x : FinSubstT cx dx) -> FinSubstMorph {cx} {cy=cx} 0 x x
  FinCompose : {0 cx, dx, cy, dy, cz, dz : Nat} -> {0 dg, df : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} -> {z : FinSubstT cz dz} ->
    FinSubstMorph dg y z -> FinSubstMorph df x y ->
    FinSubstMorph (smax dg df) x z
  FinFromInit : {0 cy, dy : Nat} -> (y : FinSubstT cy dy) ->
    FinSubstMorph {cx=0} {cy} 0 FinInitial y
  FinToTerminal : {0 cx, dx : Nat} -> (x : FinSubstT cx dx) ->
    FinSubstMorph {cx} {cy=1} 0 x FinTerminal
  FinInjLeft : {0 cx, dx, cy, dy : Nat} ->
    (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
    FinSubstMorph {cx} {cy=(cx + cy)} 0 x (FinCoproduct {cx} {cy} x y)
  FinInjRight : {0 cx, dx, cy, dy : Nat} ->
    (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
    FinSubstMorph {cx=cy} {cy=(cx + cy)} 0 y (FinCoproduct {cx} {cy} x y)
  FinCase : {0 cx, dx, cy, dy, cz, dz : Nat} -> {0 df, dg : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} -> {z : FinSubstT cz dz} ->
    FinSubstMorph {cx} {cy=cz} df x z ->
    FinSubstMorph {cx=cy} {cy=cz} dg y z ->
    FinSubstMorph {cx=(cx + cy)} {cy=cz}
      (smax df dg) (FinCoproduct {cx} {cy} x y) z
  FinProd : {0 cx, dx, cy, dy, cz, dz : Nat} -> {0 df, dg : Nat} ->
    {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} -> {z : FinSubstT cz dz} ->
    FinSubstMorph {cx} {cy} df x y ->
    FinSubstMorph {cx} {cy=cz} dg x z ->
    FinSubstMorph {cx} {cy=(cy * cz)} (smax df dg) x
      (FinProduct {cx=cy} {cy=cz} y z)
  FinProjLeft : {0 cx, dx, cy, dy : Nat} ->
    (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
    FinSubstMorph {cx=(cx * cy)} {cy=cx} 0 (FinProduct {cx} {cy} x y) x
  FinProjRight : {0 cx, dx, cy, dy : Nat} ->
    (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
    FinSubstMorph {cx=(cx * cy)} {cy} 0 (FinProduct {cx} {cy} x y) y
  FinDistrib : {0 cx, dx, cy, dy, cz, dz : Nat} ->
    (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) -> (z : FinSubstT cz dz) ->
    FinSubstMorph 0
      (FinProduct x (FinCoproduct y z))
      (FinCoproduct (FinProduct x y) (FinProduct x z))

public export
0 finSubstHomObjCard : {0 cx, dx, cy, dy : Nat} ->
  FinSubstT cx dx -> FinSubstT cy dy -> Nat
finSubstHomObjCard {cx} {cy} _ _ = power cy cx

public export
EvalMorphType : {0 cx, dx, cy, dy, dh : Nat} ->
  (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
  FinSubstT (finSubstHomObjCard x y) dh -> (df : Nat) -> Type
EvalMorphType x y hxy df = FinSubstMorph df (FinProduct hxy x) y

public export
HomObjWithEvalMorphType : {0 cx, dx, cy, dy : Nat} ->
  FinSubstT cx dx -> FinSubstT cy dy -> (dh : Nat) -> Type
HomObjWithEvalMorphType x y dh =
  (hxy : FinSubstT (finSubstHomObjCard x y) dh **
   Exists {type=Nat} (EvalMorphType x y hxy))

-- Compute the exponential object and evaluation morphism of the given finite
-- substitutive types.
public export
FinSubstHomDepthObjEval : {0 cx, dx, cy, dy : Nat} ->
  (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
  Exists {type=Nat} (HomObjWithEvalMorphType x y)
-- 0 -> x == 1
FinSubstHomDepthObjEval FinInitial x =
  (Evidence 0 (FinTerminal **
    Evidence 1 $
      FinCompose (FinFromInit x) $ FinProjRight FinTerminal FinInitial))
-- 1 -> x == x
FinSubstHomDepthObjEval {cy} {dy} FinTerminal x =
  let eq = mulPowerZeroRightNeutral {m=cy} {n=cy} in
  (Evidence dy $ rewrite eq in (x **
   Evidence 0 $ rewrite eq in FinProjLeft x FinTerminal))
-- (x + y) -> z == (x -> z) * (y -> z)
FinSubstHomDepthObjEval {cx=(cx + cy)} {cy=cz} (FinCoproduct x y) z with
 (FinSubstHomDepthObjEval x z, FinSubstHomDepthObjEval y z)
  FinSubstHomDepthObjEval {cx=(cx + cy)} {cy=cz} (FinCoproduct x y) z |
   ((Evidence dxz (hxz ** (Evidence hdxz evalxz))),
    (Evidence dyz (hyz ** (Evidence hdyz evalyz)))) =
    (Evidence (smax dxz dyz) $ rewrite powerOfSum cz cx cy in
     (FinProduct hxz hyz ** Evidence
      (S (maximum (smax hdxz hdyz) 5))
      $
      rewrite powerOfSum cz cx cy in
      FinCompose (FinCase evalxz evalyz) $ FinCompose
        (FinCase
          (FinCompose (FinInjLeft _ _)
            (FinProd (FinCompose (FinProjLeft _ _) (FinProjLeft _ _))
              (FinProjRight _ _)))
          (FinCompose (FinInjRight _ _)
            (FinProd (FinCompose (FinProjRight _ _) (FinProjLeft _ _))
              (FinProjRight _ _))))
        (FinDistrib (FinProduct hxz hyz) x y)))
-- (x * y) -> z == x -> y -> z
FinSubstHomDepthObjEval {cx=(cx * cy)} {dx=(smax dx dy)} {cy=cz} {dy=dz}
  (FinProduct x y) z with
  (FinSubstHomDepthObjEval y z)
    FinSubstHomDepthObjEval {cx=(cx * cy)} {dx=(smax dx dy)} {cy=cz} {dy=dz}
      (FinProduct x y) z | (Evidence dyz (hyz ** Evidence hdyz evalyz)) =
        let
          Evidence dxyz hexyz = FinSubstHomDepthObjEval {dx} {dy=dyz} x hyz
          (hxyz ** Evidence dexyz evalxyz) = hexyz
        in
        Evidence dxyz $ rewrite powerOfMulSym cz cx cy in
          (hxyz ** Evidence (smax hdyz (smax (smax dexyz 2) 1)) $
            rewrite powerOfMulSym cz cx cy in
            FinCompose evalyz $ FinProd
              (FinCompose evalxyz
               (FinProd
                (FinProjLeft hxyz (FinProduct x y))
                (FinCompose
                  (FinProjLeft x y) (FinProjRight hxyz (FinProduct x y)))))
              (FinCompose
                (FinProjRight x y) (FinProjRight hxyz (FinProduct x y))))

public export
0 finSubstHomObjDepth : {0 cx, dx, cy, dy : Nat} ->
  FinSubstT cx dx -> FinSubstT cy dy -> Nat
finSubstHomObjDepth x y = fst $ FinSubstHomDepthObjEval x y

public export
finSubstHomObj : {0 cx, dx, cy, dy : Nat} ->
  (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
  FinSubstT (finSubstHomObjCard x y) (finSubstHomObjDepth x y)
finSubstHomObj x y = fst $ snd $ FinSubstHomDepthObjEval x y

public export
0 finSubstEvalMorphDepth : {0 cx, dx, cy, dy : Nat} ->
  (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
  Nat
finSubstEvalMorphDepth x y = fst (snd (snd (FinSubstHomDepthObjEval x y)))

public export
finSubstEvalMorph : {0 cx, dx, cy, dy : Nat} ->
  (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
  EvalMorphType x y (finSubstHomObj x y) (finSubstEvalMorphDepth x y)
finSubstEvalMorph x y = snd $ snd $ snd $ FinSubstHomDepthObjEval x y

------------------------------------
---- Compilation to polynomials ----
------------------------------------

public export
0 FSToBANatMorph : {0 cx, dx, cy, dy : Nat} ->
  {0 depth : Nat} -> {dom : FinSubstT cx dx} -> {cod : FinSubstT cy dy} ->
  FinSubstMorph depth dom cod ->
  BNCPolyM
FSToBANatMorph {cx} {dx} {cy} {dy} {depth} {dom} {cod} morph =
  ?FSToBANatMorph_hole

--------------------------------------
---- Metalanguage interpretations ----
--------------------------------------

public export
InterpFSAlg : FSAlg (\_, _, _ => Type)
InterpFSAlg = MkFSAlg Void Unit (const $ const Either) (const $ const Pair)

public export
interpFinSubst : {0 c, d : Nat} -> FinSubstT c d -> Type
interpFinSubst = finSubstCata InterpFSAlg

public export
InterpTrAlg : FSTAlg (\_, _, x, _ => interpFinSubst x)
InterpTrAlg = MkFSTAlg () (\_ => Left) (\_ => Right) (\_, _ => MkPair)

public export
interpFinSubstTerm : {0 c, d : Nat} -> {x : FinSubstT c d} ->
  FinSubstTerm x -> interpFinSubst {c} {d} x
interpFinSubstTerm {x} = fstCata InterpTrAlg

public export
0 interpFinSubstMorph : {0 cx, dx, cy, dy, depth : Nat} ->
  {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
  FinSubstMorph {cx} {dx} {cy} {dy} depth x y ->
  interpFinSubst {c=cx} {d=dx} x ->
  interpFinSubst {c=cy} {d=dy} y
interpFinSubstMorph m = ?interpFinSubstMorph_hole
