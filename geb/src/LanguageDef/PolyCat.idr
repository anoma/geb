module LanguageDef.PolyCat

import Library.IdrisUtils
import Library.IdrisCategories

%default total

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
pfPos (pos ** dir) = pos

public export
pfDir : {p : PolyFunc} -> pfPos p -> Type
pfDir {p=(pos ** dir)} i = dir i

public export
pfPDir : PolyFunc -> Type
pfPDir p = DPair (pfPos p) (pfDir {p})

public export
InterpPolyFunc : PolyFunc -> Type -> Type
InterpPolyFunc (pos ** dir) x = (i : pos ** (dir i -> x))

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
PolyNatTrans (ppos ** pdir) (qpos ** qdir) =
  (onPos : ppos -> qpos ** SliceMorphism (qdir . onPos) pdir)

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
  SliceMorphism (InterpPolyFunc p) (InterpPolyFunc q)
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
VertCartFactPos : {p, q : PolyFunc} -> PolyNatTrans p q -> Type
VertCartFactPos {p} {q} alpha = pfPos p

public export
VertCartFactDir : {p, q : PolyFunc} -> (alpha : PolyNatTrans p q) ->
  VertCartFactPos {p} {q} alpha -> Type
VertCartFactDir {p=(ppos ** pdir)} {q=(qpos ** qdir)} (onPos ** onDir) i =
  qdir (onPos i)

public export
VertCartFactFunc : {p, q : PolyFunc} -> PolyNatTrans p q -> PolyFunc
VertCartFactFunc alpha = (VertCartFactPos alpha ** VertCartFactDir alpha)

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
PFHomPos : Type -> Type
PFHomPos _ = Unit

public export
PFHomDir : (a : Type) -> PFHomPos a -> Type
PFHomDir a () = a

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
pfEitherPos : Type -> Type
pfEitherPos a = Either Unit a

public export
pfEitherDir : (a : Type) -> pfEitherPos a -> Type
pfEitherDir a (Left ()) = Unit
pfEitherDir a (Right _) = Void

public export
pfEitherArena : Type -> PolyFunc
pfEitherArena a = (pfEitherPos a ** pfEitherDir a)

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
pfCoproductPos : PolyFunc -> PolyFunc -> Type
pfCoproductPos (ppos ** pdir) (qpos ** qdir) = Either ppos qpos

public export
pfCoproductDir : (p, q : PolyFunc) -> pfCoproductPos p q -> Type
pfCoproductDir (ppos ** pdir) (qpos ** qdir) = eitherElim pdir qdir

public export
pfCoproductArena : PolyFunc -> PolyFunc -> PolyFunc
pfCoproductArena p q = (pfCoproductPos p q ** pfCoproductDir p q)

public export
pfProductPos : PolyFunc -> PolyFunc -> Type
pfProductPos (ppos ** pdir) (qpos ** qdir) = Pair ppos qpos

public export
pfProductDir : (p, q : PolyFunc) -> pfProductPos p q -> Type
pfProductDir (ppos ** pdir) (qpos ** qdir) = uncurry Either . bimap pdir qdir

public export
pfProductArena : PolyFunc -> PolyFunc -> PolyFunc
pfProductArena p q = (pfProductPos p q ** pfProductDir p q)

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
pfParProductPos : PolyFunc -> PolyFunc -> Type
pfParProductPos = pfProductPos

public export
pfParProductDir : (p, q : PolyFunc) -> pfParProductPos p q -> Type
pfParProductDir (ppos ** pdir) (qpos ** qdir) = uncurry Pair . bimap pdir qdir

public export
pfParProductArena : PolyFunc -> PolyFunc -> PolyFunc
pfParProductArena p q = (pfParProductPos p q ** pfParProductDir p q)

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
pfCompositionPowerArena : PolyFunc -> Nat -> PolyFunc
pfCompositionPowerArena p Z =
  PFIdentityArena
pfCompositionPowerArena p (S n) =
  pfCompositionArena p (pfCompositionPowerArena p n)

public export
pfCompositionPowerPos : PolyFunc -> Nat -> Type
pfCompositionPowerPos p n = pfPos (pfCompositionPowerArena p n)

public export
pfCompositionPowerDir : (p : PolyFunc) -> (n : Nat) ->
  pfCompositionPowerPos p n -> Type
pfCompositionPowerDir p n = pfDir {p=(pfCompositionPowerArena p n)}

public export
pfSetCoproductPos : {a : Type} -> (a -> PolyFunc) -> Type
pfSetCoproductPos {a} ps = DPair a (fst . ps)

public export
pfSetCoproductDir : {a : Type} ->
  (ps : a -> PolyFunc) -> pfSetCoproductPos ps -> Type
pfSetCoproductDir ps (x ** xpos) = snd (ps x) xpos

public export
pfSetCoproductArena : {a : Type} -> (a -> PolyFunc) -> PolyFunc
pfSetCoproductArena ps = (pfSetCoproductPos ps ** pfSetCoproductDir ps)

public export
pfSetProductPos : {a : Type} -> (a -> PolyFunc) -> Type
pfSetProductPos {a} ps = (x : a) -> fst $ ps x

public export
pfSetProductDir : {a : Type} ->
  (ps : a -> PolyFunc) -> pfSetProductPos ps -> Type
pfSetProductDir {a} ps fpos = (x : a ** snd (ps x) $ fpos x)

public export
pfSetProductArena : {a : Type} -> (a -> PolyFunc) -> PolyFunc
pfSetProductArena {a} ps = (pfSetProductPos ps ** pfSetProductDir ps)

public export
pfSetParProductPos : {a : Type} -> (a -> PolyFunc) -> Type
pfSetParProductPos = pfSetProductPos

public export
pfSetParProductDir : {a : Type} ->
  (ps : a -> PolyFunc) -> pfSetParProductPos ps -> Type
pfSetParProductDir {a} ps fpos = ((x : a) -> snd (ps x) $ fpos x)

public export
pfSetParProductArena : {a : Type} -> (a -> PolyFunc) -> PolyFunc
pfSetParProductArena {a} ps = (pfSetParProductPos ps ** pfSetParProductDir ps)

public export
pfHomObj : PolyFunc -> PolyFunc -> PolyFunc
pfHomObj q r =
  pfSetProductArena {a=(pfPos q)} $
    pfCompositionArena r .
    pfCoproductArena PFIdentityArena .
    PFConstArena . pfDir {p=q}

public export
pfExpObj : PolyFunc -> PolyFunc -> PolyFunc
pfExpObj = flip pfHomObj

public export
pfParProdClosurePos : PolyFunc -> PolyFunc -> Type
pfParProdClosurePos = PolyNatTrans

public export
pfParProdClosureDir : (q, r : PolyFunc) -> pfParProdClosurePos q r -> Type
pfParProdClosureDir q r f = DPair (pfPos q) (pfDir {p=r} . pntOnPos f)

public export
pfParProdClosure : PolyFunc -> PolyFunc -> PolyFunc
pfParProdClosure q r = (pfParProdClosurePos q r ** pfParProdClosureDir q r)

public export
pfBaseChangePos : (p : PolyFunc) -> {a : Type} -> (a -> pfPos p) -> Type
pfBaseChangePos p {a} f = a

public export
pfBaseChangeDir : (p : PolyFunc) -> {a : Type} -> (f : a -> pfPos p) ->
  pfBaseChangePos p {a} f -> Type
pfBaseChangeDir (pos ** dir) {a} f i = dir $ f i

public export
pfBaseChangeArena : (p : PolyFunc) -> {a : Type} -> (a -> pfPos p) -> PolyFunc
pfBaseChangeArena p {a} f = (pfBaseChangePos p {a} f ** pfBaseChangeDir p {a} f)

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

-- Formula 5.81 from the "General Theory of Interaction" book.
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

-- Formula 5.84 from the "General Theory of Interaction" book (I think).
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
pntAssociate : (p, q, r : PolyFunc) ->
  PolyNatTrans
    (pfCompositionArena (pfCompositionArena p q) r)
    (pfCompositionArena p (pfCompositionArena q r))
pntAssociate (ppos ** pdir) (qpos ** qdir) (rpos ** rdir) =
  (\pqi =>
    (fst (fst pqi) **
     \pd => (snd (fst pqi) pd ** \qd => snd pqi (pd ** qd))) **
   \pqi, qd => ((fst qd ** fst (snd qd)) ** snd (snd qd)))

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
PFAlg (pos ** dir) a = (i : pos) -> (dir i -> a) -> a

public export
PFNAlg : PolyFuncN -> Type -> Type
PFNAlg (pos ** dir) a = (i : pos) -> Vect (dir i) a -> a

public export
PFAlgFromN : {0 a : Type} -> {p : PolyFuncN} ->
  PFNAlg p a -> PFAlg (pfnFunc p) a
PFAlgFromN {a} {p=(pos ** dir)} alg i = alg i . finFToVect

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

----------------------------------------------
---- Catamorphisms of polynomial functors ----
----------------------------------------------

public export
pfCata : {0 p : PolyFunc} -> {0 a : Type} -> PFAlg p a -> PolyFuncMu p -> a
pfCata {p=p@(pos ** dir)} {a} alg (InPFM i da) =
  alg i $ \d : dir i => pfCata {p} alg $ da d

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
pfParamCata : {0 p : PolyFunc} -> {0 x, a : Type} ->
  PFParamAlg p x a -> x -> PolyFuncMu p -> a
pfParamCata alg = flip $ pfCata alg

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

-- Catamorphism on a pair of `PolyFuncMu`s giving all combinations of cases
-- to the algebra.  Uses the product-hom adjunction.
public export
PFProductHomAdjAlg : PolyFunc -> PolyFunc -> Type -> Type
PFProductHomAdjAlg p q a = PFAlg p (PFAlg q a)

public export
pfProductHomAdjCata : {0 p, q : PolyFunc} -> {0 a : Type} ->
  PFProductHomAdjAlg p q a -> PolyFuncMu p -> PolyFuncMu q -> a
pfProductHomAdjCata {p} {q} alg ep eq = pfCata {p=q} (pfCata {p} alg ep) eq

----------------------------------
---- Polynomial (free) monads ----
----------------------------------

public export
data PFTranslatePos : PolyFunc -> Type -> Type where
  PFVar : {0 p : PolyFunc} -> {0 a : Type} -> a -> PFTranslatePos p a
  PFCom : {0 p : PolyFunc} -> {0 a : Type} -> pfPos p -> PFTranslatePos p a

public export
PFTranslateDir : (p : PolyFunc) -> (a : Type) -> PFTranslatePos p a -> Type
PFTranslateDir (pos ** dir) a (PFVar ea) = Void
PFTranslateDir (pos ** dir) a (PFCom i) = dir i

public export
PFTranslate : PolyFunc -> Type -> PolyFunc
PFTranslate p a = (PFTranslatePos p a ** PFTranslateDir p a)

public export
PolyFuncFreeMPos : PolyFunc -> Type
PolyFuncFreeMPos p = PolyFuncMu $ PFTranslate p ()

public export
PolyFuncFreeMDirAlg : (p : PolyFunc) -> PFAlg (PFTranslate p ()) Type
PolyFuncFreeMDirAlg (pos ** dir) (PFVar ()) d = Unit
PolyFuncFreeMDirAlg (pos ** dir) (PFCom i) d = DPair (dir i) d

public export
PolyFuncFreeMDir : (p : PolyFunc) -> PolyFuncFreeMPos p -> Type
PolyFuncFreeMDir p = pfCata {p=(PFTranslate p ())} $ PolyFuncFreeMDirAlg p

public export
PolyFuncFreeM : PolyFunc -> PolyFunc
PolyFuncFreeM p = (PolyFuncFreeMPos p ** PolyFuncFreeMDir p)

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
pfFreeCata : {p : PolyFunc} -> {a, b : Type} ->
  PFTranslateAlg p a b -> InterpPolyFuncFreeM p a -> b
pfFreeCata {p} {a} {b} alg =
  pfCata {p=(PFTranslate p a)} {a=b} alg . PolyFMInterpToMuTranslate p a

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
PFCoalg (pos ** dir) a = a -> (i : pos ** (dir i -> a))

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
PPathPredGenPosDec : {p : PolyFunc} ->
  (dirDec : (i' : pfPos p) -> (di', di'' : pfDir {p} i') -> Dec (di' = di'')) ->
  (pred : PPathPred p) -> (i : pfPos p) -> (pp : PPathPos p i) ->
  Dec (PPathPredGenPosT {p} pred i pp)
PPathPredGenPosDec {p} dirDec pred i (PPRoot i) =
  ?PPathPredGenPosDec_hole_root
PPathPredGenPosDec {p} dirDec pred j (PPPath {i} pp di j) =
  let r = PPathPredGenPosDec {p} dirDec pred i pp in
  ?PPathPredGenPosDec_hole_path

public export
PPathPredGenPosDecPred : {p : PolyFunc} ->
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
PPathPredGenCorrect : {p : PolyFunc} -> PPathPred p -> Type
PPathPredGenCorrect {p} pred =
  (i : pfPos p) -> (ppi : PPathPos p i) ->
  PPathPredGenPos {p} pred i ppi -> (di : pfDir {p} i) ->
  IsJustTrue (pred i ppi di)

public export
PPathPredNotGenCorrect : {p : PolyFunc} -> PPathPred p -> Type
PPathPredNotGenCorrect {p} pred =
  (i : pfPos p) -> (ppi : PPathPos p i) ->
  PPathPredNotGenPos {p} pred i ppi -> (di : pfDir {p} i) ->
  IsNothingTrue (pred i ppi di)

public export
PPathPredCorrect : {p : PolyFunc} -> PPathPred p -> Type
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
PolyFuncCofreeCMPosNuScaleToPTree : {p : PolyFunc} ->
  PolyFuncCofreeCMPosFromNuScale p -> PolyFuncCofreeCMFromPTreePos p
PolyFuncCofreeCMPosNuScaleToPTree {p=p@(pos ** dir)} (InPFN (PFNode () i) d) =
  ?PolyFuncCofreeCMPosNuScaleToPTree_hole

public export
PolyFuncCofreeCMPosPTreeToNuScale : {p : PolyFunc} ->
  PolyFuncCofreeCMFromPTreePos p -> PolyFuncCofreeCMPosFromNuScale p
PolyFuncCofreeCMPosPTreeToNuScale {p=p@(pos ** dir)} =
  ?PolyFuncCofreeCMPosPTreeToNuScale_hole

public export
PolyFuncCofreeCMDirNuScaleToPTree : {p : PolyFunc} ->
  (i : PolyFuncCofreeCMPosFromNuScale p) ->
  PolyFuncCofreeCMDirFromNuScale p i ->
  PolyFuncCofreeCMFromPTreeDir p (PolyFuncCofreeCMPosNuScaleToPTree i)
PolyFuncCofreeCMDirNuScaleToPTree {p=(pos ** dir)} i di =
  ?PolyFuncCofreeCMDirNuScaleToPTree_hole

public export
PolyFuncCofreeCMDirPTreeToNuScale : {p : PolyFunc} ->
  (i : PolyFuncCofreeCMFromPTreePos p) ->
  PolyFuncCofreeCMFromPTreeDir p i ->
  PolyFuncCofreeCMDirFromNuScale p (PolyFuncCofreeCMPosPTreeToNuScale i)
PolyFuncCofreeCMDirPTreeToNuScale {p=(pos ** dir)} i di =
  ?PolyFuncCofreeCMDPTreeToNuScale_hole

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
      (pntAssociate p p p)

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
      (pntAssociate p p p)
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

-----------------------------------------------------------
-----------------------------------------------------------
---- Polynomial comands as categories (and vice versa) ----
-----------------------------------------------------------
-----------------------------------------------------------

public export
record CatSig where
  constructor MkCatSig
  catObj : Type
  catMorph : catObj -> catObj -> Type
  catId : (a : catObj) -> catMorph a a
  catComp : {a, b, c : catObj} -> catMorph b c -> catMorph a b -> catMorph a c

public export
record CatSigCorrect (cat : CatSig) where
  constructor MkCatSigCorrect
  catLeftId : {a, b : catObj cat} ->
    (m : catMorph cat a b) -> catComp cat {a} {b} {c=b} (catId cat b) m = m
  catRightId : {a, b : catObj cat} ->
    (m : catMorph cat a b) -> catComp cat {a} {b=a} {c=b} m (catId cat a) = m
  catAssoc : {a, b, c, d : catObj cat} ->
    (h : catMorph cat c d) ->
    (g : catMorph cat b c) ->
    (f : catMorph cat a b) ->
    catComp cat {a} {b=c} {c=d} h (catComp cat {a} {b} {c} g f) =
      catComp cat {a} {b} {c=d} (catComp cat {a=b} {b=c} {c=d} h g) f

public export
CorrectCatSig : Type
CorrectCatSig = DPair CatSig CatSigCorrect

public export
CatToPolyPos : CatSig -> Type
CatToPolyPos (MkCatSig o m i comp) = o

public export
CatToPolyDir : (c : CatSig) -> CatToPolyPos c -> Type
CatToPolyDir (MkCatSig o m i comp) a = (b : o ** m a b)

public export
CatToPoly : CatSig -> PolyFunc
CatToPoly c = (CatToPolyPos c ** CatToPolyDir c)

public export
CatToComonoidErase : (c : CatSig) -> PolyNatTrans (CatToPoly c) PFIdentityArena
CatToComonoidErase (MkCatSig o m i comp) = (const () ** \a, _ => (a ** i a))

public export
CatToComonoidDup : (c : CatSig) ->
  PolyNatTrans (CatToPoly c) (pfDuplicateArena (CatToPoly c))
CatToComonoidDup (MkCatSig o m i comp) =
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
ComonoidToCatComp : {p : PolyFunc} ->
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
ComonoidToCat : {p : PolyFunc} ->
  (c : PFComonoid p) -> PFComonoidCorrect p c -> CatSig
ComonoidToCat c holds =
  MkCatSig
    (ComonoidToCatObj c)
    (ComonoidToCatMorph c holds)
    (ComonoidToCatId c holds)
    (ComonoidToCatComp c holds)

public export
ComonadToCat : (com : PFComonad) ->
  PFComonoidCorrect (fst com) (snd com) -> CatSig
ComonadToCat (p ** c) holds = ComonoidToCat {p} c holds

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
PFReaderJoinOnDir env (() ** i) d with (i d) proof ideq
  PFReaderJoinOnDir env (() ** i) d | () = (d ** rewrite ideq in d)

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

---------------------------------------
---------------------------------------
---- Dependent polynomial functors ----
---------------------------------------
---------------------------------------

--------------------------------------------------------------------
---- Dependent polynomials as functors between slice categories ----
--------------------------------------------------------------------

public export
SliceIdx : PolyFunc -> Type -> Type -> Type
SliceIdx p a b = (i : pfPos p) -> (pfDir {p} i -> a) -> b

public export
SlicePolyFunc : Type -> Type -> Type
SlicePolyFunc a b = (p : PolyFunc ** SliceIdx p a b)

public export
spfFunc : {0 a, b : Type} -> SlicePolyFunc a b -> PolyFunc
spfFunc = DPair.fst

public export
spfPos : {0 a, b : Type} -> SlicePolyFunc a b -> Type
spfPos = pfPos . spfFunc

public export
spfDir : {0 a, b : Type} -> {spf : SlicePolyFunc a b} -> spfPos spf -> Type
spfDir {spf} = pfDir {p=(spfFunc spf)}

public export
spfIdx : {0 a, b : Type} ->
  {spf : SlicePolyFunc a b} -> SliceIdx (spfFunc spf) a b
spfIdx {spf} = DPair.snd spf

public export
InterpSPFunc : {a, b : Type} -> SlicePolyFunc a b -> SliceFunctor a b
InterpSPFunc {a} {b} ((pos ** dir) ** idx) sa eb =
  (i : pos **
   param : dir i -> a **
   (FunExt -> idx i param = eb,
    (d : dir i) -> sa $ param d))

public export
InterpSPFMap : {0 a, b : Type} -> (spf : SlicePolyFunc a b) ->
  {0 sa, sa' : SliceObj a} ->
  SliceMorphism sa sa' ->
  SliceMorphism (InterpSPFunc spf sa) (InterpSPFunc spf sa')
InterpSPFMap ((_ ** dir) ** _) m _ (i ** param ** (eqidx, da)) =
  (i ** param ** (eqidx, \d : dir i => m (param d) (da d)))

public export
SlicePolyEndoF : Type -> Type
SlicePolyEndoF a = SlicePolyFunc a a

-----------------------------------------------------------------------
---- Natural transformations on dependent polynomial endofunctors ----
-----------------------------------------------------------------------

public export
SPNatTransOnIdx : {x, y : Type} -> (p, q : SlicePolyFunc x y) ->
  PolyNatTrans (spfFunc p) (spfFunc q) -> Type
SPNatTransOnIdx {x} p q pnt =
  (pi : spfPos p) -> (pparam : spfDir {spf=p} pi -> x) ->
  spfIdx {spf=q} (pntOnPos pnt pi) (pparam . pntOnDir pnt pi) =
  spfIdx {spf=p} pi pparam

public export
SPNatTrans : {x, y : Type} -> SlicePolyFunc x y -> SlicePolyFunc x y -> Type
SPNatTrans {x} p q =
  (pnt : PolyNatTrans (spfFunc p) (spfFunc q) ** SPNatTransOnIdx p q pnt)

public export
spntPnt : {0 x, y : Type} -> {0 p, q : SlicePolyFunc x y} ->
  SPNatTrans p q -> PolyNatTrans (spfFunc p) (spfFunc q)
spntPnt = DPair.fst

public export
spntOnPos : {0 x, y : Type} -> {0 p, q : SlicePolyFunc x y} -> SPNatTrans p q ->
  spfPos p -> spfPos q
spntOnPos = pntOnPos . spntPnt

public export
spntOnDir : {0 x, y : Type} -> {0 p, q : SlicePolyFunc x y} ->
  (alpha : SPNatTrans p q) ->
  SliceMorphism (spfDir {spf=q} . spntOnPos {p} {q} alpha) (spfDir {spf=p})
spntOnDir alpha i = pntOnDir (spntPnt alpha) i

public export
spntOnIdx : {0 x, y : Type} -> {0 p, q : SlicePolyFunc x y} ->
  (alpha : SPNatTrans p q) -> SPNatTransOnIdx p q (spntPnt {p} {q} alpha)
spntOnIdx = DPair.snd

public export
InterpSPNT : {0 x, y : Type} -> {p, q : SlicePolyFunc x y} ->
  SPNatTrans p q -> {0 sx : SliceObj x} ->
  SliceMorphism {a=y} (InterpSPFunc p sx) (InterpSPFunc q sx)
InterpSPNT {x} {y} {p=((ppos ** pdir) ** pidx)} {q=((qpos ** qdir) ** qidx)}
  ((onPos ** onDir) ** onIdx) {sx} ey (pi ** pparam ** (extEq, pda)) =
    (onPos pi **
     pparam . onDir pi **
     (\funext => trans (onIdx pi pparam) (extEq funext),
      \qd : qdir (onPos pi) => pda $ onDir pi qd))

-----------------------------------------------
-----------------------------------------------
---- Dependent-polynomial-functors algebra ----
-----------------------------------------------
-----------------------------------------------

---------------------------------------------------
---- Algebras of dependent polynomial functors ----
---------------------------------------------------

public export
SPFAlg : {a : Type} -> SlicePolyEndoF a -> SliceObj a -> Type
SPFAlg spf sa = SliceMorphism (InterpSPFunc spf sa) sa

---------------------------------------------------
---- Initial algebras of dependent polynomials ----
---------------------------------------------------

public export
spfMu : {0 a : Type} -> SlicePolyEndoF a -> Type
spfMu = PolyFuncMu . spfFunc

public export
spfMuIdx : {0 a : Type} -> (spf : SlicePolyEndoF a) -> spfMu spf -> a
spfMuIdx (p@(pos ** dir) ** sli) = pfCata {p} sli

public export
SPFMu : {0 a : Type} -> SlicePolyEndoF a -> SliceObj a
SPFMu {a} spf@(p ** sli) ea =
  (em : PolyFuncMu p ** FunExt -> spfMuIdx spf em = ea)

public export
InSPFM : {0 a : Type} -> {spf : SlicePolyEndoF a} ->
  (i : spfPos spf) ->
  (param : spfDir {spf} i -> a) ->
  ((di : spfDir {spf} i) -> SPFMu {a} spf (param di)) ->
  SPFMu {a} spf (spfIdx {spf} i param)
InSPFM {a} {spf=spf@((pos ** dir) ** slidx)} i param sli =
  (InPFM i (\di => fst (sli di)) **
   (\funext => cong (slidx i) $ funExt $ \di => snd (sli di) funext))

--------------------------------------------------------
---- Catamorphisms of dependent polynomial functors ----
--------------------------------------------------------

public export
spfCataCurried : {0 a : Type} -> {spf : SlicePolyEndoF a} ->
  {0 sa : SliceObj a} -> {funext : FunExt} -> SPFAlg spf sa ->
  (ea : a) ->
  (em : PolyFuncMu (spfFunc spf)) ->
  (FunExt -> spfMuIdx {a} spf em = ea) ->
  sa ea
spfCataCurried
  {spf=((pos ** dir) ** idx)} {funext} alg ea (InPFM i param) slieq =
    case slieq funext of
      Refl =>
        alg
          ea
          (i **
          pfCata {p=(pos ** dir)} idx . param **
          (slieq,
            \di : dir i =>
              spfCataCurried {spf=((pos ** dir) ** idx)} {funext} alg
                (pfCata idx (param di)) (param di) (\_ => Refl)))

public export
spfCata : {0 a : Type} -> {spf : SlicePolyEndoF a} -> {0 sa : SliceObj a} ->
  {funext : FunExt} -> SPFAlg spf sa -> (ea : a) -> SPFMu spf ea -> sa ea
spfCata {a} {spf=spf@((_ ** _) ** _)} {sa} {funext} alg ea (em ** slieq) =
  spfCataCurried {a} {spf} {funext} alg ea em slieq

--------------------------------------------
---- Dependent polynomial (free) monads ----
--------------------------------------------

public export
SPFTranslatePos : {0 x, y : Type} -> SlicePolyFunc x y -> Type -> Type
SPFTranslatePos = PFTranslatePos . spfFunc

public export
SPFTranslateDir : {x, y : Type} -> (spf : SlicePolyFunc x y) -> (a : Type) ->
  SPFTranslatePos spf a -> Type
SPFTranslateDir spf a = PFTranslateDir (spfFunc spf) a

public export
SPFTranslateFunc : {x, y : Type} -> (spf : SlicePolyFunc x y) -> (a : Type) ->
  PolyFunc
SPFTranslateFunc spf a = (SPFTranslatePos spf a ** SPFTranslateDir spf a)

public export
SPFTranslateIdx : {0 x, y : Type} -> (spf : SlicePolyFunc x y) -> (a : Type) ->
  (a -> y) -> SliceIdx (SPFTranslateFunc spf a) x y
SPFTranslateIdx ((pos ** dir) ** idx) a f (PFVar v) di = f v
SPFTranslateIdx ((pos ** dir) ** idx) a f (PFCom i) di = idx i di

public export
SPFTranslate : {x, y : Type} -> SlicePolyFunc x y -> (a : Type) ->
  (a -> y) -> SlicePolyFunc x y
SPFTranslate spf a f = (SPFTranslateFunc spf a ** SPFTranslateIdx spf a f)

public export
SPFFreeMFromMu : {x : Type} -> SlicePolyEndoF x -> SliceObj x -> SliceObj x
SPFFreeMFromMu spf sx =
  SPFMu {a=x} (SPFTranslate {x} {y=x} spf (Sigma sx) DPair.fst)

-------------------------------------------------
-------------------------------------------------
---- Dependent-polynomial-functors coalgebra ----
-------------------------------------------------
-------------------------------------------------

-----------------------------------------------------
---- Coalgebras of dependent polynomial functors ----
-----------------------------------------------------

public export
SPFCoalg : {a : Type} -> SlicePolyEndoF a -> SliceObj a -> Type
SPFCoalg spf sa = SliceMorphism sa (InterpSPFunc spf sa)

------------------------------------------------------
---- Terminal coalgebras of dependent polynomials ----
------------------------------------------------------

public export
data SPFNu : {0 a : Type} -> SlicePolyEndoF a -> SliceObj a where
  InSPFN : {0 a : Type} -> {0 spf : SlicePolyEndoF a} ->
    (i : spfPos spf) ->
    (param : spfDir {spf} i -> a) ->
    ((di : spfDir {spf} i) -> Inf (SPFNu {a} spf (param di))) ->
    SPFNu {a} spf (spfIdx {spf} i param)

-------------------------------------------------------
---- Anamorphisms of dependent polynomial functors ----
-------------------------------------------------------

public export
spfAna : {0 a : Type} -> {spf : SlicePolyEndoF a} -> {0 sa : SliceObj a} ->
  {funext : FunExt} -> SPFCoalg spf sa -> (ea : a) -> sa ea -> SPFNu spf ea
spfAna {a} {spf=((pos ** dir) ** idx)} {sa} {funext} coalg ea esa =
  case coalg ea esa of
    (i ** param ** (extEq, da)) => case (extEq funext) of
      Refl =>
        InSPFN {spf=((pos ** dir) ** idx)} i param $
          \di : dir i => spfAna {funext} coalg (param di) (da di)

------------------------------------------------
---- Dependent polynomial (cofree) comonads ----
------------------------------------------------

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
  SPFNu {a=x} (SPFScale {x} {y=x} spf (Sigma sx) (const id))

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
data FinTFNewTermAlg : FinTFNewIndAlg (\_, _ => Type) where
  FTTUnit :
    {0 hyp : FinTFDepth Z -> Type} ->
    FinTFNewTermAlg Z hyp FTFNTerminal
  FTTLeft :
    {0 m, n : Nat} -> {0 hyp : FinTFDepth (maximum m n) -> Type} ->
    {0 x : FinTFNew m} -> {0 y : FinTFNew n} ->
    hyp (FinPromoteLeft {n} x) ->
    FinTFNewTermAlg (maximum m n) hyp (FTFNCoproduct x y)
  FTTRight :
    {0 m, n : Nat} -> {0 hyp : FinTFDepth (maximum m n) -> Type} ->
    {0 x : FinTFNew m} -> {0 y : FinTFNew n} ->
    hyp (FinPromoteRight {m} y) ->
    FinTFNewTermAlg (maximum m n) hyp (FTFNCoproduct x y)
  FTTPair :
    {0 m, n : Nat} -> {0 hyp : FinTFDepth (maximum m n) -> Type} ->
    {0 x : FinTFNew m} -> {0 y : FinTFNew n} ->
    hyp (FinPromoteLeft {n} x) ->
    hyp (FinPromoteRight {m} y) ->
    FinTFNewTermAlg (maximum m n) hyp (FTFNProduct x y)

public export
FinTFNewTerm : {funext : FunExt} -> (n : Nat) -> FinTFNew n -> Type
FinTFNewTerm {funext} = finTFNewInd {funext} FinTFNewTermAlg

-- Generate the exponential object of a pair of finite unrefined objects.
public export
FinExpObjF : (n : Nat) ->
  (FinTFDepth n -> MuFinTF -> MuFinTF) -> FinTFNew (S n) -> MuFinTF -> MuFinTF
FinExpObjF n morph type cod = ?FinExpObjF_hole

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
FinNewMorphF n morph type cod = ?FinNewMorphF_hole

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
isubstOEval : (x, y : MuISubstO) ->
  isubstOMorphism (ISOProduct (isubstOHomObj x y) x) y
isubstOEval x y = ?isubstOEval_hole

public export
isubstOCurry : {x, y, z : MuISubstO} ->
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
s0ObjTermAlg : FreeS0SliceAlg
s0ObjTermAlg = MkS0ObjAlg Void Unit Either Pair

public export
s0ObjTerm : {0 v : Type} -> (v -> Type) -> FreeS0Slice v
s0ObjTerm = s0slice s0ObjTermAlg

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
scalePreservesValid : {0 pt : PolyTerm} -> {0 poly : PolyShape} ->
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
parProdMonPreservesValid : {0 pt : PolyTerm} -> {0 poly : PolyShape} ->
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
addPreservesValid : {0 p, q : PolyShape} ->
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
mulPreservesValid : {0 p, q : PolyShape} ->
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
parProdPreservesValid : {0 p, q : PolyShape} ->
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
expNPreservesValid : {0 n : Nat} -> {0 poly : PolyShape} ->
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
composePreservesValid : {0 p, q : PolyShape} ->
  ValidPoly q -> ValidPoly p -> ValidPoly (composePolyShape q p)
composePreservesValid {p} {q} pvalid qvalid = ?composePolyShapeCorrect_hole

public export
composePoly : Polynomial -> Polynomial -> Polynomial
composePoly (Element0 q qvalid) (Element0 p pvalid) =
  Element0 (composePolyShape q p) (composePreservesValid qvalid pvalid)

infixr 1 <|
public export
(<|) : Polynomial -> Polynomial -> Polynomial
(<|) = composePoly

infixr 1 |>
public export
(|>) : Polynomial -> Polynomial -> Polynomial
(|>) = flip (<|)

public export
iterNPolyShape : Nat -> PolyShape -> PolyShape
iterNPolyShape n p = foldrNat (composePolyShape p) terminalPolyShape n

public export
iterNPreservesValid : {0 n : Nat} -> {0 poly : PolyShape} ->
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
idPSCorrect : (0 range : NatRange) ->
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
BoundedNat n = Refinement {a=Nat} ((>=) n)

public export
MkBoundedNat : {0 n : Nat} ->
  (m : Nat) -> {auto 0 gte : gteTrue n m} -> BoundedNat n
MkBoundedNat m {gte} = MkRefinement m {satisfies=gte}

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
validPNTS : Polynomial -> Polynomial -> DecPred PolyNTShape
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
pntsComponent : PolyShape -> PolyShape -> PolyNTShape -> AugNatRange -> AugRNM
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

infixr 8 !!+
infixr 9 !!*

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

public export
Functor SubstObjF where
  map m SO0 = SO0
  map m SO1 = SO1
  map m (x !!+ y) = m x !!+ m y
  map m (x !!* y) = m x !!* m y

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

infixr 8 !+
infixr 9 !*

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

public export
substObjSize : SubstObjMu -> Nat
substObjSize = substObjCata SOSizeAlg

public export
SODepthAlg : MetaSOAlg Nat
SODepthAlg SO0 = 0
SODepthAlg SO1 = 0
SODepthAlg (p !!+ q) = smax p q
SODepthAlg (p !!* q) = smax p q

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
substObjMuDecEq (InSO SO1) (InSO SO0) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO SO1) (InSO SO1) = Yes Refl
substObjMuDecEq (InSO SO1) (InSO (_ !!+ _)) =
  No $ \eq => case eq of Refl impossible
substObjMuDecEq (InSO SO1) (InSO (_ !!* _)) =
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

public export
substObjRemoveOne : SubstObjMu -> SubstObjMu
substObjRemoveOne = substObjCata SORemoveOneAlg

public export
substObjNormalize : SubstObjMu -> SubstObjMu
substObjNormalize = substObjRemoveOne . substObjRemoveZero

-----------------------------------------------------
---- Multiplication by a constant (via addition) ----
-----------------------------------------------------

infix 10 !:*
public export
(!:*) : Nat -> SubstObjMu -> SubstObjMu
n !:* p = foldrNatNoUnit ((!+) p) Subst0 p n

---------------------------------------
---- Multiplicative exponentiation ----
---------------------------------------

infix 10 !*^
public export
(!*^) : SubstObjMu -> Nat -> SubstObjMu
p !*^ n = foldrNatNoUnit ((!*) p) Subst1 p n

----------------------------------------
---- Terms of substitutive category ----
----------------------------------------

public export
SubstTermAlg : MetaSOAlg Type
SubstTermAlg SO0 = Void
SubstTermAlg SO1 = ()
SubstTermAlg (x !!+ y) = Either x y
SubstTermAlg (x !!* y) = Pair x y

public export
SubstTerm : SubstObjMu -> Type
SubstTerm = substObjCata SubstTermAlg

public export
SubstContradictionAlg : MetaSOAlg Type
SubstContradictionAlg SO0 = ()
SubstContradictionAlg SO1 = Void
SubstContradictionAlg (x !!+ y) = Pair x y
SubstContradictionAlg (x !!* y) = Either x y

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
SubstHomObjAlg : MetaSOAlg (SubstObjMu -> SubstObjMu)
-- 0 -> x == 1
SubstHomObjAlg SO0 _ = Subst1
-- 1 -> x == x
SubstHomObjAlg SO1 q = q
-- (p + q) -> r == (p -> r) * (q -> r)
SubstHomObjAlg (p !!+ q) r = p r !* q r
-- (p * q) -> r == p -> q -> r
SubstHomObjAlg (p !!* q) r = p $ q r

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

infixr 1 <!
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

infixr 10 !->
public export
(!->) : SubstObjMu -> SubstObjMu -> SubstObjMu
(!->) = SubstHomObj

infix 10 !^
public export
(!^) : SubstObjMu -> SubstObjMu -> SubstObjMu
(!^) = flip SubstHomObj

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
soConst : {x, y : SubstObjMu} -> SOTerm y -> SubstMorph x y
soConst {x} {y} f = f <! SMToTerminal _

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
SubstBool : SubstObjMu
SubstBool = Subst1 !+ Subst1

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
  soEval x y <! SMPair (SMCase (MorphAsTerm t) (MorphAsTerm f) <! b) (SMId x)

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

public export
MetaSOType : SubstObjMu -> Type
MetaSOType = substObjCata MetaSOTypeAlg

public export
MetaSOShowTypeAlg : MetaSOAlg String
MetaSOShowTypeAlg SO0 = "Void"
MetaSOShowTypeAlg SO1 = "Unit"
MetaSOShowTypeAlg (p !!+ q) = "Either (" ++ p ++ ") (" ++ q ++ ")"
MetaSOShowTypeAlg (p !!* q) = "Pair (" ++ p ++ ") (" ++ q ++ ")"

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
SubstMorphADTPFAlgCheckSig : SubstMorphADTPFAlg (Maybe SubstMorphADTSig)
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
substMorphADTCata : SubstMorphADTAlg x -> SubstMorphADT -> Maybe x
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
smadtCheckSig : SubstMorphADT -> Maybe (SubstObjMu, SubstObjMu)
smadtCheckSig = substMorphADTCata SMADTCheckSigAlg

-------------------------------------------------------------
-------------------------------------------------------------
---- Natural numbers as objects representing finite sets ----
-------------------------------------------------------------
-------------------------------------------------------------

-- Define and translate two ways of interpreting natural numbers.

---------------------------------------
---- Bounded unary natural numbers ----
---------------------------------------

-- First, as coproducts of Unit.  As such, they are the first non-trivial
-- objects that can be formed in a category which is inductively defined as
-- the smallest one containing only (all) finite coproducts and finite products.
-- In this form, they are unary natural numbers, often suited as indexes.

public export
BUNat : Nat -> Type
BUNat Z = Void
BUNat (S n) = Either Unit (BUNat n)

public export
BUNatDepAlg :
  {0 p : (n : Nat) -> BUNat n -> Type} ->
  ((n : Nat) -> p (S n) (Left ())) ->
  ((n : Nat) ->
   ((bu : BUNat n) -> p n bu) ->
   (bu : BUNat n) -> p (S n) (Right bu)) ->
  NatDepAlgebra (\n => (bu : BUNat n) -> p n bu)
BUNatDepAlg {p} z s =
  (\bu => void bu,
   \n, hyp, bu => case bu of
    Left () => z n
    Right bu' => s n hyp bu')

public export
buNatDepCata :
  {0 p : (n : Nat) -> BUNat n -> Type} ->
  ((n : Nat) -> p (S n) (Left ())) ->
  ((n : Nat) ->
   ((bu : BUNat n) -> p n bu) ->
   (bu : BUNat n) -> p (S n) (Right bu)) ->
  (n : Nat) -> (bu : BUNat n) -> p n bu
buNatDepCata {p} z s = natDepCata (BUNatDepAlg {p} z s)

--------------------------------------------
---- Bounded arithmetic natural numbers ----
--------------------------------------------

-- Second, as bounds, which allow us to do bounded arithmetic,
-- or arithmetic modulo a given number.

public export
BoundedBy : Nat -> DecPred Nat
BoundedBy = gt

public export
NotBoundedBy : Nat -> DecPred Nat
NotBoundedBy = not .* BoundedBy

public export
IsBoundedBy : Nat -> Nat -> Type
IsBoundedBy = Satisfies . BoundedBy

public export
BANat : (0 _ : Nat) -> Type
BANat n = Refinement {a=Nat} (BoundedBy n)

public export
MkBANat : {0 n : Nat} -> (m : Nat) -> {auto 0 satisfies : IsBoundedBy n m} ->
  BANat n
MkBANat = MkRefinement

public export
baS : {0 n : Nat} -> BANat n -> BANat (S n)
baS (Element0 m lt) = Element0 (S m) lt

public export
baShowLong : {n : Nat} -> BANat n -> String
baShowLong {n} m = show m ++ "[<" ++ show n ++ "]"

public export
baNatDepCata :
  {0 p : (n : Nat) -> BANat n -> Type} ->
  ((n : Nat) -> p (S n) (Element0 0 Refl)) ->
  ((n : Nat) ->
   ((ba : BANat n) -> p n ba) ->
   (ba : BANat n) -> p (S n) (baS {n} ba)) ->
  (n : Nat) -> (ba : BANat n) -> p n ba
baNatDepCata {p} z s =
  natDepCata {p=(\n' => (ba' : BANat n') -> p n' ba')}
    (\ba => case ba of Element0 ba' Refl impossible,
     \n, hyp, ba => case ba of
      Element0 Z lt => rewrite uip {eq=lt} {eq'=Refl} in z n
      Element0 (S ba') lt => s n hyp (Element0 ba' lt))

-------------------------------------------------------------------
---- Translation between unary and arithmetic bounded naturals ----
-------------------------------------------------------------------

public export
u2a : {n : Nat} -> BUNat n -> BANat n
u2a {n=Z} v = void v
u2a {n=(S n)} (Left ()) = Element0 0 Refl
u2a {n=(S n)} (Right bu) with (u2a bu)
  u2a {n=(S n)} (Right bu) | Element0 bu' lt = Element0 (S bu') lt

public export
a2u : {n : Nat} -> BANat n -> BUNat n
a2u {n=Z} (Element0 ba Refl) impossible
a2u {n=(S n)} (Element0 Z lt) = Left ()
a2u {n=(S n)} (Element0 (S ba) lt) = Right $ a2u $ Element0 ba lt

public export
u2a2u_correct : {n : Nat} -> {bu : BUNat n} -> bu = a2u {n} (u2a {n} bu)
u2a2u_correct {n=Z} {bu} = void bu
u2a2u_correct {n=(S n)} {bu=(Left ())} = Refl
u2a2u_correct {n=(S n)} {bu=(Right bu)} with (u2a bu) proof eq
  u2a2u_correct {n=(S n)} {bu=(Right bu)} | Element0 m lt =
    rewrite (sym eq) in cong Right $ u2a2u_correct {n} {bu}

public export
a2u2a_fst_correct : {n : Nat} -> {ba : BANat n} ->
  fst0 ba = fst0 (u2a {n} (a2u {n} ba))
a2u2a_fst_correct {n=Z} {ba=(Element0 ba Refl)} impossible
a2u2a_fst_correct {n=(S n)} {ba=(Element0 Z lt)} = Refl
a2u2a_fst_correct {n=(S n)} {ba=(Element0 (S ba) lt)}
  with (u2a (a2u (Element0 ba lt))) proof p
    a2u2a_fst_correct {n=(S n)} {ba=(Element0 (S ba) lt)} | Element0 ba' lt' =
      cong S $ trans (a2u2a_fst_correct {ba=(Element0 ba lt)}) $ cong fst0 p

public export
a2u2a_correct : {n : Nat} -> {ba : BANat n} -> ba = u2a {n} (a2u {n} ba)
a2u2a_correct {n} {ba} = refinementFstEq $ a2u2a_fst_correct {n} {ba}

public export
MkBUNat : {n : Nat} -> (m : Nat) -> {auto 0 satisfies : IsBoundedBy n m} ->
  BUNat n
MkBUNat m {satisfies} = a2u (MkBANat m {satisfies})

public export
up2a : {n : Nat} -> (BUNat n -> Type) -> BANat n -> Type
up2a p ba = p (a2u ba)

public export
ap2u : {n : Nat} -> (BANat n -> Type) -> BUNat n -> Type
ap2u p bu = p (u2a bu)

public export
up2a_rewrite : {0 n : Nat} -> {0 p : BUNat n -> Type} ->
  {0 bu : BUNat n} -> p bu -> up2a {n} p (u2a {n} bu)
up2a_rewrite {p} t = replace {p} u2a2u_correct t

public export
ap2u_rewrite : {0 n : Nat} -> {0 p : BANat n -> Type} ->
  {0 ba : BANat n} -> p ba -> ap2u {n} p (a2u {n} ba)
ap2u_rewrite {p} t = replace {p} a2u2a_correct t

----------------------------------------
---- Bounded-natural-number objects ----
----------------------------------------

-- The bounded natural numbers can be interpreted as a category whose
-- objects are simply natural numbers (which give the bounds) and whose
-- morphisms are the polynomial circuit operations modulo the bounds.
-- An object is therefore specified simply by a natural number, and
-- interpreted as a Nat-bounded set.

public export
BNCatObj : Type
BNCatObj = Nat

-- We can interpret objects of the natural-number-bounded category as
-- bounded unary representations of Nat.
public export
bncInterpU : BNCatObj -> Type
bncInterpU = BUNat

-- We can also interpreted a `BNCatObj` as an arithmetic Nat-bounded set.
-- bounded unary representations of Nat.
public export
bncObjA : (0 _ : BNCatObj) -> Type
bncObjA = BANat

-- The simplest morphisms of the Nat-bounded-set category are specified
-- by spelling out, for each term of the domain, which term of the codomain
-- it maps to.
public export
BNCListMorph : Type
BNCListMorph = List Nat

-- For a given BNCListMorph, we can check whether it is a valid morphism
-- between a given pair of objects.
public export
checkVBNCLM : BNCatObj -> BNCatObj -> DecPred BNCListMorph
checkVBNCLM Z _ [] = True
checkVBNCLM Z _ (_ :: _) = False
checkVBNCLM (S _) _ [] = False
checkVBNCLM (S m') n (k :: ks) = BoundedBy n k && checkVBNCLM m' n ks

public export
isVBNCLM : BNCatObj -> BNCatObj -> BNCListMorph -> Type
isVBNCLM = Satisfies .* checkVBNCLM

-- Given a pair of objects, we can define a type dependent on those
-- objects representing just those BNCListMorphs which are valid
-- morphisms between those particular objects.

public export
VBNCLM : BNCatObj -> BNCatObj -> Type
VBNCLM m n = Refinement {a=BNCListMorph} $ checkVBNCLM m n

public export
MkVBNCLM : {0 m, n : BNCatObj} -> (l : BNCListMorph) ->
  {auto 0 satisfies : isVBNCLM m n l} -> VBNCLM m n
MkVBNCLM l {satisfies} = MkRefinement l {satisfies}

-- We can interpret a valid list-specified morphism as a function
-- of the metalanguage.
public export
bncLMA : {m, n : BNCatObj} -> VBNCLM m n -> BANat m -> BANat n
bncLMA {m=Z} {n} (Element0 [] kvalid) (Element0 p pvalid) = exfalsoFT pvalid
bncLMA {m=(S _)} {n} (Element0 [] kvalid) vp = exfalsoFT kvalid
bncLMA {m=(S m)} {n} (Element0 (k :: ks) kvalid) (Element0 Z pvalid) =
  Element0 k (andLeft kvalid)
bncLMA {m=(S m)} {n} (Element0 (k :: ks) kvalid) (Element0 (S p) pvalid) =
  bncLMA {m} {n} (Element0 ks (andRight kvalid)) (Element0 p pvalid)

-- Utility function for applying a bncLMA to a Nat that can be
-- validated at compile time as satisfying the bounds.
public export
bncLMAN : {m, n : BNCatObj} -> VBNCLM m n -> (k : Nat) ->
  {auto 0 satisfies : IsBoundedBy m k} -> BANat n
bncLMAN lm k {satisfies} = bncLMA lm $ MkBANat k {satisfies}

-- Utility function for applying bncLMAN and then forgetting the
-- constraint on the output.
public export
bncLMANN : {m, n : BNCatObj} -> VBNCLM m n -> (k : Nat) ->
  {auto 0 satisfies : IsBoundedBy m k} -> Nat
bncLMANN l k {satisfies} = fst0 $ bncLMAN l k {satisfies}

-- Another class of morphism in the category of bounded arithmetic
-- natural numbers is the polynomial functions -- constants, addition,
-- multiplication.  Because we are so far defining only a "single-variable"
-- category, we can make all such morphisms valid (as opposed to invalid if
-- they fail bound checks) by performing the arithmetic modulo the sizes
-- of the domain and codomain.

-- Thus we can in particular interpret any metalanguage function on the
-- natural numbers as a function from any BANat object to any non-empty
-- BANat object by post-composing with modulus.

public export
metaToNatToBNC : {n : Nat} -> (Integer -> Integer) -> Nat -> BANat (S n)
metaToNatToBNC {n} f k =
  let
    k' = natToInteger k
    fk = integerToNat $ f k'
  in
  Element0 (modNatNZ fk (S n) SIsNonZero) (modLtDivisor fk n)

public export
metaToBNCToBNC : {m, n : Nat} -> (Integer -> Integer) -> BANat m -> BANat (S n)
metaToBNCToBNC f (Element0 k _) = metaToNatToBNC {n} f k

-- Object-language representation of polynomial morphisms.

prefix 11 #|
infixr 8 #+
infix 8 #-
infixr 9 #*
infix 9 #/
infix 9 #%
infixr 2 #.

public export
data BNCPolyM : Type where
  -- Polynomial operations --

  -- Constant
  (#|) : Nat -> BNCPolyM

  -- Identity
  PI : BNCPolyM

  -- Compose
  (#.) : BNCPolyM -> BNCPolyM -> BNCPolyM

  -- Add
  (#+) : BNCPolyM -> BNCPolyM -> BNCPolyM

  -- Multiply
  (#*) : BNCPolyM -> BNCPolyM -> BNCPolyM

  -- Inverse operations --

  -- Subtract
  (#-) : BNCPolyM -> BNCPolyM -> BNCPolyM

  -- Divide (division by zero returns zero)
  (#/) : BNCPolyM -> BNCPolyM -> BNCPolyM

  -- Modulus (modulus by zero returns zero)
  (#%) : BNCPolyM -> BNCPolyM -> BNCPolyM

  -- Branch operation(s)

  -- Compare with zero: equal takes first branch; not-equal takes second branch
  IfZero : BNCPolyM -> BNCPolyM -> BNCPolyM -> BNCPolyM

  -- If the first argument is strictly less than the second, then
  -- take the first branch (which is the third argument); otherwise,
  -- take the second branch (which is the fourth argument)
  IfLT : BNCPolyM -> BNCPolyM -> BNCPolyM -> BNCPolyM -> BNCPolyM

public export
record BNCPolyMAlg (0 a : BNCPolyM -> Type) where
  constructor MkBNCPolyAlg
  bncaConst : (n : Nat) -> a (#| n)
  bncaId : a PI
  bncaCompose : (q, p : BNCPolyM) -> a q -> a p -> a (q #. p)
  bncaAdd : (p, q : BNCPolyM) -> a p -> a q -> a (p #+ q)
  bncaMul : (p, q : BNCPolyM) -> a p -> a q -> a (p #* q)
  bncaSub : (p, q : BNCPolyM) -> a p -> a q -> a (p #- q)
  bncaDiv : (p, q : BNCPolyM) -> a p -> a q -> a (p #/ q)
  bncaMod : (p, q : BNCPolyM) -> a p -> a q -> a (p #% q)
  bncaIfZ : (p, q, r : BNCPolyM) -> a p -> a q -> a r -> a (IfZero p q r)
  bncaIfLT :
     (p, q, r, s : BNCPolyM) -> a p -> a q -> a r -> a s -> a (IfLT p q r s)

public export
bncPolyMInd : {0 a : BNCPolyM -> Type} -> BNCPolyMAlg a -> (p : BNCPolyM) -> a p
bncPolyMInd alg (#| k) = bncaConst alg k
bncPolyMInd alg PI = bncaId alg
bncPolyMInd alg (q #. p) =
  bncaCompose alg q p (bncPolyMInd alg q) (bncPolyMInd alg p)
bncPolyMInd alg (p #+ q) =
  bncaAdd alg p q (bncPolyMInd alg p) (bncPolyMInd alg q)
bncPolyMInd alg (p #* q) =
  bncaMul alg p q (bncPolyMInd alg p) (bncPolyMInd alg q)
bncPolyMInd alg (p #- q) =
  bncaSub alg p q (bncPolyMInd alg p) (bncPolyMInd alg q)
bncPolyMInd alg (p #/ q) =
  bncaDiv alg p q (bncPolyMInd alg p) (bncPolyMInd alg q)
bncPolyMInd alg (p #% q) =
  bncaMod alg p q (bncPolyMInd alg p) (bncPolyMInd alg q)
bncPolyMInd alg (IfZero p q r) =
  bncaIfZ alg p q r (bncPolyMInd alg p) (bncPolyMInd alg q) (bncPolyMInd alg r)
bncPolyMInd alg (IfLT p q r s) =
  bncaIfLT alg p q r s
    (bncPolyMInd alg p) (bncPolyMInd alg q)
    (bncPolyMInd alg r) (bncPolyMInd alg s)

public export
showInfix : (is, ls, rs : String) -> String
showInfix is ls rs = "(" ++ ls ++ ") " ++ is ++ " (" ++ rs ++ ")"

public export
const2ShowInfix : {0 a, b : Type} ->
  (is : String) -> a -> b -> (ls, rs : String) -> String
const2ShowInfix is _ _ = showInfix is

public export
BNCPMshowAlg : BNCPolyMAlg (const String)
BNCPMshowAlg = MkBNCPolyAlg
  show
  "PI"
  (const2ShowInfix ".")
  (const2ShowInfix "+")
  (const2ShowInfix "*")
  (const2ShowInfix "-")
  (const2ShowInfix "/")
  (const2ShowInfix "%")
  (\_, _, _, ps, qs, rs =>
    "(" ++ ps ++ " == 0 ? " ++ qs ++ " : " ++ rs ++ ")")
  (\_, _, _, _, ps, qs, rs, ss =>
    "(" ++ ps ++ " < " ++ qs ++ " ? " ++ rs ++ " : " ++ ss ++ ")")

public export
Show BNCPolyM where
  show  = bncPolyMInd BNCPMshowAlg

public export
P0 : BNCPolyM
P0 = #| 0

public export
P1 : BNCPolyM
P1 = #| 1

public export
powerAcc : BNCPolyM -> Nat -> BNCPolyM -> BNCPolyM
powerAcc p Z acc = acc
powerAcc p (S n) acc = powerAcc p n (p #* acc)

infixl 10 #^
public export
(#^) : BNCPolyM -> Nat -> BNCPolyM
(#^) p n = powerAcc p n P1

-- Interpret a BNCPolyM into the metalanguage.
public export
MetaBNCPolyMAlg : BNCPolyMAlg (\_ => Integer -> Integer)
MetaBNCPolyMAlg = MkBNCPolyAlg
  (\n, _ => natToInteger n)
  id
  (\q, p, qf, pf, k => qf (pf k))
  (\p, q, pf, qf, k => pf k + qf k)
  (\p, q, pf, qf, k => pf k * qf k)
  (\p, q, pf, qf, k => pf k - qf k)
  (\p, q, pf, qf, k => divWithZtoZ (pf k) (qf k))
  (\p, q, pf, qf, k => modWithZtoZ (pf k) (qf k))
  (\p, q, r, pf, qf, rf, k => if pf k == 0 then qf k else rf k)
  (\p, q, r, s, pf, qf, rf, sf, k => if pf k < qf k then rf k else sf k)

public export
metaBNCPolyM : (modpred : Integer) -> BNCPolyM -> Integer -> Integer
metaBNCPolyM modpred p n = modSucc (bncPolyMInd MetaBNCPolyMAlg p n) modpred

-- Interpret a BNCPolyM as a function between BANat objects.
public export
baPolyM : {m, n : Nat} -> BNCPolyM -> BANat m -> BANat (S n)
baPolyM {n} p = metaToBNCToBNC (metaBNCPolyM (natToInteger n) p)

----------------------------------------------------------------------
----------------------------------------------------------------------
---- Compilation of finite polynomial types to circuit operations ----
----------------------------------------------------------------------
----------------------------------------------------------------------

public export
substObjToNat : SubstObjMu -> Nat
substObjToNat = substObjCard

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
STLC_Context : Type
STLC_Context = List SubstObjMu

-- Indexed by the context and the type of the term within that context
-- to which the term compiles. (Thus, the type of the term abstracted over
-- the context is `ctx -> ty`.)
public export
data Checked_STLC_Term : STLC_Context -> SubstObjMu -> Type where
  -- The "void" or "absurd" function, which takes a term of type Void
  -- to any type; there's no explicit constructor for terms of type Void,
  -- but a lambda could introduce one.  The SubstObjMu is the type of the
  -- resulting term (since we can get any type from a term of Void).
  Checked_STLC_Absurd : {ctx : STLC_Context} -> {cod : SubstObjMu} ->
    Checked_STLC_Term ctx Subst0 -> Checked_STLC_Term ctx cod

  -- The only term of type Unit.
  Checked_STLC_Unit : {ctx : STLC_Context} ->
    Checked_STLC_Term ctx Subst1

  -- Construct coproducts.  In each case, the type of the injected term
  -- tells us the type of one side of the coproduct, so we provide a
  -- SubstObjMu to tell us the type of the other side.
  Checked_STLC_Left :
    {ctx : STLC_Context} -> {lty, rty : SubstObjMu} ->
      Checked_STLC_Term ctx lty -> Checked_STLC_Term ctx (lty !+ rty)
  Checked_STLC_Right :
    {ctx : STLC_Context} -> {lty, rty : SubstObjMu} ->
      Checked_STLC_Term ctx rty -> Checked_STLC_Term ctx (lty !+ rty)

  -- Case statement : parameters are expression to case on, which must be
  -- a coproduct, and then left and right case, which must be of the same
  -- type, which becomes the type of the overall term.  The cases receive
  -- the the result of the coproduct elimination in their contexts.
  Checked_STLC_Case :
    {ctx : STLC_Context} -> {lty, rty, cod : SubstObjMu} ->
    Checked_STLC_Term ctx (lty !+ rty) ->
    Checked_STLC_Term (lty :: ctx) cod -> Checked_STLC_Term (rty :: ctx) cod ->
    Checked_STLC_Term ctx cod

  -- Construct a term of a pair type
  Checked_STLC_Pair : {ctx : STLC_Context} -> {lty, rty : SubstObjMu} ->
    Checked_STLC_Term ctx lty -> Checked_STLC_Term ctx rty ->
    Checked_STLC_Term ctx (lty !* rty)

  -- Projections; in each case, the given term must be of a product type
  Checked_STLC_Fst : {ctx : STLC_Context} -> {lty, rty : SubstObjMu} ->
    Checked_STLC_Term ctx (lty !* rty) -> Checked_STLC_Term ctx lty
  Checked_STLC_Snd :
    Checked_STLC_Term ctx (lty !* rty) -> Checked_STLC_Term ctx rty

  -- Lambda abstraction:  introduce into the context a (de Bruijn-indexed)
  -- variable of the given type.
  Checked_STLC_Lambda :
    {ctx : STLC_Context} -> {vty, tty : SubstObjMu} ->
    Checked_STLC_Term (vty :: ctx) tty -> Checked_STLC_Term ctx (vty !-> tty)

  -- Function application
  Checked_STLC_App : {ctx : STLC_Context} -> {dom, cod : SubstObjMu} ->
    Checked_STLC_Term ctx (dom !-> cod) -> Checked_STLC_Term ctx dom ->
    Checked_STLC_Term ctx cod

  -- The variable at the given de Bruijn index
  Checked_STLC_Var :
    {ctx : STLC_Context} -> {i : Nat} -> {auto ok : InBounds i ctx} ->
    Checked_STLC_Term ctx (index i ctx {ok})

public export
stlcCtxToSOMu : STLC_Context -> SubstObjMu
stlcCtxToSOMu = foldr (!*) Subst1

public export
stlcCtxProj :
  (ctx : STLC_Context) -> (n : Nat) -> {auto 0 ok : InBounds n ctx} ->
  SubstMorph (stlcCtxToSOMu ctx) (index n ctx {ok})
stlcCtxProj (ty :: ctx) Z {ok=InFirst} =
  SMProjLeft ty (stlcCtxToSOMu ctx)
stlcCtxProj (ty :: ctx) Z {ok=InLater} impossible
stlcCtxProj (ty :: ctx) (S n) {ok=InFirst} impossible
stlcCtxProj (ty :: ctx) (S n) {ok=(InLater ok)} =
  stlcCtxProj ctx n {ok} <! SMProjRight ty (stlcCtxToSOMu ctx)

public export
SignedSubstMorph : Type
SignedSubstMorph =
  (sig : (SubstObjMu, SubstObjMu) ** SubstMorph (fst sig) (snd sig))

public export
SignedSubstCtxMorph : STLC_Context -> Type
SignedSubstCtxMorph ctx =
  (sig : (SubstObjMu, SubstObjMu) **
   SubstMorph (stlcCtxToSOMu ctx !* fst sig) (snd sig))

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

  -- Function application
  STLC_App : STLC_Term -> STLC_Term -> STLC_Term

  -- Lisp-style eval: interpret a term as a function and apply it.
  -- The type parameter is the output type.
  STLC_Eval : SubstObjMu -> STLC_Term -> STLC_Term -> STLC_Term

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
  show (STLC_App x y) = "app(" ++ show x ++ ", " ++ show y ++ ")"
  show (STLC_Eval ty f x) =
    "eval((" ++ show ty ++ ")" ++ show f ++ ", " ++ show x ++ ")"
  show (STLC_Var k) = "v" ++ show k

public export
stlcToCCC_ctx :
  (ctx : STLC_Context) ->
  STLC_Term ->
  Maybe (SignedSubstCtxMorph ctx)
stlcToCCC_ctx ctx (STLC_Absurd t ty) = do
  t' <- stlcToCCC_ctx ctx t
  case t' of
    ((dom, InSO SO0) ** m) => Just ((dom, ty) ** SMFromInit ty <! m)
    _ => Nothing
stlcToCCC_ctx ctx STLC_Unit =
  Just ((Subst1, Subst1) ** SMToTerminal $ stlcCtxToSOMu ctx !* Subst1)
stlcToCCC_ctx ctx (STLC_Left t ty) = do
  ((dom, cod) ** m) <- stlcToCCC_ctx ctx t
  Just ((dom, cod !+ ty) ** SMInjLeft cod ty <! m)
stlcToCCC_ctx ctx (STLC_Right ty t) = do
  ((dom, cod) ** m) <- stlcToCCC_ctx ctx t
  Just ((dom, ty !+ cod) ** SMInjRight ty cod <! m)
stlcToCCC_ctx ctx (STLC_Case x l r) = do
  let ctx' = stlcCtxToSOMu ctx
  ((xdom, xcod) ** xm) <- stlcToCCC_ctx ctx x
  ((ldom, lcod) ** lm) <- stlcToCCC_ctx ctx l
  ((rdom, rcod) ** rm) <- stlcToCCC_ctx ctx r
  case xcod of
    (InSO (xcodl !!+ xcodr)) => case
      (decEq xcodl ldom, decEq xcodr rdom, decEq lcod rcod) of
        (Yes Refl, Yes Refl, Yes Refl) =>
          Just
            ((xdom, lcod) **
             soUncurry
              (soUncurry soCaseAbstract
               <! SMPair (soCurry xm) (SMPair (soCurry lm) (soCurry rm))))
        _ => Nothing
    _ => Nothing
stlcToCCC_ctx ctx (STLC_Pair t1 t2) = do
  ((dom1, cod1) ** m1) <- stlcToCCC_ctx ctx t1
  ((dom2, cod2) ** m2) <- stlcToCCC_ctx ctx t2
  case decEq dom1 dom2 of
    Yes Refl => Just ((dom2, cod1 !* cod2) ** SMPair m1 m2)
    _ => Nothing
stlcToCCC_ctx ctx (STLC_Fst x) = do
  ((dom, cod) ** m) <- stlcToCCC_ctx ctx x
  case cod of
    InSO (codl !!* codr) => Just ((dom, codl) ** SMProjLeft codl codr <! m)
    _ => Nothing
stlcToCCC_ctx ctx (STLC_Snd x) = do
  ((dom, cod) ** m) <- stlcToCCC_ctx ctx x
  case cod of
    InSO (codl !!* codr) => Just ((dom, codr) ** SMProjRight codl codr <! m)
    _ => Nothing
stlcToCCC_ctx ctx (STLC_Lambda vty t) = case stlcToCCC_ctx (vty :: ctx) t of
  Just ((dom, cod) ** m) =>
    Just ((vty !* dom, cod) ** m <!
      SMPair
        (SMPair (SMProjLeft _ _ <! SMProjRight _ _) (SMProjLeft _ _))
        (SMProjRight _ _ <! SMProjRight _ _))
  Nothing => Nothing
stlcToCCC_ctx ctx (STLC_App f x) = do
  ((fdom, fcod) ** fm) <- stlcToCCC_ctx ctx f
  ((xdom, xcod) ** xm) <- stlcToCCC_ctx ctx x
  case decEq xcod fdom of
    Yes Refl =>
      Just ((xdom, fcod) ** soUncurry $ ctxCompose (soCurry fm) (soCurry xm))
    No _ => Nothing
stlcToCCC_ctx ctx (STLC_Eval ty f x) = do
  ((fdom, fcod) ** fm) <- stlcToCCC_ctx ctx f
  ((xdom, xcod) ** xm) <- stlcToCCC_ctx ctx x
  case (decEq fdom xdom, decEq fcod (xcod !-> ty)) of
    (Yes Refl, Yes eq) =>
      Just ((xdom, ty) ** soEval xcod ty <! SMPair (rewrite sym eq in fm) xm)
    (_, _) => Nothing
stlcToCCC_ctx ctx (STLC_Var v) = case inBounds v ctx of
  Yes ok => let proj = stlcCtxProj ctx v {ok} in
    Just ((stlcCtxToSOMu ctx, index v ctx {ok}) ** proj <! SMProjLeft _ _)
  No _ => Nothing

public export
stlcToCCC :
  STLC_Term ->
  Maybe SignedSubstMorph
stlcToCCC t with (stlcToCCC_ctx [] t)
  stlcToCCC t | Just ((dom, cod) ** m) = Just ((dom, cod) ** soProd1LeftElim m)
  stlcToCCC t | Nothing = Nothing

public export
stlcToCCC_valid :
  (t : STLC_Term) ->
  {auto isValid : IsJustTrue (stlcToCCC t)} ->
  SignedSubstMorph
stlcToCCC_valid t {isValid} = fromIsJust isValid

public export
Show SignedSubstMorph where
  show ((dom, cod) ** m) =
    "(" ++ show dom ++ " -> " ++ show cod ++ " : " ++ showSubstMorph m ++ ")"

public export
stlcToBNC :
  (t : STLC_Term) ->
  {auto isValid : IsJustTrue (stlcToCCC t)} ->
  SignedBNCMorph
stlcToBNC t {isValid} =
  let ((dom, cod) ** m) = stlcToCCC_valid t {isValid} in
  (substObjToNat dom, substObjToNat cod, substMorphToBNC m)

---------------------------------------------------
---------------------------------------------------
---- Older version of polynomial-type category ----
---------------------------------------------------
---------------------------------------------------

public export
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
  FinSubstT (finSubstHomObjCard x y) dh -> (0 df : Nat) -> Type
EvalMorphType x y hxy df = FinSubstMorph df (FinProduct hxy x) y

public export
HomObjWithEvalMorphType : {0 cx, dx, cy, dy : Nat} ->
  FinSubstT cx dx -> FinSubstT cy dy -> (0 dh : Nat) -> Type
HomObjWithEvalMorphType x y dh =
  (hxy : FinSubstT (finSubstHomObjCard x y) dh **
   Exists0 Nat (EvalMorphType x y hxy))

-- Compute the exponential object and evaluation morphism of the given finite
-- substitutive types.
public export
FinSubstHomDepthObjEval : {0 cx, dx, cy, dy : Nat} ->
  (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
  Exists0 Nat (HomObjWithEvalMorphType x y)
-- 0 -> x == 1
FinSubstHomDepthObjEval FinInitial x =
  (Evidence0 0 (FinTerminal **
    Evidence0 1 $
      FinCompose (FinFromInit x) $ FinProjRight FinTerminal FinInitial))
-- 1 -> x == x
FinSubstHomDepthObjEval {cy} {dy} FinTerminal x =
  let eq = mulPowerZeroRightNeutral {m=cy} {n=cy} in
  (Evidence0 dy $ rewrite eq in (x **
   Evidence0 0 $ rewrite eq in FinProjLeft x FinTerminal))
-- (x + y) -> z == (x -> z) * (y -> z)
FinSubstHomDepthObjEval {cx=(cx + cy)} {cy=cz} (FinCoproduct x y) z with
 (FinSubstHomDepthObjEval x z, FinSubstHomDepthObjEval y z)
  FinSubstHomDepthObjEval {cx=(cx + cy)} {cy=cz} (FinCoproduct x y) z |
   ((Evidence0 dxz (hxz ** (Evidence0 hdxz evalxz))),
    (Evidence0 dyz (hyz ** (Evidence0 hdyz evalyz)))) =
    (Evidence0 (smax dxz dyz) $ rewrite powerOfSum cz cx cy in
     (FinProduct hxz hyz ** Evidence0
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
      (FinProduct x y) z | (Evidence0 dyz (hyz ** Evidence0 hdyz evalyz)) =
        let
          Evidence0 dxyz hexyz = FinSubstHomDepthObjEval {dx} {dy=dyz} x hyz
          (hxyz ** Evidence0 dexyz evalxyz) = hexyz
        in
        Evidence0 dxyz $ rewrite powerOfMulSym cz cx cy in
          (hxyz ** Evidence0 (smax hdyz (smax (smax dexyz 2) 1)) $
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
finSubstHomObjDepth x y = fst0 $ FinSubstHomDepthObjEval x y

public export
finSubstHomObj : {0 cx, dx, cy, dy : Nat} ->
  (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
  FinSubstT (finSubstHomObjCard x y) (finSubstHomObjDepth x y)
finSubstHomObj x y = fst $ snd0 $ FinSubstHomDepthObjEval x y

public export
0 finSubstEvalMorphDepth : {0 cx, dx, cy, dy : Nat} ->
  (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
  Nat
finSubstEvalMorphDepth x y = fst0 (snd (snd0 (FinSubstHomDepthObjEval x y)))

public export
finSubstEvalMorph : {0 cx, dx, cy, dy : Nat} ->
  (x : FinSubstT cx dx) -> (y : FinSubstT cy dy) ->
  EvalMorphType x y (finSubstHomObj x y) (finSubstEvalMorphDepth x y)
finSubstEvalMorph x y = snd0 $ snd $ snd0 $ FinSubstHomDepthObjEval x y

------------------------------------
---- Compilation to polynomials ----
------------------------------------

public export
FSToBANatMorph : {0 cx, dx, cy, dy : Nat} ->
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
InterpTermAlg : FSTAlg (\_, _, x, _ => interpFinSubst x)
InterpTermAlg = MkFSTAlg () (\_ => Left) (\_ => Right) (\_, _ => MkPair)

public export
interpFinSubstTerm : {0 c, d : Nat} -> {x : FinSubstT c d} ->
  FinSubstTerm x -> interpFinSubst {c} {d} x
interpFinSubstTerm {x} = fstCata InterpTermAlg

public export
interpFinSubstMorph : {0 cx, dx, cy, dy, depth : Nat} ->
  {x : FinSubstT cx dx} -> {y : FinSubstT cy dy} ->
  FinSubstMorph {cx} {dx} {cy} {dy} depth x y ->
  interpFinSubst {c=cx} {d=dx} x ->
  interpFinSubst {c=cy} {d=dy} y
interpFinSubstMorph m = ?interpFinSubstMorph_hole
