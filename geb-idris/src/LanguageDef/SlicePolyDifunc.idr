module LanguageDef.SlicePolyDifunc

import public Library.IdrisUtils
import public Library.IdrisCategories
import public Library.IdrisAlgebra
import public LanguageDef.SlicePolyCat
import public LanguageDef.GenPolyFunc
import public LanguageDef.PolySliceCat
import public LanguageDef.DislicePolyCat
import public LanguageDef.PolyDifunc

%hide Library.IdrisCategories.BaseChangeF

public export
DFInitialArena : MLDirichCatObj
DFInitialArena = PFInitialArena

public export
dfFromInitialMor : (p : MLDirichCatObj) -> DirichNatTrans DFInitialArena p
dfFromInitialMor p = (\ev => void ev ** \ev, _ => void ev)

public export
DFTerminalArena : MLDirichCatObj
DFTerminalArena = PFIdentityArena

public export
dfToTerminalMor : (p : MLDirichCatObj) -> DirichNatTrans p DFTerminalArena
dfToTerminalMor p = (\_ => () ** \_, _ => ())

public export
pfGenClosureObjPos : (p, q, r : PolyFunc) -> Type
pfGenClosureObjPos p q r = PolyNatTrans (pfProductArena p q) r

public export
pfGenPolyProdClosureObj : PolyFunc
pfGenPolyProdClosureObj = PFIdentityArena

public export
pfGenDirichParProdClosureObj : PolyFunc
pfGenDirichParProdClosureObj = PFTerminalArena

public export
pfGenPolyProdClosurePos : (q, r : PolyFunc) -> Type
pfGenPolyProdClosurePos = pfGenClosureObjPos pfGenPolyProdClosureObj

public export
pfGenDirichParProdClosurePos : (q, r : PolyFunc) -> Type
pfGenDirichParProdClosurePos = pfGenClosureObjPos pfGenDirichParProdClosureObj

public export
pfHomObjPosFromGen : (q, p : PolyFunc) ->
  pfHomObjPosNT q p -> pfGenPolyProdClosurePos q p
pfHomObjPosFromGen q p hi =
  (fst hi . snd **
   \qi => snd hi (snd qi))

public export
pfHomObjPosToGen : (q, p : PolyFunc) ->
  pfGenPolyProdClosurePos q p -> pfHomObjPosNT q p
pfHomObjPosToGen q p gi =
  (fst gi . MkPair () **
   \qi => snd gi ((), qi))

public export
pfParProdClosureObjPosFromGen : (q, p : PolyFunc) ->
  pfParProdClosurePosNT q p -> pfGenDirichParProdClosurePos q p
pfParProdClosureObjPosFromGen q p ci =
  (fst ci . snd **
   \qi => Right . snd ci (snd qi))

public export
pfParProdClosureObjPosToGen : (q, p : PolyFunc) ->
  pfGenDirichParProdClosurePos q p -> pfParProdClosurePosNT q p
pfParProdClosureObjPosToGen q p gi =
  (fst gi . MkPair () **
   \qi, pd => case snd gi ((), qi) pd of Left ev => void ev ; Right qd => qd)

public export
pfGenClosureObjDirSlOnPos : (p, q, r : PolyFunc) ->
  ((pfPos p, pfPos q) -> pfPos r) -> SliceObj (pfProductPos p q)
pfGenClosureObjDirSlOnPos p q r = (.) (pfDir {p=r})

public export
pfGenClosureObjDirSlNT : (p, q, r : PolyFunc) ->
  PolyNatTrans (pfProductArena p q) r -> SliceObj (pfPDir (pfProductArena p q))
pfGenClosureObjDirSlNT p q r alpha pqd =
  (rd :
    pfGenClosureObjDirSlOnPos p q r
      (pntOnPos {p=(pfProductArena p q)} {q=r} alpha)
      (fst pqd) **
   pntOnDir {p=(pfProductArena p q)} {q=r} alpha (fst pqd) rd = snd pqd)

public export
pfGenClosureObjDirSl : (p, q, r : PolyFunc) ->
  pfGenClosureObjPos p q r -> SliceObj (pfPDir (pfProductArena p q))
pfGenClosureObjDirSl = pfGenClosureObjDirSlNT

public export
pfGenClosureObjDir : (p, q, r : PolyFunc) ->
  PolyNatTrans (pfProductArena p q) r -> pfGenClosureObjPos p q r -> Type
pfGenClosureObjDir p q r alpha gi =
  (pqi : pfPos (pfProductArena p q) **
   ieq : fst gi pqi = fst alpha pqi **
   rd : pfDir {p=r} (fst gi pqi) **
   snd gi pqi rd = snd alpha pqi (rewrite sym ieq in rd))

public export
pfGenPolyProdClosureNT : (q, r : PolyFunc) ->
  PolyNatTrans
    (pfProductArena SlicePolyDifunc.pfGenPolyProdClosureObj q)
    r ->
  PolyNatTrans
    (pfProductArena SlicePolyDifunc.pfGenPolyProdClosureObj q)
    r
pfGenPolyProdClosureNT q r alpha = (fst alpha ** \_, _ => Left ())

public export
pfGenPolyProdClosureDir : (q, r : PolyFunc) ->
  pfGenPolyProdClosurePos q r -> Type
pfGenPolyProdClosureDir q r gi =
  pfGenClosureObjDir
    pfGenPolyProdClosureObj
    q
    r
    (pfGenPolyProdClosureNT q r gi)
    gi

public export
pfGenDirichParProdClosureNT : (q, r : PolyFunc) ->
  PolyNatTrans
    (pfProductArena SlicePolyDifunc.pfGenDirichParProdClosureObj q)
    r ->
  PolyNatTrans
    (pfProductArena SlicePolyDifunc.pfGenDirichParProdClosureObj q)
    r
pfGenDirichParProdClosureNT q r = id

public export
pfGenDirichParProdClosureDir : (q, r : PolyFunc) ->
  pfGenDirichParProdClosurePos q r -> Type
pfGenDirichParProdClosureDir q r gi =
  pfGenClosureObjDir
    pfGenDirichParProdClosureObj
    q
    r
    (pfGenDirichParProdClosureNT q r gi)
    gi

public export
pfGenClosureObj : (p, q, r : PolyFunc) ->
  PolyNatTrans (pfProductArena p q) r -> PolyFunc
pfGenClosureObj p q r alpha =
  (pfGenClosureObjPos p q r ** pfGenClosureObjDir p q r alpha)

-- The left adjoint of the covariant hom-functor on `PolyFunc`,
-- which is multiplication by a constant (polynomial) functor
-- (whose position-type is the argument to the adjoint,
-- and has no directions at any position).
public export
polyHomAdjL : PolyFunc -> Type -> PolyFunc
polyHomAdjL p x = ((pfPos p, x) ** \pix => pfDir {p} (fst pix))

public export
polyHomAdjLmap : (p : PolyFunc) -> (a, b : Type) ->
  (a -> b) -> PolyNatTrans (polyHomAdjL p a) (polyHomAdjL p b)
polyHomAdjLmap p a b m = (mapSnd m ** \(pi, ea) => id {a=(pfDir {p} pi)})

-- The hom-profunctor, or with the first argument fixed, covariant hom-functor
-- on `PolyFunc`.
public export
polyHomAdjR : PolyFunc -> PolyFunc -> Type
polyHomAdjR = PolyNatTrans

public export
polyHomAdjRmap : (p, q, r : PolyFunc) ->
  PolyNatTrans q r -> polyHomAdjR p q -> polyHomAdjR p r
polyHomAdjRmap p q r = pntVCatComp {p} {q} {r}

public export
polyHomAdjLAdjunct : (p : PolyFunc) -> (a : Type) -> (q : PolyFunc) ->
  PolyNatTrans (polyHomAdjL p a) q -> (a -> polyHomAdjR p q)
polyHomAdjLAdjunct (ppos ** pdir) a (qpos ** qdir) (onpos ** ondir) ea =
  (\pi => onpos (pi, ea) ** \pi => ondir (pi, ea))

public export
polyHomAdjRAdjunct : (p : PolyFunc) -> (a : Type) -> (q : PolyFunc) ->
  (a -> polyHomAdjR p q) -> PolyNatTrans (polyHomAdjL p a) q
polyHomAdjRAdjunct (ppos ** pdir) a (qpos ** qdir) m =
  (\(pi, ea) => fst (m ea) pi ** \(pi, ea) => snd (m ea) pi)

public export
pfDirichChangeArena : (p, q : PolyFunc) -> DirichNatTrans p q -> PolyFunc
pfDirichChangeArena (ppos ** pdir) (qpos ** qdir) (onpos ** ondir) =
  (pfPosChangePos (ppos ** pdir) (qpos ** qdir) onpos **
   \(pi ** qd) =>
    (pd : pfPosChangeDir (ppos ** pdir) (qpos ** qdir) onpos (pi ** qd) **
     ondir pi pd = qd))

public export
PIP : Type
PIP =
  (t1p : Type **
   t1d : SliceObj t1p **
   et1p : SliceObj t1p **
   et1d : (it1 : t1p) -> SliceObj (et1p it1) **
   et2p : (it1 : t1p) -> SliceObj (t1d it1) **
   et2d : (it1 : t1p) -> (dt1 : t1d it1) -> SliceObj (et2p it1 dt1) **
   -- The following two constitute a `(t1p, t1d)`-indexed family of
   -- polynomial natural transformations from `et1` to `et2`, or
   -- equivalently, universal-family morphisms from `et2` to `et1`.
   etonpos : (it1 : t1p) -> (dt1 : t1d it1) -> et1p it1 -> et2p it1 dt1 **
   {- etondir : -} (it1 : t1p) -> (dt1 : t1d it1) -> (ie1 : et1p it1) ->
    et2d it1 dt1 (etonpos it1 dt1 ie1) -> et1d it1 ie1)

public export
InterpPIPposR : (pip : PIP) -> PolyFunc -> SliceObj (fst pip)
InterpPIPposR (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir)
  p it1 =
    polyHomAdjR (et1p it1 ** et1d it1) p

public export
InterpPIPposRmap : (pip : PIP) -> (p, q : PolyFunc) ->
  PolyNatTrans p q ->
  SliceMorphism {a=(fst pip)} (InterpPIPposR pip p) (InterpPIPposR pip q)
InterpPIPposRmap
  (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir)
    p q nt it1 =
      polyHomAdjRmap (et1p it1 ** et1d it1) p q nt

public export
InterpPIPposL : (pip : PIP) -> SliceObj (fst pip) -> PolyFunc
InterpPIPposL
  (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir) slp =
    ((it1 : t1p ** (et1p it1, slp it1)) **
     \(it1 ** (iet1, ex)) => et1d it1 iet1)

public export
InterpPIPposLmap : (pip : PIP) -> (x, y : SliceObj (fst pip)) ->
  SliceMorphism {a=(fst pip)} x y ->
  PolyNatTrans (InterpPIPposL pip x) (InterpPIPposL pip y)
InterpPIPposLmap
  (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir) x y m =
    (dpMapSnd $ \it1 => mapSnd (m it1) **
     \(it1 ** (iet1, ex)) => id)

-- We exhibit an adjunction between `Poly` on the left and `Type/(fst pip)`
-- on the right, with `InterpPIPposL` and `InterpPIPposR` being the
-- adjoint functors.  This may be seen as a first component of a generalized
-- version of formula 6.73 in the polynomial functors book, where instead
-- of functors `p`, `q`, and `r` and the function `f` we have an
-- `x : SliceObj(fst pip)`, a `pip : PIP`, and a functor `p`; and the
-- `arch(q, f)` operation (which we have called `\p => pfPosChangeArena p q f`)
-- corresponds to `InterpPIPposL pip`, post-composition with `q`
-- corresponds with `InterpPIPposR pip`, and `q . 1` (AKA `const (pfPos q)`)
-- corresponds with `InterpPIPposR pip 1`, which is the terminal object
-- of `SliceObj(fst pip)`.  In particular this means that `f` has no
-- analogue (yet) because the type signature of its analogue would constrain
-- it to be the terminal morphism in `SliceObj(fst pip)`.
--
-- Later we shall exhibit a (multi-)adjunction dependent on this one, such that
-- putting the two together will produce a parametric right adjoint on
-- `Poly` itself.

public export
InterpPIPposLAdjunct : (pip : PIP) ->
  (x : SliceObj (fst pip)) -> (p : PolyFunc) ->
  PolyNatTrans (InterpPIPposL pip x) p ->
  SliceMorphism {a=(fst pip)} x (InterpPIPposR pip p)
InterpPIPposLAdjunct
  (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir)
  x (ppos ** pdir) (onpos ** ondir) it1 ex =
    (\iet1 => onpos (it1 ** (iet1, ex)) **
     \iet1 => ondir (it1 ** (iet1, ex)))

public export
InterpPIPposRAdjunct : (pip : PIP) ->
  (x : SliceObj (fst pip)) -> (p : PolyFunc) ->
  SliceMorphism {a=(fst pip)} x (InterpPIPposR pip p) ->
  PolyNatTrans (InterpPIPposL pip x) p
InterpPIPposRAdjunct
  (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir)
  x (ppos ** pdir) m =
    (\(it1 ** (iet1, ex)) => fst (m it1 ex) iet1 **
     \(it1 ** (iet1, ex)) => snd (m it1 ex) iet1)

-- The first component of a polynomial functor on `PolyFunc` -- the
-- interpretation of a `PIP` -- is a coproduct of representables (thus
-- a parametric right adjoint from `PolyFunc` to `Type`).
public export
InterpPIPpos : PIP -> PolyFunc -> Type
InterpPIPpos (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir)
  =
    DPair t1p
    . InterpPIPposR
      (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir)

public export
InterpPIPposMap : (pip : PIP) -> (p, q : PolyFunc) ->
  PolyNatTrans p q -> InterpPIPpos pip p -> InterpPIPpos pip q
InterpPIPposMap
  (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir)
  p q alpha (it1 ** nt1) =
    (it1 **
     InterpPIPposRmap
      (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir)
      p q alpha it1 nt1)

-- Because the category of universal families is the opposite of the
-- category of polynomial functors, we may view `InterpPIPpos`, which we
-- have shown is a copresheaf of `PolyFunc`, equivalently as a presheaf
-- on `MLUFamObj/MLUFamMor`.
public export
InterpPIPposOp : PIP -> MLUFamObj -> Type
InterpPIPposOp
  (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir) p =
    (it1 : t1p ** MLUFamMor p (et1p it1 ** et1d it1))

-- Polynomial functors and universal families are defined by the same
-- data (they have the same objects, being opposite categories), and
-- `InterpPIPposOp` is just `InterpPIPpos` verbatim, with a different
-- view on it.
public export
InterpPIPposOpEquiv : (pip : PIP) -> (f : MLUFamObj) ->
  InterpPIPpos pip f = InterpPIPposOp pip f
InterpPIPposOpEquiv
  (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir) f =
    Refl

-- Exhibit `InterpPIPpos` explicitly as a presheaf on `MLUFamObj`.
public export
InterpPIPposOpContramap : (pip : PIP) -> (f, g : MLUFamObj) ->
  MLUFamMor g f -> InterpPIPposOp pip f -> InterpPIPposOp pip g
InterpPIPposOpContramap
  (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir)
  f g (it1 ** nt1) =
    InterpPIPposMap
      (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir)
      f g (it1 ** nt1)

-- The Yoneda lemma and the universal property of the coproduct together
-- tell us that a natural transformation from a copresheaf of the form
-- `InterpPIPpos pip` is a product of applications of the codomain to
-- the directions of the domain.
public export
PIPposNT : PIP -> PIP -> Type
PIPposNT
  (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir)
  (t1p' ** t1d' ** et1p' ** et1d' ** et2p' ** et2d' ** etonpos' ** etondir') =
    (ont1p : t1p -> t1p' **
     onet1p : (it1 : t1p) -> et1p' (ont1p it1) -> et1p it1 **
     {- onet1d : -} (it1 : t1p) -> (it1' : et1p' (ont1p it1)) ->
      et1d it1 (onet1p it1 it1') -> et1d' (ont1p it1) it1')

public export
InterpPIPposNT : (f, g : PIP) -> PIPposNT f g ->
  (p : PolyFunc) -> InterpPIPpos f p -> InterpPIPpos g p
InterpPIPposNT
  (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir)
  (t1p' ** t1d' ** et1p' ** et1d' ** et2p' ** et2d' ** etonpos' ** etondir')
  (ont1p ** onet1p ** onet1d) (ppos ** pdir) (it1 ** onpos ** ondir) =
    (ont1p it1 **
     pntVCatComp
      {p=(et1p' (ont1p it1) ** et1d' (ont1p it1))}
      {q=(et1p it1 ** et1d it1)}
      {r=(ppos ** pdir)}
      (onpos ** ondir)
      (onet1p it1 ** onet1d it1))

-- For any `pip : PIP`, `InterpPIPpos pip 1` is `fst pip`.  Because
-- we have exhibited `InterpPIPposR pip` as a right adjoint from
-- `PolyFunc` to `SliceObj (fst pip)`, and `InterpPIPpos pip` is
-- the dependent sum of `InterpPIPposR pip` over the terminal morphism
-- from `fst pip`, we can exhibit `InterpPIPpos` as a parametric
-- right adjoint (with a left multi-adjoint).
public export
InterpPIPposMultiI : PIP -> Type -> Type
InterpPIPposMultiI pip x = x -> fst pip

public export
InterpPIPposMultiIcontramap : (pip : PIP) -> (x, y : Type) ->
  (y -> x) -> InterpPIPposMultiI pip x -> InterpPIPposMultiI pip y
InterpPIPposMultiIcontramap pip x y = (|>)

public export
InterpPIPposMultiLSl :
  (pip : PIP) -> (x : Type) -> InterpPIPposMultiI pip x -> SliceObj (fst pip)
InterpPIPposMultiLSl pip x f it1 = (ex : x ** f ex = it1)

public export
InterpPIPposMultiL :
  (pip : PIP) -> (x : Type) -> InterpPIPposMultiI pip x -> PolyFunc
InterpPIPposMultiL pip x f = InterpPIPposL pip (InterpPIPposMultiLSl pip x f)

public export
InterpPIPposMultiLmap : (pip : PIP) ->
  (x, y : Type) -> (mxy : x -> y) -> (el : InterpPIPposMultiI pip y) ->
  PolyNatTrans
    (InterpPIPposMultiL pip x $ InterpPIPposMultiIcontramap pip y x mxy el)
    (InterpPIPposMultiL pip y el)
InterpPIPposMultiLmap
  (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir)
  x y mxy el =
    (dpMapSnd $ \it1 => mapSnd $ dpBimap mxy $ \ex => id **
     \(it1 ** (ie1, (ex ** ieq))) => id)

public export
InterpPIPposMultiILpair : PIP -> Type -> PolyFunc -> Type
InterpPIPposMultiILpair pip x y =
  (i : InterpPIPposMultiI pip x ** PolyNatTrans (InterpPIPposMultiL pip x i) y)

public export
InterpPIPposLMultiAdjunct : (pip : PIP) -> (x : Type) -> (y : PolyFunc) ->
  InterpPIPposMultiILpair pip x y -> (x -> InterpPIPpos pip y)
InterpPIPposLMultiAdjunct
  (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir)
  x y (i ** onpos ** ondir) ex =
    (i ex **
     \ie1 => onpos (i ex ** (ie1, (ex ** Refl))) **
     \ie1, dy => ondir (i ex ** (ie1, (ex ** Refl))) dy)

public export
InterpPIPposRMultiAdjunct : (pip : PIP) -> (x : Type) -> (y : PolyFunc) ->
  (x -> InterpPIPpos pip y) -> InterpPIPposMultiILpair pip x y
InterpPIPposRMultiAdjunct
  (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir)
  x y mxi =
    (fst . mxi **
     \(it1 ** (ie1, (ex ** comm))) =>
      fst (snd (mxi ex)) (rewrite comm in ie1) **
     \(it1 ** (ie1, (ex ** comm))), dy =>
      rewrite sym comm in snd (snd (mxi ex)) (rewrite comm in ie1) dy)

public export
UFamPFObj : Type
UFamPFObj = IntUFamObj PolyFunc

public export
UFamPFMor : IntMorSig UFamPFObj
UFamPFMor = IntUFamMor {c=PolyFunc} PolyNatTrans

public export
InterpPIPposLMultiK : PIP -> Type -> UFamPFObj
InterpPIPposLMultiK pip x =
  (InterpPIPposMultiI pip x ** InterpPIPposMultiL pip x)

public export
InterpPIPposLMultiKmap : (pip : PIP) -> (x, y : Type) ->
  (x -> y) -> UFamPFMor (InterpPIPposLMultiK pip x) (InterpPIPposLMultiK pip y)
InterpPIPposLMultiKmap pip x y mxy =
  (InterpPIPposMultiIcontramap pip y x mxy ** InterpPIPposMultiLmap pip x y mxy)

public export
InterpPIPdir : (pip : PIP) -> (p : PolyFunc) -> InterpPIPpos pip p -> Type
InterpPIPdir
  (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir)
  p (it1 ** onpos1 ** ondir1) =
    (dt1 : t1d it1 **
     nt :
      DirichNatTrans
        (et2p it1 dt1 ** et2d it1 dt1)
        (arBaseChangeArena {a=(et1p it1)} p onpos1) **
     onposeq : (ie2 : et2p it1 dt1) -> etonpos it1 dt1 (fst nt ie2) = ie2 **
     (ie2 : et2p it1 dt1) -> (de2 : et2d it1 dt1 ie2) ->
      ondir1 (fst nt ie2) (snd nt ie2 de2) =
      etondir it1 dt1 (fst nt ie2) (rewrite (onposeq ie2) in de2))

public export
InterpPIPdirMap : (pip : PIP) -> {p, q : PolyFunc} ->
  (nt : PolyNatTrans p q) -> (i : InterpPIPpos pip p) ->
  InterpPIPdir pip q (InterpPIPposMap pip p q nt i) ->
  InterpPIPdir pip p i
InterpPIPdirMap
  (t1p ** t1d ** et1p ** et1d ** et2p ** et2d ** etonpos ** etondir)
  {p=(ppos ** pdir)} {q=(qpos ** qdir)} (monpos ** mondir)
  (it1 ** onpos1 ** ondir1) =
    \(dt1 ** (onpos2 ** ondir2) ** ondir2eq) =>
      (dt1 **
       (onpos2 **
        \ie2, de2 => mondir (onpos1 (onpos2 ie2)) (ondir2 ie2 de2)) **
       ondir2eq)

public export
InterpPIP : PIP -> PolyFunc -> PolyFunc
InterpPIP pip p = (InterpPIPpos pip p ** InterpPIPdir pip p)

public export
InterpPIPmap : (pip : PIP) -> {p, q : PolyFunc} ->
  PolyNatTrans p q -> PolyNatTrans (InterpPIP pip p) (InterpPIP pip q)
InterpPIPmap pip {p} {q} nt =
  (InterpPIPposMap pip p q nt ** InterpPIPdirMap pip {p} {q} nt)

-- Here we see that `InterpPIPdir/InterpPIPdirMap`, which provide the second
-- component of the polynomial functor on polynomial functors represented by
-- a `PIP`, may be viewed as a copresheaf on the _opposite_ of the category
-- of elements of `InterpPIPpos/InterpPIPposMap` (which is a copresheaf on
-- `PolyFunc`).
public export
InterpPIPposElemMap : (pip : PIP) -> {p, q : PolyFunc} ->
  (pi : InterpPIPpos pip p) -> (qi : InterpPIPpos pip q) ->
  -- A morphism from (q, qi) to (p, pi)...
  (nt : PolyNatTrans q p) -> InterpPIPposMap pip q p nt qi = pi ->
  -- ...induces a morphism from `InterpPIPdir pip p pi` to
  -- `InterpPIPdir pip q qi`.
  InterpPIPdir pip p pi -> InterpPIPdir pip q qi
InterpPIPposElemMap pip {p} {q} pi qi nt eq pd =
  InterpPIPdirMap pip {p=q} {q=p} nt qi $ rewrite eq in pd

public export
PostcompToPIP : PolyFunc -> PIP
PostcompToPIP (qpos ** qdir) =
  (qpos **
   \_ => Unit **
   qdir **
   \_, _ => Unit **
   \_, _ => Unit **
   \_, _, _ => Unit **
   \_, _, _ => () **
   \_, _, _, () => ())

public export
InterpPostcompToPIP : (q : PolyFunc) -> (p : PolyFunc) ->
  PolyNatTrans (pfCompositionArena q p) (InterpPIP (PostcompToPIP q) p)
InterpPostcompToPIP (qpos ** qdir) (ppos ** pdir) =
  (\(qi ** qdp) => (qi ** qdp ** \_, _ => ()) **
   \(qi ** qdp), (() ** (qd ** pd) ** ueq1_ ** ueq2_) => (qd () ** pd () ()))

public export
InterpPostcompFromPIP : (q : PolyFunc) -> (p : PolyFunc) ->
  PolyNatTrans (InterpPIP (PostcompToPIP q) p) (pfCompositionArena q p)
InterpPostcompFromPIP (qpos ** qdir) (ppos ** pdir) =
  (\(qi ** qdp ** u_) =>
    (qi ** qdp) **
   \(qi ** qdp ** u_), (qd ** pd) =>
    (() **
     (\() => qd ** \(), () => pd) **
     \() => Refl ** \(), () => unitUnique (u_ qd pd) ()))

public export
PolyIntPoly : Type
PolyIntPoly =
  (posp : Type **
   posd : SliceObj posp **
   dirp : SliceObj posp **
   dird : (pi : posp) -> SliceObj (dirp pi) **
   {- ondir : -} (pi : posp) -> posd pi -> (di : dirp pi) -> dird pi di)

public export
pipPos : PolyIntPoly -> PolyFunc
pipPos pip = (fst pip ** fst (snd pip))

public export
pipDir : PolyIntPoly -> PolyFunc
pipDir pip =
  (Sigma {a=(fst pip)} (fst (snd (snd pip))) **
   \i => fst (snd (snd (snd pip))) (fst i) (snd i))

public export
pipDirPosMor : (pip : PolyIntPoly) -> PolyNatTrans (pipDir pip) (pipPos pip)
pipDirPosMor (posp ** posd ** dirp ** dird ** ondir) =
  (DPair.fst ** \i, d => ondir (fst i) d (snd i))

public export
pfPullbackPos : {p, q, r : PolyFunc} ->
  PolyNatTrans p r -> PolyNatTrans q r -> Type
pfPullbackPos {p} {q} {r} f g =
  (pqi : (pfPos p, pfPos q) **
   pntOnPos {p} {q=r} f (fst pqi) = pntOnPos {p=q} {q=r} g (snd pqi))

public export
pfPullbackDir : {p, q, r : PolyFunc} ->
  (f : PolyNatTrans p r) -> (g : PolyNatTrans q r) ->
  pfPullbackPos {p} {q} {r} f g -> Type
pfPullbackDir {p} {q} {r} f g i =
  impredPushout
    {a=(pfDir {p=r} (fst f $ fst $ fst i))}
    {b=(pfDir {p} (fst $ fst i))}
    {c=(pfDir {p=q} (snd $ fst i))}
    (snd f (fst $ fst i))
    (\rd => snd g (snd $ fst i) (replace {p=(pfDir {p=r})} (snd i) rd))

public export
pfPullbackAr : {p, q, r : PolyFunc} ->
  PolyNatTrans p r -> PolyNatTrans q r -> PolyFunc
pfPullbackAr {p} {q} {r} f g =
  (pfPullbackPos {p} {q} {r} f g ** pfPullbackDir {p} {q} {r} f g)

public export
pfPullbackArProj1 : {p, q, r : PolyFunc} ->
  (psl : PolyNatTrans p r) -> (qsl : PolyNatTrans q r) ->
  PolyNatTrans (pfPullbackAr {p} {q} {r} psl qsl) p
pfPullbackArProj1 {p} {q} {r} psl qsl =
  (\pqi => fst (fst pqi) ** \pqi, pd, x, el => fst el $ Left pd)

public export
pfPullbackArProj2 : {p, q, r : PolyFunc} ->
  (psl : PolyNatTrans p r) -> (qsl : PolyNatTrans q r) ->
  PolyNatTrans (pfPullbackAr {p} {q} {r} psl qsl) q
pfPullbackArProj2 {p} {q} {r} psl qsl =
  (\pqi => snd (fst pqi) ** \pqi, pd, x, el => fst el $ Right pd)

public export
pfPullbackArSlProj1 : {p, q, r : PolyFunc} ->
  (psl : PolyNatTrans p r) -> (qsl : PolyNatTrans q r) ->
  PolyNatTrans (pfPullbackAr {p} {q} {r} psl qsl) r
pfPullbackArSlProj1 {p} {q} {r} psl qsl =
  pntVCatComp {p=(pfPullbackAr {p} {q} {r} psl qsl)} {q=p} {r}
    psl
    (pfPullbackArProj1 {p} {q} {r} psl qsl)

public export
pfPullbackArSlProj2 : {p, q, r : PolyFunc} ->
  (psl : PolyNatTrans p r) -> (qsl : PolyNatTrans q r) ->
  PolyNatTrans (pfPullbackAr {p} {q} {r} psl qsl) r
pfPullbackArSlProj2 {p} {q} {r} psl qsl =
  pntVCatComp {p=(pfPullbackAr {p} {q} {r} psl qsl)} {q} {r}
    qsl
    (pfPullbackArProj2 {p} {q} {r} psl qsl)

public export
0 pfPullbackArSlProjEq : FunExt -> {p, q, r : PolyFunc} ->
  (psl : PolyNatTrans p r) -> (qsl : PolyNatTrans q r) ->
  CPFNatTransEq
    (pfPullbackAr {p} {q} {r} psl qsl)
    r
    (pfPullbackArSlProj1 {p} {q} {r} psl qsl)
    (pfPullbackArSlProj2 {p} {q} {r} psl qsl)
pfPullbackArSlProjEq fext {p} {q} {r} psl qsl =
  Evidence0 snd (\i, d => funExt $ \x => funExt $ \el => sym $ snd el d)

-- Since we have proven that `pfPullbackArSlProj1` and `pfPullbackArSlProj2`
-- are equal (which is part of what characterizes the pullback), we may
-- arbitrarily choose one of them to call simply `pfPullbackArSlProj`.
public export
pfPullbackArSlProj : {p, q, r : PolyFunc} ->
  (psl : PolyNatTrans p r) -> (qsl : PolyNatTrans q r) ->
  PolyNatTrans (pfPullbackAr {p} {q} {r} psl qsl) r
pfPullbackArSlProj = pfPullbackArSlProj1

public export
pfPullbackArSlObj : {p, q, r : PolyFunc} ->
  (psl : PolyNatTrans p r) -> (qsl : PolyNatTrans q r) ->
  CPFSliceObj r
pfPullbackArSlObj {p} {q} {r} psl qsl =
  (pfPullbackAr {p} {q} {r} psl qsl ** pfPullbackArSlProj {p} {q} {r} psl qsl)

-- To interpret a polynomial functor on `PolyFunc` itself, first
-- we perform a base change, which is a pullback, which in the case
-- of a polynomial functor is a pullback on positions and a pushout
-- on directions.  In this case we're pulling back along the unique
-- morphism to the terminal object, which means that the pullback
-- reduces to a product.
public export
InterpPIPpb : PolyIntPoly -> PolyFunc -> PolyFunc
InterpPIPpb (posp ** posd ** dirp ** dird ** ondir) (ppos ** pdir) =
  ((Sigma {a=posp} dirp, ppos) **
   \((pi ** di), i) => Either (dird pi di) (pdir i))

public export
InterpPIPpbProj : (pip : PolyIntPoly) -> (p : PolyFunc) ->
  PolyNatTrans (InterpPIPpb pip p) (pipDir pip)
InterpPIPpbProj (posp ** posd ** dirp ** dird ** ondir) (ppos ** pdir) =
  (Builtin.fst ** \((pi ** di), i) => Left)

-- The composite of the dependent product ("pi") after the base change
-- which constitutes the first two components of the three-way composite
-- (sigma after pi after base change) in the interpretation of a `PolyIntPoly`.
-- `InterppPIPpb` is the first component, so we may view this as the action
-- of the "pi" on the output of `InterpPIPpb`.
public export
InterpPIPpibc : PolyIntPoly -> PolyFunc -> PolyFunc
InterpPIPpibc (posp ** posd ** dirp ** dird ** ondir) (ppos ** pdir) =
  ((pi : posp **
    pm : dirp pi -> ppos **
    (di : dirp pi) -> pdir (pm di) -> dird pi di) **
   \(pi ** pm ** dm) =>
    (pd : posd pi **
     di : dirp pi **
     d : pdir (pm di) **
     dm di d = ondir pi pd di))

public export
PEAtoPIP : PolyEnrAr -> PIP
PEAtoPIP (PEA peaPos peaDir) =
  (peaPos **
   \_ => Unit **
   \i => fst (peaDir i) **
   \i, pd1 => Either Unit (snd (peaDir i) pd1) **
   \_, _ => Unit **
   \_, _, _ => Unit **
   \_, _, _ => () **
   \_, _, _, () => Left ())

public export
InterpPEAtoPIP : (pea : PolyEnrAr) -> (p : PolyFunc) ->
  PolyNatTrans (InterpPEA pea p) (InterpPIP (PEAtoPIP pea) p)
InterpPEAtoPIP (PEA peaPos peaDir) (ppos ** pdir) =
  (\(i ** d) => (i ** \pd1 => fst (d pd1) ** \pd1, pd2 => snd (d pd1) pd2) **
   \(i ** d), (() ** (pd1 ** pd) ** pieq ** pdeq) =>
    (pd1 () ** pd () () ** rewrite pdeq () () in ()))

public export
InterpPEAfromPIPpos : (pea : PolyEnrAr) -> (p : PolyFunc) ->
  fst (InterpPIP (PEAtoPIP pea) p) -> fst (InterpPEA pea p)
InterpPEAfromPIPpos (PEA peaPos peaDir) (ppos ** pdir) (pi ** pm ** dm) =
  (pi ** \pd1 => (pm pd1 ** \pd2 => dm pd1 pd2))

public export
InterpPEAfromPIPdir : (pea : PolyEnrAr) -> (p : PolyFunc) ->
  (i : fst (InterpPIP (PEAtoPIP pea) p)) ->
  snd (InterpPEA pea p) (InterpPEAfromPIPpos pea p i) ->
  snd (InterpPIP (PEAtoPIP pea) p) i
InterpPEAfromPIPdir
    (PEA peaPos peaDir) (ppos ** pdir) (pi ** pm ** dm) (pd1 ** pd ** pd2)
    with (dm pd1 pd) proof dmeq
  InterpPEAfromPIPdir
    (PEA peaPos peaDir) (ppos ** pdir) (pi ** pm ** dm) (pd1 ** pd ** ())
    | Left () =
      (() ** (\() => pd1 ** \(), () => pd) ** \() => Refl ** \(), () => dmeq)
  InterpPEAfromPIPdir
    (PEA peaPos peaDir) (ppos ** pdir) (pi ** pm ** dm) (pd1 ** pd ** pd2)
    | Right _ =
      void pd2

public export
InterpPEAfromPIP : (pea : PolyEnrAr) -> (p : PolyFunc) ->
  PolyNatTrans (InterpPIP (PEAtoPIP pea) p) (InterpPEA pea p)
InterpPEAfromPIP pea p =
  (InterpPEAfromPIPpos pea p ** InterpPEAfromPIPdir pea p)

public export
InterpPIPpibcMap : (pip : PolyIntPoly) -> {p, q : PolyFunc} ->
  PolyNatTrans p q -> PolyNatTrans (InterpPIPpibc pip p) (InterpPIPpibc pip q)
InterpPIPpibcMap (posp ** posd ** dirp ** dird ** ondir)
  {p=(ppos ** pdir)} {q=(qpos ** qdir)} (monpos ** mondir) =
    (\(pi ** pm ** dm) =>
      (pi ** monpos . pm ** \di => dm di . mondir (pm di)) **
     \(pi ** pm ** dm), (pd ** di ** d ** deq) =>
      (pd ** di ** mondir (pm di) d ** deq))

-- Note that if the polynomial functor is to have no negative directions,
-- then `dm` must be made redundant, which means making it the unique
-- morphism to the terminal object, which in turn means making
-- `peaDir2` the constant initial object.  And with that reduction,
-- `PolyEnrAr` becomes effectively a single polynomial functor, and its
-- application becomes post-composition.  Thus post-compositions are the
-- only strictly positive polynomial functors on the category of polynomial
-- functors.  (The negative occurrence in the more general case is also
-- an inductive-inductive occurrence and the only one.  Thus post-compositions
-- are equivalently the only non-inductive-inductive polynomial functors on
-- the category of polynomial functors.)
public export
data PIPmuPos :
    PolyEnrAr -> Type where
  InPMPpi : {pip : PolyEnrAr} ->
    PIPmuPos pip
  InPMPpc : {pip : PolyEnrAr} ->
    (i : peaPos pip) ->
    (pm : peaPos2 pip i -> PIPmuPos pip) ->
    {-
     - This would be a negative occurrence (as well as an
     - inductive-inductive one).
    ((i2 :  peaPos2 pip i) ->
     PIPmuDir pip p (pm i2) -> Either Unit (peaDir2 pip i i2)) ->
     -}
    PIPmuPos pip

public export
data PIPmuDir :
    (pip : PolyEnrAr) -> PIPmuPos pip -> Type where
  InPMPdi : {pip : PolyEnrAr} ->
    PIPmuDir pip (InPMPpi {pip})
  InPMPdc : {pip : PolyEnrAr} ->
    (i : peaPos pip) ->
    (pm : peaPos2 pip i -> PIPmuPos pip) ->
    (i2 : peaPos2 pip i) ->
    (d : PIPmuDir pip (pm i2)) ->
    {-
     - This would be a negative occurrence.
    (dm : (i2 :  peaPos2 pip i) ->
     PIPmuDir pip p (pm i2) -> Either Unit (peaDir2 pip i i2)) ->
    dm i2 d = Left () ->
     -}
    PIPmuDir pip (InPMPpc {pip} i pm)

public export
PIPmu : PolyEnrAr -> PolyFunc
PIPmu pip = (PIPmuPos pip ** PIPmuDir pip)

public export
PIPconv : PolyIntPoly -> PIP
PIPconv (posp ** posd ** dirp ** dird ** ondir) =
  (posp **
   posd **
   dirp **
   dird **
   \_, _ => Unit **
   \_, _, _ => Unit **
   \_, _, _ => () **
   \it1, dt1, ie1, () => ondir it1 dt1 ie1)

public export
InterpPIPtoConv : (pip : PolyIntPoly) -> (p : PolyFunc) ->
  PolyNatTrans (InterpPIPpibc pip p) (InterpPIP (PIPconv pip) p)
InterpPIPtoConv (posp ** posd ** dirp ** dird ** ondir)
  (ppos ** pdir) =
    (id **
     \(it1 ** onpos1 ** ondir1),
      (dt1 ** (onpos2 ** ondir2) ** onposeq ** ondireq) =>
      (dt1 **
       onpos2 () **
       ondir2 () () **
       ondireq () ()))

public export
InterpPIPfromConv : (pip : PolyIntPoly) -> (p : PolyFunc) ->
  PolyNatTrans (InterpPIP (PIPconv pip) p) (InterpPIPpibc pip p)
InterpPIPfromConv
  (posp ** posd ** dirp ** dird ** ondir)
  (ppos ** pdir) =
    (id **
     \(it1 ** onpos1 ** ondir1), (dt1 ** onpos2 ** ondir2 ** ondireq) =>
      (dt1 **
       (\() => onpos2 **
        \(), () => ondir2) **
       \() => Refl **
       \(), () => ondireq))

public export
PEAtoPolyIntPoly : PolyEnrAr -> PolyIntPoly
PEAtoPolyIntPoly (PEA peaPos peaDir) =
  (peaPos **
   \_ => Unit **
   \i => fst (peaDir i) **
   \i, pd1 => Either Unit (snd (peaDir i) pd1) **
   \_, _, _ => Left ())

public export
InterpPEAtoPolyIntPoly : (pea : PolyEnrAr) -> (p : PolyFunc) ->
  PolyNatTrans (InterpPEA pea p) (InterpPIPpibc (PEAtoPolyIntPoly pea) p)
InterpPEAtoPolyIntPoly (PEA peaPos peaDir) (ppos ** pdir) =
  (\(i ** d) => (i ** \pd1 => fst (d pd1) ** \pd1, pd2 => snd (d pd1) pd2) **
   \(i ** d), (pi ** pd1 ** pd ** pdeq) => (pd1 ** pd ** rewrite pdeq in ()))

public export
InterpPEAfromPolyIntPolypos : (pea : PolyEnrAr) -> (p : PolyFunc) ->
  fst (InterpPIPpibc (PEAtoPolyIntPoly pea) p) -> fst (InterpPEA pea p)
InterpPEAfromPolyIntPolypos
  (PEA peaPos peaDir) (ppos ** pdir) (pi ** pm ** dm) =
    (pi ** \pd1 => (pm pd1 ** \pd2 => dm pd1 pd2))

public export
InterpPEAfromPolyIntPolydir : (pea : PolyEnrAr) -> (p : PolyFunc) ->
  (i : fst (InterpPIPpibc (PEAtoPolyIntPoly pea) p)) ->
  snd (InterpPEA pea p) (InterpPEAfromPolyIntPolypos pea p i) ->
  snd (InterpPIPpibc (PEAtoPolyIntPoly pea) p) i
InterpPEAfromPolyIntPolydir
    (PEA peaPos peaDir) (ppos ** pdir) (pi ** pm ** dm) (pd1 ** pd ** pd2)
    with (dm pd1 pd) proof dmeq
  InterpPEAfromPolyIntPolydir
    (PEA peaPos peaDir) (ppos ** pdir) (pi ** pm ** dm) (pd1 ** pd ** ())
    | Left () =
      (() ** pd1 ** pd ** dmeq)
  InterpPEAfromPolyIntPolydir
    (PEA peaPos peaDir) (ppos ** pdir) (pi ** pm ** dm) (pd1 ** pd ** pd2)
    | Right _ =
      void pd2

public export
InterpPEAfromPolyIntPoly : (pea : PolyEnrAr) -> (p : PolyFunc) ->
  PolyNatTrans
    (InterpPIPpibc (PEAtoPolyIntPoly pea) p)
    (InterpPEA pea p)
InterpPEAfromPolyIntPoly pea p =
  (InterpPEAfromPolyIntPolypos pea p ** InterpPEAfromPolyIntPolydir pea p)

public export
PostcompToPolyIntPoly : PolyFunc -> PolyIntPoly
PostcompToPolyIntPoly (qpos ** qdir) =
  (qpos **
   \_ => Unit **
   qdir **
   \_, _ => Unit **
   \_, _, _ => ())

public export
InterpPostcompToPolyIntPoly : (q : PolyFunc) -> (p : PolyFunc) ->
  PolyNatTrans
    (pfCompositionArena q p)
    (InterpPIPpibc (PostcompToPolyIntPoly q) p)
InterpPostcompToPolyIntPoly (qpos ** qdir) (ppos ** pdir) =
  (\(qi ** qdp) => (qi ** qdp ** \_, _ => ()) **
   \(qi ** qdp), (() ** qd ** pd ** Refl) => (qd ** pd))

public export
InterpPostcompFromPolyIntPoly : (q : PolyFunc) -> (p : PolyFunc) ->
  PolyNatTrans
    (InterpPIPpibc (PostcompToPolyIntPoly q) p)
    (pfCompositionArena q p)
InterpPostcompFromPolyIntPoly (qpos ** qdir) (ppos ** pdir) =
  (\(qi ** qdp ** u_) =>
    (qi ** qdp) **
   \(qi ** qdp ** u_), (qd ** pd) =>
    (() ** qd ** pd ** unitUnique (u_ qd pd) ()))

-- Note that if the polynomial functor is to have no negative directions,
-- then `dm` must be made redundant, which means making it the unique
-- morphism to the terminal object, which in turn means making
-- `peaDir2` the constant initial object.  And with that reduction,
-- `PolyEnrAr` becomes effectively a single polynomial functor, and its
-- application becomes post-composition.  Thus post-compositions are the
-- only strictly positive polynomial functors on the category of polynomial
-- functors.
mutual
  public export
  partial
  data PIPfreePos :
      PolyEnrAr -> PolyFunc -> Type where
    InPFPpv : {pip : PolyEnrAr} -> {p : PolyFunc} ->
      pfPos p ->
      PIPfreePos pip p
    InPFPpc : {pip : PolyEnrAr} -> {p : PolyFunc} ->
      (i : peaPos pip) ->
      (pm : peaPos2 pip i -> PIPfreePos pip p) ->
      ((i2 :  peaPos2 pip i) ->
       PIPfreeDir pip p (pm i2) -> Either Unit (peaDir2 pip i i2)) ->
      PIPfreePos pip p

  public export
  partial
  data PIPfreeDir :
      (pip : PolyEnrAr) -> (p : PolyFunc) -> PIPfreePos pip p -> Type where
    InPFPdv : {pip : PolyEnrAr} -> {p : PolyFunc} ->
      (i : pfPos p) -> pfDir {p} i ->
      PIPfreeDir pip p (InPFPpv {pip} {p} i)
    InPFPdc : {pip : PolyEnrAr} -> {p : PolyFunc} ->
      (i : peaPos pip) ->
      (pm : peaPos2 pip i -> PIPfreePos pip p) ->
      (i2 : peaPos2 pip i) ->
      (d : PIPfreeDir pip p (pm i2)) ->
      (dm : (i2 :  peaPos2 pip i) ->
       PIPfreeDir pip p (pm i2) -> Either Unit (peaDir2 pip i i2)) ->
      dm i2 d = Left () ->
      PIPfreeDir pip p (InPFPpc {pip} i pm dm)

  public export
  partial
  PIPfree : PolyEnrAr -> PolyFunc -> PolyFunc
  PIPfree pip p = (PIPfreePos pip p ** PIPfreeDir pip p)

-- The dependent sum ("sigma") which constitutes the last composite in the
-- interpretation of a `PolyIntPoly`.
--
-- A dependent sum along the unique morphism to the terminal object
-- simply forgets the morphism component of the slice object.
public export
InterpPIPsig : (pip : PolyIntPoly) -> (p : PolyFunc) ->
  (sl : PolyNatTrans p (fst pip ** fst (snd pip))) ->
  PolyFunc
InterpPIPsig pip p sl = p

-- The base change which constitutes the right adjoint of the dependent sum
-- ("sigma") which itself constitutes the last composite in the interpretation
-- of a `PolyIntPoly`.
public export
InterpPIPsigAdj : PolyIntPoly -> PolyFunc -> PolyFunc
InterpPIPsigAdj (posp ** posd ** dirp ** dird ** ondir) (ppos ** pdir) =
  ((posp, ppos) ** \i => Either (posd $ fst i) (pdir $ snd i))

public export
InterpPIPsigbcLAdjunct : (pip : PolyIntPoly) -> (p, q : PolyFunc) ->
  (sl : PolyNatTrans p (fst pip ** fst (snd pip))) ->
  PolyNatTrans (InterpPIPsig pip p sl) q ->
  PolyNatTrans p (InterpPIPsigAdj pip q)
InterpPIPsigbcLAdjunct
  (posp ** posd ** dirp ** dird ** ondir)
  (ppos ** pdir) (qpos ** qdir) (slonpos ** slondir) (monpos ** mondir) =
    (\i => (slonpos i, monpos i) **
     \i => eitherElim (slondir i) (mondir i))

public export
InterpPIPsigbcRAdjunct : (pip : PolyIntPoly) -> (p, q : PolyFunc) ->
  (sl : PolyNatTrans p (fst pip ** fst (snd pip))) ->
  PolyNatTrans p (InterpPIPsigAdj pip q) ->
  PolyNatTrans (InterpPIPsig pip p sl) q
InterpPIPsigbcRAdjunct
  (posp ** posd ** dirp ** dird ** ondir)
  (ppos ** pdir) (qpos ** qdir) (slonpos ** slondir) (monpos ** mondir) =
    (snd . monpos ** \i => mondir i . Right)

public export
PFt1Pos : Type
PFt1Pos = Type

public export
PFetPos : PFt1Pos -> Type
PFetPos i1 = SliceObj i1

public export
PFetDir : (t1p : PFt1Pos) -> PFetPos t1p -> Type
PFetDir t1p etp = (i1 : t1p) -> SliceObj (etp i1)

public export
PFt1Dir : (t1p : PFt1Pos) -> (etp : PFetPos t1p) -> PFetDir t1p etp -> Type
PFt1Dir t1p etp etd = (i1 : t1p) -> (i2 : etp i1) -> SliceObj (etd i1 i2)

public export
PFeffNTdomPos : (t1p : PFt1Pos) -> PFetPos t1p -> Type
PFeffNTdomPos t1p = Sigma {a=t1p}

public export
PFeffNTdomDir : (t1p : PFt1Pos) -> (etp : PFetPos t1p) ->
  (etd : PFetDir t1p etp) -> PFeffNTdomPos t1p etp -> Type
PFeffNTdomDir t1p etp = DPair.uncurry

public export
PFeffNTdom :
  (t1p : PFt1Pos) -> (etp : PFetPos t1p) -> PFetDir t1p etp ->
  PolyFunc
PFeffNTdom t1p etp etd = (PFeffNTdomPos t1p etp ** PFeffNTdomDir t1p etp etd)

public export
PFeffNTcodPos : PFt1Pos -> Type
PFeffNTcodPos = id

public export
PFeffNTcodDir : (t1p : PFt1Pos) -> (etp : PFetPos t1p) ->
  (etd : PFetDir t1p etp) -> PFt1Dir t1p etp etd ->
  PFeffNTcodPos t1p -> Type
PFeffNTcodDir t1p etp etd t1d i1 =
  (i2 : etp i1) -> (d2 : etd i1 i2 ** t1d i1 i2 d2)

public export
PFeffNTcod : (t1p : PFt1Pos) -> (etp : PFetPos t1p) ->
  (etd : PFetDir t1p etp) -> PFt1Dir t1p etp etd ->
  PolyFunc
PFeffNTcod t1p etp etd t1d =
  (PFeffNTcodPos t1p ** PFeffNTcodDir t1p etp etd t1d)

public export
PFeffNTonpos : (t1p : PFt1Pos) -> (etp : PFetPos t1p) ->
  PFeffNTdomPos t1p etp -> PFeffNTcodPos t1p
PFeffNTonpos t1p etp = DPair.fst

public export
PFeffNTondir : (t1p : PFt1Pos) -> (etp : PFetPos t1p) ->
  (etd : PFetDir t1p etp) -> (t1d : PFt1Dir t1p etp etd) ->
  (i1 : PFeffNTdomPos t1p etp) ->
  PFeffNTcodDir t1p etp etd t1d (PFeffNTonpos t1p etp i1) ->
  PFeffNTdomDir t1p etp etd i1
PFeffNTondir t1p etp etd t1d i2 d1 = DPair.fst $ d1 $ DPair.snd i2

public export
PFeffNT : (t1p : PFt1Pos) -> (etp : PFetPos t1p) ->
  (etd : PFetDir t1p etp) -> (t1d : PFt1Dir t1p etp etd) ->
  PolyNatTrans
    (PFeffNTdom t1p etp etd)
    (PFeffNTcod t1p etp etd t1d)
PFeffNT t1p etp etd t1d =
  (PFeffNTonpos t1p etp ** PFeffNTondir t1p etp etd t1d)

--------------------------
--------------------------
---- Slices of `Poly` ----
--------------------------
--------------------------

----------------------------------
---- Identity and composition ----
----------------------------------

public export
polySliceIdObj : PolyFunc -> PolyFunc
polySliceIdObj b = (pfPos b ** \_ => Unit)

public export
polySliceIdProj : (b : PolyFunc) -> PolyNatTrans (polySliceIdObj b) b
polySliceIdProj b = (id ** \_, _ => ())

public export
polySliceCompTot : {b : PolyFunc} -> {q, p : PolyFunc} ->
  PolyNatTrans q b -> PolyNatTrans p b -> PolyFunc
polySliceCompTot {b} {q} {p} qsl psl =
  ((i : pfCompositionPos q p **
    (qd : pfDir {p=q} (fst i)) ->
    pntOnPos qsl (fst i) = pntOnPos psl (snd i qd)) **
   \i => pfCompositionDir q p (fst i))

public export
polySliceCompProj : {b : PolyFunc} -> {q, p : PolyFunc} ->
  (qsl : PolyNatTrans q b) -> (psl : PolyNatTrans p b) ->
  PolyNatTrans (polySliceCompTot {b} {q} {p} qsl psl) b
polySliceCompProj {b} {q} {p} qsl psl =
  (\i => pntOnPos qsl (fst $ fst i) **
   \i, bd =>
    (pntOnDir qsl (fst $ fst i) bd **
     pntOnDir psl (snd (fst i) $
      pntOnDir qsl (fst $ fst i) bd) $
      replace {p=(pfDir {p=b})} (snd i (pntOnDir qsl (fst $ fst i) bd)) bd))

-----------------------------------------------
---- As refinements of polynomial functors ----
-----------------------------------------------

-- We now show how a slice over a polynomial functor may be viewed
-- as a refined polynomial functor.

public export
PolyRefinement : PolyFunc -> PolyFunc -> Type
PolyRefinement b p = (i : pfPos p) -> InterpPolyFunc b (pfDir {p} i)

public export
pfRefElPos : {b, p : PolyFunc} -> (pr : PolyRefinement b p) ->
  pfPos p -> pfPos b
pfRefElPos {b} {p} pr pi = fst $ pr pi

public export
pfRefElDir : {b, p : PolyFunc} -> (pr : PolyRefinement b p) ->
  (pi : pfPos p) -> pfDir {p=b} (pfRefElPos {b} {p} pr pi) -> pfDir {p} pi
pfRefElDir {b} {p} pr pi = snd $ pr pi

public export
pfRefEl : {b, p : PolyFunc} -> (pr : PolyRefinement b p) ->
  (pi : pfPos p) -> InterpPolyFunc b (pfDir {p} pi)
pfRefEl {b} {p} pr pi = pr pi

---------------------------------------------------
---- As copresheaves on categories of elements ----
---------------------------------------------------

-- The category of elements of a polynomial functor is a coproduct
-- category (indexed by the positions) of coslice categories (under
-- the corresponding directions).

public export
PolyCatElemObj : PolyFunc -> Type
PolyCatElemObj p = (x : Type ** InterpPolyFunc p x)

public export
PolyCatElemMor : {p : PolyFunc} -> IntMorSig (PolyCatElemObj p)
PolyCatElemMor {p} elx ely =
  (mxy : fst elx -> fst ely **
   InterpPFMap p {a=(fst elx)} {b=(fst ely)} mxy (snd elx) = snd ely)

public export
PolyCatElemCopr : PolyFunc -> Type
PolyCatElemCopr p = (pos : Type ** pos -> PolyCatElemObj p)

public export
PolyCatElemCoprMap : {p : PolyFunc} -> IntMorSig (PolyCatElemCopr p)
PolyCatElemCoprMap {p} f g =
  (onpos : fst f -> fst g **
   (i : fst f) -> PolyCatElemMor (snd g $ onpos i) (snd f i))

public export
PolyCatElemPreshf : PolyFunc -> Type
PolyCatElemPreshf = PolyCatElemCopr

public export
PolyCatElemPreshfMap : {p : PolyFunc} -> IntMorSig (PolyCatElemCopr p)
PolyCatElemPreshfMap {p} f g =
  (onpos : fst f -> fst g **
   (i : fst f) -> PolyCatElemMor (snd f i) (snd g $ onpos i))

public export
PolyCatElemRepCopr : {p : PolyFunc} ->
  (x : Type) -> InterpPolyFunc p x -> PolyCatElemCopr p
PolyCatElemRepCopr {p} x elb = (Unit ** \_ => (x ** elb))

public export
PolyCatElemCoprToSliceTot : {p : PolyFunc} ->
  PolyCatElemCopr p -> PolyFunc
PolyCatElemCoprToSliceTot {p} f = (DPair.fst f ** \i => fst $ snd f i)

public export
PolyCatElemCoprToSliceProj : {p : PolyFunc} ->
  (pc : PolyCatElemCopr p) -> PolyNatTrans (PolyCatElemCoprToSliceTot {p} pc) p
PolyCatElemCoprToSliceProj {p} f =
  (\i => DPair.fst $ DPair.snd $ DPair.snd f i **
   \i => DPair.snd $ DPair.snd $ DPair.snd f i)

public export
PolyCatElemCoprToSliceObj : {p : PolyFunc} ->
  PolyCatElemCopr p -> CPFSliceObj p
PolyCatElemCoprToSliceObj {p} f =
  (PolyCatElemCoprToSliceTot {p} f ** PolyCatElemCoprToSliceProj {p} f)

public export
PolyCatElemCoprFromSliceObj : {p : PolyFunc} ->
  CPFSliceObj p -> PolyCatElemCopr p
PolyCatElemCoprFromSliceObj {p} f =
  (DPair.fst (DPair.fst f) **
   \i =>
    (DPair.snd (DPair.fst f) i **
     DPair.fst (DPair.snd f) i **
     \d => DPair.snd (DPair.snd f) i d))

public export
PolyCatElemCoprToSliceToCoprIdL :
  {p : PolyFunc} -> (f : PolyCatElemCopr p) ->
  PolyCatElemCoprMap {p}
    (PolyCatElemCoprFromSliceObj {p} (PolyCatElemCoprToSliceObj {p} f))
    f
PolyCatElemCoprToSliceToCoprIdL {p} el = (id ** \i => (id ** Refl))

public export
PolyCatElemCoprToSliceToCoprIdR :
  {p : PolyFunc} -> (f : PolyCatElemCopr p) ->
  PolyCatElemCoprMap {p}
    f
    (PolyCatElemCoprFromSliceObj {p} (PolyCatElemCoprToSliceObj {p} f))
PolyCatElemCoprToSliceToCoprIdR {p} el =
  (id ** \ex => (id ** sym dpEqPat))

public export
PolyCatSliceToElemCoprToSliceIdL :
  {p : PolyFunc} -> (f : CPFSliceObj p) ->
  CPFSliceMorph p
    (PolyCatElemCoprToSliceObj {p} (PolyCatElemCoprFromSliceObj {p} f))
    f
PolyCatSliceToElemCoprToSliceIdL {p} el =
  Element0
    (id ** \ex => id)
    (Evidence0
      (\ex => Refl)
      (\ex, d => Refl))

public export
PolyCatSliceToElemCoprToSliceIdR :
  {p : PolyFunc} -> (f : CPFSliceObj p) ->
  CPFSliceMorph p
    f
    (PolyCatElemCoprToSliceObj {p} (PolyCatElemCoprFromSliceObj {p} f))
PolyCatSliceToElemCoprToSliceIdR {p} el =
  Element0
    (id ** \ex => id)
    (Evidence0
      (\ex => Refl)
      (\ex, d => Refl))

public export
PolyCatElemCoprMapToNT : {p : PolyFunc} -> (q, r : PolyCatElemCopr p) ->
  PolyCatElemCoprMap {p} q r ->
  CPFSliceMorph p
    (PolyCatElemCoprToSliceObj {p} q)
    (PolyCatElemCoprToSliceObj {p} r)
PolyCatElemCoprMapToNT {p} q r m =
  Element0
    (\qi => fst m qi **
     \qi, rd => DPair.fst (snd m qi) rd)
    (Evidence0
      (\qi => sym $ cong DPair.fst (DPair.snd (snd m qi)))
      (\qi, pd =>
        fconghet
          (dpeq2 (DPair.snd (snd m qi)))
          (rewrite cong DPair.fst (DPair.snd (snd m qi)) in Refl)))

public export
PolyCatElemCoprMapFromNT : FunExt ->
  {p : PolyFunc} -> (q, r : PolyCatElemCopr p) ->
  CPFSliceMorph p
    (PolyCatElemCoprToSliceObj {p} q)
    (PolyCatElemCoprToSliceObj {p} r) ->
  PolyCatElemCoprMap {p} q r
PolyCatElemCoprMapFromNT fext {p} q r el =
    (\qi => (fst (fst0 el) qi) **
     \qi =>
      (snd (fst0 el) qi **
       rewrite sym (fst0 (snd0 el) qi) in
       trans
        (dpEq12 Refl $ funExt $ snd0 (snd0 el) qi)
        (sym $ dpEqPat {dp=(snd $ snd q qi)})))

public export
0 NTtoPolyCatElemCoprMap : FunExt ->
  {p : PolyFunc} -> (q, r : CPFSliceObj p) ->
  CPFSliceMorph p q r ->
  PolyCatElemCoprMap {p}
    (PolyCatElemCoprFromSliceObj {p} q)
    (PolyCatElemCoprFromSliceObj {p} r)
NTtoPolyCatElemCoprMap {p} fext q r m =
  (fst (fst0 m) **
   \qi =>
    (snd (fst0 m) qi **
     rewrite sym $ fst0 (snd0 m) qi in
     dpEq12
      Refl
      (funExt $ \pd => snd0 (snd0 m) qi pd)))

public export
NTfromPolyCatElemCoprMap : {p : PolyFunc} -> (q, r : CPFSliceObj p) ->
  PolyCatElemCoprMap {p}
    (PolyCatElemCoprFromSliceObj {p} q)
    (PolyCatElemCoprFromSliceObj {p} r) ->
  CPFSliceMorph p q r
NTfromPolyCatElemCoprMap {p} q r m =
  Element0
    (fst m ** \qi => fst (snd m qi))
    (Evidence0
      (\qi =>
        sym $ dpeq1 $ snd (snd m qi))
      (\qi, pd =>
        fconghet
          (dpeq2 $ snd $ snd m qi)
          (rewrite sym $ dpeq1 $ snd $ snd m qi in Refl)))

-- Interpret a coproduct of representable copresheaves on a category
-- of elements of a polynomial functor (i.e. a polynomial functor on
-- the category of elements of a polynomial functor).
public export
InterpPolyCatElemCopr : {b : PolyFunc} -> PolyCatElemCopr b ->
  (x : Type) -> SliceObj (InterpPolyFunc b x)
InterpPolyCatElemCopr {b} p x elb =
  (i : fst p ** PolyCatElemMor {p=b} (snd p i) (x ** elb))

public export
InterpPolyCatElemCoprMap : FunExt ->
  {b : PolyFunc} -> (p : PolyCatElemCopr b) ->
  (x, y : Type) -> (elx : InterpPolyFunc b x) -> (mxy : x -> y) ->
  InterpPolyCatElemCopr {b} p x elx ->
  InterpPolyCatElemCopr {b} p y (InterpPFMap b mxy elx)
InterpPolyCatElemCoprMap fext {b} p x y (bi ** bdx) mxy (pi ** pdx ** comm) =
  (pi **
   mxy . pdx **
   case dpeq1 comm of
    Refl => dpEq12 Refl (funExt $ \bd => cong mxy $ fcong (dpeq2 comm) {x=bd}))

public export
InterpPolyCatElemCoprNT : FunExt ->
  {b : PolyFunc} -> (p, q : PolyCatElemCopr b) ->
  PolyCatElemCoprMap {p=b} p q ->
  (x : Type) -> (elx : InterpPolyFunc b x) ->
  InterpPolyCatElemCopr {b} p x elx ->
  InterpPolyCatElemCopr {b} q x elx
InterpPolyCatElemCoprNT fext {b} p q (onpos ** ondir) x
  (bi ** bdx) (pi ** pdx ** comm) =
    (onpos pi **
     pdx . fst (ondir pi) **
     let
      comm1 = dpeq1 comm
      comm2 = dpeq2 comm
      dcomm = trans (snd (ondir pi)) dpEqPat
      dcomm1 = dpeq1 dcomm
      dcomm2 = dpeq2 dcomm
     in
     case comm1 of
      Refl =>
        rewrite dcomm1 in
        dpEq12
          Refl
          (trans
            (funExt $
              \bd => cong pdx $ ?InterpPolyCatElemCoprNT_dcomm2_hole)
            comm2))

-- Interpret a coproduct of representable presheaves on a category
-- of elements of a polynomial functor (i.e. a polynomial functor on
-- the _opposite_ of the category of elements of a polynomial functor).
public export
InterpPolyCatElemPreshf : {b : PolyFunc} -> PolyCatElemPreshf b ->
  (x : Type) -> SliceObj (InterpPolyFunc b x)
InterpPolyCatElemPreshf {b} p x elb =
  (i : fst p ** PolyCatElemMor {p=b} (x ** elb) (snd p i))

public export
InterpPolyCatElemPreshfMap : FunExt ->
  {b : PolyFunc} -> (p : PolyCatElemPreshf b) ->
  (x, y : Type) -> (ely : InterpPolyFunc b y) -> (myx : y -> x) ->
  InterpPolyCatElemPreshf {b} p x (InterpPFMap b myx ely) ->
  InterpPolyCatElemPreshf {b} p y ely
InterpPolyCatElemPreshfMap fext {b} p x y (bi ** bdx) myx (pi ** xpd ** comm) =
  (pi ** xpd . myx ** comm)

public export
InterpPolyCatElemPreshfNT : FunExt ->
  {b : PolyFunc} -> (p, q : PolyCatElemPreshf b) ->
  PolyCatElemPreshfMap {p=b} p q ->
  (x : Type) -> (elx : InterpPolyFunc b x) ->
  InterpPolyCatElemPreshf {b} p x elx ->
  InterpPolyCatElemPreshf {b} q x elx
InterpPolyCatElemPreshfNT fext {b} p q (onpos ** ondir) x
  (bi ** bdx) (pi ** xpd ** comm) =
    (onpos pi **
     fst (ondir pi) . xpd **
     let
      comm1 = dpeq1 comm
      comm2 = dpeq2 comm
      deq = snd (ondir pi)
      deq1 = dpeq1 deq
      deq2 = dpeq2 deq
     in
     case comm1 of
      Refl =>
        trans
          (dpEq12
            deq1
            (rewrite deq1 in ?InterpPolyCatElemPreshfNT_hole_comm2_deq2))
          (sym $ dpEqPat {dp=(snd (snd q (onpos pi)))}))

-- This predicate states that the component of `alpha` at `x`
-- applied to `elp` equals `elb`.
public export
InterpPolySliceCond : (b, p : PolyFunc) -> PolyNatTrans p b ->
  (x : Type) -> InterpPolyFunc b x -> InterpPolyFunc p x -> Type
InterpPolySliceCond b p alpha x elb elp =
  (onposeq : pntOnPos alpha (fst elp) = fst elb **
   {- ondireq : -} (bd : pfDir {p=b} (fst elb)) ->
    snd elb
      bd =
    snd elp (pntOnDir alpha (fst elp)
      (replace {p=(pfDir {p=b})} (sym onposeq) bd)))

-- Interpret a slice of `Poly` as a copresheaf over a category of elements.
-- This takes an object of the category of elements of `b` to its preimage
-- under the `alpha`, the natural transformation which comprises the projection
-- of the slice object `p` over `b`.
public export
InterpPolySlice : (b, p : PolyFunc) -> PolyNatTrans p b ->
  (x : Type) -> SliceObj (InterpPolyFunc b x)
InterpPolySlice b p alpha x elb =
  DPair (InterpPolyFunc p x) (InterpPolySliceCond b p alpha x elb)

public export
InterpPolySliceToCatElemCopr : FunExt ->
  {b, p : PolyFunc} -> (psl : PolyNatTrans p b) ->
  (x : Type) -> (elb : InterpPolyFunc b x) ->
  InterpPolySlice b p psl x elb ->
  InterpPolyCatElemCopr {b}
    (PolyCatElemCoprFromSliceObj {p=b} (p ** psl)) x elb
InterpPolySliceToCatElemCopr fext {b} {p} psl x elb elp =
  (fst (fst elp) ** snd (fst elp) **
   rewrite fst (snd elp) in
   trans
    (dpEq12 Refl (funExt $ \bd => sym $ snd (snd elp) bd))
    (sym $ dpEqPat {dp=elb}))

public export
InterpPolySliceFromCatElemCopr :
  {b, p : PolyFunc} -> (psl : PolyNatTrans p b) ->
  (x : Type) -> (elb : InterpPolyFunc b x) ->
  InterpPolyCatElemCopr {b}
    (PolyCatElemCoprFromSliceObj {p=b} (p ** psl)) x elb ->
  InterpPolySlice b p psl x elb
InterpPolySliceFromCatElemCopr {b} {p} psl x elb elp =
  ((fst elp ** fst $ snd elp) **
   rewrite sym $ snd $ snd elp in (Refl ** \bd => Refl))

public export
InterpPolyCatElemCoprToSlice :
  {b : PolyFunc} -> (pc : PolyCatElemCopr b) ->
  (x : Type) -> (elb : InterpPolyFunc b x) ->
  InterpPolyCatElemCopr {b} pc x elb ->
  InterpPolySlice b
    (fst $ PolyCatElemCoprToSliceObj {p=b} pc)
    (snd $ PolyCatElemCoprToSliceObj {p=b} pc)
    x
    elb
InterpPolyCatElemCoprToSlice {b} pc x elb elc =
  ((fst elc ** fst (snd elc)) **
   rewrite sym $ snd (snd elc) in (Refl ** \bd => Refl))

public export
InterpPolyCatElemCoprFromSlice : FunExt ->
  {b : PolyFunc} -> (pc : PolyCatElemCopr b) ->
  (x : Type) -> (elb : InterpPolyFunc b x) ->
  InterpPolySlice b
    (fst $ PolyCatElemCoprToSliceObj {p=b} pc)
    (snd $ PolyCatElemCoprToSliceObj {p=b} pc)
    x
    elb ->
  InterpPolyCatElemCopr {b} pc x elb
InterpPolyCatElemCoprFromSlice fext {b} pc x elb elc =
  (fst (fst elc) ** snd (fst elc) **
   rewrite fst (snd elc) in
   trans
    (dpEq12 Refl (funExt $ \bd => sym $ snd (snd elc) bd))
    (sym $ dpEqPat {dp=elb}))

-- Interpret a slice of `Poly` when viewed as a copresheaf over a category
-- of elements is a subset of the interpretation of the total space.  Thus
-- there is an injection from the interpretation of the sliice into the
-- interpretation of the total space.
public export
InterpPolySliceInj : (b, p : PolyFunc) -> (alpha : PolyNatTrans p b) ->
  (x : Type) -> (elb : InterpPolyFunc b x) ->
  InterpPolySlice b p alpha x elb -> InterpPolyFunc p x
InterpPolySliceInj b p alpha x elb = DPair.fst

-- Interpret a slice morphism of `Poly` as a natural transformation
-- between copresheaves on categories of elements.
public export
InterpPolySliceMorNT : {p, q, r : PolyFunc} ->
  (qsl : PolyNatTrans q p) -> (rsl : PolyNatTrans r p) ->
  (m : PolyNatTrans q r) -> PNTisSliceM {p} {q} {r} qsl rsl m ->
  (x : Type) -> (elb : InterpPolyFunc p x) ->
  InterpPolySlice p q qsl x elb ->
  InterpPolySlice p r rsl x elb
InterpPolySliceMorNT {p} {q} {r} qsl rsl (monpos ** mondir) (onposeq ** ondireq)
  x elb elsl =
    ((monpos (fst (fst elsl)) ** snd (fst elsl) . mondir (fst (fst elsl))) **
     trans (onposeq $ fst (fst elsl)) (fst (snd elsl)) **
     \pd =>
      trans
        (snd (snd elsl) pd)
        (cong (snd (fst elsl))
          (sym $ ondireq (fst (fst elsl))
           $ rewrite (trans (onposeq $ fst (fst elsl)) (fst (snd elsl))) in
           pd)))

--------------------------------------------------
---- Slices of polynomial functors as W-types ----
--------------------------------------------------

-- The position-type of a coproduct of representable copresheaves on
-- the category of elements of a polynomial functor, together with the
-- on-positions function of the projection, may be viewed as selecting
-- a type dependent on the position-type of the base.
public export
PCECW : PolyFunc -> Type
PCECW b =
  (pos : SliceObj (pfPos b) **
   cotot : (bi : pfPos b) -> SliceObj (pos bi) **
   {- coproj : -}
   (bi : pfPos b) -> (pi : pos bi) -> pfDir {p=b} bi -> cotot bi pi)

public export
PCECWmap : (b : PolyFunc) -> IntMorSig (PCECW b)
PCECWmap b q r =
  (onpos : (bi : pfPos b) -> fst q bi -> fst r bi **
   ontot : (bi : pfPos b) -> (qi : fst q bi) ->
    fst (snd r) bi (onpos bi qi) -> fst (snd q) bi qi **
   {- comm : -} (bi : pfPos b) -> (qi : fst q bi) ->
    ExtEq {a=(pfDir {p=b} bi)} {b=(fst (snd q) bi qi)}
      (ontot bi qi . snd (snd r) bi (onpos bi qi)) (snd (snd q) bi qi))

public export
PCECfromW : (b : PolyFunc) -> PCECW b -> PolyCatElemCopr b
PCECfromW b pc =
  ((bi : pfPos b ** fst pc bi) **
   \pci =>
    (fst (snd pc) (fst pci) (snd pci) **
     (fst pci) **
     snd (snd pc) (fst pci) (snd pci)))

public export
PCECtoW : (b : PolyFunc) -> PolyCatElemCopr b -> PCECW b
PCECtoW b pc =
  (\bi =>
    (pi : fst pc ** fst (snd $ snd pc pi) = bi) **
   \bi, pieq =>
    fst $ snd pc (fst pieq) **
   \bi, pieq, bd =>
    snd (snd $ snd pc $ fst pieq) $
      replace {p=(pfDir {p=b})} (sym $ snd pieq) bd)

public export
PCECfromWmap : FunExt -> {b : PolyFunc} -> (q, r : PCECW b) ->
  PCECWmap b q r -> PolyCatElemCoprMap {p=b} (PCECfromW b q) (PCECfromW b r)
PCECfromWmap fext {b} q r m =
  (dpMapSnd (fst m) **
   \bqi =>
    (fst (snd m) (fst bqi) (snd bqi) **
     dpEq12 Refl (funExt $ snd (snd m) (fst bqi) (snd bqi))))

public export
PCECtoWmap : {b : PolyFunc} -> (q, r : PCECW b) ->
  PolyCatElemCoprMap {p=b} (PCECfromW b q) (PCECfromW b r) ->
  PCECWmap b q r
PCECtoWmap {b=(bpos ** bdir)}
  (qpos ** qcotot ** qproj) (rpos ** rcotot ** rproj) (monpos ** mondir) =
    (\bi, qi =>
      rewrite sym $ dpeq1 $ snd (mondir (bi ** qi)) in
      snd (monpos (bi ** qi)) **
     \bi, qi, rct =>
      fst (mondir (bi ** qi)) $
        rewrite dpeq1 $ snd (mondir (bi ** qi)) in rct **
     \bi, qi, bd =>
      let bieq = dpeq1 $ snd (mondir (bi ** qi)) in
      rewrite
        sym $
          fconghet
            {ea=(rewrite bieq in bd)}
            {ea'=bd}
            (dpeq2 $ snd (mondir (bi ** qi)))
            (rewrite bieq in Refl)
      in
      rewrite bieq in
      Refl)

public export
PCECWfromPCECmap : {b : PolyFunc} -> (q, r : PolyCatElemCopr b) ->
  PolyCatElemCoprMap {p=b} q r ->
  PCECWmap b (PCECtoW b q) (PCECtoW b r)
PCECWfromPCECmap {b=(bpos ** bdir)}
  (qpos ** qdir) (rpos ** rdir) (monpos ** mondir) =
    (\bi, (qi ** qieq) =>
      (monpos qi ** trans (rewrite sym $ snd (mondir qi) in Refl) qieq) **
     \bi, (qi ** qieq), rd => fst (mondir qi) rd **
     \bi, (qi ** qieq), bd => rewrite sym $ snd (mondir qi) in Refl)

public export
PCECWtoPCECmap : FunExt -> {b : PolyFunc} -> (q, r : PolyCatElemCopr b) ->
  PCECWmap b (PCECtoW b q) (PCECtoW b r) ->
  PolyCatElemCoprMap {p=b} q r
PCECWtoPCECmap fext {b=(bpos ** bdir)}
  (qpos ** qdir) (rpos ** rdir) (monpos ** montot ** mcomm) =
    (\qi =>
      fst $ monpos (fst $ snd $ qdir qi) (qi ** Refl) **
     \qi =>
      (\rd => montot (fst $ snd $ qdir qi) (qi ** Refl) rd **
       rewrite dpEqPat {dp=(snd $ qdir qi)} in
       rewrite snd $ monpos (fst $ snd $ qdir qi) (qi ** Refl) in
       dpEq12 Refl (funExt $ mcomm (fst $ snd $ qdir qi) (qi ** Refl))))

-- Yet another view of a polynomial functor on a category of elements of
-- a polynomial functor, also known as a slice of a polynomial functor,
-- is as a collection, indexed by the position-type of the base functor,
-- of slices of the covariant hom-functors of the directions of the base
-- functor.
public export
CoprCovHomSlice : PolyFunc -> Type
CoprCovHomSlice b = (i : pfPos b) -> CovHomSlice (pfDir {p=b} i)

public export
CoprCovHomSliceMap : (b : PolyFunc) -> IntMorSig (CoprCovHomSlice b)
CoprCovHomSliceMap b q r =
  (i : pfPos b) -> CovHomSliceMor {a=(pfDir {p=b} i)} (q i) (r i)

public export
PCECWtoCHS : (b : PolyFunc) -> PCECW b -> CoprCovHomSlice b
PCECWtoCHS b pc bi = (fst pc bi ** fst (snd pc) bi ** snd (snd pc) bi)

public export
PCECWfromCHS : (b : PolyFunc) -> CoprCovHomSlice b -> PCECW b
PCECWfromCHS b pc =
  (\bi => fst (pc bi) ** \bi => fst (snd $ pc bi) ** \bi => snd (snd $ pc bi))

public export
PCECWtoCHSmor : {b : PolyFunc} -> (q, r : PCECW b) ->
  PCECWmap b q r -> CoprCovHomSliceMap b (PCECWtoCHS b q) (PCECWtoCHS b r)
PCECWtoCHSmor {b} q r m bi = (fst m bi ** fst (snd m) bi ** snd (snd m) bi)

public export
PCECWfromCHSmor : {b : PolyFunc} -> (q, r : PCECW b) ->
  CoprCovHomSliceMap b (PCECWtoCHS b q) (PCECWtoCHS b r) -> PCECWmap b q r
PCECWfromCHSmor {b} q r m =
  (\bi => fst (m bi) ** \bi => fst (snd $ m bi) ** \bi => snd (snd $ m bi))

public export
CHStoPCECWmap : {b : PolyFunc} -> (q, r : CoprCovHomSlice b) ->
  CoprCovHomSliceMap b q r -> PCECWmap b (PCECWfromCHS b q) (PCECWfromCHS b r)
CHStoPCECWmap {b} q r m =
  (\bi => fst (m bi) ** \bi => fst (snd $ m bi) ** \bi => snd (snd $ m bi))

public export
CHSfromPCECWmap : {b : PolyFunc} -> (q, r : CoprCovHomSlice b) ->
  PCECWmap b (PCECWfromCHS b q) (PCECWfromCHS b r) -> CoprCovHomSliceMap b q r
CHSfromPCECWmap {b} q r m bi = (fst m bi ** fst (snd m) bi ** snd (snd m) bi)

--------------------------------------------------------------
---- Representable copresheaves on categories of elements ----
--------------------------------------------------------------

-- Interpret a representable copresheaf on a category of elements.
public export
PFinterpElemRep : (b : PolyFunc) -> (x : Type) -> (el : InterpPolyFunc b x) ->
  (y : Type) -> InterpPolyFunc b y -> Type
PFinterpElemRep b x elbx y elby =
  (mxy : x -> y **
   ieq : fst elbx = fst elby **
   ExtEq {a=(snd b (fst elbx))} {b=y}
    (mxy . snd elbx)
    (rewrite ieq in snd elby))

-- Since a polynomial-slice category is equivalent to a copresheaf
-- category on a category of elements, we can in particular treat
-- a representable copresheaf on the category of elements of a
-- polynomial functor as a slice over that functor.
public export
PFelemRepSliceTot : (b : PolyFunc) ->
  (x : Type) -> (el : InterpPolyFunc b x) ->
  PolyFunc
PFelemRepSliceTot b x el = (Unit ** \_ => x)

public export
PFelemRepSliceProj : (b : PolyFunc) ->
  (x : Type) -> (el : InterpPolyFunc b x) ->
  PolyNatTrans (PFelemRepSliceTot b x el) b
PFelemRepSliceProj b x el = (\_ => fst el ** \_, bd => snd el bd)

public export
PFelemRepSliceObj : (b : PolyFunc) ->
  (x : Type) -> (el : InterpPolyFunc b x) ->
  CPFSliceObj b
PFelemRepSliceObj b x el =
  (PFelemRepSliceTot b x el ** PFelemRepSliceProj b x el)

public export
PFelemRepToSliceToElem : (b : PolyFunc) ->
  (x : Type) -> (elx : InterpPolyFunc b x) ->
  (y : Type) -> (ely : InterpPolyFunc b y) ->
  InterpPolySlice b (PFelemRepSliceTot b x elx) (PFelemRepSliceProj b x elx)
    y ely ->
  PFinterpElemRep b x elx y ely
PFelemRepToSliceToElem b x elx y ely elsl =
  (snd (fst elsl) **
   (fst (snd elsl)) **
   \bdx => sym $ (snd (snd elsl)) $ rewrite sym (fst (snd elsl)) in bdx)

public export
PFelemRepToSliceFromElem : (b : PolyFunc) ->
  (x : Type) -> (elx : InterpPolyFunc b x) ->
  (y : Type) -> (ely : InterpPolyFunc b y) ->
  PFinterpElemRep b x elx y ely ->
  InterpPolySlice b (PFelemRepSliceTot b x elx) (PFelemRepSliceProj b x elx)
    y ely
PFelemRepToSliceFromElem b x elx y ely elr =
  ((() ** (fst elr)) **
   (fst (snd elr)) **
   \bdy => sym $ (snd (snd elr)) (rewrite (fst (snd elr)) in bdy))

public export
polyCatElemTerminal : (b : PolyFunc) -> PolyCatElemCopr b
polyCatElemTerminal b =
  PolyCatElemCoprFromSliceObj {p=b} (b ** id ** \_ => id)

public export
polyCatElemTerminalFormula : (b : PolyFunc) ->
  polyCatElemTerminal b =
  (pfPos b ** \i : pfPos b => (pfDir {p=b} i ** i ** Prelude.id))
polyCatElemTerminalFormula b = Refl

public export
polyCatElemToTerminal : (b : PolyFunc) -> (p : PolyCatElemCopr b) ->
  PolyCatElemCoprMap {p=b} p (polyCatElemTerminal b)
polyCatElemToTerminal b p =
  (\pi => fst (snd $ snd p pi) **
   \pi => (snd (snd $ snd p pi) ** sym $ dpEqPat {dp=(snd $ snd p pi)}))

public export
InterpPFsliceHomDomTot : {b : PolyFunc} -> (q : PolyFunc) ->
  PolyNatTrans q b -> (x : Type) -> InterpPolyFunc b x -> PolyFunc
InterpPFsliceHomDomTot {b} q qsl x bel =
  pfPullbackAr {p=(PFelemRepSliceTot b x bel)} {q} {r=b}
    (PFelemRepSliceProj b x bel)
    qsl

public export
InterpPFsliceHomDomProj : {b : PolyFunc} -> (q : PolyFunc) ->
  (qsl : PolyNatTrans q b) -> (x : Type) -> (bel : InterpPolyFunc b x) ->
  PolyNatTrans (InterpPFsliceHomDomTot {b} q qsl x bel) b
InterpPFsliceHomDomProj {b} q qsl x bel =
  pfPullbackArSlProj {p=(PFelemRepSliceTot b x bel)} {q} {r=b}
    (PFelemRepSliceProj b x bel)
    qsl

public export
InterpPFsliceHom : {b : PolyFunc} -> (q, p : PolyFunc) ->
  PolyNatTrans q b -> (x : Type) -> InterpPolyFunc b x -> Type
InterpPFsliceHom {b} q p qsl x bel =
  PolyNatTrans (InterpPFsliceHomDomTot {b} q qsl x bel) p

public export
InterpPFsliceHomComm : {b : PolyFunc} -> (q, p : PolyFunc) ->
  (qsl : PolyNatTrans q b) -> (psl : PolyNatTrans p b) ->
  (x : Type) -> (bel : InterpPolyFunc b x) ->
  InterpPFsliceHom {b} q p qsl x bel -> Type
InterpPFsliceHomComm {b} q p qsl psl x bel =
  PNTisSliceM {p=b} {q=(InterpPFsliceHomDomTot {b} q qsl x bel)} {r=p}
    (InterpPFsliceHomDomProj {b} q qsl x bel)
    psl

public export
InterpPFrepSliceHom : {b : PolyFunc} ->
  (q : Type) -> (qel : InterpPolyFunc b q) ->
  (p : PolyFunc) -> (x : Type) -> InterpPolyFunc b x -> Type
InterpPFrepSliceHom {b} q qel p =
  InterpPFsliceHom {b}
    (PFelemRepSliceTot b q qel) p (PFelemRepSliceProj b q qel)

public export
InterpPFrepSliceHomComm : {b : PolyFunc} ->
  (q : Type) -> (qel : InterpPolyFunc b q) ->
  (p : PolyFunc) -> (psl : PolyNatTrans p b) ->
  (x : Type) -> (bel : InterpPolyFunc b x) ->
  InterpPFrepSliceHom {b} q qel p x bel -> Type
InterpPFrepSliceHomComm {b} q qel p =
  InterpPFsliceHomComm {b}
    (PFelemRepSliceTot b q qel) p (PFelemRepSliceProj b q qel)

---------------------------------------
---- Interpretation of composition ----
---------------------------------------

-- Interpret a composition of slices of `Poly` as a copresheaf
-- over a category of elements.
public export
0 InterpPolySliceComp : {b, q, p : PolyFunc} ->
  PolyNatTrans q b -> PolyNatTrans p b ->
  (a : Type) -> SliceObj (InterpPolyFunc b a)
InterpPolySliceComp {b} {q} {p} qsl psl a elb =
  (elq : InterpPolyFunc q (InterpPolySlice b p psl a elb) **
   onposeq : fst elb = pntOnPos qsl (fst elq) **
   {- ondireq : -} (bd : pfDir {p=b} (fst elb)) ->
    let
      elq2 =
        snd elq (pntOnDir qsl (fst elq) (replace {p=(pfDir {p=b})} onposeq bd))
     in
     snd elb bd =
     snd (fst elq2)
      (pntOnDir psl
        (fst $ fst elq2)
        (replace {p=(pfDir {p=b})} (sym $ fst $ snd elq2) bd)))

-- Interpret the `polySliceCompTot`/`polySliceCompProj` slice object
-- as a copresheaf over a category of elements.
public export
InterpPolySliceCompAr : {b, q, p : PolyFunc} ->
  PolyNatTrans q b -> PolyNatTrans p b ->
  (a : Type) -> SliceObj (InterpPolyFunc b a)
InterpPolySliceCompAr {b} {q} {p} qsl psl =
  InterpPolySlice
    b
    (polySliceCompTot {b} {q} {p} qsl psl)
    (polySliceCompProj {b} {q} {p} qsl psl)

-------------------------------------------
---- Local Cartesian closure of `Poly` ----
-------------------------------------------

-- Step-by-step computation of the position of the polynomial-slice hom-object.

public export
polySliceCofreeCopointedObj : (b, p : PolyFunc) -> PolyNatTrans p b -> PolyFunc
polySliceCofreeCopointedObj b p =
  pfPullbackAr {p=(polySliceIdObj b)} {q=p} {r=b} (polySliceIdProj b)

public export
polySliceCofreeCopointedProj : (b, p : PolyFunc) -> (psl : PolyNatTrans p b) ->
  PolyNatTrans (polySliceCofreeCopointedObj b p psl) b
polySliceCofreeCopointedProj b p =
  pfPullbackArSlProj {p=(polySliceIdObj b)} {q=p} {r=b} (polySliceIdProj b)

public export
polySliceCofreeCopointedProjId :
  (b, p : PolyFunc) -> (psl : PolyNatTrans p b) ->
  PolyNatTrans (polySliceCofreeCopointedObj b p psl) (polySliceIdObj b)
polySliceCofreeCopointedProjId b p =
  pfPullbackArProj1 {p=(polySliceIdObj b)} {q=p} {r=b} (polySliceIdProj b)

public export
polySliceCofreeCopointedProjIdComm :
  (b, p : PolyFunc) -> (psl : PolyNatTrans p b) ->
  PNTisSliceM
    {p=b} {q=(polySliceCofreeCopointedObj b p psl)} {r=(polySliceIdObj b)}
    (polySliceCofreeCopointedProj b p psl)
    (polySliceIdProj b)
    (polySliceCofreeCopointedProjId b p psl)
polySliceCofreeCopointedProjIdComm b p psl =
  (\_ => Refl ** \_, _ => Refl)

public export
polySliceCofreeCopointedProjBase :
  (b, p : PolyFunc) -> (psl : PolyNatTrans p b) ->
  PolyNatTrans (polySliceCofreeCopointedObj b p psl) p
polySliceCofreeCopointedProjBase b p =
  pfPullbackArProj2 {p=(polySliceIdObj b)} {q=p} {r=b} (polySliceIdProj b)

public export
polySliceCofreeCopointedProjBaseComm : FunExt ->
  (b, p : PolyFunc) -> (psl : PolyNatTrans p b) ->
  PNTisSliceM
    {p=b} {q=(polySliceCofreeCopointedObj b p psl)} {r=p}
    (polySliceCofreeCopointedProj b p psl)
    psl
    (polySliceCofreeCopointedProjBase b p psl)
polySliceCofreeCopointedProjBaseComm fext b p psl =
  (\el =>
    sym (snd el) **
   \el, bd =>
    funExt $ \x => funExt $ \ex => sym $ snd ex $ rewrite snd el in bd)

public export
polyRepSliceHomAdjLMap : {b : PolyFunc} ->
  {q : Type} -> (qel : InterpPolyFunc b q) ->
  {p, p' : PolyFunc} ->
  (psl : PolyNatTrans p b) -> (psl' : PolyNatTrans p' b) ->
  (mpp : PolyNatTrans p p') ->
  PNTisSliceM {p=b} {q=p} {r=p'} psl psl' mpp ->
  PolyNatTrans
    (pfPullbackAr
      {r=b}
      {p}
      {q=(PFelemRepSliceTot b q qel)}
      psl
      (PFelemRepSliceProj b q qel))
    (pfPullbackAr
      {r=b}
      {p=p'}
      {q=(PFelemRepSliceTot b q qel)}
      psl'
      (PFelemRepSliceProj b q qel))
polyRepSliceHomAdjLMap {b} {q} qel {p} {p'} psl psl' mpp (poscomm ** dircomm) =
  (\((pi, ()) ** icomm) =>
    ((fst mpp pi, ()) ** trans (poscomm pi) icomm) **
   \((pi, ()) ** icomm), el, x, (dmx ** dcomm) =>
    el x
      (dmx . mapFst {f=Either} (snd mpp pi) **
       \bd =>
        trans
          (cong dmx $ cong Left $ dircomm pi bd)
          (dcomm $ replace {p=(pfDir {p=b})} (poscomm pi) bd)))

public export
polyRepSliceHomAdjLMapComm : FunExt -> {b : PolyFunc} ->
  {q : Type} -> (qel : InterpPolyFunc b q) ->
  {p, p' : PolyFunc} ->
  (psl : PolyNatTrans p b) -> (psl' : PolyNatTrans p' b) ->
  (mpp : PolyNatTrans p p') ->
  (issl : PNTisSliceM {p=b} {q=p} {r=p'} psl psl' mpp) ->
  PNTisSliceM
    {p=b}
    {q=(pfPullbackAr
      {r=b}
      {p}
      {q=(PFelemRepSliceTot b q qel)}
      psl
      (PFelemRepSliceProj b q qel))}
    {r=(pfPullbackAr
      {r=b}
      {p=p'}
      {q=(PFelemRepSliceTot b q qel)}
      psl'
      (PFelemRepSliceProj b q qel))}
    (pfPullbackArSlProj
      {r=b}
      {p}
      {q=(PFelemRepSliceTot b q qel)}
      psl
      (PFelemRepSliceProj b q qel))
    (pfPullbackArSlProj
      {r=b}
      {p=p'}
      {q=(PFelemRepSliceTot b q qel)}
      psl'
      (PFelemRepSliceProj b q qel))
    (polyRepSliceHomAdjLMap {b} {q} qel {p} {p'} psl psl' mpp issl)
polyRepSliceHomAdjLMapComm fext {b} {q} qel {p} {p'} psl psl' mpp
  (poscomm ** dircomm) =
    (\((pi, ()) ** bieq) =>
      poscomm pi **
     \((pi, ()) ** bieq), bd =>
      funExt $ \x => funExt $ \(dmx ** dcomm) =>
        cong dmx $ cong Left $ dircomm pi bd)

-- Suppose `a` and `f` are objects of the category of elements of the
-- polynomial functor `b`.  Here we compute the copresheaf on the
-- category of elements of `b` which comprises the product of the
-- copresheaves represented by `a` and `f`.
public export
polyCatElemCoprRepProd : (b : PolyFunc) ->
  (a : Type) -> (ela : InterpPolyFunc b a) ->
  (f : Type) -> (elf : InterpPolyFunc b f) ->
  PolyCatElemCopr b
polyCatElemCoprRepProd b a ela f elf =
  PolyCatElemCoprFromSliceObj {p=b}
    (pfPullbackArSlObj
      {p=(PFelemRepSliceTot b a ela)}
      {q=(PFelemRepSliceTot b f elf)}
      {r=b}
      (PFelemRepSliceProj b a ela)
      (PFelemRepSliceProj b f elf))

-------------------------------------
-------------------------------------
---- `Poly`-slice hom-objects -------
-------------------------------------
-------------------------------------

-- A pullback is a product in a slice category, so the product-hom
-- adjunction in a slice category is a pullback-hom adjunction.

public export
polySliceHomObjPos : {b : PolyFunc} -> {q, p : PolyFunc} ->
  (qsl : PolyNatTrans q b) -> (psl : PolyNatTrans p b) -> Type
polySliceHomObjPos {b} {q} {p} qsl psl =
  (bi : pfPos b **
   onpos : (qi : pfPos q) -> pntOnPos qsl qi = bi -> pfPos p **
   poscomm :
    (qi : pfPos q) -> (qieq : pntOnPos qsl qi = bi) ->
    pntOnPos psl (onpos qi qieq) = bi **
   ondir :
    (qi : pfPos q) -> (qieq : pntOnPos qsl qi = bi) ->
    pfDir {p} (onpos qi qieq) -> Either Unit (pfDir {p=q} qi) **
   {- ondircomm : -}
    (qi : pfPos q) -> (qieq : pntOnPos qsl qi = bi) ->
    (bd : pfDir {p=b} bi) ->
      (ondir qi qieq (pntOnDir psl (onpos qi qieq) $
        replace {p=(pfDir {p=b})} (sym $ poscomm qi qieq) bd)) =
      (Right $ pntOnDir qsl qi (replace {p=(pfDir {p=b})} (sym qieq) bd)))

public export
polySliceHomObjDirBase : {b : PolyFunc} -> {q, p : PolyFunc} ->
  (qsl : PolyNatTrans q b) -> (psl : PolyNatTrans p b) ->
  polySliceHomObjPos {b} {q} {p} qsl psl -> Type
polySliceHomObjDirBase {b} {q} {p} qsl psl
  (bi ** qponpos ** onposcomm ** qpondir ** ondircomm) =
    Either
      (pfDir {p=b} bi)
      (qi : pfPos q **
       ieq : pntOnPos qsl qi = bi **
       pd : pfDir {p} (qponpos qi ieq) **
       qpondir qi ieq pd = Left ())

public export
polySliceHomObjDirRel : {b : PolyFunc} -> {q, p : PolyFunc} ->
  (qsl : PolyNatTrans q b) -> (psl : PolyNatTrans p b) ->
  (i : polySliceHomObjPos {b} {q} {p} qsl psl) ->
  RelationOn (polySliceHomObjDirBase {b} {q} {p} qsl psl i)
polySliceHomObjDirRel {b} {q} {p} qsl psl
  (bi ** qponpos ** onposcomm ** qpondir ** ondircomm)
  (Left bd) (Right (qi ** ieq ** pd ** isl)) =
    pntOnDir psl
      (qponpos qi ieq)
      (replace {p=(pfDir {p=b})} (sym $ onposcomm qi ieq) bd) =
    pd
polySliceHomObjDirRel {b} {q} {p} qsl psl
  (bi ** qponpos ** onposcomm ** qpondir ** ondircomm)
  _ _ =
    Void

public export
polySliceHomObjDir : {b : PolyFunc} -> {q, p : PolyFunc} ->
  (qsl : PolyNatTrans q b) -> (psl : PolyNatTrans p b) ->
  polySliceHomObjPos {b} {q} {p} qsl psl -> Type
polySliceHomObjDir {b} {q} {p} qsl psl i =
  impredCoeqRel
    (polySliceHomObjDirBase {b} {q} {p} qsl psl i)
    (polySliceHomObjDirRel {b} {q} {p} qsl psl i)

public export
polySliceHomObjTot : {b : PolyFunc} -> {q, p : PolyFunc} ->
  (qsl : PolyNatTrans q b) -> (psl : PolyNatTrans p b) ->
  PolyFunc
polySliceHomObjTot {b} {q} {p} qsl psl =
  (polySliceHomObjPos {b} {q} {p} qsl psl **
   polySliceHomObjDir {b} {q} {p} qsl psl)

public export
polySliceHomObjProjOnPos : {b : PolyFunc} -> {q, p : PolyFunc} ->
  (qsl : PolyNatTrans q b) -> (psl : PolyNatTrans p b) ->
  pfPos (polySliceHomObjTot {b} {q} {p} qsl psl) -> pfPos b
polySliceHomObjProjOnPos {b} {q} {p} qsl psl = DPair.fst

public export
polySliceHomObjProjOnDir : {b : PolyFunc} -> {q, p : PolyFunc} ->
  (qsl : PolyNatTrans q b) -> (psl : PolyNatTrans p b) ->
  (i : pfPos (polySliceHomObjTot {b} {q} {p} qsl psl)) ->
  pfDir {p=b} (polySliceHomObjProjOnPos {b} {q} {p} qsl psl i) ->
  pfDir {p=(polySliceHomObjTot {b} {q} {p} qsl psl)} i
polySliceHomObjProjOnDir {b} {q} {p} qsl psl
  (bi ** pqonpos ** onposcomm ** qpondir ** ondircomm) =
    impredCoeqInj . Left

public export
polySliceHomObjProj : {b : PolyFunc} -> {q, p : PolyFunc} ->
  (qsl : PolyNatTrans q b) -> (psl : PolyNatTrans p b) ->
  PolyNatTrans (polySliceHomObjTot {b} {q} {p} qsl psl) b
polySliceHomObjProj {b} {q} {p} qsl psl =
  (polySliceHomObjProjOnPos {b} {q} {p} qsl psl **
   polySliceHomObjProjOnDir {b} {q} {p} qsl psl)

-- Since a polynomial-slice category is equivalent to a copresheaf
-- category, we can use Yoneda reasoning to determine what its
-- hom-objects must be.
public export
PolySliceToNT : (b : PolyFunc) -> (q, p : PolyFunc) ->
  (qsl : PolyNatTrans q b) -> (psl : PolyNatTrans p b) ->
  (x : Type) -> (bel : InterpPolyFunc b x) ->
  InterpPolySlice
    b
    (polySliceHomObjTot {b} {q} {p} qsl psl)
    (polySliceHomObjProj {b} {q} {p} qsl psl)
    x
    bel ->
  InterpPFsliceHom {b} q p qsl x bel
PolySliceToNT b q p (qonpos ** qondir) (ponpos ** pondir) x
  (bi ** bdx)
  (((_ **  qponpos ** onposcomm ** ondir ** ondircomm) ** bondir) **
   Refl ** ondireq) =
    (\(qi ** ieq) =>
      qponpos (snd qi) (sym ieq) **
     \(qi ** ieq), pd, y, el =>
      fst el $ case decCase $ ondir (snd qi) (sym ieq) pd of
        Left (() ** isl) =>
          Left $ bondir $ impredCoeqInj $
            Right (snd qi ** sym ieq ** pd ** isl)
        Right (qd ** isr) =>
          Right qd)

public export
0 PolySliceToNTcomm : FunExt -> ImpredCoeqRelEqAssumption ->
  (b : PolyFunc) -> (q, p : PolyFunc) ->
  (qsl : PolyNatTrans q b) -> (psl : PolyNatTrans p b) ->
  (x : Type) -> (bel : InterpPolyFunc b x) ->
  (isl : InterpPolySlice
    b
    (polySliceHomObjTot {b} {q} {p} qsl psl)
    (polySliceHomObjProj {b} {q} {p} qsl psl)
    x
    bel) ->
  InterpPFsliceHomComm {b} q p qsl psl x bel
    (PolySliceToNT b q p qsl psl x bel isl)
PolySliceToNTcomm fext coeqr b q p (qonpos ** qondir) (ponpos ** pondir) x
  (bi ** bdx)
  (((_ **  qponpos ** onposcomm ** ondir ** ondircomm) ** pdx) **
   Refl ** ondireq) =
    (\(qi ** pqieq) =>
      trans (onposcomm (snd qi) (sym pqieq)) Refl **
     \(qi ** pqieq), bd =>
      let bieq = trans (onposcomm (snd qi) (sym pqieq)) Refl in
      funExt $ \y => funExt $ \el =>
        case
          decCase
            (ondir (snd qi) (sym pqieq)
              (pondir (qponpos (snd qi) (sym pqieq)) bd))
          of
            Left (() ** isl) =>
              rewrite isl in
              rewrite ondireq (replace {p=(pfDir {p=b})} bieq bd) in
              ?PolySliceToNTcomm_hole_rewrite_uip $
              cong (fst el) $
                cong Left $
                cong pdx $ cong impredCoeqInj $ sym $
                  coeqr
                    (polySliceHomObjDirBase
                      {b} {q} {p} (qonpos ** qondir) (ponpos ** pondir)
                      (bi ** qponpos ** onposcomm ** ondir ** ondircomm))
                    (polySliceHomObjDirRel
                      {b} {q} {p} (qonpos ** qondir) (ponpos ** pondir)
                      (bi ** qponpos ** onposcomm ** ondir ** ondircomm))
                    (Left $ replace {p=(pfDir {p=b})} bieq bd)
                    (Right (snd qi ** (sym pqieq **
                      (pondir (qponpos (snd qi) (sym pqieq)) bd ** isl))))
                    Refl
            Right (qd ** isr) =>
              rewrite isr in
              rewrite
                sym $ injective $
                  trans
                    (sym $ ondircomm (snd qi) (sym pqieq)
                      (replace {p=(pfDir {p=b})} bieq bd))
                    isr
              in
              sym $ snd el $ replace {p=(pfDir {p=b})} bieq bd)

-------------------------------------------------
-------------------------------------------------
---- Polynomial functors on slices of `Poly` ----
-------------------------------------------------
-------------------------------------------------

--------------------------------
---- Pullback / base change ----
--------------------------------

-- The base change, or pullback, functor internal to `PolyFunc`.
-- A natural transformation `q -> p` induces a functor from slices
-- over `p` to slices over `q`.
public export
PolyBCFtot : {p, q : PolyFunc} -> (f : PolyNatTrans q p) ->
  (r : PolyFunc) -> (sl : PolyNatTrans r p) ->
  PolyFunc
PolyBCFtot {p} {q} f r sl = pfPullbackAr {p=r} {q} {r=p} sl f

public export
PolyBCFprojOnPos : {p, q : PolyFunc} -> (f : PolyNatTrans q p) ->
  (r : PolyFunc) -> (sl : PolyNatTrans r p) ->
  pfPos (PolyBCFtot {p} {q} f r sl) -> pfPos q
PolyBCFprojOnPos {p} {q} f r sl i = snd (fst i)

public export
PolyBCFprojOnDir : {p, q : PolyFunc} -> (f : PolyNatTrans q p) ->
  (r : PolyFunc) -> (sl : PolyNatTrans r p) ->
  (i : pfPos (PolyBCFtot {p} {q} f r sl)) ->
  pfDir {p=q} (PolyBCFprojOnPos {p} {q} f r sl i) ->
  pfDir {p=(PolyBCFtot {p} {q} f r sl)} i
PolyBCFprojOnDir {p} {q} f r sl i qd x el = fst el $ Right qd

public export
PolyBCFproj : {p, q : PolyFunc} -> (f : PolyNatTrans q p) ->
  (r : PolyFunc) -> (sl : PolyNatTrans r p) ->
  PolyNatTrans (PolyBCFtot {p} {q} f r sl) q
PolyBCFproj {p} {q} f r sl =
  (PolyBCFprojOnPos {p} {q} f r sl ** PolyBCFprojOnDir {p} {q} f r sl)

public export
PolyBCFtotMapPos : {p, q : PolyFunc} -> (f : PolyNatTrans q p) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  (s : PolyFunc) -> (ssl : PolyNatTrans s p) ->
  (alpha : PolyNatTrans r s) ->
  PNTisSliceM {p} {q=r} {r=s} rsl ssl alpha ->
  pfPos (PolyBCFtot {p} {q} f r rsl) -> pfPos (PolyBCFtot {p} {q} f s ssl)
PolyBCFtotMapPos {p} {q} f r rsl s ssl (rsonpos ** rsondir) (poseq ** direq)
  ((ri, qi) ** ieq) =
    ((rsonpos ri, qi) ** trans (poseq ri) ieq)

public export
PolyBCFtotMapDir : {p, q : PolyFunc} -> (f : PolyNatTrans q p) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  (s : PolyFunc) -> (ssl : PolyNatTrans s p) ->
  (alpha : PolyNatTrans r s) ->
  (comm : PNTisSliceM {p} {q=r} {r=s} rsl ssl alpha) ->
  (i : pfPos (PolyBCFtot {p} {q} f r rsl)) ->
  pfDir {p=(PolyBCFtot {p} {q} f s ssl)}
    (PolyBCFtotMapPos {p} {q} f r rsl s ssl alpha comm i) ->
  pfDir {p=(PolyBCFtot {p} {q} f r rsl)} i
PolyBCFtotMapDir {p} {q} f r rsl s ssl (rsonpos ** rsondir) (poseq ** direq)
  ((ri, qi) ** ieq) eleq x (dmx ** dmeq) =
    eleq x
      (dmx . mapFst {f=Either} (rsondir ri) **
       \pd =>
        trans
          (cong dmx $ cong Left $ direq ri pd)
          (dmeq $ rewrite sym $ poseq ri in pd))

public export
PolyBCFtotMap : {p, q : PolyFunc} -> (f : PolyNatTrans q p) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  (s : PolyFunc) -> (ssl : PolyNatTrans s p) ->
  (alpha : PolyNatTrans r s) ->
  PNTisSliceM {p} {q=r} {r=s} rsl ssl alpha ->
  PolyNatTrans (PolyBCFtot {p} {q} f r rsl) (PolyBCFtot {p} {q} f s ssl)
PolyBCFtotMap {p} {q} f r rsl s ssl alpha comm =
  (PolyBCFtotMapPos {p} {q} f r rsl s ssl alpha comm **
   PolyBCFtotMapDir {p} {q} f r rsl s ssl alpha comm)

--------------------------------
---- Pi / dependent product ----
--------------------------------

public export
PolyPiPbDom1Tot : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyFunc
PolyPiPbDom1Tot {p} {q} f r rsl = q

public export
PolyPiPbDom1Proj : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyNatTrans (PolyPiPbDom1Tot {p} {q} f r rsl) q
PolyPiPbDom1Proj {p} {q} f r rsl = pntId q

public export
PolyPiPbDom2DomTot : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyFunc
PolyPiPbDom2DomTot {p} {q} f r rsl = p

public export
PolyPiPbDom2DomProj : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyNatTrans (PolyPiPbDom2DomTot {p} {q} f r rsl) q
PolyPiPbDom2DomProj {p} {q} f r rsl = f

public export
PolyPiPbDom2CodTot : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyFunc
PolyPiPbDom2CodTot {p} {q} f r rsl = r

public export
PolyPiPbDom2CodProj : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyNatTrans (PolyPiPbDom2CodTot {p} {q} f r rsl) q
PolyPiPbDom2CodProj {p} {q} f r rsl = pntVCatComp {p=r} {q=p} {r=q} f rsl

public export
PolyPiPbDom2Tot : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyFunc
PolyPiPbDom2Tot {p} {q} f r rsl =
  polySliceHomObjTot
    {b=q}
    {q=(PolyPiPbDom2DomTot {p} {q} f r rsl)}
    {p=(PolyPiPbDom2CodTot {p} {q} f r rsl)}
    (PolyPiPbDom2DomProj {p} {q} f r rsl)
    (PolyPiPbDom2CodProj {p} {q} f r rsl)

public export
PolyPiPbDom2Proj : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyNatTrans (PolyPiPbDom2Tot {p} {q} f r rsl) q
PolyPiPbDom2Proj {p} {q} f r rsl =
  polySliceHomObjProj
    {b=q}
    {q=(PolyPiPbDom2DomTot {p} {q} f r rsl)}
    {p=(PolyPiPbDom2CodTot {p} {q} f r rsl)}
    (PolyPiPbDom2DomProj {p} {q} f r rsl)
    (PolyPiPbDom2CodProj {p} {q} f r rsl)

public export
PolyPiPbCodDomTot : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyFunc
PolyPiPbCodDomTot {p} {q} f r rsl = p

public export
PolyPiPbCodDomProj : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyNatTrans (PolyPiPbCodDomTot {p} {q} f r rsl) q
PolyPiPbCodDomProj {p} {q} f r rsl = f

public export
PolyPiPbCodCodTot : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyFunc
PolyPiPbCodCodTot {p} {q} f r rsl = p

public export
PolyPiPbCodCodProj : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyNatTrans (PolyPiPbCodCodTot {p} {q} f r rsl) q
PolyPiPbCodCodProj {p} {q} f r rsl = f

public export
PolyPiPbCodTot : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyFunc
PolyPiPbCodTot {p} {q} f r rsl =
  polySliceHomObjTot
    {b=q}
    {q=(PolyPiPbCodDomTot {p} {q} f r rsl)}
    {p=(PolyPiPbCodCodTot {p} {q} f r rsl)}
    (PolyPiPbCodDomProj {p} {q} f r rsl)
    (PolyPiPbCodCodProj {p} {q} f r rsl)

public export
PolyPiPbCodProj : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyNatTrans (PolyPiPbCodTot {p} {q} f r rsl) q
PolyPiPbCodProj {p} {q} f r rsl =
  polySliceHomObjProj
    {b=q}
    {q=(PolyPiPbCodDomTot {p} {q} f r rsl)}
    {p=(PolyPiPbCodCodTot {p} {q} f r rsl)}
    (PolyPiPbCodDomProj {p} {q} f r rsl)
    (PolyPiPbCodCodProj {p} {q} f r rsl)

public export
PolyPiPbMor1 : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyNatTrans
    (PolyPiPbDom1Tot {p} {q} f r rsl)
    (PolyPiPbCodTot {p} {q} f r rsl)
PolyPiPbMor1 {p} {q} f r rsl =
  (\qi =>
    (qi **
     \pi, fqieq => pi **
     \pi, fqieq => fqieq **
     \pi, fqieq, pd => Right pd **
     \pi, fqieq, pd => Refl) **
   \qi, bd =>
    impredCoeqElim
      bd
      (eitherElim
        id
        (\(qi ** ieq ** pd ** comm) => case comm of Refl impossible))
      (\((dl, dr) ** dh) =>
        case decCase dl of
          Left (qd ** lisl) => rewrite lisl in case decCase dr of
            Left (qd' ** risl) =>
              case lisl of Refl => case risl of Refl => void dh
            Right ((qi ** ieq ** pd ** comm) ** risr) =>
              rewrite risr in case comm of Refl impossible
          Right ((qi ** ieq ** pd ** comm) ** lisr) =>
            rewrite lisr in case comm of Refl impossible))

public export
PolyPiPbMor2 : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyNatTrans
    (PolyPiPbDom2Tot {p} {q} f r rsl)
    (PolyPiPbCodTot {p} {q} f r rsl)
PolyPiPbMor2 {p} {q} f r rsl =
  (\(qi ** onpos ** poscomm ** ondir ** dircomm) =>
    (qi **
     \pi, fqieq => pi **
     \pi, fqieq => fqieq **
     \pi, fqieq, pd => Right pd **
     \pi, fqieq, qd => Refl) **
   \(qi ** onpos ** poscomm ** ondir ** dircomm), bd, x,
    (dmx ** el) =>
    bd
      x
      (\dd =>
        dmx
          (eitherElim
            Left
            (\(_ ** _ ** _ ** pdeq) => case pdeq of Refl impossible)
            dd) **
       \((dl, dr) ** dh) =>
        case decCase dl of
          Left (qd ** lisl) => rewrite lisl in case decCase dr of
            Left (qd' ** risl) =>
              case lisl of Refl => case risl of Refl => void dh
            Right ((qi ** ieq ** pd ** comm) ** risr) =>
              rewrite risr in case comm of Refl impossible
          Right ((qi ** ieq ** pd ** comm) ** lisr) =>
            rewrite lisr in case comm of Refl impossible))

public export
PolyPiTot : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) -> PolyFunc
PolyPiTot {p} {q} f r rsl =
  pfPullbackAr
    {p=(PolyPiPbDom1Tot {p} {q} f r rsl)}
    {q=(PolyPiPbDom2Tot {p} {q} f r rsl)}
    {r=(PolyPiPbCodTot {p} {q} f r rsl)}
    (PolyPiPbMor1 {p} {q} f r rsl)
    (PolyPiPbMor2 {p} {q} f r rsl)

public export
PolyPiProj : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyNatTrans (PolyPiTot {p} {q} f r rsl) q
PolyPiProj {p} {q} f r rsl =
  pntVCatComp
    {p=(PolyPiTot {p} {q} f r rsl)}
    {q=(PolyPiPbCodTot {p} {q} f r rsl)}
    {r=q}
    (PolyPiPbCodProj {p} {q} f r rsl)
    (pfPullbackArSlProj
      {p=(PolyPiPbDom1Tot {p} {q} f r rsl)}
      {q=(PolyPiPbDom2Tot {p} {q} f r rsl)}
      {r=(PolyPiPbCodTot {p} {q} f r rsl)}
      (PolyPiPbMor1 {p} {q} f r rsl)
      (PolyPiPbMor2 {p} {q} f r rsl))

-------------------------------------
---- Sigma / dependent sum ----------
-------------------------------------

-- The dependent sum (Sigma) functor internal to `PolyFunc`.
-- A natural transformation `p -> q` induces a functor from slices
-- over `p` to slices over `q`, which is left adjoint to base change.
-- The Sigma functor simply composes the slice projection with the
-- given natural transformation.
public export
PolySigmaTot : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyFunc
PolySigmaTot {p} {q} f r rsl = r

public export
PolySigmaProj : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  PolyNatTrans (PolySigmaTot {p} {q} f r rsl) q
PolySigmaProj {p} {q} f r rsl = pntVCatComp {p=r} {q=p} {r=q} f rsl

public export
PolySigmaTotMap : {p, q : PolyFunc} -> (f : PolyNatTrans p q) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r p) ->
  (s : PolyFunc) -> (ssl : PolyNatTrans s p) ->
  (alpha : PolyNatTrans r s) ->
  PNTisSliceM {p} {q=r} {r=s} rsl ssl alpha ->
  PolyNatTrans (PolySigmaTot {p} {q} f r rsl) (PolySigmaTot {p} {q} f s ssl)
PolySigmaTotMap {p} {q} f r rsl s ssl alpha comm = alpha

------------------------------------------------------------
---- Full polynomial functor (Sigma . Pi . base change) ----
------------------------------------------------------------

-- A polynomial functor between slice categories of PolyFunc is determined
-- by a diagram: b <- i -> e -> a (reading right to left)
-- which gives the composition: Sigma_g . Pi_h . f*
-- where f* is base change along f : e -> a,
-- Pi_h is dependent product along h : e -> i,
-- and Sigma_g is dependent sum along g : i -> b.

public export
record PolyFuncArena where
  constructor MkPolyFuncArena
  baseA : PolyFunc
  baseB : PolyFunc
  intermediate : PolyFunc
  exponent : PolyFunc
  bcMor : PolyNatTrans exponent baseA
  piMor : PolyNatTrans exponent intermediate
  sigmaMor : PolyNatTrans intermediate baseB

-- The full polynomial functor from PolyFunc/baseA to PolyFunc/baseB
public export
PolyFuncArenaInterpTot : (arena : PolyFuncArena) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r (baseA arena)) ->
  PolyFunc
PolyFuncArenaInterpTot arena r rsl =
  let bcResult : PolyFunc
      bcResult = PolyBCFtot
        {p=(baseA arena)}
        {q=(exponent arena)}
        (bcMor arena)
        r
        rsl
      bcpbsl : PolyNatTrans bcResult (exponent arena)
      bcpbsl = PolyBCFproj
        {p=(baseA arena)}
        {q=(exponent arena)}
        (bcMor arena)
        r
        rsl
      piResult : PolyFunc
      piResult = PolyPiTot
        {p=(exponent arena)}
        {q=(intermediate arena)}
        (piMor arena)
        bcResult
        bcpbsl
      pisl : PolyNatTrans piResult (intermediate arena)
      pisl = PolyPiProj
        {p=(exponent arena)}
        {q=(intermediate arena)}
        (piMor arena)
        bcResult
        bcpbsl
  in PolySigmaTot
       {p=(intermediate arena)}
       {q=(baseB arena)}
       (sigmaMor arena)
       piResult
       pisl

public export
PolyFuncArenaInterpProj : (arena : PolyFuncArena) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r (baseA arena)) ->
  PolyNatTrans (PolyFuncArenaInterpTot arena r rsl) (baseB arena)
PolyFuncArenaInterpProj arena r rsl =
  let bcResult : PolyFunc
      bcResult = PolyBCFtot
        {p=(baseA arena)}
        {q=(exponent arena)}
        (bcMor arena)
        r
        rsl
      bcpbsl : PolyNatTrans bcResult (exponent arena)
      bcpbsl = PolyBCFproj
        {p=(baseA arena)}
        {q=(exponent arena)}
        (bcMor arena)
        r
        rsl
      piResult : PolyFunc
      piResult = PolyPiTot
        {p=(exponent arena)}
        {q=(intermediate arena)}
        (piMor arena)
        bcResult
        bcpbsl
      pisl : PolyNatTrans piResult (intermediate arena)
      pisl = PolyPiProj
        {p=(exponent arena)}
        {q=(intermediate arena)}
        (piMor arena)
        bcResult
        bcpbsl
  in PolySigmaProj
       {p=(intermediate arena)}
       {q=(baseB arena)}
       (sigmaMor arena)
       piResult
       pisl

----------------------------------------------
---- Closed form of the composition ----------
----------------------------------------------

-- To better understand the polynomial functor defined by a PolyFuncArena,
-- let's write out the explicit closed form by expanding the definitions.
--
-- Given an arena with:
--   baseA = (aPos ** aDir)
--   exponent = (ePos ** eDir)
--   intermediate = (iPos ** iDir)
--   baseB = (bPos ** bDir)
--   bcMor : e -> a
--   piMor : e -> i
--   sigmaMor : i -> b
--
-- And a slice r with rsl : r -> a, the result is:
--
-- Since PolySigmaTot just returns its input, the result is PolyPiTot applied
-- to the base change result. PolyPiTot itself is defined as a pullback, which
-- makes the full expansion quite involved. For practical purposes, we provide
-- accessor functions below.

public export
PolyFuncArenaInterpPos : (arena : PolyFuncArena) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r (baseA arena)) ->
  Type
PolyFuncArenaInterpPos arena r rsl =
  pfPos (PolyFuncArenaInterpTot arena r rsl)

public export
PolyFuncArenaInterpDir : (arena : PolyFuncArena) ->
  (r : PolyFunc) -> (rsl : PolyNatTrans r (baseA arena)) ->
  PolyFuncArenaInterpPos arena r rsl -> Type
PolyFuncArenaInterpDir arena r rsl i =
  pfDir {p=(PolyFuncArenaInterpTot arena r rsl)} i
