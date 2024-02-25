module LanguageDef.SlicePolyCat

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.PolyCat
import public LanguageDef.InternalCat

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

------------------------------------------------------
------------------------------------------------------
---- Slices over arenas (in dependent-type style) ----
------------------------------------------------------
------------------------------------------------------

-- The natural transformations of both polynomial and Dirichlet functors have
-- on-positions functions from the domain to the codomain.  Thus, the
-- on-positions function of a natural transformation between either of those
-- types of objects (functors) may be viewed as a fibration of the arena
-- being sliced over.
public export
MlSlArOnPos : MLArena -> Type
MlSlArOnPos ar = fst ar -> Type

-- Thus, the positions of the slice object's domain can be viewed as
-- the sum of all the fibers.
public export
MlSlArPos : {ar : MLArena} -> MlSlArOnPos ar -> Type
MlSlArPos {ar} onpos = Sigma {a=(fst ar)} onpos

-- Consequently, the positions of the slice object's domain are a slice
-- of the sum of the fibers.
public export
MlSlArDir : {ar : MLArena} -> MlSlArOnPos ar -> Type
MlSlArDir {ar} onpos = SliceObj (MlSlArPos onpos)

public export
record MlSlArDom (ar : MLArena) where
  constructor MSAdom
  msaOnPos : MlSlArOnPos ar
  msaDir : MlSlArDir {ar} msaOnPos

-- When we view the on-positions function as a fibration, the on-directions
-- function becomes a (slice) morphism between directions of the object being
-- sliced over (the codomain of a slice object) and slices over the fibers of
-- the on-positions function.  As usual, the polynomial version goes in the
-- opposite direction from the on-positions function, while the Dirichlet
-- version goes in the same direction as the on-positions function.

public export
MlSlPolyOnDir : {ar : MLArena} -> MlSlArDom ar -> Type
MlSlPolyOnDir {ar} (MSAdom {ar} onpos dir) =
  (i : fst ar) -> (j : onpos i) -> snd ar i -> dir (i ** j)

public export
MlSlDirichOnDir : {ar : MLArena} -> MlSlArDom ar -> Type
MlSlDirichOnDir {ar} (MSAdom {ar} onpos dir) =
  (i : fst ar) -> (j : onpos i) -> dir (i ** j) -> snd ar i

public export
record MlSlPolyObj (ar : MLArena) where
  constructor MSPobj
  mspDom : MlSlArDom ar
  mspOnDir : MlSlPolyOnDir mspDom

public export
record MlSlDirichObj (ar : MLArena) where
  constructor MSDobj
  msdDom : MlSlArDom ar
  msdOnDir : MlSlDirichOnDir msdDom

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

-- If we factor out the (dependent) products in the domain of `PFSliceObj''`,
-- and reorder some parameters, we obtain the following structure:
record PFSliceObj' (s : PolyFunc) where
  constructor PFS
  pfsPos : SliceObj (pfPos s)
  pfsDir :
    (si : pfPos s) -> (pi : pfsPos si) -> (dir : Type ** pfDir {p=s} si -> dir)

-- The signature of the `erase` operation of a polynomial comonad, which
-- may be viewed as a section of the polynomial functor:  that is, one
-- direction for each position.
PFEraseSig : PolyFunc -> Type
PFEraseSig = flip PolyNatTrans PFIdentityArena

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
PFSliceObjDir (pos ** dir) spf = SliceMorphism {a=pos} dir (PFEraseSig . spf)

PFSliceObjPF : PolyFunc -> PolyFunc
PFSliceObjPF p = (PFSliceObjPos p ** PFSliceObjDir p)

PFSliceObj : PolyFunc -> Type
PFSliceObj p = pfPDir $ PFSliceObjPF p

CPFSliceObjToPFS : (p : PolyFunc) -> CPFSliceObj p -> PFSliceObj p
CPFSliceObjToPFS (ppos ** pdir) ((qpos ** qdir) ** (onpos ** ondir)) =
  (\i : ppos => (PreImage onpos i ** \(Element0 j inpre) => qdir j) **
   \i : ppos, d : pdir i =>
    (\_ => () ** \(Element0 j inpre), () => ondir j $ rewrite inpre in d))

CPFSliceObjFromPFS : (p : PolyFunc) -> PFSliceObj p -> CPFSliceObj p
CPFSliceObjFromPFS (ppos ** pdir) (psl ** m) =
  (((i : ppos ** fst (psl i)) ** \(i ** j) => snd (psl i) j) **
   (fst ** \(i ** j), d => snd (m i d) j ()))

PFBaseChange : {p, q : PolyFunc} ->
  DirichNatTrans q p -> PFSliceObj p -> PFSliceObj q
PFBaseChange {p=(ppos ** pdir)} {q=(qpos ** qdir)} (onpos ** ondir) (psl ** m) =
  (psl . onpos **
   \qi, qd =>
    (\_ => () ** \pslp, () => snd (m (onpos qi) (ondir qi qd)) pslp ()))

PFSliceSigma : (q : PolyFunc) -> {p : PolyFunc} ->
  PolyNatTrans p q -> PFSliceObj p -> PFSliceObj q
PFSliceSigma q {p} beta sl with (CPFSliceObjFromPFS p sl)
  PFSliceSigma q {p} beta sl | (r ** alpha) =
    let csigma = (r ** pntVCatComp beta alpha) in
    CPFSliceObjToPFS q csigma

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

-- A slice object over the terminal polynomial functor is effectively
-- just a polynomial functor, just as a slice of `Type` over `Unit` is
-- effectively just a type.
PFSliceOver1 : PFSliceObj PFTerminalArena -> PolyFunc
PFSliceOver1 psl = PFSliceOverConst {x=Unit} psl ()

PFAppI : {p : PolyFunc} ->
  {- these two parameters form an object of the category of elements of `p` -}
  (ty : Type) -> (el : InterpDirichFunc p ty) ->
  PFSliceObj p -> PFSliceObj (PFHomArena ty)
PFAppI {p=p@(_ ** _)} ty (i ** d) =
  PFBaseChange {p} {q=(PFHomArena ty)} (\() => i ** \() => d)

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

-- Any morphism in the slice category of `p` out of `(q ** alpha)` will have
-- the same `onpos` component, so we can constrain the slice morphisms as
-- follows.
data PFSliceMorph : {0 p : PolyFunc} ->
    CPFSliceObj p -> CPFSliceObj p -> Type where
  PFSM :
    {0 ppos, qpos, rpos : Type} ->
    {0 pdir : ppos -> Type} -> {0 qdir : qpos -> Type} ->
    {0 rdir : rpos -> Type} ->
    (rponpos : rpos -> ppos) -> (qronpos : qpos -> rpos) ->
    (rpondir : (i : rpos) -> pdir (rponpos i) -> rdir i) ->
    (qrondir : (i : qpos) -> rdir (qronpos i) -> qdir i) ->
    PFSliceMorph {p=(ppos ** pdir)}
      ((qpos ** qdir) **
       (rponpos . qronpos ** \i, pd => qrondir i $ rpondir (qronpos i) pd))
      ((rpos ** rdir) **
       (rponpos ** rpondir))

CPFSliceMorphFromPFS : (p : PolyFunc) -> (sp, sq : CPFSliceObj p) ->
  PFSliceMorph {p} sp sq -> CPFSliceMorph p sp sq
CPFSliceMorphFromPFS (ppos ** pdir) ((qpos ** qdir) ** _) ((rpos ** rdir) ** _)
  (PFSM rpop qrop rpod qrod) =
    Element0
      (qrop ** qrod)
      (Evidence0 (\_ => Refl) $ \qi, pd => Refl)

0 CPFSliceMorphToPFS : FunExt -> (p : PolyFunc) -> (sp, sq : CPFSliceObj p) ->
  CPFSliceMorph p sp sq -> PFSliceMorph {p} sp sq
CPFSliceMorphToPFS funext (ppos ** pdir)
  ((qpos ** qdir) ** (qponpos ** qpondir))
  ((rpos ** rdir) ** (rponpos ** rpondir))
  (Element0 (qrop ** qrod) (Evidence0 opeq odeq)) =
    rewrite funExt opeq in
    rewrite sym (funExt $ \i : qpos => funExt $ odeq i) in
    PFSM {pdir} rponpos qrop rpondir qrod

PFSliceMorphDomDir : {pos : Type} -> {dir : pos -> Type} ->
  (dom : PFSliceObjPos (pos ** dir)) -> (cod : PFSliceObj (pos ** dir)) ->
  ((i : pos) -> PolyNatTrans (dom i) (fst cod i)) ->
  PFSliceObjDir (pos ** dir) dom
PFSliceMorphDomDir {pos} {dir} dom (codonpos ** codondir) ntfam i d =
  (\_ => () **
   \j, () => snd (ntfam i) j (snd (codondir i d) (fst (ntfam i) j) ()))

data PFSliceMorph' : {pos : Type} -> {dir : pos -> Type} ->
    PFSliceObj (pos ** dir) -> PFSliceObj (pos ** dir) -> Type where
  PFSM' : {pos : Type} -> {dir : pos -> Type} ->
    (dom : PFSliceObjPos (pos ** dir)) -> (cod : PFSliceObj (pos ** dir)) ->
    (ntfam : (i : pos) -> PolyNatTrans (dom i) (fst cod i)) ->
    PFSliceMorph' {pos} {dir}
      (dom ** PFSliceMorphDomDir {pos} {dir} dom cod ntfam) cod

0 PFSliceMorphToPFS' :
  (pos : Type) -> (dir : pos -> Type) ->
  (sp, sq : CPFSliceObj (pos ** dir)) ->
  PFSliceMorph {p=(pos ** dir)} sp sq ->
  PFSliceMorph' {pos} {dir}
    (CPFSliceObjToPFS (pos ** dir) sp) (CPFSliceObjToPFS (pos ** dir) sq)
PFSliceMorphToPFS' pos dir
  ((qpos ** qdir) ** (_ ** _))
  ((rpos ** rdir) ** (_ ** _))
  (PFSM rpop qrop rpod qrod) =
    ?PFSliceMorphToPFS'_hole

0 PFSliceMorphFromPFS' :
  (pos : Type) -> (dir : pos -> Type) ->
  (dom, cod : PFSliceObj (pos ** dir)) ->
  PFSliceMorph' {pos} {dir} dom cod ->
  PFSliceMorph {p=(pos ** dir)}
    (CPFSliceObjFromPFS (pos ** dir) dom) (CPFSliceObjFromPFS (pos ** dir) cod)
PFSliceMorphFromPFS' _ _ (_ ** _) (_ ** _)
  (PFSM' {pos} {dir} dompos (codpos ** coddir) ntfam) =
    ?PFSliceMorphFromPFS'_hole

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
