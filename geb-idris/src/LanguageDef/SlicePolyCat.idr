module LanguageDef.SlicePolyCat

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.PolyCat
import public LanguageDef.InternalCat

--------------------------------------
--------------------------------------
---- Internal polynomial functors ----
--------------------------------------
--------------------------------------

-- An internal polynomial functor is a sum of representable internal
-- copresheaves. It can be expressed as a slice object over the object
-- of the objects of the internal category -- the total-space object is
-- the index of the sum, known as the "position set [or "type", or "object"]".
-- The projection morphism assigns to each position a "direction", which is
-- an object of the internal category.
public export
IntArena : (c : Type) -> Type
IntArena c = CSliceObj c

public export
InterpIPFobj : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntArena c -> c -> Type
InterpIPFobj c mor (pos ** dir) a = (i : pos ** mor (dir i) a)

public export
InterpIPFmap : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (ar : IntArena c) -> IntCopreshfMapSig c mor (InterpIPFobj c mor ar)
InterpIPFmap c mor comp (pos ** dir) x y m (i ** dm) =
  (i ** comp (dir i) x y m dm)

public export
InterpIDFobj : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntArena c -> c -> Type
InterpIDFobj c mor (pos ** dir) a = (i : pos ** mor a (dir i))

public export
InterpIDFmap : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (ar : IntArena c) -> IntPreshfMapSig c mor (InterpIDFobj c mor ar)
InterpIDFmap c mor comp (pos ** dir) x y m (i ** dm) =
  (i ** comp y x (dir i) dm m)

public export
IntPNTar : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntArena c -> IntArena c -> Type
IntPNTar c mor (ppos ** pdir) (qpos ** qdir) =
  (onpos : ppos -> qpos ** (i : ppos) -> mor (qdir (onpos i)) (pdir i))

public export
InterpIPnt : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (p, q : IntArena c) -> IntPNTar c mor p q ->
  IntCopreshfNTSig c (InterpIPFobj c mor p) (InterpIPFobj c mor q)
InterpIPnt c mor comp (ppos ** pdir) (qpos ** qdir) (onpos ** ondir) x
  (i ** dm) =
    (onpos i ** comp (qdir (onpos i)) (pdir i) x dm (ondir i))

public export
IntDNTar : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntArena c -> IntArena c -> Type
IntDNTar c mor (ppos ** pdir) (qpos ** qdir) =
  (onpos : ppos -> qpos ** (i : ppos) -> mor (pdir i) (qdir (onpos i)))

public export
InterpIDnt : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (p, q : IntArena c) -> IntDNTar c mor p q ->
  IntPreshfNTSig c (InterpIDFobj c mor p) (InterpIDFobj c mor q)
InterpIDnt c mor comp (ppos ** pdir) (qpos ** qdir) (onpos ** ondir) x
  (i ** dm) =
    (onpos i ** comp x (pdir i) (qdir (onpos i)) (ondir i) dm)

-------------------------------------
-------------------------------------
---- Dirichlet-functor embedding ----
-------------------------------------
-------------------------------------

public export
IntDirichCatObj : Type -> Type
IntDirichCatObj = IntArena

public export
IntDirichCatMor : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntDifunctorSig (IntDirichCatObj c)
IntDirichCatMor = IntDNTar

-- We can embed a category `c/mor` into its category of Dirichlet functors
-- (sums of representable presheaves) with natural transformations.
public export
IntDirichEmbedObj : (c : Type) -> (a : c) -> IntDirichCatObj c
IntDirichEmbedObj c a = (() ** (\_ : Unit => a))

-- Note that we can _not_ embed a category into its category of polynomial
-- functors (sums of representable copresheaves) with natural transformations,
-- because trying to define this with `IntPNTar` substituted for `IntDNTar`
-- would require us to define a morphism in the opposite direction from `m`.
-- There is no guarantee that such a morphism exists in `c/mor`.
public export
IntDirichEmbedMor : (c : Type) -> (mor : IntDifunctorSig c) ->
  (a, b : c) ->
  mor a b ->
  IntDirichCatMor c mor (IntDirichEmbedObj c a) (IntDirichEmbedObj c b)
IntDirichEmbedMor c mor a b m = ((\_ : Unit => ()) ** (\_ : Unit => m))

-- The inverse of the embedding of a category into its category of
-- Dirichlet functors.  The existence of this inverse shows that
-- the embedding is full and faithful.
public export
IntDirichEmbedMorInv : (c : Type) -> (mor : IntDifunctorSig c) ->
  (a, b : c) ->
  IntDirichCatMor c mor (IntDirichEmbedObj c a) (IntDirichEmbedObj c b) ->
  mor a b
IntDirichEmbedMorInv c mor a b (pos ** dir) =
  -- Note that `pos` has type `Unit -> Unit`, so there is only one thing
  -- it can be, which is the identity on `Unit` (equivalently, the constant
  -- function returning `()`).
  dir ()

-------------------------------------------
-------------------------------------------
---- Polynomial categories of elements ----
-------------------------------------------
-------------------------------------------

public export
PolyCatElemObj : (c : Type) -> (mor : IntDifunctorSig c) -> IntArena c -> Type
PolyCatElemObj c mor p = (x : c ** InterpIPFobj c mor p x)

-- Unfolding the definition of a morphism in the category of elements
-- specifically of a polynomial endofunctor on `Type` yields the following:
--
--  - A position `i` of the polynomial functor
--  - A pair of types `x`, `y`
--  - An assignment of the directions of `p` at `i` to `x` (together with the
--    type `x`, this can be viewed as an object of the coslice category of
--    the direction-set)
--  - A morphism in `Type` (a function) from `x` to `y`
--
-- One way of looking at all of that together is, if we view a polynomial
-- functor `p` as representing open terms of a data structure, then a morphism
-- of its category of elements is a closed term with elements of `x`
-- substituted for its variables (comprising the type `x` which we then view
-- as a type of variables together with the choice of a position and and
-- assignment of its directions to `x`), together with a function from `x`
-- to `y`, which uniquely determines a closed term with elements of `y`
-- substituted for its variables, by mapping the elements of `x` in the
-- closed term with the chosen function to elements of `y`, while preserving the
-- structure of the term.
--
-- Because of that unique determination, we do not need explicitly to choose
-- the element component of the codomain object, as in the general definition
-- of the category of elements -- the choice of both components of the domain
-- object together with a morphism from its underlying object to some other
-- object of `Type` between them uniquely determine the one codomain object to which there
-- is a corresponding morphism in the category of elements.
public export
data PolyCatElemMor :
    (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
    (p : IntArena c) ->
    PolyCatElemObj c mor p -> PolyCatElemObj c mor p -> Type where
  PCEM : {c : Type} -> {mor : IntDifunctorSig c} ->
    (comp : IntCompSig c mor) ->
    -- `pos` and `dir` together form an `IntArena c`.
    (pos : Type) -> (dir : pos -> c) ->
    -- `i` and `dm` comprise a term of `InterpIPFobj c mor (pos ** dir) x`;
    -- `x` and `dm` together comprise an object of the coslice category
    -- of `dir i`.  `x`, `i`, and `dm` all together comprise an object of
    -- the category of elements of `(pos ** dir)`.
    (x : c) -> (i : pos) -> (dm : mor (dir i) x) ->
    -- `y` and `m` together form an object of the coslice category of `x`.
    (y : c) -> (m : mor x y) ->
    PolyCatElemMor c mor comp (pos ** dir)
      (x ** (i ** dm))
      (y ** (i ** comp (dir i) x y m dm))

public export
DirichCatElemObj : (c : Type) -> (mor : IntDifunctorSig c) -> IntArena c -> Type
DirichCatElemObj c mor p = (x : c ** InterpIDFobj c mor p x)

public export
data DirichCatElemMor :
    (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
    (p : IntArena c) ->
    DirichCatElemObj c mor p -> DirichCatElemObj c mor p -> Type where
  DCEM : {c : Type} -> {mor : IntDifunctorSig c} ->
    (comp : IntCompSig c mor) ->
    -- `pos` and `dir` together form an `IntArena c`.
    (pos : Type) -> (dir : pos -> c) ->
    -- `i` and `dm` comprise a term of `InterpIDFobj c mor (pos ** dir) x`;
    -- `x` and `dm` together comprise an object of the slice category
    -- of `dir i`.  `x`, `i`, and `dm` all together comprise an object of
    -- the category of elements of `(pos ** dir)`.
    (x : c) -> (i : pos) -> (dm : mor x (dir i)) ->
    -- `y` and `m` together form an object of the slice category of `x`.
    (y : c) -> (m : mor y x) ->
    DirichCatElemMor c mor comp (pos ** dir)
      (y ** (i ** comp y x (dir i) dm m))
      (x ** (i ** dm))

----------------------------------------------------------------------------
----------------------------------------------------------------------------
---- Slice objects in the category of polynomial endofunctors on `Type` ----
----------------------------------------------------------------------------
----------------------------------------------------------------------------

public export
IntPolyCatObj : Type -> Type
IntPolyCatObj = IntArena

public export
IntPolyCatMor : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntDifunctorSig (IntPolyCatObj c)
IntPolyCatMor = IntDNTar

public export
MLPolyCatObj : Type
MLPolyCatObj = IntPolyCatObj Type

public export
MLPolyCatMor : MLPolyCatObj -> MLPolyCatObj -> Type
MLPolyCatMor = IntPolyCatMor Type HomProf

public export
MLPolyCatElemObj : MLPolyCatObj -> Type
MLPolyCatElemObj = PolyCatElemObj Type HomProf

public export
MLPolyCatElemMor : (p : MLPolyCatObj) -> (x, y : MLPolyCatElemObj p) -> Type
MLPolyCatElemMor = PolyCatElemMor Type HomProf typeComp

public export
MLDirichCatObj : Type
MLDirichCatObj = IntDirichCatObj Type

public export
MLDirichCatMor : MLDirichCatObj -> MLDirichCatObj -> Type
MLDirichCatMor = IntDirichCatMor Type HomProf

public export
MLDirichCatElemObj : MLDirichCatObj -> Type
MLDirichCatElemObj = DirichCatElemObj Type HomProf

public export
MLDirichCatElemMor : (ar : MLDirichCatObj) ->
  MLDirichCatElemObj ar -> MLDirichCatElemObj ar -> Type
MLDirichCatElemMor = DirichCatElemMor Type HomProf typeComp

----------------------------------
---- Category-theoretic style ----
----------------------------------

CPFSliceObj : PolyFunc -> Type
CPFSliceObj p = (q : PolyFunc ** PolyNatTrans q p)

public export
0 CPFNatTransEq : (p, q : PolyFunc) -> (alpha, beta : PolyNatTrans p q) -> Type
CPFNatTransEq (ppos ** pdir) (qpos ** qdir)
  (aonpos ** aondir) (bonpos ** bondir) =
    Exists0
      (ExtEq {a=ppos} {b=qpos} aonpos bonpos)
      $ \onposeq =>
        (i : ppos) -> (d : qdir (aonpos i)) ->
        bondir i (replace {p=qdir} (onposeq i) d) = aondir i d

CPFSliceMorph : (p : PolyFunc) -> CPFSliceObj p -> CPFSliceObj p -> Type
CPFSliceMorph p (q ** qp) (r ** rp) =
  Subset0 (PolyNatTrans q r) (\qr => CPFNatTransEq q p qp (pntVCatComp rp qr))

---------------------------------------------
---- Arena/dependent-type-universe-style ----
---------------------------------------------

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
  (el : MLDirichCatElemObj p) ->
  PFSliceObj p -> PFSliceObj (PFHomArena $ fst el)
PFAppI {p=p@(_ ** _)} (ty ** i ** d) =
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
  PFSliceOver1 $ PFAppI {p} (Void ** i ** \v => void v) slp

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
