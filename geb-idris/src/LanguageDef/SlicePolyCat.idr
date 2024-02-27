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
MlSlArOnPos : MLArena -> Type
MlSlArOnPos ar = fst ar -> Type

-- Thus, the positions of the slice object's domain can be viewed as
-- the sum of all the fibers.
public export
MlSlArPos : {ar : MLArena} -> MlSlArOnPos ar -> Type
MlSlArPos {ar} onpos = Sigma {a=(fst ar)} onpos

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
MlSlDirichDir : {ar : MLArena} -> {onpos : MlSlArOnPos ar} ->
  MlSlArPos {ar} onpos -> Type
MlSlDirichDir {ar} {onpos} pos = SliceObj (snd ar $ fst pos)

public export
record MlDirSlObj (ar : MLArena) where
  constructor MDSobj
  mdsOnPos : MlSlArOnPos ar
  mdsDir :
    Pi {a=(MlSlArPos {ar} mdsOnPos)} $ MlSlDirichDir {ar} {onpos=mdsOnPos}

-- When we replace the on-positions and on-directions functions with fibrations,
-- what we might consider to be the on-directions function is a pi type.
public export
MlSlDirichOnDir : {ar : MLArena} -> (sl : MlDirSlObj ar) ->
  (i : MlSlArPos {ar} $ mdsOnPos sl) ->
  MlSlDirichDir {ar} {onpos=(mdsOnPos sl)} i
MlSlDirichOnDir {ar} (MDSobj onpos dir) (i ** j) d = dir (i ** j) d

-----------------------------------
---- Slice morphism definition ----
-----------------------------------

-- The morphisms of slice categories correspond to morphisms of the
-- base category which commute with the projections.  When we take
-- the dependent-type view in the Dirichlet-functor category, the
-- commutativity conditions are hidden in the type-checking of dependent
-- functions.

public export
MlDirSlMorOnPos : {ar : MLArena} -> MlDirSlObj ar -> MlDirSlObj ar -> Type
MlDirSlMorOnPos {ar=(bpos ** bdir)}
  (MDSobj donpos ddir) (MDSobj conpos cdir) =
    SliceMorphism {a=bpos} donpos conpos

public export
MlDirSlMorOnDir : {ar : MLArena} -> (dom, cod : MlDirSlObj ar) ->
  MlDirSlMorOnPos {ar} dom cod -> Type
MlDirSlMorOnDir {ar=(bpos ** bdir)}
  (MDSobj donpos ddir) (MDSobj conpos cdir) onpos =
    (i : bpos) -> (j : donpos i) -> (d : bdir i) ->
    ddir (i ** j) d -> cdir (i ** onpos i j) d

public export
record MlDirSlMor {ar : MLArena} (dom, cod : MlDirSlObj ar) where
  constructor MDSM
  mdsOnPos : MlDirSlMorOnPos {ar} dom cod
  mdsOnDir : MlDirSlMorOnDir {ar} dom cod mdsOnPos

------------------------------------------------------------------------------
---- Equivalence of dependent-type and categorial-style objects/morphisms ----
------------------------------------------------------------------------------

public export
mlDirSlObjToC : {ar : MLArena} -> MlDirSlObj ar -> CDFSliceObj ar
mlDirSlObjToC {ar=ar@(bpos ** bdir)} (MDSobj onpos dir) =
  ((MlSlArPos {ar} onpos ** \i => Sigma $ dir i) **
   (DPair.fst ** \_ => DPair.fst))

public export
mlDirSlObjFromC : {ar : MLArena} -> CDFSliceObj ar -> MlDirSlObj ar
mlDirSlObjFromC {ar=ar@(bpos ** bdir)} ((slpos ** sldir) ** (onpos ** ondir)) =
  MDSobj
    (\i => PreImage onpos i)
    (\(i ** (Element0 j eq)), bd =>
      Subset0 (sldir j) $ \sld => ondir j sld = replace {p=bdir} (sym eq) bd)

public export
mlDirSlMorToCBase : {ar : MLArena} -> {dom, cod : MlDirSlObj ar} ->
  MlDirSlMor dom cod ->
  DirichNatTrans (fst (mlDirSlObjToC dom)) (fst (mlDirSlObjToC cod))
mlDirSlMorToCBase {ar=(bpos ** bdir)}
  {dom=(MDSobj donpos ddir)} {cod=(MDSobj conpos cdir)} (MDSM onpos ondir) =
    (\ij => (fst ij ** onpos (fst ij) (snd ij)) **
     \(i ** j), (d ** dd) => (d ** ondir i j d dd))

public export
mlDirSlMorToD : {ar : MLArena} -> {dom, cod : MlDirSlObj ar} ->
  MlDirSlMor dom cod -> DFSliceMorph {p=ar} (mlDirSlObjToC cod)
mlDirSlMorToD {ar=ar@(bpos ** bdir)}
  {dom=dom@(MDSobj donpos ddir)} {cod=cod@(MDSobj conpos cdir)}
  mor@(MDSM onpos ondir) =
    (fst (mlDirSlObjToC dom) ** mlDirSlMorToCBase {ar} {dom} {cod} mor)

public export
0 mlDirSlMorToC : {ar : MLArena} -> {dom, cod : MlDirSlObj ar} ->
  MlDirSlMor dom cod -> CDFSliceMorph ar (mlDirSlObjToC dom) (mlDirSlObjToC cod)
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
            $ \i : (DPair ppos donpos), d : (DPair (pdir (fst i)) (ddir i)) =>
            trans (odeq i d)
              $ case i of (i' ** j') => case d of (d' ** dd') => Refl)

public export
mlDirSlMorFromD : {ar : MLArena} -> {cod : CDFSliceObj ar} ->
  (mor : DFSliceMorph {p=ar} cod) ->
  MlDirSlMor
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
  MlDirSlMor (mlDirSlObjFromC {ar} dom) (mlDirSlObjFromC {ar} cod)
mlDirSlMorFromC {ar=(ppos ** pdir)}
  {dom=((dtot ** dproj) ** (donpos ** dondir))}
  {cod=((ctot ** cproj) ** (conpos ** condir))}
  (Element0 (monpos ** mondir) (Evidence0 opeq odeq)) =
    MDSM
      (\i, (Element0 j peq) => Element0 (monpos j) $ trans (sym $ opeq j) peq)
      (\i, (Element0 j peq), pd, (Element0 md deq) =>
        Element0 (mondir j md) $
          trans (odeq j md) $ rewrite sym (opeq j) in deq)

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

PFSliceMorphDomDir : {pos : Type} -> {dir : pos -> Type} ->
  (dom : PFSliceObjPos (pos ** dir)) -> (cod : PFSliceObj (pos ** dir)) ->
  ((i : pos) -> PolyNatTrans (dom i) (fst cod i)) ->
  PFSliceObjDir (pos ** dir) dom
PFSliceMorphDomDir {pos} {dir} dom (codonpos ** codondir) ntfam i d j =
   let (onpos ** ondir) = ntfam i in ondir j $ codondir i d $ onpos j

data PFSliceMorph' : {pos : Type} -> {dir : pos -> Type} ->
    PFSliceObj (pos ** dir) -> PFSliceObj (pos ** dir) -> Type where
  PFSM' : {pos : Type} -> {dir : pos -> Type} ->
    (dom : PFSliceObjPos (pos ** dir)) -> (cod : PFSliceObj (pos ** dir)) ->
    (ntfam : (i : pos) -> PolyNatTrans (dom i) (fst cod i)) ->
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
