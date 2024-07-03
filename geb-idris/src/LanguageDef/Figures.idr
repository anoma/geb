module LanguageDef.Figures

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.PolyCat
import public LanguageDef.DiagramCat

%default total

-- In favor of the (identical) one from `SliceFuncCat`.
%hide Library.IdrisCategories.BaseChangeF

------------------------------
------------------------------
---- Metalanguage quivers ----
------------------------------
------------------------------

-- In this section, we shall define the notion of a "quiver"
-- (see https://ncatlab.org/nlab/show/quiver and
-- https://en.wikipedia.org/wiki/Quiver_(mathematics) ) internal to the
-- metalanguage -- in this case, Idris's `Type`.
--
-- A quiver may be viewed as a functor from the category called the "walking
-- quiver" (see again the ncatlab page) to `Set`, or in general any category,
-- or in this specific case, Idris's `Type`.  When viewed as such, quivers may
-- be treated as the objects of the category of functors from the walking
-- quiver to Idris's `Type`, where the morphisms of the category are, as usual
-- in functor categories, the natural transformations.

-- So we begin by defining the walking quiver.

----------------------------
---- The walking quiver ----
----------------------------

-- The walking quiver's objects.
public export
data WQObj : Type where
  WQOvert : WQObj
  WQOedge : WQObj

-- The walking quiver's (non-identity) morphisms.
public export
data WQMorph : Type where
  WQMsrc : WQMorph
  WQMtgt : WQMorph

-- Next we specify the signatures of the walking quiver's morphisms
-- by assigning to each morphism a source and target object.

public export
WQSrc : WQMorph -> WQObj
WQSrc WQMsrc = WQOedge
WQSrc WQMtgt = WQOedge

public export
WQTgt : WQMorph -> WQObj
WQTgt WQMsrc = WQOvert
WQTgt WQMtgt = WQOvert

public export
WQSigT : Type
WQSigT = (WQObj, WQObj)

public export
WQSig : WQMorph -> WQSigT
WQSig m = (WQSrc m, WQTgt m)

-- We do not here explicitly define composition in the walking quiver,
-- because it does not contain any compositions between two non-identity
-- morphisms.  Since the identities are units of composition, the
-- composition map is fully determined just by prescribing that it follows
-- the laws of a category.
--
-- Therefore, we can now treat the walking quiver as defined as a category.

----------------------------
---- Quivers in general ----
----------------------------

-- Now, we define the notion of "quiver" (internal to `Type`) as a functor
-- from the walking quiver (whose objects are `WQObj` and whose morphisms
-- are `WQMorph`) to `Type`.

-- Because there are only two terms in `WQObj`, a functor from `WQObj` is
-- is just a slightly abstract way of defining a pair of types.  The reason
-- for doing it this way is that it translates directly to more general
-- situations (in particular, to the definition of (co)presheaves).
public export
QuivObjMap : Type
QuivObjMap = SliceObj WQObj

-- The category-theoretic form of `QuivObjMap`.  In this formulation,
-- the total space could be viewed (conceptually, though an implementation
-- might below the surface be more compact) as a coproduct of one object of
-- `Type` for each object of the walking quiver (as represented by a term
-- of the `WQObj` type), with the projection map taking each term of a `Type`
-- to the corresponding object of the walking quiver.
public export
CQuivObjMap : Type
CQuivObjMap = CSliceObj WQObj

-- Given an object map, we can pull it back along `WQSrc` to obtain
-- a mapping from morphisms to the `Type`s to which their domains are
-- mapped by the object map.
public export
QuivDomMap : QuivObjMap -> SliceObj WQMorph
QuivDomMap = BaseChangeF WQSrc

-- This is the analogue of `QuivDomMap` in category-theoretic style.
-- Given a slice object representing an object map (the object component
-- of a quiver), it re-slices it over morphisms by their domains.  (That
-- means that instead of being fibred over objects of the walking quiver,
-- the range of the object map is fibred over collections of morphisms,
-- in this case the collection of morphisms whose domain maps to each fiber
-- of the range of the object map.  We might now view the total space as
-- a type of _pairs_ of a term of the range of the object map and a morphism,
-- where the term is in the type to which the domain of the morphism is mapped.)
public export
CQuivDomMap : CSliceFunctor WQObj WQMorph
CQuivDomMap = CSBaseChange WQSrc

-- And the same for codomains.
public export
QuivCodMap : QuivObjMap -> SliceObj WQMorph
QuivCodMap = BaseChangeF WQTgt

-- And the category-theoretic style for codomains.
public export
CQuivCodMap : CSliceFunctor WQObj WQMorph
CQuivCodMap = CSBaseChange WQTgt

-- Given an object map, we can take a diagonal of it which maps each
-- object of the walking quiver to a symmetric pair of objects of `Type`.
public export
QuivDiagMap : SliceFunctor WQObj WQSigT
QuivDiagMap f (a, b) = (f a, f b)

-- And the category-theoretic style.
public export
CQuivDiagMap : CSliceFunctor WQObj WQSigT
CQuivDiagMap (x ** px) = (ProductMonad x ** mapHom {f=Pair} px)

-- Given an object map, we can take its diagonal and then pull it back
-- along `WQSig` to obtain a mapping from each morphism to a pair made
-- up of a term of its domain together with a term of its codomain.
public export
QuivSigMap : QuivObjMap -> SliceObj WQMorph
QuivSigMap = BaseChangeF WQSig . QuivDiagMap

public export
CQuivSigMap : CSliceFunctor WQObj WQMorph
CQuivSigMap = CSBaseChange WQSig . CQuivDiagMap

public export
QuivMorphHom : QuivObjMap -> SliceObj WQMorph
QuivMorphHom f m = TypeHomObj (QuivDomMap f m) (QuivCodMap f m)

-- Because of the particular structure of the walking quiver (there's no way to
-- get via morphisms from the vertex object to the edge object), there are no
-- compositions of either of the two non-identity morphisms with each other
-- (and hence no compositions of either of the two non-identity morphisms
-- with any non-identity morphisms), so the morphism-map component does not
-- need any explicit identity-preserving or composition-preserving conditions;
-- a correct morphism map is precisely determined by any two functions with
-- the signatures below.
public export
QuivMorphMap : SliceObj QuivObjMap
QuivMorphMap = Pi {a=WQMorph} . QuivMorphHom

-- Note:  I think this is the generalized slice-profunctor form
-- of CSNTCovarFunctor.
public export
CQuivMorphMap : CSliceFunctor WQObj WQMorph
CQuivMorphMap f = CSHomObj (CQuivDomMap f) (CQuivCodMap f)

-- A (metalanguage) quiver, as a functor, is an object map (from objects of
-- the walking quiver to types in `Type`) together with a morphism map (from
-- the morphisms of the walking quiver to the functions on `Type`).
public export
MLQuiver : Type
MLQuiver = Sigma {a=QuivObjMap} QuivMorphMap

public export
MLQvert : SliceObj MLQuiver
MLQvert q = fst q WQOvert

public export
MLQedgeTot : MLQuiver -> Type
MLQedgeTot q = fst q WQOedge

public export
MLQsrc : (q : MLQuiver) -> MLQedgeTot q -> MLQvert q
MLQsrc q = snd q WQMsrc

public export
MLQtgt : (q : MLQuiver) -> MLQedgeTot q -> MLQvert q
MLQtgt q = snd q WQMtgt

public export
MLQedge : (q : MLQuiver) -> MLQvert q -> MLQvert q -> Type
MLQedge q src tgt =
  Subset0 (MLQedgeTot q) $ \e => (MLQsrc q e = src, MLQtgt q e = tgt)

-- The morphisms of the (functor) category `Quiv` as a category internal
-- to the metalanguage's `Type` (i.e. the category of functors from the
-- walking quiver to `Type`, whose objects are `MLQuiver`) are natural
-- transformations.  The walking quiver has two objects, so a natural
-- transformation has two components.  The target category is `Type`, so
-- each component is simply a function between the targets of the object-map
-- components of the functors (in general, each component of a natural
-- transformation between functors is a morphism in the target category of the
-- functors).
--
-- When we view the functors in `Quiv` as quivers, a natural transformation
-- comprises a vertex (object) map and an edge (morphism) map, where the
-- naturality condition states that the endpoints of an edge which is an
-- output of the morphism map are the outputs of the object map.  In other
-- words, a natural transformation from a functor in `Quiv` to another specifies
-- a quiver/graph homomorphism.  (Note that that in turn specifies a functor
-- between the free categories on the graphs, but that not all functors between
-- free categories on those graphs may be specified that way -- such functors
-- map edges of the domain to arbitrary _paths_ in the codomain, not necessarily
-- only to edges in the codomain.)
public export
record MLQMorph (dom, cod : MLQuiver) where
  constructor MLQM
  mlqmComponent : SliceMorphism {a=WQObj} (fst dom) (fst cod)

  0 mlqNaturality : (m : WQMorph) ->
    ExtEq
      (mlqmComponent (WQTgt m) . snd dom m)
      (snd cod m . mlqmComponent (WQSrc m))

public export
MLQMid : (0 x : MLQuiver) -> MLQMorph x x
MLQMid x = MLQM (\_ => id) $ \_, _ => Refl

public export
MLQMcomp : {x, y, z : MLQuiver} ->
  MLQMorph y z -> MLQMorph x y -> MLQMorph x z
MLQMcomp {x} {y} {z} (MLQM gc gn) (MLQM fc fn) =
  MLQM (sliceComp gc fc) $
    \m, el => trans (cong (gc $ WQTgt m) $ fn m el) (gn m $ fc (WQSrc m) el)

----------------------------------------
---- The walking quiver as a quiver ----
----------------------------------------

-- The walking quiver is so-called because it may itself be viewed _as_
-- a quiver -- that is, as a particular functor from a particular category
-- (which, as often with such functors, we call an "index category") to
-- `Type` (or whichever category the notion of "quiver" is internal to).
-- So we now define the walking quiver explicitly as a quiver (having
-- defined quivers in terms of the walking quiver!).

public export
WalkingQuivObjMap : QuivObjMap
WalkingQuivObjMap WQOvert = WQObj
WalkingQuivObjMap WQOedge = WQMorph

public export
WalkingQuivMorphMap : QuivMorphMap WalkingQuivObjMap
WalkingQuivMorphMap WQMsrc = WQSrc
WalkingQuivMorphMap WQMtgt = WQTgt

public export
WalkingQuiv : MLQuiver
WalkingQuiv = (WalkingQuivObjMap ** WalkingQuivMorphMap)

-------------------------------
-------------------------------
---- Paths through quivers ----
-------------------------------
-------------------------------

---------------
---- Paths ----
---------------

public export
0 IsNeQPathAcc :
  (q : MLQuiver) -> Type -> MLQedgeTot q -> List (MLQedgeTot q) -> Type
IsNeQPathAcc q acc e [] = acc
IsNeQPathAcc q acc e (e' :: es) =
  IsNeQPathAcc q (MLQtgt q e = MLQsrc q e', acc) e' es

public export
0 IsNeQPathAccDec :
  (q : MLQuiver) -> DecEqPred (MLQvert q) -> (acc : Type) -> Dec acc ->
  (e : MLQedgeTot q) -> (es : List (MLQedgeTot q)) ->
  Dec (IsNeQPathAcc q acc e es)
IsNeQPathAccDec q veq acc adec e [] = adec
IsNeQPathAccDec q veq acc adec e (e' :: es) =
  let
    adec' : Dec (MLQtgt q e = MLQsrc q e', acc) =
      case (veq (MLQtgt q e) (MLQsrc q e'), adec) of
        (Yes eq, Yes eacc) => Yes (eq, eacc)
        (No neq, _) => No $ \(eq, eacc) => neq eq
        (_ , No nacc) => No $ \(eq, eacc) => nacc eacc
  in
  IsNeQPathAccDec q veq (MLQtgt q e = MLQsrc q e', acc) adec' e' es

public export
0 IsNeQPath : (q : MLQuiver) -> MLQedgeTot q -> List (MLQedgeTot q) -> Type
IsNeQPath q = IsNeQPathAcc q Unit

public export
0 IsNeQPathDec : (q : MLQuiver) -> DecEqPred (MLQvert q) ->
  (e : MLQedgeTot q) -> (es : List (MLQedgeTot q)) -> Dec (IsNeQPath q e es)
IsNeQPathDec q veq = IsNeQPathAccDec q veq Unit (Yes ())

public export
data QPathData : SliceObj MLQuiver where
  QPDLoop : {0 q : MLQuiver} ->
    MLQvert q -> QPathData q
  QPDComp : {0 q : MLQuiver} ->
    MLQedgeTot q -> List (MLQedgeTot q) -> QPathData q

public export
qpdSrc : {q : MLQuiver} -> QPathData q -> MLQvert q
qpdSrc {q} (QPDLoop {q} v) = v
qpdSrc {q} (QPDComp {q} e es) = MLQsrc q e

public export
qpdTgt : {q : MLQuiver} -> QPathData q -> MLQvert q
qpdTgt {q} (QPDLoop {q} v) = v
qpdTgt {q} (QPDComp {q} e es) = case maybeLast es of
  Just e' => MLQtgt q e'
  Nothing => MLQtgt q e

public export
showQPD : {0 q : MLQuiver} -> (MLQvert q -> String) ->
  (MLQedgeTot q -> String) -> QPathData q -> String
showQPD {q} shv she (QPDLoop v) = shv v
showQPD {q} shv she (QPDComp e es) =
  let Show (MLQedgeTot q) where show = she in show (e :: es)

public export
(shv : Show (MLQvert q)) => (she : Show (MLQedgeTot q)) =>
    Show (QPathData q) where
  show = showQPD show show

public export
0 IsQPath : (q : MLQuiver) -> QPathData q -> Type
IsQPath q (QPDLoop {q} v) = Unit
IsQPath q (QPDComp {q} e es) = IsNeQPath q e es

public export
0 IsQPathDec : (q : MLQuiver) -> DecEqPred (MLQvert q) ->
  (p : QPathData q) -> Dec (IsQPath q p)
IsQPathDec q veq (QPDLoop {q} v) = Yes ()
IsQPathDec q veq (QPDComp {q} e es) = IsNeQPathDec q veq e es

public export
QuivPath : MLQuiver -> Type
QuivPath q = Subset0 (QPathData q) (IsQPath q)

public export
0 isQPath : (q : MLQuiver) -> DecEqPred (MLQvert q) ->
  (es : QPathData q) -> Bool
isQPath q veq es = isYes $ IsQPathDec q veq es

public export
QuivPathDec : (q : MLQuiver) -> DecEqPred (MLQvert q) -> Type
QuivPathDec q veq = Refinement {a=(QPathData q)} (isQPath q veq)

public export
qpSrc : {q : MLQuiver} -> QuivPath q -> MLQvert q
qpSrc {q} p = qpdSrc (fst0 p)

public export
qpTgt : {q : MLQuiver} -> QuivPath q -> MLQvert q
qpTgt {q} p = qpdTgt (fst0 p)

----------------------
---- Path closure ----
----------------------

public export
PCQuiverObj : MLQuiver -> WQObj -> Type
PCQuiverObj q WQOvert = MLQvert q
PCQuiverObj q WQOedge = QuivPath q

public export
PCQuiverMorph : (q : MLQuiver) ->
  (m : WQMorph) -> PCQuiverObj q (WQSrc m) -> PCQuiverObj q (WQTgt m)
PCQuiverMorph q WQMsrc = qpSrc {q}
PCQuiverMorph q WQMtgt = qpTgt {q}

-- The path-closure (i.e. reflexive/transitive-closure) monad (on `Quiv`).
public export
PCQuiver : MLQuiver -> MLQuiver
PCQuiver q = (PCQuiverObj q ** PCQuiverMorph q)

public export
PCQAlg : MLQuiver -> Type
PCQAlg q = MLQMorph (PCQuiver q) q

public export
PCQpureComponent : (q : MLQuiver) ->
  SliceMorphism {a=WQObj} (fst q) (fst $ PCQuiver q)
PCQpureComponent (f ** fm) WQOvert elfx = elfx
PCQpureComponent (f ** fm) WQOedge elfx = Element0 (QPDComp elfx []) ()

public export
PCQpureNaturality : (q : MLQuiver) -> (m : WQMorph) ->
  ExtEq
    (PCQpureComponent q (WQTgt m) . snd q m)
    (snd (PCQuiver q) m . PCQpureComponent q (WQSrc m))
PCQpureNaturality (f ** fm) WQMsrc el = Refl
PCQpureNaturality (f ** fm) WQMtgt el = Refl

public export
PCQpure : (q : MLQuiver) -> MLQMorph q (PCQuiver q)
PCQpure q = MLQM (PCQpureComponent q) (PCQpureNaturality q)

public export
PCQevalComponent : (v, a : MLQuiver) -> MLQMorph v a -> PCQAlg a ->
  SliceMorphism {a=WQObj} (fst $ PCQuiver v) (fst a)
PCQevalComponent (vf ** vfm) (af ** afm) (MLQM mcomp mnat) (MLQM algcomp algnat)
  WQOvert x =
    mcomp WQOvert x
PCQevalComponent (vf ** vfm) (af ** afm) (MLQM mcomp mnat) (MLQM algcomp algnat)
  WQOedge (Element0 qpd isqp) =
    algcomp WQOedge $ case qpd of
      QPDLoop x => Element0 (QPDLoop $ mcomp WQOvert x) ()
      QPDComp ve vl =>
        Element0 (QPDComp (mcomp WQOedge ve) (map (mcomp WQOedge) vl)) $
          case vl of
            [] => ()
            ve' :: ves => ?PCQevalComponent_hole

public export
PCQevalNaturality : (v, a : MLQuiver) ->
  (subst : MLQMorph v a) -> (alg : PCQAlg a) ->
  (m : WQMorph) ->
  ExtEq
    (PCQevalComponent v a subst alg (WQTgt m) . snd (PCQuiver v) m)
    (snd a m . PCQevalComponent v a subst alg (WQSrc m))
PCQevalNaturality (vf ** vfm) (af ** afm)
  (MLQM mcomp mnat) (MLQM algcomp algnat) WQMsrc (Element0 qpd isqp) =
    ?PCQevalNaturality_hole_src
PCQevalNaturality (vf ** vfm) (af ** afm)
  (MLQM mcomp mnat) (MLQM algcomp algnat) WQMtgt (Element0 qpd isqp) =
    ?PCQevalNaturality_hole_tgt

-- The "eval" universal morphism of `PCQuiver`.
public export
PCQeval : (v, a : MLQuiver) -> MLQMorph v a -> PCQAlg a ->
  MLQMorph (PCQuiver v) a
PCQeval v a m alg =
  MLQM (PCQevalComponent v a m alg) (PCQevalNaturality v a m alg)

public export
PCQbind : {q, q' : MLQuiver} ->
  MLQMorph q (PCQuiver q') -> MLQMorph (PCQuiver q) (PCQuiver q')
PCQbind {q} {q'} m = PCQeval q (PCQuiver q') m ?PCQbind_hole_init_alg

public export
PCQmap : {q, q' : MLQuiver} ->
  MLQMorph q q' -> MLQMorph (PCQuiver q) (PCQuiver q')
PCQmap {q} {q'} m = PCQbind {q} {q'} (MLQMcomp ?PCQmap_hole m)

---------------------------
---- Symmetric closure ----
---------------------------

public export
data SCEdge : MLQuiver -> Type where
  SCEv : {0 q : MLQuiver} -> MLQedgeTot q -> SCEdge q
  SCEsym : {0 q : MLQuiver} -> MLQedgeTot q -> SCEdge q

public export
SCsrc : {q : MLQuiver} -> SCEdge q -> MLQvert q
SCsrc {q} (SCEv {q} e) = MLQsrc q e
SCsrc {q} (SCEsym {q} e) = MLQtgt q e

public export
SCtgt : {q : MLQuiver} -> SCEdge q -> MLQvert q
SCtgt {q} (SCEv {q} e) = MLQtgt q e
SCtgt {q} (SCEsym {q} e) = MLQsrc q e

public export
SCQuiverObj : MLQuiver -> WQObj -> Type
SCQuiverObj q WQOvert = MLQvert q
SCQuiverObj q WQOedge = SCEdge q

public export
SCQuiverMorph : (q : MLQuiver) ->
  (m : WQMorph) -> SCQuiverObj q (WQSrc m) -> SCQuiverObj q (WQTgt m)
SCQuiverMorph q WQMsrc = SCsrc {q}
SCQuiverMorph q WQMtgt = SCtgt {q}

-- The symmetric-closure monad (on `Quiv`).
public export
SCQuiver : MLQuiver -> MLQuiver
SCQuiver q = (SCQuiverObj q ** SCQuiverMorph q)

-----------------------------
---- Equivalence closure ----
-----------------------------

-- The equivalence-closure monad (on `Quiv`).
public export
ECQuiver : MLQuiver -> MLQuiver
ECQuiver = PCQuiver . SCQuiver

---------------------------------
---------------------------------
---- Categories from quivers ----
---------------------------------
---------------------------------

-- A quiver is a covariant functor from the walking quiver to the category
-- to which the quiver is internal (in the above definition, that's `Type`).
-- We can now use the notion of "quiver" as a basis for a definition of
-- "category" internal to the same category to which our definition of
-- "quiver" is internal (in this case, Idris's `Type`).
--
-- Specifically, we can define the category of free categories internal to
-- `Type` as the Kleisli category of the path-closure monad on `Quiv`.

public export
KPCQuivObj : Type
KPCQuivObj = MLQuiver

public export
KPCQuivMorph : KPCQuivObj -> KPCQuivObj -> Type
KPCQuivMorph x y = MLQMorph x (PCQuiver y)

public export
KPQMbind : {0 x, y : KPCQuivObj} ->
  KPCQuivMorph x y -> MLQMorph (PCQuiver x) (PCQuiver y)
KPQMbind {x} {y} f = ?KPQMbind_hole

public export
KPQMid : (0 x : KPCQuivObj) -> KPCQuivMorph x x
KPQMid x = ?KPQMid_hole

public export
KPQMcomp : {0 x, y, z : KPCQuivObj} ->
  KPCQuivMorph y z -> KPCQuivMorph x y -> KPCQuivMorph x z
KPQMcomp {x} {y} {z} g f = ?KPQMcomp_hole

-----------------------------------------------
-----------------------------------------------
---- Relations in category-theoretic style ----
-----------------------------------------------
-----------------------------------------------

-----------------------------------------
---- Relations as slices of products ----
-----------------------------------------

public export
CRelation : Type -> Type -> Type
CRelation a b = CSliceObj (a, b)

public export
CEndoRel : Type -> Type
CEndoRel a = CRelation a a

public export
CRelMorph : {0 a, b : Type} -> CRelation a b -> CRelation a b -> Type
CRelMorph {a} {b} = CSliceMorphism {c=(a, b)}

public export
CRelId : {0 a, b : Type} -> (0 r : CRelation a b) -> CRelMorph {a} {b} r r
CRelId {a} {b} = CSliceId {c=(a, b)}

public export
CRelCompose : {0 a, b : Type} -> {0 r, r', r'' : CRelation a b} ->
  CRelMorph r' r'' -> CRelMorph r r' -> CRelMorph r r''
CRelCompose {a} {b} = CSliceCompose {c=(a, b)}

public export
CRelFunctor : Type -> Type -> Type -> Type -> Type
CRelFunctor a b c d = CSliceFunctor (a, b) (c, d)

public export
CEndoRelFunctor : Type -> Type -> Type
CEndoRelFunctor a b = CRelFunctor a a b b

public export
CRelEndofunctor : Type -> Type -> Type
CRelEndofunctor a b = CRelFunctor a b a b

public export
CEndoRelEndofunctor : Type -> Type
CEndoRelEndofunctor a = CRelFunctor a a a a

public export
CRelFAlgMap : {0 a, b : Type} -> CRelEndofunctor a b -> CRelation a b -> Type
CRelFAlgMap {a} {b} f r = CRelMorph {a} {b} (f r) r

public export
CRelFAlg : {a, b : Type} -> CRelEndofunctor a b -> Type
CRelFAlg {a} {b} f = DPair (CRelation a b) (CRelFAlgMap {a} {b} f)

public export
CRelFCoalgMap : {0 a, b : Type} -> CRelEndofunctor a b -> CRelation a b -> Type
CRelFCoalgMap {a} {b} f r = CRelMorph {a} {b} r (f r)

public export
CRelFCoalg : {a, b : Type} -> CRelEndofunctor a b -> Type
CRelFCoalg {a} {b} f = DPair (CRelation a b) (CRelFCoalgMap {a} {b} f)

public export
CRelFMap : {a, b, c, d : Type} -> CRelFunctor a b c d -> Type
CRelFMap {a} {b} {c} {d} f =
  (x, y : CRelation a b) ->
  CRelMorph {a} {b} x y -> CRelMorph {a=c} {b=d} (f x) (f y)

public export
CRelFContramap : {a, b, c, d : Type} -> CRelFunctor a b c d -> Type
CRelFContramap {a} {b} {c} {d} f =
  (x, y : CRelation a b) ->
  CRelMorph {a} {b} x y -> CRelMorph {a=c} {b=d} (f y) (f x)

public export
CRelated : {0 a, b : Type} -> (r : CRelation a b) -> SliceObj (a, b)
CRelated {a} {b} = SliceFromCSlice {c=(a, b)}

-------------------------------
---- Equivalence relations ----
-------------------------------

public export
CRelReflF : {a : Type} -> CEndoRelEndofunctor a
CRelReflF {a} (r ** p) = (Either r a ** eitherElim p $ ProductNTUnit {a})

public export
record IsEquiv {0 a : Type} (r : CEndoRel a) where
  constructor IEQ
  IErefl : (0 x : a) -> CRelated r (x, x)
  IEsym : (0 x, x' : a) -> CRelated r (x, x') -> CRelated r (x', x)
  IEtrans : (0 x, x', x'' : a) ->
    CRelated r (x', x'') -> CRelated r (x, x') -> CRelated r (x, x'')

--------------------------------------------------------
---- Congruence-parameterized categories as quivers ----
--------------------------------------------------------

public export
record CPCat where
  constructor CPC
  cpcObj : Type
  cpcObjEq : Type
  cpcObjEqDom : cpcObjEq -> cpcObj
  cpcObjEqCod : cpcObjEq -> cpcObj
  cpcMorph : Type
  cpcMorphEq : Type
  cpcMorphEqDom : cpcMorphEq -> cpcMorph
  cpcMorphEqCod : cpcMorphEq -> cpcMorph
  cpcDom : cpcMorph -> cpcObj
  cpcCod : cpcMorph -> cpcObj

------------------------------------------------------------
------------------------------------------------------------
---- Presheaf/figure-style diagram/category definitions ----
------------------------------------------------------------
------------------------------------------------------------

------------------------
---- (Co)presheaves ----
------------------------

-- Quivers are functors to `Type` (insofar as we have defined them to this
-- point -- they can be generalized to have arbitrary codomain categories,
-- although the structure of the quiver categories will depend on the structure
-- of the codomain category) from the walking quiver -- that is, using
-- the walking quiver as an index (domain) category.
--
-- The objects of the category of diagrams, when that category is defined
-- as the copresheaf category on the diagram (interpreted as an index
-- category) of diagrams themselves (WQObj/WQMorph).
--
-- A copresheaf is a (covariant) functor, so the _objects_ are
-- (covariant) functors from the `DiagDiag` index category to `Type`.
public export
record DiagCopreshfObj where
  constructor DCObj
  -- If we wrote it in dependent-type-with-universes style rather than
  -- category-theoretic style, DCObj would have type `WQObj -> Type` --
  -- although there are only two objects, so this is also equivalent to
  -- simply two `Type`s.
  DCObj : CSliceObj WQObj

  -- If we wrote it in dependent-type-with-universes style rather than
  -- category-theoretic style, DCMorph would look something like this:
  --  DCMorph : (e : WQMorph) ->
  --    DCObj (copreshfDiagSrc e) -> DCObj (copreshfDiagTgt e)
  -- (There are only two edges, so this is equivalent to simply two functions,
  -- both from the `Type` to which we map `WQOedge` to the type to which
  -- we map `WQOvert`, representing the source and target maps.)
  DCMorph : CSliceMorphism {c=WQMorph} (CQuivDomMap DCObj) (CQuivCodMap DCObj)

-- The objects of the category of diagrams, when that category is defined
-- as the presheaf category on the diagram (interpreted as an index
-- category) of diagrams themselves (WQObj/WQMorph).
--
-- A presheaf is a (contravariant) functor, so the _objects_ are
-- (contravariant) functors from the `DiagDiag` index category to `Type`.
public export
record DiagPreshfObj where
  constructor DPObj
  -- If we wrote it in dependent-type-with-universes style rather than
  -- category-theoretic style, DPObj would have type `WQObj -> Type`.
  -- That's the same type as `DCObj`, but when we interpret diagrams as
  -- presheaves rather than copresheaves, we interpret the edge type
  -- differently; see `DPMorph`.
  DPObj : CSliceObj WQObj

  DPEdgeTot : Type

  -- This is `DPMorph`'s signature backwards, reflecting that we are
  -- now interpreting the diagram as a "generic figure", meaning as a
  -- presheaf (contravariant functor), rather than the usual interpretation
  -- of "diagram" as "(covariant) functor", AKA copresheaf.
  --
  -- That's the same signature as `DPMorph`, but when we interpret diagrams
  -- as presheaves rather than copresheaves, we interpret the source and
  -- target mappings differently (as we must, since they point in opposite
  -- directions).  In this interpretation, rather than mapping each edge
  -- to its source or target respectively, the source mapping maps each
  -- vertex to the set of edges with that vertex as source, and the target
  -- mapping maps each vertex to the set of edges with that vertex as target.
  --
  -- This also means that, while we interpret the vertex type the same way
  -- in both the copresheaf and presheaf interpretations, we interpret the
  -- edge type differently.  In the copresheaf interpretation, it was just
  -- the type of edges.  In the presheaf interpretation, however, because the
  -- source and target mappings produce _sets_ of edges, the edge type in
  -- the presheaf interpretation must be a collection of subobjects of some
  -- type of edges.
  DPMorph : WQMorph -> (DPEdgeTot -> Type)

---------------------
---------------------
---- Prafunctors ----
---------------------
---------------------

-- We should start using `DiagCopreshfObj` instead of the record type below,
-- but we begin with a more explicit but less reflective representation.
-- (IndexCat = DiagCopreshfObj)
public export
record IndexCat where
  constructor IC
  icVert : Type
  icEdge : icVert -> icVert -> Type

-- A copresheaf on `j`, a category (which in this formulation is defined via a
-- diagram in `Type`), is a covariant functor from `j` to `Type`.  As such it
-- is a choice of a type for each vertex and a function for each edge (with
-- domain and codomain matching source and target, respectively).
--
-- (The copresheaves on a given index category `j` themselves form the objects
-- of a functor category, whose morphisms are natural transformations).
public export
record Copresheaf (j : IndexCat) where
  constructor Copreshf
  copreshfObj : icVert j -> Type
  copreshfMorph : (x, y : icVert j) ->
    icEdge j x y -> copreshfObj x -> copreshfObj y

-- A polyomial functor can be given the structure of a prafunctor by assigning
-- a copresheaf to each position and direction.
public export
record PrafunctorData (p : PolyFunc) (dom, cod : IndexCat) where
  constructor PRAF
  praPos : pfPos p -> Copresheaf cod
  praDir : (i : pfPos p) -> pfDir {p} i -> Copresheaf dom

public export
InterpPRAFobj : {p : PolyFunc} -> {dom, cod : IndexCat} ->
  PrafunctorData p dom cod -> Copresheaf dom -> icVert cod -> Type
InterpPRAFobj {p=(pos ** dir)}
  {dom=(IC dvert dedge)} {cod=(IC cvert cedge)} (PRAF prap prad)
  (Copreshf obj morph) cv =
    (i : pos **
     (copreshfObj (prap i) cv,
      (d : dir i) -> (dv : dvert) -> (copreshfObj (prad i d) dv, obj dv)))

public export
InterpPRAFmorph : {p : PolyFunc} -> {dom, cod : IndexCat} ->
  (prad : PrafunctorData p dom cod) -> (domc : Copresheaf dom) ->
  (x, y : icVert cod) -> icEdge cod x y ->
  InterpPRAFobj prad domc x -> InterpPRAFobj prad domc y
InterpPRAFmorph {p=(pos ** dir)}
  {dom=(IC dvert dedge)} {cod=(IC cvert cedge)} (PRAF prap prad)
  (Copreshf obj morph) x y e (i ** (co, m)) =
    (i ** (copreshfMorph (prap i) x y e co, m))

public export
InterpPRAF : {p : PolyFunc} -> {dom, cod : IndexCat} ->
  PrafunctorData p dom cod -> Copresheaf dom -> Copresheaf cod
InterpPRAF prad codc =
  Copreshf (InterpPRAFobj prad codc) (InterpPRAFmorph prad codc)
