module LanguageDef.Figures

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.Atom
import public LanguageDef.RefinedADT
import public LanguageDef.PolyCat
import public LanguageDef.ADTCat

%default total

-----------------------------------------
-----------------------------------------
---- Inductive-inductive definitions ----
-----------------------------------------
-----------------------------------------

-- See
-- https://www.semanticscholar.org/paper/A-Categorical-Semantics-for-Inductive-Inductive-Altenkirch-Morris/4653b2f69670c358063bac0d57d4288fbfe6d52c

--------------------------------
---- Non-indexed definition ----
--------------------------------

public export
FamSetObj : Type
FamSetObj = PolyFunc

public export
FamSetMorph : FamSetObj -> FamSetObj -> Type
FamSetMorph = DirichNatTrans

public export
IndIndF1 : Type
IndIndF1 = FamSetObj -> Type

public export
IndIndAlg : IndIndF1 -> (a : Type) -> (a -> Type) -> Type
IndIndAlg f1 a b = f1 (a ** b) -> a

public export
IndIndF2 : IndIndF1 -> Type
IndIndF2 f1 = (a : Type) -> (b : a -> Type) ->
  IndIndAlg f1 a b -> f1 (a ** b) -> Type

public export
IndInd : Type
IndInd = DPair IndIndF1 IndIndF2

--------------------------------------
---- Indexed/dependent definition ----
--------------------------------------

public export
DepFamSetObj : Type -> Type
DepFamSetObj x = (a : Type ** (x, a) -> Type)

public export
DepFamSetMorph : {x : Type} -> DepFamSetObj x -> DepFamSetObj x -> x -> Type
DepFamSetMorph {x} (a ** b) (a' ** b') elx =
  (onPos : (x, a) -> (x, a') ** SliceMorphism {a=(x, a)} b (b' . onPos))

public export
DepIndIndF1 : Type -> Type
DepIndIndF1 x = DepFamSetObj x -> Type

public export
DepIndIndAlg : {0 x : Type} ->
  DepIndIndF1 x -> (a : Type) -> ((x, a) -> Type) -> Type
DepIndIndAlg {x} f1 a b = f1 (a ** b) -> a

public export
DepIndIndF2 : {x : Type} -> DepIndIndF1 x -> Type
DepIndIndF2 {x} f1 = (a : Type) -> (b : (x, a) -> Type) ->
  DepIndIndAlg {x} f1 a b -> f1 (a ** b) -> Type

public export
DepIndInd : Type -> Type
DepIndInd x = DPair (DepIndIndF1 x) (DepIndIndF2 {x})

---------------------------------------------------------
---- Nat-dependent indexed inductive-inductive types ----
---------------------------------------------------------

public export
NatFamSetObj : Type
NatFamSetObj = DepFamSetObj Nat

public export
NatFamSetMorph : NatFamSetObj -> NatFamSetObj -> Nat -> Type
NatFamSetMorph = DepFamSetMorph {x=Nat}

public export
NatIndIndF1 : Type
NatIndIndF1 = DepIndIndF1 Nat

public export
NatIndIndAlg : NatIndIndF1 -> (a : Type) -> ((Nat, a) -> Type) -> Type
NatIndIndAlg = DepIndIndAlg {x=Nat}

public export
NatIndIndF2 : NatIndIndF1 -> Type
NatIndIndF2 = DepIndIndF2 {x=Nat}

public export
NatIndInd : Type
NatIndInd = DepIndInd Nat

------------------------------
---- Example (SortedList) ----
------------------------------

public export
data ArgSList : NatIndIndF1 where
  SLnil : {0 a : Type} -> {0 b : (Nat, a) -> Type} -> ArgSList (a ** b)
  SLcons : {0 a : Type} -> {0 b : (Nat, a) -> Type} ->
    (n : Nat) -> (ela : a) -> b (n, ela) -> ArgSList (a ** b)

public export
data ArgLteL : NatIndIndF2 ArgSList where
  IsSLnil : {0 a : Type} -> {0 b : (Nat, a) -> Type} ->
    {0 alg : NatIndIndAlg ArgSList a b} -> ArgLteL a b alg (SLnil {a} {b})

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

---------------------------------
---------------------------------
---- Categories from quivers ----
---------------------------------
---------------------------------

---------------------------
---- Quivers in `Type` ----
---------------------------

-- A "strict quiver", where the only equalities (among vertices or edges)
-- are intensional.
public export
record SQuiver where
  constructor SQuiv
  SQVert : Type
  SQEdge : Type
  sqSrc : SQEdge -> SQVert
  sqTgt : SQEdge -> SQVert

---------------
---- Paths ----
---------------

public export
0 IsNeSQPathAcc :
  (sq : SQuiver) -> Type -> SQEdge sq -> List (SQEdge sq) -> Type
IsNeSQPathAcc sq acc e [] = acc
IsNeSQPathAcc sq acc e (e' :: es) =
  IsNeSQPathAcc sq (sqTgt sq e = sqSrc sq e', acc) e' es

public export
0 IsNeSQPathAccDec :
  (sq : SQuiver) -> DecEqPred (SQVert sq) -> (acc : Type) -> Dec acc ->
  (e : SQEdge sq) -> (es : List (SQEdge sq)) -> Dec (IsNeSQPathAcc sq acc e es)
IsNeSQPathAccDec sq veq acc adec e [] = adec
IsNeSQPathAccDec sq veq acc adec e (e' :: es) =
  let
    adec' : Dec (sq .sqTgt e = sq .sqSrc e', acc) =
      case (veq (sqTgt sq e) (sqSrc sq e'), adec) of
        (Yes eq, Yes eacc) => Yes (eq, eacc)
        (No neq, _) => No $ \(eq, eacc) => neq eq
        (_ , No nacc) => No $ \(eq, eacc) => nacc eacc
  in
  IsNeSQPathAccDec sq veq (sqTgt sq e = sqSrc sq e', acc) adec' e' es

public export
0 IsNeSQPath : (sq : SQuiver) -> SQEdge sq -> List (SQEdge sq) -> Type
IsNeSQPath sq = IsNeSQPathAcc sq Unit

public export
0 IsNeSQPathDec : (sq : SQuiver) -> DecEqPred (SQVert sq) ->
  (e : SQEdge sq) -> (es : List (SQEdge sq)) -> Dec (IsNeSQPath sq e es)
IsNeSQPathDec sq veq = IsNeSQPathAccDec sq veq Unit (Yes ())

public export
data SQPathData : SliceObj SQuiver where
  SQPDLoop : {0 sq : SQuiver} -> SQVert sq -> SQPathData sq
  SQPDComp : {0 sq : SQuiver} -> SQEdge sq -> List (SQEdge sq) -> SQPathData sq

public export
sqpdSrc : {sq : SQuiver} -> SQPathData sq -> SQVert sq
sqpdSrc {sq} (SQPDLoop {sq} v) = v
sqpdSrc {sq} (SQPDComp {sq} e es) = sqSrc sq e

public export
sqpdTgt : {sq : SQuiver} -> SQPathData sq -> SQVert sq
sqpdTgt {sq} (SQPDLoop {sq} v) = v
sqpdTgt {sq} (SQPDComp {sq} e es) = case last' es of
  Just e' => sqTgt sq e'
  Nothing => sqTgt sq e

public export
showSQPD : {0 sq : SQuiver} -> (SQVert sq -> String) -> (SQEdge sq -> String) ->
  SQPathData sq -> String
showSQPD {sq} shv she (SQPDLoop v) = shv v
showSQPD {sq} shv she (SQPDComp e es) =
  let Show (SQEdge sq) where show = she in show (e :: es)

public export
(shv : Show (SQVert sq)) => (she : Show (SQEdge sq)) =>
    Show (SQPathData sq) where
  show = showSQPD show show

public export
0 IsSQPath : (sq : SQuiver) -> SQPathData sq -> Type
IsSQPath sq (SQPDLoop {sq} v) = Unit
IsSQPath sq (SQPDComp {sq} e es) = IsNeSQPath sq e es

public export
0 IsSQPathDec : (sq : SQuiver) -> DecEqPred (SQVert sq) ->
  (p : SQPathData sq) -> Dec (IsSQPath sq p)
IsSQPathDec sq veq (SQPDLoop {sq} v) = Yes ()
IsSQPathDec sq veq (SQPDComp {sq} e es) = IsNeSQPathDec sq veq e es

public export
SQuivPath : SQuiver -> Type
SQuivPath sq = Subset0 (SQPathData sq) (IsSQPath sq)

public export
0 isSQPath : (sq : SQuiver) -> DecEqPred (SQVert sq) ->
  (es : SQPathData sq) -> Bool
isSQPath sq veq es = isYes $ IsSQPathDec sq veq es

public export
SQuivPathDec : (sq : SQuiver) -> DecEqPred (SQVert sq) -> Type
SQuivPathDec sq veq = Refinement {a=(SQPathData sq)} (isSQPath sq veq)

public export
sqpSrc : {sq : SQuiver} -> SQuivPath sq -> SQVert sq
sqpSrc {sq} p = sqpdSrc (fst0 p)

public export
sqpTgt : {sq : SQuiver} -> SQuivPath sq -> SQVert sq
sqpTgt {sq} p = sqpdTgt (fst0 p)

----------------------
---- Path closure ----
----------------------

-- The path closure, or reflexive/transitive closure, of a quiver.
public export
SPCQuiver : SQuiver -> SQuiver
SPCQuiver sq = SQuiv (SQVert sq) (SQuivPath sq) (sqpSrc {sq}) (sqpTgt {sq})

---------------------------
---- Symmetric closure ----
---------------------------

public export
data SSCEdge : SQuiver -> Type where
  SSCEv : {0 sq : SQuiver} -> SQEdge sq -> SSCEdge sq
  SSCEsym : {0 sq : SQuiver} -> SQEdge sq -> SSCEdge sq

public export
SSCsrc : {sq : SQuiver} -> SSCEdge sq -> SQVert sq
SSCsrc {sq} (SSCEv {sq} e) = sqSrc sq e
SSCsrc {sq} (SSCEsym {sq} e) = sqTgt sq e

public export
SSCtgt : {sq : SQuiver} -> SSCEdge sq -> SQVert sq
SSCtgt {sq} (SSCEv {sq} e) = sqTgt sq e
SSCtgt {sq} (SSCEsym {sq} e) = sqSrc sq e

public export
SSCQuiver : SQuiver -> SQuiver
SSCQuiver sq = SQuiv (SQVert sq) (SSCEdge sq) (SSCsrc {sq}) (SSCtgt {sq})

-----------------------------
---- Equivalence closure ----
-----------------------------

public export
SECQuiver : SQuiver -> SQuiver
SECQuiver = SPCQuiver . SSCQuiver

---------------------------
---- Symmetric closure ----
---------------------------

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

-- Because there are only two terms in `WQObj`, a function from `WQObj` is
-- is just a slightly abstract way of defining a pair of types.  The reason
-- for doing it this way is that it translates directly to more general
-- situations (in particular, to the definition of (co)presheaves).
public export
QuivObjMap : Type
QuivObjMap = WQObj -> Type

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
QuivDomMap : QuivObjMap -> WQMorph -> Type
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
QuivCodMap : QuivObjMap -> WQMorph -> Type
QuivCodMap = BaseChangeF WQTgt

-- And the category-theoretic style for codomains.
public export
CQuivCodMap : CSliceFunctor WQObj WQMorph
CQuivCodMap = CSBaseChange WQTgt

-- Given an object map, we can take a diagonal of it which maps each
-- object of the walking quiver to a symmetric pair of objects of `Type`.
public export
QuivDiagMap : QuivObjMap -> WQSigT -> Type
QuivDiagMap f (a, b) = (f a, f b)

-- And the category-theoretic style.
public export
CQuivDiagMap : CSliceFunctor WQObj WQSigT
CQuivDiagMap (x ** px) = (ProductMonad x ** mapHom {f=Pair} px)

-- Given an object map, we can take its diagonal and then pull it back
-- along `WQSig` to obtain a mapping from each morphism to a pair made
-- up of a term of its domain together with a term of its codomain.
public export
QuivSigMap : QuivObjMap -> WQMorph -> Type
QuivSigMap = BaseChangeF WQSig . QuivDiagMap

public export
CQuivSigMap : CSliceFunctor WQObj WQMorph
CQuivSigMap = CSBaseChange WQSig . CQuivDiagMap

public export
QuivMorphHom : QuivObjMap -> WQMorph -> Type
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
QuivMorphMap : QuivObjMap -> Type
QuivMorphMap = Pi {a=WQMorph} . QuivMorphHom

public export
CQuivMorphMap : CSliceFunctor WQObj WQMorph
CQuivMorphMap f = CSHomObj (CQuivDomMap f) (CQuivCodMap f)

-- A (metalanguage) quiver, as a functor, is an object map together with a
-- morphism map.
public export
MLQuiver : Type
MLQuiver = Sigma {a=QuivObjMap} QuivMorphMap

-- The morphisms of the (functor) category `Quiv` are natural transformations.
-- The walking quiver has two objects, so a natural transformation has two
-- components.  The target category is `Type`, so each component is simply a
-- function between the targets of the object-map components of the functors
-- (in general, each component of a natural transformation between functors is
-- a morphism in the target category of the functors).
public export
record MLQMorph (dom, cod : MLQuiver) where
  constructor MLQM
  mlqmComponent : SliceMorphism {a=WQObj} (fst dom) (fst cod)

  0 mlqNaturality : (m : WQMorph) ->
    ExtEq
      (mlqmComponent (WQTgt m) . snd dom m)
      (snd cod m . mlqmComponent (WQSrc m))

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
record DiagCoprshfObj where
  constructor DCObj
  -- If we wrote it in dependent-type-with-universes style rather than
  -- category-theoretic style, DCObj would have type `WQObj -> Type` --
  -- although there are only two objects, so this is also equivalent to
  -- simply two `Type`s.
  DCObj : CSliceObj WQObj

  -- If we wrote it in dependent-type-with-universes style rather than
  -- category-theoretic style, DCMorph would look something like this:
  --  DCMorph : (e : WQMorph) ->
  --    DCObj (coprshfDiagSrc e) -> DCObj (coprshfDiagTgt e)
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
record DiagPrshfObj where
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

-- We should start using `DiagCoprshfObj` instead of the record type below,
-- but we begin with a more explicit but less reflective representation.
-- (IndexCat = DiagCoprshfObj)
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
  constructor Coprshf
  coprshfObj : icVert j -> Type
  coprshfMorph : (x, y : icVert j) ->
    icEdge j x y -> coprshfObj x -> coprshfObj y

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
  (Coprshf obj morph) cv =
    (i : pos **
     (coprshfObj (prap i) cv,
      (d : dir i) -> (dv : dvert) -> (coprshfObj (prad i d) dv, obj dv)))

public export
InterpPRAFmorph : {p : PolyFunc} -> {dom, cod : IndexCat} ->
  (prad : PrafunctorData p dom cod) -> (domc : Copresheaf dom) ->
  (x, y : icVert cod) -> icEdge cod x y ->
  InterpPRAFobj prad domc x -> InterpPRAFobj prad domc y
InterpPRAFmorph {p=(pos ** dir)}
  {dom=(IC dvert dedge)} {cod=(IC cvert cedge)} (PRAF prap prad)
  (Coprshf obj morph) x y e (i ** (co, m)) =
    (i ** (coprshfMorph (prap i) x y e co, m))

public export
InterpPRAF : {p : PolyFunc} -> {dom, cod : IndexCat} ->
  PrafunctorData p dom cod -> Copresheaf dom -> Copresheaf cod
InterpPRAF prad codc =
  Coprshf (InterpPRAFobj prad codc) (InterpPRAFmorph prad codc)
