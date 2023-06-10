module LanguageDef.Figures

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.RefinedADT
import public LanguageDef.PolyCat

%default total

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
--
-- Here we do _not_ use a category-theory-style `CSliceObj`, nor even call
-- this a `SliceObject` -- because we are going to represent it in Geb as
-- an internal functor, there will be a type of Geb which represents the
-- objects of the target category, which will replace `Type` here.
public export
QuivObjMap : Type
QuivObjMap = WQObj -> Type

-- The category-theoretic form of `QuivObjMap`.
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
QuivMorphMap f = SliceMorphism {a=WQMorph} (QuivDomMap f) (QuivCodMap f)

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
