module LanguageDef.Figures

import Library.IdrisUtils
import Library.IdrisCategories
import public LanguageDef.Atom
import public LanguageDef.RefinedADT
import public LanguageDef.PolyCat

%default total

------------------------------------------------------------
------------------------------------------------------------
---- Presheaf/figure-style diagram/category definitions ----
------------------------------------------------------------
------------------------------------------------------------

------------------
---- Diagrams ----
------------------

-- The vertices of the diagram, which, when interpreted as an index
-- category for presheaves or copreasheaves (depending on the directions
-- of the edges), defines the category of diagrams.
public export
data DiagDiagVert : Type where
  DDVvert : DiagDiagVert
  DDVedge : DiagDiagVert

-- The edges of the diagram which, when interpreted as an index category
-- for (co)presheaves, defines the category of diagrams.
public export
data DiagDiagEdge : Type where
  DDEsrc : DiagDiagEdge
  DDEtgt : DiagDiagEdge

-- The sources of the edges of the diagram which, when interpreted as an
-- index category for copresheaves, defines the category of diagrams.
public export
CoprshfDiagSrc : DiagDiagEdge -> DiagDiagVert
CoprshfDiagSrc = const DDVedge

public export
CDSbc : CSliceObj DiagDiagVert -> CSliceObj DiagDiagEdge
CDSbc = CSBaseChange CoprshfDiagSrc

-- The targets of the edges of the diagram which, when interpreted as an
-- index category for copresheaves, defines the category of diagrams.
public export
CoprshfDiagTgt : DiagDiagEdge -> DiagDiagVert
CoprshfDiagTgt = const DDVvert

public export
CDTbc : CSliceObj DiagDiagVert -> CSliceObj DiagDiagEdge
CDTbc = CSBaseChange CoprshfDiagTgt

-- The sources of the edges of the diagram which, when interpreted as an
-- index category for presheaves, defines the category of diagrams.
-- (Such an index category is sometimes called a "generic figure").
public export
PrshfDiagSrc : DiagDiagEdge -> DiagDiagVert
PrshfDiagSrc = CoprshfDiagTgt

public export
PDSbc : CSliceObj DiagDiagVert -> CSliceObj DiagDiagEdge
PDSbc = CSBaseChange PrshfDiagSrc

-- The targets of the edges of the diagram which, when interpreted as an
-- index category for presheaves, defines the category of diagrams.
public export
PrshfDiagTgt : DiagDiagEdge -> DiagDiagVert
PrshfDiagTgt = CoprshfDiagSrc

public export
PDTbc : CSliceObj DiagDiagVert -> CSliceObj DiagDiagEdge
PDTbc = CSBaseChange PrshfDiagTgt

------------------------
---- (Co)presheaves ----
------------------------

-- The objects of the category of diagrams, when that category is defined
-- as the copresheaf category on the diagram (interpreted as an index
-- category) of diagrams themselves (DiagDiagVert/DiagDiagEdge).
--
-- A copresheaf is a (covariant) functor, so the _objects_ are
-- (covariant) functors from the `DiagDiag` index category to `Type`.
public export
record DiagCoprshfObj where
  constructor DCObj
  -- If we wrote it in dependent-type-with-universes style rather than
  -- category-theoretic style, DCObj would have type `DiagDiagVert -> Type` --
  -- although there are only two objects, so this is also equivalent to
  -- simply two `Type`s.
  DCObj : CSliceObj DiagDiagVert

  -- If we wrote it in dependent-type-with-universes style rather than
  -- category-theoretic style, DCMorph would look something like this:
  --  DCMorph : (e : DiagDiagEdge) ->
  --    DCObj (coprshfDiagSrc e) -> DCObj (coprshfDiagTgt e)
  -- (There are only two edges, so this is equivalent to simply two functions,
  -- both from the `Type` to which we map `DDVedge` to the type to which
  -- we map `DDVvert`, representing the source and target maps.)
  DCMorph : CSliceMorphism {c=DiagDiagEdge} (CDSbc DCObj) (CDTbc DCObj)

-- The objects of the category of diagrams, when that category is defined
-- as the presheaf category on the diagram (interpreted as an index
-- category) of diagrams themselves (DiagDiagVert/DiagDiagEdge).
--
-- A presheaf is a (contravariant) functor, so the _objects_ are
-- (contravariant) functors from the `DiagDiag` index category to `Type`.
public export
record DiagPrshfObj where
  constructor DPObj
  -- If we wrote it in dependent-type-with-universes style rather than
  -- category-theoretic style, DPObj would have type `DiagDiagVert -> Type`.
  -- That's the same type as `DCObj`, but when we interpret diagrams as
  -- presheaves rather than copresheaves, we interpret the edge type
  -- differently; see `DPMorph`.
  DPObj : CSliceObj DiagDiagVert

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
  DPMorph : CSliceMorphism {c=DiagDiagEdge} (PDSbc DPObj) (PDTbc DPObj)
