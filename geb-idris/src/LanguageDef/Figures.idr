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

-- The targets of the edges of the diagram which, when interpreted as an
-- index category for copresheaves, defines the category of diagrams.
public export
CoprshfDiagTgt : DiagDiagEdge -> DiagDiagVert
CoprshfDiagTgt = const DDVvert

-- The sources of the edges of the diagram which, when interpreted as an
-- index category for presheaves, defines the category of diagrams.
-- (Such an index category is sometimes called a "generic figure").
public export
PrshfDiagSrc : DiagDiagEdge -> DiagDiagVert
PrshfDiagSrc = CoprshfDiagTgt

-- The targets of the edges of the diagram which, when interpreted as an
-- index category for presheaves, defines the category of diagrams.
public export
PrshfDiagTgt : DiagDiagEdge -> DiagDiagVert
PrshfDiagTgt = CoprshfDiagSrc

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
  -- category-theoretic style, DCObjMap would hae type `DiagDiagVert -> Type`.
  DCObjMap : CSliceObj DiagDiagVert

  -- If we wrote it in dependent-type-with-universes style rather than
  -- category-theoretic style, DCMorphMap would look something like this:
  --  DCMorphMap : (e : DiagDiagEdge) ->
  --    DCObjMap (coprshfDiagSrc e) -> DCObjMap (coprshfDiagTgt e)
  DCMorphMap :
    CSliceMorphism {c=DiagDiagEdge}
      (CSBaseChange {c=DiagDiagVert} {d=DiagDiagEdge} CoprshfDiagSrc DCObjMap)
      (CSBaseChange {c=DiagDiagVert} {d=DiagDiagEdge} CoprshfDiagTgt DCObjMap)

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
  -- category-theoretic style, DPObjMap would hae type `DiagDiagVert -> Type`.
  DPObjMap : CSliceObj DiagDiagVert

  -- This is `DPMorphMap`'s signature backwards, reflecting that we are
  -- now interpreting the diagram as a "generic figure", meaning as a
  -- presheaf (contravariant functor), rather than the usual interpretation
  -- of "diagram" as "(covariant) functor", AKA copresheaf.
  DPMorphMap :
    CSliceMorphism {c=DiagDiagEdge}
      (CSBaseChange {c=DiagDiagVert} {d=DiagDiagEdge} PrshfDiagSrc DPObjMap)
      (CSBaseChange {c=DiagDiagVert} {d=DiagDiagEdge} PrshfDiagTgt DPObjMap)
