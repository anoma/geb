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
  -- category-theoretic style, DCObj would hae type `DiagDiagVert -> Type` --
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
  DCMorph :
    CSliceMorphism {c=DiagDiagEdge}
      (CSBaseChange {c=DiagDiagVert} {d=DiagDiagEdge} CoprshfDiagSrc DCObj)
      (CSBaseChange {c=DiagDiagVert} {d=DiagDiagEdge} CoprshfDiagTgt DCObj)

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
  -- category-theoretic style, DPObj would hae type `DiagDiagVert -> Type`.
  DPObj : CSliceObj DiagDiagVert

  -- This is `DPMorph`'s signature backwards, reflecting that we are
  -- now interpreting the diagram as a "generic figure", meaning as a
  -- presheaf (contravariant functor), rather than the usual interpretation
  -- of "diagram" as "(covariant) functor", AKA copresheaf.
  DPMorph :
    CSliceMorphism {c=DiagDiagEdge}
      (CSBaseChange {c=DiagDiagVert} {d=DiagDiagEdge} PrshfDiagSrc DPObj)
      (CSBaseChange {c=DiagDiagVert} {d=DiagDiagEdge} PrshfDiagTgt DPObj)
