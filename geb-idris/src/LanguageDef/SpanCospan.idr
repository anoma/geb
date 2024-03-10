module LanguageDef.SpanCospan

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra

-----------------------------------------------------------------------
-----------------------------------------------------------------------
---- Objects of span and cospan categories in dependent-type style ----
-----------------------------------------------------------------------
-----------------------------------------------------------------------

-- A span is a diagram with three objects and two non-identity arrows, both of
-- which emanate from a common domain, each to one of the other two objects.
-- (The index category underlying such a diagram we call the "span index
-- category".)
--
-- Because that constitutes a DAG (ignoring the identity self-loops), we can
-- equivalently express it as one object (the domain) fibered over two
-- (the codomains).
--
-- The colimit of a span is a pushout, so a span is sometimes called a
-- "pushout diagram".
public export
record SpanObj where
  constructor Span
  spCodL : Type
  spCodR : Type
  spDom : spCodL -> spCodR -> Type

-- A cospan is a diagram with three objects and two non-identity arrows, each
-- of which emanates from a different domain, both to a common domain.
-- (The index category underlying such a diagram we call the "cospan index
-- category".)
--
-- Because that constitutes a DAG (ignoring the identity self-loops), we can
-- equivalently express it as two objects (the domains) each fibered over a
-- single object (the codomain).
--
-- The limit of a span is a pullback, so a cospan is sometimes called a
-- "pullback diagram".
public export
record CospanObj where
  constructor Cospan
  cospCod : Type
  cospDomL : cospCod -> Type
  cospDomR : cospCod -> Type

-------------------------------------------------------------------------
-------------------------------------------------------------------------
---- Morphisms of span and cospan categories in dependent-type style ----
-------------------------------------------------------------------------
-------------------------------------------------------------------------

-- A span is a functor (from the span index category), so a morphism
-- of spans is a natural transformation.  A morphism of spans in `Type` (the
-- base category of the metalanguage), when the spans themselves are
-- represented in dependent-type style as above, can be expressed as
-- metalanguage functions (which are the morphisms of `Type`) between
-- corresponding objects in the diagram, with the commutativity conditions
-- being represented by the functions' respecting the dependent-type
-- relationships.
public export
record SpanMorph (dom, cod : SpanObj) where
  constructor SpanM
  spmCodL : spCodL dom -> spCodL cod
  spmCodR : spCodR dom -> spCodR cod
  spmDom : (l : spCodL dom) -> (r : spCodR dom) ->
    spDom dom l r -> spDom cod (spmCodL l) (spmCodR r)
