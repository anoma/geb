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

-- A cospan is a functor (from the cospan index category), so a morphism
-- of cospans is a natural transformation.  A morphism of cospans in `Type` (the
-- base category of the metalanguage), when the cospans themselves are
-- represented in dependent-type style as above, can be expressed as
-- metalanguage functions (which are the morphisms of `Type`) between
-- corresponding objects in the diagram, with the commutativity conditions
-- being represented by the functions' respecting the dependent-type
-- relationships.
public export
record CospanMorph (dom, cod : CospanObj) where
  constructor CospanM
  cospmCod : cospCod dom -> cospCod cod
  cospmDomL : (ed : cospCod dom) ->
    cospDomL dom ed -> cospDomL cod (cospmCod ed)
  cospmDomR : (ed : cospCod dom) ->
    cospDomR dom ed -> cospDomR cod (cospmCod ed)

---------------------------------------------------------------
---------------------------------------------------------------
---- Adjunctions defining pullbacks and pushouts in `Type` ----
---------------------------------------------------------------
---------------------------------------------------------------

---------------------------
---- Diagonal functors ----
---------------------------

-- The object-map component of the diagonal functor from `Type` to the category
-- of spans in `Type` (which is the functor category from the span index
-- category to `Type`).
--
-- The diagonal functor sends an object `x` of `Type` to the object of the
-- functor category `SpanObj` whose objects are all `x`.  Because we have
-- expressed `SpanObj` in a dependent-type style, we have to represent the
-- common domain as a type which depends upon pairs of terms of `x` yet is
-- equivalent to just `x` itself.  We must pare an input of cardinality
-- `|x|^2` down to one of cardinality `|x|`.
--
-- This is possible, in one straightforward way:  treat the type family as
-- `Void` for all non-diagonal inputs, and `Unit` for all diagonal inputs.
--
-- The effect of this on the implicit morphisms which we have represented in
-- `SpanObj` as type dependencies is to make each morphism the equivalent of the
-- identity morphism (which makes sense because we have mapped each object of
-- the span index category to the same object), as required by the definition
-- of the diagonal functor.
export
SpanDiagObj : Type -> SpanObj
SpanDiagObj x = Span x x (\ex, ex' => ex = ex')

-- The object-map component of the diagonal functor from `Type` to the category
-- of cospans in `Type` (which is the functor category from the cospan index
-- category to `Type`).
--
-- In this case, dually for what we had to do with `SpanDiagObj`, we must make
-- the common codomain simply `x`, and make each of the common domains a type
-- (family) which depends upon terms of `x` yet is equivalent to simply `x`.
-- This we can do by making each type of the family `Unit`.
export
CospanDiagObj : Type -> CospanObj
CospanDiagObj x = Cospan x (\_ => Unit) (\_ => Unit)

-- The morphism-map component of the diagonal functor from `Type` to the
-- category of spans in `Type`.
--
-- The diagonal functor takes each morphism of `Type` to the identity morphism
-- in the category of spans (which is sensible because it takes each object of
-- the span index category to the same object).
export
SpanDiagMorph : (0 x, y : Type) ->
  (x -> y) -> SpanMorph (SpanDiagObj x) (SpanDiagObj y)
SpanDiagMorph x y f = SpanM f f (\l, r, eqlr => cong f eqlr)

-- The morphism-map component of the diagonal functor from `Type` to the
-- category of cospans in `Type`, defined dually to `SpanDiagMorph`.
export
CospanDiagMorph : (0 x, y : Type) ->
  (x -> y) -> CospanMorph (CospanDiagObj x) (CospanDiagObj y)
CospanDiagMorph x y f = CospanM f (\_, _ => ()) (\_, _ => ())

-------------------------------------------------------
---- Pushouts/pullbacks as co(limits) of (co)spans ----
-------------------------------------------------------

-- The pushout functor from the category of spans to `Type` is left
-- adjoint to the diagonal functor (pushouts are colimits).
--
-- In the pushout-defining functor, therefore,
-- `SpanDiagObj`/`SpanDiagMorph` is the right adjoint.
--
-- The pullback functor from the category of cospans to `Type` is right
-- adjoint to the diagonal functor (pullbacks are limits).
--
-- In the pullback-defining functor, therefore,
-- `CospanDiagObj`/`CospanDiagMorph` is the left adjoint.

-- To compute the left adjoint of the pushout adjunction -- the pushout
-- functor -- we reason as follows:  if `L` is the pushout functor, `R` is
-- the span-diagonal functor, `a` is a span, and `b` is an object of `Type`,
-- then `L a -> b ~=~ a -> R b`; hence, `L a` must be "that which is eliminated
-- [to a given `b`] by an `a -> R b` [which is a `SpanMorph`]".  For it to be
-- possible to map out (eliminate) the pushout to `b` by an `a -> R b` means
-- that we must have a natural transformation:  for each `b`, we can get from
-- `a -> R b` to `b`.  Hence we define:
export
PushoutElimSig : SpanObj -> Type -> Type
PushoutElimSig = (|>) SpanDiagObj . SpanMorph

export
PushoutLAdjointObj : SpanObj -> Type
PushoutLAdjointObj =
  flip NaturalTransformation (id {a=Type}) . PushoutElimSig

-- Note that we could also have defined the left adjoint of the pullback
-- functor via an existential quantifier rather than a universal one,
-- as follows -- note however that the definition is partial, because it is
-- recursive with the type being defined in a negative position, so
-- for left adjoints we use the universal forms:
export
partial
data PushoutLAdjointObjExist : SpanObj -> Type where
  PLAOE : {0 a : SpanObj} ->
    NaturalTransformation
      (HomProf (PushoutLAdjointObjExist a))
      (PushoutElimSig a) ->
    PushoutLAdjointObjExist a

-- To compute the right adjoint of the pullback adjunction -- the pullback
-- functor -- we reason as follows:  if `R` is the pullback functor, `L` is
-- the cospan-diagonal functor, `a` is an object of `Type`, and `b` is a cospan,
-- then `L a -> b ~=~ a -> R b`; hence, `R b` must be "that which is introduced
-- [from a given `a`] by an `L a -> b` [which is a `CospanMorph`]".  Hence we
-- define:
export
PullbackIntroSig : Type -> CospanObj -> Type
PullbackIntroSig = CospanMorph . CospanDiagObj

export
PullbackRAdjointObj : CospanObj -> Type
PullbackRAdjointObj = Exists {type=Type} . flip PullbackIntroSig

-- Note that we could also have defined the right adjoint of the pullback
-- functor via a universal quantifier rather than an existential one,
-- as follows -- note however that the definition is recursive, so for
-- right adjoints we use the existential form:
export
data PullbackRAdjointObjUniv : CospanObj -> Type where
  PRAOU : {0 b : CospanObj} ->
    NaturalTransformation
      (flip PullbackIntroSig b)
      (flip HomProf (PullbackRAdjointObjUniv b)) ->
    PullbackRAdjointObjUniv b
