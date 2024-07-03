module LanguageDef.Quiver

import Library.IdrisUtils
import Library.IdrisCategories

%default total

-----------------
-----------------
---- Quivers ----
-----------------
-----------------

--------------------------------------------------
---- Quivers internal to arbitrary categories ----
--------------------------------------------------

-- An enriched quiver internal to a category which is itself internal to `Type`
-- is one whose edge-objects are drawn from some arbitrary category internal to
-- `Type` (possibly `Type` itself, which is self-enriched), and whose vertex
-- object comes from some other arbitrary category internal to `Type` (again
-- possibly `Type` itself).  A `QuivVE {vb} vp v e` is one whose vertex
-- category's objects are indexed by `vb` and are of the form `vb v'` for
-- some `v' : vb`, whose specific vertex-object is `v`, and whose edge-objects
-- are drawn from `e`.
public export
QuivVE : {0 vb : Type} -> SliceObj vb -> vb -> Type -> Type
QuivVE {vb} vp v = HomProf (ProductMonad $ vp v)

---------------------------------------------
---- Enriched quivers internal to `Type` ----
---------------------------------------------

-- An enriched quiver internal to `Type` is one whose edge-objects are drawn
-- from some arbitrary category internal to `Type` (possibly `Type` itself,
-- which is self-enriched), and whose vertex object comes from `Type` itself.
-- An `EnrQuivVE v e` is one whose vertex-object is `v` and whose edge-objects
-- are drawn from `e`.
public export
EnrQuivVE : Type -> Type -> Type
EnrQuivVE = QuivVE {vb=Type} id

------------------------------------------
---- `Type`-internal/enriched quivers ----
------------------------------------------

-- A quiver internal to and enriched over `Type` is one whose vertex object
-- and edge-objects are drawn from `Type`, the core category of the
-- metalanguage.  A `TypeQuivV v` is one whose vertex-object is `v`.
public export
TypeQuivV : Type -> Type
TypeQuivV = flip EnrQuivVE Type

-----------------------------------
---- `FinSet`-enriched quivers ----
-----------------------------------

-- A quiver internal to `Type` and enriched over `FinSet` is one whose
-- edge-objects are drawn from `FinSet` -- in other words, whose edge-sets are
-- all finite.  Such a quiver need not necessarily have a finite number of
-- _vertices_.  A `FinEnrQuivV v` is a `FinSet`-enriched quiver whose
-- vertex-object, which is an object of the metalanguage's core category
-- (`Type`), is `v`.
public export
FinEnrQuivV : Type -> Type
FinEnrQuivV = flip EnrQuivVE Nat

-----------------------------------
---- `FinSet`-internal quivers ----
-----------------------------------

-- A quiver internal to and enriched over `FinSet` is one whose vertex-objects
-- _and_ edge-objects are drawn from `FinSet`, so it has finite numbers of
-- both vertices and edges.  A `FinQuivN n` is one with `n` vertices.
public export
FinQuivN : Nat -> Type
FinQuivN = FinEnrQuivV . Fin

---------------------------
---- Reflexive quivers ----
---------------------------

-- A reflexive quiver is a quiver where every vertex has a distinguished
-- self-loop.

-- A reflexive quiver internal to and enriched over `Type` is one whose
-- vertex-object and edge-objects are drawn from `Type`, the core category
-- of the metalanguage, together with a distinguished self-loop for each vertex.
-- A `TypeRQuivSL {v} q` is a selection from a `TypeQuivV v` of self-loops for
-- each vertex object (which makes it a reflexive `Type-internal-and-enriched
-- quiver).
public export
TypeRQuivSL : {v : Type} -> TypeQuivV v -> Type
TypeRQuivSL {v} q = (x : v) -> q (x, x)

-- A reflexive quiver internal to `Type` and enriched over `FinSet` is a
-- reflexive quiver whose edge-objects are drawn from `FinSet`.
-- A `FinEnrQuivSL {v} q` is a selection from a `FinEnrQuivV v` of self-loops
-- for each vertex object (which makes it a reflexive
-- `Type-internal/FinSet-enriched quiver).
public export
FinEnrQuivSL : {v : Type} -> FinEnrQuivV v -> Type
FinEnrQuivSL {v} q = TypeRQuivSL {v} (Fin . q)

-- A reflexive quiver internal to and enriched over `FinSet` is one whose
-- vertex-objects _and_ edge-objects are drawn from `FinSet`, so it has finite
-- numbers of both vertices and edges.  A `FinQuivSL {n} q` is a selection
-- from a `FinQuivN n` of self-loops for each vertex object (which makes it
-- a reflexive FinSet-internal-and-enriched quiver).
public export
FinQuivSL : {n : Nat} -> FinQuivN n -> Type
FinQuivSL {n} = FinEnrQuivSL {v=(Fin n)}

-------------------------------
---- Compositional quivers ----
-------------------------------

-- A compositional quiver is a quiver with an assignment of each pair of
-- edges into and out of a shared vertex -- `x -- e --> y --> e' -- z` --
-- to a single edge following the same path -- `x -- e'' --> z`.

public export
TypeCQuivComp : {v : Type} -> TypeQuivV v -> Type
TypeCQuivComp {v} q = (x, y, z : v) -> q (y, z) -> q (x, y) -> q (x, z)

public export
FinEnrQuivComp : {v : Type} -> FinEnrQuivV v -> Type
FinEnrQuivComp {v} q = TypeCQuivComp {v} (Fin . q)

public export
FinQuivComp : {n : Nat} -> FinQuivN n -> Type
FinQuivComp {n} = FinEnrQuivComp {v=(Fin n)}

----------------------
---- "Proquivers" ----
----------------------

-- What we shall call a "proquiver" is a quiver of the shape which underlies
-- a profunctor, as a quiver is the shape which underlies a category.  The
-- shape of a proquiver is that of the collage (or "cograph") of a
-- profunctor, which allows a profunctor to be viewed as a pair of categories
-- with morphisms in one direction between them.

-- An enriched proquiver internal to a category which is itself internal to
-- `Type` is one whose two edge-objects are drawn from some arbitrary categories
-- internal to `Type` (possibly `Type` itself, which is self-enriched), and
-- whose two vertex objects come from some other arbitrary categories internal
-- to `Type` (again possibly `Type` itself), and whose het-object is drawn from
-- some arbitrary category internal to type.  A
-- `ProquivVE {vb} {vb'} vp vp' v v' e e' h` is one whose vertex
-- categories' objects are indexed by `vb` and `vb`' and are of the form
-- `vb v` or `vb' v'` for some `v : vb` or `v' : vb'`, whose specific
-- vertex-objects are `v` and `v'`, whose edge-objects are drawn from `e` and
-- `e'`, and whose het-objects are drawn from `h`.
public export
record ProquivVE {0 vb, vb' : Type} (vp : SliceObj vb) (vp' : SliceObj vb')
    (v : vb) (v' : vb') (e, e', h : Type) where
  constructor Proquiv
  prqContra : QuivVE {vb} vp v e
  prqCovar : QuivVE {vb=vb'} vp' v' e'
  prqHet : (vp v, vp' v') -> h

-- An enriched proquiver internal to `Type` is one whose edge-objects are drawn
-- from arbitrary categories internal to `Type` (possibly `Type` itself,
-- which is self-enriched), and whose vertex objects come from `Type` itself.
-- The five `Type` parameters are two vertex objects, two edge types, and one
-- het-type.
public export
EnrProquivVE : Type -> Type -> Type -> Type -> Type -> Type
EnrProquivVE = ProquivVE {vb=Type} {vb'=Type} id id

-- A proquiver internal to and enriched over `Type` is one whose vertex objects,
-- edge-objects, and het-object are drawn from `Type`, the core category of the
-- metalanguage.
public export
TypeProquivV : Type -> Type -> Type
TypeProquivV v v' = EnrProquivVE v v' Type Type Type

-------------------
---- Diquivers ----
-------------------

-- A diquiver is a symmetric proquiver -- one whose two quivers are the same.
public export
record DiquivVE {0 vb : Type} (vp : SliceObj vb) (v : vb) (e, h : Type) where
  constructor Diqquiv
  dqQuiv : QuivVE {vb} vp v e
  dqHet : (vp v, vp v) -> h

public export
EnrDiquivVE : Type -> Type -> Type -> Type
EnrDiquivVE = DiquivVE {vb=Type} id

public export
TypeDiquivV : Type -> Type
TypeDiquivV v = EnrDiquivVE v Type Type
