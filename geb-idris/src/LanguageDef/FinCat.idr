module LanguageDef.FinCat

import Library.IdrisUtils
import Library.IdrisCategories

--------------------------
--------------------------
---- Finitary quivers ----
--------------------------
--------------------------

-- A quiver enriched over `FinSet` is one whose edge-objects are drawn
-- from `FinSet` -- in other words, whose edge-sets are all finite.
-- Such a quiver need not necessarily have a finite number of _vertices_.
-- A `FinEnrQuivV v` is one whose vertex-object, which is an object of
-- the metalanguage's core category (`Type`), is `v`.
public export
FinEnrQuivV : Type -> Type
FinEnrQuivV v = (v, v) -> Nat

-- A quiver internal to `FinSet` is one whose vertex-objects _and_
-- edge-objects are drawn from `FinSet`, so it has finite numbers of
-- both vertices and edges.  A `FinIntQuivN n` is one with `n` vertices.
public export
FinIntQuivN : Nat -> Type
FinIntQuivN = FinEnrQuivV . Fin
