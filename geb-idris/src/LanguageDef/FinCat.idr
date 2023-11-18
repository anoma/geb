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
public export
FinEnrQuiv : Type -> Type
FinEnrQuiv v = (v, v) -> Nat
