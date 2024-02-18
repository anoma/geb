module LanguageDef.MLQuivCat

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.Quiver

-----------------------------------
-----------------------------------
---- (Co)presheaves on quivers ----
-----------------------------------
-----------------------------------

----------------------------------------------
---- Internal to and enriched over `Type` ----
----------------------------------------------

-- Given a quiver internal to and enriched over `Type` and a slice object
-- over its vertex object -- the latter of which may be treated as the
-- object-map component of a functor from the free category on the quiver to
-- `Type` (a "presheaf", if the functor is contravariant, or "copresheaf", if
-- it is covariant) -- this is the type of the morphism-map component of such a
-- contravariant functor (presheaf).
public export
TypeQuivPreshfMmap : {v : Type} -> TypeQuivV v -> SliceObj v -> Type
TypeQuivPreshfMmap {v} q sl =
  (dom, cod : v) -> q (cod, dom) -> sl dom -> sl cod

-- Given a quiver internal to and enriched over `Type` and a slice object
-- over its vertex object -- the latter of which may be treated as the
-- object-map component of a functor from the free category on the quiver to
-- `Type` (a "presheaf", if the functor is contravariant, or "copresheaf", if
-- it is covariant) -- this is the type of the morphism-map component of such a
-- covariant functor (copresheaf).
public export
TypeQuivCopreshfMmap : {v : Type} -> TypeQuivV v -> SliceObj v -> Type
TypeQuivCopreshfMmap {v} q sl =
  (dom, cod : v) -> q (dom, cod) -> sl dom -> sl cod

--------------------------------
---- Enriched over `FinSet` ----
--------------------------------

-- Given a quiver internal to `Type` but enriched over `FinSet`, and a slice
-- object over its vertex object -- the latter of which may be treated as the
-- object-map component of a functor from the free category on the quiver to
-- `Type` (a "presheaf", if the functor is contravariant, or "copresheaf", if
-- it is covariant) -- this is the type of the morphism-map component of such a
-- contravariant functor (presheaf).
public export
FinEnrQuivPreshfMmap : {v : Type} -> FinEnrQuivV v -> SliceObj v -> Type
FinEnrQuivPreshfMmap {v} q = TypeQuivPreshfMmap {v} (Fin . q)

-- Given a quiver internal to `Type` but enriched over `FinSet`, and a slice
-- object over its vertex object -- the latter of which may be treated as the
-- object-map component of a functor from the free category on the quiver to
-- `Type` (a "presheaf", if the functor is contravariant, or "copresheaf", if
-- it is covariant) -- this is the type of the morphism-map component of such a
-- contravariant functor (presheaf).
public export
FinEnrQuivCopreshfMmap : {v : Type} -> FinEnrQuivV v -> SliceObj v -> Type
FinEnrQuivCopreshfMmap {v} q = TypeQuivCopreshfMmap {v} (Fin . q)

------------------------------------------------
---- Internal to and enriched over `FinSet` ----
------------------------------------------------

-- Given a quiver internal to and enriched over `FinSet`, and a slice
-- object over its vertex object -- the latter of which may be treated as the
-- object-map component of a functor from the free category on the quiver to
-- `Type` (a "presheaf", if the functor is contravariant, or "copresheaf", if
-- it is covariant) -- this is the type of the morphism-map component of such a
-- contravariant functor (presheaf).
public export
FinQuivPreshfMmap : {n : Nat} -> FinQuivN n -> FinSliceObj n -> Type
FinQuivPreshfMmap {n} q = TypeQuivPreshfMmap {v=(Fin n)} (Fin . q)

-- Given a quiver internal to and enriched over `FinSet`, and a slice
-- object over its vertex object -- the latter of which may be treated as the
-- object-map component of a functor from the free category on the quiver to
-- `Type` (a "presheaf", if the functor is contravariant, or "copresheaf", if
-- it is covariant) -- this is the type of the morphism-map component of such a
-- covariant functor (copresheaf).
public export
FinQuivCopreshfMmap : {n : Nat} -> FinQuivN n -> FinSliceObj n -> Type
FinQuivCopreshfMmap {n} q = TypeQuivCopreshfMmap {v=(Fin n)} (Fin . q)

-- A presheaf into `Type` from an internal category with object type `v`
-- and morphism type `e`, defined by a quiver.
public export
record TQPresheaf (v : Type) (e : TypeQuivV v) where
  constructor TQPre
  tqpOmap : SliceObj v
  tqpFmap : TypeQuivPreshfMmap {v} e tqpOmap

public export
record TQCopresheaf (v : Type) (e : TypeQuivV v) where
  constructor TQCopre
  tqcOmap : SliceObj v
  tqcFmap : TypeQuivCopreshfMmap {v} e tqcOmap

-----------------------------------------------------------------
-----------------------------------------------------------------
---- Endo-profunctors ("difunctors"/"prosheaves") on quivers ----
-----------------------------------------------------------------
-----------------------------------------------------------------

public export
TypeQuivProshfSig : (v : Type) -> Type
TypeQuivProshfSig v = v -> v -> Type

public export
TypeQuivDimapSig : {v : Type} -> TypeQuivV v -> TypeQuivProshfSig v -> Type
TypeQuivDimapSig {v} q p =
  (a, b, c, d : v) -> q (c, a) -> q (b, d) -> p a b -> p c d

public export
TypeQuivLmapSig : {v : Type} -> TypeQuivV v -> TypeQuivProshfSig v -> Type
TypeQuivLmapSig {v} q p = (a, b, c : v) -> q (b, a) -> p a c -> p b c

public export
TypeQuivRmapSig : {v : Type} -> TypeQuivV v -> TypeQuivProshfSig v -> Type
TypeQuivRmapSig {v} q p = (a, b, c : v) -> q (a, b) -> p c a -> p c b

---------------------------------
---------------------------------
---- Categories from quivers ----
---------------------------------
---------------------------------
