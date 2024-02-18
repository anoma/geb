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
record TQPresheaf (v : Type) (e : TypeQuivV v) where
  constructor TQPre
  tqpOmap : SliceObj v
  tqpFmap : TypeQuivPreshfMmap {v} e tqpOmap

record TQCopresheaf (v : Type) (e : TypeQuivV v) where
  constructor TQCopre
  tqcOmap : SliceObj v
  tqcFmap : TypeQuivCopreshfMmap {v} e tqcOmap

-------------------------------------
-------------------------------------
---- Kan extensions from quivers ----
-------------------------------------
-------------------------------------

public export
TypeQuivDimapSig : {v : Type} -> TypeQuivV v -> (v -> v -> Type) -> Type
TypeQuivDimapSig {v} q p =
  (a, b, c, d : v) -> q (c, a) -> q (b, d) -> p a b -> p c d

public export
TypeQuivLmapSig : {v : Type} -> TypeQuivV v -> (v -> v -> Type) -> Type
TypeQuivLmapSig {v} q p = (a, b, c : v) -> q (b, a) -> p a c -> p b c

public export
TypeQuivRmapSig : {v : Type} -> TypeQuivV v -> (v -> v -> Type) -> Type
TypeQuivRmapSig {v} q p = (a, b, c : v) -> q (a, b) -> p c a -> p c b

--------------------------------------------------
--------------------------------------------------
---- Functors in free-(co)presheaf categories ----
--------------------------------------------------
--------------------------------------------------

-- The object-map component of a functor in a presheaf category.
public export
TypeQuivPreshfFunctor : {v, w : Type} -> TypeQuivV v -> TypeQuivV w -> Type
TypeQuivPreshfFunctor {v} {w} qv qw =
  TQPresheaf v qv -> TQPresheaf w qw

-- The object-map component of a functor in a copresheaf category.
public export
TypeQuivCopreshfFunctor : {v, w : Type} -> TypeQuivV v -> TypeQuivV w -> Type
TypeQuivCopreshfFunctor {v} {w} qv qw =
  TQCopresheaf v qv -> TQCopresheaf w qw

---------------------------------
---------------------------------
---- Categories from quivers ----
---------------------------------
---------------------------------
