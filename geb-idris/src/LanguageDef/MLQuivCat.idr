module LanguageDef.MLQuivCat

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.Quiver

-------------------------------
-------------------------------
---- Quivers as a category ----
-------------------------------
-------------------------------

public export
record TQuivObj where
  constructor TQO
  tqV : Type
  tqE : TypeQuivV tqV

public export
TQVP : TQuivObj -> Type
TQVP = ProductMonad . tqV

public export
record TQuivMorph (dom, cod : TQuivObj) where
  constructor TQM
  tqmV : tqV dom -> tqV cod
  tqmE : SliceMorphism {a=(TQVP dom)} (tqE dom) (tqE cod . mapHom tqmV)

export
TQMvmap : {0 dom, cod : TQuivObj} -> TQuivMorph dom cod -> TQVP dom -> TQVP cod
TQMvmap {dom} {cod} = mapHom . tqmV

public export
tqId : (q : TQuivObj) -> TQuivMorph q q
tqId q = TQM id (\vp => case vp of (_, _) => id)

public export
tqComp : {q, r, s : TQuivObj} ->
  TQuivMorph r s -> TQuivMorph q r -> TQuivMorph q s
tqComp {q} {r} {s} m' m =
  TQM
    (tqmV m' . tqmV m)
    (\qp => case qp of
      (qv, qv') => tqmE m' (TQMvmap m (qv, qv')) . tqmE m (qv, qv'))

-----------------------------------
-----------------------------------
---- (Co)presheaves on quivers ----
-----------------------------------
-----------------------------------

----------------------------------------------
---- Internal to and enriched over `Type` ----
----------------------------------------------

public export
TypeQuivPreshfSig : (v : Type) -> Type
TypeQuivPreshfSig = SliceObj

public export
TypeQuivCopreshfSig : (v : Type) -> Type
TypeQuivCopreshfSig = SliceObj

-- Given a quiver internal to and enriched over `Type` and a slice object
-- over its vertex object -- the latter of which may be treated as the
-- object-map component of a functor from the free category on the quiver to
-- `Type` (a "presheaf", if the functor is contravariant, or "copresheaf", if
-- it is covariant) -- this is the type of the morphism-map component of such a
-- contravariant functor (presheaf).
public export
TypeQuivPreshfMmap : {v : Type} ->
  TypeQuivV v -> TypeQuivPreshfSig v -> Type
TypeQuivPreshfMmap {v} q sl =
  (dom, cod : v) -> q (cod, dom) -> sl dom -> sl cod

-- Given a quiver internal to and enriched over `Type` and a slice object
-- over its vertex object -- the latter of which may be treated as the
-- object-map component of a functor from the free category on the quiver to
-- `Type` (a "presheaf", if the functor is contravariant, or "copresheaf", if
-- it is covariant) -- this is the type of the morphism-map component of such a
-- covariant functor (copresheaf).
public export
TypeQuivCopreshfMmap : {v : Type} ->
  TypeQuivV v -> TypeQuivCopreshfSig v -> Type
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
FinEnrQuivPreshfMmap : {v : Type} ->
  FinEnrQuivV v -> TypeQuivPreshfSig v -> Type
FinEnrQuivPreshfMmap {v} q = TypeQuivPreshfMmap {v} (Fin . q)

-- Given a quiver internal to `Type` but enriched over `FinSet`, and a slice
-- object over its vertex object -- the latter of which may be treated as the
-- object-map component of a functor from the free category on the quiver to
-- `Type` (a "presheaf", if the functor is contravariant, or "copresheaf", if
-- it is covariant) -- this is the type of the morphism-map component of such a
-- contravariant functor (presheaf).
public export
FinEnrQuivCopreshfMmap : {v : Type} ->
  FinEnrQuivV v -> TypeQuivCopreshfSig v -> Type
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
  tqpOmap : TypeQuivPreshfSig v
  tqpFmap : TypeQuivPreshfMmap {v} e tqpOmap

public export
record TQCopresheaf (v : Type) (e : TypeQuivV v) where
  constructor TQCopre
  tqcOmap : TypeQuivCopreshfSig v
  tqcFmap : TypeQuivCopreshfMmap {v} e tqcOmap

-----------------------------------------------
-----------------------------------------------
---- Profunctors on quivers ("prosheaves") ----
-----------------------------------------------
-----------------------------------------------

public export
TypeQuivProshfSig : (w, v : Type) -> Type
TypeQuivProshfSig w v = w -> v -> Type

public export
TypeQuivDimapSig : {w, v : Type} -> TypeQuivV w -> TypeQuivV v ->
  TypeQuivProshfSig w v -> Type
TypeQuivDimapSig {w} {v} qw qv p =
  (a, c : w) -> (b, d : v) -> qw (c, a) -> qv (b, d) -> p a b -> p c d

public export
TypeQuivLmapSig : {w, v : Type} -> TypeQuivV w -> TypeQuivProshfSig w v -> Type
TypeQuivLmapSig {w} {v} qw p = (a, b : w) -> (c : v) ->
  qw (b, a) -> p a c -> p b c

public export
TypeQuivRmapSig : {w, v : Type} -> TypeQuivV v -> TypeQuivProshfSig w v -> Type
TypeQuivRmapSig {w} {v} qv p = (c : w) -> (a, b : v) ->
  qv (a, b) -> p c a -> p c b

public export
record TQProsheaf (w, v : Type) (qw : TypeQuivV w) (qv : TypeQuivV v) where
  constructor TQPro
  tqcOmap : TypeQuivProshfSig w v
  tqcLmap : TypeQuivLmapSig {w} {v} qw tqcOmap
  tqcRmap : TypeQuivRmapSig {w} {v} qv tqcOmap

public export
record TQCollage {dobj, cobj : Type}
    {dmor : TypeQuivV dobj} {cmor : TypeQuivV cobj}
    (dmap : TQPresheaf dobj dmor) (cmap : TQCopresheaf cobj cmor) where
  constructor TQC
  tqcHetOmap : dobj -> cobj -> Type
  tqcHetFmap : (s : dobj) -> (t : cobj) -> tqcHetOmap s t ->
    tqpOmap dmap s -> tqcOmap cmap t

-------------------------------------------------------
-------------------------------------------------------
---- Functors in free-(co)presheaf double category ----
-------------------------------------------------------
-------------------------------------------------------
