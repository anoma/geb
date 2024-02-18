module LanguageDef.MLQuivCat

import Library.IdrisUtils
import Library.IdrisCategories
import LanguageDef.Quiver

-------------------------------------
-------------------------------------
---- (Co)presheaves from quivers ----
-------------------------------------
-------------------------------------

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

---------------------------------
---------------------------------
---- Categories from quivers ----
---------------------------------
---------------------------------

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

public export
TypeQuivEndBase : {v : Type} -> (v -> v -> Type) -> Type
TypeQuivEndBase {v} p = (ev : v) -> p ev ev

public export
TypeQuivProdP : {v : Type} -> (q : TypeQuivV v) -> (v -> v -> Type) -> Type
TypeQuivProdP {v} q p = (ev, ev' : v) -> q (ev, ev') -> p ev ev'

public export
TypeQuivCoendBase : {v : Type} -> (v -> v -> Type) -> Type
TypeQuivCoendBase {v} p = (ev : v ** p ev ev)

public export
TypeQuivSumP : {v : Type} -> (q : TypeQuivV v) -> (v -> v -> Type) -> Type
TypeQuivSumP {v} q p = (ev : v ** ev' : v ** (q (ev', ev), p ev ev'))

-- This is the profunctor underlying both the left and right Kan extensions of
-- a copresheaf, as described by a quiver internal to and enriched over `Type`,
-- along the constant functor from the index category to the terminal object of
-- `Type` (i.e. `Unit`).  The reason that the same profunctor underlies both
-- directions of Kan extension is that when extending a copresheaf `P` along
-- the constant functor to the terminal object, the left-extension profunctor
-- is effectively `1 x P` while the right-extension profunctor is effectively
-- `P ^ 1`, both of which are isomorphic to just `P`.
public export
TypeQuivKanExtProf : {v : Type} -> (slv : SliceObj v) -> v -> v -> Type
TypeQuivKanExtProf {v} slv _ = slv

public export
TypeQuivKanExtProfDimap :
  {v : Type} -> (q : TypeQuivV v) -> (slv : SliceObj v) ->
  TypeQuivCopreshfMmap {v} q slv ->
  TypeQuivDimapSig {v} q (TypeQuivKanExtProf {v} slv)
TypeQuivKanExtProfDimap {v} q slv fm a b c d mca mbd slvb = fm b d mbd slvb

public export
TypeQuivKanExtProfLmap :
  {v : Type} -> (q : TypeQuivV v) -> (slv : SliceObj v) ->
  TypeQuivCopreshfMmap {v} q slv ->
  TypeQuivLmapSig {v} q (TypeQuivKanExtProf {v} slv)
TypeQuivKanExtProfLmap {v} q slv fm a b c mba = id {a=(slv c)}

public export
TypeQuivKanExtProfRmap :
  {v : Type} -> (q : TypeQuivV v) -> (slv : SliceObj v) ->
  TypeQuivCopreshfMmap {v} q slv ->
  TypeQuivRmapSig {v} q (TypeQuivKanExtProf {v} slv)
TypeQuivKanExtProfRmap {v} q slv fm a b c mab = fm a b mab

public export
TypeQuivRKanExtBase : {v : Type} -> (slv : SliceObj v) -> Type
TypeQuivRKanExtBase {v} slv =
  TypeQuivEndBase {v} (TypeQuivKanExtProf {v} slv)

public export
TypeQuivRKanProdP : {v : Type} -> TypeQuivV v -> SliceObj v -> Type
TypeQuivRKanProdP {v} q slv = TypeQuivProdP {v} q (TypeQuivKanExtProf {v} slv)

public export
TypeQuivRKanExt :
  {v : Type} -> (q : TypeQuivV v) -> (slv : SliceObj v) ->
  TypeQuivCopreshfMmap {v} q slv -> Type
TypeQuivRKanExt {v} q slv fm =
  (pi : ((ev : v) -> slv ev) **
   (ev, ev' : v) -> (f : q (ev, ev')) -> fm ev ev' f (pi ev) = pi ev')

public export
TypeQuivLKanExtBase : {v : Type} -> (q : TypeQuivV v) -> (slv : SliceObj v) ->
  TypeQuivCopreshfMmap {v} q slv -> Type
TypeQuivLKanExtBase {v} q slv fm =
  TypeQuivCoendBase {v} (TypeQuivKanExtProf {v} slv)

public export
TypeQuivLKanSumP : {v : Type} -> TypeQuivV v -> SliceObj v -> Type
TypeQuivLKanSumP {v} q slv = TypeQuivSumP {v} q (TypeQuivKanExtProf {v} slv)
