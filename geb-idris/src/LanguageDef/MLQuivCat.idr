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
record TQCollage (w, v : Type) (q : TypeProquivV w v) where
  constructor TQC
  tqcContra : TQPresheaf w (prqContra q)
  tqcCovar : TQCopresheaf v (prqCovar q)
  tqcHet : (s : w) -> (t : v) -> prqHet q (s, t) ->
    tqpOmap tqcContra s -> tqcOmap tqcCovar t

public export
record TQDiCollage (v : Type) (q : TypeDiquivV v) where
  constructor TQDC
  tqdcCat : TQPresheaf v (dqQuiv q)
  tqdcHet : (s, t : v) -> dqHet q (s, t) ->
    tqpOmap tqdcCat s -> tqpOmap tqdcCat t

----------------------------------------------------
----------------------------------------------------
---- Metalanguage difunctors as figure-collages ----
----------------------------------------------------
----------------------------------------------------

public export
record MLCollage where
  constructor MLC
  mlcHetIdx : Type
  mlcDom : SliceObj mlcHetIdx
  mlcCod : SliceObj mlcHetIdx

export
InterpMLC : MLCollage -> ProfunctorSig
InterpMLC mlc x y =
  (i : mlcHetIdx mlc ** (x -> mlcDom mlc i, mlcCod mlc i -> y))

export
InterpMLClmap : (mlc : MLCollage) ->
  (0 s, t, a : Type) -> (a -> s) -> InterpMLC mlc s t -> InterpMLC mlc a t
InterpMLClmap mlc s t a mas pst =
  (fst pst ** (fst (snd pst) . mas, snd (snd pst)))

export
InterpMLCrmap : (mlc : MLCollage) ->
  (0 s, t, b : Type) -> (t -> b) -> InterpMLC mlc s t -> InterpMLC mlc s b
InterpMLCrmap mlc s t b mtb pst =
  (fst pst ** (fst (snd pst), mtb . snd (snd pst)))

export
InterpMLCdimap : (mlc : MLCollage) ->
  (0 s, t, a, b : Type) -> (a -> s) -> (t -> b) ->
    InterpMLC mlc s t -> InterpMLC mlc a b
InterpMLCdimap mlc s t a b mas mtb =
  InterpMLClmap mlc s b a mas . InterpMLCrmap mlc s t b mtb

public export
record MLCNatTrans (p, q : MLCollage) where
  constructor MLNT
  mpOnIdx : mlcHetIdx p -> mlcHetIdx q
  mpOnDom :
    (i : mlcHetIdx p) -> mlcDom p i ->
      mlcDom q (mpOnIdx i)
  mpOnCod :
    (i : mlcHetIdx p) -> mlcCod q (mpOnIdx i) ->
      mlcCod p i

public export
record MLCParaNT (p, q : MLCollage) where
  constructor MLPNT
  mpOnIdx : mlcHetIdx p -> mlcHetIdx q
  mpOnDom :
    (i : mlcHetIdx p) -> (mlcCod p i -> mlcDom p i) -> mlcDom p i ->
      mlcDom q (mpOnIdx i)
  mpOnCod :
    (i : mlcHetIdx p) -> (mlcCod p i -> mlcDom p i) -> mlcCod q (mpOnIdx i) ->
      mlcCod p i

export
InterpMLCnt : {0 p, q : MLCollage} -> MLCNatTrans p q ->
  (0 x, y : Type) -> InterpMLC p x y -> InterpMLC q x y
InterpMLCnt {p} {q} (MLNT oni ond onc) x y (i ** (dd, dc)) =
  (oni i ** (ond i . dd, dc . onc i))

export
0 InterpMLCisNatural : {0 p, q : MLCollage} -> (mlnt : MLCNatTrans p q) ->
  (0 s, t, a, b : Type) ->
  (mas : a -> s) -> (mtb : t -> b) ->
  ExtEq {a=(InterpMLC p s t)} {b=(InterpMLC q a b)}
    (InterpMLCdimap q s t a b mas mtb . InterpMLCnt {p} {q} mlnt s t)
    (InterpMLCnt {p} {q} mlnt a b . InterpMLCdimap p s t a b mas mtb)
InterpMLCisNatural {p=(MLC ph pd pc)} {q=(MLC qh qd qc)}
  (MLNT onidx ondom oncod) s t a b mas mtb (pi ** (spd, pct)) =
    dpEq12 Refl $ pairEqCong Refl Refl

export
InterpMLCpara : {0 p, q : MLCollage} -> MLCParaNT p q ->
  (0 x : Type) -> InterpMLC p x x -> InterpMLC q x x
InterpMLCpara {p} {q} (MLPNT oni ond onc) x (i ** (dd, dc)) =
  (oni i ** (ond i (dd . dc) . dd, dc . onc i (dd . dc)))

export
0 InterpMLCisPara : {0 p, q : MLCollage} -> (mlpnt : MLCParaNT p q) ->
  (i0, i1 : Type) -> (i2 : i0 -> i1) ->
  (d0 : InterpMLC p i0 i0) -> (d1 : InterpMLC p i1 i1) ->
  (InterpMLClmap p i1 i1 i0 i2 d1 = InterpMLCrmap p i0 i0 i1 i2 d0) ->
  (InterpMLClmap q i1 i1 i0 i2 (InterpMLCpara {p} {q} mlpnt i1 d1) =
   InterpMLCrmap q i0 i0 i1 i2 (InterpMLCpara {p} {q} mlpnt i0 d0))
InterpMLCisPara {p=(MLC ph pd pc)} {q=(MLC qh qd qc)} (MLPNT onidx ondom oncod)
  i0 i1 i2 (pi0 ** (i0d0, c0i0)) (pi1 ** (i1d1, c1i1)) cond =
    case mkDPairInjectiveFstHet cond of
      Refl => case mkDPairInjectiveSndHet cond of
        Refl => dpEq12 Refl
          $ pairEqCong Refl Refl
