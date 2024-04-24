module LanguageDef.IntArena

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import public LanguageDef.InternalCat

--------------------------------------
--------------------------------------
---- Internal polynomial functors ----
--------------------------------------
--------------------------------------

-- An internal polynomial functor is a sum of representable internal
-- copresheaves. It can be expressed as a slice object over the object
-- of the objects of the internal category -- the total-space object is
-- the index of the sum, known as the "position set [or "type", or "object"]".
-- The projection morphism assigns to each position a "direction", which is
-- an object of the internal category.
public export
IntArena : (c : Type) -> Type
IntArena c = CSliceObj c

public export
IA : {0 c : Type} -> (idx : Type) -> (idx -> c) -> IntArena c
IA {c} = MkDPair {a=Type} {p=(ContravarHomFunc c)}

public export
iaIdx : {0 c : Type} -> IntArena c -> Type
iaIdx {c} = DPair.fst {a=Type} {p=(ContravarHomFunc c)}

public export
iaObj : {0 c : Type} -> (ar : IntArena c) -> iaIdx {c} ar -> c
iaObj {c} = DPair.snd {a=Type} {p=(ContravarHomFunc c)}

public export
InterpIPFobj : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntArena c -> c -> Type
InterpIPFobj c mor (pos ** dir) a = (i : pos ** mor (dir i) a)

public export
InterpIPFmap : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (ar : IntArena c) -> IntCopreshfMapSig c mor (InterpIPFobj c mor ar)
InterpIPFmap c mor comp (pos ** dir) x y m (i ** dm) =
  (i ** comp (dir i) x y m dm)

public export
InterpIDFobj : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntArena c -> c -> Type
InterpIDFobj c mor (pos ** dir) a = (i : pos ** mor a (dir i))

public export
InterpIDFmap : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (ar : IntArena c) -> IntPreshfMapSig c mor (InterpIDFobj c mor ar)
InterpIDFmap c mor comp (pos ** dir) x y m (i ** dm) =
  (i ** comp y x (dir i) dm m)

public export
IntPNTar : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntArena c -> IntArena c -> Type
IntPNTar c mor (ppos ** pdir) (qpos ** qdir) =
  (onpos : ppos -> qpos ** (i : ppos) -> mor (qdir (onpos i)) (pdir i))

public export
InterpIPnt : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (p, q : IntArena c) -> IntPNTar c mor p q ->
  IntCopreshfNTSig c (InterpIPFobj c mor p) (InterpIPFobj c mor q)
InterpIPnt c mor comp (ppos ** pdir) (qpos ** qdir) (onpos ** ondir) x
  (i ** dm) =
    (onpos i ** comp (qdir (onpos i)) (pdir i) x dm (ondir i))

public export
IntDNTar : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntArena c -> IntArena c -> Type
IntDNTar c mor p q =
  (onpos : fst p -> fst q ** (i : fst p) -> mor (snd p i) (snd q (onpos i)))

public export
InterpIDnt : (c : Type) -> (mor : IntDifunctorSig c) ->
  (comp : IntCompSig c mor) ->
  (p, q : IntArena c) -> IntDNTar c mor p q ->
  IntPreshfNTSig c (InterpIDFobj c mor p) (InterpIDFobj c mor q)
InterpIDnt c mor comp (ppos ** pdir) (qpos ** qdir) (onpos ** ondir) x
  (i ** dm) =
    (onpos i ** comp x (pdir i) (qdir (onpos i)) (ondir i) dm)

-------------------------------------
-------------------------------------
---- Dirichlet-functor embedding ----
-------------------------------------
-------------------------------------

public export
IntDirichCatObj : Type -> Type
IntDirichCatObj = IntArena

public export
IntDirichCatMor : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntDifunctorSig (IntDirichCatObj c)
IntDirichCatMor = IntDNTar

-- We can embed a category `c/mor` into its category of Dirichlet functors
-- (sums of representable presheaves) with natural transformations.
public export
IntDirichEmbedObj : (c : Type) -> (a : c) -> IntDirichCatObj c
IntDirichEmbedObj c a = (() ** (\_ : Unit => a))

-- Note that we can _not_ embed a category into its category of polynomial
-- functors (sums of representable copresheaves) with natural transformations,
-- because trying to define this with `IntPNTar` substituted for `IntDNTar`
-- would require us to define a morphism in the opposite direction from `m`.
-- There is no guarantee that such a morphism exists in `c/mor`.
public export
IntDirichEmbedMor : (c : Type) -> (mor : IntDifunctorSig c) ->
  (a, b : c) ->
  mor a b ->
  IntDirichCatMor c mor (IntDirichEmbedObj c a) (IntDirichEmbedObj c b)
IntDirichEmbedMor c mor a b m = ((\_ : Unit => ()) ** (\_ : Unit => m))

-- The inverse of the embedding of a category into its category of
-- Dirichlet functors.  The existence of this inverse shows that
-- the embedding is full and faithful.
public export
IntDirichEmbedMorInv : (c : Type) -> (mor : IntDifunctorSig c) ->
  (a, b : c) ->
  IntDirichCatMor c mor (IntDirichEmbedObj c a) (IntDirichEmbedObj c b) ->
  mor a b
IntDirichEmbedMorInv c mor a b (pos ** dir) =
  -- Note that `pos` has type `Unit -> Unit`, so there is only one thing
  -- it can be, which is the identity on `Unit` (equivalently, the constant
  -- function returning `()`).
  dir ()

-------------------------------------------
-------------------------------------------
---- Polynomial categories of elements ----
-------------------------------------------
-------------------------------------------

public export
PolyCatElemObj : (c : Type) -> (mor : IntDifunctorSig c) -> IntArena c -> Type
PolyCatElemObj c mor p = (x : c ** InterpIPFobj c mor p x)

-- Unfolding the definition of a morphism in the category of elements
-- specifically of a polynomial endofunctor on `Type` yields the following:
--
--  - A position `i` of the polynomial functor
--  - A pair of types `x`, `y`
--  - An assignment of the directions of `p` at `i` to `x` (together with the
--    type `x`, this can be viewed as an object of the coslice category of
--    the direction-set)
--  - A morphism in `Type` (a function) from `x` to `y`
--
-- One way of looking at all of that together is, if we view a polynomial
-- functor `p` as representing open terms of a data structure, then a morphism
-- of its category of elements is a closed term with elements of `x`
-- substituted for its variables (comprising the type `x` which we then view
-- as a type of variables together with the choice of a position and and
-- assignment of its directions to `x`), together with a function from `x`
-- to `y`, which uniquely determines a closed term with elements of `y`
-- substituted for its variables, by mapping the elements of `x` in the
-- closed term with the chosen function to elements of `y`, while preserving the
-- structure of the term.
--
-- Because of that unique determination, we do not need explicitly to choose
-- the element component of the codomain object, as in the general definition
-- of the category of elements -- the choice of both components of the domain
-- object together with a morphism from its underlying object to some other
-- object of `Type` between them uniquely determine the one codomain object to which there
-- is a corresponding morphism in the category of elements.
public export
data PolyCatElemMor :
    (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
    (p : IntArena c) ->
    PolyCatElemObj c mor p -> PolyCatElemObj c mor p -> Type where
  PCEM : {c : Type} -> {mor : IntDifunctorSig c} ->
    (comp : IntCompSig c mor) ->
    -- `pos` and `dir` together form an `IntArena c`.
    (pos : Type) -> (dir : pos -> c) ->
    -- `i` and `dm` comprise a term of `InterpIPFobj c mor (pos ** dir) x`;
    -- `x` and `dm` together comprise an object of the coslice category
    -- of `dir i`.  `x`, `i`, and `dm` all together comprise an object of
    -- the category of elements of `(pos ** dir)`.
    (x : c) -> (i : pos) -> (dm : mor (dir i) x) ->
    -- `y` and `m` together form an object of the coslice category of `x`.
    (y : c) -> (m : mor x y) ->
    PolyCatElemMor c mor comp (pos ** dir)
      (x ** (i ** dm))
      (y ** (i ** comp (dir i) x y m dm))

public export
pcemMor :
  (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
  (p : IntArena c) ->
  (x, y : PolyCatElemObj c mor p) ->
  PolyCatElemMor c mor comp p x y ->
  mor (fst x) (fst y)
pcemMor _ _ _ _ _ _ (PCEM _ _ _ _ _ _ _ m) = m

public export
DirichCatElemObj : (c : Type) -> (mor : IntDifunctorSig c) -> IntArena c -> Type
DirichCatElemObj c mor p = (x : c ** InterpIDFobj c mor p x)

public export
data DirichCatElemMor :
    (c : Type) -> (mor : IntDifunctorSig c) -> (comp : IntCompSig c mor) ->
    (p : IntArena c) ->
    DirichCatElemObj c mor p -> DirichCatElemObj c mor p -> Type where
  DCEM : {c : Type} -> {mor : IntDifunctorSig c} ->
    (comp : IntCompSig c mor) ->
    -- `pos` and `dir` together form an `IntArena c`.
    (pos : Type) -> (dir : pos -> c) ->
    -- `i` and `dm` comprise a term of `InterpIDFobj c mor (pos ** dir) x`;
    -- `x` and `dm` together comprise an object of the slice category
    -- of `dir i`.  `x`, `i`, and `dm` all together comprise an object of
    -- the category of elements of `(pos ** dir)`.
    (x : c) -> (i : pos) -> (dm : mor x (dir i)) ->
    -- `y` and `m` together form an object of the slice category of `x`.
    (y : c) -> (m : mor y x) ->
    DirichCatElemMor c mor comp (pos ** dir)
      (y ** (i ** comp y x (dir i) dm m))
      (x ** (i ** dm))

---------------------------------------------------------------------
---------------------------------------------------------------------
---- Categories of elements of polynomial endofunctors on `Type` ----
---------------------------------------------------------------------
---------------------------------------------------------------------

public export
IntPolyCatObj : Type -> Type
IntPolyCatObj = IntArena

public export
IntPolyCatMor : (c : Type) -> (mor : IntDifunctorSig c) ->
  IntDifunctorSig (IntPolyCatObj c)
IntPolyCatMor = IntDNTar

public export
MLPolyCatObj : Type
MLPolyCatObj = IntPolyCatObj Type

public export
MLPolyCatMor : MLPolyCatObj -> MLPolyCatObj -> Type
MLPolyCatMor = IntPolyCatMor Type HomProf

public export
MLPolyCatElemObj : MLPolyCatObj -> Type
MLPolyCatElemObj = PolyCatElemObj Type HomProf

public export
MLPolyCatElemMor : (p : MLPolyCatObj) -> (x, y : MLPolyCatElemObj p) -> Type
MLPolyCatElemMor = PolyCatElemMor Type HomProf typeComp

public export
MLDirichCatObj : Type
MLDirichCatObj = IntDirichCatObj Type

public export
MLDirichCatMor : MLDirichCatObj -> MLDirichCatObj -> Type
MLDirichCatMor = IntDirichCatMor Type HomProf

public export
MLDirichCatElemObj : MLDirichCatObj -> Type
MLDirichCatElemObj = DirichCatElemObj Type HomProf

public export
MLDirichCatElemMor : (ar : MLDirichCatObj) ->
  MLDirichCatElemObj ar -> MLDirichCatElemObj ar -> Type
MLDirichCatElemMor = DirichCatElemMor Type HomProf typeComp
