module LanguageDef.IntArena

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra
import LanguageDef.InternalCat

-------------------------
-------------------------
---- Internal arenas ----
-------------------------
-------------------------

-- An "arena" on an internal category `c` is a metalanguage object called the
-- "index" or "position-set" together with a morphism from that object to the
-- object of objects of the internal category.  (That is, in particular, the
-- same data which represent a (metalanguage) slice object over the object of
-- objects of the internal category.)  If the metalanguage is a well-pointed
-- topos, then we can view the morphism as mapping each term of the position-set
-- to an object of the internal category which we call the "direction" at that
-- position.
--
-- We can form several different categories whose objects are arenas, by
-- choosing different types of morphisms.  See for example:
--
--  - `IntUFamCat` -- universal families of objects (drawn from the internal
--    category), AKA the free cartesian monoidal category (of the internal
--    category)
--  - `IntEFamCat` -- existential families, AKA the free coproduct completion,
--    AKA Dirichlet functors
--  - `IntUCofamCat` -- universal cofamilies (i.e. families of objects drawn
--    from the opposite of the internal category)
--  - `IntECofamCat` -- existential cofamilies, AKA polynomial functors
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
MLArena : Type
MLArena = IntArena Type

public export
ia1 : {0 c : Type} -> c -> IntArena c
ia1 {c} x = IA Unit (\_ => x)

-- A morphism from an existential family represented by an arena to
-- an object of the underlying category.  This is a morphism of the
-- free coproduct completion of the underlying category, and in this
-- restricted case, it preserves coproducts in the underlying category,
-- because it has the same covariant representing object as would a
-- product in the underlying category itself (namely, the product of the
-- objects in the family).
public export
iaMorFromEx : {0 c : Type} -> IntMorSig c -> IntArena c -> c -> Type
iaMorFromEx {c} mor ar y = (i : iaIdx ar) -> mor (iaObj ar i) y

-- A morphism to a universal family represented by an arena from
-- an object of the underlying category.  This is a morphism of the
-- free product completion of the underlying category, and, dually to
-- `iaMorFromEx`, it preserves products in the underlying category.
public export
iaMorToUniv : {0 c : Type} -> IntMorSig c -> c -> IntArena c -> Type
iaMorToUniv {c} mor x ar = (i : iaIdx ar) -> mor x (iaObj ar i)

-- A morphism from an existential family represented by an arena to
-- a universal family represented by an arena.  This is a morphism of
-- the free coproduct completion of the free product completion of the
-- underlying category, and in this restricted case, it preserves
-- both products and coproducts in the underlying category.
public export
iaMorFromExToUniv : {0 c : Type} -> IntMorSig c -> IntMorSig (IntArena c)
iaMorFromExToUniv {c} mor x y =
  (i : iaIdx x) -> (j : iaIdx y) -> mor (iaObj x i) (iaObj y j)

-- Precompose a morphism before a map to a universal family.
public export
iaPrecompToUniv : {0 c : Type} -> {mor : IntMorSig c} ->
  (comp : IntCompSig c mor) -> {w, x : c} -> {y : IntArena c} ->
  iaMorToUniv {c} mor x y -> mor w x -> iaMorToUniv {c} mor w y
iaPrecompToUniv {c} {mor} comp {w} {x} {y} g f i = comp w x (iaObj y i) (g i) f

-- Postcompose a morphism after a map from a universal family.
public export
iaPostcompFromEx : {0 c : Type} -> {mor : IntMorSig c} ->
  (comp : IntCompSig c mor) -> {x : IntArena c} -> {y, z : c} ->
  mor y z -> iaMorFromEx {c} mor x y -> iaMorFromEx {c} mor x z
iaPostcompFromEx {c} {mor} comp {x} {y} {z} g f i = comp (iaObj x i) y z g (f i)
