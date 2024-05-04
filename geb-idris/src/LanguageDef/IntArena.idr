module LanguageDef.IntArena

import Library.IdrisUtils
import Library.IdrisCategories
import Library.IdrisAlgebra

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
