# Polynomial Functor Extensions

Status: Planning - Ready for Grothendieck Refactoring

## Objective

Extend the polynomial endofunctor framework in `GebLean.PolyAlg` with
additional categorical structure, factorization systems, and connections
to related mathematical frameworks.

## Current Work: Free Monad Monad and Cofree Comonad Comonad

### Mathematical Background

From Spivak-Libkind (ACT 2024: "Pattern runs on matter: The free monad
monad as a module over the cofree comonad comonad"):

- The free monad on `P`, written `𝔪ₚ`, satisfies: `𝔪ₚ ≅ y + p ◁ 𝔪ₚ`
- The assignment `P ↦ 𝔪ₚ` forms a monad on `Poly`
- The cofree comonad on `P`, written `𝔠ₚ`, satisfies: `𝔠ₚ ≅ p ⊗ 𝔠ₚ`
- The assignment `P ↦ 𝔠ₚ` forms a comonad on `Poly`

### Implementation Strategy

We already have in `PolyAlg.lean`:

- `polyFreeMPoly P : PolyEndo X` - the polynomial for the free monad
- `polyCofreeMPoly P : PolyEndo X` - the polynomial for the cofree comonad
- Monad structure on `PolyFreeM`: `polyFreeMPure`, `polyFreeMBind`, laws
- Comonad structure on `PolyCofreeM`: `polyCofreeExtract`, `polyCofreeCounit`
- Free/forgetful adjunction for algebras
- Cofree/forgetful adjunction for coalgebras

### Free Monad Monad (P ↦ polyFreeMPoly P)

Unit: `η : P → polyFreeMPoly P`

- Conceptually: embed each P-operation as a single-node tree
- Implementation: Use the algebra structure map `polyFreeMStr` which embeds
  P-operations into Free P trees

Multiplication: `μ : polyFreeMPoly (polyFreeMPoly P) → polyFreeMPoly P`

- Conceptually: flatten trees-of-trees into trees
- Implementation: This is the "join" operation. A tree whose internal nodes
  are themselves labeled by trees flattens to a single tree.
- Connection to existing work: `polyFreeMBind` provides substitution;
  the multiplication is bind with identity

### Cofree Comonad Comonad (P ↦ polyCofreeMPoly P)

Counit: `ε : polyCofreeMPoly P → P`

- Conceptually: extract the root operation from a cofree comonad stream
- Implementation: Already have `polyCofreeCounit` for the comonad counit

Comultiplication: `δ : polyCofreeMPoly P → polyCofreeMPoly (polyCofreeMPoly P)`

- Conceptually: annotate each node with its subtree (duplicate)
- Implementation: Similar to `polyCofixToCofreeAtCofix` - each node gets
  annotated with the stream rooted at that node

### Implementation Steps

1. Define morphisms of polynomial endofunctors (natural transformations
   between induced functors on Over X)

2. Free Monad Monad:
   a. Unit: P → polyFreeMPoly P (single-operation trees)
   b. Multiplication: polyFreeMPoly (polyFreeMPoly P) → polyFreeMPoly P
   c. Prove monad laws (associativity, unit laws)

3. Cofree Comonad Comonad:
   a. Counit: polyCofreeMPoly P → P (extract root)
   b. Comultiplication: polyCofreeMPoly P → polyCofreeMPoly (polyCofreeMPoly P)
   c. Prove comonad laws (coassociativity, counit laws)

4. Connection to existing adjunctions - the monad/comonad structures arise
   from composing the free-forgetful and cofree-forgetful adjunctions

### References on (co)free (co)monad-(co)monad

- Spivak, Libkind. "Pattern runs on matter" (ACT 2024)
- Topos Institute blog: "Poly-morphic effect handlers" (Jan 2024)
- nLab: free monad, polynomial functor, polynomial monad
- 1lab: Cat.Functor.Algebra
- Gambino, Kock. "Polynomial functors and polynomial monads"

## Planned Work

### 1. Small Adjunctions with Type

There are several adjunctions between categories of polynomial functors
and `Type`. These should be formalized.

### 2. Free Monad as a Monad on Polynomial Endofunctors (IN PROGRESS)

The operation `P ↦ Free P` (taking the free monad of a polynomial
endofunctor) is itself a monad on the category of polynomial endofunctors
over any `X : Type`. Dually, `P ↦ Cofree P` is a comonad. These monadic
and comonadic structures should be made explicit.

### 3. Left Multi-Adjoints

Implement the notion of left multi-adjoint, which is closely related to
parametric right adjoints.

### 4. Epi/Mono Factorization

Implement epi/mono factorization for morphisms of polynomial functors.

### 5. Vertical/Cartesian Factorization

Implement vertical/Cartesian factorization for polynomial functors.

### 6. Universal Morphisms and Categorical Structure

Formalize universal morphisms in categories of polynomial functors:

- Limits and colimits (all exist)
- Exponential objects
- Parallel product (Dirichlet product)
- Left Kan extensions

### 7. Dual-Variance Polynomial Functors

Investigate dual-variance versions of polynomial functors and their
connections to:

- Paranatural category theory
- Twisted-arrow categories
- The connected Grothendieck construction (already implemented in
  `GebLean.Utilities.Grothendieck`)

### 8. Double Category of Slice Polynomial Functors

Extend the slice/Over polynomial functor implementation to the double
category (which is also a framed bicategory) of slice polynomial functors.

## Dependencies

- `GebLean.Polynomial` - Polynomial functor infrastructure
- `GebLean.PolyAlg` - Algebras, coalgebras, and universal constructions
  (initial algebras, terminal coalgebras)
- `GebLean.Utilities.Grothendieck` - Connected Grothendieck construction
- `GebLean.Utilities.TwistedArrow` - Twisted arrow categories

## Current Status (2026-02-12)

### Polynomial Composition Category

Working on filling holes in `GebLean/Polynomial.lean` for the
polynomial composition category (`polyCompGFunctor` and
`PolyHorizontalCat`).

#### Completed

- Cleaned up proof chain: removed `_rec_at_rhs`,
  `_rec_at_lhs_fst`, `_rec_at_lhs`, `_rec_at`,
  `pi_transport`, `grothendieckContra'_rec_fiber`,
  `polyCompGMap_comp_fiber`, `polyCompGMap_comp_rec_eq`,
  `polyCompGMap_comp_fiber_heq`
- Added `GrothendieckContra'.ext_of_heq` (lines ~2115):
  structure ext using HEq instead of eqToHom
- `polyCompGMap_comp` (line ~2191) uses `ext_of_heq` with
  base = `polyCompGMap_comp_base` and fiber = `_` (HEq hole)
- `polyBetweenComp_nonempty_iso` (line ~2232): forward/inverse
  morphisms `hf_hom`/`hf_inv` compile; iso laws are `_` holes

#### Remaining Holes (3 total)

1. **`polyCompGMap_comp` fiber HEq** (line ~2203):

   ```lean
   (polyCompGMap f (φ ≫ ψ)).fiber ≍
     (polyCompGMap f φ ≫ polyCompGMap f ψ).fiber
   ```

   After `dsimp [polyCompGMap]`, the LHS is an explicit
   function using `ccrFiberMor (φ ≫ ψ)`. The RHS has
   `(ccrHomMk ≫ ccrHomMk).fiber` which is the
   GrothendieckContra' composition. The two live in
   different types (dependent on different base `.snd`).

2. **`hf_hom_inv`** (line ~2293): `hf_hom G ≫ hf_inv G = 𝟙`
3. **`hf_inv_hom`** (line ~2295): `hf_inv G ≫ hf_hom G = 𝟙`

All three reduce to the same pattern: HEq or Eq of
`GrothendieckContra'.Hom` fiber functions where base `.fst`
agrees definitionally but base `.snd` differs.

#### Obstacle

The fiber type of `GrothendieckContra'.Hom` depends on the
WHOLE base function, not just `.fst`. Since base `.snd`
differs propositionally (not definitionally), the fiber
types genuinely differ. Approaches that fail include:

- `rfl`: not definitionally equal (base `.snd` differs)
- `heq_of_eq`: types not definitionally equal
- `cast_cast + cast_heq`: HEq chains don't terminate
  because the `eqToHom`/`≫` in the fiber category doesn't
  decompose at the sigma element level
- `set + clear_value + subst` on `.base`: only replaces
  the variable, not the `.fiber` field of the same structure
- `Functor.eqToHom_proj`: applies to Pi-category eqToHom
  but the fiber category involves `Cat.opFunctor'` which
  wraps it differently

#### Path Forward

Write a dedicated lemma in `Families.lean` (near
`CoprodCovarRepCat` definitions) that states: for `ccrHomMk`
morphisms in `CoprodCovarRepCat (Over X)`, if the base
`.fst` (index reindexing) agrees definitionally and the
fiber `Over.homMk` `.left` functions produce pointwise equal
sigma elements (with `.fst` equal by `ccrComp_fiberMor_left`
and `.snd` equal by `cast_cast` + proof irrelevance), then
the morphisms are equal.

This is the "instantiation by substitution" approach: factor
the general principle about `CoprodCovarRepCat` morphism
equality, then instantiate for each of the 3 holes.

### Previous Status (2025-12-22)

#### Cleanup Complete - Ready for Grothendieck Refactoring

All incomplete code containing low-level transport proofs has been removed from
`GebLean/PolyAlg.lean`. The following definitions were removed:

- `polyFreeMMonadMulAtLeft`, `polyFreeMMonadMulLeft`, `polyFreeMMonadMul_comm`
- `sigma_match_transport_val`
- `polyFreeMLeafData_map_inr`
- `polyFreeMLeafData_map`
- `polyFreeM_to_polyFreeMPolyEval_map`
- `polyFreeMMonadMul`

Build and tests pass successfully. The codebase is in a clean state.

### Path Forward: Grothendieck Approach

Instead of continuing with low-level transport manipulations, we will implement
the free monad monad and cofree comonad comonad using the Grothendieck
construction approach documented in:

- `docs/polynomial-functors-as-grothendieck.md` - Theoretical foundation
- `.session/workstreams/grothendieck-refactoring.md` - Implementation plan

This approach will:

1. Recognize polynomial functors as double Grothendieck constructions
2. Define generic functorFrom/functorTo/functorBetween for all polynomial
   functors
3. Eliminate all manual transport proofs
4. Make naturality and functoriality automatic from categorical composition

See the implementation plan for the 6-phase refactoring strategy.

## References on polynomial functors

- nLab: polynomial functor, free monad, polynomial monad
- Gambino, Kock. "Polynomial functors and polynomial monads"
- Spivak, Niu. "Polynomial Functors: A Mathematical Theory of Interaction"
- Spivak, Libkind. "Pattern runs on matter" (ACT 2024)
