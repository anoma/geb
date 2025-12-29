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

## Current Status (2025-12-22)

### Cleanup Complete - Ready for Grothendieck Refactoring

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
