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

## Current Status (2025-12-21)

### Blocked: polyFreeMLeafData_map_inr proof

The proof chain for free monad monad multiplication naturality is blocked at
`polyFreeMLeafData_map_inr` (line 7588 in PolyAlg.lean). The lemma needs to
show that mapping preserves leaf data for internal nodes in trees.

**Proof Structure:**

1. `polyFreeMMonadMul` naturality (line 7739) - needs:
2. `polyFreeM_to_polyFreeMPolyEval_map` (line 7686) - needs:
3. `polyFreeMLeafData_map` (line 7666) - needs:
4. `polyFreeMLeafData_map_inr` (line 7588) **← STUCK HERE**

**The Problem:**

After applying the induction hypothesis, we need to show:

```lean
(polyFreeMLeafData A P (children e) (transport1 ▸ childPos)).val =
(match (transport2 ▸ ⟨e, childPos⟩) with | ⟨e', pos'⟩ =>
  (polyFreeMLeafData A P (children e') pos').val)
```

where `transport1` and `transport2` are anonymous transports introduced by
simplification. We need to show these equal our explicit transports by proof
irrelevance, but attempts to use `sigma_transport_match_eq_transport` and
related lemmas encounter:

- Universe level mismatches (u+1 vs u+2)
- Anonymous transports that don't unify with explicit proofs
- Complex dependent type equalities

**Proposed Strategy:**

1. **Factor into helper lemmas:**
   - Lemma: Transport of `polyFreeMLeafData` with different proofs gives equal
     results (by proof irrelevance)
   - Lemma: Matching on transported sigma with anonymous vs explicit transport
   - Lemma: Specific transport equality for `PolyFreeMLeafPos` types

2. **Alternative approach:**
   Consider reformulating the proof to avoid anonymous transports entirely:
   - Use explicit `cast` instead of relying on simplification
   - Work at a higher level of abstraction (sigma transport lemmas)
   - Define intermediate types to make transports more manageable

3. **If still blocked:**
   Consider restructuring `polyFreeMLeafData_map` to not rely on this helper,
   or reformulate the naturality proof of `polyFreeM_to_polyFreeMPolyEval_map`
   to avoid the leaf data transformation entirely.

## References on polynomial functors

- nLab: polynomial functor, free monad, polynomial monad
- Gambino, Kock. "Polynomial functors and polynomial monads"
- Spivak, Niu. "Polynomial Functors: A Mathematical Theory of Interaction"
- Spivak, Libkind. "Pattern runs on matter" (ACT 2024)
