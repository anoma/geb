# Decisions Log

Cross-cutting decisions and their rationale. Consult this to avoid
re-litigating settled questions.

## Format

```markdown
### [Date] Topic

**Decision**: What was decided

**Rationale**: Why this choice was made

**Alternatives considered**: What else was evaluated (if relevant)
```

---

<!-- Add decisions below this line -->

### 2025-11-30 W-Type Diagram Morphism Direction

**Decision**: Fiber maps in `WTypeDiagramHom` go from target to source
(`Q.fiber -> P.fiber`), matching the contravariant structure of
`CoprodCovarRepCat`.

**Rationale**: `CoprodCovarRepCat` is built from the Grothendieck construction
on `familyFunctor . opFunctor'`, which introduces contravariance in the fiber
direction. A morphism `(I_P, F_P) -> (I_Q, F_Q)` has reindexing `r : I_P -> I_Q`
but fiber morphisms `phi : forall i, F_Q(r i) -> F_P(i)`. This matches the
semantics of polynomial functors where arities/directions are pulled back.

**Alternatives considered**: Covariant fiber maps would not match the existing
`CoprodCovarRepCat` structure and would require additional contravariancy
somewhere else to establish the equivalence.

### 2025-11-30 Equivalence via Sigma Rearrangement

**Decision**: The equivalence between `WTypeDiagramCat` and
`PolyFunctorBetweenCat` works by recognizing that `Sigma y, {b : B // t b = y}`
is equivalent to `B` (with `t` implicit in the first component).

**Rationale**: W-type diagrams have a single base type `B` with a target map
`t : B -> Y`, while `PolyFunctorBetweenCat` has separate index types for each
`y`. These are equivalent representations: partitioning `B` by `t` vs having
pre-partitioned index types. The equivalence is essentially reorganizing the
same data.

**Alternatives considered**: Could have tried to make the two representations
definitionally equal via type synonyms, but the sigma-type packaging makes this
impractical. An explicit equivalence is cleaner.

### 2025-11-30 Grothendieck Functor Factorization Strategy

**Decision**: Factor functors into/between Grothendieck constructions via
the `pre` functor and related structures (sections, lax natural
transformations).

**Rationale**:

1. **FunctorTo factorization**: A functor `E ⥤ Grothendieck F` factors as
   a choice of base functor `E ⥤ C` plus a section of the pulled-back
   Grothendieck construction. This separates "which base point" from
   "which fiber element" and leverages mathlib's `pre` functor.

2. **FunctorFrom**: No factorization recommended. The current structure
   (fiber functors + coherent natural transformations) is already atomic.
   There is no dual "pushforward" operation to `pre`.

3. **FunctorBetween factorization**: A functor `Grothendieck G ⥤ Grothendieck F`
   factors as a base functor `C ⥤ D` plus a lax natural transformation
   `G ⟹ baseFib ⋙ F`. The lax transformation captures the "same base"
   case, and composition with `pre` handles the base change.

**Alternatives considered**:

- Keeping current monolithic structures: simpler but less modular
- Different factorization orderings: the chosen order (base first, then
  fiber data) aligns with the mathematical interpretation and leverages
  existing `pre` infrastructure
