# Binary Product Preservation Workstream

## Status: In Progress

Working on proving that LFunctor preserves binary products:
`L(F₁ × F₂) ≅ L(F₁) × L(F₂)` in BundledOverCategoryData.

## Cast/Match

We need to figure out the standard way of handling how pattern matching does
not reduce through `cast` operations. When we have functions like:

```lean
def freeMorProj₁ (m : FreeMor Q a b) : FreeMor Q' a.1 b.1 :=
  match m with
  | .var (f₁, f₂) => ...
  | .id _ => ...
  | .comp g f => ...
```

And we apply this to `cast h (FreeMor.var x)`, the match cannot see that the
input is a `var` because the `cast` wrapper prevents definitional reduction.

### Potential Solutions

1. **Explicit transport lemmas**: Define helper lemmas that compute how each
   function behaves on casted inputs, using `Eq.rec` or similar.

2. **Restructure definitions**: Change `freeMorLeftEmbed` and `freeMorProj₁`
   to not use pattern matching on the outer FreeMor, instead using explicit
   recursors that can handle casts.

3. **Work at quotient level**: Move more reasoning to the quotient level
   where the cast distinction doesn't matter (since equivalent elements
   are identified).

## Completed Components

### 1. Product Copresheaf Structure

- `FunctorData.prod F₁ F₂` - componentwise product of copresheaves
- `prodQuotData F₁ F₂` - CategoryQuotientData for the product
- `quotData₁`, `quotData₂` - abbreviations for component CategoryQuotientData

### 2. Forward Direction (Projections) - Complete

- `freeMorProj₁`, `freeMorProj₂` - project free morphisms to components
- `freeMorProj₁_respects_gen` - projection 1 respects generators
- `freeMorProj₂_respects_gen` - projection 2 respects generators
- `freeMorProj₁_respects_equiv` - projection 1 respects equivalence
- `freeMorProj₂_respects_equiv` - projection 2 respects equivalence
- `quotMorProj₁`, `quotMorProj₂` - quotient-level projections

### 3. Backward Direction (Computational Pairing) - Partial

- `HasAllIdentities` - structure for identity witness existence
- `prodHasAllIdentities` - product preserves HasAllIdentities
- `freeMorLeftEmbed` - embed component 1 morphism with identity in component 2
- `freeMorRightEmbed` - embed component 2 morphism with identity in component 1
- `freeMorPairComp` - compositional pairing via embeddings

## Components Not Yet Implemented

The following theorems and definitions are required before product preservation
can be completed.

### Embedding Respects Theorems

These theorems prove that the embedding functions respect the equivalence
relation on free morphisms. Required for lifting to quotients.

1. **`freeMorLeftEmbed_lift_gen`**: Prove that `freeMorLeftEmbed` lifts
   generators from component 1 to the product. The id_witness and comp_witness
   cases require proving how pattern matching behaves on casted inputs.

2. **`freeMorRightEmbed_lift_gen`**: Symmetric to above for component 2.

3. **`freeMorLeftEmbed_respects`**: Prove that if `m₁ ~ m₁'` in component 1,
   then `leftEmbed m₁ a₂ ~ leftEmbed m₁' a₂`. Depends on `lift_gen`.

4. **`freeMorRightEmbed_respects`**: Symmetric to above for component 2.

5. **`freeMorPairComp_respects_equiv₁`**: Prove `freeMorPairComp` respects
   equivalence in the first argument. Depends on `freeMorLeftEmbed_respects`.

6. **`freeMorPairComp_respects_equiv₂`**: Prove `freeMorPairComp` respects
   equivalence in the second argument. Depends on `freeMorRightEmbed_respects`.

7. **`freeMorPairComp_respects`**: Combined theorem for both arguments.

8. **`quotMorPairComp`**: Lift `freeMorPairComp` to quotient level using
   `Quotient.lift₂`. Depends on `freeMorPairComp_respects`.

### Round-Trip Theorems (In Progress)

These theorems prove that `proj ∘ pair = id`, establishing one direction
of the isomorphism.

1. **`freeMorProj₁_leftEmbed_equiv`**: Prove `proj₁(leftEmbed m₁ a₂) ~ m₁`.
   The var case requires showing that projecting a casted var extracts the
   correct component through the cast.

2. **`freeMorProj₁_rightEmbed_equiv`**: Prove `proj₁(rightEmbed b₁ m₂) ~ id b₁`.
   The var case requires similar cast handling.

3. **`freeMorProj₂_rightEmbed_equiv`**: Symmetric to (1) for component 2.

4. **`freeMorProj₂_leftEmbed_equiv`**: Symmetric to (2) for component 2.

5. **`freeMorProj₁_pairComp_equiv`**: Prove `proj₁(pairComp m₁ m₂) ~ m₁`.
   Depends on (1) and (2).

6. **`freeMorProj₂_pairComp_equiv`**: Prove `proj₂(pairComp m₁ m₂) ~ m₂`.
   Depends on (3) and (4).

7. **`quotMorProj₁_pairComp`**: Lift (5) to quotients.

8. **`quotMorProj₂_pairComp`**: Lift (6) to quotients.

### Other Round-Trip Direction

1. **`freeMorPairComp_proj_equiv`**: Prove `pairComp(proj₁ m, proj₂ m) ~ m`.
   This establishes the other direction of the isomorphism.

### Final Isomorphism

1. **Product isomorphism at `BundledOverCategoryData` level**: Construct the
   isomorphism `L(F₁ × F₂) ≅ L(F₁) × L(F₂)` using the above round-trips.

2. **Connect to mathlib's `PreservesLimitPair` instance**: Use the isomorphism
   to establish that LFunctor preserves binary products in mathlib's sense.

## Files Modified

- `GebLean/CatJudgmentAdjunction.lean` - BinaryProduct section (lines ~4200-4940)
