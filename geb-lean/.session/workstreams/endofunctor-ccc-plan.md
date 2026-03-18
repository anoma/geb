# Workstream: Endofunctor CCC for PshRelEdge

## Status

Planning — detailed implementation plan.

## Goal

We need `MonoidalClosed (PshRelEdge C ⥤ PshRelEdge C)` —
the endofunctor category of `PshRelEdge C` is cartesian
closed. The internal hom `[F, G]` of two endofunctors
should be the endofunctor sending `E` to the end
`∫_X [F(X), G(X)]`.

## Universe Obstruction

Mathlib's `MonoidalClosed (J ⥤ C)` instance (from
`Monoidal/Closed/FunctorCategory/Basic.lean`) requires
`HasEnrichedHom C F₁ F₂` for all pairs of functors,
which is `HasEnd (diagram C F₁ F₂)`. The end is a limit
over the `Under j` category for each `j : J ⥤ C`.

For `J = C = PshRelEdge.{u, v, max u v} C`:

- Objects of `PshRelEdge C` are at `Type (max u v + 1)`
- `Under j` objects include `PshRelEdge C` objects, so
  they're at `Type (max u v + 1)`
- The end requires `HasLimitsOfSize.{max u v + 1, ...}`
- We only have `HasLimitsOfSize.{max u v, max u v}`

This is a genuine universe-level gap: the end over
`PshRelEdge C` is a large limit that our limit instances
don't cover.

## Solution: Yoneda Reduction via Reflective Embedding

### Observation

`PshRelEdge C` is a reflective subcategory of the
presheaf topos `PSh(C × I^op)` where `I = WalkingPair`.
The presheaf topos has:

1. `MonoidalClosed (PSh(C × I^op))` — from mathlib
2. The Yoneda reduction: enriched homs in presheaf
   categories compute as ends over `C × I^op` (small),
   NOT over `PSh(C × I^op)` (large)
3. `ExponentialIdeal (pshRelEdgeInclusionFunctor C)` —
   the reflector preserves binary products, so by
   mathlib's `exponentialIdeal_of_preservesBinaryProducts`

### Architecture

The plan has four layers, each building on the previous:

```text
Layer 1: Presheaf topos endofunctor CCC
  MonoidalClosed (PSh(C × I^op) ⥤ PSh(C × I^op))

Layer 2: Barr lift embedding
  PshRelEdge-endofunctors → PSh(C × I^op)-endofunctors
  via sep ⋙ F ⋙ incl (reflect, apply, include)

Layer 3: Exponential in PSh(C × I^op) endofunctors
  [sep ⋙ F ⋙ incl, sep ⋙ G ⋙ incl] computed by
  the enriched hom (end over C × I^op)

Layer 4: Restriction to PshRelEdge endofunctors
  Apply the reflector to bring the exponential back
  to PshRelEdge C, using the exponential ideal property
```

## Detailed Implementation Plan

### Step 1: Establish PshSpanCat = PSh(C × I^op)

**File**: `GebLean/Utilities/Presheaf.lean` or new file

- Define `PshSpanCat C := WalkingSpan ⥤ (Cᵒᵖ ⥤ Type w)`
  as an abbreviation
- Verify `MonoidalClosed (PshSpanCat C)` from mathlib's
  `MonoidalClosed` for functor categories into `Type`
- Verify `HasLimitsOfSize (PshSpanCat C)`

**Estimated effort**: Low (type aliases and instance
verification)

### Step 2: PshSpanCat endofunctor CCC

**File**: `GebLean/PshRelEdgeSeparation.lean` or new file

- Verify `MonoidalClosed (PshSpanCat C ⥤ PshSpanCat C)`
  This SHOULD work from mathlib because:
  - `PshSpanCat C` is a functor category into `Type`
  - The enriched hom end is over `WalkingSpan × C^op`
    (small)
  - `HasLimitsOfSize` on `PshSpanCat C` covers this

  If this doesn't work due to universe constraints with
  the double functor category, we may need to establish
  it through the uncurried presheaf category
  `(WalkingSpan × C^op)^op ⥤ Type w` and its
  equivalence with `WalkingSpan ⥤ (C^op ⥤ Type w)`.

- Also establish `CartesianMonoidalCategory` on the
  endofunctor category

**Estimated effort**: Medium (universe wrangling)

### Step 3: Embedding PshRelEdge endofunctors

**File**: New section in `PshRelEdgeSeparation.lean`

Define the embedding functor:

```lean
embed : (PshRelEdge C ⥤ PshRelEdge C) ⥤
          (PshSpanCat C ⥤ PshSpanCat C)
```

sending `F` to `sep ⋙ F ⋙ incl` (separate, apply F,
include back).

Properties to prove:

- `embed` is fully faithful (from the reflective
  adjunction: `incl` is fully faithful, `sep ⋙ incl`
  is naturally isomorphic to the identity on
  `PshRelEdge C`)
- `embed` preserves finite products (products of
  endofunctors are pointwise; `sep` preserves
  finite products)

Each property should be a separate definition/theorem.

**Estimated effort**: High (precise use of the
reflective adjunction; factor into many small lemmas)

### Step 4: Essential image and exponential ideal

**File**: Same section

Show that the essential image of `embed` is an
exponential ideal in `PshSpanCat C ⥤ PshSpanCat C`:

- This follows from `ExponentialIdeal
  (pshRelEdgeInclusionFunctor C)` (which we have)
  lifted to the endofunctor level
- The argument: if `G` is in the image of `embed`
  (i.e., `G = sep ⋙ G₀ ⋙ incl` for some
  `G₀ : PshRelEdge C ⥤ PshRelEdge C`), and `F` is
  arbitrary, then `[F, G]` applied to any separated
  presheaf gives a separated presheaf (because
  `[-, B]` preserves separation when `B` is separated)

Factor this into:

- Lemma: `[A, B]` is separated when `B` is separated
  (exponential ideal at the object level — we have this)
- Lemma: `[F, G](E)` is separated when `G(E)` is
  separated for all `E` in `PshRelEdge C`
- Theorem: the endofunctor embedding is an exponential
  ideal

**Estimated effort**: High (multiple layers of
universal properties)

### Step 5: MonoidalClosed on PshRelEdge endofunctors

**File**: Same section

Apply `cartesianClosedOfReflective` from mathlib to
the embedding `embed`:

```lean
instance :
    MonoidalClosed
      (PshRelEdge C ⥤ PshRelEdge C) :=
  cartesianClosedOfReflective embed
```

This requires:

- `Reflective embed` (from step 3: fully faithful +
  left adjoint)
- `ExponentialIdeal embed` (from step 4)
- `CartesianMonoidalCategory
    (PshRelEdge C ⥤ PshRelEdge C)` (step 2)
- `MonoidalClosed
    (PshSpanCat C ⥤ PshSpanCat C)` (step 2)

**Estimated effort**: Low (if steps 2-4 are done)

### Step 6: Allow dialgebra tasks

With `MonoidalClosed (PshRelEdge C ⥤ PshRelEdge C)`:

- Task #156: Define `dialEdgeFunctor F G` using the
  endofunctor internal hom
  `ihom (Barr(F)) |>.obj (Barr(G))`
- Task #157: Connect to parametricity via
  `ParametricCone`

## Dependencies

```text
Step 1 ← Step 2 ← Step 5
                ↗
Step 3 ← Step 4 ← Step 5 → Task #156 → Task #157
```

## Risks

1. **Universe levels in Step 2**: The double functor
   category `(PshSpanCat C ⥤ PshSpanCat C)` may have
   universe constraints similar to the PshRelEdge case.
   We need to verify that `PshSpanCat C`'s enriched hom
   end is over `WalkingSpan × C^op` (small), not over
   `PshSpanCat C` itself (large). This depends on
   mathlib's `MonoidalClosed` instance for functor
   categories into `Type` using the Yoneda reduction.

2. **Reflective embedding in Step 3**: The functor
   `sep ⋙ F ⋙ incl` may not be the right embedding.
   An alternative: use the adjunction to define
   `embed(F) = incl ⋙ F ⋙ sep` (include, apply,
   separate) which goes the other direction. Need to
   check which direction gives a reflective embedding
   of endofunctor categories.

3. **Exponential ideal at endofunctor level (Step 4)**:
   Lifting the object-level exponential ideal to the
   endofunctor level may require showing that the
   endofunctor exponential preserves separation
   pointwise. This is the most mathematically
   substantive step.

## Factoring Principles

Following CLAUDE.md's factoring-out-lemmas technique:

- Every intermediate result should be its own named
  `def`/`theorem`
- No proof should have more than ~20 lines of tactics
- Break compositions into helper lemmas
- Use `_` (underscore) frequently to check intermediate
  goal states
- Build one definition at a time, running `lake build`
  after each

## Open Questions

1. Does mathlib's `MonoidalClosed (C ⥤ Type w)`
   use the Yoneda reduction, or does it compute the
   end over `C ⥤ Type w` directly? If the latter,
   Step 2 may have the same universe constraint.

2. Is there a construction that avoids the reflective
   embedding entirely? E.g., defining
   `[F, G](E) = ∫_{c, i} [F(y(c,i))(E), G(y(c,i))(E)]`
   directly as an end over `C × I^op` (small).

3. For the specific dialgebra application, do we need
   the full endofunctor CCC, or just the exponential
   of Barr-lifted endofunctors? The latter might be
   more direct to construct.
