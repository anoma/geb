# Workstream: Endofunctor CCC for PshRelEdge

## Status

Planning — revised after discovering mathlib gap.

## Goal

We need `MonoidalClosed (PshRelEdge C ⥤ PshRelEdge C)` —
the endofunctor category of `PshRelEdge C` is cartesian
closed. The internal hom `[F, G]` of two endofunctors
should be the endofunctor sending `E` to the end
`∫_X [F(X), G(X)]`.

## Mathlib Gap (discovered 2026-03-18)

Mathlib does NOT provide `MonoidalClosed` for ANY
endofunctor category — not even `[Set, Set]` or
`[PSh(C), PSh(C)]`. The generic
`MonoidalClosed (J ⥤ C)` instance (from
`Monoidal/Closed/FunctorCategory/Basic.lean`) requires
`HasEnrichedHom C F₁ F₂` for all functor pairs. This
is `HasEnd (diagram C F₁ F₂)`, which requires a limit
indexed over the `Under j` category for each `j`.

For endofunctors, `J = C`, so the end is indexed over
`Under j` for `j : C ⥤ C`. This category has objects
at the same universe level as `C`'s objects (bundling
`(k : C, f : k ⟶ j)`), making it as large as `C`
itself. The standard `HasLimitsOfSize` instances are
one universe level too small to cover this.

**Verified**: `MonoidalClosed ((Cᵒᵖ ⥤ Type v) ⥤
(Cᵒᵖ ⥤ Type v))` fails to synthesize even for small
presheaf categories.

The mathematical result IS true — endofunctor
categories of CCCs with sufficient limits are CCC.
The proof uses the Yoneda reduction to compute the
enriched hom end over the small base category. Mathlib's
enriched category machinery does not perform this
reduction automatically.

## Revised Plan: Direct Construction

Since mathlib cannot provide this, we construct the
endofunctor CCC directly for `PshRelEdge C`, using
the Yoneda reduction via the reflective embedding.

### Architecture (revised)

```text
Layer 1: Enriched hom via Yoneda reduction
  [F, G](E) = ∫_{c : C, i : I} [F(y(c,i))(E),
  G(y(c,i))(E)] where y is the Yoneda embedding
  into PshRelEdge C via pshRelIdentFunctor.

Layer 2: Functoriality in E
  Show the end is natural in E, making [F, G] an
  endofunctor.

Layer 3: Adjunction
  Show tensorLeft F ⊣ [F, -], making the
  endofunctor category monoidal closed.
```

### Step 1: Small end formula for the enriched hom

**File**: New section in `PshRelEdgeSeparation.lean`

Define the enriched hom of two endofunctors `F, G` on
`PshRelEdge C` at an edge `E`:

```lean
def endoIhomObj (F G :
    PshRelEdge C ⥤ PshRelEdge C)
    (E : PshRelEdge C) : PshRelEdge C :=
  -- The end ∫_{X : PshRelEdge C} [F(X), G(X)]
  -- reduced to ∫_{(c,i) : C × I^op} via Yoneda.
  -- Concretely: the limit of the diagram
  -- (c, i) ↦ [F(y(c,i))(E), G(y(c,i))(E)]
  -- where y = pshRelEdgeInclusionFunctor ⋙
  --   yoneda-embedding of PshSpanCat into
  --   PshRelEdge
```

The end over `C × WalkingSpan^op` is a small limit
(indexed by `C × WalkingSpan`, which is at universe
`max u v`). Our `HasLimitsOfSize.{max u v, max u v}`
covers this.

Factor into:

- `endoIhomDiagram F G E` : the diagram
  `(C × WalkingSpan)^op ⥤ PshRelEdge C` sending
  `(c, i)` to `[F(y(c,i))(E), G(y(c,i))(E)]`
- `endoIhomObj F G E` : the limit of this diagram
- Helper: `pshRelEdgeRepresentable (c : C) (i : WalkingSpan)
  : PshRelEdge C` — the representable edge at `(c, i)`

**Estimated effort**: Medium

### Step 2: Functoriality of the enriched hom

**File**: Same section

Show `endoIhomObj F G` is functorial in `E`:

```lean
def endoIhom (F G :
    PshRelEdge C ⥤ PshRelEdge C) :
    PshRelEdge C ⥤ PshRelEdge C
```

The functoriality follows from the limit being
preserved by the diagram's naturality in `E`. Each
`[F(y(c,i))(E), G(y(c,i))(E)]` is functorial in `E`
via the bifunctoriality of the internal hom (F acts
on the representable, not on E directly — the
representable is FIXED, so there's no contravariance
in E).

Note: this needs refinement. `F(y(c,i))` is a FIXED
edge (independent of `E`), and `G(y(c,i))` is also
fixed. So `[F(y(c,i)), G(y(c,i))]` is a fixed edge
too. The "end" `∫_{(c,i)} [F(y(c,i)), G(y(c,i))]`
is a fixed edge, NOT a functor of `E`!

**Correction**: The enriched hom `[F, G]` as an
endofunctor does NOT have the form
`E ↦ ∫ [F(y)(E), G(y)(E)]`. The correct formula
involves the END of the diagram that DOES depend on E:

`[F, G](E) = end_{X} Hom_C(E ⊗ F(X), G(X))`

or equivalently using the internal hom:

`[F, G](E) = end_{X} [F(X), [E, G(X)]]`

Correction: this isn't right either. For the enriched hom
in a CCC, the standard formula for functor categories
is:

`enrichedHom(F, G) = end_{X : C} [F(X), G(X)]`

This is a FIXED object of C (the enriched hom object),
NOT an endofunctor. To get an endofunctor, we need
the INTERNAL ihom in the endofunctor category, which
sends an endofunctor `H` to `[H, -]` or `[-, H]`.

### Reassessment

The endofunctor category CCC has:

- Products: pointwise `(F × G)(X) = F(X) × G(X)` ✓
- Terminal: constant functor at terminal object ✓
- Exponential: `[F, G]` where
  `[F, G](X) = ∫_Y [F(Y), G(Y)]^{Hom(X,Y)}`
  — this IS a functor of X, using the copower/hom
  formula

The formula `[F, G](X) = ∫_Y [F(Y), G(Y)]^{Hom(X,Y)}`
involves a weighted limit (powered end). This IS
functorial in X because `Hom(X, Y)` is
contravariantly functorial in X.

For presheaf categories, the Yoneda reduction gives:
`[F, G](X) = ∫_c [F(y(c)), G(y(c))]^{X(c)}`

where `c` ranges over the small base category and
`X(c) = Hom(y(c), X)` by Yoneda. This IS a small
end (over `c`), functorial in `X`.

### Revised Step 2: Powered end formula

Define:

```lean
def endoIhomObj (F G :
    PshRelEdge C ⥤ PshRelEdge C)
    (E : PshRelEdge C) : PshRelEdge C :=
  -- ∫_{(c,i)} [F(y(c,i)), G(y(c,i))]^{E(c,i)}
  -- where E(c,i) = (incl E).obj (c,i) : Type w
  -- and [-,-]^S is the S-indexed power
  -- (product of S copies of [-,-])
```

This uses the POWER `A^S` where `S : Type w` and
`A : PshRelEdge C`. The power `A^S` is the product
of `S` copies of `A`, which exists when `PshRelEdge C`
has products indexed by `S`.

Factor into:

- `pshRelEdgePower (S : Type w) (A : PshRelEdge C)` :
  the S-indexed power `A^S = ∏_{s : S} A`
- `endoIhomDiagram F G E` : the diagram sending
  `(c, i)` to `[F(y(c,i)), G(y(c,i))]^{E(c,i)}`
- `endoIhomObj F G E` : the end (limit) of this diagram
- Show functoriality in `E`

**Estimated effort**: High

## Dependencies

```text
Power → Diagram → End → Functoriality → MonoidalClosed
                                              ↓
                                        Task #156 → Task #157
```

## Open Questions (updated)

1. Does the powered end formula work for `PshRelEdge C`
   specifically, or do we need to go through the
   reflective embedding for the powers?

2. Can we use the reflective embedding more directly:
   compute `[F, G]` in `PSh(C × I^op)` endofunctors
   (where the Yoneda reduction gives a small end),
   then reflect?

3. For the dialgebra application, `F` and `G` are
   Barr lifts of `PSh(C)` endofunctors. Can we exploit
   this structure to define the enriched hom more
   directly?
