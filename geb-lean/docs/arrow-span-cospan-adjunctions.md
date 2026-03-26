# Arrow-Span and Arrow-Cospan Adjunctions

## Overview

The arrow category of a category C sits between its span and
cospan diagram categories via two adjunctions, each requiring
only a single colimit or limit construction per diagram:

- **Pushouts** yield a reflective inclusion of arrows into spans.
- **Pullbacks** yield a coreflective inclusion of arrows into
  cospans.

Both are formalized in
`GebLean/Utilities/ArrowSpanAdjunction.lean` and
`GebLean/Utilities/ArrowCospanAdjunction.lean`, parameterized
by explicit (co)limit cone assignments to avoid
`Classical.choice`.

## The Pushout (Span) Side

Given constructive pushouts
`(S : WalkingSpan ⥤ C) → ColimitCocone S`:

```text
spanArrowReflector pushouts ⊣ arrowSpanInclusion C
```

The inclusion sends an arrow `f : P ⟶ Q` to the span
`P ←[𝟙]─ P ─[f]→ Q`. The reflector sends a span
`P ← R → Q` to the arrow `P → pushout(P, R, Q)` given by
the left injection into the pushout.

### Interpretation: functionalizing relations

A span `P ← R → Q` represents a relation between P and Q,
with R witnessing the related pairs via the two projections.
The reflector *functionalizes* this relation: it identifies
`inl(p)` with `inr(q)` whenever `(p, q)` is witnessed by some
`r ∈ R`, producing a quotient arrow `P → (P ⊕ Q)/~`. This
collapses a many-valued correspondence into a single-valued
function by quotienting.

The counit at an arrow `f` maps the pushout of
`span (𝟙 P) f` back to `Q` via `[inl(p)] ↦ f(p)` and
`[inr(q)] ↦ q`, recovering `f` from its reflection.

## The Pullback (Cospan) Side

Given constructive pullbacks
`(S : WalkingCospan ⥤ C) → LimitCone S`:

```text
arrowCospanInclusion C ⊣ cospanArrowCoreflector pullbacks
```

The inclusion sends an arrow `f : P ⟶ Q` to the cospan
`P ─[f]→ Q ←[𝟙]─ Q`. The coreflector sends a cospan
`P → X ← Q` to the arrow `P ×_X Q → Q` given by the right
projection from the pullback.

### Interpretation: tabulating correspondences

A cospan `P → X ← Q` represents an *implicit* correspondence:
`p` relates to `q` when `f(p) = g(q)` in the common codomain
`X`. The coreflector *tabulates* this correspondence: it
extracts the fiber product `P ×_X Q = { (p, q) | f(p) = g(q) }`
and projects onto Q, producing a subobject arrow. This refines
an implicit agreement condition into an explicit function by
restricting to the compatible pairs.

The unit at an arrow `f` lifts `P` into the pullback of
`cospan f (𝟙 Q)` via `p ↦ (p, f(p))`, embedding `f` into its
coreflection.

## Duality

The two constructions are formal duals:

| Span / Pushout | Cospan / Pullback |
|---|---|
| Relation: explicit witness `R` | Correspondence: implicit condition in `X` |
| Reflector: quotient (collapse) | Coreflector: fiber product (restrict) |
| Counit recovers the arrow | Unit embeds the arrow |
| `P → (P ⊕ Q) / ~` | `P ×_X Q → Q` |
| Many-valued → single-valued | Implicit → explicit |
| Existential (∃ r) | Universal (∀ compatible pairs) |

In the language of relation theory: functionalization
produces a quotient from an explicit relation, while
tabulation produces a subobject from an implicit
correspondence.

In database terms: functionalization corresponds to
`GROUP BY` (collapsing equivalence classes), while
tabulation corresponds to `INNER JOIN` (extracting
matching records from a shared key space).

## Connection to Subobject Classification

In a topos, every subobject `R ↪ P × Q` is classified by
a characteristic morphism `χ : P × Q → Ω` into the subobject
classifier. The cospan `P × Q → Ω ← 1` (with `true : 1 → Ω`)
represents the relation intensionally. The pullback of this
cospan recovers `R` extensionally. The arrow-cospan adjunction
generalizes this pattern to arbitrary cospans in any category
with pullbacks.

## Presheaf Instantiation

For presheaf categories `PSh(C) = Cᵒᵖ ⥤ Type w`:

- `pshSpanPushouts C` provides constructive pushouts via
  pointwise `Quot` in `Type w`.
- Constructive pullbacks can be provided via pointwise
  `Subtype` in `Type w` (the fiber product at each stage is
  `{ (p, q) | f(p) = g(q) }`).

The span-side presheaf instantiation is used in the reflective
chain `PSh(C) ↪ Arrow(PSh(C)) ↪ WalkingSpan ⥤ PSh(C)` and
in the functionalization of presheaf relations
(`PshRelEdgeFunctionalize.lean`).
