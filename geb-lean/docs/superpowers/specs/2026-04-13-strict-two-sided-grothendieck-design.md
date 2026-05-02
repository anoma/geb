# Strict Two-Sided Grothendieck Construction — Design

## Context

Our `GebLean/Utilities/Grothendieck.lean` currently contains two
non-slice-refined "two-sided Grothendieck" definitions
(`twoSidedGrothendieckCovContra`, `twoSidedGrothendieckContraCov`) plus
an exploratory uncurried strict version
(`strictTwoSidedGrothendieckUncurried`). These do not match the standard
mathematical construction as documented in
`docs/two-sided-grothendieck-construction.md` (Lucyshyn-Wright, *Bifold
Algebras and Commutants*, Def. 7.1; cf. Stefanich, [arXiv:2011.03027](https://arxiv.org/pdf/2011.03027)).

They are to be removed and replaced with a single strict construction
having two equivalent compositional realizations, landing in a slice
category of `Cat` over the product category `C × D`. The slice
refinement is how the commutativity conditions inherent to the two-sided
construction are expressed: morphisms in `Over (Cat.of (C × D))` must
commute strictly with the product projection, capturing both the
`C`-direction and the `D`-direction commutativities in one witness.

## Reference

- Lucyshyn-Wright, *Bifold Algebras and Commutants*, Def. 7.1.
- Stefanich, "Presentable (∞, n)-categories" ([arXiv:2011.03027](https://arxiv.org/pdf/2011.03027)).
- Project note: `docs/two-sided-grothendieck-construction.md`.

## Requirements

1. Remove the existing non-slice-refined two-sided Grothendieck
   definitions: `twoSidedGrothendieckCovContra`,
   `twoSidedGrothendieckContraCov`,
   `strictTwoSidedGrothendieckUncurried` (and their supporting section
   structure).
2. Provide a strict two-sided Grothendieck landing in
   `Over (Cat.of (C × D))`, matching the Lucyshyn-Wright construction.
3. Realize it in two compositional ways (covariant-then-contravariant
   and contravariant-then-covariant orderings), *both* landing in the
   same `Over (Cat.of (C × D))` slice.
4. Prove the two realizations are naturally isomorphic.
5. Build the two-sided functors as thin compositions of reusable
   higher-order slice-preserving Grothendieck constructions, which are
   themselves useful primitives.

## Architecture

### Building blocks (new primitives)

Two new slice-preserving Grothendieck constructions, each one a genuine
categorical primitive in its own right:

```lean
/- Slice-preserving contravariant Grothendieck. -/
def sliceContraFunctor {C D : Cat.{v, u}} :
    (Dᵒᵖ ⥤ Over (T := Cat.{v, u}) C) ⥤
      Over (T := Cat.{v, u}) (Cat.of (C × D))

/- Slice-preserving covariant Grothendieck. -/
def sliceCovFunctor {C D : Cat.{v, u}} :
    (C ⥤ Over (T := Cat.{v, u}) D) ⥤
      Over (T := Cat.{v, u}) (Cat.of (C × D))
```

These generalize `grothendieckContraFunctorOver` and mathlib's
`Grothendieck.functor` respectively, from "input is a `C ⥤ Cat`" to
"input is a `C ⥤ Over X`" functor — preserving the inner slice
structure by combining with the outer Grothendieck projection to
land in a slice over the product.

### Two-sided constructions (thin compositions)

```lean
def twoSidedGrothendieckCovContra {C D : Cat.{v, u}} :
    (Dᵒᵖ ⥤ C ⥤ Cat.{v, u}) ⥤
      Over (T := Cat.{v, u}) (Cat.of (C × D)) :=
  (Functor.whiskeringRight _ _ _).obj Grothendieck.functor ⋙
    sliceContraFunctor

def twoSidedGrothendieckContraCov {C D : Cat.{v, u}} :
    (Dᵒᵖ ⥤ C ⥤ Cat.{v, u}) ⥤
      Over (T := Cat.{v, u}) (Cat.of (C × D)) :=
  flipFunctor _ _ _ ⋙
    (Functor.whiskeringRight _ _ _).obj grothendieckContraFunctorOver ⋙
    sliceCovFunctor
```

### Natural isomorphism

```lean
def twoSidedGrothendieckIso {C D : Cat.{v, u}} :
    twoSidedGrothendieckCovContra (C := C) (D := D) ≅
      twoSidedGrothendieckContraCov (C := C) (D := D)
```

## Data Flow

```
  (Dᵒᵖ ⥤ C ⥤ Cat)
        │
        │ whiskeringRight.obj Grothendieck.functor
        ▼
  (Dᵒᵖ ⥤ Over C)              ← slice-refined inner, cov direction
        │
        │ sliceContraFunctor
        ▼
  Over (Cat.of (C × D))        ← strict two-sided total
```

And analogously via flip + slice-refined contra inner + `sliceCovFunctor`.

### Object-level unfolding (for verification)

For `H : Dᵒᵖ ⥤ C ⥤ Cat` and the CovContra path:

- `H` paired with `whiskeringRight.obj Grothendieck.functor` gives
  `G : Dᵒᵖ ⥤ Over C` with
  `G.obj (op d) = (Cat.of (Grothendieck (H.obj (op d))), forget_d)`,
  so the fibre at `d` is the ordinary covariant Grothendieck of
  `H(d, -) : C ⥤ Cat`, together with its projection to `C`.
- `sliceContraFunctor G` has:
  - Total category: the contravariant Grothendieck of `G ⋙ Over.forget`,
    which at the level of objects is `(d : D, (c : C, y : H(d, c)))`.
  - Projection to `C × D`: the pair of
    - the "C" coordinate, built from `G`'s slice structure
      (`G(op d).hom.obj : X_d → C`), and
    - the "D" coordinate, built from the contravariant Grothendieck
      forgetful (`(d, _) ↦ d`).
- Morphisms in `Over (Cat.of (C × D))` must strictly commute with this
  pair projection, which is equivalent to the Lucyshyn-Wright morphism
  data `(a : d → d', b : c → c', x : b!(X) → a*(X'))`.

### The natural iso

At each `H`, the underlying `Cat` objects of `twoSidedCovContra.obj H`
and `twoSidedContraCov.obj H` are not literally equal as types (they
differ in `Opposite`-wrapper nesting), but they are canonically
isomorphic via object reshuffling `⟨d, c, y⟩ ↔ ⟨c, d, y⟩` modulo
appropriate `op`/`unop` unwrapping. The iso lifts to an iso in
`Over (C × D)` because both projections land in the same pair.

## Implementation Components

Ordered by build dependency:

### 1. Remove obsolete code
- Delete `twoSidedGrothendieckCovContra` (current non-slice-refined).
- Delete `twoSidedGrothendieckContraCov` (current non-slice-refined).
- Delete `strictTwoSidedGrothendieckUncurried`.
- Delete the `TwoSidedGrothendieck` and `StrictTwoSidedViaUncurry`
  sections if fully obsolete.

### 2. `sliceContraFunctor`
- `obj`: builds the pair-projection functor from the contra-Groth total
  to `C × D`.
- `map`: induced functor with commutativity proof.
- `map_id`, `map_comp`: via reuse of `Grothendieck.map_id_eq`,
  `Grothendieck.map_comp_eq`, and `Over` structure.

Pair-projection internal construction:
- `π_D`: reuse `grothendieckContraFunctorOver D`'s `.hom` on
  `G ⋙ Over.forget`.
- `π_C`: apply `grothendieckContraFunctor D .map` to the natural
  transformation `G ⋙ Over.forget ⟶ Δ C` (extracted from `G`'s
  `.hom` fields), then use a direct functor
  `grothContraD(Δ C) ⥤ C` built without going through a full
  `grothContraD(Δ C) ≅ D × C` equivalence proof.
- Combine via `prod.lift π_C π_D` (mathlib's product pairing).

### 3. `sliceCovFunctor`
- Symmetric construction to `sliceContraFunctor` but for covariant
  outer and contravariant inner (so input is `C ⥤ Over D` rather than
  `Dᵒᵖ ⥤ Over C`).
- Same shape: `obj`, `map`, `map_id`, `map_comp`.

### 4. `twoSidedGrothendieckCovContra` (new)
- Thin composition.

### 5. `twoSidedGrothendieckContraCov` (new)
- Thin composition with `flipFunctor`.

### 6. `twoSidedGrothendieckIso`
- Natural iso between CovContra and ContraCov orderings.
- Construction: exhibit forward and backward Cat-Homs at each `H`
  that reshuffle the object/morphism data, verify they're mutual
  inverses (by `rfl`-friendly `Over.homMk` + Grothendieck-structure
  equalities), and verify naturality in `H`.

## Error Handling

Not applicable — this is pure categorical Lean. The "error" modes are:
- Universe inference failures → handled with explicit `@[...]` and
  universe annotations.
- Typeclass synthesis on `Cat.of (C × D)` → mathlib provides the
  product-category instance.
- Opposite-nesting definitional-equality issues → handled with
  `Quiver.Hom.op/.unop` wrapping (cf. our existing `mkHom`,
  `homBase`, etc. for `grothendieckContraFunctor`).

## Testing

- `lake build` must pass with no warnings.
- `lake test` must pass.
- Project constraints: no `sorry`, no `admit`, no custom axioms,
  standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).
- `twoSidedGrothendieckIso`'s forward and inverse components are mutual
  inverses (the `hom_inv_id` and `inv_hom_id` fields of the iso).

## Scope and Risk

**In scope:**
- `sliceContraFunctor`, `sliceCovFunctor`, `twoSidedGrothendieckCovContra`,
  `twoSidedGrothendieckContraCov`, `twoSidedGrothendieckIso`.
- Deletion of the three obsolete definitions.

**Out of scope:**
- Generalizing to `Cat.{v', u'}` with differing universe levels from the
  base (would follow the mathlib pattern that same-universe is required
  for slice-refined constructions).
- Providing a third "direct" definition via uncurrying (mentioned as
  Approach C in the brainstorm) — one canonical construction with two
  iterated realizations suffices.

**Risks:**
- The natural iso proof may require more machinery than expected, since
  the two sides nest opposites differently. If pure `rfl`-style proofs
  fail, we may need `Functor.ext` + explicit object/morphism iso
  construction (~50-100 lines).
- `grothContraD(Δ C) ⥤ C` direct projection — may require explicit
  construction rather than reuse of mathlib machinery.

**Fallback:** If a component proves intractable, pause and escalate
to the user for direction rather than attempting `sorry`-stubs (no
`sorry` is allowed by project policy). The `sorry-filler-deep` agent
may be used as a tactic for filling specific proof obligations
within bounded scope, as done successfully for the morphism
convenience API of `grothendieckContraFunctor`.

## File Layout

All changes in `GebLean/Utilities/Grothendieck.lean`:

- Delete obsolete section contents.
- Add new section `StrictTwoSidedGrothendieck` after
  `GrothendieckContraFunctorOver` (since `sliceContraFunctor` uses that)
  and before `CatOverCat`.
- Structure of the new section:
  1. `sliceContraFunctor` and supporting lemmas.
  2. `sliceCovFunctor` and supporting lemmas.
  3. `twoSidedGrothendieckCovContra` (composition).
  4. `twoSidedGrothendieckContraCov` (composition).
  5. `twoSidedGrothendieckIso` natural iso.
