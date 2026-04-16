# Two-Sided Grothendieck: Equivalence Between Orderings

## Status

Partial (substantial infrastructure in place; full Cat functoriality
still blocked).

The two orderings `twoSidedGrothendieckCovContra` and
`twoSidedGrothendieckContraCov` in
`GebLean/Utilities/Grothendieck.lean` have:

- An object-level type equivalence (`twoSidedGrothendieckObjEquiv`)
  with both roundtrips by `rfl`.
- Symmetric constructor/destructor APIs (`TwoSidedGrothendieckCovContra`
  and `TwoSidedGrothendieckContraCov` namespaces) with identical type
  signatures, providing `mkObj` / `objD` / `objC` / `objFiber` and
  `mkHom` / `homD` / `homC` / `homFiber` plus roundtrip simp lemmas.
- Composition-helper simp lemmas: `homD_id` / `homC_id` / `homD_comp`
  / `homC_comp` in both namespaces (four of eight are `rfl`; four
  require internal `Grothendieck.id_fiber`/`comp_fiber` rewrites).
- Primitive `forwardObj` / `forwardMap` / `backwardObj` / `backwardMap`
  functions in a `twoSidedGrothendieckEquiv` namespace, built
  compositionally via destructors + constructors.

A full `CategoryTheory.Equivalence` is not yet formalized.  The
blocker is the `map_id` and `map_comp` proof obligations for the
full Cat functors: the `w_fiber` sub-goal after `Grothendieck.ext`
requires chasing `eqToHom` through three nested
Grothendieck + Opposite layers, with motive type errors at each
rewrite step.

## Three attempts, same wall

1. Direct field-by-field construction (pre-API work) — failed on
   `map_id` and `map_comp` for the Cat functors.
2. After compositional refactor of `projC` / `projD` — the same
   technique does not extend to the equivalence functors because
   there's no analogous "target nat-trans to a constant" factoring.
3. With symmetric API + helper lemmas + primitive obj/map — `map_id`
   on the Cat functors closes `w_base`, but `w_fiber` still requires
   motive-dependent `eqToHom` rewrites.

Each attempt added genuine infrastructure.  The fundamental blocker
is `Grothendieck.comp_fiber` + `Grothendieck.id_fiber` introducing
`eqToHom` terms that must be canceled across the nested
Grothendieck + Opposite structure, and this cancellation hits
motive errors under `Grothendieck.ext`.

## What's done (on branch terence/grothendieck)

- `twoSidedGrothendieckObjEquiv H` — object-level `Equiv` (rfl
  roundtrips).
- `TwoSidedGrothendieckCovContra` namespace (11 defs + 9 simp
  lemmas).
- `TwoSidedGrothendieckContraCov` namespace (11 defs + 9 simp
  lemmas).
- `twoSidedGrothendieckEquiv.forwardObj`,
  `twoSidedGrothendieckEquiv.forwardMap`,
  `twoSidedGrothendieckEquiv.backwardObj`,
  `twoSidedGrothendieckEquiv.backwardMap` — primitive, not yet
  wrapped as Cat functors.
- `twoSidedGrothendieckEquiv.homEquivForward` and
  `.homEquivBackward` — pointwise hom-set `Equiv`s between the
  two orderings.  Both roundtrips close by `rfl` (η-expansion on
  `mkHom` with `homD`/`homC`/`homFiber` destructors is
  definitional).

## What remains

- `twoSidedGrothendieckEquiv.forward` and `.backward` as
  `CategoryTheory.Functor` (requires `map_id` and `map_comp`
  proofs).
- `twoSidedGrothendieckEquiv.unitIso` and `.counitIso`.
- Full `twoSidedGrothendieckEquivalence` as a
  `CategoryTheory.Equivalence` at each `H`.
- Possibly naturality in `H`.

## Approaches to consider if returning to this

1. **Use a pseudofunctor / bicategorical framework** — promote both
   constructions to `Pseudofunctor` and use mathlib's `StrongTrans`
   from `CategoryTheory.Bicategory.NaturalTransformation.Pseudo`.
2. **Introduce an explicit intermediate form** — e.g., define a
   "direct" version of the strict two-sided Grothendieck as
   `Functor.uncurry ⋙ Grothendieck.functor ⋙ slice-manipulation`,
   and prove both orderings equivalent to it.  This shifts the
   `eqToHom` chasing to a different (possibly simpler) place.
3. **Target a hom-set bijection** — skip `CategoryTheory.Equivalence`
   and state a `∀ H x y, (x ⟶ y) ≃ (forwardObj x ⟶ forwardObj y)`.
   Weaker but potentially easier.
4. **Follow the `ConnectedGrothendieck.lean` pattern** — their proof
   benefits from `op'` being involutive by `rfl`; adapting to
   mathlib's `Opposite` is the core difficulty.

## Related files

- `GebLean/Utilities/Grothendieck.lean`, `StrictTwoSidedGrothendieck`
  section (lines ~7318–7970).
- `GebLean/Utilities/ConnectedGrothendieck.lean` — reference for
  similar equivalence proofs.
- `docs/two-sided-grothendieck-construction.md` — mathematical
  reference (Lucyshyn-Wright / Stefanich).
- `docs/superpowers/specs/2026-04-13-strict-two-sided-grothendieck-design.md`
  — design spec.
- `docs/superpowers/plans/2026-04-13-strict-two-sided-grothendieck.md`
  — implementation plan.
