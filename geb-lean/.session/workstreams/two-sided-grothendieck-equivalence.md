# Two-Sided Grothendieck: Equivalence Between Orderings

## Status

Partial.  The two orderings
(`twoSidedGrothendieckCovContra` and `twoSidedGrothendieckContraCov`)
in `GebLean/Utilities/Grothendieck.lean` have an object-level type
equivalence (`twoSidedGrothendieckObjEquiv`) at each bifunctor `H`.
A full `CategoryTheory.Equivalence` between the two Cat objects is
not yet formalized.

## What's done

- Pointwise object `Equiv`: `twoSidedGrothendieckObjEquiv H`
  exhibits a bijection between the underlying object types, with
  both roundtrips by `rfl`.  Confirms both orderings encode the same
  Lucyshyn-Wright triples `(d, c, y)` modulo nested `Opposite`
  presentation.

## What remains

A full `CategoryTheory.Equivalence` between the underlying Cat
objects at each `H` — i.e., providing forward / backward Cat
functors with strict `map_id` / `map_comp`, plus unit / counit
natural isomorphisms.  The challenge is that the forward / backward
Cat functors require `eqToHom` chasing through three nested
`Grothendieck` + `Opposite` layers; `Grothendieck.comp_fiber`
introduces `eqToHom` terms that don't cleanly cancel under the
project's strict `backward.isDefEq.respectTransparency = false`
setting.

Two attempts by subagents (a general implementer and
`lean4:sorry-filler-deep`) hit the same proof-obligation wall for
`map_id` / `map_comp` of the reshuffle functors.  A third attempt
restricted scope to the object-level `Equiv`, which succeeded
cleanly.

## Approaches to consider if returning to this

1. **Build the Cat functors as compositions** of existing mathlib
   operations whose functoriality is already established (e.g.,
   chains of `Grothendieck.pre`, `Grothendieck.map`, `Cat.opFunctor`,
   `Functor.op`, `Functor.leftOp`, etc.) — avoids direct
   `map_id` / `map_comp` obligations.
2. **Use a pseudofunctor / bicategorical framework** — promote
   both constructions to `Pseudofunctor` and use mathlib's
   `StrongTrans` from `CategoryTheory.Bicategory.NaturalTransformation.Pseudo`.
3. **Follow the `ConnectedGrothendieck.lean` pattern more closely** —
   that file proved an analogous equivalence via type `Equiv` +
   explicit `cases` on dependent equalities + heavy `eqToHom` chasing.
   Adaptation needed because that file uses custom `op'` (involutive
   by `rfl`) while we use mathlib's `Opposite`.

## Related files

- `GebLean/Utilities/Grothendieck.lean`, `StrictTwoSidedGrothendieck`
  section (around line 7318–7636).
- `GebLean/Utilities/ConnectedGrothendieck.lean` — reference for
  similar equivalence proofs.
- `docs/two-sided-grothendieck-construction.md` — mathematical
  reference (Lucyshyn-Wright / Stefanich).
- `docs/superpowers/specs/2026-04-13-strict-two-sided-grothendieck-design.md` —
  design spec.
- `docs/superpowers/plans/2026-04-13-strict-two-sided-grothendieck.md` —
  implementation plan.
