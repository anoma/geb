# Adversarial review — types-classifier design, round 3

Reviewer: fresh-context agent. Artifact:
`docs/superpowers/specs/2026-06-09-types-classifier-design.md`
(state as of commit "(doc) Apply round-2 adversarial-review fixes
to types-classifier spec"). mathlib claims checked against the
pinned revision; elaboration claims checked empirically.

## Summary

| # | Severity | Title | Response |
| --- | --- | --- | --- |
| F1 | Minor | §3 "merely unprovable" readable as an irrefutability claim the spec elsewhere declines to make | fix |
| F2 | Minor | §7 `sievePUnitEquiv` row hedges `Quot.sound` while §6 commits to `Sieve.ext`, which carries it | fix |
| F3 | Cosmetic-taste | §3 inline formula `∃ a : U, m a = x : Prop` parses ambiguously | fix |
| F4 | Cosmetic-taste | §11 item 4 page number is pagination-format-dependent | fix |

## Findings

### F1 (Minor) — §3 "merely unprovable" readable as irrefutability

Evidence: the contrast "refutable … merely unprovable" invites
the independence reading the round-2 F2 fix removed.

Author response: fix. Reworded: "for univalence restricted to
subsingletons, this design claims only unprovability, not
independence."

### F2 (Minor) — §7 `sievePUnitEquiv` axiom row vs §6

Evidence: `#print axioms CategoryTheory.Sieve.ext` reports
`propext`, `Quot.sound`; §6 commits the round trips to
`Sieve.ext`, so `Quot.sound` is expected, not merely possible.

Author response: fix. Row now lists `propext`, `Quot.sound`, and
the reviewer's suggested `Classical.choice` hedge for the
transport step.

### F3 (Cosmetic-taste) — §3 inline formula parse

Author response: fix. Rewritten as `(∃ a, m a = x) : Prop` with
the domain stated in prose.

### F4 (Cosmetic-taste) — Page number pagination-dependent

Author response: fix. Page number dropped; the theorem number is
the stable identifier.

## Convergence statement

Round 3: zero blockers, zero serious findings. **Converged.**
This file is the convergence record; the four findings above were
fixed inline after convergence.

Load-bearing claims verified without defect this round (reviewer
summary): §5.1 `typesIsTerminalPUnit` via `IsTerminal.ofUniqueHom`
elaborates as a plain computable `def` with the module's planned
imports, and its `#print axioms` output matches §7; the failure
of `IsTerminal.ofUnique _` reproduces; the full §5.1 assembly
(`typesClassifier` via `mkOfTerminalΩ₀`, the `HasClassifier`
instance, the §8 `rfl` checks) elaborates end-to-end; both §5.2
statements elaborate against the actual
`GebLean.Utilities.Presheaf` declarations; all cited mathlib
names exist at the pinned revision with the stated properties;
§3's modal claims are accurate as rewritten; no
`Classifier (Type u)` exists in mathlib, CSLib, or b-mehta/topos;
Idris line ranges and HoTT book citations are exact; §7 is
consistent with the CLAUDE.md axiom policy; round-2 fixes are all
present and introduced no fresh errors beyond the items above.
