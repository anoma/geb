# Adversarial review — types-classifier design, round 2

Reviewer: fresh-context agent. Artifact:
`docs/superpowers/specs/2026-06-09-types-classifier-design.md`
(state as of commit "(doc) Apply round-1 adversarial-review fixes
to types-classifier spec"). mathlib claims checked against the
pinned revision; load-bearing elaboration claims checked
empirically against this project's environment.

## Summary

| # | Severity | Title | Response |
| --- | --- | --- | --- |
| F1 | Blocker | §5.1 `IsTerminal.ofUnique _` does not elaborate: no `Unique (X ⟶ PUnit)` instance is synthesized | fix |
| F2 | Serious | §3 Idris independence claim unsupported: Idris proves UIP, so the simplicial model does not model its theory | fix |
| F3 | Minor | §7 axiom-budget row for `typesIsTerminalPUnit` contradicted empirically | fix |
| F4 | Minor | §11 punch-list item 2 cites `WClassifier`; stale after round-1 F3 fix | fix |
| F5 | Minor | §9 "requires new general machinery" inaccurate; contradicts §2 | fix |
| F6 | Cosmetic-taste | "cost center" metaphor in §6 | fix |

## Findings

### F1 (Blocker) — §5.1 `IsTerminal.ofUnique _` does not elaborate

Evidence: `Mathlib/CategoryTheory/Limits/Shapes/IsTerminal.lean:79`
requires `[h : ∀ X : C, Unique (X ⟶ Y)]`. Typeclass resolution
does not unfold `X ⟶ PUnit` (a `Quiver.Hom` projection through
the `types` category instance) to `X → PUnit`, so the instance is
not found. Verified empirically with the module's planned
imports: the §5.1 definition fails with "failed to synthesize
instance ... `(X : Type u) → Unique (X ⟶ PUnit)`". The cited
precedent `pshTerminalIsTerminal` works only because of the
explicit `instance pshTerminalUnique`
(`GebLean/Utilities/Presheaf.lean:672–680`), which the spec did
not carry over. Two repairs verified to elaborate computably:
an explicit `Unique` instance plus `ofUnique`, or
`IsTerminal.ofUniqueHom (fun _ _ => PUnit.unit)
(fun _ _ => funext fun _ => rfl)` (the form mathlib's
`SubobjectRepresentableBy.isTerminalΩ₀` uses).

Author response: fix. Adopted the `ofUniqueHom` form (no new
instance; smaller API surface); §5.1 code block and prose
updated, including the reason `ofUnique _` fails.

### F2 (Serious) — §3 Idris independence claim unsupported

Evidence: independence requires a model validating the principle;
the simplicial model validates univalence but refutes UIP, and
Idris proves UIP (`geb-idris/src/Library/IdrisUtils.idr:450–452`,
axiom-K pattern matching; `ChiForHProp` itself invokes `uip`). A
theory proving UIP has no simplicial model, so the
irrefutability half of the claim is unsupported. The
set-theoretic half (unprovability) stands.

Author response: fix. §3 now claims unprovability only, for both
systems, and notes that both prove unique identity proofs, so
models of full univalence do not apply to them.

### F3 (Minor) — §7 axiom row for `typesIsTerminalPUnit` inaccurate

Evidence: `#print axioms typesIsTerminalPUnit` (with either F1
repair) reports `propext`, `Classical.choice`, `Quot.sound` —
autoparam-discharged `IsLimit` proof fields pull in
`Classical.choice`; `funext` pulls in `Quot.sound`. The
definition remains computable; no rule violated, but the table
would fail its own audit.

Author response: fix. `typesIsTerminalPUnit` moved to its own
row listing the three axioms, with the computability note.

### F4 (Minor) — Stale `WClassifier` reference in §11 item 2

Evidence: after the round-1 F3 fix, the universe pattern is
attributed to `pshSieveFunctor`/`pshClassifierData` in
`Presheaf.lean`; §11 item 2 still pointed reviewers at
`WClassifier`.

Author response: fix. §11 item 2 now names
`pshSieveFunctor`/`pshClassifierData`.

### F5 (Minor) — §9 transfer-exclusion rationale inaccurate

Evidence: every component of the transport exists at the pinned
revision (`Classifier.ofEquivalence`, `Discrete.opposite`,
`Equivalence.congrLeft`, the `Discrete PUnit ⥤ C ≌ C`
equivalence), so "requires new general machinery" is false and
contradicts §2's derivability statement.

Author response: fix. §9 bullet restated: composable from
existing mathlib declarations, excluded because the transported
classifying object is not `ULift Prop` and §5.2's comparison
delivers the cross-check.

### F6 (Cosmetic-taste) — "cost center" metaphor

Evidence: CLAUDE.md § Avoid colloquialisms and metaphors.

Author response: fix. Reworded to "the expected largest step of
this proof".

## Convergence statement

Round 2: one blocker (F1), one serious (F2). Not converged;
round 3 required after revisions.

Verified without defect by this reviewer: `mkOfTerminalΩ₀` exact
signature (the spec's `typesCharMap_unique` matches its `uniq`
argument shape argument-for-argument; computable given computable
arguments); `Classifier.ofEquivalence`; `Types.isPullback_iff`
and `Types.exists_of_isPullback` statements, universes, and the
§6 usage shapes; `mono_iff_injective`; `Sieve.ext`;
`Discrete.ext`; the §6 transport story; §8's `rfl` claims for
`typesClassifier.Ω`/`.truth`; `Mono` and `HasClassifier` are
`Prop`-classes; `Limits.Types.isTerminalPUnit` noncomputability
and deprecation date; absence of `Classifier (Type u)` in mathlib
and of `Classifier` in CSLib; Idris-source and HoTT-book claims;
`scripts/check-axioms.sh` accepted-axiom list; index-file
conventions; naming/casing against fresh fetches of the mathlib
guides; markdownlint cleanliness and current TOC.
