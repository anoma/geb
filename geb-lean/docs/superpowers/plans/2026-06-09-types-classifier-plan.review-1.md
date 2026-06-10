# Adversarial review — types-classifier plan, round 1

Reviewer: fresh-context agent. Artifact:
`docs/superpowers/plans/2026-06-09-types-classifier-plan.md`
(state as of commit "(doc) Add types-classifier implementation
plan"). The reviewer empirically elaborated the plan's Lean code
blocks against the pinned toolchain and this repository's
environment.

## Summary

| # | Severity | Title | Response |
| --- | --- | --- | --- |
| F1 | Blocker | Task 6 member example fails to elaborate; no fallback given | fix |
| F2 | Serious | Task 6 non-member example fails as written; note's fallback is mandatory | fix |
| F3 | Minor | Task 7 Step 4 counts five implementation commits; Tasks 1–6 produce six | fix |
| F4 | Minor | Task 0 Step 1 expected branch-head description already stale | fix |
| F5 | Minor | Commit subjects of Tasks 2, 3, 4, 6 are noun phrases, not imperative | fix |
| F6 | Minor | `typesHasClassifier` instance lacks the mandatory docstring | fix |
| F7 | Minor | New modules omit the `module` keyword mandated by lean-coding rules | fix (deviation recorded) |
| F8 | Cosmetic-taste | `## Main declarations` deviates from required section names | fix |
| F9 | Cosmetic-taste | Import-ordering convention claim unsupported | fix |

## Findings

### F1 (Blocker) — Task 6 member example fails to elaborate

Evidence (empirical): `typesCharMap_apply_eq_true _ ⟨4, rfl⟩`
fails with "Invalid `⟨...⟩` notation: The expected type of this
term could not be determined" — the morphism hole leaves the
subtype a metavariable when the anonymous constructor
elaborates. The plan's own escalation rule makes this a halt
point. The reviewer verified the repair
`typesCharMap_apply_eq_true _ (⟨4, rfl⟩ : {n : Nat // n % 2 =
0})` elaborates, and that naming the morphism instead does NOT
work (the predicate is inferred from the witness).

Author response: fix. Adopted the type-ascription form; an
implementer note records why the two alternatives fail.

### F2 (Serious) — Task 6 non-member example fails as written

Evidence (empirical): `Nat.one_ne_zero (ha ▸ a.property)` fails
— `▸` computes its motive from the expected type `1 = 0`, which
contains neither side of `ha`. The note's conditional framing
("If the `▸` motive fails") is wrong: the failure is
unconditional at the pin.

Author response: fix. The reviewer's verified `by`-block
rewrite (`have hp := a.property; rw [ha] at hp; exact hp`) is
now the primary code; the note states the motive failure as
fact.

### F3 (Minor) — Commit count in Task 7 Step 4

Author response: fix. "five" corrected to "six (five `feat`,
one `test`)".

### F4 (Minor) — Stale branch-head description in Task 0

Author response: fix. Expectation pinned to the stable facts
(clean working copy; parent at the `feat/types-classifier`
bookmark) rather than a specific description.

### F5 (Minor) — Non-imperative commit subjects

Evidence: mathlib commit convention requires imperative present
tense; Tasks 2, 3, 4, 6 had verbless subjects.

Author response: fix. Subjects now "prove pullback square…",
"prove uniqueness…", "assemble Classifier (Type u)…", "add
classifier evaluation and round-trip tests".

### F6 (Minor) — Missing instance docstring

Evidence: `.claude/rules/lean-coding.md` § Comment and
docstring rules mandates docstrings for every `instance`.

Author response: fix. Added "/-- `Type u` has a subobject
classifier. -/".

### F7 (Minor) — `module` keyword omitted

Evidence: `.claude/rules/lean-coding.md` § Lean 4 module system
mandates the `module` keyword; no existing `GebLean` source
uses it; the plan followed practice without recording the
conflict.

Author response: fix (deviation recorded). Task 1 now carries
an explicit note: a lone module-system file would interact with
non-module importers through visibility rules the surrounding
code is not written for; repository-wide migration is out of
scope. The rule/practice conflict is also surfaced to the user
at plan handoff.

### F8 (Cosmetic-taste) — Docstring section name

Author response: fix. `## Main declarations` renamed to
`## Main definitions` (matches the digest and `Presheaf.lean`).

### F9 (Cosmetic-taste) — Unsupported convention claim

Author response: fix. The parenthetical convention claim
dropped; the concrete import instruction stands.

## Convergence statement

Round 1: one blocker (F1), one serious (F2). Not converged;
round 2 required after revisions.

Verified without defect by the reviewer (empirically, except
where noted): Task 1's module exactly as written; Task 2's
`typesCharMap_isPullback` exactly as written (no fallback
needed); Task 3's `typesCharMap_unique` exactly as written
(structure-eta `congrArg` steps accepted); Task 4's
`mkOfTerminalΩ₀` invocation, instance, and both `rfl`
spot-checks; Task 5's `sievePUnitEquiv` and
`sievePUnitEquiv_truth` exactly as written; Task 6's four other
examples; all axiom sets match the plan's expectations;
mathlib signatures by inspection (`mkOfTerminalΩ₀`,
`isPullback_iff`, `exists_of_isPullback`,
`mono_iff_injective`, `Sieve.ext`, `Sieve.top_apply`);
repository facts (import anchors, `testDriver`, scripts, `jj`
recipe, topic branch); spec fidelity of every §5.1/§5.2
signature and §8 test; markdownlint cleanliness and current
TOC.
