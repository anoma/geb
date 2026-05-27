# T5 final holistic review

## Summary

The T5 branch (`feat/t5-equivalence`, change `qosxnzpw` /
commit `ce928eec`) implements the categorical equivalence
`LawvereERCat ≌ LawvereKSimDCat 2` as five small task
commits (T5.A.1, T5.A.2, T5.B.1, T5.B.2, T5.C) plus
preceding spec / plan documentation commits. The final
state hangs together as a coherent feature: all
identifiers, mirror citations, axiom-allow annotations,
and module-docstring sections are consistent across the
three touched Lean files. Verdict: ready for PR. Findings:
0 blockers, 0 serious, 4 minor, 2 nits.

## Branch state

```text
qosxnzpwwtzq feat(equivalence): package LawvereERCat ≌ LawvereKSimDCat 2
qzwqlqytkltw feat(equivalence): add eqToIso natural isos
olqqwxpswlwz feat(equivalence): add round-trip strict equalities
sxvvztyvmkvp feat(ertok): add erToKFunctor_comp_kInterp
yssuztrnrszm docs(equivalence): fold module-docstring update into T5.A.2 plan task
ysxxynslzoso feat(ertok): add erToKFunctor_map_interp
txopuzrlstzp docs(equivalence): add missing LawvereERInterp import to T5.A.1 plan/spec
syvyqqtlzwqp docs(equivalence): record T5 plan round-5 review (CONVERGED)
znopxolzmysl docs(equivalence): apply T5 plan round-4 fixes (stale prose + minimal simp set)
qtuqwzzywnmx docs(equivalence): apply T5 plan round-3 fixes + spec triangle-discharge amendment
xromsooqqrpv docs(equivalence): apply T5 plan round-2 fixes + spec proof-shape amendment
oyktuwypsknv docs(equivalence): apply T5 plan round-1 adversarial-review fixes
konznknxoqtq docs(equivalence): write T5 implementation plan
pyronxvsxtwm docs(equivalence): record T5 spec round-3 review (CONVERGED) and reconcile T5.C LOC
vomkmtwokqmm docs(equivalence): apply T5 spec round-2 adversarial-review fixes
puuuuzzkyzok docs(equivalence): apply T5 spec round-1 adversarial-review fixes
zqtutvlszmkq docs(equivalence): write T5 categorical equivalence spec
```

`jj diff --stat`: 5501 insertions, 3 deletions across
3 Lean files plus 10 spec/plan markdown files.

## Verification ran

- `lake build`: pass (`Build completed successfully (1565 jobs).`).
- `lake test`: pass (exit 0; the `GebLeanTests` driver runs
  without output on success).
- `bash scripts/check-axioms.sh GebLean/LawvereERKSim/Equivalence.lean
  GebLean/LawvereERKSim/ErToKFunctor.lean`: pass.
  - `Equivalence.lean`: 7 declarations, all using only standard
    axioms.
  - `ErToKFunctor.lean`: 10 declarations, all using only
    standard axioms.
  - Envelope: `propext`, `Quot.sound`, `quot.sound`.
- `lake lint`: one warning, but it is pre-existing and not
  caused by T5. `GebLean/Utilities/KSimURMSimulator.lean:201`
  reports `@GebLean.KMor1.interp_pcDispatch_match` is not in
  simp-normal form. That file was added in T3 (commits
  `66bb20aa`–`3fd85f3e`); T5 does not touch it and no T5
  diff hunk lands in `Utilities/`. Recommend opening a
  separate issue to address.

## Findings

### M (minor) — spec uses `𝟙` glyph where code uses `𝟭`

- Files:
  `docs/superpowers/specs/2026-05-25-step-t5-equivalence-design.md`
  lines 203–206, 472, 476 (and TOC references).
- The spec's §4.2 / §4.3 tables and §6.5 code-block render
  the round-trip identities with `𝟙 LawvereERCat` and
  `𝟙 (LawvereKSimDCat 2)`. In Lean / mathlib notation,
  `𝟙` (U+1D7D9) is `CategoryStruct.id` (object-level
  identity), and `𝟭` (U+1D7ED) is `Functor.id`
  (functor-level identity). The actual Lean source uses
  `𝟭` correctly throughout; the spec would not compile
  with the printed glyph. The umbrella docstring (also)
  uses `𝟭`. Recommend a spec-text-only fix replacing the
  six spec occurrences of `𝟙` with `𝟭`.

### M (minor) — three commit subjects exceed the ~72-char target

Subjects in question (lengths 75, 79, 82, 83) all begin
with `docs(equivalence): apply T5 plan round-N fixes …`
or `docs(equivalence): record T5 spec round-3 review …`;
see `jj log -r 'main@origin..feat/t5-equivalence'` for
the full list.

The mathlib commit guide says "aim for the subject under
~72 characters"; this is a soft target. All other
attributes (lowercase, imperative, no trailing period,
documented type/scope) are clean. Recommend leaving as-is
if rewriting history is undesirable, otherwise tighten in
a `jj describe` pass before push.

### M (minor) — non-standard footer types in T2 ancestry

- Not a T5 issue per se: the docs-commits in T5 use
  documented types only. The `feat(equivalence)` and
  `feat(ertok)` scopes are consistent with the existing
  `feat(ertok)` ancestry. No action required for T5.

### M (minor) — `lake test` produces no output on success

- `GebLeanTests` runs without printed output; the only
  signal is exit code 0. This is a project-wide property,
  not a T5 issue. Worth noting in the PR description that
  test-pass is confirmed by exit code rather than visible
  output.

### N (nit) — `change` tactic appears five times across two proofs in `Equivalence.lean`

- `Equivalence.lean:106` and `Equivalence.lean:140`. The
  `change` is required because `Functor.map_injective`
  unfolds compositional `Functor.map` differently from
  `(_ ⋙ _).map`; the goal would not match the rewrite
  source without it. Idiomatic per the mirror file's style
  (`LawvereKSimER.lean` uses the same construction). No
  action.

### N (nit) — `kToErErToKIso` name camelcase

- The mixed casing `kToErErToKIso` (rather than
  `kToErErToKIso` → `kToERErToKIso` to mirror the
  `kToERFunctor` casing) is a deliberate readability
  trade-off per spec §4.4: the four-letter run `EREr` is
  hard to read, so the convention adopts `Er` after the
  arrow for one side. Documented in the spec and
  consistent with `erToKKToErIso`. No action.

## Cross-file consistency

The three touched Lean files (`ErToKFunctor.lean`,
`Equivalence.lean`, `LawvereERKSim.lean`) use a uniform
terminology vocabulary: "categorical equivalence",
"round-trip", "interp preservation", "strict functor
equality", "mirror at `LawvereKSimER.lean:NNN`". Module
docstrings of `ErToKFunctor.lean` and `Equivalence.lean`
each carry the required sections in canonical order
(`# Title`, summary, `## Main definitions`,
`## Main statements`, `## Implementation notes` (only in
`Equivalence.lean`, where the `mk'` vs `mk` choice and
the explicit-instance choice warrant explanation),
`## References`, `## Tags`). The umbrella docstring
section bullet for `Equivalence` enumerates the
declarations in the order they appear in the file. Mirror
line citations (`LawvereKSimER.lean:488–520` for
`erToKFunctor_map_interp`, `LawvereKSimER.lean:538–547`
for `erToKFunctor_comp_kInterpFunctor`) verified accurate.
All 17 new declarations across the two touched files
carry `AXIOM_ALLOW: Classical.choice` comments with
specific transitive-dependency rationale.

## Bottom-up discipline

Preserved. T5 does not introduce any new constructor in
either `LawvereERCat` or `LawvereKSimDCat 2`; it
exclusively assembles the equivalence value
(`erKSimEquiv`) and its two natural-iso witnesses from
pre-existing named declarations: `erToKFunctor` (from
T4), `kToERFunctor` (pre-T5), `erInterpFunctor` /
`kInterpFunctor` (pre-T5), plus the two new strict
functor equalities `erToKFunctor_comp_kToERFunctor` /
`kToERFunctor_comp_erToKFunctor`. The two `eqToIso`
isomorphisms are one-liners over the strict equalities.
The `Equivalence.mk'` invocation is a five-argument
record assembly. The two `IsEquivalence` instances are
one-line projections of mathlib globals against
`erKSimEquiv`. No piece-by-piece construction is added;
the file is composition all the way down.

## Pre-PR notes

- The pre-existing `lake lint` warning at
  `KSimURMSimulator.lean:201` is unrelated to T5. Mention
  in the PR description (or open a separate tracking
  issue) so an upstream reviewer does not attribute it
  to this PR.
- The spec / code glyph mismatch (`𝟙` vs `𝟭`) is a
  documentation-only fix that does not affect Lean
  elaboration. If the spec is to remain canonical
  reference material after merge, recommend a follow-up
  `docs(equivalence)` commit to repair it before opening
  the PR.
- The user line-by-line review of all five `feat` commits
  is required before `jj git push --remote origin -b
  feat/t5-equivalence` per `CLAUDE.md` § Hard rules; the
  `gh pr create --base main --head feat/t5-equivalence`
  invocation that follows is also user-gated.
- The PR title and body must be user-authored (no
  LLM-drafted text in user-facing channels per
  `CLAUDE.md` § Hard rules).
