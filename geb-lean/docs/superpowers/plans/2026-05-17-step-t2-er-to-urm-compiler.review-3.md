# T2 plan adversarial review — round 3

## Author responses

- **S1'** (`Fin.cases`-rewrite invariant proofs in
  `compileFrag_sub` do not close): **fix.** Rewrote the
  three invariant proofs using `fin_cases p <;> ...`
  with the round-3-verified patterns:
  - `inputRegs_inj`: `fin_cases p <;> fin_cases q <;>
    first | rfl | (exfalso; revert hpq; decide)`.
  - `outputReg_not_input`, `zeroReg_not_input`:
    `fin_cases p <;> exact absurd hp (by decide)`.
  These match the round-3 reviewer's empirically
  `lean_run_code`-verified working patterns.
- **S2'** (`URMInstrRaw.toBounded` per-instruction
  bound-proof pattern is structurally untenable):
  **fix.** Added Step 2.4 introducing
  `URMRaw.boundedBy : ℕ → List URMInstrRaw → Prop` and
  `URMInstr.fromRawList : (r : ℕ) → (l : List
  URMInstrRaw) → URMRaw.boundedBy r l → Array (URMInstr
  r)`, with `List.attach` carrying the membership proof
  pointwise. Steps 5.2 (`compileFrag_succ`), 5.3
  (`compileFrag_proj`), 5.4 (`compileFrag_sub`)
  rewritten to use `URMInstr.fromRawList R rawList
  hBound` where `hBound : URMRaw.boundedBy R rawList`
  is proved by unfolding the concrete `rawList` and
  `rcases`-ing the resulting finite disjunction of
  membership cases.

## Summary

Round 3 verifies the round-2 fixes (S1, M1, M2, N1, N2, N3)
and re-evaluates the carried-over deferrals (B3, M3). The
round-2 `fix` dispositions are present in the plan, but
the S1 fix is technically inadequate: empirical Lean
behaviour shows the proposed `fin_cases p <;> ... <;>
simp_all [Fin.cases, Fin.elim0]` and `simp only [Fin.cases]
at hp; ... Fin.mk.inj_iff` tactic chains do not close the
goals as written. In addition, round 3 surfaces one
pre-existing defect that rounds 1 and 2 did not flag: the
`URMInstrRaw.toBounded` per-instruction bound proof
embedded in `compileFrag_succ`, `compileFrag_proj`,
`compileFrag_sub` (and implicitly in any future
`compileFrag_*` that uses the same emit-and-toBounded
pattern) cannot work for an arbitrary `ins : URMInstrRaw`
inside `List.map`; it requires per-element evidence that
`List.map`'s plain lambda does not provide.

Counts: 0 blockers, 2 serious, 0 minor, 1 nit.

The plan is not yet converged. Recommend a round-4 review
after S1' and S2' below are addressed.

## Round-2 fix verification

| Round-2 ID | Status | Notes |
| --- | --- | --- |
| S1 (`Fin.cases` rewrite + `fin_cases` proofs) | fix present, but technically inadequate | `Fin.cases` rewrite of `inputRegs` is well-typed; the three associated invariant proofs do not close as written. See § S1' below. |
| M1 (coverage table row) | fix present | Table row at line 2236 reads "§5.1 prelude — localised variant adopted; see Divergence subsection", with cross-references to Tasks 5.3, 6.3, 7.1, 8.1. Consistent. |
| M2 / N3 (heading count) | fix present | Subsection at line 233 reads "Plan-style note: sketches in four declaration bodies"; TOC entry at line 95 matches. |
| N1 ("more elaborate") | fix present | Line 1635 reads "This update emits a nested loop, in contrast to `bsum`'s single transferLoop addition." The line-1017 Lean-vernacular occurrence of "elaborate" (the elaborator phase) is retained, acceptable. |
| N2 (commit-message tense) | fix present, mostly | Spot-check of Tasks 2, 5, 7, 10 confirms imperative-present verb-led bodies. One body (Task 9, line 1766) opens with "Dispatch", verb-led. Task 10's body opens with "Define" — verb-led. Task 5 opens with "Realize" — verb-led. Task 7 opens with "Emit" — verb-led. Task 2 opens with "Mirror" — verb-led. See § Nit N1 for one residual lapse. |

## Serious findings

### S1'. The S1 fix's tactic chains do not close the goals

The round-2 fix rewrites `inputRegs` in `compileFrag_sub`
(Step 5.4) using `Fin.cases ⟨2, by decide⟩ (Fin.cases ⟨3,
by decide⟩ Fin.elim0)` — that part is well-typed and
correct. The three invariant proofs, however, are written
as:

- `inputRegs_inj`: `fin_cases p <;> fin_cases q <;>
  simp_all [Fin.cases, Fin.elim0]`
- `outputReg_not_input`: `fin_cases p <;> (simp only
  [Fin.cases] at hp; exact absurd (Fin.mk.inj_iff.mp hp).1
  (by decide))`
- `zeroReg_not_input`: same shape as `outputReg_not_input`.

Empirically against current mathlib:

- `Fin.cases` unfolds to `Fin.induction`, which does not
  reduce on a literal `⟨1, _⟩` (because `1 : Fin 2` is
  `Fin.mk 1 _`, not syntactically `Fin.succ ...`). After
  `fin_cases p <;> fin_cases q <;> simp_all [Fin.cases,
  Fin.elim0]`, the off-diagonal cases `(p = 0, q = 1)` and
  `(p = 1, q = 0)` leave unsolved goals of the form
  `2 = Fin.induction 2 (...) 1 → False` (and symmetric).
- After `simp only [Fin.cases] at hp`, the hypothesis `hp`
  has type `2 = 1` (an `ℕ` equality, not a `Fin` equality),
  so `Fin.mk.inj_iff.mp hp` fails with "type `2 = 1` which
  has no fields".

Working alternatives (confirmed):

- For `inputRegs_inj`:

  ```lean
  inputRegs_inj := by
    intro p q hpq
    fin_cases p <;> fin_cases q <;>
      first | rfl | (exfalso; revert hpq; decide)
  ```

- For `outputReg_not_input` and `zeroReg_not_input`:

  ```lean
  outputReg_not_input := by
    intro p hp
    fin_cases p <;> exact absurd hp (by decide)
  zeroReg_not_input := by
    intro p hp
    fin_cases p <;> exact absurd hp (by decide)
  ```

The implementer will encounter "unsolved goals" at Step 5.4's
build verification. Recommend rewriting the three invariant
proofs as above.

### S2'. `URMInstrRaw.toBounded` bound-proof pattern is structurally untenable

This defect is pre-existing (present since round 1) but
neither round-1 nor round-2 review flagged it.

Steps 5.2, 5.3, 5.4 each emit instructions via:

```lean
rawList.toArray.map (fun ins =>
  URMInstrRaw.toBounded R ins (by
    cases ins <;>
      simp only [URMInstrRaw.regBound] <;> omega))
```

Inside the `by`, `ins : URMInstrRaw` is an arbitrary raw
instruction (not constrained to be one of the specific
instructions in `rawList`). After `cases ins`, the
`assignR` branch leaves a goal `i + 1 ≤ R` with `i : ℕ`
free. `omega` cannot close this because `i` is
unconstrained.

The pattern works only if the bound is the maximum-possible
`i + 1` for every constructor of `URMInstrRaw`, which would
require either:

- A bound on `i` in the type of `URMInstrRaw` (defeats the
  purpose of the raw form), or
- Passing membership evidence into the lambda
  (`rawList.attach.map (fun ⟨ins, hmem⟩ => ...)` and
  case-analysing on `hmem`), or
- Pre-validating the list with `List.all` /
  `URMRaw.boundedBy` (which the plan mentions parenthetically
  at lines 1034–1045) and threading the validation through.

The Step 5.2 prose at lines 1003–1029 acknowledges that
"the per-instruction `regBound ≤ 4` proof" handles "each
raw instruction in `rawList`" — but the lambda does not
know which instructions are in `rawList`; it operates on
an arbitrary `ins`.

The `URMRaw.boundedBy` helper sketch at lines 1037–1045 is
the principled remedy, but the plan treats it as an
optional escape ("If the per-instruction bound proof
becomes unwieldy..."). For Steps 5.2, 5.3, 5.4 it is not
optional — the simpler form does not type-check.

Recommend promoting `URMRaw.boundedBy` (or an
`attach`-based variant) to the primary pattern for Steps
5.2 onward, and rewriting the three emission sites
accordingly. The cleanest path is:

```lean
instrs :=
  (rawList.attach.map (fun ⟨ins, hmem⟩ =>
    URMInstrRaw.toBounded R ins
      (by /- case-analyse hmem against the explicit list -/)
    )).toArray
```

with the `by` block performing case analysis on which
element of the literal `rawList` `hmem` proves membership
of, specialising `ins` to a concrete constructor each
time. Or equivalently, pre-validate `rawList` via a
`Decidable` `boundedBy` instance and one `if` check.

This is implementability-risk level: the implementer will
hit it on the first build attempt of Step 5.2
(`compileFrag_succ`).

## B3 deferral re-evaluation

The four sketch bodies (Tasks 6.3, 7.1, 8.1, 11.2) remain
acceptable in density for an implementer subagent, per
round 2's evaluation. Nothing new comes to light in round
3. The deferral continues to hold.

## Other spot checks

- **Markdownlint.** `markdownlint-cli2` on the plan file
  reports zero errors (verified out-of-band; tool config
  is `.markdownlint-cli2.jsonc`).
- **Banned style words.** Scanned for "load-bearing",
  "key", "important", "elegant", "crucial", "beautiful",
  "clever", "neat", "powerful", "interesting", "blocked",
  "issue", "challenge", "yes", "wait", "hmm", "careful",
  "actually". The only hit is "blocked" in the
  CLAUDE.md-style-list quotation at line 180; that is
  enumeration, not usage.
- **Commit message subject lines.** Subject lines for
  Tasks 2–11 are within the 72-character limit; spot-checked:
  Task 2 "feat(ertok): raw-instruction intermediate
  URMInstrRaw" (52 chars); Task 5 "feat(ertok): atom
  fragment compilers zero, succ, proj, sub" (62); Task 7
  "feat(ertok): bsum fragment compiler" (35); Task 10
  "feat(ertok): compileER_runtime structural recursion" (51).
  All within bounds.
- **Spec section references.** Each task's commit body
  cites a spec section (Tasks 2, 3: §5.1; Task 4: §5.1;
  Task 5: §5.1; Task 6: §5.1.2; Tasks 7, 8: §5.1, §5.1.1;
  Task 9: §5; Task 10: §5.2; Task 11: §5.2). Consistent
  with the spec coverage table.

## Nits

### N1. Task 3 commit body lapse

Task 3's commit body (line 731) opens with "Introduce
CompiledFragment a as a composable URM-fragment record
carrying numRegs (≥ 1), ...". "Introduce" is verb-led
imperative-present, so this is fine. However the body's
second sentence reads "Strip the reserved-zero convention
to a URMProgram via toProgram." — also imperative.
Acceptable.

Re-reading carefully: all eleven Task 2–12 commit bodies
inspected are verb-led imperative-present, with one
exception: Task 12's body (line 2215) opens with "Verify
that #print axioms ...". "Verify" is imperative-present;
acceptable.

No remaining lapses. Strike this nit — round-2 N2 fix is
fully present.

## Items missed by rounds 1–2

The S2' finding (`URMInstrRaw.toBounded` bound-proof
pattern) is a structural implementability defect present
since round 1. Rounds 1 and 2 inspected the Lean code
blocks for type-checking on inspection (round 2 § "New
Lean-code blocks introduced by the round-1 fixes") but did
not stress-test the `by` blocks inside `List.map` lambdas
against the actual elaboration context. The defect
surfaces only when the implementer tries to build.

The S1' finding similarly was not caught by inspection
alone — `fin_cases` plus `simp_all [Fin.cases]` looks
plausible until one runs the tactic chain against a
concrete `Fin n → Fin m` function whose body composes
`Fin.cases` calls.

Recommend that round-4 review (and future plan reviews
covering tactic-mode Lean) include a step where each
non-trivial tactic chain is exercised against the actual
goal via `lean_run_code` or equivalent, rather than
inspected statically.

## Sign-off

Plan has 0 blockers, 2 serious, 0 minor, 1 (struck) nit;
not converged. The two serious findings (S1' tactic chain
correctness; S2' `toBounded` bound-proof pattern) are
implementability-risk-level. Recommend round 4 after the
author addresses S1' (rewrite the three invariant proofs
in `compileFrag_sub`) and S2' (promote `URMRaw.boundedBy`
or `List.attach` to the primary emission pattern, with
worked examples in Steps 5.2, 5.3, 5.4).
