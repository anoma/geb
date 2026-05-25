# Post-T3 handoff — T3 landing summary + T4 brainstorming

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Where we are](#where-we-are)
- [Step A — T4 brainstorming and spec (runtime bound)](#step-a--t4-brainstorming-and-spec-runtime-bound)
  - [Inputs (binding for T4 brainstorming)](#inputs-binding-for-t4-brainstorming)
- [T3 actually-landed surface](#t3-actually-landed-surface)
- [Policy decisions to remember](#policy-decisions-to-remember)
- [T3 axiom hygiene](#t3-axiom-hygiene)
- [Known T3 follow-ups (low priority; not blocking T4)](#known-t3-follow-ups-low-priority-not-blocking-t4)
- [Brainstorming and spec workflow](#brainstorming-and-spec-workflow)
- [Operational rules (carry forward from T3)](#operational-rules-carry-forward-from-t3)
- [Resumption prompt](#resumption-prompt)
- [References](#references)

<!-- END doctoc -->

Handoff for the next workstream after T3's completion. T3
(K^sim simulator) merged to `main@origin` via PR #22 on
2026-05-22 (merge commit `db059ef4`). The simulator landed as
`simulate : URMProgram a → KMor1 (a + 1)` together with
`simulate_interp` and `simulate_level ≤ 2`, in
`GebLean/Utilities/KSimURMSimulator.lean` (re-exported via
`GebLean.lean`). T4 (the runtime-bound workstream) is now the
critical-path piece for the `erToK` direction.

## Where we are

The ER ↔ K^sim_2 categorical equivalence project decomposes
into a forward direction (`kToER`, complete) and a reverse
direction (`erToK`, T1+T2+T3 complete, T4+T5 remaining), plus
a final categorical-iso packaging. Status at 2026-05-22:

| Workstream | Description | Status |
| --- | --- | --- |
| kToER (Steps 0–5) | Structural-induction proof of `K^sim_2 ⊆ ER` plus `kToERFunctor` | Complete |
| T1 (≈ Step 7) | URM kernel `GebLean/Utilities/ZeroTestURM.lean` | Complete |
| T2 (≈ Steps 6+8) | ER → URM compiler + `compileER_runFor` in `GebLean/LawvereERKSim/` | Complete |
| Followup #654 | Deferred cleanups (naming, refactor, private re-evaluation) | Partial (sub-tasks A–F, M, N complete; G–L pending) |
| T3 (≈ Step 9) | K^sim simulator for URM kernel (`simulate` + `simulate_interp` + `simulate_level`) | Complete (PR #22, merge commit `db059ef4`) |
| T4 (≈ Step 10) | Runtime bound + `erToK` assembly + `erToKFunctor` | Pending |
| T5 (≈ Step 11) | Strict iso `LawvereERCat ≌ LawvereKSimDCat 2` | Pending |

Binding documents for the landed work:

- Master research design:
  `docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
- Master ER-to-K spec (T1 + T2 + T3):
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.
- T2 plan:
  `docs/superpowers/plans/2026-05-17-step-t2-er-to-urm-compiler.md`.
- T3 spec (4-round adversarial-converged):
  `docs/superpowers/specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md`.
- T3 plan (9-round adversarial-converged):
  `docs/superpowers/plans/2026-05-21-step-t3-urm-to-ksim-simulator-plan.md`.
- Post-T2 handoff (also followup catalogue):
  `docs/superpowers/plans/2026-05-20-post-t2-handoff.md`.

## Step A — T4 brainstorming and spec (runtime bound)

**Sub-skill**: `superpowers:brainstorming` first (per the
project rule "Always-on for any creative work"), then
`superpowers:writing-plans` once a spec converges.

**Goal**: design the runtime-bound infrastructure that
allows `erToK` to be assembled from T2's `compileER_runFor`
and T3's `simulate`. The composition
`(simulate (compileER e)) ≫ projection` already simulates `e`
post-stop given a sufficiently large step count; the runtime
bound `boundExprK e` must be realised as a K^sim term of
level ≤ 2 whose value dominates the URM runtime of
`compileER e` on every input. Combined with T2's
`compileER_runFor` and T3's `simulate_interp`, this yields the
`erToK : ERMor1 a → KMor1 (a + 1)` of level ≤ 2 with
`(erToK e).interp v = e.interp v`.

### Inputs (binding for T4 brainstorming)

- T3 spec at
  `docs/superpowers/specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md`
  (4-round adversarial-converged) — for the simulator's
  actually-landed shape.
- T3 plan at
  `docs/superpowers/plans/2026-05-21-step-t3-urm-to-ksim-simulator-plan.md`
  (9-round adversarial-converged) — for the patterns surfaced
  during execution.
- T3 landing surface (see "T3 actually-landed surface" below).
- The two policy decisions surfaced by T3 (constructive
  `KMor1.level` refactor; `Fin.lastCases_castSucc` AXIOM_ALLOW)
  — both already documented in `.claude/rules/lean-coding.md`
  § Accepted exceptions.
- Master ER-to-K design's §7 forward-looking content (the
  `boundExprK` runtime-bound function):
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.
- Master research design's relevant T4 framing:
  `docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`
  § "Step 10 — `erToK` and `erToKFunctor`".
- Tourlakis §0.1.0.42 (existence of ER-level runtime bound),
  §0.1.0.43 (Ritchie–Cobham), §0.1.0.44 proof (URM simulation
  chain). Citations: `PR-complexity-topics.pdf` pp. 15–22.
- Existing K^sim composites under
  `GebLean/Utilities/KArith.lean` and the K^sim level
  hierarchy in `GebLean/LawvereKSim*.lean`. In particular,
  the kToER side's `KMor1.majorize_by_A_n_iter` is the
  reusable majorization-via-Ackermann-iterate result.

## T3 actually-landed surface

For T4 to consume.

**File**: `GebLean/Utilities/KSimURMSimulator.lean`
(re-exported via `GebLean.lean`).

**Supporting declarations in `GebLean/Utilities/KArith.lean`**:

- `KMor1.natK` — constant K^sim morphism returning a `Nat`
  literal.
- `KMor1.natK'` — variant returning a `Nat` literal under any
  arity, via composition.
- `KMor1.interp_natK` — `(KMor1.natK n).interp v = n`.
- `KMor1.interp_natK'` — analogous reduction for `natK'`.
- `KMor1.natK_level` — level bound for `natK`.
- `KMor1.natK'_level` — level bound for `natK'`.

**Public declarations in `KSimURMSimulator.lean`**:

- `KMor1.predIter` — K^sim `n`-fold predecessor combinator.
- `KMor1.interp_predIter` — reduction lemma.
- `KMor1.predIter_level` — level bound.
- `KMor1.pcDispatch` — n-way PC dispatch combinator on a
  vector of branch morphisms.
- `KMor1.interp_pcDispatch_match` — matched-branch reduction.
- `KMor1.interp_pcDispatch_default` — default-branch reduction.
- `KMor1.pcDispatch_level` — level bound.
- `baseFamily` — the `simrec` base-case state-update family.
- `baseFamily_level` — level bound.
- `stepFamily` — the `simrec` step-case state-update family.
- `stepFamily_level` — level bound.
- `simulate` — top-level simulator assembly.
- `simulate_interp` — correctness theorem.
- `simulate_level` — level-≤ 2 bound.

**Key signature for T4 consumption**:

- `simulate : URMProgram a → KMor1 (a + 1)`
- `simulate_interp : (simulate P).interp (Fin.cons y v) =
  ((URMState.init P v).runFor P y).regs P.outputReg`
- `simulate_level (P) : (simulate P).level ≤ 2`

The `+ 1` in the arity holds the step-count input `y`; T4's
`boundExprK e` must compute (a value at least as large as)
the URM runtime of `compileER e` on `v`, then feed it as `y`.

## Policy decisions to remember

These decisions emerged during T3 execution and were not
anticipated in the 9-round-converged plan. They bind T4 going
forward.

1. **`KMor1.level` is now constructive.** Mathlib's
   `Finset.univ.sup` transitively pulls `Classical.choice`
   through unbundled-order machinery. T3's prerequisite
   refactor (commit `719af741`) replaced it with a
   constructive `Fin.maxOfNat` helper (`Fin.foldr` plus
   `Nat.max`), axiom-clean. The helper lives in
   `GebLean/LawvereKSim.lean`; supporting lemmas are
   `Fin.maxOfNat`, `Fin.le_maxOfNat`, `Fin.maxOfNat_le`. Any
   future level-related work should use `Fin.maxOfNat_le` /
   `Fin.le_maxOfNat` rather than mathlib's `Finset.sup_le` /
   `Finset.le_sup`. The refactor's blast radius touched
   `LawvereKSim.lean`, `LawvereKSimQuot.lean`,
   `LawvereKSimER.lean`, `LawvereKSimERDirect.lean`,
   `LawvereKSimMajorization.lean`,
   `LawvereKSimPolynomialBound.lean`, and
   `GebLeanTests/LawvereKSimER.lean`.
2. **`Fin.lastCases_castSucc` is AXIOM_ALLOW'd.** Mathlib's
   reduction lemmas for `Fin.lastCases` pull
   `Classical.choice` through `Fin.reverseInduction.go`. The
   project already used these lemmas in `LawvereBTInterp.lean`,
   `LawvereBTEq.lean`, `Tupling.lean`, and `ERTupling.lean`
   (implicit dependency). T3 Task 4's blocker forced the
   explicit user-approval choice; the AXIOM_ALLOW policy is
   documented in `.claude/rules/lean-coding.md` § Accepted
   exceptions. Five T3 theorems carry the annotation:
   `baseFamily_level`, `stepFamily_level`,
   `simulate_step_match` (private), `simulate_interp`,
   `simulate_level`. Any T4 theorem that proves things via
   `simp only [Fin.lastCases_castSucc]` will need the same
   annotation.

## T3 axiom hygiene

Of the 19 T3 public declarations, 14 are
`[propext, Quot.sound]`-only (or no axioms); 5 are
`[propext, Classical.choice, Quot.sound]` (the AXIOM_ALLOW'd
theorems listed above).

## Known T3 follow-ups (low priority; not blocking T4)

1. **`step_ctx_eval_simrec` lambda-form lemma statement.**
   The current statement does not fire post-`simp` (the
   surrounding `simp` beta-reduces the lambda); restating it
   in `dif`-form would let it fire. Each call site currently
   inlines the helper's `dif_neg` body manually.
2. **`KMor1.interp_natK'` simp-noop under dite-form ctx.**
   `simp only [KMor1.interp_natK']` does not fire when the
   `ctx` argument is a dite-form lambda (Lean 4.29-rc6
   quirk). Workaround in place at the call sites:
   `simp only [KMor1.natK', KMor1.interp_comp, KMor1.interp_natK]`.

## Brainstorming and spec workflow

1. Brainstorm using `superpowers:brainstorming`, focusing on
   how to realise the URM runtime of `compileER e` as a K^sim
   term of level ≤ 2 that majorises the actual runtime on
   every input. Produce a spec draft.
2. Self-review (inline).
3. Adversarial-review loop (≥ 3 rounds, fresh-context Agent
   subagents). Aim for zero blocker, zero serious.
4. Hand off to user review.
5. Once approved, write the T4 implementation plan
   (`superpowers:writing-plans`). Adversarial-review the plan
   ≥ 3 rounds.
6. Hand the plan off to the user. Execute via SDD.

## Operational rules (carry forward from T3)

- No `jj git push` without user line-by-line review.
- No raw mutating `git` subcommands.
- No `noncomputable`, no `admit`, minimal `Classical`.
- One concern per branch.
- Markdownlint cleanliness on any `.md` touched.
- `lake build` only (never `lake env lean`, never
  `lake clean`).
- One declaration at a time during implementation; per-
  declaration axiom audit before commit.
- AXIOM_ALLOW for `Fin.lastCases_castSucc` as appropriate,
  per `.claude/rules/lean-coding.md` § Accepted exceptions.
- Conventional commits in imperative present
  (`feat(ertok):`, `fix(ertok):`, `chore(ertok):`,
  `refactor(ertok):`, etc.); lowercase first letter; no
  trailing period; generic user references.
- Cite literature for every transcribed lemma; cite internal
  reuse points.

## Resumption prompt

To pick up T4:

```text
Read docs/superpowers/plans/2026-05-22-post-t3-handoff.md and
proceed to Step A (T4 brainstorming) per the workflow above.
Treat the T3 actually-landed surface and the two policy
decisions (constructive KMor1.level, Fin.lastCases_castSucc
AXIOM_ALLOW) as binding inputs to brainstorming.
```

The brainstorming subagent should start by reading the T3
spec and plan to internalise the simulator's shape, then the
master ER-to-K design's §7 prose, then the K^sim composites
under `GebLean/Utilities/KArith.lean` and the kToER side's
`KMor1.majorize_by_A_n_iter` infrastructure.

## References

- T3 spec:
  `docs/superpowers/specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md`.
- T3 plan:
  `docs/superpowers/plans/2026-05-21-step-t3-urm-to-ksim-simulator-plan.md`.
- Master research design:
  `docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
- Master ER-to-K design:
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.
- Post-T2 handoff (pattern precedent):
  `docs/superpowers/plans/2026-05-20-post-t2-handoff.md`.
- Project rules: `CLAUDE.md`, `.claude/rules/lean-coding.md`,
  `.claude/rules/markdown-writing.md`,
  `.claude/rules/fork-upstream-flow.md`.
- Tourlakis 2018 `PR-complexity-topics.pdf` §0.1.0.37
  (URM simulation), §0.1.0.42 (ER runtime bound),
  §0.1.0.43 (Ritchie–Cobham), §0.1.0.44 (`K^sim_n = E^{n+1}`
  proof).
