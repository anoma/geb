# T4 Tasks 5–8 handoff — `boundExprKParams_dominates` continuation

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Where we are](#where-we-are)
- [Branch and commit state](#branch-and-commit-state)
- [Working-copy state (do NOT commit)](#working-copy-state-do-not-commit)
- [Spec/plan amendment history](#specplan-amendment-history)
- [The amended recipe (binding)](#the-amended-recipe-binding)
- [Available infrastructure (in working copy)](#available-infrastructure-in-working-copy)
- [Per-case chain specifications (binding from spec §4.2)](#per-case-chain-specifications-binding-from-spec-42)
  - [`comp` case (Task 6)](#comp-case-task-6)
  - [`bsum` case (Task 7)](#bsum-case-task-7)
  - [`bprod` case (Task 8)](#bprod-case-task-8)
- [Key invariant for bsum/bprod (`mu_f` is at least 2)](#key-invariant-for-bsumbprod-mu_f-is-at-least-2)
- [Build constraint](#build-constraint)
- [Subagent-driven-development plan](#subagent-driven-development-plan)
- [Operational rules (carry forward)](#operational-rules-carry-forward)
- [Resumption prompt](#resumption-prompt)
- [References](#references)

<!-- END doctoc -->

Handoff for the dedicated follow-up session that completes
T4 SDD Tasks 5–8 (the `boundExprKParams_dominates` joint
inductive theorem). Tasks 1–4 are committed to
`feat/ertok-runtime-bound`; Task 5 atom cases and helper
infrastructure live in the working copy as uncommitted state
(`-DwarningAsError=true` rejects `sorry`, so the partial work
cannot be committed until the proof is complete). The session
that produced this handoff converged the spec/plan via five
rounds of adversarial review and discovered that the
"compileER\_numRegs ≤ offset" helper (option 3) does not
materially shorten the chains; the proof work is intrinsic.

## Where we are

T4 decomposes into 15 SDD tasks (plus a final holistic review).
The recipe `boundExprKParams` and the four atom cases of
`boundExprKParams_dominates` are working; the three remaining
cases (`comp`, `bsum`, `bprod`) constitute the bulk of the
proof effort. The downstream tasks (9–15) depend on Tasks 5–8
having a working `boundExprKParams_dominates` to consume.

| Task | Description | Status |
| --- | --- | --- |
| 0 | Baseline verification | Complete |
| 1 | `KMor1.maxK` in `KArith.lean` | Complete (commit `90f03b1`) |
| 2 | `KMor1.maxOver` in `KArith.lean` | Complete (commit `17dcc48`) |
| 3 | `KMor1.pow2_iter` in `KArith.lean` | Complete (commit `e8c0028` prereq) |
| 4 | `RuntimeBound.lean` scaffold + `boundExprKParams` | Complete (commit `e8c0028`) |
| 5–8 | `boundExprKParams_dominates` (joint commit) | In progress — atoms done, `comp`/`bsum`/`bprod` remaining |
| 9 | `boundExprK` + level + interp + dominates | Pending |
| 10 | `ErToK.lean` + `erToK` + level + interp | Pending |
| 11 | `ErToKFunctor.lean` + `erToKN` | Pending |
| 12 | `erToKFunctor_map` via `Quotient.liftOn` | Pending |
| 13 | `erToKFunctor_map_id` and `_map_comp` | Pending |
| 14 | `erToKFunctor` assembly | Pending |
| 15 | Re-export, axiom audit, lint, tests | Pending |
| Final | Holistic code review | Pending |

## Branch and commit state

- Branch: `feat/ertok-runtime-bound` (child of `main`).
- Bookmark at `puynnrsk e8c00280` (Task 4).
- Working copy: change `uzymllsp a6ce5f9b` — WIP atoms + spec/plan
  amendments + helper infrastructure + 3 `sorry`s.
- The working copy is uncommittable because of the `sorry`s and
  the project's `-DwarningAsError=true` setting.

## Working-copy state (do NOT commit)

Modified files (relative to commit `e8c00280`):

- `GebLean/LawvereERKSim/RuntimeBound.lean`:
  - Recipe def `boundExprKParams` updated to the post-convergence
    form (see [The amended recipe](#the-amended-recipe-binding)).
  - Atom cases (`zero`, `succ`, `proj`, `sub`) of
    `boundExprKParams_dominates` proved.
  - Helper infrastructure added (see
    [Available infrastructure](#available-infrastructure-in-working-copy)).
  - `comp`, `bsum`, `bprod` cases of
    `boundExprKParams_dominates` remain as `sorry`.
  - Imports added: `Mathlib.Tactic.Ring`, `Mathlib.Tactic.Linarith`.
- `docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`:
  - §4.2 recipe table and rationale amended (offsets include
    `k`, `compileER_numRegs f`; `mu` for bsum is `mu_f + 6`,
    bprod is `mu_f + 9`).
  - §4.2 Tourlakis-faithfulness paragraph rewritten to clarify
    that `mu_e` values are derivable from the chain, not
    literature-pinned.
  - §4.3 chain summary bullets updated.
- `docs/superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md`:
  - Recipe def synced with spec.
  - Step 4 commit-message scaffold updated.
  - Step 5/6 of comp, bsum, bprod sections updated.

The session ran `markdownlint-cli2` on both `.md` files; no
errors.

## Spec/plan amendment history

The spec/plan as of commit `e8c00280` (Task 4) had a recipe
that was too tight in three places. The five-round adversarial
review converged on the following amendments:

1. **`comp` offset adds `+ k`**: the outer `k`-fold sum
   `Σ_{i∈Fin k} (...)` in `compileER_runtime` was unbounded
   without `k ≤ m`; adding `+ k` to the offset makes
   `k ≤ m` available by `omega` from the recipe.
2. **`bsum` offset adds `+ k + compileER_numRegs f`**: per-iter
   contains `2·(k+1)`, `10·outerSum` (where `outerSum ≤ k·m`),
   and `nRegs_f`; adding both `k` and `nRegs_f` makes those
   absorbable.
3. **`bsum` `mu` bumped from `+2` to `+6`**: the original spec
   ignored the per-iter URM-side overhead (`50 + 2(k+1) +
   10·outerSum + nRegs_f`); the corrected chain has four
   absorption steps totalling `+6`.
4. **`bprod` offset adds `+ k + compileER_numRegs f`**: same
   reason as bsum.
5. **`bprod` `mu` bumped from `+7` to `+9`**: per-iter has
   additional `9·A_i·B_i + 4·A_i + 9·B_i + nRegs_f` terms; the
   corrected chain has a six-part partition where parts 5–6
   land at `tower (mu_f + 7) m` and the final mul step lifts
   to `tower (mu_f + 9) m`.

Each amendment is justified in spec §4.2 with an explicit
per-case rationale. The amendments are within Tourlakis's
"for some `r ∈ ℕ`" framing — `r` is allowed to depend on the
ER expression's structural data (arity `a`, inner arity `k`,
register count `compileER_numRegs f`), so adding these terms to
`offset_e` is a numeric refinement, not an asymptotic
divergence.

## The amended recipe (binding)

```lean
def boundExprKParams : {a : ℕ} → ERMor1 a → ℕ × ℕ
  | _, .zero    => (0, 3)
  | _, .succ    => (2, 16)
  | _, .proj _  => (2, 16)
  | _, .sub     => (2, 24)
  | a, .comp (k := k) f gs =>
      let p_f  := boundExprKParams f
      let mu_g := Fin.maxOfNat k
                    (fun i => (boundExprKParams (gs i)).1)
      let o_g  := Fin.maxOfNat k
                    (fun i => (boundExprKParams (gs i)).2)
      (p_f.1 + mu_g + 6, p_f.2 + o_g + 4 * a + k + 8)
  | _, .bsum (k := k) f  =>
      let p_f := boundExprKParams f
      (p_f.1 + 6, p_f.2 + k + LawvereERKSim.compileER_numRegs f + 32)
  | _, .bprod (k := k) f =>
      let p_f := boundExprKParams f
      (p_f.1 + 9, p_f.2 + k + LawvereERKSim.compileER_numRegs f + 44)
```

This is what's currently in
`GebLean/LawvereERKSim/RuntimeBound.lean`. Do not change it
without escalating.

## Available infrastructure (in working copy)

The session-1 atom proofs and the subagent's contribution
leave the following helpers in
`GebLean/LawvereERKSim/RuntimeBound.lean`:

- `cm_le_tower_two : c ≤ m → 2 ≤ m → c * m ≤ tower 2 m` —
  the linear-into-`tower 2` absorption pattern used in every
  atom case; one application of `mul_tower_le_tower_add_two`.
- `foldl_map_le_length_mul_aux`,
  `foldl_map_le_length_mul`: `(l.map g).foldl (· + ·) 0 ≤
  l.length * M` when `∀ x ∈ l, g x ≤ M`.
- `foldl_finRange_le_mul_maxOfNat`: specialised to
  `List.finRange k`, gives `≤ k * Fin.maxOfNat k g`.
- `Fin.maxOfNat_mono`: pointwise monotonicity of
  `Fin.maxOfNat`.
- `natBSum_le_mul_max : ∀ i < b, f i ≤ M → natBSum b f ≤
  b * M` — constructive (no `Classical.choice`).
- `natBProd_le_pow_max : ∀ i < b, f i ≤ M → natBProd b f ≤
  M ^ b` — constructive.
- `two_le_tower : 2 ≤ m → 2 ≤ tower k m`.
- `foldl_add_mono_aux`, `foldl_add_mono`: pointwise
  monotonicity of `(l.map _).foldl (· + ·) 0` —
  `(∀ x ∈ l, f x ≤ g x) → fold f l ≤ fold g l`.

These helpers are intended to be consumed by the
`comp`/`bsum`/`bprod` cases. They encode the recurring
patterns (list-fold bounds, bounded-sum/prod bounds, pointwise
monotonicity) so each case can cite them rather than re-derive
inline.

## Per-case chain specifications (binding from spec §4.2)

### `comp` case (Task 6)

Goal:

```text
compileER_runtime (.comp f gs) v ≤ tower (mu_f + mu_g + 6) m
∧ (.comp f gs).interp v ≤ tower (mu_f + mu_g + 6) m
```

where `m = Fin.maxOfNat _ v + (boundExprKParams (.comp f gs)).2`,
`mu_f = (boundExprKParams f).1`, `mu_g = Fin.maxOfNat k
(fun i => (boundExprKParams (gs i)).1)`.

Chain (spec §4.2 comp rationale):

1. **Inner-offset absorption**: `tower mu_f (tower mu_g m +
   offset_f) ≤ tower mu_f (tower (mu_g + 2) m)` via one
   `mul_tower_le_tower_add_two` on the `m·tower mu_g m`
   factor (using `offset_f ≤ m`).
2. **`tower_comp` equality**:
   `tower mu_f (tower (mu_g + 2) m) = tower (mu_f + mu_g + 2) m`,
   bounding `rt(f at gs_interp)`.
3. **Per-summand glue**: each glue summand
   `(rt(gs i) + 4 + 5·val(gs i) + 9·v_total + 2·a) ≤ tower
   (mu_g + 4) m` for `mu_g ≥ 2`. Components: `rt(gs i) ≤
   tower mu_g m` (IH), `5·val(gs i) ≤ tower (mu_g + 2) m`
   (one mul step from IH value), `9·v_total ≤ m·m ≤ tower
   2 m ≤ tower (mu_g + 4) m` (uses `a ≤ m` from offset),
   plus small constants.
4. **Outer `k`-fold**: `k · tower (mu_g + 4) m ≤ m · tower
   (mu_g + 4) m ≤ tower (mu_g + 6) m` via one
   `mul_tower_le_tower_add_two` (uses `k ≤ m` from
   amended offset).
5. **Combining glue + rt(f) + 2**: both `glue ≤ tower
   (mu_g + 6) m` and `rt(f) ≤ tower (mu_f + mu_g + 2) m`
   satisfy `≤ tower (mu_f + mu_g + 4) m` for `mu_f ≥ 2`.
   Sum-of-three: `3·tower (mu_f + mu_g + 4) m ≤ m·tower
   (mu_f + mu_g + 4) m ≤ tower (mu_f + mu_g + 6) m`.

Edge case `mu_f = 0` ⟹ `f = .zero` ⟹ `k = 0` ⟹
`glue = 0`; total = 3 + 2 = 5; trivially ≤ tower bound.

### `bsum` case (Task 7)

Goal:

```text
compileER_runtime (.bsum f) v ≤ tower (mu_f + 6) m
∧ natBSum (v 0) (fun j => f.interp (Fin.cons j (Fin.tail v)))
    ≤ tower (mu_f + 6) m
```

Chain (four-part decomposition; all parts ≤ `tower (mu_f + 4)
m` for `mu_f ≥ 2`):

1. `Σ_{i<v 0} compileER_runtime f ctx_f_i ≤ m·tower mu_f m
   ≤ tower (mu_f + 2) m` (one mul step).
2. `Σ_{i<v 0} 5·f.interp ctx_f_i ≤ 5m·tower mu_f m ≤
   m·m·tower mu_f m ≤ tower (mu_f + 4) m` (two mul steps).
3. `Σ_{i<v 0} (50 + 2(k+1) + 10·i + 10·outerSum + nRegs_f)
   ≤ 5·m³ ≤ tower 6 m ≤ tower (mu_f + 4) m` (uses
   `mu_f ≥ 2` so `mu_f + 4 ≥ 6`; uses `k ≤ m`, `nRegs_f ≤
   m` from amended offset).
4. `30 + 10·v 0 ≤ tower 2 m ≤ tower (mu_f + 4) m`.

Combining: `4·tower (mu_f + 4) m ≤ m·tower (mu_f + 4) m ≤
tower (mu_f + 6) m`.

Value bound: `natBSum v_0 (f.interp ∘ …) ≤ v_0·tower mu_f m ≤
tower (mu_f + 2) m ≤ tower (mu_f + 6) m` via `natBSum_le_mul_max`.

### `bprod` case (Task 8)

Goal:

```text
compileER_runtime (.bprod f) v ≤ tower (mu_f + 9) m
∧ natBProd (v 0) (fun j => f.interp (Fin.cons j (Fin.tail v)))
    ≤ tower (mu_f + 9) m
```

Chain (six-part decomposition; parts 1–4 land at
`tower (mu_f + 4) m`, parts 5–6 at `tower (mu_f + 7) m`):

- **Parts 1–4**: Same as bsum parts 1–4 (with `Σ 9·B_i ≤
  tower (mu_f + 4) m` replacing bsum's outer `30 + 10·v_0`).
- **Part 5**: `Σ 4·A_i ≤ 4·m·tower (mu_f + 3) m ≤
  m·m·tower (mu_f + 3) m ≤ m·tower (mu_f + 5) m ≤ tower
  (mu_f + 7) m` (uses `A_i ≤ tower (mu_f + 3) m` from value
  bound; two mul steps).
- **Part 6**: `Σ 9·A_i·B_i = Σ 9·A_{i+1} ≤ 9·m·tower
  (mu_f + 3) m ≤ m·m·tower (mu_f + 3) m ≤ m·tower
  (mu_f + 5) m ≤ tower (mu_f + 7) m` (same chain).

Combining: `6·tower (mu_f + 7) m ≤ m·tower (mu_f + 7) m ≤
tower (mu_f + 9) m`.

Value: `natBProd v_0 (f.interp ∘ …) = Π_{j<v_0} f.interp_j
≤ (tower mu_f m)^{v_0} ≤ (tower mu_f m)^m ≤ tower (mu_f + 3) m`
via `Tower.tower_pow_le_tower_add_three` (uses `mu_f ≥ 2` so
`m ≥ 2`).

## Key invariant for bsum/bprod (`mu_f` is at least 2)

`bsum`/`bprod` require `f : ERMor1 (k+1)`, i.e. `f`'s arity is
≥ 1. The only ER atom with `mu = 0` is `.zero : ERMor1 0`
(arity 0), so `f` cannot be `.zero`. All other atoms have `mu
= 2`, and composite constructors inherit `mu ≥ 2` from their
children. Therefore `mu_f ≥ 2` holds throughout the recursion
in the bsum/bprod cases. Several chain steps depend on this
invariant (e.g., `tower 6 m ≤ tower (mu_f + 4) m` requires
`mu_f + 4 ≥ 6` i.e. `mu_f ≥ 2`).

The `comp` case treats `mu_f = 0` as the degenerate `f =
.zero, k = 0` edge where `glue = 0` and the bound trivialises.

## Build constraint

`-DwarningAsError=true` rejects `sorry`. The current working
copy file does not build because of the three remaining
`sorry`s. **The implementation strategy is to fill all three
cases before the next build will pass.** Intermediate sorry
states cannot be committed.

The recipe is also internally non-trivial — earlier session
attempts to switch comp's children-offset from `max` to `Σ`
(to enable a separate `compileER_numRegs e ≤
(boundExprKParams e).2` lemma) triggered `whnf` heartbeat
timeouts. The current recipe (with `max` for `o_g`) avoids
that issue. Do not modify the recipe without escalating.

## Subagent-driven-development plan

Per the user's direction, this session uses
`superpowers:subagent-driven-development` to preserve main
context across the three remaining proof cases. The recommended
breakdown:

1. **Sub-task A: comp case** — dispatch one focused subagent
   with the comp chain spec (above) plus the helpers
   available. The subagent should iterate build-test-fix.
   Expected scope: ~150–250 LOC.
2. **Sub-task B: bsum case** — sequentially after comp lands.
   Same pattern. Carries `AXIOM_ALLOW: Classical.choice`
   annotation (via `Fin.lastCases_castSucc` on `Fin.cons`
   simp). Expected scope: ~150–250 LOC.
3. **Sub-task C: bprod case** — sequentially after bsum. Same
   pattern, with the additional `tower_pow_le_tower_add_three`
   step for the value bound. Expected scope: ~200–300 LOC.

Each sub-task ends only when the relevant case compiles with
no `sorry` and the axiom audit shows the expected envelope.
Sub-tasks are sequential, not parallel — they share the same
file.

Sub-task dispatch prompts must include:

- A pointer to this handoff document.
- The relevant chain spec from §4.2 of the spec doc.
- A reminder that the recipe is fixed and cannot be modified.
- A reminder that `warningAsError=true` requires the case to
  fully close.
- Escalation rule: if a chain genuinely cannot close at the
  recipe values, stop and report rather than silently bumping
  the recipe.

After all three sub-tasks land, run the project-wide
verification: `lake build`, `lake test`, `bash
scripts/check-axioms.sh GebLean/LawvereERKSim/RuntimeBound.lean`.
Expected axiom envelope: `[propext, Quot.sound, Classical.choice]`
for `boundExprKParams_dominates` (Classical.choice inherited
via bsum/bprod `Fin.cons` simp).

## Operational rules (carry forward)

- **Working directory**: `/home/terence/git-workspaces/geb/geb-lean`.
- **No `jj git push` without user line-by-line review**.
- **No raw mutating `git` subcommands** (use `jj`).
- **Build with `lake build`. Never `lake env lean`. Never
  `lake clean`.**
- **Avoid bash process substitution `<(...)`/`>(...)`** (they
  trigger manual approval prompts).
- **Don't `set` a long expression** as a local def — `set m
  := ...` in earlier proof attempts caused whnf timeouts; the
  atom proofs use inline `Fin.maxOfNat _ v + offset` directly
  and complete in reasonable heartbeat budget.
- **Subagent dispatch** is mandatory for each of the three
  cases per the SDD plan above.
- **No commit during this session** — the work goes into the
  working copy, builds clean only when all three cases land,
  then a single commit happens at the end.

## Resumption prompt

Paste this verbatim into the next Claude Code session:

```text
Continue T4 SDD Tasks 5-8 from the existing working copy.

Start by reading:
  docs/superpowers/plans/2026-05-23-step-t4-tasks-5-8-handoff.md

That document is the binding handoff. It contains:
  - The current branch/commit/working-copy state.
  - The spec/plan amendment history (5 rounds adversarial
    review converged on a new recipe with `+k` and
    `+nRegs_f` offset additions plus mu bumps for bsum/bprod).
  - The amended recipe (binding; do NOT modify it).
  - The available helper infrastructure already in the working
    copy.
  - The per-case chain specifications for comp/bsum/bprod.
  - The `mu_f ≥ 2` invariant for bsum/bprod.
  - The subagent-driven-development plan (one subagent per
    case, sequential).
  - The build constraint (warningAsError=true rejects sorry,
    so the implementation must fill all three cases before
    committing).

The branch is `feat/ertok-runtime-bound`. The working copy is
change `uzymllsp` on top of commit `e8c00280` (Task 4). It
contains amended spec/plan, the updated recipe def, atom
proofs (zero/succ/proj/sub), helper infrastructure, and three
remaining sorrys (comp/bsum/bprod). Do not commit until all
three are filled.

Use the `superpowers:subagent-driven-development` skill.
Dispatch one focused subagent for each case (comp, then bsum,
then bprod, sequentially) with the handoff doc plus the
relevant §4.2 chain spec from
  docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md
as the binding inputs.

After all three sub-cases land:
  - `lake build` clean.
  - `lake test` clean.
  - `bash scripts/check-axioms.sh
    GebLean/LawvereERKSim/RuntimeBound.lean` — expect
    `[propext, Quot.sound, Classical.choice]` (Classical.choice
    via the bsum/bprod AXIOM_ALLOW annotation).
  - Then commit (Tasks 5-8 land as one joint commit per the
    plan's joint-commit exception).
```

## References

- T4 spec (5-round adversarial-converged):
  `docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`.
- T4 plan (5-round adversarial-converged):
  `docs/superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md`.
- Post-T3 handoff (T4 brainstorming context):
  `docs/superpowers/plans/2026-05-22-post-t3-handoff.md`.
- Master ER-to-K spec (T1+T2+T3 binding):
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.
- T2 file-split spec:
  `docs/superpowers/specs/2026-05-19-lawvere-er-k-sim-file-split-design.md`.
- Tower lemma surface: `GebLean/Utilities/Tower.lean`.
- `compileER_runtime` and `compileER_numRegs` definitions:
  `GebLean/LawvereERKSim/Compiler.lean` (lines 1598 and 1722).
