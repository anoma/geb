# T3 — URM → Ksim simulator — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** build the K^sim simulator `simulate : URMProgram a →
KMor1 (a + 1)` for the zero-test URM kernel (T1) consumed by the
ER→URM compiler (T2), with correctness theorem `simulate_interp`
and level bound `simulate_level ≤ 2`.

**Architecture:** a single `KMor1.simrec` with system size
`P.numRegs + 1` whose components track register values
(indices `0..numRegs−1`) and the PC (index `numRegs`, the last
slot). Per-instruction dispatch via a non-substituting bottom-up
`cond`-chain helper `KMor1.pcDispatch`, which reads the last
context slot and selects branches keyed to PC values. Correctness
by induction on time `y` with a conjunctive vector IH
(`simulate_step_match`) covering all `numRegs + 1` simrec
components.

**Tech Stack:** Lean 4 (toolchain `lean-toolchain`), mathlib (via
`lake`), project-local `GebLean.LawvereKSim`,
`GebLean.LawvereKSimInterp`, `GebLean.Utilities.KArith`,
`GebLean.Utilities.ZeroTestURM`.

**Spec under implementation:**
[`docs/superpowers/specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md`](../specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md)
(rounds 1–4 converged on 2026-05-21).

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Workflow notes](#workflow-notes)
- [Task 0: Baseline verification](#task-0-baseline-verification)
- [Task 1: `KMor1.natK` and `KMor1.natK'` in `KArith.lean`](#task-1-kmor1natk-and-kmor1natk-in-karithlean)
- [Task 2: Create `KSimURMSimulator.lean`; add `KMor1.predIter`](#task-2-create-ksimurmsimulatorlean-add-kmor1prediter)
- [Task 3: `KMor1.pcDispatchFrom` + `KMor1.pcDispatch`](#task-3-kmor1pcdispatchfrom--kmor1pcdispatch)
- [Task 4: `baseFamily`](#task-4-basefamily)
- [Task 5: `stepFamily`](#task-5-stepfamily)
- [Task 6: `simulate` assembly](#task-6-simulate-assembly)
- [Task 7: `simulate_step_match` conjunctive induction](#task-7-simulate_step_match-conjunctive-induction)
- [Task 8: `simulate_interp` and `simulate_level`](#task-8-simulate_interp-and-simulate_level)
- [Task 9: Re-export, axiom audit, final lint sweep](#task-9-re-export-axiom-audit-final-lint-sweep)

<!-- END doctoc -->

---

## Workflow notes

Rules that bind every task in this plan:

- **Build with `lake build`. Never `lake env lean`. Never `lake
  clean`** (per
  [`.claude/rules/lean-coding.md`](../../.claude/rules/lean-coding.md)
  § Lake / build workflow).
- **One declaration at a time.** Get each new `def` / `theorem`
  to fully compile (no `sorry`, no `_`, no `admit`) before
  proceeding to the next. Per
  `.claude/rules/lean-coding.md` § Proof guidelines.
- **`sorry` only between commits.** Use the underscore `_` form
  for genuine placeholders during exploration; replace with the
  filled term before committing. `admit` is never permitted.
- **Axiom audit per declaration.** After each task's final
  build is clean, run
  `bash scripts/check-axioms.sh <FullyQualifiedName>` on every
  new public declaration. Expected output: only `[propext,
  Quot.sound]` in the axiom set. Any extra axiom (in
  particular `Classical.choice` or `sorryAx`) is a defect that
  must be fixed before commit.
- **Conventional commits.** Subject line: `feat(ertok): …`
  for the new helpers and simulator; `chore(ertok): …` for
  axiom audits and re-exports; `refactor(ertok): …` if any
  reshape is needed. Imperative present, lowercase first
  letter, no trailing period. Body: motivation + scope.
- **Markdownlint-clean docstrings.** Lean module docstrings
  inside `/-! … -/` and declaration docstrings inside
  `/-- … -/` follow the mathlib `doc.html` section ordering.
- **Generic user references in commit messages.** Use "the
  user" / "they" / "them"; no first names.
- **No raw mutating `git` subcommands.** Use `jj` for
  state-mutating operations (per
  [`CLAUDE.md`](../../CLAUDE.md) § Rules).
- **Mathlib upstream guides (re-fetch on entry to each task that
  introduces new public API):**
  - `https://leanprover-community.github.io/contribute/naming.html`
  - `https://leanprover-community.github.io/contribute/style.html`
  - `https://leanprover-community.github.io/contribute/doc.html`

For every `def` / `theorem` introduced below, the implementer
must:

1. Read the spec §-reference cited in the task header.
2. Add the declaration with the type signature and a `by sorry`
   body (for theorems) or `:= sorry` (for `def`s whose body is
   non-trivial). Compile with `lake build` to verify the
   signature type-checks.
3. Replace the `sorry` with the actual term/proof.
4. Compile again. Verify the build is clean (zero errors, zero
   warnings).
5. Run `bash scripts/check-axioms.sh <FullyQualifiedName>`
   (for public declarations only; `private` declarations are
   not separately audited but inherit clean audit from their
   public consumers).
6. Commit per the task's commit message template.

---

## Task 0: Baseline verification

Confirm the working state before touching anything. If this
fails, fix the failure before proceeding.

**Files:**

- No edits.

- [ ] **Step 0.1: Confirm `lake build` is clean on the current
  HEAD.**

Run: `lake build`

Expected: zero errors, zero warnings, exit code 0.

- [ ] **Step 0.2: Confirm `scripts/check-axioms.sh` passes on
  the T2 final theorem.**

Run: `bash scripts/check-axioms.sh GebLean.LawvereERKSim.compileER_runFor`

Expected: axiom set is `[propext, Quot.sound]` only.

- [ ] **Step 0.3: Confirm the plan commit is at HEAD.**

Run: `jj log -r 'description(glob:"docs(ertok)*plan*")' --no-graph --limit 3`

Expected: the most recent matching commit's description
includes the phrase "implementation plan" and references T3.

If any of the above fails, halt: investigate before
proceeding. T3 should land on a clean baseline.

---

## Task 1: `KMor1.natK` and `KMor1.natK'` in `KArith.lean`

Spec § 3.6. Constant-K^sim morphisms at level 0; `natK c : KMor1
0` is built by `c`-fold composition of `succ` with `zero`;
`natK' n c : KMor1 n` lifts to arbitrary arity via composition
with `Fin.elim0`.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean` (append between
  line 264, the end of the `cond` example, and line 266, the
  start of the `notEq1` docstring).

- [ ] **Step 1.1: Locate the insertion point.**

Run (from the project root
`/home/terence/git-workspaces/geb/geb-lean`):

```bash
grep -n "KMor1.cond\|KMor1.notEq1" \
  /home/terence/git-workspaces/geb/geb-lean/GebLean/Utilities/KArith.lean \
  | head -10
```

Expected: shows `def KMor1.cond` at line 222 and the
`example : KMor1.cond.level = 1` example at line 264; `def
KMor1.notEq1` at line 278 with its docstring starting at line
266. Insert new declarations between line 264 and line 266
(after the `cond` example, before the `notEq1` docstring).

- [ ] **Step 1.2: Add `KMor1.natK` definition.**

Insert into `GebLean/Utilities/KArith.lean`:

```lean
/-- Constant-`c` morphism at arity 0, built by `c`-fold
composition of `KMor1.succ` over `KMor1.zero`. Level 0.

Tourlakis 2018 § 0.1.0.2 (p. 1): closure of `K_0 = {λx.x,
λx.x+1}` under substitution yields all natural-number
constants. GebLean's `KMor1.zero` is a separate constructor; the
`succ ∘ zero` pattern realises the same level-0 closure
principle. -/
def KMor1.natK : ℕ → KMor1 0
  | 0     => KMor1.zero
  | c + 1 =>
    KMor1.comp KMor1.succ (fun _ : Fin 1 => KMor1.natK c)
```

- [ ] **Step 1.3: Build to verify the definition.**

Run: `lake build GebLean.Utilities.KArith`

Expected: clean build.

- [ ] **Step 1.4: Add `interp_natK` simp lemma.**

Insert directly below `KMor1.natK`:

```lean
/-- The interpretation of `KMor1.natK c` at the empty
context is `c`. -/
@[simp] theorem KMor1.interp_natK (c : ℕ) (ctx : Fin 0 → ℕ) :
    (KMor1.natK c).interp ctx = c := by
  induction c with
  | zero => rfl
  | succ c ih =>
    simp only [KMor1.natK, KMor1.interp_comp, KMor1.interp_succ]
    rw [ih]
```

- [ ] **Step 1.5: Add `natK_level` lemma.**

Insert below `interp_natK`:

```lean
/-- `KMor1.natK c` has level 0 for every `c`. -/
theorem KMor1.natK_level (c : ℕ) : (KMor1.natK c).level = 0 := by
  induction c with
  | zero => rfl
  | succ c ih =>
    -- natK (c+1) = comp succ (fun _ : Fin 1 => natK c). By
    -- `KMor1.level`'s `.comp` clause, this is
    -- `max succ.level (Finset.univ.sup (fun _ => (natK c).level))`.
    -- `succ.level = 0` (rfl); the Fin 1 sup is bounded by 0 via
    -- `Finset.sup_le` plus `ih`; the outer max closes by `omega`.
    show KMor1.level
        (KMor1.comp KMor1.succ (fun _ : Fin 1 => KMor1.natK c)) = 0
    unfold KMor1.level
    have hsup :
        Finset.univ.sup (fun _ : Fin 1 => (KMor1.natK c).level) ≤ 0 := by
      apply Finset.sup_le
      intro _ _
      rw [ih]
    omega
```

Note: the proof relies on three mathlib lemmas: `Finset.sup_le`
(verified by `mcp__lean-lsp__lean_local_search` against
`Mathlib.Data.Finset.Lattice.Fold`); `KMor1.level`'s `.succ`
case reduces `KMor1.succ.level` to `0` definitionally; and
`omega` discharges the `max 0 hsup ≤ 0 → max 0 hsup = 0` shape
constructively.

- [ ] **Step 1.6: Add `KMor1.natK'` lifted variant.**

Insert below `natK_level`:

```lean
/-- The constant-`c` morphism at arity `n`, obtained by
composing `KMor1.natK c` with the empty family `Fin.elim0`.
Level 0. -/
def KMor1.natK' (n c : ℕ) : KMor1 n :=
  KMor1.comp (KMor1.natK c) Fin.elim0

/-- The interpretation of `KMor1.natK' n c` at any context is
`c`. -/
@[simp] theorem KMor1.interp_natK' (n c : ℕ) (ctx : Fin n → ℕ) :
    (KMor1.natK' n c).interp ctx = c := by
  simp only [KMor1.natK', KMor1.interp_comp, KMor1.interp_natK]

/-- `KMor1.natK' n c` has level 0 for every `n` and `c`. -/
theorem KMor1.natK'_level (n c : ℕ) :
    (KMor1.natK' n c).level = 0 := by
  -- natK' n c = comp (natK c) Fin.elim0. By `KMor1.level`'s
  -- `.comp` clause, this is `max (natK c).level (Finset.univ.sup
  -- (fun i : Fin 0 => …))`. The `Fin 0` instance of `Finset.univ`
  -- is empty (`Finset.univ_eq_empty`); `Finset.sup_empty` then
  -- collapses the sup to `⊥ = 0`; `(natK c).level = 0` by
  -- `KMor1.natK_level`; the outer `max 0 0 = 0`.
  show KMor1.level (KMor1.comp (KMor1.natK c) Fin.elim0) = 0
  unfold KMor1.level
  rw [KMor1.natK_level, show (Finset.univ : Finset (Fin 0)) = ∅
    from Finset.univ_eq_empty, Finset.sup_empty]
```

Note: `Finset.univ_eq_empty` (verified via `lean_local_search`,
from `Mathlib.Data.Finset.Basic`) carries an `IsEmpty` instance
inferred from `Fin 0`'s emptiness. `Finset.sup_empty` is the
standard sup-of-empty lemma in the same module.

- [ ] **Step 1.7: Build to verify all five new declarations
  compile.**

Run: `lake build GebLean.Utilities.KArith`

Expected: clean build, zero errors, zero warnings.

- [ ] **Step 1.8: Run axiom audit on each new public declaration.**

Run, in sequence:

```bash
bash scripts/check-axioms.sh GebLean.KMor1.natK
bash scripts/check-axioms.sh GebLean.KMor1.interp_natK
bash scripts/check-axioms.sh GebLean.KMor1.natK_level
bash scripts/check-axioms.sh GebLean.KMor1.natK'
bash scripts/check-axioms.sh GebLean.KMor1.interp_natK'
bash scripts/check-axioms.sh GebLean.KMor1.natK'_level
```

Expected for each: axiom set is `[propext, Quot.sound]` only.
If any audit reports `Classical.choice` or `sorryAx`, halt and
fix the offending proof.

- [ ] **Step 1.9: Commit Task 1.**

```bash
jj describe -m "feat(ertok): add KMor1.natK and KMor1.natK' constant helpers

introduce KMor1.natK : ℕ → KMor1 0 built by c-fold composition of
KMor1.succ over KMor1.zero, plus KMor1.natK' n c : KMor1 n via
KMor1.comp with Fin.elim0. interp simp lemmas and level=0 lemmas
included. Per spec § 3.6; precedent KMor1.one at KArith.lean:31.
audit [propext, Quot.sound]-only axiom hygiene on all six new
public declarations."
jj new -m ""
```

---

## Task 2: Create `KSimURMSimulator.lean`; add `KMor1.predIter`

Spec § 3.5 (predIter portion). The `k`-fold composition of
`KMor1.pred` over `KMor1.proj (Fin.last n)`. Private declaration;
provides the level-1 test slot for `pcDispatch`'s `cond` chain.

**Files:**

- Create: `GebLean/Utilities/KSimURMSimulator.lean`

- [ ] **Step 2.1: Create the new file with imports and module
  docstring.**

Write to `GebLean/Utilities/KSimURMSimulator.lean`:

```lean
import GebLean.Utilities.ZeroTestURM
import GebLean.Utilities.KArith
import GebLean.LawvereKSim
import GebLean.LawvereKSimInterp

/-!
# K^sim simulator for the zero-test URM kernel

For every `URMProgram a` (T1 + T2's `URMProgram` family at
`GebLean/Utilities/ZeroTestURM.lean:122`), this module builds a
single-output K^sim morphism `simulate : URMProgram a →
KMor1 (a + 1)` whose interpretation at `(y, v)` equals the value
of the output register after `y` steps from `URMState.init P v`.
The simulator is a `KMor1.simrec` (`LawvereKSim.lean:50`) with
system size `P.numRegs + 1`: components `0, …, numRegs - 1`
track register values; component `numRegs` (the last) tracks the
PC. Output index is `P.outputReg.castSucc`. The simulator is at
K^sim level ≤ 2 (base sup 0, step sup ≤ 1, simrec adds 1).

## Main definitions

- `KMor1.pcDispatch`: a non-substituting bottom-up `cond`-chain
  combinator reading the last context slot (the PC) and
  selecting branches keyed to specific PC values.
- `baseFamily`: the simrec's base family at the initial state.
- `stepFamily`: the simrec's step family at one URM step.
- `simulate`: the public-facing simulator term.

## Main statements

- `KMor1.interp_pcDispatch_match`, `KMor1.interp_pcDispatch_default`:
  the dispatcher's interpretation simp lemmas.
- `KMor1.pcDispatch_level`: the dispatcher's level bound (1 when
  branches and default are level ≤ 1).
- `simulate_interp`: the simulator's output equals
  `URMState.runFor`'s output projected at `outputReg`.
- `simulate_level`: the simulator is at K^sim level ≤ 2.

## Implementation notes

The bottom-up `cond`-chain reads
`pred^k(PC) = 0 ⇔ PC ≤ k` (Tourlakis § 0.1.0.20 chained with
§ 0.1.0.8); the nested fall-through structure converts the
inequality into the equality `PC = k` at each level. The
recursive case does *not* substitute the PC slot via
`KMor1.comp _ shift` — branches and default sit at the same
context as their siblings, so the interp simp lemmas hold
verbatim without context-substitution corrections.

## References

- Tourlakis 2018 `PR-complexity-topics.pdf` § 0.1.0.37
  (simulation lemma).
- `docs/superpowers/specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md`
  § 3 (architecture), § 4 (correctness), § 5 (level).

## Tags

URM, K^sim, simulator, simrec, Tourlakis
-/

namespace GebLean

end GebLean

namespace GebLean.KSimURMSimulator

open GebLean.ZeroTestURM
open GebLean

end GebLean.KSimURMSimulator
```

(The two `namespace … end namespace` skeletons are placeholders;
later tasks fill them with the relevant declarations. The single
`open GebLean.ZeroTestURM` inside `namespace GebLean.KSimURMSimulator`
serves all consumers in Tasks 4 – 8; the outer `namespace GebLean`
block carries only the `KMor1.*` extensions in Tasks 2 – 3 and
does not require `open`. Duplicate `open`s removed per plan
round-3 finding R3-M2.)

**File-layout reference (per R3-S5):**

| Task | Content | Namespace |
| --- | --- | --- |
| 2 (`predIter`) | `KMor1.predIter`, `interp_predIter`, `predIter_level` | `GebLean` |
| 3 (`pcDispatch`) | `KMor1.pcDispatchFrom`, `KMor1.pcDispatch`, the four interp / level lemmas | `GebLean` |
| 4 (`baseFamily`) | `baseFamily`, `baseFamily_level` | `GebLean.KSimURMSimulator` |
| 5 (`stepFamily`) | `I_prev`, `v_j_prev`, `branches_pc`, `branches_j`, `stepFamily`, `stepFamily_level` | `GebLean.KSimURMSimulator` |
| 6 (`simulate`) | `simulate` | `GebLean.KSimURMSimulator` |
| 7 (correctness) | `runFor_succ_init_back`, `simulate_step_match` | `GebLean.KSimURMSimulator` |
| 8 (public theorems) | `simulate_interp`, `simulate_level` | `GebLean.KSimURMSimulator` |

The implementer inserts Task 2 – 3 content between the first
`namespace GebLean` and `end GebLean`; Task 4 – 8 content between
`namespace GebLean.KSimURMSimulator` and
`end GebLean.KSimURMSimulator`.

- [ ] **Step 2.2: Build to verify the skeleton compiles.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: clean build.

- [ ] **Step 2.3: Add `KMor1.predIter` private definition.**

Insert inside the `namespace GebLean` block (replacing or
augmenting the empty body):

```lean
/-- The `k`-fold composition of `KMor1.pred` over the last
context slot, `KMor1.proj (Fin.last n)`. Level 0 for `k = 0`,
level 1 for `k ≥ 1`. Used inside `KMor1.pcDispatch`'s `cond`
chain as the level-1 inequality test `predIter k = 0 ⇔ PC ≤ k`
(Tourlakis § 0.1.0.20 chained with § 0.1.0.8). -/
private def KMor1.predIter (n k : ℕ) : KMor1 (n + 1) :=
  match k with
  | 0     => KMor1.proj (Fin.last n)
  | k + 1 =>
    KMor1.comp KMor1.pred
      (fun _ : Fin 1 => KMor1.predIter n k)
```

- [ ] **Step 2.4: Build to verify.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: clean build.

- [ ] **Step 2.5: Add `interp_predIter` simp lemma.**

Insert directly below `KMor1.predIter`:

```lean
/-- `KMor1.predIter n k` interprets as `k`-fold `Nat.pred` over
the last context slot, equivalent to `ctx (Fin.last n) ∸ k`. -/
@[simp] theorem KMor1.interp_predIter
    (n k : ℕ) (ctx : Fin (n + 1) → ℕ) :
    (KMor1.predIter n k).interp ctx = ctx (Fin.last n) ∸ k := by
  induction k with
  | zero =>
    simp only [KMor1.predIter, KMor1.interp_proj, Nat.sub_zero]
  | succ k ih =>
    simp only [KMor1.predIter, KMor1.interp_comp,
      KMor1.interp_pred]
    rw [ih]
    omega
```

- [ ] **Step 2.6: Add `predIter_level` lemma.**

Insert directly below `interp_predIter`:

```lean
/-- `KMor1.predIter n k` has level ≤ 1 for every `n` and `k`
(level 0 when `k = 0`, level 1 when `k ≥ 1`). -/
theorem KMor1.predIter_level (n k : ℕ) :
    (KMor1.predIter n k).level ≤ 1 := by
  induction k with
  | zero =>
    -- predIter n 0 = proj (Fin.last n); proj.level = 0 ≤ 1.
    show KMor1.level (KMor1.proj (Fin.last n)) ≤ 1
    unfold KMor1.level
    omega
  | succ k ih =>
    -- predIter n (k+1) = comp pred (fun _ : Fin 1 => predIter n k).
    -- level = max pred.level (Finset.univ.sup (fun _ => (predIter n k).level))
    --       = max 1 (≤ 1) = 1.
    show KMor1.level
        (KMor1.comp KMor1.pred (fun _ : Fin 1 => KMor1.predIter n k))
        ≤ 1
    unfold KMor1.level
    have hsup :
        Finset.univ.sup (fun _ : Fin 1 => (KMor1.predIter n k).level) ≤ 1 := by
      apply Finset.sup_le
      intro _ _
      exact ih
    omega
```

Note: replaces the round-2-flagged `simp only [Finset.univ.sup]`
(dot-notation-as-simp-arg) with explicit `unfold KMor1.level`
plus `Finset.sup_le` discharge. `KMor1.pred.level = 1` reduces
through `unfold KMor1.level`'s `.pred` clause; `omega` closes
the resulting `max 1 hsup ≤ 1` shape using `hsup`.

- [ ] **Step 2.7: Build to verify.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: clean build.

- [ ] **Step 2.8: Axiom audit.**

Run:

```bash
bash scripts/check-axioms.sh GebLean.KMor1.interp_predIter
bash scripts/check-axioms.sh GebLean.KMor1.predIter_level
```

Note: `KMor1.predIter` is `private` and not separately audited;
its hygiene flows through its public consumers in later tasks.

Expected for each: `[propext, Quot.sound]` only.

- [ ] **Step 2.9: Commit Task 2.**

```bash
jj describe -m "feat(ertok): create KSimURMSimulator.lean with KMor1.predIter helper

introduce the new GebLean/Utilities/KSimURMSimulator.lean file
with module docstring and namespace skeleton; add private def
KMor1.predIter (n k : ℕ) : KMor1 (n + 1) computing the k-fold
pred composition over the last context slot, plus the @[simp]
interp lemma KMor1.interp_predIter (= ctx (Fin.last n) ∸ k) and
the level lemma KMor1.predIter_level (≤ 1). Per spec § 3.5
predIter portion; predIter feeds pcDispatch's cond-chain test
in Task 3."
jj new -m ""
```

---

## Task 3: `KMor1.pcDispatchFrom` + `KMor1.pcDispatch`

Spec § 3.5. The non-substituting bottom-up `cond` chain that
reads the last context slot (the PC) and selects branches at
specific PC values. `pcDispatchFrom k size` is a private
auxiliary; `pcDispatch size` is the public entry point.

**Files:**

- Modify: `GebLean/Utilities/KSimURMSimulator.lean` (append
  inside `namespace GebLean`, after `predIter_level`).

- [ ] **Step 3.1: Add `KMor1.pcDispatchFrom` private
  definition.**

Insert below `KMor1.predIter_level`:

```lean
/-- Auxiliary continuation for `KMor1.pcDispatch`: at offset
`k`, test `KMor1.predIter n k = 0 ⇔ PC ≤ k`, select
`branches ⟨0, _⟩` if so, else recurse at offset `k + 1` over
`branches ∘ Fin.succ`. The recursive call sits at the *same*
context as the surrounding `cond`; branches and default are
never wrapped in a context-substituting `KMor1.comp`. -/
private def KMor1.pcDispatchFrom {n : ℕ}
    (k size : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) :
    KMor1 (n + 1) :=
  match size with
  | 0 => default
  | size' + 1 =>
    KMor1.comp KMor1.cond
      (fun i : Fin 3 => match i with
        | ⟨0, _⟩ => KMor1.predIter n k
        | ⟨1, _⟩ => branches ⟨0, by omega⟩
        | ⟨2, _⟩ =>
          KMor1.pcDispatchFrom (k + 1) size'
            (fun j : Fin size' => branches j.succ) default)
```

Note: the inner `match` on `Fin 3` uses unbundled
constructors `⟨0, _⟩`, `⟨1, _⟩`, `⟨2, _⟩` because `Fin.cases`
on the literal `Fin 3` value indices is what `KMor1.comp`'s
family expects. The `by omega` discharges the
`0 < size' + 1` proof obligation for `Fin (size' + 1)`'s
constructor.

- [ ] **Step 3.2: Build to verify.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: clean build.

- [ ] **Step 3.3: Add `KMor1.pcDispatch` public definition.**

Insert below `KMor1.pcDispatchFrom`:

```lean
/-- The PC-dispatch combinator: given `size` branches keyed to
specific PC values (the last context slot) and a `default` for
PC values `≥ size`, return a `KMor1 (n + 1)` that interprets to
`branches k` when PC = `k` (`k < size`), else `default`.

Implementation defers to `KMor1.pcDispatchFrom 0 size`. -/
def KMor1.pcDispatch {n : ℕ} (size : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) :
    KMor1 (n + 1) :=
  KMor1.pcDispatchFrom 0 size branches default
```

- [ ] **Step 3.4: Build to verify.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: clean build.

- [ ] **Step 3.5: Add two inner lemmas
  (`pcDispatchFrom_match`, `pcDispatchFrom_default`) with
  explicit hypotheses.**

Insert below `KMor1.pcDispatch`:

```lean
private theorem KMor1.interp_pcDispatchFrom_match
    {n : ℕ} (size : ℕ) (k : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) (ctx : Fin (n + 1) → ℕ)
    (j : Fin size) (h : ctx (Fin.last n) = k + j.val) :
    (KMor1.pcDispatchFrom k size branches default).interp ctx
      = (branches j).interp ctx := by
  induction size generalizing k branches j with
  | zero => exact Fin.elim0 j
  | succ size' ih =>
    simp only [KMor1.pcDispatchFrom, KMor1.interp_comp,
      KMor1.interp_cond, KMor1.interp_predIter]
    by_cases hj : j = ⟨0, by omega⟩
    · subst hj
      have : ctx (Fin.last n) - k = 0 := by
        rw [h]; simp
      rw [this]; simp
    · -- j ≥ 1, so PC ≥ k + 1; recurse via ih at (k + 1).
      have hjpos : 0 < j.val := by
        rcases j with ⟨v, hv⟩
        rcases v with _ | v'
        · exact absurd (Fin.ext rfl : (⟨0, by omega⟩ : Fin (size' + 1)) = ⟨0, hv⟩) hj
        · simp
      have hsub : ctx (Fin.last n) - k ≠ 0 := by
        rw [h]; omega
      -- Per plan round-3 finding R3-B1: discharge the `if`-branch
      -- selection directly via `rw [if_neg hsub]` on the open goal,
      -- rather than via a metavariable-laden `have` block.
      rw [if_neg hsub]
      -- Now apply ih to the recursive call.
      have hpred : ctx (Fin.last n) = (k + 1) + (j.val - 1) := by
        rw [h]; omega
      have ih_applied :=
        ih (k + 1) (fun j' : Fin size' => branches j'.succ)
          ⟨j.val - 1, by omega⟩ hpred
      convert ih_applied using 1
      congr 1
      apply Fin.ext
      simp [Fin.succ]
      omega

private theorem KMor1.interp_pcDispatchFrom_default
    {n : ℕ} (size : ℕ) (k : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) (ctx : Fin (n + 1) → ℕ)
    (h : ctx (Fin.last n) ≥ k + size) :
    (KMor1.pcDispatchFrom k size branches default).interp ctx
      = default.interp ctx := by
  induction size generalizing k branches with
  | zero => simp [KMor1.pcDispatchFrom]
  | succ size' ih =>
    simp only [KMor1.pcDispatchFrom, KMor1.interp_comp,
      KMor1.interp_cond, KMor1.interp_predIter]
    have hsub : ctx (Fin.last n) - k ≠ 0 := by omega
    rw [if_neg hsub]
    apply ih
    omega
```

- [ ] **Step 3.6: Build to verify.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: clean build. If any of the auxiliary lemmas fails
(unification or arithmetic), use
`mcp__lean-lsp__lean_goal` to inspect the goal state at the
failure point and adjust.

- [ ] **Step 3.7: Add the public `interp_pcDispatch_match` simp
  lemma.**

Insert below `interp_pcDispatchFrom_default`:

```lean
/-- When the PC slot equals `k.val` for some `k : Fin size`,
`KMor1.pcDispatch` interprets as `branches k`. -/
@[simp] theorem KMor1.interp_pcDispatch_match
    {n : ℕ} (size : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) (ctx : Fin (n + 1) → ℕ)
    (k : Fin size) (h : ctx (Fin.last n) = k.val) :
    (KMor1.pcDispatch size branches default).interp ctx
      = (branches k).interp ctx := by
  unfold KMor1.pcDispatch
  exact KMor1.interp_pcDispatchFrom_match size 0 branches default
    ctx k (by rw [h]; rfl)
```

- [ ] **Step 3.8: Add the public `interp_pcDispatch_default`
  simp lemma.**

Insert below `interp_pcDispatch_match`:

```lean
/-- When the PC slot is ≥ `size`, `KMor1.pcDispatch` interprets
as `default`. -/
@[simp] theorem KMor1.interp_pcDispatch_default
    {n : ℕ} (size : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) (ctx : Fin (n + 1) → ℕ)
    (h : ctx (Fin.last n) ≥ size) :
    (KMor1.pcDispatch size branches default).interp ctx
      = default.interp ctx := by
  unfold KMor1.pcDispatch
  exact KMor1.interp_pcDispatchFrom_default size 0 branches default
    ctx (by omega)
```

- [ ] **Step 3.9: Add the `pcDispatch_level` lemma.**

Insert below `interp_pcDispatch_default`:

```lean
/-- Inner level lemma for `pcDispatchFrom`: when branches and
default are level ≤ 1, the dispatcher is level ≤ 1. By
induction on `size` with `k` and `branches` generalised. -/
private theorem KMor1.pcDispatchFrom_level
    {n : ℕ} (size : ℕ) (k : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1))
    (h_branches : ∀ j, (branches j).level ≤ 1)
    (h_default : default.level ≤ 1) :
    (KMor1.pcDispatchFrom k size branches default).level ≤ 1 := by
  induction size generalizing k branches with
  | zero =>
    -- pcDispatchFrom k 0 branches default = default.
    show (default).level ≤ 1
    exact h_default
  | succ size' ih =>
    have hpred : (KMor1.predIter n k).level ≤ 1 :=
      KMor1.predIter_level n k
    have hb0 : (branches ⟨0, by omega⟩).level ≤ 1 :=
      h_branches _
    have hrecur : (KMor1.pcDispatchFrom (k + 1) size'
        (fun j : Fin size' => branches j.succ) default).level ≤ 1 :=
      ih (k + 1) (fun j => branches j.succ)
        (fun j => h_branches j.succ)
    -- Pin the goal to its `KMor1.level`-of-`.comp`-of-`.cond`
    -- normal form via `change`, which preserves the inner
    -- `(KMor1.pcDispatchFrom (k+1) size' …).level` slot as an
    -- opaque ≤-1 bound from `hrecur` (rather than recursively
    -- unfolding it, as `simp only [KMor1.level]` would do — per
    -- plan round-2 finding R2-S3).
    change max (KMor1.cond.level)
           (Finset.univ.sup (fun i : Fin 3 =>
             match i with
             | ⟨0, _⟩ => (KMor1.predIter n k).level
             | ⟨1, _⟩ => (branches ⟨0, by omega⟩).level
             | ⟨2, _⟩ => (KMor1.pcDispatchFrom (k + 1) size'
                 (fun j : Fin size' => branches j.succ) default).level))
           ≤ 1
    have hcond_level : (KMor1.cond : KMor1 3).level = 1 := by decide
    have hsup :
        Finset.univ.sup (fun i : Fin 3 =>
          match i with
          | ⟨0, _⟩ => (KMor1.predIter n k).level
          | ⟨1, _⟩ => (branches ⟨0, by omega⟩).level
          | ⟨2, _⟩ => (KMor1.pcDispatchFrom (k + 1) size'
              (fun j => branches j.succ) default).level) ≤ 1 := by
      apply Finset.sup_le
      intro i _
      -- Lean-core `match` discharge per project memory
      -- `feedback_fin_cases_pulls_classical_choice.md`.
      match i with
      | ⟨0, _⟩ => exact hpred
      | ⟨1, _⟩ => exact hb0
      | ⟨2, _⟩ => exact hrecur
    rw [hcond_level]
    exact Nat.max_le.mpr ⟨le_refl 1, hsup⟩
```

Note: `change` is preferred over `simp only [KMor1.level]` here
because `simp only` would recursively descend into the inner
`(KMor1.pcDispatchFrom (k+1) size' …).level` and unfold it,
defeating the opaque-bound reasoning via `hrecur`. The `change`
relies on `pcDispatchFrom`'s `.succ` equation and `KMor1.level`'s
`.comp` equation as `rfl`-equalities at the top level only.

- [ ] **Step 3.10: Add the public `pcDispatch_level` lemma.**

Insert below `pcDispatchFrom_level`:

```lean
/-- `KMor1.pcDispatch` is at level ≤ 1 when branches and
default are level ≤ 1. -/
theorem KMor1.pcDispatch_level
    {n : ℕ} (size : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1))
    (h_branches : ∀ j, (branches j).level ≤ 1)
    (h_default : default.level ≤ 1) :
    (KMor1.pcDispatch size branches default).level ≤ 1 := by
  unfold KMor1.pcDispatch
  exact KMor1.pcDispatchFrom_level size 0 branches default
    h_branches h_default
```

- [ ] **Step 3.11: Build to verify.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: clean build.

- [ ] **Step 3.12: Axiom audit on the three public
  declarations.**

```bash
bash scripts/check-axioms.sh GebLean.KMor1.interp_pcDispatch_match
bash scripts/check-axioms.sh GebLean.KMor1.interp_pcDispatch_default
bash scripts/check-axioms.sh GebLean.KMor1.pcDispatch_level
```

Expected for each: `[propext, Quot.sound]` only.

If `Classical.choice` appears, suspect a stray mathlib
`fin_cases` tactic and replace with explicit `match` /
Lean-core `Fin.cases` per the project memory at
[`feedback_fin_cases_pulls_classical_choice.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_fin_cases_pulls_classical_choice.md).

- [ ] **Step 3.13: Commit Task 3.**

```bash
jj describe -m "feat(ertok): add KMor1.pcDispatch and its inner lemmas

introduce private def KMor1.pcDispatchFrom (n k size : ℕ) and
public def KMor1.pcDispatch (size : ℕ), the non-substituting
bottom-up cond-chain combinator reading the last context slot
and selecting branches at specific PC values. include private
interp_pcDispatchFrom_match / _default and pcDispatchFrom_level
inner lemmas, plus the public @[simp] interp_pcDispatch_match /
_default and pcDispatch_level. per spec § 3.5. branches and
default share arity (n + 1) so each may read the PC slot
directly; the recursion is a flat fold with no
context-substitution wrapper. audit [propext, Quot.sound]-only
axiom hygiene on all three public declarations."
jj new -m ""
```

---

## Task 4: `baseFamily`

Spec § 3.3. The simrec's base family at `y = 0`: PC component is
`KMor1.zero` (initial PC = 0); register-`j` component (for
`j : Fin P.numRegs`) returns the input slot's projection if `j`
is in `inputRegs`' image, else `KMor1.zero`.

**Files:**

- Modify: `GebLean/Utilities/KSimURMSimulator.lean` (append
  inside `namespace GebLean.KSimURMSimulator`).

- [ ] **Step 4.1: Add `baseFamily` definition.**

Insert inside `namespace GebLean.KSimURMSimulator`:

```lean
/-- The base family for `simulate`'s simrec at time `y = 0`,
mirroring `URMState.init` syntactically. By `Fin.lastCases`:
the `Fin.last` case is the PC component (`KMor1.zero`, since
`URMState.init`'s `pc := 0`); the `castSucc` case is a register
component for `r : Fin P.numRegs`, which performs the same
`List.find?` lookup as `URMState.init`'s `regs` field and
returns the corresponding `KMor1.proj` for an input slot, or
`KMor1.zero` otherwise.

In the `some i` branch, `i : Fin a` is the input slot index
returned by `List.find?` (distinct from the outer-scope
register index `r : Fin P.numRegs`); `KMor1.proj i` then has
type `KMor1 a`, matching the `baseFamily` return type.

Per spec § 3.3. -/
def baseFamily {a : ℕ} (P : URMProgram a) :
    Fin (P.numRegs + 1) → KMor1 a :=
  Fin.lastCases
    -- PC component: initial value 0.
    (KMor1.zero : KMor1 a)
    -- Register-r component: input projection if `r` is the
    -- target of some input slot, else zero.
    (fun r : Fin P.numRegs =>
      match (List.finRange a).find?
            (fun i => decide (P.inputRegs i = r)) with
      | some i => KMor1.proj i
      | none   => KMor1.zero)
```

- [ ] **Step 4.2: Build to verify.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: clean build.

- [ ] **Step 4.3: Add a level lemma for the base family.**

Insert below `baseFamily`:

```lean
/-- Every base-family component is at level 0 (each is
`KMor1.zero` or `KMor1.proj _`). -/
theorem baseFamily_level {a : ℕ} (P : URMProgram a)
    (j : Fin (P.numRegs + 1)) :
    (baseFamily P j).level = 0 := by
  -- Project-idiomatic Fin.lastCases case-split: per
  -- `GebLean/LawvereBTInterp.lean:625, 627, 637, 668, 669`, the
  -- pattern is `refine Fin.lastCases ?_ ?_ j` followed by
  -- `simp only [Fin.lastCases_last]` / `[Fin.lastCases_castSucc]`
  -- (per plan round-3 finding R3-S4). The `induction j using
  -- Fin.lastCases with | last | cast` syntax is not used in this
  -- project; the eliminator's binding rules for that form depend
  -- on whether `Fin.lastCases` is tagged `@[elab_as_elim]`, which
  -- is not guaranteed across mathlib revisions.
  refine Fin.lastCases ?_ ?_ j
  · -- j = Fin.last P.numRegs
    simp only [baseFamily, Fin.lastCases_last]
    rfl
  · -- j = r.castSucc for some r : Fin P.numRegs
    intro r
    simp only [baseFamily, Fin.lastCases_castSucc]
    -- Per round-4 finding R4-S7: discharge both arms with an
    -- explicit `unfold KMor1.level; omega` rather than bare `rfl`.
    -- `rfl` plausibly succeeds via `KMor1.level`'s definitional
    -- clauses, but is fragile against future reduction-strategy
    -- changes (e.g., the field becoming `@[reducible]` rather than
    -- definitionally `0`).
    cases h : (List.finRange a).find?
        (fun i => decide (P.inputRegs i = r)) with
    | some i => unfold KMor1.level; omega
    | none => unfold KMor1.level; omega
```

- [ ] **Step 4.4: Build to verify.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: clean build.

- [ ] **Step 4.5: Axiom audit.**

```bash
bash scripts/check-axioms.sh GebLean.KSimURMSimulator.baseFamily
bash scripts/check-axioms.sh GebLean.KSimURMSimulator.baseFamily_level
```

Expected for each: `[propext, Quot.sound]` only.

- [ ] **Step 4.6: Commit Task 4.**

```bash
jj describe -m "feat(ertok): add KSimURMSimulator.baseFamily for the simrec base case

introduce baseFamily : URMProgram a → Fin (numRegs + 1) →
KMor1 a, mirroring URMState.init: PC component (Fin.last) is
KMor1.zero; register components (Fin.castSucc) use the same
List.find? lookup as URMState.init's regs field. include
baseFamily_level showing every component is at level 0. per
spec § 3.3. audit [propext, Quot.sound]-only axiom hygiene."
jj new -m ""
```

---

## Task 5: `stepFamily`

Spec § 3.4. The simrec's step family for one URM `step`:
PC component (`Fin.last numRegs`) dispatches on `P.instrs[pc]`
via `pcDispatch` and returns the new PC; each register-`j`
component (`j.castSucc`) dispatches similarly and returns the
new register value via `Function.update` semantics.

**Files:**

- Modify: `GebLean/Utilities/KSimURMSimulator.lean` (append
  inside `namespace GebLean.KSimURMSimulator`).

- [ ] **Step 5.1: Add the helper projections `I_prev` and
  `v_j_prev`.**

Insert below `baseFamily_level`:

```lean
/-- Projection at the step context's last slot: the previous
PC value. Level 0. The Fin index is pinned numerically as
`⟨a + 1 + P.numRegs, _⟩` rather than `Fin.last …` because
`Fin.last (a + P.numRegs + 1)` and `Fin (a + 1 + (P.numRegs + 1))`
may fail to unify definitionally under Lean's `Nat.add` normal
form; the explicit construction sidesteps that elaboration risk. -/
private def I_prev {a : ℕ} (P : URMProgram a) :
    KMor1 (a + 1 + (P.numRegs + 1)) :=
  KMor1.proj ⟨a + 1 + P.numRegs, by omega⟩

/-- Projection at slot `a + 1 + j.val` of the step context:
the previous value of register `j`. Level 0. -/
private def v_j_prev {a : ℕ} (P : URMProgram a)
    (j : Fin P.numRegs) :
    KMor1 (a + 1 + (P.numRegs + 1)) :=
  KMor1.proj ⟨a + 1 + j.val, by
    have := j.isLt
    omega⟩
```

- [ ] **Step 5.2: Add the per-instruction branch builders for
  the PC component.**

Insert below `v_j_prev`:

```lean
/-- The PC-component step-family branch for instruction at
PC = k. Returns the new PC value after executing the
instruction:

- `.stop` → unchanged (`I_prev`);
- `.jumpZ i l₁ l₂` → `cond` on `v_i_prev` selecting `l₁` if 0,
  else `l₂`;
- `.assign`, `.inc`, `.dec` → `I_prev + 1`.

Per round-4 finding R4-S3: enumerate all five constructors
explicitly rather than via a wildcard `_` arm, matching the
project precedent in `URMState.step`
([`GebLean/Utilities/ZeroTestURM.lean:155`](../../GebLean/Utilities/ZeroTestURM.lean#L155)).
This stabilises the definition against future `URMInstr`
extensions and aligns with the case-equation propagation
discharges in Steps 7.8 / 7.9. -/
private def branches_pc {a : ℕ} (P : URMProgram a)
    (k : Fin P.instrs.size) :
    KMor1 (a + 1 + (P.numRegs + 1)) :=
  match P.instrs[k]'k.isLt with
  | URMInstr.stop => I_prev P
  | URMInstr.jumpZ i l₁ l₂ =>
    KMor1.comp KMor1.cond
      (fun ix : Fin 3 => match ix with
        | ⟨0, _⟩ => v_j_prev P i
        | ⟨1, _⟩ => KMor1.natK' _ l₁
        | ⟨2, _⟩ => KMor1.natK' _ l₂)
  | URMInstr.assign _ _ =>
    KMor1.comp KMor1.succ (fun _ : Fin 1 => I_prev P)
  | URMInstr.inc _ =>
    KMor1.comp KMor1.succ (fun _ : Fin 1 => I_prev P)
  | URMInstr.dec _ =>
    KMor1.comp KMor1.succ (fun _ : Fin 1 => I_prev P)
```

- [ ] **Step 5.3: Add the per-instruction branch builders for
  the register-`j` component.**

Insert below `branches_pc`:

```lean
/-- The register-`j`-component step-family branch for
instruction at PC = k. Returns the new register-`j` value
after executing the instruction:

- `.assign i c` if `i = j` → `c`; else `v_j_prev`.
- `.inc i` if `i = j` → `v_j_prev + 1`; else `v_j_prev`.
- `.dec i` if `i = j` → `pred v_j_prev`; else `v_j_prev`.
- `.jumpZ`, `.stop` → `v_j_prev` (registers unchanged). -/
private def branches_j {a : ℕ} (P : URMProgram a)
    (j : Fin P.numRegs) (k : Fin P.instrs.size) :
    KMor1 (a + 1 + (P.numRegs + 1)) :=
  match P.instrs[k]'k.isLt with
  | URMInstr.assign i c =>
    if i.val = j.val then KMor1.natK' _ c else v_j_prev P j
  | URMInstr.inc i =>
    if i.val = j.val then
      KMor1.comp KMor1.succ (fun _ : Fin 1 => v_j_prev P j)
    else v_j_prev P j
  | URMInstr.dec i =>
    if i.val = j.val then
      KMor1.comp KMor1.pred (fun _ : Fin 1 => v_j_prev P j)
    else v_j_prev P j
  | URMInstr.jumpZ _ _ _ => v_j_prev P j
  | URMInstr.stop => v_j_prev P j
```

- [ ] **Step 5.4: Add `stepFamily` definition.**

Insert below `branches_j`:

```lean
/-- The step family for `simulate`'s simrec. By `Fin.lastCases`:
the `Fin.last` case is the PC component (dispatched via
`pcDispatch` over `branches_pc` with `default_pc := I_prev`);
the `castSucc` case is a register-`j` component (dispatched via
`pcDispatch` over `branches_j j` with `default_j := v_j_prev`).
Each branch is at level ≤ 1 by inspection (cond, pred are
level 1; succ, proj, natK' are level 0); the dispatcher's
`pcDispatch_level` gives `stepFamily P i` at level ≤ 1.

Per spec § 3.4. -/
def stepFamily {a : ℕ} (P : URMProgram a) :
    Fin (P.numRegs + 1) → KMor1 (a + 1 + (P.numRegs + 1)) :=
  Fin.lastCases
    -- PC component
    (KMor1.pcDispatch P.instrs.size
      (fun k => branches_pc P k)
      (I_prev P))
    -- Register-j component
    (fun j : Fin P.numRegs =>
      KMor1.pcDispatch P.instrs.size
        (fun k => branches_j P j k)
        (v_j_prev P j))
```

- [ ] **Step 5.5: Build to verify.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: clean build.

- [ ] **Step 5.6: Add a level lemma for the step family.**

Insert below `stepFamily`:

```lean
/-- Every step-family component is at level ≤ 1. Each branch
and the default are at level ≤ 1 by inspection; the dispatcher's
`KMor1.pcDispatch_level` gives the result. -/
theorem stepFamily_level {a : ℕ} (P : URMProgram a)
    (j : Fin (P.numRegs + 1)) :
    (stepFamily P j).level ≤ 1 := by
  -- Project-idiomatic Fin.lastCases case-split (per
  -- GebLean/LawvereBTInterp.lean:625, 627, 637, 668, 669): use
  -- `refine Fin.lastCases ?_ ?_ j`, not `induction j using
  -- Fin.lastCases with | last | cast` (per R3-S4).
  refine Fin.lastCases ?_ ?_ j
  · -- j = Fin.last P.numRegs
    simp only [stepFamily, Fin.lastCases_last]
    apply KMor1.pcDispatch_level
    · intro k
      -- Each branches_pc k is level ≤ 1. One explicit cases per
      -- URMInstr constructor, closed via the
      -- `unfold KMor1.level` + `Finset.sup_le` + `omega` pattern
      -- (per plan round-2 finding R2-S5: `simp` with constructor
      -- arguments is not deterministic).
      unfold branches_pc
      cases hi : P.instrs[k]'k.isLt with
      | assign i c =>
        -- Returns `comp succ (fun _ => I_prev P)`. level = max 0 0 = 0.
        show KMor1.level
            (KMor1.comp KMor1.succ (fun _ : Fin 1 => I_prev P)) ≤ 1
        unfold KMor1.level I_prev
        have hsup :
            Finset.univ.sup (fun _ : Fin 1 =>
              (KMor1.proj (⟨a + 1 + P.numRegs, by omega⟩ :
                  Fin (a + 1 + (P.numRegs + 1)))).level) ≤ 1 := by
          apply Finset.sup_le; intro _ _; exact Nat.zero_le _
        omega
      | inc i =>
        show KMor1.level
            (KMor1.comp KMor1.succ (fun _ : Fin 1 => I_prev P)) ≤ 1
        unfold KMor1.level I_prev
        have hsup :
            Finset.univ.sup (fun _ : Fin 1 =>
              (KMor1.proj (⟨a + 1 + P.numRegs, by omega⟩ :
                  Fin (a + 1 + (P.numRegs + 1)))).level) ≤ 1 := by
          apply Finset.sup_le; intro _ _; exact Nat.zero_le _
        omega
      | dec i =>
        show KMor1.level
            (KMor1.comp KMor1.succ (fun _ : Fin 1 => I_prev P)) ≤ 1
        unfold KMor1.level I_prev
        have hsup :
            Finset.univ.sup (fun _ : Fin 1 =>
              (KMor1.proj (⟨a + 1 + P.numRegs, by omega⟩ :
                  Fin (a + 1 + (P.numRegs + 1)))).level) ≤ 1 := by
          apply Finset.sup_le; intro _ _; exact Nat.zero_le _
        omega
      | jumpZ i l₁ l₂ =>
        -- Returns `comp cond [v_j_prev P i, natK' _ l₁, natK' _ l₂]`.
        -- level = max cond.level (sup …) = max 1 0 = 1.
        show KMor1.level
            (KMor1.comp KMor1.cond
              (fun ix : Fin 3 => match ix with
                | ⟨0, _⟩ => v_j_prev P i
                | ⟨1, _⟩ => KMor1.natK' _ l₁
                | ⟨2, _⟩ => KMor1.natK' _ l₂)) ≤ 1
        unfold KMor1.level
        have hcond : (KMor1.cond : KMor1 3).level = 1 := by decide
        have hsup :
            Finset.univ.sup (fun ix : Fin 3 =>
              (match ix with
                | ⟨0, _⟩ => v_j_prev P i
                | ⟨1, _⟩ => KMor1.natK' _ l₁
                | ⟨2, _⟩ => KMor1.natK' _ l₂).level) ≤ 1 := by
          apply Finset.sup_le; intro ix _
          match ix with
          | ⟨0, _⟩ => unfold v_j_prev KMor1.level; omega
          | ⟨1, _⟩ => rw [KMor1.natK'_level]; omega
          | ⟨2, _⟩ => rw [KMor1.natK'_level]; omega
        rw [hcond]; omega
      | stop =>
        -- Returns `I_prev P`; level = 0.
        unfold I_prev KMor1.level; omega
    · -- default = I_prev (level 0).
      unfold I_prev KMor1.level; omega
  · -- j = r.castSucc for some r : Fin P.numRegs
    intro r
    simp only [stepFamily, Fin.lastCases_castSucc]
    apply KMor1.pcDispatch_level
    · intro k
      unfold branches_j
      cases hi : P.instrs[k]'k.isLt with
      | assign i c =>
        by_cases h : i.val = r.val
        · -- Branch returns `natK' _ c`; level = 0 by natK'_level.
          rw [if_pos h, KMor1.natK'_level]; omega
        · -- Branch returns `v_j_prev P r`; level = 0 by proj.
          rw [if_neg h]
          unfold v_j_prev KMor1.level; omega
      | inc i =>
        by_cases h : i.val = r.val
        · -- branch returns `comp succ (fun _ => v_j_prev P r)`.
          -- level = max succ.level (sup of singleton family) = max 0 0 = 0.
          rw [if_pos h]
          show KMor1.level
              (KMor1.comp KMor1.succ
                (fun _ : Fin 1 => v_j_prev P r)) ≤ 1
          unfold KMor1.level v_j_prev
          have hsup :
              Finset.univ.sup (fun _ : Fin 1 =>
                (KMor1.proj (⟨a + 1 + r.val, by omega⟩ :
                    Fin (a + 1 + (P.numRegs + 1)))).level) ≤ 1 := by
            apply Finset.sup_le; intro _ _; exact Nat.zero_le _
          omega
        · rw [if_neg h]
          unfold v_j_prev KMor1.level; omega
      | dec i =>
        by_cases h : i.val = r.val
        · -- branch returns `comp pred (fun _ => v_j_prev P r)`.
          -- level = max pred.level (sup of singleton family) = max 1 0 = 1.
          rw [if_pos h]
          show KMor1.level
              (KMor1.comp KMor1.pred
                (fun _ : Fin 1 => v_j_prev P r)) ≤ 1
          unfold KMor1.level v_j_prev
          have hsup :
              Finset.univ.sup (fun _ : Fin 1 =>
                (KMor1.proj (⟨a + 1 + r.val, by omega⟩ :
                    Fin (a + 1 + (P.numRegs + 1)))).level) ≤ 1 := by
            apply Finset.sup_le; intro _ _; exact Nat.zero_le _
          omega
        · rw [if_neg h]
          unfold v_j_prev KMor1.level; omega
      | jumpZ i l₁ l₂ =>
        -- Returns `v_j_prev P r`; level = 0.
        unfold v_j_prev KMor1.level; omega
      | stop =>
        unfold v_j_prev KMor1.level; omega
    · -- default = v_j_prev P r; level = 0.
      unfold v_j_prev KMor1.level; omega
```

Note: the explicit per-constructor `cases hi : P.instrs[k]`
discharge sidesteps the `split <;> split <;> simp <;> decide`
brittleness flagged in plan round 1. Each per-instruction block
is ~3 – 5 LOC; total ~40 LOC for `branches_pc` and ~50 LOC for
`branches_j`. Inspect each goal state via
`mcp__lean-lsp__lean_goal` if `decide` or `omega` does not close.

- [ ] **Step 5.7: Build to verify.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: clean build.

- [ ] **Step 5.8: Axiom audit.**

```bash
bash scripts/check-axioms.sh GebLean.KSimURMSimulator.stepFamily
bash scripts/check-axioms.sh GebLean.KSimURMSimulator.stepFamily_level
```

Expected for each: `[propext, Quot.sound]` only.

- [ ] **Step 5.9: Commit Task 5.**

```bash
jj describe -m "feat(ertok): add KSimURMSimulator.stepFamily for the simrec step case

introduce stepFamily : URMProgram a → Fin (numRegs + 1) →
KMor1 (a + 1 + (numRegs + 1)) plus private helper projections
I_prev, v_j_prev and per-instruction branch builders
branches_pc, branches_j. PC component dispatches via
pcDispatch over branches_pc with default_pc := I_prev;
register components dispatch via pcDispatch over branches_j j
with default_j := v_j_prev. include stepFamily_level showing
every component is at level ≤ 1. per spec § 3.4.
audit [propext, Quot.sound]-only axiom hygiene."
jj new -m ""
```

---

## Task 6: `simulate` assembly

Spec § 3.1, § 3.2. Bundle `baseFamily` and `stepFamily` into a
single `KMor1.simrec` term with output index
`P.outputReg.castSucc`.

**Files:**

- Modify: `GebLean/Utilities/KSimURMSimulator.lean` (append
  inside `namespace GebLean.KSimURMSimulator`).

- [ ] **Step 6.1: Add `simulate` definition.**

Insert below `stepFamily_level`:

```lean
/-- The K^sim simulator for a URMProgram: a single
`KMor1.simrec` with system size `P.numRegs + 1` (registers at
indices `0..numRegs - 1`, PC at index `numRegs`), base family
`baseFamily P`, step family `stepFamily P`, and output index
`P.outputReg.castSucc`. Returns a morphism of arity `a + 1`:
slot 0 carries the time bound `y`, slots `1..a` carry the
input vector.

Per spec § 3.1, § 3.2. -/
def simulate {a : ℕ} (P : URMProgram a) : KMor1 (a + 1) :=
  KMor1.simrec (a := a) (k := P.numRegs)
    (i := P.outputReg.castSucc)
    (baseFamily P)
    (stepFamily P)
```

- [ ] **Step 6.2: Build to verify.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: clean build.

- [ ] **Step 6.3: Axiom audit.**

```bash
bash scripts/check-axioms.sh GebLean.KSimURMSimulator.simulate
```

Expected: `[propext, Quot.sound]` only.

- [ ] **Step 6.4: Commit Task 6.**

```bash
jj describe -m "feat(ertok): add KSimURMSimulator.simulate top-level assembly

introduce simulate : URMProgram a → KMor1 (a + 1) as a single
KMor1.simrec with system size P.numRegs + 1 (registers at
indices 0..numRegs - 1, PC at index numRegs), base family
baseFamily P, step family stepFamily P, output index
P.outputReg.castSucc. per spec § 3.1, § 3.2.
audit [propext, Quot.sound]-only axiom hygiene."
jj new -m ""
```

---

## Task 7: `simulate_step_match` conjunctive induction

Spec § 4.2, § 4.3. The conjunctive vector invariant: for every
`y : ℕ`, `simrecVec (baseFamily P) (stepFamily P) v y` agrees
component-by-component with `(URMState.init P v).runFor y`'s PC
and registers. Proof by induction on `y`, case-by-case on the
instruction at `(runFor y).pc` in the step case.

**Files:**

- Modify: `GebLean/Utilities/KSimURMSimulator.lean` (append
  inside `namespace GebLean.KSimURMSimulator`).

- [ ] **Step 7.1: Add the back-peel reduction lemma for
  `runFor`.**

Insert below `simulate`:

```lean
/-- Back-peel reduction for `URMState.runFor`: derived from the
front-peel `runFor_succ` (`ZeroTestURM.lean:192`) and additivity
`runFor_add` (`:199`). Inside the helper-lemma scope the `s`
parameter is fully general — the helper itself does not hit the
fixed-`s := init P v` trap. Only the consumer
(`simulate_step_match`'s step case) is locked to that specific
`s`, which is why `runFor_succ` (front-peel, `@[simp]`) is
wrong-directional there and this back-peel form must be
invoked explicitly. Placed directly under
`namespace GebLean.KSimURMSimulator` (no `URMState`
sub-namespace) so the fully qualified name is
`GebLean.KSimURMSimulator.runFor_succ_init_back`, avoiding
confusing parallelism with `GebLean.ZeroTestURM.URMState`. Per
spec § 4.3. -/
private theorem runFor_succ_init_back {a : ℕ}
    (P : URMProgram a) (s : URMState P) (y : ℕ) :
    URMState.runFor P s (y + 1)
      = URMState.step P (URMState.runFor P s y) := by
  -- runFor s (y + 1) = runFor (runFor s y) 1 (by runFor_add)
  --                  = step (runFor s y)     (by runFor_succ at n = 0)
  -- The rewrite chain pins each rewrite to a specific subterm via
  -- explicit arguments, avoiding the round-2-flagged
  -- generic-`y`-rewrite-site ambiguity that `rw` would otherwise
  -- expose if multiple `runFor _ (· + 1)` patterns exist in the
  -- goal for arbitrary `y`.
  rw [URMState.runFor_add P s y 1]
  rw [URMState.runFor_succ P (URMState.runFor P s y) 0]
  rw [URMState.runFor_zero]
```

- [ ] **Step 7.1.5: Add the dispatcher-context evaluation
  helper.**

Per round-4 findings R4-B2, R4-S6, and R4-M3: the `simrecVec_succ`
-produced dispatcher context evaluated at any slot in the
"previous-component" range (`a + 1 ≤ slot < a + 1 + (P.numRegs + 1)`)
reduces to the previous simrec component at the residue index
`slot - (a + 1)`. This single helper replaces the three inline
`dite`-reduction derivations that round 3 produced (one for
`h_ctx_last_pc` and one for `h_ctx_ge` in each of Steps 7.8
and 7.9), and supplies the per-register-component bridging
that round 3 left implicit in Step 7.9's `.jumpZ` and `.stop`
discharges.

Insert below `runFor_succ_init_back`:

```lean
/-- The `simrecVec_succ`-produced dispatcher context, evaluated
at any slot in the "previous-component" range
(`a + 1 ≤ slot < a + 1 + (P.numRegs + 1)`), equals the previous
simrec component at the residue index `slot - (a + 1)`. Used
across both the PC and the register-`j` components in the step
case of `simulate_step_match`. Per round-4 findings R4-B2,
R4-S6, R4-M3.

This helper is the sole site in T3 that couples directly to
`KMor1.simrecVec_succ`'s `dite`-form context shape
(`LawvereKSimInterp.lean:193 – 209`). If that lemma's shape
changes (for example, the inner
`if h₂ : idx.val = 0 then n else params ⟨…⟩` becomes a
`match`), the body's `show` will need to be re-stated to match
the new form. All call sites consume the helper through its
declared signature only — per plan round-6 serious finding R6-S1. -/
private lemma step_ctx_eval_simrec {a : ℕ} (P : URMProgram a)
    (v : Fin a → ℕ) (y : ℕ)
    (slot : ℕ) (h_slot_bound : slot < a + 1 + (P.numRegs + 1))
    (h_slot_ge : a + 1 ≤ slot) :
    (fun idx : Fin (a + 1 + (P.numRegs + 1)) =>
       if h₁ : idx.val < a + 1 then
         if h₂ : idx.val = 0 then (y : ℕ)
         else v ⟨idx.val - 1, by omega⟩
       else
         KMor1.simrecVec (baseFamily P) (stepFamily P) v y
           ⟨idx.val - (a + 1), by omega⟩)
        ⟨slot, h_slot_bound⟩
    = KMor1.simrecVec (baseFamily P) (stepFamily P) v y
        ⟨slot - (a + 1), by omega⟩ := by
  show (if h₁ : slot < a + 1 then _ else
          KMor1.simrecVec (baseFamily P) (stepFamily P) v y
            ⟨slot - (a + 1), by omega⟩) = _
  rw [dif_neg (by omega)]
```

- [ ] **Step 7.2: Add `simulate_step_match` declaration with
  `by sorry` body.**

Insert below `step_ctx_eval_simrec`:

```lean
/-- The conjunctive vector invariant: at every time `y`, the
simrec state vector at each component matches the URM state's
corresponding field. The PC component is at index
`Fin.last P.numRegs`; each register-`j` component is at index
`j.castSucc` (for `j : Fin P.numRegs`).

Per spec § 4.2. -/
private theorem simulate_step_match {a : ℕ}
    (P : URMProgram a) (v : Fin a → ℕ) (y : ℕ) :
    KMor1.simrecVec (baseFamily P) (stepFamily P) v y
        (Fin.last P.numRegs)
      = ((URMState.init P v).runFor P y).pc
    ∧ ∀ j : Fin P.numRegs,
        KMor1.simrecVec (baseFamily P) (stepFamily P) v y
            j.castSucc
          = ((URMState.init P v).runFor P y).regs j := by
  sorry
```

- [ ] **Step 7.3: Build to verify the signature type-checks.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: build succeeds with a `sorry` warning. The signature
is type-correct.

- [ ] **Step 7.4: Fill the base case `y = 0`.**

Replace the `sorry` body with:

```lean
  induction y with
  | zero =>
    refine ⟨?_, ?_⟩
    · -- PC component at y = 0.
      simp only [KMor1.simrecVec_zero, baseFamily,
        Fin.lastCases_last, KMor1.interp_zero]
      -- (URMState.runFor P (URMState.init P v) 0).pc
      --   = (URMState.init P v).pc = 0.
      rw [URMState.runFor_zero]
      -- Per round-4 finding R4-S4: `(URMState.init P v).pc = 0` is
      -- a structure-projection identity, but the projection
      -- reduction does not always fire automatically against the
      -- LHS shape `0`. Explicitly unfold `URMState.init` to expose
      -- the `pc := 0` field before closing with `rfl`.
      show (0 : ℕ) = (URMState.init P v).pc
      unfold URMState.init
    · -- Register components at y = 0.
      intro j
      simp only [KMor1.simrecVec_zero, baseFamily,
        Fin.lastCases_castSucc]
      rw [URMState.runFor_zero]
      -- baseFamily P j.castSucc unfolds to the match on
      -- List.find?; URMState.init's regs field unfolds to the
      -- same match. Case-split on the find?-result. Per project
      -- memory `feedback_urmstate_init_let_reduction.md`, the
      -- `URMState.init` projection reduction is unreliable through
      -- `simp only [URMState.init, h]` alone — use an explicit
      -- `show … = (URMState.init P v).regs j; unfold URMState.init;
      -- simp only [h]; rfl` reduction (round-2 finding R2-S6).
      cases h : (List.finRange a).find?
          (fun i => decide (P.inputRegs i = j)) with
      | some i =>
        simp only [KMor1.interp_proj]
        show v i = (URMState.init P v).regs j
        unfold URMState.init
        simp only [h]
      | none =>
        simp only [KMor1.interp_zero]
        show (0 : ℕ) = (URMState.init P v).regs j
        unfold URMState.init
        simp only [h]
  | succ y ih => sorry  -- replace in step 7.6
```

- [ ] **Step 7.5: Build to verify the base case.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: build with one `sorry` warning (the succ case).

- [ ] **Step 7.6: Begin the succ case structure.**

Replace the `| succ y ih => sorry` line with:

```lean
  | succ y ih =>
    obtain ⟨ih_pc, ih_regs⟩ := ih
    -- URM side: peel via back-peel reduction.
    rw [runFor_succ_init_back]
    -- K^sim side: peel via simrecVec_succ.
    refine ⟨?_, ?_⟩
    · -- PC component at y + 1.
      rw [KMor1.simrecVec_succ]
      -- Now reduce the step-family PC component over the
      -- previous-iteration vector, which by ih matches the URM
      -- state at y.
      sorry  -- replace in step 7.8
    · -- Register-j component at y + 1.
      intro j
      rw [KMor1.simrecVec_succ]
      sorry  -- replace in step 7.9
```

- [ ] **Step 7.7: Intermediate build to verify the succ-case
  skeleton.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: build with exactly two `sorry` warnings (one per
branch of the conjunctive `refine ⟨?_, ?_⟩`). The structural
skeleton type-checks; the two open sub-goals are the PC and
register-`j` step cases, addressed in Steps 7.8 and 7.9.
This intermediate build (per plan round-2 finding R2-S7)
verifies the succ-case structure before the substantive
case-analysis work; if the build fails here, fix the
structural skeleton before proceeding to the case fills.

- [ ] **Step 7.8: Fill the PC step case.**

Replace the first `sorry` (the PC component) with a case-split
on the instruction at `(runFor y).pc`. Use
`mcp__lean-lsp__lean_goal` to inspect the goal shape; the
structure is:

```lean
      -- Set up the step context shape.
      simp only [stepFamily, Fin.lastCases_last]
      -- Bridging hypothesis (per plan round-2 finding R2-B1): the
      -- dispatcher's interpretation context is the `dite`-form
      -- produced by `KMor1.simrecVec_succ` at
      -- `LawvereKSimInterp.lean:193 – 209` (NOT a `Fin.cons` of two
      -- arguments). Compute its last-slot value once and reuse
      -- across the in-bounds / past-end branches. Per round-4
      -- findings R4-B2 / R4-M3: derive the reduction from the
      -- shared helper `step_ctx_eval_simrec` rather than re-deriving
      -- the `dite`-reduction inline.
      have h_ctx_last_pc :
          (fun idx : Fin (a + 1 + (P.numRegs + 1)) =>
            if h₁ : idx.val < a + 1 then
              if h₂ : idx.val = 0 then (y : ℕ)
              else v ⟨idx.val - 1, by omega⟩
            else
              KMor1.simrecVec (baseFamily P) (stepFamily P) v y
                ⟨idx.val - (a + 1), by omega⟩)
              (Fin.last (a + P.numRegs + 1))
            = ((URMState.init P v).runFor P y).pc := by
        -- `Fin.last (a + P.numRegs + 1) = ⟨a + P.numRegs + 1, _⟩`
        -- by `Fin.ext`; apply the helper at `slot := a + P.numRegs + 1`.
        rw [show (Fin.last (a + P.numRegs + 1)
                : Fin (a + 1 + (P.numRegs + 1)))
              = ⟨a + P.numRegs + 1, by omega⟩
              from by apply Fin.ext; simp [Fin.last]]
        rw [step_ctx_eval_simrec P v y (a + P.numRegs + 1)
              (by omega) (by omega)]
        rw [show (⟨a + P.numRegs + 1 - (a + 1), by omega⟩
                : Fin (P.numRegs + 1))
              = Fin.last P.numRegs
              from by apply Fin.ext; simp [Fin.last]; omega]
        exact ih_pc
      -- The dispatcher's match-vs-default split.
      by_cases h_inbounds :
          ((URMState.init P v).runFor P y).pc < P.instrs.size
      · -- In-bounds: pcDispatch_match fires at k = (runFor y).pc.
        -- Per round-4 blocker R4-B1: mathlib's `set ... with hpc`
        -- already runs `rewrite [show vale = a from rfl] at *`
        -- (`Mathlib/Tactic/Set.lean:30 – 31`), substituting in all
        -- hypotheses including `h_ctx_last_pc`. No subsequent
        -- `rw [← hpc] at h_ctx_last_pc` is needed (the round-3 fix
        -- that added that rewrite was built on an incorrect premise).
        set pcVal := ((URMState.init P v).runFor P y).pc with hpc
        -- Apply pcDispatch_match with the bridged hypothesis.
        rw [KMor1.interp_pcDispatch_match P.instrs.size
              (fun k => branches_pc P k) (I_prev P) _
              ⟨pcVal, h_inbounds⟩ h_ctx_last_pc]
        -- Case-split on the instruction at pcVal. Per round-4
        -- serious finding R4-S1: `simp only [branches_pc, h_instr]`
        -- may fail to rewrite past the bound-proof-object
        -- difference between `h_inbounds` and
        -- `⟨pcVal, h_inbounds⟩.isLt` (the inner-match subject after
        -- `branches_pc` unfolds). The likely path of `simp only` is
        -- successful via `GetElem.getElem`'s proof-irrelevance, but
        -- if it fails, the fallback is `subst h_instr` (if
        -- substitution is permitted, i.e., the cased expression is
        -- a local variable) or the explicit
        -- `generalize h_instr : P.instrs[⟨pcVal, h_inbounds⟩.val]'_
        -- = ins; cases ins with …` pattern.
        --
        -- Per round-4 serious finding R4-S5: the `dif_pos h_inbounds`
        -- application is split out of the `simp only` invocation
        -- (using a separate `rw` step) to defend against the
        -- documented `simp only [if_pos h] / [dif_pos h]` sorryAx
        -- leakage pattern (project memory
        -- `feedback_simp_if_pos_sorryAx_leak.md`). The sequence is:
        -- `simp only [URMState.step]` to expose the `dite`, then
        -- `rw [dif_pos h_inbounds]` to select the in-bounds branch,
        -- then `simp only [h_instr]` to push the instruction
        -- case-equation through the inner match.
        --
        -- Per round-4 blocker R4-B2: the closing `rw [h_ctx_last_pc]`
        -- of round 3 cannot fire because `h_ctx_last_pc`'s LHS uses
        -- `Fin.last (a + P.numRegs + 1)` whereas the post-`simp`
        -- goal has `⟨a + 1 + P.numRegs, _⟩` (from `I_prev`'s
        -- deliberate explicit-index construction). Close via the
        -- shared helper `step_ctx_eval_simrec` plus a `Fin.ext`
        -- bridge to `Fin.last P.numRegs`, then `exact ih_pc`.
        cases h_instr : P.instrs[pcVal]'h_inbounds with
        | assign i c =>
          -- branches_pc returns succ ∘ I_prev (PC + 1).
          simp only [branches_pc, h_instr, KMor1.interp_comp,
            KMor1.interp_succ, I_prev, KMor1.interp_proj]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          simp only [h_instr]
          rw [step_ctx_eval_simrec P v y (a + 1 + P.numRegs)
                (by omega) (by omega)]
          rw [show (⟨a + 1 + P.numRegs - (a + 1), by omega⟩
                  : Fin (P.numRegs + 1))
                = Fin.last P.numRegs
                from by apply Fin.ext; simp [Fin.last]; omega]
          -- Per round-5 blocker R5-B1: both sides carry a trailing
          -- `+ 1`; `ih_pc` lacks it. Rewriting under the `+ 1`
          -- closes via the implicit `rfl`.
          rw [ih_pc]
        | inc i =>
          simp only [branches_pc, h_instr, KMor1.interp_comp,
            KMor1.interp_succ, I_prev, KMor1.interp_proj]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          simp only [h_instr]
          rw [step_ctx_eval_simrec P v y (a + 1 + P.numRegs)
                (by omega) (by omega)]
          rw [show (⟨a + 1 + P.numRegs - (a + 1), by omega⟩
                  : Fin (P.numRegs + 1))
                = Fin.last P.numRegs
                from by apply Fin.ext; simp [Fin.last]; omega]
          -- Per round-5 blocker R5-B1: see `.assign` comment above.
          rw [ih_pc]
        | dec i =>
          simp only [branches_pc, h_instr, KMor1.interp_comp,
            KMor1.interp_succ, I_prev, KMor1.interp_proj]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          simp only [h_instr]
          rw [step_ctx_eval_simrec P v y (a + 1 + P.numRegs)
                (by omega) (by omega)]
          rw [show (⟨a + 1 + P.numRegs - (a + 1), by omega⟩
                  : Fin (P.numRegs + 1))
                = Fin.last P.numRegs
                from by apply Fin.ext; simp [Fin.last]; omega]
          -- Per round-5 blocker R5-B1: see `.assign` comment above.
          rw [ih_pc]
        | jumpZ i l₁ l₂ =>
          simp only [branches_pc, h_instr, KMor1.interp_comp,
            KMor1.interp_cond, v_j_prev, KMor1.interp_proj,
            KMor1.interp_natK']
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          simp only [h_instr]
          -- URM side: pc := if regs i = 0 then l₁ else l₂.
          -- K^sim side: cond on v_i_prev (= regs i by ih_regs i).
          -- Per plan round-6 blocker R6-B1: the K-side's
          -- `v_i_prev` projection reads the dispatcher's
          -- `dite`-ctx at slot `a + 1 + i.val`; bridge to
          -- `simrecVec _ _ y i.castSucc` via `step_ctx_eval_simrec`
          -- + `Fin.ext`, mirroring Step 7.9's `.jumpZ` block.
          -- Without this bridge `rw [ih_regs i]` cannot find an
          -- instance of its LHS pattern in the goal.
          rw [step_ctx_eval_simrec P v y (a + 1 + i.val) (by omega)
              (by omega)]
          rw [show (⟨a + 1 + i.val - (a + 1), by omega⟩
                : Fin (P.numRegs + 1)) = i.castSucc
                from by apply Fin.ext; simp [Fin.castSucc]; omega]
          rw [ih_regs i]
          -- Match the if-then-else shape on both sides. Per round-4
          -- serious finding R4-S2: replace bare `simp` / `simp [h_zero]`
          -- with a `simp only` whitelist to avoid pulling in the
          -- entire default simp set (which on goals involving
          -- `Fin.cons`, propositional `if`, and `Decidable`
          -- instances can route through `Classical.choice`, per
          -- project memory `feedback_mathlib_choice_in_functor_cat.md`).
          -- The closing simp set is enumerated below; if at
          -- execution any one of these names is missing or the
          -- goal shape diverges, use `mcp__lean-lsp__lean_goal` to
          -- inspect and extend the whitelist (do NOT fall back to
          -- bare `simp`).
          -- Per round-5 serious finding R5-S1: replace the prior
          -- whitelist containing `Fin.cons_zero` / `Fin.cons_succ`
          -- (which do not fire on the literal Fin 3 match arms
          -- produced by `KMor1.interp_cond`) with a defensive form
          -- that first unfolds `KMor1.interp_cond` and then
          -- discharges the resulting `if`-`then`-`else` via
          -- `if_pos h_zero` / `if_neg h_zero`. If at execution
          -- `KMor1.interp_cond` produces a different shape
          -- (e.g. `Fin.cases` or `Decidable.rec`), extend the
          -- whitelist accordingly per `mcp__lean-lsp__lean_goal`.
          -- Per plan round-7 serious finding R7-S2: the
          -- `simp only [KMor1.interp_natK']` invocation in the
          -- first simp only chain above already reduces
          -- `natK' …` occurrences; further invocations after
          -- the `by_cases` split are operationally noops and
          -- emit `Simp made no progress`. Close via implicit
          -- `rfl` after the `if_pos` / `if_neg` rewrite.
          by_cases h_zero : ((URMState.init P v).runFor P y).regs i = 0
          · simp only [KMor1.interp_cond]
            rw [if_pos h_zero]
          · simp only [KMor1.interp_cond]
            rw [if_neg h_zero]
        | stop =>
          simp only [branches_pc, h_instr, I_prev, KMor1.interp_proj]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          simp only [h_instr]
          -- Per round-4 blocker R4-B2 and minor R4-M1: bridge the
          -- `⟨a + 1 + P.numRegs, _⟩` form to `Fin.last P.numRegs`
          -- via the shared helper.
          rw [step_ctx_eval_simrec P v y (a + 1 + P.numRegs)
                (by omega) (by omega)]
          rw [show (⟨a + 1 + P.numRegs - (a + 1), by omega⟩
                  : Fin (P.numRegs + 1))
                = Fin.last P.numRegs
                from by apply Fin.ext; simp [Fin.last]; omega]
          exact ih_pc
      · -- Past-end: pcDispatch_default fires.
        push_neg at h_inbounds
        -- Lift the in-bounds hypothesis to the dispatcher's ge form
        -- via the bridged `h_ctx_last_pc`.
        have h_ctx_ge :
            (fun idx : Fin (a + 1 + (P.numRegs + 1)) =>
              if h₁ : idx.val < a + 1 then
                if h₂ : idx.val = 0 then (y : ℕ)
                else v ⟨idx.val - 1, by omega⟩
              else
                KMor1.simrecVec (baseFamily P) (stepFamily P) v y
                  ⟨idx.val - (a + 1), by omega⟩)
                (Fin.last (a + P.numRegs + 1))
              ≥ P.instrs.size := by
          rw [h_ctx_last_pc]; exact h_inbounds
        rw [KMor1.interp_pcDispatch_default P.instrs.size
              (fun k => branches_pc P k) (I_prev P) _ h_ctx_ge]
        simp only [I_prev, KMor1.interp_proj]
        -- URM side: step returns s unchanged.
        unfold URMState.step
        rw [dif_neg (Nat.not_lt_of_ge h_inbounds)]
        exact ih_pc
```

Note: the `h_ctx_last_pc` and `h_ctx_ge` `have` statements
(per R2-B1) supply `pcDispatch_match`'s and `pcDispatch_default`'s
context-slot hypotheses by reducing the `dite`-form context
produced by `simrecVec_succ` (LawvereKSimInterp.lean:193 – 209)
via the shared helper `step_ctx_eval_simrec` (added in Step 7.1.5
per round-4 findings R4-B2 / R4-M3) plus a `Fin.ext`-bridge to
`Fin.last P.numRegs`, then chaining with `ih_pc`. Use
`mcp__lean-lsp__lean_goal` at each `rw` invocation to verify the
exact step context shape and adjust if the elaborator displays it
in a different but equivalent form.

- [ ] **Step 7.9: Fill the register-`j` step case.**

Replace the second `sorry` (the register-`j` component) with the
following six-block structure mirroring Step 7.8 (one block per
`URMInstr` constructor plus past-end). The per-instruction
discriminator is `by_cases h_eq : i.val = j.val`, matching
`branches_j`'s shape and `Function.update`'s equality semantics
on the URM side. The shared helper `step_ctx_eval_simrec`
(Step 7.1.5) supplies both the `h_ctx_last_pc` reduction and the
per-register-component bridging at `slot := a + 1 + j.val` (per
round-4 findings R4-B2, R4-S6, R4-M3). The `set` /
no-`rw [← hpc]` and split `simp` / `rw [dif_pos]` patterns
mirror Step 7.8 (R4-B1 and R4-S5 respectively). Use
`mcp__lean-lsp__lean_goal` at each subcase to confirm goal
shape; the structure is fixed but the final `rfl` discharges
may need minor argument adjustments.

```lean
      -- Set up the step context shape (mirrors Step 7.8).
      simp only [stepFamily, Fin.lastCases_castSucc]
      -- Bridging hypothesis: same dite-form last-slot reduction as
      -- in Step 7.8 (per R2-B1, R4-B2). Re-derived rather than
      -- shared via a `have` outside the refine because the two
      -- refine branches live in independent tactic scopes; the
      -- shared computation lives in `step_ctx_eval_simrec`.
      have h_ctx_last_pc :
          (fun idx : Fin (a + 1 + (P.numRegs + 1)) =>
            if h₁ : idx.val < a + 1 then
              if h₂ : idx.val = 0 then (y : ℕ)
              else v ⟨idx.val - 1, by omega⟩
            else
              KMor1.simrecVec (baseFamily P) (stepFamily P) v y
                ⟨idx.val - (a + 1), by omega⟩)
              (Fin.last (a + P.numRegs + 1))
            = ((URMState.init P v).runFor P y).pc := by
        rw [show (Fin.last (a + P.numRegs + 1)
                : Fin (a + 1 + (P.numRegs + 1)))
              = ⟨a + P.numRegs + 1, by omega⟩
              from by apply Fin.ext; simp [Fin.last]]
        rw [step_ctx_eval_simrec P v y (a + P.numRegs + 1)
              (by omega) (by omega)]
        rw [show (⟨a + P.numRegs + 1 - (a + 1), by omega⟩
                : Fin (P.numRegs + 1))
              = Fin.last P.numRegs
              from by apply Fin.ext; simp [Fin.last]; omega]
        exact ih_pc
      by_cases h_inbounds :
          ((URMState.init P v).runFor P y).pc < P.instrs.size
      · -- In-bounds: pcDispatch_match fires at k = (runFor y).pc.
        -- Per round-4 blocker R4-B1: `set ... with hpc` already
        -- substitutes in all hypotheses, so no `rw [← hpc] at
        -- h_ctx_last_pc` is needed.
        set pcVal := ((URMState.init P v).runFor P y).pc with hpc
        rw [KMor1.interp_pcDispatch_match P.instrs.size
              (fun k => branches_j P j k) (v_j_prev P j) _
              ⟨pcVal, h_inbounds⟩ h_ctx_last_pc]
        cases h_instr : P.instrs[pcVal]'h_inbounds with
        | assign i c =>
          -- Per R3-S2 / R4-S1: propagate `h_instr` through both
          -- the K^sim match (inside `branches_j`) and the URM
          -- match (inside `URMState.step`) via `simp only`;
          -- bridge the dispatcher's `dite`-ctx slot-`a + 1 + j.val`
          -- read via `step_ctx_eval_simrec` + `Fin.ext` to
          -- `j.castSucc` where the K^sim side reads a
          -- previous-component value (per R4-B2 / R4-S6).
          -- Per R4-S5: split `dif_pos h_inbounds` out of `simp only`
          -- into its own `rw`.
          simp only [branches_j, h_instr]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          simp only [h_instr]
          by_cases h_eq : i.val = j.val
          · -- Register j is the target: K^sim branch is natK' _ c;
            -- URM-side regs j = Function.update _ i c j = c.
            -- Per round-5 S2: no `step_ctx_eval_simrec` bridge is
            -- needed in this sub-case — both K-side and URM-side
            -- reduce to the literal `c` with no `simrecVec`
            -- occurrence and no `i`-vs-`j` register reference.
            rw [if_pos h_eq]
            simp only [KMor1.interp_natK']
            rw [Function.update_apply, if_pos (Fin.ext h_eq).symm]
          · -- Register j is not the target: branch is v_j_prev;
            -- URM-side regs j unchanged = ih_regs j.
            rw [if_neg h_eq]
            simp only [v_j_prev, KMor1.interp_proj]
            rw [Function.update_apply,
                if_neg (fun h => h_eq (Fin.val_eq_of_eq h).symm)]
            rw [step_ctx_eval_simrec P v y (a + 1 + j.val)
                  (by omega) (by omega)]
            rw [show (⟨a + 1 + j.val - (a + 1), by omega⟩
                    : Fin (P.numRegs + 1))
                  = j.castSucc
                  from by apply Fin.ext; simp [Fin.castSucc]; omega]
            exact ih_regs j
        | inc i =>
          simp only [branches_j, h_instr]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          simp only [h_instr]
          by_cases h_eq : i.val = j.val
          · rw [if_pos h_eq]
            simp only [KMor1.interp_comp, KMor1.interp_succ,
              v_j_prev, KMor1.interp_proj]
            rw [Function.update_apply, if_pos (Fin.ext h_eq).symm]
            rw [step_ctx_eval_simrec P v y (a + 1 + j.val)
                  (by omega) (by omega)]
            rw [show (⟨a + 1 + j.val - (a + 1), by omega⟩
                    : Fin (P.numRegs + 1))
                  = j.castSucc
                  from by apply Fin.ext; simp [Fin.castSucc]; omega]
            rw [ih_regs j]
            -- Per round-5 blocker R5-B2: URM-side is
            -- `s.regs i + 1`, K-side is `s.regs j + 1`. Bridge
            -- `i` to `j` via the `h_eq : i.val = j.val` witness.
            -- Rewrite `i ↦ j` in the goal only (per plan round-7
            -- serious finding R7-S1: the prior `at *` form
            -- over-broadens, rewriting `h_eq : i.val = j.val` to a
            -- degenerate `j.val = j.val` and tripping the
            -- unusedHypothesis linter).
            rw [show i = j from Fin.ext h_eq]
          · rw [if_neg h_eq]
            simp only [v_j_prev, KMor1.interp_proj]
            rw [Function.update_apply,
                if_neg (fun h => h_eq (Fin.val_eq_of_eq h).symm)]
            rw [step_ctx_eval_simrec P v y (a + 1 + j.val)
                  (by omega) (by omega)]
            rw [show (⟨a + 1 + j.val - (a + 1), by omega⟩
                    : Fin (P.numRegs + 1))
                  = j.castSucc
                  from by apply Fin.ext; simp [Fin.castSucc]; omega]
            exact ih_regs j
        | dec i =>
          simp only [branches_j, h_instr]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          simp only [h_instr]
          by_cases h_eq : i.val = j.val
          · rw [if_pos h_eq]
            simp only [KMor1.interp_comp, KMor1.interp_pred,
              v_j_prev, KMor1.interp_proj]
            rw [Function.update_apply, if_pos (Fin.ext h_eq).symm]
            rw [step_ctx_eval_simrec P v y (a + 1 + j.val)
                  (by omega) (by omega)]
            rw [show (⟨a + 1 + j.val - (a + 1), by omega⟩
                    : Fin (P.numRegs + 1))
                  = j.castSucc
                  from by apply Fin.ext; simp [Fin.castSucc]; omega]
            rw [ih_regs j]
            -- Per round-5 blocker R5-B2: bridge `i` to `j` —
            -- URM-side is `s.regs i - 1`, K-side is `s.regs j - 1`.
            -- Rewrite `i ↦ j` in the goal only (per plan round-7
            -- serious finding R7-S1: the prior `at *` form
            -- over-broadens, rewriting `h_eq : i.val = j.val` to a
            -- degenerate `j.val = j.val` and tripping the
            -- unusedHypothesis linter).
            rw [show i = j from Fin.ext h_eq]
          · rw [if_neg h_eq]
            simp only [v_j_prev, KMor1.interp_proj]
            rw [Function.update_apply,
                if_neg (fun h => h_eq (Fin.val_eq_of_eq h).symm)]
            rw [step_ctx_eval_simrec P v y (a + 1 + j.val)
                  (by omega) (by omega)]
            rw [show (⟨a + 1 + j.val - (a + 1), by omega⟩
                    : Fin (P.numRegs + 1))
                  = j.castSucc
                  from by apply Fin.ext; simp [Fin.castSucc]; omega]
            exact ih_regs j
        | jumpZ i l₁ l₂ =>
          -- jumpZ leaves all registers unchanged. Per plan round-7
          -- blocker R7-B1: restore the URM-side chain (round 6's
          -- R6-S3 incorrectly stripped it on the assumption that
          -- `URMState.step P s`'s `.regs j` projection reduces
          -- definitionally; in landed Lean
          -- `URMState.step` is `if h : s.pc < P.instrs.size then …
          -- else s`, whose outer `if` is not eliminated until the
          -- proof tactically commits to one branch — so the chain
          -- is operationally necessary to expose `s.regs j`).
          simp only [branches_j, h_instr, v_j_prev, KMor1.interp_proj]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          simp only [h_instr]
          -- K^sim returns v_j_prev = ih_regs j after bridging the
          -- dispatcher's slot-`a + 1 + j.val` read to `j.castSucc`
          -- (per R4-B2 / R4-S6).
          rw [step_ctx_eval_simrec P v y (a + 1 + j.val)
                (by omega) (by omega)]
          rw [show (⟨a + 1 + j.val - (a + 1), by omega⟩
                  : Fin (P.numRegs + 1))
                = j.castSucc
                from by apply Fin.ext; simp [Fin.castSucc]; omega]
          exact ih_regs j
        | stop =>
          simp only [branches_j, h_instr, v_j_prev, KMor1.interp_proj]
          simp only [URMState.step]
          rw [dif_pos h_inbounds]
          simp only [h_instr]
          rw [step_ctx_eval_simrec P v y (a + 1 + j.val)
                (by omega) (by omega)]
          rw [show (⟨a + 1 + j.val - (a + 1), by omega⟩
                  : Fin (P.numRegs + 1))
                = j.castSucc
                from by apply Fin.ext; simp [Fin.castSucc]; omega]
          exact ih_regs j
      · -- Past-end: pcDispatch_default fires; default is v_j_prev.
        push_neg at h_inbounds
        have h_ctx_ge :
            (fun idx : Fin (a + 1 + (P.numRegs + 1)) =>
              if h₁ : idx.val < a + 1 then
                if h₂ : idx.val = 0 then (y : ℕ)
                else v ⟨idx.val - 1, by omega⟩
              else
                KMor1.simrecVec (baseFamily P) (stepFamily P) v y
                  ⟨idx.val - (a + 1), by omega⟩)
                (Fin.last (a + P.numRegs + 1))
              ≥ P.instrs.size := by
          rw [h_ctx_last_pc]; exact h_inbounds
        rw [KMor1.interp_pcDispatch_default P.instrs.size
              (fun k => branches_j P j k) (v_j_prev P j) _ h_ctx_ge]
        simp only [v_j_prev, KMor1.interp_proj]
        -- URM side: step returns s unchanged ⇒ regs j = ih_regs j.
        unfold URMState.step
        rw [dif_neg (Nat.not_lt_of_ge h_inbounds)]
        rw [step_ctx_eval_simrec P v y (a + 1 + j.val)
              (by omega) (by omega)]
        rw [show (⟨a + 1 + j.val - (a + 1), by omega⟩
                : Fin (P.numRegs + 1))
              = j.castSucc
              from by apply Fin.ext; simp [Fin.castSucc]; omega]
        exact ih_regs j
```

Each per-instruction block is ~12 – 15 LOC; total ~80 LOC for
the register-`j` branch (plus the past-end block). The
`Function.update_apply` / `Fin.ext` rewrite pair is the canonical
discharge for "register `j` equals register `i`" on the URM
side, matching K^sim's `if i.val = j.val` discriminator.

- [ ] **Step 7.10: Build to verify the full induction.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: clean build (zero `sorry` warnings, zero errors,
zero warnings).

- [ ] **Step 7.11: Axiom audit.**

```bash
bash scripts/check-axioms.sh GebLean.KSimURMSimulator.runFor_succ_init_back
bash scripts/check-axioms.sh GebLean.KSimURMSimulator.simulate_step_match
```

Expected for each: `[propext, Quot.sound]` only.

If `Classical.choice` appears, the most likely cause is
`by_cases` on a `Prop` without a `Decidable` instance, or
`fin_cases`. Per project memories
[`feedback_fin_cases_pulls_classical_choice.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_fin_cases_pulls_classical_choice.md)
and
[`feedback_mathlib_choice_in_functor_cat.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_mathlib_choice_in_functor_cat.md),
replace with explicit `Nat.decEq`-using `if … then … else`
constructs or core `Fin.cases` discriminations.

- [ ] **Step 7.12: Commit Task 7.**

```bash
jj describe -m "feat(ertok): add simulate_step_match conjunctive vector induction

introduce private theorem simulate_step_match : the conjunctive
vector IH for simulate_interp's induction on y. covers PC and
all numRegs registers component-by-component via Fin.lastCases.
include private runFor_succ_init_back deriving the back-peel
runFor s (y+1) = step (runFor s y) from front-peel runFor_succ
(:192) and runFor_add (:199), since the fixed s := init P v
makes the @[simp] front-peel rewrite wrong-direction. base case
discharged by simrecVec_zero plus the find?-result case-split;
step case case-by-case on the five URMInstr constructors plus
past-end. per spec § 4.2, § 4.3. audit axiom hygiene as
[propext, Quot.sound]-only on both new declarations."
jj new -m ""
```

---

## Task 8: `simulate_interp` and `simulate_level`

Spec § 4.1, § 4.4, § 5. The public-facing correctness theorem
(projecting `simulate_step_match` at the output register) and
the level bound.

**Files:**

- Modify: `GebLean/Utilities/KSimURMSimulator.lean` (append
  inside `namespace GebLean.KSimURMSimulator`).

- [ ] **Step 8.1: Add `simulate_interp`.**

Insert below `simulate_step_match`:

```lean
/-- The K^sim simulator's output at time `y` and input `v`
equals the value of `P.outputReg` after `y` URM steps from
`URMState.init P v`. Holds for every `URMProgram a`; no
`WellBounded` precondition required. Per spec § 4.1. -/
theorem simulate_interp {a : ℕ} (P : URMProgram a)
    (y : ℕ) (v : Fin a → ℕ) :
    (simulate P).interp (Fin.cons y v)
      = ((URMState.init P v).runFor P y).regs P.outputReg := by
  -- Per plan round-1 finding S5: replace the order-dependent
  -- `convert ... using 1` with an explicit chain. `Fin.cons_zero`
  -- and `Fin.cons_succ` are existing mathlib `@[simp]` lemmas
  -- that handle the context-splitting deterministically; the
  -- final `exact` closes against `simulate_step_match`'s register
  -- clause projected at `j := P.outputReg`.
  simp only [simulate, KMor1.interp_simrec, Fin.cons_zero,
    Fin.cons_succ]
  exact (simulate_step_match P v y).2 P.outputReg
```

- [ ] **Step 8.2: Build to verify.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: clean build.

- [ ] **Step 8.3: Add `simulate_level`.**

Insert below `simulate_interp`:

```lean
/-- The K^sim simulator is at level ≤ 2. By `KMor1.level`'s
`.simrec` clause, the level is `max sup_h sup_g + 1` where
`sup_h ≤ 0` (each base-family component is level 0 per
`baseFamily_level`) and `sup_g ≤ 1` (each step-family
component is level ≤ 1 per `stepFamily_level`). Per spec § 5. -/
theorem simulate_level {a : ℕ} (P : URMProgram a) :
    (simulate P).level ≤ 2 := by
  -- Per plan round-2 finding R2-M5: pin the goal to its `.simrec`
  -- normal form via `change` rather than `simp only [KMor1.level]`,
  -- which would recursively descend into inner `.level` slots and
  -- defeat the `baseFamily_level` / `stepFamily_level` bounds.
  unfold simulate
  change max (Finset.univ.sup (fun i => (baseFamily P i).level))
             (Finset.univ.sup (fun i => (stepFamily P i).level))
         + 1 ≤ 2
  apply Nat.add_le_add_right
  apply max_le
  · -- sup_h ≤ 1 (in fact = 0).
    apply Finset.sup_le
    intro i _
    rw [baseFamily_level]
    omega
  · -- sup_g ≤ 1.
    apply Finset.sup_le
    intro i _
    exact stepFamily_level P i
```

- [ ] **Step 8.4: Build to verify.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: clean build.

- [ ] **Step 8.5: Axiom audit on the two public theorems.**

```bash
bash scripts/check-axioms.sh GebLean.KSimURMSimulator.simulate_interp
bash scripts/check-axioms.sh GebLean.KSimURMSimulator.simulate_level
```

Expected for each: `[propext, Quot.sound]` only.

- [ ] **Step 8.6: Commit Task 8.**

```bash
jj describe -m "feat(ertok): add simulate_interp and simulate_level public theorems

introduce simulate_interp : (simulate P).interp (Fin.cons y v)
= ((URMState.init P v).runFor y).regs P.outputReg, derived by
projecting simulate_step_match's register clause at
j := P.outputReg combined with interp_simrec's context split.
introduce simulate_level : (simulate P).level ≤ 2 from
baseFamily_level (sup = 0) and stepFamily_level (sup ≤ 1) via
KMor1.level's .simrec clause max sup_h sup_g + 1. per spec §
4.1, § 4.4, § 5. audit [propext, Quot.sound]-only axiom
hygiene."
jj new -m ""
```

---

## Task 9: Re-export, axiom audit, final lint sweep

Spec § 6.1, § 6.3.

**Files:**

- Modify: `GebLean.lean` (add re-export line).
- Verify: all new modules in T3 still axiom-clean.
- Verify: markdownlint clean on spec and review files.

- [ ] **Step 9.1: Re-export `KSimURMSimulator` from
  `GebLean.lean`.**

Run: `grep -n "GebLean.Utilities.KArith" GebLean.lean`

Expected: shows the existing re-export line for `KArith`.

Modify `GebLean.lean` to add directly after the `KArith` line:

```lean
import GebLean.Utilities.KSimURMSimulator
```

Verify markdown-cleanliness of this change is irrelevant
(Lean file).

- [ ] **Step 9.2: Build the full project to verify the
  re-export.**

Run: `lake build`

Expected: clean build for all targets.

- [ ] **Step 9.3: Final axiom audit on every T3-introduced
  public declaration.**

Run, in sequence:

```bash
bash scripts/check-axioms.sh GebLean.KMor1.natK
bash scripts/check-axioms.sh GebLean.KMor1.interp_natK
bash scripts/check-axioms.sh GebLean.KMor1.natK_level
bash scripts/check-axioms.sh GebLean.KMor1.natK'
bash scripts/check-axioms.sh GebLean.KMor1.interp_natK'
bash scripts/check-axioms.sh GebLean.KMor1.natK'_level
bash scripts/check-axioms.sh GebLean.KMor1.interp_predIter
bash scripts/check-axioms.sh GebLean.KMor1.predIter_level
bash scripts/check-axioms.sh GebLean.KMor1.pcDispatch
bash scripts/check-axioms.sh GebLean.KMor1.interp_pcDispatch_match
bash scripts/check-axioms.sh GebLean.KMor1.interp_pcDispatch_default
bash scripts/check-axioms.sh GebLean.KMor1.pcDispatch_level
bash scripts/check-axioms.sh GebLean.KSimURMSimulator.baseFamily
bash scripts/check-axioms.sh GebLean.KSimURMSimulator.baseFamily_level
bash scripts/check-axioms.sh GebLean.KSimURMSimulator.stepFamily
bash scripts/check-axioms.sh GebLean.KSimURMSimulator.stepFamily_level
bash scripts/check-axioms.sh GebLean.KSimURMSimulator.simulate
bash scripts/check-axioms.sh GebLean.KSimURMSimulator.simulate_interp
bash scripts/check-axioms.sh GebLean.KSimURMSimulator.simulate_level
```

Expected for each: `[propext, Quot.sound]` only.

- [ ] **Step 9.4: Markdownlint on spec and review files.**

Run:

```bash
markdownlint-cli2 'docs/superpowers/specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md' \
  'docs/superpowers/specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.review-*.md' \
  'docs/superpowers/plans/2026-05-21-step-t3-urm-to-ksim-simulator-plan.md' \
  'docs/superpowers/plans/2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-*.md'
```

Expected: 0 errors.

- [ ] **Step 9.5: Run `lake test` to verify no test regressions.**

Run: `lake test`

Expected: all tests pass (T1/T2 tests should be unaffected; T3
does not introduce new tests beyond the in-Lean theorems).

- [ ] **Step 9.6: Commit Task 9 (re-export + audit).**

```bash
jj describe -m "chore(ertok): re-export KSimURMSimulator from GebLean.lean

add public import GebLean.Utilities.KSimURMSimulator to
GebLean.lean. axiom audit confirms [propext, Quot.sound]-only
hygiene on all 19 T3-introduced public declarations: KMor1.natK,
KMor1.natK', KMor1.interp_natK, KMor1.interp_natK',
KMor1.natK_level, KMor1.natK'_level, KMor1.interp_predIter,
KMor1.predIter_level, KMor1.pcDispatch,
KMor1.interp_pcDispatch_match, KMor1.interp_pcDispatch_default,
KMor1.pcDispatch_level, baseFamily, baseFamily_level,
stepFamily, stepFamily_level, simulate, simulate_interp,
simulate_level. lake build and lake test both clean."
jj new -m ""
```

- [ ] **Step 9.7: T3 implementation complete. Final
  verification.**

Run:

```bash
lake build
lake test
markdownlint-cli2 \
  'docs/superpowers/specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.md' \
  'docs/superpowers/specs/2026-05-21-step-t3-urm-to-ksim-simulator-design.review-*.md' \
  'docs/superpowers/plans/2026-05-21-step-t3-urm-to-ksim-simulator-plan.md' \
  'docs/superpowers/plans/2026-05-21-step-t3-urm-to-ksim-simulator-plan.review-*.md'
jj log -r '..@-' --no-graph --limit 12
```

Expected:

- `lake build`: zero errors, zero warnings.
- `lake test`: all tests pass.
- `markdownlint-cli2`: zero errors.
- `jj log`: shows the T3 commit chain (Task 1 through Task 9)
  at the tip of the topic branch.

If all four checks pass, T3 is complete. Hand off the topic
branch for user line-by-line review and, on approval, merge to
`origin/main` per the fork–upstream rule (merge-commit
strategy, no force push, user-gated `jj git push`).
