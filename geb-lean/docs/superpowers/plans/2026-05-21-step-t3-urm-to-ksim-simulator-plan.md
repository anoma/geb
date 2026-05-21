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

- [ ] **Step 0.3: Note the starting commit hash.**

Run: `jj log -r @- --no-graph --limit 1`

Expected: shows the spec's last commit
(`docs(ertok): apply T3 spec round-4 responses; adv review
converged` or any superseding chore commit).

If any of the above fails, halt: investigate before
proceeding. T3 should land on a clean baseline.

---

## Task 1: `KMor1.natK` and `KMor1.natK'` in `KArith.lean`

Spec § 3.6. Constant-K^sim morphisms at level 0; `natK c : KMor1
0` is built by `c`-fold composition of `succ` with `zero`;
`natK' n c : KMor1 n` lifts to arbitrary arity via composition
with `Fin.elim0`.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean` (append after the
  existing `KMor1.cond` block, around line 270; before
  `KMor1.notEq1` at line 278 if present).

- [ ] **Step 1.1: Locate the insertion point.**

Run: `grep -n "KMor1.cond\|KMor1.notEq1" GebLean/Utilities/KArith.lean | head -10`

Expected: shows `def KMor1.cond` at line 222 and the
`example : KMor1.cond.level = 1` block ending around line 270.
Insert new declarations after the `KMor1.cond` block and before
any later existing declaration.

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
    simp only [KMor1.natK, KMor1.level, Finset.univ.sup, ih]
    rfl
```

Note: the inner `simp only` reduces `(comp succ ...).level`
to `max succ.level (sup [natK c].level) = max 0 0 = 0`. If the
proof breaks, replace the `simp only` line with explicit
unfolds (`unfold KMor1.level`) and a `decide` on the final
arithmetic.

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
  simp only [KMor1.natK', KMor1.level, KMor1.natK_level]
  rfl
```

Note: the `Finset.univ.sup` over `Fin 0 → KMor1 n` (the
`Fin.elim0` family) is `0` because `Finset.univ` on `Fin 0` is
the empty finset and `Finset.sup ∅ f = ⊥ = 0` in `ℕ`.

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
[propext, Quot.sound]-only axiom hygiene confirmed on all six
new public declarations."
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

open GebLean.ZeroTestURM

end GebLean

namespace GebLean.KSimURMSimulator

open GebLean.ZeroTestURM
open GebLean

end GebLean.KSimURMSimulator
```

(The two `namespace … end namespace` skeletons are placeholders;
later tasks fill them with the relevant declarations.)

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
    simp only [KMor1.predIter, KMor1.level]
  | succ k ih =>
    simp only [KMor1.predIter, KMor1.level, Finset.univ.sup]
    -- comp pred [predIter k] at level max pred.level (predIter k).level
    -- = max 1 (≤ 1) = 1.
    cases h : (KMor1.predIter n k).level with
    | zero => omega
    | succ m => omega
```

Note: if `Finset.univ.sup` does not reduce cleanly, replace
the `simp only` with `unfold KMor1.level Finset.univ.sup` plus
a `by_cases`/`omega` close on the `max` term. The `cases h`
plus `omega` are belt-and-suspenders for the level-bound
argument.

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

- [ ] **Step 3.5: Add the `pcDispatchFrom` interp lemma
  (private, used by `pcDispatch`'s simp lemmas).**

Insert below `KMor1.pcDispatch`:

```lean
/-- Inner correctness lemma: `pcDispatchFrom k size` selects
`branches j` when the PC value equals `k + j.val`
(for `j : Fin size`), else `default`. Used to derive the public
`interp_pcDispatch_match` and `interp_pcDispatch_default`. -/
private theorem KMor1.interp_pcDispatchFrom
    {n : ℕ} (k size : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) (ctx : Fin (n + 1) → ℕ) :
    (KMor1.pcDispatchFrom k size branches default).interp ctx
      = if h : ctx (Fin.last n) < k + size then
          (branches ⟨ctx (Fin.last n) - k, by
            have : k ≤ ctx (Fin.last n) := by
              -- For this branch to fire correctly when used by
              -- pcDispatch's outer simp lemmas, k = 0 and PC < size
              -- (so k ≤ PC trivially); the general statement
              -- requires the additional hypothesis k ≤ PC, which
              -- the caller-side simp lemmas instantiate.
              sorry  -- replace via induction in step 3.6
            omega⟩).interp ctx
        else default.interp ctx := by
  sorry  -- replace in step 3.6
```

Note: this intermediate form is awkward because of the
"distance from offset" arithmetic. Step 3.6 replaces it with a
cleaner statement keyed to the specific `pcDispatch` use case
(`k = 0` in the public lemmas).

- [ ] **Step 3.6: Replace with the actual interp_pcDispatchFrom
  lemma and prove by induction on `size` with `k`, `branches`
  generalised.**

Replace the body of `KMor1.interp_pcDispatchFrom` with:

```lean
private theorem KMor1.interp_pcDispatchFrom
    {n : ℕ} (size : ℕ) (k : ℕ)
    (branches : Fin size → KMor1 (n + 1))
    (default : KMor1 (n + 1)) (ctx : Fin (n + 1) → ℕ) :
    (KMor1.pcDispatchFrom k size branches default).interp ctx
      = if h : ∃ j : Fin size, ctx (Fin.last n) = k + j.val then
          (branches h.choose).interp ctx
        else default.interp ctx := by
  induction size generalizing k branches with
  | zero =>
    simp only [KMor1.pcDispatchFrom]
    rw [dif_neg (by
      intro ⟨j, _⟩; exact Fin.elim0 j)]
  | succ size' ih =>
    simp only [KMor1.pcDispatchFrom, KMor1.interp_comp,
      KMor1.interp_cond, KMor1.interp_predIter]
    by_cases h0 : ctx (Fin.last n) = k
    · -- PC = k: outer cond's test (PC ∸ k = 0) fires, select branches ⟨0, _⟩.
      rw [h0]
      simp only [Nat.sub_self, ↓reduceIte]
      rw [dif_pos ⟨⟨0, by omega⟩, by simp⟩]
      congr 1
      -- The branch index `h.choose` for the existential proof equals ⟨0, _⟩.
      sorry  -- replace via Classical.choose_spec / direct construction
    · -- PC ≠ k: outer cond falls through to pcDispatchFrom (k+1) size'.
      have hsub : ctx (Fin.last n) ∸ k ≠ 0 := by
        intro he
        apply h0
        omega
      simp only [Nat.sub_eq_zero_iff_le, hsub.symm.le_iff_lt] at hsub
      sorry  -- replace by applying ih at (k+1) and equating the existentials
```

Note: this proof is intricate and may need refactoring. The
honest decomposition is to state and prove TWO separate inner
lemmas keyed to the dichotomy: a match case and a default case,
each conditioned on the relevant hypothesis. Step 3.7 replaces
the existential-flavoured statement with that decomposition.

- [ ] **Step 3.7: Refactor to two inner lemmas
  (`pcDispatchFrom_match`, `pcDispatchFrom_default`) with
  explicit hypotheses.**

Replace the entire `interp_pcDispatchFrom` block with:

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
      have hreduce : (if ctx (Fin.last n) - k = 0 then _ else _)
        = _ := by
        rw [if_neg hsub]
      rw [hreduce]
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

- [ ] **Step 3.8: Build to verify.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: clean build. If any of the auxiliary lemmas fails
(unification or arithmetic), use
`mcp__lean-lsp__lean_goal` to inspect the goal state at the
failure point and adjust.

- [ ] **Step 3.9: Add the public `interp_pcDispatch_match` simp
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

- [ ] **Step 3.10: Add the public `interp_pcDispatch_default`
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

- [ ] **Step 3.11: Add the `pcDispatch_level` lemma.**

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
  | zero => simpa [KMor1.pcDispatchFrom] using h_default
  | succ size' ih =>
    simp only [KMor1.pcDispatchFrom, KMor1.level]
    -- comp cond [predIter, branches[0], recur] at level
    -- max cond.level (max predIter.level (max b0.level recur.level))
    -- = max 1 (max 1 (max ≤1 ≤1)) = 1.
    have hpred : (KMor1.predIter n k).level ≤ 1 :=
      KMor1.predIter_level n k
    have hb0 : (branches ⟨0, by omega⟩).level ≤ 1 :=
      h_branches _
    have hrecur : (KMor1.pcDispatchFrom (k + 1) size'
        (fun j : Fin size' => branches j.succ) default).level ≤ 1 :=
      ih (k + 1) (fun j => branches j.succ)
        (fun j => h_branches j.succ)
    -- KMor1.cond.level = 1; max with level-≤-1 children stays ≤ 1.
    have hcond_level : (KMor1.cond : KMor1 3).level = 1 := by decide
    -- The sup over Fin 3 of the family's levels.
    have hsup : Finset.univ.sup (fun i : Fin 3 =>
        match i with
        | ⟨0, _⟩ => (KMor1.predIter n k).level
        | ⟨1, _⟩ => (branches ⟨0, by omega⟩).level
        | ⟨2, _⟩ => (KMor1.pcDispatchFrom (k + 1) size'
            (fun j => branches j.succ) default).level) ≤ 1 := by
      apply Finset.sup_le
      intro i _
      fin_cases i <;> [exact hpred; exact hb0; exact hrecur]
    rw [hcond_level]
    exact Nat.le_of_eq_of_le (max_eq_right hsup) hsup  -- or omega-style closure
```

Note: the final step's `max 1 hsup ≤ 1` may need
`Nat.max_le` plus the hypothesis bounds. If the displayed
`Nat.le_of_eq_of_le` line fails, replace with:

```lean
    omega  -- if the goal is purely arithmetic
```

or unfold `max` manually and case-split.

- [ ] **Step 3.12: Add the public `pcDispatch_level` lemma.**

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

- [ ] **Step 3.13: Build to verify.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: clean build.

- [ ] **Step 3.14: Axiom audit on the three public
  declarations.**

```bash
bash scripts/check-axioms.sh GebLean.KMor1.interp_pcDispatch_match
bash scripts/check-axioms.sh GebLean.KMor1.interp_pcDispatch_default
bash scripts/check-axioms.sh GebLean.KMor1.pcDispatch_level
```

Expected for each: `[propext, Quot.sound]` only.

If `Classical.choice` appears, the `fin_cases` tactic (Step
3.11) is the likely cause; replace with explicit
`match`/`omega` discharge per the project memory at
[`feedback_fin_cases_pulls_classical_choice.md`](../../.claude/projects/-home-terence-git-workspaces-geb/memory/feedback_fin_cases_pulls_classical_choice.md).

- [ ] **Step 3.15: Commit Task 3.**

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
context-substitution wrapper. [propext, Quot.sound]-only axiom
hygiene confirmed on all three public declarations."
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
  -- Case-split on Fin.lastCases.
  rcases Fin.lastCases_eq_last_or_castSucc j with hL | ⟨r, hR⟩
  · -- j = Fin.last P.numRegs
    subst hL; simp [baseFamily, Fin.lastCases_last]
  · -- j = r.castSucc for some r : Fin P.numRegs
    subst hR
    simp only [baseFamily, Fin.lastCases_castSucc]
    cases (List.finRange a).find?
        (fun i => decide (P.inputRegs i = r)) with
    | some i => rfl
    | none => rfl
```

Note: `Fin.lastCases_eq_last_or_castSucc` may be a different
name in current mathlib. If not present, use
`Fin.lastCases_last` and `Fin.lastCases_castSucc` directly on
`j` after a `rcases j.eq_last_or_castSucc` (or similar) — check
mathlib via `mcp__lean-lsp__lean_local_search` for the exact
name.

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
spec § 3.3. [propext, Quot.sound]-only axiom hygiene confirmed."
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
PC value. Level 0. -/
private def I_prev {a : ℕ} (P : URMProgram a) :
    KMor1 (a + 1 + (P.numRegs + 1)) :=
  KMor1.proj (Fin.last (a + P.numRegs + 1))

/-- Projection at slot `a + 1 + j.val` of the step context:
the previous value of register `j`. Level 0. -/
private def v_j_prev {a : ℕ} (P : URMProgram a)
    (j : Fin P.numRegs) :
    KMor1 (a + 1 + (P.numRegs + 1)) :=
  KMor1.proj ⟨a + 1 + j.val, by
    have := j.isLt
    omega⟩
```

Note: the `Fin.last (a + P.numRegs + 1)` index lives in
`Fin (a + 1 + (P.numRegs + 1)) = Fin (a + P.numRegs + 2)`; the
literal `Fin.last (a + P.numRegs + 1)` constructs this. Verify
with `mcp__lean-lsp__lean_goal` if the type does not match.

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
- otherwise (`.assign`, `.inc`, `.dec`) → `I_prev + 1`. -/
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
  | _ =>
    -- .assign, .inc, .dec: PC + 1
    KMor1.comp KMor1.succ
      (fun _ : Fin 1 => I_prev P)
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
  -- Case-split on Fin.lastCases.
  rcases Fin.lastCases_eq_last_or_castSucc j with hL | ⟨r, hR⟩
  · subst hL
    simp only [stepFamily, Fin.lastCases_last]
    apply KMor1.pcDispatch_level
    · intro k
      -- Each branches_pc k is level ≤ 1: stop = I_prev (level 0),
      -- jumpZ = comp cond [...] (level 1), default = comp succ [I_prev] (level 0).
      unfold branches_pc
      split <;> simp [KMor1.level, I_prev, v_j_prev, KMor1.natK'_level] <;>
        decide
    · -- default = I_prev (level 0).
      unfold I_prev; simp [KMor1.level]
  · subst hR
    simp only [stepFamily, Fin.lastCases_castSucc]
    apply KMor1.pcDispatch_level
    · intro k
      unfold branches_j
      split <;> split <;>
        simp [KMor1.level, v_j_prev, KMor1.natK'_level,
          KMor1.pred, KMor1.succ] <;> decide
    · unfold v_j_prev; simp [KMor1.level]
```

Note: the inner `split <;> simp <;> decide` chains are
best-effort; if they fail, decompose into explicit `cases`
on `P.instrs[k]` plus `unfold KMor1.level` plus targeted
arithmetic. Inspect goal state via `mcp__lean-lsp__lean_goal`.

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
[propext, Quot.sound]-only axiom hygiene confirmed."
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
[propext, Quot.sound]-only axiom hygiene confirmed."
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
`runFor_add` (`:199`). The fixed `s := URMState.init P v` makes
this the form needed inside the simulate_step_match induction;
`runFor_succ` itself (front-peel) is `@[simp]` in the wrong
direction for that purpose. Per spec § 4.3. -/
private theorem URMState.runFor_succ_back {a : ℕ}
    (P : URMProgram a) (s : URMState P) (y : ℕ) :
    URMState.runFor P s (y + 1)
      = URMState.step P (URMState.runFor P s y) := by
  -- runFor s (y + 1) = runFor (runFor s y) 1 (by runFor_add)
  --                  = step (runFor s y)     (by runFor_succ at n = 0)
  rw [URMState.runFor_add P s y 1, URMState.runFor_succ,
      URMState.runFor_zero]
```

- [ ] **Step 7.2: Add `simulate_step_match` declaration with
  `by sorry` body.**

Insert below `URMState.runFor_succ_back`:

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
      -- (runFor 0).pc = (init P v).pc = 0.
      rfl
    · -- Register components at y = 0.
      intro j
      simp only [KMor1.simrecVec_zero, baseFamily,
        Fin.lastCases_castSucc]
      -- baseFamily P j.castSucc unfolds to the match on
      -- List.find?; URMState.init's regs field unfolds to the
      -- same match. Case-split on the find?-result.
      cases h : (List.finRange a).find?
          (fun i => decide (P.inputRegs i = j)) with
      | some i =>
        simp only [KMor1.interp_proj]
        -- URMState.init P v has regs r = match find? ... with
        --   | some i => v i | none => 0
        -- and h pins find? to some i, so regs j = v i.
        simp only [URMState.init, h]
      | none =>
        simp only [KMor1.interp_zero, URMState.init, h]
  | succ y ih => sorry  -- replace in step 7.5
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
    rw [URMState.runFor_succ_back]
    -- K^sim side: peel via simrecVec_succ.
    refine ⟨?_, ?_⟩
    · -- PC component at y + 1.
      rw [KMor1.simrecVec_succ]
      -- Now reduce the step-family PC component over the
      -- previous-iteration vector, which by ih matches the URM
      -- state at y.
      sorry  -- replace in step 7.7
    · -- Register-j component at y + 1.
      intro j
      rw [KMor1.simrecVec_succ]
      sorry  -- replace in step 7.8
```

- [ ] **Step 7.7: Fill the PC step case.**

Replace the first `sorry` (the PC component) with a case-split
on the instruction at `(runFor y).pc`. Use
`mcp__lean-lsp__lean_goal` to inspect the goal shape; the
structure is:

```lean
      -- Set up the step context shape.
      simp only [stepFamily, Fin.lastCases_last]
      -- The dispatcher's match-vs-default split.
      by_cases h_inbounds :
          ((URMState.init P v).runFor P y).pc < P.instrs.size
      · -- In-bounds: pcDispatch_match fires at k = (runFor y).pc.
        set pcVal := ((URMState.init P v).runFor P y).pc with hpc
        -- After `simrecVec_succ` unfolding, the step context at the
        -- last slot reads the previous PC = `simrecVec ... y
        -- (Fin.last P.numRegs)`, which by `ih_pc` equals `pcVal`.
        -- Use `mcp__lean-lsp__lean_goal` to inspect the exact step
        -- context shape; `h_pc_eq` is then a literal restatement of
        -- `ih_pc` after the substitution.
        have h_pc_eq :
            KMor1.simrecVec (baseFamily P) (stepFamily P) v y
                (Fin.last P.numRegs)
              = pcVal := ih_pc
        -- Apply pcDispatch_match.
        rw [KMor1.interp_pcDispatch_match P.instrs.size
              (fun k => branches_pc P k) (I_prev P) _
              ⟨pcVal, h_inbounds⟩ h_pc_eq]
        -- Now case-split on the instruction at pcVal.
        cases h_instr : P.instrs[pcVal]'h_inbounds with
        | assign i c =>
          -- branches_pc returns succ ∘ I_prev (PC + 1).
          unfold branches_pc
          rw [h_instr]
          simp only [KMor1.interp_comp, KMor1.interp_succ,
            I_prev, KMor1.interp_proj]
          -- URM side: step performs `assign i c`, PC := pc + 1.
          unfold URMState.step
          rw [dif_pos h_inbounds, h_instr]
          simp [ih_pc]
        | inc i =>
          unfold branches_pc
          rw [h_instr]
          simp only [KMor1.interp_comp, KMor1.interp_succ,
            I_prev, KMor1.interp_proj]
          unfold URMState.step
          rw [dif_pos h_inbounds, h_instr]
          simp [ih_pc]
        | dec i =>
          unfold branches_pc
          rw [h_instr]
          simp only [KMor1.interp_comp, KMor1.interp_succ,
            I_prev, KMor1.interp_proj]
          unfold URMState.step
          rw [dif_pos h_inbounds, h_instr]
          simp [ih_pc]
        | jumpZ i l₁ l₂ =>
          unfold branches_pc
          rw [h_instr]
          simp only [KMor1.interp_comp, KMor1.interp_cond,
            v_j_prev, KMor1.interp_proj, KMor1.interp_natK']
          unfold URMState.step
          rw [dif_pos h_inbounds, h_instr]
          -- URM side: pc := if regs i = 0 then l₁ else l₂.
          -- K^sim side: cond on v_i_prev (= regs i by ih_regs i).
          rw [ih_regs i]
          -- Match the if-then-else shape on both sides.
          by_cases h_zero : ((URMState.init P v).runFor P y).regs i = 0
          · rw [h_zero]; simp
          · rw [if_neg h_zero]; simp [h_zero]
        | stop =>
          unfold branches_pc
          rw [h_instr]
          simp only [I_prev, KMor1.interp_proj]
          unfold URMState.step
          rw [dif_pos h_inbounds, h_instr]
          exact ih_pc
      · -- Past-end: pcDispatch_default fires.
        push_neg at h_inbounds
        -- The step context's last slot reads
        -- `simrecVec ... y (Fin.last P.numRegs)`, which by
        -- `ih_pc` equals `(runFor y).pc` and is `≥ P.instrs.size`
        -- by `h_inbounds`.
        have h_pc_ge :
            KMor1.simrecVec (baseFamily P) (stepFamily P) v y
                (Fin.last P.numRegs)
              ≥ P.instrs.size := by
          rw [ih_pc]; exact h_inbounds
        rw [KMor1.interp_pcDispatch_default P.instrs.size
              (fun k => branches_pc P k) (I_prev P) _ h_pc_ge]
        simp only [I_prev, KMor1.interp_proj]
        -- URM side: step returns s unchanged.
        unfold URMState.step
        rw [dif_neg (Nat.not_lt_of_ge h_inbounds)]
        exact ih_pc
```

Note: the `h_pc_eq` and `h_pc_ge` `have` statements supply
`pcDispatch_match`'s and `pcDispatch_default`'s context-slot
hypotheses by reading the previous PC out of the simrec
component vector via `ih_pc`. The step context's last slot
(per `simrecVec_succ`'s layout, spec § 3.4) is precisely the
previous-component value at index `Fin.last P.numRegs`, so
the hypothesis form is a literal `ih_pc` after substitution.
Use `mcp__lean-lsp__lean_goal` at each `rw` invocation to
verify the exact step context shape and adjust if the
elaborator displays it in a different but equivalent form.

- [ ] **Step 7.8: Fill the register-`j` step case.**

Replace the second `sorry` (the register-`j` component) with
the same shape: `Fin.lastCases_castSucc` plus dispatcher match
vs default, plus the five `URMInstr` cases. The only structural
difference is that each branch returns either an updated
register-`j` value or `v_j_prev` (unchanged). Mirror Step 7.7's
shape with the per-instruction `if i.val = j.val` discriminator
handling.

```lean
      -- (Pattern follows Step 7.7. Each instruction's branch
      -- either updates register-j via Function.update equality
      -- on the URM side, or leaves it via `regs j`.)
      sorry  -- substantial; allocate ~80 LOC; verify via
             -- mcp__lean-lsp__lean_goal at each subcase
```

Mirror Step 7.7's structure for the register-`j` component;
the URM-side `Function.update`'s `j = i.val` vs `j ≠ i.val`
case-split discharges by Lean's `Function.update_apply` and
the `if`-`then`-`else` shape on the K^sim side. Each instruction
case takes ~12-15 LOC; total ~80 LOC for the register branch.

- [ ] **Step 7.9: Build to verify the full induction.**

Run: `lake build GebLean.Utilities.KSimURMSimulator`

Expected: clean build (zero `sorry` warnings, zero errors,
zero warnings).

- [ ] **Step 7.10: Axiom audit.**

```bash
bash scripts/check-axioms.sh GebLean.KSimURMSimulator.URMState.runFor_succ_back
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

- [ ] **Step 7.11: Commit Task 7.**

```bash
jj describe -m "feat(ertok): add simulate_step_match conjunctive vector induction

introduce private theorem simulate_step_match : the conjunctive
vector IH for simulate_interp's induction on y. covers PC and
all numRegs registers component-by-component via Fin.lastCases.
include private URMState.runFor_succ_back deriving the back-peel
runFor s (y+1) = step (runFor s y) from front-peel runFor_succ
(:192) and runFor_add (:199), since the fixed s := init P v
makes the @[simp] front-peel rewrite wrong-direction. base case
discharged by simrecVec_zero plus the find?-result case-split;
step case case-by-case on the five URMInstr constructors plus
past-end. per spec § 4.2, § 4.3. [propext, Quot.sound]-only
axiom hygiene confirmed on both new declarations."
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
  -- Unfold `simulate` to its underlying simrec; reduce
  -- `interp_simrec` to `simrecVec` over the public-facing
  -- context (recvar = `Fin.cons y v 0 = y`; params = v).
  simp only [simulate, KMor1.interp_simrec]
  -- The output index is P.outputReg.castSucc; project
  -- simulate_step_match's register clause at j := P.outputReg.
  have h := (simulate_step_match P v y).2 P.outputReg
  -- Match contexts: Fin.cons's slot 0 is y, and params at
  -- Fin.succ j is v j.
  convert h using 1
  · -- Equating `simrecVec ... y P.outputReg.castSucc` on both sides.
    rfl
  · -- The parameter projection matches.
    funext j
    simp [Fin.cons, Fin.succ]
```

Note: the exact `convert ... using 1` arity and the
`funext` discharge may need adjustment depending on
`interp_simrec`'s exact unfolding. Use
`mcp__lean-lsp__lean_goal` to inspect the goal shape.

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
  unfold simulate
  simp only [KMor1.level]
  -- Reduce to: max sup_h sup_g + 1 ≤ 2.
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
4.1, § 4.4, § 5. [propext, Quot.sound]-only axiom hygiene
confirmed."
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
markdownlint-cli2 'docs/**/*.md'
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
