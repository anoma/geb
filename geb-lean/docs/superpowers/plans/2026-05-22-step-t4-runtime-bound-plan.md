# T4 — Runtime bound and `erToK` assembly — implementation plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> `superpowers:subagent-driven-development` (recommended) or
> `superpowers:executing-plans` to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.
>
> **Status (2026-05-23):** Tasks 0–8 committed on
> `feat/ertok-runtime-bound`. The recipe was amended in five
> rounds of adversarial review during Task 5–8 execution (see
> §4.2 of the spec for the binding form; mu values bumped for
> bsum and bprod, offsets augmented with `k` and
> `compileER_numRegs f` where needed). The Tasks 5–8 SDD
> session landed `boundExprKParams_dominates` as one joint
> commit at `3e1dd99`. Tasks 9–15 plus the holistic final
> review remain. The continuation handoff at
> [`2026-05-23-step-t4-tasks-9-15-handoff.md`](2026-05-23-step-t4-tasks-9-15-handoff.md)
> is the binding entry point for the next session. The earlier
> handoff [`2026-05-23-step-t4-tasks-5-8-handoff.md`](2026-05-23-step-t4-tasks-5-8-handoff.md)
> is retained as a historical artifact of the recipe-amendment
> convergence.

**Goal:** assemble `erToK : ERMor1 a → KMor1 a` of level ≤ 2
with `(erToK e).interp v = e.interp v`, and package it as
`erToKFunctor : LawvereERCat ⥤ LawvereKSimDCat 2`. Transcribes
the ⊇ direction of Tourlakis 2018 Corollary 0.1.0.44 at
`n = 2`.

**Architecture:** five pieces (matching spec §3). (1) a per-ER-
constructor recipe `boundExprKParams : ERMor1 a → ℕ × ℕ`
producing `(mu_e, offset_e)` with a joint runtime+value bound
theorem against `tower mu_e (Fin.maxOfNat _ v + offset_e)`;
(2) three K^sim composites `maxK`, `maxOver`, `pow2_iter` in
`KArith.lean`; (3) `boundExprK := pow2_iter mu ∘ (add ∘ ⟨maxOver
a, natK' a offset⟩)`; (4) `erToK := comp (simulate (compileER
e)) (Fin.cons (boundExprK e) projections)`; (5) the multi-output
extension `erToKN` lifted through the ER quotient with
depth-2 witness on the K side, mirroring `kToERFunctor` at
`GebLean/LawvereKSimER.lean:474`.

**Tech Stack:** Lean 4 (toolchain `lean-toolchain`), mathlib
(via `lake`), project-local `GebLean.LawvereKSim`,
`GebLean.LawvereKSimInterp`, `GebLean.LawvereKSimQuot`,
`GebLean.LawvereER`, `GebLean.LawvereERQuot`,
`GebLean.Utilities.KArith`, `GebLean.Utilities.ZeroTestURM`,
`GebLean.Utilities.Tower`, `GebLean.Utilities.ERAMajorants`,
`GebLean.LawvereERKSim.Compiler`,
`GebLean.LawvereERKSim.Top`, `GebLean.Utilities.KSimURMSimulator`.

**Spec under implementation:**
[`docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`](../specs/2026-05-22-step-t4-runtime-bound-design.md)
(rounds 1–4 converged on 2026-05-22).

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Workflow notes](#workflow-notes)
- [Task 0: Baseline verification](#task-0-baseline-verification)
- [Task 1: `KMor1.maxK` in `KArith.lean`](#task-1-kmor1maxk-in-karithlean)
- [Task 2: `KMor1.maxOver` in `KArith.lean`](#task-2-kmor1maxover-in-karithlean)
- [Task 3: `KMor1.pow2_iter` in `KArith.lean`](#task-3-kmor1pow2_iter-in-karithlean)
- [Task 4: Create `RuntimeBound.lean`; `boundExprKParams` skeleton](#task-4-create-runtimeboundlean-boundexprkparams-skeleton)
- [Task 5: `boundExprKParams_dominates` atom cases](#task-5-boundexprkparams_dominates-atom-cases)
- [Task 6: `boundExprKParams_dominates` comp case](#task-6-boundexprkparams_dominates-comp-case)
- [Task 7: `boundExprKParams_dominates` bsum case](#task-7-boundexprkparams_dominates-bsum-case)
- [Task 8: `boundExprKParams_dominates` bprod case](#task-8-boundexprkparams_dominates-bprod-case)
- [Task 9: `boundExprK` def + level + interp + dominates](#task-9-boundexprk-def--level--interp--dominates)
- [Task 10: Create `ErToK.lean`; `erToK` + level + interp](#task-10-create-ertoklean-ertok--level--interp)
- [Task 11: Create `ErToKFunctor.lean`; `erToKN` + interp + level + compat](#task-11-create-ertokfunctorlean-ertokn--interp--level--compat)
- [Task 12: `erToKFunctor_map` via `Quotient.liftOn`](#task-12-ertokfunctor_map-via-quotientlifton)
- [Task 13: `erToKFunctor_map_id` and `erToKFunctor_map_comp`](#task-13-ertokfunctor_map_id-and-ertokfunctor_map_comp)
- [Task 14: `erToKFunctor` assembly](#task-14-ertokfunctor-assembly)
- [Task 15: Re-export, axiom audit, final lint sweep, tests](#task-15-re-export-axiom-audit-final-lint-sweep-tests)

<!-- END doctoc -->

---

## Workflow notes

Rules that bind every task in this plan:

- **Build with `lake build`. Never `lake env lean`. Never
  `lake clean`** (per
  [`.claude/rules/lean-coding.md`](../../.claude/rules/lean-coding.md)
  § Lake / build workflow).
- **One declaration at a time.** Get each new `def` / `theorem`
  to fully compile (no `sorry`, no `_`, no `admit`) before
  proceeding to the next. Per
  `.claude/rules/lean-coding.md` § Proof guidelines.
- **`sorry` only between commits.** Use it as a TDD analog
  inside a task (write signature with `by sorry`, build to
  confirm the signature elaborates, then fill the body). Never
  commit `sorry`. `admit` is never permitted.
- **Axiom audit per task.** After each task's final build is
  clean, run `bash scripts/check-axioms.sh <file-path>` on the
  file(s) the task modified (the script auto-discovers public
  declarations in the files; it accepts file or directory
  paths, not declaration names). Expected output: only
  `[propext, Quot.sound]` in the axiom set, with the exception
  of the three AXIOM_ALLOW sites enumerated in spec §11
  (`boundExprKParams_dominates` bsum and bprod cases;
  `erToK_interp`). Theorems that *inherit* `Classical.choice`
  via transitive dependence on those three sites
  (e.g., `boundExprK_dominates`, `erToKN_interp`,
  `erToKFunctor_map_id` if it routes through `erToK_interp`)
  carry the annotation by inheritance but are not counted as
  new sites. Any unanticipated extra axiom (in particular
  unexpected `Classical.choice` or `sorryAx`) is a defect that
  must be fixed before commit.

- **Level-proof style for K^sim composites.** The codebase
  does not expose `KMor1.level_*` simp lemmas. The
  established pattern (see `KArith.lean:38, 159, 472, 598,
  …`) is `example : <decl>.level = N := by decide` for
  individual composites, and `unfold <decl> ; change …`
  followed by `Nat.max_le` + `Fin.maxOfNat_le` /
  `Fin.le_maxOfNat` for upper-bound theorems (see
  `KSimURMSimulator.lean:975-984` for the canonical
  pattern). All Tasks 1-3, 9, 10 below use this pattern;
  the Lean code blocks state the intent and rely on the
  implementer to instantiate the unfold/max_le chain
  against the codebase's current surface.

- **Namespace qualification for T2 surface.** `compileER`,
  `compileER_runtime`, `compileER_runFor`, `compileER_numRegs`,
  `URMState.init`, and `URMState.runFor` reside under
  `namespace GebLean.LawvereERKSim` /
  `namespace GebLean.LawvereERKSim.URMState`. Inside the
  T4 modules' `namespace GebLean` blocks, refer to them as
  `LawvereERKSim.compileER_runtime`, etc. The plan's pseudo-
  Lean elides the qualifier in some places for brevity; the
  implementer adds the prefix at every use site (Tasks 4-10
  in particular).

- **AXIOM\_ALLOW annotation placement.** Each annotated
  declaration carries its own
  `-- AXIOM_ALLOW: Classical.choice (rationale)` comment
  immediately above its declaration (per
  `.claude/rules/lean-coding.md` § Accepted exceptions).
  Inheritance does not auto-propagate to callers; theorems
  that consume an AXIOM\_ALLOW'd lemma carry their own
  annotation. The three primary sites
  (`boundExprKParams_dominates` bsum/bprod cases via
  conjunctive theorem; `erToK_interp`) plus the inherited
  sites (`boundExprK_dominates`, `erToKN_interp`,
  `erToKFunctor_map_id`, `erToKFunctor_map_comp`,
  `erToKFunctor`) each need an explicit annotation line at
  their declaration.

- **Tower lemma surface** (verified in `Tower.lean`):
  - `self_le_tower (k x : ℕ) : x ≤ tower k x` — two args,
    no precondition.
  - `tower_mono_left {k₁ k₂ : ℕ} (h : k₁ ≤ k₂) (x : ℕ) :
    tower k₁ x ≤ tower k₂ x`.
  - `tower_mono_right (k : ℕ) {x y : ℕ} (h : x ≤ y) :
    tower k x ≤ tower k y`.
  - `tower_comp (j k x : ℕ) : tower j (tower k x) = tower
    (j + k) x`.
  - `mul_tower_le_tower_add_two {k m : ℕ} (hm : 2 ≤ m) :
    m * tower k m ≤ tower (k + 2) m`.
  - `tower_pow_le_tower_add_three {k m : ℕ} (hm : 2 ≤ m) :
    tower k m ^ m ≤ tower (k + 3) m`.

  Tasks 5-8 must stage the `2 ≤ m` hypothesis (every
  recipe offset is `≥ 3`, so `m = Fin.maxOfNat _ v +
  offset ≥ 3 ≥ 2`). The plan does not assume any
  unlisted Tower lemmas exist; combinations like
  `tower_mono_both` are synthesised inline as
  `(tower_mono_left h₁ _).trans (tower_mono_right _ h₂)`.
- **Conventional commits.** Subject: `feat(ertok): …` for
  new helpers and theorems; `chore(ertok): …` for axiom audits
  and re-exports; `refactor(ertok): …` for reshape; `test(ertok): …`
  for tests. Imperative present, lowercase first letter, no
  trailing period.
- **Markdownlint-clean docstrings.** Lean module docstrings
  inside `/-! … -/` and declaration docstrings inside
  `/-- … -/` follow the mathlib `doc.html` section ordering.
- **Generic user references** in commit messages and
  docstrings. Use "the user" / "they" / "them"; no first
  names.
- **No raw mutating `git` subcommands.** Use `jj` for
  state-mutating operations.
- **Mathlib upstream guides (re-fetch on entry to each task
  that introduces new public API):**
  - `https://leanprover-community.github.io/contribute/naming.html`
  - `https://leanprover-community.github.io/contribute/style.html`
  - `https://leanprover-community.github.io/contribute/doc.html`

**TDD pattern for Lean** (per task): (i) write the
declaration's signature with a `by sorry` body (theorems) or
`:= sorry` (definitions whose body is non-trivial); (ii)
`lake build` to confirm the signature elaborates; (iii) fill
the body; (iv) `lake build` clean; (v) per-task axiom check;
(vi) commit. Tests where applicable land in
`GebLeanTests/` (Tasks 1–3 and Task 15).

**Joint-commit exception (Tasks 5–8).** `boundExprKParams_dominates`
is a single conjunctive inductive theorem with four
structural cases (atoms / comp / bsum / bprod). The four
cases land jointly as Task 5's commit. Tasks 5–8 are
sub-tasks of one logical commit unit; the implementer
proceeds through 5 → 6 → 7 → 8 with the working copy
carrying `sorry`-bearing intermediate states, then runs
`lake build`, axiom audit, and a single `jj describe`/`jj
new` at the *end of Task 8*. The SDD harness treats Tasks
5–8 as one "task" for progress-tracking purposes; the plan
keeps them numbered separately for narrative clarity but
the work-on/check-off boundary is at Task 8's commit. No
other task carries this exception.

**Branch:** Tasks land on `feat/ertok-runtime-bound`. Each
task ends with a commit (jj describe + new); no `jj git push`
between tasks (push requires user line-by-line review).

---

## Task 0: Baseline verification

**Goal:** confirm the spec branch state is buildable and
clean before any T4 work.

**Files:** none modified.

- [ ] **Step 1: Confirm jj working copy is on the spec branch**

```bash
jj log -r 'feat/ertok-runtime-bound' --no-graph | head -3
```

Expected: the bookmark points at the spec commit `edf20634`
(or a later commit if the plan has already been amended).

- [ ] **Step 2: Build the project**

Run: `lake build`
Expected: 0 errors, 0 warnings.

- [ ] **Step 3: Run the existing test suite**

Run: `lake test`
Expected: 0 failures.

- [ ] **Step 4: Run the axiom audit**

Run: `bash scripts/check-axioms.sh`
Expected: 0 failures (all existing declarations within the
allowed axiom envelope).

- [ ] **Step 5: Confirm markdownlint clean**

Run: `markdownlint-cli2 'docs/**/*.md'`
Expected: 0 errors.

No commit for Task 0.

---

## Task 1: `KMor1.maxK` in `KArith.lean`

**Spec ref:** §5.1.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean` (extend the
  `KMor1` namespace; place after `KMor1.monus` and
  `KMor1.add`).
- Modify: `GebLeanTests/Utilities/KArith.lean` (append
  `#guard` tests).

- [ ] **Step 1: Add the declaration with `sorry`**

After the last existing `KMor1.*` declaration in
`KArith.lean`, append:

```lean
/-- Binary maximum of two natural-number inputs, as a
`K^sim` morphism. Defined via truncated subtraction:
`max x y = (x ∸ y) + y`. Closed form: `(maxK).interp v =
Nat.max (v 0) (v 1)`. Level ≤ 2 (composition of
`KMor1.add` at level 1 with `KMor1.monus` at level 2 and
projections at level 0). -/
def KMor1.maxK : KMor1 2 := sorry
```

- [ ] **Step 2: `lake build` to confirm signature elaborates**

Run: `lake build`
Expected: build fails with "declaration uses 'sorry'"
warning at `KMor1.maxK`. Signature type-checks.

- [ ] **Step 3: Fill the body**

Replace the `sorry` with:

```lean
def KMor1.maxK : KMor1 2 :=
  KMor1.comp KMor1.add
    (fun i : Fin 2 =>
      match i with
      | ⟨0, _⟩ => KMor1.comp KMor1.monus (fun j : Fin 2 =>
                    match j with
                    | ⟨0, _⟩ => KMor1.proj ⟨0, by decide⟩
                    | ⟨1, _⟩ => KMor1.proj ⟨1, by decide⟩)
      | ⟨1, _⟩ => KMor1.proj ⟨1, by decide⟩)
```

- [ ] **Step 4: Add the interp lemma with `sorry`**

```lean
@[simp] theorem KMor1.interp_maxK (v : Fin 2 → ℕ) :
    KMor1.maxK.interp v = Nat.max (v 0) (v 1) := by sorry
```

- [ ] **Step 5: `lake build`, then fill the proof**

The body should reduce via `simp only [KMor1.maxK,
KMor1.interp_comp, KMor1.interp_add, KMor1.interp_monus,
KMor1.interp_proj]` to `(v 0 ∸ v 1) + v 1 = Nat.max (v 0) (v
1)`. Discharge with `omega` (or `Nat.sub_add_cancel`-style
case split on `v 0 ≤ v 1`).

```lean
@[simp] theorem KMor1.interp_maxK (v : Fin 2 → ℕ) :
    KMor1.maxK.interp v = Nat.max (v 0) (v 1) := by
  simp only [KMor1.maxK, KMor1.interp_comp,
    KMor1.interp_add, KMor1.interp_monus,
    KMor1.interp_proj]
  omega
```

- [ ] **Step 6: Add the level fact via `decide`**

Follow the codebase pattern (`KArith.lean:38, 159, 472,
598, …`): add a concrete `example` line beside the def
that the project linter and downstream consumers can
re-derive.

```lean
example : KMor1.maxK.level = 2 := by decide
theorem KMor1.maxK_level : KMor1.maxK.level ≤ 2 := by
  decide
```

`decide` works here because `level` reduces fully on a
closed term (no `KMor1`-valued metavariables; the
composite is fully spelled out). If `decide` fails on
the open-arity `maxOver` / `pow2_iter` variants later
(Tasks 2-3), the level proof there uses `unfold ; change
… ; Nat.max_le.mpr ⟨…, …⟩` (the
`KSimURMSimulator.lean:975-984` pattern).

- [ ] **Step 7: `lake build`**

Run: `lake build`
Expected: 0 errors, 0 warnings.

- [ ] **Step 8: Axiom audit**

Run: `bash scripts/check-axioms.sh GebLean/Utilities/KArith.lean`
Expected: `[propext, Quot.sound]` only for the three new
`KMor1.maxK`-related declarations (the script auto-discovers
top-level declarations in the file).

- [ ] **Step 9: Append `#guard` test**

In `GebLeanTests/Utilities/KArith.lean`, append:

```lean
#guard (KMor1.maxK).interp ![3, 5] = 5
#guard (KMor1.maxK).interp ![7, 2] = 7
```

- [ ] **Step 10: `lake test`**

Run: `lake test`
Expected: 0 failures.

- [ ] **Step 11: Commit**

```bash
jj describe -m 'feat(ertok): add KMor1.maxK in KArith

Binary max via add ∘ ⟨monus, proj 1⟩. Level ≤ 2. Closed-form
interp lemma `interp_maxK` reduces to `Nat.max` via omega.
Spec §5.1.'
jj new
```

---

## Task 2: `KMor1.maxOver` in `KArith.lean`

**Spec ref:** §5.2.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean` (after `maxK`).
- Modify: `GebLeanTests/Utilities/KArith.lean`.

- [ ] **Step 1: Add the recursive def with `sorry`**

```lean
/-- N-ary maximum over the input vector, as a `K^sim`
morphism of arity `a`. Recursive: `maxOver 0` is the
constant-0 morphism; `maxOver (a+1)` takes the max of
slot 0 with `maxOver a` applied to the tail. Closed
form: `(maxOver a).interp v = Fin.maxOfNat _ v`. Level
≤ 2. -/
def KMor1.maxOver : (a : ℕ) → KMor1 a := sorry
```

- [ ] **Step 2: `lake build` to confirm signature elaborates**

- [ ] **Step 3: Fill the body**

```lean
def KMor1.maxOver : (a : ℕ) → KMor1 a
  | 0     => KMor1.zero  -- constant 0 at arity 0
  | a + 1 =>
      KMor1.comp KMor1.maxK
        (fun i : Fin 2 =>
          match i with
          | ⟨0, _⟩ => KMor1.proj ⟨0, by decide⟩
          | ⟨1, _⟩ => KMor1.comp (KMor1.maxOver a)
                        (fun j : Fin a =>
                          KMor1.proj ⟨j.val + 1,
                            Nat.succ_lt_succ j.isLt⟩))
```

- [ ] **Step 4: Add the interp lemma**

```lean
@[simp] theorem KMor1.interp_maxOver :
    ∀ (a : ℕ) (v : Fin a → ℕ),
      (KMor1.maxOver a).interp v = Fin.maxOfNat a v := by
  intro a
  induction a with
  | zero => intro v
            simp only [KMor1.maxOver, KMor1.interp_zero,
              Fin.maxOfNat]
            rfl
  | succ n ih => intro v
                 simp only [KMor1.maxOver, KMor1.interp_comp,
                   KMor1.interp_maxK, KMor1.interp_proj]
                 -- right component is maxOver n applied to
                 -- the tail; by ih, equals Fin.maxOfNat n
                 -- of the tail. Conclude via Fin.maxOfNat's
                 -- recursive equation.
                 sorry
```

- [ ] **Step 5: Fill the inductive step proof**

The `sorry` discharges via:

```lean
                 rw [ih]
                 -- Both sides now in terms of Fin.maxOfNat.
                 -- LHS: Nat.max (v 0) (Fin.maxOfNat n (v ∘ Fin.succ))
                 -- RHS: Fin.maxOfNat (n+1) v
                 -- Equal by definition of Fin.maxOfNat
                 -- (Fin.foldr (n+1) ...).
                 simp [Fin.maxOfNat, Fin.foldr_succ]
```

If `simp [Fin.maxOfNat, Fin.foldr_succ]` does not close, use
`Fin.maxOfNat_succ` (introduce it locally as a helper lemma
in `LawvereKSim.lean` if not already present).

- [ ] **Step 6: Add the level lemma**

Use the open-arity pattern: `unfold` the def, then chain
`Nat.max_le.mpr ⟨…, …⟩` with `Fin.maxOfNat_le` (mirroring
`KSimURMSimulator.lean:975-984`). The base case `maxOver
0 = KMor1.zero` has level 0; the successor case
`maxOver (n+1)` is a `KMor1.comp` whose level is
`max maxK.level (max-fold of family levels)`, all ≤ 2.

```lean
theorem KMor1.maxOver_level :
    ∀ a, (KMor1.maxOver a).level ≤ 2 := by
  intro a
  induction a with
  | zero =>
      -- maxOver 0 = KMor1.zero; level 0 ≤ 2.
      unfold KMor1.maxOver
      decide
  | succ n ih =>
      -- maxOver (n+1) = comp maxK ⟨proj 0, maxOver n ∘ proj-tail⟩.
      -- Level of comp = max head.level (Fin.maxOfNat family levels).
      -- head.level = maxK.level = 2 (by maxK_level / by decide).
      -- Family: proj 0 has level 0; maxOver n ∘ proj-tail has
      -- level ≤ max ih (Fin.maxOfNat of proj levels = 0).
      unfold KMor1.maxOver
      -- Concrete chain: apply Nat.max_le.mpr to split
      -- comp's level into head + family parts. Then on the
      -- family side, apply Fin.maxOfNat_le and dispatch
      -- per i ∈ Fin 2. Implementer fills the chain by
      -- following the simulate_level pattern.
      sorry
```

The `sorry` here is a TDD intermediate; replace before
the task's final commit. The implementer should follow
the `simulate_level` chain pattern from
`KSimURMSimulator.lean:975-984` (a `change` step followed
by `Nat.max_le.mpr`/`Fin.maxOfNat_le` to split the goal
into per-branch bounds, then `decide` or `exact ih` on
each branch).

- [ ] **Step 7: `lake build`**

- [ ] **Step 8: Axiom audit**

Run: `bash scripts/check-axioms.sh GebLean/Utilities/KArith.lean`
Expected: `[propext, Quot.sound]` only for the three new
`KMor1.maxOver`-related declarations.

- [ ] **Step 9: Append `#guard` tests**

```lean
#guard (KMor1.maxOver 4).interp ![3, 5, 2, 4] = 5
#guard (KMor1.maxOver 0).interp Fin.elim0 = 0
```

- [ ] **Step 10: `lake test`**

- [ ] **Step 11: Commit**

```bash
jj describe -m 'feat(ertok): add KMor1.maxOver in KArith

N-ary max over an input vector, recursive over arity.
Closed-form interp lemma reduces to Fin.maxOfNat (constructive,
axiom-clean per T3 refactor). Level ≤ 2 by induction on arity.
Spec §5.2.'
jj new
```

---

## Task 3: `KMor1.pow2_iter` in `KArith.lean`

**Spec ref:** §5.3.

**Files:**

- Modify: `GebLean/Utilities/KArith.lean` (after `maxOver`).
- Modify: `GebLeanTests/Utilities/KArith.lean`.

- [ ] **Step 1: Add the recursive def**

```lean
/-- R-fold composition of `KMor1.pow2`. `pow2_iter 0` is
the arity-1 identity (i.e., `KMor1.proj 0`); `pow2_iter
(r+1)` composes `pow2` with `pow2_iter r`. Closed form:
`(pow2_iter r).interp ![x] = tower r x`. Level ≤ 2. -/
def KMor1.pow2_iter : (r : ℕ) → KMor1 1
  | 0     => KMor1.proj ⟨0, by decide⟩
  | r + 1 => KMor1.comp KMor1.pow2
              (fun _ : Fin 1 => KMor1.pow2_iter r)
```

- [ ] **Step 2: `lake build`**

- [ ] **Step 3: Add the interp lemma**

```lean
@[simp] theorem KMor1.interp_pow2_iter :
    ∀ (r : ℕ) (v : Fin 1 → ℕ),
      (KMor1.pow2_iter r).interp v = tower r (v 0) := by
  intro r
  induction r with
  | zero => intro v
            -- pow2_iter 0 = KMor1.proj ⟨0, _⟩; interp returns v 0.
            simp [KMor1.pow2_iter, KMor1.interp_proj, tower]
  | succ n ih =>
      intro v
      simp only [KMor1.pow2_iter, KMor1.interp_comp,
        KMor1.interp_pow2]
      -- Inner family is (fun _ : Fin 1 => pow2_iter n) applied at v;
      -- its interp at any index equals (pow2_iter n).interp v = tower n (v 0)
      -- by ih. Reshape and close via tower's recursive equation.
      have h_inner : (fun _ : Fin 1 => (KMor1.pow2_iter n).interp v)
                       = (fun _ : Fin 1 => tower n (v 0)) := by
        funext _; exact ih v
      rw [h_inner]
      simp [tower]
```

This generalised form (`Fin 1 → ℕ` rather than `![x]`)
is the prerequisite the Task 9 `boundExprK_interp` proof
relies on; the `![x]` specialised form would not have
matched the lambda-bound family produced by Task 9's
`KMor1.interp_comp` expansion.

- [ ] **Step 4: Add the level lemma**

```lean
theorem KMor1.pow2_iter_level :
    ∀ r, (KMor1.pow2_iter r).level ≤ 2 := by
  intro r
  induction r with
  | zero =>
      -- pow2_iter 0 = KMor1.proj ⟨0, _⟩; level 0 ≤ 2.
      unfold KMor1.pow2_iter
      decide
  | succ n ih =>
      -- pow2_iter (n+1) = comp pow2 (fun _ => pow2_iter n).
      -- Level = max pow2.level (Fin.maxOfNat fam.level).
      -- pow2.level = 2 (KArith.lean:598); fam is constant
      -- pow2_iter n at every index, ≤ 2 by ih.
      unfold KMor1.pow2_iter
      -- Concrete chain via Nat.max_le.mpr + Fin.maxOfNat_le.
      -- Follow simulate_level pattern (KSimURMSimulator.lean:975).
      sorry
```

Same TDD-intermediate scaffold as Task 2 Step 6.

- [ ] **Step 5: `lake build`**

- [ ] **Step 6: Axiom audit**

Run: `bash scripts/check-axioms.sh GebLean/Utilities/KArith.lean`
Expected: `[propext, Quot.sound]` only for the three new
`KMor1.pow2_iter`-related declarations.

- [ ] **Step 7: Append `#guard` tests**

```lean
#guard (KMor1.pow2_iter 0).interp ![5] = 5
#guard (KMor1.pow2_iter 1).interp ![3] = 8
#guard (KMor1.pow2_iter 2).interp ![2] = 16
```

- [ ] **Step 8: `lake test`**

- [ ] **Step 9: Commit**

```bash
jj describe -m 'feat(ertok): add KMor1.pow2_iter in KArith

R-fold composition of pow2. Closed-form interp lemma reduces
to `tower r x` (the ER-side `A_two_iter` interp form), bridging
the K^sim side to the existing ER A-iterate infrastructure.
Level ≤ 2. Spec §5.3.'
jj new
```

---

## Task 4: Create `RuntimeBound.lean`; `boundExprKParams` skeleton

**Spec ref:** §4.1, §4.2.

**Files:**

- Create: `GebLean/LawvereERKSim/RuntimeBound.lean`.
- Modify: `GebLean/LawvereERKSim.lean` (index re-export
  with `public import`).

- [ ] **Step 1: Create the module skeleton**

```lean
module

public import GebLean.LawvereERKSim.Compiler
public import GebLean.LawvereERKSim.Top
public import GebLean.Utilities.KArith
public import GebLean.Utilities.Tower
public import GebLean.LawvereKSim

/-!
# Runtime bound for `compileER`

This module realises Tourlakis 2018 Corollary 0.1.0.27
specialised to the ER → URM compiler of T2: every ER
morphism's compile-time URM runtime is dominated by a
`tower r (Fin.maxOfNat _ v + offset)` expression, for
explicit `(r, offset) : ℕ × ℕ` computed by ER recursion.
The result is consumed by §6/§7 to define `boundExprK` and
`erToK`.

## Main definitions

- `boundExprKParams : ERMor1 a → ℕ × ℕ` — the recipe.

## Main statements

- `boundExprKParams_dominates` — joint runtime+value bound
  theorem (§4.3 of the spec).

## References

- Tourlakis 2018, *Topics in PR Complexity*, §0.1.0.27,
  §0.1.0.42, §0.1.0.44.
- Spec:
  [`docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`](../../docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md).

## Tags

ertok, runtime-bound, tourlakis, tower
-/

namespace GebLean

open Tower

end GebLean
```

- [ ] **Step 2: `lake build` to confirm imports resolve**

Run: `lake build GebLean.LawvereERKSim.RuntimeBound`
Expected: 0 errors.

- [ ] **Step 3: Add the recipe def**

Inside the `namespace GebLean` block, add:

```lean
/-- Per-ER-constructor recipe returning the tower height
`mu_e` and offset `offset_e` jointly bounding both the URM
runtime of `compileER e` and the ER value `e.interp v` by
`tower mu_e (Fin.maxOfNat _ v + offset_e)`. -/
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

- [ ] **Step 4: `lake build`**

- [ ] **Step 5: Axiom audit on `boundExprKParams`**

Run: `bash scripts/check-axioms.sh GebLean/LawvereERKSim/RuntimeBound.lean`
Expected: `[propext, Quot.sound]` only for
`boundExprKParams` (pure Nat recursion; no Classical).

- [ ] **Step 6: Update `GebLean/LawvereERKSim.lean` index**

Add a `public import GebLean.LawvereERKSim.RuntimeBound`
line in the index file.

- [ ] **Step 7: `lake build`** (full project)

- [ ] **Step 8: Commit**

```bash
jj describe -m 'feat(ertok): scaffold RuntimeBound; add boundExprKParams

Per-ER-constructor recipe returning (mu_e, offset_e). Recipe
table per spec §4.2: zero (0,3); succ/proj/sub (2,16-24);
comp (mu_f + max mu_gs + 6, offset_f + max offset_gs + 4·a + k + 8);
bsum (mu_f+6, offset_f + k + compileER_numRegs f + 32);
bprod (mu_f+9, offset_f + k + compileER_numRegs f + 44).
Constructive (Fin.maxOfNat from T3).
Spec §4.1, §4.2.'
jj new
```

---

## Task 5: `boundExprKParams_dominates` atom cases

**Spec ref:** §4.3 atom rationale.

**Files:**

- Modify: `GebLean/LawvereERKSim/RuntimeBound.lean`.

- [ ] **Step 1: Add the theorem signature with `sorry`**

```lean
/-- Joint runtime+value bound: `compileER_runtime e v ≤
tower mu_e (Fin.maxOfNat _ v + offset_e)` AND `e.interp v
≤ tower mu_e (Fin.maxOfNat _ v + offset_e)`, where
`(mu_e, offset_e) = boundExprKParams e`. Proof by
structural induction on `e`. -/
theorem boundExprKParams_dominates :
    {a : ℕ} → (e : ERMor1 a) → (v : Fin a → ℕ) →
    compileER_runtime e v ≤
        tower (boundExprKParams e).1
              (Fin.maxOfNat _ v + (boundExprKParams e).2) ∧
    e.interp v ≤
        tower (boundExprKParams e).1
              (Fin.maxOfNat _ v + (boundExprKParams e).2) := by
  intro a e v
  induction e with
  | zero    => sorry
  | succ    => sorry
  | proj i  => sorry
  | sub     => sorry
  | comp f gs ih_f ih_gs => sorry
  | bsum f ih_f          => sorry
  | bprod f ih_f         => sorry
```

- [ ] **Step 2: `lake build` to confirm the induction skeleton elaborates**

- [ ] **Step 3: Fill the `zero` case**

Replace the `zero` `sorry` with:

```lean
  | zero    =>
      simp only [compileER_runtime, ERMor1.interp_zero,
        boundExprKParams, tower]
      omega
```

`tower 0 x = x` so the bound is `Fin.maxOfNat _ v + 3 ≥ 3`,
which holds. Both conjuncts close with `omega`.

- [ ] **Step 4: Fill the `succ` case**

```lean
  | succ    =>
      simp only [compileER_runtime, ERMor1.interp_succ,
        boundExprKParams]
      -- Goal: 12 + 10·v 0 ≤ tower 2 m ∧ v 0 + 1 ≤ tower 2 m
      -- where m = Fin.maxOfNat _ v + 16.
      -- v 0 ≤ Fin.maxOfNat _ v ≤ m. tower 2 m = 2^(2^m).
      -- One mul_tower_le_tower_add_two on 10 · m ≤ tower 2 m.
      have h_m : Fin.maxOfNat _ v + 16 ≥ 16 := by omega
      have h_v0 : v 0 ≤ Fin.maxOfNat _ v :=
        Fin.le_maxOfNat _ v ⟨0, by decide⟩
      refine ⟨?_, ?_⟩
      · -- runtime: 12 + 10·v 0 ≤ tower 2 m
        calc 12 + 10 * v 0
            ≤ 10 * (v 0 + 2) := by omega
          _ ≤ 10 * (Fin.maxOfNat _ v + 16) := by
              have := h_v0; omega
          _ ≤ (Fin.maxOfNat _ v + 16) *
              (Fin.maxOfNat _ v + 16) := by
              nlinarith [h_m]
          _ = (Fin.maxOfNat _ v + 16) *
              tower 0 (Fin.maxOfNat _ v + 16) := by
              simp [tower]
          _ ≤ tower 2 (Fin.maxOfNat _ v + 16) := by
              apply Tower.mul_tower_le_tower_add_two
              · omega
      · -- value: v 0 + 1 ≤ tower 2 m
        have : v 0 + 1 ≤ Fin.maxOfNat _ v + 16 := by omega
        exact this.trans (Tower.self_le_tower _ _)
```

(If `nlinarith` is too heavy or `self_le_tower`'s exact
signature differs, substitute `Tower.tower_mono_right` or
explicit `Nat.le_pow` chains; consult `Tower.lean` headers
for the actual lemma surface.)

- [ ] **Step 5: Fill the `proj` case**

```lean
  | proj i  =>
      simp only [compileER_runtime, ERMor1.interp_proj,
        boundExprKParams]
      have h_vi : v i ≤ Fin.maxOfNat _ v := Fin.le_maxOfNat _ v i
      -- Same shape as succ; just `v i` instead of `v 0`.
      refine ⟨?_, ?_⟩
      · calc 11 + 10 * v i
            ≤ 10 * (v i + 2) := by omega
          _ ≤ 10 * (Fin.maxOfNat _ v + 16) := by
              have := h_vi; omega
          _ ≤ (Fin.maxOfNat _ v + 16) *
              tower 0 (Fin.maxOfNat _ v + 16) := by
              simp [tower]; nlinarith
          _ ≤ tower 2 (Fin.maxOfNat _ v + 16) := by
              apply Tower.mul_tower_le_tower_add_two; omega
      · have : v i ≤ Fin.maxOfNat _ v + 16 := by
          have := h_vi; omega
        exact this.trans (Tower.self_le_tower _ _)
```

- [ ] **Step 6: Fill the `sub` case**

```lean
  | sub     =>
      simp only [compileER_runtime, ERMor1.interp_sub,
        boundExprKParams]
      have h_v0 : v 0 ≤ Fin.maxOfNat _ v :=
        Fin.le_maxOfNat _ v ⟨0, by decide⟩
      have h_v1 : v 1 ≤ Fin.maxOfNat _ v :=
        Fin.le_maxOfNat _ v ⟨1, by decide⟩
      refine ⟨?_, ?_⟩
      · -- 20 + 10·v 0 + 10·v 1 ≤ tower 2 m
        calc 20 + 10 * v 0 + 10 * v 1
            ≤ 20 * (Fin.maxOfNat _ v + 24) := by
              have := h_v0; have := h_v1; omega
          _ ≤ (Fin.maxOfNat _ v + 24) *
              tower 0 (Fin.maxOfNat _ v + 24) := by
              simp [tower]; nlinarith
          _ ≤ tower 2 (Fin.maxOfNat _ v + 24) := by
              apply Tower.mul_tower_le_tower_add_two; omega
      · -- v 0 ∸ v 1 ≤ v 0 ≤ Fin.maxOfNat _ v + 24 ≤ tower 2 _
        have : v 0 ∸ v 1 ≤ Fin.maxOfNat _ v + 24 := by
          have := h_v0; omega
        exact this.trans (Tower.self_le_tower _ _)
```

- [ ] **Step 7: `lake build`** (with comp/bsum/bprod still
`sorry`)

Expected: build fails with three `sorry` warnings
(comp/bsum/bprod still pending). Atom proofs verified
elaborate.

- [ ] **Step 8: Commit (with remaining `sorry`s noted as
WIP)**

Do NOT commit while `sorry` is present in committed code.
Per the project rule, `sorry` is permitted only between
commits while a skill needs it. Since this commit would
land `sorry`-bearing code, defer the commit until Task 8
completes all four inductive cases. Mark this task as
*partially complete* and proceed to Task 6 in the same
working-copy state.

---

## Task 6: `boundExprKParams_dominates` comp case

**Spec ref:** §4.2 comp rationale (steps i, ii, iii); §4.3
comp proof outline.

**Files:**

- Modify: `GebLean/LawvereERKSim/RuntimeBound.lean` (replace
  the `comp` `sorry`).

- [ ] **Step 1: Fill the `comp` case skeleton**

```lean
  | comp f gs ih_f ih_gs =>
      simp only [compileER_runtime, ERMor1.interp_comp,
        boundExprKParams]
      set m := Fin.maxOfNat _ v +
        ((boundExprKParams f).2 +
         Fin.maxOfNat _ (fun i => (boundExprKParams (gs i)).2)
         + 4 * a + k + 8)
      set mu_f := (boundExprKParams f).1
      set mu_g := Fin.maxOfNat _
                    (fun i => (boundExprKParams (gs i)).1)
      -- Goal:
      -- (glue + rt(f at inner) + 2 ≤ tower (mu_f + mu_g + 6) m)
      -- ∧ (f.interp inner ≤ tower (mu_f + mu_g + 6) m)
      -- where inner i = (gs i).interp v.
      sorry
```

- [ ] **Step 2: Establish the value bound on `inner`**

Before refining into the conjunction, derive:

```lean
      have h_inner_val :
          ∀ i, (gs i).interp v ≤ tower mu_g m := by
        intro i
        have ih_i := (ih_gs i v).2  -- value bound on gs i
        have h_mu_le :
            (boundExprKParams (gs i)).1 ≤ mu_g :=
          Fin.le_maxOfNat _ _ i
        have h_o_le :
            (boundExprKParams (gs i)).2 ≤ _ := by
          -- offset of gs i ≤ Fin.maxOfNat _ (fun … offset)
          -- ≤ the offset_e for the whole comp expression
          apply Nat.le_add_right_of_le
          apply Fin.le_maxOfNat
        -- ih_i: (gs i).interp v ≤ tower (mu_{gs i}) (… + offset_{gs i})
        -- Bound:                ≤ tower mu_g m   by tower_mono_left + tower_mono_right
        calc (gs i).interp v
            ≤ tower (boundExprKParams (gs i)).1
                (Fin.maxOfNat _ v + (boundExprKParams (gs i)).2) := ih_i
          _ ≤ tower mu_g m := by
              -- Synthesise "tower_mono_both" from
              -- tower_mono_left + tower_mono_right.
              -- LHS exponent: (boundExprKParams (gs i)).1 ≤ mu_g
              --   by Fin.le_maxOfNat.
              -- LHS argument: Fin.maxOfNat _ v + (boundExprKParams (gs i)).2
              --   ≤ m by definition of m and omega.
              exact (Tower.tower_mono_left
                      (Fin.le_maxOfNat _ _ i) _).trans
                    (Tower.tower_mono_right _ (by omega))
```

- [ ] **Step 3: Establish the value bound on `Fin.maxOfNat _ inner`**

```lean
      have h_inner_max :
          Fin.maxOfNat _ (fun i => (gs i).interp v)
            ≤ tower mu_g m := by
        apply Fin.maxOfNat_le
        intro i
        exact h_inner_val i
```

- [ ] **Step 4: Apply IH-f at the specialised inner vector + tower_comp**

```lean
      have h_f_rt :
          compileER_runtime f (fun i => (gs i).interp v)
            ≤ tower (mu_f + mu_g + 2) m := by
        have ih_f_inner := (ih_f (fun i => (gs i).interp v)).1
        -- ih_f_inner: rt(f, inner)
        --   ≤ tower mu_f (Fin.maxOfNat _ inner + offset_f)
        -- ≤ tower mu_f (tower mu_g m + offset_f)        by h_inner_max
        -- absorb offset_f: ≤ tower mu_f (tower (mu_g + 2) m) by mul_tower
        -- = tower (mu_f + mu_g + 2) m                    by tower_comp
        calc compileER_runtime f
                (fun i => (gs i).interp v)
            ≤ tower mu_f
                (Fin.maxOfNat _ (fun i => (gs i).interp v)
                  + (boundExprKParams f).2) := ih_f_inner
          _ ≤ tower mu_f (tower mu_g m + (boundExprKParams f).2) := by
              apply Tower.tower_mono_right
              exact Nat.add_le_add_right h_inner_max _
          _ ≤ tower mu_f (tower (mu_g + 2) m) := by
              apply Tower.tower_mono_right
              -- offset_f absorption: X + offset_f ≤ 2X ≤ m · X ≤ tower 2 X
              -- where X = tower mu_g m.
              -- Synthesise tower mu_g m ≥ 2 from self_le_tower:
              --   m ≥ 2 (since offset ≥ 8 ≥ 2),
              --   m ≤ tower mu_g m by self_le_tower,
              --   therefore tower mu_g m ≥ 2.
              have h_m_ge_2 : m ≥ 2 := by
                -- m = Fin.maxOfNat _ v + offset, offset ≥ 8.
                omega
              have h_X_ge_m : tower mu_g m ≥ m :=
                Tower.self_le_tower mu_g m
              have h_X_ge_2 : tower mu_g m ≥ 2 :=
                h_X_ge_m.trans' h_m_ge_2 |>.le
              -- (offset_f ≤ tower mu_g m: similarly by
              --  self_le_tower if offset_f ≤ m; offsets are
              --  small additive constants compared with m.)
              calc tower mu_g m + (boundExprKParams f).2
                  ≤ 2 * tower mu_g m := by
                    have h_off_le : (boundExprKParams f).2 ≤ tower mu_g m := by
                      have : (boundExprKParams f).2 ≤ m := by omega
                      exact this.trans h_X_ge_m
                    omega
                _ ≤ m * tower mu_g m := by
                    have : m ≥ 2 := by omega
                    nlinarith
                _ = m * tower 0 (tower mu_g m) := by simp [tower]
                _ ≤ tower 2 (tower mu_g m) := by
                    apply Tower.mul_tower_le_tower_add_two
                    omega
                _ = tower (mu_g + 2) m := by
                    rw [Tower.tower_comp]
          _ = tower (mu_f + mu_g + 2) m := by
              rw [Tower.tower_comp]
              ring_nf
```

- [ ] **Step 5: Handle the `glue` (Σ over gs i) factor**

```lean
      have h_glue :
          ((List.finRange k).map
            (fun i => compileER_runtime (gs i) v
              + 4 + 5 * (gs i).interp v
              + 9 * ((List.finRange a).map v).foldl (· + ·) 0
              + 2 * a)).foldl (· + ·) 0
            ≤ tower (mu_g + 6) m := by
        -- Each summand: rt(gs i) ≤ tower mu_g m (by IH-gs),
        -- (gs i).interp v ≤ tower mu_g m (by h_inner_val),
        -- v_total = Σ_j v j ≤ a · Fin.maxOfNat _ v ≤ m · m
        -- (since `a ≤ m` from the `4·a + k + 8` portion of offset),
        -- the `+ 4 + 2·a` constants are ≤ m for offset ≥ 4·a + k + 8.
        -- Σ over i (k summands): the `k`-fold loop count is bounded
        -- by `k ≤ m` (from the explicit `+ k` term in the offset),
        -- absorbing the k-fold via `mul_tower_le_tower_add_two`
        -- as `k · tower (mu_g + 4) m ≤ m · tower (mu_g + 4) m
        -- ≤ tower (mu_g + 6) m`.
        -- absorbed by mul_tower_le_tower_add_two.
        sorry
```

This sub-step is the bulkiest. The implementer should
break it into named local lemmas if needed; expected
length ~40-60 lines including all the chain of inequalities.

- [ ] **Step 6: Combine `h_glue + h_f_rt + 2` into the
final bound**

```lean
      have h_runtime_total :
          ((List.finRange k).map ...).foldl (· + ·) 0
            + compileER_runtime f (fun i => (gs i).interp v) + 2
            ≤ tower (mu_f + mu_g + 6) m := by
        -- Per spec §4.2 comp rationale (post-amendment):
        -- glue ≤ tower (mu_g + 6) m and rt(f) ≤
        -- tower (mu_f + mu_g + 2) m. For `mu_f ≥ 2`, both
        -- ≤ tower (mu_f + mu_g + 4) m. The sum-of-three step
        -- closes as glue + rt(f) + 2 ≤ 3·tower (mu_f + mu_g
        -- + 4) m ≤ m·tower (mu_f + mu_g + 4) m ≤ tower
        -- (mu_f + mu_g + 6) m via one
        -- `mul_tower_le_tower_add_two`. The `+ k` offset
        -- addition ensures `k ≤ m`, enabling the inner
        -- `k · tower (mu_g + 4) m ≤ m · tower (mu_g + 4) m
        -- ≤ tower (mu_g + 6) m` step in the glue bound.
        sorry
```

- [ ] **Step 7: Value bound conjunct**

```lean
      have h_value :
          f.interp (fun i => (gs i).interp v)
            ≤ tower (mu_f + mu_g + 6) m := by
        have ih_f_val := (ih_f (fun i => (gs i).interp v)).2
        calc f.interp (fun i => (gs i).interp v)
            ≤ tower mu_f
                (Fin.maxOfNat _ (fun i => (gs i).interp v)
                  + (boundExprKParams f).2) := ih_f_val
          _ ≤ tower mu_f (tower (mu_g + 2) m) := by
              apply Tower.tower_mono_right
              -- same chain as in h_f_rt
              sorry
          _ = tower (mu_f + mu_g + 2) m := by
              rw [Tower.tower_comp]; ring_nf
          _ ≤ tower (mu_f + mu_g + 6) m :=
              Tower.tower_mono_left (by omega) _
```

- [ ] **Step 8: Combine the two conjuncts and close**

```lean
      refine ⟨h_runtime_total, h_value⟩
```

- [ ] **Step 9: `lake build`**

Run: `lake build`
Expected: 0 errors. `boundExprKParams_dominates` discharges
the `comp` case fully.

- [ ] **Step 10: Per-case axiom check (informational, not commit-gating)**

The full theorem still has bsum/bprod `sorry`s; defer the
axiom audit and commit until Task 8 completes.

---

## Task 7: `boundExprKParams_dominates` bsum case

**Spec ref:** §4.2 bsum rationale; §4.3 bsum proof outline.

**Files:**

- Modify: `GebLean/LawvereERKSim/RuntimeBound.lean` (replace
  the `bsum` `sorry`).

- [ ] **Step 1: Fill the `bsum` case skeleton**

```lean
  | bsum f ih_f =>
      simp only [compileER_runtime, ERMor1.interp_bsum,
        boundExprKParams]
      set m := Fin.maxOfNat _ v +
        ((boundExprKParams f).2 + k + LawvereERKSim.compileER_numRegs f + 32)
      set mu_f := (boundExprKParams f).1
      -- Goal:
      -- (30 + 10·v 0 + Σ_{i<v 0} perIter_f(i) ≤ tower (mu_f + 6) m)
      -- ∧ (natBSum (v 0) (f.interp ∘ ctx_f) ≤ tower (mu_f + 6) m)
      sorry
```

- [ ] **Step 2: Per-iteration bound (runtime side)**

```lean
      have h_perIter :
          ∀ i < v 0, perIter_f i ≤ tower mu_f m := by
        intro i hi
        -- perIter_f i contains compileER_runtime f ctx_f
        -- where ctx_f = Fin.cons i (Fin.tail v).
        -- Note: This case will surface Fin.lastCases_castSucc
        -- via simp on Fin.cons normalisation, per spec §11.
        -- Carry AXIOM_ALLOW annotation accordingly.
        sorry
```

**AXIOM_ALLOW annotation requirement:** before the
declaration, add the comment line:

```lean
-- AXIOM_ALLOW: Classical.choice (Fin.lastCases_castSucc via
-- simp on perIter_f's Fin.cons / Fin.tail normalisation;
-- per spec §11 and .claude/rules/lean-coding.md § Accepted
-- exceptions).
```

This applies to the enclosing theorem
`boundExprKParams_dominates`, not to a local `have`. Place
the annotation immediately above the `theorem` keyword (or
in its `/-- … -/` docstring per the rule).

- [ ] **Step 3: Per-iteration bound (value side)**

```lean
      have h_perIter_val :
          ∀ i < v 0,
            f.interp (Fin.cons i (Fin.tail v)) ≤ tower mu_f m := by
        intro i hi
        have ih := (ih_f (Fin.cons i (Fin.tail v))).2
        -- ih bounds f.interp by tower mu_f (Fin.maxOfNat _
        --   (Fin.cons i (Fin.tail v)) + offset_f).
        -- Fin.maxOfNat _ (Fin.cons i (Fin.tail v))
        --   ≤ max i (Fin.maxOfNat _ (Fin.tail v))
        --   ≤ Fin.maxOfNat _ v
        -- (since i < v 0 ≤ Fin.maxOfNat _ v).
        sorry
```

- [ ] **Step 4: Sum bound via `mul_tower_le_tower_add_two`**

```lean
      have h_sum :
          ((List.range (v 0)).map (fun i => perIter_f i))
            .foldl (· + ·) 0 ≤ tower (mu_f + 6) m := by
        -- Σ_{i<v 0} perIter_f i ≤ v 0 · tower mu_f m
        --   ≤ m · tower mu_f m            (v 0 ≤ m)
        --   ≤ tower (mu_f + 6) m          (mul_tower_le_tower_add_two)
        sorry
```

- [ ] **Step 5: Combine runtime conjunct**

```lean
      have h_runtime :
          30 + 10 * v 0 +
            ((List.range (v 0)).map (fun i => perIter_f i))
              .foldl (· + ·) 0
            ≤ tower (mu_f + 6) m := by
        -- 30 + 10 v 0 ≤ 10 · m + 30 ≤ tower 2 m ≤ tower (mu_f + 6) m
        -- Sum h_sum.
        sorry
```

- [ ] **Step 6: Value conjunct**

```lean
      have h_value :
          natBSum (v 0)
            (fun j => f.interp (Fin.cons j (Fin.tail v)))
            ≤ tower (mu_f + 6) m := by
        -- natBSum (v 0) g ≤ v 0 · (max over j of g j)
        --   ≤ m · tower mu_f m
        --   ≤ tower (mu_f + 6) m
        sorry
```

- [ ] **Step 7: Close the bsum case**

```lean
      exact ⟨h_runtime, h_value⟩
```

- [ ] **Step 8: `lake build`**

Expected: 0 errors apart from any remaining `sorry`
warnings on bprod and the sub-proofs.

---

## Task 8: `boundExprKParams_dominates` bprod case

**Spec ref:** §4.2 bprod rationale; §4.3 bprod proof outline.

**Files:**

- Modify: `GebLean/LawvereERKSim/RuntimeBound.lean` (replace
  the `bprod` `sorry`).

- [ ] **Step 1: Fill the `bprod` case skeleton**

```lean
  | bprod f ih_f =>
      simp only [compileER_runtime, ERMor1.interp_bprod,
        boundExprKParams]
      set m := Fin.maxOfNat _ v +
        ((boundExprKParams f).2 + k + LawvereERKSim.compileER_numRegs f + 44)
      set mu_f := (boundExprKParams f).1
      -- Goal:
      -- runtime ≤ tower (mu_f + 9) m
      -- ∧ natBProd (v 0) (f.interp ∘ ctx_f) ≤ tower (mu_f + 9) m
      sorry
```

- [ ] **Step 2: Per-iteration f-interp bound (same as bsum)**

```lean
      have h_perIter_val :
          ∀ i < v 0,
            f.interp (Fin.cons i (Fin.tail v)) ≤ tower mu_f m := by
        intro i hi
        -- Same shape as bsum case Step 3; lift ctx_f bound.
        sorry
```

- [ ] **Step 3: Running-product bound via
`tower_pow_le_tower_add_three`**

```lean
      have h_running_prod :
          ∀ i ≤ v 0,
            natBProd i (fun j =>
              f.interp (Fin.cons j (Fin.tail v)))
              ≤ tower (mu_f + 3) m := by
        intro i hi
        -- natBProd i (g) = Π_{j<i} g j
        -- ≤ (max over j of g j)^i ≤ (tower mu_f m)^i
        -- ≤ (tower mu_f m)^m              (i ≤ v 0 ≤ m)
        -- ≤ tower (mu_f + 3) m            (tower_pow_le_tower_add_three)
        sorry
```

- [ ] **Step 4: A_i · B_i bound**

```lean
      have h_A_B :
          ∀ i < v 0,
            let A_i := natBProd i (fun j =>
              f.interp (Fin.cons j (Fin.tail v)))
            let B_i := f.interp (Fin.cons i (Fin.tail v))
            A_i * B_i ≤ tower (mu_f + 3) m := by
        intro i hi
        -- A_i · B_i = natBProd (i+1) g ≤ tower (mu_f + 3) m
        sorry
```

- [ ] **Step 5: Sum bound: `Σ_{i<v 0} 9·A_i·B_i ≤
tower (mu_f + 7) m`**

```lean
      have h_sum_9AB :
          ((List.range (v 0)).map (fun i =>
            9 * (natBProd i (fun j =>
              f.interp (Fin.cons j (Fin.tail v))) *
              f.interp (Fin.cons i (Fin.tail v)))))
              .foldl (· + ·) 0
            ≤ tower (mu_f + 7) m := by
        -- Let T := A_i · B_i ≤ tower (mu_f + 3) m via h_A_B.
        -- The 9 factor pulls out of the fold (e.g. via
        -- `List.sum_map_mul_left` or an explicit fold lemma):
        -- Σ_i 9·(A_i·B_i) = 9·Σ_i (A_i·B_i).
        -- Σ_i (A_i·B_i) ≤ v 0·T ≤ m·T (v 0 ≤ m).
        -- So Σ_i 9·(A_i·B_i) ≤ 9·m·T ≤ m·m·T (9 ≤ m, since
        -- m ≥ 44 from the bprod offset additive constant).
        --        = m·(m·T) ≤ m·tower (mu_f + 5) m
        --                  (mul_tower_le_tower_add_two on m·T,
        --                   taking mu_f+3 to mu_f+5)
        --        ≤ tower (mu_f + 7) m
        --                  (mul_tower_le_tower_add_two on
        --                   m·tower (mu_f + 5) m, taking
        --                   mu_f+5 to mu_f+7).
        -- The final lift from mu_f+7 to mu_f+9 happens in
        -- h_runtime (Step 7) via the cross-parts combining
        -- mul step.
        sorry
```

- [ ] **Step 6: Per-iteration runtime bound**

```lean
      have h_perIter_runtime :
          ∀ i < v 0,
            (compileER_runtime f (Fin.cons i (Fin.tail v))
              + 60 + 2 * (k + 1)
              + 10 * (i + outerSum)
              + 9 * (A_i * B_i + small_terms)
              + nRegs_f) ≤ tower (mu_f + 7) m := by
        -- Per-iter naturally lands at mu_f + 7: parts at
        -- tower (mu_f + 5) m (9·A_i·B_i and 4·A_i) plus
        -- smaller IH and overhead contributions all combine
        -- under tower (mu_f + 7) m via one mul step from
        -- their sum.
        sorry
```

(Use the precise term names from
`Compiler.lean:1753-1770`.)

- [ ] **Step 7: Combine runtime conjunct**

```lean
      have h_runtime : (40 + 10 * v 0 + Σ perIter) ≤
          tower (mu_f + 9) m := by
        sorry
```

- [ ] **Step 8: Value conjunct via
`tower_pow_le_tower_add_three`**

```lean
      have h_value :
          natBProd (v 0)
            (fun j => f.interp (Fin.cons j (Fin.tail v)))
            ≤ tower (mu_f + 9) m := by
        have h3 := h_running_prod (v 0) (le_refl _)
        exact h3.trans
          (Tower.tower_mono_left (by omega) _)
```

(The value only needs `+ 3`, but the recipe carries `+ 9`
to dominate the runtime; the value conjunct lifts via
`tower_mono_left`.)

- [ ] **Step 9: Close**

```lean
      exact ⟨h_runtime, h_value⟩
```

- [ ] **Step 10: `lake build` clean**

All four cases of `boundExprKParams_dominates` discharge.
Expected: 0 errors, 0 warnings (no `sorry` remaining).

- [ ] **Step 11: Axiom audit**

Run: `bash scripts/check-axioms.sh GebLean/LawvereERKSim/RuntimeBound.lean`

Expected: `boundExprKParams` uses `[propext, Quot.sound]`;
`boundExprKParams_dominates` uses
`[propext, Classical.choice, Quot.sound]` with the
AXIOM_ALLOW annotation explaining
`Fin.lastCases_castSucc` exposure in the bsum/bprod cases.

- [ ] **Step 12: Commit (Tasks 5–8 land together)**

```bash
jj describe -m 'feat(ertok): land boundExprKParams_dominates

Joint runtime+value bound theorem against tower mu_e
(Fin.maxOfNat _ v + offset_e). Structural induction on
ERMor1 with all four atom cases + comp + bsum + bprod.

- Atoms: one mul_tower_le_tower_add_two for the linear
  coefficient.
- Comp: inner-offset absorption (+2), tower_comp, outer
  v_total absorption (+4), totalling mu_f + mu_g + 6.
- Bsum: four mul_tower_le_tower_add_two steps (IH-sum,
  5·IH-sum, per-iter overhead m³-bound, final collapse),
  totalling mu_f + 6.
- Bprod: tower_pow_le_tower_add_three for the running
  product (+3) plus six per-iter contribution bounds and
  a final mul_tower_le_tower_add_two collapse, totalling
  mu_f + 9.

Carries AXIOM_ALLOW: Classical.choice annotation on the
bsum and bprod cases (Fin.lastCases_castSucc via simp on
perIter ctx_f). Spec §4.3, §11.'
jj new
```

---

## Task 9: `boundExprK` def + level + interp + dominates

**Spec ref:** §6.

**Files:**

- Modify: `GebLean/LawvereERKSim/RuntimeBound.lean`.

- [ ] **Step 1: Add `boundExprK` def**

```lean
/-- The K^sim majorant of `compileER_runtime e` at level
≤ 2. Assembled from `pow2_iter` (the K^sim realisation of
`A_2^r`), `maxOver` (the K^sim realisation of
`Fin.maxOfNat`), `add`, and `natK'`. -/
def boundExprK : {a : ℕ} → ERMor1 a → KMor1 a := fun e =>
  let p := boundExprKParams e
  KMor1.comp
    (KMor1.pow2_iter p.1)
    (fun _ : Fin 1 =>
      KMor1.comp KMor1.add
        (fun i : Fin 2 =>
          match i with
          | ⟨0, _⟩ => KMor1.maxOver _
          | ⟨1, _⟩ => KMor1.natK' _ p.2))
```

- [ ] **Step 2: `lake build`**

- [ ] **Step 3: Add the interp lemma**

Prerequisite: in Task 3, generalise the
`KMor1.interp_pow2_iter` form from the arity-1
literal `![x]` to "any `Fin 1 → ℕ` family". The actual
statement should be:

```lean
@[simp] theorem KMor1.interp_pow2_iter (r : ℕ) (v : Fin 1 → ℕ) :
    (KMor1.pow2_iter r).interp v = tower r (v 0)
```

(rather than the `![x]` form). The proof's `simp [tower]`
step then closes after `Fin 0`-vector destruction. Update
Task 3 Step 3 accordingly.

With that prerequisite, the `boundExprK_interp` body
discharges via:

```lean
@[simp] theorem boundExprK_interp
    {a : ℕ} (e : ERMor1 a) (v : Fin a → ℕ) :
    (boundExprK e).interp v
      = tower (boundExprKParams e).1
              (Fin.maxOfNat _ v + (boundExprKParams e).2) := by
  -- Expand boundExprK and apply the @[simp] interp lemmas
  -- on pow2_iter, add, maxOver, natK'. The `match i` on
  -- Fin 2 dispatches symbolically; close with `rfl` once
  -- the Fin.cons/Fin.elim0 normalisation lands.
  simp only [boundExprK, KMor1.interp_comp,
    KMor1.interp_pow2_iter, KMor1.interp_add,
    KMor1.interp_maxOver, KMor1.interp_natK']
  -- Goal at this point should be a literal equality between
  -- `tower mu (...)` and `tower mu (Fin.maxOfNat _ v + offset)`.
  -- If the `match i with | ⟨0,_⟩ => ... | ⟨1,_⟩ => ...` does
  -- not reduce on the LHS, follow with `simp only [Fin.cons_zero,
  -- Fin.cons_succ]` or an explicit `Fin.cases` rewrite.
  rfl  -- or: `congr 1; omega`, if the goal needs offset arithmetic
```

- [ ] **Step 4: Add the level lemma**

```lean
theorem boundExprK_level
    {a : ℕ} (e : ERMor1 a) : (boundExprK e).level ≤ 2 := by
  -- boundExprK = comp pow2_iter ⟨comp add ⟨maxOver a, natK' a _⟩⟩.
  -- Each leaf is level ≤ 2: pow2_iter_level, add (level 1),
  -- maxOver_level, natK' (level 0). The Nat.max + Fin.maxOfNat
  -- fold stays ≤ 2.
  unfold boundExprK
  -- Concrete chain via Nat.max_le.mpr + Fin.maxOfNat_le, splitting
  -- the comp into head + family. The implementer applies the
  -- per-leaf lemmas (pow2_iter_level, maxOver_level, etc.) at
  -- each branch.
  sorry
```

Same TDD-intermediate scaffold as Tasks 2-3 level proofs.

- [ ] **Step 5: Add the domination lemma**

```lean
theorem boundExprK_dominates
    {a : ℕ} (e : ERMor1 a) (v : Fin a → ℕ) :
    compileER_runtime e v ≤ (boundExprK e).interp v := by
  rw [boundExprK_interp]
  exact (boundExprKParams_dominates e v).1
```

- [ ] **Step 6: `lake build`**

- [ ] **Step 7: Axiom audit**

Run: `bash scripts/check-axioms.sh GebLean/LawvereERKSim/RuntimeBound.lean`

Expected: `boundExprK`, `boundExprK_interp`,
`boundExprK_level` are `[propext, Quot.sound]`;
`boundExprK_dominates` inherits AXIOM_ALLOW from
`boundExprKParams_dominates` (not a new annotated site).

- [ ] **Step 8: Commit**

```bash
jj describe -m $'feat(ertok): assemble boundExprK from pow2_iter, maxOver, natK\'\n\nComposite shape: pow2_iter mu ∘ (add ∘ ⟨maxOver a, natK\' a offset⟩).
Closed-form interp lemma reduces to tower mu (Fin.maxOfNat _ v + offset).
Level ≤ 2 by composition. boundExprK_dominates chains
boundExprK_interp with boundExprKParams_dominates'\''s runtime conjunct.
Spec §6.'
jj new
```

---

## Task 10: Create `ErToK.lean`; `erToK` + level + interp

**Spec ref:** §7.

**Files:**

- Create: `GebLean/LawvereERKSim/ErToK.lean`.
- Modify: `GebLean/LawvereERKSim.lean` index.

- [ ] **Step 1: Create the module skeleton**

```lean
module

public import GebLean.LawvereERKSim.Compiler
public import GebLean.LawvereERKSim.Top
public import GebLean.LawvereERKSim.RuntimeBound
public import GebLean.Utilities.KSimURMSimulator

/-!
# `erToK`: single-output ER → K^sim_2 functor on morphisms

This module composes T3's URM simulator with T4's K^sim
runtime bound to produce a level-≤ 2 K^sim morphism whose
interp agrees with the original ER morphism.

## Main definitions

- `erToK : ERMor1 a → KMor1 a`.

## Main statements

- `erToK_level : (erToK e).level ≤ 2`.
- `erToK_interp : (erToK e).interp v = e.interp v`.

## References

- Spec:
  [`docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`](../../docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md)
  §7.

## Tags

ertok, simulator, runtime-bound
-/

namespace GebLean

end GebLean
```

- [ ] **Step 2: `lake build`**

- [ ] **Step 3: Add the `erToK` def**

```lean
/-- ER morphism `e : ERMor1 a` as a level-≤ 2 K^sim
morphism of the same arity, via simulation of `compileER
e` for `boundExprK e` steps. Spec §7.1. -/
def erToK : {a : ℕ} → ERMor1 a → KMor1 a := fun e =>
  KMor1.comp
    (KSimURMSimulator.simulate (compileER e))
    (Fin.cons (boundExprK e)
      (fun i : Fin _ => KMor1.proj i))
```

- [ ] **Step 4: `lake build`**

- [ ] **Step 5: Add the level lemma**

```lean
theorem erToK_level
    {a : ℕ} (e : ERMor1 a) : (erToK e).level ≤ 2 := by
  -- erToK = comp (simulate (compileER e))
  --              (Fin.cons (boundExprK e) projections).
  -- Level = max simulate.level (Fin.maxOfNat family-levels).
  -- simulate_level ≤ 2; family slot 0 = boundExprK
  -- (boundExprK_level ≤ 2); other slots = KMor1.proj (level 0).
  unfold erToK
  -- Concrete chain via Nat.max_le.mpr + Fin.maxOfNat_le;
  -- per-i dispatch via `cases i using Fin.cases` on
  -- `Fin.cons`'s components. Implementer fills.
  sorry
```

- [ ] **Step 6: Add the interp lemma**

Add the AXIOM_ALLOW annotation immediately above the
declaration. The proof chain reduces `KMor1.interp_comp`
to expose the projection family, applies T3's
`simulate_interp`, then closes with T2's
`compileER_runFor` (consuming `boundExprK_dominates` as
the step-count hypothesis). Note: `compileER_runFor` and
`compileER_runtime` reside in
`namespace GebLean.LawvereERKSim` (Top.lean / Compiler.lean);
inside `namespace GebLean` the qualified path is
`LawvereERKSim.compileER_runFor`.

```lean
-- AXIOM_ALLOW: Classical.choice (Fin.lastCases_castSucc
-- via simulate_interp's existing exception; per spec §11
-- and .claude/rules/lean-coding.md § Accepted exceptions).
theorem erToK_interp
    {a : ℕ} (e : ERMor1 a) (v : Fin a → ℕ) :
    (erToK e).interp v = e.interp v := by
  unfold erToK
  -- Reduce the comp's family at v: slot 0 = (boundExprK e).interp v,
  -- slots 1..a = (KMor1.proj _).interp v = v _.
  -- Note: `simp only [Fin.cons_zero, Fin.cons_succ]` does not fire
  -- under the `fun i => family i .interp v` lambda introduced by
  -- KMor1.interp_comp's unfolding; we use `show` to state the
  -- desired post-reduction form explicitly, then close via funext
  -- + Fin.cases on the family argument.
  rw [KMor1.interp_comp]
  -- Goal:
  --   (simulate (compileER e)).interp
  --     (fun i : Fin (a+1) =>
  --       (Fin.cons (boundExprK e) (KMor1.proj ·) i).interp v)
  --   = e.interp v
  -- Rewrite the lambda to a concrete Fin.cons form:
  have h_fam :
      (fun i : Fin _ =>
        (Fin.cons (boundExprK e) (fun j : Fin a => KMor1.proj j) i).interp v)
        = Fin.cons ((boundExprK e).interp v) v := by
    funext i
    induction i using Fin.cases with
    | zero    => simp [Fin.cons_zero, KMor1.interp_proj]
    | succ j  => simp [Fin.cons_succ, KMor1.interp_proj]
  rw [h_fam]
  -- Goal now:
  --   (simulate (compileER e)).interp
  --     (Fin.cons ((boundExprK e).interp v) v)
  --   = e.interp v
  rw [KSimURMSimulator.simulate_interp]
  -- Goal:
  --   ((URMState.init (compileER e) v).runFor
  --     ((boundExprK e).interp v)).regs (compileER e).outputReg
  --   = e.interp v
  exact LawvereERKSim.compileER_runFor e v _
    (boundExprK_dominates e v)
```

If `LawvereERKSim.compileER_runFor`'s exact signature
differs (e.g., the hypothesis is `≤` or the equality is
expressed in `Eq.symm` form), the implementer adjusts the
final line. Consult `Top.lean:89-97` for the precise
signature at execution time.

- [ ] **Step 7: `lake build`**

- [ ] **Step 8: Axiom audit**

Run: `bash scripts/check-axioms.sh GebLean/LawvereERKSim/ErToK.lean`

Expected: `erToK` and `erToK_level` are
`[propext, Quot.sound]`; `erToK_interp` has
`[propext, Classical.choice, Quot.sound]` with the
AXIOM_ALLOW annotation.

- [ ] **Step 9: Append `#guard` smoke tests**

Create `GebLeanTests/LawvereERKSim/ErToK.lean`:

```lean
import GebLean.LawvereERKSim.ErToK

#guard (GebLean.erToK ERMor1.succ).interp ![3] = 4
#guard (GebLean.erToK ERMor1.zero).interp Fin.elim0 = 0
```

(Do NOT add tests on `comp`/`bsum`/`bprod`; the tower
expansion is not `#guard`-safe per
[`feedback_godel_interp_not_decidable_in_tests`](../../memory/feedback_godel_interp_not_decidable_in_tests.md).)

- [ ] **Step 10: `lake test`**

- [ ] **Step 11: Update `GebLean/LawvereERKSim.lean` index**

Append `public import GebLean.LawvereERKSim.ErToK`.

- [ ] **Step 12: Commit**

```bash
jj describe -m 'feat(ertok): assemble erToK via simulate + boundExprK

erToK e := comp (simulate (compileER e))
  (Fin.cons (boundExprK e) projections).

- erToK_level ≤ 2: composition of simulate_level ≤ 2,
  boundExprK_level ≤ 2, projections level 0.
- erToK_interp: chain simulate_interp + compileER_runFor
  (hypothesis discharged by boundExprK_dominates).

Carries AXIOM_ALLOW: Classical.choice on erToK_interp
(via simulate_interp). Spec §7.'
jj new
```

---

## Task 11: Create `ErToKFunctor.lean`; `erToKN` + interp + level + compat

**Spec ref:** §8.1.

**Files:**

- Create: `GebLean/LawvereERKSim/ErToKFunctor.lean`.

- [ ] **Step 1: Create the module skeleton**

```lean
module

public import GebLean.LawvereERKSim.ErToK
public import GebLean.LawvereERQuot
public import GebLean.LawvereKSimQuot

/-!
# `erToKFunctor`: ER → K^sim_2 functor on quotient categories

Mirrors the forward functor `kToERFunctor` at
`GebLean/LawvereKSimER.lean:474` on the reverse direction.
Lifts the single-output `erToK` to a multi-output `erToKN`,
passes through the ER quotient via `Quotient.liftOn`, and
packages with the depth-2 witness on the K side.

## Main definitions

- `erToKN : ERMorN n m → KMorN n m`.
- `erToKFunctor_map : ERMorNQuo n m → KSimMor 2 n m`.
- `erToKFunctor : LawvereERCat ⥤ LawvereKSimDCat 2`.

## Main statements

- `erToKN_interp`.
- `erToKN_level`.
- `erToKN_compat_extEq`.
- `erToKFunctor_map_id`, `erToKFunctor_map_comp`.

## References

- Spec:
  [`docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`](../../docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md)
  §8.

## Tags

ertok, functor, quotient
-/

namespace GebLean

end GebLean
```

- [ ] **Step 2: `lake build`**

- [ ] **Step 3: Add `erToKN`**

```lean
/-- Componentwise lift of `erToK` to multi-output ER
families. Spec §8.1. -/
def erToKN {n m : ℕ} (e : ERMorN n m) : KMorN n m :=
  fun j => erToK (e j)
```

- [ ] **Step 4: Add interp**

```lean
theorem erToKN_interp {n m : ℕ} (e : ERMorN n m)
    (v : Fin n → ℕ) (j : Fin m) :
    (erToKN e j).interp v = (e j).interp v :=
  erToK_interp (e j) v
```

- [ ] **Step 5: Add level**

```lean
theorem erToKN_level {n m : ℕ} (e : ERMorN n m)
    (j : Fin m) : (erToKN e j).level ≤ 2 :=
  erToK_level (e j)
```

- [ ] **Step 6: Add compat_extEq**

```lean
theorem erToKN_compat_extEq {n m : ℕ}
    {e₁ e₂ : ERMorN n m}
    (he : ∀ v j, (e₁ j).interp v = (e₂ j).interp v) :
    ∀ v j, (erToKN e₁ j).interp v
            = (erToKN e₂ j).interp v := by
  intro v j
  rw [erToKN_interp, erToKN_interp]
  exact he v j
```

- [ ] **Step 7: `lake build`**

- [ ] **Step 8: Axiom audit on the four new declarations**

Run: `bash scripts/check-axioms.sh GebLean/LawvereERKSim/ErToKFunctor.lean`

Expected: `erToKN`, `erToKN_level`,
`erToKN_compat_extEq` are
`[propext, Quot.sound]`; `erToKN_interp` inherits
AXIOM_ALLOW from `erToK_interp` (not a new annotated site).

- [ ] **Step 9: Commit**

```bash
jj describe -m 'feat(ertok): add erToKN componentwise lift

erToKN := fun e j => erToK (e j), with interp + level +
compat_extEq lemmas. compat_extEq feeds the
Quotient.liftOn well-definedness obligation in
erToKFunctor_map. Mirrors kToERN at LawvereKSimER.lean:336.
Spec §8.1.'
jj new
```

---

## Task 12: `erToKFunctor_map` via `Quotient.liftOn`

**Spec ref:** §8.2.

**Files:**

- Modify: `GebLean/LawvereERKSim/ErToKFunctor.lean`.

- [ ] **Step 1: Inspect the kToER pattern**

Read `GebLean/LawvereKSimER.lean:384-402` for the analogous
forward construction. The key insight is that
`KSimMor 2 n m` is a structure with `hom : KMorNQuo n m`
plus a depth-2 witness `KMorNQuo.atDepth 2 hom`.

- [ ] **Step 2: Construct the depth-2 witness helper**

Add a private helper that lifts a per-component level
bound to the depth-2 witness. The codebase (see
`LawvereKSimQuot.lean:373-440`) uses *named-field* syntax
for `KMorNQuo.atDepth` builders (`id_atDepth`,
`comp_atDepth`); follow that convention rather than the
anonymous-constructor form.

```lean
private def erToKN_atDepth {n m : ℕ}
    (e : ERMorN n m) :
    KMorNQuo.atDepth 2
      (Quotient.mk (kMorNSetoid n m) (erToKN e)) :=
  Quotient.mk _ {
    rep := erToKN e,
    rep_level := fun j => erToKN_level e j,
    rep_eq := rfl
  }
```

The exact field names (`rep`, `rep_level`, `rep_eq`)
match `LawvereKSimER.lean:387-388`'s consumer-side
`rcases rec with ⟨rep, rep_level, rep_eq⟩`. If the actual
`KMorNQuoAtDepthRep` structure uses different field
names at execution time, the implementer adjusts to
match — the *named-field* discipline is the contract;
field names are a Lean-side detail.

- [ ] **Step 3: Add `erToKFunctor_map` with `sorry`**

```lean
def erToKFunctor_map {n m : ℕ}
    (e : ERMorNQuo n m) : KSimMor 2 n m := by sorry
```

- [ ] **Step 4: `lake build`** to confirm signature elaborates

- [ ] **Step 5: Fill the body via `Quotient.liftOn`**

```lean
def erToKFunctor_map {n m : ℕ}
    (e : ERMorNQuo n m) : KSimMor 2 n m :=
  Quotient.liftOn e
    (fun rec => ⟨Quotient.mk (kMorNSetoid n m) (erToKN rec),
                 erToKN_atDepth rec⟩)
    (fun e₁ e₂ h => by
      apply Quotient.sound
      intro v
      funext j
      exact erToKN_compat_extEq
        (fun v' j' => congr_fun (h v') j') v j)
```

(The exact `Quotient.sound` discharge depends on
`KSimMor`'s setoid structure; adapt as needed.)

- [ ] **Step 6: `lake build`**

- [ ] **Step 7: Axiom audit**

Run: `bash scripts/check-axioms.sh GebLean/LawvereERKSim/ErToKFunctor.lean`

Expected: `[propext, Quot.sound]` (or with AXIOM_ALLOW
inheritance from `erToKN_interp` if the discharge chain
surfaces it).

- [ ] **Step 8: Commit**

```bash
jj describe -m 'feat(ertok): add erToKFunctor_map via Quotient.liftOn

Lifts ER quotient ⟦e⟧ to a KSimMor 2 n m via
Quotient.liftOn, packaging the K^sim component with the
depth-2 witness. Well-definedness via erToKN_compat_extEq.
Mirrors kToERFunctor_map at LawvereKSimER.lean:384. Spec §8.2.'
jj new
```

---

## Task 13: `erToKFunctor_map_id` and `erToKFunctor_map_comp`

**Spec ref:** §8.3.

**Files:**

- Modify: `GebLean/LawvereERKSim/ErToKFunctor.lean`.

- [ ] **Step 1: Add `erToKFunctor_map_id`**

```lean
theorem erToKFunctor_map_id (n : LawvereERCat) :
    erToKFunctor_map
        (CategoryTheory.CategoryStruct.id
          (obj := LawvereERCat) n)
      = CategoryTheory.CategoryStruct.id
          (obj := LawvereKSimDCat 2)
          (n : LawvereKSimDCat 2) := by
  unfold erToKFunctor_map
  apply Quotient.sound
  intro v
  funext j
  -- 𝟙 n in LawvereERCat is ERMorN.id n, i.e., j ↦ ERMor1.proj j.
  -- (erToKN (ERMorN.id n) j).interp v = (erToK (ERMor1.proj j)).interp v
  -- = (ERMor1.proj j).interp v        -- by erToK_interp
  -- = v j
  -- and the K-side identity (𝟙 n in LawvereKSimDCat 2)'s
  -- representative at slot j is KMor1.proj j, whose interp at v is v j.
  -- The equality follows from erToK_interp on both sides plus
  -- the projection interp identities.
  rw [erToKN_interp]
  -- Both sides now have shape (proj j).interp v; close by rfl.
  rfl
```

Note: this proof inherits the AXIOM_ALLOW on
`erToK_interp` (via `erToKN_interp`) and is therefore
`[propext, Classical.choice, Quot.sound]` rather than the
plan's earlier disclaim. Update §11 expectations and the
Task 13 Step 6 axiom audit accordingly.

- [ ] **Step 2: `lake build`**

- [ ] **Step 3: Add `erToKFunctor_map_comp`**

```lean
theorem erToKFunctor_map_comp {n m k : ℕ}
    (e : ERMorNQuo n m) (f : ERMorNQuo m k) :
    erToKFunctor_map
        (CategoryTheory.CategoryStruct.comp
          (obj := LawvereERCat) e f)
      = CategoryTheory.CategoryStruct.comp
          (obj := LawvereKSimDCat 2)
          (erToKFunctor_map e) (erToKFunctor_map f) := by
  unfold erToKFunctor_map
  -- Mirrors kToERFunctor_map_comp at LawvereKSimER.lean:427.
  -- Pattern: rcases e and f, refine Quotient.inductionOn₂,
  -- apply Quotient.sound, intro v / funext j, reduce both
  -- sides to interp equality via erToKN_interp + KMorN.comp's
  -- interp identity.
  rcases e with ⟨_⟩
  rcases f with ⟨_⟩
  apply Quotient.sound
  intro v
  funext j
  rw [erToKN_interp]
  -- Goal: erToK (e_rep j) (f_rep ∘ erToK) ≫ ... reduces to
  -- ... = (composition of the e, f representatives).
  -- See LawvereKSimER.lean:457-468 for the analogous chain.
  sorry
```

- [ ] **Step 4: Fill the `sorry` per the kToER pattern**

The kToER analogue at `LawvereKSimER.lean:457-468`:

```lean
  rw [kToERN_interp, kToERN_interp]
  simp only [KMorN.comp, KMor1.interp_comp]
  congr 1
  funext j
  rw [kToERN_interp]
```

Mirror this for the ER→K direction. The composition's
interp identity uses `ERMorN.comp`'s definition and
`erToKN_interp`.

- [ ] **Step 5: `lake build`** (with no `sorry`)

- [ ] **Step 6: Axiom audit**

Run: `bash scripts/check-axioms.sh GebLean/LawvereERKSim/ErToKFunctor.lean`

Expected: `erToKFunctor_map_id` and
`erToKFunctor_map_comp` inherit AXIOM_ALLOW from
`erToKN_interp` (per the round-1 review correction to
Task 13's previous-disclaim); both end up
`[propext, Classical.choice, Quot.sound]` by inheritance,
not as new annotated sites.

- [ ] **Step 7: Commit**

```bash
jj describe -m 'feat(ertok): add erToKFunctor functor laws

map_id: erToK on ERMorN.id discharges via rfl after
Quotient.sound (erToK ∘ proj = proj definitionally).

map_comp: rcases the ER witnesses, refine Quotient.sound,
chain erToKN_interp on both sides + KMorN.comp interp
identity. Mirrors kToERFunctor_map_comp at
LawvereKSimER.lean:427. Spec §8.3.'
jj new
```

---

## Task 14: `erToKFunctor` assembly

**Spec ref:** §8.4.

**Files:**

- Modify: `GebLean/LawvereERKSim/ErToKFunctor.lean`.

- [ ] **Step 1: Add `erToKFunctor`**

```lean
/-- The reverse functor of the categorical equivalence
`LawvereERCat ≌ LawvereKSimDCat 2`. Forward direction in
`kToERFunctor`; equivalence assembled in T5. Spec §8.4. -/
def erToKFunctor : CategoryTheory.Functor
    LawvereERCat (LawvereKSimDCat 2) where
  obj n     := n
  map       := erToKFunctor_map
  map_id    := erToKFunctor_map_id
  map_comp  := erToKFunctor_map_comp
```

- [ ] **Step 2: `lake build`**

- [ ] **Step 3: Axiom audit**

Run: `bash scripts/check-axioms.sh GebLean/LawvereERKSim/ErToKFunctor.lean`

Expected: `erToKFunctor` itself is `[propext, Quot.sound]`;
its `map_id` and `map_comp` fields inherit AXIOM_ALLOW from
`erToK_interp` via `erToKN_interp`.

- [ ] **Step 4: Commit**

```bash
jj describe -m 'feat(ertok): assemble erToKFunctor

CategoryTheory.Functor from LawvereERCat to
LawvereKSimDCat 2. obj n := n (both categories ℕ-objects
by def-unfolding). map is erToKFunctor_map. Laws via the
two preceding theorems. Spec §8.4.'
jj new
```

---

## Task 15: Re-export, axiom audit, final lint sweep, tests

**Spec ref:** §9, §11, §12.

**Files:**

- Modify: `GebLean/LawvereERKSim.lean` (index).
- Modify: `GebLean.lean` (top-level re-export).
- Create / modify:
  `GebLeanTests/LawvereERKSim/ErToK.lean` (if not landed in
  Task 10).

- [ ] **Step 1: Verify all new modules are re-exported via `public import`**

Open `GebLean/LawvereERKSim.lean`. Ensure the following
lines exist (add any missing):

```lean
public import GebLean.LawvereERKSim.RuntimeBound
public import GebLean.LawvereERKSim.ErToK
public import GebLean.LawvereERKSim.ErToKFunctor
```

- [ ] **Step 2: Verify `GebLean.lean` re-exports the top index**

`GebLean.lean` should `public import GebLean.LawvereERKSim`
(already present from prior workstreams). Confirm.

- [ ] **Step 3: `lake build`** (full project)

Expected: 0 errors, 0 warnings.

- [ ] **Step 4: `lake test`**

Expected: 0 failures. All `#guard` tests for Tasks 1-3 and
Task 10 pass.

- [ ] **Step 5: Full-project axiom audit**

Run: `bash scripts/check-axioms.sh`

Expected: 0 failures. The three AXIOM_ALLOW'd primary sites
per spec §11 (`boundExprKParams_dominates`'s bsum and bprod
cases; `erToK_interp`) carry their annotations. Theorems
that *inherit* `Classical.choice` via transitive dependence
(`boundExprK_dominates`, `erToKN_interp`,
`erToKFunctor_map_id`, `erToKFunctor_map_comp`, downstream
clients) are not re-counted as new sites.

- [ ] **Step 6: Manual lint sweep**

Run: `lake lint` (or `lake exe runLinter` per project
convention).

Expected: 0 violations.

Run: `markdownlint-cli2 'docs/**/*.md'`

Expected: 0 errors.

- [ ] **Step 7: Regenerate doctoc**

Run: `doctoc 'docs/**/*.md'`

Expected: TOCs unchanged or refreshed.

- [ ] **Step 8: Final commit**

```bash
jj describe -m 'chore(ertok): T4 closeout - re-exports, axiom audit, lint

Re-export RuntimeBound, ErToK, ErToKFunctor via
LawvereERKSim/index. Verify clean build + tests + axiom
audit; confirm 3 primary AXIOM_ALLOW sites match spec §11.
Markdownlint + doctoc clean.

T4 deliverables landed:
- KMor1.maxK, maxOver, pow2_iter (KArith).
- boundExprKParams + boundExprKParams_dominates
  (RuntimeBound).
- boundExprK + level + interp + dominates
  (RuntimeBound).
- erToK + level + interp (ErToK).
- erToKN + interp + level + compat_extEq
  (ErToKFunctor).
- erToKFunctor_map + map_id + map_comp + erToKFunctor
  (ErToKFunctor).

~1480 LOC. Comparable to T3.'
jj new
```

- [ ] **Step 9: Branch handoff**

Working copy is on `feat/ertok-runtime-bound`. Push to
fork (user line-by-line review per `CLAUDE.md` § Rules):

```bash
bash scripts/pre-push.sh
# User reviews the lease-protected push commit-by-commit.
jj git push --remote origin -b feat/ertok-runtime-bound
```

After the user confirms the push:

- Open an internal PR against `origin/main` (per Op 1 of
  `.claude/rules/fork-upstream-flow.md`).
- Merge with `--merge` strategy after CI passes.

- [ ] **Step 10: Update task tracker**

Mark T4 complete in any external tracker; seed T5 handoff
document (analogous to
[`docs/superpowers/plans/2026-05-22-post-t3-handoff.md`](2026-05-22-post-t3-handoff.md))
to summarise T4's actually-landed surface and bind T5's
brainstorming.

---

## Closeout — what success looks like

After Task 15:

- `feat/ertok-runtime-bound` carries ~15 commits.
- `lake build` clean, `lake test` clean, `check-axioms.sh`
  clean (3 primary AXIOM_ALLOW sites annotated per spec §11).
- `markdownlint-cli2` clean across `docs/**/*.md`.
- Public surface: `boundExprK`, `boundExprK_interp`,
  `boundExprK_level`, `boundExprK_dominates`,
  `boundExprKParams`, `boundExprKParams_dominates`,
  `erToK`, `erToK_interp`, `erToK_level`, `erToKN`,
  `erToKN_interp`, `erToKN_level`,
  `erToKN_compat_extEq`, `erToKFunctor_map`,
  `erToKFunctor_map_id`, `erToKFunctor_map_comp`,
  `erToKFunctor`.
- KArith.lean additions: `KMor1.maxK`, `KMor1.maxOver`,
  `KMor1.pow2_iter`, and their interp + level lemmas.

T5 (strict iso `LawvereERCat ≌ LawvereKSimDCat 2`) is now
unblocked: it has access to both `kToERFunctor` (existing)
and `erToKFunctor` (new), plus their pointwise interp
agreement (`kToER_interp`, `erToK_interp`).

## References

- Spec under implementation:
  [`docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`](../specs/2026-05-22-step-t4-runtime-bound-design.md).
- Adversarial-review rounds 1–4 of the spec:
  [`docs/research/2026-05-22-step-t4-spec-adversarial-review-round-{1..4}.md`](../../research/).
- Post-T3 handoff:
  [`docs/superpowers/plans/2026-05-22-post-t3-handoff.md`](2026-05-22-post-t3-handoff.md).
- kToER mirror (binding reference for §8 multi-output
  passage): `GebLean/LawvereKSimER.lean` lines 336-479.
- T2 surface consumed: `GebLean/LawvereERKSim/Compiler.lean`
  lines 1590, 1722-1770; `GebLean/LawvereERKSim/Top.lean`
  lines 89-97 (`compileER_runFor`).
- T3 surface consumed:
  `GebLean/Utilities/KSimURMSimulator.lean` lines 548,
  958-984.
- Tower lemmas: `GebLean/Utilities/Tower.lean` lines 27, 42,
  51, 101, 120.
- Constructive max: `GebLean/LawvereKSim.lean` line 106.
- Project rules: [`CLAUDE.md`](../../CLAUDE.md),
  [`.claude/rules/lean-coding.md`](../../.claude/rules/lean-coding.md),
  [`.claude/rules/markdown-writing.md`](../../.claude/rules/markdown-writing.md),
  [`.claude/rules/fork-upstream-flow.md`](../../.claude/rules/fork-upstream-flow.md).
- Tourlakis 2018 `PR-complexity-topics.pdf` §0.1.0.27, §0.1.0.37,
  §0.1.0.42, §0.1.0.43, §0.1.0.44.
