# Step 5 — `kToER` structural-recursion functor — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Land the forward functor of the ER ↔ K^sim_2
categorical equivalence: `kToER : KMor1 a → ERMor1 a` for
level ≤ 2, the multi-output companion `kToERN`, the
correctness theorem `kToER_interp` (Tourlakis 2018 §0.1.0.44
⊆-direction pointwise), and the categorical functor
`kToERFunctor : LawvereKSimDCat 2 ⥤ LawvereERCat`.  All
load-bearing arithmetic was absorbed in step 4
(`KMor1.majorize_by_A_two_iter` /
`KMor1.majorize_by_componentBound`) and step 2
(`simultaneousBoundedRec_interp_correct`); step 5 is
structural plumbing.

**Architecture:** Mostly one new module
`GebLean/LawvereKSimER.lean`.  Three small additions to
existing modules: a bridge lemma
`KMor1.simrecVec_eq_Nat_simRecVec` in
`LawvereKSimInterp.lean` (Task 1), an index-independence
lemma `KMor1.majorize_simrec_index_indep` in
`LawvereKSimMajorization.lean` (Task 2), and a
context-sum monotonicity helper
`ERMor1.sumCtxER_cons_le_of_le` in
`LawvereKSimMajorization.lean` (Task 3).  Then the new
module: `kToER` structural-recursion definition, three
Factoring R simrec-branch helpers
(`kToER_simrec_dominates`, `kToER_simrec_bound_mono`,
`kToER_interp_simrec`), the universal correctness theorem
`kToER_interp`, the multi-output companion `kToERN` plus
`kToERN_interp`, the Quotient-lift well-definedness helper
`kToERN_compat_extEq`, and the categorical functor
`kToERFunctor` with `map_id` and `map_comp`.

**Tech Stack:** Lean 4 + mathlib4.  Build via `lake build`,
test via `lake test`.  Existing infrastructure consumed:

- `KMor1`, `KMor1.level`, `KMor1.interp`, `KMor1.simrecVec`,
  `KMor1.interp_simrec` (`LawvereKSim.lean`,
  `LawvereKSimInterp.lean`).
- `KSimMor`, `KMorNQuo`, `KMorNQuo.atDepth`,
  `KMorNQuo.AtDepthRaw`, `kMorNSetoid`, `LawvereKSimDCat`
  (`LawvereKSimQuot.lean`).
- `ERMor1`, `ERMor1.zeroN`, `ERMor1.succ`, `ERMor1.proj`,
  `ERMor1.comp`, `ERMor1.interp`, ER-side interp simp
  lemmas (`LawvereER.lean`, `LawvereERInterp.lean`).
- `ERMorNQuo`, `erMorNSetoid`, `LawvereERCat`
  (`LawvereERQuot.lean`).
- `ERMor1.simultaneousBoundedRec`,
  `simultaneousBoundedRec_interp_correct`
  (`Utilities/ERSimultaneousBoundedRec.lean`).
- `ERMor1.A_two_iter`, `interp_A_two_iter`
  (`Utilities/ERAMajorants.lean`).
- `ERMor1.sumCtxER`, `interp_sumCtxER`
  (`LawvereERBoundComputable.lean`).
- `KMor1.majorize`, `KMor1.majorize_by_componentBound`,
  `ERMor1.sumCtxERPlusOffset`,
  `interp_sumCtxERPlusOffset` (step 4's
  `LawvereKSimMajorization.lean`).
- `Nat.simRecVec` (`Utilities/SimRec.lean`).
- Mathlib: `Quotient.liftOn`, `Quotient.sound`,
  `Quotient.exact`, `Quotient.lift_mk`,
  `Quotient.liftOn_mk`, `Fin.cons`, `Fin.cons_zero`,
  `Fin.cons_succ`, `Fin.tail`, `Fin.cons_self_tail`,
  `Fin.append`, `Fin.append_left`, `Fin.append_right`,
  `Finset.le_sup`, `Nat.le_of_succ_le_succ`.

**Spec:**
`docs/superpowers/specs/2026-05-03-step-5-ksim-to-er-functor-design.md`
(approved after 3 rounds of adversarial review;
round 3 reports 0 blockers / 0 majors / 3 minors all
addressed).

**Master design:**
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`
§3.5 (lines 1089-1163) — `kToER` definition, `kToER_interp`
proof outline, `kToERFunctor` lift sketch.

---

## File structure

**Created (implementation):**

- `GebLean/LawvereKSimER.lean` — top-level module with
  `kToER`, `kToERN`, the three Factoring R helpers,
  `kToER_interp`, `kToERN_interp`, `kToERN_compat_extEq`,
  `kToERFunctor`, plus optional Scope-B step-11 helpers.

**Created (tests):**

- `GebLeanTests/LawvereKSimER.lean` — Tier 1 atomic
  `#guard`-or-`rfl` tests, Tier 2 universal-theorem
  `example` proofs on inline `addK`, Tier 3 `kToERFunctor`
  obj/map sanity checks.

**Modified:**

- `GebLean.lean` — register the new module's import
  alphabetically.
- `GebLeanTests.lean` — register the new test module
  alphabetically.
- `GebLean/LawvereKSimInterp.lean` — add the
  `KMor1.simrecVec_eq_Nat_simRecVec` bridge lemma plus the
  required `import GebLean.Utilities.SimRec` (Task 1).
- `GebLean/LawvereKSimMajorization.lean` — add
  `KMor1.majorize_simrec_index_indep` (Task 2) and
  `ERMor1.sumCtxER_cons_le_of_le` (Task 3).

---

## Style and discipline reminders (from steps 1-4)

Each task's code must follow CLAUDE.md:

- Lines ≤ 80 characters.
- Spaces around binary operators in source: write
  `Fin (k + 1)` not `Fin (k+1)`.
- Every public `def`/`theorem` carries a literature
  reference in its docstring (Tourlakis 2018 §0.1.0.44 for
  `kToER` and `kToER_interp`; §0.1.0.34 for the
  bounded-recursion-closure shape; §0.1.0.10 transitively
  via step 4's bridge for the simrec helpers; master
  design §3.5 throughout).
- Use `simp only [...]` not bare `simp [...]`.
- Use `change` not `show` when the goal text differs from
  what Lean has internally.
- No banned words from CLAUDE.md (especially "important",
  "key", "complex", "simple", "actually", "core",
  "advanced", "fundamental", "critical", "advantage",
  "benefit", "insight", "careful", "difficult", "blocked",
  "incomplete", "future", "issue", "problem", "block").
- Banned-word discipline applies to commit messages too.
- Discipline #1 (import-at-skeleton-creation): when
  creating a new `.lean` file, register its import in the
  appropriate index module (`GebLean.lean` /
  `GebLeanTests.lean`) in the same task — before adding any
  body code.
- Discipline #4 (ER-side `.interp` `#guard` is impractical
  for any K^sim term involving `simrec`): use `example`
  proofs invoking the universal `kToER_interp` theorem at
  concrete inputs instead of direct `#guard` evaluation.
- Build verification: after every task touching a `.lean`
  file, run `lake build` (and `lake test` where
  applicable).  Inspect output for `error:` and `warning:`
  lines.  No `.olean` removal.  Use
  `mcp__lean-lsp__lean_build` only if the lean-lsp output
  appears stale.
- No `nlinarith` (not in scope per
  `LawvereKSimMajorization.lean`'s import set; `omega`
  plus explicit `Nat.*` lemmas instead).

---

## Task 1 — Bridge lemma `KMor1.simrecVec_eq_Nat_simRecVec`

**Files:**

- Modify: `GebLean/LawvereKSimInterp.lean` (add import +
  new theorem)

This bridge equates K^sim's K-side `simrecVec` interpreter
to the Nat-side `simRecVec` consumed by step 2's
`simultaneousBoundedRec_interp_correct`.  The two functions
are equivalent but not definitionally equal: K^sim
`simrecVec` uses an inline `dite`-based step context
(LawvereKSimInterp.lean lines 65-82) while `Nat.simRecVec`
uses `Fin.append (Fin.cons n x) prev` (`Utilities/SimRec.lean`
lines 40-48).

The proof shape mirrors the existing private
`interp_simrec_eq_simrecVec` at lines 121-155 (35 lines).

- [ ] **Step 1.1: Add the import**

Add `import GebLean.Utilities.SimRec` to the import section
of `GebLean/LawvereKSimInterp.lean` (alphabetical order;
should come before any deeper `Utilities/...` imports if
present).

- [ ] **Step 1.2: Build to verify the import is clean**

Run: `lake build GebLean.LawvereKSimInterp 2>&1 | tail -10`

Expected: `Build completed successfully` with no
`error:` / `warning:` lines.

- [ ] **Step 1.3: Add the theorem skeleton**

Append to the file (inside the `namespace GebLean` block,
near the existing `interp_simrec_eq_simrecVec` private
theorem):

```lean
/-- Bridge between K^sim's `simrecVec` interpreter (which
recurses with `KMor1.interp` calls inline) and `Nat.simRecVec`
(the value-side simultaneous recursion consumed by
`ERMor1.simultaneousBoundedRec_interp_correct`).  Master
design §3.5; supports the simrec branch of step 5's
`kToER_simrec_dominates` / `kToER_interp_simrec`. -/
theorem KMor1.simrecVec_eq_Nat_simRecVec {a k : ℕ}
    (h : Fin (k + 1) → KMor1 a)
    (g : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (params : Fin a → ℕ) :
    ∀ (n : ℕ) (j : Fin (k + 1)),
      KMor1.simrecVec h g params n j
        = Nat.simRecVec k a (fun j' => (h j').interp)
            (fun j' => (g j').interp) n params j := by
  _
```

- [ ] **Step 1.4: Build to see the goal type**

Run: `lake build GebLean.LawvereKSimInterp 2>&1 | tail -10`

Expected: an "unsolved goals" error showing the goal type
(the universal statement above).

- [ ] **Step 1.5: Fill in the proof body**

Replace the `_` with:

```lean
  intro n
  induction n with
  | zero => intro j; rfl
  | succ n ih =>
      intro j
      -- KMor1.simrecVec step case uses inline dite-based
      -- stepCtx; Nat.simRecVec uses Fin.append (Fin.cons n
      -- params) (prev).  Bridge the two stepCtx forms by
      -- congr 1 + funext + by_cases on idx.val < a + 1.
      simp only [KMor1.simrecVec, Nat.simRecVec_succ]
      congr 1
      funext idx
      by_cases h₁ : idx.val < a + 1
      · -- Inner branch: route to (Fin.cons n params).
        simp only [h₁, dite_true, Fin.append]
        by_cases h₂ : idx.val = 0
        · simp only [h₂, dite_true, Fin.cons_zero,
            Fin.append_left]
          rfl
        · simp only [h₂, dite_false, Fin.cons_succ,
            Fin.append_left]
          rfl
      · -- Outer branch: route via ih to the previous-iter
        -- vector embedded inside Fin.append.
        simp only [h₁, dite_false, Fin.append_right]
        -- ih j' : KMor1.simrecVec ... params n j'
        --        = Nat.simRecVec ... n params j'
        -- We need this for the specific j' carried by idx.
        exact ih ⟨idx.val - (a + 1), by omega⟩
```

(If specific mathlib lemma names differ — e.g.,
`Fin.append_left` vs `Fin.append_left'` — adjust at task
time using `lean_local_search` / `lean_loogle`.)

- [ ] **Step 1.6: Build to verify clean**

Run: `lake build GebLean.LawvereKSimInterp 2>&1 | tail -10`

Expected: `Build completed successfully` with no errors,
no warnings.

If errors persist:

- For `Fin.append_left` / `Fin.append_right` name
  shifts: use `lean_local_search "Fin.append"` to find
  current names.
- For `Fin.cons_zero` / `Fin.cons_succ` name shifts:
  same.
- The mathlib `Fin.append`-based unfolding may need an
  explicit `Fin.cast` reveal at the boundary.  Step 4's
  `interp_packedStepCtx` proof
  (`Utilities/ERSimultaneousBoundedRec.lean` lines
  196-285) handles a structurally identical case-split
  and may serve as a more direct template than the
  private `interp_simrec_eq_simrecVec`.

- [ ] **Step 1.7: Run tests to confirm no regressions**

Run: `lake test 2>&1 | tail -20`

Expected: all tests pass; no new warnings.

- [ ] **Step 1.8: Commit**

```bash
git add GebLean/LawvereKSimInterp.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 1: KMor1.simrecVec_eq_Nat_simRecVec bridge lemma

Bridges K^sim's `simrecVec` interpreter to `Nat.simRecVec`
consumed by step 2's `simultaneousBoundedRec_interp_correct`.
Step 5's simrec helpers (kToER_simrec_dominates,
kToER_interp_simrec) consume this lemma to align the
dominance hypothesis form.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 2 — `KMor1.majorize_simrec_index_indep`

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (add new
  theorem after `KMor1.majorize` def)

This lemma asserts that `KMor1.majorize` at the simrec
node ignores the output index argument — definitional from
step 4's `KMor1.majorize` simrec branch (lines 632-657 of
`LawvereKSimMajorization.lean`) which binds the index
to `_` and produces `(2, r_H + r_G + 2)` regardless.

- [ ] **Step 2.1: Locate the insertion point**

Read `GebLean/LawvereKSimMajorization.lean` and find the
end of the `KMor1.majorize` def (around line 657).
Insertion point: immediately after `KMor1.majorize`'s
final `(2, r_H + r_G + 2)` line, before
`KMor1.majorize_by_A_two_iter`.

- [ ] **Step 2.2: Add the theorem**

Insert:

```lean
/-- Index-independence of `KMor1.majorize` at simrec: the
result depends only on the families `h_fam` and `g_fam`,
not on the output index `i`.  Used by step 5's
`kToER_simrec_dominates` to align the bound built from
output index `i` with the bound built from any other
output index `j`.  Master design §3.5 + §3.4. -/
theorem KMor1.majorize_simrec_index_indep
    {a k : ℕ}
    (i j : Fin (k + 1))
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_i : (KMor1.simrec i h_fam g_fam).level ≤ 2)
    (h_j : (KMor1.simrec j h_fam g_fam).level ≤ 2) :
    KMor1.majorize (KMor1.simrec i h_fam g_fam) h_i
      = KMor1.majorize (KMor1.simrec j h_fam g_fam) h_j := by
  simp only [KMor1.majorize]
```

- [ ] **Step 2.3: Build to verify**

Run: `lake build GebLean.LawvereKSimMajorization 2>&1 | tail -10`

Expected: `Build completed successfully`, no warnings.

If `simp only [KMor1.majorize]` does not close the goal:

- Check whether `KMor1.majorize`'s level-discharge `have`s
  produce different proof terms on the LHS vs RHS.  If so,
  try `simp only [KMor1.majorize]; rfl`.
- As a hand-construction fallback, inspect the
  `KMor1.majorize` simrec branch via
  `lean_declaration_file KMor1.majorize` and write the
  result as an explicit term-level proof:
  `Prod.ext rfl (by simp [Fin.foldr])`.

- [ ] **Step 2.4: Commit**

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 2: KMor1.majorize_simrec_index_indep

Asserts KMor1.majorize at simrec ignores the output index
argument.  Definitional from step 4's KMor1.majorize
simrec branch.  Used by step 5's kToER_simrec_dominates to
align the bound across components.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 3 — `ERMor1.sumCtxER_cons_le_of_le`

**Files:**

- Modify: `GebLean/LawvereKSimMajorization.lean` (add new
  theorem near `vMax_cons` / `interp_sumCtxER` use sites)

This helper lifts `m ≤ n` to monotonicity of
`(sumCtxER (a+1)).interp (Fin.cons m x) ≤
(sumCtxER (a+1)).interp (Fin.cons n x)`, used by
`kToER_simrec_bound_mono` to prove the bound is monotone
in the iteration counter.

- [ ] **Step 3.1: Locate the insertion point**

Look for `vMax_cons` / `vMax_apply_le` in
`GebLean/LawvereKSimMajorization.lean` (around line
60-100).  Insertion point: immediately after `vMax_cons`,
matching the analogue's shape.

- [ ] **Step 3.2: Add the theorem**

Insert (full proof; the spec's pseudocode body is a
strategy outline — write the real Lean here):

```lean
/-- Monotonicity of `sumCtxER` in the cons-head slot: if
`m ≤ n` then `(sumCtxER (a+1)).interp (Fin.cons m x) ≤
(sumCtxER (a+1)).interp (Fin.cons n x)`.  Used by step 5's
`kToER_simrec_bound_mono` for the bound's
iteration-counter monotonicity.  Master design §3.5;
analogue of `vMax_cons` for the sum-context. -/
theorem ERMor1.sumCtxER_cons_le_of_le {a : ℕ}
    (x : Fin a → ℕ) {m n : ℕ} (h : m ≤ n) :
    (ERMor1.sumCtxER (a + 1)).interp (Fin.cons m x)
      ≤ (ERMor1.sumCtxER (a + 1)).interp (Fin.cons n x) := by
  rw [ERMor1.interp_sumCtxER, ERMor1.interp_sumCtxER]
  -- (sumCtxER (a+1)).interp ctx evaluates to a Fin.foldr
  -- over (fun i acc => acc + ctx i).  The two foldrs
  -- differ only at index 0 (where Fin.cons m x = m,
  -- Fin.cons n x = n) and agree on every other index
  -- (where both reduce to x via Fin.cons_succ).
  -- Strategy: prove a generalisation over an arbitrary
  -- accumulator, then specialise to acc = 0.
  suffices h_gen : ∀ (acc : ℕ),
      Fin.foldr (a + 1)
          (fun i acc' => acc' + Fin.cons m x i) acc
        ≤ Fin.foldr (a + 1)
            (fun i acc' => acc' + Fin.cons n x i) acc by
    exact h_gen 0
  intro acc
  induction a with
  | zero =>
      simp only [Fin.foldr_succ, Fin.foldr_zero,
        Fin.cons_zero]
      omega
  | succ a' ih =>
      simp only [Fin.foldr_succ]
      -- After Fin.foldr_succ, the goal is over
      -- `Fin.foldr a' (fun i acc' => acc' + cons _ x
      --     (Fin.succ i)) (acc + cons _ x 0)`.
      -- Both LHS and RHS share the fact that for i ≥ 1,
      -- cons m x (Fin.succ i) = cons n x (Fin.succ i) =
      -- x i.  Apply ih on the rewritten body.
      -- Tactic: this is implementer-discretion at task
      -- time — possible paths:
      --   a) `apply Fin.foldr_le_of_le; intro i acc1
      --       acc2 hacc; omega` if such a mathlib lemma
      --       exists.
      --   b) Direct induction on `a'` rewriting via
      --       Fin.cons_succ to drop the cons-head
      --       difference, then apply ih.
      -- Use lean_local_search / lean_loogle at task time
      -- to find the cleanest path.
      _
```

The `_` at the end is a task-time hole.  The implementer
fills it via the strategy comments above.

- [ ] **Step 3.3: Build to see the goal type at the hole**

Run: `lake build GebLean.LawvereKSimMajorization 2>&1 | tail -15`

Expected: an "unsolved goals" error showing the
post-`Fin.foldr_succ` goal.  Use `mcp__lean-lsp__lean_goal`
on the file at the underscore line to see the full goal.

- [ ] **Step 3.4: Search for available `Fin.foldr` lemmas**

Run via lean-lsp: `lean_local_search "Fin.foldr"` and
`lean_loogle "Fin.foldr ... ≤ Fin.foldr ..."`.

Document any helpful hits in the task's commit message.

- [ ] **Step 3.5: Fill in the proof**

Replace `_` with whichever tactic chain closes the goal.
A likely working pattern (subject to verification at task
time):

```lean
      -- Specialise ih to the accumulator that matches the
      -- Strategy: peel the head difference (Fin.cons m x 0
      -- = m on LHS, = n on RHS), then the inner foldr
      -- bodies agree pointwise.
      have h_inner : ∀ (acc' : ℕ),
          Fin.foldr a'
              (fun i acc'' => acc'' + Fin.cons m x
                (Fin.succ i)) acc'
            = Fin.foldr a'
                (fun i acc'' => acc'' + Fin.cons n x
                  (Fin.succ i)) acc' := by
        intro acc'
        congr 1
        funext i acc''
        simp [Fin.cons_succ]
      -- After the head peel, the foldr bodies match on
      -- the inner indices; only the head accumulators
      -- differ by m vs n.
      rw [h_inner]
      -- Goal: Fin.foldr a' f (acc + Fin.cons m x 0) ≤
      --       Fin.foldr a' f (acc + Fin.cons n x 0)
      -- By Fin.cons_zero: Fin.cons m x 0 = m, etc.
      simp only [Fin.cons_zero]
      -- Goal: Fin.foldr a' f (acc + m) ≤
      --       Fin.foldr a' f (acc + n)
      -- Apply ih with acc := acc + m, leveraging
      -- monotonicity of Fin.foldr in its initial
      -- accumulator (a separate lemma if not directly
      -- provided).
      exact ih (acc + m)
```

(Verify at task time; if `ih (acc + m)` does not match the
goal's RHS shape, refactor with the correct accumulator.
If a `Fin.foldr_mono_acc`-style lemma is needed and not
available, prove it inline as a 5-line side-induction.)

- [ ] **Step 3.6: Build to verify**

Run: `lake build GebLean.LawvereKSimMajorization 2>&1 | tail -15`

Expected: `Build completed successfully`, no warnings.

- [ ] **Step 3.7: Commit**

```bash
git add GebLean/LawvereKSimMajorization.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 3: ERMor1.sumCtxER_cons_le_of_le

Monotonicity of sumCtxER in the cons-head slot.  Used by
step 5's kToER_simrec_bound_mono for the bound's
iteration-counter monotonicity.  Analogue of vMax_cons.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 4 — `LawvereKSimER.lean` skeleton + index registrations

**Files:**

- Create: `GebLean/LawvereKSimER.lean` (skeleton with
  imports and namespace open/end only)
- Modify: `GebLean.lean` (alphabetical insertion of
  `import GebLean.LawvereKSimER`)

Per discipline #1, the skeleton creation and the index
registration land in the same task.

- [ ] **Step 4.1: Create the skeleton**

Create `GebLean/LawvereKSimER.lean` with this content:

```lean
import GebLean.LawvereER
import GebLean.LawvereERQuot
import GebLean.LawvereKSim
import GebLean.LawvereKSimInterp
import GebLean.LawvereKSimMajorization
import GebLean.LawvereKSimQuot
import GebLean.Utilities.ERAMajorants
import GebLean.Utilities.ERSimultaneousBoundedRec

/-!
# Forward functor `kToER : KMor1 → ERMor1` (level ≤ 2)

Realises Tourlakis 2018 §0.1.0.44 ⊆-direction pointwise:
every K^sim morphism of level ≤ 2 translates structurally
to an `ERMor1` term, with the simrec node routed through
`ERMor1.simultaneousBoundedRec` (step 2) using the bound
from `KMor1.majorize_by_componentBound` (step 4).
Master design §3.5.
-/

namespace GebLean

end GebLean
```

- [ ] **Step 4.2: Register the import in `GebLean.lean`**

Read `GebLean.lean`.  Find the alphabetically-correct
location for `import GebLean.LawvereKSimER`.  Per
case-insensitive ordering, this comes between
`LawvereKSim*` siblings — specifically between
`GebLean.LawvereKSim` (or its variants) and
`GebLean.LawvereKSimInterp`/`LawvereKSimMajorization`/etc.

Add the import line.

- [ ] **Step 4.3: Build to verify the skeleton compiles**

Run: `lake build GebLean.LawvereKSimER 2>&1 | tail -10`

Expected: `Build completed successfully`, no warnings.

- [ ] **Step 4.4: Commit**

```bash
git add GebLean/LawvereKSimER.lean GebLean.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 4: LawvereKSimER.lean skeleton + index registration

Empty module with import section and namespace.  Registered
in GebLean.lean per discipline #1.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 5 — `kToER` definition (all five constructor cases)

**Files:**

- Modify: `GebLean/LawvereKSimER.lean` (add the def inside
  the namespace scope)

The structural-recursion definition.  All five cases per
spec §4.2.

- [ ] **Step 5.1: Add the def**

Insert inside `namespace GebLean`:

```lean
/-- Forward translation `KMor1 a → ERMor1 a` for K^sim
morphisms of level ≤ 2.  Atomic constructors map to ER
atoms; `comp` and `raise` recurse structurally; `simrec`
routes through `ERMor1.simultaneousBoundedRec` with the
bound from `KMor1.majorize_by_componentBound` (step 4).
Master design §3.5; Tourlakis 2018 §0.1.0.44 ⊆ direction. -/
def kToER : ∀ {a : ℕ} (f : KMor1 a), f.level ≤ 2 → ERMor1 a
  | _, .zero,         _ => ERMor1.zeroN _
  | _, .succ,         _ => ERMor1.succ
  | _, .proj i,       _ => ERMor1.proj i
  | _, .comp f gs,    h =>
      have hf  : f.level ≤ 2 :=
        le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 2 := fun i =>
        le_trans
          (Finset.le_sup
            (f := fun j => (gs j).level)
            (Finset.mem_univ i))
          (le_trans (le_max_right _ _) h)
      ERMor1.comp (kToER f hf)
        (fun i => kToER (gs i) (hgs i))
  | _, .raise f,      h =>
      have hf : f.level ≤ 2 := by
        unfold KMor1.level at h; omega
      kToER f hf
  | _, .simrec (a := a) (k := k) i h_fam g_fam, hyp =>
      have h_h : ∀ j, (h_fam j).level ≤ 2 := fun j => by
        have h1 : (h_fam j).level ≤ 1 :=
          le_trans
            (Finset.le_sup
              (f := fun l => (h_fam l).level)
              (Finset.mem_univ j))
            (le_trans (le_max_left _ _)
              (Nat.le_of_succ_le_succ
                (by unfold KMor1.level at hyp; exact hyp)))
        omega
      have h_g : ∀ j, (g_fam j).level ≤ 2 := fun j => by
        have h1 : (g_fam j).level ≤ 1 :=
          le_trans
            (Finset.le_sup
              (f := fun l => (g_fam l).level)
              (Finset.mem_univ j))
            (le_trans (le_max_right _ _)
              (Nat.le_of_succ_le_succ
                (by unfold KMor1.level at hyp; exact hyp)))
        omega
      let bases : Fin (k + 1) → ERMor1 a :=
        fun j => kToER (h_fam j) (h_h j)
      let steps : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)) :=
        fun j => kToER (g_fam j) (h_g j)
      let p : ℕ × ℕ :=
        KMor1.majorize (.simrec i h_fam g_fam) hyp
      let bound : ERMor1 (a + 1) :=
        ERMor1.comp (ERMor1.A_two_iter p.1)
          (fun _ : Fin 1 => ERMor1.sumCtxERPlusOffset (a + 1) p.2)
      ERMor1.simultaneousBoundedRec k a bases steps bound i
```

- [ ] **Step 5.2: Build to verify**

Run: `lake build GebLean.LawvereKSimER 2>&1 | tail -15`

Expected: `Build completed successfully`, no warnings.

If the equation compiler complains about termination:

- The recursion is structural on `f`; Lean should infer
  `decreasing_by` automatically.
- If not, add `termination_by f => f` after the last
  branch.
- If Lean rejects the `let` chain in the simrec branch,
  refactor by inlining the lets into the
  `simultaneousBoundedRec` call (verbose but correct).

- [ ] **Step 5.3: Commit**

```bash
git add GebLean/LawvereKSimER.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 5: kToER structural-recursion def

All five constructor cases per master design §3.5.
Atomic constructors map to ER atoms; comp and raise
recurse; simrec routes through simultaneousBoundedRec with
bound from KMor1.majorize_by_componentBound.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 6 — `kToER` atomic-case interp lemmas

**Files:**

- Modify: `GebLean/LawvereKSimER.lean`

For atomic constructors and `raise`/`comp` non-recursive
unfolding, add small `@[simp]`-or-named lemmas establishing
the definitional unfolding of `(kToER ...).interp`.  These
support `kToER_interp`'s per-case dispatch.

- [ ] **Step 6.1: Add atomic interp lemmas**

Insert after `kToER`:

```lean
@[simp] theorem kToER_zero {a : ℕ} (h : (KMor1.zero (n := a)).level ≤ 2) :
    kToER (KMor1.zero (n := a)) h = ERMor1.zeroN a := rfl

@[simp] theorem kToER_succ (h : KMor1.succ.level ≤ 2) :
    kToER KMor1.succ h = ERMor1.succ := rfl

@[simp] theorem kToER_proj {a : ℕ} (i : Fin a)
    (h : (KMor1.proj i).level ≤ 2) :
    kToER (KMor1.proj i) h = ERMor1.proj i := rfl

@[simp] theorem kToER_raise {a : ℕ} (f : KMor1 a)
    (h : (KMor1.raise f).level ≤ 2)
    (h' : f.level ≤ 2) :
    kToER (KMor1.raise f) h = kToER f h' := by
  -- kToER raise body: passthrough (definitional).  The
  -- two level proofs are propositionally equal but not
  -- syntactically; rfl after the definitional unfolding.
  rfl

@[simp] theorem kToER_comp {a b : ℕ} (f : KMor1 b)
    (gs : Fin b → KMor1 a)
    (h : (KMor1.comp f gs).level ≤ 2)
    (hf : f.level ≤ 2)
    (hgs : ∀ i, (gs i).level ≤ 2) :
    kToER (KMor1.comp f gs) h
      = ERMor1.comp (kToER f hf)
          (fun i => kToER (gs i) (hgs i)) := by
  -- comp branch of kToER: structural translation.  The
  -- level-discharge `have`s in kToER's body are
  -- propositionally equal to the externally-supplied
  -- `hf` / `hgs` by Prop irrelevance; `rfl` closes.
  rfl
```

- [ ] **Step 6.2: Build to verify**

Run: `lake build GebLean.LawvereKSimER 2>&1 | tail -10`

Expected: `Build completed successfully`, no warnings.

If `kToER_raise`'s `rfl` fails due to proof-irrelevance:

- Try `unfold kToER` first.
- Try `congr` then close residual proof-irrelevance with
  `proof_irrel _ _` or `Subsingleton.elim _ _`.
- Worst case, drop the lemma — it's a convenience helper,
  not load-bearing.

- [ ] **Step 6.3: Commit**

```bash
git add GebLean/LawvereKSimER.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 6: kToER atomic-case interp simp lemmas

@[simp] lemmas for kToER_{zero, succ, proj, raise}
establishing definitional unfolding.  Supports
kToER_interp's per-case dispatch.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 7 — `kToER_simrec_dominates` (Factoring R helper)

**Files:**

- Modify: `GebLean/LawvereKSimER.lean`

This is the load-bearing helper: it produces the dominance
hypothesis that `simultaneousBoundedRec_interp_correct`
consumes.  Per spec §6.2.2, the helper takes the inductive
hypotheses (`ih_h`, `ih_g`) as arguments and produces the
dominance over the *kToER-translated* families.

- [ ] **Step 7.1: Add the theorem**

Insert (full body):

```lean
/-- Dominance hypothesis for
`ERMor1.simultaneousBoundedRec_interp_correct` at step 5's
simrec branch.  States that for each component `j` and
each iteration `m ≤ n`, the value-side simRecVec over the
kToER-translated families is dominated by the bound
`bound = comp (A_two_iter p.1) ![sumCtxERPlusOffset (a+1)
p.2]` evaluated at `Fin.cons m x`, where `p` is
`KMor1.majorize` of the simrec node.  Master design §3.5;
Tourlakis 2018 §0.1.0.34 (bounded-recursion closure
underlying step 4's bridge) + §0.1.0.10 (level-2
majorization). -/
theorem kToER_simrec_dominates
    {a k : ℕ}
    (i : Fin (k + 1))
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (hyp : (KMor1.simrec i h_fam g_fam).level ≤ 2)
    (h_h : ∀ j, (h_fam j).level ≤ 2)
    (h_g : ∀ j, (g_fam j).level ≤ 2)
    (ih_h : ∀ (j : Fin (k + 1))
             (h' : (h_fam j).level ≤ 2)
             (v' : Fin a → ℕ),
       (kToER (h_fam j) h').interp v'
         = (h_fam j).interp v')
    (ih_g : ∀ (j : Fin (k + 1))
             (h' : (g_fam j).level ≤ 2)
             (v' : Fin (a + 1 + (k + 1)) → ℕ),
       (kToER (g_fam j) h').interp v'
         = (g_fam j).interp v')
    (n : ℕ) (x : Fin a → ℕ) :
    let p := KMor1.majorize (.simrec i h_fam g_fam) hyp
    let bound : ERMor1 (a + 1) :=
      ERMor1.comp (ERMor1.A_two_iter p.1)
        (fun _ : Fin 1 => ERMor1.sumCtxERPlusOffset (a + 1) p.2)
    ∀ (m : ℕ), m ≤ n → ∀ (j : Fin (k + 1)),
      Nat.simRecVec k a
          (fun j' => (kToER (h_fam j') (h_h j')).interp)
          (fun j' => (kToER (g_fam j') (h_g j')).interp)
          m x j
        ≤ bound.interp (Fin.cons m x) := by
  intro p bound m _ j
  -- Step 1: rewrite kToER-translated families to K^sim
  -- families using the IHs.
  have h_bases :
      (fun j' => (kToER (h_fam j') (h_h j')).interp)
        = (fun j' => (h_fam j').interp) := by
    funext j' v'; exact ih_h j' (h_h j') v'
  have h_steps :
      (fun j' => (kToER (g_fam j') (h_g j')).interp)
        = (fun j' => (g_fam j').interp) := by
    funext j' v'; exact ih_g j' (h_g j') v'
  rw [h_bases, h_steps]
  -- Step 2: bridge Nat.simRecVec → KMor1.simrecVec.
  rw [← KMor1.simrecVec_eq_Nat_simRecVec h_fam g_fam x m j]
  -- Step 3: bridge KMor1.simrecVec ←
  -- (.simrec j h_fam g_fam).interp via reverse of
  -- KMor1.interp_simrec.
  have h_rev :
      KMor1.simrecVec h_fam g_fam x m j
        = (KMor1.simrec j h_fam g_fam).interp
            (Fin.cons m x) := by
    rw [KMor1.interp_simrec]
    congr 2
  rw [h_rev]
  -- Step 4: get the simrec at index j's level proof from
  -- index-independence of KMor1.level at simrec.  The
  -- simrec branch of KMor1.level (LawvereKSim.lean:112-114)
  -- ignores the index argument, so the equality
  -- (.simrec j ...).level = (.simrec i ...).level closes
  -- by `rfl`.  Fallback to `simp only [KMor1.level]` only
  -- if `rfl` fails (e.g., due to elaboration of the
  -- internal lambda).
  have h_j : (KMor1.simrec j h_fam g_fam).level ≤ 2 := by
    have hfact :
        (KMor1.simrec j h_fam g_fam).level
          = (KMor1.simrec i h_fam g_fam).level :=
      rfl
    rw [hfact]; exact hyp
  -- Step 5: apply step 4's bridge lemma.
  have h_dom :=
    KMor1.majorize_by_componentBound
      (.simrec j h_fam g_fam) h_j (Fin.cons m x)
  -- Step 6: align the bound at index j with `bound` at i.
  rw [KMor1.majorize_simrec_index_indep j i h_fam g_fam
        h_j hyp] at h_dom
  exact h_dom
```

- [ ] **Step 7.2: Build to verify**

Run: `lake build GebLean.LawvereKSimER 2>&1 | tail -15`

Expected: `Build completed successfully`, no warnings.

If errors occur:

- For Step 3 `congr 2` failure: try `congr 1`; if residual
  goals appear, dispatch them with
  `funext j'; rw [Fin.cons_succ]` /
  `simp only [Fin.cons_zero]`.
- For Step 4 `simp only [KMor1.level]` failure: the simrec
  branch of `KMor1.level` is at line 112-114 of
  `LawvereKSim.lean`; if `simp only` doesn't unfold the
  match, use `show ... = ...; rfl`.
- For Step 6 `rw` failure: the index-independence lemma
  rewrites `KMor1.majorize (.simrec j ...) h_j` to
  `KMor1.majorize (.simrec i ...) hyp`; if the `rw`
  pattern doesn't match (e.g., due to elaboration of the
  `bound` projection), use
  `change _ ≤ (KMor1.majorize (.simrec i h_fam g_fam) hyp,
   ...).interp ...` to align.

- [ ] **Step 7.3: Commit**

```bash
git add GebLean/LawvereKSimER.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 7: kToER_simrec_dominates Factoring R helper

5-step proof: IH-rewrite of families, bridge to
KMor1.simrecVec via simrecVec_eq_Nat_simRecVec, bridge to
.simrec j .interp via KMor1.interp_simrec reverse, apply
step 4's majorize_by_componentBound, align via
majorize_simrec_index_indep.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 8 — `kToER_simrec_bound_mono` (Factoring R helper)

**Files:**

- Modify: `GebLean/LawvereKSimER.lean`

Monotonicity of the bound in the iteration counter.  Used
as the `h_mono` argument to
`simultaneousBoundedRec_interp_correct`.

- [ ] **Step 8.1: Add the theorem**

Insert:

```lean
/-- Monotonicity of the kToER simrec bound in the
iteration counter.  The bound is `comp (A_two_iter p.1)
![sumCtxERPlusOffset (a+1) p.2]`; both `tower` and
`sumCtxER` are monotone in the slot incremented from `m`
to `n`.  Used as the `h_mono` argument to
`simultaneousBoundedRec_interp_correct`.  Master design
§3.5; transitively step 4 §3. -/
theorem kToER_simrec_bound_mono
    {a k : ℕ}
    (i : Fin (k + 1))
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (hyp : (KMor1.simrec i h_fam g_fam).level ≤ 2)
    (n : ℕ) (x : Fin a → ℕ) :
    let p := KMor1.majorize (.simrec i h_fam g_fam) hyp
    let bound : ERMor1 (a + 1) :=
      ERMor1.comp (ERMor1.A_two_iter p.1)
        (fun _ : Fin 1 => ERMor1.sumCtxERPlusOffset (a + 1) p.2)
    ∀ (m : ℕ), m ≤ n →
      bound.interp (Fin.cons m x)
        ≤ bound.interp (Fin.cons n x) := by
  intro p bound m h_m_le_n
  -- The bound's `fun _ : Fin 1 => sumCtxERPlusOffset
  -- (a+1) p.2` shape (post-round-1 M1 fix) does not need
  -- `Matrix.cons_val_zero`; the lambda's single argument
  -- beta-reduces directly under `interp_comp`.
  simp only [bound, ERMor1.interp_comp,
    ERMor1.interp_A_two_iter,
    ERMor1.interp_sumCtxERPlusOffset]
  apply tower_mono_right
  apply Nat.add_le_add_right
  exact ERMor1.sumCtxER_cons_le_of_le x h_m_le_n
```

- [ ] **Step 8.2: Build to verify**

Run: `lake build GebLean.LawvereKSimER 2>&1 | tail -10`

Expected: `Build completed successfully`, no warnings.

If errors:

- `tower_mono_right` lives in `Utilities/Tower.lean`;
  imported transitively via `LawvereKSimMajorization`.
- The `simp only` set must reduce `bound.interp` cleanly;
  if a residual `Matrix.cons` term remains, add
  `Matrix.cons_val_zero` (already present) or
  `Matrix.cons_val_succ`.

- [ ] **Step 8.3: Commit**

```bash
git add GebLean/LawvereKSimER.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 8: kToER_simrec_bound_mono

Monotonicity of the bound in the iteration counter, via
tower_mono_right + Nat.add_le_add_right +
sumCtxER_cons_le_of_le.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 9 — `kToER_interp_simrec` (Factoring R helper, assembly)

**Files:**

- Modify: `GebLean/LawvereKSimER.lean`

Assembles `simultaneousBoundedRec_interp_correct` with
Tasks 7 and 8's hypotheses to prove the simrec case of
`kToER_interp`.

- [ ] **Step 9.1: Add the theorem**

Insert:

```lean
/-- The simrec case of `kToER_interp`: combines step 2's
correctness theorem `simultaneousBoundedRec_interp_correct`
with step 5's `kToER_simrec_dominates` and
`kToER_simrec_bound_mono` (Tasks 7 and 8) plus the
inductive hypotheses on each child to establish that
`(kToER (.simrec i h_fam g_fam) h).interp` agrees with
`(KMor1.simrec i h_fam g_fam).interp`.  Master design §3.5;
Tourlakis 2018 §0.1.0.44 (level-2 case). -/
theorem kToER_interp_simrec
    {a k : ℕ}
    (i : Fin (k + 1))
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h : (KMor1.simrec i h_fam g_fam).level ≤ 2)
    (v : Fin (a + 1) → ℕ)
    (ih_h : ∀ (j : Fin (k + 1))
             (h' : (h_fam j).level ≤ 2)
             (v' : Fin a → ℕ),
       (kToER (h_fam j) h').interp v'
         = (h_fam j).interp v')
    (ih_g : ∀ (j : Fin (k + 1))
             (h' : (g_fam j).level ≤ 2)
             (v' : Fin (a + 1 + (k + 1)) → ℕ),
       (kToER (g_fam j) h').interp v'
         = (g_fam j).interp v') :
    (kToER (.simrec i h_fam g_fam) h).interp v
      = (KMor1.simrec i h_fam g_fam).interp v := by
  -- Reconstruct the level-discharge h_h, h_g locally so
  -- the proof body matches kToER's simrec-branch shape.
  have h_h : ∀ j, (h_fam j).level ≤ 2 := fun j => by
    have h1 : (h_fam j).level ≤ 1 :=
      le_trans
        (Finset.le_sup
          (f := fun l => (h_fam l).level)
          (Finset.mem_univ j))
        (le_trans (le_max_left _ _)
          (Nat.le_of_succ_le_succ
            (by unfold KMor1.level at h; exact h)))
    omega
  have h_g : ∀ j, (g_fam j).level ≤ 2 := fun j => by
    have h1 : (g_fam j).level ≤ 1 :=
      le_trans
        (Finset.le_sup
          (f := fun l => (g_fam l).level)
          (Finset.mem_univ j))
        (le_trans (le_max_right _ _)
          (Nat.le_of_succ_le_succ
            (by unfold KMor1.level at h; exact h)))
    omega
  -- Step 1: cons/tail-shape v.
  set n := v 0
  set x := Fin.tail v
  have hv : v = Fin.cons n x := (Fin.cons_self_tail v).symm
  rw [hv]
  -- Step 2: unfold kToER's simrec branch.  Use `change`
  -- rather than `show` for elaboration robustness —
  -- `show` requires exact goal-text match, while `change`
  -- accepts defeq-modulo-let unfolding.
  change (ERMor1.simultaneousBoundedRec k a
          (fun j => kToER (h_fam j) (h_h j))
          (fun j => kToER (g_fam j) (h_g j))
          (let p :=
            KMor1.majorize (.simrec i h_fam g_fam) h
           ERMor1.comp (ERMor1.A_two_iter p.1)
             (fun _ : Fin 1 =>
               ERMor1.sumCtxERPlusOffset (a + 1) p.2))
          i).interp (Fin.cons n x) = _
  -- Step 3: apply simultaneousBoundedRec_interp_correct.
  rw [ERMor1.simultaneousBoundedRec_interp_correct
        k a _ _ _ n x i
        (kToER_simrec_dominates i h_fam g_fam h
          h_h h_g ih_h ih_g n x)
        (kToER_simrec_bound_mono i h_fam g_fam h n x)]
  -- Step 4: convert the result's Nat.simRecVec form back
  -- to the K^sim simrec interp via IH + bridge +
  -- KMor1.interp_simrec.
  have h_bases :
      (fun j' => (kToER (h_fam j') (h_h j')).interp)
        = (fun j' => (h_fam j').interp) := by
    funext j' v'; exact ih_h j' (h_h j') v'
  have h_steps :
      (fun j' => (kToER (g_fam j') (h_g j')).interp)
        = (fun j' => (g_fam j').interp) := by
    funext j' v'; exact ih_g j' (h_g j') v'
  rw [h_bases, h_steps]
  rw [← KMor1.simrecVec_eq_Nat_simRecVec h_fam g_fam x n i]
  rw [KMor1.interp_simrec]
  congr 2
```

- [ ] **Step 9.2: Build to verify**

Run: `lake build GebLean.LawvereKSimER 2>&1 | tail -20`

Expected: `Build completed successfully`, no warnings.

If errors:

- The `show` move (Step 2) requires the goal text to
  match exactly.  Use `mcp__lean-lsp__lean_goal` to see
  the actual goal-text after the `rw [hv]`, and adjust
  the `show` to match.
- The `simultaneousBoundedRec_interp_correct` call must
  unify on its `(h, g, componentBound)` arguments — the
  underscores let Lean infer them from the goal.  If
  unification fails, write them out explicitly.
- The final `congr 2` should close after
  `KMor1.interp_simrec` reduces the K^sim-side simrec
  interp to a `simrecVec` form matching the LHS.  If
  residual goals remain, dispatch via
  `simp only [Fin.cons_zero, Fin.cons_succ]` (but verify
  no unused-tactic warning fires under
  `warningAsError = true`).

- [ ] **Step 9.3: Commit**

```bash
git add GebLean/LawvereKSimER.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 9: kToER_interp_simrec assembly

Combines simultaneousBoundedRec_interp_correct (step 2)
with kToER_simrec_dominates and kToER_simrec_bound_mono
(Tasks 7-8) plus the inductive hypotheses to prove the
simrec case of kToER_interp.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 10 — `kToER_interp` universal theorem

**Files:**

- Modify: `GebLean/LawvereKSimER.lean`

The universal correctness theorem.  Structural induction
on `f` dispatching to per-case helpers (atomic via
@[simp] lemmas from Task 6; comp via `congr_arg` + IH;
raise via passthrough; simrec via Task 9).

- [ ] **Step 10.1: Add the theorem**

Insert:

```lean
/-- Universal correctness of `kToER`: for every
`f : KMor1 a` of level ≤ 2 and every context `v`,
`(kToER f h).interp v = f.interp v`.  Realises Tourlakis
2018 §0.1.0.44 (K^sim_n ⊆ E^{n+1}) ⊆-direction pointwise
at level ≤ 2.  Master design §3.5. -/
theorem kToER_interp :
    ∀ {a : ℕ} (f : KMor1 a) (h : f.level ≤ 2)
      (v : Fin a → ℕ),
    (kToER f h).interp v = f.interp v
  | _, .zero,         _, _ => rfl
  | _, .succ,         _, _ => rfl
  | _, .proj _,       _, _ => rfl
  | _, .comp f gs,    h, v => by
      have hf  : f.level ≤ 2 :=
        le_trans (le_max_left _ _) h
      have hgs : ∀ i, (gs i).level ≤ 2 := fun i =>
        le_trans
          (Finset.le_sup
            (f := fun j => (gs j).level)
            (Finset.mem_univ i))
          (le_trans (le_max_right _ _) h)
      simp only [kToER, KMor1.interp_comp,
        ERMor1.interp_comp]
      congr 1
      · exact kToER_interp f hf _
      · funext i
        exact kToER_interp (gs i) (hgs i) v
  | _, .raise f,      h, v => by
      have hf : f.level ≤ 2 := by
        unfold KMor1.level at h; omega
      simp only [kToER, KMor1.interp_raise]
      exact kToER_interp f hf v
  | _, .simrec i h_fam g_fam, h, v =>
      have h_h : ∀ j, (h_fam j).level ≤ 2 := fun j => by
        have h1 : (h_fam j).level ≤ 1 :=
          le_trans
            (Finset.le_sup
              (f := fun l => (h_fam l).level)
              (Finset.mem_univ j))
            (le_trans (le_max_left _ _)
              (Nat.le_of_succ_le_succ
                (by unfold KMor1.level at h; exact h)))
        omega
      have h_g : ∀ j, (g_fam j).level ≤ 2 := fun j => by
        have h1 : (g_fam j).level ≤ 1 :=
          le_trans
            (Finset.le_sup
              (f := fun l => (g_fam l).level)
              (Finset.mem_univ j))
            (le_trans (le_max_right _ _)
              (Nat.le_of_succ_le_succ
                (by unfold KMor1.level at h; exact h)))
        omega
      kToER_interp_simrec i h_fam g_fam h v
        (fun j h' v' => kToER_interp (h_fam j) h' v')
        (fun j h' v' => kToER_interp (g_fam j) h' v')
```

The recursive calls to `kToER_interp` in the IH-supplier
position will compile as long as `kToER_interp` is
structurally recursive on `f`.  Lean's equation compiler
should accept this.

- [ ] **Step 10.2: Build to verify**

Run: `lake build GebLean.LawvereKSimER 2>&1 | tail -15`

Expected: `Build completed successfully`, no warnings.

If termination is rejected:

- Add `termination_by f h v => f` after the last branch.
- If the recursive call in the simrec branch's IH-suppliers
  is rejected (because `f.simrec` is not recognised as a
  decreasing argument), refactor by using `induction f`
  inside a `by` tactic body instead of pattern-matching at the
  def level.

- [ ] **Step 10.3: Commit**

```bash
git add GebLean/LawvereKSimER.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 10: kToER_interp universal theorem

Structural induction on f, dispatching to per-case
helpers: atomic constructors via rfl, comp via
congr+IH, raise via passthrough+IH, simrec via
kToER_interp_simrec (Task 9).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 11 — `kToERN` and `kToERN_interp`

**Files:**

- Modify: `GebLean/LawvereKSimER.lean`

Multi-output companion of `kToER`, with its correctness
theorem.

- [ ] **Step 11.1: Add the def and theorem**

Insert:

```lean
/-- Multi-output companion of `kToER`: pointwise lift to
`KMorN n m → ERMorN n m`.  Master design §3.5. -/
def kToERN {n m : ℕ} (f : KMorN n m)
    (h : ∀ i, (f i).level ≤ 2) : ERMorN n m :=
  fun i => kToER (f i) (h i)

/-- Componentwise correctness of `kToERN`: each component
of the kToERN-translated family agrees with the
corresponding K^sim component on every context.  Master
design §3.5. -/
theorem kToERN_interp {n m : ℕ} (f : KMorN n m)
    (h : ∀ i, (f i).level ≤ 2)
    (v : Fin n → ℕ) (j : Fin m) :
    (kToERN f h j).interp v = (f j).interp v :=
  kToER_interp (f j) (h j) v
```

- [ ] **Step 11.2: Build to verify**

Run: `lake build GebLean.LawvereKSimER 2>&1 | tail -10`

Expected: `Build completed successfully`, no warnings.

- [ ] **Step 11.3: Commit**

```bash
git add GebLean/LawvereKSimER.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 11: kToERN multi-output + kToERN_interp

Pointwise lift of kToER to KMorN families.  Correctness
theorem follows from componentwise application of
kToER_interp.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 12 — `kToERN_compat_extEq`

**Files:**

- Modify: `GebLean/LawvereKSimER.lean`

Quotient-lift well-definedness helper for `kToERFunctor`.

- [ ] **Step 12.1: Add the theorem**

Insert:

```lean
/-- Compatibility of `kToERN` with K^sim ext-eq:
extensionally-equal K^sim families produce extensionally-
equal ER families.  Used by `kToERFunctor.map` to discharge
the Quotient.lift well-definedness obligation.  Master
design §3.5. -/
theorem kToERN_compat_extEq {n m : ℕ}
    {f g : KMorN n m}
    (hf : ∀ i, (f i).level ≤ 2)
    (hg : ∀ i, (g i).level ≤ 2)
    (hfg : ∀ v i, (f i).interp v = (g i).interp v) :
    ∀ v i, (kToERN f hf i).interp v
            = (kToERN g hg i).interp v := by
  intro v i
  rw [kToERN_interp, kToERN_interp]
  exact hfg v i
```

- [ ] **Step 12.2: Build to verify**

Run: `lake build GebLean.LawvereKSimER 2>&1 | tail -10`

Expected: `Build completed successfully`, no warnings.

- [ ] **Step 12.3: Commit**

```bash
git add GebLean/LawvereKSimER.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 12: kToERN_compat_extEq

Quotient-lift well-definedness helper for kToERFunctor.
Two K^sim families with equal interps produce kToERN-
translated ER families with equal interps.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 13 — `kToERFunctor` obj + map

**Files:**

- Modify: `GebLean/LawvereKSimER.lean`

The categorical functor's object map (identity on ℕ) and
morphism map (Quotient.lift over the depth_witness).
Per spec §8.2.

- [ ] **Step 13.1: Add the obj and map**

Insert:

```lean
/-- Morphism component of the forward functor.  Lifts a
`KSimMor 2 n m` (an equivalence class of `KMorN n m`
families with depth-2 witness) to an `ERMorNQuo n m`.
Well-definedness via `kToERN_compat_extEq` plus
`Quotient.exact` on the depth-witness's `rep_eq` fields.
Master design §3.5 lines 1153-1163. -/
def kToERFunctor_map {n m : ℕ}
    (f : KSimMor 2 n m) : ERMorNQuo n m :=
  Quotient.liftOn f.depth_witness
    (fun rec => Quotient.mk (erMorNSetoid n m)
                 (kToERN rec.rep rec.rep_level))
    (fun rec₁ rec₂ _ => by
      apply Quotient.sound
      have h_eq :
          Quotient.mk (kMorNSetoid n m) rec₁.rep
            = Quotient.mk (kMorNSetoid n m) rec₂.rep :=
        rec₁.rep_eq.trans rec₂.rep_eq.symm
      have hrel :
          (kMorNSetoid n m).r rec₁.rep rec₂.rep :=
        Quotient.exact h_eq
      -- hrel : ∀ ctx, rec₁.rep.interp ctx
      --              = rec₂.rep.interp ctx
      -- where rec_i.rep.interp ctx : Fin m → ℕ.
      -- Per-component eq via congr_fun.
      intro v i
      exact kToERN_compat_extEq rec₁.rep_level
        rec₂.rep_level
        (fun v' i' => congr_fun (hrel v') i') v i)
```

- [ ] **Step 13.2: Build to verify**

Run: `lake build GebLean.LawvereKSimER 2>&1 | tail -15`

Expected: `Build completed successfully`, no warnings.

If errors:

- The `Quotient.exact h_eq` call requires `h_eq` to have
  shape `Quotient.mk _ a = Quotient.mk _ b`; if Lean
  doesn't infer this from `rec₁.rep_eq.trans
  rec₂.rep_eq.symm`, write out the type ascription.
- The setoid relation `(kMorNSetoid n m).r` may need
  unfolding via `simp only [kMorNSetoid]` to expose the
  pointwise interp-equality.  Inspect the setoid's
  definition at `LawvereKSimQuot.lean:21-31`.

- [ ] **Step 13.3: Commit**

```bash
git add GebLean/LawvereKSimER.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 13: kToERFunctor_map (morphism component)

Quotient.liftOn over depth_witness; well-definedness via
kToERN_compat_extEq + Quotient.exact on rep_eq.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 14 — `kToERFunctor.map_id`

**Files:**

- Modify: `GebLean/LawvereKSimER.lean`

The first functor law.

- [ ] **Step 14.1: Add the theorem**

Insert:

```lean
/-- Functor law: `kToERFunctor_map` preserves identities.
The `𝟙 n` morphism in `LawvereKSimDCat 2` has
representative `KMorN.id n`; its kToERN-translation
componentwise equals `ERMorN.id n` (since
`kToER (KMor1.proj i) _ = ERMor1.proj i`).  Master design
§3.5. -/
theorem kToERFunctor_map_id (n : LawvereKSimDCat 2) :
    kToERFunctor_map (𝟙 n) = 𝟙 (n : LawvereERCat) := by
  -- Unfold the morphism map's Quotient.liftOn so the
  -- inner Quotient.mk on the ER side becomes visible.
  unfold kToERFunctor_map
  -- After Quotient.liftOn_mk fires (which it does
  -- definitionally on Quotient.mk-applied liftOn), the
  -- goal is Quotient.mk _ (kToERN ...) = Quotient.mk _ (...).
  apply Quotient.sound
  intro v i
  -- Per-component extEq.  Use kToER_proj for the proj-i
  -- atom on the K^sim side, ERMor1.interp_proj for the
  -- ER side.
  -- kToERFunctor_map uses Quotient.liftOn (not lift), so
  -- only Quotient.liftOn_mk is needed here.
  simp only [Quotient.liftOn_mk,
    kToERN, kToER_proj, KMorN.id, ERMorN.id,
    KMor1.interp_proj, ERMor1.interp_proj]
```

- [ ] **Step 14.2: Build to verify**

Run: `lake build GebLean.LawvereKSimER 2>&1 | tail -10`

Expected: `Build completed successfully`, no warnings.

If `Quotient.liftOn_mk` / `Quotient.lift_mk` fail to fire:

- Check the actual name in current mathlib via
  `lean_local_search "Quotient.liftOn"`.
- The simp set may need
  `Quotient.mk_eq_mk` instead of / in addition to.
- If `simp only` leaves residual goals, add a `congr 1`
  followed by component dispatch.
- Worst case: replace the `simp only` with a chained
  `unfold` followed by `rfl`.

- [ ] **Step 14.3: Commit**

```bash
git add GebLean/LawvereKSimER.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 14: kToERFunctor.map_id

First functor law.  Quotient.sound + simp set including
Quotient.liftOn_mk to fire through the lift wrapper.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 15 — `kToERFunctor.map_comp`

**Files:**

- Modify: `GebLean/LawvereKSimER.lean`

The second functor law.

- [ ] **Step 15.1: Add the theorem**

Insert:

```lean
/-- Functor law: `kToERFunctor_map` preserves composition.
`kToER`'s `comp` branch translates `KMor1.comp f gs`
literally to `ERMor1.comp (kToER f) (fun i => kToER (gs i))`,
and `kToERN` commutes with `KMorN.comp` pointwise.  Master
design §3.5. -/
theorem kToERFunctor_map_comp {n m k : ℕ}
    (f : KSimMor 2 n m) (g : KSimMor 2 m k) :
    kToERFunctor_map (f ≫ g)
      = kToERFunctor_map f ≫ kToERFunctor_map g := by
  unfold kToERFunctor_map
  apply Quotient.sound
  intro v i
  -- kToER_comp from Task 6 reduces the kToER of a
  -- composition to ERMor1.comp at the morphism level.
  -- kToERFunctor_map uses Quotient.liftOn (not lift), so
  -- only Quotient.liftOn_mk is needed here.
  simp only [Quotient.liftOn_mk,
    kToERN, kToER_comp, KMorN.comp, ERMorN.comp,
    KMor1.interp_comp, ERMor1.interp_comp]
```

- [ ] **Step 15.2: Build to verify**

Run: `lake build GebLean.LawvereKSimER 2>&1 | tail -10`

Expected: `Build completed successfully`, no warnings.

Failure handling: see Task 14.

- [ ] **Step 15.3: Commit**

```bash
git add GebLean/LawvereKSimER.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 15: kToERFunctor.map_comp

Second functor law via Quotient.sound + simp set.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 16 — Bundle `kToERFunctor`

**Files:**

- Modify: `GebLean/LawvereKSimER.lean`

Assemble the categorical functor from the obj, map,
map_id, and map_comp components.

- [ ] **Step 16.1: Add the bundled functor**

Insert:

```lean
/-- The forward functor of the categorical equivalence
`LawvereKSimDCat 2 ≌ LawvereERCat` (forward direction;
reverse direction in step 10, equivalence assembled in
step 11).  Master design §3.5. -/
def kToERFunctor : CategoryTheory.Functor
    (LawvereKSimDCat 2) LawvereERCat where
  obj n := n
  map := kToERFunctor_map
  map_id := kToERFunctor_map_id
  map_comp := kToERFunctor_map_comp
```

- [ ] **Step 16.2: Build to verify**

Run: `lake build GebLean.LawvereKSimER 2>&1 | tail -10`

Expected: `Build completed successfully`, no warnings.

- [ ] **Step 16.3: Commit**

```bash
git add GebLean/LawvereKSimER.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 16: kToERFunctor bundle

Bundle obj, map, map_id, map_comp into the categorical
Functor instance.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 17 — Test module skeleton + Tier 1 atomic `#guard`s

**Files:**

- Create: `GebLeanTests/LawvereKSimER.lean`
- Modify: `GebLeanTests.lean` (alphabetical insertion of
  `import GebLeanTests.LawvereKSimER`)

Per discipline #1, the test-module creation and the
test-driver registration land in the same task.

- [ ] **Step 17.1: Create the test module**

Create `GebLeanTests/LawvereKSimER.lean`:

```lean
import GebLean

namespace GebLeanTests.LawvereKSimER

open GebLean

-- Tier 1 — atomic kToER definitional rfl checks.

example : kToER (a := 3) KMor1.zero
              (by simp [KMor1.level])
            = ERMor1.zeroN 3 := rfl

example : kToER KMor1.succ (by simp [KMor1.level])
            = ERMor1.succ := rfl

example : kToER (a := 3)
              (KMor1.proj (Fin.mk 1 (by omega)))
              (by simp [KMor1.level])
            = ERMor1.proj (Fin.mk 1 (by omega)) := rfl

example {f : KMor1 2}
        (h : (KMor1.raise f).level ≤ 2)
        (h' : f.level ≤ 2) :
    kToER (KMor1.raise f) h = kToER f h' := rfl

end GebLeanTests.LawvereKSimER
```

- [ ] **Step 17.2: Register the test module in `GebLeanTests.lean`**

Read `GebLeanTests.lean`.  Add `import GebLeanTests.LawvereKSimER`
in alphabetical order.

- [ ] **Step 17.3: Build to verify**

Run: `lake build GebLeanTests.LawvereKSimER 2>&1 | tail -10`
followed by `lake test 2>&1 | tail -10`.

Expected: both succeed; no warnings.

If `rfl` fails on any test:

- For atoms (zero/succ/proj): the level-discharge
  `by simp [KMor1.level]` should produce a term that
  matches what `kToER`'s match arm reduces to.  If not,
  check whether `kToER`'s level-proof argument needs to be
  unified explicitly via `(_ : (KMor1.zero (n := 3)).level
  ≤ 2)`.
- For `raise`: the proof-irrelevance concern noted in Task 6
  may bite; if so, the test is a casualty — drop it or
  prove it by `unfold kToER; rfl`.

- [ ] **Step 17.4: Commit**

```bash
git add GebLeanTests/LawvereKSimER.lean GebLeanTests.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 17: Test module skeleton + Tier 1 atomic guards

Atomic kToER rfl checks (zero, succ, proj, raise) in new
test module GebLeanTests/LawvereKSimER.lean.  Module
registered in GebLeanTests.lean.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 18 — Tier 2 universal-theorem `example` proofs

**Files:**

- Modify: `GebLeanTests/LawvereKSimER.lean`

Inline `addK : KMor1 2` construction + `kToER_interp`
applications at concrete inputs.

- [ ] **Step 18.1: Add inline `addK` and Tier 2 examples**

Append to the test module (before the closing `end`):

```lean
-- Tier 2 — universal-theorem example proofs.
--
-- Inline addK : KMor1 2 simrec witness (level 1).
-- λ(x, y). x + y, defined via simrec over successor.
-- The Phase-1 addK at GebLeanTests/LawvereKSimInterp.lean
-- is private; reconstruct here for step 5's tests.
private def addK : KMor1 2 :=
  KMor1.simrec (k := 0)
    ⟨0, by omega⟩
    -- Base family at index 0: KMor1 1 returning the
    -- single parameter (= y, since arity 1 with one
    -- input slot).
    (fun _ => KMor1.proj 0)
    -- Step family at index 0: KMor1 (1 + 1 + 1) = KMor1 3.
    -- Inputs: slot 0 = iter counter, slot 1 = parameter
    -- (= y), slot 2 = previous-iter value.  Apply succ to
    -- slot 2.
    (fun _ =>
      KMor1.comp KMor1.succ
        ![KMor1.proj 2])

example : (kToER addK
              (by simp [addK, KMor1.level])).interp ![3, 5]
            = addK.interp ![3, 5] :=
  kToER_interp addK (by simp [addK, KMor1.level]) ![3, 5]

example : (kToER addK
              (by simp [addK, KMor1.level])).interp ![0, 7]
            = addK.interp ![0, 7] :=
  kToER_interp addK (by simp [addK, KMor1.level]) ![0, 7]
```

- [ ] **Step 18.2: Build and test**

Run: `lake build GebLeanTests.LawvereKSimER 2>&1 | tail -10`
followed by `lake test 2>&1 | tail -10`.

Expected: both succeed; no warnings.

If `addK.level` doesn't reduce to ≤ 2 via
`simp [addK, KMor1.level]`:

- Use `lean_goal` to inspect what `addK.level` reduces to.
- The simrec branch of `KMor1.level` is `max ... + 1`;
  `addK`'s base + step are all level-0 atoms, so
  `addK.level = 1 ≤ 2`.
- If the simp doesn't reduce the `Finset.univ.sup`, add
  `Finset.sup_singleton` or unfold manually.

- [ ] **Step 18.3: Commit**

```bash
git add GebLeanTests/LawvereKSimER.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 18: Tier 2 universal-theorem example proofs

Inline addK : KMor1 2 simrec witness (level 1) plus
kToER_interp applications at concrete inputs ![3, 5] and
![0, 7].  Per discipline #4: ER-side .interp #guard not
practical for simrec terms.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 19 — Tier 3 `kToERFunctor` sanity tests

**Files:**

- Modify: `GebLeanTests/LawvereKSimER.lean`

- [ ] **Step 19.1: Add Tier 3 examples**

Append to the test module:

```lean
-- Tier 3 — kToERFunctor sanity.

example : kToERFunctor.obj 5 = 5 := rfl

example {n : ℕ} :
    kToERFunctor.map (𝟙 (n : LawvereKSimDCat 2))
      = 𝟙 (kToERFunctor.obj n) :=
  kToERFunctor.map_id n
```

- [ ] **Step 19.2: Build and test**

Run: `lake test 2>&1 | tail -10`.

Expected: pass; no warnings.

- [ ] **Step 19.3: Commit**

```bash
git add GebLeanTests/LawvereKSimER.lean
git commit -m "$(cat <<'EOF'
Step 5 Task 19: Tier 3 kToERFunctor sanity tests

obj-fixed-point and map_id sanity check.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 20 — Final verification + workstream update

**Files:**

- Modify: `.session/workstreams/er-ksim2-equiv-via-urm.md`
  (add step 5 completion entry)

Final clean-build check, axiom audit, and workstream
update.

- [ ] **Step 20.1: Clean build verification**

Run: `lake build 2>&1 | tail -20`

Expected: `Build completed successfully`, zero
`error:` lines, zero `warning:` lines.

- [ ] **Step 20.2: Test verification**

Run: `lake test 2>&1 | tail -20`

Expected: all tests pass; zero new failures; zero new
warnings.

- [ ] **Step 20.3: Axiom hygiene check**

Open `GebLean/LawvereKSimER.lean` in lean-lsp and add at
the end of the file (temporarily):

```lean
#print axioms kToER
#print axioms kToER_interp
#print axioms kToERFunctor
```

Run via `mcp__lean-lsp__lean_diagnostic_messages`.
Expected output: each `#print axioms` reports only Lean's
native axioms (`propext`, `Quot.sound`, possibly
`Classical.choice` from mathlib transitively if
unavoidable).  Confirm no custom axioms (`sorry`, `axiom`,
or non-constructive imports) are introduced.

Per CLAUDE.md, the development must be fully
constructive; if `Classical.choice` shows up in the
axiom list and is reachable from the new code (not just
mathlib transitively), trace and eliminate.

After verification, remove the `#print axioms` lines.

- [ ] **Step 20.4: Workstream update**

Append to `.session/workstreams/er-ksim2-equiv-via-urm.md`
under the existing "Progress" section:

```markdown
- Step 5 (`kToER` structural-recursion functor):
  complete.  Lands `kToER : KMor1 a → ERMor1 a` (level ≤
  2), `kToERN` multi-output companion, the universal
  correctness theorem `kToER_interp` (Tourlakis 2018
  §0.1.0.44 ⊆ pointwise, level-2 case), three Factoring R
  simrec-branch helpers (`kToER_simrec_dominates`,
  `kToER_simrec_bound_mono`, `kToER_interp_simrec`), the
  Quotient-lift well-definedness helper
  `kToERN_compat_extEq`, and the categorical functor
  `kToERFunctor : LawvereKSimDCat 2 ⥤ LawvereERCat` with
  `map_id` and `map_comp`.  Adds three small lemmas to
  existing modules: `KMor1.simrecVec_eq_Nat_simRecVec` to
  `LawvereKSimInterp.lean` (bridge between K^sim simrecVec
  and Nat.simRecVec), `KMor1.majorize_simrec_index_indep`
  + `ERMor1.sumCtxER_cons_le_of_le` to
  `LawvereKSimMajorization.lean`.  Plan at
  `docs/superpowers/plans/2026-05-03-step-5-ksim-to-er-functor.md`.
  Spec at
  `docs/superpowers/specs/2026-05-03-step-5-ksim-to-er-functor-design.md`.
  3 rounds adversarial review on the spec; round 3 reports
  0 blockers / 0 majors.
```

Update "Next steps" to say:

```markdown
- Step 6: RegisterMachine audit (master design §4 + step 6).
  Begin the URM-side chain for the reverse direction
  `erToK : ERMor1 a → KMor1 a`.
```

- [ ] **Step 20.5: Final commit**

```bash
git add .session/workstreams/er-ksim2-equiv-via-urm.md
git commit -m "$(cat <<'EOF'
Step 5 Task 20: final verification + workstream update

All Tier 1-3 tests pass; clean build; axiom hygiene
verified.  Workstream updated with step 5 completion
entry; next steps point to step 6 (URM register-machine
audit) for the reverse direction.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Next steps (after step 5 lands)

Master design's serial chain on the kToER side completes
at step 5: `0 → 1 → 2 → 3 → 4 → 5`.  Step 11 (the
categorical iso) requires step 5 + step 10.  Steps 6-10
form the erToK side (URM-simulation) and are independent
of step 5.

Recommended next cycle: step 6 (`RegisterMachine.lean`
audit; near-empty cycle per master design) →
step 7 (`URMConcrete.lean`) → step 8 / 9 (parallel) →
step 10 (`erToK` + `erToKFunctor`) → step 11
(categorical iso).

If opportunistic Scope-B helpers were added in step 5
(per spec §1.2), note them in the step-5 completion entry
so step 11 can find them.

---

## Self-review

After writing this plan, verify each spec section maps
to a task:

| Spec section | Task |
|---|---|
| §3.1 LawvereKSimInterp.lean addition | Task 1 |
| §3.1 majorize_simrec_index_indep | Task 2 |
| §3.1 sumCtxER_cons_le_of_le | Task 3 |
| §3.1 LawvereKSimER.lean NEW | Tasks 4-16 |
| §3.1 GebLean.lean import | Task 4 |
| §3.1 GebLeanTests/LawvereKSimER.lean | Tasks 17-19 |
| §3.1 GebLeanTests.lean import | Task 17 |
| §3.2 LawvereKSimER.lean import set | Task 4 |
| §4 kToER def | Task 5 (all five constructor cases) |
| §4.4 termination | Task 5 step 5.2 |
| §5 kToER_interp universal theorem | Task 10 |
| §6.1 simrecVec_eq_Nat_simRecVec bridge | Task 1 |
| §6.2.1 majorize_simrec_index_indep | Task 2 |
| §6.2.2 kToER_simrec_dominates | Task 7 |
| §6.2.3 kToER_simrec_bound_mono + sumCtxER_cons_le_of_le | Tasks 8, 3 |
| §6.2.4 kToER_interp_simrec | Task 9 |
| §6.3 risk callouts | Distributed across Tasks 5, 6, 9 step instructions |
| §7 kToERN + kToERN_interp | Task 11 |
| §7.2 kToERN_compat_extEq | Task 12 |
| §8.1 kToERFunctor signature | Task 16 |
| §8.2 kToERFunctor_map | Task 13 |
| §8.3 functor laws map_id / map_comp | Tasks 14, 15 |
| §8.4 opportunistic step-11 helpers | Implementer-discretion |
| §9.1 Tier 1 atomic #guards | Task 17 |
| §9.2 Tier 2 example proofs (inline addK) | Task 18 |
| §9.3 Tier 3 functor sanity | Task 19 |
| §10 discipline cross-references | Plan-header + per-task |
| §11 acceptance criteria | Task 20 |
| §12 reference catalogue | Imports per Task 4 |

All spec content covered; no orphan tasks.

Method-name consistency check: `kToER`, `kToERN`,
`kToER_interp`, `kToERN_interp`, `kToER_simrec_dominates`,
`kToER_simrec_bound_mono`, `kToER_interp_simrec`,
`kToERN_compat_extEq`, `kToERFunctor`, `kToERFunctor_map`,
`kToERFunctor_map_id`, `kToERFunctor_map_comp` — all
consistent across tasks.

---

## Execution handoff

Plan complete and saved to
`docs/superpowers/plans/2026-05-03-step-5-ksim-to-er-functor.md`.
20 tasks; estimated ~12-20 hours of implementer work.

Two execution options:

**1. Subagent-Driven (recommended)** — dispatch a fresh
subagent per task, review between tasks, fast iteration.
Per the project's discipline established in steps 1-4,
substantive tasks (Task 1's bridge proof, Task 7's 5-step
chain, Task 9's correctness proof, Task 13's
well-definedness, Tasks 14-15 functor laws) get a
spec-compliance reviewer subagent; trivially mechanical
tasks (skeleton creation, atomic def additions) skip the
extra review.

**2. Inline Execution** — execute tasks in this session
using `superpowers:executing-plans` with batch checkpoints.

Which approach?
