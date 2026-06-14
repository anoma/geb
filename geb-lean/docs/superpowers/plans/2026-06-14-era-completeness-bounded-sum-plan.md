# Era completeness — implementation plan (Phase 1 + M3 gate)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Scope and staging](#scope-and-staging)
- [File structure](#file-structure)
- [Task 1: Bridge module skeleton](#task-1-bridge-module-skeleton)
- [Task 2: Per-operation `ERMor1` witnesses for the basis](#task-2-per-operation-ermor1-witnesses-for-the-basis)
- [Task 3: The soundness inclusion (Era into ER)](#task-3-the-soundness-inclusion-era-into-er)
- [Task 4: M3 construction-choice assessment (the gate)](#task-4-m3-construction-choice-assessment-the-gate)
- [Deferred to the follow-on plan (after Task 4)](#deferred-to-the-follow-on-plan-after-task-4)
- [Self-review](#self-review)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps
> use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Establish the bridge module and the soundness direction
`Era ⊆ E³` of basis adequacy, then resolve the bounded-sum construction
choice at the M3 gate so the engine and completeness assembly can be
planned in detail.

**Architecture:** A new Mathlib-importing bridge module
`GebLean/EraCompleteness.lean` relates `Era`'s term denotations
(`Tm.eval eraInterp`) to `ERMor1`. Phase 1 builds the easy inclusion by
mapping each `ETm` to an `ERMor1` term using the arithmetic already in
`Utilities/ERArith.lean`. Phase 2 is the construction-choice assessment
(spec § 13) that gates the harder completeness direction.

**Tech stack:** Lean 4, Mathlib (`ERMor1`, `Dioph`, number theory),
`lake build`/`lake test`/`lake lint`, `scripts/check-axioms.sh`, `jj`.

---

## Scope and staging

The companion spec
(`docs/superpowers/specs/2026-06-14-era-completeness-bounded-sum-design.md`)
has milestones M1–M5. M2/M3 contain a genuine construction-choice gate:
the bounded-sum term former `eraBSum` may follow the Marchenkov `σ`
route, a direct rich-basis closed form, or lean partly on Mathlib's
`Dioph`. Detailing `eraBSum`'s proof steps before that choice is made
would be speculative. This plan therefore covers only what is
determined:

- **Phase 1 (spec M5 soundness half + M1 bridge):** the bridge module
  and `era_sound_er` (`Era ⊆ E³`). Fully concrete; pure reuse.
- **Phase 2 (spec M2/M3 gate):** the construction-choice assessment,
  whose deliverable is a decision that unblocks the engine.

Deferred to a follow-on plan, written after Phase 2 fixes the
construction: `eraBSum` (M3), `eraBProd` (M4), `era_complete` and the
K-sim-2 corollary (M5 completeness half). See "Deferred" below.

Each task lands at a sorry-free, axiom-clean, committable state (`sorry`
is permitted only between commits, never in a commit). In Lean the unit
test is the build plus `scripts/check-axioms.sh`; proof tactics are
discovered interactively during execution, so proof steps state the goal
and the exact lemmas to use rather than guaranteed-final tactic scripts.

## File structure

- Create: `GebLean/EraCompleteness.lean` — the bridge. Responsibility:
  relate `ETm` denotations to `ERMor1`. Imports `GebLean.Era` and
  `GebLean.LawvereER` (hence Mathlib); `Era.lean` is not modified and
  keeps its no-Mathlib property.
- Modify: `GebLean.lean` — add `import GebLean.EraCompleteness` so the
  default `GebLean` lib target builds it.
- Test: assertions live in the module itself (the build is the test);
  no separate `GebLeanTests` file is required for Phase 1.

---

## Task 1: Bridge module skeleton

**Files:**

- Create: `GebLean/EraCompleteness.lean`
- Modify: `GebLean.lean` (add one import line, alphabetical/position to
  match the existing block around `import GebLean.LawvereER`)

- [ ] **Step 1: Create the module with header and namespace**

Mirror the header style of `GebLean/LawvereER.lean` (import-first, no
copyright header, module docstring with the required sections). Content:

```lean
import GebLean.Era
import GebLean.LawvereER

/-!
# Era basis completeness bridge

Relates the denotations of `Era` terms (`Tm.eval eraInterp`) to the
Kalmár elementary functions as formalised by `ERMor1`
(`GebLean/LawvereER.lean`).

## Main statements

* `era_sound_er` — every `ETm` denotes an `ERMor1` function
  (the inclusion `Era ⊆ E³`).

## References

* Prunescu, Sauras-Altuzarra, Shunia, arXiv:2505.23787.

## Tags

elementary recursive, substitution basis, completeness
-/

namespace GebLean.EraCompleteness

open Era

end GebLean.EraCompleteness
```

- [ ] **Step 2: Register the module**

Add `import GebLean.EraCompleteness` to `GebLean.lean` next to the other
`GebLean.*` imports.

- [ ] **Step 3: Build**

Run: `lake build GebLean.EraCompleteness`
Expected: builds with no errors (empty namespace).

- [ ] **Step 4: Commit**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): add EraCompleteness bridge module skeleton"
```

(End commit messages with the `Co-Authored-By` trailer per project
convention.)

---

## Task 2: Per-operation `ERMor1` witnesses for the basis

Each `eraInterp` operation must be exhibited as an `ERMor1` term. The
witnesses already exist in `Utilities/ERArith.lean` (and `LawvereER`):
`ERMor1.addN` (`interp_addN`), `ERMor1.mod` (`interp_mod`), `ERMor1.sub`
(`interp_sub`), `ERMor1.mulN` (`interp_mulN`), `ERMor1.div`
(`interp_div`), `ERMor1.powN` (`interp_powN`); `2 ^ x` is `powN`
composed with the constant `2` (`ERMor1.natN`) and `proj 0`.

**Files:**

- Modify: `GebLean/EraCompleteness.lean`

- [ ] **Step 1: Define the operation map**

```lean
/-- The `ERMor1` term realising each basis operation. -/
def eraOpToER : (b : EraB) → ERMor1 (eraAr b)
  | .add  => ERMor1.addN
  | .mod  => ERMor1.mod
  | .pow2 => ERMor1.comp ERMor1.powN ![ERMor1.natN 1 2, ERMor1.proj (0 : Fin 1)]
  | .tsub => ERMor1.sub
  | .mul  => ERMor1.mulN
  | .div  => ERMor1.div
  | .pow  => ERMor1.powN
```

(`![…]` is Mathlib's `Matrix.of`/`Fin.cons` vector notation; the `pow2`
case builds `2 ^ (ctx 0)`. Verify `ERMor1.natN`'s exact arity arguments
against `interp_natN` at `ERArith.lean:82` during execution.)

- [ ] **Step 2: Build to confirm it elaborates**

Run: `lake build GebLean.EraCompleteness`
Expected: builds (it is a total `def`, no `sorry`).

- [ ] **Step 3: State and prove the correctness lemma**

```lean
theorem eraOpToER_interp (b : EraB) (ctx : Fin (eraAr b) → ℕ) :
    (eraOpToER b).interp ctx = eraInterp b ctx := by
  cases b <;> ...   -- prove per constructor; not a uniform one-liner
```

Strategy (a single `simp` does not close it; two known wrinkles):

- `eraInterp` (`Era.lean:483`) produces proof-carrying `Fin` indices
  `ctx ⟨0, _⟩` / `ctx ⟨1, _⟩`; reduce `eraAr b` and normalise these to
  `ctx 0` / `ctx 1` over `Fin 2`.
- `interp_addN`, `interp_mulN`, `interp_powN` (`ERArith.lean:58,35,1278`)
  accept a generic `ctx`, so `add`/`mul`/`pow` close directly; `tsub`
  uses `interp_sub` (`LawvereER.lean:116`); `pow2` uses `interp_comp` +
  `interp_powN` + `interp_natN` + `interp_proj`. But `interp_mod` and
  `interp_div` (`ERArith.lean:689,646`) are stated only for the literal
  vector `![a, b]`, so in the `mod`/`div` cases rewrite
  `ctx = ![ctx 0, ctx 1]` (Fin-2 eta) before the lemma fires.

- [ ] **Step 4: Verify**

Run: `lake build GebLean.EraCompleteness && lake lint`
Run: `bash scripts/check-axioms.sh` (expect only `propext`,
`Quot.sound`, `Classical.choice`)
Expected: no errors; `eraOpToER` and `eraOpToER_interp` are sorry-free.

- [ ] **Step 5: Commit**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): map each basis operation to an ERMor1 witness"
```

---

## Task 3: The soundness inclusion (Era into ER)

Map every `ETm` to an `ERMor1` term by structural recursion, then prove
denotational agreement. A computable recursion (not a choice-based
existence) keeps the construction constructive.

**Files:**

- Modify: `GebLean/EraCompleteness.lean`

- [ ] **Step 1: Define the term translation**

```lean
/-- Translate an `Era` term to an `ERMor1` term of the same arity. -/
def erOfETm {n : ℕ} : ETm n → ERMor1 n
  | .var i    => ERMor1.proj i
  | .zero     => ERMor1.natN n 0
  | .succ t   => ERMor1.comp ERMor1.succ ![erOfETm t]
  | .app b ts => ERMor1.comp (eraOpToER b) (fun i => erOfETm (ts i))
```

Match only on the term, with `n` implicit in scope (used in the `zero`
case as `ERMor1.natN n 0`, the arity-`n` constant `0`). This mirrors
`Tm.eval` (`Era.lean:473`), which recurses through `app`'s
`Fin (ar b) → Tm` family the same way and compiles. Matching on the
index instead (`| n, .zero => …`) defeats the structural-recursion
checker; if the equation compiler still does not infer termination here,
add `termination_by t => sizeOf t` with a `decreasing_by` discharging
`sizeOf (ts i) < sizeOf (Tm.app b ts)`.

- [ ] **Step 2: Build to confirm it elaborates**

Run: `lake build GebLean.EraCompleteness`
Expected: builds, as `Tm.eval` does. If the equation compiler does not
infer termination, apply the `termination_by`/`decreasing_by` note above,
then build.

- [ ] **Step 3: State and prove the agreement lemma**

```lean
theorem erOfETm_interp {n : ℕ} (t : ETm n) (ctx : Fin n → ℕ) :
    (erOfETm t).interp ctx = Tm.eval eraInterp t ctx := by
  induction t with
  | var i => simp [erOfETm, Tm.eval]
  | zero => simp [erOfETm, Tm.eval]
  | succ t ih => simp [erOfETm, Tm.eval, ih]
  | app b ts ih => simp [erOfETm, Tm.eval, eraOpToER_interp, ih]
```

Goal: each case reduces both sides equationally; the `app` case uses
`eraOpToER_interp` and the induction hypotheses `ih` for the arguments
(via `ERMor1.interp_comp` and `funext`). Fill exact rewrites during
execution.

- [ ] **Step 4: State the soundness corollary**

```lean
/-- Every `Era` term denotes an `ERMor1` (elementary) function. -/
theorem era_sound_er {n : ℕ} (t : ETm n) :
    ∃ f : ERMor1 n, ∀ ctx, f.interp ctx = Tm.eval eraInterp t ctx :=
  ⟨erOfETm t, erOfETm_interp t⟩
```

- [ ] **Step 5: Verify**

Run: `lake build GebLean.EraCompleteness && lake lint`
Run: `bash scripts/check-axioms.sh` (expect only `propext`,
`Quot.sound`, `Classical.choice`)
Expected: `erOfETm`, `erOfETm_interp`, `era_sound_er` sorry-free and
axiom-clean.

- [ ] **Step 6: Commit**

```bash
bash scripts/pre-commit.sh
jj describe -m "feat(era): prove the Era-into-ER soundness inclusion"
```

---

## Task 4: M3 construction-choice assessment (the gate)

This is an investigative task, not a TDD cycle; its deliverable is a
decision that unblocks the engine plan. It corresponds to the spec's
M2/M3 opening assessment (spec § 5 Library reuse, § 13).

**Files:**

- Create: `docs/superpowers/notes/<date>-erabsum-construction-decision.md`
  (markdownlint-clean, with a doctoc TOC if it has more than one `##`).

- [ ] **Step 1: Evaluate the Mathlib `Dioph` route**

Determine concretely whether `Mathlib.NumberTheory.Dioph` can yield a
*constructive* bounded-sum `Era` term. Expected obstruction (spec § 5):
`Dioph S` is a classical `Prop` with unbounded `∃`, so it cannot define
a computable term under the `noncomputable` ban; confirm this against the
actual definitions (`Dioph`, `DiophFn`, `Dioph.pow_dioph`) and record the
precise point of failure (or, if it transfers, how).

- [ ] **Step 2: Probe a direct rich-basis closed form**

Attempt, in a throwaway module under `GebLean/`, a search-free `Era`
term for a representative bounded sum (e.g. `Σ_{i<y} c`, then a
non-constant body), using `mod`, `div`, `pow2`, `pow` and the
`mod (β − 1)` digit-extraction idea (spec § 13). Record whether the
recursion/packing closes without a bounded search.

- [ ] **Step 3: Scope the Marchenkov `σ` fallback**

If neither route above closes, outline the Marchenkov § 4–§ 5 transcription
against the available Mathlib support (`geom_sum_eq`, `Nat.bitIndices`,
`Nat.centralBinom`, `Mathlib.Data.Nat.Choose.Factorization`): which
`ℕ`-identities are mathlib citations and which `Era`-term constructions
are new.

- [ ] **Step 4: Record the decision and delete the probe**

Write the chosen construction, its lemma outline, and the magnitude
estimate into the decision note; remove the throwaway probe module.
Acceptance: the note names one construction for `eraBSum` and lists its
`Era`-term obligations and `eval` lemma, sufficient to drive a follow-on
plan.

- [ ] **Step 5: Commit**

```bash
markdownlint-cli2 docs/superpowers/notes/<date>-erabsum-construction-decision.md
jj describe -m "doc(era): record the eraBSum construction-choice decision"
```

---

## Deferred to the follow-on plan (after Task 4)

Planned in detail once Task 4 fixes the construction:

- **`eraBSum`** (spec M3): the bounded-sum term former; its `eval`
  lemma reproduces `natBSum` over the body (spec § 4 signature block).
- **`eraBProd`** (spec M4): via the `2^x` elimination (Marchenkov 2003,
  Statement 2.13).
- **`era_complete`** (spec M5): structural induction on `ERMor1` using
  the routine cases plus the two `eval` lemmas; assembled in the bridge
  module.
- **K-sim-2 corollary** (spec § 8): compose `Era ≃ E³` with `erKSimEquiv`
  (`GebLean/LawvereERKSim/Equivalence.lean`).

---

## Self-review

- **Spec coverage.** Phase 1 implements the spec's soundness direction
  (§ 7) and the bridge module (§ 3 module placement); Task 4 implements
  the spec's M2/M3 assessment gate (§ 5 Library reuse, § 13). The
  completeness direction (§ 3–§ 6) and the corollary (§ 8) are
  explicitly deferred with their spec references — a staging decision,
  not a gap, justified by the construction gate.
- **Placeholders.** No "TBD"/"add error handling" steps. Where proof
  tactics are left to interactive execution, the goal statement and the
  exact lemmas are given (Lean proofs are not reliably writable ahead of
  the build).
- **Type consistency.** `eraOpToER : (b : EraB) → ERMor1 (eraAr b)` and
  `erOfETm : ETm n → ERMor1 n` feed `era_sound_er`; `eraOpToER_interp`
  and `erOfETm_interp` carry the matching `eval` agreements. Names are
  used identically across tasks.
- **Verification.** Every implementation task ends with `lake build`,
  `lake lint`, and `scripts/check-axioms.sh`, and a sorry-free commit.
