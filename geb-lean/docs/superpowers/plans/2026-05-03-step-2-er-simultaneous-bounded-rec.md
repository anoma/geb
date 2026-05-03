# Step 2 — ER-side multi-output bounded simultaneous recursion — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Land `ERMor1.simultaneousBoundedRec` as a Lean
named composite realizing Tourlakis 2018 §0.1.0.35
(closure of E^{n+1} under simultaneous bounded recursion),
plus its conditional correctness theorem against the
abstract `Nat.simRecVec` semantic function and a
per-component PolyBound builder. Three new modules:
`SimRec.lean` (Nat-level), `ERPackedBound.lean` (ER-level
packed-state bound), `ERSimultaneousBoundedRec.lean`
(consumer-facing API).

**Architecture:** Pack the `(k+1)`-component state into a
single Nat via step 1's `Nat.tuplePack`; apply existing
single-output `ERMor1.boundedRec` with a packed-state bound
`tuplePackCoef k * (componentBound + 1)^{2^k}`; unpack
component-wise via `Nat.tupleAt`. Correctness conditional on
`componentBound`-dominance (against `Nat.simRecVec`) plus
counter-monotonicity (matching
`boundedRec_eq_natRec_of_bounded`'s hypothesis shape).

**Tech Stack:** Lean 4 + mathlib4. Build via `lake build`,
test via `lake test`. Existing infrastructure consumed:
step 1's `Nat.tuplePack`, `Nat.tupleAt`, `Nat.tuplePack_le`,
`Nat.tupleAt_le`, `Nat.tupleAt_tuplePack`,
`ERMor1.tuplePack`, `ERMor1.tupleAt`,
`ERMor1.interp_tuplePack`, `ERMor1.interp_tupleAt`,
`ERMor1.PolyBound.ofTuplePack`, `ERMor1.PolyBound.ofTupleAt`.
Existing arithmetic primitives: `ERMor1.boundedRec`
(`ERArith.lean:1782`), `boundedRec_eq_natRec_of_bounded`
(`ERArith.lean:2193`), `interp_boundedRec_le_bound`
(`ERArith.lean:1804`), `ERMor1.expER`, `ERMor1.mulN`,
`ERMor1.addN`, `ERMor1.natN`.

**Spec:**
`docs/superpowers/specs/2026-05-03-step-2-er-simultaneous-bounded-rec-design.md`
(commit `93b65e0a`, signed off after brainstorming).

**Master design:**
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`
§3.2 (interface, packed-state bound, tower-height
arithmetic), §15.13 (punch-list claim).

---

## File structure

**Created (implementation):**

- `GebLean/Utilities/SimRec.lean` — `Nat.simRecVec`,
  `Nat.simRec`, recurrence simp lemmas, dominance helper.
  Imports `Mathlib.Data.Fin.Tuple.Basic` only.
- `GebLean/Utilities/ERPackedBound.lean` —
  `ERMor1.tuplePackedBound`, interp lemma, PolyBound
  builder, `tuplePackedBound_dominates` helper. Imports
  `GebLean.Utilities.Tupling`,
  `GebLean.Utilities.ERArith`,
  `GebLean.LawvereERPolynomialBound`.
- `GebLean/Utilities/ERSimultaneousBoundedRec.lean` —
  definitional helpers, `simultaneousBoundedRec`, named
  intermediate lemmas, `_interp_correct` theorem,
  `ofSimultaneousBoundedRec` PolyBound builder. Imports
  `GebLean.Utilities.SimRec`,
  `GebLean.Utilities.ERTupling`,
  `GebLean.Utilities.ERPackedBound`.

**Created (tests):**

- `GebLeanTests/Utilities/SimRec.lean`.
- `GebLeanTests/Utilities/ERPackedBound.lean`.
- `GebLeanTests/Utilities/ERSimultaneousBoundedRec.lean`.

**Modified:**

- `GebLean.lean` — add public exports of three new
  utility modules.
- `GebLeanTests.lean` — add imports of three new test
  modules.

---

## Style and discipline reminders (from step 1's lessons)

Each task's code must follow CLAUDE.md:

- Lines ≤ 80 characters.
- Spaces around binary operators in source: write
  `Fin (k + 1)` not `Fin (k+1)`, `(2 ^ k)` not `(2^k)`.
- Every implemented function/definition/theorem carries a
  literature reference in its docstring (Tourlakis 2018
  §0.1.0.35 / §0.1.0.7 / §0.1.0.34, p. 14, or master
  design §3.2).
- Use `simp only [...]` not bare `simp [...]`.
- Use `change` not `show` when the goal text differs from
  what Lean has after reduction.
- No `sorry`, `admit`, `Classical`, `noncomputable`,
  `axiom`, or warnings (lakefile sets `warningAsError =
  true`).
- No banned words from CLAUDE.md's list.
- `markdownlint-cli2` clean on any new docs.

### Import-at-skeleton-creation rule

**Add the import to `GebLean.lean` (and the test
counterpart to `GebLeanTests.lean`) the moment you create
the skeleton file**, before adding any code. This is
verified during the skeleton task itself.

### Forced re-elaboration before commit

After each task that touches a `.lean` file, force
re-elaboration to catch latent linter errors masked by
incremental cache:

```bash
rm -f .lake/build/lib/lean/<path-to-module>.olean
lake build <module-name>
```

Inspect output for `error:` lines (do not stop at "Build
completed successfully" — that line is unreliable when the
module was already cached).

### ER-side `.interp` test discipline (Gödel numbering)

Per step 1's lesson: `#guard` on `ERMor1.<X>.interp` for
`X` involving `tuplePack k` / `tupleAt k` / `natPair` /
`natUnpair*` / `boundedRec` / `boundedSearch` / `expER` /
`towerER` is impractical even for tiny inputs. Restrict
ER-side `#guard`s to `k = 0` with tiny inputs; rely on the
universal `_interp_correct` proof for higher arity.

---

## Task 1 — `Nat.simRecVec` and `Nat.simRec` skeleton + def

**Files:**

- Create: `GebLean/Utilities/SimRec.lean`
- Modify: `GebLean.lean` (add import per the skeleton rule)

- [ ] **Step 1.1: Create the module skeleton**

```lean
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Nat-level simultaneous primitive recursion

Vector-valued semantic function for simultaneous primitive
recursion.  Used to state
`simultaneousBoundedRec_interp_correct` per master design
§3.2.  Realizes Tourlakis 2018 §0.1.0.7 (definition of
K^sim hierarchy via simultaneous primitive recursion).

The step input convention matches `ERMor1.boundedRec` in
`Utilities/ERArith.lean:1782-1799`: slot 0 is the
iteration counter, slots 1..k+1 are the previous-iteration
component values, slots k+2..k+1+a are the parameter
context.

See `docs/superpowers/specs/2026-05-03-step-2-er-simultaneous-bounded-rec-design.md`
and master design §3.2 in
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
-/

namespace Nat

end Nat
```

- [ ] **Step 1.2: Register the import in `GebLean.lean` immediately**

Open `GebLean.lean`. Add (in alphabetical order, near the
existing `import GebLean.Utilities.Tupling`):

```lean
import GebLean.Utilities.SimRec
```

- [ ] **Step 1.3: Verify the empty skeleton builds**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/SimRec.olean
lake build GebLean.Utilities.SimRec 2>&1 | tail -3
```

Expected: clean build of the empty skeleton (only the
imports and module docstring).

- [ ] **Step 1.4: Define `Nat.simRecVec`**

Inside `namespace Nat`:

```lean
/-- Vector-valued simultaneous primitive recursion.
Returns the full `(k + 1)`-vector of component values at
iteration `n` with parameter context `x : Fin a → ℕ`.

Step input convention (matching `ERMor1.boundedRec` in
`Utilities/ERArith.lean:1782-1799`): slot 0 is the
iteration counter, slots 1..k+1 are the previous-iteration
component values, slots k+2..k+1+a are the parameter
context.  The step is therefore
`g_all : Fin (k + 1) → (Fin (1 + (k + 1) + a) → ℕ) → ℕ`,
applied as
`g_all j (Fin.cons n (Fin.append prev x))`.

Used to state `simultaneousBoundedRec_interp_correct` per
master design §3.2.  Realizes Tourlakis 2018 §0.1.0.7
(definition of K^sim hierarchy via simultaneous primitive
recursion). -/
def simRecVec (k a : ℕ)
    (h_all : Fin (k + 1) → (Fin a → ℕ) → ℕ)
    (g_all : Fin (k + 1) →
      (Fin (1 + (k + 1) + a) → ℕ) → ℕ) :
    ℕ → (Fin a → ℕ) → (Fin (k + 1) → ℕ)
  | 0,     x => fun j => h_all j x
  | n + 1, x => fun j =>
      g_all j (Fin.cons n
        (Fin.append (simRecVec k a h_all g_all n x) x))
```

- [ ] **Step 1.5: Define `Nat.simRec`**

```lean
/-- Component projection: `simRec` returns the j-th
component value at iteration `n`.  Plain `def` (not
`@[simp]`); promote if downstream proofs frequently
unfold it.  Master design §3.2. -/
def simRec (k a : ℕ)
    (h_all : Fin (k + 1) → (Fin a → ℕ) → ℕ)
    (g_all : Fin (k + 1) →
      (Fin (1 + (k + 1) + a) → ℕ) → ℕ)
    (j : Fin (k + 1)) (n : ℕ) (x : Fin a → ℕ) : ℕ :=
  simRecVec k a h_all g_all n x j
```

- [ ] **Step 1.6: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/SimRec.olean
lake build GebLean.Utilities.SimRec 2>&1 | tail -5
```

Expected: clean build, no warnings.

```bash
lake build 2>&1 | tail -3
lake test 2>&1 | tail -3
```

Both pass.

```bash
git add GebLean/Utilities/SimRec.lean GebLean.lean
git commit -m "Step 2 task 1: Nat.simRecVec and Nat.simRec definitions

Vector-valued simultaneous primitive recursion semantic
function for the ER ↔ K^sim_2 categorical equivalence.
Step input convention matches ERMor1.boundedRec: slot 0 is
the iteration counter, slots 1..k+1 are the previous-
iteration component values, slots k+2..k+1+a are the
parameter context.

Per the import-at-skeleton-creation rule, GebLean.lean's
import is registered as part of this same commit.

Realizes Tourlakis 2018 §0.1.0.7 (definition of K^sim
hierarchy via simultaneous primitive recursion); master
design §3.2."
```

---

## Task 2 — `@[simp]` recurrence lemmas

**Files:**

- Modify: `GebLean/Utilities/SimRec.lean` (append, inside
  the existing `namespace Nat ... end Nat` block)

- [ ] **Step 2.1: Add `simRecVec_zero` and `simRecVec_succ`**

Append within `namespace Nat`:

```lean
@[simp] theorem simRecVec_zero (k a : ℕ)
    (h_all : Fin (k + 1) → (Fin a → ℕ) → ℕ)
    (g_all : Fin (k + 1) →
      (Fin (1 + (k + 1) + a) → ℕ) → ℕ)
    (x : Fin a → ℕ) (j : Fin (k + 1)) :
    simRecVec k a h_all g_all 0 x j = h_all j x := rfl

@[simp] theorem simRecVec_succ (k a : ℕ)
    (h_all : Fin (k + 1) → (Fin a → ℕ) → ℕ)
    (g_all : Fin (k + 1) →
      (Fin (1 + (k + 1) + a) → ℕ) → ℕ)
    (n : ℕ) (x : Fin a → ℕ) (j : Fin (k + 1)) :
    simRecVec k a h_all g_all (n + 1) x j
      = g_all j (Fin.cons n
          (Fin.append (simRecVec k a h_all g_all n x) x))
        := rfl
```

- [ ] **Step 2.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/SimRec.olean
lake build GebLean.Utilities.SimRec 2>&1 | tail -5
```

Expected: clean.

```bash
git add GebLean/Utilities/SimRec.lean
git commit -m "Step 2 task 2: @[simp] recurrence lemmas for Nat.simRecVec

Two simp lemmas (simRecVec_zero, simRecVec_succ) unfolding
the recursive definition.  Master design §3.2."
```

---

## Task 3 — `Nat.simRecVec_le_of_dominates` (dominance helper)

**Files:**

- Modify: `GebLean/Utilities/SimRec.lean` (append)

- [ ] **Step 3.1: Add `simRecVec_le_of_dominates`**

```lean
/-- If each base value is dominated by `componentBound`
at iteration 0, and the step preserves dominance
inductively, then every component value at every
iteration up to `n` is bounded.  Internal helper for
`simultaneousBoundedRec_interp_correct`'s dominance-
hypothesis discharge.  Master design §3.2. -/
theorem simRecVec_le_of_dominates
    (k a : ℕ)
    (h_all : Fin (k + 1) → (Fin a → ℕ) → ℕ)
    (g_all : Fin (k + 1) →
      (Fin (1 + (k + 1) + a) → ℕ) → ℕ)
    (componentBound : ℕ → (Fin a → ℕ) → ℕ)
    (h_base : ∀ j x, h_all j x ≤ componentBound 0 x)
    (h_step : ∀ n x prev j,
       (∀ j', prev j' ≤ componentBound n x) →
       g_all j (Fin.cons n (Fin.append prev x))
         ≤ componentBound (n + 1) x) :
    ∀ (n : ℕ) (x : Fin a → ℕ) (j : Fin (k + 1)),
      simRecVec k a h_all g_all n x j
        ≤ componentBound n x
  | 0,     x, j => by
      simp only [simRecVec_zero]
      exact h_base j x
  | n + 1, x, j => by
      simp only [simRecVec_succ]
      apply h_step n x (simRecVec k a h_all g_all n x) j
      intro j'
      exact simRecVec_le_of_dominates k a h_all g_all
        componentBound h_base h_step n x j'
```

- [ ] **Step 3.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/SimRec.olean
lake build GebLean.Utilities.SimRec 2>&1 | tail -5
```

Expected: clean.

```bash
git add GebLean/Utilities/SimRec.lean
git commit -m "Step 2 task 3: Nat.simRecVec_le_of_dominates dominance helper

Inductive dominance lemma: under h_base + h_step
hypotheses, every simRecVec component value at every
iteration is bounded by componentBound.  Internal helper
for simultaneousBoundedRec_interp_correct's hypothesis
discharge.  Master design §3.2."
```

---

## Task 4 — Nat-side tests in `GebLeanTests/Utilities/SimRec.lean`

**Files:**

- Create: `GebLeanTests/Utilities/SimRec.lean`
- Modify: `GebLeanTests.lean` (add import)

- [ ] **Step 4.1: Create the test module skeleton + register import**

Create `GebLeanTests/Utilities/SimRec.lean`:

```lean
import GebLean.Utilities.SimRec

/-!
# Tests for `Nat.simRecVec`, `Nat.simRec`,
# `Nat.simRecVec_le_of_dominates`.

Nat-level simultaneous primitive-recursion semantic
function for the ER ↔ K^sim_2 categorical equivalence.
See `GebLean.Utilities.SimRec` and master design §3.2
in `docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
-/

open Nat

end
```

(Trailing `end` is a placeholder; remove after adding
tests.)

Add to `GebLeanTests.lean` (alphabetical position among
`GebLeanTests.Utilities.*`):

```lean
import GebLeanTests.Utilities.SimRec
```

Verify skeleton compiles:

```bash
rm -f .lake/build/lib/lean/GebLeanTests/Utilities/SimRec.olean
lake test 2>&1 | tail -3
```

- [ ] **Step 4.2: Add identity-case smoke `#guard`s**

Replace the `end` placeholder. Add:

```lean
-- Identity-case smoke (k = 0, a = 0): 1-component
-- "simrec" reduces to ordinary recursion.  Step input
-- arity = 1 + 1 + 0 = 2: slot 0 = counter, slot 1 =
-- previous singleton component.

-- Constant base, constant step: f(0) = 5, f(n+1) = 7.
#guard simRecVec 0 0 (fun _ _ => 5) (fun _ _ => 7) 0
         (fun _ => 0) ⟨0, by decide⟩ = 5

-- Successor step on the previous value: f(0) = 5,
-- f(n+1) = prev + 1.  Step `fun _ ctx => ctx 1 + 1`
-- consumes slot 1 (the previous value).
#guard simRecVec 0 0 (fun _ _ => 5)
         (fun _ ctx => ctx 1 + 1) 1
         (fun _ => 0) ⟨0, by decide⟩ = 6
```

- [ ] **Step 4.3: Add a non-trivial 2-component smoke (swap example)**

At `k = 1, a = 0`, step input arity is `1 + 2 + 0 = 3`:
slot 0 = counter, slot 1 = previous component 0, slot 2
= previous component 1.  The swap step (component 0
returns slot 2; component 1 returns slot 1) gives
parity-dependent values from bases `(1, 2)`:

```text
iteration 0: (1, 2)
iteration 1: swap → (2, 1)
iteration 2: swap → (1, 2)
iteration 3: swap → (2, 1)
...
iteration 5: (2, 1)  — component 0 at n = 5 is 2.
```

Values stay in `{1, 2}` regardless of `n`.

```lean
-- Non-trivial 2-component swap: f_0(0) = 1, f_1(0) = 2,
-- step swaps the components.  At odd n, component 0 = 2.
example :
    simRecVec 1 0
      (fun j _ => match j with
        | ⟨0, _⟩ => 1
        | ⟨1, _⟩ => 2)
      (fun j ctx => match j with
        | ⟨0, _⟩ => ctx ⟨2, by decide⟩
        | ⟨1, _⟩ => ctx ⟨1, by decide⟩)
      5 (fun _ => 0) ⟨0, by decide⟩ = 2 := by decide
```

- [ ] **Step 4.4: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLeanTests/Utilities/SimRec.olean
lake test 2>&1 | tail -5
```

Expected: clean — all `#guard`s and `example`s pass.

```bash
git add GebLeanTests/Utilities/SimRec.lean GebLeanTests.lean
git commit -m "Step 2 task 4: Nat-side tests for SimRec

Identity-case #guards (k = 0): simRecVec degenerates to
ordinary recursion.  Non-trivial 2-component swap example
verifying the step input convention (slot 0 = counter,
slots 1..k+1 = prev-vector, slots k+2..k+1+a = params) and
the parity behavior of the swap step.

Per the import-at-skeleton-creation rule, the test
import is registered in GebLeanTests.lean alongside the
test module's creation.

Spec §6.1 transcribed."
```

---

## Task 5 — `ERMor1.tuplePackedBound` skeleton + def

**Files:**

- Create: `GebLean/Utilities/ERPackedBound.lean`
- Modify: `GebLean.lean` (add import)

- [ ] **Step 5.1: Create the module skeleton**

```lean
import GebLean.Utilities.Tupling
import GebLean.Utilities.ERArith
import GebLean.LawvereERPolynomialBound

/-!
# ER-side packed-state value bound for simultaneous bounded recursion

Named composite `ERMor1.tuplePackedBound k componentBound`
expressing the ER-level packed-state bound
`tuplePackCoef k * (componentBound + 1)^(2^k)` per master
design §3.2.  Used by `ERMor1.simultaneousBoundedRec` (in
`GebLean.Utilities.ERSimultaneousBoundedRec`) as the
single-output `ERMor1.boundedRec` bound when packing a
`(k+1)`-tuple of bounded component values via
`Nat.tuplePack`.  Reusable by step 4 majorization
arithmetic.

Bottom-up construction from atomic ER generators
(`ERMor1.natN`, `ERMor1.addN`, `ERMor1.expER`,
`ERMor1.mulN`) per CLAUDE.md "bottom-up named-composite
discipline".

See `docs/superpowers/specs/2026-05-03-step-2-er-simultaneous-bounded-rec-design.md`
and master design §3.2 in
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
-/

namespace GebLean
namespace ERMor1

end ERMor1
end GebLean
```

- [ ] **Step 5.2: Register the import in `GebLean.lean`**

Add `import GebLean.Utilities.ERPackedBound` (alphabetical
position).

- [ ] **Step 5.3: Verify the empty skeleton builds**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERPackedBound.olean
lake build GebLean.Utilities.ERPackedBound 2>&1 | tail -3
```

Expected: clean.

- [ ] **Step 5.4: Define `ERMor1.tuplePackedBound`**

Inside `namespace GebLean / namespace ERMor1`:

```lean
/-- ER named composite for the packed-state value bound:
`tuplePackCoef k * (componentBound + 1)^(2^k)`.  Used by
`ERMor1.simultaneousBoundedRec` (master design §3.2) as
the single-output `ERMor1.boundedRec` bound when packing
a `(k + 1)`-tuple of bounded component values via
`Nat.tuplePack`.

Built bottom-up from `ERMor1.natN`, `ERMor1.addN`,
`ERMor1.expER`, `ERMor1.mulN` per CLAUDE.md "bottom-up
named-composite discipline".  Master design §3.2;
underlying bound from step 1's `Nat.tuplePack_le` (citing
Tourlakis 2018 §0.1.0.34, p. 14). -/
def tuplePackedBound (k : ℕ) {a : ℕ}
    (componentBound : ERMor1 a) : ERMor1 a :=
  ERMor1.comp ERMor1.mulN
    ![ ERMor1.natN a (Nat.tuplePackCoef k)
     , ERMor1.comp ERMor1.expER
         ![ ERMor1.comp ERMor1.addN
              ![ componentBound
               , ERMor1.natN a 1 ]
          , ERMor1.natN a (2 ^ k) ] ]
```

- [ ] **Step 5.5: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERPackedBound.olean
lake build GebLean.Utilities.ERPackedBound 2>&1 | tail -5
```

Expected: clean.

```bash
git add GebLean/Utilities/ERPackedBound.lean GebLean.lean
git commit -m "Step 2 task 5: ERMor1.tuplePackedBound skeleton + def

ER named composite for the packed-state value bound
'tuplePackCoef k * (componentBound + 1)^(2^k)' per master
design §3.2.  Bottom-up construction from natN, addN,
expER, mulN.

Per the import-at-skeleton-creation rule, GebLean.lean's
import is registered as part of this same commit.

Master design §3.2; underlying bound from step 1's
Nat.tuplePack_le (Tourlakis 2018 §0.1.0.34, p. 14)."
```

---

## Task 6 — `@[simp] ERMor1.interp_tuplePackedBound`

**Files:**

- Modify: `GebLean/Utilities/ERPackedBound.lean` (append)

- [ ] **Step 6.1: Add the interp lemma**

```lean
@[simp] theorem interp_tuplePackedBound (k : ℕ) {a : ℕ}
    (componentBound : ERMor1 a) (ctx : Fin a → ℕ) :
    (ERMor1.tuplePackedBound k componentBound).interp ctx
      = Nat.tuplePackCoef k *
          (componentBound.interp ctx + 1) ^ (2 ^ k) := by
  simp only [ERMor1.tuplePackedBound, ERMor1.interp_comp,
    ERMor1.interp_mulN, ERMor1.interp_expER,
    ERMor1.interp_addN, ERMor1.interp_natN,
    Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons]
```

(If the simp set above doesn't close it cleanly, the
implementer may need to add `Matrix.head_fin_const` or
case-split via `match` on the `Fin 2` indices, similar to
step 1 Task 8's `hctx` bridges. Report any deviation.)

- [ ] **Step 6.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERPackedBound.olean
lake build GebLean.Utilities.ERPackedBound 2>&1 | tail -5
```

Expected: clean.

```bash
git add GebLean/Utilities/ERPackedBound.lean
git commit -m "Step 2 task 6: @[simp] interp_tuplePackedBound lemma

Reduces (tuplePackedBound k cb).interp ctx to
'Nat.tuplePackCoef k * (cb.interp ctx + 1) ^ (2 ^ k)'.
Master design §3.2."
```

---

## Task 7 — `ERMor1.tuplePackedBound_dominates`

**Files:**

- Modify: `GebLean/Utilities/ERPackedBound.lean` (append)

- [ ] **Step 7.1: Add the dominance helper**

```lean
/-- If each component of a `(k + 1)`-vector `v` is
bounded by `componentBound.interp ctx`, then
`Nat.tuplePack k v` is bounded by
`(tuplePackedBound k componentBound).interp ctx`.  This
is the per-iteration bound feeding into
`boundedRec_eq_natRec_of_bounded`'s dominance hypothesis
inside `simultaneousBoundedRec_interp_correct`.  Master
design §3.2. -/
theorem tuplePackedBound_dominates
    (k : ℕ) {a : ℕ} (componentBound : ERMor1 a)
    (v : Fin (k + 1) → ℕ) (ctx : Fin a → ℕ)
    (h_components :
        ∀ j, v j ≤ componentBound.interp ctx) :
    Nat.tuplePack k v
      ≤ (ERMor1.tuplePackedBound k componentBound).interp
          ctx := by
  rw [ERMor1.interp_tuplePackedBound]
  have h_pack :
      Nat.tuplePack k v
        ≤ Nat.tuplePackCoef k *
            ((Finset.univ : Finset (Fin (k + 1))).sup v + 1)
              ^ (2 ^ k) :=
    Nat.tuplePack_le k v
  have h_sup :
      (Finset.univ : Finset (Fin (k + 1))).sup v
        ≤ componentBound.interp ctx := by
    apply Finset.sup_le
    intro j _
    exact h_components j
  have h_pow_le :
      ((Finset.univ : Finset (Fin (k + 1))).sup v + 1)
            ^ (2 ^ k)
        ≤ (componentBound.interp ctx + 1) ^ (2 ^ k) := by
    apply Nat.pow_le_pow_left
    omega
  calc Nat.tuplePack k v
      ≤ Nat.tuplePackCoef k *
          ((Finset.univ : Finset (Fin (k + 1))).sup v + 1)
            ^ (2 ^ k) := h_pack
    _ ≤ Nat.tuplePackCoef k *
          (componentBound.interp ctx + 1) ^ (2 ^ k) := by
        apply Nat.mul_le_mul_left
        exact h_pow_le
```

- [ ] **Step 7.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERPackedBound.olean
lake build GebLean.Utilities.ERPackedBound 2>&1 | tail -5
```

Expected: clean.

```bash
git add GebLean/Utilities/ERPackedBound.lean
git commit -m "Step 2 task 7: ERMor1.tuplePackedBound_dominates helper

Per-iteration bound: if each component of v is bounded
by componentBound.interp ctx, then Nat.tuplePack k v is
bounded by (tuplePackedBound k componentBound).interp ctx.
Feeds into simultaneousBoundedRec_interp_correct's
dominance-hypothesis discharge.  Master design §3.2."
```

---

## Task 8 — `ERMor1.PolyBound.ofTuplePackedBound`

**Files:**

- Modify: `GebLean/Utilities/ERPackedBound.lean` (append,
  inside a new `namespace ERMor1.PolyBound` block)

- [ ] **Step 8.1: Add the PolyBound builder**

```lean
namespace PolyBound

/-- PolyBound for `tuplePackedBound k componentBound`.
Given `pb : PolyBound componentBound`, produces:

- `degree = pb.degree * 2^k`
- `coefficient = tuplePackCoef k *
                   (pb.coefficient + pb.constant + 1)^(2^k)`
- `constant = 0`

Derivation: substituting `pb`'s formula
`componentBound.interp ctx ≤
  pb.coefficient * X^pb.degree + pb.constant`
(where `X = maxCtx ctx + 1`) into
`tuplePackCoef k * (componentBound.interp ctx + 1)^(2^k)`
and applying
`(A * X^d + B + 1) ≤ (A + B + 1) * X^d` for `X ≥ 1`,
we get the formula above.  Master design §3.2; §15.13
punch-list. -/
def ofTuplePackedBound (k : ℕ) {a : ℕ}
    {componentBound : ERMor1 a}
    (pb : PolyBound componentBound) :
    PolyBound (ERMor1.tuplePackedBound k componentBound)
    where
  degree := pb.degree * 2 ^ k
  coefficient := Nat.tuplePackCoef k *
    (pb.coefficient + pb.constant + 1) ^ (2 ^ k)
  constant := 0
  bounds := fun ctx => by
    rw [ERMor1.interp_tuplePackedBound]
    set M := (Finset.univ : Finset (Fin a)).sup ctx with hM
    have h_cb := pb.bounds ctx
    set X := M + 1 with hX
    have hX_pos : 1 ≤ X := by omega
    -- componentBound.interp ctx ≤ pb.coefficient * X^pb.degree + pb.constant
    have h_cb_step :
        componentBound.interp ctx + 1
          ≤ (pb.coefficient + pb.constant + 1)
              * X ^ pb.degree := by
      have h_const_le :
          pb.constant ≤ pb.constant * X ^ pb.degree := by
        have hpow_pos :
            1 ≤ X ^ pb.degree := Nat.one_le_pow _ _ hX_pos
        exact Nat.le_mul_of_pos_right _ hpow_pos
      have h_one_le :
          1 ≤ X ^ pb.degree :=
        Nat.one_le_pow _ _ hX_pos
      calc componentBound.interp ctx + 1
          ≤ pb.coefficient * X ^ pb.degree + pb.constant + 1 := by
            have := h_cb; omega
        _ ≤ pb.coefficient * X ^ pb.degree
              + pb.constant * X ^ pb.degree
              + X ^ pb.degree := by
            have := h_const_le
            have := h_one_le
            omega
        _ = (pb.coefficient + pb.constant + 1)
              * X ^ pb.degree := by ring
    -- Raise both sides to the (2^k)-th power
    have h_pow :
        (componentBound.interp ctx + 1) ^ (2 ^ k)
          ≤ ((pb.coefficient + pb.constant + 1)
                * X ^ pb.degree) ^ (2 ^ k) :=
      Nat.pow_le_pow_left h_cb_step (2 ^ k)
    have h_expand :
        ((pb.coefficient + pb.constant + 1)
              * X ^ pb.degree) ^ (2 ^ k)
          = (pb.coefficient + pb.constant + 1) ^ (2 ^ k)
              * X ^ (pb.degree * 2 ^ k) := by
      rw [Nat.mul_pow, ← pow_mul]
    -- Multiply by tuplePackCoef k and absorb +0
    calc Nat.tuplePackCoef k
          * (componentBound.interp ctx + 1) ^ (2 ^ k)
        ≤ Nat.tuplePackCoef k
            * ((pb.coefficient + pb.constant + 1)
                * X ^ pb.degree) ^ (2 ^ k) := by
          exact Nat.mul_le_mul_left _ h_pow
      _ = Nat.tuplePackCoef k
            * ((pb.coefficient + pb.constant + 1) ^ (2 ^ k)
                * X ^ (pb.degree * 2 ^ k)) := by
          rw [h_expand]
      _ = Nat.tuplePackCoef k
            * (pb.coefficient + pb.constant + 1) ^ (2 ^ k)
            * X ^ (pb.degree * 2 ^ k) := by ring
      _ = Nat.tuplePackCoef k
            * (pb.coefficient + pb.constant + 1) ^ (2 ^ k)
            * (M + 1) ^ (pb.degree * 2 ^ k) := by
          rw [hX]
      _ ≤ Nat.tuplePackCoef k
            * (pb.coefficient + pb.constant + 1) ^ (2 ^ k)
            * (M + 1) ^ (pb.degree * 2 ^ k) + 0 := by omega

end PolyBound
```

(The proof is long but mechanical. If a step doesn't go
through cleanly, the implementer may insert intermediate
`have` blocks or use `linarith`/`omega` with explicit
hypotheses. Report any structural changes.)

- [ ] **Step 8.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERPackedBound.olean
lake build GebLean.Utilities.ERPackedBound 2>&1 | tail -5
```

Expected: clean.

```bash
git add GebLean/Utilities/ERPackedBound.lean
git commit -m "Step 2 task 8: ERMor1.PolyBound.ofTuplePackedBound

PolyBound builder for tuplePackedBound k componentBound:
- degree = pb.degree * 2^k
- coefficient = tuplePackCoef k * (pb.coefficient + pb.constant + 1)^(2^k)
- constant = 0

Derived by substituting pb's formula into
'tuplePackCoef k * (cb + 1)^(2^k)' and applying
'(A * X^d + B + 1) ≤ (A + B + 1) * X^d' for X ≥ 1.

Master design §3.2; §15.13 punch-list claim
('no 3^E-style coefficient leaks out') satisfied: the
coefficient depends only on (k, pb), not on the source
K^sim term's structure."
```

---

## Task 9 — `ERPackedBound` tests

**Files:**

- Create: `GebLeanTests/Utilities/ERPackedBound.lean`
- Modify: `GebLeanTests.lean` (add import)

- [ ] **Step 9.1: Create test module skeleton + register import**

Create `GebLeanTests/Utilities/ERPackedBound.lean`:

```lean
import GebLean.Utilities.ERPackedBound

/-!
# Tests for `ERMor1.tuplePackedBound`,
# `ERMor1.PolyBound.ofTuplePackedBound`.

ER-side packed-state value bound for the ER ↔ K^sim_2
categorical equivalence.  See
`GebLean.Utilities.ERPackedBound` and master design §3.2.

Per the test discipline from
`GebLeanTests/Utilities/ERTupling.lean` (Gödel-numbering
kernel-reduction is impractical), this file restricts
runtime checks to PolyBound shape verification (struct
field access only).
-/

open GebLean

end
```

Add import to `GebLeanTests.lean`:

```lean
import GebLeanTests.Utilities.ERPackedBound
```

- [ ] **Step 9.2: Add PolyBound shape examples**

Replace the `end` placeholder. Add:

```lean
-- PolyBound shape at k = 0: degree 1 * 2^0 = 1,
-- coefficient = tuplePackCoef 0 * (1 + 0 + 1)^1 = 1 * 2 = 2.
-- (Using ERMor1.PolyBound.ofZero at arity 0 as a trivial
-- componentBound: degree = 0, coefficient = 0, constant = 0.)
example :
    (ERMor1.PolyBound.ofTuplePackedBound 0
       (ERMor1.PolyBound.ofZero
          (n := 0))).degree = 0 := rfl

example :
    (ERMor1.PolyBound.ofTuplePackedBound 1
       (ERMor1.PolyBound.ofZero
          (n := 0))).degree = 0 := rfl

-- tuplePackCoef k for small k (sanity).
example :
    (ERMor1.PolyBound.ofTuplePackedBound 1
       (ERMor1.PolyBound.ofZero
          (n := 0))).coefficient
      = Nat.tuplePackCoef 1 * 1 ^ (2 ^ 1) := rfl

example :
    (ERMor1.PolyBound.ofTuplePackedBound 1
       (ERMor1.PolyBound.ofZero
          (n := 0))).constant = 0 := rfl
```

`ERMor1.PolyBound.ofZero` produces a PolyBound with
`degree = 0`, `coefficient = 0`, `constant = 0`. The
derived `ofTuplePackedBound` therefore has
`degree = pb.degree * 2^k = 0`, `coefficient =
tuplePackCoef k * (0 + 0 + 1)^(2^k) = tuplePackCoef k`,
`constant = 0`. Adjust the example values to match.

- [ ] **Step 9.3: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLeanTests/Utilities/ERPackedBound.olean
lake test 2>&1 | tail -5
```

Expected: clean.

```bash
git add GebLeanTests/Utilities/ERPackedBound.lean GebLeanTests.lean
git commit -m "Step 2 task 9: ERPackedBound tests

PolyBound shape verification at small k (struct field
access only — no .interp evaluation per the Gödel-
numbering test discipline from step 1).  Spec §6.2
transcribed."
```

---

## Task 10 — `ERSimultaneousBoundedRec` skeleton + definitional helpers

**Files:**

- Create: `GebLean/Utilities/ERSimultaneousBoundedRec.lean`
- Modify: `GebLean.lean` (add import)

- [ ] **Step 10.1: Create the module skeleton**

```lean
import GebLean.Utilities.SimRec
import GebLean.Utilities.ERTupling
import GebLean.Utilities.ERPackedBound

/-!
# ER-side multi-output bounded simultaneous recursion

Realizes Tourlakis 2018 §0.1.0.35 (closure of E^{n+1}
under simultaneous bounded recursion).  Master design
§3.2.

Packs the `(k + 1)`-component state into a single
natural via `Nat.tuplePack` (step 1), applies single-
output `ERMor1.boundedRec` with packed-state bound
`ERMor1.tuplePackedBound k componentBound` (this step's
ERPackedBound module), and unpacks component-wise via
`Nat.tupleAt` (step 1).  Bottom-up named composite per
CLAUDE.md "bottom-up named-composite discipline".

Step input convention matches `ERMor1.boundedRec`: slot
0 is the iteration counter, slots 1..k+1 are the
previous-iteration component values, slots k+2..k+1+a
are the parameter context.

See `docs/superpowers/specs/2026-05-03-step-2-er-simultaneous-bounded-rec-design.md`
and master design §3.2 in
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
-/

namespace GebLean
namespace ERMor1

end ERMor1
end GebLean
```

- [ ] **Step 10.2: Register import in `GebLean.lean`**

Add `import GebLean.Utilities.ERSimultaneousBoundedRec`
(alphabetical position).

- [ ] **Step 10.3: Verify the empty skeleton builds**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERSimultaneousBoundedRec.olean
lake build GebLean.Utilities.ERSimultaneousBoundedRec 2>&1 | tail -3
```

Expected: clean.

- [ ] **Step 10.4: Define `ERMor1.packedBase`**

Inside the namespaces:

```lean
/-- Initial packed state for `simultaneousBoundedRec`:
applies the `(k + 1)` bases and packs the resulting
vector via `Nat.tuplePack`.  Master design §3.2 step 3. -/
def packedBase (k a : ℕ)
    (h : Fin (k + 1) → ERMor1 a) : ERMor1 a :=
  ERMor1.comp (ERMor1.tuplePack k) h
```

- [ ] **Step 10.5: Define `ERMor1.packedStepCtx`**

```lean
/-- Slot-routing for `packedStep`'s input context: takes
a `Fin (1 + (k + 1) + a)` index and returns the
`ERMor1 (1 + 1 + a)` selecting the appropriate slot.
- Slot 0 → counter (proj 0).
- Slots 1..k+1 → tupleAt extraction from the packed
  prev state (proj 1).
- Slots k+2..k+1+a → params (proj 2..k+2+a).
Master design §3.2. -/
def packedStepCtx (k a : ℕ) :
    Fin (1 + (k + 1) + a) → ERMor1 (1 + 1 + a)
  | ⟨0, _⟩ => ERMor1.proj 0
  | ⟨s + 1, h_in⟩ =>
      if h_prev : s < k + 1 then
        ERMor1.comp (ERMor1.tupleAt k ⟨s, h_prev⟩)
          ![ERMor1.proj 1]
      else
        ERMor1.proj
          ⟨s - k, by
            have hs_ge : s ≥ k + 1 :=
              Nat.le_of_not_lt h_prev
            have h_in' : s + 1 < 1 + (k + 1) + a :=
              h_in
            -- s + 1 < 1 + k + 1 + a means s < k + 1 + a;
            -- since s ≥ k + 1, s - k ≥ 1, and s - k <
            -- a + 2.
            omega⟩
```

(The `omega` at the bottom may need adjustment if the
exact arithmetic doesn't go through. The `Fin` index
`⟨s - k, _⟩` needs `s - k < 1 + 1 + a`, given
`s + 1 < 1 + (k + 1) + a` and `s ≥ k + 1`.)

- [ ] **Step 10.6: Define `ERMor1.packedStep`**

```lean
/-- Packed step function: takes the packed previous
state and produces the packed next state.  Each
component step `g j` is evaluated on the unpacked
context (counter + previous-component vector + params),
results are repacked via `Nat.tuplePack`.  Master design
§3.2 step 1. -/
def packedStep (k a : ℕ)
    (g : Fin (k + 1) → ERMor1 (1 + (k + 1) + a)) :
    ERMor1 (1 + 1 + a) :=
  ERMor1.comp (ERMor1.tuplePack k)
    (fun j : Fin (k + 1) =>
      ERMor1.comp (g j) (ERMor1.packedStepCtx k a))
```

- [ ] **Step 10.7: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERSimultaneousBoundedRec.olean
lake build GebLean.Utilities.ERSimultaneousBoundedRec 2>&1 | tail -5
```

Expected: clean.

```bash
git add GebLean/Utilities/ERSimultaneousBoundedRec.lean GebLean.lean
git commit -m "Step 2 task 10: ERSimultaneousBoundedRec skeleton + definitional helpers

Three named definitional helpers:
- packedBase: comp tuplePack h.
- packedStepCtx: slot routing for packed step's input
  context, decomposing Fin (1 + (k + 1) + a) into
  (counter, prev_vector, params).
- packedStep: comp tuplePack (g j ∘ packedStepCtx) for
  each component j.

Per the import-at-skeleton-creation rule, GebLean.lean's
import is registered as part of this same commit.

Master design §3.2."
```

---

## Task 11 — `ERMor1.simultaneousBoundedRec` def

**Files:**

- Modify: `GebLean/Utilities/ERSimultaneousBoundedRec.lean`
  (append)

- [ ] **Step 11.1: Add the main def**

```lean
/-- Multi-output bounded simultaneous recursion in ER.
Realizes Tourlakis 2018 §0.1.0.35 (closure of E^{n+1}
under simultaneous bounded recursion).  Master design
§3.2.

The implementation packs the `(k + 1)`-component state
into a single natural via `Nat.tuplePack`, applies
single-output `ERMor1.boundedRec` with a packed-state
bound derived via `ERMor1.tuplePackedBound`, then
unpacks the result component-wise via `Nat.tupleAt`.
Bottom-up named composite per CLAUDE.md "bottom-up
named-composite discipline".  -/
def simultaneousBoundedRec (k a : ℕ)
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (1 + (k + 1) + a))
    (componentBound : ERMor1 (1 + a)) :
    ERMorN (1 + a) (k + 1) :=
  let packedRec : ERMor1 (1 + a) :=
    ERMor1.boundedRec
      (ERMor1.packedBase k a h)
      (ERMor1.packedStep k a g)
      (ERMor1.tuplePackedBound k componentBound)
  fun i : Fin (k + 1) =>
    ERMor1.comp (ERMor1.tupleAt k i) ![packedRec]
```

- [ ] **Step 11.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERSimultaneousBoundedRec.olean
lake build GebLean.Utilities.ERSimultaneousBoundedRec 2>&1 | tail -5
```

Expected: clean.

```bash
git add GebLean/Utilities/ERSimultaneousBoundedRec.lean
git commit -m "Step 2 task 11: ERMor1.simultaneousBoundedRec def

Multi-output bounded simultaneous recursion: packs (k+1)
components via tuplePack, applies boundedRec with
tuplePackedBound, unpacks component-wise via tupleAt.

Realizes Tourlakis 2018 §0.1.0.35; master design §3.2."
```

---

## Task 12 — Named intermediate lemmas (1/2): base case

**Files:**

- Modify: `GebLean/Utilities/ERSimultaneousBoundedRec.lean`
  (append)

- [ ] **Step 12.1: Add `packedBase_interp_eq_tuplePack_simRecVec_zero`**

```lean
/-- Base case: at iteration 0, the packed initial state
equals `Nat.tuplePack k` applied to the bases.  Master
design §3.2. -/
theorem packedBase_interp_eq_tuplePack_simRecVec_zero
    (k a : ℕ) (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (1 + (k + 1) + a))
    (x : Fin a → ℕ) :
    (ERMor1.packedBase k a h).interp x
      = Nat.tuplePack k
          (Nat.simRecVec k a (fun j' => (h j').interp)
            (fun j' => (g j').interp) 0 x) := by
  simp only [ERMor1.packedBase, ERMor1.interp_comp,
    ERMor1.interp_tuplePack, Nat.simRecVec_zero]
```

(If the simp set doesn't reduce cleanly, the implementer
may add a `funext` or `change` step; report deviation.)

- [ ] **Step 12.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERSimultaneousBoundedRec.olean
lake build GebLean.Utilities.ERSimultaneousBoundedRec 2>&1 | tail -5
```

Expected: clean.

```bash
git add GebLean/Utilities/ERSimultaneousBoundedRec.lean
git commit -m "Step 2 task 12: packedBase_interp_eq_tuplePack_simRecVec_zero

Base case of the iteration-induction in
simultaneousBoundedRec_interp_correct: at n = 0, the
packed initial state equals Nat.tuplePack k applied to
the bases.  Master design §3.2."
```

---

## Task 13 — Named intermediate lemmas (2/2): step case + main intermediate

**Files:**

- Modify: `GebLean/Utilities/ERSimultaneousBoundedRec.lean`
  (append)

- [ ] **Step 13.1: Add helper for `packedStepCtx`'s interp**

A small helper that the step-case proof will consume —
proving how `packedStepCtx`'s interp maps slots of the
step's input context to the inner ER computation:

```lean
/-- Interp of `packedStepCtx` at each slot of the
`Fin (1 + (k + 1) + a)`-context.  Slot 0 routes to the
counter (slot 0 of the inner 1+1+a context); slots 1..k+1
route to `Nat.tupleAt k` extraction from the packed prev
state (slot 1 of inner context); slots k+2..k+1+a route
to the params (slots 2..1+a of inner context). -/
theorem interp_packedStepCtx (k a : ℕ)
    (n prev_packed : ℕ) (x : Fin a → ℕ)
    (i : Fin (1 + (k + 1) + a)) :
    (ERMor1.packedStepCtx k a i).interp
        (Fin.cons n (Fin.cons prev_packed x))
      = (Fin.cons n
          (Fin.append
            (Nat.tupleAt k prev_packed) x)) i := by
  -- Case-split on `i.val`: 0, or 1..k+1, or k+2..k+1+a.
  rcases i with ⟨v, h_v⟩
  match v, h_v with
  | 0, _ => simp [ERMor1.packedStepCtx, ERMor1.interp_proj]
  | s + 1, h_in =>
      by_cases h_prev : s < k + 1
      · simp [ERMor1.packedStepCtx, h_prev,
          ERMor1.interp_comp, ERMor1.interp_tupleAt,
          ERMor1.interp_proj, Fin.cons, Fin.append]
        -- The slot s+1 in (Fin.cons n (Fin.append ... x))
        -- corresponds to (Fin.append ... x) at index s,
        -- which is Nat.tupleAt k prev_packed s for s < k+1.
        sorry  -- placeholder; implementer fills in
      · simp [ERMor1.packedStepCtx, h_prev,
          ERMor1.interp_proj, Fin.cons, Fin.append]
        sorry  -- placeholder; implementer fills in
```

(The `sorry`s are placeholders. The implementer must fill
them in by working out the `Fin.cons`/`Fin.append`
arithmetic. If the proof gets stuck, report `BLOCKED`
with the goal state. CLAUDE.md forbids `sorry` in
commits; this lemma is allowed to fail and the implementer
should iterate until clean before committing. The
structure of the proof is: distinguish the three index
ranges and verify each routes correctly.)

- [ ] **Step 13.2: Add `packedStep_interp_eq_tuplePack_step`**

```lean
/-- Step case: applying `packedStep` to a packed state
`prev_packed` (which equals
`Nat.tuplePack k (simRecVec ... n x)`) yields
`Nat.tuplePack k (simRecVec ... (n + 1) x)`.  Master
design §3.2. -/
theorem packedStep_interp_eq_tuplePack_step
    (k a : ℕ)
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (1 + (k + 1) + a))
    (n : ℕ) (x : Fin a → ℕ) :
    let prev_packed :=
      Nat.tuplePack k
        (Nat.simRecVec k a (fun j' => (h j').interp)
          (fun j' => (g j').interp) n x)
    (ERMor1.packedStep k a g).interp
        (Fin.cons n (Fin.cons prev_packed x))
      = Nat.tuplePack k
          (Nat.simRecVec k a (fun j' => (h j').interp)
            (fun j' => (g j').interp) (n + 1) x) := by
  intro prev_packed
  simp only [ERMor1.packedStep, ERMor1.interp_comp,
    ERMor1.interp_tuplePack]
  congr 1
  funext j
  -- Reduce the j-th component:
  -- (g j).interp (packedStepCtx k a · ).interp ctx
  -- = (g j).interp (Fin.cons n (Fin.append (tupleAt k prev_packed) x))
  -- = (g j).interp (Fin.cons n (Fin.append (simRecVec ... n x) x))
  -- (using Nat.tupleAt_tuplePack)
  -- = simRecVec ... (n + 1) x j  (by simRecVec_succ)
  rw [ERMor1.interp_comp]
  congr 1
  funext i
  rw [ERMor1.interp_packedStepCtx]
  -- Now reduce tupleAt of tuplePack = id:
  show (Fin.cons n
        (Fin.append (Nat.tupleAt k prev_packed) x)) i
      = (Fin.cons n
        (Fin.append (Nat.simRecVec k a
          (fun j' => (h j').interp)
          (fun j' => (g j').interp) n x) x)) i
  congr 1
  funext j'
  show Nat.tupleAt k prev_packed j'
    = Nat.simRecVec k a (fun j' => (h j').interp)
        (fun j' => (g j').interp) n x j'
  -- prev_packed = Nat.tuplePack k (simRecVec ... n x)
  -- so tupleAt k prev_packed j' = simRecVec ... n x j'
  -- by Nat.tupleAt_tuplePack.
  show Nat.tupleAt k
        (Nat.tuplePack k
          (Nat.simRecVec k a (fun j' => (h j').interp)
            (fun j' => (g j').interp) n x)) j'
      = Nat.simRecVec k a (fun j' => (h j').interp)
          (fun j' => (g j').interp) n x j'
  exact Nat.tupleAt_tuplePack k _ j'
```

(The proof uses `congr 1; funext` to walk into nested
function applications. If the elaboration gets confused
by the `let` binding, the implementer may need to unfold
`prev_packed` explicitly via `show` or `change`. Report
deviation.)

- [ ] **Step 13.3: Add `packedRec_eq_tuplePack_simRecVec`**

```lean
/-- Main intermediate: the packed `boundedRec` output at
iteration `n` equals
`Nat.tuplePack k (Nat.simRecVec ... n x)`, under the
dominance hypothesis.  Master design §3.2. -/
theorem packedRec_eq_tuplePack_simRecVec
    (k a : ℕ)
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (1 + (k + 1) + a))
    (componentBound : ERMor1 (1 + a))
    (n : ℕ) (x : Fin a → ℕ)
    (h_dominates :
      ∀ (m : ℕ), m ≤ n → ∀ (j : Fin (k + 1)),
        Nat.simRecVec k a (fun j' => (h j').interp)
            (fun j' => (g j').interp) m x j
          ≤ componentBound.interp (Fin.cons m x))
    (h_mono :
      ∀ (m : ℕ), m ≤ n →
        componentBound.interp (Fin.cons m x)
          ≤ componentBound.interp (Fin.cons n x)) :
    (ERMor1.boundedRec
        (ERMor1.packedBase k a h)
        (ERMor1.packedStep k a g)
        (ERMor1.tuplePackedBound k componentBound)).interp
        (Fin.cons n x)
      = Nat.tuplePack k
          (Nat.simRecVec k a (fun j' => (h j').interp)
            (fun j' => (g j').interp) n x) := by
  -- Apply boundedRec_eq_natRec_of_bounded with
  --   base := packedBase k a h
  --   step := packedStep k a g
  --   bound := tuplePackedBound k componentBound
  -- Goal becomes: Nat.rec (packedBase.interp x)
  --                  (fun m prev => packedStep.interp ...) n
  --              = Nat.tuplePack k (simRecVec ... n x)
  -- Which we prove by induction on n.
  --
  -- Hypothesis 1 of boundedRec_eq_natRec_of_bounded:
  --   ∀ j, j ≤ n → Nat.rec ...j ≤ tuplePackedBound interp.
  -- Discharged via packedBound_dominates_iter (next task).
  -- Hypothesis 2: bound monotone in counter.
  -- Discharged via packedBound_mono (next task).
  --
  -- The inductive proof of Nat.rec value = Nat.tuplePack k ...
  -- uses packedBase_interp_eq_tuplePack_simRecVec_zero
  -- (base) and packedStep_interp_eq_tuplePack_step
  -- (step) in turn.
  sorry  -- placeholder; full proof follows in implementation
```

(The actual proof is ~40 lines and requires Tasks 14–15
which discharge the dominance and monotonicity
hypotheses. The implementer is expected to land this
fully — `sorry` is a placeholder showing the proof
structure but must be replaced with real tactics. Report
status `BLOCKED` if you cannot fill it.)

- [ ] **Step 13.4: Build and commit (with all three lemmas filled in)**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERSimultaneousBoundedRec.olean
lake build GebLean.Utilities.ERSimultaneousBoundedRec 2>&1 | tail -5
```

Expected: clean (no `sorry`-warnings).

```bash
git add GebLean/Utilities/ERSimultaneousBoundedRec.lean
git commit -m "Step 2 task 13: step-case lemmas for simultaneousBoundedRec correctness

Three intermediate lemmas:
- interp_packedStepCtx: slot routing's interp.
- packedStep_interp_eq_tuplePack_step: step case of the
  iteration-induction.
- packedRec_eq_tuplePack_simRecVec: main intermediate
  combining base and step via boundedRec_eq_natRec_of_bounded.

Master design §3.2."
```

---

## Task 14 — Hypothesis-discharge lemmas

**Files:**

- Modify: `GebLean/Utilities/ERSimultaneousBoundedRec.lean`
  (append, before `simultaneousBoundedRec_interp_correct`)

- [ ] **Step 14.1: Add `packedBound_dominates_iter`**

```lean
/-- Dominance hypothesis discharge: under
`h_dominates`, the packed state at iteration `m ≤ n` is
bounded by `tuplePackedBound k componentBound`'s
interp.  Used to apply
`boundedRec_eq_natRec_of_bounded` inside
`packedRec_eq_tuplePack_simRecVec`.  Master design §3.2. -/
theorem packedBound_dominates_iter
    (k a : ℕ)
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (1 + (k + 1) + a))
    (componentBound : ERMor1 (1 + a))
    (n : ℕ) (x : Fin a → ℕ) (m : ℕ) (h_m_le_n : m ≤ n)
    (h_dominates :
      ∀ (m' : ℕ), m' ≤ n → ∀ (j : Fin (k + 1)),
        Nat.simRecVec k a (fun j' => (h j').interp)
            (fun j' => (g j').interp) m' x j
          ≤ componentBound.interp (Fin.cons m' x)) :
    Nat.tuplePack k
        (Nat.simRecVec k a (fun j' => (h j').interp)
          (fun j' => (g j').interp) m x)
      ≤ (ERMor1.tuplePackedBound k componentBound).interp
          (Fin.cons m x) := by
  apply ERMor1.tuplePackedBound_dominates
  intro j
  exact h_dominates m h_m_le_n j
```

- [ ] **Step 14.2: Add `packedBound_mono`**

```lean
/-- Monotonicity hypothesis discharge: if
`componentBound.interp` is monotone in the iteration
counter, so is `tuplePackedBound k componentBound`.
Master design §3.2. -/
theorem packedBound_mono
    (k a : ℕ) (componentBound : ERMor1 (1 + a))
    (n : ℕ) (x : Fin a → ℕ)
    (h_mono :
      ∀ (m : ℕ), m ≤ n →
        componentBound.interp (Fin.cons m x)
          ≤ componentBound.interp (Fin.cons n x))
    (m : ℕ) (h_m_le_n : m ≤ n) :
    (ERMor1.tuplePackedBound k componentBound).interp
        (Fin.cons m x)
      ≤ (ERMor1.tuplePackedBound k componentBound).interp
          (Fin.cons n x) := by
  rw [ERMor1.interp_tuplePackedBound,
    ERMor1.interp_tuplePackedBound]
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  have := h_mono m h_m_le_n
  omega
```

- [ ] **Step 14.3: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERSimultaneousBoundedRec.olean
lake build GebLean.Utilities.ERSimultaneousBoundedRec 2>&1 | tail -5
```

Expected: clean.

```bash
git add GebLean/Utilities/ERSimultaneousBoundedRec.lean
git commit -m "Step 2 task 14: hypothesis-discharge lemmas

Two helpers for packedRec_eq_tuplePack_simRecVec's
boundedRec_eq_natRec_of_bounded application:
- packedBound_dominates_iter: dominance discharge via
  tuplePackedBound_dominates.
- packedBound_mono: monotonicity discharge via
  componentBound's monotonicity.

Master design §3.2."
```

---

## Task 15 — `simultaneousBoundedRec_interp_correct`

**Files:**

- Modify: `GebLean/Utilities/ERSimultaneousBoundedRec.lean`
  (append)

- [ ] **Step 15.1: Add the main correctness theorem**

```lean
/-- Conditional correctness of `simultaneousBoundedRec`:
when `componentBound` dominates each component value at
every iteration up to `n` (against the abstract semantic
function `Nat.simRecVec`), and `componentBound` is
monotone in the iteration counter up to `n`, the
ERMorN's i-th component computes exactly the i-th
simultaneous-recursion value at iteration `n`.  Master
design §3.2.  Realizes Tourlakis 2018 §0.1.0.35. -/
theorem simultaneousBoundedRec_interp_correct
    (k a : ℕ)
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (1 + (k + 1) + a))
    (componentBound : ERMor1 (1 + a))
    (n : ℕ) (x : Fin a → ℕ) (i : Fin (k + 1))
    (h_dominates :
      ∀ (m : ℕ), m ≤ n → ∀ (j : Fin (k + 1)),
        Nat.simRecVec k a (fun j' => (h j').interp)
            (fun j' => (g j').interp) m x j
          ≤ componentBound.interp (Fin.cons m x))
    (h_mono :
      ∀ (m : ℕ), m ≤ n →
        componentBound.interp (Fin.cons m x)
          ≤ componentBound.interp (Fin.cons n x)) :
    ((ERMor1.simultaneousBoundedRec k a h g componentBound)
        i).interp (Fin.cons n x) =
      Nat.simRecVec k a (fun j' => (h j').interp)
        (fun j' => (g j').interp) n x i := by
  simp only [ERMor1.simultaneousBoundedRec,
    ERMor1.interp_comp, ERMor1.interp_tupleAt]
  rw [ERMor1.packedRec_eq_tuplePack_simRecVec
        k a h g componentBound n x h_dominates h_mono]
  -- Goal: Nat.tupleAt k (Nat.tuplePack k (simRecVec ... n x)) i
  --     = simRecVec ... n x i
  rw [Nat.tupleAt_tuplePack]
```

- [ ] **Step 15.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERSimultaneousBoundedRec.olean
lake build GebLean.Utilities.ERSimultaneousBoundedRec 2>&1 | tail -5
```

Expected: clean.

```bash
git add GebLean/Utilities/ERSimultaneousBoundedRec.lean
git commit -m "Step 2 task 15: simultaneousBoundedRec_interp_correct

Conditional correctness: under componentBound dominance
+ monotonicity, the ERMorN's i-th component computes
the i-th simultaneous-recursion value.  Composes
packedRec_eq_tuplePack_simRecVec with
Nat.tupleAt_tuplePack.

Realizes Tourlakis 2018 §0.1.0.35; master design §3.2."
```

---

## Task 16 — `ERMor1.PolyBound.ofSimultaneousBoundedRec`

**Files:**

- Modify: `GebLean/Utilities/ERSimultaneousBoundedRec.lean`
  (append, inside a `namespace PolyBound` block)

- [ ] **Step 16.1: Add the PolyBound builder**

```lean
namespace PolyBound

/-- PolyBound builder for the i-th component of
`simultaneousBoundedRec`.  Each output component is
bounded by the packed state's value (via
`Nat.tupleAt_le`), which is itself bounded by
`tuplePackedBound k componentBound` (via
`interp_boundedRec_le_bound`).  The PolyBound shape
inherits from `ofTuplePackedBound`:

- `degree = pb_bound.degree * 2^k`
- `coefficient = tuplePackCoef k *
                   (pb_bound.coefficient + pb_bound.constant + 1)^(2^k)`
- `constant = 0`

Master design §3.2; §15.13 punch-list claim
("no `3^E`-style coefficient leaks out") satisfied:
the coefficient depends only on `(k, pb_bound)`, not on
the source K^sim term's structure.  -/
def ofSimultaneousBoundedRec (k a : ℕ)
    {h : Fin (k + 1) → ERMor1 a}
    {g : Fin (k + 1) → ERMor1 (1 + (k + 1) + a)}
    {componentBound : ERMor1 (1 + a)}
    (pb_bound : PolyBound componentBound)
    (i : Fin (k + 1)) :
    PolyBound
      ((ERMor1.simultaneousBoundedRec k a h g
          componentBound) i)
    where
  degree :=
    (PolyBound.ofTuplePackedBound k pb_bound).degree
  coefficient :=
    (PolyBound.ofTuplePackedBound k pb_bound).coefficient
  constant :=
    (PolyBound.ofTuplePackedBound k pb_bound).constant
  bounds := fun ctx => by
    -- Chain: component ≤ packedRec ≤ packedBound interp ≤ poly bound
    have h_component :
        ((ERMor1.simultaneousBoundedRec k a h g
              componentBound) i).interp ctx
          ≤ (ERMor1.boundedRec
                (ERMor1.packedBase k a h)
                (ERMor1.packedStep k a g)
                (ERMor1.tuplePackedBound k componentBound)).interp
                ctx := by
      simp only [ERMor1.simultaneousBoundedRec,
        ERMor1.interp_comp, ERMor1.interp_tupleAt]
      have h_at :
          Nat.tupleAt k
              ((ERMor1.boundedRec
                  (ERMor1.packedBase k a h)
                  (ERMor1.packedStep k a g)
                  (ERMor1.tuplePackedBound k
                    componentBound)).interp ctx) i
            ≤
              (ERMor1.boundedRec
                  (ERMor1.packedBase k a h)
                  (ERMor1.packedStep k a g)
                  (ERMor1.tuplePackedBound k
                    componentBound)).interp ctx :=
        Nat.tupleAt_le k _ i
      -- The simp + rw above reduces to Nat.tupleAt
      -- applied to the boundedRec interp; bound it.
      exact h_at
    have h_bound :
        (ERMor1.boundedRec
            (ERMor1.packedBase k a h)
            (ERMor1.packedStep k a g)
            (ERMor1.tuplePackedBound k componentBound)).interp
            ctx
          ≤ (ERMor1.tuplePackedBound k componentBound).interp
              ctx :=
      ERMor1.interp_boundedRec_le_bound _ _ _ ctx
    have h_poly :=
      (PolyBound.ofTuplePackedBound k pb_bound).bounds ctx
    -- Chain: h_component ≤ h_bound ≤ h_poly
    -- Final: ≤ coefficient * (max + 1)^degree + constant.
    omega

end PolyBound
```

(The `omega` at the end may not close the goal directly
if the inequality chain involves non-linear terms.
Fallback: `linarith [h_component, h_bound, h_poly]` or
explicit `Nat.le_trans` chain. Report deviation.)

- [ ] **Step 16.2: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERSimultaneousBoundedRec.olean
lake build GebLean.Utilities.ERSimultaneousBoundedRec 2>&1 | tail -5
```

Expected: clean.

```bash
git add GebLean/Utilities/ERSimultaneousBoundedRec.lean
git commit -m "Step 2 task 16: ERMor1.PolyBound.ofSimultaneousBoundedRec

Per-component PolyBound builder.  Each output component
is bounded via the chain (Nat.tupleAt_le)
(interp_boundedRec_le_bound) (ofTuplePackedBound's
bounds).  Inherits PolyBound shape from ofTuplePackedBound.

Master design §3.2; §15.13 punch-list claim satisfied."
```

---

## Task 17 — ER-side simultaneous-bounded-rec tests

**Files:**

- Create:
  `GebLeanTests/Utilities/ERSimultaneousBoundedRec.lean`
- Modify: `GebLeanTests.lean` (add import)

- [ ] **Step 17.1: Create test module skeleton + register import**

```lean
import GebLean.Utilities.ERSimultaneousBoundedRec

/-!
# Tests for `ERMor1.simultaneousBoundedRec`,
# `ERMor1.PolyBound.ofSimultaneousBoundedRec`.

Per the test discipline from
`GebLeanTests/Utilities/ERTupling.lean` (Gödel-numbering
kernel-reduction is impractical), this file restricts
runtime checks to PolyBound shape verification (struct
field access only).  Higher-arity correctness rests on
`simultaneousBoundedRec_interp_correct`.
-/

open GebLean

end
```

Add import to `GebLeanTests.lean`:

```lean
import GebLeanTests.Utilities.ERSimultaneousBoundedRec
```

- [ ] **Step 17.2: Add PolyBound shape examples**

Replace the `end` placeholder. Add:

```lean
-- PolyBound shape at small k with trivial componentBound
-- (ERMor1.PolyBound.ofZeroN at appropriate arity).
-- Struct field access only — no .interp evaluation.
example :
    (ERMor1.PolyBound.ofSimultaneousBoundedRec 1 0
       (ERMor1.PolyBound.ofZeroN 1)
       ⟨0, by decide⟩).degree = 0 := rfl
```

(If `ERMor1.PolyBound.ofZeroN` doesn't exist with that
signature, substitute the appropriate constructor.
`ofZeroN` is in `LawvereERPolynomialBound.lean`.)

- [ ] **Step 17.3: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLeanTests/Utilities/ERSimultaneousBoundedRec.olean
lake test 2>&1 | tail -5
```

Expected: clean.

```bash
git add GebLeanTests/Utilities/ERSimultaneousBoundedRec.lean GebLeanTests.lean
git commit -m "Step 2 task 17: ERSimultaneousBoundedRec tests

PolyBound shape verification at small k (struct field
access only).  Higher-arity correctness rests on
simultaneousBoundedRec_interp_correct's universal proof.

Per the import-at-skeleton-creation rule, the test import
is registered in GebLeanTests.lean as part of this same
commit.  Spec §6.3 transcribed."
```

---

## Task 18 — Final verification

**Files:**

- (No code changes; verification + workstream update.)

- [ ] **Step 18.1: Force re-elaboration of all 6 new modules**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/SimRec.olean
rm -f .lake/build/lib/lean/GebLean/Utilities/ERPackedBound.olean
rm -f .lake/build/lib/lean/GebLean/Utilities/ERSimultaneousBoundedRec.olean
rm -f .lake/build/lib/lean/GebLeanTests/Utilities/SimRec.olean
rm -f .lake/build/lib/lean/GebLeanTests/Utilities/ERPackedBound.olean
rm -f .lake/build/lib/lean/GebLeanTests/Utilities/ERSimultaneousBoundedRec.olean

lake build 2>&1 | tail -5
lake test 2>&1 | tail -5
```

Expected: clean — no `error:` lines anywhere.

- [ ] **Step 18.2: Citation cross-check**

For each public `def` / `theorem` in the three new
implementation modules, verify the docstring contains the
spec §7-listed citation verbatim:

- `Nat.simRecVec`, `Nat.simRec` — Tourlakis 2018 §0.1.0.7;
  master design §3.2.
- `Nat.simRecVec_zero`, `Nat.simRecVec_succ` — master
  design §3.2.
- `Nat.simRecVec_le_of_dominates` — master design §3.2.
- `ERMor1.tuplePackedBound` — master design §3.2;
  Tourlakis 2018 §0.1.0.34, p. 14.
- `ERMor1.interp_tuplePackedBound` — master design §3.2.
- `ERMor1.PolyBound.ofTuplePackedBound` — master design
  §3.2 + §15.13.
- `ERMor1.tuplePackedBound_dominates` — master design §3.2.
- `ERMor1.packedBase`, `packedStepCtx`, `packedStep` —
  master design §3.2.
- `ERMor1.simultaneousBoundedRec` — Tourlakis 2018
  §0.1.0.35; master design §3.2.
- Named intermediate lemmas
  (`packedBase_interp_eq_tuplePack_simRecVec_zero`,
  `packedStep_interp_eq_tuplePack_step`,
  `interp_packedStepCtx`,
  `packedRec_eq_tuplePack_simRecVec`,
  `packedBound_dominates_iter`, `packedBound_mono`) —
  master design §3.2.
- `simultaneousBoundedRec_interp_correct` — Tourlakis 2018
  §0.1.0.35; master design §3.2.
- `ERMor1.PolyBound.ofSimultaneousBoundedRec` — master
  design §3.2 + §15.13.

Fix any missing citations inline.

- [ ] **Step 18.3: Banned-words and lint scan**

Run `grep -nE` against the CLAUDE.md banned-words list
on the six new Lean files (three implementation +
three test). Expected: no output.

Run `markdownlint-cli2` on the spec and plan documents.
Expected: 0 errors.

```bash
git diff --check origin/terence/develop..HEAD
```

Expected: no whitespace errors.

- [ ] **Step 18.4: Update `.session/workstreams/`**

Open `.session/workstreams/er-ksim2-equiv-via-urm.md`.
Update the Progress section:

```markdown
## Progress

- Step 0 (master design): complete (3 rounds adversarial
  review, signed off).
- Step 1 (foundational ER-side tupling): complete.  Lands
  `Nat.tuplePack`, `Nat.tupleAt`, `Nat.tuplePackCoef`,
  bijection theorems, polynomial value bound, ER-side
  named composites, PolyBound builders, ERMorN-quotient
  round-trip lemmas, and decorative
  `LawvereERCat.tupleIso (k + 1) ≅ 1`.
- Step 2 (ER-side simultaneous bounded recursion):
  complete.  Lands `Nat.simRecVec` / `Nat.simRec`
  semantic functions, `ERMor1.tuplePackedBound` packed-
  state bound + PolyBound builder + dominance helper,
  `ERMor1.simultaneousBoundedRec` with conditional
  correctness theorem `simultaneousBoundedRec_interp_correct`
  and per-component PolyBound builder
  `ofSimultaneousBoundedRec`.  Plan at
  `docs/superpowers/plans/2026-05-03-step-2-er-simultaneous-bounded-rec.md`.
  Spec at
  `docs/superpowers/specs/2026-05-03-step-2-er-simultaneous-bounded-rec-design.md`.

## Next steps

- Step 3: `A_n^r` Tourlakis named composites in ER
  (`ERMor1.A_one`, `ERMor1.A_one_iter`, `ERMor1.A_two_iter`).
  See master design §3.3.
```

```bash
git add .session/workstreams/er-ksim2-equiv-via-urm.md
git commit -m "Step 2 task 18: final verification — step 2 complete

Forced re-elaboration of all 6 new modules clean.
Citation cross-check against spec §7 passes.
Banned-words scan clean.  Markdownlint clean.  No
whitespace errors.

.session/workstreams/er-ksim2-equiv-via-urm.md updated
with cycle-2 outcome.

Step 2 of the ER ↔ K^sim_2 categorical-equivalence
formalization complete; ERMor1.simultaneousBoundedRec is
in place for step 3 (A_n^r named composites)."
```

---

## Self-review

Before declaring step 2 done:

- [ ] **Spec coverage**: every entity in spec §3 / §4 / §5
  has an implementing task. Tasks 1–4 cover §3; Tasks 5–9
  cover §4; Tasks 10–17 cover §5.
- [ ] **Citation-discipline check**: every public entity
  has the §7-listed citation in its docstring.
- [ ] **`Fin (k + 1)` / `Fin (1 + (k + 1) + a)` index
  consistency**: the slot conventions match between
  `Nat.simRecVec`, `ERMor1.packedStepCtx`, `ERMor1.packedStep`,
  and the correctness theorem hypotheses.
- [ ] **Forced re-elaboration**: every new `.lean` module
  passes a fresh `lake build <Module>` after
  `rm .olean`.

---

## Notes for the implementer

- **`lake env lean` is forbidden** — always use
  `lake build` and `lake test`.
- **`lake clean` is forbidden** — never use it.
- **`sorry` placeholders in this plan are illustrative** —
  they show proof structure but must be replaced with
  real tactics before commit. The lakefile's
  `warningAsError = true` will reject any `sorry`-bearing
  code.
- **Forced re-elaboration is mandatory** before commit
  (per step 1's lesson; the trailing "Build completed
  successfully (N jobs)" line is unreliable when the
  module is already cached).
- **`#guard`-style ER-side `.interp` tests are restricted
  to trivial arity** (`k = 0`); higher-arity correctness
  rests on the universal `_interp_correct` proof.
- **Tactic flexibility**: when `simp only [...]` doesn't
  close a step, fall back to `change` + `rw` + explicit
  `Nat.tupleAt_tuplePack` or `congr 1; funext` chains
  per step-1's patterns. Report any deviation from the
  plan's tactics.
- **Adversarial review history**: cycle-2 plan-side
  reviews will live at
  `docs/research/2026-05-03-step-2-spec-adversarial-review-round-{1,2,3}.md`
  (the planning-phase chain mirrors step 1's three
  rounds).
