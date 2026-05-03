# Step 2 — ER-side multi-output bounded simultaneous recursion — Implementation Plan

> **For agentic workers:** Required sub-skill: use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Land `ERMor1.simultaneousBoundedRec` as a Lean
named composite realizing Tourlakis 2018 §0.1.0.34 (closure
of E^2 under simultaneous bounded recursion via the
pairing-based pack-and-unpack proof technique; §0.1.0.35 is
the higher-level corollary for `n ≥ 2`), plus its
conditional correctness theorem against the abstract
`Nat.simRecVec` semantic function and a per-component
PolyBound builder. Three new modules:
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
  §0.1.0.34 / §0.1.0.7 / §0.1.0.35, or master design §3.2).
  The primary citation is §0.1.0.34 (the pairing-based
  proof technique for E^2); §0.1.0.35 is cited only as the
  higher-level corollary for `n ≥ 2`.
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
K^sim hierarchy via simultaneous primitive recursion); the
pairing-based proof technique is from Tourlakis 2018
§0.1.0.34.

The step input convention matches master design §3.2's
prose `g_j(n, x⃗, F_0..F_k)` and the existing
`kSimStepContext` in `Utilities/KSimSzudzikSimrec.lean:364`:
slot 0 is the iteration counter, slots 1..a are the
parameter context, slots a+1..a+k+1 are the
previous-iteration component values.

See
`docs/superpowers/specs/2026-05-03-step-2-er-simultaneous-bounded-rec-design.md`
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

Step input convention (matching master design §3.2's
prose `g_j(n, x⃗, F_0..F_k)` and existing
`kSimStepContext` in
`Utilities/KSimSzudzikSimrec.lean:364`): slot 0 is the
iteration counter, slots 1..a are the parameter context,
slots a+1..a+k+1 are the previous-iteration component
values.  The step is therefore
`g_all : Fin (k + 1) → (Fin (a + 1 + (k + 1)) → ℕ) → ℕ`,
applied as
`g_all j (Fin.append (Fin.cons n x) prev)`.

Used to state `simultaneousBoundedRec_interp_correct` per
master design §3.2.  Realizes Tourlakis 2018 §0.1.0.7
(definition of K^sim hierarchy via simultaneous primitive
recursion); the pairing-based proof technique is from
Tourlakis 2018 §0.1.0.34. -/
def simRecVec (k a : ℕ)
    (h_all : Fin (k + 1) → (Fin a → ℕ) → ℕ)
    (g_all : Fin (k + 1) →
      (Fin (a + 1 + (k + 1)) → ℕ) → ℕ) :
    ℕ → (Fin a → ℕ) → (Fin (k + 1) → ℕ)
  | 0,     x => fun j => h_all j x
  | n + 1, x => fun j =>
      g_all j (Fin.append (Fin.cons n x)
        (simRecVec k a h_all g_all n x))
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
      (Fin (a + 1 + (k + 1)) → ℕ) → ℕ)
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
Step input convention matches master design §3.2 prose
g_j(n, x⃗, F_0..F_k) and existing kSimStepContext: slot 0
is the iteration counter, slots 1..a are the parameter
context, slots a+1..a+k+1 are the previous-iteration
component values.

Per the import-at-skeleton-creation rule, GebLean.lean's
import is registered as part of this same commit.

Realizes Tourlakis 2018 §0.1.0.7 (definition of K^sim
hierarchy via simultaneous primitive recursion); the
pairing-based proof technique is from §0.1.0.34.  Master
design §3.2."
```

---

## Task 2 — `@[simp]` recurrence lemmas

**Files:**

- Modify: `GebLean/Utilities/SimRec.lean` (append, inside
  the existing `namespace Nat ... end Nat` region)

- [ ] **Step 2.1: Add `simRecVec_zero` and `simRecVec_succ`**

Append within `namespace Nat`:

```lean
@[simp] theorem simRecVec_zero (k a : ℕ)
    (h_all : Fin (k + 1) → (Fin a → ℕ) → ℕ)
    (g_all : Fin (k + 1) →
      (Fin (a + 1 + (k + 1)) → ℕ) → ℕ)
    (x : Fin a → ℕ) (j : Fin (k + 1)) :
    simRecVec k a h_all g_all 0 x j = h_all j x := rfl

@[simp] theorem simRecVec_succ (k a : ℕ)
    (h_all : Fin (k + 1) → (Fin a → ℕ) → ℕ)
    (g_all : Fin (k + 1) →
      (Fin (a + 1 + (k + 1)) → ℕ) → ℕ)
    (n : ℕ) (x : Fin a → ℕ) (j : Fin (k + 1)) :
    simRecVec k a h_all g_all (n + 1) x j
      = g_all j (Fin.append (Fin.cons n x)
          (simRecVec k a h_all g_all n x))
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
      (Fin (a + 1 + (k + 1)) → ℕ) → ℕ)
    (componentBound : ℕ → (Fin a → ℕ) → ℕ)
    (h_base : ∀ j x, h_all j x ≤ componentBound 0 x)
    (h_step : ∀ n x prev j,
       (∀ j', prev j' ≤ componentBound n x) →
       g_all j (Fin.append (Fin.cons n x) prev)
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
-- arity = a + 1 + (k + 1) = 0 + 1 + 1 = 2: slot 0 =
-- counter, slot 1 = previous singleton component (no
-- params at a = 0).

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

At `k = 1, a = 0`, step input arity is
`a + 1 + (k + 1) = 0 + 1 + 2 = 3`: slot 0 = counter, no
params (a = 0), slots 1..2 = previous components 0 and 1.
The swap step (component 0 returns slot 2; component 1
returns slot 1) gives parity-dependent values from bases
`(1, 2)`:

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
slots 1..a = params, slots a+1..a+k+1 = prev-vector) and
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
  inside a new `namespace ERMor1.PolyBound` region)

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
-- PolyBound shape at k = 0: degree 0 * 2^0 = 0,
-- coefficient = tuplePackCoef 0 * (0 + 0 + 1)^1 = 1.
-- (Using ERMor1.PolyBound.ofZeroN 0 at arity 0 as a
-- trivial componentBound: degree = 0, coefficient = 0,
-- constant = 0.)
example :
    (ERMor1.PolyBound.ofTuplePackedBound 0
       (ERMor1.PolyBound.ofZeroN 0)).degree = 0 := rfl

example :
    (ERMor1.PolyBound.ofTuplePackedBound 1
       (ERMor1.PolyBound.ofZeroN 0)).degree = 0 := rfl

-- tuplePackCoef k for small k (sanity).
example :
    (ERMor1.PolyBound.ofTuplePackedBound 1
       (ERMor1.PolyBound.ofZeroN 0)).coefficient
      = Nat.tuplePackCoef 1 * 1 ^ (2 ^ 1) := rfl

example :
    (ERMor1.PolyBound.ofTuplePackedBound 1
       (ERMor1.PolyBound.ofZeroN 0)).constant = 0 := rfl
```

`ERMor1.PolyBound.ofZeroN 0` produces a PolyBound for
`ERMor1.zeroN 0` with `degree = 0`, `coefficient = 0`,
`constant = 0`.  The derived `ofTuplePackedBound`
therefore has `degree = pb.degree * 2^k = 0`,
`coefficient = tuplePackCoef k * (0 + 0 + 1)^(2^k) =
tuplePackCoef k`, `constant = 0`.  Adjust the example
values to match.

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

Realizes Tourlakis 2018 §0.1.0.34 (closure of E^2 under
simultaneous bounded recursion via the pairing-based
pack-and-unpack proof technique; §0.1.0.35 is the
higher-level corollary for `n ≥ 2`).  Master design §3.2.

Packs the `(k + 1)`-component state into a single
natural via `Nat.tuplePack` (step 1), applies single-
output `ERMor1.boundedRec` with packed-state bound
`ERMor1.tuplePackedBound k componentBound` (this step's
ERPackedBound module), and unpacks component-wise via
`Nat.tupleAt` (step 1).  Bottom-up named composite per
CLAUDE.md "bottom-up named-composite discipline".

Outer `simRecVec` step input convention (matching master
design §3.2's prose `g_j(n, x⃗, F_0..F_k)`): slot 0 is the
iteration counter, slots 1..a are the parameter context,
slots a+1..a+k+1 are the previous-iteration component
values.  Inner `boundedRec` step input convention
(matching `Utilities/ERArith.lean:2200`): slot 0 is the
counter, slot 1 is the packed previous state, slots
2..a+1 are the parameters.

See
`docs/superpowers/specs/2026-05-03-step-2-er-simultaneous-bounded-rec-design.md`
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
a `Fin (a + 1 + (k + 1))` index and returns the
`ERMor1 (a + 2)` selecting the appropriate slot.

Outer `(a + 1 + (k + 1))`-context (matching master design
§3.2 `g_j(n, x⃗, F_0..F_k)`):

- Slot 0 = counter.
- Slots 1..a = parameters.
- Slots a+1..a+k+1 = previous-iteration components.

Inner `(a + 2)`-context (matching `ERMor1.boundedRec`'s
step input convention, `Utilities/ERArith.lean:2200`):

- Slot 0 = counter.
- Slot 1 = packed previous state.
- Slots 2..a+1 = parameters.

Routing:

- Outer slot 0 → inner slot 0 (`proj 0`).
- Outer slots 1..a (parameter indices 0..a-1) → inner
  slots 2..a+1 (`proj (v + 1)` for outer index `v + 1`
  with `v < a`).
- Outer slots a+1..a+k+1 (prev indices 0..k) → tupleAt
  extraction from inner slot 1 (the packed previous
  state). -/
def packedStepCtx (k a : ℕ) :
    Fin (a + 1 + (k + 1)) → ERMor1 (a + 2)
  | ⟨0, _⟩ => ERMor1.proj 0
  | ⟨v + 1, h_v⟩ =>
      if h_param : v < a then
        ERMor1.proj ⟨v + 2, by omega⟩
      else
        ERMor1.comp
          (ERMor1.tupleAt k ⟨v - a, by omega⟩)
          ![ERMor1.proj 1]
```

(The first branch's outer index is 0; the second
branch's outer index is `v + 1`.  For the parameter case
(`v < a`, outer index `1 ≤ v + 1 ≤ a`), the target inner
slot is `v + 2` (zero-based parameter index `v` mapping
to inner slot `v + 2`).  For the prev case (`v ≥ a`,
outer index `a + 1 ≤ v + 1 ≤ a + k + 1`), the
prev-component index is `v - a`.  The two `omega`
invocations must close `v + 2 < a + 2` (from `v < a`)
and `v - a < k + 1` (from `v + 1 < a + 1 + (k + 1)` and
`v ≥ a`).)

- [ ] **Step 10.6: Define `ERMor1.packedStep`**

```lean
/-- Packed step function: takes the packed previous
state and produces the packed next state.  Each
component step `g j` is evaluated on the unpacked
context (counter + parameters + previous-component
vector), results are repacked via `Nat.tuplePack`.
Master design §3.2 step 1. -/
def packedStep (k a : ℕ)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    ERMor1 (a + 2) :=
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
  context, mapping outer Fin (a + 1 + (k + 1)) with
  (counter, params, prev_vector) layout to inner
  Fin (a + 2) with (counter, packed_prev, params)
  layout.
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
Realizes Tourlakis 2018 §0.1.0.34 (the proof technique:
closure of E^2 under simultaneous bounded recursion via
pairing-based pack-and-unpack; §0.1.0.35 is the
higher-level corollary for `n ≥ 2`).  Master design §3.2.

The implementation packs the `(k + 1)`-component state
into a single natural via `Nat.tuplePack`, applies
single-output `ERMor1.boundedRec` with a packed-state
bound derived via `ERMor1.tuplePackedBound`, then
unpacks the result component-wise via `Nat.tupleAt`.
Bottom-up named composite per CLAUDE.md "bottom-up
named-composite discipline".  -/
def simultaneousBoundedRec (k a : ℕ)
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (componentBound : ERMor1 (a + 1)) :
    ERMorN (a + 1) (k + 1) :=
  let packedRec : ERMor1 (a + 1) :=
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

Realizes Tourlakis 2018 §0.1.0.34 (the proof technique;
§0.1.0.35 is the higher-level corollary); master design
§3.2."
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
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
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

## Task 13 — Hypothesis-discharge lemmas

**Note (round-1 review C2):** Tasks 13 and 14 swapped
relative to the original draft, so the discharge lemmas
land before the main intermediate that consumes them.

**Files:**

- Modify: `GebLean/Utilities/ERSimultaneousBoundedRec.lean`
  (append)

- [ ] **Step 13.1: Add `packedBound_dominates_iter`**

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
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (componentBound : ERMor1 (a + 1))
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

- [ ] **Step 13.2: Add `packedBound_mono`**

```lean
/-- Monotonicity hypothesis discharge: if
`componentBound.interp` is monotone in the iteration
counter, so is `tuplePackedBound k componentBound`.
Master design §3.2. -/
theorem packedBound_mono
    (k a : ℕ) (componentBound : ERMor1 (a + 1))
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

- [ ] **Step 13.3: Build and commit**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERSimultaneousBoundedRec.olean
lake build GebLean.Utilities.ERSimultaneousBoundedRec 2>&1 | tail -5
```

Expected: clean.

```bash
git add GebLean/Utilities/ERSimultaneousBoundedRec.lean
git commit -m "Step 2 task 13: hypothesis-discharge lemmas

Two helpers for packedRec_eq_tuplePack_simRecVec's
boundedRec_eq_natRec_of_bounded application:
- packedBound_dominates_iter: dominance discharge via
  tuplePackedBound_dominates.
- packedBound_mono: monotonicity discharge via
  componentBound's monotonicity.

Master design §3.2."
```

---

## Task 14 — Step lemma + main intermediate

**Files:**

- Modify: `GebLean/Utilities/ERSimultaneousBoundedRec.lean`
  (append)

- [ ] **Step 14.1: Add helper `interp_packedStepCtx`**

A small helper that the step-case proof will consume —
proving how `packedStepCtx`'s interp maps slots of the
outer step's input context to the inner ER computation.
The outer convention is `(counter, params, prev)` and the
inner is `(counter, packed_prev, params)`:

```lean
/-- Interp of `packedStepCtx` at each slot of the
`Fin (a + 1 + (k + 1))`-context.

Outer slot 0 routes to the inner counter (slot 0).
Outer slots 1..a (parameter indices 0..a-1) route to
inner slots 2..a+1 (the parameters).  Outer slots
a+1..a+k+1 (prev indices 0..k) route via `Nat.tupleAt k`
extraction from inner slot 1 (the packed previous
state).  -/
theorem interp_packedStepCtx (k a : ℕ)
    (n prev_packed : ℕ) (x : Fin a → ℕ)
    (i : Fin (a + 1 + (k + 1))) :
    (ERMor1.packedStepCtx k a i).interp
        (Fin.cons n (Fin.cons prev_packed x))
      = (Fin.append (Fin.cons n x)
          (Nat.tupleAt k prev_packed)) i := by
  rcases i with ⟨v, h_v⟩
  match v, h_v with
  | 0, _ =>
      -- proj 0: returns slot 0 of the inner ctx = n.
      -- RHS at index 0: Fin.append's left = (Fin.cons n x) 0 = n.
      simp only [ERMor1.packedStepCtx, ERMor1.interp_proj,
        Fin.append_left, Fin.cons_zero]
  | s + 1, h_in =>
      by_cases h_param : s < a
      · -- Param case: proj (s + 2) returns x ⟨s, _⟩.
        -- RHS at index s + 1: Fin.append's left at s + 1
        -- = Fin.cons n x ⟨s + 1, _⟩ = x ⟨s, _⟩.
        simp only [ERMor1.packedStepCtx, h_param,
          ERMor1.interp_proj, Fin.append_left,
          Fin.cons_succ]
      · -- Prev case: comp tupleAt at inner slot 1 returns
        -- Nat.tupleAt k prev_packed ⟨s - a, _⟩.
        -- RHS at index s + 1 ≥ a + 1: Fin.append's right
        -- at (s + 1 - (a + 1)) = s - a, which is the
        -- prev-vector index.
        simp only [ERMor1.packedStepCtx, h_param,
          ERMor1.interp_comp, ERMor1.interp_tupleAt,
          ERMor1.interp_proj, Fin.append_right,
          Fin.cons_zero]
```

(If the `simp only` calls do not close, additional
`Fin.append_left` / `Fin.append_right` /
`Fin.cons_zero` / `Fin.cons_succ` lemmas may be needed.
The implementer can also reference the existing
`kSimStepContext_interp` lemma in `KSimSzudzikSimrec.lean`
for an analogous slot-routing pattern.  CLAUDE.md forbids
`sorry` in commits; iterate until clean before
committing.)

- [ ] **Step 14.2: Add `packedStep_interp_eq_tuplePack_step`**

```lean
/-- Step case: applying `packedStep` to a packed state
`prev_packed` (which equals
`Nat.tuplePack k (simRecVec ... n x)`) yields
`Nat.tuplePack k (simRecVec ... (n + 1) x)`.  Master
design §3.2. -/
theorem packedStep_interp_eq_tuplePack_step
    (k a : ℕ)
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
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
    ERMor1.interp_tuplePack, Nat.simRecVec_succ]
  congr 1
  funext j
  rw [ERMor1.interp_comp]
  congr 1
  funext i
  rw [ERMor1.interp_packedStepCtx]
  -- Goal: (Fin.append (Fin.cons n x)
  --         (Nat.tupleAt k prev_packed)) i
  --     = (Fin.append (Fin.cons n x)
  --         (Nat.simRecVec k a ... n x)) i
  congr 1
  funext j'
  show Nat.tupleAt k prev_packed j'
    = Nat.simRecVec k a (fun j' => (h j').interp)
        (fun j' => (g j').interp) n x j'
  show Nat.tupleAt k
        (Nat.tuplePack k
          (Nat.simRecVec k a (fun j' => (h j').interp)
            (fun j' => (g j').interp) n x)) j'
      = Nat.simRecVec k a (fun j' => (h j').interp)
          (fun j' => (g j').interp) n x j'
  exact Nat.tupleAt_tuplePack k _ j'
```

(The proof uses `congr 1; funext` to walk into nested
function applications.  If the elaboration gets confused
by the `let` binding, the implementer may need to unfold
`prev_packed` explicitly via `show` or `change`.)

- [ ] **Step 14.3: Add `Nat_rec_packed_eq_tuplePack_simRecVec`**

This is the unconditional `Nat.rec`-trace identity,
extracted to top level so it is available both for the
dominance discharge and for the main equality (round-2
review fix E1):

```lean
/-- The `Nat.rec`-trace of `(packedBase, packedStep)`
equals `Nat.tuplePack k (simRecVec ... j x)`.  Proven by
induction on `j`, dispatching the base case via
`packedBase_interp_eq_tuplePack_simRecVec_zero` and the
step case via `packedStep_interp_eq_tuplePack_step`.
This is an unconditional equation (no dominance
hypothesis); the `boundedRec`-vs-`Nat.rec` correctness
input is what consumes the dominance hypothesis at the
caller.  Master design §3.2. -/
theorem Nat_rec_packed_eq_tuplePack_simRecVec
    (k a : ℕ)
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (j : ℕ) (x : Fin a → ℕ) :
    Nat.rec ((ERMor1.packedBase k a h).interp x)
        (fun m prev =>
          (ERMor1.packedStep k a g).interp
            (Fin.cons m (Fin.cons prev x))) j
      = Nat.tuplePack k
          (Nat.simRecVec k a (fun j' => (h j').interp)
            (fun j' => (g j').interp) j x) := by
  induction j with
  | zero =>
      -- The zero case of `Nat.rec` reduces definitionally
      -- to the base value.  The base value
      -- `(packedBase k a h).interp x` equals
      -- `Nat.tuplePack k (simRecVec ... 0 x)` by the
      -- packedBase lemma.
      exact
        ERMor1.packedBase_interp_eq_tuplePack_simRecVec_zero
          k a h g x
  | succ m ih =>
      -- The succ case of `Nat.rec` reduces definitionally
      -- to `step m (Nat.rec ... m)`.  Substitute the
      -- inductive hypothesis to expose the
      -- `tuplePack k (simRecVec ... m x)` form, then
      -- close via `packedStep_interp_eq_tuplePack_step`.
      simp only [ih]
      exact
        ERMor1.packedStep_interp_eq_tuplePack_step
          k a h g m x
```

(If `simp only [ih]` does not fire because `Nat.rec`'s
definitional unfolding is needed first, the implementer
can use a `change` step to expose
`(packedStep ...).interp (Fin.cons m (Fin.cons (Nat.rec ... m) x))
= _` and then `rw [ih]`.)

- [ ] **Step 14.4: Add `packedRec_eq_tuplePack_simRecVec`**

```lean
/-- Main intermediate: the packed `boundedRec` output at
iteration `n` equals
`Nat.tuplePack k (Nat.simRecVec ... n x)`, under the
dominance hypothesis.  Master design §3.2. -/
theorem packedRec_eq_tuplePack_simRecVec
    (k a : ℕ)
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (componentBound : ERMor1 (a + 1))
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
  -- Rewrite `boundedRec` via `boundedRec_eq_natRec_of_bounded`
  -- to expose a `Nat.rec`-trace, then close via
  -- `Nat_rec_packed_eq_tuplePack_simRecVec`.  The two
  -- side-conditions of `boundedRec_eq_natRec_of_bounded`
  -- (dominance + monotonicity) are dispatched via the
  -- discharge lemmas from Task 13, with the `Nat.rec`-vs-
  -- `simRecVec` identity reused inside the dominance
  -- discharge to convert the `Nat.rec` form (matching the
  -- lemma's hypothesis shape) into the `simRecVec` form
  -- (matching `packedBound_dominates_iter`'s shape).
  rw [ERMor1.boundedRec_eq_natRec_of_bounded
        (ERMor1.packedBase k a h)
        (ERMor1.packedStep k a g)
        (ERMor1.tuplePackedBound k componentBound)
        n x ?_ ?_]
  · exact ERMor1.Nat_rec_packed_eq_tuplePack_simRecVec
      k a h g n x
  · -- Hypothesis 1 of boundedRec_eq_natRec_of_bounded:
    -- ∀ j ≤ n, Nat.rec ... j ≤ tuplePackedBound interp.
    intro j h_j_le_n
    rw [ERMor1.Nat_rec_packed_eq_tuplePack_simRecVec
          k a h g j x]
    exact ERMor1.packedBound_dominates_iter
      k a h g componentBound n x j h_j_le_n h_dominates
  · -- Hypothesis 2: bound monotone in counter.
    exact ERMor1.packedBound_mono
      k a componentBound n x h_mono
```

(`rw` against `boundedRec_eq_natRec_of_bounded` produces
the equation with side-conditions exposed via `?_`
placeholders, which are discharged in order: the main
equality (closed by `Nat_rec_packed_eq_tuplePack_simRecVec`),
then the dominance hypothesis, then the monotonicity
hypothesis.  If `rw` does not unify (depending on the
lemma's exact form), fall back to constructing the
equality via `Eq.trans
(boundedRec_eq_natRec_of_bounded ...) (Nat_rec_packed_...)`
and dispatching the side-conditions separately.)

- [ ] **Step 14.5: Build and commit (with all four lemmas filled in)**

```bash
rm -f .lake/build/lib/lean/GebLean/Utilities/ERSimultaneousBoundedRec.olean
lake build GebLean.Utilities.ERSimultaneousBoundedRec 2>&1 | tail -5
```

Expected: clean (no `sorry`-warnings).

```bash
git add GebLean/Utilities/ERSimultaneousBoundedRec.lean
git commit -m "Step 2 task 14: step-case lemmas + main intermediate

Four intermediate lemmas:
- interp_packedStepCtx: slot routing's interp.
- packedStep_interp_eq_tuplePack_step: step case of the
  iteration-induction.
- Nat_rec_packed_eq_tuplePack_simRecVec: unconditional
  Nat.rec-trace identity, factored to top level so it is
  available both for the dominance discharge and for the
  main equality (round-2 review fix E1).
- packedRec_eq_tuplePack_simRecVec: main intermediate
  combining base and step via boundedRec_eq_natRec_of_bounded
  and the discharge lemmas from task 13.

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
design §3.2.  Realizes Tourlakis 2018 §0.1.0.34 (the
proof technique; §0.1.0.35 is the higher-level
corollary). -/
theorem simultaneousBoundedRec_interp_correct
    (k a : ℕ)
    (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (componentBound : ERMor1 (a + 1))
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
    ERMor1.interp_comp, ERMor1.interp_tupleAt,
    Matrix.cons_val_zero]
  rw [ERMor1.packedRec_eq_tuplePack_simRecVec
        k a h g componentBound n x h_dominates h_mono]
  -- Goal: Nat.tupleAt k (Nat.tuplePack k
  --         (simRecVec ... n x)) i
  --     = simRecVec ... n x i
  exact Nat.tupleAt_tuplePack k _ i
```

(If `simp only` does not reduce the
`fun _ : Fin 1 => packedRec.interp ctx` lambda to a
direct `interp` call, add a `change` step to align the
goal:

```lean
change Nat.tupleAt k
          ((ERMor1.boundedRec ...).interp
            (Fin.cons n x)) i = _
```

Iterate until clean before committing.)

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

Realizes Tourlakis 2018 §0.1.0.34 (the proof technique;
§0.1.0.35 is the higher-level corollary); master design
§3.2."
```

---

## Task 16 — `ERMor1.PolyBound.ofSimultaneousBoundedRec`

**Files:**

- Modify: `GebLean/Utilities/ERSimultaneousBoundedRec.lean`
  (append, inside a `namespace PolyBound` region)

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
    {g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))}
    {componentBound : ERMor1 (a + 1)}
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
    -- Chain via Nat.le_trans: component ≤ packedRec
    -- ≤ tuplePackedBound interp ≤ poly bound.  Cannot
    -- use `omega` here because the final goal has a
    -- non-linear `^` term (round-1 review fix C5).
    have h_component :
        ((ERMor1.simultaneousBoundedRec k a h g
              componentBound) i).interp ctx
          ≤ (ERMor1.boundedRec
                (ERMor1.packedBase k a h)
                (ERMor1.packedStep k a g)
                (ERMor1.tuplePackedBound k
                  componentBound)).interp ctx := by
      simp only [ERMor1.simultaneousBoundedRec,
        ERMor1.interp_comp, ERMor1.interp_tupleAt,
        Matrix.cons_val_zero]
      exact Nat.tupleAt_le k _ i
    have h_bound :=
      ERMor1.interp_boundedRec_le_bound
        (ERMor1.packedBase k a h)
        (ERMor1.packedStep k a g)
        (ERMor1.tuplePackedBound k componentBound) ctx
    have h_poly :=
      (PolyBound.ofTuplePackedBound k pb_bound).bounds ctx
    exact h_component.trans (h_bound.trans h_poly)

end PolyBound
```

(The terminal `Nat.le_trans` chain replaces the original
`omega`, which cannot close non-linear `^`-bearing goals.
The `simp only`+`exact Nat.tupleAt_le` is a tighter
restatement of the per-component bound; if it does not
reduce cleanly, fall back to a `change` step matching the
post-`simp` goal shape.)

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

- `Nat.simRecVec`, `Nat.simRec` — Tourlakis 2018 §0.1.0.7
  (definition); §0.1.0.34 (proof technique); master design
  §3.2.
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
  §0.1.0.34 (the proof technique; §0.1.0.35 is the
  higher-level corollary for `n ≥ 2`); master design §3.2.
- Named intermediate lemmas
  (`packedBase_interp_eq_tuplePack_simRecVec_zero`,
  `packedStep_interp_eq_tuplePack_step`,
  `interp_packedStepCtx`,
  `Nat_rec_packed_eq_tuplePack_simRecVec`,
  `packedRec_eq_tuplePack_simRecVec`,
  `packedBound_dominates_iter`, `packedBound_mono`) —
  master design §3.2.
- `simultaneousBoundedRec_interp_correct` — Tourlakis 2018
  §0.1.0.34 (the proof technique; §0.1.0.35 is the
  higher-level corollary); master design §3.2.
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
- [ ] **`Fin (k + 1)` / `Fin (a + 1 + (k + 1))` index
  consistency**: the slot conventions match between
  `Nat.simRecVec`, `ERMor1.packedStepCtx`,
  `ERMor1.packedStep`, and the correctness theorem
  hypotheses.
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
