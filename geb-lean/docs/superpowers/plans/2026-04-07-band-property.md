# ElegantPairing Band Property and Injectivity

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended)
> or superpowers:executing-plans to implement this plan
> task-by-task.

**Goal:** Fix the `elegantPair`/`elegantUnpair`
boundary condition, then prove the band property
(`isqrt(EP(x,y)) = toRSN(max(x,y))`) and derive
injectivity.

**Architecture:** The band property decomposes into
a level-transition lemma (isqrtState at perfect
squares) and a within-level stability lemma (isqrt
doesn't change within a level).  Both use NNO fold
composition ("iterate m+n = iterate n after m").

**Tech Stack:** Lean 4, `HasPBTO`,
`HasChosenFiniteProducts`, `nnoElim`, `iteBranches`

---

## Execution Status (2026-04-08)

- **Task 0:** DONE (commit `6dd5da22`)
- **Task 1:** DONE (commit `8781b212`)
  `nnoElim_fold_compose`, `isqrtState_natPlus`,
  `iteBranches_postcomp` (new infrastructure)
- **Tasks 2-3:** Building blocks DONE, main proofs
  BLOCKED on within-level stability (multi-step).

### What's proved

- `nnoElim_fold_compose`: iterate additivity
- `iteBranches_postcomp`: post-composition through
  conditionals (via `elim_algebra_morphism`
  naturality of `iteFold`)
- `isqrtState_natPlus`: fold composition for
  isqrtState
- `isqrtStep_fst/snd`: projection rules
- `isqrtLevelState` + `_ℓ` + `_s`: definition
  and computation rules
- `isqrtStep_at_ℓ`: boundary behavior
- `isqrtStep_at_β`: one-step countdown agreement
- `isqrtStep_fst_stable`: one-step root stability
- `isqrtCountdown` + `nnoElim_countdown_fst`:
  unconditional root preservation under countdown
- `natSquareGap`: `2k + 1` definition

### Open problem: multi-step within-level stability

The gap: showing `isqrtStep^j(s, r)` agrees with
`countdown^j(s, r)` when `j ≤ r`.  `nnoElim_uniq`
only proves unconditional equalities, but this
agreement is conditional on `j ≤ r`.  One-step
case (`isqrtStep_at_β`) and unconditional countdown
root stability (`nnoElim_countdown_fst`) are proved.

**Candidate approaches:**

**(A) Combined fold with internal dispatch.**
Define a fold on `j` that maintains
`(countdown_state, isqrtStep_state)` and uses
`iteBranches` at each step to dispatch based on
whether the remaining (tracked in the countdown
state) is positive.  When positive, both states
advance identically via `isqrtStep_at_β`.  When
zero, the isqrt state crosses a boundary but the
fold result is already determined.

**(B) Direct decomposition via natSquareGap.**
Split the `2k + 1` steps as
`natPlus(natPlus(k, k), natSucc(ℓ))`, use fold
composition to separate the `2k` countdown steps
from the final boundary step.  Prove the countdown
part `isqrtStep^(2k)(k, 2k) = (k, ℓ)` as a
separate lemma, possibly by fold on `k` using the
self-subtraction property `natTruncSub(n, n) = ℓ`.

**(C) Bounded NNO fold combinator.**
Introduce a general "iterate step `j` times,
but only while a condition holds" combinator, prove
it agrees with `nnoElim` when the condition holds
throughout.  Most general but most infrastructure.

---

## Task 0: Fix boundary condition bug

**File:** `GebLean/NatElegantPair.lean`

The condition `natTruncSub ≫ isLeafEndo` gives
`ℓ` when `x ≤ y`, but Szudzik's pairing sends
`x = y` to the row phase (`x² + x + y`), not the
column phase (`y² + x`).

- [x] **Step 1:** Change `elegantPair` condition
- [x] **Step 2:** Fix `elegantUnpair` to match
- [x] **Step 3:** Update computation theorems
- [x] **Step 4:** Build and verify

---

## Task 1: NNO fold composition (iterate additivity)

**File:** `GebLean/NatNNO.lean`

Prove that iterating a step function `m+n` times
equals iterating `n` times after `m` times.

```lean
theorem nnoElim_natPlus
    {X : C} (g : X ⟶ X) :
    cfpMap (nnoElim (𝟙 X) g) (𝟙 p.T) ≫
      nnoElim (𝟙 X) g =
    cfpMap (𝟙 X) natPlus ≫
      nnoElim (𝟙 X) g
```

This says: `g^n(g^m(init)) = g^(m+n)(init)`.

- [x] **Step 1:** Proved as `nnoElim_fold_compose`
  (reformulated with correct product association:
  `cfpMap (nnoElim f g) (𝟙 T) ≫ nnoElim (𝟙 X) g
  = nnoElim (nnoElim f g) g`).
  Also proved `isqrtState_natPlus` (specialized).
  Also proved `iteBranches_postcomp` (new
  infrastructure via `elim_algebra_morphism`).
- [x] **Step 2:** Build and verify

---

## Task 2: Level transition

**File:** `GebLean/NatElegantPair.lean`

Prove that `isqrtState` at perfect squares gives the
correct level boundary state.

```lean
theorem isqrtState_natSquare :
    natSquare ≫ isqrtState =
    cfpLift (isqrt_counter) (isqrt_remaining)
```

where the state at `k²` is `(toRSN(k), 2·toRSN(k))`.

- [x] **Step 1:** `isqrtLevelState` defined with
  `isqrtLevelStep`, base (`_ℓ`), and step (`_s`)
  rules proved.

- [ ] **Step 2:** Prove `natSquare ≫ isqrtState
  = isqrtLevelState`.  BLOCKED on multi-step
  within-level stability (see status section
  above for candidate approaches).

- [ ] **Step 3:** Build and verify.

---

## Task 3: Within-level stability

**File:** `GebLean/NatElegantPair.lean`

Prove that applying `isqrtStep` to a state
`(s, r)` with `r > 0` preserves `s`:
`fst(isqrtStep(s, r)) = s` when
`isLeafEndo(r) = treeFalse`.

```lean
theorem isqrtStep_fst_nonzero :
    isqrtStep ≫ cfpFst T T =
    iteBranches (cfpFst T T ≫ natSucc)
      (cfpFst T T)
      (cfpSnd T T ≫ isLeafEndo)
```

This follows directly from the definition of
`isqrtStep` (the first component IS this
`iteBranches` expression).

Then for a countdown of `j` steps from state
`(s, r)` with `r ≥ j` (all `r, r-1, ..., r-j+1`
are nonzero), the root stays `s`.

- [x] **Step 1:** Proved as `isqrtStep_fst`
  (definitional), `isqrtStep_at_β` (one-step
  countdown agreement), `isqrtStep_fst_stable`
  (one-step root stability).

- [ ] **Step 2:** Multi-step root stability.
  BLOCKED: conditional fold reasoning.
  Building blocks in place:
  `isqrtCountdown` + `nnoElim_countdown_fst`
  (unconditional countdown root preservation).
  See status section for candidate approaches.

- [ ] **Step 3:** Build and verify.

---

## Task 4: Band property

**File:** `GebLean/NatElegantPair.lean`

- [ ] **Step 1:** Column band:
  `isqrt(natPlus(natSquare(y), x)) = toRSN(y)`
  when `x < y`.  Proof: by Task 2, state at `y²`
  is `(toRSN(y), 2y)`.  By Task 3, `x` more steps
  (with `x < y ≤ 2y`) keep root at `toRSN(y)`.

- [ ] **Step 2:** Row band:
  `isqrt(natPlus(natPlus(natSquare(x), x), y))
  = toRSN(x)` when `y ≤ x`.  Proof: state at
  `x²` is `(toRSN(x), 2x)`.  After `x` more
  steps: `(toRSN(x), x)`.  After `y` more steps
  (with `y ≤ x`): root stays `toRSN(x)`.

- [ ] **Step 3:** Combine into:
  `elegantPair ≫ isqrt = max_morphism ≫ toRSN`.
  Use `iteBranches` dispatch on the same condition
  as `elegantPair`.

- [ ] **Step 4:** Build and verify.

---

## Task 5: Section property and injectivity

**File:** `GebLean/NatElegantPair.lean`

- [ ] **Step 1:** Prove remainder extraction:
  `elegantPair ≫ elegantUnpairRemainder`
  recovers the "offset within level."

- [ ] **Step 2:** Prove section:
  `elegantPair ≫ elegantUnpair = 𝟙 (T × T)`.
  Dispatch on the phase condition:
  - Column: EP = y² + x. isqrt = y, r = x.
    s > r (since y > x). Unpair returns (r, s)
    = (x, y). ✓
  - Row: EP = x² + x + y. isqrt = x, r = x + y.
    s ≤ r. Unpair returns (s, r-s) = (x, y). ✓

- [ ] **Step 3:** Derive injectivity:
  `natEq(EP(a,b), EP(c,d))` absorbed by
  `boolAnd(natEq(a,c), natEq(b,d))`.

- [ ] **Step 4:** Build and verify. Commit.

---

## Notes

### Why the boundary fix matters

Szudzik's pairing assigns `EP(k, k) = k² + 2k`
(row phase), not `k² + k` (column).  This ensures
level `k` has exactly `2k + 1` pairs:

- Column: `(0,k), ..., (k-1,k)` gives `k` pairs,
  values `k², ..., k²+k-1`
- Row: `(k,0), ..., (k,k)` gives `k+1` pairs,
  values `k²+k, ..., k²+2k`

Total: `k² + 2k + 1 = (k+1)²` pairs through
level `k`.

### Available lemmas

- `nnoElim_ℓ`, `nnoElim_s`, `nnoElim_uniq`
- `natSquare_ℓ`, `natSquareState_s`
- `isqrtState_ℓ`, `isqrt_ℓ`, `isqrtState_s`
- `natTruncSub_natPlus_cancel`
- `natPlus_isLeafEndo_eq_boolAnd`
- `isLeafEndo_natTruncSub_mono`
