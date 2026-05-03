# Step 2 — ER-side multi-output bounded simultaneous recursion

Spec for cycle 2 of the ER ↔ K^sim_2 categorical-equivalence
formalization (master design:
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`).
This cycle lands `ERMor1.simultaneousBoundedRec` and its
correctness theorem and per-component PolyBound builder.
The construction packs the multi-component state via the
step-1 `Nat.tuplePack` infrastructure, applies the
existing single-output `ERMor1.boundedRec`, and unpacks
component-wise via `Nat.tupleAt`.

## §1 Status and motivation

### §1.1 Goal

Realize Tourlakis 2018 §0.1.0.34 (closure of E^2 under
simultaneous bounded recursion via the pairing-based
pack-and-unpack proof technique; §0.1.0.35 is the
higher-level generalization to E^{n+1} for `n ≥ 2`) as a
Lean named composite `ERMor1.simultaneousBoundedRec`
with conditional correctness against the abstract
semantic function `Nat.simRecVec`, plus a PolyBound
builder per output component.  Downstream consumers:

- Step 4 majorization (master design §3.4):
  `simultaneousBoundedRec`'s polyBound feeds the level-2
  iteration arithmetic.
- Step 5 `kToER` (master design §3.5): the simrec case of
  `kToER` translates each K^sim simrec into an ER
  `simultaneousBoundedRec` call.

### §1.2 Scope

In scope:

- `GebLean/Utilities/SimRec.lean` (Nat-level): `Nat.simRecVec`,
  `Nat.simRec`, recurrence simp lemmas, dominance helper.
- `GebLean/Utilities/ERPackedBound.lean` (ER-level):
  `ERMor1.tuplePackedBound`, interp lemma, PolyBound builder
  `ofTuplePackedBound`, helper `tuplePackedBound_dominates`.
- `GebLean/Utilities/ERSimultaneousBoundedRec.lean` (ER-level):
  `ERMor1.simultaneousBoundedRec` def with named helpers
  (`packedBase`, `packedStep`, `packedStepCtx`),
  conditional correctness theorem
  `simultaneousBoundedRec_interp_correct` with named
  intermediate lemmas, per-component PolyBound builder
  `ofSimultaneousBoundedRec`.
- Tests: `GebLeanTests/Utilities/SimRec.lean`,
  `GebLeanTests/Utilities/ERPackedBound.lean`,
  `GebLeanTests/Utilities/ERSimultaneousBoundedRec.lean`.

Out of scope:

- `A_n^r` named composites (step 3).
- Majorization theorem (step 4).
- `kToER` translation (step 5).
- K^sim-side simrec construction (built into `KMor1` already
  per Phase 1).
- Tower-height arithmetic as an explicit theorem (documented
  property only; promote if step 4 needs it).

### §1.3 Implementation flexibility vs literature contract

Per CLAUDE.md "Non-negotiable interfaces for categories
formalizing pre-existing mathematical objects": the
mathematical content is fixed by literature; Lean
representation choices may flex if implementation reveals
a cleaner path.

**Literature-fixed (non-negotiable):**

- The `simultaneousBoundedRec` API realizes Tourlakis 2018
  §0.1.0.34 (the proof technique: pairing-based pack-and-
  unpack; §0.1.0.35 is the higher-level corollary for
  `n ≥ 2`).
- The packing strategy uses `Nat.tuplePack` per master
  design §3.2 (consuming step 1's infrastructure).
- The packed-state bound formula is
  `tuplePackCoef k * (cb + 1)^(2^k)`, derived from step 1's
  `Nat.tuplePack_le`.
- Correctness is stated against `Nat.simRecVec` (the
  abstract semantic function for simultaneous primitive
  recursion).
- The PolyBound shape inherits step 1's
  `coefficient * (max+1)^degree + constant` structure.

**Lean-side flexible:**

- Named-helper decomposition (which sub-expressions get
  named `def`s vs inlined).
- Per-component vs vector PolyBound representation
  (current spec is per-component; switching to vector is
  acceptable if implementation lessons reveal it).
- Exact form of intermediate lemmas (split / combined /
  helper-factored).
- Slot-routing implementations for `Fin` indices.
- Choice of tactic (e.g., `omega` vs `linarith` vs explicit
  arithmetic) for arithmetic steps.

The implementer may revise any Lean-side representation
during implementation if proofs reveal a cleaner path,
provided the literature contract is preserved.

## §2 Architecture and module layout

Three new modules under `GebLean/Utilities/`, in
dependency order:

### §2.1 `GebLean/Utilities/SimRec.lean` (Nat-level)

- Imports: `Mathlib.Data.Fin.Tuple.Basic` only.
  Standalone Nat-level — no ER imports.
- Namespace: `Nat`.
- Public surface:
  - `Nat.simRecVec`, `Nat.simRec`.
  - `@[simp] Nat.simRecVec_zero`, `Nat.simRecVec_succ`.
  - `Nat.simRecVec_le_of_dominates` (dominance helper).

### §2.2 `GebLean/Utilities/ERPackedBound.lean` (ER-level)

- Imports: `GebLean.Utilities.Tupling` (for
  `Nat.tuplePackCoef`, `Nat.tuplePack_le`),
  `GebLean.Utilities.ERArith` (for `mulN`, `expER`, `addN`,
  `natN`), `GebLean.LawvereERPolynomialBound` (for
  `PolyBound`).
- Namespace: `GebLean.ERMor1`, sub-namespace
  `ERMor1.PolyBound`.
- Public surface:
  - `ERMor1.tuplePackedBound`.
  - `@[simp] ERMor1.interp_tuplePackedBound`.
  - `ERMor1.PolyBound.ofTuplePackedBound`.
  - `ERMor1.tuplePackedBound_dominates`.

### §2.3 `GebLean/Utilities/ERSimultaneousBoundedRec.lean`

- Imports: `GebLean.Utilities.SimRec`,
  `GebLean.Utilities.ERTupling`,
  `GebLean.Utilities.ERPackedBound`.
- Namespace: `GebLean.ERMor1`, sub-namespace
  `ERMor1.PolyBound`.
- Public surface:
  - `ERMor1.packedBase`, `ERMor1.packedStep`,
    `ERMor1.packedStepCtx`.
  - `ERMor1.simultaneousBoundedRec`.
  - Named intermediate lemmas: `packedBase_interp_eq_tuplePack_simRecVec_zero`,
    `packedStep_interp_eq_tuplePack_step`,
    `packedRec_eq_tuplePack_simRecVec`,
    `packedBound_dominates_iter`, `packedBound_mono`.
  - `simultaneousBoundedRec_interp_correct`.
  - `ERMor1.PolyBound.ofSimultaneousBoundedRec`.

### §2.4 Tests

- `GebLeanTests/Utilities/SimRec.lean`.
- `GebLeanTests/Utilities/ERPackedBound.lean`.
- `GebLeanTests/Utilities/ERSimultaneousBoundedRec.lean`.

### §2.5 Imports at skeleton-creation time

Per the rule from step 1's plan: each new module's import
is registered in `GebLean.lean` (or `GebLeanTests.lean` for
tests) immediately when the skeleton file is created,
before any code is added to it.  This guarantees `lake
build` re-elaborates the new module on every subsequent
task, catching linter regressions in real time.

### §2.6 Dependency graph for downstream Path-2 modules

```text
SimRec.lean                  [step 2, this cycle]
   ↓                         (Nat-level only)
   ↓
ERPackedBound.lean           [step 2, this cycle]
   ↓                         (consumes step-1 Tupling)
   ↓
ERSimultaneousBoundedRec.lean  [step 2, this cycle]
   ↓                         (consumes ERTupling + SimRec
   ↓                          + ERPackedBound)
   ↓
ERAckermann.lean             [step 3]
   ↓
LawvereKSimMajorization.lean [step 4]
   ↓
LawvereKSimER.lean           [step 5]
```

## §3 `Nat`-level entities (`SimRec.lean`)

### §3.1 Definitions

```lean
namespace Nat

/-- Vector-valued simultaneous primitive recursion.
Returns the full `(k+1)`-vector of component values at
iteration `n` with parameter context `x : Fin a → ℕ`.

Step input convention (matching master design §3.2's
prose `g_j(n, x⃗, F_0(n, x⃗), …, F_k(n, x⃗))` and existing
`kSimStepContext` in
`Utilities/KSimSzudzikSimrec.lean:364`): slot 0 is the
iteration counter, slots 1..a are the parameter context,
slots a+1..a+k+1 are the previous-iteration component
values.  The step is therefore
`g_all : Fin (k+1) → (Fin (a + 1 + (k+1)) → ℕ) → ℕ`,
applied as
`g_all j (Fin.append (Fin.cons n x) prev)`.

Used to state `simultaneousBoundedRec_interp_correct`
per master design §3.2.  Realizes Tourlakis 2018
§0.1.0.7 (definition of K^sim hierarchy via simultaneous
primitive recursion); the pairing-based proof technique
is from Tourlakis 2018 §0.1.0.34.  -/
def simRecVec (k a : ℕ)
    (h_all : Fin (k + 1) → (Fin a → ℕ) → ℕ)
    (g_all : Fin (k + 1) →
      (Fin (a + 1 + (k + 1)) → ℕ) → ℕ) :
    ℕ → (Fin a → ℕ) → (Fin (k + 1) → ℕ)
  | 0,     x => fun j => h_all j x
  | n + 1, x => fun j =>
      g_all j (Fin.append (Fin.cons n x)
                (simRecVec k a h_all g_all n x))

/-- Component projection: `simRec` returns the j-th
component value at iteration `n`.  Plain `def` (not
`@[simp]`); promote if downstream proofs frequently
unfold it.  -/
def simRec (k a : ℕ)
    (h_all : Fin (k + 1) → (Fin a → ℕ) → ℕ)
    (g_all : Fin (k + 1) →
      (Fin (a + 1 + (k + 1)) → ℕ) → ℕ)
    (j : Fin (k + 1)) (n : ℕ) (x : Fin a → ℕ) : ℕ :=
  simRecVec k a h_all g_all n x j

end Nat
```

### §3.2 `@[simp]` recurrence lemmas

```lean
@[simp] theorem Nat.simRecVec_zero (k a : ℕ)
    (h_all : Fin (k + 1) → (Fin a → ℕ) → ℕ)
    (g_all : Fin (k + 1) →
      (Fin (a + 1 + (k + 1)) → ℕ) → ℕ)
    (x : Fin a → ℕ) (j : Fin (k + 1)) :
    Nat.simRecVec k a h_all g_all 0 x j = h_all j x := rfl

@[simp] theorem Nat.simRecVec_succ (k a : ℕ)
    (h_all : Fin (k + 1) → (Fin a → ℕ) → ℕ)
    (g_all : Fin (k + 1) →
      (Fin (a + 1 + (k + 1)) → ℕ) → ℕ)
    (n : ℕ) (x : Fin a → ℕ) (j : Fin (k + 1)) :
    Nat.simRecVec k a h_all g_all (n + 1) x j
      = g_all j (Fin.append (Fin.cons n x)
          (Nat.simRecVec k a h_all g_all n x))
        := rfl
```

### §3.3 Dominance helper

```lean
/-- If each base value is dominated by `componentBound`
at iteration 0, and the step preserves dominance
inductively, then every component value at every
iteration up to `n` is bounded.  Internal helper for
`simultaneousBoundedRec_interp_correct`'s dominance-
hypothesis discharge.  -/
theorem Nat.simRecVec_le_of_dominates
    (k a : ℕ)
    (h_all : Fin (k + 1) → (Fin a → ℕ) → ℕ)
    (g_all : Fin (k + 1) →
      (Fin (a + 1 + (k + 1)) → ℕ) → ℕ)
    (componentBound : ℕ → (Fin a → ℕ) → ℕ)
    (h_base : ∀ j x, h_all j x ≤ componentBound 0 x)
    (h_step : ∀ n x prev j,
       (∀ j', prev j' ≤ componentBound n x) →
       g_all j (Fin.append (Fin.cons n x) prev)
         ≤ componentBound (n + 1) x)
    (n : ℕ) (x : Fin a → ℕ) (j : Fin (k + 1)) :
    Nat.simRecVec k a h_all g_all n x j
      ≤ componentBound n x
```

Proof: induction on `n`.  Base case dispatches via
`h_base`.  Step case: applies `h_step` to the inductive
hypothesis (which gives that every component at iteration
`n` is dominated).

## §4 ER-side packed bound (`ERPackedBound.lean`)

### §4.1 `ERMor1.tuplePackedBound`

```lean
namespace GebLean
namespace ERMor1

/-- ER named composite for the packed-state value bound:
`tuplePackCoef k * (componentBound + 1)^(2^k)`.  Used by
`simultaneousBoundedRec` (master design §3.2) as the
single-output `boundedRec` bound when packing a
`(k+1)`-tuple of bounded component values via
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

end ERMor1
end GebLean
```

### §4.2 `@[simp]` interp lemma

```lean
@[simp] theorem ERMor1.interp_tuplePackedBound (k : ℕ)
    {a : ℕ} (componentBound : ERMor1 a) (ctx : Fin a → ℕ) :
    (ERMor1.tuplePackedBound k componentBound).interp ctx
      = Nat.tuplePackCoef k *
          (componentBound.interp ctx + 1) ^ (2 ^ k)
```

Proof: `simp only [tuplePackedBound, ERMor1.interp_comp,
ERMor1.interp_mulN, ERMor1.interp_expER,
ERMor1.interp_addN, ERMor1.interp_natN]` plus
`Matrix.cons_val_*` lemmas as needed (similar to step 1
Task 8's interp proofs).

### §4.3 `PolyBound.ofTuplePackedBound`

```lean
namespace PolyBound

/-- PolyBound for `tuplePackedBound k componentBound`.
Given `pb : PolyBound componentBound`, produces:

- `degree = pb.degree * 2^k`
- `coefficient = tuplePackCoef k * (pb.coefficient + pb.constant + 1)^(2^k)`
- `constant = 0`

Derivation: substituting `pb`'s formula
`componentBound.interp ctx ≤ pb.coefficient * X^pb.degree + pb.constant`
(where `X = maxCtx ctx + 1`) into
`tuplePackCoef k * (componentBound.interp ctx + 1)^(2^k)` and
applying `(A * X^d + B + 1) ≤ (A + B + 1) * X^d` for `X ≥ 1`,
we get the formula above.  Master design §3.2; §15.13
punch-list.  -/
def ofTuplePackedBound (k : ℕ) {a : ℕ}
    {componentBound : ERMor1 a}
    (pb : PolyBound componentBound) :
    PolyBound (ERMor1.tuplePackedBound k componentBound)

end PolyBound
```

Proof: rewrite via `interp_tuplePackedBound`, apply
`pb.bounds` to bound the inner `componentBound.interp`,
expand via the algebraic substitution above, simplify.

### §4.4 `tuplePackedBound_dominates`

```lean
/-- If each component of a `(k+1)`-vector `v` is bounded
by `componentBound.interp ctx`, then `Nat.tuplePack k v`
is bounded by `(tuplePackedBound k componentBound).interp ctx`.
This is the per-iteration bound feeding into
`boundedRec_eq_natRec_of_bounded`'s dominance hypothesis
inside `simultaneousBoundedRec_interp_correct`.  Master
design §3.2.  -/
theorem ERMor1.tuplePackedBound_dominates
    (k : ℕ) {a : ℕ} (componentBound : ERMor1 a)
    (v : Fin (k + 1) → ℕ) (ctx : Fin a → ℕ)
    (h_components : ∀ j, v j ≤ componentBound.interp ctx) :
    Nat.tuplePack k v
      ≤ (ERMor1.tuplePackedBound k componentBound).interp ctx
```

Proof: rewrite via `interp_tuplePackedBound`; apply step
1's `Nat.tuplePack_le k v`; bound the resulting
`(maxCtx_v + 1)^(2^k)` by `(componentBound.interp ctx + 1)^(2^k)`
using `h_components` and monotonicity.

## §5 ER-side recursion (`ERSimultaneousBoundedRec.lean`)

### §5.1 Definitional helpers

```lean
namespace GebLean
namespace ERMor1

/-- Initial packed state for `simultaneousBoundedRec`:
applies the `(k+1)` bases and packs the resulting vector
via `Nat.tuplePack`.  Master design §3.2 step 3. -/
def packedBase (k a : ℕ)
    (h : Fin (k + 1) → ERMor1 a) : ERMor1 a :=
  ERMor1.comp (ERMor1.tuplePack k) h

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

/-- Packed step function: takes the packed previous
state and produces the packed next state.  Each
component step `g j` is evaluated on the unpacked
context, results are repacked via `Nat.tuplePack`.
Master design §3.2 step 1. -/
def packedStep (k a : ℕ)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    ERMor1 (a + 2) :=
  ERMor1.comp (ERMor1.tuplePack k)
    (fun j : Fin (k + 1) =>
      ERMor1.comp (g j) (ERMor1.packedStepCtx k a))

end ERMor1
end GebLean
```

### §5.2 `ERMor1.simultaneousBoundedRec`

```lean
/-- Multi-output bounded simultaneous recursion in ER.
Realizes Tourlakis 2018 §0.1.0.34 (the proof technique:
closure of E^2 under simultaneous bounded recursion via
pairing-based pack-and-unpack; §0.1.0.35 is the higher-
level corollary for `n ≥ 2`).  Master design §3.2.

The implementation packs the `(k+1)`-component state
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

### §5.3 Named intermediate lemmas

```lean
/-- Base case: at iteration 0, the packed initial state
equals `Nat.tuplePack k` applied to the bases. -/
theorem packedBase_interp_eq_tuplePack_simRecVec_zero
    (k a : ℕ) (h : Fin (k + 1) → ERMor1 a)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (x : Fin a → ℕ) :
    (ERMor1.packedBase k a h).interp x
      = Nat.tuplePack k
          (Nat.simRecVec k a (fun j' => (h j').interp)
            (fun j' => (g j').interp) 0 x)

/-- Step case: applying `packedStep` to a packed state
that equals `Nat.tuplePack k (Nat.simRecVec ... n x)`
yields `Nat.tuplePack k (Nat.simRecVec ... (n+1) x)`.
The inner `boundedRec` step input convention is
`(counter, packed_prev, params)`, so the assembled
context is `Fin.cons n (Fin.cons prev_packed x)`. -/
theorem packedStep_interp_eq_tuplePack_step
    (k a : ℕ)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (n : ℕ) (x : Fin a → ℕ) (prev_packed : ℕ)
    (h_prev :
      prev_packed = Nat.tuplePack k
        (Nat.simRecVec k a
          (fun j' => fun y => 0)  -- bases unused at step
          (fun j' => (g j').interp) n x)) :
    (ERMor1.packedStep k a g).interp
        (Fin.cons n (Fin.cons prev_packed x))
      = Nat.tuplePack k
          (Nat.simRecVec k a (fun j' => fun y => 0)
            (fun j' => (g j').interp) (n + 1) x)

/-- Main intermediate: the packed `boundedRec` output at
iteration `n` equals `Nat.tuplePack k (Nat.simRecVec ... n x)`,
under the dominance hypothesis. -/
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
            (fun j' => (g j').interp) n x)

/-- Dominance hypothesis discharge: under
`h_dominates`, the packed state at iteration `m ≤ n` is
bounded by `tuplePackedBound k componentBound`'s interp.
Used to apply `boundedRec_eq_natRec_of_bounded`. -/
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
          (Fin.cons m x)

/-- Monotonicity hypothesis discharge: if
`componentBound` is monotone in the iteration counter,
so is `tuplePackedBound k componentBound`. -/
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
          (Fin.cons n x)
```

### §5.4 `simultaneousBoundedRec_interp_correct`

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
        (fun j' => (g j').interp) n x i
```

Proof outline:

1. Unfold `simultaneousBoundedRec` and `interp_comp`,
   `interp_tupleAt`.  Note: a `change` step or
   `Matrix.cons_val_zero` may be needed to collapse the
   `fun _ : Fin 1 => packedRec.interp ctx` lambda into the
   form `interp_tupleAt` expects:

   ```lean
   simp only [ERMor1.simultaneousBoundedRec,
     ERMor1.interp_comp, ERMor1.interp_tupleAt,
     Matrix.cons_val_zero]
   ```

2. Apply `packedRec_eq_tuplePack_simRecVec` to identify
   the inner `boundedRec` output.
3. Apply `Nat.tupleAt_tuplePack` (step 1) to extract the
   `i`-th component.

If `simp only` does not reduce the goal to a direct
`interp` call, add `change` to align it:

```lean
change Nat.tupleAt k
          ((boundedRec ...).interp (Fin.cons n x)) i = ...
```

The proof is a clean chain: unfold → rewrite → extract.

### §5.5 `PolyBound.ofSimultaneousBoundedRec`

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
                   (pb_bound.coefficient
                      + pb_bound.constant + 1)^(2^k)`
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
      ((ERMor1.simultaneousBoundedRec k a h g componentBound)
        i)

end PolyBound
```

Proof of `bounds`: chain
`component ≤ packedRec ≤ tuplePackedBound interp ≤ poly bound`,
using `Nat.tupleAt_le`, `interp_boundedRec_le_bound`, and
`(ofTuplePackedBound k pb_bound).bounds`.  Use
`Nat.le_trans` chaining (not `omega`, which cannot close a
non-linear `^`-bearing goal):

```lean
def ofSimultaneousBoundedRec ... where
  ...
  bounds := fun ctx => by
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
```

## §6 Tests

### §6.1 `GebLeanTests/Utilities/SimRec.lean`

Smoke `#guard`s and a non-trivial 2-component example
(bounded values, ≤ tens):

```lean
import GebLean.Utilities.SimRec

/-! # Tests for `Nat.simRecVec`, `Nat.simRec`. -/

open Nat

-- Identity-case smoke (k = 0): 1-component "simrec"
-- reduces to ordinary recursion.
#guard simRecVec 0 0 (fun _ _ => 5) (fun _ _ => 7) 0
         (fun _ => 0) 0 = 5

-- A non-trivial 2-component swap example: f_0(0) = 1,
-- f_1(0) = 2, step swaps the components.  Values stay
-- in {1, 2} regardless of n — bounded.
example :
    Nat.simRecVec 1 0
      (fun j _ => match j with | ⟨0, _⟩ => 1 | ⟨1, _⟩ => 2)
      (fun j ctx => match j with
        | ⟨0, _⟩ => ctx ⟨2, by decide⟩  -- prev component 1
        | ⟨1, _⟩ => ctx ⟨1, by decide⟩) -- prev component 0
      5 (fun _ => 0) = ![1, 2] := by ...
```

### §6.2 `GebLeanTests/Utilities/ERPackedBound.lean`

PolyBound shape verification only (per the Gödel-numbering
test discipline from step 1):

```lean
import GebLean.Utilities.ERPackedBound

/-! # Tests for `ERMor1.tuplePackedBound`,
# `ERMor1.PolyBound.ofTuplePackedBound`. -/

open GebLean

-- PolyBound shape at k = 1 with a trivial componentBound
-- (e.g., `ERMor1.zeroN`).  Struct field access only.
example :
    (ERMor1.PolyBound.ofTuplePackedBound 1
       (ERMor1.PolyBound.ofZeroN 0)).degree = 0 := rfl
```

### §6.3 `GebLeanTests/Utilities/ERSimultaneousBoundedRec.lean`

```lean
import GebLean.Utilities.ERSimultaneousBoundedRec

/-! # Tests for `ERMor1.simultaneousBoundedRec`,
# `ERMor1.PolyBound.ofSimultaneousBoundedRec`.

Per the test discipline from
`GebLeanTests/Utilities/ERTupling.lean` (Gödel-numbering
kernel-reduction is impractical), this file restricts
runtime checks to small-k smoke and PolyBound shape.
Higher-k correctness rests on
`simultaneousBoundedRec_interp_correct`. -/

open GebLean

-- PolyBound shape at k = 1 (no `.interp` evaluation).
example :
    (ERMor1.PolyBound.ofSimultaneousBoundedRec 1 0
       (ERMor1.PolyBound.ofZeroN 1) ⟨0, by decide⟩).degree
      = 0 := rfl
```

### §6.4 Test discipline reminders

- `#guard` permitted at the Nat level (`SimRec.lean`):
  fast kernel reduction.
- `#guard` on ER `.interp` permitted only at trivial
  arity and tiny inputs.
- Higher-arity ER correctness proven universally via
  `simultaneousBoundedRec_interp_correct`.
- All numeric values kept in the tens (preferably) per
  the unary-arithmetic caveat.
- No Plausible.

## §7 Citations

Per CLAUDE.md transcription discipline.

### §7.1 Nat-side entities

- **`Nat.simRecVec`, `Nat.simRec`** — Tourlakis 2018
  §0.1.0.7 (definition of K^sim hierarchy via
  simultaneous primitive recursion); master design §3.2.
- **`Nat.simRecVec_zero`, `Nat.simRecVec_succ`** — direct
  recurrence unfolding; master design §3.2.
- **`Nat.simRecVec_le_of_dominates`** — auxiliary
  dominance helper; master design §3.2 (consumed by
  `simultaneousBoundedRec_interp_correct`'s hypothesis
  discharge).

### §7.2 ER-side packed-bound entities

- **`ERMor1.tuplePackedBound`** — master design §3.2;
  underlying `Nat.tuplePack_le` from step 1 (Tourlakis
  2018 §0.1.0.34, p. 14).
- **`ERMor1.interp_tuplePackedBound`** — master design
  §3.2.
- **`ERMor1.PolyBound.ofTuplePackedBound`** — master
  design §3.2 + §15.13 punch-list.
- **`ERMor1.tuplePackedBound_dominates`** — auxiliary;
  master design §3.2.

### §7.3 ER-side recursion entities

- **`ERMor1.packedBase`, `ERMor1.packedStep`,
  `ERMor1.packedStepCtx`** — auxiliary named composites;
  master design §3.2 implementation outline.
- **`ERMor1.simultaneousBoundedRec`** — Tourlakis 2018
  §0.1.0.34 (E^2 closed under simultaneous bounded
  recursion via the pairing-based pack-and-unpack proof
  technique; §0.1.0.35 is the higher-level corollary
  generalizing to E^{n+1} for `n ≥ 2`); master design
  §3.2; underlying single-output `ERMor1.boundedRec` in
  `Utilities/ERArith.lean`.
- **`packedBase_interp_eq_tuplePack_simRecVec_zero`,
  `packedStep_interp_eq_tuplePack_step`,
  `packedRec_eq_tuplePack_simRecVec`,
  `packedBound_dominates_iter`, `packedBound_mono`** —
  auxiliary intermediate lemmas; master design §3.2.
- **`simultaneousBoundedRec_interp_correct`** — Tourlakis
  2018 §0.1.0.34 (correctness implicit in the
  pairing-based closure proof; §0.1.0.35 is the
  higher-level corollary); master design §3.2; underlying
  `boundedRec_eq_natRec_of_bounded` in
  `Utilities/ERArith.lean:2193`.
- **`ERMor1.PolyBound.ofSimultaneousBoundedRec`** —
  master design §3.2 + §15.13 punch-list.

## §8 Open follow-ups and risks

### §8.1 Lean ergonomic risks

1. **`packedStepCtx`'s slot routing.** The
   `Fin (a + 1 + (k + 1))` decomposition into
   `(counter, params, prev_vector)` for the outer
   simRecVec convention, mapped to the inner
   boundedRec convention `(counter, packed_prev, params)`,
   requires explicit `Fin` arithmetic for the `v - a`
   calculation in the prev branch.  Factor into the named
   `packedStepCtx` helper (per §5.1) and prove its interp
   lemma cleanly before use.  Fallback: explicit
   `if-then-else` with `omega` for bounds.

2. **`packedRec_eq_tuplePack_simRecVec` induction.**
   The step case requires:
   - Unpacking the previous packed state via
     `Nat.tupleAt` (recovering `Nat.simRecVec ... n x`
     by step 1's `tupleAt_tuplePack`).
   - Applying each `g j` on the assembled context.
   - Repacking via `Nat.tuplePack`.

   Slot conventions must align.  The implementer should
   isolate the slot-alignment lemma (`packedStep_interp_eq_tuplePack_step`)
   and prove it before the main induction.

3. **`tuplePackedBound`'s `expER` use.** `2^k`
   appearing as a literal large `Nat` for `k ≥ 4` makes
   `decide`-based smoke tests slow; tests at `k ≤ 2`
   only.

4. **Tower-height arithmetic** — documented property,
   not a separate lemma in step 2.  If step 4 needs it
   as an explicit theorem, add a follow-up to
   `ERPackedBound.lean`.

### §8.2 Master-design forward constraints

- The `componentBound`-with-monotonicity hypothesis
  matches `boundedRec_eq_natRec_of_bounded`'s shape.
  Step 5 (kToER) discharges it for the level-2 case
  using `A_2^r`'s monotonicity (master design §3.4).

- The PolyBound builder's coefficient is determined
  uniquely by step 1's `Nat.tuplePack_le` plus the
  algebraic substitution in §4.3.  No design freedom.

### §8.3 Test runtime

Per step 1's lesson, ER-side `.interp` `#guard`s
restricted to `k = 0` with tiny inputs.  Higher-arity
correctness rests on the universal proof.  All numeric
values in tests kept ≤ tens to avoid unary-arithmetic
slowdown.

### §8.4 `boundedRec_eq_natRec_of_bounded` consumption

The existing `ERMor1.boundedRec_eq_natRec_of_bounded`
(in `Utilities/ERArith.lean:2193`) is the conditional
correctness primitive.  Its hypothesis form (pointwise
dominance up to `n` plus monotonicity) shapes step 2's
`simultaneousBoundedRec_interp_correct` hypothesis form.

### §8.5 `@[simp]` on `Nat.simRec`

Initially kept as plain `def`.  If downstream proofs
frequently `unfold Nat.simRec`, promote to `@[simp]` in
a follow-up.

### §8.6 Vector PolyBound representation

Currently per-component
(`ofSimultaneousBoundedRec _ i : PolyBound (... i)`).
If implementation reveals consumers consistently want a
vector form (a `Fin (k+1) → PolyBound`), refactor to
vector PolyBounds without changing the literature
contract.

## §9 Implementation order

Per the import-at-skeleton-creation rule and the
step-1-lesson on forced re-elaboration, each task ends
with a forced re-elaboration check
(`rm .olean && lake build <Module>`) before commit.

1. `GebLean/Utilities/SimRec.lean`:
   1. Skeleton + register import in `GebLean.lean`.
   2. `Nat.simRecVec`, `Nat.simRec`.
   3. `@[simp]` recurrence lemmas.
   4. `Nat.simRecVec_le_of_dominates`.
2. `GebLeanTests/Utilities/SimRec.lean`: §6.1 (Nat-level
   smoke + 2-component example).
3. `GebLean/Utilities/ERPackedBound.lean`:
   1. Skeleton + register import in `GebLean.lean`.
   2. `ERMor1.tuplePackedBound`.
   3. `@[simp] ERMor1.interp_tuplePackedBound`.
   4. `ERMor1.PolyBound.ofTuplePackedBound`.
   5. `ERMor1.tuplePackedBound_dominates`.
4. `GebLeanTests/Utilities/ERPackedBound.lean`: §6.2
   (PolyBound shape).
5. `GebLean/Utilities/ERSimultaneousBoundedRec.lean`:
   1. Skeleton + register import in `GebLean.lean`.
   2. Definitional helpers (`packedBase`,
      `packedStepCtx`, `packedStep`).
   3. `ERMor1.simultaneousBoundedRec`.
   4. Named intermediate lemmas
      (`packedBase_interp_eq_tuplePack_simRecVec_zero`,
      `packedStep_interp_eq_tuplePack_step`,
      `packedRec_eq_tuplePack_simRecVec`,
      `packedBound_dominates_iter`, `packedBound_mono`).
   5. `simultaneousBoundedRec_interp_correct`.
   6. `ERMor1.PolyBound.ofSimultaneousBoundedRec`.
6. `GebLeanTests/Utilities/ERSimultaneousBoundedRec.lean`:
   §6.3 (small-k smoke + PolyBound shape).
7. **Citation cross-check** (per the rule from step 1):
   verify each docstring contains the §7-listed
   citation verbatim.
8. **Final verification:** forced re-elaboration of all
   six new modules; `lake build`, `lake test`,
   `markdownlint-cli2` clean; banned-word grep clean;
   whitespace check clean.
9. Update `.session/workstreams/er-ksim2-equiv-via-urm.md`
   with the cycle-2 outcome.

## §10 Success criteria

- All six new modules (3 implementation + 3 test) compile
  with no warnings (no `sorry`, `admit`, no banned
  words, no Classical / noncomputable / axiom).
- `simultaneousBoundedRec_interp_correct` and
  `ofSimultaneousBoundedRec` proven without holes.
- Forced re-elaboration of each new module clean.
- Full `lake build` and `lake test` clean.
- `markdownlint-cli2` clean on this spec and any new
  research-doc updates.
- All entities carry the §7-listed literature citations
  in their docstrings.
- All four imports registered in `GebLean.lean` /
  `GebLeanTests.lean` at skeleton-creation time.
- The `.session/workstreams/er-ksim2-equiv-via-urm.md`
  is updated with cycle-2 progress.
