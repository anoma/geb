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

/-- Initial packed state for `simultaneousBoundedRec`:
applies the `(k + 1)` bases and packs the resulting
vector via `Nat.tuplePack`.  Master design §3.2 step 3. -/
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
  state).  Master design §3.2. -/
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
context (counter + parameters + previous-component
vector), results are repacked via `Nat.tuplePack`.
Master design §3.2 step 1. -/
def packedStep (k a : ℕ)
    (g : Fin (k + 1) → ERMor1 (a + 1 + (k + 1))) :
    ERMor1 (a + 2) :=
  ERMor1.comp (ERMor1.tuplePack k)
    (fun j : Fin (k + 1) =>
      ERMor1.comp (g j) (ERMor1.packedStepCtx k a))

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
named-composite discipline". -/
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
    ERMor1.interp_tuplePack]
  rfl

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

/-- Interp of `packedStepCtx` at each slot of the
`Fin (a + 1 + (k + 1))`-context.

Outer slot 0 routes to the inner counter (slot 0).
Outer slots 1..a (parameter indices 0..a-1) route to
inner slots 2..a+1 (the parameters).  Outer slots
a+1..a+k+1 (prev indices 0..k) route via `Nat.tupleAt k`
extraction from inner slot 1 (the packed previous
state).  Master design §3.2. -/
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
      change (ERMor1.proj (k := a + 2) 0).interp _
        = Fin.append (Fin.cons n x)
            (Nat.tupleAt k prev_packed) ⟨0, _⟩
      rw [ERMor1.interp_proj]
      have h_cast :
          (⟨0, by omega⟩ : Fin (a + 1 + (k + 1)))
            = Fin.castAdd (k + 1)
                (⟨0, by omega⟩ : Fin (a + 1)) := by
        apply Fin.ext; rfl
      rw [h_cast, Fin.append_left]
      rfl
  | s + 1, h_in =>
      by_cases h_param : s < a
      · have h_eq :
            ERMor1.packedStepCtx k a ⟨s + 1, h_in⟩
              = ERMor1.proj ⟨s + 2, by omega⟩ := by
          change (if h_param : s < a then
                    ERMor1.proj (k := a + 2)
                      ⟨s + 2, by omega⟩
                  else
                    ERMor1.comp
                      (ERMor1.tupleAt k
                        ⟨s - a, by omega⟩)
                      ![ERMor1.proj 1])
                = ERMor1.proj ⟨s + 2, by omega⟩
          rw [dif_pos h_param]
        rw [h_eq, ERMor1.interp_proj]
        have h_cast :
            (⟨s + 1, h_in⟩ : Fin (a + 1 + (k + 1)))
              = Fin.castAdd (k + 1)
                  (⟨s + 1, by omega⟩ : Fin (a + 1)) := by
          apply Fin.ext; rfl
        rw [h_cast, Fin.append_left]
        have h1 :
            (⟨s + 2, by omega⟩ : Fin (a + 1 + 1))
              = Fin.succ
                  (⟨s + 1, by omega⟩ : Fin (a + 1)) := by
          apply Fin.ext; rfl
        have h2 :
            (⟨s + 1, by omega⟩ : Fin (a + 1))
              = Fin.succ (⟨s, h_param⟩ : Fin a) := by
          apply Fin.ext; rfl
        rw [h1, Fin.cons_succ, h2, Fin.cons_succ,
          Fin.cons_succ]
      · push_neg at h_param
        have h_eq :
            ERMor1.packedStepCtx k a ⟨s + 1, h_in⟩
              = ERMor1.comp
                  (ERMor1.tupleAt k ⟨s - a, by omega⟩)
                  ![ERMor1.proj 1] := by
          change (if h_param : s < a then
                    ERMor1.proj (k := a + 2)
                      ⟨s + 2, by omega⟩
                  else
                    ERMor1.comp
                      (ERMor1.tupleAt k
                        ⟨s - a, by omega⟩)
                      ![ERMor1.proj 1])
                = ERMor1.comp
                    (ERMor1.tupleAt k ⟨s - a, by omega⟩)
                    ![ERMor1.proj 1]
          rw [dif_neg (Nat.not_lt.mpr h_param)]
        rw [h_eq, ERMor1.interp_comp,
          ERMor1.interp_tupleAt]
        have h_proj1 :
            (![ERMor1.proj (k := a + 2) 1] 0).interp
                (Fin.cons n (Fin.cons prev_packed x))
              = prev_packed := by
          rfl
        rw [h_proj1]
        have h_cast :
            (⟨s + 1, h_in⟩ : Fin (a + 1 + (k + 1)))
              = Fin.natAdd (a + 1)
                  ⟨s - a, by omega⟩ := by
          apply Fin.ext
          change s + 1 = (a + 1) + (s - a)
          omega
        rw [h_cast, Fin.append_right]

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
    (ERMor1.packedStep k a g).interp
        (Fin.cons n (Fin.cons
          (Nat.tuplePack k
            (Nat.simRecVec k a (fun j' => (h j').interp)
              (fun j' => (g j').interp) n x))
          x))
      = Nat.tuplePack k
          (Nat.simRecVec k a (fun j' => (h j').interp)
            (fun j' => (g j').interp) (n + 1) x) := by
  change (ERMor1.comp (ERMor1.tuplePack k) _).interp _ = _
  rw [ERMor1.interp_comp, ERMor1.interp_tuplePack]
  congr 1
  funext j
  rw [Nat.simRecVec_succ]
  rw [ERMor1.interp_comp]
  congr 1
  funext i
  rw [ERMor1.interp_packedStepCtx]
  congr 1
  funext j'
  exact Nat.tupleAt_tuplePack k _ j'

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
      exact
        ERMor1.packedBase_interp_eq_tuplePack_simRecVec_zero
          k a h g x
  | succ m ih =>
      change (ERMor1.packedStep k a g).interp
          (Fin.cons m (Fin.cons _ x)) = _
      rw [ih]
      exact ERMor1.packedStep_interp_eq_tuplePack_step
        k a h g m x

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
  rw [ERMor1.boundedRec_eq_natRec_of_bounded
        (ERMor1.packedBase k a h)
        (ERMor1.packedStep k a g)
        (ERMor1.tuplePackedBound k componentBound)
        n x ?h_dom ?h_mon]
  · exact ERMor1.Nat_rec_packed_eq_tuplePack_simRecVec
      k a h g n x
  case h_dom =>
    intro j h_j_le_n
    rw [ERMor1.Nat_rec_packed_eq_tuplePack_simRecVec
          k a h g j x]
    exact ERMor1.packedBound_dominates_iter
      k a h g componentBound n x j h_j_le_n h_dominates
  case h_mon =>
    intro j h_j_le_n
    exact ERMor1.packedBound_mono
      k a componentBound n x h_mono j h_j_le_n

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
  exact Nat.tupleAt_tuplePack k _ i

end ERMor1
end GebLean
