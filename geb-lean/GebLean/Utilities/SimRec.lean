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

/-- Vector-valued simultaneous primitive recursion.
Returns the full `(k + 1)`-vector of component values at
iteration `n` with parameter context `x : Fin a → ℕ`.
The step is applied as
`g_all j (Fin.append (Fin.cons n x) prev)`; see the
module docstring for the slot-layout convention.

Realizes Tourlakis 2018 §0.1.0.7 (definition of K^sim
hierarchy via simultaneous primitive recursion); the
pairing-based proof technique is from Tourlakis 2018
§0.1.0.34.  Master design §3.2. -/
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
component value at iteration `n`.  Master design §3.2. -/
def simRec (k a : ℕ)
    (h_all : Fin (k + 1) → (Fin a → ℕ) → ℕ)
    (g_all : Fin (k + 1) →
      (Fin (a + 1 + (k + 1)) → ℕ) → ℕ)
    (j : Fin (k + 1)) (n : ℕ) (x : Fin a → ℕ) : ℕ :=
  simRecVec k a h_all g_all n x j

/-- Recurrence at zero; master design §3.2. -/
@[simp] theorem simRecVec_zero (k a : ℕ)
    (h_all : Fin (k + 1) → (Fin a → ℕ) → ℕ)
    (g_all : Fin (k + 1) →
      (Fin (a + 1 + (k + 1)) → ℕ) → ℕ)
    (x : Fin a → ℕ) (j : Fin (k + 1)) :
    simRecVec k a h_all g_all 0 x j = h_all j x := rfl

/-- Recurrence at successor; master design §3.2. -/
@[simp] theorem simRecVec_succ (k a : ℕ)
    (h_all : Fin (k + 1) → (Fin a → ℕ) → ℕ)
    (g_all : Fin (k + 1) →
      (Fin (a + 1 + (k + 1)) → ℕ) → ℕ)
    (n : ℕ) (x : Fin a → ℕ) (j : Fin (k + 1)) :
    simRecVec k a h_all g_all (n + 1) x j
      = g_all j (Fin.append (Fin.cons n x)
          (simRecVec k a h_all g_all n x))
        := rfl

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
         ≤ componentBound (n + 1) x)
    (n : ℕ) :
    ∀ (x : Fin a → ℕ) (j : Fin (k + 1)),
      simRecVec k a h_all g_all n x j
        ≤ componentBound n x := by
  induction n with
  | zero =>
      intro x j
      simp only [simRecVec_zero]
      exact h_base j x
  | succ n ih =>
      intro x j
      simp only [simRecVec_succ]
      apply h_step n x (simRecVec k a h_all g_all n x) j
      intro j'
      exact ih x j'

end Nat
