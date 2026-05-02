import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Fixed-length k-tuple Szudzik pairing

Foundational tupling infrastructure for the ER ↔ K^sim_2
categorical equivalence.  Realizes Tourlakis 2018
§0.1.0.34, p. 14's k-tuple coding scheme
`[[z_1,…,z_k]]^{(k)}` with Szudzik pairing
(`Nat.pair x y = if x < y then y² + x else x² + x + y`)
replacing Cantor's `J = (x+y)² + x`.  Both are bijections
`ℕ × ℕ → ℕ` polynomially bounded by `(x+y+1)²`.

The parameter `k : ℕ` of `tuplePack` and `tupleAt` indexes
a tuple of length `k + 1`; using `Fin (k+1)` makes the
empty tuple unrepresentable, since the bijection
`(Fin (k+1) → ℕ) ↔ ℕ` is only meaningful for non-empty
products.

See `docs/superpowers/specs/2026-05-02-step-1-er-tupling-design.md`
and master design §3.1 in
`docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
-/

namespace Nat

/-- Pack a `(k+1)`-tuple of naturals into a single natural
via iterated left-associated Szudzik pairing.  Realizes
Tourlakis 2018 §0.1.0.34, p. 14's `[[z_1,…,z_{k+1}]]^{(k+1)}`
(with Szudzik replacing Cantor's J).  See master design
§3.1. -/
def tuplePack : (k : ℕ) → (Fin (k+1) → ℕ) → ℕ
  | 0,     v => v 0
  | k + 1, v =>
      Nat.pair (tuplePack k (Fin.init v))
        (v (Fin.last (k+1)))

/-- Extract the `i`-th component from a packed
`(k+1)`-tuple.  Inverse of `tuplePack`.  Realizes Tourlakis
2018 §0.1.0.34, p. 14's `Π^{k+1}_i` projections (with
index orientation matched to the left-fold recurrence;
`Nat.unpair.fst` plays the role of Tourlakis's K and
`Nat.unpair.snd` plays L).  See master design §3.1. -/
def tupleAt : (k : ℕ) → ℕ → Fin (k+1) → ℕ
  | 0,     n, _ => n
  | k + 1, n, i =>
      Fin.lastCases (motive := fun _ : Fin (k+2) => ℕ)
        ((Nat.unpair n).2)
        (fun j : Fin (k+1) => tupleAt k (Nat.unpair n).1 j)
        i

/-- Closed-form coefficient witnessing the polynomial
bound `tuplePack k v ≤ tuplePackCoef k * (M+1)^(2^k)`,
where `M = sup v` over `Fin (k+1)`.  Recurrence derived
from `Nat.pair_le_sq` per master design §3.1. -/
def tuplePackCoef : ℕ → ℕ
  | 0     => 1
  | k + 1 => (tuplePackCoef k + 2)^2

@[simp] theorem tuplePack_zero (v : Fin 1 → ℕ) :
    tuplePack 0 v = v 0 := rfl

@[simp] theorem tuplePack_succ (k : ℕ)
    (v : Fin (k+2) → ℕ) :
    tuplePack (k+1) v
      = Nat.pair (tuplePack k (Fin.init v))
          (v (Fin.last (k+1))) := rfl

@[simp] theorem tupleAt_zero (n : ℕ) (i : Fin 1) :
    tupleAt 0 n i = n := rfl

/-- `tupleAt` reduction at the last index: peels one
`Nat.unpair` step on the right. -/
@[simp] theorem tupleAt_succ_last (k n : ℕ) :
    tupleAt (k+1) n (Fin.last (k+1))
      = (Nat.unpair n).2 := by
  simp [tupleAt, Fin.lastCases_last]

/-- `tupleAt` reduction at a non-last index: peels one
`Nat.unpair` step on the left and recurses at depth `k`. -/
@[simp] theorem tupleAt_succ_castSucc (k n : ℕ)
    (j : Fin (k+1)) :
    tupleAt (k+1) n j.castSucc
      = tupleAt k (Nat.unpair n).1 j := by
  simp [tupleAt, Fin.lastCases_castSucc]

/-- Every component extracted from a packed natural is
bounded by the packed natural itself.  Mirrors existing
`Nat.seqAt_le` in `Utilities/SzudzikSeq.lean`; underlying
mathlib lemmas: `Nat.unpair_left_le`,
`Nat.unpair_right_le`. -/
theorem tupleAt_le : ∀ (k n : ℕ) (i : Fin (k+1)),
    tupleAt k n i ≤ n
  | 0,     n, _ => by
      simp [tupleAt]
  | k + 1, n, i => by
      refine Fin.lastCases ?_ ?_ i
      · simp [tupleAt, Fin.lastCases_last]
        exact Nat.unpair_right_le n
      · intro j
        simp [tupleAt, Fin.lastCases_castSucc]
        exact le_trans (tupleAt_le k (Nat.unpair n).1 j)
          (Nat.unpair_left_le n)

/-- Round-trip: extracting component `i` from a packed
tuple returns the original component.  Realizes Tourlakis
2018 §0.1.0.34, p. 14's
`Π^k_i [[z_1,…,z_k]]^{(k)} = z_i`. -/
theorem tupleAt_tuplePack :
    ∀ (k : ℕ) (v : Fin (k+1) → ℕ) (i : Fin (k+1)),
      tupleAt k (tuplePack k v) i = v i
  | 0,     v, i => by
      simp only [tupleAt_zero]
      exact congrArg v (Subsingleton.elim _ i)
  | k + 1, v, i => by
      refine Fin.lastCases ?_ ?_ i
      · simp only [tuplePack_succ, tupleAt_succ_last,
              Nat.unpair_pair]
      · intro j
        simp only [tuplePack_succ, tupleAt_succ_castSucc,
              Nat.unpair_pair]
        exact tupleAt_tuplePack k (Fin.init v) j

/-- Round-trip: packing the components extracted from a
packed natural returns the original natural.  Realizes the
inverse round-trip implicit in Tourlakis 2018 §0.1.0.34,
p. 14's bijection (each `z` recovers from its projections
under `[[·]]^{(k)}`). -/
theorem tuplePack_tupleAt :
    ∀ (k n : ℕ),
      tuplePack k (tupleAt k n) = n
  | 0,     n => by
      simp only [tuplePack_zero, tupleAt_zero]
  | k + 1, n => by
      simp only [tuplePack_succ, tupleAt_succ_last]
      have h_init :
          Fin.init (tupleAt (k+1) n)
            = tupleAt k (Nat.unpair n).1 := by
        funext j
        show tupleAt (k+1) n j.castSucc
          = tupleAt k (Nat.unpair n).1 j
        exact tupleAt_succ_castSucc k n j
      rw [h_init]
      rw [tuplePack_tupleAt k (Nat.unpair n).1]
      exact Nat.pair_unpair n

end Nat
