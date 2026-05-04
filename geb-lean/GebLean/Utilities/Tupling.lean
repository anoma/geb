import Mathlib.Data.Nat.Pairing
import Mathlib.Data.Fin.Tuple.Basic
import GebLean.Utilities.ComputationalComplexity

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
def tuplePack : (k : ℕ) → (Fin (k + 1) → ℕ) → ℕ
  | 0,     v => v 0
  | k + 1, v =>
      Nat.pair (tuplePack k (Fin.init v))
        (v (Fin.last (k + 1)))

/-- Extract the `i`-th component from a packed
`(k+1)`-tuple.  Inverse of `tuplePack`.  Realizes Tourlakis
2018 §0.1.0.34, p. 14's `Π^{k+1}_i` projections (with
index orientation matched to the left-fold recurrence;
`Nat.unpair.fst` plays the role of Tourlakis's K and
`Nat.unpair.snd` plays L).  See master design §3.1. -/
def tupleAt : (k : ℕ) → ℕ → Fin (k + 1) → ℕ
  | 0,     n, _ => n
  | k + 1, n, i =>
      Fin.lastCases (motive := fun _ : Fin (k + 2) => ℕ)
        ((Nat.unpair n).2)
        (fun j : Fin (k + 1) => tupleAt k (Nat.unpair n).1 j)
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
    (v : Fin (k + 2) → ℕ) :
    tuplePack (k + 1) v
      = Nat.pair (tuplePack k (Fin.init v))
          (v (Fin.last (k + 1))) := rfl

@[simp] theorem tupleAt_zero (n : ℕ) (i : Fin 1) :
    tupleAt 0 n i = n := rfl

/-- `tupleAt` reduction at the last index: peels one
`Nat.unpair` step on the right. -/
@[simp] theorem tupleAt_succ_last (k n : ℕ) :
    tupleAt (k + 1) n (Fin.last (k + 1))
      = (Nat.unpair n).2 := by
  simp [tupleAt, Fin.lastCases_last]

/-- `tupleAt` reduction at a non-last index: peels one
`Nat.unpair` step on the left and recurses at depth `k`. -/
@[simp] theorem tupleAt_succ_castSucc (k n : ℕ)
    (j : Fin (k + 1)) :
    tupleAt (k + 1) n j.castSucc
      = tupleAt k (Nat.unpair n).1 j := by
  simp [tupleAt, Fin.lastCases_castSucc]

/-- Every component extracted from a packed natural is
bounded by the packed natural itself.  Mirrors existing
`Nat.seqAt_le` in `Utilities/SzudzikSeq.lean`; underlying
mathlib lemmas: `Nat.unpair_left_le`,
`Nat.unpair_right_le`. -/
theorem tupleAt_le : ∀ (k n : ℕ) (i : Fin (k + 1)),
    tupleAt k n i ≤ n
  | 0,     n, _ => by
      simp [tupleAt]
  | k + 1, n, i => by
      refine Fin.lastCases ?_ ?_ i
      · simp only [tupleAt, Fin.lastCases_last]
        exact Nat.unpair_right_le n
      · intro j
        simp only [tupleAt, Fin.lastCases_castSucc]
        exact le_trans (tupleAt_le k (Nat.unpair n).1 j)
          (Nat.unpair_left_le n)

/-- Round-trip: extracting component `i` from a packed
tuple returns the original component.  Realizes Tourlakis
2018 §0.1.0.34, p. 14's
`Π^k_i [[z_1,…,z_k]]^{(k)} = z_i`. -/
theorem tupleAt_tuplePack :
    ∀ (k : ℕ) (v : Fin (k + 1) → ℕ) (i : Fin (k + 1)),
      tupleAt k (tuplePack k v) i = v i
  | 0,     v, ⟨0, _⟩ => by
      simp only [tupleAt_zero]
      rfl
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
          Fin.init (tupleAt (k + 1) n)
            = tupleAt k (Nat.unpair n).1 := by
        funext j
        change tupleAt (k + 1) n j.castSucc
          = tupleAt k (Nat.unpair n).1 j
        exact tupleAt_succ_castSucc k n j
      rw [h_init]
      rw [tuplePack_tupleAt k (Nat.unpair n).1]
      exact Nat.pair_unpair n

/-- The sup of `Fin.init v` is at most the sup of `v`. -/
private theorem tuplePack_sup_init_le_sup
    {k : ℕ} (v : Fin (k + 2) → ℕ) :
    (Finset.univ : Finset (Fin (k + 1))).sup (Fin.init v)
      ≤ (Finset.univ : Finset (Fin (k + 2))).sup v := by
  apply Finset.sup_le
  intro i _
  change v i.castSucc ≤ _
  exact Finset.le_sup (f := v) (Finset.mem_univ _)

/-- Polynomial value bound on `tuplePack`.  At parameter
`k` (packing `(k + 1)`-tuples), `tuplePack k v` is bounded
by `tuplePackCoef k * (M + 1)^(2^k)` where `M = sup v` over
`Fin (k + 1)`.  Cites Tourlakis 2018 §0.1.0.34, p. 14
(proof that pairing stays in E²); master design §3.1. -/
theorem tuplePack_le :
    ∀ (k : ℕ) (v : Fin (k + 1) → ℕ),
      tuplePack k v ≤
        tuplePackCoef k *
          ((Finset.univ : Finset (Fin (k + 1))).sup v
            + 1) ^ (2 ^ k)
  | 0, v => by
      simp only [tuplePack_zero, tuplePackCoef, pow_zero,
        pow_one, one_mul]
      have hv0 : v 0
          ≤ (Finset.univ : Finset (Fin 1)).sup v :=
        Finset.le_sup (f := v) (Finset.mem_univ 0)
      omega
  | k + 1, v => by
      set M' :=
        (Finset.univ : Finset (Fin (k + 2))).sup v
      set Mi :=
        (Finset.univ : Finset (Fin (k + 1))).sup
          (Fin.init v)
      have hMi : Mi ≤ M' := tuplePack_sup_init_le_sup v
      have hlast : v (Fin.last (k + 1)) ≤ M' :=
        Finset.le_sup (f := v) (Finset.mem_univ _)
      have ih := tuplePack_le k (Fin.init v)
      have ih' :
          tuplePack k (Fin.init v)
            ≤ tuplePackCoef k * (M' + 1) ^ (2 ^ k) := by
        apply le_trans ih
        apply Nat.mul_le_mul_left
        apply Nat.pow_le_pow_left
        omega
      have hpair :
          tuplePack (k + 1) v
            ≤ (tuplePack k (Fin.init v)
                + v (Fin.last (k + 1)) + 1) ^ 2 := by
        rw [tuplePack_succ]
        exact Nat.pair_le_sq _ _
      have hsum :
          tuplePack k (Fin.init v)
              + v (Fin.last (k + 1)) + 1
            ≤ (tuplePackCoef k + 2)
                * (M' + 1) ^ (2 ^ k) := by
        have hC : 1 ≤ (M' + 1) ^ (2 ^ k) := by
          apply Nat.one_le_pow
          omega
        have hM'1 :
            v (Fin.last (k + 1)) + 1 ≤ M' + 1 := by omega
        have hM'pow :
            (M' + 1) ≤ (M' + 1) ^ (2 ^ k) := by
          have h2k : 1 ≤ 2 ^ k :=
            Nat.one_le_pow _ _ (by omega)
          calc M' + 1
              = (M' + 1) ^ 1 := by ring
            _ ≤ (M' + 1) ^ (2 ^ k) :=
                Nat.pow_le_pow_right (by omega) h2k
        calc tuplePack k (Fin.init v)
              + v (Fin.last (k + 1)) + 1
            ≤ tuplePackCoef k * (M' + 1) ^ (2 ^ k)
                + (M' + 1) := by omega
          _ ≤ tuplePackCoef k * (M' + 1) ^ (2 ^ k)
                + (M' + 1) ^ (2 ^ k) := by
              have := hM'pow; omega
          _ = (tuplePackCoef k + 1)
                * (M' + 1) ^ (2 ^ k) := by ring
          _ ≤ (tuplePackCoef k + 2)
                * (M' + 1) ^ (2 ^ k) := by
              apply Nat.mul_le_mul_right; omega
      have hsq :
          (tuplePack k (Fin.init v)
              + v (Fin.last (k + 1)) + 1) ^ 2
            ≤ ((tuplePackCoef k + 2)
                * (M' + 1) ^ (2 ^ k)) ^ 2 :=
        Nat.pow_le_pow_left hsum 2
      have hexpand :
          ((tuplePackCoef k + 2)
                * (M' + 1) ^ (2 ^ k)) ^ 2
            = (tuplePackCoef k + 2) ^ 2
                * (M' + 1) ^ (2 * 2 ^ k) := by
          rw [Nat.mul_pow, ← pow_mul]
          ring_nf
      have h2k1 : 2 * 2 ^ k = 2 ^ (k + 1) := by
        rw [pow_succ]; ring
      have hcoef :
          tuplePackCoef (k + 1)
            = (tuplePackCoef k + 2) ^ 2 :=
        rfl
      calc tuplePack (k + 1) v
          ≤ (tuplePack k (Fin.init v)
              + v (Fin.last (k + 1)) + 1) ^ 2 := hpair
        _ ≤ ((tuplePackCoef k + 2)
                * (M' + 1) ^ (2 ^ k)) ^ 2 := hsq
        _ = (tuplePackCoef k + 2) ^ 2
                * (M' + 1) ^ (2 * 2 ^ k) := hexpand
        _ = tuplePackCoef (k + 1)
                * (M' + 1) ^ (2 ^ (k + 1)) := by
            rw [h2k1, hcoef]

end Nat
