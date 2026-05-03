import GebLean.Utilities.Tupling
import GebLean.Utilities.ERArith
import GebLean.LawvereERArith
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
  ERMor1.comp ERMor1.mulN fun i => match i with
    | ⟨0, _⟩ => ERMor1.natN a (Nat.tuplePackCoef k)
    | ⟨1, _⟩ =>
        ERMor1.comp ERMor1.expER fun j => match j with
          | ⟨0, _⟩ => ERMor1.natN a (2 ^ k)
          | ⟨1, _⟩ =>
              ERMor1.comp ERMor1.addN fun l => match l with
                | ⟨0, _⟩ => componentBound
                | ⟨1, _⟩ => ERMor1.natN a 1

/-- Interpretation of `tuplePackedBound`:
`Nat.tuplePackCoef k * (componentBound.interp ctx + 1) ^ (2 ^ k)`.
Master design §3.2. -/
@[simp] theorem interp_tuplePackedBound (k : ℕ) {a : ℕ}
    (componentBound : ERMor1 a) (ctx : Fin a → ℕ) :
    (ERMor1.tuplePackedBound k componentBound).interp ctx
      = Nat.tuplePackCoef k *
          (componentBound.interp ctx + 1) ^ (2 ^ k) := by
  unfold ERMor1.tuplePackedBound
  simp only [ERMor1.interp_comp, ERMor1.interp_mulN,
    ERMor1.interp_expER, ERMor1.interp_addN,
    ERMor1.interp_natN]

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

namespace PolyBound

/-- PolyBound for `tuplePackedBound k componentBound`.
Given `pb : PolyBound componentBound`, produces:

- `degree = pb.degree * 2 ^ k`
- `coefficient = tuplePackCoef k *
                   (pb.coefficient + pb.constant + 1) ^ (2 ^ k)`
- `constant = 0`

Derivation: substituting `pb`'s formula
`componentBound.interp ctx ≤
  pb.coefficient * X ^ pb.degree + pb.constant`
(where `X = maxCtx ctx + 1`) into
`tuplePackCoef k * (componentBound.interp ctx + 1) ^ (2 ^ k)`
and applying
`(A * X ^ d + B + 1) ≤ (A + B + 1) * X ^ d` for `X ≥ 1`,
we get the formula above.  Master design §3.2; §15.13
punch-list. -/
def ofTuplePackedBound (k : ℕ) {a : ℕ}
    {componentBound : ERMor1 a}
    (pb : PolyBound componentBound) :
    PolyBound (ERMor1.tuplePackedBound k componentBound) where
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
    have h_cb_step :
        componentBound.interp ctx + 1
          ≤ (pb.coefficient + pb.constant + 1)
              * X ^ pb.degree := by
      have hpow_pos : 1 ≤ X ^ pb.degree :=
        Nat.one_le_pow _ _ hX_pos
      have h_const_le :
          pb.constant ≤ pb.constant * X ^ pb.degree :=
        Nat.le_mul_of_pos_right _ hpow_pos
      calc componentBound.interp ctx + 1
          ≤ pb.coefficient * X ^ pb.degree
              + pb.constant + 1 := by
            have := h_cb
            omega
        _ ≤ pb.coefficient * X ^ pb.degree
              + pb.constant * X ^ pb.degree
              + X ^ pb.degree := by
            have := h_const_le
            have := hpow_pos
            omega
        _ = (pb.coefficient + pb.constant + 1)
              * X ^ pb.degree := by ring
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
    calc Nat.tuplePackCoef k
          * (componentBound.interp ctx + 1) ^ (2 ^ k)
        ≤ Nat.tuplePackCoef k
            * ((pb.coefficient + pb.constant + 1)
                * X ^ pb.degree) ^ (2 ^ k) :=
          Nat.mul_le_mul_left _ h_pow
      _ = Nat.tuplePackCoef k
            * ((pb.coefficient + pb.constant + 1) ^ (2 ^ k)
                * X ^ (pb.degree * 2 ^ k)) := by
          rw [h_expand]
      _ = Nat.tuplePackCoef k
            * (pb.coefficient + pb.constant + 1) ^ (2 ^ k)
            * (M + 1) ^ (pb.degree * 2 ^ k) := by
          rw [hX]; ring
      _ ≤ Nat.tuplePackCoef k
            * (pb.coefficient + pb.constant + 1) ^ (2 ^ k)
            * (M + 1) ^ (pb.degree * 2 ^ k) + 0 := by omega

end PolyBound

end ERMor1
end GebLean
