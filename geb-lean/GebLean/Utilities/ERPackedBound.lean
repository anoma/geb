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

end ERMor1
end GebLean
