import GebLean.Utilities.Tupling
import GebLean.Utilities.ERArith
import GebLean.LawvereERPolynomialBound
import GebLean.LawvereERQuot

/-!
# ER-side fixed-length k-tuple Szudzik pairing

ER-level named composites mirroring `Nat.tuplePack` and
`Nat.tupleAt` in `Utilities/Tupling.lean`.  Bottom-up
construction from existing atomic ER generators (`proj`,
`natPair`, `natUnpairFst`, `natUnpairSnd`, `comp`) per
CLAUDE.md "bottom-up named-composite discipline".

See master design §3.1 (Lean entities, ER layer) and
the spec at
`docs/superpowers/specs/2026-05-02-step-1-er-tupling-design.md`.
-/

namespace GebLean
namespace ERMor1

/-- ER named composite for fixed-length `(k + 1)`-tuple
Szudzik pack.  Built bottom-up from `proj`, `natPair`,
`comp` per CLAUDE.md "bottom-up named-composite
discipline".  Mirrors `Nat.tuplePack`'s left-fold
recurrence (master design §3.1; Tourlakis 2018 §0.1.0.34,
p. 14). -/
def tuplePack : (k : ℕ) → ERMor1 (k + 1)
  | 0     => ERMor1.proj 0
  | k + 1 =>
      ERMor1.comp ERMor1.natPair
        ![ ERMor1.comp (tuplePack k)
             (fun i : Fin (k + 1) =>
               ERMor1.proj i.castSucc)
         , ERMor1.proj (Fin.last (k + 1)) ]

/-- ER named composite extracting component `i` from a
packed `(k + 1)`-tuple.  Built bottom-up from `proj`,
`natUnpairFst`, `natUnpairSnd`, `comp`.  Mirrors
`Nat.tupleAt`'s left-fold recurrence (master design §3.1;
Tourlakis 2018 §0.1.0.34, p. 14, with index orientation
matched to the inverse of the left-fold recurrence). -/
def tupleAt : (k : ℕ) → Fin (k + 1) → ERMor1 1
  | 0,     _ => ERMor1.proj 0
  | k + 1, i =>
      Fin.lastCases
        (motive := fun _ : Fin (k + 2) => ERMor1 1)
        ERMor1.natUnpairSnd
        (fun j : Fin (k + 1) =>
          ERMor1.comp (tupleAt k j) ![ERMor1.natUnpairFst])
        i

end ERMor1
end GebLean
