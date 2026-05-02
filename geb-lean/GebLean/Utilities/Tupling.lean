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

end Nat
