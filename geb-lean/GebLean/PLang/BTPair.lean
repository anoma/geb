import GebLean.PLang.Syntax
import GebLean.LawvereBT
import Mathlib.Data.Nat.Pairing
import Mathlib.Logic.Equiv.Defs

/-!
# Bijection between Finite-Alphabet Binary Trees and ℕ

For each `n : ℕ`, a bijection `BTα (Fin (n+1)) ≃ ℕ` via the
"tree of finite alphabet" pairing function (Wikipedia,
"Restriction to natural numbers"); composition through ℕ gives
alphabet-shift bijections; specializing at `m = 0` plus
`Fin 1 ≃ PUnit` gives `BTα (Fin (n+1)) ≃ BT.{0}`.  Includes the
perfect-tree generator and the depth-ordering biconditional.

Relocates `encodeBT`/`decodeBT`/`Encodable BT.{0}` from
`LawvereBTPrimrec.lean` and recovers them as `n = 0` aliases.
-/

namespace GebLean

open CategoryTheory

universe u

/-- The `Over PUnit` carrier for `BTα α`: the constant fibration
`α → PUnit`. -/
def BTα.carrier (α : Type u) : Over PUnit.{u + 1} :=
  Over.mk (fun _ : α => PUnit.unit)

/-- Labeled binary trees with leaf labels in `α`, as the free
monad of `polyProdType` at the `α`-fibered carrier.  Specializes
to the existing `BT` at `α = PUnit` (modulo a propositional
carrier-equality bridge). -/
abbrev BTα (α : Type u) : Type u :=
  PolyFreeM (BTα.carrier α) polyProdType PUnit.unit

end GebLean
