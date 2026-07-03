import GebLean
import GebLean.Ramified.AlgSig

/-!
# Tests for free-algebra signatures and their recurrence

Executable checks that `GebLean.Ramified.FreeAlg.recurse` computes the
length recurrence (base `0`, step `+1`) over the `1 + X` word signature
built from `AlgSig`.
-/

namespace GebLeanTests.Ramified.AlgSig

open GebLean.Ramified

/-- The `1 + X` word signature: `false` is the 0-ary constructor,
`true` the unary constructor. -/
def wordSig : AlgSig := ⟨Bool, fun b => cond b 1 0⟩

/-- The base element (the 0-ary constructor with no subterms). -/
def zero : FreeAlg wordSig := FreeAlg.mk false Fin.elim0

/-- The unary constructor applied to one subterm. -/
def succ (t : FreeAlg wordSig) : FreeAlg wordSig := FreeAlg.mk true (fun _ => t)

/-- The length recurrence: `0` at the base, one more than the recursive
result at the unary step. -/
def length : FreeAlg wordSig → Nat :=
  FreeAlg.recurse (P := Unit) (C := Nat)
    (fun b => match b with
      | true => fun _ _ (recResults : Fin 1 → Nat) => recResults 0 + 1
      | false => fun _ _ _ => 0) ()

#guard length zero = 0
#guard length (succ zero) = 1
#guard length (succ (succ (succ zero))) = 3

end GebLeanTests.Ramified.AlgSig
