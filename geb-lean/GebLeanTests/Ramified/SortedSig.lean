import GebLean
import GebLean.Ramified.SortedSig

/-!
# Tests for multi-sorted signatures and the constructor summand

Executable checks that `GebLean.Ramified.SortedSig.sum` exposes both
summands' operations and that `GebLean.Ramified.constructorSig` derives,
over the `1 + X` word signature, a 0-ary and a 1-ary operation at a
single object sort.
-/

namespace GebLeanTests.Ramified.SortedSig

open GebLean.Ramified

/-- The constructor summand of the `1 + X` word signature, with every
sort an object sort. -/
def cSig : SortedSig Nat := constructorSig natAlgSig (fun _ => True)

#guard (cSig.arity (⟨0, True.intro⟩, false)).length = 0
#guard (cSig.arity (⟨0, True.intro⟩, true)).length = 1
#guard cSig.arity (⟨0, True.intro⟩, true) = [0]
#guard cSig.result (⟨0, True.intro⟩, false) = 0
#guard cSig.result (⟨0, True.intro⟩, true) = 0

/-- A one-operation signature: a unary operation with argument sort `0` and
result sort `0`. -/
def sigA : SortedSig Nat := { Op := Unit, arity := fun _ => [0], result := fun _ => 0 }

/-- A one-operation signature: a binary operation at sort `2`. -/
def sigB : SortedSig Nat := { Op := Unit, arity := fun _ => [1, 1], result := fun _ => 2 }

/-- Their data-types-a-la-carte sum. -/
def sigAB : SortedSig Nat := sigA.sum sigB

#guard sigAB.arity (Sum.inl ()) = [0]
#guard sigAB.arity (Sum.inr ()) = [1, 1]
#guard sigAB.result (Sum.inl ()) = 0
#guard sigAB.result (Sum.inr ()) = 2

end GebLeanTests.Ramified.SortedSig
