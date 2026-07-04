import GebLean.Ramified.Soundness.Applicative

/-!
# Tests for the applicative binder signatures

The bare names `Tm`, `Tm.op`, and `Tm.var` are qualified to `GebLean.Binding`
throughout: `GebLean.Ramified` carries its own `Tm` (the sorted-signature term
type of `GebLean/Ramified/Term.lean`), which would otherwise shadow the
binder-kit `Tm` used here.
-/

namespace GebLean.Ramified

/-- A closed nullary constant elaborates: the zero-constructor of the `1 + X`
word algebra has arity `0`, so `con o false` has result `o` and no arguments,
yielding a closed term of sort `o`. -/
example : Binding.Tm (rlmrOSig natAlgSig) [] RType.o :=
  Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.con RType.o false) (fun j => j.elim0)

/-- A `lam` node exercises the binder/argument positions: `lam o o` has result
`o.arrow o` and a single body argument of sort `o` under one binder of sort
`o`; the body is the bound variable, at de Bruijn position `0` of the extended
context `[] ++ [o] = [o]`. -/
example : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow RType.o RType.o) :=
  Binding.Tm.op (S := rlmrOSig natAlgSig) (RlmrOOp.lam RType.o RType.o)
    (fun j => Fin.cases (Binding.Tm.var ⟨⟨0, by decide⟩, rfl⟩) (fun k => k.elim0) j)

end GebLean.Ramified
