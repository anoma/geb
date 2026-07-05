import GebLean.Ramified.Soundness.Represents

/-!
# Tests for the representation relation

The bare names `Tm`, `Tm.op`, and `Tm.var` are qualified to `GebLean.Binding`
throughout, since `GebLean.Ramified` carries its own `Tm` (the sorted-signature
term type of `GebLean/Ramified/Term.lean`) that would otherwise shadow the
binder-kit `Tm` used here.
-/

namespace GebLean.Ramified

/-- The zero constructor `c_false^o : o` as a closed source term of the
object-sorted applicative calculus, the nullary constructor node at the base
object sort. -/
def sourceZero : Binding.Tm (rlmrOSig natAlgSig) [] RType.o :=
  Binding.Tm.op (S := rlmrOSig natAlgSig)
    (RlmrOOp.con RType.o (Or.inl rfl) false) (fun k => k.elim0)

/-- At the base sort `o`, a closed source term is represented by the concrete
`o`-term of its denotation, holding reflexively: `Represents o F (conc (appEval F
finZeroElim))` by `ReflTransGen.refl`. -/
example : Represents RType.o sourceZero (conc (appEval sourceZero finZeroElim)) :=
  Relation.ReflTransGen.refl

/-- The arrow clause of `Represents` unfolds to the logical-relation quantifier:
representation at `σ → τ'` sends represented arguments to represented
applications. Exercised here at `o → o` by discharging the hypothesis
definitionally. -/
example (F : Binding.Tm (rlmrOSig natAlgSig) [] (RType.arrow RType.o RType.o))
    (Fhat : Binding.Tm (oneLambdaSig natAlgSig) [] (barTy (RType.arrow RType.o RType.o)))
    (h : ∀ (G : Binding.Tm (rlmrOSig natAlgSig) [] RType.o)
        (Ghat : Binding.Tm (oneLambdaSig natAlgSig) [] (barTy RType.o)),
        Represents RType.o G Ghat →
          Represents RType.o (sourceApp F G) (OneLambda.app' Fhat Ghat)) :
    Represents (RType.arrow RType.o RType.o) F Fhat := h

end GebLean.Ramified
