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

/-- `lemma8` prepends a `1λ(A)` reduction to a representative. Exercised
non-vacuously at the base sort `o` with a concrete one-step β reduction
`(λx:o. b) N ⇒ b[x := N]`: representation of the reduct `b[x := N]` yields
representation of the redex `(λx:o. b) N`. -/
example (b : Binding.Tm (oneLambdaSig natAlgSig) ([] ++ [RType.o]) RType.o)
    (N : Binding.Tm (oneLambdaSig natAlgSig) [] RType.o)
    (F : Binding.Tm (rlmrOSig natAlgSig) [] RType.o)
    (h : Represents RType.o F (Binding.instantiate₁ N b)) :
    Represents RType.o F (OneLambda.app' (OneLambda.lam' b) N) :=
  lemma8 h (Relation.ReflTransGen.single (OneLambdaStep.beta b N))

/-- `lemma9_o` applied to a concrete closed source term at the base sort:
`sourceZero` represents itself as the concrete `o`-term of its denotation. -/
example : Represents RType.o sourceZero (conc (appEval sourceZero finZeroElim)) :=
  lemma9_o sourceZero

/-- The zero-successor combinator `λx:o. c_true^o(x) : o → o` as a closed
source term, exercising `lemma9_omega` at the shifted object sort `Ω o`. Since
its body is closed under the empty context, `RlmrOOp.lam` here targets the
object sort `RType.omega RType.o`, giving a closed term of that sort directly
via the `con` node — no binder is needed at `Ω τ'` itself, so the source term
is simply the shifted constructor node. -/
def sourceOmegaZero : Binding.Tm (rlmrOSig natAlgSig) [] (RType.omega RType.o) :=
  Binding.Tm.op (S := rlmrOSig natAlgSig)
    (RlmrOOp.con (RType.omega RType.o) (Or.inr rfl) false) (fun k => k.elim0)

/-- `lemma9_omega` applied to a concrete closed source term at an object sort
`Ω τ'`: `sourceOmegaZero` represents itself as the Berarducci-Böhm
representation of its own denotation. -/
example :
    Represents (RType.omega RType.o) sourceOmegaZero
      (bbRep (appEval sourceOmegaZero finZeroElim) (barTy RType.o)) :=
  lemma9_omega RType.o sourceOmegaZero

/-- A variable applied to a variable is `LamFree`: with `Γ = [o → o, o]`, the
application of the function variable at position `0` to the argument variable at
position `1` is a variable-application term, built from `LamFree.var` at the
leaves and `LamFree.app` at the node. -/
example :
    LamFree (Γ := [RType.arrow RType.o RType.o, RType.o])
      (app' (Binding.Tm.var ⟨⟨0, by decide⟩, rfl⟩)
        (Binding.Tm.var ⟨⟨1, by decide⟩, rfl⟩)) :=
  LamFree.app (LamFree.var _) (LamFree.var _)

end GebLean.Ramified
