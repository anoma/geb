import GebLean
import GebLean.Ramified.Polynomial.SynCat

/-!
# Tests for the primed syntactic category

Executable checks that, over a one-binary-operation presentation on `S :=
Bool` with its `Nat` standard model, the `Category` instance of
`GebLean.Ramified.Polynomial.SynCat'` fires: the identity and associativity
laws hold on concrete morphisms, and `GebLean.Ramified.Polynomial.Hom'.eval`
respects composition on a concrete morphism.
-/

namespace GebLeanTests.Ramified.Polynomial.SynCat

open GebLean.Ramified GebLean.Ramified.Polynomial CategoryTheory

/-- A one-operation signature over `Bool`: a single binary operation, result
sort `true`. -/
abbrev binSig : SortedSig Bool :=
  { Op := Bool, arity := fun _ => [true, true], result := fun _ => true }

/-- The `Nat` model reading the binary operation as addition. -/
abbrev natModel : SortedModel binSig where
  carrier := fun _ => Nat
  interpOp := fun _ args => args 0 + args 1

/-- The presentation carrying `binSig` and its `Nat` standard model. -/
abbrev natPres : Presentation where
  S := Bool
  sig := binSig
  IsObj := fun _ => True
  alg := natAlgSig
  std := natModel

/-- The in-scope quotient relation: interpretative equality at the standard
model. -/
abbrev r : QuotRel' natPres.sig := interpQuotRel' natPres

/-- A two-variable context, as an object of the syntactic category. -/
abbrev twoCtx : SynCat' natPres r := [true, true]

/-- A one-variable context, as an object of the syntactic category. -/
abbrev oneCtx : SynCat' natPres r := [true]

/-- The sum term: `op true (var 0) (var 1)`, at the sole codomain position. -/
def sumTerm : Tm' binSig twoCtx true :=
  Tm'.op true (Fin.cons (Tm'.var 0) (Fin.cons (Tm'.var 1) finZeroElim))

/-- A concrete morphism `twoCtx ⟶ oneCtx`: the single component sends the sole
codomain position to `sumTerm`. -/
abbrev sumMor : twoCtx ⟶ oneCtx :=
  Quotient.mk _ (Fin.cons sumTerm finZeroElim)

-- The left identity law holds on the concrete morphism.
example : 𝟙 twoCtx ≫ sumMor = sumMor := Category.id_comp sumMor

-- The right identity law holds on the concrete morphism.
example : sumMor ≫ 𝟙 oneCtx = sumMor := Category.comp_id sumMor

/-- A second concrete morphism `twoCtx ⟶ oneCtx`: the projection `var 0`. -/
abbrev projMor : twoCtx ⟶ oneCtx :=
  Quotient.mk _ (Fin.cons (Tm'.var 0) finZeroElim)

-- Associativity holds on the concrete composite `twoCtx ⟶ oneCtx ⟶ oneCtx`.
example : (sumMor ≫ 𝟙 oneCtx) ≫ 𝟙 oneCtx = sumMor ≫ (𝟙 oneCtx ≫ 𝟙 oneCtx) :=
  Category.assoc sumMor (𝟙 oneCtx) (𝟙 oneCtx)

/-- A concrete two-variable environment in the `Nat` model, assigning `2` and
`3` to the two positions. -/
abbrev twoEnv : (standardModel natPres).Env twoCtx :=
  Fin.cons 2 (Fin.cons 3 finZeroElim)

-- Evaluating the identity morphism at an environment returns the environment.
example (ρ : (standardModel natPres).Env oneCtx) : Hom'.eval (𝟙 oneCtx) ρ = ρ :=
  Hom'.eval_id ρ

/-- `Hom'.eval` reduces the sum term at `(2, 3)` to their sum, through the
named computation rules `Hom'.eval_mk`, `Tm'.eval_op`, and `Tm'.eval_var`, not
kernel reduction of the underlying tree. -/
example : Hom'.eval sumMor twoEnv 0 = 5 := by
  rw [Hom'.eval_mk]
  change sumTerm.eval natModel twoEnv = 5
  rw [sumTerm, Tm'.eval_op natModel twoEnv true]
  change Tm'.eval natModel twoEnv (Tm'.var 0) + Tm'.eval natModel twoEnv (Tm'.var 1) = 5
  rw [Tm'.eval_var, Tm'.eval_var]
  rfl

-- `Hom'.eval` respects composition (`Hom'.eval_comp`).
example :
    Hom'.eval (𝟙 twoCtx ≫ sumMor) twoEnv
      = Hom'.eval sumMor (Hom'.eval (𝟙 twoCtx) twoEnv) :=
  Hom'.eval_comp (𝟙 twoCtx) sumMor twoEnv

-- Pairing followed by the first projection recovers the first component.
example :
    SynProd'.lift sumMor projMor ≫ SynProd'.fst natPres r oneCtx oneCtx = sumMor :=
  SynProd'.lift_fst sumMor projMor

-- Pairing followed by the second projection recovers the second component.
example :
    SynProd'.lift sumMor projMor ≫ SynProd'.snd natPres r oneCtx oneCtx = projMor :=
  SynProd'.lift_snd sumMor projMor

-- Every morphism to the empty context is the terminal morphism.
example (f : twoCtx ⟶ ([] : SynCat' natPres r)) : f = Hom'.terminal natPres r twoCtx :=
  Hom'.terminal_uniq f

end GebLeanTests.Ramified.Polynomial.SynCat
