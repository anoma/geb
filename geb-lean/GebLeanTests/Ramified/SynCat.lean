import GebLean
import GebLean.Ramified.SynCat

/-!
# Tests for the generic syntactic category

Executable checks that, over the one-binary-operation presentation on
`S := Unit` with its `Nat` standard model, the `Category` and
`CartesianMonoidalCategory` instances of `GebLean.Ramified.SynCat` fire: the
identity laws hold on a concrete morphism, the tensor object is context
concatenation, and the pairing morphism composes correctly with the
projections.
-/

namespace GebLeanTests.Ramified.SynCat

open GebLean.Ramified CategoryTheory
open scoped MonoidalCategory

/-- A one-operation signature over `Unit`: a single binary operation. -/
abbrev binSig : SortedSig Unit :=
  { Op := Unit, arity := fun _ => [(), ()], result := fun _ => () }

/-- The `Nat` model reading the binary operation as addition. -/
abbrev natModel : SortedModel binSig where
  carrier := fun _ => Nat
  interpOp := fun _ args => args 0 + args 1

/-- The presentation carrying `binSig` and its `Nat` standard model. -/
abbrev pres : Presentation where
  S := Unit
  sig := binSig
  IsObj := fun _ => True
  alg := natAlgSig
  std := natModel

/-- The in-scope quotient relation: interpretative equality at the standard
model. -/
abbrev r : QuotRel pres.sig := interpQuotRel pres

/-- A two-variable context, as an object of the syntactic category. -/
abbrev twoCtx : SynCat pres r := [(), ()]

/-- A one-variable context, as an object of the syntactic category. -/
abbrev oneCtx : SynCat pres r := [()]

/-- A concrete morphism `twoCtx ⟶ oneCtx`: the single component sends the sole
codomain position to the sum term `op (var 0) (var 1)`. -/
abbrev sumMor : twoCtx ⟶ oneCtx :=
  Quotient.mk _ (fun _ : Fin 1 =>
    Tm.op () (Fin.cons (Tm.var 0) (Fin.cons (Tm.var 1) finZeroElim)))

-- The left identity law holds on the concrete morphism.
example : 𝟙 twoCtx ≫ sumMor = sumMor := Category.id_comp sumMor

-- The right identity law holds on the concrete morphism.
example : sumMor ≫ 𝟙 oneCtx = sumMor := Category.comp_id sumMor

-- The tensor object is context concatenation.
example : (twoCtx ⊗ oneCtx : SynCat pres r) = ([(), (), ()] : SynCat pres r) := rfl

/-- A second concrete morphism `twoCtx ⟶ oneCtx`: the projection `var 0`. -/
abbrev projMor : twoCtx ⟶ oneCtx :=
  Quotient.mk _ (fun _ : Fin 1 => Tm.var 0)

-- Pairing then first projection recovers the first component.
example :
    SynProd.lift sumMor projMor ≫ SynProd.fst pres r oneCtx oneCtx = sumMor :=
  SynProd.lift_fst sumMor projMor

-- Pairing then second projection recovers the second component.
example :
    SynProd.lift sumMor projMor ≫ SynProd.snd pres r oneCtx oneCtx = projMor :=
  SynProd.lift_snd sumMor projMor

end GebLeanTests.Ramified.SynCat
