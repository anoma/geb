import GebLean.Ramified.PresentationEquiv
import GebLeanTests.Ramified.SigEquiv
import Mathlib.Logic.Equiv.Bool

/-!
# Tests for presentation equivalences

The Task C.8 toy signatures `toySig` / `toySig'` (over `Bool`, related by
`Equiv.boolNot`) are packaged as two toy presentations with matched standard
models over the constant carrier `ℕ`. The equivalence `toyPresEquiv` exercises
`PresentationEquiv.tmMap_eval` at a concrete term and the functoriality of
`PresentationEquiv.synCatFunctor` (its `map_comp`).
-/

namespace GebLean.Ramified

open CategoryTheory

/-- A trivial base algebra: one label of arity zero. -/
abbrev toyAlg : AlgSig where
  B := PUnit
  ar := fun _ => 0

/-- The standard model of `toySig`: the constant carrier `ℕ`, with the nullary
operation zero and the unary operation successor. -/
abbrev toyModel : SortedModel toySig where
  carrier := fun _ => ℕ
  interpOp := fun o args => match o with
    | false => 0
    | true => args 0 + 1

/-- The standard model of `toySig'`: the constant carrier `ℕ`, matched to
`toyModel` through the identity carrier equivalence. -/
abbrev toyModel' : SortedModel toySig' where
  carrier := fun _ => ℕ
  interpOp := fun o args => match o with
    | false => 0
    | true => args 0 + 1

/-- The toy presentation over `toySig`. -/
abbrev toyPres : Presentation where
  S := Bool
  sig := toySig
  IsObj := fun _ => True
  alg := toyAlg
  std := toyModel

/-- The negated toy presentation over `toySig'`. -/
abbrev toyPres' : Presentation where
  S := Bool
  sig := toySig'
  IsObj := fun _ => True
  alg := toyAlg
  std := toyModel'

/-- The presentation equivalence relating the toy presentations by `Bool`
negation on sorts and the identity carrier equivalence. -/
abbrev toyPresEquiv : PresentationEquiv toyPres toyPres' where
  sigEquiv := toyEquiv
  carrierEquiv := fun _ => Equiv.refl ℕ
  interpOp_comm := fun o args => by cases o <;> rfl

/-- `tmMap_eval` at a variable term: the translated variable evaluates to the
carrier-equivalence image of the original evaluation. -/
example {Γ : Ctx Bool} {s : Bool} (i : Fin Γ.length) (h : Γ.get i = s)
    (ρ : (standardModel toyPres).Env Γ) :
    (toyPresEquiv.sigEquiv.tmMap (Tm.reind h (Tm.var i))).eval
        (standardModel toyPres') (toyPresEquiv.mapEnv ρ)
      = toyPresEquiv.carrierEquiv s ((Tm.reind h (Tm.var i)).eval (standardModel toyPres) ρ) :=
  toyPresEquiv.tmMap_eval (Tm.reind h (Tm.var i)) ρ

/-- The syntactic-category functor of the toy equivalence respects composition. -/
example {Γ Δ E : SynCat toyPres (interpQuotRel toyPres)}
    (f : Γ ⟶ Δ) (g : Δ ⟶ E) :
    (toyPresEquiv.synCatFunctor).map (f ≫ g)
      = (toyPresEquiv.synCatFunctor).map f ≫ (toyPresEquiv.synCatFunctor).map g :=
  (toyPresEquiv.synCatFunctor).map_comp f g

end GebLean.Ramified
