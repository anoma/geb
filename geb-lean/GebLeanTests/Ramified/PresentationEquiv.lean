import GebLean.Ramified.PresentationEquiv
import GebLeanTests.Ramified.SigEquiv
import Mathlib.Logic.Equiv.Bool

/-!
# Tests for presentation equivalences

The toy signatures `toySig` / `toySig'` of `GebLeanTests/Ramified/SigEquiv.lean`
(over `Bool`, related by `Equiv.boolNot`) are packaged as two toy presentations
with matched standard models over the constant carrier `ℕ`. The equivalence
`toyPresEquiv` exercises the functoriality of `PresentationEquiv.synCatFunctor`
(its `map_comp`) and `PresentationEquiv.tmMap_eval` at the closed term
`succ zero`, whose two readings both evaluate to `1`.
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

/-- The empty environment at the toy presentation. -/
abbrev toyEnv : (standardModel toyPres).Env [] := fun i => i.elim0

/-- The closed term `succ zero` evaluates to `1` in the toy standard model. -/
example : toySuccZero.eval (standardModel toyPres) toyEnv = 1 := rfl

/-- Its explicitly written counterpart over the translated signature evaluates
to `1` in the translated standard model, at the transported environment. -/
example :
    toySuccZero'.eval (standardModel toyPres') (toyPresEquiv.mapEnv toyEnv) = 1 := rfl

/-- The two readings agree through the named lemmas: `tmMap_eval` at the closed
term, with the term translation identified by `toyEquiv_tmMap_toySuccZero`. -/
example :
    toySuccZero'.eval (standardModel toyPres') (toyPresEquiv.mapEnv toyEnv)
      = toyPresEquiv.carrierEquiv true (toySuccZero.eval (standardModel toyPres) toyEnv) := by
  rw [← toyEquiv_tmMap_toySuccZero]
  exact toyPresEquiv.tmMap_eval toySuccZero toyEnv

end GebLean.Ramified
