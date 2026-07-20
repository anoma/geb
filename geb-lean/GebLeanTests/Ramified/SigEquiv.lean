import GebLean.Ramified.SigEquiv
import Mathlib.Logic.Equiv.Bool

/-!
# Tests for sorted-signature equivalences and the term translation

Two toy two-sorted signatures over `Bool`, related by the nontrivial sort
equivalence `Equiv.boolNot`, exercise the constructor-naturality lemmas
`tmMap_var` / `tmMap_op`, the substitution-commutation lemma `tmMap_subst`,
and one `tmEquiv` round trip.
-/

namespace GebLean.Ramified

/-- A toy two-sorted signature over `Bool`: a nullary operation at `false`
and a unary operation at `true` with argument sort `false`. -/
abbrev toySig : SortedSig Bool where
  Op := Bool
  arity := fun o => match o with | true => [false] | false => []
  result := fun o => o

/-- The negated toy signature: the same operations with sorts and arities
transported along `Bool` negation. -/
abbrev toySig' : SortedSig Bool where
  Op := Bool
  arity := fun o => match o with | true => [true] | false => []
  result := fun o => !o

/-- The sorted-signature equivalence relating the toy signatures by `Bool`
negation on sorts and the identity on operations. -/
abbrev toyEquiv : SortedSigEquiv toySig toySig' where
  sortEquiv := Equiv.boolNot
  opEquiv := Equiv.refl Bool
  arity_comm := fun o => by cases o <;> rfl
  result_comm := fun _ => rfl

/-- `tmMap` on a variable node is the reindexed translated variable. -/
example {Γ : Ctx Bool} (i : Fin Γ.length) :
    toyEquiv.tmMap (Tm.var (sig := toySig) i) =
      Tm.reind (toyEquiv.get_ctx Γ i) (Tm.var (Fin.cast (toyEquiv.ctx_length Γ) i)) :=
  toyEquiv.tmMap_var i

/-- `tmMap` on an operation node is the reindexed translated operation. -/
example {Γ : Ctx Bool} (o : Bool)
    (args : ∀ i : Fin (toySig.arity o).length, Tm toySig Γ ((toySig.arity o).get i)) :
    toyEquiv.tmMap (Tm.op o args) =
      Tm.reind (toyEquiv.result_comm o) (Tm.op (toyEquiv.opEquiv o)
        (fun j => Tm.reind (toyEquiv.get_arity o j)
          (toyEquiv.tmMap (args (Fin.cast (toyEquiv.arity_length o) j))))) :=
  toyEquiv.tmMap_op o args

/-- `tmMap` commutes with substitution at a concrete operation term. -/
example {Γ Δ : Ctx Bool}
    (args : ∀ i : Fin (toySig.arity true).length, Tm toySig Γ ((toySig.arity true).get i))
    (σ : ∀ i : Fin Γ.length, Tm toySig Δ (Γ.get i)) :
    toyEquiv.tmMap ((Tm.op (sig := toySig) true args).subst σ) =
      (toyEquiv.tmMap (Tm.op (sig := toySig) true args)).subst
        (fun j => Tm.reind (toyEquiv.get_ctx Γ (Fin.cast (toyEquiv.ctx_length Γ).symm j)).symm
          (toyEquiv.tmMap (σ (Fin.cast (toyEquiv.ctx_length Γ).symm j)))) :=
  toyEquiv.tmMap_subst (Tm.op (sig := toySig) true args) σ

/-- The `tmEquiv` round trip: translating and translating back is the
identity. -/
example {Γ : Ctx Bool} {s : Bool} (t : Tm toySig Γ s) :
    (toyEquiv.tmEquiv Γ s).symm (toyEquiv.tmEquiv Γ s t) = t :=
  (toyEquiv.tmEquiv Γ s).symm_apply_apply t

end GebLean.Ramified
