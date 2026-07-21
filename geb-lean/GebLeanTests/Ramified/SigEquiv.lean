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

/-- The closed nullary term over `toySig`, at sort `false`. -/
abbrev toyZero : Tm toySig [] false :=
  Tm.op (sig := toySig) false (fun i => i.elim0)

/-- The closed term `succ zero` over `toySig`: the unary operation at sort
`true` applied to `toyZero`. -/
abbrev toySuccZero : Tm toySig [] true :=
  Tm.op (sig := toySig) true (Fin.cases toyZero (fun k => k.elim0))

/-- The closed nullary term over `toySig'`, at the negated sort `true`. -/
abbrev toyZero' : Tm toySig' [] true :=
  Tm.op (sig := toySig') false (fun i => i.elim0)

/-- The counterpart of `toySuccZero` written directly over `toySig'`: the same
two operations, now at the negated sorts — the unary operation at sort `false`
applied to `toyZero'`. -/
abbrev toySuccZero' : Tm toySig' [] false :=
  Tm.op (sig := toySig') true (Fin.cases toyZero' (fun k => k.elim0))

/-- The term translation carries the nullary closed term onto its counterpart
at the negated result sort. -/
theorem toyEquiv_tmMap_toyZero : toyEquiv.tmMap toyZero = toyZero' := by
  simp only [toyZero, toyZero', toyEquiv.tmMap_op]
  congr 3
  funext m
  exact m.elim0

/-- The term translation carries the closed term onto its explicitly written
counterpart, arity and result transported the same way. -/
theorem toyEquiv_tmMap_toySuccZero : toyEquiv.tmMap toySuccZero = toySuccZero' := by
  simp only [toySuccZero, toySuccZero', toyEquiv.tmMap_op]
  congr 3
  funext k
  induction k using Fin.cases with
  | zero => exact toyEquiv_tmMap_toyZero
  | succ m => exact m.elim0

end GebLean.Ramified
