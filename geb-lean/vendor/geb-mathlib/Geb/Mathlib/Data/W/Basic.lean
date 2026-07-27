/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.W.Basic
public import Geb.Mathlib.Data.FinEnum

/-!
# The W-type fold and paramorphism: computation rules and uniqueness

`WType.elim` is the non-dependent fold of a W-type: the morphism into a
given algebra of the polynomial endofunctor `X ↦ Σ a, β a → X`. mathlib
states the fold but neither its computation rule as a named `@[simp]`
lemma nor its uniqueness. Together the two make `WType β` the initial
algebra of that endofunctor, stated concretely. `WType.para` generalises
the fold to a paramorphism, whose step additionally sees each node's
children as subtrees, not only as their folded values.

## Main definitions

* `WType.para` — the paramorphism: a fold whose step function receives
  each child as a subtree paired with its folded value.
* `WType.beq` — Boolean equality of W-trees, decidable when the shape
  type has decidable equality and every direction type is finitely
  enumerable.

## Main statements

* `WType.elim_mk` — the computation rule: the fold of a constructor
  application is the algebra applied to the folded children.
* `WType.elim_unique` — uniqueness: a function satisfying the
  computation rule is the fold.
* `WType.para_mk` — the paramorphism's computation rule.
* `WType.beq_eq_true_iff` — `beq` decides equality of W-trees.
* `WType.instDecidableEq` — the resulting `DecidableEq (WType β)`
  instance.

## Implementation notes

`elim_mk` holds by `rfl`; mathlib's equation compiler generates the
equation, and the named `@[simp]` form is what makes the hypothesis
shape of `elim_unique` usable by `simp` at call sites. `elim_unique`
drives its recursion through an explicit `WType.rec` application into a
`Prop`-valued motive. `para` is `elim` at the product carrier
`WType β × γ`, whose first component reconstructs the subtree; its
computation rule `para_mk` does not hold by `rfl` and is proved through
that reconstruction.

## References

* [GambinoHyland2004]
* [Meertens1992]

## Tags

W-type, fold, initial algebra, polynomial functor
-/

public section

universe uA uB uC

namespace WType

/-- The fold's computation rule: folding a constructor application
applies the algebra to the children's folds. -/
@[simp] theorem elim_mk {α : Type uA} {β : α → Type uB} {γ : Type uC}
    (fγ : (Σ a : α, β a → γ) → γ) (a : α) (f : β a → WType β) :
    elim γ fγ (mk a f) = fγ ⟨a, fun b ↦ elim γ fγ (f b)⟩ :=
  rfl

/-- The fold is the unique function satisfying its computation rule.
With `elim` itself, this is the initiality of `WType β` among algebras
of the polynomial endofunctor `X ↦ Σ a, β a → X`. -/
theorem elim_unique {α : Type uA} {β : α → Type uB} {γ : Type uC}
    (fγ : (Σ a : α, β a → γ) → γ) (g : WType β → γ)
    (hg : ∀ (a : α) (f : β a → WType β),
      g (mk a f) = fγ ⟨a, fun b ↦ g (f b)⟩) :
    g = elim γ fγ :=
  funext fun x ↦
    rec (motive := fun x ↦ g x = elim γ fγ x)
      (fun a f ih ↦ (hg a f).trans (congrArg (fun h ↦ fγ ⟨a, h⟩) (funext ih))) x

/-- The algebra of the paramorphism fold: rebuild the node from the
children's reconstructed subtrees, and apply the step to the node. -/
@[expose] def paraStep {α : Type uA} {β : α → Type uB} (γ : Type uC)
    (fγ : (Σ a : α, β a → WType β × γ) → γ) :
    (Σ a : α, β a → WType β × γ) → WType β × γ :=
  fun x ↦ (mk x.1 fun b ↦ (x.2 b).1, fγ x)

/-- The fold's first component reconstructs its input. -/
private theorem paraStep_fst {α : Type uA} {β : α → Type uB} (γ : Type uC)
    (fγ : (Σ a : α, β a → WType β × γ) → γ) (w : WType β) :
    (elim (WType β × γ) (paraStep γ fγ) w).1 = w :=
  rec (motive := fun w ↦ (elim (WType β × γ) (paraStep γ fγ) w).1 = w)
    (fun a _f ih ↦ congrArg (mk a) (funext ih)) w

/-- The paramorphism of a W-type: a fold whose step sees each node's
children as subtrees together with their folded values. Obtained from
`elim` at the product carrier `WType β × γ`, whose first component
reconstructs the subtree, so no new recursion is introduced.
[Meertens1992] -/
@[expose] def para {α : Type uA} {β : α → Type uB} (γ : Type uC)
    (fγ : (Σ a : α, β a → WType β × γ) → γ) : WType β → γ :=
  fun w ↦ (elim (WType β × γ) (paraStep γ fγ) w).2

/-- The paramorphism's computation rule: it applies the step to the node's
children paired with their own paramorphisms. Unlike `elim_mk` this does
not hold by `rfl`; it is `paraStep_fst` under a `congrArg`. -/
@[simp] theorem para_mk {α : Type uA} {β : α → Type uB} {γ : Type uC}
    (fγ : (Σ a : α, β a → WType β × γ) → γ) (a : α) (f : β a → WType β) :
    para γ fγ (mk a f) = fγ ⟨a, fun b ↦ (f b, para γ fγ (f b))⟩ :=
  congrArg (fun h ↦ fγ ⟨a, h⟩)
    (funext fun b ↦ Prod.ext (paraStep_fst γ fγ (f b)) rfl)

/-- Boolean equality of W-trees: compare the shapes, then compare the
children pointwise over the finite direction type. A fold by `elim` at
the carrier `WType β → Bool`, so no recursion is introduced. -/
@[expose] def beq {α : Type uA} {β : α → Type uB} [DecidableEq α]
    [∀ a, FinEnum (β a)] : WType β → WType β → Bool :=
  elim (WType β → Bool) fun x t' ↦
    if h : x.1 = (toSigma t').1 then
      decide (∀ b : β x.1, x.2 b ((toSigma t').2 (h ▸ b)) = true)
    else false

/-- `beq` unfolded on two constructor applications. -/
theorem beq_mk {α : Type uA} {β : α → Type uB} [DecidableEq α]
    [∀ a, FinEnum (β a)] (a : α) (f : β a → WType β) (a' : α)
    (f' : β a' → WType β) :
    beq (mk a f) (mk a' f') =
      if h : a = a' then decide (∀ b : β a, beq (f b) (f' (h ▸ b)) = true) else false :=
  rfl

/-- `beq` decides equality of W-trees. -/
theorem beq_eq_true_iff {α : Type uA} {β : α → Type uB} [DecidableEq α]
    [∀ a, FinEnum (β a)] (s t : WType β) : beq s t = true ↔ s = t :=
  rec (motive := fun s ↦ ∀ t, beq s t = true ↔ s = t)
    (fun a f ih t ↦
      match t with
      | mk a' f' =>
        match ‹DecidableEq α› a a' with
        | isTrue h => by
            subst h
            rw [beq_mk, dif_pos rfl, decide_eq_true_iff]
            exact ⟨fun hb ↦ congrArg (mk a) (funext fun b ↦ (ih b (f' b)).mp (hb b)),
              fun he b ↦ (ih b (f' b)).mpr (congrFun (eq_of_heq (mk.inj he).2) b)⟩
        | isFalse h => by
            rw [beq_mk, dif_neg h]
            exact ⟨fun hb ↦ Bool.noConfusion hb, fun he ↦ absurd (mk.inj he).1 h⟩)
    s t

/-- Equality of W-trees is decidable when shapes have decidable equality
and every direction type is finitely enumerable. mathlib reaches this
only through `Encodable`, which additionally requires the shape and
direction types countable. -/
instance instDecidableEq {α : Type uA} {β : α → Type uB} [DecidableEq α]
    [∀ a, FinEnum (β a)] : DecidableEq (WType β) :=
  fun s t ↦ decidable_of_iff _ (beq_eq_true_iff s t)

end WType
