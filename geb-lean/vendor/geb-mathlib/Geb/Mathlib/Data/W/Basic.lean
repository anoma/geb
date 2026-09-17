/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Mathlib.Data.W.Basic
public import Geb.Mathlib.Data.FinEnum

set_option doc.verso true in
/-!
# The W-type fold and paramorphism: computation rules and uniqueness

{name}`WType.elim` is the non-dependent fold of a W-type: the morphism
into a given algebra of the polynomial endofunctor
{lit}`X ↦ Σ a, β a → X`. mathlib states the fold but neither its
computation rule as a named {lit}`@[simp]` lemma nor its uniqueness.
Together the two make {lit}`WType β` the initial algebra of that
endofunctor, stated concretely. {lit}`WType.para` generalises the fold
to a paramorphism, whose step additionally sees each node's children as
subtrees, not only as their folded values.

## Main definitions

* {lit}`WType.para` — the paramorphism: a fold whose step function
  receives each child as a subtree paired with its folded value.
* {lit}`WType.beq` — Boolean equality of W-trees, decidable when the
  shape type has decidable equality and every direction type is
  finitely enumerable.

## Main statements

* {lit}`WType.elim_mk` — the computation rule: the fold of a
  constructor application is the algebra applied to the folded
  children.
* {lit}`WType.elim_unique` — uniqueness: a function satisfying the
  computation rule is the fold.
* {lit}`WType.para_mk` — the paramorphism's computation rule.
* {lit}`WType.beq_eq_true_iff` — {lit}`beq` decides equality of
  W-trees.
* {lit}`WType.instDecidableEq` — the resulting
  {lit}`DecidableEq (WType β)` instance.

## Implementation notes

{lit}`elim_mk` holds by {name}`rfl`; mathlib's equation compiler
generates the equation, and the named {lit}`@[simp]` form is what makes
the hypothesis shape of {lit}`elim_unique` usable by {lit}`simp` at
call sites. {lit}`elim_unique` drives its recursion through an explicit
{name}`WType.rec` application into a {lit}`Prop`-valued motive.
{lit}`para` is {name}`WType.elim` at the product carrier
{lit}`WType β × γ`, whose first component reconstructs the subtree;
its computation rule {lit}`para_mk` does not hold by {name}`rfl` and is
proved through that reconstruction.

## References

* \[GambinoHyland2004\]
* \[Meertens1992\]

## Tags

W-type, fold, initial algebra, polynomial functor
-/

set_option doc.verso true

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
With {name}`WType.elim` itself, this is the initiality of {lit}`WType β`
among algebras of the polynomial endofunctor {lit}`X ↦ Σ a, β a → X`. -/
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
{name}`WType.elim` at the product carrier {lit}`WType β × γ`, whose
first component reconstructs the subtree, so no new recursion is
introduced. \[Meertens1992\] -/
@[expose] def para {α : Type uA} {β : α → Type uB} (γ : Type uC)
    (fγ : (Σ a : α, β a → WType β × γ) → γ) : WType β → γ :=
  fun w ↦ (elim (WType β × γ) (paraStep γ fγ) w).2

/-- The paramorphism's computation rule: it applies the step to the node's
children paired with their own paramorphisms. Unlike {name}`WType.elim_mk`
this does not hold by {name}`rfl`; it is {lit}`paraStep_fst` under a
{name}`congrArg`. -/
@[simp] theorem para_mk {α : Type uA} {β : α → Type uB} {γ : Type uC}
    (fγ : (Σ a : α, β a → WType β × γ) → γ) (a : α) (f : β a → WType β) :
    para γ fγ (mk a f) = fγ ⟨a, fun b ↦ (f b, para γ fγ (f b))⟩ :=
  congrArg (fun h ↦ fγ ⟨a, h⟩)
    (funext fun b ↦ Prod.ext (paraStep_fst γ fγ (f b)) rfl)

/-- Boolean equality of W-trees: compare the shapes, then compare the
children pointwise over the finite direction type. A fold by
{name}`WType.elim` at the carrier {lit}`WType β → Bool`, so no recursion
is introduced. -/
@[expose] def beq {α : Type uA} {β : α → Type uB} [DecidableEq α]
    [∀ a, FinEnum (β a)] : WType β → WType β → Bool :=
  elim (WType β → Bool) fun x t' ↦
    if h : x.1 = (toSigma t').1 then
      decide (∀ b : β x.1, x.2 b ((toSigma t').2 (h ▸ b)) = true)
    else false

/-- {name}`WType.beq` unfolded on two constructor applications. -/
theorem beq_mk {α : Type uA} {β : α → Type uB} [DecidableEq α]
    [∀ a, FinEnum (β a)] (a : α) (f : β a → WType β) (a' : α)
    (f' : β a' → WType β) :
    beq (mk a f) (mk a' f') =
      if h : a = a' then decide (∀ b : β a, beq (f b) (f' (h ▸ b)) = true) else false :=
  rfl

/-- {name}`WType.beq` decides equality of W-trees. -/
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
only through {name}`Encodable`, which additionally requires the shape and
direction types countable. -/
instance instDecidableEq {α : Type uA} {β : α → Type uB} [DecidableEq α]
    [∀ a, FinEnum (β a)] : DecidableEq (WType β) :=
  fun s t ↦ decidable_of_iff _ (beq_eq_true_iff s t)

end WType
