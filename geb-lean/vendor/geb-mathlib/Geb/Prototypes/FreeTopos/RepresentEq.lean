/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Represent

set_option doc.verso true in
/-!
# The representation of equality

In the topos of types and functional relations the equality of two arrows into one object, the
characteristic map of that object's diagonal after their pairing, relates an element to the
proposition that its images under the two are equal. It therefore represents the equality of
the functions the arrows represent, a function into the propositions, where the representation
of the object relates each value to at most one value in each direction: equal values of the
functions then have equal representations, and conversely. The propositions are represented
by themselves.

## Main definitions

* {lit}`Rep.prop` — the representation of the propositions, by themselves.

## Main statements

* {lit}`isMono_diag` — the diagonal of a type is a monomorphism.
* {lit}`eval_tru`, {lit}`eval_chi` — the values of truth and of a monomorphism's
  characteristic map.
* {lit}`represents_eq` — the equality of two arrows represents the equality of the functions
  they represent.
* {lit}`represents_truth` — an arrow into the subobject classifier represents its truth.
* {lit}`truth_iff_of_represents` — an arrow's truth at an element is the proposition it
  represents at what the element represents.

## Tags

functional relation, logical relation, representation, equality, subobject classifier
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn Sorts SetRel

variable {ρ : List relTopos.model.Val} {S T X A B : Type}

/-- The representation of the propositions, by themselves. -/
def Rep.prop : Prop → Prop → Prop := fun p q ↦ p = q

/-- The diagonal of a type is a monomorphism of the topos of types and functional relations:
its composite with the first projection is the identity. -/
theorem isMono_diag (A : Type) :
    relTopos.IsMono (FunRel.pair (FunRel.ofFun (id : A → A)) (FunRel.ofFun id)) :=
  fun {X : Type} (f g : FunRel X A) h ↦ by
    have key : ∀ k : FunRel X A, FunRel.comp (FunRel.ofFun Prod.fst)
        (FunRel.comp (FunRel.pair (FunRel.ofFun (id : A → A)) (FunRel.ofFun id)) k) = k :=
      fun k ↦ by rw [FunRel.comp_assoc, FunRel.fst_pair, FunRel.ofFun_id_comp]
    exact (key f).symm.trans ((congrArg (FunRel.comp (FunRel.ofFun Prod.fst)) h).trans (key g))

/-- The value of truth. -/
theorem eval_tru : ArrVal ρ tru FunRel.tru := by
  simp only [ArrVal]
  simp only [tru, eval_op, List.mapM_nil, Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of the characteristic map of a monomorphism. -/
theorem eval_chi {m : Tree} {φ : FunRel A B} (hm : ArrVal ρ m φ) (hφ : relTopos.IsMono φ) :
    ArrVal ρ (chi m) (FunRel.chi φ) := by
  simp only [ArrVal] at *
  simp only [chi, eval_op, List.mapM_cons, List.mapM_nil, hm, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  exact ChosenTopos.mk_eq_some (p := relTopos.IsMono φ) @hφ

/-- The equality of two arrows into one object, the characteristic map of the object's diagonal
after their pairing, represents the equality of the functions the arrows represent, where the
representation of the object relates each value to at most one value in each direction. -/
theorem represents_eq {a f g : Tree} (ha : ObjVal ρ a A) {R : S → X → Prop}
    {R₁ : T → A → Prop} {F F' : S → T} (hf : Represents ρ f R R₁ F)
    (hg : Represents ρ g R R₁ F') (hl : ∀ t x y, R₁ t x → R₁ t y → x = y)
    (hr : ∀ t t' x, R₁ t x → R₁ t' x → t = t') :
    Represents ρ (comp (chi (diag a)) (pair f g)) R Rep.prop fun s ↦ F s = F' s := by
  obtain ⟨φ, hφ, hF⟩ := hf
  obtain ⟨ψ, hψ, hG⟩ := hg
  have hd : ArrVal ρ (diag a) (FunRel.pair (FunRel.ofFun (id : A → A)) (FunRel.ofFun id)) :=
    eval_pair (eval_idt ha) (eval_idt ha)
  refine ⟨_, eval_comp (eval_pair hφ hψ) (eval_chi hd (isMono_diag A)), ?_⟩
  rintro s x hs p ⟨⟨b₁, b₂⟩, ⟨hb₁, hb₂⟩, hp⟩
  have hp' : p = ∃ c, c ~[(FunRel.pair (FunRel.ofFun (id : A → A)) (FunRel.ofFun id)).rel]
      (b₁, b₂) := hp
  rw [hp']
  refine propext ⟨fun e ↦ ⟨b₁, rfl, ?_⟩, ?_⟩
  · exact hl _ _ _ (hF s x hs b₁ hb₁) (e ▸ hG s x hs b₂ hb₂)
  · rintro ⟨c, hc₁, hc₂⟩
    have e : b₁ = b₂ := (show c = b₁ from hc₁).symm.trans (show c = b₂ from hc₂)
    exact hr _ _ _ (hF s x hs b₁ hb₁) (e ▸ hG s x hs b₂ hb₂)

/-- An arrow into the subobject classifier represents its truth, the function that sends an
element to the proposition that the arrow relates it to the true proposition, where each
element represents itself: the proposition the arrow relates an element to holds exactly when
it is the true one. -/
theorem represents_truth {f : Tree} {φ : FunRel A Prop} (hf : ArrVal ρ f φ) :
    Represents ρ f (fun a b : A ↦ a = b) Rep.prop fun a ↦ a ~[φ.rel] True :=
  ⟨φ, hf, fun s a hs b hb ↦ by
    subst hs
    exact propext ⟨fun h ↦ φ.unique h hb ▸ trivial, fun h ↦ eq_true h ▸ hb⟩⟩

/-- An arrow term has at most one value between two types. -/
theorem arrVal_unique {f : Tree} {φ ψ : FunRel A B} (hφ : ArrVal ρ f φ) (hψ : ArrVal ρ f ψ) :
    φ = ψ := by
  unfold ArrVal at hφ hψ
  have h := Part.some_injective (hφ.symm.trans hψ)
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at h
  obtain ⟨-, h₁⟩ := Sigma.mk.inj h
  exact eq_of_heq (Sigma.mk.inj (eq_of_heq h₁)).2

/-- Where an arrow into the subobject classifier represents a function into the propositions,
its value relates an element to the true proposition exactly when the function's proposition
holds at what the element represents. -/
theorem truth_iff_of_represents {f : Tree} {φ : FunRel A Prop} (hφ : ArrVal ρ f φ)
    {R : S → A → Prop} {F : S → Prop} (hF : Represents ρ f R Rep.prop F) {s : S} {a : A}
    (hs : R s a) : a ~[φ.rel] True ↔ F s := by
  obtain ⟨ψ, hψ, hrep⟩ := hF
  obtain rfl := arrVal_unique hφ hψ
  refine ⟨fun h ↦ (show F s = True from hrep s a hs True h) ▸ trivial, fun h ↦ ?_⟩
  obtain ⟨b, hb, -⟩ := φ.functional a
  have e : F s = b := hrep s a hs b hb
  exact (eq_true (e ▸ h)) ▸ hb

end Geb.FreeTopos

end
