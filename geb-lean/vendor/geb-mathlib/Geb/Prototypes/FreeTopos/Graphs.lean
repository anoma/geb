/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Converse
public import Geb.Prototypes.FreeTopos.Relations
public import Geb.Prototypes.PartialHorn.Development

set_option doc.verso true in
/-!
# Lean's functions in the topos of functional relations

The topos of Lean's types and functional relations ({name}`Geb.FreeTopos.relTopos`) is a model
of the theory of a topos, by the model of every topos with chosen structure
({name}`Geb.FreeTopos.ChosenTopos.isModel`).
Lean's functions enter it as their graphs ({name}`Geb.FreeTopos.FunRel.ofFun`). A graph
determines its function, and the graphs are closed under the operations with which programs
are built: composition, pairing, copairing, the folds of the natural numbers, of lists and of
rose trees, and currying with evaluation, the currying of a graph being the graph of a function
whose values are graphs; the identities, projections, injections and the constructors of the
data objects are graphs by definition. A sequent a certificate proves, or a development that
checks, is valid in the model, so that at an assignment at which its hypotheses hold, two
functions whose graphs its sides evaluate to are equal: a theorem of the theory about arrows is
a theorem of Lean about functions.

## Main statements

* {lit}`FunRel.ofFun_injective` — a graph determines its function.
* {lit}`FunRel.comp_ofFun`, {lit}`FunRel.pair_ofFun`, {lit}`FunRel.copair_ofFun`,
  {lit}`FunRel.natRec_ofFun`, {lit}`FunRel.listRec_ofFun`, {lit}`FunRel.treeRec_ofFun`,
  {lit}`FunRel.curry_ofFun`, {lit}`FunRel.ev_pair_ofFun` — the operations at graphs are graphs.
* {lit}`eq_of_check`, {lit}`eq_of_checkDevelopment` — the functions whose graphs the sides of a
  proved sequent evaluate to are equal.

## Tags

functional relation, graph of a function, model, soundness, elementary topos
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn Sorts

namespace FunRel

variable {A B C X : Type}

/-- A graph determines its function. -/
theorem ofFun_injective : Function.Injective (ofFun : (A → B) → FunRel A B) :=
  fun _ _ h ↦ Function.graph_injective (congrArg FunRel.rel h)

/-- The composite of graphs is the graph of the composite. -/
theorem comp_ofFun (g : B → C) (f : A → B) : comp (ofFun g) (ofFun f) = ofFun (g ∘ f) :=
  ext_of_le fun _ _ ⟨_, hb, hc⟩ ↦ mem_ofFun.mpr ((congrArg g (mem_ofFun.mp hb)).trans hc)

/-- The pairing of graphs is the graph of the pairing. -/
theorem pair_ofFun (f : X → A) (g : X → B) :
    pair (ofFun f) (ofFun g) = ofFun fun x ↦ (f x, g x) :=
  ext_of_le fun _ _ ⟨ha, hb⟩ ↦ Prod.ext ha hb

/-- The copairing of graphs is the graph of the copairing. -/
theorem copair_ofFun (f : A → C) (g : B → C) : copair (ofFun f) (ofFun g) = ofFun (Sum.elim f g) :=
  ext_of_le fun s c ↦
    Sum.rec (motive := fun s ↦ Sum.elim (fun a ↦ f a = c) (fun b ↦ g b = c) s →
      Sum.elim f g s = c) (fun _ h ↦ h) (fun _ h ↦ h) s

/-- The fold of the natural numbers with graphs is the graph of the recursion. -/
theorem natRec_ofFun (z : Unit → C) (s : C → C) :
    natRec (ofFun z) (ofFun s) = ofFun fun n ↦ Nat.rec (motive := fun _ ↦ C) (z ()) (fun _ ↦ s) n :=
  ext_of_le fun n ↦ Nat.rec
    (motive := fun n ↦ ∀ c, natRel (ofFun z) (ofFun s) n c →
      Nat.rec (motive := fun _ ↦ C) (z ()) (fun _ ↦ s) n = c)
    (fun _ h ↦ h) (fun _ ih _ ⟨c', hc', hc⟩ ↦ (congrArg s (ih c' hc')).trans hc) n

/-- The fold of a list type with graphs is the graph of the right fold. -/
theorem listRec_ofFun (z : Unit → C) (s : A × C → C) :
    listRec A (ofFun z) (ofFun s) = ofFun (List.foldr (fun a c ↦ s (a, c)) (z ())) :=
  ext_of_le fun l ↦ List.rec
    (motive := fun l ↦ ∀ c, listRel (ofFun z) (ofFun s) l c →
      List.foldr (fun a c ↦ s (a, c)) (z ()) l = c)
    (fun _ h ↦ h) (fun a _ ih _ ⟨c', hc', hc⟩ ↦ (congrArg (fun c ↦ s (a, c)) (ih c' hc')).trans hc)
    l

/-- The fold of a rose-tree type with a graph is the graph of the fold. -/
theorem treeRec_ofFun {L : Type} (f : L × List C → C) :
    treeRec (ofFun f) = ofFun (RoseTree.elim fun l cs ↦ f (l, cs)) :=
  ext_of_le fun t ↦ RoseTree.ind
    (P := fun t ↦ ∀ c, treeRel (ofFun f) t c → RoseTree.elim (fun l cs ↦ f (l, cs)) t = c)
    (fun l ts ih c h ↦ by
      rw [treeRel, RoseTree.elim_node] at h
      obtain ⟨cs, hcs, hc⟩ := h
      have he : List.Forall₂ (fun t c ↦ RoseTree.elim (fun l cs ↦ f (l, cs)) t = c) ts cs :=
        forall₂_imp_mem ts cs ih
          ((List.forall₂_map_left_iff (f := treeRel (ofFun f)) (R := fun R c ↦ R c)).mp hcs)
      have hm : ts.map (RoseTree.elim fun l cs ↦ f (l, cs)) = cs := by
        rw [← List.forall₂_eq_eq_eq]
        exact List.forall₂_map_left_iff.mpr he
      rw [RoseTree.elim_node, hm]
      exact hc) t

/-- The functional relation a graph from a product determines at a first component is the
graph of the function of the second component. -/
theorem section'_ofFun (f : C × A → B) (c : C) : section' (ofFun f) c = ofFun fun a ↦ f (c, a) :=
  ext_of_le fun _ _ h ↦ h

/-- The currying of a graph is the graph of the function whose value at a first component is
the graph of the function of the second. -/
theorem curry_ofFun (f : C × A → B) : curry (ofFun f) = ofFun fun c ↦ ofFun fun a ↦ f (c, a) :=
  ext_of_le fun c _ h ↦ (section'_ofFun f c).symm.trans h.symm

/-- Evaluation after the pairing of a graph of graphs with a graph is the graph of the
application. -/
theorem ev_pair_ofFun (F : X → A → B) (g : X → A) :
    comp (ev A B) (pair (ofFun fun x ↦ ofFun (F x)) (ofFun g)) = ofFun fun x ↦ F x (g x) :=
  ext_of_le fun _ _ ⟨⟨_, _⟩, ⟨h₁, h₂⟩, h⟩ ↦ by
    subst h₁ h₂
    exact h

end FunRel

/-- The values of a sequent's sides valid in the topos of types and functional relations, at an
assignment at which its hypotheses hold, that are the graphs of two functions, are the graphs
of one function. -/
theorem eq_of_valid {a : Seq} (hv : a.Valid relTopos.model) {ρ : List relTopos.model.Val}
    (hρ : ρ.map Sigma.fst = a.ctx) (hH : ∀ h ∈ a.hyps, h.Holds relTopos.model ρ) {A B : Type}
    {F G : A → B} (hl : eval relTopos.model ρ a.concl.lhs = Part.some ⟨arr, ⟨A, B, .ofFun F⟩⟩)
    (hr : eval relTopos.model ρ a.concl.rhs = Part.some ⟨arr, ⟨A, B, .ofFun G⟩⟩) : F = G := by
  obtain ⟨w, h₁, h₂⟩ := hv ρ hρ hH
  rw [hl] at h₁
  rw [hr] at h₂
  have h := ChosenTopos.eq_of_arr_eq (T := relTopos)
    ((Part.some_inj.mp h₁).trans (Part.some_inj.mp h₂).symm)
  exact FunRel.ofFun_injective h

/-- A sequent a certificate proves in the theory of a topos, from theorems valid in the topos of
types and functional relations, equates the functions whose graphs its sides evaluate to, at an
assignment at which its hypotheses hold. -/
theorem eq_of_check {E : Array Seq} (hE : ∀ a ∈ E, a.Valid relTopos.model) {c : Tree}
    {Γ : List ℕ} {H : List Eqn} {q : Eqn} (hc : check theory E c Γ H = some q)
    {ρ : List relTopos.model.Val} (hρ : ρ.map Sigma.fst = Γ)
    (hH : ∀ h ∈ H, h.Holds relTopos.model ρ) {A B : Type} {F G : A → B}
    (hl : eval relTopos.model ρ q.lhs = Part.some ⟨arr, ⟨A, B, .ofFun F⟩⟩)
    (hr : eval relTopos.model ρ q.rhs = Part.some ⟨arr, ⟨A, B, .ofFun G⟩⟩) : F = G :=
  eq_of_valid (a := ⟨Γ, H, q⟩)
    (check_sound (List.prefix_refl _) relTopos.isModel hE c Γ H q hc) hρ hH hl hr

/-- A sequent of a development that checks in the theory of a topos equates the functions whose
graphs its sides evaluate to, at an assignment at which its hypotheses hold. -/
theorem eq_of_checkDevelopment {D : Development} (hD : checkDevelopment theory D = true)
    {a : Seq} (ha : a ∈ D.map Prod.fst) {ρ : List relTopos.model.Val}
    (hρ : ρ.map Sigma.fst = a.ctx) (hH : ∀ h ∈ a.hyps, h.Holds relTopos.model ρ) {A B : Type}
    {F G : A → B} (hl : eval relTopos.model ρ a.concl.lhs = Part.some ⟨arr, ⟨A, B, .ofFun F⟩⟩)
    (hr : eval relTopos.model ρ a.concl.rhs = Part.some ⟨arr, ⟨A, B, .ofFun G⟩⟩) : F = G :=
  eq_of_valid (checkDevelopment_sound relTopos.isModel hD a ha) hρ hH hl hr

end Geb.FreeTopos

end
