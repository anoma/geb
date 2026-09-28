/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.FreeTopos.Coproducts
public import Geb.Prototypes.FreeTopos.Converse
public import Geb.Prototypes.FreeTopos.Relations

set_option doc.verso true

/-!
# Lean's functions represented by arrows of functional relations

In the topos of Lean's types and functional relations ({name}`Geb.FreeTopos.relTopos`), an
arrow term of the theory, evaluated at an assignment of objects to its object variables, is a
functional relation. It represents a Lean function between two types of values when each value
is represented by elements of the topos's types, by a relation chosen for each type, and the
functional relation relates a representation of each argument only to representations of the
function's value ({lit}`Represents`). The representations of the topos's constructions are
built from those of their parts: componentwise for products, by the same function for sums and
lists and rose trees, and, for the exponential, a functional relation represents a function when
it relates representations of each argument only to representations of its value, the logical
relation of the simply typed λ-calculus. The arrows of the theory represent, at representations
so built, the Lean functions of the same universal properties: the identity, composition,
projections, pairing, injections and copairing, currying and evaluation, and the folds of lists
and of rose trees.

The representation of a type by itself, by equality, makes a representation of a function the
graph of the function ({name}`Geb.FreeTopos.FunRel.ofFun`) at first-order types; a
representation by another relation changes the carrier, as a bitstring represents the natural
number it enumerates.

## Main definitions

* {lit}`Rep.unit`, {lit}`Rep.prod`, {lit}`Rep.exp`, {lit}`Rep.sum`, {lit}`Rep.list`,
  {lit}`Rep.rose` — the representations of the constructions' values.
* {lit}`Represents` — an arrow term represents a function.

## Main statements

* {lit}`eval_comp`, {lit}`eval_pair`, {lit}`eval_curry`, {lit}`eval_listRec`,
  {lit}`eval_lroseRec` and the others — the values of the operations' applications.
* {lit}`represents_comp`, {lit}`represents_pair`, {lit}`represents_curry`, {lit}`represents_ev`,
  {lit}`represents_copair`, {lit}`represents_caseArr`, {lit}`represents_listRec`,
  {lit}`represents_lroseRec` and the others — the arrows represent the functions of the same
  universal properties.

## Tags

functional relation, logical relation, representation, model, elementary topos
-/

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn Sorts SetRel

/-! The values of the operations' applications. -/

section Eval

variable {ρ : List relTopos.model.Val}

/-- An object term's value is a type. -/
@[irreducible] def ObjVal (ρ : List relTopos.model.Val) (a : Tree) (A : Type) : Prop :=
  eval relTopos.model ρ a = Part.some ⟨obj, ⟨A⟩⟩

/-- An arrow term's value is a functional relation. -/
@[irreducible] def ArrVal (ρ : List relTopos.model.Val) (f : Tree) {A B : Type} (φ : FunRel A B) :
    Prop :=
  eval relTopos.model ρ f = Part.some ⟨arr, ⟨A, B, φ⟩⟩

/-- The value of the terminal object. -/
theorem eval_one : ObjVal ρ one Unit := by
  simp only [ObjVal] at *
  simp only [one, eval_op, List.mapM_nil, Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of the initial object. -/
theorem eval_zero : ObjVal ρ zero Empty := by
  simp only [ObjVal] at *
  simp only [zero, eval_op, List.mapM_nil, Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of the subobject classifier. -/
theorem eval_omega : ObjVal ρ omega Prop := by
  simp only [ObjVal] at *
  simp only [omega, eval_op, List.mapM_nil, Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of the natural numbers object. -/
theorem eval_nat : ObjVal ρ nat ℕ := by
  simp only [ObjVal] at *
  simp only [nat, eval_op, List.mapM_nil, Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of the rose-tree object. -/
theorem eval_rose : ObjVal ρ rose (RoseTree ℕ) := by
  simp only [ObjVal] at *
  simp only [rose, eval_op, List.mapM_nil, Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of a product. -/
theorem eval_prod {a b : Tree} {A B : Type} (ha : ObjVal ρ a A) (hb : ObjVal ρ b B) :
    ObjVal ρ (prod a b) (A × B) := by
  simp only [ObjVal] at *
  simp only [prod, eval_op, List.mapM_cons, List.mapM_nil, ha, hb, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of an exponential. -/
theorem eval_exp {a b : Tree} {A B : Type} (ha : ObjVal ρ a A) (hb : ObjVal ρ b B) :
    ObjVal ρ (exp a b) (FunRel A B) := by
  simp only [ObjVal] at *
  simp only [exp, eval_op, List.mapM_cons, List.mapM_nil, ha, hb, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of a coproduct. -/
theorem eval_coprod {a b : Tree} {A B : Type} (ha : ObjVal ρ a A) (hb : ObjVal ρ b B) :
    ObjVal ρ (coprod a b) (A ⊕ B) := by
  simp only [ObjVal] at *
  simp only [coprod, eval_op, List.mapM_cons, List.mapM_nil, ha, hb, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of a list object. -/
theorem eval_list {a : Tree} {A : Type} (ha : ObjVal ρ a A) : ObjVal ρ (list a) (List A) := by
  simp only [ObjVal] at *
  simp only [list, eval_op, List.mapM_cons, List.mapM_nil, ha, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of a rose-tree object over a type of labels. -/
theorem eval_lrose {a : Tree} {A : Type} (ha : ObjVal ρ a A) :
    ObjVal ρ (lrose a) (RoseTree A) := by
  simp only [ObjVal] at *
  simp only [lrose, eval_op, List.mapM_cons, List.mapM_nil, ha, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of an identity. -/
theorem eval_idt {a : Tree} {A : Type} (ha : ObjVal ρ a A) :
    ArrVal ρ (idt a) (FunRel.ofFun (id : A → A)) := by
  simp only [ObjVal, ArrVal] at *
  simp only [idt, eval_op, List.mapM_cons, List.mapM_nil, ha, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of a composite. -/
theorem eval_comp {f g : Tree} {A B C : Type} {φ : FunRel A B} {ψ : FunRel B C}
    (hf : ArrVal ρ f φ) (hg : ArrVal ρ g ψ) : ArrVal ρ (comp g f) (FunRel.comp ψ φ) := by
  simp only [ArrVal] at *
  simp only [comp, eval_op, List.mapM_cons, List.mapM_nil, hf, hg, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  exact ChosenTopos.mk_eq_some rfl

/-- The value of the arrow to the terminal object. -/
theorem eval_bang {a : Tree} {A : Type} (ha : ObjVal ρ a A) :
    ArrVal ρ (bang a) (FunRel.bang A) := by
  simp only [ObjVal, ArrVal] at *
  simp only [bang, eval_op, List.mapM_cons, List.mapM_nil, ha, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of a first projection. -/
theorem eval_fst {a b : Tree} {A B : Type} (ha : ObjVal ρ a A) (hb : ObjVal ρ b B) :
    ArrVal ρ (fst a b) (FunRel.ofFun (Prod.fst : A × B → A)) := by
  simp only [ObjVal, ArrVal] at *
  simp only [fst, eval_op, List.mapM_cons, List.mapM_nil, ha, hb, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of a second projection. -/
theorem eval_snd {a b : Tree} {A B : Type} (ha : ObjVal ρ a A) (hb : ObjVal ρ b B) :
    ArrVal ρ (snd a b) (FunRel.ofFun (Prod.snd : A × B → B)) := by
  simp only [ObjVal, ArrVal] at *
  simp only [snd, eval_op, List.mapM_cons, List.mapM_nil, ha, hb, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of a pairing. -/
theorem eval_pair {f g : Tree} {X A B : Type} {φ : FunRel X A} {ψ : FunRel X B}
    (hf : ArrVal ρ f φ) (hg : ArrVal ρ g ψ) : ArrVal ρ (pair f g) (FunRel.pair φ ψ) := by
  simp only [ArrVal] at *
  simp only [pair, eval_op, List.mapM_cons, List.mapM_nil, hf, hg, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  exact ChosenTopos.mk_eq_some rfl

/-- The value of a left injection. -/
theorem eval_inl {a b : Tree} {A B : Type} (ha : ObjVal ρ a A) (hb : ObjVal ρ b B) :
    ArrVal ρ (inl a b) (FunRel.ofFun (Sum.inl : A → A ⊕ B)) := by
  simp only [ObjVal, ArrVal] at *
  simp only [inl, eval_op, List.mapM_cons, List.mapM_nil, ha, hb, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of a right injection. -/
theorem eval_inr {a b : Tree} {A B : Type} (ha : ObjVal ρ a A) (hb : ObjVal ρ b B) :
    ArrVal ρ (inr a b) (FunRel.ofFun (Sum.inr : B → A ⊕ B)) := by
  simp only [ObjVal, ArrVal] at *
  simp only [inr, eval_op, List.mapM_cons, List.mapM_nil, ha, hb, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of a copairing. -/
theorem eval_copair {f g : Tree} {A B C : Type} {φ : FunRel A C} {ψ : FunRel B C}
    (hf : ArrVal ρ f φ) (hg : ArrVal ρ g ψ) : ArrVal ρ (copair f g) (FunRel.copair φ ψ) := by
  simp only [ArrVal] at *
  simp only [copair, eval_op, List.mapM_cons, List.mapM_nil, hf, hg, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  exact ChosenTopos.mk_eq_some rfl

/-- The value of an evaluation. -/
theorem eval_ev {a b : Tree} {A B : Type} (ha : ObjVal ρ a A) (hb : ObjVal ρ b B) :
    ArrVal ρ (ev a b) (FunRel.ev A B) := by
  simp only [ObjVal, ArrVal] at *
  simp only [ev, eval_op, List.mapM_cons, List.mapM_nil, ha, hb, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of a currying. -/
theorem eval_curry {c a f : Tree} {C A B : Type} {φ : FunRel (C × A) B} (hc : ObjVal ρ c C)
    (ha : ObjVal ρ a A) (hf : ArrVal ρ f φ) : ArrVal ρ (curry c a f) (FunRel.curry φ) := by
  simp only [ObjVal, ArrVal] at *
  simp only [curry, eval_op, List.mapM_cons, List.mapM_nil, hc, ha, hf,
    Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some]
  exact ChosenTopos.mk_eq_some rfl

/-- The value of an empty list. -/
theorem eval_nil {a : Tree} {A : Type} (ha : ObjVal ρ a A) :
    ArrVal ρ (nil a) (FunRel.ofFun fun _ : Unit ↦ ([] : List A)) := by
  simp only [ObjVal, ArrVal] at *
  simp only [nil, eval_op, List.mapM_cons, List.mapM_nil, ha, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of the construction of lists. -/
theorem eval_cons {a : Tree} {A : Type} (ha : ObjVal ρ a A) :
    ArrVal ρ (cons a) (FunRel.ofFun fun p : A × List A ↦ p.1 :: p.2) := by
  simp only [ObjVal, ArrVal] at *
  simp only [cons, eval_op, List.mapM_cons, List.mapM_nil, ha, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of the fold of a list object. -/
theorem eval_listRec {a z s : Tree} {A C : Type} {φ : FunRel Unit C} {ψ : FunRel (A × C) C}
    (ha : ObjVal ρ a A) (hz : ArrVal ρ z φ) (hs : ArrVal ρ s ψ) :
    ArrVal ρ (listRec a z s) (FunRel.listRec A φ ψ) := by
  simp only [ObjVal, ArrVal] at *
  simp only [listRec, eval_op, List.mapM_cons, List.mapM_nil, ha, hz, hs,
    Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some]
  exact ChosenTopos.mk_eq_some ⟨rfl, rfl, rfl⟩

/-- The value of the construction of rose trees over a type of labels. -/
theorem eval_lnode {a : Tree} {A : Type} (ha : ObjVal ρ a A) :
    ArrVal ρ (lnode a)
      (FunRel.ofFun fun p : A × List (RoseTree A) ↦ RoseTree.node p.1 p.2) := by
  simp only [ObjVal, ArrVal] at *
  simp only [lnode, eval_op, List.mapM_cons, List.mapM_nil, ha, Part.bind_eq_bind,
    Part.bind_some, Part.pure_eq_some]
  rfl

/-- The value of the fold of a rose-tree object over a type of labels. -/
theorem eval_lroseRec {a f : Tree} {A C : Type} {φ : FunRel (A × List C) C} (ha : ObjVal ρ a A)
    (hf : ArrVal ρ f φ) : ArrVal ρ (lroseRec a f) (FunRel.treeRec φ) := by
  simp only [ObjVal, ArrVal] at *
  simp only [lroseRec, eval_op, List.mapM_cons, List.mapM_nil, ha, hf,
    Part.bind_eq_bind, Part.bind_some, Part.pure_eq_some]
  exact ChosenTopos.mk_eq_some rfl

end Eval

/-! The representations. -/

namespace Rep

variable {S S' T A A' B : Type}

/-- The representation of the element of the terminal type. -/
@[nolint unusedArguments]
def unit : Unit → Unit → Prop := fun _ _ ↦ True

/-- The representation of pairs, componentwise. -/
def prod (R : S → A → Prop) (R' : S' → A' → Prop) : S × S' → A × A' → Prop :=
  fun s a ↦ R s.1 a.1 ∧ R' s.2 a.2

/-- The representation of functions by functional relations: a functional relation represents a
function when it relates a representation of each argument only to representations of the
function's value. -/
def exp (R : S → A → Prop) (R' : T → B → Prop) : (S → T) → FunRel A B → Prop :=
  fun F φ ↦ ∀ s a, R s a → ∀ b, a ~[φ.rel] b → R' (F s) b

/-- The representation of the injections into a sum, by the same injection. -/
def sum (R : S → A → Prop) (R' : S' → A' → Prop) : S ⊕ S' → A ⊕ A' → Prop := Sum.LiftRel R R'

/-- The representation of lists, elementwise. -/
def list (R : S → A → Prop) : List S → List A → Prop := List.Forall₂ R

/-- The representation of rose trees, node by node. -/
def rose (R : S → A → Prop) : RoseTree S → RoseTree A → Prop :=
  RoseTree.elim fun l rs t ↦ R l t.label ∧ List.Forall₂ (fun r u ↦ r u) rs t.children

/-- A node represents a node when the labels and the children do. -/
theorem rose_node (R : S → A → Prop) (l : S) (cs : List (RoseTree S)) (l' : A)
    (cs' : List (RoseTree A)) :
    rose R (RoseTree.node l cs) (RoseTree.node l' cs') ↔ R l l' ∧ list (rose R) cs cs' := by
  rw [rose, RoseTree.elim_node, RoseTree.label_node, RoseTree.children_node, list,
    List.forall₂_map_left_iff]

end Rep

/-- An arrow term represents a function between representations: at the assignment {lit}`ρ` it
evaluates to a functional relation from {lit}`A` to {lit}`B` that represents the function
{lit}`F`, relating a representation of each argument only to representations of its value. -/
def Represents (ρ : List relTopos.model.Val) (f : Tree) {S T A B : Type} (R : S → A → Prop)
    (R' : T → B → Prop) (F : S → T) : Prop :=
  ∃ φ : FunRel A B, ArrVal ρ f φ ∧ Rep.exp R R' F φ

section Represent

variable {ρ : List relTopos.model.Val} {S S' S'' T T' A A' A'' B C : Type}

/-- A representation of a function is one of each function it is precomposed or postcomposed
with, at representations related by them. -/
theorem Represents.mono {f : Tree} {R : S → A → Prop} {R' : T → B → Prop} {F : S → T}
    (h : Represents ρ f R R' F) {Q : S' → A → Prop} {Q' : T' → B → Prop} (g : S' → S)
    (k : T → T') (hQ : ∀ s a, Q s a → R (g s) a) (hQ' : ∀ t b, R' t b → Q' (k t) b) :
    Represents ρ f Q Q' (k ∘ F ∘ g) :=
  let ⟨φ, hφ, hF⟩ := h
  ⟨φ, hφ, fun s a hs b hb ↦ hQ' _ _ (hF (g s) a (hQ s a hs) b hb)⟩

/-- A representation of a function is one of an equal function. -/
theorem Represents.congr {f : Tree} {R : S → A → Prop} {R' : T → B → Prop} {F G : S → T}
    (h : Represents ρ f R R' F) (hFG : ∀ s, F s = G s) : Represents ρ f R R' G :=
  let ⟨φ, hφ, hF⟩ := h
  ⟨φ, hφ, fun s a hs b hb ↦ hFG s ▸ hF s a hs b hb⟩

/-- The identity represents the identity. -/
theorem represents_idt {a : Tree} (ha : ObjVal ρ a A) (R : S → A → Prop) :
    Represents ρ (idt a) R R id :=
  ⟨_, eval_idt ha, fun _ _ h _ hb ↦ FunRel.mem_ofFun.mp hb ▸ h⟩

/-- A composite represents the composite. -/
theorem represents_comp {f g : Tree} {R : S → A → Prop} {R' : T → B → Prop}
    {R'' : T' → C → Prop} {F : S → T} {G : T → T'} (hf : Represents ρ f R R' F)
    (hg : Represents ρ g R' R'' G) : Represents ρ (comp g f) R R'' (G ∘ F) :=
  let ⟨_, hφ, hF⟩ := hf
  let ⟨_, hψ, hG⟩ := hg
  ⟨_, eval_comp hφ hψ, fun s a hs _ ⟨b, hb, hc⟩ ↦ hG _ b (hF s a hs b hb) _ hc⟩

/-- The arrow to the terminal object represents the function to the element. -/
theorem represents_bang {a : Tree} (ha : ObjVal ρ a A) (R : S → A → Prop) :
    Represents ρ (bang a) R Rep.unit fun _ ↦ () :=
  ⟨_, eval_bang ha, fun _ _ _ _ _ ↦ trivial⟩

/-- The first projection represents the first projection. -/
theorem represents_fst {a b : Tree} (ha : ObjVal ρ a A) (hb : ObjVal ρ b A')
    (R : S → A → Prop) (R' : S' → A' → Prop) :
    Represents ρ (fst a b) (Rep.prod R R') R Prod.fst :=
  ⟨_, eval_fst ha hb, fun _ _ h _ hc ↦ FunRel.mem_ofFun.mp hc ▸ h.1⟩

/-- The second projection represents the second projection. -/
theorem represents_snd {a b : Tree} (ha : ObjVal ρ a A) (hb : ObjVal ρ b A')
    (R : S → A → Prop) (R' : S' → A' → Prop) :
    Represents ρ (snd a b) (Rep.prod R R') R' Prod.snd :=
  ⟨_, eval_snd ha hb, fun _ _ h _ hc ↦ FunRel.mem_ofFun.mp hc ▸ h.2⟩

/-- A pairing represents the pairing. -/
theorem represents_pair {f g : Tree} {R : S → A → Prop} {R₁ : T → A' → Prop}
    {R₂ : T' → A'' → Prop} {F : S → T} {G : S → T'} (hf : Represents ρ f R R₁ F)
    (hg : Represents ρ g R R₂ G) : Represents ρ (pair f g) R (Rep.prod R₁ R₂) fun s ↦ (F s, G s) :=
  let ⟨_, hφ, hF⟩ := hf
  let ⟨_, hψ, hG⟩ := hg
  ⟨_, eval_pair hφ hψ, fun s a hs _ ⟨h₁, h₂⟩ ↦ ⟨hF s a hs _ h₁, hG s a hs _ h₂⟩⟩

/-- The left injection represents the left injection. -/
theorem represents_inl {a b : Tree} (ha : ObjVal ρ a A) (hb : ObjVal ρ b A')
    (R : S → A → Prop) (R' : S' → A' → Prop) :
    Represents ρ (inl a b) R (Rep.sum R R') Sum.inl :=
  ⟨_, eval_inl ha hb, fun _ _ h _ hc ↦ FunRel.mem_ofFun.mp hc ▸ Sum.LiftRel.inl h⟩

/-- The right injection represents the right injection. -/
theorem represents_inr {a b : Tree} (ha : ObjVal ρ a A) (hb : ObjVal ρ b A')
    (R : S → A → Prop) (R' : S' → A' → Prop) :
    Represents ρ (inr a b) R' (Rep.sum R R') Sum.inr :=
  ⟨_, eval_inr ha hb, fun _ _ h _ hc ↦ FunRel.mem_ofFun.mp hc ▸ Sum.LiftRel.inr h⟩

/-- A copairing represents the copairing. -/
theorem represents_copair {f g : Tree} {R₁ : S → A → Prop} {R₂ : S' → A' → Prop}
    {R : T → B → Prop} {F : S → T} {G : S' → T} (hf : Represents ρ f R₁ R F)
    (hg : Represents ρ g R₂ R G) : Represents ρ (copair f g) (Rep.sum R₁ R₂) R (Sum.elim F G) :=
  let ⟨_, hφ, hF⟩ := hf
  let ⟨_, hψ, hG⟩ := hg
  ⟨_, eval_copair hφ hψ, fun s a hs b hb ↦ by
    cases hs with
    | inl h => exact hF _ _ h b hb
    | inr h => exact hG _ _ h b hb⟩

/-- Evaluation represents application. -/
theorem represents_ev {a b : Tree} (ha : ObjVal ρ a A) (hb : ObjVal ρ b B) (R : S → A → Prop)
    (R' : T → B → Prop) :
    Represents ρ (ev a b) (Rep.prod (Rep.exp R R') R) R' fun p ↦ p.1 p.2 :=
  ⟨_, eval_ev ha hb, fun _ _ h _ hc ↦ h.1 _ _ h.2 _ hc⟩

/-- A currying represents the currying. -/
theorem represents_curry {c a f : Tree} (hc : ObjVal ρ c C) (ha : ObjVal ρ a A)
    {R : S → C → Prop} {R₁ : S' → A → Prop} {R₂ : T → B → Prop} {F : S × S' → T}
    (hf : Represents ρ f (Rep.prod R R₁) R₂ F) :
    Represents ρ (curry c a f) R (Rep.exp R₁ R₂) fun s t ↦ F (s, t) :=
  let ⟨φ, hφ, hF⟩ := hf
  ⟨_, eval_curry hc ha hφ, fun s x hs _ hψ t y ht b hb ↦ by
    obtain rfl := hψ
    exact hF (s, t) (x, y) ⟨hs, ht⟩ b hb⟩

/-- The empty list represents the empty list. -/
theorem represents_nil {a : Tree} (ha : ObjVal ρ a A) (R : S → A → Prop) :
    Represents ρ (nil a) Rep.unit (Rep.list R) fun _ ↦ [] :=
  ⟨_, eval_nil ha, fun _ _ _ _ hb ↦ FunRel.mem_ofFun.mp hb ▸ List.Forall₂.nil⟩

/-- The construction of lists represents the construction. -/
theorem represents_cons {a : Tree} (ha : ObjVal ρ a A) (R : S → A → Prop) :
    Represents ρ (cons a) (Rep.prod R (Rep.list R)) (Rep.list R) fun p ↦ p.1 :: p.2 :=
  ⟨_, eval_cons ha, fun _ _ h _ hb ↦ FunRel.mem_ofFun.mp hb ▸ List.Forall₂.cons h.1 h.2⟩

/-- The fold of a list object represents the right fold. -/
theorem represents_listRec {a z s : Tree} (ha : ObjVal ρ a A) {R : S → A → Prop}
    {R' : T → C → Prop} {Z : Unit → T} {St : S × T → T} (hz : Represents ρ z Rep.unit R' Z)
    (hs : Represents ρ s (Rep.prod R R') R' St) :
    Represents ρ (listRec a z s) (Rep.list R) R' (List.foldr (fun x c ↦ St (x, c)) (Z ())) :=
  let ⟨φ, hφ, hZ⟩ := hz
  let ⟨ψ, hψ, hS⟩ := hs
  ⟨_, eval_listRec ha hφ hψ, fun l l' hl ↦ by
    induction hl with
    | nil => exact fun c hc ↦ hZ () () trivial c hc
    | cons hxy _ ih =>
      intro c ⟨c', hc', hc⟩
      exact hS _ _ ⟨hxy, ih c' hc'⟩ c hc⟩

/-- The construction of rose trees represents the construction. -/
theorem represents_lnode {a : Tree} (ha : ObjVal ρ a A) (R : S → A → Prop) :
    Represents ρ (lnode a) (Rep.prod R (Rep.list (Rep.rose R))) (Rep.rose R)
      fun p ↦ RoseTree.node p.1 p.2 :=
  ⟨_, eval_lnode ha, fun _ _ h _ hb ↦ by
    obtain rfl := FunRel.mem_ofFun.mp hb
    exact (Rep.rose_node R _ _ _ _).mpr h⟩

/-- Two elementwise relations chain to a third, elementwise on the images of the first list. -/
theorem forall₂_chain {α β γ δ : Type} {P : α → β → Prop} {Q : β → γ → Prop}
    {R : δ → γ → Prop} {f : α → δ} :
    ∀ {ts : List α} {bs : List β} {cs : List γ}, List.Forall₂ P ts bs → List.Forall₂ Q bs cs →
      (∀ t ∈ ts, ∀ b c, P t b → Q b c → R (f t) c) → List.Forall₂ R (ts.map f) cs
  | _, _, _, .nil, .nil, _ => .nil
  | _, _, _, .cons hp hps, .cons hq hqs, h =>
    .cons (h _ List.mem_cons_self _ _ hp hq)
      (forall₂_chain hps hqs fun t ht ↦ h t (List.mem_cons_of_mem _ ht))

/-- The fold of a rose-tree object represents the fold of rose trees. -/
theorem represents_lroseRec {a f : Tree} (ha : ObjVal ρ a A) {R : S → A → Prop}
    {R' : T → C → Prop} {Fn : S × List T → T}
    (hf : Represents ρ f (Rep.prod R (Rep.list R')) R' Fn) :
    Represents ρ (lroseRec a f) (Rep.rose R) R' (RoseTree.elim fun l cs ↦ Fn (l, cs)) :=
  let ⟨φ, hφ, hF⟩ := hf
  ⟨_, eval_lroseRec ha hφ, fun s ↦ RoseTree.ind (P := fun s ↦ ∀ a, Rep.rose R s a → ∀ c,
      FunRel.treeRel φ a c → R' (RoseTree.elim (fun l cs ↦ Fn (l, cs)) s) c)
    (fun l ts ih a h c hc ↦ by
      obtain ⟨l', cs', rfl⟩ : ∃ l cs, a = RoseTree.node l cs :=
        ⟨_, _, (RoseTree.node_label_children a).symm⟩
      rw [Rep.rose_node] at h
      rw [FunRel.treeRel, RoseTree.elim_node] at hc
      obtain ⟨ds, hds, hc⟩ := hc
      rw [RoseTree.elim_node]
      exact hF (l, ts.map _) (l', ds)
        ⟨h.1, forall₂_chain h.2 (List.forall₂_map_left_iff.mp hds)
          fun t ht b d hb hd ↦ ih t ht b hb d hd⟩ c hc) s⟩

/-- An application, evaluation after the pairing of a function and an argument, represents the
application. -/
theorem represents_app {a b f g : Tree} (ha : ObjVal ρ a A) (hb : ObjVal ρ b B)
    {R : S → C → Prop} {R₁ : S' → A → Prop} {R₂ : T → B → Prop} {F : S → S' → T} {G : S → S'}
    (hf : Represents ρ f R (Rep.exp R₁ R₂) F) (hg : Represents ρ g R R₁ G) :
    Represents ρ (comp (ev a b) (pair f g)) R R₂ fun s ↦ F s (G s) :=
  represents_comp (represents_pair hf hg) (represents_ev ha hb R₁ R₂)

/-- The case analysis of a coproduct represents the case analysis of a sum. -/
theorem represents_caseArr {a b c : Tree} (ha : ObjVal ρ a A) (hb : ObjVal ρ b A')
    (hc : ObjVal ρ c C) (R₁ : S → A → Prop) (R₂ : S' → A' → Prop) (R : T → C → Prop) :
    Represents ρ (caseArr a b c) (Rep.prod (Rep.exp R₁ R) (Rep.exp R₂ R))
      (Rep.exp (Rep.sum R₁ R₂) R) fun p ↦ Sum.elim p.1 p.2 := by
  have hac := eval_exp ha hc
  have hbc := eval_exp hb hc
  have hP := eval_prod hac hbc
  have hAB := eval_coprod ha hb
  let RP := Rep.prod (Rep.exp R₁ R) (Rep.exp R₂ R)
  have hF : Represents ρ (comp (ev a c) (pair (comp (fst (exp a c) (exp b c)) (fst
      (prod (exp a c) (exp b c)) a)) (snd (prod (exp a c) (exp b c)) a))) (Rep.prod RP R₁) R
      fun p ↦ p.1.1 p.2 :=
    represents_app ha hc (represents_comp (represents_fst hP ha RP R₁)
      (represents_fst hac hbc _ (Rep.exp R₂ R))) (represents_snd hP ha RP R₁)
  have hG : Represents ρ (comp (ev b c) (pair (comp (snd (exp a c) (exp b c)) (fst
      (prod (exp a c) (exp b c)) b)) (snd (prod (exp a c) (exp b c)) b))) (Rep.prod RP R₂) R
      fun p ↦ p.1.2 p.2 :=
    represents_app hb hc (represents_comp (represents_fst hP hb RP R₂)
      (represents_snd hac hbc (Rep.exp R₁ R) _)) (represents_snd hP hb RP R₂)
  have hswap {d : Tree} {D V : Type} (hd : ObjVal ρ d D) {Q : V → D → Prop} :
      Represents ρ (pair (snd d (prod (exp a c) (exp b c))) (fst d (prod (exp a c) (exp b c))))
        (Rep.prod Q RP) (Rep.prod RP Q) fun p ↦ (p.2, p.1) :=
    represents_pair (represents_snd hd hP Q RP) (represents_fst hd hP Q RP)
  refine (represents_curry hP hAB (represents_app hP hc
    (represents_comp (represents_snd hP hAB RP (Rep.sum R₁ R₂))
      (represents_copair (represents_curry ha hP (represents_comp (hswap ha) hF))
        (represents_curry hb hP (represents_comp (hswap hb) hG))))
    (represents_fst hP hAB RP (Rep.sum R₁ R₂)))).congr fun p ↦ funext fun s ↦ ?_
  cases s <;> rfl

end Represent

end Geb.FreeTopos

end
