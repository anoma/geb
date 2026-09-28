/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Theory

set_option doc.verso true in
/-!
# The operations of a model of the theory of an elementary topos

A model of the partial Horn theory {lit}`theory` interprets each operation as a partial
function on sorted values. This module reads the model's objects and arrows as types and its
operations as functions on the arguments at which the axioms make them defined, and states the
axioms as equations between those functions: the domain, the codomain, identities and
composition with the laws of a category; the terminal and initial objects; binary products and
coproducts; equalizers and coequalizers; exponentials; and the subobject classifier, each with
the equations and the uniqueness of its universal property. A monomorphism is an arrow whose
kernel pair's projections are equal, the kernel pair being the equalizer of the arrow's
composites with the projections of the square of its domain. The natural numbers, list and
rose-tree objects are read with their structure maps and folds, each with its fold's equations
and its uniqueness.

The value of an operation defined at its arguments is the value the model's partial function
returns, read at the operation's result sort ({name}`Geb.PartialHorn.Model.get`), so no value is
chosen.

## Main definitions

* {lit}`ToposModel` — a model of the theory with its proof.
* {lit}`ToposModel.domOf`, {lit}`ToposModel.codOf`, {lit}`ToposModel.idOf`,
  {lit}`ToposModel.compOf` — the domain, the codomain, identities and composition.
* {lit}`ToposModel.oneOf`, {lit}`ToposModel.prodOf`, {lit}`ToposModel.eqzOf`,
  {lit}`ToposModel.zeroOf`, {lit}`ToposModel.coprodOf`, {lit}`ToposModel.coeqzOf` — the finite
  limits and colimits, with their universal morphisms.
* {lit}`ToposModel.expOf`, {lit}`ToposModel.evOf`, {lit}`ToposModel.curryOf` — exponentials.
* {lit}`ToposModel.IsMono`, {lit}`ToposModel.omegaOf`, {lit}`ToposModel.truOf`,
  {lit}`ToposModel.chiOf`, {lit}`ToposModel.chiInvOf` — monomorphisms and the subobject
  classifier.
* {lit}`ToposModel.natOf`, {lit}`ToposModel.natRecOf`, {lit}`ToposModel.listOf`,
  {lit}`ToposModel.listRecOf`, {lit}`ToposModel.roseOf`, {lit}`ToposModel.roseRecOf` — the data
  objects and their folds.

## Main statements

* {lit}`ToposModel.compOf_assoc`, {lit}`ToposModel.compOf_idOf`, {lit}`ToposModel.idOf_compOf`
  — the laws of a category.
* {lit}`ToposModel.eq_bangOf`, {lit}`ToposModel.pairOf_eta`, {lit}`ToposModel.eqLiftOf_eta`,
  {lit}`ToposModel.eq_absurdOf`, {lit}`ToposModel.copairOf_eta`,
  {lit}`ToposModel.coeqDescOf_eta`, {lit}`ToposModel.curryOf_eta`, {lit}`ToposModel.eq_chiOf`,
  {lit}`ToposModel.eq_natRecOf`, {lit}`ToposModel.eq_listRecOf`, {lit}`ToposModel.eq_roseRecOf`
  — the uniqueness of each universal morphism.

## Tags

elementary topos, model, partial Horn logic, category
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn Sorts

universe v

/-- A model of the theory of an elementary topos with the data objects. -/
structure ToposModel where
  /-- The model. -/
  model : PartialHorn.Model.{v} sig
  /-- The model satisfies the axioms. -/
  isModel : IsModel theory model

namespace ToposModel

variable (T : ToposModel.{v})

/-- The objects of a model. -/
abbrev Obj : Type v := T.model.Car obj

/-- The arrows of a model. -/
abbrev Ar : Type v := T.model.Car arr

/-- An axiom of the category block, by index, is valid in the model. -/
theorem axCategory (k : ℕ) (hk : k < categoryAxioms.length := by decide) :
    (categoryAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- The simplification of a term's value at explicit values, with the given lemmas, at a
location or the goal: the terms' builders unfold, and the value of each operation's application
is the operation at its arguments' values. -/
local macro "simp_eval" " [" ls:Lean.Parser.Tactic.simpLemma,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [x, dfd, dom, cod, idt, comp, one, bang, prod, fst, snd, pair, eqz, eqIncl,
    eqLift, zero, absurd, coprod, inl, inr, copair, coeqz, coeqProj, coeqDesc, exp, ev, curry,
    omega, tru, chi, chiInv, nat, zeroN, succ, natRec, list, nil, cons, listRec, rose, node,
    roseRec, prodMapLeft, prodMapRight, listMap, monoCond, truthEq, truthIncl, truthLift,
    eval_op, eval_var, List.mapM_cons,
    List.mapM_nil, List.getElem?_cons_zero, List.getElem?_cons_succ, Part.coe_some,
    Part.pure_eq_some, Part.bind_eq_bind, Part.bind_some, $ls,*] $[$loc]?)

/-- Every arrow has a domain. -/
theorem domOf_exists (f : T.Ar) : ∃ o, T.model.op 0 [⟨arr, f⟩] = Part.some ⟨obj, o⟩ := by
  have h : Valid T.model [arr] [] (dfd (dom (x 0))) := T.axCategory 0
  obtain ⟨w, hw, -⟩ := h [⟨arr, f⟩] rfl (by simp)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The domain of an arrow. -/
def domOf (f : T.Ar) : T.Obj := T.model.get (T.domOf_exists f)

/-- The model's domain operation at an arrow. -/
@[simp] theorem op_domOf (f : T.Ar) : T.model.op 0 [⟨arr, f⟩] = Part.some ⟨obj, T.domOf f⟩ :=
  T.model.op_eq_get _

/-- Every arrow has a codomain. -/
theorem codOf_exists (f : T.Ar) : ∃ o, T.model.op 1 [⟨arr, f⟩] = Part.some ⟨obj, o⟩ := by
  have h : Valid T.model [arr] [] (dfd (cod (x 0))) := T.axCategory 1
  obtain ⟨w, hw, -⟩ := h [⟨arr, f⟩] rfl (by simp)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The codomain of an arrow. -/
def codOf (f : T.Ar) : T.Obj := T.model.get (T.codOf_exists f)

/-- The model's codomain operation at an arrow. -/
@[simp] theorem op_codOf (f : T.Ar) : T.model.op 1 [⟨arr, f⟩] = Part.some ⟨obj, T.codOf f⟩ :=
  T.model.op_eq_get _

/-- Every object has an identity. -/
theorem idOf_exists (a : T.Obj) : ∃ i, T.model.op 2 [⟨obj, a⟩] = Part.some ⟨arr, i⟩ := by
  have h : Valid T.model [obj] [] (dfd (idt (x 0))) := T.axCategory 2
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩] rfl (by simp)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The identity of an object. -/
def idOf (a : T.Obj) : T.Ar := T.model.get (T.idOf_exists a)

/-- The model's identity operation at an object. -/
@[simp] theorem op_idOf (a : T.Obj) : T.model.op 2 [⟨obj, a⟩] = Part.some ⟨arr, T.idOf a⟩ :=
  T.model.op_eq_get _

/-- Two arrows compose when the codomain of the first is the domain of the second. -/
theorem compOf_exists {g f : T.Ar} (h : T.codOf f = T.domOf g) :
    ∃ c, T.model.op 3 [⟨arr, g⟩, ⟨arr, f⟩] = Part.some ⟨arr, c⟩ := by
  have hv : Valid T.model [arr, arr] [⟨cod (x 1), dom (x 0)⟩] (dfd (comp (x 0) (x 1))) :=
    T.axCategory 4
  obtain ⟨w, hw, -⟩ := hv [⟨arr, g⟩, ⟨arr, f⟩] rfl (by
    simp only [List.mem_singleton, forall_eq, Eqn.Holds]
    simp_eval [op_codOf, op_domOf, h]
    exact ⟨_, rfl, rfl⟩)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The composite of {lit}`g` after {lit}`f`. -/
def compOf (g f : T.Ar) (h : T.codOf f = T.domOf g) : T.Ar := T.model.get (T.compOf_exists h)

/-- The model's composition at two composable arrows. -/
@[simp] theorem op_compOf {g f : T.Ar} (h : T.codOf f = T.domOf g) :
    T.model.op 3 [⟨arr, g⟩, ⟨arr, f⟩] = Part.some ⟨arr, T.compOf g f h⟩ :=
  T.model.op_eq_get _

/-- Two values an equation's sides have at an assignment where it holds are equal. -/
theorem holds_eq {ρ : List T.model.Val} {q : Eqn} (h : q.Holds T.model ρ) {a b : T.model.Val}
    (ha : eval T.model ρ q.lhs = Part.some a) (hb : eval T.model ρ q.rhs = Part.some b) :
    a = b := by
  obtain ⟨w, h1, h2⟩ := h
  rw [ha] at h1
  rw [hb] at h2
  exact (Part.some_inj.mp h1).trans (Part.some_inj.mp h2).symm

/-- Two values of one sort are equal when they are equal as sorted values. -/
theorem val_inj {s : ℕ} {a b : T.model.Car s} (h : (⟨s, a⟩ : T.model.Val) = ⟨s, b⟩) : a = b :=
  eq_of_heq (Sigma.mk.inj h).2

/-- The domain of a composite is the domain of its first arrow. -/
theorem domOf_compOf {g f : T.Ar} (h : T.codOf f = T.domOf g) :
    T.domOf (T.compOf g f h) = T.domOf f := by
  have hv : Valid T.model [arr, arr] [dfd (comp (x 0) (x 1))]
      ⟨dom (comp (x 0) (x 1)), dom (x 1)⟩ := T.axCategory 5
  have hq := hv [⟨arr, g⟩, ⟨arr, f⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨arr, T.compOf g f h⟩, by simp_eval [T.op_compOf h], by simp_eval [T.op_compOf h]⟩)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_compOf h, op_domOf])
    (by simp_eval [op_domOf])

/-- The codomain of a composite is the codomain of its second arrow. -/
theorem codOf_compOf {g f : T.Ar} (h : T.codOf f = T.domOf g) :
    T.codOf (T.compOf g f h) = T.codOf g := by
  have hv : Valid T.model [arr, arr] [dfd (comp (x 0) (x 1))]
      ⟨cod (comp (x 0) (x 1)), cod (x 0)⟩ := T.axCategory 6
  have hq := hv [⟨arr, g⟩, ⟨arr, f⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨arr, T.compOf g f h⟩, by simp_eval [T.op_compOf h], by simp_eval [T.op_compOf h]⟩)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_compOf h, op_codOf])
    (by simp_eval [op_codOf])

/-- The domain of an identity. -/
theorem domOf_idOf (a : T.Obj) : T.domOf (T.idOf a) = a := by
  have hv : Valid T.model [obj] [] ⟨dom (idt (x 0)), x 0⟩ := T.axCategory 8
  exact T.val_inj <| T.holds_eq (hv [⟨obj, a⟩] rfl (by simp)) (by simp_eval [op_idOf, op_domOf])
    (by simp_eval [])

/-- The codomain of an identity. -/
theorem codOf_idOf (a : T.Obj) : T.codOf (T.idOf a) = a := by
  have hv : Valid T.model [obj] [] ⟨cod (idt (x 0)), x 0⟩ := T.axCategory 9
  exact T.val_inj <| T.holds_eq (hv [⟨obj, a⟩] rfl (by simp)) (by simp_eval [op_idOf, op_codOf])
    (by simp_eval [])

/-- An arrow after the identity of its domain is the arrow. -/
theorem compOf_idOf (f : T.Ar) :
    T.compOf f (T.idOf (T.domOf f)) (T.codOf_idOf _) = f := by
  have hv : Valid T.model [arr] [] ⟨comp (x 0) (idt (dom (x 0))), x 0⟩ := T.axCategory 10
  exact T.val_inj <| T.holds_eq (hv [⟨arr, f⟩] rfl (by simp))
    (by simp_eval [op_domOf, op_idOf, T.op_compOf (T.codOf_idOf _)]) (by simp_eval [])

/-- The identity of an arrow's codomain after the arrow is the arrow. -/
theorem idOf_compOf (f : T.Ar) :
    T.compOf (T.idOf (T.codOf f)) f (T.domOf_idOf _).symm = f := by
  have hv : Valid T.model [arr] [] ⟨comp (idt (cod (x 0))) (x 0), x 0⟩ := T.axCategory 11
  exact T.val_inj <| T.holds_eq (hv [⟨arr, f⟩] rfl (by simp))
    (by simp_eval [op_codOf, op_idOf, T.op_compOf (T.domOf_idOf _).symm]) (by simp_eval [])

/-- Composition is associative. -/
theorem compOf_assoc {h g f : T.Ar} (hgf : T.codOf f = T.domOf g)
    (hhg : T.codOf g = T.domOf h) :
    T.compOf h (T.compOf g f hgf) ((T.codOf_compOf hgf).trans hhg) =
      T.compOf (T.compOf h g hhg) f (hgf.trans (T.domOf_compOf hhg).symm) := by
  have hv : Valid T.model [arr, arr, arr] [dfd (comp (x 0) (comp (x 1) (x 2)))]
      ⟨comp (x 0) (comp (x 1) (x 2)), comp (comp (x 0) (x 1)) (x 2)⟩ := T.axCategory 7
  have hq := hv [⟨arr, h⟩, ⟨arr, g⟩, ⟨arr, f⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨arr, T.compOf h (T.compOf g f hgf) ((T.codOf_compOf hgf).trans hhg)⟩,
      by simp_eval [T.op_compOf hgf, T.op_compOf ((T.codOf_compOf hgf).trans hhg)],
      by simp_eval [T.op_compOf hgf, T.op_compOf ((T.codOf_compOf hgf).trans hhg)]⟩)
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [T.op_compOf hgf, T.op_compOf ((T.codOf_compOf hgf).trans hhg)])
    (by simp_eval [T.op_compOf hhg, T.op_compOf (hgf.trans (T.domOf_compOf hhg).symm)])

/-- Composites of equal arrows are equal, whatever the proofs that they compose. -/
theorem compOf_congr {g g' f f' : T.Ar} (hg : g = g') (hf : f = f') (h : T.codOf f = T.domOf g)
    (h' : T.codOf f' = T.domOf g') : T.compOf g f h = T.compOf g' f' h' := by
  subst hg hf
  rfl

/-- An axiom of the terminal block, by index, is valid in the model. -/
theorem axTerminal (k : ℕ) (hk : k < terminalAxioms.length := by decide) :
    (terminalAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- The terminal object is defined. -/
theorem oneOf_exists : ∃ o, T.model.op 4 [] = Part.some ⟨obj, o⟩ := by
  have h : Valid T.model [] [] (dfd one) := T.axTerminal 0
  obtain ⟨w, hw, -⟩ := h [] rfl (by simp)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The terminal object. -/
def oneOf : T.Obj := T.model.get T.oneOf_exists

/-- The model's terminal object. -/
@[simp] theorem op_oneOf : T.model.op 4 [] = Part.some ⟨obj, T.oneOf⟩ := T.model.op_eq_get _

/-- Every object has a morphism to the terminal object. -/
theorem bangOf_exists (a : T.Obj) : ∃ f, T.model.op 5 [⟨obj, a⟩] = Part.some ⟨arr, f⟩ := by
  have h : Valid T.model [obj] [] ⟨dom (bang (x 0)), x 0⟩ := T.axTerminal 1
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩] rfl (by simp)
  simp_eval [] at hw
  obtain ⟨l, hl, -⟩ := part_bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := part_bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- The morphism from an object to the terminal object. -/
def bangOf (a : T.Obj) : T.Ar := T.model.get (T.bangOf_exists a)

/-- The model's morphism to the terminal object. -/
@[simp] theorem op_bangOf (a : T.Obj) : T.model.op 5 [⟨obj, a⟩] = Part.some ⟨arr, T.bangOf a⟩ :=
  T.model.op_eq_get _

/-- The domain of the morphism from an object to the terminal object is that object. -/
theorem domOf_bangOf (a : T.Obj) : T.domOf (T.bangOf a) = a := by
  have h : Valid T.model [obj] [] ⟨dom (bang (x 0)), x 0⟩ := T.axTerminal 1
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩] rfl (by simp)) (by simp_eval [op_bangOf, op_domOf])
    (by simp_eval [])

/-- The codomain of the morphism from an object to the terminal object is the terminal
object. -/
theorem codOf_bangOf (a : T.Obj) : T.codOf (T.bangOf a) = T.oneOf := by
  have h : Valid T.model [obj] [] ⟨cod (bang (x 0)), one⟩ := T.axTerminal 2
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩] rfl (by simp)) (by simp_eval [op_bangOf, op_codOf])
    (by simp_eval [op_oneOf])

/-- A morphism to the terminal object is the morphism from its domain. -/
theorem eq_bangOf {f : T.Ar} (hf : T.codOf f = T.oneOf) : f = T.bangOf (T.domOf f) := by
  have h : Valid T.model [arr] [⟨cod (x 0), one⟩] ⟨x 0, bang (dom (x 0))⟩ := T.axTerminal 3
  have hq := h [⟨arr, f⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨obj, T.oneOf⟩, by simp_eval [op_codOf, hf], by simp_eval [op_oneOf]⟩)
  exact T.val_inj <| T.holds_eq hq (by simp_eval []) (by simp_eval [op_domOf, op_bangOf])

/-- An axiom of the product block, by index, is valid in the model. -/
theorem axProduct (k : ℕ) (hk : k < productAxioms.length := by decide) :
    (productAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- Every two objects have a product. -/
theorem prodOf_exists (a b : T.Obj) :
    ∃ p, T.model.op 6 [⟨obj, a⟩, ⟨obj, b⟩] = Part.some ⟨obj, p⟩ := by
  have h : Valid T.model [obj, obj] [] (dfd (prod (x 0) (x 1))) := T.axProduct 0
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The product of two objects. -/
def prodOf (a b : T.Obj) : T.Obj := T.model.get (T.prodOf_exists a b)

/-- The model's product of two objects. -/
@[simp] theorem op_prodOf (a b : T.Obj) :
    T.model.op 6 [⟨obj, a⟩, ⟨obj, b⟩] = Part.some ⟨obj, T.prodOf a b⟩ :=
  T.model.op_eq_get _

/-- Every product has a first projection. -/
theorem fstOf_exists (a b : T.Obj) :
    ∃ f, T.model.op 7 [⟨obj, a⟩, ⟨obj, b⟩] = Part.some ⟨arr, f⟩ := by
  have h : Valid T.model [obj, obj] [] ⟨dom (fst (x 0) (x 1)), prod (x 0) (x 1)⟩ :=
    T.axProduct 1
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp)
  simp_eval [] at hw
  obtain ⟨l, hl, -⟩ := part_bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := part_bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- The first projection of a product. -/
def fstOf (a b : T.Obj) : T.Ar := T.model.get (T.fstOf_exists a b)

/-- The model's first projection. -/
@[simp] theorem op_fstOf (a b : T.Obj) :
    T.model.op 7 [⟨obj, a⟩, ⟨obj, b⟩] = Part.some ⟨arr, T.fstOf a b⟩ :=
  T.model.op_eq_get _

/-- Every product has a second projection. -/
theorem sndOf_exists (a b : T.Obj) :
    ∃ f, T.model.op 8 [⟨obj, a⟩, ⟨obj, b⟩] = Part.some ⟨arr, f⟩ := by
  have h : Valid T.model [obj, obj] [] ⟨dom (snd (x 0) (x 1)), prod (x 0) (x 1)⟩ :=
    T.axProduct 3
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp)
  simp_eval [] at hw
  obtain ⟨l, hl, -⟩ := part_bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := part_bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- The second projection of a product. -/
def sndOf (a b : T.Obj) : T.Ar := T.model.get (T.sndOf_exists a b)

/-- The model's second projection. -/
@[simp] theorem op_sndOf (a b : T.Obj) :
    T.model.op 8 [⟨obj, a⟩, ⟨obj, b⟩] = Part.some ⟨arr, T.sndOf a b⟩ :=
  T.model.op_eq_get _

/-- The domain of the first projection is the product. -/
theorem domOf_fstOf (a b : T.Obj) : T.domOf (T.fstOf a b) = T.prodOf a b := by
  have h : Valid T.model [obj, obj] [] ⟨dom (fst (x 0) (x 1)), prod (x 0) (x 1)⟩ :=
    T.axProduct 1
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp))
    (by simp_eval [op_fstOf, op_domOf]) (by simp_eval [op_prodOf])

/-- The codomain of the first projection is the first factor. -/
theorem codOf_fstOf (a b : T.Obj) : T.codOf (T.fstOf a b) = a := by
  have h : Valid T.model [obj, obj] [] ⟨cod (fst (x 0) (x 1)), x 0⟩ := T.axProduct 2
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp))
    (by simp_eval [op_fstOf, op_codOf]) (by simp_eval [])

/-- The domain of the second projection is the product. -/
theorem domOf_sndOf (a b : T.Obj) : T.domOf (T.sndOf a b) = T.prodOf a b := by
  have h : Valid T.model [obj, obj] [] ⟨dom (snd (x 0) (x 1)), prod (x 0) (x 1)⟩ :=
    T.axProduct 3
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp))
    (by simp_eval [op_sndOf, op_domOf]) (by simp_eval [op_prodOf])

/-- The codomain of the second projection is the second factor. -/
theorem codOf_sndOf (a b : T.Obj) : T.codOf (T.sndOf a b) = b := by
  have h : Valid T.model [obj, obj] [] ⟨cod (snd (x 0) (x 1)), x 1⟩ := T.axProduct 4
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp))
    (by simp_eval [op_sndOf, op_codOf]) (by simp_eval [])

/-- Two morphisms of one domain have a pairing. -/
theorem pairOf_exists {f g : T.Ar} (h : T.domOf f = T.domOf g) :
    ∃ p, T.model.op 9 [⟨arr, f⟩, ⟨arr, g⟩] = Part.some ⟨arr, p⟩ := by
  have hv : Valid T.model [arr, arr] [⟨dom (x 0), dom (x 1)⟩] (dfd (pair (x 0) (x 1))) :=
    T.axProduct 6
  obtain ⟨w, hw, -⟩ := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨obj, T.domOf g⟩, by simp_eval [op_domOf, h], by simp_eval [op_domOf]⟩)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The pairing of two morphisms of one domain. -/
def pairOf (f g : T.Ar) (h : T.domOf f = T.domOf g) : T.Ar := T.model.get (T.pairOf_exists h)

/-- The model's pairing. -/
@[simp] theorem op_pairOf {f g : T.Ar} (h : T.domOf f = T.domOf g) :
    T.model.op 9 [⟨arr, f⟩, ⟨arr, g⟩] = Part.some ⟨arr, T.pairOf f g h⟩ :=
  T.model.op_eq_get _

/-- A pairing is defined at its components. -/
theorem holds_pairOf {f g : T.Ar} (h : T.domOf f = T.domOf g) :
    (dfd (pair (x 0) (x 1))).Holds T.model [⟨arr, f⟩, ⟨arr, g⟩] :=
  ⟨⟨arr, T.pairOf f g h⟩, by simp_eval [T.op_pairOf h], by simp_eval [T.op_pairOf h]⟩

/-- The domain of a pairing is its components' domain. -/
theorem domOf_pairOf {f g : T.Ar} (h : T.domOf f = T.domOf g) :
    T.domOf (T.pairOf f g h) = T.domOf f := by
  have hv : Valid T.model [arr, arr] [dfd (pair (x 0) (x 1))]
      ⟨dom (pair (x 0) (x 1)), dom (x 0)⟩ := T.axProduct 7
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_pairOf h)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_pairOf h, op_domOf])
    (by simp_eval [op_domOf])

/-- The codomain of a pairing is the product of its components' codomains. -/
theorem codOf_pairOf {f g : T.Ar} (h : T.domOf f = T.domOf g) :
    T.codOf (T.pairOf f g h) = T.prodOf (T.codOf f) (T.codOf g) := by
  have hv : Valid T.model [arr, arr] [dfd (pair (x 0) (x 1))]
      ⟨cod (pair (x 0) (x 1)), prod (cod (x 0)) (cod (x 1))⟩ := T.axProduct 8
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_pairOf h)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_pairOf h, op_codOf])
    (by simp_eval [op_codOf, op_prodOf])

/-- The first projection after a pairing is its first component. -/
theorem fstOf_pairOf {f g : T.Ar} (h : T.domOf f = T.domOf g) :
    T.compOf (T.fstOf (T.codOf f) (T.codOf g)) (T.pairOf f g h)
      ((T.codOf_pairOf h).trans (T.domOf_fstOf _ _).symm) = f := by
  have hv : Valid T.model [arr, arr] [dfd (pair (x 0) (x 1))]
      ⟨comp (fst (cod (x 0)) (cod (x 1))) (pair (x 0) (x 1)), x 0⟩ := T.axProduct 9
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_pairOf h)
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [T.op_pairOf h, op_codOf, op_fstOf,
      T.op_compOf ((T.codOf_pairOf h).trans (T.domOf_fstOf _ _).symm)])
    (by simp_eval [])

/-- The second projection after a pairing is its second component. -/
theorem sndOf_pairOf {f g : T.Ar} (h : T.domOf f = T.domOf g) :
    T.compOf (T.sndOf (T.codOf f) (T.codOf g)) (T.pairOf f g h)
      ((T.codOf_pairOf h).trans (T.domOf_sndOf _ _).symm) = g := by
  have hv : Valid T.model [arr, arr] [dfd (pair (x 0) (x 1))]
      ⟨comp (snd (cod (x 0)) (cod (x 1))) (pair (x 0) (x 1)), x 1⟩ := T.axProduct 10
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_pairOf h)
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [T.op_pairOf h, op_codOf, op_sndOf,
      T.op_compOf ((T.codOf_pairOf h).trans (T.domOf_sndOf _ _).symm)])
    (by simp_eval [])

/-- A morphism into a product is the pairing of its composites with the projections. -/
theorem pairOf_eta {k : T.Ar} {a b : T.Obj} (h : T.codOf k = T.prodOf a b) :
    T.pairOf (T.compOf (T.fstOf a b) k (h.trans (T.domOf_fstOf a b).symm))
      (T.compOf (T.sndOf a b) k (h.trans (T.domOf_sndOf a b).symm))
      ((T.domOf_compOf _).trans (T.domOf_compOf _).symm) = k := by
  have hv : Valid T.model [arr, obj, obj] [⟨cod (x 0), prod (x 1) (x 2)⟩]
      ⟨pair (comp (fst (x 1) (x 2)) (x 0)) (comp (snd (x 1) (x 2)) (x 0)), x 0⟩ :=
    T.axProduct 11
  have hq := hv [⟨arr, k⟩, ⟨obj, a⟩, ⟨obj, b⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨obj, T.prodOf a b⟩, by simp_eval [op_codOf, h], by simp_eval [op_prodOf]⟩)
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [op_fstOf, op_sndOf, T.op_compOf (h.trans (T.domOf_fstOf a b).symm),
      T.op_compOf (h.trans (T.domOf_sndOf a b).symm),
      T.op_pairOf ((T.domOf_compOf (h.trans (T.domOf_fstOf a b).symm)).trans
        (T.domOf_compOf (h.trans (T.domOf_sndOf a b).symm)).symm)])
    (by simp_eval [])

/-- An axiom of the equalizer block, by index, is valid in the model. -/
theorem axEqualizer (k : ℕ) (hk : k < equalizerAxioms.length := by decide) :
    (equalizerAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- Two arrows are parallel: they have one domain and one codomain. -/
def Par (f g : T.Ar) : Prop := T.domOf f = T.domOf g ∧ T.codOf f = T.codOf g

/-- Two parallel arrows have an equalizer. -/
theorem eqzOf_exists {f g : T.Ar} (hp : T.Par f g) :
    ∃ e, T.model.op 10 [⟨arr, f⟩, ⟨arr, g⟩] = Part.some ⟨obj, e⟩ := by
  have hv : Valid T.model [arr, arr] [⟨dom (x 0), dom (x 1)⟩, ⟨cod (x 0), cod (x 1)⟩]
      (dfd (eqz (x 0) (x 1))) := T.axEqualizer 2
  obtain ⟨w, hw, -⟩ := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    exact ⟨⟨⟨obj, T.domOf g⟩, by simp_eval [op_domOf, hp.1], by simp_eval [op_domOf]⟩,
      ⟨⟨obj, T.codOf g⟩, by simp_eval [op_codOf, hp.2], by simp_eval [op_codOf]⟩⟩)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The equalizer of two parallel arrows. -/
def eqzOf (f g : T.Ar) (hp : T.Par f g) : T.Obj := T.model.get (T.eqzOf_exists hp)

/-- The model's equalizer. -/
@[simp] theorem op_eqzOf {f g : T.Ar} (hp : T.Par f g) :
    T.model.op 10 [⟨arr, f⟩, ⟨arr, g⟩] = Part.some ⟨obj, T.eqzOf f g hp⟩ :=
  T.model.op_eq_get _

/-- The equalizer of two parallel arrows is defined at them. -/
theorem holds_eqzOf {f g : T.Ar} (hp : T.Par f g) :
    (dfd (eqz (x 0) (x 1))).Holds T.model [⟨arr, f⟩, ⟨arr, g⟩] :=
  ⟨⟨obj, T.eqzOf f g hp⟩, by simp_eval [T.op_eqzOf hp], by simp_eval [T.op_eqzOf hp]⟩

/-- An equalizer has an inclusion. -/
theorem eqInclOf_exists {f g : T.Ar} (hp : T.Par f g) :
    ∃ e, T.model.op 11 [⟨arr, f⟩, ⟨arr, g⟩] = Part.some ⟨arr, e⟩ := by
  have hv : Valid T.model [arr, arr] [dfd (eqz (x 0) (x 1))] (dfd (eqIncl (x 0) (x 1))) :=
    T.axEqualizer 4
  obtain ⟨w, hw, -⟩ := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_eqzOf hp)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The inclusion of the equalizer of two parallel arrows. -/
def eqInclOf (f g : T.Ar) (hp : T.Par f g) : T.Ar := T.model.get (T.eqInclOf_exists hp)

/-- The model's inclusion of an equalizer. -/
@[simp] theorem op_eqInclOf {f g : T.Ar} (hp : T.Par f g) :
    T.model.op 11 [⟨arr, f⟩, ⟨arr, g⟩] = Part.some ⟨arr, T.eqInclOf f g hp⟩ :=
  T.model.op_eq_get _

/-- The domain of an equalizer's inclusion is the equalizer. -/
theorem domOf_eqInclOf {f g : T.Ar} (hp : T.Par f g) :
    T.domOf (T.eqInclOf f g hp) = T.eqzOf f g hp := by
  have hv : Valid T.model [arr, arr] [dfd (eqz (x 0) (x 1))]
      ⟨dom (eqIncl (x 0) (x 1)), eqz (x 0) (x 1)⟩ := T.axEqualizer 5
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_eqzOf hp)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_eqInclOf hp, op_domOf])
    (by simp_eval [T.op_eqzOf hp])

/-- The codomain of an equalizer's inclusion is the arrows' domain. -/
theorem codOf_eqInclOf {f g : T.Ar} (hp : T.Par f g) :
    T.codOf (T.eqInclOf f g hp) = T.domOf f := by
  have hv : Valid T.model [arr, arr] [dfd (eqz (x 0) (x 1))]
      ⟨cod (eqIncl (x 0) (x 1)), dom (x 0)⟩ := T.axEqualizer 6
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_eqzOf hp)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_eqInclOf hp, op_codOf])
    (by simp_eval [op_domOf])

/-- An equalizer's inclusion equalizes the arrows. -/
theorem compOf_eqInclOf {f g : T.Ar} (hp : T.Par f g) :
    T.compOf f (T.eqInclOf f g hp) (T.codOf_eqInclOf hp) =
      T.compOf g (T.eqInclOf f g hp) ((T.codOf_eqInclOf hp).trans hp.1) := by
  have hv : Valid T.model [arr, arr] [dfd (eqz (x 0) (x 1))]
      ⟨comp (x 0) (eqIncl (x 0) (x 1)), comp (x 1) (eqIncl (x 0) (x 1))⟩ := T.axEqualizer 7
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_eqzOf hp)
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [T.op_eqInclOf hp, T.op_compOf (T.codOf_eqInclOf hp)])
    (by simp_eval [T.op_eqInclOf hp, T.op_compOf ((T.codOf_eqInclOf hp).trans hp.1)])

/-- A morphism that equalizes two parallel arrows factors through their equalizer. -/
theorem eqLiftOf_exists {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf k = T.domOf f)
    (he : T.compOf f k hk = T.compOf g k (hk.trans hp.1)) :
    ∃ l, T.model.op 12 [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] = Part.some ⟨arr, l⟩ := by
  have hv : Valid T.model [arr, arr, arr]
      [dfd (eqz (x 0) (x 1)), ⟨comp (x 0) (x 2), comp (x 1) (x 2)⟩]
      (dfd (eqLift (x 0) (x 1) (x 2))) := T.axEqualizer 10
  obtain ⟨w, hw, -⟩ := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    exact ⟨⟨⟨obj, T.eqzOf f g hp⟩, by simp_eval [T.op_eqzOf hp], by simp_eval [T.op_eqzOf hp]⟩,
      ⟨⟨arr, T.compOf g k (hk.trans hp.1)⟩, by simp_eval [T.op_compOf hk, he],
        by simp_eval [T.op_compOf (hk.trans hp.1)]⟩⟩)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The factorization through the equalizer of two parallel arrows of a morphism that
equalizes them. -/
def eqLiftOf (f g k : T.Ar) (hp : T.Par f g) (hk : T.codOf k = T.domOf f)
    (he : T.compOf f k hk = T.compOf g k (hk.trans hp.1)) : T.Ar :=
  T.model.get (T.eqLiftOf_exists hp hk he)

/-- The model's factorization through an equalizer. -/
@[simp] theorem op_eqLiftOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf k = T.domOf f)
    (he : T.compOf f k hk = T.compOf g k (hk.trans hp.1)) :
    T.model.op 12 [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] = Part.some ⟨arr, T.eqLiftOf f g k hp hk he⟩ :=
  T.model.op_eq_get _

/-- A factorization through an equalizer is defined at its arguments. -/
theorem holds_eqLiftOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf k = T.domOf f)
    (he : T.compOf f k hk = T.compOf g k (hk.trans hp.1)) :
    (dfd (eqLift (x 0) (x 1) (x 2))).Holds T.model [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] :=
  ⟨⟨arr, T.eqLiftOf f g k hp hk he⟩, by simp_eval [T.op_eqLiftOf hp hk he],
    by simp_eval [T.op_eqLiftOf hp hk he]⟩

/-- The domain of a factorization through an equalizer is the factored morphism's. -/
theorem domOf_eqLiftOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf k = T.domOf f)
    (he : T.compOf f k hk = T.compOf g k (hk.trans hp.1)) :
    T.domOf (T.eqLiftOf f g k hp hk he) = T.domOf k := by
  have hv : Valid T.model [arr, arr, arr] [dfd (eqLift (x 0) (x 1) (x 2))]
      ⟨dom (eqLift (x 0) (x 1) (x 2)), dom (x 2)⟩ := T.axEqualizer 11
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] rfl (by simpa using T.holds_eqLiftOf hp hk he)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_eqLiftOf hp hk he, op_domOf])
    (by simp_eval [op_domOf])

/-- The codomain of a factorization through an equalizer is the equalizer. -/
theorem codOf_eqLiftOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf k = T.domOf f)
    (he : T.compOf f k hk = T.compOf g k (hk.trans hp.1)) :
    T.codOf (T.eqLiftOf f g k hp hk he) = T.eqzOf f g hp := by
  have hv : Valid T.model [arr, arr, arr] [dfd (eqLift (x 0) (x 1) (x 2))]
      ⟨cod (eqLift (x 0) (x 1) (x 2)), eqz (x 0) (x 1)⟩ := T.axEqualizer 12
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] rfl (by simpa using T.holds_eqLiftOf hp hk he)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_eqLiftOf hp hk he, op_codOf])
    (by simp_eval [T.op_eqzOf hp])

/-- The inclusion after a factorization through an equalizer is the factored morphism. -/
theorem eqInclOf_eqLiftOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf k = T.domOf f)
    (he : T.compOf f k hk = T.compOf g k (hk.trans hp.1)) :
    T.compOf (T.eqInclOf f g hp) (T.eqLiftOf f g k hp hk he)
      ((T.codOf_eqLiftOf hp hk he).trans (T.domOf_eqInclOf hp).symm) = k := by
  have hv : Valid T.model [arr, arr, arr] [dfd (eqLift (x 0) (x 1) (x 2))]
      ⟨comp (eqIncl (x 0) (x 1)) (eqLift (x 0) (x 1) (x 2)), x 2⟩ := T.axEqualizer 13
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] rfl (by simpa using T.holds_eqLiftOf hp hk he)
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [T.op_eqLiftOf hp hk he, T.op_eqInclOf hp,
      T.op_compOf ((T.codOf_eqLiftOf hp hk he).trans (T.domOf_eqInclOf hp).symm)])
    (by simp_eval [])

/-- The composite of two parallel arrows with an arrow into their equalizer, through the
inclusion, is equal. -/
theorem compOf_eqInclOf_comp {f g m : T.Ar} (hp : T.Par f g)
    (hm : T.codOf m = T.domOf (T.eqInclOf f g hp)) :
    T.compOf f (T.compOf (T.eqInclOf f g hp) m hm)
        ((T.codOf_compOf hm).trans (T.codOf_eqInclOf hp)) =
      T.compOf g (T.compOf (T.eqInclOf f g hp) m hm)
        (((T.codOf_compOf hm).trans (T.codOf_eqInclOf hp)).trans hp.1) :=
  calc _ = T.compOf (T.compOf f (T.eqInclOf f g hp) (T.codOf_eqInclOf hp)) m
        (hm.trans (T.domOf_compOf _).symm) := T.compOf_assoc hm (T.codOf_eqInclOf hp)
    _ = T.compOf (T.compOf g (T.eqInclOf f g hp) ((T.codOf_eqInclOf hp).trans hp.1)) m
        (hm.trans (T.domOf_compOf _).symm) := T.compOf_congr (T.compOf_eqInclOf hp) rfl _ _
    _ = _ := (T.compOf_assoc hm ((T.codOf_eqInclOf hp).trans hp.1)).symm

/-- A morphism into an equalizer is the factorization of its composite with the inclusion. -/
theorem eqLiftOf_eta {f g m : T.Ar} (hp : T.Par f g) (hm : T.codOf m = T.eqzOf f g hp) :
    T.eqLiftOf f g (T.compOf (T.eqInclOf f g hp) m (hm.trans (T.domOf_eqInclOf hp).symm)) hp
      ((T.codOf_compOf _).trans (T.codOf_eqInclOf hp)) (T.compOf_eqInclOf_comp hp _) = m := by
  have hv : Valid T.model [arr, arr, arr] [dfd (eqz (x 0) (x 1)), ⟨cod (x 2), eqz (x 0) (x 1)⟩]
      ⟨eqLift (x 0) (x 1) (comp (eqIncl (x 0) (x 1)) (x 2)), x 2⟩ := T.axEqualizer 14
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, m⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    exact ⟨⟨⟨obj, T.eqzOf f g hp⟩, by simp_eval [T.op_eqzOf hp], by simp_eval [T.op_eqzOf hp]⟩,
      ⟨⟨obj, T.eqzOf f g hp⟩, by simp_eval [op_codOf, hm], by simp_eval [T.op_eqzOf hp]⟩⟩)
  have hlift := T.op_eqLiftOf hp ((T.codOf_compOf _).trans (T.codOf_eqInclOf hp))
    (T.compOf_eqInclOf_comp hp (hm.trans (T.domOf_eqInclOf hp).symm))
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [T.op_eqInclOf hp, T.op_compOf (hm.trans (T.domOf_eqInclOf hp).symm), hlift])
    (by simp_eval [])

/-- Equalizers of pairs with equal second arrows are equal. -/
theorem eqzOf_congr {f g g' : T.Ar} (e : g = g') (hp : T.Par f g) (hp' : T.Par f g') :
    T.eqzOf f g hp = T.eqzOf f g' hp' := by
  subst e
  rfl

/-- Factorizations through equalizers of pairs with equal second arrows are equal. -/
theorem eqLiftOf_congr {f g g' k : T.Ar} (e : g = g') (hp : T.Par f g) (hp' : T.Par f g')
    (hk : T.codOf k = T.domOf f) (he : T.compOf f k hk = T.compOf g k (hk.trans hp.1))
    (he' : T.compOf f k hk = T.compOf g' k (hk.trans hp'.1)) :
    T.eqLiftOf f g k hp hk he = T.eqLiftOf f g' k hp' hk he' := by
  subst e
  rfl

/-- An axiom of the initial block, by index, is valid in the model. -/
theorem axInitial (k : ℕ) (hk : k < initialAxioms.length := by decide) :
    (initialAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- The initial object is defined. -/
theorem zeroOf_exists : ∃ o, T.model.op 13 [] = Part.some ⟨obj, o⟩ := by
  have h : Valid T.model [] [] (dfd zero) := T.axInitial 0
  obtain ⟨w, hw, -⟩ := h [] rfl (by simp)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The initial object. -/
def zeroOf : T.Obj := T.model.get T.zeroOf_exists

/-- The model's initial object. -/
@[simp] theorem op_zeroOf : T.model.op 13 [] = Part.some ⟨obj, T.zeroOf⟩ := T.model.op_eq_get _

/-- Every object has a morphism from the initial object. -/
theorem absurdOf_exists (a : T.Obj) : ∃ f, T.model.op 14 [⟨obj, a⟩] = Part.some ⟨arr, f⟩ := by
  have h : Valid T.model [obj] [] ⟨dom (absurd (x 0)), zero⟩ := T.axInitial 1
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩] rfl (by simp)
  simp_eval [] at hw
  obtain ⟨l, hl, -⟩ := part_bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := part_bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- The morphism from the initial object to an object. -/
def absurdOf (a : T.Obj) : T.Ar := T.model.get (T.absurdOf_exists a)

/-- The model's morphism from the initial object. -/
@[simp] theorem op_absurdOf (a : T.Obj) :
    T.model.op 14 [⟨obj, a⟩] = Part.some ⟨arr, T.absurdOf a⟩ :=
  T.model.op_eq_get _

/-- The domain of the morphism from the initial object is the initial object. -/
theorem domOf_absurdOf (a : T.Obj) : T.domOf (T.absurdOf a) = T.zeroOf := by
  have h : Valid T.model [obj] [] ⟨dom (absurd (x 0)), zero⟩ := T.axInitial 1
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩] rfl (by simp))
    (by simp_eval [op_absurdOf, op_domOf]) (by simp_eval [op_zeroOf])

/-- The codomain of the morphism from the initial object to an object is that object. -/
theorem codOf_absurdOf (a : T.Obj) : T.codOf (T.absurdOf a) = a := by
  have h : Valid T.model [obj] [] ⟨cod (absurd (x 0)), x 0⟩ := T.axInitial 2
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩] rfl (by simp))
    (by simp_eval [op_absurdOf, op_codOf]) (by simp_eval [])

/-- A morphism from the initial object is the morphism to its codomain. -/
theorem eq_absurdOf {f : T.Ar} (hf : T.domOf f = T.zeroOf) : f = T.absurdOf (T.codOf f) := by
  have h : Valid T.model [arr] [⟨dom (x 0), zero⟩] ⟨x 0, absurd (cod (x 0))⟩ := T.axInitial 3
  have hq := h [⟨arr, f⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨obj, T.zeroOf⟩, by simp_eval [op_domOf, hf], by simp_eval [op_zeroOf]⟩)
  exact T.val_inj <| T.holds_eq hq (by simp_eval []) (by simp_eval [op_codOf, op_absurdOf])

/-- An axiom of the coproduct block, by index, is valid in the model. -/
theorem axCoproduct (k : ℕ) (hk : k < coproductAxioms.length := by decide) :
    (coproductAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- Every two objects have a coproduct. -/
theorem coprodOf_exists (a b : T.Obj) :
    ∃ p, T.model.op 15 [⟨obj, a⟩, ⟨obj, b⟩] = Part.some ⟨obj, p⟩ := by
  have h : Valid T.model [obj, obj] [] (dfd (coprod (x 0) (x 1))) := T.axCoproduct 0
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The coproduct of two objects. -/
def coprodOf (a b : T.Obj) : T.Obj := T.model.get (T.coprodOf_exists a b)

/-- The model's coproduct of two objects. -/
@[simp] theorem op_coprodOf (a b : T.Obj) :
    T.model.op 15 [⟨obj, a⟩, ⟨obj, b⟩] = Part.some ⟨obj, T.coprodOf a b⟩ :=
  T.model.op_eq_get _

/-- Every coproduct has a first injection. -/
theorem inlOf_exists (a b : T.Obj) :
    ∃ f, T.model.op 16 [⟨obj, a⟩, ⟨obj, b⟩] = Part.some ⟨arr, f⟩ := by
  have h : Valid T.model [obj, obj] [] ⟨dom (inl (x 0) (x 1)), x 0⟩ := T.axCoproduct 1
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp)
  simp_eval [] at hw
  obtain ⟨l, hl, -⟩ := part_bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := part_bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- The first injection into a coproduct. -/
def inlOf (a b : T.Obj) : T.Ar := T.model.get (T.inlOf_exists a b)

/-- The model's first injection. -/
@[simp] theorem op_inlOf (a b : T.Obj) :
    T.model.op 16 [⟨obj, a⟩, ⟨obj, b⟩] = Part.some ⟨arr, T.inlOf a b⟩ :=
  T.model.op_eq_get _

/-- Every coproduct has a second injection. -/
theorem inrOf_exists (a b : T.Obj) :
    ∃ f, T.model.op 17 [⟨obj, a⟩, ⟨obj, b⟩] = Part.some ⟨arr, f⟩ := by
  have h : Valid T.model [obj, obj] [] ⟨dom (inr (x 0) (x 1)), x 1⟩ := T.axCoproduct 3
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp)
  simp_eval [] at hw
  obtain ⟨l, hl, -⟩ := part_bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := part_bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- The second injection into a coproduct. -/
def inrOf (a b : T.Obj) : T.Ar := T.model.get (T.inrOf_exists a b)

/-- The model's second injection. -/
@[simp] theorem op_inrOf (a b : T.Obj) :
    T.model.op 17 [⟨obj, a⟩, ⟨obj, b⟩] = Part.some ⟨arr, T.inrOf a b⟩ :=
  T.model.op_eq_get _

/-- The domain of the first injection is the first summand. -/
theorem domOf_inlOf (a b : T.Obj) : T.domOf (T.inlOf a b) = a := by
  have h : Valid T.model [obj, obj] [] ⟨dom (inl (x 0) (x 1)), x 0⟩ := T.axCoproduct 1
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp))
    (by simp_eval [op_inlOf, op_domOf]) (by simp_eval [])

/-- The codomain of the first injection is the coproduct. -/
theorem codOf_inlOf (a b : T.Obj) : T.codOf (T.inlOf a b) = T.coprodOf a b := by
  have h : Valid T.model [obj, obj] [] ⟨cod (inl (x 0) (x 1)), coprod (x 0) (x 1)⟩ :=
    T.axCoproduct 2
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp))
    (by simp_eval [op_inlOf, op_codOf]) (by simp_eval [op_coprodOf])

/-- The domain of the second injection is the second summand. -/
theorem domOf_inrOf (a b : T.Obj) : T.domOf (T.inrOf a b) = b := by
  have h : Valid T.model [obj, obj] [] ⟨dom (inr (x 0) (x 1)), x 1⟩ := T.axCoproduct 3
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp))
    (by simp_eval [op_inrOf, op_domOf]) (by simp_eval [])

/-- The codomain of the second injection is the coproduct. -/
theorem codOf_inrOf (a b : T.Obj) : T.codOf (T.inrOf a b) = T.coprodOf a b := by
  have h : Valid T.model [obj, obj] [] ⟨cod (inr (x 0) (x 1)), coprod (x 0) (x 1)⟩ :=
    T.axCoproduct 4
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp))
    (by simp_eval [op_inrOf, op_codOf]) (by simp_eval [op_coprodOf])

/-- Two morphisms of one codomain have a copairing. -/
theorem copairOf_exists {f g : T.Ar} (h : T.codOf f = T.codOf g) :
    ∃ p, T.model.op 18 [⟨arr, f⟩, ⟨arr, g⟩] = Part.some ⟨arr, p⟩ := by
  have hv : Valid T.model [arr, arr] [⟨cod (x 0), cod (x 1)⟩] (dfd (copair (x 0) (x 1))) :=
    T.axCoproduct 6
  obtain ⟨w, hw, -⟩ := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨obj, T.codOf g⟩, by simp_eval [op_codOf, h], by simp_eval [op_codOf]⟩)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The copairing of two morphisms of one codomain. -/
def copairOf (f g : T.Ar) (h : T.codOf f = T.codOf g) : T.Ar :=
  T.model.get (T.copairOf_exists h)

/-- The model's copairing. -/
@[simp] theorem op_copairOf {f g : T.Ar} (h : T.codOf f = T.codOf g) :
    T.model.op 18 [⟨arr, f⟩, ⟨arr, g⟩] = Part.some ⟨arr, T.copairOf f g h⟩ :=
  T.model.op_eq_get _

/-- A copairing is defined at its components. -/
theorem holds_copairOf {f g : T.Ar} (h : T.codOf f = T.codOf g) :
    (dfd (copair (x 0) (x 1))).Holds T.model [⟨arr, f⟩, ⟨arr, g⟩] :=
  ⟨⟨arr, T.copairOf f g h⟩, by simp_eval [T.op_copairOf h], by simp_eval [T.op_copairOf h]⟩

/-- The domain of a copairing is the coproduct of its components' domains. -/
theorem domOf_copairOf {f g : T.Ar} (h : T.codOf f = T.codOf g) :
    T.domOf (T.copairOf f g h) = T.coprodOf (T.domOf f) (T.domOf g) := by
  have hv : Valid T.model [arr, arr] [dfd (copair (x 0) (x 1))]
      ⟨dom (copair (x 0) (x 1)), coprod (dom (x 0)) (dom (x 1))⟩ := T.axCoproduct 7
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_copairOf h)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_copairOf h, op_domOf])
    (by simp_eval [op_domOf, op_coprodOf])

/-- The codomain of a copairing is its components' codomain. -/
theorem codOf_copairOf {f g : T.Ar} (h : T.codOf f = T.codOf g) :
    T.codOf (T.copairOf f g h) = T.codOf f := by
  have hv : Valid T.model [arr, arr] [dfd (copair (x 0) (x 1))]
      ⟨cod (copair (x 0) (x 1)), cod (x 0)⟩ := T.axCoproduct 8
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_copairOf h)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_copairOf h, op_codOf])
    (by simp_eval [op_codOf])

/-- A copairing after the first injection is its first component. -/
theorem copairOf_inlOf {f g : T.Ar} (h : T.codOf f = T.codOf g) :
    T.compOf (T.copairOf f g h) (T.inlOf (T.domOf f) (T.domOf g))
      ((T.codOf_inlOf _ _).trans (T.domOf_copairOf h).symm) = f := by
  have hv : Valid T.model [arr, arr] [dfd (copair (x 0) (x 1))]
      ⟨comp (copair (x 0) (x 1)) (inl (dom (x 0)) (dom (x 1))), x 0⟩ := T.axCoproduct 9
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_copairOf h)
  have hc := T.op_compOf ((T.codOf_inlOf (T.domOf f) (T.domOf g)).trans (T.domOf_copairOf h).symm)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_copairOf h, op_domOf, op_inlOf, hc])
    (by simp_eval [])

/-- A copairing after the second injection is its second component. -/
theorem copairOf_inrOf {f g : T.Ar} (h : T.codOf f = T.codOf g) :
    T.compOf (T.copairOf f g h) (T.inrOf (T.domOf f) (T.domOf g))
      ((T.codOf_inrOf _ _).trans (T.domOf_copairOf h).symm) = g := by
  have hv : Valid T.model [arr, arr] [dfd (copair (x 0) (x 1))]
      ⟨comp (copair (x 0) (x 1)) (inr (dom (x 0)) (dom (x 1))), x 1⟩ := T.axCoproduct 10
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_copairOf h)
  have hc := T.op_compOf ((T.codOf_inrOf (T.domOf f) (T.domOf g)).trans (T.domOf_copairOf h).symm)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_copairOf h, op_domOf, op_inrOf, hc])
    (by simp_eval [])

/-- A morphism from a coproduct is the copairing of its composites with the injections. -/
theorem copairOf_eta {k : T.Ar} {a b : T.Obj} (h : T.domOf k = T.coprodOf a b) :
    T.copairOf (T.compOf k (T.inlOf a b) ((T.codOf_inlOf a b).trans h.symm))
      (T.compOf k (T.inrOf a b) ((T.codOf_inrOf a b).trans h.symm))
      ((T.codOf_compOf _).trans (T.codOf_compOf _).symm) = k := by
  have hv : Valid T.model [arr, obj, obj] [⟨dom (x 0), coprod (x 1) (x 2)⟩]
      ⟨copair (comp (x 0) (inl (x 1) (x 2))) (comp (x 0) (inr (x 1) (x 2))), x 0⟩ :=
    T.axCoproduct 11
  have hq := hv [⟨arr, k⟩, ⟨obj, a⟩, ⟨obj, b⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨obj, T.coprodOf a b⟩, by simp_eval [op_domOf, h], by simp_eval [op_coprodOf]⟩)
  have hl := T.op_compOf ((T.codOf_inlOf a b).trans h.symm)
  have hr := T.op_compOf ((T.codOf_inrOf a b).trans h.symm)
  have hp := T.op_copairOf ((T.codOf_compOf ((T.codOf_inlOf a b).trans h.symm)).trans
    (T.codOf_compOf ((T.codOf_inrOf a b).trans h.symm)).symm)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [op_inlOf, op_inrOf, hl, hr, hp])
    (by simp_eval [])

/-- An axiom of the coequalizer block, by index, is valid in the model. -/
theorem axCoequalizer (k : ℕ) (hk : k < coequalizerAxioms.length := by decide) :
    (coequalizerAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- Two parallel arrows have a coequalizer. -/
theorem coeqzOf_exists {f g : T.Ar} (hp : T.Par f g) :
    ∃ e, T.model.op 19 [⟨arr, f⟩, ⟨arr, g⟩] = Part.some ⟨obj, e⟩ := by
  have hv : Valid T.model [arr, arr] [⟨dom (x 0), dom (x 1)⟩, ⟨cod (x 0), cod (x 1)⟩]
      (dfd (coeqz (x 0) (x 1))) := T.axCoequalizer 2
  obtain ⟨w, hw, -⟩ := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    exact ⟨⟨⟨obj, T.domOf g⟩, by simp_eval [op_domOf, hp.1], by simp_eval [op_domOf]⟩,
      ⟨⟨obj, T.codOf g⟩, by simp_eval [op_codOf, hp.2], by simp_eval [op_codOf]⟩⟩)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The coequalizer of two parallel arrows. -/
def coeqzOf (f g : T.Ar) (hp : T.Par f g) : T.Obj := T.model.get (T.coeqzOf_exists hp)

/-- The model's coequalizer. -/
@[simp] theorem op_coeqzOf {f g : T.Ar} (hp : T.Par f g) :
    T.model.op 19 [⟨arr, f⟩, ⟨arr, g⟩] = Part.some ⟨obj, T.coeqzOf f g hp⟩ :=
  T.model.op_eq_get _

/-- The coequalizer of two parallel arrows is defined at them. -/
theorem holds_coeqzOf {f g : T.Ar} (hp : T.Par f g) :
    (dfd (coeqz (x 0) (x 1))).Holds T.model [⟨arr, f⟩, ⟨arr, g⟩] :=
  ⟨⟨obj, T.coeqzOf f g hp⟩, by simp_eval [T.op_coeqzOf hp], by simp_eval [T.op_coeqzOf hp]⟩

/-- A coequalizer has a projection. -/
theorem coeqProjOf_exists {f g : T.Ar} (hp : T.Par f g) :
    ∃ e, T.model.op 20 [⟨arr, f⟩, ⟨arr, g⟩] = Part.some ⟨arr, e⟩ := by
  have hv : Valid T.model [arr, arr] [dfd (coeqz (x 0) (x 1))] (dfd (coeqProj (x 0) (x 1))) :=
    T.axCoequalizer 4
  obtain ⟨w, hw, -⟩ := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_coeqzOf hp)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The projection onto the coequalizer of two parallel arrows. -/
def coeqProjOf (f g : T.Ar) (hp : T.Par f g) : T.Ar := T.model.get (T.coeqProjOf_exists hp)

/-- The model's projection onto a coequalizer. -/
@[simp] theorem op_coeqProjOf {f g : T.Ar} (hp : T.Par f g) :
    T.model.op 20 [⟨arr, f⟩, ⟨arr, g⟩] = Part.some ⟨arr, T.coeqProjOf f g hp⟩ :=
  T.model.op_eq_get _

/-- The domain of a coequalizer's projection is the arrows' codomain. -/
theorem domOf_coeqProjOf {f g : T.Ar} (hp : T.Par f g) :
    T.domOf (T.coeqProjOf f g hp) = T.codOf f := by
  have hv : Valid T.model [arr, arr] [dfd (coeqz (x 0) (x 1))]
      ⟨dom (coeqProj (x 0) (x 1)), cod (x 0)⟩ := T.axCoequalizer 5
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_coeqzOf hp)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_coeqProjOf hp, op_domOf])
    (by simp_eval [op_codOf])

/-- The codomain of a coequalizer's projection is the coequalizer. -/
theorem codOf_coeqProjOf {f g : T.Ar} (hp : T.Par f g) :
    T.codOf (T.coeqProjOf f g hp) = T.coeqzOf f g hp := by
  have hv : Valid T.model [arr, arr] [dfd (coeqz (x 0) (x 1))]
      ⟨cod (coeqProj (x 0) (x 1)), coeqz (x 0) (x 1)⟩ := T.axCoequalizer 6
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_coeqzOf hp)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_coeqProjOf hp, op_codOf])
    (by simp_eval [T.op_coeqzOf hp])

/-- A coequalizer's projection coequalizes the arrows. -/
theorem compOf_coeqProjOf {f g : T.Ar} (hp : T.Par f g) :
    T.compOf (T.coeqProjOf f g hp) f (T.domOf_coeqProjOf hp).symm =
      T.compOf (T.coeqProjOf f g hp) g (hp.2.symm.trans (T.domOf_coeqProjOf hp).symm) := by
  have hv : Valid T.model [arr, arr] [dfd (coeqz (x 0) (x 1))]
      ⟨comp (coeqProj (x 0) (x 1)) (x 0), comp (coeqProj (x 0) (x 1)) (x 1)⟩ :=
    T.axCoequalizer 7
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩] rfl (by simpa using T.holds_coeqzOf hp)
  have h1 := T.op_compOf (T.domOf_coeqProjOf hp).symm
  have h2 := T.op_compOf (hp.2.symm.trans (T.domOf_coeqProjOf hp).symm)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_coeqProjOf hp, h1])
    (by simp_eval [T.op_coeqProjOf hp, h2])

/-- A morphism that coequalizes two parallel arrows descends through their coequalizer. -/
theorem coeqDescOf_exists {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf f = T.domOf k)
    (he : T.compOf k f hk = T.compOf k g (hp.2.symm.trans hk)) :
    ∃ l, T.model.op 21 [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] = Part.some ⟨arr, l⟩ := by
  have hv : Valid T.model [arr, arr, arr]
      [dfd (coeqz (x 0) (x 1)), ⟨comp (x 2) (x 0), comp (x 2) (x 1)⟩]
      (dfd (coeqDesc (x 0) (x 1) (x 2))) := T.axCoequalizer 10
  obtain ⟨w, hw, -⟩ := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    exact ⟨⟨⟨obj, T.coeqzOf f g hp⟩, by simp_eval [T.op_coeqzOf hp],
        by simp_eval [T.op_coeqzOf hp]⟩,
      ⟨⟨arr, T.compOf k g (hp.2.symm.trans hk)⟩, by simp_eval [T.op_compOf hk, he],
        by simp_eval [T.op_compOf (hp.2.symm.trans hk)]⟩⟩)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The descent through the coequalizer of two parallel arrows of a morphism that
coequalizes them. -/
def coeqDescOf (f g k : T.Ar) (hp : T.Par f g) (hk : T.codOf f = T.domOf k)
    (he : T.compOf k f hk = T.compOf k g (hp.2.symm.trans hk)) : T.Ar :=
  T.model.get (T.coeqDescOf_exists hp hk he)

/-- The model's descent through a coequalizer. -/
@[simp] theorem op_coeqDescOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf f = T.domOf k)
    (he : T.compOf k f hk = T.compOf k g (hp.2.symm.trans hk)) :
    T.model.op 21 [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] = Part.some ⟨arr, T.coeqDescOf f g k hp hk he⟩ :=
  T.model.op_eq_get _

/-- A descent through a coequalizer is defined at its arguments. -/
theorem holds_coeqDescOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf f = T.domOf k)
    (he : T.compOf k f hk = T.compOf k g (hp.2.symm.trans hk)) :
    (dfd (coeqDesc (x 0) (x 1) (x 2))).Holds T.model [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] :=
  ⟨⟨arr, T.coeqDescOf f g k hp hk he⟩, by simp_eval [T.op_coeqDescOf hp hk he],
    by simp_eval [T.op_coeqDescOf hp hk he]⟩

/-- The domain of a descent through a coequalizer is the coequalizer. -/
theorem domOf_coeqDescOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf f = T.domOf k)
    (he : T.compOf k f hk = T.compOf k g (hp.2.symm.trans hk)) :
    T.domOf (T.coeqDescOf f g k hp hk he) = T.coeqzOf f g hp := by
  have hv : Valid T.model [arr, arr, arr] [dfd (coeqDesc (x 0) (x 1) (x 2))]
      ⟨dom (coeqDesc (x 0) (x 1) (x 2)), coeqz (x 0) (x 1)⟩ := T.axCoequalizer 11
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] rfl (by simpa using T.holds_coeqDescOf hp hk he)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_coeqDescOf hp hk he, op_domOf])
    (by simp_eval [T.op_coeqzOf hp])

/-- The codomain of a descent through a coequalizer is the descended morphism's. -/
theorem codOf_coeqDescOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf f = T.domOf k)
    (he : T.compOf k f hk = T.compOf k g (hp.2.symm.trans hk)) :
    T.codOf (T.coeqDescOf f g k hp hk he) = T.codOf k := by
  have hv : Valid T.model [arr, arr, arr] [dfd (coeqDesc (x 0) (x 1) (x 2))]
      ⟨cod (coeqDesc (x 0) (x 1) (x 2)), cod (x 2)⟩ := T.axCoequalizer 12
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] rfl (by simpa using T.holds_coeqDescOf hp hk he)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_coeqDescOf hp hk he, op_codOf])
    (by simp_eval [op_codOf])

/-- A descent through a coequalizer after the projection is the descended morphism. -/
theorem coeqDescOf_coeqProjOf {f g k : T.Ar} (hp : T.Par f g) (hk : T.codOf f = T.domOf k)
    (he : T.compOf k f hk = T.compOf k g (hp.2.symm.trans hk)) :
    T.compOf (T.coeqDescOf f g k hp hk he) (T.coeqProjOf f g hp)
      ((T.codOf_coeqProjOf hp).trans (T.domOf_coeqDescOf hp hk he).symm) = k := by
  have hv : Valid T.model [arr, arr, arr] [dfd (coeqDesc (x 0) (x 1) (x 2))]
      ⟨comp (coeqDesc (x 0) (x 1) (x 2)) (coeqProj (x 0) (x 1)), x 2⟩ := T.axCoequalizer 13
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, k⟩] rfl (by simpa using T.holds_coeqDescOf hp hk he)
  have hc := T.op_compOf ((T.codOf_coeqProjOf hp).trans (T.domOf_coeqDescOf hp hk he).symm)
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [T.op_coeqDescOf hp hk he, T.op_coeqProjOf hp, hc]) (by simp_eval [])

/-- An arrow out of a coequalizer, after the projection, coequalizes the two parallel
arrows. -/
theorem compOf_coeqProjOf_comp {f g m : T.Ar} (hp : T.Par f g)
    (hm : T.codOf (T.coeqProjOf f g hp) = T.domOf m) :
    T.compOf (T.compOf m (T.coeqProjOf f g hp) hm) f
        ((T.domOf_coeqProjOf hp).symm.trans (T.domOf_compOf hm).symm) =
      T.compOf (T.compOf m (T.coeqProjOf f g hp) hm) g
        (hp.2.symm.trans ((T.domOf_coeqProjOf hp).symm.trans (T.domOf_compOf hm).symm)) :=
  calc _ = T.compOf m (T.compOf (T.coeqProjOf f g hp) f (T.domOf_coeqProjOf hp).symm)
        ((T.codOf_compOf _).trans hm) := (T.compOf_assoc (T.domOf_coeqProjOf hp).symm hm).symm
    _ = T.compOf m (T.compOf (T.coeqProjOf f g hp) g
          (hp.2.symm.trans (T.domOf_coeqProjOf hp).symm)) ((T.codOf_compOf _).trans hm) :=
        T.compOf_congr rfl (T.compOf_coeqProjOf hp) _ _
    _ = _ := T.compOf_assoc (hp.2.symm.trans (T.domOf_coeqProjOf hp).symm) hm

/-- A morphism out of a coequalizer is the descent of its composite with the projection. -/
theorem coeqDescOf_eta {f g m : T.Ar} (hp : T.Par f g) (hm : T.domOf m = T.coeqzOf f g hp) :
    T.coeqDescOf f g (T.compOf m (T.coeqProjOf f g hp) ((T.codOf_coeqProjOf hp).trans hm.symm))
      hp ((T.domOf_coeqProjOf hp).symm.trans (T.domOf_compOf _).symm)
      (T.compOf_coeqProjOf_comp hp _) = m := by
  have hv : Valid T.model [arr, arr, arr]
      [dfd (coeqz (x 0) (x 1)), ⟨dom (x 2), coeqz (x 0) (x 1)⟩]
      ⟨coeqDesc (x 0) (x 1) (comp (x 2) (coeqProj (x 0) (x 1))), x 2⟩ := T.axCoequalizer 14
  have hq := hv [⟨arr, f⟩, ⟨arr, g⟩, ⟨arr, m⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    exact ⟨⟨⟨obj, T.coeqzOf f g hp⟩, by simp_eval [T.op_coeqzOf hp],
        by simp_eval [T.op_coeqzOf hp]⟩,
      ⟨⟨obj, T.coeqzOf f g hp⟩, by simp_eval [op_domOf, hm], by simp_eval [T.op_coeqzOf hp]⟩⟩)
  have hc := T.op_compOf ((T.codOf_coeqProjOf hp).trans hm.symm)
  have hd := T.op_coeqDescOf hp ((T.domOf_coeqProjOf hp).symm.trans (T.domOf_compOf _).symm)
    (T.compOf_coeqProjOf_comp hp ((T.codOf_coeqProjOf hp).trans hm.symm))
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_coeqProjOf hp, hc, hd])
    (by simp_eval [])

/-- The morphism {lit}`f × id`, from the product of the domain of {lit}`f` and {lit}`a` to the
product of its codomain and {lit}`a`. -/
abbrev prodMapLeftOf (f : T.Ar) (a : T.Obj) : T.Ar :=
  T.pairOf (T.compOf f (T.fstOf (T.domOf f) a) (T.codOf_fstOf _ _)) (T.sndOf (T.domOf f) a)
    ((T.domOf_compOf _).trans ((T.domOf_fstOf _ _).trans (T.domOf_sndOf _ _).symm))

/-- The domain of {lit}`f × id` is the product of the domain of {lit}`f` and {lit}`a`. -/
theorem domOf_prodMapLeftOf (f : T.Ar) (a : T.Obj) :
    T.domOf (T.prodMapLeftOf f a) = T.prodOf (T.domOf f) a :=
  (T.domOf_pairOf _).trans ((T.domOf_compOf _).trans (T.domOf_fstOf _ _))

/-- The codomain of {lit}`f × id` is the product of the codomain of {lit}`f` and {lit}`a`. -/
theorem codOf_prodMapLeftOf (f : T.Ar) (a : T.Obj) :
    T.codOf (T.prodMapLeftOf f a) = T.prodOf (T.codOf f) a := by
  rw [prodMapLeftOf, codOf_pairOf, codOf_compOf, codOf_sndOf]

/-- An axiom of the exponential block, by index, is valid in the model. -/
theorem axExponential (k : ℕ) (hk : k < exponentialAxioms.length := by decide) :
    (exponentialAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- Every two objects have an exponential. -/
theorem expOf_exists (a b : T.Obj) :
    ∃ e, T.model.op 22 [⟨obj, a⟩, ⟨obj, b⟩] = Part.some ⟨obj, e⟩ := by
  have h : Valid T.model [obj, obj] [] (dfd (exp (x 0) (x 1))) := T.axExponential 0
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The exponential {lit}`expOf a b`, the object of morphisms from {lit}`a` to {lit}`b`. -/
def expOf (a b : T.Obj) : T.Obj := T.model.get (T.expOf_exists a b)

/-- The model's exponential. -/
@[simp] theorem op_expOf (a b : T.Obj) :
    T.model.op 22 [⟨obj, a⟩, ⟨obj, b⟩] = Part.some ⟨obj, T.expOf a b⟩ :=
  T.model.op_eq_get _

/-- Every exponential has an evaluation morphism. -/
theorem evOf_exists (a b : T.Obj) :
    ∃ e, T.model.op 23 [⟨obj, a⟩, ⟨obj, b⟩] = Part.some ⟨arr, e⟩ := by
  have h : Valid T.model [obj, obj] [] ⟨dom (ev (x 0) (x 1)), prod (exp (x 0) (x 1)) (x 0)⟩ :=
    T.axExponential 1
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp)
  simp_eval [] at hw
  obtain ⟨l, hl, -⟩ := part_bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := part_bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- The evaluation morphism, from the product of {lit}`expOf a b` and {lit}`a` to {lit}`b`. -/
def evOf (a b : T.Obj) : T.Ar := T.model.get (T.evOf_exists a b)

/-- The model's evaluation morphism. -/
@[simp] theorem op_evOf (a b : T.Obj) :
    T.model.op 23 [⟨obj, a⟩, ⟨obj, b⟩] = Part.some ⟨arr, T.evOf a b⟩ :=
  T.model.op_eq_get _

/-- The domain of evaluation. -/
theorem domOf_evOf (a b : T.Obj) : T.domOf (T.evOf a b) = T.prodOf (T.expOf a b) a := by
  have h : Valid T.model [obj, obj] [] ⟨dom (ev (x 0) (x 1)), prod (exp (x 0) (x 1)) (x 0)⟩ :=
    T.axExponential 1
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp))
    (by simp_eval [op_evOf, op_domOf]) (by simp_eval [op_expOf, op_prodOf])

/-- The codomain of evaluation. -/
theorem codOf_evOf (a b : T.Obj) : T.codOf (T.evOf a b) = b := by
  have h : Valid T.model [obj, obj] [] ⟨cod (ev (x 0) (x 1)), x 1⟩ := T.axExponential 2
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩, ⟨obj, b⟩] rfl (by simp))
    (by simp_eval [op_evOf, op_codOf]) (by simp_eval [])

/-- A morphism from a product has a currying. -/
theorem curryOf_exists {c a : T.Obj} {f : T.Ar} (h : T.domOf f = T.prodOf c a) :
    ∃ g, T.model.op 24 [⟨obj, c⟩, ⟨obj, a⟩, ⟨arr, f⟩] = Part.some ⟨arr, g⟩ := by
  have hv : Valid T.model [obj, obj, arr] [⟨dom (x 2), prod (x 0) (x 1)⟩]
      (dfd (curry (x 0) (x 1) (x 2))) := T.axExponential 4
  obtain ⟨w, hw, -⟩ := hv [⟨obj, c⟩, ⟨obj, a⟩, ⟨arr, f⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨obj, T.prodOf c a⟩, by simp_eval [op_domOf, h], by simp_eval [op_prodOf]⟩)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The currying of a morphism from the product of {lit}`c` and {lit}`a`. -/
def curryOf (c a : T.Obj) (f : T.Ar) (h : T.domOf f = T.prodOf c a) : T.Ar :=
  T.model.get (T.curryOf_exists h)

/-- The model's currying. -/
@[simp] theorem op_curryOf {c a : T.Obj} {f : T.Ar} (h : T.domOf f = T.prodOf c a) :
    T.model.op 24 [⟨obj, c⟩, ⟨obj, a⟩, ⟨arr, f⟩] = Part.some ⟨arr, T.curryOf c a f h⟩ :=
  T.model.op_eq_get _

/-- A currying is defined at its arguments. -/
theorem holds_curryOf {c a : T.Obj} {f : T.Ar} (h : T.domOf f = T.prodOf c a) :
    (dfd (curry (x 0) (x 1) (x 2))).Holds T.model [⟨obj, c⟩, ⟨obj, a⟩, ⟨arr, f⟩] :=
  ⟨⟨arr, T.curryOf c a f h⟩, by simp_eval [T.op_curryOf h], by simp_eval [T.op_curryOf h]⟩

/-- The domain of a currying. -/
theorem domOf_curryOf {c a : T.Obj} {f : T.Ar} (h : T.domOf f = T.prodOf c a) :
    T.domOf (T.curryOf c a f h) = c := by
  have hv : Valid T.model [obj, obj, arr] [dfd (curry (x 0) (x 1) (x 2))]
      ⟨dom (curry (x 0) (x 1) (x 2)), x 0⟩ := T.axExponential 5
  have hq := hv [⟨obj, c⟩, ⟨obj, a⟩, ⟨arr, f⟩] rfl (by simpa using T.holds_curryOf h)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_curryOf h, op_domOf]) (by simp_eval [])

/-- The codomain of a currying. -/
theorem codOf_curryOf {c a : T.Obj} {f : T.Ar} (h : T.domOf f = T.prodOf c a) :
    T.codOf (T.curryOf c a f h) = T.expOf a (T.codOf f) := by
  have hv : Valid T.model [obj, obj, arr] [dfd (curry (x 0) (x 1) (x 2))]
      ⟨cod (curry (x 0) (x 1) (x 2)), exp (x 1) (cod (x 2))⟩ := T.axExponential 6
  have hq := hv [⟨obj, c⟩, ⟨obj, a⟩, ⟨arr, f⟩] rfl (by simpa using T.holds_curryOf h)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_curryOf h, op_codOf])
    (by simp_eval [op_codOf, op_expOf])

/-- Curryings of equal morphisms are equal, whatever the proofs of their domains. -/
theorem curryOf_congr {c a : T.Obj} {f f' : T.Ar} (e : f = f') {h : T.domOf f = T.prodOf c a}
    {h' : T.domOf f' = T.prodOf c a} : T.curryOf c a f h = T.curryOf c a f' h' := by
  subst e
  rfl

/-- The morphism {lit}`curry f × id` composes with evaluation. -/
theorem codOf_prodMapLeftOf_curryOf {c a : T.Obj} {f : T.Ar} (h : T.domOf f = T.prodOf c a) :
    T.codOf (T.prodMapLeftOf (T.curryOf c a f h) a) = T.domOf (T.evOf a (T.codOf f)) := by
  rw [codOf_prodMapLeftOf, codOf_curryOf, domOf_evOf]

/-- Evaluation after {lit}`curry f × id` is {lit}`f`. -/
theorem evOf_curryOf {c a : T.Obj} {f : T.Ar} (h : T.domOf f = T.prodOf c a) :
    T.compOf (T.evOf a (T.codOf f)) (T.prodMapLeftOf (T.curryOf c a f h) a)
      (T.codOf_prodMapLeftOf_curryOf h) = f := by
  have hv : Valid T.model [obj, obj, arr] [dfd (curry (x 0) (x 1) (x 2))]
      ⟨comp (ev (x 1) (cod (x 2))) (prodMapLeft (curry (x 0) (x 1) (x 2)) (x 1)), x 2⟩ :=
    T.axExponential 7
  have hq := hv [⟨obj, c⟩, ⟨obj, a⟩, ⟨arr, f⟩] rfl (by simpa using T.holds_curryOf h)
  have h1 := T.op_compOf (T.codOf_fstOf (T.domOf (T.curryOf c a f h)) a)
  have h2 := T.op_pairOf ((T.domOf_compOf (T.codOf_fstOf (T.domOf (T.curryOf c a f h)) a)).trans
    ((T.domOf_fstOf _ _).trans (T.domOf_sndOf (T.domOf (T.curryOf c a f h)) a).symm))
  have hc := T.op_compOf (T.codOf_prodMapLeftOf_curryOf h)
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [T.op_curryOf h, op_codOf, op_evOf, op_domOf, op_fstOf, op_sndOf, h1, h2, hc])
    (by simp_eval [])

/-- The domain of the evaluation after {lit}`k × id`, for {lit}`k` from {lit}`c`, is the
product of {lit}`c` and {lit}`a`. -/
theorem domOf_evOf_prodMapLeftOf {c a b : T.Obj} {k : T.Ar} (hd : T.domOf k = c)
    (hc : T.codOf (T.prodMapLeftOf k a) = T.domOf (T.evOf a b)) :
    T.domOf (T.compOf (T.evOf a b) (T.prodMapLeftOf k a) hc) = T.prodOf c a := by
  rw [domOf_compOf, domOf_prodMapLeftOf, hd]

/-- A morphism into an exponential is the currying of evaluation after it times the
identity. -/
theorem curryOf_eta {c a b : T.Obj} {k : T.Ar} (hd : T.domOf k = c)
    (hk : T.codOf k = T.expOf a b) :
    T.curryOf c a (T.compOf (T.evOf a b) (T.prodMapLeftOf k a)
      (by rw [codOf_prodMapLeftOf, domOf_evOf, hk])) (T.domOf_evOf_prodMapLeftOf hd _) = k := by
  have hv : Valid T.model [obj, obj, obj, arr] [⟨dom (x 3), x 0⟩, ⟨cod (x 3), exp (x 1) (x 2)⟩]
      ⟨curry (x 0) (x 1) (comp (ev (x 1) (x 2)) (prodMapLeft (x 3) (x 1))), x 3⟩ :=
    T.axExponential 8
  have hq := hv [⟨obj, c⟩, ⟨obj, a⟩, ⟨obj, b⟩, ⟨arr, k⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    exact ⟨⟨⟨obj, c⟩, by simp_eval [op_domOf, hd], by simp_eval []⟩,
      ⟨⟨obj, T.expOf a b⟩, by simp_eval [op_codOf, hk], by simp_eval [op_expOf]⟩⟩)
  have hc : T.codOf (T.prodMapLeftOf k a) = T.domOf (T.evOf a b) := by
    rw [codOf_prodMapLeftOf, domOf_evOf, hk]
  have h1 := T.op_compOf (T.codOf_fstOf (T.domOf k) a)
  have h2 := T.op_pairOf ((T.domOf_compOf (T.codOf_fstOf (T.domOf k) a)).trans
    ((T.domOf_fstOf _ _).trans (T.domOf_sndOf (T.domOf k) a).symm))
  have he := T.op_compOf hc
  have hcu := T.op_curryOf (T.domOf_evOf_prodMapLeftOf hd hc)
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [op_evOf, op_domOf, op_fstOf, op_sndOf, h1, h2, he, hcu]) (by simp_eval [])

/-- The morphism to the terminal object after an arrow is the morphism from the arrow's
domain. -/
theorem compOf_bangOf (f : T.Ar) :
    T.compOf (T.bangOf (T.codOf f)) f (T.domOf_bangOf _).symm = T.bangOf (T.domOf f) := by
  rw [T.eq_bangOf ((T.codOf_compOf _).trans (T.codOf_bangOf _)), domOf_compOf]

/-- An axiom of the classifier block, by index, is valid in the model. -/
theorem axClassifier (k : ℕ) (hk : k < classifierAxioms.length := by decide) :
    (classifierAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- The subobject classifier is defined. -/
theorem omegaOf_exists : ∃ o, T.model.op 25 [] = Part.some ⟨obj, o⟩ := by
  have h : Valid T.model [] [] (dfd omega) := T.axClassifier 0
  obtain ⟨w, hw, -⟩ := h [] rfl (by simp)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The subobject classifier. -/
def omegaOf : T.Obj := T.model.get T.omegaOf_exists

/-- The model's subobject classifier. -/
@[simp] theorem op_omegaOf : T.model.op 25 [] = Part.some ⟨obj, T.omegaOf⟩ := T.model.op_eq_get _

/-- Truth is defined. -/
theorem truOf_exists : ∃ t, T.model.op 26 [] = Part.some ⟨arr, t⟩ := by
  have h : Valid T.model [] [] ⟨dom tru, one⟩ := T.axClassifier 1
  obtain ⟨w, hw, -⟩ := h [] rfl (by simp)
  simp_eval [] at hw
  obtain ⟨l, hl, -⟩ := part_bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := part_bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- Truth, from the terminal object to the subobject classifier. -/
def truOf : T.Ar := T.model.get T.truOf_exists

/-- The model's truth. -/
@[simp] theorem op_truOf : T.model.op 26 [] = Part.some ⟨arr, T.truOf⟩ := T.model.op_eq_get _

/-- The domain of truth is the terminal object. -/
theorem domOf_truOf : T.domOf T.truOf = T.oneOf := by
  have h : Valid T.model [] [] ⟨dom tru, one⟩ := T.axClassifier 1
  exact T.val_inj <| T.holds_eq (h [] rfl (by simp)) (by simp_eval [op_truOf, op_domOf])
    (by simp_eval [op_oneOf])

/-- The codomain of truth is the subobject classifier. -/
theorem codOf_truOf : T.codOf T.truOf = T.omegaOf := by
  have h : Valid T.model [] [] ⟨cod tru, omega⟩ := T.axClassifier 2
  exact T.val_inj <| T.holds_eq (h [] rfl (by simp)) (by simp_eval [op_truOf, op_codOf])
    (by simp_eval [op_omegaOf])

/-- The two composites of an arrow with the projections of the square of its domain are
parallel. -/
theorem par_kernel (m : T.Ar) :
    T.Par (T.compOf m (T.fstOf (T.domOf m) (T.domOf m)) (T.codOf_fstOf _ _))
      (T.compOf m (T.sndOf (T.domOf m) (T.domOf m)) (T.codOf_sndOf _ _)) :=
  ⟨(T.domOf_compOf _).trans ((T.domOf_fstOf _ _).trans ((T.domOf_sndOf _ _).symm.trans
    (T.domOf_compOf _).symm)), (T.codOf_compOf _).trans (T.codOf_compOf _).symm⟩

/-- The inclusion of an arrow's kernel pair into the square of its domain. -/
abbrev kernelInclOf (m : T.Ar) : T.Ar :=
  T.eqInclOf (T.compOf m (T.fstOf (T.domOf m) (T.domOf m)) (T.codOf_fstOf _ _))
    (T.compOf m (T.sndOf (T.domOf m) (T.domOf m)) (T.codOf_sndOf _ _)) (T.par_kernel m)

/-- The kernel pair's inclusion composes with the projections. -/
theorem codOf_kernelInclOf (m : T.Ar) :
    T.codOf (T.kernelInclOf m) = T.prodOf (T.domOf m) (T.domOf m) :=
  (T.codOf_eqInclOf _).trans ((T.domOf_compOf _).trans (T.domOf_fstOf _ _))

/-- An arrow is a monomorphism: the projections of its kernel pair are equal. -/
def IsMono (m : T.Ar) : Prop :=
  T.compOf (T.fstOf (T.domOf m) (T.domOf m)) (T.kernelInclOf m)
      ((T.codOf_kernelInclOf m).trans (T.domOf_fstOf _ _).symm) =
    T.compOf (T.sndOf (T.domOf m) (T.domOf m)) (T.kernelInclOf m)
      ((T.codOf_kernelInclOf m).trans (T.domOf_sndOf _ _).symm)

/-- The condition of monicity holds at a monomorphism. -/
theorem holds_monoCond {m : T.Ar} (hm : T.IsMono m) :
    (monoCond (x 0)).Holds T.model [⟨arr, m⟩] := by
  have h1 := T.op_compOf (T.codOf_fstOf (T.domOf m) (T.domOf m))
  have h2 := T.op_compOf (T.codOf_sndOf (T.domOf m) (T.domOf m))
  have hk := T.op_eqInclOf (T.par_kernel m)
  have hp1 := T.op_compOf ((T.codOf_kernelInclOf m).trans (T.domOf_fstOf _ _).symm)
  have hp2 := T.op_compOf ((T.codOf_kernelInclOf m).trans (T.domOf_sndOf _ _).symm)
  unfold IsMono at hm
  refine ⟨⟨arr, T.compOf (T.sndOf (T.domOf m) (T.domOf m)) (T.kernelInclOf m)
    ((T.codOf_kernelInclOf m).trans (T.domOf_sndOf _ _).symm)⟩, ?_, ?_⟩
  · simp_eval [op_domOf, op_fstOf, op_sndOf, h1, h2, hk, hp1, hm]
  · simp_eval [op_domOf, op_fstOf, op_sndOf, h1, h2, hk, hp2]

/-- A monomorphism has a characteristic map. -/
theorem chiOf_exists {m : T.Ar} (hm : T.IsMono m) :
    ∃ c, T.model.op 27 [⟨arr, m⟩] = Part.some ⟨arr, c⟩ := by
  have hv : Valid T.model [arr] [monoCond (x 0)] (dfd (chi (x 0))) := T.axClassifier 4
  obtain ⟨w, hw, -⟩ := hv [⟨arr, m⟩] rfl (by simpa using T.holds_monoCond hm)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The characteristic map of a monomorphism. -/
def chiOf (m : T.Ar) (hm : T.IsMono m) : T.Ar := T.model.get (T.chiOf_exists hm)

/-- The model's characteristic map. -/
@[simp] theorem op_chiOf {m : T.Ar} (hm : T.IsMono m) :
    T.model.op 27 [⟨arr, m⟩] = Part.some ⟨arr, T.chiOf m hm⟩ :=
  T.model.op_eq_get _

/-- A characteristic map is defined at its monomorphism. -/
theorem holds_chiOf {m : T.Ar} (hm : T.IsMono m) :
    (dfd (chi (x 0))).Holds T.model [⟨arr, m⟩] :=
  ⟨⟨arr, T.chiOf m hm⟩, by simp_eval [T.op_chiOf hm], by simp_eval [T.op_chiOf hm]⟩

/-- The domain of a characteristic map is its monomorphism's codomain. -/
theorem domOf_chiOf {m : T.Ar} (hm : T.IsMono m) : T.domOf (T.chiOf m hm) = T.codOf m := by
  have hv : Valid T.model [arr] [dfd (chi (x 0))] ⟨dom (chi (x 0)), cod (x 0)⟩ :=
    T.axClassifier 5
  have hq := hv [⟨arr, m⟩] rfl (by simpa using T.holds_chiOf hm)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_chiOf hm, op_domOf])
    (by simp_eval [op_codOf])

/-- The codomain of a characteristic map is the subobject classifier. -/
theorem codOf_chiOf {m : T.Ar} (hm : T.IsMono m) : T.codOf (T.chiOf m hm) = T.omegaOf := by
  have hv : Valid T.model [arr] [dfd (chi (x 0))] ⟨cod (chi (x 0)), omega⟩ := T.axClassifier 6
  have hq := hv [⟨arr, m⟩] rfl (by simpa using T.holds_chiOf hm)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_chiOf hm, op_codOf])
    (by simp_eval [op_omegaOf])

/-- Truth after the morphism to the terminal object composes. -/
theorem codOf_bangOf_eq_domOf_truOf (a : T.Obj) :
    T.codOf (T.bangOf a) = T.domOf T.truOf :=
  (T.codOf_bangOf a).trans T.domOf_truOf.symm

/-- A characteristic map's square commutes. -/
theorem chiOf_square {m : T.Ar} (hm : T.IsMono m) :
    T.compOf (T.chiOf m hm) m (T.domOf_chiOf hm).symm =
      T.compOf T.truOf (T.bangOf (T.domOf m)) (T.codOf_bangOf_eq_domOf_truOf _) := by
  have hv : Valid T.model [arr] [dfd (chi (x 0))]
      ⟨comp (chi (x 0)) (x 0), comp tru (bang (dom (x 0)))⟩ := T.axClassifier 7
  have hq := hv [⟨arr, m⟩] rfl (by simpa using T.holds_chiOf hm)
  have h1 := T.op_compOf (T.domOf_chiOf hm).symm
  have h2 := T.op_compOf (T.codOf_bangOf_eq_domOf_truOf (T.domOf m))
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_chiOf hm, h1])
    (by simp_eval [op_truOf, op_domOf, op_bangOf, h2])

/-- A morphism into the subobject classifier and truth after the morphism to the terminal
object are parallel. -/
theorem par_truth {φ : T.Ar} (hφ : T.codOf φ = T.omegaOf) :
    T.Par φ (T.compOf T.truOf (T.bangOf (T.domOf φ)) (T.codOf_bangOf_eq_domOf_truOf _)) :=
  ⟨((T.domOf_bangOf _).symm.trans (T.domOf_compOf _).symm),
    hφ.trans (T.codOf_truOf.symm.trans (T.codOf_compOf _).symm)⟩

/-- The equalizer of a morphism into the classifier and truth: the pullback of truth along
it. -/
abbrev truthEqOf (φ : T.Ar) (hφ : T.codOf φ = T.omegaOf) : T.Obj :=
  T.eqzOf φ _ (T.par_truth hφ)

/-- The inclusion of {lit}`truthEqOf`. -/
abbrev truthInclOf (φ : T.Ar) (hφ : T.codOf φ = T.omegaOf) : T.Ar :=
  T.eqInclOf φ _ (T.par_truth hφ)

/-- A monomorphism equalizes its characteristic map and truth after the morphism to the
terminal object. -/
theorem chiOf_equalizes {m : T.Ar} (hm : T.IsMono m) :
    T.compOf (T.chiOf m hm) m (T.domOf_chiOf hm).symm =
      T.compOf (T.compOf T.truOf (T.bangOf (T.domOf (T.chiOf m hm)))
        (T.codOf_bangOf_eq_domOf_truOf _)) m
        ((T.domOf_chiOf hm).symm.trans (T.par_truth (T.codOf_chiOf hm)).1) := by
  have hb : T.codOf m = T.domOf (T.bangOf (T.domOf (T.chiOf m hm))) :=
    (T.domOf_chiOf hm).symm.trans (T.domOf_bangOf _).symm
  rw [T.chiOf_square hm, ← T.compOf_assoc hb (T.codOf_bangOf_eq_domOf_truOf _)]
  refine T.compOf_congr rfl ?_ _ _
  rw [T.compOf_congr (congrArg T.bangOf (T.domOf_chiOf hm)) rfl hb (T.domOf_bangOf _).symm,
    T.compOf_bangOf]

/-- The factorization of a monomorphism through the pullback of truth along its
characteristic map. -/
abbrev truthLiftOf (m : T.Ar) (hm : T.IsMono m) : T.Ar :=
  T.eqLiftOf (T.chiOf m hm) _ m (T.par_truth (T.codOf_chiOf hm)) (T.domOf_chiOf hm).symm
    (T.chiOf_equalizes hm)

/-- The value of the pullback of truth along a characteristic map. -/
theorem op_truthEq {m : T.Ar} (hm : T.IsMono m) :
    T.model.op 10 [⟨arr, T.chiOf m hm⟩, ⟨arr, T.compOf T.truOf (T.bangOf (T.domOf (T.chiOf m hm)))
      (T.codOf_bangOf_eq_domOf_truOf _)⟩] =
      Part.some ⟨obj, T.truthEqOf (T.chiOf m hm) (T.codOf_chiOf hm)⟩ :=
  T.op_eqzOf _

/-- The value of a monomorphism's factorization through the pullback of truth. -/
theorem op_truthLift {m : T.Ar} (hm : T.IsMono m) :
    T.model.op 12 [⟨arr, T.chiOf m hm⟩, ⟨arr, T.compOf T.truOf
      (T.bangOf (T.domOf (T.chiOf m hm))) (T.codOf_bangOf_eq_domOf_truOf _)⟩, ⟨arr, m⟩] =
      Part.some ⟨arr, T.truthLiftOf m hm⟩ :=
  T.op_eqLiftOf _ _ _

/-- A monomorphism's pullback comparison has an inverse. -/
theorem chiInvOf_exists {m : T.Ar} (hm : T.IsMono m) :
    ∃ c, T.model.op 28 [⟨arr, m⟩] = Part.some ⟨arr, c⟩ := by
  have hv : Valid T.model [arr] [dfd (chi (x 0))] (dfd (chiInv (x 0))) := T.axClassifier 9
  obtain ⟨w, hw, -⟩ := hv [⟨arr, m⟩] rfl (by simpa using T.holds_chiOf hm)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The inverse of a monomorphism's factorization through the pullback of truth along its
characteristic map. -/
def chiInvOf (m : T.Ar) (hm : T.IsMono m) : T.Ar := T.model.get (T.chiInvOf_exists hm)

/-- The model's inverse of a pullback comparison. -/
@[simp] theorem op_chiInvOf {m : T.Ar} (hm : T.IsMono m) :
    T.model.op 28 [⟨arr, m⟩] = Part.some ⟨arr, T.chiInvOf m hm⟩ :=
  T.model.op_eq_get _

/-- The domain of the inverse is the pullback of truth. -/
theorem domOf_chiInvOf {m : T.Ar} (hm : T.IsMono m) :
    T.domOf (T.chiInvOf m hm) = T.truthEqOf (T.chiOf m hm) (T.codOf_chiOf hm) := by
  have hv : Valid T.model [arr] [dfd (chi (x 0))] ⟨dom (chiInv (x 0)), truthEq (chi (x 0))⟩ :=
    T.axClassifier 10
  have hq := hv [⟨arr, m⟩] rfl (by simpa using T.holds_chiOf hm)
  have hc := T.op_compOf (T.codOf_bangOf_eq_domOf_truOf (T.domOf (T.chiOf m hm)))
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_chiInvOf hm, op_domOf])
    (by simp_eval [T.op_chiOf hm, op_domOf, op_bangOf, op_truOf, hc, T.op_truthEq hm])

/-- The codomain of the inverse is the monomorphism's domain. -/
theorem codOf_chiInvOf {m : T.Ar} (hm : T.IsMono m) :
    T.codOf (T.chiInvOf m hm) = T.domOf m := by
  have hv : Valid T.model [arr] [dfd (chi (x 0))] ⟨cod (chiInv (x 0)), dom (x 0)⟩ :=
    T.axClassifier 11
  have hq := hv [⟨arr, m⟩] rfl (by simpa using T.holds_chiOf hm)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_chiInvOf hm, op_codOf])
    (by simp_eval [op_domOf])

/-- The codomain of a monomorphism's pullback comparison. -/
theorem codOf_truthLiftOf {m : T.Ar} (hm : T.IsMono m) :
    T.codOf (T.truthLiftOf m hm) = T.truthEqOf (T.chiOf m hm) (T.codOf_chiOf hm) :=
  T.codOf_eqLiftOf _ _ _

/-- The domain of a monomorphism's pullback comparison. -/
theorem domOf_truthLiftOf {m : T.Ar} (hm : T.IsMono m) :
    T.domOf (T.truthLiftOf m hm) = T.domOf m :=
  T.domOf_eqLiftOf _ _ _

/-- The comparison after its inverse is the identity of the pullback. -/
theorem truthLiftOf_chiInvOf {m : T.Ar} (hm : T.IsMono m) :
    T.compOf (T.truthLiftOf m hm) (T.chiInvOf m hm)
      ((T.codOf_chiInvOf hm).trans (T.domOf_truthLiftOf hm).symm) =
      T.idOf (T.truthEqOf (T.chiOf m hm) (T.codOf_chiOf hm)) := by
  have hv : Valid T.model [arr] [dfd (chi (x 0))]
      ⟨comp (truthLift (chi (x 0)) (x 0)) (chiInv (x 0)), idt (truthEq (chi (x 0)))⟩ :=
    T.axClassifier 12
  have hq := hv [⟨arr, m⟩] rfl (by simpa using T.holds_chiOf hm)
  have hc := T.op_compOf (T.codOf_bangOf_eq_domOf_truOf (T.domOf (T.chiOf m hm)))
  have hl := T.op_compOf ((T.codOf_chiInvOf hm).trans (T.domOf_truthLiftOf hm).symm)
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [T.op_chiOf hm, op_domOf, op_bangOf, op_truOf, hc, T.op_truthLift hm,
      T.op_chiInvOf hm, hl])
    (by simp_eval [T.op_chiOf hm, op_domOf, op_bangOf, op_truOf, hc, T.op_truthEq hm, op_idOf])

/-- The inverse after the comparison is the identity of the monomorphism's domain. -/
theorem chiInvOf_truthLiftOf {m : T.Ar} (hm : T.IsMono m) :
    T.compOf (T.chiInvOf m hm) (T.truthLiftOf m hm)
      ((T.codOf_truthLiftOf hm).trans (T.domOf_chiInvOf hm).symm) = T.idOf (T.domOf m) := by
  have hv : Valid T.model [arr] [dfd (chi (x 0))]
      ⟨comp (chiInv (x 0)) (truthLift (chi (x 0)) (x 0)), idt (dom (x 0))⟩ := T.axClassifier 13
  have hq := hv [⟨arr, m⟩] rfl (by simpa using T.holds_chiOf hm)
  have hc := T.op_compOf (T.codOf_bangOf_eq_domOf_truOf (T.domOf (T.chiOf m hm)))
  have hl := T.op_compOf ((T.codOf_truthLiftOf hm).trans (T.domOf_chiInvOf hm).symm)
  exact T.val_inj <| T.holds_eq hq
    (by simp_eval [T.op_chiOf hm, op_domOf, op_bangOf, op_truOf, hc, T.op_truthLift hm,
      T.op_chiInvOf hm, hl])
    (by simp_eval [op_domOf, op_idOf])

/-- A morphism into the classifier along which a monomorphism is a pullback of truth, by an
isomorphism onto the equalizer, is the monomorphism's characteristic map. -/
theorem eq_chiOf {m φ i j : T.Ar} (hm : T.IsMono m) (hd : T.domOf φ = T.codOf m)
    (hc : T.codOf φ = T.omegaOf) (hi : T.codOf i = T.domOf (T.truthInclOf φ hc))
    (hmi : T.compOf (T.truthInclOf φ hc) i hi = m) (hij : T.codOf j = T.domOf i)
    (hid : T.compOf i j hij = T.idOf (T.truthEqOf φ hc)) (hji : T.codOf i = T.domOf j)
    (hjd : T.compOf j i hji = T.idOf (T.domOf m)) : φ = T.chiOf m hm := by
  have hv : Valid T.model [arr, arr, arr, arr]
      [dfd (chi (x 0)), ⟨dom (x 1), cod (x 0)⟩, ⟨cod (x 1), omega⟩,
        ⟨comp (truthIncl (x 1)) (x 2), x 0⟩, ⟨comp (x 2) (x 3), idt (truthEq (x 1))⟩,
        ⟨comp (x 3) (x 2), idt (dom (x 0))⟩]
      ⟨x 1, chi (x 0)⟩ := T.axClassifier 14
  have hb := T.op_compOf (T.codOf_bangOf_eq_domOf_truOf (T.domOf φ))
  have hinc := T.op_eqInclOf (T.par_truth hc)
  have hq := hv [⟨arr, m⟩, ⟨arr, φ⟩, ⟨arr, i⟩, ⟨arr, j⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    refine ⟨⟨⟨arr, T.chiOf m hm⟩, by simp_eval [T.op_chiOf hm], by simp_eval [T.op_chiOf hm]⟩,
      ⟨⟨obj, T.codOf m⟩, by simp_eval [op_domOf, hd],
      by simp_eval [op_codOf]⟩, ⟨⟨obj, T.omegaOf⟩, by simp_eval [op_codOf, hc],
      by simp_eval [op_omegaOf]⟩, ⟨⟨arr, m⟩, ?_, by simp_eval []⟩,
      ⟨⟨arr, T.idOf (T.truthEqOf φ hc)⟩, ?_, ?_⟩, ⟨⟨arr, T.idOf (T.domOf m)⟩, ?_, ?_⟩⟩
    · simp_eval [op_domOf, op_bangOf, op_truOf, hb, hinc, T.op_compOf hi, hmi]
    · simp_eval [T.op_compOf hij, hid]
    · simp_eval [op_domOf, op_bangOf, op_truOf, hb, T.op_eqzOf (T.par_truth hc), op_idOf]
    · simp_eval [T.op_compOf hji, hjd]
    · simp_eval [op_domOf, op_idOf])
  exact T.val_inj <| T.holds_eq hq (by simp_eval []) (by simp_eval [T.op_chiOf hm])

/-- An axiom of the natural numbers block, by index, is valid in the model. -/
theorem axNat (k : ℕ) (hk : k < natAxioms.length := by decide) :
    (natAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- Zero is defined. -/
theorem zeroNOf_exists : ∃ z, T.model.op 30 [] = Part.some ⟨arr, z⟩ := by
  have h : Valid T.model [] [] ⟨dom zeroN, one⟩ := T.axNat 0
  obtain ⟨w, hw, -⟩ := h [] rfl (by simp)
  simp_eval [] at hw
  obtain ⟨l, hl, -⟩ := part_bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := part_bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- Zero, from the terminal object to the natural numbers object. -/
def zeroNOf : T.Ar := T.model.get T.zeroNOf_exists

/-- The model's zero. -/
@[simp] theorem op_zeroNOf : T.model.op 30 [] = Part.some ⟨arr, T.zeroNOf⟩ := T.model.op_eq_get _

/-- The natural numbers object is defined. -/
theorem natOf_exists : ∃ n, T.model.op 29 [] = Part.some ⟨obj, n⟩ := by
  have h : Valid T.model [] [] ⟨cod zeroN, nat⟩ := T.axNat 1
  obtain ⟨w, -, hw⟩ := h [] rfl (by simp)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The natural numbers object. -/
def natOf : T.Obj := T.model.get T.natOf_exists

/-- The model's natural numbers object. -/
@[simp] theorem op_natOf : T.model.op 29 [] = Part.some ⟨obj, T.natOf⟩ := T.model.op_eq_get _

/-- The successor is defined. -/
theorem succOf_exists : ∃ z, T.model.op 31 [] = Part.some ⟨arr, z⟩ := by
  have h : Valid T.model [] [] ⟨dom succ, nat⟩ := T.axNat 2
  obtain ⟨w, hw, -⟩ := h [] rfl (by simp)
  simp_eval [] at hw
  obtain ⟨l, hl, -⟩ := part_bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := part_bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- The successor. -/
def succOf : T.Ar := T.model.get T.succOf_exists

/-- The model's successor. -/
@[simp] theorem op_succOf : T.model.op 31 [] = Part.some ⟨arr, T.succOf⟩ := T.model.op_eq_get _

/-- The domain of zero is the terminal object. -/
theorem domOf_zeroNOf : T.domOf T.zeroNOf = T.oneOf := by
  have h : Valid T.model [] [] ⟨dom zeroN, one⟩ := T.axNat 0
  exact T.val_inj <| T.holds_eq (h [] rfl (by simp)) (by simp_eval [op_zeroNOf, op_domOf])
    (by simp_eval [op_oneOf])

/-- The codomain of zero is the natural numbers object. -/
theorem codOf_zeroNOf : T.codOf T.zeroNOf = T.natOf := by
  have h : Valid T.model [] [] ⟨cod zeroN, nat⟩ := T.axNat 1
  exact T.val_inj <| T.holds_eq (h [] rfl (by simp)) (by simp_eval [op_zeroNOf, op_codOf])
    (by simp_eval [op_natOf])

/-- The domain of the successor is the natural numbers object. -/
theorem domOf_succOf : T.domOf T.succOf = T.natOf := by
  have h : Valid T.model [] [] ⟨dom succ, nat⟩ := T.axNat 2
  exact T.val_inj <| T.holds_eq (h [] rfl (by simp)) (by simp_eval [op_succOf, op_domOf])
    (by simp_eval [op_natOf])

/-- The codomain of the successor is the natural numbers object. -/
theorem codOf_succOf : T.codOf T.succOf = T.natOf := by
  have h : Valid T.model [] [] ⟨cod succ, nat⟩ := T.axNat 3
  exact T.val_inj <| T.holds_eq (h [] rfl (by simp)) (by simp_eval [op_succOf, op_codOf])
    (by simp_eval [op_natOf])

/-- A start and a step of one object define a recursion from the natural numbers object. -/
theorem natRecOf_exists {z s : T.Ar} (hz : T.domOf z = T.oneOf) (hzs : T.codOf z = T.domOf s)
    (hs : T.domOf s = T.codOf s) :
    ∃ r, T.model.op 32 [⟨arr, z⟩, ⟨arr, s⟩] = Part.some ⟨arr, r⟩ := by
  have hv : Valid T.model [arr, arr] [⟨dom (x 0), one⟩, ⟨cod (x 0), dom (x 1)⟩,
      ⟨dom (x 1), cod (x 1)⟩] (dfd (natRec (x 0) (x 1))) := T.axNat 7
  obtain ⟨w, hw, -⟩ := hv [⟨arr, z⟩, ⟨arr, s⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    exact ⟨⟨⟨obj, T.oneOf⟩, by simp_eval [op_domOf, hz], by simp_eval [op_oneOf]⟩,
      ⟨⟨obj, T.domOf s⟩, by simp_eval [op_codOf, hzs], by simp_eval [op_domOf]⟩,
      ⟨⟨obj, T.codOf s⟩, by simp_eval [op_domOf, hs], by simp_eval [op_codOf]⟩⟩)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The morphism from the natural numbers object that recursion with a start and a step
defines. -/
def natRecOf (z s : T.Ar) (hz : T.domOf z = T.oneOf) (hzs : T.codOf z = T.domOf s)
    (hs : T.domOf s = T.codOf s) : T.Ar :=
  T.model.get (T.natRecOf_exists hz hzs hs)

/-- The model's recursion. -/
@[simp] theorem op_natRecOf {z s : T.Ar} (hz : T.domOf z = T.oneOf)
    (hzs : T.codOf z = T.domOf s) (hs : T.domOf s = T.codOf s) :
    T.model.op 32 [⟨arr, z⟩, ⟨arr, s⟩] = Part.some ⟨arr, T.natRecOf z s hz hzs hs⟩ :=
  T.model.op_eq_get _

/-- A recursion is defined at its start and step. -/
theorem holds_natRecOf {z s : T.Ar} (hz : T.domOf z = T.oneOf) (hzs : T.codOf z = T.domOf s)
    (hs : T.domOf s = T.codOf s) :
    (dfd (natRec (x 0) (x 1))).Holds T.model [⟨arr, z⟩, ⟨arr, s⟩] :=
  ⟨⟨arr, T.natRecOf z s hz hzs hs⟩, by simp_eval [T.op_natRecOf hz hzs hs],
    by simp_eval [T.op_natRecOf hz hzs hs]⟩

/-- The domain of a recursion is the natural numbers object. -/
theorem domOf_natRecOf {z s : T.Ar} (hz : T.domOf z = T.oneOf) (hzs : T.codOf z = T.domOf s)
    (hs : T.domOf s = T.codOf s) : T.domOf (T.natRecOf z s hz hzs hs) = T.natOf := by
  have hv : Valid T.model [arr, arr] [dfd (natRec (x 0) (x 1))]
      ⟨dom (natRec (x 0) (x 1)), nat⟩ := T.axNat 8
  have hq := hv [⟨arr, z⟩, ⟨arr, s⟩] rfl (by simpa using T.holds_natRecOf hz hzs hs)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_natRecOf hz hzs hs, op_domOf])
    (by simp_eval [op_natOf])

/-- The codomain of a recursion is its start's. -/
theorem codOf_natRecOf {z s : T.Ar} (hz : T.domOf z = T.oneOf) (hzs : T.codOf z = T.domOf s)
    (hs : T.domOf s = T.codOf s) : T.codOf (T.natRecOf z s hz hzs hs) = T.codOf z := by
  have hv : Valid T.model [arr, arr] [dfd (natRec (x 0) (x 1))]
      ⟨cod (natRec (x 0) (x 1)), cod (x 0)⟩ := T.axNat 9
  have hq := hv [⟨arr, z⟩, ⟨arr, s⟩] rfl (by simpa using T.holds_natRecOf hz hzs hs)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_natRecOf hz hzs hs, op_codOf])
    (by simp_eval [op_codOf])

/-- A recursion after zero is its start. -/
theorem natRecOf_zeroNOf {z s : T.Ar} (hz : T.domOf z = T.oneOf) (hzs : T.codOf z = T.domOf s)
    (hs : T.domOf s = T.codOf s) :
    T.compOf (T.natRecOf z s hz hzs hs) T.zeroNOf
      (T.codOf_zeroNOf.trans (T.domOf_natRecOf hz hzs hs).symm) = z := by
  have hv : Valid T.model [arr, arr] [dfd (natRec (x 0) (x 1))]
      ⟨comp (natRec (x 0) (x 1)) zeroN, x 0⟩ := T.axNat 10
  have hq := hv [⟨arr, z⟩, ⟨arr, s⟩] rfl (by simpa using T.holds_natRecOf hz hzs hs)
  have hc := T.op_compOf (T.codOf_zeroNOf.trans (T.domOf_natRecOf hz hzs hs).symm)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_natRecOf hz hzs hs, op_zeroNOf, hc])
    (by simp_eval [])

/-- A recursion after the successor is the step after the recursion. -/
theorem natRecOf_succOf {z s : T.Ar} (hz : T.domOf z = T.oneOf) (hzs : T.codOf z = T.domOf s)
    (hs : T.domOf s = T.codOf s) :
    T.compOf (T.natRecOf z s hz hzs hs) T.succOf
        (T.codOf_succOf.trans (T.domOf_natRecOf hz hzs hs).symm) =
      T.compOf s (T.natRecOf z s hz hzs hs) ((T.codOf_natRecOf hz hzs hs).trans hzs) := by
  have hv : Valid T.model [arr, arr] [dfd (natRec (x 0) (x 1))]
      ⟨comp (natRec (x 0) (x 1)) succ, comp (x 1) (natRec (x 0) (x 1))⟩ := T.axNat 11
  have hq := hv [⟨arr, z⟩, ⟨arr, s⟩] rfl (by simpa using T.holds_natRecOf hz hzs hs)
  have h1 := T.op_compOf (T.codOf_succOf.trans (T.domOf_natRecOf hz hzs hs).symm)
  have h2 := T.op_compOf ((T.codOf_natRecOf hz hzs hs).trans hzs)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_natRecOf hz hzs hs, op_succOf, h1])
    (by simp_eval [T.op_natRecOf hz hzs hs, h2])

/-- A morphism from the natural numbers object satisfying the recursion equations is the
recursion. -/
theorem eq_natRecOf {z s u : T.Ar} (hz : T.domOf z = T.oneOf) (hzs : T.codOf z = T.domOf s)
    (hs : T.domOf s = T.codOf s) (hu : T.domOf u = T.natOf)
    (hu0 : T.compOf u T.zeroNOf (T.codOf_zeroNOf.trans hu.symm) = z)
    (hus : T.codOf u = T.domOf s)
    (hu1 : T.compOf u T.succOf (T.codOf_succOf.trans hu.symm) = T.compOf s u hus) :
    u = T.natRecOf z s hz hzs hs := by
  have hv : Valid T.model [arr, arr, arr]
      [dfd (natRec (x 0) (x 1)), ⟨dom (x 2), nat⟩, ⟨comp (x 2) zeroN, x 0⟩,
        ⟨comp (x 2) succ, comp (x 1) (x 2)⟩] ⟨x 2, natRec (x 0) (x 1)⟩ := T.axNat 12
  have hq := hv [⟨arr, z⟩, ⟨arr, s⟩, ⟨arr, u⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    exact ⟨⟨⟨arr, T.natRecOf z s hz hzs hs⟩, by simp_eval [T.op_natRecOf hz hzs hs],
        by simp_eval [T.op_natRecOf hz hzs hs]⟩,
      ⟨⟨obj, T.natOf⟩, by simp_eval [op_domOf, hu], by simp_eval [op_natOf]⟩,
      ⟨⟨arr, z⟩, by simp_eval [op_zeroNOf, T.op_compOf (T.codOf_zeroNOf.trans hu.symm), hu0],
        by simp_eval []⟩,
      ⟨⟨arr, T.compOf s u hus⟩,
        by simp_eval [op_succOf, T.op_compOf (T.codOf_succOf.trans hu.symm), hu1],
        by simp_eval [T.op_compOf hus]⟩⟩)
  exact T.val_inj <| T.holds_eq hq (by simp_eval []) (by simp_eval [T.op_natRecOf hz hzs hs])

/-- The morphism {lit}`id × f`, from the product of {lit}`a` and the domain of {lit}`f` to the
product of {lit}`a` and its codomain. -/
abbrev prodMapRightOf (a : T.Obj) (f : T.Ar) : T.Ar :=
  T.pairOf (T.fstOf a (T.domOf f)) (T.compOf f (T.sndOf a (T.domOf f)) (T.codOf_sndOf _ _))
    ((T.domOf_fstOf _ _).trans ((T.domOf_sndOf _ _).symm.trans (T.domOf_compOf _).symm))

/-- The domain of {lit}`id × f`. -/
theorem domOf_prodMapRightOf (a : T.Obj) (f : T.Ar) :
    T.domOf (T.prodMapRightOf a f) = T.prodOf a (T.domOf f) :=
  (T.domOf_pairOf _).trans (T.domOf_fstOf _ _)

/-- The codomain of {lit}`id × f`. -/
theorem codOf_prodMapRightOf (a : T.Obj) (f : T.Ar) :
    T.codOf (T.prodMapRightOf a f) = T.prodOf a (T.codOf f) := by
  rw [prodMapRightOf, codOf_pairOf, codOf_fstOf, codOf_compOf]

/-- The rewriting lemmas of {lit}`id × f`'s value: its projections, its composite and its
pairing. -/
theorem op_prodMapRight_parts (a : T.Obj) (f : T.Ar) :
    T.model.op 3 [⟨arr, f⟩, ⟨arr, T.sndOf a (T.domOf f)⟩] =
        Part.some ⟨arr, T.compOf f (T.sndOf a (T.domOf f)) (T.codOf_sndOf _ _)⟩ ∧
      T.model.op 9 [⟨arr, T.fstOf a (T.domOf f)⟩,
        ⟨arr, T.compOf f (T.sndOf a (T.domOf f)) (T.codOf_sndOf _ _)⟩] =
        Part.some ⟨arr, T.prodMapRightOf a f⟩ :=
  ⟨T.op_compOf _, T.op_pairOf _⟩

/-- An axiom of the list block, by index, is valid in the model. -/
theorem axList (k : ℕ) (hk : k < listAxioms.length := by decide) :
    (listAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- Every object has a list object. -/
theorem listOf_exists (a : T.Obj) : ∃ l, T.model.op 33 [⟨obj, a⟩] = Part.some ⟨obj, l⟩ := by
  have h : Valid T.model [obj] [] (dfd (list (x 0))) := T.axList 0
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩] rfl (by simp)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The list object of an object. -/
def listOf (a : T.Obj) : T.Obj := T.model.get (T.listOf_exists a)

/-- The model's list object. -/
@[simp] theorem op_listOf (a : T.Obj) : T.model.op 33 [⟨obj, a⟩] = Part.some ⟨obj, T.listOf a⟩ :=
  T.model.op_eq_get _

/-- Every list object has the empty list. -/
theorem nilOf_exists (a : T.Obj) : ∃ n, T.model.op 34 [⟨obj, a⟩] = Part.some ⟨arr, n⟩ := by
  have h : Valid T.model [obj] [] ⟨dom (nil (x 0)), one⟩ := T.axList 1
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩] rfl (by simp)
  simp_eval [] at hw
  obtain ⟨l, hl, -⟩ := part_bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := part_bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- The empty list, from the terminal object. -/
def nilOf (a : T.Obj) : T.Ar := T.model.get (T.nilOf_exists a)

/-- The model's empty list. -/
@[simp] theorem op_nilOf (a : T.Obj) : T.model.op 34 [⟨obj, a⟩] = Part.some ⟨arr, T.nilOf a⟩ :=
  T.model.op_eq_get _

/-- Every list object has the construction of a list. -/
theorem consOf_exists (a : T.Obj) : ∃ c, T.model.op 35 [⟨obj, a⟩] = Part.some ⟨arr, c⟩ := by
  have h : Valid T.model [obj] [] ⟨dom (cons (x 0)), prod (x 0) (list (x 0))⟩ := T.axList 3
  obtain ⟨w, hw, -⟩ := h [⟨obj, a⟩] rfl (by simp)
  simp_eval [] at hw
  obtain ⟨l, hl, -⟩ := part_bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := part_bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- The construction of a list from an element and a list. -/
def consOf (a : T.Obj) : T.Ar := T.model.get (T.consOf_exists a)

/-- The model's construction of a list. -/
@[simp] theorem op_consOf (a : T.Obj) : T.model.op 35 [⟨obj, a⟩] = Part.some ⟨arr, T.consOf a⟩ :=
  T.model.op_eq_get _

/-- The domain of the empty list. -/
theorem domOf_nilOf (a : T.Obj) : T.domOf (T.nilOf a) = T.oneOf := by
  have h : Valid T.model [obj] [] ⟨dom (nil (x 0)), one⟩ := T.axList 1
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩] rfl (by simp))
    (by simp_eval [op_nilOf, op_domOf]) (by simp_eval [op_oneOf])

/-- The codomain of the empty list. -/
theorem codOf_nilOf (a : T.Obj) : T.codOf (T.nilOf a) = T.listOf a := by
  have h : Valid T.model [obj] [] ⟨cod (nil (x 0)), list (x 0)⟩ := T.axList 2
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩] rfl (by simp))
    (by simp_eval [op_nilOf, op_codOf]) (by simp_eval [op_listOf])

/-- The domain of the construction of a list. -/
theorem domOf_consOf (a : T.Obj) : T.domOf (T.consOf a) = T.prodOf a (T.listOf a) := by
  have h : Valid T.model [obj] [] ⟨dom (cons (x 0)), prod (x 0) (list (x 0))⟩ := T.axList 3
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩] rfl (by simp))
    (by simp_eval [op_consOf, op_domOf]) (by simp_eval [op_listOf, op_prodOf])

/-- The codomain of the construction of a list. -/
theorem codOf_consOf (a : T.Obj) : T.codOf (T.consOf a) = T.listOf a := by
  have h : Valid T.model [obj] [] ⟨cod (cons (x 0)), list (x 0)⟩ := T.axList 4
  exact T.val_inj <| T.holds_eq (h [⟨obj, a⟩] rfl (by simp))
    (by simp_eval [op_consOf, op_codOf]) (by simp_eval [op_listOf])

/-- A start and a step over an element object define a recursion from its list object. -/
theorem listRecOf_exists {a : T.Obj} {z s : T.Ar} (hz : T.domOf z = T.oneOf)
    (hzs : T.codOf z = T.codOf s) (hs : T.domOf s = T.prodOf a (T.codOf s)) :
    ∃ r, T.model.op 36 [⟨obj, a⟩, ⟨arr, z⟩, ⟨arr, s⟩] = Part.some ⟨arr, r⟩ := by
  have hv : Valid T.model [obj, arr, arr] [⟨dom (x 1), one⟩, ⟨cod (x 1), cod (x 2)⟩,
      ⟨dom (x 2), prod (x 0) (cod (x 2))⟩] (dfd (listRec (x 0) (x 1) (x 2))) := T.axList 8
  obtain ⟨w, hw, -⟩ := hv [⟨obj, a⟩, ⟨arr, z⟩, ⟨arr, s⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    exact ⟨⟨⟨obj, T.oneOf⟩, by simp_eval [op_domOf, hz], by simp_eval [op_oneOf]⟩,
      ⟨⟨obj, T.codOf s⟩, by simp_eval [op_codOf, hzs], by simp_eval [op_codOf]⟩,
      ⟨⟨obj, T.prodOf a (T.codOf s)⟩, by simp_eval [op_domOf, hs],
        by simp_eval [op_codOf, op_prodOf]⟩⟩)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The morphism from the list object of {lit}`a` that recursion with a start and a step
defines. -/
def listRecOf (a : T.Obj) (z s : T.Ar) (hz : T.domOf z = T.oneOf) (hzs : T.codOf z = T.codOf s)
    (hs : T.domOf s = T.prodOf a (T.codOf s)) : T.Ar :=
  T.model.get (T.listRecOf_exists hz hzs hs)

/-- The model's recursion on lists. -/
@[simp] theorem op_listRecOf {a : T.Obj} {z s : T.Ar} (hz : T.domOf z = T.oneOf)
    (hzs : T.codOf z = T.codOf s) (hs : T.domOf s = T.prodOf a (T.codOf s)) :
    T.model.op 36 [⟨obj, a⟩, ⟨arr, z⟩, ⟨arr, s⟩] = Part.some ⟨arr, T.listRecOf a z s hz hzs hs⟩ :=
  T.model.op_eq_get _

/-- A recursion on lists is defined at its arguments. -/
theorem holds_listRecOf {a : T.Obj} {z s : T.Ar} (hz : T.domOf z = T.oneOf)
    (hzs : T.codOf z = T.codOf s) (hs : T.domOf s = T.prodOf a (T.codOf s)) :
    (dfd (listRec (x 0) (x 1) (x 2))).Holds T.model [⟨obj, a⟩, ⟨arr, z⟩, ⟨arr, s⟩] :=
  ⟨⟨arr, T.listRecOf a z s hz hzs hs⟩, by simp_eval [T.op_listRecOf hz hzs hs],
    by simp_eval [T.op_listRecOf hz hzs hs]⟩

/-- The domain of a recursion on lists is the list object. -/
theorem domOf_listRecOf {a : T.Obj} {z s : T.Ar} (hz : T.domOf z = T.oneOf)
    (hzs : T.codOf z = T.codOf s) (hs : T.domOf s = T.prodOf a (T.codOf s)) :
    T.domOf (T.listRecOf a z s hz hzs hs) = T.listOf a := by
  have hv : Valid T.model [obj, arr, arr] [dfd (listRec (x 0) (x 1) (x 2))]
      ⟨dom (listRec (x 0) (x 1) (x 2)), list (x 0)⟩ := T.axList 9
  have hq := hv [⟨obj, a⟩, ⟨arr, z⟩, ⟨arr, s⟩] rfl (by simpa using T.holds_listRecOf hz hzs hs)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_listRecOf hz hzs hs, op_domOf])
    (by simp_eval [op_listOf])

/-- The codomain of a recursion on lists is its start's. -/
theorem codOf_listRecOf {a : T.Obj} {z s : T.Ar} (hz : T.domOf z = T.oneOf)
    (hzs : T.codOf z = T.codOf s) (hs : T.domOf s = T.prodOf a (T.codOf s)) :
    T.codOf (T.listRecOf a z s hz hzs hs) = T.codOf z := by
  have hv : Valid T.model [obj, arr, arr] [dfd (listRec (x 0) (x 1) (x 2))]
      ⟨cod (listRec (x 0) (x 1) (x 2)), cod (x 1)⟩ := T.axList 10
  have hq := hv [⟨obj, a⟩, ⟨arr, z⟩, ⟨arr, s⟩] rfl (by simpa using T.holds_listRecOf hz hzs hs)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_listRecOf hz hzs hs, op_codOf])
    (by simp_eval [op_codOf])

/-- A recursion on lists after the empty list is its start. -/
theorem listRecOf_nilOf {a : T.Obj} {z s : T.Ar} (hz : T.domOf z = T.oneOf)
    (hzs : T.codOf z = T.codOf s) (hs : T.domOf s = T.prodOf a (T.codOf s)) :
    T.compOf (T.listRecOf a z s hz hzs hs) (T.nilOf a)
      ((T.codOf_nilOf a).trans (T.domOf_listRecOf hz hzs hs).symm) = z := by
  have hv : Valid T.model [obj, arr, arr] [dfd (listRec (x 0) (x 1) (x 2))]
      ⟨comp (listRec (x 0) (x 1) (x 2)) (nil (x 0)), x 1⟩ := T.axList 11
  have hq := hv [⟨obj, a⟩, ⟨arr, z⟩, ⟨arr, s⟩] rfl (by simpa using T.holds_listRecOf hz hzs hs)
  have hc := T.op_compOf ((T.codOf_nilOf a).trans (T.domOf_listRecOf hz hzs hs).symm)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_listRecOf hz hzs hs, op_nilOf, hc])
    (by simp_eval [])

/-- The step composes with the product of the element object and a recursion's codomain. -/
theorem codOf_prodMapRightOf_listRecOf {a : T.Obj} {z s : T.Ar} (hz : T.domOf z = T.oneOf)
    (hzs : T.codOf z = T.codOf s) (hs : T.domOf s = T.prodOf a (T.codOf s)) :
    T.codOf (T.prodMapRightOf a (T.listRecOf a z s hz hzs hs)) = T.domOf s := by
  rw [codOf_prodMapRightOf, codOf_listRecOf, hzs, hs]

/-- A recursion on lists after the construction of a list is the step after the product of the
identity with the recursion. -/
theorem listRecOf_consOf {a : T.Obj} {z s : T.Ar} (hz : T.domOf z = T.oneOf)
    (hzs : T.codOf z = T.codOf s) (hs : T.domOf s = T.prodOf a (T.codOf s)) :
    T.compOf (T.listRecOf a z s hz hzs hs) (T.consOf a)
        ((T.codOf_consOf a).trans (T.domOf_listRecOf hz hzs hs).symm) =
      T.compOf s (T.prodMapRightOf a (T.listRecOf a z s hz hzs hs))
        (T.codOf_prodMapRightOf_listRecOf hz hzs hs) := by
  have hv : Valid T.model [obj, arr, arr] [dfd (listRec (x 0) (x 1) (x 2))]
      ⟨comp (listRec (x 0) (x 1) (x 2)) (cons (x 0)),
        comp (x 2) (prodMapRight (x 0) (listRec (x 0) (x 1) (x 2)))⟩ := T.axList 12
  have hq := hv [⟨obj, a⟩, ⟨arr, z⟩, ⟨arr, s⟩] rfl (by simpa using T.holds_listRecOf hz hzs hs)
  have h1 := T.op_compOf ((T.codOf_consOf a).trans (T.domOf_listRecOf hz hzs hs).symm)
  have h2 := T.op_compOf (T.codOf_prodMapRightOf_listRecOf hz hzs hs)
  obtain ⟨p1, p2⟩ := T.op_prodMapRight_parts a (T.listRecOf a z s hz hzs hs)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_listRecOf hz hzs hs, op_consOf, h1])
    (by simp_eval [T.op_listRecOf hz hzs hs, op_domOf, op_fstOf, op_sndOf, p1, p2, h2])

/-- A morphism from a list object satisfying the recursion equations is the recursion. -/
theorem eq_listRecOf {a : T.Obj} {z s u : T.Ar} (hz : T.domOf z = T.oneOf)
    (hzs : T.codOf z = T.codOf s) (hs : T.domOf s = T.prodOf a (T.codOf s))
    (hu : T.domOf u = T.listOf a)
    (hu0 : T.compOf u (T.nilOf a) ((T.codOf_nilOf a).trans hu.symm) = z)
    (hus : T.codOf (T.prodMapRightOf a u) = T.domOf s)
    (hu1 : T.compOf u (T.consOf a) ((T.codOf_consOf a).trans hu.symm) =
      T.compOf s (T.prodMapRightOf a u) hus) :
    u = T.listRecOf a z s hz hzs hs := by
  have hv : Valid T.model [obj, arr, arr, arr]
      [dfd (listRec (x 0) (x 1) (x 2)), ⟨dom (x 3), list (x 0)⟩, ⟨comp (x 3) (nil (x 0)), x 1⟩,
        ⟨comp (x 3) (cons (x 0)), comp (x 2) (prodMapRight (x 0) (x 3))⟩]
      ⟨x 3, listRec (x 0) (x 1) (x 2)⟩ := T.axList 13
  obtain ⟨p1, p2⟩ := T.op_prodMapRight_parts a u
  have hq := hv [⟨obj, a⟩, ⟨arr, z⟩, ⟨arr, s⟩, ⟨arr, u⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    exact ⟨⟨⟨arr, T.listRecOf a z s hz hzs hs⟩, by simp_eval [T.op_listRecOf hz hzs hs],
        by simp_eval [T.op_listRecOf hz hzs hs]⟩,
      ⟨⟨obj, T.listOf a⟩, by simp_eval [op_domOf, hu], by simp_eval [op_listOf]⟩,
      ⟨⟨arr, z⟩, by simp_eval [op_nilOf, T.op_compOf ((T.codOf_nilOf a).trans hu.symm), hu0],
        by simp_eval []⟩,
      ⟨⟨arr, T.compOf s (T.prodMapRightOf a u) hus⟩,
        by simp_eval [op_consOf, T.op_compOf ((T.codOf_consOf a).trans hu.symm), hu1],
        by simp_eval [op_domOf, op_fstOf, op_sndOf, p1, p2, T.op_compOf hus]⟩⟩)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [])
    (by simp_eval [T.op_listRecOf hz hzs hs])

/-- The rewriting lemmas of {lit}`f × id`'s value: its composite and its pairing. -/
theorem op_prodMapLeft_parts (f : T.Ar) (a : T.Obj) :
    T.model.op 3 [⟨arr, f⟩, ⟨arr, T.fstOf (T.domOf f) a⟩] =
        Part.some ⟨arr, T.compOf f (T.fstOf (T.domOf f) a) (T.codOf_fstOf _ _)⟩ ∧
      T.model.op 9 [⟨arr, T.compOf f (T.fstOf (T.domOf f) a) (T.codOf_fstOf _ _)⟩,
        ⟨arr, T.sndOf (T.domOf f) a⟩] = Part.some ⟨arr, T.prodMapLeftOf f a⟩ :=
  ⟨T.op_compOf _, T.op_pairOf _⟩

/-- The step of the list functor's action composes. -/
theorem codOf_prodMapLeftOf_listOf (f : T.Ar) :
    T.codOf (T.prodMapLeftOf f (T.listOf (T.codOf f))) = T.domOf (T.consOf (T.codOf f)) := by
  rw [codOf_prodMapLeftOf, domOf_consOf]

/-- The step of the list functor's action. -/
abbrev listMapStepOf (f : T.Ar) : T.Ar :=
  T.compOf (T.consOf (T.codOf f)) (T.prodMapLeftOf f (T.listOf (T.codOf f)))
    (T.codOf_prodMapLeftOf_listOf f)

/-- The codomain of the step of the list functor's action. -/
theorem codOf_listMapStepOf (f : T.Ar) :
    T.codOf (T.listMapStepOf f) = T.listOf (T.codOf f) :=
  (T.codOf_compOf _).trans (T.codOf_consOf _)

/-- The action of the list object on a morphism, by recursion. -/
abbrev listMapOf (f : T.Ar) : T.Ar :=
  T.listRecOf (T.domOf f) (T.nilOf (T.codOf f)) (T.listMapStepOf f) (T.domOf_nilOf _)
    ((T.codOf_nilOf _).trans (T.codOf_listMapStepOf f).symm)
    ((T.domOf_compOf _).trans ((T.domOf_prodMapLeftOf _ _).trans
      (congrArg (T.prodOf (T.domOf f)) (T.codOf_listMapStepOf f).symm)))

/-- The codomain of the list functor's action. -/
theorem codOf_listMapOf (f : T.Ar) : T.codOf (T.listMapOf f) = T.listOf (T.codOf f) :=
  (T.codOf_listRecOf _ _ _).trans (T.codOf_nilOf _)

/-- The domain of the list functor's action. -/
theorem domOf_listMapOf (f : T.Ar) : T.domOf (T.listMapOf f) = T.listOf (T.domOf f) :=
  T.domOf_listRecOf _ _ _

/-- The value of the list functor's action at a morphism. -/
theorem op_listMap_parts (f : T.Ar) :
    T.model.op 3 [⟨arr, T.consOf (T.codOf f)⟩, ⟨arr, T.prodMapLeftOf f (T.listOf (T.codOf f))⟩] =
        Part.some ⟨arr, T.listMapStepOf f⟩ ∧
      T.model.op 36 [⟨obj, T.domOf f⟩, ⟨arr, T.nilOf (T.codOf f)⟩, ⟨arr, T.listMapStepOf f⟩] =
        Part.some ⟨arr, T.listMapOf f⟩ :=
  ⟨T.op_compOf _, T.op_listRecOf _ _ _⟩

/-- An axiom of the rose-tree block, by index, is valid in the model. -/
theorem axRose (k : ℕ) (hk : k < roseAxioms.length := by decide) :
    (roseAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, List.getElem_mem hk])

/-- The rose-tree object's structure map is defined. -/
theorem nodeOf_exists : ∃ n, T.model.op 38 [] = Part.some ⟨arr, n⟩ := by
  have h : Valid T.model [] [] ⟨dom node, prod nat (list rose)⟩ := T.axRose 0
  obtain ⟨w, hw, -⟩ := h [] rfl (by simp)
  simp_eval [] at hw
  obtain ⟨l, hl, -⟩ := part_bind_eq_some_iff.mp hw
  obtain ⟨y, hy, -⟩ := part_bind_eq_some_iff.mp hl
  exact T.model.exists_op_eq hy rfl

/-- The rose-tree object's structure map. -/
def nodeOf : T.Ar := T.model.get T.nodeOf_exists

/-- The model's structure map of the rose-tree object. -/
@[simp] theorem op_nodeOf : T.model.op 38 [] = Part.some ⟨arr, T.nodeOf⟩ := T.model.op_eq_get _

/-- The rose-tree object is defined. -/
theorem roseOf_exists : ∃ r, T.model.op 37 [] = Part.some ⟨obj, r⟩ := by
  have h : Valid T.model [] [] ⟨cod node, rose⟩ := T.axRose 1
  obtain ⟨w, -, hw⟩ := h [] rfl (by simp)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The rose-tree object. -/
def roseOf : T.Obj := T.model.get T.roseOf_exists

/-- The model's rose-tree object. -/
@[simp] theorem op_roseOf : T.model.op 37 [] = Part.some ⟨obj, T.roseOf⟩ := T.model.op_eq_get _

/-- The domain of the rose-tree object's structure map. -/
theorem domOf_nodeOf : T.domOf T.nodeOf = T.prodOf T.natOf (T.listOf T.roseOf) := by
  have h : Valid T.model [] [] ⟨dom node, prod nat (list rose)⟩ := T.axRose 0
  exact T.val_inj <| T.holds_eq (h [] rfl (by simp)) (by simp_eval [op_nodeOf, op_domOf])
    (by simp_eval [op_natOf, op_roseOf, op_listOf, op_prodOf])

/-- The codomain of the rose-tree object's structure map. -/
theorem codOf_nodeOf : T.codOf T.nodeOf = T.roseOf := by
  have h : Valid T.model [] [] ⟨cod node, rose⟩ := T.axRose 1
  exact T.val_inj <| T.holds_eq (h [] rfl (by simp)) (by simp_eval [op_nodeOf, op_codOf])
    (by simp_eval [op_roseOf])

/-- An algebra of the rose-tree functor has a fold. -/
theorem roseRecOf_exists {f : T.Ar} (h : T.domOf f = T.prodOf T.natOf (T.listOf (T.codOf f))) :
    ∃ r, T.model.op 39 [⟨arr, f⟩] = Part.some ⟨arr, r⟩ := by
  have hv : Valid T.model [arr] [⟨dom (x 0), prod nat (list (cod (x 0)))⟩]
      (dfd (roseRec (x 0))) := T.axRose 3
  obtain ⟨w, hw, -⟩ := hv [⟨arr, f⟩] rfl (by
    simp only [List.mem_singleton, forall_eq]
    exact ⟨⟨obj, T.prodOf T.natOf (T.listOf (T.codOf f))⟩, by simp_eval [op_domOf, h],
      by simp_eval [op_natOf, op_codOf, op_listOf, op_prodOf]⟩)
  simp_eval [] at hw
  exact T.model.exists_op_eq hw rfl

/-- The fold of the rose-tree object into an algebra. -/
def roseRecOf (f : T.Ar) (h : T.domOf f = T.prodOf T.natOf (T.listOf (T.codOf f))) : T.Ar :=
  T.model.get (T.roseRecOf_exists h)

/-- The model's fold of the rose-tree object. -/
@[simp] theorem op_roseRecOf {f : T.Ar}
    (h : T.domOf f = T.prodOf T.natOf (T.listOf (T.codOf f))) :
    T.model.op 39 [⟨arr, f⟩] = Part.some ⟨arr, T.roseRecOf f h⟩ :=
  T.model.op_eq_get _

/-- A fold of the rose-tree object is defined at its algebra. -/
theorem holds_roseRecOf {f : T.Ar} (h : T.domOf f = T.prodOf T.natOf (T.listOf (T.codOf f))) :
    (dfd (roseRec (x 0))).Holds T.model [⟨arr, f⟩] :=
  ⟨⟨arr, T.roseRecOf f h⟩, by simp_eval [T.op_roseRecOf h], by simp_eval [T.op_roseRecOf h]⟩

/-- The domain of a fold is the rose-tree object. -/
theorem domOf_roseRecOf {f : T.Ar} (h : T.domOf f = T.prodOf T.natOf (T.listOf (T.codOf f))) :
    T.domOf (T.roseRecOf f h) = T.roseOf := by
  have hv : Valid T.model [arr] [dfd (roseRec (x 0))] ⟨dom (roseRec (x 0)), rose⟩ :=
    T.axRose 4
  have hq := hv [⟨arr, f⟩] rfl (by simpa using T.holds_roseRecOf h)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_roseRecOf h, op_domOf])
    (by simp_eval [op_roseOf])

/-- The codomain of a fold is its algebra's carrier. -/
theorem codOf_roseRecOf {f : T.Ar} (h : T.domOf f = T.prodOf T.natOf (T.listOf (T.codOf f))) :
    T.codOf (T.roseRecOf f h) = T.codOf f := by
  have hv : Valid T.model [arr] [dfd (roseRec (x 0))] ⟨cod (roseRec (x 0)), cod (x 0)⟩ :=
    T.axRose 5
  have hq := hv [⟨arr, f⟩] rfl (by simpa using T.holds_roseRecOf h)
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_roseRecOf h, op_codOf])
    (by simp_eval [op_codOf])

/-- The algebra composes with the product of the natural numbers object and the list
functor's action at a morphism into its carrier. -/
theorem codOf_prodMapRightOf_listMapOf {f u : T.Ar}
    (h : T.domOf f = T.prodOf T.natOf (T.listOf (T.codOf f))) (hu : T.codOf u = T.codOf f) :
    T.codOf (T.prodMapRightOf T.natOf (T.listMapOf u)) = T.domOf f := by
  rw [codOf_prodMapRightOf, codOf_listMapOf, hu, h]

/-- A fold after the structure map is the algebra after the fold of the children. -/
theorem roseRecOf_nodeOf {f : T.Ar} (h : T.domOf f = T.prodOf T.natOf (T.listOf (T.codOf f))) :
    T.compOf (T.roseRecOf f h) T.nodeOf (T.codOf_nodeOf.trans (T.domOf_roseRecOf h).symm) =
      T.compOf f (T.prodMapRightOf T.natOf (T.listMapOf (T.roseRecOf f h)))
        (T.codOf_prodMapRightOf_listMapOf h (T.codOf_roseRecOf h)) := by
  have hv : Valid T.model [arr] [dfd (roseRec (x 0))]
      ⟨comp (roseRec (x 0)) node, comp (x 0) (prodMapRight nat (listMap (roseRec (x 0))))⟩ :=
    T.axRose 6
  have hq := hv [⟨arr, f⟩] rfl (by simpa using T.holds_roseRecOf h)
  have h1 := T.op_compOf (T.codOf_nodeOf.trans (T.domOf_roseRecOf h).symm)
  have h2 := T.op_compOf (T.codOf_prodMapRightOf_listMapOf h (T.codOf_roseRecOf h))
  obtain ⟨p1, p2⟩ := T.op_prodMapLeft_parts (T.roseRecOf f h) (T.listOf (T.codOf (T.roseRecOf f h)))
  obtain ⟨p3, p4⟩ := T.op_listMap_parts (T.roseRecOf f h)
  obtain ⟨p5, p6⟩ := T.op_prodMapRight_parts T.natOf (T.listMapOf (T.roseRecOf f h))
  exact T.val_inj <| T.holds_eq hq (by simp_eval [T.op_roseRecOf h, op_nodeOf, h1])
    (by simp_eval [T.op_roseRecOf h, op_natOf, op_domOf, op_codOf, op_nilOf, op_consOf,
      op_listOf, op_fstOf, op_sndOf, p1, p2, p3, p4, p5, p6, h2])

/-- A morphism from the rose-tree object satisfying the fold's equation is the fold. -/
theorem eq_roseRecOf {f u : T.Ar} (h : T.domOf f = T.prodOf T.natOf (T.listOf (T.codOf f)))
    (hu : T.domOf u = T.roseOf) (huc : T.codOf u = T.codOf f)
    (hu1 : T.compOf u T.nodeOf (T.codOf_nodeOf.trans hu.symm) =
      T.compOf f (T.prodMapRightOf T.natOf (T.listMapOf u))
        (T.codOf_prodMapRightOf_listMapOf h huc)) :
    u = T.roseRecOf f h := by
  have hv : Valid T.model [arr, arr]
      [dfd (roseRec (x 0)), ⟨dom (x 1), rose⟩,
        ⟨comp (x 1) node, comp (x 0) (prodMapRight nat (listMap (x 1)))⟩]
      ⟨x 1, roseRec (x 0)⟩ := T.axRose 7
  obtain ⟨p1, p2⟩ := T.op_prodMapLeft_parts u (T.listOf (T.codOf u))
  obtain ⟨p3, p4⟩ := T.op_listMap_parts u
  obtain ⟨p5, p6⟩ := T.op_prodMapRight_parts T.natOf (T.listMapOf u)
  have hq := hv [⟨arr, f⟩, ⟨arr, u⟩] rfl (by
    simp only [List.mem_cons, forall_eq_or_imp, forall_eq, List.not_mem_nil, or_false]
    exact ⟨⟨⟨arr, T.roseRecOf f h⟩, by simp_eval [T.op_roseRecOf h],
        by simp_eval [T.op_roseRecOf h]⟩,
      ⟨⟨obj, T.roseOf⟩, by simp_eval [op_domOf, hu], by simp_eval [op_roseOf]⟩,
      ⟨⟨arr, T.compOf f (T.prodMapRightOf T.natOf (T.listMapOf u))
          (T.codOf_prodMapRightOf_listMapOf h huc)⟩,
        by simp_eval [op_nodeOf, T.op_compOf (T.codOf_nodeOf.trans hu.symm), hu1],
        by simp_eval [op_natOf, op_domOf, op_codOf, op_nilOf, op_consOf, op_listOf, op_fstOf,
          op_sndOf, p1, p2, p3, p4, p5, p6, T.op_compOf (T.codOf_prodMapRightOf_listMapOf h huc)]⟩⟩)
  exact T.val_inj <| T.holds_eq hq (by simp_eval []) (by simp_eval [T.op_roseRecOf h])

end ToposModel

end Geb.FreeTopos

end
