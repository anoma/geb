/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeLCCC.Syntax
public import Mathlib.CategoryTheory.Functor.Basic

set_option doc.verso true in
/-!
# The category underlying a model

A model of the partial Horn theory has objects and arrows as its two sorts. Reading the
category operations gives a category whose hom types enforce source and target. In particular,
the closed term model gives a small category.

## Main definitions

* {lit}`LCCCModel` — a model with its proof of the axioms.
* {lit}`LCCCModel.Cat` — its category of objects and typed morphisms.
* {lit}`syntacticModel` — the model of closed syntax.
* {lit}`objOfTerm`, {lit}`homOfTerm` — objects and morphisms from typed closed terms.
* {lit}`LCCCModel.interpretation` — the interpretation functor into a model.

## Tags

syntactic category, locally cartesian closed category, partial Horn logic
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeLCCC

open PartialHorn FreeTopos.Sorts
open FreeTopos (categoryAxioms)

universe u v

/-- A model of the categorical theory with chosen structure. -/
@[ext] structure LCCCModel : Type (v + 1) where
  /-- The model. -/
  model : PartialHorn.Model.{v} sig
  /-- The model satisfies the axioms. -/
  isModel : IsModel theory model

namespace LCCCModel

variable (T : LCCCModel.{v})

/-- The objects of a model. -/
abbrev Obj : Type v := T.model.Car obj

/-- The arrows of a model. -/
abbrev Ar : Type v := T.model.Car arr

/-- An axiom of the category block, by index, is valid in the model. -/
theorem axCategory (k : ℕ) (hk : k < categoryAxioms.length := by decide) :
    (categoryAxioms[k]).Valid T.model :=
  T.isModel _ (by simp [theory, axioms, finiteAxioms, List.getElem_mem hk])

/-- The simplification of a term's value at explicit values, with the given lemmas, at a
location or the goal: the terms' builders unfold, and the value of each operation's application
is the operation at its arguments' values. -/
local macro "simp_eval" " [" ls:Lean.Parser.Tactic.simpLemma,* "]"
    loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp only [x, dfd, dom, cod, idt, comp,
    eval_op, eval_var, List.mapM_cons, List.mapM_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Part.coe_some,
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

open CategoryTheory

/-- The objects of a model, carrying the model's category. -/
def Cat : Type v := T.Obj

/-- The category laws are the interpreted axioms of the category block. -/
instance : Category T.Cat where
  Hom a b := {f : T.Ar // T.domOf f = a ∧ T.codOf f = b}
  id a := ⟨T.idOf a, T.domOf_idOf a, T.codOf_idOf a⟩
  comp f g := ⟨T.compOf g.1 f.1 (f.2.2.trans g.2.1.symm),
    (T.domOf_compOf _).trans f.2.1, (T.codOf_compOf _).trans g.2.2⟩
  id_comp f := by
    obtain ⟨f, rfl, rfl⟩ := f
    exact Subtype.ext (T.compOf_idOf f)
  comp_id f := by
    obtain ⟨f, rfl, rfl⟩ := f
    exact Subtype.ext (T.idOf_compOf f)
  assoc f g h := by
    obtain ⟨f, rfl, rfl⟩ := f
    obtain ⟨g, hg, rfl⟩ := g
    obtain ⟨h, hh, rfl⟩ := h
    exact Subtype.ext (T.compOf_assoc hg.symm hh.symm)

end LCCCModel

/-- The model consisting of closed syntax modulo the categorical equations. -/
abbrev syntacticModel : LCCCModel.{0} := ⟨model, isModel⟩

namespace LCCCModel

open CategoryTheory

variable {A : LCCCModel.{v}} {B : LCCCModel.{u}}

/-- A model homomorphism preserves sources. -/
theorem map_dom (F : ModelHom A.model B.model) (f : A.Ar) :
    B.domOf (F.app FreeTopos.Sorts.arr f) = F.app FreeTopos.Sorts.obj (A.domOf f) := by
  have h := F.map_op 0 _ _ (A.op_domOf f)
  simp only [List.map_cons, List.map_nil, ModelHom.toFun_mk] at h
  exact B.val_inj (Part.some_inj.mp ((B.op_domOf _).symm.trans h))

/-- A model homomorphism preserves targets. -/
theorem map_cod (F : ModelHom A.model B.model) (f : A.Ar) :
    B.codOf (F.app FreeTopos.Sorts.arr f) = F.app FreeTopos.Sorts.obj (A.codOf f) := by
  have h := F.map_op 1 _ _ (A.op_codOf f)
  simp only [List.map_cons, List.map_nil, ModelHom.toFun_mk] at h
  exact B.val_inj (Part.some_inj.mp ((B.op_codOf _).symm.trans h))

/-- A homomorphism of models gives a functor between their underlying categories. -/
def toFunctor (F : ModelHom A.model B.model) : A.Cat ⥤ B.Cat where
  obj := F.app obj
  map f := ⟨F.app arr f.1,
    (map_dom F f.1).trans (congrArg (F.app obj) f.2.1),
    (map_cod F f.1).trans (congrArg (F.app obj) f.2.2)⟩
  map_id a := by
    apply Subtype.ext
    have h := F.map_op 2 _ _ (A.op_idOf a)
    simp only [List.map_cons, List.map_nil] at h
    rw [F.toFun_mk obj a, F.toFun_mk arr (A.idOf a)] at h
    exact B.val_inj (Part.some_inj.mp (h.symm.trans (B.op_idOf _)))
  map_comp f g := by
    apply Subtype.ext
    have h := F.map_op 3 _ _ (A.op_compOf (f.2.2.trans g.2.1.symm))
    simp only [List.map_cons, List.map_nil, ModelHom.toFun_mk] at h
    have hh := (map_cod F f.1).trans
      ((congrArg (F.app obj) (f.2.2.trans g.2.1.symm)).trans (map_dom F g.1).symm)
    exact B.val_inj (Part.some_inj.mp (h.symm.trans (B.op_compOf hh)))

/-- The canonical interpretation of the syntactic category in a model. -/
def interpretation (T : LCCCModel.{v}) : syntacticModel.Cat ⥤ T.Cat :=
  toFunctor (TermModel.interpretHom (T := theory) T.model T.isModel)

end LCCCModel

/-- A derivably defined closed object, as an object of the syntactic category. -/
def objOfTerm (a : Tree) (ha : sortOf sig [] a = some obj)
    (da : Derives [] [] (dfd a)) : syntacticModel.Cat := ofTerm a ha da

/-- A derivably typed closed arrow, as a morphism of the syntactic category. -/
def homOfTerm {a b f : Tree} (ha : sortOf sig [] a = some obj)
    (hb : sortOf sig [] b = some obj) (hf : sortOf sig [] f = some arr)
    (da : Derives [] [] (dfd a)) (db : Derives [] [] (dfd b))
    (df : Derives [] [] (dfd f)) (hs : Derives [] [] ⟨dom f, a⟩)
    (ht : Derives [] [] ⟨cod f, b⟩) :
    objOfTerm a ha da ⟶ objOfTerm b hb db := by
  refine ⟨ofTerm f hf df, ?_, ?_⟩
  · apply syntacticModel.val_inj
    apply syntacticModel.holds_eq (ρ := []) (q := ⟨dom f, a⟩)
      (TermModel.holds_closed (T := theory) model isModel hs) _ (eval_ofTerm a ha da)
    simp only [dom, eval_op, List.mapM_cons, List.mapM_nil, eval_ofTerm f hf df,
      Part.bind_some, Part.pure_eq_some, Part.bind_eq_bind]
    exact syntacticModel.op_domOf _
  · apply syntacticModel.val_inj
    apply syntacticModel.holds_eq (ρ := []) (q := ⟨cod f, b⟩)
      (TermModel.holds_closed (T := theory) model isModel ht) _ (eval_ofTerm b hb db)
    simp only [cod, eval_op, List.mapM_cons, List.mapM_nil, eval_ofTerm f hf df,
      Part.bind_some, Part.pure_eq_some, Part.bind_eq_bind]
    exact syntacticModel.op_codOf _

end Geb.FreeLCCC

end
