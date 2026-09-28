/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.PartialHorn.Development

set_option doc.verso true in
/-!
# Definitional extensions of a partial Horn theory

A definition names a term: a new operation whose arguments are the variables of a context and
whose value is a body, a term of the signature in those variables of the definition's sort. The
extension of a theory by a definition adds the operation to the signature and two axioms:
the operation is defined where its body is and equal to it there, and defined only there. Its
unfolding replaces each application of the operation by the body, the unfolded arguments
substituted for the variables; it is the morphism of free monads from the terms of the extended
signature to those of the signature that sends the new operation to its body.

Every argument of a definition occurs in its body. The operations of a partial Horn theory are
strict, an application defined only where its arguments are; the unfolding of an application
keeps that condition when each argument occurs in the body, which is defined only where the
terms substituted for its variables are.

The criteria for a definition \[Suppes1957\] hold of the models. A model of the theory
extends to a model of the extension, the new operation read as the body's value
({lit}`Model.expand`, {lit}`isModel_expand`). The value of a well-sorted term in the extended
model is the value of its unfolding in the model ({lit}`eval_expand_unfold`), which is
eliminability; the value of a term of the signature is unchanged
({lit}`eval_expand_of_opsBelow`), so a sequent of the signature valid in every model of the
extension is valid in every model of the theory, which is non-creativity
({lit}`valid_of_valid_extendAll`). A sequent valid in every model of the extension has its
unfolding valid in every model of the theory ({lit}`valid_unfold_of_valid_expand`). Definitions
iterate, each over the signature the earlier ones extend ({lit}`Theory.extendAll`,
{lit}`valid_unfoldAll`). A development checked in the extension therefore needs no unfolding
of its certificates: its sequents' unfoldings hold in every model of the theory
({lit}`checkDevelopment_extendAll_sound`).

## Main definitions

* {lit}`Defn` — a definition: its context, its sort and its body.
* {lit}`Theory.extend`, {lit}`Theory.extendAll` — the extension by a definition, and by a list
  of definitions in order.
* {lit}`unfoldOp`, {lit}`unfoldAll` — the unfolding of a definition, and of a list of them.
* {lit}`Model.expand` — the model of the extension that reads the new operation as its body.

## Main statements

* {lit}`isModel_expand` — a model of the theory expands to a model of the extension.
* {lit}`eval_expand_unfold` — the value of a term in the expansion is its unfolding's value.
* {lit}`valid_unfold_of_valid_expand` — validity in the expansion transfers to the unfolding.
* {lit}`valid_unfoldAll` — a sequent valid in every model of an iterated extension has its
  unfolding valid in every model of the theory.
* {lit}`valid_of_valid_extendAll` — non-creativity.
* {lit}`checkDevelopment_extendAll_sound` — a development checked in an iterated extension is
  sound for the theory's models.

## References

* \[Suppes1957\], pp. 153–154, for the criteria of eliminability and non-creativity.
* \[PalmgrenVickers2007\], Section 3, for models of partial Horn theories.

## Tags

definition, definitional extension, partial Horn logic, unfolding, eliminability,
non-creativity
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PartialHorn

open scoped FinEnum

universe v

/-- A definition of an operation: the sorts of its arguments, the sort of its value, and its
body, a term in the arguments. -/
@[ext] structure Defn where
  /-- The sorts of the arguments, the variables of the body. -/
  ctx : List ℕ
  /-- The sort of the value. -/
  sort : ℕ
  /-- The body. -/
  body : Tree
deriving DecidableEq

/-- Whether the variable of index {lit}`i` occurs in a term. -/
def Occurs (i : ℕ) : Tree → Bool :=
  RoseTree.para fun l cs ↦ match l, cs with
    | 0, [(j, _)] => j.children.isEmpty && j.label == i
    | 0, _ => false
    | _ + 1, cs => cs.any Prod.snd

/-- Whether every operation of a term has an index below {lit}`n`. -/
def OpsBelow (n : ℕ) : Tree → Bool :=
  RoseTree.para fun l cs ↦ match l with
    | 0 => true
    | k + 1 => decide (k < n) && cs.all Prod.snd

/-- A definition is well formed over a signature: its body has the definition's sort in its
context, and every argument occurs in the body. -/
structure Defn.WF (S : Sig) (d : Defn) : Prop where
  /-- The body has the definition's sort in its context. -/
  sort : sortOf S d.ctx d.body = some d.sort
  /-- Every argument occurs in the body. -/
  occurs : ∀ i < d.ctx.length, Occurs i d.body = true

/-- The signature extended by a definition's operation, whose index is the signature's
length. -/
def Sig.extend (S : Sig) (d : Defn) : Sig := S ++ [(d.ctx, d.sort)]

/-- The application of the operation of index {lit}`n` to the first {lit}`m` variables. -/
def opVars (n m : ℕ) : Tree := op n ((List.range m).map var)

/-- The axioms of a definition as the operation of index {lit}`n`: the operation is defined
where the body is and equal to it there, and defined only where the body is. -/
def Defn.axioms (n : ℕ) (d : Defn) : List Seq :=
  [⟨d.ctx, [⟨d.body, d.body⟩], ⟨opVars n d.ctx.length, d.body⟩⟩,
    ⟨d.ctx, [⟨opVars n d.ctx.length, opVars n d.ctx.length⟩], ⟨d.body, d.body⟩⟩]

/-- The extension of a theory by a definition. -/
def Theory.extend (T : Theory) (d : Defn) : Theory :=
  ⟨T.sig.extend d, T.axioms ++ d.axioms T.sig.length⟩

/-- The unfolding of the operation of index {lit}`n`, defined by the body {lit}`b`: each
application is replaced by the body, with the unfolded arguments substituted for its variables.
-/
def unfoldOp (n : ℕ) (b : Tree) : Tree → Tree :=
  RoseTree.para fun l cs ↦ match l with
    | 0 => RoseTree.node 0 (cs.map Prod.fst)
    | k + 1 => if k = n then subst (cs.map Prod.snd) b else RoseTree.node (k + 1) (cs.map Prod.snd)

/-- The unfolding of both sides of an equation. -/
def Eqn.unfoldOp (n : ℕ) (b : Tree) (q : Eqn) : Eqn :=
  ⟨PartialHorn.unfoldOp n b q.lhs, PartialHorn.unfoldOp n b q.rhs⟩

/-- The unfolding of a sequent's equations. -/
def Seq.unfoldOp (n : ℕ) (b : Tree) (a : Seq) : Seq :=
  ⟨a.ctx, a.hyps.map (Eqn.unfoldOp n b), a.concl.unfoldOp n b⟩

variable {S : Sig} {d : Defn}

/-- The operations of the signature keep their sorts in the extension. -/
theorem getElem?_extend_of_lt {k : ℕ} (hk : k < S.length) : (S.extend d)[k]? = S[k]? :=
  List.getElem?_append_left hk

/-- The new operation of the extension has the definition's sorts. -/
theorem getElem?_extend_self : (S.extend d)[S.length]? = some (d.ctx, d.sort) := by
  simp [Sig.extend]

/-- The model of the extension that reads the new operation as the value of the body, at
arguments of the definition's sorts. It is reducible, so that its values are the model's. -/
abbrev Model.expand (M : Model.{v} S) (d : Defn) (hd : sortOf S d.ctx d.body = some d.sort) :
    Model.{v} (S.extend d) where
  Car := M.Car
  op k args := if k < S.length then M.op k args
    else if k = S.length ∧ args.map Sigma.fst = d.ctx then eval M args d.body else Part.none
  op_sort {k args w} h := by
    by_cases hk : k < S.length
    · rw [if_pos hk] at h
      rw [getElem?_extend_of_lt hk]
      exact M.op_sort h
    · rw [if_neg hk] at h
      by_cases he : k = S.length ∧ args.map Sigma.fst = d.ctx
      · rw [if_pos he] at h
        rw [he.1, getElem?_extend_self]
        simp only [Option.map_some, Option.some.injEq]
        exact (sort_eval he.2 d.body hd (Part.eq_some_iff.mpr h)).symm
      · rw [if_neg he] at h
        exact absurd h (Part.notMem_none w)

/-- An operation of the extension other than the new one is an operation of the signature. -/
theorem lt_of_getElem?_extend {k : ℕ} {o : List ℕ × ℕ} (ho : (S.extend d)[k]? = some o)
    (hk : ¬k = S.length) : k < S.length := by
  have h : k < (S.extend d).length := (List.getElem?_eq_some_iff.mp ho).1
  simp only [Sig.extend, List.length_append, List.length_singleton] at h
  omega

/-- A node of label zero over one child is an occurrence of a variable exactly when the child is
the leaf of its index. -/
theorem occurs_node_zero_iff (i : ℕ) (j : Tree) :
    Occurs i (RoseTree.node 0 [j]) = true ↔ j.children = [] ∧ j.label = i := by
  simp [Occurs]

/-- An application's occurrences are its arguments'. -/
theorem occurs_node_succ (i k : ℕ) (cs : List Tree) :
    Occurs i (RoseTree.node (k + 1) cs) = cs.any (Occurs i) := by
  simp [Occurs, List.any_map]
  rfl

/-- An application's operations are below {lit}`n` when its own is and its arguments' are. -/
theorem opsBelow_node_succ (n k : ℕ) (cs : List Tree) :
    OpsBelow n (RoseTree.node (k + 1) cs) = (decide (k < n) && cs.all (OpsBelow n)) := by
  simp [OpsBelow, List.all_map]
  rfl

/-- The unfolding keeps a variable's node. -/
theorem unfoldOp_node_zero (n : ℕ) (b : Tree) (cs : List Tree) :
    unfoldOp n b (RoseTree.node 0 cs) = RoseTree.node 0 cs := by
  simp [unfoldOp, Function.comp_def]

/-- The unfolding at an application. -/
theorem unfoldOp_node_succ (n : ℕ) (b : Tree) (k : ℕ) (cs : List Tree) :
    unfoldOp n b (RoseTree.node (k + 1) cs) =
      if k = n then subst (cs.map (unfoldOp n b)) b
      else RoseTree.node (k + 1) (cs.map (unfoldOp n b)) := by
  simp only [unfoldOp, RoseTree.para_node, List.map_map]
  rfl

/-- A term of a signature has its operations below the signature's length. -/
theorem opsBelow_of_sortOf {Γ : List ℕ} :
    ∀ t : Tree, ∀ {s : ℕ}, sortOf S Γ t = some s → OpsBelow S.length t = true :=
  RoseTree.ind fun l cs ih s hs ↦ by
    rcases l with _ | k
    · simp [OpsBelow]
    · rw [sortOf_node_succ, Option.bind_eq_some_iff] at hs
      obtain ⟨o, ho, hs⟩ := hs
      split at hs
      · rename_i hcs
        rw [opsBelow_node_succ, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
        refine ⟨(List.getElem?_eq_some_iff.mp ho).1, fun c hc ↦ ?_⟩
        have hm : sortOf S Γ c ∈ o.1.map some := hcs ▸ List.mem_map_of_mem hc
        obtain ⟨s', -, hs'⟩ := List.mem_map.mp hm
        exact ih c hc hs'.symm
      · exact absurd hs (by simp)

variable {M : Model.{v} S}

/-- The value of a term of the signature is the same in the expansion. -/
theorem eval_expand_of_opsBelow (hd : sortOf S d.ctx d.body = some d.sort) (ρ : List M.Val) :
    ∀ t, OpsBelow S.length t = true → eval (M.expand d hd) ρ t = eval M ρ t :=
  RoseTree.ind fun l cs ih ht ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · simp [eval]
      · rcases hc : i.children with _ | ⟨e, es⟩
        · rw [eval_node_zero hc, eval_node_zero hc]
        · rw [eval_node_zero_of_not (by simp [hc]), eval_node_zero_of_not (by simp [hc])]
      · simp [eval]
    · rw [opsBelow_node_succ, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht
      rw [eval_node_succ, eval_node_succ, mapM_congr fun c hc ↦ ih c hc (ht.2 c hc)]
      congr 1
      funext args
      simp [Model.expand, ht.1]

/-- The variables of a context evaluate to the assignment. -/
theorem mapM_vars (ρ : List M.Val) :
    ((List.range ρ.length).map var).mapM (eval M ρ) = Part.some ρ := by
  rw [mapM_part_eq_some_iff]
  refine List.ext_getElem (by simp) fun i h₁ h₂ ↦ ?_
  simp only [List.length_map, List.length_range] at h₁
  simp [h₁, Part.coe_some]

/-- The new operation applied to the variables has the body's value, at an assignment of the
definition's context. -/
theorem eval_expand_opVars (hd : sortOf S d.ctx d.body = some d.sort) {ρ : List M.Val}
    (hρ : ρ.map Sigma.fst = d.ctx) :
    eval (M.expand d hd) ρ (opVars S.length d.ctx.length) = eval M ρ d.body := by
  have hl : d.ctx.length = ρ.length := by simpa using (congrArg List.length hρ).symm
  rw [opVars, eval_op, hl, mapM_vars (M := M.expand d hd), Part.bind_some]
  simp [Model.expand, hρ]

/-- A model of a theory expands to a model of its extension by a well-formed definition, when
the theory's axioms are of its signature. -/
theorem isModel_expand {T : Theory} {M : Model.{v} T.sig} (hM : IsModel T M)
    (hT : ∀ a ∈ T.axioms, ∀ q ∈ a.concl :: a.hyps,
      OpsBelow T.sig.length q.lhs = true ∧ OpsBelow T.sig.length q.rhs = true)
    (hd : d.WF T.sig) : IsModel (T.extend d) (M.expand d hd.sort) := by
  have hb := opsBelow_of_sortOf d.body hd.sort
  have holds : ∀ (ρ : List M.Val) (q : Eqn), OpsBelow T.sig.length q.lhs = true →
      OpsBelow T.sig.length q.rhs = true →
      (q.Holds (M.expand d hd.sort) ρ ↔ q.Holds M ρ) := fun ρ q hl hr ↦ by
    unfold Eqn.Holds
    rw [eval_expand_of_opsBelow hd.sort ρ _ hl, eval_expand_of_opsBelow hd.sort ρ _ hr]
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · intro ρ hρ hH
    have hq := hT a ha
    refine (holds ρ _ (hq _ List.mem_cons_self).1 (hq _ List.mem_cons_self).2).mpr
      (hM a ha ρ hρ fun h hh ↦ ?_)
    exact (holds ρ h (hq h (List.mem_cons_of_mem _ hh)).1
      (hq h (List.mem_cons_of_mem _ hh)).2).mp (hH h hh)
  · simp only [Defn.axioms, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    · intro ρ hρ hH
      obtain ⟨w, hw, -⟩ := hH _ List.mem_cons_self
      change eval (M.expand d hd.sort) ρ d.body = Part.some w at hw
      rw [eval_expand_of_opsBelow hd.sort ρ _ hb] at hw
      exact ⟨w, (eval_expand_opVars hd.sort hρ).trans hw,
        (eval_expand_of_opsBelow hd.sort ρ _ hb).trans hw⟩
    · intro ρ hρ hH
      obtain ⟨w, hw, -⟩ := hH _ List.mem_cons_self
      change eval (M.expand d hd.sort) ρ (opVars T.sig.length d.ctx.length) = Part.some w at hw
      rw [eval_expand_opVars hd.sort hρ] at hw
      exact ⟨w, (eval_expand_of_opsBelow hd.sort ρ _ hb).trans hw,
        (eval_expand_of_opsBelow hd.sort ρ _ hb).trans hw⟩

/-- A substitution instance that is defined has defined each substituted term whose variable
occurs in it. -/
theorem exists_eval_of_occurs {ρ : List M.Val} {us : List Tree} {j : ℕ} (hj : j < us.length) :
    ∀ b : Tree, Occurs j b = true → ∀ {w : M.Val}, eval M ρ (subst us b) = Part.some w →
      ∃ v, eval M ρ us[j] = Part.some v :=
  RoseTree.ind fun l cs ih hb w hw ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨i', cs⟩⟩
      · simp [Occurs] at hb
      · obtain ⟨hc, hb⟩ := (occurs_node_zero_iff _ _).mp hb
        rw [subst_node_zero _ hc, hb, List.getElem?_eq_getElem hj, Option.getD_some] at hw
        exact ⟨w, hw⟩
      · simp [Occurs] at hb
    · rw [occurs_node_succ, List.any_eq_true] at hb
      obtain ⟨c, hc, hoc⟩ := hb
      rw [subst_node_succ, eval_node_succ, part_bind_eq_some_iff] at hw
      obtain ⟨args, hargs, -⟩ := hw
      rw [mapM_part_eq_some_iff, List.map_map] at hargs
      have hm : eval M ρ (subst us c) ∈ args.map Part.some :=
        hargs ▸ List.mem_map_of_mem (f := eval M ρ ∘ subst us) hc
      obtain ⟨v, -, hv⟩ := List.mem_map.mp hm
      exact ih c hc hoc hv.symm

/-- A substitution instance has the sort of the term, when the substituted terms have the sorts
of its variables. -/
theorem sortOf_subst {Γ Δ : List ℕ} {us : List Tree}
    (hus : us.map (sortOf S Γ) = Δ.map some) :
    ∀ b : Tree, ∀ {s : ℕ}, sortOf S Δ b = some s → sortOf S Γ (subst us b) = some s :=
  RoseTree.ind fun l cs ih s hs ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨i', cs⟩⟩
      · simp [sortOf] at hs
      · obtain ⟨hc, hs⟩ := sortOf_node_zero_eq_some.mp hs
        have hi : i.label < Δ.length := (List.getElem?_eq_some_iff.mp hs).1
        have hlen : us.length = Δ.length := by simpa using congrArg List.length hus
        have e := congrArg (fun l ↦ l[i.label]?) hus
        simp only [List.getElem?_map, List.getElem?_eq_getElem (hlen ▸ hi),
          List.getElem?_eq_getElem hi, Option.map_some, Option.some.injEq] at e
        rw [List.getElem?_eq_getElem hi] at hs
        rw [subst_node_zero _ hc, List.getElem?_eq_getElem (hlen ▸ hi), Option.getD_some, e, hs]
      · simp [sortOf] at hs
    · rw [sortOf_node_succ, Option.bind_eq_some_iff] at hs
      obtain ⟨o, ho, hs⟩ := hs
      split at hs
      · rename_i hcs
        rw [subst_node_succ, sortOf_node_succ, ho, Option.bind_some, List.map_map]
        have hc : cs.map (sortOf S Γ ∘ subst us) = cs.map (sortOf S Δ) := by
          refine List.map_congr_left fun c hc ↦ ?_
          have hm : sortOf S Δ c ∈ o.1.map some := hcs ▸ List.mem_map_of_mem hc
          obtain ⟨s', -, hs'⟩ := List.mem_map.mp hm
          exact (ih c hc hs'.symm).trans hs'
        rw [hc, if_pos hcs]
        exact hs
      · exact absurd hs (by simp)

/-- A term with a sort in a context has its variables in the context. -/
theorem scoped_of_sortOf {Γ : List ℕ} :
    ∀ t : Tree, ∀ {s : ℕ}, sortOf S Γ t = some s → Scoped Γ.length t = true :=
  RoseTree.ind fun l cs ih s hs ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨i', cs⟩⟩
      · simp [sortOf] at hs
      · obtain ⟨hc, hs⟩ := sortOf_node_zero_eq_some.mp hs
        exact scoped_node_zero_iff.mpr ⟨hc, (List.getElem?_eq_some_iff.mp hs).1⟩
      · simp [sortOf] at hs
    · rw [sortOf_node_succ, Option.bind_eq_some_iff] at hs
      obtain ⟨o, -, hs⟩ := hs
      split at hs
      · rename_i hcs
        rw [scoped_node_succ, List.all_eq_true]
        intro c hc
        have hm : sortOf S Γ c ∈ o.1.map some := hcs ▸ List.mem_map_of_mem hc
        obtain ⟨s', -, hs'⟩ := List.mem_map.mp hm
        exact ih c hc hs'.symm
      · exact absurd hs (by simp)

/-- The values of terms with sorts in a context, at an assignment of the context, have those
sorts. -/
theorem map_fst_of_eval {S' : Sig} {N : Model.{v} S'} {ρ : List N.Val} {Γ Δ : List ℕ}
    (hρ : ρ.map Sigma.fst = Γ) {cs : List Tree} {args : List N.Val}
    (hv : cs.map (eval N ρ) = args.map Part.some) (hs : cs.map (sortOf S' Γ) = Δ.map some) :
    args.map Sigma.fst = Δ := by
  have h₁ : cs.length = args.length := by simpa using congrArg List.length hv
  have h₂ : cs.length = Δ.length := by simpa using congrArg List.length hs
  refine List.ext_getElem (by simp [← h₁, h₂]) fun i hi₁ hi₂ ↦ ?_
  have hi : i < cs.length := by simpa [h₁] using hi₁
  have e₁ := congrArg (fun l ↦ l[i]?) hv
  have e₂ := congrArg (fun l ↦ l[i]?) hs
  simp only [List.getElem?_map, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem (h₁ ▸ hi),
    List.getElem?_eq_getElem hi₂, Option.map_some, Option.some.injEq] at e₁ e₂
  simpa using sort_eval hρ _ e₂ e₁

/-- The value of a well-sorted term in the expansion is the value of its unfolding in the
model, at an assignment of the term's context. -/
theorem eval_expand_unfold (hd : d.WF S) {Γ : List ℕ} {ρ : List M.Val}
    (hρ : ρ.map Sigma.fst = Γ) : ∀ t : Tree, ∀ {s : ℕ}, sortOf (S.extend d) Γ t = some s →
      eval (M.expand d hd.sort) ρ t = eval M ρ (unfoldOp S.length d.body t) :=
  RoseTree.ind fun l cs ih s hs ↦ by
    rcases l with _ | k
    · rw [unfoldOp_node_zero]
      rcases cs with _ | ⟨i, _ | ⟨i', cs⟩⟩
      · simp [eval]
      · rcases hc : i.children with _ | ⟨e, es⟩
        · rw [eval_node_zero hc, eval_node_zero hc]
        · rw [eval_node_zero_of_not (by simp [hc]), eval_node_zero_of_not (by simp [hc])]
      · simp [eval]
    · rw [sortOf_node_succ, Option.bind_eq_some_iff] at hs
      obtain ⟨o, ho, hs⟩ := hs
      split at hs
      · rename_i hcs
        have hsc : ∀ c ∈ cs, ∃ s', sortOf (S.extend d) Γ c = some s' := fun c hc ↦ by
          have hm : sortOf (S.extend d) Γ c ∈ o.1.map some := hcs ▸ List.mem_map_of_mem hc
          obtain ⟨s', -, hs'⟩ := List.mem_map.mp hm
          exact ⟨s', hs'.symm⟩
        have hargs : cs.mapM (eval (M.expand d hd.sort) ρ) =
            (cs.map (unfoldOp S.length d.body)).mapM (eval M ρ) := by
          rw [List.mapM_map]
          exact mapM_congr fun c hc ↦ by
            obtain ⟨s', hs'⟩ := hsc c hc
            exact ih c hc hs'
        rw [unfoldOp_node_succ, eval_node_succ, hargs]
        split
        · rename_i hk
          subst hk
          rw [getElem?_extend_self, Option.some.injEq] at ho
          subst ho
          have hlen : cs.length = d.ctx.length := by simpa using congrArg List.length hcs
          have hsc' : Scoped (cs.map (unfoldOp S.length d.body)).length d.body = true := by
            rw [List.length_map, hlen]
            exact scoped_of_sortOf d.body hd.sort
          have hop : ∀ args : List M.Val, args.map Sigma.fst = d.ctx →
              (M.expand d hd.sort).op S.length args = eval M args d.body := fun args h ↦ by
            simp [Model.expand, h]
          refine Part.ext fun w ↦ ?_
          rw [← Part.eq_some_iff, ← Part.eq_some_iff, part_bind_eq_some_iff]
          constructor
          · rintro ⟨args, hvs, hw⟩
            have hvs' := hvs
            rw [← hargs, mapM_part_eq_some_iff] at hvs'
            rw [hop args (map_fst_of_eval (N := M.expand d hd.sort) hρ hvs' hcs)] at hw
            rw [mapM_part_eq_some_iff] at hvs
            rwa [eval_subst hvs _ hsc']
          · intro hw
            have hdef : ∀ u ∈ cs.map (unfoldOp S.length d.body),
                ∃ v, eval M ρ u = Part.some v := by
              intro u hu
              obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hu
              exact exists_eval_of_occurs hj d.body
                (hd.occurs j (by simpa [hlen] using hj)) hw
            obtain ⟨args, hvs⟩ := exists_map_eq_map_some _ hdef
            have hvs' := (mapM_part_eq_some_iff _ args).mpr hvs
            refine ⟨args, hvs', ?_⟩
            have h₂ := hvs'
            rw [← hargs, mapM_part_eq_some_iff] at h₂
            rw [hop args (map_fst_of_eval (N := M.expand d hd.sort) hρ h₂ hcs),
              ← eval_subst hvs _ hsc']
            exact hw
        · rename_i hk
          have hlt := lt_of_getElem?_extend ho hk
          rw [eval_node_succ]
          congr 1
          funext args
          simp [Model.expand, hlt]
      · exact absurd hs (by simp)

/-- The unfolding of a well-sorted term has its sort in the signature. -/
theorem sortOf_unfold (hd : d.WF S) {Γ : List ℕ} : ∀ t : Tree, ∀ {s : ℕ},
    sortOf (S.extend d) Γ t = some s → sortOf S Γ (unfoldOp S.length d.body t) = some s :=
  RoseTree.ind fun l cs ih s hs ↦ by
    rcases l with _ | k
    · rw [unfoldOp_node_zero]
      rcases cs with _ | ⟨i, _ | ⟨i', cs⟩⟩
      · simp [sortOf] at hs
      · exact sortOf_node_zero_eq_some.mpr (sortOf_node_zero_eq_some.mp hs)
      · simp [sortOf] at hs
    · rw [sortOf_node_succ, Option.bind_eq_some_iff] at hs
      obtain ⟨o, ho, hs⟩ := hs
      split at hs
      · rename_i hcs
        have hc : cs.map (sortOf S Γ ∘ unfoldOp S.length d.body) =
            cs.map (sortOf (S.extend d) Γ) := List.map_congr_left fun c hc ↦ by
          have hm : sortOf (S.extend d) Γ c ∈ o.1.map some := hcs ▸ List.mem_map_of_mem hc
          obtain ⟨s', -, hs'⟩ := List.mem_map.mp hm
          exact (ih c hc hs'.symm).trans hs'
        rw [unfoldOp_node_succ]
        split
        · rename_i hk
          subst hk
          rw [getElem?_extend_self, Option.some.injEq] at ho
          subst ho
          have hus : (cs.map (unfoldOp S.length d.body)).map (sortOf S Γ) = d.ctx.map some := by
            rw [List.map_map, hc]
            exact hcs
          exact (sortOf_subst hus d.body hd.sort).trans hs
        · rename_i hk
          rw [sortOf_node_succ, ← getElem?_extend_of_lt (d := d) (lt_of_getElem?_extend ho hk), ho,
            Option.bind_some, List.map_map, hc, if_pos hcs]
          exact hs
      · exact absurd hs (by simp)

/-- A sequent is well sorted over a signature: each side of its conclusion and of its
hypotheses has a sort in its context. -/
def Seq.WellSorted (S : Sig) (a : Seq) : Prop :=
  ∀ q ∈ a.concl :: a.hyps, (∃ s, sortOf S a.ctx q.lhs = some s) ∧ ∃ s, sortOf S a.ctx q.rhs = some s

/-- The unfolding of a well-sorted sequent is well sorted over the signature. -/
theorem wellSorted_unfold (hd : d.WF S) {a : Seq} (ha : a.WellSorted (S.extend d)) :
    (a.unfoldOp S.length d.body).WellSorted S := by
  intro q hq
  have hq' : ∃ p ∈ a.concl :: a.hyps, q = p.unfoldOp S.length d.body := by
    simp only [Seq.unfoldOp, List.mem_cons, List.mem_map] at hq ⊢
    rcases hq with rfl | ⟨p, hp, rfl⟩
    · exact ⟨a.concl, Or.inl rfl, rfl⟩
    · exact ⟨p, Or.inr hp, rfl⟩
  obtain ⟨p, hp, rfl⟩ := hq'
  obtain ⟨⟨s₁, h₁⟩, ⟨s₂, h₂⟩⟩ := ha p hp
  exact ⟨⟨s₁, sortOf_unfold hd p.lhs h₁⟩, ⟨s₂, sortOf_unfold hd p.rhs h₂⟩⟩

/-- An equation between well-sorted terms holds in the expansion exactly when its unfolding
holds in the model. -/
theorem holds_expand_iff (hd : d.WF S) {Γ : List ℕ} {ρ : List M.Val} (hρ : ρ.map Sigma.fst = Γ)
    {q : Eqn} (hl : ∃ s, sortOf (S.extend d) Γ q.lhs = some s)
    (hr : ∃ s, sortOf (S.extend d) Γ q.rhs = some s) :
    q.Holds (M.expand d hd.sort) ρ ↔ (q.unfoldOp S.length d.body).Holds M ρ := by
  obtain ⟨_, hl⟩ := hl
  obtain ⟨_, hr⟩ := hr
  unfold Eqn.Holds Eqn.unfoldOp
  rw [eval_expand_unfold hd hρ _ hl, eval_expand_unfold hd hρ _ hr]

/-- A well-sorted sequent valid in the expansion has its unfolding valid in the model. -/
theorem valid_unfold_of_valid_expand (hd : d.WF S) {a : Seq} (ha : a.WellSorted (S.extend d))
    (hv : a.Valid (M.expand d hd.sort)) : (a.unfoldOp S.length d.body).Valid M := by
  intro ρ hρ hH
  have hq : ∀ q ∈ a.concl :: a.hyps,
      (q.Holds (M.expand d hd.sort) ρ ↔ (q.unfoldOp S.length d.body).Holds M ρ) :=
    fun q hq ↦ holds_expand_iff hd hρ (ha q hq).1 (ha q hq).2
  exact (hq _ List.mem_cons_self).mp (hv ρ hρ fun h hh ↦
    (hq h (List.mem_cons_of_mem _ hh)).mpr (hH _ (List.mem_map_of_mem hh)))

/-- The operations below {lit}`n` are below every larger bound. -/
theorem opsBelow_mono {n m : ℕ} (hnm : n ≤ m) :
    ∀ t : Tree, OpsBelow n t = true → OpsBelow m t = true :=
  RoseTree.ind fun l cs ih ht ↦ by
    rcases l with _ | k
    · simp [OpsBelow]
    · rw [opsBelow_node_succ, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht ⊢
      exact ⟨by omega, fun c hc ↦ ih c hc (ht.2 c hc)⟩

/-- The application of the operation of index {lit}`n` to variables has its operations below
{lit}`n + 1`. -/
theorem opsBelow_opVars (n m : ℕ) : OpsBelow (n + 1) (opVars n m) = true := by
  rw [opVars, op, opsBelow_node_succ, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true]
  exact ⟨by omega, fun c hc ↦ by
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hc
    simp [OpsBelow, var]⟩

/-- Every operation of a sequent's equations has an index below {lit}`n`. -/
def Seq.OpsBelow (n : ℕ) (a : Seq) : Prop :=
  ∀ q ∈ a.concl :: a.hyps, PartialHorn.OpsBelow n q.lhs = true ∧ PartialHorn.OpsBelow n q.rhs = true

/-- A theory's axioms are of its signature: their operations are the signature's. -/
def Theory.OfSig (T : Theory) : Prop := ∀ a ∈ T.axioms, a.OpsBelow T.sig.length

/-- The extension of a theory whose axioms are of its signature has axioms of its own. -/
theorem ofSig_extend {T : Theory} (hT : T.OfSig) (hd : d.WF T.sig) : (T.extend d).OfSig := by
  have hlen : (T.extend d).sig.length = T.sig.length + 1 := by
    simp [Theory.extend, Sig.extend]
  have hb := opsBelow_mono (Nat.le_succ _) d.body (opsBelow_of_sortOf d.body hd.sort)
  intro a ha q hq
  rw [hlen]
  rcases List.mem_append.mp ha with ha | ha
  · exact ⟨opsBelow_mono (Nat.le_succ _) _ (hT a ha q hq).1,
      opsBelow_mono (Nat.le_succ _) _ (hT a ha q hq).2⟩
  · simp only [Defn.axioms, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hq <;>
      rcases hq with rfl | rfl <;>
      exact ⟨by first | exact hb | exact opsBelow_opVars _ _,
        by first | exact hb | exact opsBelow_opVars _ _⟩

/-- The signature extended by a list of definitions, in order. -/
def Sig.extendAll (S : Sig) (ds : List Defn) : Sig := ds.foldl Sig.extend S

/-- The extension of a theory by a list of definitions, in order. -/
def Theory.extendAll (T : Theory) (ds : List Defn) : Theory := ds.foldl Theory.extend T

/-- The signature of an iterated extension is the iterated extension of the signature. -/
theorem Theory.extendAll_sig (ds : List Defn) :
    ∀ T : Theory, (T.extendAll ds).sig = T.sig.extendAll ds :=
  ds.rec (motive := fun ds ↦ ∀ T : Theory, (T.extendAll ds).sig = T.sig.extendAll ds)
    (fun _ ↦ rfl) (fun d _ ih T ↦ ih (T.extend d))

/-- Every definition of a list is well formed over the signature that the definitions before it
extend. -/
def DefnsWF (S : Sig) (ds : List Defn) : Prop :=
  ds.rec (motive := fun _ ↦ Sig → Prop) (fun _ ↦ True) (fun d _ ih S ↦ d.WF S ∧ ih (S.extend d)) S

/-- The definitions before others of a well-formed list are well formed. -/
theorem defnsWF_of_append (e : List Defn) :
    ∀ (ds : List Defn) (S : Sig), DefnsWF S (ds ++ e) → DefnsWF S ds :=
  List.rec (fun _ _ ↦ trivial) fun d _ ih S h ↦ ⟨h.1, ih (S.extend d) h.2⟩

/-- The unfolding of a list of definitions, the last first, so that each definition's unfolding
meets only the definitions before it. -/
def unfoldAll (S : Sig) (ds : List Defn) (a : Seq) : Seq :=
  ds.rec (motive := fun _ ↦ Sig → Seq)
    (fun _ ↦ a) (fun d _ ih S ↦ (ih (S.extend d)).unfoldOp S.length d.body) S

/-- The unfolding of a list of definitions takes a well-sorted sequent of the extension to one
of the signature. -/
theorem wellSorted_unfoldAll (ds : List Defn) :
    ∀ (S : Sig) (a : Seq), DefnsWF S ds → a.WellSorted (S.extendAll ds) →
      (unfoldAll S ds a).WellSorted S :=
  ds.rec (motive := fun ds ↦ ∀ (S : Sig) (a : Seq), DefnsWF S ds →
      a.WellSorted (S.extendAll ds) → (unfoldAll S ds a).WellSorted S)
    (fun _ _ _ ha ↦ ha)
    (fun d _ ih S a hds ha ↦ wellSorted_unfold hds.1 (ih (S.extend d) a hds.2 ha))

/-- A well-sorted sequent valid in every model of an iterated extension has its unfolding valid
in every model of the theory, when the theory's axioms are of its signature. -/
theorem valid_unfoldAll (ds : List Defn) :
    ∀ (T : Theory) (M : Model.{v} T.sig), IsModel T M → T.OfSig → DefnsWF T.sig ds →
      ∀ a : Seq, a.WellSorted (T.extendAll ds).sig →
      (∀ N : Model.{v} (T.extendAll ds).sig, IsModel (T.extendAll ds) N → a.Valid N) →
      (unfoldAll T.sig ds a).Valid M :=
  ds.rec (motive := fun ds ↦ ∀ (T : Theory) (M : Model.{v} T.sig), IsModel T M → T.OfSig →
      DefnsWF T.sig ds → ∀ a : Seq, a.WellSorted (T.extendAll ds).sig →
      (∀ N : Model.{v} (T.extendAll ds).sig, IsModel (T.extendAll ds) N → a.Valid N) →
      (unfoldAll T.sig ds a).Valid M)
    (fun _ M hM _ _ _ _ hall ↦ hall M hM)
    (fun d ds ih T M hM hT hds a ha hall ↦ by
      have h₁ := ih (T.extend d) (M.expand d hds.1.sort) (isModel_expand hM hT hds.1)
        (ofSig_extend hT hds.1) hds.2 a ha hall
      have ha' : (unfoldAll (T.sig.extend d) ds a).WellSorted (T.sig.extend d) :=
        wellSorted_unfoldAll ds _ a hds.2 ((Theory.extendAll_sig ds (T.extend d)) ▸ ha)
      exact valid_unfold_of_valid_expand hds.1 ha' h₁)

/-- The unfolding leaves a term whose operations precede the definition's. -/
theorem unfoldOp_of_opsBelow (n : ℕ) (b : Tree) :
    ∀ t : Tree, OpsBelow n t = true → unfoldOp n b t = t :=
  RoseTree.ind fun l cs ih ht ↦ by
    rcases l with _ | k
    · exact unfoldOp_node_zero n b cs
    · rw [opsBelow_node_succ, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ht
      rw [unfoldOp_node_succ, if_neg (Nat.ne_of_lt ht.1)]
      exact congrArg (RoseTree.node (k + 1))
        ((List.map_congr_left fun c hc ↦ ih c hc (ht.2 c hc)).trans cs.map_id)

/-- The unfolding of a list of definitions leaves a sequent of the signature. -/
theorem unfoldAll_of_opsBelow (ds : List Defn) :
    ∀ (S : Sig) (a : Seq), a.OpsBelow S.length → unfoldAll S ds a = a :=
  ds.rec (motive := fun ds ↦ ∀ (S : Sig) (a : Seq), a.OpsBelow S.length → unfoldAll S ds a = a)
    (fun _ _ _ ↦ rfl)
    (fun d ds' ih S a ha ↦ by
      have ha' : a.OpsBelow (S.extend d).length := fun q hq ↦
        ⟨opsBelow_mono (by simp [Sig.extend]) _ (ha q hq).1,
          opsBelow_mono (by simp [Sig.extend]) _ (ha q hq).2⟩
      change (unfoldAll (S.extend d) ds' a).unfoldOp S.length d.body = a
      rw [ih _ a ha']
      have he : ∀ q ∈ a.concl :: a.hyps, q.unfoldOp S.length d.body = q := fun q hq ↦
        Eqn.ext (unfoldOp_of_opsBelow _ _ _ (ha q hq).1) (unfoldOp_of_opsBelow _ _ _ (ha q hq).2)
      refine Seq.ext rfl ?_ (he _ List.mem_cons_self)
      exact (List.map_congr_left fun q hq ↦ he q (List.mem_cons_of_mem _ hq)).trans
        a.hyps.map_id)

/-- Non-creativity: a well-sorted sequent of the signature valid in every model of an iterated
extension is valid in every model of the theory. -/
theorem valid_of_valid_extendAll {ds : List Defn} {T : Theory} {M : Model.{v} T.sig}
    (hM : IsModel T M) (hT : T.OfSig) (hds : DefnsWF T.sig ds) {a : Seq}
    (hops : a.OpsBelow T.sig.length) (ha : a.WellSorted (T.extendAll ds).sig)
    (hall : ∀ N : Model.{v} (T.extendAll ds).sig, IsModel (T.extendAll ds) N → a.Valid N) :
    a.Valid M :=
  unfoldAll_of_opsBelow ds T.sig a hops ▸ valid_unfoldAll ds T M hM hT hds a ha hall

/-- Every well-sorted sequent of a development that checks in an iterated extension has its
unfolding valid in every model of the theory, when the theory's axioms are of its signature. -/
theorem checkDevelopment_extendAll_sound {T : Theory} (hT : T.OfSig) {ds : List Defn}
    (hds : DefnsWF T.sig ds) {D : Development} (h : checkDevelopment (T.extendAll ds) D = true)
    {M : Model.{v} T.sig} (hM : IsModel T M) :
    ∀ a ∈ D.map Prod.fst, a.WellSorted (T.extendAll ds).sig → (unfoldAll T.sig ds a).Valid M :=
  fun a ha hws ↦ valid_unfoldAll ds T M hM hT hds a hws fun _ hN ↦
    checkDevelopment_sound hN h a ha

end Geb.PartialHorn

end
