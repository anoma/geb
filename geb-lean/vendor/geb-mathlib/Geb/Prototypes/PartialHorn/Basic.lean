/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.FinEnum
public import Geb.Mathlib.Data.W.Basic
public import Geb.Prototypes.RoseTree.Basic
public import Mathlib.Data.Part

set_option doc.verso true in
/-!
# Partial Horn logic

The logic of partial Horn theories \[PalmgrenVickers2007\], over rose trees. A signature
names, for each partial operation by its index, the sorts of its arguments and the sort of its
result. A term is a rose tree: a variable is the node of label zero over the leaf of its index,
and the operation of index {lit}`k` applied to terms is the node of label {lit}`k + 1` over
them. Any other node of label zero is not a term: it has no sort, no value and no variable in
scope, so that no children of an index are admitted to be ignored. An
equation between two terms holds in a model at an assignment of the variables when both sides
are defined there and denote one value, so that the equation of a term with itself states that
the term is defined. A sequent is a context of sorts, a list of equations as hypotheses and an
equation as its conclusion; a theory is a signature with sequents as its axioms.

A model interprets each sort as a type and each operation as a partial function on sorted
values, whose domain of definition is a proposition, so that a model need not decide where an
operation is defined. It is a model of a theory when each axiom holds in it at every assignment
of the axiom's context that satisfies the axiom's hypotheses.

A certificate is a rose tree whose node's label names a rule and whose children are its
premises' certificates and the terms the rule names. An index a rule names, of a hypothesis, a
variable, an argument, an axiom or a theorem, is the label of a leaf ({lit}`leafIndex`); a node
with children names no index. The checker is a fold over the certificate
that computes each conclusion from its premises' conclusions, trusting no stated conclusion. Its
rules are those of Definition 1 of the source, stated for a single equation as conclusion: a
hypothesis; the reflexivity of a variable; symmetry and transitivity; congruence of an
operation at a defined application; the strictness of operations, by which the arguments of a
defined application are defined; the instance of an axiom at defined terms of its context's
sorts whose hypotheses are proved, which is partial term substitution followed by cut; cut; and
the instance of a theorem of an environment, as of an axiom. Every conclusion the checker
computes holds in every model of the theory in which the environment's theorems hold, and in
every model of an extension of its signature in which its axioms hold.

## Main definitions

* {lit}`Sig`, {lit}`Theory` — signatures and theories.
* {lit}`sortOf`, {lit}`subst`, {lit}`Scoped` — the sort of a term, substitution, and the scope
  of a term's variables.
* {lit}`Model`, {lit}`eval` — models and the value of a term.
* {lit}`Model.get` — the value of an operation defined at its arguments, at its result sort.
* {lit}`Eqn`, {lit}`Seq`, {lit}`Valid`, {lit}`IsModel` — equations, sequents, validity, and
  models of a theory.
* {lit}`leafIndex` — the index a certificate's leaf names.
* {lit}`checkStep`, {lit}`check` — the rules, and the checker.

## Main statements

* {lit}`eval_subst` — the value of a substitution instance is the value at the substituted
  terms' values.
* {lit}`sort_eval` — a defined term's value has the term's sort.
* {lit}`check_sound` — every conclusion the checker computes is valid in every model.

## References

* \[PalmgrenVickers2007\], Definition 1 for the rules, Section 3 for models.

## Tags

partial Horn logic, essentially algebraic theory, partial algebra, proof certificate, soundness
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PartialHorn

open scoped FinEnum

universe v

/-- The terms of a partial Horn theory, and its certificates: rose trees with natural-number
labels. -/
abbrev Tree : Type := RoseTree ℕ

/-- The variable of an index. -/
def var (i : ℕ) : Tree := RoseTree.node 0 [RoseTree.node i []]

/-- The operation of index {lit}`k` applied to terms. -/
def op (k : ℕ) (ts : List Tree) : Tree := RoseTree.node (k + 1) ts

/-- A many-sorted signature of partial operations: for each operation, by its index, the sorts
of its arguments and the sort of its result. -/
abbrev Sig : Type := List (List ℕ × ℕ)

/-- The sort of a term in a context of sorts, or nothing when the term is not well sorted. -/
def sortOf (S : Sig) (Γ : List ℕ) : Tree → Option ℕ :=
  RoseTree.para fun l cs ↦ match l, cs with
    | 0, [(i, _)] => if i.children.isEmpty then Γ[i.label]? else none
    | k + 1, cs => S[k]?.bind fun o ↦ if cs.map Prod.snd = o.1.map some then some o.2 else none
    | _, _ => none

/-- Whether every variable of a term has an index below {lit}`n`. -/
def Scoped (n : ℕ) : Tree → Bool :=
  RoseTree.para fun l cs ↦ match l, cs with
    | 0, [(i, _)] => i.children.isEmpty && decide (i.label < n)
    | 0, _ => false
    | _ + 1, cs => cs.all Prod.snd

/-- The substitution of terms for the variables of a term, the variable of index {lit}`i`
replaced by the term at position {lit}`i`; a variable beyond the terms is left in place, and so
is a node of label zero that is not a variable. -/
def subst (ts : List Tree) : Tree → Tree :=
  RoseTree.para fun l cs ↦ match l, cs with
    | 0, [(i, _)] => if i.children.isEmpty then ts[i.label]?.getD (var i.label)
      else RoseTree.node 0 [i]
    | l, cs => RoseTree.node l (cs.map Prod.snd)

/-- An equation between two terms. -/
@[ext] structure Eqn where
  /-- The left side. -/
  lhs : Tree
  /-- The right side. -/
  rhs : Tree
deriving DecidableEq

/-- The substitution of terms for the variables of both sides of an equation. -/
def Eqn.subst (ts : List Tree) (q : Eqn) : Eqn := ⟨PartialHorn.subst ts q.lhs,
  PartialHorn.subst ts q.rhs⟩

/-- Whether every variable of both sides of an equation has an index below {lit}`n`. -/
def Eqn.Scoped (n : ℕ) (q : Eqn) : Bool := PartialHorn.Scoped n q.lhs && PartialHorn.Scoped n q.rhs

/-- A Horn sequent: a context of sorts, hypotheses and a conclusion, each an equation. -/
@[ext] structure Seq where
  /-- The sorts of the variables. -/
  ctx : List ℕ
  /-- The hypotheses. -/
  hyps : List Eqn
  /-- The conclusion. -/
  concl : Eqn

/-- Whether every variable of a sequent's equations is in its context. -/
def Seq.Scoped (a : Seq) : Bool :=
  a.hyps.all (·.Scoped a.ctx.length) && a.concl.Scoped a.ctx.length

/-- A partial Horn theory: a signature and axioms. -/
structure Theory where
  /-- The signature. -/
  sig : Sig
  /-- The axioms. -/
  axioms : List Seq

/-- A model of a signature: a type for each sort, and for each operation, by its index, a
partial function from lists of sorted values to sorted values, whose values have the operation's
result sort. -/
structure Model (S : Sig) where
  /-- The values of each sort. -/
  Car : ℕ → Type v
  /-- The partial operations. -/
  op : ℕ → List (Σ s, Car s) → Part (Σ s, Car s)
  /-- A value of an operation has the operation's result sort. -/
  op_sort : ∀ {k : ℕ} {args : List (Σ s, Car s)} {w : Σ s, Car s}, w ∈ op k args →
    (S[k]?).map Prod.snd = some w.1

variable {S : Sig}

/-- The sorted values of a model. -/
abbrev Model.Val (M : Model.{v} S) : Type v := Σ s, M.Car s

/-- The value of a term in a model at an assignment of values to the variables by index,
defined where the term is. -/
def eval (M : Model.{v} S) (ρ : List M.Val) : Tree → Part M.Val :=
  RoseTree.para fun l cs ↦ match l, cs with
    | 0, [(i, _)] => if i.children.isEmpty then ρ[i.label]? else Part.none
    | k + 1, cs => (cs.mapM Prod.snd).bind (M.op k)
    | _, _ => Part.none

/-- An equation holds at an assignment when both sides are defined there with one value. -/
def Eqn.Holds (M : Model.{v} S) (ρ : List M.Val) (q : Eqn) : Prop :=
  ∃ w, eval M ρ q.lhs = Part.some w ∧ eval M ρ q.rhs = Part.some w

/-- A conclusion is valid under hypotheses in a context when it holds at every assignment of
the context's sorts at which the hypotheses hold. -/
def Valid (M : Model.{v} S) (Γ : List ℕ) (H : List Eqn) (q : Eqn) : Prop :=
  ∀ ρ : List M.Val, ρ.map Sigma.fst = Γ → (∀ h ∈ H, h.Holds M ρ) → q.Holds M ρ

/-- A sequent is valid in a model when its conclusion is valid under its hypotheses. -/
def Seq.Valid (M : Model.{v} S) (a : Seq) : Prop := PartialHorn.Valid M a.ctx a.hyps a.concl

/-- A model of a theory: every axiom is valid in it. -/
def IsModel (T : Theory) (M : Model.{v} T.sig) : Prop := ∀ a ∈ T.axioms, a.Valid M

namespace Model

variable (M : Model.{v} S)

/-- The value of an operation defined at its arguments, at its result sort. -/
def get {k : ℕ} {args : List M.Val} {s : ℕ} (h : ∃ a, M.op k args = Part.some ⟨s, a⟩) :
    M.Car s :=
  have hd : (M.op k args).Dom := by obtain ⟨a, ha⟩ := h; rw [ha]; trivial
  have he : ((M.op k args).get hd).1 = s := by
    obtain ⟨a, ha⟩ := h
    rw [Part.get_eq_of_mem (Part.eq_some_iff.mp ha)]
  he ▸ ((M.op k args).get hd).2

/-- An operation defined at its arguments returns the value {lit}`get` reads. -/
theorem op_eq_get {k : ℕ} {args : List M.Val} {s : ℕ}
    (h : ∃ a, M.op k args = Part.some ⟨s, a⟩) : M.op k args = Part.some ⟨s, M.get h⟩ := by
  obtain ⟨a, ha⟩ := h
  simp only [get]
  generalize_proofs hs he
  revert hs he
  rw [ha]
  intro hs he
  rfl

/-- A value an operation returns has the operation's result sort. -/
theorem exists_op_eq {k : ℕ} {args : List M.Val} {w : M.Val} {s : ℕ}
    (hw : M.op k args = Part.some w) (hs : (S[k]?).map Prod.snd = some s) :
    ∃ a, M.op k args = Part.some ⟨s, a⟩ := by
  have h := M.op_sort (Part.eq_some_iff.mp hw)
  rw [hs, Option.some.injEq] at h
  obtain ⟨t, a⟩ := w
  subst h
  exact ⟨a, hw⟩

end Model

namespace Rule

/-- A hypothesis, by index. -/
@[match_pattern] abbrev hyp : ℕ := 0

/-- The reflexivity of a variable, by index: the variable is defined. -/
@[match_pattern] abbrev refl : ℕ := 1

/-- Symmetry. -/
@[match_pattern] abbrev symm : ℕ := 2

/-- Transitivity. -/
@[match_pattern] abbrev trans : ℕ := 3

/-- Congruence of an operation at a defined application. -/
@[match_pattern] abbrev cong : ℕ := 4

/-- Strictness: an argument of a defined application is defined. -/
@[match_pattern] abbrev strict : ℕ := 5

/-- An instance of an axiom. -/
@[match_pattern] abbrev ax : ℕ := 6

/-- Cut. -/
@[match_pattern] abbrev cut : ℕ := 7

/-- An instance of a theorem of the environment. -/
@[match_pattern] abbrev thm : ℕ := 8

end Rule

/-- The checker's result at a certificate: the conclusion, as a function of the context and
the hypotheses, or nothing when the certificate does not check. -/
abbrev Chk : Type := List ℕ → List Eqn → Option Eqn

/-- The index a certificate's leaf names; a node with children names none, so that no children
of an index are admitted only to be ignored. -/
def leafIndex (t : Tree) : Option ℕ := if t.children.isEmpty then some t.label else none

/-- A leaf names its label. -/
@[simp] theorem leafIndex_leaf (i : ℕ) : leafIndex (RoseTree.node i []) = some i := rfl

/-- A tree names an index exactly when it is the leaf of that index. -/
theorem leafIndex_eq_some {t : Tree} {i : ℕ} : leafIndex t = some i ↔ t = RoseTree.node i [] := by
  constructor
  · intro h
    rw [leafIndex] at h
    split at h
    · rename_i hc
      obtain rfl := Option.some_inj.mp h
      conv_lhs => rw [← RoseTree.node_label_children t]
      rw [List.isEmpty_iff.mp hc]
    · exact absurd h (by simp)
  · rintro rfl
    rfl

/-- The instance of a sequent at the terms of a certificate's node: the terms for the context's
variables, then a premise for each term whose conclusion's left side is that term, then a
premise for each hypothesis whose conclusion is its instance. The terms must have the context's
sorts and the sequent's variables must lie in its context. -/
def inst (S : Sig) (a : Seq) (cs : List (Tree × Chk)) : Chk := fun Γ H ↦
  let n := a.ctx.length
  let ts := (cs.take n).map Prod.fst
  let ds := ((cs.drop n).take n).map fun c ↦ (c.2 Γ H).map Eqn.lhs
  let hs := (cs.drop (n + n)).map fun c ↦ c.2 Γ H
  if a.Scoped ∧ ts.map (sortOf S Γ) = a.ctx.map some ∧ ds = ts.map some ∧
      hs = a.hyps.map fun h ↦ some (h.subst ts) then
    some (a.concl.subst ts)
  else none

/-- One rule of the checker, by the label of a certificate's node: its children are the
premises' certificates, with their results, and the terms the rule names. -/
def checkStep (T : Theory) (E : Array Seq) (l : ℕ) (cs : List (Tree × Chk)) : Chk := fun Γ H ↦
  match l, cs with
  | Rule.hyp, [(i, _)] => (leafIndex i).bind fun i ↦ H[i]?
  | Rule.refl, [(i, _)] => (leafIndex i).bind fun i ↦
    if i < Γ.length then some ⟨var i, var i⟩ else none
  | Rule.symm, [(_, p)] => (p Γ H).map fun q ↦ ⟨q.rhs, q.lhs⟩
  | Rule.trans, [(_, p), (_, p')] => (p Γ H).bind fun q ↦ (p' Γ H).bind fun q' ↦
    if q.rhs = q'.lhs then some ⟨q.lhs, q'.rhs⟩ else none
  | Rule.cong, (_, d) :: ps => (d Γ H).bind fun q ↦
    if q.lhs.label ≠ 0 ∧ (ps.map fun p ↦ (p.2 Γ H).map Eqn.lhs) = q.lhs.children.map some then
      (ps.mapM fun (p : Tree × Chk) ↦ (p.2 Γ H).map Eqn.rhs).map fun ts ↦
        ⟨q.lhs, RoseTree.node q.lhs.label ts⟩
    else none
  | Rule.strict, [(j, _), (_, p)] => (leafIndex j).bind fun j ↦ (p Γ H).bind fun q ↦
    if q.lhs.label ≠ 0 then (q.lhs.children[j]?).map fun t ↦ ⟨t, t⟩ else none
  | Rule.ax, (j, _) :: cs => (leafIndex j).bind fun j ↦
    T.axioms[j]?.bind fun a ↦ inst T.sig a cs Γ H
  | Rule.cut, [(_, p), (_, p')] => (p Γ H).bind fun h ↦ p' Γ (h :: H)
  | Rule.thm, (j, _) :: cs => (leafIndex j).bind fun j ↦
    E[j]?.bind fun a ↦ inst T.sig a cs Γ H
  | _, _ => none

/-- The checker: the conclusion of a certificate in a theory and an environment of theorems, as
a function of the context and the hypotheses, or nothing when the certificate does not check. -/
def check (T : Theory) (E : Array Seq) (c : Tree) : Chk := RoseTree.para (checkStep T E) c

section Soundness

/-- A list's elements all have values under a partial function exactly when the function
mapped over the list is the list of those values. -/
theorem mapM_eq_some_iff {α β : Type*} {f : α → Option β} (l : List α) :
    ∀ vs : List β, l.mapM f = some vs ↔ l.map f = vs.map some :=
  l.rec (motive := fun l ↦ ∀ vs, l.mapM f = some vs ↔ l.map f = vs.map some)
    (fun vs ↦ by cases vs <;> simp)
    (fun a l ih vs ↦ by
      cases vs with
      | nil => simp [List.mapM_cons, Option.bind_eq_some_iff]
      | cons v vs =>
        simp only [List.mapM_cons, List.map_cons, List.cons.injEq, ← ih vs]
        cases f a <;> cases l.mapM f <;> simp)

/-- A bind of partial values has a value exactly when the first has one at which the function
has that value. -/
theorem part_bind_eq_some_iff {α β : Type*} {o : Part α} {f : α → Part β} {b : β} :
    o.bind f = Part.some b ↔ ∃ a, o = Part.some a ∧ f a = Part.some b := by
  simp only [Part.eq_some_iff, Part.mem_bind_iff]

/-- A list's elements all have values under a partial function exactly when the function
mapped over the list, in {name}`Part`, is the list of those values. -/
theorem mapM_part_eq_some_iff {α β : Type*} {f : α → Part β} (l : List α) :
    ∀ vs : List β, l.mapM f = Part.some vs ↔ l.map f = vs.map Part.some :=
  l.rec (motive := fun l ↦ ∀ vs, l.mapM f = Part.some vs ↔ l.map f = vs.map Part.some)
    (fun vs ↦ by cases vs <;> simp [Part.pure_eq_some, Part.some_inj])
    (fun a l ih vs ↦ by
      cases vs with
      | nil => simp [List.mapM_cons, part_bind_eq_some_iff, Part.some_inj]
      | cons v vs =>
        simp only [List.mapM_cons, List.map_cons, List.cons.injEq, ← ih vs, Part.bind_eq_bind,
          Part.pure_eq_some, part_bind_eq_some_iff, Part.some_inj]
        constructor
        · rintro ⟨b, hb, bs, hbs, rfl, rfl⟩
          exact ⟨hb, hbs⟩
        · rintro ⟨hb, hbs⟩
          exact ⟨v, hb, vs, hbs, rfl, rfl⟩)

variable {M : Model.{v} S} {ρ : List M.Val}

/-- The value of a variable is the assignment's value at its index. -/
@[simp] theorem eval_var (i : ℕ) : eval M ρ (var i) = (ρ[i]? : Part M.Val) := by
  simp [eval, var]

/-- The value of a node of label zero over a leaf is the assignment's value at the leaf's
label. -/
theorem eval_node_zero {i : Tree} (hi : i.children = []) :
    eval M ρ (RoseTree.node 0 [i]) = (ρ[i.label]? : Part M.Val) := by
  simp [eval, hi]

/-- A node of label zero over a child that is not a leaf has no value. -/
theorem eval_node_zero_of_not {i : Tree} (hi : i.children ≠ []) :
    eval M ρ (RoseTree.node 0 [i]) = Part.none := by
  simp [eval, hi]

/-- A node of label zero over one child has a value exactly when the child is a leaf whose label
has it in the assignment. -/
theorem eval_node_zero_eq_some {i : Tree} {w : M.Val} :
    eval M ρ (RoseTree.node 0 [i]) = Part.some w ↔
      i.children = [] ∧ (ρ[i.label]? : Part M.Val) = Part.some w := by
  rcases hc : i.children with _ | ⟨d, ds⟩
  · simp [eval_node_zero hc]
  · rw [eval_node_zero_of_not (i := i) (by simp [hc])]
    exact ⟨fun h ↦ absurd h.symm (Part.some_ne_none w), fun h ↦ absurd h.1 (by simp)⟩

/-- The value of an operation's application: the operation at its arguments' values, when
they are all defined. -/
theorem eval_node_succ (k : ℕ) (ts : List Tree) :
    eval M ρ (RoseTree.node (k + 1) ts) = (ts.mapM (eval M ρ)).bind (M.op k) := by
  simp only [eval, RoseTree.para_node, List.mapM_map]
  rfl

/-- The value of an operation's application, written with {name}`op`. -/
theorem eval_op (k : ℕ) (ts : List Tree) :
    eval M ρ (op k ts) = (ts.mapM (eval M ρ)).bind (M.op k) :=
  eval_node_succ k ts

/-- Substitution at a variable's node. -/
theorem subst_node_zero (ts : List Tree) {i : Tree} (hi : i.children = []) :
    subst ts (RoseTree.node 0 [i]) = ts[i.label]?.getD (var i.label) := by
  simp [subst, hi]

/-- Substitution leaves a node of label zero over a child that is not a leaf in place. -/
theorem subst_node_zero_of_not (ts : List Tree) {i : Tree} (hi : i.children ≠ []) :
    subst ts (RoseTree.node 0 [i]) = RoseTree.node 0 [i] := by
  simp [subst, hi]

/-- Substitution at an operation's node substitutes in the arguments. -/
theorem subst_node_succ (ts : List Tree) (k : ℕ) (cs : List Tree) :
    subst ts (RoseTree.node (k + 1) cs) = RoseTree.node (k + 1) (cs.map (subst ts)) := by
  simp [subst]
  rfl

/-- Substitution of no terms leaves every term in place. -/
theorem subst_nil : ∀ t : Tree, subst [] t = t :=
  RoseTree.ind fun l cs ih ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · simp [subst]
      · by_cases hi : i.children = []
        · rw [subst_node_zero _ hi, List.getElem?_nil, Option.getD_none, var,
            ← RoseTree.node_label_children i, hi, RoseTree.label_node]
        · exact subst_node_zero_of_not _ hi
      · simp only [subst, RoseTree.para_node, List.map_cons, List.map_map]
        change RoseTree.node 0 (subst [] i :: subst [] j :: cs.map (subst [])) = _
        rw [ih i (by simp), ih j (by simp),
          (List.map_congr_left fun c hc ↦ ih c (by simp [hc])).trans (List.map_id cs)]
    · rw [subst_node_succ]
      exact congrArg _ ((List.map_congr_left ih).trans (List.map_id cs))

/-- A variable's node is in scope when its index is. -/
theorem scoped_node_zero (n : ℕ) {i : Tree} (hi : i.children = []) :
    Scoped n (RoseTree.node 0 [i]) = decide (i.label < n) := by
  simp [Scoped, hi]

/-- A node of label zero over a child that is not a leaf is in no scope. -/
theorem scoped_node_zero_of_not (n : ℕ) {i : Tree} (hi : i.children ≠ []) :
    Scoped n (RoseTree.node 0 [i]) = false := by
  simp [Scoped, hi]

/-- A node of label zero over one child is in scope exactly when the child is a leaf whose label
is. -/
theorem scoped_node_zero_iff {n : ℕ} {i : Tree} :
    Scoped n (RoseTree.node 0 [i]) = true ↔ i.children = [] ∧ i.label < n := by
  rcases hc : i.children with _ | ⟨d, ds⟩
  · simp [scoped_node_zero n hc]
  · simp [scoped_node_zero_of_not n (i := i) (by simp [hc])]

/-- An operation's node is in scope when its arguments are. -/
theorem scoped_node_succ (n k : ℕ) (cs : List Tree) :
    Scoped n (RoseTree.node (k + 1) cs) = cs.all (Scoped n) := by
  simp [Scoped, List.all_map]
  rfl

/-- Mapping monadic functions that agree on a list's elements gives one result. -/
theorem mapM_congr {m : Type _ → Type _} [Monad m] [LawfulMonad m] {α β : Type _}
    {f g : α → m β} {l : List α} (h : ∀ a ∈ l, f a = g a) : l.mapM f = l.mapM g := by
  rw [← Function.id_comp f, ← Function.id_comp g, ← List.mapM_map, ← List.mapM_map,
    List.map_congr_left h]

/-- The value of a substitution instance of a term in scope is the term's value at the
substituted terms' values. -/
theorem eval_subst {ts : List Tree} {ws : List M.Val}
    (hts : ts.map (eval M ρ) = ws.map Part.some) :
    ∀ t, Scoped ts.length t = true → eval M ρ (subst ts t) = eval M ws t :=
  RoseTree.ind fun l cs ih hs ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · simp [Scoped] at hs
      · obtain ⟨hc, hi⟩ := scoped_node_zero_iff.mp hs
        have hlen : ts.length = ws.length := by simpa using congrArg List.length hts
        have hi' : i.label < ws.length := hlen ▸ hi
        have hw := congrArg (fun l ↦ l[i.label]?) hts
        simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
          List.getElem?_eq_getElem hi', Option.map_some, Option.some.injEq] at hw
        rw [subst_node_zero _ hc, eval_node_zero hc, List.getElem?_eq_getElem hi,
          List.getElem?_eq_getElem hi', Option.getD_some, Part.coe_some]
        exact hw
      · simp [Scoped] at hs
    · rw [scoped_node_succ, List.all_eq_true] at hs
      rw [subst_node_succ, eval_node_succ, eval_node_succ, List.mapM_map]
      exact congrArg (fun o ↦ Part.bind o (M.op k)) (mapM_congr fun c hc ↦ ih c hc (hs c hc))

/-- The sort of a variable's node is the context's sort at its index. -/
theorem sortOf_node_zero (Γ : List ℕ) {i : Tree} (hi : i.children = []) :
    sortOf S Γ (RoseTree.node 0 [i]) = Γ[i.label]? := by
  simp [sortOf, hi]

/-- A node of label zero over a child that is not a leaf has no sort. -/
theorem sortOf_node_zero_of_not (Γ : List ℕ) {i : Tree} (hi : i.children ≠ []) :
    sortOf S Γ (RoseTree.node 0 [i]) = none := by
  simp [sortOf, hi]

/-- A node of label zero over one child has a sort exactly when the child is a leaf whose label
has it in the context. -/
theorem sortOf_node_zero_eq_some {Γ : List ℕ} {i : Tree} {s : ℕ} :
    sortOf S Γ (RoseTree.node 0 [i]) = some s ↔ i.children = [] ∧ Γ[i.label]? = some s := by
  rcases hc : i.children with _ | ⟨d, ds⟩
  · simp [sortOf_node_zero Γ hc]
  · simp [sortOf_node_zero_of_not Γ (i := i) (by simp [hc])]

/-- The sort of an operation's node is the operation's result sort, when its arguments have
the operation's argument sorts. -/
theorem sortOf_node_succ (Γ : List ℕ) (k : ℕ) (cs : List Tree) :
    sortOf S Γ (RoseTree.node (k + 1) cs) = S[k]?.bind fun o ↦
      if cs.map (sortOf S Γ) = o.1.map some then some o.2 else none := by
  simp only [sortOf, RoseTree.para_node, List.map_map]
  rfl

/-- A term's sort is its sort in every signature that extends its own. -/
theorem sortOf_append (S' : Sig) {Γ : List ℕ} :
    ∀ t : Tree, ∀ {s : ℕ}, sortOf S Γ t = some s → sortOf (S ++ S') Γ t = some s :=
  RoseTree.ind fun l cs ih s hs ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · simp [sortOf] at hs
      rotate_left
      · simp [sortOf] at hs
      exact sortOf_node_zero_eq_some.mpr (sortOf_node_zero_eq_some.mp hs)
    · rw [sortOf_node_succ] at hs ⊢
      obtain ⟨o, ho, hs⟩ := Option.bind_eq_some_iff.mp hs
      rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp ho).1, ho, Option.bind_some]
      split_ifs at hs with hcs
      have hcs' : cs.map (sortOf (S ++ S') Γ) = o.1.map some := by
        rw [← hcs]
        refine List.map_congr_left fun c hc ↦ ?_
        obtain ⟨s', hs'⟩ : ∃ s', sortOf S Γ c = some s' := by
          have hm : sortOf S Γ c ∈ o.1.map some := hcs ▸ List.mem_map_of_mem hc
          obtain ⟨s', -, h⟩ := List.mem_map.mp hm
          exact ⟨s', h.symm⟩
        rw [hs', ih c hc hs']
      simpa [hcs'] using hs

/-- A term's sort is its sort in every signature its own is a prefix of. -/
theorem sortOf_of_prefix {S S' : Sig} (h : S <+: S') {Γ : List ℕ} {t : Tree} {s : ℕ}
    (ht : sortOf S Γ t = some s) : sortOf S' Γ t = some s := by
  obtain ⟨S'', rfl⟩ := h
  exact sortOf_append S'' t ht

/-- A defined term's value has the term's sort, at an assignment of the context's sorts. -/
theorem sort_eval {Γ : List ℕ} (hρ : ρ.map Sigma.fst = Γ) :
    ∀ t : Tree, ∀ {s : ℕ} {w : M.Val}, sortOf S Γ t = some s → eval M ρ t = Part.some w →
      w.1 = s :=
  RoseTree.ind fun l cs _ s w hs he ↦ by
    rcases l with _ | k
    · rcases cs with _ | ⟨i, _ | ⟨j, cs⟩⟩
      · simp [sortOf] at hs
      · obtain ⟨hc, hs⟩ := sortOf_node_zero_eq_some.mp hs
        rw [eval_node_zero hc] at he
        have h := congrArg (fun l ↦ l[i.label]?) hρ
        simp only [List.getElem?_map, hs] at h
        rcases hρi : ρ[i.label]? with _ | a
        · rw [hρi, Part.coe_none] at he
          exact absurd he.symm (Part.some_ne_none w)
        · rw [hρi, Part.coe_some, Part.some_inj] at he
          rw [hρi, Option.map_some, Option.some.injEq] at h
          exact he ▸ h
      · simp [sortOf] at hs
    · rw [eval_node_succ, part_bind_eq_some_iff] at he
      obtain ⟨_, -, hop⟩ := he
      have hw := M.op_sort (Part.eq_some_iff.mp hop)
      rw [sortOf_node_succ, Option.bind_eq_some_iff] at hs
      obtain ⟨o, hk, ho⟩ := hs
      rw [hk, Option.map_some, Option.some.injEq] at hw
      split at ho
      · exact hw.symm.trans (Option.some.inj ho)
      · exact absurd ho (by simp)

/-- When a partial function has a value at every element of a list, it maps the list to the
list of those values. -/
theorem exists_map_eq_map_some {α β : Type*} {f : α → Part β} (l : List α) :
    (∀ a ∈ l, ∃ b, f a = Part.some b) → ∃ bs : List β, l.map f = bs.map Part.some :=
  l.rec (motive := fun l ↦ (∀ a ∈ l, ∃ b, f a = Part.some b) →
      ∃ bs : List β, l.map f = bs.map Part.some)
    (fun _ ↦ ⟨[], rfl⟩)
    (fun a l ih h ↦ by
      obtain ⟨b, hb⟩ := h a List.mem_cons_self
      obtain ⟨bs, hbs⟩ := ih fun a' ha' ↦ h a' (List.mem_cons_of_mem a ha')
      exact ⟨b :: bs, by simp [hb, hbs]⟩)

/-- An instance of a valid sequent is valid, when the checker's premises are, its terms sorted
in a signature that the model's extends. -/
theorem inst_sound {S₀ : Sig} (hS : S₀ <+: S) {a : Seq} {cs : List (Tree × Chk)} {Γ : List ℕ}
    {H : List Eqn} {q : Eqn} (ha : a.Valid M)
    (hcs : ∀ c ∈ cs, ∀ Γ' H' q', c.2 Γ' H' = some q' → Valid M Γ' H' q')
    (h : inst S₀ a cs Γ H = some q) : Valid M Γ H q := by
  simp only [inst] at h
  split at h
  · rename_i hc
    obtain ⟨hsc, hsort, hds, hhs⟩ := hc
    cases h
    intro ρ hρ hH
    set ts := (cs.take a.ctx.length).map Prod.fst with hts
    have hlen : ts.length = a.ctx.length := by simpa using congrArg List.length hsort
    have hdef : ∀ t ∈ ts, ∃ w, eval M ρ t = Part.some w := by
      intro t ht
      have hm : some t ∈ ts.map some := List.mem_map_of_mem ht
      rw [← hds] at hm
      obtain ⟨c, hc, hct⟩ := List.mem_map.mp hm
      obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hct
      obtain ⟨w, hw, -⟩ :=
        hcs c (List.mem_of_mem_drop (List.mem_of_mem_take hc)) Γ H e he ρ hρ hH
      exact ⟨w, hw⟩
    obtain ⟨ws, hws⟩ := exists_map_eq_map_some _ hdef
    have hlw : ws.length = a.ctx.length :=
      (by simpa using congrArg List.length hws : ts.length = ws.length).symm.trans hlen
    have hwsort : ws.map Sigma.fst = a.ctx := by
      refine List.ext_getElem (by simpa using hlw) fun i h1 h2 ↦ ?_
      have hi : i < ts.length := hlen ▸ h2
      have e1 := congrArg (fun l ↦ l[i]?) hws
      have e2 := congrArg (fun l ↦ l[i]?) hsort
      simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
        List.getElem?_eq_getElem (hlw ▸ h2), List.getElem?_eq_getElem h2, Option.map_some,
        Option.some.injEq] at e1 e2
      simpa using sort_eval hρ _ (sortOf_of_prefix hS e2) e1
    have hsc' := hsc
    simp only [Seq.Scoped, Bool.and_eq_true, List.all_eq_true, Eqn.Scoped] at hsc'
    obtain ⟨hsh, hscl, hscr⟩ := hsc'
    rw [← hlen] at hsh hscl hscr
    have hhyp : ∀ h ∈ a.hyps, h.Holds M ws := by
      intro h hh
      have hm : some (h.subst ts) ∈ a.hyps.map fun h ↦ some (h.subst ts) :=
        List.mem_map.mpr ⟨h, hh, rfl⟩
      rw [← hhs] at hm
      obtain ⟨c, hc, hct⟩ := List.mem_map.mp hm
      obtain ⟨w, h1, h2⟩ := hcs c (List.mem_of_mem_drop hc) Γ H _ hct ρ hρ hH
      obtain ⟨hl, hr⟩ := hsh h hh
      exact ⟨w, (eval_subst hws _ hl).symm.trans h1, (eval_subst hws _ hr).symm.trans h2⟩
    obtain ⟨w, h1, h2⟩ := ha ws hwsort hhyp
    exact ⟨w, (eval_subst hws _ hscl).trans h1, (eval_subst hws _ hscr).trans h2⟩
  · exact absurd h (by simp)

/-- Every conclusion the checker computes is valid in every model, of a signature the theory's
is a prefix of, in which the theory's axioms and the environment's theorems are valid. -/
theorem check_sound {T : Theory} {E : Array Seq} (hS : T.sig <+: S)
    (hM : ∀ a ∈ T.axioms, a.Valid M) (hE : ∀ a ∈ E, a.Valid M) :
    ∀ c : Tree, ∀ Γ H q, check T E c Γ H = some q → Valid M Γ H q :=
  RoseTree.ind fun l cs ih Γ H q h ↦ by
    have hcs : ∀ c ∈ cs.map (fun c ↦ (c, check T E c)), ∀ Γ' H' q',
        c.2 Γ' H' = some q' → Valid M Γ' H' q' := by
      intro c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'
    rw [check, RoseTree.para_node] at h
    change checkStep T E l (cs.map fun c ↦ (c, check T E c)) Γ H = some q at h
    generalize cs.map (fun c ↦ (c, check T E c)) = rs at h hcs
    unfold checkStep at h
    split at h
    · -- a hypothesis
      obtain ⟨i, -, hi⟩ := Option.bind_eq_some_iff.mp h
      exact fun ρ _ hH ↦ hH q (List.mem_of_getElem? hi)
    · -- the reflexivity of a variable
      obtain ⟨i, -, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i hi
        cases h
        intro ρ hρ _
        have hi' : i < ρ.length := by simpa [← hρ] using hi
        exact ⟨ρ[i], by simp [hi', Part.coe_some], by simp [hi', Part.coe_some]⟩
      · exact absurd h (by simp)
    · -- symmetry
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      intro ρ hρ hH
      obtain ⟨w, h1, h2⟩ := hcs _ List.mem_cons_self Γ H q' hq' ρ hρ hH
      exact ⟨w, h2, h1⟩
    · -- transitivity
      rename_i _ p _ p'
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨q₁, hq₁, q₂, hq₂, h⟩ := h
      split at h
      · rename_i hmid
        cases h
        intro ρ hρ hH
        obtain ⟨w, h1, h2⟩ := hcs _ List.mem_cons_self Γ H q₁ hq₁ ρ hρ hH
        obtain ⟨w', h1', h2'⟩ :=
          hcs _ (List.mem_cons_of_mem _ List.mem_cons_self) Γ H q₂ hq₂ ρ hρ hH
        rw [← hmid, h2, Part.some_inj] at h1'
        exact ⟨w, h1, h1' ▸ h2'⟩
      · exact absurd h (by simp)
    · -- congruence of an operation at a defined application
      rename_i _ d ps
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨q₀, hq₀, h⟩ := h
      split at h
      · rename_i hc
        obtain ⟨hl, hls⟩ := hc
        obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
        rw [mapM_eq_some_iff] at hts
        intro ρ hρ hH
        obtain ⟨w, h1, -⟩ := hcs _ List.mem_cons_self Γ H q₀ hq₀ ρ hρ hH
        obtain ⟨k, hk⟩ : ∃ k, q₀.lhs.label = k + 1 := ⟨q₀.lhs.label - 1, by omega⟩
        have hlhs : q₀.lhs = RoseTree.node (k + 1) q₀.lhs.children := by
          rw [← hk]; exact (RoseTree.node_label_children _).symm
        have hlen₁ : ps.length = q₀.lhs.children.length := by
          simpa using congrArg List.length hls
        have hlen₂ : ps.length = ts.length := by simpa using congrArg List.length hts
        have hmap : q₀.lhs.children.map (eval M ρ) = ts.map (eval M ρ) := by
          refine List.ext_getElem (by simp [← hlen₁, hlen₂]) fun i hi₁ hi₂ ↦ ?_
          have hi : i < ps.length := by simpa [hlen₁] using hi₁
          have e₁ := congrArg (fun l ↦ l[i]?) hls
          have e₂ := congrArg (fun l ↦ l[i]?) hts
          simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
            List.getElem?_eq_getElem (hlen₁ ▸ hi), List.getElem?_eq_getElem (hlen₂ ▸ hi),
            Option.map_some, Option.some.injEq] at e₁ e₂
          obtain ⟨e, he, hel⟩ := Option.map_eq_some_iff.mp e₁
          rw [he, Option.map_some, Option.some.injEq] at e₂
          obtain ⟨v, hv₁, hv₂⟩ :=
            hcs ps[i] (List.mem_cons_of_mem _ (List.getElem_mem hi)) Γ H e he ρ hρ hH
          simp only [List.getElem_map]
          rw [← hel, hv₁, ← e₂, hv₂]
        refine ⟨w, h1, ?_⟩
        rw [hlhs, eval_node_succ] at h1
        change eval M ρ (RoseTree.node q₀.lhs.label ts) = Part.some w
        rw [hk, eval_node_succ, ← h1, ← Function.id_comp (eval M ρ), ← List.mapM_map,
          ← List.mapM_map, hmap]
      · exact absurd h (by simp)
    · -- strictness: an argument of a defined application is defined
      rename_i _ _ _ p
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨j, -, q₀, hq₀, h⟩ := h
      split at h
      · rename_i hl
        obtain ⟨t, ht, rfl⟩ := Option.map_eq_some_iff.mp h
        intro ρ hρ hH
        obtain ⟨w, h1, -⟩ := hcs _ (List.mem_cons_of_mem _ List.mem_cons_self) Γ H q₀ hq₀ ρ hρ hH
        obtain ⟨k, hk⟩ : ∃ k, q₀.lhs.label = k + 1 := ⟨q₀.lhs.label - 1, by omega⟩
        rw [← RoseTree.node_label_children q₀.lhs, hk, eval_node_succ,
          part_bind_eq_some_iff] at h1
        obtain ⟨args, hargs, -⟩ := h1
        rw [mapM_part_eq_some_iff] at hargs
        have hj : j < q₀.lhs.children.length := (List.getElem?_eq_some_iff.mp ht).1
        have e := congrArg (fun l ↦ l[j]?) hargs
        simp only [List.getElem?_map, ht, Option.map_some] at e
        obtain ⟨a, -, ha⟩ := Option.map_eq_some_iff.mp e.symm
        exact ⟨a, ha.symm, ha.symm⟩
      · exact absurd h (by simp)
    · -- an instance of an axiom
      rename_i _ _ cs'
      obtain ⟨j, -, hj⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp hj
      exact inst_sound hS (hM a (List.mem_of_getElem? ha))
        (fun c hc ↦ hcs c (List.mem_cons_of_mem _ hc)) h
    · -- cut
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨q₁, hq₁, hq⟩ := h
      intro ρ hρ hH
      have h₁ := hcs _ List.mem_cons_self Γ H q₁ hq₁ ρ hρ hH
      exact hcs _ (List.mem_cons_of_mem _ List.mem_cons_self) Γ (q₁ :: H) q hq ρ hρ
        (List.forall_mem_cons.mpr ⟨h₁, hH⟩)
    · -- an instance of a theorem
      rename_i _ _ cs'
      obtain ⟨j, -, hj⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp hj
      exact inst_sound hS (hE a (Array.mem_of_getElem? ha))
        (fun c hc ↦ hcs c (List.mem_cons_of_mem _ hc)) h
    · exact absurd h (by simp)

end Soundness

end Geb.PartialHorn

end
