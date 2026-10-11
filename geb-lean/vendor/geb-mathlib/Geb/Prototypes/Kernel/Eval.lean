/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Kernel.Loading

set_option doc.verso true

/-!
# Evaluation of kernel terms

A big-step evaluator of the kernel's terms, whose values are trees: a tree as its quotation, the
unit value, a pair of values, a list of values as the kernel's empty list and list nodes, a
function as a closure of its environment, its argument's type and its body, and a constant
applied to fewer arguments than it takes as the application of the constant to their values. The
evaluator runs with fuel: at each level it evaluates a term by structural recursion on the term,
and applies a value to a value, and evaluates a reference's definition, by the level below, so
that every application and every reference consumes fuel and the levels are a recursion on the
natural numbers.

The evaluator is adequate to the kernel's denotation ({name}`Geb.Kernel.infer`), by a logical
relation between values and denotations defined by recursion on types: a function's value is
related to a function when its application to every value related to an argument gives, at some
level, a value related to the result. Each level's results persist at the levels above it, so
finitely many results are reached at one level. The fundamental lemma states that a term the
kernel types evaluates, in an environment related to a value of its context, to a value related to
its denotation; every application of a typed program therefore terminates at some level, which is
Tait's method for the simply typed λ-calculus with the kernel's constants \[Tait1967\].

## Main definitions

* {lit}`Val.quote`, {lit}`Val.clo`, {lit}`Val.ofList` — values.
* {lit}`spine` — a partial application's head and arguments.
* {lit}`foldVal`, {lit}`paraVal`, {lit}`iterVal`, {lit}`foldrVal`, {lit}`lcaseVal` — the
  constants' computations.
* {lit}`sat` — a constant applied to all its arguments.
* {lit}`level` — the evaluation and the application at a level of fuel.
* {lit}`eval`, {lit}`apply` — their components.
* {lit}`Rel` — the relation of values to denotations.

## Main statements

* {lit}`level_le` — a level's results persist at the levels above it.
* {lit}`rel_fold`, {lit}`rel_para`, {lit}`rel_iter`, {lit}`rel_foldr`, {lit}`rel_lcase`,
  {lit}`rel_prim` — the constants are related to their denotations.
* {lit}`fundamental` — the fundamental lemma.
* {lit}`load_rel`, {lit}`eval_apply` — the definitions of a loaded program evaluate to values
  related to their globals, and the evaluator computes a global from trees to trees.

## References

* \[Tait1967\]

## Tags

bootstrap, kernel, evaluation, big-step semantics, closure, fuel, logical relation,
normalization
-/

@[expose] public section

namespace Geb.Kernel.Eval

open scoped FinEnum

/-- The label of a closure: the node of its environment, its argument's type and its body. -/
@[match_pattern] abbrev cloLabel : ℕ := 26

namespace Val

/-- The value of a tree: its quotation. -/
def quote (t : Tree) : Tree := RoseTree.node Label.quote [t]

/-- The unit value. -/
def unit : Tree := RoseTree.node Label.unit []

/-- The value of a pair. -/
def pair (a b : Tree) : Tree := RoseTree.node Label.pair [a, b]

/-- The closure of an environment, an argument's type and a body. -/
def clo (env : List Tree) (A b : Tree) : Tree := RoseTree.node cloLabel [RoseTree.node 0 env, A, b]

/-- The application of a partial application to a value. -/
def app (f x : Tree) : Tree := RoseTree.node Label.app [f, x]

/-- The value of a list of values whose elements have the type {lit}`A`: the kernel's list
nodes over the empty list at {lit}`A`. -/
def ofList (A : Tree) (vs : List Tree) : Tree :=
  vs.foldr (fun x acc ↦ RoseTree.node Label.cons [x, acc]) (RoseTree.node Label.nil [A])

end Val

/-- The tree a value quotes, if it is a quotation. -/
def unquote (v : Tree) : Option Tree :=
  match v.label, v.children with
  | Label.quote, [t] => some t
  | _, _ => none

/-- The elements of a list value, if it is one. -/
def listOf : Tree → Option (List Tree) :=
  RoseTree.para fun l rs ↦
    match l, rs with
    | Label.nil, [_] => some []
    | Label.cons, [(x, _), (_, r)] => r.map (x :: ·)
    | _, _ => none

/-- A partial application's head and its arguments, the first first. -/
def spine : Tree → Tree × List Tree :=
  RoseTree.para fun l rs ↦
    match l, rs with
    | Label.app, [(_, r), (x, _)] => (r.1, r.2 ++ [x])
    | _, _ => (RoseTree.node l (rs.map Prod.fst), [])

/-- The number of arguments a primitive takes. -/
def primArity (k : ℕ) : ℕ :=
  if k = Prim.label ∨ k = Prim.arity ∨ k = Prim.children ∨ k = Prim.log2 then 1
  else if k < 14 then 2 else 0

/-- The number of arguments a constant takes, and zero at a tree that is not a constant. -/
def arity (h : Tree) : ℕ :=
  match h.label, h.children with
  | Label.fold, [_] | Label.para, [_] => 2
  | Label.iter, [_] | Label.foldr, [_, _] | Label.lcase, [_, _] => 3
  | Label.prim, [k] => primArity k.label
  | _, _ => 0

/-- A primitive applied to the trees its arguments quote. -/
def primApply (k : ℕ) (args : List Tree) : Option Tree := do
  let ts ← args.mapM unquote
  match ts with
  | [a] =>
    if k = Prim.label then some (Val.quote (Const.label a))
    else if k = Prim.arity then some (Val.quote (Const.arity a))
    else if k = Prim.children then some (Val.ofList tT (a.children.map Val.quote))
    else if k = Prim.log2 then some (Val.quote (Const.log2 a))
    else none
  | [a, b] =>
    if k = Prim.child then some (Val.quote (Const.child a b))
    else if k = Prim.add then some (Val.quote (Const.add a b))
    else if k = Prim.sub then some (Val.quote (Const.sub a b))
    else if k = Prim.mul then some (Val.quote (Const.mul a b))
    else if k = Prim.div then some (Val.quote (Const.div a b))
    else if k = Prim.mod then some (Val.quote (Const.mod a b))
    else if k = Prim.eq then some (Val.quote (Const.eq a b))
    else if k = Prim.lt then some (Val.quote (Const.lt a b))
    else if k = Prim.equal then some (Val.quote (Const.equal a b))
    else none
  | _ => none

/-- The node primitive applied to the value of a label and a list value of children. -/
def primNode (l cs : Tree) : Option Tree := do
  let a ← unquote l
  let vs ← listOf cs
  let ts ← vs.mapM unquote
  some (Val.quote (Const.node a ts))

/-- The fold of a tree at the result type {lit}`A` by a step value: a node's result is the step
applied to its label's value and to the list value of its children's results. -/
def foldVal (ap : Tree → Tree → Option Tree) (A f : Tree) : Tree → Option Tree :=
  RoseTree.elim fun l rs ↦ do
    let vs ← rs.mapM id
    let g ← ap f (Val.quote (leaf l))
    ap g (Val.ofList A vs)

/-- The fold of a tree whose step sees the node itself, at the result type {lit}`A`. -/
def paraVal (ap : Tree → Tree → Option Tree) (A f : Tree) : Tree → Option Tree :=
  RoseTree.para fun l ps ↦ do
    let vs ← (ps.map Prod.snd).mapM id
    let g ← ap f (Val.quote (RoseTree.node l (ps.map Prod.fst)))
    ap g (Val.ofList A vs)

/-- A step value applied a number of times to a value. -/
def iterVal (ap : Tree → Tree → Option Tree) (s z : Tree) (n : ℕ) : Option Tree :=
  Nat.repeat (fun acc ↦ acc.bind (ap s)) n (some z)

/-- The right fold of a list of values by a step value. -/
def foldrVal (ap : Tree → Tree → Option Tree) (g z : Tree) (vs : List Tree) : Option Tree :=
  vs.foldr (fun x acc ↦ acc.bind fun a ↦ (ap g x).bind fun g' ↦ ap g' a) (some z)

/-- Case analysis of a list value: the value for the empty list, or the function's value applied
to the head and the tail. -/
def lcaseVal (ap : Tree → Tree → Option Tree) (xs n c : Tree) : Option Tree :=
  match xs.label, xs.children with
  | Label.nil, [_] => some n
  | Label.cons, [x, r] => (ap c x).bind fun g ↦ ap g r
  | _, _ => none

/-- A constant applied to all its arguments, applying values to values by {lit}`ap`: the
constant's label, number of children and number of arguments select its computation. -/
def sat (ap : Tree → Tree → Option Tree) (h : Tree) (args : List Tree) : Option Tree :=
  let l := h.label
  let n := h.children.length
  let k := args.length
  let a₀ := args.getD 0 (leaf 0)
  let a₁ := args.getD 1 (leaf 0)
  let a₂ := args.getD 2 (leaf 0)
  let c₀ := h.children.getD 0 (leaf 0)
  if l = Label.fold ∧ n = 1 ∧ k = 2 then (unquote a₁).bind (foldVal ap c₀ a₀)
  else if l = Label.para ∧ n = 1 ∧ k = 2 then (unquote a₁).bind (paraVal ap c₀ a₀)
  else if l = Label.iter ∧ n = 1 ∧ k = 3 then
    (unquote a₂).bind fun n₀ ↦ iterVal ap a₀ a₁ n₀.label
  else if l = Label.foldr ∧ n = 2 ∧ k = 3 then (listOf a₂).bind (foldrVal ap a₀ a₁)
  else if l = Label.lcase ∧ n = 2 ∧ k = 3 then lcaseVal ap a₀ a₁ a₂
  else if l = Label.prim ∧ n = 1 ∧ k = 2 then
    if c₀.label = Prim.node then primNode a₀ a₁ else primApply c₀.label args
  else if l = Label.prim ∧ n = 1 ∧ k = 1 then primApply c₀.label args
  else none

/-- The evaluation of a term in an environment and the application of a value to a value. -/
abbrev Fns : Type := (List Tree → Tree → Option Tree) × (Tree → Tree → Option Tree)

/-- The evaluation at a level of a node of a term in an environment, from its label and its
children with their evaluations, applying values by the application below and evaluating a
reference's definition, among the program's definitions, by the evaluation below. -/
def evStep (G : List Tree) (p : Fns) (l : ℕ)
    (rs : List (Tree × (List Tree → Option Tree))) (env : List Tree) : Option Tree :=
  match l, rs with
  | Label.var, [(n, _)] => env[n.label]?
  | Label.lam, [(A, _), (b, _)] => some (Val.clo env A b)
  | Label.app, [(_, f), (_, x)] => do
    let vf ← f env
    let vx ← x env
    p.2 vf vx
  | Label.unit, [] => some Val.unit
  | Label.pair, [(_, a), (_, b)] => do
    let va ← a env
    let vb ← b env
    some (Val.pair va vb)
  | Label.fst, [(_, p)] => do
    let vp ← p env
    match vp.label, vp.children with
    | Label.pair, [a, _] => some a
    | _, _ => none
  | Label.snd, [(_, p)] => do
    let vp ← p env
    match vp.label, vp.children with
    | Label.pair, [_, b] => some b
    | _, _ => none
  | Label.quote, [(t, _)] => some (Val.quote t)
  | Label.cond, [(_, c), (_, a), (_, b)] => do
    let vc ← c env
    let t ← unquote vc
    if t.label ≠ 0 then a env else b env
  | Label.nil, [(A, _)] => some (RoseTree.node Label.nil [A])
  | Label.cons, [(_, x), (_, xs)] => do
    let vx ← x env
    let vxs ← xs env
    some (RoseTree.node Label.cons [vx, vxs])
  | Label.fold, [(A, _)] => some (RoseTree.node Label.fold [A])
  | Label.para, [(A, _)] => some (RoseTree.node Label.para [A])
  | Label.iter, [(A, _)] => some (RoseTree.node Label.iter [A])
  | Label.foldr, [(A, _), (B, _)] => some (RoseTree.node Label.foldr [A, B])
  | Label.lcase, [(A, _), (B, _)] => some (RoseTree.node Label.lcase [A, B])
  | Label.prim, [(k, _)] => some (RoseTree.node Label.prim [leaf k.label])
  | Label.ref, [(n, _)] => G[n.label]?.bind (p.1 [])
  | _, _ => none

/-- The application at a level of a value to a value, by the functions of the level below: a
closure evaluates its body in its environment extended by the argument, and a constant collects
its arguments until it has all of them. -/
def apStep (p : Fns) (f x : Tree) : Option Tree :=
  match f.label, f.children with
  | Label.app, _ | Label.fold, _ | Label.para, _ | Label.iter, _ | Label.foldr, _
  | Label.lcase, _ | Label.prim, _ =>
    let s := spine f
    let args := s.2 ++ [x]
    if args.length < arity s.1 then some (Val.app f x) else sat p.2 s.1 args
  | cloLabel, [env, _, b] => p.1 (x :: env.children) b
  | _, _ => none

/-- The functions of the level above, from those of a level. -/
def next (G : List Tree) (p : Fns) : Fns :=
  (fun env t ↦ RoseTree.para (evStep G p) t env, apStep p)

/-- The functions at a level of fuel, given the program's definitions; the level zero fails. -/
def level (G : List Tree) (n : ℕ) : Fns :=
  Nat.repeat (next G) n (fun _ _ ↦ none, fun _ _ ↦ none)

/-- The value of a term in an environment at a level of fuel. -/
def eval (G : List Tree) (n : ℕ) (env : List Tree) (t : Tree) : Option Tree :=
  (level G n).1 env t

/-- The application of a value to a value at a level of fuel. -/
def apply (G : List Tree) (n : ℕ) (f x : Tree) : Option Tree := (level G n).2 f x

/-! The relation of values to denotations. -/

/-- A list value and a list of denotations are related when they are related element by
element, the list value ending in the empty list. -/
def ListRel {α : Type} (R : Tree → α → Prop) (v : Tree) (ds : List α) : Prop :=
  List.rec (motive := fun _ ↦ Tree → Prop) (fun v ↦ ∃ A, v = RoseTree.node Label.nil [A])
    (fun d _ ih v ↦ ∃ x r, v = RoseTree.node Label.cons [x, r] ∧ R x d ∧ ih r) ds v

/-- The relation of a value to a denotation of a type, by recursion on the type: a tree's value
is its quotation, a pair's the pair of values related to its components, a list's a list value
related element by element, and a function's a value whose application to every value related
to an argument gives, at some level of fuel, a value related to the function's result there;
the unit value is the unit's value, and a tree that is not a type relates everything. -/
def Rel (G : List Tree) : (A : Tree) → Tree → Ty.den A → Prop :=
  WType.rec fun ⟨l, k⟩ g ih ↦
    match l, k, g, ih with
    | Label.tyTree, 0, _, _ => fun v d ↦ v = Val.quote d
    | Label.tyProd, 2, _, ih => fun v d ↦ ∃ a b, v = Val.pair a b ∧ ih 0 a d.1 ∧ ih 1 b d.2
    | Label.tyArrow, 2, _, ih => fun v f ↦
        ∀ a da, ih 0 a da → ∃ n w, apply G n v a = some w ∧ ih 1 w (f da)
    | Label.tyList, 1, _, ih => fun v ds ↦ ListRel (ih 0) v ds
    | Label.tyUnit, 0, _, _ => fun v _ ↦ v = Val.unit
    | _, _, _, _ => fun _ _ ↦ True

/-- The relation at the type of trees. -/
theorem rel_tree (G : List Tree) (v d : Tree) : Rel G tT v d ↔ v = Val.quote d := Iff.rfl

/-- The relation at a product type. -/
theorem rel_prod (G : List Tree) (A B v : Tree) (d : Ty.den A × Ty.den B) :
    Rel G (tProd A B) v d ↔ ∃ a b, v = Val.pair a b ∧ Rel G A a d.1 ∧ Rel G B b d.2 := Iff.rfl

/-- The relation at a function type. -/
theorem rel_arrow (G : List Tree) (A B v : Tree) (f : Ty.den A → Ty.den B) :
    Rel G (tArrow A B) v f ↔
      ∀ a da, Rel G A a da → ∃ n w, apply G n v a = some w ∧ Rel G B w (f da) := Iff.rfl

/-- The relation at a list type. -/
theorem rel_list (G : List Tree) (A v : Tree) (ds : List (Ty.den A)) :
    Rel G (tList A) v ds ↔ ListRel (Rel G A) v ds := Iff.rfl

/-- The relation at the unit type. -/
theorem rel_unit (G : List Tree) (v : Tree) (d : Ty.den tUnit) : Rel G tUnit v d ↔ v = Val.unit :=
  Iff.rfl

/-! Monotonicity in the fuel. -/

/-- One optional result refines another: when the first is present, the second is the same. -/
def Refines {α : Type} (o o' : Option α) : Prop := ∀ v, o = some v → o' = some v

/-- Refinement is reflexive. -/
theorem Refines.refl {α : Type} (o : Option α) : Refines o o := fun _ h ↦ h

/-- Binding refines binding, at refining arguments and continuations. -/
theorem Refines.bind {α β : Type} {o o' : Option α} {k k' : α → Option β} (ho : Refines o o')
    (hk : ∀ a, Refines (k a) (k' a)) : Refines (o.bind k) (o'.bind k') := fun v h ↦ by
  obtain ⟨a, ha, hka⟩ := Option.bind_eq_some_iff.mp h
  rw [ho a ha]
  exact hk a v hka

/-- The results of a list of refining results refine theirs. -/
theorem Refines.mapM {α : Type} {rs rs' : List (Option α)} (h : List.Forall₂ Refines rs rs') :
    Refines (rs.mapM id) (rs'.mapM id) := by
  refine List.Forall₂.rec (motive := fun rs rs' _ ↦ Refines (rs.mapM id) (rs'.mapM id))
    (Refines.refl _) (fun {r r' _ _} hr _ ih v hv ↦ ?_) h
  simp only [List.mapM_cons, id, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq] at hv ⊢
  obtain ⟨a, ha, vs, hvs, rfl⟩ := hv
  exact ⟨a, hr a ha, vs, ih vs hvs, rfl⟩

/-- A function's results refine another's at every argument. -/
def RefinesFn {α β : Type} (f f' : α → Option β) : Prop := ∀ a, Refines (f a) (f' a)

/-- An application refines another when it does at every pair of values. -/
def RefinesAp (ap ap' : Tree → Tree → Option Tree) : Prop := ∀ f x, Refines (ap f x) (ap' f x)

/-- The results of a list's elements under two functions are related element by element when
they are at each element. -/
theorem forall₂_map {α β γ : Type} {R : β → γ → Prop} {f : α → β} {g : α → γ} {cs : List α}
    (h : ∀ c ∈ cs, R (f c) (g c)) : List.Forall₂ R (cs.map f) (cs.map g) :=
  List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr h))

/-- The fold refines at a refining application. -/
theorem foldVal_mono {ap ap' : Tree → Tree → Option Tree} (h : RefinesAp ap ap') (A f : Tree) :
    ∀ t, Refines (foldVal ap A f t) (foldVal ap' A f t) :=
  RoseTree.ind fun l cs ih ↦ by
    simp only [foldVal, RoseTree.elim_node]
    exact Refines.bind (Refines.mapM (forall₂_map ih)) fun vs ↦
      Refines.bind (h _ _) fun g ↦ h _ _

/-- The fold whose step sees the node refines at a refining application. -/
theorem paraVal_mono {ap ap' : Tree → Tree → Option Tree} (h : RefinesAp ap ap') (A f : Tree) :
    ∀ t, Refines (paraVal ap A f t) (paraVal ap' A f t) :=
  RoseTree.ind fun l cs ih ↦ by
    simp only [paraVal, RoseTree.para_node, List.map_map, Function.comp_def]
    exact Refines.bind (Refines.mapM (forall₂_map ih)) fun vs ↦
      Refines.bind (h _ _) fun g ↦ h _ _

/-- Iteration refines at a refining application. -/
theorem iterVal_mono {ap ap' : Tree → Tree → Option Tree} (h : RefinesAp ap ap') (s z : Tree) :
    ∀ n, Refines (iterVal ap s z n) (iterVal ap' s z n) :=
  Nat.rec (Refines.refl _) fun _ ih ↦ Refines.bind ih fun _ ↦ h _ _

/-- The right fold refines at a refining application. -/
theorem foldrVal_mono {ap ap' : Tree → Tree → Option Tree} (h : RefinesAp ap ap') (g z : Tree) :
    ∀ vs, Refines (foldrVal ap g z vs) (foldrVal ap' g z vs) :=
  List.rec (Refines.refl _) fun _ _ ih ↦
    Refines.bind ih fun _ ↦ Refines.bind (h _ _) fun _ ↦ h _ _

/-- Case analysis of lists refines at a refining application. -/
theorem lcaseVal_mono {ap ap' : Tree → Tree → Option Tree} (h : RefinesAp ap ap') (xs n c : Tree) :
    Refines (lcaseVal ap xs n c) (lcaseVal ap' xs n c) := by
  unfold lcaseVal
  split
  · exact Refines.refl _
  · exact Refines.bind (h _ _) fun _ ↦ h _ _
  · exact Refines.refl _

/-- A constant applied to its arguments refines at a refining application. -/
theorem sat_mono {ap ap' : Tree → Tree → Option Tree} (h : RefinesAp ap ap') (hd : Tree)
    (args : List Tree) : Refines (sat ap hd args) (sat ap' hd args) := by
  unfold sat
  dsimp only
  split_ifs
  · exact Refines.bind (Refines.refl _) (foldVal_mono h _ _)
  · exact Refines.bind (Refines.refl _) (paraVal_mono h _ _)
  · exact Refines.bind (Refines.refl _) fun _ ↦ iterVal_mono h _ _ _
  · exact Refines.bind (Refines.refl _) (foldrVal_mono h _ _)
  · exact lcaseVal_mono h _ _ _
  all_goals exact Refines.refl _

/-- The children of a node, paired with their results, when they are one child. -/
theorem map_pair_eq_one {β : Type} {F : Tree → β} {cs : List Tree} {x : Tree} {s : β}
    (h : cs.map (fun c ↦ (c, F c)) = [(x, s)]) : cs = [x] ∧ s = F x := by
  obtain ⟨c, _, rfl, hc, hnil⟩ := List.map_eq_cons_iff.mp h
  obtain rfl := List.map_eq_nil_iff.mp hnil
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  exact ⟨rfl, rfl⟩

/-- The children of a node, paired with their results, when they are two children. -/
theorem map_pair_eq_two {β : Type} {F : Tree → β} {cs : List Tree} {x y : Tree} {s t : β}
    (h : cs.map (fun c ↦ (c, F c)) = [(x, s), (y, t)]) : cs = [x, y] ∧ s = F x ∧ t = F y := by
  obtain ⟨c, _, rfl, hc, h'⟩ := List.map_eq_cons_iff.mp h
  obtain ⟨rfl, rfl⟩ := map_pair_eq_one h'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  exact ⟨rfl, rfl, rfl⟩

/-- The children of a node, paired with their results, when they are three children. -/
theorem map_pair_eq_three {β : Type} {F : Tree → β} {cs : List Tree} {x y z : Tree} {s t u : β}
    (h : cs.map (fun c ↦ (c, F c)) = [(x, s), (y, t), (z, u)]) :
    cs = [x, y, z] ∧ s = F x ∧ t = F y ∧ u = F z := by
  obtain ⟨c, _, rfl, hc, h'⟩ := List.map_eq_cons_iff.mp h
  obtain ⟨rfl, rfl, rfl⟩ := map_pair_eq_two h'
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hc
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The functions of one level refine another's: at every environment, term and pair of values. -/
def RefinesFns (p p' : Fns) : Prop :=
  (∀ env t, Refines (p.1 env t) (p'.1 env t)) ∧ RefinesAp p.2 p'.2

/-- The evaluation of a node by the paramorphism. -/
theorem ev_node (G : List Tree) (p : Fns) (l : ℕ) (cs : List Tree) (env : List Tree) :
    RoseTree.para (evStep G p) (RoseTree.node l cs) env =
      evStep G p l (cs.map fun c ↦ (c, RoseTree.para (evStep G p) c)) env := by
  simp only [RoseTree.para_node]

/-- A node's evaluation refines at a refining application and refining evaluations of its
children. -/
theorem evStep_mono (G : List Tree) {p p' : Fns} (h : RefinesFns p p')
    (l : ℕ) (cs : List Tree) (F F' : Tree → List Tree → Option Tree)
    (hF : ∀ c ∈ cs, ∀ env, Refines (F c env) (F' c env)) (env : List Tree) :
    Refines (evStep G p l (cs.map fun c ↦ (c, F c)) env)
      (evStep G p' l (cs.map fun c ↦ (c, F' c)) env) := by
  intro v hv
  unfold evStep at hv
  split at hv
  case h_1 n _ heq =>
    obtain ⟨rfl, -⟩ := map_pair_eq_one heq
    simpa only [List.map_cons, List.map_nil, evStep] using hv
  case h_2 A _ b _ heq =>
    obtain ⟨rfl, -, -⟩ := map_pair_eq_two heq
    simpa only [List.map_cons, List.map_nil, evStep] using hv
  case h_3 cf f cx x heq =>
    obtain ⟨rfl, rfl, rfl⟩ := map_pair_eq_two heq
    simp only [List.map_cons, List.map_nil, evStep]
    exact Refines.bind (hF cf (by simp) env) (fun _ ↦
      Refines.bind (hF cx (by simp) env) fun _ ↦ h.2 _ _) v hv
  case h_4 heq =>
    obtain rfl := List.map_eq_nil_iff.mp heq
    simpa only [List.map_nil, evStep] using hv
  case h_5 ca a cb b heq =>
    obtain ⟨rfl, rfl, rfl⟩ := map_pair_eq_two heq
    simp only [List.map_cons, List.map_nil, evStep]
    exact Refines.bind (hF ca (by simp) env) (fun _ ↦
      Refines.bind (hF cb (by simp) env) fun _ ↦ Refines.refl _) v hv
  case h_6 cp p heq =>
    obtain ⟨rfl, rfl⟩ := map_pair_eq_one heq
    simp only [List.map_cons, List.map_nil, evStep]
    exact Refines.bind (hF cp (by simp) env) (fun _ ↦ Refines.refl _) v hv
  case h_7 cp p heq =>
    obtain ⟨rfl, rfl⟩ := map_pair_eq_one heq
    simp only [List.map_cons, List.map_nil, evStep]
    exact Refines.bind (hF cp (by simp) env) (fun _ ↦ Refines.refl _) v hv
  case h_8 t _ heq =>
    obtain ⟨rfl, -⟩ := map_pair_eq_one heq
    simpa only [List.map_cons, List.map_nil, evStep] using hv
  case h_9 cc c ca a cb b heq =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := map_pair_eq_three heq
    simp only [List.map_cons, List.map_nil, evStep]
    exact Refines.bind (hF cc (by simp) env) (fun _ ↦ Refines.bind (Refines.refl _) fun _ ↦ by
      split
      · exact hF ca (by simp) env
      · exact hF cb (by simp) env) v hv
  case h_10 A _ heq =>
    obtain ⟨rfl, -⟩ := map_pair_eq_one heq
    simpa only [List.map_cons, List.map_nil, evStep] using hv
  case h_11 cx x cxs xs heq =>
    obtain ⟨rfl, rfl, rfl⟩ := map_pair_eq_two heq
    simp only [List.map_cons, List.map_nil, evStep]
    exact Refines.bind (hF cx (by simp) env) (fun _ ↦
      Refines.bind (hF cxs (by simp) env) fun _ ↦ Refines.refl _) v hv
  case h_12 A _ heq =>
    obtain ⟨rfl, -⟩ := map_pair_eq_one heq
    simpa only [List.map_cons, List.map_nil, evStep] using hv
  case h_13 A _ heq =>
    obtain ⟨rfl, -⟩ := map_pair_eq_one heq
    simpa only [List.map_cons, List.map_nil, evStep] using hv
  case h_14 A _ heq =>
    obtain ⟨rfl, -⟩ := map_pair_eq_one heq
    simpa only [List.map_cons, List.map_nil, evStep] using hv
  case h_15 A _ B _ heq =>
    obtain ⟨rfl, -, -⟩ := map_pair_eq_two heq
    simpa only [List.map_cons, List.map_nil, evStep] using hv
  case h_16 A _ B _ heq =>
    obtain ⟨rfl, -, -⟩ := map_pair_eq_two heq
    simpa only [List.map_cons, List.map_nil, evStep] using hv
  case h_17 k _ heq =>
    obtain ⟨rfl, -⟩ := map_pair_eq_one heq
    simpa only [List.map_cons, List.map_nil, evStep] using hv
  case h_18 n _ heq =>
    obtain ⟨rfl, -⟩ := map_pair_eq_one heq
    simp only [List.map_cons, List.map_nil, evStep]
    exact Refines.bind (Refines.refl _) (fun t ↦ h.1 [] t) v hv
  case h_19 => cases hv

/-- Evaluation refines at a refining application. -/
theorem ev_mono (G : List Tree) {p p' : Fns} (h : RefinesFns p p') :
    ∀ t env, Refines (RoseTree.para (evStep G p) t env) (RoseTree.para (evStep G p') t env) :=
  RoseTree.ind fun l cs ih env ↦ by
    rw [ev_node, ev_node]
    exact evStep_mono G h l cs _ _ ih env

/-- The level above refines at refining levels. -/
theorem next_mono (G : List Tree) {p p' : Fns} (h : RefinesFns p p') :
    RefinesFns (next G p) (next G p') := by
  refine ⟨fun env t ↦ ev_mono G h t env, fun f x ↦ ?_⟩
  change Refines (apStep p f x) (apStep p' f x)
  unfold apStep
  split
  all_goals first
    | exact h.1 _ _
    | exact Refines.refl _
    | (dsimp only
       split
       · exact Refines.refl _
       · exact sat_mono h.2 _ _)

/-- Each level refines the next. -/
theorem level_succ (G : List Tree) : ∀ n, RefinesFns (level G n) (level G (n + 1)) :=
  Nat.rec (motive := fun n ↦ RefinesFns (level G n) (level G (n + 1)))
    ⟨fun _ _ _ h ↦ by simp [level, Nat.repeat] at h,
      fun _ _ _ h ↦ by simp [level, Nat.repeat] at h⟩
    fun _ ih ↦ next_mono G ih

/-- Refinement of levels is transitive. -/
theorem RefinesFns.trans {p q r : Fns} (h₁ : RefinesFns p q) (h₂ : RefinesFns q r) :
    RefinesFns p r :=
  ⟨fun env t v hv ↦ h₂.1 env t v (h₁.1 env t v hv), fun f x v hv ↦ h₂.2 f x v (h₁.2 f x v hv)⟩

/-- Each level refines every level above it. -/
theorem level_le (G : List Tree) {n m : ℕ} (h : n ≤ m) : RefinesFns (level G n) (level G m) :=
  Nat.le_induction ⟨fun _ _ _ hv ↦ hv, fun _ _ _ hv ↦ hv⟩
    (fun _ _ ih ↦ ih.trans (level_succ G _)) m h

/-- An evaluation at a level gives the same value at every level above it. -/
theorem eval_le {G : List Tree} {n m : ℕ} (h : n ≤ m) {env : List Tree} {t v : Tree}
    (hv : eval G n env t = some v) : eval G m env t = some v :=
  (level_le G h).1 env t v hv

/-- An application at a level gives the same value at every level above it. -/
theorem apply_le {G : List Tree} {n m : ℕ} (h : n ≤ m) {f x v : Tree}
    (hv : apply G n f x = some v) : apply G m f x = some v :=
  (level_le G h).2 f x v hv

/-! The relation of environments, lists and bounds on the fuel. -/

/-- An environment and a value of a context's denotation are related when they are related
variable by variable. -/
def RelEnv (G : List Tree) (Γ : Ctx) (env : List Tree) (e : Γ.den) : Prop :=
  List.rec (motive := fun Γ : Ctx ↦ List Tree → Ctx.den Γ → Prop) (fun env _ ↦ env = [])
    (fun A _ ih env e ↦ ∃ v env', env = v :: env' ∧ Rel G A v e.1 ∧ ih env' e.2) Γ env e

/-- A variable's value in a related environment is related to its denotation. -/
theorem relEnv_var (G : List Tree) :
    ∀ (Γ : Ctx) (i : ℕ) (A : Tree) (f : Γ.den → Ty.den A), Ctx.var Γ i = some ⟨A, f⟩ →
      ∀ env e, RelEnv G Γ env e → ∃ v, env[i]? = some v ∧ Rel G A v (f e) := by
  refine List.rec (fun _ _ _ h ↦ by simp [Ctx.var] at h) fun B Γ ih i A f h env e he ↦ ?_
  rcases i with _ | j
  · change some (⟨B, Prod.fst⟩ : Meaning (B :: Γ)) = some ⟨A, f⟩ at h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp (Option.some.inj h)
    obtain rfl := eq_of_heq h
    obtain ⟨v, env', rfl, hv, -⟩ := he
    exact ⟨v, rfl, hv⟩
  · change Option.map (fun p : Meaning Γ ↦ (⟨p.1, p.2 ∘ Prod.snd⟩ : Meaning (B :: Γ)))
      (Ctx.var Γ j) = some ⟨A, f⟩ at h
    obtain ⟨⟨A', f'⟩, hj, hp⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨rfl, hp⟩ := Sigma.mk.inj_iff.mp hp
    obtain rfl := eq_of_heq hp
    obtain ⟨v, env', rfl, -, he'⟩ := he
    obtain ⟨w, hw, hrel⟩ := ih j A' f' hj env' e.2 he'
    exact ⟨w, by simpa using hw, hrel⟩

/-- A property that holds at some level for each element of a list, and at every level above
one where it holds, holds at one level for every element. -/
theorem exists_bound {α : Type} {P : ℕ → α → Prop} (hP : ∀ {n m} a, n ≤ m → P n a → P m a) :
    ∀ xs : List α, (∀ x ∈ xs, ∃ n, P n x) → ∃ n, ∀ x ∈ xs, P n x :=
  List.rec (fun _ ↦ ⟨0, fun _ h ↦ by cases h⟩) fun x xs ih h ↦ by
    obtain ⟨n, hn⟩ := h x List.mem_cons_self
    obtain ⟨m, hm⟩ := ih fun y hy ↦ h y (List.mem_cons_of_mem x hy)
    refine ⟨max n m, fun y hy ↦ ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hP y (le_max_left n m) hn
    · exact hP y (le_max_right n m) (hm y hy)

/-- The list value of values related element by element is related to their list. -/
theorem listRel_ofList {α : Type} {R : Tree → α → Prop} (A : Tree) {vs : List Tree}
    {ds : List α} (h : List.Forall₂ R vs ds) : ListRel R (Val.ofList A vs) ds :=
  List.Forall₂.rec (motive := fun vs ds _ ↦ ListRel R (Val.ofList A vs) ds) ⟨A, rfl⟩
    (fun {v _ _ _} hv _ ih ↦ ⟨v, _, rfl, hv, ih⟩) h

/-- The elements of a list value related to a list are related to its elements. -/
theorem listOf_of_listRel {α : Type} {R : Tree → α → Prop} :
    ∀ (ds : List α) (v : Tree), ListRel R v ds →
      ∃ vs, listOf v = some vs ∧ List.Forall₂ R vs ds :=
  List.rec (fun v ⟨A, h⟩ ↦ ⟨[], by subst h; simp [listOf], .nil⟩) fun _ ds ih v h ↦ by
    obtain ⟨x, r, rfl, hx, hr⟩ := h
    obtain ⟨vs, hvs, h₂⟩ := ih r hr
    refine ⟨x :: vs, ?_, .cons hx h₂⟩
    simp only [listOf, RoseTree.para_node, List.map_cons, List.map_nil] at hvs ⊢
    rw [hvs]
    rfl

/-! One step of application and of evaluation. -/

/-- The application at the level above a level. -/
theorem apply_succ (G : List Tree) (n : ℕ) (f x : Tree) :
    apply G (n + 1) f x = apStep (level G n) f x := rfl

/-- The evaluation at the level above a level. -/
theorem eval_succ (G : List Tree) (n : ℕ) (env : List Tree) (t : Tree) :
    eval G (n + 1) env t = RoseTree.para (evStep G (level G n)) t env := rfl

/-- A tree that is not an application is its own spine, with no arguments. -/
theorem spine_node {l : ℕ} (hl : l ≠ Label.app) (cs : List Tree) :
    spine (RoseTree.node l cs) = (RoseTree.node l cs, []) := by
  simp only [spine, RoseTree.para_node]
  split
  · exact absurd rfl hl
  · simp [List.map_map, Function.comp_def]

/-- The spine of a partial application to a value. -/
theorem spine_app (f x : Tree) : spine (Val.app f x) = ((spine f).1, (spine f).2 ++ [x]) := by
  simp only [Val.app, spine, RoseTree.para_node, List.map_cons, List.map_nil]

/-- The results of functions at a list's elements, when each is present and related to a value
of another function, are present together and related element by element. -/
theorem mapM_of_forall {α β : Type} {R : Tree → β → Prop} {F : α → Option Tree} {D : α → β}
    {cs : List α} (h : ∀ c ∈ cs, ∃ w, F c = some w ∧ R w (D c)) :
    ∃ ws, (cs.map F).mapM id = some ws ∧ List.Forall₂ R ws (cs.map D) := by
  refine List.rec (motive := fun cs ↦ (∀ c ∈ cs, ∃ w, F c = some w ∧ R w (D c)) →
    ∃ ws, (cs.map F).mapM id = some ws ∧ List.Forall₂ R ws (cs.map D))
    (fun _ ↦ ⟨[], rfl, .nil⟩) (fun c cs ih h ↦ ?_) cs h
  obtain ⟨w, hw, hr⟩ := h c List.mem_cons_self
  obtain ⟨ws, hws, h₂⟩ := ih fun d hd ↦ h d (List.mem_cons_of_mem c hd)
  refine ⟨w :: ws, ?_, .cons hr h₂⟩
  simp only [List.map_cons, List.mapM_cons, id, hw, hws, Option.bind_eq_bind, Option.bind_some,
    Option.pure_def]

/-! The constants. -/

/-- The application at the level above a level of a value whose label is a constant's or an
application's: the constant's arguments collected, or the constant applied to all of them. -/
theorem apply_partial (G : List Tree) (n : ℕ) {f : Tree}
    (hf : f.label ∈ [Label.app, Label.fold, Label.para, Label.iter, Label.foldr, Label.lcase,
      Label.prim]) (x : Tree) :
    apply G (n + 1) f x =
      if ((spine f).2 ++ [x]).length < arity (spine f).1 then some (Val.app f x)
      else sat (apply G n) (spine f).1 ((spine f).2 ++ [x]) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rw [apply_succ]
  unfold apStep
  rcases hf with h | h | h | h | h | h | h <;> simp only [h] <;> rfl

/-- The fold computes at a step related to a step: its value at every tree, at some level, is
related to the fold's denotation there. -/
theorem foldVal_rel (G : List Tree) (A f : Tree) (df : Ty.den (tArrow tT (tArrow (tList A) A)))
    (hf : Rel G (tArrow tT (tArrow (tList A) A)) f df) :
    ∀ t, ∃ n w, foldVal (apply G n) A f t = some w ∧ Rel G A w (Const.fold df t) := by
  refine RoseTree.ind fun l cs ih ↦ ?_
  obtain ⟨N, hN⟩ := exists_bound
    (P := fun n c ↦ ∃ w, foldVal (apply G n) A f c = some w ∧ Rel G A w (Const.fold df c))
    (fun c hnm ⟨w, hw, hr⟩ ↦
      ⟨w, foldVal_mono (fun _ _ ↦ (level_le G hnm).2 _ _) A f c w hw, hr⟩) cs
    (fun c hc ↦ (ih c hc).imp fun _ h ↦ h)
  obtain ⟨ws, hws, h₂⟩ := mapM_of_forall hN
  obtain ⟨n₁, g, hg, hgr⟩ := hf (Val.quote (leaf l)) (leaf l) rfl
  obtain ⟨n₂, w, hw, hwr⟩ := hgr _ _ (listRel_ofList A h₂)
  refine ⟨max N (max n₁ n₂), w, ?_, ?_⟩
  · simp only [foldVal, RoseTree.elim_node]
    have hws' : (cs.map (foldVal (apply G (max N (max n₁ n₂))) A f)).mapM id = some ws :=
      Refines.mapM (forall₂_map fun c _ ↦
        foldVal_mono (fun _ _ ↦ (level_le G (le_max_left N (max n₁ n₂))).2 _ _) A f c) ws hws
    rw [show (cs.map fun c ↦ RoseTree.elim _ c) = cs.map (foldVal (apply G (max N (max n₁ n₂))) A f)
      from rfl, hws']
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [apply_le (le_trans (le_max_left n₁ n₂) (le_max_right N _)) hg]
    exact apply_le (le_trans (le_max_right n₁ n₂) (le_max_right N _)) hw
  · refine (congrArg (Rel G A w) ?_).mpr hwr
    exact RoseTree.elim_node _ l cs

/-- The arity of the fold. -/
theorem arity_fold (A : Tree) : arity (RoseTree.node Label.fold [A]) = 2 := by
  simp [arity]

/-- The fold is related to its denotation. -/
theorem rel_fold (G : List Tree) (A : Tree) :
    Rel G (foldTy A) (RoseTree.node Label.fold [A]) (foldDen A) := by
  refine (rel_arrow G _ _ _ _).mpr fun f df hf ↦
    ⟨1, Val.app (RoseTree.node Label.fold [A]) f, ?_, ?_⟩
  · rw [apply_partial G 0 (by simp) f, spine_node (by decide)]
    simp [arity_fold]
  · refine (rel_arrow G _ _ _ _).mpr fun t dt ht ↦ ?_
    obtain rfl := (rel_tree G t dt).mp ht
    obtain ⟨n, w, hw, hr⟩ := foldVal_rel G A f df hf dt
    refine ⟨n + 1, w, ?_, hr⟩
    rw [apply_partial G n (by simp [Val.app]) _, spine_app, spine_node (by decide)]
    simp only [List.nil_append, List.singleton_append, List.length_cons, arity_fold]
    exact hw

/-- The fold whose step sees the node computes at a step related to a step. -/
theorem paraVal_rel (G : List Tree) (A f : Tree) (df : Ty.den (tArrow tT (tArrow (tList A) A)))
    (hf : Rel G (tArrow tT (tArrow (tList A) A)) f df) :
    ∀ t, ∃ n w, paraVal (apply G n) A f t = some w ∧ Rel G A w (Const.para df t) := by
  refine RoseTree.ind fun l cs ih ↦ ?_
  obtain ⟨N, hN⟩ := exists_bound
    (P := fun n c ↦ ∃ w, paraVal (apply G n) A f c = some w ∧ Rel G A w (Const.para df c))
    (fun c hnm ⟨w, hw, hr⟩ ↦
      ⟨w, paraVal_mono (fun _ _ ↦ (level_le G hnm).2 _ _) A f c w hw, hr⟩) cs
    (fun c hc ↦ (ih c hc).imp fun _ h ↦ h)
  obtain ⟨ws, hws, h₂⟩ := mapM_of_forall hN
  obtain ⟨n₁, g, hg, hgr⟩ := hf (Val.quote (RoseTree.node l cs)) (RoseTree.node l cs) rfl
  obtain ⟨n₂, w, hw, hwr⟩ := hgr _ _ (listRel_ofList A h₂)
  refine ⟨max N (max n₁ n₂), w, ?_, ?_⟩
  · simp only [paraVal, RoseTree.para_node, List.map_map, Function.comp_def, List.map_id']
    have hws' : (cs.map (paraVal (apply G (max N (max n₁ n₂))) A f)).mapM id = some ws :=
      Refines.mapM (forall₂_map fun c _ ↦
        paraVal_mono (fun _ _ ↦ (level_le G (le_max_left N (max n₁ n₂))).2 _ _) A f c) ws hws
    rw [show (cs.map fun c ↦ RoseTree.para _ c) = cs.map (paraVal (apply G (max N (max n₁ n₂))) A f)
      from rfl, hws']
    simp only [Option.bind_eq_bind, Option.bind_some]
    rw [apply_le (le_trans (le_max_left n₁ n₂) (le_max_right N _)) hg]
    exact apply_le (le_trans (le_max_right n₁ n₂) (le_max_right N _)) hw
  · refine (congrArg (Rel G A w) ?_).mpr hwr
    exact Const.para_node _ l cs

/-- The arity of the fold whose step sees the node. -/
theorem arity_para (A : Tree) : arity (RoseTree.node Label.para [A]) = 2 := by
  simp [arity]

/-- The fold whose step sees the node is related to its denotation. -/
theorem rel_para (G : List Tree) (A : Tree) :
    Rel G (foldTy A) (RoseTree.node Label.para [A]) (paraDen A) := by
  refine (rel_arrow G _ _ _ _).mpr fun f df hf ↦
    ⟨1, Val.app (RoseTree.node Label.para [A]) f, ?_, ?_⟩
  · rw [apply_partial G 0 (by simp) f, spine_node (by decide)]
    simp [arity_para]
  · refine (rel_arrow G _ _ _ _).mpr fun t dt ht ↦ ?_
    obtain rfl := (rel_tree G t dt).mp ht
    obtain ⟨n, w, hw, hr⟩ := paraVal_rel G A f df hf dt
    refine ⟨n + 1, w, ?_, hr⟩
    rw [apply_partial G n (by simp [Val.app]) _, spine_app, spine_node (by decide)]
    simp only [List.nil_append, List.singleton_append, List.length_cons, arity_para]
    exact hw

/-- A constant of three arguments applied to its first two collects them. -/
theorem apply_two {G : List Tree} {h : Tree} (hl : h.label ≠ Label.app)
    (hlab : h.label ∈ [Label.app, Label.fold, Label.para, Label.iter, Label.foldr, Label.lcase,
      Label.prim]) (ha : arity h = 3) (a b : Tree) :
    apply G 1 h a = some (Val.app h a) ∧
      apply G 1 (Val.app h a) b = some (Val.app (Val.app h a) b) := by
  have hs : spine h = (h, []) := by
    rw [← RoseTree.node_label_children h] at hl ⊢
    exact spine_node hl _
  refine ⟨?_, ?_⟩
  · rw [apply_partial G 0 hlab, hs]
    simp [ha]
  · rw [apply_partial G 0 (by simp [Val.app]), spine_app, hs]
    simp [ha]

/-- Iteration computes at a step related to a step and a start related to a start. -/
theorem iterVal_rel (G : List Tree) (A s z : Tree) (ds : Ty.den (tArrow A A)) (dz : Ty.den A)
    (hs : Rel G (tArrow A A) s ds) (hz : Rel G A z dz) :
    ∀ k, ∃ n w, iterVal (apply G n) s z k = some w ∧ Rel G A w (Nat.repeat ds k dz) :=
  Nat.rec ⟨0, z, rfl, hz⟩ fun k ⟨n₁, w₁, hw₁, hr₁⟩ ↦ by
    obtain ⟨n₂, w₂, hw₂, hr₂⟩ := hs w₁ _ hr₁
    refine ⟨max n₁ n₂, w₂, ?_, hr₂⟩
    change (iterVal (apply G (max n₁ n₂)) s z k).bind (apply G (max n₁ n₂) s) = some w₂
    have hw₁' : iterVal (apply G (max n₁ n₂)) s z k = some w₁ :=
      iterVal_mono (fun _ _ ↦ (level_le G (le_max_left n₁ n₂)).2 _ _) s z k w₁ hw₁
    rw [hw₁', Option.bind_some]
    exact apply_le (le_max_right n₁ n₂) hw₂

/-- Iteration is related to its denotation. -/
theorem rel_iter (G : List Tree) (A : Tree) :
    Rel G (iterTy A) (RoseTree.node Label.iter [A]) (iterDen A) := by
  have ha : arity (RoseTree.node Label.iter [A]) = 3 := by simp [arity]
  have h₁ := fun a b ↦ apply_two (G := G) (h := RoseTree.node Label.iter [A])
    (by simp only [RoseTree.label_node]; decide) (by simp) ha a b
  refine (rel_arrow G _ _ _ _).mpr fun s ds hs ↦ ⟨1, _, (h₁ s s).1, ?_⟩
  refine (rel_arrow G _ _ _ _).mpr fun z dz hz ↦ ⟨1, _, (h₁ s z).2, ?_⟩
  refine (rel_arrow G _ _ _ _).mpr fun t dt ht ↦ ?_
  obtain rfl := (rel_tree G t dt).mp ht
  obtain ⟨n, w, hw, hr⟩ := iterVal_rel G A s z ds dz hs hz dt.label
  refine ⟨n + 1, w, ?_, hr⟩
  rw [apply_partial G n (by simp [Val.app]) _, spine_app, spine_app, spine_node (by decide)]
  simp only [List.nil_append, List.cons_append, List.length_cons, ha]
  exact hw

/-- The right fold computes at a step related to a step and a start related to a start. -/
theorem foldrVal_rel (G : List Tree) (A B g z : Tree) (dg : Ty.den (tArrow A (tArrow B B)))
    (dz : Ty.den B) (hg : Rel G (tArrow A (tArrow B B)) g dg) (hz : Rel G B z dz)
    {vs : List Tree} {ds : List (Ty.den A)} (h : List.Forall₂ (Rel G A) vs ds) :
    ∃ n w, foldrVal (apply G n) g z vs = some w ∧ Rel G B w (ds.foldr dg dz) := by
  refine List.Forall₂.rec (motive := fun vs ds _ ↦
      ∃ n w, foldrVal (apply G n) g z vs = some w ∧ Rel G B w (ds.foldr dg dz))
    ⟨0, z, rfl, hz⟩ (fun {v d vs ds} hv _ ih ↦ ?_) h
  obtain ⟨n₁, w₁, hw₁, hr₁⟩ := ih
  obtain ⟨n₂, g', hg', hr₂⟩ := hg v d hv
  obtain ⟨n₃, w₂, hw₂, hr₃⟩ := hr₂ w₁ _ hr₁
  refine ⟨max n₁ (max n₂ n₃), w₂, ?_, hr₃⟩
  change (foldrVal (apply G (max n₁ (max n₂ n₃))) g z vs).bind (fun a ↦
    (apply G (max n₁ (max n₂ n₃)) g v).bind fun g' ↦ apply G (max n₁ (max n₂ n₃)) g' a) = some w₂
  have hw₁' : foldrVal (apply G (max n₁ (max n₂ n₃))) g z vs = some w₁ :=
    foldrVal_mono (fun _ _ ↦ (level_le G (le_max_left _ _)).2 _ _) g z vs w₁ hw₁
  rw [hw₁', Option.bind_some, apply_le (le_trans (le_max_left n₂ n₃) (le_max_right _ _)) hg',
    Option.bind_some]
  exact apply_le (le_trans (le_max_right n₂ n₃) (le_max_right _ _)) hw₂

/-- The right fold of lists is related to its denotation. -/
theorem rel_foldr (G : List Tree) (A B : Tree) :
    Rel G (foldrTy A B) (RoseTree.node Label.foldr [A, B]) (foldrDen A B) := by
  have ha : arity (RoseTree.node Label.foldr [A, B]) = 3 := by simp [arity]
  have h₁ := fun a b ↦ apply_two (G := G) (h := RoseTree.node Label.foldr [A, B])
    (by simp only [RoseTree.label_node]; decide) (by simp) ha a b
  refine (rel_arrow G _ _ _ _).mpr fun g dg hg ↦ ⟨1, _, (h₁ g g).1, ?_⟩
  refine (rel_arrow G _ _ _ _).mpr fun z dz hz ↦ ⟨1, _, (h₁ g z).2, ?_⟩
  refine (rel_arrow G _ _ _ _).mpr fun xs dxs hxs ↦ ?_
  obtain ⟨vs, hvs, h₂⟩ := listOf_of_listRel dxs xs ((rel_list G A xs dxs).mp hxs)
  obtain ⟨n, w, hw, hr⟩ := foldrVal_rel G A B g z dg dz hg hz h₂
  refine ⟨n + 1, w, ?_, hr⟩
  rw [apply_partial G n (by simp [Val.app]) _, spine_app, spine_app, spine_node (by decide)]
  simp only [List.nil_append, List.cons_append, List.length_cons, ha]
  change (listOf xs).bind (foldrVal (apply G n) g z) = some w
  rw [hvs, Option.bind_some]
  exact hw

/-- Case analysis of lists is related to its denotation. -/
theorem rel_lcase (G : List Tree) (A B : Tree) :
    Rel G (lcaseTy A B) (RoseTree.node Label.lcase [A, B]) (lcaseDen A B) := by
  have ha : arity (RoseTree.node Label.lcase [A, B]) = 3 := by simp [arity]
  have h₁ := fun a b ↦ apply_two (G := G) (h := RoseTree.node Label.lcase [A, B])
    (by simp only [RoseTree.label_node]; decide) (by simp) ha a b
  refine (rel_arrow G _ _ _ _).mpr fun xs dxs hxs ↦ ⟨1, _, (h₁ xs xs).1, ?_⟩
  refine (rel_arrow G _ _ _ _).mpr fun nv dn hn ↦ ⟨1, _, (h₁ xs nv).2, ?_⟩
  refine (rel_arrow G _ _ _ _).mpr fun c dc hc ↦ ?_
  have hsat : ∀ n, apply G (n + 1) (Val.app (Val.app (RoseTree.node Label.lcase [A, B]) xs) nv) c =
      lcaseVal (apply G n) xs nv c := fun n ↦ by
    rw [apply_partial G n (by simp [Val.app]) _, spine_app, spine_app, spine_node (by decide)]
    simp only [List.nil_append, List.cons_append, List.length_cons, ha]
    rfl
  rcases dxs with _ | ⟨d, ds⟩
  · obtain ⟨A', rfl⟩ := (rel_list G A xs []).mp hxs
    exact ⟨1, nv, by rw [hsat]; simp [lcaseVal], hn⟩
  · obtain ⟨x, r, rfl, hx, hr⟩ := (rel_list G A xs (d :: ds)).mp hxs
    obtain ⟨n₁, g, hg, hgr⟩ := hc x d hx
    obtain ⟨n₂, w, hw, hwr⟩ := hgr r ds hr
    refine ⟨max n₁ n₂ + 1, w, ?_, hwr⟩
    rw [hsat]
    simp only [lcaseVal, RoseTree.label_node, RoseTree.children_node]
    rw [apply_le (le_max_left n₁ n₂) hg, Option.bind_some]
    exact apply_le (le_max_right n₁ n₂) hw

/-- A primitive of one argument, computing a function of the tree its argument quotes, is related
to that function. -/
theorem rel_prim1 (G : List Tree) (k : ℕ) (hk : primArity k = 1) (F : Tree → Tree)
    (hF : ∀ d, sat (apply G 0) (RoseTree.node Label.prim [leaf k]) [Val.quote d] =
      some (Val.quote (F d))) :
    Rel G (tArrow tT tT) (RoseTree.node Label.prim [leaf k]) F := by
  refine (rel_arrow G _ _ _ _).mpr fun a da ha ↦ ⟨1, Val.quote (F da), ?_, rfl⟩
  obtain rfl := (rel_tree G a da).mp ha
  rw [apply_partial G 0 (by simp) _, spine_node (by decide)]
  have har : arity (RoseTree.node Label.prim [leaf k]) = 1 := hk
  simp only [List.nil_append, List.length_singleton, har, Nat.lt_irrefl, ↓reduceIte]
  exact hF da

/-- A primitive of two arguments, computing a function of the trees its arguments quote, is
related to that function. -/
theorem rel_prim2 (G : List Tree) (k : ℕ) (hk : primArity k = 2) (F : Tree → Tree → Tree)
    (hF : ∀ a b, sat (apply G 0) (RoseTree.node Label.prim [leaf k]) [Val.quote a, Val.quote b] =
      some (Val.quote (F a b))) :
    Rel G (tArrow tT (tArrow tT tT)) (RoseTree.node Label.prim [leaf k]) F := by
  have har : arity (RoseTree.node Label.prim [leaf k]) = 2 := hk
  refine (rel_arrow G _ _ _ _).mpr fun a da ha ↦
    ⟨1, Val.app (RoseTree.node Label.prim [leaf k]) a, ?_, ?_⟩
  · rw [apply_partial G 0 (by simp) _, spine_node (by decide)]
    simp [har]
  · refine (rel_arrow G _ _ _ _).mpr fun b db hb ↦ ⟨1, Val.quote (F da db), ?_, rfl⟩
    obtain rfl := (rel_tree G a da).mp ha
    obtain rfl := (rel_tree G b db).mp hb
    rw [apply_partial G 0 (by simp [Val.app]) _, spine_app, spine_node (by decide)]
    simp only [List.nil_append, List.singleton_append, List.length_cons, List.length_nil, har,
      Nat.lt_irrefl, ↓reduceIte]
    exact hF da db

/-- The trees a list of quotations quotes. -/
theorem mapM_unquote {vs ds : List Tree} (h : List.Forall₂ (fun v d ↦ v = Val.quote d) vs ds) :
    vs.mapM unquote = some ds :=
  List.Forall₂.rec (motive := fun vs ds _ ↦ vs.mapM unquote = some ds) rfl
    (fun {v d _ _} hv _ ih ↦ by
      subst hv
      simp only [List.mapM_cons, ih, Option.bind_eq_bind, Option.bind_some, Option.pure_def]
      rfl) h

/-- The list of a tree's children is related to the value of the list of their quotations. -/
theorem rel_children (G : List Tree) :
    Rel G (tArrow tT (tList tT)) (RoseTree.node Label.prim [leaf Prim.children])
      Const.children := by
  refine (rel_arrow G _ _ _ _).mpr fun a da ha ↦
    ⟨1, Val.ofList tT (da.children.map Val.quote), ?_, ?_⟩
  · obtain rfl := (rel_tree G a da).mp ha
    rw [apply_partial G 0 (by simp) _, spine_node (by decide)]
    rfl
  · exact (rel_list G _ _ _).mpr (listRel_ofList tT
      (List.forall₂_map_left_iff.mpr (List.forall₂_same.mpr fun _ _ ↦ rfl)))

/-- The node of a label and a list of children is related to the primitive building it. -/
theorem rel_node (G : List Tree) :
    Rel G (tArrow tT (tArrow (tList tT) tT)) (RoseTree.node Label.prim [leaf Prim.node])
      Const.node := by
  have har : arity (RoseTree.node Label.prim [leaf Prim.node]) = 2 := rfl
  refine (rel_arrow G _ _ _ _).mpr fun a da ha ↦
    ⟨1, Val.app (RoseTree.node Label.prim [leaf Prim.node]) a, ?_, ?_⟩
  · rw [apply_partial G 0 (by simp) _, spine_node (by decide)]
    simp [har]
  · refine (rel_arrow G _ _ _ _).mpr fun cs dcs hcs ↦ ⟨1, Val.quote (Const.node da dcs), ?_, rfl⟩
    obtain rfl := (rel_tree G a da).mp ha
    obtain ⟨vs, hvs, h₂⟩ := listOf_of_listRel dcs cs ((rel_list G tT cs dcs).mp hcs)
    rw [apply_partial G 0 (by simp [Val.app]) _, spine_app, spine_node (by decide)]
    simp only [List.nil_append, List.singleton_append, List.length_cons, List.length_nil, har,
      Nat.lt_irrefl, ↓reduceIte]
    change primNode (Val.quote da) cs = _
    simp only [primNode, hvs, mapM_unquote h₂, Option.bind_eq_bind, Option.bind_some]
    rfl

/-- Each primitive is related to its denotation. -/
theorem rel_prim (G : List Tree) :
    ∀ (k : ℕ) (g : Glob), prims[k]? = some g → Rel G g.1 (RoseTree.node Label.prim [leaf k]) g.2
  | 0, _, h => by cases h; exact rel_prim1 G 0 rfl Const.label fun _ ↦ rfl
  | 1, _, h => by cases h; exact rel_prim1 G 1 rfl Const.arity fun _ ↦ rfl
  | 2, _, h => by cases h; exact rel_prim2 G 2 rfl Const.child fun _ _ ↦ rfl
  | 3, _, h => by cases h; exact rel_node G
  | 4, _, h => by cases h; exact rel_children G
  | 5, _, h => by cases h; exact rel_prim2 G 5 rfl Const.add fun _ _ ↦ rfl
  | 6, _, h => by cases h; exact rel_prim2 G 6 rfl Const.sub fun _ _ ↦ rfl
  | 7, _, h => by cases h; exact rel_prim2 G 7 rfl Const.mul fun _ _ ↦ rfl
  | 8, _, h => by cases h; exact rel_prim2 G 8 rfl Const.div fun _ _ ↦ rfl
  | 9, _, h => by cases h; exact rel_prim2 G 9 rfl Const.mod fun _ _ ↦ rfl
  | 10, _, h => by cases h; exact rel_prim2 G 10 rfl Const.eq fun _ _ ↦ rfl
  | 11, _, h => by cases h; exact rel_prim2 G 11 rfl Const.lt fun _ _ ↦ rfl
  | 12, _, h => by cases h; exact rel_prim2 G 12 rfl Const.equal fun _ _ ↦ rfl
  | 13, _, h => by cases h; exact rel_prim1 G 13 rfl Const.log2 fun _ ↦ rfl
  | _ + 14, _, h => by simp [prims] at h

/-! The fundamental lemma. -/

/-- Trees are equal only with equal labels and numbers of children. -/
theorem mk_index_eq {x y : ℕ × ℕ} {g : RoseTree.Sig ℕ x → Tree} {g' : RoseTree.Sig ℕ y → Tree}
    (h : WType.mk x g = WType.mk y g') : x = y :=
  congrArg (fun t : Tree ↦ match t with | WType.mk x _ => x) h

/-- A tree the kernel reads as a function type is that function type. -/
theorem arrow?_eq {F A B : Tree} {h : Ty.den F = (Ty.den A → Ty.den B)}
    (hF : Ty.arrow? F = some ⟨A, B, h⟩) : F = tArrow A B := by
  obtain ⟨⟨a, k⟩, g⟩ := F
  by_cases hak : a = 3 ∧ k = 2
  · obtain ⟨rfl, rfl⟩ := hak
    rw [Ty.arrow?.eq_1] at hF
    cases hF
    exact congrArg (WType.mk (3, 2)) (funext fun i ↦ match i with | 0 => rfl | 1 => rfl)
  · rw [Ty.arrow?.eq_2 _ fun _ h ↦ hak (Prod.mk.inj (mk_index_eq h))] at hF
    cases hF

/-- A tree the kernel reads as a product type is that product type. -/
theorem prod?_eq {P A B : Tree} {h : Ty.den P = (Ty.den A × Ty.den B)}
    (hP : Ty.prod? P = some ⟨A, B, h⟩) : P = tProd A B := by
  obtain ⟨⟨a, k⟩, g⟩ := P
  by_cases hak : a = 2 ∧ k = 2
  · obtain ⟨rfl, rfl⟩ := hak
    rw [Ty.prod?.eq_1] at hP
    cases hP
    exact congrArg (WType.mk (2, 2)) (funext fun i ↦ match i with | 0 => rfl | 1 => rfl)
  · rw [Ty.prod?.eq_2 _ fun _ h ↦ hak (Prod.mk.inj (mk_index_eq h))] at hP
    cases hP

/-- A tree the kernel reads as a list type is that list type. -/
theorem list?_eq {L A : Tree} {h : Ty.den L = List (Ty.den A)}
    (hL : Ty.list? L = some ⟨A, h⟩) : L = tList A := by
  obtain ⟨⟨a, k⟩, g⟩ := L
  by_cases hak : a = 4 ∧ k = 1
  · obtain ⟨rfl, rfl⟩ := hak
    rw [Ty.list?.eq_1] at hL
    cases hL
    exact congrArg (WType.mk (4, 1)) (funext fun i ↦ match i with | 0 => rfl)
  · rw [Ty.list?.eq_2 _ fun _ h ↦ hak (Prod.mk.inj (mk_index_eq h))] at hL
    cases hL

/-- The evaluation at the level above a level of a node. -/
theorem eval_node (G : List Tree) (n : ℕ) (env : List Tree) (l : ℕ) (cs : List Tree) :
    eval G (n + 1) env (RoseTree.node l cs) =
      evStep G (level G n) l (cs.map fun c ↦ (c, fun env ↦ eval G (n + 1) env c)) env := by
  rw [eval_succ, ev_node]
  rfl

/-- The fundamental lemma of the relation: a term the checker-evaluator types, in an environment
related to a value of its context, evaluates at some level to a value related to its denotation
there, given definitions each of which evaluates at some level to a value related to the global
at its index. -/
theorem fundamental (G : List Tree) (GD : List Glob)
    (hG : ∀ (i : ℕ) (g : Glob), GD[i]? = some g →
      ∃ t n v, G[i]? = some t ∧ eval G n [] t = some v ∧ Rel G g.1 v g.2) :
    ∀ (t : Tree) (Γ : Ctx) (m : Meaning Γ), infer GD Γ t = some m →
      ∀ env e, RelEnv G Γ env e → ∃ n v, eval G n env t = some v ∧ Rel G m.1 v (m.2 e) := by
  refine RoseTree.ind fun l cs ih Γ m h env e he ↦ ?_
  simp only [infer, RoseTree.para_node] at h
  generalize hS : RoseTree.para inferStep = S at h
  unfold inferStep at h
  split at h <;> subst hS
  case h_1 n _ heq =>
    obtain ⟨rfl, -⟩ := map_pair_eq_one heq
    obtain ⟨A, f⟩ := m
    obtain ⟨v, hv, hr⟩ := relEnv_var G Γ n.label A f h env e he
    exact ⟨1, v, by rw [eval_node]; exact hv, hr⟩
  case h_2 A _ b _ heq =>
    obtain ⟨rfl, -, rfl⟩ := map_pair_eq_two heq
    split at h
    · obtain ⟨mb, hb, rfl⟩ := Option.map_eq_some_iff.mp h
      refine ⟨1, Val.clo env A b, by rw [eval_node]; rfl, ?_⟩
      refine (rel_arrow G _ _ _ _).mpr fun a da ha ↦ ?_
      obtain ⟨k, w, hw, hr⟩ :=
        ih b (by simp) (A :: Γ) mb hb (a :: env) (da, e) ⟨a, env, rfl, ha, he⟩
      refine ⟨k + 1, w, ?_, hr⟩
      change apStep (level G k) (Val.clo env A b) a = some w
      simp only [apStep, Val.clo, RoseTree.label_node, RoseTree.children_node]
      exact hw
    · cases h
  case h_3 cf f cx x heq =>
    obtain ⟨rfl, rfl, rfl⟩ := map_pair_eq_two heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨F, df⟩, hf, ⟨X, dx⟩, hx, ⟨A, B, hAB⟩, harr, h⟩ := h
    obtain rfl := arrow?_eq harr
    by_cases hXA : X = A
    · subst hXA
      simp only [↓reduceDIte] at h
      cases h
      obtain ⟨n₁, vf, hvf, hrf⟩ := ih cf (by simp) Γ _ hf env e he
      obtain ⟨n₂, vx, hvx, hrx⟩ := ih cx (by simp) Γ _ hx env e he
      obtain ⟨n₃, w, hw, hrw⟩ := (rel_arrow G X B vf (df e)).mp hrf vx (dx e) hrx
      refine ⟨max (max n₁ n₂) n₃ + 1, w, ?_, hrw⟩
      rw [eval_node]
      simp only [List.map_cons, List.map_nil, evStep,
        eval_le (m := max (max n₁ n₂) n₃ + 1) (by omega) hvf,
        eval_le (m := max (max n₁ n₂) n₃ + 1) (by omega) hvx, Option.bind_eq_bind,
        Option.bind_some]
      exact apply_le (by omega) hw
    · simp only [hXA, ↓reduceDIte] at h
      cases h
  case h_4 heq =>
    obtain rfl := List.map_eq_nil_iff.mp heq
    cases h
    exact ⟨1, Val.unit, by rw [eval_node]; rfl, (rel_unit G _ _).mpr rfl⟩
  case h_5 ca a cb b heq =>
    obtain ⟨rfl, rfl, rfl⟩ := map_pair_eq_two heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff, Option.some.injEq] at h
    obtain ⟨ma, ha, mb, hb, rfl⟩ := h
    obtain ⟨n₁, va, hva, hra⟩ := ih ca (by simp) Γ _ ha env e he
    obtain ⟨n₂, vb, hvb, hrb⟩ := ih cb (by simp) Γ _ hb env e he
    refine ⟨max n₁ n₂ + 1, Val.pair va vb, ?_, (rel_prod G _ _ _ _).mpr ⟨va, vb, rfl, hra, hrb⟩⟩
    rw [eval_node]
    simp only [List.map_cons, List.map_nil, evStep, eval_le (m := max n₁ n₂ + 1) (by omega) hva,
      eval_le (m := max n₁ n₂ + 1) (by omega) hvb, Option.bind_eq_bind, Option.bind_some]
  case h_6 cp p heq =>
    obtain ⟨rfl, rfl⟩ := map_pair_eq_one heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨P, dp⟩, hp, ⟨A, B, hAB⟩, hprod, h⟩ := h
    cases h
    obtain rfl := prod?_eq hprod
    obtain ⟨n₁, vp, hvp, hrp⟩ := ih cp (by simp) Γ _ hp env e he
    obtain ⟨a, b, rfl, hra, -⟩ := (rel_prod G A B _ _).mp hrp
    refine ⟨n₁ + 1, a, ?_, hra⟩
    rw [eval_node]
    simp only [List.map_cons, List.map_nil, evStep, eval_le (m := n₁ + 1) (by omega) hvp,
      Option.bind_eq_bind, Option.bind_some, Val.pair, RoseTree.label_node, RoseTree.children_node]
  case h_7 cp p heq =>
    obtain ⟨rfl, rfl⟩ := map_pair_eq_one heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨P, dp⟩, hp, ⟨A, B, hAB⟩, hprod, h⟩ := h
    cases h
    obtain rfl := prod?_eq hprod
    obtain ⟨n₁, vp, hvp, hrp⟩ := ih cp (by simp) Γ _ hp env e he
    obtain ⟨a, b, rfl, -, hrb⟩ := (rel_prod G A B _ _).mp hrp
    refine ⟨n₁ + 1, b, ?_, hrb⟩
    rw [eval_node]
    simp only [List.map_cons, List.map_nil, evStep, eval_le (m := n₁ + 1) (by omega) hvp,
      Option.bind_eq_bind, Option.bind_some, Val.pair, RoseTree.label_node, RoseTree.children_node]
  case h_8 t _ heq =>
    obtain ⟨rfl, -⟩ := map_pair_eq_one heq
    cases h
    exact ⟨1, Val.quote t, by rw [eval_node]; rfl, (rel_tree G _ _).mpr rfl⟩
  case h_9 cc c ca a cb b heq =>
    obtain ⟨rfl, rfl, rfl, rfl⟩ := map_pair_eq_three heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨C, dc⟩, hc, ⟨A, da⟩, ha, ⟨B, db⟩, hb, h⟩ := h
    by_cases hC : C = tT
    · subst hC
      by_cases hBA : B = A
      · subst hBA
        simp only [↓reduceDIte] at h
        cases h
        obtain ⟨n₁, vc, hvc, hrc⟩ := ih cc (by simp) Γ _ hc env e he
        obtain ⟨n₂, va, hva, hra⟩ := ih ca (by simp) Γ _ ha env e he
        obtain ⟨n₃, vb, hvb, hrb⟩ := ih cb (by simp) Γ _ hb env e he
        obtain rfl := (rel_tree G vc (dc e)).mp hrc
        have hu : unquote (Val.quote (dc e)) = some (dc e) := rfl
        by_cases hl : (dc e).label = 0
        · refine ⟨max n₁ n₃ + 1, vb, ?_, ?_⟩
          · rw [eval_node]
            simp only [List.map_cons, List.map_nil, evStep,
              eval_le (m := max n₁ n₃ + 1) (by omega) hvc, Option.bind_eq_bind, Option.bind_some,
              hu]
            change (if RoseTree.label (dc e) ≠ 0 then eval G (max n₁ n₃ + 1) env ca
              else eval G (max n₁ n₃ + 1) env cb) = some vb
            simp only [ne_eq, hl, not_true_eq_false, ↓reduceIte]
            exact eval_le (by omega) hvb
          · change Rel G B vb (if (dc e).label ≠ 0 then da e else db e)
            simp only [ne_eq, hl, not_true_eq_false, ↓reduceIte]
            exact hrb
        · refine ⟨max n₁ n₂ + 1, va, ?_, ?_⟩
          · rw [eval_node]
            simp only [List.map_cons, List.map_nil, evStep,
              eval_le (m := max n₁ n₂ + 1) (by omega) hvc, Option.bind_eq_bind, Option.bind_some,
              hu]
            change (if RoseTree.label (dc e) ≠ 0 then eval G (max n₁ n₂ + 1) env ca
              else eval G (max n₁ n₂ + 1) env cb) = some va
            simp only [ne_eq, hl, not_false_eq_true, ↓reduceIte]
            exact eval_le (by omega) hva
          · change Rel G B va (if (dc e).label ≠ 0 then da e else db e)
            simp only [ne_eq, hl, not_false_eq_true, ↓reduceIte]
            exact hra
      · simp only [hBA, ↓reduceDIte] at h
        cases h
    · simp only [hC, ↓reduceDIte] at h
      cases h
  case h_10 A _ heq =>
    obtain ⟨rfl, -⟩ := map_pair_eq_one heq
    split at h
    · cases h
      exact ⟨1, _, by rw [eval_node]; rfl, rel_fold G A⟩
    · cases h
  case h_11 A _ heq =>
    obtain ⟨rfl, -⟩ := map_pair_eq_one heq
    split at h
    · cases h
      exact ⟨1, _, by rw [eval_node]; rfl, rel_iter G A⟩
    · cases h
  case h_12 A _ heq =>
    obtain ⟨rfl, -⟩ := map_pair_eq_one heq
    split at h
    · cases h
      exact ⟨1, _, by rw [eval_node]; rfl, (rel_list G A _ []).mpr ⟨A, rfl⟩⟩
    · cases h
  case h_13 cx x cxs xs heq =>
    obtain ⟨rfl, rfl, rfl⟩ := map_pair_eq_two heq
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨⟨X, dx⟩, hx, ⟨L, dl⟩, hl, ⟨A, hLA⟩, hlist, h⟩ := h
    obtain rfl := list?_eq hlist
    by_cases hXA : X = A
    · subst hXA
      simp only [↓reduceDIte] at h
      cases h
      obtain ⟨n₁, vx, hvx, hrx⟩ := ih cx (by simp) Γ _ hx env e he
      obtain ⟨n₂, vl, hvl, hrl⟩ := ih cxs (by simp) Γ _ hl env e he
      refine ⟨max n₁ n₂ + 1, RoseTree.node Label.cons [vx, vl], ?_,
        (rel_list G X _ _).mpr ⟨vx, vl, rfl, hrx, (rel_list G X _ _).mp hrl⟩⟩
      rw [eval_node]
      simp only [List.map_cons, List.map_nil, evStep, eval_le (m := max n₁ n₂ + 1) (by omega) hvx,
        eval_le (m := max n₁ n₂ + 1) (by omega) hvl, Option.bind_eq_bind, Option.bind_some]
    · simp only [hXA, ↓reduceDIte] at h
      cases h
  case h_14 A _ B _ heq =>
    obtain ⟨rfl, -, -⟩ := map_pair_eq_two heq
    split at h
    · cases h
      exact ⟨1, _, by rw [eval_node]; rfl, rel_foldr G A B⟩
    · cases h
  case h_15 k _ heq =>
    obtain ⟨rfl, -⟩ := map_pair_eq_one heq
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp h
    exact ⟨1, _, by rw [eval_node]; rfl, rel_prim G k.label g hg⟩
  case h_16 n _ heq =>
    obtain ⟨rfl, -⟩ := map_pair_eq_one heq
    obtain ⟨g, hg, rfl⟩ := Option.map_eq_some_iff.mp h
    obtain ⟨t, k, v, ht, hv, hr⟩ := hG _ g hg
    refine ⟨k + 1, v, ?_, hr⟩
    rw [eval_node]
    simp only [List.map_cons, List.map_nil, evStep, ht, Option.bind_some]
    exact hv
  case h_17 A _ B _ heq =>
    obtain ⟨rfl, -, -⟩ := map_pair_eq_two heq
    split at h
    · cases h
      exact ⟨1, _, by rw [eval_node]; rfl, rel_lcase G A B⟩
    · cases h
  case h_18 A _ heq =>
    obtain ⟨rfl, -⟩ := map_pair_eq_one heq
    split at h
    · cases h
      exact ⟨1, _, by rw [eval_node]; rfl, rel_para G A⟩
    · cases h
  case h_19 => cases h

/-! Loaded programs. -/

/-- Globals related to a program's definitions: each global's definition is the program's at its
index, and evaluates at some level to a value related to the global. -/
def RelGlobs (P : List Tree) (GD : List Glob) : Prop :=
  ∀ (i : ℕ) (g : Glob), GD[i]? = some g →
    ∃ t n v, P[i]? = some t ∧ eval P n [] t = some v ∧ Rel P g.1 v g.2

/-- A failed load stays failed. -/
theorem foldl_loadStep_none : ∀ D : List Tree, D.foldl loadStep none = none :=
  List.rec rfl fun _ _ ih ↦ ih

/-- Loading a part of a program from globals related to the definitions before it gives globals
related to the definitions through it. -/
theorem foldl_loadStep_rel (P : List Tree) :
    ∀ (D : List Tree) (GD₀ GD : List Glob), (∀ j, P[GD₀.length + j]? = D[j]?) →
      RelGlobs P GD₀ → D.foldl loadStep (some GD₀) = some GD → RelGlobs P GD := by
  refine List.rec (fun GD₀ GD _ h₀ h ↦ ?_) fun t D ih GD₀ GD hP h₀ h ↦ ?_
  · cases h
    exact h₀
  · rw [List.foldl_cons] at h
    rcases hm : infer GD₀ [] t with _ | m
    · simp only [loadStep, hm, Option.bind_eq_bind, Option.bind_some, Option.bind_none,
        foldl_loadStep_none] at h
      cases h
    · simp only [loadStep, hm, Option.bind_eq_bind, Option.bind_some] at h
      refine ih _ GD (fun j ↦ ?_) (fun i g hg ↦ ?_) h
      · simpa [Nat.add_assoc, Nat.add_comm 1 j] using hP (j + 1)
      · rcases Nat.lt_or_ge i GD₀.length with hi | hi
        · rw [List.getElem?_append_left hi] at hg
          exact h₀ i g hg
        · rw [List.getElem?_append_right hi] at hg
          obtain ⟨hi', rfl⟩ : i - GD₀.length = 0 ∧ ⟨m.1, m.2 ()⟩ = g := by
            rcases h' : i - GD₀.length with _ | k
            · simp_all
            · simp [h'] at hg
          obtain rfl : i = GD₀.length := by omega
          obtain ⟨n, v, hv, hr⟩ := fundamental P GD₀ h₀ t [] m hm [] () rfl
          exact ⟨t, n, v, by simpa using hP 0, hv, hr⟩

/-- The adequacy of the evaluator: when a program loads, each of its definitions evaluates at
some level to a value related to the global it loads to. -/
theorem load_rel {P : List Tree} {GD : List Glob} (h : load P = some GD) : RelGlobs P GD :=
  foldl_loadStep_rel P P [] GD (fun j ↦ by simp) (fun _ _ hg ↦ by simp at hg) h

/-- A loaded global from trees to trees is computed by the evaluator: its definition evaluates to
a value whose application to the quotation of every tree it maps to a tree gives, at some level,
that tree's quotation. -/
theorem eval_apply {P : List Tree} {GD : List Glob} (h : load P = some GD) {i : ℕ} {g : Glob}
    (hg : GD[i]? = some g) :
    ∃ t n v, P[i]? = some t ∧ eval P n [] t = some v ∧
      ∀ x y, g.apply x = some y → ∃ k, apply P k v (Val.quote x) = some (Val.quote y) := by
  obtain ⟨t, n, v, ht, hv, hr⟩ := load_rel h i g hg
  refine ⟨t, n, v, ht, hv, fun x y hy ↦ ?_⟩
  obtain ⟨A, d⟩ := g
  by_cases hA : A = tArrow tT tT
  · subst hA
    simp only [Glob.apply, ↓reduceDIte] at hy
    obtain rfl := Option.some.inj hy
    obtain ⟨k, w, hw, hrw⟩ := (rel_arrow P tT tT v d).mp hr (Val.quote x) x rfl
    exact ⟨k, hw.trans (congrArg some ((rel_tree P w (d x)).mp hrw))⟩
  · simp [Glob.apply, hA] at hy

end Geb.Kernel.Eval

end
