/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.FinEnum
public import Geb.Mathlib.Data.W.Basic
public import Geb.Prototypes.RoseTree.Basic
public import Mathlib.Data.Fin.VecNotation

set_option doc.verso true in
/-!
# The bootstrap kernel

The kernel language of the bootstrap is System T \[Goedel1958\] over rose trees with
natural-number labels: simple types built from the one base type of trees by the unit type,
products, function types and lists; λ-terms with de Bruijn indices; quoted trees, a
conditional on labels, lists with their right fold, the fold of trees and the iteration of a
label's value at every type; and primitive operations on labels and children. A tree is a
label with a list of trees, and the fold of trees is that recursion: a node's result is
computed from the leaf of its label and the list of its children's results. Its terms and its
types are themselves rose trees, the label of a node naming its constructor, so a program is
a value of the language.

A term's meaning is its denotation in Lean: the base type denotes {name}`Geb.RoseTree` at
{lit}`ℕ`, a function type the Lean function type, and the fold the fold
{name}`Geb.RoseTree.elim`. The type checker and the evaluator are one fold over the term,
{lit}`infer`, which returns the term's type together with its denotation, or nothing when the
term is ill-typed. The evaluator therefore agrees with the denotation by construction; a
machine that runs the kernel is proved correct against {lit}`infer`.

The labels of the constructors, each named in {lit}`Label`:

* types: {lit}`0` the base type, {lit}`1` the unit type, {lit}`2` products over two
  children, {lit}`3` function types over a domain and a codomain, {lit}`4` lists over their
  elements' type;
* terms: {lit}`8` a variable over a leaf whose label is its de Bruijn index, {lit}`9` an
  abstraction over its domain type and its body, {lit}`10` an application, {lit}`11` the
  unit value, {lit}`12` a pair, {lit}`13` and {lit}`14` its projections, {lit}`15` a quoted
  tree, {lit}`16` a conditional on whether a tree's label is non-zero, {lit}`17` the fold of
  trees over its result type, {lit}`18` iteration over its result type, {lit}`19` the empty
  list over its elements' type, {lit}`20` the list of a head and a tail, {lit}`21` the right
  fold of lists over the elements' type and the result type, {lit}`22` a primitive over a
  leaf whose label is its index in {lit}`prims`, {lit}`23` a reference over a leaf whose
  label is its index in the global environment, and {lit}`24` case analysis of lists over
  the elements' type and the result type.

## Main definitions

* {lit}`Label`, {lit}`Prim` — the names of the labels of the constructors and of the indices of
  the primitives.
* {lit}`tT`, {lit}`tUnit`, {lit}`tProd`, {lit}`tArrow`, {lit}`tList` — the types.
* {lit}`Ty.den` — the denotation of a type.
* {lit}`Ty.IsTy` — the recognizer of types.
* {lit}`Ctx.den`, {lit}`Ctx.var` — contexts, their denotations and variable lookup.
* {lit}`Const` — the kernel's constants as plain Lean functions: the primitives, the fold of
  trees, iteration, the right fold of lists and case analysis of lists.
* {lit}`prims` — the primitives, with their types and denotations.
* {lit}`infer` — the type checker and evaluator.
* {lit}`Glob.apply`, {lit}`run` — the application of a global or a closed program from
  trees to trees.

## Implementation notes

The fold over a term needs the children as trees, to read type annotations, quoted trees
and indices, as well as their results, so {lit}`infer` is the paramorphism
{name}`Geb.RoseTree.para`, which computes each child's result once. A result is a
function of the global environment and the context, so a node's meaning is computed once
per application of its parent's meaning. The conditional evaluates one branch.

The denotation of each constant is a function of {lit}`Const` at the denotations of its
types, so Lean code written for a kernel program, which applies those functions at Lean
types, denotes what {lit}`infer` computes.

## References

* \[Goedel1958\]
* \[GirardLafontTaylor1989\], Section 7.4.2, for the functions System T defines.

## Tags

bootstrap, kernel, System T, rose tree, denotational semantics, type checking
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel

open scoped FinEnum

/-- The kernel's values: rose trees with natural-number labels. -/
abbrev Tree : Type := RoseTree ℕ

/-- The leaf with a label. -/
def leaf (n : ℕ) : Tree := RoseTree.node n []

/-- A node of two children, over a vector so that its denotation unfolds definitionally. -/
def node2 (l : ℕ) (a b : Tree) : Tree := WType.mk (l, 2) ![a, b]

namespace Label

/-- The label of the base type of trees. -/
@[match_pattern] abbrev tyTree : ℕ := 0

/-- The label of the unit type. -/
@[match_pattern] abbrev tyUnit : ℕ := 1

/-- The label of product types. -/
@[match_pattern] abbrev tyProd : ℕ := 2

/-- The label of function types. -/
@[match_pattern] abbrev tyArrow : ℕ := 3

/-- The label of list types. -/
@[match_pattern] abbrev tyList : ℕ := 4

/-- The label of a variable. -/
@[match_pattern] abbrev var : ℕ := 8

/-- The label of an abstraction. -/
@[match_pattern] abbrev lam : ℕ := 9

/-- The label of an application. -/
@[match_pattern] abbrev app : ℕ := 10

/-- The label of the unit value. -/
@[match_pattern] abbrev unit : ℕ := 11

/-- The label of a pair. -/
@[match_pattern] abbrev pair : ℕ := 12

/-- The label of the first projection. -/
@[match_pattern] abbrev fst : ℕ := 13

/-- The label of the second projection. -/
@[match_pattern] abbrev snd : ℕ := 14

/-- The label of a quoted tree. -/
@[match_pattern] abbrev quote : ℕ := 15

/-- The label of the conditional. -/
@[match_pattern] abbrev cond : ℕ := 16

/-- The label of the fold of trees. -/
@[match_pattern] abbrev fold : ℕ := 17

/-- The label of iteration. -/
@[match_pattern] abbrev iter : ℕ := 18

/-- The label of the empty list. -/
@[match_pattern] abbrev nil : ℕ := 19

/-- The label of the list of a head and a tail. -/
@[match_pattern] abbrev cons : ℕ := 20

/-- The label of the right fold of lists. -/
@[match_pattern] abbrev foldr : ℕ := 21

/-- The label of a primitive. -/
@[match_pattern] abbrev prim : ℕ := 22

/-- The label of a reference. -/
@[match_pattern] abbrev ref : ℕ := 23

/-- The label of case analysis of lists. -/
@[match_pattern] abbrev lcase : ℕ := 24

end Label

namespace Prim

/-- The index of the primitive giving the label of a tree. -/
@[match_pattern] abbrev label : ℕ := 0

/-- The index of the primitive giving the number of a tree's children. -/
@[match_pattern] abbrev arity : ℕ := 1

/-- The index of the primitive giving a tree's child by index. -/
@[match_pattern] abbrev child : ℕ := 2

/-- The index of the primitive giving a node from a label and a list of children. -/
@[match_pattern] abbrev node : ℕ := 3

/-- The index of the primitive giving the list of a tree's children. -/
@[match_pattern] abbrev children : ℕ := 4

/-- The index of the primitive giving addition. -/
@[match_pattern] abbrev add : ℕ := 5

/-- The index of the primitive giving truncated subtraction. -/
@[match_pattern] abbrev sub : ℕ := 6

/-- The index of the primitive giving multiplication. -/
@[match_pattern] abbrev mul : ℕ := 7

/-- The index of the primitive giving division. -/
@[match_pattern] abbrev div : ℕ := 8

/-- The index of the primitive giving the remainder. -/
@[match_pattern] abbrev mod : ℕ := 9

/-- The index of the primitive giving equality of labels. -/
@[match_pattern] abbrev eq : ℕ := 10

/-- The index of the primitive giving the order of labels. -/
@[match_pattern] abbrev lt : ℕ := 11

/-- The index of the primitive giving equality of trees. -/
@[match_pattern] abbrev equal : ℕ := 12

/-- The index of the primitive giving the base-two logarithm. -/
@[match_pattern] abbrev log2 : ℕ := 13

end Prim

/-- The base type of trees. -/
def tT : Tree := leaf Label.tyTree

/-- The unit type. -/
def tUnit : Tree := leaf Label.tyUnit

/-- The product type. -/
def tProd (A B : Tree) : Tree := node2 Label.tyProd A B

/-- The function type. -/
def tArrow (A B : Tree) : Tree := node2 Label.tyArrow A B

/-- The list type. -/
def tList (A : Tree) : Tree := WType.mk (Label.tyList, 1) ![A]

namespace Ty

/-- The denotation of a type. Trees of other shapes denote the unit type; the checker
rejects them as annotations. -/
def den : Tree → Type :=
  WType.elim Type fun ⟨(l, k), g⟩ ↦
    match l, k, g with
    | Label.tyTree, 0, _ => Tree
    | Label.tyProd, 2, g => g 0 × g 1
    | Label.tyArrow, 2, g => g 0 → g 1
    | Label.tyList, 1, g => List (g 0)
    | _, _, _ => Unit

/-- The recognizer of types. -/
def IsTy : Tree → Bool :=
  RoseTree.elim fun l rs ↦
    match l, rs with
    | Label.tyTree, [] | Label.tyUnit, [] => true
    | Label.tyProd, [a, b] | Label.tyArrow, [a, b] => a && b
    | Label.tyList, [a] => a
    | _, _ => false

/-- A type read as a function type, with the equation of denotations. -/
def arrow? : (F : Tree) → Option (Σ' A B : Tree, den F = (den A → den B))
  | WType.mk (Label.tyArrow, 2) g => some ⟨g 0, g 1, rfl⟩
  | _ => none

/-- A type read as a product type, with the equation of denotations. -/
def prod? : (P : Tree) → Option (Σ' A B : Tree, den P = (den A × den B))
  | WType.mk (Label.tyProd, 2) g => some ⟨g 0, g 1, rfl⟩
  | _ => none

/-- A type read as a list type, with the equation of denotations. -/
def list? : (L : Tree) → Option (Σ' A : Tree, den L = List (den A))
  | WType.mk (Label.tyList, 1) g => some ⟨g 0, rfl⟩
  | _ => none

end Ty

/-- A context: the types of the variables, the innermost first. -/
abbrev Ctx : Type := List Tree

namespace Ctx

/-- The denotation of a context: the product of its types' denotations. -/
def den (Γ : Ctx) : Type := Γ.foldr (fun A E ↦ Ty.den A × E) Unit

/-- The type and denotation of the variable of a de Bruijn index. -/
def var : (Γ : Ctx) → ℕ → Option (Σ A : Tree, Γ.den → Ty.den A) :=
  List.rec (fun _ ↦ none) fun A _ ih n ↦
    Nat.casesOn n (some ⟨A, Prod.fst⟩) fun m ↦ (ih m).map fun p ↦ ⟨p.1, p.2 ∘ Prod.snd⟩

end Ctx

/-- A global: a type with a value of it. -/
abbrev Glob : Type := Σ A : Tree, Ty.den A

/-- The meaning of a term in a context: its type and its denotation. -/
abbrev Meaning (Γ : Ctx) : Type := Σ A : Tree, Γ.den → Ty.den A

/-- The truth values of the conditional and the comparisons: label zero is false. -/
def ofBool (b : Bool) : Tree := leaf (if b then 1 else 0)

namespace Const

/-- The leaf of a tree's label. -/
def label (t : Tree) : Tree := leaf t.label

/-- The leaf of the number of a tree's children. -/
def arity : Tree → Tree
  | WType.mk (_, k) _ => leaf k

/-- A tree's child by index, the leaf of label zero when out of range. -/
def child : Tree → Tree → Tree
  | WType.mk (_, k) g, i => if h : i.label < k then g ⟨i.label, h⟩ else leaf 0

/-- The node of a tree's label over a list of children. -/
def node (l : Tree) (cs : List Tree) : Tree := RoseTree.node l.label cs

/-- The list of a tree's children. -/
def children (t : Tree) : List Tree := t.children

/-- The sum of two labels. -/
def add (a b : Tree) : Tree := leaf (a.label + b.label)

/-- The difference of two labels, truncated at zero. -/
def sub (a b : Tree) : Tree := leaf (a.label - b.label)

/-- The product of two labels. -/
def mul (a b : Tree) : Tree := leaf (a.label * b.label)

/-- The quotient of two labels, zero when dividing by zero. -/
def div (a b : Tree) : Tree := leaf (a.label / b.label)

/-- The remainder of two labels, the dividend when dividing by zero. -/
def mod (a b : Tree) : Tree := leaf (a.label % b.label)

/-- Whether two labels are equal. -/
def eq (a b : Tree) : Tree := ofBool (a.label == b.label)

/-- Whether one label is less than another. -/
def lt (a b : Tree) : Tree := ofBool (decide (a.label < b.label))

/-- Whether two trees are equal. -/
def equal (a b : Tree) : Tree := ofBool (decide (a = b))

/-- The base-two logarithm of a label, rounded down and zero at zero. -/
def log2 (t : Tree) : Tree := leaf t.label.log2

/-- The fold of trees: a node's result is the step applied to the leaf of its label and to
the list of its children's results. -/
def fold {α : Type} (f : Tree → List α → α) : Tree → α :=
  RoseTree.elim fun l rs ↦ f (leaf l) rs

/-- Iteration: the step applied as many times as the label of the tree. -/
def iter {α : Type} (s : α → α) (z : α) (n : Tree) : α := Nat.repeat s n.label z

/-- The right fold of lists. -/
def foldr {α β : Type} (g : α → β → β) (z : β) (xs : List α) : β := xs.foldr g z

/-- Case analysis of lists: the value for the empty list, or the function applied to the head
and the tail. -/
def lcase {α β : Type} (xs : List α) (n : β) (c : α → List α → β) : β :=
  match xs with
  | [] => n
  | x :: r => c x r

end Const

/-- The primitives, by index: the label of a tree, the number of its children, a child by
index, a node from the label of a tree and a list of children, the list of a tree's children,
arithmetic on labels, comparison of labels, equality of trees, and the base-two logarithm of a
label, each the function of that name in {lit}`Const`. The table is only extended, so that an
index names one primitive in every version. -/
def prims : List Glob :=
  let bin : Tree := tArrow tT (tArrow tT tT)
  [⟨tArrow tT tT, Const.label⟩, ⟨tArrow tT tT, Const.arity⟩,
   ⟨tArrow tT (tArrow tT tT), Const.child⟩, ⟨tArrow tT (tArrow (tList tT) tT), Const.node⟩,
   ⟨tArrow tT (tList tT), Const.children⟩, ⟨bin, Const.add⟩, ⟨bin, Const.sub⟩,
   ⟨bin, Const.mul⟩, ⟨bin, Const.div⟩, ⟨bin, Const.mod⟩, ⟨bin, Const.eq⟩, ⟨bin, Const.lt⟩,
   ⟨bin, Const.equal⟩, ⟨tArrow tT tT, Const.log2⟩]

/-- The type of the fold of trees at result type {lit}`A`. -/
def foldTy (A : Tree) : Tree := tArrow (tArrow tT (tArrow (tList A) A)) (tArrow tT A)

/-- The fold of trees at result type {lit}`A`. -/
def foldDen (A : Tree) : Ty.den (foldTy A) := Const.fold (α := Ty.den A)

/-- The type of the right fold of lists with elements of type {lit}`A` at result type
{lit}`B`. -/
def foldrTy (A B : Tree) : Tree :=
  tArrow (tArrow A (tArrow B B)) (tArrow B (tArrow (tList A) B))

/-- The right fold of lists with elements of type {lit}`A` at result type {lit}`B`. -/
def foldrDen (A B : Tree) : Ty.den (foldrTy A B) := Const.foldr (α := Ty.den A) (β := Ty.den B)

/-- The type of case analysis of lists with elements of type {lit}`A` at result type
{lit}`B`. -/
def lcaseTy (A B : Tree) : Tree :=
  tArrow (tList A) (tArrow B (tArrow (tArrow A (tArrow (tList A) B)) B))

/-- Case analysis of lists with elements of type {lit}`A` at result type {lit}`B`. -/
def lcaseDen (A B : Tree) : Ty.den (lcaseTy A B) := Const.lcase (α := Ty.den A) (β := Ty.den B)

/-- The type of iteration at result type {lit}`A`. -/
def iterTy (A : Tree) : Tree := tArrow (tArrow A A) (tArrow A (tArrow tT A))

/-- Iteration at result type {lit}`A`. -/
def iterDen (A : Tree) : Ty.den (iterTy A) := Const.iter (α := Ty.den A)

/-- The meaning of a term, as a function of the global environment and the context. -/
abbrev Sem : Type := List Glob → (Γ : Ctx) → Option (Meaning Γ)

/-- The meaning of a global or a primitive, constant in the context. -/
def constant {Γ : Ctx} (g : Glob) : Meaning Γ := ⟨g.1, fun _ ↦ g.2⟩

/-- One node of the checker-evaluator: the node's label, and each child as a tree with its
meaning. -/
def inferStep (l : ℕ) (cs : List (Tree × Sem)) : Sem := fun G Γ ↦
  match l, cs with
  | Label.var, [(n, _)] => Γ.var n.label
  | Label.lam, [(A, _), (_, b)] =>
    if Ty.IsTy A then (b G (A :: Γ)).map fun m ↦ ⟨tArrow A m.1, fun e a ↦ m.2 (a, e)⟩
    else none
  | Label.app, [(_, f), (_, x)] => do
    let mf ← f G Γ
    let mx ← x G Γ
    let ⟨A, B, h⟩ ← Ty.arrow? mf.1
    if hx : mx.1 = A then
      some ⟨B, fun e ↦ cast h (mf.2 e) (cast (congrArg Ty.den hx) (mx.2 e))⟩
    else none
  | Label.unit, [] => some ⟨tUnit, fun _ ↦ ()⟩
  | Label.pair, [(_, a), (_, b)] => do
    let ma ← a G Γ
    let mb ← b G Γ
    some ⟨tProd ma.1 mb.1, fun e ↦ (ma.2 e, mb.2 e)⟩
  | Label.fst, [(_, p)] => do
    let mp ← p G Γ
    let ⟨A, _, h⟩ ← Ty.prod? mp.1
    some ⟨A, fun e ↦ (cast h (mp.2 e)).1⟩
  | Label.snd, [(_, p)] => do
    let mp ← p G Γ
    let ⟨_, B, h⟩ ← Ty.prod? mp.1
    some ⟨B, fun e ↦ (cast h (mp.2 e)).2⟩
  | Label.quote, [(t, _)] => some ⟨tT, fun _ ↦ t⟩
  | Label.cond, [(_, c), (_, a), (_, b)] => do
    let mc ← c G Γ
    let ma ← a G Γ
    let mb ← b G Γ
    if hc : mc.1 = tT then
      if hb : mb.1 = ma.1 then
        some ⟨ma.1, fun e ↦
          if (cast (congrArg Ty.den hc) (mc.2 e)).label ≠ 0 then ma.2 e
          else cast (congrArg Ty.den hb) (mb.2 e)⟩
      else none
    else none
  | Label.fold, [(A, _)] => if Ty.IsTy A then some (constant ⟨foldTy A, foldDen A⟩) else none
  | Label.iter, [(A, _)] => if Ty.IsTy A then some (constant ⟨iterTy A, iterDen A⟩) else none
  | Label.nil, [(A, _)] =>
    if Ty.IsTy A then some ⟨tList A, fun _ ↦ ([] : List (Ty.den A))⟩ else none
  | Label.cons, [(_, x), (_, xs)] => do
    let mx ← x G Γ
    let mxs ← xs G Γ
    let ⟨A, h⟩ ← Ty.list? mxs.1
    if hx : mx.1 = A then
      some ⟨tList A, fun e ↦ cast (congrArg Ty.den hx) (mx.2 e) :: cast h (mxs.2 e)⟩
    else none
  | Label.foldr, [(A, _), (B, _)] =>
    if Ty.IsTy A && Ty.IsTy B then some (constant ⟨foldrTy A B, foldrDen A B⟩) else none
  | Label.prim, [(k, _)] => prims[k.label]?.map constant
  | Label.ref, [(n, _)] => G[n.label]?.map constant
  | Label.lcase, [(A, _), (B, _)] =>
    if Ty.IsTy A && Ty.IsTy B then some (constant ⟨lcaseTy A B, lcaseDen A B⟩) else none
  | _, _ => none

/-- The type checker and evaluator: the type and denotation of a term in a global
environment and a context, or nothing when the term is ill-typed. -/
def infer (G : List Glob) (Γ : Ctx) (t : Tree) : Option (Meaning Γ) :=
  RoseTree.para inferStep t G Γ

/-- Apply a global of type {lit}`T → T` to an input tree. -/
def Glob.apply (g : Glob) (input : Tree) : Option Tree :=
  if h : g.1 = tArrow tT tT then some (cast (congrArg Ty.den h) g.2 input) else none

/-- Apply a closed program of type {lit}`T → T` to an input tree. -/
def run (G : List Glob) (t input : Tree) : Option Tree := do
  let m ← infer G [] t
  Glob.apply ⟨m.1, m.2 ()⟩ input

end Geb.Kernel

end
