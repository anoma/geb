/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.BitTree.Encoding

set_option doc.verso true

/-!
# Values and applications of triage calculus

Values have leaf, stem, and fork constructors. Expressions are binary application
trees whose leaves are values. Consequently an application cannot occur below a
value constructor. Both datatypes are polynomial W-types.

## Main definitions

* {lit}`Value` and {lit}`Expr` distinguish values from pending applications.
* {lit}`Value.toTree` and {lit}`Expr.toTree` embed these datatypes into the existing
  binary trees with bitstring payloads.
* {lit}`Expr.encode` gives their concrete bitstrings.

## Implementation notes

The constant is an empty labelled leaf. A stem is a binary fork of the tag leaf
with payload {lit}`0` and its child. A value fork uses tag {lit}`1` followed by a
binary pair of children. Application uses tag {lit}`00` followed by such a pair.
These tags distinguish application from value construction without graph sharing.

## References

* \[TreeCalculusSpecification\], triage values and rules.
* \[TreeCalculusImplementation\], branch-first OCaml evaluator.

## Tags

tree calculus, triage calculus, W-type, bitstring, encoding
-/

@[expose] public section

namespace Geb.Triage

/-- The constructor labels of values. -/
inductive ValueShape
  | leaf | stem | fork
  deriving DecidableEq, Repr

/-- Value constructors have zero, one, or two children. -/
def ValueArity : ValueShape → Type
  | .leaf => Empty
  | .stem => Unit
  | .fork => Bool

/-- Values contain only values, never pending applications. -/
abbrev Value := WType ValueArity

namespace Value

/-- The triangle constant. -/
def leaf : Value := WType.mk .leaf Empty.elim

/-- A value with one child. -/
def stem (v : Value) : Value := WType.mk .stem fun _ ↦ v

/-- A value with two ordered children. -/
def fork (v w : Value) : Value := WType.mk .fork fun b : Bool ↦ if b then w else v

/-- Induction through the value polynomial's recursor. -/
theorem value_ind {P : Value → Prop} (hl : P leaf) (hs : ∀ v, P v → P (stem v))
    (hf : ∀ v w, P v → P w → P (fork v w)) : ∀ v, P v :=
  WType.rec fun s f ih ↦ by
    cases s with
    | leaf =>
      have h : f = Empty.elim := funext fun e ↦ e.elim
      subst f
      exact hl
    | stem =>
      have h : (fun _ : Unit ↦ f ()) = f := funext fun u ↦ by cases u; rfl
      exact h ▸ hs (f ()) (ih ())
    | fork =>
      have h : (fun b : Bool ↦ if b then f true else f false) = f :=
        funext fun b ↦ by cases b <;> rfl
      exact h ▸ hf (f false) (f true) (ih false) (ih true)

/-- The value embedding into binary trees of bitstrings. -/
def toTree : Value → BitTree.Tree := WType.elim BitTree.Tree fun x ↦
  match x with
  | ⟨.leaf, _⟩ => BitTree.leaf []
  | ⟨.stem, f⟩ => BitTree.fork (BitTree.leaf [false]) (f ())
  | ⟨.fork, f⟩ => BitTree.fork (BitTree.leaf [true]) (BitTree.fork (f false) (f true))

@[simp] theorem toTree_leaf : toTree leaf = BitTree.leaf [] := rfl

@[simp] theorem toTree_stem (v : Value) :
    toTree (stem v) = BitTree.fork (BitTree.leaf [false]) (toTree v) := rfl

@[simp] theorem toTree_fork (v w : Value) :
    toTree (fork v w) =
      BitTree.fork (BitTree.leaf [true]) (BitTree.fork (toTree v) (toTree w)) := rfl

end Value

/-- A value-labelled leaf has no expression children; an application has two. -/
def ExprArity : Option Value → Type
  | some _ => Empty
  | none => Bool

/-- Expressions are the free binary application trees on values. -/
abbrev Expr := WType ExprArity

namespace Expr

/-- Regard a value as a completed expression. -/
def value (v : Value) : Expr := WType.mk (some v) Empty.elim

/-- A pending application. -/
def app (f x : Expr) : Expr := WType.mk none fun b : Bool ↦ if b then x else f

/-- Induction through the expression polynomial's recursor. -/
theorem expr_ind {P : Expr → Prop} (hv : ∀ v, P (value v))
    (ha : ∀ f x, P f → P x → P (app f x)) : ∀ e, P e :=
  WType.rec fun s f ih ↦ by
    cases s with
    | some v =>
      have h : f = Empty.elim := funext fun e ↦ e.elim
      subst f
      exact hv v
    | none =>
      have h : (fun b : Bool ↦ if b then f true else f false) = f :=
        funext fun b ↦ by cases b <;> rfl
      exact h ▸ ha (f false) (f true) (ih false) (ih true)

/-- Inspect whether an expression is already a value. -/
def getValue : Expr → Option Value := fun e ↦ e.1

@[simp] theorem getValue_value (v : Value) : (value v).getValue = some v := rfl

@[simp] theorem getValue_app (f x : Expr) : (app f x).getValue = none := rfl

/-- A successful value inspection identifies the entire expression. -/
theorem getValue_eq_some_iff (e : Expr) (v : Value) : e.getValue = some v ↔ e = value v := by
  refine expr_ind (P := fun e ↦ e.getValue = some v ↔ e = value v) ?_ ?_ e
  · intro w
    constructor
    · intro h
      exact congrArg value (Option.some.inj h)
    · intro h
      exact congrArg getValue h
  · intro f x _ _
    constructor
    · intro h
      cases h
    · intro h
      have hh := congrArg getValue h
      cases hh

/-- Embed application nodes with their own tag; embedded values retain their value encoding. -/
def toTree : Expr → BitTree.Tree := WType.elim BitTree.Tree fun x ↦
  match x with
  | ⟨some v, _⟩ => v.toTree
  | ⟨none, f⟩ =>
    BitTree.fork (BitTree.leaf [false, false]) (BitTree.fork (f false) (f true))

@[simp] theorem toTree_value (v : Value) : (value v).toTree = v.toTree := rfl

@[simp] theorem toTree_app (f x : Expr) :
    (app f x).toTree =
      BitTree.fork (BitTree.leaf [false, false]) (BitTree.fork f.toTree x.toTree) := rfl

/-- Serialize an expression using the established binary-tree encoding. -/
def encode (e : Expr) : List Bool := BitTree.encode e.toTree

/-- Every encoded triage expression passes the existing binary-tree recognizer. -/
@[simp] theorem validBool_encode (e : Expr) : BitTree.validBool e.encode = true :=
  BitTree.validBool_encode e.toTree

end Expr

end Geb.Triage
