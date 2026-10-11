/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.ConcreteSyntax
public import Geb.Prototypes.RoseTree.Basic

set_option doc.verso true in
/-!
# The syntax of canonical LF

The expressions of Canonical LF, the presentation of the logical framework LF in which only
canonical forms, long βη-normal forms, are expressions (\[HarperLicata2007\], Section 2.1,
Figure 1; LF itself is \[HarperHonsellPlotkin1993\]). Its kinds are {lit}`type` and the
dependent products {lit}`Π x:A. K`; its canonical type families the atomic families
{lit}`a M₁ … Mₙ` and the dependent products {lit}`Π x:A₂. A`; its canonical terms the atomic
terms and the abstractions {lit}`λ x. M`; and its atomic terms a variable or a constant applied
to canonical terms. A signature declares constants, each with a kind or a type, and a context
declares variables with their types.

The four forms of the grammar are one rose tree: a node is the kind {lit}`type`, a dependent
product of two children, the second in the scope of the bound variable, an abstraction of one
child in its scope, or the application of a head, a variable or a constant, to the list of its
children, the spine of the application. An atomic family and an atomic term are both the
application of a head, so that a head applied to no argument is a constant family or a variable;
which of the categories an expression is in is decided by the judgments that classify it. The
grammar admits no β-redex, since only a head is applied. Variables are de Bruijn indices, the
innermost binder's variable the index zero, and constants are indices into the signature, the
first declared the index zero.

The erasure of a type to a simple type (\[HarperLicata2007\], Figure 4) forgets the
dependency of a type on terms, keeping the families at its bases and the shape of its products;
it is the index on which hereditary substitution recurses.

## Main definitions

* {lit}`Head`, {lit}`Label`, {lit}`Expr` — the heads, the labels of the nodes, and the
  expressions.
* {lit}`Label.binders` — the binding signature: the variables a node binds over each child.
* {lit}`Expr.rename`, {lit}`Expr.shift` — the renaming of an expression's variables.
* {lit}`SimpleLabel`, {lit}`SimpleTy`, {lit}`Expr.erase` — the simple types and the erasure.
* {lit}`Sig`, {lit}`Ctx` — signatures and contexts.

## References

* \[HarperLicata2007\], Section 2.1 and Figures 1 and 4.
* \[HarperHonsellPlotkin1993\]
* \[Fiore2008\], for binding signatures.

## Tags

logical framework, LF, canonical forms, spine form, de Bruijn index
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF

/-- The head of an application: a variable, a de Bruijn index, or a constant, an index into the
signature. -/
inductive Head where
  /-- The variable of a de Bruijn index. -/
  | var (i : ℕ)
  /-- The constant of an index into the signature. -/
  | const (c : ℕ)
deriving DecidableEq, Repr

/-- The label of a node of an expression. -/
inductive Label where
  /-- The kind of types. -/
  | type
  /-- The dependent product of a type and a family or kind in the scope of its variable. -/
  | pi
  /-- The abstraction of a canonical term over a variable. -/
  | lam
  /-- The application of a head to its spine, the node's children. -/
  | app (h : Head)
deriving DecidableEq, Repr

/-- An expression of canonical LF: a kind, a type family or a term. -/
abbrev Expr : Type := RoseTree Label

/-- The equality of expressions, decided node by node, each node's children enumerated by
{name}`Geb.finEnumFin`, without {lit}`Classical.choice`. -/
instance : DecidableEq Expr := @WType.instDecidableEq _ _ _ fun p ↦ finEnumFin p.2

namespace Expr

/-- The kind of types. -/
def type : Expr := RoseTree.node .type []

/-- The dependent product {lit}`Π x:A. B`, with {lit}`B` in the scope of {lit}`x`. -/
def pi (a b : Expr) : Expr := RoseTree.node .pi [a, b]

/-- The abstraction {lit}`λ x. M`. -/
def lam (m : Expr) : Expr := RoseTree.node .lam [m]

/-- The application of a head to a spine. -/
def app (h : Head) (ms : List Expr) : Expr := RoseTree.node (.app h) ms

/-- The application of the variable of index {lit}`i` to a spine. -/
def var (i : ℕ) (ms : List Expr := []) : Expr := app (.var i) ms

/-- The application of the constant of index {lit}`c` to a spine. -/
def const (c : ℕ) (ms : List Expr := []) : Expr := app (.const c) ms

end Expr

/-- The number of variables a node of a label binds over its child at a position: a product's
codomain and an abstraction's body are in the scope of one, every other child in the scope of
none. These numbers are the binding signature of the syntax (\[Fiore2008\]). -/
def Label.binders : Label → ℕ → ℕ
  | .pi, 1 => 1
  | .lam, 0 => 1
  | _, _ => 0

/-- The lifting of a renaming of variables under a binder. -/
def liftR (ρ : ℕ → ℕ) : ℕ → ℕ := fun i ↦ match i with
  | 0 => 0
  | j + 1 => ρ j + 1

/-- The renaming of a head: a variable renamed, a constant left in place. -/
def Head.rename (ρ : ℕ → ℕ) : Head → Head
  | .var i => .var (ρ i)
  | .const c => .const c

/-- The renaming of a label: the head of an application renamed, every other label left in
place. -/
def Label.rename (ρ : ℕ → ℕ) : Label → Label
  | .app h => .app (h.rename ρ)
  | l => l

/-- One step of the renaming of an expression's variables, at a node of a label, from the
renamings of its children: the label is renamed, and each child is renamed by the renaming lifted
under the variables the node binds over it. -/
def renameStep (l : Label) (cs : List ((ℕ → ℕ) → Expr)) (ρ : ℕ → ℕ) : Expr :=
  RoseTree.node (l.rename ρ) (cs.zipIdx.map fun p ↦ p.1 (liftR^[l.binders p.2] ρ))

/-- The renaming of an expression's variables. -/
def Expr.rename : Expr → (ℕ → ℕ) → Expr := RoseTree.elim renameStep

/-- The weakening of an expression by one variable, bound outside it. -/
def Expr.shift (e : Expr) : Expr := e.rename Nat.succ

/-- The non-dependent product {lit}`A → B`, whose codomain does not mention the bound variable:
{lit}`B` is written in the context outside the binder and weakened past it. -/
def Expr.arrow (a b : Expr) : Expr := Expr.pi a b.shift

/-- The label of a node of a simple type (\[HarperLicata2007\], Figure 4). -/
inductive SimpleLabel where
  /-- The base type of a family constant. -/
  | base (a : ℕ)
  /-- The function type, of two children. -/
  | arrow
deriving DecidableEq, Repr

/-- A simple type: a base type of a family constant, or a function type. -/
abbrev SimpleTy : Type := RoseTree SimpleLabel

/-- The equality of simple types, decided as that of expressions. -/
instance : DecidableEq SimpleTy := @WType.instDecidableEq _ _ _ fun p ↦ finEnumFin p.2

/-- One step of the erasure of a type to a simple type: a product to the function type of its
domain's and codomain's erasures, an atomic family to the base type of its head. The erasure is
used only at types; at other expressions its value is that of a base type. -/
def eraseStep (l : Label) (cs : List SimpleTy) : SimpleTy :=
  match l, cs with
    | .pi, [a, b] => RoseTree.node .arrow [a, b]
    | .app (.const c), _ => RoseTree.node (.base c) []
    | _, _ => RoseTree.node (.base 0) []

/-- The erasure of a type to a simple type (\[HarperLicata2007\], Figure 4). -/
def Expr.erase : Expr → SimpleTy := RoseTree.elim eraseStep

/-- A signature: the kinds and types of the constants, the first declared first, each closed
and in the scope of the constants before it. -/
abbrev Sig : Type := List Expr

/-- A context: the types of the variables, the innermost first, each in the scope of the
variables after it. -/
abbrev Ctx : Type := List Expr

end Geb.LF

end
