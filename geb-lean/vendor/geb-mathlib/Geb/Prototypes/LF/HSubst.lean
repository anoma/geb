/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Syntax

set_option doc.verso true in
/-!
# Hereditary substitution

The hereditary substitution of a canonical term for a variable, which computes the canonical form
of the result of an ordinary substitution (\[HarperLicata2007\], Section 2.2 and Figure 5,
after Watkins and others). Where an ordinary substitution would place an abstraction at the head
of an application, creating a β-redex, the hereditary substitution continues by substituting the
application's arguments into the abstraction's body, each at its own simple type. The simple type
of the substituted term guides the process: the arguments' types are smaller than the head's, so
that the process is a recursion on the simple type, and within one simple type a recursion on the
expression substituted into.

The two recursions are two folds. The substitution into an expression ({lit}`hsubWith`) is a fold
over the expression, parametrized by the reduction of an application whose head is the
substituted variable; the reduction ({lit}`reduce`) is a fold over the simple type, which at a
function type substitutes the first argument into the abstraction's body by the substitution at
the domain, and reduces the rest of the spine at the codomain. A substitution or a reduction that
meets an expression of the wrong shape for its simple type has no value: on well-typed
expressions it always has one.

With de Bruijn indices, the substitution of {lit}`N` for the variable of index {lit}`j` removes
that variable from the context: the variables above it are renumbered one lower, and under a
binder {lit}`N` is weakened and {lit}`j` raised by one.

## Main definitions

* {lit}`hsubStep`, {lit}`hsubWith` — the substitution into an expression, given the reduction.
* {lit}`reduceStep`, {lit}`reduce` — the reduction of an application at a simple type.
* {lit}`hsub` — the hereditary substitution at a simple type.

## References

* \[HarperLicata2007\], Section 2.2 and Figure 5.

## Tags

logical framework, LF, hereditary substitution, canonical forms
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF

open Expr

/-- One step of the substitution of {lit}`N` for the variable of index {lit}`j`, at a node of a
label, from the substitutions into its children, given the reduction {lit}`red` of the substituted
term applied to a spine. At an application of the substituted variable the reduction applies to
the substituted spine; at an application of another variable, the variable is renumbered past the
removed one; at every other node each child is substituted into under the variables the node binds
over it, {lit}`N` weakened past them and {lit}`j` raised by their number. -/
def hsubStep (red : Expr → List Expr → Option Expr) (l : Label)
    (cs : List (Expr → ℕ → Option Expr)) (n : Expr) (j : ℕ) : Option Expr :=
  match l with
    | .app (.var i) => do
      let ms ← cs.mapM fun c ↦ c n j
      if i = j then red n ms else pure (var (if j < i then i - 1 else i) ms)
    | l => RoseTree.node l <$>
      (cs.zipIdx.map fun p ↦ p.1 (Expr.shift^[l.binders p.2] n) (j + l.binders p.2)).mapM id

/-- The substitution of a term for a variable in an expression, given the reduction of the term
applied to a spine. -/
def hsubWith (red : Expr → List Expr → Option Expr) : Expr → Expr → ℕ → Option Expr :=
  RoseTree.elim (hsubStep red)

/-- One step of the reduction of a canonical term applied to a spine, at a node of a simple
type, from the reductions at its children: at a base type the spine is empty and the term is the
result; at a function type the term is an abstraction, the first argument is substituted into
its body by the substitution at the domain, and the rest of the spine is reduced at the
codomain. -/
def reduceStep (l : SimpleLabel) (cs : List (Expr → List Expr → Option Expr)) (n : Expr)
    (ms : List Expr) : Option Expr :=
  match l, cs, ms with
    | .base _, [], [] => some n
    | .arrow, [r₁, r₂], m :: ms =>
      match n.label, n.children with
        | .lam, [b] => (hsubWith r₁ b m 0).bind fun b' ↦ r₂ b' ms
        | _, _ => none
    | _, _, _ => none

/-- The reduction of a canonical term of a simple type applied to a spine. -/
def reduce : SimpleTy → Expr → List Expr → Option Expr := RoseTree.elim reduceStep

/-- The hereditary substitution {lit}`[N/j]^α E` of the term {lit}`N`, of the simple type
{lit}`α`, for the variable of index {lit}`j` in the expression {lit}`E`. -/
def hsub (α : SimpleTy) (n e : Expr) (j : ℕ) : Option Expr := hsubWith (reduce α) e n j

end Geb.LF

end
