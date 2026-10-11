/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Typing

set_option doc.verso true in
/-!
# Canonical LF modulo rewriting

The extension of canonical LF by rewrite rules on its constants, the λΠ-calculus modulo of
\[CousineauDowek2007\] restricted to canonical forms: types are compared after
normalization by the rules, so that a term whose type holds of another by computation checks
against it. It is the extension that the let definitions with reduction rules of
\[NormanAvigad2025\], Section 3.1, make to LF: a rule's left side is a constant applied to
patterns, its right side a canonical term in the pattern variables, applied to arguments where a
variable is of a function type.

A rule declares its pattern variables as a context. A pattern is a pattern variable, applied to no
argument whatever its type, as in the rules of \[NormanAvigad2025\], or a constant applied to
patterns; a variable that occurs twice matches equal expressions. Matching is first order and
binds each variable to an expression of the context the matched expression is in. The right side
is instantiated by hereditary substitution of the bound expressions for the pattern variables,
the innermost first, each at its type's simple type, so that an applied variable bound to an
abstraction is reduced.

Normalization rewrites in parallel: a node whose children rewrote is rebuilt from them, and a
node whose children are normal is rewritten at its root by the first rule that matches. It
repeats to a bound on its steps and has no value where the bound is reached, so that the
comparison of types it decides is sound whether or not the rules terminate; the rules need be
neither terminating nor confluent for the check to be sound, only to be complete.

A rule is well typed ({lit}`Rule.ok`) when its context is, its left side, its pattern variables
η-expanded ({lit}`eta`), synthesizes a type, and its right side checks against that type. The
η-expansion of a head at a simple type (\[WatkinsEtAl2002\], Definition 15) abstracts over
one variable for each argument the type takes and applies the head to their η-expansions.

## Main definitions

* {lit}`eta` — the η-expansion of a head applied to a spine at a simple type.
* {lit}`Rule`, {lit}`matchPat`, {lit}`instantiate`, {lit}`Rule.apply` — rewrite rules, the
  matching of a pattern, the instantiation of a right side and the rewriting at a root.
* {lit}`step`, {lit}`normalize`, {lit}`conv` — a parallel step, normalization to a bound, and
  the comparison of types by normal forms.
* {lit}`Rule.ok`, {lit}`ChecksMod`, {lit}`Sig.okMod` — the typing of a rule, and the judgments
  modulo rules.

## References

* \[CousineauDowek2007\]
* \[NormanAvigad2025\], Section 3.1.
* \[WatkinsEtAl2002\], Definition 15, for η-expansion.

## Tags

logical framework, LF, rewriting, lambda-Pi-calculus modulo, η-expansion
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF

/-- One step of the η-expansion of a head applied to a spine, at a node of a simple type: at a
base type the application; at a function type an abstraction whose body is the expansion at the
codomain of the weakened head applied to the weakened spine and the η-expansion of the new
variable at the domain. -/
def etaStep (l : SimpleLabel) (cs : List (Head → List Expr → Expr)) (h : Head) (ms : List Expr) :
    Expr :=
  match l, cs with
    | .arrow, [e₁, e₂] =>
      Expr.lam (e₂ (h.rename Nat.succ) (ms.map Expr.shift ++ [e₁ (.var 0) []]))
    | _, _ => Expr.app h ms

/-- The η-expansion of a head applied to a spine at the simple type of the application. -/
def eta : SimpleTy → Head → List Expr → Expr := RoseTree.elim etaStep

/-- A rewrite rule: the types of its pattern variables, the innermost first, a left side, a
constant applied to patterns, and a right side in the context of the pattern variables. -/
structure Rule where
  /-- The pattern variables' types, the innermost first. -/
  vars : Ctx
  /-- The left side. -/
  lhs : Expr
  /-- The right side. -/
  rhs : Expr

/-- One step of the matching of a pattern against an expression, extending an assignment of the
pattern variables: a pattern variable is bound to the expression, or, already bound, must be bound
to it; a constant applied to patterns matches the same constant applied to as many expressions,
each pattern matching its expression in turn. -/
def matchStep (l : Label) (ps : List (Expr → List (Option Expr) → Option (List (Option Expr))))
    (e : Expr) (σ : List (Option Expr)) : Option (List (Option Expr)) :=
  match l, ps with
    | .app (.var i), [] =>
      match σ[i]? with
        | some none => some (σ.set i (some e))
        | some (some e') => if e' = e then some σ else none
        | none => none
    | .app (.const c), ps =>
      if e.label = .app (.const c) ∧ e.children.length = ps.length then
        (ps.zip e.children).foldlM (fun σ pe ↦ pe.1 pe.2 σ) σ
      else none
    | _, _ => none

/-- The matching of a pattern against an expression, extending an assignment. -/
def matchPat : Expr → Expr → List (Option Expr) → Option (List (Option Expr)) :=
  RoseTree.elim matchStep

/-- The instantiation of a right side, in the context of the pattern variables, at expressions of
an outer context: the innermost pattern variable is substituted first, its expression weakened
past the pattern variables that remain. -/
def instantiate (vars : Ctx) (σ : List Expr) (rhs : Expr) : Option Expr :=
  ((vars.zip σ).zipIdx).foldlM (init := rhs) fun e p ↦
    hsub (Expr.erase p.1.1) (p.1.2.rename (· + (vars.length - 1 - p.2))) e 0

/-- The rewriting of an expression at its root by a rule, where its left side matches. -/
def Rule.apply (r : Rule) (e : Expr) : Option Expr := do
  let σ ← matchPat r.lhs e (r.vars.map fun _ ↦ none)
  instantiate r.vars (← σ.mapM id) r.rhs

/-- One parallel step of rewriting at a node, from the steps of its children, each its result and
whether it rewrote. -/
def stepStep (rules : List Rule) (l : Label) (cs : List (Expr × Bool)) : Expr × Bool :=
  let e := RoseTree.node l (cs.map Prod.fst)
  if cs.any Prod.snd then (e, true) else
    match rules.findSome? fun r ↦ r.apply e with
      | some e' => (e', true)
      | none => (e, false)

/-- One parallel step of rewriting, and whether it rewrote. -/
def step (rules : List Rule) : Expr → Expr × Bool := RoseTree.elim (stepStep rules)

/-- The normal form of an expression reached in at most {lit}`fuel` parallel steps. -/
def normalize (rules : List Rule) (fuel : ℕ) (e : Expr) : Option Expr :=
  let r := Nat.repeat (fun p ↦ if p.2 then step rules p.1 else p) fuel (e, true)
  if r.2 then none else some r.1

/-- The equality of types modulo rules: equal normal forms, each reached within the bound. -/
def conv (rules : List Rule) (fuel : ℕ) (a b : Expr) : Bool :=
  match normalize rules fuel a, normalize rules fuel b with
    | some a', some b' => a' == b'
    | _, _ => false

/-- One step of the η-expansion of the pattern variables of a pattern, each at the simple type of
its type, weakened past the variables declared after it. -/
def etaPatStep (vars : Ctx) (l : Label) (cs : List Expr) : Expr :=
  match l, cs with
    | .app (.var i), [] =>
      match vars[i]? with
        | some a => eta (Expr.erase a) (.var i) []
        | none => Expr.var i
    | l, cs => RoseTree.node l cs

/-- The well-typedness of a rule: its context is formed, its left side, its pattern variables
η-expanded, synthesizes a type, and its right side checks against it. -/
def Rule.ok (sig : Sig) (r : Rule) : Bool :=
  Ctx.ok sig r.vars &&
    match (RoseTree.elim (etaPatStep r.vars) r.lhs).label,
        (RoseTree.elim (etaPatStep r.vars) r.lhs).children with
      | .app h, cs =>
        match (classOf sig r.vars h).bind fun a ↦
            spine r.vars a (cs.map fun m ↦ (m, judge sig m)) with
          | some a => IsApp a && Checks sig r.vars r.rhs a
          | none => false
      | _, _ => false

/-- {lit}`Γ ⊢ M ⇐ A` modulo rules, types compared by their normal forms within a bound. -/
def ChecksMod (rules : List Rule) (fuel : ℕ) (sig : Sig) (Γ : Ctx) (m a : Expr) : Bool :=
  judgeWith (conv rules fuel) sig m Γ (.check a)

/-- The formation of a signature modulo rules: the signature is formed and each rule well typed
in it. -/
def Sig.okMod (sig : Sig) (rules : List Rule) : Bool := sig.ok && rules.all (Rule.ok sig)

end Geb.LF

end
