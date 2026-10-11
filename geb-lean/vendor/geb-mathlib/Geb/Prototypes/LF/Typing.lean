/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.HSubst

set_option doc.verso true in
/-!
# The judgments of canonical LF

The formation judgments of Canonical LF (\[HarperLicata2007\], Section 2.2, Figures 2 and 3),
with the subordination relation the complete one, so that it restricts nothing. They are
bidirectional and directed by the syntax, so that each is decided by a fold over the expression it
classifies, one clause for each rule:

* {lit}`Γ ⊢ K kind`: {lit}`type` is a kind (canon kind type), and {lit}`Π x:A. K` is one when
  {lit}`A` is a type and {lit}`K` a kind in the extended context (canon kind pi);
* {lit}`Γ ⊢ A type`: {lit}`Π x:A₂. A` is a type when {lit}`A₂` is one and {lit}`A` is one in the
  extended context (canon fam pi), and an atomic family is one when its kind is {lit}`type`
  (canon fam atom);
* {lit}`Γ ⊢ P ⇒ K`: the kind of an atomic family is its constant's kind, instantiated at its
  arguments by hereditary substitution (atom fam const, atom fam app);
* {lit}`Γ ⊢ M ⇐ A`: an abstraction checks against a product when its body checks against the
  codomain in the extended context (canon term lam), and an atomic term checks against an atomic
  type, and only against one, when it synthesizes that type (canon term atom), so that the terms
  that check are η-long;
* {lit}`Γ ⊢ R ⇒ A`: the type of an atomic term is its head's, a variable's from the context and a
  constant's from the signature, instantiated at its arguments, each checked against the domain
  it meets, by hereditary substitution (atom term var, atom term const, atom term app).

An application is a head with its spine, so that the rules atom fam app and atom term app,
applied once per argument, are one pass along the spine ({lit}`spine`). Types are compared as
expressions: canonical forms are unique, so that no other equality is needed. The rules for
contexts and signatures (Figure 2) check each declaration in the scope of those before it.

## Main definitions

* {lit}`Mode` — the three judgments that check an expression.
* {lit}`classOf`, {lit}`spine` — the classifier of a head, and its instantiation along a spine.
* {lit}`judgeWith`, {lit}`judge` — the fold deciding the judgments, with a given equality of
  types and with the equality of expressions.
* {lit}`IsKind`, {lit}`IsType`, {lit}`Checks` — the judgments.
* {lit}`Ctx.ok`, {lit}`Sig.ok` — the formation of contexts and signatures.

## References

* \[HarperLicata2007\], Section 2.2 and Figures 2 and 3.

## Tags

logical framework, LF, bidirectional typing, canonical forms, signature
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF

open Expr

/-- The judgment an expression is checked in. -/
inductive Mode where
  /-- That it is a kind. -/
  | kind
  /-- That it is a type. -/
  | type
  /-- That it is a canonical term of a type. -/
  | check (a : Expr)

/-- The classifier of a head in a signature and a context: a variable's type from the context,
weakened past the variables declared after it, and a constant's kind or type from the
signature. -/
def classOf (sig : Sig) (Γ : Ctx) : Head → Option Expr
  | .var i => Γ[i]?.map fun a ↦ a.rename (· + (i + 1))
  | .const c => sig[c]?

/-- The instantiation of a classifier along a spine: each argument is checked against the domain
of the product it meets, and substituted hereditarily, at the domain's simple type, for the
product's variable in its codomain. -/
def spine (Γ : Ctx) (c : Expr) (ms : List (Expr × (Ctx → Mode → Bool))) : Option Expr :=
  ms.foldlM (init := c) fun c m ↦
    match c.label, c.children with
      | .pi, [a, b] => if m.2 Γ (.check a) then hsub (Expr.erase a) m.1 b 0 else none
      | _, _ => none

/-- Whether an expression is an atomic family or term, the application of a head. -/
def IsApp (e : Expr) : Bool :=
  match e.label with
    | .app _ => true
    | _ => false

/-- One step of the judgments, at a node of a label, from the judgments of its children, each
child paired with its judgment, with {lit}`eqv` the equality of the types an atomic term
synthesizes and is checked against. -/
def judgeStep (eqv : Expr → Expr → Bool) (sig : Sig) (l : Label)
    (cs : List (Expr × (Ctx → Mode → Bool))) (Γ : Ctx) : Mode → Bool
  | .kind =>
    match l, cs with
      | .type, [] => true
      | .pi, [(a, ja), (_, jk)] => ja Γ .type && jk (a :: Γ) .kind
      | _, _ => false
  | .type =>
    match l, cs with
      | .pi, [(a, ja), (_, jb)] => ja Γ .type && jb (a :: Γ) .type
      | .app (.const c), cs => (sig[c]?.bind fun k ↦ spine Γ k cs) == some type
      | _, _ => false
  | .check p =>
    match l, cs with
      | .lam, [(_, jm)] =>
        match p.label, p.children with
          | .pi, [a, b] => jm (a :: Γ) (.check b)
          | _, _ => false
      | .app h, cs =>
        IsApp p && match (classOf sig Γ h).bind fun a ↦ spine Γ a cs with
          | some a => eqv a p
          | none => false
      | _, _ => false

/-- The judgments of an expression in a signature, in a context, with {lit}`eqv` the equality of
types. -/
def judgeWith (eqv : Expr → Expr → Bool) (sig : Sig) : Expr → Ctx → Mode → Bool :=
  RoseTree.para (judgeStep eqv sig)

/-- The judgments of an expression in a signature, in a context, types compared as expressions. -/
def judge (sig : Sig) : Expr → Ctx → Mode → Bool := judgeWith (· == ·) sig

/-- {lit}`Γ ⊢ K kind`. -/
def IsKind (sig : Sig) (Γ : Ctx) (k : Expr) : Bool := judge sig k Γ .kind

/-- {lit}`Γ ⊢ A type`. -/
def IsType (sig : Sig) (Γ : Ctx) (a : Expr) : Bool := judge sig a Γ .type

/-- {lit}`Γ ⊢ M ⇐ A`. -/
def Checks (sig : Sig) (Γ : Ctx) (m a : Expr) : Bool := judge sig m Γ (.check a)

/-- The formation of a context: each type is a type in the context of the variables after it. -/
def Ctx.ok (sig : Sig) (Γ : Ctx) : Bool :=
  Γ.tails.all fun t ↦
    match t with
      | [] => true
      | a :: Γ' => IsType sig Γ' a

/-- The formation of a signature: each declaration is a kind or a type, closed, in the scope of
the constants before it. -/
def Sig.ok (sig : Sig) : Bool :=
  (sig.zip sig.inits).all fun (d, pre) ↦ IsKind pre [] d || IsType pre [] d

end Geb.LF

end
