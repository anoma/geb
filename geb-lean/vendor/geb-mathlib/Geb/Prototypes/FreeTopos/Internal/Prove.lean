/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Derivation

set_option doc.verso true in
/-!
# A prover for the internal language

A prover, prototyped in Lean, that computes derivations the checker
{name}`Geb.FreeTopos.Internal.check` checks. It normalizes a term innermost first: it
normalizes the children, each in its own context, then applies at the root the first rule of a
list that applies, and normalizes the result; or weak head normal forms first, an argument used
more than once reduced before it is substituted, so that its value is computed once, and a case
analysis's branches reduced only once one is selected, to a weak normal form, which leaves the
bodies of abstractions and the starts and steps of folds, to a normal form but for folds' starts
and steps, or to the normal form. The rules are the language's equations, the unfolding of the
definitions below an index, a variable of the terminal type as its element, the earlier
theorems, whose instances it finds by matching their left sides, and the hypotheses; a rule is
tried again at a node whose children a reduction rewrote.
It proves an equation by normalizing both sides to one term, by induction on the innermost
variable with a step it is given, and by induction on a rose tree in the form of the uniqueness
of its fold, each premise by normalization; with the induction hypothesis, it normalizes the
hypothesis, cuts in the normal form, and rewrites the step by it. Proofs compose: an equation of
functions by extensionality, an equation by case analysis of a variable of a coproduct anywhere
in the context, and list induction whose premises other proofs prove. The prover is not
trusted: a derivation it computes is checked.

The compiler replaces the reduction by one proved equal to it ({lit}`eval_eq_evalFast`): the
hypotheses are passed with the number of binders past which they are weakened and weakened where
a rule reads one, as the compiled checker weakens them; the rules are indexed once by the label a
term's root must have for each to apply, so that a node tries only the rules of its label; and
each equation among the hypotheses is compared with a term by its left side's renaming, folded
once, without the renaming being built.

## Main definitions

* {lit}`NormRule` — a rule the normalizer applies at a term's root.
* {lit}`tryRule`, {lit}`rootRewrite` — the rewriting of a term at its root by one rule, and by
  the first of a list that applies.
* {lit}`prepareRule`, {lit}`prepareRules` — the rules with each theorem's matching prepared
  once.
* {lit}`normStep` — one step of the normalization innermost first.
* {lit}`normalize` — the normal form of a term and its rewriting derivation.
* {lit}`byNorm`, {lit}`byNatInd`, {lit}`byListInd`, {lit}`byNatIndHyp`, {lit}`byListIndHyp`,
  {lit}`byRoseInd`, {lit}`byNormW` — the proofs of an equation.
* {lit}`byFunExt`, {lit}`bySplit`, {lit}`byListIndWith`, {lit}`byRoseIndHyp` — the proofs of an
  equation from proofs of others: of functions by extensionality, by case analysis of a variable
  of a coproduct anywhere in the context, and by list induction and rose-tree induction with each
  premise proved by a prover.
* {lit}`Depth`, {lit}`eval`, {lit}`whnf`, {lit}`normalizeW` — the depths of reduction, the
  reduction to a depth, sharing an argument's value among its uses, the weak head normal form,
  and the normal form reached through it.
* {lit}`atRoot`, {lit}`headStep`, {lit}`deepStep`, {lit}`evalStep` — the steps of the reduction
  to a depth: the rewriting at the root, the weak head normal form, and the reduction past it.
* {lit}`evalK`, {lit}`evalStepK` — the reduction under hypotheses weakened past a number of
  binders, and its step.
* {lit}`isRename`, {lit}`isWeakening` — whether a term is a pattern renamed, or weakened, decided
  without the renaming being built.
* {lit}`indexRules`, {lit}`rootRewriteK` — the rules indexed by the keys of their roots' labels,
  and the rewriting at the root by the index under weakened hypotheses.
* {lit}`evalFast` — the reduction the compiler runs in place of {lit}`eval`.

## Main statements

* {lit}`eval_eq_evalFast` — the reduction is {lit}`evalFast`, by which the compiler replaces it.

## Tags

internal language, prover, normalization, induction
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)
open Sorts
open scoped FinEnum

/-- A rule the normalizer applies at a term's root: one of the language's equations, the
equational theorem of an index at objects, whose instance is found by matching its left side, or
an equation among the hypotheses. -/
inductive NormRule where
  /-- A rule of the checker applied as it stands. -/
  | rule (r : Rule)
  /-- The unfolding of the definition of an index, and of no other. -/
  | delta (k : ℕ)
  /-- The unfolding of every definition of an index below {lit}`m` but those of a list. -/
  | deltaBelow (m : ℕ) (except : List ℕ)
  /-- A variable of the terminal type is its element. -/
  | unitVar
  /-- The equational theorem of an index at objects, from its left side to its right. -/
  | thm (j : ℕ) (θ : List Tree)
  /-- The equational theorem of an index at objects, from its left side to its right, with the
  label at the root of its left side at the objects, that left side's matching, prepared
  beforehand, and the number of its variables. -/
  | thmAt (j : ℕ) (θ : List Tree) (root : Label)
      (matching : ℕ → Term → List (Option Term) → Option (List (Option Term))) (vars : ℕ)
  /-- The equation among the hypotheses of an index, from its left side to its right. -/
  | hyp (i : ℕ)

/-- Whether a pattern's root may match a term's root, before the pattern's object variables are
instantiated: the pattern's root is a variable, or the two roots are nodes of one kind. -/
def sameShape : Label → Label → Bool
  | .var _, _ => true
  | .star, .star | .pair, .pair | .fst, .fst | .snd, .snd | .app, .app | .natRec, .natRec
    | .listRec, .listRec | .eq, .eq | .lam _, .lam _ | .roseRec _, .roseRec _ => true
  | .arr k _, .arr k' _ | .defn k _, .defn k' _ => k == k'
  | _, _ => false

/-- The matching of the pattern's variable of index {lit}`i` against a term under {lit}`d`
binders: a variable below {lit}`d` matches itself, and one from {lit}`d` on the term lowered past
the binders, where it mentions none of them, consistently with its earlier matches. -/
def matchVar (i d : ℕ) (t : Term) (σ : List (Option Term)) : Option (List (Option Term)) :=
  if i < d then (if t = Term.var i then some σ else none) else
    -- under no binders the term mentions none of theirs and is its own lowering
    let t' := if d = 0 then t else Term.rename t (· - d)
    if d = 0 ∨ Term.rename t' (· + d) = t then match σ[i - d]? with
      | some none => some (σ.set (i - d) (some t'))
      | some (some s) => if s = t' then some σ else none
      | none => if t' = Term.var (i - d) then some σ else none
    else none

/-- The matching of a node of a pattern other than a variable, of a label, against a term under
{lit}`d` binders, from the pattern's children with their matchings: the term's node has the
label and as many children, which the children match in turn, under one more binder in an
abstraction's body and a natural-number fold's step and two more in a list fold's step, the step
of a rose-tree fold, in a context of its own, matching only itself. -/
def matchNode (l : Label)
    (ps : List (Term × (ℕ → Term → List (Option Term) → Option (List (Option Term)))))
    (d : ℕ) (t : Term) (σ : List (Option Term)) : Option (List (Option Term)) :=
  if l = t.label ∧ ps.length = t.children.length then
    match l, ps, t.children with
    | .lam _, [(_, q)], [u] => q (d + 1) u σ
    | .natRec, [(_, qz), (_, qs), (_, q)], [z', s', u] =>
      ((qz d z' σ).bind (qs (d + 1) s')).bind (q d u)
    | .listRec, [(_, qz), (_, qs), (_, q)], [z', s', u] =>
      ((qz d z' σ).bind (qs (d + 2) s')).bind (q d u)
    | .roseRec _, [(s, _), (_, q)], [s', u] => if s = s' then q d u σ else none
    | _, ps, us => (ps.zip us).foldl (fun acc (q, u) ↦ acc.bind (q.2 d u)) (some σ)
  else none

/-- One step of the matching of a pattern against a term, at a node of the pattern of a label,
from the pattern's children with their matchings. -/
def matchStep (l : Label)
    (ps : List (Term × (ℕ → Term → List (Option Term) → Option (List (Option Term)))))
    (d : ℕ) (t : Term) (σ : List (Option Term)) : Option (List (Option Term)) := match l with
  | .var i => matchVar i d t σ
  | l => matchNode l ps d t σ

/-- The matching of a pattern against a term under {lit}`d` binders, the pattern's variables
from {lit}`d` on bound in the assignment to terms that do not mention the binders' variables:
the extended assignment, or nothing when they do not match. A variable below {lit}`d` matches
itself; the start and the step of a fold, in contexts of their own, match only themselves.
Lean compiles it at its full arity, so that its application to the pattern alone folds the
pattern again at each call; {lit}`prepareRules` folds a theorem's once. -/
def matchTerm (p : Term) : ℕ → Term → List (Option Term) → Option (List (Option Term)) :=
  RoseTree.para matchStep p

/-- The derivation of one rewriting after another, the identity left out. -/
def dTrans (d₁ d₂ : Deriv × Bool) : Deriv × Bool :=
  match d₁.2, d₂.2 with
  | false, _ => d₂
  | _, false => d₁
  | true, true => (RoseTree.node .trans [d₁.1, d₂.1], true)

/-- The identity derivation, marked as no rewriting. -/
def dRefl : Deriv × Bool := (RoseTree.node .refl [], false)

variable (G : Globals) (E : Array Entry) (n : ℕ)

/-- The rewriting of a term at its root by one rule: the result, and its derivation. -/
def tryRule (Γ : List Tree) (Φ : List Term) (t : Term) : NormRule → Option (Term × Deriv)
  | .rule l => (rootStep G E n Γ Φ l t).map fun t' ↦ (t', RoseTree.node l [])
  | .delta k => match t.label with
    | .defn k' _ => if k = k' then
        (rootStep G E n Γ Φ .delta t).map fun t' ↦ (t', RoseTree.node .delta [])
      else none
    | _ => none
  | .unitVar => match t.label with
    | .var i => if Γ[i]? = some one then
        (rootStep G E n Γ Φ .unitEta t).map fun t' ↦ (t', RoseTree.node .unitEta [])
      else none
    | _ => none
  | .deltaBelow m ks => match t.label with
    | .defn k' _ => if k' < m ∧ k' ∉ ks then
        (rootStep G E n Γ Φ .delta t).map fun t' ↦ (t', RoseTree.node .delta [])
      else none
    | _ => none
  | .thm j θ => do
    let a ← (E[j]?).bind Entry.language?
    let (l, _) ← eqParts a.concl
    if !sameShape l.label t.label then none else
    let σ ← matchTerm (if θ.isEmpty then l else Term.osubst θ l) 0 t
      (List.replicate a.ctx.length none)
    let σ ← σ.mapM id
    let l := Rule.thm j θ σ false
    (rootStep G E n Γ Φ l t).map fun t' ↦ (t', RoseTree.node l [])
  | .thmAt j θ root m k => if !sameShape root t.label then none else do
    let σ ← m 0 t (List.replicate k none)
    let σ ← σ.mapM id
    let l := Rule.thm j θ σ false
    (rootStep G E n Γ Φ l t).map fun t' ↦ (t', RoseTree.node l [])
  | .hyp i => (rootStep G E n Γ Φ (.rwHyp i false) t).map fun t' ↦
      (t', RoseTree.node (.rwHyp i false) [])

/-- The first rule of a list that rewrites a term at its root: the result, and its derivation. -/
def rootRewrite (rs : List NormRule) (Γ : List Tree) (Φ : List Term) (t : Term) :
    Option (Term × Deriv) :=
  rs.findSome? (tryRule G E n Γ Φ t)

/-- A rule with a theorem's matching prepared beforehand, its left side instantiated at its
objects and folded into the matching once, so that a rule tried at many nodes does neither at
each. -/
def prepareRule : NormRule → NormRule
  | .thm j θ => match (E[j]?).bind Entry.language? with
    | some a => match eqParts a.concl with
      | some (l, _) =>
        let p := if θ.isEmpty then l else Term.osubst θ l
        -- the fold applied in full, so that it is computed here rather than at each call
        .thmAt j θ p.label (RoseTree.para matchStep p) a.ctx.length
      | none => .thm j θ
    | none => .thm j θ
  | r => r

/-- The rules with each theorem's matching prepared beforehand ({lit}`prepareRule`). -/
def prepareRules (rs : List NormRule) : List NormRule := rs.map (prepareRule E)

/-- One step of the normalization innermost first, the subterms normalized by {lit}`rec`: the
children, each in its own context, then the first rule that rewrites the root and the result
normalized. -/
def normStep (rs : List NormRule)
    (rec : List Tree → List Term → Term → Option (Term × Deriv × Bool)) :
    List Tree → List Term → Term → Option (Term × Deriv × Bool) := fun Γ Φ t ↦ do
  let Γs ← childCtxs G n t.label t.children Γ Φ
  let cs ← (Γs.zip t.children).mapM fun ((Δ, Ψ), u) ↦ rec Δ Ψ u
  let t₁ := RoseTree.node t.label (cs.map Prod.fst)
  let d₁ : Deriv × Bool := if cs.any (·.2.2) then
      (RoseTree.node .cong (cs.map (·.2.1)), true)
    else dRefl
  match rootRewrite G E n rs Γ Φ t₁ with
  | some (t₂, dr) => do
    let (t₃, d₃) ← rec Γ Φ t₂
    pure (t₃, dTrans d₁ (dTrans (dr, true) d₃))
  | none => pure (t₁, d₁)

/-- The normal form of a term in a context under hypotheses, by rules, innermost first, within
a depth of {lit}`fuel`, with its rewriting derivation, marked when it rewrites. -/
def normalize (rs : List NormRule) (fuel : ℕ) :
    List Tree → List Term → Term → Option (Term × Deriv × Bool) :=
  fuel.rec (fun _ _ t ↦ some (t, dRefl)) fun _ rec ↦ normStep G E n rs rec

/-- The proof of an equation by normalizing both sides to one term. -/
def byNorm (rs : List NormRule) (fuel : ℕ) (Γ : List Tree) (Φ : List Term) (t u : Term) :
    Option Deriv := do
  let (v, d₁, _) ← normalize G E n rs fuel Γ Φ t
  let (v', d₂, _) ← normalize G E n rs fuel Γ Φ u
  if v = v' then some (RoseTree.node .join [d₁, d₂]) else none

/-- The proof of an equation in a context of a natural number variable by induction on it, with
the step {lit}`s`, each premise by normalization. -/
def byNatInd (kz ks : ℕ) (s : Term) (rs : List NormRule) (fuel : ℕ) (Γ : List Tree)
    (Φ : List Term) (t u : Term) : Option Deriv := match Γ with
  | _ :: Γ' => do
    let Φ' ← lowerHyps G n Γ' Φ
    let p₀ ← byNorm G E n rs fuel Γ' Φ' (Term.subst t (instVar (Term.arr kz [] Term.star)))
      (Term.subst u (instVar (Term.arr kz [] Term.star)))
    let p₁ ← byNorm G E n rs fuel Γ Φ (natSuccAt ks t) (Term.subst s (atVar0 t))
    let p₂ ← byNorm G E n rs fuel Γ Φ (natSuccAt ks u) (Term.subst s (atVar0 u))
    pure (RoseTree.node (.natInd kz ks s) [p₀, p₁, p₂])
  | [] => none

/-- The proof of an equation in a context of a list variable by induction on it, with the step
{lit}`s`, each premise by normalization. -/
def byListInd (kn kc : ℕ) (s : Term) (rs : List NormRule) (fuel : ℕ) (Γ : List Tree)
    (Φ : List Term) (t u : Term) : Option Deriv := match Γ with
  | c :: Γ' => do
    let a ← listPart c
    let Φ' ← lowerHyps G n Γ' Φ
    let p₀ ← byNorm G E n rs fuel Γ' Φ' (Term.subst t (instVar (Term.arr kn [a] Term.star)))
      (Term.subst u (instVar (Term.arr kn [a] Term.star)))
    let p₁ ← byNorm G E n rs fuel (c :: a :: Γ') (Φ'.map weaken2) (listConsAt kc a t)
      (Term.subst s (atVar0 (weakenElem t)))
    let p₂ ← byNorm G E n rs fuel (c :: a :: Γ') (Φ'.map weaken2) (listConsAt kc a u)
      (Term.subst s (atVar0 (weakenElem u)))
    pure (RoseTree.node (.listInd kn kc s) [p₀, p₁, p₂])
  | [] => none

/-- The proof of an equation in a context of a natural number variable by induction on it with
the induction hypothesis: each premise by normalization, the step's after the induction
hypothesis, normalized, is cut in as a hypothesis to rewrite by. -/
def byNatIndHyp (kz ks : ℕ) (rs : List NormRule) (fuel : ℕ) (Γ : List Tree) (Φ : List Term)
    (t u : Term) : Option Deriv := match Γ with
  | _ :: Γ' => do
    let Φ' ← lowerHyps G n Γ' Φ
    let p₀ ← byNorm G E n rs fuel Γ' Φ' (Term.subst t (instVar (Term.arr kz [] Term.star)))
      (Term.subst u (instVar (Term.arr kz [] Term.star)))
    let Φ₁ := Φ ++ [Term.eq t u]
    let (ψ, dψ, _) ← normalize G E n rs fuel Γ Φ₁ (Term.eq t u)
    let q ← byNorm G E n (rs ++ [.hyp (Φ₁.length)]) fuel Γ (Φ₁ ++ [ψ]) (natSuccAt ks t)
      (natSuccAt ks u)
    let ih := RoseTree.node (.convFrom (Term.eq t u)) [dψ, RoseTree.node (.hyp Φ.length) []]
    pure (RoseTree.node (.natIndHyp kz ks) [p₀, RoseTree.node (.cut ψ) [ih, q]])
  | [] => none

/-- The proof of an equation in a context of a list variable by induction on it with the
induction hypothesis: each premise by normalization, the step's after the induction hypothesis,
normalized, is cut in as a hypothesis to rewrite by. -/
def byListIndHyp (kn kc : ℕ) (rs : List NormRule) (fuel : ℕ) (Γ : List Tree) (Φ : List Term)
    (t u : Term) : Option Deriv := match Γ with
  | c :: Γ' => do
    let a ← listPart c
    let Φ' ← lowerHyps G n Γ' Φ
    let p₀ ← byNorm G E n rs fuel Γ' Φ' (Term.subst t (instVar (Term.arr kn [a] Term.star)))
      (Term.subst u (instVar (Term.arr kn [a] Term.star)))
    let Δ := c :: a :: Γ'
    let Φ₁ := Φ'.map weaken2 ++ [weakenElem (Term.eq t u)]
    let (ψ, dψ, _) ← normalize G E n rs fuel Δ Φ₁ (weakenElem (Term.eq t u))
    let q ← byNorm G E n (rs ++ [.hyp (Φ₁.length)]) fuel Δ (Φ₁ ++ [ψ]) (listConsAt kc a t)
      (listConsAt kc a u)
    let ih := RoseTree.node (.convFrom (weakenElem (Term.eq t u)))
      [dψ, RoseTree.node (.hyp Φ'.length) []]
    pure (RoseTree.node (.listIndHyp kn kc) [p₀, RoseTree.node (.cut ψ) [ih, q]])
  | [] => none

/-- The child of a node other than an application whose normalization can enable a rule at the
node's root: the pair of a component, and the datum of a fold. -/
def headChild : Label → List Term → Option ℕ
  | .fst, [_] => some 0
  | .snd, [_] => some 0
  | .natRec, [_, _, _] => some 2
  | .listRec, [_, _, _] => some 2
  | .roseRec _, [_, _] => some 1
  | _, _ => none

/-- How far the evaluator reduces a term: to its weak head normal form; to its weak normal form,
every subterm reduced but those under an abstraction and a fold's start and step; to its normal
form but for folds' starts and steps; or to its normal form. -/
inductive Depth where
  /-- The weak head normal form. -/
  | head
  /-- The weak normal form. -/
  | weak
  /-- The normal form but for the starts and steps of folds. -/
  | open
  /-- The normal form. -/
  | full
deriving DecidableEq

/-- Whether the normal form but for folds' starts and steps leaves a node's child of an index in
place: the start and the step of a fold. -/
def keepsFold (l : Label) (i : ℕ) : Bool := match l with
  | .natRec | .listRec => i < 2
  | .roseRec _ => i = 0
  | _ => false

/-- Whether the weak normal form leaves a node's child of an index in place: every child of an
abstraction, and the start and the step of a fold. -/
def keepsWeak (l : Label) (i : ℕ) : Bool := match l with
  | .lam _ => true
  | .natRec | .listRec => i < 2
  | .roseRec _ => i = 0
  | _ => false

/-- The uses of the variable of index {lit}`d` in a term, each under an abstraction and in a
fold's step counted twice, since the abstraction may be applied and the step is applied more
than once. -/
def uses : Term → ℕ → ℕ :=
  RoseTree.elim fun l cs d ↦ match l, cs with
    | .var i, _ => if i = d then 1 else 0
    | .lam _, cs => 2 * (cs.map (· (d + 1))).sum
    | .natRec, [z, s, m] => z d + 2 * s (d + 1) + m d
    | .listRec, [z, s, m] => z d + 2 * s (d + 2) + m d
    | .roseRec _, [s, m] => 2 * s (d + 1) + m d
    | _, cs => (cs.map (· d)).sum

/-- The derivation of a node's rewriting from its children's, marked when one rewrites. -/
def dCong (cs : List (Deriv × Bool)) : Deriv × Bool :=
  if cs.any (·.2) then (RoseTree.node .cong (cs.map (·.1)), true) else dRefl

/-- A reduction of terms to a depth: the reduced term in a context under hypotheses, with its
rewriting derivation, marked when it rewrites. -/
abbrev Reduction : Type := Depth → List Tree → List Term → Term → Option (Term × Deriv × Bool)

/-- The first rule that rewrites a term at its root, its result reduced to a depth by
{lit}`rec`, after the rewriting {lit}`d₁`; or the term with {lit}`d₁`. -/
def atRoot (rs : List NormRule) (rec : Reduction) (Γ : List Tree) (Φ : List Term) (dp : Depth)
    (t₁ : Term) (d₁ : Deriv × Bool) : Option (Term × Deriv × Bool) :=
  match rootRewrite G E n rs Γ Φ t₁ with
  | some (t₂, dr) => do
    let (t₃, d₃) ← rec dp Γ Φ t₂
    pure (t₃, dTrans d₁ (dTrans (dr, true) d₃))
  | none => pure (t₁, d₁)

/-- One step of the weak head normal form, the reductions of the subterms by {lit}`rec`: that of
an application is that of its function, and then, before a rule at the root, the weak normal
form of its argument when the function is an abstraction whose variable {lit}`uses` counts more
than once, so that its value is computed once rather than at each use, and its weak head normal
form when the function is not an abstraction, so that a case analysis receives its scrutinee;
that of any other node is the first rule that rewrites the root, the unfolding of a definition
receiving its arguments unreduced, else the weak head normal form of the child it depends on and
the first rule that then rewrites the root. The branches of a case analysis, abstractions, are
reduced only once one is selected. -/
def headStep (rs : List NormRule) (rec : Reduction) (Γ : List Tree) (Φ : List Term) (t : Term) :
    Option (Term × Deriv × Bool) :=
  match t.label, t.children with
  | .app, [f, u] => do
    let (f', df) ← rec .head Γ Φ f
    let (u', du) ← match f'.label, f'.children with
      | .lam _, [b] => if uses b 0 < 2 then some (u, dRefl) else rec .weak Γ Φ u
      | _, _ => rec .head Γ Φ u
    atRoot G E n rs rec Γ Φ .head (Term.app f' u') (dCong [df, du])
  | l, cs => match rootRewrite G E n rs Γ Φ t with
    | some (t₁, dr) => do
      let (t₂, d₂) ← rec .head Γ Φ t₁
      pure (t₂, dTrans (dr, true) d₂)
    | none => match headChild l cs with
      | none => some (t, dRefl)
      | some i => do
        let c ← cs[i]?
        let (c', dc) ← rec .head Γ Φ c
        if dc.2 then
          atRoot G E n rs rec Γ Φ .head (RoseTree.node l (cs.set i c'))
            (dCong ((List.range cs.length).map fun j ↦ if j = i then dc else dRefl))
        else some (t, dRefl)

/-- The reduction past the weak head normal form {lit}`w`, reached by {lit}`dw`, to a depth, the
subterms reduced by {lit}`rec`: the weak normal form reduces the children but those
{lit}`keepsWeak` leaves, the open one those but {lit}`keepsFold` leaves, each in its own
context, and the normal form every child, each in its own context; each then applies a rule at
the root, the weak and open ones where a child was rewritten, and reduces the result. The
children the weak normal form reduces are in the node's context, which it therefore does not
compute. -/
def deepStep (rs : List NormRule) (rec : Reduction) (depth : Depth) (Γ : List Tree)
    (Φ : List Term) (w : Term) (dw : Deriv × Bool) : Option (Term × Deriv × Bool) :=
  match depth with
  | .head => pure (w, dw)
  | .weak => do
    let cs ← w.children.zipIdx.mapM fun (u, i) ↦
      if keepsWeak w.label i then some (u, dRefl) else rec .weak Γ Φ u
    let t₁ := RoseTree.node w.label (cs.map Prod.fst)
    let d₁ := dTrans dw (dCong (cs.map Prod.snd))
    if cs.any (·.2.2) then atRoot G E n rs rec Γ Φ .weak t₁ d₁ else pure (t₁, d₁)
  | .open => do
    let Γs ← childCtxs G n w.label w.children Γ Φ
    let cs ← ((Γs.zip w.children).zipIdx).mapM fun (((Δ, Ψ), u), i) ↦
      if keepsFold w.label i then some (u, dRefl) else rec .open Δ Ψ u
    let t₁ := RoseTree.node w.label (cs.map Prod.fst)
    let d₁ := dTrans dw (dCong (cs.map Prod.snd))
    if cs.any (·.2.2) then atRoot G E n rs rec Γ Φ .open t₁ d₁ else pure (t₁, d₁)
  | .full => do
    let Γs ← childCtxs G n w.label w.children Γ Φ
    let cs ← (Γs.zip w.children).mapM fun ((Δ, Ψ), u) ↦ rec .full Δ Ψ u
    let t₁ := RoseTree.node w.label (cs.map Prod.fst)
    let d₁ := dCong (cs.map Prod.snd)
    match rootRewrite G E n rs Γ Φ t₁ with
    | some (t₂, dr) => do
      let (t₃, d₃) ← rec .full Γ Φ t₂
      pure (t₃, dTrans dw (dTrans d₁ (dTrans (dr, true) d₃)))
    | none => pure (t₁, dTrans dw d₁)

/-- One step of the reduction to a depth: the weak head normal form, and the reduction past it,
the subterms reduced by {lit}`rec`. -/
def evalStep (rs : List NormRule) (rec : Reduction) : Reduction := fun depth Γ Φ t ↦ do
  let (w, dw) ← headStep G E n rs rec Γ Φ t
  deepStep G E n rs rec depth Γ Φ w dw

/-- The reduction of a term in a context under hypotheses, by rules, to a depth, within a depth
of recursion of {lit}`fuel`, with its rewriting derivation, marked when it rewrites: the weak
head normal form ({lit}`headStep`) and then the reduction past it ({lit}`deepStep`). -/
def eval (rs : List NormRule) (fuel : ℕ) : Reduction :=
  fuel.rec (fun _ _ _ t ↦ some (t, dRefl)) fun _ rec ↦ evalStep G E n rs rec

/-- A reduction under weakened hypotheses: the reduction of a term to a depth in a context under
the hypotheses weakened past a number of new innermost variables, from the hypotheses before the
weakening. -/
abbrev ReductionK : Type :=
  Depth → List Tree → ℕ → List Term → Term → Option (Term × Deriv × Bool)

/-- A rewriting at the root under weakened hypotheses: the result and its derivation in a context
under the hypotheses weakened past a number of new innermost variables, from the hypotheses
before the weakening. -/
abbrev RootRewriteK : Type := List Tree → ℕ → List Term → Term → Option (Term × Deriv)

/-- {lit}`atRoot` under weakened hypotheses, by the rewriting at the root {lit}`rw`. -/
def atRootK (rw : RootRewriteK) (rec : ReductionK) (Γ : List Tree) (k : ℕ) (Φ : List Term)
    (dp : Depth) (t₁ : Term) (d₁ : Deriv × Bool) : Option (Term × Deriv × Bool) :=
  match rw Γ k Φ t₁ with
  | some (t₂, dr) => do
    let (t₃, d₃) ← rec dp Γ k Φ t₂
    pure (t₃, dTrans d₁ (dTrans (dr, true) d₃))
  | none => pure (t₁, d₁)

/-- {lit}`headStep` under weakened hypotheses, by the rewriting at the root {lit}`rw`. -/
def headStepK (rw : RootRewriteK) (rec : ReductionK) (Γ : List Tree) (k : ℕ) (Φ : List Term)
    (t : Term) : Option (Term × Deriv × Bool) :=
  match t.label, t.children with
  | .app, [f, u] => do
    let (f', df) ← rec .head Γ k Φ f
    let (u', du) ← match f'.label, f'.children with
      | .lam _, [b] => if uses b 0 < 2 then some (u, dRefl) else rec .weak Γ k Φ u
      | _, _ => rec .head Γ k Φ u
    atRootK rw rec Γ k Φ .head (Term.app f' u') (dCong [df, du])
  | l, cs => match rw Γ k Φ t with
    | some (t₁, dr) => do
      let (t₂, d₂) ← rec .head Γ k Φ t₁
      pure (t₂, dTrans (dr, true) d₂)
    | none => match headChild l cs with
      | none => some (t, dRefl)
      | some i => do
        let c ← cs[i]?
        let (c', dc) ← rec .head Γ k Φ c
        if dc.2 then
          atRootK rw rec Γ k Φ .head (RoseTree.node l (cs.set i c'))
            (dCong ((List.range cs.length).map fun j ↦ if j = i then dc else dRefl))
        else some (t, dRefl)

/-- {lit}`deepStep` under weakened hypotheses, by the rewriting at the root {lit}`rw`: a child
whose context extends the node's has the hypotheses weakened past its new variables, by the
number {lit}`childBinders` computes, rather than weakened. -/
def deepStepK (rw : RootRewriteK) (rec : ReductionK) (depth : Depth) (Γ : List Tree) (k : ℕ)
    (Φ : List Term) (w : Term) (dw : Deriv × Bool) : Option (Term × Deriv × Bool) :=
  match depth with
  | .head => pure (w, dw)
  | .weak => do
    let cs ← w.children.zipIdx.mapM fun (u, i) ↦
      if keepsWeak w.label i then some (u, dRefl) else rec .weak Γ k Φ u
    let t₁ := RoseTree.node w.label (cs.map Prod.fst)
    let d₁ := dTrans dw (dCong (cs.map Prod.snd))
    if cs.any (·.2.2) then atRootK rw rec Γ k Φ .weak t₁ d₁ else pure (t₁, d₁)
  | .open => do
    let Bs ← childBinders G n w.label w.children Γ
    let cs ← ((Bs.zip w.children).zipIdx).mapM fun (((Δ, m), u), i) ↦
      if keepsFold w.label i then some (u, dRefl) else rec .open Δ (k + m) Φ u
    let t₁ := RoseTree.node w.label (cs.map Prod.fst)
    let d₁ := dTrans dw (dCong (cs.map Prod.snd))
    if cs.any (·.2.2) then atRootK rw rec Γ k Φ .open t₁ d₁ else pure (t₁, d₁)
  | .full => do
    let Bs ← childBinders G n w.label w.children Γ
    let cs ← (Bs.zip w.children).mapM fun ((Δ, m), u) ↦ rec .full Δ (k + m) Φ u
    let t₁ := RoseTree.node w.label (cs.map Prod.fst)
    let d₁ := dCong (cs.map Prod.snd)
    match rw Γ k Φ t₁ with
    | some (t₂, dr) => do
      let (t₃, d₃) ← rec .full Γ k Φ t₂
      pure (t₃, dTrans dw (dTrans d₁ (dTrans (dr, true) d₃)))
    | none => pure (t₁, dTrans dw d₁)

/-- {lit}`evalStep` under weakened hypotheses, by the rewriting at the root {lit}`rw`. -/
def evalStepK (rw : RootRewriteK) (rec : ReductionK) : ReductionK := fun depth Γ k Φ t ↦ do
  let (w, dw) ← headStepK rw rec Γ k Φ t
  deepStepK G n rw rec depth Γ k Φ w dw

/-- {lit}`eval` under weakened hypotheses, by the rewriting at the root {lit}`rw`. -/
def evalK (rw : RootRewriteK) (fuel : ℕ) : ReductionK :=
  fuel.rec (fun _ _ _ _ t ↦ some (t, dRefl)) fun _ rec ↦ evalStepK G n rw rec

/-- One step of the reduction under weakened hypotheses is the reduction's step under the
hypotheses weakened, where its rewriting at the root and its reduction of the subterms are. -/
theorem evalStepK_eq (rs : List NormRule) (Φ : List Term) (rw : RootRewriteK)
    (hrw : ∀ Γ k t, rw Γ k Φ t = rootRewrite G E n rs Γ (Φ.map (weakenBy k)) t)
    (recK : ReductionK) (rec : Reduction)
    (hrec : ∀ dp Γ k t, recK dp Γ k Φ t = rec dp Γ (Φ.map (weakenBy k)) t)
    (dp : Depth) (Γ : List Tree) (k : ℕ) (t : Term) :
    evalStepK G n rw recK dp Γ k Φ t = evalStep G E n rs rec dp Γ (Φ.map (weakenBy k)) t := by
  -- the step passes on its hypotheses unchanged, so it reads the rewriting and the reduction
  -- only at them
  change evalStepK G n (fun Γ k _ t ↦ rw Γ k Φ t) (fun dp Γ k _ t ↦ recK dp Γ k Φ t) dp Γ k Φ t = _
  rw [show (fun Γ k (_ : List Term) t ↦ rw Γ k Φ t) =
      fun Γ k _ t ↦ rootRewrite G E n rs Γ (Φ.map (weakenBy k)) t from
    funext fun Γ ↦ funext fun k ↦ funext fun _ ↦ funext fun t ↦ hrw Γ k t,
    show (fun dp Γ k (_ : List Term) t ↦ recK dp Γ k Φ t) =
      fun dp Γ k _ t ↦ rec dp Γ (Φ.map (weakenBy k)) t from
    funext fun dp ↦ funext fun Γ ↦ funext fun k ↦ funext fun _ ↦ funext fun t ↦ hrec dp Γ k t]
  change (headStep G E n rs rec Γ (Φ.map (weakenBy k)) t).bind _ =
    (headStep G E n rs rec Γ (Φ.map (weakenBy k)) t).bind _
  refine congrArg _ (funext fun (w, dw) ↦ ?_)
  cases dp
  · rfl
  · rfl
  all_goals
    simp only [deepStepK, deepStep, childCtxs_weakenBy]
    rcases childBinders G n w.label w.children Γ with _ | Bs
    · rfl
    · simp only [Option.map_some, Option.bind_eq_bind, Option.bind_some, List.zip_map_left,
        List.zipIdx_map, List.mapM_map]
      rfl

/-- The reduction under weakened hypotheses is the reduction under the hypotheses weakened, where
its rewriting at the root is. -/
theorem evalK_eq (rs : List NormRule) (Φ : List Term) (rw : RootRewriteK)
    (hrw : ∀ Γ k t, rw Γ k Φ t = rootRewrite G E n rs Γ (Φ.map (weakenBy k)) t) (fuel : ℕ) :
    ∀ dp Γ k t, evalK G n rw fuel dp Γ k Φ t = eval G E n rs fuel dp Γ (Φ.map (weakenBy k)) t :=
  Nat.rec (motive := fun fuel ↦ ∀ dp Γ k t,
      evalK G n rw fuel dp Γ k Φ t = eval G E n rs fuel dp Γ (Φ.map (weakenBy k)) t)
    (fun _ _ _ _ ↦ rfl) (fun _ ih ↦ evalStepK_eq G E n rs Φ rw hrw _ _ ih) fuel

/-- The renamings of a node's children under a renaming at the node, each lifted past the
variables the child binds, as {lit}`Term.renameStep` lifts them. -/
def childRenamings (l : Label) (m : ℕ) (f : ℕ → ℕ) : List (ℕ → ℕ) := match l, m with
  | .lam _, 1 => [Term.liftR f]
  | .natRec, 3 => [f, Term.liftR f, f]
  | .listRec, 3 => [f, Term.liftR (Term.liftR f), f]
  | .roseRec _, 2 => [Term.liftR f, f]
  | _, m => List.replicate m f

/-- The images of a list's elements paired with one value. -/
theorem map_zip_replicate {β γ δ : Type} (g : β → δ → γ) (x : δ) :
    ∀ cs : List β, (cs.zip (List.replicate cs.length x)).map (fun p ↦ g p.1 p.2) =
      cs.map (g · x) :=
  List.rec rfl fun c cs ih ↦ by simp [List.replicate_succ, ih]

/-- The renaming at a node other than a variable is the node of its label over its children
renamed by {lit}`childRenamings`. -/
theorem renameStep_eq (l : Label) (cs : List (Term × ((ℕ → ℕ) → Term))) (f : ℕ → ℕ)
    (hl : ∀ i, l ≠ .var i) :
    Term.renameStep l cs f =
      RoseTree.node l ((cs.zip (childRenamings l cs.length f)).map fun p ↦ p.1.2 p.2) := by
  cases l
  case var => exact (hl _ rfl).elim
  all_goals rcases cs with _ | ⟨a, _ | ⟨b, _ | ⟨c, _ | ⟨d, cs⟩⟩⟩⟩ <;>
    simp [Term.renameStep, childRenamings, List.replicate_succ, map_zip_replicate]

/-- Whether tests hold of a list of terms, the first of the first, and so on, as many terms as
tests. -/
def pairsHold (ps : List (Term → Bool)) (us : List Term) : Bool :=
  ps.length == us.length && (ps.zip us).all fun p ↦ p.1 p.2

/-- Tests that each hold of exactly one term hold of a list exactly when it is the list of
those terms. -/
theorem pairsHold_iff {β : Type} (P : β → Term → Bool) (F : β → Term) :
    ∀ xs : List β, (∀ x ∈ xs, ∀ u, P x u = true ↔ u = F x) →
      ∀ us, pairsHold (xs.map P) us = true ↔ us = xs.map F :=
  List.rec (fun _ us ↦ by cases us <;> simp [pairsHold]) fun x xs ih h us ↦ by
    have ih' := ih fun y hy ↦ h y (List.mem_cons_of_mem x hy)
    rcases us with _ | ⟨u, us⟩
    · simp [pairsHold]
    · have hx := h x List.mem_cons_self u
      have hs := ih' us
      simp only [pairsHold, List.map_cons, List.length_cons, List.zip_cons_cons, List.all_cons,
        Bool.and_eq_true, beq_iff_eq, Nat.add_right_cancel_iff] at hs ⊢
      rw [List.cons.injEq, ← hx, ← hs]
      exact ⟨fun ⟨a, b, c⟩ ↦ ⟨b, a, c⟩, fun ⟨b, a, c⟩ ↦ ⟨a, b, c⟩⟩

/-- One step of the test whether a term is a pattern renamed, at a node of the pattern, from its
children's tests: a variable's renaming, or the node's label over its children each renamed as
{lit}`childRenamings` lifts the renaming. -/
def isRenameStep (l : Label) (cs : List ((ℕ → ℕ) → Term → Bool)) (f : ℕ → ℕ) (t : Term) :
    Bool := match l with
  | .var i => t.label == .var (f i) && t.children.isEmpty
  | l => t.label == l &&
      pairsHold ((cs.zip (childRenamings l cs.length f)).map fun p ↦ p.1 p.2) t.children

/-- Whether a term is a pattern renamed by a renaming, decided without the renaming being built:
its nodes compared with the pattern's in turn. -/
def isRename : Term → (ℕ → ℕ) → Term → Bool := RoseTree.elim isRenameStep

/-- The test at a node other than a variable holds of a term exactly when it is the node
renamed, where the tests at its children hold exactly of their renamings. -/
theorem isRenameStep_iff (l : Label) (cs : List Term) (hl : ∀ i, l ≠ .var i)
    (ih : ∀ c ∈ cs, ∀ f t, isRename c f t = true ↔ t = Term.rename c f) (f : ℕ → ℕ) (t : Term) :
    isRenameStep l (cs.map isRename) f t = true ↔
      t = Term.renameStep l (cs.map fun c ↦ (c, Term.rename c)) f := by
  have key (a : Label) (us : List Term) :
      t = RoseTree.node a us ↔ a = t.label ∧ us = t.children :=
    eq_comm.trans RoseTree.node_eq_iff
  rw [renameStep_eq l _ f hl, key, List.length_map]
  have hs : isRenameStep l (cs.map isRename) f t = (t.label == l &&
      pairsHold (((cs.zip (childRenamings l cs.length f))).map fun p ↦ isRename p.1 p.2)
        t.children) := by
    cases l
    case var => exact (hl _ rfl).elim
    all_goals simp [isRenameStep, List.zip_map_left, List.map_map, Function.comp_def]
  rw [hs, Bool.and_eq_true, beq_iff_eq, eq_comm (a := l),
    pairsHold_iff (fun p u ↦ isRename p.1 p.2 u) (fun p ↦ Term.rename p.1 p.2) _
      (fun x hx u ↦ ih x.1 (List.of_mem_zip hx).1 x.2 u), List.zip_map_left, List.map_map,
    eq_comm (b := t.children)]
  rfl

/-- The test holds of a term exactly when it is the pattern renamed. -/
theorem isRename_iff : ∀ (p : Term) (f : ℕ → ℕ) (t : Term),
    isRename p f t = true ↔ t = Term.rename p f :=
  RoseTree.ind fun l cs ih f t ↦ by
    rw [isRename, RoseTree.elim_node, ← isRename, Term.rename_node]
    cases l
    case var i =>
      rw [Term.renameStep, Term.var, show t = RoseTree.node (.var (f i)) [] ↔ _ from
        eq_comm.trans RoseTree.node_eq_iff]
      simp only [isRenameStep, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff]
      exact ⟨fun h ↦ ⟨h.1.symm, h.2.symm⟩, fun h ↦ ⟨h.1.symm, h.2.symm⟩⟩
    all_goals exact isRenameStep_iff _ cs (fun _ h ↦ by cases h) ih f t

/-- Whether a term is a pattern weakened past new innermost variables, decided without the
weakening being built. -/
def isWeakening (k : ℕ) (p t : Term) : Bool := if k = 0 then t == p else isRename p (· + k) t

/-- The test holds of a term exactly when it is the pattern weakened. -/
theorem isWeakening_iff (k : ℕ) (p t : Term) : isWeakening k p t = true ↔ t = weakenBy k p := by
  by_cases hk : k = 0 <;> simp [isWeakening, weakenBy, hk, isRename_iff]

/-- The equations among hypotheses prepared for rewriting: each one's sides, and the test of
its left side's renamings folded once ({lit}`isRename`). -/
abbrev PreparedHyps : Type := List (Option (Term × Term × ((ℕ → ℕ) → Term → Bool)))

/-- The hypotheses prepared for rewriting, each equation's test folded here rather than at each
use. -/
def prepareHyps (Φ : List Term) : PreparedHyps :=
  -- the fold applied in full, so that it is computed here rather than at each call
  Φ.map fun ψ ↦ (eqParts ψ).map fun p ↦ (p.1, p.2, RoseTree.elim isRenameStep p.1)

/-- The rewriting of a term at its root by a rule under weakened hypotheses, the equations among
them prepared in {lit}`hs`: an equation is weakened only where the term is its left side
weakened ({lit}`isWeakening`), a rule of the checker by {lit}`rootStepK`, and the other rules
under none of the hypotheses, which they do not read. -/
def tryRuleK (Γ : List Tree) (k : ℕ) (Φ : List Term) (hs : PreparedHyps) (t : Term) :
    NormRule → Option (Term × Deriv)
  | .rule l => (rootStepK G E n Γ k Φ l t).map fun t' ↦ (t', RoseTree.node l [])
  | .hyp i => match hs[i]? with
    | some (some (l, r, test)) => if (if k = 0 then t == l else test (· + k) t) then
        some (weakenBy k r, RoseTree.node (.rwHyp i false) [])
      else none
    | _ => none
  | r => tryRule G E n Γ [] t r

/-- The rewriting by a rule under weakened hypotheses is the rule's under the hypotheses
weakened. -/
theorem tryRuleK_eq (Γ : List Tree) (k : ℕ) (Φ : List Term) (t : Term) (r : NormRule) :
    tryRuleK G E n Γ k Φ (prepareHyps Φ) t r = tryRule G E n Γ (Φ.map (weakenBy k)) t r := by
  have h (l : Rule) (hl : rootHyps l k Φ = []) :
      rootStep G E n Γ [] l t = rootStep G E n Γ (Φ.map (weakenBy k)) l t :=
    hl ▸ rootStep_rootHyps G E n Γ l k Φ t
  have hthm (j : ℕ) (θ : List Tree) (σ : List Term) (b : Bool) :=
    h (.thm j θ σ b) rfl
  cases r with
  | rule l => simp only [tryRuleK, tryRule, rootStepK_eq]
  | hyp i =>
    simp only [tryRuleK, tryRule, rootStep, prepareHyps, List.getElem?_map]
    rcases Φ[i]? with _ | ψ
    · rfl
    · simp only [Option.map_some, Option.bind_some, eqParts_weakenBy]
      rcases eqParts ψ with _ | ⟨l, r⟩
      · rfl
      · change (if isWeakening k l t then _ else _) = _
        by_cases hl : t = weakenBy k l
        · simp [hl, (isWeakening_iff k l _).mpr rfl]
        · simp [hl, Bool.eq_false_iff.mpr (mt (isWeakening_iff k l t).mp hl)]
  | delta => simp only [tryRuleK, tryRule, h .delta rfl]
  | deltaBelow => simp only [tryRuleK, tryRule, h .delta rfl]
  | unitVar => simp only [tryRuleK, tryRule, h .unitEta rfl]
  | thm => simp only [tryRuleK, tryRule, hthm]
  | thmAt => simp only [tryRuleK, tryRule, hthm]

/-- The key of a label that a rule's root must have for the rule to rewrite at it: one for each
kind of node, and one for each index of a primitive arrow and of a definition. -/
def Label.rootKey : Label → ℕ
  | .var _ => 0
  | .star => 1
  | .pair => 2
  | .fst => 3
  | .snd => 4
  | .lam _ => 5
  | .app => 6
  | .natRec => 7
  | .listRec => 8
  | .roseRec _ => 9
  | .eq => 10
  | .arr k _ => 11 + 2 * k
  | .defn k _ => 12 + 2 * k

/-- The key of the labels at which a rule of the checker may rewrite a term at its root, where
there is one. -/
def Rule.rootKey? : Rule → Option ℕ
  | .beta | .caseInl _ _ | .caseInr _ _ => some 6
  | .fstPair => some 3
  | .sndPair => some 4
  | .pairEta => some 2
  | .natZero _ | .natSucc _ => some 7
  | .listNil _ | .listCons _ => some 8
  | .roseNode _ _ _ => some 9
  | _ => none

/-- The key of the labels at which a pattern of a root label may match, where there is one: every
label's, where the root is a variable, else its own. -/
def Label.patternKey? : Label → Option ℕ
  | .var _ => none
  | l => some l.rootKey

/-- The key of the labels at which a rule of the normalizer may rewrite a term at its root, where
there is one: a theorem's is that of the root of its left side. -/
def NormRule.rootKey? : NormRule → Option ℕ
  | .rule l => l.rootKey?
  | .delta k => some (12 + 2 * k)
  | .unitVar => some 0
  | .thm j _ => ((E[j]?).bind Entry.language?).bind fun a ↦
      (eqParts a.concl).bind fun p ↦ p.1.label.patternKey?
  | .thmAt _ _ root _ _ => root.patternKey?
  | _ => none

/-- Whether a rule of a key, where it has one, may rewrite at a label of the key {lit}`k`: it has
no key, or that one. -/
def keyFits (k : ℕ) : Option ℕ → Bool
  | none => true
  | some k' => k' == k

/-- A pattern's root may match a term's only where their keys fit. -/
theorem sameShape_eq_false (l l' : Label) (h : keyFits l'.rootKey l.patternKey? = false) :
    sameShape l l' = false := by
  cases l <;> cases l' <;> simp_all [sameShape, keyFits, Label.patternKey?, Label.rootKey] <;>
    omega

/-- A rule of the checker rewrites no term at its root of a label its key does not fit. -/
theorem rootStep_eq_none (Γ : List Tree) (Φ : List Term) (l : Rule) (t : Term)
    (h : keyFits t.label.rootKey l.rootKey? = false) : rootStep G E n Γ Φ l t = none := by
  cases l <;> simp only [Rule.rootKey?, keyFits, Bool.true_eq_false] at h <;> unfold rootStep <;>
    split <;> simp_all [Label.rootKey]

/-- A rule of the normalizer rewrites no term at its root of a label its key does not fit. -/
theorem tryRule_eq_none (Γ : List Tree) (Φ : List Term) (t : Term) (r : NormRule)
    (h : keyFits t.label.rootKey (r.rootKey? E) = false) : tryRule G E n Γ Φ t r = none := by
  cases r with
  | rule l => simp [tryRule, rootStep_eq_none G E n Γ Φ l t h]
  | delta k =>
    simp only [tryRule]
    cases hl : t.label <;> simp_all [NormRule.rootKey?, keyFits, Label.rootKey]
    omega
  | unitVar =>
    simp only [tryRule]
    cases hl : t.label <;> simp_all [NormRule.rootKey?, keyFits, Label.rootKey]
  | thm j θ =>
    simp only [NormRule.rootKey?] at h
    cases ha : (E[j]?).bind Entry.language? with
    | none => simp [tryRule, ha]
    | some a =>
      cases hp : eqParts a.concl with
      | none => simp [tryRule, ha, hp]
      | some p =>
        simp only [ha, hp, Option.bind_some] at h
        simp [tryRule, ha, hp, sameShape_eq_false p.1.label t.label h]
  | thmAt j θ root m k =>
    simp [tryRule, sameShape_eq_false root t.label h]
  | _ => simp [NormRule.rootKey?, keyFits] at h

/-- The matching of a pattern at objects has the shape of the pattern's root. -/
theorem sameShape_osubst (θ : List Tree) (l l' : Label) :
    sameShape (l.osubst θ) l' = sameShape l l' := by
  cases l <;> cases l' <;> rfl

/-- A rule with a theorem's matching prepared beforehand rewrites as the rule does. -/
theorem tryRule_prepareRule (Γ : List Tree) (Φ : List Term) (t : Term) (r : NormRule) :
    tryRule G E n Γ Φ t (prepareRule E r) = tryRule G E n Γ Φ t r := by
  cases r with
  | thm j θ =>
    cases ha : (E[j]?).bind Entry.language? with
    | none => simp only [prepareRule, ha]
    | some a =>
      cases hp : eqParts a.concl with
      | none => simp only [prepareRule, ha, hp]
      | some p =>
        have hs : sameShape (if θ.isEmpty then p.1 else Term.osubst θ p.1).label t.label =
            sameShape p.1.label t.label := by
          split
          · rfl
          · rw [← RoseTree.node_label_children p.1, Term.osubst_node, RoseTree.label_node,
              sameShape_osubst, RoseTree.label_node]
        simp only [prepareRule, ha, hp, tryRule, hs, Option.bind_eq_bind, Option.bind_some]
        rfl
  | _ => rfl

/-- The first element of a filtered list at which a partial function has a value is the list's,
where the function has none at the elements the filter drops. -/
theorem findSome?_filter {α β : Type} (p : α → Bool) (f : α → Option β) :
    ∀ l : List α, (∀ a ∈ l, p a = false → f a = none) → (l.filter p).findSome? f = l.findSome? f :=
  List.rec (fun _ ↦ rfl) fun a l ih h ↦ by
    have ih' := ih fun b hb ↦ h b (List.mem_cons_of_mem a hb)
    cases hp : p a
    · rw [List.filter_cons_of_neg (by simp [hp]), ih', List.findSome?_cons,
        h a List.mem_cons_self hp]
    · rw [List.filter_cons_of_pos hp, List.findSome?_cons, List.findSome?_cons, ih']

/-- The rules indexed by the keys of the labels at which they may rewrite: for each key of a
rule, the rules that may rewrite at a label of it, in order, and the rules without a key, which
alone may rewrite at a label of another key. -/
def indexRules (rs : List NormRule) : List (ℕ × List NormRule) × List NormRule :=
  let kr := rs.map fun r ↦ (r.rootKey? E, r)
  ((kr.filterMap (·.1)).eraseDups.map fun k ↦ (k, (kr.filter (keyFits k ·.1)).map Prod.snd),
    (kr.filter fun p ↦ p.1.isNone).map Prod.snd)

/-- The rules of an index that may rewrite at a label of a key. -/
def ruleBucket (idx : List (ℕ × List NormRule) × List NormRule) (k : ℕ) : List NormRule :=
  (idx.1.lookup k).getD idx.2

/-- The lookup of a key in the list of keys paired with their images. -/
theorem lookup_map_pair {β : Type} (F : ℕ → β) (k : ℕ) :
    ∀ ks : List ℕ, (ks.map fun k' ↦ (k', F k')).lookup k = if k ∈ ks then some (F k) else none :=
  List.rec rfl fun k' ks ih ↦ by
    by_cases h : k = k'
    · subst h
      simp
    · simp only [List.map_cons, List.lookup, beq_false_of_ne h, ih, List.mem_cons, h, false_or]

/-- The rules of an index that may rewrite at a label of a key are the rules its key fits. -/
theorem ruleBucket_indexRules (rs : List NormRule) (k : ℕ) :
    ruleBucket (indexRules E rs) k = rs.filter fun r ↦ keyFits k (r.rootKey? E) := by
  simp only [ruleBucket, indexRules, lookup_map_pair]
  split
  · simp [List.filter_map, Function.comp_def]
  · rename_i hk
    simp only [Option.getD_none, List.filter_map, List.map_map, Function.comp_def, List.map_id']
    refine List.filter_congr fun r hr ↦ ?_
    rcases h : r.rootKey? E with _ | k'
    · rfl
    · have : k' ≠ k := fun e ↦ hk (List.mem_eraseDups.mpr (List.mem_filterMap.mpr
        ⟨(r.rootKey? E, r), List.mem_map_of_mem hr, by simp [h, e]⟩))
      simp [keyFits, this]

/-- The rewriting at the root under weakened hypotheses by an index of rules: the first rule
of the term's label's key that rewrites it. -/
def rootRewriteK (idx : List (ℕ × List NormRule) × List NormRule) (hs : PreparedHyps) :
    RootRewriteK :=
  fun Γ k Φ t ↦ (ruleBucket idx t.label.rootKey).findSome? (tryRuleK G E n Γ k Φ hs t)

/-- The rewriting at the root under weakened hypotheses by the index of the prepared rules is
the rewriting by the rules under the hypotheses weakened. -/
theorem rootRewriteK_eq (rs : List NormRule) (Γ : List Tree) (k : ℕ) (Φ : List Term)
    (t : Term) :
    rootRewriteK G E n (indexRules E (prepareRules E rs)) (prepareHyps Φ) Γ k Φ t =
      rootRewrite G E n rs Γ (Φ.map (weakenBy k)) t := by
  have hk : tryRuleK G E n Γ k Φ (prepareHyps Φ) t = tryRule G E n Γ (Φ.map (weakenBy k)) t :=
    funext (tryRuleK_eq G E n Γ k Φ t)
  simp only [rootRewriteK, ruleBucket_indexRules, hk, rootRewrite]
  rw [findSome?_filter _ _ _ fun r _ h ↦ tryRule_eq_none G E n Γ _ t r h, prepareRules,
    List.findSome?_map]
  exact congrArg (List.findSome? · rs) (funext fun r ↦ tryRule_prepareRule G E n Γ _ t r)

/-- The reduction the compiler runs in place of {lit}`eval`: the rules prepared and indexed by
the keys of their roots once, the hypotheses prepared once, and the hypotheses weakened where a
rule reads them. -/
def evalFast (rs : List NormRule) (fuel : ℕ) : Reduction :=
  let idx := indexRules E (prepareRules E rs)
  fun dp Γ Φ t ↦ evalK G n (rootRewriteK G E n idx (prepareHyps Φ)) fuel dp Γ 0 Φ t

/-- The reduction is {lit}`evalFast`, by which the compiler replaces it. -/
@[csimp] theorem eval_eq_evalFast : @eval = @evalFast := by
  funext G E n rs fuel dp Γ Φ t
  have h := evalK_eq G E n rs Φ _ (fun Γ k t ↦ rootRewriteK_eq G E n rs Γ k Φ t) fuel dp Γ 0 t
  rw [map_weakenBy_zero] at h
  exact h.symm

/-- The weak head normal form of a term, by {lit}`eval`. -/
def whnf (rs : List NormRule) (fuel : ℕ) :
    List Tree → List Term → Term → Option (Term × Deriv × Bool) :=
  eval G E n rs fuel .head

/-- The normal form of a term reached through its weak head normal form, by {lit}`eval`: a fold
whose datum computes selects its case before the cases are normalized. -/
def normalizeW (rs : List NormRule) (fuel : ℕ) :
    List Tree → List Term → Term → Option (Term × Deriv × Bool) :=
  eval G E n rs fuel .full

/-- The proof of an equation by normalizing both sides, weak head normal forms first, to one
term. -/
def byNormW (rs : List NormRule) (fuel : ℕ) (Γ : List Tree) (Φ : List Term) (t u : Term) :
    Option Deriv := do
  let (v, d₁, _) ← normalizeW G E n rs fuel Γ Φ t
  let (v', d₂, _) ← normalizeW G E n rs fuel Γ Φ u
  if v = v' then some (RoseTree.node .join [d₁, d₂]) else none

/-- A prover of equations: a derivation of the equation of two terms in a context under
hypotheses. -/
abbrev Prover : Type := List Tree → List Term → Term → Term → Option Deriv

/-- The abstraction of a term over its variable of index {lit}`i`, of the type {lit}`c`: the
function whose application to that variable is the term. -/
def abstractVar (i : ℕ) (c : Tree) (t : Term) : Term :=
  Term.lam c (Term.subst (weaken1 t) fun j ↦ if j = i + 1 then Term.var 0 else Term.var j)

/-- The proof of an equation of functions by the proof, by {lit}`prove`, of the equation of
their applications to a new variable. -/
def byFunExt (prove : Prover) : Prover := fun Γ Φ f g ↦ do
  let (a, _) ← (typeIn G n Γ f).bind expParts
  let d ← prove (a :: Γ) (Φ.map weaken1) (Term.app (weaken1 f) (Term.var 0))
    (Term.app (weaken1 g) (Term.var 0))
  pure (RoseTree.node .funExt [d])

/-- The proof of an equation by case analysis on the variable of index {lit}`i`, of a coproduct
whose injections are the primitives of indices {lit}`kl` and {lit}`kr`, each case proved by
{lit}`prove`: the sides abstracted over the variable are equal functions, by extensionality and
the case analysis of the new, innermost variable, and the equation follows, cut in as a
hypothesis, by applying them to the variable. -/
def bySplit (kl kr i : ℕ) (prove : Prover) : Prover := fun Γ Φ t u ↦ do
  let c ← Γ[i]?
  let (a, b) ← coprodParts c
  let F := abstractVar i c t
  let H := abstractVar i c u
  let inj (k : ℕ) (s : Term) : Term := Term.app (weaken1 s) (Term.arr k [a, b] (Term.var 0))
  let q₀ ← prove (a :: Γ) (Φ.map weaken1) (inj kl F) (inj kl H)
  let q₁ ← prove (b :: Γ) (Φ.map weaken1) (inj kr F) (inj kr H)
  let pψ := RoseTree.node .funExt [RoseTree.node (.coprodInd kl kr) [q₀, q₁]]
  let dχ := RoseTree.node .cong [RoseTree.node .beta [], RoseTree.node .beta []]
  let pχ := RoseTree.node .join [RoseTree.node .cong
    [RoseTree.node (.rwHyp Φ.length false) [], RoseTree.node .refl []], RoseTree.node .refl []]
  let χ := Term.eq (Term.app F (Term.var i)) (Term.app H (Term.var i))
  pure (RoseTree.node (.cut (Term.eq F H)) [pψ, RoseTree.node (.convFrom χ) [dχ, pχ]])

/-- The proof of an equation in a context of a list variable by induction on it with the
induction hypothesis, each premise by its prover: the empty list's, and the construction's
with the induction hypothesis the last of its hypotheses. -/
def byListIndWith (kn kc : ℕ) (p₀ p₁ : Prover) : Prover := fun Γ Φ t u ↦ match Γ with
  | c :: Γ' => do
    let a ← listPart c
    let Φ' ← lowerHyps G n Γ' Φ
    let d₀ ← p₀ Γ' Φ' (Term.subst t (instVar (Term.arr kn [a] Term.star)))
      (Term.subst u (instVar (Term.arr kn [a] Term.star)))
    let d₁ ← p₁ (c :: a :: Γ') (Φ'.map weaken2 ++ [weakenElem (Term.eq t u)])
      (listConsAt kc a t) (listConsAt kc a u)
    pure (RoseTree.node (.listIndHyp kn kc) [d₀, d₁])
  | [] => none

/-- The proof of an equation in a context of a rose tree alone by induction in the form of the
uniqueness of the fold, with the step {lit}`s` at the label and the list of the values at the
children, each premise by normalization. -/
def byRoseInd (kn kl kc : ℕ) (s : Term) (rs : List NormRule) (fuel : ℕ) (Γ : List Tree)
    (t u : Term) : Option Deriv := match Γ with
  | [r] => do
    let (a, _) ← roseParts r
    let C ← typeIn G n Γ t
    let p₁ ← byNorm G E n rs fuel [list r, a] [] (roseNodeAt kn r a t)
      (Term.subst s (atVar0 (roseMapAt kl kc C t)))
    let p₂ ← byNorm G E n rs fuel [list r, a] [] (roseNodeAt kn r a u)
      (Term.subst s (atVar0 (roseMapAt kl kc C u)))
    pure (RoseTree.node (.roseInd kn kl kc s) [p₁, p₂])
  | _ => none

/-- The proof of an equation under no hypotheses by induction on the innermost variable, of a
rose-tree type, with the induction hypothesis, the premise at a construction proved by {lit}`p`
under the hypothesis that the equation holds at each child. -/
def byRoseIndHyp (kn kl kc : ℕ) (p : Prover) : Prover := fun Γ Φ t u ↦ match Γ, Φ with
  | r :: Γ', [] => do
    let (a, _) ← roseParts r
    let d ← p (list r :: a :: Γ') [roseHyp kl kc (Term.eq t u)] (roseNodeAt kn r a t)
      (roseNodeAt kn r a u)
    pure (RoseTree.node (.roseIndHyp kn kl kc) [d])
  | _, _ => none

end Geb.FreeTopos.Internal

end
