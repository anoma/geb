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
