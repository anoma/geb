/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.FinEnum
public import Geb.Mathlib.Data.W.Basic
public import Geb.Prototypes.RoseTree.Basic

set_option doc.verso true in
/-!
# First-order unification of rose trees

Rose trees over the labels {lit}`α ⊕ ℕ` are first-order terms with metavariables: a node
labelled {lit}`Sum.inr x` is the metavariable {lit}`x`, and every other node a function symbol
applied to its children. A substitution assigns trees to metavariables, and a unifier of a
list of equations is a substitution making the two sides of each equal. Robinson's algorithm
\[Robinson1965\] finds a most general unifier of a unifiable list and fails on any other: it
removes an equation whose sides are equal, binds a metavariable to the other side unless it
occurs there, decomposes an equation between nodes of one label and arity into the equations
of their children, and fails at nodes of different labels or arities.

The algorithm is a step function on a state of the substitution found and the equations that
remain, iterated within a budget of steps. A state that has not finished when the budget is
spent is reported as exhausted, distinct from a failure to unify.

## Main definitions

* {lit}`Meta`, {lit}`mvar`, {lit}`embed` — trees with metavariables, a metavariable, and the
  embedding of trees without them.
* {lit}`substM`, {lit}`occurs`, {lit}`ground` — substitution, the occurs check, and the
  instantiation of every remaining metavariable by one tree.
* {lit}`Unifier`, {lit}`unifyStep` — the state of the algorithm and its step.
* {lit}`Unified`, {lit}`unify`, {lit}`unifyFrom` — the outcome of the algorithm within a budget,
  from no substitution or continuing from one.

## Main statements

* {lit}`substM_embed` — a substitution leaves a tree without metavariables unchanged.
* {lit}`ground_embed` — instantiation recovers a tree without metavariables.

## Implementation notes

The substitution is kept idempotent: a metavariable is bound to a tree to which the
substitution has been applied and in which it does not occur, and the binding is applied to the
earlier bindings, so that one application of the substitution reaches every assigned
metavariable. Each equation is substituted when it is taken from the list.

## References

* \[Robinson1965\]

## Tags

unification, first-order term, metavariable, rose tree
-/

set_option doc.verso true

@[expose] public section

namespace Geb.RoseTree

open scoped FinEnum

variable {α : Type}

/-- Rose trees with metavariables: a node labelled {lit}`Sum.inr x` is the metavariable
{lit}`x`. -/
abbrev Meta (α : Type) : Type := RoseTree (α ⊕ ℕ)

/-- The metavariable of an index. -/
def mvar (x : ℕ) : Meta α := node (.inr x) []

/-- A tree without metavariables, as a tree with them. -/
def embed : RoseTree α → Meta α := map Sum.inl

/-- A substitution: metavariables with the trees assigned to them. -/
abbrev MSubst (α : Type) : Type := List (ℕ × Meta α)

/-- Apply a substitution, replacing each metavariable it assigns. -/
def substM (θ : MSubst α) : Meta α → Meta α :=
  elim fun l cs ↦
    match l with
    | .inl a => node (.inl a) cs
    | .inr x => (θ.lookup x).getD (node (.inr x) cs)

/-- Whether a metavariable occurs in a tree. -/
def occurs (x : ℕ) : Meta α → Bool :=
  elim fun l bs ↦
    match l with
    | .inl _ => bs.any id
    | .inr y => y == x || bs.any id

/-- Instantiate every metavariable by one tree. -/
def ground (d : RoseTree α) : Meta α → RoseTree α :=
  elim fun l cs ↦
    match l with
    | .inl a => node a cs
    | .inr _ => d

/-- A substitution leaves a tree without metavariables unchanged. -/
theorem substM_embed (θ : MSubst α) (t : RoseTree α) : substM θ (embed t) = embed t :=
  ind (P := fun t ↦ substM θ (embed t) = embed t) (fun a cs ih ↦ by
    simp only [embed, map_node, substM, elim_node, List.map_map] at ih ⊢
    congr 1
    exact List.map_congr_left fun c hc ↦ ih c hc) t

/-- Instantiation recovers a tree without metavariables. -/
theorem ground_embed (d t : RoseTree α) : ground d (embed t) = t :=
  ind (P := fun t ↦ ground d (embed t) = t) (fun a cs ih ↦ by
    simp only [embed, map_node, ground, elim_node, List.map_map] at ih ⊢
    exact congrArg (node a) ((List.map_congr_left fun c hc ↦ ih c hc).trans cs.map_id)) t

/-- The state of unification: running, with the substitution found and the equations that
remain; solved, with a unifier; or failed, at an equation whose sides do not unify. -/
inductive Unifier (α : Type) where
  /-- The substitution found and the equations that remain. -/
  | running (θ : MSubst α) (eqs : List (Meta α × Meta α))
  /-- A unifier of every equation. -/
  | solved (θ : MSubst α)
  /-- An equation, substituted, whose sides do not unify. -/
  | clash (s t : Meta α)

/-- Bind a metavariable to a tree, unless it occurs there, applying the binding to the earlier
bindings. -/
def bindMVar (θ : MSubst α) (x : ℕ) (u : Meta α) (rest : List (Meta α × Meta α)) :
    Unifier α :=
  if occurs x u then .clash (mvar x) u
  else .running ((x, u) :: θ.map fun p ↦ (p.1, substM [(x, u)] p.2)) rest

/-- One step of unification on the first remaining equation, its sides substituted: remove it
when they are equal, bind a metavariable, decompose nodes of one label and arity, or fail. -/
def unifyStep [DecidableEq α] : Unifier α → Unifier α
  | .running θ [] => .solved θ
  | .running θ ((s, t) :: rest) =>
    let s := substM θ s
    let t := substM θ t
    if s = t then .running θ rest
    else
      match s.label, t.label with
      | .inr x, _ => bindMVar θ x t rest
      | _, .inr y => bindMVar θ y s rest
      | .inl a, .inl b =>
        if a = b ∧ s.children.length = t.children.length then
          .running θ (s.children.zip t.children ++ rest)
        else .clash s t
  | u => u

/-- The outcome of unification within a budget: a unifier, a failure, or the budget spent. -/
inductive Unified (α : Type) where
  /-- A most general unifier. -/
  | solved (θ : MSubst α)
  /-- The equation, substituted, at which unification fails. -/
  | clash (s t : Meta α)
  /-- The budget was spent before unification finished. -/
  | exhausted

/-- Unify a list of equations within a budget of steps, continuing from a substitution found
before, which the result extends. -/
def unifyFrom [DecidableEq α] (fuel : ℕ) (θ : MSubst α) (eqs : List (Meta α × Meta α)) :
    Unified α :=
  match Nat.repeat unifyStep fuel (.running θ eqs) with
  | .solved θ => .solved θ
  | .clash s t => .clash s t
  | .running _ _ => .exhausted

/-- Unify a list of equations within a budget of steps. -/
def unify [DecidableEq α] (fuel : ℕ) (eqs : List (Meta α × Meta α)) : Unified α :=
  unifyFrom fuel [] eqs

end Geb.RoseTree

end
