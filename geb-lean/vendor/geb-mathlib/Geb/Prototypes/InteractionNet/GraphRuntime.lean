/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.InteractionNet.ArrayContraction
public import Geb.Prototypes.InteractionNet.GraphConfluence

set_option doc.verso true in
/-!
# An executable finite graph reducer

The runtime stores a finite indexed cell family and an array of wire partners. It checks
candidate active pairs against the rule table, allocates the selected replacement and
executes array contraction. Following each cell's principal wire gives a complete list of
candidate partners and a deterministic default schedule. Every successful step represents
one graph contraction; failure to find a redex means the represented graph is normal.

## Main definitions

* {lit}`GraphRuntime.State` — finite cells, their symbols and array-backed wiring.
* {lit}`GraphRuntime.redexAt?` — check one candidate pair against the graph and rule table.
* {lit}`GraphRuntime.step` — execute the first available active pair.

## Main statements

* {lit}`GraphRuntime.step_refines` — a runtime step is a permitted abstract graph step.
* {lit}`GraphRuntime.normal_of_step_none` — an exhausted redex search represents a normal graph.

## Tags

interaction net, runtime, graph reduction, scheduler, refinement, normal form
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.GraphRuntime

open scoped FinEnum

universe u

variable {α : Type u} {arity : α → ℕ} {boundary : ℕ}

/-- Finite indexed cells and their symbols, with array-backed wiring and an ordered boundary. -/
abbrev State (arity : α → ℕ) (boundary : ℕ) :=
  Σ cells : ℕ, Σ label : Fin cells → α, ArrayNet arity label (Fin boundary)

/-- Read a runtime state as a finite graph presentation. -/
def read (n : State arity boundary) : FiniteNet arity boundary := ⟨n.1, n.2.1, n.2.2.read⟩

/-- Materialize cell symbols once, preventing lookup chains through earlier reindexings. -/
def labelTable {cells : ℕ} (label : Fin cells → α) : Vector α cells :=
  ⟨(List.ofFn label).toArray, by simp only [List.size_toArray, List.length_ofFn]⟩

/-- Materializing the label table preserves its value at every cell. -/
theorem labelTable_get {cells : ℕ} (label : Fin cells → α) (c : Fin cells) :
    (labelTable label)[c] = label c := by
  change (List.ofFn label).toArray[c.val]'(by
    simpa only [List.size_toArray, List.length_ofFn] using c.isLt) = label c
  simp only [List.getElem_toArray, List.getElem_ofFn]

/-- Cache the current cell labels while retaining the partner array unchanged. -/
def cache (n : State arity boundary) : State arity boundary :=
  let labels := labelTable n.2.1
  ⟨n.1, fun c ↦ labels[c],
    cast (congrArg (fun label ↦ ArrayNet arity label (Fin boundary))
      (funext (labelTable_get n.2.1)).symm) n.2.2⟩

/-- Caching changes the executable representation without changing the runtime state's value. -/
@[simp] theorem cache_eq (n : State arity boundary) : cache n = n := by
  rcases n with ⟨cells, label, n⟩
  apply congrArg (Sigma.mk cells)
  exact Sigma.ext (funext (labelTable_get label)) (cast_heq _ n)

/-- Store a finite graph presentation in array form. -/
def encode (n : FiniteNet arity boundary) : State arity boundary :=
  cache ⟨n.1, n.2.1, ArrayNet.encode n.net⟩

/-- Storing and reading a finite graph preserves its complete presentation. -/
@[simp] theorem read_encode (n : FiniteNet arity boundary) : read (encode n) = n := by
  rcases n with ⟨cells, label, n⟩
  unfold encode
  rw [cache_eq]
  simp only [read, ArrayNet.read_encode]

/-- The graph represented by a runtime state, independent of its particular cell allocation. -/
def graph (n : State arity boundary) : Graph arity boundary := Graph.ofNet (read n)

/-- Execute one selected active pair by allocating and rewiring its array representation. -/
def contract {s : PortSystem arity} (n : State arity boundary) (r : s.Redex (read n).net) :
    State arity boundary :=
  cache ⟨_, _, n.2.2.contract r.active (ArrayNet.encode r.rhs.2.2)⟩

/-- Executing a selected redex refines one abstract graph contraction. -/
theorem contract_step {s : PortSystem arity} (n : State arity boundary)
    (r : s.Redex (read n).net) : FiniteNet.Step s (read n) (read (contract n r)) := by
  simp only [contract, cache_eq]
  refine ⟨r, ⟨?_⟩⟩
  have hi := n.2.2.contractIso r.active (ArrayNet.encode r.rhs.2.2)
  have he := congrArg (fun body ↦ n.2.2.read.contract r.active body)
    (ArrayNet.read_encode r.rhs.2.2)
  exact cast (congrArg (fun body ↦ body.Iso
    (n.2.2.contract r.active (ArrayNet.encode r.rhs.2.2)).read) he) hi

/-- Check a candidate principal pair and retrieve its finite rule body when one is available. -/
def redexAt? (s : PortSystem arity) (n : State arity boundary) (a b : Fin n.1) :
    Option (s.Redex (read n).net) :=
  if h : n.2.2.read.wiring.partner (PortNet.principal arity n.2.1 a) =
      PortNet.principal arity n.2.1 b then
    match hr : s.rule (n.2.1 a) (n.2.1 b) with
    | none => none
    | some rhs => some ⟨a, b, h, rhs, hr⟩
  else none

/-- Checking the cells of an existing redex finds a rule application. -/
theorem redexAt?_isSome {s : PortSystem arity} {n : State arity boundary}
    (r : s.Redex (read n).net) : (redexAt? s n r.left r.right).isSome := by
  have ha : n.2.2.read.wiring.partner (PortNet.principal arity n.2.1 r.left) =
      PortNet.principal arity n.2.1 r.right := r.active
  have hr : s.rule (n.2.1 r.left) (n.2.1 r.right) = some r.rhs := r.rule_eq
  simp only [redexAt?, dif_pos ha]
  split
  · rename_i he
    cases he.symm.trans hr
  · rfl

/-- Follow a principal wire, accepting its endpoint only when it is another principal port. -/
def principalPartner? {cells : ℕ} {label : Fin cells → α}
    (n : PortNet arity label (Fin boundary)) (a : Fin cells) : Option (Fin cells) :=
  match n.wiring.partner (PortNet.principal arity label a) with
  | .inl _ => none
  | .inr ⟨b, p⟩ => if p.val = 0 then some b else none

/-- Following the wire of an active pair discovers its other cell. -/
theorem principalPartner?_of_active {cells : ℕ} {label : Fin cells → α}
    {n : PortNet arity label (Fin boundary)} {a b : Fin cells} (h : n.Active a b) :
    principalPartner? n a = some b := by
  unfold principalPartner?
  change n.wiring.partner (PortNet.principal arity label a) =
    PortNet.principal arity label b at h
  rw [h]
  rfl

/-- Enumerate actual principal neighbors in ascending order of the first cell. -/
def candidates (n : State arity boundary) : List (Fin n.1 × Fin n.1) :=
  let net := (read n).net
  (List.finRange n.1).filterMap fun a ↦ (principalPartner? net a).map (a, ·)

/-- Every active pair occurs in the principal-neighbor candidate list. -/
theorem mem_candidates {n : State arity boundary} {a b : Fin n.1}
    (h : (read n).net.Active a b) : (a, b) ∈ candidates n :=
  List.mem_filterMap.mpr ⟨a, List.mem_finRange a, by
    rw [principalPartner?_of_active h]
    rfl⟩

/-- Select the first candidate pair that has a principal wire and a permitted rule. -/
def select (s : PortSystem arity) (n : State arity boundary) : Option (s.Redex (read n).net) :=
  (candidates n).findSome? (fun p ↦ redexAt? s n p.1 p.2)

/-- An existing redex makes the complete candidate search succeed. -/
theorem select_isSome {s : PortSystem arity} {n : State arity boundary}
    (r : s.Redex (read n).net) : (select s n).isSome :=
  List.findSome?_isSome_iff.mpr ⟨(r.left, r.right), mem_candidates r.active, redexAt?_isSome r⟩

/-- Execute a caller-selected pair when it is an active pair with a permitted rule. -/
def stepAt (s : PortSystem arity) (n : State arity boundary) (a b : Fin n.1) :
    Option (State arity boundary) := (redexAt? s n a b).map (contract n)

/-- A successful caller-selected runtime step is a permitted graph contraction. -/
theorem stepAt_refines {s : PortSystem arity} {n m : State arity boundary} {a b : Fin n.1}
    (h : stepAt s n a b = some m) : Graph.Step s (graph n) (graph m) := by
  obtain ⟨r, _, hm⟩ := Option.map_eq_some_iff.mp h
  subst m
  exact Graph.step_of_net (contract_step n r)

/-- Execute the default schedule's next active pair, if one is available. -/
def step (s : PortSystem arity) (n : State arity boundary) : Option (State arity boundary) :=
  (select s n).map (contract n)

/-- A successful runtime step represents one permitted graph contraction. -/
theorem step_refines {s : PortSystem arity} {n m : State arity boundary}
    (h : step s n = some m) : Graph.Step s (graph n) (graph m) := by
  obtain ⟨r, _, hm⟩ := Option.map_eq_some_iff.mp h
  subst m
  exact Graph.step_of_net (contract_step n r)

/-- If the exhaustive runtime search finds no step, the represented graph is normal. -/
theorem normal_of_step_none {s : PortSystem arity} {n : State arity boundary}
    (h : step s n = none) : Schedule.Normal (Graph.Step s) (graph n) := by
  have hs : select s n = none := Option.map_eq_none_iff.mp h
  intro m hm
  obtain ⟨a, b, ha, _, r, hi⟩ := hm
  obtain ⟨i⟩ := Quotient.exact ha
  have hr := select_isSome (r.map i)
  rw [hs] at hr
  cases hr

/-- A represented normal graph admits no successful runtime step. -/
theorem step_none_of_normal {s : PortSystem arity} {n : State arity boundary}
    (h : Schedule.Normal (Graph.Step s) (graph n)) : step s n = none := by
  cases he : step s n with
  | none => rfl
  | some m => exact (h (graph m) (step_refines he)).elim

end Geb.InteractionNet.GraphRuntime

end
