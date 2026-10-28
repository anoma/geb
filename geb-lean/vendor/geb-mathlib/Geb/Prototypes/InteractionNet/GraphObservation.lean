/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.GraphReadback
public import Geb.Prototypes.InteractionNet.GraphRuntimeAdequacy

set_option doc.verso true in
/-!
# Schedule-independent tree observations

Tree read-back is invariant under cell renaming, so it descends to graphs modulo renaming.
The graph confluence theorem then equates the tree observations of any two normalizing
schedules. In particular, every successful array-runtime run agrees with every abstract
normal form reachable from the same input graph.

## Main definitions

* {lit}`Graph.readTree` — the tree observation of a graph modulo cell renaming.
* {lit}`GraphRuntime.readTree` — read a tree from an array-runtime state.

## Main statements

* {lit}`Graph.readTree_eq_of_normal` — normalizing schedules have the same tree observation.
* {lit}`GraphRuntime.run_readTree_eq` — successful runtime bounds agree on tree read-back.
* {lit}`GraphRuntime.run_readTree_eq_normal` — runtime read-back agrees with a reached normal form.

## Tags

interaction net, confluence, schedule, observation, tree, read-back, runtime
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

variable {α : Type} {arity : α → ℕ}

namespace Graph

/-- Read-back descends to graphs because it is invariant under cell renaming. -/
def readTree (tag : α → Option ℕ) : Graph arity 1 → Option (RoseTree ℕ) :=
  Quotient.lift (FiniteNet.readTree tag) fun _ _ ⟨e⟩ ↦ FiniteNet.readTree_iso tag e

/-- Reading a graph presentation gives its quotient graph's tree observation. -/
@[simp] theorem readTree_ofNet (tag : α → Option ℕ) (n : FiniteNet arity 1) :
    readTree tag (ofNet n) = FiniteNet.readTree tag n := rfl

/-- Any two normalizing graph schedules have the same tree observation. -/
theorem readTree_eq_of_normal (tag : α → Option ℕ) {s : PortSystem arity}
    {n m k : Graph arity 1} (hm : Relation.ReflTransGen (Step s) n m)
    (hk : Relation.ReflTransGen (Step s) n k) (nm : Schedule.Normal (Step s) m)
    (nk : Schedule.Normal (Step s) k) : readTree tag m = readTree tag k :=
  congrArg (readTree tag) (normal_unique hm hk nm nk)

end Graph

namespace GraphRuntime

/-- Traverse the runtime partner array through its verified finite graph read-back. -/
def readTree (tag : α → Option ℕ) (n : State arity 1) : Option (RoseTree ℕ) :=
  FiniteNet.readTree tag (read n)

/-- Runtime tree read-back agrees with observation of its represented abstract graph. -/
theorem readTree_graph (tag : α → Option ℕ) (n : State arity 1) :
    readTree tag n = Graph.readTree tag (graph n) := rfl

/-- Every successful run has the same tree observation as any reached abstract normal form. -/
theorem run_readTree_eq_normal (tag : α → Option ℕ) {s : PortSystem arity}
    {fuel : ℕ} {n m : State arity 1} {q : Graph arity 1}
    (h : run s fuel n = some m) (hq : Relation.ReflTransGen (Graph.Step s) (graph n) q)
    (hn : Schedule.Normal (Graph.Step s) q) : readTree tag m = Graph.readTree tag q :=
  congrArg (Graph.readTree tag) (run_eq_normal h hq hn)

/-- Successful bounds of the same graph execution return identical tree observations. -/
theorem run_readTree_eq (tag : α → Option ℕ) {s : PortSystem arity} {fuel fuel' : ℕ}
    {n m k : State arity 1} (h : run s fuel n = some m) (h' : run s fuel' n = some k) :
    readTree tag m = readTree tag k :=
  run_readTree_eq_normal tag h (run_refines h').1 (run_refines h').2

end GraphRuntime

end Geb.InteractionNet

end
