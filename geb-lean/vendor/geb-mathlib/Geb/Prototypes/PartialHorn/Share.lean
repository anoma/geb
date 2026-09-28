/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PartialHorn.Development
public import Geb.Prototypes.PartialHorn.Shared

set_option doc.verso true in
/-!
# Sharing the terms of a development

The conversion of a development's certificates into shared certificates over one store. Terms
are interned: a node is added to the store only when no node of its label and children is there
already, so that a term is stored once and two equal terms have one index. Each certificate is
converted rule by rule: its conclusion is computed as the checker computes it, the terms are
interned, and the shared certificate names the terms its rule's conclusion introduces. A
certificate may use the rules of the shared checker's oracle, a term's definedness and the
equation of two terms, which the checker of the tree certificates does not have. The
conversion is not trusted: the shared development it produces is checked by
{name}`Geb.PartialHorn.checkShared`.

## Main definitions

* {lit}`Table` — a table of values keyed by trees, by hash.
* {lit}`intern` — the index of a term, adding its nodes to the store as needed.
* {lit}`convert` — the shared certificate of a certificate, with its conclusion.
* {lit}`share` — the shared development of a development.

## Tags

partial Horn logic, proof certificate, hash consing, sharing
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PartialHorn

open scoped FinEnum

/-- A structural hash of a tree. -/
def treeHash : Tree → UInt64 := RoseTree.elim fun l hs ↦ hs.foldl mixHash (hash l)

/-- A table of values keyed by trees: buckets of pairs, indexed by the keys' hashes. -/
structure Table (β : Type) where
  /-- The buckets. -/
  buckets : Array (List (Tree × β)) := Array.replicate 4096 []

/-- The bucket of a key. -/
def Table.index {β : Type} (tb : Table β) (t : Tree) : ℕ := (treeHash t).toNat % tb.buckets.size

/-- The value of a key, if the table has one. -/
def Table.find? {β : Type} (tb : Table β) (t : Tree) : Option β :=
  (tb.buckets[tb.index t]?.bind fun l ↦ l.find? (·.1 == t)).map Prod.snd

/-- The table with a key's value added. -/
def Table.insert {β : Type} (tb : Table β) (t : Tree) (b : β) : Table β :=
  ⟨tb.buckets.modify (tb.index t) ((t, b) :: ·)⟩

/-- The state of interning: the store's nodes, and the index of each node by its label and
children. -/
structure Interner where
  /-- The nodes. -/
  nodes : Array (ℕ × List ℕ) := #[]
  /-- The index of each node, keyed by its label over leaves labelled by its children. -/
  index : Table ℕ := {}

/-- The monad of the conversion: interning, which may fail. -/
abbrev IM : Type → Type := StateT Interner Option

/-- The key of a node: its label over leaves labelled by its children's indices. -/
def nodeKey (l : ℕ) (ks : List ℕ) : Tree := RoseTree.node l (ks.map fun k ↦ RoseTree.node k [])

/-- The index of a node of a label and children, added when absent. -/
def internNode (l : ℕ) (ks : List ℕ) : IM ℕ := do
  let st ← get
  match st.index.find? (nodeKey l ks) with
  | some i => pure i
  | none =>
    let index := st.index.insert (nodeKey l ks) st.nodes.size
    set ({ nodes := st.nodes.push (l, ks), index } : Interner)
    pure st.nodes.size

/-- The index of a term, its nodes added when absent. -/
def intern (t : Tree) : IM ℕ :=
  RoseTree.para (fun l cs ↦ do internNode l (← cs.mapM Prod.snd)) t

/-- A shared certificate's reference to a term: the leaf labelled by its index. -/
def ref (i : ℕ) : Tree := RoseTree.node i []

/-- The instance of a sequent at the terms of a certificate's node, its premises converted: the
conclusion and the shared node's children after the index of the sequent. -/
def convInst (a : Seq) (cs : List (Tree × (List Eqn → IM (Eqn × Tree)))) (H : List Eqn) :
    IM (Eqn × List Tree) := do
  let n := a.ctx.length
  let ts := (cs.take n).map Prod.fst
  let ids ← ts.mapM intern
  let prems ← (cs.drop n).mapM fun c ↦ c.2 H
  let q := a.concl.subst ts
  let l ← intern q.lhs
  let r ← intern q.rhs
  pure (q, ids.map ref ++ prems.map Prod.snd ++ [ref l, ref r])

/-- One rule of the conversion, by the label of a certificate's node: the conclusion as the
checker computes it, and the shared node. -/
def convStep (T : Theory) (E : Array Seq) (l : ℕ)
    (cs : List (Tree × (List Eqn → IM (Eqn × Tree)))) (H : List Eqn) : IM (Eqn × Tree) :=
  match l, cs with
  | Rule.hyp, [(i, _)] => do
    let some q := H[i.label]? | failure
    pure (q, RoseTree.node Rule.hyp [ref i.label])
  | Rule.refl, [(i, _)] => do
    let v ← intern (var i.label)
    pure (⟨var i.label, var i.label⟩, RoseTree.node Rule.refl [ref i.label, ref v])
  | Rule.symm, [(_, p)] => do
    let (q, c) ← p H
    pure (⟨q.rhs, q.lhs⟩, RoseTree.node Rule.symm [c])
  | Rule.trans, [(_, p), (_, p')] => do
    let (q, c) ← p H
    let (q', c') ← p' H
    pure (⟨q.lhs, q'.rhs⟩, RoseTree.node Rule.trans [c, c'])
  | Rule.cong, (_, d) :: ps => do
    let (q, c) ← d H
    let rs ← ps.mapM fun p ↦ p.2 H
    let t := RoseTree.node q.lhs.label (rs.map fun r ↦ r.1.rhs)
    let r ← intern t
    pure (⟨q.lhs, t⟩, RoseTree.node Rule.cong (c :: rs.map Prod.snd ++ [ref r]))
  | Rule.strict, [(j, _), (_, p)] => do
    let (q, c) ← p H
    let some t := q.lhs.children[j.label]? | failure
    pure (⟨t, t⟩, RoseTree.node Rule.strict [ref j.label, c])
  | Rule.ax, (j, _) :: cs => do
    let some a := T.axioms[j.label]? | failure
    let (q, rest) ← convInst a cs H
    pure (q, RoseTree.node Rule.ax (ref j.label :: rest))
  | Rule.cut, [(_, p), (_, p')] => do
    let (q, c) ← p H
    let (q', c') ← p' (q :: H)
    pure (q', RoseTree.node Rule.cut [c, c'])
  | Rule.thm, (j, _) :: cs => do
    let some a := E[j.label]? | failure
    let (q, rest) ← convInst a cs H
    pure (q, RoseTree.node Rule.thm (ref j.label :: rest))
  | Rule.typed, [(t, _)] => do
    let i ← intern t
    pure (⟨t, t⟩, RoseTree.node Rule.typed [ref i])
  | Rule.objEq, [(a, _), (b, _)] => do
    let i ← intern a
    let j ← intern b
    pure (⟨a, b⟩, RoseTree.node Rule.objEq [ref i, ref j])
  | _, _ => failure

/-- The conversion of a certificate under hypotheses: its conclusion and its shared
certificate. -/
def convert (T : Theory) (E : Array Seq) (c : Tree) : List Eqn → IM (Eqn × Tree) :=
  RoseTree.para (convStep T E) c

/-- The shared entries of a development's sequents, with the sequents of an environment and
those before each as theorems. -/
def shareEntries (T : Theory) : Development → Array Seq → IM (List SEntry) :=
  List.rec (fun _ ↦ pure []) fun e _ ih E ↦ do
    let hs ← e.1.hyps.mapM fun h ↦ do pure (← intern h.lhs, ← intern h.rhs)
    let cl ← intern e.1.concl.lhs
    let cr ← intern e.1.concl.rhs
    let (_, c) ← convert T E e.2 e.1.hyps
    pure (⟨e.1, hs, (cl, cr), c⟩ :: (← ih (E.push e.1)))

/-- The shared development of a development: its terms interned in one store. -/
def share (T : Theory) (dev : Development) : Option SDevelopment :=
  ((shareEntries T dev #[]).run {}).map fun (es, st) ↦ ⟨⟨st.nodes⟩, es⟩

end Geb.PartialHorn

end
