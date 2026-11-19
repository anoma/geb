/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.FreeTopos.Internal.Prove
public import Geb.Prototypes.Kernel.Basic

set_option doc.verso true

/-!
# The internal language's data as trees of numbers

The programs of the metalogic written in Geb read the internal language's terms, constants,
theorems and rules as trees of natural numbers: a term the node of its label's position over the
node of the label's data and its children, and a structure the node of its fields. This module
states that representation, at which the agreement of those programs with their Lean
counterparts is stated, and a partial inverse of it: a reading of a tree as the datum it
represents, which has a value only at a representation, so that a function of trees that reads
its arguments by it is given representations alone. The acceleration of a program written in
Geb by its Lean counterpart ({lit}`Geb.FreeTopos.Internal.Accelerate`) reads its arguments so.

## Main definitions

* {lit}`encWith` — a rose tree of labels as a tree of numbers.
* {lit}`encOpt`, {lit}`encTerm`, {lit}`encRule`, {lit}`encGlobals`, {lit}`encThm`,
  {lit}`encEntry` — an optional tree, a term, a rule of the normalizer, the constants, a theorem
  and an entry as trees.
* {lit}`decLeaf`, {lit}`decList`, {lit}`decTerm`, {lit}`decRule`, {lit}`decGlobals`,
  {lit}`decThm`, {lit}`decEntry` — the number, the list of trees, the term, the rule, the
  constants, the theorem and the entry a tree represents, where it represents one.

## Main statements

* {lit}`encTerm_of_decTerm`, {lit}`encRule_of_decRule`, {lit}`encGlobals_of_decGlobals`,
  {lit}`encEntry_of_decEntry` — a tree read as a datum is that datum's representation.
* {lit}`decRule_unprepared` — a rule read from a tree is no prepared theorem.

## Tags

internal language, encoding, rose tree, agreement
-/

@[expose] public section

namespace Geb.FreeTopos.Internal.Encode

open Geb.PartialHorn

/-! The representation. -/

/-- A rose tree of labels as a tree of numbers: each node the node of its label's position over
the tree of the label's data and the children. -/
def encWith {L : Type} (tag : L → ℕ) (dat : L → Tree) : RoseTree L → Tree :=
  RoseTree.elim fun l cs ↦ RoseTree.node (tag l) (dat l :: cs)

/-- The encoding of a node is the node of its label's position over the label's data and the
children's encodings. -/
@[simp] theorem encWith_node {L : Type} (tag : L → ℕ) (dat : L → Tree) (l : L)
    (cs : List (RoseTree L)) :
    encWith tag dat (RoseTree.node l cs) =
      RoseTree.node (tag l) (dat l :: cs.map (encWith tag dat)) :=
  RoseTree.elim_node _ l cs

/-- An optional tree as the reader represents it. -/
def encOpt : Option Tree → Tree
  | some t => RoseTree.node 1 [t]
  | none => Kernel.leaf 0

/-- An equation as the node of its sides. -/
def encEqn (q : Eqn) : Tree := RoseTree.node 0 [q.lhs, q.rhs]

/-- A sequent as the node of its context's sorts, its hypotheses and its conclusion. -/
def encSeq (a : Seq) : Tree :=
  RoseTree.node 0 [RoseTree.node 0 (a.ctx.map Kernel.leaf), RoseTree.node 0 (a.hyps.map encEqn),
    encEqn a.concl]

/-- The position of a label's constructor, and its data. -/
def labelData : Internal.Label → ℕ × List Tree
  | .var i => (0, [Kernel.leaf i])
  | .star => (1, [])
  | .pair => (2, [])
  | .fst => (3, [])
  | .snd => (4, [])
  | .lam a => (5, [a])
  | .app => (6, [])
  | .arr k θ => (7, [Kernel.leaf k, RoseTree.node 0 θ])
  | .natRec => (8, [])
  | .listRec => (9, [])
  | .roseRec c => (10, [c])
  | .defn k θ => (11, [Kernel.leaf k, RoseTree.node 0 θ])
  | .eq => (12, [])

/-- A term as the node of its label's position over the node of the label's data and its
children. -/
def encTerm : Internal.Term → Tree :=
  encWith (fun l ↦ (labelData l).1) fun l ↦ RoseTree.node 0 (labelData l).2

/-- The position of a rule's constructor, and its data. -/
def ruleData : Internal.Rule → ℕ × List Tree
  | .refl => (0, [])
  | .trans => (1, [])
  | .cong => (2, [])
  | .beta => (3, [])
  | .fstPair => (4, [])
  | .sndPair => (5, [])
  | .pairEta => (6, [])
  | .unitEta => (7, [])
  | .delta => (8, [])
  | .natZero k => (9, [Kernel.leaf k])
  | .natSucc k => (10, [Kernel.leaf k])
  | .listNil k => (11, [Kernel.leaf k])
  | .listCons k => (12, [Kernel.leaf k])
  | .roseNode kn kl kc => (13, [Kernel.leaf kn, Kernel.leaf kl, Kernel.leaf kc])
  | .caseInl kc kl => (14, [Kernel.leaf kc, Kernel.leaf kl])
  | .caseInr kc kr => (15, [Kernel.leaf kc, Kernel.leaf kr])
  | .thm j θ σ flip =>
    (16, [Kernel.leaf j, RoseTree.node 0 θ, RoseTree.node 0 (σ.map encTerm), Kernel.ofBool flip])
  | .rwHyp i flip => (17, [Kernel.leaf i, Kernel.ofBool flip])
  | .join => (18, [])
  | .natInd kz ks s => (19, [Kernel.leaf kz, Kernel.leaf ks, encTerm s])
  | .listInd kn kc s => (20, [Kernel.leaf kn, Kernel.leaf kc, encTerm s])
  | .hyp i => (21, [Kernel.leaf i])
  | .cut φ => (22, [encTerm φ])
  | .conv => (23, [])
  | .convFrom φ => (24, [encTerm φ])
  | .propExt => (25, [])
  | .funExt => (26, [])
  | .apply j θ σ => (27, [Kernel.leaf j, RoseTree.node 0 θ, RoseTree.node 0 (σ.map encTerm)])
  | .natIndHyp kz ks => (28, [Kernel.leaf kz, Kernel.leaf ks])
  | .listIndHyp kn kc => (29, [Kernel.leaf kn, Kernel.leaf kc])
  | .cert c => (30, [c])
  | .certSeq c => (31, [c])
  | .roseInd kn kl kc s => (32, [Kernel.leaf kn, Kernel.leaf kl, Kernel.leaf kc, encTerm s])
  | .roseIndHyp kn kl kc => (33, [Kernel.leaf kn, Kernel.leaf kl, Kernel.leaf kc])
  | .coprodInd kl kr => (34, [Kernel.leaf kl, Kernel.leaf kr])
  | .zeroInd i => (35, [Kernel.leaf i])
  | .quotInd kq θ => (36, [Kernel.leaf kq, RoseTree.node 0 θ])

/-- A rule of the prover's normalizer as the node of its constructor's position over its
fields: a prepared theorem's matching, a function, is left out, the leaf of label zero standing
for its root's label. -/
def encRule : Internal.NormRule → Tree
  | .rule r => RoseTree.node 0 [Kernel.leaf (ruleData r).1, RoseTree.node 0 (ruleData r).2]
  | .delta k => RoseTree.node 1 [Kernel.leaf k]
  | .deltaBelow m ks => RoseTree.node 2 [Kernel.leaf m, RoseTree.node 0 (ks.map Kernel.leaf)]
  | .unitVar => RoseTree.node 3 []
  | .thm j θ => RoseTree.node 4 [Kernel.leaf j, RoseTree.node 0 θ]
  | .thmAt j θ _ _ k => RoseTree.node 5 [Kernel.leaf j, RoseTree.node 0 θ, Kernel.leaf 0,
      Kernel.leaf k]
  | .hyp i => RoseTree.node 6 [Kernel.leaf i]

/-- A primitive arrow as the node of its arity, arrow, domain and codomain. -/
def encPrim (p : Internal.Prim) : Tree :=
  RoseTree.node 0 [Kernel.leaf p.arity, p.arrow, p.dom, p.cod]

/-- A definition of the language as the node of its arity, its parameters' types, its type and
its body. -/
def encLDefn (d : Internal.Defn) : Tree :=
  RoseTree.node 0 [Kernel.leaf d.arity, RoseTree.node 0 d.params, d.type, encTerm d.body]

/-- A definition of either kind as the node of its kind's position over its fields. -/
def encDefinition : Internal.Definition → Tree
  | .language d => RoseTree.node 0 [encLDefn d]
  | .object m b => RoseTree.node 1 [Kernel.leaf m, b]

/-- The constants as the node of the node of the primitive arrows, the node of the definitions
and the index of the first definition's operation. -/
def encGlobals (G : Internal.Globals) : Tree :=
  RoseTree.node 0 [RoseTree.node 0 (G.prims.map encPrim),
    RoseTree.node 0 (G.defs.map encDefinition), Kernel.leaf G.base]

/-- A theorem as the node of its arity, context, hypotheses and conclusion. -/
def encThm (a : Internal.Thm) : Tree :=
  RoseTree.node 0 [Kernel.leaf a.arity, RoseTree.node 0 a.ctx,
    RoseTree.node 0 (a.hyps.map encTerm), encTerm a.concl]

/-- An entry as the node of its kind's position over its theorem or sequent. -/
def encEntry : Internal.Entry → Tree
  | .language a => RoseTree.node 0 [encThm a]
  | .combinators s => RoseTree.node 1 [encSeq s]

/-! The reading of a tree as the datum it represents. -/

/-- The number a tree is the leaf of, where it has no children. -/
def decLeaf (x : Tree) : Option ℕ := if x.children.isEmpty then some x.label else none

/-- A tree read as a number is that number's leaf. -/
theorem leaf_of_decLeaf {x : Tree} {n : ℕ} (h : decLeaf x = some n) : Kernel.leaf n = x := by
  unfold decLeaf at h
  split at h
  · next hc =>
    obtain rfl := Option.some.inj h
    exact (congrArg (RoseTree.node x.label) (List.isEmpty_iff.mp hc).symm).trans
      (RoseTree.node_label_children x)
  · cases h

/-- The trees a tree is the node of, where its label is zero. -/
def decList (x : Tree) : Option (List Tree) := if x.label = 0 then some x.children else none

/-- A tree read as a list of trees is the node of that list. -/
theorem node_of_decList {x : Tree} {ts : List Tree} (h : decList x = some ts) :
    RoseTree.node 0 ts = x := by
  unfold decList at h
  split at h
  · next hl =>
    obtain rfl := Option.some.inj h
    exact hl ▸ RoseTree.node_label_children x
  · cases h

/-- The values a reading gives at each element of a list, where it gives one at each, are mapped
back to the list by a function that maps each value back to what was read. -/
theorem map_of_mapM {α β : Type} {dec : α → Option β} {enc : β → α} :
    ∀ xs : List α, (∀ x ∈ xs, ∀ v, dec x = some v → enc v = x) →
      ∀ vs, xs.mapM dec = some vs → vs.map enc = xs :=
  List.rec (fun _ vs h ↦ by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h
      rfl)
    fun x xs ih hx vs h ↦ by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨v, hv, vs', hvs, rfl⟩ := h
      rw [List.map_cons, hx x List.mem_cons_self v hv,
        ih (fun y hy ↦ hx y (List.mem_cons_of_mem x hy)) vs' hvs]

/-- The values a list of trees represents, each read by a reading whose values represent what is
read, represent the list. -/
theorem map_of_mapM_all {β : Type} {dec : Tree → Option β} {enc : β → Tree}
    (h : ∀ x v, dec x = some v → enc v = x) {xs : List Tree} {vs : List β}
    (hx : xs.mapM dec = some vs) : vs.map enc = xs :=
  map_of_mapM xs (fun x _ ↦ h x) vs hx

/-- Each of the values a reading gives at the elements of a list is its value at some element. -/
theorem exists_of_mem_mapM {α β : Type} {dec : α → Option β} :
    ∀ (xs : List α) (vs : List β), xs.mapM dec = some vs → ∀ v ∈ vs, ∃ x, dec x = some v :=
  List.rec (fun vs h v hv ↦ by
      simp only [List.mapM_nil, Option.pure_def, Option.some.injEq] at h
      subst h
      cases hv)
    fun x xs ih vs h v hv ↦ by
      simp only [List.mapM_cons, Option.bind_eq_bind, Option.pure_def, Option.bind_eq_some_iff,
        Option.some.injEq] at h
      obtain ⟨w, hw, vs', hvs, rfl⟩ := h
      rcases List.mem_cons.mp hv with rfl | hv
      · exact ⟨x, hw⟩
      · exact ih vs' hvs v hv

/-- The readings of the second components of a list's elements paired with their readings are the
readings of the list. -/
theorem mapM_pair {α β : Type} (f : α → Option β) (xs : List α) :
    (xs.map fun x ↦ (x, f x)).mapM Prod.snd = xs.mapM f :=
  List.rec rfl (fun x xs ih ↦ by simp only [List.map_cons, List.mapM_cons, ih]) xs

/-- The label of a position and data, where they are one's. -/
def decLabel (k : ℕ) (ds : List Tree) : Option Internal.Label := match k, ds with
  | 0, [i] => (decLeaf i).map .var
  | 1, [] => some .star
  | 2, [] => some .pair
  | 3, [] => some .fst
  | 4, [] => some .snd
  | 5, [a] => some (.lam a)
  | 6, [] => some .app
  | 7, [j, θ] => (decLeaf j).bind fun j ↦ (decList θ).map (.arr j)
  | 8, [] => some .natRec
  | 9, [] => some .listRec
  | 10, [c] => some (.roseRec c)
  | 11, [j, θ] => (decLeaf j).bind fun j ↦ (decList θ).map (.defn j)
  | 12, [] => some .eq
  | _, _ => none

/-- A position and data read as a label are that label's. -/
theorem labelData_of_decLabel {k : ℕ} {ds : List Tree} {l : Internal.Label}
    (h : decLabel k ds = some l) : labelData l = (k, ds) := by
  unfold decLabel at h
  split at h
  case h_1 =>
    obtain ⟨i, hi, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [labelData, leaf_of_decLeaf hi]
  case h_8 =>
    obtain ⟨j, hj, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨θ, hθ, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [labelData, leaf_of_decLeaf hj, node_of_decList hθ]
  case h_12 =>
    obtain ⟨j, hj, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨θ, hθ, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [labelData, leaf_of_decLeaf hj, node_of_decList hθ]
  case h_14 => cases h
  all_goals
    obtain rfl := Option.some.inj h
    rfl

/-- One step of the reading of a tree as a term, at a node of a label from its children with
their readings: the first child the node of a label's data, and the others terms. -/
def decTermStep (k : ℕ) (cs : List (Tree × Option Internal.Term)) : Option Internal.Term :=
  match cs with
  | (d, _) :: rest =>
    (decList d).bind fun ds ↦ (decLabel k ds).bind fun l ↦
      (rest.mapM Prod.snd).map (RoseTree.node l)
  | [] => none

/-- The term a tree represents, where it represents one. -/
def decTerm : Tree → Option Internal.Term := RoseTree.para decTermStep

/-- A tree read as a term is that term's representation. -/
theorem encTerm_of_decTerm : ∀ (x : Tree) (t : Internal.Term), decTerm x = some t →
    encTerm t = x :=
  RoseTree.ind fun k cs ih t h ↦ by
    rw [decTerm, RoseTree.para_node] at h
    rcases cs with _ | ⟨d, rest⟩
    · cases h
    · rw [List.map_cons, decTermStep] at h
      obtain ⟨ds, hd, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨l, hl, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨ts, hts, rfl⟩ := Option.map_eq_some_iff.mp h
      rw [mapM_pair] at hts
      have hts' : ts.map encTerm = rest :=
        map_of_mapM rest (fun c hc ↦ ih c (List.mem_cons_of_mem d hc)) ts hts
      rw [encTerm, encWith_node, labelData_of_decLabel hl, node_of_decList hd]
      exact congrArg (fun cs ↦ RoseTree.node k (d :: cs)) hts'

/-- The rule of the normalizer a tree represents, where it represents one that is neither a rule
of the checker nor a prepared theorem. -/
def decRule (x : Tree) : Option Internal.NormRule := match x.label, x.children with
  | 1, [k] => (decLeaf k).map .delta
  | 2, [m, ks] => (decLeaf m).bind fun m ↦
      (decList ks).bind fun ks ↦ (ks.mapM decLeaf).map (.deltaBelow m)
  | 3, [] => some .unitVar
  | 4, [j, θ] => (decLeaf j).bind fun j ↦ (decList θ).map (.thm j)
  | 6, [i] => (decLeaf i).map .hyp
  | _, _ => none

/-- A tree read as a rule of the normalizer is that rule's representation. -/
theorem encRule_of_decRule (x : Tree) (r : Internal.NormRule) (h : decRule x = some r) :
    encRule r = x := by
  unfold decRule at h
  split at h
  · next k hl hc =>
    obtain ⟨k', hk, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [encRule, leaf_of_decLeaf hk, ← hc, ← hl, RoseTree.node_label_children]
  · next m ks hl hc =>
    obtain ⟨m', hm, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ks', hks, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ns, hns, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [encRule, leaf_of_decLeaf hm, map_of_mapM_all (fun _ _ ↦ leaf_of_decLeaf) hns,
      node_of_decList hks, ← hc, ← hl, RoseTree.node_label_children]
  · next hl hc =>
    obtain rfl := Option.some.inj h
    rw [encRule, ← hc, ← hl, RoseTree.node_label_children]
  · next j θ hl hc =>
    obtain ⟨j', hj, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨θ', hθ, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [encRule, leaf_of_decLeaf hj, node_of_decList hθ, ← hc, ← hl,
      RoseTree.node_label_children]
  · next i hl hc =>
    obtain ⟨i', hi, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [encRule, leaf_of_decLeaf hi, ← hc, ← hl, RoseTree.node_label_children]
  · cases h

/-- A rule of the normalizer read from a tree is no prepared theorem. -/
theorem decRule_unprepared {x : Tree} {r : Internal.NormRule} (h : decRule x = some r)
    (j : ℕ) (θ : List Tree) (root : Internal.Label)
    (m : ℕ → Internal.Term → List (Option Internal.Term) → Option (List (Option Internal.Term)))
    (k : ℕ) : r ≠ .thmAt j θ root m k := by
  rintro rfl
  unfold decRule at h
  split at h
  · obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.mp h
    cases h
  · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.mp h
    cases h
  · cases h
  · obtain ⟨_, _, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.mp h
    cases h
  · obtain ⟨_, _, h⟩ := Option.map_eq_some_iff.mp h
    cases h
  · cases h

/-- The primitive arrow a tree represents, where it represents one. -/
def decPrim (x : Tree) : Option Internal.Prim := match x.label, x.children with
  | 0, [a, f, d, c] => (decLeaf a).map fun n ↦ ⟨n, f, d, c⟩
  | _, _ => none

/-- A tree read as a primitive arrow is that arrow's representation. -/
theorem encPrim_of_decPrim (x : Tree) (p : Internal.Prim) (h : decPrim x = some p) :
    encPrim p = x := by
  unfold decPrim at h
  split at h
  · next a f d c hl hc =>
    obtain ⟨n, hn, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [encPrim, leaf_of_decLeaf hn, ← hc, ← hl, RoseTree.node_label_children]
  · cases h

/-- The definition of the language a tree represents, where it represents one. -/
def decLDefn (x : Tree) : Option Internal.Defn := match x.label, x.children with
  | 0, [a, ps, ty, b] => (decLeaf a).bind fun n ↦
      (decList ps).bind fun ps ↦ (decTerm b).map fun b ↦ ⟨n, ps, ty, b⟩
  | _, _ => none

/-- A tree read as a definition of the language is that definition's representation. -/
theorem encLDefn_of_decLDefn {x : Tree} {d : Internal.Defn} (h : decLDefn x = some d) :
    encLDefn d = x := by
  unfold decLDefn at h
  split at h
  · next a ps ty b hl hc =>
    obtain ⟨n, hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ps', hps, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [encLDefn, leaf_of_decLeaf hn, node_of_decList hps, encTerm_of_decTerm b b' hb, ← hc,
      ← hl, RoseTree.node_label_children]
  · cases h

/-- The definition a tree represents, where it represents one. -/
def decDefinition (x : Tree) : Option Internal.Definition := match x.label, x.children with
  | 0, [d] => (decLDefn d).map .language
  | 1, [m, b] => (decLeaf m).map fun m ↦ .object m b
  | _, _ => none

/-- A tree read as a definition is that definition's representation. -/
theorem encDefinition_of_decDefinition (x : Tree) (d : Internal.Definition)
    (h : decDefinition x = some d) : encDefinition d = x := by
  unfold decDefinition at h
  split at h
  · next d' hl hc =>
    obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [encDefinition, encLDefn_of_decLDefn he, ← hc, ← hl, RoseTree.node_label_children]
  · next m b hl hc =>
    obtain ⟨m', hm, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [encDefinition, leaf_of_decLeaf hm, ← hc, ← hl, RoseTree.node_label_children]
  · cases h

/-- The constants a tree represents, where it represents them. -/
def decGlobals (x : Tree) : Option Internal.Globals := match x.label, x.children with
  | 0, [ps, ds, b] => (decList ps).bind fun ps ↦ (ps.mapM decPrim).bind fun ps ↦
      (decList ds).bind fun ds ↦ (ds.mapM decDefinition).bind fun ds ↦
        (decLeaf b).map fun b ↦ ⟨ps, ds, b⟩
  | _, _ => none

/-- A tree read as the constants is their representation. -/
theorem encGlobals_of_decGlobals {x : Tree} {G : Internal.Globals} (h : decGlobals x = some G) :
    encGlobals G = x := by
  unfold decGlobals at h
  split at h
  · next ps ds b hl hc =>
    obtain ⟨ps', hps, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨prims, hprims, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ds', hds, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨defs, hdefs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨b', hb, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [encGlobals, map_of_mapM_all encPrim_of_decPrim hprims, node_of_decList hps,
      map_of_mapM_all encDefinition_of_decDefinition hdefs, node_of_decList hds,
      leaf_of_decLeaf hb, ← hc, ← hl, RoseTree.node_label_children]
  · cases h

/-- The theorem a tree represents, where it represents one. -/
def decThm (x : Tree) : Option Internal.Thm := match x.label, x.children with
  | 0, [n, ctx, hs, c] => (decLeaf n).bind fun n ↦ (decList ctx).bind fun ctx ↦
      (decList hs).bind fun hs ↦ (hs.mapM decTerm).bind fun hs ↦
        (decTerm c).map fun c ↦ ⟨n, ctx, hs, c⟩
  | _, _ => none

/-- A tree read as a theorem is that theorem's representation. -/
theorem encThm_of_decThm {x : Tree} {a : Internal.Thm} (h : decThm x = some a) :
    encThm a = x := by
  unfold decThm at h
  split at h
  · next n ctx hs c hl hc =>
    obtain ⟨n', hn, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨ctx', hctx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hs', hhs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hyps, hhyps, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp h
    rw [encThm, leaf_of_decLeaf hn, node_of_decList hctx,
      map_of_mapM_all encTerm_of_decTerm hhyps, node_of_decList hhs,
      encTerm_of_decTerm c c' hc', ← hc, ← hl, RoseTree.node_label_children]
  · cases h

/-- The equation a tree represents, where it represents one. -/
def decEqn (x : Tree) : Option Eqn := match x.label, x.children with
  | 0, [l, r] => some ⟨l, r⟩
  | _, _ => none

/-- A tree read as an equation is that equation's representation. -/
theorem encEqn_of_decEqn (x : Tree) (q : Eqn) (h : decEqn x = some q) : encEqn q = x := by
  unfold decEqn at h
  split at h
  · next l r hl hc =>
    obtain rfl := Option.some.inj h
    rw [encEqn, ← hc, ← hl, RoseTree.node_label_children]
  · cases h

/-- The sequent a tree represents, where it represents one. -/
def decSeq (x : Tree) : Option Seq := match x.label, x.children with
  | 0, [ctx, hs, c] => (decList ctx).bind fun ctx ↦ (ctx.mapM decLeaf).bind fun ctx ↦
      (decList hs).bind fun hs ↦ (hs.mapM decEqn).bind fun hs ↦
        (decEqn c).map fun c ↦ ⟨ctx, hs, c⟩
  | _, _ => none

/-- A tree read as a sequent is that sequent's representation. -/
theorem encSeq_of_decSeq {x : Tree} {s : Seq} (h : decSeq x = some s) : encSeq s = x := by
  unfold decSeq at h
  split at h
  · next ctx hs c hl hc =>
    obtain ⟨ctx', hctx, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨sorts, hsorts, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hs', hhs, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨hyps, hhyps, h⟩ := Option.bind_eq_some_iff.mp h
    obtain ⟨c', hc', rfl⟩ := Option.map_eq_some_iff.mp h
    rw [encSeq, map_of_mapM_all (fun _ _ ↦ leaf_of_decLeaf) hsorts, node_of_decList hctx,
      map_of_mapM_all encEqn_of_decEqn hhyps, node_of_decList hhs, encEqn_of_decEqn c c' hc',
      ← hc, ← hl, RoseTree.node_label_children]
  · cases h

/-- The entry a tree represents, where it represents one. -/
def decEntry (x : Tree) : Option Internal.Entry := match x.label, x.children with
  | 0, [a] => (decThm a).map .language
  | 1, [s] => (decSeq s).map .combinators
  | _, _ => none

/-- A tree read as an entry is that entry's representation. -/
theorem encEntry_of_decEntry (x : Tree) (e : Internal.Entry) (h : decEntry x = some e) :
    encEntry e = x := by
  unfold decEntry at h
  split at h
  · next a hl hc =>
    obtain ⟨a', ha, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [encEntry, encThm_of_decThm ha, ← hc, ← hl, RoseTree.node_label_children]
  · next s hl hc =>
    obtain ⟨s', hs, rfl⟩ := Option.map_eq_some_iff.mp h
    rw [encEntry, encSeq_of_decSeq hs, ← hc, ← hl, RoseTree.node_label_children]
  · cases h

end Geb.FreeTopos.Internal.Encode

end
