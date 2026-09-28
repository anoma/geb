/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PartialHorn.Basic

set_option doc.verso true in
/-!
# Certificates over a store of shared terms

A store holds the terms a development mentions as nodes, each a label and the indices of its
children, every child before its parent; the index of a node denotes the tree it spells
({lit}`Store.denote`). Terms shared among certificates are stored once and cited by index, so
that the certificates repeat no term. The checker of shared certificates
({lit}`scheck`) computes the conclusion of a certificate as a pair of indices: two indices are
the same term when they are equal, the instance of an axiom or theorem is verified by matching
its sides, patterns in its variables, against the store ({lit}`Store.matchPat`), and the sorts of
the store's terms in a context are computed once, in one pass over the store
({lit}`Store.sorts`). A shared certificate names the terms a rule's conclusion introduces, the
result of a congruence and the sides of an instance, and the checker verifies them.

Its rules are those of {name}`Geb.PartialHorn.check`, and every conclusion it computes is valid
in every model of the theory in which the environment's theorems are valid
({lit}`scheck_sound`). A shared development is a store with sequents, each with the indices of
its equations' sides and a shared certificate; every sequent of one that checks is valid in
every model of the theory ({lit}`checkShared_sound`).

## Main definitions

* {lit}`Store`, {lit}`Store.denote` — a store of shared terms, and the term of an index.
* {lit}`Store.matchPat`, {lit}`Store.matchTree`, {lit}`Store.sorts` — the store's matching of
  patterns and of terms, and the sorts of its terms in a context.
* {lit}`scheck` — the checker of shared certificates.
* {lit}`SDevelopment`, {lit}`checkShared` — shared developments and their check.

## Main statements

* {lit}`Store.denote_eq` — the term of a node applies its label to its children's terms.
* {lit}`scheck_sound` — every conclusion the checker computes is valid.
* {lit}`checkShared_sound` — every sequent of a shared development that checks is valid.

## Tags

partial Horn logic, proof certificate, hash consing, sharing, soundness
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PartialHorn

open scoped FinEnum

universe v

/-- A store of terms: nodes, each a label and the indices of its children. -/
structure Store where
  /-- The nodes. -/
  nodes : Array (ℕ × List ℕ)

namespace Store

variable (st : Store)

/-- Every child of a node comes before it. -/
def WF : Prop := ∀ (i : ℕ) (x : ℕ × List ℕ), st.nodes[i]? = some x → ∀ c ∈ x.2, c < i

/-- Whether every child of a node comes before it. -/
def wf : Bool :=
  (List.range st.nodes.size).all fun i ↦ match st.nodes[i]? with
    | some x => x.2.all (· < i)
    | none => true

/-- The check of well-formedness decides it. -/
theorem wf_of_wf (h : st.wf = true) : st.WF := by
  intro i x hx c hc
  have hi : i < st.nodes.size := (Array.getElem?_eq_some_iff.mp hx).1
  have := List.all_eq_true.mp h i (List.mem_range.mpr hi)
  rw [hx, List.all_eq_true] at this
  exact decide_eq_true_eq.mp (this c hc)

/-- The tree of a node, unfolded to a depth: the node's label over its children's trees. -/
def denoteN : ℕ → ℕ → Tree :=
  Nat.rec (fun _ ↦ RoseTree.node 0 []) fun _ rec i ↦
    match st.nodes[i]? with
    | some (l, cs) => RoseTree.node l (cs.map rec)
    | none => RoseTree.node 0 []

/-- The tree a node spells. -/
def denote (i : ℕ) : Tree := st.denoteN (i + 1) i

variable {st}

/-- In a well-formed store, a node's tree does not depend on a depth beyond its index. -/
theorem denoteN_stable (hst : st.WF) (n : ℕ) :
    ∀ i < n, ∀ m, i < m → st.denoteN n i = st.denoteN m i :=
  n.rec (motive := fun n ↦ ∀ i < n, ∀ m, i < m → st.denoteN n i = st.denoteN m i)
    (fun _ h ↦ absurd h (Nat.not_lt_zero _))
    (fun n ih i hi m hm ↦ by
      obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
      simp only [denoteN]
      rcases hx : st.nodes[i]? with _ | ⟨l, cs⟩
      · rfl
      · refine congrArg (RoseTree.node l) (List.map_congr_left fun c hc ↦ ?_)
        have := hst i _ hx c hc
        exact ih c (by omega) m (by omega))

/-- The tree of a node applies its label to its children's trees. -/
theorem denote_eq (hst : st.WF) {i l : ℕ} {cs : List ℕ} (hx : st.nodes[i]? = some (l, cs)) :
    st.denote i = RoseTree.node l (cs.map st.denote) := by
  simp only [denote, denoteN, hx]
  refine congrArg (RoseTree.node l) (List.map_congr_left fun c hc ↦ ?_)
  exact denoteN_stable hst i c (hst i _ hx c hc) (c + 1) (by omega)

variable (st)

/-- Whether a node has a label and children passing tests, one test for each child. -/
def matchNode (i l : ℕ) (tests : List (ℕ → Bool)) : Bool :=
  match st.nodes[i]? with
  | some (l', ks) => l == l' && ks.length == tests.length && (tests.zip ks).all fun p ↦ p.1 p.2
  | none => false

/-- One step of matching a pattern: a variable matches the node assigned to it, and an
application a node of its label whose children match its arguments. -/
def matchStep (σ : List ℕ) (l : ℕ) (cs : List (Tree × (ℕ → Bool))) (i : ℕ) : Bool :=
  match l, cs with
  | 0, [(v, _)] => v.children.isEmpty && σ[v.label]? == some i
  | l, cs => st.matchNode i l (cs.map Prod.snd)

/-- Whether a node is the instance of a pattern at an assignment of nodes to its variables. -/
def matchPat (σ : List ℕ) : Tree → ℕ → Bool := RoseTree.para (st.matchStep σ)

/-- Whether a node spells a term: a node of the term's label whose children spell its
children. -/
def matchTree : Tree → ℕ → Bool :=
  RoseTree.para fun l cs i ↦ st.matchNode i l (cs.map Prod.snd)

/-- The sort of a node in a context, from the sorts of the nodes before it: a variable's node
has the context's sort at its child's label, and an application the operation's result sort
when its children have the operation's argument sorts. -/
def sortStep (S : Sig) (Γ : List ℕ) (acc : Array (Option ℕ)) (x : ℕ × List ℕ) : Option ℕ :=
  match x with
  | (0, [c]) => (st.nodes[c]?).bind fun y ↦ if y.2.isEmpty then Γ[y.1]? else none
  | (0, _) => none
  | (k + 1, cs) => S[k]?.bind fun o ↦
    if cs.map (fun c ↦ acc[c]?.join) = o.1.map some then some o.2 else none

/-- The sorts of the store's nodes in a context, computed in one pass. -/
def sorts (S : Sig) (Γ : List ℕ) : Array (Option ℕ) :=
  st.nodes.foldl (fun acc x ↦ acc.push (st.sortStep S Γ acc x)) #[]

variable {st}

/-- Lists whose zipped elements agree under two maps have equal images. -/
theorem map_eq_map_of_zip {α β γ : Type*} {f : α → γ} {g : β → γ} :
    ∀ (as : List α) (bs : List β), as.length = bs.length →
      (∀ p ∈ as.zip bs, f p.1 = g p.2) → as.map f = bs.map g :=
  fun as ↦ as.rec (motive := fun as ↦ ∀ (bs : List β), as.length = bs.length →
      (∀ p ∈ as.zip bs, f p.1 = g p.2) → as.map f = bs.map g)
    (fun bs h _ ↦ by
      cases bs with
      | nil => rfl
      | cons b bs =>
        rw [List.length_nil, List.length_cons] at h
        exact absurd h.symm (Nat.succ_ne_zero _))
    (fun a as ih bs h hz ↦ by
      cases bs with
      | nil =>
        rw [List.length_nil, List.length_cons] at h
        exact absurd h (Nat.succ_ne_zero _)
      | cons b bs =>
        rw [List.length_cons, List.length_cons] at h
        rw [List.map_cons, List.map_cons, hz (a, b) List.mem_cons_self,
          ih bs (Nat.succ.inj h) fun p hp ↦ hz p (List.mem_cons_of_mem _ hp)])

/-- A node that passes a node test has the tested label, and its children pass the tests. -/
theorem of_matchNode {i l : ℕ} {tests : List (ℕ → Bool)} (h : st.matchNode i l tests = true) :
    ∃ ks, st.nodes[i]? = some (l, ks) ∧ ks.length = tests.length ∧
      ∀ p ∈ tests.zip ks, p.1 p.2 = true := by
  unfold matchNode at h
  split at h
  · rename_i l' ks hx
    simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
    obtain ⟨⟨rfl, hlen⟩, hz⟩ := h
    exact ⟨ks, hx, hlen, hz⟩
  · exact absurd h (by simp)

/-- A pattern's variable matches the node assigned to it. -/
theorem matchPat_var (σ : List ℕ) (v : Tree) (i : ℕ) :
    st.matchPat σ (RoseTree.node 0 [v]) i = (v.children.isEmpty && σ[v.label]? == some i) := by
  simp [matchPat, matchStep]

/-- A pattern's application matches a node of its label whose children match its arguments. -/
theorem matchPat_app (σ : List ℕ) {l : ℕ} {cs : List Tree} (hv : ¬(l = 0 ∧ cs.length = 1))
    (i : ℕ) : st.matchPat σ (RoseTree.node l cs) i = st.matchNode i l (cs.map (st.matchPat σ)) := by
  simp only [matchPat, RoseTree.para_node]
  rcases l with _ | k
  · rcases cs with _ | ⟨c, _ | ⟨c', cs⟩⟩
    · rfl
    · simp at hv
    · simp [matchStep, Function.comp_def]
  · simp only [matchStep, List.map_map]
    rfl

/-- A term spells a node of its label whose children spell its children. -/
theorem matchTree_node (l : ℕ) (cs : List Tree) (i : ℕ) :
    st.matchTree (RoseTree.node l cs) i = st.matchNode i l (cs.map st.matchTree) := by
  simp only [matchTree, RoseTree.para_node, List.map_map]
  rfl

/-- Substitution at an application rebuilds it with its arguments substituted. -/
theorem subst_app (ts : List Tree) {l : ℕ} {cs : List Tree} (hv : ¬(l = 0 ∧ cs.length = 1)) :
    subst ts (RoseTree.node l cs) = RoseTree.node l (cs.map (subst ts)) := by
  rcases l with _ | k
  · rcases cs with _ | ⟨c, _ | ⟨c', cs⟩⟩
    · simp [subst]
    · simp at hv
    · simp [subst, Function.comp_def]
  · exact subst_node_succ ts k cs

/-- The children of a node that passes tests built from its argument trees, one for each. -/
theorem denote_of_matchNode (hst : st.WF) {i l : ℕ} {cs : List Tree} {f : Tree → ℕ → Bool}
    {g : Tree → Tree} (h : st.matchNode i l (cs.map f) = true)
    (hc : ∀ c ∈ cs, ∀ k, f c k = true → st.denote k = g c) :
    st.denote i = RoseTree.node l (cs.map g) := by
  obtain ⟨ks, hx, hlen, hz⟩ := of_matchNode h
  rw [denote_eq hst hx]
  refine congrArg (RoseTree.node l) (map_eq_map_of_zip ks cs (by simpa using hlen) ?_).symm.symm
  intro p hp
  have hp' : (p.2, p.1) ∈ cs.zip ks := by
    rw [List.mem_iff_getElem?] at hp ⊢
    obtain ⟨n, hn⟩ := hp
    exact ⟨n, by rw [List.getElem?_zip_eq_some] at hn ⊢; exact ⟨hn.2, hn.1⟩⟩
  have hm : (f p.2, p.1) ∈ (cs.map f).zip ks := by
    rw [List.zip_map_left]
    exact List.mem_map.mpr ⟨(p.2, p.1), hp', rfl⟩
  exact hc p.2 (List.of_mem_zip hp').1 p.1 (hz _ hm)

/-- A node that matches a pattern at an assignment spells the pattern's instance at the
assigned nodes' terms. -/
theorem denote_of_matchPat (hst : st.WF) (σ : List ℕ) :
    ∀ p : Tree, ∀ {i : ℕ}, st.matchPat σ p i = true →
      st.denote i = subst (σ.map st.denote) p :=
  RoseTree.ind fun l cs ih i h ↦ by
    by_cases hv : l = 0 ∧ cs.length = 1
    · obtain ⟨rfl, hl⟩ := hv
      obtain ⟨v, rfl⟩ := List.length_eq_one_iff.mp hl
      rw [matchPat_var, Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
      rw [subst_node_zero _ h.1, List.getElem?_map, h.2, Option.map_some, Option.getD_some]
    · rw [matchPat_app σ hv] at h
      rw [subst_app _ hv]
      exact denote_of_matchNode hst h fun c hc k hk ↦ ih c hc hk

/-- A node that spells a term denotes it. -/
theorem denote_of_matchTree (hst : st.WF) :
    ∀ t : Tree, ∀ {i : ℕ}, st.matchTree t i = true → st.denote i = t :=
  RoseTree.ind fun l cs ih i h ↦ by
    rw [matchTree_node] at h
    refine (denote_of_matchNode (g := id) hst h fun c hc k hk ↦ ih c hc hk).trans ?_
    rw [List.map_id]

/-- The sort the pass computes for a node, from the sorts of the nodes before it, is the sort
of its term. -/
theorem sortStep_eq (hst : st.WF) (S : Sig) (Γ : List ℕ) {acc : Array (Option ℕ)} {k l : ℕ}
    {cs : List ℕ} (hx : st.nodes[k]? = some (l, cs))
    (hacc : ∀ j < k, acc[j]? = some (sortOf S Γ (st.denote j))) :
    st.sortStep S Γ acc (l, cs) = sortOf S Γ (st.denote k) := by
  rw [denote_eq hst hx]
  have hc : ∀ c ∈ cs, c < k := hst k _ hx
  rcases l with _ | l
  · rcases cs with _ | ⟨c, _ | ⟨c', cs⟩⟩
    · simp [sortStep, sortOf]
    · have hck : c < k := hc c List.mem_cons_self
      have hcs : c < st.nodes.size :=
        hck.trans (Array.getElem?_eq_some_iff.mp hx).1
      obtain ⟨l', cs', hc'⟩ : ∃ l' cs', st.nodes[c]? = some (l', cs') :=
        ⟨_, _, Array.getElem?_eq_getElem hcs⟩
      simp only [sortStep, hc', Option.bind_some, List.map_cons, List.map_nil]
      rw [denote_eq hst hc']
      rcases cs' with _ | ⟨e, es⟩
      · rw [sortOf_node_zero _ rfl]
        rfl
      · rw [sortOf_node_zero_of_not _ (by simp)]
        rfl
    · simp [sortStep, sortOf]
  · simp only [sortStep]
    rw [sortOf_node_succ, List.map_map]
    have he : cs.map (fun c ↦ acc[c]?.join) = cs.map (sortOf S Γ ∘ st.denote) :=
      List.map_congr_left fun c h ↦ by simp [hacc c (hc c h)]
    rw [he]

/-- The one pass computes the sorts of the nodes' terms, one for each node. -/
theorem sorts_spec (hst : st.WF) (S : Sig) (Γ : List ℕ) :
    (st.sorts S Γ).size = st.nodes.size ∧
      ∀ i < st.nodes.size, (st.sorts S Γ)[i]? = some (sortOf S Γ (st.denote i)) :=
  Array.foldl_induction (as := st.nodes)
    (motive := fun k (acc : Array (Option ℕ)) ↦
      acc.size = k ∧ ∀ j < k, acc[j]? = some (sortOf S Γ (st.denote j)))
    (init := #[]) ⟨rfl, fun j hj ↦ absurd hj (Nat.not_lt_zero _)⟩
    (f := fun acc x ↦ acc.push (st.sortStep S Γ acc x))
    (fun k b hb ↦ ⟨by rw [Array.size_push, hb.1], fun j hj ↦ by
      rcases Nat.lt_or_ge j k with hjk | hjk
      · have hjb : j < b.size := hb.1 ▸ hjk
        rw [Array.getElem?_push_lt hjb, ← Array.getElem?_eq_getElem hjb]
        exact hb.2 j hjk
      · have hjk : j = k := Nat.le_antisymm (Nat.le_of_lt_succ hj) hjk
        subst hjk
        rcases hn : st.nodes[k] with ⟨l, cs⟩
        have hx : st.nodes[(k : ℕ)]? = some (l, cs) := by
          rw [Array.getElem?_eq_getElem k.2]
          exact congrArg some hn
        have hs : (k : ℕ) = b.size := hb.1.symm
        rw [hs, Array.getElem?_push_size, ← hs, sortStep_eq hst S Γ hx hb.2]⟩)

/-- A node the one pass gives a sort has that sort in the context. -/
theorem sortOf_of_sorts (hst : st.WF) {S : Sig} {Γ : List ℕ} {i s : ℕ}
    (h : (st.sorts S Γ)[i]?.join = some s) : sortOf S Γ (st.denote i) = some s := by
  obtain ⟨hsz, hsp⟩ := sorts_spec hst S Γ
  by_cases hi : i < st.nodes.size
  · rw [hsp i hi] at h
    exact h
  · rw [Array.getElem?_eq_none (by omega)] at h
    exact absurd h (by simp)

variable (st)

/-- The equation between the terms of two nodes. -/
def eqn (q : ℕ × ℕ) : Eqn := ⟨st.denote q.1, st.denote q.2⟩

end Store

/-- The shared checker's result at a certificate: the conclusion, a pair of nodes, as a function
of the hypotheses, pairs of nodes, or nothing when the certificate does not check. -/
abbrev SChk : Type := List (ℕ × ℕ) → Option (ℕ × ℕ)

namespace Rule

/-- The definedness of a node, by the checker's oracle. -/
@[match_pattern] abbrev typed : ℕ := 9

/-- The equation of two nodes, by the checker's oracle. -/
@[match_pattern] abbrev objEq : ℕ := 10

end Rule

/-- An oracle for a store: the nodes it holds defined, and the pairs of nodes it holds
equal. -/
structure Oracle where
  /-- Whether a node is defined. -/
  typed : ℕ → Bool
  /-- Whether two nodes are equal. -/
  equal : ℕ → ℕ → Bool

/-- The oracle that holds nothing. -/
def Oracle.none : Oracle := ⟨fun _ ↦ false, fun _ _ ↦ false⟩

/-- The instance of a sequent at the nodes of a shared certificate's node: the nodes for the
context's variables, a premise for each whose conclusion's left side is that node, a premise
for each hypothesis whose conclusion's sides match the hypothesis's sides, and the nodes of the
conclusion's sides, which match the sequent's. The nodes must have the context's sorts, by the
store's sorts {lit}`srt`, and the sequent's variables must lie in its context. -/
def sinst (st : Store) (srt : Array (Option ℕ)) (a : Seq) (cs : List (Tree × SChk)) : SChk :=
  fun H ↦
  let n := a.ctx.length
  let ds := ((cs.drop n).take n).map fun c ↦ (c.2 H).map Prod.fst
  let hs := (cs.drop (n + n)).take a.hyps.length
  match (cs.take n).mapM (fun c ↦ leafIndex c.1), cs.drop (n + n + a.hyps.length) with
  | some ts, [(l, _), (r, _)] => match leafIndex l, leafIndex r with
    | some l, some r =>
      if a.Scoped && ts.map (fun t ↦ srt[t]?.join) == a.ctx.map some && ds == ts.map some &&
          hs.length == a.hyps.length &&
          (hs.zip a.hyps).all (fun p ↦ match p.1.2 H with
            | some (x, y) => st.matchPat ts p.2.lhs x && st.matchPat ts p.2.rhs y
            | none => false) &&
          st.matchPat ts a.concl.lhs l && st.matchPat ts a.concl.rhs r then
        some (l, r)
      else none
    | _, _ => none
  | _, _ => none

/-- One rule of the shared checker, by the label of a certificate's node, in a context of
{lit}`m` variables whose sorts give the store's sorts {lit}`srt`, with an oracle. -/
def scheckStep (T : Theory) (E : Array Seq) (st : Store) (m : ℕ) (srt : Array (Option ℕ))
    (orc : Oracle) (l : ℕ) (cs : List (Tree × SChk)) : SChk := fun H ↦
  match l, cs with
  | Rule.hyp, [(i, _)] => (leafIndex i).bind fun i ↦ H[i]?
  | Rule.refl, [(i, _), (v, _)] => (leafIndex i).bind fun i ↦ (leafIndex v).bind fun v ↦
    if i < m && st.matchTree (var i) v then some (v, v) else none
  | Rule.symm, [(_, p)] => (p H).map fun q ↦ (q.2, q.1)
  | Rule.trans, [(_, p), (_, p')] => (p H).bind fun q ↦ (p' H).bind fun q' ↦
    if q.2 == q'.1 then some (q.1, q'.2) else none
  | Rule.cong, (_, d) :: ps => (d H).bind fun q ↦
    match ps.getLast?, st.nodes[q.1]? with
    | some (r, _), some (lx, ks) => (leafIndex r).bind fun r ↦
      match st.nodes[r]? with
      | some (lr, rs) =>
        if lx != 0 && lr == lx && ks.length == rs.length &&
            (ps.dropLast.map fun p ↦ p.2 H) == (ks.zip rs).map some then
          some (q.1, r)
        else none
      | none => none
    | _, _ => none
  | Rule.strict, [(j, _), (_, p)] => (leafIndex j).bind fun j ↦ (p H).bind fun q ↦
    match st.nodes[q.1]? with
    | some (lx, ks) => if lx != 0 then ks[j]?.map fun c ↦ (c, c) else none
    | none => none
  | Rule.ax, (j, _) :: cs => (leafIndex j).bind fun j ↦
    T.axioms[j]?.bind fun a ↦ sinst st srt a cs H
  | Rule.cut, [(_, p), (_, p')] => (p H).bind fun h ↦ p' (h :: H)
  | Rule.thm, (j, _) :: cs => (leafIndex j).bind fun j ↦
    E[j]?.bind fun a ↦ sinst st srt a cs H
  | Rule.typed, [(i, _)] => (leafIndex i).bind fun i ↦
    if orc.typed i then some (i, i) else none
  | Rule.objEq, [(a, _), (b, _)] => (leafIndex a).bind fun a ↦ (leafIndex b).bind fun b ↦
    if orc.equal a b then some (a, b) else none
  | _, _ => none

/-- The shared checker: the conclusion of a shared certificate in a theory, an environment of
theorems and a store, in a context of {lit}`m` variables whose sorts give the store's sorts
{lit}`srt`, with an oracle, as a function of the hypotheses. -/
def scheck (T : Theory) (E : Array Seq) (st : Store) (m : ℕ) (srt : Array (Option ℕ))
    (orc : Oracle) (c : Tree) : SChk :=
  RoseTree.para (scheckStep T E st m srt orc) c

section Soundness

variable {T : Theory} {M : Model.{v} T.sig} {st : Store}

/-- An element of a list at a position is a member of any list the first is a prefix of a
suffix of. -/
theorem mem_of_mem_take_drop {α : Type*} {l : List α} {a : α} {i n : ℕ}
    (h : a ∈ (l.drop i).take n) : a ∈ l :=
  List.mem_of_mem_drop (List.mem_of_mem_take h)

/-- Monadic maps with one list of results are equal. -/
theorem mapM_congr_map {m : Type _ → Type _} [Monad m] [LawfulMonad m] {α β : Type _}
    {f : α → m β} {l₁ l₂ : List α} (h : l₁.map f = l₂.map f) : l₁.mapM f = l₂.mapM f := by
  rw [← Function.id_comp f, ← List.mapM_map, ← List.mapM_map, h]

/-- An instance of a valid sequent is valid, when the shared checker's premises are. -/
theorem sinst_sound (hst : st.WF) {Γ : List ℕ} {a : Seq} {cs : List (Tree × SChk)}
    {H : List (ℕ × ℕ)} {q : ℕ × ℕ} (ha : a.Valid M)
    (hcs : ∀ c ∈ cs, ∀ q', c.2 H = some q' → Valid M Γ (H.map st.eqn) (st.eqn q'))
    (h : sinst st (st.sorts T.sig Γ) a cs H = some q) : Valid M Γ (H.map st.eqn) (st.eqn q) := by
  simp only [sinst] at h
  split at h
  · rename_i ts _ _ _ _ _ _
    split at h
    rotate_left
    · exact absurd h (by simp)
    rename_i l r _ _
    split at h
    · rename_i hc
      cases h
      simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hc
      obtain ⟨⟨⟨⟨⟨⟨hsc, hsort⟩, hds⟩, hlen⟩, hhs⟩, hl⟩, hr⟩ := hc
      intro ρ hρ hH
      have htl : ts.length = a.ctx.length := by simpa using congrArg List.length hsort
      -- each instance term is defined, by its premise
      have hdef : ∀ t ∈ ts.map st.denote, ∃ w, eval M ρ t = Part.some w := by
        intro t ht
        obtain ⟨t', ht', rfl⟩ := List.mem_map.mp ht
        have hm : some t' ∈ ts.map some := List.mem_map_of_mem ht'
        rw [← hds] at hm
        obtain ⟨c, hc, hct⟩ := List.mem_map.mp hm
        obtain ⟨e, he, rfl⟩ := Option.map_eq_some_iff.mp hct
        obtain ⟨w, hw, -⟩ := hcs c (mem_of_mem_take_drop hc) e he ρ hρ hH
        exact ⟨w, hw⟩
      obtain ⟨ws, hws⟩ := exists_map_eq_map_some _ hdef
      have hwl : ws.length = a.ctx.length := by
        simpa [htl] using (congrArg List.length hws).symm
      -- the values have the context's sorts
      have hwsort : ws.map Sigma.fst = a.ctx := by
        refine List.ext_getElem (by simpa using hwl) fun i h₁ h₂ ↦ ?_
        have hi : i < ts.length := htl ▸ h₂
        have e₁ := congrArg (fun l ↦ l[i]?) hws
        have e₂ := congrArg (fun l ↦ l[i]?) hsort
        simp only [List.getElem?_map, List.getElem?_eq_getElem hi,
          List.getElem?_eq_getElem (hwl ▸ h₂), List.getElem?_eq_getElem h₂, Option.map_some,
          Option.some.injEq] at e₁ e₂
        simpa using sort_eval hρ _ (Store.sortOf_of_sorts hst e₂) e₁
      have hsc' := hsc
      simp only [Seq.Scoped, Bool.and_eq_true, List.all_eq_true, Eqn.Scoped] at hsc'
      obtain ⟨hsh, hscl, hscr⟩ := hsc'
      have hσl : (ts.map st.denote).length = a.ctx.length := by simpa using htl
      rw [← hσl] at hsh hscl hscr
      -- the hypotheses hold at the values
      have hhyp : ∀ h ∈ a.hyps, h.Holds M ws := by
        intro h hh
        obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hh
        set hs := (cs.drop (a.ctx.length + a.ctx.length)).take a.hyps.length
        have hk' : k < hs.length := hlen ▸ hk
        have hz : (hs[k], a.hyps[k]) ∈ hs.zip a.hyps := by
          rw [List.mem_iff_getElem?]
          exact ⟨k, by rw [List.getElem?_zip_eq_some]; simp [hk, hk']⟩
        have hm := hhs _ hz
        simp only at hm
        split at hm
        · rename_i x y hxy
          simp only [Bool.and_eq_true] at hm
          obtain ⟨w, h₁, h₂⟩ := hcs hs[k] (mem_of_mem_take_drop (List.getElem_mem hk'))
            _ hxy ρ hρ hH
          obtain ⟨hl', hr'⟩ := hsh _ hh
          refine ⟨w, ?_, ?_⟩
          · rw [← eval_subst hws _ hl', ← Store.denote_of_matchPat hst ts _ hm.1]
            exact h₁
          · rw [← eval_subst hws _ hr', ← Store.denote_of_matchPat hst ts _ hm.2]
            exact h₂
        · exact absurd hm (by simp)
      obtain ⟨w, h₁, h₂⟩ := ha ws hwsort hhyp
      refine ⟨w, ?_, ?_⟩
      · change eval M ρ (st.denote l) = _
        rw [Store.denote_of_matchPat hst ts _ hl, eval_subst hws _ hscl]
        exact h₁
      · change eval M ρ (st.denote r) = _
        rw [Store.denote_of_matchPat hst ts _ hr, eval_subst hws _ hscr]
        exact h₂
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- An oracle is sound for a store in a context under hypotheses, in a model: at every
assignment of the context at which the hypotheses hold, every node it holds defined is defined,
and every pair of nodes it holds equal have one value. -/
def Oracle.Sound (orc : Oracle) (st : Store) (M : Model.{v} T.sig) (Γ : List ℕ)
    (H₀ : List Eqn) : Prop :=
  ∀ ρ : List M.Val, ρ.map Sigma.fst = Γ → (∀ h ∈ H₀, h.Holds M ρ) →
    (∀ i, orc.typed i = true → ∃ w, eval M ρ (st.denote i) = Part.some w) ∧
      ∀ a b, orc.equal a b = true → (st.eqn (a, b)).Holds M ρ

/-- The oracle that holds nothing is sound. -/
theorem Oracle.none_sound (st : Store) (M : Model.{v} T.sig) (Γ : List ℕ) (H₀ : List Eqn) :
    Oracle.none.Sound st M Γ H₀ :=
  fun _ _ _ ↦ ⟨fun _ h ↦ absurd h (by simp [Oracle.none]),
    fun _ _ h ↦ absurd h (by simp [Oracle.none])⟩

/-- Every conclusion the shared checker computes is valid in every model of the theory in which
the environment's theorems are valid, in the context whose sorts give the store's sorts. -/
theorem scheck_sound (hM : IsModel T M) {E : Array Seq} (hE : ∀ a ∈ E, a.Valid M)
    (hst : st.WF) (Γ : List ℕ) (orc : Oracle) {H₀ : List Eqn} (horc : orc.Sound st M Γ H₀) :
    ∀ c : Tree, ∀ H q, (∀ h ∈ H₀, h ∈ H.map st.eqn) →
      scheck T E st Γ.length (st.sorts T.sig Γ) orc c H = some q →
      Valid M Γ (H.map st.eqn) (st.eqn q) :=
  RoseTree.ind fun l cs ih H q hsub h ↦ by
    have hcs : ∀ c ∈ cs.map (fun c ↦ (c, scheck T E st Γ.length (st.sorts T.sig Γ) orc c)),
        ∀ H' q', (∀ h ∈ H₀, h ∈ H'.map st.eqn) → c.2 H' = some q' →
          Valid M Γ (H'.map st.eqn) (st.eqn q') := by
      intro c hc
      obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
      exact ih c' hc'
    rw [scheck, RoseTree.para_node] at h
    change scheckStep T E st Γ.length (st.sorts T.sig Γ) orc l
      (cs.map fun c ↦ (c, scheck T E st Γ.length (st.sorts T.sig Γ) orc c)) H = some q at h
    generalize cs.map (fun c ↦ (c, scheck T E st Γ.length (st.sorts T.sig Γ) orc c)) = rs
      at h hcs
    unfold scheckStep at h
    split at h
    · -- a hypothesis
      obtain ⟨i, -, hi⟩ := Option.bind_eq_some_iff.mp h
      exact fun ρ _ hH ↦ hH _ (List.mem_map_of_mem (List.mem_of_getElem? hi))
    · -- the reflexivity of a variable
      obtain ⟨i, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨v, -, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i hc
        cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
        obtain ⟨hi, hv⟩ := hc
        intro ρ hρ _
        have hi' : i < ρ.length := by simpa [← hρ] using hi
        have hd : st.eqn (v, v) = ⟨var i, var i⟩ := by
          simp [Store.eqn, Store.denote_of_matchTree hst _ hv]
        rw [hd]
        exact ⟨ρ[i], by simp [hi', Part.coe_some], by simp [hi', Part.coe_some]⟩
      · exact absurd h (by simp)
    · -- symmetry
      obtain ⟨q', hq', rfl⟩ := Option.map_eq_some_iff.mp h
      intro ρ hρ hH
      obtain ⟨w, h₁, h₂⟩ := hcs _ List.mem_cons_self H q' hsub hq' ρ hρ hH
      exact ⟨w, h₂, h₁⟩
    · -- transitivity
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨q₁, hq₁, q₂, hq₂, h⟩ := h
      split at h
      · rename_i hmid
        cases h
        rw [beq_iff_eq] at hmid
        intro ρ hρ hH
        obtain ⟨w, h₁, h₂⟩ := hcs _ List.mem_cons_self H q₁ hsub hq₁ ρ hρ hH
        obtain ⟨w', h₁', h₂'⟩ :=
          hcs _ (List.mem_cons_of_mem _ List.mem_cons_self) H q₂ hsub hq₂ ρ hρ hH
        change eval M ρ (st.denote q₂.1) = _ at h₁'
        change eval M ρ (st.denote q₁.2) = _ at h₂
        rw [← hmid, h₂, Part.some_inj] at h₁'
        exact ⟨w, h₁, h₁' ▸ h₂'⟩
      · exact absurd h (by simp)
    · -- congruence of an operation at a defined application
      rename_i _ d ps
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨q₀, hq₀, h⟩ := h
      split at h
      · rename_i r' _ lx ks hr hx
        obtain ⟨r, -, h⟩ := Option.bind_eq_some_iff.mp h
        split at h
        · rename_i lr rs hrs
          split at h
          · rename_i hc
            cases h
            simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at hc
            obtain ⟨⟨⟨hlx, rfl⟩, hlen⟩, hps⟩ := hc
            obtain ⟨k, rfl⟩ : ∃ k, lr = k + 1 := ⟨lr - 1, by omega⟩
            intro ρ hρ hH
            obtain ⟨w, h₁, -⟩ := hcs _ List.mem_cons_self H q₀ hsub hq₀ ρ hρ hH
            change eval M ρ (st.denote q₀.1) = _ at h₁
            have hpl : ps.dropLast.length = ks.length := by
              have := congrArg List.length hps
              rw [List.length_map, List.length_map, List.length_zip, hlen, Nat.min_self] at this
              rw [this, hlen]
            have hmap : (ks.map st.denote).map (eval M ρ) = (rs.map st.denote).map (eval M ρ) := by
              refine List.ext_getElem (by simp [hlen]) fun n h₁ h₂ ↦ ?_
              have hn : n < ks.length := by simpa using h₁
              have hn' : n < ps.dropLast.length := hpl ▸ hn
              have e := List.getElem_of_eq hps (by simpa using hn')
              simp only [List.getElem_map, List.getElem_zip] at e
              obtain ⟨v, hv₁, hv₂⟩ := hcs ps.dropLast[n]
                (List.mem_cons_of_mem _ (List.dropLast_subset _ (List.getElem_mem hn'))) H _ hsub
                e
                ρ hρ hH
              simp only [List.getElem_map]
              exact (show eval M ρ (st.denote ks[n]) = _ from hv₁).trans hv₂.symm
            refine ⟨w, h₁, ?_⟩
            change eval M ρ (st.denote r) = _
            rw [← h₁, Store.denote_eq hst hrs, Store.denote_eq hst hx, eval_node_succ,
              eval_node_succ, mapM_congr_map hmap.symm]
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- strictness: an argument of a defined application is defined
      rename_i _ _ _ p
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨j, -, q₀, hq₀, h⟩ := h
      split at h
      · rename_i lx ks hx
        split at h
        · rename_i hlx
          obtain ⟨c, hc, rfl⟩ := Option.map_eq_some_iff.mp h
          rw [bne_iff_ne, ne_eq] at hlx
          obtain ⟨k, rfl⟩ : ∃ k, lx = k + 1 := ⟨lx - 1, by omega⟩
          intro ρ hρ hH
          obtain ⟨w, h₁, -⟩ :=
            hcs _ (List.mem_cons_of_mem _ List.mem_cons_self) H q₀ hsub hq₀ ρ hρ hH
          change eval M ρ (st.denote q₀.1) = _ at h₁
          rw [Store.denote_eq hst hx, eval_node_succ, part_bind_eq_some_iff] at h₁
          obtain ⟨args, hargs, -⟩ := h₁
          rw [mapM_part_eq_some_iff] at hargs
          have e := congrArg (fun l ↦ l[j]?) hargs
          simp only [List.getElem?_map, hc, Option.map_some] at e
          obtain ⟨u, -, hu⟩ := Option.map_eq_some_iff.mp e.symm
          exact ⟨u, hu.symm, hu.symm⟩
        · exact absurd h (by simp)
      · exact absurd h (by simp)
    · -- an instance of an axiom
      rename_i _ _ cs'
      obtain ⟨j, -, hj⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp hj
      exact sinst_sound hst (hM a (List.mem_of_getElem? ha))
        (fun c hc q' h' ↦ hcs c (List.mem_cons_of_mem _ hc) H q' hsub h') h
    · -- cut
      simp only [Option.bind_eq_some_iff] at h
      obtain ⟨q₁, hq₁, hq⟩ := h
      intro ρ hρ hH
      have h₁ := hcs _ List.mem_cons_self H q₁ hsub hq₁ ρ hρ hH
      exact hcs _ (List.mem_cons_of_mem _ List.mem_cons_self) (q₁ :: H) q
        (fun h hh ↦ List.mem_cons_of_mem _ (hsub h hh)) hq ρ hρ
        (List.forall_mem_cons.mpr ⟨h₁, hH⟩)
    · -- an instance of a theorem
      rename_i _ _ cs'
      obtain ⟨j, -, hj⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨a, ha, h⟩ := Option.bind_eq_some_iff.mp hj
      exact sinst_sound hst (hE a (Array.mem_of_getElem? ha))
        (fun c hc q' h' ↦ hcs c (List.mem_cons_of_mem _ hc) H q' hsub h') h
    · -- the definedness of a node, by the oracle
      obtain ⟨i, -, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i ht
        cases h
        intro ρ hρ hH
        obtain ⟨w, hw⟩ := (horc ρ hρ fun h hh ↦ hH h (hsub h hh)).1 _ ht
        exact ⟨w, hw, hw⟩
      · exact absurd h (by simp)
    · -- the equation of two nodes, by the oracle
      obtain ⟨a, -, h⟩ := Option.bind_eq_some_iff.mp h
      obtain ⟨b, -, h⟩ := Option.bind_eq_some_iff.mp h
      split at h
      · rename_i he
        cases h
        intro ρ hρ hH
        exact (horc ρ hρ fun h hh ↦ hH h (hsub h hh)).2 _ _ he
      · exact absurd h (by simp)
    · exact absurd h (by simp)

end Soundness

/-- A sequent of a shared development: the sequent, the nodes of its hypotheses' and
conclusion's sides, and its shared certificate. -/
structure SEntry where
  /-- The sequent. -/
  seq : Seq
  /-- The nodes of the hypotheses' sides. -/
  hyps : List (ℕ × ℕ)
  /-- The nodes of the conclusion's sides. -/
  concl : ℕ × ℕ
  /-- The shared certificate. -/
  cert : Tree

/-- A shared development: a store, and sequents with their shared certificates, in order. -/
structure SDevelopment where
  /-- The store of the terms. -/
  store : Store
  /-- The sequents. -/
  entries : List SEntry

/-- Whether an entry's nodes spell its sequent's equations. -/
def SEntry.spells (st : Store) (e : SEntry) : Bool :=
  e.hyps.length == e.seq.hyps.length &&
    (e.hyps.zip e.seq.hyps).all
      (fun p ↦ st.matchTree p.2.lhs p.1.1 && st.matchTree p.2.rhs p.1.2) &&
    st.matchTree e.seq.concl.lhs e.concl.1 && st.matchTree e.seq.concl.rhs e.concl.2

/-- Whether each shared certificate of a list of entries proves its sequent, with the sequents
of an environment and those before it as theorems, the sorts of the store in each context given
by {lit}`sortsOf` and the oracle for each sequent by {lit}`oracleOf`. -/
def checkSharedFrom (T : Theory) (st : Store) (sortsOf : List ℕ → Array (Option ℕ))
    (oracleOf : Seq → Oracle) : List SEntry → Array Seq → Bool :=
  List.rec (fun _ ↦ true) fun e _ ih E ↦
    e.spells st &&
      scheck T E st e.seq.ctx.length (sortsOf e.seq.ctx) (oracleOf e.seq) e.cert e.hyps ==
        some e.concl &&
      ih (E.push e.seq)

/-- The sorts of a store in a context, from a table of the sorts in contexts, computing them
where the table has none. -/
def sortsFrom (T : Theory) (st : Store) (table : List (List ℕ × Array (Option ℕ)))
    (Γ : List ℕ) : Array (Option ℕ) :=
  ((table.find? (·.1 == Γ)).map Prod.snd).getD (st.sorts T.sig Γ)

/-- Whether a shared development checks with an oracle for each sequent: its store is well
formed, and each certificate proves its sequent with those before it as theorems. The store's
sorts are computed once for each context of its sequents. -/
def checkSharedWith (T : Theory) (d : SDevelopment) (oracleOf : Seq → Oracle) : Bool :=
  let table := (d.entries.map (·.seq.ctx)).eraseDups.map fun Γ ↦ (Γ, d.store.sorts T.sig Γ)
  d.store.wf && checkSharedFrom T d.store (sortsFrom T d.store table) oracleOf d.entries #[]

/-- Whether a shared development checks, with no oracle. -/
def checkShared (T : Theory) (d : SDevelopment) : Bool := checkSharedWith T d fun _ ↦ Oracle.none

section Soundness

variable {T : Theory} {M : Model.{v} T.sig} {st : Store}

/-- The nodes of an entry that spell it denote its equations. -/
theorem SEntry.eqns_of_spells (hst : st.WF) {e : SEntry} (h : e.spells st = true) :
    e.hyps.map st.eqn = e.seq.hyps ∧ st.eqn e.concl = e.seq.concl := by
  simp only [SEntry.spells, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hlen, hz⟩, hl⟩, hr⟩ := h
  refine ⟨List.ext_getElem (by simpa using hlen) fun n h₁ h₂ ↦ ?_,
    Eqn.ext (Store.denote_of_matchTree hst _ hl) (Store.denote_of_matchTree hst _ hr)⟩
  have hn : n < e.hyps.length := by simpa using h₁
  have hm := hz (e.hyps[n], e.seq.hyps[n]) (by
    rw [List.mem_iff_getElem?]
    exact ⟨n, by rw [List.getElem?_zip_eq_some]; simp [hn, h₂]⟩)
  simp only at hm
  simp only [List.getElem_map]
  exact Eqn.ext (Store.denote_of_matchTree hst _ hm.1) (Store.denote_of_matchTree hst _ hm.2)

/-- Every sequent of a list of entries that checks is valid in every model of the theory in
which the environment's sequents are valid, when {lit}`sortsOf` gives the store's sorts. -/
theorem checkSharedFrom_sound (hM : IsModel T M) (hst : st.WF)
    {sortsOf : List ℕ → Array (Option ℕ)} (hso : ∀ Γ, sortsOf Γ = st.sorts T.sig Γ)
    {oracleOf : Seq → Oracle} (horc : ∀ a, (oracleOf a).Sound st M a.ctx a.hyps)
    (es : List SEntry) :
    ∀ E : Array Seq, (∀ a ∈ E, a.Valid M) → checkSharedFrom T st sortsOf oracleOf es E = true →
      ∀ e ∈ es, e.seq.Valid M :=
  es.rec (motive := fun es ↦ ∀ E : Array Seq, (∀ a ∈ E, a.Valid M) →
      checkSharedFrom T st sortsOf oracleOf es E = true → ∀ e ∈ es, e.seq.Valid M)
    (fun _ _ _ _ he ↦ absurd he (List.not_mem_nil))
    (fun e es ih E hE h ↦ by
      simp only [checkSharedFrom, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨⟨hsp, hc⟩, hrest⟩ := h
      rw [hso] at hc
      have he : e.seq.Valid M := by
        obtain ⟨hh, hq⟩ := SEntry.eqns_of_spells hst hsp
        have hv := scheck_sound hM hE hst e.seq.ctx (oracleOf e.seq) (horc e.seq) e.cert e.hyps
          e.concl (fun h hm ↦ hh ▸ hm) hc
        rw [hh, hq] at hv
        exact hv
      have hE' : ∀ a ∈ E.push e.seq, a.Valid M := by
        simp only [Array.mem_push]
        rintro a (ha | rfl)
        · exact hE a ha
        · exact he
      intro e' he'
      rcases List.mem_cons.mp he' with rfl | he'
      · exact he
      · exact ih _ hE' hrest e' he')

/-- The table of sorts gives the store's sorts in every context. -/
theorem sortsFrom_eq (st : Store) {table : List (List ℕ × Array (Option ℕ))}
    (ht : ∀ p ∈ table, p.2 = st.sorts T.sig p.1) (Γ : List ℕ) :
    sortsFrom T st table Γ = st.sorts T.sig Γ := by
  unfold sortsFrom
  rcases hf : table.find? (·.1 == Γ) with _ | p
  · rw [hf]
    rfl
  · have hp := List.find?_some hf
    rw [beq_iff_eq] at hp
    rw [hf, Option.map_some, Option.getD_some, ht p (List.mem_of_find?_eq_some hf), hp]

/-- Every sequent of a shared development that checks with sound oracles is valid in every
model of the theory. -/
theorem checkSharedWith_sound (hM : IsModel T M) {d : SDevelopment} {oracleOf : Seq → Oracle}
    (horc : ∀ a, (oracleOf a).Sound d.store M a.ctx a.hyps)
    (h : checkSharedWith T d oracleOf = true) : ∀ e ∈ d.entries, e.seq.Valid M := by
  simp only [checkSharedWith, Bool.and_eq_true] at h
  obtain ⟨hwf, hc⟩ := h
  have hst := Store.wf_of_wf d.store hwf
  refine checkSharedFrom_sound hM hst (sortsFrom_eq d.store fun p hp ↦ ?_) horc d.entries #[]
    (fun _ ha ↦ absurd ha (by simp)) hc
  obtain ⟨Γ, -, rfl⟩ := List.mem_map.mp hp
  rfl

/-- Every sequent of a shared development that checks is valid in every model of the theory. -/
theorem checkShared_sound (hM : IsModel T M) {d : SDevelopment} (h : checkShared T d = true) :
    ∀ e ∈ d.entries, e.seq.Valid M :=
  checkSharedWith_sound hM (fun a ↦ Oracle.none_sound d.store M a.ctx a.hyps) h

end Soundness

end Geb.PartialHorn

end
