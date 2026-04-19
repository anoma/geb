import GebLean.LawvereER
import GebLean.LawvereERQuot
import GebLean.LawvereBT
import GebLean.LawvereBTPrimrec
import GebLean.Utilities.SzudzikSeq

/-!
# Two-Sort Lawvere Theory over ℕ and Labeled Binary Trees

Morphisms indexed by domain arity `(n, m) : ℕ × ℕ` and output
sort (`.nat` or `.bt`).  Generators combine `LawvereER`'s ℕ-sort
arithmetic, structural BT operations (`leaf`, `node`, `proj`,
`comp`, `foldBT`), and bridges `encodeBT` / `decodeBT`.  The
combined theory is equivalent as a category to `LawvereER`.

See `docs/superpowers/specs/2026-04-17-lawvere-natbt-design.md`
for rationale and design decisions.

**Version note**: this file defines the *bounded* variant of the
two-sort theory. `foldBTNat` and `foldBTBT` carry explicit `bound`
parameters (added in Stage β.b). The ramified variant is in
`LawvereNatBTRamified*.lean`. The two-stage equivalence
`LawvereERCat ≃ LawvereNatBT_bounded ≃ LawvereNatBT_ramified`
is documented in
`docs/superpowers/specs/2026-04-18-lawvere-natbt-two-stage-design.md`.
-/

namespace GebLean

/-- Labeled binary tree: leaves carry a ℕ label; internal nodes
are binary-branching.  The unlabeled `BT` from
`GebLean/LawvereBT.lean` embeds as `BTL` with all leaf labels
equal to 0 (a decidable subobject in the lex completion). -/
inductive BTL : Type where
  | leaf (n : ℕ) : BTL
  | node (l r : BTL) : BTL
  deriving Repr, DecidableEq, Inhabited

/-- Catamorphism over `BTL`.  `baseLeaf` processes the label at a
leaf; `stepNode` combines the two recursive results at a node. -/
def BTL.fold {α : Type*} (baseLeaf : ℕ → α)
    (stepNode : α → α → α) : BTL → α
  | BTL.leaf n => baseLeaf n
  | BTL.node l r =>
      stepNode (BTL.fold baseLeaf stepNode l)
        (BTL.fold baseLeaf stepNode r)

@[simp] theorem BTL.fold_leaf {α : Type*} (baseLeaf : ℕ → α)
    (stepNode : α → α → α) (n : ℕ) :
    BTL.fold baseLeaf stepNode (BTL.leaf n) = baseLeaf n := rfl

@[simp] theorem BTL.fold_node {α : Type*} (baseLeaf : ℕ → α)
    (stepNode : α → α → α) (l r : BTL) :
    BTL.fold baseLeaf stepNode (BTL.node l r) =
      stepNode (BTL.fold baseLeaf stepNode l)
        (BTL.fold baseLeaf stepNode r) := rfl

/-- Szudzik-based Gödel encoding of labeled BT.
`leaf n` maps to `2 * n`;
`node l r` maps to `2 * pair(encode l)(encode r) + 1`.
Even codes represent leaves (with the label recoverable as
`n / 2`); odd codes represent nodes. -/
def BTL.encode : BTL → ℕ
  | BTL.leaf n => 2 * n
  | BTL.node l r => 2 * (Nat.pair l.encode r.encode) + 1

/-- Inverse of `BTL.encode`: an even `n` decodes to
`BTL.leaf (n / 2)`; an odd `n` decodes to a node whose children
come from Szudzik-unpairing `n / 2`. -/
def BTL.decode : ℕ → BTL
  | 0 => BTL.leaf 0
  | n + 1 =>
      if (n + 1) % 2 = 0 then BTL.leaf ((n + 1) / 2)
      else
        BTL.node
          (BTL.decode (Nat.unpair ((n + 1) / 2)).1)
          (BTL.decode (Nat.unpair ((n + 1) / 2)).2)
  termination_by n => n
  decreasing_by
    all_goals
      have hdiv : (n + 1) / 2 < n + 1 :=
        Nat.div_lt_self (Nat.succ_pos n) (by decide)
      first
        | exact Nat.lt_of_le_of_lt (Nat.unpair_left_le _) hdiv
        | exact Nat.lt_of_le_of_lt (Nat.unpair_right_le _) hdiv

theorem BTL.decode_encode (t : BTL) :
    BTL.decode t.encode = t := by
  induction t with
  | leaf k =>
      change BTL.decode (2 * k) = BTL.leaf k
      match h2k : 2 * k with
      | 0 =>
          have : k = 0 := by omega
          subst this
          unfold BTL.decode
          rfl
      | m + 1 =>
          have heven : (m + 1) % 2 = 0 := by omega
          have hdiv : (m + 1) / 2 = k := by omega
          simp [BTL.decode, heven, hdiv]
  | node l r ihl ihr =>
      change BTL.decode (2 * Nat.pair l.encode r.encode + 1) =
        BTL.node l r
      set p := Nat.pair l.encode r.encode with hp
      change BTL.decode (2 * p + 1) = BTL.node l r
      have hodd : (2 * p + 1) % 2 ≠ 0 := by omega
      have hdiv : (2 * p + 1) / 2 = p := by omega
      unfold BTL.decode
      simp only [hodd, if_false, hdiv]
      rw [show Nat.unpair p = (l.encode, r.encode) from
        by rw [hp]; exact Nat.unpair_pair _ _]
      simp [ihl, ihr]

theorem BTL.encode_decode (n : ℕ) :
    (BTL.decode n).encode = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n, ih with
    | 0, _ =>
        unfold BTL.decode
        rfl
    | k + 1, ih =>
        unfold BTL.decode
        by_cases h : (k + 1) % 2 = 0
        · simp only [h, if_true]
          change 2 * ((k + 1) / 2) = k + 1
          omega
        · simp only [h, if_false]
          have hdiv : (k + 1) / 2 < k + 1 :=
            Nat.div_lt_self (Nat.succ_pos k) (by decide)
          have h1 : (Nat.unpair ((k + 1) / 2)).1 ≤ (k + 1) / 2 :=
            Nat.unpair_left_le _
          have h2 : (Nat.unpair ((k + 1) / 2)).2 ≤ (k + 1) / 2 :=
            Nat.unpair_right_le _
          have hlt1 : (Nat.unpair ((k + 1) / 2)).1 < k + 1 := by omega
          have hlt2 : (Nat.unpair ((k + 1) / 2)).2 < k + 1 := by omega
          have ihl := ih _ hlt1
          have ihr := ih _ hlt2
          change
            2 * Nat.pair (BTL.decode (Nat.unpair ((k + 1) / 2)).1).encode
              (BTL.decode (Nat.unpair ((k + 1) / 2)).2).encode + 1 =
            k + 1
          rw [ihl, ihr, Nat.pair_unpair]
          omega

/-- Discriminator for the output sort of a two-sort morphism.
`.nat` means the morphism produces a natural number; `.bt` means
it produces a labeled binary tree. -/
inductive NatBTSort : Type where
  | nat
  | bt
  deriving DecidableEq, Repr

/-- Target type for a morphism's output sort under the standard
interpretation. -/
def NatBTSort.carrier : NatBTSort → Type
  | .nat => ℕ
  | .bt  => BTL

/-- Morphism in the two-sort Lawvere theory.  Indexed by a
domain arity `(n, m) : ℕ × ℕ` and an output sort
`σ : NatBTSort`.  Constructors partition into ℕ-sort generators
(mirroring `LawvereER`), BT-sort generators, and bridges. -/
inductive NatBTMor1 : (ℕ × ℕ) → NatBTSort → Type where
  | zero {nm : ℕ × ℕ} : NatBTMor1 nm .nat
  | succ {nm : ℕ × ℕ} (x : NatBTMor1 nm .nat) :
      NatBTMor1 nm .nat
  | natProj {nm : ℕ × ℕ} (i : Fin nm.1) : NatBTMor1 nm .nat
  | sub {nm : ℕ × ℕ} (a b : NatBTMor1 nm .nat) :
      NatBTMor1 nm .nat
  | compNat {nm nm' : ℕ × ℕ}
      (f : NatBTMor1 nm' .nat)
      (gNat : Fin nm'.1 → NatBTMor1 nm .nat)
      (gBT : Fin nm'.2 → NatBTMor1 nm .bt) :
      NatBTMor1 nm .nat
  | bsum {nm : ℕ × ℕ}
      (f : NatBTMor1 (nm.1 + 1, nm.2) .nat) :
      NatBTMor1 (nm.1 + 1, nm.2) .nat
  | bprod {nm : ℕ × ℕ}
      (f : NatBTMor1 (nm.1 + 1, nm.2) .nat) :
      NatBTMor1 (nm.1 + 1, nm.2) .nat
  | leafBT {nm : ℕ × ℕ}
      (label : NatBTMor1 nm .nat) :
      NatBTMor1 nm .bt
  | nodeBT {nm : ℕ × ℕ}
      (l r : NatBTMor1 nm .bt) :
      NatBTMor1 nm .bt
  | btProj {nm : ℕ × ℕ} (i : Fin nm.2) : NatBTMor1 nm .bt
  | compBT {nm nm' : ℕ × ℕ}
      (f : NatBTMor1 nm' .bt)
      (gNat : Fin nm'.1 → NatBTMor1 nm .nat)
      (gBT : Fin nm'.2 → NatBTMor1 nm .bt) :
      NatBTMor1 nm .bt
  | foldBTNat {nm : ℕ × ℕ}
      (baseLeaf : NatBTMor1 (nm.1 + 1, nm.2) .nat)
      (stepNode : NatBTMor1 (nm.1 + 2, nm.2) .nat)
      (tree : NatBTMor1 nm .bt)
      (bound : NatBTMor1 (nm.1 + 1, nm.2) .nat) :
      NatBTMor1 nm .nat
  | foldBTBT {nm : ℕ × ℕ}
      (baseLeaf : NatBTMor1 (nm.1 + 1, nm.2) .bt)
      (stepNode : NatBTMor1 (nm.1, nm.2 + 2) .bt)
      (tree : NatBTMor1 nm .bt) :
      NatBTMor1 nm .bt
  | encodeBT {nm : ℕ × ℕ}
      (t : NatBTMor1 nm .bt) : NatBTMor1 nm .nat
  | decodeBT {nm : ℕ × ℕ}
      (k : NatBTMor1 nm .nat) : NatBTMor1 nm .bt

/-- Standard interpretation of a two-sort morphism: maps a
domain context `(ctxN, ctxB)` of arities `(nm.1, nm.2)` to an
element of `σ.carrier`. -/
def NatBTMor1.interp : {nm : ℕ × ℕ} → {σ : NatBTSort} →
    NatBTMor1 nm σ → (Fin nm.1 → ℕ) → (Fin nm.2 → BTL) →
    σ.carrier
  | _, _, NatBTMor1.zero, _, _ => (0 : ℕ)
  | _, _, NatBTMor1.succ x, ctxN, ctxB =>
      Nat.succ (NatBTMor1.interp x ctxN ctxB)
  | _, _, NatBTMor1.natProj i, ctxN, _ => ctxN i
  | _, _, NatBTMor1.sub a b, ctxN, ctxB =>
      Nat.sub (NatBTMor1.interp a ctxN ctxB)
        (NatBTMor1.interp b ctxN ctxB)
  | _, _, NatBTMor1.compNat f gNat gBT, ctxN, ctxB =>
      NatBTMor1.interp f
        (fun i => NatBTMor1.interp (gNat i) ctxN ctxB)
        (fun i => NatBTMor1.interp (gBT i) ctxN ctxB)
  | _, _, NatBTMor1.bsum f, ctxN, ctxB =>
      natBSum (ctxN 0) (fun i =>
        NatBTMor1.interp f (Fin.cons i (Fin.tail ctxN)) ctxB)
  | _, _, NatBTMor1.bprod f, ctxN, ctxB =>
      natBProd (ctxN 0) (fun i =>
        NatBTMor1.interp f (Fin.cons i (Fin.tail ctxN)) ctxB)
  | _, _, NatBTMor1.leafBT label, ctxN, ctxB =>
      BTL.leaf (NatBTMor1.interp label ctxN ctxB)
  | _, _, NatBTMor1.nodeBT l r, ctxN, ctxB =>
      BTL.node (NatBTMor1.interp l ctxN ctxB)
        (NatBTMor1.interp r ctxN ctxB)
  | _, _, NatBTMor1.btProj i, _, ctxB => ctxB i
  | _, _, NatBTMor1.compBT f gNat gBT, ctxN, ctxB =>
      NatBTMor1.interp f
        (fun i => NatBTMor1.interp (gNat i) ctxN ctxB)
        (fun i => NatBTMor1.interp (gBT i) ctxN ctxB)
  | _, _, NatBTMor1.foldBTNat baseLeaf stepNode tree bound, ctxN,
        ctxB =>
      let t := NatBTMor1.interp tree ctxN ctxB
      let boundVal :=
        NatBTMor1.interp bound (Fin.cons t.encode ctxN) ctxB
      Nat.min (Nat.foldBTLOnCode
        (fun lbl =>
          NatBTMor1.interp baseLeaf (Fin.cons lbl ctxN) ctxB)
        (fun a b =>
          NatBTMor1.interp stepNode
            (Fin.cons a (Fin.cons b ctxN)) ctxB)
        t.encode) boundVal
  | _, _, NatBTMor1.foldBTBT baseLeaf stepNode tree, ctxN, ctxB =>
      BTL.fold
        (fun lbl =>
          NatBTMor1.interp baseLeaf (Fin.cons lbl ctxN) ctxB)
        (fun a b =>
          NatBTMor1.interp stepNode ctxN
            (Fin.cons a (Fin.cons b ctxB)))
        (NatBTMor1.interp tree ctxN ctxB)
  | _, _, NatBTMor1.encodeBT t, ctxN, ctxB =>
      BTL.encode (NatBTMor1.interp t ctxN ctxB)
  | _, _, NatBTMor1.decodeBT k, ctxN, ctxB =>
      BTL.decode (NatBTMor1.interp k ctxN ctxB)

/-- Interpretation of `zero`. -/
@[simp] theorem NatBTMor1.interp_zero
    {nm : ℕ × ℕ} (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1.zero (nm := nm)).interp ctxN ctxB = (0 : ℕ) :=
  rfl

/-- Interpretation of `succ`. -/
@[simp] theorem NatBTMor1.interp_succ
    {nm : ℕ × ℕ} (x : NatBTMor1 nm .nat)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1.succ x).interp ctxN ctxB =
      Nat.succ (x.interp ctxN ctxB) := rfl

/-- Interpretation of `natProj`. -/
@[simp] theorem NatBTMor1.interp_natProj
    {nm : ℕ × ℕ} (i : Fin nm.1)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1.natProj (nm := nm) i).interp ctxN ctxB =
      ctxN i := rfl

/-- Interpretation of `sub`. -/
@[simp] theorem NatBTMor1.interp_sub
    {nm : ℕ × ℕ} (a b : NatBTMor1 nm .nat)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1.sub a b).interp ctxN ctxB =
      Nat.sub (a.interp ctxN ctxB) (b.interp ctxN ctxB) := rfl

/-- Interpretation of `compNat`. -/
@[simp] theorem NatBTMor1.interp_compNat
    {nm nm' : ℕ × ℕ}
    (f : NatBTMor1 nm' .nat)
    (gNat : Fin nm'.1 → NatBTMor1 nm .nat)
    (gBT : Fin nm'.2 → NatBTMor1 nm .bt)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1.compNat f gNat gBT).interp ctxN ctxB =
      f.interp
        (fun i => (gNat i).interp ctxN ctxB)
        (fun i => (gBT i).interp ctxN ctxB) := rfl

/-- Interpretation of `bsum`. -/
@[simp] theorem NatBTMor1.interp_bsum
    {nm : ℕ × ℕ}
    (f : NatBTMor1 (nm.1 + 1, nm.2) .nat)
    (ctxN : Fin (nm.1 + 1) → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1.bsum f).interp ctxN ctxB =
      natBSum (ctxN 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail ctxN)) ctxB) := rfl

/-- Interpretation of `bprod`. -/
@[simp] theorem NatBTMor1.interp_bprod
    {nm : ℕ × ℕ}
    (f : NatBTMor1 (nm.1 + 1, nm.2) .nat)
    (ctxN : Fin (nm.1 + 1) → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1.bprod f).interp ctxN ctxB =
      natBProd (ctxN 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail ctxN)) ctxB) := rfl

/-- Interpretation of `leafBT`. -/
@[simp] theorem NatBTMor1.interp_leafBT
    {nm : ℕ × ℕ} (label : NatBTMor1 nm .nat)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1.leafBT label).interp ctxN ctxB =
      BTL.leaf (label.interp ctxN ctxB) := rfl

/-- Interpretation of `nodeBT`. -/
@[simp] theorem NatBTMor1.interp_nodeBT
    {nm : ℕ × ℕ} (l r : NatBTMor1 nm .bt)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1.nodeBT l r).interp ctxN ctxB =
      BTL.node (l.interp ctxN ctxB) (r.interp ctxN ctxB) := rfl

/-- Interpretation of `btProj`. -/
@[simp] theorem NatBTMor1.interp_btProj
    {nm : ℕ × ℕ} (i : Fin nm.2)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1.btProj (nm := nm) i).interp ctxN ctxB =
      ctxB i := rfl

/-- Interpretation of `compBT`. -/
@[simp] theorem NatBTMor1.interp_compBT
    {nm nm' : ℕ × ℕ}
    (f : NatBTMor1 nm' .bt)
    (gNat : Fin nm'.1 → NatBTMor1 nm .nat)
    (gBT : Fin nm'.2 → NatBTMor1 nm .bt)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1.compBT f gNat gBT).interp ctxN ctxB =
      f.interp
        (fun i => (gNat i).interp ctxN ctxB)
        (fun i => (gBT i).interp ctxN ctxB) := rfl

/-- Interpretation of `foldBTNat`. -/
@[simp] theorem NatBTMor1.interp_foldBTNat
    {nm : ℕ × ℕ}
    (baseLeaf : NatBTMor1 (nm.1 + 1, nm.2) .nat)
    (stepNode : NatBTMor1 (nm.1 + 2, nm.2) .nat)
    (tree : NatBTMor1 nm .bt)
    (bound : NatBTMor1 (nm.1 + 1, nm.2) .nat)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1.foldBTNat baseLeaf stepNode tree bound).interp
        ctxN ctxB =
      Nat.min (Nat.foldBTLOnCode
        (fun lbl => baseLeaf.interp (Fin.cons lbl ctxN) ctxB)
        (fun a b =>
          stepNode.interp (Fin.cons a (Fin.cons b ctxN)) ctxB)
        (tree.interp ctxN ctxB).encode)
        (bound.interp
          (Fin.cons (tree.interp ctxN ctxB).encode ctxN) ctxB)
  := rfl

/-- Interpretation of `foldBTBT`. -/
@[simp] theorem NatBTMor1.interp_foldBTBT
    {nm : ℕ × ℕ}
    (baseLeaf : NatBTMor1 (nm.1 + 1, nm.2) .bt)
    (stepNode : NatBTMor1 (nm.1, nm.2 + 2) .bt)
    (tree : NatBTMor1 nm .bt)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1.foldBTBT baseLeaf stepNode tree).interp
        ctxN ctxB =
      BTL.fold
        (fun lbl => baseLeaf.interp (Fin.cons lbl ctxN) ctxB)
        (fun a b =>
          stepNode.interp ctxN
            (Fin.cons a (Fin.cons b ctxB)))
        (tree.interp ctxN ctxB) := rfl

/-- Interpretation of `encodeBT`. -/
@[simp] theorem NatBTMor1.interp_encodeBT
    {nm : ℕ × ℕ} (t : NatBTMor1 nm .bt)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1.encodeBT t).interp ctxN ctxB =
      (t.interp ctxN ctxB).encode := rfl

/-- Interpretation of `decodeBT`. -/
@[simp] theorem NatBTMor1.interp_decodeBT
    {nm : ℕ × ℕ} (k : NatBTMor1 nm .nat)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1.decodeBT k).interp ctxN ctxB =
      BTL.decode (k.interp ctxN ctxB) := rfl

/-- A morphism `(n, m) → (n', m')` in the two-sort theory:
`n'` ℕ-valued components and `m'` BT-valued components, each a
`NatBTMor1` with domain arity `(n, m)`. -/
@[ext]
structure NatBTMorN (nm nm' : ℕ × ℕ) where
  natComps : Fin nm'.1 → NatBTMor1 nm .nat
  btComps  : Fin nm'.2 → NatBTMor1 nm .bt

/-- Identity morphism `(n, m) → (n, m)`: tuple of projections at
each sort. -/
def NatBTMorN.id (nm : ℕ × ℕ) : NatBTMorN nm nm where
  natComps i := NatBTMor1.natProj i
  btComps i := NatBTMor1.btProj i

/-- Composition of two-sort tuples via `compNat` / `compBT` at
each component. -/
def NatBTMorN.comp {nm nm' nm'' : ℕ × ℕ}
    (f : NatBTMorN nm nm') (g : NatBTMorN nm' nm'') :
    NatBTMorN nm nm'' where
  natComps i :=
    NatBTMor1.compNat (g.natComps i) f.natComps f.btComps
  btComps i :=
    NatBTMor1.compBT (g.btComps i) f.natComps f.btComps

/-- Tuple interpretation: apply `NatBTMor1.interp` at each
component. -/
def NatBTMorN.interp {nm nm' : ℕ × ℕ}
    (f : NatBTMorN nm nm')
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (Fin nm'.1 → ℕ) × (Fin nm'.2 → BTL) :=
  (fun i => (f.natComps i).interp ctxN ctxB,
   fun i => (f.btComps i).interp ctxN ctxB)

@[simp] theorem NatBTMorN.interp_id (nm : ℕ × ℕ)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMorN.id nm).interp ctxN ctxB = (ctxN, ctxB) := by
  simp [NatBTMorN.id, NatBTMorN.interp]

@[simp] theorem NatBTMorN.interp_comp
    {nm nm' nm'' : ℕ × ℕ}
    (f : NatBTMorN nm nm') (g : NatBTMorN nm' nm'')
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMorN.comp f g).interp ctxN ctxB =
      let ctxN' := (f.interp ctxN ctxB).1
      let ctxB' := (f.interp ctxN ctxB).2
      g.interp ctxN' ctxB' := by
  simp [NatBTMorN.comp, NatBTMorN.interp]

/-- Terminal morphism into arity `(0, 0)`: the empty tuple. -/
def NatBTMorN.terminal (nm : ℕ × ℕ) : NatBTMorN nm (0, 0) where
  natComps i := i.elim0
  btComps i := i.elim0

/-- First projection from the product arity
`(nm₁.1 + nm₂.1, nm₁.2 + nm₂.2)`. -/
def NatBTMorN.fst {nm₁ nm₂ : ℕ × ℕ} :
    NatBTMorN (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2) nm₁ where
  natComps i := NatBTMor1.natProj (Fin.castAdd nm₂.1 i)
  btComps i := NatBTMor1.btProj (Fin.castAdd nm₂.2 i)

/-- Second projection from the product arity
`(nm₁.1 + nm₂.1, nm₁.2 + nm₂.2)`. -/
def NatBTMorN.snd {nm₁ nm₂ : ℕ × ℕ} :
    NatBTMorN (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2) nm₂ where
  natComps i := NatBTMor1.natProj (Fin.natAdd nm₁.1 i)
  btComps i := NatBTMor1.btProj (Fin.natAdd nm₁.2 i)

/-- Pairing: given morphisms into `nm₁` and `nm₂`, build one into
`(nm₁.1 + nm₂.1, nm₁.2 + nm₂.2)` via `Fin.addCases`. -/
def NatBTMorN.pair {nm nm₁ nm₂ : ℕ × ℕ}
    (f : NatBTMorN nm nm₁) (g : NatBTMorN nm nm₂) :
    NatBTMorN nm (nm₁.1 + nm₂.1, nm₁.2 + nm₂.2) where
  natComps := Fin.addCases f.natComps g.natComps
  btComps := Fin.addCases f.btComps g.btComps

@[simp] theorem NatBTMorN.interp_terminal
    {nm : ℕ × ℕ} (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMorN.terminal nm).interp ctxN ctxB =
      ((fun i => i.elim0), (fun i => i.elim0)) := by
  apply Prod.ext
  · exact funext (fun i => i.elim0)
  · exact funext (fun i => i.elim0)

@[simp] theorem NatBTMorN.interp_fst
    {nm₁ nm₂ : ℕ × ℕ}
    (ctxN : Fin (nm₁.1 + nm₂.1) → ℕ)
    (ctxB : Fin (nm₁.2 + nm₂.2) → BTL) :
    (NatBTMorN.fst (nm₁ := nm₁) (nm₂ := nm₂)).interp
        ctxN ctxB =
      ((fun i => ctxN (Fin.castAdd nm₂.1 i)),
       (fun i => ctxB (Fin.castAdd nm₂.2 i))) := rfl

@[simp] theorem NatBTMorN.interp_snd
    {nm₁ nm₂ : ℕ × ℕ}
    (ctxN : Fin (nm₁.1 + nm₂.1) → ℕ)
    (ctxB : Fin (nm₁.2 + nm₂.2) → BTL) :
    (NatBTMorN.snd (nm₁ := nm₁) (nm₂ := nm₂)).interp
        ctxN ctxB =
      ((fun i => ctxN (Fin.natAdd nm₁.1 i)),
       (fun i => ctxB (Fin.natAdd nm₁.2 i))) := rfl

@[simp] theorem NatBTMorN.interp_pair
    {nm nm₁ nm₂ : ℕ × ℕ}
    (f : NatBTMorN nm nm₁) (g : NatBTMorN nm nm₂)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMorN.pair f g).interp ctxN ctxB =
      ((fun i => Fin.addCases
          (fun j => (f.natComps j).interp ctxN ctxB)
          (fun j => (g.natComps j).interp ctxN ctxB) i),
       (fun i => Fin.addCases
          (fun j => (f.btComps j).interp ctxN ctxB)
          (fun j => (g.btComps j).interp ctxN ctxB) i)) := by
  apply Prod.ext
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [NatBTMorN.interp, NatBTMorN.pair]
    · simp [NatBTMorN.interp, NatBTMorN.pair]
  · funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [NatBTMorN.interp, NatBTMorN.pair]
    · simp [NatBTMorN.interp, NatBTMorN.pair]

end GebLean
