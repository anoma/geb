import GebLean.LawvereER
import GebLean.LawvereERQuot
import GebLean.LawvereBT
import GebLean.LawvereBTPrimrec

/-!
# Two-Sort Lawvere Theory over ℕ and Labeled Binary Trees

Morphisms indexed by domain arity `(n, m) : ℕ × ℕ` and output
sort (`.nat` or `.bt`).  Generators combine `LawvereER`'s ℕ-sort
arithmetic, structural BT operations (`leaf`, `node`, `proj`,
`comp`, `foldBT`), and bridges `encodeBT` / `decodeBT`.  The
combined theory is equivalent as a category to `LawvereER`.

See `docs/superpowers/specs/2026-04-17-lawvere-natbt-design.md`
for rationale and design decisions.
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
      (gBT  : Fin nm'.2 → NatBTMor1 nm .bt) :
      NatBTMor1 nm .nat
  | bsum {nm : ℕ × ℕ}
      (f : NatBTMor1 (nm.1 + 1, nm.2) .nat) :
      NatBTMor1 nm .nat
  | bprod {nm : ℕ × ℕ}
      (f : NatBTMor1 (nm.1 + 1, nm.2) .nat) :
      NatBTMor1 nm .nat
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
      (gBT  : Fin nm'.2 → NatBTMor1 nm .bt) :
      NatBTMor1 nm .bt
  | foldBTNat {nm : ℕ × ℕ}
      (baseLeaf : NatBTMor1 (nm.1 + 1, nm.2) .nat)
      (stepNode : NatBTMor1 (nm.1, nm.2 + 2) .nat)
      (tree : NatBTMor1 nm .bt) :
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

end GebLean
