import GebLean.LawvereNatBT
import GebLean.Utilities.NatERStyle

/-!
# Bounded Two-Sort Lawvere Theory over ℕ and Labeled Binary Trees

The bounded variant of the two-sort theory.  Morphisms are
indexed by domain arity `(n, m) : ℕ × ℕ` and output sort
(`.nat` or `.bt`).  The three recursive constructors —
`foldBTNat`, `foldBTBT`, `boundedNatRec` — carry explicit
`bound` parameters; their interp delegates to Layer 0
ER-style helpers (`Nat.foldBTLOnCodeERStyle`,
`Nat.boundedRecERStyle`) so that the categorical equivalence
with `LawvereERCat` is on-the-nose at the raw constructor
level.

Programmer-friendly auto-bound combinators (Layer 1) are
provided in `LawvereNatBTBoundedAuto.lean`; the equivalence
with `LawvereERCat` is in `LawvereERNatBTBoundedEquiv.lean`.

The two-stage architecture is documented in
`docs/superpowers/specs/2026-04-18-option-e-bounded-natbt-design.md`.
-/

namespace GebLean

/-- Morphism in the bounded two-sort Lawvere theory.  Indexed
by a domain arity `(n, m) : ℕ × ℕ` and an output sort
`σ : NatBTSort`.  The three recursive constructors —
`foldBTNat`, `foldBTBT`, `boundedNatRec` — carry an explicit
`bound` parameter so that interp can delegate to the Layer 0
ER-style helpers. -/
inductive NatBTMor1Bounded :
    (nm : ℕ × ℕ) → NatBTSort → Type
  | zero {nm : ℕ × ℕ} : NatBTMor1Bounded nm .nat
  | succ {nm : ℕ × ℕ} (x : NatBTMor1Bounded nm .nat) :
      NatBTMor1Bounded nm .nat
  | natProj {nm : ℕ × ℕ} (i : Fin nm.1) :
      NatBTMor1Bounded nm .nat
  | sub {nm : ℕ × ℕ}
      (a b : NatBTMor1Bounded nm .nat) :
      NatBTMor1Bounded nm .nat
  | compNat {nm nm' : ℕ × ℕ}
      (f : NatBTMor1Bounded nm' .nat)
      (gNat : Fin nm'.1 → NatBTMor1Bounded nm .nat)
      (gBT : Fin nm'.2 → NatBTMor1Bounded nm .bt) :
      NatBTMor1Bounded nm .nat
  | bsum {nm : ℕ × ℕ}
      (f : NatBTMor1Bounded (nm.1 + 1, nm.2) .nat) :
      NatBTMor1Bounded (nm.1 + 1, nm.2) .nat
  | bprod {nm : ℕ × ℕ}
      (f : NatBTMor1Bounded (nm.1 + 1, nm.2) .nat) :
      NatBTMor1Bounded (nm.1 + 1, nm.2) .nat
  | leafBT {nm : ℕ × ℕ}
      (label : NatBTMor1Bounded nm .nat) :
      NatBTMor1Bounded nm .bt
  | nodeBT {nm : ℕ × ℕ}
      (l r : NatBTMor1Bounded nm .bt) :
      NatBTMor1Bounded nm .bt
  | btProj {nm : ℕ × ℕ} (i : Fin nm.2) :
      NatBTMor1Bounded nm .bt
  | compBT {nm nm' : ℕ × ℕ}
      (f : NatBTMor1Bounded nm' .bt)
      (gNat : Fin nm'.1 → NatBTMor1Bounded nm .nat)
      (gBT : Fin nm'.2 → NatBTMor1Bounded nm .bt) :
      NatBTMor1Bounded nm .bt
  | foldBTNat {nm : ℕ × ℕ}
      (baseLeaf : NatBTMor1Bounded (nm.1 + 1, nm.2) .nat)
      (stepNode : NatBTMor1Bounded (nm.1 + 2, nm.2) .nat)
      (tree : NatBTMor1Bounded nm .bt)
      (bound : NatBTMor1Bounded (nm.1 + 1, nm.2) .nat) :
      NatBTMor1Bounded nm .nat
  | foldBTBT {nm : ℕ × ℕ}
      (baseLeaf : NatBTMor1Bounded (nm.1 + 1, nm.2) .bt)
      (stepNode : NatBTMor1Bounded (nm.1, nm.2 + 2) .bt)
      (tree : NatBTMor1Bounded nm .bt)
      (bound : NatBTMor1Bounded (nm.1 + 1, nm.2) .nat) :
      NatBTMor1Bounded nm .bt
  | boundedNatRec {nm : ℕ × ℕ}
      (base : NatBTMor1Bounded nm .nat)
      (step : NatBTMor1Bounded (nm.1 + 2, nm.2) .nat)
      (n : NatBTMor1Bounded nm .nat)
      (bound : NatBTMor1Bounded (nm.1 + 1, nm.2) .nat) :
      NatBTMor1Bounded nm .nat
  | encodeBT {nm : ℕ × ℕ}
      (t : NatBTMor1Bounded nm .bt) :
      NatBTMor1Bounded nm .nat
  | decodeBT {nm : ℕ × ℕ}
      (k : NatBTMor1Bounded nm .nat) :
      NatBTMor1Bounded nm .bt

/-- Standard interpretation of a bounded two-sort morphism.
The three recursive cases delegate to the Layer 0 ER-style
helpers `Nat.foldBTLOnCodeERStyle` and
`Nat.boundedRecERStyle`, mirroring `LawvereERCat`'s interp on
the nose. -/
def NatBTMor1Bounded.interp : {nm : ℕ × ℕ} → {σ : NatBTSort} →
    NatBTMor1Bounded nm σ → (Fin nm.1 → ℕ) →
    (Fin nm.2 → BTL) → σ.carrier
  | _, _, NatBTMor1Bounded.zero, _, _ => (0 : ℕ)
  | _, _, NatBTMor1Bounded.succ x, ctxN, ctxB =>
      Nat.succ (NatBTMor1Bounded.interp x ctxN ctxB)
  | _, _, NatBTMor1Bounded.natProj i, ctxN, _ => ctxN i
  | _, _, NatBTMor1Bounded.sub a b, ctxN, ctxB =>
      Nat.sub (NatBTMor1Bounded.interp a ctxN ctxB)
        (NatBTMor1Bounded.interp b ctxN ctxB)
  | _, _, NatBTMor1Bounded.compNat f gNat gBT, ctxN, ctxB =>
      NatBTMor1Bounded.interp f
        (fun i => NatBTMor1Bounded.interp (gNat i) ctxN ctxB)
        (fun i => NatBTMor1Bounded.interp (gBT i) ctxN ctxB)
  | _, _, NatBTMor1Bounded.bsum f, ctxN, ctxB =>
      natBSum (ctxN 0) (fun i =>
        NatBTMor1Bounded.interp f
          (Fin.cons i (Fin.tail ctxN)) ctxB)
  | _, _, NatBTMor1Bounded.bprod f, ctxN, ctxB =>
      natBProd (ctxN 0) (fun i =>
        NatBTMor1Bounded.interp f
          (Fin.cons i (Fin.tail ctxN)) ctxB)
  | _, _, NatBTMor1Bounded.leafBT label, ctxN, ctxB =>
      BTL.leaf (NatBTMor1Bounded.interp label ctxN ctxB)
  | _, _, NatBTMor1Bounded.nodeBT l r, ctxN, ctxB =>
      BTL.node (NatBTMor1Bounded.interp l ctxN ctxB)
        (NatBTMor1Bounded.interp r ctxN ctxB)
  | _, _, NatBTMor1Bounded.btProj i, _, ctxB => ctxB i
  | _, _, NatBTMor1Bounded.compBT f gNat gBT, ctxN, ctxB =>
      NatBTMor1Bounded.interp f
        (fun i => NatBTMor1Bounded.interp (gNat i) ctxN ctxB)
        (fun i => NatBTMor1Bounded.interp (gBT i) ctxN ctxB)
  | _, _,
      NatBTMor1Bounded.foldBTNat baseLeaf stepNode tree bound,
      ctxN, ctxB =>
    Nat.foldBTLOnCodeERStyle
      (fun lbl =>
        NatBTMor1Bounded.interp baseLeaf
          (Fin.cons lbl ctxN) ctxB)
      (fun a b =>
        NatBTMor1Bounded.interp stepNode
          (Fin.cons a (Fin.cons b ctxN)) ctxB)
      (fun j =>
        NatBTMor1Bounded.interp bound
          (Fin.cons j ctxN) ctxB)
      (NatBTMor1Bounded.interp tree ctxN ctxB).encode
  | _, _,
      NatBTMor1Bounded.foldBTBT baseLeaf stepNode tree bound,
      ctxN, ctxB =>
    let t := NatBTMor1Bounded.interp tree ctxN ctxB
    BTL.decode (Nat.foldBTLOnCodeERStyle
      (fun lbl =>
        (NatBTMor1Bounded.interp baseLeaf
          (Fin.cons lbl ctxN) ctxB).encode)
      (fun a b =>
        (NatBTMor1Bounded.interp stepNode ctxN
          (Fin.cons (BTL.decode a)
            (Fin.cons (BTL.decode b) ctxB))).encode)
      (fun j =>
        NatBTMor1Bounded.interp bound
          (Fin.cons j ctxN) ctxB)
      t.encode)
  | _, _,
      NatBTMor1Bounded.boundedNatRec base step n bound,
      ctxN, ctxB =>
    Nat.boundedRecERStyle
      (NatBTMor1Bounded.interp base ctxN ctxB)
      (fun j prev =>
        NatBTMor1Bounded.interp step
          (Fin.cons j (Fin.cons prev ctxN)) ctxB)
      (fun j =>
        NatBTMor1Bounded.interp bound
          (Fin.cons j ctxN) ctxB)
      (NatBTMor1Bounded.interp n ctxN ctxB)
  | _, _, NatBTMor1Bounded.encodeBT t, ctxN, ctxB =>
      BTL.encode (NatBTMor1Bounded.interp t ctxN ctxB)
  | _, _, NatBTMor1Bounded.decodeBT k, ctxN, ctxB =>
      BTL.decode (NatBTMor1Bounded.interp k ctxN ctxB)

/-- Interpretation of `zero`. -/
@[simp] theorem NatBTMor1Bounded.interp_zero
    {nm : ℕ × ℕ} (ctxN : Fin nm.1 → ℕ)
    (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1Bounded.zero (nm := nm)).interp ctxN ctxB =
      (0 : ℕ) := rfl

/-- Interpretation of `succ`. -/
@[simp] theorem NatBTMor1Bounded.interp_succ
    {nm : ℕ × ℕ} (x : NatBTMor1Bounded nm .nat)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1Bounded.succ x).interp ctxN ctxB =
      Nat.succ (x.interp ctxN ctxB) := rfl

/-- Interpretation of `natProj`. -/
@[simp] theorem NatBTMor1Bounded.interp_natProj
    {nm : ℕ × ℕ} (i : Fin nm.1)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1Bounded.natProj (nm := nm) i).interp ctxN ctxB =
      ctxN i := rfl

/-- Interpretation of `sub`. -/
@[simp] theorem NatBTMor1Bounded.interp_sub
    {nm : ℕ × ℕ} (a b : NatBTMor1Bounded nm .nat)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1Bounded.sub a b).interp ctxN ctxB =
      Nat.sub (a.interp ctxN ctxB) (b.interp ctxN ctxB) :=
  rfl

/-- Interpretation of `compNat`. -/
@[simp] theorem NatBTMor1Bounded.interp_compNat
    {nm nm' : ℕ × ℕ}
    (f : NatBTMor1Bounded nm' .nat)
    (gNat : Fin nm'.1 → NatBTMor1Bounded nm .nat)
    (gBT : Fin nm'.2 → NatBTMor1Bounded nm .bt)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1Bounded.compNat f gNat gBT).interp ctxN ctxB =
      f.interp
        (fun i => (gNat i).interp ctxN ctxB)
        (fun i => (gBT i).interp ctxN ctxB) := rfl

/-- Interpretation of `bsum`. -/
@[simp] theorem NatBTMor1Bounded.interp_bsum
    {nm : ℕ × ℕ}
    (f : NatBTMor1Bounded (nm.1 + 1, nm.2) .nat)
    (ctxN : Fin (nm.1 + 1) → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1Bounded.bsum f).interp ctxN ctxB =
      natBSum (ctxN 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail ctxN)) ctxB) := rfl

/-- Interpretation of `bprod`. -/
@[simp] theorem NatBTMor1Bounded.interp_bprod
    {nm : ℕ × ℕ}
    (f : NatBTMor1Bounded (nm.1 + 1, nm.2) .nat)
    (ctxN : Fin (nm.1 + 1) → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1Bounded.bprod f).interp ctxN ctxB =
      natBProd (ctxN 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail ctxN)) ctxB) := rfl

/-- Interpretation of `leafBT`. -/
@[simp] theorem NatBTMor1Bounded.interp_leafBT
    {nm : ℕ × ℕ} (label : NatBTMor1Bounded nm .nat)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1Bounded.leafBT label).interp ctxN ctxB =
      BTL.leaf (label.interp ctxN ctxB) := rfl

/-- Interpretation of `nodeBT`. -/
@[simp] theorem NatBTMor1Bounded.interp_nodeBT
    {nm : ℕ × ℕ} (l r : NatBTMor1Bounded nm .bt)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1Bounded.nodeBT l r).interp ctxN ctxB =
      BTL.node (l.interp ctxN ctxB)
        (r.interp ctxN ctxB) := rfl

/-- Interpretation of `btProj`. -/
@[simp] theorem NatBTMor1Bounded.interp_btProj
    {nm : ℕ × ℕ} (i : Fin nm.2)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1Bounded.btProj (nm := nm) i).interp ctxN ctxB =
      ctxB i := rfl

/-- Interpretation of `compBT`. -/
@[simp] theorem NatBTMor1Bounded.interp_compBT
    {nm nm' : ℕ × ℕ}
    (f : NatBTMor1Bounded nm' .bt)
    (gNat : Fin nm'.1 → NatBTMor1Bounded nm .nat)
    (gBT : Fin nm'.2 → NatBTMor1Bounded nm .bt)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1Bounded.compBT f gNat gBT).interp ctxN ctxB =
      f.interp
        (fun i => (gNat i).interp ctxN ctxB)
        (fun i => (gBT i).interp ctxN ctxB) := rfl

/-- Interpretation of `foldBTNat`.  Delegates to the Layer 0
ER-style helper `Nat.foldBTLOnCodeERStyle`, encoding the tree
to ℕ before invoking the Nat-level fold. -/
@[simp] theorem NatBTMor1Bounded.interp_foldBTNat
    {nm : ℕ × ℕ}
    (baseLeaf : NatBTMor1Bounded (nm.1 + 1, nm.2) .nat)
    (stepNode : NatBTMor1Bounded (nm.1 + 2, nm.2) .nat)
    (tree : NatBTMor1Bounded nm .bt)
    (bound : NatBTMor1Bounded (nm.1 + 1, nm.2) .nat)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1Bounded.foldBTNat baseLeaf stepNode tree
        bound).interp ctxN ctxB =
      Nat.foldBTLOnCodeERStyle
        (fun lbl =>
          baseLeaf.interp (Fin.cons lbl ctxN) ctxB)
        (fun a b =>
          stepNode.interp
            (Fin.cons a (Fin.cons b ctxN)) ctxB)
        (fun j => bound.interp (Fin.cons j ctxN) ctxB)
        (tree.interp ctxN ctxB).encode := rfl

/-- Interpretation of `foldBTBT`.  Delegates to the Layer 0
ER-style helper `Nat.foldBTLOnCodeERStyle`, encoding the tree
and each handler's BTL output to ℕ and decoding the final
result back to BTL. -/
@[simp] theorem NatBTMor1Bounded.interp_foldBTBT
    {nm : ℕ × ℕ}
    (baseLeaf : NatBTMor1Bounded (nm.1 + 1, nm.2) .bt)
    (stepNode : NatBTMor1Bounded (nm.1, nm.2 + 2) .bt)
    (tree : NatBTMor1Bounded nm .bt)
    (bound : NatBTMor1Bounded (nm.1 + 1, nm.2) .nat)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1Bounded.foldBTBT baseLeaf stepNode tree
        bound).interp ctxN ctxB =
      BTL.decode (Nat.foldBTLOnCodeERStyle
        (fun lbl =>
          (baseLeaf.interp (Fin.cons lbl ctxN) ctxB).encode)
        (fun a b =>
          (stepNode.interp ctxN
            (Fin.cons (BTL.decode a)
              (Fin.cons (BTL.decode b) ctxB))).encode)
        (fun j => bound.interp (Fin.cons j ctxN) ctxB)
        (tree.interp ctxN ctxB).encode) := rfl

/-- Interpretation of `boundedNatRec`.  Delegates to the
Layer 0 ER-style helper `Nat.boundedRecERStyle`. -/
@[simp] theorem NatBTMor1Bounded.interp_boundedNatRec
    {nm : ℕ × ℕ}
    (base : NatBTMor1Bounded nm .nat)
    (step : NatBTMor1Bounded (nm.1 + 2, nm.2) .nat)
    (n : NatBTMor1Bounded nm .nat)
    (bound : NatBTMor1Bounded (nm.1 + 1, nm.2) .nat)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1Bounded.boundedNatRec base step n bound).interp
        ctxN ctxB =
      Nat.boundedRecERStyle
        (base.interp ctxN ctxB)
        (fun j prev =>
          step.interp
            (Fin.cons j (Fin.cons prev ctxN)) ctxB)
        (fun j => bound.interp (Fin.cons j ctxN) ctxB)
        (n.interp ctxN ctxB) := rfl

/-- Interpretation of `encodeBT`. -/
@[simp] theorem NatBTMor1Bounded.interp_encodeBT
    {nm : ℕ × ℕ} (t : NatBTMor1Bounded nm .bt)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1Bounded.encodeBT t).interp ctxN ctxB =
      (t.interp ctxN ctxB).encode := rfl

/-- Interpretation of `decodeBT`. -/
@[simp] theorem NatBTMor1Bounded.interp_decodeBT
    {nm : ℕ × ℕ} (k : NatBTMor1Bounded nm .nat)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1Bounded.decodeBT k).interp ctxN ctxB =
      BTL.decode (k.interp ctxN ctxB) := rfl

end GebLean
