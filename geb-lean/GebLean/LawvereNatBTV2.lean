import GebLean.LawvereNatBT
import GebLean.Utilities.ERArith
import GebLean.Utilities.ERTreeArith
import GebLean.LawvereERBoundComputable

/-!
# `LawvereNatBTV2`: Bottom-Up Two-Sort Theory over ER

A two-sort Lawvere theory over ℕ and labeled binary trees.
Each constructor IS a named ER expression: `toER` translates
NatBTMor1V2 terms to ERMor1 terms structurally, and `interp` is
derived via `(t.toER).interp combinedCtx` with sort-aware
decoding.  No parallel Nat-level helpers; the categorical
equivalence with `LawvereERCat` is preserved by construction.

Reuses `BTL` and `NatBTSort` from `LawvereNatBT.lean`.

The bottom-up design is documented in
`docs/superpowers/specs/2026-04-19-bottom-up-natbt-design.md`.

This is wave 1 of the inductive construction: the foundational
ER-direct constructors (zero, succ, natProj, sub, compNat, bsum,
bprod).  Wave 2 (in subsequent commit) adds BT structural and
bounded recursive constructors.
-/

namespace GebLean

/-- Interpretation transports along an arity equality: an
`ERMor1 a` cast to `ERMor1 b` via `h : a = b` interprets at a
context `Fin b → ℕ` as the original interpreted at the
re-indexed context. -/
theorem ERMor1.interp_eqRec {a b : ℕ} (h : a = b)
    (t : ERMor1 a) (ctx : Fin b → ℕ) :
    (h ▸ t).interp ctx = t.interp (fun i => ctx ⟨i.val, by
      have := i.isLt; omega⟩) := by
  subst h
  rfl

/-- Two-sort term type indexed by domain arity `(n, m) : ℕ × ℕ`
and output sort.  Wave 1 constructors only; wave 2 adds BT
structural and bounded recursive ones. -/
inductive NatBTMor1V2 : (ℕ × ℕ) → NatBTSort → Type where
  | zero {nm : ℕ × ℕ} : NatBTMor1V2 nm .nat
  | succ {nm : ℕ × ℕ} (x : NatBTMor1V2 nm .nat) :
      NatBTMor1V2 nm .nat
  | natProj {nm : ℕ × ℕ} (i : Fin nm.1) : NatBTMor1V2 nm .nat
  | sub {nm : ℕ × ℕ} (a b : NatBTMor1V2 nm .nat) :
      NatBTMor1V2 nm .nat
  | compNat {nm nm' : ℕ × ℕ}
      (f : NatBTMor1V2 nm' .nat)
      (gNat : Fin nm'.1 → NatBTMor1V2 nm .nat)
      (gBT : Fin nm'.2 → NatBTMor1V2 nm .bt) :
      NatBTMor1V2 nm .nat
  | bsum {nm : ℕ × ℕ}
      (f : NatBTMor1V2 (nm.1 + 1, nm.2) .nat) :
      NatBTMor1V2 (nm.1 + 1, nm.2) .nat
  | bprod {nm : ℕ × ℕ}
      (f : NatBTMor1V2 (nm.1 + 1, nm.2) .nat) :
      NatBTMor1V2 (nm.1 + 1, nm.2) .nat

/-- Structural translation to ER.  Each NatBTMor1V2 constructor
maps to its named ER implementation, with BT context slots
treated as encoded ℕ slots in the wider ER arity. -/
def NatBTMor1V2.toER : {nm : ℕ × ℕ} → {σ : NatBTSort} →
    NatBTMor1V2 nm σ → ERMor1 (nm.1 + nm.2)
  | _, _, NatBTMor1V2.zero => ERMor1.zeroN _
  | _, _, NatBTMor1V2.succ x =>
      ERMor1.comp ERMor1.succ
        (fun _ : Fin 1 => x.toER)
  | nm, _, NatBTMor1V2.natProj i =>
      ERMor1.proj (k := nm.1 + nm.2) ⟨i.val, by omega⟩
  | _, _, NatBTMor1V2.sub a b =>
      ERMor1.comp ERMor1.sub (fun i => match i with
        | ⟨0, _⟩ => a.toER
        | ⟨1, _⟩ => b.toER)
  | nm, _, NatBTMor1V2.compNat (nm' := nm') f gNat gBT =>
      ERMor1.comp f.toER (fun i =>
        if h : i.val < nm'.1 then
          (gNat ⟨i.val, h⟩).toER
        else
          (gBT ⟨i.val - nm'.1, by
            have hi := i.isLt
            omega⟩).toER)
  | _, _, NatBTMor1V2.bsum (nm := nm0) f =>
      let f' : ERMor1 ((nm0.1 + nm0.2) + 1) :=
        (by omega : (nm0.1 + 1) + nm0.2 = (nm0.1 + nm0.2) + 1)
          ▸ f.toER
      let g : ERMor1 ((nm0.1 + nm0.2) + 1) := ERMor1.bsum f'
      (by omega : (nm0.1 + nm0.2) + 1 = (nm0.1 + 1) + nm0.2)
        ▸ g
  | _, _, NatBTMor1V2.bprod (nm := nm0) f =>
      let f' : ERMor1 ((nm0.1 + nm0.2) + 1) :=
        (by omega : (nm0.1 + 1) + nm0.2 = (nm0.1 + nm0.2) + 1)
          ▸ f.toER
      let g : ERMor1 ((nm0.1 + nm0.2) + 1) := ERMor1.bprod f'
      (by omega : (nm0.1 + nm0.2) + 1 = (nm0.1 + 1) + nm0.2)
        ▸ g

/-- Standard interpretation derived from `toER`.  Combined
context places ℕ slots first, encoded BT slots second.  At sort
`.nat`, the ER value is the result; at sort `.bt`, decode back
to BTL. -/
def NatBTMor1V2.interp {nm : ℕ × ℕ} {σ : NatBTSort}
    (t : NatBTMor1V2 nm σ)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    σ.carrier :=
  let combinedCtx : Fin (nm.1 + nm.2) → ℕ :=
    Fin.append ctxN (fun i => (ctxB i).encode)
  let v := t.toER.interp combinedCtx
  match σ with
  | .nat => v
  | .bt => BTL.decode v

/-- Interpretation of `zero`. -/
@[simp] theorem NatBTMor1V2.interp_zero {nm : ℕ × ℕ}
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1V2.zero (nm := nm)).interp ctxN ctxB =
      (0 : ℕ) := rfl

/-- Interpretation of `succ`. -/
@[simp] theorem NatBTMor1V2.interp_succ {nm : ℕ × ℕ}
    (x : NatBTMor1V2 nm .nat)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1V2.succ x).interp ctxN ctxB =
      Nat.succ (x.interp ctxN ctxB) := rfl

/-- Interpretation of `natProj`. -/
@[simp] theorem NatBTMor1V2.interp_natProj {nm : ℕ × ℕ}
    (i : Fin nm.1)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1V2.natProj (nm := nm) i).interp ctxN ctxB =
      ctxN i := by
  unfold NatBTMor1V2.interp NatBTMor1V2.toER
  change Fin.append ctxN
      (fun j => (ctxB j).encode) ⟨i.val, _⟩ = ctxN i
  have heq : (⟨i.val, by omega⟩ : Fin (nm.1 + nm.2)) =
      Fin.castAdd nm.2 i := rfl
  rw [heq, Fin.append_left]

/-- Interpretation of `sub`. -/
@[simp] theorem NatBTMor1V2.interp_sub {nm : ℕ × ℕ}
    (a b : NatBTMor1V2 nm .nat)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1V2.sub a b).interp ctxN ctxB =
      Nat.sub (a.interp ctxN ctxB) (b.interp ctxN ctxB) := rfl

/-- Interpretation of `compNat`. -/
@[simp] theorem NatBTMor1V2.interp_compNat
    {nm nm' : ℕ × ℕ}
    (f : NatBTMor1V2 nm' .nat)
    (gNat : Fin nm'.1 → NatBTMor1V2 nm .nat)
    (gBT : Fin nm'.2 → NatBTMor1V2 nm .bt)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1V2.compNat f gNat gBT).interp ctxN ctxB =
      f.interp
        (fun i => (gNat i).interp ctxN ctxB)
        (fun i => (gBT i).interp ctxN ctxB) := by
  change f.toER.interp _ = f.toER.interp _
  congr 1
  funext i
  simp only []
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [Fin.append_left]
    have h : (Fin.castAdd nm'.2 j).val < nm'.1 := j.isLt
    rw [dif_pos h]
    rfl
  · rw [Fin.append_right]
    have h : ¬ (Fin.natAdd nm'.1 j).val < nm'.1 := by
      change ¬ nm'.1 + j.val < nm'.1
      omega
    rw [dif_neg h]
    have hidx : (⟨(Fin.natAdd nm'.1 j).val - nm'.1, by
      change nm'.1 + j.val - nm'.1 < nm'.2
      omega⟩ : Fin nm'.2) = j := by
      apply Fin.ext
      change nm'.1 + j.val - nm'.1 = j.val
      omega
    rw [hidx]
    change (gBT j).toER.interp _ =
      BTL.encode (BTL.decode ((gBT j).toER.interp _))
    rw [BTL.encode_decode]

/-- Helper: pointwise computation of the
`Fin.append`-on-cons-extended-context against the
`Fin.cons` of the re-indexed combined context.  For each index
`k`, both sides return either `i` (at position 0), a value
from `ctxN` (at remaining ℕ positions), or an encoded BT slot. -/
theorem NatBTMor1V2.bsumCtx_eq {nm : ℕ × ℕ}
    (ctxN : Fin (nm.1 + 1) → ℕ)
    (ctxB : Fin nm.2 → BTL) (i : ℕ)
    (k : Fin ((nm.1 + 1) + nm.2)) :
    Fin.cons i (Fin.tail (fun (j : Fin ((nm.1 + nm.2) + 1)) =>
        Fin.append ctxN (fun j => (ctxB j).encode)
          ⟨j.val, by have := j.isLt; omega⟩))
        ⟨k.val, by have := k.isLt; omega⟩ =
      Fin.append (Fin.cons i (Fin.tail ctxN))
        (fun j => (ctxB j).encode) k := by
  by_cases hk : k.val = 0
  · have hk1 : (⟨k.val, by have := k.isLt; omega⟩ :
        Fin ((nm.1 + nm.2) + 1)) = 0 := by
      apply Fin.ext; exact hk
    rw [hk1, Fin.cons_zero]
    have hk2 : k = Fin.castAdd nm.2 0 := by
      apply Fin.ext; exact hk
    rw [hk2, Fin.append_left]
    rw [Fin.cons_zero]
  · have hkpos : 0 < k.val := Nat.pos_of_ne_zero hk
    by_cases hkN : k.val < nm.1 + 1
    · have hk2 : k = Fin.castAdd nm.2 ⟨k.val, hkN⟩ := by
        apply Fin.ext; rfl
      conv_rhs => rw [hk2, Fin.append_left]
      have hk1 : (⟨k.val, by have := k.isLt; omega⟩ :
          Fin ((nm.1 + nm.2) + 1)) = Fin.succ
          ⟨k.val - 1, by omega⟩ := by
        apply Fin.ext
        change k.val = (k.val - 1) + 1
        omega
      rw [hk1, Fin.cons_succ]
      have hk3 : (⟨k.val, hkN⟩ : Fin (nm.1 + 1)) = Fin.succ
          ⟨k.val - 1, by omega⟩ := by
        apply Fin.ext
        change k.val = (k.val - 1) + 1
        omega
      rw [hk3, Fin.cons_succ, Fin.tail]
      have hk4 : (⟨(Fin.succ (⟨k.val - 1, by omega⟩
            : Fin (nm.1 + nm.2))).val, by
            have := k.isLt; omega⟩ :
            Fin ((nm.1 + 1) + nm.2)) =
          Fin.castAdd nm.2 (Fin.succ
            ⟨k.val - 1, by omega⟩) := by
        apply Fin.ext; rfl
      rw [hk4, Fin.append_left]
      rfl
    · have hkBT : nm.1 + 1 ≤ k.val := Nat.le_of_not_lt hkN
      have hk2 : k = Fin.natAdd (nm.1 + 1)
          ⟨k.val - (nm.1 + 1), by
            have := k.isLt; omega⟩ := by
        apply Fin.ext
        change k.val = (nm.1 + 1) + (k.val - (nm.1 + 1))
        omega
      conv_rhs => rw [hk2, Fin.append_right]
      have hk1 : (⟨k.val, by have := k.isLt; omega⟩ :
          Fin ((nm.1 + nm.2) + 1)) = Fin.succ
          ⟨k.val - 1, by have := k.isLt; omega⟩ := by
        apply Fin.ext
        change k.val = (k.val - 1) + 1
        omega
      rw [hk1, Fin.cons_succ, Fin.tail]
      have hk3 : (⟨(Fin.succ (⟨k.val - 1, by
              have := k.isLt; omega⟩ :
              Fin (nm.1 + nm.2))).val, by
            have := k.isLt; omega⟩ :
            Fin ((nm.1 + 1) + nm.2)) =
          Fin.natAdd (nm.1 + 1)
            ⟨k.val - (nm.1 + 1), by
              have := k.isLt; omega⟩ := by
        apply Fin.ext
        change (k.val - 1) + 1 = (nm.1 + 1) + (k.val
          - (nm.1 + 1))
        omega
      rw [hk3, Fin.append_right]

/-- Interpretation of `bsum`. -/
@[simp] theorem NatBTMor1V2.interp_bsum {nm : ℕ × ℕ}
    (f : NatBTMor1V2 (nm.1 + 1, nm.2) .nat)
    (ctxN : Fin (nm.1 + 1) → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1V2.bsum f).interp ctxN ctxB =
      natBSum (ctxN 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail ctxN)) ctxB) := by
  change ((NatBTMor1V2.bsum f).toER.interp _) =
      natBSum (ctxN 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail ctxN)) ctxB)
  unfold NatBTMor1V2.toER
  simp only []
  rw [ERMor1.interp_eqRec]
  rw [ERMor1.interp_bsum]
  have hbound : (Fin.append ctxN
        (fun j => (ctxB j).encode) :
        Fin ((nm.1 + 1) + nm.2) → ℕ)
        ⟨(0 : Fin ((nm.1 + nm.2) + 1)).val, by omega⟩ =
      ctxN 0 := by
    change Fin.append ctxN _ (Fin.castAdd nm.2 0) = ctxN 0
    rw [Fin.append_left]
  rw [hbound]
  congr 1
  funext i
  rw [ERMor1.interp_eqRec]
  change f.toER.interp _ = f.interp _ _
  unfold NatBTMor1V2.interp
  congr 1
  funext k
  exact NatBTMor1V2.bsumCtx_eq ctxN ctxB i k

/-- Interpretation of `bprod`. -/
@[simp] theorem NatBTMor1V2.interp_bprod {nm : ℕ × ℕ}
    (f : NatBTMor1V2 (nm.1 + 1, nm.2) .nat)
    (ctxN : Fin (nm.1 + 1) → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1V2.bprod f).interp ctxN ctxB =
      natBProd (ctxN 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail ctxN)) ctxB) := by
  change ((NatBTMor1V2.bprod f).toER.interp _) =
      natBProd (ctxN 0) (fun i =>
        f.interp (Fin.cons i (Fin.tail ctxN)) ctxB)
  unfold NatBTMor1V2.toER
  simp only []
  rw [ERMor1.interp_eqRec]
  rw [ERMor1.interp_bprod]
  have hbound : (Fin.append ctxN
        (fun j => (ctxB j).encode) :
        Fin ((nm.1 + 1) + nm.2) → ℕ)
        ⟨(0 : Fin ((nm.1 + nm.2) + 1)).val, by omega⟩ =
      ctxN 0 := by
    change Fin.append ctxN _ (Fin.castAdd nm.2 0) = ctxN 0
    rw [Fin.append_left]
  rw [hbound]
  congr 1
  funext i
  rw [ERMor1.interp_eqRec]
  change f.toER.interp _ = f.interp _ _
  unfold NatBTMor1V2.interp
  congr 1
  funext k
  exact NatBTMor1V2.bsumCtx_eq ctxN ctxB i k

end GebLean
