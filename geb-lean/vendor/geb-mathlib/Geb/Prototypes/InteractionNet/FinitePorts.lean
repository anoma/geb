/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.PortNet
public import Mathlib.Data.FinEnum
public import Mathlib.Logic.Equiv.Fin.Basic

set_option doc.verso true in
/-!
# Finite ordinal indices for ports

The ports of finitely many indexed cells can be enumerated by concatenating each cell's
ordered port block. The resulting equivalence supplies concrete array positions for all
cell ports and external boundary positions, with no choice of representatives.

## Main definitions

* {lit}`finiteSigmaEnum` — enumerate a finite family of finite ordinal blocks.
* {lit}`cellPortEnum` — enumerate every ordered port of a finite indexed cell family.

## Tags

interaction net, port, finite enumeration, array index
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

open scoped FinEnum

/-- Enumerate the two wire ends while retaining Boolean structural equality. -/
@[instance_reducible] def boolEnum : FinEnum Bool where
  card := 2
  equiv :=
    { toFun := fun b ↦ if b then 1 else 0
      invFun := fun i ↦ i.val == 1
      left_inv := by intro b; cases b <;> rfl
      right_inv := fun i ↦ Fin.cases rfl
        (fun i ↦ Fin.cases rfl (fun j ↦ Fin.elim0 j) i) i }
  decEq := inferInstance

/-- Separate the first block of a nonempty finite family from its remaining blocks. -/
def finiteSigmaSucc {n : ℕ} (sizes : Fin (n + 1) → ℕ) :
    (Σ i, Fin (sizes i)) ≃ Fin (sizes 0) ⊕ (Σ i : Fin n, Fin (sizes i.succ)) where
  toFun p := Fin.cases (motive := fun i ↦ Fin (sizes i) → _)
    Sum.inl (fun i p ↦ .inr ⟨i, p⟩) p.1 p.2
  invFun p := match p with
    | .inl p => ⟨0, p⟩
    | .inr ⟨i, p⟩ => ⟨i.succ, p⟩
  left_inv p := by
    rcases p with ⟨i, p⟩
    revert p
    exact Fin.cases (fun _ ↦ rfl) (fun _ _ ↦ rfl) i
  right_inv p := by cases p <;> rfl

/-- Concatenate finite ordinal blocks to obtain an explicit finite enumeration. -/
@[instance_reducible] def finiteSigmaEnum (n : ℕ) (sizes : Fin n → ℕ) :
    FinEnum (Σ i, Fin (sizes i)) :=
  Nat.rec (motive := fun n ↦ (sizes : Fin n → ℕ) → FinEnum (Σ i, Fin (sizes i)))
    (fun _ ↦
      { card := 0
        equiv :=
          { toFun := fun p ↦ Fin.elim0 p.1
            invFun := Fin.elim0
            left_inv := fun p ↦ Fin.elim0 p.1
            right_inv := fun i ↦ Fin.elim0 i }
        decEq := inferInstance })
    (fun _ ih sizes ↦
      let tail := ih (fun i ↦ sizes i.succ)
      { card := sizes 0 + tail.card
        equiv := (finiteSigmaSucc sizes).trans
          ((Equiv.sumCongr (Equiv.refl _) tail.equiv).trans finSumFinEquiv)
        decEq := inferInstance }) n sizes

/-- Enumerate a dependent family by the supplied enumerations of its index and fibers. -/
@[instance_reducible] def sigmaEnum {I : Type*} {C : I → Type*} [FinEnum I]
    [∀ i, FinEnum (C i)] : FinEnum (Σ i, C i) :=
  let e := (Equiv.sigmaCongrLeft (β := C) (FinEnum.equiv : I ≃ _).symm).symm.trans
    (sigmaCongrRight' fun i ↦ (FinEnum.equiv : C (FinEnum.equiv.symm i) ≃ _))
  let := finiteSigmaEnum (FinEnum.card I) (fun i ↦ FinEnum.card (C (FinEnum.equiv.symm i)))
  FinEnum.ofEquiv _ e

/-- An explicit enumeration of all ordered ports of finitely many indexed cells. -/
@[instance_reducible] scoped instance cellPortEnum {α : Type*} {n : ℕ}
    (arity : α → ℕ) (label : Fin n → α) : FinEnum (CellPort arity label) :=
  finiteSigmaEnum n (fun c ↦ arity (label c) + 1)

end Geb.InteractionNet

end
