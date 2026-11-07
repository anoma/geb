/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.PortNet
public import Geb.Prototypes.InteractionNet.InverseTable
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
* {lit}`finiteSigmaEnumFast` — the same enumeration, its positions and elements read from tables.
* {lit}`cellPortEnum` — enumerate every ordered port of a finite indexed cell family.

## Main statements

* {lit}`finiteSigmaEnum_equiv_val` — an element's position is the sum of the sizes of the blocks
  before its own and its position within its block.
* {lit}`finiteSigmaEnum_eq_finiteSigmaEnumFast` — the two enumerations are equal, and compiled
  code computes the first as the second.

## Implementation notes

{lit}`finiteSigmaEnum` is a recursion on the number of blocks, so that a position is a sum of
the blocks' sizes computed block by block, and the size of the block {lit}`i` is reached through
{lit}`i` reindexings of the family; a lookup costs about the square of its block's index.
{lit}`finiteSigmaEnumFast` tabulates the blocks' starts by prefix sums and the elements by an
inverse table ({lit}`Geb.InteractionNet.inverseTable`), each once for the enumeration, so that a
position and an element each cost a constant number of array reads. The attribute {lit}`csimp`
replaces the one by the other in compiled code, and every proof reasons about the first. The
tables are bound as values outside the enumeration's functions: the compiler moves a binding of
a function into the function that applies it, where it would be computed at each lookup.

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

/-- The concatenated blocks' cardinality unfolds to the first block's size and the rest's. -/
theorem finiteSigmaEnum_card_succ (n : ℕ) (sizes : Fin (n + 1) → ℕ) :
    (finiteSigmaEnum (n + 1) sizes).card =
      sizes 0 + (finiteSigmaEnum n (fun i ↦ sizes i.succ)).card := rfl

/-- The concatenation of the blocks has the sum of their sizes as its cardinality. -/
theorem finiteSigmaEnum_card (n : ℕ) (sizes : Fin n → ℕ) :
    (finiteSigmaEnum n sizes).card = (List.ofFn sizes).sum :=
  Nat.rec (motive := fun n ↦ ∀ sizes : Fin n → ℕ,
      (finiteSigmaEnum n sizes).card = (List.ofFn sizes).sum)
    (fun _ ↦ by rw [List.ofFn_zero]; rfl)
    (fun n ih sizes ↦ by
      rw [finiteSigmaEnum_card_succ, ih, List.ofFn_succ, List.sum_cons]) n sizes

/-- An element's position is the sum of the sizes of the blocks before its own, and its own
position within its block. -/
theorem finiteSigmaEnum_equiv_val (n : ℕ) (sizes : Fin n → ℕ) (p : Σ i, Fin (sizes i)) :
    ((finiteSigmaEnum n sizes).equiv p).val = ((List.ofFn sizes).take p.1).sum + p.2 :=
  Nat.rec (motive := fun n ↦ ∀ (sizes : Fin n → ℕ) (p : Σ i, Fin (sizes i)),
      ((finiteSigmaEnum n sizes).equiv p).val = ((List.ofFn sizes).take p.1).sum + p.2)
    (fun _ p ↦ Fin.elim0 p.1)
    (fun n ih sizes p ↦ by
      rcases p with ⟨c, q⟩
      revert q
      refine Fin.cases (motive := fun c ↦ ∀ q : Fin (sizes c),
        ((finiteSigmaEnum (n + 1) sizes).equiv ⟨c, q⟩).val =
          ((List.ofFn sizes).take c).sum + q) ?_ (fun c q ↦ ?_) c
      · intro q
        change (q : ℕ) = _
        rw [Fin.val_zero, List.take_zero, List.sum_nil, Nat.zero_add]
      · change sizes 0 + ((finiteSigmaEnum n (fun i ↦ sizes i.succ)).equiv ⟨c, q⟩).val = _
        rw [ih, List.ofFn_succ, Fin.val_succ, List.take_succ_cons, List.sum_cons,
          Nat.add_assoc]) n sizes p

/-- The start of each block, the sum of the sizes of the blocks before it, and after them the
sum of every size, tabulated by prefix sums. -/
def blockStarts {n : ℕ} (sizes : Fin n → ℕ) : Vector ℕ (n + 1) :=
  ⟨((List.ofFn sizes).scanl (· + ·) 0).toArray, by
    simp only [List.size_toArray, List.length_scanl, List.length_ofFn]⟩

/-- The tabulated start of a block is the sum of the sizes of the blocks before it. -/
theorem blockStarts_get {n : ℕ} (sizes : Fin n → ℕ) (i : ℕ) (h : i < n + 1) :
    (blockStarts sizes)[i] = ((List.ofFn sizes).take i).sum := by
  change ((List.ofFn sizes).scanl (· + ·) 0).toArray[i]'(by
    simpa only [List.size_toArray, List.length_scanl, List.length_ofFn] using h) = _
  rw [List.getElem_toArray, List.getElem_scanl, List.sum_eq_foldl_nat]

/-- The tabulated total is the concatenation's cardinality. -/
theorem blockStarts_last {n : ℕ} (sizes : Fin n → ℕ) :
    (blockStarts sizes)[n] = (finiteSigmaEnum n sizes).card := by
  rw [blockStarts_get, finiteSigmaEnum_card, List.take_of_length_le (by
    rw [List.length_ofFn])]

/-- An element's position is its block's tabulated start and its position within the block. -/
theorem blockStarts_add {n : ℕ} (sizes : Fin n → ℕ) (p : Σ i, Fin (sizes i)) :
    (blockStarts sizes)[p.1.val] + p.2 = ((finiteSigmaEnum n sizes).equiv p).val := by
  rw [blockStarts_get, finiteSigmaEnum_equiv_val]

/-- An element's position, from a table of the starts, is below their total. -/
theorem blockStarts_pos_lt {n : ℕ} (sizes : Fin n → ℕ) (starts : Vector ℕ (n + 1))
    (h : starts = blockStarts sizes) (p : Σ i, Fin (sizes i)) :
    starts[p.1.val] + p.2 < starts[n] := by
  subst h
  rw [blockStarts_add, blockStarts_last]
  exact ((finiteSigmaEnum n sizes).equiv p).isLt

/-- The position of an element of the concatenated blocks, from the tabulated starts. -/
def blockPos {n : ℕ} (sizes : Fin n → ℕ) :
    (Σ i, Fin (sizes i)) ↪ Fin (blockStarts sizes)[n] where
  toFun p := ⟨(blockStarts sizes)[p.1.val] + p.2, blockStarts_pos_lt sizes _ rfl p⟩
  inj' p q h := (finiteSigmaEnum n sizes).equiv.injective (Fin.ext (by
    have h := congrArg Fin.val h
    simp only at h
    rwa [blockStarts_add, blockStarts_add] at h))

/-- Every position is that of an element. -/
theorem exists_blockPos {n : ℕ} (sizes : Fin n → ℕ) (j : Fin (blockStarts sizes)[n]) :
    ∃ p, blockPos sizes p = j :=
  ⟨(finiteSigmaEnum n sizes).equiv.symm ⟨j, by rw [← blockStarts_last]; exact j.isLt⟩,
    Fin.ext (by
      change (blockStarts sizes)[_] + _ = _
      rw [blockStarts_add, Equiv.apply_symm_apply])⟩

/-- The elements of the blocks, block by block. -/
def sigmaBlocks (n : ℕ) (sizes : Fin n → ℕ) : List (Σ i, Fin (sizes i)) :=
  (List.finRange n).flatMap fun i ↦ (List.finRange (sizes i)).map (Sigma.mk i)

/-- Every element of the blocks is listed. -/
theorem mem_sigmaBlocks {n : ℕ} (sizes : Fin n → ℕ) (p : Σ i, Fin (sizes i)) :
    p ∈ sigmaBlocks n sizes :=
  List.mem_flatMap.mpr ⟨p.1, List.mem_finRange _,
    List.mem_map.mpr ⟨p.2, List.mem_finRange _, rfl⟩⟩

/-- The element at each position of the concatenated blocks, from a table built once. -/
def blockTable {n : ℕ} (sizes : Fin n → ℕ) :
    Vector (Option (Σ i, Fin (sizes i))) (blockStarts sizes)[n] :=
  let starts := blockStarts sizes
  inverseTable ⟨fun p ↦ ⟨starts[p.1.val] + p.2, blockStarts_pos_lt sizes starts rfl p⟩,
    (blockPos sizes).injective⟩ (sigmaBlocks n sizes)

/-- The table holds each element at its position. -/
theorem blockTable_pos {n : ℕ} (sizes : Fin n → ℕ) (p : Σ i, Fin (sizes i)) :
    (blockTable sizes)[blockPos sizes p] = some p :=
  inverseTable_get _ (mem_sigmaBlocks sizes p)

/-- Every entry of the table is an element. -/
theorem blockTable_isSome {n : ℕ} (sizes : Fin n → ℕ) (j : Fin (blockStarts sizes)[n]) :
    ((blockTable sizes)[j]).isSome := by
  obtain ⟨p, rfl⟩ := exists_blockPos sizes j
  rw [blockTable_pos]
  rfl

/-- The element at a position of the concatenated blocks, read from a table. -/
def blockAt {n : ℕ} (sizes : Fin n → ℕ)
    (table : Vector (Option (Σ i, Fin (sizes i))) (blockStarts sizes)[n])
    (h : table = blockTable sizes) (j : Fin (blockStarts sizes)[n]) : Σ i, Fin (sizes i) :=
  (table[j]).get (h ▸ blockTable_isSome sizes j)

/-- Reading the table at an element's position returns the element. -/
theorem blockAt_pos {n : ℕ} (sizes : Fin n → ℕ)
    (table : Vector (Option (Σ i, Fin (sizes i))) (blockStarts sizes)[n])
    (h : table = blockTable sizes) (p : Σ i, Fin (sizes i)) :
    blockAt sizes table h (blockPos sizes p) = p := by
  subst h
  exact Option.get_of_eq_some _ (blockTable_pos sizes p)

/-- The position of the element read at a position is that position. -/
theorem blockPos_blockAt {n : ℕ} (sizes : Fin n → ℕ)
    (table : Vector (Option (Σ i, Fin (sizes i))) (blockStarts sizes)[n])
    (h : table = blockTable sizes) (j : Fin (blockStarts sizes)[n]) :
    blockPos sizes (blockAt sizes table h j) = j := by
  obtain ⟨p, rfl⟩ := exists_blockPos sizes j
  rw [blockAt_pos]

/-- The concatenation of finite ordinal blocks with its positions computed from the blocks'
starts and its elements read from a table, each tabulated once, so that a position and an
element each cost a constant number of array reads. -/
@[instance_reducible] def finiteSigmaEnumFast (n : ℕ) (sizes : Fin n → ℕ) :
    FinEnum (Σ i, Fin (sizes i)) :=
  let starts := blockStarts sizes
  let table := blockTable sizes
  { card := starts[n]
    equiv :=
      { toFun := fun p ↦ ⟨starts[p.1.val] + p.2, blockStarts_pos_lt sizes starts rfl p⟩
        invFun := fun j ↦ blockAt sizes table rfl j
        left_inv := blockAt_pos sizes table rfl
        right_inv := blockPos_blockAt sizes table rfl }
    decEq := inferInstance }

/-- Two enumerations of a type are equal where their cardinalities and their positions are. -/
theorem finEnum_ext {γ : Type*} {a b : FinEnum γ} (hc : a.card = b.card)
    (he : ∀ x, (a.equiv x).val = (b.equiv x).val) : a = b := by
  cases a with | @mk ca ea da =>
  cases b with | @mk cb eb db =>
  change ca = cb at hc
  subst hc
  obtain rfl : ea = eb := Equiv.ext fun x ↦ Fin.ext (he x)
  obtain rfl : da = db := Subsingleton.elim _ _
  rfl

/-- The tabulated enumeration is the recursive one, which compiled code replaces by it. -/
@[csimp] theorem finiteSigmaEnum_eq_finiteSigmaEnumFast :
    @finiteSigmaEnum = @finiteSigmaEnumFast := by
  funext n sizes
  refine finEnum_ext (a := finiteSigmaEnum n sizes) (b := finiteSigmaEnumFast n sizes) ?_ ?_
  · exact (blockStarts_last sizes).symm
  · exact fun p ↦ (blockStarts_add sizes p).symm

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
