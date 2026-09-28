/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.NumScanExpr

set_option doc.verso true in
/-!
# A lockstep fold over the bits of two numerals

A simultaneous recursion over the word that visits the bits of three coded
numbers at three positions in lockstep. Each number contributes two
registers: a pointer at the bit it has reached, and a mask, an end segment as
long as the run of bits to be read, so that reading a bit is a dispatch on a
register's head and the test of the run's end a dispatch on a register's
emptiness, rather than a scan of the numeral from its position. Both
registers advance by a tail at every level, and their bases are a parameter
of the fold, {lit}`segBit` reading the bits at their offsets.

Two choices of bases serve. {lit}`codeScan` reads a numeral's code from its
position: the pointer is the position itself and the mask needs the scanner's
end position alone, so equality of numbers, which by
{name}`Geb.SizeBounded.Logspace.WTree.Numeral.natCode_injective` is equality
of codes, costs one run of the scanner per position. {lit}`payScan` reads a
numeral's payload, the bits of the number least significant first, which the
order, the sum and the reading into a counter need aligned by index: the
gamma code's zero run fixes where the payload begins and the size field's
value how long it is, so it costs two runs per position.

# Main definitions

* {lit}`runAt`, {lit}`sizeAt`, {lit}`endAt`, {lit}`payStart`,
  {lit}`payMaskStart`, {lit}`codeMaskStart` — the scanner's fields at a
  position and the offsets the two choices of bases read from.
* {lit}`segBit`, {lit}`payBit`, {lit}`codeBit` — the bit at an offset within
  a run of a given length, and the two instances.
* {lit}`zSeg`, {lit}`sSeg`, {lit}`endSeg`, {lit}`payPtr`, {lit}`payMask`,
  {lit}`codeMask`, {lit}`payScan`, {lit}`codeScan` — those offsets as
  expressions, and the two choices of bases.
* {lit}`scanSlot`, {lit}`regSlot`, {lit}`parSlot`, {lit}`maskedBit`,
  {lit}`updEnv` — the slots of the step environment, the bit of one numeral,
  and the environment an update reads.
* {lit}`foldBase`, {lit}`foldStep`, {lit}`foldReg`, {lit}`bitFold` — the
  recursion, and a register after the fold over the word as an expression
  of arity four.
* {lit}`updF`, {lit}`iter` — the update's meaning on registers and bits,
  and its iteration over the indices below a bound.

# Main statements

* {lit}`payBit_natCode`, {lit}`codeBit_natCode` — on a word holding a coded
  number at a position, the payload's bit at an index is the number's bit
  there and the code's bit is the code's.
* {lit}`sem_payScan`, {lit}`sem_codeScan` — the two choices of bases read
  from those offsets.
* {lit}`regs_eq` — after a prefix of the word, the pointers and masks hold the
  word dropped that much further and the registers the iteration over the
  prefix's length.
* {lit}`sem_bitFold`, {lit}`sem_bitFold_pay`, {lit}`sem_bitFold_code` — a
  register's value is the iteration over the word's length.

# References

* \[Kristiansen2005\]

# Tags

logspace, simultaneous recursion on notation, binary numeral, lockstep
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree.BitFold

open Numeral

public section

/-- The width of the zero run of the gamma code of the numeral at a position:
the scanner's zero run after the word. -/
@[expose] def runAt (y : List Bool) (p : ℕ) : ℕ := (nrun p 0 y).z

/-- The size field's value of the numeral at a position: one more than the
payload's length. -/
@[expose] def sizeAt (y : List Bool) (p : ℕ) : ℕ := (nrun p 0 y).s

/-- The position after the numeral at a position. -/
@[expose] def endAt (y : List Bool) (p : ℕ) : ℕ := (nrun p 0 y).endPos

/-- The first position of the payload of the numeral at a position: past the
gamma code, which is twice the zero run and one bit long. -/
@[expose] def payStart (y : List Bool) (p : ℕ) : ℕ := p + runAt y p + runAt y p + 1

/-- The position from which an end segment of the word is as long as the
payload of the numeral at a position. -/
@[expose] def payMaskStart (y : List Bool) (p : ℕ) : ℕ := y.length - sizeAt y p + 1

/-- The position from which an end segment of the word is as long as the code
of the numeral at a position. -/
@[expose] def codeMaskStart (y : List Bool) (p : ℕ) : ℕ := p + (y.length - endAt y p)

/-- The bit at an offset into a run of bits that begins at one position and is
as long as the end segment from another: the word's bit there, and clear past
the run. -/
@[expose] def segBit (y : List Bool) (ps ms i : ℕ) : Bool :=
  if y.length ≤ ms + i then false else (y.drop (ps + i)).headD false

/-- The bit of the payload of the numeral at a position at an index. -/
@[expose] def payBit (y : List Bool) (p i : ℕ) : Bool :=
  segBit y (payStart y p) (payMaskStart y p) i

/-- The bit of the code of the numeral at a position at an index. -/
@[expose] def codeBit (y : List Bool) (p i : ℕ) : Bool := segBit y p (codeMaskStart y p) i

/-- The head of an end segment is the entry at its offset. -/
theorem headD_drop (l : List Bool) (i : ℕ) : (l.drop i).headD false = l.getD i false := by
  rw [List.headD_eq_head?_getD, List.head?_eq_getElem?, List.getElem?_drop, Nat.add_zero,
    List.getD_eq_getElem?_getD]

/-- An entry past a list's end is the default. -/
theorem getD_of_length_le (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]
  rfl

/-- A coded number's length is within the word's. -/
theorem length_natCode_le (y u r : List Bool) (m : ℕ) (hy : y = u ++ natCode m ++ r) :
    (natCode m).length ≤ y.length := by
  rw [hy, List.length_append, List.length_append]
  omega

/-- On a word holding a coded number at a position, the end segment from the
position begins with the code. -/
theorem drop_natCode (y u r : List Bool) (m p : ℕ) (hu : u.length = p)
    (hy : y = u ++ natCode m ++ r) : y.drop p = natCode m ++ r := by
  rw [hy, List.append_assoc, ← hu, List.drop_left]

/-- On a word holding a coded number at a position, the payload begins past
the number's gamma code. -/
theorem drop_payStart_natCode (y u r : List Bool) (m p : ℕ) (hu : u.length = p)
    (hy : y = u ++ natCode m ++ r) : y.drop (payStart y p) = m.bits ++ r := by
  have hs := nrun_eq_natCode p 0 u r y m hu hy
  have hz : runAt y p = (m.size + 1).size - 1 := by rw [runAt, hs]
  rw [payStart, hz, hy, natCode, List.append_assoc, List.append_assoc,
    show p + ((m.size + 1).size - 1) + ((m.size + 1).size - 1) + 1 =
      u.length + (Geb.BitTree.Elias.encodeGamma (m.size + 1)).length by
      rw [hu, Geb.BitTree.Elias.length_encodeGamma]; omega,
    ← List.length_append, ← List.append_assoc, List.drop_left]

/-- On a word holding a coded number at a position, the bit of the payload at
an index is the number's bit there. -/
theorem payBit_natCode (y u r : List Bool) (m p : ℕ) (hu : u.length = p)
    (hy : y = u ++ natCode m ++ r) (i : ℕ) : payBit y p i = m.bits.getD i false := by
  have hs := nrun_eq_natCode p 0 u r y m hu hy
  have hsz : sizeAt y p = m.size + 1 := by rw [sizeAt, hs]
  have hml : m.size + 1 ≤ y.length := by
    have := length_natCode m
    have := length_natCode_le y u r m hy
    omega
  have hbl : m.bits.length = m.size := length_bits m
  rw [payBit, segBit, payMaskStart, hsz]
  by_cases hi : m.size ≤ i
  · rw [if_pos (by omega), getD_of_length_le _ _ (by omega)]
  · rw [if_neg (by omega), ← List.drop_drop, drop_payStart_natCode y u r m p hu hy,
      headD_drop, List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]

/-- On a word holding a coded number at a position, the bit of the code at an
index is the code's bit there. -/
theorem codeBit_natCode (y u r : List Bool) (m p : ℕ) (hu : u.length = p)
    (hy : y = u ++ natCode m ++ r) (i : ℕ) : codeBit y p i = (natCode m).getD i false := by
  have hs := nrun_eq_natCode p 0 u r y m hu hy
  have he : endAt y p = p + (natCode m).length := by rw [endAt, hs]
  have hp : p + (natCode m).length ≤ y.length := by
    rw [hy, List.length_append, List.length_append, hu]
    omega
  rw [codeBit, segBit, codeMaskStart, he]
  by_cases hi : (natCode m).length ≤ i
  · rw [if_pos (by omega), getD_of_length_le _ _ hi]
  · rw [if_neg (by omega), ← List.drop_drop, drop_natCode y u r m p hu hy, headD_drop,
      List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (by omega)]

/-- The zero run of the numeral at a position, as an end segment of the
word. -/
@[expose] def zSeg {n : ℕ} (W q : LOf n) : LOf n := compL (NumExpr.numReg 2) ![W, q, W]

/-- The size field's value of the numeral at a position, as an end segment of
the word. -/
@[expose] def sSeg {n : ℕ} (W q : LOf n) : LOf n := compL (NumExpr.numReg 4) ![W, q, W]

/-- The position after the numeral at a position, as an end segment of the
word. -/
@[expose] def endSeg {n : ℕ} (W q : LOf n) : LOf n := compL (NumExpr.numReg 7) ![W, q, W]

/-- The first position of the payload, as an end segment of the word. -/
@[expose] def payPtr {n : ℕ} (W q : LOf n) : LOf n :=
  tailAppL (addSeg (zSeg W q) (addSeg (zSeg W q) q W) W)

/-- An end segment of the word as long as the payload. -/
@[expose] def payMask {n : ℕ} (W q : LOf n) : LOf n := tailAppL (dropByApp (sSeg W q) W)

/-- An end segment of the word as long as the numeral's code. -/
@[expose] def codeMask {n : ℕ} (W q : LOf n) : LOf n := dropByApp (endSeg W q) q

variable {n : ℕ} (W q : LOf n) (x : Fin n → List Bool) (y : List Bool) (p : ℕ)
  (hW : W.sem x = y) (hq : q.sem x = y.drop p) (hp : p ≤ y.length)

include hW hq hp

/-- A scanner register at a position, read with the index at zero. -/
theorem sem_numRegAt (l : Fin 8) :
    (compL (NumExpr.numReg l) ![W, q, W]).sem x = NumExpr.encodeNS y [] (nrun p 0 y) l := by
  rw [sem_compL,
    show (fun i ↦ (![W, q, W] i).sem x) = ![y, y.drop p, y.drop 0] from
      funext fun i ↦ match i with
        | 0 => hW
        | 1 => hq
        | 2 => by rw [List.drop_zero]; exact hW]
  exact NumExpr.sem_numReg l y p 0 hp (Nat.zero_le _)

/-- The zero run's meaning. -/
theorem sem_zSeg : (zSeg W q).sem x = y.drop (runAt y p) := sem_numRegAt W q x y p hW hq hp 2

/-- The size field's value's meaning. -/
theorem sem_sSeg : (sSeg W q).sem x = y.drop (sizeAt y p) := sem_numRegAt W q x y p hW hq hp 4

/-- The end position's meaning. -/
theorem sem_endSeg : (endSeg W q).sem x = y.drop (endAt y p) := sem_numRegAt W q x y p hW hq hp 7

/-- The payload pointer's meaning. -/
theorem sem_payPtr : (payPtr W q).sem x = y.drop (payStart y p) := by
  rw [payPtr, sem_tailAppL,
    sem_addSeg _ _ _ x y (runAt y p) (p + runAt y p) (sem_zSeg W q x y p hW hq hp)
      (sem_addSeg _ _ _ x y (runAt y p) p (sem_zSeg W q x y p hW hq hp) hq hW) hW,
    List.tail_drop, payStart]

/-- The payload mask's meaning. -/
theorem sem_payMask : (payMask W q).sem x = y.drop (payMaskStart y p) := by
  rw [payMask, sem_tailAppL, sem_dropByApp, sem_sSeg W q x y p hW hq hp, hW, List.length_drop,
    List.tail_drop, payMaskStart]

/-- The code mask's meaning. -/
theorem sem_codeMask : (codeMask W q).sem x = y.drop (codeMaskStart y p) := by
  rw [codeMask, sem_dropByApp, sem_endSeg W q x y p hW hq hp, hq, List.length_drop,
    List.drop_drop, codeMaskStart]

omit hW hq hp

variable {k : ℕ}

/-- A scanner register's slot: the three pointers and then the three masks. -/
@[expose] def scanSlot (j : Fin 6) : Fin (6 + k + 4 + 1) :=
  Fin.succ (Fin.castAdd 4 (Fin.castAdd k j))

/-- A register's slot, after the scanner's. -/
@[expose] def regSlot (j : Fin k) : Fin (6 + k + 4 + 1) :=
  Fin.succ (Fin.castAdd 4 (Fin.natAdd 6 j))

/-- A parameter's slot: the word and the three positions. -/
@[expose] def parSlot (j : Fin 4) : Fin (6 + k + 4 + 1) := Fin.succ (Fin.natAdd (6 + k) j)

/-- A scanner register. -/
@[expose] def scanV (j : Fin 6) : LOf (6 + k + 4 + 1) := projL _ (scanSlot j)

/-- The word. -/
@[expose] def wordV : LOf (6 + k + 4 + 1) := projL _ (parSlot 0)

/-- The bit of a numeral at the index the fold has reached: the bit its
pointer begins with, and clear once its mask is exhausted. The pointer is
read first, so a clear bit costs no evaluation of the mask. -/
@[expose] def maskedBit (mask ptr : LOf (6 + k + 4 + 1)) : LOf (6 + k + 4 + 1) :=
  cond4L ptr (constL _ []) (andOkAt mask (constL _ [true])) (constL _ [])

/-- The environment an update reads: the registers, the three bits and the
word. -/
@[expose] def updEnv : Fin (k + 4) → LOf (6 + k + 4 + 1) :=
  Fin.append (fun j ↦ projL _ (regSlot j))
    ![maskedBit (scanV 3) (scanV 0), maskedBit (scanV 4) (scanV 1),
      maskedBit (scanV 5) (scanV 2), wordV]

/-- A scanner register's step: its tail, which advances the pointer or the
mask by one index. -/
@[expose] def scanStep (j : Fin 6) : LOf (6 + k + 4 + 1) := tailAppL (scanV j)

/-- A register's step: its update at the registers, the three bits and the
word. -/
@[expose] def regStep (upd : Fin k → LOf (k + 4)) (j : Fin k) : LOf (6 + k + 4 + 1) :=
  compL (upd j) updEnv

/-- The recursion's steps: the scanner registers' tails and the registers'
updates, the same for either bit of the counter. -/
@[expose, nolint unusedArguments] def foldStep (upd : Fin k → LOf (k + 4)) :
    Bool → Fin (6 + k) → LOf (6 + k + 4 + 1) :=
  fun _ ↦ Fin.append scanStep (regStep upd)

/-- The bases that read each numeral's payload: the payload pointer and the
payload mask of each of the three positions. -/
@[expose] def payScan : Fin 6 → LOf 4 :=
  ![payPtr (projL 4 0) (projL 4 1), payPtr (projL 4 0) (projL 4 2),
    payPtr (projL 4 0) (projL 4 3), payMask (projL 4 0) (projL 4 1),
    payMask (projL 4 0) (projL 4 2), payMask (projL 4 0) (projL 4 3)]

/-- The bases that read each numeral's code: the position itself and the code
mask of each of the three positions. -/
@[expose] def codeScan : Fin 6 → LOf 4 :=
  ![projL 4 1, projL 4 2, projL 4 3, codeMask (projL 4 0) (projL 4 1),
    codeMask (projL 4 0) (projL 4 2), codeMask (projL 4 0) (projL 4 3)]

/-- The recursion's bases: the scanner registers' and the given ones. -/
@[expose] def foldBase (scan : Fin 6 → LOf 4) (base : Fin k → LOf 4) : Fin (6 + k) → LOf 4 :=
  Fin.append scan base

/-- A step environment of the recursion: the level, the scanner registers and
the registers, and the word and the three positions. -/
@[expose] def envOf (v : List Bool) (vals : Fin (6 + k) → List Bool) (x : Fin 4 → List Bool) :
    Fin (6 + k + 4 + 1) → List Bool :=
  stepEnv (a := 4) (b := 6 + k) v vals x

/-- The registers, as expressions of arity five: the counter, the word and
the three positions. -/
@[expose] def foldReg (scan : Fin 6 → LOf 4) (base : Fin k → LOf 4) (upd : Fin k → LOf (k + 4))
    (l : Fin (6 + k)) : LOf 5 :=
  srnL (foldBase scan base) (foldStep upd) l

/-- A register after the fold over the word, of arity four: the word and
the three positions. -/
@[expose] def bitFold (scan : Fin 6 → LOf 4) (base : Fin k → LOf 4) (upd : Fin k → LOf (k + 4))
    (j : Fin k) : LOf 4 :=
  compL (foldReg scan base upd (Fin.natAdd 6 j))
    ![projL 4 0, projL 4 0, projL 4 1, projL 4 2, projL 4 3]

/-- The update's meaning on registers and three bits, at a word. -/
@[expose] def updF (upd : Fin k → LOf (k + 4)) (y : List Bool) (regs : Fin k → List Bool)
    (a b c : Bool) : Fin k → List Bool :=
  fun j ↦ (upd j).sem (Fin.append regs ![boolWord a, boolWord b, boolWord c, y])

/-- The registers after the indices below a bound: the update iterated on the
three bit streams at the successive indices. -/
@[expose] def iter (upd : Fin k → LOf (k + 4)) (y : List Bool) (bA bB bC : ℕ → Bool)
    (regs0 : Fin k → List Bool) : ℕ → Fin k → List Bool :=
  Nat.rec regs0 fun i regs ↦ updF upd y regs (bA i) (bB i) (bC i)

/-- The bases' meanings at a word and three positions. -/
@[expose] def regs0 (base : Fin k → LOf 4) (y : List Bool) (pA pB pC : ℕ) : Fin k → List Bool :=
  fun j ↦ (base j).sem ![y, y.drop pA, y.drop pB, y.drop pC]

/-- The offsets the payload bases read from. -/
@[expose] def payOff (y : List Bool) (pA pB pC : ℕ) : Fin 6 → ℕ :=
  ![payStart y pA, payStart y pB, payStart y pC, payMaskStart y pA, payMaskStart y pB,
    payMaskStart y pC]

/-- The offsets the code bases read from. -/
@[expose] def codeOff (y : List Bool) (pA pB pC : ℕ) : Fin 6 → ℕ :=
  ![pA, pB, pC, codeMaskStart y pA, codeMaskStart y pB, codeMaskStart y pC]

/-- The payload bases read from the payload offsets. -/
theorem sem_payScan (y : List Bool) (pA pB pC : ℕ) (hA : pA ≤ y.length) (hB : pB ≤ y.length)
    (hC : pC ≤ y.length) (j : Fin 6) :
    (payScan j).sem ![y, y.drop pA, y.drop pB, y.drop pC] = y.drop (payOff y pA pB pC j) := by
  have hpar : ∀ m : Fin 4, (projL 4 m).sem ![y, y.drop pA, y.drop pB, y.drop pC] =
      ![y, y.drop pA, y.drop pB, y.drop pC] m := fun _ ↦ rfl
  match j with
  | 0 => exact sem_payPtr _ _ _ y pA (hpar 0) (hpar 1) hA
  | 1 => exact sem_payPtr _ _ _ y pB (hpar 0) (hpar 2) hB
  | 2 => exact sem_payPtr _ _ _ y pC (hpar 0) (hpar 3) hC
  | 3 => exact sem_payMask _ _ _ y pA (hpar 0) (hpar 1) hA
  | 4 => exact sem_payMask _ _ _ y pB (hpar 0) (hpar 2) hB
  | 5 => exact sem_payMask _ _ _ y pC (hpar 0) (hpar 3) hC

/-- The code bases read from the code offsets. -/
theorem sem_codeScan (y : List Bool) (pA pB pC : ℕ) (hA : pA ≤ y.length) (hB : pB ≤ y.length)
    (hC : pC ≤ y.length) (j : Fin 6) :
    (codeScan j).sem ![y, y.drop pA, y.drop pB, y.drop pC] = y.drop (codeOff y pA pB pC j) := by
  have hpar : ∀ m : Fin 4, (projL 4 m).sem ![y, y.drop pA, y.drop pB, y.drop pC] =
      ![y, y.drop pA, y.drop pB, y.drop pC] m := fun _ ↦ rfl
  match j with
  | 0 | 1 | 2 => rfl
  | 3 => exact sem_codeMask _ _ _ y pA (hpar 0) (hpar 1) hA
  | 4 => exact sem_codeMask _ _ _ y pB (hpar 0) (hpar 2) hB
  | 5 => exact sem_codeMask _ _ _ y pC (hpar 0) (hpar 3) hC

/-- The registers' meanings at a counter, a word and three positions. -/
@[expose] def regs (scan : Fin 6 → LOf 4) (base : Fin k → LOf 4) (upd : Fin k → LOf (k + 4))
    (u y : List Bool) (pA pB pC : ℕ) : Fin (6 + k) → List Bool :=
  fun l ↦ (foldReg scan base upd l).sem (Fin.cons u ![y, y.drop pA, y.drop pB, y.drop pC])

/-- A scanner register's slot of a step environment. -/
theorem envOf_scanSlot (v : List Bool) (vals : Fin (6 + k) → List Bool) (x : Fin 4 → List Bool)
    (j : Fin 6) : envOf v vals x (scanSlot j) = vals (Fin.castAdd k j) := by
  rw [envOf, stepEnv, scanSlot, Fin.cons_succ, Fin.append_left]

/-- A register's slot of a step environment. -/
theorem envOf_regSlot (v : List Bool) (vals : Fin (6 + k) → List Bool) (x : Fin 4 → List Bool)
    (j : Fin k) : envOf v vals x (regSlot j) = vals (Fin.natAdd 6 j) := by
  rw [envOf, stepEnv, regSlot, Fin.cons_succ, Fin.append_left]

/-- A parameter's slot of a step environment. -/
theorem envOf_parSlot (v : List Bool) (vals : Fin (6 + k) → List Bool) (x : Fin 4 → List Bool)
    (j : Fin 4) : envOf v vals x (parSlot j) = x j := by
  rw [envOf, stepEnv, parSlot, Fin.cons_succ, Fin.append_right]

/-- The bit of a numeral, on registers holding the pointer and the mask at an
index. -/
theorem sem_maskedBit (mask ptr : LOf (6 + k + 4 + 1)) (z : Fin (6 + k + 4 + 1) → List Bool)
    (y : List Bool) (ms ps : ℕ) (hm : mask.sem z = y.drop ms) (hs : ptr.sem z = y.drop ps) :
    (maskedBit mask ptr).sem z =
      boolWord (if y.length ≤ ms then false else (y.drop ps).headD false) := by
  have hmask : (andOkAt mask (constL (6 + k + 4 + 1) [true])).sem z =
      boolWord (if y.length ≤ ms then false else true) := by
    rw [andOkAt, sem_cond4L, hm, sem_constL, sem_constL, EliasTree.cond4Sem_same]
    by_cases hl : y.length ≤ ms
    · rw [if_pos (List.drop_eq_nil_iff.mpr hl), if_pos hl]
      rfl
    · rw [if_neg fun h ↦ hl (List.drop_eq_nil_iff.mp h), if_neg hl]
      rfl
  rw [maskedBit, sem_cond4L, hs, hmask]
  by_cases hl : y.length ≤ ms
  · simp only [if_pos hl]
    cases hd : y.drop ps with
    | nil => rfl
    | cons c cs => cases c <;> rfl
  · simp only [if_neg hl]
    cases hd : y.drop ps with
    | nil => rfl
    | cons c cs => cases c <;> rfl

/-- The update's environment on a step environment holding the scanner
registers at an index and the registers is the registers, the three numerals'
bits at that index, and the word. -/
theorem sem_updEnv (v y : List Bool) (pA pB pC i : ℕ) (off : Fin 6 → ℕ)
    (rs : Fin k → List Bool) :
    (fun m ↦ (updEnv m).sem
        (envOf v (Fin.append (fun j ↦ y.drop (off j + i)) rs)
          ![y, y.drop pA, y.drop pB, y.drop pC])) =
      Fin.append rs
        ![boolWord (segBit y (off 0) (off 3) i), boolWord (segBit y (off 1) (off 4) i),
          boolWord (segBit y (off 2) (off 5) i), y] := by
  have hv : ∀ j : Fin 6,
      (scanV j).sem (envOf v (Fin.append (fun j ↦ y.drop (off j + i)) rs)
        ![y, y.drop pA, y.drop pB, y.drop pC]) = y.drop (off j + i) := fun j ↦ by
    rw [scanV, sem_projL, envOf_scanSlot, Fin.append_left]
  funext m
  refine Fin.addCases (motive := fun m ↦ (updEnv m).sem
    (envOf v (Fin.append (fun j ↦ y.drop (off j + i)) rs) ![y, y.drop pA, y.drop pB, y.drop pC]) =
      Fin.append rs
        ![boolWord (segBit y (off 0) (off 3) i), boolWord (segBit y (off 1) (off 4) i),
          boolWord (segBit y (off 2) (off 5) i), y] m)
    (fun j ↦ ?_) (fun j ↦ ?_) m
  · beta_reduce
    rw [updEnv, Fin.append_left, Fin.append_left, sem_projL, envOf_regSlot, Fin.append_right]
  · beta_reduce
    rw [updEnv, Fin.append_right, Fin.append_right]
    match j with
    | 0 =>
      change (maskedBit (scanV 3) (scanV 0)).sem _ = boolWord (segBit y (off 0) (off 3) i)
      rw [sem_maskedBit _ _ _ y (off 3 + i) (off 0 + i) (hv 3) (hv 0), segBit]
    | 1 =>
      change (maskedBit (scanV 4) (scanV 1)).sem _ = boolWord (segBit y (off 1) (off 4) i)
      rw [sem_maskedBit _ _ _ y (off 4 + i) (off 1 + i) (hv 4) (hv 1), segBit]
    | 2 =>
      change (maskedBit (scanV 5) (scanV 2)).sem _ = boolWord (segBit y (off 2) (off 5) i)
      rw [sem_maskedBit _ _ _ y (off 5 + i) (off 2 + i) (hv 5) (hv 2), segBit]
    | 3 =>
      change wordV.sem _ = y
      rw [wordV, sem_projL, envOf_parSlot]
      rfl

/-- One more counter bit runs the step of each register at the environment
holding the registers and the parameters. -/
theorem regs_cons (scan : Fin 6 → LOf 4) (base : Fin k → LOf 4) (upd : Fin k → LOf (k + 4))
    (b : Bool) (v y : List Bool) (pA pB pC : ℕ) (l : Fin (6 + k)) :
    regs scan base upd (b :: v) y pA pB pC l =
      (foldStep upd b l).sem
        (envOf v (regs scan base upd v y pA pB pC) ![y, y.drop pA, y.drop pB, y.drop pC]) :=
  sem_srnL_cons (foldBase scan base) (foldStep upd) l b v ![y, y.drop pA, y.drop pB, y.drop pC]

/-- After a prefix of the word is read, the pointers and masks hold the word
dropped by the prefix's length further and the registers the iteration over
it. -/
theorem regs_eq (scan : Fin 6 → LOf 4) (base : Fin k → LOf 4) (upd : Fin k → LOf (k + 4))
    (y : List Bool) (pA pB pC : ℕ) (off : Fin 6 → ℕ)
    (hoff : ∀ j, (scan j).sem ![y, y.drop pA, y.drop pB, y.drop pC] = y.drop (off j)) :
    ∀ u : List Bool,
      regs scan base upd u y pA pB pC =
        Fin.append (fun j ↦ y.drop (off j + u.length))
          (iter upd y (segBit y (off 0) (off 3)) (segBit y (off 1) (off 4))
            (segBit y (off 2) (off 5)) (regs0 base y pA pB pC) u.length) :=
  List.rec (by
      funext l
      refine Fin.addCases (motive := fun l ↦ regs scan base upd [] y pA pB pC l =
        Fin.append (fun j ↦ y.drop (off j + List.length ([] : List Bool)))
          (iter upd y (segBit y (off 0) (off 3)) (segBit y (off 1) (off 4))
            (segBit y (off 2) (off 5)) (regs0 base y pA pB pC) 0) l)
        (fun j ↦ ?_) (fun j ↦ ?_) l
      · change (foldReg scan base upd (Fin.castAdd k j)).sem
          (Fin.cons [] ![y, y.drop pA, y.drop pB, y.drop pC]) = _
        rw [foldReg, sem_srnL_nil, foldBase, Fin.append_left, Fin.append_left]
        exact hoff j
      · change (foldReg scan base upd (Fin.natAdd 6 j)).sem
          (Fin.cons [] ![y, y.drop pA, y.drop pB, y.drop pC]) = _
        rw [foldReg, sem_srnL_nil, foldBase, Fin.append_right, Fin.append_right]
        rfl)
    (fun b v ih ↦ by
      funext l
      rw [regs_cons, ih]
      refine Fin.addCases (motive := fun l ↦ (foldStep upd b l).sem (envOf v
          (Fin.append (fun j ↦ y.drop (off j + v.length))
            (iter upd y (segBit y (off 0) (off 3)) (segBit y (off 1) (off 4))
              (segBit y (off 2) (off 5)) (regs0 base y pA pB pC) v.length))
          ![y, y.drop pA, y.drop pB, y.drop pC]) =
        Fin.append (fun j ↦ y.drop (off j + (v.length + 1)))
          (iter upd y (segBit y (off 0) (off 3)) (segBit y (off 1) (off 4))
            (segBit y (off 2) (off 5)) (regs0 base y pA pB pC) (v.length + 1)) l)
        (fun j ↦ ?_) (fun j ↦ ?_) l
      · beta_reduce
        rw [foldStep, Fin.append_left, Fin.append_left]
        change (tailAppL (scanV j)).sem _ = _
        rw [sem_tailAppL, scanV, sem_projL, envOf_scanSlot, Fin.append_left]
        exact List.tail_drop
      · beta_reduce
        rw [foldStep, Fin.append_right, Fin.append_right]
        change (regStep upd j).sem _ =
          updF upd y _ (segBit y (off 0) (off 3) v.length) (segBit y (off 1) (off 4) v.length)
            (segBit y (off 2) (off 5) v.length) j
        rw [regStep, sem_compL, sem_updEnv v y pA pB pC v.length off]
        rfl)

/-- A register after the fold over the word is the iteration over the word's
length. -/
theorem sem_bitFold (scan : Fin 6 → LOf 4) (base : Fin k → LOf 4) (upd : Fin k → LOf (k + 4))
    (y : List Bool) (pA pB pC : ℕ) (off : Fin 6 → ℕ)
    (hoff : ∀ j, (scan j).sem ![y, y.drop pA, y.drop pB, y.drop pC] = y.drop (off j))
    (j : Fin k) :
    (bitFold scan base upd j).sem ![y, y.drop pA, y.drop pB, y.drop pC] =
      iter upd y (segBit y (off 0) (off 3)) (segBit y (off 1) (off 4)) (segBit y (off 2) (off 5))
        (regs0 base y pA pB pC) y.length j := by
  rw [bitFold, sem_compL]
  rw [show (fun i ↦ (![projL 4 0, projL 4 0, projL 4 1, projL 4 2, projL 4 3] i).sem
      ![y, y.drop pA, y.drop pB, y.drop pC]) = Fin.cons y ![y, y.drop pA, y.drop pB, y.drop pC] from
    funext fun i ↦ match i with | 0 | 1 | 2 | 3 | 4 => rfl]
  have h := congrFun (regs_eq scan base upd y pA pB pC off hoff y) (Fin.natAdd 6 j)
  rw [Fin.append_right] at h
  exact h

/-- A register after the fold over the word with the payload bases. -/
theorem sem_bitFold_pay (base : Fin k → LOf 4) (upd : Fin k → LOf (k + 4)) (y : List Bool)
    (pA pB pC : ℕ) (hA : pA ≤ y.length) (hB : pB ≤ y.length) (hC : pC ≤ y.length) (j : Fin k) :
    (bitFold payScan base upd j).sem ![y, y.drop pA, y.drop pB, y.drop pC] =
      iter upd y (payBit y pA) (payBit y pB) (payBit y pC) (regs0 base y pA pB pC) y.length j :=
  sem_bitFold payScan base upd y pA pB pC (payOff y pA pB pC) (sem_payScan y pA pB pC hA hB hC) j

/-- A register after the fold over the word with the code bases. -/
theorem sem_bitFold_code (base : Fin k → LOf 4) (upd : Fin k → LOf (k + 4)) (y : List Bool)
    (pA pB pC : ℕ) (hA : pA ≤ y.length) (hB : pB ≤ y.length) (hC : pC ≤ y.length) (j : Fin k) :
    (bitFold codeScan base upd j).sem ![y, y.drop pA, y.drop pB, y.drop pC] =
      iter upd y (codeBit y pA) (codeBit y pB) (codeBit y pC) (regs0 base y pA pB pC) y.length j :=
  sem_bitFold codeScan base upd y pA pB pC (codeOff y pA pB pC) (sem_codeScan y pA pB pC hA hB hC) j

end

end Geb.SizeBounded.Logspace.WTree.BitFold
