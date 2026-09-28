/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.NumScan
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.ExprBase

set_option doc.verso true in
/-!
# The numeral scanner as a successor-free expression

The scanner of a coded number at a position,
{name}`Geb.SizeBounded.Logspace.WTree.Numeral.nrun`, as expressions of the
logspace subalgebra {name}`Geb.SizeBounded.Logspace.LOf` of arity three: the
word, the word dropped by the position, and the word dropped by an index. The
scanner is a simultaneous recursion with eight registers run over the word as
the counter: the unread input; the mode as a three-bit code; the zero run, the
count and the size field's value as end segments of the word; the bit at the
index and the canonicality as flags; and the position after the numeral as an
end segment. The position and the index enter as end segments too, so that
the tests of the position and of the index are comparisons of end segments,
{name}`Geb.SizeBounded.Logspace.WTree.eqSeg`. The size field's value doubles
by {name}`Geb.SizeBounded.Logspace.bitApp`, which saturates at the word's
length as the scanner's value does.

# Main definitions

* {lit}`modeCode`, {lit}`onModeAt`, {lit}`isDoneN` — the codes of the modes,
  the dispatch on a mode register, and the test of the completed mode.
* {lit}`atTp`, {lit}`sizeEnd`, {lit}`bitsEnd`, {lit}`idxHit`, {lit}`bitWord`,
  {lit}`sBit` — the tests of the step and the values it takes from the
  current bit.
* {lit}`nsBase`, {lit}`nsStep`, {lit}`nsReg` — the recursion's bases and
  steps, and its registers.
* {lit}`numHit`, {lit}`numOk`, {lit}`numEnd` — the bit at the index, the
  acceptance, and the end position, as expressions of arity three.
* {lit}`NValid` — the invariant of the scanner's state at a position that
  bounds the counters the tests compare.

# Main statements

* {lit}`step_encodeNS` — one step on the encoded state is the encoded step of
  the state.
* {lit}`regsNS_eq` — after a prefix of the word, the registers hold the
  encoded run over that prefix.
* {lit}`sem_numOk`, {lit}`sem_numHit`, {lit}`sem_numEnd` — the outputs'
  meanings by the scanner.
* {lit}`num_natCode`, {lit}`num_of_ok` — the outputs on a coded number, and a
  coded number from the acceptance.

# References

* \[Kristiansen2005\]

# Tags

logspace, simultaneous recursion on notation, binary numeral, scanner
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree.NumExpr

open Numeral

public section

/-- The three-bit code of a mode. -/
@[expose] def modeCode : NMode → List Bool
  | .before => [true, true, true]
  | .zeros => [true, true, false]
  | .size => [true, false, true]
  | .bits => [true, false, false]
  | .done => [false, true, true]

/-- Dispatch on a mode register: the three bits of the code select among the
five modes. -/
@[expose] def onModeAt {n : ℕ} (mode before zeros size bits done : LOf n) : LOf n :=
  cond4L mode done
    (cond4L (tailAppL mode) done
      (cond4L (tailAppL (tailAppL mode)) done before zeros)
      (cond4L (tailAppL (tailAppL mode)) done size bits))
    done

/-- The dispatch on a mode code selects the expression of that mode. -/
theorem sem_onModeAt {n : ℕ} (mode before zeros size bits done : LOf n) (x : Fin n → List Bool)
    (m : NMode) (hx : mode.sem x = modeCode m) :
    (onModeAt mode before zeros size bits done).sem x =
      (match m with
        | .before => before
        | .zeros => zeros
        | .size => size
        | .bits => bits
        | .done => done).sem x := by
  simp only [onModeAt, sem_cond4L, sem_tailAppL, hx]
  cases m <;> rfl

/-- The test of the completed mode on a mode register: {lit}`[true]` when the
register holds its code, the empty word otherwise. -/
@[expose] def isDoneN {n : ℕ} (mode : LOf n) : LOf n :=
  cond4L mode (constL n []) (constL n [])
    (cond4L (tailAppL mode) (constL n [])
      (cond4L (tailAppL (tailAppL mode)) (constL n []) (constL n [true]) (constL n []))
      (constL n []))

/-- The test's meaning on a mode code. -/
theorem sem_isDoneN {n : ℕ} (mode : LOf n) (x : Fin n → List Bool) (m : NMode)
    (hx : mode.sem x = modeCode m) : (isDoneN mode).sem x = if m = .done then [true] else [] := by
  simp only [isDoneN, sem_cond4L, sem_tailAppL, sem_constL, hx]
  cases m <;> rfl

/-- A conditional on a flag: the second expression when the flag is set, the
third otherwise. -/
@[expose] def ifFlag {n : ℕ} (f t e : LOf n) : LOf n := cond4L f e t t

/-- The set flag as a word. -/
theorem boolWord_true : boolWord true = [true] := rfl

/-- The clear flag as a word. -/
theorem boolWord_false : boolWord false = [] := rfl

/-- The word dropped by a number cut off at its length is the word dropped by
the number. -/
theorem drop_min_length (y : List Bool) (a : ℕ) : y.drop (min a y.length) = y.drop a := by
  rcases Nat.le_total a y.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.drop_length, List.drop_of_length_le h]

/-- The unread input, slot one of the step environment. -/
@[expose] def restV : LOf 12 := projL 12 1

/-- The mode register, slot two. -/
@[expose] def modeV : LOf 12 := projL 12 2

/-- The zero run, slot three. -/
@[expose] def zV : LOf 12 := projL 12 3

/-- The count, slot four. -/
@[expose] def cntV : LOf 12 := projL 12 4

/-- The size field's value, slot five. -/
@[expose] def sV : LOf 12 := projL 12 5

/-- The bit at the index, slot six. -/
@[expose] def hitV : LOf 12 := projL 12 6

/-- The canonicality, slot seven. -/
@[expose] def okV : LOf 12 := projL 12 7

/-- The end position, slot eight. -/
@[expose] def endV : LOf 12 := projL 12 8

/-- The word, the parameter in slot nine. -/
@[expose] def wordV : LOf 12 := projL 12 9

/-- The position, the parameter in slot ten. -/
@[expose] def tpV : LOf 12 := projL 12 10

/-- The index, the parameter in slot eleven. -/
@[expose] def idxV : LOf 12 := projL 12 11

/-- A mode's code as a constant of the step arity. -/
@[expose] def code (m : NMode) : LOf 12 := constL 12 (modeCode m)

/-- The current bit lies at the position. -/
@[expose] def atTp : LOf 12 := eqSeg restV tpV

/-- The size field ends with this bit: the count raised by one is the zero
run. -/
@[expose] def sizeEnd : LOf 12 := eqSeg (tailAppL cntV) zV

/-- The bits end with this bit: the count raised by two is the value. -/
@[expose] def bitsEnd : LOf 12 := eqSeg (tailAppL (tailAppL cntV)) sV

/-- The current bit lies at the index among the bits. -/
@[expose] def idxHit : LOf 12 := eqSeg cntV idxV

/-- The current bit as a flag. -/
@[expose] def bitWord : LOf 12 := onBitAt restV (constL 12 []) (constL 12 [true]) (constL 12 [])

/-- The value taking the current bit. -/
@[expose] def sBit : LOf 12 := lenAfterHeaderAt restV sV wordV

/-- The unread input's step drops the current bit. -/
@[expose] def restStep : LOf 12 := tailAppL restV

/-- The mode's step. -/
@[expose] def modeStep : LOf 12 :=
  onModeAt modeV
    (ifFlag atTp (onBitAt restV modeV (code .done) (code .zeros)) (code .before))
    (onBitAt restV modeV (code .size) (code .zeros))
    (ifFlag sizeEnd (code .bits) (code .size))
    (ifFlag bitsEnd (code .done) (code .bits))
    modeV

/-- The zero run's step: one at the position on a {lit}`false` bit, rising by
one per further zero. -/
@[expose] def zStep : LOf 12 :=
  onModeAt modeV
    (ifFlag atTp (onBitAt restV zV wordV (tailAppL wordV)) zV)
    (onBitAt restV zV zV (tailAppL zV))
    zV zV zV

/-- The count's step: zero until the size field, rising by one per bit of the
size field and of the bits, and zero again when the size field ends. -/
@[expose] def cntStep : LOf 12 :=
  onModeAt modeV wordV wordV (ifFlag sizeEnd wordV (tailAppL cntV)) (tailAppL cntV) cntV

/-- The value's step: one at the position, taking each bit of the size
field. -/
@[expose] def sStep : LOf 12 :=
  onModeAt modeV (ifFlag atTp (tailAppL wordV) sV) (tailAppL wordV) sBit sV sV

/-- The step of the bit at the index: the current bit when the count is the
index among the bits. -/
@[expose] def hitStep : LOf 12 :=
  onModeAt modeV (constL 12 []) (constL 12 []) (constL 12 [])
    (ifFlag idxHit bitWord hitV) hitV

/-- The canonicality's step: the current bit when it completes the numeral. -/
@[expose] def okStep : LOf 12 :=
  onModeAt modeV (ifFlag atTp bitWord okV) (constL 12 []) (constL 12 [])
    (ifFlag bitsEnd bitWord (constL 12 [])) okV

/-- The end position's step: past the current bit when it completes the
numeral. -/
@[expose] def endStep : LOf 12 :=
  onModeAt modeV
    (ifFlag atTp (onBitAt restV endV (tailAppL restV) wordV) endV)
    wordV wordV
    (ifFlag bitsEnd (tailAppL restV) wordV)
    endV

/-- The recursion's bases: the word, the code of the mode before the position,
the word for each counter at zero, the flags clear, and the word for the end
position at zero. -/
@[expose] def nsBase : Fin 8 → LOf 3 :=
  ![projL 3 0, constL 3 (modeCode .before), projL 3 0, projL 3 0, projL 3 0, constL 3 [],
    constL 3 [], projL 3 0]

/-- The recursion's steps, the same for either bit of the counter. -/
@[expose, nolint unusedArguments] def nsStep : Bool → Fin 8 → LOf 12 :=
  fun _ ↦ ![restStep, modeStep, zStep, cntStep, sStep, hitStep, okStep, endStep]

/-- The eight registers, as expressions of arity four: the counter, the word,
the position and the index. -/
@[expose] def nsReg (l : Fin 8) : LOf 4 := srnL nsBase nsStep l

/-- A register with the word as the counter, of arity three. -/
@[expose] def numReg (l : Fin 8) : LOf 3 :=
  compL (nsReg l) ![projL 3 0, projL 3 0, projL 3 1, projL 3 2]

/-- The bit at the index, as a flag. -/
@[expose] def numHit : LOf 3 := numReg 5

/-- The acceptance: the canonicality when the scanner ended done. -/
@[expose] def numOk : LOf 3 := cond4L (isDoneN (numReg 1)) (constL 3 []) (numReg 6) (numReg 6)

/-- The end position, as an end segment of the word. -/
@[expose] def numEnd : LOf 3 := numReg 7

/-- The registers holding a remaining word and a state: the mode's code, the
word dropped by each counter, the flags as words, and the word dropped by the
end position. -/
@[expose] def encodeNS (y r : List Bool) (x : NState) : Fin 8 → List Bool :=
  ![r, modeCode x.mode, y.drop x.z, y.drop x.cnt, y.drop x.s, boolWord x.hit, boolWord x.ok,
    y.drop x.endPos]

/-- The step environment at a level, holding the registers, the word, the
position and the index. -/
@[expose] def stepAtNS (u y r : List Bool) (x : NState) (tp i : ℕ) : Fin 12 → List Bool :=
  stepEnv u (encodeNS y r x) ![y, y.drop tp, y.drop i]

variable (u y r : List Bool) (x : NState) (tp i : ℕ)

/-- The unread input's meaning. -/
theorem sem_restV : restV.sem (stepAtNS u y r x tp i) = r := rfl

/-- The mode register's meaning. -/
theorem sem_modeV : modeV.sem (stepAtNS u y r x tp i) = modeCode x.mode := rfl

/-- The zero run's meaning. -/
theorem sem_zV : zV.sem (stepAtNS u y r x tp i) = y.drop x.z := rfl

/-- The count's meaning. -/
theorem sem_cntV : cntV.sem (stepAtNS u y r x tp i) = y.drop x.cnt := rfl

/-- The value's meaning. -/
theorem sem_sV : sV.sem (stepAtNS u y r x tp i) = y.drop x.s := rfl

/-- The meaning of the bit at the index. -/
theorem sem_hitV : hitV.sem (stepAtNS u y r x tp i) = boolWord x.hit := rfl

/-- The canonicality's meaning. -/
theorem sem_okV : okV.sem (stepAtNS u y r x tp i) = boolWord x.ok := rfl

/-- The end position's meaning. -/
theorem sem_endV : endV.sem (stepAtNS u y r x tp i) = y.drop x.endPos := rfl

/-- The word's meaning. -/
theorem sem_wordV : wordV.sem (stepAtNS u y r x tp i) = y := rfl

/-- The position's meaning. -/
theorem sem_tpV : tpV.sem (stepAtNS u y r x tp i) = y.drop tp := rfl

/-- The index's meaning. -/
theorem sem_idxV : idxV.sem (stepAtNS u y r x tp i) = y.drop i := rfl

/-- The dispatch on the mode register of a step environment selects the
expression of the state's mode. -/
theorem sem_onModeAt_stepAt (before zeros size bits done : LOf 12) :
    (onModeAt modeV before zeros size bits done).sem (stepAtNS u y r x tp i) =
      (match x.mode with
        | .before => before
        | .zeros => zeros
        | .size => size
        | .bits => bits
        | .done => done).sem (stepAtNS u y r x tp i) :=
  sem_onModeAt _ _ _ _ _ _ _ x.mode rfl

/-- The invariant of the scanner's state at a position: before the position
the state is initial; in the zero run the count is zero, the value one and the
run between one and the position; in the size field the count is below the
run, the run and the count lie before the position, and the value is bounded
by the word's length; among the bits the count lies three before the position
and the value is bounded. -/
@[expose] def NValid (n pos : ℕ) (x : NState) : Prop :=
  (x.mode = .before →
    x.z = 0 ∧ x.cnt = 0 ∧ x.s = 0 ∧ x.hit = false ∧ x.ok = false ∧ x.endPos = 0) ∧
  (x.mode = .zeros → x.cnt = 0 ∧ x.s = 1 ∧ 1 ≤ x.z ∧ x.z ≤ pos) ∧
  (x.mode = .size → x.cnt < x.z ∧ x.z + x.cnt + 1 ≤ pos ∧ x.s ≤ n) ∧
  (x.mode = .bits → x.cnt + 3 ≤ pos ∧ x.s ≤ n)

/-- The initial state satisfies the invariant. -/
theorem nvalid_nstart (n : ℕ) : NValid n 0 nstart := by
  refine ⟨fun _ ↦ ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩, fun h ↦ ?_, fun h ↦ ?_, fun h ↦ ?_⟩ <;>
    exact absurd h (by decide)

/-- One bit within the word preserves the invariant. -/
theorem nvalid_step (n tp i pos : ℕ) (x : NState) (b : Bool) (hpos : pos < n)
    (hv : NValid n pos x) : NValid n (pos + 1) (nstep n tp i x pos b) := by
  cases hm : x.mode <;>
    simp only [NValid, hm, reduceCtorEq, false_implies, true_implies, true_and, and_true] at hv <;>
    unfold nstep <;> rw [hm] <;> dsimp only <;> cases b <;> (try split_ifs) <;>
    simp only [NValid, reduceCtorEq, false_implies, true_implies, true_and, and_true,
      Bool.toNat_false, Bool.toNat_true, *] <;>
    (repeat' apply And.intro) <;> omega

/-- A segment within the word preserves the invariant. -/
theorem nvalid_runFrom (n tp i : ℕ) (v : List Bool) : ∀ (x : NState) (pos : ℕ), NValid n pos x →
    pos + v.length ≤ n → NValid n (pos + v.length) (nrunFrom n tp i x pos v).1 :=
  List.rec (fun x pos hv _ ↦ hv) (fun b v ih x pos hv hn ↦ by
    rw [List.length_cons] at hn ⊢
    rw [nrunFrom_cons, show pos + (v.length + 1) = pos + 1 + v.length by omega]
    exact ih _ (pos + 1) (nvalid_step n tp i pos x b (by omega) hv) (by omega)) v

/-- The position after a segment. -/
theorem nrunFrom_snd (n tp i : ℕ) (v : List Bool) : ∀ (x : NState) (pos : ℕ),
    (nrunFrom n tp i x pos v).2 = pos + v.length :=
  List.rec (fun _ _ ↦ rfl) (fun b v ih x pos ↦ by
    rw [nrunFrom_cons, ih, List.length_cons]
    omega) v

section StepLemmas

variable (c : Bool) (p : List Bool) (hy : y = p ++ c :: r) (hv : NValid y.length p.length x)
  (htp : tp ≤ y.length) (hi : i ≤ y.length)

include hy in
/-- The remaining word from the current bit. -/
theorem drop_length_eq : y.drop p.length = c :: r := by
  rw [hy, List.drop_left]

include hy in
/-- The remaining word past the current bit. -/
theorem drop_succ_length : y.drop (p.length + 1) = r := by
  rw [hy, ← List.drop_drop, List.drop_left, List.drop_one]
  rfl

include hy in
/-- The current bit lies within the word. -/
theorem length_lt : p.length < y.length := by
  rw [hy, List.length_append, List.length_cons]
  omega

include htp in
/-- The position test's meaning. -/
theorem sem_atTp (hr : y.drop p.length = c :: r) (hp : p.length ≤ y.length) :
    atTp.sem (stepAtNS u y (c :: r) x tp i) = boolWord (decide (p.length = tp)) :=
  sem_eqSeg restV tpV _ y p.length tp hr.symm rfl hp htp

/-- The size-end test's meaning. -/
theorem sem_sizeEnd (h1 : x.cnt + 1 ≤ y.length) (h2 : x.z ≤ y.length) :
    sizeEnd.sem (stepAtNS u y (c :: r) x tp i) = boolWord (decide (x.cnt + 1 = x.z)) :=
  sem_eqSeg _ _ _ y (x.cnt + 1) x.z
    (by rw [sem_tailAppL]; change (y.drop x.cnt).tail = _; rw [List.tail_drop]) rfl h1 h2

/-- The bits-end test's meaning. -/
theorem sem_bitsEnd (h1 : x.cnt + 1 + 1 ≤ y.length) (h2 : x.s ≤ y.length) :
    bitsEnd.sem (stepAtNS u y (c :: r) x tp i) = boolWord (decide (x.cnt + 1 + 1 = x.s)) :=
  sem_eqSeg _ _ _ y (x.cnt + 1 + 1) x.s
    (by
      rw [sem_tailAppL, sem_tailAppL]
      change (y.drop x.cnt).tail.tail = _
      rw [List.tail_drop, List.tail_drop])
    rfl h1 h2

include hi in
/-- The index test's meaning. -/
theorem sem_idxHit (h1 : x.cnt ≤ y.length) :
    idxHit.sem (stepAtNS u y (c :: r) x tp i) = boolWord (decide (x.cnt = i)) :=
  sem_eqSeg _ _ _ y x.cnt i rfl rfl h1 hi

/-- The current bit as a flag, its meaning. -/
theorem sem_bitWord : bitWord.sem (stepAtNS u y (c :: r) x tp i) = boolWord c := by
  rw [bitWord, sem_onBitAt _ _ _ _ _ c r rfl]
  cases c <;> rfl

/-- The value taking the current bit, its meaning. -/
theorem sem_sBit : sBit.sem (stepAtNS u y (c :: r) x tp i) = y.drop (2 * x.s + c.toNat) :=
  sem_lenAfterHeaderAt restV sV wordV _ y r c x.s rfl rfl rfl

/-- The dispatch on the current bit of a step environment selects by that
bit. -/
theorem sem_onBitAt_stepAt (e t f : LOf 12) :
    (onBitAt restV e t f).sem (stepAtNS u y (c :: r) x tp i) =
      (if c then t else f).sem (stepAtNS u y (c :: r) x tp i) :=
  sem_onBitAt _ _ _ _ _ c r rfl

/-- The facts the register steps share: the position test's meaning and the
remaining words; the word's decomposition is then discarded, so that the
evaluation does not rewrite the word by it. -/
local macro "ns_facts" : tactic =>
  `(tactic| (have hr0 := drop_length_eq y r c p hy
             have hr := drop_succ_length y r c p hy
             have hp := length_lt y r c p hy
             have hp' := Nat.le_of_lt hp
             have hA := sem_atTp u y r x tp i c p htp hr0 hp'
             clear hy))

/-- The evaluation of a register step on a step environment: the dispatch on
the bit, the conditionals, the tests, the registers, and the reductions of the
literal codes and counters. -/
local macro "eval_ns" : tactic =>
  `(tactic| simp only [sem_onBitAt_stepAt, ifFlag, sem_cond4L, cond4Sem, sem_sizeEnd,
      sem_bitsEnd, sem_idxHit, sem_bitWord, sem_sBit, sem_tailAppL, sem_constL, code, sem_restV,
      sem_modeV, sem_zV, sem_cntV, sem_sV, sem_hitV, sem_okV, sem_endV, sem_wordV, boolWord_true,
      boolWord_false, List.tail_cons, List.tail_drop, List.drop_zero, List.drop_one,
      drop_min_length, ↓reduceIte, eq_self_iff_true, decide_true, decide_false,
      Bool.false_eq_true, Bool.toNat_false, Bool.toNat_true, Nat.add_zero, *])

/-- The case analysis of a register step: by the mode, by the current bit,
and by the outcomes of the tests, with the bounds the tests need. -/
local macro "ns_cases" : tactic =>
  `(tactic| (cases hm : x.mode <;>
             simp only [NValid, hm, reduceCtorEq, false_implies, true_implies, true_and,
               and_true] at hv <;>
             unfold nstep <;> rw [hm] <;> dsimp only <;> cases c <;>
             by_cases h1 : p.length = tp <;> (try subst h1) <;>
             by_cases h2 : x.cnt + 1 = x.z <;> by_cases h3 : x.cnt + 1 + 1 = x.s <;>
             by_cases h4 : x.cnt = i <;>
             (try have b1 : x.cnt + 1 ≤ y.length := by omega) <;>
             (try have b2 : x.z ≤ y.length := by omega) <;>
             (try have b3 : x.cnt + 1 + 1 ≤ y.length := by omega) <;>
             (try have b4 : x.s ≤ y.length := by omega) <;>
             (try have b5 : x.cnt ≤ y.length := by omega) <;>
             (try replace h1 := eq_false h1) <;>
             (first | replace h2 := eq_false h2 | replace h2 := eq_true h2) <;>
             (first | replace h3 := eq_false h3 | replace h3 := eq_true h3) <;>
             (first | replace h4 := eq_false h4 | replace h4 := eq_true h4)))

/-- The unread input's step on the encoded state drops the current bit. -/
theorem rest_step : restStep.sem (stepAtNS u y (c :: r) x tp i) = r := by
  rw [restStep, sem_tailAppL, sem_restV]
  rfl

include hy hv htp hi in
/-- The mode's step on the encoded state is the encoded step of the mode. -/
theorem mode_step :
    modeStep.sem (stepAtNS u y (c :: r) x tp i) =
      modeCode (nstep y.length tp i x p.length c).mode := by
  ns_facts
  rw [modeStep, sem_onModeAt_stepAt]
  ns_cases <;> eval_ns

include hy hv htp hi in
/-- The zero run's step on the encoded state is the encoded step of the zero
run. -/
theorem z_step :
    zStep.sem (stepAtNS u y (c :: r) x tp i) = y.drop (nstep y.length tp i x p.length c).z := by
  ns_facts
  rw [zStep, sem_onModeAt_stepAt]
  ns_cases <;> eval_ns

include hy hv htp hi in
/-- The count's step on the encoded state is the encoded step of the count. -/
theorem cnt_step :
    cntStep.sem (stepAtNS u y (c :: r) x tp i) =
      y.drop (nstep y.length tp i x p.length c).cnt := by
  ns_facts
  rw [cntStep, sem_onModeAt_stepAt]
  ns_cases <;> eval_ns

include hy hv htp hi in
/-- The value's step on the encoded state is the encoded step of the value. -/
theorem s_step :
    sStep.sem (stepAtNS u y (c :: r) x tp i) = y.drop (nstep y.length tp i x p.length c).s := by
  ns_facts
  rw [sStep, sem_onModeAt_stepAt]
  ns_cases <;> eval_ns

include hy hv htp hi in
/-- The step of the bit at the index on the encoded state is the encoded step
of that bit. -/
theorem hit_step :
    hitStep.sem (stepAtNS u y (c :: r) x tp i) =
      boolWord (nstep y.length tp i x p.length c).hit := by
  ns_facts
  rw [hitStep, sem_onModeAt_stepAt]
  ns_cases <;> eval_ns

include hy hv htp hi in
/-- The canonicality's step on the encoded state is the encoded step of the
canonicality. -/
theorem ok_step :
    okStep.sem (stepAtNS u y (c :: r) x tp i) =
      boolWord (nstep y.length tp i x p.length c).ok := by
  ns_facts
  rw [okStep, sem_onModeAt_stepAt]
  ns_cases <;> eval_ns

include hy hv htp hi in
/-- The end position's step on the encoded state is the encoded step of the
end position. -/
theorem end_step :
    endStep.sem (stepAtNS u y (c :: r) x tp i) =
      y.drop (nstep y.length tp i x p.length c).endPos := by
  ns_facts
  rw [endStep, sem_onModeAt_stepAt]
  ns_cases <;> eval_ns

include hy hv htp hi in
/-- One step on the encoded state is the encoded step of the state. -/
theorem step_encodeNS (b : Bool) (l : Fin 8) :
    (nsStep b l).sem (stepAtNS u y (c :: r) x tp i) =
      encodeNS y r (nstep y.length tp i x p.length c) l :=
  match l with
  | 0 => rest_step u y r x tp i c
  | 1 => mode_step u y r x tp i c p hy hv htp hi
  | 2 => z_step u y r x tp i c p hy hv htp hi
  | 3 => cnt_step u y r x tp i c p hy hv htp hi
  | 4 => s_step u y r x tp i c p hy hv htp hi
  | 5 => hit_step u y r x tp i c p hy hv htp hi
  | 6 => ok_step u y r x tp i c p hy hv htp hi
  | 7 => end_step u y r x tp i c p hy hv htp hi

end StepLemmas

/-- The registers' meanings at a counter, a word, a position and an index. -/
@[expose] def regsNS (u y : List Bool) (tp i : ℕ) : Fin 8 → List Bool :=
  fun l ↦ (nsReg l).sem (Fin.cons u ![y, y.drop tp, y.drop i])

/-- On the empty counter the registers hold the encoded initial state with the
whole word remaining. -/
theorem regsNS_nil (y : List Bool) (tp i : ℕ) : regsNS [] y tp i = encodeNS y y nstart :=
  funext fun l ↦ match l with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => rfl

/-- One more counter bit runs the step of each register at the environment
holding the registers and the parameters. -/
theorem regsNS_cons (b : Bool) (v y : List Bool) (tp i : ℕ) (l : Fin 8) :
    regsNS (b :: v) y tp i l =
      (nsStep b l).sem (stepEnv v (regsNS v y tp i) ![y, y.drop tp, y.drop i]) :=
  sem_srnL_cons nsBase nsStep l b v _

/-- After a prefix of the word is read, the registers hold the remaining word
and the encoded run over that prefix. -/
theorem regsNS_eq (y u : List Bool) (tp i : ℕ) (htp : tp ≤ y.length) (hi : i ≤ y.length) :
    ∀ (p r : List Bool), y = p ++ r → p.length = u.length →
      regsNS u y tp i = encodeNS y r (nrunFrom y.length tp i nstart 0 p).1 :=
  List.rec
    (motive := fun u ↦ ∀ (p r : List Bool), y = p ++ r → p.length = u.length →
      regsNS u y tp i = encodeNS y r (nrunFrom y.length tp i nstart 0 p).1)
    (fun p r hy hp ↦ by
      have hp' : p = [] := List.eq_nil_of_length_eq_zero hp
      subst hp'
      subst hy
      exact regsNS_nil _ tp i)
    (fun b v ih p r hy hp ↦ by
      rcases List.eq_nil_or_concat p with hn | ⟨p', c, hc⟩
      · subst hn
        exact absurd hp.symm (Nat.succ_ne_zero v.length)
      · rw [List.concat_eq_append] at hc
        subst hc
        rw [List.length_append, List.length_singleton, List.length_cons] at hp
        rw [List.append_assoc, List.singleton_append] at hy
        have hv : NValid y.length p'.length (nrunFrom y.length tp i nstart 0 p').1 := by
          have := nvalid_runFrom y.length tp i p' nstart 0 (nvalid_nstart _)
            (by rw [hy, List.length_append, List.length_cons]; omega)
          rwa [Nat.zero_add] at this
        funext l
        rw [regsNS_cons, ih p' (c :: r) hy (by omega), nrunFrom_append, nrunFrom_snd, Nat.zero_add]
        exact step_encodeNS v y r _ tp i c p' hy hv htp hi b l) u

/-- A register with the word as the counter holds the encoded run over the
word, with nothing remaining. -/
theorem sem_numReg (l : Fin 8) (y : List Bool) (tp i : ℕ) (htp : tp ≤ y.length)
    (hi : i ≤ y.length) :
    (numReg l).sem ![y, y.drop tp, y.drop i] = encodeNS y [] (nrun tp i y) l := by
  rw [numReg, sem_compL]
  rw [show (fun j ↦ (![projL 3 0, projL 3 0, projL 3 1, projL 3 2] j).sem
      ![y, y.drop tp, y.drop i]) = Fin.cons y ![y, y.drop tp, y.drop i] from
    funext fun j ↦ match j with | 0 | 1 | 2 | 3 => rfl]
  exact congrFun (regsNS_eq y y tp i htp hi y [] (List.append_nil y).symm rfl) l

/-- The bit at the index, its meaning. -/
theorem sem_numHit (y : List Bool) (tp i : ℕ) (htp : tp ≤ y.length) (hi : i ≤ y.length) :
    numHit.sem ![y, y.drop tp, y.drop i] = boolWord (nrun tp i y).hit :=
  sem_numReg 5 y tp i htp hi

/-- The end position, its meaning. -/
theorem sem_numEnd (y : List Bool) (tp i : ℕ) (htp : tp ≤ y.length) (hi : i ≤ y.length) :
    numEnd.sem ![y, y.drop tp, y.drop i] = y.drop (nrun tp i y).endPos :=
  sem_numReg 7 y tp i htp hi

/-- The acceptance, its meaning: set when the scanner ended done and
canonical. -/
theorem sem_numOk (y : List Bool) (tp i : ℕ) (htp : tp ≤ y.length) (hi : i ≤ y.length) :
    numOk.sem ![y, y.drop tp, y.drop i] =
      boolWord (decide ((nrun tp i y).mode = .done) && (nrun tp i y).ok) := by
  rw [numOk, sem_cond4L, sem_isDoneN _ _ (nrun tp i y).mode (sem_numReg 1 y tp i htp hi),
    sem_numReg 6 y tp i htp hi, sem_constL]
  change cond4Sem _ [] (boolWord (nrun tp i y).ok) (boolWord (nrun tp i y).ok) = _
  by_cases hd : (nrun tp i y).mode = .done
  · rw [if_pos hd, decide_eq_true hd, Bool.true_and]
    cases (nrun tp i y).ok <;> rfl
  · rw [if_neg hd, decide_eq_false hd, Bool.false_and]
    rfl

/-- On a word holding a coded number at the position, the acceptance is set,
the end position is past the numeral, and the bit at the index is the
number's. -/
theorem num_natCode (u rest y : List Bool) (m tp i : ℕ) (hu : u.length = tp)
    (hy : y = u ++ natCode m ++ rest) (hi : i ≤ y.length) :
    numOk.sem ![y, y.drop tp, y.drop i] = [true] ∧
      numEnd.sem ![y, y.drop tp, y.drop i] = y.drop (tp + (natCode m).length) ∧
      numHit.sem ![y, y.drop tp, y.drop i] = boolWord (m.bits.getD i false) := by
  have htp : tp ≤ y.length := by
    rw [hy, List.length_append, List.length_append, hu]
    omega
  obtain ⟨hd, hok, he, hh⟩ := nrun_natCode tp i u rest y m hu hy
  rw [sem_numOk y tp i htp hi, sem_numEnd y tp i htp hi, sem_numHit y tp i htp hi, hd, hok, he, hh]
  exact ⟨rfl, rfl, rfl⟩

/-- When the acceptance is set, the word holds a coded number at the position,
the end position is past it, and the bit at the index is the number's. -/
theorem num_of_ok (y : List Bool) (tp i : ℕ) (htp : tp ≤ y.length) (hi : i ≤ y.length)
    (h : numOk.sem ![y, y.drop tp, y.drop i] = [true]) :
    ∃ m rest, y.drop tp = natCode m ++ rest ∧
      numEnd.sem ![y, y.drop tp, y.drop i] = y.drop (tp + (natCode m).length) ∧
      numHit.sem ![y, y.drop tp, y.drop i] = boolWord (m.bits.getD i false) := by
  rw [sem_numOk y tp i htp hi] at h
  have hd : (nrun tp i y).mode = .done := by
    by_contra hd
    rw [decide_eq_false hd, Bool.false_and] at h
    cases h
  have hok : (nrun tp i y).ok = true := by
    rw [decide_eq_true hd, Bool.true_and] at h
    cases hk : (nrun tp i y).ok
    · rw [hk] at h
      cases h
    · rfl
  obtain ⟨m, rest, hw, he, hh⟩ := nrun_done tp i y hd hok
  exact ⟨m, rest, hw, by rw [sem_numEnd y tp i htp hi, he], by rw [sem_numHit y tp i htp hi, hh]⟩

end

end Geb.SizeBounded.Logspace.WTree.NumExpr
