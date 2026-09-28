/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.ExprBase
public import Geb.Prototypes.Computability.SizeBounded.Logspace.EliasTree.Correct
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Nodes

set_option doc.verso true in
/-!
# The scan over the nodes as a successor-free expression

The scan over the nodes of an encoded tree,
{name}`Geb.SizeBounded.Logspace.WTree.nodeScan`, as an expression of the
logspace subalgebra: a simultaneous recursion over the word with nine
registers, the seven of the Elias-length tree recognizer and two more, the
fork count as the word dropped by it and the flag as a word, run over the
word as the counter with the word as the parameter. The check at a node is a
parameter of the expression, of arity four: the word, the remaining word
from the label's first payload bit, the word dropped by one more than the
label's length, and the word dropped by the node's arity. The expression
computes the scan whose check is the expression's, read as a flag.

# Main definitions

* {lit}`emb`, {lit}`lift` — the Elias step's slots among the scan's, and an
  Elias step at the scan's arity.
* {lit}`restV`, {lit}`modeV`, {lit}`widthV`, {lit}`countV`, {lit}`valueV`,
  {lit}`kV`, {lit}`okV`, {lit}`wordV` — the registers and the parameter of
  the step environment.
* {lit}`fieldEndV`, {lit}`lenAfterHeader` — the field-end test and the
  length counter a completed header yields.
* {lit}`andOk`, {lit}`checkAt` — the conjunction with the flag register, and
  the check applied.
* {lit}`kStep`, {lit}`okStep`, {lit}`nodeBase`, {lit}`nodeStep`,
  {lit}`nodeReg` — the two new steps, the recursion's bases and steps, and
  its registers.
* {lit}`accept`, {lit}`nodeScanExpr` — the acceptance test and the scan as
  an expression of arity one.
* {lit}`checkB` — the check an expression defines.
* {lit}`encodeN`, {lit}`stepAtN` — the registers holding a remaining word,
  counters, a fork count and a flag, and the step environment holding them.

# Main statements

* {lit}`elias_step`, {lit}`k_step`, {lit}`ok_step`, {lit}`step_encodeN` —
  each register's step on the encoded state is the encoded step of the
  state.
* {lit}`regsN_eq` — after a prefix, the registers hold the remaining word and
  the encoded state on the prefix.
* {lit}`nodeScanExprSem_eq` — the expression's value: {lit}`[true]` when the
  word encodes a tree and the scan accepts, the empty word otherwise.

# References

* \[Kristiansen2005\]

# Tags

logspace, simultaneous recursion on notation, W-type, recognizer
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree.NodeExpr

open Geb.BitTree.Elias.Scanner (Mode State step finish scan)
open EliasTree (Phase Counters Valid advance init phaseCode)

public section

/-- The Elias step's slots among the scan's: the level, the seven registers,
and the word, which the scan holds after its two further registers. -/
@[expose] def emb : Fin 9 → Fin 11 := ![0, 1, 2, 3, 4, 5, 6, 7, 10]

/-- An Elias step at the scan's arity. -/
@[expose] def lift (e : LOf 9) : LOf 11 := liftBy emb e

/-- The unread input, slot one. -/
@[expose] def restV : LOf 11 := projL 11 1

/-- The phase register, slot two. -/
@[expose] def modeV : LOf 11 := projL 11 2

/-- The width, slot five. -/
@[expose] def widthV : LOf 11 := projL 11 5

/-- The count, slot six. -/
@[expose] def countV : LOf 11 := projL 11 6

/-- The value, slot seven. -/
@[expose] def valueV : LOf 11 := projL 11 7

/-- The fork count, slot eight. -/
@[expose] def kV : LOf 11 := projL 11 8

/-- The flag, slot nine. -/
@[expose] def okV : LOf 11 := projL 11 9

/-- The word, the parameter in slot ten. -/
@[expose] def wordV : LOf 11 := projL 11 10

/-- The field-end test, as {name}`Geb.SizeBounded.Logspace.EliasTree.fieldEnd`
at the scan's arity. -/
@[expose] def fieldEndV : LOf 11 := dropByApp widthV (tailAppL countV)

/-- The length counter a completed length field yields. -/
@[expose] def lenAfterHeader : LOf 11 := lenAfterHeaderAt restV valueV wordV

/-- The conjunction of the flag register with a flag. -/
@[expose] def andOk (e : LOf 11) : LOf 11 := andOkAt okV e

/-- The check applied to the word, the remaining word past the current bit,
a length counter and the fork count. -/
@[expose] def checkAt (check : LOf 4) (len : LOf 11) : LOf 11 :=
  compL check ![wordV, tailAppL restV, len, kV]

/-- The fork count's step: a fork tag raises it, a completed leaf resets it. -/
@[expose] def kStep : LOf 11 :=
  eventStep modeV restV fieldEndV (tailAppL kV) kV wordV kV wordV kV

/-- The flag's step: a completed header conjoins the check, with the length
counter the header yields. -/
@[expose] def okStep (check : LOf 4) : LOf 11 :=
  eventStep modeV restV fieldEndV okV okV
    (andOk (flagOf (checkAt check (tailAppL wordV))))
    (andOk (flagOf (checkAt check lenAfterHeader))) okV okV

/-- The recursion's bases: the Elias bases, the word for the fork count at
zero, and the flag set. -/
@[expose] def nodeBase : Fin 9 → LOf 1 :=
  Fin.append EliasTree.treeBase ![projL 1 0, constL 1 [true]]

/-- The recursion's steps: the Elias steps lifted, and the two new steps. -/
@[expose] def nodeStep (check : LOf 4) : Bool → Fin 9 → LOf 11 :=
  fun i ↦ Fin.append (fun l ↦ lift (EliasTree.treeStep i l)) ![kStep, okStep check]

/-- The nine registers, as expressions of arity two: the counter and the
word. -/
@[expose] def nodeReg (check : LOf 4) (l : Fin 9) : LOf 2 := srnL nodeBase (nodeStep check) l

/-- The acceptance test: the flag register when the phase register holds the
code of the completed phase, the empty word otherwise. -/
@[expose] def accept (check : LOf 4) : LOf 2 :=
  cond4L (isDone (nodeReg check 1)) (constL 2 []) (nodeReg check 8) (constL 2 [])

/-- The scan as an expression of arity one: the acceptance test with the word
as counter and parameter. -/
@[expose] def nodeScanExpr (check : LOf 4) : LOf 1 := diagL (accept check)

/-- The check an expression of arity four defines on a word: its value read
as a flag, at the word, the remaining word from the label's first payload bit,
the word dropped by one more than the label's length, and the word dropped by
the node's arity. -/
@[expose] def checkB (check : LOf 4) (y : List Bool) (l : Loc) (k : ℕ) : Bool :=
  isTrueWord (check.sem ![y, y.drop l.pos, y.drop (l.len + 1), y.drop k])

/-- The registers holding a remaining word, counters, a fork count and a flag. -/
@[expose] def encodeN (y r : List Bool) (x : Counters) (k : ℕ) (ok : Bool) : Fin 9 → List Bool :=
  Fin.append (EliasTree.encode y r x) ![y.drop k, boolWord ok]

/-- The step environment at a level, holding the registers and the word. -/
@[expose] def stepAtN (u y r : List Bool) (x : Counters) (k : ℕ) (ok : Bool) :
    Fin 11 → List Bool :=
  stepEnv u (encodeN y r x k ok) ![y]

/-- The Elias slots of the step environment are the Elias step environment. -/
theorem stepAtN_emb (u y r : List Bool) (x : Counters) (k : ℕ) (ok : Bool) :
    stepAtN u y r x k ok ∘ emb = EliasTree.stepAt u y r x :=
  funext fun i ↦ match i with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl

/-- Slot one is the remaining word. -/
theorem stepAtN_one (u y r : List Bool) (x : Counters) (k : ℕ) (ok : Bool) :
    stepAtN u y r x k ok 1 = r := rfl

/-- Slot two is the phase code. -/
theorem stepAtN_two (u y r : List Bool) (x : Counters) (k : ℕ) (ok : Bool) :
    stepAtN u y r x k ok 2 = phaseCode x.phase := rfl

/-- Slot five is the width. -/
theorem stepAtN_five (u y r : List Bool) (x : Counters) (k : ℕ) (ok : Bool) :
    stepAtN u y r x k ok 5 = y.drop x.width := rfl

/-- Slot six is the count. -/
theorem stepAtN_six (u y r : List Bool) (x : Counters) (k : ℕ) (ok : Bool) :
    stepAtN u y r x k ok 6 = y.drop x.count := rfl

/-- Slot seven is the value. -/
theorem stepAtN_seven (u y r : List Bool) (x : Counters) (k : ℕ) (ok : Bool) :
    stepAtN u y r x k ok 7 = y.drop x.value := rfl

/-- Slot eight is the fork count. -/
theorem stepAtN_eight (u y r : List Bool) (x : Counters) (k : ℕ) (ok : Bool) :
    stepAtN u y r x k ok 8 = y.drop k := rfl

/-- Slot nine is the flag. -/
theorem stepAtN_nine (u y r : List Bool) (x : Counters) (k : ℕ) (ok : Bool) :
    stepAtN u y r x k ok 9 = boolWord ok := rfl

/-- Slot ten is the word. -/
theorem stepAtN_ten (u y r : List Bool) (x : Counters) (k : ℕ) (ok : Bool) :
    stepAtN u y r x k ok 10 = y := rfl

/-- The remaining-input register's meaning. -/
theorem sem_restV (u y r : List Bool) (x : Counters) (k : ℕ) (ok : Bool) :
    restV.sem (stepAtN u y r x k ok) = r := rfl

/-- The phase register's meaning. -/
theorem sem_modeV (u y r : List Bool) (x : Counters) (k : ℕ) (ok : Bool) :
    modeV.sem (stepAtN u y r x k ok) = phaseCode x.phase := rfl

/-- An Elias register's step on the encoded state is the encoded step of the
counters. -/
theorem elias_step (u y r : List Bool) (c : Bool) (x : Counters) (k₀ : ℕ) (hv : Valid k₀ x)
    (hk : k₀ < y.length) (k : ℕ) (ok : Bool) (i : Bool) (l : Fin 7) :
    (lift (EliasTree.treeStep i l)).sem (stepAtN u y (c :: r) x k ok) =
      EliasTree.encode y r (advance x c) l := by
  rw [lift, sem_liftBy, stepAtN_emb]
  exact EliasTree.step_encode u y r c x k₀ hv hk i l

/-- The field-end test's meaning. -/
theorem sem_fieldEndV (u y r : List Bool) (x : Counters) (k : ℕ) (ok : Bool) :
    fieldEndV.sem (stepAtN u y r x k ok) = (y.drop x.count).tail.drop (y.drop x.width).length := by
  simp only [fieldEndV, sem_dropByApp, sem_tailAppL, widthV, countV, sem_projL, stepAtN_five,
    stepAtN_six]

/-- The fork count's step on the encoded state is the encoded step of the
count. -/
theorem k_step (u y r : List Bool) (c : Bool) (x : Counters) (k₀ : ℕ) (hv : Valid k₀ x)
    (hk : k₀ < y.length) (k : ℕ) (ok : Bool) (check : Loc → ℕ → Bool) (pos : ℕ) :
    kStep.sem (stepAtN u y (c :: r) x k ok) =
      y.drop (nodeUpd check pos (eventC x c) ⟨k, ok⟩).k := by
  rw [kStep, sem_eventStep _ _ _ _ _ _ _ _ _ _ y r c x k₀ hv hk (sem_modeV _ _ _ _ _ _)
    (sem_restV _ _ _ _ _ _) (sem_fieldEndV _ _ _ _ _ _)]
  rcases eventC_cases x c with h | h | h | ⟨L, h⟩ | h | h <;> rw [h] <;>
    simp only [eventValue, nodeUpd, Event.silent, ↓reduceIte, Bool.false_eq_true, sem_tailAppL,
      kV, wordV, sem_projL, stepAtN_eight, stepAtN_ten, List.tail_drop, List.drop_zero]

/-- The check applied, on the encoded state. -/
theorem sem_checkAt (check : LOf 4) (len : LOf 11) (u y r : List Bool) (c : Bool) (x : Counters)
    (k : ℕ) (ok : Bool) :
    (checkAt check len).sem (stepAtN u y (c :: r) x k ok) =
      check.sem ![y, r, len.sem (stepAtN u y (c :: r) x k ok), y.drop k] := by
  rw [checkAt, sem_compL]
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 =>
    change (tailAppL restV).sem _ = r
    rw [sem_tailAppL, sem_restV]
    rfl
  | 2 => rfl
  | 3 => rfl

/-- The length counter a completed header yields, on the encoded state. -/
theorem sem_lenAfterHeader (u y r : List Bool) (c : Bool) (x : Counters) (k : ℕ) (ok : Bool) :
    lenAfterHeader.sem (stepAtN u y (c :: r) x k ok) = y.drop (2 * x.value + c.toNat) :=
  sem_lenAfterHeaderAt restV valueV wordV (stepAtN u y (c :: r) x k ok) y r c x.value
    (sem_restV u y (c :: r) x k ok) (stepAtN_seven u y (c :: r) x k ok)
    (stepAtN_ten u y (c :: r) x k ok)

/-- The flag's step on the encoded state is the encoded step of the flag, the
check being the expression's. -/
theorem ok_step (p u y r : List Bool) (c : Bool) (x : Counters) (k₀ : ℕ) (hv : Valid k₀ x)
    (hk : k₀ < y.length) (k : ℕ) (ok : Bool) (check : LOf 4) (hy : y = p ++ c :: r) :
    (okStep check).sem (stepAtN u y (c :: r) x k ok) =
      boolWord (nodeUpd (checkB check y) p.length (eventC x c) ⟨k, ok⟩).ok := by
  have hr : y.drop (p.length + 1) = r := by
    rw [hy, ← List.drop_drop, List.drop_left, List.drop_one]
    rfl
  rw [okStep, sem_eventStep _ _ _ _ _ _ _ _ _ _ y r c x k₀ hv hk (sem_modeV _ _ _ _ _ _)
    (sem_restV _ _ _ _ _ _) (sem_fieldEndV _ _ _ _ _ _)]
  rcases eventC_cases x c with h | h | h | ⟨L, h⟩ | h | h
  · rw [h]
    simp only [eventValue, nodeUpd, ↓reduceIte, okV, sem_projL, stepAtN_nine]
  · rw [h]
    simp only [eventValue, nodeUpd, ↓reduceIte, Bool.false_eq_true, okV, sem_projL, stepAtN_nine]
  · rw [h]
    simp only [eventValue, nodeUpd, ↓reduceIte, Bool.false_eq_true, andOk, andOkAt, sem_cond4L,
      okV, sem_projL, stepAtN_nine, sem_constL, sem_flagOf, sem_checkAt, sem_tailAppL, wordV,
      stepAtN_ten, checkB, hr, Nat.zero_add, List.drop_one, cond4Sem_boolWord]
  · have hL := eventC_payload_of_not_done k₀ x c L hv (by rw [h]) (by rw [h])
    rw [h]
    simp only [eventValue, nodeUpd, ↓reduceIte, Bool.false_eq_true, andOk, andOkAt, sem_cond4L,
      okV, sem_projL, stepAtN_nine, sem_constL, sem_flagOf, sem_checkAt, sem_lenAfterHeader, checkB,
      hr, hL, cond4Sem_boolWord]
  · rw [h]
    simp only [eventValue, nodeUpd, ↓reduceIte, Bool.false_eq_true, okV, sem_projL, stepAtN_nine]
  · rw [h]
    simp only [eventValue, nodeUpd, Event.silent, ↓reduceIte, Bool.false_eq_true, okV, sem_projL,
      stepAtN_nine]

/-- One step on the encoded state is the encoded step of the state. -/
theorem step_encodeN (check : LOf 4) (p u y r : List Bool) (c : Bool) (x : Counters) (k₀ : ℕ)
    (hv : Valid k₀ x) (hk : k₀ < y.length) (k : ℕ) (ok : Bool) (hy : y = p ++ c :: r) (i : Bool)
    (l : Fin 9) :
    (nodeStep check i l).sem (stepAtN u y (c :: r) x k ok) =
      encodeN y r (advance x c) (nodeUpd (checkB check y) p.length (eventC x c) ⟨k, ok⟩).k
        (nodeUpd (checkB check y) p.length (eventC x c) ⟨k, ok⟩).ok l :=
  match l with
  | 0 => elias_step u y r c x k₀ hv hk k ok i 0
  | 1 => elias_step u y r c x k₀ hv hk k ok i 1
  | 2 => elias_step u y r c x k₀ hv hk k ok i 2
  | 3 => elias_step u y r c x k₀ hv hk k ok i 3
  | 4 => elias_step u y r c x k₀ hv hk k ok i 4
  | 5 => elias_step u y r c x k₀ hv hk k ok i 5
  | 6 => elias_step u y r c x k₀ hv hk k ok i 6
  | 7 => k_step u y r c x k₀ hv hk k ok (checkB check y) p.length
  | 8 => ok_step p u y r c x k₀ hv hk k ok check hy

/-- The registers' meanings at a counter and a word. -/
@[expose] def regsN (check : LOf 4) (u y : List Bool) : Fin 9 → List Bool :=
  fun l ↦ (nodeReg check l).sem (Fin.cons u ![y])

/-- On the empty counter the registers hold the word, the tree code, the word
for each counter, the word for the fork count, and the flag set. -/
theorem regsN_nil (check : LOf 4) (y : List Bool) : regsN check [] y = encodeN y y init 0 true :=
  funext fun l ↦ match l with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl

/-- One more counter bit runs the step of each register at the environment
holding the registers and the word. -/
theorem regsN_cons (check : LOf 4) (i : Bool) (v y : List Bool) (l : Fin 9) :
    regsN check (i :: v) y l = (nodeStep check i l).sem (stepEnv v (regsN check v y) ![y]) :=
  sem_srnL_cons nodeBase (nodeStep check) l i v ![y]

/-- The extended fold of the scan's registers on the counters. -/
@[expose] def foldN (check : LOf 4) (y p : List Bool) : ExtC NodeReg :=
  p.foldl (extStepC (nodeUpd (checkB check y))) ⟨init, 0, ⟨0, true⟩⟩

/-- The fold over one more bit. -/
theorem foldN_concat (check : LOf 4) (y p : List Bool) (c : Bool) :
    foldN check y (p ++ [c]) = extStepC (nodeUpd (checkB check y)) (foldN check y p) c := by
  unfold foldN
  rw [List.foldl_concat]

/-- After a prefix of the word is read, the registers hold the remaining word
and the encoded state on that prefix. -/
theorem regsN_eq (check : LOf 4) (y u : List Bool) :
    ∀ (p r : List Bool), y = p ++ r → p.length = u.length →
      regsN check u y =
        encodeN y r (foldN check y p).counters (foldN check y p).extra.k
          (foldN check y p).extra.ok :=
  List.rec
    (motive := fun u ↦ ∀ (p r : List Bool), y = p ++ r → p.length = u.length →
      regsN check u y =
        encodeN y r (foldN check y p).counters (foldN check y p).extra.k (foldN check y p).extra.ok)
    (fun p r hy hp ↦ by
      have hp' : p = [] := List.eq_nil_of_length_eq_zero hp
      subst hp'
      subst hy
      exact regsN_nil check _)
    (fun i v ih p r hy hp ↦ by
      rcases List.eq_nil_or_concat p with hn | ⟨p', c, hc⟩
      · subst hn
        exact absurd hp.symm (Nat.succ_ne_zero v.length)
      · rw [List.concat_eq_append] at hc
        subst hc
        rw [List.length_append, List.length_singleton, List.length_cons] at hp
        rw [List.append_assoc, List.singleton_append] at hy
        have hv := (foldl_extStepC_toExt (nodeUpd (checkB check y)) p' 0 ⟨init, 0, ⟨0, true⟩⟩
          EliasTree.valid_init).1
        rw [Nat.zero_add] at hv
        have hk : p'.length < y.length := by
          rw [hy, List.length_append, List.length_cons]
          omega
        have hpos : (foldN check y p').pos = p'.length := by
          rw [foldN, foldl_extStepC_pos]
          exact Nat.zero_add _
        funext l
        rw [regsN_cons, ih p' (c :: r) hy (by omega), foldN_concat]
        change (nodeStep check i l).sem (stepAtN v y (c :: r) _ _ _) =
          encodeN y r (advance _ c) (nodeUpd (checkB check y) (foldN check y p').pos _ _).k
            (nodeUpd (checkB check y) (foldN check y p').pos _ _).ok l
        rw [hpos]
        exact step_encodeN check p' v y r c _ _ hv hk _ _ hy i l) u

/-- The expression's value: {lit}`[true]` when the word encodes a tree and the
scan with the expression's check accepts, the empty word otherwise. -/
theorem nodeScanExprSem_eq (check : LOf 4) (y : List Bool) :
    (nodeScanExpr check).sem ![y] =
      if (scan y).1 = .done ∧ (nodeScan (checkB check y) y).extra.ok = true then [true]
      else [] := by
  rw [nodeScanExpr, sem_diagL, accept, sem_cond4L]
  have h := regsN_eq check y y y [] (List.append_nil y).symm rfl
  have h1 : (nodeReg check 1).sem ![y, y] = phaseCode (foldN check y y).counters.phase :=
    congrFun h 1
  have h8 : (nodeReg check 8).sem ![y, y] = boolWord (foldN check y y).extra.ok := congrFun h 8
  have hc : (foldN check y y).counters = EliasTree.run y := by
    rw [foldN, foldl_extStepC_counters]
    rfl
  have he : (foldN check y y).extra = (nodeScan (checkB check y) y).extra := by
    have := (foldl_extStepC_toExt (nodeUpd (checkB check y)) y 0 ⟨init, 0, ⟨0, true⟩⟩
      EliasTree.valid_init).2
    exact congrArg Ext.extra this
  rw [sem_isDone _ _ _ h1, h8, sem_constL, hc, he]
  simp only [EliasTree.run_phase_done_iff]
  by_cases hd : (scan y).1 = .done
  · rw [if_pos hd]
    cases (nodeScan (checkB check y) y).extra.ok
    · rw [if_neg (fun h ↦ absurd h.2 (by decide))]
      rfl
    · rw [if_pos ⟨hd, rfl⟩]
      rfl
  · rw [if_neg hd, if_neg (fun h ↦ hd h.1)]
    rfl

end

end Geb.SizeBounded.Logspace.WTree.NodeExpr
