/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Combinators
public import Geb.Prototypes.Computability.BitTree.Encoding

set_option doc.verso true in
/-!
# The bit-tree recognizer in the non-size-increasing algebra

{name}`Geb.BitTree.validBool` — the left-to-right scan recognizing the encodings
of binary trees with bitstrings at the leaves, with a finite control and a
pending-tree counter — as an expression of {name}`Geb.SizeBounded.S`. The
expression is correct against the scan on every word, and it is
non-size-increasing by {name}`Geb.SizeBounded.nsi_eval` with no argument specific
to it: the polynomial-time, linear-space reading of its membership,
\[Mazzanti2016\] Theorem 5.7, is
{lit}`Geb.SizeBounded.Machine.computableInTimeAndSpace_sem`.

The scan is a simultaneous recursion with three registers, run over the input
word used as a counter, with the word itself as the parameter. The first
register holds the input not yet read, and is shortened by one bit per step;
the second holds the scanner's mode as a two-bit code, the dead mode being the
empty word; the third holds the pending-tree count minus one in unary. The
count is incremented by the size-bounded successor with the whole word as
bound, and never reaches the bound: the count minus one is at most the number
of bits read, and a bit remains to be read when it is incremented. The scan
therefore agrees with {name}`Geb.BitTree.scan` exactly, and the recognizer
accepts exactly when the final mode is {name}`Geb.BitTree.Mode.done`.

# Main definitions

* {lit}`modeCode` — the two-bit code of a scanner mode.
* {lit}`restVar`, {lit}`modeVar`, {lit}`countVar`, {lit}`wordVar` — the step
  environment's registers and parameter.
* {lit}`onMode`, {lit}`modeAfter`, {lit}`countAfter` — dispatch on the mode
  register, and the mode and count after reading a bit.
* {lit}`restStep`, {lit}`modeStep`, {lit}`countStep` — the three step
  expressions.
* {lit}`treeBase`, {lit}`treeStep`, {lit}`treeReg` — the recursion's bases and
  steps, and its three registers as expressions of arity two.
* {lit}`treeAccept`, {lit}`isBitTree` — the acceptance test on the mode
  register, and the recognizer of arity one.
* {lit}`onModeSem`, {lit}`modeAfterSem`, {lit}`countAfterSem`, {lit}`regs` —
  the meanings of the dispatch, of the two updates, and of the registers.

# Main statements

* {lit}`regs_nil`, {lit}`regs_cons` — the registers on the empty counter and
  after one more step.
* {lit}`modeAfterSem_code`, {lit}`countAfterSem_code` — the two updates
  compute {name}`Geb.BitTree.step` on the coded state.
* {lit}`regs_eq` — after reading a prefix, the registers hold the remaining
  word and the coded scanner state.
* {lit}`isBitTreeSem_eq` — the recognizer returns {lit}`[true]` on a word the
  scan accepts and the empty word on every other.
* {lit}`isBitTreeSem_eq_singleton_iff` — it accepts exactly the encodings of
  trees.
* {lit}`nsi_isBitTree`, {lit}`nsiConst_isBitTree` — it is non-size-increasing,
  with constant two.

# Implementation notes

The recursion variable is consumed from its head, so a recursion over the word
alone computes a right fold; the scan is a left fold. Running the recursion over
the word as a counter, with the word again as the parameter and the unread
input as a register, computes the left fold in one linear pass, each step
constant. Reading the current bit from the register rather than from the
parameter at a computed offset is what keeps the step constant.

The count register holds the count minus one so that its length never exceeds
the number of bits read: the count itself starts at one, and the initial word's
extra bit would exceed the bound at the last step of an all-fork word. On the
scanner's side that convention is {lit}`n - 1` with truncated subtraction, which
is zero in the two terminal modes, where the count is not read.

# References

* \[Mazzanti2016\]

# Tags

non-size-increasing, simultaneous recursion on notation, binary tree, bitstring,
recognizer, linear time
-/

set_option doc.verso true

namespace Geb.SizeBounded

open Geb.BitTree (Mode State step finish scan validBool Active)

public section

/-- The two-bit code of a scanner mode; the dead mode is the empty word. -/
@[expose] def modeCode : Mode → List Bool
  | .tree => [true, true]
  | .string => [true, false]
  | .bit => [false, true]
  | .done => [false, false]
  | .dead => []

/-- The unread input, slot one of the step environment. -/
@[expose] def restVar : SOf 5 := projOf 5 1

/-- The mode register, slot two of the step environment. -/
@[expose] def modeVar : SOf 5 := projOf 5 2

/-- The count register, slot three of the step environment. -/
@[expose] def countVar : SOf 5 := projOf 5 3

/-- The whole word, the parameter in slot four of the step environment. -/
@[expose] def wordVar : SOf 5 := projOf 5 4

/-- A mode's code as a constant of the step arity. -/
@[expose] def code5 (m : Mode) : SOf 5 := constOf 5 (modeCode m)

/-- Dispatch on the mode register: the empty code is the dead mode, and the two
bits of the other codes select among the four live modes. -/
@[expose] def onMode (tree string bit done dead : SOf 5) : SOf 5 :=
  cond4 modeVar dead (cond4 (tailApp modeVar) dead tree string)
    (cond4 (tailApp modeVar) dead bit done)

/-- The mode after reading the bit {lit}`b`, transcribing {name}`Geb.BitTree.step`:
in string mode a {lit}`false` bit finishes a leaf, which completes the scan when
the count register is empty. -/
@[expose] def modeAfter : Bool → SOf 5
  | true => onMode (code5 .tree) (code5 .bit) (code5 .string) (code5 .dead) (code5 .dead)
  | false =>
      onMode (code5 .string) (cond4 countVar (code5 .done) (code5 .tree) (code5 .tree))
        (code5 .string) (code5 .dead) (code5 .dead)

/-- The count register after reading the bit {lit}`b`: a fork increments it by
the size-bounded successor with the whole word as bound, a completed leaf
decrements it, and the other transitions keep it. -/
@[expose] def countAfter : Bool → SOf 5
  | true => onMode (sbsApp true countVar wordVar) countVar countVar countVar countVar
  | false => onMode countVar (tailApp countVar) countVar countVar countVar

/-- The unread input loses its head bit. -/
@[expose] def restStep : SOf 5 := tailApp restVar

/-- The mode step: the head bit of the unread input selects the update. -/
@[expose] def modeStep : SOf 5 := cond4 restVar modeVar (modeAfter true) (modeAfter false)

/-- The count step: the head bit of the unread input selects the update. -/
@[expose] def countStep : SOf 5 := cond4 restVar countVar (countAfter true) (countAfter false)

/-- The recursion's bases: the whole word, the code of the tree mode, and the
empty count. -/
@[expose] def treeBase : Fin 3 → SOf 1 :=
  ![projOf 1 0, constOf 1 (modeCode .tree), constOf 1 []]

/-- The recursion's steps, the same for either bit of the counter. -/
@[expose, nolint unusedArguments] def treeStep : Bool → Fin 3 → SOf 5 :=
  fun _ ↦ ![restStep, modeStep, countStep]

/-- The three registers of the scan, as expressions of arity two: the counter and
the word. -/
@[expose] def treeReg (l : Fin 3) : SOf 2 := srnOf treeBase treeStep l

/-- The acceptance test: {lit}`[true]` when the mode register holds the code of
the done mode, the empty word otherwise. -/
@[expose] def treeAccept : SOf 2 :=
  cond4 (treeReg 1) (constOf 2 []) (constOf 2 [])
    (cond4 (tailApp (treeReg 1)) (constOf 2 []) (constOf 2 []) (constOf 2 [true]))

/-- The recognizer: the acceptance test with the word as counter and parameter. -/
@[expose] def isBitTree : SOf 1 := diagOf treeAccept

/-- The meaning of {lit}`onMode`. -/
@[expose] def onModeSem (m tree string bit done dead : List Bool) : List Bool :=
  cond4Sem m dead (cond4Sem m.tail dead tree string) (cond4Sem m.tail dead bit done)

/-- The meaning of {lit}`modeAfter`. -/
@[expose] def modeAfterSem : Bool → List Bool → List Bool → List Bool
  | true, m, _ => onModeSem m (modeCode .tree) (modeCode .bit) (modeCode .string) [] []
  | false, m, c =>
      onModeSem m (modeCode .string) (cond4Sem c (modeCode .done) (modeCode .tree) (modeCode .tree))
        (modeCode .string) [] []

/-- The meaning of {lit}`countAfter`. -/
@[expose] def countAfterSem : Bool → List Bool → List Bool → List Bool → List Bool
  | true, m, c, y => onModeSem m (sbsSem true c y) c c c c
  | false, m, c, _ => onModeSem m c c.tail c c c

/-- The registers' meanings at a counter and a word. -/
@[expose] def regs (u y : List Bool) : Fin 3 → List Bool :=
  fun l ↦ (treeReg l).sem (Fin.cons u ![y])

/-- Slot one of a step environment is register zero. -/
theorem stepEnv_one (v : List Bool) (vals : Fin 3 → List Bool) (y : Fin 1 → List Bool) :
    stepEnv v vals y 1 = vals 0 := rfl

/-- Slot two of a step environment is register one. -/
theorem stepEnv_two (v : List Bool) (vals : Fin 3 → List Bool) (y : Fin 1 → List Bool) :
    stepEnv v vals y 2 = vals 1 := rfl

/-- Slot three of a step environment is register two. -/
theorem stepEnv_three (v : List Bool) (vals : Fin 3 → List Bool) (y : Fin 1 → List Bool) :
    stepEnv v vals y 3 = vals 2 := rfl

/-- Slot four of a step environment is the parameter. -/
theorem stepEnv_four (v : List Bool) (vals : Fin 3 → List Bool) (y : Fin 1 → List Bool) :
    stepEnv v vals y 4 = y 0 := rfl

/-- The dispatch computes {lit}`onModeSem`. -/
theorem sem_onMode (tree string bit done dead : SOf 5) (x : Fin 5 → List Bool) :
    (onMode tree string bit done dead).sem x =
      onModeSem (x 2) (tree.sem x) (string.sem x) (bit.sem x) (done.sem x) (dead.sem x) := by
  simp only [onMode, sem_cond4, sem_tailApp, modeVar, sem_projOf]
  rfl

/-- The mode update computes {lit}`modeAfterSem`. -/
theorem sem_modeAfter (b : Bool) (x : Fin 5 → List Bool) :
    (modeAfter b).sem x = modeAfterSem b (x 2) (x 3) := by
  cases b
  · simp only [modeAfter, sem_onMode, code5, sem_constOf, sem_cond4, countVar, sem_projOf]
    rfl
  · simp only [modeAfter, sem_onMode, code5, sem_constOf]
    rfl

/-- The count update computes {lit}`countAfterSem`. -/
theorem sem_countAfter (b : Bool) (x : Fin 5 → List Bool) :
    (countAfter b).sem x = countAfterSem b (x 2) (x 3) (x 4) := by
  cases b
  · simp only [countAfter, sem_onMode, sem_tailApp, countVar, sem_projOf]
    rfl
  · simp only [countAfter, sem_onMode, sem_sbsApp, countVar, wordVar, sem_projOf]
    rfl

/-- On the empty counter the registers hold the word, the tree code and the empty
count. -/
theorem regs_nil (y : List Bool) : regs [] y = ![y, modeCode .tree, []] :=
  funext fun l ↦ match l with | 0 | 1 | 2 => rfl

/-- One more counter bit runs the step of each register at the environment holding
the registers and the word. -/
theorem regs_cons_apply (i : Bool) (v y : List Bool) (l : Fin 3) :
    regs (i :: v) y l = (treeStep i l).sem (stepEnv v (regs v y) ![y]) :=
  sem_srnOf_cons treeBase treeStep l i v ![y]

/-- One more counter bit runs the three steps on the registers. -/
theorem regs_cons (i : Bool) (v y : List Bool) :
    regs (i :: v) y =
      ![(regs v y 0).tail,
        cond4Sem (regs v y 0) (regs v y 1) (modeAfterSem true (regs v y 1) (regs v y 2))
          (modeAfterSem false (regs v y 1) (regs v y 2)),
        cond4Sem (regs v y 0) (regs v y 2) (countAfterSem true (regs v y 1) (regs v y 2) y)
          (countAfterSem false (regs v y 1) (regs v y 2) y)] := by
  funext l
  rw [regs_cons_apply]
  match l with
  | 0 =>
    change restStep.sem (stepEnv v (regs v y) ![y]) = (regs v y 0).tail
    simp only [restStep, sem_tailApp, restVar, sem_projOf, stepEnv_one]
  | 1 =>
    change modeStep.sem (stepEnv v (regs v y) ![y]) =
      cond4Sem (regs v y 0) (regs v y 1) (modeAfterSem true (regs v y 1) (regs v y 2))
        (modeAfterSem false (regs v y 1) (regs v y 2))
    simp only [modeStep, sem_cond4, sem_modeAfter, restVar, modeVar, sem_projOf, stepEnv_one,
      stepEnv_two, stepEnv_three]
  | 2 =>
    change countStep.sem (stepEnv v (regs v y) ![y]) =
      cond4Sem (regs v y 0) (regs v y 2) (countAfterSem true (regs v y 1) (regs v y 2) y)
        (countAfterSem false (regs v y 1) (regs v y 2) y)
    simp only [countStep, sem_cond4, sem_countAfter, restVar, countVar, sem_projOf, stepEnv_one,
      stepEnv_two, stepEnv_three, stepEnv_four, Matrix.cons_val_zero]

/-- The mode update on a coded active state is the scanner's step. -/
theorem modeAfterSem_code (b : Bool) (m : Mode) (n : ℕ) (hA : Active (m, n)) :
    modeAfterSem b (modeCode m) (List.replicate (n - 1) true) = modeCode (step (m, n) b).1 := by
  cases m <;> cases b
  all_goals
    first
    | rfl
    | (match n with
       | 0 => exact absurd (hA (by simp)) (Nat.lt_irrefl 0)
       | 1 => rfl
       | _ + 2 => rfl)

/-- The count update on a coded active state is the scanner's step, provided the
count is bounded by the word: the increment is then within the bound. -/
theorem countAfterSem_code (b : Bool) (m : Mode) (n : ℕ) (y : List Bool)
    (hA : Active (m, n)) (hy : n ≤ y.length) :
    countAfterSem b (modeCode m) (List.replicate (n - 1) true) y =
      List.replicate ((step (m, n) b).2 - 1) true := by
  cases m <;> cases b
  case tree.true =>
    match n with
    | 0 => exact absurd (hA (by simp)) (Nat.lt_irrefl 0)
    | k + 1 =>
      change sbsSem true (List.replicate k true) y = List.replicate (k + 1) true
      unfold sbsSem
      split
      · rfl
      · exact absurd (show (List.replicate k true).length + 1 ≤ y.length by
          rw [List.length_replicate]; exact hy) ‹_›
  all_goals
    first
    | rfl
    | (match n with
       | 0 => exact absurd (hA (by simp)) (Nat.lt_irrefl 0)
       | 1 => rfl
       | _ + 2 => rfl)

/-- One step of the scanner raises the count by at most one. -/
theorem finish_snd_le (n : ℕ) : (finish n).2 ≤ n + 1 := by
  unfold finish
  split
  · exact Nat.zero_le _
  · exact Nat.le_trans (Nat.sub_le n 1) (Nat.le_succ n)

/-- One step of the scanner raises the count by at most one. -/
theorem step_snd_le (s : State) (b : Bool) : (step s b).2 ≤ s.2 + 1 := by
  rcases s with ⟨m, n⟩
  cases m <;> cases b
  case string.false => exact finish_snd_le n
  all_goals first | exact Nat.le_succ _ | exact Nat.le_refl _

/-- The scanner's count after a word is at most its initial count plus the word's
length. -/
theorem foldl_step_snd_le (p : List Bool) : ∀ s : State, (p.foldl step s).2 ≤ s.2 + p.length :=
  List.rec (fun _ ↦ Nat.le_refl _)
    (fun b _ ih s ↦ by
      rw [List.foldl_cons, List.length_cons]
      exact Nat.le_trans (ih (step s b)) (by have := step_snd_le s b; omega)) p

/-- After a prefix of the word is read, the registers hold the remaining word and
the coded scanner state on that prefix. -/
theorem regs_eq (y u : List Bool) : ∀ (p r : List Bool), y = p ++ r → p.length = u.length →
    regs u y = ![r, modeCode (p.foldl step (.tree, 1)).1,
      List.replicate ((p.foldl step (.tree, 1)).2 - 1) true] :=
  List.rec
    (motive := fun u ↦ ∀ (p r : List Bool), y = p ++ r → p.length = u.length →
      regs u y = ![r, modeCode (p.foldl step (.tree, 1)).1,
        List.replicate ((p.foldl step (.tree, 1)).2 - 1) true])
    (fun p r hy hp ↦ by
      have hp' : p = [] := List.eq_nil_of_length_eq_zero hp
      subst hp'
      subst hy
      exact regs_nil _)
    (fun i v ih p r hy hp ↦ by
      rcases List.eq_nil_or_concat p with hn | ⟨p', c, hc⟩
      · subst hn
        exact absurd hp.symm (Nat.succ_ne_zero v.length)
      · rw [List.concat_eq_append] at hc
        subst hc
        rw [List.length_append, List.length_singleton, List.length_cons] at hp
        rw [List.append_assoc, List.singleton_append] at hy
        rw [regs_cons, ih p' (c :: r) hy (by omega)]
        have hA : Active (p'.foldl step (.tree, 1)) :=
          Geb.BitTree.active_foldl p' (.tree, 1) (fun _ ↦ Nat.zero_lt_one)
        have hle := foldl_step_snd_le p' (.tree, 1)
        have hlen : p'.length + 1 ≤ y.length := by
          rw [hy, List.length_append, List.length_cons]
          omega
        rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
        rcases hs : p'.foldl step (.tree, 1) with ⟨m, n⟩
        rw [hs] at hA hle
        dsimp only at hle
        have hn : n ≤ y.length := by omega
        funext l
        match l with
        | 0 => rfl
        | 1 =>
          change cond4Sem (c :: r) (modeCode m)
            (modeAfterSem true (modeCode m) (List.replicate (n - 1) true))
            (modeAfterSem false (modeCode m) (List.replicate (n - 1) true)) =
            modeCode (step (m, n) c).1
          cases c
          · exact modeAfterSem_code false m n hA
          · exact modeAfterSem_code true m n hA
        | 2 =>
          change cond4Sem (c :: r) (List.replicate (n - 1) true)
            (countAfterSem true (modeCode m) (List.replicate (n - 1) true) y)
            (countAfterSem false (modeCode m) (List.replicate (n - 1) true) y) =
            List.replicate ((step (m, n) c).2 - 1) true
          cases c
          · exact countAfterSem_code false m n y hA hn
          · exact countAfterSem_code true m n y hA hn) u

/-- The recognizer returns {lit}`[true]` on a word the scan accepts and the empty
word on every other. -/
theorem isBitTreeSem_eq (y : List Bool) :
    isBitTree.sem ![y] = if (scan y).1 = .done then [true] else [] := by
  rw [isBitTree, sem_diagOf]
  have h := regs_eq y y y [] (List.append_nil y).symm rfl
  have h1 : (treeReg 1).sem ![y, y] = modeCode (scan y).1 := congrFun h 1
  simp only [treeAccept, sem_cond4, sem_tailApp, sem_constOf, h1]
  generalize (scan y).1 = m
  cases m <;> rfl

/-- The recognizer accepts exactly the words the scanner accepts. -/
theorem isBitTreeSem_eq_singleton_iff_validBool (y : List Bool) :
    isBitTree.sem ![y] = [true] ↔ validBool y = true := by
  rw [isBitTreeSem_eq, validBool]
  constructor
  · intro h
    split at h
    · exact decide_eq_true ‹_›
    · exact absurd h (by simp)
  · intro h
    split
    · rfl
    · exact absurd (of_decide_eq_true h) ‹_›

/-- The recognizer accepts exactly the encodings of trees. -/
theorem isBitTreeSem_eq_singleton_iff (y : List Bool) :
    isBitTree.sem ![y] = [true] ↔ ∃ t, Geb.BitTree.encode t = y :=
  (isBitTreeSem_eq_singleton_iff_validBool y).trans (Geb.BitTree.validBool_iff y)

/-- The recognizer is non-size-increasing, by the algebra's closure theorem
alone. -/
theorem nsi_isBitTree : NSI (nsiConst isBitTree.1.1) isBitTree.sem := nsi_sem isBitTree

/-- The recognizer's constant is two: the longest constant in it is a mode
code. -/
theorem nsiConst_isBitTree : nsiConst isBitTree.1.1 = 2 := by decide

end

end Geb.SizeBounded
