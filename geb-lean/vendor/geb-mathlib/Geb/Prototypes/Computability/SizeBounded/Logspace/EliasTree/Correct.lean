/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.EliasTree.Expr
public import Geb.Prototypes.Computability.BitTree.Elias.ScannerCorrect

set_option doc.verso true in
/-!
# Correctness of the successor-free Elias-length tree recognizer

The registers of {name}`Geb.SizeBounded.Logspace.EliasTree.treeReg`, after a
prefix of the word has been read, hold the remaining word and the counters of
{name}`Geb.SizeBounded.Logspace.EliasTree.advance` on that prefix, each as the
word dropped by its number; and the recognizer
{name}`Geb.SizeBounded.Logspace.EliasTree.isEliasTree` returns {lit}`[true]`
on a word the streaming scanner accepts and the empty word on every other,
so it accepts exactly the encodings of trees. Each step of a register agrees
with the counters' step at every prefix short of the whole word, which is
where the invariant {name}`Geb.SizeBounded.Logspace.EliasTree.Valid` places
every compared counter below the word's length, so that a comparison of end
segments is a comparison of numbers.

# Main definitions

* {lit}`regs` — the registers' meanings at a counter and a word.

# Main statements

* {lit}`regs_nil`, {lit}`regs_cons` — the registers on the empty counter and
  after one more step.
* {lit}`rest_step`, {lit}`mode_step`, {lit}`forks_step`, {lit}`leaves_step`,
  {lit}`width_step`, {lit}`count_step`, {lit}`value_step` — each register's
  step on the encoded counters is the encoded step of the counters.
* {lit}`regs_eq` — after a prefix, the registers hold the remaining word and
  the encoded counters on the prefix.
* {lit}`isEliasTreeSem_eq`, {lit}`isEliasTreeSem_eq_validBool` — the
  recognizer's value on both kinds of word, against the scanner and against
  the decoder.
* {lit}`isEliasTreeSem_eq_singleton_iff_validBool`,
  {lit}`isEliasTreeSem_eq_singleton_iff` — it accepts exactly the words the
  recognizer accepts, the encodings of trees.

# References

* \[Kristiansen2005\]
* \[Elias1975\]

# Tags

logspace, simultaneous recursion on notation, Elias delta code, binary tree,
recognizer, correctness
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.EliasTree

open Geb.BitTree.Elias.Scanner (scan)

public section

/-- The registers' meanings at a counter and a word. -/
@[expose] def regs (u y : List Bool) : Fin 7 → List Bool :=
  fun l ↦ (treeReg l).sem (Fin.cons u ![y])

/-- On the empty counter the registers hold the word, the tree code and the
word for each counter. -/
theorem regs_nil (y : List Bool) : regs [] y = encode y y init :=
  funext fun l ↦ match l with | 0 | 1 | 2 | 3 | 4 | 5 | 6 => rfl

/-- One more counter bit runs the step of each register at the environment
holding the registers and the word. -/
theorem regs_cons (i : Bool) (v y : List Bool) (l : Fin 7) :
    regs (i :: v) y l = (treeStep i l).sem (stepEnv v (regs v y) ![y]) :=
  sem_srnL_cons treeBase treeStep l i v ![y]

/-- The dispatch on the phase register of a step environment selects the
expression of the counters' phase. -/
theorem sem_onPhase_stepAt (tree header zeros size length payload done dead : LOf 9)
    (u y r : List Bool) (x : Counters) :
    (onPhase tree header zeros size length payload done dead).sem (stepAt u y r x) =
      (match x.phase with
        | .tree => tree
        | .header => header
        | .zeros => zeros
        | .size => size
        | .length => length
        | .payload => payload
        | .done => done
        | .dead => dead).sem (stepAt u y r x) :=
  sem_onPhase _ _ _ _ _ _ _ _ _ x.phase rfl

/-- The dispatch on the current bit of a step environment selects by that
bit. -/
theorem sem_onBit_stepAt (e t f : LOf 9) (u y r : List Bool) (b : Bool) (x : Counters) :
    (onBit e t f).sem (stepAt u y (b :: r) x) = (if b then t else f).sem (stepAt u y (b :: r) x) :=
  sem_onBit e t f _ b r rfl

section StepLemmas

/-- The evaluation of a register step on a step environment: the dispatches,
the comparisons, the variables and the slots, with the reductions of the
literal codes, the conditionals and the counters. -/
local macro "eval_step" : tactic =>
    `(tactic| simp only [sem_onPhase_stepAt, sem_onBit_stepAt, sem_cond4L, sem_fieldEnd,
        sem_rootEnd, sem_tailAppL, sem_bitApp, sem_constL, sem_projL, code9, finishMode, bitValue,
        restVar, modeVar, forksVar, leavesVar, widthVar, countVar, valueVar, wordVar, stepAt_one,
        stepAt_two, stepAt_three, stepAt_four, stepAt_five, stepAt_six, stepAt_seven, stepAt_eight,
        cond4Sem_same, List.tail_drop, List.drop_one, List.drop_zero, bitSem_drop, advance, finishC,
        phaseCode, modeStep, forksStep, leavesStep, widthStep, countStep, valueStep,
        drop_drop_length_eq_nil_iff, ↓reduceIte, eq_self_iff_true, Nat.le_refl, Bool.false_eq_true,
        Bool.toNat_false, Bool.toNat_true, Nat.add_zero, *])

/-- The unread-input step drops the current bit. -/
theorem rest_step (u y r : List Bool) (c : Bool) (x : Counters) :
    (tailAppL restVar).sem (stepAt u y (c :: r) x) = r := by
  rw [sem_tailAppL, restVar, sem_projL, stepAt_one]
  rfl

/-- The phase step is the counters' phase step, encoded. -/
theorem mode_step (u y r : List Bool) (c : Bool) (x : Counters) (k : ℕ) (hv : Valid k x)
    (hk : k < y.length) : modeStep.sem (stepAt u y (c :: r) x) = phaseCode (advance x c).phase := by
  rcases x with ⟨ph, f, l, z, cnt, v⟩
  cases ph <;> cases c <;> simp only [Valid] at hv <;>
    by_cases he : cnt + 1 = z <;> by_cases hf : f = l <;>
    (try have hb : cnt + 1 < y.length := by omega) <;>
    (try have hb' : z < y.length := by omega) <;>
    (try have hl : l < y.length := by omega) <;>
    (try have hle : z ≤ cnt + 1 := by omega) <;>
    (try have hnle : ¬z ≤ cnt + 1 := by omega) <;>
    (try have hfl : f ≤ l := by omega) <;>
    (try have hnfl : ¬f ≤ l := by omega) <;>
    eval_step

/-- The forks step is the counters' forks step, encoded. -/
theorem forks_step (u y r : List Bool) (c : Bool) (x : Counters) (k : ℕ) (hv : Valid k x)
    (hk : k < y.length) : forksStep.sem (stepAt u y (c :: r) x) = y.drop (advance x c).forks := by
  rcases x with ⟨ph, f, l, z, cnt, v⟩
  cases ph <;> cases c <;> simp only [Valid] at hv <;>
    by_cases he : cnt + 1 = z <;> by_cases hf : f = l <;>
    (try have hb : cnt + 1 < y.length := by omega) <;>
    (try have hb' : z < y.length := by omega) <;>
    (try have hl : l < y.length := by omega) <;>
    (try have hle : z ≤ cnt + 1 := by omega) <;>
    (try have hnle : ¬z ≤ cnt + 1 := by omega) <;>
    (try have hfl : f ≤ l := by omega) <;>
    (try have hnfl : ¬f ≤ l := by omega) <;>
    eval_step

/-- The leaves step is the counters' leaves step, encoded. -/
theorem leaves_step (u y r : List Bool) (c : Bool) (x : Counters) (k : ℕ) (hv : Valid k x)
    (hk : k < y.length) :
    leavesStep.sem (stepAt u y (c :: r) x) = y.drop (advance x c).leaves := by
  rcases x with ⟨ph, f, l, z, cnt, v⟩
  cases ph <;> cases c <;> simp only [Valid] at hv <;>
    by_cases he : cnt + 1 = z <;> by_cases hf : f = l <;>
    (try have hb : cnt + 1 < y.length := by omega) <;>
    (try have hb' : z < y.length := by omega) <;>
    (try have hl : l < y.length := by omega) <;>
    (try have hle : z ≤ cnt + 1 := by omega) <;>
    (try have hnle : ¬z ≤ cnt + 1 := by omega) <;>
    (try have hfl : f ≤ l := by omega) <;>
    (try have hnfl : ¬f ≤ l := by omega) <;>
    eval_step

/-- The width step is the counters' width step, encoded. -/
theorem width_step (u y r : List Bool) (c : Bool) (x : Counters) (k : ℕ) (hv : Valid k x)
    (hk : k < y.length) : widthStep.sem (stepAt u y (c :: r) x) = y.drop (advance x c).width := by
  rcases x with ⟨ph, f, l, z, cnt, v⟩
  cases ph <;> cases c <;> simp only [Valid] at hv <;>
    by_cases he : cnt + 1 = z <;> by_cases hf : f = l <;>
    (try have hb : cnt + 1 < y.length := by omega) <;>
    (try have hb' : z < y.length := by omega) <;>
    (try have hl : l < y.length := by omega) <;>
    (try have hle : z ≤ cnt + 1 := by omega) <;>
    (try have hnle : ¬z ≤ cnt + 1 := by omega) <;>
    (try have hfl : f ≤ l := by omega) <;>
    (try have hnfl : ¬f ≤ l := by omega) <;>
    eval_step

/-- The count step is the counters' count step, encoded. -/
theorem count_step (u y r : List Bool) (c : Bool) (x : Counters) (k : ℕ) (hv : Valid k x)
    (hk : k < y.length) : countStep.sem (stepAt u y (c :: r) x) = y.drop (advance x c).count := by
  rcases x with ⟨ph, f, l, z, cnt, v⟩
  cases ph <;> cases c <;> simp only [Valid] at hv <;>
    by_cases he : cnt + 1 = z <;> by_cases hf : f = l <;>
    (try have hb : cnt + 1 < y.length := by omega) <;>
    (try have hb' : z < y.length := by omega) <;>
    (try have hl : l < y.length := by omega) <;>
    (try have hle : z ≤ cnt + 1 := by omega) <;>
    (try have hnle : ¬z ≤ cnt + 1 := by omega) <;>
    (try have hfl : f ≤ l := by omega) <;>
    (try have hnfl : ¬f ≤ l := by omega) <;>
    eval_step

/-- The value step is the counters' value step, encoded. -/
theorem value_step (u y r : List Bool) (c : Bool) (x : Counters) (k : ℕ) (hv : Valid k x)
    (hk : k < y.length) : valueStep.sem (stepAt u y (c :: r) x) = y.drop (advance x c).value := by
  rcases x with ⟨ph, f, l, z, cnt, v⟩
  cases ph <;> cases c <;> simp only [Valid] at hv <;>
    by_cases he : cnt + 1 = z <;> by_cases hf : f = l <;>
    (try have hb : cnt + 1 < y.length := by omega) <;>
    (try have hb' : z < y.length := by omega) <;>
    (try have hl : l < y.length := by omega) <;>
    (try have hle : z ≤ cnt + 1 := by omega) <;>
    (try have hnle : ¬z ≤ cnt + 1 := by omega) <;>
    (try have hfl : f ≤ l := by omega) <;>
    (try have hnfl : ¬f ≤ l := by omega) <;>
    eval_step

end StepLemmas

/-- One step on the encoded counters is the encoded step of the counters. -/
theorem step_encode (u y r : List Bool) (c : Bool) (x : Counters) (k : ℕ) (hv : Valid k x)
    (hk : k < y.length) (i : Bool) (l : Fin 7) :
    (treeStep i l).sem (stepAt u y (c :: r) x) = encode y r (advance x c) l :=
  match l with
  | 0 => rest_step u y r c x
  | 1 => mode_step u y r c x k hv hk
  | 2 => forks_step u y r c x k hv hk
  | 3 => leaves_step u y r c x k hv hk
  | 4 => width_step u y r c x k hv hk
  | 5 => count_step u y r c x k hv hk
  | 6 => value_step u y r c x k hv hk

/-- After a prefix of the word is read, the registers hold the remaining word
and the encoded counters on that prefix. -/
theorem regs_eq (y u : List Bool) : ∀ (p r : List Bool), y = p ++ r → p.length = u.length →
    regs u y = encode y r (p.foldl advance init) :=
  List.rec
    (motive := fun u ↦ ∀ (p r : List Bool), y = p ++ r → p.length = u.length →
      regs u y = encode y r (p.foldl advance init))
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
        have hv := (toState_foldl p' 0 init valid_init).1
        rw [Nat.zero_add] at hv
        have hk : p'.length < y.length := by
          rw [hy, List.length_append, List.length_cons]
          omega
        funext l
        rw [regs_cons, ih p' (c :: r) hy (by omega), List.foldl_append, List.foldl_cons,
          List.foldl_nil]
        exact step_encode v y r c _ _ hv hk i l) u

/-- The recognizer returns {lit}`[true]` on a word the streaming scanner
accepts and the empty word on every other. -/
theorem isEliasTreeSem_eq (y : List Bool) :
    isEliasTree.sem ![y] = if (scan y).1 = .done then [true] else [] := by
  rw [isEliasTree, sem_diagL]
  have h := regs_eq y y y [] (List.append_nil y).symm rfl
  have h1 : (treeReg 1).sem ![y, y] = phaseCode (run y).phase := congrFun h 1
  simp only [accept, sem_cond4L, sem_tailAppL, sem_constL, h1, ← run_phase_done_iff]
  generalize (run y).phase = p
  cases p <;> rfl

/-- The recognizer returns {lit}`[true]` on a word the Elias-length recognizer
accepts and the empty word on every other. -/
theorem isEliasTreeSem_eq_validBool (y : List Bool) :
    isEliasTree.sem ![y] = if Geb.BitTree.Elias.validBool y then [true] else [] := by
  rw [isEliasTreeSem_eq, ← Geb.BitTree.Elias.Scanner.validBool_eq,
    Geb.BitTree.Elias.Scanner.validBool]
  simp only [decide_eq_true_eq]

/-- The recognizer accepts exactly the words the Elias-length recognizer
accepts. -/
theorem isEliasTreeSem_eq_singleton_iff_validBool (y : List Bool) :
    isEliasTree.sem ![y] = [true] ↔ Geb.BitTree.Elias.validBool y = true := by
  rw [isEliasTreeSem_eq_validBool]
  cases Geb.BitTree.Elias.validBool y <;> simp

/-- The recognizer accepts exactly the encodings of trees. -/
theorem isEliasTreeSem_eq_singleton_iff (y : List Bool) :
    isEliasTree.sem ![y] = [true] ↔ ∃ t, Geb.BitTree.Elias.encode t = y :=
  (isEliasTreeSem_eq_singleton_iff_validBool y).trans (Geb.BitTree.Elias.validBool_iff y)

end

end Geb.SizeBounded.Logspace.EliasTree
