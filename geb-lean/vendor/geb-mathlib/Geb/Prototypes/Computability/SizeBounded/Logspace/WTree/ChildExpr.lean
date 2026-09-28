/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.ExprBase
public import Geb.Prototypes.Computability.SizeBounded.Logspace.EliasTree.Correct
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Children

set_option doc.verso true in
/-!
# The scan over one node's children as a successor-free expression

The scan over the children of one node,
{name}`Geb.SizeBounded.Logspace.WTree.childScan`, as an expression of the
logspace subalgebra: a simultaneous recursion over the word with twelve
registers, the seven of the Elias-length tree recognizer and five more, the
mode as a three-bit code, the fork count, the leaf count and the number of
children completed each as the word dropped by it, and the flag as a word,
with four parameters, the word, the remaining word from the node's first
payload bit, the word dropped by one more than the node's label length, and
the word dropped by the node's arity. The check at a child is a parameter of
the expression, of arity six: the four parameters of the scan followed by the
remaining word from the child's first payload bit and the word dropped by one
more than the child's label length. The expression computes the scan whose
check is the expression's, read as a flag.

# Main definitions

* {lit}`emb`, {lit}`lift` — the Elias step's slots among the scan's, and an
  Elias step at the scan's arity.
* {lit}`restV`, {lit}`modeV`, {lit}`widthV`, {lit}`countV`, {lit}`valueV`,
  {lit}`mV`, {lit}`fcV`, {lit}`lcV`, {lit}`jV`, {lit}`okV`, {lit}`wordV`,
  {lit}`targetPtrV`, {lit}`targetLenV`, {lit}`kV` — the registers and the
  parameters of the step environment.
* {lit}`modeCode`, {lit}`onMode2` — the codes of the modes and the dispatch on
  the mode register.
* {lit}`fieldEndV`, {lit}`eqT`, {lit}`zF`, {lit}`eqLF`, {lit}`after0`,
  {lit}`after1`, {lit}`edgeAt`, {lit}`okE`, {lit}`lenH` — the tests and
  values the steps share.
* {lit}`mStep`, {lit}`fcStep`, {lit}`lcStep`, {lit}`jStep`, {lit}`okStep`,
  {lit}`childBase`, {lit}`childStep`, {lit}`childReg`, {lit}`childScanExpr` —
  the five new steps, the recursion's bases and steps, its registers, and the
  scan as an expression of arity four.
* {lit}`edgeB` — the check an expression defines.
* {lit}`ChildReg.Bounded` — the counts are bounded by the bits read.
* {lit}`encodeC`, {lit}`stepAtC` — the registers holding a remaining word,
  counters and the scan's registers, and the step environment holding them
  and the parameters.

# Main statements

* {lit}`childUpd_bounded` — the bound is preserved.
* {lit}`step_encodeC` — each register's step on the encoded state is the
  encoded step of the state.
* {lit}`regsC_eq` — after a prefix, the registers hold the remaining word and
  the encoded state on the prefix.
* {lit}`childScanExprSem_eq` — the expression's value is the scan's flag.

# References

* \[Kristiansen2005\]

# Tags

logspace, simultaneous recursion on notation, W-type, recognizer
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree.ChildExpr

open Geb.BitTree.Elias.Scanner (Mode State step finish scan)
open EliasTree (Phase Counters Valid advance init phaseCode)

public section

/-- The Elias step's slots among the scan's: the level, the seven registers,
and the word, the first parameter, held after the five further registers. -/
@[expose] def emb : Fin 9 → Fin 17 := ![0, 1, 2, 3, 4, 5, 6, 7, 13]

/-- An Elias step at the scan's arity. -/
@[expose] def lift (e : LOf 9) : LOf 17 := liftBy emb e

/-- The unread input, slot one. -/
@[expose] def restV : LOf 17 := projL 17 1

/-- The phase register, slot two. -/
@[expose] def modeV : LOf 17 := projL 17 2

/-- The width, slot five. -/
@[expose] def widthV : LOf 17 := projL 17 5

/-- The count, slot six. -/
@[expose] def countV : LOf 17 := projL 17 6

/-- The value, slot seven. -/
@[expose] def valueV : LOf 17 := projL 17 7

/-- The mode register, slot eight. -/
@[expose] def mV : LOf 17 := projL 17 8

/-- The fork count, slot nine. -/
@[expose] def fcV : LOf 17 := projL 17 9

/-- The leaf count, slot ten. -/
@[expose] def lcV : LOf 17 := projL 17 10

/-- The number of children completed, slot eleven. -/
@[expose] def jV : LOf 17 := projL 17 11

/-- The flag, slot twelve. -/
@[expose] def okV : LOf 17 := projL 17 12

/-- The word, the first parameter, slot thirteen. -/
@[expose] def wordV : LOf 17 := projL 17 13

/-- The remaining word from the node's first payload bit, slot fourteen. -/
@[expose] def targetPtrV : LOf 17 := projL 17 14

/-- The word dropped by one more than the node's label length, slot fifteen. -/
@[expose] def targetLenV : LOf 17 := projL 17 15

/-- The word dropped by the node's arity, slot sixteen. -/
@[expose] def kV : LOf 17 := projL 17 16

/-- The three-bit code of a mode. -/
@[expose] def modeCode : CMode → List Bool
  | .before => [true, true, true]
  | .label => [true, true, false]
  | .spine => [true, false, true]
  | .body => [true, false, false]
  | .done => [false, true, true]

/-- A mode's code as a constant of the step arity. -/
@[expose] def code17 (m : CMode) : LOf 17 := constL 17 (modeCode m)

/-- Dispatch on the mode register. -/
@[expose] def onMode2 (m before label spine body done : LOf 17) : LOf 17 :=
  cond4L m done
    (cond4L (tailAppL m) done
      (cond4L (tailAppL (tailAppL m)) done before label)
      (cond4L (tailAppL (tailAppL m)) done spine body))
    done

/-- The dispatch on a mode code selects the expression of that mode. -/
theorem sem_onMode2 (m before label spine body done : LOf 17) (x : Fin 17 → List Bool)
    (md : CMode) (hx : m.sem x = modeCode md) :
    (onMode2 m before label spine body done).sem x =
      (match md with
        | .before => before
        | .label => label
        | .spine => spine
        | .body => body
        | .done => done).sem x := by
  simp only [onMode2, sem_cond4L, sem_tailAppL, hx]
  cases md <;> rfl

/-- The field-end test. -/
@[expose] def fieldEndV : LOf 17 := dropByApp widthV (tailAppL countV)

/-- The next bit is the node's first payload bit. -/
@[expose] def eqT : LOf 17 := eqSeg (tailAppL restV) targetPtrV

/-- The fork count at zero. -/
@[expose] def zF : LOf 17 := isZeroSeg fcV wordV

/-- The leaf count equals the fork count. -/
@[expose] def eqLF : LOf 17 := eqSeg lcV fcV

/-- The mode after no children: done when the node has none, else at the
first child's fork tags. -/
@[expose] def after0 : LOf 17 :=
  cond4L (eqSeg wordV kV) (code17 .spine) (code17 .done) (code17 .done)

/-- The mode after one more child: done when it was the last, else at the
next child's fork tags. -/
@[expose] def after1 : LOf 17 :=
  cond4L (eqSeg (tailAppL jV) kV) (code17 .spine) (code17 .done) (code17 .done)

/-- The check applied to the parameters, the remaining word past the current
bit, a length counter and the number of children completed. -/
@[expose] def edgeAt (edge : LOf 6) (len : LOf 17) : LOf 17 :=
  compL edge ![wordV, targetPtrV, targetLenV, tailAppL restV, len, jV]

/-- The flag conjoined with the check at a child. -/
@[expose] def okE (edge : LOf 6) (len : LOf 17) : LOf 17 := andOkAt okV (flagOf (edgeAt edge len))

/-- The length counter a completed length field yields. -/
@[expose] def lenH : LOf 17 := lenAfterHeaderAt restV valueV wordV

/-- A register's step in a mode, by its values at the events. -/
@[expose] def ev (fork tag headerDone lengthEnd payloadDone dflt : LOf 17) : LOf 17 :=
  eventStep modeV restV fieldEndV fork tag headerDone lengthEnd payloadDone dflt

/-- The mode's step. -/
@[expose] def mStep : LOf 17 :=
  onMode2 mV
    (ev mV mV (cond4L eqT mV after0 after0) (cond4L eqT mV (code17 .label) (code17 .label)) mV mV)
    (ev mV mV after0 mV after0 mV)
    (ev mV mV (cond4L zF after1 (code17 .body) (code17 .body)) (code17 .body) mV mV)
    (ev mV mV (cond4L eqLF mV after1 after1) mV (cond4L eqLF mV after1 after1) mV)
    mV

/-- The fork count's step. -/
@[expose] def fcStep : LOf 17 :=
  onMode2 mV
    (ev fcV fcV (cond4L eqT fcV wordV wordV) (cond4L eqT fcV wordV wordV) fcV fcV)
    (ev fcV fcV wordV fcV wordV fcV)
    (ev (tailAppL fcV) fcV (cond4L zF wordV fcV fcV) fcV fcV fcV)
    (ev (tailAppL fcV) fcV (cond4L eqLF fcV wordV wordV) fcV (cond4L eqLF fcV wordV wordV) fcV)
    fcV

/-- The leaf count's step. -/
@[expose] def lcStep : LOf 17 :=
  onMode2 mV
    (ev lcV lcV (cond4L eqT lcV wordV wordV) (cond4L eqT lcV wordV wordV) lcV lcV)
    (ev lcV lcV wordV lcV wordV lcV)
    (ev lcV lcV (cond4L zF wordV (tailAppL wordV) (tailAppL wordV)) wordV lcV lcV)
    (ev lcV lcV (cond4L eqLF (tailAppL lcV) wordV wordV) lcV
      (cond4L eqLF (tailAppL lcV) wordV wordV) lcV)
    lcV

/-- The step of the number of children completed. -/
@[expose] def jStep : LOf 17 :=
  onMode2 mV
    (ev jV jV (cond4L eqT jV wordV wordV) (cond4L eqT jV wordV wordV) jV jV)
    (ev jV jV wordV jV wordV jV)
    (ev jV jV (cond4L zF (tailAppL jV) jV jV) jV jV jV)
    (ev jV jV (cond4L eqLF jV (tailAppL jV) (tailAppL jV)) jV
      (cond4L eqLF jV (tailAppL jV) (tailAppL jV)) jV)
    jV

/-- The flag's step: at a child's fork tags, the completed header conjoins the
check. -/
@[expose] def okStep (edge : LOf 6) : LOf 17 :=
  onMode2 mV okV okV (ev okV okV (okE edge (tailAppL wordV)) (okE edge lenH) okV okV) okV okV

/-- The recursion's bases: the Elias bases at the scan's parameters, the code
of the mode before the node, the word for each count at zero, and the flag
set. -/
@[expose] def childBase : Fin 12 → LOf 4 :=
  Fin.append (fun l ↦ compL (EliasTree.treeBase l) ![projL 4 0])
    ![constL 4 (modeCode .before), projL 4 0, projL 4 0, projL 4 0, constL 4 [true]]

/-- The recursion's steps: the Elias steps lifted, and the five new steps. -/
@[expose] def childStep (edge : LOf 6) : Bool → Fin 12 → LOf 17 :=
  fun i ↦ Fin.append (fun l ↦ lift (EliasTree.treeStep i l))
    ![mStep, fcStep, lcStep, jStep, okStep edge]

/-- The twelve registers, as expressions of arity five: the counter and the
four parameters. -/
@[expose] def childReg (edge : LOf 6) (l : Fin 12) : LOf 5 := srnL childBase (childStep edge) l

/-- The scan as an expression of arity four: the flag register with the word
as counter and first parameter. -/
@[expose] def childScanExpr (edge : LOf 6) : LOf 4 :=
  compL (childReg edge 11) ![projL 4 0, projL 4 0, projL 4 1, projL 4 2, projL 4 3]

/-- The check an expression of arity six defines on a word and a node's label:
its value read as a flag, at the word, the remaining word from the node's
first payload bit, the word dropped by one more than the node's label length,
and the same two for the child, and the word dropped by the child's position. -/
@[expose] def edgeB (edge : LOf 6) (y : List Bool) (target : Loc) (l : Loc) (j : ℕ) : Bool :=
  isTrueWord (edge.sem ![y, y.drop target.pos, y.drop (target.len + 1), y.drop l.pos,
    y.drop (l.len + 1), y.drop j])

/-- The counts are bounded by the bits read. -/
@[expose] def ChildReg.Bounded (pos : ℕ) (z : ChildReg) : Prop :=
  z.fc ≤ pos ∧ z.lc ≤ pos ∧ z.j ≤ pos

/-- One bit preserves the bound, at one more bit read. -/
theorem childUpd_bounded (target : Loc) (k : ℕ) (edge : Loc → ℕ → Bool) (pos : ℕ) (e : Event)
    (z : ChildReg) (h : ChildReg.Bounded pos z) :
    ChildReg.Bounded (pos + 1) (childUpd target k edge pos e z) := by
  obtain ⟨h₁, h₂, h₃⟩ := h
  rcases z with ⟨m, fc, lc, j, ok⟩
  simp only at h₁ h₂ h₃
  cases m <;> simp only [childUpd, afterChildren] <;> (try cases e.payload) <;> (try split_ifs) <;>
    simp only [ChildReg.Bounded] <;> exact ⟨by omega, by omega, by omega⟩

/-- The registers holding a remaining word, counters and the scan's registers. -/
@[expose] def encodeC (y r : List Bool) (x : Counters) (z : ChildReg) : Fin 12 → List Bool :=
  Fin.append (EliasTree.encode y r x)
    ![modeCode z.mode, y.drop z.fc, y.drop z.lc, y.drop z.j, boolWord z.ok]

/-- The step environment at a level, holding the registers and the
parameters. -/
@[expose] def stepAtC (u y r : List Bool) (x : Counters) (z : ChildReg) (target : Loc) (k : ℕ) :
    Fin 17 → List Bool :=
  stepEnv u (encodeC y r x z) ![y, y.drop target.pos, y.drop (target.len + 1), y.drop k]

variable (u y r : List Bool) (x : Counters) (z : ChildReg) (target : Loc) (k : ℕ)

/-- The Elias slots of the step environment are the Elias step environment. -/
theorem stepAtC_emb : stepAtC u y r x z target k ∘ emb = EliasTree.stepAt u y r x :=
  funext fun i ↦ match i with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 => rfl

/-- The remaining-input register's meaning. -/
theorem sem_restV : restV.sem (stepAtC u y r x z target k) = r := rfl

/-- The phase register's meaning. -/
theorem sem_modeV : modeV.sem (stepAtC u y r x z target k) = phaseCode x.phase := rfl

/-- The width's meaning. -/
theorem sem_widthV : widthV.sem (stepAtC u y r x z target k) = y.drop x.width := rfl

/-- The count's meaning. -/
theorem sem_countV : countV.sem (stepAtC u y r x z target k) = y.drop x.count := rfl

/-- The value's meaning. -/
theorem sem_valueV : valueV.sem (stepAtC u y r x z target k) = y.drop x.value := rfl

/-- The mode register's meaning. -/
theorem sem_mV : mV.sem (stepAtC u y r x z target k) = modeCode z.mode := rfl

/-- The fork count's meaning. -/
theorem sem_fcV : fcV.sem (stepAtC u y r x z target k) = y.drop z.fc := rfl

/-- The leaf count's meaning. -/
theorem sem_lcV : lcV.sem (stepAtC u y r x z target k) = y.drop z.lc := rfl

/-- The meaning of the number of children completed. -/
theorem sem_jV : jV.sem (stepAtC u y r x z target k) = y.drop z.j := rfl

/-- The flag's meaning. -/
theorem sem_okV : okV.sem (stepAtC u y r x z target k) = boolWord z.ok := rfl

/-- The word's meaning. -/
theorem sem_wordV : wordV.sem (stepAtC u y r x z target k) = y := rfl

/-- The node pointer's meaning. -/
theorem sem_targetPtrV : targetPtrV.sem (stepAtC u y r x z target k) = y.drop target.pos := rfl

/-- The node length counter's meaning. -/
theorem sem_targetLenV :
    targetLenV.sem (stepAtC u y r x z target k) = y.drop (target.len + 1) := rfl

/-- The arity counter's meaning. -/
theorem sem_kV : kV.sem (stepAtC u y r x z target k) = y.drop k := rfl

/-- The field-end test's meaning. -/
theorem sem_fieldEndV :
    fieldEndV.sem (stepAtC u y r x z target k) =
      (y.drop x.count).tail.drop (y.drop x.width).length := by
  simp only [fieldEndV, sem_dropByApp, sem_tailAppL, sem_widthV, sem_countV]

/-- An Elias register's step on the encoded state is the encoded step of the
counters. -/
theorem elias_step (c : Bool) (k₀ : ℕ) (hv : Valid k₀ x) (hk : k₀ < y.length) (i : Bool)
    (l : Fin 7) :
    (lift (EliasTree.treeStep i l)).sem (stepAtC u y (c :: r) x z target k) =
      EliasTree.encode y r (advance x c) l := by
  rw [lift, sem_liftBy, stepAtC_emb]
  exact EliasTree.step_encode u y r c x k₀ hv hk i l

/-- The check applied, on the encoded state. -/
theorem sem_edgeAt (edge : LOf 6) (len : LOf 17) (c : Bool) :
    (edgeAt edge len).sem (stepAtC u y (c :: r) x z target k) =
      edge.sem ![y, y.drop target.pos, y.drop (target.len + 1), r,
        len.sem (stepAtC u y (c :: r) x z target k), y.drop z.j] := by
  rw [edgeAt, sem_compL]
  congr 1
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl
  | 2 => rfl
  | 3 =>
    change (tailAppL restV).sem _ = r
    rw [sem_tailAppL, sem_restV]
    rfl
  | 4 => rfl
  | 5 => rfl

/-- The length counter a completed header yields, on the encoded state. -/
theorem sem_lenH (c : Bool) :
    lenH.sem (stepAtC u y (c :: r) x z target k) = y.drop (2 * x.value + c.toNat) :=
  sem_lenAfterHeaderAt restV valueV wordV (stepAtC u y (c :: r) x z target k) y r c x.value
    (sem_restV u y (c :: r) x z target k) (sem_valueV u y (c :: r) x z target k)
    (sem_wordV u y (c :: r) x z target k)

section StepLemmas

variable (c : Bool) (k₀ : ℕ) (hv : Valid k₀ x) (hk : k₀ < y.length) (p : List Bool)
  (hy : y = p ++ c :: r) (hb : ChildReg.Bounded p.length z) (htp : target.pos ≤ y.length)
  (hkl : k ≤ y.length)

include hy in
/-- The remaining word past the current bit. -/
theorem drop_succ_length : y.drop (p.length + 1) = r := by
  rw [hy, ← List.drop_drop, List.drop_left, List.drop_one]
  rfl

include hy in
/-- The next bit lies within the word. -/
theorem succ_length_le : p.length + 1 ≤ y.length := by
  rw [hy, List.length_append, List.length_cons]
  omega

include hy htp in
/-- The target test's meaning. -/
theorem sem_eqT :
    eqT.sem (stepAtC u y (c :: r) x z target k) = boolWord (decide (p.length + 1 = target.pos)) :=
  sem_eqSeg _ _ _ y (p.length + 1) target.pos
    (by rw [sem_tailAppL, sem_restV, drop_succ_length y r c p hy]; rfl)
    (sem_targetPtrV u y (c :: r) x z target k) (succ_length_le y r c p hy) htp

include hy hb in
/-- The equality test of the counts, its meaning. -/
theorem sem_eqLF :
    eqLF.sem (stepAtC u y (c :: r) x z target k) = boolWord (decide (z.lc = z.fc)) :=
  sem_eqSeg _ _ _ y z.lc z.fc (sem_lcV u y (c :: r) x z target k)
    (sem_fcV u y (c :: r) x z target k)
    (by have := hb.2.1; have := succ_length_le y r c p hy; omega)
    (by have := hb.1; have := succ_length_le y r c p hy; omega)

include hy hb hkl in
/-- The test of the last child, its meaning. -/
theorem sem_eqJK :
    (eqSeg (tailAppL jV) kV).sem (stepAtC u y (c :: r) x z target k) =
      boolWord (decide (z.j + 1 = k)) :=
  sem_eqSeg _ _ _ y (z.j + 1) k (by rw [sem_tailAppL, sem_jV, List.tail_drop])
    (sem_kV u y (c :: r) x z target k)
    (by have := hb.2.2; have := succ_length_le y r c p hy; omega) hkl

include hkl in
/-- The test of no children, its meaning. -/
theorem sem_eq0K :
    (eqSeg wordV kV).sem (stepAtC u y (c :: r) x z target k) = boolWord (decide (0 = k)) :=
  sem_eqSeg _ _ _ y 0 k (by rw [sem_wordV, List.drop_zero]) (sem_kV u y (c :: r) x z target k)
    (Nat.zero_le _) hkl

/-- The zero test of the fork count, its meaning. -/
theorem sem_zF : zF.sem (stepAtC u y (c :: r) x z target k) = y.drop (y.length - z.fc) :=
  sem_isZeroSeg _ _ _ y z.fc (sem_fcV u y (c :: r) x z target k)
    (sem_wordV u y (c :: r) x z target k)

/-- The flag conjoined with the check, on the encoded state. -/
theorem sem_okE (edge : LOf 6) (len : LOf 17) (c : Bool) :
    (okE edge len).sem (stepAtC u y (c :: r) x z target k) =
      boolWord (z.ok && isTrueWord (edge.sem ![y, y.drop target.pos, y.drop (target.len + 1), r,
        len.sem (stepAtC u y (c :: r) x z target k), y.drop z.j])) := by
  rw [okE, andOkAt, sem_cond4L, sem_okV, sem_flagOf, sem_edgeAt, sem_constL, cond4Sem_boolWord]

/-- The evaluation of a register step on a step environment: the dispatches,
the tests, the registers, and the abstract update, with the reductions of the
literal codes and the conditionals, and the given facts. -/
local macro "eval_child" : tactic =>
  `(tactic| simp only [eventValue, childUpd, afterChildren, Event.silent, ↓reduceIte,
      Bool.false_eq_true, sem_cond4L, cond4Sem_boolWord_same, cond4Sem_boolWord, decide_eq_true_eq,
      sem_tailAppL, sem_fcV, sem_lcV, sem_jV, sem_wordV, sem_okV, sem_mV, code17, sem_constL,
      after0, after1, List.tail_drop, List.drop_zero, sem_okE, sem_lenH, edgeB, Nat.zero_add,
      List.drop_one, *])

/-- The facts the register steps share: the meanings of the tests, at the
registers, and the remaining word; the word's decomposition is then
discarded, so that the evaluation does not rewrite the word by it. -/
local macro "child_facts" : tactic =>
  `(tactic| (have hT := sem_eqT u y r x z target k c p hy htp
             have hLF := sem_eqLF u y r x z target k c p hy hb
             have hJK := sem_eqJK u y r x z target k c p hy hb hkl
             have h0K := sem_eq0K u y r x z target k c hkl
             have hZ := sem_zF u y r x z target k c
             have hZc := cond4Sem_drop_length_sub y z.fc
               (by have := hb.1; have := succ_length_le y r c p hy; omega)
             have hr := drop_succ_length y r c p hy
             have hL : ∀ L, (eventC x c).payload = some L → (eventC x c).done = false →
               L + 1 = 2 * x.value + c.toNat := fun L h1 h2 ↦
                 eventC_payload_of_not_done k₀ x c L hv h1 h2
             clear hy))

include hv hk hy hb htp hkl in
/-- The mode's step on the encoded state is the encoded step of the mode. -/
theorem m_step (edge : LOf 6) : mStep.sem (stepAtC u y (c :: r) x z target k) =
    modeCode (childUpd target k (edgeB edge y target) p.length (eventC x c) z).mode := by
  child_facts
  rcases z with ⟨m, fc, lc, j, ok⟩
  dsimp only at *
  rw [mStep, sem_onMode2 _ _ _ _ _ _ _ m rfl]
  cases m <;> dsimp only <;> (try rw [ev, sem_eventStep _ _ _ _ _ _ _ _ _ _ y r c x k₀ hv hk
    (sem_modeV _ _ _ _ _ _ _) (sem_restV _ _ _ _ _ _ _) (sem_fieldEndV _ _ _ _ _ _ _)]) <;>
    (try rcases eventC_cases x c with h | h | h | ⟨L, h⟩ | h | h <;> rw [h]) <;>
    eval_child <;> (try split_ifs) <;> dsimp only

include hv hk hy hb htp hkl in
/-- The fork count's step on the encoded state is the encoded step of the
count. -/
theorem fc_step (edge : LOf 6) : fcStep.sem (stepAtC u y (c :: r) x z target k) =
    y.drop (childUpd target k (edgeB edge y target) p.length (eventC x c) z).fc := by
  child_facts
  rcases z with ⟨m, fc, lc, j, ok⟩
  dsimp only at *
  rw [fcStep, sem_onMode2 _ _ _ _ _ _ _ m rfl]
  cases m <;> dsimp only <;> (try rw [ev, sem_eventStep _ _ _ _ _ _ _ _ _ _ y r c x k₀ hv hk
    (sem_modeV _ _ _ _ _ _ _) (sem_restV _ _ _ _ _ _ _) (sem_fieldEndV _ _ _ _ _ _ _)]) <;>
    (try rcases eventC_cases x c with h | h | h | ⟨L, h⟩ | h | h <;> rw [h]) <;>
    eval_child <;> (try split_ifs) <;> (try dsimp only) <;> rfl

include hv hk hy hb htp hkl in
/-- The leaf count's step on the encoded state is the encoded step of the
count. -/
theorem lc_step (edge : LOf 6) : lcStep.sem (stepAtC u y (c :: r) x z target k) =
    y.drop (childUpd target k (edgeB edge y target) p.length (eventC x c) z).lc := by
  child_facts
  rcases z with ⟨m, fc, lc, j, ok⟩
  dsimp only at *
  rw [lcStep, sem_onMode2 _ _ _ _ _ _ _ m rfl]
  cases m <;> dsimp only <;> (try rw [ev, sem_eventStep _ _ _ _ _ _ _ _ _ _ y r c x k₀ hv hk
    (sem_modeV _ _ _ _ _ _ _) (sem_restV _ _ _ _ _ _ _) (sem_fieldEndV _ _ _ _ _ _ _)]) <;>
    (try rcases eventC_cases x c with h | h | h | ⟨L, h⟩ | h | h <;> rw [h]) <;>
    eval_child <;> (try split_ifs) <;> (try dsimp only) <;> (try rw [List.drop_one]) <;> rfl

include hv hk hy hb htp hkl in
/-- The step of the number of children completed, on the encoded state. -/
theorem j_step (edge : LOf 6) : jStep.sem (stepAtC u y (c :: r) x z target k) =
    y.drop (childUpd target k (edgeB edge y target) p.length (eventC x c) z).j := by
  child_facts
  rcases z with ⟨m, fc, lc, j, ok⟩
  dsimp only at *
  rw [jStep, sem_onMode2 _ _ _ _ _ _ _ m rfl]
  cases m <;> dsimp only <;> (try rw [ev, sem_eventStep _ _ _ _ _ _ _ _ _ _ y r c x k₀ hv hk
    (sem_modeV _ _ _ _ _ _ _) (sem_restV _ _ _ _ _ _ _) (sem_fieldEndV _ _ _ _ _ _ _)]) <;>
    (try rcases eventC_cases x c with h | h | h | ⟨L, h⟩ | h | h <;> rw [h]) <;>
    eval_child <;> (try split_ifs) <;> (try dsimp only) <;> rfl

include hv hk hy hb htp hkl in
/-- The flag's step on the encoded state is the encoded step of the flag, the
check being the expression's. -/
theorem ok_step (edge : LOf 6) : (okStep edge).sem (stepAtC u y (c :: r) x z target k) =
    boolWord (childUpd target k (edgeB edge y target) p.length (eventC x c) z).ok := by
  child_facts
  rcases z with ⟨m, fc, lc, j, ok⟩
  dsimp only at *
  rw [okStep, sem_onMode2 _ _ _ _ _ _ _ m rfl]
  cases m <;> dsimp only <;> (try rw [ev, sem_eventStep _ _ _ _ _ _ _ _ _ _ y r c x k₀ hv hk
    (sem_modeV _ _ _ _ _ _ _) (sem_restV _ _ _ _ _ _ _) (sem_fieldEndV _ _ _ _ _ _ _)]) <;>
    (try rcases eventC_cases x c with h | h | h | ⟨L, h⟩ | h | h <;> rw [h]) <;>
    eval_child <;> (try split_ifs) <;> dsimp only

include hv hk hy hb htp hkl in
/-- One step on the encoded state is the encoded step of the state. -/
theorem step_encodeC (edge : LOf 6) (i : Bool) (l : Fin 12) :
    (childStep edge i l).sem (stepAtC u y (c :: r) x z target k) =
      encodeC y r (advance x c) (childUpd target k (edgeB edge y target) p.length (eventC x c) z)
        l :=
  match l with
  | 0 => elias_step u y r x z target k c k₀ hv hk i 0
  | 1 => elias_step u y r x z target k c k₀ hv hk i 1
  | 2 => elias_step u y r x z target k c k₀ hv hk i 2
  | 3 => elias_step u y r x z target k c k₀ hv hk i 3
  | 4 => elias_step u y r x z target k c k₀ hv hk i 4
  | 5 => elias_step u y r x z target k c k₀ hv hk i 5
  | 6 => elias_step u y r x z target k c k₀ hv hk i 6
  | 7 => m_step u y r x z target k c k₀ hv hk p hy hb htp hkl edge
  | 8 => fc_step u y r x z target k c k₀ hv hk p hy hb htp hkl edge
  | 9 => lc_step u y r x z target k c k₀ hv hk p hy hb htp hkl edge
  | 10 => j_step u y r x z target k c k₀ hv hk p hy hb htp hkl edge
  | 11 => ok_step u y r x z target k c k₀ hv hk p hy hb htp hkl edge

end StepLemmas

/-- The registers' meanings at a counter, a word and the parameters. -/
@[expose] def regsC (edge : LOf 6) (u y : List Bool) (target : Loc) (k : ℕ) : Fin 12 → List Bool :=
  fun l ↦ (childReg edge l).sem
    (Fin.cons u ![y, y.drop target.pos, y.drop (target.len + 1), y.drop k])

/-- On the empty counter the registers hold the word, the tree code, the word
for each counter, the code of the mode before the node, the word for each
count, and the flag set. -/
theorem regsC_nil (edge : LOf 6) (y : List Bool) (target : Loc) (k : ℕ) :
    regsC edge [] y target k = encodeC y y init ⟨.before, 0, 0, 0, true⟩ :=
  funext fun l ↦ match l with | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 | 8 | 9 | 10 | 11 => rfl

/-- One more counter bit runs the step of each register at the environment
holding the registers and the parameters. -/
theorem regsC_cons (edge : LOf 6) (i : Bool) (v y : List Bool) (target : Loc) (k : ℕ)
    (l : Fin 12) :
    regsC edge (i :: v) y target k l =
      (childStep edge i l).sem
        (stepEnv v (regsC edge v y target k)
          ![y, y.drop target.pos, y.drop (target.len + 1), y.drop k]) :=
  sem_srnL_cons childBase (childStep edge) l i v _

/-- The extended fold of the scan's registers on the counters. -/
@[expose] def foldC (edge : LOf 6) (y : List Bool) (target : Loc) (k : ℕ) (p : List Bool) :
    ExtC ChildReg :=
  p.foldl (extStepC (childUpd target k (edgeB edge y target))) ⟨init, 0, ⟨.before, 0, 0, 0, true⟩⟩

/-- The fold over one more bit. -/
theorem foldC_concat (edge : LOf 6) (y : List Bool) (target : Loc) (k : ℕ) (p : List Bool)
    (c : Bool) :
    foldC edge y target k (p ++ [c]) =
      extStepC (childUpd target k (edgeB edge y target)) (foldC edge y target k p) c := by
  unfold foldC
  rw [List.foldl_concat]

/-- The counts of the fold are bounded by the bits read. -/
theorem foldC_bounded (edge : LOf 6) (y : List Bool) (target : Loc) (k : ℕ) (p : List Bool) :
    ChildReg.Bounded p.length (foldC edge y target k p).extra := by
  have key : ∀ (p : List Bool) (s : ExtC ChildReg), ChildReg.Bounded s.pos s.extra →
      ChildReg.Bounded (p.foldl (extStepC (childUpd target k (edgeB edge y target))) s).pos
        (p.foldl (extStepC (childUpd target k (edgeB edge y target))) s).extra :=
    List.rec (fun _ h ↦ h) fun b p ih s h ↦ by
      rw [List.foldl_cons]
      exact ih _ (childUpd_bounded _ _ _ _ _ _ h)
  have := key p ⟨init, 0, ⟨.before, 0, 0, 0, true⟩⟩ ⟨Nat.le_refl 0, Nat.le_refl 0, Nat.le_refl 0⟩
  rwa [foldl_extStepC_pos, Nat.zero_add] at this

/-- After a prefix of the word is read, the registers hold the remaining word
and the encoded state on that prefix. -/
theorem regsC_eq (edge : LOf 6) (y u : List Bool) (target : Loc) (k : ℕ)
    (htp : target.pos ≤ y.length) (hkl : k ≤ y.length) :
    ∀ (p r : List Bool), y = p ++ r → p.length = u.length →
      regsC edge u y target k =
        encodeC y r (foldC edge y target k p).counters (foldC edge y target k p).extra :=
  List.rec
    (motive := fun u ↦ ∀ (p r : List Bool), y = p ++ r → p.length = u.length →
      regsC edge u y target k =
        encodeC y r (foldC edge y target k p).counters (foldC edge y target k p).extra)
    (fun p r hy hp ↦ by
      have hp' : p = [] := List.eq_nil_of_length_eq_zero hp
      subst hp'
      subst hy
      exact regsC_nil edge _ target k)
    (fun i v ih p r hy hp ↦ by
      rcases List.eq_nil_or_concat p with hn | ⟨p', c, hc⟩
      · subst hn
        exact absurd hp.symm (Nat.succ_ne_zero v.length)
      · rw [List.concat_eq_append] at hc
        subst hc
        rw [List.length_append, List.length_singleton, List.length_cons] at hp
        rw [List.append_assoc, List.singleton_append] at hy
        have hv := (foldl_extStepC_toExt (childUpd target k (edgeB edge y target)) p' 0
          ⟨init, 0, ⟨.before, 0, 0, 0, true⟩⟩ EliasTree.valid_init).1
        rw [Nat.zero_add] at hv
        have hk : p'.length < y.length := by
          rw [hy, List.length_append, List.length_cons]
          omega
        have hpos : (foldC edge y target k p').pos = p'.length := by
          rw [foldC, foldl_extStepC_pos]
          exact Nat.zero_add _
        have hb := foldC_bounded edge y target k p'
        funext l
        rw [regsC_cons, ih p' (c :: r) hy (by omega), foldC_concat]
        change (childStep edge i l).sem (stepAtC v y (c :: r) _ _ target k) =
          encodeC y r (advance _ c)
            (childUpd target k (edgeB edge y target) (foldC edge y target k p').pos _ _) l
        rw [hpos]
        exact step_encodeC v y r _ _ target k c _ hv hk p' hy hb htp hkl edge i l) u

/-- The expression's value is the scan's flag: for a node with the label at a
location within the word and an arity within the word's length. -/
theorem childScanExprSem_eq (edge : LOf 6) (y : List Bool) (target : Loc) (k : ℕ)
    (htp : target.pos ≤ y.length) (hkl : k ≤ y.length) :
    (childScanExpr edge).sem ![y, y.drop target.pos, y.drop (target.len + 1), y.drop k] =
      boolWord (childScan target k (edgeB edge y target) y).extra.ok := by
  rw [childScanExpr, sem_compL]
  have hargs : (fun i ↦ (![projL 4 0, projL 4 0, projL 4 1, projL 4 2, projL 4 3] i).sem
      ![y, y.drop target.pos, y.drop (target.len + 1), y.drop k]) =
      Fin.cons y ![y, y.drop target.pos, y.drop (target.len + 1), y.drop k] :=
    funext fun i ↦ match i with | 0 | 1 | 2 | 3 | 4 => rfl
  rw [hargs]
  have h := regsC_eq edge y y target k htp hkl y [] (List.append_nil y).symm rfl
  have h11 := congrFun h 11
  change (childReg edge 11).sem _ = boolWord (foldC edge y target k y).extra.ok at h11
  rw [h11]
  have he : (foldC edge y target k y).extra =
      (childScan target k (edgeB edge y target) y).extra := by
    have := (foldl_extStepC_toExt (childUpd target k (edgeB edge y target)) y 0
      ⟨init, 0, ⟨.before, 0, 0, 0, true⟩⟩ EliasTree.valid_init).2
    exact congrArg Ext.extra this
  rw [he]

end

end Geb.SizeBounded.Logspace.WTree.ChildExpr
