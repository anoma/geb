/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.SuffixCounter
public import Geb.Prototypes.Computability.SizeBounded.Logspace.EliasTree.Scanner

set_option doc.verso true in
/-!
# The Elias-length tree recognizer as a successor-free expression

The recognizer of the Elias-length tree encoding, {lit}`Geb.BitTree.Elias.validBool`,
as an expression of the logspace subalgebra {name}`Geb.SizeBounded.Logspace.LOf`.
The expression is a simultaneous recursion with seven registers, run over the
input word as the counter with the word as the parameter, as
{lit}`Geb.SizeBounded.isBitTree` runs its three: the unread input, shortened by
one bit per step; the phase of {name}`Geb.SizeBounded.Logspace.EliasTree.advance`
as a three-bit code, the abandoned phase being the empty word; and the five
counters of {name}`Geb.SizeBounded.Logspace.EliasTree.Counters`, each the word
dropped by its number, {lit}`Geb.Prototypes.Computability.SizeBounded.Logspace.SuffixCounter`.
A counter rises by the tail and is compared by a drop, a value takes a bit by
the doubling, and no counter falls, which is what the absence of a successor
requires. The step reads the current bit from the head of the unread input.

# Main definitions

* {lit}`restVar`, {lit}`modeVar`, {lit}`forksVar`, {lit}`leavesVar`,
  {lit}`widthVar`, {lit}`countVar`, {lit}`valueVar`, {lit}`wordVar` — the
  registers and the parameter of the step environment.
* {lit}`phaseCode`, {lit}`code9`, {lit}`onPhase`, {lit}`onBit` — the codes of
  the phases, and the dispatch on the phase register and on the current bit.
* {lit}`fieldEnd`, {lit}`rootEnd`, {lit}`finishMode` — the two comparisons and
  the phase after a completed leaf.
* {lit}`modeStep`, {lit}`forksStep`, {lit}`leavesStep`, {lit}`widthStep`,
  {lit}`countStep`, {lit}`valueStep` — the six counter steps.
* {lit}`treeBase`, {lit}`treeStep`, {lit}`treeReg` — the recursion's bases and
  steps, and its registers as expressions of arity two.
* {lit}`accept`, {lit}`isEliasTree` — the acceptance test on the phase
  register, and the recognizer of arity one.
* {lit}`encode`, {lit}`stepAt` — the registers holding a remaining word and
  the counters, and the step environment holding them and the word.

# Main statements

* {lit}`stepAt_one` to {lit}`stepAt_eight` — the slots of the step environment.
* {lit}`sem_onPhase`, {lit}`sem_onBit`, {lit}`sem_fieldEnd`,
  {lit}`sem_rootEnd` — the meanings of the dispatches and the comparisons.
* {lit}`cond4Sem_same` — a conditional with equal branches on the head bit
  tests emptiness.

# References

* \[Kristiansen2005\]
* \[Elias1975\]

# Tags

logspace, simultaneous recursion on notation, Elias delta code, binary tree,
recognizer
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.EliasTree

public section

/-- The unread input, slot one of the step environment. -/
@[expose] def restVar : LOf 9 := projL 9 1

/-- The phase register, slot two. -/
@[expose] def modeVar : LOf 9 := projL 9 2

/-- The forks counter, slot three. -/
@[expose] def forksVar : LOf 9 := projL 9 3

/-- The leaves counter, slot four. -/
@[expose] def leavesVar : LOf 9 := projL 9 4

/-- The width, slot five. -/
@[expose] def widthVar : LOf 9 := projL 9 5

/-- The count, slot six. -/
@[expose] def countVar : LOf 9 := projL 9 6

/-- The value, slot seven. -/
@[expose] def valueVar : LOf 9 := projL 9 7

/-- The whole word, the parameter in slot eight. -/
@[expose] def wordVar : LOf 9 := projL 9 8

/-- The three-bit code of a phase; the abandoned phase is the empty word. -/
@[expose] def phaseCode : Phase → List Bool
  | .tree => [true, true, true]
  | .header => [true, true, false]
  | .zeros => [true, false, true]
  | .size => [true, false, false]
  | .length => [false, true, true]
  | .payload => [false, true, false]
  | .done => [false, false, true]
  | .dead => []

/-- A phase's code as a constant of the step arity. -/
@[expose] def code9 (p : Phase) : LOf 9 := constL 9 (phaseCode p)

/-- Dispatch on the phase register: the empty code is the abandoned phase, and
the three bits of the other codes select among the seven live phases. -/
@[expose] def onPhase (tree header zeros size length payload done dead : LOf 9) : LOf 9 :=
  cond4L modeVar dead
    (cond4L (tailAppL modeVar) dead
      (cond4L (tailAppL (tailAppL modeVar)) dead tree header)
      (cond4L (tailAppL (tailAppL modeVar)) dead zeros size))
    (cond4L (tailAppL modeVar) dead
      (cond4L (tailAppL (tailAppL modeVar)) dead length payload)
      (cond4L (tailAppL (tailAppL modeVar)) dead done dead))

/-- Dispatch on the current bit, the head of the unread input: the first
expression on no input, the second on a {lit}`true` bit, the third on a
{lit}`false` one. -/
@[expose] def onBit (e t f : LOf 9) : LOf 9 := cond4L restVar e t f

/-- The current field is complete after this bit: the count raised by one
reaches the width, tested as the width's end segment dropped by the raised
count's end segment being empty. -/
@[expose] def fieldEnd : LOf 9 := dropByApp widthVar (tailAppL countVar)

/-- The root is complete at this leaf: the leaves reach the forks. -/
@[expose] def rootEnd : LOf 9 := dropByApp forksVar leavesVar

/-- The phase after a completed leaf: done when the root is complete, the tree
phase otherwise. -/
@[expose] def finishMode : LOf 9 := cond4L rootEnd (code9 .done) (code9 .tree) (code9 .tree)

/-- The phase step. -/
@[expose] def modeStep : LOf 9 :=
  onPhase (onBit modeVar (code9 .tree) (code9 .header))
    (onBit modeVar finishMode (code9 .zeros))
    (onBit modeVar (code9 .size) (code9 .zeros))
    (cond4L fieldEnd (code9 .length) (code9 .size) (code9 .size))
    (cond4L fieldEnd (code9 .payload) (code9 .length) (code9 .length))
    (cond4L fieldEnd finishMode (code9 .payload) (code9 .payload))
    (code9 .dead) (code9 .dead)

/-- The forks step: a fork tag raises the counter. -/
@[expose] def forksStep : LOf 9 :=
  onPhase (onBit forksVar (tailAppL forksVar) forksVar) forksVar forksVar forksVar forksVar
    forksVar forksVar forksVar

/-- The leaves step: a completed leaf raises the counter. -/
@[expose] def leavesStep : LOf 9 :=
  onPhase leavesVar (onBit leavesVar (tailAppL leavesVar) leavesVar) leavesVar leavesVar
    leavesVar (cond4L fieldEnd (tailAppL leavesVar) leavesVar leavesVar) leavesVar leavesVar

/-- The value taking the current bit. -/
@[expose] def bitValue : LOf 9 :=
  onBit valueVar (bitApp true valueVar wordVar) (bitApp false valueVar wordVar)

/-- The width step: a zero run starts at one and rises by one per zero, and a
completed size or length field makes its value the next field's bound. -/
@[expose] def widthStep : LOf 9 :=
  onPhase widthVar (onBit widthVar widthVar (tailAppL wordVar))
    (onBit widthVar widthVar (tailAppL widthVar))
    (cond4L fieldEnd bitValue widthVar widthVar)
    (cond4L fieldEnd bitValue widthVar widthVar)
    widthVar widthVar widthVar

/-- The count step: from zero in the size field, from one in the length field
and the payload, rising by one per bit. -/
@[expose] def countStep : LOf 9 :=
  onPhase countVar countVar (onBit countVar wordVar countVar)
    (cond4L fieldEnd (tailAppL wordVar) (tailAppL countVar) (tailAppL countVar))
    (cond4L fieldEnd (tailAppL wordVar) (tailAppL countVar) (tailAppL countVar))
    (tailAppL countVar) countVar countVar

/-- The value step: one at the start of a field, taking each bit of the size
and length fields. -/
@[expose] def valueStep : LOf 9 :=
  onPhase valueVar valueVar (onBit valueVar (tailAppL wordVar) valueVar)
    (cond4L fieldEnd (tailAppL wordVar) bitValue bitValue)
    bitValue valueVar valueVar valueVar

/-- The recursion's bases: the whole word, the code of the tree phase, and the
word for each counter at zero. -/
@[expose] def treeBase : Fin 7 → LOf 1 :=
  ![projL 1 0, constL 1 (phaseCode .tree), projL 1 0, projL 1 0, projL 1 0, projL 1 0,
    projL 1 0]

/-- The recursion's steps, the same for either bit of the counter. -/
@[expose, nolint unusedArguments] def treeStep : Bool → Fin 7 → LOf 9 :=
  fun _ ↦ ![tailAppL restVar, modeStep, forksStep, leavesStep, widthStep, countStep, valueStep]

/-- The seven registers, as expressions of arity two: the counter and the
word. -/
@[expose] def treeReg (l : Fin 7) : LOf 2 := srnL treeBase treeStep l

/-- The acceptance test: {lit}`[true]` when the phase register holds the code
of the completed phase, the empty word otherwise. -/
@[expose] def accept : LOf 2 :=
  cond4L (treeReg 1) (constL 2 []) (constL 2 [])
    (cond4L (tailAppL (treeReg 1)) (constL 2 []) (constL 2 [])
      (cond4L (tailAppL (tailAppL (treeReg 1))) (constL 2 []) (constL 2 [true]) (constL 2 [])))

/-- The recognizer: the acceptance test with the word as counter and
parameter. -/
@[expose] def isEliasTree : LOf 1 := diagL accept

/-- The registers holding a remaining word and counters at a word: the phase
code and the word dropped by each counter. -/
@[expose] def encode (y r : List Bool) (x : Counters) : Fin 7 → List Bool :=
  ![r, phaseCode x.phase, y.drop x.forks, y.drop x.leaves, y.drop x.width, y.drop x.count,
    y.drop x.value]

/-- The step environment at a level, holding the registers and the word. -/
@[expose] def stepAt (u y r : List Bool) (x : Counters) : Fin 9 → List Bool :=
  stepEnv u (encode y r x) ![y]

/-- Slot one is the remaining word. -/
theorem stepAt_one (u y r : List Bool) (x : Counters) : stepAt u y r x 1 = r := rfl

/-- Slot two is the phase code. -/
theorem stepAt_two (u y r : List Bool) (x : Counters) : stepAt u y r x 2 = phaseCode x.phase :=
  rfl

/-- Slot three is the forks counter. -/
theorem stepAt_three (u y r : List Bool) (x : Counters) : stepAt u y r x 3 = y.drop x.forks :=
  rfl

/-- Slot four is the leaves counter. -/
theorem stepAt_four (u y r : List Bool) (x : Counters) : stepAt u y r x 4 = y.drop x.leaves :=
  rfl

/-- Slot five is the width. -/
theorem stepAt_five (u y r : List Bool) (x : Counters) : stepAt u y r x 5 = y.drop x.width :=
  rfl

/-- Slot six is the count. -/
theorem stepAt_six (u y r : List Bool) (x : Counters) : stepAt u y r x 6 = y.drop x.count :=
  rfl

/-- Slot seven is the value. -/
theorem stepAt_seven (u y r : List Bool) (x : Counters) : stepAt u y r x 7 = y.drop x.value :=
  rfl

/-- Slot eight is the word. -/
theorem stepAt_eight (u y r : List Bool) (x : Counters) : stepAt u y r x 8 = y := rfl

/-- A conditional whose two head-bit branches agree tests the emptiness of its
scrutinee. -/
theorem cond4Sem_same (s e t : List Bool) : cond4Sem s e t t = if s = [] then e else t := by
  cases s with
  | nil => rfl
  | cons c cs => cases c <;> rfl

/-- The dispatch on a phase code selects the expression of that phase. -/
theorem sem_onPhase (tree header zeros size length payload done dead : LOf 9)
    (x : Fin 9 → List Bool) (p : Phase) (hx : x 2 = phaseCode p) :
    (onPhase tree header zeros size length payload done dead).sem x =
      (match p with
        | .tree => tree
        | .header => header
        | .zeros => zeros
        | .size => size
        | .length => length
        | .payload => payload
        | .done => done
        | .dead => dead).sem x := by
  simp only [onPhase, sem_cond4L, sem_tailAppL, modeVar, sem_projL, hx]
  cases p <;> rfl

/-- The dispatch on the current bit selects by that bit. -/
theorem sem_onBit (e t f : LOf 9) (x : Fin 9 → List Bool) (b : Bool) (r : List Bool)
    (hx : x 1 = b :: r) : (onBit e t f).sem x = (if b then t else f).sem x := by
  simp only [onBit, sem_cond4L, restVar, sem_projL, hx]
  cases b <;> rfl

/-- The field-end test's meaning. -/
theorem sem_fieldEnd (x : Fin 9 → List Bool) :
    fieldEnd.sem x = (x 6).tail.drop (x 5).length := by
  simp only [fieldEnd, sem_dropByApp, sem_tailAppL, widthVar, countVar, sem_projL]

/-- The root-end test's meaning. -/
theorem sem_rootEnd (x : Fin 9 → List Bool) : rootEnd.sem x = (x 4).drop (x 3).length := by
  simp only [rootEnd, sem_dropByApp, forksVar, leavesVar, sem_projL]

end

end Geb.SizeBounded.Logspace.EliasTree
