/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.EliasTree.Expr
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Events

set_option doc.verso true in
/-!
# Extending the Elias-length tree expression by further registers

The recognizers of the W-trees of a coded signature are simultaneous
recursions whose registers are the seven of
{name}`Geb.SizeBounded.Logspace.EliasTree.treeReg`, the monotone counters of
the Elias-length tree scanner, and further registers updated at the events
of {lit}`Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Events`. This
module supplies what the extension needs: the events read off the counters,
{lit}`eventC`, agreeing with those read off the scanner's state; the seven
steps lifted to a step arity with more registers and parameters,
{lit}`liftBy`, so that their step lemmas apply unchanged; the dispatches on
the phase register and on the current bit at any arity; and
{lit}`eventStep`, a register step given by its value at each event, whose
meaning on a step environment holding encoded counters is the value at the
event of the current bit.

# Main definitions

* {lit}`eventC` — the event a bit raises at the counters.
* {lit}`ExtC`, {lit}`extStepC`, {lit}`ExtC.toExt` — the counters with a
  position and a register updated at events, and the projection to the
  scanner's state.
* {lit}`liftBy` — an expression of the Elias step arity at a larger arity.
* {lit}`onPhaseAt`, {lit}`onBitAt`, {lit}`isDone` — the dispatches on a phase
  register and on a remaining-input register, and the test of the completed
  phase, at any arity.
* {lit}`eventStep` — a register step by its values at the events.
* {lit}`boolWord`, {lit}`isTrueWord`, {lit}`flagOf`, {lit}`andOkAt` — a flag
  as a word, a word read as a flag, the reading as an expression, and the
  conjunction with a flag register.
* {lit}`addSeg` — the sum of two counters held as end segments of the word.
* {lit}`eqSeg`, {lit}`isZeroSeg` — the equality test of two counters held as
  end segments, and the test of one at zero.
* {lit}`lenAfterHeaderAt` — the length counter a completed length field
  yields.

# Main statements

* {lit}`eventC_eq_eventS` — the counters' event is the state's, on valid
  counters.
* {lit}`eventC_payload_of_done`, {lit}`eventC_payload_of_not_done` — the
  payload length a completed header carries: zero when the leaf completes
  with it, otherwise the value taking the current bit, less one.
* {lit}`eventC_cases` — the six shapes an event takes.
* {lit}`extStepC_toExt`, {lit}`foldl_extStepC_toExt` — the projection commutes
  with one bit and with a word.
* {lit}`foldl_extStepC_counters`, {lit}`foldl_extStepC_pos` — the counters
  and the position of the extended fold.
* {lit}`sem_liftBy` — the meaning of a lifted expression.
* {lit}`sem_onPhaseAt`, {lit}`sem_onBitAt`, {lit}`sem_isDone` — the meanings
  of the dispatches and the test.
* {lit}`sem_eventStep` — the meaning of an event-driven step on encoded
  counters.
* {lit}`sem_flagOf`, {lit}`cond4Sem_boolWord`, {lit}`cond4Sem_boolWord_same`,
  {lit}`sem_addSeg`, {lit}`sem_eqSeg`, {lit}`sem_isZeroSeg`,
  {lit}`cond4Sem_drop_length_sub`,
  {lit}`sem_lenAfterHeaderAt` — the meanings of the flag, comparison and
  counter expressions.

# References

* \[Kristiansen2005\]

# Tags

logspace, simultaneous recursion on notation, Elias delta code, event
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree

open Geb.BitTree.Elias.Scanner (Mode State step finish)
open EliasTree (Phase Counters Valid advance finishC toState phaseCode)

public section

/-- The event a bit raises at the counters: the tags in the tree phase, the
header of an empty payload completing with its leaf, the last bit of the
length field completing the header with the payload length it carries, and
the last bit of the payload completing the leaf. -/
@[expose] def eventC (x : Counters) (b : Bool) : Event :=
  match x.phase, b with
  | .tree, true => ⟨true, false, none, false⟩
  | .tree, false => ⟨false, true, none, false⟩
  | .header, true => ⟨false, false, some 0, true⟩
  | .length, b =>
    if x.count + 1 = x.width then ⟨false, false, some (2 * x.value + b.toNat - 1), false⟩
    else .silent
  | .payload, _ => if x.count + 1 = x.width then ⟨false, false, none, true⟩ else .silent
  | _, _ => .silent

/-- The counters' event is the state's. -/
theorem eventC_eq_eventS (k : ℕ) (x : Counters) (b : Bool) (h : Valid k x) :
    eventC x b = eventS (toState x) b := by
  rcases x with ⟨ph, f, l, z, c, v⟩
  cases ph <;> cases b <;> simp only [Valid] at h <;>
    simp only [eventC, toState, EliasTree.modeOf, eventS, Nat.bit_val]
  all_goals first
    | rfl
    | (rw [if_neg (show ¬z = 0 by omega)])
    | (by_cases he : c + 1 = z
       · rw [if_pos he, if_pos (show z - c = 1 by omega)]
       · rw [if_neg he, if_neg (show ¬z - c = 1 by omega)])

/-- A header completing with its leaf is the header of an empty payload. -/
theorem eventC_payload_of_done (x : Counters) (c : Bool) (L : ℕ)
    (h : (eventC x c).payload = some L) (hd : (eventC x c).done = true) : L = 0 := by
  rcases x with ⟨ph, f, l, z, cnt, v⟩
  cases ph <;> cases c <;> simp only [eventC, Event.silent] at h hd <;> (try split_ifs at h hd) <;>
    first
      | exact hd.elim
      | exact absurd hd (by decide)
      | (cases h; rfl)

/-- A header completing without its leaf carries the payload length the value
takes with the current bit, less one. -/
theorem eventC_payload_of_not_done (k : ℕ) (x : Counters) (c : Bool) (L : ℕ) (hv : Valid k x)
    (h : (eventC x c).payload = some L) (hd : (eventC x c).done = false) :
    L + 1 = 2 * x.value + c.toNat := by
  rcases x with ⟨ph, f, l, z, cnt, v⟩
  cases ph <;> cases c <;> simp only [Valid] at hv <;> simp only [eventC, Event.silent] at h hd <;>
    (try split_ifs at h hd) <;>
    first
      | exact hd.elim
      | exact absurd hd (by decide)
      | (cases h <;> dsimp only <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega)

/-- The six shapes an event takes: the two tags, the header of an empty
payload completing with its leaf, a header completing without its leaf, a
leaf completing, and no event. -/
theorem eventC_cases (x : Counters) (c : Bool) :
    eventC x c = ⟨true, false, none, false⟩ ∨ eventC x c = ⟨false, true, none, false⟩ ∨
      eventC x c = ⟨false, false, some 0, true⟩ ∨
        (∃ L, eventC x c = ⟨false, false, some L, false⟩) ∨
          eventC x c = ⟨false, false, none, true⟩ ∨ eventC x c = .silent := by
  rcases x with ⟨ph, f, l, z, cnt, v⟩
  cases ph <;> cases c <;> dsimp only [eventC] <;> (try split_ifs) <;>
    first
      | exact Or.inl rfl
      | exact Or.inr (Or.inl rfl)
      | exact Or.inr (Or.inr (Or.inl rfl))
      | exact Or.inr (Or.inr (Or.inr (Or.inl ⟨_, rfl⟩)))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
      | exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr rfl))))

/-- The counters with the number of bits read and a register. -/
structure ExtC (α : Type) where
  /-- The counters. -/
  counters : Counters
  /-- The number of bits read. -/
  pos : ℕ
  /-- The register. -/
  extra : α

/-- One bit: the counters advance, the position advances, and the register is
updated by the event, at the position of the bit. -/
@[expose] def extStepC {α : Type} (upd : ℕ → Event → α → α) (s : ExtC α) (b : Bool) : ExtC α :=
  ⟨advance s.counters b, s.pos + 1, upd s.pos (eventC s.counters b) s.extra⟩

/-- The projection to the scanner's state. -/
@[expose] def ExtC.toExt {α : Type} (s : ExtC α) : Ext α := ⟨toState s.counters, s.pos, s.extra⟩

/-- The projection commutes with one bit on valid counters. -/
theorem extStepC_toExt {α : Type} (upd : ℕ → Event → α → α) (k : ℕ) (s : ExtC α) (b : Bool)
    (h : Valid k s.counters) : (extStepC upd s b).toExt = extStep upd s.toExt b := by
  unfold extStepC extStep ExtC.toExt
  rw [EliasTree.toState_advance k s.counters b h, eventC_eq_eventS k s.counters b h]

/-- The projection commutes with a word: after the word, the counters are valid
at the bits read and project to the scanner's state. -/
theorem foldl_extStepC_toExt {α : Type} (upd : ℕ → Event → α → α) (p : List Bool) :
    ∀ (k : ℕ) (s : ExtC α), Valid k s.counters →
      Valid (k + p.length) (p.foldl (extStepC upd) s).counters ∧
        (p.foldl (extStepC upd) s).toExt = p.foldl (extStep upd) s.toExt :=
  List.rec (fun k s h ↦ ⟨h, rfl⟩) (fun b p ih k s h ↦ by
    obtain ⟨hv, he⟩ := ih (k + 1) (extStepC upd s b) (EliasTree.valid_advance k s.counters b h)
    rw [List.foldl_cons, List.foldl_cons, List.length_cons, ← extStepC_toExt upd k s b h,
      show k + (p.length + 1) = k + 1 + p.length by omega]
    exact ⟨hv, he⟩) p

/-- The counters of the extended fold are the counters' fold. -/
theorem foldl_extStepC_counters {α : Type} (upd : ℕ → Event → α → α) (p : List Bool) :
    ∀ s : ExtC α, (p.foldl (extStepC upd) s).counters = p.foldl advance s.counters :=
  List.rec (fun _ ↦ rfl) (fun b p ih s ↦ by rw [List.foldl_cons, List.foldl_cons, ih]; rfl) p

/-- The position of the extended fold advances by the word's length. -/
theorem foldl_extStepC_pos {α : Type} (upd : ℕ → Event → α → α) (p : List Bool) :
    ∀ s : ExtC α, (p.foldl (extStepC upd) s).pos = s.pos + p.length :=
  List.rec (fun _ ↦ rfl) (fun b p ih s ↦ by
    rw [List.foldl_cons, ih, List.length_cons]
    change s.pos + 1 + p.length = _
    omega) p

/-- An expression of the Elias step arity at a larger arity, its variables
read through an embedding of the slots. -/
@[expose] def liftBy {n : ℕ} (f : Fin 9 → Fin n) (e : LOf 9) : LOf n :=
  compL e fun i ↦ projL n (f i)

/-- The meaning of a lifted expression. -/
theorem sem_liftBy {n : ℕ} (f : Fin 9 → Fin n) (e : LOf 9) (x : Fin n → List Bool) :
    (liftBy f e).sem x = e.sem (x ∘ f) := rfl

/-- Dispatch on a phase register: the empty code is the abandoned phase, and
the three bits of the other codes select among the seven live phases, as
{name}`Geb.SizeBounded.Logspace.EliasTree.onPhase` does at its arity. -/
@[expose] def onPhaseAt {n : ℕ} (mode tree header zeros size length payload done dead : LOf n) :
    LOf n :=
  cond4L mode dead
    (cond4L (tailAppL mode) dead
      (cond4L (tailAppL (tailAppL mode)) dead tree header)
      (cond4L (tailAppL (tailAppL mode)) dead zeros size))
    (cond4L (tailAppL mode) dead
      (cond4L (tailAppL (tailAppL mode)) dead length payload)
      (cond4L (tailAppL (tailAppL mode)) dead done dead))

/-- The dispatch on a phase code selects the expression of that phase. -/
theorem sem_onPhaseAt {n : ℕ} (mode tree header zeros size length payload done dead : LOf n)
    (x : Fin n → List Bool) (p : Phase) (hx : mode.sem x = phaseCode p) :
    (onPhaseAt mode tree header zeros size length payload done dead).sem x =
      (match p with
        | .tree => tree
        | .header => header
        | .zeros => zeros
        | .size => size
        | .length => length
        | .payload => payload
        | .done => done
        | .dead => dead).sem x := by
  simp only [onPhaseAt, sem_cond4L, sem_tailAppL, hx]
  cases p <;> rfl

/-- Dispatch on the current bit, the head of a remaining-input register: the
first expression on no input, the second on a {lit}`true` bit, the third on
a {lit}`false` one. -/
@[expose] def onBitAt {n : ℕ} (rest e t f : LOf n) : LOf n := cond4L rest e t f

/-- The dispatch on the current bit selects by that bit. -/
theorem sem_onBitAt {n : ℕ} (rest e t f : LOf n) (x : Fin n → List Bool) (b : Bool)
    (r : List Bool) (hx : rest.sem x = b :: r) :
    (onBitAt rest e t f).sem x = (if b then t else f).sem x := by
  simp only [onBitAt, sem_cond4L, hx]
  cases b <;> rfl

/-- The test of the completed phase on a phase register: {lit}`[true]` when
the register holds the code of the completed phase, the empty word otherwise,
as {name}`Geb.SizeBounded.Logspace.EliasTree.accept` tests at its arity. -/
@[expose] def isDone {n : ℕ} (mode : LOf n) : LOf n :=
  cond4L mode (constL n []) (constL n [])
    (cond4L (tailAppL mode) (constL n []) (constL n [])
      (cond4L (tailAppL (tailAppL mode)) (constL n []) (constL n [true]) (constL n [])))

/-- The test's meaning on a phase code. -/
theorem sem_isDone {n : ℕ} (mode : LOf n) (x : Fin n → List Bool) (p : Phase)
    (hx : mode.sem x = phaseCode p) :
    (isDone mode).sem x = if p = .done then [true] else [] := by
  simp only [isDone, sem_cond4L, sem_tailAppL, sem_constL, hx]
  cases p <;> rfl

/-- A flag as a word: {lit}`[true]` or the empty word. -/
@[expose] def boolWord (b : Bool) : List Bool := if b then [true] else []

/-- A word read as a flag: set when its head is {lit}`true`. -/
@[expose] def isTrueWord : List Bool → Bool
  | true :: _ => true
  | _ => false

/-- A flag read back is itself. -/
theorem isTrueWord_boolWord (b : Bool) : isTrueWord (boolWord b) = b := by cases b <;> rfl

/-- The reading of a word as a flag, as an expression. -/
@[expose] def flagOf {n : ℕ} (e : LOf n) : LOf n :=
  cond4L e (constL n []) (constL n [true]) (constL n [])

/-- The meaning of the reading. -/
theorem sem_flagOf {n : ℕ} (e : LOf n) (x : Fin n → List Bool) :
    (flagOf e).sem x = boolWord (isTrueWord (e.sem x)) := by
  rw [flagOf, sem_cond4L]
  cases h : e.sem x with
  | nil => rfl
  | cons b bs => cases b <;> rfl

/-- The conjunction of two flags as words. -/
theorem cond4Sem_boolWord (ok b : Bool) :
    cond4Sem (boolWord ok) [] (boolWord b) (boolWord b) = boolWord (ok && b) := by
  cases ok <;> cases b <;> rfl

/-- A conditional on a flag whose two head-bit branches agree selects by the
flag. -/
theorem cond4Sem_boolWord_same (b : Bool) (e t : List Bool) :
    cond4Sem (boolWord b) e t t = if b then t else e := by
  cases b <;> rfl

/-- The conjunction of a flag register with a flag, as an expression. -/
@[expose] def andOkAt {n : ℕ} (ok e : LOf n) : LOf n := cond4L ok (constL n []) e e

/-- The equality test of two counters held as end segments of the word:
{lit}`[true]` when each dropped by the other's length is empty. -/
@[expose] def eqSeg {n : ℕ} (a b : LOf n) : LOf n :=
  cond4L (dropByApp a b) (cond4L (dropByApp b a) (constL n [true]) (constL n []) (constL n []))
    (constL n []) (constL n [])

/-- The equality test decides equality of the counters, below the word's
length. -/
theorem sem_eqSeg {n : ℕ} (a b : LOf n) (x : Fin n → List Bool) (y : List Bool) (A B : ℕ)
    (ha : a.sem x = y.drop A) (hb : b.sem x = y.drop B) (hA : A ≤ y.length) (hB : B ≤ y.length) :
    (eqSeg a b).sem x = boolWord (decide (A = B)) := by
  simp only [eqSeg, sem_cond4L, sem_dropByApp, sem_constL, ha, hb, EliasTree.cond4Sem_same,
    List.drop_eq_nil_iff, List.length_drop]
  by_cases h : A = B
  · subst h
    rw [if_pos (Nat.le_refl _), if_pos (Nat.le_refl _), decide_eq_true rfl]
    rfl
  · rw [decide_eq_false h]
    by_cases h₁ : y.length - B ≤ y.length - A
    · rw [if_pos h₁, if_neg (show ¬y.length - A ≤ y.length - B by omega)]
      rfl
    · rw [if_neg h₁]
      rfl

/-- The word dropped by a number and by another cut off at the word's length
is the word dropped by their sum. -/
theorem drop_add_min (y : List Bool) (V P : ℕ) : y.drop (V + min P y.length) = y.drop (V + P) := by
  rcases Nat.le_total P y.length with h | h
  · rw [Nat.min_eq_left h]
  · rw [Nat.min_eq_right h, List.drop_of_length_le (by omega), List.drop_of_length_le (by omega)]

/-- The sum of two counters held as end segments of the word: the second
dropped by the first's number, the latter cut off at the word's length. -/
@[expose] def addSeg {n : ℕ} (p v w : LOf n) : LOf n := dropByApp (dropByApp p w) v

/-- The sum's meaning. -/
theorem sem_addSeg {n : ℕ} (p v w : LOf n) (x : Fin n → List Bool) (y : List Bool) (P V : ℕ)
    (hp : p.sem x = y.drop P) (hv : v.sem x = y.drop V) (hw : w.sem x = y) :
    (addSeg p v w).sem x = y.drop (V + P) := by
  rw [addSeg, sem_dropByApp, sem_dropByApp, hp, hv, hw, List.length_drop, List.length_drop,
    List.drop_drop, show y.length - (y.length - P) = min P y.length by omega, drop_add_min]

/-- The test of a counter held as an end segment of the word at zero: the word
dropped by the segment's length, empty exactly then. -/
@[expose] def isZeroSeg {n : ℕ} (a word : LOf n) : LOf n := dropByApp a word

/-- The test's meaning: the word dropped by all but the counter. -/
theorem sem_isZeroSeg {n : ℕ} (a word : LOf n) (x : Fin n → List Bool) (y : List Bool) (A : ℕ)
    (ha : a.sem x = y.drop A) (hw : word.sem x = y) :
    (isZeroSeg a word).sem x = y.drop (y.length - A) := by
  rw [isZeroSeg, sem_dropByApp, ha, hw, List.length_drop]

/-- The word dropped by all but a counter is empty exactly when the counter is
zero, below the word's length. -/
theorem drop_length_sub_eq_nil_iff (y : List Bool) (A : ℕ) (hA : A ≤ y.length) :
    y.drop (y.length - A) = [] ↔ A = 0 := by
  rw [List.drop_eq_nil_iff]
  constructor
  · intro h
    omega
  · intro h
    omega

/-- A conditional on the zero test whose two head-bit branches agree selects by
the test. -/
theorem cond4Sem_drop_length_sub (y : List Bool) (A : ℕ) (hA : A ≤ y.length) (e t : List Bool) :
    cond4Sem (y.drop (y.length - A)) e t t = if A = 0 then e else t := by
  simp only [EliasTree.cond4Sem_same, drop_length_sub_eq_nil_iff y A hA]

/-- The length counter a completed length field yields: the value taking the
current bit, the word dropped by one more than the payload's length. -/
@[expose] def lenAfterHeaderAt {n : ℕ} (rest value word : LOf n) : LOf n :=
  onBitAt rest value (bitApp true value word) (bitApp false value word)

/-- The length counter's meaning. -/
theorem sem_lenAfterHeaderAt {n : ℕ} (rest value word : LOf n) (x : Fin n → List Bool)
    (y r : List Bool) (c : Bool) (v : ℕ) (hrest : rest.sem x = c :: r)
    (hvalue : value.sem x = y.drop v) (hword : word.sem x = y) :
    (lenAfterHeaderAt rest value word).sem x = y.drop (2 * v + c.toNat) := by
  rw [lenAfterHeaderAt, sem_onBitAt _ _ _ _ _ c r hrest]
  cases c <;> simp only [↓reduceIte, Bool.false_eq_true, sem_bitApp, hvalue, hword, bitSem_drop]

/-- A register step by its values at the events: at a fork tag, at a leaf tag,
at the header of an empty payload completing with its leaf, at the last bit
of a length field, at the last bit of a payload, and at no event. The phase
register, the remaining-input register, and the field-end test are given, the
last as the comparison of the width and count registers. -/
@[expose] def eventStep {n : ℕ} (mode rest fieldEnd fork tag headerDone lengthEnd payloadDone dflt :
    LOf n) : LOf n :=
  onPhaseAt mode
    (onBitAt rest dflt fork tag)
    (onBitAt rest dflt headerDone dflt)
    dflt dflt
    (cond4L fieldEnd lengthEnd dflt dflt)
    (cond4L fieldEnd payloadDone dflt dflt)
    dflt dflt

/-- The value of an event-driven step at an event. -/
@[expose] def eventValue {n : ℕ} (fork tag headerDone lengthEnd payloadDone dflt : LOf n)
    (e : Event) : LOf n :=
  if e.fork then fork
  else if e.tag then tag
  else match e.payload, e.done with
    | some _, true => headerDone
    | some _, false => lengthEnd
    | none, true => payloadDone
    | none, false => dflt

/-- The meaning of an event-driven step on a step environment holding encoded
counters: the value at the event of the current bit. The phase register holds
the phase's code, the remaining-input register the current bit and the rest,
and the width and count registers the word dropped by the counters, which are
valid and below the word's length. -/
theorem sem_eventStep {n : ℕ} (mode rest fieldEnd fork tag headerDone lengthEnd payloadDone dflt :
    LOf n) (x : Fin n → List Bool) (y r : List Bool) (c : Bool) (z : Counters) (k : ℕ)
    (hv : Valid k z) (hk : k < y.length) (hmode : mode.sem x = phaseCode z.phase)
    (hrest : rest.sem x = c :: r)
    (hfe : fieldEnd.sem x = (y.drop z.count).tail.drop (y.drop z.width).length) :
    (eventStep mode rest fieldEnd fork tag headerDone lengthEnd payloadDone dflt).sem x =
      (eventValue fork tag headerDone lengthEnd payloadDone dflt (eventC z c)).sem x := by
  rw [eventStep, sem_onPhaseAt _ _ _ _ _ _ _ _ _ x z.phase hmode]
  rcases z with ⟨ph, f, l, w, cnt, v⟩
  simp only at hmode hfe
  cases ph <;> cases c <;> simp only [Valid] at hv <;> by_cases he : w = cnt + 1 <;>
    (try have he' : ¬cnt + 1 = w := fun h ↦ he h.symm) <;>
    (try have hle : w ≤ cnt + 1 := by omega) <;> (try have hnle : ¬w ≤ cnt + 1 := by omega) <;>
    (try have hb : cnt + 1 < y.length := by omega) <;>
    simp only [eventC, eventValue, Event.silent, sem_onBitAt _ _ _ _ x _ r hrest, ↓reduceIte,
      Bool.false_eq_true, sem_cond4L, EliasTree.cond4Sem_same, List.tail_drop,
      drop_drop_length_eq_nil_iff, Nat.le_refl, *]

end

end Geb.SizeBounded.Logspace.WTree
