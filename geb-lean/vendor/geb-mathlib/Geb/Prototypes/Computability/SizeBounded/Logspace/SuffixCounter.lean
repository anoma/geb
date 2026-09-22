/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.Combinators

set_option doc.verso true in
/-!
# Counters as end segments of the input

A natural number {lit}`v` no greater than the length of a word {lit}`w` is
represented in the successor-free subalgebra by the end segment
{lit}`w.drop v`, the word with its first {lit}`v` bits removed, which the
representation theorem {lit}`Geb.SizeBounded.Logspace.length_le_or_suffix`
admits as a value. The representation is total, {lit}`w.drop v` being the
empty word for every {lit}`v` at least the length, and monotone: raising the
number by one is the tail, and a number exceeds another exactly when its end
segment is the shorter. Zero is the word itself, and a comparison of two
counters is the emptiness of one end segment dropped by the length of the
other. This is the arithmetic a logarithmic-space machine performs on a binary
counter bounded by the input's length, \[Kristiansen2005\] Theorem 4.7
representing such an end segment by its length in binary.

Doubling, which the reading of a binary field as a number requires, is a
recursion over the word: a register runs the end segments of the word up from
the empty one while another runs those of the counter's end segment, and the
result is the latter at the level where the former is the counter's end
segment, which drops the number from its own end segment.

# Main definitions

* {lit}`dropBy`, {lit}`dropByApp` — the second argument dropped by the length
  of the first, and its application to expressions of a common arity.
* {lit}`dblReg`, {lit}`dbl`, {lit}`dblApp` — the registers of the doubling
  recursion, the doubling of a counter, and its application.
* {lit}`bitSem`, {lit}`bitApp` — a counter doubled and raised by a bit, as a
  function and as an applied expression.

# Main statements

* {lit}`sem_dropBy`, {lit}`sem_dropByApp` — the meaning of the drop.
* {lit}`drop_drop_length_eq_nil_iff` — the comparison of two counters below
  the word's length.
* {lit}`dblRegs_eq`, {lit}`sem_dbl_drop`, {lit}`sem_dblApp` — the registers
  of the doubling recursion at every level, and the doubling of a counter.
* {lit}`bitSem_drop`, {lit}`sem_bitApp` — the bit step on a counter.

# References

* \[Kristiansen2005\]

# Tags

logspace, end segment, counter, simultaneous recursion on notation
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace

open Cobham (Sem)

public section

/-- The second argument dropped by the length of the first: a recursion over
the first whose base is the second and whose step is the tail. -/
@[expose] def dropBy : LOf 2 := srnL (fun _ ↦ projL 1 0) (fun _ _ ↦ tailAppL (projL 3 1)) 0

/-- The meaning of the drop. -/
theorem sem_dropBy (a b : List Bool) : dropBy.sem ![a, b] = b.drop a.length :=
  List.rec rfl
    (fun i a ih ↦ by
      change (srnL (fun _ ↦ projL 1 0) (fun _ _ ↦ tailAppL (projL 3 1)) 0).sem
        (Fin.cons (i :: a) ![b]) = b.drop (i :: a).length
      rw [sem_srnL_cons, sem_tailAppL, sem_projL]
      change (dropBy.sem ![a, b]).tail = _
      rw [ih, List.tail_drop, List.length_cons]) a

/-- The drop applied to two expressions of a common arity. -/
@[expose] def dropByApp {n : ℕ} (a b : LOf n) : LOf n := compL dropBy ![a, b]

/-- The meaning of an applied drop. -/
theorem sem_dropByApp {n : ℕ} (a b : LOf n) (x : Fin n → List Bool) :
    (dropByApp a b).sem x = (b.sem x).drop (a.sem x).length := by
  change dropBy.sem (fun i ↦ (![a, b] i).sem x) = _
  rw [show (fun i ↦ (![a, b] i).sem x) = ![a.sem x, b.sem x] from
    funext fun i ↦ match i with | 0 | 1 => rfl]
  exact sem_dropBy _ _

/-- The comparison of two counters: the end segment of {lit}`b` dropped by the
length of the end segment of {lit}`a` is empty exactly when {lit}`a` is at
most {lit}`b`, provided {lit}`b` is below the word's length. -/
theorem drop_drop_length_eq_nil_iff (w : List Bool) {a b : ℕ} (hb : b < w.length) :
    (w.drop b).drop (w.drop a).length = [] ↔ a ≤ b := by
  rw [List.drop_eq_nil_iff, List.length_drop, List.length_drop]
  constructor
  · intro h
    omega
  · intro h
    omega

/-- The registers of the doubling recursion after each bit of the counter: the
end segments of the word and of the argument at the current level, and the
result, which takes the argument's end segment at the level where the word's is
one shorter than the argument, and keeps its value above that level. The step
environment holds the level in slot zero, the three registers in slots one to
three, the argument in slot four and the word in slot five. -/
@[expose] def dblStep : Fin 3 → LOf 6 :=
  ![tailAppL (projL 6 1), tailAppL (projL 6 2),
    cond4L (dropByApp (tailAppL (projL 6 4)) (projL 6 1)) (projL 6 3) (projL 6 2) (projL 6 2)]

/-- The bases of the doubling recursion: the word, the argument, and the empty
word. -/
@[expose] def dblBase : Fin 3 → LOf 2 := ![projL 2 1, projL 2 0, constL 2 []]

/-- The registers of the doubling recursion, as expressions of arity three:
the counter, the argument and the word. -/
@[expose] def dblReg (l : Fin 3) : LOf 3 := srnL dblBase (fun _ ↦ dblStep) l

/-- The result register of the doubling recursion as a function of the level,
by recursion on the level: at level zero the empty word; one level up, the
argument's end segment at the previous level when the word's end segment there
is longer than the argument's tail, and otherwise the previous result. -/
@[expose] def dblF (d w : List Bool) : ℕ → List Bool :=
  Nat.rec [] fun j ih ↦ cond4Sem ((w.drop j).drop d.tail.length) ih (d.drop j) (d.drop j)

/-- The registers of the doubling recursion at every level. -/
theorem dblRegs_eq (d w u : List Bool) : ∀ l : Fin 3,
    (dblReg l).sem (Fin.cons u ![d, w]) =
      ![w.drop u.length, d.drop u.length, dblF d w u.length] l :=
  List.rec (fun l ↦ match l with | 0 | 1 | 2 => rfl)
    (fun i u ih l ↦ by
      change (srnL dblBase (fun _ ↦ dblStep) l).sem (Fin.cons (i :: u) ![d, w]) = _
      rw [sem_srnL_cons]
      have h0 : stepEnv u (fun l ↦ (srnL dblBase (fun _ ↦ dblStep) l).sem (Fin.cons u ![d, w]))
          ![d, w] = ![u, w.drop u.length, d.drop u.length, dblF d w u.length, d, w] :=
        funext fun s ↦ match s with
        | 0 => rfl
        | 1 => ih 0
        | 2 => ih 1
        | 3 => ih 2
        | 4 => rfl
        | 5 => rfl
      rw [h0]
      match l with
      | 0 =>
        change (tailAppL (projL 6 1)).sem _ = w.drop (i :: u).length
        rw [sem_tailAppL, sem_projL, List.length_cons]
        exact List.tail_drop
      | 1 =>
        change (tailAppL (projL 6 2)).sem _ = d.drop (i :: u).length
        rw [sem_tailAppL, sem_projL, List.length_cons]
        exact List.tail_drop
      | 2 =>
        change (cond4L (dropByApp (tailAppL (projL 6 4)) (projL 6 1)) (projL 6 3) (projL 6 2)
          (projL 6 2)).sem _ = dblF d w (i :: u).length
        rw [sem_cond4L, sem_dropByApp, sem_tailAppL, sem_projL, sem_projL, sem_projL, sem_projL,
          List.length_cons]
        rfl) u

/-- The doubling of a counter: the result register with the word as the
counter, the argument and the word as parameters. -/
@[expose] def dbl : LOf 2 := compL (dblReg 2) ![projL 2 1, projL 2 0, projL 2 1]

/-- The result register at a level below the word's length: the word dropped by
the number and by the level, the latter capped at the number. -/
theorem dblF_drop (w : List Bool) (v : ℕ) : ∀ j, j < w.length →
    dblF (w.drop v) w (j + 1) = w.drop (min j v + v) :=
  Nat.rec
    (fun hj ↦ by
      change cond4Sem ((w.drop 0).drop (w.drop v).tail.length) [] ((w.drop v).drop 0)
        ((w.drop v).drop 0) = w.drop (min 0 v + v)
      have hj' : 0 < w.length := hj
      rw [List.tail_drop, show min 0 v + v = v by omega]
      have hne : (w.drop 0).drop (w.drop (v + 1)).length ≠ [] :=
        fun h ↦ absurd ((drop_drop_length_eq_nil_iff w hj').mp h) (by omega)
      cases hd : (w.drop 0).drop (w.drop (v + 1)).length with
      | nil => exact absurd hd hne
      | cons c cs => cases c <;> exact List.drop_zero)
    (fun j ih hj ↦ by
      change cond4Sem ((w.drop (j + 1)).drop (w.drop v).tail.length) (dblF (w.drop v) w (j + 1))
        ((w.drop v).drop (j + 1)) ((w.drop v).drop (j + 1)) = w.drop (min (j + 1) v + v)
      have hj' : j + 1 < w.length := hj
      rw [ih (by omega), List.tail_drop]
      by_cases hle : v + 1 ≤ j + 1
      · rw [(drop_drop_length_eq_nil_iff w hj').mpr hle]
        change w.drop (min j v + v) = w.drop (min (j + 1) v + v)
        rw [show min j v = v by omega, show min (j + 1) v = v by omega]
      · have hne : (w.drop (j + 1)).drop (w.drop (v + 1)).length ≠ [] :=
          fun h ↦ hle ((drop_drop_length_eq_nil_iff w hj').mp h)
        cases hd : (w.drop (j + 1)).drop (w.drop (v + 1)).length with
        | nil => exact absurd hd hne
        | cons c cs =>
          cases c <;>
            (change (w.drop v).drop (j + 1) = w.drop (min (j + 1) v + v)
             rw [List.drop_drop, show v + (j + 1) = min (j + 1) v + v by omega]))

/-- Doubling a counter doubles its number. -/
theorem sem_dbl_drop (w : List Bool) (v : ℕ) : dbl.sem ![w.drop v, w] = w.drop (2 * v) := by
  change (dblReg 2).sem (fun i ↦ (![projL 2 1, projL 2 0, projL 2 1] i).sem ![w.drop v, w]) = _
  rw [show (fun i ↦ (![projL 2 1, projL 2 0, projL 2 1] i).sem ![w.drop v, w]) =
    Fin.cons w ![w.drop v, w] from funext fun i ↦ match i with | 0 | 1 | 2 => rfl]
  rw [dblRegs_eq]
  change dblF (w.drop v) w w.length = _
  cases w with
  | nil =>
    simp only [List.drop_nil]
    rfl
  | cons c cs =>
    rw [List.length_cons, dblF_drop _ v cs.length (by simp)]
    rcases Nat.lt_or_ge v (cs.length + 1) with hv | hv
    · rw [show min cs.length v + v = 2 * v by omega]
    · rw [List.drop_eq_nil_iff.mpr (by simp only [List.length_cons]; omega),
        List.drop_eq_nil_iff.mpr (by simp only [List.length_cons]; omega)]

/-- The doubling applied to two expressions of a common arity. -/
@[expose] def dblApp {n : ℕ} (d w : LOf n) : LOf n := compL dbl ![d, w]

/-- The meaning of an applied doubling. -/
theorem sem_dblApp {n : ℕ} (d w : LOf n) (x : Fin n → List Bool) :
    (dblApp d w).sem x = dbl.sem ![d.sem x, w.sem x] := by
  change dbl.sem (fun i ↦ (![d, w] i).sem x) = _
  rw [show (fun i ↦ (![d, w] i).sem x) = ![d.sem x, w.sem x] from
    funext fun i ↦ match i with | 0 | 1 => rfl]

/-- A counter doubled and raised by a bit: the tail of the doubling on a
{lit}`true` bit, the doubling itself on a {lit}`false` one. -/
@[expose] def bitSem : Bool → List Bool → List Bool → List Bool
  | true, d, w => (dbl.sem ![d, w]).tail
  | false, d, w => dbl.sem ![d, w]

/-- The bit step on a counter appends the bit to its number. -/
theorem bitSem_drop (b : Bool) (w : List Bool) (v : ℕ) :
    bitSem b (w.drop v) w = w.drop (2 * v + b.toNat) := by
  cases b
  · exact sem_dbl_drop w v
  · change (dbl.sem ![w.drop v, w]).tail = _
    rw [sem_dbl_drop, List.tail_drop]
    rfl

/-- The bit step applied to expressions of a common arity. -/
@[expose] def bitApp {n : ℕ} : Bool → LOf n → LOf n → LOf n
  | true, d, w => tailAppL (dblApp d w)
  | false, d, w => dblApp d w

/-- The meaning of an applied bit step. -/
theorem sem_bitApp {n : ℕ} (b : Bool) (d w : LOf n) (x : Fin n → List Bool) :
    (bitApp b d w).sem x = bitSem b (d.sem x) (w.sem x) := by
  cases b
  · exact sem_dblApp d w x
  · change (tailAppL (dblApp d w)).sem x = _
    rw [sem_tailAppL, sem_dblApp]
    rfl

end

end Geb.SizeBounded.Logspace
