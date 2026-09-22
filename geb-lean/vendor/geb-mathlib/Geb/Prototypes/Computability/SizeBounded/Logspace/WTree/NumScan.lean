/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Numeral

set_option doc.verso true in
/-!
# Scanning a numeral at a position of a word

A scanner that reads a word bit by bit, waits for a given position, and from
there reads a length-prefixed binary numeral,
{name}`Geb.SizeBounded.Logspace.WTree.Numeral.natCode`: the zero run of the
gamma code, the size field, read most significant bit first into a value
saturated at the word's length, and then the bits, of which it records the
one at a given index. It ends with the position after
the numeral and whether the numeral was canonical. On a word holding a coded
number at the position the scanner ends so, and a scanner that ends so has
read a coded number, which is what a recognizer reading numerals in a label
needs in both directions.

# Main definitions

* {lit}`NMode`, {lit}`NState`, {lit}`nstep`, {lit}`nrunFrom`, {lit}`nrun`
  — the modes and state, one bit, and the runs over a segment and over a
  word.
* {lit}`satFold` — the size field's value, saturated.

# Main statements

* {lit}`nrunFrom_before`, {lit}`nrunFrom_zeros`, {lit}`nrunFrom_size`,
  {lit}`nrunFrom_bits`, {lit}`nrunFrom_done` — the runs over the segments.
* {lit}`nrun_eq_natCode`, {lit}`nrun_natCode` — on a word holding a coded
  number at the position, the scanner's final state, and from it that the
  scanner ends done and canonical, after the numeral, with its bit at the
  index.
* {lit}`nrun_done` — a scanner that ends done and canonical has read a coded
  number at the position.

# Tags

binary numeral, streaming recognizer, monotone counter
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree.Numeral

open Geb.BitTree.Elias (encodeGamma fromPayload payload)

public section

/-- The modes: before the position; the zero run; the size field; the bits;
and done. -/
inductive NMode where
  | before
  | zeros
  | size
  | bits
  | done
  deriving DecidableEq, Repr

/-- The state: the mode; the zero run, which is the size field's width; the
bits read in the current field; the size field's value, saturated at the
word's length; the bit at the index; whether the numeral ended canonical; and
the position after it. -/
structure NState where
  /-- The mode. -/
  mode : NMode
  /-- The zero run, the size field's width. -/
  z : ℕ
  /-- The bits read in the current field. -/
  cnt : ℕ
  /-- The size field's value, from one, saturated at the word's length. -/
  s : ℕ
  /-- The bit at the index. -/
  hit : Bool
  /-- The numeral ended canonical: its last bit was {lit}`true`. -/
  ok : Bool
  /-- The position after the numeral. -/
  endPos : ℕ
  deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprNState.repr

/-- The initial state. -/
@[expose] def nstart : NState := ⟨.before, 0, 0, 0, false, false, 0⟩

/-- One bit at a position, for the word's length {lit}`n`, the numeral's
position {lit}`tp` and the index {lit}`i`. At the position, a {lit}`true` bit
is the numeral zero, complete; a {lit}`false` bit opens the zero run. The run
ends at a {lit}`true` bit, which opens the size field, of as many bits as the
run had; the field's last bit opens the bits, one fewer than the value; and
the last bit of those completes the numeral. -/
@[expose] def nstep (n tp i : ℕ) (x : NState) (pos : ℕ) (b : Bool) : NState :=
  match x.mode with
  | .before =>
    if pos = tp then
      if b then ⟨.done, 0, 0, 1, false, true, pos + 1⟩ else ⟨.zeros, 1, 0, 1, false, false, 0⟩
    else x
  | .zeros =>
    if b then ⟨.size, x.z, 0, 1, false, false, 0⟩ else ⟨.zeros, x.z + 1, 0, 1, false, false, 0⟩
  | .size =>
    if x.cnt + 1 = x.z then ⟨.bits, x.z, 0, min (2 * x.s + b.toNat) n, false, false, 0⟩
    else ⟨.size, x.z, x.cnt + 1, min (2 * x.s + b.toNat) n, false, false, 0⟩
  | .bits =>
    if x.cnt + 1 + 1 = x.s then
      ⟨.done, x.z, x.cnt + 1, x.s, if x.cnt = i then b else x.hit, b, pos + 1⟩
    else ⟨.bits, x.z, x.cnt + 1, x.s, if x.cnt = i then b else x.hit, false, 0⟩
  | .done => x

/-- The run over a segment from a state at a position. -/
@[expose] def nrunFrom (n tp i : ℕ) (x : NState) (pos : ℕ) (v : List Bool) : NState × ℕ :=
  v.foldl (fun p b ↦ (nstep n tp i p.1 p.2 b, p.2 + 1)) (x, pos)

/-- The run over a word. -/
@[expose] def nrun (tp i : ℕ) (w : List Bool) : NState := (nrunFrom w.length tp i nstart 0 w).1

/-- The run over one more bit. -/
theorem nrunFrom_cons (n tp i : ℕ) (x : NState) (pos : ℕ) (b : Bool) (v : List Bool) :
    nrunFrom n tp i x pos (b :: v) = nrunFrom n tp i (nstep n tp i x pos b) (pos + 1) v := rfl

/-- The run over two segments. -/
theorem nrunFrom_append (n tp i : ℕ) (x : NState) (pos : ℕ) (u v : List Bool) :
    nrunFrom n tp i x pos (u ++ v) =
      nrunFrom n tp i (nrunFrom n tp i x pos u).1 (nrunFrom n tp i x pos u).2 v := by
  unfold nrunFrom
  rw [List.foldl_append]

/-- Before the position, the scanner waits. -/
theorem nrunFrom_before (n tp i : ℕ) (u : List Bool) : ∀ (pos : ℕ) (x : NState), x.mode = .before →
    pos + u.length ≤ tp → nrunFrom n tp i x pos u = (x, pos + u.length) :=
  List.rec (fun pos x _ _ ↦ by rw [nrunFrom]; rfl) (fun b u ih pos x hx hp ↦ by
    rw [List.length_cons] at hp
    rw [nrunFrom_cons, show nstep n tp i x pos b = x by
      unfold nstep; rw [hx]; dsimp only; rw [if_neg (by omega)], ih (pos + 1) x hx (by omega),
      List.length_cons]
    rw [Nat.add_assoc, Nat.add_comm 1]) u

/-- Done, the scanner stays. -/
theorem nrunFrom_done (n tp i : ℕ) (v : List Bool) : ∀ (pos : ℕ) (x : NState), x.mode = .done →
    nrunFrom n tp i x pos v = (x, pos + v.length) :=
  List.rec (fun pos x _ ↦ by rw [nrunFrom]; rfl) (fun b v ih pos x hx ↦ by
    rw [nrunFrom_cons, show nstep n tp i x pos b = x by unfold nstep; rw [hx], ih (pos + 1) x hx,
      List.length_cons]
    rw [Nat.add_assoc, Nat.add_comm 1]) v

/-- A zero run raises the count. -/
theorem nrunFrom_zeros (n tp i : ℕ) (k : ℕ) : ∀ (pos z : ℕ),
    nrunFrom n tp i ⟨.zeros, z, 0, 1, false, false, 0⟩ pos (List.replicate k false) =
      (⟨.zeros, z + k, 0, 1, false, false, 0⟩, pos + k) :=
  Nat.rec (fun pos z ↦ by rw [List.replicate_zero, nrunFrom]; rfl) (fun k ih pos z ↦ by
    rw [List.replicate_succ, nrunFrom_cons]
    change nrunFrom n tp i ⟨.zeros, z + 1, 0, 1, false, false, 0⟩ (pos + 1) _ = _
    rw [ih, show z + 1 + k = z + (k + 1) by omega, show pos + 1 + k = pos + (k + 1) by omega]) k

/-- The size field's value, most significant bit first, saturated at the
word's length. -/
@[expose] def satFold (n : ℕ) (s : ℕ) (sb : List Bool) : ℕ :=
  sb.foldl (fun a b ↦ min (2 * a + b.toNat) n) s

/-- The saturated value is the value when the value is within the bound, the
value rising with every bit. -/
theorem satFold_eq (n : ℕ) (sb : List Bool) : ∀ s : ℕ,
    sb.foldl (fun a b ↦ Nat.bit b a) s ≤ n → satFold n s sb = sb.foldl (fun a b ↦ Nat.bit b a) s :=
  List.rec (fun _ _ ↦ rfl) (fun b sb ih s h ↦ by
    have hmono : ∀ (sb : List Bool) (s : ℕ), s ≤ sb.foldl (fun a b ↦ Nat.bit b a) s :=
      List.rec (fun _ ↦ Nat.le_refl _) fun b sb ih s ↦ by
        rw [List.foldl_cons]
        exact Nat.le_trans (by rw [Nat.bit_val]; omega) (ih (Nat.bit b s))
    rw [List.foldl_cons] at h ⊢
    have h1 : Nat.bit b s ≤ n := Nat.le_trans (hmono sb _) h
    rw [satFold, List.foldl_cons, show min (2 * s + b.toNat) n = Nat.bit b s by
      rw [Nat.bit_val] at h1 ⊢; omega]
    exact ih (Nat.bit b s) h) sb

/-- The size field's bits, as many as the width, read the value into the
state and open the bits. -/
theorem nrunFrom_size (n tp i : ℕ) (sb : List Bool) : ∀ (pos z cnt s : ℕ), sb ≠ [] →
    cnt + sb.length = z →
    nrunFrom n tp i ⟨.size, z, cnt, s, false, false, 0⟩ pos sb =
      (⟨.bits, z, 0, satFold n s sb, false, false, 0⟩, pos + sb.length) :=
  List.rec (fun _ _ _ _ h _ ↦ (h rfl).elim) (fun b sb ih pos z cnt s _ hl ↦ by
    rw [List.length_cons] at hl
    rw [nrunFrom_cons]
    cases sb with
    | nil =>
      change nrunFrom n tp i (if cnt + 1 = z then _ else _) (pos + 1) [] = _
      rw [if_pos (by simp only [List.length_nil] at hl; omega), nrunFrom]
      rfl
    | cons c sb =>
      change nrunFrom n tp i (if cnt + 1 = z then _ else _) (pos + 1) (c :: sb) = _
      rw [if_neg (by simp only [List.length_cons] at hl; omega),
        ih (pos + 1) z (cnt + 1) (min (2 * s + b.toNat) n) (List.cons_ne_nil c sb)
          (by simp only [List.length_cons] at hl ⊢; omega), List.length_cons, List.length_cons]
      rw [show pos + 1 + (sb.length + 1) = pos + (sb.length + 1 + 1) by omega]
      rfl) sb

/-- The bit at an index among the bits read: the index counted from the
bits read before, or the bit already held. -/
@[expose] def hitAfter (hit : Bool) (cnt i : ℕ) (bs : List Bool) : Bool :=
  if i < cnt then hit else bs.getD (i - cnt) hit

/-- The bits, one fewer than the value, complete the numeral, recording the
bit at the index, the last bit as the canonicality, and the position after. -/
theorem nrunFrom_bits (n tp i : ℕ) (bs : List Bool) :
    ∀ (pos z cnt s : ℕ) (hit : Bool) (hbs : bs ≠ []), cnt + bs.length + 1 = s →
    nrunFrom n tp i ⟨.bits, z, cnt, s, hit, false, 0⟩ pos bs =
      (⟨.done, z, cnt + bs.length, s, hitAfter hit cnt i bs, bs.getLast hbs, pos + bs.length⟩,
        pos + bs.length) :=
  List.rec (fun _ _ _ _ _ h _ ↦ (h rfl).elim) (fun b bs ih pos z cnt s hit _ hl ↦ by
    rw [List.length_cons] at hl
    rw [nrunFrom_cons]
    cases bs with
    | nil =>
      change nrunFrom n tp i (if cnt + 1 + 1 = s then _ else _) (pos + 1) [] = _
      rw [if_pos (by simp only [List.length_nil] at hl; omega), nrunFrom]
      simp only [List.foldl_nil, List.getLast_singleton, hitAfter]
      by_cases hi : i < cnt
      · rw [if_pos hi, if_neg (by omega)]
        rfl
      · rw [if_neg hi]
        by_cases hc : cnt = i
        · rw [if_pos hc, hc, Nat.sub_self, List.getD_cons_zero]
          rfl
        · rw [if_neg hc, show i - cnt = i - cnt - 1 + 1 by omega, List.getD_cons_succ,
            List.getD_nil]
          rfl
    | cons c bs =>
      change nrunFrom n tp i (if cnt + 1 + 1 = s then _ else _) (pos + 1) (c :: bs) = _
      rw [if_neg (by simp only [List.length_cons] at hl; omega),
        ih (pos + 1) z (cnt + 1) s (if cnt = i then b else hit) (List.cons_ne_nil c bs)
          (by simp only [List.length_cons] at hl ⊢; omega), List.length_cons, List.length_cons]
      have hpos : pos + 1 + (bs.length + 1) = pos + (bs.length + 1 + 1) := by omega
      have hcnt : cnt + 1 + (bs.length + 1) = cnt + (bs.length + 1 + 1) := by omega
      have hlast : (c :: bs).getLast (List.cons_ne_nil c bs) =
          (b :: c :: bs).getLast (List.cons_ne_nil b (c :: bs)) := by
        rw [List.getLast_cons (List.cons_ne_nil c bs)]
      have hhit : hitAfter (if cnt = i then b else hit) (cnt + 1) i (c :: bs) =
          hitAfter hit cnt i (b :: c :: bs) := by
        unfold hitAfter
        by_cases hi : i < cnt
        · rw [if_pos (by omega), if_pos hi, if_neg (by omega)]
        · rw [if_neg hi]
          by_cases hc : cnt = i
          · rw [if_pos (by omega), if_pos hc, hc, Nat.sub_self, List.getD_cons_zero]
          · rw [if_neg (by omega), if_neg hc, show i - cnt = i - (cnt + 1) + 1 by omega,
              List.getD_cons_succ]
      rw [hlast, hhit]
      simp only [List.length_cons, hpos, hcnt]) bs

/-- A nonempty canonical bit list ends in {lit}`true`. -/
theorem getLast_of_canonical (bs : List Bool) (hbs : bs ≠ []) (hc : canonical bs = true) :
    bs.getLast hbs = true := by
  unfold canonical at hc
  rw [List.getLast?_eq_some_getLast hbs, decide_eq_true_iff] at hc
  cases h : bs.getLast hbs
  · exact absurd (by rw [h]) hc
  · rfl

/-- A number of two or more has binary size two or more. -/
theorem two_le_size (x : ℕ) (hx : 2 ≤ x) : 2 ≤ x.size := by
  refine @Nat.bitCasesOn (fun x ↦ 2 ≤ x → 2 ≤ x.size) x (fun b y hx ↦ ?_) hx
  rw [Nat.bit_val] at hx
  have hb := Bool.toNat_le b
  have hy : y ≠ 0 := by omega
  rw [Nat.size_bit (by rw [Nat.bit_val]; omega)]
  have := Geb.BitTree.Elias.size_pos y hy
  omega

/-- The length of a coded number. -/
theorem length_natCode (m : ℕ) :
    (natCode m).length = 2 * ((m.size + 1).size - 1) + 1 + m.size := by
  rw [natCode, List.length_append, Geb.BitTree.Elias.length_encodeGamma, length_bits]

/-- Over a coded number from its position, the scanner ends done and canonical,
after the numeral, holding the number's binary size and the size field's
value, and the number's bit at the index. -/
theorem nrunFrom_natCode (n tp i m : ℕ) (hnl : (natCode m).length ≤ n) :
    nrunFrom n tp i nstart tp (natCode m) =
      (⟨.done, (m.size + 1).size - 1, m.size, m.size + 1, m.bits.getD i false, true,
        tp + (natCode m).length⟩, tp + (natCode m).length) := by
  cases m with
  | zero =>
    change nrunFrom n tp i nstart tp [true] = _
    rw [nrunFrom_cons]
    change nrunFrom n tp i (if tp = tp then _ else _) (tp + 1) [] = _
    rw [if_pos rfl, nrunFrom]
    rfl
  | succ m' =>
    have hm : m' + 1 ≠ 0 := Nat.succ_ne_zero m'
    have hs2 : 2 ≤ (m' + 1).size + 1 := by
      have := Geb.BitTree.Elias.size_pos (m' + 1) hm
      omega
    have hz2 : 2 ≤ ((m' + 1).size + 1).size := two_le_size _ hs2
    obtain ⟨k, hk⟩ : ∃ k, ((m' + 1).size + 1).size - 1 = k + 1 :=
      ⟨((m' + 1).size + 1).size - 2, by omega⟩
    have hgamma : encodeGamma ((m' + 1).size + 1) =
        false :: List.replicate k false ++ true :: payload ((m' + 1).size + 1) := by
      rw [encodeGamma, hk, List.replicate_succ]
    have hpl : (payload ((m' + 1).size + 1)).length = k + 1 := by
      rw [Geb.BitTree.Elias.length_payload, hk]
    have hpne : payload ((m' + 1).size + 1) ≠ [] := by
      intro h
      rw [h] at hpl
      cases hpl
    have hbl : (m' + 1).bits.length = (m' + 1).size := length_bits _
    have hbne : (m' + 1).bits ≠ [] := by
      intro h
      rw [h] at hbl
      have := Geb.BitTree.Elias.size_pos (m' + 1) hm
      simp only [List.length_nil] at hbl
      omega
    have hlen : (natCode (m' + 1)).length = 2 * (k + 1) + 1 + (m' + 1).size := by
      rw [length_natCode, hk]
    have hsat : satFold n 1 (payload ((m' + 1).size + 1)) = (m' + 1).size + 1 := by
      rw [satFold_eq n _ 1 ?_]
      · exact Geb.BitTree.Elias.fromPayload_payload _ (by omega)
      · change fromPayload (payload ((m' + 1).size + 1)) ≤ n
        rw [Geb.BitTree.Elias.fromPayload_payload _ (by omega)]
        omega
    have hsplit : natCode (m' + 1) =
        false :: (List.replicate k false ++
          true :: (payload ((m' + 1).size + 1) ++ (m' + 1).bits)) := by
      rw [natCode, hgamma]
      simp only [List.cons_append, List.append_assoc]
    rw [hlen, hsplit, nrunFrom_cons]
    change nrunFrom n tp i (if tp = tp then _ else _) (tp + 1) _ = _
    rw [if_pos rfl, if_neg (show ¬false = true by decide), nrunFrom_append,
      nrunFrom_zeros, nrunFrom_cons]
    change nrunFrom n tp i ⟨.size, 1 + k, 0, 1, false, false, 0⟩ (tp + 1 + k + 1) _ = _
    rw [nrunFrom_append, nrunFrom_size _ _ _ _ _ _ _ _ hpne (by rw [hpl]; omega), hpl, hsat,
      nrunFrom_bits _ _ _ _ _ _ _ _ _ hbne (by rw [hbl]; omega), hbl, hk]
    have hhit : hitAfter false 0 i (m' + 1).bits = (m' + 1).bits.getD i false := by
      unfold hitAfter
      rw [if_neg (Nat.not_lt_zero i), Nat.sub_zero]
    rw [hhit, getLast_of_canonical _ hbne (canonical_bits _), Nat.zero_add,
      show 1 + k = k + 1 by omega,
      show tp + 1 + k + 1 + (k + 1) + (m' + 1).size = tp + (2 * (k + 1) + 1 + (m' + 1).size) by
        omega]

/-- On a word holding a coded number at the position, the scanner ends in the
state the run over the numeral alone ends in. -/
theorem nrun_eq_natCode (tp i : ℕ) (u rest w : List Bool) (m : ℕ) (hu : u.length = tp)
    (hw : w = u ++ natCode m ++ rest) :
    nrun tp i w = ⟨.done, (m.size + 1).size - 1, m.size, m.size + 1, m.bits.getD i false, true,
      tp + (natCode m).length⟩ := by
  obtain ⟨n, hn⟩ : ∃ n, w.length = n := ⟨_, rfl⟩
  have hnl : (natCode m).length ≤ n := by
    rw [← hn, hw, List.length_append, List.length_append]
    omega
  have hst : nrunFrom n tp i nstart 0 u = (nstart, tp) := by
    rw [nrunFrom_before n tp i u 0 nstart rfl (by rw [hu]; omega), Nat.zero_add, hu]
  rw [nrun, hn, hw, List.append_assoc, nrunFrom_append, hst]
  change (nrunFrom n tp i nstart tp (natCode m ++ rest)).1 = _
  rw [nrunFrom_append, nrunFrom_natCode n tp i m hnl, nrunFrom_done _ _ _ rest _ _ rfl]

/-- On a word holding a coded number at the position, the scanner ends done and
canonical, after the numeral, with the numeral's bit at the index. -/
theorem nrun_natCode (tp i : ℕ) (u rest w : List Bool) (m : ℕ) (hu : u.length = tp)
    (hw : w = u ++ natCode m ++ rest) :
    (nrun tp i w).mode = .done ∧ (nrun tp i w).ok = true ∧
      (nrun tp i w).endPos = tp + (natCode m).length ∧
      (nrun tp i w).hit = m.bits.getD i false := by
  rw [nrun_eq_natCode tp i u rest w m hu hw]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- The bit at an index among no bits is the bit held. -/
theorem hitAfter_nil (hit : Bool) (cnt i : ℕ) : hitAfter hit cnt i [] = hit := by
  unfold hitAfter
  rw [List.getD_nil, ite_self]

/-- The bit at an index among one more bit: the bit itself at the count, else
among the rest from one more. -/
theorem hitAfter_cons (hit : Bool) (cnt i : ℕ) (b : Bool) (bs : List Bool) :
    hitAfter hit cnt i (b :: bs) = hitAfter (if cnt = i then b else hit) (cnt + 1) i bs := by
  unfold hitAfter
  by_cases hi : i < cnt
  · rw [if_pos hi, if_pos (show i < cnt + 1 by omega),
      if_neg (show ¬cnt = i by omega)]
  · rw [if_neg hi]
    by_cases hc : cnt = i
    · rw [hc, Nat.sub_self, List.getD_cons_zero, if_pos (Nat.lt_succ_self i), if_pos rfl]
    · rw [if_neg (show ¬i < cnt + 1 by omega), if_neg hc,
        show i - cnt = i - (cnt + 1) + 1 by omega, List.getD_cons_succ]

/-- A run from the zero run that ends done read a zero run and the bit
opening the size field. -/
theorem done_of_zeros (n tp i : ℕ) (v : List Bool) : ∀ (pos z : ℕ),
    (nrunFrom n tp i ⟨.zeros, z, 0, 1, false, false, 0⟩ pos v).1.mode = .done →
    ∃ k v', v = List.replicate k false ++ true :: v' ∧
      nrunFrom n tp i ⟨.zeros, z, 0, 1, false, false, 0⟩ pos v =
        nrunFrom n tp i ⟨.size, z + k, 0, 1, false, false, 0⟩ (pos + k + 1) v' :=
  List.rec (fun pos z h ↦ by rw [nrunFrom] at h; cases h) (fun b v ih pos z h ↦ by
    cases b with
    | true => exact ⟨0, v, rfl, rfl⟩
    | false =>
      have hstep : nstep n tp i ⟨.zeros, z, 0, 1, false, false, 0⟩ pos false =
          ⟨.zeros, z + 1, 0, 1, false, false, 0⟩ := rfl
      rw [nrunFrom_cons, hstep] at h ⊢
      obtain ⟨k, v', rfl, he⟩ := ih (pos + 1) (z + 1) h
      refine ⟨k + 1, v', by simp only [List.replicate_succ, List.cons_append], ?_⟩
      rw [he, show z + 1 + k = z + (k + 1) by omega,
        show pos + 1 + k + 1 = pos + (k + 1) + 1 by omega]) v

/-- A run from the size field that ends done read the field's remaining bits
and opened the bits. -/
theorem done_of_size (n tp i : ℕ) (v : List Bool) : ∀ (pos z cnt s : ℕ),
    (nrunFrom n tp i ⟨.size, z, cnt, s, false, false, 0⟩ pos v).1.mode = .done →
    ∃ sb v', v = sb ++ v' ∧ cnt + sb.length = z ∧
      nrunFrom n tp i ⟨.size, z, cnt, s, false, false, 0⟩ pos v =
        nrunFrom n tp i ⟨.bits, z, 0, satFold n s sb, false, false, 0⟩ (pos + sb.length) v' :=
  List.rec (fun pos z cnt s h ↦ by rw [nrunFrom] at h; cases h) (fun b v ih pos z cnt s h ↦ by
    have hstep : nstep n tp i ⟨.size, z, cnt, s, false, false, 0⟩ pos b =
        if cnt + 1 = z then ⟨.bits, z, 0, min (2 * s + b.toNat) n, false, false, 0⟩
        else ⟨.size, z, cnt + 1, min (2 * s + b.toNat) n, false, false, 0⟩ := rfl
    rw [nrunFrom_cons, hstep] at h ⊢
    by_cases hc : cnt + 1 = z
    · rw [if_pos hc] at h ⊢
      exact ⟨[b], v, rfl, by rw [List.length_singleton]; exact hc, rfl⟩
    · rw [if_neg hc] at h ⊢
      obtain ⟨sb, v', rfl, hl, he⟩ := ih (pos + 1) z (cnt + 1) (min (2 * s + b.toNat) n) h
      refine ⟨b :: sb, v', rfl, by rw [List.length_cons]; omega, ?_⟩
      rw [he, List.length_cons, show pos + 1 + sb.length = pos + (sb.length + 1) by omega]
      rfl) v

/-- A run from the bits that ends done read the remaining bits, one fewer than
the value, and completed the numeral. -/
theorem done_of_bits (n tp i : ℕ) (v : List Bool) : ∀ (pos z cnt s : ℕ) (hit : Bool),
    (nrunFrom n tp i ⟨.bits, z, cnt, s, hit, false, 0⟩ pos v).1.mode = .done →
    ∃ (bs v' : List Bool) (hbs : bs ≠ []), v = bs ++ v' ∧ cnt + bs.length + 1 = s ∧
      nrunFrom n tp i ⟨.bits, z, cnt, s, hit, false, 0⟩ pos v =
        nrunFrom n tp i ⟨.done, z, cnt + bs.length, s, hitAfter hit cnt i bs, bs.getLast hbs,
          pos + bs.length⟩ (pos + bs.length) v' :=
  List.rec (fun pos z cnt s hit h ↦ by rw [nrunFrom] at h; cases h)
    (fun b v ih pos z cnt s hit h ↦ by
      have hstep : nstep n tp i ⟨.bits, z, cnt, s, hit, false, 0⟩ pos b =
          if cnt + 1 + 1 = s then ⟨.done, z, cnt + 1, s, if cnt = i then b else hit, b, pos + 1⟩
          else ⟨.bits, z, cnt + 1, s, if cnt = i then b else hit, false, 0⟩ := rfl
      rw [nrunFrom_cons, hstep] at h ⊢
      by_cases hc : cnt + 1 + 1 = s
      · rw [if_pos hc] at h ⊢
        refine ⟨[b], v, List.cons_ne_nil b [], rfl, by rw [List.length_singleton]; exact hc, ?_⟩
        rw [List.length_singleton, List.getLast_singleton, hitAfter_cons, hitAfter_nil]
      · rw [if_neg hc] at h ⊢
        obtain ⟨bs, v', hbs, rfl, hl, he⟩ :=
          ih (pos + 1) z (cnt + 1) s (if cnt = i then b else hit) h
        refine ⟨b :: bs, v', List.cons_ne_nil b bs, rfl, by rw [List.length_cons]; omega, ?_⟩
        rw [he, List.length_cons, hitAfter_cons, List.getLast_cons hbs,
          show pos + 1 + bs.length = pos + (bs.length + 1) by omega,
          show cnt + 1 + bs.length = cnt + (bs.length + 1) by omega]) v

/-- The value read from bits is at least the value read before them. -/
theorem le_foldl_bit (sb : List Bool) : ∀ s : ℕ, s ≤ sb.foldl (fun a b ↦ Nat.bit b a) s :=
  List.rec (fun _ ↦ Nat.le_refl _) (fun b sb ih s ↦ by
    rw [List.foldl_cons]
    exact Nat.le_trans (by rw [Nat.bit_val]; omega) (ih (Nat.bit b s))) sb

/-- The saturated value is the value cut off at the bound. -/
theorem satFold_eq_min (n : ℕ) (sb : List Bool) : ∀ s : ℕ, s ≤ n →
    satFold n s sb = min (sb.foldl (fun a b ↦ Nat.bit b a) s) n :=
  List.rec (fun s hs ↦ by rw [satFold, List.foldl_nil, List.foldl_nil, Nat.min_eq_left hs])
    (fun b sb ih s hs ↦ by
      rw [satFold, List.foldl_cons, List.foldl_cons]
      change satFold n (min (2 * s + b.toNat) n) sb = _
      rw [ih _ (Nat.min_le_right _ _)]
      by_cases h : 2 * s + b.toNat ≤ n
      · rw [Nat.min_eq_left h, Nat.bit_val]
      · have h2 : n ≤ sb.foldl (fun a b ↦ Nat.bit b a) (Nat.bit b s) :=
          Nat.le_trans (by rw [Nat.bit_val]; omega) (le_foldl_bit sb _)
        rw [Nat.min_eq_right (show n ≤ 2 * s + b.toNat by omega),
          Nat.min_eq_right (le_foldl_bit sb n), Nat.min_eq_right h2])
    sb

/-- A run that ends done and canonical has read a coded number at the position,
ending after it with the number's bit at the index. -/
theorem nrun_done (tp i : ℕ) (w : List Bool) (hd : (nrun tp i w).mode = .done)
    (hok : (nrun tp i w).ok = true) :
    ∃ m rest, w.drop tp = natCode m ++ rest ∧ (nrun tp i w).endPos = tp + (natCode m).length ∧
      (nrun tp i w).hit = m.bits.getD i false := by
  obtain ⟨n, hn⟩ : ∃ n, w.length = n := ⟨_, rfl⟩
  have hsplit : w.length = (w.take tp).length + (w.drop tp).length := by
    rw [← List.length_append, List.take_append_drop]
  by_cases htp : w.length ≤ tp
  · exfalso
    rw [nrun, nrunFrom_before _ tp i w 0 nstart rfl (by omega)] at hd
    cases hd
  · have hlt : (w.take tp).length = tp := List.length_take_of_le (by omega)
    obtain ⟨b, v, hv⟩ : ∃ b v, w.drop tp = b :: v := by
      cases hdrop : w.drop tp with
      | nil =>
        have : (w.drop tp).length = w.length - tp := List.length_drop
        rw [hdrop] at this
        simp only [List.length_nil] at this
        exfalso
        omega
      | cons b v => exact ⟨b, v, rfl⟩
    have hrun : nrun tp i w = (nrunFrom n tp i nstart tp (b :: v)).1 := by
      have hw : nrunFrom n tp i nstart 0 w = nrunFrom n tp i nstart 0 (w.take tp ++ w.drop tp) := by
        rw [List.take_append_drop]
      rw [nrun, hn, hw, nrunFrom_append, nrunFrom_before n tp i _ 0 nstart rfl (by rw [hlt]; omega),
        Nat.zero_add, hlt, hv]
    rw [hrun] at hd hok ⊢
    rw [hv]
    rw [nrunFrom_cons] at hd hok ⊢
    change (nrunFrom n tp i (if tp = tp then _ else _) (tp + 1) v).1.mode = .done at hd
    change (nrunFrom n tp i (if tp = tp then _ else _) (tp + 1) v).1.ok = true at hok
    change ∃ m rest, b :: v = natCode m ++ rest ∧
      (nrunFrom n tp i (if tp = tp then _ else _) (tp + 1) v).1.endPos = _ ∧
      (nrunFrom n tp i (if tp = tp then _ else _) (tp + 1) v).1.hit = _
    rw [if_pos rfl] at hd hok ⊢
    cases b with
    | true =>
      rw [nrunFrom_done n tp i v _ _ rfl]
      exact ⟨0, v, rfl, rfl, rfl⟩
    | false =>
      rw [if_neg (show ¬false = true by decide)] at hd hok ⊢
      obtain ⟨k, v', rfl, he₁⟩ := done_of_zeros n tp i v (tp + 1) 1 hd
      rw [he₁] at hd hok ⊢
      obtain ⟨sb, v'', rfl, hsl, he₂⟩ := done_of_size n tp i v' _ (1 + k) 0 1 hd
      rw [he₂] at hd hok ⊢
      obtain ⟨bs, v₃, hbs, rfl, hbl, he₃⟩ :=
        done_of_bits n tp i v'' _ (1 + k) 0 (satFold n 1 sb) false hd
      rw [he₃, nrunFrom_done n tp i v₃ _ _ rfl] at hd hok ⊢
      change bs.getLast hbs = true at hok
      have hlen : n = tp + 1 + k + 1 + sb.length + bs.length + v₃.length := by
        rw [← hn, hsplit, hlt, hv]
        simp only [List.length_append, List.length_cons, List.length_replicate]
        omega
      rw [satFold_eq_min n sb 1 (by omega)] at hbl
      change 0 + bs.length + 1 = min (fromPayload sb) n at hbl
      have hval : bs.length + 1 = fromPayload sb := by
        rcases Nat.le_total (fromPayload sb) n with h | h
        · rw [Nat.min_eq_left h] at hbl
          omega
        · rw [Nat.min_eq_right h] at hbl
          omega
      have hcan : canonical bs = true := by
        unfold canonical
        rw [List.getLast?_eq_some_getLast hbs, hok]
        decide
      have hbits : (fromBits bs).bits = bs := bits_fromBits bs hcan
      have hsize : (fromBits bs).size = bs.length := by rw [← length_bits, hbits]
      have hcode : natCode (fromBits bs) =
          false :: (List.replicate k false ++ true :: (sb ++ bs)) := by
        rw [natCode, hbits, hsize, hval, encodeGamma, Geb.BitTree.Elias.size_fromPayload,
          Geb.BitTree.Elias.payload_fromPayload, Nat.add_sub_cancel,
          show sb.length = k + 1 by omega, List.replicate_succ]
        simp only [List.cons_append, List.append_assoc]
      refine ⟨fromBits bs, v₃,
        by rw [hcode]; simp only [List.cons_append, List.append_assoc], ?_, ?_⟩
      · rw [hcode]
        simp only [List.length_cons, List.length_append, List.length_replicate]
        omega
      · change hitAfter false 0 i bs = _
        rw [hbits]
        unfold hitAfter
        rw [if_neg (Nat.not_lt_zero i), Nat.sub_zero]

end

end Geb.SizeBounded.Logspace.WTree.Numeral
