/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Spell
public import Geb.Prototypes.Computability.SizeBounded.Logspace.WTree.Numeral
public import Geb.Prototypes.Computability.SizeBounded.Basic

set_option doc.verso true in
/-!
# The algebra's own signature as a coded signature

The signature of the size-bounded algebra, {name}`Geb.SizeBounded.sig`, with
its shapes coded by bitstrings: a three-bit tag, then the numeric fields as
coded numbers, {name}`Geb.SizeBounded.Logspace.WTree.Numeral.natCode`, and for
a constant its word. The decoder reads the fields back and checks the
constraints of a projection and a recursion. The directions of a shape are
enumerated explicitly, the head of a substitution before its arguments and
the bases of a recursion before its steps on either bit, so that the count
and the order of a shape's directions compute by unfolding.

# Main definitions

* {lit}`compEquiv`, {lit}`srnEquiv`, {lit}`finitary` — the enumerations of
  the directions.
* {lit}`code`, {lit}`decode` — the code of a shape and the decoder.
* {lit}`sigCoded` — the coded signature.

# Main statements

* {lit}`decode_code`, {lit}`code_of_decode` — the decoder inverts the code,
  and a word that decodes is the code of what it decodes to.

# References

* \[Mazzanti2016\]

# Tags

size-bounded algebra, signature, code
-/

set_option doc.verso true

namespace Geb.SizeBounded.Logspace.WTree.Sig

open Numeral
open Geb.SizeBounded (Shape Direction sig)

public section

/-- The directions of a substitution in order: the head, then the arguments. -/
@[expose] def compEquiv (m : ℕ) : Unit ⊕ Fin m ≃ Fin (m + 1) where
  toFun
    | .inl _ => 0
    | .inr i => i.succ
  invFun j := Fin.cases (.inl ()) (fun i ↦ .inr i) j
  left_inv x := by
    cases x with
    | inl u => rfl
    | inr i => simp only [Fin.cases_succ]
  right_inv j := by
    refine Fin.cases (motive := fun j ↦ (match (Fin.cases (.inl ()) (fun i ↦ .inr i) j :
      Unit ⊕ Fin m) with | .inl _ => (0 : Fin (m + 1)) | .inr i => i.succ) = j) ?_ (fun i ↦ ?_) j
    · rfl
    · simp only [Fin.cases_succ]

/-- The directions of a recursion in order: the bases, the steps on a
{lit}`false` bit, the steps on a {lit}`true` bit. -/
@[expose] def srnEquiv (b : ℕ) : Fin b ⊕ (Fin b ⊕ Fin b) ≃ Fin (3 * b) where
  toFun
    | .inl i => ⟨i, by omega⟩
    | .inr (.inl i) => ⟨b + i, by omega⟩
    | .inr (.inr i) => ⟨2 * b + i, by omega⟩
  invFun j :=
    if h1 : j.1 < b then .inl ⟨j, h1⟩
    else if h2 : j.1 < 2 * b then .inr (.inl ⟨j - b, by omega⟩)
    else .inr (.inr ⟨j - 2 * b, by omega⟩)
  left_inv x := by
    rcases x with i | i | i
    · exact dif_pos i.2
    · dsimp only
      rw [dif_neg (by omega), dif_pos (by omega)]
      exact congrArg Sum.inr (congrArg Sum.inl (Fin.ext (Nat.add_sub_cancel_left _ _)))
    · dsimp only
      rw [dif_neg (by omega), dif_neg (by omega)]
      exact congrArg Sum.inr (congrArg Sum.inr (Fin.ext (Nat.add_sub_cancel_left _ _)))
  right_inv j := by
    dsimp only
    split_ifs with h1 h2
    · rfl
    · exact Fin.ext (by dsimp only; omega)
    · exact Fin.ext (by dsimp only; omega)

/-- The shapes' directions enumerated: none for the three base forms; the head
then the arguments of a substitution; the bases then the steps on either bit
of a recursion. -/
@[expose, instance_reducible] def finitary : sig.toPFunctor.Finitary
  | .const _ _ => @FinEnum.mk (Fin 0) 0 (Equiv.refl (Fin 0)) inferInstance
  | .proj _ _ => @FinEnum.mk (Fin 0) 0 (Equiv.refl (Fin 0)) inferInstance
  | .sbs _ => @FinEnum.mk (Fin 0) 0 (Equiv.refl (Fin 0)) inferInstance
  | .comp _ m => @FinEnum.mk (Unit ⊕ Fin m) (m + 1) (compEquiv m) inferInstance
  | .srn _ b _ => @FinEnum.mk (Fin b ⊕ (Fin b ⊕ Fin b)) (3 * b) (srnEquiv b) inferInstance

/-- The code of a shape: a three-bit tag, then the numeric fields as coded
numbers, and for a constant its word. -/
@[expose] def code : Shape → List Bool
  | .const n w => false :: false :: false :: (natCode n ++ w)
  | .proj n i => false :: false :: true :: (natCode n ++ natCode i)
  | .sbs b => [false, true, false, b]
  | .comp n m => false :: true :: true :: (natCode n ++ natCode m)
  | .srn a b j => true :: false :: false :: (natCode a ++ natCode b ++ natCode j)

/-- The decoder. -/
@[expose] def decode : List Bool → Option Shape
  | false :: false :: false :: s => (readNatCode s).map fun p ↦ .const p.1 p.2
  | false :: false :: true :: s =>
    (readNatCode s).bind fun p ↦ (readNatCode p.2).bind fun q ↦
      if q.2 = [] then if h : q.1 < p.1 then some (.proj p.1 ⟨q.1, h⟩) else none else none
  | [false, true, false, b] => some (.sbs b)
  | false :: true :: true :: s =>
    (readNatCode s).bind fun p ↦ (readNatCode p.2).bind fun q ↦
      if q.2 = [] then some (.comp p.1 q.1) else none
  | true :: false :: false :: s =>
    (readNatCode s).bind fun p ↦ (readNatCode p.2).bind fun q ↦ (readNatCode q.2).bind fun r ↦
      if r.2 = [] then if h : r.1 < q.1 then some (.srn p.1 q.1 ⟨r.1, h⟩) else none else none
  | _ => none

/-- The decoder inverts the code. -/
theorem decode_code : ∀ a, decode (code a) = some a
  | .const n w => by
    change (readNatCode (natCode n ++ w)).map _ = _
    rw [readNatCode_natCode_append]
    rfl
  | .proj n i => by
    change (readNatCode (natCode n ++ natCode i)).bind _ = _
    rw [readNatCode_natCode_append, Option.bind_some]
    change (readNatCode (natCode i)).bind _ = _
    rw [← List.append_nil (natCode i), readNatCode_natCode_append, Option.bind_some]
    dsimp only
    rw [if_pos rfl, dif_pos i.2]
  | .sbs b => rfl
  | .comp n m => by
    change (readNatCode (natCode n ++ natCode m)).bind _ = _
    rw [readNatCode_natCode_append, Option.bind_some]
    change (readNatCode (natCode m)).bind _ = _
    rw [← List.append_nil (natCode m), readNatCode_natCode_append, Option.bind_some]
    dsimp only
    rw [if_pos rfl]
  | .srn a b j => by
    change (readNatCode (natCode a ++ natCode b ++ natCode j)).bind _ = _
    rw [List.append_assoc, readNatCode_natCode_append, Option.bind_some]
    change (readNatCode (natCode b ++ natCode j)).bind _ = _
    rw [readNatCode_natCode_append, Option.bind_some]
    change (readNatCode (natCode j)).bind _ = _
    rw [← List.append_nil (natCode j), readNatCode_natCode_append, Option.bind_some]
    dsimp only
    rw [if_pos rfl, dif_pos j.2]

/-- A word that decodes is the code of what it decodes to. -/
theorem code_of_decode {w : List Bool} {a : Shape} (h : decode w = some a) : code a = w := by
  match w, h with
  | false :: false :: false :: s, h =>
    change (readNatCode s).map _ = _ at h
    cases hr : readNatCode s with
    | none => rw [hr] at h; cases h
    | some p =>
      rw [hr, Option.map_some] at h
      obtain rfl := Option.some.inj h
      change false :: false :: false :: (natCode p.1 ++ p.2) = _
      rw [← readNatCode_eq_some s p.1 p.2 hr]
  | false :: false :: true :: s, h =>
    change (readNatCode s).bind _ = _ at h
    cases hr : readNatCode s with
    | none => rw [hr] at h; cases h
    | some p =>
      rw [hr, Option.bind_some] at h
      cases hq : readNatCode p.2 with
      | none => rw [hq] at h; cases h
      | some q =>
        rw [hq, Option.bind_some] at h
        by_cases he : q.2 = []
        · rw [if_pos he] at h
          by_cases hlt : q.1 < p.1
          · rw [dif_pos hlt] at h
            obtain rfl := Option.some.inj h
            change false :: false :: true :: (natCode p.1 ++ natCode q.1) = _
            rw [readNatCode_eq_some s p.1 p.2 hr, readNatCode_eq_some p.2 q.1 q.2 hq, he,
              List.append_nil]
          · rw [dif_neg hlt] at h; cases h
        · rw [if_neg he] at h; cases h
  | [false, true, false, b], h =>
    obtain rfl := Option.some.inj h
    rfl
  | false :: true :: true :: s, h =>
    change (readNatCode s).bind _ = _ at h
    cases hr : readNatCode s with
    | none => rw [hr] at h; cases h
    | some p =>
      rw [hr, Option.bind_some] at h
      cases hq : readNatCode p.2 with
      | none => rw [hq] at h; cases h
      | some q =>
        rw [hq, Option.bind_some] at h
        by_cases he : q.2 = []
        · rw [if_pos he] at h
          obtain rfl := Option.some.inj h
          change false :: true :: true :: (natCode p.1 ++ natCode q.1) = _
          rw [readNatCode_eq_some s p.1 p.2 hr, readNatCode_eq_some p.2 q.1 q.2 hq, he,
            List.append_nil]
        · rw [if_neg he] at h; cases h
  | true :: false :: false :: s, h =>
    change (readNatCode s).bind _ = _ at h
    cases hr : readNatCode s with
    | none => rw [hr] at h; cases h
    | some p =>
      rw [hr, Option.bind_some] at h
      cases hq : readNatCode p.2 with
      | none => rw [hq] at h; cases h
      | some q =>
        rw [hq, Option.bind_some] at h
        cases hs : readNatCode q.2 with
        | none => rw [hs] at h; cases h
        | some r =>
          rw [hs, Option.bind_some] at h
          by_cases he : r.2 = []
          · rw [if_pos he] at h
            by_cases hlt : r.1 < q.1
            · rw [dif_pos hlt] at h
              obtain rfl := Option.some.inj h
              change true :: false :: false :: (natCode p.1 ++ natCode q.1 ++ natCode r.1) = _
              rw [List.append_assoc, readNatCode_eq_some s p.1 p.2 hr,
                readNatCode_eq_some p.2 q.1 q.2 hq, readNatCode_eq_some q.2 r.1 r.2 hs, he,
                List.append_nil]
            · rw [dif_neg hlt] at h; cases h
          · rw [if_neg he] at h; cases h

/-- The algebra's signature as a coded signature. -/
@[expose] def sigCoded : CodedSig ℕ where
  P := sig
  finitary := finitary
  code := code
  decode := decode
  decode_code := decode_code
  code_of_decode := code_of_decode

end

end Geb.SizeBounded.Logspace.WTree.Sig
