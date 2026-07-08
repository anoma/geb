import GebLean.Ramified.Soundness.DetStep
import Mathlib.Data.Nat.Pairing

/-!
# Ramified recurrence: sort codes

The Gödel coding of the ramified types (Leivant III section 2.3) as natural
numbers, opening the coding layer of the deterministic normalizer. `codeRType`
folds an r-type to a `Nat.pair`-nested numeral tagged by its top shape, and
`ordCode` reads the type order `RType.ord` directly off that numeral by strong
recursion on the code value, mirroring `RType.ord` without decoding.

`codeRType` is a three-shape fold: the base sort `o` codes to `Nat.pair 0 0`, an
arrow `σ → τ` to `Nat.pair 1 (Nat.pair (codeRType σ) (codeRType τ))`, and an
`Ω τ` to `Nat.pair 2 (codeRType τ)`. The leading `Nat.pair` component is the
shape tag, read back by `shapeCode`; the trailing components carry the child
codes, read back by `argCode` (the single child of an `Ω` code), and by
`domCode` and `codCode` (the domain and codomain codes of an arrow code).

`ordCode` recurses on the code by well-founded recursion: it dispatches on the
shape tag and recurses into the child codes, which the pairing inequalities
`OneLambda.self_lt_pair_one` and `OneLambda.self_lt_pair_two` place strictly
below the composite code. The mirror theorem `ordCode_codeRType` proves the two
routes agree: reading the order off the code equals computing it on the type.

## Main definitions

* `OneLambda.codeRType` — the Gödel code of an r-type: a shape-tagged
  `Nat.pair` numeral.
* `OneLambda.shapeCode` — the top shape tag of a code (`0` for `o`, `1` for an
  arrow, `2` for an `Ω`).
* `OneLambda.argCode` — the child code of an `Ω` code (the payload after the
  tag).
* `OneLambda.domCode`, `OneLambda.codCode` — the domain and codomain child codes
  of an arrow code.
* `OneLambda.ordCode` — the type order read off a code by strong recursion,
  mirroring `RType.ord`.

## Main statements

* `OneLambda.codeRType_o`, `OneLambda.codeRType_arrow`,
  `OneLambda.codeRType_omega` — the node equations of the code fold.
* `OneLambda.shapeCode_codeRType_o`, `OneLambda.shapeCode_codeRType_arrow`,
  `OneLambda.shapeCode_codeRType_omega` — the shape tag on each code shape.
* `OneLambda.argCode_codeRType_omega`, `OneLambda.domCode_codeRType_arrow`,
  `OneLambda.codCode_codeRType_arrow` — the child-code reads on each code shape.
* `OneLambda.self_lt_pair_one`, `OneLambda.self_lt_pair_two` — the strict
  pairing steps `p < Nat.pair 1 p` and `p < Nat.pair 2 p` that bound the
  recursion of `ordCode`.
* `OneLambda.ordCode_pair_zero`, `OneLambda.ordCode_pair_one`,
  `OneLambda.ordCode_pair_two` — the dispatch unfoldings of `ordCode` at each
  code shape.
* `OneLambda.ordCode_codeRType` — the mirror theorem: `ordCode (codeRType σ) =
  RType.ord σ`.

## Implementation notes

`codeRType` follows the measure-fold house pattern of `RType.ord`
(`GebLean/Ramified/Soundness/Normalization.lean`): the dependent eliminator
`PolyFix.ind` over `rTypeSig.polyEndo` (decision 8), with the three node
equations holding definitionally. `ordCode` is a well-founded recursion on the
code value; its child recursions are guarded by `self_lt_pair_one` and
`self_lt_pair_two`, which reconstruct the code as `Nat.pair tag payload`
(`Nat.pair_unpair`) and step strictly past the payload. This project's coding
layer pins the algebra signature at `natAlgSig`.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher
type recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`, section 2.2 (p. 213): the
order of a simple type; section 2.3: the ramified types. The Gödel coding of
the r-types as `Nat.pair` numerals and the order read `ordCode` are a novel
realization; the underlying type conventions transcribe Leivant III section 2.3.

## Tags

ramified recurrence, ramified type, Gödel numbering, pairing function, type
order, well-founded recursion
-/

namespace GebLean.Ramified

namespace OneLambda

/-- The Gödel code of an r-type (Leivant III section 2.3): the base sort `o`
codes to `Nat.pair 0 0`, an arrow `σ → τ` to `Nat.pair 1 (Nat.pair (codeRType
σ) (codeRType τ))`, and an `Ω τ` to `Nat.pair 2 (codeRType τ)`. The leading
`Nat.pair` component is the shape tag; the trailing components carry the child
codes. Realized by the dependent eliminator `PolyFix.ind` (decision 8),
following `RType.ord`'s fold pattern. Novel realization. -/
def codeRType (τ : RType) : ℕ :=
  PolyFix.ind (P := rTypeSig.polyEndo) (motive := fun {_} _ => ℕ)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => Nat.pair 0 0
      | RTypeShape.arrow, _, ih =>
        Nat.pair 1
          (Nat.pair (ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)))
            (ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))))
      | RTypeShape.omega, _, ih =>
        Nat.pair 2 (ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega)))) τ

@[simp] theorem codeRType_o : codeRType RType.o = Nat.pair 0 0 := rfl

@[simp] theorem codeRType_arrow (σ τ : RType) :
    codeRType (RType.arrow σ τ)
      = Nat.pair 1 (Nat.pair (codeRType σ) (codeRType τ)) := rfl

@[simp] theorem codeRType_omega (τ : RType) :
    codeRType (RType.omega τ) = Nat.pair 2 (codeRType τ) := rfl

/-- The top shape tag of a code: the leading `Nat.pair` component. On a
`codeRType` image it is `0` for `o`, `1` for an arrow, and `2` for an `Ω`. -/
def shapeCode (n : ℕ) : ℕ := (Nat.unpair n).1

/-- The child code carried after the shape tag: the trailing `Nat.pair`
component. On an `Ω` code it is the code of the child; on an arrow code it is
the pair of the domain and codomain codes. -/
def argCode (n : ℕ) : ℕ := (Nat.unpair n).2

/-- The domain child code of an arrow code: the first component of `argCode`. -/
def domCode (n : ℕ) : ℕ := (Nat.unpair (argCode n)).1

/-- The codomain child code of an arrow code: the second component of
`argCode`. -/
def codCode (n : ℕ) : ℕ := (Nat.unpair (argCode n)).2

theorem shapeCode_codeRType_o : shapeCode (codeRType RType.o) = 0 := by
  simp [shapeCode, Nat.unpair_pair]

theorem shapeCode_codeRType_arrow (σ τ : RType) :
    shapeCode (codeRType (RType.arrow σ τ)) = 1 := by
  simp [shapeCode, Nat.unpair_pair]

theorem shapeCode_codeRType_omega (τ : RType) :
    shapeCode (codeRType (RType.omega τ)) = 2 := by
  simp [shapeCode, Nat.unpair_pair]

theorem argCode_codeRType_omega (τ : RType) :
    argCode (codeRType (RType.omega τ)) = codeRType τ := by
  simp [argCode, Nat.unpair_pair]

theorem domCode_codeRType_arrow (σ τ : RType) :
    domCode (codeRType (RType.arrow σ τ)) = codeRType σ := by
  simp [domCode, argCode, Nat.unpair_pair]

theorem codCode_codeRType_arrow (σ τ : RType) :
    codCode (codeRType (RType.arrow σ τ)) = codeRType τ := by
  simp [codCode, argCode, Nat.unpair_pair]

/-- The strict pairing step past the shape tag `1`: `p < Nat.pair 1 p`. On the
`p ≤ 1` branch `Nat.pair 1 p = p + 2`; on the `1 < p` branch `Nat.pair 1 p =
p * p + 1 > p`. Bounds the arrow recursion of `ordCode`. -/
theorem self_lt_pair_one (p : ℕ) : p < Nat.pair 1 p := by
  rw [Nat.pair]
  split_ifs with h
  · have hp : p ≤ p * p := Nat.le_mul_of_pos_left p (by omega)
    omega
  · omega

/-- The strict pairing step past the shape tag `2`: `p < Nat.pair 2 p`. On the
`p ≤ 2` branch `Nat.pair 2 p = p + 6`; on the `2 < p` branch `Nat.pair 2 p =
p * p + 2 > p`. Bounds the `Ω` recursion of `ordCode`. -/
theorem self_lt_pair_two (p : ℕ) : p < Nat.pair 2 p := by
  rw [Nat.pair]
  split_ifs with h
  · have hp : p ≤ p * p := Nat.le_mul_of_pos_left p (by omega)
    omega
  · omega

/-- The type order read off a code (Leivant III section 2.2, p. 213): dispatch on
the shape tag `shapeCode n` and recurse into the child codes, mirroring
`RType.ord`. Shape `1` (arrow) reads `max (ordCode (domCode n) + 1) (ordCode
(codCode n))`; shape `2` (`Ω`) reads `ordCode (argCode n)`; every other tag reads
`0`. Well-founded on the code value: `self_lt_pair_one` and `self_lt_pair_two`
place the child codes strictly below the composite. Novel realization. -/
def ordCode (n : ℕ) : ℕ :=
  match h : (Nat.unpair n).1 with
  | 1 =>
    max (ordCode (Nat.unpair (Nat.unpair n).2).1 + 1)
      (ordCode (Nat.unpair (Nat.unpair n).2).2)
  | 2 => ordCode (Nat.unpair n).2
  | _ => 0
  termination_by n
  decreasing_by
    · have hlt : (Nat.unpair n).2 < n := by
        conv_rhs => rw [← Nat.pair_unpair n, h]
        exact self_lt_pair_one _
      exact Nat.lt_of_le_of_lt (Nat.unpair_left_le _) hlt
    · have hlt : (Nat.unpair n).2 < n := by
        conv_rhs => rw [← Nat.pair_unpair n, h]
        exact self_lt_pair_one _
      exact Nat.lt_of_le_of_lt (Nat.unpair_right_le _) hlt
    · conv_rhs => rw [← Nat.pair_unpair n, h]
      exact self_lt_pair_two _

/-- The dispatch unfolding of `ordCode` at a base-sort code `Nat.pair 0 0`. -/
theorem ordCode_pair_zero : ordCode (Nat.pair 0 0) = 0 := by
  rw [ordCode]
  split <;> simp_all [Nat.unpair_pair]

/-- The dispatch unfolding of `ordCode` at an arrow code `Nat.pair 1 (Nat.pair a
b)`: the shape-`1` branch reads the two child orders. -/
theorem ordCode_pair_one (a b : ℕ) :
    ordCode (Nat.pair 1 (Nat.pair a b)) = max (ordCode a + 1) (ordCode b) := by
  rw [ordCode]
  split <;> simp_all [Nat.unpair_pair]

/-- The dispatch unfolding of `ordCode` at an `Ω` code `Nat.pair 2 a`: the
shape-`2` branch reads the single child order. -/
theorem ordCode_pair_two (a : ℕ) : ordCode (Nat.pair 2 a) = ordCode a := by
  rw [ordCode]
  split <;> simp_all [Nat.unpair_pair]

/-- The mirror theorem (Leivant III section 2.2, p. 213): reading the type order
off a code agrees with computing it on the type, `ordCode (codeRType σ) =
RType.ord σ`. By structural induction on the r-type via `PolyFix.ind`, the node
equations of `codeRType` and `RType.ord` feeding the `ordCode` dispatch
unfoldings. Novel realization. -/
theorem ordCode_codeRType (σ : RType) : ordCode (codeRType σ) = RType.ord σ :=
  PolyFix.ind (P := rTypeSig.polyEndo)
    (motive := fun {_} t => ordCode (codeRType t) = RType.ord t)
    (fun i childx ih =>
      match i, childx, ih with
      | RTypeShape.o, _, _ => ordCode_pair_zero
      | RTypeShape.arrow, childx, ih => by
        change ordCode (Nat.pair 1
            (Nat.pair (codeRType (childx (⟨0, by decide⟩ : Fin (rTypeSig.ar
                RTypeShape.arrow))))
              (codeRType (childx (⟨1, by decide⟩ : Fin (rTypeSig.ar
                RTypeShape.arrow)))))) = _
        rw [ordCode_pair_one,
          ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow)),
          ih (⟨1, by decide⟩ : Fin (rTypeSig.ar RTypeShape.arrow))]
        rfl
      | RTypeShape.omega, childx, ih => by
        change ordCode (Nat.pair 2 (codeRType (childx (⟨0, by decide⟩ :
            Fin (rTypeSig.ar RTypeShape.omega))))) = _
        rw [ordCode_pair_two,
          ih (⟨0, by decide⟩ : Fin (rTypeSig.ar RTypeShape.omega))]
        rfl) σ

end OneLambda

end GebLean.Ramified
