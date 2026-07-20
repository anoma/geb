import Geb.Mathlib.Data.PFunctor.Slice.Basic

/-!
# The translate augmentation of a slice endofunctor

Given a slice endofunctor `F` over `I` and a map `v : Y → I` from a leaf
type `Y`, the translate `translate v F` is the slice endofunctor `Y + F(-)`
over `I`: a fresh nullary shape for each `y : Y` whose shape-output map is
`v y`, alongside `F`'s own shapes with their positions and maps unchanged.
This is the augmentation `Y + F(-)` of Gambino–Kock 2013, whose initial
algebra (once the associated W-type is in hand) is the free monad on `F`
with leaves `Y`.

## Main definitions

* `SlicePFunctor.translate` — the augmented slice endofunctor `Y + F(-)`.

## Main statements

* `SlicePFunctor.translate_A`, `translate_B_inl`, `translate_B_inr`,
  `translate_q_inl`, `translate_q_inr`, `translate_r_inr` — the
  characterization of each field of `translate v F` in terms of `v` and `F`.

## References

N. Gambino and J. Kock, "Polynomial functors and polynomial monads",
Mathematical Proceedings of the Cambridge Philosophical Society 154 (2013)
153-192, DOI `10.1017/S0305004112000394`.

## Tags

polynomial functor, slice category, free monad, container, PFunctor
-/

namespace SlicePFunctor

universe uY uA uB uI

/-- The translate of a slice endofunctor `F` over `I` along a leaf map
`v : Y → I`: the slice endofunctor `Y + F(-)`. Shapes are `Y ⊕ F.A`; a left
shape `y` is nullary (`PEmpty` positions) and outputs `v y`, a right shape
`a` keeps `F`'s positions, direction-input map, and shape-output map. -/
def translate {I : Type uI} {Y : Type uY} (v : Y → I)
    (F : SlicePFunctor.{uA, uB, uI, uI} I I) : SlicePFunctor.{max uY uA, uB, uI, uI} I I where
  A := Y ⊕ F.A
  B := fun a => match a with
    | .inl _ => PEmpty
    | .inr a => F.B a
  r := fun x => match x with
    | ⟨.inl _, e⟩ => e.elim
    | ⟨.inr a, b⟩ => F.r ⟨a, b⟩
  q := Sum.elim v F.q

variable {I : Type uI} {Y : Type uY} {v : Y → I} {F : SlicePFunctor.{uA, uB, uI, uI} I I}

/-- The shape type of `translate v F` is `Y ⊕ F.A`. The ascription orients
`Sum`'s universe unification along `translate`'s own `max uY uA`; without it
the elaborator matches `Sum`'s implicit levels against `(translate v F).A`'s
level in its normalized (alphabetical) order `max uA uY` and fails on `Y`. -/
@[simp]
theorem translate_A : (translate v F).A = (Y ⊕ F.A : Type (max uY uA)) :=
  rfl

/-- A left shape `y` of `translate v F` is nullary. -/
@[simp]
theorem translate_B_inl (y : Y) : (translate v F).B (.inl y) = PEmpty :=
  rfl

/-- A right shape `a` of `translate v F` keeps `F`'s positions at `a`. -/
@[simp]
theorem translate_B_inr (a : F.A) : (translate v F).B (.inr a) = F.B a :=
  rfl

/-- The shape-output map of `translate v F` at a left shape `y` is `v y`. -/
@[simp]
theorem translate_q_inl (y : Y) : (translate v F).q (.inl y) = v y :=
  rfl

/-- The shape-output map of `translate v F` at a right shape `a` is `F.q a`. -/
@[simp]
theorem translate_q_inr (a : F.A) : (translate v F).q (.inr a) = F.q a :=
  rfl

/-- The direction-input map of `translate v F` at a right shape `a` and
position `b` is `F.r ⟨a, b⟩`. -/
@[simp]
theorem translate_r_inr (a : F.A) (b : F.B a) :
    (translate v F).r ⟨.inr a, b⟩ = F.r ⟨a, b⟩ :=
  rfl

end SlicePFunctor
