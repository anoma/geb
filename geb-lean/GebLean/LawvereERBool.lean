import GebLean.LawvereER

/-!
# Boolean Operations on Elementary Recursive Terms

Defines `boolNot`, `boolAnd`, and `boolEqNat` as
specific `ERMor1` terms, together with `@[simp]`
interpretation lemmas and Boolean-closure properties.
Convention: `1 = true`, `0 = false`.

These operations are the building blocks for the
finite-product and equalizer constructions in
`LawvereERLex.lean`.
-/

namespace GebLean

/-- Boolean negation as the indicator of `x = 0`:
returns `1` if input is `0`, else `0`.
Definable as `1 ⊖ x`. -/
def ERMor1.boolNot : ERMor1 1 :=
  ERMor1.comp ERMor1.sub fun i => match i with
    | ⟨0, _⟩ => ERMor1.oneN 1
    | ⟨1, _⟩ => ERMor1.proj 0

/-- Interpretation of `boolNot`: returns `1 ⊖ ctx 0`. -/
@[simp] theorem ERMor1.interp_boolNot
    (ctx : Fin 1 → ℕ) :
    ERMor1.boolNot.interp ctx = 1 - ctx 0 :=
  rfl

/-- `boolNot` always returns a Boolean value. -/
theorem ERMor1.boolNot_le_one (ctx : Fin 1 → ℕ) :
    ERMor1.boolNot.interp ctx ≤ 1 := by
  rw [ERMor1.interp_boolNot]
  exact Nat.sub_le 1 (ctx 0)

/-- Boolean conjunction.  At arity 2, computes
`ctx 0 * ctx 1` via bounded summation; for `{0, 1}`
inputs this is the Boolean `and`. -/
def ERMor1.boolAnd : ERMor1 2 :=
  ERMor1.bsum (ERMor1.proj 1)

/-- Interpretation of `boolAnd`: returns the product
of its two inputs. -/
@[simp] theorem ERMor1.interp_boolAnd
    (ctx : Fin 2 → ℕ) :
    ERMor1.boolAnd.interp ctx = ctx 0 * ctx 1 := by
  change natBSum (ctx 0) _ = ctx 0 * ctx 1
  have h : (fun i : ℕ =>
      (ERMor1.proj (1 : Fin 2)).interp
        (Fin.cons i (Fin.tail ctx))) =
      (fun _ : ℕ => ctx 1) := by
    funext i
    rfl
  rw [h]
  exact natBSum_const _ _

/-- `boolAnd` returns a Boolean value when both its
inputs are Boolean. -/
theorem ERMor1.boolAnd_le_one_of_le_one
    (ctx : Fin 2 → ℕ)
    (h0 : ctx 0 ≤ 1) (h1 : ctx 1 ≤ 1) :
    ERMor1.boolAnd.interp ctx ≤ 1 := by
  rw [ERMor1.interp_boolAnd]
  calc ctx 0 * ctx 1
      _ ≤ 1 * ctx 1 := Nat.mul_le_mul_right _ h0
      _ ≤ 1 * 1 := Nat.mul_le_mul_left _ h1
      _ = 1 := Nat.one_mul 1

end GebLean
