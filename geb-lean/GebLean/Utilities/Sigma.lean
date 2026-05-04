import Mathlib.Logic.Equiv.Defs

/-!
# Sigma Utilities

Miscellaneous utilities for working with sigma types.
-/

universe u v

namespace GebLean

/-- A subtype of a sigma where both indices are constrained to specific
values is equivalent to the underlying fiber. -/
def sigmaTrivialSubtype {α : Type*} {β : α → α → Type*} (a b : α) :
    {m : Σ (a' b' : α), β a' b' // m.1 = a ∧ m.2.1 = b} ≃ β a b where
  toFun m := by
    rcases m with ⟨⟨a', b', x⟩, ha, hb⟩
    cases ha
    cases hb
    exact x
  invFun x := ⟨⟨a, b, x⟩, rfl, rfl⟩
  left_inv := by
    intro m
    rcases m with ⟨⟨a', b', x⟩, ha, hb⟩
    cases ha
    cases hb
    rfl
  right_inv := by
    intro x
    rfl

section SigmaCast

universe w w'

/--
When `cast` acts on a Sigma type along a proof
derived from a family equality `F = G`, it
preserves the first component and casts the
second.
-/
@[simp]
theorem sigma_cast_of_funEq
    {K : Type w} {F G : K → Type w'}
    (h : F = G) (k : K) (e : F k) :
    cast (congrArg (fun H => Σ k, H k) h)
      ⟨k, e⟩ = ⟨k, cast (congrFun h k) e⟩ := by
  subst h; rfl

/--
The first component of a Sigma cast along a
family equality is preserved.
-/
@[simp]
theorem sigma_cast_fst_of_funEq
    {K : Type w} {F G : K → Type w'}
    (h : F = G) (k : K) (e : F k) :
    (cast (congrArg (fun H => Σ k, H k) h)
      ⟨k, e⟩).fst = k := by
  subst h; rfl

/--
When a sigma-typed element is matched after a
`cast` along a proof derived from a family
equality `F = G`, the first component is
preserved and the function applied to the
second component can be rewritten in terms of
the original element's second component.
-/
theorem sigma_cast_match_apply
    {K : Type w} {F G : K → Type w'}
    {R : Type*}
    (h : (Σ k, F k) = (Σ k, G k))
    (hfam : F = G)
    (hh : h = congrArg (fun H => Σ k, H k) hfam)
    (f : (k : K) → G k → R)
    (k : K) (e : F k) :
    (match cast h ⟨k, e⟩ with
     | ⟨k', e'⟩ => f k' e') =
    f k (cast (congrFun hfam k) e) := by
  subst hh; subst hfam; rfl


end SigmaCast

end GebLean
