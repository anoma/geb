import GebLean.ParamPoly
import GebLean.Utilities.DoubleCategory

/-!
# Yoneda Relation Double Category

The `relRelated` predicate from `ParamPoly` captures when
two morphisms `f : A ⟶ B` and `f' : A' ⟶ B'` in `C` are
related by a pair of Yoneda relations `(R, S)` via a
commutative square:

```
  A ──f──▶ B
  │        │
  R        S
  ▼        ▼
  A'──f'─▶ B'
```

This has the shape of a 2-cell in a double category.

- Objects: objects of `C`
- Horizontal morphisms: morphisms in `C`
- Vertical morphisms: Yoneda relations (`YonedaRel`)
- Squares: `relRelated` (`Prop`-valued)

Since the square type is `Prop`, all square laws
(associativity, identity, interchange) hold by proof
irrelevance once the boundary types match.
-/

namespace GebLean

open CategoryTheory Limits

universe u v

variable {C : Type u} [Category.{v} C]

/-- The square type family for the Yoneda relation double
category. Given vertical morphisms `R : YonedaRel A C`,
`S : YonedaRel B D` and horizontal morphisms `f : A ⟶ B`,
`f' : C ⟶ D`, the square is `relRelated f f' R S`. -/
abbrev yonedaRelSQS :
    @SquareSet C
      (fun (A B : C) => YonedaRel A B)
      (fun (A B : C) => (A ⟶ B)) :=
  fun R S f f' => relRelated f f' R S

/-- Horizontal composition of relatedness squares.

Given `relRelated f g R S` (a square with top `f`,
bottom `g`, left `R`, right `S`) and
`relRelated f' g' S T`, the composite has top
`f ≫ f'`, bottom `g ≫ g'`, left `R`, right `T`.

The witness at the `YonedaProdOver` level is the
composite `φ₁ ≫ φ₂` of the two individual witnesses,
with commutativity following from `yonedaProdMap_comp`. -/
theorem relRelatedHComp
    {A₁ A₂ A₃ B₁ B₂ B₃ : C}
    {R : YonedaRel A₁ B₁}
    {S : YonedaRel A₂ B₂}
    {T : YonedaRel A₃ B₃}
    {f : A₁ ⟶ A₂} {f' : A₂ ⟶ A₃}
    {g : B₁ ⟶ B₂} {g' : B₂ ⟶ B₃}
    (α : relRelated f g R S)
    (β : relRelated f' g' S T) :
    relRelated (f ≫ f') (g ≫ g') R T := by
  induction R using Quotient.inductionOn with
  | h R₀ =>
  induction S using Quotient.inductionOn with
  | h S₀ =>
  induction T using Quotient.inductionOn with
  | h T₀ =>
  obtain ⟨φ₁, hφ₁⟩ := α
  obtain ⟨φ₂, hφ₂⟩ := β
  exact ⟨φ₁ ≫ φ₂, by
    rw [Category.assoc, hφ₂,
      ← Category.assoc, hφ₁, Category.assoc,
      yonedaProdMap_comp]⟩

/-- Horizontal identity square: for each vertical
morphism `R : YonedaRel A B`, the pair `(𝟙 A, 𝟙 B)` is
`(R, R)`-related.

The witness is the identity `𝟙 R₀.left`, with
commutativity following from `yonedaProdMap_id`. -/
theorem relRelatedSqHorId
    {A B : C}
    (R : YonedaRel (C := C) A B) :
    relRelated (𝟙 A) (𝟙 B) R R := by
  induction R using Quotient.inductionOn with
  | h R₀ =>
  exact ⟨𝟙 R₀.left, by
    simp [yonedaProdMap_id]⟩

/-- Vertical identity square: for each horizontal
morphism `f : A ⟶ B`, the pair `(relId A, relId B)` is
`(f, f)`-related.

The witness is `yoneda.map f`, with commutativity
checked componentwise via `yonedaProdPresheaf_hom_ext`. -/
theorem relRelatedSqVertId
    {A B : C}
    (f : A ⟶ B) :
    relRelated f f
      (relId (C := C) A) (relId B) := by
  change YonedaProdOverRelated
    (yonedaProdOverId A) (yonedaProdOverId B) f f
  refine ⟨yoneda.map f, ?_⟩
  ext T x
  exact Prod.ext rfl rfl

end GebLean
