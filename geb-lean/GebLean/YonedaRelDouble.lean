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

/-- The square type family for the Yoneda relation
double category. Given vertical morphisms
`R : YonedaRel A C`, `S : YonedaRel B D` and
horizontal morphisms `f : A ⟶ B`, `f' : C ⟶ D`,
the square is `relRelated f f' R S`. -/
abbrev yonedaRelSQS :
    @SquareSet C YonedaRel (homSetOfQuiver C) :=
  fun R S f f' => relRelated f f' R S

@[reassoc (attr := simp)]
theorem yonedaProdOverComp_fst {X Y Z : C}
    (R : YonedaProdOver X Y)
    (S : YonedaProdOver Y Z) :
    (yonedaProdOverComp R S).hom ≫
      yonedaProdFst X Z =
    presheafPullbackFst
      (R.hom ≫ yonedaProdSnd X Y)
      (S.hom ≫ yonedaProdFst Y Z) ≫
    R.hom ≫ yonedaProdFst X Y := by
  simp [yonedaProdOverComp, yonedaProdLift]

@[reassoc (attr := simp)]
theorem yonedaProdOverComp_snd {X Y Z : C}
    (R : YonedaProdOver X Y)
    (S : YonedaProdOver Y Z) :
    (yonedaProdOverComp R S).hom ≫
      yonedaProdSnd X Z =
    presheafPullbackSnd
      (R.hom ≫ yonedaProdSnd X Y)
      (S.hom ≫ yonedaProdFst Y Z) ≫
    S.hom ≫ yonedaProdSnd Y Z := by
  simp [yonedaProdOverComp, yonedaProdLift]

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

/-- Vertical composition of relatedness squares.

Given `relRelated f g R S` and `relRelated g h R' S'`,
the composite has top `f`, bottom `h`, left
`relComp R R'`, right `relComp S S'`.

At the `YonedaProdOver` level, the witness is
constructed via `presheafPullbackLift` from the
two individual witnesses composed with the pullback
projections. -/
theorem relRelatedVComp
    {A₁ A₂ A₃ B₁ B₂ B₃ : C}
    {R : YonedaRel A₁ A₂}
    {S : YonedaRel B₁ B₂}
    {R' : YonedaRel A₂ A₃}
    {S' : YonedaRel B₂ B₃}
    {f : A₁ ⟶ B₁} {g : A₂ ⟶ B₂} {h : A₃ ⟶ B₃}
    (α : relRelated f g R S)
    (β : relRelated g h R' S') :
    relRelated f h (relComp R R')
      (relComp S S') := by
  induction R using Quotient.inductionOn with
  | h R₀ =>
  induction S using Quotient.inductionOn with
  | h S₀ =>
  induction R' using Quotient.inductionOn with
  | h R₀' =>
  induction S' using Quotient.inductionOn with
  | h S₀' =>
  obtain ⟨φ₁, hφ₁⟩ := α
  obtain ⟨φ₂, hφ₂⟩ := β
  have hφ₁_r := reassoc_of% hφ₁
  have hφ₂_r := reassoc_of% hφ₂
  have pbcondR := presheafPullbackCondition
    (R₀.hom ≫ yonedaProdSnd A₁ A₂)
    (R₀'.hom ≫ yonedaProdFst A₂ A₃)
  have pbcondR_r := reassoc_of% pbcondR
  refine ⟨presheafPullbackLift
    (S₀.hom ≫ yonedaProdSnd B₁ B₂)
    (S₀'.hom ≫ yonedaProdFst B₂ B₃)
    (presheafPullbackFst
      (R₀.hom ≫ yonedaProdSnd A₁ A₂)
      (R₀'.hom ≫ yonedaProdFst A₂ A₃) ≫ φ₁)
    (presheafPullbackSnd
      (R₀.hom ≫ yonedaProdSnd A₁ A₂)
      (R₀'.hom ≫ yonedaProdFst A₂ A₃) ≫ φ₂)
    ?_, ?_⟩
  · -- Pullback condition for the lift
    simp only [Category.assoc, hφ₁_r,
      yonedaProdMap_snd, hφ₂_r,
      yonedaProdMap_fst]
    exact pbcondR_r _
  · -- Commutativity
    apply yonedaProdPresheaf_hom_ext <;>
    simp only [Category.assoc,
      yonedaProdOverComp_fst,
      yonedaProdOverComp_fst_assoc,
      yonedaProdOverComp_snd,
      yonedaProdOverComp_snd_assoc,
      yonedaProdMap_fst, yonedaProdMap_snd,
      PullbackCone.IsLimit.lift_fst_assoc,
      PullbackCone.IsLimit.lift_snd_assoc,
      hφ₁_r, hφ₂_r]

/-- Operations for the Yoneda relation double category
on objects of `C`. -/
def yonedaRelDoubleOps :
    DoubleCategoryOps C YonedaRel
      (homSetOfQuiver C) yonedaRelSQS where
  vComp := fun R S => relComp R S
  hComp := fun f g => f ≫ g
  vId := fun A => relId A
  hId := fun A => 𝟙 A
  sqVComp := fun α β => relRelatedVComp α β
  sqHComp := fun α β => relRelatedHComp α β
  sqVertId := fun h => relRelatedSqVertId h
  sqHorId := fun v => relRelatedSqHorId v

/-- Laws for the Yoneda relation double category.

The vertical category laws follow from `relComp_assoc`,
`relComp_relId_left`, `relComp_relId_right`. The
horizontal category laws follow from `Category.assoc`,
`Category.id_comp`, `Category.comp_id`. All square
laws hold because the square type `relRelated` is
`Prop`-valued: either both sides have the same type
(use `Subsingleton.elim`) or the types differ by a
category law (use `Subsingleton.helim`). -/
theorem yonedaRelDoubleLaws :
    DoubleCategoryLaws
      (yonedaRelDoubleOps (C := C)) where
  vertLaws := {
    assoc := fun R S T => relComp_assoc R S T
    id_laws := {
      id_comp := fun R => relComp_relId_left R
      comp_id := fun R => relComp_relId_right R
    }
  }
  horLaws := {
    assoc := fun f g h => Category.assoc f g h
    id_laws := {
      id_comp := fun f => Category.id_comp f
      comp_id := fun f => Category.comp_id f
    }
  }
  sqLaws := {
    sqVAssoc := fun _ _ _ => by
      simp only [yonedaRelDoubleOps, relComp_assoc]
      exact HEq.rfl
    sqHAssoc := fun _ _ _ => by
      simp only [yonedaRelDoubleOps, Category.assoc]
      exact HEq.rfl
    sqVIdComp := fun _ => by
      simp only [yonedaRelDoubleOps,
        relComp_relId_left]
      exact HEq.rfl
    sqVCompId := fun _ => by
      simp only [yonedaRelDoubleOps,
        relComp_relId_right]
      exact HEq.rfl
    sqHIdComp := fun _ => by
      simp only [yonedaRelDoubleOps,
        Category.id_comp]
      exact HEq.rfl
    sqHCompId := fun _ => by
      simp only [yonedaRelDoubleOps,
        Category.comp_id]
      exact HEq.rfl
    interchange := fun _ _ _ _ =>
      Subsingleton.elim _ _
    vertIdVComp := fun _ _ =>
      Subsingleton.elim _ _
    horIdHComp := fun _ _ =>
      Subsingleton.elim _ _
    idOnId := fun _ =>
      Subsingleton.elim _ _
  }

/-- The Yoneda relation double category data on
objects of `C`: operations and laws bundled
together. -/
def yonedaRelDoubleData :
    DoubleCategoryData C YonedaRel
      (homSetOfQuiver C) yonedaRelSQS where
  toDoubleCategoryOps := yonedaRelDoubleOps
  laws := yonedaRelDoubleLaws

end GebLean
