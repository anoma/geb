import Mathlib.CategoryTheory.Category.Basic

/-!
# Powers and Copowers

This module defines type-indexed products (powers) and coproducts (copowers)
for categories.

A copower `S ·. X` for a type `S` and object `X` is characterized by the
adjunction:

  `Hom(S ·. X, Y) ≃ (S → Hom(X, Y))`

Dually, a power `X ^. S` is characterized by:

  `Hom(Y, X ^. S) ≃ (S → Hom(Y, X))`
-/

namespace GebLean

open CategoryTheory

universe u v

/-!
## Copowers
-/

/-- A category has copowers if for every type `S` and object `X`, there is an
object `S ·. X` with injections `X → S ·. X` indexed by elements of `S`, and a
universal property: any family of morphisms `X → Y` indexed by `S` factors
uniquely through the copower. -/
class HasCopowers (C : Type u) [Category.{v} C] where
  /-- The copower object S · X for a type S and object X. -/
  copower : Type v → C → C
  /-- The family of injections indexed by elements of S. -/
  inj : ∀ (S : Type v) (X : C), S → (X ⟶ copower S X)
  /-- The universal property: any family factors through the copower. -/
  desc : ∀ {S : Type v} {X Y : C}, (S → (X ⟶ Y)) → (copower S X ⟶ Y)
  /-- The family factors through the universal morphism. -/
  fac : ∀ {S : Type v} {X Y : C} (f : S → (X ⟶ Y)) (s : S),
    inj S X s ≫ desc f = f s
  /-- Uniqueness of the factorization. -/
  uniq : ∀ {S : Type v} {X Y : C} (f : S → (X ⟶ Y)) (g : copower S X ⟶ Y),
    (∀ s, inj S X s ≫ g = f s) → g = desc f

namespace HasCopowers

variable {C : Type u} [Category.{v} C] [HasCopowers C]

/-- Notation for the copower. -/
infixl:70 " ·. " => copower

/-- Extensionality for morphisms out of copowers: two morphisms are equal
if they agree on all injections. -/
theorem ext {S : Type v} {X Y : C} (f g : S ·. X ⟶ Y)
    (h : ∀ s, inj S X s ≫ f = inj S X s ≫ g) : f = g := by
  have hf := uniq (fun s => inj S X s ≫ f) f (fun _ => rfl)
  have hg := uniq (fun s => inj S X s ≫ f) g (fun s => (h s).symm)
  rw [hf, hg]

/-- Functorial action of copowers on the base object.
Given `g : X → Y`, we get `mapVal g : S · X → S · Y`. -/
def mapVal {S : Type v} {X Y : C} (g : X ⟶ Y) : copower S X ⟶ copower S Y :=
  desc (fun s => g ≫ inj S Y s)

@[simp]
theorem mapVal_inj {S : Type v} {X Y : C} (g : X ⟶ Y) (s : S) :
    inj S X s ≫ mapVal g = g ≫ inj S Y s := fac _ s

@[simp]
theorem mapVal_id {S : Type v} {X : C} : mapVal (𝟙 X) = 𝟙 (copower S X) := by
  apply ext
  intro s
  rw [mapVal_inj, Category.id_comp, Category.comp_id]

@[simp]
theorem mapVal_comp {S : Type v} {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapVal (f ≫ g) = mapVal f ≫ mapVal (S := S) g := by
  apply ext
  intro s
  calc inj S X s ≫ mapVal (f ≫ g) = (f ≫ g) ≫ inj S Z s := mapVal_inj _ s
    _ = f ≫ g ≫ inj S Z s := by rw [Category.assoc]
    _ = f ≫ (inj S Y s ≫ mapVal g) := by rw [← mapVal_inj g s]
    _ = (f ≫ inj S Y s) ≫ mapVal g := by rw [← Category.assoc]
    _ = (inj S X s ≫ mapVal f) ≫ mapVal g := by rw [← mapVal_inj f s]
    _ = inj S X s ≫ mapVal f ≫ mapVal g := by rw [Category.assoc]

/-- Functorial action of copowers on the indexing type.
Given `f : S → T`, we get `mapIdx f : S · X → T · X`. -/
def mapIdx {S T : Type v} {X : C} (f : S → T) : copower S X ⟶ copower T X :=
  desc (fun s => inj T X (f s))

@[simp]
theorem mapIdx_inj {S T : Type v} {X : C} (f : S → T) (s : S) :
    inj S X s ≫ mapIdx f = inj T X (f s) := fac _ s

@[simp]
theorem mapIdx_id {S : Type v} {X : C} : mapIdx (id : S → S) = 𝟙 (copower S X) := by
  apply ext
  intro s
  rw [mapIdx_inj, id_eq, Category.comp_id]

@[simp]
theorem mapIdx_comp {S T U : Type v} {X : C} (f : S → T) (g : T → U) :
    mapIdx (g ∘ f) = mapIdx f ≫ mapIdx (X := X) g := by
  apply ext
  intro s
  calc inj S X s ≫ mapIdx (g ∘ f) = inj U X ((g ∘ f) s) := mapIdx_inj _ s
    _ = inj U X (g (f s)) := rfl
    _ = inj T X (f s) ≫ mapIdx g := (mapIdx_inj g _).symm
    _ = (inj S X s ≫ mapIdx f) ≫ mapIdx g := by rw [← mapIdx_inj f s]
    _ = inj S X s ≫ mapIdx f ≫ mapIdx g := by rw [Category.assoc]

/-- Combined functorial action: given `f : S → T` and `g : X → Y`,
we get `bimap f g : S · X → T · Y`. -/
def bimap {S T : Type v} {X Y : C} (f : S → T) (g : X ⟶ Y) :
    copower S X ⟶ copower T Y :=
  desc (fun s => g ≫ inj T Y (f s))

@[simp]
theorem bimap_inj {S T : Type v} {X Y : C} (f : S → T) (g : X ⟶ Y) (s : S) :
    inj S X s ≫ bimap f g = g ≫ inj T Y (f s) := fac _ s

theorem bimap_eq_mapIdx_mapVal {S T : Type v} {X Y : C} (f : S → T) (g : X ⟶ Y) :
    bimap f g = mapIdx f ≫ mapVal (S := T) g := by
  apply ext
  intro s
  rw [bimap_inj, ← Category.assoc, mapIdx_inj, mapVal_inj]

theorem bimap_eq_mapVal_mapIdx {S T : Type v} {X Y : C} (f : S → T) (g : X ⟶ Y) :
    bimap f g = mapVal g ≫ mapIdx (X := Y) f := by
  apply ext
  intro s
  calc inj S X s ≫ bimap f g = g ≫ inj T Y (f s) := bimap_inj _ _ s
    _ = g ≫ (inj S Y s ≫ mapIdx f) := by rw [← mapIdx_inj f s]
    _ = (g ≫ inj S Y s) ≫ mapIdx f := by rw [← Category.assoc]
    _ = (inj S X s ≫ mapVal g) ≫ mapIdx f := by rw [← mapVal_inj g s]
    _ = inj S X s ≫ mapVal g ≫ mapIdx f := by rw [Category.assoc]

@[simp]
theorem bimap_id {S : Type v} {X : C} : bimap (id : S → S) (𝟙 X) = 𝟙 (copower S X) := by
  apply ext
  intro s
  rw [bimap_inj, id_eq, Category.id_comp, Category.comp_id]

@[simp]
theorem bimap_comp {S T U : Type v} {X Y Z : C}
    (f₁ : S → T) (g₁ : X ⟶ Y) (f₂ : T → U) (g₂ : Y ⟶ Z) :
    bimap (f₂ ∘ f₁) (g₁ ≫ g₂) = bimap f₁ g₁ ≫ bimap f₂ g₂ := by
  apply ext
  intro s
  have step1 : inj S X s ≫ bimap (f₂ ∘ f₁) (g₁ ≫ g₂) =
      (g₁ ≫ g₂) ≫ inj U Z (f₂ (f₁ s)) := bimap_inj _ _ s
  calc inj S X s ≫ bimap (f₂ ∘ f₁) (g₁ ≫ g₂)
      = (g₁ ≫ g₂) ≫ inj U Z (f₂ (f₁ s)) := step1
    _ = g₁ ≫ g₂ ≫ inj U Z (f₂ (f₁ s)) := by rw [Category.assoc]
    _ = g₁ ≫ (inj T Y (f₁ s) ≫ bimap f₂ g₂) := by rw [← bimap_inj f₂ g₂]
    _ = (g₁ ≫ inj T Y (f₁ s)) ≫ bimap f₂ g₂ := by rw [← Category.assoc]
    _ = (inj S X s ≫ bimap f₁ g₁) ≫ bimap f₂ g₂ := by rw [← bimap_inj f₁ g₁]
    _ = inj S X s ≫ bimap f₁ g₁ ≫ bimap f₂ g₂ := by rw [Category.assoc]

/-- Postcomposing desc with a morphism: `desc f ≫ g = desc (fun s => f s ≫ g)`. -/
theorem desc_comp {S : Type v} {X Y Z : C} (f : S → (X ⟶ Y)) (g : Y ⟶ Z) :
    desc f ≫ g = desc (fun s => f s ≫ g) := by
  apply ext
  intro s
  rw [← Category.assoc, fac, ← fac (fun s' => f s' ≫ g) s]

/-- If the families commute with postcomposition, then desc respects it. -/
theorem desc_postcomp_eq {S : Type v} {X Y Z : C} (f : S → (X ⟶ Y)) (h : S → (X ⟶ Z))
    (g : Y ⟶ Z) (hfg : ∀ s, f s ≫ g = h s) :
    desc f ≫ g = desc h := by
  rw [desc_comp]
  congr 1
  funext s
  exact hfg s

/-- Copower round-trip: `desc (fun s => inj s ≫ g) = g`. -/
@[simp]
theorem desc_inj {S : Type v} {X Y : C} (g : copower S X ⟶ Y) :
    desc (fun s => inj S X s ≫ g) = g := by
  apply ext
  intro s
  rw [fac]

end HasCopowers

end GebLean
