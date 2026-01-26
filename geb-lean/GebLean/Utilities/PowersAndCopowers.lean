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

/-!
## Powers
-/

/-- A category has powers if for every type `S` and object `X`, there is an
object `X ^. S` with projections `X ^. S → X` indexed by elements of `S`, and a
universal property: any family of morphisms `Y → X` indexed by `S` factors
uniquely through the power. -/
class HasPowers (C : Type u) [Category.{v} C] where
  /-- The power object X ^. S for an object X and type S. -/
  power : C → Type v → C
  /-- The family of projections indexed by elements of S. -/
  proj : ∀ (X : C) (S : Type v), S → (power X S ⟶ X)
  /-- The universal property: any family factors through the power. -/
  lift : ∀ {X : C} {S : Type v} {Y : C}, (S → (Y ⟶ X)) → (Y ⟶ power X S)
  /-- The family factors through the universal morphism. -/
  fac : ∀ {X : C} {S : Type v} {Y : C} (f : S → (Y ⟶ X)) (s : S),
    lift f ≫ proj X S s = f s
  /-- Uniqueness of the factorization. -/
  uniq : ∀ {X : C} {S : Type v} {Y : C} (f : S → (Y ⟶ X)) (g : Y ⟶ power X S),
    (∀ s, g ≫ proj X S s = f s) → g = lift f

namespace HasPowers

variable {C : Type u} [Category.{v} C] [HasPowers C]

/-- Notation for the power. -/
infixl:80 " ^. " => power

/-- Extensionality for morphisms into powers: two morphisms are equal
if they agree on all projections. -/
theorem ext {X : C} {S : Type v} {Y : C} (f g : Y ⟶ X ^. S)
    (h : ∀ s, f ≫ proj X S s = g ≫ proj X S s) : f = g := by
  have hf := uniq (fun s => f ≫ proj X S s) f (fun _ => rfl)
  have hg := uniq (fun s => f ≫ proj X S s) g (fun s => (h s).symm)
  rw [hf, hg]

/-- Functorial action of powers on the base object.
Given `g : X → Y`, we get `mapVal g : X ^. S → Y ^. S`. -/
def mapVal {X Y : C} {S : Type v} (g : X ⟶ Y) : power X S ⟶ power Y S :=
  lift (fun s => proj X S s ≫ g)

@[simp]
theorem mapVal_proj {X Y : C} {S : Type v} (g : X ⟶ Y) (s : S) :
    mapVal g ≫ proj Y S s = proj X S s ≫ g := fac _ s

@[simp]
theorem mapVal_id {X : C} {S : Type v} : mapVal (𝟙 X) = 𝟙 (power X S) := by
  apply ext
  intro s
  rw [mapVal_proj, Category.comp_id, Category.id_comp]

@[simp]
theorem mapVal_comp {X Y Z : C} {S : Type v} (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapVal (f ≫ g) = mapVal (S := S) f ≫ mapVal g := by
  apply ext
  intro s
  calc mapVal (f ≫ g) ≫ proj Z S s = proj X S s ≫ (f ≫ g) := mapVal_proj _ s
    _ = (proj X S s ≫ f) ≫ g := by rw [Category.assoc]
    _ = (mapVal f ≫ proj Y S s) ≫ g := by rw [← mapVal_proj f s]
    _ = mapVal f ≫ proj Y S s ≫ g := by rw [Category.assoc]
    _ = mapVal f ≫ (mapVal g ≫ proj Z S s) := by rw [← mapVal_proj g s]
    _ = (mapVal f ≫ mapVal g) ≫ proj Z S s := by rw [← Category.assoc]

/-- Functorial action of powers on the indexing type.
Given `f : S → T`, we get `mapIdx f : X ^. T → X ^. S` (contravariant). -/
def mapIdx {X : C} {S T : Type v} (f : S → T) : power X T ⟶ power X S :=
  lift (fun s => proj X T (f s))

@[simp]
theorem mapIdx_proj {X : C} {S T : Type v} (f : S → T) (s : S) :
    mapIdx f ≫ proj X S s = proj X T (f s) := fac _ s

@[simp]
theorem mapIdx_id {X : C} {S : Type v} : mapIdx (id : S → S) = 𝟙 (power X S) := by
  apply ext
  intro s
  rw [mapIdx_proj, id_eq, Category.id_comp]

@[simp]
theorem mapIdx_comp {X : C} {S T U : Type v} (f : S → T) (g : T → U) :
    mapIdx (g ∘ f) = mapIdx (X := X) g ≫ mapIdx f := by
  apply ext
  intro s
  calc mapIdx (g ∘ f) ≫ proj X S s = proj X U ((g ∘ f) s) := mapIdx_proj _ s
    _ = proj X U (g (f s)) := rfl
    _ = mapIdx g ≫ proj X T (f s) := (mapIdx_proj g _).symm
    _ = mapIdx g ≫ (mapIdx f ≫ proj X S s) := by rw [← mapIdx_proj f s]
    _ = (mapIdx g ≫ mapIdx f) ≫ proj X S s := by rw [← Category.assoc]

/-- Combined functorial action: given `f : S → T` and `g : X → Y`,
we get `bimap f g : X ^. T → Y ^. S` (contravariant in index, covariant in object). -/
def bimap {X Y : C} {S T : Type v} (f : S → T) (g : X ⟶ Y) :
    power X T ⟶ power Y S :=
  lift (fun s => proj X T (f s) ≫ g)

@[simp]
theorem bimap_proj {X Y : C} {S T : Type v} (f : S → T) (g : X ⟶ Y) (s : S) :
    bimap f g ≫ proj Y S s = proj X T (f s) ≫ g := fac _ s

theorem bimap_eq_mapIdx_mapVal {X Y : C} {S T : Type v} (f : S → T) (g : X ⟶ Y) :
    bimap f g = mapIdx f ≫ mapVal (S := S) g := by
  apply ext
  intro s
  rw [bimap_proj, Category.assoc, mapVal_proj, ← Category.assoc, mapIdx_proj]

theorem bimap_eq_mapVal_mapIdx {X Y : C} {S T : Type v} (f : S → T) (g : X ⟶ Y) :
    bimap f g = mapVal (S := T) g ≫ mapIdx (X := Y) f := by
  apply ext
  intro s
  calc bimap f g ≫ proj Y S s = proj X T (f s) ≫ g := bimap_proj _ _ s
    _ = (mapVal g ≫ proj Y T (f s)) ≫ 𝟙 Y := by rw [← mapVal_proj g, Category.comp_id]
    _ = mapVal g ≫ proj Y T (f s) := by rw [Category.comp_id]
    _ = mapVal g ≫ (mapIdx f ≫ proj Y S s) := by rw [← mapIdx_proj f s]
    _ = (mapVal g ≫ mapIdx f) ≫ proj Y S s := by rw [← Category.assoc]

@[simp]
theorem bimap_id {X : C} {S : Type v} : bimap (id : S → S) (𝟙 X) = 𝟙 (power X S) := by
  apply ext
  intro s
  rw [bimap_proj, id_eq, Category.comp_id, Category.id_comp]

@[simp]
theorem bimap_comp {X Y Z : C} {S T U : Type v}
    (f₁ : T → U) (g₁ : X ⟶ Y) (f₂ : S → T) (g₂ : Y ⟶ Z) :
    bimap (f₁ ∘ f₂) (g₁ ≫ g₂) = bimap f₁ g₁ ≫ bimap f₂ g₂ := by
  apply ext
  intro s
  have step1 : bimap (f₁ ∘ f₂) (g₁ ≫ g₂) ≫ proj Z S s =
      proj X U (f₁ (f₂ s)) ≫ (g₁ ≫ g₂) := bimap_proj _ _ s
  calc bimap (f₁ ∘ f₂) (g₁ ≫ g₂) ≫ proj Z S s
      = proj X U (f₁ (f₂ s)) ≫ (g₁ ≫ g₂) := step1
    _ = (proj X U (f₁ (f₂ s)) ≫ g₁) ≫ g₂ := by rw [Category.assoc]
    _ = (bimap f₁ g₁ ≫ proj Y T (f₂ s)) ≫ g₂ := by rw [← bimap_proj f₁ g₁]
    _ = bimap f₁ g₁ ≫ proj Y T (f₂ s) ≫ g₂ := by rw [Category.assoc]
    _ = bimap f₁ g₁ ≫ (bimap f₂ g₂ ≫ proj Z S s) := by rw [← bimap_proj f₂ g₂]
    _ = (bimap f₁ g₁ ≫ bimap f₂ g₂) ≫ proj Z S s := by rw [← Category.assoc]

/-- Precomposing lift with a morphism: `f ≫ lift g = lift (fun s => f ≫ g s)`. -/
theorem lift_comp {X : C} {S : Type v} {Y Z : C} (f : Z ⟶ Y) (g : S → (Y ⟶ X)) :
    f ≫ lift g = lift (fun s => f ≫ g s) := by
  apply ext
  intro s
  rw [Category.assoc, fac, ← fac (fun s' => f ≫ g s') s]

/-- If the families commute with precomposition, then lift respects it. -/
theorem lift_precomp_eq {X : C} {S : Type v} {Y Z : C} (f : S → (Y ⟶ X)) (h : S → (Z ⟶ X))
    (g : Z ⟶ Y) (hfg : ∀ s, g ≫ f s = h s) :
    g ≫ lift f = lift h := by
  rw [lift_comp]
  congr 1
  funext s
  exact hfg s

/-- Power round-trip: `lift (fun s => g ≫ proj s) = g`. -/
@[simp]
theorem lift_proj {X : C} {S : Type v} {Y : C} (g : Y ⟶ power X S) :
    lift (fun s => g ≫ proj X S s) = g := by
  apply ext
  intro s
  rw [fac]

end HasPowers

end GebLean
