import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Discrete.Basic
import GebLean.Weighted

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

/-!
## Copowers as Weighted Colimits over the Terminal Category

A copower `S ·. X` is exactly the weighted colimit of the constant diagram
`terminalDiagram X : Discrete PUnit ⥤ C` with weight
`terminalWeight S : (Discrete PUnit)ᵒᵖ ⥤ Type v` that picks the type `S`.

This provides a consistency check for the definitions and connects copowers
to the general theory of weighted colimits.
-/

section CopowerAsWeightedColimit

open CategoryTheory CategoryTheory.Limits CategoryTheory.Discrete

variable {C : Type u} [Category.{v} C]

/-- The constant functor from the discrete terminal category picking object X. -/
def terminalDiagram (X : C) : Discrete PUnit ⥤ C :=
  Functor.fromPUnit X

/-- The weight functor picking type S from the opposite of discrete terminal. -/
def terminalWeight (S : Type v) : (Discrete PUnit)ᵒᵖ ⥤ Type v where
  obj := fun _ => S
  map := fun _ => id

@[simp]
theorem terminalWeight_obj (S : Type v) (j : (Discrete PUnit)ᵒᵖ) :
    (terminalWeight S).obj j = S := rfl

@[simp]
theorem terminalWeight_map (S : Type v) {j₁ j₂ : (Discrete PUnit)ᵒᵖ} (f : j₁ ⟶ j₂) :
    (terminalWeight S).map f = id := rfl

@[simp]
theorem terminalDiagram_obj (X : C) (j : Discrete PUnit) :
    (terminalDiagram X).obj j = X := rfl

@[simp]
theorem terminalDiagram_map (X : C) {j₁ j₂ : Discrete PUnit} (f : j₁ ⟶ j₂) :
    (terminalDiagram X).map f = 𝟙 X := by
  simp only [terminalDiagram, Functor.fromPUnit]
  rfl

/-- The homToFunctor map for terminalDiagram is precomposition with identity. -/
theorem terminalDiagram_homToFunctor_map (X Y : C)
    {j₁ j₂ : (Discrete PUnit)ᵒᵖ} (f : j₁ ⟶ j₂) (g : X ⟶ Y) :
    (homToFunctor (terminalDiagram X) Y).map f g = g := by
  change (terminalDiagram X).map f.unop ≫ g = g
  simp only [terminalDiagram_map]
  exact Category.id_comp g

variable [HasCopowers C]

/-- The weighted cocone for a copower, with apex `copower S X` and legs given
by the injection maps. -/
def copowerCocone (S : Type v) (X : C) :
    WeightedCocone (terminalWeight S) (terminalDiagram X) where
  pt := HasCopowers.copower S X
  toWeightedCoconeOver := {
    app := fun _ s => HasCopowers.inj S X s
    naturality := fun j₁ j₂ f => by
      ext s
      simp only [types_comp_apply, terminalWeight_map, id_eq]
      rw [terminalDiagram_homToFunctor_map]
  }

/-- A weighted cocone over the terminal diagram and weight is determined by
a single family of morphisms `S → (X ⟶ pt)`. -/
def coconeOfFamily (S : Type v) (X : C) (apex : C) (fam : S → (X ⟶ apex)) :
    WeightedCocone (terminalWeight S) (terminalDiagram X) where
  pt := apex
  toWeightedCoconeOver := {
    app := fun _ s => fam s
    naturality := fun j₁ j₂ f => by
      ext s
      simp only [types_comp_apply, terminalWeight_map, id_eq]
      rw [terminalDiagram_homToFunctor_map]
  }

@[simp]
theorem copowerCocone_pt (S : Type v) (X : C) :
    (copowerCocone S X).pt = HasCopowers.copower S X := rfl

theorem copowerCocone_ι_app (S : Type v) (X : C) (j : (Discrete PUnit)ᵒᵖ) (s : S) :
    (copowerCocone S X).ι.app j s = HasCopowers.inj S X s := rfl

@[simp]
theorem copowerCocone_leg (S : Type v) (X : C) (j : Discrete PUnit) (s : S) :
    (copowerCocone S X).leg j s = HasCopowers.inj S X s := rfl

/-- The universal morphism from the copower cocone to any weighted cocone. -/
def copowerCoconeDesc (S : Type v) (X : C)
    (d : WeightedCocone (terminalWeight S) (terminalDiagram X)) :
    WeightedCocone.Hom (copowerCocone S X) d where
  hom := HasCopowers.desc (fun t => d.leg (mk ()) t)
  w := fun j s => by
    obtain ⟨⟨⟩⟩ := j
    simp only [copowerCocone_leg]
    have hfac := HasCopowers.fac (fun t => d.leg (mk ()) t) s
    simp only [terminalWeight_obj, terminalDiagram_obj] at hfac
    exact hfac

/-- Uniqueness of morphisms from the copower cocone. -/
theorem copowerCoconeDesc_unique (S : Type v) (X : C)
    (d : WeightedCocone (terminalWeight S) (terminalDiagram X))
    (f : WeightedCocone.Hom (copowerCocone S X) d) :
    f = copowerCoconeDesc S X d := by
  apply WeightedCocone.Hom.ext
  apply HasCopowers.ext
  intro s
  have hw := f.w (mk ()) s
  simp only [copowerCocone_leg] at hw
  simp only [copowerCoconeDesc]
  have hfac := HasCopowers.fac (fun t => d.leg (mk ()) t) s
  simp only [terminalWeight_obj, terminalDiagram_obj] at hfac
  rw [hfac]
  exact hw

/-- The copower cocone is initial in the category of weighted cocones,
making copowers weighted colimits over the terminal category. -/
def copowerIsWeightedColimit (S : Type v) (X : C) :
    IsWeightedColimit (copowerCocone S X) :=
  IsInitial.ofUniqueHom
    (fun d => copowerCoconeDesc S X d)
    (fun _ => copowerCoconeDesc_unique S X _)

end CopowerAsWeightedColimit

/-!
## Powers as Weighted Limits over the Terminal Category

Dually, a power `X ^. S` is exactly the weighted limit of the constant diagram
`terminalDiagram X : Discrete PUnit ⥤ C` with weight
`terminalWeightCov S : Discrete PUnit ⥤ Type v` that picks the type `S`.
-/

section PowerAsWeightedLimit

open CategoryTheory CategoryTheory.Limits CategoryTheory.Discrete

variable {C : Type u} [Category.{v} C]

/-- The covariant weight functor picking type S from discrete terminal. -/
def terminalWeightCov (S : Type v) : Discrete PUnit ⥤ Type v where
  obj := fun _ => S
  map := fun _ => id

@[simp]
theorem terminalWeightCov_obj (S : Type v) (j : Discrete PUnit) :
    (terminalWeightCov S).obj j = S := rfl

@[simp]
theorem terminalWeightCov_map (S : Type v) {j₁ j₂ : Discrete PUnit} (f : j₁ ⟶ j₂) :
    (terminalWeightCov S).map f = id := rfl

/-- The homFromFunctor map for terminalDiagram is postcomposition with identity. -/
theorem terminalDiagram_homFromFunctor_map (X Y : C)
    {j₁ j₂ : Discrete PUnit} (f : j₁ ⟶ j₂) (g : Y ⟶ X) :
    (homFromFunctor (terminalDiagram X) Y).map f g = g := by
  change g ≫ (terminalDiagram X).map f = g
  simp only [terminalDiagram_map, Category.comp_id]

variable [HasPowers C]

/-- The weighted cone for a power, with apex `power X S` and legs given
by the projection maps. -/
def powerCone (X : C) (S : Type v) :
    WeightedCone (terminalWeightCov S) (terminalDiagram X) where
  pt := HasPowers.power X S
  toWeightedConeUnder := {
    app := fun _ s => HasPowers.proj X S s
    naturality := fun j₁ j₂ f => by
      ext s
      simp only [types_comp_apply, terminalWeightCov_map, id_eq]
      rw [terminalDiagram_homFromFunctor_map]
  }

@[simp]
theorem powerCone_pt (X : C) (S : Type v) :
    (powerCone X S).pt = HasPowers.power X S := rfl

theorem powerCone_π_app (X : C) (S : Type v) (j : Discrete PUnit) (s : S) :
    (powerCone X S).π.app j s = HasPowers.proj X S s := rfl

@[simp]
theorem powerCone_leg (X : C) (S : Type v) (j : Discrete PUnit) (s : S) :
    (powerCone X S).leg j s = HasPowers.proj X S s := rfl

/-- The universal morphism from any weighted cone to the power cone. -/
def powerConeLift (X : C) (S : Type v)
    (d : WeightedCone (terminalWeightCov S) (terminalDiagram X)) :
    WeightedCone.Hom d (powerCone X S) where
  hom := HasPowers.lift (fun t => d.leg (mk ()) t)
  w := fun j s => by
    obtain ⟨⟨⟩⟩ := j
    simp only [powerCone_leg]
    have hfac := HasPowers.fac (fun t => d.leg (mk ()) t) s
    simp only [terminalWeightCov_obj, terminalDiagram_obj] at hfac
    exact hfac

/-- Uniqueness of morphisms to the power cone. -/
theorem powerConeLift_unique (X : C) (S : Type v)
    (d : WeightedCone (terminalWeightCov S) (terminalDiagram X))
    (f : WeightedCone.Hom d (powerCone X S)) :
    f = powerConeLift X S d := by
  apply WeightedCone.Hom.ext
  apply HasPowers.ext
  intro s
  have hw := f.w (mk ()) s
  simp only [powerCone_leg] at hw
  simp only [powerConeLift]
  have hfac := HasPowers.fac (fun t => d.leg (mk ()) t) s
  simp only [terminalWeightCov_obj, terminalDiagram_obj] at hfac
  rw [hfac]
  exact hw

/-- The power cone is terminal in the category of weighted cones,
making powers weighted limits over the terminal category. -/
def powerIsWeightedLimit (X : C) (S : Type v) :
    IsWeightedLimit (powerCone X S) :=
  IsTerminal.ofUniqueHom
    (fun d => powerConeLift X S d)
    (fun _ => powerConeLift_unique X S _)

end PowerAsWeightedLimit

/-!
## Tensor-Hom Adjunction (Copower-Power Adjunction)

When a category has both copowers and powers, they are adjoint:

  `C(S ·. X, Y) ≅ (S → C(X, Y)) ≅ C(X, Y ^. S)`

This is the "elimination rule for copowers using powers" - morphisms out of a
copower correspond to morphisms into a power.
-/

section TensorHomAdjunction

variable {C : Type u} [Category.{v} C]

/-- The isomorphism `C(S ·. X, Y) ≅ (S → C(X, Y))` from the copower universal
property. Morphisms out of a copower correspond to families of morphisms. -/
def copowerHomEquiv [HasCopowers C] (S : Type v) (X Y : C) :
    (HasCopowers.copower S X ⟶ Y) ≃ (S → (X ⟶ Y)) where
  toFun f s := HasCopowers.inj S X s ≫ f
  invFun := HasCopowers.desc
  left_inv f := by
    apply HasCopowers.ext
    intro s
    rw [HasCopowers.fac]
  right_inv fam := by
    funext s
    simp only
    rw [HasCopowers.fac]

@[simp]
theorem copowerHomEquiv_apply [HasCopowers C] {S : Type v} {X Y : C}
    (f : HasCopowers.copower S X ⟶ Y) (s : S) :
    copowerHomEquiv S X Y f s = HasCopowers.inj S X s ≫ f := rfl

@[simp]
theorem copowerHomEquiv_symm_apply [HasCopowers C] {S : Type v} {X Y : C}
    (fam : S → (X ⟶ Y)) :
    (copowerHomEquiv S X Y).symm fam = HasCopowers.desc fam := rfl

/-- The isomorphism `(S → C(X, Y)) ≅ C(X, Y ^. S)` from the power universal
property. Families of morphisms correspond to morphisms into a power. -/
def powerHomEquiv [HasPowers C] (S : Type v) (X Y : C) :
    (S → (Y ⟶ X)) ≃ (Y ⟶ HasPowers.power X S) where
  toFun := HasPowers.lift
  invFun f s := f ≫ HasPowers.proj X S s
  left_inv fam := by
    funext s
    simp only
    rw [HasPowers.fac]
  right_inv f := by
    apply HasPowers.ext
    intro s
    rw [HasPowers.fac]

@[simp]
theorem powerHomEquiv_apply [HasPowers C] {S : Type v} {X Y : C}
    (fam : S → (Y ⟶ X)) :
    powerHomEquiv S X Y fam = HasPowers.lift fam := rfl

@[simp]
theorem powerHomEquiv_symm_apply [HasPowers C] {S : Type v} {X Y : C}
    (f : Y ⟶ HasPowers.power X S) (s : S) :
    (powerHomEquiv S X Y).symm f s = f ≫ HasPowers.proj X S s := rfl

/-- The full copower-power adjunction: `C(S ·. X, Y) ≅ C(X, Y ^. S)`.
This combines the copower and power universal properties. -/
def copowerPowerEquiv [HasCopowers C] [HasPowers C] (S : Type v) (X Y : C) :
    (HasCopowers.copower S X ⟶ Y) ≃ (X ⟶ HasPowers.power Y S) :=
  (copowerHomEquiv S X Y).trans (powerHomEquiv S Y X)

@[simp]
theorem copowerPowerEquiv_apply [HasCopowers C] [HasPowers C]
    {S : Type v} {X Y : C} (f : HasCopowers.copower S X ⟶ Y) :
    copowerPowerEquiv S X Y f =
      HasPowers.lift (fun s => HasCopowers.inj S X s ≫ f) := rfl

@[simp]
theorem copowerPowerEquiv_symm_apply [HasCopowers C] [HasPowers C]
    {S : Type v} {X Y : C} (f : X ⟶ HasPowers.power Y S) :
    (copowerPowerEquiv S X Y).symm f =
      HasCopowers.desc (fun s => f ≫ HasPowers.proj Y S s) := rfl

/-- The copower functor for a fixed type `S`. Maps `X ↦ S ·. X`.
This is the left adjoint to `powerByTypeFunctor S`. -/
def copowerWithTypeFunctor [HasCopowers C] (S : Type v) : C ⥤ C where
  obj := fun X => HasCopowers.copower S X
  map := fun f => HasCopowers.mapVal f
  map_id := fun _ => HasCopowers.mapVal_id
  map_comp := fun _ _ => HasCopowers.mapVal_comp _ _

@[simp]
theorem copowerWithTypeFunctor_obj [HasCopowers C] (S : Type v) (X : C) :
    (copowerWithTypeFunctor S).obj X = HasCopowers.copower S X := rfl

@[simp]
theorem copowerWithTypeFunctor_map [HasCopowers C] (S : Type v) {X Y : C} (f : X ⟶ Y) :
    (copowerWithTypeFunctor S).map f = HasCopowers.mapVal f := rfl

/-- The power functor for a fixed type `S`. Maps `X ↦ X ^. S`.
This is the right adjoint to `copowerWithTypeFunctor S`. -/
def powerByTypeFunctor [HasPowers C] (S : Type v) : C ⥤ C where
  obj := fun X => HasPowers.power X S
  map := fun f => HasPowers.mapVal f
  map_id := fun _ => HasPowers.mapVal_id
  map_comp := fun _ _ => HasPowers.mapVal_comp _ _

@[simp]
theorem powerByTypeFunctor_obj [HasPowers C] (S : Type v) (X : C) :
    (powerByTypeFunctor S).obj X = HasPowers.power X S := rfl

@[simp]
theorem powerByTypeFunctor_map [HasPowers C] (S : Type v) {X Y : C} (f : X ⟶ Y) :
    (powerByTypeFunctor S).map f = HasPowers.mapVal f := rfl

/-- The copower-power adjunction: `S ·. _ ⊣ _ ^. S`.

This is the categorical form of the tensor-hom adjunction, expressing that
copower with a type is left adjoint to power by that type. -/
def copowerPowerAdjunction [HasCopowers C] [HasPowers C] (S : Type v) :
    copowerWithTypeFunctor (C := C) S ⊣ powerByTypeFunctor S :=
  Adjunction.mkOfHomEquiv {
    homEquiv := fun X Y => copowerPowerEquiv S X Y
    homEquiv_naturality_left_symm := fun {X' X Y} f g => by
      apply HasCopowers.ext
      intro s
      simp only [copowerWithTypeFunctor_map, copowerWithTypeFunctor_obj,
        powerByTypeFunctor_obj, copowerPowerEquiv_symm_apply]
      rw [← Category.assoc, HasCopowers.mapVal_inj, Category.assoc, HasCopowers.fac,
        HasCopowers.fac, Category.assoc]
    homEquiv_naturality_right := fun {X Y Y'} f g => by
      apply HasPowers.ext
      intro s
      simp only [powerByTypeFunctor_map, powerByTypeFunctor_obj,
        copowerWithTypeFunctor_obj, copowerPowerEquiv_apply]
      rw [HasPowers.fac]
      rw [Category.assoc (HasPowers.lift _) (HasPowers.mapVal g) (HasPowers.proj Y' S s)]
      rw [HasPowers.mapVal_proj]
      rw [← Category.assoc (HasPowers.lift _) (HasPowers.proj Y S s) g]
      rw [HasPowers.fac, Category.assoc]
  }

end TensorHomAdjunction

/-!
## Weighted (Co)Limits via Ends/Coends of Powers/Copowers

For categories with powers/copowers and ordinary ends/coends, weighted
(co)limits can be expressed as:

- `{W, F} ≅ ∫_j F(j) ^. W(j)` (weighted limit via end of powers)
- `W * F ≅ ∫^j W(j) ·. F(j)` (weighted colimit via coend of copowers)

This section defines the profunctors whose ends/coends give weighted
(co)limits, and establishes the isomorphisms.
-/

section WeightedViaEnds

open CategoryTheory Limits Opposite

universe u₁ v₁ u₂

variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₁} C]

/-!
### The Copower Profunctor

Given a weight `W : Jᵒᵖ ⥤ Type v` and a diagram `F : J ⥤ C`, the copower
profunctor `copowerProfunctor W F : Jᵒᵖ ⥤ J ⥤ C` has:

- Objects: `(copowerProfunctor W F).obj (op j₁).obj j₂ = W(j₁) ·. F(j₂)`
- On the diagonal: `W(j) ·. F(j)`

The coend of this profunctor gives the weighted colimit `W * F`.
-/

section CopowerProfunctor

variable [HasCopowers C] (W : Jᵒᵖ ⥤ Type v₁) (F : J ⥤ C)

/-- The inner functor of the copower profunctor: for a fixed `j : Jᵒᵖ`,
maps `j' : J` to `W(j) ·. F(j')`.

This is the composition `F ⋙ copowerWithTypeFunctor (W.obj j)`. -/
def copowerProfunctorInner (j : Jᵒᵖ) : J ⥤ C :=
  F ⋙ copowerWithTypeFunctor (W.obj j)

@[simp]
theorem copowerProfunctorInner_obj (j : Jᵒᵖ) (j' : J) :
    (copowerProfunctorInner W F j).obj j' =
      HasCopowers.copower (W.obj j) (F.obj j') := rfl

@[simp]
theorem copowerProfunctorInner_map (j : Jᵒᵖ) {j₁ j₂ : J} (g : j₁ ⟶ j₂) :
    (copowerProfunctorInner W F j).map g = HasCopowers.mapVal (F.map g) := rfl

/-- The copower profunctor `Jᵒᵖ ⥤ J ⥤ C` whose coend gives weighted colimits.

For weight `W : Jᵒᵖ ⥤ Type v` and diagram `F : J ⥤ C`:
- `(copowerProfunctor W F).obj (op j₁).obj j₂ = W(j₁) ·. F(j₂)`
- On the diagonal: `W(j) ·. F(j)` -/
def copowerProfunctor : Jᵒᵖ ⥤ J ⥤ C where
  obj := copowerProfunctorInner W F
  map := fun {j₁ j₂} f => {
    app := fun j' => HasCopowers.mapIdx (W.map f)
    naturality := fun j₁' j₂' g => by
      simp only [copowerProfunctorInner_map]
      rw [← HasCopowers.bimap_eq_mapVal_mapIdx, ← HasCopowers.bimap_eq_mapIdx_mapVal]
  }
  map_id := fun j => by
    ext j'
    simp only [copowerProfunctorInner_obj, W.map_id, NatTrans.id_app]
    exact HasCopowers.mapIdx_id
  map_comp := fun {j₁ j₂ j₃} f g => by
    ext j'
    simp only [copowerProfunctorInner_obj, W.map_comp, NatTrans.comp_app]
    exact HasCopowers.mapIdx_comp (W.map f) (W.map g)

@[simp]
theorem copowerProfunctor_obj_obj (j : Jᵒᵖ) (j' : J) :
    ((copowerProfunctor W F).obj j).obj j' =
      HasCopowers.copower (W.obj j) (F.obj j') := rfl

@[simp]
theorem copowerProfunctor_obj_map (j : Jᵒᵖ) {j₁ j₂ : J} (g : j₁ ⟶ j₂) :
    ((copowerProfunctor W F).obj j).map g = HasCopowers.mapVal (F.map g) := rfl

@[simp]
theorem copowerProfunctor_map_app {j₁ j₂ : Jᵒᵖ} (f : j₁ ⟶ j₂) (j' : J) :
    ((copowerProfunctor W F).map f).app j' = HasCopowers.mapIdx (W.map f) := rfl

end CopowerProfunctor

/-!
### The Power Profunctor

Given a weight `W : J ⥤ Type v` and a diagram `F : J ⥤ C`, the power
profunctor `powerProfunctor W F : Jᵒᵖ ⥤ J ⥤ C` has:

- Objects: `(powerProfunctor W F).obj (op j₁).obj j₂ = F(j₂) ^. W(j₁)`
- On the diagonal: `F(j) ^. W(j)`

The end of this profunctor gives the weighted limit `{W, F}`.
-/

section PowerProfunctor

variable [HasPowers C] (W : J ⥤ Type v₁) (F : J ⥤ C)

/-- The inner functor of the power profunctor: for a fixed `j : Jᵒᵖ`,
maps `j' : J` to `F(j') ^. W(j.unop)`.

This is the composition `F ⋙ powerByTypeFunctor (W.obj j.unop)`. -/
def powerProfunctorInner (j : Jᵒᵖ) : J ⥤ C :=
  F ⋙ powerByTypeFunctor (W.obj j.unop)

@[simp]
theorem powerProfunctorInner_obj (j : Jᵒᵖ) (j' : J) :
    (powerProfunctorInner W F j).obj j' =
      HasPowers.power (F.obj j') (W.obj j.unop) := rfl

@[simp]
theorem powerProfunctorInner_map (j : Jᵒᵖ) {j₁ j₂ : J} (g : j₁ ⟶ j₂) :
    (powerProfunctorInner W F j).map g = HasPowers.mapVal (F.map g) := rfl

/-- The power profunctor `Jᵒᵖ ⥤ J ⥤ C` whose end gives weighted limits.

For weight `W : J ⥤ Type v` and diagram `F : J ⥤ C`:
- `(powerProfunctor W F).obj (op j₁).obj j₂ = F(j₂) ^. W(j₁)`
- On the diagonal: `F(j) ^. W(j)` -/
def powerProfunctor : Jᵒᵖ ⥤ J ⥤ C where
  obj := powerProfunctorInner W F
  map := fun {j₁ j₂} f => {
    app := fun j' => HasPowers.mapIdx (W.map f.unop)
    naturality := fun j₁' j₂' g => by
      simp only [powerProfunctorInner_map]
      rw [← HasPowers.bimap_eq_mapIdx_mapVal, ← HasPowers.bimap_eq_mapVal_mapIdx]
  }
  map_id := fun j => by
    ext j'
    simp only [powerProfunctorInner_obj, unop_id, W.map_id, NatTrans.id_app]
    exact HasPowers.mapIdx_id
  map_comp := fun {j₁ j₂ j₃} f g => by
    ext j'
    simp only [powerProfunctorInner_obj, unop_comp, W.map_comp, NatTrans.comp_app]
    exact HasPowers.mapIdx_comp (W.map g.unop) (W.map f.unop)

@[simp]
theorem powerProfunctor_obj_obj (j : Jᵒᵖ) (j' : J) :
    ((powerProfunctor W F).obj j).obj j' =
      HasPowers.power (F.obj j') (W.obj j.unop) := rfl

@[simp]
theorem powerProfunctor_obj_map (j : Jᵒᵖ) {j₁ j₂ : J} (g : j₁ ⟶ j₂) :
    ((powerProfunctor W F).obj j).map g = HasPowers.mapVal (F.map g) := rfl

@[simp]
theorem powerProfunctor_map_app {j₁ j₂ : Jᵒᵖ} (f : j₁ ⟶ j₂) (j' : J) :
    ((powerProfunctor W F).map f).app j' = HasPowers.mapIdx (W.map f.unop) := rfl

end PowerProfunctor

/-!
### Weighted Cocones as Cocones over the Copower Diagram

The correspondence between weighted cocones and cocones over
`profunctorOnCoTwistedArrow J (copowerProfunctor W F)`. A weighted cocone over
`W` and `F` consists of maps `W(j) → (F(j) ⟶ pt)` natural in `j`. Via the
copower adjunction, this corresponds to maps `W(j) ·. F(j) ⟶ pt` with the
naturality condition of a cocone.

Composing with `cowedgeCoconeEquiv` gives:
`WeightedCocone W F ≌ Cowedge (copowerProfunctor W F)`
-/

section WeightedCoconeCoconeEquiv

variable {J : Type u} [Category.{v} J]
variable {C : Type u} [Category.{v} C] [HasCopowers C]
variable (W : Jᵒᵖ ⥤ Type v) (F : J ⥤ C)

open Limits

/-- The cocone leg at a co-twisted arrow from weighted cocone data.

For a co-twisted arrow `tw : j → j'` in J, the cocone leg is:
`mapIdx (W.map (coTwArr tw).op) ≫ desc (c.leg (coTwCod tw))`

This uses the copower profunctor action to transport from the codomain
diagonal to the full co-twisted arrow. -/
def copowerCoconeιApp (c : WeightedCocone W F) (tw : CoTwistedArrow J) :
    (profunctorOnCoTwistedArrow J (copowerProfunctor W F)).obj tw ⟶ c.pt :=
  HasCopowers.mapIdx (W.map (coTwArr tw).op) ≫
    HasCopowers.desc (c.leg (coTwCod tw))

/-- At identity co-twisted arrows, the cocone leg is just `desc (c.leg j)`. -/
@[simp]
theorem copowerCoconeιApp_at_id (c : WeightedCocone W F) (j : J) :
    copowerCoconeιApp W F c (coTwObjMk (𝟙 j)) =
      HasCopowers.desc (c.leg j) := by
  simp only [copowerCoconeιApp, coTwObjMk_arr, coTwObjMk_cod]
  erw [W.map_id, HasCopowers.mapIdx_id, Category.id_comp]

/-- The cocone legs form a natural transformation. -/
theorem copowerCoconeιApp_naturality (c : WeightedCocone W F)
    {x y : CoTwistedArrow J} (m : x ⟶ y) :
    (profunctorOnCoTwistedArrow J (copowerProfunctor W F)).map m ≫
      copowerCoconeιApp W F c y =
    copowerCoconeιApp W F c x := by
  apply HasCopowers.ext
  intro s
  simp only [copowerCoconeιApp, profunctorOnCoTwistedArrow_map,
    copowerProfunctor_map_app, copowerProfunctor_obj_map]
  -- Use simp_rw to apply copower lemmas with reassociation
  simp_rw [← Category.assoc]
  simp_rw [HasCopowers.mapIdx_inj, HasCopowers.mapVal_inj, HasCopowers.fac]
  -- Goal: ((F.map (coTwCodArr m) ≫ inj ... (W.map (coTwDomArr m).op s)) ≫
  --        mapIdx (W.map (coTwArr y).op)) ≫ desc (c.leg (coTwCod y))
  --       = c.leg (coTwCod x) (W.map (coTwArr x).op s)
  -- Apply the remaining copower lemmas using conv
  conv_lhs =>
    rw [Category.assoc, Category.assoc]
    arg 2
    rw [← Category.assoc, HasCopowers.mapIdx_inj]
    rw [HasCopowers.fac]
  -- Goal: F.map (coTwCodArr m) ≫ c.leg y' (W.map (coTwArr y).op (W.map domArr.op s))
  --       = c.leg x' (W.map (coTwArr x).op s)  where y' = coTwCod y, domArr = coTwDomArr m
  rw [WeightedCocone.naturality c (coTwCodArr m)]
  -- Goal: c.leg x' (W.map codArr.op (W.map (coTwArr y).op (W.map domArr.op s)))
  --       = c.leg x' (W.map (coTwArr x).op s)  where codArr = coTwCodArr m
  -- Show the weight values are equal via co-twisted arrow commutativity
  simp only [← FunctorToTypes.map_comp_apply, ← op_comp, coTwHomComm m]

/-- Convert a weighted cocone to a cocone over the copower profunctor diagram.

Given a weighted cocone with `ι(j) : W(j) → (F(j) ⟶ pt)`, we construct a
cocone with legs at each co-twisted arrow using `HasCopowers.desc` and
`mapIdx`. -/
def weightedCoconeToCopowerCocone (c : WeightedCocone W F) :
    Cocone (profunctorOnCoTwistedArrow J (copowerProfunctor W F)) where
  pt := c.pt
  ι := {
    app := copowerCoconeιApp W F c
    naturality := fun _ _ m => by
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
      exact copowerCoconeιApp_naturality W F c m
  }

/-- Convert a cocone over the copower profunctor diagram to a weighted cocone.

Given a cocone with legs at each co-twisted arrow, we extract a weighted
cocone by restricting to the diagonal (identity co-twisted arrows) and using
the copower injection. -/
def copowerCoconeToWeightedCocone
    (c : Cocone (profunctorOnCoTwistedArrow J (copowerProfunctor W F))) :
    WeightedCocone W F where
  pt := c.pt
  toWeightedCoconeOver := {
    app := fun j s =>
      HasCopowers.inj (W.obj j) (F.obj j.unop) s ≫ c.ι.app (coTwObjMk (𝟙 j.unop))
    naturality := fun {j j'} f => by
      funext s
      simp only [types_comp_apply]
      -- Use two naturality facts via the intermediate coTwObjMk f.unop
      -- h1: mapIdx (W.map f) ≫ c.ι.app (id j') = c.ι.app f.unop
      have h1 : HasCopowers.mapIdx (W.map f) ≫ c.ι.app (coTwObjMk (𝟙 j'.unop)) =
          c.ι.app (coTwObjMk f.unop) := by
        have nat := c.ι.naturality (coTwObjMkToIdentity f.unop)
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
          profunctorOnCoTwistedArrow_map, copowerProfunctor_map_app,
          copowerProfunctor_obj_map, coTwObjMkToIdentity_domArr,
          coTwObjMkToIdentity_codArr, coTwObjMk_dom, coTwObjMk_cod,
          Opposite.op_unop, F.map_id, HasCopowers.mapVal_id] at nat
        -- nat: (mapIdx (W.map f.unop.op) ≫ 𝟙 _) ≫ c.ι.app _ = c.ι.app _
        -- Reassociate: mapIdx _ ≫ (𝟙 _ ≫ c.ι.app _)
        rw [Category.assoc] at nat
        -- Use id_comp: mapIdx _ ≫ c.ι.app _
        erw [Category.id_comp] at nat
        -- Convert f.unop.op to f
        rw [Quiver.Hom.op_unop] at nat
        exact nat
      -- h2: mapVal (F.map f.unop) ≫ c.ι.app (id j) = c.ι.app f.unop
      have h2 : HasCopowers.mapVal (F.map f.unop) ≫
          c.ι.app (coTwObjMk (𝟙 j.unop)) =
          c.ι.app (coTwObjMk f.unop) := by
        have nat := c.ι.naturality (coTwObjMkToIdentityAtDom f.unop)
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
          profunctorOnCoTwistedArrow_map, copowerProfunctor_map_app,
          copowerProfunctor_obj_map, coTwObjMkToIdentityAtDom_domArr,
          coTwObjMkToIdentityAtDom_codArr, coTwObjMk_dom, coTwObjMk_cod,
          Opposite.op_unop] at nat
        -- nat: (mapIdx (W.map (𝟙 j.unop).op) ≫ mapVal _) ≫ c.ι.app _ = c.ι.app _
        -- (𝟙 j.unop).op = 𝟙 j, W.map (𝟙 j) = id, mapIdx id = 𝟙
        erw [op_id, W.map_id, HasCopowers.mapIdx_id, Category.id_comp] at nat
        exact nat
      -- From h1.symm.trans h2:
      -- mapIdx (W.map f) ≫ c.ι.app (id j') = mapVal (F.map f.unop) ≫ c.ι.app (id j)
      calc HasCopowers.inj (W.obj j') (F.obj j'.unop) (W.map f s) ≫
              c.ι.app (coTwObjMk (𝟙 j'.unop))
          = (HasCopowers.inj (W.obj j) (F.obj j'.unop) s ≫
              HasCopowers.mapIdx (W.map f)) ≫
                c.ι.app (coTwObjMk (𝟙 j'.unop)) := by
                rw [HasCopowers.mapIdx_inj]
        _ = HasCopowers.inj (W.obj j) (F.obj j'.unop) s ≫
              (HasCopowers.mapIdx (W.map f) ≫
                c.ι.app (coTwObjMk (𝟙 j'.unop))) := by
                rw [Category.assoc]
        _ = HasCopowers.inj (W.obj j) (F.obj j'.unop) s ≫
              (HasCopowers.mapVal (F.map f.unop) ≫
                c.ι.app (coTwObjMk (𝟙 j.unop))) := by
                rw [h1, ← h2]
        _ = (HasCopowers.inj (W.obj j) (F.obj j'.unop) s ≫
              HasCopowers.mapVal (F.map f.unop)) ≫
                c.ι.app (coTwObjMk (𝟙 j.unop)) := by
                rw [← Category.assoc]
        _ = (F.map f.unop ≫ HasCopowers.inj (W.obj j) (F.obj j.unop) s) ≫
                c.ι.app (coTwObjMk (𝟙 j.unop)) := by
                rw [HasCopowers.mapVal_inj]
        _ = F.map f.unop ≫
              (HasCopowers.inj (W.obj j) (F.obj j.unop) s ≫
                c.ι.app (coTwObjMk (𝟙 j.unop))) := by
                rw [Category.assoc]
        _ = (homToFunctor F c.pt).map f
              (HasCopowers.inj (W.obj j) (F.obj j.unop) s ≫
                c.ι.app (coTwObjMk (𝟙 j.unop))) := rfl
  }

/-- Round-trip from weighted cocone to copower cocone and back yields the
original. -/
theorem copowerCoconeToWeightedCocone_of_weightedCocone (c : WeightedCocone W F) :
    copowerCoconeToWeightedCocone W F (weightedCoconeToCopowerCocone W F c) = c := by
  apply WeightedCocone.ext
  · rfl
  · apply heq_of_eq
    ext j s
    -- First simplify the LHS without unfolding copowerCoconeιApp
    simp only [copowerCoconeToWeightedCocone]
    -- Now we have: inj _ _ s ≫ (weightedCoconeToCopowerCocone W F c).ι.app ...
    -- Unfold the cocone ι to get copowerCoconeιApp
    simp only [weightedCoconeToCopowerCocone]
    -- Now apply the identity simplification
    -- Use erw because op (unop j) = j is only defeq
    rw [copowerCoconeιApp_at_id]
    erw [HasCopowers.fac]
    -- c.leg (unop j) s = c.toWeightedCoconeOver.app j s by definition of leg
    rfl

/-- Round-trip from copower cocone to weighted cocone and back yields the
original. -/
theorem weightedCoconeToCopowerCocone_of_copowerCocone
    (c : Cocone (profunctorOnCoTwistedArrow J (copowerProfunctor W F))) :
    weightedCoconeToCopowerCocone W F (copowerCoconeToWeightedCocone W F c) = c := by
  -- Destruct c and prove equality component-wise
  obtain ⟨pt, ι⟩ := c
  -- The pt is the same by definition (copowerCoconeToWeightedCocone preserves pt)
  -- The ι is the same by construction
  simp only [weightedCoconeToCopowerCocone, copowerCoconeToWeightedCocone]
  -- Prove the cocones are equal by showing ι components match
  congr 1
  -- Need to prove the ι NatTrans are equal
  ext tw
  simp only [copowerCoconeιApp]
  apply HasCopowers.ext
  intro s
  -- Reassociate to expose inj ≫ mapIdx pattern
  rw [← Category.assoc, HasCopowers.mapIdx_inj]
  -- Now we have: (inj _ _ (mapIdx s)) ≫ desc (...) = inj _ _ s ≫ ι.app tw
  -- The desc factors through:
  erw [HasCopowers.fac]
  -- Use naturality of ι: for the morphism coTwToIdentityAtCod tw
  -- which goes from tw to coTwObjMk (𝟙 (coTwCod tw))
  have h := ι.naturality (coTwToIdentityAtCod tw)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
    profunctorOnCoTwistedArrow_map, copowerProfunctor_map_app,
    copowerProfunctor_obj_map, coTwToIdentityAtCod_domArr,
    coTwToIdentityAtCod_codArr] at h
  -- h : mapIdx (W.map (coTwArr tw).op) ≫ mapVal (F.map (𝟙 _)) ≫ ι.app _ = ι.app tw
  simp only [F.map_id, HasCopowers.mapVal_id] at h
  -- h : (mapIdx _ ≫ 𝟙 _) ≫ ι.app _ = ι.app tw
  -- Reassociate to get mapIdx _ ≫ (𝟙 _ ≫ ι.app _)
  rw [Category.assoc] at h
  -- Now use id_comp (use erw because the types are only defeq)
  erw [Category.id_comp] at h
  -- h : mapIdx (W.map (coTwArr tw).op) ≫ ι.app (coTwObjMk (𝟙 (coTwCod tw))) = ι.app tw
  -- The goal is: leg (coTwCod tw) (W.map (coTwArr tw).op s) = inj _ _ s ≫ ι.app tw
  -- First unfold the leg definition
  simp only [WeightedCocone.leg, coTwistedArrowProdEquiv_forget_fst,
    coTwistedArrowProdEquiv_forget_snd]
  -- Now goal is: inj (W.obj (op (coTwCod tw))) _ (W.map (coTwArr tw).op s) ≫ ι.app ...
  --            = inj (W.obj (op (coTwDom tw))) _ s ≫ ι.app tw
  -- Rewrite inj _ _ (W.map _ s) as (inj _ _ s ≫ mapIdx _)
  rw [← HasCopowers.mapIdx_inj (W.map (coTwArr tw).op) s]
  -- Reassociate
  rw [Category.assoc]
  -- Apply h
  rw [h]

/-- Convert a weighted cocone morphism to a copower cocone morphism. -/
def weightedCoconeHomToCopowerCoconeHom {c₁ c₂ : WeightedCocone W F}
    (f : WeightedCocone.Hom c₁ c₂) :
    (weightedCoconeToCopowerCocone W F c₁) ⟶
      (weightedCoconeToCopowerCocone W F c₂) where
  hom := f.hom
  w := fun tw => by
    -- Goal: copowerCoconeιApp c₁ tw ≫ f.hom = copowerCoconeιApp c₂ tw
    -- Expand: (mapIdx _ ≫ desc (c₁.leg _)) ≫ f.hom = mapIdx _ ≫ desc (c₂.leg _)
    simp only [weightedCoconeToCopowerCocone, copowerCoconeιApp]
    -- Reassociate to: mapIdx _ ≫ (desc _ ≫ f.hom) = mapIdx _ ≫ desc _
    rw [Category.assoc]
    -- It suffices to prove: desc (c₁.leg _) ≫ f.hom = desc (c₂.leg _)
    congr 1
    -- Use ext to reduce to showing: inj s ≫ (desc _ ≫ f.hom) = inj s ≫ desc _
    apply HasCopowers.ext
    intro s
    rw [← Category.assoc]
    erw [HasCopowers.fac, HasCopowers.fac]
    exact f.w (coTwCod tw) s

/-- Convert a copower cocone morphism to a weighted cocone morphism. -/
def copowerCoconeHomToWeightedCoconeHom
    {c₁ c₂ : Cocone (profunctorOnCoTwistedArrow J (copowerProfunctor W F))}
    (f : c₁ ⟶ c₂) :
    WeightedCocone.Hom (copowerCoconeToWeightedCocone W F c₁)
      (copowerCoconeToWeightedCocone W F c₂) where
  hom := f.hom
  w := fun j s => by
    simp only [copowerCoconeToWeightedCocone, WeightedCocone.leg]
    rw [Category.assoc]
    congr 1
    exact f.w (coTwObjMk (𝟙 j))

@[simp]
theorem weightedCoconeHomToCopowerCoconeHom_hom {c₁ c₂ : WeightedCocone W F}
    (f : WeightedCocone.Hom c₁ c₂) :
    (weightedCoconeHomToCopowerCoconeHom W F f).hom = f.hom := rfl

@[simp]
theorem copowerCoconeHomToWeightedCoconeHom_hom
    {c₁ c₂ : Cocone (profunctorOnCoTwistedArrow J (copowerProfunctor W F))}
    (f : c₁ ⟶ c₂) :
    (copowerCoconeHomToWeightedCoconeHom W F f).hom = f.hom := rfl

/-- The functor from weighted cocones to copower cocones. -/
def weightedCoconeToCopowerCoconesFunctor :
    WeightedCocone W F ⥤
      Cocone (profunctorOnCoTwistedArrow J (copowerProfunctor W F)) where
  obj := weightedCoconeToCopowerCocone W F
  map := weightedCoconeHomToCopowerCoconeHom W F
  map_id := fun _ => rfl
  map_comp := fun {_ _ _} _ _ => rfl

/-- The functor from copower cocones to weighted cocones. -/
def copowerCoconesToWeightedCoconeFunctor :
    Cocone (profunctorOnCoTwistedArrow J (copowerProfunctor W F)) ⥤
      WeightedCocone W F where
  obj := copowerCoconeToWeightedCocone W F
  map := copowerCoconeHomToWeightedCoconeHom W F
  map_id := fun _ => by
    apply WeightedCocone.Hom.ext
    rfl
  map_comp := fun {_ _ _} _ _ => by
    apply WeightedCocone.Hom.ext
    rfl

/-- The equivalence between weighted cocones and copower cocones.

This relates weighted colimits to coends of copowers via the equivalence
`Cocone (profunctorOnCoTwistedArrow J P) ≌ Cowedge P`. -/
def weightedCoconeCopowerCoconeEquiv :
    WeightedCocone W F ≌
      Cocone (profunctorOnCoTwistedArrow J (copowerProfunctor W F)) where
  functor := weightedCoconeToCopowerCoconesFunctor W F
  inverse := copowerCoconesToWeightedCoconeFunctor W F
  unitIso := NatIso.ofComponents
    (fun c => eqToIso
      (copowerCoconeToWeightedCocone_of_weightedCocone W F c).symm)
    (fun {c₁ c₂} f => by
      apply WeightedCocone.Hom.ext
      simp only [weightedCoconeToCopowerCoconesFunctor,
        copowerCoconesToWeightedCoconeFunctor, Functor.id_obj, Functor.comp_obj,
        Functor.id_map, Functor.comp_map, eqToIso.hom,
        weightedCoconeHomToCopowerCoconeHom_hom, copowerCoconeHomToWeightedCoconeHom_hom,
        WeightedCocone.category_comp_hom, WeightedCocone.eqToHom_hom,
        copowerCoconeToWeightedCocone, weightedCoconeToCopowerCocone,
        eqToHom_refl, Category.id_comp, Category.comp_id])
  counitIso := NatIso.ofComponents
    (fun c => eqToIso
      (weightedCoconeToCopowerCocone_of_copowerCocone W F c))
    (fun {c₁ c₂} f => by
      ext
      simp only [copowerCoconesToWeightedCoconeFunctor,
        weightedCoconeToCopowerCoconesFunctor, Functor.comp_obj, Functor.id_obj,
        Functor.comp_map, Functor.id_map, eqToIso.hom,
        copowerCoconeHomToWeightedCoconeHom_hom, weightedCoconeHomToCopowerCoconeHom_hom,
        Cocone.category_comp_hom, Cocone.eqToHom_hom, copowerCoconeToWeightedCocone,
        weightedCoconeToCopowerCocone, eqToHom_refl, Category.id_comp, Category.comp_id])
  functor_unitIso_comp := fun c => by
    ext
    simp only [weightedCoconeToCopowerCoconesFunctor,
      copowerCoconesToWeightedCoconeFunctor, Functor.comp_obj, Functor.id_obj,
      NatIso.ofComponents_hom_app, eqToIso.hom,
      eqToHom_map, eqToHom_trans, eqToHom_refl]

/-- The equivalence between weighted cocones and cowedges over the copower
profunctor.

This is the categorical formulation of the fact that weighted colimits can be
computed as coends of copowers: `W * F ≅ ∫^j W(j) ·. F(j)`. -/
def weightedCoconeCowedgeEquiv :
    WeightedCocone W F ≌ Cowedge (copowerProfunctor W F) :=
  (weightedCoconeCopowerCoconeEquiv W F).trans (cowedgeCoconeEquiv _).symm

/-- `HasInitial (WeightedCocone W F)` from `HasInitial (Cowedge _)` via the
equivalence between them.

Uses `hasColimitsOfShape_of_equivalence` to transfer `HasInitial` across
the categorical equivalence. -/
def hasInitialWeightedCoconeOfHasInitialCopowerCowedge
    [HasInitial (Cowedge (copowerProfunctor W F))] :
    HasInitial (WeightedCocone W F) :=
  Adjunction.hasColimitsOfShape_of_equivalence
    (weightedCoconeCowedgeEquiv W F).functor

/-- `HasInitial (Cowedge _)` from `HasInitial (WeightedCocone W F)` via the
equivalence between them. -/
def hasInitialCopowerCowedgeOfHasInitialWeightedCocone
    [HasInitial (WeightedCocone W F)] :
    HasInitial (Cowedge (copowerProfunctor W F)) :=
  Adjunction.hasColimitsOfShape_of_equivalence
    (weightedCoconeCowedgeEquiv W F).inverse

/-- Transfer `IsWeightedColimit` to `IsInitial` on cowedges over the copower
profunctor.

Given a weighted cocone that is initial (i.e., a weighted colimit), its image
under the equivalence to cowedges is also initial. -/
def isInitialCopowerCowedgeOfIsWeightedColimit {c : WeightedCocone W F}
    (hc : IsWeightedColimit c) :
    IsInitial ((weightedCoconeCowedgeEquiv W F).functor.obj c) :=
  isInitialOfEquivFunctor (weightedCoconeCowedgeEquiv W F) hc

/-- Transfer `IsInitial` on cowedges over the copower profunctor to
`IsWeightedColimit`.

Given a cowedge that is initial (i.e., a coend), its image under the inverse
equivalence is a weighted colimit. -/
def isWeightedColimitOfIsInitialCopowerCowedge
    {c : Cowedge (copowerProfunctor W F)} (hc : IsInitial c) :
    IsWeightedColimit ((weightedCoconeCowedgeEquiv W F).inverse.obj c) :=
  isInitialOfEquivFunctor (weightedCoconeCowedgeEquiv W F).symm hc

/-- Isomorphism between a weighted colimit apex and a coend of copowers apex.

Given a weighted cocone `c` that is a weighted colimit and a cowedge `w` over
the copower profunctor that is initial (a coend), their apices are isomorphic.
This formalizes the formula `W * F ≅ ∫^j W(j) ·. F(j)`. -/
def weightedColimitIsoCopowerCoend {c : WeightedCocone W F}
    (hc : IsWeightedColimit c)
    {w : Cowedge (copowerProfunctor W F)} (hw : IsInitial w) :
    c.pt ≅ w.pt :=
  isInitialCowedgeIso (copowerProfunctor W F)
    (isInitialCopowerCowedgeOfIsWeightedColimit W F hc) hw

end WeightedCoconeCoconeEquiv

/-!
### Weighted Cones as Cones over Power Profunctor

The dual construction: weighted cones correspond to cones over the twisted
arrow diagram of the power profunctor.

Given a weight `W : Jᵒᵖ ⥤ Type v` and diagram `F : J ⥤ C`, the power
profunctor `powerProfunctor W F` has:
- Diagonal: `F(j) ^. W(j)` (power of F(j) by W(j))
- Off-diagonal: mediated by power's functorial action

A weighted cone with apex `pt` and projections `π : (j : Jᵒᵖ) → W(j) →
(pt ⟶ F(j))` corresponds to a cone over the twisted arrow diagram with legs
`pt ⟶ F(twDom tw) ^. W(op (twDom tw))` for each twisted arrow `tw`.

This establishes the equivalence:
`WeightedCone W F ≌ Wedge (powerProfunctor W F)`
-/

section WeightedConeConeEquiv

variable {J : Type u} [Category.{v} J]
variable {C : Type u} [Category.{v} C] [HasPowers C]
variable (W : J ⥤ Type v) (F : J ⥤ C)

open Limits

/-- The cone leg at a twisted arrow from weighted cone data.

For a twisted arrow `tw : j' → j` in J (with `twArr tw : twCod tw ⟶ twDom tw`),
the cone leg is:
`lift (c.leg (twDom tw)) ≫ mapVal (F.map (twArr tw))`

This uses the power profunctor action to transport from the domain
diagonal to the full twisted arrow. -/
def powerConeπApp (c : WeightedCone W F) (tw : TwistedArrow J) :
    c.pt ⟶ (profunctorOnTwistedArrow J (powerProfunctor W F)).obj tw :=
  HasPowers.lift (c.leg (twDom tw)) ≫ HasPowers.mapVal (F.map (twArr tw))

/-- At identity twisted arrows, the cone leg is just `lift (c.leg j)`. -/
@[simp]
theorem powerConeπApp_at_id (c : WeightedCone W F) (j : J) :
    powerConeπApp W F c (twObjMk (𝟙 j)) =
      HasPowers.lift (c.leg j) := by
  simp only [powerConeπApp, twObjMk_arr, twObjMk_dom]
  erw [F.map_id, HasPowers.mapVal_id, Category.comp_id]

/-- The cone legs form a natural transformation.

For cones, naturality says: `π.app y = π.app x ≫ D.map m` for `m : x ⟶ y`. -/
theorem powerConeπApp_naturality (c : WeightedCone W F)
    {x y : TwistedArrow J} (m : x ⟶ y) :
    powerConeπApp W F c y =
    powerConeπApp W F c x ≫
      (profunctorOnTwistedArrow J (powerProfunctor W F)).map m := by
  apply HasPowers.ext
  intro s
  simp only [powerConeπApp, profunctorOnTwistedArrow_map,
    powerProfunctor_map_app, powerProfunctor_obj_map, Category.assoc]
  -- LHS: lift (leg (twDom y)) ≫ mapVal (F.map (twArr y)) ≫ proj _ _ s
  -- RHS: lift (leg (twDom x)) ≫ mapVal ≫ mapIdx ≫ mapVal ≫ proj _ _ s
  -- The twistedArrowForget projections are definitionally equal to twDom/twCod
  -- Convert s to have the canonical type for easier pattern matching
  let s' : W.obj (twDom y) := s
  change HasPowers.lift (c.leg (twDom y)) ≫
       HasPowers.mapVal (F.map (twArr y)) ≫
       HasPowers.proj (F.obj (twCod y)) (W.obj (twDom y)) s' =
    HasPowers.lift (c.leg (twDom x)) ≫
      HasPowers.mapVal (F.map (twArr x)) ≫
        HasPowers.mapIdx (W.map (twDomArr m)) ≫
          HasPowers.mapVal (F.map (twCodArr m)) ≫
            HasPowers.proj (F.obj (twCod y)) (W.obj (twDom y)) s'
  -- RHS: Apply power lemmas working from inside out using conv_rhs
  -- Step 1: mapVal (twCodArr m) ≫ proj → proj ≫ F.map (twCodArr m)
  conv_rhs => rw [HasPowers.mapVal_proj]
  -- RHS: lift ≫ mapVal ≫ mapIdx ≫ (proj ≫ F.map)
  -- Step 2: Need to left-assoc (mapIdx ≫ proj) for mapIdx_proj
  conv_rhs => rw [← Category.assoc (f := HasPowers.mapIdx _), HasPowers.mapIdx_proj]
  -- RHS: lift ≫ mapVal ≫ proj (W.map _ s') ≫ F.map
  -- Step 3: Need to left-assoc to get (mapVal ≫ proj), then apply mapVal_proj
  conv_rhs =>
    rw [← Category.assoc (f := HasPowers.mapVal _), HasPowers.mapVal_proj]
  -- RHS: lift ≫ ((proj ≫ F.map (twArr x)) ≫ F.map (twCodArr m))
  -- Step 4: Flatten, then get (lift ≫ proj) adjacent, then apply fac
  conv_rhs =>
    rw [Category.assoc (f := HasPowers.proj _ _ _)]  -- flatten inner
    rw [← Category.assoc (f := HasPowers.lift _)]   -- left-assoc lift ≫ proj
    rw [HasPowers.fac]                              -- apply fac
  -- RHS: leg (twDom x) (W.map _ s') ≫ F.map (twArr x) ≫ F.map (twCodArr m)
  -- LHS: Apply power lemmas
  conv_lhs => rw [HasPowers.mapVal_proj, ← Category.assoc, HasPowers.fac]
  -- LHS: leg (twDom y) s' ≫ F.map (twArr y)
  -- RHS: leg (twDom x) (W.map (twDomArr m) s') ≫ F.map (twArr x) ≫ F.map (twCodArr m)
  -- Now prove LHS = RHS using twisted arrow commutativity and naturality
  -- RHS: leg (twDom x) (W.map (twDomArr m) s') ≫ F.map (twArr x) ≫ F.map (twCodArr m)
  -- Use naturality: leg (twDom x) (W.map (twDomArr m) s') = leg (twDom y) s' ≫ F.map (twDomArr m)
  -- (since twDomArr m : twDom y ⟶ twDom x in the twisted arrow category)
  rw [← WeightedCone.naturality c (twDomArr m)]
  -- RHS: (leg (twDom y) s' ≫ F.map (twDomArr m)) ≫ F.map (twArr x) ≫ F.map (twCodArr m)
  -- Reassociate and combine F.maps
  rw [Category.assoc, ← F.map_comp, ← F.map_comp]
  -- RHS: leg (twDom y) s' ≫ F.map (twDomArr m ≫ twArr x ≫ twCodArr m)
  -- Use twisted arrow commutativity
  rw [twHomComm m]

/-- Convert a weighted cone to a cone over the power profunctor diagram.

Given a weighted cone with `π(j) : W(j) → (pt ⟶ F(j))`, we construct a
cone with legs at each twisted arrow using `HasPowers.lift` and
`mapVal`. -/
def weightedConeToPowerCone (c : WeightedCone W F) :
    Cone (profunctorOnTwistedArrow J (powerProfunctor W F)) where
  pt := c.pt
  π := {
    app := powerConeπApp W F c
    naturality := fun _ _ m => by
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
      exact powerConeπApp_naturality W F c m
  }

/-- Convert a cone over the power profunctor diagram to a weighted cone.

Given a cone with legs at each twisted arrow, we extract a weighted
cone by restricting to the diagonal (identity twisted arrows) and using
the power projection. -/
def powerConeToWeightedCone
    (c : Cone (profunctorOnTwistedArrow J (powerProfunctor W F))) :
    WeightedCone W F where
  pt := c.pt
  toWeightedConeUnder := {
    app := fun j s =>
      c.π.app (twObjMk (𝟙 j)) ≫ HasPowers.proj (F.obj j) (W.obj j) s
    naturality := fun {j j'} f => by
      funext s
      simp only [types_comp_apply]
      -- Goal: π(id_j') ≫ proj (W.map f s) = π(id_j) ≫ proj s ≫ F.map f
      -- Use cone naturality at two twisted arrow morphisms
      have h1 : c.π.app (twObjMk (𝟙 j)) ≫ HasPowers.mapVal (F.map f) =
          c.π.app (twObjMk f) := by
        have nat := c.π.naturality (twFromIdentityAtDom (twObjMk f))
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
          profunctorOnTwistedArrow_map, powerProfunctor_map_app,
          powerProfunctor_obj_map, twFromIdentityAtDom_domArr,
          twFromIdentityAtDom_codArr, twObjMk_dom, twObjMk_cod,
          twObjMk_arr] at nat
        erw [W.map_id, HasPowers.mapIdx_id, Category.id_comp] at nat
        exact nat.symm
      have h2 : c.π.app (twObjMk (𝟙 j')) ≫ HasPowers.mapIdx (W.map f) =
          c.π.app (twObjMk f) := by
        have nat := c.π.naturality (twObjMkFromIdentityAtCod f)
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
          profunctorOnTwistedArrow_map, powerProfunctor_map_app,
          powerProfunctor_obj_map, twObjMkFromIdentityAtCod_domArr,
          twObjMkFromIdentityAtCod_codArr, twObjMk_dom, twObjMk_cod] at nat
        erw [F.map_id, HasPowers.mapVal_id, Category.comp_id] at nat
        exact nat.symm
      -- Use calc chain analogous to copowerCoconeToWeightedCocone
      calc c.π.app (twObjMk (𝟙 j')) ≫
            HasPowers.proj (F.obj j') (W.obj j') (W.map f s)
        _ = c.π.app (twObjMk (𝟙 j')) ≫
            (HasPowers.mapIdx (W.map f) ≫
              HasPowers.proj (F.obj j') (W.obj j) s) := by
              rw [← HasPowers.mapIdx_proj]
        _ = (c.π.app (twObjMk (𝟙 j')) ≫ HasPowers.mapIdx (W.map f)) ≫
              HasPowers.proj (F.obj j') (W.obj j) s := by
              rw [← Category.assoc]
        _ = c.π.app (twObjMk f) ≫
              HasPowers.proj (F.obj j') (W.obj j) s := by
              rw [h2]
        _ = (c.π.app (twObjMk (𝟙 j)) ≫ HasPowers.mapVal (F.map f)) ≫
              HasPowers.proj (F.obj j') (W.obj j) s := by
              rw [← h1]
        _ = c.π.app (twObjMk (𝟙 j)) ≫
              (HasPowers.mapVal (F.map f) ≫
                HasPowers.proj (F.obj j') (W.obj j) s) := by
              rw [Category.assoc]
        _ = c.π.app (twObjMk (𝟙 j)) ≫
              (HasPowers.proj (F.obj j) (W.obj j) s ≫ F.map f) := by
              conv_lhs => rw [HasPowers.mapVal_proj (F.map f) s]
        _ = (c.π.app (twObjMk (𝟙 j)) ≫
              HasPowers.proj (F.obj j) (W.obj j) s) ≫ F.map f := by
              rw [← Category.assoc]
        _ = (homFromFunctor F c.pt).map f
              (c.π.app (twObjMk (𝟙 j)) ≫
                HasPowers.proj (F.obj j) (W.obj j) s) := rfl
  }

/-- Round-trip from weighted cone to power cone and back yields the original. -/
theorem powerConeToWeightedCone_of_weightedCone (c : WeightedCone W F) :
    powerConeToWeightedCone W F (weightedConeToPowerCone W F c) = c := by
  apply WeightedCone.ext
  · rfl
  · apply heq_of_eq
    ext j s
    simp only [powerConeToWeightedCone]
    simp only [weightedConeToPowerCone]
    rw [powerConeπApp_at_id]
    erw [HasPowers.fac]
    rfl

/-- Round-trip from power cone to weighted cone and back yields the original. -/
theorem weightedConeToPowerCone_of_powerCone
    (c : Cone (profunctorOnTwistedArrow J (powerProfunctor W F))) :
    weightedConeToPowerCone W F (powerConeToWeightedCone W F c) = c := by
  obtain ⟨pt, π⟩ := c
  simp only [weightedConeToPowerCone, powerConeToWeightedCone]
  congr 1
  ext tw
  simp only [powerConeπApp]
  apply HasPowers.ext
  intro s
  simp only [Category.assoc]
  erw [HasPowers.mapVal_proj (F.map (twArr tw)) s]
  rw [← Category.assoc]
  erw [HasPowers.fac]
  simp only [WeightedCone.leg]
  rw [Category.assoc]
  erw [← HasPowers.mapVal_proj (F.map (twArr tw)) s]
  have h := π.naturality (twFromIdentityAtDom tw)
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
    profunctorOnTwistedArrow_map, powerProfunctor_map_app,
    powerProfunctor_obj_map, twFromIdentityAtDom_domArr,
    twFromIdentityAtDom_codArr] at h
  erw [W.map_id, HasPowers.mapIdx_id, Category.id_comp] at h
  rw [← Category.assoc, ← h]
  rfl

/-- Convert a weighted cone morphism to a power cone morphism. -/
def weightedConeHomToPowerConeHom {c₁ c₂ : WeightedCone W F}
    (f : WeightedCone.Hom c₁ c₂) :
    (weightedConeToPowerCone W F c₁) ⟶ (weightedConeToPowerCone W F c₂) where
  hom := f.hom
  w := fun tw => by
    simp only [weightedConeToPowerCone, powerConeπApp]
    apply HasPowers.ext
    intro s
    simp only [Category.assoc]
    erw [HasPowers.mapVal_proj (F.map (twArr tw)) s]
    conv_lhs =>
      arg 2
      rw [← Category.assoc]
    conv_rhs => rw [← Category.assoc]
    erw [HasPowers.fac, HasPowers.fac]
    rw [← Category.assoc]
    congr 1
    exact f.w (twDom tw) s

/-- Convert a power cone morphism to a weighted cone morphism. -/
def powerConeHomToWeightedConeHom
    {c₁ c₂ : Cone (profunctorOnTwistedArrow J (powerProfunctor W F))}
    (f : c₁ ⟶ c₂) :
    WeightedCone.Hom (powerConeToWeightedCone W F c₁)
      (powerConeToWeightedCone W F c₂) where
  hom := f.hom
  w := fun j s => by
    simp only [powerConeToWeightedCone, WeightedCone.leg]
    rw [← Category.assoc]
    congr 1
    exact f.w (twObjMk (𝟙 j))

@[simp]
theorem weightedConeHomToPowerConeHom_hom {c₁ c₂ : WeightedCone W F}
    (f : WeightedCone.Hom c₁ c₂) :
    (weightedConeHomToPowerConeHom W F f).hom = f.hom := rfl

@[simp]
theorem powerConeHomToWeightedConeHom_hom
    {c₁ c₂ : Cone (profunctorOnTwistedArrow J (powerProfunctor W F))}
    (f : c₁ ⟶ c₂) :
    (powerConeHomToWeightedConeHom W F f).hom = f.hom := rfl

/-- The functor from weighted cones to power cones. -/
def weightedConeToPowerConesFunctor :
    WeightedCone W F ⥤
      Cone (profunctorOnTwistedArrow J (powerProfunctor W F)) where
  obj := weightedConeToPowerCone W F
  map := weightedConeHomToPowerConeHom W F
  map_id := fun _ => rfl
  map_comp := fun {_ _ _} _ _ => rfl

/-- The functor from power cones to weighted cones. -/
def powerConesToWeightedConeFunctor :
    Cone (profunctorOnTwistedArrow J (powerProfunctor W F)) ⥤
      WeightedCone W F where
  obj := powerConeToWeightedCone W F
  map := powerConeHomToWeightedConeHom W F
  map_id := fun _ => by
    apply WeightedCone.Hom.ext
    rfl
  map_comp := fun {_ _ _} _ _ => by
    apply WeightedCone.Hom.ext
    rfl

/-- The equivalence between weighted cones and power cones.

This relates weighted limits to ends of powers via the equivalence
`Cone (profunctorOnTwistedArrow J P) ≌ Wedge P`. -/
def weightedConePowerConeEquiv :
    WeightedCone W F ≌
      Cone (profunctorOnTwistedArrow J (powerProfunctor W F)) where
  functor := weightedConeToPowerConesFunctor W F
  inverse := powerConesToWeightedConeFunctor W F
  unitIso := NatIso.ofComponents
    (fun c => eqToIso
      (powerConeToWeightedCone_of_weightedCone W F c).symm)
    (fun {c₁ c₂} f => by
      apply WeightedCone.Hom.ext
      simp only [weightedConeToPowerConesFunctor,
        powerConesToWeightedConeFunctor, Functor.id_obj, Functor.comp_obj,
        Functor.id_map, Functor.comp_map, eqToIso.hom,
        weightedConeHomToPowerConeHom_hom, powerConeHomToWeightedConeHom_hom,
        WeightedCone.category_comp_hom, WeightedCone.eqToHom_hom,
        powerConeToWeightedCone, weightedConeToPowerCone,
        eqToHom_refl, Category.id_comp, Category.comp_id])
  counitIso := NatIso.ofComponents
    (fun c => eqToIso
      (weightedConeToPowerCone_of_powerCone W F c))
    (fun {c₁ c₂} f => by
      ext
      simp only [powerConesToWeightedConeFunctor,
        weightedConeToPowerConesFunctor, Functor.comp_obj, Functor.id_obj,
        Functor.comp_map, Functor.id_map, eqToIso.hom,
        powerConeHomToWeightedConeHom_hom, weightedConeHomToPowerConeHom_hom,
        Cone.category_comp_hom, Cone.eqToHom_hom, powerConeToWeightedCone,
        weightedConeToPowerCone, eqToHom_refl, Category.id_comp, Category.comp_id])
  functor_unitIso_comp := fun c => by
    ext
    simp only [weightedConeToPowerConesFunctor,
      powerConesToWeightedConeFunctor, Functor.comp_obj, Functor.id_obj,
      NatIso.ofComponents_hom_app, eqToIso.hom,
      eqToHom_map, eqToHom_trans, eqToHom_refl]

/-- The equivalence between weighted cones and wedges over the power profunctor.

This is the categorical formulation of the fact that weighted limits can be
computed as ends of powers: `{W, F} ≅ ∫_j F(j) ^. W(j)`. -/
def weightedConeWedgeEquiv :
    WeightedCone W F ≌ Wedge (powerProfunctor W F) :=
  (weightedConePowerConeEquiv W F).trans (wedgeConeEquiv (powerProfunctor W F)).symm

/-- `HasTerminal (WeightedCone W F)` from `HasTerminal (Wedge _)` via the
equivalence between them.

Uses `hasLimitsOfShape_of_equivalence` to transfer `HasTerminal` across
the categorical equivalence. -/
def hasTerminalWeightedConeOfHasTerminalPowerWedge
    [HasTerminal (Wedge (powerProfunctor W F))] :
    HasTerminal (WeightedCone W F) :=
  Adjunction.hasLimitsOfShape_of_equivalence
    (weightedConeWedgeEquiv W F).functor

/-- `HasTerminal (Wedge _)` from `HasTerminal (WeightedCone W F)` via the
equivalence between them. -/
def hasTerminalPowerWedgeOfHasTerminalWeightedCone
    [HasTerminal (WeightedCone W F)] :
    HasTerminal (Wedge (powerProfunctor W F)) :=
  Adjunction.hasLimitsOfShape_of_equivalence
    (weightedConeWedgeEquiv W F).inverse

/-- Transfer `IsWeightedLimit` to `IsTerminal` on wedges over the power
profunctor.

Given a weighted cone that is terminal (i.e., a weighted limit), its image
under the equivalence to wedges is also terminal. -/
def isTerminalPowerWedgeOfIsWeightedLimit {c : WeightedCone W F}
    (hc : IsWeightedLimit c) :
    IsTerminal ((weightedConeWedgeEquiv W F).functor.obj c) :=
  isTerminalOfEquivFunctor (weightedConeWedgeEquiv W F) hc

/-- Transfer `IsTerminal` on wedges over the power profunctor to
`IsWeightedLimit`.

Given a wedge that is terminal (i.e., an end), its image under the inverse
equivalence is a weighted limit. -/
def isWeightedLimitOfIsTerminalPowerWedge
    {c : Wedge (powerProfunctor W F)} (hc : IsTerminal c) :
    IsWeightedLimit ((weightedConeWedgeEquiv W F).inverse.obj c) :=
  isTerminalOfEquivFunctor (weightedConeWedgeEquiv W F).symm hc

/-- Isomorphism between a weighted limit apex and an end of powers apex.

Given a weighted cone `c` that is a weighted limit and a wedge `w` over
the power profunctor that is terminal (an end), their apices are isomorphic.
This formalizes the formula `{W, F} ≅ ∫_j F(j) ^. W(j)`. -/
def weightedLimitIsoPowerEnd {c : WeightedCone W F}
    (hc : IsWeightedLimit c)
    {w : Wedge (powerProfunctor W F)} (hw : IsTerminal w) :
    c.pt ≅ w.pt :=
  isTerminalWedgeIso (powerProfunctor W F)
    (isTerminalPowerWedgeOfIsWeightedLimit W F hc) hw

end WeightedConeConeEquiv

/-!
### Profunctor Weights: Copower and Power Profunctors

For weighted cowedges/wedges with profunctor weights `W : Cᵒᵖ ⥤ C ⥤ Type v` and
target profunctor `P : Cᵒᵖ ⥤ C ⥤ D`, we define composed profunctors:

- `copowerWeightedProfunctor W P : Cᵒᵖ ⥤ C ⥤ D` with
  `(copowerWeightedProfunctor W P).obj (op A).obj B = W(A,B) ·. P(A,B)`
- `powerWeightedProfunctor W P : Cᵒᵖ ⥤ C ⥤ D` with
  `(powerWeightedProfunctor W P).obj (op A).obj B = P(A,B) ^. W(A,B)`

These establish:
- `WeightedCowedge W P ≌ Cowedge (copowerWeightedProfunctor W P)`
- `WeightedWedge W P ≌ Wedge (powerWeightedProfunctor W P)`

On the diagonal, these give `W(A,A) ·. P(A,A)` and `P(A,A) ^. W(A,A)`, so:
- Weighted coend = coend of copowers: `∫^_W P ≅ ∫^A W(A,A) ·. P(A,A)`
- Weighted end = end of powers: `∫_W P ≅ ∫_A P(A,A) ^. W(A,A)`
-/

section ProfunctorWeights

variable {C : Type u} [Category.{v} C]
variable {D : Type u} [Category.{v} D]

section CopowerWeightedProfunctor

variable [HasCopowers D]
variable (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D)

/-- The inner functor of the copower weighted profunctor: for a fixed `A : Cᵒᵖ`,
maps `B : C` to `W(A,B) ·. P(A,B)`.

This composes `W.obj A` and `P.obj A` pointwise via copower. -/
def copowerWeightedProfunctorInner (A : Cᵒᵖ) : C ⥤ D where
  obj B := HasCopowers.copower ((W.obj A).obj B) ((P.obj A).obj B)
  map {B₁ B₂} g :=
    HasCopowers.bimap ((W.obj A).map g) ((P.obj A).map g)
  map_id B := by
    simp only [Functor.map_id]
    exact HasCopowers.bimap_id
  map_comp {B₁ B₂ B₃} g h := by
    simp only [Functor.map_comp, types_comp, HasCopowers.bimap_comp]

@[simp]
theorem copowerWeightedProfunctorInner_obj (A : Cᵒᵖ) (B : C) :
    (copowerWeightedProfunctorInner W P A).obj B =
      HasCopowers.copower ((W.obj A).obj B) ((P.obj A).obj B) := rfl

@[simp]
theorem copowerWeightedProfunctorInner_map (A : Cᵒᵖ) {B₁ B₂ : C} (g : B₁ ⟶ B₂) :
    (copowerWeightedProfunctorInner W P A).map g =
      HasCopowers.bimap ((W.obj A).map g) ((P.obj A).map g) := rfl

/-- The copower weighted profunctor `Cᵒᵖ ⥤ C ⥤ D` whose coend gives weighted
coends.

For weight profunctor `W : Cᵒᵖ ⥤ C ⥤ Type v` and target profunctor
`P : Cᵒᵖ ⥤ C ⥤ D`:
- `(copowerWeightedProfunctor W P).obj (op A).obj B = W(A,B) ·. P(A,B)`
- On the diagonal: `W(A,A) ·. P(A,A)` -/
def copowerWeightedProfunctor : Cᵒᵖ ⥤ C ⥤ D where
  obj := copowerWeightedProfunctorInner W P
  map {A₁ A₂} f := {
    app := fun B => HasCopowers.bimap ((W.map f).app B) ((P.map f).app B)
    naturality := fun B₁ B₂ g => by
      simp only [copowerWeightedProfunctorInner_map]
      rw [← HasCopowers.bimap_comp, ← HasCopowers.bimap_comp]
      congr 1
      · simp only [← types_comp]
        exact (W.map f).naturality g
      · exact (P.map f).naturality g
  }
  map_id A := by
    ext B
    simp only [copowerWeightedProfunctorInner_obj, NatTrans.id_app]
    erw [W.map_id, P.map_id]
    simp only [NatTrans.id_app]
    exact HasCopowers.bimap_id
  map_comp {A₁ A₂ A₃} f g := by
    ext B
    simp only [copowerWeightedProfunctorInner_obj, NatTrans.comp_app]
    rw [W.map_comp, P.map_comp, NatTrans.comp_app, NatTrans.comp_app]
    exact HasCopowers.bimap_comp _ _ _ _

@[simp]
theorem copowerWeightedProfunctor_obj (A : Cᵒᵖ) :
    (copowerWeightedProfunctor W P).obj A = copowerWeightedProfunctorInner W P A :=
  rfl

@[simp]
theorem copowerWeightedProfunctor_obj_obj (A : Cᵒᵖ) (B : C) :
    ((copowerWeightedProfunctor W P).obj A).obj B =
      HasCopowers.copower ((W.obj A).obj B) ((P.obj A).obj B) := rfl

@[simp]
theorem copowerWeightedProfunctor_map_app {A₁ A₂ : Cᵒᵖ} (f : A₁ ⟶ A₂) (B : C) :
    ((copowerWeightedProfunctor W P).map f).app B =
      HasCopowers.bimap ((W.map f).app B) ((P.map f).app B) := rfl

end CopowerWeightedProfunctor

section PowerWeightedProfunctor

variable [HasPowers D]
variable (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D)

/-- The inner functor of the power weighted profunctor: for a fixed `A : Cᵒᵖ`,
maps `B : C` to `P(A, B) ^. W(A.unop, op B)`. -/
def powerWeightedProfunctorInner (A : Cᵒᵖ) : C ⥤ D where
  obj B := HasPowers.power ((P.obj A).obj B) ((W.flip.obj A.unop).obj (op B))
  map {B₁ B₂} g :=
    HasPowers.bimap ((W.flip.obj A.unop).map g.op) ((P.obj A).map g)
  map_id B := by
    simp only [Functor.map_id, op_id]
    exact HasPowers.bimap_id
  map_comp {B₁ B₂ B₃} g h := by
    simp only [Functor.map_comp, op_comp]
    exact HasPowers.bimap_comp _ _ _ _

@[simp]
theorem powerWeightedProfunctorInner_obj (A : Cᵒᵖ) (B : C) :
    (powerWeightedProfunctorInner W P A).obj B =
      HasPowers.power ((P.obj A).obj B) ((W.flip.obj A.unop).obj (op B)) := rfl

@[simp]
theorem powerWeightedProfunctorInner_map (A : Cᵒᵖ) {B₁ B₂ : C} (g : B₁ ⟶ B₂) :
    (powerWeightedProfunctorInner W P A).map g =
      HasPowers.bimap ((W.flip.obj A.unop).map g.op) ((P.obj A).map g) := rfl

/-- The power weighted profunctor `Cᵒᵖ ⥤ C ⥤ D` whose end gives weighted ends
with profunctor weights.

For weight profunctor `W : Cᵒᵖ ⥤ C ⥤ Type v` and target profunctor
`P : Cᵒᵖ ⥤ C ⥤ D`:
- `(powerWeightedProfunctor W P).obj (op A).obj B = P(A,B) ^. W(A, op B)`
- On the diagonal: `P(A,A) ^. W(A, op A)` -/
def powerWeightedProfunctor : Cᵒᵖ ⥤ C ⥤ D where
  obj := powerWeightedProfunctorInner W P
  map {A₁ A₂} f := {
    app := fun B => HasPowers.bimap ((W.flip.map f.unop).app (op B)) ((P.map f).app B)
    naturality := fun B₁ B₂ g => by
      simp only [powerWeightedProfunctorInner_map]
      rw [← HasPowers.bimap_comp, ← HasPowers.bimap_comp]
      congr 1
      · simp only [← types_comp]
        exact ((W.flip.map f.unop).naturality g.op).symm
      · exact (P.map f).naturality g
  }
  map_id A := by
    ext B
    simp only [powerWeightedProfunctorInner_obj, NatTrans.id_app, unop_id]
    erw [W.flip.map_id, P.map_id]
    simp only [NatTrans.id_app]
    exact HasPowers.bimap_id
  map_comp {A₁ A₂ A₃} f g := by
    ext B
    simp only [powerWeightedProfunctorInner_obj, NatTrans.comp_app, unop_comp]
    rw [W.flip.map_comp, P.map_comp, NatTrans.comp_app, NatTrans.comp_app]
    exact HasPowers.bimap_comp _ _ _ _

@[simp]
theorem powerWeightedProfunctor_obj (A : Cᵒᵖ) :
    (powerWeightedProfunctor W P).obj A = powerWeightedProfunctorInner W P A :=
  rfl

@[simp]
theorem powerWeightedProfunctor_obj_obj (A : Cᵒᵖ) (B : C) :
    ((powerWeightedProfunctor W P).obj A).obj B =
      HasPowers.power ((P.obj A).obj B) ((W.flip.obj A.unop).obj (op B)) := rfl

@[simp]
theorem powerWeightedProfunctor_map_app {A₁ A₂ : Cᵒᵖ} (f : A₁ ⟶ A₂) (B : C) :
    ((powerWeightedProfunctor W P).map f).app B =
      HasPowers.bimap ((W.flip.map f.unop).app (op B)) ((P.map f).app B) := rfl

end PowerWeightedProfunctor

end ProfunctorWeights

end WeightedViaEnds

end GebLean
