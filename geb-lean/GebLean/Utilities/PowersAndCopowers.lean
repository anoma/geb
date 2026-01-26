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

end WeightedViaEnds

end GebLean
