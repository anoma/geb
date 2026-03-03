import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Pi.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Over
import GebLean.Utilities.Category
import GebLean.Utilities.Equalities
import GebLean.Utilities.Families
import GebLean.Utilities.Skeleton
import GebLean.Utilities.DoubleCategory
import GebLean.Utilities.Slice

/-!
# Polynomial Functors via Grothendieck Constructions

This module defines polynomial functors on `Type` using Grothendieck constructions.
For a locally Cartesian closed category like `Type`, polynomial functors can be
characterized in multiple equivalent ways:

1. **Via coproducts of covariant representables**: A polynomial functor
   `Over X → Type` is an object of `CoprodCovarRepCat (Over X)`.

2. **Via W-type diagrams**: A polynomial functor `Over X → Over Y` is given by
   a diagram `X ← E → B → Y` (pullback, dependent product, dependent sum).

3. **Via families**: A polynomial functor `Over X → Over Y` can be viewed as a
   `Y`-indexed family of polynomial functors `Over X → Type`, using the
   equivalence `FamilyCat Type Y ≃ Over Y`.

## Main definitions

* `familySliceForward` - Functor from families to slice: `FamilyCat Type Y → Over Y`
* `familySliceBackward` - Functor from slice to families: `Over Y → FamilyCat Type Y`
* `familySliceEquiv` - The equivalence `FamilyCat Type Y ≃ Over Y`

* `PolyFunctorCat` - Category of polynomial functors `Over X → Type`
* `PolyFunctorBetweenCat` - Category of polynomial functors `Over X → Over Y`

## References

* https://ncatlab.org/nlab/show/polynomial+functor
* https://ncatlab.org/nlab/show/free+coproduct+completion
-/

namespace GebLean

open CategoryTheory

universe u u'

/-! ## Family-Slice Equivalence

The fundamental equivalence between `Y`-indexed families of types and the slice
category `Over Y`. This equivalence is:
- Forward: `F ↦ (Σ y, F y, π₁)` (total space with first projection)
- Backward: `(A, f) ↦ (y ↦ f⁻¹(y))` (fibers of the map)
-/

section FamilySliceEquivalence

variable (Y : Type u)

/--
Forward functor from families to slice categories.
Given a family `F : Y → Type`, construct the total space `Σ y, F y` with the
first projection `π₁ : Σ y, F y → Y`.
-/
@[simp]
def familySliceForwardObj (F : FamilyCat (Type u) Y) : Over Y :=
  Over.mk (Sigma.fst : (Σ y, F y) → Y)

/--
Forward functor action on morphisms.
A morphism `φ : F → G` in `FamilyCat` (a family of functions `∀ y, F y → G y`)
induces a morphism on total spaces.
-/
@[simp]
def familySliceForwardMap {F G : FamilyCat (Type u) Y} (φ : F ⟶ G) :
    familySliceForwardObj Y F ⟶ familySliceForwardObj Y G :=
  Over.homMk (fun ⟨y, x⟩ => ⟨y, φ y x⟩) rfl

/--
The forward functor from `FamilyCat Type Y` to `Over Y`.
-/
@[simp]
def familySliceForward : FamilyCat (Type u) Y ⥤ Over Y where
  obj := familySliceForwardObj Y
  map := familySliceForwardMap Y
  map_id F := by
    apply Over.OverMorphism.ext
    funext ⟨y, x⟩
    rfl
  map_comp φ ψ := by
    apply Over.OverMorphism.ext
    funext ⟨y, x⟩
    rfl

/--
Backward functor from slice categories to families.
Given an object `(A, f : A → Y)` in `Over Y`, construct the family of fibers
`y ↦ f⁻¹(y) = { a : A | f a = y }`.
-/
@[simp]
def familySliceBackwardObj (obj : Over Y) : FamilyCat (Type u) Y :=
  fun y => { a : obj.left // obj.hom a = y }

/--
Backward functor action on morphisms.
A morphism `g : (A, f) → (B, h)` in `Over Y` (a map `g : A → B` with `h ∘ g = f`)
induces a morphism on fibers.
-/
@[simp]
def familySliceBackwardMap {A B : Over Y} (g : A ⟶ B) :
    familySliceBackwardObj Y A ⟶ familySliceBackwardObj Y B :=
  fun y ⟨a, ha⟩ => ⟨g.left a, by
    have hw := congrFun (Over.w g) a
    exact hw.trans ha⟩

/--
The backward functor from `Over Y` to `FamilyCat Type Y`.
-/
@[simp]
def familySliceBackward : Over Y ⥤ FamilyCat (Type u) Y where
  obj := familySliceBackwardObj Y
  map := familySliceBackwardMap Y
  map_id A := by
    funext y ⟨a, ha⟩
    simp only [familySliceBackwardMap]
    rfl
  map_comp g h := by
    funext y ⟨a, ha⟩
    simp only [familySliceBackwardMap]
    rfl

/-! ### Unit isomorphism

For a family `F : Y → Type`, the fibers of the total space `Σ y, F y` at each
`y` are exactly `F y`. More precisely, `familySliceForward ⋙ familySliceBackward`
is naturally isomorphic to the identity on `FamilyCat Type Y`.
-/

/--
For a family `F`, the fiber of the total space at `y` is isomorphic to `F y`.
The fiber at `y` consists of pairs `⟨(y', x), h⟩` where `h : y' = y`.
The isomorphism transports `x` along `h`.
-/
def familySliceUnitComponent (F : FamilyCat (Type u) Y) (y : Y) :
    (familySliceForward Y ⋙ familySliceBackward Y).obj F y ≃ F y where
  toFun := fun ⟨⟨y', x⟩, h⟩ => h ▸ x
  invFun := fun x => ⟨⟨y, x⟩, rfl⟩
  left_inv := fun ⟨⟨y', x⟩, h⟩ => by
    cases h
    rfl
  right_inv := fun _ => rfl

/--
The unit natural isomorphism: `familySliceForward ⋙ familySliceBackward ≅ 𝟭`.
For each family `F` and each `y`, the isomorphism `fibers of total space at y ≅ F y`.
-/
def familySliceUnitIso :
    familySliceForward Y ⋙ familySliceBackward Y ≅ 𝟭 (FamilyCat (Type u) Y) :=
  NatIso.ofComponents
    (fun F => {
      hom := fun y => (familySliceUnitComponent Y F y).toFun
      inv := fun y => (familySliceUnitComponent Y F y).invFun })
    (fun {F G} φ => by
      funext y ⟨⟨y', x⟩, h⟩
      cases h
      rfl)

/-! ### Counit isomorphism

For an over object `(A, f : A → Y)`, the total space of its fibers is
isomorphic to `A`. More precisely, `familySliceBackward ⋙ familySliceForward`
is naturally isomorphic to the identity on `Over Y`.
-/

/--
The left component of the counit isomorphism.
For an over object `obj = (A, f)`, the total space of fibers `Σ y, f⁻¹(y)`
is isomorphic to `A`.
-/
def familySliceCounitComponentLeft (obj : Over Y) :
    ((familySliceBackward Y ⋙ familySliceForward Y).obj obj).left ≃ obj.left where
  toFun := fun ⟨_, ⟨a, _⟩⟩ => a
  invFun := fun a => ⟨obj.hom a, ⟨a, rfl⟩⟩
  left_inv := fun ⟨y, ⟨a, h⟩⟩ => by
    cases h
    rfl
  right_inv := fun _ => rfl

/--
For an over object `obj = (A, f)`, the total space of fibers is isomorphic to `A`
as an object of `Over Y`.
-/
def familySliceCounitComponent (obj : Over Y) :
    (familySliceBackward Y ⋙ familySliceForward Y).obj obj ≅ obj :=
  Over.isoMk (familySliceCounitComponentLeft Y obj).toIso (by
    funext ⟨y, ⟨a, h⟩⟩
    exact h)

/--
The counit natural isomorphism: `familySliceBackward ⋙ familySliceForward ≅ 𝟭 (Over Y)`.
-/
def familySliceCounitIso :
    familySliceBackward Y ⋙ familySliceForward Y ≅ 𝟭 (Over Y) :=
  NatIso.ofComponents
    (fun obj => familySliceCounitComponent Y obj)
    (fun {A B} g => by
      apply Over.OverMorphism.ext
      funext ⟨y, ⟨a, h⟩⟩
      simp only [Functor.comp_obj, familySliceBackward, familySliceBackwardObj,
                 familySliceForward, familySliceForwardObj, Functor.id_obj]
      simp only [familySliceCounitComponent, familySliceCounitComponentLeft]
      simp only [Over.isoMk]
      rfl)

/-! ### The equivalence -/

/--
The equivalence between `FamilyCat Type Y` and `Over Y`.

This is the fundamental equivalence between dependent types (families of types
indexed by `Y`) and fibrations (maps into `Y`).

- Forward: `F ↦ (Σ y, F y, π₁)`
- Backward: `(A, f) ↦ (y ↦ f⁻¹(y))`
-/
def familySliceEquiv : FamilyCat (Type u) Y ≌ Over Y where
  functor := familySliceForward Y
  inverse := familySliceBackward Y
  unitIso := (familySliceUnitIso Y).symm
  counitIso := familySliceCounitIso Y
  functor_unitIso_comp F := by
    apply Over.OverMorphism.ext
    funext ⟨y, x⟩
    simp only [Functor.id_obj, familySliceForward, familySliceForwardObj, Functor.comp_obj,
               familySliceBackward, familySliceBackwardObj,
               familySliceForwardMap, familySliceUnitIso, familySliceUnitComponent,
               familySliceCounitIso, familySliceCounitComponent,
               familySliceCounitComponentLeft, Over.isoMk, Over.homMk]
    rfl

end FamilySliceEquivalence

/-! ## General Polynomial Functors

A polynomial functor from an arbitrary category `D` to `Type` is given by an
object of `CoprodCovarRepCat D`. An object `(I, F)` where `I : Type` and
`F : I → D` represents the polynomial functor:

```
A ↦ Σ_{i : I} Hom_D(F(i), A)
```

This section defines evaluation for arbitrary domain categories. The existing
`PolyFunctorCat X` is the specialization to `D = Over X`.
-/

section GeneralPolynomialFunctors

universe u''

variable {D : Type u'} [Category.{u} D]

/--
Evaluation of a polynomial functor at an object of `D`.
Given a polynomial `P = (I, F)` where `F : I → D` and an object `A : D`,
the evaluation `P(A) = Σ_{i : I} Hom_D(F(i), A)` is a type.
-/
def ccrEval (P : CoprodCovarRepCat.{u', u, u''} D) (A : D) :=
  Σ i : ccrIndex P, (ccrFamily P i ⟶ A)

/--
Extract the index from an element of a polynomial evaluation.
-/
def ccrEvalIndex {P : CoprodCovarRepCat.{u', u, u''} D} {A : D} (x : ccrEval P A) :
    ccrIndex P :=
  x.1

/--
Extract the morphism from an element of a polynomial evaluation.
-/
def ccrEvalMor {P : CoprodCovarRepCat.{u', u, u''} D} {A : D} (x : ccrEval P A) :
    ccrFamily P (ccrEvalIndex x) ⟶ A :=
  x.2

/--
Construct an element of a polynomial evaluation from an index and a morphism.
-/
def ccrEvalMk {P : CoprodCovarRepCat.{u', u, u''} D} {A : D}
    (i : ccrIndex P) (f : ccrFamily P i ⟶ A) : ccrEval P A :=
  ⟨i, f⟩

@[simp]
lemma ccrEvalMk_index {P : CoprodCovarRepCat.{u', u, u''} D} {A : D}
    (i : ccrIndex P) (f : ccrFamily P i ⟶ A) :
    ccrEvalIndex (ccrEvalMk i f) = i := rfl

@[simp]
lemma ccrEvalMk_mor {P : CoprodCovarRepCat.{u', u, u''} D} {A : D}
    (i : ccrIndex P) (f : ccrFamily P i ⟶ A) :
    ccrEvalMor (ccrEvalMk i f) = f := rfl

/--
Extensionality for polynomial evaluations.
-/
lemma ccrEval_ext {P : CoprodCovarRepCat.{u', u, u''} D} {A : D} (x y : ccrEval P A)
    (hi : ccrEvalIndex x = ccrEvalIndex y)
    (hm : ccrEvalMor x ≍ ccrEvalMor y) : x = y := by
  obtain ⟨ix, mx⟩ := x
  obtain ⟨iy, my⟩ := y
  simp only [ccrEvalIndex] at hi
  cases hi
  simp only [ccrEvalMor] at hm
  cases eq_of_heq hm
  rfl

@[simp]
lemma ccrEvalMk_eta {P : CoprodCovarRepCat.{u', u, u''} D} {A : D} (x : ccrEval P A) :
    ccrEvalMk (ccrEvalIndex x) (ccrEvalMor x) = x := rfl

/--
The action of a polynomial functor on morphisms.
Given `f : A ⟶ B`, maps `⟨i, h⟩ : ccrEval P A` to `⟨i, h ≫ f⟩ : ccrEval P B`.
-/
def ccrEvalMap {P : CoprodCovarRepCat.{u', u, u''} D} {A B : D} (f : A ⟶ B) :
    ccrEval P A → ccrEval P B :=
  fun ⟨i, h⟩ => ⟨i, h ≫ f⟩

@[simp]
lemma ccrEvalMap_index {P : CoprodCovarRepCat.{u', u, u''} D} {A B : D} (f : A ⟶ B)
    (x : ccrEval P A) : ccrEvalIndex (ccrEvalMap f x) = ccrEvalIndex x := rfl

@[simp]
lemma ccrEvalMap_mor {P : CoprodCovarRepCat.{u', u, u''} D} {A B : D} (f : A ⟶ B)
    (x : ccrEval P A) : ccrEvalMor (ccrEvalMap f x) = ccrEvalMor x ≫ f := rfl

@[simp]
lemma ccrEvalMap_id {P : CoprodCovarRepCat.{u', u, u''} D} {A : D} :
    ccrEvalMap (𝟙 A) = (id : ccrEval P A → ccrEval P A) := by
  funext ⟨i, h⟩
  simp only [ccrEvalMap, Category.comp_id, id_eq]

@[simp]
lemma ccrEvalMap_comp {P : CoprodCovarRepCat.{u', u, u''} D} {A B C : D} (f : A ⟶ B) (g : B ⟶ C) :
    ccrEvalMap (f ≫ g) = ccrEvalMap g ∘ ccrEvalMap (P := P) f := by
  funext ⟨i, h⟩
  simp only [ccrEvalMap, Category.assoc, Function.comp_apply]

/--
A polynomial functor `P : CoprodCovarRepCat D` gives a functor `D ⥤ Type`.
-/
def ccrToFunctor (P : CoprodCovarRepCat.{u', u, u''} D) : D ⥤ Type _ where
  obj := ccrEval P
  map := ccrEvalMap
  map_id := fun _ => ccrEvalMap_id
  map_comp := fun f g => ccrEvalMap_comp f g

/-! ### Category of Elements

The category of elements of a coproduct of covariant representables is
obtained by applying mathlib's `Functor.Elements` to `ccrToFunctor`.

Objects are pairs `(A : D, x : ccrEval P A)` where `x = ⟨i, f⟩` consists of
a position `i : ccrIndex P` and a morphism `f : ccrFamily P i ⟶ A`.

Morphisms `(A, ⟨i, f⟩) ⟶ (B, ⟨j, g⟩)` are morphisms `h : A ⟶ B` in `D` such
that `ccrEvalMap h ⟨i, f⟩ = ⟨j, g⟩`, which means `i = j` and `f ≫ h = g`.
-/

/-- The category of elements of a polynomial functor. -/
abbrev ccrElements (P : CoprodCovarRepCat.{u', u, u''} D) : Type _ := (ccrToFunctor P).Elements

/-- Objects of the category of elements: pairs `(A, x)` where `x : ccrEval P A`. -/
abbrev ccrElementsObj (P : CoprodCovarRepCat.{u', u, u''} D) : Type _ := (ccrToFunctor P).Elements

instance ccrElementsCategory (P : CoprodCovarRepCat.{u', u, u''} D) :
    Category (ccrElements P) :=
  inferInstance

/-- Morphisms in the category of elements. -/
abbrev ccrElementsMor {P : CoprodCovarRepCat.{u', u, u''} D} (X Y : ccrElements P) : Type _ :=
  X ⟶ Y

/-- The base object of an element in the category of elements. -/
def ccrElementsBase {P : CoprodCovarRepCat.{u', u, u''} D} (e : ccrElements P) : D := e.fst

/-- The fiber (the element of `ccrEval P A`) of an element in the category of
elements. -/
def ccrElementsFiber {P : CoprodCovarRepCat.{u', u, u''} D} (e : ccrElements P) :
    ccrEval P (ccrElementsBase e) := e.snd

/-- The position component of an element in the category of elements. -/
def ccrElementsPos {P : CoprodCovarRepCat.{u', u, u''} D} (e : ccrElements P) : ccrIndex P :=
  (ccrElementsFiber e).1

/-- The morphism component of an element in the category of elements. -/
def ccrElementsHom {P : CoprodCovarRepCat.{u', u, u''} D} (e : ccrElements P) :
    ccrFamily P (ccrElementsPos e) ⟶ ccrElementsBase e :=
  (ccrElementsFiber e).2

end GeneralPolynomialFunctors

/-! ## General Polynomial Functors to Over Categories

A polynomial functor from an arbitrary category `D` to `Over Y` is a
`Y`-indexed family of polynomial functors `D → Type`. Since each
`D → Type` polynomial functor is an object of `CoprodCovarRepCat D`,
a polynomial functor `D → Over Y` is an object of
`FamilyCat (CoprodCovarRepCat D) Y`.

Evaluation: For `P : FamilyCat (CoprodCovarRepCat D) Y` and `A : D`,
we compute the family `y ↦ ccrEval (P y) A` and use `familySliceForward`
to convert to `Over Y`.
-/

section GeneralPolynomialFunctorsToOver

variable {D : Type u'} [Category.{u} D]
variable (Y : Type u)

/--
The category of polynomial functors `D → Over Y`.

Objects are `Y`-indexed families of polynomial functors `D → Type`.
For each `y : Y`, we have a polynomial functor `P(y) : D → Type`, which
is an object of `CoprodCovarRepCat D`, i.e., a pair `(I_y, F_y)` where
`I_y` is a type of positions and `F_y : I_y → D` gives the representables.
-/
abbrev PolyToOverCat : Cat := FamilyCat (CoprodCovarRepCat D) Y

/--
Extract the polynomial functor at a specific codomain point.
-/
def polyToOverAt (P : PolyToOverCat (D := D) Y) (y : Y) : CoprodCovarRepCat D :=
  P y

/--
The index type (positions) at a specific codomain point.
-/
def polyToOverIndex (P : PolyToOverCat (D := D) Y) (y : Y) :=
  ccrIndex (P y)

/--
The family of representables at a specific codomain point and position.
-/
def polyToOverFamily (P : PolyToOverCat (D := D) Y) (y : Y)
    (i : polyToOverIndex Y P y) : D :=
  ccrFamily (P y) i

/--
Evaluate a polynomial functor `D → Over Y` at an object `A : D`,
producing a family `Y → Type`.

For each `y : Y`, we evaluate the polynomial `P(y)` at `A`:
`P(A)(y) = Σ (i : positions at y), Hom_D(F_y(i), A)`
-/
def polyToOverEvalFamily (P : PolyToOverCat (D := D) Y) (A : D) :=
  fun y => ccrEval (P y) A

/--
Evaluate a polynomial functor at an object of `D`, producing an object
of `Over Y` via the family-slice equivalence.
-/
def polyToOverEval (P : PolyToOverCat (D := D) Y) (A : D) : Over Y :=
  (familySliceForward Y).obj (polyToOverEvalFamily Y P A)

/-! ### polyToOverEvalFamily helpers -/

/--
Extract the index from an element of `polyToOverEvalFamily`.
-/
def ptoefIndex {P : PolyToOverCat (D := D) Y} {A : D} {y : Y}
    (x : polyToOverEvalFamily Y P A y) : ccrIndex (P y) :=
  ccrEvalIndex x

/--
Extract the morphism from an element of `polyToOverEvalFamily`.
-/
def ptoefMor {P : PolyToOverCat (D := D) Y} {A : D} {y : Y}
    (x : polyToOverEvalFamily Y P A y) :
    ccrFamily (P y) (ccrEvalIndex x) ⟶ A :=
  ccrEvalMor x

/--
Construct an element of `polyToOverEvalFamily` from an index and morphism.
-/
def ptoefMk {P : PolyToOverCat (D := D) Y} {A : D} {y : Y}
    (i : ccrIndex (P y)) (f : ccrFamily (P y) i ⟶ A) :
    polyToOverEvalFamily Y P A y :=
  ccrEvalMk i f

@[simp]
lemma ptoefMk_index {P : PolyToOverCat (D := D) Y} {A : D}
    {y : Y} (i : ccrIndex (P y)) (f : ccrFamily (P y) i ⟶ A) :
    ccrEvalIndex (ptoefMk Y i f) = i := rfl

@[simp]
lemma ptoefMk_mor {P : PolyToOverCat (D := D) Y} {A : D}
    {y : Y} (i : ccrIndex (P y)) (f : ccrFamily (P y) i ⟶ A) :
    ccrEvalMor (ptoefMk Y i f) = f := rfl

@[simp]
lemma ptoefMk_eta {P : PolyToOverCat (D := D) Y} {A : D}
    {y : Y} (x : polyToOverEvalFamily Y P A y) :
    ptoefMk Y (ccrEvalIndex x) (ccrEvalMor x) = x := rfl

/-! ### polyToOverEval functoriality -/

/--
The action on morphisms for `polyToOverEvalFamily`.
Given `f : A ⟶ B`, produces a fiber-wise map.
-/
def polyToOverEvalFamilyMap (P : PolyToOverCat (D := D) Y) {A B : D} (f : A ⟶ B) :
    polyToOverEvalFamily Y P A ⟶ polyToOverEvalFamily Y P B :=
  fun _ => ccrEvalMap f

@[simp]
lemma polyToOverEvalFamilyMap_id (P : PolyToOverCat (D := D) Y) (A : D) :
    polyToOverEvalFamilyMap Y P (𝟙 A) = 𝟙 (polyToOverEvalFamily Y P A) := by
  funext _
  exact ccrEvalMap_id

@[simp]
lemma polyToOverEvalFamilyMap_comp (P : PolyToOverCat (D := D) Y)
    {A B C : D} (f : A ⟶ B) (g : B ⟶ C) :
    polyToOverEvalFamilyMap Y P (f ≫ g) =
      polyToOverEvalFamilyMap Y P f ≫ polyToOverEvalFamilyMap Y P g := by
  funext _
  exact ccrEvalMap_comp f g

/--
A polynomial functor `P : PolyToOverCat D Y` gives a functor `D ⥤ FamilyCat (Type) Y`.

This functor applies `ccrToFunctor (P y)` at each fiber `y : Y`, producing a
`Y`-indexed family of types for each object `A : D`.
-/
def polyToOverFamilyFunctor (P : PolyToOverCat (D := D) Y) :
    D ⥤ FamilyCat (Type u) Y where
  obj := polyToOverEvalFamily Y P
  map := polyToOverEvalFamilyMap Y P
  map_id := fun A => polyToOverEvalFamilyMap_id Y P A
  map_comp := fun f g => polyToOverEvalFamilyMap_comp Y P f g

/--
The action on morphisms for `polyToOverEval`.
Given `f : A ⟶ B`, produces a morphism in `Over Y`.
-/
def polyToOverEvalMap (P : PolyToOverCat (D := D) Y) {A B : D} (f : A ⟶ B) :
    polyToOverEval Y P A ⟶ polyToOverEval Y P B :=
  (familySliceForward Y).map (polyToOverEvalFamilyMap Y P f)

@[simp]
lemma polyToOverEvalMap_left (P : PolyToOverCat (D := D) Y) {A B : D}
    (f : A ⟶ B) (x : (polyToOverEval Y P A).left) :
    (polyToOverEvalMap Y P f).left x = ⟨x.fst, ccrEvalMap f x.snd⟩ := rfl

@[simp]
lemma polyToOverEvalMap_id (P : PolyToOverCat (D := D) Y) (A : D) :
    polyToOverEvalMap Y P (𝟙 A) = 𝟙 (polyToOverEval Y P A) := by
  simp only [polyToOverEvalMap, polyToOverEvalFamilyMap_id,
    CategoryTheory.Functor.map_id]
  rfl

@[simp]
lemma polyToOverEvalMap_comp (P : PolyToOverCat (D := D) Y)
    {A B C : D} (f : A ⟶ B) (g : B ⟶ C) :
    polyToOverEvalMap Y P (f ≫ g) =
      polyToOverEvalMap Y P f ≫ polyToOverEvalMap Y P g := by
  simp only [polyToOverEvalMap, polyToOverEvalFamilyMap_comp,
    CategoryTheory.Functor.map_comp]

/--
A polynomial functor `P : PolyToOverCat D Y` gives a functor `D ⥤ Over Y`.
-/
def polyToOverFunctor (P : PolyToOverCat (D := D) Y) : D ⥤ Over Y where
  obj := polyToOverEval Y P
  map := polyToOverEvalMap Y P
  map_id := fun A => polyToOverEvalMap_id Y P A
  map_comp := fun f g => polyToOverEvalMap_comp Y P f g

/-- `polyToOverFunctor` factors through `polyToOverFamilyFunctor` and
`familySliceForward`. -/
lemma polyToOverFunctor_eq_comp (P : PolyToOverCat (D := D) Y) :
    polyToOverFunctor Y P = polyToOverFamilyFunctor Y P ⋙ familySliceForward Y :=
  rfl

/-! ### polyToOverEval structure -/

/--
The left component of `polyToOverEval` is the sigma type over the family.
-/
lemma polyToOverEval_left (P : PolyToOverCat (D := D) Y) (A : D) :
    (polyToOverEval Y P A).left = Σ y, polyToOverEvalFamily Y P A y := rfl

/--
The structure map of `polyToOverEval` is the first projection.
-/
lemma polyToOverEval_hom (P : PolyToOverCat (D := D) Y) (A : D) :
    (polyToOverEval Y P A).hom = Sigma.fst := rfl

/--
Extract the Y-coordinate from an element of `(polyToOverEval Y P A).left`.
-/
def ptoeLeftY {P : PolyToOverCat (D := D) Y} {A : D}
    (e : (polyToOverEval Y P A).left) : Y :=
  e.fst

/--
Extract the fiber element from an element of `(polyToOverEval Y P A).left`.
-/
def ptoeLeftFiber {P : PolyToOverCat (D := D) Y} {A : D}
    (e : (polyToOverEval Y P A).left) :
    polyToOverEvalFamily Y P A e.fst :=
  e.snd

/--
Construct an element of `(polyToOverEval Y P A).left` from components.
-/
def ptoeLeftMk {P : PolyToOverCat (D := D) Y} {A : D}
    (y : Y) (x : polyToOverEvalFamily Y P A y) :
    (polyToOverEval Y P A).left :=
  ⟨y, x⟩

@[simp]
lemma ptoeLeftMk_y {P : PolyToOverCat (D := D) Y} {A : D}
    (y : Y) (x : polyToOverEvalFamily Y P A y) :
    (ptoeLeftMk Y y x).fst = y := rfl

@[simp]
lemma ptoeLeftMk_fiber {P : PolyToOverCat (D := D) Y} {A : D}
    (y : Y) (x : polyToOverEvalFamily Y P A y) :
    (ptoeLeftMk Y y x).snd = x := rfl

@[simp]
lemma ptoeLeftMk_eta {P : PolyToOverCat (D := D) Y} {A : D}
    (e : (polyToOverEval Y P A).left) :
    ptoeLeftMk Y e.fst e.snd = e := rfl

/--
The structure map applied to a left element gives the Y-coordinate.
-/
@[simp]
lemma polyToOverEval_hom_ptoeLeftMk {P : PolyToOverCat (D := D) Y} {A : D}
    (y : Y) (x : polyToOverEvalFamily Y P A y) :
    (polyToOverEval Y P A).hom (ptoeLeftMk Y y x) = y := rfl

/-! ### Morphisms into polyToOverEval

When we have a morphism `h : B ⟶ polyToOverEval Y P A` in `Over Y`, the
commutativity condition ensures that `h.left b` has Y-coordinate `B.hom b`.
This allows us to extract the fiber element at the appropriate type.
-/

/--
For a morphism into `polyToOverEval`, the Y-coordinate of the image equals
the structure map of the source.
-/
lemma mor_to_ptoe_y {P : PolyToOverCat (D := D) Y} {A : D}
    {B : Over Y} (h : B ⟶ polyToOverEval Y P A) (b : B.left) :
    ptoeLeftY Y (h.left b) = B.hom b :=
  congrFun (Over.w h) b

/--
Given a morphism `h : B ⟶ polyToOverEval Y P A` and `b : B.left`, we can
extract the fiber element at `B.hom b`. This uses the commutativity condition
to transport from `ptoeLeftY (h.left b)` to `B.hom b`.
-/
def mor_to_ptoe_fiber {P : PolyToOverCat (D := D) Y} {A : D}
    {B : Over Y} (h : B ⟶ polyToOverEval Y P A) (b : B.left) :
    polyToOverEvalFamily Y P A (B.hom b) :=
  (mor_to_ptoe_y Y h b) ▸ ptoeLeftFiber Y (h.left b)

/--
The fiber element from a morphism: extract the index.
-/
def mor_to_ptoe_fiber_index {P : PolyToOverCat (D := D) Y} {A : D}
    {B : Over Y} (h : B ⟶ polyToOverEval Y P A) (b : B.left) :
    ccrIndex (P (B.hom b)) :=
  ptoefIndex Y (mor_to_ptoe_fiber Y h b)

/--
The fiber element from a morphism: extract the inner morphism.
-/
def mor_to_ptoe_fiber_mor {P : PolyToOverCat (D := D) Y} {A : D}
    {B : Over Y} (h : B ⟶ polyToOverEval Y P A) (b : B.left) :
    ccrFamily (P (B.hom b)) (mor_to_ptoe_fiber_index Y h b) ⟶ A :=
  ptoefMor Y (mor_to_ptoe_fiber Y h b)

/--
Heterogeneous equality between `mor_to_ptoe_fiber` and the raw fiber.
-/
lemma mor_to_ptoe_fiber_heq_raw {P : PolyToOverCat (D := D) Y} {A : D}
    {B : Over Y} (h : B ⟶ polyToOverEval Y P A) (b : B.left) :
    mor_to_ptoe_fiber Y h b ≍ ptoeLeftFiber Y (h.left b) := by
  simp only [mor_to_ptoe_fiber]
  exact eqRec_heq (mor_to_ptoe_y Y h b) (ptoeLeftFiber Y (h.left b))

/--
When the morphism `h` is constructed via `Over.homMk` and the fiber function
produces elements with the correct Y-coordinate (i.e., `w` is
`funext (fun _ => rfl)`), `mor_to_ptoe_fiber_index` reduces definitionally.
-/
lemma mor_to_ptoe_fiber_index_homMk_rfl {P : PolyToOverCat (D := D) Y} {A : D}
    {B : Over Y}
    (fn : (b : B.left) → polyToOverEvalFamily Y P A (B.hom b))
    (b : B.left) :
    mor_to_ptoe_fiber_index Y
      (Over.homMk (fun b => ptoeLeftMk Y (B.hom b) (fn b))
        (funext (fun _ => rfl))) b = ptoefIndex Y (fn b) := by
  simp only [mor_to_ptoe_fiber_index, mor_to_ptoe_fiber, ptoefIndex,
             ptoeLeftMk, ptoeLeftFiber]
  rfl

/--
The analogous lemma for `mor_to_ptoe_fiber_mor`.
-/
lemma mor_to_ptoe_fiber_mor_homMk_rfl {P : PolyToOverCat (D := D) Y} {A : D}
    {B : Over Y}
    (fn : (b : B.left) → polyToOverEvalFamily Y P A (B.hom b))
    (b : B.left) :
    mor_to_ptoe_fiber_mor Y
      (Over.homMk (fun b => ptoeLeftMk Y (B.hom b) (fn b))
        (funext (fun _ => rfl))) b = ptoefMor Y (fn b) := by
  simp only [mor_to_ptoe_fiber_mor, mor_to_ptoe_fiber, ptoefMor,
             ptoeLeftMk, ptoeLeftFiber]
  rfl

end GeneralPolynomialFunctorsToOver

/-! ## Generalized Polynomial Functor Composition

Composition of polynomial functors can be generalized to domain categories `D`
that have all small coproducts. The composed representable is constructed as
a coproduct over the directions of `g`.

For `f : PolyToOverCat D Y` and `g : PolyToOverCat (Over Y) Z`:
- The composed index at `z` is `ccrEval (g z) (index object of f)`
- The composed representable at position `(ig, pf)` is:
  `∐ (eg : g-directions at ig), (f-representable at pf(eg))`
-/

section GeneralizedComposition

variable {D : Type u'} [Category.{u} D] [CoprodData.{u} D]
variable {Y Z : Type u}

/--
The index type for composition of general polynomial functors.

Given `f : PolyToOverCat D Y` and `g : PolyToOverCat (Over Y) Z`, at `z : Z`,
positions are pairs of a g-position and a function assigning f-positions
to each g-direction.
-/
def polyToOverCompIndex (g : PolyToOverCat (D := Over Y) Z)
    (f : PolyToOverCat (D := D) Y) (z : Z) : Type _ :=
  Σ (ig : ccrIndex (g z)),
    ∀ (eg : (ccrFamily (g z) ig).left), ccrIndex (f ((ccrFamily (g z) ig).hom eg))

/--
The family of representables for composition, defined using `CoprodData`.

At position `(ig, pf)`, the composed representable is the coproduct over
g-directions of the f-representables at the selected positions.

This definition is computable when `CoprodData D` has a computable instance
(e.g., for `D = Over X`). The use of `CoprodData` instead of `HasCoproducts`
separates the coproduct structure from the universal property proofs.
-/
def polyToOverCompFamily (g : PolyToOverCat (D := Over Y) Z)
    (f : PolyToOverCat (D := D) Y) (z : Z)
    (p : polyToOverCompIndex g f z) : D :=
  ∐' (fun (eg : (ccrFamily (g z) p.1).left) =>
    ccrFamily (f ((ccrFamily (g z) p.1).hom eg)) (p.2 eg))

/--
Composition of polynomial functors with general domain `D` having coproduct data.

Given `f : D → Over Y` and `g : Over Y → Over Z`, produces `f ≫ g : D → Over Z`.

This definition is computable when `CoprodData D` has a computable instance.
-/
def polyToOverComp (g : PolyToOverCat (D := Over Y) Z)
    (f : PolyToOverCat (D := D) Y) : PolyToOverCat (D := D) Z :=
  fun z => ccrObjMk (polyToOverCompFamily g f z)

end GeneralizedComposition

/-! ## Polynomial Functors Over X → Type

A polynomial functor `Over X → Type` is given by an object of
`CoprodCovarRepCat (Over X)`. An object `(I, F)` where `I : Type` and
`F : I → Over X` represents the polynomial functor:

```
A ↦ Σ_{i : I} Hom_{Over X}(F(i), A)
```

This section defines the category of polynomial functors and the evaluation
functor.
-/

section PolynomialFunctorsToType

variable (X : Type u)

/--
The category of polynomial functors `Over X → Type`.

Objects are pairs `(I, F)` where `I : Type` and `F : I → Over X`.
An object represents the polynomial functor `A ↦ Σ_{i : I} Hom(F(i), A)`.

Morphisms `(I, F) → (J, G)` consist of:
- `r : I → J` (a reindexing function)
- `φ : ∀ i, G(r(i)) ⟶ F(i)` (a family of morphisms in `Over X`)
-/
abbrev PolyFunctorCat : Cat := CoprodCovarRepCat (Over X)

/--
Evaluation of a polynomial functor at an object of `Over X`.
Given a polynomial `P = (I, F)` and an object `A : Over X`, the evaluation
`P(A) = Σ_{i : I} Hom_{Over X}(F(i), A)` is a type.

This is the specialization of `ccrEval` to `D = Over X`.
-/
def polyEval (P : PolyFunctorCat X) (A : Over X) : Type u :=
  ccrEval P A

/--
Extract the index from an element of a polynomial evaluation.
Specialization of `ccrEvalIndex`.
-/
def polyEvalIndex {P : PolyFunctorCat X} {A : Over X} (x : polyEval X P A) :
    ccrIndex P :=
  ccrEvalIndex x

/--
Extract the morphism from an element of a polynomial evaluation.
Specialization of `ccrEvalMor`.
-/
def polyEvalMor {P : PolyFunctorCat X} {A : Over X} (x : polyEval X P A) :
    ccrFamily P (polyEvalIndex X x) ⟶ A :=
  ccrEvalMor x

/--
Construct an element of a polynomial evaluation from an index and a morphism.
Specialization of `ccrEvalMk`.
-/
def polyEvalMk {P : PolyFunctorCat X} {A : Over X}
    (i : ccrIndex P) (f : ccrFamily P i ⟶ A) : polyEval X P A :=
  ccrEvalMk i f

@[simp]
lemma polyEvalMk_index {P : PolyFunctorCat X} {A : Over X}
    (i : ccrIndex P) (f : ccrFamily P i ⟶ A) :
    polyEvalIndex X (polyEvalMk X i f) = i := rfl

@[simp]
lemma polyEvalMk_mor {P : PolyFunctorCat X} {A : Over X}
    (i : ccrIndex P) (f : ccrFamily P i ⟶ A) :
    polyEvalMor X (polyEvalMk X i f) = f := rfl

/--
Extensionality for polynomial evaluations.
Specialization of `ccrEval_ext`.
-/
lemma polyEval_ext {P : PolyFunctorCat X} {A : Over X} (x y : polyEval X P A)
    (hi : polyEvalIndex X x = polyEvalIndex X y)
    (hm : polyEvalMor X x ≍ polyEvalMor X y) : x = y :=
  ccrEval_ext x y hi hm

/--
Round-trip: constructing and then extracting gives the original.
-/
@[simp]
lemma polyEvalMk_eta {P : PolyFunctorCat X} {A : Over X} (x : polyEval X P A) :
    polyEvalMk X (polyEvalIndex X x) (polyEvalMor X x) = x := rfl

/--
The action of a polynomial functor on morphisms.
Specialization of `ccrEvalMap` to `D = Over X`.
-/
def polyEvalMap {P : PolyFunctorCat X} {A B : Over X} (f : A ⟶ B) :
    polyEval X P A → polyEval X P B :=
  ccrEvalMap f

@[simp]
lemma polyEvalMap_index {P : PolyFunctorCat X} {A B : Over X} (f : A ⟶ B)
    (x : polyEval X P A) :
    polyEvalIndex X (polyEvalMap X f x) = polyEvalIndex X x := rfl

@[simp]
lemma polyEvalMap_mor {P : PolyFunctorCat X} {A B : Over X} (f : A ⟶ B)
    (x : polyEval X P A) :
    polyEvalMor X (polyEvalMap X f x) = polyEvalMor X x ≫ f := rfl

@[simp]
lemma polyEvalMap_id {P : PolyFunctorCat X} {A : Over X} :
    polyEvalMap X (𝟙 A) = (id : polyEval X P A → polyEval X P A) :=
  ccrEvalMap_id

@[simp]
lemma polyEvalMap_comp {P : PolyFunctorCat X} {A B C : Over X}
    (f : A ⟶ B) (g : B ⟶ C) :
    polyEvalMap X (f ≫ g) = polyEvalMap X g ∘ polyEvalMap (P := P) X f :=
  ccrEvalMap_comp f g

/--
A polynomial functor `P : PolyFunctorCat X` gives a functor `Over X ⥤ Type u`.
Specialization of `ccrToFunctor` to `D = Over X`.
-/
def polyEvalFunctor (P : PolyFunctorCat X) : Over X ⥤ Type u :=
  ccrToFunctor P

/--
The composition `.fiber ≫ eqToHom` at index equals composition in Over.
-/
private lemma fiber_comp_eqToHom_at_idx {x y : CoprodCovarRepCat (Over X)}
    (f : x ⟶ y) {h : f.base = f.base} :
    (f.fiber ≫ eqToHom (by rw [h])) = f.fiber := by
  simp only [eqToHom_refl, Category.comp_id]

end PolynomialFunctorsToType

/-! ## Polynomial Functors Between Slices via FamilyCat

A polynomial functor `Over X → Over Y` is represented as a `Y`-indexed
family of polynomial functors `Over X → Type`. Since each `Over X → Type`
polynomial functor is an object of `PolyFunctorCat X`, a polynomial functor
`Over X → Over Y` is an object of `FamilyCat (PolyFunctorCat X) Y`.

This reuses our existing infrastructure for:
- `PolyFunctorCat X = CoprodCovarRepCat (Over X)` - polynomial functors to Type
- `FamilyCat C Y` - `Y`-indexed families of objects from category `C`
-/

section PolyFunctorBetween

variable (X : Type u) (Y : Type u)

/--
The category of polynomial functors `Over X → Over Y`.

An object is a `Y`-indexed family of polynomial functors `Over X → Type`.
This is the specialization of `PolyToOverCat` to `D = Over X`.

For each `y : Y`, we have a polynomial functor `P(y) : Over X → Type`, which
is an object of `CoprodCovarRepCat (Over X)`, i.e., a pair `(I_y, F_y)` where
`I_y` is a type of positions and `F_y : I_y → Over X` gives the representables.
-/
abbrev PolyFunctorBetweenCat : Cat :=
  PolyToOverCat (D := Over X) Y

/--
Extract the polynomial functor at a specific codomain point.
Specialization of `polyToOverAt`.
-/
def polyBetweenAt (P : PolyFunctorBetweenCat X Y) (y : Y) : PolyFunctorCat X :=
  polyToOverAt Y P y

/--
The index type (positions) at a specific codomain point.
Specialization of `polyToOverIndex`.
-/
def polyBetweenIndex (P : PolyFunctorBetweenCat X Y) (y : Y) :=
  polyToOverIndex Y P y

/--
The object in `Over Y` whose fiber at `y` is the index type of `P` at `y`.
This is the family of positions viewed as a single object over `Y`.
-/
def polyBetweenIndexObj (P : PolyFunctorBetweenCat X Y) : Over Y :=
  (familySliceForward Y).obj (polyBetweenIndex X Y P)

/--
The family of representables at a specific codomain point and position.
Specialization of `polyToOverFamily`.
-/
def polyBetweenFamily (P : PolyFunctorBetweenCat X Y) (y : Y)
    (i : polyBetweenIndex X Y P y) : Over X :=
  polyToOverFamily Y P y i

/--
Data witnessing that a polynomial functor
`Over X → Over Y` is finitary: for every codomain
point `y : Y` and position `i`, the carrier type
of the family `polyBetweenFamily X Y P y i` has
a `Fintype` instance (constructive enumeration).
-/
structure PolyBetweenFinitaryData
    (P : PolyFunctorBetweenCat X Y) where
  familyFintype :
    ∀ (y : Y) (i : polyBetweenIndex X Y P y),
      Fintype (polyBetweenFamily X Y P y i).left

/--
A polynomial functor `Over X → Over Y` is finitary
when each family fiber has finitely many elements
with constructive enumeration data.
-/
class PolyBetweenFinitary
    (P : PolyFunctorBetweenCat X Y) where
  data : PolyBetweenFinitaryData X Y P

instance polyBetweenFamilyFintype
    {P : PolyFunctorBetweenCat X Y}
    [h : PolyBetweenFinitary X Y P]
    (y : Y) (i : polyBetweenIndex X Y P y) :
    Fintype (polyBetweenFamily X Y P y i).left :=
  h.data.familyFintype y i

/--
Evaluate a polynomial functor `Over X → Over Y` at an object `A : Over X`,
producing a family `Y → Type`.
Specialization of `polyToOverEvalFamily`.

For each `y : Y`, we evaluate the polynomial `P(y)` at `A`:
`P(A)(y) = Σ (i : positions at y), Hom_{Over X}(F_y(i), A)`
-/
def polyBetweenEvalFamily (P : PolyFunctorBetweenCat X Y) (A : Over X) :=
  polyToOverEvalFamily Y P A

/--
Evaluate a polynomial functor at an object of `Over X`, producing an object
of `Over Y` via the family-slice equivalence.
Specialization of `polyToOverEval`.
-/
def polyBetweenEval (P : PolyFunctorBetweenCat X Y) (A : Over X) : Over Y :=
  polyToOverEval Y P A

/-! #### polyBetweenEvalFamily helpers

Since `polyBetweenEvalFamily P A y = polyEval X (P y) A`, we can reuse the
`polyEval` infrastructure. However, we also need lemmas connecting these
to the structure of `polyBetweenEval P A` as an `Over Y` object.
-/

/--
Extract the index from an element of `polyBetweenEvalFamily`.
Specialization of `ptoefIndex`.
-/
def pbefIndex {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X} {y : Y}
    (x : polyBetweenEvalFamily X Y P A y) : ccrIndex (P y) :=
  ptoefIndex Y x

/--
Extract the morphism from an element of `polyBetweenEvalFamily`.
Specialization of `ptoefMor`.
-/
def pbefMor {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X} {y : Y}
    (x : polyBetweenEvalFamily X Y P A y) :
    ccrFamily (P y) (pbefIndex x) ⟶ A :=
  ptoefMor Y x

/--
Construct an element of `polyBetweenEvalFamily` from an index and morphism.
Specialization of `ptoefMk`.
-/
def pbefMk {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X} {y : Y}
    (i : ccrIndex (P y)) (f : ccrFamily (P y) i ⟶ A) :
    polyBetweenEvalFamily X Y P A y :=
  ptoefMk Y i f

@[simp]
lemma pbefMk_index {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X}
    {y : Y} (i : ccrIndex (P y)) (f : ccrFamily (P y) i ⟶ A) :
    pbefIndex (pbefMk i f) = i := rfl

@[simp]
lemma pbefMk_mor {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X}
    {y : Y} (i : ccrIndex (P y)) (f : ccrFamily (P y) i ⟶ A) :
    pbefMor (pbefMk i f) = f := rfl

@[simp]
lemma pbefMk_eta {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X}
    {y : Y} (x : polyBetweenEvalFamily X Y P A y) :
    pbefMk (pbefIndex x) (pbefMor x) = x := rfl

/-! #### polyBetweenEval functoriality -/

/--
The action on morphisms for `polyBetweenEvalFamily`.
Specialization of `polyToOverEvalFamilyMap`.
-/
def polyBetweenEvalFamilyMap (P : PolyFunctorBetweenCat X Y) {A B : Over X}
    (f : A ⟶ B) : polyBetweenEvalFamily X Y P A ⟶ polyBetweenEvalFamily X Y P B :=
  polyToOverEvalFamilyMap Y P f

/--
The action on morphisms for `polyBetweenEval`.
Specialization of `polyToOverEvalMap`.
-/
def polyBetweenEvalMap (P : PolyFunctorBetweenCat X Y) {A B : Over X} (f : A ⟶ B) :
    polyBetweenEval X Y P A ⟶ polyBetweenEval X Y P B :=
  polyToOverEvalMap Y P f

@[simp]
lemma polyBetweenEvalMap_left (P : PolyFunctorBetweenCat X Y) {A B : Over X}
    (f : A ⟶ B) (x : (polyBetweenEval X Y P A).left) :
    (polyBetweenEvalMap X Y P f).left x = ⟨x.fst, ccrEvalMap f x.snd⟩ :=
  polyToOverEvalMap_left Y P f x

@[simp]
lemma polyBetweenEvalFamilyMap_id (P : PolyFunctorBetweenCat X Y) (A : Over X) :
    polyBetweenEvalFamilyMap X Y P (𝟙 A) = 𝟙 (polyBetweenEvalFamily X Y P A) :=
  polyToOverEvalFamilyMap_id Y P A

@[simp]
lemma polyBetweenEvalMap_id (P : PolyFunctorBetweenCat X Y) (A : Over X) :
    polyBetweenEvalMap X Y P (𝟙 A) = 𝟙 (polyBetweenEval X Y P A) :=
  polyToOverEvalMap_id Y P A

@[simp]
lemma polyBetweenEvalFamilyMap_comp (P : PolyFunctorBetweenCat X Y)
    {A B C : Over X} (f : A ⟶ B) (g : B ⟶ C) :
    polyBetweenEvalFamilyMap X Y P (f ≫ g) =
      polyBetweenEvalFamilyMap X Y P f ≫ polyBetweenEvalFamilyMap X Y P g :=
  polyToOverEvalFamilyMap_comp Y P f g

@[simp]
lemma polyBetweenEvalMap_comp (P : PolyFunctorBetweenCat X Y)
    {A B C : Over X} (f : A ⟶ B) (g : B ⟶ C) :
    polyBetweenEvalMap X Y P (f ≫ g) =
      polyBetweenEvalMap X Y P f ≫ polyBetweenEvalMap X Y P g :=
  polyToOverEvalMap_comp Y P f g

/--
A polynomial functor `P : PolyFunctorBetweenCat X Y` gives a functor
`Over X ⥤ Over Y`.
Specialization of `polyToOverFunctor`.
-/
def polyBetweenEvalFunctor (P : PolyFunctorBetweenCat X Y) : Over X ⥤ Over Y :=
  polyToOverFunctor Y P

/-! #### polyBetweenEval structure

The `polyBetweenEval P A` object in `Over Y` has:
- `left = Σ y, polyBetweenEvalFamily X Y P A y`
- `hom = Sigma.fst`

Elements of the left component are pairs `⟨y, x⟩` where `x : polyBetweenEvalFamily`.
-/

/--
The left component of `polyBetweenEval` is the sigma type over the family.
-/
lemma polyBetweenEval_left {X Y : Type u} (P : PolyFunctorBetweenCat X Y)
    (A : Over X) :
    (polyBetweenEval X Y P A).left = Σ y, polyBetweenEvalFamily X Y P A y := rfl

/--
The structure map of `polyBetweenEval` is the first projection.
-/
lemma polyBetweenEval_hom {X Y : Type u} (P : PolyFunctorBetweenCat X Y)
    (A : Over X) :
    (polyBetweenEval X Y P A).hom = Sigma.fst := rfl

/--
An element of `(polyBetweenEval P A).left` consists of a `y : Y` and an
element of the fiber at `y`.
-/
def pbeLeft {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X}
    (e : (polyBetweenEval X Y P A).left) : Σ y, polyBetweenEvalFamily X Y P A y :=
  e

/--
Extract the Y-coordinate from an element of `(polyBetweenEval P A).left`.
Specialization of `ptoeLeftY`.
-/
def pbeLeftY {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X}
    (e : (polyBetweenEval X Y P A).left) : Y :=
  ptoeLeftY Y e

/--
Extract the fiber element from an element of `(polyBetweenEval P A).left`.
Specialization of `ptoeLeftFiber`.
-/
def pbeLeftFiber {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X}
    (e : (polyBetweenEval X Y P A).left) :
    polyBetweenEvalFamily X Y P A (pbeLeftY e) :=
  ptoeLeftFiber Y e

/--
Construct an element of `(polyBetweenEval P A).left` from components.
Specialization of `ptoeLeftMk`.
-/
def pbeLeftMk {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X}
    (y : Y) (x : polyBetweenEvalFamily X Y P A y) :
    (polyBetweenEval X Y P A).left :=
  ptoeLeftMk Y y x

@[simp]
lemma pbeLeftMk_y {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X}
    (y : Y) (x : polyBetweenEvalFamily X Y P A y) :
    pbeLeftY (pbeLeftMk y x) = y := rfl

@[simp]
lemma pbeLeftMk_fiber {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X}
    (y : Y) (x : polyBetweenEvalFamily X Y P A y) :
    pbeLeftFiber (pbeLeftMk y x) = x := rfl

@[simp]
lemma pbeLeftMk_eta {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X}
    (e : (polyBetweenEval X Y P A).left) :
    pbeLeftMk (pbeLeftY e) (pbeLeftFiber e) = e := rfl

/--
The structure map applied to a left element gives the Y-coordinate.
-/
@[simp]
lemma polyBetweenEval_hom_pbeLeftMk {X Y : Type u}
    {P : PolyFunctorBetweenCat X Y} {A : Over X}
    (y : Y) (x : polyBetweenEvalFamily X Y P A y) :
    (polyBetweenEval X Y P A).hom (pbeLeftMk y x) = y := rfl

/-! #### Morphisms into polyBetweenEval

When we have a morphism `h : B ⟶ polyBetweenEval X Y P A` in `Over Y`, the
commutativity condition ensures that `h.left b` has Y-coordinate `B.hom b`.
This allows us to extract the fiber element at the appropriate type.
-/

/--
For a morphism into `polyBetweenEval`, the Y-coordinate of the image equals
the structure map of the source.
Specialization of `mor_to_ptoe_y`.
-/
lemma mor_to_pbe_y {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X}
    {B : Over Y} (h : B ⟶ polyBetweenEval X Y P A) (b : B.left) :
    pbeLeftY (h.left b) = B.hom b :=
  mor_to_ptoe_y Y h b

/--
Given a morphism `h : B ⟶ polyBetweenEval X Y P A` and `b : B.left`, we can
extract the fiber element at `B.hom b`. This uses the commutativity condition
to transport from `pbeLeftY (h.left b)` to `B.hom b`.
Specialization of `mor_to_ptoe_fiber`.
-/
def mor_to_pbe_fiber {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X}
    {B : Over Y} (h : B ⟶ polyBetweenEval X Y P A) (b : B.left) :
    polyBetweenEvalFamily X Y P A (B.hom b) :=
  mor_to_ptoe_fiber Y h b

/--
The fiber element from a morphism: extract the index.
Specialization of `mor_to_ptoe_fiber_index`.
-/
def mor_to_pbe_fiber_index {X Y : Type u} {P : PolyFunctorBetweenCat X Y}
    {A : Over X} {B : Over Y} (h : B ⟶ polyBetweenEval X Y P A) (b : B.left) :
    ccrIndex (P (B.hom b)) :=
  mor_to_ptoe_fiber_index Y h b

/--
The fiber element from a morphism: extract the inner morphism.
Specialization of `mor_to_ptoe_fiber_mor`.
-/
def mor_to_pbe_fiber_mor {X Y : Type u} {P : PolyFunctorBetweenCat X Y}
    {A : Over X} {B : Over Y} (h : B ⟶ polyBetweenEval X Y P A) (b : B.left) :
    ccrFamily (P (B.hom b)) (mor_to_pbe_fiber_index h b) ⟶ A :=
  mor_to_ptoe_fiber_mor Y h b

/--
Heterogeneous equality between `mor_to_pbe_fiber` and the raw fiber.
Specialization of `mor_to_ptoe_fiber_heq_raw`.
-/
lemma mor_to_pbe_fiber_heq_raw {X Y : Type u} {P : PolyFunctorBetweenCat X Y}
    {A : Over X} {B : Over Y} (h : B ⟶ polyBetweenEval X Y P A) (b : B.left) :
    mor_to_pbe_fiber h b ≍ pbeLeftFiber (h.left b) :=
  mor_to_ptoe_fiber_heq_raw Y h b

/--
When the morphism `h` is constructed via `Over.homMk` and the fiber function
produces elements with the correct Y-coordinate (i.e., `w` is `funext (fun _ => rfl)`),
`mor_to_pbe_fiber_index` reduces definitionally.
Specialization of `mor_to_ptoe_fiber_index_homMk_rfl`.
-/
lemma mor_to_pbe_fiber_index_homMk_rfl {X Y : Type u} {P : PolyFunctorBetweenCat X Y}
    {A : Over X} {B : Over Y}
    (fn : (b : B.left) → polyBetweenEvalFamily X Y P A (B.hom b))
    (b : B.left) :
    mor_to_pbe_fiber_index
      (Over.homMk (fun b => pbeLeftMk (B.hom b) (fn b))
        (funext (fun _ => rfl))) b = pbefIndex (fn b) :=
  mor_to_ptoe_fiber_index_homMk_rfl Y fn b

/--
The analogous lemma for `mor_to_pbe_fiber_mor`.
Specialization of `mor_to_ptoe_fiber_mor_homMk_rfl`.
-/
lemma mor_to_pbe_fiber_mor_homMk_rfl {X Y : Type u} {P : PolyFunctorBetweenCat X Y}
    {A : Over X} {B : Over Y}
    (fn : (b : B.left) → polyBetweenEvalFamily X Y P A (B.hom b))
    (b : B.left) :
    mor_to_pbe_fiber_mor
      (Over.homMk (fun b => pbeLeftMk (B.hom b) (fn b))
        (funext (fun _ => rfl))) b = pbefMor (fn b) :=
  mor_to_ptoe_fiber_mor_homMk_rfl Y fn b

/-! #### Morphism evaluation

A morphism `α : P ⟶ Q` in `PolyFunctorBetweenCat X Y`
induces a natural transformation between the evaluated
functors `polyBetweenEvalFunctor X Y P` and
`polyBetweenEvalFunctor X Y Q`.
-/

/--
Pointwise evaluation of a polynomial functor morphism
at a fiber. Given `α : P ⟶ Q` and `A : Over X`, at
fiber `y` the map sends `(i, f)` to
`(ccrReindex (α y) i, ccrFiberMor (α y) i ≫ f)`.
-/
def polyBetweenMorphEvalAt
    {P Q : PolyFunctorBetweenCat X Y}
    (α : P ⟶ Q) (A : Over X) (y : Y) :
    polyBetweenEvalFamily X Y P A y →
    polyBetweenEvalFamily X Y Q A y :=
  fun ev => ptoefMk Y
    (ccrReindex (α y) (ptoefIndex Y ev))
    (ccrFiberMor (α y) (ptoefIndex Y ev) ≫
      ptoefMor Y ev)

/--
Evaluation of a polynomial functor morphism. Given
`α : P ⟶ Q` and `A : Over X`, produce a morphism
`(polyBetweenEvalFunctor X Y P).obj A ⟶
  (polyBetweenEvalFunctor X Y Q).obj A`
in `Over Y`.
-/
def polyBetweenMorphEval
    {P Q : PolyFunctorBetweenCat X Y}
    (α : P ⟶ Q) (A : Over X) :
    (polyBetweenEvalFunctor X Y P).obj A ⟶
    (polyBetweenEvalFunctor X Y Q).obj A :=
  (familySliceForward Y).map
    (fun y =>
      polyBetweenMorphEvalAt X Y α A y)

theorem polyBetweenMorphEval_natural
    {P Q : PolyFunctorBetweenCat X Y}
    (α : P ⟶ Q)
    {A B : Over X} (f : A ⟶ B) :
    polyBetweenMorphEval X Y α A ≫
      (polyBetweenEvalFunctor X Y Q).map f =
    (polyBetweenEvalFunctor X Y P).map f ≫
      polyBetweenMorphEval X Y α B := by
  apply Over.OverMorphism.ext
  funext ⟨y, i, g⟩
  dsimp [polyBetweenMorphEval,
    polyBetweenMorphEvalAt,
    polyBetweenEvalFunctor,
    polyToOverFunctor, polyToOverEvalMap,
    familySliceForward, familySliceForwardMap,
    polyToOverEvalFamilyMap,
    ptoefMk, ptoefIndex, ptoefMor,
    ccrEvalMap, ccrEvalMk, ccrEvalIndex,
    ccrEvalMor, Over.comp_left]
  simp only [Category.assoc]

@[simp]
theorem polyBetweenMorphEval_id
    (P : PolyFunctorBetweenCat X Y)
    (A : Over X) :
    polyBetweenMorphEval X Y (𝟙 P) A =
      𝟙 ((polyBetweenEvalFunctor X Y P).obj
        A) := by
  unfold polyBetweenMorphEval
    polyBetweenMorphEvalAt
  exact (familySliceForward Y).map_id _

@[simp]
theorem polyBetweenMorphEval_comp
    {P Q R : PolyFunctorBetweenCat X Y}
    (α : P ⟶ Q) (β : Q ⟶ R) (A : Over X) :
    polyBetweenMorphEval X Y (α ≫ β) A =
      polyBetweenMorphEval X Y α A ≫
        polyBetweenMorphEval X Y β A := by
  unfold polyBetweenMorphEval
  rw [← (familySliceForward Y).map_comp]
  rfl

/--
The evaluation functor from `PolyFunctorBetweenCat X Y`
to the functor category `Over X ⥤ Over Y`.

Maps a polynomial functor `P` to the evaluated functor
`polyBetweenEvalFunctor X Y P`, and a morphism `α : P ⟶ Q`
to the induced natural transformation.
-/
def polyBetweenEvalCatFunctor :
    PolyFunctorBetweenCat X Y ⥤
      (Over X ⥤ Over Y) where
  obj := polyBetweenEvalFunctor X Y
  map α :=
    { app := fun A =>
        polyBetweenMorphEval X Y α A
      naturality := fun _ _ f =>
        (polyBetweenMorphEval_natural
          X Y α f).symm }
  map_id P := by
    apply NatTrans.ext
    funext A
    exact polyBetweenMorphEval_id X Y P A
  map_comp α β := by
    apply NatTrans.ext
    funext A
    exact polyBetweenMorphEval_comp
      X Y α β A

end PolyFunctorBetween

/-! ### Identity Polynomial Functor

The identity polynomial functor `Over X → Over X` at each `x : X` has:
- A single position (indexed by `PUnit`)
- The representable at that position is the fiber over `x`
-/

section PolyBetweenIdentity

variable (X : Type u)

/--
The identity polynomial functor `Over X → Over X`.

At each `x : X`, there is one position with the representable being the
terminal object over `x` (which is `Over.mk (fun _ : PUnit => x)`).
-/
def polyBetweenId : PolyFunctorBetweenCat X X :=
  fun x => ccrObjMk (fun _ : PUnit.{u + 1} => Over.mk (fun _ : PUnit.{u + 1} => x))

/--
The identity has one position at each point.
-/
lemma polyBetweenId_index (x : X) :
    polyBetweenIndex X X (polyBetweenId X) x = PUnit.{u + 1} := rfl

end PolyBetweenIdentity

/-! ### Composition of Polynomial Functors

The composition of `g : PolyFunctorBetweenCat Y Z` and
`f : PolyFunctorBetweenCat X Y` is defined at each `z : Z` by evaluating
`g(z)` at the family of positions from `f`.
-/

section PolyBetweenComposition

variable {X Y Z : Type u}

/--
The position type for the composition of polynomial functors at `z : Z`.

This is equivalent to `ccrEval (g z) (polyBetweenIndexObj X Y f)` (see
`polyBetweenCompIndexEquiv`), but we use the sigma/forall form for
definitional convenience.
-/
def polyBetweenCompIndex (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (z : Z) : Type _ :=
  Σ (ig : ccrIndex (g z)),
    ∀ (e : (ccrFamily (g z) ig).left), ccrIndex (f ((ccrFamily (g z) ig).hom e))

/--
`polyBetweenCompIndex` is the specialization of `polyToOverCompIndex` to `D = Over X`.
-/
lemma polyBetweenCompIndex_eq_polyToOverCompIndex (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (z : Z) :
    polyBetweenCompIndex g f z = polyToOverCompIndex g f z := rfl

/--
The equivalence between `polyBetweenCompIndex` and the `ccrEval` formulation.

The sigma/forall form is isomorphic to `ccrEval (g z) (polyBetweenIndexObj f)`,
where a forall giving indices is equivalent to an `Over.Hom` into the index
object.
-/
def polyBetweenCompIndexEquiv (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (z : Z) :
    polyBetweenCompIndex g f z ≃ ccrEval (g z) (polyBetweenIndexObj X Y f) where
  toFun := fun ⟨ig, pf⟩ =>
    ⟨ig, Over.homMk (fun e => ⟨(ccrFamily (g z) ig).hom e, pf e⟩) rfl⟩
  invFun := fun ⟨ig, mor⟩ => ⟨ig, fun e =>
    have h : (ccrFamily (g z) ig).hom e = (mor.left e).fst :=
      (congrFun (Over.w mor) e).symm
    h ▸ (mor.left e).snd⟩
  left_inv := fun ⟨_, _⟩ => rfl
  right_inv := fun ⟨ig, mor⟩ => by
    simp only [ccrEval]
    congr 1
    apply Over.OverMorphism.ext
    funext e
    have h : (ccrFamily (g z) ig).hom e = (mor.left e).fst :=
      (congrFun (Over.w mor) e).symm
    apply Sigma.ext h
    exact eqRec_heq _ _

/--
The representable for the composition at a given composed position.

At position `(ig, pf)`, the representable is the total space of all
directions in `f` at the positions selected by `pf`.
-/
def polyBetweenCompFamily (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (z : Z)
    (p : polyBetweenCompIndex g f z) : Over X :=
  Over.mk (fun (e : Σ (eg : (ccrFamily (g z) p.1).left),
                      (ccrFamily (f ((ccrFamily (g z) p.1).hom eg)) (p.2 eg)).left) =>
    (ccrFamily (f ((ccrFamily (g z) p.1).hom e.1)) (p.2 e.1)).hom e.2)

/--
`polyBetweenCompFamily` provides the computable construction of the composed
representable for `Over X`. It constructs the sigma type directly rather than
using the categorical coproduct `∐`. This is the explicit form of the coproduct
in `Over X`: the coproduct of `(A_i, h_i)` is `(Σ i, A_i, copairing)`.
-/
lemma polyBetweenCompFamily_is_sigma (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (z : Z) (p : polyBetweenCompIndex g f z) :
    (polyBetweenCompFamily g f z p).left =
    Σ (eg : (ccrFamily (g z) p.1).left),
      (ccrFamily (f ((ccrFamily (g z) p.1).hom eg)) (p.2 eg)).left := rfl

/--
`polyBetweenCompFamily` is the specialization of `polyToOverCompFamily` to
`D = Over X`. This is definitionally true because `CoprodData (Over X)` uses
the same sigma type construction as `polyBetweenCompFamily`.
-/
lemma polyBetweenCompFamily_eq_polyToOverCompFamily (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (z : Z) (p : polyBetweenCompIndex g f z) :
    polyBetweenCompFamily g f z p = polyToOverCompFamily g f z p := rfl

/--
Composition of polynomial functors `Over X → Over Y` and `Over Y → Over Z`.
-/
def polyBetweenComp (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) : PolyFunctorBetweenCat X Z :=
  fun z => ccrObjMk (polyBetweenCompFamily g f z)

/-! #### Composition structure lemmas -/

/--
The index type of the composition at `z`.
-/
lemma polyBetweenComp_index (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (z : Z) :
    ccrIndex (polyBetweenComp g f z) = polyBetweenCompIndex g f z := rfl

/--
The family of the composition at a position.
-/
lemma polyBetweenComp_family (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (z : Z)
    (p : ccrIndex (polyBetweenComp g f z)) :
    ccrFamily (polyBetweenComp g f z) p = polyBetweenCompFamily g f z p := rfl

/--
The left type of the composition family at position `(ig, pf)` is a sigma of
fibers from `g` and fibers from `f`.
-/
lemma polyBetweenCompFamily_left (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (z : Z)
    (ig : ccrIndex (g z))
    (pf : ∀ eg : (ccrFamily (g z) ig).left,
      ccrIndex (f ((ccrFamily (g z) ig).hom eg))) :
    (ccrFamily (polyBetweenComp g f z) ⟨ig, pf⟩).left =
    Σ (eg : (ccrFamily (g z) ig).left),
      (ccrFamily (f ((ccrFamily (g z) ig).hom eg)) (pf eg)).left := rfl

/--
The structure map of the composition family sends `(eg, ef)` to
`(ccrFamily (f y) (pf eg)).hom ef` where `y = (ccrFamily (g z) ig).hom eg`.
-/
lemma polyBetweenCompFamily_hom (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (z : Z)
    (ig : ccrIndex (g z))
    (pf : ∀ eg : (ccrFamily (g z) ig).left,
      ccrIndex (f ((ccrFamily (g z) ig).hom eg)))
    (eg : (ccrFamily (g z) ig).left)
    (ef : (ccrFamily (f ((ccrFamily (g z) ig).hom eg)) (pf eg)).left) :
    (ccrFamily (polyBetweenComp g f z) ⟨ig, pf⟩).hom ⟨eg, ef⟩ =
    (ccrFamily (f ((ccrFamily (g z) ig).hom eg)) (pf eg)).hom ef := rfl

end PolyBetweenComposition

/-! ## Identity Interpretation

We show that evaluating the identity polynomial functor produces a result
equivalent to the input (up to the family-slice equivalence).
-/

section IdentityInterpretation

variable (X : Type u)

/--
The evaluation of the identity polynomial at `A : Over X` produces the same
family as applying the backward direction of the family-slice equivalence.

For each `x : X`, the fiber of `polyBetweenEval (polyBetweenId X) A` at `x`
is equivalent to the fiber of `A` at `x`.
-/
def polyBetweenId_eval_fiberEquiv (A : Over X) (x : X) :
    polyBetweenEvalFamily X X (polyBetweenId X) A x ≃ { a : A.left // A.hom a = x } where
  toFun := fun ⟨_, f⟩ =>
    let mor := f.left PUnit.unit
    ⟨mor, congrFun (Over.w f) PUnit.unit⟩
  invFun := fun ⟨a, ha⟩ =>
    ⟨PUnit.unit, Over.homMk (fun _ => a) (by funext _; exact ha)⟩
  left_inv := fun ⟨i, f⟩ => by
    cases i
    simp only [polyBetweenEvalFamily, polyBetweenId, ccrObjMk, ccrIndex, ccrFamily]
    apply Sigma.ext <;> rfl
  right_inv := fun ⟨a, ha⟩ => rfl

/--
Equivalence between the left component of the identity evaluation and the
original object.
-/
def polyBetweenId_eval_leftEquiv (A : Over X) :
    (polyBetweenEval X X (polyBetweenId X) A).left ≃ A.left where
  toFun := fun ⟨_, ⟨_, f⟩⟩ => f.left PUnit.unit
  invFun := fun a => ⟨A.hom a, ⟨PUnit.unit,
    Over.homMk (fun _ => a) (by funext _; rfl)⟩⟩
  left_inv := fun ⟨x, ⟨i, f⟩⟩ => by
    cases i
    simp only [polyBetweenEval, polyBetweenId, ccrObjMk, ccrIndex, ccrFamily]
    have hw : A.hom (f.left PUnit.unit) = x := congrFun (Over.w f) PUnit.unit
    refine Sigma.ext hw ?_
    simp only
    congr 1
    · funext _; simp only [hw]
    · have hsrc : (Over.mk (Y := PUnit) (fun _ => A.hom (f.left PUnit.unit)) : Over X) =
                  Over.mk (Y := PUnit) (fun _ => x) := by simp only [hw]
      have hfl : f.left = fun _ => f.left PUnit.unit := by funext p; cases p; rfl
      refine heq_of_cast_eq ?_ ?_
      · exact congrArg (fun s => s ⟶ A) hsrc
      · apply Over.OverMorphism.ext
        funext p
        rw [congrFun hfl p]
        rw [GebLean.over_cast_left hsrc]
        simp only [Over.homMk_left]
  right_inv := fun _ => rfl

/--
The evaluation of the identity polynomial at `A : Over X` is isomorphic to `A`
in the slice category `Over X`.
-/
def polyBetweenId_eval_iso (A : Over X) :
    polyBetweenEval X X (polyBetweenId X) A ≅ A :=
  Over.isoMk (polyBetweenId_eval_leftEquiv X A).toIso (by
    funext ⟨x, ⟨_, f⟩⟩
    exact congrFun (Over.w f) PUnit.unit)

end IdentityInterpretation

/-! ## Composition Interpretation

We show that evaluating the composition of polynomial functors is equivalent
to composing their evaluations.
-/

section CompositionInterpretation

variable {X Y Z : Type u}

/--
The fiber of the composition evaluation at `z : Z`.

For `polyBetweenEval (polyBetweenComp g f) A` at `z`, the fiber consists of:
- A position `ig` in `g` at `z`
- For each direction `eg` in the fiber of `g` at `ig`, a position in `f`
- For each pair of directions, a morphism into `A`

We show this is equivalent to the fiber of `polyBetweenEval g (polyBetweenEval f A)`.
-/
def polyBetweenComp_eval_fiberEquiv_toFun (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (A : Over X) (z : Z)
    (x : polyBetweenEvalFamily X Z (polyBetweenComp g f) A z) :
    polyBetweenEvalFamily Y Z g (polyBetweenEval X Y f A) z :=
  let ig := x.1.1
  let pf := x.1.2
  let mor := x.2
  ⟨ig, Over.homMk
    (fun eg => ⟨(ccrFamily (g z) ig).hom eg, ⟨pf eg,
      Over.homMk (fun ef => mor.left ⟨eg, ef⟩) (by
        funext ef
        exact congrFun (Over.w mor) ⟨eg, ef⟩)⟩⟩)
    (by funext eg; rfl)⟩

def polyBetweenComp_eval_fiberEquiv_invFun (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (A : Over X) (z : Z)
    (x : polyBetweenEvalFamily Y Z g (polyBetweenEval X Y f A) z) :
    polyBetweenEvalFamily X Z (polyBetweenComp g f) A z :=
  let ig := pbefIndex x
  let h := pbefMor x
  let pf' : (eg : (ccrFamily (g z) ig).left) →
            ccrIndex (f ((ccrFamily (g z) ig).hom eg)) :=
    fun eg => mor_to_pbe_fiber_index h eg
  ⟨⟨ig, pf'⟩,
   Over.homMk
     (fun ⟨eg, ef⟩ =>
       (mor_to_pbe_fiber_mor h eg).left ef)
     (by
       funext ⟨eg, ef⟩
       exact congrFun (Over.w (mor_to_pbe_fiber_mor h eg)) ef)⟩

def polyBetweenComp_eval_fiberEquiv (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (A : Over X) (z : Z) :
    polyBetweenEvalFamily X Z (polyBetweenComp g f) A z ≃
    polyBetweenEvalFamily Y Z g (polyBetweenEval X Y f A) z where
  toFun := polyBetweenComp_eval_fiberEquiv_toFun g f A z
  invFun := polyBetweenComp_eval_fiberEquiv_invFun g f A z
  left_inv := fun x => by
    obtain ⟨⟨ig, pf⟩, mor⟩ := x
    simp only [polyBetweenComp_eval_fiberEquiv_toFun,
               polyBetweenComp_eval_fiberEquiv_invFun,
               pbefIndex, pbefMor, ptoefIndex, ptoefMor]
    -- The goal reduces to showing the constructed sigma equals the original
    -- The inner `mor_to_pbe_fiber_index` on the constructed `Over.homMk` reduces
    -- because the Y-coordinate proof is `funext (fun _ => rfl)`
    rfl
  right_inv := fun x => by
    obtain ⟨ig, h⟩ := x
    simp only [polyBetweenComp_eval_fiberEquiv_toFun,
               polyBetweenComp_eval_fiberEquiv_invFun,
               pbefIndex, pbefMor, ptoefIndex, ptoefMor,
               ccrEvalIndex, ccrEvalMor]
    congr 1
    apply Over.OverMorphism.ext
    funext eg
    simp only [Over.homMk_left]
    apply Sigma.ext
    · exact (mor_to_pbe_y h eg).symm
    · -- Goal: ⟨mor_to_pbe_fiber_index h eg,
      --         Over.homMk (fun ef ↦ (mor_to_pbe_fiber_mor h eg).left ef) ⋯⟩
      --      ≍ (h.left eg).snd
      -- First show inner_mor = mor_to_pbe_fiber_mor h eg
      have h_inner_eq : Over.homMk
          (fun ef => (mor_to_pbe_fiber_mor h eg).left ef)
          (by funext ef; exact congrFun (Over.w (mor_to_pbe_fiber_mor h eg)) ef) =
          mor_to_pbe_fiber_mor h eg := by
        apply Over.OverMorphism.ext
        rfl
      -- Now LHS = ⟨idx, inner⟩ = ⟨idx, mor⟩ = mor_to_pbe_fiber h eg
      have h_lhs_eq : (⟨mor_to_pbe_fiber_index h eg, mor_to_pbe_fiber_mor h eg⟩ :
              polyBetweenEvalFamily X Y f A ((ccrFamily (g z) ig).hom eg)) =
             mor_to_pbe_fiber h eg := rfl
      -- Use congr_arg to rewrite the inner morphism, then use h_lhs_eq and heq
      simp only
      have h_lhs_rewrite :
          (⟨mor_to_pbe_fiber_index h eg, Over.homMk
              (fun ef => (mor_to_pbe_fiber_mor h eg).left ef)
              (by funext ef; exact congrFun (Over.w (mor_to_pbe_fiber_mor h eg)) ef)⟩ :
              polyBetweenEvalFamily X Y f A ((ccrFamily (g z) ig).hom eg)) =
          ⟨mor_to_pbe_fiber_index h eg, mor_to_pbe_fiber_mor h eg⟩ := by
        simp only [Sigma.mk.injEq, true_and]
        exact heq_of_eq h_inner_eq
      rw [h_lhs_rewrite, h_lhs_eq]
      exact mor_to_pbe_fiber_heq_raw h eg

end CompositionInterpretation

/-! ## Horizontal Category of Polynomial Functors

Polynomial functors `Over X → Over Y` compose via `polyBetweenComp` with
identity `polyBetweenId`. The composition satisfies the category laws up to
isomorphism (not strict equality), because the index types of composed
polynomials are wrapped in `Σ PUnit, PUnit → _` which is isomorphic but not
definitionally equal to the unwrapped type.

We quotient by isomorphism using `Skeleton` to obtain a category
`PolyHorizontalCat` whose objects are types and whose morphisms are
isomorphism classes of polynomial functors.
-/

section PolyHorizontalCategory

variable {X Y Z W : Type u}

/--
At each `y : Y`, the forward base map for the left identity iso sends
`⟨_, pf⟩ : Σ (_ : PUnit), PUnit → ccrIndex (f y)` to `pf PUnit.unit`.
-/
def polyIdLeftFwdBase
    (f : PolyFunctorBetweenCat X Y) (y : Y) :
    ccrIndex (polyBetweenComp (polyBetweenId Y) f y) →
    ccrIndex (f y) :=
  fun ⟨_, pf⟩ => pf PUnit.unit

/--
At each `y : Y`, the forward fiber morphism for the left identity iso
at index `i` sends `a : (ccrFamily (f y) (i.2 PUnit.unit)).left` to
`⟨PUnit.unit, a⟩` in the sigma fiber of the composition.
-/
def polyIdLeftFwdFiber
    (f : PolyFunctorBetweenCat X Y) (y : Y)
    (i : ccrIndex
      (polyBetweenComp (polyBetweenId Y) f y)) :
    ccrFamily (f y) (polyIdLeftFwdBase f y i) ⟶
    ccrFamily
      (polyBetweenComp (polyBetweenId Y) f y) i :=
  Over.homMk (fun a => ⟨PUnit.unit, a⟩) rfl

/--
At each `y : Y`, the backward base map for the left identity iso sends
`i : ccrIndex (f y)` to `⟨PUnit.unit, fun _ => i⟩`.
-/
def polyIdLeftInvBase
    (f : PolyFunctorBetweenCat X Y) (y : Y) :
    ccrIndex (f y) →
    ccrIndex
      (polyBetweenComp (polyBetweenId Y) f y) :=
  fun i => ⟨PUnit.unit, fun _ => i⟩

/--
At each `y : Y`, the backward fiber morphism for the left identity iso
at index `i` projects out the PUnit sigma component.
-/
def polyIdLeftInvFiber
    (f : PolyFunctorBetweenCat X Y) (y : Y)
    (i : ccrIndex (f y)) :
    ccrFamily
      (polyBetweenComp (polyBetweenId Y) f y)
      (polyIdLeftInvBase f y i) ⟶
    ccrFamily (f y) i :=
  Over.homMk (fun ⟨_, a⟩ => a) rfl

/--
Forward morphism for the pointwise left identity iso at `y`.
-/
def polyIdLeftFwd
    (f : PolyFunctorBetweenCat X Y) (y : Y) :
    polyBetweenComp (polyBetweenId Y) f y ⟶ f y :=
  ccrHomMk
    (polyIdLeftFwdBase f y)
    (polyIdLeftFwdFiber f y)

/--
Backward morphism for the pointwise left identity iso at `y`.
-/
def polyIdLeftInv
    (f : PolyFunctorBetweenCat X Y) (y : Y) :
    f y ⟶ polyBetweenComp (polyBetweenId Y) f y :=
  ccrHomMk
    (polyIdLeftInvBase f y)
    (polyIdLeftInvFiber f y)

lemma polyIdLeft_hom_inv
    (f : PolyFunctorBetweenCat X Y) (y : Y) :
    polyIdLeftFwd f y ≫ polyIdLeftInv f y =
      𝟙 (polyBetweenComp (polyBetweenId Y) f y) := by
  ext
  · -- base (pointwise, after ext did funext)
    rename_i a
    obtain ⟨⟨⟩, pf⟩ := a
    dsimp [polyIdLeftFwd, polyIdLeftInv,
      ccrHomMk, polyIdLeftFwdBase,
      polyIdLeftInvBase,
      GrothendieckContra'.comp,
      GrothendieckContra'.id]
    exact Sigma.ext rfl
      (heq_of_eq (funext fun _ => rfl))
  · -- fiber (with eqToHom transport)
    dsimp only [polyIdLeftFwd, polyIdLeftInv,
      ccrHomMk, polyIdLeftFwdFiber,
      polyIdLeftInvFiber,
      GrothendieckContra'.comp,
      GrothendieckContra'.id]
    simp only [eqToHom_refl, Category.comp_id]
    funext ⟨⟨⟩, pf⟩
    dsimp
    apply Over.OverMorphism.ext
    funext ⟨⟨⟩, a⟩
    rfl

lemma polyIdLeft_inv_hom
    (f : PolyFunctorBetweenCat X Y) (y : Y) :
    polyIdLeftInv f y ≫ polyIdLeftFwd f y =
      𝟙 (f y) := rfl

/--
Pointwise isomorphism for left identity at `y`: the composition
`polyBetweenComp (polyBetweenId Y) f` evaluated at `y` is
isomorphic to `f y` in `CoprodCovarRepCat (Over X)`.
-/
def polyIdLeftIsoAt
    (f : PolyFunctorBetweenCat X Y) (y : Y) :
    polyBetweenComp (polyBetweenId Y) f y ≅
      f y where
  hom := polyIdLeftFwd f y
  inv := polyIdLeftInv f y
  hom_inv_id := polyIdLeft_hom_inv f y
  inv_hom_id := polyIdLeft_inv_hom f y

/--
Left identity isomorphism: composing with the identity
polynomial on the left yields an isomorphic polynomial.
-/
def polyBetweenComp_id_left_iso
    (f : PolyFunctorBetweenCat X Y) :
    polyBetweenComp (polyBetweenId Y) f ≅ f :=
  Pi.isoMk (fun y => polyIdLeftIsoAt f y)

/-! #### Right identity isomorphism -/

def polyIdRightFwdBase
    (g : PolyFunctorBetweenCat X Y) (y : Y) :
    ccrIndex
      (polyBetweenComp g (polyBetweenId X) y) →
    ccrIndex (g y) :=
  fun ⟨ig, _⟩ => ig

def polyIdRightFwdFiber
    (g : PolyFunctorBetweenCat X Y) (y : Y)
    (i : ccrIndex
      (polyBetweenComp g (polyBetweenId X) y)) :
    ccrFamily (g y) (polyIdRightFwdBase g y i) ⟶
    ccrFamily
      (polyBetweenComp g (polyBetweenId X) y) i :=
  Over.homMk (fun eg => ⟨eg, PUnit.unit⟩) rfl

def polyIdRightInvBase
    (g : PolyFunctorBetweenCat X Y) (y : Y) :
    ccrIndex (g y) →
    ccrIndex
      (polyBetweenComp g (polyBetweenId X) y) :=
  fun ig => ⟨ig, fun _ => PUnit.unit⟩

def polyIdRightInvFiber
    (g : PolyFunctorBetweenCat X Y) (y : Y)
    (j : ccrIndex (g y)) :
    ccrFamily
      (polyBetweenComp g (polyBetweenId X) y)
      (polyIdRightInvBase g y j) ⟶
    ccrFamily (g y) j :=
  Over.homMk (fun ⟨eg, _⟩ => eg) rfl

def polyIdRightFwd
    (g : PolyFunctorBetweenCat X Y) (y : Y) :
    polyBetweenComp g (polyBetweenId X) y ⟶
      g y :=
  ccrHomMk (polyIdRightFwdBase g y)
    (polyIdRightFwdFiber g y)

def polyIdRightInv
    (g : PolyFunctorBetweenCat X Y) (y : Y) :
    g y ⟶
      polyBetweenComp g (polyBetweenId X) y :=
  ccrHomMk (polyIdRightInvBase g y)
    (polyIdRightInvFiber g y)

lemma polyIdRight_hom_inv
    (g : PolyFunctorBetweenCat X Y) (y : Y) :
    polyIdRightFwd g y ≫ polyIdRightInv g y =
      𝟙 (polyBetweenComp g
        (polyBetweenId X) y) := by
  ext
  · rename_i a
    obtain ⟨ig, pf⟩ := a
    dsimp [polyIdRightFwd, polyIdRightInv,
      ccrHomMk, polyIdRightFwdBase,
      polyIdRightInvBase,
      GrothendieckContra'.comp,
      GrothendieckContra'.id]
    exact Sigma.ext rfl (heq_of_eq
      (funext fun x => by
        cases pf x; rfl))
  · dsimp only [polyIdRightFwd, polyIdRightInv,
      ccrHomMk, polyIdRightFwdFiber,
      polyIdRightInvFiber,
      GrothendieckContra'.comp,
      GrothendieckContra'.id]
    simp only [eqToHom_refl, Category.comp_id]
    funext ⟨ig, pf⟩
    dsimp
    apply Over.OverMorphism.ext
    funext ⟨eg, ⟨⟩⟩
    rfl

lemma polyIdRight_inv_hom
    (g : PolyFunctorBetweenCat X Y) (y : Y) :
    polyIdRightInv g y ≫ polyIdRightFwd g y =
      𝟙 (g y) := rfl

def polyIdRightIsoAt
    (g : PolyFunctorBetweenCat X Y) (y : Y) :
    polyBetweenComp g (polyBetweenId X) y ≅
      g y where
  hom := polyIdRightFwd g y
  inv := polyIdRightInv g y
  hom_inv_id := polyIdRight_hom_inv g y
  inv_hom_id := polyIdRight_inv_hom g y

def polyBetweenComp_id_right_iso
    (g : PolyFunctorBetweenCat X Y) :
    polyBetweenComp g (polyBetweenId X) ≅ g :=
  Pi.isoMk (fun y => polyIdRightIsoAt g y)

/-! #### Associativity isomorphism -/

variable {W : Type u}

/--
Forward base map for associativity: reassociates the
nested sigma/forall from `(h ∘ g) ∘ f` to `h ∘ (g ∘ f)`.
-/
def polyAssocFwdBase
    (h : PolyFunctorBetweenCat Z W)
    (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (w : W) :
    ccrIndex (polyBetweenComp
      (polyBetweenComp h g) f w) →
    ccrIndex (polyBetweenComp
      h (polyBetweenComp g f) w) :=
  fun ⟨⟨ih, pg⟩, pf⟩ =>
    ⟨ih, fun eh => ⟨pg eh, fun eg => pf ⟨eh, eg⟩⟩⟩

/--
Backward base map for associativity: reassociates from
`h ∘ (g ∘ f)` to `(h ∘ g) ∘ f`.
-/
def polyAssocInvBase
    (h : PolyFunctorBetweenCat Z W)
    (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (w : W) :
    ccrIndex (polyBetweenComp
      h (polyBetweenComp g f) w) →
    ccrIndex (polyBetweenComp
      (polyBetweenComp h g) f w) :=
  fun ⟨ih, pgf⟩ =>
    ⟨⟨ih, fun eh => (pgf eh).1⟩,
     fun ⟨eh, eg⟩ => (pgf eh).2 eg⟩

def polyAssocFwdFiber
    (h : PolyFunctorBetweenCat Z W)
    (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (w : W)
    (i : ccrIndex (polyBetweenComp
      (polyBetweenComp h g) f w)) :
    ccrFamily (polyBetweenComp
      h (polyBetweenComp g f) w)
      (polyAssocFwdBase h g f w i) ⟶
    ccrFamily (polyBetweenComp
      (polyBetweenComp h g) f w) i :=
  Over.homMk (fun ⟨eh, ⟨eg, ef⟩⟩ =>
    ⟨⟨eh, eg⟩, ef⟩) rfl

def polyAssocInvFiber
    (h : PolyFunctorBetweenCat Z W)
    (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (w : W)
    (j : ccrIndex (polyBetweenComp
      h (polyBetweenComp g f) w)) :
    ccrFamily (polyBetweenComp
      (polyBetweenComp h g) f w)
      (polyAssocInvBase h g f w j) ⟶
    ccrFamily (polyBetweenComp
      h (polyBetweenComp g f) w) j :=
  Over.homMk (fun ⟨⟨eh, eg⟩, ef⟩ =>
    ⟨eh, ⟨eg, ef⟩⟩) rfl

def polyAssocFwd
    (h : PolyFunctorBetweenCat Z W)
    (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (w : W) :
    polyBetweenComp (polyBetweenComp h g) f w ⟶
    polyBetweenComp h (polyBetweenComp g f) w :=
  ccrHomMk (polyAssocFwdBase h g f w)
    (polyAssocFwdFiber h g f w)

def polyAssocInv
    (h : PolyFunctorBetweenCat Z W)
    (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (w : W) :
    polyBetweenComp h (polyBetweenComp g f) w ⟶
    polyBetweenComp (polyBetweenComp h g) f w :=
  ccrHomMk (polyAssocInvBase h g f w)
    (polyAssocInvFiber h g f w)

lemma polyAssoc_hom_inv
    (h : PolyFunctorBetweenCat Z W)
    (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (w : W) :
    polyAssocFwd h g f w ≫
      polyAssocInv h g f w =
    𝟙 (polyBetweenComp
      (polyBetweenComp h g) f w) := rfl

lemma polyAssoc_inv_hom
    (h : PolyFunctorBetweenCat Z W)
    (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (w : W) :
    polyAssocInv h g f w ≫
      polyAssocFwd h g f w =
    𝟙 (polyBetweenComp
      h (polyBetweenComp g f) w) := rfl

def polyAssocIsoAt
    (h : PolyFunctorBetweenCat Z W)
    (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (w : W) :
    polyBetweenComp (polyBetweenComp h g) f w ≅
    polyBetweenComp h (polyBetweenComp g f) w
    where
  hom := polyAssocFwd h g f w
  inv := polyAssocInv h g f w
  hom_inv_id := polyAssoc_hom_inv h g f w
  inv_hom_id := polyAssoc_inv_hom h g f w

def polyBetweenComp_assoc_iso
    (h : PolyFunctorBetweenCat Z W)
    (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) :
    polyBetweenComp (polyBetweenComp h g) f ≅
    polyBetweenComp h (polyBetweenComp g f) :=
  Pi.isoMk (fun w => polyAssocIsoAt h g f w)

/-! #### Composition as a functor in the outer
    polynomial -/

/--
Transport lemma: when `h : y₁ = y₂`, the fiber
left-types at `h.symm ▸ idx` and `idx` are equal.
Used for the dependent type transport in the
composition functor's fiber map.
-/
private def overWTransportLeft
    (f : PolyFunctorBetweenCat X Y)
    {y₁ y₂ : Y}
    (h : y₁ = y₂)
    (idx : ccrIndex (f y₁)) :
    (ccrFamily (f y₂)
      (h.symm ▸ idx)).left =
    (ccrFamily (f y₁) idx).left :=
  @Eq.rec Y y₁
    (fun y (h' : y₁ = y) =>
      (ccrFamily (f y)
        (h'.symm ▸ idx)).left =
      (ccrFamily (f y₁) idx).left)
    rfl y₂ h

private lemma overWTransportHom
    (f : PolyFunctorBetweenCat X Y)
    {y₁ y₂ : Y}
    (h : y₁ = y₂)
    (idx : ccrIndex (f y₁))
    (ef : (ccrFamily (f y₂)
      (h.symm ▸ idx)).left) :
    (ccrFamily (f y₁) idx).hom
      (cast (overWTransportLeft f h idx)
        ef) =
    (ccrFamily (f y₂)
      (h.symm ▸ idx)).hom ef :=
  @Eq.rec Y y₁
    (fun y (h' : y₁ = y) =>
      ∀ (ef' : (ccrFamily (f y)
        (h'.symm ▸ idx)).left),
      (ccrFamily (f y₁) idx).hom
        (cast (overWTransportLeft f h' idx)
          ef') =
      (ccrFamily (f y)
        (h'.symm ▸ idx)).hom ef')
    (fun _ => rfl) y₂ h ef

/--
The `.left` component of a composed fiber morphism
equals the composition of the `.left` components.
-/
lemma ccrComp_fiberMor_left
    {P Q R : CoprodCovarRepCat (Over Y)}
    (φ : P ⟶ Q) (ψ : Q ⟶ R)
    (i : ccrIndex P)
    (e : (ccrFamily R
      (ccrReindex (φ ≫ ψ) i)).left) :
    (ccrFiberMor (φ ≫ ψ) i).left e =
    (ccrFiberMor φ i).left
      ((ccrFiberMor ψ
        (ccrReindex φ i)).left e) :=
  congrFun (congrArg (·.left)
    (ccrComp_fiberMor φ ψ i)) e

def polyCompGObj
    (f : PolyFunctorBetweenCat X Y)
    (G : CoprodCovarRepCat (Over Y)) :
    CoprodCovarRepCat (Over X) :=
  ccrObjMk
    (fun (p : Σ (ig : ccrIndex G),
      ∀ (e : (ccrFamily G ig).left),
        ccrIndex
          (f ((ccrFamily G ig).hom e))) =>
    Over.mk (fun (e : Σ (eg :
        (ccrFamily G p.1).left),
      (ccrFamily
        (f ((ccrFamily G p.1).hom eg))
        (p.2 eg)).left) =>
    (ccrFamily
      (f ((ccrFamily G p.1).hom e.1))
      (p.2 e.1)).hom e.2))

def polyCompGMap
    (f : PolyFunctorBetweenCat X Y)
    {G₁ G₂ : CoprodCovarRepCat (Over Y)}
    (φ : G₁ ⟶ G₂) :
    polyCompGObj f G₁ ⟶ polyCompGObj f G₂ :=
  ccrHomMk
    (fun ⟨ig, pf⟩ =>
      let ψ := ccrFiberMor φ ig
      let h := fun e₂ =>
        congrFun (Over.w ψ) e₂
      ⟨ccrReindex φ ig,
       fun e₂ => (h e₂).symm ▸
         pf (ψ.left e₂)⟩)
    (fun ⟨ig, pf⟩ =>
      let ψ := ccrFiberMor φ ig
      let h := fun e₂ =>
        congrFun (Over.w ψ) e₂
      Over.homMk
        (fun ⟨e₂, ef⟩ =>
          ⟨ψ.left e₂,
           cast (overWTransportLeft f
             (h e₂) (pf (ψ.left e₂))) ef⟩)
        (by
          funext ⟨e₂, ef⟩
          exact (overWTransportHom f (h e₂)
            (pf (ψ.left e₂)) ef)))

lemma polyCompGMap_id
    (f : PolyFunctorBetweenCat X Y)
    (G : CoprodCovarRepCat (Over Y)) :
    polyCompGMap f (𝟙 G) =
      𝟙 (polyCompGObj f G) := rfl

/--
If two `GrothendieckContra'.Hom` values have equal
`.base` and the `.rec`-cast of one `.fiber` equals
the other, then the `.fiber` values are `HEq`.
-/
private lemma GrothendieckContra'.ext_fiber_heq
    {C : Type*} [Category C] {F' : Cᵒᵖ' ⥤ Cat}
    {X Y : GrothendieckContra' F'}
    {f g : GrothendieckContra'.Hom X Y}
    (hb : f.base = g.base)
    (hf : hb.rec f.fiber = g.fiber) :
    HEq f.fiber g.fiber := by
  cases f; cases g; dsimp at hb
  subst hb; exact heq_of_eq hf

/--
For `GrothendieckContra'.Hom`, two morphisms are
equal if their bases are equal and fibers are HEq.
-/
private lemma GrothendieckContra'.ext_of_heq
    {C : Type*} [Category C] {F' : Cᵒᵖ' ⥤ Cat}
    {X Y : GrothendieckContra' F'}
    (f g : GrothendieckContra'.Hom X Y)
    (hb : f.base = g.base)
    (hf : HEq f.fiber g.fiber) :
    f = g := by
  cases f; cases g; dsimp at hb
  subst hb; exact congrArg _ (eq_of_heq hf)

/--
For a dependent function `pf : ∀ e, M (g e)`, if
`x₁ = x₂` then any `▸`-transports of `pf x₁` and
`pf x₂` to a common target type are equal,
regardless of the transport paths used (single-step
vs multi-step).
-/
private lemma dep_fun_transport_eq
    {T : Type*} {Y : Type*} {g : T → Y}
    {M : Y → Type*}
    (pf : ∀ e : T, M (g e))
    {x₁ x₂ : T} (hx : x₁ = x₂)
    {y₂ y₃ : Y}
    (h_single : g x₁ = y₃)
    (h_inner : g x₂ = y₂)
    (h_outer : y₂ = y₃) :
    (h_single ▸ pf x₁ : M y₃) =
    h_outer ▸ h_inner ▸ pf x₂ := by
  subst hx; subst h_inner; subst h_outer
  rfl

private lemma polyCompGMap_comp_base_inner
    (f : PolyFunctorBetweenCat X Y)
    {G₁ G₂ G₃ : CoprodCovarRepCat (Over Y)}
    (φ : G₁ ⟶ G₂) (ψ : G₂ ⟶ G₃)
    (ig : ccrIndex G₁)
    (pf : ∀ e : (ccrFamily G₁ ig).left,
      ccrIndex (f ((ccrFamily G₁ ig).hom e)))
    (e₃ : (ccrFamily G₃
      (ccrReindex (φ ≫ ψ) ig)).left) :
    ((polyCompGMap f (φ ≫ ψ)).base
      ⟨ig, pf⟩).2 e₃ =
    ((polyCompGMap f ψ).base
      ((polyCompGMap f φ).base
        ⟨ig, pf⟩)).2 e₃ := by
  dsimp only [polyCompGMap, ccrHomMk]
  exact dep_fun_transport_eq
    (M := fun y => ccrIndex (f y)) pf
    (ccrComp_fiberMor_left φ ψ ig e₃)
    _ _ _

lemma polyCompGMap_comp_base
    (f : PolyFunctorBetweenCat X Y)
    {G₁ G₂ G₃ : CoprodCovarRepCat (Over Y)}
    (φ : G₁ ⟶ G₂) (ψ : G₂ ⟶ G₃) :
    (polyCompGMap f (φ ≫ ψ)).base =
    (polyCompGMap f φ ≫
      polyCompGMap f ψ).base := by
  change (polyCompGMap f (φ ≫ ψ)).base =
    (polyCompGMap f ψ).base ∘
      (polyCompGMap f φ).base
  funext ⟨ig, pf⟩
  dsimp only [Function.comp, polyCompGMap,
    ccrHomMk]
  exact Sigma.ext rfl (heq_of_eq
    (funext fun e₂ =>
      polyCompGMap_comp_base_inner
        f φ ψ ig pf e₂))

/--
To show `h ▸ x = y` where `h : α = β`, `x : C α`,
`y : C β`, it suffices to show `HEq x y`.
-/
private lemma eq_rec_of_heq
    {α : Sort*} {C : α → Sort*}
    {a b : α} (h : a = b)
    {x : C a} {y : C b}
    (hxy : HEq x y) :
    h ▸ x = y := by
  subst h; exact eq_of_heq hxy

/--
In `Over X`, `(f ≫ g).left x = g.left (f.left x)`.
-/
private lemma over_comp_left_apply
    {X : Type*} {A B C : Over X}
    (f : A ⟶ B) (g : B ⟶ C)
    (x : A.left) :
    (f ≫ g).left x = g.left (f.left x) :=
  rfl

/--
The base value of `polyCompGMap f (φ ≫ ψ)` at
index `⟨ig, pf⟩`.
-/
private abbrev compBaseAt
    (f : PolyFunctorBetweenCat X Y)
    {G₁ G₂ G₃ : CoprodCovarRepCat (Over Y)}
    (φ : G₁ ⟶ G₂) (ψ : G₂ ⟶ G₃)
    (ig : ccrIndex G₁)
    (pf : ∀ e : (ccrFamily G₁ ig).left,
      ccrIndex
        (f ((ccrFamily G₁ ig).hom e))) :
    ccrIndex (polyCompGObj f G₃) :=
  (polyCompGMap f (φ ≫ ψ)).base ⟨ig, pf⟩

/--
The base value of the sequential composition
`polyCompGMap f φ ≫ polyCompGMap f ψ` at index
`⟨ig, pf⟩`.
-/
private abbrev seqBaseAt
    (f : PolyFunctorBetweenCat X Y)
    {G₁ G₂ G₃ : CoprodCovarRepCat (Over Y)}
    (φ : G₁ ⟶ G₂) (ψ : G₂ ⟶ G₃)
    (ig : ccrIndex G₁)
    (pf : ∀ e : (ccrFamily G₁ ig).left,
      ccrIndex
        (f ((ccrFamily G₁ ig).hom e))) :
    ccrIndex (polyCompGObj f G₃) :=
  (polyCompGMap f φ ≫
    polyCompGMap f ψ).base ⟨ig, pf⟩

/--
The pointwise base equality at `⟨ig, pf⟩`.
-/
private lemma baseAtEq
    (f : PolyFunctorBetweenCat X Y)
    {G₁ G₂ G₃ : CoprodCovarRepCat (Over Y)}
    (φ : G₁ ⟶ G₂) (ψ : G₂ ⟶ G₃)
    (ig : ccrIndex G₁)
    (pf : ∀ e : (ccrFamily G₁ ig).left,
      ccrIndex
        (f ((ccrFamily G₁ ig).hom e))) :
    compBaseAt f φ ψ ig pf =
      seqBaseAt f φ ψ ig pf :=
  congrFun
    (polyCompGMap_comp_base f φ ψ)
    ⟨ig, pf⟩

private abbrev fiberLeftAt
    (f : PolyFunctorBetweenCat X Y)
    (G₃ : CoprodCovarRepCat (Over Y))
    (p : ccrIndex (polyCompGObj f G₃)) :
    Type u :=
  (ccrFamily (polyCompGObj f G₃) p).left

private lemma fiberLeftCastEq
    (f : PolyFunctorBetweenCat X Y)
    {G₁ G₂ G₃ : CoprodCovarRepCat (Over Y)}
    (φ : G₁ ⟶ G₂) (ψ : G₂ ⟶ G₃)
    (ig : ccrIndex G₁)
    (pf : ∀ e : (ccrFamily G₁ ig).left,
      ccrIndex
        (f ((ccrFamily G₁ ig).hom e))) :
    fiberLeftAt f G₃
      (compBaseAt f φ ψ ig pf) =
    fiberLeftAt f G₃
      (seqBaseAt f φ ψ ig pf) :=
  congrArg (fiberLeftAt f G₃)
    (baseAtEq f φ ψ ig pf)

/--
The outer element type of the composite fiber
sigma at a given base index.
-/
private abbrev fiberOuterAt
    (f : PolyFunctorBetweenCat X Y)
    (G₃ : CoprodCovarRepCat (Over Y))
    (p : ccrIndex (polyCompGObj f G₃)) :
    Type u :=
  (ccrFamily G₃ p.fst).left

/--
The inner element type of the composite fiber
sigma at a given outer element.
-/
private abbrev fiberInnerAt
    (f : PolyFunctorBetweenCat X Y)
    (G₃ : CoprodCovarRepCat (Over Y))
    (p : ccrIndex (polyCompGObj f G₃))
    (eg : fiberOuterAt f G₃ p) :
    Type u :=
  (ccrFamily
    (f ((ccrFamily G₃ p.fst).hom eg))
    (p.snd eg)).left

/--
The result element type (in the domain fiber).
-/
private abbrev domFiberLeftAt
    (f : PolyFunctorBetweenCat X Y)
    (G₁ : CoprodCovarRepCat (Over Y))
    (ig : ccrIndex G₁)
    (pf : ∀ e : (ccrFamily G₁ ig).left,
      ccrIndex
        (f ((ccrFamily G₁ ig).hom e))) :
    Type u :=
  (ccrFamily (polyCompGObj f G₁)
    ⟨ig, pf⟩).left

/--
The LHS sigma element: apply `ccrFiberMor (φ ≫ ψ)`
to the cast of `⟨e₃, ef⟩`. This is what the
composed fiber morphism produces.
-/
private abbrev compFiberResult
    (f : PolyFunctorBetweenCat X Y)
    {G₁ G₂ G₃ : CoprodCovarRepCat (Over Y)}
    (φ : G₁ ⟶ G₂) (ψ : G₂ ⟶ G₃)
    (ig : ccrIndex G₁)
    (pf : ∀ e : (ccrFamily G₁ ig).left,
      ccrIndex
        (f ((ccrFamily G₁ ig).hom e)))
    (e₃ : fiberOuterAt f G₃
      (seqBaseAt f φ ψ ig pf))
    (ef : fiberInnerAt f G₃
      (seqBaseAt f φ ψ ig pf) e₃) :
    domFiberLeftAt f G₁ ig pf :=
  (ccrFiberMor (polyCompGMap f (φ ≫ ψ))
    ⟨ig, pf⟩).left
    ((eqToHom (show
      ccrFamily (polyCompGObj f G₃)
        ((polyCompGMap f φ ≫
          polyCompGMap f ψ).base
          ⟨ig, pf⟩) =
      ccrFamily (polyCompGObj f G₃)
        ((polyCompGMap f (φ ≫ ψ)).base
          ⟨ig, pf⟩)
      by rw [polyCompGMap_comp_base])).left
      ⟨e₃, ef⟩)

/--
The RHS sigma element: apply sequential
`ccrFiberMor` to `⟨e₃, ef⟩`.
-/
private abbrev seqFiberResult
    (f : PolyFunctorBetweenCat X Y)
    {G₁ G₂ G₃ : CoprodCovarRepCat (Over Y)}
    (φ : G₁ ⟶ G₂) (ψ : G₂ ⟶ G₃)
    (ig : ccrIndex G₁)
    (pf : ∀ e : (ccrFamily G₁ ig).left,
      ccrIndex
        (f ((ccrFamily G₁ ig).hom e)))
    (e₃ : fiberOuterAt f G₃
      (seqBaseAt f φ ψ ig pf))
    (ef : fiberInnerAt f G₃
      (seqBaseAt f φ ψ ig pf) e₃) :
    domFiberLeftAt f G₁ ig pf :=
  (ccrFiberMor (polyCompGMap f φ)
    ⟨ig, pf⟩).left
    ((ccrFiberMor (polyCompGMap f ψ)
      ((polyCompGMap f φ).base
        ⟨ig, pf⟩)).left ⟨e₃, ef⟩)

private lemma polyCompGMap_comp_cast_elim
    (f : PolyFunctorBetweenCat X Y)
    {G₁ G₂ G₃ : CoprodCovarRepCat (Over Y)}
    (φ : G₁ ⟶ G₂) (ψ : G₂ ⟶ G₃)
    (ig : ccrIndex G₁)
    (pf : ∀ e : (ccrFamily G₁ ig).left,
      ccrIndex
        (f ((ccrFamily G₁ ig).hom e)))
    (e₃ : fiberOuterAt f G₃
      (seqBaseAt f φ ψ ig pf))
    (ef : fiberInnerAt f G₃
      (seqBaseAt f φ ψ ig pf) e₃) :
    (ccrFiberMor (polyCompGMap f (φ ≫ ψ))
      ⟨ig, pf⟩).left
      (cast (fiberLeftCastEq
        f φ ψ ig pf).symm
        ⟨e₃, ef⟩) =
    (ccrFiberMor (polyCompGMap f φ)
      ⟨ig, pf⟩).left
      ((ccrFiberMor (polyCompGMap f ψ)
        ((polyCompGMap f φ).base
          ⟨ig, pf⟩)).left ⟨e₃, ef⟩) := by
  -- The cast goes between two sigma types with
  -- the same outer type (since compBaseAt.fst =
  -- seqBaseAt.fst definitionally) but different
  -- inner families (because .snd differs).
  -- The cast direction is .symm: from seq to comp.
  -- We decompose using cast_sigma_eq'.
  have h := baseAtEq f φ ψ ig pf
  have h_snd : HEq
    (compBaseAt f φ ψ ig pf).snd
    (seqBaseAt f φ ψ ig pf).snd :=
    (Sigma.ext_iff.mp h).2
  have h_snd_eq := eq_of_heq h_snd
  -- The inner family equality (seq → comp direction)
  have hFG : (fun eg =>
    (ccrFamily
      (f ((ccrFamily G₃
        (seqBaseAt f φ ψ ig pf).fst).hom eg))
      ((seqBaseAt f φ ψ ig pf).snd eg)).left) =
    (fun eg =>
    (ccrFamily
      (f ((ccrFamily G₃
        (compBaseAt f φ ψ ig pf).fst).hom eg))
      ((compBaseAt f φ ψ ig pf).snd eg)).left) :=
    funext fun eg => congrArg (fun s =>
      (ccrFamily
        (f ((ccrFamily G₃
          (seqBaseAt f φ ψ ig pf).fst).hom eg))
        (s eg)).left) h_snd_eq.symm
  -- Decompose the outer cast
  dsimp only [polyCompGMap, ccrHomMk,
    ccrFiberMor, ccrReindex,
    fiberLeftCastEq, fiberLeftAt,
    compBaseAt, seqBaseAt]
  -- Use the sigma cast decomposition
  rw [cast_sigma_eq' _ hFG e₃ ef]
  -- Now the goal has ⟨e₃, cast ... ef⟩ on the
  -- LHS and the sequential application on the RHS.
  -- Both produce sigma pairs.
  apply Sigma.ext
  · -- fst: composition of .left functions
    rfl
  · -- snd: cast compositions
    refine heq_of_eq ?_
    simp only [Over.homMk_left]
    -- Goal: cast ⋯ (cast ⋯ ef) = cast ⋯ (cast ⋯ ef)
    -- Both are double-casts with different proofs.
    -- Collapse each to a single cast, then they
    -- are equal by proof irrelevance.
    simp only [cast_cast]

private lemma polyCompGMap_comp_cast_step
    (f : PolyFunctorBetweenCat X Y)
    {G₁ G₂ G₃ : CoprodCovarRepCat (Over Y)}
    (φ : G₁ ⟶ G₂) (ψ : G₂ ⟶ G₃)
    (ig : ccrIndex G₁)
    (pf : ∀ e : (ccrFamily G₁ ig).left,
      ccrIndex
        (f ((ccrFamily G₁ ig).hom e)))
    (e₃ : fiberOuterAt f G₃
      (seqBaseAt f φ ψ ig pf))
    (ef : fiberInnerAt f G₃
      (seqBaseAt f φ ψ ig pf) e₃) :
    compFiberResult f φ ψ ig pf e₃ ef =
    seqFiberResult f φ ψ ig pf e₃ ef := by
  dsimp only [compFiberResult,
    seqFiberResult]
  rw [Over.eqToHom_left,
    types_eqToHom_eq_cast]
  -- Goal:
  -- (ccrFiberMor (polyCompGMap f (φ ≫ ψ))
  --   ⟨ig, pf⟩).left (cast ⋯ ⟨e₃, ef⟩) =
  -- (ccrFiberMor (polyCompGMap f φ)
  --   ⟨ig, pf⟩).left
  --   ((ccrFiberMor (polyCompGMap f ψ)
  --     ...).left ⟨e₃, ef⟩)
  --
  -- Factor: eliminate the cast on ⟨e₃, ef⟩.
  exact polyCompGMap_comp_cast_elim
    f φ ψ ig pf e₃ ef

private lemma polyCompGMap_comp_fiber_at_elem
    (f : PolyFunctorBetweenCat X Y)
    {G₁ G₂ G₃ : CoprodCovarRepCat (Over Y)}
    (φ : G₁ ⟶ G₂) (ψ : G₂ ⟶ G₃)
    (ig : ccrIndex G₁)
    (pf : ∀ e : (ccrFamily G₁ ig).left,
      ccrIndex
        (f ((ccrFamily G₁ ig).hom e)))
    (e₃ : (ccrFamily G₃
      ((polyCompGMap f φ ≫
        polyCompGMap f ψ).base
        ⟨ig, pf⟩).fst).left)
    (ef : (ccrFamily
      (f ((ccrFamily G₃
        ((polyCompGMap f φ ≫
          polyCompGMap f ψ).base
          ⟨ig, pf⟩).fst).hom e₃))
      (((polyCompGMap f φ ≫
        polyCompGMap f ψ).base
        ⟨ig, pf⟩).snd e₃)).left) :
    (ccrFiberMor
      (polyCompGMap f (φ ≫ ψ)) ⟨ig, pf⟩).left
      ((eqToHom (show
        ccrFamily (polyCompGObj f G₃)
          ((polyCompGMap f φ ≫
            polyCompGMap f ψ).base
            ⟨ig, pf⟩) =
        ccrFamily (polyCompGObj f G₃)
          ((polyCompGMap f (φ ≫ ψ)).base
            ⟨ig, pf⟩)
        by rw [polyCompGMap_comp_base])).left
        ⟨e₃, ef⟩) =
    (ccrFiberMor (polyCompGMap f φ)
      ⟨ig, pf⟩).left
      ((ccrFiberMor (polyCompGMap f ψ)
        ((polyCompGMap f φ).base
          ⟨ig, pf⟩)).left
        ⟨e₃, ef⟩) := by
  exact polyCompGMap_comp_cast_step
    f φ ψ ig pf e₃ ef

private lemma polyCompGMap_comp_fiber_at
    (f : PolyFunctorBetweenCat X Y)
    {G₁ G₂ G₃ : CoprodCovarRepCat (Over Y)}
    (φ : G₁ ⟶ G₂) (ψ : G₂ ⟶ G₃)
    (ig : ccrIndex G₁)
    (pf : ∀ e : (ccrFamily G₁ ig).left,
      ccrIndex
        (f ((ccrFamily G₁ ig).hom e))) :
    eqToHom (show
      ccrFamily (polyCompGObj f G₃)
        ((polyCompGMap f φ ≫
          polyCompGMap f ψ).base
          ⟨ig, pf⟩) =
      ccrFamily (polyCompGObj f G₃)
        ((polyCompGMap f (φ ≫ ψ)).base
          ⟨ig, pf⟩)
      by rw [polyCompGMap_comp_base]) ≫
    ccrFiberMor
      (polyCompGMap f (φ ≫ ψ)) ⟨ig, pf⟩ =
    ccrFiberMor (polyCompGMap f φ ≫
      polyCompGMap f ψ) ⟨ig, pf⟩ := by
  rw [ccrComp_fiberMor]
  apply Over.OverMorphism.ext
  funext ⟨e₃, ef⟩
  rw [over_comp_left_apply,
    over_comp_left_apply]
  exact polyCompGMap_comp_fiber_at_elem
    f φ ψ ig pf e₃ ef

lemma polyCompGMap_comp
    (f : PolyFunctorBetweenCat X Y)
    {G₁ G₂ G₃ : CoprodCovarRepCat (Over Y)}
    (φ : G₁ ⟶ G₂) (ψ : G₂ ⟶ G₃) :
    polyCompGMap f (φ ≫ ψ) =
    polyCompGMap f φ ≫
      polyCompGMap f ψ :=
  GrothendieckContra'.ext _ _
    (polyCompGMap_comp_base f φ ψ) (by
    funext ⟨ig, pf⟩
    rw [piOp'_fiber_comp_eqToHom_at_idx]
    dsimp only [ccrFiberMor]
    exact polyCompGMap_comp_fiber_at
      f φ ψ ig pf)

/--
Composition of polynomial functors, viewed as a
functor in the outer polynomial `G`.
-/
def polyCompGFunctor
    (f : PolyFunctorBetweenCat X Y) :
    CoprodCovarRepCat (Over Y) ⥤
      CoprodCovarRepCat (Over X) where
  obj := polyCompGObj f
  map := polyCompGMap f
  map_id := polyCompGMap_id f
  map_comp := polyCompGMap_comp f

/--
Forward morphism for `polyCompGObj` functoriality
in the inner polynomial `f`: at each fiber point,
apply `αf.hom` to reindex and transport.
-/
private def polyCompGObj_isoHom
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂)
    (G : CoprodCovarRepCat (Over Y)) :
    polyCompGObj f₁ G ⟶ polyCompGObj f₂ G :=
  ccrHomMk
    (fun ⟨ig, pf⟩ =>
      ⟨ig, fun e =>
        ccrReindex (αf.hom
          ((ccrFamily G ig).hom e))
          (pf e)⟩)
    (fun ⟨ig, pf⟩ =>
      Over.homMk
        (fun ⟨e, ef⟩ =>
          ⟨e, (ccrFiberMor (αf.hom
            ((ccrFamily G ig).hom e))
            (pf e)).left ef⟩)
        (by
          funext ⟨e, ef⟩
          exact congrFun (Over.w
            (ccrFiberMor (αf.hom
              ((ccrFamily G ig).hom e))
              (pf e))) ef))

/--
Backward morphism for `polyCompGObj` functoriality
in the inner polynomial `f`: at each fiber point,
apply `αf.inv` to reindex and transport.
-/
private def polyCompGObj_isoInv
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂)
    (G : CoprodCovarRepCat (Over Y)) :
    polyCompGObj f₂ G ⟶ polyCompGObj f₁ G :=
  ccrHomMk
    (fun ⟨ig, pf⟩ =>
      ⟨ig, fun e =>
        ccrReindex (αf.inv
          ((ccrFamily G ig).hom e))
          (pf e)⟩)
    (fun ⟨ig, pf⟩ =>
      Over.homMk
        (fun ⟨e, ef⟩ =>
          ⟨e, (ccrFiberMor (αf.inv
            ((ccrFamily G ig).hom e))
            (pf e)).left ef⟩)
        (by
          funext ⟨e, ef⟩
          exact congrFun (Over.w
            (ccrFiberMor (αf.inv
              ((ccrFamily G ig).hom e))
              (pf e))) ef))

/--
Reindex roundtrip: applying `αf.hom` then `αf.inv`
at the same fiber point recovers the original index.
-/
private lemma ccrReindex_hom_inv_cancel
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂) (y : Y)
    (i : ccrIndex (f₁ y)) :
    ccrReindex (αf.inv y)
      (ccrReindex (αf.hom y) i) = i := by
  have h : αf.hom y ≫ αf.inv y = 𝟙 (f₁ y) :=
    congrFun αf.hom_inv_id y
  have := congrFun (show ccrReindex (αf.hom y ≫
      αf.inv y) = ccrReindex (𝟙 (f₁ y))
    from congrArg ccrReindex h) i
  rwa [ccrComp_reindex, ccrId_reindex] at this

/--
Reindex roundtrip: applying `αf.inv` then `αf.hom`
at the same fiber point recovers the original index.
-/
private lemma ccrReindex_inv_hom_cancel
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂) (y : Y)
    (i : ccrIndex (f₂ y)) :
    ccrReindex (αf.hom y)
      (ccrReindex (αf.inv y) i) = i := by
  have h : αf.inv y ≫ αf.hom y = 𝟙 (f₂ y) :=
    congrFun αf.inv_hom_id y
  have := congrFun (show ccrReindex (αf.inv y ≫
      αf.hom y) = ccrReindex (𝟙 (f₂ y))
    from congrArg ccrReindex h) i
  rwa [ccrComp_reindex, ccrId_reindex] at this

/--
Fiber-level roundtrip: the fiber morphism of the
composed inner morphism `αf.hom y ≫ αf.inv y` at
index `i` is HEq to that of the identity.
-/
private lemma ccrFiberMor_hom_inv_cancel
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂) (y : Y)
    (i : ccrIndex (f₁ y)) :
    HEq (ccrFiberMor (αf.hom y ≫ αf.inv y) i)
         (ccrFiberMor (𝟙 (f₁ y)) i) :=
  congr_arg_heq (fun f => ccrFiberMor f i)
    (congrFun αf.hom_inv_id y)

/--
Fiber-level roundtrip: the fiber morphism of the
composed inner morphism `αf.inv y ≫ αf.hom y` at
index `i` is HEq to that of the identity.
-/
private lemma ccrFiberMor_inv_hom_cancel
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂) (y : Y)
    (i : ccrIndex (f₂ y)) :
    HEq (ccrFiberMor (αf.inv y ≫ αf.hom y) i)
         (ccrFiberMor (𝟙 (f₂ y)) i) :=
  congr_arg_heq (fun f => ccrFiberMor f i)
    (congrFun αf.inv_hom_id y)

/--
The composed fiber morphism from the `hom ≫ inv` roundtrip
equals `eqToHom` of the reindexing roundtrip equality.
-/
private lemma polyComp_fiberMor_roundtrip
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂) (y : Y)
    (i : ccrIndex (f₁ y)) :
    ccrFiberMor (αf.inv y)
      (ccrReindex (αf.hom y) i) ≫
    ccrFiberMor (αf.hom y) i =
    eqToHom (congrArg (ccrFamily (f₁ y))
      (ccrReindex_hom_inv_cancel αf y i)) := by
  rw [← ccrComp_fiberMor]
  have heq : HEq (ccrFiberMor (αf.hom y ≫
      αf.inv y) i) (𝟙 (ccrFamily (f₁ y) i)) :=
    (ccrFiberMor_hom_inv_cancel αf y i).trans
      (heq_of_eq (ccrId_fiberMor _ i))
  rw [eq_of_heq_eqToHom heq, Category.comp_id]

/--
The composed fiber morphism from the `inv ≫ hom` roundtrip
equals `eqToHom` of the reindexing roundtrip equality.
-/
private lemma polyComp_fiberMor_roundtrip_inv
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂) (y : Y)
    (i : ccrIndex (f₂ y)) :
    ccrFiberMor (αf.hom y)
      (ccrReindex (αf.inv y) i) ≫
    ccrFiberMor (αf.inv y) i =
    eqToHom (congrArg (ccrFamily (f₂ y))
      (ccrReindex_inv_hom_cancel αf y i)) := by
  rw [← ccrComp_fiberMor]
  have heq : HEq (ccrFiberMor (αf.inv y ≫
      αf.hom y) i) (𝟙 (ccrFamily (f₂ y) i)) :=
    (ccrFiberMor_inv_hom_cancel αf y i).trans
      (heq_of_eq (ccrId_fiberMor _ i))
  rw [eq_of_heq_eqToHom heq, Category.comp_id]

/--
The composition of the two fiber `Over.homMk` morphisms
from `polyCompGObj_isoInv` and `polyCompGObj_isoHom`
equals `eqToHom` (no leading transport).
-/
private lemma polyComp_homMk_inv_hom
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂)
    (G : CoprodCovarRepCat (Over Y))
    (ig : ccrIndex G)
    (pf : (e : (ccrFamily G ig).left) →
      ccrIndex
        (f₁ ((ccrFamily G ig).hom e))) :
    ∀ (h : _ = _),
    (polyCompGObj_isoInv αf G).fiber
      ((polyCompGObj_isoHom αf G).base
        ⟨ig, pf⟩) ≫
    (polyCompGObj_isoHom αf G).fiber
      ⟨ig, pf⟩ =
    eqToHom h := by
  intro h
  dsimp only [polyCompGObj_isoHom,
    polyCompGObj_isoInv, ccrHomMk]
  ext ⟨e, ef⟩
  simp only [Over.comp_left, Over.homMk_left,
    types_comp_apply]
  have rt := polyComp_fiberMor_roundtrip αf
    ((ccrFamily G ig).hom e) (pf e)
  have rt_left : ((ccrFiberMor
      (αf.inv ((ccrFamily G ig).hom e))
      (ccrReindex
        (αf.hom ((ccrFamily G ig).hom e))
        (pf e))).left ≫
    (ccrFiberMor
      (αf.hom ((ccrFamily G ig).hom e))
      (pf e)).left) ef =
    (eqToHom
      (congrArg
        (ccrFamily (f₁ ((ccrFamily G ig).hom e)))
        (ccrReindex_hom_inv_cancel αf
          ((ccrFamily G ig).hom e)
          (pf e)))).left ef := by
    rw [← Over.comp_left, rt]
  simp only [types_comp_apply] at rt_left
  rw [rt_left, Over.eqToHom_left,
    types_eqToHom_eq_cast, Over.eqToHom_left,
    types_eqToHom_eq_cast]
  symm
  exact cast_sigma_eq' _ (funext fun e =>
    congrArg (fun i =>
      (ccrFamily
        (f₁ ((ccrFamily G ig).hom e)) i).left)
      (ccrReindex_hom_inv_cancel αf
        ((ccrFamily G ig).hom e) (pf e))) e ef

/--
Base component of the forward-then-backward roundtrip:
the composed base map is the identity base map.
-/
private lemma polyCompGObj_iso_hom_inv_base
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂)
    (G : CoprodCovarRepCat (Over Y)) :
    (polyCompGObj_isoHom αf G ≫
      polyCompGObj_isoInv αf G).base =
    (GrothendieckContra'.id (polyCompGObj f₁ G)).base := by
  dsimp [polyCompGObj_isoHom, polyCompGObj_isoInv, ccrHomMk,
    GrothendieckContra'.comp, GrothendieckContra'.id]
  funext ⟨ig, pf⟩
  exact Sigma.ext rfl (heq_of_eq
    (funext fun e => ccrReindex_hom_inv_cancel αf _ _))

/--
Per-index fiber equality for the `hom ≫ inv` roundtrip: at each
index, the composed fiber morphism preceded by its `eqToHom`
transport equals the identity fiber morphism.
-/
private lemma polyComp_hom_inv_at_idx
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂)
    (G : CoprodCovarRepCat (Over Y))
    (idx : ccrIndex (polyCompGObj f₁ G)) :
    ∀ (h : _ = _),
    eqToHom h ≫
      (polyCompGObj_isoInv αf G).fiber
        ((polyCompGObj_isoHom αf G).base
          idx) ≫
      (polyCompGObj_isoHom αf G).fiber
        idx =
    (GrothendieckContra'.id
      (polyCompGObj f₁ G)).fiber idx := by
  intro h
  let ⟨ig, pf⟩ := idx
  rw [polyComp_homMk_inv_hom αf G ig pf,
    eqToHom_trans,
    GrothendieckContra'.id_fiber_val,
    eqToHom_catOp_pi_at_idx]
  simp [polyCompGObj_isoHom,
    polyCompGObj_isoInv, ccrHomMk,
    ccrReindex_hom_inv_cancel]

/--
The composition of the two fiber `Over.homMk` morphisms
from `polyCompGObj_isoHom` and `polyCompGObj_isoInv`
equals `eqToHom` (no leading transport).
-/
private lemma polyComp_homMk_hom_inv
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂)
    (G : CoprodCovarRepCat (Over Y))
    (ig : ccrIndex G)
    (pf : (e : (ccrFamily G ig).left) →
      ccrIndex
        (f₂ ((ccrFamily G ig).hom e))) :
    ∀ (h : _ = _),
    (polyCompGObj_isoHom αf G).fiber
      ((polyCompGObj_isoInv αf G).base
        ⟨ig, pf⟩) ≫
    (polyCompGObj_isoInv αf G).fiber
      ⟨ig, pf⟩ =
    eqToHom h := by
  intro h
  dsimp only [polyCompGObj_isoHom,
    polyCompGObj_isoInv, ccrHomMk]
  ext ⟨e, ef⟩
  simp only [Over.comp_left, Over.homMk_left,
    types_comp_apply]
  have rt := polyComp_fiberMor_roundtrip_inv αf
    ((ccrFamily G ig).hom e) (pf e)
  have rt_left : ((ccrFiberMor
      (αf.hom ((ccrFamily G ig).hom e))
      (ccrReindex
        (αf.inv ((ccrFamily G ig).hom e))
        (pf e))).left ≫
    (ccrFiberMor
      (αf.inv ((ccrFamily G ig).hom e))
      (pf e)).left) ef =
    (eqToHom
      (congrArg
        (ccrFamily
          (f₂ ((ccrFamily G ig).hom e)))
        (ccrReindex_inv_hom_cancel αf
          ((ccrFamily G ig).hom e)
          (pf e)))).left ef := by
    rw [← Over.comp_left, rt]
  simp only [types_comp_apply] at rt_left
  rw [rt_left, Over.eqToHom_left,
    types_eqToHom_eq_cast, Over.eqToHom_left,
    types_eqToHom_eq_cast]
  symm
  exact cast_sigma_eq' _ (funext fun e =>
    congrArg (fun i =>
      (ccrFamily
        (f₂ ((ccrFamily G ig).hom e)) i).left)
      (ccrReindex_inv_hom_cancel αf
        ((ccrFamily G ig).hom e) (pf e))) e ef

/--
Base component of the backward-then-forward roundtrip:
the composed base map is the identity base map.
-/
private lemma polyCompGObj_iso_inv_hom_base
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂)
    (G : CoprodCovarRepCat (Over Y)) :
    (polyCompGObj_isoInv αf G ≫
      polyCompGObj_isoHom αf G).base =
    (GrothendieckContra'.id
      (polyCompGObj f₂ G)).base := by
  dsimp [polyCompGObj_isoHom,
    polyCompGObj_isoInv, ccrHomMk,
    GrothendieckContra'.comp,
    GrothendieckContra'.id]
  funext ⟨ig, pf⟩
  exact Sigma.ext rfl (heq_of_eq
    (funext fun e =>
      ccrReindex_inv_hom_cancel αf _ _))

/--
Per-index fiber equality for the `inv ≫ hom` roundtrip.
-/
private lemma polyComp_inv_hom_at_idx
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂)
    (G : CoprodCovarRepCat (Over Y))
    (idx : ccrIndex (polyCompGObj f₂ G)) :
    ∀ (h : _ = _),
    eqToHom h ≫
      (polyCompGObj_isoHom αf G).fiber
        ((polyCompGObj_isoInv αf G).base
          idx) ≫
      (polyCompGObj_isoInv αf G).fiber
        idx =
    (GrothendieckContra'.id
      (polyCompGObj f₂ G)).fiber idx := by
  intro h
  let ⟨ig, pf⟩ := idx
  rw [polyComp_homMk_hom_inv αf G ig pf,
    eqToHom_trans,
    GrothendieckContra'.id_fiber_val,
    eqToHom_catOp_pi_at_idx]
  simp [polyCompGObj_isoHom,
    polyCompGObj_isoInv, ccrHomMk,
    ccrReindex_inv_hom_cancel]

/--
Transported fiber equality for the forward-then-backward roundtrip:
transporting the composed fiber along the base equality gives
the identity fiber.
-/
private lemma polyCompGObj_iso_hom_inv_fiber_cond
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂)
    (G : CoprodCovarRepCat (Over Y)) :
    (polyCompGObj_isoHom αf G ≫
      polyCompGObj_isoInv αf G).fiber ≫
    eqToHom (congrArg
      (fun b => ((familyFunctor (Over X) ⋙
        Cat.opFunctor').map b).toFunctor.obj
          (polyCompGObj f₁ G).fiber)
      (polyCompGObj_iso_hom_inv_base αf G)) =
    (GrothendieckContra'.id
      (polyCompGObj f₁ G)).fiber := by
  funext ⟨ig, pf⟩
  rw [piOp'_fiber_comp_eqToHom_at_idx]
  simp only [CategoryOp'.eq_1,
    familyFunctor.eq_1,
    FamilyCat.eq_1, Cat.of_α, familyMap.eq_1,
    Cat.opFunctor'.eq_1, Functor.op'.eq_1,
    functorOp'Obj.eq_1, Functor.comp_obj,
    Functor.comp_map,
    Functor.toCatHom_toFunctor,
    GrothendieckContra'.id_base,
    types_id_apply, CoprodCovarRepCat.eq_1,
    GrothendieckContra'.cat_comp_base,
    types_comp_apply,
    GrothendieckContra'.cat_comp_fiber,
    eqToHom_refl, Category.comp_id]
  rw [show
    ((polyCompGObj_isoHom αf G).fiber ≫
      fun x =>
        (polyCompGObj_isoInv αf G).fiber
          ((polyCompGObj_isoHom αf G).base x))
      ⟨ig, pf⟩ =
    ((fun x =>
        (polyCompGObj_isoInv αf G).fiber
          ((polyCompGObj_isoHom αf G).base x))
        ⟨ig, pf⟩ ≫
      (polyCompGObj_isoHom αf G).fiber
        ⟨ig, pf⟩)
    from piOp'_comp_at_idx _ _ _]
  exact polyComp_hom_inv_at_idx αf G
    ⟨ig, pf⟩ _

/--
Fiber component of the forward-then-backward roundtrip:
the composed fiber NatTrans is HEq to the identity fiber NatTrans.
-/
private lemma polyCompGObj_iso_hom_inv_fiber
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂)
    (G : CoprodCovarRepCat (Over Y)) :
    HEq (polyCompGObj_isoHom αf G ≫
           polyCompGObj_isoInv αf G).fiber
         (GrothendieckContra'.id
           (polyCompGObj f₁ G)).fiber := by
  have h := polyCompGObj_iso_hom_inv_fiber_cond αf G
  -- h : (hom ≫ inv).fiber ≫ eqToHom _ = (𝟙 x).fiber
  -- This is exactly the fiber condition for ext.
  -- We can derive HEq from it via heq_iff_comp_eqToHom:
  rw [heq_iff_comp_eqToHom]
  convert h using 1

/--
Transported fiber equality for the backward-then-forward roundtrip:
transporting the composed fiber along the base equality gives
the identity fiber.
-/
private lemma polyCompGObj_iso_inv_hom_fiber_cond
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂)
    (G : CoprodCovarRepCat (Over Y)) :
    (polyCompGObj_isoInv αf G ≫
      polyCompGObj_isoHom αf G).fiber ≫
    eqToHom (congrArg
      (fun b => ((familyFunctor (Over X) ⋙
        Cat.opFunctor').map b).toFunctor.obj
          (polyCompGObj f₂ G).fiber)
      (polyCompGObj_iso_inv_hom_base αf G)) =
    (GrothendieckContra'.id
      (polyCompGObj f₂ G)).fiber := by
  funext ⟨ig, pf⟩
  rw [piOp'_fiber_comp_eqToHom_at_idx]
  simp only [CategoryOp'.eq_1,
    familyFunctor.eq_1,
    FamilyCat.eq_1, Cat.of_α, familyMap.eq_1,
    Cat.opFunctor'.eq_1, Functor.op'.eq_1,
    functorOp'Obj.eq_1, Functor.comp_obj,
    Functor.comp_map,
    Functor.toCatHom_toFunctor,
    GrothendieckContra'.id_base,
    types_id_apply, CoprodCovarRepCat.eq_1,
    GrothendieckContra'.cat_comp_base,
    types_comp_apply,
    GrothendieckContra'.cat_comp_fiber,
    eqToHom_refl, Category.comp_id]
  rw [show
    ((polyCompGObj_isoInv αf G).fiber ≫
      fun x =>
        (polyCompGObj_isoHom αf G).fiber
          ((polyCompGObj_isoInv αf G).base x))
      ⟨ig, pf⟩ =
    ((fun x =>
        (polyCompGObj_isoHom αf G).fiber
          ((polyCompGObj_isoInv αf G).base x))
        ⟨ig, pf⟩ ≫
      (polyCompGObj_isoInv αf G).fiber
        ⟨ig, pf⟩)
    from piOp'_comp_at_idx _ _ _]
  exact polyComp_inv_hom_at_idx αf G
    ⟨ig, pf⟩ _

/--
Fiber component of the backward-then-forward roundtrip:
the composed fiber NatTrans is HEq to the identity fiber NatTrans.
-/
private lemma polyCompGObj_iso_inv_hom_fiber
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂)
    (G : CoprodCovarRepCat (Over Y)) :
    HEq (polyCompGObj_isoInv αf G ≫
           polyCompGObj_isoHom αf G).fiber
         (GrothendieckContra'.id
           (polyCompGObj f₂ G)).fiber := by
  have h := polyCompGObj_iso_inv_hom_fiber_cond αf G
  rw [heq_iff_comp_eqToHom]
  convert h using 1

/--
The forward-then-backward roundtrip is the identity.
-/
private lemma polyCompGObj_iso_hom_inv
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂)
    (G : CoprodCovarRepCat (Over Y)) :
    polyCompGObj_isoHom αf G ≫
      polyCompGObj_isoInv αf G =
    𝟙 (polyCompGObj f₁ G) :=
  GrothendieckContra'.ext_of_heq _ _
    (polyCompGObj_iso_hom_inv_base αf G)
    (polyCompGObj_iso_hom_inv_fiber αf G)

/--
The backward-then-forward roundtrip is the identity.
-/
private lemma polyCompGObj_iso_inv_hom
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    (αf : f₁ ≅ f₂)
    (G : CoprodCovarRepCat (Over Y)) :
    polyCompGObj_isoInv αf G ≫
      polyCompGObj_isoHom αf G =
    𝟙 (polyCompGObj f₂ G) :=
  GrothendieckContra'.ext_of_heq _ _
    (polyCompGObj_iso_inv_hom_base αf G)
    (polyCompGObj_iso_inv_hom_fiber αf G)

private lemma polyBetweenComp_nonempty_iso
    {f₁ f₂ : PolyFunctorBetweenCat X Y}
    {g₁ g₂ : PolyFunctorBetweenCat Y Z}
    (αf : f₁ ≅ f₂) (αg : g₁ ≅ g₂) :
    Nonempty (polyBetweenComp g₁ f₁ ≅
      polyBetweenComp g₂ f₂) := by
  -- polyBetweenComp g f z = polyCompGObj f (g z)
  -- Factor: vary f with g₁ fixed, then vary g
  -- with f₂ fixed.
  have hg : ∀ z, polyCompGObj f₂ (g₁ z) ≅
      polyCompGObj f₂ (g₂ z) :=
    fun z =>
      (polyCompGFunctor f₂).mapIso
        ⟨αg.hom z, αg.inv z,
         congrFun αg.hom_inv_id z,
         congrFun αg.inv_hom_id z⟩
  have hf_iso : ∀ G, polyCompGObj f₁ G ≅
      polyCompGObj f₂ G :=
    fun G =>
      ⟨polyCompGObj_isoHom αf G,
       polyCompGObj_isoInv αf G,
       polyCompGObj_iso_hom_inv αf G,
       polyCompGObj_iso_inv_hom αf G⟩
  exact ⟨⟨fun z => ((hf_iso (g₁ z)).trans
      (hg z)).hom,
    fun z => ((hf_iso (g₁ z)).trans
      (hg z)).inv,
    funext fun z => ((hf_iso (g₁ z)).trans
      (hg z)).hom_inv_id,
    funext fun z => ((hf_iso (g₁ z)).trans
      (hg z)).inv_hom_id⟩⟩

/-! #### Quotient-level operations -/

/--
Morphisms in the horizontal category: isomorphism
classes of polynomial functors `Over X → Over Y`.
-/
abbrev PolyHorizontalHom (X Y : Type u) :=
  Skeleton
    (↑(PolyFunctorBetweenCat X Y))

def polyHorizId (X : Type u) :
    PolyHorizontalHom X X :=
  toSkeleton
    (↑(PolyFunctorBetweenCat X X))
    (polyBetweenId X)

def polyHorizComp :
    PolyHorizontalHom X Y →
    PolyHorizontalHom Y Z →
    PolyHorizontalHom X Z :=
  Skeleton.lift₂
    (fun f g =>
      toSkeleton _ (polyBetweenComp g f))
    (fun _ _ _ _ ⟨αf⟩ ⟨αg⟩ =>
      toSkeleton_eq_iff.mpr
        (polyBetweenComp_nonempty_iso αf αg))

theorem polyHorizComp_id_left
    (f : PolyHorizontalHom X Y) :
    polyHorizComp (polyHorizId X) f = f := by
  induction f using Quotient.inductionOn with
  | h f' =>
    exact toSkeleton_eq_iff.mpr
      ⟨polyBetweenComp_id_right_iso f'⟩

theorem polyHorizComp_id_right
    (g : PolyHorizontalHom X Y) :
    polyHorizComp g (polyHorizId Y) = g := by
  induction g using Quotient.inductionOn with
  | h g' =>
    exact toSkeleton_eq_iff.mpr
      ⟨polyBetweenComp_id_left_iso g'⟩

theorem polyHorizComp_assoc
    (f : PolyHorizontalHom X Y)
    (g : PolyHorizontalHom Y Z)
    (h : PolyHorizontalHom Z W) :
    polyHorizComp (polyHorizComp f g) h =
      polyHorizComp f (polyHorizComp g h) := by
  induction f using Quotient.inductionOn with
  | h f' =>
  induction g using Quotient.inductionOn with
  | h g' =>
  induction h using Quotient.inductionOn with
  | h h' =>
    exact toSkeleton_eq_iff.mpr
      ⟨(polyBetweenComp_assoc_iso h' g' f').symm⟩

/-! #### Category instance -/

@[ext]
structure PolyHorizontalCat where
  obj : Type u

instance : Category.{max u (u + 1)}
    PolyHorizontalCat.{u} where
  Hom X Y := PolyHorizontalHom X.obj Y.obj
  id X := polyHorizId X.obj
  comp f g := polyHorizComp f g
  id_comp := polyHorizComp_id_left
  comp_id := polyHorizComp_id_right
  assoc := polyHorizComp_assoc

end PolyHorizontalCategory

/-! ## W-Type Diagrams

A polynomial functor `Over X → Over Y` can alternatively be represented by a
W-type diagram `X ← E → B → Y`, which consists of:
- A type `B` (the base)
- A family `E : B → Type` (the fibers, giving `E → B`)
- A map `s : E → X` (the source map, making each `E(b)` an object over `X`)
- A map `t : B → Y` (the target map)

The polynomial functor is then:
`A ↦ Σ_{b : B} Π_{e : E(b)} Hom_{Over X}(s(e), A)` (composed with `t`)
-/

section WTypeDiagramDefs

variable (X Y : Type u)

/--
A W-type diagram from `X` to `Y` consists of a span `X ← E → B` together with
a map `B → Y`. This represents a polynomial functor `Over X → Over Y`.

Concretely:
- `B` is the base type (positions/shapes)
- `p : E → B` is the projection (arities/fiber structure)
- `s : E → X` is the source map (each position comes from `Over X`)
- `t : B → Y` is the target map (each position goes to `Over Y`)
-/
structure WTypeDiagram where
  /-- The base type (positions/shapes) -/
  B : Type u
  /-- The total space of fibers (arities) -/
  E : Type u
  /-- The projection from E to B -/
  p : E → B
  /-- The source map: each fiber element comes from a point over X -/
  s : E → X
  /-- The target map: each position maps to Y -/
  t : B → Y

/--
The fiber of a W-type diagram at a base point.
-/
def WTypeDiagram.fiber (W : WTypeDiagram X Y) (b : W.B) : Type u :=
  { e : W.E // W.p e = b }

/--
The source map restricted to a fiber, giving an object of `Over X`.
-/
def WTypeDiagram.fiberOver (W : WTypeDiagram X Y) (b : W.B) : Over X :=
  Over.mk (fun (x : WTypeDiagram.fiber X Y W b) => W.s x.val)

/--
Convert a W-type diagram to a polynomial functor (as an object of
`CoprodCovarRepCat (Over X)`).
-/
def WTypeDiagram.toPolyFunctor (W : WTypeDiagram X Y) : PolyFunctorCat X :=
  ccrObjMk W.fiberOver

/--
Evaluate a W-type diagram at an object of `Over X`, producing a family over `Y`.
For `A : Over X` and `W : WTypeDiagram X Y`, this computes:
`y ↦ Σ_{b : t⁻¹(y)} Π_{e : p⁻¹(b)} Hom_{Over X}(fiberOver(b), A)`
-/
def WTypeDiagram.evalFamily (W : WTypeDiagram X Y) (A : Over X) : Y → Type u :=
  fun y => Σ (b : { b : W.B // W.t b = y }),
    (WTypeDiagram.fiberOver X Y W b.val ⟶ A)

/--
Evaluate a W-type diagram at an object of `Over X`, producing an object of `Over Y`.
This uses the Family-Slice equivalence.
-/
def WTypeDiagram.eval (W : WTypeDiagram X Y) (A : Over X) : Over Y :=
  (familySliceForward Y).obj (W.evalFamily X Y A)

/--
The action on morphisms for `WTypeDiagram.evalFamily`.
Given `f : A ⟶ B`, produces a fiber-wise map.
-/
def WTypeDiagram.evalFamilyMap (W : WTypeDiagram X Y) {A B : Over X} (f : A ⟶ B) :
    W.evalFamily X Y A ⟶ W.evalFamily X Y B :=
  fun _ ⟨b, h⟩ => ⟨b, h ≫ f⟩

/--
The action on morphisms for `WTypeDiagram.eval`.
Given `f : A ⟶ B`, produces a morphism in `Over Y`.
-/
def WTypeDiagram.evalMap (W : WTypeDiagram X Y) {A B : Over X} (f : A ⟶ B) :
    W.eval X Y A ⟶ W.eval X Y B :=
  (familySliceForward Y).map (W.evalFamilyMap X Y f)

@[simp]
lemma WTypeDiagram.evalMap_left (W : WTypeDiagram X Y) {A B : Over X}
    (f : A ⟶ B) (x : (W.eval X Y A).left) :
    (W.evalMap X Y f).left x = ⟨x.fst, ⟨x.snd.fst, x.snd.snd ≫ f⟩⟩ := rfl

@[simp]
lemma WTypeDiagram.evalFamilyMap_id (W : WTypeDiagram X Y) (A : Over X) :
    W.evalFamilyMap X Y (𝟙 A) = 𝟙 (W.evalFamily X Y A) := by
  funext _ ⟨b, h⟩
  simp only [evalFamilyMap, Category.comp_id]
  rfl

@[simp]
lemma WTypeDiagram.evalMap_id (W : WTypeDiagram X Y) (A : Over X) :
    W.evalMap X Y (𝟙 A) = 𝟙 (W.eval X Y A) := by
  simp only [evalMap, evalFamilyMap_id, CategoryTheory.Functor.map_id]
  rfl

@[simp]
lemma WTypeDiagram.evalFamilyMap_comp (W : WTypeDiagram X Y)
    {A B C : Over X} (f : A ⟶ B) (g : B ⟶ C) :
    W.evalFamilyMap X Y (f ≫ g) =
      W.evalFamilyMap X Y f ≫ W.evalFamilyMap X Y g := by
  funext _ ⟨b, h⟩
  simp only [evalFamilyMap]
  rfl

@[simp]
lemma WTypeDiagram.evalMap_comp (W : WTypeDiagram X Y)
    {A B C : Over X} (f : A ⟶ B) (g : B ⟶ C) :
    W.evalMap X Y (f ≫ g) = W.evalMap X Y f ≫ W.evalMap X Y g := by
  simp only [evalMap, evalFamilyMap_comp, CategoryTheory.Functor.map_comp]

/--
A W-type diagram `W : WTypeDiagram X Y` gives a functor `Over X ⥤ Over Y`.
-/
def WTypeDiagram.evalFunctor (W : WTypeDiagram X Y) : Over X ⥤ Over Y where
  obj := W.eval X Y
  map := W.evalMap X Y
  map_id := fun A => W.evalMap_id X Y A
  map_comp := fun f g => W.evalMap_comp X Y f g

/--
Construct a W-type diagram from a polynomial functor and a target map.
Given `P : PolyFunctorCat X` with index type `I` and a map `t : I → Y`,
we get a W-type diagram.
-/
def polyFunctorToWType (P : PolyFunctorCat X) (t : ccrIndex P → Y) :
    WTypeDiagram X Y where
  B := ccrIndex P
  E := Σ i : ccrIndex P, (ccrFamily P i).left
  p := Sigma.fst
  s := fun ⟨i, e⟩ => (ccrFamily P i).hom e
  t := t

/--
The fiber of a polynomial-to-W-type diagram at index `i` is the domain of the
`i`-th representable.
-/
lemma polyFunctorToWType_fiber (P : PolyFunctorCat X) (t : ccrIndex P → Y)
    (i : ccrIndex P) :
    WTypeDiagram.fiber X Y (polyFunctorToWType X Y P t) i =
      { x : Σ j : ccrIndex P, (ccrFamily P j).left // x.1 = i } := rfl

end WTypeDiagramDefs

/-! ## W-type Identity and Composition

For W-type diagrams, we define identity and composition operations.
-/

section WTypeIdentityComposition

variable (X : Type u)

/--
The identity W-type diagram for `Over X → Over X`.

- `B = X` (positions are points of `X`)
- `E = X` (arities/directions are also points of `X`)
- `p = id` (fiber over `x` contains just `x`)
- `s = id` (source is the point itself)
- `t = id` (target is the point itself)
-/
def WTypeDiagram.identity : WTypeDiagram X X where
  B := X
  E := X
  p := id
  s := id
  t := id

variable {X Y Z : Type u}

/--
The base type (positions) for a composition of W-type diagrams.

Given `g : WTypeDiagram Y Z` and `f : WTypeDiagram X Y`, a position in the
composition at `z : Z` is a position `bg` of `g` mapping to `z`, together with
a choice of position in `f` for each direction in the fiber of `g` at `bg`.
-/
def WTypeDiagram.compB (g : WTypeDiagram Y Z) (f : WTypeDiagram X Y) : Type u :=
  Σ (bg : g.B), (eg : WTypeDiagram.fiber Y Z g bg) → { bf : f.B // f.t bf = g.s eg.val }

/--
The arity type (directions) for a composition of W-type diagrams.

An element consists of a position in the composition, a direction in `g`, and
a direction in the corresponding `f` fiber.
-/
def WTypeDiagram.compE (g : WTypeDiagram Y Z) (f : WTypeDiagram X Y) : Type u :=
  Σ (b : g.compB f), Σ (eg : WTypeDiagram.fiber Y Z g b.1),
    WTypeDiagram.fiber X Y f (b.2 eg).val

/--
Composition of W-type diagrams.

Given `g : WTypeDiagram Y Z` and `f : WTypeDiagram X Y`, their composition
is a W-type diagram `X ← E' → B' → Z` where:
- `B'` is pairs of a `g`-position and a family of `f`-positions
- `E'` consists of pairs of directions from both diagrams
-/
def WTypeDiagram.comp (g : WTypeDiagram Y Z) (f : WTypeDiagram X Y) :
    WTypeDiagram X Z where
  B := g.compB f
  E := g.compE f
  p := fun ⟨b, _⟩ => b
  s := fun ⟨_, ⟨_, ef⟩⟩ => f.s ef.val
  t := fun ⟨bg, _⟩ => g.t bg

end WTypeIdentityComposition

/-! ## W-Type Composition Interpretation

We show that evaluating the composition of W-type diagrams is equivalent to
composing their evaluations.
-/

section WTypeCompositionInterpretation

variable {X Y Z : Type u}

/--
The fiber of a composition of W-type diagrams at a composed position.

For `gf = g.comp f` and a position `⟨bg, pf⟩ : gf.B`, the fiber consists of
pairs `(eg, ef)` where `eg` is in the fiber of `g` at `bg` and `ef` is in the
fiber of `f` at the position `(pf eg).val`.
-/
def WTypeDiagram.comp_fiber_equiv (g : WTypeDiagram Y Z) (f : WTypeDiagram X Y)
    (b : (g.comp f).B) :
    WTypeDiagram.fiber X Z (g.comp f) b ≃
    Σ (eg : WTypeDiagram.fiber Y Z g b.1), WTypeDiagram.fiber X Y f (b.2 eg).val where
  toFun := fun ⟨e, hp⟩ =>
    match b, hp with
    | _, rfl => ⟨e.2.1, e.2.2⟩
  invFun := fun ⟨eg, ef⟩ => ⟨⟨b, eg, ef⟩, rfl⟩
  left_inv := fun ⟨e, hp⟩ => by
    simp only [WTypeDiagram.comp, WTypeDiagram.compE, WTypeDiagram.compB] at hp e ⊢
    cases hp
    rfl
  right_inv := fun ⟨eg, ef⟩ => rfl

@[simp]
lemma WTypeDiagram.comp_fiber_equiv_toFun_rfl (g : WTypeDiagram Y Z) (f : WTypeDiagram X Y)
    (b : (g.comp f).B) (eg : WTypeDiagram.fiber Y Z g b.1)
    (ef : WTypeDiagram.fiber X Y f (b.2 eg).val) :
    (g.comp_fiber_equiv f b).toFun ⟨⟨b, eg, ef⟩, rfl⟩ = ⟨eg, ef⟩ := rfl

@[simp]
lemma WTypeDiagram.comp_fiber_equiv_fst_rfl (g : WTypeDiagram Y Z) (f : WTypeDiagram X Y)
    (b : (g.comp f).B) (eg : WTypeDiagram.fiber Y Z g b.1)
    (ef : WTypeDiagram.fiber X Y f (b.2 eg).val) :
    ((g.comp_fiber_equiv f b) ⟨⟨b, eg, ef⟩, rfl⟩).fst = eg := rfl

@[simp]
lemma WTypeDiagram.comp_fiber_equiv_snd_rfl (g : WTypeDiagram Y Z) (f : WTypeDiagram X Y)
    (b : (g.comp f).B) (eg : WTypeDiagram.fiber Y Z g b.1)
    (ef : WTypeDiagram.fiber X Y f (b.2 eg).val) :
    ((g.comp_fiber_equiv f b) ⟨⟨b, eg, ef⟩, rfl⟩).snd = ef := rfl

/--
The fiberOver of a composition at position `b` is equivalent to the sigma type
over fibers of `g` with fibers of `f`.
-/
def WTypeDiagram.comp_fiberOver_equiv (g : WTypeDiagram Y Z) (f : WTypeDiagram X Y)
    (b : (g.comp f).B) :
    (WTypeDiagram.fiberOver X Z (g.comp f) b).left ≃
    Σ (eg : (WTypeDiagram.fiberOver Y Z g b.1).left),
      (WTypeDiagram.fiberOver X Y f (b.2 eg).val).left :=
  WTypeDiagram.comp_fiber_equiv g f b

/--
The source map of a composition fiber element corresponds to the source of the
`f` component.
-/
lemma WTypeDiagram.comp_fiberOver_source (g : WTypeDiagram Y Z) (f : WTypeDiagram X Y)
    (b : (g.comp f).B) (e : (WTypeDiagram.fiberOver X Z (g.comp f) b).left) :
    (WTypeDiagram.fiberOver X Z (g.comp f) b).hom e =
      (WTypeDiagram.fiberOver X Y f (b.2 (comp_fiberOver_equiv g f b e).1).val).hom
        (comp_fiberOver_equiv g f b e).2 := by
  obtain ⟨⟨_, eg, ef⟩, hp⟩ := e
  cases hp
  rfl

/--
The forward direction of the W-type composition evaluation equivalence.

Given an element of `(g.comp f).evalFamily A z`, produce an element of
`g.evalFamily (f.eval A) z`.
-/
def WTypeDiagram.comp_eval_fiberEquiv_toFun (g : WTypeDiagram Y Z) (f : WTypeDiagram X Y)
    (A : Over X) (z : Z)
    (x : (g.comp f).evalFamily X Z A z) :
    g.evalFamily Y Z (f.eval X Y A) z :=
  let ⟨⟨⟨bg, pf⟩, ht⟩, mor⟩ := x
  -- bg : g.B with g.t bg = z
  -- pf : (eg : g.fiber bg) → { bf : f.B // f.t bf = g.s eg.val }
  -- mor : (g.comp f).fiberOver ⟨bg, pf⟩ ⟶ A
  ⟨⟨bg, ht⟩, Over.homMk
    (fun eg =>
      -- eg : g.fiber bg (equivalently, (g.fiberOver bg).left)
      let bf := pf eg
      -- bf : { bf : f.B // f.t bf = g.s eg.val }
      -- Need to produce an element of (f.eval A).left = Σ y, f.evalFamily A y
      -- i.e., Σ y, Σ (b : {b : f.B // f.t b = y}), (f.fiberOver b.val ⟶ A)
      let y := g.s eg.val
      -- We have bf.2 : f.t bf.val = y
      (⟨y, ⟨⟨bf.val, bf.2⟩, Over.homMk
        (fun ef =>
          -- ef : f.fiber bf.val
          -- Need to produce element of A.left
          -- Use mor applied to the composed fiber element
          mor.left ⟨⟨⟨bg, pf⟩, eg, ef⟩, rfl⟩)
        (by
          funext ef
          exact congrFun (Over.w mor) ⟨⟨⟨bg, pf⟩, eg, ef⟩, rfl⟩)⟩⟩ :
          (f.eval X Y A).left))
    (by funext eg; rfl)⟩

/--
The inverse direction of the W-type composition evaluation equivalence.

Given an element of `g.evalFamily (f.eval A) z`, produce an element of
`(g.comp f).evalFamily A z`.
-/
def WTypeDiagram.comp_eval_fiberEquiv_invFun (g : WTypeDiagram Y Z) (f : WTypeDiagram X Y)
    (A : Over X) (z : Z)
    (x : g.evalFamily Y Z (f.eval X Y A) z) :
    (g.comp f).evalFamily X Z A z :=
  let ⟨⟨bg, ht⟩, h⟩ := x
  -- bg : g.B with g.t bg = z
  -- h : g.fiberOver bg ⟶ f.eval A
  -- h.left : g.fiber bg → (f.eval A).left = Σ y, f.evalFamily A y
  -- For each eg : g.fiber bg, h.left eg gives:
  --   ⟨y, ⟨⟨bf, _⟩, mor⟩⟩ : Σ y, f.evalFamily A y
  -- Commutativity of h: (g.fiberOver bg).hom eg = (f.eval A).hom (h.left eg)
  -- i.e., g.s eg.val = (h.left eg).fst
  let pf : (eg : WTypeDiagram.fiber Y Z g bg) →
           { bf : f.B // f.t bf = g.s eg.val } :=
    fun eg =>
      let fEvalElem := h.left eg
      -- fEvalElem : (f.eval A).left = Σ y, f.evalFamily A y
      -- fEvalElem.1 = y = g.s eg.val (by Over.w h)
      -- fEvalElem.2 = ⟨⟨bf, ht'⟩, mor⟩ where ht' : f.t bf = y
      let bf := fEvalElem.2.1.val
      -- fEvalElem.2.1.2 : f.t bf = fEvalElem.1
      -- (congrFun (Over.w h) eg) : (g.fiberOver bg).hom eg = fEvalElem.1
      -- i.e., g.s eg.val = fEvalElem.1
      ⟨bf, fEvalElem.2.1.2.trans (congrFun (Over.w h) eg)⟩
  ⟨⟨⟨bg, pf⟩, ht⟩, Over.homMk
    (fun e =>
      -- e : (g.comp f).fiber ⟨bg, pf⟩
      -- e = ⟨⟨⟨bg, pf⟩, eg, ef⟩, rfl⟩ after pattern matching
      let eg := (WTypeDiagram.comp_fiber_equiv g f ⟨bg, pf⟩ e).1
      let ef := (WTypeDiagram.comp_fiber_equiv g f ⟨bg, pf⟩ e).2
      -- ef : f.fiber (pf eg).val
      -- We need to apply the inner morphism from h.left eg to ef
      -- h.left eg = ⟨y, ⟨⟨bf, _⟩, innerMor⟩⟩
      -- where bf = (pf eg).val by construction of pf
      let fEvalElem := h.left eg
      let innerMor := fEvalElem.2.2
      -- innerMor : f.fiberOver (fEvalElem.2.1.val) ⟶ A
      -- Need: f.fiberOver (fEvalElem.2.1.val) = f.fiberOver (pf eg).val
      -- This follows from the construction: fEvalElem.2.1.val = (pf eg).val by def
      innerMor.left ef)
    (by
      funext e
      simp only [WTypeDiagram.comp, WTypeDiagram.comp_fiber_equiv,
                 WTypeDiagram.fiberOver]
      obtain ⟨⟨_, eg, ef⟩, hp⟩ := e
      cases hp
      exact congrFun (Over.w (h.left eg).2.2) ef)⟩

/--
Evaluating the composition of W-type diagrams is equivalent to composing their
evaluations.

For `g : WTypeDiagram Y Z` and `f : WTypeDiagram X Y`, and `A : Over X`:
`(g.comp f).evalFamily A z ≃ g.evalFamily (f.eval A) z`

This is the W-type analog of `polyBetweenComp_eval_fiberEquiv`.
-/
def WTypeDiagram.comp_eval_fiberEquiv (g : WTypeDiagram Y Z) (f : WTypeDiagram X Y)
    (A : Over X) (z : Z) :
    (g.comp f).evalFamily X Z A z ≃ g.evalFamily Y Z (f.eval X Y A) z where
  toFun := comp_eval_fiberEquiv_toFun g f A z
  invFun := comp_eval_fiberEquiv_invFun g f A z
  left_inv := fun x => by
    obtain ⟨⟨⟨bg, pf⟩, ht⟩, mor⟩ := x
    simp only [comp_eval_fiberEquiv_toFun, comp_eval_fiberEquiv_invFun,
               Over.homMk_left]
    -- Show equality by Sigma.ext
    apply Sigma.ext
    · -- Index equality: simp already solved the .fst part
      simp only
    · -- Morphism equality (HEq)
      apply heq_of_eq
      apply Over.OverMorphism.ext
      funext e
      simp only [Over.homMk_left, comp_fiber_equiv]
      obtain ⟨⟨_, eg, ef⟩, hp⟩ := e
      cases hp
      rfl
  right_inv := fun x => by
    obtain ⟨⟨bg, ht⟩, h⟩ := x
    simp only [comp_eval_fiberEquiv_toFun, comp_eval_fiberEquiv_invFun]
    apply congrArg
    apply Over.OverMorphism.ext
    funext eg
    -- Goal: the LHS function at eg equals h.left eg
    -- LHS: ⟨g.s eg.val, ⟨⟨(h.left eg).snd.fst.val, proof⟩, morphism⟩⟩
    -- RHS: h.left eg = ⟨(h.left eg).fst, (h.left eg).snd⟩
    -- By Over.w h: (h.left eg).fst = g.s eg.val
    simp only [Over.homMk_left]
    have h1 : (h.left eg).fst = g.s eg.val := congrFun (Over.w h) eg
    -- Both sides are in (eval X Y f A).left = Σ y, evalFamily X Y f A y
    -- The outer sigma has fst at g.s eg.val on LHS, and (h.left eg).fst on RHS
    -- By h1 these are equal
    -- Use Sigma.eta on both sides and prove componentwise
    conv_lhs => rw [← Sigma.eta (⟨g.s eg.val, _⟩ : (eval X Y f A).left)]
    conv_rhs => rw [← Sigma.eta (h.left eg)]
    simp only
    -- Now goal is: ⟨fst1, snd1⟩ = ⟨fst2, snd2⟩
    -- where fst1 = g.s eg.val, fst2 = (h.left eg).fst
    -- and snd1 = LHS_snd, snd2 = (h.left eg).snd
    apply Sigma.ext
    · exact h1.symm
    · -- HEq goal: need LHS_snd ≍ (h.left eg).snd
      simp only [comp_fiber_equiv]
      -- LHS_snd is a sigma ⟨subtype, morphism⟩ in evalFamily ... (g.s eg.val)
      -- RHS_snd is (h.left eg).snd in evalFamily ... ((h.left eg).fst)
      conv_rhs => rw [← Sigma.eta ((h.left eg).snd)]
      -- We need to prove HEq between sigma types at different parameter indices
      -- This is exactly what sigma_heq_of_param_eq handles
      refine @sigma_heq_of_param_eq Y
        (fun y => { b : f.B // f.t b = y })
        (fun y b => fiberOver X Y f b.val ⟶ A)
        (g.s eg.val) ((h.left eg).fst) h1.symm
        ⟨(h.left eg).snd.fst.val, _⟩ (h.left eg).snd.fst
        ?_ _ (h.left eg).snd.snd ?_
      · -- First components HEq: subtypes with same .val
        refine @subtype_heq_of_index_eq f.B Y (fun i b => f.t b = i)
          (g.s eg.val) ((h.left eg).fst) h1.symm
          ⟨(h.left eg).snd.fst.val, _⟩ (h.left eg).snd.fst ?_
        rfl
      · -- Second components HEq: morphisms
        apply heq_of_eq
        apply Over.OverMorphism.ext
        funext ef
        simp only [Over.homMk_left]
        -- LHS: (h.left (comp_fiber_equiv ...).fst).snd.snd.left (comp_fiber_equiv ...).snd
        -- RHS: (h.left eg).snd.snd.left ef
        -- The comp_fiber_equiv computes to (eg, ef) with input ⟨⟨⟨bg, pf⟩, ⟨eg, ef⟩⟩, rfl⟩
        -- So (comp_fiber_equiv ...).fst = eg and (comp_fiber_equiv ...).snd = ef
        -- Therefore LHS = (h.left eg).snd.snd.left ef = RHS
        rfl

end WTypeCompositionInterpretation

/-! ## W-Type Diagram Morphisms

Morphisms between W-type diagrams use the category-theoretic formulation with
explicit pullbacks and commutative diagrams. A morphism `f : P → Q` consists of:

1. A map `onPos : P.B → Q.B` on positions
2. A map `onDir : Pullback → P.E` on directions, where the pullback is the
   categorical pullback of `Q.p` along `onPos`
3. Three commutativity conditions forming commutative diagrams

This matches the standard 2-category of polynomial functors from ncatlab.
-/

section WTypeDiagramMorphisms

variable {X Y : Type u}

/--
The pullback type for W-type diagram morphisms.

Given `P, Q : WTypeDiagram X Y` and `onPos : P.B → Q.B`, the pullback is:
```
Pullback --pbProj1--> Q.E
   |                   |
pbProj2              Q.p
   |                   |
   v                   v
 P.B ----onPos----> Q.B
```

An element of the pullback is a pair `(q_e, p_b)` where `q_e : Q.E` and
`p_b : P.B` such that `Q.p q_e = onPos p_b`.
-/
def WTypePullback (P Q : WTypeDiagram X Y) (onPos : P.B → Q.B) : Type u :=
  { pair : Q.E × P.B // Q.p pair.1 = onPos pair.2 }

/--
First projection from the pullback: extracts the Q.E component.
-/
def WTypePullback.proj1 {P Q : WTypeDiagram X Y} {onPos : P.B → Q.B}
    (pb : WTypePullback P Q onPos) : Q.E :=
  pb.val.1

/--
Second projection from the pullback: extracts the P.B component.
-/
def WTypePullback.proj2 {P Q : WTypeDiagram X Y} {onPos : P.B → Q.B}
    (pb : WTypePullback P Q onPos) : P.B :=
  pb.val.2

/--
The commutativity condition for pullback elements.
-/
lemma WTypePullback.comm {P Q : WTypeDiagram X Y} {onPos : P.B → Q.B}
    (pb : WTypePullback P Q onPos) : Q.p pb.proj1 = onPos pb.proj2 :=
  pb.property

/--
Construct a pullback element from components and a proof of commutativity.
-/
def WTypePullback.mk {P Q : WTypeDiagram X Y} {onPos : P.B → Q.B}
    (qe : Q.E) (pb : P.B) (h : Q.p qe = onPos pb) : WTypePullback P Q onPos :=
  ⟨(qe, pb), h⟩

@[simp]
lemma WTypePullback.mk_proj1 {P Q : WTypeDiagram X Y} {onPos : P.B → Q.B}
    (qe : Q.E) (pb : P.B) (h : Q.p qe = onPos pb) :
    (WTypePullback.mk qe pb h).proj1 = qe := rfl

@[simp]
lemma WTypePullback.mk_proj2 {P Q : WTypeDiagram X Y} {onPos : P.B → Q.B}
    (qe : Q.E) (pb : P.B) (h : Q.p qe = onPos pb) :
    (WTypePullback.mk qe pb h).proj2 = pb := rfl

/--
Extensionality for pullback elements.
-/
@[ext]
lemma WTypePullback.ext {P Q : WTypeDiagram X Y} {onPos : P.B → Q.B}
    {pb1 pb2 : WTypePullback P Q onPos}
    (h1 : pb1.proj1 = pb2.proj1) (h2 : pb1.proj2 = pb2.proj2) : pb1 = pb2 := by
  obtain ⟨⟨qe1, b1⟩, _⟩ := pb1
  obtain ⟨⟨qe2, b2⟩, _⟩ := pb2
  simp only [proj1] at h1
  simp only [proj2] at h2
  cases h1
  cases h2
  rfl

/--
Transport on `WTypePullback` preserves the underlying pair value.
-/
lemma WTypePullback.transport_val {P Q : WTypeDiagram X Y}
    {onPos1 onPos2 : P.B → Q.B} (h : onPos1 = onPos2)
    (pb : WTypePullback P Q onPos1) : (h ▸ pb).val = pb.val := by
  cases h
  rfl

/--
Transport on `WTypePullback` preserves proj1.
-/
lemma WTypePullback.transport_proj1 {P Q : WTypeDiagram X Y}
    {onPos1 onPos2 : P.B → Q.B} (h : onPos1 = onPos2)
    (pb : WTypePullback P Q onPos1) : (h ▸ pb).proj1 = pb.proj1 := by
  cases h
  rfl

/--
Transport on `WTypePullback` preserves proj2.
-/
lemma WTypePullback.transport_proj2 {P Q : WTypeDiagram X Y}
    {onPos1 onPos2 : P.B → Q.B} (h : onPos1 = onPos2)
    (pb : WTypePullback P Q onPos1) : (h ▸ pb).proj2 = pb.proj2 := by
  cases h
  rfl

/--
A morphism between W-type diagrams.

Given `P, Q : WTypeDiagram X Y`, a morphism `P → Q` consists of:
- `onPos : P.B → Q.B` - a map on positions (base types)
- `onDir : WTypePullback P Q onPos → P.E` - a map from the pullback to P's directions

With three commutativity conditions:

1. Position-target commutativity (triangle):
```
    P.B --onPos--> Q.B
     \            /
  P.t \          / Q.t
       \        /
        v      v
           Y
```
That is, `Q.t (onPos b) = P.t b` for all `b : P.B`.

2. Direction-projection commutativity:
```
P.p ∘ onDir = proj2
```
The direction map followed by P.p equals the pullback's second projection.

3. Source/assignment commutativity:
```
   Pullback --proj1--> Q.E
      |                 |
   onDir             Q.s
      |                 |
      v                 v
    P.E ----P.s------> X
```
That is, `P.s (onDir pb) = Q.s (pb.proj1)` for all pullback elements.
-/
structure WTypeDiagramHom (P Q : WTypeDiagram X Y) where
  /-- Map on positions (base types) -/
  onPos : P.B → Q.B
  /-- Map on directions from the pullback to P's directions -/
  onDir : WTypePullback P Q onPos → P.E
  /-- Position map preserves target: Q.t ∘ onPos = P.t -/
  commPos : ∀ b : P.B, Q.t (onPos b) = P.t b
  /-- Direction map respects projection: P.p ∘ onDir = proj2 -/
  commDir : ∀ pb : WTypePullback P Q onPos, P.p (onDir pb) = pb.proj2
  /-- Direction map preserves source: P.s ∘ onDir = Q.s ∘ proj1 -/
  commAssign : ∀ pb : WTypePullback P Q onPos, P.s (onDir pb) = Q.s pb.proj1

/--
Extensionality for W-type diagram morphisms.

Two morphisms are equal if their position maps and direction maps are equal.
The commutativity proofs are propositional and thus irrelevant.
-/
@[ext (iff := false)]
lemma WTypeDiagramHom.ext {P Q : WTypeDiagram X Y} {f g : WTypeDiagramHom P Q}
    (hPos : f.onPos = g.onPos)
    (hDir : ∀ pb : WTypePullback P Q f.onPos,
      f.onDir pb = g.onDir (hPos ▸ pb)) : f = g := by
  obtain ⟨fPos, fDir, _, _, _⟩ := f
  obtain ⟨gPos, gDir, _, _, _⟩ := g
  cases hPos
  have hDir' : fDir = gDir := funext hDir
  cases hDir'
  rfl

/--
The identity morphism on a W-type diagram.

For `P : WTypeDiagram X Y`, the identity has:
- `onPos = id` (identity on positions)
- `onDir pb = pb.proj1` (the direction is just the Q.E component of the pullback,
  which equals P.E when Q = P and onPos = id)

The pullback for the identity is `{(e, b) : P.E × P.B | P.p e = b}`, which is
equivalent to `P.E` via the first projection.
-/
def WTypeDiagramHom.id (P : WTypeDiagram X Y) : WTypeDiagramHom P P where
  onPos := _root_.id
  onDir := fun pb => pb.proj1
  commPos := fun _ => rfl
  commDir := fun pb => pb.comm
  commAssign := fun _ => rfl

/--
Composition of W-type diagram morphisms.

For `f : P → Q` and `g : Q → R`, the composition `g ∘ f : P → R` has:
- `onPos = g.onPos ∘ f.onPos`
- `onDir` works by threading through both pullbacks:
  1. Given `pb : WTypePullback P R (g.onPos ∘ f.onPos)` with
     `R.p pb.proj1 = g.onPos (f.onPos pb.proj2)`
  2. Form `pb_g : WTypePullback Q R g.onPos` as `(pb.proj1, f.onPos pb.proj2)`
  3. Apply `g.onDir pb_g` to get a `Q.E` element
  4. By `g.commDir`, this satisfies `Q.p (g.onDir pb_g) = f.onPos pb.proj2`
  5. Form `pb_f : WTypePullback P Q f.onPos` as `(g.onDir pb_g, pb.proj2)`
  6. Apply `f.onDir pb_f` to get the final `P.E` element
-/
def WTypeDiagramHom.comp {P Q R : WTypeDiagram X Y}
    (g : WTypeDiagramHom Q R) (f : WTypeDiagramHom P Q) : WTypeDiagramHom P R where
  onPos := g.onPos ∘ f.onPos
  onDir := fun pb =>
    let pb_g : WTypePullback Q R g.onPos := WTypePullback.mk pb.proj1 (f.onPos pb.proj2) pb.comm
    let qe := g.onDir pb_g
    let pb_f : WTypePullback P Q f.onPos := WTypePullback.mk qe pb.proj2 (g.commDir pb_g)
    f.onDir pb_f
  commPos := fun b => by
    simp only [Function.comp_apply]
    rw [g.commPos, f.commPos]
  commDir := fun pb => by
    simp only
    exact f.commDir _
  commAssign := fun pb => by
    simp only
    let pb_g : WTypePullback Q R g.onPos :=
      WTypePullback.mk pb.proj1 (f.onPos pb.proj2) pb.comm
    let pb_f : WTypePullback P Q f.onPos :=
      WTypePullback.mk (g.onDir pb_g) pb.proj2 (g.commDir pb_g)
    calc P.s (f.onDir pb_f) = Q.s pb_f.proj1 := f.commAssign pb_f
      _ = Q.s (g.onDir pb_g) := rfl
      _ = R.s pb_g.proj1 := g.commAssign pb_g
      _ = R.s pb.proj1 := rfl

/--
Left identity law: `id.comp f = f`.
-/
lemma WTypeDiagramHom.id_comp {P Q : WTypeDiagram X Y} (f : WTypeDiagramHom P Q) :
    WTypeDiagramHom.comp (WTypeDiagramHom.id Q) f = f := by
  apply WTypeDiagramHom.ext (hPos := rfl)
  intro pb
  simp only [comp, WTypeDiagramHom.id, WTypePullback.mk_proj1]

/--
Right identity law: `f.comp id = f`.
-/
lemma WTypeDiagramHom.comp_id {P Q : WTypeDiagram X Y} (f : WTypeDiagramHom P Q) :
    WTypeDiagramHom.comp f (WTypeDiagramHom.id P) = f := by
  apply WTypeDiagramHom.ext (hPos := rfl)
  intro pb
  simp only [comp, WTypeDiagramHom.id]

/--
Associativity: `(h.comp g).comp f = h.comp (g.comp f)`.
-/
lemma WTypeDiagramHom.comp_assoc {P Q R S : WTypeDiagram X Y}
    (h : WTypeDiagramHom R S) (g : WTypeDiagramHom Q R) (f : WTypeDiagramHom P Q) :
    WTypeDiagramHom.comp (WTypeDiagramHom.comp h g) f =
    WTypeDiagramHom.comp h (WTypeDiagramHom.comp g f) := by
  apply WTypeDiagramHom.ext (hPos := rfl)
  intro pb
  simp only [comp]

/--
Category instance for W-type diagrams.

Objects are W-type diagrams `X ← E → B → Y`, and morphisms are `WTypeDiagramHom`
structures with explicit pullbacks and commutative diagrams.
-/
instance WTypeDiagramCategory : Category (WTypeDiagram X Y) where
  Hom := WTypeDiagramHom
  id := WTypeDiagramHom.id
  comp := fun f g => WTypeDiagramHom.comp g f
  id_comp := WTypeDiagramHom.comp_id
  comp_id := WTypeDiagramHom.id_comp
  assoc := fun f g h => (WTypeDiagramHom.comp_assoc h g f).symm

end WTypeDiagramMorphisms

/-! ## W-Type Diagram Category as a Cat

We package the category of W-type diagrams as a `Cat` for consistency with
`PolyFunctorCat` and `PolyFunctorBetweenCat`.
-/

section WTypeDiagramCatDef

variable (X Y : Type u)

/--
The category of W-type diagrams `X ← E → B → Y`.

Objects are `WTypeDiagram X Y` structures and morphisms are `WTypeDiagramHom`
with explicit pullbacks and three commutativity conditions.

This is equivalent to (and will be shown equivalent to) `PolyFunctorBetweenCat X Y`.
-/
abbrev WTypeDiagramCat : Cat := Cat.of (WTypeDiagram X Y)

end WTypeDiagramCatDef

/-! ## Functor: WTypeDiagramCat → PolyFunctorBetweenCat

We define a functor from W-type diagrams to Y-indexed families of polynomial
functors (the Grothendieck representation).

Given `W : WTypeDiagram X Y`:
- At each `y : Y`, the polynomial functor has:
  - Index type: `{b : W.B // W.t b = y}` (positions mapping to y)
  - Family: `b ↦ W.fiberOver b.val` (the fiber at each position)
-/

section WTypeToPolyBetween

variable {X Y : Type u}

/--
Convert a W-type diagram to a Grothendieck-style polynomial functor.

Given `W : WTypeDiagram X Y`, for each `y : Y` we get a polynomial functor
`Over X → Type` with:
- Index type: positions in W that map to y (i.e., `{b : W.B // W.t b = y}`)
- At each such position b, the representable is `W.fiberOver b`
-/
def wTypeToPolyBetweenObj (W : WTypeDiagram X Y) : PolyFunctorBetweenCat X Y :=
  fun y => ccrObjMk (fun (b : { b : W.B // W.t b = y }) => W.fiberOver X Y b.val)

/--
The reindexing function for the morphism mapping.

Given `f : WTypeDiagramHom P Q` and a position in P at y, produce the
corresponding position in Q at y.
-/
def wTypeToPolyBetweenReindex {P Q : WTypeDiagram X Y} (f : WTypeDiagramHom P Q)
    (y : Y) (b : { b : P.B // P.t b = y }) : { b : Q.B // Q.t b = y } :=
  ⟨f.onPos b.val, (f.commPos b.val).trans b.property⟩

/--
The fiber morphism for the morphism mapping.

Given `f : WTypeDiagramHom P Q` and a position `b` in P at y, produce a
morphism from `Q.fiberOver (f.onPos b)` to `P.fiberOver b` in `Over X`.

This uses the pullback structure: given `e : Q.E` with `Q.p e = f.onPos b`,
we form a pullback element and apply `f.onDir` to get an element of P.E
in the fiber over b.
-/
def wTypeToPolyBetweenFiberMor {P Q : WTypeDiagram X Y} (f : WTypeDiagramHom P Q)
    (y : Y) (b : { b : P.B // P.t b = y }) :
    Q.fiberOver X Y (f.onPos b.val) ⟶ P.fiberOver X Y b.val :=
  Over.homMk
    (fun (e : WTypeDiagram.fiber X Y Q (f.onPos b.val)) =>
      let pb : WTypePullback P Q f.onPos := WTypePullback.mk e.val b.val e.property
      ⟨f.onDir pb, f.commDir pb⟩)
    (by
      funext e
      simp only [WTypeDiagram.fiberOver, Over.mk_hom]
      exact f.commAssign _)

/--
Convert a W-type diagram morphism to a PolyFunctorBetweenCat morphism.

Given `f : WTypeDiagramHom P Q`, at each `y : Y` we get a morphism between
the polynomial functors:
- Reindexing: `b ↦ f.onPos b`
- Fiber morphism: uses `f.onDir` via the pullback
-/
def wTypeToPolyBetweenMap {P Q : WTypeDiagram X Y} (f : WTypeDiagramHom P Q) :
    wTypeToPolyBetweenObj P ⟶ wTypeToPolyBetweenObj Q :=
  fun y => ccrHomMk
    (wTypeToPolyBetweenReindex f y)
    (fun b => wTypeToPolyBetweenFiberMor f y b)

/--
The W-type to PolyBetween mapping preserves identity morphisms.
-/
lemma wTypeToPolyBetweenMap_id (P : WTypeDiagram X Y) :
    wTypeToPolyBetweenMap (WTypeDiagramHom.id P) = 𝟙 (wTypeToPolyBetweenObj P) := by
  funext y
  rfl

/--
The W-type to PolyBetween mapping preserves composition.
-/
lemma wTypeToPolyBetweenMap_comp {P Q R : WTypeDiagram X Y}
    (f : WTypeDiagramHom P Q) (g : WTypeDiagramHom Q R) :
    wTypeToPolyBetweenMap (WTypeDiagramHom.comp g f) =
    wTypeToPolyBetweenMap f ≫ wTypeToPolyBetweenMap g := by
  funext y
  rfl

/--
The functor from W-type diagrams to Grothendieck-style polynomial functors.
-/
def wTypeToPolyBetween : WTypeDiagram X Y ⥤ PolyFunctorBetweenCat X Y where
  obj := wTypeToPolyBetweenObj
  map := wTypeToPolyBetweenMap
  map_id := wTypeToPolyBetweenMap_id
  map_comp f g := wTypeToPolyBetweenMap_comp f g

end WTypeToPolyBetween

/-! ## Functor: PolyFunctorBetweenCat → WTypeDiagramCat

We define a functor from Y-indexed families of polynomial functors
(the Grothendieck representation) to W-type diagrams.

Given `P : PolyFunctorBetweenCat X Y`:
- `B = Σ y, ccrIndex (P y)` (all positions across all y)
- `E = Σ (y : Y) (i : ccrIndex (P y)), (ccrFamily (P y) i).left`
- `p`, `s`, `t` are the natural projection and structure maps
-/

section PolyBetweenToWType

variable {X Y : Type u}

/--
Convert a Grothendieck-style polynomial functor to a W-type diagram.

Given `P : PolyFunctorBetweenCat X Y`, we construct:
- `B = Σ y, ccrIndex (P y)` - positions are pairs of (target y, index at y)
- `E` - directions are triples (y, index, fiber element)
- `p` - projects out the position (y, index)
- `s` - source comes from the Over structure of each fiber
- `t` - target is the first component y
-/
def polyBetweenToWTypeObj (P : PolyFunctorBetweenCat X Y) : WTypeDiagram X Y where
  B := Σ y : Y, ccrIndex (P y)
  E := Σ (y : Y) (i : ccrIndex (P y)), (ccrFamily (P y) i).left
  p := fun ⟨y, i, _⟩ => ⟨y, i⟩
  s := fun ⟨y, i, e⟩ => (ccrFamily (P y) i).hom e
  t := fun ⟨y, _⟩ => y

/--
The fiber of `polyBetweenToWTypeObj P` at position `(y, i)` is the left component
of `ccrFamily (P y) i`.
-/
lemma polyBetweenToWTypeObj_fiber (P : PolyFunctorBetweenCat X Y)
    (yi : (polyBetweenToWTypeObj P).B) :
    WTypeDiagram.fiber X Y (polyBetweenToWTypeObj P) yi =
      { e : Σ (y : Y) (i : ccrIndex (P y)), (ccrFamily (P y) i).left //
        (⟨e.1, e.2.1⟩ : Σ y, ccrIndex (P y)) = yi } := rfl

/--
Equivalence between the fiber at `(y, i)` and the left component of
`ccrFamily (P y) i`.
-/
def polyBetweenToWTypeObj_fiber_equiv (P : PolyFunctorBetweenCat X Y)
    (y : Y) (i : ccrIndex (P y)) :
    WTypeDiagram.fiber X Y (polyBetweenToWTypeObj P) ⟨y, i⟩ ≃
      (ccrFamily (P y) i).left where
  toFun := fun ⟨⟨y', i', e⟩, h⟩ =>
    match y', i', e, h with
    | _, _, e, rfl => e
  invFun := fun e => ⟨⟨y, i, e⟩, rfl⟩
  left_inv := fun ⟨⟨y', i', e⟩, h⟩ => by
    match y', i', e, h with
    | _, _, _, rfl => rfl
  right_inv := fun _ => rfl

/--
The reindexing function for the morphism mapping.

Given `f : P ⟶ Q` in `PolyFunctorBetweenCat X Y` and a position `(y, i)` in the
W-type for P, produce the corresponding position in the W-type for Q.
-/
def polyBetweenToWTypeReindex {P Q : PolyFunctorBetweenCat X Y} (f : P ⟶ Q)
    (yi : (polyBetweenToWTypeObj P).B) : (polyBetweenToWTypeObj Q).B :=
  ⟨yi.1, ccrReindex (f yi.1) yi.2⟩

/--
Helper to extract the fiber element with correct type from a pullback.

Uses pattern matching to handle the sigma equality.
-/
def polyBetweenToWTypeMap_fiberCast {P Q : PolyFunctorBetweenCat X Y}
    (f : P ⟶ Q) (pb : WTypePullback (polyBetweenToWTypeObj P)
      (polyBetweenToWTypeObj Q) (polyBetweenToWTypeReindex f)) :
    (ccrFamily (Q pb.proj2.1) (ccrReindex (f pb.proj2.1) pb.proj2.2)).left :=
  match pb.proj1, pb.proj2, pb.comm with
  | ⟨y, i, e⟩, ⟨y', i'⟩, h =>
    match y, i, e, y', i', h with
    | _, _, e, _, _, rfl => e

/--
Helper lemma: the fiber cast equals the original element when the pullback commutes.
-/
lemma polyBetweenToWTypeMap_fiberCast_eq {P Q : PolyFunctorBetweenCat X Y}
    (f : P ⟶ Q) (y : Y) (i' : ccrIndex (P y))
    (e : (ccrFamily (Q y) (ccrReindex (f y) i')).left) :
    polyBetweenToWTypeMap_fiberCast f
      ⟨(⟨y, ccrReindex (f y) i', e⟩, ⟨y, i'⟩), rfl⟩ = e := rfl

lemma polyBetweenToWTypeMap_fiberCast_eq' {P Q : PolyFunctorBetweenCat X Y}
    (f : P ⟶ Q) (y : Y) (i' : ccrIndex (P y))
    (e : (ccrFamily (Q y) (ccrReindex (f y) i')).left)
    (h : (polyBetweenToWTypeObj Q).p ⟨y, ccrReindex (f y) i', e⟩ =
         polyBetweenToWTypeReindex f ⟨y, i'⟩) :
    polyBetweenToWTypeMap_fiberCast f
      ⟨(⟨y, ccrReindex (f y) i', e⟩, ⟨y, i'⟩), h⟩ = e := by
  have hrfl : h = rfl := Subsingleton.elim _ _
  subst hrfl
  rfl

/--
General lemma: `polyBetweenToWTypeMap_fiberCast` extracts the fiber element from proj1.

The result's underlying element equals `pb.proj1.2.2` (the innermost component)
after accounting for the type differences induced by the pullback commutativity.
-/
lemma polyBetweenToWTypeMap_fiberCast_proj1 {P Q : PolyFunctorBetweenCat X Y}
    (f : P ⟶ Q) (pb : WTypePullback (polyBetweenToWTypeObj P)
      (polyBetweenToWTypeObj Q) (polyBetweenToWTypeReindex f)) :
    HEq (polyBetweenToWTypeMap_fiberCast f pb) pb.proj1.2.2 := by
  obtain ⟨⟨⟨y, i, e⟩, ⟨y', i'⟩⟩, h⟩ := pb
  simp only [polyBetweenToWTypeObj, polyBetweenToWTypeReindex, WTypePullback.proj1,
             WTypePullback.proj2] at h ⊢
  obtain ⟨rfl, hi⟩ := Sigma.mk.inj h
  have hi' : i = ccrReindex (f y) i' := eq_of_heq hi
  subst hi'
  rfl

/--
For `wTypeToPolyBetween.map f`, the underlying element of `polyBetweenToWTypeMap_fiberCast`
equals the val of `pb.proj1.2.2`.

This is the specialized version needed for unitHom_naturality.
-/
lemma polyBetweenToWTypeMap_fiberCast_val_wType {W W' : WTypeDiagram X Y}
    (f : WTypeDiagramHom W W')
    (pb : WTypePullback (polyBetweenToWTypeObj (wTypeToPolyBetweenObj W))
      (polyBetweenToWTypeObj (wTypeToPolyBetweenObj W'))
      (polyBetweenToWTypeReindex (wTypeToPolyBetween.map f))) :
    (polyBetweenToWTypeMap_fiberCast (wTypeToPolyBetween.map f) pb).val =
      pb.proj1.2.2.val := by
  obtain ⟨⟨⟨y, i, e⟩, ⟨y', i'⟩⟩, hcomm⟩ := pb
  simp only [polyBetweenToWTypeObj, polyBetweenToWTypeReindex, wTypeToPolyBetween,
             wTypeToPolyBetweenMap, WTypePullback.proj1, WTypePullback.proj2] at hcomm ⊢
  obtain ⟨rfl, hi⟩ := Sigma.mk.inj hcomm
  have hi' : i = wTypeToPolyBetweenReindex f y i' := eq_of_heq hi
  subst hi'
  rfl

/--
Helper: the `onDir` computation result for a PolyBetweenToWType morphism.

Given `f : P ⟶ Q` and position `(y, i')` in P, with fiber element `e` from Q's
fiber over `ccrReindex (f y) i'`, returns `(y, i', (ccrFiberMor (f y) i').left e)`.
-/
def polyBetweenToWTypeMap_onDir {P Q : PolyFunctorBetweenCat X Y}
    (f : P ⟶ Q) (y : Y) (i' : ccrIndex (P y))
    (e : (ccrFamily (Q y) (ccrReindex (f y) i')).left) :
    (polyBetweenToWTypeObj P).E :=
  ⟨y, i', (ccrFiberMor (f y) i').left e⟩

/--
Convert a PolyFunctorBetweenCat morphism to a WTypeDiagramHom.

Given `f : P ⟶ Q`, we construct:
- `onPos ⟨y, i⟩ = ⟨y, ccrReindex (f y) i⟩`
- `onDir` uses the fiber morphism `ccrFiberMor (f y) i`
-/
def polyBetweenToWTypeMap {P Q : PolyFunctorBetweenCat X Y} (f : P ⟶ Q) :
    WTypeDiagramHom (polyBetweenToWTypeObj P) (polyBetweenToWTypeObj Q) where
  onPos := polyBetweenToWTypeReindex f
  onDir := fun pb =>
    ⟨pb.proj2.1, pb.proj2.2,
     (ccrFiberMor (f pb.proj2.1) pb.proj2.2).left (polyBetweenToWTypeMap_fiberCast f pb)⟩
  commPos := fun ⟨_, _⟩ => rfl
  commDir := fun _ => rfl
  commAssign := fun pb => by
    obtain ⟨⟨⟨y, i, e⟩, ⟨y', i'⟩⟩, h⟩ := pb
    simp only [polyBetweenToWTypeObj, polyBetweenToWTypeReindex, WTypePullback.proj1,
               WTypePullback.proj2] at h ⊢
    obtain ⟨rfl, hi⟩ := Sigma.mk.inj h
    have hi' : i = ccrReindex (f y) i' := eq_of_heq hi
    subst hi'
    conv_lhs => rw [show polyBetweenToWTypeMap_fiberCast f
      ⟨(⟨y, ccrReindex (f y) i', e⟩, ⟨y, i'⟩), h⟩ = e from rfl]
    have hw := congrFun (Over.w (ccrFiberMor (f y) i')) e
    simp only [ccrFamily, ccrFiberMor, CategoryStruct.comp, Function.comp_apply] at hw ⊢
    exact hw

/--
The PolyBetween to W-type mapping preserves identity morphisms.
-/
lemma polyBetweenToWTypeMap_id (P : PolyFunctorBetweenCat X Y) :
    polyBetweenToWTypeMap (𝟙 P) = WTypeDiagramHom.id (polyBetweenToWTypeObj P) := by
  have hPos : (polyBetweenToWTypeMap (𝟙 P)).onPos =
      (WTypeDiagramHom.id (polyBetweenToWTypeObj P)).onPos := by
    funext ⟨y, i⟩
    simp only [polyBetweenToWTypeMap, WTypeDiagramHom.id, polyBetweenToWTypeReindex, ccrReindex]
    rfl
  apply WTypeDiagramHom.ext hPos
  intro pb
  obtain ⟨⟨⟨y, i, e⟩, ⟨y', i'⟩⟩, h⟩ := pb
  simp only [polyBetweenToWTypeMap, WTypeDiagramHom.id, WTypePullback.proj1, WTypePullback.proj2,
             polyBetweenToWTypeObj, polyBetweenToWTypeReindex] at h ⊢
  obtain ⟨rfl, hi⟩ := Sigma.mk.inj h
  have hi' : i = ccrReindex ((𝟙 P) y) i' := eq_of_heq hi
  simp only [ccrReindex] at hi'
  subst hi'
  conv_lhs => rw [show polyBetweenToWTypeMap_fiberCast (𝟙 P)
    ⟨(⟨y, i, e⟩, ⟨y, i⟩), h⟩ = e from rfl]
  simp only [ccrFiberMor]
  rfl

/--
The PolyBetween to W-type mapping preserves composition.
-/
lemma polyBetweenToWTypeMap_comp {P Q R : PolyFunctorBetweenCat X Y}
    (f : P ⟶ Q) (g : Q ⟶ R) :
    polyBetweenToWTypeMap (f ≫ g) =
    WTypeDiagramHom.comp (polyBetweenToWTypeMap g) (polyBetweenToWTypeMap f) := by
  have hPos : (polyBetweenToWTypeMap (f ≫ g)).onPos =
      (WTypeDiagramHom.comp (polyBetweenToWTypeMap g) (polyBetweenToWTypeMap f)).onPos := by
    funext ⟨y, i⟩
    simp only [polyBetweenToWTypeMap, WTypeDiagramHom.comp, polyBetweenToWTypeReindex,
               ccrReindex, Function.comp_apply]
    rfl
  apply WTypeDiagramHom.ext hPos
  intro pb
  obtain ⟨⟨⟨y, i, e⟩, ⟨y', i'⟩⟩, h⟩ := pb
  simp only [polyBetweenToWTypeMap, WTypeDiagramHom.comp, WTypePullback.proj1, WTypePullback.proj2,
             WTypePullback.mk, polyBetweenToWTypeObj, polyBetweenToWTypeReindex] at h ⊢
  obtain ⟨rfl, hi⟩ := Sigma.mk.inj h
  have hi' : i = ccrReindex ((f ≫ g) y) i' := eq_of_heq hi
  simp only [ccrReindex] at hi'
  subst hi'
  conv_lhs => rw [show polyBetweenToWTypeMap_fiberCast (f ≫ g)
    ⟨(⟨y, ((f ≫ g) y).base i', e⟩, ⟨y, i'⟩), h⟩ = e from rfl]
  simp only [ccrFiberMor, ccrFamily]
  have hcomp := ccrComp_fiberMor (f y) (g y) i'
  simp only [ccrFiberMor, ccrReindex] at hcomp
  have heq : ((f ≫ g) y).fiber i' = (f y ≫ g y).fiber i' := rfl
  rw [heq, hcomp]
  simp only [CategoryStruct.comp, Function.comp_apply, ccrReindex]
  rfl

/--
The functor from Grothendieck-style polynomial functors to W-type diagrams.
-/
def polyBetweenToWType : PolyFunctorBetweenCat X Y ⥤ WTypeDiagram X Y where
  obj := polyBetweenToWTypeObj
  map := polyBetweenToWTypeMap
  map_id := polyBetweenToWTypeMap_id
  map_comp := polyBetweenToWTypeMap_comp

end PolyBetweenToWType

/-! ## Equivalence between W-type diagrams and Grothendieck-style polynomial functors -/

section WTypePolyBetweenEquiv

variable {X Y : Type u}

/--
The composite `polyBetweenToWType ∘ wTypeToPolyBetween` applied to a W-type diagram W
produces a W-type diagram with:
- `B = Σ y, { b : W.B // W.t b = y }` which is equivalent to `W.B`
- The equivalence is `⟨y, ⟨b, h⟩⟩ ↔ b`

This defines the forward direction of the base type equivalence.
-/
def unitBase_toFun (W : WTypeDiagram X Y) :
    (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)).B → W.B :=
  fun ⟨_, ⟨b, _⟩⟩ => b

/--
Inverse of `unitBase_toFun`.
-/
def unitBase_invFun (W : WTypeDiagram X Y) :
    W.B → (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)).B :=
  fun b => ⟨W.t b, ⟨b, rfl⟩⟩

/--
The base type equivalence for the unit isomorphism.
-/
def unitBase_equiv (W : WTypeDiagram X Y) :
    (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)).B ≃ W.B where
  toFun := unitBase_toFun W
  invFun := unitBase_invFun W
  left_inv := fun ⟨y, ⟨b, h⟩⟩ => by
    simp only [unitBase_toFun, unitBase_invFun]
    subst h
    rfl
  right_inv := fun _ => rfl

/--
The `onPos` map for the unit isomorphism component.
-/
def unitInv_onPos (W : WTypeDiagram X Y) :
    (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)).B → W.B :=
  unitBase_toFun W

/--
The target preservation for the unit isomorphism.
-/
lemma unitInv_commPos (W : WTypeDiagram X Y) (pos : _) :
    W.t (unitInv_onPos W pos) =
    (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)).t pos := by
  obtain ⟨y, ⟨b, h⟩⟩ := pos
  simp only [unitInv_onPos, unitBase_toFun, polyBetweenToWType, polyBetweenToWTypeObj]
  exact h

/--
The direction map for the unit inverse morphism.

Given a pullback element `pb`, we need to produce an element of `G(F(W)).E`.
The pullback element contains `pb.proj1 : W.E` and `pb.proj2 : G(F(W)).B`.
Since `W.p pb.proj1 = unitInv_onPos W pb.proj2`, the element `pb.proj1` lies
in the W-fiber over the appropriate position, which we can translate to
the `G(F(W))` fiber structure.
-/
def unitInv_onDir (W : WTypeDiagram X Y)
    (pb : WTypePullback (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)) W
      (unitInv_onPos W)) :
    (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)).E :=
  match pb.proj1, pb.proj2, pb.comm with
  | e, ⟨y, ⟨b, h⟩⟩, pe => ⟨y, ⟨b, h⟩, ⟨e, pe⟩⟩

/--
The direction map respects the projection.
-/
lemma unitInv_commDir (W : WTypeDiagram X Y)
    (pb : WTypePullback (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)) W
      (unitInv_onPos W)) :
    (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)).p (unitInv_onDir W pb) =
    pb.proj2 := by
  obtain ⟨⟨e, ⟨y, ⟨b, h⟩⟩⟩, pe⟩ := pb
  simp only [unitInv_onDir, polyBetweenToWType, polyBetweenToWTypeObj, WTypePullback.proj2]

/--
The direction map preserves source/assignment.
-/
lemma unitInv_commAssign (W : WTypeDiagram X Y)
    (pb : WTypePullback (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)) W
      (unitInv_onPos W)) :
    (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)).s (unitInv_onDir W pb) =
    W.s pb.proj1 := by
  obtain ⟨⟨e, ⟨y, ⟨b, h⟩⟩⟩, pe⟩ := pb
  simp only [unitInv_onDir, polyBetweenToWType, polyBetweenToWTypeObj,
             wTypeToPolyBetween, wTypeToPolyBetweenObj, WTypePullback.proj1,
             WTypeDiagram.fiberOver, ccrObjMk_family, Over.mk_left, Over.mk_hom]
  rfl

/--
The unit inverse morphism component: G(F(W)) → W.
-/
def unitInv (W : WTypeDiagram X Y) :
    WTypeDiagramHom (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)) W where
  onPos := unitInv_onPos W
  onDir := unitInv_onDir W
  commPos := unitInv_commPos W
  commDir := unitInv_commDir W
  commAssign := unitInv_commAssign W

/--
The position map for the unit morphism: W.B → G(F(W)).B.
-/
def unitHom_onPos (W : WTypeDiagram X Y) :
    W.B → (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)).B :=
  unitBase_invFun W

lemma unitHom_commPos (W : WTypeDiagram X Y) (b : W.B) :
    (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)).t (unitHom_onPos W b) = W.t b := by
  simp only [unitHom_onPos, unitBase_invFun, polyBetweenToWType, polyBetweenToWTypeObj]

def unitHom_onDir (W : WTypeDiagram X Y)
    (pb : WTypePullback W (polyBetweenToWType.obj (wTypeToPolyBetween.obj W))
      (unitHom_onPos W)) :
    W.E :=
  match pb.proj1, pb.proj2, pb.comm with
  | ⟨_, ⟨_, _⟩, ⟨e, _⟩⟩, _, _ => e

lemma unitHom_commDir (W : WTypeDiagram X Y)
    (pb : WTypePullback W (polyBetweenToWType.obj (wTypeToPolyBetween.obj W))
      (unitHom_onPos W)) :
    W.p (unitHom_onDir W pb) = pb.proj2 := by
  obtain ⟨⟨⟨y, ⟨b, h⟩, ⟨e, pe⟩⟩, b'⟩, hcomm⟩ := pb
  simp only [unitHom_onDir, WTypePullback.proj2, unitHom_onPos, unitBase_invFun,
             polyBetweenToWType, polyBetweenToWTypeObj] at hcomm ⊢
  have hb : b = b' := by
    have h1 := congrArg (·.2.val) hcomm
    simp only at h1
    exact h1
  subst hb
  exact pe

lemma unitHom_commAssign (W : WTypeDiagram X Y)
    (pb : WTypePullback W (polyBetweenToWType.obj (wTypeToPolyBetween.obj W))
      (unitHom_onPos W)) :
    W.s (unitHom_onDir W pb) =
    (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)).s pb.proj1 := by
  obtain ⟨⟨⟨y, ⟨b, h⟩, ⟨e, pe⟩⟩, b'⟩, hcomm⟩ := pb
  simp only [unitHom_onDir, polyBetweenToWType, polyBetweenToWTypeObj,
             wTypeToPolyBetween, wTypeToPolyBetweenObj, WTypePullback.proj1,
             WTypeDiagram.fiberOver, ccrObjMk_family, Over.mk_left, Over.mk_hom]

/--
The `unitHom_onDir` function extracts the `W.E` component from the pullback's first
projection. This lemma makes the extraction explicit.
-/
lemma unitHom_onDir_eq (W : WTypeDiagram X Y)
    (pb : WTypePullback W (polyBetweenToWType.obj (wTypeToPolyBetween.obj W))
      (unitHom_onPos W)) :
    unitHom_onDir W pb = pb.proj1.2.snd.val := by
  obtain ⟨⟨⟨y, ⟨b, h⟩, ⟨e, pe⟩⟩, b'⟩, hcomm⟩ := pb
  rfl

/--
Version of `unitHom_onDir_eq` for transported pullbacks.
-/
lemma unitHom_onDir_transport_eq (W : WTypeDiagram X Y)
    {onPos' : W.B → (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)).B}
    (pb : WTypePullback W (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)) onPos')
    (h : onPos' = unitHom_onPos W) :
    unitHom_onDir W (h ▸ pb) = (h ▸ pb).proj1.2.snd.val :=
  unitHom_onDir_eq W (h ▸ pb)

/--
The unit morphism component: W → G(F(W)).
-/
def unitHom (W : WTypeDiagram X Y) :
    WTypeDiagramHom W (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)) where
  onPos := unitHom_onPos W
  onDir := unitHom_onDir W
  commPos := unitHom_commPos W
  commDir := unitHom_commDir W
  commAssign := unitHom_commAssign W

/--
Proof that unitHom ≫ unitInv = id (composition W → G(F(W)) → W equals identity on W).
-/
lemma unitHom_unitInv (W : WTypeDiagram X Y) :
    WTypeDiagramHom.comp (unitInv W) (unitHom W) = WTypeDiagramHom.id W := by
  have hPos : (WTypeDiagramHom.comp (unitInv W) (unitHom W)).onPos =
              (WTypeDiagramHom.id W).onPos := by
    funext b
    simp only [WTypeDiagramHom.comp, WTypeDiagramHom.id, unitInv, unitInv_onPos, unitHom,
               unitHom_onPos]
    exact (unitBase_equiv W).right_inv b
  apply WTypeDiagramHom.ext hPos
  intro pb
  simp only [WTypeDiagramHom.id]
  obtain ⟨⟨e, b⟩, he⟩ := pb
  simp only [WTypeDiagramHom.comp, unitInv, unitInv_onDir, unitHom,
             unitHom_onDir, unitHom_onPos, unitBase_invFun, WTypePullback.proj1,
             WTypePullback.proj2, polyBetweenToWType, polyBetweenToWTypeObj,
             unitInv_onPos, unitBase_toFun]
  rfl

/--
Proof that unitInv ≫ unitHom = id (composition G(F(W)) → W → G(F(W)) equals identity).
-/
lemma unitInv_unitHom (W : WTypeDiagram X Y) :
    WTypeDiagramHom.comp (unitHom W) (unitInv W) =
    WTypeDiagramHom.id (polyBetweenToWType.obj (wTypeToPolyBetween.obj W)) := by
  have hPos : (WTypeDiagramHom.comp (unitHom W) (unitInv W)).onPos =
              (WTypeDiagramHom.id _).onPos := by
    funext x
    simp only [WTypeDiagramHom.comp, WTypeDiagramHom.id, unitInv, unitInv_onPos, unitHom,
               unitHom_onPos]
    exact (unitBase_equiv W).left_inv x
  apply WTypeDiagramHom.ext hPos
  intro pb
  simp only [WTypeDiagramHom.id, WTypePullback.transport_proj1]
  obtain ⟨⟨⟨y, ⟨b, h⟩, ⟨e, pe⟩⟩, ⟨y', ⟨b', h'⟩⟩⟩, hcomm⟩ := pb
  simp only [WTypeDiagramHom.comp, unitInv, unitInv_onDir, unitHom,
             unitHom_onDir, unitHom_onPos, unitBase_invFun, WTypePullback.proj1,
             WTypePullback.proj2, polyBetweenToWType, polyBetweenToWTypeObj,
             unitInv_onPos, unitBase_toFun, wTypeToPolyBetween, wTypeToPolyBetweenObj,
             WTypeDiagram.fiberOver, ccrObjMk_family, Over.mk_left, Over.mk_hom,
             Function.comp_apply] at hcomm ⊢
  have hy : y = W.t b' := congrArg (·.1) hcomm
  have hb : b = b' := congrArg (·.2.val) hcomm
  subst hy hb h'
  rfl

/--
The index type of `F(G(P))(y)` where F is wTypeToPolyBetween and G is
polyBetweenToWType. This is `{ b : (Σ y', ccrIndex (P y')) // b.1 = y }`.
-/
def counitIndexType (P : PolyFunctorBetweenCat X Y) (y : Y) : Type u :=
  { b : (polyBetweenToWType.obj P).B // (polyBetweenToWType.obj P).t b = y }

/--
Forward direction of counit index equivalence: from `F(G(P))(y)` index to `P(y)`
index. Maps `⟨⟨y, i⟩, rfl⟩` to `i`.
-/
def counitIndex_toFun (P : PolyFunctorBetweenCat X Y) (y : Y)
    (b : counitIndexType P y) : ccrIndex (P y) :=
  match b.val, b.property with
  | ⟨y', i⟩, h =>
    match y', i, h with
    | _, i, rfl => i

/--
Backward direction of counit index equivalence: from `P(y)` index to `F(G(P))(y)`
index. Maps `i` to `⟨⟨y, i⟩, rfl⟩`.
-/
def counitIndex_invFun (P : PolyFunctorBetweenCat X Y) (y : Y)
    (i : ccrIndex (P y)) : counitIndexType P y :=
  ⟨⟨y, i⟩, rfl⟩

/--
The counit index equivalence: `counitIndexType P y ≃ ccrIndex (P y)`.
-/
def counitIndex_equiv (P : PolyFunctorBetweenCat X Y) (y : Y) :
    counitIndexType P y ≃ ccrIndex (P y) where
  toFun := counitIndex_toFun P y
  invFun := counitIndex_invFun P y
  left_inv := fun ⟨⟨y', i⟩, h⟩ => by
    simp only [counitIndex_toFun, counitIndex_invFun]
    match y', i, h with
    | _, _, rfl => rfl
  right_inv := fun i => by
    simp only [counitIndex_invFun, counitIndex_toFun]

/--
The fiber map underlying the counit fiber morphism.
-/
def counitFiberMap (P : PolyFunctorBetweenCat X Y) (y : Y) (i : ccrIndex (P y)) :
    (ccrFamily (P y) i).left →
      (ccrFamily (wTypeToPolyBetween.obj (polyBetweenToWType.obj P) y)
        (counitIndex_invFun P y i)).left :=
  (polyBetweenToWTypeObj_fiber_equiv P y i).symm.toFun

lemma counitFiberMap_comm (P : PolyFunctorBetweenCat X Y) (y : Y) (i : ccrIndex (P y)) :
    (ccrFamily (P y) i).hom =
      (ccrFamily (wTypeToPolyBetween.obj (polyBetweenToWType.obj P) y)
        (counitIndex_invFun P y i)).hom ∘ counitFiberMap P y i := by
  funext e
  simp only [Function.comp_apply, counitFiberMap, polyBetweenToWTypeObj_fiber_equiv,
             polyBetweenToWType, polyBetweenToWTypeObj, WTypeDiagram.fiberOver, Over.mk_hom,
             wTypeToPolyBetween, wTypeToPolyBetweenObj, ccrObjMk_family, Over.mk_left,
             counitIndex_invFun]
  rfl

/--
The fiber morphism for the counit. For each `b : counitIndexType P y`, produces
a morphism in `Over X` from `ccrFamily (P y) (counitIndex_toFun P y b)` to
`ccrFamily (wTypeToPolyBetween.obj (polyBetweenToWType.obj P) y) b`.
-/
def counitFiberMor (P : PolyFunctorBetweenCat X Y) (y : Y)
    (b : counitIndexType P y) :
    ccrFamily (P y) (counitIndex_toFun P y b) ⟶
      ccrFamily (wTypeToPolyBetween.obj (polyBetweenToWType.obj P) y) b := by
  obtain ⟨⟨y', i⟩, h⟩ := b
  simp only [counitIndex_toFun] at h ⊢
  subst h
  exact Over.homMk (counitFiberMap P y' i) (counitFiberMap_comm P y' i)

/--
The counit morphism component at y: F(G(P))(y) -> P(y) in CoprodCovarRepCat.
-/
def counitHom_component (P : PolyFunctorBetweenCat X Y) (y : Y) :
    wTypeToPolyBetween.obj (polyBetweenToWType.obj P) y ⟶ P y :=
  ccrHomMk (counitIndex_toFun P y) (counitFiberMor P y)

/--
The counit morphism: F(G(P)) -> P in PolyFunctorBetweenCat.
-/
def counitHom (P : PolyFunctorBetweenCat X Y) :
    wTypeToPolyBetween.obj (polyBetweenToWType.obj P) ⟶ P :=
  counitHom_component P

/--
The inverse fiber map for the counit inverse.
-/
def counitInvFiberMap (P : PolyFunctorBetweenCat X Y) (y : Y) (i : ccrIndex (P y)) :
    (ccrFamily (wTypeToPolyBetween.obj (polyBetweenToWType.obj P) y)
      (counitIndex_invFun P y i)).left → (ccrFamily (P y) i).left :=
  (polyBetweenToWTypeObj_fiber_equiv P y i).toFun

lemma counitInvFiberMap_comm (P : PolyFunctorBetweenCat X Y) (y : Y) (i : ccrIndex (P y)) :
    counitInvFiberMap P y i ≫
      (ccrFamily (P y) i).hom =
      (ccrFamily (wTypeToPolyBetween.obj (polyBetweenToWType.obj P) y)
        (counitIndex_invFun P y i)).hom := by
  funext e
  simp only [CategoryStruct.comp, Function.comp_apply, counitInvFiberMap,
             polyBetweenToWTypeObj_fiber_equiv, polyBetweenToWType, polyBetweenToWTypeObj,
             WTypeDiagram.fiberOver, Over.mk_hom, wTypeToPolyBetween, wTypeToPolyBetweenObj,
             ccrObjMk_family, Over.mk_left, counitIndex_invFun]
  obtain ⟨⟨y', i', e'⟩, h⟩ := e
  cases h
  rfl

/--
The inverse fiber morphism for the counit inverse.
-/
def counitInvFiberMor (P : PolyFunctorBetweenCat X Y) (y : Y)
    (i : ccrIndex (P y)) :
    ccrFamily (wTypeToPolyBetween.obj (polyBetweenToWType.obj P) y)
      (counitIndex_invFun P y i) ⟶ ccrFamily (P y) i :=
  Over.homMk (counitInvFiberMap P y i) (counitInvFiberMap_comm P y i)

/--
The counit inverse morphism component at y: P(y) -> F(G(P))(y) in CoprodCovarRepCat.
-/
def counitInv_component (P : PolyFunctorBetweenCat X Y) (y : Y) :
    P y ⟶ wTypeToPolyBetween.obj (polyBetweenToWType.obj P) y :=
  ccrHomMk (counitIndex_invFun P y) (counitInvFiberMor P y)

/--
The counit inverse morphism: P -> F(G(P)) in PolyFunctorBetweenCat.
-/
def counitInv (P : PolyFunctorBetweenCat X Y) :
    P ⟶ wTypeToPolyBetween.obj (polyBetweenToWType.obj P) :=
  counitInv_component P

/--
Proof that counitInv ≫ counitHom = id (composition P → F(G(P)) → P equals identity).
-/
lemma counitInv_counitHom (P : PolyFunctorBetweenCat X Y) :
    counitInv P ≫ counitHom P = 𝟙 P := by
  funext y
  apply ccrHom_ext (hbase := rfl)
  simp only [eqToHom_refl, Category.comp_id]

private lemma counitHom_counitInv_base (P : PolyFunctorBetweenCat X Y) (y : Y) :
    ((counitHom P ≫ counitInv P) y).base =
      (𝟙 (wTypeToPolyBetween.obj (polyBetweenToWType.obj P)) y).base := by
  funext ⟨⟨y', i⟩, h⟩
  subst h
  rfl

private lemma counitInvFiberMap_counitFiberMap (P : PolyFunctorBetweenCat X Y)
    (y : Y) (i : ccrIndex (P y)) :
    counitInvFiberMap P y i ∘ counitFiberMap P y i = id := by
  funext e
  simp only [Function.comp_apply, id_eq, counitFiberMap, counitInvFiberMap]
  exact (polyBetweenToWTypeObj_fiber_equiv P y i).right_inv e

private lemma counitFiberMap_counitInvFiberMap (P : PolyFunctorBetweenCat X Y)
    (y : Y) (i : ccrIndex (P y)) :
    counitFiberMap P y i ∘ counitInvFiberMap P y i = id := by
  funext e
  simp only [Function.comp_apply, id_eq, counitFiberMap, counitInvFiberMap]
  exact (polyBetweenToWTypeObj_fiber_equiv P y i).left_inv e

/--
The counit index after round-trip F(G(P)) -> P -> F(G(P)) at `⟨y', i⟩` equals `⟨y', i⟩`.
-/
private lemma counitIndex_roundtrip (P : PolyFunctorBetweenCat X Y) (y' : Y)
    (i : ccrIndex (P y')) :
    counitIndex_invFun P y' (counitIndex_toFun P y' ⟨⟨y', i⟩, rfl⟩) = ⟨⟨y', i⟩, rfl⟩ := by
  simp only [counitIndex_toFun, counitIndex_invFun]

/--
For `⟨⟨y', i⟩, rfl⟩ : counitIndexType P y'`, the family at this index equals the family
at the `counitIndex_invFun P y' i` index.
-/
private lemma counitFamily_eq (P : PolyFunctorBetweenCat X Y) (y' : Y)
    (i : ccrIndex (P y')) :
    ccrFamily (wTypeToPolyBetween.obj (polyBetweenToWType.obj P) y')
      ⟨⟨y', i⟩, rfl⟩ =
    ccrFamily (wTypeToPolyBetween.obj (polyBetweenToWType.obj P) y')
      (counitIndex_invFun P y' i) := rfl

/--
Abbreviation for the W-type-based polynomial functor category object F(G(P)).
-/
private abbrev FGP (P : PolyFunctorBetweenCat X Y) :=
  wTypeToPolyBetween.obj (polyBetweenToWType.obj P)

/--
Identity in FamilyCat at a component equals identity in the fiber category.
-/
private lemma family_id_component (P : PolyFunctorBetweenCat X Y) (y' : Y) :
    (𝟙 (FGP P) y') = GrothendieckContra'.id (FGP P y') := rfl

/--
The type of elements in the fiber at index `⟨⟨y', i⟩, rfl⟩` for FGP.
-/
private abbrev FGPFiberElemType (P : PolyFunctorBetweenCat X Y) (y' : Y)
    (i : ccrIndex (P y')) :=
  (((familyFunctor (Over X) ⋙ Cat.opFunctor').map (𝟙 (FGP P) y').base).toFunctor.obj
      (FGP P y').fiber ⟨⟨y', i⟩, rfl⟩).left

/--
Step 1a: The composition base at `⟨⟨y', i⟩, rfl⟩` maps to `⟨⟨y', i⟩, rfl⟩`.
Specifically, `counitIndex_invFun (counitIndex_toFun ⟨⟨y', i⟩, rfl⟩) = ⟨⟨y', i⟩, rfl⟩`.
-/
private lemma counitHom_counitInv_base_at_idx (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) :
    ((counitHom P ≫ counitInv P) y').base ⟨⟨y', i⟩, rfl⟩ = ⟨⟨y', i⟩, rfl⟩ := rfl

/--
Step 1b: The counit reindex at `⟨⟨y', i⟩, rfl⟩` gives `i`.
-/
private lemma counitHom_reindex_at_idx (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) :
    (counitHom P y').base ⟨⟨y', i⟩, rfl⟩ = i := rfl

/--
The counit reindex using `ccrReindex` at `⟨⟨y', i⟩, rfl⟩` gives `i`.
-/
private lemma counitHom_ccrReindex_at_idx (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) :
    ccrReindex (counitHom P y') ⟨⟨y', i⟩, rfl⟩ = i := rfl

/--
The fiber morphism of counitHom at index `⟨⟨y', i⟩, rfl⟩` equals `counitFiberMor`.
-/
private lemma counitHom_fiberMor_at_idx (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) :
    ccrFiberMor (counitHom P y') ⟨⟨y', i⟩, rfl⟩ =
      counitFiberMor P y' ⟨⟨y', i⟩, rfl⟩ := by
  simp only [counitHom, counitHom_component, ccrHomMk_fiberMor]

/--
The fiber morphism of counitInv at index `i` equals `counitInvFiberMor`.
-/
private lemma counitInv_fiberMor_at_idx (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) :
    ccrFiberMor (counitInv P y') i = counitInvFiberMor P y' i := by
  simp only [counitInv, counitInv_component, ccrHomMk_fiberMor]

/--
The composed fiber morphism at index `⟨⟨y', i⟩, rfl⟩` decomposes into
`counitInvFiberMor ≫ counitFiberMor`.
-/
private lemma comp_fiberMor_at_idx (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) :
    ccrFiberMor ((counitHom P ≫ counitInv P) y') ⟨⟨y', i⟩, rfl⟩ =
      counitInvFiberMor P y' i ≫ counitFiberMor P y' ⟨⟨y', i⟩, rfl⟩ := by
  -- In FamilyCat, (f ≫ g) y' = f y' ≫ g y' definitionally
  change ccrFiberMor (counitHom P y' ≫ counitInv P y') ⟨⟨y', i⟩, rfl⟩ = _
  simp only [ccrComp_fiberMor, counitHom_ccrReindex_at_idx, counitInv_fiberMor_at_idx,
      counitHom_fiberMor_at_idx]

/--
The `.left` of `counitFiberMor` at `⟨⟨y', i⟩, rfl⟩` equals `counitFiberMap`.
-/
private lemma counitFiberMor_left_at_idx (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) :
    (counitFiberMor P y' ⟨⟨y', i⟩, rfl⟩).left = counitFiberMap P y' i := rfl

/--
The `.left` of `counitInvFiberMor` equals `counitInvFiberMap`.
-/
private lemma counitInvFiberMor_left (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) :
    (counitInvFiberMor P y' i).left = counitInvFiberMap P y' i := by
  simp only [counitInvFiberMor, Over.homMk_left]

/--
The `.left` of the composed fiber morphism equals `counitFiberMap ∘ counitInvFiberMap`.
The composition order is reversed because `.left` of `f ≫ g` in Over is `g.left ∘ f.left`.
-/
private lemma comp_fiberMor_left_at_idx (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) :
    (ccrFiberMor ((counitHom P ≫ counitInv P) y') ⟨⟨y', i⟩, rfl⟩).left =
      counitFiberMap P y' i ∘ counitInvFiberMap P y' i := by
  rw [comp_fiberMor_at_idx]
  simp only [Over_comp_left, counitInvFiberMor_left, counitFiberMor_left_at_idx]

/--
The `.left` of the composed fiber morphism is the identity function.
-/
private lemma comp_fiberMor_left_is_id (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) :
    (ccrFiberMor ((counitHom P ≫ counitInv P) y') ⟨⟨y', i⟩, rfl⟩).left = id := by
  rw [comp_fiberMor_left_at_idx, counitFiberMap_counitInvFiberMap]

/--
Sub-lemma 1a: The composition in FamilyCat at y' equals pointwise composition.
-/
private lemma counitHom_counitInv_comp_at_y (P : PolyFunctorBetweenCat X Y) (y' : Y) :
    (counitHom P ≫ counitInv P) y' =
      counitHom_component P y' ≫ counitInv_component P y' := rfl

/--
The `.fiber` field of a morphism equals `ccrFiberMor` applied pointwise.
-/
private lemma fiber_eq_ccrFiberMor {x y : CoprodCovarRepCat (Over X)}
    (f : x ⟶ y) (i : ccrIndex x) :
    f.fiber i = ccrFiberMor f i := rfl

/--
The fiber-level equality proof generated by rewriting with base equality.
-/
private def counitHom_counitInv_fiber_eq_proof (P : PolyFunctorBetweenCat X Y) (y' : Y) :
    ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
        ((counitHom P ≫ counitInv P) y').base).toFunctor.obj (FGP P y').fiber =
      ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
        (𝟙 (FGP P) y').base).toFunctor.obj (FGP P y').fiber := by
  rw [counitHom_counitInv_base P y']

/--
The fiber of `(counitHom P ≫ counitInv P) y'` at index `⟨⟨y', i⟩, rfl⟩` equals the
composition of the inverse and forward fiber morphisms.
-/
private lemma comp_fiber_at_idx (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) :
    ((counitHom P ≫ counitInv P) y').fiber ⟨⟨y', i⟩, rfl⟩ =
      counitInvFiberMor P y' i ≫ counitFiberMor P y' ⟨⟨y', i⟩, rfl⟩ :=
  comp_fiberMor_at_idx P y' i

/--
The source and target of the fiber equality at index `⟨⟨y', i⟩, rfl⟩` are
definitionally equal (both are `(FGP P y').fiber ⟨⟨y', i⟩, rfl⟩`).
-/
private lemma fiber_eq_proof_at_idx_source_eq_target (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) :
    ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
        ((counitHom P ≫ counitInv P) y').base).toFunctor.obj (FGP P y').fiber ⟨⟨y', i⟩, rfl⟩ =
    ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
        (𝟙 (FGP P) y').base).toFunctor.obj (FGP P y').fiber ⟨⟨y', i⟩, rfl⟩ :=
  rfl

/--
The `.fiber` at the specific index has `.left = id`.
This factors out the computation of `(counitHom ≫ counitInv).fiber idx` without
dealing with the `eqToHom` composition.
-/
private lemma comp_fiber_at_idx_left_is_id (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) :
    (((counitHom P ≫ counitInv P) y').fiber ⟨⟨y', i⟩, rfl⟩).left = id := by
  rw [fiber_eq_ccrFiberMor]
  exact comp_fiberMor_left_is_id P y' i

/--
When the source and target at a particular index are definitionally equal,
the `eqToHom` at that index has `.left = id`.
-/
private lemma eqToHom_at_idx_left_eq_id (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y'))
    (h : ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
            ((counitHom P ≫ counitInv P) y').base).toFunctor.obj (FGP P y').fiber =
         ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
            (𝟙 (FGP P) y').base).toFunctor.obj (FGP P y').fiber) :
    ((eqToHom h) ⟨⟨y', i⟩, rfl⟩).left = id := by
  let idx : ccrIndex (FGP P y') := ⟨⟨y', i⟩, rfl⟩
  change ((eqToHom h) idx).left = id
  -- At idx, both functions evaluate to the same type definitionally
  -- So congrFun h idx : F idx = G idx is propositionally rfl
  have h_at_idx_eq : congrFun h idx = rfl := Subsingleton.elim _ _
  -- Therefore (congrFun h idx).symm = rfl, and eqToHom rfl = 𝟙
  have h_symm_eq : (congrFun h idx).symm = rfl := by rw [h_at_idx_eq]
  -- Show the result using the helper lemma
  rw [eqToHom_catOp_pi_at_idx h idx, h_symm_eq]
  rfl

/--
The composed fiber with eqToHom at the specific index has `.left = id`.
This is because in the opposite of a pi category, the composition is reversed,
and the eqToHom at this index is the identity (since the types are definitionally equal).
-/
private lemma comp_fiber_eqToHom_at_idx_left_is_id (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) :
    ((((counitHom P ≫ counitInv P) y').fiber ≫
        eqToHom (counitHom_counitInv_fiber_eq_proof P y')) ⟨⟨y', i⟩, rfl⟩).left = id := by
  let idx : ccrIndex (FGP P y') := ⟨⟨y', i⟩, rfl⟩
  let h := counitHom_counitInv_fiber_eq_proof P y'
  have comp_eq : (((counitHom P ≫ counitInv P) y').fiber ≫ eqToHom h) idx =
      (eqToHom h) idx ≫ ((counitHom P ≫ counitInv P) y').fiber idx := rfl
  rw [comp_eq]
  rw [Over_comp_left]
  have fiber_left_id : (((counitHom P ≫ counitInv P) y').fiber idx).left = id :=
    comp_fiber_at_idx_left_is_id P y' i
  rw [fiber_left_id]
  simp only [Function.id_comp]
  exact eqToHom_at_idx_left_eq_id P y' i h

private lemma counitHom_counitInv_lhs_step (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) (e : FGPFiberElemType P y' i) :
    ((((counitHom P ≫ counitInv P) y').fiber ≫
        eqToHom (counitHom_counitInv_fiber_eq_proof P y')) ⟨⟨y', i⟩, rfl⟩).left e =
      e := by
  rw [congrFun (comp_fiber_eqToHom_at_idx_left_is_id P y' i) e]
  rfl

/--
The identity fiber in FamilyCat at y' is an eqToHom.
-/
private lemma id_fiber_is_eqToHom (P : PolyFunctorBetweenCat X Y) (y' : Y) :
    (𝟙 (FGP P) y').fiber = eqToHom (GrothendieckContra'.id_base_eq (FGP P y')).symm := rfl

/--
Step 2a: Show identity fiber at index equals eqToHom applied at that index.
-/
private lemma counitHom_counitInv_rhs_step_a (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) :
    (𝟙 (FGP P) y').fiber ⟨⟨y', i⟩, rfl⟩ =
      eqToHom (GrothendieckContra'.id_base_eq (FGP P y')).symm ⟨⟨y', i⟩, rfl⟩ := rfl

/--
Step 2b: Show eqToHom at index applied to `.left` and `e` equals `e`.
The proof uses the fact that `id_base_eq` is definitionally `rfl` due to
how the functor map of identity works.
-/
private lemma counitHom_counitInv_rhs_step_b (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) (e : FGPFiberElemType P y' i) :
    (eqToHom (GrothendieckContra'.id_base_eq (FGP P y')).symm ⟨⟨y', i⟩, rfl⟩).left e = e := by
  -- The id_base_eq proof is definitionally rfl, making the eqToHom trivial
  -- The goal reduces to showing identity Over morphism .left applied to e equals e
  -- Over.id_left: (𝟙 U).left = 𝟙 U.left
  -- In Type, 𝟙 is id, so (𝟙 U.left) e = e is rfl
  rfl

private lemma counitHom_counitInv_rhs_step (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) (e : FGPFiberElemType P y' i) :
    ((𝟙 (FGP P) y').fiber ⟨⟨y', i⟩, rfl⟩).left e = e :=
  counitHom_counitInv_rhs_step_b P y' i e

/--
The main fiber equality, composed from the two steps.
-/
private lemma counitHom_counitInv_fiber_eq (P : PolyFunctorBetweenCat X Y)
    (y' : Y) (i : ccrIndex (P y')) (e : FGPFiberElemType P y' i) :
    ((((counitHom P ≫ counitInv P) y').fiber ≫
        eqToHom (by rw [counitHom_counitInv_base P y'])) ⟨⟨y', i⟩, rfl⟩).left e =
      ((𝟙 (FGP P) y').fiber ⟨⟨y', i⟩, rfl⟩).left e :=
  (counitHom_counitInv_lhs_step P y' i e).trans
    (counitHom_counitInv_rhs_step P y' i e).symm

lemma counitHom_counitInv (P : PolyFunctorBetweenCat X Y) :
    counitHom P ≫ counitInv P =
      𝟙 (wTypeToPolyBetween.obj (polyBetweenToWType.obj P)) := by
  funext y
  fapply GrothendieckContra'.ext
  case w_base => exact counitHom_counitInv_base P y
  case w_fiber =>
    funext ⟨⟨y', i⟩, h⟩
    subst h
    ext e
    dsimp only [polyBetweenToWType, polyBetweenToWTypeObj] at e ⊢
    exact counitHom_counitInv_fiber_eq P y' i e

/-! ### Triangle Identity

The triangle identity for the equivalence: F(η_W) ≫ ε_{FW} = id_{FW}
where F = wTypeToPolyBetween, G = polyBetweenToWType, η = unit, ε = counit.
-/

/--
The base component of the triangle identity composition equals identity base.
-/
private lemma functor_unitIso_comp_base (W : WTypeDiagram X Y) (y : Y) :
    ((wTypeToPolyBetween.map (unitHom W) ≫
      counitHom (wTypeToPolyBetween.obj W)) y).base =
    (𝟙 (wTypeToPolyBetween.obj W) y).base := by
  funext ⟨b, hb⟩
  subst hb
  rfl

/--
Type alias for the fiber element type at index ⟨b, rfl⟩ in F(W)(W.t b).
-/
private abbrev FWFiberElemType (W : WTypeDiagram X Y) (b : W.B) : Type u :=
  ((wTypeToPolyBetweenObj W (W.t b)).fiber ⟨b, rfl⟩).left

/--
The fiber equality for the triangle identity at index ⟨b, rfl⟩.
The proof shows that the composition F(unitHom W) ≫ counitHom(F(W)) acts as
identity on fibers.
-/
private lemma functor_unitIso_comp_fiber_eq_goal (W : WTypeDiagram X Y) (b : W.B) :
    ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
        (𝟙 (wTypeToPolyBetween.obj W) (W.t b)).base).toFunctor.obj
      (wTypeToPolyBetween.obj W (W.t b)).fiber =
    (wTypeToPolyBetweenObj W (W.t b)).fiber := by
  dsimp only [wTypeToPolyBetween, Functor.comp_map]
  rfl

private lemma triangle_comp_fiber_left_is_id (W : WTypeDiagram X Y) (b : W.B) :
    (((wTypeToPolyBetween.map (unitHom W) ≫
        counitHom (wTypeToPolyBetween.obj W)) (W.t b)).fiber ⟨b, rfl⟩).left = id := by
  dsimp only [wTypeToPolyBetween, wTypeToPolyBetweenMap, wTypeToPolyBetweenObj,
              unitHom, counitHom, counitHom_component, counitFiberMor, counitFiberMap,
              ccrHomMk, ccrObjMk, ccrHomMk_fiberMor, ccrFiberMor, ccrComp_fiberMor,
              WTypeDiagram.fiberOver, Over.homMk_left, Function.comp_apply,
              wTypeToPolyBetweenFiberMor, wTypeToPolyBetweenReindex,
              unitHom_onPos, unitHom_onDir, unitBase_invFun,
              polyBetweenToWType, polyBetweenToWTypeObj,
              counitIndex_toFun, polyBetweenToWTypeObj_fiber_equiv,
              Over_comp_left]
  rfl

private lemma triangle_eqToHom_left_is_id (W : WTypeDiagram X Y) (b : W.B)
    (h : ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
            ((wTypeToPolyBetween.map (unitHom W) ≫
              counitHom (wTypeToPolyBetween.obj W)) (W.t b)).base).toFunctor.obj
          (wTypeToPolyBetween.obj W (W.t b)).fiber =
        ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
            (𝟙 (wTypeToPolyBetween.obj W) (W.t b)).base).toFunctor.obj
          (wTypeToPolyBetween.obj W (W.t b)).fiber) :
    ((eqToHom h) ⟨b, rfl⟩).left = id := by
  let idx : ccrIndex (wTypeToPolyBetween.obj W (W.t b)) := ⟨b, rfl⟩
  have h_at_idx_eq : congrFun h idx = rfl := Subsingleton.elim _ _
  have h_symm_eq : (congrFun h idx).symm = rfl := by rw [h_at_idx_eq]
  rw [eqToHom_catOp_pi_at_idx h idx, h_symm_eq]
  rfl

private lemma triangle_comp_fiber_eqToHom_at_idx_left_is_id (W : WTypeDiagram X Y)
    (b : W.B)
    (h : ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
            ((wTypeToPolyBetween.map (unitHom W) ≫
              counitHom (wTypeToPolyBetween.obj W)) (W.t b)).base).toFunctor.obj
          (wTypeToPolyBetween.obj W (W.t b)).fiber =
        ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
            (𝟙 (wTypeToPolyBetween.obj W) (W.t b)).base).toFunctor.obj
          (wTypeToPolyBetween.obj W (W.t b)).fiber) :
    ((((wTypeToPolyBetween.map (unitHom W) ≫
        counitHom (wTypeToPolyBetween.obj W)) (W.t b)).fiber ≫
      eqToHom h) ⟨b, rfl⟩).left = id := by
  let idx : ccrIndex (wTypeToPolyBetween.obj W (W.t b)) := ⟨b, rfl⟩
  have comp_eq : (((wTypeToPolyBetween.map (unitHom W) ≫
      counitHom (wTypeToPolyBetween.obj W)) (W.t b)).fiber ≫ eqToHom h) idx =
      (eqToHom h) idx ≫ ((wTypeToPolyBetween.map (unitHom W) ≫
        counitHom (wTypeToPolyBetween.obj W)) (W.t b)).fiber idx := rfl
  rw [comp_eq]
  rw [Over_comp_left]
  have fiber_left_id : (((wTypeToPolyBetween.map (unitHom W) ≫
      counitHom (wTypeToPolyBetween.obj W)) (W.t b)).fiber idx).left = id :=
    triangle_comp_fiber_left_is_id W b
  rw [fiber_left_id]
  simp only [Function.id_comp]
  exact triangle_eqToHom_left_is_id W b h

private def triangle_fiber_eq_proof (W : WTypeDiagram X Y) (b : W.B) :
    ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
        ((wTypeToPolyBetween.map (unitHom W) ≫
          counitHom (wTypeToPolyBetween.obj W)) (W.t b)).base).toFunctor.obj
      (wTypeToPolyBetween.obj W (W.t b)).fiber =
    ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
        (𝟙 (wTypeToPolyBetween.obj W) (W.t b)).base).toFunctor.obj
      (wTypeToPolyBetween.obj W (W.t b)).fiber := by
  rw [functor_unitIso_comp_base W (W.t b)]

private lemma functor_unitIso_comp_fiber_eq (W : WTypeDiagram X Y) (b : W.B)
    (e : FWFiberElemType W b) :
    ((((wTypeToPolyBetween.map (unitHom W) ≫
        counitHom (wTypeToPolyBetween.obj W)) (W.t b)).fiber ≫
      eqToHom (triangle_fiber_eq_proof W b)) ⟨b, rfl⟩).left e =
    ((𝟙 (wTypeToPolyBetween.obj W) (W.t b)).fiber ⟨b, rfl⟩).left e := by
  rw [congrFun (triangle_comp_fiber_eqToHom_at_idx_left_is_id W b (triangle_fiber_eq_proof W b)) e]
  rfl

/--
The triangle identity: applying F to the unit, then the counit, gives identity.
F(unitHom W) ≫ counitHom (F W) = id (F W)
-/
lemma functor_unitIso_comp (W : WTypeDiagram X Y) :
    wTypeToPolyBetween.map (unitHom W) ≫ counitHom (wTypeToPolyBetween.obj W) =
      𝟙 (wTypeToPolyBetween.obj W) := by
  funext y
  fapply GrothendieckContra'.ext
  case w_base =>
    funext ⟨b, hb⟩
    subst hb
    rfl
  case w_fiber =>
    funext ⟨b, hb⟩
    subst hb
    apply Over.OverMorphism.ext
    funext e
    exact functor_unitIso_comp_fiber_eq W b e

/-! ### Unit Naturality

Proof that unitHom is natural: for f : W ⟶ W', f ≫ unitHom W' = unitHom W ≫ G(F(f)).
-/

/--
The unit morphism is natural.
-/
lemma unitHom_naturality {W W' : WTypeDiagram X Y} (f : WTypeDiagramHom W W') :
    WTypeDiagramHom.comp (unitHom W') f =
      WTypeDiagramHom.comp (polyBetweenToWType.map (wTypeToPolyBetween.map f)) (unitHom W) := by
  have hPos : ((unitHom W').comp f).onPos =
      ((polyBetweenToWType.map (wTypeToPolyBetween.map f)).comp (unitHom W)).onPos := by
    funext b
    simp only [WTypeDiagramHom.comp, unitHom, unitHom_onPos, unitBase_invFun,
               polyBetweenToWType, polyBetweenToWTypeMap,
               wTypeToPolyBetween, wTypeToPolyBetweenMap]
    apply Sigma.ext
    · simp only [polyBetweenToWTypeObj, wTypeToPolyBetweenObj, WTypeDiagram.fiberOver]
      exact f.commPos b
    · apply subtype_heq_of_val_eq
      · simp only [polyBetweenToWTypeObj, wTypeToPolyBetweenObj, WTypeDiagram.fiberOver]
        dsimp only [unitBase_invFun, polyBetweenToWTypeReindex, wTypeToPolyBetweenMap,
                    Function.comp_apply]
        exact congrArg (fun y => (fun b' => W'.t b' = y)) (f.commPos b)
      · rfl
  have hDir : ∀ pb, ((unitHom W').comp f).onDir pb =
      ((polyBetweenToWType.map (wTypeToPolyBetween.map f)).comp (unitHom W)).onDir (hPos ▸ pb) := by
    intro pb
    obtain ⟨⟨qe, b⟩, hcomm⟩ := pb
    obtain ⟨y, ⟨⟨b', hb'⟩, ⟨e', pe'⟩⟩⟩ := qe
    dsimp at hcomm
    obtain ⟨hy, heq⟩ := Sigma.mk.inj hcomm
    subst hy
    have hb'_eq : b' = f.onPos b := congrArg Subtype.val (eq_of_heq heq)
    subst hb'_eq
    let pb' : WTypePullback W (polyBetweenToWType.obj (wTypeToPolyBetween.obj W'))
                ((unitHom W').comp f).onPos :=
      ⟨(⟨W'.t (f.onPos b), ⟨⟨f.onPos b, hb'⟩, ⟨e', pe'⟩⟩⟩, b), hcomm⟩
    have hval : (hPos ▸ pb').val = pb'.val := by
      simp only [WTypePullback]
      exact Eq.rec (motive := fun _ h =>
        (h ▸ pb').val = pb'.val) rfl hPos
    have hproj1 : (hPos ▸ pb').val.1 = pb'.val.1 := congrArg (·.1) hval
    have hproj2 : (hPos ▸ pb').val.2 = pb'.val.2 := congrArg (·.2) hval
    simp only [WTypeDiagramHom.comp, unitHom, unitHom_onDir,
               polyBetweenToWType, polyBetweenToWTypeMap,
               WTypePullback.proj1, WTypePullback.proj2]
    congr 1
    apply Subtype.ext
    apply Prod.ext
    · simp only [WTypePullback.mk, unitHom_onPos, unitBase_invFun]
      rw [polyBetweenToWTypeMap_fiberCast_val_wType, WTypePullback.proj1, hproj1]
    · simp only [WTypePullback.mk, unitHom_onPos, unitBase_invFun]
      exact hproj2.symm
  exact WTypeDiagramHom.ext hPos hDir

/-! ### Counit Naturality

Proof that counitHom is natural: for g : P ⟶ P', F(G(g)) ≫ counitHom P' = counitHom P ≫ g.
-/

/--
The counit morphism is natural.
-/
lemma counitHom_naturality {P P' : PolyFunctorBetweenCat X Y} (g : P ⟶ P') :
    wTypeToPolyBetween.map (polyBetweenToWType.map g) ≫ counitHom P' = counitHom P ≫ g := by
  funext y
  fapply GrothendieckContra'.ext
  case w_base =>
    funext ⟨⟨y', i⟩, h⟩
    subst h
    rfl
  case w_fiber =>
    funext ⟨⟨y', i⟩, h⟩
    subst h
    apply Over.OverMorphism.ext
    funext e
    let idx : ccrIndex (wTypeToPolyBetween.obj (polyBetweenToWType.obj P)
                ((polyBetweenToWType.obj P).t ⟨y', i⟩)) := ⟨⟨y', i⟩, rfl⟩
    have h_base_eq : ((wTypeToPolyBetween.map (polyBetweenToWType.map g) ≫
          counitHom P') ((polyBetweenToWType.obj P).t ⟨y', i⟩)).base =
        ((counitHom P ≫ g) ((polyBetweenToWType.obj P).t ⟨y', i⟩)).base := by
      funext ⟨⟨y'', j⟩, heq⟩
      dsimp only [polyBetweenToWType, polyBetweenToWTypeObj, WTypeDiagram.t] at heq
      subst heq
      dsimp only [wTypeToPolyBetween, counitHom, counitIndex_toFun]
      rfl
    have h_fiber_eq : ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
            ((wTypeToPolyBetween.map (polyBetweenToWType.map g) ≫
              counitHom P') ((polyBetweenToWType.obj P).t ⟨y', i⟩)).base).toFunctor.obj
          (P' ((polyBetweenToWType.obj P).t ⟨y', i⟩)).fiber =
        ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
            ((counitHom P ≫ g) ((polyBetweenToWType.obj P).t ⟨y', i⟩)).base).toFunctor.obj
          (P' ((polyBetweenToWType.obj P).t ⟨y', i⟩)).fiber :=
      congrArg (fun f => ((familyFunctor (Over X) ⋙ Cat.opFunctor').map f).toFunctor.obj
        (P' ((polyBetweenToWType.obj P).t ⟨y', i⟩)).fiber) h_base_eq
    have h_at_idx : congrFun h_fiber_eq idx = rfl := Subsingleton.elim _ _
    have h_symm : (congrFun h_fiber_eq idx).symm = rfl := by rw [h_at_idx]
    have eqToHom_is_id : ((eqToHom h_fiber_eq) idx).left = id := by
      rw [eqToHom_catOp_pi_at_idx h_fiber_eq idx, h_symm]
      rfl
    have lhs_unfold : ((((wTypeToPolyBetween.map (polyBetweenToWType.map g) ≫
          counitHom P') ((polyBetweenToWType.obj P).t ⟨y', i⟩)).fiber ≫
        eqToHom h_fiber_eq) idx) =
        (eqToHom h_fiber_eq idx) ≫
        ((wTypeToPolyBetween.map (polyBetweenToWType.map g) ≫
          counitHom P') ((polyBetweenToWType.obj P).t ⟨y', i⟩)).fiber idx := rfl
    rw [lhs_unfold, Over_comp_left, eqToHom_is_id]
    simp only [Function.comp_apply, id]
    dsimp only [wTypeToPolyBetween, wTypeToPolyBetweenMap, wTypeToPolyBetweenObj,
                wTypeToPolyBetweenFiberMor, wTypeToPolyBetweenReindex,
                polyBetweenToWType, polyBetweenToWTypeMap, polyBetweenToWTypeObj,
                polyBetweenToWTypeReindex, polyBetweenToWTypeMap_fiberCast,
                counitHom, counitHom_component, counitFiberMap, counitFiberMor,
                ccrHomMk, ccrHomMk_fiberMor, ccrFiberMor, ccrComp_fiberMor,
                GrothendieckContra'.comp_base, GrothendieckContra'.comp_fiber,
                CategoryStruct.comp, Function.comp_apply, Over_comp_left,
                WTypeDiagram.fiberOver, Over.homMk_left,
                counitIndex_invFun, counitIndex_toFun, idx]
    rfl

/-! ### The Categorical Equivalence

Package all components into an equivalence of categories.
-/

/--
The unit natural isomorphism: 𝟭 (WTypeDiagramCat X Y) ≅ wTypeToPolyBetween ⋙ polyBetweenToWType.
-/
def unitNatIso : 𝟭 (WTypeDiagramCat X Y) ≅ wTypeToPolyBetween ⋙ polyBetweenToWType :=
  NatIso.ofComponents
    (fun W => ⟨unitHom W, unitInv W, unitHom_unitInv W, unitInv_unitHom W⟩)
    (fun f => unitHom_naturality f)

/--
The counit natural isomorphism:
`polyBetweenToWType ⋙ wTypeToPolyBetween ≅ 𝟭 (PolyFunctorBetweenCat X Y)`.
-/
def counitNatIso : polyBetweenToWType ⋙ wTypeToPolyBetween ≅ 𝟭 (PolyFunctorBetweenCat X Y) :=
  NatIso.ofComponents
    (fun P => ⟨counitHom P, counitInv P, counitHom_counitInv P, counitInv_counitHom P⟩)
    (fun g => counitHom_naturality g)

/--
The equivalence between W-type diagrams and Grothendieck-style polynomial functors.
-/
def wTypePolyBetweenEquiv : WTypeDiagramCat X Y ≌ PolyFunctorBetweenCat X Y where
  functor := wTypeToPolyBetween
  inverse := polyBetweenToWType
  unitIso := unitNatIso
  counitIso := counitNatIso
  functor_unitIso_comp W := functor_unitIso_comp W

end WTypePolyBetweenEquiv

/-! ## Polynomial Double Category

The bicategory of polynomial functors extends to a double category
(a framed bicategory) with:

- Objects: types
- Vertical morphisms: functions
- Horizontal morphisms: polynomial functors
- 2-cells: natural transformations from pushouts

See `SlicePolyCat.idr` (`SPFpoDoubleCat`) for the Idris reference.
-/

/-! ### Pushout of Polynomial Functors

Given functions `bcl : X → X'` and `bcr : Y → Y'`, the pushout
`polyPushout bcl bcr f` pushes a polynomial `f : Over X → Over Y`
forward to `Over X' → Over Y'` by:

- Pushing positions forward along `bcr` (fiber of the codomain map)
- Post-composing fiber maps with `bcl`
-/

section PolyPushout

variable {X X' Y Y' : Type u}

/--
The index type of the pushout at `y' : Y'`.

Positions of `polyPushout bcl bcr f` at `y'` are pairs of a preimage
`y` of `y'` under `bcr` together with a position of `f` at `y`.
-/
def polyPushoutIndex (bcr : Y → Y')
    (f : PolyFunctorBetweenCat X Y) (y' : Y') : Type u :=
  Σ (p : { y : Y // bcr y = y' }), ccrIndex (f p.val)

/--
The family of the pushout at a given position.

At position `⟨⟨y, _⟩, i⟩`, the `Over X'` object has the same
underlying type as `ccrFamily (f y) i` but with structure map
post-composed with `bcl`.
-/
def polyPushoutFamily (bcl : X → X')
    (bcr : Y → Y') (f : PolyFunctorBetweenCat X Y) (y' : Y')
    (p : polyPushoutIndex bcr f y') : Over X' :=
  Over.mk (fun e => bcl ((ccrFamily (f p.1.val) p.2).hom e))

/--
Pushout of a polynomial functor along domain and codomain functions.

`polyPushout bcl bcr f` is the polynomial `Over X' → Over Y'` obtained
by pushing `f : Over X → Over Y` forward along `bcl : X → X'` and
`bcr : Y → Y'`.
-/
def polyPushout (bcl : X → X') (bcr : Y → Y')
    (f : PolyFunctorBetweenCat X Y) :
    PolyFunctorBetweenCat X' Y' :=
  fun y' => ccrObjMk (polyPushoutFamily bcl bcr f y')

lemma polyPushout_index (bcl : X → X') (bcr : Y → Y')
    (f : PolyFunctorBetweenCat X Y) (y' : Y') :
    ccrIndex (polyPushout bcl bcr f y') =
      polyPushoutIndex bcr f y' := rfl

lemma polyPushout_family (bcl : X → X') (bcr : Y → Y')
    (f : PolyFunctorBetweenCat X Y) (y' : Y')
    (p : polyPushoutIndex bcr f y') :
    ccrFamily (polyPushout bcl bcr f y') p =
      polyPushoutFamily bcl bcr f y' p := rfl

end PolyPushout

/-! ### 2-Cells via Pushout

A 2-cell in the polynomial double category is a morphism
(natural transformation) from the pushout of the domain polynomial
to the codomain polynomial, both viewed in `PolyFunctorBetweenCat X' Y'`.
-/

section PolyCells

variable {X X' Y Y' : Type u}

/--
A 2-cell (square) in the polynomial double category.

Given vertical morphisms `bcl : X → X'` and `bcr : Y → Y'` and
horizontal morphisms `f : PolyFunctorBetweenCat X Y` and
`g : PolyFunctorBetweenCat X' Y'`, a `PolyCell` is a morphism
from `polyPushout bcl bcr f` to `g` in `PolyFunctorBetweenCat X' Y'`.

```
  X ───f───▶ Y
  │          │
  bcl        bcr
  ▼          ▼
  X' ──g──▶ Y'
```
-/
abbrev PolyCell (bcl : X → X') (bcr : Y → Y')
    (f : PolyFunctorBetweenCat X Y)
    (g : PolyFunctorBetweenCat X' Y') :=
  polyPushout bcl bcr f ⟶ g

/-! #### Vertical identity 2-cell

When both vertical morphisms are `id`, the pushout
`polyPushout id id f` has positions `Σ (p : { y // y = y' }), I_y`
and the same families (since `id ∘ hom = hom`). The identity 2-cell
maps this to `f` by extracting the preimage witness.
-/

/--
The on-positions map of the vertical identity 2-cell at `y`.

Maps `⟨⟨y₀, hy₀⟩, i⟩ : polyPushoutIndex id f y` to an index of
`f y` by transporting `i` along `hy₀ : id y₀ = y`.
-/
def polyCellVIdBase
    {X Y : Type u}
    (f : PolyFunctorBetweenCat X Y) (y : Y)
    (p : polyPushoutIndex id f y) : ccrIndex (f y) :=
  p.1.prop ▸ p.2

/--
The on-directions map of the vertical identity 2-cell at `y`.
-/
def polyCellVIdFiber
    {X Y : Type u}
    (f : PolyFunctorBetweenCat X Y) (y : Y)
    (p : polyPushoutIndex id f y) :
    ccrFamily (f y) (polyCellVIdBase f y p) ⟶
      polyPushoutFamily id id f y p := by
  obtain ⟨⟨y₀, rfl⟩, i⟩ := p
  exact 𝟙 _

/--
The vertical identity 2-cell: `PolyCell id id f f`.

When both vertical morphisms are identity functions, there is a
canonical 2-cell from `polyPushout id id f` to `f`.
-/
def polyCellVId
    {X Y : Type u}
    (f : PolyFunctorBetweenCat X Y) :
    PolyCell id id f f := fun y =>
  ccrHomMk (polyCellVIdBase f y) (polyCellVIdFiber f y)

/-! #### Horizontal identity 2-cell

When both horizontal morphisms are `polyBetweenId`, a 2-cell with
vertical morphism `bcw : X → X'` maps
`polyPushout bcw bcw (polyBetweenId X)` to `polyBetweenId X'`.
The pushout at `x' : X'` has positions
`Σ (p : { x // bcw x = x' }), PUnit` and the identity has
positions `PUnit`, so the on-positions map discards the preimage.
-/

/--
The on-positions map of the horizontal identity 2-cell.
-/
def polyCellHIdBase
    (bcw : X → X') (x' : X')
    (_p : polyPushoutIndex bcw (polyBetweenId X) x') :
    ccrIndex (polyBetweenId X' x') :=
  PUnit.unit

/--
The on-directions map of the horizontal identity 2-cell.
-/
def polyCellHIdFiber
    (bcw : X → X') (x' : X')
    (p : polyPushoutIndex bcw (polyBetweenId X) x') :
    ccrFamily (polyBetweenId X' x') (polyCellHIdBase bcw x' p) ⟶
      polyPushoutFamily bcw bcw (polyBetweenId X) x' p := by
  obtain ⟨⟨x, rfl⟩, ⟨⟩⟩ := p
  exact 𝟙 _

/--
The horizontal identity 2-cell: `PolyCell bcw bcw (polyBetweenId X) (polyBetweenId X')`.

For a vertical morphism `bcw : X → X'`, this fills the square
whose horizontal edges are identity polynomials.
-/
def polyCellHId
    (bcw : X → X') :
    PolyCell bcw bcw (polyBetweenId X)
      (polyBetweenId X') := fun x' =>
  ccrHomMk (polyCellHIdBase bcw x')
    (polyCellHIdFiber bcw x')

/-! #### Vertical composition of 2-cells

Given `alpha : PolyCell bcl bcr f g` and
`beta : PolyCell bcl' bcr' g h`, vertical composition produces
`PolyCell (bcl' ∘ bcl) (bcr' ∘ bcr) f h`.
-/

section PolyCellVComp

variable {X X' X'' Y Y' Y'' : Type u}
variable {bcl : X → X'} {bcl' : X' → X''}
variable {bcr : Y → Y'} {bcr' : Y' → Y''}
variable {f : PolyFunctorBetweenCat X Y}
variable {g : PolyFunctorBetweenCat X' Y'}
variable {h : PolyFunctorBetweenCat X'' Y''}

/--
The on-positions map of the vertical composite 2-cell.

Given a pushout position `⟨⟨y, hy⟩, i⟩` of `f` at `y''`, first
apply `alpha` to get a position of `g` at `bcr y`, then apply
`beta` to get a position of `h` at `bcr' (bcr y) = y''`.
-/
def polyCellVCompBase
    (beta : PolyCell bcl' bcr' g h)
    (alpha : PolyCell bcl bcr f g) (y'' : Y'')
    (p : polyPushoutIndex (bcr' ∘ bcr) f y'') :
    ccrIndex (h y'') := by
  obtain ⟨⟨y, rfl⟩, i⟩ := p
  let alphaIdx := ccrReindex (alpha (bcr y))
    (⟨⟨y, rfl⟩, i⟩ : polyPushoutIndex bcr f (bcr y))
  exact ccrReindex (beta (bcr' (bcr y)))
    (⟨⟨bcr y, rfl⟩, alphaIdx⟩ :
      polyPushoutIndex bcr' g (bcr' (bcr y)))

/--
The on-directions map of the vertical composite 2-cell.

The fiber morphism composes the underlying `.left` functions of
the `alpha` and `beta` fiber morphisms. Since `alpha` is a morphism
in `Over X'` and `beta` in `Over X''`, we compose at the level of
underlying functions and verify the `Over X''` commutativity.
-/
def polyCellVCompFiber
    (beta : PolyCell bcl' bcr' g h)
    (alpha : PolyCell bcl bcr f g) (y'' : Y'')
    (p : polyPushoutIndex (bcr' ∘ bcr) f y'') :
    ccrFamily (h y'') (polyCellVCompBase beta alpha y'' p) ⟶
      polyPushoutFamily (bcl' ∘ bcl) (bcr' ∘ bcr)
        f y'' p := by
  obtain ⟨⟨y, rfl⟩, i⟩ := p
  let pf : polyPushoutIndex bcr f (bcr y) := ⟨⟨y, rfl⟩, i⟩
  let alphaIdx := ccrReindex (alpha (bcr y)) pf
  let pg : polyPushoutIndex bcr' g (bcr' (bcr y)) :=
    ⟨⟨bcr y, rfl⟩, alphaIdx⟩
  let betaFib := ccrFiberMor (beta (bcr' (bcr y))) pg
  let alphaFib := ccrFiberMor (alpha (bcr y)) pf
  refine Over.homMk (alphaFib.left ∘ betaFib.left) ?_
  funext e
  have hb := congrFun (Over.w betaFib) e
  have ha := congrFun (Over.w alphaFib) (betaFib.left e)
  simp only [types_comp_apply] at hb ha
  change bcl (((f y).fiber i).hom
    (alphaFib.left (betaFib.left e))) =
    ((g (bcr y)).fiber alphaIdx).hom
      (betaFib.left e) at ha
  change bcl' (((g (bcr y)).fiber alphaIdx).hom
    (betaFib.left e)) =
    ((h (bcr' (bcr y))).fiber
      (ccrReindex (beta (bcr' (bcr y))) pg)).hom e at hb
  simp only [types_comp_apply, Function.comp_apply]
  dsimp only [polyPushoutFamily, ccrFamily, polyPushout,
    ccrObjMk, Over.mk_hom]
  unfold Function.comp
  rw [ha, hb]
  rfl

/--
Vertical composition of 2-cells.

Given `alpha : PolyCell bcl bcr f g` and
`beta : PolyCell bcl' bcr' g h`, produces
`PolyCell (bcl' ∘ bcl) (bcr' ∘ bcr) f h`.
-/
def polyCellVComp
    (beta : PolyCell bcl' bcr' g h)
    (alpha : PolyCell bcl bcr f g) :
    PolyCell (bcl' ∘ bcl) (bcr' ∘ bcr) f h :=
  fun y'' => ccrHomMk
    (polyCellVCompBase beta alpha y'')
    (polyCellVCompFiber beta alpha y'')

end PolyCellVComp

/-! #### Horizontal composition of 2-cells

Given `alpha : PolyCell bcw bcx f g` (left square) and
`beta : PolyCell bcx bcz f' g'` (right square), horizontal
composition produces
`PolyCell bcw bcz (polyBetweenComp f' f) (polyBetweenComp g' g)`.

```
  X ──f──▶ W ──f'──▶ Z
  │        │         │
  bcw      bcx       bcz
  ▼        ▼         ▼
  X' ─g──▶ W' ─g'──▶ Z'
```
-/

section PolyCellHComp

variable {X X' W W' Z Z' : Type u}
variable {bcw : X → X'} {bcx : W → W'} {bcz : Z → Z'}
variable {f : PolyFunctorBetweenCat X W}
variable {f' : PolyFunctorBetweenCat W Z}
variable {g : PolyFunctorBetweenCat X' W'}
variable {g' : PolyFunctorBetweenCat W' Z'}

/--
The on-positions map of the horizontal composite 2-cell.

Given a position `⟨⟨z, _⟩, ⟨ig', ef⟩⟩` of the pushout of the
composite `polyBetweenComp f' f`:

1. Apply `beta` to get `ig_g'` = a position of `g'` at `z'`
2. For each direction `e'` of `g'` at `ig_g'`, apply `beta`'s
   fiber map to get a direction of `f'`, then use `ef` to get a
   position of `f`, then apply `alpha` to get a position of `g`
-/
def polyCellHCompBase
    (beta : PolyCell bcx bcz f' g')
    (alpha : PolyCell bcw bcx f g) (z' : Z')
    (p : polyPushoutIndex bcz (polyBetweenComp f' f) z') :
    ccrIndex (polyBetweenComp g' g z') := by
  obtain ⟨⟨z, rfl⟩, ig', ef⟩ := p
  let pbeta : polyPushoutIndex bcz f' (bcz z) :=
    ⟨⟨z, rfl⟩, ig'⟩
  let ig_g' := ccrReindex (beta (bcz z)) pbeta
  refine ⟨ig_g', fun e' => ?_⟩
  let betaFib := ccrFiberMor (beta (bcz z)) pbeta
  let betaDir := betaFib.left e'
  let w : W := (ccrFamily (f' z) ig').hom betaDir
  have hw : bcx w =
      (ccrFamily (g' (bcz z)) ig_g').hom e' := by
    have h := congrFun (Over.w betaFib) e'
    simp only [types_comp_apply] at h
    exact h
  let palpha : polyPushoutIndex bcx f
      ((ccrFamily (g' (bcz z)) ig_g').hom e') :=
    ⟨⟨w, hw⟩, ef betaDir⟩
  exact ccrReindex (alpha _) palpha

/--
The on-directions map of the horizontal composite 2-cell.
-/
def polyCellHCompFiber
    (beta : PolyCell bcx bcz f' g')
    (alpha : PolyCell bcw bcx f g) (z' : Z')
    (p : polyPushoutIndex bcz (polyBetweenComp f' f) z') :
    ccrFamily (polyBetweenComp g' g z')
        (polyCellHCompBase beta alpha z' p) ⟶
      polyPushoutFamily bcw bcz
        (polyBetweenComp f' f) z' p := by
  obtain ⟨⟨z, rfl⟩, ig', ef⟩ := p
  let pbeta : polyPushoutIndex bcz f' (bcz z) :=
    ⟨⟨z, rfl⟩, ig'⟩
  let ig_g' := ccrReindex (beta (bcz z)) pbeta
  let betaFib := ccrFiberMor (beta (bcz z)) pbeta
  refine Over.homMk ?func ?proof
  case func =>
    intro ⟨eg', eg⟩
    let betaDir := betaFib.left eg'
    let w : W := (ccrFamily (f' z) ig').hom betaDir
    have hw : bcx w =
        (ccrFamily (g' (bcz z)) ig_g').hom eg' := by
      have h := congrFun (Over.w betaFib) eg'
      simp only [types_comp_apply] at h
      exact h
    let palpha : polyPushoutIndex bcx f
        ((ccrFamily (g' (bcz z)) ig_g').hom eg') :=
      ⟨⟨w, hw⟩, ef betaDir⟩
    let alphaFib := ccrFiberMor (alpha _) palpha
    exact ⟨betaDir, alphaFib.left eg⟩
  case proof =>
    funext ⟨eg', eg⟩
    simp only [types_comp_apply]
    dsimp only [polyPushoutFamily, polyBetweenComp,
      polyBetweenCompFamily, ccrFamily, ccrObjMk,
      Over.mk_hom]
    let betaDir := betaFib.left eg'
    let w := (ccrFamily (f' z) ig').hom betaDir
    have hw : bcx w =
        (ccrFamily (g' (bcz z)) ig_g').hom eg' := by
      have h := congrFun (Over.w betaFib) eg'
      simp only [types_comp_apply] at h
      exact h
    let palpha : polyPushoutIndex bcx f
        ((ccrFamily (g' (bcz z)) ig_g').hom eg') :=
      ⟨⟨w, hw⟩, ef betaDir⟩
    let alphaFib := ccrFiberMor (alpha _) palpha
    have ha := congrFun (Over.w alphaFib) eg
    simp only [types_comp_apply] at ha
    dsimp only [polyPushoutFamily, ccrFamily, polyPushout,
      ccrObjMk, Over.mk_hom, Subtype.val] at ha
    exact ha

/--
Horizontal composition of 2-cells.

Given `alpha : PolyCell bcw bcx f g` (left square) and
`beta : PolyCell bcx bcz f' g'` (right square), produces
`PolyCell bcw bcz (polyBetweenComp f' f) (polyBetweenComp g' g)`.
-/
def polyCellHComp
    (beta : PolyCell bcx bcz f' g')
    (alpha : PolyCell bcw bcx f g) :
    PolyCell bcw bcz (polyBetweenComp f' f)
      (polyBetweenComp g' g) :=
  fun z' => ccrHomMk
    (polyCellHCompBase beta alpha z')
    (polyCellHCompFiber beta alpha z')

end PolyCellHComp

end PolyCells

/-! ### Polynomial Double Category

Strict double category structure on polynomial functors, with:

- Objects: `Type u`
- Vertical morphisms: functions
- Horizontal morphisms: `PolyHorizontalHom` (isomorphism classes)
- Squares: `Prop`-valued (existence of a concrete 2-cell)
-/

section PolyDoubleCategory

/--
The square type for the polynomial double category.

A square exists between vertical morphisms `bcl, bcr` and
horizontal morphisms `fq, gq` (in `PolyHorizontalHom`) when
for all representatives `f, g` of the equivalence classes
`fq, gq`, there exists a concrete 2-cell
`PolyCell bcl bcr f g`.
-/
def polyDoubleSqs : @SquareSet (Type u)
    (fun X Y => X → Y)
    (fun X Y => PolyHorizontalHom X Y) :=
  fun {_A _B _C _D} (bcl : _A → _C)
    (bcr : _B → _D)
    (fq : PolyHorizontalHom _A _B)
    (gq : PolyHorizontalHom _C _D) =>
  ∃ (f : PolyFunctorBetweenCat _A _B)
    (g : PolyFunctorBetweenCat _C _D),
    toSkeleton _ f = fq ∧
    toSkeleton _ g = gq ∧
    Nonempty (PolyCell bcl bcr f g)

lemma polyHorizComp_mk
    {X Y Z : Type u}
    (f : PolyFunctorBetweenCat X Y)
    (g : PolyFunctorBetweenCat Y Z) :
    polyHorizComp
      (toSkeleton _ f) (toSkeleton _ g) =
    toSkeleton _
      (polyBetweenComp g f) := rfl

/--
Operations for the polynomial double category.
-/
def polyDoubleOps : @DoubleCategoryOps (Type u)
    (fun X Y => X → Y)
    (fun X Y => PolyHorizontalHom X Y)
    polyDoubleSqs where
  vComp f g := g ∘ f
  hComp := polyHorizComp
  vId _ := id
  hId := polyHorizId
  sqVComp := fun {_A _B _C _D _E _F}
      {v₁} {v₂} {v₁'} {v₂'} {h₁} {h₂} {h₃}
      α β => by
    obtain ⟨f₀, g₀, hf₀, hg₀, ⟨c₁⟩⟩ := α
    obtain ⟨g₁, h₀, hg₁, hh₀, ⟨c₂⟩⟩ := β
    have hiso : Nonempty (g₀ ≅ g₁) :=
      toSkeleton_eq_iff.mp (hg₀.trans hg₁.symm)
    obtain ⟨iso⟩ := hiso
    exact ⟨f₀, h₀, hf₀, hh₀,
      ⟨polyCellVComp c₂ (c₁ ≫ iso.hom)⟩⟩
  sqHComp := fun {_A _B _C _D _E _F}
      {v₁} {v₂} {v₃} {h₁} {h₂} {h₃} {h₄}
      α β => by
    obtain ⟨f₀, g₀, hf₀, hg₀, ⟨c₁⟩⟩ := α
    obtain ⟨f'₀, g'₀, hf'₀, hg'₀, ⟨c₂⟩⟩ := β
    refine ⟨polyBetweenComp f'₀ f₀,
      polyBetweenComp g'₀ g₀, ?_, ?_,
      ⟨polyCellHComp c₂ c₁⟩⟩
    · rw [← hf₀, ← hf'₀]; rfl
    · rw [← hg₀, ← hg'₀]; rfl
  sqVertId := fun {_A _B} hq => by
    obtain ⟨f₀, rfl⟩ :=
      Quotient.exists_rep (s := isIsomorphicSetoid _)
        hq
    exact ⟨f₀, f₀, rfl, rfl,
      ⟨polyCellVId f₀⟩⟩
  sqHorId := fun {_A _C} v =>
    ⟨polyBetweenId _A, polyBetweenId _C,
      rfl, rfl, ⟨polyCellHId v⟩⟩

/--
Laws for the polynomial double category.

The vertical category laws hold because function composition
is definitionally associative and unital. The horizontal
category laws are `polyHorizComp_assoc`,
`polyHorizComp_id_left`, and `polyHorizComp_id_right`.
All square laws hold because the square type
`polyDoubleSqs` is `Prop`-valued, so elements of the same
proposition are equal by proof irrelevance.
-/
theorem polyDoubleLaws :
    DoubleCategoryLaws polyDoubleOps where
  vertLaws := {
    assoc := fun _ _ _ => rfl
    id_laws := {
      id_comp := fun _ => rfl
      comp_id := fun _ => rfl
    }
  }
  horLaws := {
    assoc := polyHorizComp_assoc
    id_laws := {
      id_comp := polyHorizComp_id_left
      comp_id := polyHorizComp_id_right
    }
  }
  sqLaws := {
    sqVAssoc := fun _ _ _ =>
      proof_irrel_heq _ _
    sqHAssoc := fun _ _ _ =>
      proof_irrel_heq _ _
    sqVIdComp := fun _ =>
      proof_irrel_heq _ _
    sqVCompId := fun _ =>
      proof_irrel_heq _ _
    sqHIdComp := fun _ =>
      proof_irrel_heq _ _
    sqHCompId := fun _ =>
      proof_irrel_heq _ _
    interchange := fun _ _ _ _ =>
      Subsingleton.elim _ _
    vertIdVComp := fun _ _ =>
      Subsingleton.elim _ _
    horIdHComp := fun _ _ =>
      Subsingleton.elim _ _
    idOnId := fun _ =>
      Subsingleton.elim _ _
  }

/--
The polynomial double category: operations and laws bundled.
-/
def polyDoubleData : DoubleCategoryData (Type u)
    (fun X Y => X → Y)
    (fun X Y => PolyHorizontalHom X Y)
    polyDoubleSqs where
  toDoubleCategoryOps := polyDoubleOps
  laws := polyDoubleLaws

end PolyDoubleCategory

end GebLean
