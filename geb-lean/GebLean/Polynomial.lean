import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Pi.Basic
import GebLean.Utilities.Equalities
import GebLean.Utilities.Families
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

variable {D : Type u'} [Category.{u} D]

/--
Evaluation of a polynomial functor at an object of `D`.
Given a polynomial `P = (I, F)` where `F : I → D` and an object `A : D`,
the evaluation `P(A) = Σ_{i : I} Hom_D(F(i), A)` is a type.
-/
def ccrEval (P : CoprodCovarRepCat D) (A : D) : Type _ :=
  Σ i : ccrIndex P, (ccrFamily P i ⟶ A)

/--
Extract the index from an element of a polynomial evaluation.
-/
def ccrEvalIndex {P : CoprodCovarRepCat D} {A : D} (x : ccrEval P A) :
    ccrIndex P :=
  x.1

/--
Extract the morphism from an element of a polynomial evaluation.
-/
def ccrEvalMor {P : CoprodCovarRepCat D} {A : D} (x : ccrEval P A) :
    ccrFamily P (ccrEvalIndex x) ⟶ A :=
  x.2

/--
Construct an element of a polynomial evaluation from an index and a morphism.
-/
def ccrEvalMk {P : CoprodCovarRepCat D} {A : D}
    (i : ccrIndex P) (f : ccrFamily P i ⟶ A) : ccrEval P A :=
  ⟨i, f⟩

@[simp]
lemma ccrEvalMk_index {P : CoprodCovarRepCat D} {A : D}
    (i : ccrIndex P) (f : ccrFamily P i ⟶ A) :
    ccrEvalIndex (ccrEvalMk i f) = i := rfl

@[simp]
lemma ccrEvalMk_mor {P : CoprodCovarRepCat D} {A : D}
    (i : ccrIndex P) (f : ccrFamily P i ⟶ A) :
    ccrEvalMor (ccrEvalMk i f) = f := rfl

/--
Extensionality for polynomial evaluations.
-/
lemma ccrEval_ext {P : CoprodCovarRepCat D} {A : D} (x y : ccrEval P A)
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
lemma ccrEvalMk_eta {P : CoprodCovarRepCat D} {A : D} (x : ccrEval P A) :
    ccrEvalMk (ccrEvalIndex x) (ccrEvalMor x) = x := rfl

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
def polyToOverIndex (P : PolyToOverCat (D := D) Y) (y : Y) : Type u :=
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
def polyToOverEvalFamily (P : PolyToOverCat (D := D) Y) (A : D) : Y → Type u :=
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

end GeneralPolynomialFunctorsToOver

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
def polyBetweenIndex (P : PolyFunctorBetweenCat X Y) (y : Y) : Type u :=
  polyToOverIndex Y P y

/--
The family of representables at a specific codomain point and position.
Specialization of `polyToOverFamily`.
-/
def polyBetweenFamily (P : PolyFunctorBetweenCat X Y) (y : Y)
    (i : polyBetweenIndex X Y P y) : Over X :=
  polyToOverFamily Y P y i

/--
Evaluate a polynomial functor `Over X → Over Y` at an object `A : Over X`,
producing a family `Y → Type`.
Specialization of `polyToOverEvalFamily`.

For each `y : Y`, we evaluate the polynomial `P(y)` at `A`:
`P(A)(y) = Σ (i : positions at y), Hom_{Over X}(F_y(i), A)`
-/
def polyBetweenEvalFamily (P : PolyFunctorBetweenCat X Y) (A : Over X) :
    Y → Type u :=
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
-/
lemma mor_to_pbe_y {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X}
    {B : Over Y} (h : B ⟶ polyBetweenEval X Y P A) (b : B.left) :
    pbeLeftY (h.left b) = B.hom b :=
  congrFun (Over.w h) b

/--
Given a morphism `h : B ⟶ polyBetweenEval X Y P A` and `b : B.left`, we can
extract the fiber element at `B.hom b`. This uses the commutativity condition
to transport from `pbeLeftY (h.left b)` to `B.hom b`.
-/
def mor_to_pbe_fiber {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X}
    {B : Over Y} (h : B ⟶ polyBetweenEval X Y P A) (b : B.left) :
    polyBetweenEvalFamily X Y P A (B.hom b) :=
  (mor_to_pbe_y h b) ▸ pbeLeftFiber (h.left b)

/--
The fiber element from a morphism: extract the index.
-/
def mor_to_pbe_fiber_index {X Y : Type u} {P : PolyFunctorBetweenCat X Y}
    {A : Over X} {B : Over Y} (h : B ⟶ polyBetweenEval X Y P A) (b : B.left) :
    ccrIndex (P (B.hom b)) :=
  pbefIndex (mor_to_pbe_fiber h b)

/--
The fiber element from a morphism: extract the inner morphism.
-/
def mor_to_pbe_fiber_mor {X Y : Type u} {P : PolyFunctorBetweenCat X Y}
    {A : Over X} {B : Over Y} (h : B ⟶ polyBetweenEval X Y P A) (b : B.left) :
    ccrFamily (P (B.hom b)) (mor_to_pbe_fiber_index h b) ⟶ A :=
  pbefMor (mor_to_pbe_fiber h b)

/--
Heterogeneous equality between `mor_to_pbe_fiber` and the raw fiber.
-/
lemma mor_to_pbe_fiber_heq_raw {X Y : Type u} {P : PolyFunctorBetweenCat X Y}
    {A : Over X} {B : Over Y} (h : B ⟶ polyBetweenEval X Y P A) (b : B.left) :
    mor_to_pbe_fiber h b ≍ pbeLeftFiber (h.left b) := by
  simp only [mor_to_pbe_fiber]
  exact eqRec_heq (mor_to_pbe_y h b) (pbeLeftFiber (h.left b))

/--
When the morphism `h` is constructed via `Over.homMk` and the fiber function
produces elements with the correct Y-coordinate (i.e., `w` is `funext (fun _ => rfl)`),
`mor_to_pbe_fiber_index` reduces definitionally.
-/
lemma mor_to_pbe_fiber_index_homMk_rfl {X Y : Type u} {P : PolyFunctorBetweenCat X Y}
    {A : Over X} {B : Over Y}
    (fn : (b : B.left) → polyBetweenEvalFamily X Y P A (B.hom b))
    (b : B.left) :
    mor_to_pbe_fiber_index
      (Over.homMk (fun b => pbeLeftMk (B.hom b) (fn b))
        (funext (fun _ => rfl))) b = pbefIndex (fn b) := by
  simp only [mor_to_pbe_fiber_index, mor_to_pbe_fiber, pbefIndex,
             ptoefIndex, pbeLeftMk, pbeLeftFiber]
  rfl

/--
The analogous lemma for `mor_to_pbe_fiber_mor`.
-/
lemma mor_to_pbe_fiber_mor_homMk_rfl {X Y : Type u} {P : PolyFunctorBetweenCat X Y}
    {A : Over X} {B : Over Y}
    (fn : (b : B.left) → polyBetweenEvalFamily X Y P A (B.hom b))
    (b : B.left) :
    mor_to_pbe_fiber_mor
      (Over.homMk (fun b => pbeLeftMk (B.hom b) (fn b))
        (funext (fun _ => rfl))) b = pbefMor (fn b) := by
  simp only [mor_to_pbe_fiber_mor, mor_to_pbe_fiber, pbefMor,
             ptoefMor, pbeLeftMk, pbeLeftFiber]
  rfl

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

This is `g(z)` evaluated at the family of position types from `f`.
Positions are: `Σ (i : positions of g at z), ∀ (e : fiber of g at i), positions of f at s(e)`
-/
def polyBetweenCompIndex (g : PolyFunctorBetweenCat Y Z)
    (f : PolyFunctorBetweenCat X Y) (z : Z) : Type _ :=
  Σ (ig : ccrIndex (g z)),
    ∀ (e : (ccrFamily (g z) ig).left), ccrIndex (f ((ccrFamily (g z) ig).hom e))

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
  (((familyFunctor (Over X) ⋙ Cat.opFunctor').map (𝟙 (FGP P) y').base).obj
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
        ((counitHom P ≫ counitInv P) y').base).obj (FGP P y').fiber =
      ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
        (𝟙 (FGP P) y').base).obj (FGP P y').fiber := by
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
        ((counitHom P ≫ counitInv P) y').base).obj (FGP P y').fiber ⟨⟨y', i⟩, rfl⟩ =
    ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
        (𝟙 (FGP P) y').base).obj (FGP P y').fiber ⟨⟨y', i⟩, rfl⟩ :=
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
            ((counitHom P ≫ counitInv P) y').base).obj (FGP P y').fiber =
         ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
            (𝟙 (FGP P) y').base).obj (FGP P y').fiber) :
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
        (𝟙 (wTypeToPolyBetween.obj W) (W.t b)).base).obj
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
              counitHom (wTypeToPolyBetween.obj W)) (W.t b)).base).obj
          (wTypeToPolyBetween.obj W (W.t b)).fiber =
        ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
            (𝟙 (wTypeToPolyBetween.obj W) (W.t b)).base).obj
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
              counitHom (wTypeToPolyBetween.obj W)) (W.t b)).base).obj
          (wTypeToPolyBetween.obj W (W.t b)).fiber =
        ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
            (𝟙 (wTypeToPolyBetween.obj W) (W.t b)).base).obj
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
          counitHom (wTypeToPolyBetween.obj W)) (W.t b)).base).obj
      (wTypeToPolyBetween.obj W (W.t b)).fiber =
    ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
        (𝟙 (wTypeToPolyBetween.obj W) (W.t b)).base).obj
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
              counitHom P') ((polyBetweenToWType.obj P).t ⟨y', i⟩)).base).obj
          (P' ((polyBetweenToWType.obj P).t ⟨y', i⟩)).fiber =
        ((familyFunctor (Over X) ⋙ Cat.opFunctor').map
            ((counitHom P ≫ g) ((polyBetweenToWType.obj P).t ⟨y', i⟩)).base).obj
          (P' ((polyBetweenToWType.obj P).t ⟨y', i⟩)).fiber :=
      congrArg (fun f => ((familyFunctor (Over X) ⋙ Cat.opFunctor').map f).obj
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

end GebLean
