import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Category.Cat
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

universe u

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
-/
def polyEval (P : PolyFunctorCat X) (A : Over X) : Type u :=
  Σ i : ccrIndex P, (ccrFamily P i ⟶ A)

/--
Extract the index from an element of a polynomial evaluation.
-/
def polyEvalIndex {P : PolyFunctorCat X} {A : Over X} (x : polyEval X P A) :
    ccrIndex P :=
  x.1

/--
Extract the morphism from an element of a polynomial evaluation.
-/
def polyEvalMor {P : PolyFunctorCat X} {A : Over X} (x : polyEval X P A) :
    ccrFamily P (polyEvalIndex X x) ⟶ A :=
  x.2

/--
Construct an element of a polynomial evaluation from an index and a morphism.
-/
def polyEvalMk {P : PolyFunctorCat X} {A : Over X}
    (i : ccrIndex P) (f : ccrFamily P i ⟶ A) : polyEval X P A :=
  ⟨i, f⟩

end PolynomialFunctorsToType

/-! ## Polynomial Functors Over X → Over Y

A polynomial functor `Over X → Over Y` can be viewed as a `Y`-indexed family
of polynomial functors `Over X → Type`. Using the equivalence
`FamilyCat Type Y ≃ Over Y`, we can represent such functors as objects of
`FreeProdCompletionCat (PolyFunctorCat X)` indexed by `Y`.

Alternatively, a polynomial functor `Over X → Over Y` is given by a W-type
diagram `X ← E → B → Y`, which consists of:
- A type `B` (the base)
- A family `E : B → Type` (the fibers, giving `E → B`)
- A map `s : E → X` (the source map, making each `E(b)` an object over `X`)
- A map `t : B → Y` (the target map)

The polynomial functor is then:
`A ↦ Σ_{b : B} Π_{e : E(b)} Hom_{Over X}(s(e), A)` (composed with `t`)
-/

section PolynomialFunctorsBetweenSlices

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

end PolynomialFunctorsBetweenSlices

end GebLean
