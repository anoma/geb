import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Category.Cat
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
-/
lemma polyEval_ext {P : PolyFunctorCat X} {A : Over X} (x y : polyEval X P A)
    (hi : polyEvalIndex X x = polyEvalIndex X y)
    (hm : polyEvalMor X x ≍ polyEvalMor X y) : x = y := by
  obtain ⟨ix, mx⟩ := x
  obtain ⟨iy, my⟩ := y
  simp only [polyEvalIndex] at hi
  cases hi
  simp only [polyEvalMor] at hm
  cases eq_of_heq hm
  rfl

/--
Round-trip: constructing and then extracting gives the original.
-/
@[simp]
lemma polyEvalMk_eta {P : PolyFunctorCat X} {A : Over X} (x : polyEval X P A) :
    polyEvalMk X (polyEvalIndex X x) (polyEvalMor X x) = x := rfl

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
This is an object of `FamilyCat (PolyFunctorCat X) Y`.

For each `y : Y`, we have a polynomial functor `P(y) : Over X → Type`, which
is an object of `CoprodCovarRepCat (Over X)`, i.e., a pair `(I_y, F_y)` where
`I_y` is a type of positions and `F_y : I_y → Over X` gives the representables.
-/
abbrev PolyFunctorBetweenCat : Cat :=
  FamilyCat (PolyFunctorCat X) Y

/--
Extract the polynomial functor at a specific codomain point.
-/
def polyBetweenAt (P : PolyFunctorBetweenCat X Y) (y : Y) : PolyFunctorCat X :=
  P y

/--
The index type (positions) at a specific codomain point.
-/
def polyBetweenIndex (P : PolyFunctorBetweenCat X Y) (y : Y) : Type u :=
  ccrIndex (P y)

/--
The family of representables at a specific codomain point and position.
-/
def polyBetweenFamily (P : PolyFunctorBetweenCat X Y) (y : Y)
    (i : polyBetweenIndex X Y P y) : Over X :=
  ccrFamily (P y) i

/--
Evaluate a polynomial functor `Over X → Over Y` at an object `A : Over X`,
producing a family `Y → Type`.

For each `y : Y`, we evaluate the polynomial `P(y)` at `A`:
`P(A)(y) = Σ (i : positions at y), Hom_{Over X}(F_y(i), A)`
-/
def polyBetweenEvalFamily (P : PolyFunctorBetweenCat X Y) (A : Over X) :
    Y → Type u :=
  fun y => polyEval X (P y) A

/--
Evaluate a polynomial functor at an object of `Over X`, producing an object
of `Over Y` via the family-slice equivalence.
-/
def polyBetweenEval (P : PolyFunctorBetweenCat X Y) (A : Over X) : Over Y :=
  (familySliceForward Y).obj (polyBetweenEvalFamily X Y P A)

/-! #### polyBetweenEvalFamily helpers

Since `polyBetweenEvalFamily P A y = polyEval X (P y) A`, we can reuse the
`polyEval` infrastructure. However, we also need lemmas connecting these
to the structure of `polyBetweenEval P A` as an `Over Y` object.
-/

/--
Extract the index from an element of `polyBetweenEvalFamily`.
-/
def pbefIndex {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X} {y : Y}
    (x : polyBetweenEvalFamily X Y P A y) : ccrIndex (P y) :=
  polyEvalIndex X x

/--
Extract the morphism from an element of `polyBetweenEvalFamily`.
-/
def pbefMor {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X} {y : Y}
    (x : polyBetweenEvalFamily X Y P A y) :
    ccrFamily (P y) (pbefIndex x) ⟶ A :=
  polyEvalMor X x

/--
Construct an element of `polyBetweenEvalFamily` from an index and morphism.
-/
def pbefMk {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X} {y : Y}
    (i : ccrIndex (P y)) (f : ccrFamily (P y) i ⟶ A) :
    polyBetweenEvalFamily X Y P A y :=
  polyEvalMk X i f

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
-/
def pbeLeftY {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X}
    (e : (polyBetweenEval X Y P A).left) : Y :=
  e.fst

/--
Extract the fiber element from an element of `(polyBetweenEval P A).left`.
-/
def pbeLeftFiber {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X}
    (e : (polyBetweenEval X Y P A).left) :
    polyBetweenEvalFamily X Y P A (pbeLeftY e) :=
  e.snd

/--
Construct an element of `(polyBetweenEval P A).left` from components.
-/
def pbeLeftMk {X Y : Type u} {P : PolyFunctorBetweenCat X Y} {A : Over X}
    (y : Y) (x : polyBetweenEvalFamily X Y P A y) :
    (polyBetweenEval X Y P A).left :=
  ⟨y, x⟩

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
             polyEvalIndex, pbeLeftMk, pbeLeftFiber]
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
             polyEvalMor, pbeLeftMk, pbeLeftFiber]
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
    simp only [polyBetweenEvalFamily, polyEval, polyBetweenId, ccrObjMk, ccrIndex, ccrFamily]
    ext; rfl
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
    simp only [polyBetweenEval, polyBetweenEvalFamily, polyEval, polyBetweenId,
               ccrObjMk, ccrIndex, ccrFamily, familySliceForward, familySliceForwardObj]
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
               pbefIndex, pbefMor, polyEvalIndex, polyEvalMor]
    -- The goal reduces to showing the constructed sigma equals the original
    -- The inner `mor_to_pbe_fiber_index` on the constructed `Over.homMk` reduces
    -- because the Y-coordinate proof is `funext (fun _ => rfl)`
    rfl
  right_inv := fun x => by
    obtain ⟨ig, h⟩ := x
    simp only [polyBetweenComp_eval_fiberEquiv_toFun,
               polyBetweenComp_eval_fiberEquiv_invFun,
               pbefIndex, pbefMor, polyEvalIndex, polyEvalMor]
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

end GebLean
