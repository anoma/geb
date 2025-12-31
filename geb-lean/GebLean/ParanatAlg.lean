import GebLean.Paranatural
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Limits.Shapes.Terminal

/-!
# Paranatural transformations and initial algebras

This module establishes the correspondence between paranatural transformations
from the algebra profunctor to the identity profunctor and the initial algebra
of an endofunctor.

Given an endofunctor `F : C ⥤ C`, we form:
- The algebra profunctor `AlgProf F : Cᵒᵖ ⥤ C ⥤ Type` with
  `AlgProf F x y := F.obj x ⟶ y`
- The identity profunctor `IdProf : Cᵒᵖ ⥤ C ⥤ Type` with
  `IdProf x y := y`

The main result (following Uustalu, as referenced by Neumann) is:
- `DiagElem (AlgProf F) ≌ Endofunctor.Algebra F`
- `DiagElem IdProf ≌ Pointed C` (objects with a distinguished point)
- When `F` has an initial algebra `μF`, `Paranat (AlgProf F) IdProf ≃ μF`

## References

* Uustalu, "The Recursion Scheme from the Cofree Recursive Comonad"
* Neumann, "Paranatural Category Theory", Section 4

-/

namespace GebLean

open CategoryTheory Limits

universe u v

variable {C : Type u} [Category.{v} C]

section AlgebraProfunctor

variable (F : C ⥤ C)

/-!
### The algebra profunctor

For an endofunctor `F : C ⥤ C`, the algebra profunctor `AlgProf F` sends
`(x, y)` to the type of morphisms `F.obj x ⟶ y`. This profunctor encodes
the structure of F-algebras: a diagonal element at `A` is precisely an
F-algebra structure `F.obj A ⟶ A`.
-/

/-- The algebra profunctor for an endofunctor `F`. At objects `(x, y)`,
this is the type `F.obj x ⟶ y` of "algebra-like" morphisms.
Contravariant in `x` via precomposition with `F.map`, covariant in `y`
via postcomposition. -/
@[simps]
def AlgProf : Cᵒᵖ ⥤ C ⥤ Type v where
  obj x := {
    obj := fun y => F.obj x.unop ⟶ y
    map := fun g a => a ≫ g
    map_id := fun _ => by ext; simp
    map_comp := fun _ _ => by ext; simp [Category.assoc]
  }
  map {x₁ x₂} f := {
    app := fun y a => F.map f.unop ≫ a
    naturality := fun _ _ g => by ext; simp [Category.assoc]
  }
  map_id x := by ext y a; simp
  map_comp {x₁ x₂ x₃} f g := by ext y a; simp [Category.assoc]

end AlgebraProfunctor

section IdentityProfunctor

/-!
### The identity profunctor

The identity profunctor for `C = Type v` sends `(x, y)` to `y` itself.
A diagonal element at `A` is just a point of `A`, making `DiagElem IdProf`
equivalent to the category of pointed types.

Note: This profunctor only makes sense when `C = Type v` since we need
objects to be types that can contain elements.
-/

/-- The identity profunctor on `Type v`, sending `(x, y)` to `y`.
This is constant in the first argument and the identity in the second. -/
@[simps!]
def IdProf : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v where
  obj _ := 𝟭 (Type v)
  map _ := 𝟙 (𝟭 (Type v))
  map_id _ := rfl
  map_comp _ _ := rfl

end IdentityProfunctor

section DiagElemAlgebraEquiv

variable (F : C ⥤ C)

/-!
### Diagonal elements of AlgProf F are F-algebras

A diagonal element of `AlgProf F` at object `A` consists of:
- A base object `A : C`
- An element of `AlgProf F A A = (F.obj A ⟶ A)`

This is precisely the data of an F-algebra.
-/

/-- Convert a diagonal element of `AlgProf F` to an F-algebra. -/
@[simps]
def diagElemToAlg (x : DiagElem (AlgProf F)) : Endofunctor.Algebra F where
  a := x.base
  str := x.elem

/-- Convert an F-algebra to a diagonal element of `AlgProf F`. -/
@[simps]
def algToDiagElem (alg : Endofunctor.Algebra F) : DiagElem (AlgProf F) where
  base := alg.a
  elem := alg.str

/-- Convert a morphism of diagonal elements to an algebra morphism. -/
@[simps]
def diagElemHomToAlgHom {x y : DiagElem (AlgProf F)} (f : x ⟶ y) :
    diagElemToAlg F x ⟶ diagElemToAlg F y where
  f := f.base
  h := by
    simp only [diagElemToAlg_a, diagElemToAlg_str]
    have hcompat := f.compat
    simp only [DiagCompat, AlgProf_obj_obj, AlgProf_obj_map, AlgProf_map_app] at hcompat
    exact hcompat.symm

/-- Convert an algebra morphism to a morphism of diagonal elements. -/
@[simps]
def algHomToDiagElemHom {alg₁ alg₂ : Endofunctor.Algebra F}
    (f : alg₁ ⟶ alg₂) :
    algToDiagElem F alg₁ ⟶ algToDiagElem F alg₂ where
  base := f.f
  compat := by
    simp only [DiagCompat, algToDiagElem_base, algToDiagElem_elem,
      AlgProf_obj_obj, AlgProf_obj_map, AlgProf_map_app]
    exact f.h.symm

/-- The functor from diagonal elements of `AlgProf F` to F-algebras. -/
@[simps]
def diagElemToAlgFunctor : DiagElem (AlgProf F) ⥤ Endofunctor.Algebra F where
  obj := diagElemToAlg F
  map := diagElemHomToAlgHom F
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor from F-algebras to diagonal elements of `AlgProf F`. -/
@[simps]
def algToDiagElemFunctor : Endofunctor.Algebra F ⥤ DiagElem (AlgProf F) where
  obj := algToDiagElem F
  map := algHomToDiagElemHom F
  map_id _ := DiagElem.Hom.ext rfl
  map_comp _ _ := DiagElem.Hom.ext rfl

/-- The unit isomorphism for the equivalence between diagonal elements and
F-algebras: the round-trip through algebras and back is the identity. -/
def diagElemAlgUnitIso :
    𝟭 (DiagElem (AlgProf F)) ≅ diagElemToAlgFunctor F ⋙ algToDiagElemFunctor F :=
  NatIso.ofComponents
    (fun x => eqToIso rfl)
    (fun {x y} f => by
      apply DiagElem.Hom.ext
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
        diagElemToAlgFunctor_map, algToDiagElemFunctor_map,
        diagElemHomToAlgHom_f, algHomToDiagElemHom_base,
        eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp])

/-- The counit isomorphism for the equivalence: the round-trip through
diagonal elements and back is the identity. -/
def diagElemAlgCounitIso :
    algToDiagElemFunctor F ⋙ diagElemToAlgFunctor F ≅ 𝟭 (Endofunctor.Algebra F) :=
  NatIso.ofComponents
    (fun alg => Endofunctor.Algebra.isoMk (Iso.refl _) (by simp))
    (fun {alg₁ alg₂} f => by
      apply Endofunctor.Algebra.Hom.ext
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
        diagElemToAlgFunctor_map, algToDiagElemFunctor_map, Functor.id_map,
        Endofunctor.Algebra.comp_f, Endofunctor.Algebra.isoMk, Iso.refl_hom,
        diagElemHomToAlgHom_f, algHomToDiagElemHom_base,
        Category.comp_id, Category.id_comp])

/-- The equivalence between diagonal elements of `AlgProf F` and F-algebras. -/
def diagElemAlgEquiv : DiagElem (AlgProf F) ≌ Endofunctor.Algebra F :=
  CategoryTheory.Equivalence.mk
    (diagElemToAlgFunctor F)
    (algToDiagElemFunctor F)
    (diagElemAlgUnitIso F)
    (diagElemAlgCounitIso F)

end DiagElemAlgebraEquiv

section DiagElemPointedEquiv

/-!
### Diagonal elements of IdProf are pointed types

A diagonal element of `IdProf` at object `A` consists of:
- A base object `A : Type v`
- An element of `IdProf A A = A`

This is precisely a pointed type. We use mathlib's `Pointed` category.

Note: `Pointed` is also equivalent to the category of elements of the identity
functor `𝟭 (Type v)`, since `(𝟭 (Type v)).Elements = Σ (A : Type v), A`.
-/

/-- Convert a diagonal element of `IdProf` to a pointed type. -/
@[simps]
def diagElemToPointed (x : DiagElem IdProf) : Pointed.{v} :=
  Pointed.mk x.base x.elem

/-- Convert a pointed type to a diagonal element of `IdProf`. -/
@[simps]
def pointedToDiagElem (p : Pointed.{v}) : DiagElem IdProf where
  base := p.X
  elem := p.point

/-- Convert a morphism of diagonal elements to a pointed type morphism. -/
@[simps]
def diagElemHomToPointedHom {x y : DiagElem IdProf} (f : x ⟶ y) :
    diagElemToPointed x ⟶ diagElemToPointed y where
  toFun := f.base
  map_point := by
    simp only [diagElemToPointed]
    have hcompat := f.compat
    simp only [DiagCompat, IdProf] at hcompat
    exact hcompat

/-- Convert a pointed type morphism to a morphism of diagonal elements. -/
@[simps]
def pointedHomToDiagElemHom {p q : Pointed.{v}}
    (f : p ⟶ q) :
    pointedToDiagElem p ⟶ pointedToDiagElem q where
  base := f.toFun
  compat := by
    simp only [DiagCompat, pointedToDiagElem_base, pointedToDiagElem_elem, IdProf]
    exact f.map_point

/-- The functor from diagonal elements of `IdProf` to pointed types. -/
@[simps]
def diagElemToPointedFunctor :
    DiagElem IdProf ⥤ Pointed.{v} where
  obj := diagElemToPointed
  map := diagElemHomToPointedHom
  map_id _ := Pointed.Hom.ext rfl
  map_comp _ _ := Pointed.Hom.ext rfl

/-- The functor from pointed types to diagonal elements of `IdProf`. -/
@[simps]
def pointedToDiagElemFunctor :
    Pointed.{v} ⥤ DiagElem IdProf where
  obj := pointedToDiagElem
  map := pointedHomToDiagElemHom
  map_id _ := DiagElem.Hom.ext rfl
  map_comp _ _ := DiagElem.Hom.ext rfl

/-- The unit isomorphism for the equivalence between diagonal elements of
`IdProf` and pointed types. -/
def diagElemPointedUnitIso :
    𝟭 (DiagElem IdProf) ≅ diagElemToPointedFunctor ⋙ pointedToDiagElemFunctor :=
  NatIso.ofComponents
    (fun x => eqToIso rfl)
    (fun {_ _} _ => by apply DiagElem.Hom.ext; rfl)

/-- The counit isomorphism for the equivalence between diagonal elements of
`IdProf` and pointed types. -/
def diagElemPointedCounitIso :
    pointedToDiagElemFunctor ⋙ diagElemToPointedFunctor ≅ 𝟭 Pointed.{v} :=
  NatIso.ofComponents
    (fun p => by
      refine ⟨⟨_root_.id, rfl⟩, ⟨_root_.id, rfl⟩, ?_, ?_⟩
      · apply Pointed.Hom.ext; rfl
      · apply Pointed.Hom.ext; rfl)
    (fun {_ _} _ => by apply Pointed.Hom.ext; rfl)

/-- The equivalence between diagonal elements of `IdProf` and pointed types. -/
def diagElemPointedEquiv :
    DiagElem IdProf ≌ Pointed.{v} :=
  CategoryTheory.Equivalence.mk
    diagElemToPointedFunctor
    pointedToDiagElemFunctor
    diagElemPointedUnitIso
    diagElemPointedCounitIso

end DiagElemPointedEquiv

section InitialAlgebraCorrespondence

/-!
### Paranatural transformations and initial algebras

The main theorem: when an endofunctor `F : Type v ⥤ Type v` has an initial
algebra `μF`, there is a bijection between:
- Paranatural transformations `Paranat (AlgProf F) IdProf`
- Elements of the carrier `μF.a`

The correspondence is:
- Forward: Given `x : μF.a`, define `α(A, alg) := (unique algebra hom μF → A)(x)`
- Backward: Given `α : Paranat`, define `x := α(μF.a, μF.str)`

The paranaturality condition ensures that the forward direction is well-defined
(the result is independent of how we transport `x` through algebra homomorphisms),
and the initiality ensures the round-trip properties.
-/

variable (F : Type v ⥤ Type v)

/-- Given an element of an initial F-algebra, construct a paranatural
transformation from `AlgProf F` to `IdProf`. At each type `A` with algebra
structure `alg : F.obj A → A`, we apply the unique algebra homomorphism
from the initial algebra to `(A, alg)`. -/
def initialToParanat (μF : Endofunctor.Algebra F) (hμF : IsInitial μF)
    (x : μF.a) : Paranat (AlgProf F) IdProf where
  app A alg :=
    let targetAlg : Endofunctor.Algebra F := ⟨A, alg⟩
    (hμF.to targetAlg).f x
  paranatural := fun A₀ A₁ f d₀ d₁ hcompat => by
    simp only [DiagCompat, AlgProf_obj_obj, AlgProf_obj_map, AlgProf_map_app] at hcompat
    simp only [DiagCompat, IdProf, Functor.id_obj, Functor.id_map, NatTrans.id_app,
      types_id_apply]
    let alg₀ : Endofunctor.Algebra F := ⟨A₀, d₀⟩
    let alg₁ : Endofunctor.Algebra F := ⟨A₁, d₁⟩
    let algHom : alg₀ ⟶ alg₁ := ⟨f, hcompat.symm⟩
    have h := hμF.hom_ext (hμF.to alg₀ ≫ algHom) (hμF.to alg₁)
    have hfx : (hμF.to alg₀ ≫ algHom).f x = f ((hμF.to alg₀).f x) := rfl
    have heq : (hμF.to alg₁).f x = (hμF.to alg₀ ≫ algHom).f x := by
      rw [h]
    rw [heq, hfx]

/-- Given a paranatural transformation from `AlgProf F` to `IdProf`, extract
an element of the initial algebra by applying the transformation to the
initial algebra's own structure map. -/
def paranatToInitial (μF : Endofunctor.Algebra F)
    (α : Paranat (AlgProf F) IdProf) : μF.a :=
  α.app μF.a μF.str

/-- The round-trip from initial algebra element to paranatural and back
yields the original element. -/
theorem paranatToInitial_initialToParanat (μF : Endofunctor.Algebra F)
    (hμF : IsInitial μF) (x : μF.a) :
    paranatToInitial F μF (initialToParanat F μF hμF x) = x := by
  simp only [paranatToInitial, initialToParanat]
  have h := hμF.hom_ext (hμF.to μF) (𝟙 μF)
  have heq : (hμF.to μF).f = _root_.id := by
    ext y
    exact congrFun (congrArg Endofunctor.Algebra.Hom.f h) y
  rw [heq]
  rfl

/-- The round-trip from paranatural to initial algebra element and back
yields the original paranatural transformation. -/
theorem initialToParanat_paranatToInitial (μF : Endofunctor.Algebra F)
    (hμF : IsInitial μF) (α : Paranat (AlgProf F) IdProf) :
    initialToParanat F μF hμF (paranatToInitial F μF α) = α := by
  apply Paranat.ext
  funext A alg
  simp only [initialToParanat, paranatToInitial]
  let targetAlg : Endofunctor.Algebra F := ⟨A, alg⟩
  let homToTarget := hμF.to targetAlg
  have hcompat : DiagCompat (AlgProf F) μF.a A homToTarget.f μF.str alg := by
    simp only [DiagCompat, AlgProf_obj_obj, AlgProf_obj_map, AlgProf_map_app]
    exact homToTarget.h.symm
  have hpara := α.paranatural μF.a A homToTarget.f μF.str alg hcompat
  simp only [DiagCompat, IdProf, Functor.id_obj, Functor.id_map, NatTrans.id_app,
    types_id_apply] at hpara
  exact hpara

/-- The bijection between elements of an initial F-algebra and paranatural
transformations from `AlgProf F` to `IdProf`. -/
def initialAlgebraParanatEquiv (μF : Endofunctor.Algebra F) (hμF : IsInitial μF) :
    μF.a ≃ Paranat (AlgProf F) IdProf where
  toFun := initialToParanat F μF hμF
  invFun := paranatToInitial F μF
  left_inv := paranatToInitial_initialToParanat F μF hμF
  right_inv := initialToParanat_paranatToInitial F μF hμF

end InitialAlgebraCorrespondence

end GebLean
