import GebLean.Paranatural
import Mathlib.CategoryTheory.Category.Pointed
import Mathlib.CategoryTheory.Endofunctor.Algebra
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Types.Limits

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

section CoalgebraProfunctor

variable (F : C ⥤ C)

/-!
### The coalgebra profunctor

For an endofunctor `F : C ⥤ C`, the coalgebra profunctor `CoalgProf F` sends
`(x, y)` to the type of morphisms `x ⟶ F.obj y`. This profunctor encodes
the structure of F-coalgebras: a diagonal element at `A` is precisely an
F-coalgebra structure `A ⟶ F.obj A`.
-/

/-- The coalgebra profunctor for an endofunctor `F`. At objects `(x, y)`,
this is the type `x ⟶ F.obj y` of "coalgebra-like" morphisms.
Contravariant in `x` via precomposition, covariant in `y`
via postcomposition with `F.map`. -/
@[simps]
def CoalgProf : Cᵒᵖ ⥤ C ⥤ Type v where
  obj x := {
    obj := fun y => x.unop ⟶ F.obj y
    map := fun g a => a ≫ F.map g
    map_id := fun _ => by ext; simp
    map_comp := fun _ _ => by ext; simp [Category.assoc]
  }
  map {x₁ x₂} f := {
    app := fun y a => f.unop ≫ a
    naturality := fun _ _ g => by ext; simp [Category.assoc]
  }
  map_id x := by ext y a; simp
  map_comp {x₁ x₂ x₃} f g := by ext y a; simp [Category.assoc]

end CoalgebraProfunctor

section DialgebraProfunctor

universe u' v'

variable {D : Type u'} [Category.{v'} D]
variable (F G : C ⥤ D)

/-!
### The dialgebra profunctor

For functors `F, G : C ⥤ D`, the dialgebra profunctor `DialgebraProf F G` sends
`(x, y)` to the type of morphisms `F.obj x ⟶ G.obj y` in `D`. This profunctor
encodes the structure of (F,G)-dialgebras: a diagonal element at `A` is
precisely a dialgebra structure `F.obj A ⟶ G.obj A`.

This generalizes both algebra and coalgebra profunctors:
- `AlgProf F ≅ DialgebraProf F (𝟭 C)` when `D = C`
- `CoalgProf F ≅ DialgebraProf (𝟭 C) F` when `D = C`
-/

/-- The dialgebra profunctor for functors `F, G : C ⥤ D`. At objects `(x, y)`,
this is the type `F.obj x ⟶ G.obj y` of "dialgebra-like" morphisms in `D`.
Contravariant in `x` via precomposition with `F.map`, covariant in `y`
via postcomposition with `G.map`. -/
@[simps]
def DialgebraProf : Cᵒᵖ ⥤ C ⥤ Type v' where
  obj x := {
    obj := fun y => F.obj x.unop ⟶ G.obj y
    map := fun g a => a ≫ G.map g
    map_id := fun _ => by ext; simp
    map_comp := fun _ _ => by ext; simp [Category.assoc]
  }
  map {x₁ x₂} f := {
    app := fun y a => F.map f.unop ≫ a
    naturality := fun _ _ g => by ext; simp [Category.assoc]
  }
  map_id x := by ext y a; simp
  map_comp {x₁ x₂ x₃} f g := by ext y a; simp [Category.assoc]

abbrev DialgebraProfType.{w}
  (F' G' : C ⥤ Type w) :
    Cᵒᵖ ⥤ C ⥤ Type w :=
  DialgebraProf (D := Type w) F' G'

abbrev DialgebraProfPresheaf.{u'', v'', w}
  {E : Type u''} [Category.{v'', u''} E]
  (F' G' : C ⥤ Eᵒᵖ ⥤ Type w) :
    Cᵒᵖ ⥤ C ⥤ Type (max u'' w) :=
  DialgebraProf (D := Eᵒᵖ ⥤ Type w) F' G'

end DialgebraProfunctor

section DialgebraCategory

/-!
### The dialgebra category

For functors `F, G : C ⥤ D`, the dialgebra category `Dialgebra F G` has:
- Objects: pairs `(A, str : F.obj A ⟶ G.obj A)` where `A : C`
- Morphisms: `m : A ⟶ B` in `C` such that the square commutes:
  ```
  F.obj A ---str---> G.obj A
     |                  |
  F.map m            G.map m
     |                  |
     v                  v
  F.obj B ---str---> G.obj B
  ```

This generalizes both algebras and coalgebras:
- When `G = 𝟭 C`, a dialgebra is an F-algebra
- When `F = 𝟭 C`, a dialgebra is a G-coalgebra
-/

universe u' v'

variable {D : Type u'} [Category.{v'} D]
variable (F G : C ⥤ D)

/-- An object of the dialgebra category for functors `F, G : C ⥤ D`.
This consists of an object `A : C` together with a structure morphism
`str : F.obj A ⟶ G.obj A` in `D`. -/
structure Dialgebra where
  /-- The carrier object in `C`. -/
  carrier : C
  /-- The structure morphism `F.obj carrier ⟶ G.obj carrier`. -/
  str : F.obj carrier ⟶ G.obj carrier

namespace Dialgebra

variable {F G}

/-- A morphism of dialgebras is a morphism in the base category that makes the
structure square commute. -/
@[ext]
structure Hom (X Y : Dialgebra F G) where
  /-- The underlying morphism in `C`. -/
  base : X.carrier ⟶ Y.carrier
  /-- The commutativity condition: the structure square commutes. -/
  comm : X.str ≫ G.map base = F.map base ≫ Y.str := by aesop_cat

attribute [reassoc (attr := simp)] Hom.comm

/-- The identity morphism of a dialgebra. -/
@[simps]
def Hom.id (X : Dialgebra F G) : Hom X X where
  base := 𝟙 X.carrier
  comm := by simp

/-- Composition of dialgebra morphisms. -/
@[simps]
def Hom.comp {X Y Z : Dialgebra F G} (f : Hom X Y) (g : Hom Y Z) : Hom X Z where
  base := f.base ≫ g.base
  comm := by
    simp only [Functor.map_comp, Category.assoc]
    rw [← Category.assoc, f.comm, Category.assoc, g.comm]

instance : Category (Dialgebra F G) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp _ := Hom.ext (Category.id_comp _)
  comp_id _ := Hom.ext (Category.comp_id _)
  assoc _ _ _ := Hom.ext (Category.assoc _ _ _)

@[simp]
theorem id_base (X : Dialgebra F G) : Hom.base (𝟙 X) = 𝟙 X.carrier := rfl

@[simp]
theorem comp_base {X Y Z : Dialgebra F G} (f : X ⟶ Y) (g : Y ⟶ Z) :
    (f ≫ g).base = f.base ≫ g.base := rfl

/-- Construct an isomorphism of dialgebras from an isomorphism of carriers
that respects the structure. -/
@[simps]
def isoMk {X Y : Dialgebra F G} (e : X.carrier ≅ Y.carrier)
    (h : X.str ≫ G.map e.hom = F.map e.hom ≫ Y.str := by aesop_cat) :
    X ≅ Y where
  hom := ⟨e.hom, h⟩
  inv := ⟨e.inv, by
    have step1 : X.str ≫ G.map e.hom ≫ G.map e.inv =
                 F.map e.hom ≫ Y.str ≫ G.map e.inv := by
      rw [← Category.assoc, h, Category.assoc]
    have step2 : X.str = F.map e.hom ≫ Y.str ≫ G.map e.inv := by
      simp only [← G.map_comp, e.hom_inv_id, G.map_id, Category.comp_id] at step1
      exact step1
    have step3 : F.map e.inv ≫ X.str = Y.str ≫ G.map e.inv := by
      rw [step2]
      simp only [← Category.assoc, ← F.map_comp, e.inv_hom_id, F.map_id,
        Category.id_comp]
    exact step3.symm⟩
  hom_inv_id := Hom.ext e.hom_inv_id
  inv_hom_id := Hom.ext e.inv_hom_id

end Dialgebra

end DialgebraCategory

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

/-- The equivalence between diagonal elements of `AlgProf F` and F-algebras. -/
def diagElemAlgIsoCat : DiagElem (AlgProf F) ≅Cat Endofunctor.Algebra F :=
  { hom := (diagElemToAlgFunctor F).toCatHom
    inv := (algToDiagElemFunctor F).toCatHom
  }

/-- The equivalence between diagonal elements of `AlgProf F` and F-algebras. -/
def diagElemAlgEquiv : DiagElem (AlgProf F) ≌ Endofunctor.Algebra F :=
  Cat.equivOfIso (diagElemAlgIsoCat F)

end DiagElemAlgebraEquiv

section DiagElemCoalgebraEquiv

variable (F : C ⥤ C)

/-!
### Diagonal elements of CoalgProf F are F-coalgebras

A diagonal element of `CoalgProf F` at object `A` consists of:
- A base object `A : C`
- An element of `CoalgProf F A A = (A ⟶ F.obj A)`

This is precisely the data of an F-coalgebra.
-/

/-- Convert a diagonal element of `CoalgProf F` to an F-coalgebra. -/
@[simps]
def diagElemToCoalg (x : DiagElem (CoalgProf F)) : Endofunctor.Coalgebra F where
  V := x.base
  str := x.elem

/-- Convert an F-coalgebra to a diagonal element of `CoalgProf F`. -/
@[simps]
def coalgToDiagElem (coalg : Endofunctor.Coalgebra F) : DiagElem (CoalgProf F) where
  base := coalg.V
  elem := coalg.str

/-- Convert a morphism of diagonal elements to a coalgebra morphism. -/
@[simps]
def diagElemHomToCoalgHom {x y : DiagElem (CoalgProf F)} (f : x ⟶ y) :
    diagElemToCoalg F x ⟶ diagElemToCoalg F y where
  f := f.base
  h := by
    simp only [diagElemToCoalg_V, diagElemToCoalg_str]
    have hcompat := f.compat
    simp only [DiagCompat, CoalgProf_obj_obj, CoalgProf_obj_map, CoalgProf_map_app] at hcompat
    exact hcompat

/-- Convert a coalgebra morphism to a morphism of diagonal elements. -/
@[simps]
def coalgHomToDiagElemHom {coalg₁ coalg₂ : Endofunctor.Coalgebra F}
    (f : coalg₁ ⟶ coalg₂) :
    coalgToDiagElem F coalg₁ ⟶ coalgToDiagElem F coalg₂ where
  base := f.f
  compat := by
    simp only [DiagCompat, coalgToDiagElem_base, coalgToDiagElem_elem,
      CoalgProf_obj_obj, CoalgProf_obj_map, CoalgProf_map_app]
    exact f.h

/-- The functor from diagonal elements of `CoalgProf F` to F-coalgebras. -/
@[simps]
def diagElemToCoalgFunctor : DiagElem (CoalgProf F) ⥤ Endofunctor.Coalgebra F where
  obj := diagElemToCoalg F
  map := diagElemHomToCoalgHom F
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor from F-coalgebras to diagonal elements of `CoalgProf F`. -/
@[simps]
def coalgToDiagElemFunctor : Endofunctor.Coalgebra F ⥤ DiagElem (CoalgProf F) where
  obj := coalgToDiagElem F
  map := coalgHomToDiagElemHom F
  map_id _ := DiagElem.Hom.ext rfl
  map_comp _ _ := DiagElem.Hom.ext rfl

def diagElemCoalgIsoCat : DiagElem (CoalgProf F) ≅Cat Endofunctor.Coalgebra F :=
  { hom := (diagElemToCoalgFunctor F).toCatHom
    inv := (coalgToDiagElemFunctor F).toCatHom
  }

/-- The equivalence between diagonal elements of `CoalgProf F` and F-coalgebras. -/
def diagElemCoalgEquiv : DiagElem (CoalgProf F) ≌ Endofunctor.Coalgebra F :=
  Cat.equivOfIso (diagElemCoalgIsoCat F)

end DiagElemCoalgebraEquiv

section DiagElemDialgebraEquiv

universe u' v'

variable {D : Type u'} [Category.{v'} D]
variable (F G : C ⥤ D)

/-!
### Diagonal elements of DialgebraProf F G are (F,G)-dialgebras

A diagonal element of `DialgebraProf F G` at object `A` consists of:
- A base object `A : C`
- An element of `DialgebraProf F G A A = (F.obj A ⟶ G.obj A)`

This is precisely the data of an (F,G)-dialgebra.
-/

/-- Convert a diagonal element of `DialgebraProf F G` to a dialgebra. -/
@[simps]
def diagElemToDialg (x : DiagElem (DialgebraProf F G)) : Dialgebra F G where
  carrier := x.base
  str := x.elem

/-- Convert a dialgebra to a diagonal element of `DialgebraProf F G`. -/
@[simps]
def dialgToDiagElem (d : Dialgebra F G) : DiagElem (DialgebraProf F G) where
  base := d.carrier
  elem := d.str

/-- Convert a morphism of diagonal elements to a dialgebra morphism. -/
@[simps]
def diagElemHomToDialgHom {x y : DiagElem (DialgebraProf F G)} (f : x ⟶ y) :
    diagElemToDialg F G x ⟶ diagElemToDialg F G y where
  base := f.base
  comm := by
    simp only [diagElemToDialg_carrier, diagElemToDialg_str]
    have hcompat := f.compat
    simp only [DiagCompat, DialgebraProf_obj_obj, DialgebraProf_obj_map,
      DialgebraProf_map_app, Quiver.Hom.unop_op] at hcompat
    exact hcompat

/-- Convert a dialgebra morphism to a morphism of diagonal elements. -/
@[simps]
def dialgHomToDiagElemHom {d₁ d₂ : Dialgebra F G}
    (f : d₁ ⟶ d₂) :
    dialgToDiagElem F G d₁ ⟶ dialgToDiagElem F G d₂ where
  base := f.base
  compat := by
    simp only [DiagCompat, dialgToDiagElem_base, dialgToDiagElem_elem,
      DialgebraProf_obj_obj, DialgebraProf_obj_map, DialgebraProf_map_app,
      Quiver.Hom.unop_op]
    exact f.comm

/-- The functor from diagonal elements of `DialgebraProf F G` to dialgebras. -/
@[simps]
def diagElemToDialgFunctor :
    DiagElem (DialgebraProf F G) ⥤ Dialgebra F G where
  obj := diagElemToDialg F G
  map := diagElemHomToDialgHom F G
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor from dialgebras to diagonal elements of `DialgebraProf F G`. -/
@[simps]
def dialgToDiagElemFunctor :
    Dialgebra F G ⥤ DiagElem (DialgebraProf F G) where
  obj := dialgToDiagElem F G
  map := dialgHomToDiagElemHom F G
  map_id _ := DiagElem.Hom.ext rfl
  map_comp _ _ := DiagElem.Hom.ext rfl

def diagElemDialgIsoCat :
    DiagElem (DialgebraProf F G) ≅Cat Dialgebra F G :=
  {
    hom := (diagElemToDialgFunctor F G).toCatHom
    inv := (dialgToDiagElemFunctor F G).toCatHom
  }

/-- The equivalence between diagonal elements of `DialgebraProf F G` and
(F,G)-dialgebras. -/
def diagElemDialgEquiv :
    DiagElem (DialgebraProf F G) ≌ Dialgebra F G :=
  Cat.equivOfIso (diagElemDialgIsoCat F G)

end DiagElemDialgebraEquiv

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

def diagElemPointedIsoCat :
    DiagElem IdProf ≅Cat Pointed.{v} :=
  { hom := (diagElemToPointedFunctor).toCatHom
    inv := (pointedToDiagElemFunctor).toCatHom
  }

/-- The equivalence between diagonal elements of `IdProf` and pointed types. -/
def diagElemPointedEquiv :
    DiagElem IdProf ≌ Pointed.{v} :=
  Cat.equivOfIso (diagElemPointedIsoCat)

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
    simp only [DiagCompat, IdProf, Functor.const_obj_obj, Functor.const_obj_map,
      Functor.id_obj, Functor.id_map, NatTrans.id_app, types_id_apply]
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
  simp only [DiagCompat, IdProf, Functor.const_obj_obj, Functor.const_obj_map,
    Functor.id_obj, Functor.id_map, NatTrans.id_app, types_id_apply] at hpara
  exact hpara

/-- The bijection between elements of an initial F-algebra and paranatural
transformations from `AlgProf F` to `IdProf`. -/
def initialAlgebraParanatEquiv (μF : Endofunctor.Algebra F) (hμF : IsInitial μF) :
    μF.a ≃ Paranat (AlgProf F) IdProf where
  toFun := initialToParanat F μF hμF
  invFun := paranatToInitial F μF
  left_inv := paranatToInitial_initialToParanat F μF hμF
  right_inv := initialToParanat_paranatToInitial F μF hμF

/-- The bijection between elements of an initial F-algebra and the
structural end `StructuralEnd (AlgProf F)`. -/
def initialAlgebraStructuralEndEquiv (μF : Endofunctor.Algebra F)
    (hμF : IsInitial μF) :
    μF.a ≃ StructuralEnd (AlgProf F) :=
  (initialAlgebraParanatEquiv F μF hμF).trans
    (structureIntegralEquivParanat (AlgProf F) IdProf).symm

end InitialAlgebraCorrespondence

section TerminalCoalgebraCorrespondence

/-!
### Structural coend and terminal coalgebras

The dual of the initial algebra correspondence: when an endofunctor
`F : Type v ⥤ Type v` has a terminal coalgebra `νF`, there is a bijection
between elements of the carrier `νF.V` and the structural coend
`StructuralCoend (CoalgProf F)`.

The structural coend `StructuralCoend (CoalgProf F) = CostructureIntegral (CoalgProf F) IdProf`
consists of:
- Pairs `(coalg, a)` where `coalg : DiagElem (CoalgProf F)` is an F-coalgebra
  and `a : coalg.base` is an element of the carrier
- Quotiented by: for a coalgebra morphism `f : coalg₁ → coalg₂`, we identify
  `(coalg₁, a) ~ (coalg₂, f(a))`

The correspondence is:
- Forward: Given `x : νF.V`, form the class `[(νF, x)]`
- Backward: Given a class `[(A, a)]`, apply the unique coalgebra hom `! : A → νF.V`
  and return `!(a)`

The terminality of `νF` ensures both round-trip properties hold.
-/

variable (F : Type v ⥤ Type v)

/-- Given an element of a terminal F-coalgebra, construct an element of the
structural coend `StructuralCoend (CoalgProf F)`. -/
def terminalToStructuralCoend (νF : Endofunctor.Coalgebra F) (x : νF.V) :
    StructuralCoend (CoalgProf F) :=
  CostructureIntegral.mk (coalgToDiagElem F νF) x

/-- Given an element of the structural coend, extract an element of the
terminal coalgebra by applying the unique coalgebra morphism. -/
def structuralCoendToTerminal (νF : Endofunctor.Coalgebra F) (hνF : IsTerminal νF)
    (c : StructuralCoend (CoalgProf F)) : νF.V :=
  CostructureIntegral.lift
    (fun (coalg : DiagElem (CoalgProf F)) (a : coalg.base) =>
      (hνF.from (diagElemToCoalg F coalg)).f a)
    (fun {x y} (f : x ⟶ y) (a : x.base) => by
      have hcompat := f.compat
      simp only [DiagCompat, CoalgProf_obj_map, CoalgProf_map_app] at hcompat
      let coalgX := diagElemToCoalg F x
      let coalgY := diagElemToCoalg F y
      let coalgHom : coalgX ⟶ coalgY := ⟨f.base, hcompat⟩
      have hUniq := hνF.hom_ext (hνF.from coalgX) (coalgHom ≫ hνF.from coalgY)
      exact congrFun (congrArg Endofunctor.Coalgebra.Hom.f hUniq) a)
    c

/-- The round-trip from terminal coalgebra element to structural coend
and back yields the original element. -/
theorem structuralCoendToTerminal_terminalToStructuralCoend
    (νF : Endofunctor.Coalgebra F) (hνF : IsTerminal νF) (x : νF.V) :
    structuralCoendToTerminal F νF hνF (terminalToStructuralCoend F νF x) = x := by
  have h := hνF.hom_ext (hνF.from νF) (𝟙 νF)
  have hf : (hνF.from νF).f = id := congrArg Endofunctor.Coalgebra.Hom.f h
  unfold structuralCoendToTerminal terminalToStructuralCoend
  simp only [CostructureIntegral.mk, CostructureIntegral.lift,
    Quotient.lift_mk, coalgToDiagElem, diagElemToCoalg, hf]
  rfl

/-- The round-trip from structural coend to terminal coalgebra element
and back yields the original element. -/
theorem terminalToStructuralCoend_structuralCoendToTerminal
    (νF : Endofunctor.Coalgebra F) (hνF : IsTerminal νF)
    (c : StructuralCoend (CoalgProf F)) :
    terminalToStructuralCoend F νF (structuralCoendToTerminal F νF hνF c) = c := by
  induction c using Quotient.ind with
  | _ p =>
    let ⟨coalg, a⟩ := p
    unfold structuralCoendToTerminal terminalToStructuralCoend
    simp only [CostructureIntegral.mk, CostructureIntegral.lift, Quotient.lift_mk]
    apply Quotient.sound
    let coalgObj := diagElemToCoalg F coalg
    let homToν := hνF.from coalgObj
    let coalgHom := coalgHomToDiagElemHom F homToν
    apply Relation.EqvGen.symm
    apply Relation.EqvGen.rel
    refine ⟨⟨coalg, coalgToDiagElem F νF, coalgHom, a⟩, rfl, ?_⟩
    simp only [costructIntMapCov, covAction, IdProf, coalgToDiagElem_base,
      diagElemToCoalg]
    rfl

/-- The bijection between elements of a terminal F-coalgebra and the
structural coend `StructuralCoend (CoalgProf F)`. -/
def terminalCoalgebraStructuralCoendEquiv (νF : Endofunctor.Coalgebra F)
    (hνF : IsTerminal νF) :
    νF.V ≃ StructuralCoend (CoalgProf F) where
  toFun := terminalToStructuralCoend F νF
  invFun := structuralCoendToTerminal F νF hνF
  left_inv := structuralCoendToTerminal_terminalToStructuralCoend F νF hνF
  right_inv := terminalToStructuralCoend_structuralCoendToTerminal F νF hνF

end TerminalCoalgebraCorrespondence

section StructuralEndSections

/-!
### Structural ends as sections of the forgetful functor

The structural end `StructuralEnd F` is the type of families
`(x : DiagElem F) → x.base` satisfying paranaturality:
`f.base (φ x) = φ y` for all `f : x ⟶ y` in `DiagElem F`.

This is equivalent to `(DiagElem.forget F).sections`, the
sections of the forgetful functor `DiagElem F ⥤ Type v`.
The sections of a functor `G : J ⥤ Type v` are the
compatible families `(j : J) → G.obj j` satisfying
`G.map f (u j) = u j'` for all morphisms `f : j ⟶ j'`.

Since limits in `Type v` are computed by sections, this
identifies `StructuralEnd F` with the limit of
`DiagElem.forget F` in `Type v`.

For `F = AlgProf G`, the equivalence
`DiagElem (AlgProf G) ≌ Endofunctor.Algebra G` identifies
`DiagElem.forget (AlgProf G)` with
`Endofunctor.Algebra.forget G`, so:
```
StructuralEnd (AlgProf G) ≃ (Algebra.forget G).sections
```
connecting the paranatural end to the limit of the diagram
of G-algebras projected to their carriers.
-/

variable (F : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v)

/-- The structural end maps to sections of the forgetful
functor on diagonal elements. The family of a structural end
element is a section because paranaturality gives exactly
the sections compatibility condition. -/
def structuralEndToSections
    (φ : StructuralEnd F) :
    (DiagElem.forget F).sections :=
  ⟨φ.family, fun f => φ.paranatural f⟩

/-- A section of the forgetful functor on diagonal elements
gives a structural end element. The sections compatibility
`f.base (u x) = u y` provides the equalizer condition. -/
def sectionsToStructuralEnd
    (s : (DiagElem.forget F).sections) :
    StructuralEnd F where
  family := s.val
  equalizer := by
    funext x y f
    exact s.property f

/-- The structural end `StructuralEnd F` is equivalent to
sections of the forgetful functor `DiagElem.forget F`.
Since limits in `Type v` are computed by sections, this
identifies `StructuralEnd F` with
`lim (DiagElem.forget F)`. -/
def structuralEndEquivSections :
    StructuralEnd F ≃
      (DiagElem.forget F).sections where
  toFun := structuralEndToSections F
  invFun := sectionsToStructuralEnd F
  left_inv _ := rfl
  right_inv _ := rfl

end StructuralEndSections

section StructuralEndIsLimit

/-!
### Structural end as a limit cone

`StructuralEnd F` satisfies the universal property of the
limit of the forgetful functor `DiagElem.forget F`, making
it a limit in the formal sense of mathlib's `IsLimit`.

Since `DiagElem F : Type (v+1)` while
`DiagElem.forget F : DiagElem F ⥤ Type v`, the sections
live in `Type (v+1)`. To form a cone in the correct
universe, we compose with
`uliftFunctor.{v+1, v} : Type v ⥤ Type (v+1)`.
-/

variable (F : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v)

/-- The structural end as the cone point of a limit cone
for the universe-lifted forgetful functor on diagonal
elements.  The projections extract components of the
compatible family. -/
def structuralEndLimitCone :
    Limits.Cone
      (DiagElem.forget F ⋙ uliftFunctor.{v + 1}) where
  pt := StructuralEnd F
  π :=
    { app := fun x φ => ⟨φ.family x⟩
      naturality := fun x y f => by
        funext φ
        simp only [
          Functor.comp_obj,
          Functor.const_obj_obj,
          Functor.comp_map,
          Functor.const_obj_map,
          Category.id_comp,
          uliftFunctor_obj,
          DiagElem.forget_map
        ]
        exact congrArg ULift.up
          (φ.paranatural f).symm }

/-- The structural end limit cone is a limit: for any
cone `s` over the lifted forgetful functor, there is a
unique morphism `s.pt → StructuralEnd F` commuting with
all projections. -/
def structuralEndLimitCone_isLimit :
    Limits.IsLimit (structuralEndLimitCone F) where
  lift s p :=
    { family := fun x => (s.π.app x p).down
      equalizer := by
        funext x y f
        dsimp [structIntMapCov, structIntMapContrav,
          covAction, contravAction]
        exact congrArg ULift.down
          (congr_fun (s.w f) p) }
  fac s j := by
    funext p
    exact (ULift.up_down _).symm
  uniq s m hm := by
    funext p
    exact StructureIntegral.ext
      (funext fun x =>
        congrArg ULift.down (congr_fun (hm x) p))

end StructuralEndIsLimit

section StructuralCoendIsColimit

/-!
### Structural coend as a colimit cocone

`StructuralCoend F` satisfies the universal property of the
colimit of the forgetful functor `DiagElem.forget F`, making
it a colimit in the formal sense of mathlib's `IsColimit`.

As with the limit case, we compose with
`uliftFunctor.{v+1, v} : Type v ⥤ Type (v+1)` to match the
universe of `DiagElem F : Type (v+1)`.
-/

variable (F : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v)

/-- The structural coend as the cocone point of a colimit
cocone for the universe-lifted forgetful functor on diagonal
elements.  The coprojections inject elements via the quotient
map `CostructureIntegral.mk`. -/
def structuralCoendColimitCocone :
    Limits.Cocone
      (DiagElem.forget F ⋙ uliftFunctor.{v + 1}) where
  pt := StructuralCoend F
  ι :=
    { app := fun x a => CostructureIntegral.mk x a.down
      naturality := fun x y f => by
        funext a
        simp only [
          Functor.comp_obj,
          Functor.const_obj_obj,
          Functor.comp_map,
          DiagElem.forget_map,
          Functor.const_obj_map
        ]
        exact (structuralCoend_sound F f a.down).symm }

/-- The structural coend colimit cocone is a colimit: for
any cocone `s` over the lifted forgetful functor, there is a
unique morphism `StructuralCoend F → s.pt` commuting with
all coprojections. -/
def structuralCoendColimitCocone_isColimit :
    Limits.IsColimit
      (structuralCoendColimitCocone F) where
  desc s :=
    CostructureIntegral.lift
      (fun x a => s.ι.app x ⟨a⟩)
      (fun {x y} f ψ => by
        dsimp [contravAction, covAction]
        exact (congr_fun (s.w f) ⟨ψ⟩).symm)
  fac s j := by
    funext a
    change s.ι.app j ⟨a.down⟩ = s.ι.app j a
    exact congrArg (s.ι.app j) (ULift.up_down a)
  uniq s m hm :=
    funext (Quotient.ind fun ⟨x, a⟩ =>
      congr_fun (hm x) ⟨a⟩)

end StructuralCoendIsColimit

section AlgebraSections

/-!
### Algebra forgetful functor sections

The equivalence `DiagElem (AlgProf G) ≌ Endofunctor.Algebra G`
identifies `DiagElem.forget (AlgProf G)` with
`Endofunctor.Algebra.forget G`. Composing with
`structuralEndEquivSections` connects the structural end
to sections of mathlib's forgetful functor on algebras.
-/

variable (G : Type v ⥤ Type v)

/-- The forgetful functor on `DiagElem (AlgProf G)` equals
the composition of the equivalence functor with mathlib's
algebra forgetful functor. -/
theorem diagElemAlg_forget_eq :
    DiagElem.forget (AlgProf G) =
      diagElemToAlgFunctor G ⋙
        Endofunctor.Algebra.forget G := by
  refine _root_.CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => ?_)
  simp only [
    eqToHom_refl,
    Category.comp_id,
    Category.id_comp,
    DiagElem.forget_map,
    Functor.comp_map,
    Endofunctor.Algebra.forget,
    diagElemToAlgFunctor,
    diagElemHomToAlgHom
  ]

/-- The structural end of `AlgProf G` is equivalent to
sections of mathlib's algebra forgetful functor
composed with the `DiagElem`-to-`Algebra` equivalence.

Composing with `initialAlgebraStructuralEndEquiv`, this
gives:
```
(diagElemToAlgFunctor G ⋙ Algebra.forget G).sections
  ≃ StructuralEnd (AlgProf G)
  ≃ μG.a
```
connecting the limit of the diagram of G-algebras
(projected to carriers) to the initial algebra carrier. -/
def algSectionsEquivStructuralEnd :
    (diagElemToAlgFunctor G ⋙
      Endofunctor.Algebra.forget G).sections ≃
    StructuralEnd (AlgProf G) :=
  (Equiv.cast
    (congrArg (↑·.sections)
      (diagElemAlg_forget_eq G).symm)).trans
    (structuralEndEquivSections (AlgProf G)).symm

end AlgebraSections

section CoalgebraSections

/-!
### Coalgebra forgetful functor sections

The dual of the algebra case: the equivalence
`DiagElem (CoalgProf G) ≌ Endofunctor.Coalgebra G`
identifies `DiagElem.forget (CoalgProf G)` with
`Endofunctor.Coalgebra.forget G`.
-/

variable (G : Type v ⥤ Type v)

/-- The forgetful functor on `DiagElem (CoalgProf G)` equals
the composition of the equivalence functor with mathlib's
coalgebra forgetful functor. -/
theorem diagElemCoalg_forget_eq :
    DiagElem.forget (CoalgProf G) =
      diagElemToCoalgFunctor G ⋙
        Endofunctor.Coalgebra.forget G := by
  refine _root_.CategoryTheory.Functor.ext (fun _ => rfl) (fun _ _ _ => ?_)
  simp only [
    eqToHom_refl,
    Category.comp_id,
    Category.id_comp,
    DiagElem.forget_map,
    Functor.comp_map,
    Endofunctor.Coalgebra.forget,
    diagElemToCoalgFunctor,
    diagElemHomToCoalgHom
  ]

/-- The structural end of `CoalgProf G` is equivalent to
sections of mathlib's coalgebra forgetful functor
composed with the `DiagElem`-to-`Coalgebra` equivalence.

Composing with `terminalCoalgebraStructuralCoendEquiv`,
this connects the limit of the diagram of G-coalgebras
(projected to carriers) to the terminal coalgebra carrier.
-/
def coalgSectionsEquivStructuralEnd :
    (diagElemToCoalgFunctor G ⋙
      Endofunctor.Coalgebra.forget G).sections ≃
    StructuralEnd (CoalgProf G) :=
  (Equiv.cast
    (congrArg (↑·.sections)
      (diagElemCoalg_forget_eq G).symm)).trans
    (structuralEndEquivSections (CoalgProf G)).symm

end CoalgebraSections

end GebLean
