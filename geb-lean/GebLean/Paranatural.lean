import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Discrete.Basic
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Opposites
import GebLean.Utilities.ConnectedGrothendieck
import GebLean.Utilities.Elements
import GebLean.Utilities.TwistedArrow

/-!
# Category of diagonal elements and paranatural transformations

Given an endoprofunctor `F : Cᵒᵖ ⥤ C ⥤ Type`, the category of diagonal
elements has as objects pairs `(I, g)` where `I : C` and `g : F.obj (op I) I`,
and as morphisms from `(I₀, g₀)` to `(I₁, g₁)` those morphisms `f : I₀ ⟶ I₁`
satisfying `(F.obj (op I₀)).map f g₀ = (F.map (op f)).app I₁ g₁`.

A paranatural transformation between two endoprofunctors `F` and `G` is
a family of functions `α_I : F.obj (op I) I → G.obj (op I) I` that preserves
the diagonal morphism condition: if `(F.obj (op I₀)).map f d₀ = (F.map (op f)).app I₁ d₁`,
then `(G.obj (op I₀)).map f (α I₀ d₀) = (G.map (op f)).app I₁ (α I₁ d₁)`.

## References

* Definition 2.7 in Neumann, "Paranatural Category Theory"
* https://ncatlab.org/nlab/show/algebra+for+a+profunctor

-/

namespace GebLean

open CategoryTheory

universe u v

variable {C : Type u} [Category.{v} C]

section DiagonalElements

universe w

variable (F : Cᵒᵖ ⥤ C ⥤ Type w)

/-- Apply an endoprofunctor at the diagonal: `diagApp F I` is `F(I, I)`. -/
abbrev diagApp (I : C) : Type w := (F.obj (Opposite.op I)).obj I

/-- The type of diagonal elements for an endoprofunctor `F : Cᵒᵖ ⥤ C ⥤ Type w`.
An object consists of a base object `I : C` and a diagonal element
`elem : (F.obj (op I)).obj I`. -/
@[ext]
structure DiagElem where
  /-- The base object in `C` -/
  base : C
  /-- The diagonal element in `diagApp F base` -/
  elem : diagApp F base

/-- The diagonal compatibility condition for an endoprofunctor. Given a morphism
`f : I₀ ⟶ I₁` and diagonal elements `d₀ ∈ F(I₀, I₀)` and `d₁ ∈ F(I₁, I₁)`,
this asserts that the covariant action of `f` on `d₀` equals the contravariant
action of `f` on `d₁`. -/
@[simp]
def DiagCompat (I₀ I₁ : C) (f : I₀ ⟶ I₁)
    (d₀ : diagApp F I₀) (d₁ : diagApp F I₁) : Prop :=
  (F.obj (Opposite.op I₀)).map f d₀ = (F.map f.op).app I₁ d₁

/-- A morphism in the category of diagonal elements from `(I₀, g₀)` to `(I₁, g₁)`
is a morphism `f : I₀ ⟶ I₁` in `C` such that the covariant action of `f` on `g₀`
equals the contravariant action of `f` on `g₁`. -/
@[ext]
structure DiagElem.Hom (x y : DiagElem F) where
  /-- The underlying morphism in `C` -/
  base : x.base ⟶ y.base
  /-- The compatibility condition: covariant action on source element equals
  contravariant action on target element -/
  compat : DiagCompat F x.base y.base base x.elem y.elem

namespace DiagElem

/-- The identity morphism on a diagonal element. -/
@[simp]
def Hom.id (x : DiagElem F) : Hom F x x where
  base := 𝟙 x.base
  compat := by simp

/-- Composition of morphisms of diagonal elements. -/
@[simp]
def Hom.comp {x y z : DiagElem F} (f : Hom F x y) (g : Hom F y z) :
    Hom F x z where
  base := f.base ≫ g.base
  compat := by
    simp only [DiagCompat, Functor.map_comp]
    change (F.obj (Opposite.op x.base)).map g.base
        ((F.obj (Opposite.op x.base)).map f.base x.elem) =
      (F.map (f.base ≫ g.base).op).app z.base z.elem
    rw [f.compat]
    have nat := congrFun ((F.map f.base.op).naturality g.base) y.elem
    simp only [types_comp_apply] at nat
    rw [← nat, g.compat]
    rw [op_comp]
    simp only [Functor.map_comp, NatTrans.comp_app, types_comp_apply]

instance diagElemCategory : Category (DiagElem F) where
  Hom := Hom F
  id := Hom.id F
  comp := Hom.comp F
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp [Category.assoc]

/-- The base component of `eqToHom` in `DiagElem` is `eqToHom` in `C`. -/
@[simp]
theorem Hom.eqToHom_base {x y : DiagElem F} (h : x = y) :
    (eqToHom h).base = eqToHom (congrArg DiagElem.base h) := by
  subst h
  rfl

/-- The base component of a composition in `DiagElem`. -/
@[simp]
theorem Hom.comp_base {x y z : DiagElem F} (f : x ⟶ y) (g : y ⟶ z) :
    (f ≫ g).base = f.base ≫ g.base :=
  rfl

variable {F}
variable {G : Cᵒᵖ ⥤ C ⥤ Type w}

/-- A natural transformation `η : F ⟶ G` induces a functor `DiagElem F ⥤ DiagElem G`
by applying `η` to diagonal elements. -/
@[simps]
def map (η : F ⟶ G) : DiagElem F ⥤ DiagElem G where
  obj x := ⟨x.base, (η.app (Opposite.op x.base)).app x.base x.elem⟩
  map {x y} f := ⟨f.base, by
    simp only [DiagCompat]
    have nat_cov := congrFun ((η.app (Opposite.op x.base)).naturality f.base) x.elem
    simp only [types_comp_apply] at nat_cov
    rw [← nat_cov, f.compat]
    have nat_con := congrFun (congrArg (NatTrans.app · y.base) (η.naturality f.base.op)) y.elem
    simp only [types_comp_apply, NatTrans.comp_app] at nat_con
    exact nat_con⟩
  map_id x := Hom.ext rfl
  map_comp f g := Hom.ext rfl

/-- `DiagElem.map` sends the identity natural transformation to the identity functor. -/
@[simp]
theorem map_id_nat : map (𝟙 F) = 𝟭 (DiagElem F) := by
  refine Functor.ext (fun x => ?_) (fun x y f => ?_)
  · apply DiagElem.ext <;> rfl
  · simp only [Functor.id_map, eqToHom_refl, Category.comp_id, Category.id_comp]
    apply Hom.ext; rfl

variable {H : Cᵒᵖ ⥤ C ⥤ Type w}

/-- `DiagElem.map` preserves composition of natural transformations. -/
@[simp]
theorem map_comp_nat (η : F ⟶ G) (θ : G ⟶ H) :
    map (η ≫ θ) = map η ⋙ map θ := by
  refine Functor.ext (fun x => ?_) (fun x y f => ?_)
  · apply DiagElem.ext <;> rfl
  · simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp]
    apply Hom.ext; rfl

variable (F) in
/-- The forgetful functor from the category of diagonal elements to the base
category, projecting out the underlying object. -/
@[simps]
def forget : DiagElem F ⥤ C where
  obj x := x.base
  map f := f.base
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The forgetful functor is faithful: morphisms in `DiagElem F` are determined
by their base component. The compatibility condition is a property (a proof),
not additional data, so two morphisms with the same base are equal. -/
instance forget_faithful : (forget F).Faithful where
  map_injective h := Hom.ext h

/-- `DiagElem.map` commutes with the forgetful functor: the square
```
DiagElem F --map η--> DiagElem G
    |                     |
 forget F              forget G
    |                     |
    v                     v
    C ========id========= C
```
commutes. -/
theorem map_forget (η : F ⟶ G) : map η ⋙ forget G = forget F := by
  refine Functor.ext (fun x => ?_) (fun x y f => ?_)
  · rfl
  · simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp,
      map_map_base, forget_map]

end DiagElem

/-- The functor from endoprofunctors on `C` to the category of categories,
sending each endoprofunctor `F` to its category of diagonal elements. -/
@[simps]
def diagElemFunctor : (Cᵒᵖ ⥤ C ⥤ Type w) ⥤ Cat where
  obj F := Cat.of (DiagElem F)
  map η := DiagElem.map η
  map_id _ := DiagElem.map_id_nat
  map_comp η θ := DiagElem.map_comp_nat η θ

end DiagonalElements

section DiagElemSlice

/-- The functor from endoprofunctors on `C` (valued in `Type u` to match `C`)
to the slice category `Cat/C`, sending each endoprofunctor `F` to the pair
`(DiagElem F, forget F)`. The commutativity of the forgetful functor with
`DiagElem.map` ensures this is well-defined on morphisms.

Note: This requires the profunctor to be valued in `Type u` (same universe as
`C`) for the slice category to be well-defined. For general universe levels,
see `diagElemFunctor` which targets `Cat` directly. -/
def diagElemSliceFunctor (C : Type u) [Category.{v} C] :
    (Cᵒᵖ ⥤ C ⥤ Type u) ⥤ Over (Cat.of C) :=
  { obj := fun F => Over.mk (Y := Cat.of (DiagElem F)) (DiagElem.forget F)
    map := fun {F G} η => Over.homMk (DiagElem.map η)
    map_id := fun F => Over.OverMorphism.ext DiagElem.map_id_nat
    map_comp := fun {F G H} η θ => Over.OverMorphism.ext (DiagElem.map_comp_nat η θ) }

end DiagElemSlice

section Paranatural

universe w

variable (F G : Cᵒᵖ ⥤ C ⥤ Type w)

/-- The type of component families for a (potential) paranatural transformation
between two endoprofunctors. This is the signature without the paranaturality
condition. -/
def ParanatSig : Type (max u w) :=
  (I : C) → diagApp F I → diagApp G I

/-- The paranaturality condition for a family of functions between diagonal
elements of two endoprofunctors. A family `α` is paranatural if whenever
the covariant and contravariant actions of a morphism agree on elements of `F`,
then the same morphism's actions agree on the images under `α` in `G`. -/
def IsParanatural (α : ParanatSig F G) : Prop :=
  ∀ (I₀ I₁ : C) (f : I₀ ⟶ I₁) (d₀ : diagApp F I₀) (d₁ : diagApp F I₁),
    DiagCompat F I₀ I₁ f d₀ d₁ → DiagCompat G I₀ I₁ f (α I₀ d₀) (α I₁ d₁)

/-- A paranatural transformation between two endoprofunctors `F` and `G` on `C`.
A family of functions on diagonal elements that preserves the compatibility
condition for morphisms between diagonal elements. -/
@[ext]
structure Paranat where
  /-- The component of the paranatural transformation at object `I` -/
  app : ParanatSig F G
  /-- The paranaturality condition -/
  paranatural : IsParanatural F G app

/-- Restriction of a natural transformation between endoprofunctors to the
diagonal. Given `η : F ⟶ G`, we obtain a family of functions on diagonal
elements by applying `η` at both contravariant and covariant positions. -/
def NatTrans.restrict (η : F ⟶ G) : ParanatSig F G :=
  fun I d => (η.app (Opposite.op I)).app I d

/-- The restriction of a natural transformation to the diagonal is paranatural.
This uses naturality in both the contravariant and covariant directions,
combined with the identity laws for the category. -/
theorem NatTrans.restrict_isParanatural (η : F ⟶ G) :
    IsParanatural F G (NatTrans.restrict F G η) := by
  intro I₀ I₁ f d₀ d₁ hcompat
  simp only [NatTrans.restrict, DiagCompat]
  have nat_cov := congrFun ((η.app (Opposite.op I₀)).naturality f) d₀
  simp only [types_comp_apply] at nat_cov
  rw [← nat_cov, hcompat]
  have nat_con := congrFun (congrArg (NatTrans.app · I₁) (η.naturality f.op)) d₁
  simp only [types_comp_apply, NatTrans.comp_app] at nat_con
  exact nat_con

/-- Construct a paranatural transformation from a natural transformation
by restricting to the diagonal. -/
def Paranat.ofNatTrans (η : F ⟶ G) : Paranat F G where
  app := NatTrans.restrict F G η
  paranatural := NatTrans.restrict_isParanatural F G η

namespace Paranat

variable {F G}

/-- The identity paranatural transformation on an endoprofunctor. -/
@[simp]
def id : Paranat F F where
  app _ d := d
  paranatural _ _ _ _ _ h := h

variable {H : Cᵒᵖ ⥤ C ⥤ Type w}

/-- Composition of paranatural transformations. -/
@[simp]
def comp (α : Paranat F G) (β : Paranat G H) : Paranat F H where
  app I d := β.app I (α.app I d)
  paranatural I₀ I₁ f d₀ d₁ hF := β.paranatural I₀ I₁ f _ _ (α.paranatural I₀ I₁ f d₀ d₁ hF)

end Paranat

/-- The type of endoprofunctors on a category `C`, viewed as objects of a
category where morphisms are paranatural transformations. -/
def EndoProf : Type max u v (w + 1) := Cᵒᵖ ⥤ C ⥤ Type w

instance endoProfCategory : Category (EndoProf (C := C)) where
  Hom F G := Paranat F G
  id F := Paranat.id
  comp := Paranat.comp
  id_comp _ := by ext; rfl
  comp_id _ := by ext; rfl
  assoc _ _ _ := by ext; rfl

end Paranatural

section ParanaturalSliceEquiv

/-!
## Equivalence between paranatural transformations and slice morphisms

A paranatural transformation `α : Paranat F G` corresponds precisely to a
morphism in `Over (Cat.of C)` from `(DiagElem F, forget F)` to
`(DiagElem G, forget G)`. This section establishes this correspondence,
showing that `EndoProf` embeds fully faithfully into `Cat/C`.
-/

variable (C : Type u) [Category.{v} C]
variable (F G : Cᵒᵖ ⥤ C ⥤ Type u)

/-- A paranatural transformation induces a functor between diagonal element
categories. The functor preserves the base object and transforms diagonal
elements via the paranatural components. -/
@[simps]
def Paranat.toFunctor (α : Paranat F G) : DiagElem F ⥤ DiagElem G where
  obj x := ⟨x.base, α.app x.base x.elem⟩
  map {x y} f := ⟨f.base, α.paranatural x.base y.base f.base x.elem y.elem f.compat⟩
  map_id _ := DiagElem.Hom.ext rfl
  map_comp _ _ := DiagElem.Hom.ext rfl

/-- The functor induced by a paranatural transformation commutes with the
forgetful functors to `C`. -/
theorem Paranat.toFunctor_forget (α : Paranat F G) :
    α.toFunctor ⋙ DiagElem.forget G = DiagElem.forget F := by
  refine Functor.ext (fun x => ?_) (fun x y f => ?_)
  · rfl
  · simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp,
      toFunctor_map_base, DiagElem.forget_map]

/-- A paranatural transformation induces a morphism in the slice category
`Over (Cat.of C)`. -/
def Paranat.toOverHom (α : Paranat F G) :
    (diagElemSliceFunctor C).obj F ⟶ (diagElemSliceFunctor C).obj G :=
  Over.homMk α.toFunctor (α.toFunctor_forget)

variable {F G}

/-- The slice condition for an Over morphism: the functor composition with
the forgetful functor equals the domain's forgetful functor. -/
theorem sliceCondition
    (φ : (diagElemSliceFunctor C).obj F ⟶ (diagElemSliceFunctor C).obj G) :
    φ.left ⋙ DiagElem.forget G = DiagElem.forget F := by
  have h := φ.w
  simp only [diagElemSliceFunctor, Over.mk_left, Over.mk_hom] at h
  exact h

/-- A slice morphism preserves the base object of diagonal elements. -/
theorem sliceCondition_obj
    (φ : (diagElemSliceFunctor C).obj F ⟶ (diagElemSliceFunctor C).obj G)
    (x : DiagElem F) :
    (φ.left.obj x).base = x.base :=
  congrFun (congrArg Functor.obj (sliceCondition C φ)) x

/-- A slice morphism preserves the base of mapped morphisms, via transport. -/
theorem sliceCondition_map
    (φ : (diagElemSliceFunctor C).obj F ⟶ (diagElemSliceFunctor C).obj G)
    {x y : DiagElem F} (f : x ⟶ y) :
    (φ.left.map f).base =
      eqToHom (sliceCondition_obj C φ x) ≫ f.base ≫
        eqToHom (sliceCondition_obj C φ y).symm := by
  have heq := sliceCondition C φ
  have h := Functor.congr_hom heq f
  simp only [Functor.comp_map, DiagElem.forget_map] at h
  exact h

/-- Extract a paranatural transformation from a slice morphism. The slice
condition ensures the functor preserves base objects, giving us a family
of functions on diagonal elements. Functoriality ensures paranaturality. -/
def Paranat.ofOverHom
    (φ : (diagElemSliceFunctor C).obj F ⟶ (diagElemSliceFunctor C).obj G) :
    Paranat F G where
  app I d :=
    let x : DiagElem F := ⟨I, d⟩
    let y : DiagElem G := φ.left.obj x
    have hbase : y.base = I := sliceCondition_obj C φ x
    hbase ▸ y.elem
  paranatural := fun I₀ I₁ f d₀ d₁ hcompat => by
    simp only [DiagCompat]
    let x₀ : DiagElem F := ⟨I₀, d₀⟩
    let x₁ : DiagElem F := ⟨I₁, d₁⟩
    let mor : x₀ ⟶ x₁ := ⟨f, hcompat⟩
    let y₀ := φ.left.obj x₀
    let y₁ := φ.left.obj x₁
    let hmor := φ.left.map mor
    have hcompat' : DiagCompat G y₀.base y₁.base hmor.base y₀.elem y₁.elem := hmor.compat
    simp only [DiagCompat] at hcompat'
    have hbase₀ : y₀.base = I₀ := sliceCondition_obj C φ x₀
    have hbase₁ : y₁.base = I₁ := sliceCondition_obj C φ x₁
    have hmor_base := sliceCondition_map C φ mor
    suffices h : ∀ (b₀ b₁ : C) (g : b₀ ⟶ b₁) (e₀ : diagApp G b₀) (e₁ : diagApp G b₁)
        (h₀ : b₀ = I₀) (h₁ : b₁ = I₁) (_ : g = eqToHom h₀ ≫ f ≫ eqToHom h₁.symm)
        (_ : DiagCompat G b₀ b₁ g e₀ e₁),
        (G.obj (Opposite.op I₀)).map f (h₀ ▸ e₀) =
          (G.map f.op).app I₁ (h₁ ▸ e₁) by
      exact h y₀.base y₁.base hmor.base y₀.elem y₁.elem hbase₀ hbase₁ hmor_base hcompat'
    intro b₀ b₁ g e₀ e₁ h₀ h₁ hg hc
    subst h₀ h₁
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp] at hg
    subst hg
    exact hc

/-- Converting a paranatural transformation to a slice morphism and back
yields the original transformation. -/
@[simp]
theorem Paranat.ofOverHom_toOverHom (α : Paranat F G) :
    ofOverHom C (toOverHom C F G α) = α := by
  ext
  rfl

/-- Converting a slice morphism to a paranatural transformation and back
yields the original slice morphism. -/
@[simp]
theorem Paranat.toOverHom_ofOverHom
    (φ : (diagElemSliceFunctor C).obj F ⟶ (diagElemSliceFunctor C).obj G) :
    toOverHom C F G (ofOverHom C φ) = φ := by
  apply Over.OverMorphism.ext
  refine Functor.ext ?h_obj ?h_map
  case h_obj =>
    intro x
    apply DiagElem.ext
    · exact (sliceCondition_obj C φ x).symm
    · simp only [ofOverHom, toOverHom, Over.homMk_left, toFunctor_obj_base,
        toFunctor_obj_elem, eqRec_eq_cast]
      exact cast_heq _ _
  case h_map =>
    intro x y f
    apply DiagElem.Hom.ext
    simp only [ofOverHom, toOverHom, Over.homMk_left, toFunctor_map_base]
    rw [DiagElem.Hom.comp_base, DiagElem.Hom.comp_base,
        DiagElem.Hom.eqToHom_base, DiagElem.Hom.eqToHom_base]
    rw [sliceCondition_map]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_trans, eqToHom_refl,
      Category.comp_id, Category.id_comp]

/-- The equivalence between paranatural transformations and slice morphisms.
This shows that `Paranat F G` is isomorphic to the hom-set in `Over (Cat.of C)`
between the diagonal element categories. -/
def paranaturalSliceEquiv :
    Paranat F G ≃
    ((diagElemSliceFunctor C).obj F ⟶ (diagElemSliceFunctor C).obj G) where
  toFun := Paranat.toOverHom C F G
  invFun := Paranat.ofOverHom C
  left_inv := Paranat.ofOverHom_toOverHom C
  right_inv := Paranat.toOverHom_ofOverHom C

end ParanaturalSliceEquiv

section EndoProfFullyFaithful

/-!
## EndoProf as a full subcategory of Cat/C

The category `EndoProf` of endoprofunctors with paranatural transformations
embeds fully faithfully into the slice category `Cat/C` via the diagonal
elements construction. This establishes `EndoProf` as a full subcategory
of `Cat/C`, where the objects are those of the form `(DiagElem F, forget F)`.
-/

variable (C : Type u) [Category.{v} C]

/-- The functor induced by a paranatural identity is the identity functor. -/
@[simp]
theorem Paranat.toFunctor_id (F : Cᵒᵖ ⥤ C ⥤ Type u) :
    (Paranat.id (F := F)).toFunctor = 𝟭 (DiagElem F) := by
  refine Functor.ext (fun x => ?_) (fun x y f => ?_)
  · rfl
  · simp only [Functor.id_map, eqToHom_refl, Category.comp_id, Category.id_comp]
    rfl

/-- `Paranat.toOverHom` sends the identity to the identity morphism. -/
@[simp]
theorem Paranat.toOverHom_id (F : Cᵒᵖ ⥤ C ⥤ Type u) :
    Paranat.toOverHom C F F Paranat.id = 𝟙 ((diagElemSliceFunctor C).obj F) := by
  apply Over.OverMorphism.ext
  exact Paranat.toFunctor_id C F

/-- The functor induced by a composition of paranatural transformations is
the composition of the induced functors. -/
@[simp]
theorem Paranat.toFunctor_comp {F G H : Cᵒᵖ ⥤ C ⥤ Type u}
    (α : Paranat F G) (β : Paranat G H) :
    (α.comp β).toFunctor = α.toFunctor ⋙ β.toFunctor := by
  refine Functor.ext (fun x => ?_) (fun x y f => ?_)
  · rfl
  · simp only [Functor.comp_map, eqToHom_refl, Category.comp_id, Category.id_comp]
    rfl

/-- `Paranat.toOverHom` preserves composition. -/
@[simp]
theorem Paranat.toOverHom_comp {F G H : Cᵒᵖ ⥤ C ⥤ Type u}
    (α : Paranat F G) (β : Paranat G H) :
    Paranat.toOverHom C F H (α.comp β) =
      Paranat.toOverHom C F G α ≫ Paranat.toOverHom C G H β := by
  apply Over.OverMorphism.ext
  exact Paranat.toFunctor_comp C α β

/-- The functor from `EndoProf` to `Over (Cat.of C)` sending each endoprofunctor
to its category of diagonal elements with the forgetful functor to `C`.
Morphisms (paranatural transformations) are sent to slice morphisms via the
induced functors on diagonal elements. -/
def diagElemEndoProf : EndoProf (C := C) ⥤ Over (Cat.of C) where
  obj F := (diagElemSliceFunctor C).obj F
  map α := Paranat.toOverHom C _ _ α
  map_id F := Paranat.toOverHom_id C F
  map_comp α β := Paranat.toOverHom_comp C α β

/-- `diagElemEndoProf` is fully faithful, establishing `EndoProf` as a full
subcategory of `Cat/C`. The objects of this subcategory are precisely those
of the form `(DiagElem F, forget F)` for endoprofunctors `F`. -/
def diagElemEndoProf_fullyFaithful : (diagElemEndoProf C).FullyFaithful where
  preimage φ := Paranat.ofOverHom C φ
  map_preimage φ := Paranat.toOverHom_ofOverHom C φ
  preimage_map α := Paranat.ofOverHom_toOverHom C α

instance diagElemEndoProf_full : (diagElemEndoProf C).Full :=
  (diagElemEndoProf_fullyFaithful C).full

instance diagElemEndoProf_faithful : (diagElemEndoProf C).Faithful :=
  (diagElemEndoProf_fullyFaithful C).faithful

end EndoProfFullyFaithful

section Paranat2

/-!
## 2-categorical structure: transformations between paranatural transformations

Given two paranatural transformations `α β : Paranat F G`, we can view them
as functors `α.toFunctor β.toFunctor : DiagElem F ⥤ DiagElem G`. A natural
transformation between these functors constitutes a "2-morphism" between
paranatural transformations.

### Slice 2-morphisms and faithfulness

In the slice 2-category `Cat/C`, a 2-morphism `θ : H ⟹ K` between 1-morphisms
`H, K : (D, F) → (E, G)` must satisfy `G(θ_d) = 𝟙` for all `d : D`. This
constraint means `θ_d` lies in the kernel of `G` on morphisms.

The triviality of 2-morphisms depends on the **faithfulness** of the structure
morphism `G : E ⥤ C`:

- If `G` is faithful, then `G(θ_d) = 𝟙` implies `θ_d = 𝟙`, forcing all
  2-morphisms to be identities (locally discrete).
- If `G` is not faithful, non-trivial 2-morphisms can exist in the kernel.

For example, `Cat/1 ≃ Cat` as a 2-category with full 2-morphism structure,
since the unique functor to the terminal category is maximally non-faithful.

### Our case

The forgetful functor `DiagElem.forget G : DiagElem G ⥤ C` is faithful because
morphisms in `DiagElem G` are determined by their base component (the
compatibility condition is a property, not additional data). This faithfulness
forces the locally discrete structure: any slice-compatible 2-morphism between
paranatural transformations implies they are equal.
-/

variable (C : Type u) [Category.{v} C]
variable {F G : Cᵒᵖ ⥤ C ⥤ Type u}

/-- A 2-morphism in the slice category `Cat/C` between two slice morphisms.
This consists of a natural transformation between the underlying functors
that is compatible with the projections to `C`.

For slice morphisms `φ ψ : Over X`, a 2-cell `θ : φ ⟹ ψ` must satisfy
`θ_a ≫ ψ.hom = φ.hom` for each object `a`. When `X = Cat.of C` and the
morphisms are forgetful functors, this means `(forget G).map (θ.app x) = 𝟙`. -/
@[ext]
structure Slice2Hom (α β : Paranat F G) where
  /-- The underlying natural transformation -/
  nat : α.toFunctor ⟶ β.toFunctor
  /-- Compatibility with the forgetful functor: θ_x.base = 𝟙 -/
  slice_compat : ∀ x : DiagElem F, (nat.app x).base = 𝟙 x.base

variable {α β : Paranat F G}

/-- The component of a slice 2-morphism at a diagonal element. -/
abbrev Slice2Hom.component (θ : Slice2Hom C α β) (x : DiagElem F) :
    (Paranat.toFunctor C F G α).obj x ⟶ (Paranat.toFunctor C F G β).obj x :=
  θ.nat.app x

/-- The base of a slice 2-morphism component is the identity. -/
theorem Slice2Hom.component_base (θ : Slice2Hom C α β) (x : DiagElem F) :
    (θ.component C x).base = 𝟙 x.base :=
  θ.slice_compat x

/-- When the slice compatibility condition holds, the slice 2-morphism forces
the targets to have the same element component. This is because the morphism
has base component `𝟙` but connects `α.app x.base x.elem` to `β.app x.base x.elem`.
The only way a DiagElem morphism with base `𝟙` can exist is if the elements
are equal (due to the diagonal compatibility condition). -/
theorem Slice2Hom.elem_eq (θ : Slice2Hom C α β) (x : DiagElem F) :
    α.app x.base x.elem = β.app x.base x.elem := by
  have hbase := θ.component_base C x
  let mor := θ.component C x
  have hcompat := mor.compat
  simp only [DiagCompat, Paranat.toFunctor_obj_base, Paranat.toFunctor_obj_elem] at hcompat
  rw [hbase] at hcompat
  simp only [op_id, Functor.map_id, NatTrans.id_app, types_id_apply] at hcompat
  exact hcompat

/-- Any two paranatural transformations admitting a slice 2-morphism between
them must be equal. This shows that `EndoProf` is locally discrete when
viewed as a 2-category via the embedding into `Cat/C`. -/
theorem Slice2Hom.paranat_eq (θ : Slice2Hom C α β) : α = β := by
  apply Paranat.ext
  funext I d
  exact θ.elem_eq C ⟨I, d⟩

/-- If `α = β`, there is a canonical slice 2-morphism between them
(the identity). -/
def Slice2Hom.ofEq (h : α = β) : Slice2Hom C α β where
  nat := eqToHom (congrArg (Paranat.toFunctor C F G) h)
  slice_compat x := by
    subst h
    simp only [eqToHom_refl, NatTrans.id_app]
    rfl

/-- The type of slice 2-morphisms is equivalent to the equality type. -/
def slice2HomEquivEq (α β : Paranat F G) : Slice2Hom C α β ≃ (α = β) where
  toFun θ := θ.paranat_eq C
  invFun h := Slice2Hom.ofEq C h
  left_inv θ := by
    have h := θ.paranat_eq C
    subst h
    apply Slice2Hom.ext
    simp only [Slice2Hom.ofEq, eqToHom_refl]
    ext x
    have hbase := θ.component_base C x
    apply DiagElem.Hom.ext
    simp only [NatTrans.id_app]
    exact hbase.symm
  right_inv h := Subsingleton.elim _ _

/-- The hom-set `Paranat F G` has at most one slice 2-morphism between any
two elements (in fact, exactly one iff they are equal). This is the
"locally discrete" property. -/
instance slice2Hom_subsingleton (α β : Paranat F G) : Subsingleton (Slice2Hom C α β) where
  allEq θ₁ θ₂ := by
    have h := θ₁.paranat_eq C
    subst h
    apply Slice2Hom.ext
    ext x
    have hbase₁ := θ₁.component_base C x
    have hbase₂ := θ₂.component_base C x
    apply DiagElem.Hom.ext
    rw [hbase₁, hbase₂]

end Paranat2

section StructuralEndsCoends

/-!
## Structure and costructure integrals

Neumann defines "structure integrals" (structural ends) and "costructure
integrals" (structural coends) as universal constructions over the category
of diagonal elements (F-structures).

### General definitions

For two endoprofunctors `F, G : Cᵒᵖ ⥤ C ⥤ Type w`:

**Structure integral** `∫_{C:C} F(C,C) → G(C,C) pC`:
The type of families `φ : Π (x : F-Struct), G(x.base, x.base)` satisfying the
paranaturality condition: for any morphism `f : x → y` in F-Struct,
```
G(x.base, f) (φ x) = G(f, y.base) (φ y)
```
This is expressed as an equalizer.

**Costructure integral** `∫^{C:C} F(C,C) pG(C,C)`:
The quotient `(Σ (x : F-Struct), G(x.base, x.base)) / Sim_{F,G}` where
`Sim_{F,G}` identifies, for any morphism `f : x → y` in F-Struct and
`ψ : G(y.base, x.base)`:
```
(x, G(f, x.base) ψ) ~ (y, G(y.base, f) ψ)
```
This is expressed as a coequalizer.

### Profunctor actions

For a profunctor `G : Cᵒᵖ ⥤ C ⥤ Type w` and morphism `f : I → J`:
- Covariant action `G(K, f)` : `G(K, I) → G(K, J)` (second slot)
- Contravariant action `G(f, K)` : `G(J, K) → G(I, K)` (first slot)

### References

* Neumann, "Paranatural Category Theory", Definition 4.5, 4.7
* docs/structure-and-costructure-integrals.md
-/

universe w

variable {C : Type u} [Category.{v} C]
variable (F G : Cᵒᵖ ⥤ C ⥤ Type w)

/-! ### Profunctor applications and actions -/

/-- Off-diagonal application of a profunctor: `offDiagApp G J I` is `G(J, I)`.
This generalizes `diagApp` to non-equal arguments. -/
abbrev offDiagApp (J I : C) : Type w := (G.obj (Opposite.op J)).obj I

/-- Covariant action of a morphism on a profunctor in the second slot.
For `f : I → J`, this gives `G(K, f) : G(K, I) → G(K, J)`. -/
abbrev covAction (K : C) {I J : C} (f : I ⟶ J) : offDiagApp G K I → offDiagApp G K J :=
  (G.obj (Opposite.op K)).map f

/-- Contravariant action of a morphism on a profunctor in the first slot.
For `f : I → J`, this gives `G(f, K) : G(J, K) → G(I, K)`. -/
abbrev contravAction {I J : C} (f : I ⟶ J) (K : C) :
    offDiagApp G J K → offDiagApp G I K :=
  (G.map f.op).app K

@[simp]
theorem offDiagApp_diag (I : C) : offDiagApp G I I = diagApp G I := rfl

@[simp]
theorem covAction_id (K I : C) : covAction G K (𝟙 I) = id := by
  simp only [covAction, Functor.map_id]
  rfl

@[simp]
theorem contravAction_id (I K : C) : contravAction G (𝟙 I) K = id := by
  simp only [contravAction, op_id, Functor.map_id, NatTrans.id_app]
  rfl

/-! ### Structure integral (equalizer definition) -/

/-- Domain of the structure integral equalizer: families assigning to each
F-structure a G-diagonal element. -/
abbrev StructIntDom : Type _ := (x : DiagElem F) → diagApp G x.base

/-- Codomain of the structure integral equalizer: indexed by morphisms of
F-structures, with values in G's off-diagonal. -/
abbrev StructIntCod : Type _ :=
  (x y : DiagElem F) → (f : x ⟶ y) → offDiagApp G x.base y.base

/-- First equalizer map for structure integral: applies covariant action.
Given `φ : StructIntDom F G` and morphism `f : x → y` in F-Struct,
produces `G(x.base, f) (φ x) : G(x.base, y.base)`. -/
def structIntMapCov : StructIntDom F G → StructIntCod F G :=
  fun φ x _ f => covAction G x.base f.base (φ x)

/-- Second equalizer map for structure integral: applies contravariant action.
Given `φ : StructIntDom F G` and morphism `f : x → y` in F-Struct,
produces `G(f, y.base) (φ y) : G(x.base, y.base)`. -/
def structIntMapContrav : StructIntDom F G → StructIntCod F G :=
  fun φ _ y f => contravAction G f.base y.base (φ y)

/-- The structure integral of endoprofunctors `F` and `G`.
This is the equalizer of `structIntMapCov` and `structIntMapContrav`.

A family `φ : (x : F-Struct) → G(x.base, x.base)` is in the structure integral
iff for all morphisms `f : x → y` in F-Struct:
```
G(x.base, f) (φ x) = G(f, y.base) (φ y)
```
-/
@[ext]
structure StructureIntegral where
  /-- The family of G-diagonal elements indexed by F-structures -/
  family : StructIntDom F G
  /-- The equalizer condition: covariant and contravariant actions agree -/
  equalizer : structIntMapCov F G family = structIntMapContrav F G family

namespace StructureIntegral

variable {F G}

/-- The paranaturality condition in pointwise form. -/
theorem paranatural (φ : StructureIntegral F G)
    {x y : DiagElem F} (f : x ⟶ y) :
    covAction G x.base f.base (φ.family x) =
      contravAction G f.base y.base (φ.family y) :=
  congrFun (congrFun (congrFun φ.equalizer x) y) f

/-- Evaluate the structure integral at an F-structure. -/
abbrev eval (φ : StructureIntegral F G) (x : DiagElem F) : diagApp G x.base :=
  φ.family x

end StructureIntegral

/-! ### Equivalence between StructureIntegral and Paranat

The structure integral `StructureIntegral F G` is equivalent to the type of
paranatural transformations `Paranat F G`. The correspondence is:
- A family `(x : DiagElem F) → diagApp G x.base` corresponds to
  a function `(I : C) → diagApp F I → diagApp G I` by currying.
- The equalizer condition corresponds to the paranaturality condition.
-/

/-- Convert a `StructureIntegral` to a `Paranat` by uncurrying.
The family indexed by F-structures becomes a curried function. -/
def StructureIntegral.toParanat (φ : StructureIntegral F G) : Paranat F G where
  app I d := φ.family ⟨I, d⟩
  paranatural I₀ I₁ f d₀ d₁ hcompat := by
    simp only [DiagCompat] at hcompat ⊢
    let x : DiagElem F := ⟨I₀, d₀⟩
    let y : DiagElem F := ⟨I₁, d₁⟩
    let fHom : x ⟶ y := ⟨f, hcompat⟩
    have h := φ.paranatural fHom
    simp only [covAction, contravAction] at h
    exact h

/-- Convert a `Paranat` to a `StructureIntegral` by currying.
The curried function becomes a family indexed by F-structures. -/
def Paranat.toStructureIntegral (α : Paranat F G) : StructureIntegral F G where
  family x := α.app x.base x.elem
  equalizer := by
    funext x y f
    simp only [structIntMapCov, structIntMapContrav, covAction, contravAction]
    exact α.paranatural x.base y.base f.base x.elem y.elem f.compat

/-- The structure integral is equivalent to paranatural transformations. -/
def structureIntegralEquivParanat : StructureIntegral F G ≃ Paranat F G where
  toFun := StructureIntegral.toParanat F G
  invFun := Paranat.toStructureIntegral F G
  left_inv φ := by
    ext x
    simp only [Paranat.toStructureIntegral, StructureIntegral.toParanat]
  right_inv α := by
    ext
    simp only [StructureIntegral.toParanat, Paranat.toStructureIntegral]

/-! ### Costructure integral (coequalizer definition) -/

/-- Codomain of the costructure integral coequalizer: pairs of an F-structure
with a G-diagonal element. -/
abbrev CostructIntCod : Type _ := Σ (x : DiagElem F), diagApp G x.base

/-- Domain of the costructure integral coequalizer: tuples consisting of
two F-structures, a morphism between them, and a G-element at the off-diagonal.
This is `Σ (x y : F-Struct) (f : x → y), G(y.base, x.base)`. -/
abbrev CostructIntDom : Type _ :=
  Σ (x : DiagElem F) (y : DiagElem F) (_ : x ⟶ y), offDiagApp G y.base x.base

/-- First coequalizer map: applies contravariant action to land in source.
Sends `(x, y, f, ψ)` to `(x, G(f, x.base) ψ)` where `ψ : G(y.base, x.base)`. -/
def costructIntMapContrav : CostructIntDom F G → CostructIntCod F G :=
  fun ⟨x, _, f, ψ⟩ => ⟨x, contravAction G f.base x.base ψ⟩

/-- Second coequalizer map: applies covariant action to land in target.
Sends `(x, y, f, ψ)` to `(y, G(y.base, f) ψ)` where `ψ : G(y.base, x.base)`. -/
def costructIntMapCov : CostructIntDom F G → CostructIntCod F G :=
  fun ⟨_, y, f, ψ⟩ => ⟨y, covAction G y.base f.base ψ⟩

/-- The generating relation for the costructure integral coequalizer.
Two pairs are related if they are in the image of the same domain element
under the two coequalizer maps. -/
def CostructIntRel : CostructIntCod F G → CostructIntCod F G → Prop :=
  fun p q => ∃ d : CostructIntDom F G,
    costructIntMapContrav F G d = p ∧ costructIntMapCov F G d = q

/-- The setoid on the coequalizer codomain whose equivalence relation is
generated by `CostructIntRel`. -/
def costructIntSetoid : Setoid (CostructIntCod F G) :=
  Relation.EqvGen.setoid (CostructIntRel F G)

/-- The costructure integral of endoprofunctors `F` and `G`.
This is the coequalizer of `costructIntMapContrav` and `costructIntMapCov`.

In notation: `∫^{C:C} F(C,C) pG(C,C)`

Two pairs `(x, g)` and `(y, h)` are identified when there exists a morphism
`f : x → y` in F-Struct and `ψ : G(y.base, x.base)` such that:
```
g = G(f, x.base) ψ  and  h = G(y.base, f) ψ
```
-/
def CostructureIntegral := Quotient (costructIntSetoid F G)

namespace CostructureIntegral

variable {F G}

/-- The quotient map from the codomain to the costructure integral. -/
def mk (x : DiagElem F) (g : diagApp G x.base) : CostructureIntegral F G :=
  Quotient.mk (costructIntSetoid F G) ⟨x, g⟩

/-- The coequalizer condition: the two maps agree after quotienting.
For any `(x, y, f, ψ)` in the domain, we have:
`mk x (G(f, x.base) ψ) = mk y (G(y.base, f) ψ)` -/
theorem sound {x y : DiagElem F} (f : x ⟶ y) (ψ : offDiagApp G y.base x.base) :
    mk x (contravAction G f.base x.base ψ) =
      mk y (covAction G y.base f.base ψ) := by
  apply Quotient.sound
  apply Relation.EqvGen.rel
  exact ⟨⟨x, y, f, ψ⟩, rfl, rfl⟩

/-- Lift a function out of the costructure integral, given that it respects
the equivalence relation. -/
def lift {β : Sort*} (fn : (x : DiagElem F) → diagApp G x.base → β)
    (h : ∀ {x y : DiagElem F} (f : x ⟶ y) (ψ : offDiagApp G y.base x.base),
      fn x (contravAction G f.base x.base ψ) =
        fn y (covAction G y.base f.base ψ)) :
    CostructureIntegral F G → β :=
  Quotient.lift (fun p => fn p.1 p.2) (by
    intro a b hrel
    induction hrel with
    | rel p q hpq =>
      obtain ⟨⟨x, y, f, ψ⟩, hp, hq⟩ := hpq
      simp only [costructIntMapContrav, costructIntMapCov] at hp hq
      subst hp hq
      exact h f ψ
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2)

@[simp]
theorem lift_mk {β : Sort*} (fn : (x : DiagElem F) → diagApp G x.base → β)
    (h : ∀ {x y : DiagElem F} (f : x ⟶ y) (ψ : offDiagApp G y.base x.base),
      fn x (contravAction G f.base x.base ψ) =
        fn y (covAction G y.base f.base ψ))
    (x : DiagElem F) (g : diagApp G x.base) :
    lift fn h (mk x g) = fn x g := rfl

end CostructureIntegral

/-! ### Single-profunctor case (F = G)

When `F = G`, the structure and costructure integrals specialize to simpler
forms involving the diagonal elements and base objects directly. -/

/-- The domain of the structure integral when F = G is families of diagonal
elements of F. -/
abbrev StructIntDomSelf : Type _ := (x : DiagElem F) → diagApp F x.base

/-- The structure integral of a single profunctor with itself.
This is the type of strong dinatural transformations F → F. -/
abbrev StructureIntegralSelf := StructureIntegral F F

/-- The costructure integral of a single profunctor with itself. -/
abbrev CostructureIntegralSelf := CostructureIntegral F F

/-! ### The identity profunctor and structural ends/coends

The identity profunctor for `Type v` sends `(x, y)` to `y`. This gives the
single-profunctor structure/costructure integrals when used as the second
argument: `StructuralEnd F = StructureIntegral F IdProf` and
`StructuralCoend F = CostructureIntegral F IdProf`.
-/

/-- The identity profunctor on `Type v`, sending `(x, y)` to `y`.
This is constant in the first argument and the identity in the second.
A diagonal element at `A` is just a point of `A`, making `DiagElem IdProf`
equivalent to the category of pointed types. -/
abbrev IdProf : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v :=
  (Functor.const (Type v)ᵒᵖ).obj (𝟭 (Type v))

/-- The structural end (single-profunctor structure integral).
This is `∫_C F(C,C) pC`, the equalizer of families indexed by F-structures
taking values in their carriers.

For `F = AlgProf G`, this gives paranatural transformations from algebras
to their carriers, equivalent to the initial algebra `μG.a`. -/
abbrev StructuralEnd (F : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v) : Type _ :=
  StructureIntegral F IdProf

/-- The structural coend (single-profunctor costructure integral).
This is `∫^C F(C,C) pC`, the coequalizer of F-structures paired with
carrier elements.

For `F = CoalgProf G`, this gives pointed coalgebras quotiented by
coalgebra morphisms, equivalent to the terminal coalgebra `νG.V`. -/
abbrev StructuralCoend (F : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v) : Type _ :=
  CostructureIntegral F IdProf

/-- For the structural coend, the off-diagonal is just the source carrier. -/
theorem structuralCoend_offDiag (F : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v)
    (x y : DiagElem F) : offDiagApp IdProf y.base x.base = x.base := rfl

/-- For the structural coend, the contravariant action is identity
(IdProf is constant in the first argument). -/
theorem structuralCoend_contravAction (F : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v)
    {x y : DiagElem F} (f : x ⟶ y) (a : x.base) :
    contravAction IdProf f.base x.base a = a := rfl

/-- For the structural coend, the covariant action applies the morphism. -/
theorem structuralCoend_covAction (F : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v)
    {x y : DiagElem F} (f : x ⟶ y) (a : x.base) :
    covAction IdProf y.base f.base a = f.base a := rfl

/-- The structural coend sim relation: `(x, a) ~ (y, f a)` for morphism `f`. -/
theorem structuralCoend_sound (F : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v)
    {x y : DiagElem F} (f : x ⟶ y) (a : x.base) :
    CostructureIntegral.mk (G := IdProf) x a =
      CostructureIntegral.mk y (f.base a) := by
  have h := CostructureIntegral.sound (G := IdProf) f a
  simp only [structuralCoend_contravAction, structuralCoend_covAction] at h
  exact h

end StructuralEndsCoends

section ProfunctorConversions

/-!
## Converting presheaves and copresheaves to profunctors

A copresheaf `P : C ⥤ Type w` can be viewed as a profunctor that is constant
in the contravariant argument: `copresheafToProf P` sends `(x, y)` to `P(y)`.

A presheaf `P : Cᵒᵖ ⥤ Type w` can be viewed as a profunctor that is constant
in the covariant argument: `presheafToProf P` sends `(x, y)` to `P(x)`.

These conversions provide a uniform way to treat presheaves and copresheaves
as profunctors, and they preserve the category of diagonal elements up to
equivalence with the (contravariant) category of elements.
-/

variable {C : Type u} [Category.{v} C]

universe w

/-- Convert a copresheaf to a profunctor by making it constant in the
contravariant argument. For `P : C ⥤ Type w`, the profunctor
`copresheafToProf P` sends `(x, y)` to `P(y)`. -/
abbrev copresheafToProf (P : C ⥤ Type w) : Cᵒᵖ ⥤ C ⥤ Type w :=
  (Functor.const Cᵒᵖ).obj P

/-- Convert a presheaf to a profunctor by making it constant in the
covariant argument. For `P : Cᵒᵖ ⥤ Type w`, the profunctor
`presheafToProf P` sends `(x, y)` to `P(x)`. -/
abbrev presheafToProf (P : Cᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ C ⥤ Type w :=
  P ⋙ Functor.const C

@[simp]
theorem copresheafToProf_obj_obj (P : C ⥤ Type w) (x : Cᵒᵖ) (y : C) :
    ((copresheafToProf P).obj x).obj y = P.obj y := rfl

@[simp]
theorem copresheafToProf_obj_map (P : C ⥤ Type w) (x : Cᵒᵖ) {y₀ y₁ : C}
    (f : y₀ ⟶ y₁) :
    ((copresheafToProf P).obj x).map f = P.map f := rfl

@[simp]
theorem copresheafToProf_map_app (P : C ⥤ Type w) {x₀ x₁ : Cᵒᵖ}
    (f : x₀ ⟶ x₁) (y : C) :
    ((copresheafToProf P).map f).app y = id := rfl

@[simp]
theorem presheafToProf_obj_obj (P : Cᵒᵖ ⥤ Type w) (x : Cᵒᵖ) (y : C) :
    ((presheafToProf P).obj x).obj y = P.obj x := rfl

@[simp]
theorem presheafToProf_obj_map (P : Cᵒᵖ ⥤ Type w) (x : Cᵒᵖ) {y₀ y₁ : C}
    (f : y₀ ⟶ y₁) :
    ((presheafToProf P).obj x).map f = id := rfl

@[simp]
theorem presheafToProf_map_app (P : Cᵒᵖ ⥤ Type w) {x₀ x₁ : Cᵒᵖ}
    (f : x₀ ⟶ x₁) (y : C) :
    ((presheafToProf P).map f).app y = P.map f := rfl

/-- The diagonal of `copresheafToProf P` at `I` is `P(I)`. -/
theorem copresheafToProf_diag (P : C ⥤ Type w) (I : C) :
    diagApp (copresheafToProf P) I = P.obj I := rfl

/-- The diagonal of `presheafToProf P` at `I` is `P(op I)`. -/
theorem presheafToProf_diag (P : Cᵒᵖ ⥤ Type w) (I : C) :
    diagApp (presheafToProf P) I = P.obj (Opposite.op I) := rfl

/-- The identity profunctor can be expressed as a copresheaf-to-profunctor
conversion of the identity functor on `Type v`. -/
theorem IdProf_eq_copresheafToProf :
    IdProf = copresheafToProf (𝟭 (Type v)) := rfl

end ProfunctorConversions

section DiagElemElementsEquiv

/-!
## Equivalence between diagonal elements and categories of elements

When we view a copresheaf `P : C ⥤ Type w` as a profunctor via
`copresheafToProf`, the category of diagonal elements `DiagElem` is
isomorphic to the (covariant) category of elements `P.Elements`.

When we view a presheaf `Q : Cᵒᵖ ⥤ Type w` as a profunctor via
`presheafToProf`, the category of diagonal elements is isomorphic to
the opposite of the category of elements `Q.Elementsᵒᵖ`.
-/

variable {C : Type u} [Category.{v} C]

universe w

/-! ### Copresheaf case: DiagElem ≃ Elements -/

variable (P : C ⥤ Type w)

/-- Functor from `DiagElem (copresheafToProf P)` to `P.Elements`.
Objects `(I, elem)` map to `⟨I, elem⟩`. -/
@[simps]
def diagElemToElements : DiagElem (copresheafToProf P) ⥤ P.Elements where
  obj x := ⟨x.base, x.elem⟩
  map {x y} f := ⟨f.base, by
    have h := f.compat
    simp only [DiagCompat] at h
    exact h⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Functor from `P.Elements` to `DiagElem (copresheafToProf P)`.
Objects `⟨I, elem⟩` map to `(I, elem)`. -/
@[simps]
def elementsToDiagElem : P.Elements ⥤ DiagElem (copresheafToProf P) where
  obj p := ⟨p.fst, p.snd⟩
  map {p q} f := ⟨f.val, by
    simp only [DiagCompat]
    exact f.property⟩
  map_id _ := DiagElem.Hom.ext rfl
  map_comp _ _ := DiagElem.Hom.ext rfl

/-- The category of diagonal elements of `copresheafToProf P` is isomorphic
to the (covariant) category of elements `P.Elements`. -/
def diagElemCopresheafIso : DiagElem (copresheafToProf P) ≅Cat P.Elements where
  hom := diagElemToElements P
  inv := elementsToDiagElem P
  hom_inv_id := by
    apply Functor.ext
    case h_obj => intro x; apply DiagElem.ext <;> rfl
    case h_map => intro x y f; apply DiagElem.Hom.ext; simp
  inv_hom_id := by
    apply Functor.ext
    case h_obj => intro p; rfl
    case h_map =>
      intro p q f
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      apply Subtype.ext
      rfl

/-- The categorical equivalence between diagonal elements and Elements. -/
def diagElemCopresheafEquiv : DiagElem (copresheafToProf P) ≌ P.Elements :=
  Cat.equivOfIso (diagElemCopresheafIso P)

/-! ### Presheaf case: DiagElem ≃ ElementsPre

For a presheaf `Q : Cᵒᵖ ⥤ Type w`, the diagonal elements of `presheafToProf Q`
are isomorphic to `Q.ElementsPre`, the standard (contravariant) category of
elements for presheaves.

`Q.ElementsPre` is defined as `Q.Elementsᵒᵖ` where `Q.Elements` treats `Q` as a
copresheaf on `Cᵒᵖ`. This is the conventional definition where:
- Objects: pairs `(X, x)` with `X : C` and `x : Q.obj (op X)`
- Morphisms `(X, x) → (Y, y)`: maps `f : X ⟶ Y` in `C` with `Q.map f.op y = x`

The morphism direction in `DiagElem` matches `ElementsPre`:
- In `DiagElem`, morphisms `f : I₀ ⟶ I₁` go from `(I₀, elem₀)` to `(I₁, elem₁)`
  with condition `elem₀ = Q.map (op f) elem₁`
- In `Q.ElementsPre`, morphisms go in the same direction with the same condition
-/

variable {P}
variable (Q : Cᵒᵖ ⥤ Type w)

/-- Functor from `DiagElem (presheafToProf Q)` to `Q.ElementsPre`.
Objects `(I, elem : Q(op I))` map to `op ⟨op I, elem⟩`.
A morphism `f : I₀ ⟶ I₁` with `elem₀ = Q.map (op f) elem₁` corresponds to
`op ⟨op f, ...⟩ : (op I₁, elem₁) ⟶ (op I₀, elem₀)` in `Q.ElementsPre`. -/
@[simps!]
def diagElemToElementsPre :
    DiagElem (presheafToProf Q) ⥤ Q.ElementsPre where
  obj x := Opposite.op ⟨Opposite.op x.base, x.elem⟩
  map {x y} f := Opposite.op ⟨f.base.op, by
    have h := f.compat
    simp only [DiagCompat] at h
    exact h.symm⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Functor from `Q.ElementsPre` to `DiagElem (presheafToProf Q)`.
Objects `op ⟨op I, elem⟩` map to `(I, elem)`. -/
@[simps!]
def elementsPreToDiagElem :
    Q.ElementsPre ⥤ DiagElem (presheafToProf Q) where
  obj p := ⟨p.unop.fst.unop, p.unop.snd⟩
  map {p q} f := ⟨f.unop.val.unop, by
    simp only [DiagCompat]
    have h := f.unop.property
    exact h.symm⟩
  map_id _ := DiagElem.Hom.ext rfl
  map_comp _ _ := DiagElem.Hom.ext rfl

/-- The category of diagonal elements of `presheafToProf Q` is isomorphic
to `Q.ElementsPre`, the standard category of elements for presheaves. -/
def diagElemPresheafIso : DiagElem (presheafToProf Q) ≅Cat Q.ElementsPre where
  hom := diagElemToElementsPre Q
  inv := elementsPreToDiagElem Q
  hom_inv_id := by
    apply Functor.ext
    case h_obj => intro x; apply DiagElem.ext <;> rfl
    case h_map => intro x y f; apply DiagElem.Hom.ext; simp
  inv_hom_id := by
    apply Functor.ext
    case h_obj => intro p; rfl
    case h_map =>
      intro p q f
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      exact Opposite.op_unop f

/-- The categorical equivalence between diagonal elements and Q.ElementsPre. -/
def diagElemPresheafEquiv : DiagElem (presheafToProf Q) ≌ Q.ElementsPre :=
  Cat.equivOfIso (diagElemPresheafIso Q)

end DiagElemElementsEquiv

section TwCoprToArr

universe w

variable (F : TwistedArrow' C ⥤ Type w)

/-- Interpret an Arrow object as a TwistedArrow' object.
An arrow `f : X ⟶ Y` becomes the twisted arrow with domain `X`, codomain `Y`,
and arrow `f`. -/
def arrToTw' (arr : Arrow C) : TwistedArrow' C :=
  twObjMk' arr.hom

/-- Given an Arrow morphism `φ : arr₁ ⟶ arr₂`, the "diagonal" arrow is
`arr₁.hom ≫ φ.right = φ.left ≫ arr₂.hom`, which goes from `arr₁.left` to
`arr₂.right`. -/
def arrDiag {arr₁ arr₂ : Arrow C} (φ : arr₁ ⟶ arr₂) :
    arr₁.left ⟶ arr₂.right :=
  arr₁.hom ≫ φ.right

/-- The diagonal as a TwistedArrow' object. -/
def arrDiagTw' {arr₁ arr₂ : Arrow C} (φ : arr₁ ⟶ arr₂) : TwistedArrow' C :=
  twObjMk' (arrDiag φ)

/-- From the source twisted arrow `tw(arr₁.hom)` to the diagonal `tw(diag φ)`.
This uses `𝟙` on domains and `φ.right` on codomains. -/
def arrToDiagFromSource {arr₁ arr₂ : Arrow C} (φ : arr₁ ⟶ arr₂) :
    arrToTw' arr₁ ⟶ arrDiagTw' φ :=
  twHomMk'
    (𝟙 arr₁.left)
    φ.right
    (by simp only [arrToTw', arrDiagTw', arrDiag, twObjMk'_arr]
        exact Category.id_comp _)

/-- From the target twisted arrow `tw(arr₂.hom)` to the diagonal `tw(diag φ)`.
This uses `φ.left` on domains and `𝟙` on codomains. -/
def arrToDiagFromTarget {arr₁ arr₂ : Arrow C} (φ : arr₁ ⟶ arr₂) :
    arrToTw' arr₂ ⟶ arrDiagTw' φ :=
  twHomMk'
    φ.left
    (𝟙 arr₂.right)
    (by simp only [arrToTw', arrDiagTw', arrDiag, twObjMk'_arr]
        calc φ.left ≫ arr₂.hom ≫ 𝟙 arr₂.right
            = φ.left ≫ arr₂.hom := congrArg (φ.left ≫ ·) (Category.comp_id _)
          _ = arr₁.hom ≫ φ.right := φ.w)

/-- The diagonal compatibility condition for twisted arrow copresheaves over
arrows. Given an Arrow morphism `φ : arr₁ ⟶ arr₂` and elements
`e₁ ∈ F(tw(arr₁.hom))` and `e₂ ∈ F(tw(arr₂.hom))`, this asserts that
transporting `e₁` forward via `(𝟙, φ.right)` equals transporting `e₂`
forward via `(φ.left, 𝟙)` in `F(tw(diag φ))`. -/
def TwArrCompat {arr₁ arr₂ : Arrow C} (φ : arr₁ ⟶ arr₂)
    (e₁ : F.obj (arrToTw' arr₁)) (e₂ : F.obj (arrToTw' arr₂)) : Prop :=
  F.map (arrToDiagFromSource φ) e₁ = F.map (arrToDiagFromTarget φ) e₂

/-- An element of the twisted arrow copresheaf over an arrow: an arrow paired
with an element of the copresheaf at that arrow (interpreted as a twisted
arrow). -/
@[ext]
structure TwCoprArrElem where
  /-- The underlying arrow in `C` -/
  arr : Arrow C
  /-- The element of the copresheaf at this arrow -/
  elem : F.obj (arrToTw' arr)

/-- A morphism in `TwCoprArrElem F` from `(arr₁, e₁)` to `(arr₂, e₂)` consists
of an Arrow morphism `φ : arr₁ ⟶ arr₂` such that the diagonal compatibility
condition holds. -/
@[ext]
structure TwCoprArrElem.Hom (x y : TwCoprArrElem F) where
  /-- The underlying Arrow morphism -/
  base : x.arr ⟶ y.arr
  /-- The compatibility condition -/
  compat : TwArrCompat F base x.elem y.elem

namespace TwCoprArrElem

/-- Given composable Arrow morphisms `f : arr₁ → arr₂` and `g : arr₂ → arr₃`,
there is a twisted arrow morphism from `diag(f)` to `diag(f ≫ g)` via
`(𝟙, g.right)`. -/
def diagToCompDiagViaCod {arr₁ arr₂ arr₃ : Arrow C} (f : arr₁ ⟶ arr₂)
    (g : arr₂ ⟶ arr₃) : arrDiagTw' f ⟶ arrDiagTw' (f ≫ g) :=
  twHomMk'
    (𝟙 arr₁.left)
    g.right
    (by simp only [arrDiagTw', arrDiag, twObjMk'_arr, Arrow.comp_right]
        calc 𝟙 arr₁.left ≫ (arr₁.hom ≫ f.right) ≫ g.right
            = (arr₁.hom ≫ f.right) ≫ g.right := Category.id_comp _
          _ = arr₁.hom ≫ f.right ≫ g.right := by rw [Category.assoc])

/-- Given composable Arrow morphisms `f : arr₁ → arr₂` and `g : arr₂ → arr₃`,
there is a twisted arrow morphism from `diag(g)` to `diag(f ≫ g)` via
`(f.left, 𝟙)`. -/
def diagToCompDiagViaDom {arr₁ arr₂ arr₃ : Arrow C} (f : arr₁ ⟶ arr₂)
    (g : arr₂ ⟶ arr₃) : arrDiagTw' g ⟶ arrDiagTw' (f ≫ g) :=
  twHomMk'
    f.left
    (𝟙 arr₃.right)
    (by simp only [arrDiagTw', arrDiag, twObjMk'_arr, Arrow.comp_right]
        calc f.left ≫ (arr₂.hom ≫ g.right) ≫ 𝟙 arr₃.right
            = f.left ≫ (arr₂.hom ≫ g.right) :=
                congrArg (f.left ≫ ·) (Category.comp_id _)
          _ = (f.left ≫ arr₂.hom) ≫ g.right := by rw [← Category.assoc]
          _ = (arr₁.hom ≫ f.right) ≫ g.right :=
                congrArg (· ≫ g.right) (f.w)
          _ = arr₁.hom ≫ f.right ≫ g.right := by rw [Category.assoc])

def Hom.id (x : TwCoprArrElem F) : Hom F x x where
  base := 𝟙 x.arr
  compat := by
    simp only [TwArrCompat]
    have h : arrToDiagFromSource (𝟙 x.arr) = arrToDiagFromTarget (𝟙 x.arr) := by
      apply Subtype.ext
      simp only [Arrow.id_left, Arrow.id_right, arrToDiagFromSource, arrToDiagFromTarget,
        twHomMk', CategoryOfElements.homMk]
    rw [h]

def Hom.comp {x y z : TwCoprArrElem F} (f : Hom F x y) (g : Hom F y z) :
    Hom F x z where
  base := f.base ≫ g.base
  compat := by
    simp only [TwArrCompat]
    have step1 : arrToDiagFromSource (f.base ≫ g.base) =
        arrToDiagFromSource f.base ≫ diagToCompDiagViaCod f.base g.base := by
      apply Subtype.ext
      simp only [arrToDiagFromSource, diagToCompDiagViaCod, twHomMk',
        CategoryOfElements.homMk, Arrow.comp_right]
      rw [CategoryOfElements.comp_val]
      ext
      · simp only [CategoryTheory.prod_comp_fst]
        symm
        exact Category.id_comp _
      · simp only [CategoryTheory.prod_comp_snd]
    have step2 : arrToDiagFromTarget (f.base ≫ g.base) =
        arrToDiagFromTarget g.base ≫ diagToCompDiagViaDom f.base g.base := by
      apply Subtype.ext
      simp only [arrToDiagFromTarget, diagToCompDiagViaDom, twHomMk',
        CategoryOfElements.homMk, Arrow.comp_left]
      rw [CategoryOfElements.comp_val]
      ext
      · simp only [CategoryTheory.prod_comp_fst]
        -- In Cᵒᵖ', composition is reversed: g ≫ f in Cᵒᵖ' = f ≫ g in C
        change f.base.left ≫ g.base.left = f.base.left ≫ g.base.left
        rfl
      · simp only [CategoryTheory.prod_comp_snd]
        symm
        exact Category.comp_id _
    have step3 : arrToDiagFromTarget f.base ≫ diagToCompDiagViaCod f.base g.base =
        arrToDiagFromSource g.base ≫ diagToCompDiagViaDom f.base g.base := by
      apply Subtype.ext
      simp only [arrToDiagFromTarget, arrToDiagFromSource, diagToCompDiagViaCod,
        diagToCompDiagViaDom, twHomMk', CategoryOfElements.homMk]
      rw [CategoryOfElements.comp_val, CategoryOfElements.comp_val]
      ext
      · simp only [CategoryTheory.prod_comp_fst]
        -- In Cᵒᵖ', comp is reversed: f ≫ g = g ≫ f in C
        -- So f.base.left ≫ 𝟙 x.arr.left (in Cᵒᵖ') = 𝟙 x.arr.left ≫ f.base.left (in C)
        -- and 𝟙 y.arr.left ≫ f.base.left (in Cᵒᵖ') = f.base.left ≫ 𝟙 y.arr.left (in C)
        change 𝟙 x.arr.left ≫ f.base.left = f.base.left ≫ 𝟙 y.arr.left
        simp only [Category.id_comp, Category.comp_id]
      · simp only [CategoryTheory.prod_comp_snd]
        change 𝟙 y.arr.right ≫ g.base.right = g.base.right ≫ 𝟙 z.arr.right
        simp only [Category.id_comp, Category.comp_id]
    calc F.map (arrToDiagFromSource (f.base ≫ g.base)) x.elem
        = F.map (arrToDiagFromSource f.base ≫ diagToCompDiagViaCod f.base g.base)
            x.elem := by rw [step1]
      _ = F.map (diagToCompDiagViaCod f.base g.base)
            (F.map (arrToDiagFromSource f.base) x.elem) := by
          rw [F.map_comp]; rfl
      _ = F.map (diagToCompDiagViaCod f.base g.base)
            (F.map (arrToDiagFromTarget f.base) y.elem) := by
          rw [f.compat]
      _ = F.map (arrToDiagFromTarget f.base ≫ diagToCompDiagViaCod f.base g.base)
            y.elem := by
          rw [F.map_comp]; rfl
      _ = F.map (arrToDiagFromSource g.base ≫ diagToCompDiagViaDom f.base g.base)
            y.elem := by rw [step3]
      _ = F.map (diagToCompDiagViaDom f.base g.base)
            (F.map (arrToDiagFromSource g.base) y.elem) := by
          rw [F.map_comp]; rfl
      _ = F.map (diagToCompDiagViaDom f.base g.base)
            (F.map (arrToDiagFromTarget g.base) z.elem) := by
          rw [g.compat]
      _ = F.map (arrToDiagFromTarget g.base ≫ diagToCompDiagViaDom f.base g.base)
            z.elem := by
          rw [F.map_comp]; rfl
      _ = F.map (arrToDiagFromTarget (f.base ≫ g.base)) z.elem := by
          rw [step2]

instance : CategoryStruct (TwCoprArrElem F) where
  Hom := Hom F
  id := @Hom.id _ _ F
  comp := @Hom.comp _ _ F

instance : Category (TwCoprArrElem F) where
  id_comp f := by
    apply Hom.ext
    dsimp only [CategoryStruct.id, CategoryStruct.comp, Hom.id, Hom.comp]
    exact Category.id_comp f.base
  comp_id f := by
    apply Hom.ext
    dsimp only [CategoryStruct.id, CategoryStruct.comp, Hom.id, Hom.comp]
    exact Category.comp_id f.base
  assoc f g h := by
    apply Hom.ext
    dsimp only [CategoryStruct.comp, Hom.comp]
    exact Category.assoc f.base g.base h.base

end TwCoprArrElem

section TwCoprArrElemIsoConnGrothendieck

/-! ## Isomorphism with connected Grothendieck construction

We prove that `TwCoprArrElem F` is isomorphic to the connected Grothendieck
construction applied to `F` composed with the discrete category functor.

Given `F : TwistedArrow' C ⥤ Type w`, composing with `typeToCat` gives
`F ⋙ typeToCat : TwistedArrow' C ⥤ Cat` where each fiber `F.obj tw` becomes
the discrete category `Discrete (F.obj tw)`.

In discrete categories, morphisms exist only between equal elements (as
identities). This means the fiber morphism condition in `ConnGrothendieckHom`
reduces to an equality, matching `TwArrCompat`.
-/

/-- Convert a twisted arrow back to an Arrow. -/
def twToArr' (tw : TwistedArrow' C) : Arrow C :=
  Arrow.mk (twArr' tw)

lemma twToArr'_arrToTw' (φ : Arrow C) : twToArr' (arrToTw' φ) = φ := by
  simp only [twToArr', arrToTw', twArr']
  rfl

lemma arrToTw'_twToArr' (tw : TwistedArrow' C) : arrToTw' (twToArr' tw) = tw := by
  simp only [arrToTw', twToArr', twArr', twDom', twCod']
  rfl

lemma twToArr'_left (tw : TwistedArrow' C) :
    (twToArr' tw).left = twDom' tw := rfl

lemma twToArr'_right (tw : TwistedArrow' C) :
    (twToArr' tw).right = twCod' tw := rfl

lemma twToArr'_hom (tw : TwistedArrow' C) :
    (twToArr' tw).hom = twArr' tw := rfl

/-! ### Correspondence with connected Grothendieck for discrete fibers

We now show that `TwCoprArrElem F` is the "discrete fiber" case of the
connected Grothendieck construction. Specifically:

- Objects `(arr, elem)` in `TwCoprArrElem F` correspond to objects
  `(arrToTw' arr, elem)` in `ConnGrothendieck (F composed with discrete)`

- Morphisms in `TwCoprArrElem F` (Arrow morphisms with `TwArrCompat`) correspond
  to morphisms in `ConnGrothendieck` where the fiber morphism is an identity
  (the only kind of morphism in discrete categories)

We establish this correspondence via explicit bijections on objects and
morphisms.
-/

/-- Object bijection: `TwCoprArrElem F` objects correspond bijectively to
pairs `(tw, elem)` where `tw : TwistedArrow' C` and `elem : F.obj tw`. -/
def TwCoprArrElem.equivTwElem :
    TwCoprArrElem F ≃ Σ tw : TwistedArrow' C, F.obj tw where
  toFun x := ⟨arrToTw' x.arr, x.elem⟩
  invFun p := ⟨twToArr' p.1, (arrToTw'_twToArr' p.1).symm ▸ p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- An Arrow morphism `φ : arr₁ ⟶ arr₂` satisfies the square commutativity
`φ.left ≫ arr₂.hom = arr₁.hom ≫ φ.right`. -/
lemma Arrow.hom_w {arr₁ arr₂ : Arrow C} (φ : arr₁ ⟶ arr₂) :
    φ.left ≫ arr₂.hom = arr₁.hom ≫ φ.right :=
  φ.w

/-- The TwArrCompat condition for `TwCoprArrElem` morphisms corresponds to
the fiber equality needed for discrete Grothendieck morphisms. -/
lemma TwArrCompat_as_fiberEq {x y : TwCoprArrElem F} (φ : x.arr ⟶ y.arr)
    (h : TwArrCompat F φ x.elem y.elem) :
    F.map (arrToDiagFromSource φ) x.elem =
    F.map (arrToDiagFromTarget φ) y.elem :=
  h

/-! ### Correspondence with ConnGrothendieck constructions

The diagonal constructions in `ConnGrothendieck` (using `connGrothendieckDiagCod`
and the twisted arrow morphisms `connGrothendieckTwMorphCod/Dom`) correspond
exactly to our `arrDiagTw'` and `arrToDiagFromSource/Target` constructions.
-/

/-- The diagonal from `ConnGrothendieck` matches `arrDiagTw'`. Given an
Arrow morphism `φ : arr₁ ⟶ arr₂`, both compute `tw(arr₁.hom ≫ φ.right)`. -/
lemma connGrothendieckDiagCod_eq_arrDiagTw' {arr₁ arr₂ : Arrow C}
    (φ : arr₁ ⟶ arr₂) :
    connGrothendieckDiagCod C (arrToTw' arr₁) φ.right = arrDiagTw' φ := by
  simp only [connGrothendieckDiagCod, arrDiagTw', arrDiag, arrToTw', twObjMk'_arr]

/-- The domain-based diagonal matches `arrDiagTw'` via the arrow square
commutativity. -/
lemma connGrothendieckDiagDom_eq_arrDiagTw' {arr₁ arr₂ : Arrow C}
    (φ : arr₁ ⟶ arr₂) :
    connGrothendieckDiagDom C (arrToTw' arr₂) φ.left = arrDiagTw' φ := by
  simp only [connGrothendieckDiagDom, arrDiagTw', arrDiag, arrToTw',
    twObjMk'_arr, Arrow.hom_w]

/-- The two diagonal representations are equal. -/
lemma connGrothendieckDiags_eq {arr₁ arr₂ : Arrow C} (φ : arr₁ ⟶ arr₂) :
    connGrothendieckDiagCod C (arrToTw' arr₁) φ.right =
    connGrothendieckDiagDom C (arrToTw' arr₂) φ.left := by
  rw [connGrothendieckDiagCod_eq_arrDiagTw', connGrothendieckDiagDom_eq_arrDiagTw']

/-! ### The morphism correspondence

For a functor `F : TwistedArrow' C ⥤ Type w`, morphisms in `TwCoprArrElem F`
consist of an Arrow morphism `φ` together with the `TwArrCompat` condition.

In `ConnGrothendieck (F ⋙ discrete)` (where fibers are discrete categories),
morphisms would consist of `(domArr, codArr, square_comm, fiberMorph)`.
In a discrete category, morphisms only exist between equal elements,
so `fiberMorph` existing implies the transported fibers are equal.

Specifically, the `fiberMorph` in `ConnGrothendieck` goes from
`F.map (twMorphCod) x.fiber` to `F.map (twMorphDom) y.fiber`
in the fiber at the diagonal. For discrete fibers, this morphism
exists iff these elements are equal, which is exactly `TwArrCompat`.

The correspondence:
- `connGrothendieckTwMorphCod C (arrToTw' arr₁) φ.right` corresponds to
  `arrToDiagFromSource φ` (both are `twHomMk' (𝟙 _) φ.right ...`)
- `connGrothendieckTwMorphDom C (arrToTw' arr₂) φ.left` corresponds to
  `arrToDiagFromTarget φ` (both are `twHomMk' φ.left (𝟙 _) ...`)
-/

/-- The twisted arrow morphisms have the same components. -/
lemma twMorphCod_domArr_eq {arr₁ arr₂ : Arrow C} (φ : arr₁ ⟶ arr₂) :
    twDomArr' (connGrothendieckTwMorphCod C (arrToTw' arr₁) φ.right) =
    twDomArr' (arrToDiagFromSource φ) := by
  simp only [connGrothendieckTwMorphCod, arrToDiagFromSource, twHomMk'_domArr,
    connGrothendieckDiagCod, arrToTw', twObjMk'_dom, Functor.id_obj]

lemma twMorphCod_codArr_eq {arr₁ arr₂ : Arrow C} (φ : arr₁ ⟶ arr₂) :
    twCodArr' (connGrothendieckTwMorphCod C (arrToTw' arr₁) φ.right) =
    twCodArr' (arrToDiagFromSource φ) := by
  simp only [connGrothendieckTwMorphCod, arrToDiagFromSource, twHomMk'_codArr]

lemma twMorphDom_domArr_eq {arr₁ arr₂ : Arrow C} (φ : arr₁ ⟶ arr₂) :
    twDomArr' (connGrothendieckTwMorphDom C (arrToTw' arr₂) φ.left) =
    twDomArr' (arrToDiagFromTarget φ) := by
  simp only [connGrothendieckTwMorphDom, arrToDiagFromTarget, twHomMk'_domArr]

lemma twMorphDom_codArr_eq {arr₁ arr₂ : Arrow C} (φ : arr₁ ⟶ arr₂) :
    twCodArr' (connGrothendieckTwMorphDom C (arrToTw' arr₂) φ.left) =
    twCodArr' (arrToDiagFromTarget φ) := by
  simp only [connGrothendieckTwMorphDom, arrToDiagFromTarget, twHomMk'_codArr,
    arrToTw', twObjMk'_cod, Functor.id_obj]

/-! ### Summary of correspondence

The results above establish that `TwCoprArrElem F` is the discrete-fiber
specialization of `ConnGrothendieck`. Specifically:

**Objects:**
- `TwCoprArrElem F` object: `(arr : Arrow C, elem : F.obj (arrToTw' arr))`
- `ConnGrothendieck (F ⋙ discrete)` object: `(tw, fiber)` where `fiber ∈ Discrete (F.obj tw)`

Via `equivTwElem`, these correspond: `arr ↔ arrToTw' arr` and `elem ↔ fiber`.

**Morphisms:**
- In `TwCoprArrElem F`: Arrow morphism `φ` plus `TwArrCompat F φ x.elem y.elem`
- In `ConnGrothendieck (F ⋙ discrete)`: `(φ.left, φ.right, φ.w, fiberMorph)`

The `fiberMorph` is a morphism in the discrete category `Discrete (F.obj diag)`
from the transported source fiber to the transported target fiber.
In a discrete category, such a morphism exists iff the elements are equal.

By the lemmas above:
- `connGrothendieckDiagCod/Dom` match `arrDiagTw'`
- `connGrothendieckTwMorphCod/Dom` have the same dom/cod components as
  `arrToDiagFromSource/Target`

Therefore the transported fibers in `ConnGrothendieck` are:
- `F.map (connGrothendieckTwMorphCod ...) x.fiber` matches
  `F.map (arrToDiagFromSource φ) x.elem`
- `F.map (connGrothendieckTwMorphDom ...) y.fiber` matches
  `F.map (arrToDiagFromTarget φ) y.elem`

The `fiberMorph` condition (morphism exists in discrete category) is
equivalent to equality of these transported fibers, which is `TwArrCompat`.
-/

end TwCoprArrElemIsoConnGrothendieck

end TwCoprToArr

end GebLean
