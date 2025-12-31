import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Types.Basic
import Mathlib.CategoryTheory.Opposites

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
## Structural ends and coends (structure integrals)

Neumann defines "structural ends" and "structural coends" (also called
"structure integrals" and "costructure integrals") as universal constructions
over the category of diagonal elements (F-structures).

### Structural End (Definition 4.5, Neumann)

The **structural end** of a profunctor `F : Cᵒᵖ ⥤ C ⥤ Type w` is defined as
an equalizer. Concretely, it is the type of "global sections": assignments
that pick, for each F-structure `(I, d)`, a point `c : I` such that these
choices are compatible with all morphisms of F-structures.

That is, if `f : (I, d) → (J, e)` is a morphism in `DiagElem F`, then the
chosen point for `(I, d)` must map to the chosen point for `(J, e)` under `f`.

### Structural Coend

The **structural coend** of a profunctor `F : Cᵒᵖ ⥤ C ⥤ Type w` is defined as
a coequalizer (quotient). We take the sigma type `Σ (x : DiagElem F), x.base`
(pairing each F-structure with a point of its underlying object) and quotient
by the equivalence relation generated by:

  `(x, c) ~ (y, f.base c)` whenever `f : x ⟶ y` in `DiagElem F`

This identifies points that are related by morphisms of F-structures.

### Notation

Following Neumann, we write:
- `∫_{C:C} F(C,C) pC` for the structural end
- `∫^{C:C} F(C,C) pC` for the structural coend

The "pC" notation indicates that the diagonal is "parametric" in C.
-/

universe w

variable (F : (Type w)ᵒᵖ ⥤ Type w ⥤ Type w)

/-- A global section of an endoprofunctor `F` on `Type w` assigns to each
F-structure `(A, d)` a point `c : A`, such that these assignments are
compatible with morphisms of F-structures.

This is the type underlying the structural end. -/
structure GlobalSection where
  /-- For each diagonal element, a point in the base type -/
  section_ : (x : DiagElem F) → x.base
  /-- The section respects morphisms: if `f : x ⟶ y`, then `f(section x) =
  section y` -/
  compat : ∀ {x y : DiagElem F} (f : x ⟶ y), f.base (section_ x) = section_ y

/-- The structural end of an endoprofunctor `F` on `Type w`, consisting of
global sections over all F-structures.

In Neumann's notation: `∫_{C:C} F(C,C) pC`

This is defined as an equalizer in Definition 4.5 of Neumann's paper. The
equalizer diagram is:
```
∏_{(C,γ):F-Struct} C ⇉ ∏_{f:(C,γ)→(D,δ)} D
```
where the two maps send a family `(c_{(C,γ)})` to:
- First map: `(c_{(D,δ)})` (the target's section)
- Second map: `(f(c_{(C,γ)}))` (apply the morphism to the source's section)

A global section is an element of the equalizer: a family where these agree. -/
abbrev StructuralEnd := GlobalSection F

namespace GlobalSection

variable {F}

/-- Extensionality for global sections: two sections are equal if their
components agree at all diagonal elements. -/
@[ext]
theorem ext {s t : GlobalSection F} (h : ∀ x, s.section_ x = t.section_ x) :
    s = t := by
  cases s; cases t
  simp only [mk.injEq]
  funext x
  exact h x

/-- Evaluate a global section at a specific diagonal element. -/
abbrev eval (s : GlobalSection F) (x : DiagElem F) : x.base := s.section_ x

/-- Alternative constructor: a global section from a family with explicit
compatibility proof. -/
def mk' (sec : (x : DiagElem F) → x.base)
    (h : ∀ {x y : DiagElem F} (f : x ⟶ y), f.base (sec x) = sec y) :
    GlobalSection F :=
  ⟨sec, h⟩

end GlobalSection

/-- The equivalence relation on `Σ (x : DiagElem F), x.base` that identifies
points related by morphisms of F-structures.

Two pairs `(x, c)` and `(y, d)` are related if there exists a morphism
`f : x ⟶ y` such that `f.base c = d`. -/
def StructuralCoendRel : (Σ x : DiagElem F, x.base) →
    (Σ x : DiagElem F, x.base) → Prop :=
  fun ⟨x, c⟩ ⟨y, d⟩ => ∃ (f : x ⟶ y), f.base c = d

/-- The setoid on `Σ (x : DiagElem F), x.base` whose equivalence relation is
generated by `StructuralCoendRel`. This is the "Sim_F" relation from Neumann's
definition. -/
def structuralCoendSetoid : Setoid (Σ x : DiagElem F, x.base) :=
  Relation.EqvGen.setoid (StructuralCoendRel F)

/-- The structural coend of an endoprofunctor `F` on `Type w`, defined as the
quotient of the total space by the structural coend relation.

In Neumann's notation: `∫^{C:C} F(C,C) pC`

From Neumann's video definition:
```
∫^{C:C} F(C,C) pC := (Σ_{(C,γ):F-Struct} C) / Sim_F
```
where Sim_F is the least equivalence relation such that for all F-structures
`(C,γ)`, `(D,δ)`, morphisms `f : (C,γ) → (D,δ)`, and points `c₀ : C`:
```
Sim_F (C, γ, c₀) (D, δ, f c₀)
```
-/
def StructuralCoend := Quotient (structuralCoendSetoid F)

namespace StructuralCoend

variable {F}

/-- The quotient map from the total space to the structural coend. -/
def mk (x : DiagElem F) (c : x.base) : StructuralCoend F :=
  Quotient.mk (structuralCoendSetoid F) ⟨x, c⟩

/-- Points related by a morphism of F-structures are identified in the
structural coend. -/
theorem sound {x y : DiagElem F} (f : x ⟶ y) (c : x.base) :
    mk x c = mk y (f.base c) := by
  apply Quotient.sound
  apply Relation.EqvGen.rel
  exact ⟨f, rfl⟩

/-- Lift a function out of the structural coend, given that it respects the
equivalence relation. -/
def lift {β : Sort*} (fn : (x : DiagElem F) → x.base → β)
    (h : ∀ {x y : DiagElem F} (g : x ⟶ y) (c : x.base),
      fn x c = fn y (g.base c)) : StructuralCoend F → β :=
  Quotient.lift (fun p => fn p.1 p.2) (by
    intro a b hrel
    induction hrel with
    | rel p q hpq =>
      obtain ⟨x, c⟩ := p
      obtain ⟨y, d⟩ := q
      obtain ⟨f, hf⟩ := hpq
      simp only at hf ⊢
      subst hf
      exact h f c
    | refl => rfl
    | symm _ _ _ ih => exact ih.symm
    | trans _ _ _ _ _ ih1 ih2 => exact ih1.trans ih2)

/-- The computation rule for lift. -/
@[simp]
theorem lift_mk {β : Sort*} (fn : (x : DiagElem F) → x.base → β)
    (h : ∀ {x y : DiagElem F} (g : x ⟶ y) (c : x.base),
      fn x c = fn y (g.base c))
    (x : DiagElem F) (c : x.base) : lift fn h (mk x c) = fn x c := rfl

end StructuralCoend

end StructuralEndsCoends

end GebLean
