import GebLean.Utilities.Elements
import GebLean.Utilities.Skeleton
import GebLean.Utilities.Presheaf
import GebLean.Utilities.DoubleCategory
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Products.Basic
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

/-!
# Yoneda Relations and the Yoneda Relation Double Category

## Presheaf representation of relations

The presheaf `yoneda(X) × yoneda(Y)` represents "coherent
pairs of generalized elements": its category of elements
has objects `(T, a : T ⟶ X, b : T ⟶ Y)` (spans from `X`
to `Y`) and morphisms given by stage-change maps `s : T' ⟶ T`
compatible with both components.

A proof-relevant relation from `X` to `Y` is a presheaf on
this category of elements, or equivalently (by the standard
equivalence `PSh(∫F) ≃ PSh(C)/F`) a morphism into
`yoneda(X) × yoneda(Y)` in `PSh(C)`.

The construction `(X, Y) ↦ yoneda(X) × yoneda(Y)` is
bifunctorial in `X` and `Y`, arising as a composition of
existing higher-order functors: the Yoneda embedding
applied to each component, the functorial pairing into
a product functor category, and the pointwise application
of the binary product on types.

## Yoneda Relation Double Category

The `relRelated` predicate captures when two morphisms
`f : A ⟶ B` and `f' : A' ⟶ B'` in `C` are related by a
pair of Yoneda relations `(R, S)` via a commutative square:

```
  A ──f──▶ B
  │        │
  R        S
  ▼        ▼
  A'──f'─▶ B'
```

This has the shape of a 2-cell in a double category.

- Objects: objects of `C`
- Horizontal morphisms: morphisms in `C`
- Vertical morphisms: Yoneda relations (`YonedaRel`)
- Squares: `relRelated` (`Prop`-valued)

Since the square type is `Prop`, all square laws
(associativity, identity, interchange) hold by proof
irrelevance once the boundary types match.
-/

namespace GebLean

open CategoryTheory Limits

universe u v

variable {C : Type u} [Category.{v} C]

section PresheafRelations

open Limits.Types in
/-- The presheaf `T ↦ Hom(T, X) × Hom(T, Y)`, bifunctorial
in `X` and `Y`, constructed as a composition of the Yoneda
embedding, the functorial pairing
`prodFunctorToFunctorProd`, and the pointwise binary
product on types. -/
def yonedaProd : C ⥤ C ⥤ (Cᵒᵖ ⥤ Type v) :=
  Functor.curry.obj
    ((yoneda (C := C)).prod (yoneda (C := C)) ⋙
     prodFunctorToFunctorProd Cᵒᵖ (Type v) (Type v) ⋙
     (Functor.whiskeringRight Cᵒᵖ _ _).obj
       (Functor.uncurry.obj binaryProductFunctor))

abbrev yonedaProdPresheaf (X Y : C) :
    Cᵒᵖ ⥤ Type v :=
  (yonedaProd.obj X).obj Y

/-- A proof-relevant relation from `X` to `Y` in
`PSh(C)`: an object of the slice category over the
product presheaf `yoneda(X) × yoneda(Y)`. -/
abbrev YonedaProdOver (X Y : C) :=
  Over (yonedaProdPresheaf (C := C) X Y)

/-- The category of elements of `yonedaProd X Y`,
bifunctorial in `X` and `Y`.  The resulting category
(for fixed `X` and `Y`) has objects `(T, a, b)` with
`a : T ⟶ X` and `b : T ⟶ Y` (spans from `X` to `Y`),
and morphisms `s : T' ⟶ T` compatible with both
components.

Constructed as `yonedaProd` post-composed (via
`whiskeringRight`) with the functorial contravariant
category of elements `ElementsPreF`. -/
def yonedaProdElem : C ⥤ C ⥤ Cat :=
  yonedaProd ⋙
    (Functor.whiskeringRight C _ _).obj
      (ElementsPreF Cᵒᵖ)

theorem yonedaProdElem_obj (X Y : C) :
    (yonedaProdElem.obj X).obj Y =
    Cat.of
      (yonedaProdPresheaf X Y).ElementsPre :=
  rfl

/-- The slice category of `PSh(C)` over
`yonedaProd X Y`, bifunctorial in `X` and `Y`.

For fixed `(X, Y)`, the resulting category is
`Over (yonedaProd X Y)`, whose objects are
morphisms `G ⟶ yonedaProd X Y` in `PSh(C)` and
whose morphisms are commuting triangles.  By the
equivalence `sliceEquivCopresheaf`, this is
equivalent to copresheaves on the (covariant)
category of elements of `yonedaProd X Y`, i.e.
presheaves on the category of spans from `X` to `Y`.

Constructed as `yonedaProd` post-composed (via
`whiskeringRight`) with mathlib's `Over.mapFunctor`,
the functorial slice construction. -/
def yonedaProdSlice : C ⥤ C ⥤ Cat :=
  yonedaProd ⋙
    (Functor.whiskeringRight C _ _).obj
      (Over.mapFunctor (Cᵒᵖ ⥤ Type v))

theorem yonedaProdSlice_obj (X Y : C) :
    (yonedaProdSlice.obj X).obj Y =
    Cat.of (YonedaProdOver X Y) :=
  rfl

/-- The presheaf category on the category of elements
of `yonedaProd X Y`.  For fixed `(X, Y)`, this is
`PSh(∫(yoneda(X) × yoneda(Y)))`, whose objects are
presheaves on spans from `X` to `Y`.

For a bifunctorial version, use `yonedaProdSlice`,
which is equivalent pointwise via `sliceEquivPre`. -/
def yonedaProdElemPresheaf (X Y : C) : Cat :=
  Cat.of
    ((yonedaProdPresheaf X Y).ElementsPreᵒᵖ ⥤
      Type v)

/-- The slice category `Over (yonedaProd X Y)` in
`PSh(C)` is equivalent to the presheaf category on
the category of elements of `yonedaProd X Y`.

This is `sliceEquivPre` applied to `yonedaProd X Y`,
witnessing that `yonedaProdSlice` is pointwise the
presheaf topos `PSh(∫(yoneda(X) × yoneda(Y)))`. -/
def yonedaProdSlice_equiv (X Y : C) :
    ((yonedaProdSlice.obj X).obj Y).α ≌
    (yonedaProdElemPresheaf X Y).α :=
  sliceEquivPre (yonedaProdPresheaf X Y)

/-- `(yonedaProd.obj X).obj Y` is the explicit
`FunctorToTypes` product of `yoneda.obj X` and
`yoneda.obj Y`. -/
theorem yonedaProd_eq_prod (X Y : C) :
    yonedaProdPresheaf X Y =
    FunctorToTypes.prod
      (yoneda.obj X) (yoneda.obj Y) :=
  rfl

/-- First projection from the product presheaf
`yonedaProd X Y` to `yoneda X`, via
`FunctorToTypes.prod.fst`. -/
abbrev yonedaProdFst (X Y : C) :
    yonedaProdPresheaf X Y ⟶ yoneda.obj X :=
  @FunctorToTypes.prod.fst
    _ _ (yoneda.obj X) (yoneda.obj Y)

/-- Second projection from the product presheaf
`yonedaProd X Y` to `yoneda Y`, via
`FunctorToTypes.prod.snd`. -/
abbrev yonedaProdSnd (X Y : C) :
    yonedaProdPresheaf X Y ⟶ yoneda.obj Y :=
  @FunctorToTypes.prod.snd
    _ _ (yoneda.obj X) (yoneda.obj Y)

/-- Pairing of morphisms into representables to a
morphism into the product presheaf `yonedaProd X Y`,
via `FunctorToTypes.prod.lift`. -/
abbrev yonedaProdLift {P : Cᵒᵖ ⥤ Type v} (X Y : C)
    (f : P ⟶ yoneda.obj X)
    (g : P ⟶ yoneda.obj Y) :
    P ⟶ yonedaProdPresheaf X Y :=
  FunctorToTypes.prod.lift f g

/-- Two morphisms into `yonedaProdPresheaf X Y` are
equal iff their compositions with the two projections
agree. -/
theorem yonedaProdPresheaf_hom_ext
    {P : Cᵒᵖ ⥤ Type v} {X Y : C}
    {h₁ h₂ : P ⟶ yonedaProdPresheaf X Y}
    (hfst : h₁ ≫ yonedaProdFst X Y =
      h₂ ≫ yonedaProdFst X Y)
    (hsnd : h₁ ≫ yonedaProdSnd X Y =
      h₂ ≫ yonedaProdSnd X Y) :
    h₁ = h₂ := by
  ext T x
  exact Prod.ext
    (congr_fun (NatTrans.congr_app hfst T) x)
    (congr_fun (NatTrans.congr_app hsnd T) x)

@[simp]
theorem yonedaProdLift_fst_snd
    {P : Cᵒᵖ ⥤ Type v} (X Y : C)
    (h : P ⟶ yonedaProdPresheaf X Y) :
    yonedaProdLift X Y
      (h ≫ yonedaProdFst X Y)
      (h ≫ yonedaProdSnd X Y) = h :=
  yonedaProdPresheaf_hom_ext
    (by simp [yonedaProdLift])
    (by simp [yonedaProdLift])

/-- The identity relation on `X` in the over category,
given by the diagonal
`yoneda(X) → yoneda(X) × yoneda(X)`. -/
def yonedaProdOverId (X : C) :
    YonedaProdOver X X :=
  Over.mk (yonedaProdLift X X
    (𝟙 (yoneda.obj X)) (𝟙 (yoneda.obj X)))

@[simp]
theorem yonedaProdOverId_fst (X : C) :
    (yonedaProdOverId X).hom ≫
      yonedaProdFst X X =
    𝟙 (yoneda.obj X) :=
  rfl

@[simp]
theorem yonedaProdOverId_snd (X : C) :
    (yonedaProdOverId X).hom ≫
      yonedaProdSnd X X =
    𝟙 (yoneda.obj X) :=
  rfl

/-- The graph of a morphism `f : X ⟶ Y` as a
proof-relevant relation. The underlying presheaf is
`yoneda(X)`, with first projection the identity and
second projection `yoneda.map f`. At each test object
`T`, a pair `(a : T ⟶ X, b : T ⟶ Y)` is in the graph
iff `b = f ≫ a`. This generalizes `graphRel` from
`Type` to an arbitrary category `C`. -/
def yonedaProdOverGraph {X Y : C} (f : X ⟶ Y) :
    YonedaProdOver X Y :=
  Over.mk (yonedaProdLift X Y
    (𝟙 (yoneda.obj X)) (yoneda.map f))

@[simp]
theorem yonedaProdOverGraph_fst
    {X Y : C} (f : X ⟶ Y) :
    (yonedaProdOverGraph f).hom ≫
      yonedaProdFst X Y =
    𝟙 (yoneda.obj X) :=
  rfl

@[simp]
theorem yonedaProdOverGraph_snd
    {X Y : C} (f : X ⟶ Y) :
    (yonedaProdOverGraph f).hom ≫
      yonedaProdSnd X Y =
    yoneda.map f :=
  rfl

theorem yonedaProdOverGraph_snd_assoc
    {X Y : C} (f : X ⟶ Y)
    {P : Cᵒᵖ ⥤ Type v}
    (k : yoneda.obj Y ⟶ P) :
    (yonedaProdOverGraph f).hom ≫
      yonedaProdSnd X Y ≫ k =
    yoneda.map f ≫ k := by
  rw [← Category.assoc,
    yonedaProdOverGraph_snd]

theorem yonedaProdOverGraph_fst_assoc
    {X Y : C} (f : X ⟶ Y)
    {P : Cᵒᵖ ⥤ Type v}
    (k : yoneda.obj X ⟶ P) :
    (yonedaProdOverGraph f).hom ≫
      yonedaProdFst X Y ≫ k =
    k := by
  rw [← Category.assoc,
    yonedaProdOverGraph_fst]
  exact Category.id_comp k

theorem yonedaProdOverGraph_id (X : C) :
    yonedaProdOverGraph (𝟙 X) =
      yonedaProdOverId X := by
  simp [yonedaProdOverGraph, yonedaProdOverId,
    yoneda]

/-- Composition of proof-relevant relations in the over
category.

Given `R ⟶ yonedaProd X Y` and `S ⟶ yonedaProd Y Z`,
their composite is obtained by pulling back `R` and `S`
over `yoneda Y` (matching the second component of `R`
with the first component of `S`), then projecting the
first component from `R` and the second from `S` into
`yonedaProd X Z`. -/
def yonedaProdOverComp {X Y Z : C}
    (R : YonedaProdOver X Y)
    (S : YonedaProdOver Y Z) :
    YonedaProdOver X Z :=
  Over.mk
    (yonedaProdLift X Z
      (presheafPullbackFst
          (R.hom ≫ yonedaProdSnd X Y)
          (S.hom ≫ yonedaProdFst Y Z) ≫
        R.hom ≫ yonedaProdFst X Y)
      (presheafPullbackSnd
          (R.hom ≫ yonedaProdSnd X Y)
          (S.hom ≫ yonedaProdFst Y Z) ≫
        S.hom ≫ yonedaProdSnd Y Z))

/-- A relation from `X` to `Y` up to isomorphism:
an isomorphism class in the over category
`Over (yonedaProdPresheaf X Y)`. -/
abbrev YonedaRel (X Y : C) :=
  Skeleton (YonedaProdOver X Y)

/-- The identity relation on `X`, up to isomorphism. -/
def relId (X : C) : YonedaRel X X :=
  toSkeleton _ (yonedaProdOverId X)

/-- `yonedaProdOverComp` respects isomorphisms: given
isomorphisms `R₁ ≅ R₂` and `S₁ ≅ S₂` in the over
categories, their compositions are isomorphic. -/
def yonedaProdOverComp_iso {X Y Z : C}
    {R₁ R₂ : YonedaProdOver X Y}
    {S₁ S₂ : YonedaProdOver Y Z}
    (αR : R₁ ≅ R₂) (αS : S₁ ≅ S₂) :
    yonedaProdOverComp R₁ S₁ ≅
      yonedaProdOverComp R₂ S₂ := by
  have hR := Over.w αR.hom
  have hS := Over.w αS.hom
  refine Over.isoMk
    (presheafPullbackIsoOfIso
      ((Over.forget _).mapIso αR)
      ((Over.forget _).mapIso αS)
      (by simp only [Functor.mapIso_hom,
        Over.forget_map, ← Category.assoc, hR])
      (by simp only [Functor.mapIso_hom,
        Over.forget_map, ← Category.assoc, hS]))
    ?_
  simp only [yonedaProdOverComp, Over.mk_hom]
  apply yonedaProdPresheaf_hom_ext
  · -- fst projection
    open Limits in
    simp only [Category.assoc,
      FunctorToTypes.prod.lift_fst]
    rw [presheafPullbackIsoOfIso_hom_fst_assoc]
    simp only [Functor.mapIso_hom, Over.forget_map,
      ← Category.assoc, hR]
  · -- snd projection
    open Limits in
    simp only [Category.assoc,
      FunctorToTypes.prod.lift_snd]
    rw [presheafPullbackIsoOfIso_hom_snd_assoc]
    simp only [Functor.mapIso_hom, Over.forget_map,
      ← Category.assoc, hS]

/-- Left identity for `yonedaProdOverComp`: composing
with the identity relation on `X` yields an isomorphic
relation. -/
def yonedaProdOverComp_id_left
    {X Y : C} (R : YonedaProdOver X Y) :
    yonedaProdOverComp (yonedaProdOverId X) R ≅
      R :=
  Over.isoMk
    (presheafPullbackIdLeftIso
      (R.hom ≫ yonedaProdFst X Y))
    (by
      simp only [yonedaProdOverComp, Over.mk_hom]
      apply yonedaProdPresheaf_hom_ext
      · simp only [Category.assoc,
          presheafPullbackIdLeftIso]
        have := presheafPullbackCondition
          (𝟙 (yoneda.obj X))
          (R.hom ≫ yonedaProdFst X Y)
        simp only [Category.comp_id] at this
        exact this.symm
      · rfl)

/-- Right identity for `yonedaProdOverComp`: composing
with the identity relation on `Y` yields an isomorphic
relation. -/
def yonedaProdOverComp_id_right
    {X Y : C} (R : YonedaProdOver X Y) :
    yonedaProdOverComp R (yonedaProdOverId Y) ≅
      R :=
  Over.isoMk
    (presheafPullbackIdRightIso
      (R.hom ≫ yonedaProdSnd X Y))
    (by
      simp only [yonedaProdOverComp, Over.mk_hom]
      apply yonedaProdPresheaf_hom_ext
      · rfl
      · simp only [Category.assoc,
          presheafPullbackIdRightIso]
        exact presheafPullbackCondition _ _)

/-- Associativity for `yonedaProdOverComp`:
`(R ; S) ; T ≅ R ; (S ; T)`. -/
def yonedaProdOverComp_assoc
    {X Y Z W : C}
    (R : YonedaProdOver X Y)
    (S : YonedaProdOver Y Z)
    (T : YonedaProdOver Z W) :
    yonedaProdOverComp
      (yonedaProdOverComp R S) T ≅
    yonedaProdOverComp
      R (yonedaProdOverComp S T) :=
  Over.isoMk
    (presheafPullbackAssocIso
      (R.hom ≫ yonedaProdSnd X Y)
      (S.hom ≫ yonedaProdFst Y Z)
      (S.hom ≫ yonedaProdSnd Y Z)
      (T.hom ≫ yonedaProdFst Z W))
    (by
      simp only [yonedaProdOverComp, Over.mk_hom]
      apply yonedaProdPresheaf_hom_ext <;> rfl)

/-- The composite of two graph relations
`graph(f) ; graph(g)` is isomorphic to `graph(f ≫ g)`.
The pullback that defines relational composition
matches `yoneda.map f` with `𝟙 (yoneda Y)`, giving
back `yoneda X` via `presheafPullbackIdRightIso`. -/
def yonedaProdOverGraph_comp
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    yonedaProdOverComp
      (yonedaProdOverGraph f)
      (yonedaProdOverGraph g) ≅
    yonedaProdOverGraph (f ≫ g) :=
  Over.isoMk
    (presheafPullbackIdRightIso (yoneda.map f))
    (by
      simp only [yonedaProdOverComp,
        yonedaProdOverGraph, Over.mk_hom]
      apply yonedaProdPresheaf_hom_ext
      · simp [presheafPullbackIdRightIso,
          presheafPullbackLift]
      · simp only [Category.assoc,
          FunctorToTypes.prod.lift_snd,
          FunctorToTypes.prod.lift_fst]
        have hpb := presheafPullbackCondition
          (yoneda.map f) (𝟙 (yoneda.obj Y))
        simp only [Category.comp_id] at hpb
        change presheafPullbackFst
          (yoneda.map f) (𝟙 _) ≫
          yoneda.map (f ≫ g) = _
        rw [yoneda.map_comp,
          ← Category.assoc, hpb])

/-- Composition of relations up to isomorphism:
applies `yonedaProdOverComp` via `Skeleton.lift₂`,
using `yonedaProdOverComp_iso` for
well-definedness. -/
def relComp {X Y Z : C} :
    YonedaRel X Y → YonedaRel Y Z →
    YonedaRel X Z :=
  Skeleton.lift₂
    (fun R S =>
      toSkeleton _ (yonedaProdOverComp R S))
    (fun _ _ _ _ ⟨αR⟩ ⟨αS⟩ =>
      toSkeleton_eq_iff.mpr
        ⟨yonedaProdOverComp_iso αR αS⟩)

theorem relComp_relId_left
    {X Y : C} (R : YonedaRel X Y) :
    relComp (relId X) R = R := by
  induction R using Quotient.inductionOn with
  | h R' =>
    exact toSkeleton_eq_iff.mpr
      ⟨yonedaProdOverComp_id_left R'⟩

theorem relComp_relId_right
    {X Y : C} (R : YonedaRel X Y) :
    relComp R (relId Y) = R := by
  induction R using Quotient.inductionOn with
  | h R' =>
    exact toSkeleton_eq_iff.mpr
      ⟨yonedaProdOverComp_id_right R'⟩

theorem relComp_assoc
    {X Y Z W : C}
    (R : YonedaRel X Y)
    (S : YonedaRel Y Z)
    (T : YonedaRel Z W) :
    relComp (relComp R S) T =
      relComp R (relComp S T) := by
  induction R using Quotient.inductionOn with
  | h R' =>
  induction S using Quotient.inductionOn with
  | h S' =>
  induction T using Quotient.inductionOn with
  | h T' =>
    exact toSkeleton_eq_iff.mpr
      ⟨yonedaProdOverComp_assoc R' S' T'⟩

/-- The graph of a morphism as a `YonedaRel`
(isomorphism class of `YonedaProdOver`). -/
def yonedaRelGraph {X Y : C} (f : X ⟶ Y) :
    YonedaRel X Y :=
  toSkeleton _ (yonedaProdOverGraph f)

theorem yonedaRelGraph_eq_relId (X : C) :
    yonedaRelGraph (𝟙 X) = relId (C := C) X := by
  simp [yonedaRelGraph, relId,
    yonedaProdOverGraph_id]

theorem yonedaRelGraph_comp
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    relComp (yonedaRelGraph f) (yonedaRelGraph g) =
      yonedaRelGraph (f ≫ g) :=
  toSkeleton_eq_iff.mpr
    ⟨yonedaProdOverGraph_comp f g⟩

end PresheafRelations

section YonedaRelCategory

/-- Wrapper type for objects of `C` whose morphisms
are Yoneda relations (`YonedaRel`). Using a
`structure` prevents the existing `Category` instance
on `C` from leaking through. -/
@[ext]
structure YonedaRelCat (C : Type u)
    [Category.{v} C] where
  obj : C

instance : Category.{max u (v + 1)}
    (YonedaRelCat C) where
  Hom X Y := YonedaRel X.obj Y.obj
  id X := relId X.obj
  comp R S := relComp R S
  id_comp := relComp_relId_left
  comp_id := relComp_relId_right
  assoc := relComp_assoc

/-- Functor sending each morphism `f : X ⟶ Y` in
`C` to its graph relation `yonedaRelGraph f` in
`YonedaRelCat C`. This is the categorical
generalization of the assignment `f ↦ graphRel f`
from `Type` to an arbitrary category. -/
def yonedaRelGraphFunctor :
    C ⥤ YonedaRelCat C where
  obj X := ⟨X⟩
  map f := yonedaRelGraph f
  map_id X := yonedaRelGraph_eq_relId X
  map_comp f g := (yonedaRelGraph_comp f g).symm

end YonedaRelCategory

section RelatedMorphisms

/-- The bifunctorial action of a pair of morphisms
`(f, f')` on the product presheaf
`yoneda(A) × yoneda(A')`. At stage `T`, this sends
`(a : T ⟶ A, a' : T ⟶ A')` to
`(a ≫ f : T ⟶ B, a' ≫ f' : T ⟶ B')`. -/
abbrev yonedaProdMap {A A' B B' : C}
    (f : A ⟶ B) (f' : A' ⟶ B') :
    yonedaProdPresheaf A A' ⟶
      yonedaProdPresheaf B B' :=
  yonedaProdLift B B'
    (yonedaProdFst A A' ≫ yoneda.map f)
    (yonedaProdSnd A A' ≫ yoneda.map f')

@[simp]
theorem yonedaProdMap_fst {A A' B B' : C}
    (f : A ⟶ B) (f' : A' ⟶ B') :
    yonedaProdMap f f' ≫ yonedaProdFst B B' =
      yonedaProdFst A A' ≫ yoneda.map f := by
  simp [yonedaProdMap, yonedaProdLift]

@[simp]
theorem yonedaProdMap_snd {A A' B B' : C}
    (f : A ⟶ B) (f' : A' ⟶ B') :
    yonedaProdMap f f' ≫ yonedaProdSnd B B' =
      yonedaProdSnd A A' ≫ yoneda.map f' := by
  simp [yonedaProdMap, yonedaProdLift]

@[simp]
theorem yonedaProdMap_id (A A' : C) :
    yonedaProdMap (𝟙 A) (𝟙 A') =
      𝟙 (yonedaProdPresheaf A A') := by
  apply yonedaProdPresheaf_hom_ext <;>
    simp [yoneda]

theorem yonedaProdMap_comp
    {A A' B B' D D' : C}
    (f : A ⟶ B) (f' : A' ⟶ B')
    (g : B ⟶ D) (g' : B' ⟶ D') :
    yonedaProdMap (f ≫ g) (f' ≫ g') =
      yonedaProdMap f f' ≫
        yonedaProdMap g g' := by
  apply yonedaProdPresheaf_hom_ext <;> {
    simp only [Category.assoc,
      yonedaProdMap_fst, yonedaProdMap_snd]
    simp only [← Category.assoc,
      yonedaProdMap_fst, yonedaProdMap_snd]
    simp only [Category.assoc, yoneda.map_comp]
  }

/-- Two morphisms `f : A ⟶ B` and `f' : A' ⟶ B'` are
`(R, S)`-related at the `YonedaProdOver` level when
there exists a lift `φ : R.left ⟶ S.left` making the
square commute:
```
  R.left ---φ---> S.left
    |                |
    R.hom           S.hom
    v                v
  yonedaProd A A' -> yonedaProd B B'
         (yonedaProdMap f f')
```
-/
def YonedaProdOverRelated
    {A A' B B' : C}
    (R : YonedaProdOver A A')
    (S : YonedaProdOver B B')
    (f : A ⟶ B) (f' : A' ⟶ B') : Prop :=
  ∃ (φ : R.left ⟶ S.left),
    φ ≫ S.hom =
      R.hom ≫ yonedaProdMap f f'

/-- `YonedaProdOverRelated` is invariant under
isomorphism in both relation arguments. -/
theorem yonedaProdOverRelated_iso
    {A A' B B' : C}
    {R₁ R₂ : YonedaProdOver A A'}
    {S₁ S₂ : YonedaProdOver B B'}
    (αR : R₁ ≅ R₂) (αS : S₁ ≅ S₂)
    {f : A ⟶ B} {f' : A' ⟶ B'} :
    YonedaProdOverRelated R₁ S₁ f f' ↔
      YonedaProdOverRelated R₂ S₂ f f' := by
  constructor
  · rintro ⟨φ, hφ⟩
    exact ⟨αR.inv.left ≫ φ ≫ αS.hom.left, by
      simp only [Category.assoc, Over.w αS.hom]
      rw [hφ, ← Category.assoc,
        Over.w αR.inv]⟩
  · rintro ⟨φ, hφ⟩
    exact ⟨αR.hom.left ≫ φ ≫ αS.inv.left, by
      simp only [Category.assoc, Over.w αS.inv]
      rw [hφ, ← Category.assoc,
        Over.w αR.hom]⟩

/-- Two morphisms `f : A ⟶ B` and `f' : A' ⟶ B'` in
`C` are `(R, S)`-related (where `R : YonedaRel A A'`
and `S : YonedaRel B B'`) when they admit a lifting at
the `YonedaProdOver` level. This descends through the
skeleton quotient via `Skeleton.lift₂`, using
`yonedaProdOverRelated_iso` for well-definedness. -/
def relRelated
    {A A' B B' : C}
    (f : A ⟶ B) (f' : A' ⟶ B') :
    YonedaRel A A' → YonedaRel B B' → Prop :=
  Skeleton.lift₂
    (fun R S =>
      YonedaProdOverRelated R S f f')
    (fun _ _ _ _ ⟨αR⟩ ⟨αS⟩ =>
      propext
        (yonedaProdOverRelated_iso αR αS))

/-- For graph relations, `YonedaProdOverRelated`
reduces to commutativity of the naturality square.
The forward direction extracts the square from the
lift; the reverse constructs a lift from the commuting
square using `yoneda.map g₀`. -/
theorem yonedaProdOverRelated_graph_iff
    {A A' B B' : C}
    (f : A ⟶ A') (f' : B ⟶ B')
    (g₀ : A ⟶ B) (g₁ : A' ⟶ B') :
    YonedaProdOverRelated
      (yonedaProdOverGraph f)
      (yonedaProdOverGraph f')
      g₀ g₁ ↔
    g₀ ≫ f' = f ≫ g₁ := by
  constructor
  · rintro ⟨φ, hφ⟩
    have hfst : φ = yoneda.map g₀ := by
      have h :=
        congr_arg (· ≫ yonedaProdFst B B') hφ
      simp only [Category.assoc,
        yonedaProdOverGraph_fst,
        yonedaProdOverGraph_fst_assoc,
        yonedaProdMap_fst] at h
      exact h
    have hsnd : φ ≫ yoneda.map f' =
        yoneda.map f ≫ yoneda.map g₁ := by
      have h :=
        congr_arg (· ≫ yonedaProdSnd B B') hφ
      simp only [Category.assoc,
        yonedaProdOverGraph_snd,
        yonedaProdOverGraph_snd_assoc,
        yonedaProdMap_snd] at h
      exact h
    rw [hfst] at hsnd
    rw [← yoneda.map_comp,
      ← yoneda.map_comp] at hsnd
    exact yoneda.map_injective hsnd
  · intro hsq
    refine ⟨yoneda.map g₀, ?_⟩
    apply yonedaProdPresheaf_hom_ext
    · simp only [Category.assoc,
        yonedaProdOverGraph_fst,
        yonedaProdOverGraph_fst_assoc,
        yonedaProdMap_fst]
      exact Category.comp_id _
    · simp only [Category.assoc,
        yonedaProdOverGraph_snd,
        yonedaProdOverGraph_snd_assoc,
        yonedaProdMap_snd]
      rw [← yoneda.map_comp, hsq,
        yoneda.map_comp]

end RelatedMorphisms

/-- The square type family for the Yoneda relation
double category. Given vertical morphisms
`R : YonedaRel A C`, `S : YonedaRel B D` and
horizontal morphisms `f : A ⟶ B`, `f' : C ⟶ D`,
the square is `relRelated f f' R S`. -/
abbrev yonedaRelSQS :
    @SquareSet C YonedaRel (homSetOfQuiver C) :=
  fun R S f f' => relRelated f f' R S

@[reassoc (attr := simp)]
theorem yonedaProdOverComp_fst {X Y Z : C}
    (R : YonedaProdOver X Y)
    (S : YonedaProdOver Y Z) :
    (yonedaProdOverComp R S).hom ≫
      yonedaProdFst X Z =
    presheafPullbackFst
      (R.hom ≫ yonedaProdSnd X Y)
      (S.hom ≫ yonedaProdFst Y Z) ≫
    R.hom ≫ yonedaProdFst X Y := by
  simp [yonedaProdOverComp, yonedaProdLift]

@[reassoc (attr := simp)]
theorem yonedaProdOverComp_snd {X Y Z : C}
    (R : YonedaProdOver X Y)
    (S : YonedaProdOver Y Z) :
    (yonedaProdOverComp R S).hom ≫
      yonedaProdSnd X Z =
    presheafPullbackSnd
      (R.hom ≫ yonedaProdSnd X Y)
      (S.hom ≫ yonedaProdFst Y Z) ≫
    S.hom ≫ yonedaProdSnd Y Z := by
  simp [yonedaProdOverComp, yonedaProdLift]

/-- Horizontal composition of relatedness squares.

Given `relRelated f g R S` (a square with top `f`,
bottom `g`, left `R`, right `S`) and
`relRelated f' g' S T`, the composite has top
`f ≫ f'`, bottom `g ≫ g'`, left `R`, right `T`.

The witness at the `YonedaProdOver` level is the
composite `φ₁ ≫ φ₂` of the two individual witnesses,
with commutativity following from `yonedaProdMap_comp`. -/
theorem relRelatedHComp
    {A₁ A₂ A₃ B₁ B₂ B₃ : C}
    {R : YonedaRel A₁ B₁}
    {S : YonedaRel A₂ B₂}
    {T : YonedaRel A₃ B₃}
    {f : A₁ ⟶ A₂} {f' : A₂ ⟶ A₃}
    {g : B₁ ⟶ B₂} {g' : B₂ ⟶ B₃}
    (α : relRelated f g R S)
    (β : relRelated f' g' S T) :
    relRelated (f ≫ f') (g ≫ g') R T := by
  induction R using Quotient.inductionOn with
  | h R₀ =>
  induction S using Quotient.inductionOn with
  | h S₀ =>
  induction T using Quotient.inductionOn with
  | h T₀ =>
  obtain ⟨φ₁, hφ₁⟩ := α
  obtain ⟨φ₂, hφ₂⟩ := β
  exact ⟨φ₁ ≫ φ₂, by
    rw [Category.assoc, hφ₂,
      ← Category.assoc, hφ₁, Category.assoc,
      yonedaProdMap_comp]⟩

/-- Horizontal identity square: for each vertical
morphism `R : YonedaRel A B`, the pair `(𝟙 A, 𝟙 B)` is
`(R, R)`-related.

The witness is the identity `𝟙 R₀.left`, with
commutativity following from `yonedaProdMap_id`. -/
theorem relRelatedSqHorId
    {A B : C}
    (R : YonedaRel (C := C) A B) :
    relRelated (𝟙 A) (𝟙 B) R R := by
  induction R using Quotient.inductionOn with
  | h R₀ =>
  exact ⟨𝟙 R₀.left, by
    simp [yonedaProdMap_id]⟩

/-- Vertical identity square: for each horizontal
morphism `f : A ⟶ B`, the pair `(relId A, relId B)` is
`(f, f)`-related.

The witness is `yoneda.map f`, with commutativity
checked componentwise via `yonedaProdPresheaf_hom_ext`. -/
theorem relRelatedSqVertId
    {A B : C}
    (f : A ⟶ B) :
    relRelated f f
      (relId (C := C) A) (relId B) := by
  change YonedaProdOverRelated
    (yonedaProdOverId A) (yonedaProdOverId B) f f
  refine ⟨yoneda.map f, ?_⟩
  ext T x
  exact Prod.ext rfl rfl

/-- Vertical composition of relatedness squares.

Given `relRelated f g R S` and `relRelated g h R' S'`,
the composite has top `f`, bottom `h`, left
`relComp R R'`, right `relComp S S'`.

At the `YonedaProdOver` level, the witness is
constructed via `presheafPullbackLift` from the
two individual witnesses composed with the pullback
projections. -/
theorem relRelatedVComp
    {A₁ A₂ A₃ B₁ B₂ B₃ : C}
    {R : YonedaRel A₁ A₂}
    {S : YonedaRel B₁ B₂}
    {R' : YonedaRel A₂ A₃}
    {S' : YonedaRel B₂ B₃}
    {f : A₁ ⟶ B₁} {g : A₂ ⟶ B₂} {h : A₃ ⟶ B₃}
    (α : relRelated f g R S)
    (β : relRelated g h R' S') :
    relRelated f h (relComp R R')
      (relComp S S') := by
  induction R using Quotient.inductionOn with
  | h R₀ =>
  induction S using Quotient.inductionOn with
  | h S₀ =>
  induction R' using Quotient.inductionOn with
  | h R₀' =>
  induction S' using Quotient.inductionOn with
  | h S₀' =>
  obtain ⟨φ₁, hφ₁⟩ := α
  obtain ⟨φ₂, hφ₂⟩ := β
  have hφ₁_r := reassoc_of% hφ₁
  have hφ₂_r := reassoc_of% hφ₂
  have pbcondR := presheafPullbackCondition
    (R₀.hom ≫ yonedaProdSnd A₁ A₂)
    (R₀'.hom ≫ yonedaProdFst A₂ A₃)
  have pbcondR_r := reassoc_of% pbcondR
  refine ⟨presheafPullbackLift
    (S₀.hom ≫ yonedaProdSnd B₁ B₂)
    (S₀'.hom ≫ yonedaProdFst B₂ B₃)
    (presheafPullbackFst
      (R₀.hom ≫ yonedaProdSnd A₁ A₂)
      (R₀'.hom ≫ yonedaProdFst A₂ A₃) ≫ φ₁)
    (presheafPullbackSnd
      (R₀.hom ≫ yonedaProdSnd A₁ A₂)
      (R₀'.hom ≫ yonedaProdFst A₂ A₃) ≫ φ₂)
    ?_, ?_⟩
  · -- Pullback condition for the lift
    simp only [Category.assoc, hφ₁_r,
      yonedaProdMap_snd, hφ₂_r,
      yonedaProdMap_fst]
    exact pbcondR_r _
  · -- Commutativity
    apply yonedaProdPresheaf_hom_ext <;>
    simp only [Category.assoc,
      yonedaProdOverComp_fst,
      yonedaProdOverComp_fst_assoc,
      yonedaProdOverComp_snd,
      yonedaProdOverComp_snd_assoc,
      yonedaProdMap_fst, yonedaProdMap_snd,
      PullbackCone.IsLimit.lift_fst_assoc,
      PullbackCone.IsLimit.lift_snd_assoc,
      hφ₁_r, hφ₂_r]

/-- Operations for the Yoneda relation double category
on objects of `C`. -/
def yonedaRelDoubleOps :
    DoubleCategoryOps C YonedaRel
      (homSetOfQuiver C) yonedaRelSQS where
  vComp := fun R S => relComp R S
  hComp := fun f g => f ≫ g
  vId := fun A => relId A
  hId := fun A => 𝟙 A
  sqVComp := fun α β => relRelatedVComp α β
  sqHComp := fun α β => relRelatedHComp α β
  sqVertId := fun h => relRelatedSqVertId h
  sqHorId := fun v => relRelatedSqHorId v

/-- Laws for the Yoneda relation double category.

The vertical category laws follow from `relComp_assoc`,
`relComp_relId_left`, `relComp_relId_right`. The
horizontal category laws follow from `Category.assoc`,
`Category.id_comp`, `Category.comp_id`. All square
laws hold because the square type `relRelated` is
`Prop`-valued: either both sides have the same type
(use `Subsingleton.elim`) or the types differ by a
category law (use `Subsingleton.helim`). -/
theorem yonedaRelDoubleLaws :
    DoubleCategoryLaws
      (yonedaRelDoubleOps (C := C)) where
  vertLaws := {
    assoc := fun R S T => relComp_assoc R S T
    id_laws := {
      id_comp := fun R => relComp_relId_left R
      comp_id := fun R => relComp_relId_right R
    }
  }
  horLaws := {
    assoc := fun f g h => Category.assoc f g h
    id_laws := {
      id_comp := fun f => Category.id_comp f
      comp_id := fun f => Category.comp_id f
    }
  }
  sqLaws := {
    sqVAssoc := fun _ _ _ => by
      simp only [yonedaRelDoubleOps, relComp_assoc]
      exact HEq.rfl
    sqHAssoc := fun _ _ _ => by
      simp only [yonedaRelDoubleOps, Category.assoc]
      exact HEq.rfl
    sqVIdComp := fun _ => by
      simp only [yonedaRelDoubleOps,
        relComp_relId_left]
      exact HEq.rfl
    sqVCompId := fun _ => by
      simp only [yonedaRelDoubleOps,
        relComp_relId_right]
      exact HEq.rfl
    sqHIdComp := fun _ => by
      simp only [yonedaRelDoubleOps,
        Category.id_comp]
      exact HEq.rfl
    sqHCompId := fun _ => by
      simp only [yonedaRelDoubleOps,
        Category.comp_id]
      exact HEq.rfl
    interchange := fun _ _ _ _ =>
      Subsingleton.elim _ _
    vertIdVComp := fun _ _ =>
      Subsingleton.elim _ _
    horIdHComp := fun _ _ =>
      Subsingleton.elim _ _
    idOnId := fun _ =>
      Subsingleton.elim _ _
  }

/-- The Yoneda relation double category data on
objects of `C`: operations and laws bundled
together. -/
def yonedaRelDoubleData :
    DoubleCategoryData C YonedaRel
      (homSetOfQuiver C) yonedaRelSQS where
  toDoubleCategoryOps := yonedaRelDoubleOps
  laws := yonedaRelDoubleLaws

end GebLean
