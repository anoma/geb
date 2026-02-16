import GebLean.PshRelDouble
import GebLean.Utilities.Elements
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Products.Basic

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
  pshProdPresheaf (yoneda.obj X) (yoneda.obj Y)

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
    h₁ = h₂ :=
  pshProdPresheaf_hom_ext hfst hsnd

@[simp]
theorem yonedaProdLift_fst_snd
    {P : Cᵒᵖ ⥤ Type v} (X Y : C)
    (h : P ⟶ yonedaProdPresheaf X Y) :
    yonedaProdLift X Y
      (h ≫ yonedaProdFst X Y)
      (h ≫ yonedaProdSnd X Y) = h :=
  pshProdLift_fst_snd h

/-- The identity relation on `X` in the over category,
given by the diagonal
`yoneda(X) → yoneda(X) × yoneda(X)`. -/
abbrev yonedaProdOverId (X : C) :
    YonedaProdOver X X :=
  pshProdOverId (yoneda.obj X)

@[simp]
theorem yonedaProdOverId_fst (X : C) :
    (yonedaProdOverId X).hom ≫
      yonedaProdFst X X =
    𝟙 (yoneda.obj X) :=
  pshProdOverId_fst (yoneda.obj X)

@[simp]
theorem yonedaProdOverId_snd (X : C) :
    (yonedaProdOverId X).hom ≫
      yonedaProdSnd X X =
    𝟙 (yoneda.obj X) :=
  pshProdOverId_snd (yoneda.obj X)

/-- The graph of a morphism `f : X ⟶ Y` as a
proof-relevant relation. The underlying presheaf is
`yoneda(X)`, with first projection the identity and
second projection `yoneda.map f`. At each test object
`T`, a pair `(a : T ⟶ X, b : T ⟶ Y)` is in the graph
iff `b = f ≫ a`. This generalizes `graphRel` from
`Type` to an arbitrary category `C`. -/
abbrev yonedaProdOverGraph {X Y : C}
    (f : X ⟶ Y) : YonedaProdOver X Y :=
  pshProdOverGraph (yoneda.map f)

@[simp]
theorem yonedaProdOverGraph_fst
    {X Y : C} (f : X ⟶ Y) :
    (yonedaProdOverGraph f).hom ≫
      yonedaProdFst X Y =
    𝟙 (yoneda.obj X) :=
  pshProdOverGraph_fst (yoneda.map f)

@[simp]
theorem yonedaProdOverGraph_snd
    {X Y : C} (f : X ⟶ Y) :
    (yonedaProdOverGraph f).hom ≫
      yonedaProdSnd X Y =
    yoneda.map f :=
  pshProdOverGraph_snd (yoneda.map f)

theorem yonedaProdOverGraph_snd_assoc
    {X Y : C} (f : X ⟶ Y)
    {P : Cᵒᵖ ⥤ Type v}
    (k : yoneda.obj Y ⟶ P) :
    (yonedaProdOverGraph f).hom ≫
      yonedaProdSnd X Y ≫ k =
    yoneda.map f ≫ k :=
  pshProdOverGraph_snd_assoc (yoneda.map f) k

theorem yonedaProdOverGraph_fst_assoc
    {X Y : C} (f : X ⟶ Y)
    {P : Cᵒᵖ ⥤ Type v}
    (k : yoneda.obj X ⟶ P) :
    (yonedaProdOverGraph f).hom ≫
      yonedaProdFst X Y ≫ k =
    k :=
  pshProdOverGraph_fst_assoc (yoneda.map f) k

theorem yonedaProdOverGraph_id (X : C) :
    yonedaProdOverGraph (𝟙 X) =
      yonedaProdOverId X := by
  simp [yonedaProdOverGraph, yonedaProdOverId,
    pshProdOverGraph, pshProdOverId, yoneda]

/-- Composition of proof-relevant relations in the over
category.

Given `R ⟶ yonedaProd X Y` and `S ⟶ yonedaProd Y Z`,
their composite is obtained by pulling back `R` and `S`
over `yoneda Y` (matching the second component of `R`
with the first component of `S`), then projecting the
first component from `R` and the second from `S` into
`yonedaProd X Z`. -/
abbrev yonedaProdOverComp {X Y Z : C}
    (R : YonedaProdOver X Y)
    (S : YonedaProdOver Y Z) :
    YonedaProdOver X Z :=
  pshProdOverComp R S

/-- A relation from `X` to `Y` up to isomorphism:
an isomorphism class in the over category
`Over (yonedaProdPresheaf X Y)`. -/
abbrev YonedaRel (X Y : C) :=
  Skeleton (YonedaProdOver X Y)

/-- The identity relation on `X`, up to isomorphism. -/
abbrev relId (X : C) : YonedaRel X X :=
  pshRelId (yoneda.obj X)

/-- `yonedaProdOverComp` respects isomorphisms: given
isomorphisms `R₁ ≅ R₂` and `S₁ ≅ S₂` in the over
categories, their compositions are isomorphic. -/
abbrev yonedaProdOverComp_iso {X Y Z : C}
    {R₁ R₂ : YonedaProdOver X Y}
    {S₁ S₂ : YonedaProdOver Y Z}
    (αR : R₁ ≅ R₂) (αS : S₁ ≅ S₂) :
    yonedaProdOverComp R₁ S₁ ≅
      yonedaProdOverComp R₂ S₂ :=
  pshProdOverComp_iso αR αS

/-- Left identity for `yonedaProdOverComp`: composing
with the identity relation on `X` yields an isomorphic
relation. -/
abbrev yonedaProdOverComp_id_left
    {X Y : C} (R : YonedaProdOver X Y) :
    yonedaProdOverComp (yonedaProdOverId X) R ≅
      R :=
  pshProdOverComp_id_left R

/-- Right identity for `yonedaProdOverComp`: composing
with the identity relation on `Y` yields an isomorphic
relation. -/
abbrev yonedaProdOverComp_id_right
    {X Y : C} (R : YonedaProdOver X Y) :
    yonedaProdOverComp R (yonedaProdOverId Y) ≅
      R :=
  pshProdOverComp_id_right R

/-- Associativity for `yonedaProdOverComp`:
`(R ; S) ; T ≅ R ; (S ; T)`. -/
abbrev yonedaProdOverComp_assoc
    {X Y Z W : C}
    (R : YonedaProdOver X Y)
    (S : YonedaProdOver Y Z)
    (T : YonedaProdOver Z W) :
    yonedaProdOverComp
      (yonedaProdOverComp R S) T ≅
    yonedaProdOverComp
      R (yonedaProdOverComp S T) :=
  pshProdOverComp_assoc R S T

/-- The composite of two graph relations
`graph(f) ; graph(g)` is isomorphic to `graph(f ≫ g)`.
The pullback that defines relational composition
matches `yoneda.map f` with `𝟙 (yoneda Y)`, giving
back `yoneda X` via `presheafPullbackIdRightIso`. -/
abbrev yonedaProdOverGraph_comp
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    yonedaProdOverComp
      (yonedaProdOverGraph f)
      (yonedaProdOverGraph g) ≅
    yonedaProdOverGraph (f ≫ g) :=
  pshProdOverGraph_comp (yoneda.map f)
    (yoneda.map g) ≪≫
  eqToIso (by simp [yonedaProdOverGraph,
    pshProdOverGraph, yoneda.map_comp])

/-- Composition of relations up to isomorphism:
applies `yonedaProdOverComp` via `Skeleton.lift₂`,
using `yonedaProdOverComp_iso` for
well-definedness. -/
abbrev relComp {X Y Z : C} :
    YonedaRel X Y → YonedaRel Y Z →
    YonedaRel X Z :=
  pshRelComp

theorem relComp_relId_left
    {X Y : C} (R : YonedaRel X Y) :
    relComp (relId X) R = R :=
  pshRelComp_id_left R

theorem relComp_relId_right
    {X Y : C} (R : YonedaRel X Y) :
    relComp R (relId Y) = R :=
  pshRelComp_id_right R

theorem relComp_assoc
    {X Y Z W : C}
    (R : YonedaRel X Y)
    (S : YonedaRel Y Z)
    (T : YonedaRel Z W) :
    relComp (relComp R S) T =
      relComp R (relComp S T) :=
  pshRelComp_assoc R S T

/-- The graph of a morphism as a `YonedaRel`
(isomorphism class of `YonedaProdOver`). -/
def yonedaRelGraph {X Y : C} (f : X ⟶ Y) :
    YonedaRel X Y :=
  pshRelGraph (yoneda.map f)

theorem yonedaRelGraph_eq_relId (X : C) :
    yonedaRelGraph (𝟙 X) = relId (C := C) X := by
  simp [yonedaRelGraph, relId,
    pshRelGraph, pshRelId,
    pshProdOverGraph, pshProdOverId, yoneda]

theorem yonedaRelGraph_comp
    {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    relComp (yonedaRelGraph f) (yonedaRelGraph g) =
      yonedaRelGraph (f ≫ g) := by
  simp only [yonedaRelGraph, relComp,
    yoneda.map_comp]
  exact pshRelGraph_comp (yoneda.map f)
    (yoneda.map g)

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
  pshProdMap (yoneda.map f) (yoneda.map f')

@[simp]
theorem yonedaProdMap_fst {A A' B B' : C}
    (f : A ⟶ B) (f' : A' ⟶ B') :
    yonedaProdMap f f' ≫ yonedaProdFst B B' =
      yonedaProdFst A A' ≫ yoneda.map f :=
  pshProdMap_fst (yoneda.map f) (yoneda.map f')

@[simp]
theorem yonedaProdMap_snd {A A' B B' : C}
    (f : A ⟶ B) (f' : A' ⟶ B') :
    yonedaProdMap f f' ≫ yonedaProdSnd B B' =
      yonedaProdSnd A A' ≫ yoneda.map f' :=
  pshProdMap_snd (yoneda.map f) (yoneda.map f')

@[simp]
theorem yonedaProdMap_id (A A' : C) :
    yonedaProdMap (𝟙 A) (𝟙 A') =
      𝟙 (yonedaProdPresheaf A A') := by
  simp only [yonedaProdMap, yoneda.map_id]
  exact pshProdMap_id
    (yoneda.obj A) (yoneda.obj A')

theorem yonedaProdMap_comp
    {A A' B B' D D' : C}
    (f : A ⟶ B) (f' : A' ⟶ B')
    (g : B ⟶ D) (g' : B' ⟶ D') :
    yonedaProdMap (f ≫ g) (f' ≫ g') =
      yonedaProdMap f f' ≫
        yonedaProdMap g g' := by
  simp only [yonedaProdMap, yoneda.map_comp]
  exact pshProdMap_comp
    (yoneda.map f) (yoneda.map f')
    (yoneda.map g) (yoneda.map g')

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
abbrev YonedaProdOverRelated
    {A A' B B' : C}
    (R : YonedaProdOver A A')
    (S : YonedaProdOver B B')
    (f : A ⟶ B) (f' : A' ⟶ B') : Prop :=
  PshProdOverRelated R S
    (yoneda.map f) (yoneda.map f')

/-- `YonedaProdOverRelated` is invariant under
isomorphism in both relation arguments. -/
theorem yonedaProdOverRelated_iso
    {A A' B B' : C}
    {R₁ R₂ : YonedaProdOver A A'}
    {S₁ S₂ : YonedaProdOver B B'}
    (αR : R₁ ≅ R₂) (αS : S₁ ≅ S₂)
    {f : A ⟶ B} {f' : A' ⟶ B'} :
    YonedaProdOverRelated R₁ S₁ f f' ↔
      YonedaProdOverRelated R₂ S₂ f f' :=
  pshProdOverRelated_iso αR αS

/-- Two morphisms `f : A ⟶ B` and `f' : A' ⟶ B'` in
`C` are `(R, S)`-related (where `R : YonedaRel A A'`
and `S : YonedaRel B B'`) when they admit a lifting at
the `YonedaProdOver` level. This descends through the
skeleton quotient via `Skeleton.lift₂`, using
`yonedaProdOverRelated_iso` for well-definedness. -/
abbrev relRelated
    {A A' B B' : C}
    (f : A ⟶ B) (f' : A' ⟶ B') :
    YonedaRel A A' → YonedaRel B B' → Prop :=
  pshRelRelated (yoneda.map f) (yoneda.map f')

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
  rw [show YonedaProdOverRelated
    (yonedaProdOverGraph f)
    (yonedaProdOverGraph f') g₀ g₁ =
    PshProdOverRelated
      (pshProdOverGraph (yoneda.map f))
      (pshProdOverGraph (yoneda.map f'))
      (yoneda.map g₀) (yoneda.map g₁) from rfl]
  rw [pshProdOverRelated_graph_iff]
  constructor
  · intro h
    rw [← yoneda.map_comp,
      ← yoneda.map_comp] at h
    exact yoneda.map_injective h
  · intro hsq
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
    R.hom ≫ yonedaProdFst X Y :=
  pshProdOverComp_fst R S

@[reassoc (attr := simp)]
theorem yonedaProdOverComp_snd {X Y Z : C}
    (R : YonedaProdOver X Y)
    (S : YonedaProdOver Y Z) :
    (yonedaProdOverComp R S).hom ≫
      yonedaProdSnd X Z =
    presheafPullbackSnd
      (R.hom ≫ yonedaProdSnd X Y)
      (S.hom ≫ yonedaProdFst Y Z) ≫
    S.hom ≫ yonedaProdSnd Y Z :=
  pshProdOverComp_snd R S

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
  change pshRelRelated
    (yoneda.map (f ≫ f'))
    (yoneda.map (g ≫ g')) R T
  simp only [yoneda.map_comp]
  exact pshRelRelatedHComp α β

/-- Horizontal identity square: for each vertical
morphism `R : YonedaRel A B`, the pair `(𝟙 A, 𝟙 B)` is
`(R, R)`-related.

The witness is the identity `𝟙 R₀.left`, with
commutativity following from `yonedaProdMap_id`. -/
theorem relRelatedSqHorId
    {A B : C}
    (R : YonedaRel (C := C) A B) :
    relRelated (𝟙 A) (𝟙 B) R R := by
  change pshRelRelated
    (yoneda.map (𝟙 A))
    (yoneda.map (𝟙 B)) R R
  simp only [yoneda.map_id]
  exact pshRelRelatedSqHorId R

/-- Vertical identity square: for each horizontal
morphism `f : A ⟶ B`, the pair `(relId A, relId B)` is
`(f, f)`-related.

The witness is `yoneda.map f`, with commutativity
checked componentwise via `yonedaProdPresheaf_hom_ext`. -/
theorem relRelatedSqVertId
    {A B : C}
    (f : A ⟶ B) :
    relRelated f f
      (relId (C := C) A) (relId B) :=
  pshRelRelatedSqVertId (yoneda.map f)

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
      (relComp S S') :=
  pshRelRelatedVComp α β

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
