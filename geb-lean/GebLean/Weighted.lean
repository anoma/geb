import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Basic
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Products.Basic
import GebLean.Utilities.TwistedArrow

/-!
# Weighted limits and colimits via twisted arrow categories

This module establishes the relationship between wedges/cowedges and
cones/cocones via twisted arrow categories.

For a profunctor `P : Cᵒᵖ ⥤ C ⥤ D`:
- A wedge for `P` is a cone for `P' : TwistedArrow C ⥤ D` where `P'` is
  the composition of `P` with the forgetful functor from twisted arrows.
- A cowedge for `P` is a cocone for `P'' : CoTwistedArrow' C ⥤ D` obtained
  similarly via the co-twisted arrow category.

This formulation provides a foundation for weighted limits and colimits,
where ends and coends are the prototypical examples.

## References

* [nLab: weighted limit](https://ncatlab.org/nlab/show/weighted+limit)
* [nLab: end](https://ncatlab.org/nlab/show/end)
* [Riehl: Weighted Limits and Colimits](https://math.jhu.edu/~eriehl/weighted.pdf)
-/

namespace GebLean

open CategoryTheory
open CategoryTheory.Limits

universe v u w

variable {C : Type u} [Category.{v} C]

section TwistedArrowForgetful

/-!
## Forgetful functors from twisted arrow categories

The twisted arrow category `TwistedArrow C` forgets to `Cᵒᵖ × C` via
the standard forgetful functor from the category of elements.
-/

/--
The forgetful functor from `TwistedArrow C` to `Cᵒᵖ × C`.

This is `CategoryOfElements.π` applied to the hom functor.
-/
abbrev twistedArrowForget : TwistedArrow C ⥤ Cᵒᵖ × C :=
  CategoryOfElements.π (Functor.hom C)

/--
The forgetful functor from `CoTwistedArrow C` to `Cᵒᵖᵒᵖ × Cᵒᵖ`.

This projects from the co-twisted arrow category to the base product category.
The encoding stores `(op (op coTwCod), op coTwDom)` in the pair.
-/
def coTwistedArrowForget : CoTwistedArrow C ⥤ Cᵒᵖᵒᵖ × Cᵒᵖ where
  obj tw := (Opposite.op (Opposite.op (coTwCod tw)), Opposite.op (coTwDom tw))
  map f := ⟨(coTwCodArr f).op.op, (coTwDomArr f).op⟩
  map_id tw := by
    ext <;> rfl
  map_comp f g := by
    ext <;> rfl

end TwistedArrowForgetful

section ProfunctorOnTwistedArrow

/-!
## Profunctors composed with forgetful functors

Given a profunctor `P : Cᵒᵖ ⥤ C ⥤ D`, we can compose with the forgetful
functor to get a functor `TwistedArrow C ⥤ D`.
-/

variable {D : Type w} [Category.{v} D]

/--
Given a profunctor `P : Cᵒᵖ ⥤ C ⥤ D`, compose with the forgetful functor
to get a functor from `TwistedArrow C` to `D`.

For a twisted arrow `(dom, cod, f)`, this evaluates to `(P.obj (op dom)).obj cod`.
-/
def profunctorOnTwistedArrow (P : Cᵒᵖ ⥤ C ⥤ D) : TwistedArrow C ⥤ D :=
  twistedArrowForget ⋙ Functor.uncurry.obj P

@[simp]
theorem profunctorOnTwistedArrow_obj (P : Cᵒᵖ ⥤ C ⥤ D) (tw : TwistedArrow C) :
    (profunctorOnTwistedArrow P).obj tw =
    (P.obj (Opposite.op (twDom tw))).obj (twCod tw) := rfl

@[simp]
theorem profunctorOnTwistedArrow_map (P : Cᵒᵖ ⥤ C ⥤ D)
    {x y : TwistedArrow C} (f : x ⟶ y) :
    (profunctorOnTwistedArrow P).map f =
    (P.map (twDomArr f).op).app (twCod x) ≫
    (P.obj (Opposite.op (twDom y))).map (twCodArr f) := rfl

end ProfunctorOnTwistedArrow

section WedgeAsCone

/-!
## Wedges as cones over twisted arrow categories

For a profunctor `P : Cᵒᵖ ⥤ C ⥤ D`, a wedge for `P` with apex `X` consists of:
- For each `j : C`, a morphism `π j : X ⟶ (P.obj (op j)).obj j`
- Compatibility: for `f : i ⟶ j`, we have
  `π i ≫ (P.obj (op i)).map f = π j ≫ (P.map f.op).app j`

This is exactly a cone over the functor `profunctorOnTwistedArrow P`:
- The cone point is `X`
- The legs are indexed by `TwistedArrow C`
- For a twisted arrow `tw = (dom, cod, f)`, the leg is
  `X ⟶ (P.obj (op dom)).obj cod`

The wedge condition follows from the cone naturality condition.
-/

variable {D : Type w} [Category.{v} D]

/--
Convert a cone over `profunctorOnTwistedArrow P` to component morphisms
indexed by objects of `C` (the diagonal components).
-/
def coneToWedgeComponents (P : Cᵒᵖ ⥤ C ⥤ D)
    (c : Cone (profunctorOnTwistedArrow P)) (j : C) :
    c.pt ⟶ (P.obj (Opposite.op j)).obj j :=
  c.π.app (twObjMk (𝟙 j))

/--
A cone over `profunctorOnTwistedArrow P` is determined by its diagonal
components `coneToWedgeComponents`.

This shows that the data of a cone leg at any twisted arrow can be recovered
from the diagonal components via composition with the profunctor action.
-/
theorem cone_determined_by_wedge_components (P : Cᵒᵖ ⥤ C ⥤ D)
    (c : Cone (profunctorOnTwistedArrow P)) (tw : TwistedArrow C) :
    c.π.app tw = coneToWedgeComponents P c (twDom tw) ≫
                 (P.obj (Opposite.op (twDom tw))).map (twArr tw) := by
  unfold coneToWedgeComponents
  let twId := twObjMk (𝟙 (twDom tw))
  have twId_arr : twArr twId = 𝟙 (twDom tw) := @twObjMk_arr _ _ _ _ (𝟙 (twDom tw))
  have cond : 𝟙 (twDom tw) ≫ twArr twId ≫ twArr tw = twArr tw := by
    rw [twId_arr, Category.id_comp, Category.id_comp]
  let morph := twHomMk (x := twId) (y := tw)
    (domArr := 𝟙 (twDom tw)) (codArr := twArr tw) cond
  have dom_eq : twDomArr morph = 𝟙 (twDom tw) := rfl
  have cod_eq : twCodArr morph = twArr tw := rfl
  have twId_cod : twCod twId = twDom tw := rfl
  have map_eq : (profunctorOnTwistedArrow P).map morph =
      (P.obj (Opposite.op (twDom tw))).map (twArr tw) := by
    simp only [profunctorOnTwistedArrow_map, dom_eq, cod_eq, op_id]
    rw [P.map_id (Opposite.op (twDom tw)), NatTrans.id_app]
    exact Category.id_comp _
  have h := c.π.naturality morph
  simp only [Functor.const_obj_map] at h
  have h' : c.π.app tw = c.π.app twId ≫ (profunctorOnTwistedArrow P).map morph := by
    calc c.π.app tw = 𝟙 c.pt ≫ c.π.app tw := (Category.id_comp _).symm
      _ = c.π.app twId ≫ (profunctorOnTwistedArrow P).map morph := h
  rw [map_eq] at h'
  exact h'

end WedgeAsCone

section CowedgeAsCocone

/-!
## Profunctors on co-twisted arrow categories

For a profunctor `P : Cᵒᵖ ⥤ C ⥤ D`, we can evaluate it on the co-twisted
arrow category to get a functor `CoTwistedArrow C ⥤ D`.

For a co-twisted arrow with domain `a` and codomain `b` (representing a
morphism `a ⟶ b`), the functor evaluates to `(P.obj (op a)).obj b = P(a, b)`.

A cocone over this functor consists of:
- For each morphism `f : i ⟶ j`, a morphism from `P(i, j)` to the apex
- Naturality conditions relating these

The diagonal components (at identity morphisms) satisfy factorization
properties: for `f : i ⟶ j`, both `P(i, i) ⟶ apex` and `P(j, j) ⟶ apex`
factor through `P(i, j) ⟶ apex` via the profunctor's covariant and
contravariant actions respectively.

The functor `profunctorOnCoTwistedArrow P` is defined via composition:
- `coTwistedArrowForget` projects to `Cᵒᵖᵒᵖ × Cᵒᵖ`
- `Prod.braiding` gives `Cᵒᵖ × Cᵒᵖᵒᵖ`
- Applying `opOpEquivalence` to the second component gives `Cᵒᵖ × C`
- Finally, `Functor.uncurry.obj P` evaluates the profunctor
-/

variable {D : Type w} [Category.{v} D]

/--
The equivalence from `Cᵒᵖᵒᵖ × Cᵒᵖ` to `Cᵒᵖ × C` via swap and `opOpEquivalence`.
-/
def coTwistedArrowProdEquiv :
    Cᵒᵖᵒᵖ × Cᵒᵖ ≌ Cᵒᵖ × C :=
  (Prod.braiding Cᵒᵖᵒᵖ Cᵒᵖ).trans
    (CategoryTheory.Equivalence.prod
      (CategoryTheory.Equivalence.refl (C := Cᵒᵖ))
      (opOpEquivalence C))

/--
Given a profunctor `P : Cᵒᵖ ⥤ C ⥤ D`, compose with the forgetful functor
and equivalence to get a functor from `CoTwistedArrow C` to `D`.

For a co-twisted arrow with `coTwDom = a` and `coTwCod = b`, this evaluates to
`(P.obj (op a)).obj b`. The dom/cod are swapped relative to the arrow direction
because of how the equivalence and braiding compose.
-/
def profunctorOnCoTwistedArrow (P : Cᵒᵖ ⥤ C ⥤ D) : CoTwistedArrow C ⥤ D :=
  coTwistedArrowForget ⋙ coTwistedArrowProdEquiv.functor ⋙ Functor.uncurry.obj P

@[simp]
theorem profunctorOnCoTwistedArrow_obj (P : Cᵒᵖ ⥤ C ⥤ D) (tw : CoTwistedArrow C) :
    (profunctorOnCoTwistedArrow P).obj tw =
    (P.obj (Opposite.op (coTwDom tw))).obj (coTwCod tw) := rfl

/--
The functor map formula for `profunctorOnCoTwistedArrow`.

For a morphism `m : x ⟶ y` in `CoTwistedArrow C`, the profunctor functor maps it
to the composition of the contravariant action (via `coTwDomArr`) followed by
the covariant action (via `coTwCodArr`).
-/
theorem profunctorOnCoTwistedArrow_map (P : Cᵒᵖ ⥤ C ⥤ D)
    {x y : CoTwistedArrow C} (m : x ⟶ y) :
    (profunctorOnCoTwistedArrow P).map m =
    (P.map (coTwDomArr m).op).app (coTwCod x) ≫
    (P.obj (Opposite.op (coTwDom y))).map (coTwCodArr m) := rfl

/--
Convert a cocone over `profunctorOnCoTwistedArrow P` to component morphisms
indexed by objects of `C` (the diagonal components).
-/
def coconeToCoWedgeComponents (P : Cᵒᵖ ⥤ C ⥤ D)
    (c : Cocone (profunctorOnCoTwistedArrow P)) (j : C) :
    (P.obj (Opposite.op j)).obj j ⟶ c.pt :=
  c.ι.app (coTwObjMk (𝟙 j))

/--
The functor map from a general arrow to the domain identity via contravariant.

For `f : i ⟶ j`, there is a morphism in `CoTwistedArrow` from `coTwObjMk f`
to `coTwObjMk (𝟙 i)`, and the profunctor functor maps this via the
contravariant action: `(P.map f.op).app i : P(j, i) → P(i, i)`.
-/
theorem profunctorOnCoTwistedArrow_map_to_dom (P : Cᵒᵖ ⥤ C ⥤ D)
    {i j : C} (f : i ⟶ j) :
    let morph_to_i : coTwObjMk f ⟶ coTwObjMk (𝟙 i) := coTwHomMk
      (domArr := f) (codArr := 𝟙 i)
      (by simp [Category.id_comp])
    (profunctorOnCoTwistedArrow P).map morph_to_i =
      (P.map f.op).app i := by
  intro morph_to_i
  rw [profunctorOnCoTwistedArrow_map]
  simp only [morph_to_i, coTwDomArr_coTwHomMk, coTwCodArr_coTwHomMk,
    coTwObjMk_cod, coTwObjMk_dom, Functor.map_id, Category.comp_id]

/--
The functor map from a general arrow to the codomain identity via covariant.

For `f : i ⟶ j`, there is a morphism in `CoTwistedArrow` from `coTwObjMk f`
to `coTwObjMk (𝟙 j)`, and the profunctor functor maps this via the
covariant action: `(P.obj (op j)).map f : P(j, i) → P(j, j)`.
-/
theorem profunctorOnCoTwistedArrow_map_to_cod (P : Cᵒᵖ ⥤ C ⥤ D)
    {i j : C} (f : i ⟶ j) :
    let morph_to_j : coTwObjMk f ⟶ coTwObjMk (𝟙 j) := coTwHomMk
      (domArr := 𝟙 j) (codArr := f)
      (by simp [Category.comp_id])
    (profunctorOnCoTwistedArrow P).map morph_to_j =
      (P.obj (Opposite.op j)).map f := by
  intro morph_to_j
  rw [profunctorOnCoTwistedArrow_map]
  simp only [morph_to_j, coTwDomArr_coTwHomMk, coTwCodArr_coTwHomMk,
    coTwObjMk_cod, coTwObjMk_dom, op_id, Functor.map_id, NatTrans.id_app,
    Category.id_comp]

/--
Factorization: the off-diagonal cocone morphism at `f : i ⟶ j` factors
through the diagonal component at `i` via the contravariant profunctor action.
-/
theorem coconeComponent_factorization_dom (P : Cᵒᵖ ⥤ C ⥤ D)
    (c : Cocone (profunctorOnCoTwistedArrow P)) {i j : C} (f : i ⟶ j) :
    let morph : coTwObjMk f ⟶ coTwObjMk (𝟙 i) :=
      coTwHomMk (domArr := f) (codArr := 𝟙 i) (by simp [Category.id_comp])
    c.ι.app (coTwObjMk f) =
    (profunctorOnCoTwistedArrow P).map morph ≫ c.ι.app (coTwObjMk (𝟙 i)) := by
  intro morph
  exact (c.w morph).symm

/--
Factorization: the off-diagonal cocone morphism at `f : i ⟶ j` factors
through the diagonal component at `j` via the covariant profunctor action.
-/
theorem coconeComponent_factorization_cod (P : Cᵒᵖ ⥤ C ⥤ D)
    (c : Cocone (profunctorOnCoTwistedArrow P)) {i j : C} (f : i ⟶ j) :
    let morph : coTwObjMk f ⟶ coTwObjMk (𝟙 j) :=
      coTwHomMk (domArr := 𝟙 j) (codArr := f) (by simp [Category.comp_id])
    c.ι.app (coTwObjMk f) =
    (profunctorOnCoTwistedArrow P).map morph ≫ c.ι.app (coTwObjMk (𝟙 j)) := by
  intro morph
  exact (c.w morph).symm

/--
The cowedge condition holds for cocone components.

Given `f : i ⟶ j` in `C`, the two paths from `P(j, i)` to `c.pt` are equal:
`(P.map f.op).app i ≫ coconeToCoWedgeComponents P c i =
 (P.obj (op j)).map f ≫ coconeToCoWedgeComponents P c j`

This is the standard cowedge/coend condition.
-/
theorem coconeToCoWedge_condition (P : Cᵒᵖ ⥤ C ⥤ D)
    (c : Cocone (profunctorOnCoTwistedArrow P)) {i j : C} (f : i ⟶ j) :
    (P.map f.op).app i ≫ coconeToCoWedgeComponents P c i =
    (P.obj (Opposite.op j)).map f ≫ coconeToCoWedgeComponents P c j := by
  unfold coconeToCoWedgeComponents
  -- Both sides equal c.ι.app (coTwObjMk f) by the factorization lemmas
  have fact_i := coconeComponent_factorization_dom P c f
  have fact_j := coconeComponent_factorization_cod P c f
  -- Eliminate the let bindings in fact_i and fact_j
  simp only [] at fact_i fact_j
  -- Now rewrite the functor maps using our lemmas
  rw [profunctorOnCoTwistedArrow_map_to_dom] at fact_i
  rw [profunctorOnCoTwistedArrow_map_to_cod] at fact_j
  exact fact_i.symm.trans fact_j

end CowedgeAsCocone

section WeightedLimitColimit

/-!
## Weighted limits and colimits

Weighted limits generalize ordinary limits by adding a "weight" functor
that specifies how much each object contributes to the limit.

For a weight `W : Jᵒᵖ ⥤ Type` and diagram `F : J ⥤ C`, the weighted limit
`{W, F}` is characterized by the universal property:
`Hom(X, {W, F}) ≅ Nat(W, Hom(X, F-))`

Ends and coends are weighted limits/colimits where:
- The end `∫_j F(j,j)` is the weighted limit with `W = Hom(-,-)` (the hom
  profunctor)
- The coend `∫^j F(j,j)` is the weighted colimit with `W = Hom(-,-)`

The relationship to twisted arrow categories:
- Weighted limits can be computed as ordinary limits over the category of
  elements of the weight
- For ends, this category of elements is the twisted arrow category
-/

end WeightedLimitColimit

end GebLean
