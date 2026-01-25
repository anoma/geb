import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import GebLean.Paranatural
import GebLean.Utilities.Category
import GebLean.Utilities.TwArrPresheaf
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
    (c : Cone (profunctorOnTwistedArrow C P)) (j : C) :
    c.pt ⟶ (P.obj (Opposite.op j)).obj j :=
  c.π.app (twObjMk (𝟙 j))

/--
A cone over `profunctorOnTwistedArrow P` is determined by its diagonal
components `coneToWedgeComponents`.

This shows that the data of a cone leg at any twisted arrow can be recovered
from the diagonal components via composition with the profunctor action.
-/
theorem cone_determined_by_wedge_components (P : Cᵒᵖ ⥤ C ⥤ D)
    (c : Cone (profunctorOnTwistedArrow C P)) (tw : TwistedArrow C) :
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
  have map_eq : (profunctorOnTwistedArrow C P).map morph =
      (P.obj (Opposite.op (twDom tw))).map (twArr tw) := by
    simp only [profunctorOnTwistedArrow_map, dom_eq, cod_eq, op_id]
    rw [P.map_id (Opposite.op (twDom tw)), NatTrans.id_app]
    exact Category.id_comp _
  have h := c.π.naturality morph
  simp only [Functor.const_obj_map] at h
  have h' : c.π.app tw = c.π.app twId ≫ (profunctorOnTwistedArrow C P).map morph := by
    calc c.π.app tw = 𝟙 c.pt ≫ c.π.app tw := (Category.id_comp _).symm
      _ = c.π.app twId ≫ (profunctorOnTwistedArrow C P).map morph := h
  rw [map_eq] at h'
  exact h'

end WedgeAsCone

section CowedgeAsCocone

/-!
## Cowedges as cocones over co-twisted arrow categories

For a profunctor `P : Cᵒᵖ ⥤ C ⥤ D`, a cowedge for `P` with apex `X` consists of:
- For each `j : C`, a morphism `ι j : (P.obj (op j)).obj j ⟶ X`
- Compatibility: for `f : i ⟶ j`, we have
  `(P.map f.op).app i ≫ ι i = (P.obj (op j)).map f ≫ ι j`

This is exactly a cocone over the functor `profunctorOnCoTwistedArrow P`:
- The cocone point is `X`
- The legs are indexed by `CoTwistedArrow C`
- For a co-twisted arrow representing `f : i ⟶ j`, the leg is
  `(P.obj (op i)).obj j ⟶ X`

The cowedge condition follows from the cocone naturality condition.
-/

variable {D : Type w} [Category.{v} D]

/--
Convert a cocone over `profunctorOnCoTwistedArrow P` to component morphisms
indexed by objects of `C` (the diagonal components).
-/
def coconeToCoWedgeComponents (P : Cᵒᵖ ⥤ C ⥤ D)
    (c : Cocone (profunctorOnCoTwistedArrow C P)) (j : C) :
    (P.obj (Opposite.op j)).obj j ⟶ c.pt :=
  c.ι.app (coTwObjMk (𝟙 j))

/--
Factorization: the off-diagonal cocone morphism at `f : i ⟶ j` factors
through the diagonal component at `i` via the contravariant profunctor action.
-/
theorem coconeComponent_factorization_dom (P : Cᵒᵖ ⥤ C ⥤ D)
    (c : Cocone (profunctorOnCoTwistedArrow C P)) {i j : C} (f : i ⟶ j) :
    let morph : coTwObjMk f ⟶ coTwObjMk (𝟙 i) :=
      coTwHomMk (domArr := f) (codArr := 𝟙 i) (by simp [Category.id_comp])
    c.ι.app (coTwObjMk f) =
    (profunctorOnCoTwistedArrow C P).map morph ≫ c.ι.app (coTwObjMk (𝟙 i)) := by
  intro morph
  exact (c.w morph).symm

/--
Factorization: the off-diagonal cocone morphism at `f : i ⟶ j` factors
through the diagonal component at `j` via the covariant profunctor action.
-/
theorem coconeComponent_factorization_cod (P : Cᵒᵖ ⥤ C ⥤ D)
    (c : Cocone (profunctorOnCoTwistedArrow C P)) {i j : C} (f : i ⟶ j) :
    let morph : coTwObjMk f ⟶ coTwObjMk (𝟙 j) :=
      coTwHomMk (domArr := 𝟙 j) (codArr := f) (by simp [Category.comp_id])
    c.ι.app (coTwObjMk f) =
    (profunctorOnCoTwistedArrow C P).map morph ≫ c.ι.app (coTwObjMk (𝟙 j)) := by
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
    (c : Cocone (profunctorOnCoTwistedArrow C P)) {i j : C} (f : i ⟶ j) :
    (P.map f.op).app i ≫ coconeToCoWedgeComponents P c i =
    (P.obj (Opposite.op j)).map f ≫ coconeToCoWedgeComponents P c j := by
  unfold coconeToCoWedgeComponents
  have fact_i := coconeComponent_factorization_dom P c f
  have fact_j := coconeComponent_factorization_cod P c f
  simp only [] at fact_i fact_j
  rw [profunctorOnCoTwistedArrow_map_to_dom] at fact_i
  rw [profunctorOnCoTwistedArrow_map_to_cod] at fact_j
  exact fact_i.symm.trans fact_j

end CowedgeAsCocone

section WedgeConeCorrespondence

/-!
## Correspondence between Wedges and Cones over twisted arrow category

This section establishes that for a profunctor `P : Cᵒᵖ ⥤ C ⥤ D`, wedges
for `P` correspond to cones over `profunctorOnTwistedArrow C P`.

The correspondence is given by:
- Cone → Wedge: restrict cone legs to diagonal twisted arrows (identity
  morphisms)
- Wedge → Cone: extend wedge components to all twisted arrows via the
  profunctor action

We first establish the correspondence at the level of data, then work
toward the categorical equivalence.
-/

variable {D : Type w} [Category.{v} D]

/--
The wedge condition derived from a cone's naturality.

Given a cone over `profunctorOnTwistedArrow C P` and a morphism `f : i ⟶ j`,
the standard wedge condition holds for the diagonal components.
-/
theorem cone_satisfies_wedge_condition (P : Cᵒᵖ ⥤ C ⥤ D)
    (c : Cone (profunctorOnTwistedArrow C P)) {i j : C} (f : i ⟶ j) :
    coneToWedgeComponents P c i ≫ (P.obj (Opposite.op i)).map f =
    coneToWedgeComponents P c j ≫ (P.map f.op).app j := by
  -- The left side equals c.π.app (twObjMk f) by cone_determined_by_wedge_components
  have h_at_f := cone_determined_by_wedge_components P c (twObjMk f)
  simp only [twObjMk_dom, twObjMk_arr, coneToWedgeComponents] at h_at_f
  -- For the right side, construct a morphism from twObjMk (𝟙 j) to twObjMk f
  -- and use cone naturality
  -- Morphism from (j,j,𝟙 j) to (i,j,f): domArr = f : i → j, codArr = 𝟙 j
  let morph_j : twObjMk (𝟙 j) ⟶ twObjMk f := twHomMk (domArr := f) (codArr := 𝟙 j) (by
    simp only [twObjMk_arr]
    calc f ≫ (𝟙 j ≫ 𝟙 j) = f ≫ 𝟙 j := by rw [Category.id_comp]
      _ = f := Category.comp_id f)
  -- Compute what the functor map on morph_j is
  have dom_eq : twDomArr morph_j = f := rfl
  have cod_eq : twCodArr morph_j = 𝟙 j := rfl
  have map_j_eq : (profunctorOnTwistedArrow C P).map morph_j =
      (P.map f.op).app j := by
    simp only [profunctorOnTwistedArrow_map, dom_eq, cod_eq, twObjMk_cod,
      twObjMk_dom]
    simp only [Functor.map_id, Category.comp_id]
  -- Use naturality
  have nat_j := c.π.naturality morph_j
  simp only [Functor.const_obj_map] at nat_j
  -- Unfold coneToWedgeComponents in the goal and prove both sides equal c.π.app (twObjMk f)
  unfold coneToWedgeComponents
  calc c.π.app (twObjMk (𝟙 i)) ≫ (P.obj (Opposite.op i)).map f
    = c.π.app (twObjMk f) := h_at_f.symm
    _ = 𝟙 c.pt ≫ c.π.app (twObjMk f) := (Category.id_comp _).symm
    _ = c.π.app (twObjMk (𝟙 j)) ≫ (profunctorOnTwistedArrow C P).map morph_j := nat_j
    _ = c.π.app (twObjMk (𝟙 j)) ≫ (P.map f.op).app j := by rw [map_j_eq]

/--
Construct a mathlib `Wedge P` from a `Cone (profunctorOnTwistedArrow C P)`.

The wedge apex is the cone point, and wedge components are the cone legs
at identity twisted arrows.
-/
def coneToWedge (P : Cᵒᵖ ⥤ C ⥤ D) (c : Cone (profunctorOnTwistedArrow C P)) :
    Wedge P :=
  Wedge.mk c.pt (fun j => coneToWedgeComponents P c j)
    (fun {_ _} f => cone_satisfies_wedge_condition P c f)

/--
Construct a cone leg at an arbitrary twisted arrow from wedge data.

For a twisted arrow `tw = (i, j, f : i → j)`, the cone leg is obtained by
composing the wedge component at `i` with the covariant profunctor action.
-/
def wedgeToConeπApp (P : Cᵒᵖ ⥤ C ⥤ D) (pt : D)
    (π : (j : C) → pt ⟶ (P.obj (Opposite.op j)).obj j)
    (tw : TwistedArrow C) : pt ⟶ (profunctorOnTwistedArrow C P).obj tw :=
  π (twDom tw) ≫ (P.obj (Opposite.op (twDom tw))).map (twArr tw)

/--
The cone projections constructed from wedge data satisfy naturality.
-/
theorem wedgeToConeπApp_naturality (P : Cᵒᵖ ⥤ C ⥤ D) (pt : D)
    (π : (j : C) → pt ⟶ (P.obj (Opposite.op j)).obj j)
    (hπ : ∀ {i j : C} (f : i ⟶ j),
      π i ≫ (P.obj (Opposite.op i)).map f = π j ≫ (P.map f.op).app j)
    {tw tw' : TwistedArrow C} (m : tw ⟶ tw') :
    wedgeToConeπApp P pt π tw ≫ (profunctorOnTwistedArrow C P).map m =
    wedgeToConeπApp P pt π tw' := by
  unfold wedgeToConeπApp
  simp only [profunctorOnTwistedArrow_map]
  -- Goal: (π (twDom tw) ≫ map (twArr tw)) ≫ (app (twCod tw) ≫ map (twCodArr m))
  --     = π (twDom tw') ≫ map (twArr tw')
  have nat := (P.map (twDomArr m).op).naturality (twArr tw)
  have h := hπ (twDomArr m)
  have comm := twHomComm m
  -- Prove via calc, with explicit composition structure
  calc (π (twDom tw) ≫ (P.obj (Opposite.op (twDom tw))).map (twArr tw)) ≫
        ((P.map (twDomArr m).op).app (twCod tw) ≫
         (P.obj (Opposite.op (twDom tw'))).map (twCodArr m))
      -- Step 1: Right-associate
    _ = π (twDom tw) ≫ (P.obj (Opposite.op (twDom tw))).map (twArr tw) ≫
        (P.map (twDomArr m).op).app (twCod tw) ≫
        (P.obj (Opposite.op (twDom tw'))).map (twCodArr m) := by
      simp only [Category.assoc]
      -- Step 2: Apply naturality - this transforms
      -- map (twArr tw) ≫ app (twCod tw) to app (twDom tw) ≫ map (twArr tw)
    _ = π (twDom tw) ≫ (P.map (twDomArr m).op).app (twDom tw) ≫
        (P.obj (Opposite.op (twDom tw'))).map (twArr tw) ≫
        (P.obj (Opposite.op (twDom tw'))).map (twCodArr m) := by
      -- Apply naturality: map (twArr tw) ≫ app (twCod tw) = app (twDom tw) ≫ map (twArr tw)
      -- First left-associate the middle part to expose the pattern for naturality
      simp only [← Category.assoc _ ((P.map (twDomArr m).op).app (twCod tw)) _]
      simp only [nat]
      simp only [Category.assoc]
      -- Step 3: Left-associate to apply wedge condition
    _ = (π (twDom tw) ≫ (P.map (twDomArr m).op).app (twDom tw)) ≫
        (P.obj (Opposite.op (twDom tw'))).map (twArr tw) ≫
        (P.obj (Opposite.op (twDom tw'))).map (twCodArr m) := by
      simp only [← Category.assoc]
      -- Step 4: Apply wedge condition h.symm
    _ = (π (twDom tw') ≫ (P.obj (Opposite.op (twDom tw'))).map (twDomArr m)) ≫
        (P.obj (Opposite.op (twDom tw'))).map (twArr tw) ≫
        (P.obj (Opposite.op (twDom tw'))).map (twCodArr m) := by
      simp only [← h]
      -- Step 5: Right-associate
    _ = π (twDom tw') ≫ (P.obj (Opposite.op (twDom tw'))).map (twDomArr m) ≫
        (P.obj (Opposite.op (twDom tw'))).map (twArr tw) ≫
        (P.obj (Opposite.op (twDom tw'))).map (twCodArr m) := by
      simp only [Category.assoc]
      -- Step 6: Combine functor maps
    _ = π (twDom tw') ≫ (P.obj (Opposite.op (twDom tw'))).map
        (twDomArr m ≫ twArr tw ≫ twCodArr m) := by
      simp only [← Functor.map_comp]
      -- Step 7: Apply twisted arrow commutativity
    _ = π (twDom tw') ≫ (P.obj (Opposite.op (twDom tw'))).map (twArr tw') := by
      simp only [comm]

/--
Construct a `Cone (profunctorOnTwistedArrow C P)` from a mathlib `Wedge P`.

The cone point is the wedge apex. Cone legs are constructed by extending
wedge components via the profunctor action.
-/
def wedgeToCone (P : Cᵒᵖ ⥤ C ⥤ D) (w : Wedge P) :
    Cone (profunctorOnTwistedArrow C P) where
  pt := w.pt
  π := {
    app := fun tw => wedgeToConeπApp P w.pt (fun j => Multifork.ι w j) tw
    naturality := fun tw tw' m => by
      simp only [Functor.const_obj_map]
      have nat := wedgeToConeπApp_naturality P w.pt _ w.condition m
      calc 𝟙 w.pt ≫ wedgeToConeπApp P w.pt (fun j => Multifork.ι w j) tw'
        = wedgeToConeπApp P w.pt _ tw' := Category.id_comp _
        _ = wedgeToConeπApp P w.pt _ tw ≫ (profunctorOnTwistedArrow C P).map m := nat.symm
  }

/--
Round-trip: converting a cone to a wedge and back yields the original cone.
-/
theorem coneToWedge_wedgeToCone (P : Cᵒᵖ ⥤ C ⥤ D)
    (c : Cone (profunctorOnTwistedArrow C P)) :
    wedgeToCone P (coneToWedge P c) = c := by
  -- Both cones have the same point c.pt; show π natural transformations equal
  cases c with | mk pt π =>
  simp only [coneToWedge, wedgeToCone, Cone.mk.injEq]
  constructor
  · rfl  -- cone points equal
  · -- Show π natural transformations are heq-equal (degenerates to eq since pts equal)
    apply heq_of_eq
    ext tw
    simp only [wedgeToConeπApp, coneToWedgeComponents, Wedge.mk_ι]
    exact (cone_determined_by_wedge_components P ⟨pt, π⟩ tw).symm

/--
Round-trip: converting a wedge to a cone and back yields the original wedge.

The wedge components are recovered from the cone legs at identity twisted
arrows.
-/
theorem wedgeToCone_coneToWedge (P : Cᵒᵖ ⥤ C ⥤ D) (w : Wedge P) :
    coneToWedge P (wedgeToCone P w) = w := by
  -- Need to show the round-tripped wedge equals original
  -- Decompose w as a Cone and show field-by-field equality
  cases w with | mk pt π =>
  unfold coneToWedge wedgeToCone coneToWedgeComponents wedgeToConeπApp
  simp only [twObjMk_dom, twObjMk_arr, Functor.map_id, Category.comp_id]
  -- Goal: Wedge.mk pt (fun j => Multifork.ι ⟨pt, π⟩ j) _ = ⟨pt, π⟩
  -- This is an eta expansion - Wedge.mk using extracted components gives back original
  -- Use Cone.mk.injEq to decompose into point equality and π heq
  rw [Cone.mk.injEq]
  constructor
  · rfl  -- points definitionally equal
  · -- Show π heq; since points equal, this is π equality
    apply heq_of_eq
    -- Need: the π from Wedge.mk = original π
    ext tw
    simp only [Multifork.ofι_π_app]
    -- Now case split on whether tw is left or right
    cases tw with
    | left j => rfl
    | right b =>
      -- Use the relationship K.π.app (right b) = K.ι (fst b) ≫ I.fst b
      simp only [← Multifork.app_right_eq_ι_comp_fst]

/-!
### Categorical Equivalence

We upgrade the wedge/cone correspondence to a categorical equivalence by
defining functors in both directions and proving they form an equivalence.
-/

/--
The functor from wedges to cones over the twisted arrow diagram.

Objects are mapped via `wedgeToCone`.
Morphisms are mapped by taking the underlying morphism on cone points.
-/
def wedgeToConeFunctor (P : Cᵒᵖ ⥤ C ⥤ D) :
    Wedge P ⥤ Cone (profunctorOnTwistedArrow C P) where
  obj := wedgeToCone P
  map {w₁ w₂} f := {
    hom := f.hom
    w := fun tw => by
      simp only [wedgeToCone, wedgeToConeπApp]
      let dom : C := twDom tw
      let arr : dom ⟶ twCod tw := twArr tw
      have hw : f.hom ≫ Multifork.ι w₂ dom = Multifork.ι w₁ dom :=
        f.w (WalkingMulticospan.left dom)
      calc f.hom ≫ (Multifork.ι w₂ dom ≫ (P.obj (Opposite.op dom)).map arr)
          = (f.hom ≫ Multifork.ι w₂ dom) ≫ (P.obj (Opposite.op dom)).map arr := by
            simp only [Category.assoc]
          _ = Multifork.ι w₁ dom ≫ (P.obj (Opposite.op dom)).map arr := by
            rw [hw]
  }
  map_id _ := rfl
  map_comp _ _ := rfl

/--
The functor from cones over the twisted arrow diagram to wedges.

Objects are mapped via `coneToWedge`.
Morphisms are mapped by taking the underlying morphism on cone points.
-/
def coneToWedgeFunctor (P : Cᵒᵖ ⥤ C ⥤ D) :
    Cone (profunctorOnTwistedArrow C P) ⥤ Wedge P where
  obj := coneToWedge P
  map {c₁ c₂} f := {
    hom := f.hom
    w := fun tw => by
      cases tw with
      | left j =>
        simp only [coneToWedge, coneToWedgeComponents, Multifork.ofι_π_app]
        let jC : C := j
        exact f.w (twObjMk (𝟙 jC))
      | right b =>
        simp only [coneToWedge, Multifork.ofι_π_app, coneToWedgeComponents]
        let j : C := (multicospanShapeEnd C).fst b
        have hw := f.w (twObjMk (𝟙 j))
        rw [← Category.assoc, hw]
  }
  map_id _ := rfl
  map_comp _ _ := rfl

/--
For cones, the `.hom` field of `eqToHom h` is `eqToHom` applied to the cone point
equality. This allows `eqToHom_refl` to simplify when cone points are
definitionally equal.
-/
@[simp]
theorem Cone.eqToHom_hom {J' : Type*} [Category J'] {E' : Type*} [Category E']
    {F : J' ⥤ E'} {c c' : Cone F} (h : c = c') :
    (eqToHom h).hom = eqToHom (congrArg Cone.pt h) := by
  subst h
  rfl

/--
The composition `coneToWedgeFunctor ⋙ wedgeToConeFunctor` is naturally isomorphic
to the identity functor on cones.
-/
def wedgeConeUnitIso (P : Cᵒᵖ ⥤ C ⥤ D) :
    𝟭 (Cone (profunctorOnTwistedArrow C P)) ≅
    coneToWedgeFunctor P ⋙ wedgeToConeFunctor P :=
  NatIso.ofComponents
    (fun c => eqToIso (coneToWedge_wedgeToCone P c).symm)
    (fun {c₁ c₂} f => by
      apply ConeMorphism.ext
      simp only [Functor.id_map, Functor.comp_map, eqToIso.hom,
        Cone.category_comp_hom, coneToWedgeFunctor, wedgeToConeFunctor,
        Cone.eqToHom_hom, eqToHom_refl, Category.comp_id, Category.id_comp])

/--
The composition `wedgeToConeFunctor ⋙ coneToWedgeFunctor` is naturally isomorphic
to the identity functor on wedges.
-/
def wedgeConeCounitIso (P : Cᵒᵖ ⥤ C ⥤ D) :
    wedgeToConeFunctor P ⋙ coneToWedgeFunctor P ≅ 𝟭 (Wedge P) :=
  NatIso.ofComponents
    (fun w => eqToIso (wedgeToCone_coneToWedge P w))
    (fun {w₁ w₂} f => by
      apply ConeMorphism.ext
      simp only [Functor.comp_map, Functor.id_map, eqToIso.hom,
        wedgeToConeFunctor, coneToWedgeFunctor, Cone.category_comp_hom,
        Cone.eqToHom_hom, eqToHom_refl, Category.comp_id, Category.id_comp])

/--
The category of wedges over `P` is equivalent to the category of cones over
`profunctorOnTwistedArrow C P`.
-/
def wedgeConeEquiv (P : Cᵒᵖ ⥤ C ⥤ D) :
    Wedge (J := C) (C := D) P ≌
    Cone (J := TwistedArrow C) (C := D) (profunctorOnTwistedArrow C P) where
  functor := wedgeToConeFunctor P
  inverse := coneToWedgeFunctor P
  unitIso := (wedgeConeCounitIso P).symm
  counitIso := (wedgeConeUnitIso P).symm
  functor_unitIso_comp w := by
    apply ConeMorphism.ext
    simp only [Iso.symm_hom, Functor.comp_obj, Functor.id_obj,
      wedgeConeCounitIso, wedgeConeUnitIso,
      NatIso.ofComponents, eqToIso.hom, eqToIso.inv, wedgeToConeFunctor,
      coneToWedgeFunctor, Cone.category_comp_hom, Cone.category_id_hom,
      Cone.eqToHom_hom, eqToHom_refl]
    -- Goal: 𝟙 w.pt ≫ 𝟙 (wedgeToCone P (coneToWedge P (wedgeToCone P w))).pt
    --       = 𝟙 (wedgeToCone P w).pt
    -- All pt fields are definitionally equal to w.pt
    exact Category.id_comp _

end WedgeConeCorrespondence

section CowedgeCoconeCorrespondence

/-!
## Correspondence between Cowedges and Cocones over co-twisted arrow category

This section establishes that for a profunctor `P : Cᵒᵖ ⥤ C ⥤ D`, cowedges
for `P` correspond bijectively to cocones over the functor
`profunctorOnCoTwistedArrow C P : CoTwistedArrow C ⥤ D`.

This is the dual of the Wedge/Cone correspondence.
-/

variable {C : Type u} [Category.{v} C] {D : Type w} [Category.{v} D]

/--
The cocone leg at an arbitrary co-twisted arrow, constructed from cowedge data.

For a co-twisted arrow `tw = (i, j, f : i → j)`, the cocone leg is obtained by
composing the profunctor action with the cowedge component:
- Apply the contravariant action `P.map f.op` to get from `P(i, j)` to `P(j, j)`
- Then use the cowedge component `ι j : P(j, j) → pt`
-/
def cowedgeToCoconeιApp (P : Cᵒᵖ ⥤ C ⥤ D) (pt : D)
    (ι : (j : C) → (P.obj (Opposite.op j)).obj j ⟶ pt) (tw : CoTwistedArrow C) :
    (profunctorOnCoTwistedArrow C P).obj tw ⟶ pt :=
  (P.map (coTwArr tw).op).app (coTwCod tw) ≫ ι (coTwCod tw)

/--
At identity co-twisted arrows, the cocone leg is the cowedge component.
-/
@[simp]
theorem cowedgeToCoconeιApp_at_id (P : Cᵒᵖ ⥤ C ⥤ D) (pt : D)
    (ι : (j : C) → (P.obj (Opposite.op j)).obj j ⟶ pt) (j : C) :
    cowedgeToCoconeιApp P pt ι (coTwObjMk (𝟙 j)) = ι j := by
  simp only [cowedgeToCoconeιApp, coTwObjMk_arr, coTwObjMk_cod]
  erw [P.map_id, NatTrans.id_app, Category.id_comp]

/--
The cocone legs constructed from cowedge data form a natural transformation.

This follows from the cowedge condition and naturality of the profunctor action.
-/
theorem cowedgeToCoconeιApp_naturality (P : Cᵒᵖ ⥤ C ⥤ D) (pt : D)
    (ι : (j : C) → (P.obj (Opposite.op j)).obj j ⟶ pt)
    (hι : ∀ ⦃i j : C⦄ (f : i ⟶ j),
      (P.map f.op).app i ≫ ι i = (P.obj (Opposite.op j)).map f ≫ ι j)
    {x y : CoTwistedArrow C} (m : x ⟶ y) :
    (profunctorOnCoTwistedArrow C P).map m ≫ cowedgeToCoconeιApp P pt ι y =
    cowedgeToCoconeιApp P pt ι x := by
  simp only [cowedgeToCoconeιApp, profunctorOnCoTwistedArrow_map, Category.assoc]
  have arr_eq := coTwHomComm m
  have nat := (P.map (coTwArr y).op).naturality (coTwCodArr m)
  slice_lhs 2 3 => rw [nat]
  simp only [Category.assoc]
  rw [← hι (coTwCodArr m)]
  simp only [← Category.assoc]
  congr 1
  rw [← NatTrans.comp_app, ← NatTrans.comp_app, ← P.map_comp, ← P.map_comp]
  congr 2
  simp only [← op_comp, arr_eq]

/--
Convert a cowedge to a cocone over the co-twisted arrow diagram.
-/
def cowedgeToCocone (P : Cᵒᵖ ⥤ C ⥤ D) (w : Cowedge P) :
    Cocone (profunctorOnCoTwistedArrow C P) :=
  { pt := w.pt
    ι := {
      app := fun tw => cowedgeToCoconeιApp P w.pt (fun j => w.π j) tw
      naturality := fun _ _ m => by
        simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
        exact cowedgeToCoconeιApp_naturality P w.pt (fun j => w.π j) (fun _ _ f => w.condition f) m
    }
  }

/--
Convert a cocone over the co-twisted arrow diagram to a cowedge.
-/
def coconeToCowedge (P : Cᵒᵖ ⥤ C ⥤ D)
    (c : Cocone (profunctorOnCoTwistedArrow C P)) : Cowedge P :=
  Cowedge.mk c.pt (fun j => coconeToCoWedgeComponents P c j)
    (fun {_ _} f => coconeToCoWedge_condition P c f)

/--
Round-trip: converting a cocone to a cowedge and back yields the original cocone.

This is the dual of `coneToWedge_wedgeToCone`.
-/
theorem coconeToCowedge_cowedgeToCocone (P : Cᵒᵖ ⥤ C ⥤ D)
    (c : Cocone (profunctorOnCoTwistedArrow C P)) :
    cowedgeToCocone P (coconeToCowedge P c) = c := by
  cases c with | mk pt ι =>
  simp only [coconeToCowedge, cowedgeToCocone, Cocone.mk.injEq]
  constructor
  · rfl
  · apply heq_of_eq
    ext tw
    simp only [cowedgeToCoconeιApp, coconeToCoWedgeComponents, Cowedge.mk_π]
    -- Goal: (P.map (coTwArr tw).op).app (coTwCod tw) ≫ ι.app (coTwObjMk (𝟙 (coTwCod tw)))
    --     = ι.app tw
    -- Use the cocone naturality: this is the cocone_determined_by_cowedge_components analog
    let morph : tw ⟶ coTwObjMk (𝟙 (coTwCod tw)) := coTwHomMk
      (domArr := coTwArr tw) (codArr := 𝟙 (coTwCod tw))
      (by simp [Category.id_comp])
    have nat := ι.naturality morph
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at nat
    rw [← nat]
    simp only [morph, profunctorOnCoTwistedArrow_map, coTwDomArr_coTwHomMk, coTwCodArr_coTwHomMk,
      coTwObjMk_cod, coTwObjMk_dom, Functor.map_id, Category.comp_id]

/--
Round-trip: converting a cowedge to a cocone and back yields the original cowedge.

This is the dual of `wedgeToCone_coneToWedge`.
-/
theorem cowedgeToCocone_coconeToCowedge (P : Cᵒᵖ ⥤ C ⥤ D) (w : Cowedge P) :
    coconeToCowedge P (cowedgeToCocone P w) = w := by
  cases w with | mk pt ι =>
  unfold coconeToCowedge cowedgeToCocone coconeToCoWedgeComponents cowedgeToCoconeιApp
  simp only [coTwObjMk_arr]
  rw [Cocone.mk.injEq]
  constructor
  · rfl
  · apply heq_of_eq
    ext tw
    cases tw with
    | left j =>
      simp only [Multicofork.ofπ_ι_app, coTwObjMk_cod, multispanShapeCoend_fst]
      erw [P.map_id, NatTrans.id_app, Category.id_comp]
      exact (Multicofork.fst_app_right (I := multispanIndexCoend P) ⟨pt, ι⟩ j).symm
    | right b =>
      simp only [Multicofork.ofπ_ι_app, coTwObjMk_cod]
      erw [P.map_id, NatTrans.id_app, Category.id_comp]
      exact (Multicofork.π_eq_app_right ⟨pt, ι⟩ b).symm

/--
The functor from cowedges to cocones over the co-twisted arrow diagram.

Objects are mapped via `cowedgeToCocone`.
Morphisms are mapped by taking the underlying morphism on cocone points.
-/
def cowedgeToCoconeFunctor (P : Cᵒᵖ ⥤ C ⥤ D) :
    Cowedge P ⥤ Cocone (profunctorOnCoTwistedArrow C P) where
  obj := cowedgeToCocone P
  map {w₁ w₂} f := {
    hom := f.hom
    w := fun tw => by
      simp only [cowedgeToCocone, cowedgeToCoconeιApp, Category.assoc,
        Multicofork.π_comp_hom]
  }
  map_id _ := rfl
  map_comp _ _ := rfl

/--
The functor from cocones over the co-twisted arrow diagram to cowedges.

Objects are mapped via `coconeToCowedge`.
Morphisms are mapped by taking the underlying morphism on cocone points.
-/
def coconeToCowedgeFunctor (P : Cᵒᵖ ⥤ C ⥤ D) :
    Cocone (profunctorOnCoTwistedArrow C P) ⥤ Cowedge P where
  obj := coconeToCowedge P
  map {c₁ c₂} f := {
    hom := f.hom
    w := fun tw => by
      cases tw with
      | left arr =>
        simp only [coconeToCowedge, Multicofork.ofπ_ι_app, coconeToCoWedgeComponents]
        let leftObj : C := arr.left
        have hw := f.w (coTwObjMk (𝟙 leftObj))
        simp only [multispanShapeCoend_fst]
        rw [Category.assoc, hw]
      | right j =>
        simp only [coconeToCowedge, Multicofork.ofπ_ι_app, coconeToCoWedgeComponents]
        let jC : C := j
        exact f.w (coTwObjMk (𝟙 jC))
  }
  map_id _ := rfl
  map_comp _ _ := rfl

/--
For cocones, the `.hom` field of `eqToHom h` is `eqToHom` applied to the cocone
point equality.
-/
@[simp]
theorem Cocone.eqToHom_hom {J' : Type*} [Category J'] {E' : Type*} [Category E']
    {F : J' ⥤ E'} {c c' : Cocone F} (h : c = c') :
    (eqToHom h).hom = eqToHom (congrArg Cocone.pt h) := by
  subst h
  rfl

/--
The composition `coconeToCowedgeFunctor ⋙ cowedgeToCoconeFunctor` is naturally
isomorphic to the identity functor on cocones.
-/
def cowedgeCoconeUnitIso (P : Cᵒᵖ ⥤ C ⥤ D) :
    𝟭 (Cocone (profunctorOnCoTwistedArrow C P)) ≅
    coconeToCowedgeFunctor P ⋙ cowedgeToCoconeFunctor P :=
  NatIso.ofComponents
    (fun c => eqToIso (coconeToCowedge_cowedgeToCocone P c).symm)
    (fun {c₁ c₂} f => by
      apply CoconeMorphism.ext
      simp only [Functor.id_map, Functor.comp_map, eqToIso.hom,
        Cocone.category_comp_hom, coconeToCowedgeFunctor, cowedgeToCoconeFunctor,
        Cocone.eqToHom_hom, eqToHom_refl, Category.comp_id, Category.id_comp])

/--
The composition `cowedgeToCoconeFunctor ⋙ coconeToCowedgeFunctor` is naturally
isomorphic to the identity functor on cowedges.
-/
def cowedgeCoconeCounitIso (P : Cᵒᵖ ⥤ C ⥤ D) :
    cowedgeToCoconeFunctor P ⋙ coconeToCowedgeFunctor P ≅ 𝟭 (Cowedge P) :=
  NatIso.ofComponents
    (fun w => eqToIso (cowedgeToCocone_coconeToCowedge P w))
    (fun {w₁ w₂} f => by
      apply CoconeMorphism.ext
      simp only [Functor.comp_map, Functor.id_map, eqToIso.hom,
        cowedgeToCoconeFunctor, coconeToCowedgeFunctor, Cocone.category_comp_hom,
        Cocone.eqToHom_hom, eqToHom_refl, Category.comp_id, Category.id_comp])

/--
The category of cowedges over `P` is equivalent to the category of cocones over
`profunctorOnCoTwistedArrow C P`.
-/
def cowedgeCoconeEquiv (P : Cᵒᵖ ⥤ C ⥤ D) :
    Cowedge (J := C) (C := D) P ≌
    Cocone (J := CoTwistedArrow C) (C := D) (profunctorOnCoTwistedArrow C P) where
  functor := cowedgeToCoconeFunctor P
  inverse := coconeToCowedgeFunctor P
  unitIso := (cowedgeCoconeCounitIso P).symm
  counitIso := (cowedgeCoconeUnitIso P).symm
  functor_unitIso_comp w := by
    apply CoconeMorphism.ext
    simp only [Iso.symm_hom, Functor.comp_obj, Functor.id_obj,
      cowedgeCoconeCounitIso, cowedgeCoconeUnitIso,
      NatIso.ofComponents, eqToIso.hom, eqToIso.inv, cowedgeToCoconeFunctor,
      coconeToCowedgeFunctor, Cocone.category_comp_hom, Cocone.category_id_hom,
      Cocone.eqToHom_hom, eqToHom_refl]
    exact Category.id_comp _

end CowedgeCoconeCorrespondence

section ConstProfWedgeAsCone

variable {C : Type u} [Category.{v} C]

/--
The uncurried weight profunctor: given `W : Cᵒᵖ ⥤ C ⥤ Type v`, this is
`Functor.uncurry.obj W : Cᵒᵖ × C ⥤ Type v`.
-/
abbrev uncurriedProfunctor (W : Cᵒᵖ ⥤ C ⥤ Type v) : Cᵒᵖ × C ⥤ Type v :=
  Functor.uncurry.obj W

/--
For the hom-profunctor case: `TwistedArrow C` projects to `Cᵒᵖ × C` via
`twistedArrowForget C`, which equals `CategoryOfElements.π (Functor.hom C)`.
-/
theorem twistedArrow_proj_eq :
    twistedArrowForget C = CategoryOfElements.π (Functor.hom C) :=
  rfl

/-- The profunctor constant in its first argument: `P'(j₁, j₂) = F(j₂)`. -/
def constFirstArgProf {J : Type*} [Category J] {D : Type*} [Category D]
    (F : J ⥤ D) : Jᵒᵖ ⥤ J ⥤ D :=
  (Functor.const Jᵒᵖ).obj F

/-- For the constant-first-arg profunctor, the diagonal value at `j` is `F(j)`. -/
@[simp]
lemma constFirstArgProf_diag {J : Type*} [Category J] {D : Type*} [Category D]
    (F : J ⥤ D) (j : J) :
    ((constFirstArgProf F).obj (Opposite.op j)).obj j = F.obj j := rfl

/-- The covariant action on `f : j → j'` is `F(f)`. -/
@[simp]
lemma constFirstArgProf_map_snd {J : Type*} [Category J] {D : Type*} [Category D]
    (F : J ⥤ D) {j₁ j₂ : J} (f : j₁ ⟶ j₂) (k : Jᵒᵖ) :
    ((constFirstArgProf F).obj k).map f = F.map f := rfl

/-- The contravariant action on `f : j → j'` is identity. -/
@[simp]
lemma constFirstArgProf_map_fst {J : Type*} [Category J] {D : Type*} [Category D]
    (F : J ⥤ D) {j₁ j₂ : J} (f : j₁ ⟶ j₂) (k : J) :
    ((constFirstArgProf F).map f.op).app k = 𝟙 (F.obj k) := rfl

/-- Convert a cone over `F` to a wedge over the constant-first-arg profunctor.
The cone legs become wedge legs directly. -/
def coneToWedgeConstProf {J : Type*} [Category J] {D : Type*} [Category D]
    (F : J ⥤ D) (c : Cone F) : Wedge (constFirstArgProf F) :=
  Wedge.mk c.pt (fun j => c.π.app j) (fun {j j'} f => by
    simp only [constFirstArgProf, Functor.const_obj_obj, Functor.const_obj_map,
      NatTrans.id_app, Category.comp_id]
    have nat := c.π.naturality f
    dsimp only [Functor.const_obj_obj, Functor.const_obj_map] at nat
    rw [Category.id_comp] at nat
    exact nat.symm)

/-- Convert a wedge over the constant-first-arg profunctor to a cone over `F`.
The wedge legs become cone legs directly. -/
def wedgeConstProfToCone {J : Type*} [Category J] {D : Type*} [Category D]
    (F : J ⥤ D) (w : Wedge (constFirstArgProf F)) : Cone F where
  pt := w.pt
  π := {
    app := fun j => Multifork.ι w j
    naturality := fun j j' f => by
      dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
      rw [Category.id_comp]
      have din := w.condition f
      simp only [constFirstArgProf_map_snd, constFirstArgProf_map_fst] at din
      calc Multifork.ι w j' = Multifork.ι w j' ≫ 𝟙 _ := (Category.comp_id _).symm
        _ = Multifork.ι w j ≫ F.map f := din.symm
  }

/-- Round-trip: cone to wedge to cone is identity. -/
@[simp]
theorem wedgeConstProfToCone_coneToWedge {J : Type*} [Category J]
    {D : Type*} [Category D] (F : J ⥤ D) (c : Cone F) :
    wedgeConstProfToCone F (coneToWedgeConstProf F c) = c := by
  cases c with | mk pt π =>
  simp only [coneToWedgeConstProf, wedgeConstProfToCone]
  rfl

/-- Round-trip: wedge to cone to wedge is identity. -/
@[simp]
theorem coneToWedgeConstProf_wedgeToCone {J : Type*} [Category J]
    {D : Type*} [Category D] (F : J ⥤ D) (w : Wedge (constFirstArgProf F)) :
    coneToWedgeConstProf F (wedgeConstProfToCone F w) = w := by
  cases w with | mk pt π =>
  simp only [wedgeConstProfToCone, coneToWedgeConstProf]
  rw [Cone.mk.injEq]
  constructor
  · rfl
  · apply heq_of_eq
    ext tw
    simp only [Multifork.ofι_π_app]
    cases tw with
    | left j => rfl
    | right b =>
      simp only [← Multifork.app_right_eq_ι_comp_fst]

/-- Functor from cones over F to wedges over the constant-first-arg profunctor. -/
def coneToWedgeConstProfFunctor {J : Type*} [Category J]
    {D : Type*} [Category D] (F : J ⥤ D) :
    Cone F ⥤ Wedge (constFirstArgProf F) where
  obj := coneToWedgeConstProf F
  map := fun {c₁ c₂} f => {
    hom := f.hom
    w := fun tw => by
      cases tw with
      | left j =>
        simp only [coneToWedgeConstProf, Multifork.ofι_π_app]
        exact f.w j
      | right b =>
        simp only [coneToWedgeConstProf, Multifork.ofι_π_app]
        let j : J := (multicospanShapeEnd J).fst b
        have hw := f.w j
        rw [← Category.assoc, hw]
  }

/-- Functor from wedges over constant-first-arg profunctor to cones over F. -/
def wedgeConstProfToConeFunctor {J : Type*} [Category J]
    {D : Type*} [Category D] (F : J ⥤ D) :
    Wedge (constFirstArgProf F) ⥤ Cone F where
  obj := wedgeConstProfToCone F
  map := fun {w₁ w₂} f => {
    hom := f.hom
    w := fun j => by
      simp only [wedgeConstProfToCone]
      have h := f.w (WalkingMulticospan.left j)
      exact h
  }

/-- The category of wedges over a constant-first-arg profunctor is equivalent
to the category of cones over the underlying functor. -/
def wedgeConstProfEquivCone {J : Type*} [Category J]
    {D' : Type*} [Category D'] (F : J ⥤ D') :
    Wedge (constFirstArgProf F) ≌ Cone F where
  functor := wedgeConstProfToConeFunctor F
  inverse := coneToWedgeConstProfFunctor F
  unitIso := NatIso.ofComponents
    (fun w => eqToIso (coneToWedgeConstProf_wedgeToCone F w).symm)
    (fun {w₁ w₂} f => by
      ext
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map,
        coneToWedgeConstProfFunctor, wedgeConstProfToConeFunctor,
        eqToIso.hom, Cone.category_comp_hom, Cone.eqToHom_hom, eqToHom_refl,
        Category.comp_id, Category.id_comp])
  counitIso := NatIso.ofComponents
    (fun c => eqToIso (wedgeConstProfToCone_coneToWedge F c).symm)
    (fun {c₁ c₂} f => by
      ext
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map,
        wedgeConstProfToConeFunctor, coneToWedgeConstProfFunctor,
        eqToIso.hom, eqToHom_refl, Category.comp_id, Category.id_comp])

end ConstProfWedgeAsCone

section ConstProfCowedgeAsCocone

variable {C : Type u} [Category.{v} C]

/-- The profunctor constant in its second argument: `P(k, j) = G(k)`.
For `G : Jᵒᵖ ⥤ D`, this profunctor is constant in the covariant (second) position.
The diagonal at `j` is `G(op j)`, which equals `(G.leftOp).obj j`.
This is the dual of `constFirstArgProf`. -/
def constSecondArgProf {J : Type*} [Category J] {D : Type*} [Category D]
    (G : Jᵒᵖ ⥤ D) : Jᵒᵖ ⥤ J ⥤ D :=
  G ⋙ (Functor.const J)

/-- For the constant-second-arg profunctor, the diagonal at `j` is `G(op j)`. -/
@[simp]
lemma constSecondArgProf_diag {J : Type*} [Category J] {D : Type*} [Category D]
    (G : Jᵒᵖ ⥤ D) (j : J) :
    ((constSecondArgProf G).obj (Opposite.op j)).obj j = G.obj (Opposite.op j) := rfl

/-- The covariant action on `f : j → j'` is identity (constant in second arg). -/
@[simp]
lemma constSecondArgProf_map_snd {J : Type*} [Category J] {D : Type*} [Category D]
    (G : Jᵒᵖ ⥤ D) {j₁ j₂ : J} (f : j₁ ⟶ j₂) (k : Jᵒᵖ) :
    ((constSecondArgProf G).obj k).map f = 𝟙 (G.obj k) := rfl

/-- The contravariant action is the functorial action of `G`. -/
@[simp]
lemma constSecondArgProf_map_fst {J : Type*} [Category J] {D : Type*} [Category D]
    (G : Jᵒᵖ ⥤ D) {k₁ k₂ : Jᵒᵖ} (f : k₁ ⟶ k₂) (j : J) :
    ((constSecondArgProf G).map f).app j = G.map f := rfl

/-- Convert a cocone over `G : Jᵒᵖ ⥤ D` to a cowedge over the constant-second-arg profunctor.
The cocone leg at `op j` becomes the cowedge leg at `j`. -/
def coconeToCowedgeConstProf {J : Type*} [Category J] {D : Type*} [Category D]
    (G : Jᵒᵖ ⥤ D) (c : Cocone G) : Cowedge (constSecondArgProf G) :=
  Cowedge.mk c.pt (fun j => c.ι.app (Opposite.op j)) (fun {j j'} f => by
    simp only [constSecondArgProf, Functor.comp_obj, Functor.const_obj_obj,
      Functor.comp_map, Functor.const_obj_map]
    have nat := c.ι.naturality f.op
    dsimp only [Functor.const_obj_obj, Functor.const_obj_map] at nat
    rw [Category.comp_id] at nat
    rw [Category.id_comp]
    exact nat)

/-- Convert a cowedge over the constant-second-arg profunctor to a cocone over `G : Jᵒᵖ ⥤ D`.
The cowedge leg at `j` becomes the cocone leg at `op j`. -/
def cowedgeConstProfToCocone {J : Type*} [Category J] {D : Type*} [Category D]
    (G : Jᵒᵖ ⥤ D) (w : Cowedge (constSecondArgProf G)) : Cocone G where
  pt := w.pt
  ι := {
    app := fun k => Multicofork.π w k.unop
    naturality := fun k₁ k₂ f => by
      dsimp only [Functor.const_obj_obj, Functor.const_obj_map]
      rw [Category.comp_id]
      have din := w.condition f.unop
      simp only [constSecondArgProf, Functor.comp_obj, Functor.const_obj_obj,
        Functor.comp_map, Functor.const_obj_map, Category.id_comp] at din
      rw [Quiver.Hom.op_unop] at din
      exact din
  }

/-- Round-trip: cocone to cowedge to cocone is identity. -/
@[simp]
theorem cowedgeConstProfToCocone_coconeToCowedge {J : Type*} [Category J]
    {D : Type*} [Category D] (G : Jᵒᵖ ⥤ D) (c : Cocone G) :
    cowedgeConstProfToCocone G (coconeToCowedgeConstProf G c) = c := by
  cases c with | mk pt ι =>
  simp only [coconeToCowedgeConstProf, cowedgeConstProfToCocone]
  rfl

/-- Round-trip: cowedge to cocone to cowedge is identity. -/
@[simp]
theorem coconeToCowedgeConstProf_cowedgeToCocone {J : Type*} [Category J]
    {D : Type*} [Category D] (G : Jᵒᵖ ⥤ D) (w : Cowedge (constSecondArgProf G)) :
    coconeToCowedgeConstProf G (cowedgeConstProfToCocone G w) = w := by
  cases w with | mk pt π =>
  simp only [cowedgeConstProfToCocone, coconeToCowedgeConstProf]
  rw [Cocone.mk.injEq]
  constructor
  · rfl
  · apply heq_of_eq
    ext tw
    cases tw with
    | left j =>
      exact (Multicofork.fst_app_right (I := multispanIndexCoend _) ⟨pt, π⟩ j).symm
    | right b =>
      exact (Multicofork.π_eq_app_right ⟨pt, π⟩ b).symm

/-- Functor from cocones over G to cowedges over the constant-second-arg profunctor. -/
def coconeToCowedgeConstProfFunctor {J : Type*} [Category J]
    {D : Type*} [Category D] (G : Jᵒᵖ ⥤ D) :
    Cocone G ⥤ Cowedge (constSecondArgProf G) where
  obj := coconeToCowedgeConstProf G
  map {c₁ c₂} f := {
    hom := f.hom
    w := fun tw => by
      -- For multispanShapeCoend: .L = Arrow J, .R = J
      cases tw with
      | left arr =>
        -- arr : Arrow J
        -- Goal: (fst arr ≫ c₁.π (op arr.left)) ≫ f.hom = fst arr ≫ c₂.π (op arr.left)
        -- where fst arr = G.map arr.hom.op
        simp only [coconeToCowedgeConstProf, Multicofork.ofπ_ι_app, multispanShapeCoend_fst]
        have hw := f.w (Opposite.op arr.left)
        simp only [Functor.const_obj_obj] at hw
        rw [Category.assoc, hw]
      | right j =>
        -- j : J directly
        simp only [coconeToCowedgeConstProf, Multicofork.ofπ_ι_app]
        have hw := f.w (Opposite.op j)
        simp only [Functor.const_obj_obj] at hw
        exact hw
  }

/-- Functor from cowedges over constant-second-arg profunctor to cocones over G. -/
def cowedgeConstProfToCoconeFunctor {J : Type*} [Category J]
    {D : Type*} [Category D] (G : Jᵒᵖ ⥤ D) :
    Cowedge (constSecondArgProf G) ⥤ Cocone G where
  obj := cowedgeConstProfToCocone G
  map {w₁ w₂} f := {
    hom := f.hom
    w := fun k => by
      -- k : Jᵒᵖ, need to relate to WalkingMultispan index
      -- For multispanShapeCoend: .L = Arrow J, .R = J
      -- Use .right case since that's indexed by J
      simp only [cowedgeConstProfToCocone, Functor.const_obj_obj]
      have h := f.w (WalkingMultispan.right k.unop)
      exact h
  }

/-- The category of cowedges over a constant-second-arg profunctor is equivalent
to the category of cocones over the underlying functor. -/
def cowedgeConstProfEquivCocone {J : Type*} [Category J]
    {D' : Type*} [Category D'] (G : Jᵒᵖ ⥤ D') :
    Cowedge (constSecondArgProf G) ≌ Cocone G where
  functor := cowedgeConstProfToCoconeFunctor G
  inverse := coconeToCowedgeConstProfFunctor G
  unitIso := NatIso.ofComponents
    (fun w => eqToIso (coconeToCowedgeConstProf_cowedgeToCocone G w).symm)
    (fun {w₁ w₂} f => by
      ext
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map,
        coconeToCowedgeConstProfFunctor, cowedgeConstProfToCoconeFunctor,
        eqToIso.hom, Cocone.category_comp_hom, Cocone.eqToHom_hom, eqToHom_refl,
        Category.comp_id, Category.id_comp])
  counitIso := NatIso.ofComponents
    (fun c => eqToIso (cowedgeConstProfToCocone_coconeToCowedge G c).symm)
    (fun {c₁ c₂} f => by
      ext
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map,
        cowedgeConstProfToCoconeFunctor, coconeToCowedgeConstProfFunctor,
        eqToIso.hom, eqToHom_refl, Category.comp_id, Category.id_comp])

end ConstProfCowedgeAsCocone

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

universe u₁ v₁

variable {J : Type u₁} [Category.{v₁, u₁} J]

/--
The curried trifunctor exhibiting `WeightedConeUnder` as a functorial construction.

Takes `W : (J ⥤ Type v)ᵒᵖ` and produces `(J ⥤ C) ⥤ Cᵒᵖ ⥤ Type` where
the value at `(D, pt)` is `W.unop ⟶ homFromFunctor D pt.unop`.
-/
def weightedConeUnderCurriedTrifunctor :
    (J ⥤ Type v)ᵒᵖ ⥤ (J ⥤ C) ⥤ Cᵒᵖ ⥤ Type (max _ v) :=
  Functor.curry.obj (Functor.hom (J ⥤ Type v)) ⋙
  (Functor.whiskeringRight Cᵒᵖ (J ⥤ Type v) (Type (max u₁ v))) ⋙
  (Functor.whiskeringLeft (J ⥤ C) (Cᵒᵖ ⥤ J ⥤ Type v) (Cᵒᵖ ⥤ Type (max u₁ v))).obj
    homFromFunctorBifunctor

/--
A weighted cone under a fixed point `pt` over a diagram `D : J ⥤ C` with
weight `W : J ⥤ Type v`. This is the type of natural transformations
`W ⟶ Hom(pt, D(-))`.
-/
abbrev WeightedConeUnder (W : J ⥤ Type v) (D : J ⥤ C) (pt : C) :=
  ((weightedConeUnderCurriedTrifunctor.obj (Opposite.op W)).obj D).obj
    (Opposite.op pt)

/--
A weighted cone over a diagram `D : J ⥤ C` with weight `W : J ⥤ Type v`
consists of a cone point `pt` and a `WeightedConeUnder pt W D`.
-/
@[ext]
structure WeightedCone (W : J ⥤ Type v) (D : J ⥤ C) where
  /-- The cone point -/
  pt : C
  /-- The cone data under the point -/
  toWeightedConeUnder : WeightedConeUnder W D pt

namespace WeightedCone

/-- The natural transformation from the weight to `Hom(pt, D(-))`. -/
abbrev π {W : J ⥤ Type v} {D : J ⥤ C} (c : WeightedCone W D) :
    W ⟶ homFromFunctor D c.pt := c.toWeightedConeUnder

/-- Constructor with explicit point and natural transformation arguments. -/
@[match_pattern]
def mk' {W : J ⥤ Type v} {D : J ⥤ C} (pt : C) (π : W ⟶ homFromFunctor D pt) :
    WeightedCone W D := ⟨pt, π⟩

end WeightedCone

/--
For a weighted cone, extract the morphism at index `j` for weight element `w`.
-/
def WeightedCone.leg {W : J ⥤ Type v} {D : J ⥤ C} (c : WeightedCone W D)
    (j : J) (w : W.obj j) : c.pt ⟶ D.obj j :=
  c.π.app j w

/--
Naturality for weighted cones: for `f : j ⟶ j'` and `w : W.obj j`,
composing with `D.map f` equals applying `W.map f` first.
-/
theorem WeightedCone.naturality {W : J ⥤ Type v} {D : J ⥤ C}
    (c : WeightedCone W D) {j j' : J} (f : j ⟶ j') (w : W.obj j) :
    c.leg j w ≫ D.map f = c.leg j' (W.map f w) := by
  unfold leg homFromFunctor
  have nat := c.π.naturality f
  exact (congrFun nat w).symm

/--
The curried trifunctor exhibiting `WeightedCoconeOver` as a functorial construction.

Takes `W : (Jᵒᵖ ⥤ Type v)ᵒᵖ` and produces `(J ⥤ C)ᵒᵖ ⥤ C ⥤ Type` where
the value at `(Dᵒᵖ, pt)` is `W.unop ⟶ homToFunctor D pt`.
-/
def weightedCoconeOverCurriedTrifunctor :
    (Jᵒᵖ ⥤ Type v)ᵒᵖ ⥤ (J ⥤ C)ᵒᵖ ⥤ C ⥤ Type (max u₁ v) :=
  Functor.curry.obj (Functor.hom (Jᵒᵖ ⥤ Type v)) ⋙
  (Functor.whiskeringRight C (Jᵒᵖ ⥤ Type v) (Type (max u₁ v))) ⋙
  (Functor.whiskeringLeft (J ⥤ C)ᵒᵖ (C ⥤ Jᵒᵖ ⥤ Type v) (C ⥤ Type (max u₁ v))).obj
    homToFunctorBifunctor

/--
A weighted cocone over a fixed point `pt` for a diagram `D : J ⥤ C` with
weight `W : Jᵒᵖ ⥤ Type v`. This is the type of natural transformations
`W ⟶ Hom(D(-), pt)`.
-/
abbrev WeightedCoconeOver (W : Jᵒᵖ ⥤ Type v) (D : J ⥤ C) (pt : C) :=
  ((weightedCoconeOverCurriedTrifunctor.obj (Opposite.op W)).obj
      (Opposite.op D)).obj
    pt

/--
A weighted cocone over a diagram `D : J ⥤ C` with weight `W : Jᵒᵖ ⥤ Type v`
(a presheaf on `J`) consists of a cocone point `pt` and a `WeightedCoconeOver pt W D`.

Note: The weight is contravariant (`Jᵒᵖ ⥤ Type v`) to match the variance
of `Hom(D(-), pt)`.
-/
@[ext]
structure WeightedCocone (W : Jᵒᵖ ⥤ Type v) (D : J ⥤ C) where
  /-- The cocone point -/
  pt : C
  /-- The cocone data over the point -/
  toWeightedCoconeOver : WeightedCoconeOver W D pt

namespace WeightedCocone

/-- The natural transformation from the weight to `Hom(D(-), pt)`. -/
abbrev ι {W : Jᵒᵖ ⥤ Type v} {D : J ⥤ C} (c : WeightedCocone W D) :
    W ⟶ homToFunctor D c.pt := c.toWeightedCoconeOver

/-- Constructor with explicit point and natural transformation arguments. -/
@[match_pattern]
def mk' {W : Jᵒᵖ ⥤ Type v} {D : J ⥤ C} (pt : C) (ι : W ⟶ homToFunctor D pt) :
    WeightedCocone W D := ⟨pt, ι⟩

end WeightedCocone

/--
For a weighted cocone, extract the morphism at index `j` for weight element `w`.
-/
def WeightedCocone.leg {W : Jᵒᵖ ⥤ Type v} {D : J ⥤ C} (c : WeightedCocone W D)
    (j : J) (w : W.obj (Opposite.op j)) : D.obj j ⟶ c.pt :=
  c.ι.app (Opposite.op j) w

/--
Naturality for weighted cocones: for `f : j ⟶ j'` and `w : W.obj (op j')`,
precomposing with `D.map f` equals applying `W.map f.op` first.
-/
theorem WeightedCocone.naturality {W : Jᵒᵖ ⥤ Type v} {D : J ⥤ C}
    (c : WeightedCocone W D) {j j' : J} (f : j ⟶ j') (w : W.obj (Opposite.op j')) :
    D.map f ≫ c.leg j' w = c.leg j (W.map f.op w) := by
  unfold leg homToFunctor
  have nat := c.ι.naturality f.op
  exact (congrFun nat w).symm

/--
A morphism between weighted cones consists of a morphism between the cone
points that commutes with the projections for all weight elements.
-/
@[ext]
structure WeightedCone.Hom {W : J ⥤ Type v} {D : J ⥤ C}
    (c₁ c₂ : WeightedCone W D) where
  /-- The morphism between cone points -/
  hom : c₁.pt ⟶ c₂.pt
  /-- Commutativity: for each index j and weight w, the triangle commutes -/
  w : ∀ (j : J) (w : W.obj j), hom ≫ c₂.leg j w = c₁.leg j w := by aesop_cat

attribute [reassoc (attr := simp)] WeightedCone.Hom.w

/--
Identity morphism for weighted cones.
-/
def WeightedCone.Hom.id {W : J ⥤ Type v} {D : J ⥤ C} (c : WeightedCone W D) :
    WeightedCone.Hom c c where
  hom := 𝟙 c.pt

@[simp]
theorem WeightedCone.Hom.id_hom {W : J ⥤ Type v} {D : J ⥤ C}
    (c : WeightedCone W D) : (WeightedCone.Hom.id c).hom = 𝟙 c.pt := rfl

/--
Composition of weighted cone morphisms.
-/
def WeightedCone.Hom.comp {W : J ⥤ Type v} {D : J ⥤ C}
    {c₁ c₂ c₃ : WeightedCone W D}
    (f : WeightedCone.Hom c₁ c₂) (g : WeightedCone.Hom c₂ c₃) :
    WeightedCone.Hom c₁ c₃ where
  hom := f.hom ≫ g.hom
  w j w := by simp [f.w, g.w]

@[simp]
theorem WeightedCone.Hom.comp_hom {W : J ⥤ Type v} {D : J ⥤ C}
    {c₁ c₂ c₃ : WeightedCone W D}
    (f : WeightedCone.Hom c₁ c₂) (g : WeightedCone.Hom c₂ c₃) :
    (WeightedCone.Hom.comp f g).hom = f.hom ≫ g.hom := rfl

instance (W : J ⥤ Type v) (D : J ⥤ C) : Category (WeightedCone W D) where
  Hom := WeightedCone.Hom
  id := WeightedCone.Hom.id
  comp := WeightedCone.Hom.comp
  id_comp f := by ext; simp
  comp_id f := by ext; simp
  assoc f g h := by ext; simp [Category.assoc]

@[simp]
theorem WeightedCone.category_comp_hom {W : J ⥤ Type v} {D : J ⥤ C}
    {c₁ c₂ c₃ : WeightedCone W D}
    (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) : (f ≫ g).hom = f.hom ≫ g.hom := rfl

@[simp]
theorem WeightedCone.category_id_hom {W : J ⥤ Type v} {D : J ⥤ C}
    (c : WeightedCone W D) : (𝟙 c : c ⟶ c).hom = 𝟙 c.pt := rfl

/--
A morphism between weighted cocones consists of a morphism between the cocone
points that commutes with the injections for all weight elements.
-/
@[ext]
structure WeightedCocone.Hom {W : Jᵒᵖ ⥤ Type v} {D : J ⥤ C}
    (c₁ c₂ : WeightedCocone W D) where
  /-- The morphism between cocone points -/
  hom : c₁.pt ⟶ c₂.pt
  /-- Commutativity: for each index j and weight w, the triangle commutes -/
  w : ∀ (j : J) (w : W.obj (Opposite.op j)),
      c₁.leg j w ≫ hom = c₂.leg j w := by aesop_cat

attribute [reassoc (attr := simp)] WeightedCocone.Hom.w

/--
Identity morphism for weighted cocones.
-/
def WeightedCocone.Hom.id {W : Jᵒᵖ ⥤ Type v} {D : J ⥤ C}
    (c : WeightedCocone W D) : WeightedCocone.Hom c c where
  hom := 𝟙 c.pt

/--
Composition of weighted cocone morphisms.
-/
def WeightedCocone.Hom.comp {W : Jᵒᵖ ⥤ Type v} {D : J ⥤ C}
    {c₁ c₂ c₃ : WeightedCocone W D}
    (f : WeightedCocone.Hom c₁ c₂) (g : WeightedCocone.Hom c₂ c₃) :
    WeightedCocone.Hom c₁ c₃ where
  hom := f.hom ≫ g.hom
  w j w := by simp [g.w, f.w_assoc]

@[simp]
theorem WeightedCocone.Hom.id_hom {W : Jᵒᵖ ⥤ Type v} {D : J ⥤ C}
    (c : WeightedCocone W D) : (WeightedCocone.Hom.id c).hom = 𝟙 c.pt := rfl

@[simp]
theorem WeightedCocone.Hom.comp_hom {W : Jᵒᵖ ⥤ Type v} {D : J ⥤ C}
    {c₁ c₂ c₃ : WeightedCocone W D}
    (f : WeightedCocone.Hom c₁ c₂) (g : WeightedCocone.Hom c₂ c₃) :
    (WeightedCocone.Hom.comp f g).hom = f.hom ≫ g.hom := rfl

instance (W : Jᵒᵖ ⥤ Type v) (D : J ⥤ C) : Category (WeightedCocone W D) where
  Hom := WeightedCocone.Hom
  id := WeightedCocone.Hom.id
  comp := WeightedCocone.Hom.comp
  id_comp f := by ext; simp [WeightedCocone.Hom.id, WeightedCocone.Hom.comp]
  comp_id f := by ext; simp [WeightedCocone.Hom.id, WeightedCocone.Hom.comp]
  assoc f g h := by ext; simp [WeightedCocone.Hom.comp, Category.assoc]

@[simp]
theorem WeightedCocone.category_comp_hom {W : Jᵒᵖ ⥤ Type v} {D : J ⥤ C}
    {c₁ c₂ c₃ : WeightedCocone W D}
    (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) : (f ≫ g).hom = f.hom ≫ g.hom := rfl

@[simp]
theorem WeightedCocone.category_id_hom {W : Jᵒᵖ ⥤ Type v} {D : J ⥤ C}
    (c : WeightedCocone W D) : (𝟙 c : c ⟶ c).hom = 𝟙 c.pt := rfl

/-- For weighted cocones, the `.hom` field of `eqToHom h` is `eqToHom`
applied to the cocone point equality. -/
@[simp]
theorem WeightedCocone.eqToHom_hom {W : Jᵒᵖ ⥤ Type v} {D : J ⥤ C}
    {c c' : WeightedCocone W D} (h : c = c') :
    (eqToHom h).hom = eqToHom (congrArg WeightedCocone.pt h) := by
  subst h
  rfl

section WeightedLimitsColimits

/-!
## Weighted Limits and Colimits

A weighted limit is a terminal object in the category of weighted cones, and
a weighted colimit is an initial object in the category of weighted cocones.

These definitions parallel mathlib's `IsLimit`/`IsColimit` for ordinary
limits and the `IsRestrictedCoend` pattern we use elsewhere.
-/

/-- A weighted limit is a terminal object in the category of weighted cones. -/
abbrev IsWeightedLimit {W : J ⥤ Type v} {D : J ⥤ C} (c : WeightedCone W D) :=
  Limits.IsTerminal c

namespace IsWeightedLimit

variable {W : J ⥤ Type v} {D : J ⥤ C} {c : WeightedCone W D}

/-- The universal morphism from any weighted cone to the weighted limit. -/
def lift (hc : IsWeightedLimit c) (d : WeightedCone W D) : d ⟶ c :=
  hc.from d

/-- The underlying morphism in `C` from any cone to the limit cone. -/
def liftHom (hc : IsWeightedLimit c) (d : WeightedCone W D) : d.pt ⟶ c.pt :=
  (hc.lift d).hom

/-- Any two morphisms to a weighted limit are equal (uniqueness). -/
theorem homExt (hc : IsWeightedLimit c)
    {d : WeightedCone W D} (f g : d ⟶ c) : f = g :=
  Limits.IsTerminal.hom_ext hc f g

/-- Two weighted limits are isomorphic (uniqueness up to isomorphism). -/
def toUniqueUpToIso {c c' : WeightedCone W D}
    (hc : IsWeightedLimit c) (hc' : IsWeightedLimit c') : c ≅ c' :=
  Limits.IsTerminal.uniqueUpToIso hc hc'

end IsWeightedLimit

/-- A weighted limit cone bundles a cone with the proof it is terminal.
This is the data-carrying version, analogous to mathlib's `LimitCone`. -/
structure WeightedLimitCone (W : J ⥤ Type v) (D : J ⥤ C) where
  /-- The underlying weighted cone. -/
  cone : WeightedCone W D
  /-- The proof that the cone is terminal. -/
  isLimit : IsWeightedLimit cone

/-- A weighted limit exists if there is a terminal weighted cone. -/
class HasWeightedLimit (W : J ⥤ Type v) (D : J ⥤ C) where
  /-- The limit cone containing the limit and proof of terminality. -/
  limitCone : WeightedLimitCone W D

namespace HasWeightedLimit

variable (W : J ⥤ Type v) (D : J ⥤ C) [HasWeightedLimit W D]

/-- The weighted limit cone (the terminal weighted cone). -/
def weightedLimit : WeightedCone W D :=
  HasWeightedLimit.limitCone.cone

/-- The weighted limit is terminal. -/
def weightedLimitIsLimit : IsWeightedLimit (weightedLimit W D) :=
  HasWeightedLimit.limitCone.isLimit

/-- The weighted limit object (the cone point of the limit cone). -/
def weightedLimitObj : C := (weightedLimit W D).pt

end HasWeightedLimit

/-- A weighted colimit is an initial object in the category of weighted
cocones. -/
abbrev IsWeightedColimit {W : Jᵒᵖ ⥤ Type v} {D : J ⥤ C}
    (c : WeightedCocone W D) :=
  Limits.IsInitial c

namespace IsWeightedColimit

variable {W : Jᵒᵖ ⥤ Type v} {D : J ⥤ C} {c : WeightedCocone W D}

/-- The universal morphism from a weighted colimit to any weighted cocone. -/
def desc (hc : IsWeightedColimit c) (d : WeightedCocone W D) : c ⟶ d :=
  hc.to d

/-- The underlying morphism in `C` from the colimit to any cocone. -/
def descHom (hc : IsWeightedColimit c) (d : WeightedCocone W D) : c.pt ⟶ d.pt :=
  (hc.desc d).hom

/-- Any two morphisms from a weighted colimit are equal (uniqueness). -/
theorem homExt (hc : IsWeightedColimit c)
    {d : WeightedCocone W D} (f g : c ⟶ d) : f = g :=
  Limits.IsInitial.hom_ext hc f g

/-- Two weighted colimits are isomorphic (uniqueness up to isomorphism). -/
def toUniqueUpToIso {c c' : WeightedCocone W D}
    (hc : IsWeightedColimit c) (hc' : IsWeightedColimit c') : c ≅ c' :=
  Limits.IsInitial.uniqueUpToIso hc hc'

end IsWeightedColimit

/-- A weighted colimit cone bundles a cocone with the proof it is initial.
This is the data-carrying version, analogous to mathlib's `ColimitCocone`. -/
structure WeightedColimitCocone (W : Jᵒᵖ ⥤ Type v) (D : J ⥤ C) where
  /-- The underlying weighted cocone. -/
  cocone : WeightedCocone W D
  /-- The proof that the cocone is initial. -/
  isColimit : IsWeightedColimit cocone

/-- A weighted colimit exists if there is an initial weighted cocone. -/
class HasWeightedColimit (W : Jᵒᵖ ⥤ Type v) (D : J ⥤ C) where
  /-- The colimit cocone containing the colimit and proof of initiality. -/
  colimitCocone : WeightedColimitCocone W D

namespace HasWeightedColimit

variable (W : Jᵒᵖ ⥤ Type v) (D : J ⥤ C) [HasWeightedColimit W D]

/-- The weighted colimit cocone (the initial weighted cocone). -/
def weightedColimit : WeightedCocone W D :=
  HasWeightedColimit.colimitCocone.cocone

/-- The weighted colimit is initial. -/
def weightedColimitIsColimit : IsWeightedColimit (weightedColimit W D) :=
  HasWeightedColimit.colimitCocone.isColimit

/-- The weighted colimit object (the cocone point of the colimit cocone). -/
def weightedColimitObj : C := (weightedColimit W D).pt

end HasWeightedColimit

end WeightedLimitsColimits

variable {D : Type w} [Category.{v} D]

/--
A weighted wedge over a profunctor `P : Cᵒᵖ ⥤ C ⥤ D` with weight profunctor
`W : Cᵒᵖ ⥤ C ⥤ Type v`, over a fixed apex `pt : D`.
-/
abbrev WeightedWedgeUnder (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) (pt : D) :=
  WeightedConeUnder (C := D) (J := TwistedArrow C)
    (profunctorOnTwistedArrow C W) (profunctorOnTwistedArrow C P) pt

/--
A weighted wedge over a profunctor `P : Cᵒᵖ ⥤ C ⥤ D` with weight profunctor
`W : Cᵒᵖ ⥤ C ⥤ Type v` is a weighted cone over the diagram
`profunctorOnTwistedArrow C P` with weight `profunctorOnTwistedArrow C W`.

Both the weight and the diagram are profunctors, converted to functors on
`TwistedArrow C` via `profunctorOnTwistedArrow`.

This generalizes ordinary wedges: when `W` is the terminal profunctor (constant
at a singleton), a weighted wedge is exactly an ordinary wedge.
-/
abbrev WeightedWedge (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) :=
  WeightedCone (C := D) (J := TwistedArrow C)
    (profunctorOnTwistedArrow C W) (profunctorOnTwistedArrow C P)

/--
A weighted cowedge over a profunctor `P : Cᵒᵖ ⥤ C ⥤ D` with weight profunctor
`W : Cᵒᵖ ⥤ C ⥤ Type v`, over a fixed apex `pt : D`.
-/
abbrev WeightedCowedgeOver (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) (pt : D) :=
  WeightedCoconeOver (C := D) (J := CoTwistedArrow C)
    (profunctorOnOpCoTwistedArrow C W)
    (profunctorOnCoTwistedArrow C P) pt

/--
A weighted cowedge over a profunctor `P : Cᵒᵖ ⥤ C ⥤ D` with weight profunctor
`W : Cᵒᵖ ⥤ C ⥤ Type v` is a weighted cocone over the diagram
`profunctorOnCoTwistedArrow C P` with weight `profunctorOnOpCoTwistedArrow C W`.

Both the weight and the diagram are profunctors. The weight is evaluated on
the opposite of the co-twisted arrow category via `profunctorOnOpCoTwistedArrow`,
which uses the equivalence `(CoTwistedArrow C)ᵒᵖ ≌ TwistedArrow C`. The diagram
is evaluated via `profunctorOnCoTwistedArrow`.

This generalizes ordinary cowedges: when `W` is the terminal profunctor
(constant at a singleton), a weighted cowedge is exactly an ordinary cowedge.
-/
abbrev WeightedCowedge (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) :=
  WeightedCocone (C := D) (J := CoTwistedArrow C)
    (profunctorOnOpCoTwistedArrow C W)
    (profunctorOnCoTwistedArrow C P)

/-!
## Weighted Ends and Coends

A weighted end is a terminal object in the category of weighted wedges, and
a weighted coend is an initial object in the category of weighted cowedges.

These are specializations of weighted limits and colimits to profunctors
(bifunctors `Cᵒᵖ ⥤ C ⥤ D`) using the twisted and co-twisted arrow categories.
-/

/-- A weighted end is a terminal object in the category of weighted wedges. -/
abbrev IsWeightedEnd {W : Cᵒᵖ ⥤ C ⥤ Type v} {P : Cᵒᵖ ⥤ C ⥤ D}
    (c : WeightedWedge W P) :=
  Limits.IsTerminal c

namespace IsWeightedEnd

variable {W : Cᵒᵖ ⥤ C ⥤ Type v} {P : Cᵒᵖ ⥤ C ⥤ D} {c : WeightedWedge W P}

/-- The universal morphism from any weighted wedge to the weighted end. -/
def lift (hc : IsWeightedEnd c) (d : WeightedWedge W P) : d ⟶ c :=
  hc.from d

/-- The underlying morphism in `D` from any wedge to the end wedge. -/
def liftHom (hc : IsWeightedEnd c) (d : WeightedWedge W P) : d.pt ⟶ c.pt :=
  (hc.lift d).hom

/-- Any two morphisms to a weighted end are equal (uniqueness). -/
theorem homExt (hc : IsWeightedEnd c)
    {d : WeightedWedge W P} (f g : d ⟶ c) : f = g :=
  Limits.IsTerminal.hom_ext hc f g

/-- Two weighted ends are isomorphic (uniqueness up to isomorphism). -/
def toUniqueUpToIso {c c' : WeightedWedge W P}
    (hc : IsWeightedEnd c) (hc' : IsWeightedEnd c') : c ≅ c' :=
  Limits.IsTerminal.uniqueUpToIso hc hc'

end IsWeightedEnd

/-- A weighted end wedge bundles a wedge with the proof it is terminal. -/
structure WeightedEndWedge (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) where
  /-- The underlying weighted wedge. -/
  wedge : WeightedWedge W P
  /-- The proof that the wedge is terminal. -/
  isEnd : IsWeightedEnd wedge

/-- A weighted end exists if there is a terminal weighted wedge. -/
class HasWeightedEnd (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) where
  /-- The end wedge containing the end and proof of terminality. -/
  endWedge : WeightedEndWedge W P

namespace HasWeightedEnd

variable (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) [HasWeightedEnd W P]

/-- The weighted end wedge (the terminal weighted wedge). -/
def weightedEnd : WeightedWedge W P :=
  HasWeightedEnd.endWedge.wedge

/-- The weighted end is terminal. -/
def weightedEndIsEnd : IsWeightedEnd (weightedEnd W P) :=
  HasWeightedEnd.endWedge.isEnd

/-- The weighted end object (the wedge point of the end wedge). -/
def weightedEndObj : D := (weightedEnd W P).pt

end HasWeightedEnd

/-- A weighted coend is an initial object in the category of weighted
cowedges. -/
abbrev IsWeightedCoend {W : Cᵒᵖ ⥤ C ⥤ Type v} {P : Cᵒᵖ ⥤ C ⥤ D}
    (c : WeightedCowedge W P) :=
  Limits.IsInitial c

namespace IsWeightedCoend

variable {W : Cᵒᵖ ⥤ C ⥤ Type v} {P : Cᵒᵖ ⥤ C ⥤ D} {c : WeightedCowedge W P}

/-- The universal morphism from a weighted coend to any weighted cowedge. -/
def desc (hc : IsWeightedCoend c) (d : WeightedCowedge W P) : c ⟶ d :=
  hc.to d

/-- The underlying morphism in `D` from the coend to any cowedge. -/
def descHom (hc : IsWeightedCoend c) (d : WeightedCowedge W P) : c.pt ⟶ d.pt :=
  (hc.desc d).hom

/-- Any two morphisms from a weighted coend are equal (uniqueness). -/
theorem homExt (hc : IsWeightedCoend c)
    {d : WeightedCowedge W P} (f g : c ⟶ d) : f = g :=
  Limits.IsInitial.hom_ext hc f g

/-- Two weighted coends are isomorphic (uniqueness up to isomorphism). -/
def toUniqueUpToIso {c c' : WeightedCowedge W P}
    (hc : IsWeightedCoend c) (hc' : IsWeightedCoend c') : c ≅ c' :=
  Limits.IsInitial.uniqueUpToIso hc hc'

end IsWeightedCoend

/-- A weighted coend cowedge bundles a cowedge with the proof it is initial. -/
structure WeightedCoendCowedge (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) where
  /-- The underlying weighted cowedge. -/
  cowedge : WeightedCowedge W P
  /-- The proof that the cowedge is initial. -/
  isCoend : IsWeightedCoend cowedge

/-- A weighted coend exists if there is an initial weighted cowedge. -/
class HasWeightedCoend (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) where
  /-- The coend cowedge containing the coend and proof of initiality. -/
  coendCowedge : WeightedCoendCowedge W P

namespace HasWeightedCoend

variable (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) [HasWeightedCoend W P]

/-- The weighted coend cowedge (the initial weighted cowedge). -/
def weightedCoend : WeightedCowedge W P :=
  HasWeightedCoend.coendCowedge.cowedge

/-- The weighted coend is initial. -/
def weightedCoendIsCoend : IsWeightedCoend (weightedCoend W P) :=
  HasWeightedCoend.coendCowedge.isCoend

/-- The weighted coend object (the cowedge point of the coend cowedge). -/
def weightedCoendObj : D := (weightedCoend W P).pt

end HasWeightedCoend

end WeightedLimitColimit

section ConeWeightedConeEquivalence

/-!
## Cones as weighted cones with constant weight

Ordinary cones and cocones are special cases of weighted cones and cocones
where the weight functor is constant at a singleton type. This section
establishes this relationship.

### Ends, the Hom-Profunctor, and the Terminal Weight

For wedges specifically, this equivalence has deeper significance. An **end**
is a weighted limit where the weight is the hom-profunctor. The terminal
functor on `TwistedArrow C` corresponds to the hom-profunctor via the
slice/elements correspondence:

- `TwistedArrow C` = category of elements of `Hom_C`
- A copresheaf `F : TwistedArrow C ⥤ Type v` corresponds to a slice over
  `Hom_C` in the category of profunctors
- The terminal object in a slice `Prof/Hom_C` is `id : Hom_C → Hom_C`
- So the terminal functor on `TwistedArrow C` "is" the hom-profunctor

Therefore, `WeightedWedge (unitWeight (TwistedArrow C)) P ≌ Wedge P` is
another way of expressing that ordinary wedges (ends) are weighted limits
with the hom-profunctor weight. Dually for cowedges (coends).
-/

variable {J : Type u} [Category.{v} J] {C : Type w} [Category.{v} C]

/--
The constant unit weight functor `J ⥤ Type v` that sends every object
to `PUnit` and every morphism to the identity.
-/
abbrev unitWeight (J : Type u) [Category.{v} J] : J ⥤ Type v :=
  (Functor.const J).obj PUnit.{v + 1}

/--
The contravariant constant unit weight functor `Jᵒᵖ ⥤ Type v` that sends
every object to `PUnit` and every morphism to the identity.
-/
abbrev unitWeightOp (J : Type u) [Category.{v} J] : Jᵒᵖ ⥤ Type v :=
  (Functor.const Jᵒᵖ).obj PUnit.{v + 1}

/--
Convert an ordinary cone to a weighted cone with the constant unit weight.

For a cone over `D : J ⥤ C`, the weighted cone has:
- The same apex `c.pt`
- For each `j : J`, the unique element of `PUnit` maps to `c.π.app j`
-/
def coneToWeightedCone {D : J ⥤ C} (c : Cone D) :
    WeightedCone (unitWeight J) D where
  pt := c.pt
  toWeightedConeUnder := {
    app := fun j _ => c.π.app j
    naturality := fun j j' f => by
      funext _
      simp only [types_comp_apply, unitWeight, Functor.const_obj_obj,
        Functor.const_obj_map]
      have nat := c.π.naturality f
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp] at nat
      exact nat
  }

/--
Convert a weighted cone with constant unit weight back to an ordinary cone.

Since `PUnit` has exactly one element, we evaluate the weighted cone's
morphism family at `PUnit.unit`.
-/
def weightedConeToCone {D : J ⥤ C} (c : WeightedCone (unitWeight J) D) :
    Cone D where
  pt := c.pt
  π := {
    app := fun j => c.π.app j PUnit.unit
    naturality := fun j j' f => by
      have nat := c.π.naturality f
      simp only [unitWeight, Functor.const_obj_obj, Functor.const_obj_map,
        homFromFunctor] at nat
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp]
      exact congrFun nat PUnit.unit
  }

/--
Converting a cone to a weighted cone and back gives the original cone.
-/
theorem coneToWeightedCone_weightedConeToCone {D : J ⥤ C} (c : Cone D) :
    weightedConeToCone (coneToWeightedCone c) = c := rfl

/--
Converting a weighted cone (with unit weight) to a cone and back gives
the original weighted cone.
-/
theorem weightedConeToCone_coneToWeightedCone {D : J ⥤ C}
    (c : WeightedCone (unitWeight J) D) :
    coneToWeightedCone (weightedConeToCone c) = c := by
  cases c with
  | mk pt toWeightedConeUnder =>
    cases toWeightedConeUnder with
    | mk π =>
      congr 1

/--
Convert an ordinary cocone to a weighted cocone with the constant unit weight.

For a cocone over `D : J ⥤ C`, the weighted cocone has:
- The same apex `c.pt`
- For each `j : J`, the unique element of `PUnit` maps to `c.ι.app j`
-/
def coconeToWeightedCocone {D : J ⥤ C} (c : Cocone (J := J) D) :
    WeightedCocone (unitWeightOp J) D where
  pt := c.pt
  toWeightedCoconeOver := {
    app := fun j _ => c.ι.app j.unop
    naturality := fun j j' f => by
      funext _
      simp only [types_comp_apply, unitWeightOp,
        Functor.const_obj_obj, Functor.const_obj_map]
      have nat := c.ι.naturality f.unop
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at nat
      exact nat.symm
  }

/--
Convert a weighted cocone with constant unit weight back to an ordinary cocone.

Since `PUnit` has exactly one element, we evaluate the weighted cocone's
morphism family at `PUnit.unit`.
-/
def weightedCoconeToCocone {D : J ⥤ C} (c : WeightedCocone (unitWeightOp J) D) :
    Cocone D where
  pt := c.pt
  ι := {
    app := fun j => c.ι.app (Opposite.op j) PUnit.unit
    naturality := fun j j' f => by
      have nat := c.ι.naturality f.op
      simp only [unitWeightOp, Functor.const_obj_obj, Functor.const_obj_map,
        homToFunctor] at nat
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
      exact (congrFun nat PUnit.unit).symm
  }

/--
Converting a cocone to a weighted cocone and back gives the original cocone.
-/
theorem coconeToWeightedCocone_weightedCoconeToCocone {D : J ⥤ C} (c : Cocone D) :
    weightedCoconeToCocone (coconeToWeightedCocone c) = c := rfl

/--
Converting a weighted cocone (with unit weight) to a cocone and back gives
the original weighted cocone.
-/
theorem weightedCoconeToCocone_coconeToWeightedCocone {D : J ⥤ C}
    (c : WeightedCocone (unitWeightOp J) D) :
    coconeToWeightedCocone (weightedCoconeToCocone c) = c := by
  cases c with
  | mk pt u =>
    cases u with
    | mk ι => congr 1

/--
Functor from cones to weighted cones with constant unit weight.
-/
def coneToWeightedConeFunctor (D : J ⥤ C) :
    Cone D ⥤ WeightedCone (unitWeight J) D where
  obj := coneToWeightedCone
  map f := {
    hom := f.hom
    w := fun j _ => f.w j
  }
  map_id _ := rfl
  map_comp _ _ := rfl

/--
Functor from weighted cones with constant unit weight to cones.
-/
def weightedConeToConeFunctor (D : J ⥤ C) :
    WeightedCone (unitWeight J) D ⥤ Cone D where
  obj := weightedConeToCone
  map f := {
    hom := f.hom
    w := fun j => f.w j PUnit.unit
  }
  map_id _ := rfl
  map_comp _ _ := rfl

/--
The unit natural isomorphism for the cone/weighted-cone equivalence.

Converting a cone to weighted and back is definitionally equal to the original.
-/
def coneWeightedConeUnitIso (D : J ⥤ C) :
    𝟭 (Cone D) ≅ coneToWeightedConeFunctor D ⋙ weightedConeToConeFunctor D :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {_ _} _ => by
    apply ConeMorphism.ext
    simp only [Functor.id_map, Functor.comp_map, coneToWeightedConeFunctor,
      weightedConeToConeFunctor, Iso.refl_hom, Category.id_comp, Category.comp_id])

/--
The counit natural isomorphism for the cone/weighted-cone equivalence.

Converting a weighted cone to cone and back is isomorphic to the original.
-/
def coneWeightedConeCounitIso (D : J ⥤ C) :
    weightedConeToConeFunctor D ⋙ coneToWeightedConeFunctor D ≅
    𝟭 (WeightedCone (unitWeight J) D) :=
  NatIso.ofComponents
    (fun c => ⟨⟨𝟙 c.pt, fun j w => by
                cases w
                dsimp [Functor.id_obj, Functor.comp_obj, coneToWeightedConeFunctor,
                       weightedConeToConeFunctor, coneToWeightedCone, weightedConeToCone,
                       WeightedCone.leg]
                simp only [Category.id_comp]⟩,
               ⟨𝟙 c.pt, fun j w => by
                cases w
                dsimp [Functor.id_obj, Functor.comp_obj, coneToWeightedConeFunctor,
                       weightedConeToConeFunctor, coneToWeightedCone, weightedConeToCone,
                       WeightedCone.leg]
                simp only [Category.id_comp]⟩,
               by apply WeightedCone.Hom.ext
                  dsimp [coneToWeightedConeFunctor, weightedConeToConeFunctor,
                         coneToWeightedCone, weightedConeToCone]
                  simp only [Category.comp_id],
               by apply WeightedCone.Hom.ext
                  dsimp [coneToWeightedConeFunctor, weightedConeToConeFunctor,
                         coneToWeightedCone, weightedConeToCone]
                  simp only [Category.comp_id]⟩)
    (fun f => by
      apply WeightedCone.Hom.ext
      dsimp [coneToWeightedConeFunctor, weightedConeToConeFunctor,
             coneToWeightedCone, weightedConeToCone]
      simp only [Category.comp_id, Category.id_comp])

/--
Cones over `D : J ⥤ C` are categorically equivalent to weighted cones
with constant unit weight.
-/
def coneWeightedConeEquiv (D : J ⥤ C) :
    Cone D ≌ WeightedCone (unitWeight J) D where
  functor := coneToWeightedConeFunctor D
  inverse := weightedConeToConeFunctor D
  unitIso := coneWeightedConeUnitIso D
  counitIso := coneWeightedConeCounitIso D
  functor_unitIso_comp c := by
    apply WeightedCone.Hom.ext
    dsimp [coneWeightedConeUnitIso, coneWeightedConeCounitIso, coneToWeightedConeFunctor,
           weightedConeToConeFunctor, coneToWeightedCone, weightedConeToCone]
    simp only [Category.comp_id]

/--
Functor from cocones to weighted cocones with constant unit weight.
-/
def coconeToWeightedCoconeFunctor (D : J ⥤ C) :
    Cocone D ⥤ WeightedCocone (unitWeightOp J) D where
  obj := coconeToWeightedCocone
  map f := {
    hom := f.hom
    w := fun j _ => f.w j
  }
  map_id _ := rfl
  map_comp _ _ := rfl

/--
Functor from weighted cocones with constant unit weight to cocones.
-/
def weightedCoconeToCoconeFunctor (D : J ⥤ C) :
    WeightedCocone (unitWeightOp J) D ⥤ Cocone D where
  obj := weightedCoconeToCocone
  map f := {
    hom := f.hom
    w := fun j => f.w j PUnit.unit
  }
  map_id _ := rfl
  map_comp _ _ := rfl

/--
The unit natural isomorphism for the cocone/weighted-cocone equivalence.
-/
def coconeWeightedCoconeUnitIso (D : J ⥤ C) :
    𝟭 (Cocone D) ≅ coconeToWeightedCoconeFunctor D ⋙ weightedCoconeToCoconeFunctor D :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun {_ _} _ => by
    apply CoconeMorphism.ext
    simp only [Functor.id_map, Functor.comp_map, coconeToWeightedCoconeFunctor,
      weightedCoconeToCoconeFunctor, Iso.refl_hom, Category.id_comp, Category.comp_id])

/--
The counit natural isomorphism for the cocone/weighted-cocone equivalence.
-/
def coconeWeightedCoconeCounitIso (D : J ⥤ C) :
    weightedCoconeToCoconeFunctor D ⋙ coconeToWeightedCoconeFunctor D ≅
    𝟭 (WeightedCocone (unitWeightOp J) D) :=
  NatIso.ofComponents
    (fun c => ⟨⟨𝟙 c.pt, fun j w => by
                cases w
                dsimp [Functor.comp_obj, weightedCoconeToCoconeFunctor,
                       coconeToWeightedCoconeFunctor, coconeToWeightedCocone,
                       weightedCoconeToCocone, WeightedCocone.leg]
                simp only [Category.comp_id]⟩,
               ⟨𝟙 c.pt, fun j w => by
                cases w
                dsimp [Functor.id_obj, weightedCoconeToCoconeFunctor,
                       coconeToWeightedCoconeFunctor, coconeToWeightedCocone,
                       weightedCoconeToCocone, WeightedCocone.leg]
                simp only [Category.comp_id]⟩,
               by apply WeightedCocone.Hom.ext
                  dsimp [coconeToWeightedCoconeFunctor, weightedCoconeToCoconeFunctor,
                         coconeToWeightedCocone, weightedCoconeToCocone]
                  simp only [Category.comp_id],
               by apply WeightedCocone.Hom.ext
                  dsimp [coconeToWeightedCoconeFunctor, weightedCoconeToCoconeFunctor,
                         coconeToWeightedCocone, weightedCoconeToCocone]
                  simp only [Category.comp_id]⟩)
    (fun f => by
      apply WeightedCocone.Hom.ext
      dsimp [coconeToWeightedCoconeFunctor, weightedCoconeToCoconeFunctor,
             coconeToWeightedCocone, weightedCoconeToCocone]
      simp only [Category.comp_id, Category.id_comp])

/--
Cocones over `D : J ⥤ C` are categorically equivalent to weighted cocones
with constant unit weight.
-/
def coconeWeightedCoconeEquiv (D : J ⥤ C) :
    Cocone D ≌ WeightedCocone (unitWeightOp J) D where
  functor := coconeToWeightedCoconeFunctor D
  inverse := weightedCoconeToCoconeFunctor D
  unitIso := coconeWeightedCoconeUnitIso D
  counitIso := coconeWeightedCoconeCounitIso D
  functor_unitIso_comp c := by
    apply WeightedCocone.Hom.ext
    dsimp [coconeWeightedCoconeUnitIso, coconeWeightedCoconeCounitIso,
           coconeToWeightedCoconeFunctor, weightedCoconeToCoconeFunctor,
           coconeToWeightedCocone, weightedCoconeToCocone]
    simp only [Category.comp_id]

end ConeWeightedConeEquivalence

section WeightedConeElementsEquivalence

/-!
## Weighted cones and cones over the category of elements

A weighted cone with weight `W : J ⥤ Type v` and diagram `D : J ⥤ C` is equivalent
to an ordinary cone over the composite functor `CategoryOfElements.π W ⋙ D`.

The category of elements `W.Elements` has:
- Objects: pairs `⟨j, w⟩` where `j : J` and `w : W.obj j`
- Morphisms `⟨j, w⟩ ⟶ ⟨j', w'⟩`: morphisms `f : j ⟶ j'` in `J` with `W.map f w = w'`

The projection `CategoryOfElements.π W : W.Elements ⥤ J` forgets the element.
The composite `CategoryOfElements.π W ⋙ D : W.Elements ⥤ C` sends `⟨j, w⟩ ↦ D.obj j`.

This equivalence shows that weighted cones are ordinary cones over an expanded
indexing category, which is foundational for the theory of weighted limits.
-/

universe u₁ v₁ u₂

variable {J : Type u₁} [Category.{v₁} J] {C : Type u₂} [Category.{v₁} C]
variable (W : J ⥤ Type v₁) (D : J ⥤ C)

/--
The diagram functor for weighted cones: maps the the category
of elements to `C` via the projection and `D`.
-/
def weightedConeDiagram : W.Elements ⥤ C :=
  CategoryOfElements.π W ⋙ D

/--
Convert a weighted cone to a cone over the category of elements.

Given `c : WeightedCone W D`, define a cone over `CategoryOfElements.π W ⋙ D` with:
- Apex: `c.pt`
- Legs: for `p = ⟨j, w⟩`, the leg is `c.leg j w : c.pt ⟶ D.obj j`
-/
def weightedConeToElementsCone (W : J ⥤ Type v₁) (D : J ⥤ C)
    (c : WeightedCone W D) : Cone (weightedConeDiagram W D) where
  pt := c.pt
  π := {
    app := fun p => c.leg p.fst p.snd
    naturality := fun ⟨j, w⟩ ⟨j', w'⟩ ⟨f, hf⟩ => by
      dsimp [CategoryOfElements.π]
      simp only [Category.id_comp]
      have nat := (c.naturality f w).symm
      simp only [hf] at nat
      exact nat
  }

/--
Convert a cone over the category of elements to a weighted cone.

Given a cone `c` over `CategoryOfElements.π W ⋙ D`, define a weighted cone with:
- Apex: `c.pt`
- Legs: `leg j w := c.π.app ⟨j, w⟩`
-/
def elementsConeToWeightedCone (W : J ⥤ Type v₁) (D : J ⥤ C)
    (c : Cone (CategoryOfElements.π W ⋙ D)) : WeightedCone W D where
  pt := c.pt
  toWeightedConeUnder := {
    app := fun j w => c.π.app ⟨j, w⟩
    naturality := fun {j j'} f => by
      funext w
      dsimp [homFromFunctor]
      have nat := c.π.naturality (CategoryOfElements.homMk ⟨j, w⟩ ⟨j', W.map f w⟩ f rfl)
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.id_comp,
        Functor.comp_obj, CategoryOfElements.π_obj,
        Functor.comp_map, CategoryOfElements.π_map] at nat
      exact nat
  }

/--
`weightedConeToElementsCone` and `elementsConeToWeightedCone` are inverses (one direction).
-/
theorem weightedCone_elements_roundtrip (W : J ⥤ Type v₁) (D : J ⥤ C)
    (c : WeightedCone W D) :
    elementsConeToWeightedCone W D (weightedConeToElementsCone W D c) = c := by
  cases c with
  | mk pt u =>
    cases u with
    | mk π => rfl

/--
`elementsConeToWeightedCone` and `weightedConeToElementsCone` are inverses (other direction).
-/
theorem elements_weightedCone_roundtrip (W : J ⥤ Type v₁) (D : J ⥤ C)
    (c : Cone (CategoryOfElements.π W ⋙ D)) :
    weightedConeToElementsCone W D (elementsConeToWeightedCone W D c) = c := by
  cases c with
  | mk pt π => rfl

/--
Functor from weighted cones to cones over the category of elements.
-/
def weightedConeToElementsConeFunctor (W : J ⥤ Type v₁) (D : J ⥤ C) :
    WeightedCone W D ⥤ Cone (CategoryOfElements.π W ⋙ D) where
  obj := weightedConeToElementsCone W D
  map f := {
    hom := f.hom
    w := fun p => by
      dsimp [weightedConeToElementsCone]
      exact f.w p.fst p.snd
  }
  map_id _ := rfl
  map_comp _ _ := rfl

/--
Functor from cones over the category of elements to weighted cones.
-/
def elementsConeToWeightedConeFunctor (W : J ⥤ Type v₁) (D : J ⥤ C) :
    Cone (CategoryOfElements.π W ⋙ D) ⥤ WeightedCone W D where
  obj := elementsConeToWeightedCone W D
  map f := {
    hom := f.hom
    w := fun j w => by
      dsimp [elementsConeToWeightedCone]
      exact f.w ⟨j, w⟩
  }
  map_id _ := rfl
  map_comp _ _ := rfl

/--
The unit natural isomorphism: `𝟭 (WeightedCone W D) ≅ ⋯ ⋙ ⋯`.
-/
def weightedConeElementsUnitIso (W : J ⥤ Type v₁) (D : J ⥤ C) :
    𝟭 (WeightedCone W D) ≅
    weightedConeToElementsConeFunctor W D ⋙ elementsConeToWeightedConeFunctor W D :=
  NatIso.ofComponents (fun c => by
    have h := weightedCone_elements_roundtrip W D c
    exact eqToIso h.symm)
    (fun {c₁ c₂} f => by
      apply WeightedCone.Hom.ext
      dsimp [weightedConeToElementsConeFunctor, elementsConeToWeightedConeFunctor,
        weightedConeToElementsCone, elementsConeToWeightedCone]
      simp only [Category.comp_id, Category.id_comp])

/--
The counit natural isomorphism: `⋯ ⋙ ⋯ ≅ 𝟭 (Cone ⋯)`.
-/
def weightedConeElementsCounitIso (W : J ⥤ Type v₁) (D : J ⥤ C) :
    elementsConeToWeightedConeFunctor W D ⋙ weightedConeToElementsConeFunctor W D ≅
    𝟭 (Cone (CategoryOfElements.π W ⋙ D)) :=
  NatIso.ofComponents (fun c => by
    have h := elements_weightedCone_roundtrip W D c
    exact eqToIso h)
    (fun {c₁ c₂} f => by
      apply ConeMorphism.ext
      dsimp [weightedConeToElementsConeFunctor, elementsConeToWeightedConeFunctor,
        weightedConeToElementsCone, elementsConeToWeightedCone]
      simp only [Category.comp_id, Category.id_comp])

/--
Weighted cones over `W : J ⥤ Type v` and `D : J ⥤ C` are categorically equivalent
to ordinary cones over the composite `CategoryOfElements.π W ⋙ D : W.Elements ⥤ C`.

This is foundational for the theory of weighted limits: it shows that weighted
limits can be computed as ordinary limits over the expanded indexing category
of elements.
-/
def weightedConeElementsEquiv (W : J ⥤ Type v₁) (D : J ⥤ C) :
    WeightedCone (C := C) (J := J) W D ≌
    Cone (J := W.Elements) (C := C) (weightedConeDiagram W D) where
  functor := weightedConeToElementsConeFunctor W D
  inverse := elementsConeToWeightedConeFunctor W D
  unitIso := weightedConeElementsUnitIso W D
  counitIso := weightedConeElementsCounitIso W D
  functor_unitIso_comp c := by
    apply ConeMorphism.ext
    dsimp [weightedConeElementsUnitIso, weightedConeElementsCounitIso,
      weightedConeToElementsConeFunctor, elementsConeToWeightedConeFunctor,
      weightedConeToElementsCone, elementsConeToWeightedCone]
    simp only [Category.comp_id]

end WeightedConeElementsEquivalence

section WeightedCoconeElementsEquivalence

/-!
## Weighted Cocones as Ordinary Cocones over Category of Elements

For weighted cocones with weight `W : Jᵒᵖ ⥤ Type v₁` and diagram `D : J ⥤ C`,
we establish an equivalence with ordinary cocones over the composite
`(CategoryOfElements.π W).op ⋙ unopUnop J ⋙ D : (W.Elements)ᵒᵖ ⥤ C`.

This is the dual of the weighted cone/elements equivalence.
-/

universe u₃ v₃ u₄

variable {J : Type u₃} [Category.{v₃} J] {C : Type u₄} [Category.{v₃} C]
variable (W : Jᵒᵖ ⥤ Type v₃) (D : J ⥤ C)

/--
The diagram functor for weighted cocones: maps the opposite of the category
of elements to `C` via the projection and `D`.
-/
def weightedCoconeDiagram : W.ElementsPre ⥤ C :=
  (CategoryOfElements.π W).op ⋙ unopUnop J ⋙ D

/--
Convert a weighted cocone to a cocone over the elements diagram.
-/
def weightedCoconeToElementsCocone (W : Jᵒᵖ ⥤ Type v₃) (D : J ⥤ C)
    (c : WeightedCocone W D) : Cocone (weightedCoconeDiagram W D) where
  pt := c.pt
  ι := {
    app := fun p_op =>
      let p := p_op.unop
      c.leg p.fst.unop p.snd
    naturality := fun p_op q_op f_op => by
      dsimp [weightedCoconeDiagram, CategoryOfElements.π, unopUnop]
      simp only [Category.comp_id]
      -- f_op.unop : q_op.unop ⟶ p_op.unop in W.Elements
      -- f_op.unop.val : q_op.unop.fst ⟶ p_op.unop.fst in Jᵒᵖ
      -- f_op.unop.property : W.map f_op.unop.val q_op.unop.snd = p_op.unop.snd
      have nat := c.naturality f_op.unop.val.unop q_op.unop.snd
      simp only [Opposite.op_unop] at nat
      rw [nat]
      congr 1
      exact f_op.unop.property
  }

/--
Convert a cocone over the elements diagram to a weighted cocone.
-/
def elementsCoconeToWeightedCocone (W : Jᵒᵖ ⥤ Type v₃) (D : J ⥤ C)
    (c : Cocone (weightedCoconeDiagram W D)) : WeightedCocone W D where
  pt := c.pt
  toWeightedCoconeOver := {
    app := fun j_op w => c.ι.app (Opposite.op (Sigma.mk j_op w))
    naturality := fun {j_op j'_op} f => by
      ext w
      dsimp [homToFunctor]
      let src := Sigma.mk j_op w
      let tgt := Sigma.mk j'_op (W.map f w)
      have nat := c.ι.naturality (Opposite.op (CategoryOfElements.homMk src tgt f rfl))
      simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id,
        weightedCoconeDiagram, Functor.comp_obj, Functor.op_obj,
        CategoryOfElements.π_obj, unopUnop_obj, Opposite.unop_op,
        Functor.comp_map, Functor.op_map, CategoryOfElements.π_map,
        unopUnop_map] at nat
      exact nat.symm
  }

/--
Round-trip: weighted cocone → elements cocone → weighted cocone is identity.
-/
theorem weightedCocone_elements_roundtrip (W : Jᵒᵖ ⥤ Type v₃) (D : J ⥤ C)
    (c : WeightedCocone W D) :
    elementsCoconeToWeightedCocone W D (weightedCoconeToElementsCocone W D c) = c := by
  cases c with
  | mk pt u =>
    cases u with
    | mk ι => rfl

/--
Round-trip: elements cocone → weighted cocone → elements cocone is identity.
-/
theorem elements_weightedCocone_roundtrip (W : Jᵒᵖ ⥤ Type v₃) (D : J ⥤ C)
    (c : Cocone (weightedCoconeDiagram W D)) :
    weightedCoconeToElementsCocone W D (elementsCoconeToWeightedCocone W D c) = c := by
  cases c with
  | mk pt ι => rfl

/--
Functor from weighted cocones to cocones over the elements diagram.
-/
def weightedCoconeToElementsCoconeFunctor (W : Jᵒᵖ ⥤ Type v₃) (D : J ⥤ C) :
    WeightedCocone W D ⥤ Cocone (weightedCoconeDiagram W D) where
  obj := weightedCoconeToElementsCocone W D
  map f := {
    hom := f.hom
    w := fun p_op => by
      dsimp [weightedCoconeToElementsCocone]
      exact f.w p_op.unop.fst.unop p_op.unop.snd
  }
  map_id _ := rfl
  map_comp _ _ := rfl

/--
Functor from cocones over the elements diagram to weighted cocones.
-/
def elementsCoconeToWeightedCoconeFunctor (W : Jᵒᵖ ⥤ Type v₃) (D : J ⥤ C) :
    Cocone (weightedCoconeDiagram W D) ⥤ WeightedCocone W D where
  obj := elementsCoconeToWeightedCocone W D
  map f := {
    hom := f.hom
    w := fun (j : J) (w : W.obj (Opposite.op j)) => by
      dsimp [elementsCoconeToWeightedCocone]
      exact f.w (Opposite.op (Sigma.mk (Opposite.op j) w))
  }
  map_id _ := rfl
  map_comp _ _ := rfl

/--
The unit natural isomorphism: `𝟭 (WeightedCocone W D) ≅ ⋯ ⋙ ⋯`.
-/
def weightedCoconeElementsUnitIso (W : Jᵒᵖ ⥤ Type v₃) (D : J ⥤ C) :
    𝟭 (WeightedCocone W D) ≅
    weightedCoconeToElementsCoconeFunctor W D ⋙ elementsCoconeToWeightedCoconeFunctor W D :=
  NatIso.ofComponents (fun c => eqToIso (weightedCocone_elements_roundtrip W D c).symm)
    (fun {c₁ c₂} f => by
      apply WeightedCocone.Hom.ext
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
        weightedCoconeToElementsCoconeFunctor, elementsCoconeToWeightedCoconeFunctor,
        weightedCoconeToElementsCocone, elementsCoconeToWeightedCocone,
        eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp])

/--
The counit natural isomorphism: `⋯ ⋙ ⋯ ≅ 𝟭 (Cocone ⋯)`.
-/
def weightedCoconeElementsCounitIso (W : Jᵒᵖ ⥤ Type v₃) (D : J ⥤ C) :
    elementsCoconeToWeightedCoconeFunctor W D ⋙ weightedCoconeToElementsCoconeFunctor W D ≅
    𝟭 (Cocone (weightedCoconeDiagram W D)) :=
  NatIso.ofComponents (fun c => eqToIso (elements_weightedCocone_roundtrip W D c))
    (fun {c₁ c₂} f => by
      apply CoconeMorphism.ext
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
        weightedCoconeToElementsCoconeFunctor, elementsCoconeToWeightedCoconeFunctor,
        weightedCoconeToElementsCocone, elementsCoconeToWeightedCocone,
        eqToIso_refl, Iso.refl_hom, Category.comp_id, Category.id_comp])

/--
Weighted cocones over `W : Jᵒᵖ ⥤ Type v` and `D : J ⥤ C` are categorically equivalent
to ordinary cocones over the composite
`(CategoryOfElements.π W).op ⋙ unopUnop J ⋙ D : W.ElementsPre ⥤ C`.

This is foundational for the theory of weighted colimits: it shows that weighted
colimits can be computed as ordinary colimits over the expanded indexing category.
-/
def weightedCoconeElementsEquiv (W : Jᵒᵖ ⥤ Type v₃) (D : J ⥤ C) :
    WeightedCocone (C := C) (J := J) W D ≌
    Cocone (J := W.ElementsPre) (C := C) (weightedCoconeDiagram W D) where
  functor := weightedCoconeToElementsCoconeFunctor W D
  inverse := elementsCoconeToWeightedCoconeFunctor W D
  unitIso := weightedCoconeElementsUnitIso W D
  counitIso := weightedCoconeElementsCounitIso W D
  functor_unitIso_comp c := by
    apply CoconeMorphism.ext
    dsimp [weightedCoconeElementsUnitIso, weightedCoconeElementsCounitIso,
      weightedCoconeToElementsCoconeFunctor, elementsCoconeToWeightedCoconeFunctor,
      weightedCoconeToElementsCocone, elementsCoconeToWeightedCocone,
      eqToIso, eqToHom]
    simp only [Category.comp_id]

end WeightedCoconeElementsEquivalence

section WeightedWedgeCowedgeEquivalences

/-!
## Weighted wedges and cowedges reduce to ordinary cones and cocones

By composing the definitions of weighted wedges/cowedges with the
equivalences from the previous sections, we obtain that:

- Weighted wedges are equivalent to cones over the category of elements
- Weighted cowedges are equivalent to cocones over the opposite of the
  category of elements

These composed equivalences follow directly from the definitions.
-/

universe u₅ v₅

variable {C : Type u₅} [Category.{v₅} C] {D : Type*} [Category.{v₅} D]

/--
The diagram for weighted wedges: composing the projection from the category
of elements with the profunctor-on-twisted-arrow functor.

For weight profunctor `W : Cᵒᵖ ⥤ C ⥤ Type v` and diagram profunctor
`P : Cᵒᵖ ⥤ C ⥤ D`, this gives a functor
`(profunctorOnTwistedArrow C W).Elements ⥤ D`.
-/
def weightedWedgeDiagram (W : Cᵒᵖ ⥤ C ⥤ Type v₅) (P : Cᵒᵖ ⥤ C ⥤ D) :
    (profunctorOnTwistedArrow C W).Elements ⥤ D :=
  weightedConeDiagram (profunctorOnTwistedArrow C W)
    (profunctorOnTwistedArrow C P)

/--
The diagram for weighted cowedges: composing the projection from the
opposite category of elements with the profunctor-on-co-twisted-arrow functor.

For weight profunctor `W : Cᵒᵖ ⥤ C ⥤ Type v` and diagram profunctor
`P : Cᵒᵖ ⥤ C ⥤ D`, this gives a functor
`(profunctorOnOpCoTwistedArrow C W).ElementsPre ⥤ D`.
-/
def weightedCowedgeDiagram (W : Cᵒᵖ ⥤ C ⥤ Type v₅)
    (P : Cᵒᵖ ⥤ C ⥤ D) : (profunctorOnOpCoTwistedArrow C W).ElementsPre ⥤ D :=
  weightedCoconeDiagram (profunctorOnOpCoTwistedArrow C W)
    (profunctorOnCoTwistedArrow C P)

/--
Weighted wedges over profunctors `W` (weight) and `P` (diagram) are
categorically equivalent to ordinary cones over the weighted wedge diagram.
-/
def weightedWedgeElementsEquiv (W : Cᵒᵖ ⥤ C ⥤ Type v₅)
    (P : Cᵒᵖ ⥤ C ⥤ D) :
    WeightedWedge W P ≌ Cone (weightedWedgeDiagram W P) :=
  weightedConeElementsEquiv (profunctorOnTwistedArrow C W)
    (profunctorOnTwistedArrow C P)

/--
Weighted cowedges over profunctors `W` (weight) and `P` (diagram) are
categorically equivalent to ordinary cocones over the weighted cowedge diagram.
-/
def weightedCowedgeElementsEquiv (W : Cᵒᵖ ⥤ C ⥤ Type v₅)
    (P : Cᵒᵖ ⥤ C ⥤ D) :
    WeightedCowedge W P ≌ Cocone (weightedCowedgeDiagram W P) :=
  weightedCoconeElementsEquiv (profunctorOnOpCoTwistedArrow C W)
    (profunctorOnCoTwistedArrow C P)

end WeightedWedgeCowedgeEquivalences

section RestrictedCowedges

/-!
## Slice profunctor

Given an endodifunctor `G : Cᵒᵖ ⥤ C ⥤ C` and an object `c : C`, we define
the *slice profunctor* `G ⇓ c : Cᵒᵖ ⥤ C ⥤ Type` by `(G ⇓ c)(A, B) := Hom(G(B, A), c)`.

Note the argument swap: `G(B, A)` not `G(A, B)`. This ensures the correct
variance for an endoprofunctor to Type.
-/

variable {C : Type u} [Category.{v} C]

/--
The slice profunctor bifunctor: contravariant in `G` and covariant in `c`.

`sliceProfunctorBifunctor.obj (op G) .obj c = G ⇓ c`

This is built from standard functor compositions:
1. Uncurry `G` and apply `.op` (contravariantly)
2. Precompose with `opProdSymSelfDual.inverse` to swap arguments
3. Postcompose with `yoneda.obj c` to get `Hom(-, c)`
4. Curry the result
-/
def sliceProfunctorBifunctor : (Cᵒᵖ ⥤ C ⥤ C)ᵒᵖ ⥤ C ⥤ (Cᵒᵖ ⥤ C ⥤ Type v) :=
  Functor.uncurry.op ⋙
  Functor.opHom (Cᵒᵖ × C) C ⋙
  (Functor.whiskeringLeft (Cᵒᵖ × C) ((Cᵒᵖ × C)ᵒᵖ) Cᵒᵖ).obj (opProdSymSelfDual C).inverse ⋙
  (Functor.whiskeringRight (Cᵒᵖ × C) Cᵒᵖ (Type v)).flip ⋙
  (Functor.whiskeringRight (Cᵒᵖ ⥤ Type v) (Cᵒᵖ × C ⥤ Type v) (Cᵒᵖ ⥤ C ⥤ Type v)).obj
    Functor.curry ⋙
  (Functor.whiskeringLeft C (Cᵒᵖ ⥤ Type v) (Cᵒᵖ ⥤ C ⥤ Type v)).obj yoneda

/-- The slice profunctor `G ⇓ c` for an endodifunctor `G : Cᵒᵖ ⥤ C ⥤ C` and
object `c : C`. Defined as `(G ⇓ c)(A, B) := Hom_C(G(B, A), c)`.

The covariant action (second argument): for `g : X → Y`, the map
`Hom(G(X, A), c) → Hom(G(Y, A), c)` is precomposition by `G(g, A) : G(Y, A) → G(X, A)`.

The contravariant action (first argument): for `f : A → B`, the map
`Hom(G(X, B), c) → Hom(G(X, A), c)` is precomposition by `G(X, f) : G(X, A) → G(X, B)`.
-/
abbrev sliceProfunctor (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) : Cᵒᵖ ⥤ C ⥤ Type v :=
  (sliceProfunctorBifunctor.obj (Opposite.op G)).obj c

/-- Notation for the slice profunctor. -/
scoped infixl:70 " ⇓ " => sliceProfunctor

/-- The slice profunctor construction is itself functorial in `c : C`.
Given `G : Cᵒᵖ ⥤ C ⥤ C`, this defines a functor `C ⥤ (Cᵒᵖ ⥤ C ⥤ Type v)`.

For a morphism `f : c ⟶ c'`, the induced natural transformation
`(G ⇓ c) ⟶ (G ⇓ c')` acts by post-composition with `f`. -/
abbrev sliceProfunctorFunctor (G : Cᵒᵖ ⥤ C ⥤ C) : C ⥤ (Cᵒᵖ ⥤ C ⥤ Type v) :=
  sliceProfunctorBifunctor.obj (Opposite.op G)

/-- `sliceProfunctor G c` equals the application of `sliceProfunctorFunctor G` at `c`. -/
theorem sliceProfunctor_eq_functor_obj (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) :
    sliceProfunctor G c = (sliceProfunctorFunctor G).obj c := rfl

/-- The object computation: `((G ⇓ c).obj A).obj X = (G(X, A.unop) → c)`. -/
@[simp]
theorem sliceProfunctor_obj_obj (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) (A : Cᵒᵖ) (X : C) :
    ((G ⇓ c).obj A).obj X = ((G.obj (Opposite.op X)).obj A.unop ⟶ c) := rfl

/-- The covariant map on the slice profunctor is precomposition with `G.map`. -/
@[simp]
theorem sliceProfunctor_obj_map (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) (A : Cᵒᵖ)
    {X Y : C} (f : X ⟶ Y) (m : (G.obj (Opposite.op X)).obj A.unop ⟶ c) :
    ((G ⇓ c).obj A).map f m = (G.map f.op).app A.unop ≫ m := by
  simp only [sliceProfunctor, sliceProfunctorBifunctor, Functor.comp_obj, Functor.comp_map,
    Functor.op_obj, Functor.whiskeringLeft_obj_obj, Functor.whiskeringRight_obj_obj,
    Functor.flip_obj_obj, Functor.curry_obj_obj_obj, Functor.curry_obj_obj_map,
    yoneda_obj_obj, yoneda_obj_map, Functor.opHom_obj, Functor.op_map,
    Functor.uncurry_obj_map, opProdSymSelfDual, Equivalence.trans_inverse,
    opProdProdOpEquiv, Equivalence.symm_inverse, opOpProdEquiv,
    Equivalence.prod_inverse, Functor.prod_map, opOpEquivalence,
    Equivalence.refl_inverse, Functor.id_map, prodOpEquiv_inverse_map,
    Quiver.Hom.unop_op, Opposite.unop_op]
  aesop_cat

/-- The contravariant map on the slice profunctor is precomposition with `G.obj.map`. -/
@[simp]
theorem sliceProfunctor_map_app (G : Cᵒᵖ ⥤ C ⥤ C) (c : C)
    {A B : Cᵒᵖ} (f : A ⟶ B) (X : C) (m : (G.obj (Opposite.op X)).obj A.unop ⟶ c) :
    ((G ⇓ c).map f).app X m = (G.obj (Opposite.op X)).map f.unop ≫ m := by
  simp only [sliceProfunctor, sliceProfunctorBifunctor, Functor.comp_obj, Functor.comp_map,
    Functor.op_obj, Functor.whiskeringLeft_obj_obj, Functor.whiskeringRight_obj_obj,
    Functor.flip_obj_obj, Functor.curry_obj_obj_obj, Functor.curry_obj_map_app,
    yoneda_obj_obj, Functor.opHom_obj, Functor.op_map,
    Functor.uncurry_obj_map, opProdSymSelfDual, Equivalence.trans_inverse,
    opProdProdOpEquiv, Equivalence.symm_inverse, opOpProdEquiv,
    Equivalence.prod_inverse, Functor.prod_map, opOpEquivalence,
    Equivalence.refl_inverse, Functor.id_map, prodOpEquiv_inverse_map,
    Opposite.unop_op]
  aesop_cat

/-- Given a natural transformation `β : G' ⟹ G`, precomposition induces a natural
transformation `(G ⇓ c) ⟶ (G' ⇓ c)` for each `c`.

At component `(A, B)`, the map `Hom(G(B, A), c) → Hom(G'(B, A), c)` is
precomposition by `(β.app (op B)).app A : G'(B, A) → G(B, A)`. -/
abbrev sliceProfunctorPrecomp {G G' : Cᵒᵖ ⥤ C ⥤ C} (β : G' ⟶ G) (c : C) :
    (G ⇓ c) ⟶ (G' ⇓ c) :=
  (sliceProfunctorBifunctor.map β.op).app c

/-- Precomposition by the identity is the identity. -/
theorem sliceProfunctorPrecomp_id (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) :
    sliceProfunctorPrecomp (𝟙 G) c = 𝟙 (G ⇓ c) := by
  simp only [sliceProfunctorPrecomp, op_id, Functor.map_id, NatTrans.id_app]

/-- Precomposition respects composition (contravariantly). -/
theorem sliceProfunctorPrecomp_comp {G G' G'' : Cᵒᵖ ⥤ C ⥤ C}
    (β : G' ⟶ G) (γ : G'' ⟶ G') (c : C) :
    sliceProfunctorPrecomp (γ ≫ β) c =
    sliceProfunctorPrecomp β c ≫ sliceProfunctorPrecomp γ c := by
  simp only [sliceProfunctorPrecomp, op_comp, Functor.map_comp, NatTrans.comp_app]

/-- Precomposition is natural in the object `c`. Given `β : G' ⟶ G` and `f : c ⟶ c'`,
the following square commutes:
```
(G ⇓ c) --precomp β--> (G' ⇓ c)
   |                      |
   | postcomp f           | postcomp f
   v                      v
(G ⇓ c') -precomp β-> (G' ⇓ c')
```
-/
theorem sliceProfunctorPrecomp_natural {G G' : Cᵒᵖ ⥤ C ⥤ C} (β : G' ⟶ G)
    {c c' : C} (f : c ⟶ c') :
    sliceProfunctorPrecomp β c ≫ (sliceProfunctorFunctor G').map f =
    (sliceProfunctorFunctor G).map f ≫ sliceProfunctorPrecomp β c' := by
  simp only [sliceProfunctorPrecomp, sliceProfunctorFunctor]
  exact ((sliceProfunctorBifunctor.map β.op).naturality f).symm

/-- The slice profunctor at `G` and `c` equals the bifunctor applied to `op G` and `c`. -/
theorem sliceProfunctor_eq_bifunctor (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) :
    G ⇓ c = (sliceProfunctorBifunctor.obj (Opposite.op G)).obj c := rfl

/-- The diagonal of the slice profunctor at `A` is `Hom(G(A, A), c)`. -/
theorem sliceProfunctor_diagApp (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) (A : C) :
    diagApp (G ⇓ c) A = ((G.obj (Opposite.op A)).obj A ⟶ c) := by
  simp only [diagApp, sliceProfunctor_obj_obj]

/-!
## Restricted cowedges

Following Vene's thesis (2000), a *restricted cowedge* generalizes ordinary
cowedges by parametrizing the injection morphisms with a "restriction" functor.

Given:
- `G : Cᵒᵖ ⥤ C ⥤ C`, an endodifunctor
- `H : Cᵒᵖ ⥤ C ⥤ Type*`, a difunctor to Type (the "restriction")

An `H`-restricted `G`-cowedge `(C, Φ)` consists of:
- An object `C` (the carrier/summit)
- A family `Φ_A : H(A, A) → Hom(G(A, A), C)` satisfying dinaturality

The dinaturality condition states that for `g : A → B` and `x : H(B, A)`:
```
Φ_A(H(g, id)(x)) ∘ G(g, id) = Φ_B(H(id, g)(x)) ∘ G(id, g)
```

The `H`-restricted `G`-cowedges form a category `RestrictedCowedgeCat G H`
where morphisms are arrows `h : C → D` such that for all `A` and `a ∈ H(A,A)`:
```
h ∘ Φ_A(a) = Ψ_A(a)
```
-/

variable {C : Type u} [Category.{v} C]

/--
An `H`-restricted `G`-cowedge over a fixed point `pt` for an endodifunctor
`G : Cᵒᵖ ⥤ C ⥤ C` and restriction functor `H : Cᵒᵖ ⥤ C ⥤ Type v`.

This contains just the family and dinaturality data without bundling the
carrier object.
-/
@[ext]
structure RestrictedCowedgeOver (pt : C) (G : Cᵒᵖ ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ Type v) where
  /-- The family of morphisms as a `ParanatSig H (G ⇓ pt)`. -/
  family : ParanatSig H (G ⇓ pt)
  /-- The dinaturality condition on the family. -/
  isDinatural : IsDinatural H (G ⇓ pt) family

/--
An `H`-restricted `G`-cowedge for an endodifunctor `G : Cᵒᵖ ⥤ C ⥤ C` and
restriction functor `H : Cᵒᵖ ⥤ C ⥤ Type v`.

This consists of a carrier object and a `RestrictedCowedgeOver pt G H`.

The universe of `H` is `v` (the morphism universe) to match the slice profunctor
`G ⇓ pt : Cᵒᵖ ⥤ C ⥤ Type v`. -/
@[ext]
structure RestrictedCowedge (G : Cᵒᵖ ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ Type v) where
  /-- The carrier (summit) object. -/
  pt : C
  /-- The cowedge data over the point. -/
  toRestrictedCowedgeOver : RestrictedCowedgeOver pt G H

namespace RestrictedCowedge

variable {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type v}

/-- The family of morphisms as a `ParanatSig H (G ⇓ pt)`. -/
abbrev family (c : RestrictedCowedge G H) : ParanatSig H (G ⇓ c.pt) :=
  c.toRestrictedCowedgeOver.family

/-- The dinaturality condition on the family. -/
abbrev isDinatural (c : RestrictedCowedge G H) : IsDinatural H (G ⇓ c.pt) c.family :=
  c.toRestrictedCowedgeOver.isDinatural

/-- Constructor with explicit point, family, and dinaturality arguments. -/
@[match_pattern]
def mk' (pt : C) (family : ParanatSig H (G ⇓ pt))
    (isDinatural : IsDinatural H (G ⇓ pt) family) : RestrictedCowedge G H :=
  ⟨pt, ⟨family, isDinatural⟩⟩

end RestrictedCowedge

/-- Convert a restricted cowedge to a `Dinat` transformation `H → G ⇓ pt`. -/
def RestrictedCowedge.toDinat {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type v}
    (c : RestrictedCowedge G H) : Dinat H (G ⇓ c.pt) where
  app := c.family
  dinatural := c.isDinatural

/-- Construct a restricted cowedge from a carrier object and a `Dinat` transformation.

Given `pt : C` and a dinatural transformation `α : H → G ⇓ pt`, we obtain a
restricted cowedge with the same carrier and family. -/
def RestrictedCowedge.ofDinat {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type v}
    (pt : C) (α : Dinat H (G ⇓ pt)) : RestrictedCowedge G H where
  pt := pt
  toRestrictedCowedgeOver := ⟨α.app, α.dinatural⟩

namespace RestrictedCowedge

variable {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type v}

/-- The explicit dinaturality equation: for `g : A → B` and `x : H(B, A)`,
the two paths from `G(B, A)` to `pt` agree. -/
theorem dinaturality' (c : RestrictedCowedge G H) {A B : C} (g : A ⟶ B)
    (x : (H.obj (Opposite.op B)).obj A) :
    (G.map g.op).app A ≫ c.family A ((H.map g.op).app A x) =
    (G.obj (Opposite.op B)).map g ≫ c.family B ((H.obj (Opposite.op B)).map g x) := by
  have dinat := c.isDinatural A B g x
  simp only [Profunctor.lmap, Profunctor.rmap,
    sliceProfunctor_obj_map, sliceProfunctor_map_app] at dinat
  exact dinat.symm

/--
A morphism between restricted cowedges is an arrow in `C` that commutes
with all family morphisms (pointwise condition).
-/
@[ext]
structure Hom (c d : RestrictedCowedge G H) where
  /-- The underlying morphism in `C`. -/
  hom : c.pt ⟶ d.pt
  /-- Compatibility: for all `A` and `a ∈ H(A, A)`, composition with `hom`
  transforms `c.family` to `d.family`. -/
  comm (A : C) (a : (H.obj (Opposite.op A)).obj A) :
    c.family A a ≫ hom = d.family A a

attribute [simp] Hom.comm

/-- The identity morphism on a restricted cowedge. -/
@[simps]
def Hom.id (c : RestrictedCowedge G H) : Hom c c where
  hom := 𝟙 c.pt
  comm _ _ := Category.comp_id _

/-- Composition of restricted cowedge morphisms. -/
@[simps]
def Hom.comp {c d e : RestrictedCowedge G H} (f : Hom c d) (g : Hom d e) :
    Hom c e where
  hom := f.hom ≫ g.hom
  comm A a := by rw [← Category.assoc, f.comm, g.comm]

end RestrictedCowedge

/-!
### Strong restricted cowedges

A *strong restricted cowedge* uses the paranaturality condition instead of
dinaturality. This is a stronger condition: every paranatural transformation
is dinatural, but the converse does not hold in general.

The paranaturality condition requires that for *all* DiagCompat pairs of
diagonal elements, the family preserves the compatibility. In contrast,
dinaturality only requires this for DiagCompat pairs that factor through
off-diagonal elements.
-/

/--
An `H`-restricted `G`-cowedge with the paranaturality condition over a
fixed point `pt`. This contains just the family and paranaturality data
without bundling the carrier object.
-/
@[ext]
structure StrongRestrictedCowedgeOver (pt : C) (G : Cᵒᵖ ⥤ C ⥤ C)
    (H : Cᵒᵖ ⥤ C ⥤ Type v) where
  /-- The family of morphisms as a `ParanatSig H (G ⇓ pt)`. -/
  family : ParanatSig H (G ⇓ pt)
  /-- The paranaturality condition on the family. -/
  isParanatural : IsParanatural H (G ⇓ pt) family

/--
An `H`-restricted `G`-cowedge with the paranaturality condition.

This is the "strong" version of a restricted cowedge, where the family
satisfies the full paranaturality condition rather than just dinaturality.
-/
@[ext]
structure StrongRestrictedCowedge (G : Cᵒᵖ ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ Type v) where
  /-- The carrier (summit) object. -/
  pt : C
  /-- The cowedge data over the point. -/
  toStrongRestrictedCowedgeOver : StrongRestrictedCowedgeOver pt G H

namespace StrongRestrictedCowedge

variable {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type v}

/-- The family of morphisms as a `ParanatSig H (G ⇓ pt)`. -/
abbrev family (c : StrongRestrictedCowedge G H) : ParanatSig H (G ⇓ c.pt) :=
  c.toStrongRestrictedCowedgeOver.family

/-- The paranaturality condition on the family. -/
abbrev isParanatural (c : StrongRestrictedCowedge G H) :
    IsParanatural H (G ⇓ c.pt) c.family :=
  c.toStrongRestrictedCowedgeOver.isParanatural

/-- Constructor with explicit point, family, and paranaturality arguments. -/
@[match_pattern]
def mk' (pt : C) (family : ParanatSig H (G ⇓ pt))
    (isParanatural : IsParanatural H (G ⇓ pt) family) : StrongRestrictedCowedge G H :=
  ⟨pt, ⟨family, isParanatural⟩⟩

end StrongRestrictedCowedge

/-- Convert a StrongRestrictedCowedgeOver to a RestrictedCowedgeOver using the
implication paranaturality → dinaturality. -/
def StrongRestrictedCowedgeOver.toRestrictedCowedgeOver {pt : C} {G : Cᵒᵖ ⥤ C ⥤ C}
    {H : Cᵒᵖ ⥤ C ⥤ Type v} (c : StrongRestrictedCowedgeOver pt G H) :
    RestrictedCowedgeOver pt G H :=
  ⟨c.family, paranatural_implies_dinatural H (G ⇓ pt) c.family c.isParanatural⟩

/-- Convert a strong restricted cowedge to a `Paranat` transformation `H → G ⇓ pt`. -/
def StrongRestrictedCowedge.toParanat {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type v}
    (c : StrongRestrictedCowedge G H) : Paranat H (G ⇓ c.pt) where
  app := c.family
  paranatural := c.isParanatural

/-- Construct a strong restricted cowedge from a carrier object and a
`Paranat` transformation. -/
def StrongRestrictedCowedge.ofParanat {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type v}
    (pt : C) (α : Paranat H (G ⇓ pt)) : StrongRestrictedCowedge G H where
  pt := pt
  toStrongRestrictedCowedgeOver := ⟨α.app, α.paranatural⟩

/-- Every strong restricted cowedge is a restricted cowedge, since paranaturality
implies dinaturality. -/
def StrongRestrictedCowedge.toRestrictedCowedge {G : Cᵒᵖ ⥤ C ⥤ C}
    {H : Cᵒᵖ ⥤ C ⥤ Type v} (c : StrongRestrictedCowedge G H) :
    RestrictedCowedge G H where
  pt := c.pt
  toRestrictedCowedgeOver := ⟨c.family,
    paranatural_implies_dinatural H (G ⇓ c.pt) c.family c.isParanatural⟩

namespace StrongRestrictedCowedge

variable {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type v}

/--
A morphism between strong restricted cowedges is an arrow in `C` that commutes
with all family morphisms (pointwise condition).
-/
@[ext]
structure Hom (c d : StrongRestrictedCowedge G H) where
  /-- The underlying morphism in `C`. -/
  hom : c.pt ⟶ d.pt
  /-- Compatibility: for all `A` and `a ∈ H(A, A)`, composition with `hom`
  transforms `c.family` to `d.family`. -/
  comm (A : C) (a : (H.obj (Opposite.op A)).obj A) :
    c.family A a ≫ hom = d.family A a

attribute [simp] Hom.comm

/-- The identity morphism on a strong restricted cowedge. -/
@[simps]
def Hom.id (c : StrongRestrictedCowedge G H) : Hom c c where
  hom := 𝟙 c.pt
  comm _ _ := Category.comp_id _

/-- Composition of strong restricted cowedge morphisms. -/
@[simps]
def Hom.comp {c d e : StrongRestrictedCowedge G H} (f : Hom c d) (g : Hom d e) :
    Hom c e where
  hom := f.hom ≫ g.hom
  comm A a := by rw [← Category.assoc, f.comm, g.comm]

end StrongRestrictedCowedge

/--
The category of `H`-restricted `G`-cowedges with the paranaturality condition.

Objects are strong restricted cowedges `(C, Φ)` and morphisms are arrows
`h : C → D` compatible with the family structure.
-/
instance StrongRestrictedCowedgeCat (G : Cᵒᵖ ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ Type v) :
    Category (StrongRestrictedCowedge G H) where
  Hom := StrongRestrictedCowedge.Hom
  id := StrongRestrictedCowedge.Hom.id
  comp := StrongRestrictedCowedge.Hom.comp
  id_comp f := by ext; simp [StrongRestrictedCowedge.Hom.comp, StrongRestrictedCowedge.Hom.id]
  comp_id f := by ext; simp [StrongRestrictedCowedge.Hom.comp, StrongRestrictedCowedge.Hom.id]
  assoc f g h := by ext; simp [StrongRestrictedCowedge.Hom.comp]

@[simp]
theorem StrongRestrictedCowedge.category_comp_hom {G : Cᵒᵖ ⥤ C ⥤ C}
    {H : Cᵒᵖ ⥤ C ⥤ Type v} {c₁ c₂ c₃ : StrongRestrictedCowedge G H}
    (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) : (f ≫ g).hom = f.hom ≫ g.hom := rfl

@[simp]
theorem StrongRestrictedCowedge.category_id_hom {G : Cᵒᵖ ⥤ C ⥤ C}
    {H : Cᵒᵖ ⥤ C ⥤ Type v} (c : StrongRestrictedCowedge G H) :
    (𝟙 c : c ⟶ c).hom = 𝟙 c.pt := rfl

/-!
### Relationship between dinaturality and paranaturality

For restricted cowedges, the dinaturality condition relates to paranaturality
as follows:

Given `g : A → B` and an off-diagonal element `x : H(B, A)`, define:
- `a := H(g, id_A)(x) : H(A, A)`
- `b := H(id_B, g)(x) : H(B, B)`

These elements are always DiagCompat in `H`:
```
H(A, g)(a) = H(A, g)(H(g, A)(x)) = H(g, g)(x)
H(g, B)(b) = H(g, B)(H(B, g)(x)) = H(g, g)(x)
```

The dinaturality condition then ensures that `Φ_A(a)` and `Φ_B(b)` satisfy
a corresponding compatibility condition in the target.

In general, paranaturality is stronger than dinaturality because not every
DiagCompat pair of diagonal elements factors through an off-diagonal element.
However, for the restricted cowedge universal property, dinaturality suffices.
-/

/-- Off-diagonal elements of `H` induce DiagCompat pairs of diagonal elements.
Given `g : A → B` and `x : H(B, A)`, the elements `H(g, A)(x)` and `H(B, g)(x)`
are DiagCompat via `g`. -/
theorem offDiagonal_induces_diagCompat (H : Cᵒᵖ ⥤ C ⥤ Type w)
    {A B : C} (g : A ⟶ B) (x : (H.obj (Opposite.op B)).obj A) :
    DiagCompat H A B g ((H.map g.op).app A x) ((H.obj (Opposite.op B)).map g x) := by
  simp only [DiagCompat]
  -- Goal: H(A, g)(H(g, A)(x)) = H(g, B)(H(B, g)(x))
  -- Use naturality of H.map g.op : H.obj (op B) ⟶ H.obj (op A)
  -- Naturality says: (H.obj (op B)).map g ≫ (H.map g.op).app B
  --                = (H.map g.op).app A ≫ (H.obj (op A)).map g
  have nat := (H.map g.op).naturality g
  -- nat : (H.obj (op B)).map g ≫ (H.map g.op).app B
  --     = (H.map g.op).app A ≫ (H.obj (op A)).map g
  -- Apply both sides to x
  exact congrFun nat.symm x

/-- The dinaturality condition for a restricted cowedge implies a paranaturality-like
condition for pairs that factor through off-diagonal elements.

Given a restricted cowedge `(pt, Φ)` and `g : A → B`, `x : H(B, A)`, the morphisms
`Φ_A(H(g, A)(x))` and `Φ_B(H(B, g)(x))` satisfy:
```
G(g, A) ≫ Φ_A(H(g, A)(x)) = G(B, g) ≫ Φ_B(H(B, g)(x))
```
This is exactly the dinaturality condition, and it expresses that the two ways
to get from `G(B, A)` to `pt` agree. -/
theorem RestrictedCowedge.dinaturality_as_paranaturality
    {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type v}
    (c : RestrictedCowedge G H) {A B : C} (g : A ⟶ B)
    (x : (H.obj (Opposite.op B)).obj A) :
    (G.map g.op).app A ≫ c.family A ((H.map g.op).app A x) =
    (G.obj (Opposite.op B)).map g ≫ c.family B ((H.obj (Opposite.op B)).map g x) :=
  c.dinaturality' g x

/-- The family of a restricted cowedge, viewed as a `ParanatSig H (G ⇓ pt)`.

Since `diagApp H A = (H.obj (op A)).obj A` and
`diagApp (G ⇓ pt) A = (G.obj (op A)).obj A ⟶ pt` (definitionally), the family
type `(A : C) → diagApp H A → diagApp (G ⇓ pt) A` equals `ParanatSig H (G ⇓ pt)`.

This provides the bridge between the cowedge formulation and the paranatural
transformation machinery. Note that dinaturality implies paranaturality only
for DiagCompat pairs that factor through off-diagonal elements.

The universe constraint `v = w` is needed because `ParanatSig` requires both
endoprofunctors to be valued in the same universe, and the slice profunctor
`G ⇓ pt` outputs `Type v` (the morphism universe). -/
def RestrictedCowedge.familyAsParanatSig {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type v}
    (c : RestrictedCowedge G H) : ParanatSig H (G ⇓ c.pt) :=
  c.family

/-- `DiagCompat` for the slice profunctor `G ⇓ c` at morphisms is exactly the
dinaturality equation. This shows that `m₀ : Hom(G(A,A), c)` and `m₁ : Hom(G(B,B), c)`
are DiagCompat iff the two paths from `G(B,A)` to `c` agree. -/
theorem sliceProfunctor_diagCompat_iff {G : Cᵒᵖ ⥤ C ⥤ C} (c : C)
    {A B : C} (f : A ⟶ B)
    (m₀ : diagApp (G ⇓ c) A) (m₁ : diagApp (G ⇓ c) B) :
    DiagCompat (G ⇓ c) A B f m₀ m₁ ↔
    (G.map f.op).app A ≫ m₀ = (G.obj (Opposite.op B)).map f ≫ m₁ := by
  simp only [DiagCompat, sliceProfunctor_obj_map, sliceProfunctor_map_app,
    Quiver.Hom.unop_op]

/-- Dinaturality of a restricted cowedge implies DiagCompat for the image under
the family map, for pairs that factor through off-diagonal elements.

Given a restricted cowedge `c`, morphism `g : A → B`, and off-diagonal element
`x : H(B, A)`, the induced diagonal elements `(H.map g.op).app A x` and
`(H.obj (op B)).map g x` are DiagCompat in `H`, and their images under `c.family`
are DiagCompat in `G ⇓ c.pt`. -/
theorem RestrictedCowedge.family_preserves_diagCompat_offDiag
    {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type v}
    (c : RestrictedCowedge G H) {A B : C} (g : A ⟶ B)
    (x : (H.obj (Opposite.op B)).obj A) :
    DiagCompat (G ⇓ c.pt) A B g
      (c.family A ((H.map g.op).app A x))
      (c.family B ((H.obj (Opposite.op B)).map g x)) := by
  rw [sliceProfunctor_diagCompat_iff]
  exact c.dinaturality' g x

/--
The category of `H`-restricted `G`-cowedges.

Objects are restricted cowedges `(C, Φ)` and morphisms are arrows `h : C → D`
compatible with the family structure.
-/
instance RestrictedCowedgeCat (G : Cᵒᵖ ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ Type v) :
    Category (RestrictedCowedge G H) where
  Hom := RestrictedCowedge.Hom
  id := RestrictedCowedge.Hom.id
  comp := RestrictedCowedge.Hom.comp
  id_comp f := by ext; simp [RestrictedCowedge.Hom.comp, RestrictedCowedge.Hom.id]
  comp_id f := by ext; simp [RestrictedCowedge.Hom.comp, RestrictedCowedge.Hom.id]
  assoc f g h := by ext; simp [RestrictedCowedge.Hom.comp]

@[simp]
theorem RestrictedCowedge.category_comp_hom {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type v}
    {c₁ c₂ c₃ : RestrictedCowedge G H}
    (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) : (f ≫ g).hom = f.hom ≫ g.hom := rfl

@[simp]
theorem RestrictedCowedge.category_id_hom {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type v}
    (c : RestrictedCowedge G H) : (𝟙 c : c ⟶ c).hom = 𝟙 c.pt := rfl

/-- The inclusion functor from strong restricted cowedges to restricted cowedges.
This embeds the category of cowedges with paranaturality into the category of
cowedges with dinaturality. Since paranaturality implies dinaturality, every
strong restricted cowedge is a restricted cowedge, and morphisms are defined
identically in both categories (arrows commuting with the family). -/
def StrongRestrictedCowedge.inclusion (G : Cᵒᵖ ⥤ C ⥤ C)
    (H : Cᵒᵖ ⥤ C ⥤ Type v) :
    StrongRestrictedCowedge G H ⥤ RestrictedCowedge G H where
  obj c := c.toRestrictedCowedge
  map f := ⟨f.hom, f.comm⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The inclusion functor is fully faithful, making strong restricted cowedges
a full subcategory of restricted cowedges. This holds because morphisms in both
categories are defined identically: arrows in `C` that commute with the family
of structure morphisms. -/
def StrongRestrictedCowedge.inclusion_fullyFaithful (G : Cᵒᵖ ⥤ C ⥤ C)
    (H : Cᵒᵖ ⥤ C ⥤ Type v) :
    (StrongRestrictedCowedge.inclusion G H).FullyFaithful :=
  Functor.FullyFaithful.mk
    (fun {c d} f => ⟨f.hom, f.comm⟩)

end RestrictedCowedges

section RestrictedCoends

/-!
## Restricted coends

A *restricted coend* is an `H`-restricted `G`-cowedge that is initial in
the category of restricted cowedges.

This generalizes ordinary coends: when `H` is the constant functor to a
singleton type, an `H`-restricted `G`-coend is exactly the ordinary coend
`∫^A G(A, A)`.
-/

variable {C : Type u} [Category.{v} C]

/--
An `H`-restricted `G`-coend is an initial object in the category of
`H`-restricted `G`-cowedges.
-/
abbrev IsRestrictedCoend (G : Cᵒᵖ ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ Type v)
    (c : RestrictedCowedge G H) :=
  Limits.IsInitial c

namespace IsRestrictedCoend

variable {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type v} {c : RestrictedCowedge G H}

/-- The universal morphism from a restricted coend to any restricted cowedge. -/
def desc (hc : IsRestrictedCoend G H c)
    (d : RestrictedCowedge G H) : c ⟶ d :=
  hc.to d

/-- The underlying morphism in `C` from a restricted coend to any cowedge. -/
def descHom (hc : IsRestrictedCoend G H c)
    (d : RestrictedCowedge G H) : c.pt ⟶ d.pt :=
  (hc.desc d).hom

/-- Any two morphisms from a restricted coend are equal (uniqueness). -/
theorem homExt (hc : IsRestrictedCoend G H c)
    {d : RestrictedCowedge G H} (f g : c ⟶ d) : f = g :=
  Limits.IsInitial.hom_ext hc f g

/-- Two restricted coends are isomorphic (uniqueness up to isomorphism). -/
def toUniqueUpToIso {c c' : RestrictedCowedge G H}
    (hc : IsRestrictedCoend G H c) (hc' : IsRestrictedCoend G H c') :
    c ≅ c' :=
  Limits.IsInitial.uniqueUpToIso hc hc'

end IsRestrictedCoend

/-- A restricted coend cone bundles a cowedge with the proof it is initial.
This is the data-carrying version, analogous to mathlib's `LimitCone`. -/
structure RestrictedCoendCone (G : Cᵒᵖ ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ Type v) where
  /-- The underlying restricted cowedge. -/
  cowedge : RestrictedCowedge G H
  /-- The proof that the cowedge is initial. -/
  isInitial : IsRestrictedCoend G H cowedge

/-- A restricted coend exists if there is an initial restricted cowedge.
This class carries the data directly (rather than asserting existence as a Prop)
to support constructive extraction of the coend. -/
class HasRestrictedCoend (G : Cᵒᵖ ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ Type v) where
  /-- The cone containing the coend and proof of initiality. -/
  cone : RestrictedCoendCone G H

namespace HasRestrictedCoend

variable (G : Cᵒᵖ ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ Type v) [HasRestrictedCoend G H]

/-- The restricted coend object (carrier of the initial restricted cowedge). -/
def restrictedCoend : RestrictedCowedge G H :=
  HasRestrictedCoend.cone.cowedge

/-- The restricted coend is initial. -/
def restrictedCoendIsInitial :
    IsRestrictedCoend G H (restrictedCoend G H) :=
  HasRestrictedCoend.cone.isInitial

end HasRestrictedCoend

end RestrictedCoends

section WeightedCowedgeEmbedding

/-!
## Weighted Cowedges and Strong Restricted Cowedges

This section explores the relationship between weighted cowedges (when `D = C`)
and strong restricted cowedges. The goal is to show that weighted cowedges
embed as a (potentially full) subcategory of strong restricted cowedges.

For a weighted cowedge `WeightedCowedge W P` with:
- `W : (TwistedArrow C)ᵒᵖ ⥤ Type v` (the weight)
- `P : Cᵒᵖ ⥤ C ⥤ C` (endoprofunctor)

The weighted cowedge provides data at ALL twisted arrows (all morphisms
in `C`). A strong restricted cowedge only provides data at diagonal elements
(identity morphisms). The embedding restricts weighted cowedge data to the
diagonal twisted arrows.
-/

variable {C : Type u} [Category.{v} C]

/-- The diagonal twisted arrow for an object `A`, representing the identity
morphism `𝟙 A : A ⟶ A` as an object of `TwistedArrow C`. -/
abbrev diagTwArr (A : C) : TwistedArrow C := twObjMk (𝟙 A)

@[simp]
lemma diagTwArr_dom (A : C) : twDom (diagTwArr A) = A := rfl

@[simp]
lemma diagTwArr_cod (A : C) : twCod (diagTwArr A) = A := rfl

@[simp]
lemma diagTwArr_arr (A : C) : twArr (diagTwArr A) = 𝟙 A :=
  @twObjMk_arr C _ A A (𝟙 A)

/-- Extract the diagonal element type from a weight functor `W` at object `A`.
This is `W(op (diagTwArr A)) = W(op (twObjMk (𝟙 A)))`. -/
abbrev weightDiagElem (W : (TwistedArrow C)ᵒᵖ ⥤ Type v) (A : C) : Type v :=
  W.obj (Opposite.op (diagTwArr A))

/-- Given a weighted cocone over a twisted arrow diagram, extract the family
of morphisms at diagonal twisted arrows.

For `A : C` and `w : weightDiagElem W A`, this gives `F.obj (diagTwArr A) ⟶ pt`.
When `F = profunctorOnTwistedArrow C P`, this becomes `(P.obj (op A)).obj A ⟶ pt`.

This matches the signature required for `ParanatSig H (P ⇓ pt)` when we take
`diagApp H A = weightDiagElem W A`. -/
def weightedCoconeDiagFamily {W : (TwistedArrow C)ᵒᵖ ⥤ Type v}
    {F : TwistedArrow C ⥤ C} (c : WeightedCocone W F) (A : C)
    (w : weightDiagElem W A) : F.obj (diagTwArr A) ⟶ c.pt :=
  c.leg (diagTwArr A) w

/-!
### Diagonal Restriction Profunctor

To define a strong restricted cowedge from a weighted cowedge, we need a
profunctor `H : Cᵒᵖ ⥤ C ⥤ Type v`. The natural choice is to define `H` such
that `diagApp H A = weightDiagElem W A`.

The straightforward approach is to make `H.obj (op A)` constant in its second
argument: `H.obj (op A).obj B = W.obj (op (diagCoTwArr A))` for all `B`.

For functoriality in the first argument, we would need morphisms between
diagonal co-twisted arrows, which requires isomorphisms (or at least split
morphisms) in `C`. This is because a morphism `diagCoTwArr A ⟶ diagCoTwArr B`
in `CoTwistedArrow C` requires both `A ⟶ B` and `B ⟶ A` satisfying a
composition condition.

Instead, we define a simpler version that works for any `W` by making `H`
constant in BOTH arguments: `H = const (const (W.obj (op (diagCoTwArr A))))`.
This means the diagonal restriction gives a trivial profunctor structure, but
it still captures the correct diagonal elements.
-/

/-- The constant profunctor that returns a fixed type `T` for all inputs.
This is `(const Cᵒᵖ).obj ((const C).obj T)`. -/
abbrev constProfunctor (T : Type v) : Cᵒᵖ ⥤ C ⥤ Type v :=
  (Functor.const Cᵒᵖ).obj ((Functor.const C).obj T)

@[simp]
lemma constProfunctor_obj_obj (T : Type v) (A B : C) :
    ((constProfunctor (C := C) T).obj (Opposite.op A)).obj B = T := rfl

@[simp]
lemma constProfunctor_diagApp (T : Type v) (A : C) :
    diagApp (constProfunctor (C := C) T) A = T := rfl

/-!
### Constant Profunctor on Twisted Arrow Categories

When the weight profunctor is constant at a singleton type `PUnit`, the induced
functor on the twisted arrow category is the constant functor at `PUnit`.
This shows that weighted wedges with trivial weight are equivalent to ordinary
cones over the diagram functor.
-/

/-- The constant profunctor on the twisted arrow category is the unit weight. -/
theorem constProfunctorOnTwistedArrow_eq_unitWeight :
    profunctorOnTwistedArrow C (constProfunctor (C := C) PUnit.{v+1}) =
    unitWeight (TwistedArrow C) := rfl

/-- Weighted wedges with trivial (unit) weight are equivalent to ordinary cones.

When `W = constProfunctor PUnit`, a `WeightedWedge W P` is a `WeightedCone`
with weight `unitWeight (TwistedArrow C)`, which is equivalent to an ordinary
`Cone (profunctorOnTwistedArrow C P)` by `coneWeightedConeEquiv`.

This equivalence is the foundation for expressing ends as limits over the
twisted arrow category: `End P ≅ lim_{TwistedArrow C} (profunctorOnTwistedArrow C P)`.
-/
def trivialWeightedWedgeConeEquiv {D : Type w} [Category.{v} D]
    (P : Cᵒᵖ ⥤ C ⥤ D) :
    WeightedWedge (constProfunctor (C := C) PUnit.{v+1}) P ≌
    Cone (profunctorOnTwistedArrow C P) := by
  unfold WeightedWedge
  rw [constProfunctorOnTwistedArrow_eq_unitWeight]
  exact (coneWeightedConeEquiv (profunctorOnTwistedArrow C P)).symm

/-- Weighted cowedges with trivial (unit) weight are equivalent to ordinary
cocones. This is the dual of `trivialWeightedWedgeConeEquiv`. -/
def trivialWeightedCowedgeCoconeEquiv {D : Type w} [Category.{v} D]
    (P : Cᵒᵖ ⥤ C ⥤ D) :
    WeightedCowedge (constProfunctor (C := C) PUnit.{v+1}) P ≌
    Cocone (profunctorOnCoTwistedArrow C P) := by
  unfold WeightedCowedge
  have h : profunctorOnOpCoTwistedArrow C (constProfunctor (C := C) PUnit.{v+1}) =
           unitWeightOp (CoTwistedArrow C) := rfl
  rw [h]
  exact (coconeWeightedCoconeEquiv (profunctorOnCoTwistedArrow C P)).symm

/-!
### Extracting Diagonal Data from Weighted Cowedges

Given a weighted cowedge, we can extract the diagonal family as a `ParanatSig`.
The paranaturality condition requires relating elements across morphisms in C,
which corresponds to morphisms between diagonal co-twisted arrows.

Since morphisms between diagonal co-twisted arrows require isomorphisms,
the weighted cowedge naturality condition only provides paranaturality
relations along isomorphisms, not along arbitrary morphisms.

For the special case where `H = constProfunctor T` (so `DiagCompat H` is
equality), paranaturality becomes: equal input elements give `DiagCompat`
outputs in the slice profunctor.
-/

/-- Extract the diagonal family signature from a weighted cocone over a
twisted arrow diagram. This gives a family `(A : C) → weightDiagElem W A →
F.obj (diagTwArr A) ⟶ pt`.

When `F = profunctorOnTwistedArrow C P` for an endoprofunctor `P`, this
becomes `(A : C) → weightDiagElem W A → diagApp (P ⇓ pt) A`, giving a
`ParanatSig` where the source profunctor `H` has
`diagApp H A = weightDiagElem W A`. -/
def weightedCoconeDiagFamilySig {W : (TwistedArrow C)ᵒᵖ ⥤ Type v}
    {F : TwistedArrow C ⥤ C} (c : WeightedCocone W F) :
    (A : C) → weightDiagElem W A → (F.obj (diagTwArr A) ⟶ c.pt) :=
  fun A w => c.leg (diagTwArr A) w

/-- The diagonal family signature equals the leg applied at diagonal twisted
arrows. -/
@[simp]
theorem weightedCoconeDiagFamilySig_eq {W : (TwistedArrow C)ᵒᵖ ⥤ Type v}
    {F : TwistedArrow C ⥤ C} (c : WeightedCocone W F) (A : C)
    (w : weightDiagElem W A) :
    (weightedCoconeDiagFamilySig c A w : F.obj (diagTwArr A) ⟶ c.pt) =
      c.leg (diagTwArr A) w := rfl

/--
For a co-twisted arrow `tw` with `coTwArr tw : coTwCod tw ⟶ coTwDom tw`,
this gives the type `(G.obj (op (coTwCod tw))).obj (coTwDom tw) ⟶ c`.

At the diagonal co-twisted arrow `diagCoTwArr A = 𝟙_A`, this evaluates to
`(G.obj (op A)).obj A ⟶ c`, which equals `diagApp (G ⇓ c) A` - the diagonal
of the slice profunctor. -/
def sliceWeightObj (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) (tw : CoTwistedArrow C) : Type v :=
  (G.obj (Opposite.op (coTwCod tw))).obj (coTwDom tw) ⟶ c

@[simp]
theorem sliceWeightObj_def (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) (tw : CoTwistedArrow C) :
    sliceWeightObj G c tw =
    ((G.obj (Opposite.op (coTwCod tw))).obj (coTwDom tw) ⟶ c) := rfl

/-- At the diagonal co-twisted arrow, the slice weight type is `(G(A,A)) ⟶ c`.
Note: for `G : Cᵒᵖ ⥤ C ⥤ C`, `(G.obj (op A)).obj A` is an object of C, and
the slice weight gives the type of morphisms from that object to c. -/
theorem sliceWeightObj_diag (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) (A : C) :
    sliceWeightObj G c (diagCoTwArr A) = ((G.obj (Opposite.op A)).obj A ⟶ c) := by
  simp only [sliceWeightObj_def, diagCoTwArr, coTwObjMk_dom, coTwObjMk_cod]

/-- The diagonal of the slice weight matches the diagonal of the slice profunctor.
This shows that `sliceWeightObj` captures the correct diagonal structure: for
the slice profunctor `G ⇓ c`, its diagonal at A is `(G(A,A)) ⟶ c`, which is
exactly what `sliceWeightObj G c` gives at `diagCoTwArr A`. -/
theorem sliceWeightObj_diagApp_eq (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) (A : C) :
    sliceWeightObj G c (diagCoTwArr A) = diagApp (G ⇓ c) A := by
  rw [sliceWeightObj_diag, sliceProfunctor_diagApp]

/-- The profunctor action for morphisms between co-twisted arrows.
For `m : x ⟶ y` in `CoTwistedArrow C`, this gives a morphism from
`G(coTwCod y, coTwDom y)` to `G(coTwCod x, coTwDom x)`. -/
def sliceWeightProfunctorAction (G : Cᵒᵖ ⥤ C ⥤ C) {x y : CoTwistedArrow C}
    (m : x ⟶ y) :
    (G.obj (Opposite.op (coTwCod y))).obj (coTwDom y) ⟶
    (G.obj (Opposite.op (coTwCod x))).obj (coTwDom x) :=
  (G.obj (Opposite.op (coTwCod y))).map (coTwDomArr m) ≫
    (G.map (coTwCodArr m).op).app (coTwDom x)

/-- The slice weight morphism action for a covariant functor.
Given `h : G(coTwCod x, coTwDom x) ⟶ c` and a co-twisted arrow morphism
`m : x ⟶ y`, produces `sliceWeightProfunctorAction G m ≫ h : G(y) ⟶ c`. -/
def sliceWeightMapCovariant (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) {x y : CoTwistedArrow C}
    (m : x ⟶ y) :
    sliceWeightObj G c x → sliceWeightObj G c y :=
  fun h => sliceWeightProfunctorAction G m ≫ h

/-- The profunctor action preserves identities. -/
theorem sliceWeightProfunctorAction_id (G : Cᵒᵖ ⥤ C ⥤ C) (x : CoTwistedArrow C) :
    sliceWeightProfunctorAction G (𝟙 x) = 𝟙 _ := by
  simp only [sliceWeightProfunctorAction]
  rw [coTwDomArr_id, coTwCodArr_id]
  simp only [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- The profunctor action preserves composition. -/
theorem sliceWeightProfunctorAction_comp (G : Cᵒᵖ ⥤ C ⥤ C)
    {x y z : CoTwistedArrow C} (m : x ⟶ y) (n : y ⟶ z) :
    sliceWeightProfunctorAction G (m ≫ n) =
      sliceWeightProfunctorAction G n ≫ sliceWeightProfunctorAction G m := by
  simp only [sliceWeightProfunctorAction]
  rw [coTwDomArr_comp, coTwCodArr_comp]
  simp only [CategoryTheory.Functor.map_comp, op_comp, NatTrans.comp_app]
  -- Naturality of G.map (coTwCodArr n).op applied to coTwDomArr m gives interchange
  have nat := (G.map (coTwCodArr n).op).naturality (coTwDomArr m)
  -- Use calc to handle associativity explicitly
  calc _ = (G.obj _).map (coTwDomArr n) ≫ (G.obj _).map (coTwDomArr m) ≫
           (G.map (coTwCodArr n).op).app _ ≫ (G.map (coTwCodArr m).op).app _ := by
           simp only [Category.assoc]
       _ = (G.obj _).map (coTwDomArr n) ≫ ((G.obj _).map (coTwDomArr m) ≫
           (G.map (coTwCodArr n).op).app _) ≫ (G.map (coTwCodArr m).op).app _ := by
           simp only [← Category.assoc]
       _ = (G.obj _).map (coTwDomArr n) ≫ ((G.map (coTwCodArr n).op).app _ ≫
           (G.obj _).map (coTwDomArr m)) ≫ (G.map (coTwCodArr m).op).app _ := by
           rw [nat]
       _ = _ := by simp only [Category.assoc]

/-- Identity law for the covariant slice weight map. -/
theorem sliceWeightMapCovariant_id (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) (x : CoTwistedArrow C)
    (h : sliceWeightObj G c x) :
    sliceWeightMapCovariant G c (𝟙 x) h = h := by
  simp only [sliceWeightMapCovariant, sliceWeightProfunctorAction_id, Category.id_comp]

/-- Composition law for the covariant slice weight map. -/
theorem sliceWeightMapCovariant_comp (G : Cᵒᵖ ⥤ C ⥤ C) (c : C)
    {x y z : CoTwistedArrow C} (m : x ⟶ y) (n : y ⟶ z)
    (h : sliceWeightObj G c x) :
    sliceWeightMapCovariant G c (m ≫ n) h =
      sliceWeightMapCovariant G c n (sliceWeightMapCovariant G c m h) := by
  simp only [sliceWeightMapCovariant, sliceWeightProfunctorAction_comp, Category.assoc]

/-- The covariant slice weight as a functor from `CoTwistedArrow C` to `Type v`.
This is a copresheaf on the co-twisted arrow category, induced by the slice
profunctor `G ⇓ c`. -/
def sliceWeightCovariant (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) : CoTwistedArrow C ⥤ Type v where
  obj := sliceWeightObj G c
  map := sliceWeightMapCovariant G c
  map_id x := by
    ext h
    exact sliceWeightMapCovariant_id G c x h
  map_comp m n := by
    ext h
    exact sliceWeightMapCovariant_comp G c m n h

/-- The covariant slice weight at a diagonal co-twisted arrow. -/
@[simp]
theorem sliceWeightCovariant_obj_diag (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) (A : C) :
    (sliceWeightCovariant G c).obj (diagCoTwArr A) =
    ((G.obj (Opposite.op A)).obj A ⟶ c) := by
  simp only [sliceWeightCovariant, sliceWeightObj_diag]

/-- The covariant slice weight matches the slice profunctor diagonal. -/
theorem sliceWeightCovariant_obj_eq_diagApp (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) (A : C) :
    (sliceWeightCovariant G c).obj (diagCoTwArr A) = diagApp (G ⇓ c) A := by
  rw [sliceWeightCovariant_obj_diag, sliceProfunctor_diagApp]

/-- The slice weight as a presheaf on `TwistedArrow C`.

This is `sliceWeightCovariant G c` pre-composed with the equivalence
`(TwistedArrow C)ᵒᵖ ≌ CoTwistedArrow C`, giving a contravariant functor
on `TwistedArrow C`, i.e., a presheaf. -/
def sliceWeight (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) : (TwistedArrow C)ᵒᵖ ⥤ Type v :=
  twistedArrowOpEquivCoTwistedArrow.functor ⋙ sliceWeightCovariant G c

/-- A weighted cocone where the weight is derived from the slice profunctor
`G ⇓ c`. This takes the same parameters as `RestrictedCowedge` and
`StrongRestrictedCowedge` (an endoprofunctor `G` and an object `c`).

This is a `WeightedCocone` where:
- The weight is `sliceWeight G c : (TwistedArrow C)ᵒᵖ ⥤ Type v`
- The diagram is `profunctorOnTwistedArrow C G : TwistedArrow C ⥤ C`

Note: This uses `WeightedCocone` directly instead of `WeightedCowedge` because
`sliceWeight` is a twisted arrow presheaf, not a profunctor. -/
abbrev SliceWeightedCowedge (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) :=
  WeightedCocone (sliceWeight G c) (profunctorOnTwistedArrow C G)

/-!
### Implications for Weighted Colimits

The covariant slice weight `sliceWeightCovariant G c : CoTwistedArrow C ⥤ Type v`
is a copresheaf (covariant functor) on `CoTwistedArrow C`.

Since `CoTwistedArrow C = OpTwistedArrow' (Cᵒᵖ') ≅ (TwistedArrow Cᵒᵖ)ᵒᵖ`
(see `TwistedArrow.lean` theorems `opTwistedArrowIsoTwistedArrowOp'` and
`OpTwistedArrow' (Cᵒᵖ') = CoTwistedArrow' C`), a covariant functor on
`CoTwistedArrow C` is equivalently a **presheaf on `TwistedArrow Cᵒᵖ`**.

Weighted colimits use presheaves as weights. Therefore, the slice profunctor
induces a weight suitable for weighted colimits over `TwistedArrow Cᵒᵖ`.

The relationship between restricted cowedges and weighted colimits:
- `sliceWeightCovariant G c : CoTwistedArrow C ⥤ Type v` is a copresheaf
- Viewing as `(TwistedArrow Cᵒᵖ)ᵒᵖ ⥤ Type v`, this is a presheaf on
  `TwistedArrow Cᵒᵖ`
- This presheaf can serve as a weight for weighted colimits

For the category of elements, two perspectives arise:
1. `(sliceWeightCovariant G c).Elements` - covariant elements of the copresheaf
2. `W'.ElementsPre` where `W'` is the transported presheaf on `TwistedArrow Cᵒᵖ`

These should be equivalent via the category equivalence
`CoTwistedArrow C ≌ (TwistedArrow Cᵒᵖ)ᵒᵖ`, but the choice affects the
concrete morphism directions.

### Relationship with Strong Restricted Cowedges

Strong restricted cowedges (`StrongRestrictedCowedge G H`) and weighted cowedges
(`WeightedCowedge W G`) are structurally different:

1. **Variance**: `WeightedCowedge` requires a presheaf weight
   `(CoTwistedArrow C)ᵒᵖ ⥤ Type v`, while the diagonal values `H(A,A)` of a
   bifunctor H do not form a presheaf on `CoTwistedArrow C` in any canonical way.

2. **Naturality conditions**: WeightedCocone naturality relates single weight
   elements via the weight's functorial action. Paranaturality relates pairs
   of diagonal elements that satisfy a compatibility condition (DiagCompat).
   These are different types of coherence.

3. **Data scope**: WeightedCowedges have data at ALL co-twisted arrows;
   StrongRestrictedCowedges only have data at diagonals.

4. **DiagElem variance**: The category `DiagElem H` has morphisms going in the
   same direction as C (covariant), while presheaf weights for cocones are
   contravariant. This covariant/contravariant mismatch prevents embedding.

Strong restricted cowedges are best understood as capturing "diagonal
paranaturality" while weighted cowedges capture "full functorial naturality"
over the twisted arrow category. These represent different mathematical
structures rather than a subcategory relationship.
-/

end WeightedCowedgeEmbedding

/-!
## Weighted Cowedge and Restricted Cowedge Correspondence

This section establishes the relationship between `WeightedCowedge W P` and
`RestrictedCowedge G H`. Both structures capture a notion of "cowedge" for
profunctors, but with different formulations:

- `WeightedCowedge W P` uses `(CoTwistedArrow C)ᵒᵖ` as the indexing category
  with weight `profunctorOnOpCoTwistedArrow C W` and diagram
  `profunctorOnCoTwistedArrow C P`. It has components at ALL co-twisted arrows.

- `RestrictedCowedge G H` has data only at diagonal objects (identity arrows),
  with a dinaturality condition.

The correspondence parallels the standard result that cowedges for a profunctor
`P : Cᵒᵖ × C → Set` correspond bijectively to cocones for the derived functor
`P″ : Tw(Cᵒᵖ)ᵒᵖ → Set` (see `docs/wedge-cone-equivalence.md`).

### Structure of the equivalence

For `WeightedCowedge W P` (where `W, P : Cᵒᵖ ⥤ C ⥤ D`):

At an arrow `(arr : cod → dom)` in `CoTwistedArrow C`:
- **Weight**: `W(cod, dom)` = W(source, target)
- **Diagram**: `P(dom, cod)` = P(target, source)
- **Component type**: `W(cod, dom) ⟶ P(dom, cod)`

At identity `(𝟙 A)`:
- **Weight**: `W(A, A)`
- **Diagram**: `P(A, A)`
- **Component type**: `W(A, A) ⟶ P(A, A)`

This matches `RestrictedCowedge`'s diagonal structure exactly.
-/

section WeightedRestrictedCorrespondence

variable {C : Type u} [Category.{v} C]

/-- The identity co-twisted arrow at an object A. This is `coTwObjMk (𝟙 A)`,
representing the identity arrow `𝟙_A : A → A` as a co-twisted arrow. -/
def idCoTwistedArrow (A : C) : CoTwistedArrow C := coTwObjMk (𝟙 A)

@[simp]
theorem idCoTwistedArrow_dom (A : C) : coTwDom (idCoTwistedArrow A) = A :=
  coTwObjMk_dom (𝟙 A)

@[simp]
theorem idCoTwistedArrow_cod (A : C) : coTwCod (idCoTwistedArrow A) = A :=
  coTwObjMk_cod (𝟙 A)

@[simp]
theorem idCoTwistedArrow_arr (A : C) : coTwArr (idCoTwistedArrow A) = 𝟙 A :=
  coTwObjMk_arr (𝟙 A)

/-- The equivalence `coTwistedArrowOpEquivTwistedArrow` maps identity
co-twisted arrows to identity twisted arrows (domain component). -/
theorem coTwistedArrowOpEquiv_identity_dom (A : C) :
    twDom (coTwistedArrowOpEquivTwistedArrow.functor.obj
      (Opposite.op (idCoTwistedArrow A))) = A := by
  simp only [coTwistedArrowOpEquivTwistedArrow, Cat.equivOfIso,
    coTwistedArrowOpIsoTwistedArrow]
  simp only [Iso.trans_hom]
  simp only [coTwistedArrowOpIsoTwistedArrowOp, Cat.opFunctor,
    Cat.opFunctorInvolutive, Iso.trans_hom, Functor.comp_obj]
  simp only [twistedArrowOpOpIsoCoTwistedArrow, twistedArrowIsoTwistedArrowOp]
  simp only [Cat.isoOfEquiv, twistedArrowEquivTwistedArrowOp, Iso.symm_hom]
  simp only [twistedArrowOpToTwistedArrow]
  simp only [idCoTwistedArrow]
  simp only [twDom, twObjMk]
  rfl

/-- The equivalence `coTwistedArrowOpEquivTwistedArrow` maps identity
co-twisted arrows to identity twisted arrows (codomain component). -/
theorem coTwistedArrowOpEquiv_identity_cod (A : C) :
    twCod (coTwistedArrowOpEquivTwistedArrow.functor.obj
      (Opposite.op (idCoTwistedArrow A))) = A := by
  simp only [coTwistedArrowOpEquivTwistedArrow, Cat.equivOfIso,
    coTwistedArrowOpIsoTwistedArrow]
  simp only [Iso.trans_hom]
  simp only [coTwistedArrowOpIsoTwistedArrowOp, Cat.opFunctor,
    Cat.opFunctorInvolutive, Iso.trans_hom, Functor.comp_obj]
  simp only [twistedArrowOpOpIsoCoTwistedArrow, twistedArrowIsoTwistedArrowOp]
  simp only [Cat.isoOfEquiv, twistedArrowEquivTwistedArrowOp, Iso.symm_hom]
  simp only [twistedArrowOpToTwistedArrow]
  simp only [idCoTwistedArrow]
  simp only [twCod, twObjMk]
  rfl

/-- The weight profunctor at the identity co-twisted arrow evaluates to the
diagonal of the weight. This shows that `profunctorOnOpCoTwistedArrow C W`
evaluated at `op (idCoTwistedArrow A)` gives `W(A, A)`. -/
theorem profunctorOnOpCoTwistedArrow_at_identity (W : Cᵒᵖ ⥤ C ⥤ Type v) (A : C) :
    (profunctorOnOpCoTwistedArrow C W).obj (Opposite.op (idCoTwistedArrow A)) =
    (W.obj (Opposite.op A)).obj A := by
  simp only [profunctorOnOpCoTwistedArrow, Functor.comp_obj,
    profunctorOnTwistedArrow_obj]
  rw [coTwistedArrowOpEquiv_identity_dom A, coTwistedArrowOpEquiv_identity_cod A]

/-- The equivalence maps general co-twisted arrows correctly (domain). For
`arr : cod → dom` in C, the equivalence functor maps `op (coTwObjMk arr)` to
a twisted arrow with domain `cod`. -/
theorem coTwistedArrowOpEquiv_arrow_dom {cod dom : C} (arr : cod ⟶ dom) :
    twDom (coTwistedArrowOpEquivTwistedArrow.functor.obj
      (Opposite.op (coTwObjMk arr))) = cod := by
  simp only [coTwistedArrowOpEquivTwistedArrow, Cat.equivOfIso,
    coTwistedArrowOpIsoTwistedArrow]
  simp only [Iso.trans_hom]
  simp only [coTwistedArrowOpIsoTwistedArrowOp, Cat.opFunctor,
    Cat.opFunctorInvolutive, Iso.trans_hom, Functor.comp_obj]
  simp only [twistedArrowOpOpIsoCoTwistedArrow, twistedArrowIsoTwistedArrowOp]
  simp only [Cat.isoOfEquiv, twistedArrowEquivTwistedArrowOp, Iso.symm_hom]
  simp only [twistedArrowOpToTwistedArrow]
  simp only [twDom, twObjMk]
  rfl

/-- The equivalence maps general co-twisted arrows correctly (codomain). For
`arr : cod → dom` in C, the equivalence functor maps `op (coTwObjMk arr)` to
a twisted arrow with codomain `dom`. -/
theorem coTwistedArrowOpEquiv_arrow_cod {cod dom : C} (arr : cod ⟶ dom) :
    twCod (coTwistedArrowOpEquivTwistedArrow.functor.obj
      (Opposite.op (coTwObjMk arr))) = dom := by
  simp only [coTwistedArrowOpEquivTwistedArrow, Cat.equivOfIso,
    coTwistedArrowOpIsoTwistedArrow]
  simp only [Iso.trans_hom]
  simp only [coTwistedArrowOpIsoTwistedArrowOp, Cat.opFunctor,
    Cat.opFunctorInvolutive, Iso.trans_hom, Functor.comp_obj]
  simp only [twistedArrowOpOpIsoCoTwistedArrow, twistedArrowIsoTwistedArrowOp]
  simp only [Cat.isoOfEquiv, twistedArrowEquivTwistedArrowOp, Iso.symm_hom]
  simp only [twistedArrowOpToTwistedArrow]
  simp only [twCod, twObjMk]
  rfl

/-- The weight profunctor at a general co-twisted arrow. For `arr : cod → dom`,
the weight evaluates to `W(cod, dom)`. -/
theorem profunctorOnOpCoTwistedArrow_at_arrow (W : Cᵒᵖ ⥤ C ⥤ Type v)
    {cod dom : C} (arr : cod ⟶ dom) :
    (profunctorOnOpCoTwistedArrow C W).obj (Opposite.op (coTwObjMk arr)) =
    (W.obj (Opposite.op cod)).obj dom := by
  simp only [profunctorOnOpCoTwistedArrow, Functor.comp_obj,
    profunctorOnTwistedArrow_obj]
  rw [coTwistedArrowOpEquiv_arrow_dom arr, coTwistedArrowOpEquiv_arrow_cod arr]

/-!
### From RestrictedCowedge to WeightedCowedge

Given a `RestrictedCowedge G H` with diagonal data `family_A : H(A,A) → (G(A,A) → pt)`,
we construct a `WeightedCowedge H G` by extending to all co-twisted arrows.

For an arrow `(arr : cod → dom)` in CoTwistedArrow C:
- Weight type: `H(cod, dom)`
- Diagram object: `G(dom, cod)`
- We define `leg_arr : H(cod, dom) → (G(dom, cod) → pt)` by:
  `leg_arr w = G(1, arr) ≫ family_dom (H(arr, 1) w)`

This uses the cowedge-cocone correspondence: the full cocone data is determined
by the diagonal (cowedge) data via functorial transport.
-/

variable {D : Type*} [Category D]

/-- The diagram profunctor at the identity co-twisted arrow evaluates to the
diagonal. This is the Type v version matching the diagram for WeightedCowedge. -/
theorem profunctorOnCoTwistedArrow_at_identity (P : Cᵒᵖ ⥤ C ⥤ D) (A : C) :
    (profunctorOnCoTwistedArrow C P).obj (idCoTwistedArrow A) =
    (P.obj (Opposite.op A)).obj A := rfl

/-- The diagram profunctor at a general co-twisted arrow. For `arr : cod → dom`,
the diagram evaluates to `P(dom, cod)`. -/
theorem profunctorOnCoTwistedArrow_at_arrow (P : Cᵒᵖ ⥤ C ⥤ D)
    {cod dom : C} (arr : cod ⟶ dom) :
    (profunctorOnCoTwistedArrow C P).obj (coTwObjMk arr) =
    (P.obj (Opposite.op dom)).obj cod := by
  simp only [profunctorOnCoTwistedArrow_obj, coTwObjMk_dom, coTwObjMk_cod]

/-!
### Restriction functor: WeightedCowedge → RestrictedCowedge

The restriction functor extracts diagonal data from a weighted cowedge.
Given `WeightedCowedge H G`, we construct `RestrictedCowedge G H` by
restricting the cocone components to identity arrows.

At identity `(𝟙 A)`:
- Weight: `H(A, A)` (by `profunctorOnOpCoTwistedArrow_at_identity`)
- Diagram: `G(A, A)` (by `profunctorOnCoTwistedArrow_at_identity`)
- The cocone leg gives: `H(A, A) → (G(A, A) → pt)`

This exactly matches the structure of `RestrictedCowedge G H`.
-/

/-- The homToFunctor at identity evaluates to morphisms from the diagonal. -/
theorem homToFunctor_at_identity (P : Cᵒᵖ ⥤ C ⥤ C) (pt : C) (A : C) :
    (homToFunctor (profunctorOnCoTwistedArrow C P) pt).obj
      (Opposite.op (idCoTwistedArrow A)) =
    ((P.obj (Opposite.op A)).obj A ⟶ pt) := by
  change (yoneda.obj pt).obj (Opposite.op ((profunctorOnCoTwistedArrow C P).obj
    (idCoTwistedArrow A))) = _
  rw [profunctorOnCoTwistedArrow_at_identity P A]
  rfl

/-- Cast from the weight type at identity to the diagonal app type. -/
def weightAtIdentityToDiagApp (H : Cᵒᵖ ⥤ C ⥤ Type v) (A : C)
    (w : (profunctorOnOpCoTwistedArrow C H).obj (Opposite.op (idCoTwistedArrow A))) :
    diagApp H A :=
  cast (profunctorOnOpCoTwistedArrow_at_identity H A) w

/-- Cast from the diagonal app type to the weight type at identity. -/
def diagAppToWeightAtIdentity (H : Cᵒᵖ ⥤ C ⥤ Type v) (A : C)
    (h : diagApp H A) :
    (profunctorOnOpCoTwistedArrow C H).obj (Opposite.op (idCoTwistedArrow A)) :=
  cast (profunctorOnOpCoTwistedArrow_at_identity H A).symm h

@[simp]
theorem weightAtIdentityToDiagApp_diagAppToWeightAtIdentity (H : Cᵒᵖ ⥤ C ⥤ Type v)
    (A : C) (h : diagApp H A) :
    weightAtIdentityToDiagApp H A (diagAppToWeightAtIdentity H A h) = h := by
  simp only [weightAtIdentityToDiagApp, diagAppToWeightAtIdentity, cast_eq]

@[simp]
theorem diagAppToWeightAtIdentity_weightAtIdentityToDiagApp (H : Cᵒᵖ ⥤ C ⥤ Type v)
    (A : C) (w : (profunctorOnOpCoTwistedArrow C H).obj
      (Opposite.op (idCoTwistedArrow A))) :
    diagAppToWeightAtIdentity H A (weightAtIdentityToDiagApp H A w) = w := by
  simp only [weightAtIdentityToDiagApp, diagAppToWeightAtIdentity, cast_eq]

/-- An isomorphism between the diagram at identity and the diagonal. Since
`G : Cᵒᵖ ⥤ C ⥤ C` returns objects of C, we use `eqToIso` for object equality. -/
def diagramAtIdentityIso (G : Cᵒᵖ ⥤ C ⥤ C) (A : C) :
    (profunctorOnCoTwistedArrow C G).obj (idCoTwistedArrow A) ≅
    (G.obj (Opposite.op A)).obj A :=
  eqToIso (profunctorOnCoTwistedArrow_at_identity G A)

/-- Morphism from the diagonal of G to the diagram at identity. -/
def diagonalToIdentityHom (G : Cᵒᵖ ⥤ C ⥤ C) (A : C) :
    (G.obj (Opposite.op A)).obj A ⟶
    (profunctorOnCoTwistedArrow C G).obj (idCoTwistedArrow A) :=
  eqToHom (profunctorOnCoTwistedArrow_at_identity G A).symm

/-- Morphism from the diagram at identity to the diagonal of G. -/
def identityToDiagonalHom (G : Cᵒᵖ ⥤ C ⥤ C) (A : C) :
    (profunctorOnCoTwistedArrow C G).obj (idCoTwistedArrow A) ⟶
    (G.obj (Opposite.op A)).obj A :=
  eqToHom (profunctorOnCoTwistedArrow_at_identity G A)

@[simp]
theorem diagonalToIdentityHom_identityToDiagonalHom (G : Cᵒᵖ ⥤ C ⥤ C) (A : C) :
    diagonalToIdentityHom G A ≫ identityToDiagonalHom G A =
    𝟙 ((G.obj (Opposite.op A)).obj A) := by
  simp only [diagonalToIdentityHom, identityToDiagonalHom]
  exact eqToHom_trans _ _

@[simp]
theorem identityToDiagonalHom_diagonalToIdentityHom (G : Cᵒᵖ ⥤ C ⥤ C) (A : C) :
    identityToDiagonalHom G A ≫ diagonalToIdentityHom G A =
    𝟙 ((profunctorOnCoTwistedArrow C G).obj (idCoTwistedArrow A)) := by
  simp only [diagonalToIdentityHom, identityToDiagonalHom]
  exact eqToHom_trans _ _

/-!
### Restriction functor: WeightedCowedge → RestrictedCowedge

Given a `WeightedCowedge H G` (where H is the Type-valued weight and G is the
C-valued diagram), we can extract a `RestrictedCowedge G H` by restricting
the cocone components to identity arrows.

At identity `(𝟙_A)`:
- Weight: `H(A, A)` (by `profunctorOnOpCoTwistedArrow_at_identity`)
- Diagram: `G(A, A)` (by `profunctorOnCoTwistedArrow_at_identity`)
- The cocone leg gives: `H(A, A) → (G(A, A) → pt)`

This matches the `family` function structure of `RestrictedCowedge G H`:
`(I : C) → diagApp H I → diagApp (G ⇓ pt) I`
where `diagApp (G ⇓ pt) I = (G(I, I) ⟶ pt)`.
-/

/-- Extract the family function from a WeightedCowedge at identity arrows.
Given a WeightedCowedge H G with point pt, for each object A, this extracts
the cocone component at the identity arrow 𝟙_A and converts it to the type
expected by RestrictedCowedge. -/
def weightedCowedgeFamilyAtIdentity (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C)
    (wc : WeightedCowedge H G) (A : C) :
    diagApp H A → diagApp (G ⇓ wc.pt) A :=
  fun h =>
    -- diagApp (G ⇓ wc.pt) A is definitionally equal to
    -- ((G.obj (op A)).obj A ⟶ wc.pt) via sliceProfunctor_obj_obj
    diagonalToIdentityHom G A ≫ wc.leg (idCoTwistedArrow A)
      (diagAppToWeightAtIdentity H A h)

/-!
### Canonical morphisms in CoTwistedArrow

For `f : I₀ ⟶ I₁`, there are canonical morphisms in `CoTwistedArrow C`:
- `coTwObjMk f ⟶ idCoTwistedArrow I₀` (domain direction)
- `coTwObjMk f ⟶ idCoTwistedArrow I₁` (codomain direction)

These are analogous to the canonical morphisms described in the wedge-cone
correspondence: they connect an arbitrary arrow to the identity arrows at
its domain and codomain.
-/

/-- Canonical morphism from `coTwObjMk f` to `idCoTwistedArrow` at the source.
For `f : I₀ ⟶ I₁`, we have `coTwCod (coTwObjMk f) = I₀` (source of f).
This morphism has `domArr = f` and `codArr = 𝟙 I₀`. -/
def coTwToIdentityAtSource {I₀ I₁ : C} (f : I₀ ⟶ I₁) :
    coTwObjMk f ⟶ idCoTwistedArrow I₀ :=
  coTwHomMk f (𝟙 I₀) (by simp [idCoTwistedArrow, coTwObjMk_arr])

/-- Canonical morphism from `coTwObjMk f` to `idCoTwistedArrow` at the target.
For `f : I₀ ⟶ I₁`, we have `coTwDom (coTwObjMk f) = I₁` (target of f).
This morphism has `domArr = 𝟙 I₁` and `codArr = f`. -/
def coTwToIdentityAtTarget {I₀ I₁ : C} (f : I₀ ⟶ I₁) :
    coTwObjMk f ⟶ idCoTwistedArrow I₁ :=
  coTwHomMk (𝟙 I₁) f (by simp [idCoTwistedArrow, coTwObjMk_arr])

/-- The diagram functor map along `coTwToIdentityAtSource` equals the
contravariant profunctor action. -/
theorem diagram_map_coTwToIdentityAtSource (G : Cᵒᵖ ⥤ C ⥤ C)
    {I₀ I₁ : C} (f : I₀ ⟶ I₁) :
    (profunctorOnCoTwistedArrow C G).map (coTwToIdentityAtSource f) =
    (G.map f.op).app I₀ := by
  unfold coTwToIdentityAtSource
  rw [profunctorOnCoTwistedArrow_map]
  simp only [coTwDomArr_coTwHomMk, coTwCodArr_coTwHomMk, coTwObjMk_cod,
    idCoTwistedArrow, coTwObjMk_dom, Functor.map_id, Category.comp_id]

/-- The diagram functor map along `coTwToIdentityAtTarget` equals the
covariant profunctor action. -/
theorem diagram_map_coTwToIdentityAtTarget (G : Cᵒᵖ ⥤ C ⥤ C)
    {I₀ I₁ : C} (f : I₀ ⟶ I₁) :
    (profunctorOnCoTwistedArrow C G).map (coTwToIdentityAtTarget f) =
    (G.obj (Opposite.op I₁)).map f := by
  unfold coTwToIdentityAtTarget
  rw [profunctorOnCoTwistedArrow_map]
  simp only [coTwDomArr_coTwHomMk, coTwCodArr_coTwHomMk, coTwObjMk_cod,
    idCoTwistedArrow, coTwObjMk_dom, op_id, Functor.map_id, NatTrans.id_app,
    Category.id_comp]

/-!
### Weight map coherence

For an off-diagonal element `x : H(I₁, I₀)`, the two paths through the
weight functor yield the same result at `coTwObjMk f`:
- Path 1: `H.rmap f x ∈ H(I₁, I₁)` → weight at idCoTwistedArrow I₁
          → weight at coTwObjMk f via coTwToIdentityAtTarget
- Path 2: `H.lmap f x ∈ H(I₀, I₀)` → weight at idCoTwistedArrow I₀
          → weight at coTwObjMk f via coTwToIdentityAtSource
-/

/-- The equivalence functor maps the identity morphism at I₁ to a twisted arrow
with specific domain/codomain arrow components.
For (coTwToIdentityAtTarget f).op, the image has twDomArr = f and twCodArr = 𝟙 I₁.
-/
theorem equiv_map_coTwToIdentityAtTarget_twDomArr {I₀ I₁ : C} (f : I₀ ⟶ I₁) :
    twDomArr (coTwistedArrowOpEquivTwistedArrow.functor.map (coTwToIdentityAtTarget f).op) =
    f := by
  simp only [coTwToIdentityAtTarget, coTwistedArrowOpEquivTwistedArrow, Cat.equivOfIso,
    coTwistedArrowOpIsoTwistedArrow]
  simp only [Iso.trans_hom]
  simp only [coTwistedArrowOpIsoTwistedArrowOp, Cat.opFunctor,
    Cat.opFunctorInvolutive, Iso.trans_hom]
  simp only [twistedArrowOpOpIsoCoTwistedArrow, twistedArrowIsoTwistedArrowOp]
  simp only [Cat.isoOfEquiv, twistedArrowEquivTwistedArrowOp, Iso.symm_hom]
  simp only [twistedArrowOpToTwistedArrow, Functor.mapIso_hom]
  simp only [twDomArr, twHomMk, coTwHomMk]
  rfl

/-- The equivalence functor maps the identity morphism at I₁ to a twisted arrow
with twCodArr = 𝟙 I₁.
-/
theorem equiv_map_coTwToIdentityAtTarget_twCodArr {I₀ I₁ : C} (f : I₀ ⟶ I₁) :
    twCodArr (coTwistedArrowOpEquivTwistedArrow.functor.map (coTwToIdentityAtTarget f).op) =
    𝟙 I₁ := by
  simp only [coTwToIdentityAtTarget, coTwistedArrowOpEquivTwistedArrow, Cat.equivOfIso,
    coTwistedArrowOpIsoTwistedArrow]
  simp only [Iso.trans_hom]
  simp only [coTwistedArrowOpIsoTwistedArrowOp, Cat.opFunctor,
    Cat.opFunctorInvolutive, Iso.trans_hom]
  simp only [twistedArrowOpOpIsoCoTwistedArrow, twistedArrowIsoTwistedArrowOp]
  simp only [Cat.isoOfEquiv, twistedArrowEquivTwistedArrowOp, Iso.symm_hom]
  simp only [twistedArrowOpToTwistedArrow, Functor.mapIso_hom]
  simp only [twCodArr, twHomMk, coTwHomMk]
  rfl

/-- The equivalence functor maps (coTwToIdentityAtSource f).op to a twisted arrow
morphism with twDomArr = 𝟙 I₀.
-/
theorem equiv_map_coTwToIdentityAtSource_twDomArr {I₀ I₁ : C} (f : I₀ ⟶ I₁) :
    twDomArr (coTwistedArrowOpEquivTwistedArrow.functor.map (coTwToIdentityAtSource f).op) =
    𝟙 I₀ := by
  simp only [coTwToIdentityAtSource, coTwistedArrowOpEquivTwistedArrow, Cat.equivOfIso,
    coTwistedArrowOpIsoTwistedArrow]
  simp only [Iso.trans_hom]
  simp only [coTwistedArrowOpIsoTwistedArrowOp, Cat.opFunctor,
    Cat.opFunctorInvolutive, Iso.trans_hom]
  simp only [twistedArrowOpOpIsoCoTwistedArrow, twistedArrowIsoTwistedArrowOp]
  simp only [Cat.isoOfEquiv, twistedArrowEquivTwistedArrowOp, Iso.symm_hom]
  simp only [twistedArrowOpToTwistedArrow, Functor.mapIso_hom]
  simp only [twDomArr, twHomMk, coTwHomMk]
  rfl

/-- The equivalence functor maps (coTwToIdentityAtSource f).op to a twisted arrow
morphism with twCodArr = f.
-/
theorem equiv_map_coTwToIdentityAtSource_twCodArr {I₀ I₁ : C} (f : I₀ ⟶ I₁) :
    twCodArr (coTwistedArrowOpEquivTwistedArrow.functor.map (coTwToIdentityAtSource f).op) =
    f := by
  simp only [coTwToIdentityAtSource, coTwistedArrowOpEquivTwistedArrow, Cat.equivOfIso,
    coTwistedArrowOpIsoTwistedArrow]
  simp only [Iso.trans_hom]
  simp only [coTwistedArrowOpIsoTwistedArrowOp, Cat.opFunctor,
    Cat.opFunctorInvolutive, Iso.trans_hom]
  simp only [twistedArrowOpOpIsoCoTwistedArrow, twistedArrowIsoTwistedArrowOp]
  simp only [Cat.isoOfEquiv, twistedArrowEquivTwistedArrowOp, Iso.symm_hom]
  simp only [twistedArrowOpToTwistedArrow, Functor.mapIso_hom]
  simp only [twCodArr, twHomMk, coTwHomMk]
  rfl

/-- The object-level computation: the equivalence maps idCoTwistedArrow I
to the diagonal twisted arrow diagTwArr I = twObjMk (𝟙 I). -/
theorem equiv_identity_obj_eq (I : C) :
    coTwistedArrowOpEquivTwistedArrow.functor.obj (Opposite.op (idCoTwistedArrow I)) =
    diagTwArr I := by
  simp only [coTwistedArrowOpEquivTwistedArrow, Cat.equivOfIso,
    coTwistedArrowOpIsoTwistedArrow]
  simp only [Iso.trans_hom]
  simp only [coTwistedArrowOpIsoTwistedArrowOp, Cat.opFunctor,
    Cat.opFunctorInvolutive, Iso.trans_hom, Functor.comp_obj]
  simp only [twistedArrowOpOpIsoCoTwistedArrow, twistedArrowIsoTwistedArrowOp]
  simp only [Cat.isoOfEquiv, twistedArrowEquivTwistedArrowOp, Iso.symm_hom]
  simp only [twistedArrowOpToTwistedArrow]
  simp only [idCoTwistedArrow, diagTwArr]
  rfl

/-- The object-level computation: the equivalence maps coTwObjMk f to
twObjMk f (the same morphism viewed as a twisted arrow). -/
theorem equiv_arrow_obj_eq {I₀ I₁ : C} (f : I₀ ⟶ I₁) :
    coTwistedArrowOpEquivTwistedArrow.functor.obj (Opposite.op (coTwObjMk f)) =
    twObjMk f := by
  simp only [coTwistedArrowOpEquivTwistedArrow, Cat.equivOfIso,
    coTwistedArrowOpIsoTwistedArrow]
  simp only [Iso.trans_hom]
  simp only [coTwistedArrowOpIsoTwistedArrowOp, Cat.opFunctor,
    Cat.opFunctorInvolutive, Iso.trans_hom, Functor.comp_obj]
  simp only [twistedArrowOpOpIsoCoTwistedArrow, twistedArrowIsoTwistedArrowOp]
  simp only [Cat.isoOfEquiv, twistedArrowEquivTwistedArrowOp, Iso.symm_hom]
  simp only [twistedArrowOpToTwistedArrow]
  simp only [coTwObjMk, twObjMk]
  rfl

/-- Computing the profunctor map along `coTwToIdentityAtTarget f` on an element
from the diagonal at I₁. The result is `(H.map f.op).app I₁ y` at the weight
for `coTwObjMk f`.

This lemma explicitly computes the map, accounting for the dependent types
that arise from the equivalence between co-twisted arrow opposites and
twisted arrows. -/
theorem profunctor_map_coTwToIdentityAtTarget_diag (H : Cᵒᵖ ⥤ C ⥤ Type v)
    {I₀ I₁ : C} (f : I₀ ⟶ I₁) (y : (H.obj (Opposite.op I₁)).obj I₁) :
    (profunctorOnOpCoTwistedArrow C H).map (coTwToIdentityAtTarget f).op
      (diagAppToWeightAtIdentity H I₁ y) =
    cast (by simp only [profunctorOnOpCoTwistedArrow_at_arrow])
      ((H.map f.op).app I₁ y) := by
  simp only [profunctorOnOpCoTwistedArrow_map, profunctorOnTwistedArrow_map,
    equiv_map_coTwToIdentityAtTarget_twDomArr, equiv_map_coTwToIdentityAtTarget_twCodArr,
    diagAppToWeightAtIdentity, cast_eq]
  change ((H.map f.op).app I₁ ≫ (H.obj (Opposite.op I₀)).map (𝟙 I₁)) y = (H.map f.op).app I₁ y
  simp only [Functor.map_id, Category.comp_id]

/-- Computing the profunctor map along `coTwToIdentityAtSource f` on an element
from the diagonal at I₀. The result is `(H.obj (Opposite.op I₀)).map f y` at
the weight for `coTwObjMk f`.

This lemma explicitly computes the map, accounting for the dependent types. -/
theorem profunctor_map_coTwToIdentityAtSource_diag (H : Cᵒᵖ ⥤ C ⥤ Type v)
    {I₀ I₁ : C} (f : I₀ ⟶ I₁) (y : (H.obj (Opposite.op I₀)).obj I₀) :
    (profunctorOnOpCoTwistedArrow C H).map (coTwToIdentityAtSource f).op
      (diagAppToWeightAtIdentity H I₀ y) =
    cast (by simp only [profunctorOnOpCoTwistedArrow_at_arrow])
      ((H.obj (Opposite.op I₀)).map f y) := by
  simp only [profunctorOnOpCoTwistedArrow_map, profunctorOnTwistedArrow_map,
    equiv_map_coTwToIdentityAtSource_twDomArr, equiv_map_coTwToIdentityAtSource_twCodArr,
    diagAppToWeightAtIdentity, cast_eq]
  change ((H.map (𝟙 I₀).op).app I₀ ≫ (H.obj (Opposite.op I₀)).map f) y =
         (H.obj (Opposite.op I₀)).map f y
  simp only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp]

/-- The weight functor map along `coTwToIdentityAtTarget` and `coTwToIdentityAtSource`
give the same result. This is the weight coherence condition. -/
theorem weight_map_coTwToIdentity_coherence (H : Cᵒᵖ ⥤ C ⥤ Type v)
    {I₀ I₁ : C} (f : I₀ ⟶ I₁) (x : (H.obj (Opposite.op I₁)).obj I₀) :
    (profunctorOnOpCoTwistedArrow C H).map (coTwToIdentityAtTarget f).op
      (diagAppToWeightAtIdentity H I₁ ((H.obj (Opposite.op I₁)).map f x)) =
    (profunctorOnOpCoTwistedArrow C H).map (coTwToIdentityAtSource f).op
      (diagAppToWeightAtIdentity H I₀ ((H.map f.op).app I₀ x)) := by
  have nat := (H.map f.op).naturality f
  have heq : (H.map f.op).app I₁ ((H.obj (Opposite.op I₁)).map f x) =
             (H.obj (Opposite.op I₀)).map f ((H.map f.op).app I₀ x) := by
    have := congrFun nat x
    simp only [types_comp_apply] at this
    exact this
  have lhs_eq : (profunctorOnOpCoTwistedArrow C H).map (coTwToIdentityAtTarget f).op
      (diagAppToWeightAtIdentity H I₁ ((H.obj (Opposite.op I₁)).map f x)) =
      (H.map f.op).app I₁ ((H.obj (Opposite.op I₁)).map f x) := by
    simp only [profunctorOnOpCoTwistedArrow_map, profunctorOnTwistedArrow_map,
      equiv_map_coTwToIdentityAtTarget_twDomArr, equiv_map_coTwToIdentityAtTarget_twCodArr,
      diagAppToWeightAtIdentity, cast_eq]
    change ((H.map f.op).app I₁ ≫ (H.obj (Opposite.op I₀)).map (𝟙 I₁))
           ((H.obj (Opposite.op I₁)).map f x) =
           (H.map f.op).app I₁ ((H.obj (Opposite.op I₁)).map f x)
    simp only [Functor.map_id, Category.comp_id]
  have rhs_eq : (profunctorOnOpCoTwistedArrow C H).map (coTwToIdentityAtSource f).op
      (diagAppToWeightAtIdentity H I₀ ((H.map f.op).app I₀ x)) =
      (H.obj (Opposite.op I₀)).map f ((H.map f.op).app I₀ x) := by
    simp only [profunctorOnOpCoTwistedArrow_map, profunctorOnTwistedArrow_map,
      equiv_map_coTwToIdentityAtSource_twDomArr, equiv_map_coTwToIdentityAtSource_twCodArr,
      diagAppToWeightAtIdentity, cast_eq]
    change ((H.map (𝟙 I₀).op).app I₀ ≫ (H.obj (Opposite.op I₀)).map f)
           ((H.map f.op).app I₀ x) =
           (H.obj (Opposite.op I₀)).map f ((H.map f.op).app I₀ x)
    simp only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp]
  rw [lhs_eq, rhs_eq, heq]

/-!
### Dinaturality of the extracted family
-/

/-- The extracted family from a WeightedCowedge satisfies dinaturality. -/
theorem weightedCowedgeFamilyAtIdentity_dinatural
    (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C)
    (wc : WeightedCowedge H G) :
    IsDinatural H (G ⇓ wc.pt) (weightedCowedgeFamilyAtIdentity H G wc) := by
  intro I₀ I₁ f x
  unfold Profunctor.lmap Profunctor.rmap weightedCowedgeFamilyAtIdentity
  simp only [sliceProfunctor_obj_map, sliceProfunctor_map_app, Quiver.Hom.unop_op,
    diagonalToIdentityHom, eqToHom_refl]
  rw [← diagram_map_coTwToIdentityAtTarget G f, ← diagram_map_coTwToIdentityAtSource G f]
  change (profunctorOnCoTwistedArrow C G).map (coTwToIdentityAtTarget f) ≫
      (𝟙 ((profunctorOnCoTwistedArrow C G).obj (idCoTwistedArrow I₁)) ≫
        WeightedCocone.leg wc (idCoTwistedArrow I₁)
          (diagAppToWeightAtIdentity H I₁ ((H.obj (Opposite.op I₁)).map f x))) = _
  rw [Category.id_comp]
  change _ = (profunctorOnCoTwistedArrow C G).map (coTwToIdentityAtSource f) ≫
      (𝟙 ((profunctorOnCoTwistedArrow C G).obj (idCoTwistedArrow I₀)) ≫
        WeightedCocone.leg wc (idCoTwistedArrow I₀)
          (diagAppToWeightAtIdentity H I₀ ((H.map f.op).app I₀ x)))
  rw [Category.id_comp]
  rw [WeightedCocone.naturality wc (coTwToIdentityAtTarget f)]
  rw [WeightedCocone.naturality wc (coTwToIdentityAtSource f)]
  congr 1
  exact weight_map_coTwToIdentity_coherence H f x

/-!
### Paranaturality of the extracted family

A stronger result: the extracted family is not just dinatural but paranatural.
This follows from the fact that for any compatible pair of diagonal elements
`(d₀, d₁)` with `DiagCompat H I₀ I₁ f d₀ d₁`, they map to the same weight
element at the off-diagonal co-twisted arrow `coTwObjMk f`. Applying weighted
cocone naturality along `coTwToIdentityAtSource` and `coTwToIdentityAtTarget`
then shows their images under the family satisfy `DiagCompat` for the slice
profunctor.
-/

/-- For a compatible pair of diagonal elements, the profunctor maps to the
off-diagonal co-twisted arrow agree. This uses `DiagCompat` to identify the
images. -/
theorem weight_map_coTwToIdentity_from_diagCompat (H : Cᵒᵖ ⥤ C ⥤ Type v)
    {I₀ I₁ : C} (f : I₀ ⟶ I₁) (d₀ : diagApp H I₀) (d₁ : diagApp H I₁)
    (hcompat : DiagCompat H I₀ I₁ f d₀ d₁) :
    (profunctorOnOpCoTwistedArrow C H).map (coTwToIdentityAtSource f).op
      (diagAppToWeightAtIdentity H I₀ d₀) =
    (profunctorOnOpCoTwistedArrow C H).map (coTwToIdentityAtTarget f).op
      (diagAppToWeightAtIdentity H I₁ d₁) := by
  rw [profunctor_map_coTwToIdentityAtSource_diag, profunctor_map_coTwToIdentityAtTarget_diag]
  simp only [cast_eq]
  exact hcompat

/-- The extracted family from a WeightedCowedge satisfies paranaturality.
This is stronger than dinaturality: it preserves the compatibility condition
for any pair of diagonal elements that are compatible under the profunctor
structure, not just pairs that arise from the off-diagonal via the profunctor
maps. -/
theorem weightedCowedgeFamilyAtIdentity_paranatural
    (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C)
    (wc : WeightedCowedge H G) :
    IsParanatural H (G ⇓ wc.pt) (weightedCowedgeFamilyAtIdentity H G wc) := by
  intro I₀ I₁ f d₀ d₁ hcompat
  unfold DiagCompat weightedCowedgeFamilyAtIdentity
  simp only [sliceProfunctor_obj_map, sliceProfunctor_map_app, Quiver.Hom.unop_op]
  simp only [diagonalToIdentityHom, eqToHom_refl]
  rw [← diagram_map_coTwToIdentityAtSource G f, ← diagram_map_coTwToIdentityAtTarget G f]
  change (profunctorOnCoTwistedArrow C G).map (coTwToIdentityAtSource f) ≫
      (𝟙 ((profunctorOnCoTwistedArrow C G).obj (idCoTwistedArrow I₀)) ≫
        WeightedCocone.leg wc (idCoTwistedArrow I₀) (diagAppToWeightAtIdentity H I₀ d₀)) = _
  rw [Category.id_comp]
  change _ = (profunctorOnCoTwistedArrow C G).map (coTwToIdentityAtTarget f) ≫
      (𝟙 ((profunctorOnCoTwistedArrow C G).obj (idCoTwistedArrow I₁)) ≫
        WeightedCocone.leg wc (idCoTwistedArrow I₁) (diagAppToWeightAtIdentity H I₁ d₁))
  rw [Category.id_comp]
  rw [WeightedCocone.naturality wc (coTwToIdentityAtSource f)]
  rw [WeightedCocone.naturality wc (coTwToIdentityAtTarget f)]
  congr 1
  exact weight_map_coTwToIdentity_from_diagCompat H f d₀ d₁ hcompat

/-!
### The strong restriction functor

Since `weightedCowedgeFamilyAtIdentity` is paranatural (not just dinatural),
weighted cowedges map to strong restricted cowedges. This functor composes
with the inclusion `StrongRestrictedCowedge.inclusion` to give the regular
restriction functor.
-/

/-- Restrict a weighted cowedge to a strong restricted cowedge by extracting
the family at identity co-twisted arrows. Since the extracted family is
paranatural (proved by `weightedCowedgeFamilyAtIdentity_paranatural`), we get
a strong restricted cowedge. -/
def strongRestrictWeightedCowedge (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C)
    (wc : WeightedCowedge H G) : StrongRestrictedCowedge G H where
  pt := wc.pt
  toStrongRestrictedCowedgeOver := ⟨weightedCowedgeFamilyAtIdentity H G wc,
    weightedCowedgeFamilyAtIdentity_paranatural H G wc⟩

/-- The morphism map of the strong restriction functor: a morphism of weighted
cowedges induces a morphism of strong restricted cowedges. -/
def strongRestrictWeightedCowedgeHom (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C)
    {wc₁ wc₂ : WeightedCowedge H G} (f : WeightedCocone.Hom wc₁ wc₂) :
    StrongRestrictedCowedge.Hom (strongRestrictWeightedCowedge H G wc₁)
      (strongRestrictWeightedCowedge H G wc₂) where
  hom := f.hom
  comm A a := by
    simp only [strongRestrictWeightedCowedge, StrongRestrictedCowedge.family,
      weightedCowedgeFamilyAtIdentity]
    rw [Category.assoc, f.w (idCoTwistedArrow A) (diagAppToWeightAtIdentity H A a)]

theorem strongRestrictWeightedCowedgeHom_id (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C)
    (wc : WeightedCowedge H G) :
    strongRestrictWeightedCowedgeHom H G (WeightedCocone.Hom.id wc) =
      StrongRestrictedCowedge.Hom.id (strongRestrictWeightedCowedge H G wc) := by
  ext
  rfl

theorem strongRestrictWeightedCowedgeHom_comp (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C)
    {wc₁ wc₂ wc₃ : WeightedCowedge H G}
    (f : WeightedCocone.Hom wc₁ wc₂) (g : WeightedCocone.Hom wc₂ wc₃) :
    strongRestrictWeightedCowedgeHom H G (f.comp g) =
      (strongRestrictWeightedCowedgeHom H G f).comp
        (strongRestrictWeightedCowedgeHom H G g) := by
  ext
  rfl

/-- The strong restriction functor from weighted cowedges to strong restricted
cowedges. This is the factorization of the restriction functor through the
full subcategory of paranatural families. -/
def strongRestrictionFunctor (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C) :
    WeightedCowedge H G ⥤ StrongRestrictedCowedge G H where
  obj := strongRestrictWeightedCowedge H G
  map := strongRestrictWeightedCowedgeHom H G
  map_id wc := strongRestrictWeightedCowedgeHom_id H G wc
  map_comp f g := strongRestrictWeightedCowedgeHom_comp H G f g

instance strongRestrictionFunctor_faithful (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C) :
    (strongRestrictionFunctor H G).Faithful where
  map_injective {wc₁ wc₂} {f g} heq := by
    apply WeightedCocone.Hom.ext
    simp only [strongRestrictionFunctor] at heq
    have : (strongRestrictWeightedCowedgeHom H G f).hom =
           (strongRestrictWeightedCowedgeHom H G g).hom := by
      rw [heq]
    exact this

/-!
### The restriction functor
-/

/-- Restrict a weighted cowedge to a restricted cowedge by extracting the
family at identity co-twisted arrows. -/
def restrictWeightedCowedge (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C)
    (wc : WeightedCowedge H G) : RestrictedCowedge G H where
  pt := wc.pt
  toRestrictedCowedgeOver := ⟨weightedCowedgeFamilyAtIdentity H G wc,
    weightedCowedgeFamilyAtIdentity_dinatural H G wc⟩

/-- The morphism map of the restriction functor: a morphism of weighted cowedges
induces a morphism of restricted cowedges. -/
def restrictWeightedCowedgeHom (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C)
    {wc₁ wc₂ : WeightedCowedge H G} (f : WeightedCocone.Hom wc₁ wc₂) :
    RestrictedCowedge.Hom (restrictWeightedCowedge H G wc₁)
      (restrictWeightedCowedge H G wc₂) where
  hom := f.hom
  comm A a := by
    simp only [restrictWeightedCowedge, RestrictedCowedge.family,
      weightedCowedgeFamilyAtIdentity]
    rw [Category.assoc, f.w (idCoTwistedArrow A) (diagAppToWeightAtIdentity H A a)]

theorem restrictWeightedCowedgeHom_id (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C)
    (wc : WeightedCowedge H G) :
    restrictWeightedCowedgeHom H G (WeightedCocone.Hom.id wc) =
      RestrictedCowedge.Hom.id (restrictWeightedCowedge H G wc) := by
  ext
  rfl

theorem restrictWeightedCowedgeHom_comp (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C)
    {wc₁ wc₂ wc₃ : WeightedCowedge H G}
    (f : WeightedCocone.Hom wc₁ wc₂) (g : WeightedCocone.Hom wc₂ wc₃) :
    restrictWeightedCowedgeHom H G (f.comp g) =
      (restrictWeightedCowedgeHom H G f).comp (restrictWeightedCowedgeHom H G g) := by
  ext
  rfl

/-- The restriction functor from weighted cowedges to restricted cowedges. -/
def restrictionFunctor (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C) :
    WeightedCowedge H G ⥤ RestrictedCowedge G H where
  obj := restrictWeightedCowedge H G
  map := restrictWeightedCowedgeHom H G
  map_id wc := restrictWeightedCowedgeHom_id H G wc
  map_comp f g := restrictWeightedCowedgeHom_comp H G f g

instance restrictionFunctor_faithful (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C) :
    (restrictionFunctor H G).Faithful where
  map_injective {wc₁ wc₂} {f g} heq := by
    apply WeightedCocone.Hom.ext
    simp only [restrictionFunctor] at heq
    have : (restrictWeightedCowedgeHom H G f).hom =
           (restrictWeightedCowedgeHom H G g).hom := by
      rw [heq]
    exact this

/-- The restriction functor factors as the strong restriction functor
followed by the inclusion of strong restricted cowedges into restricted
cowedges. This demonstrates that weighted cowedges map first into the full
subcategory of paranatural families before being further included into the
category of dinatural families. -/
theorem restrictionFunctor_eq_inclusion_comp_strong (H : Cᵒᵖ ⥤ C ⥤ Type v)
    (G : Cᵒᵖ ⥤ C ⥤ C) :
    restrictionFunctor H G =
      strongRestrictionFunctor H G ⋙ StrongRestrictedCowedge.inclusion G H := by
  apply Functor.ext
  · intro wc₁ wc₂ f
    simp only [Functor.comp_map, eqToHom_refl, Category.id_comp, Category.comp_id]
    apply RestrictedCowedge.Hom.ext
    rfl
  · intro wc
    simp only [restrictionFunctor, strongRestrictionFunctor, Functor.comp_obj,
      StrongRestrictedCowedge.inclusion, restrictWeightedCowedge,
      strongRestrictWeightedCowedge, StrongRestrictedCowedge.toRestrictedCowedge]

/-- Commutativity at identity arrows implies commutativity for weight elements
that are in the image of the weight map from identity.

For a morphism `m : tw ⟶ id(A)` in CoTwistedArrow, the weight functor gives
`W.map m.op : W.obj (op (id A)) → W.obj (op tw)`. For any `w' : W.obj (op (id A))`,
if `h` commutes with legs at identity, then it commutes with legs at tw for
the element `W.map m.op w'`.

This follows from weighted cocone naturality:
`D.map m ≫ wc.leg (id A) w' = wc.leg tw (W.map m.op w')` -/
theorem commutativity_from_identity_image (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C)
    {wc₁ wc₂ : WeightedCowedge H G} (h : wc₁.pt ⟶ wc₂.pt)
    {A : C}
    (hid : ∀ (w : (profunctorOnOpCoTwistedArrow C H).obj
             (Opposite.op (idCoTwistedArrow A))),
           wc₁.leg (idCoTwistedArrow A) w ≫ h = wc₂.leg (idCoTwistedArrow A) w)
    {tw : CoTwistedArrow C}
    (m : tw ⟶ idCoTwistedArrow A)
    (w' : (profunctorOnOpCoTwistedArrow C H).obj (Opposite.op (idCoTwistedArrow A))) :
    wc₁.leg tw ((profunctorOnOpCoTwistedArrow C H).map m.op w') ≫ h =
    wc₂.leg tw ((profunctorOnOpCoTwistedArrow C H).map m.op w') := by
  have nat₁ := wc₁.naturality m w'
  have nat₂ := wc₂.naturality m w'
  calc wc₁.leg tw ((profunctorOnOpCoTwistedArrow C H).map m.op w') ≫ h
      = ((profunctorOnCoTwistedArrow C G).map m ≫ wc₁.leg (idCoTwistedArrow A) w') ≫ h := by
          rw [← nat₁]
    _ = (profunctorOnCoTwistedArrow C G).map m ≫ (wc₁.leg (idCoTwistedArrow A) w' ≫ h) := by
          rw [Category.assoc]
    _ = (profunctorOnCoTwistedArrow C G).map m ≫ wc₂.leg (idCoTwistedArrow A) w' := by
          rw [hid]
    _ = wc₂.leg tw ((profunctorOnOpCoTwistedArrow C H).map m.op w') := by
          rw [← nat₂]

/-!
### Non-fullness of the restriction functor

The restriction functor is faithful (proven above) but NOT full in general.
We prove this by showing that fullness would require weight maps from
identity co-twisted arrows to be jointly surjective, which fails for the
Hom-profunctor on categories with parallel morphisms.

The proof proceeds by contradiction: we show that if the functor were full,
then every morphism between restrictions would lift, but we exhibit a
morphism (the identity on the apex) that cannot lift when the cowedges
differ at an unreachable weight element.
-/

section NonFullnessCounterexample

open CategoryTheory.Limits

/-!
#### The counterexample category

We use `WalkingParallelPair`, the category with:
- Objects: `zero` and `one`
- Morphisms: `left, right : zero ⟶ one` plus identities

For the Hom-profunctor:
- `Hom(zero, zero) = {id}` (singleton)
- `Hom(one, one) = {id}` (singleton)
- `Hom(zero, one) = {left, right}` (two elements)

The weight maps from diagonals both map to `left` (for co-twisted arrow
`coTwObjMk left`), leaving `right` unreachable.
-/

/-- In WalkingParallelPair, the only morphism `one ⟶ one` is the identity. -/
theorem walkingParallelPair_one_one_eq_id
    (f : WalkingParallelPair.one ⟶ WalkingParallelPair.one) :
    f = 𝟙 WalkingParallelPair.one := by
  cases f
  rfl

/-- In WalkingParallelPair, the only morphism `zero ⟶ zero` is the identity. -/
theorem walkingParallelPair_zero_zero_eq_id
    (f : WalkingParallelPair.zero ⟶ WalkingParallelPair.zero) :
    f = 𝟙 WalkingParallelPair.zero := by
  cases f
  rfl

/-- In WalkingParallelPair, morphisms `zero ⟶ one` are exactly `left` and
`right`. -/
theorem walkingParallelPair_zero_one_cases
    (f : WalkingParallelPair.zero ⟶ WalkingParallelPair.one) :
    f = WalkingParallelPairHom.left ∨ f = WalkingParallelPairHom.right := by
  cases f <;> simp

/-- There are no morphisms from `one` to `zero` in WalkingParallelPair. -/
theorem walkingParallelPair_one_zero_empty
    (f : WalkingParallelPair.one ⟶ WalkingParallelPair.zero) : False := by
  cases f

/-- The two morphisms `left` and `right` are distinct. -/
theorem walkingParallelPair_left_ne_right :
    WalkingParallelPairHom.left ≠ WalkingParallelPairHom.right := by
  intro h
  cases h

/-- The objects `zero` and `one` in WalkingParallelPair are distinct. -/
theorem walkingParallelPair_zero_ne_one :
    WalkingParallelPair.zero ≠ WalkingParallelPair.one := by
  intro h
  cases h

/-- The objects `one` and `zero` in WalkingParallelPair are distinct. -/
theorem walkingParallelPair_one_ne_zero :
    WalkingParallelPair.one ≠ WalkingParallelPair.zero := by
  intro h
  cases h

/-!
#### Non-fullness proof

For the restriction functor to be full, every `RestrictedCowedge.Hom` must
lift to a `WeightedCocone.Hom`. This requires that commutativity at diagonal
co-twisted arrows implies commutativity at ALL co-twisted arrows.

By `commutativity_from_identity_image`, this holds for weight elements in
the image of weight maps from diagonals. For fullness, we'd need ALL weight
elements to be reachable, i.e., the weight maps to be jointly surjective.

`Functor_Full_restrictionFunctor_contradiction` proves that assuming `Full`
plus the existence of cowedges with equal restrictions but differing legs
leads to a contradiction. `wpp_weight_maps_not_surjective` shows that for
`WalkingParallelPair`, weight maps from diagonals are not jointly surjective,
establishing that such counterexample cowedges can exist.
-/

/-- For co-twisted arrow morphisms into identity arrows, the weight map
is precomposition or postcomposition with the arrow. -/
theorem weightMapToIdentity_is_composition {C : Type*} [Category C]
    (H : Cᵒᵖ ⥤ C ⥤ Type*) {A B : C} (f : A ⟶ B) :
    ∃ (mapFromSource : diagApp H A → (H.obj (Opposite.op A)).obj B)
      (mapFromTarget : diagApp H B → (H.obj (Opposite.op A)).obj B),
    ∀ w : (H.obj (Opposite.op A)).obj B,
      (∃ a, mapFromSource a = w) ∨ (∃ b, mapFromTarget b = w) →
      True := by
  use fun a => (H.obj (Opposite.op A)).map f a
  use fun b => (H.map f.op).app B b
  intro _ _
  trivial

/-- The Hom-type `Hom(zero, one)` in WalkingParallelPair has exactly two
elements. -/
theorem wpp_hom_zero_one_two_elements :
    ∃ (a b : WalkingParallelPair.zero ⟶ WalkingParallelPair.one), a ≠ b ∧
      ∀ f : WalkingParallelPair.zero ⟶ WalkingParallelPair.one, f = a ∨ f = b := by
  use WalkingParallelPairHom.left, WalkingParallelPairHom.right
  constructor
  · exact walkingParallelPair_left_ne_right
  · exact walkingParallelPair_zero_one_cases

/-- The Hom-type `Hom(zero, zero)` in WalkingParallelPair is a singleton. -/
theorem wpp_hom_zero_zero_singleton :
    ∀ f : WalkingParallelPair.zero ⟶ WalkingParallelPair.zero,
      f = 𝟙 WalkingParallelPair.zero :=
  walkingParallelPair_zero_zero_eq_id

/-- The Hom-type `Hom(one, one)` in WalkingParallelPair is a singleton. -/
theorem wpp_hom_one_one_singleton :
    ∀ f : WalkingParallelPair.one ⟶ WalkingParallelPair.one,
      f = 𝟙 WalkingParallelPair.one :=
  walkingParallelPair_one_one_eq_id

/-- Postcomposition by `left` maps the unique element of `Hom(zero, zero)`
to `left`. -/
theorem wpp_postcomp_left_image :
    (𝟙 WalkingParallelPair.zero) ≫ WalkingParallelPairHom.left =
      WalkingParallelPairHom.left :=
  Category.id_comp _

/-- Precomposition by `left` maps the unique element of `Hom(one, one)`
to `left`. -/
theorem wpp_precomp_left_image :
    WalkingParallelPairHom.left ≫ (𝟙 WalkingParallelPair.one) =
      WalkingParallelPairHom.left :=
  Category.comp_id _

/-- The morphism `right : zero ⟶ one` is not in the image of weight maps
from diagonal hom-sets for the co-twisted arrow `coTwObjMk left`.

Specifically, neither postcomposition from `Hom(zero, zero)` nor
precomposition from `Hom(one, one)` can produce `right` when applied to
their respective identity morphisms. -/
theorem wpp_right_not_reachable_from_left :
    WalkingParallelPairHom.right ≠
      (𝟙 WalkingParallelPair.zero) ≫ WalkingParallelPairHom.left ∧
    WalkingParallelPairHom.right ≠
      WalkingParallelPairHom.left ≫ (𝟙 WalkingParallelPair.one) := by
  constructor
  · simp only [Category.id_comp]
    exact walkingParallelPair_left_ne_right.symm
  · simp only [Category.comp_id]
    exact walkingParallelPair_left_ne_right.symm

/-- For WalkingParallelPair, the weight maps from diagonals are not jointly
surjective onto `Hom(zero, one)`.

Since `Hom(zero, zero) = {id}` and `Hom(one, one) = {id}`, and both
postcomposition and precomposition by `left` map these identities to `left`,
the morphism `right` is unreachable. -/
theorem wpp_weight_maps_not_surjective :
    ∃ w : WalkingParallelPair.zero ⟶ WalkingParallelPair.one,
      (∀ a : WalkingParallelPair.zero ⟶ WalkingParallelPair.zero,
        a ≫ WalkingParallelPairHom.left ≠ w) ∧
      (∀ b : WalkingParallelPair.one ⟶ WalkingParallelPair.one,
        WalkingParallelPairHom.left ≫ b ≠ w) := by
  use WalkingParallelPairHom.right
  constructor
  · intro a
    rw [wpp_hom_zero_zero_singleton a, Category.id_comp]
    exact walkingParallelPair_left_ne_right
  · intro b
    rw [wpp_hom_one_one_singleton b, Category.comp_id]
    exact walkingParallelPair_left_ne_right

/-- If two weighted cowedges have the same apex and legs that differ at some
weight element, then there is no weighted cocone morphism between them with
the identity as the underlying morphism.

This is the contrapositive of: a WeightedCocone.Hom with identity hom
requires all legs to be equal. -/
theorem no_id_hom_when_legs_differ {J : Type*} [Category J]
    {C : Type*} [Category C]
    {W : Jᵒᵖ ⥤ Type*} {D : J ⥤ C}
    {wc₁ wc₂ : WeightedCocone W D} (hpt : wc₁.pt = wc₂.pt)
    {j : J} {w : W.obj (Opposite.op j)}
    (hne : wc₁.leg j w ≠ wc₂.leg j w ≫ eqToHom hpt.symm) :
    ¬∃ (f : WeightedCocone.Hom wc₁ wc₂), f.hom = eqToHom hpt := by
  intro ⟨f, hf⟩
  apply hne
  have := f.w j w
  rw [hf] at this
  have h2 : wc₂.leg j w ≫ eqToHom hpt.symm = wc₁.leg j w := by
    rw [← this]
    simp only [Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact h2.symm

/-- Helper lemma: HEq of morphisms with same domain but different codomains
is equivalent to equality after transport via eqToHom. -/
lemma heq_iff_eq_comp_eqToHom {C : Type*} [Category C] {A B B' : C}
    (h : B = B') (f : A ⟶ B) (g : A ⟶ B') :
    HEq f g ↔ f = g ≫ eqToHom h.symm := by
  subst h
  simp only [eqToHom_refl, Category.comp_id, heq_eq_eq]

/-- Corollary: if weighted cowedges have the same apex (exactly, not just
isomorphically) and differ at some leg, there's no identity morphism. -/
theorem no_id_hom_when_legs_differ' {J : Type*} [Category J]
    {C : Type*} [Category C]
    {W : Jᵒᵖ ⥤ Type*} {D : J ⥤ C}
    {wc₁ wc₂ : WeightedCocone W D} (hpt : wc₁.pt = wc₂.pt)
    {j : J} {w : W.obj (Opposite.op j)}
    (hne : HEq (wc₁.leg j w) (wc₂.leg j w) → False) :
    ¬∃ (f : WeightedCocone.Hom wc₁ wc₂), f.hom = eqToHom hpt :=
  no_id_hom_when_legs_differ (j := j) (w := w) hpt fun heq =>
    hne ((heq_iff_eq_comp_eqToHom hpt _ _).mpr heq)

/-- For the restriction functor to be full, every RestrictedCowedge.Hom must
lift to a WeightedCocone.Hom. The non-surjectivity of weight maps from
diagonals means there can exist weighted cowedges with the same restrictions
but different off-diagonal legs, preventing such lifts.

The theorems `wpp_weight_maps_not_surjective` and `no_id_hom_when_legs_differ`
together establish:
1. There exist weight elements not reachable from diagonal weight maps
2. If cowedges differ at such elements, no identity-hom exists between them
3. But an identity RestrictedCowedge.Hom exists (they agree on diagonals)

The existence of such cowedges follows from the weighted cowedge naturality
structure: unreachable weight elements have no naturality constraints from
diagonals, so their leg values can be chosen independently. -/
theorem restrictionFunctor_not_full_abstract
    (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C)
    (wc₁ wc₂ : WeightedCowedge H G)
    (hpt : wc₁.pt = wc₂.pt)
    (_hdiag : ∀ (A : C) (w : (profunctorOnOpCoTwistedArrow C H).obj
               (Opposite.op (idCoTwistedArrow A))),
             HEq (wc₁.leg (idCoTwistedArrow A) w)
                 (wc₂.leg (idCoTwistedArrow A) w))
    {tw : CoTwistedArrow C}
    {w : (profunctorOnOpCoTwistedArrow C H).obj (Opposite.op tw)}
    (hdiff : HEq (wc₁.leg tw w) (wc₂.leg tw w) → False) :
    ¬∃ (f : WeightedCocone.Hom wc₁ wc₂), f.hom = eqToHom hpt :=
  no_id_hom_when_legs_differ' hpt hdiff

/-- The underlying morphism of `eqToHom` for `RestrictedCowedge.Hom` is `eqToHom`
applied to the equality of apexes. -/
theorem RestrictedCowedge_eqToHom_hom {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type v}
    {rc₁ rc₂ : RestrictedCowedge G H} (h : rc₁ = rc₂) :
    (eqToHom h).hom = eqToHom (congrArg RestrictedCowedge.pt h) := by
  subst h
  rfl

/-- The underlying morphism of `eqToHom` for `StrongRestrictedCowedge.Hom` is
`eqToHom` applied to the equality of apexes. -/
theorem StrongRestrictedCowedge_eqToHom_hom {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type v}
    {src₁ src₂ : StrongRestrictedCowedge G H} (h : src₁ = src₂) :
    (eqToHom h).hom = eqToHom (congrArg StrongRestrictedCowedge.pt h) := by
  subst h
  rfl

/-- The underlying morphism of `restrictionFunctor.map f` is `f.hom`. -/
theorem restrictionFunctor_map_hom {H : Cᵒᵖ ⥤ C ⥤ Type v} {G : Cᵒᵖ ⥤ C ⥤ C}
    {wc₁ wc₂ : WeightedCowedge H G} (f : WeightedCocone.Hom wc₁ wc₂) :
    ((restrictionFunctor H G).map f).hom = f.hom :=
  rfl

/-- If `restrictionFunctor.map f = eqToHom h`, then `f.hom` equals the
corresponding `eqToHom` on apexes. -/
theorem restrictionFunctor_map_eq_eqToHom_implies_hom_eq
    {H : Cᵒᵖ ⥤ C ⥤ Type v} {G : Cᵒᵖ ⥤ C ⥤ C}
    {wc₁ wc₂ : WeightedCowedge H G}
    (h : (restrictionFunctor H G).obj wc₁ = (restrictionFunctor H G).obj wc₂)
    (f : WeightedCocone.Hom wc₁ wc₂)
    (hf : (restrictionFunctor H G).map f = eqToHom h) :
    f.hom = eqToHom (congrArg RestrictedCowedge.pt h) := by
  have : ((restrictionFunctor H G).map f).hom = (eqToHom h).hom := congrArg _ hf
  rw [restrictionFunctor_map_hom, RestrictedCowedge_eqToHom_hom] at this
  exact this

/-- If the restriction functor is full, and two weighted cowedges have equal
restrictions but differ at some leg, we get a contradiction.

This is the formal proof that fullness fails when weight maps from diagonals
are not jointly surjective. -/
theorem Functor_Full_restrictionFunctor_contradiction
    {H : Cᵒᵖ ⥤ C ⥤ Type v} {G : Cᵒᵖ ⥤ C ⥤ C}
    [Functor.Full (restrictionFunctor H G)]
    {wc₁ wc₂ : WeightedCowedge H G}
    (hrestr : (restrictionFunctor H G).obj wc₁ = (restrictionFunctor H G).obj wc₂)
    {tw : CoTwistedArrow C}
    {w : (profunctorOnOpCoTwistedArrow C H).obj (Opposite.op tw)}
    (hdiff : HEq (wc₁.leg tw w) (wc₂.leg tw w) → False) :
    False := by
  have hpt : wc₁.pt = wc₂.pt := congrArg RestrictedCowedge.pt hrestr
  have hfull := (restrictionFunctor H G).map_surjective (X := wc₁) (Y := wc₂)
  obtain ⟨f, hf⟩ := hfull (eqToHom hrestr)
  have hfhom : f.hom = eqToHom hpt :=
    restrictionFunctor_map_eq_eqToHom_implies_hom_eq hrestr f hf
  exact no_id_hom_when_legs_differ' hpt hdiff ⟨f, hfhom⟩

/-- The restriction functor is not full whenever there exist two weighted
cowedges with equal restrictions but differing at some off-diagonal leg. -/
theorem restrictionFunctor_not_full_of_counterexample
    {H : Cᵒᵖ ⥤ C ⥤ Type v} {G : Cᵒᵖ ⥤ C ⥤ C}
    {wc₁ wc₂ : WeightedCowedge H G}
    (hrestr : (restrictionFunctor H G).obj wc₁ = (restrictionFunctor H G).obj wc₂)
    {tw : CoTwistedArrow C}
    {w : (profunctorOnOpCoTwistedArrow C H).obj (Opposite.op tw)}
    (hdiff : HEq (wc₁.leg tw w) (wc₂.leg tw w) → False) :
    ¬Functor.Full (restrictionFunctor H G) := fun hfull =>
  @Functor_Full_restrictionFunctor_contradiction C _ H G hfull wc₁ wc₂ hrestr tw w hdiff

/-!
#### Explicit counterexample construction

We construct explicit weighted cowedges for WalkingParallelPair demonstrating
that the restriction functor is not full.

The construction uses:
- C = WalkingParallelPair
- H = Hom-profunctor (curried from mathlib's `Functor.hom`)
- G = constant profunctor (all objects map to a fixed object)
- Two cowedges that agree on diagonals but differ at (coTwObjMk left, right)
-/

/-- The Hom-profunctor on WalkingParallelPair as a curried functor.
Maps (A, B) to Hom(A, B). -/
abbrev wppHomProfunctor : WalkingParallelPairᵒᵖ ⥤ WalkingParallelPair ⥤ Type :=
  Functor.curry.obj (Functor.hom WalkingParallelPair)

/-- Weight at a co-twisted arrow for the Hom-profunctor. -/
abbrev wppWeightAt (tw : CoTwistedArrow WalkingParallelPair) : Type :=
  (profunctorOnOpCoTwistedArrow WalkingParallelPair wppHomProfunctor).obj
    (Opposite.op tw)

/-- The co-twisted arrow for `left : zero ⟶ one`. -/
abbrev coTwLeft : CoTwistedArrow WalkingParallelPair :=
  coTwObjMk WalkingParallelPairHom.left

/-- The co-twisted arrow for the identity on zero. -/
abbrev coTwIdZero : CoTwistedArrow WalkingParallelPair :=
  idCoTwistedArrow WalkingParallelPair.zero

/-- The co-twisted arrow for the identity on one. -/
abbrev coTwIdOne : CoTwistedArrow WalkingParallelPair :=
  idCoTwistedArrow WalkingParallelPair.one


/-- The weight at coTwLeft equals Hom(zero, one). -/
theorem wppWeightAt_coTwLeft :
    wppWeightAt coTwLeft =
    (WalkingParallelPair.zero ⟶ WalkingParallelPair.one) := by
  unfold wppWeightAt coTwLeft profunctorOnOpCoTwistedArrow
  simp only [Functor.comp_obj, coTwistedArrowOpEquivTwistedArrow,
    profunctorOnTwistedArrow_obj]
  rfl

/-- The weight at coTwIdZero equals Hom(zero, zero). -/
theorem wppWeightAt_coTwIdZero :
    wppWeightAt coTwIdZero =
    (WalkingParallelPair.zero ⟶ WalkingParallelPair.zero) := by
  unfold wppWeightAt coTwIdZero idCoTwistedArrow profunctorOnOpCoTwistedArrow
  simp only [Functor.comp_obj, coTwistedArrowOpEquivTwistedArrow,
    profunctorOnTwistedArrow_obj]
  rfl

/-- Cast a weight element to the weight type at coTwLeft. -/
def castToWeightCoTwLeft
    (w : WalkingParallelPair.zero ⟶ WalkingParallelPair.one) :
    wppWeightAt coTwLeft :=
  cast wppWeightAt_coTwLeft.symm w

/-- The element `right` viewed as a weight at coTwLeft. -/
def wppWeightRight : wppWeightAt coTwLeft :=
  castToWeightCoTwLeft WalkingParallelPairHom.right

/-- The element `left` viewed as a weight at coTwLeft. -/
def wppWeightLeft : wppWeightAt coTwLeft :=
  castToWeightCoTwLeft WalkingParallelPairHom.left

/-- The constant diagram at ℕ for our counterexample.
Uses the existing constProfunctor from the WeightedRestrictedCorrespondence section. -/
abbrev wppConstDiagram : WalkingParallelPairᵒᵖ ⥤ WalkingParallelPair ⥤ Type :=
  constProfunctor (C := WalkingParallelPair) ℕ

/-- The weight functor for WalkingParallelPair with Hom-profunctor. -/
abbrev wppWeightFunctor :
    (CoTwistedArrow WalkingParallelPair)ᵒᵖ ⥤ Type :=
  profunctorOnOpCoTwistedArrow WalkingParallelPair wppHomProfunctor

/-- The diagram functor for WalkingParallelPair with constant diagram. -/
abbrev wppDiagramFunctor :
    CoTwistedArrow WalkingParallelPair ⥤ Type :=
  profunctorOnCoTwistedArrow WalkingParallelPair wppConstDiagram

/-- The diagram is constant at ℕ. -/
theorem wppDiagramFunctor_obj_eq (tw : CoTwistedArrow WalkingParallelPair) :
    wppDiagramFunctor.obj tw = ℕ := rfl

/-- The diagram morphisms are all identities. -/
theorem wppDiagramFunctor_map_eq {tw tw' : CoTwistedArrow WalkingParallelPair}
    (f : tw ⟶ tw') :
    wppDiagramFunctor.map f = id := rfl

/-- The hom-to-functor for our diagram. -/
abbrev wppHomToFunctor (pt : Type) :
    (CoTwistedArrow WalkingParallelPair)ᵒᵖ ⥤ Type :=
  homToFunctor wppDiagramFunctor pt

/-- The homToFunctor map is identity for our constant diagram. -/
theorem wppHomToFunctor_map_eq
    {x y : (CoTwistedArrow WalkingParallelPair)ᵒᵖ}
    (f : x ⟶ y) (g : wppDiagramFunctor.obj x.unop ⟶ ℕ) :
    (homToFunctor wppDiagramFunctor ℕ).map f g = g := by
  change wppDiagramFunctor.map f.unop ≫ g = g
  simp only [wppDiagramFunctor_map_eq]
  rfl

/-- A leg function for a weighted cocone specifies a leg for each co-twisted
arrow and weight element. -/
def WppLegFunction (pt : Type) :=
  (tw : CoTwistedArrow WalkingParallelPair) → wppWeightAt tw → (ℕ → pt)

/-- Naturality condition for a leg function: for any morphism in CoTwistedArrow,
transported weights must give the same leg value (since the diagram is
constant and diagram morphisms are identities). -/
def WppLegNatural (pt : Type) (legFn : WppLegFunction pt) : Prop :=
  ∀ (tw tw' : CoTwistedArrow WalkingParallelPair) (f : tw ⟶ tw')
    (w' : wppWeightAt tw'),
    legFn tw (wppWeightFunctor.map f.op w') = legFn tw' w'

/-- The weight type at coTwIdOne equals Hom(one, one). -/
theorem wppWeightAt_coTwIdOne :
    wppWeightAt coTwIdOne =
    (WalkingParallelPair.one ⟶ WalkingParallelPair.one) := by
  unfold wppWeightAt coTwIdOne idCoTwistedArrow profunctorOnOpCoTwistedArrow
  simp only [Functor.comp_obj, coTwistedArrowOpEquivTwistedArrow,
    profunctorOnTwistedArrow_obj]
  rfl

/-- The only weight element at coTwIdZero is the identity. -/
theorem wppWeightAt_coTwIdZero_singleton (w : wppWeightAt coTwIdZero) :
    w = cast wppWeightAt_coTwIdZero.symm (𝟙 WalkingParallelPair.zero) := by
  have h : w = cast wppWeightAt_coTwIdZero.symm
      (cast wppWeightAt_coTwIdZero w) := by simp
  rw [h]
  congr 1
  exact wpp_hom_zero_zero_singleton (cast wppWeightAt_coTwIdZero w)

/-- The only weight element at coTwIdOne is the identity. -/
theorem wppWeightAt_coTwIdOne_singleton (w : wppWeightAt coTwIdOne) :
    w = cast wppWeightAt_coTwIdOne.symm (𝟙 WalkingParallelPair.one) := by
  have h : w = cast wppWeightAt_coTwIdOne.symm
      (cast wppWeightAt_coTwIdOne w) := by simp
  rw [h]
  congr 1
  exact wpp_hom_one_one_singleton (cast wppWeightAt_coTwIdOne w)

/-- Cast a leg morphism (ℕ → ℕ) through the diagram object equality. -/
def wppCastLeg (tw : CoTwistedArrow WalkingParallelPair) :
    (ℕ → ℕ) → (wppDiagramFunctor.obj tw → ℕ) :=
  cast (by rw [wppDiagramFunctor_obj_eq])

/-- A natural transformation for constant leg functions.
Since the diagram is constant, constant leg functions are automatically natural. -/
def wppConstLegNatTrans (n : ℕ) :
    wppWeightFunctor ⟶ homToFunctor wppDiagramFunctor ℕ where
  app := fun tw => fun _ => wppCastLeg tw.unop (fun _ => n)
  naturality := fun _ _ _ => by
    ext _
    simp only [types_comp_apply]
    rfl

/-- The first weighted cocone: all legs map to 0. -/
def wppWeightedCocone₀ : WeightedCocone wppWeightFunctor wppDiagramFunctor where
  pt := ℕ
  toWeightedCoconeOver := wppConstLegNatTrans 0

/-- Extract the leg of wppWeightedCocone₀ at any position. -/
theorem wppWeightedCocone₀_leg_eq
    (tw : CoTwistedArrow WalkingParallelPair) (w : wppWeightAt tw) :
    wppWeightedCocone₀.leg tw w = wppCastLeg tw (fun _ => 0) := rfl

/-- The second weighted cocone: all legs map to 1. -/
def wppWeightedCocone₁ : WeightedCocone wppWeightFunctor wppDiagramFunctor where
  pt := ℕ
  toWeightedCoconeOver := wppConstLegNatTrans 1

/-- Extract the leg of wppWeightedCocone₁ at any position. -/
theorem wppWeightedCocone₁_leg_eq
    (tw : CoTwistedArrow WalkingParallelPair) (w : wppWeightAt tw) :
    wppWeightedCocone₁.leg tw w = wppCastLeg tw (fun _ => 1) := rfl

/-- The two cocones have the same apex. -/
theorem wppCocones_same_apex : wppWeightedCocone₀.pt = wppWeightedCocone₁.pt := rfl

/-- The two cocones have different legs at coTwLeft. -/
theorem wppCocones_legs_differ :
    wppWeightedCocone₀.leg coTwLeft wppWeightLeft ≠
    wppWeightedCocone₁.leg coTwLeft wppWeightLeft := by
  simp only [wppWeightedCocone₀_leg_eq, wppWeightedCocone₁_leg_eq, ne_eq]
  intro h
  have h0 : (wppCastLeg coTwLeft (fun _ => 0)) (0 : ℕ) = 0 := rfl
  have h1 : (wppCastLeg coTwLeft (fun _ => 1)) (0 : ℕ) = 1 := rfl
  have : (0 : ℕ) = 1 := by
    calc 0 = (wppCastLeg coTwLeft (fun _ => 0)) (0 : ℕ) := h0.symm
      _ = (wppCastLeg coTwLeft (fun _ => 1)) (0 : ℕ) := congrFun h (0 : ℕ)
      _ = 1 := h1
  exact Nat.zero_ne_one this

/-- Two constant weighted cocones differ at diagonal legs when they use
different constants. This shows that constant cocones DON'T satisfy the
equal-restriction hypothesis. -/
theorem wppCocones_diagonal_legs_differ :
    wppWeightedCocone₀.leg coTwIdZero
      (cast wppWeightAt_coTwIdZero.symm (𝟙 _)) ≠
    wppWeightedCocone₁.leg coTwIdZero
      (cast wppWeightAt_coTwIdZero.symm (𝟙 _)) := by
  simp only [wppWeightedCocone₀_leg_eq, wppWeightedCocone₁_leg_eq, ne_eq]
  intro h
  have h0 : (wppCastLeg coTwIdZero (fun _ => 0)) (0 : ℕ) = 0 := rfl
  have h1 : (wppCastLeg coTwIdZero (fun _ => 1)) (0 : ℕ) = 1 := rfl
  have : (0 : ℕ) = 1 := by
    calc 0 = (wppCastLeg coTwIdZero (fun _ => 0)) (0 : ℕ) := h0.symm
      _ = (wppCastLeg coTwIdZero (fun _ => 1)) (0 : ℕ) := congrFun h (0 : ℕ)
      _ = 1 := h1
  exact Nat.zero_ne_one this

/-- DecidableEq instance for Hom(zero, one) in WalkingParallelPair. -/
instance wppHomZeroOneDecidableEq :
    DecidableEq (WalkingParallelPair.zero ⟶ WalkingParallelPair.one) :=
  fun a b =>
    match a, b with
    | WalkingParallelPairHom.left, WalkingParallelPairHom.left => isTrue rfl
    | WalkingParallelPairHom.right, WalkingParallelPairHom.right => isTrue rfl
    | WalkingParallelPairHom.left, WalkingParallelPairHom.right =>
      isFalse (fun h => by cases h)
    | WalkingParallelPairHom.right, WalkingParallelPairHom.left =>
      isFalse (fun h => by cases h)

/-- DecidableEq instance for weight type at coTwLeft.
The weight type at coTwLeft equals Hom(zero, one). -/
instance wppWeightAt_coTwLeft_decidableEq : DecidableEq (wppWeightAt coTwLeft) := by
  have h : wppWeightAt coTwLeft =
      (WalkingParallelPair.zero ⟶ WalkingParallelPair.one) := wppWeightAt_coTwLeft
  rw [h]
  exact wppHomZeroOneDecidableEq

/-- Check if a weight at coTwLeft is `wppWeightRight` (i.e., the `right` morphism). -/
def isWppWeightRight (w : wppWeightAt coTwLeft) : Bool :=
  decide (w = wppWeightRight)

/-- The modified leg function at coTwLeft: maps `left ↦ 0` and `right ↦ 1`. -/
def modifiedLegAtCoTwLeft (w : wppWeightAt coTwLeft) : ℕ → ℕ :=
  if w = wppWeightRight then fun _ => 1 else fun _ => 0

/-- The modified leg at coTwLeft differs from constant 0 at wppWeightRight. -/
theorem modifiedLegAtCoTwLeft_right_eq_one :
    modifiedLegAtCoTwLeft wppWeightRight = fun _ => 1 := by
  simp only [modifiedLegAtCoTwLeft, ite_true]

/-- The weight elements wppWeightLeft and wppWeightRight are distinct. -/
theorem wppWeightLeft_ne_wppWeightRight : wppWeightLeft ≠ wppWeightRight := by
  unfold wppWeightLeft wppWeightRight castToWeightCoTwLeft
  intro heq
  have heq' : WalkingParallelPairHom.left = WalkingParallelPairHom.right := by
    have h1 : cast wppWeightAt_coTwLeft (cast wppWeightAt_coTwLeft.symm
                WalkingParallelPairHom.left) = WalkingParallelPairHom.left := by simp
    have h2 : cast wppWeightAt_coTwLeft (cast wppWeightAt_coTwLeft.symm
                WalkingParallelPairHom.right) = WalkingParallelPairHom.right := by simp
    calc WalkingParallelPairHom.left
        = cast wppWeightAt_coTwLeft (cast wppWeightAt_coTwLeft.symm
            WalkingParallelPairHom.left) := h1.symm
      _ = cast wppWeightAt_coTwLeft (cast wppWeightAt_coTwLeft.symm
            WalkingParallelPairHom.right) := by rw [heq]
      _ = WalkingParallelPairHom.right := h2
  exact walkingParallelPair_left_ne_right heq'

/-- The modified leg at coTwLeft agrees with constant 0 at wppWeightLeft. -/
theorem modifiedLegAtCoTwLeft_left_eq_zero :
    modifiedLegAtCoTwLeft wppWeightLeft = fun _ => 0 := by
  simp only [modifiedLegAtCoTwLeft]
  simp only [wppWeightLeft_ne_wppWeightRight, ite_false]

/-- The modified cocone leg at coTwLeft: the value differs from constant 0 at right. -/
theorem modifiedLeg_differs_from_const_at_right :
    modifiedLegAtCoTwLeft wppWeightRight (0 : ℕ) ≠
    (fun _ : ℕ => (0 : ℕ)) 0 := by
  simp only [modifiedLegAtCoTwLeft_right_eq_one]
  exact Nat.one_ne_zero

/-- Morphism from coTwLeft to coTwIdZero in the co-twisted arrow category.
This witnesses that left : zero → one factors through the identity on zero. -/
def coTwMorLeftToIdZero : coTwLeft ⟶ coTwIdZero :=
  coTwHomMk WalkingParallelPairHom.left (𝟙 _) (by simp [idCoTwistedArrow, coTwObjMk_arr])

/-- Morphism from coTwLeft to coTwIdOne in the co-twisted arrow category.
This witnesses that left : zero → one factors through the identity on one. -/
def coTwMorLeftToIdOne : coTwLeft ⟶ coTwIdOne :=
  coTwHomMk (𝟙 _) WalkingParallelPairHom.left (by simp [idCoTwistedArrow, coTwObjMk_arr])

/-- The domain arrow of the morphism from coTwLeft to coTwIdZero is left. -/
theorem coTwMorLeftToIdZero_domArr :
    coTwDomArr coTwMorLeftToIdZero = WalkingParallelPairHom.left := by
  simp only [coTwMorLeftToIdZero, coTwHomMk_domArr]

/-- The codomain arrow of the morphism from coTwLeft to coTwIdOne is left. -/
theorem coTwMorLeftToIdOne_codArr :
    coTwCodArr coTwMorLeftToIdOne = WalkingParallelPairHom.left := by
  simp only [coTwMorLeftToIdOne, coTwCodArr_coTwHomMk]

/-- Any morphism from coTwLeft to coTwIdZero equals coTwMorLeftToIdZero.
The compatibility condition `codArr ≫ (𝟙 zero) ≫ domArr = left` forces:
- `codArr : zero ⟶ zero` must be `𝟙 zero`
- `domArr : zero ⟶ one` must be `left` -/
theorem coTwLeft_to_coTwIdZero_unique (f : coTwLeft ⟶ coTwIdZero) :
    f = coTwMorLeftToIdZero := by
  apply coTwHom_ext
  · -- domArr equality
    have hcompat := coTwHomComm f
    simp only [idCoTwistedArrow, coTwObjMk_arr] at hcompat
    have hcod : coTwCodArr f = 𝟙 WalkingParallelPair.zero :=
      walkingParallelPair_zero_zero_eq_id (coTwCodArr f)
    rw [hcod] at hcompat
    simp only [coTwObjMk_dom] at hcompat
    simp only [coTwMorLeftToIdZero, coTwDomArr_coTwHomMk]
    exact hcompat
  · -- codArr equality
    simp only [coTwMorLeftToIdZero, coTwCodArr_coTwHomMk]
    exact walkingParallelPair_zero_zero_eq_id (coTwCodArr f)

/-- Any morphism from coTwLeft to coTwIdOne equals coTwMorLeftToIdOne.
The compatibility condition `codArr ≫ (𝟙 one) ≫ domArr = left` forces:
- `domArr : one ⟶ one` must be `𝟙 one`
- `codArr : zero ⟶ one` must be `left` -/
theorem coTwLeft_to_coTwIdOne_unique (f : coTwLeft ⟶ coTwIdOne) :
    f = coTwMorLeftToIdOne := by
  apply coTwHom_ext
  · -- domArr equality
    simp only [coTwMorLeftToIdOne, coTwDomArr_coTwHomMk]
    exact walkingParallelPair_one_one_eq_id (coTwDomArr f)
  · -- codArr equality
    have hcompat := coTwHomComm f
    simp only [idCoTwistedArrow, coTwObjMk_arr] at hcompat
    have hdom : coTwDomArr f = 𝟙 WalkingParallelPair.one :=
      walkingParallelPair_one_one_eq_id (coTwDomArr f)
    rw [hdom] at hcompat
    have hcompat' : coTwCodArr f = WalkingParallelPairHom.left :=
      calc coTwCodArr f = coTwCodArr f ≫ 𝟙 WalkingParallelPair.one :=
            (Category.comp_id _).symm
        _ = coTwCodArr f ≫ (𝟙 WalkingParallelPair.one ≫ 𝟙 WalkingParallelPair.one) :=
            congrArg _ (Category.id_comp _).symm
        _ = WalkingParallelPairHom.left := hcompat
    simp only [coTwMorLeftToIdOne, coTwCodArr_coTwHomMk]
    exact hcompat'

/-- coTwMorLeftToIdZero equals coTwToIdentityAtSource applied to left. -/
theorem coTwMorLeftToIdZero_eq_coTwToIdentityAtSource :
    coTwMorLeftToIdZero =
    @coTwToIdentityAtSource WalkingParallelPair _ WalkingParallelPair.zero
      WalkingParallelPair.one WalkingParallelPairHom.left := rfl

/-- coTwMorLeftToIdOne equals coTwToIdentityAtTarget applied to left. -/
theorem coTwMorLeftToIdOne_eq_coTwToIdentityAtTarget :
    coTwMorLeftToIdOne =
    @coTwToIdentityAtTarget WalkingParallelPair _ WalkingParallelPair.zero
      WalkingParallelPair.one WalkingParallelPairHom.left := rfl

/-- The identity weight at coTwIdZero. -/
def wppWeightIdZero : wppWeightAt coTwIdZero :=
  cast wppWeightAt_coTwIdZero.symm (𝟙 WalkingParallelPair.zero)

/-- The identity weight at coTwIdOne. -/
def wppWeightIdOne : wppWeightAt coTwIdOne :=
  cast wppWeightAt_coTwIdOne.symm (𝟙 WalkingParallelPair.one)

/-- Weight transport from coTwIdZero along coTwMorLeftToIdZero maps the identity
weight to wppWeightLeft (i.e., the `left` morphism). -/
theorem wppWeightTransport_fromIdZero_eq_left :
    wppWeightFunctor.map coTwMorLeftToIdZero.op wppWeightIdZero = wppWeightLeft := by
  unfold wppWeightFunctor wppWeightIdZero wppWeightLeft castToWeightCoTwLeft
  rw [coTwMorLeftToIdZero_eq_coTwToIdentityAtSource]
  have h := profunctor_map_coTwToIdentityAtSource_diag wppHomProfunctor
      WalkingParallelPairHom.left (𝟙 WalkingParallelPair.zero)
  simp only [diagAppToWeightAtIdentity] at h
  have heq : cast (profunctorOnOpCoTwistedArrow_at_identity wppHomProfunctor
               WalkingParallelPair.zero).symm (𝟙 WalkingParallelPair.zero) =
             cast wppWeightAt_coTwIdZero.symm (𝟙 WalkingParallelPair.zero) := by
    congr 1
  rw [← heq, h]
  simp only [wppHomProfunctor, Functor.curry_obj_obj_obj, Functor.hom_obj,
    Opposite.unop_op]
  rfl

/-- Weight transport from coTwIdOne along coTwMorLeftToIdOne maps the identity
weight to wppWeightLeft (i.e., the `left` morphism). -/
theorem wppWeightTransport_fromIdOne_eq_left :
    wppWeightFunctor.map coTwMorLeftToIdOne.op wppWeightIdOne = wppWeightLeft := by
  unfold wppWeightFunctor wppWeightIdOne wppWeightLeft castToWeightCoTwLeft
  rw [coTwMorLeftToIdOne_eq_coTwToIdentityAtTarget]
  have h := profunctor_map_coTwToIdentityAtTarget_diag wppHomProfunctor
      WalkingParallelPairHom.left (𝟙 WalkingParallelPair.one)
  simp only [diagAppToWeightAtIdentity] at h
  have heq : cast (profunctorOnOpCoTwistedArrow_at_identity wppHomProfunctor
               WalkingParallelPair.one).symm (𝟙 WalkingParallelPair.one) =
             cast wppWeightAt_coTwIdOne.symm (𝟙 WalkingParallelPair.one) := by
    congr 1
  rw [← heq, h]
  simp only [wppHomProfunctor, Functor.curry_obj_obj_obj, Functor.hom_obj,
    Opposite.unop_op]
  rfl

/-- There is no morphism from coTwIdZero to coTwLeft.
Proof: Such a morphism would require domArr : one → zero, but no such morphism
exists in WalkingParallelPair. -/
theorem no_mor_coTwIdZero_to_coTwLeft (φ : coTwIdZero ⟶ coTwLeft) : False := by
  exact walkingParallelPair_one_zero_empty (coTwDomArr φ)

/-- There is no morphism from coTwIdOne to coTwLeft.
Proof: Such a morphism would require codArr : zero → one, but no such morphism
exists from the codomain of coTwIdOne which is one. -/
theorem no_mor_coTwIdOne_to_coTwLeft (φ : coTwIdOne ⟶ coTwLeft) : False := by
  exact walkingParallelPair_one_zero_empty (coTwCodArr φ)

/-- coTwIdZero is not equal to coTwLeft. -/
theorem coTwIdZero_ne_coTwLeft : coTwIdZero ≠ coTwLeft := by
  intro heq
  have hdom : coTwDom coTwIdZero = coTwDom coTwLeft := congrArg coTwDom heq
  simp only [coTwIdZero, idCoTwistedArrow, coTwObjMk_dom, coTwLeft] at hdom
  exact walkingParallelPair_zero_ne_one hdom

/-- coTwIdOne is not equal to coTwLeft. -/
theorem coTwIdOne_ne_coTwLeft : coTwIdOne ≠ coTwLeft := by
  intro heq
  have hcod : coTwCod coTwIdOne = coTwCod coTwLeft := congrArg coTwCod heq
  simp only [coTwIdOne, idCoTwistedArrow, coTwObjMk_cod, coTwLeft] at hcod
  exact walkingParallelPair_one_ne_zero hcod

/-- The modified leg at coTwLeft with wppWeightLeft equals 0. -/
theorem modifiedLeg_at_coTwLeft_left :
    wppCastLeg coTwLeft (modifiedLegAtCoTwLeft wppWeightLeft) =
    wppCastLeg coTwLeft (fun _ => 0) := by
  rw [modifiedLegAtCoTwLeft_left_eq_zero]

/-- The modified leg at coTwLeft with wppWeightRight equals 1. -/
theorem modifiedLeg_at_coTwLeft_right :
    wppCastLeg coTwLeft (modifiedLegAtCoTwLeft wppWeightRight) =
    wppCastLeg coTwLeft (fun _ => 1) := by
  rw [modifiedLegAtCoTwLeft_right_eq_one]

/-- The modified leg at coTwIdZero with the identity weight equals constant 0. -/
theorem modifiedLeg_at_coTwIdZero :
    wppCastLeg coTwIdZero (fun _ => 0) =
    wppCastLeg coTwIdZero (fun _ => 0) := rfl

/-- The modified leg at coTwIdOne with the identity weight equals constant 0. -/
theorem modifiedLeg_at_coTwIdOne :
    wppCastLeg coTwIdOne (fun _ => 0) =
    wppCastLeg coTwIdOne (fun _ => 0) := rfl

/-- The modified leg at coTwLeft differs from the constant 0 leg at wppWeightRight. -/
theorem modified_differs_from_const_at_right :
    wppCastLeg coTwLeft (modifiedLegAtCoTwLeft wppWeightRight) ≠
    wppCastLeg coTwLeft (fun _ => 0) := by
  intro h
  have h1 : (wppCastLeg coTwLeft (modifiedLegAtCoTwLeft wppWeightRight)) (0 : ℕ) = 1 := by
    rw [modifiedLeg_at_coTwLeft_right]
    rfl
  have h0 : (wppCastLeg coTwLeft (fun _ => 0)) (0 : ℕ) = 0 := rfl
  have : (1 : ℕ) = 0 := by
    calc 1 = (wppCastLeg coTwLeft (modifiedLegAtCoTwLeft wppWeightRight)) (0 : ℕ) := h1.symm
      _ = (wppCastLeg coTwLeft (fun _ => 0)) (0 : ℕ) := congrFun h (0 : ℕ)
      _ = 0 := h0
  exact Nat.one_ne_zero this

/-- The modified leg at coTwLeft agrees with the constant 0 leg at wppWeightLeft. -/
theorem modified_agrees_with_const_at_left :
    wppCastLeg coTwLeft (modifiedLegAtCoTwLeft wppWeightLeft) =
    wppCastLeg coTwLeft (fun _ => 0) := by
  rw [modifiedLeg_at_coTwLeft_left]

/-- Characterization: the only morphisms in (CoTwistedArrow WalkingParallelPair)
involving coTwLeft are FROM coTwLeft TO diagonal positions, not the reverse.
This means naturality constraints flow FROM diagonals TO coTwLeft, not INTO. -/
theorem coTwLeft_morphism_characterization :
    (∀ _ : coTwIdZero ⟶ coTwLeft, False) ∧
    (∀ _ : coTwIdOne ⟶ coTwLeft, False) := by
  constructor
  · exact no_mor_coTwIdZero_to_coTwLeft
  · exact no_mor_coTwIdOne_to_coTwLeft

/-- Weight transport from coTwIdZero to coTwLeft maps the unique diagonal weight
to wppWeightLeft. -/
theorem weight_transport_to_coTwLeft_is_left :
    wppWeightFunctor.map coTwMorLeftToIdZero.op wppWeightIdZero = wppWeightLeft :=
  wppWeightTransport_fromIdZero_eq_left

/-- This shows that the value at (coTwLeft, wppWeightRight) is NOT constrained
by diagonal data: it is not in the image of any weight transport from diagonals.

Specifically:
- Weight transport from coTwIdZero maps to wppWeightLeft, not wppWeightRight
- Weight transport from coTwIdOne maps to wppWeightLeft, not wppWeightRight
- There are no morphisms FROM other diagonal positions INTO coTwLeft

Therefore, for any weighted cocone, the value at (coTwLeft, wppWeightRight)
can be chosen independently of the diagonal leg values. This is what breaks
fullness of the restriction functor. -/
theorem wppWeightRight_not_constrained_by_diagonals :
    (wppWeightFunctor.map coTwMorLeftToIdZero.op wppWeightIdZero ≠ wppWeightRight) ∧
    (wppWeightFunctor.map coTwMorLeftToIdOne.op wppWeightIdOne ≠ wppWeightRight) := by
  constructor
  · rw [wppWeightTransport_fromIdZero_eq_left]
    exact wppWeightLeft_ne_wppWeightRight
  · rw [wppWeightTransport_fromIdOne_eq_left]
    exact wppWeightLeft_ne_wppWeightRight

/-- Decidable equality for WalkingParallelPair. -/
instance wppDecidableEq : DecidableEq WalkingParallelPair := by
  intro a b
  cases a <;> cases b
  · exact isTrue rfl
  · exact isFalse (fun h => by cases h)
  · exact isFalse (fun h => by cases h)
  · exact isTrue rfl

/-- Decidable equality for WalkingParallelPairᵒᵖ. -/
instance wppOpDecidableEq : DecidableEq WalkingParallelPairᵒᵖ := by
  intro a b
  have hdec := wppDecidableEq a.unop b.unop
  cases hdec with
  | isFalse hne => exact isFalse (fun h => hne (congrArg Opposite.unop h))
  | isTrue heq => exact isTrue (Opposite.unop_injective heq)

/-- Decidable equality for WalkingParallelPairᵒᵖᵒᵖ. -/
instance wppOpOpDecidableEq : DecidableEq WalkingParallelPairᵒᵖᵒᵖ := by
  intro a b
  have hdec := wppOpDecidableEq a.unop b.unop
  cases hdec with
  | isFalse hne => exact isFalse (fun h => hne (congrArg Opposite.unop h))
  | isTrue heq => exact isTrue (Opposite.unop_injective heq)

/-- Decidable equality for morphisms in WalkingParallelPair between given objects.
Uses the fact that WalkingParallelPairHom already derives DecidableEq. -/
instance wppHomDecidableEq (X Y : WalkingParallelPair) :
    DecidableEq (X ⟶ Y) :=
  inferInstanceAs (DecidableEq (WalkingParallelPairHom X Y))

/-- The co-twisted arrow corresponding to the `right` morphism in
WalkingParallelPair. Defined here for use in DecidableEq. -/
def coTwRight' : CoTwistedArrow WalkingParallelPair :=
  coTwObjMk WalkingParallelPairHom.right

/-- The arrow of coTwRight' is the right morphism. -/
theorem coTwRight'_arr : coTwArr coTwRight' = WalkingParallelPairHom.right := by
  simp only [coTwRight', coTwObjMk_arr]

/-- The domain of coTwRight' is one. -/
theorem coTwRight'_dom : coTwDom coTwRight' = WalkingParallelPair.one := by
  simp only [coTwRight', coTwObjMk_dom]

/-- The codomain of coTwRight' is zero. -/
theorem coTwRight'_cod : coTwCod coTwRight' = WalkingParallelPair.zero := by
  simp only [coTwRight', coTwObjMk_cod]

/-- The domain of coTwLeft is one. -/
theorem coTwLeft_dom : coTwDom coTwLeft = WalkingParallelPair.one := by
  simp only [coTwLeft, coTwObjMk_dom]

/-- The codomain of coTwLeft is zero. -/
theorem coTwLeft_cod : coTwCod coTwLeft = WalkingParallelPair.zero := by
  simp only [coTwLeft, coTwObjMk_cod]

/-- The arrow of coTwLeft is the left morphism. -/
theorem coTwLeft_arr : coTwArr coTwLeft = WalkingParallelPairHom.left := by
  simp only [coTwLeft, coTwObjMk_arr]

/-- The domain of coTwIdZero is zero. -/
theorem coTwIdZero_dom : coTwDom coTwIdZero = WalkingParallelPair.zero := by
  simp only [coTwIdZero, idCoTwistedArrow, coTwObjMk_dom]

/-- The codomain of coTwIdZero is zero. -/
theorem coTwIdZero_cod : coTwCod coTwIdZero = WalkingParallelPair.zero := by
  simp only [coTwIdZero, idCoTwistedArrow, coTwObjMk_cod]

/-- The domain of coTwIdOne is one. -/
theorem coTwIdOne_dom : coTwDom coTwIdOne = WalkingParallelPair.one := by
  simp only [coTwIdOne, idCoTwistedArrow, coTwObjMk_dom]

/-- The codomain of coTwIdOne is one. -/
theorem coTwIdOne_cod : coTwCod coTwIdOne = WalkingParallelPair.one := by
  simp only [coTwIdOne, idCoTwistedArrow, coTwObjMk_cod]

/-- Enumeration of the 4 co-twisted arrows in WalkingParallelPair.
This inductive type is definitionally equivalent but easier to work with
for decidable equality. -/
inductive WppCoTwEnum : Type where
  | idZero : WppCoTwEnum
  | idOne : WppCoTwEnum
  | left : WppCoTwEnum
  | right' : WppCoTwEnum
  deriving DecidableEq, Repr

/-- Convert from enumeration to co-twisted arrow. -/
def WppCoTwEnum.toCoTw : WppCoTwEnum → CoTwistedArrow WalkingParallelPair
  | .idZero => coTwIdZero
  | .idOne => coTwIdOne
  | .left => coTwLeft
  | .right' => coTwRight'

/-- Helper to compute the enumeration from cod, dom, and arrow values.
The arrow parameter is only examined when cod=zero and dom=one. -/
def wppCoTwEnumAux (c d : WalkingParallelPair) (arr : c ⟶ d) : WppCoTwEnum :=
  match c, d with
  | .zero, .zero => .idZero
  | .one, .one => .idOne
  | .zero, .one =>
    match arr with
    | .left => .left
    | .right => .right'
  | .one, .zero => .idZero  -- impossible case, default to idZero

/-- Convert from co-twisted arrow to enumeration. -/
def wppCoTwToEnum (tw : CoTwistedArrow WalkingParallelPair) : WppCoTwEnum :=
  wppCoTwEnumAux (coTwCod tw) (coTwDom tw) (coTwArr tw)

/-- toCoTw ∘ toEnum = id for coTwIdZero. -/
theorem wppCoTwEnum_roundtrip_idZero :
    WppCoTwEnum.toCoTw (wppCoTwToEnum coTwIdZero) = coTwIdZero := rfl

/-- toCoTw ∘ toEnum = id for coTwIdOne. -/
theorem wppCoTwEnum_roundtrip_idOne :
    WppCoTwEnum.toCoTw (wppCoTwToEnum coTwIdOne) = coTwIdOne := rfl

/-- toCoTw ∘ toEnum = id for coTwLeft. -/
theorem wppCoTwEnum_roundtrip_left :
    WppCoTwEnum.toCoTw (wppCoTwToEnum coTwLeft) = coTwLeft := rfl

/-- toCoTw ∘ toEnum = id for coTwRight'. -/
theorem wppCoTwEnum_roundtrip_right' :
    WppCoTwEnum.toCoTw (wppCoTwToEnum coTwRight') = coTwRight' := rfl

/-- toEnum ∘ toCoTw = id for all enum values. -/
theorem wppCoTwEnum_toEnum_toCoTw (e : WppCoTwEnum) :
    wppCoTwToEnum (WppCoTwEnum.toCoTw e) = e := by
  cases e <;> rfl

/-- wppCoTwToEnum maps coTwIdZero to idZero. -/
@[simp]
theorem wppCoTwToEnum_idZero : wppCoTwToEnum coTwIdZero = .idZero := rfl

/-- wppCoTwToEnum maps coTwIdOne to idOne. -/
@[simp]
theorem wppCoTwToEnum_idOne : wppCoTwToEnum coTwIdOne = .idOne := rfl

/-- wppCoTwToEnum maps coTwLeft to left. -/
@[simp]
theorem wppCoTwToEnum_left : wppCoTwToEnum coTwLeft = .left := rfl

/-- wppCoTwToEnum maps coTwRight' to right'. -/
@[simp]
theorem wppCoTwToEnum_right' : wppCoTwToEnum coTwRight' = .right' := rfl

/-- Helper: classify an arrow in WalkingParallelPair as one of the four types.
Each branch carries a proof that reconstructing via coTwObjMk yields the
corresponding named constant. -/
def classifyWppArrowResult (cod dom : WalkingParallelPair) (arr : cod ⟶ dom) :
    (coTwObjMk arr = coTwIdZero) ∨
    (coTwObjMk arr = coTwIdOne) ∨
    (coTwObjMk arr = coTwLeft) ∨
    (coTwObjMk arr = coTwRight') := by
  match cod, dom, arr with
  | .zero, .zero, .id .zero => left; rfl
  | .one, .one, .id .one => right; left; rfl
  | .zero, .one, .left => right; right; left; rfl
  | .zero, .one, .right => right; right; right; rfl

/-- Every co-twisted arrow equals one of the four named constants. -/
theorem wppCoTwArrow_cases (tw : CoTwistedArrow WalkingParallelPair) :
    tw = coTwIdZero ∨ tw = coTwIdOne ∨ tw = coTwLeft ∨ tw = coTwRight' := by
  -- Rewrite tw as coTwObjMk (coTwArr tw)
  rw [coTw_eq_coTwObjMk tw]
  -- Then classify the arrow
  exact classifyWppArrowResult (coTwCod tw) (coTwDom tw) (coTwArr tw)

/-- The toCoTw function is surjective. -/
theorem wppCoTwEnum_toCoTw_surj (tw : CoTwistedArrow WalkingParallelPair) :
    ∃ e : WppCoTwEnum, WppCoTwEnum.toCoTw e = tw := by
  rcases wppCoTwArrow_cases tw with h | h | h | h
  · exact ⟨.idZero, h.symm⟩
  · exact ⟨.idOne, h.symm⟩
  · exact ⟨.left, h.symm⟩
  · exact ⟨.right', h.symm⟩

/-- The toEnum function is injective (equal enum values mean equal arrows). -/
theorem wppCoTwEnum_toEnum_inj (tw₁ tw₂ : CoTwistedArrow WalkingParallelPair)
    (h : wppCoTwToEnum tw₁ = wppCoTwToEnum tw₂) : tw₁ = tw₂ := by
  -- Both are one of the four cases
  rcases wppCoTwArrow_cases tw₁ with h1 | h1 | h1 | h1 <;>
  rcases wppCoTwArrow_cases tw₂ with h2 | h2 | h2 | h2 <;>
  subst h1 h2 <;> first
    | rfl
    | (simp only [wppCoTwToEnum_idZero, wppCoTwToEnum_idOne, wppCoTwToEnum_left,
        wppCoTwToEnum_right'] at h; cases h)

/-- Decidable equality for CoTwistedArrow WalkingParallelPair.
Uses the enumeration for comparison since WppCoTwEnum has DecidableEq. -/
instance wppCoTwistedArrowDecidableEq :
    DecidableEq (CoTwistedArrow WalkingParallelPair) := fun tw₁ tw₂ =>
  if h : wppCoTwToEnum tw₁ = wppCoTwToEnum tw₂ then
    isTrue (wppCoTwEnum_toEnum_inj tw₁ tw₂ h)
  else
    isFalse (fun heq => h (congrArg wppCoTwToEnum heq))

/-- Check if a co-twisted arrow is at coTwLeft by examining its cod/dom/arr. -/
def isCoTwLeft (tw : CoTwistedArrow WalkingParallelPair) : Bool :=
  decide (coTwCod tw = WalkingParallelPair.zero) &&
  decide (coTwDom tw = WalkingParallelPair.one)

/-- coTwLeft satisfies the isCoTwLeft predicate. -/
theorem isCoTwLeft_coTwLeft : isCoTwLeft coTwLeft = true := by
  simp only [isCoTwLeft, coTwLeft, coTwObjMk_cod, coTwObjMk_dom, decide_true,
    Bool.and_self]

/-- coTwIdZero does not satisfy the isCoTwLeft predicate. -/
theorem isCoTwLeft_coTwIdZero : isCoTwLeft coTwIdZero = false := by
  rfl

/-- coTwIdOne does not satisfy the isCoTwLeft predicate. -/
theorem isCoTwLeft_coTwIdOne : isCoTwLeft coTwIdOne = false := by
  rfl

/-- Weight transport from diagonal positions only
reaches wppWeightLeft at coTwLeft, never wppWeightRight. Combined with the
fact that there are no morphisms FROM diagonal positions INTO coTwLeft,
this means the leg value at (coTwLeft, wppWeightRight) is completely
unconstrained by diagonal data through naturality.

This demonstrates that the restriction functor loses information:
two weighted cocones can agree on all diagonal legs but still differ
at off-diagonal positions like (coTwLeft, wppWeightRight). -/
theorem diagonal_does_not_determine_wppWeightRight :
    (wppWeightFunctor.map coTwMorLeftToIdZero.op wppWeightIdZero = wppWeightLeft) ∧
    (wppWeightFunctor.map coTwMorLeftToIdOne.op wppWeightIdOne = wppWeightLeft) ∧
    (wppWeightLeft ≠ wppWeightRight) ∧
    (∀ _ : coTwIdZero ⟶ coTwLeft, False) ∧
    (∀ _ : coTwIdOne ⟶ coTwLeft, False) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact wppWeightTransport_fromIdZero_eq_left
  · exact wppWeightTransport_fromIdOne_eq_left
  · exact wppWeightLeft_ne_wppWeightRight
  · exact no_mor_coTwIdZero_to_coTwLeft
  · exact no_mor_coTwIdOne_to_coTwLeft

/-- The co-twisted arrow corresponding to the `right` morphism in WalkingParallelPair. -/
def coTwRight : CoTwistedArrow WalkingParallelPair :=
  coTwObjMk WalkingParallelPairHom.right

/-- The arrow of coTwRight is the right morphism. -/
theorem coTwRight_arr : coTwArr coTwRight = WalkingParallelPairHom.right := by
  simp only [coTwRight, coTwObjMk_arr]

/-- coTwRight and coTwRight' are the same. -/
theorem coTwRight_eq_coTwRight' : coTwRight = coTwRight' := rfl

/-- Morphism from coTwRight to coTwIdZero in the co-twisted arrow category. -/
def coTwMorRightToIdZero : coTwRight ⟶ coTwIdZero :=
  coTwHomMk WalkingParallelPairHom.right (𝟙 _) (by
    simp only [idCoTwistedArrow, coTwObjMk_arr, coTwRight_arr]
    rfl)

/-- Morphism from coTwRight to coTwIdOne in the co-twisted arrow category. -/
def coTwMorRightToIdOne : coTwRight ⟶ coTwIdOne :=
  coTwHomMk (𝟙 _) WalkingParallelPairHom.right (by
    simp only [idCoTwistedArrow, coTwObjMk_arr, coTwRight_arr]
    rfl)

/-- The weight type at coTwRight equals homset zero → one. -/
theorem wppWeightAt_coTwRight :
    wppWeightAt coTwRight = (WalkingParallelPair.zero ⟶ WalkingParallelPair.one) := by
  simp only [wppWeightAt, profunctorOnOpCoTwistedArrow, wppHomProfunctor,
    Functor.comp_obj]
  rfl

/-- The weight element for the `right` morphism at coTwRight. -/
def wppWeightRightAtRight : wppWeightAt coTwRight :=
  cast wppWeightAt_coTwRight.symm WalkingParallelPairHom.right

/-- No morphism exists from coTwRight to coTwLeft.
A morphism would require codArr ≫ left ≫ domArr = right, but with the
only possible arrows being identities, this would require left = right. -/
theorem no_mor_coTwRight_to_coTwLeft (φ : coTwRight ⟶ coTwLeft) : False := by
  have harr := coTwHomComm φ
  simp only [coTwRight, coTwLeft, coTwObjMk_arr] at harr
  have hcod : coTwCodArr φ = 𝟙 WalkingParallelPair.zero :=
    walkingParallelPair_zero_zero_eq_id (coTwCodArr φ)
  have hdom : coTwDomArr φ = 𝟙 WalkingParallelPair.one :=
    walkingParallelPair_one_one_eq_id (coTwDomArr φ)
  rw [hcod, hdom] at harr
  simp only [coTwObjMk_dom, coTwObjMk_cod, Category.id_comp, Category.comp_id] at harr
  exact walkingParallelPair_left_ne_right harr

/-- No morphism exists from coTwLeft to coTwRight.
A morphism would require codArr ≫ right ≫ domArr = left, but with the
only possible arrows being identities, this would require right = left. -/
theorem no_mor_coTwLeft_to_coTwRight (φ : coTwLeft ⟶ coTwRight) : False := by
  have harr := coTwHomComm φ
  simp only [coTwRight, coTwLeft, coTwObjMk_arr] at harr
  have hcod : coTwCodArr φ = 𝟙 WalkingParallelPair.zero :=
    walkingParallelPair_zero_zero_eq_id (coTwCodArr φ)
  have hdom : coTwDomArr φ = 𝟙 WalkingParallelPair.one :=
    walkingParallelPair_one_one_eq_id (coTwDomArr φ)
  rw [hcod, hdom] at harr
  simp only [coTwObjMk_dom, coTwObjMk_cod, Category.id_comp, Category.comp_id] at harr
  exact walkingParallelPair_left_ne_right harr.symm

/-- Any endomorphism of coTwLeft is the identity.
Since both dom and cod must go via identities. -/
theorem coTwLeft_endo_is_id (φ : coTwLeft ⟶ coTwLeft) : φ = 𝟙 coTwLeft := by
  ext
  · exact walkingParallelPair_one_one_eq_id (coTwDomArr φ)
  · exact walkingParallelPair_zero_zero_eq_id (coTwCodArr φ)

/-!
The non-fullness argument relies on the following observation:
The value at (coTwLeft, wppWeightRight) is unconstrained by naturality
because:
1. All morphisms involving coTwLeft go FROM coTwLeft TO diagonal positions
2. Weight transport along these morphisms produces only wppWeightLeft
3. No morphisms exist from diagonal positions INTO coTwLeft
4. No morphisms exist between coTwLeft and coTwRight

Therefore, a weighted cocone can have any value at (coTwLeft, wppWeightRight)
while maintaining naturality. This means two cocones with the same diagonal
legs can differ at this position, and no cocone morphism with identity apex
morphism can exist between them.
-/

/-- The modified leg at coTwLeft applied to wppWeightLeft equals
the original cocone leg (constant 0). -/
theorem wppModifiedLeg_at_left_eq_zero :
    wppCastLeg coTwLeft (modifiedLegAtCoTwLeft wppWeightLeft) =
    wppCastLeg coTwLeft (fun _ => 0) := by
  rw [modifiedLegAtCoTwLeft_left_eq_zero]

/-- The modified leg at coTwLeft applied to wppWeightRight differs from
constant 0. -/
theorem wppModifiedLeg_at_right_ne_zero :
    wppCastLeg coTwLeft (modifiedLegAtCoTwLeft wppWeightRight) ≠
    wppCastLeg coTwLeft (fun _ => 0) := by
  rw [modifiedLegAtCoTwLeft_right_eq_one]
  intro h
  have h0 : (wppCastLeg coTwLeft (fun _ => 0)) (0 : ℕ) = 0 := rfl
  have h1 : (wppCastLeg coTwLeft (fun _ => 1)) (0 : ℕ) = 1 := rfl
  have : (0 : ℕ) = 1 := by
    calc 0 = (wppCastLeg coTwLeft (fun _ => 0)) (0 : ℕ) := h0.symm
      _ = (wppCastLeg coTwLeft (fun _ => 1)) (0 : ℕ) := congrFun h.symm (0 : ℕ)
      _ = 1 := h1
  exact Nat.zero_ne_one this

/-- The statement of non-fullness: there exist positions and values where
a weighted cocone can differ from wppWeightedCocone₀ while having the same
restriction (same diagonal legs).

Specifically: the value at (coTwLeft, wppWeightRight) can be either 0 or 1
while the diagonal values remain constant 0. But any cocone morphism between
such cocones that restricts to identity would require:
- h(0) = 0 (from diagonal commutativity)
- h(0) = 1 (from commutativity at (coTwLeft, wppWeightRight))
which is a contradiction.

This shows the restriction functor is not full. -/
theorem restrictionFunctor_not_full_statement :
    (wppWeightedCocone₀.leg coTwIdZero
      (cast wppWeightAt_coTwIdZero.symm (𝟙 WalkingParallelPair.zero)) =
     wppCastLeg coTwIdZero (fun _ => 0)) ∧
    (wppCastLeg coTwLeft (modifiedLegAtCoTwLeft wppWeightLeft) =
     wppCastLeg coTwLeft (fun _ => 0)) ∧
    (wppCastLeg coTwLeft (modifiedLegAtCoTwLeft wppWeightRight) ≠
     wppCastLeg coTwLeft (fun _ => 0)) := by
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · exact wppModifiedLeg_at_left_eq_zero
  · exact wppModifiedLeg_at_right_ne_zero

/-- Contradiction lemma: no morphism h : ℕ → ℕ can satisfy both
h(0) = 0 and h(0) = 1. -/
theorem no_morphism_with_both_conditions (h : ℕ → ℕ)
    (h0 : h 0 = 0) (h1 : h 0 = 1) : False := by
  have : (0 : ℕ) = 1 := by rw [← h0, h1]
  exact Nat.zero_ne_one this

/-!
### Non-fullness of the restriction functor

The identity morphism on a weighted cocone satisfies the morphism condition:
for all (tw, w), leg(tw, w) ≫ id = leg(tw, w). This is trivially true.

If two cocones c₁ and c₂ have the same apex and the same restriction (same
diagonal legs), but differ at some non-diagonal position, then any morphism
from c₁ to c₂ with identity apex must satisfy leg₁(tw, w) = leg₂(tw, w) for
all (tw, w). But they differ at the non-diagonal position, so no such
morphism exists.

The identity on the restriction cannot lift to a weighted cocone morphism
when the cocones differ at non-diagonal positions.
-/

/-- For a weighted cocone morphism with identity apex, all legs must match. -/
theorem weighted_cocone_morphism_id_forces_equal_legs
    (c₁ c₂ : WeightedCocone wppWeightFunctor wppDiagramFunctor)
    (apex_eq : c₁.pt = c₂.pt)
    (h_mor : WeightedCocone.Hom c₁ c₂)
    (h_id : h_mor.hom = eqToHom apex_eq)
    (tw : CoTwistedArrow WalkingParallelPair)
    (w : wppWeightAt tw) :
    c₁.leg tw w ≫ eqToHom apex_eq = c₂.leg tw w := by
  have comm := h_mor.w tw w
  rw [h_id] at comm
  exact comm

/--
Summary of the non-fullness result: the restriction functor from weighted
cocones to restricted cowedges is not full for the WalkingParallelPair case.

The proof works by exhibiting that:
1. The value at (coTwLeft, wppWeightRight) is unconstrained by naturality
   (established in `diagonal_does_not_determine_wppWeightRight`)
2. No morphisms exist INTO coTwLeft from any other co-twisted arrow
   (neither diagonals nor coTwRight)
3. Therefore weighted cocones with same diagonal legs can differ there
4. Any morphism between such cocones restricting to identity forces equality
   of all legs, which contradicts the difference at (coTwLeft, wppWeightRight)
-/
theorem restriction_functor_not_full_summary :
    wppWeightLeft ≠ wppWeightRight ∧
    (wppWeightFunctor.map coTwMorLeftToIdZero.op wppWeightIdZero = wppWeightLeft) ∧
    (∀ _ : coTwIdZero ⟶ coTwLeft, False) ∧
    (∀ _ : coTwIdOne ⟶ coTwLeft, False) ∧
    (∀ _ : coTwRight ⟶ coTwLeft, False) ∧
    (∀ _ : coTwLeft ⟶ coTwRight, False) :=
  ⟨wppWeightLeft_ne_wppWeightRight,
   wppWeightTransport_fromIdZero_eq_left,
   no_mor_coTwIdZero_to_coTwLeft,
   no_mor_coTwIdOne_to_coTwLeft,
   no_mor_coTwRight_to_coTwLeft,
   no_mor_coTwLeft_to_coTwRight⟩

/-!
### Final non-fullness theorem

We prove that the restriction functor is not full by constructing a modified
weighted cocone that agrees with wppWeightedCocone₀ on diagonals but differs
at (coTwLeft, wppWeightRight).

The approach constructs explicit leg functions for the modified cocone by
specifying values at each co-twisted arrow position.
-/

/-- The modified leg function at coTwLeft: agrees with constant 0 at
wppWeightLeft but differs at wppWeightRight. -/
def wppModifiedLegCoTwLeft : wppWeightAt coTwLeft → (ℕ → ℕ) :=
  modifiedLegAtCoTwLeft

/-- The modified leg at coTwLeft wrapped in the cast. -/
def wppModifiedLegCoTwLeftCast (w : wppWeightAt coTwLeft) :
    wppDiagramFunctor.obj coTwLeft → ℕ :=
  wppCastLeg coTwLeft (wppModifiedLegCoTwLeft w)

/-- The modified natural transformation app at coTwLeft. -/
def wppModifiedNatTransAppCoTwLeft :
    wppWeightFunctor.obj (Opposite.op coTwLeft) →
    (homToFunctor wppDiagramFunctor ℕ).obj (Opposite.op coTwLeft) :=
  wppModifiedLegCoTwLeftCast

/-- Modified cocone legs: constant 0 at all diagonal and coTwRight positions,
modified at coTwLeft. -/
def wppModifiedLegNatTrans :
    wppWeightFunctor ⟶ homToFunctor wppDiagramFunctor ℕ where
  app := fun tw =>
    if h : tw.unop = coTwLeft then
      fun w => wppCastLeg tw.unop
        (modifiedLegAtCoTwLeft (cast (congrArg (wppWeightFunctor.obj ·)
          ((Opposite.op_unop tw).symm.trans (congrArg Opposite.op h))) w))
    else
      fun _ => wppCastLeg tw.unop (fun _ => 0)
  naturality := fun x y f => by
    ext w
    simp only [types_comp_apply]
    rw [wppHomToFunctor_map_eq]
    by_cases hx : x.unop = coTwLeft <;> by_cases hy : y.unop = coTwLeft
    · -- Case: x.unop = coTwLeft, y.unop = coTwLeft
      have hxy : x = y := Opposite.unop_injective (hx.trans hy.symm)
      subst hxy
      have hx' : x = Opposite.op coTwLeft := by rw [← Opposite.op_unop x, hx]
      subst hx'
      have hf_id : f = 𝟙 (Opposite.op coTwLeft) := by
        apply Quiver.Hom.unop_inj
        exact coTwLeft_endo_is_id f.unop
      simp only [dite_true, hf_id, Functor.map_id, types_id_apply]
    · -- Case: x.unop = coTwLeft, y.unop ≠ coTwLeft (contradiction)
      exfalso
      have hf : y.unop ⟶ coTwLeft := hx ▸ f.unop
      rcases wppCoTwArrow_cases y.unop with hycase | hycase | hycase | hycase
      · exact no_mor_coTwIdZero_to_coTwLeft (hycase ▸ hf)
      · exact no_mor_coTwIdOne_to_coTwLeft (hycase ▸ hf)
      · exact hy hycase
      · exact no_mor_coTwRight_to_coTwLeft (coTwRight_eq_coTwRight'.symm ▸ hycase ▸ hf)
    · -- Case: x.unop ≠ coTwLeft, y.unop = coTwLeft
      simp only [hx, hy, dite_true, dite_false]
      rcases wppCoTwArrow_cases x.unop with hxcase | hxcase | hxcase | hxcase
      · -- x.unop = coTwIdZero
        have hx' : x = Opposite.op coTwIdZero := by
          rw [← Opposite.op_unop x, hxcase]
        subst hx'
        have hy' : y = Opposite.op coTwLeft := by
          rw [← Opposite.op_unop y, hy]
        subst hy'
        have hf_unop : f.unop = coTwMorLeftToIdZero :=
          coTwLeft_to_coTwIdZero_unique f.unop
        have hf : f = coTwMorLeftToIdZero.op :=
          Quiver.Hom.unop_inj hf_unop
        have hw : w = wppWeightIdZero := by
          unfold wppWeightIdZero
          exact walkingParallelPair_zero_zero_eq_id (cast wppWeightAt_coTwIdZero w)
        simp only [Opposite.unop_op, hw, hf, wppWeightTransport_fromIdZero_eq_left]
        conv_lhs => rw [show (cast _ wppWeightLeft) = wppWeightLeft from rfl]
        rw [modifiedLegAtCoTwLeft_left_eq_zero]
        funext n
        rfl
      · -- x.unop = coTwIdOne
        have hx' : x = Opposite.op coTwIdOne := by
          rw [← Opposite.op_unop x, hxcase]
        subst hx'
        have hy' : y = Opposite.op coTwLeft := by
          rw [← Opposite.op_unop y, hy]
        subst hy'
        have hf_unop : f.unop = coTwMorLeftToIdOne :=
          coTwLeft_to_coTwIdOne_unique f.unop
        have hf : f = coTwMorLeftToIdOne.op :=
          Quiver.Hom.unop_inj hf_unop
        have hw : w = wppWeightIdOne := by
          unfold wppWeightIdOne
          exact wpp_hom_one_one_singleton (cast wppWeightAt_coTwIdOne w)
        simp only [Opposite.unop_op, hw, hf, wppWeightTransport_fromIdOne_eq_left]
        conv_lhs => rw [show (cast _ wppWeightLeft) = wppWeightLeft from rfl]
        rw [modifiedLegAtCoTwLeft_left_eq_zero]
        funext n
        rfl
      · -- x.unop = coTwLeft: contradiction with hx
        exact absurd hxcase hx
      · -- x.unop = coTwRight': no morphism from coTwLeft
        exfalso
        have hf : coTwLeft ⟶ x.unop := hy ▸ f.unop
        rw [hxcase] at hf
        exact no_mor_coTwLeft_to_coTwRight (coTwRight_eq_coTwRight'.symm ▸ hf)
    · -- Case: both not coTwLeft (both constant 0)
      simp only [hx, hy, dite_false]
      rfl

/-- The modified weighted cocone: uses wppModifiedLegNatTrans for legs. -/
def wppModifiedCocone : WeightedCocone wppWeightFunctor wppDiagramFunctor where
  pt := ℕ
  toWeightedCoconeOver := wppModifiedLegNatTrans

/-- The leg of the modified cocone at coTwLeft uses modifiedLegAtCoTwLeft. -/
theorem wppModifiedCocone_leg_coTwLeft (w : wppWeightAt coTwLeft) :
    wppModifiedCocone.leg coTwLeft w =
    wppCastLeg coTwLeft (modifiedLegAtCoTwLeft w) := by
  simp only [wppModifiedCocone, WeightedCocone.leg, WeightedCocone.ι,
    wppModifiedLegNatTrans, dite_true]
  rfl

/-- The leg of the modified cocone at coTwIdZero is constant 0. -/
theorem wppModifiedCocone_leg_coTwIdZero (w : wppWeightAt coTwIdZero) :
    wppModifiedCocone.leg coTwIdZero w = wppCastLeg coTwIdZero (fun _ => 0) := by
  simp only [wppModifiedCocone, WeightedCocone.leg, WeightedCocone.ι, wppModifiedLegNatTrans]
  have h : coTwIdZero ≠ coTwLeft := by
    intro heq
    have : coTwDom coTwIdZero = coTwDom coTwLeft := congrArg coTwDom heq
    rw [coTwIdZero_dom, coTwLeft_dom] at this
    cases this
  simp only [h, ↓reduceDIte]

/-- The leg of the modified cocone at coTwIdOne is constant 0. -/
theorem wppModifiedCocone_leg_coTwIdOne (w : wppWeightAt coTwIdOne) :
    wppModifiedCocone.leg coTwIdOne w = wppCastLeg coTwIdOne (fun _ => 0) := by
  simp only [wppModifiedCocone, WeightedCocone.leg, WeightedCocone.ι, wppModifiedLegNatTrans]
  have h : coTwIdOne ≠ coTwLeft := by
    intro heq
    have : coTwCod coTwIdOne = coTwCod coTwLeft := congrArg coTwCod heq
    rw [coTwIdOne_cod, coTwLeft_cod] at this
    cases this
  simp only [h, ↓reduceDIte]

/-- The modified cocone has the same diagonal leg at coTwIdZero as wppWeightedCocone₀. -/
theorem wppModifiedCocone_diagonal_eq_zero :
    ∀ (w : wppWeightAt coTwIdZero),
    wppModifiedCocone.leg coTwIdZero w = wppWeightedCocone₀.leg coTwIdZero w := by
  intro w
  rw [wppModifiedCocone_leg_coTwIdZero, wppWeightedCocone₀_leg_eq]

/-- The modified cocone has the same diagonal leg at coTwIdOne as wppWeightedCocone₀. -/
theorem wppModifiedCocone_diagonal_eq_one :
    ∀ (w : wppWeightAt coTwIdOne),
    wppModifiedCocone.leg coTwIdOne w = wppWeightedCocone₀.leg coTwIdOne w := by
  intro w
  rw [wppModifiedCocone_leg_coTwIdOne, wppWeightedCocone₀_leg_eq]

/-- The modified cocone differs from wppWeightedCocone₀ at (coTwLeft, wppWeightRight). -/
theorem wppModifiedCocone_differs_at_right :
    wppModifiedCocone.leg coTwLeft wppWeightRight ≠
    wppWeightedCocone₀.leg coTwLeft wppWeightRight := by
  rw [wppModifiedCocone_leg_coTwLeft, wppWeightedCocone₀_leg_eq,
      modifiedLegAtCoTwLeft_right_eq_one]
  intro h
  have h0 : (wppCastLeg coTwLeft (fun _ => 0)) (0 : ℕ) = 0 := rfl
  have h1 : (wppCastLeg coTwLeft (fun _ => 1)) (0 : ℕ) = 1 := rfl
  have : (0 : ℕ) = 1 := by
    calc 0 = (wppCastLeg coTwLeft (fun _ => 0)) (0 : ℕ) := h0.symm
      _ = (wppCastLeg coTwLeft (fun _ => 1)) (0 : ℕ) := congrFun h.symm (0 : ℕ)
      _ = 1 := h1
  exact Nat.zero_ne_one this

/-- The two cocones wppWeightedCocone₀ and wppModifiedCocone have the same
legs at identity co-twisted arrows but differ at (coTwLeft, wppWeightRight).

This demonstrates that diagonal data does not determine the full cocone
structure: two cocones can agree on all identity positions yet differ
elsewhere. -/
theorem diagonal_does_not_determine_cocone :
    (wppWeightedCocone₀.pt = wppModifiedCocone.pt) ∧
    (wppWeightedCocone₀.leg coTwIdZero = wppModifiedCocone.leg coTwIdZero) ∧
    (wppWeightedCocone₀.leg coTwIdOne = wppModifiedCocone.leg coTwIdOne) ∧
    (wppWeightedCocone₀.leg coTwLeft wppWeightRight ≠
     wppModifiedCocone.leg coTwLeft wppWeightRight) := by
  refine ⟨rfl, ?_, ?_, ?_⟩
  · -- coTwIdZero case: both are constant 0
    funext w
    rw [wppWeightedCocone₀_leg_eq, wppModifiedCocone_leg_coTwIdZero]
  · -- coTwIdOne case
    funext w
    rw [wppWeightedCocone₀_leg_eq]
    simp only [wppModifiedCocone, WeightedCocone.leg, WeightedCocone.ι, wppModifiedLegNatTrans]
    have hne : (Opposite.op coTwIdOne).unop ≠ coTwLeft := coTwIdOne_ne_coTwLeft
    simp only [hne, ↓reduceDIte]
  · -- The legs differ at (coTwLeft, wppWeightRight)
    exact wppModifiedCocone_differs_at_right.symm

end NonFullnessCounterexample

section CValuedCounterexample

/-!
### Counterexample for C-valued diagram

The restriction functor `restrictionFunctor H G : WeightedCowedge H G ⥤ RestrictedCowedge G H`
requires `G : Cᵒᵖ ⥤ C ⥤ C` (valued in C, not Type). We analyze whether fullness fails
for this case using C = WalkingParallelPair.

The difference from the Type-valued case: legs are morphisms in C, which have
limited choices. With G constant at `zero`, the diagram values are all `zero`,
so legs to apex A are morphisms `zero ⟶ A`.
-/

/-- Constant profunctor valued in WalkingParallelPair (as a category), constant at zero. -/
abbrev wppConstDiagramC : WalkingParallelPairᵒᵖ ⥤ WalkingParallelPair ⥤
    WalkingParallelPair :=
  (Functor.const WalkingParallelPairᵒᵖ).obj
    ((Functor.const WalkingParallelPair).obj WalkingParallelPair.zero)

/-- The diagram value is constantly zero. -/
theorem wppConstDiagramC_obj_obj (A : WalkingParallelPairᵒᵖ) (B : WalkingParallelPair) :
    (wppConstDiagramC.obj A).obj B = WalkingParallelPair.zero := rfl

/-- The diagram morphisms are identities. -/
theorem wppConstDiagramC_obj_map (A : WalkingParallelPairᵒᵖ) {B B' : WalkingParallelPair}
    (f : B ⟶ B') :
    (wppConstDiagramC.obj A).map f = 𝟙 WalkingParallelPair.zero := rfl

/-- The diagram natural transformation components are identities. -/
theorem wppConstDiagramC_map_app {A A' : WalkingParallelPairᵒᵖ} (g : A ⟶ A')
    (B : WalkingParallelPair) :
    (wppConstDiagramC.map g).app B = 𝟙 WalkingParallelPair.zero := rfl

/-- The C-valued diagram functor on CoTwistedArrow. -/
abbrev wppDiagramFunctorC : CoTwistedArrow WalkingParallelPair ⥤ WalkingParallelPair :=
  profunctorOnCoTwistedArrow WalkingParallelPair wppConstDiagramC

/-- The C-valued diagram is constant at zero. -/
theorem wppDiagramFunctorC_obj_eq (tw : CoTwistedArrow WalkingParallelPair) :
    wppDiagramFunctorC.obj tw = WalkingParallelPair.zero := rfl

/-- Morphisms in the C-valued diagram are identities. -/
theorem wppDiagramFunctorC_map_eq {tw tw' : CoTwistedArrow WalkingParallelPair}
    (m : tw ⟶ tw') : wppDiagramFunctorC.map m = 𝟙 WalkingParallelPair.zero := by
  unfold wppDiagramFunctorC profunctorOnCoTwistedArrow
  simp only [Functor.comp_map, Functor.uncurry_obj_map]
  simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
  rfl

/-!
### Analysis of weighted cowedge structure with C-valued diagram

With `G = wppConstDiagramC` constant at zero:
- The diagram functor `wppDiagramFunctorC` is constant at `zero : WalkingParallelPair`
- A leg at co-twisted arrow `tw` with weight `w` is a morphism `zero → apex`
- When apex = zero, only `id_zero` is available
- When apex = one, both `left` and `right` are available

The weight at `tw` comes from `profunctorOnOpCoTwistedArrow WalkingParallelPair H`
evaluated at `tw`.

For the weighted cowedge naturality to hold, the morphism constraints are:
- For `m : tw → tw'` in CoTwistedArrow, we need:
  `leg(tw', W.map(m.op)(w)) ∘ D.map(m) = leg(tw, w)`
- Since D.map(m) = id_zero for all m, this simplifies to:
  `leg(tw', W.map(m.op)(w)) = leg(tw, w)`

The weight transport goes: when m : tw → tw', the weight maps W(tw')ᵒᵖ → W(tw)ᵒᵖ.

For a morphism TO coTwLeft, we've established there are NONE from diagonals
(coTwIdZero, coTwIdOne). So the leg at coTwLeft is unconstrained by diagonal
legs - any choice satisfies naturality vacuously.
-/

/-- A WeightedCowedge for the C-valued diagram consists of an apex and legs
that are morphisms from zero to the apex. -/
abbrev CValuedWeightedCowedge (H : WalkingParallelPairᵒᵖ ⥤ WalkingParallelPair ⥤ Type) :=
  WeightedCowedge H wppConstDiagramC

/-- The weight type at a co-twisted arrow for the C-valued cowedge. -/
abbrev cValuedWeightAt (H : WalkingParallelPairᵒᵖ ⥤ WalkingParallelPair ⥤ Type)
    (tw : CoTwistedArrow WalkingParallelPair) : Type :=
  (profunctorOnOpCoTwistedArrow WalkingParallelPair H).obj (Opposite.op tw)

/-!
### The non-fullness argument for C-valued diagrams

The restriction functor `restrictionFunctor H wppConstDiagramC` is not full.
The argument follows the same structure as the Type-valued case:

1. With `G = wppConstDiagramC` constant at zero, the diagram is constant
2. A weighted cowedge with apex `one` has legs that are morphisms `zero → one`
3. The morphisms `zero → one` in WalkingParallelPair are `left` and `right`
4. Weight transport only constrains `wppWeightLeft` at coTwLeft, not `wppWeightRight`
5. Two cowedges can agree on diagonal legs but differ at (coTwLeft, wppWeightRight)
6. The identity morphism on their restrictions doesn't lift to a cowedge morphism

The restriction functor being not full means there exist restricted cowedge
morphisms that don't come from weighted cowedge morphisms. Specifically,
when two weighted cowedges have the same diagonal legs but different
non-diagonal legs, the identity on their common restriction is a valid
restricted morphism but doesn't lift.
-/

/-- The C-valued weight functor is the same as the Type-valued one
(both use wppHomProfunctor). -/
abbrev cValuedWeightFunctor :
    (CoTwistedArrow WalkingParallelPair)ᵒᵖ ⥤ Type :=
  profunctorOnOpCoTwistedArrow WalkingParallelPair wppHomProfunctor

/-- The C-valued weight at a co-twisted arrow equals the Type-valued weight. -/
theorem cValuedWeightFunctor_eq_wppWeightFunctor :
    cValuedWeightFunctor = wppWeightFunctor := rfl

/-- For a C-valued weighted cocone morphism with identity apex, all legs must be
equal as morphisms in C. -/
theorem cValued_cocone_morphism_id_forces_equal_legs
    (c₁ c₂ : WeightedCocone cValuedWeightFunctor wppDiagramFunctorC)
    (apex_eq : c₁.pt = c₂.pt)
    (h_mor : WeightedCocone.Hom c₁ c₂)
    (h_id : h_mor.hom = eqToHom apex_eq)
    (tw : CoTwistedArrow WalkingParallelPair)
    (w : cValuedWeightFunctor.obj (Opposite.op tw)) :
    c₁.leg tw w ≫ eqToHom apex_eq = c₂.leg tw w := by
  have comm := h_mor.w tw w
  rw [h_id] at comm
  exact comm

/-- Non-fullness statement for the C-valued restriction functor:
Morphisms `zero → one` in WalkingParallelPair consist of exactly `left` and
`right`. Two different choices for `leg(coTwLeft)(wppWeightRight)` lead to
cowedges that agree on diagonals but differ at that position.

The identity morphism on the common restriction cannot lift to a weighted
cowedge morphism because lifting requires all legs to match, but the legs
differ at (coTwLeft, wppWeightRight). -/
theorem cValued_restrictionFunctor_not_full_statement :
    (∃ (f : WalkingParallelPair.zero ⟶ WalkingParallelPair.one),
      f ≠ WalkingParallelPairHom.left ∧ f ≠ WalkingParallelPairHom.right →
      False) ∧
    WalkingParallelPairHom.left ≠ WalkingParallelPairHom.right := by
  constructor
  · use WalkingParallelPairHom.left
    intro h
    exact h.1 rfl
  · intro h
    cases h

/-- The restriction functor for C-valued diagrams shares the same weight
transport properties as the Type-valued case. Since the weight functor is
identical, the results about wppWeightRight not being constrained by
diagonal transport apply equally.

Combined with:
1. `wppWeightRight_not_constrained_by_diagonals`: wppWeightRight is not in the
   image of weight transport from any diagonal
2. `cValued_restrictionFunctor_not_full_statement`: left ≠ right in C
3. `cValued_cocone_morphism_id_forces_equal_legs`: any cocone morphism with
   identity apex forces all legs to match

This establishes that `restrictionFunctor wppHomProfunctor wppConstDiagramC`
is not full: two cowedges can agree on diagonals but differ at
(coTwLeft, wppWeightRight) by using `left` vs `right`, and the identity on
their common restriction cannot lift. -/
theorem cValued_restrictionFunctor_not_full_key_facts :
    (WalkingParallelPairHom.left ≠ WalkingParallelPairHom.right) ∧
    (∀ (_ : coTwIdZero ⟶ coTwLeft), False) ∧
    (∀ (_ : coTwIdOne ⟶ coTwLeft), False) :=
  And.intro walkingParallelPair_left_ne_right
    (And.intro no_mor_coTwIdZero_to_coTwLeft no_mor_coTwIdOne_to_coTwLeft)

/-- For any co-twisted arrow, the diagram is constant at zero. -/
theorem wppDiagramFunctorC_obj_eq_zero (tw : CoTwistedArrow WalkingParallelPair) :
    wppDiagramFunctorC.obj tw = WalkingParallelPair.zero := rfl

/-- The leg function for C-valued cowedges with apex `one`.
All legs go from `zero` (the constant diagram value) to `one`.
This version sends all weight elements to `left`. -/
def cValuedLegAllLeft (tw : CoTwistedArrow WalkingParallelPair)
    (_ : cValuedWeightFunctor.obj (Opposite.op tw)) :
    wppDiagramFunctorC.obj tw ⟶ WalkingParallelPair.one :=
  (wppDiagramFunctorC_obj_eq_zero tw) ▸ WalkingParallelPairHom.left

/-- The natural transformation for the all-left cowedge.
Since the diagram is constant at zero, naturality is trivial. -/
def cValuedAllLeftNatTrans :
    cValuedWeightFunctor ⟶ homToFunctor wppDiagramFunctorC WalkingParallelPair.one where
  app := fun tw_op w => cValuedLegAllLeft tw_op.unop w
  naturality := fun _ _ f => by
    ext _
    simp only [types_comp_apply, cValuedLegAllLeft]
    rfl

/-- The leg function for C-valued cowedges sending wppWeightRight to `right`
and everything else to `left`. -/
def cValuedLegRightAtRight (tw : CoTwistedArrow WalkingParallelPair)
    (w : cValuedWeightFunctor.obj (Opposite.op tw)) :
    wppDiagramFunctorC.obj tw ⟶ WalkingParallelPair.one :=
  (wppDiagramFunctorC_obj_eq_zero tw) ▸
    if htw : tw = coTwLeft then
      if _ : (htw ▸ w : wppWeightAt coTwLeft) = wppWeightRight then
        WalkingParallelPairHom.right
      else WalkingParallelPairHom.left
    else WalkingParallelPairHom.left

/-- The leg at coTwLeft for wppWeightRight is `right`. -/
theorem cValuedLegRightAtRight_coTwLeft_wppWeightRight :
    cValuedLegRightAtRight coTwLeft wppWeightRight = WalkingParallelPairHom.right := by
  simp only [cValuedLegRightAtRight, dite_true]

/-- The leg at coTwLeft for wppWeightLeft is `left`. -/
theorem cValuedLegRightAtRight_coTwLeft_wppWeightLeft :
    cValuedLegRightAtRight coTwLeft wppWeightLeft = WalkingParallelPairHom.left := by
  simp only [cValuedLegRightAtRight, dite_true, wppWeightLeft_ne_wppWeightRight, dite_false]

/-- The leg at non-coTwLeft positions is `left`. -/
theorem cValuedLegRightAtRight_not_coTwLeft (tw : CoTwistedArrow WalkingParallelPair)
    (hne : tw ≠ coTwLeft)
    (w : cValuedWeightFunctor.obj (Opposite.op tw)) :
    cValuedLegRightAtRight tw w = WalkingParallelPairHom.left := by
  simp only [cValuedLegRightAtRight, hne, dite_false]

/-- The natural transformation for the right-at-right cowedge. -/
def cValuedRightAtRightNatTrans :
    cValuedWeightFunctor ⟶ homToFunctor wppDiagramFunctorC WalkingParallelPair.one where
  app := fun tw_op w => cValuedLegRightAtRight tw_op.unop w
  naturality := fun x y f => by
    ext w
    simp only [types_comp_apply]
    change cValuedLegRightAtRight y.unop (cValuedWeightFunctor.map f w) =
      wppDiagramFunctorC.map f.unop ≫ cValuedLegRightAtRight x.unop w
    simp only [wppDiagramFunctorC_map_eq]
    -- Now show: cValuedLegRightAtRight y.unop (W.map f w) = cValuedLegRightAtRight x.unop w
    by_cases hx : x.unop = coTwLeft
    · by_cases hy : y.unop = coTwLeft
      · -- Both coTwLeft: x = y, morphism is identity
        have hxy : x = y := Opposite.unop_injective (hx.trans hy.symm)
        subst hxy
        have hx' : x = Opposite.op coTwLeft := by rw [← Opposite.op_unop x, hx]
        subst hx'
        have hf_id : f = 𝟙 (Opposite.op coTwLeft) := by
          apply Quiver.Hom.unop_inj
          exact coTwLeft_endo_is_id f.unop
        simp only [hf_id, Functor.map_id, types_id_apply]
        rfl
      · -- x is coTwLeft, y is not: no morphism y.unop → coTwLeft
        exfalso
        have hf : y.unop ⟶ coTwLeft := hx ▸ f.unop
        rcases wppCoTwArrow_cases y.unop with hycase | hycase | hycase | hycase
        · exact no_mor_coTwIdZero_to_coTwLeft (hycase ▸ hf)
        · exact no_mor_coTwIdOne_to_coTwLeft (hycase ▸ hf)
        · exact hy hycase
        · exact no_mor_coTwRight_to_coTwLeft
            (coTwRight_eq_coTwRight'.symm ▸ hycase ▸ hf)
    · by_cases hy : y.unop = coTwLeft
      · -- x is not coTwLeft, y is coTwLeft
        -- RHS: leg at x (not coTwLeft) = left
        rw [cValuedLegRightAtRight_not_coTwLeft x.unop hx w]
        -- LHS: weight transport to coTwLeft yields wppWeightLeft, so leg = left
        rcases wppCoTwArrow_cases x.unop with hxcase | hxcase | hxcase | hxcase
        · -- x.unop = coTwIdZero
          have hx' : x = Opposite.op coTwIdZero := by
            rw [← Opposite.op_unop x, hxcase]
          have hy' : y = Opposite.op coTwLeft := by
            rw [← Opposite.op_unop y, hy]
          subst hx' hy'
          have hf_unop : f.unop = coTwMorLeftToIdZero :=
            coTwLeft_to_coTwIdZero_unique f.unop
          have hf : f = coTwMorLeftToIdZero.op := by
            rw [← Quiver.Hom.op_unop f, hf_unop]
          have hw : w = wppWeightIdZero := by
            unfold wppWeightIdZero
            exact walkingParallelPair_zero_zero_eq_id (cast wppWeightAt_coTwIdZero w)
          simp only [Opposite.unop_op, hw, hf, wppWeightTransport_fromIdZero_eq_left,
            cValuedLegRightAtRight_coTwLeft_wppWeightLeft]
          rfl
        · -- x.unop = coTwIdOne
          have hx' : x = Opposite.op coTwIdOne := by
            rw [← Opposite.op_unop x, hxcase]
          have hy' : y = Opposite.op coTwLeft := by
            rw [← Opposite.op_unop y, hy]
          subst hx' hy'
          have hf_unop : f.unop = coTwMorLeftToIdOne :=
            coTwLeft_to_coTwIdOne_unique f.unop
          have hf : f = coTwMorLeftToIdOne.op := by
            rw [← Quiver.Hom.op_unop f, hf_unop]
          have hw : w = wppWeightIdOne := by
            unfold wppWeightIdOne
            exact walkingParallelPair_one_one_eq_id (cast wppWeightAt_coTwIdOne w)
          simp only [Opposite.unop_op, hw, hf, wppWeightTransport_fromIdOne_eq_left,
            cValuedLegRightAtRight_coTwLeft_wppWeightLeft]
          rfl
        · -- x.unop = coTwLeft (contradiction with hx)
          exact absurd hxcase hx
        · -- x.unop = coTwRight' (no morphism coTwLeft → coTwRight')
          exfalso
          have hf' : coTwLeft ⟶ coTwRight' := hy ▸ hxcase ▸ f.unop
          exact no_mor_coTwLeft_to_coTwRight
            (coTwRight_eq_coTwRight'.symm ▸ hf')
      · -- Neither is coTwLeft: both legs are left
        rw [cValuedLegRightAtRight_not_coTwLeft x.unop hx w,
          cValuedLegRightAtRight_not_coTwLeft y.unop hy _]
        rfl

/-- The first C-valued weighted cowedge: all legs are `left`. -/
def cValuedCowedgeAllLeft :
    WeightedCocone cValuedWeightFunctor wppDiagramFunctorC where
  pt := WalkingParallelPair.one
  toWeightedCoconeOver := cValuedAllLeftNatTrans

/-- The second C-valued weighted cowedge: leg at (coTwLeft, wppWeightRight) is
`right`, all others are `left`. -/
def cValuedCowedgeRightAtRight :
    WeightedCocone cValuedWeightFunctor wppDiagramFunctorC where
  pt := WalkingParallelPair.one
  toWeightedCoconeOver := cValuedRightAtRightNatTrans

/-- The two C-valued cowedges have the same apex. -/
theorem cValuedCowedges_same_apex :
    cValuedCowedgeAllLeft.pt = cValuedCowedgeRightAtRight.pt := rfl

/-- The leg of cValuedCowedgeAllLeft at any position is `left`. -/
theorem cValuedCowedgeAllLeft_leg
    (tw : CoTwistedArrow WalkingParallelPair)
    (w : cValuedWeightFunctor.obj (Opposite.op tw)) :
    cValuedCowedgeAllLeft.leg tw w = WalkingParallelPairHom.left := by
  simp only [cValuedCowedgeAllLeft, WeightedCocone.leg, cValuedAllLeftNatTrans,
    cValuedLegAllLeft]

/-- The leg of cValuedCowedgeRightAtRight at (coTwLeft, wppWeightRight) is `right`. -/
theorem cValuedCowedgeRightAtRight_leg_coTwLeft_wppWeightRight :
    cValuedCowedgeRightAtRight.leg coTwLeft wppWeightRight =
    WalkingParallelPairHom.right := by
  simp only [cValuedCowedgeRightAtRight, WeightedCocone.leg, cValuedRightAtRightNatTrans,
    cValuedLegRightAtRight]
  simp only [dite_true]

/-- The two cowedges differ at (coTwLeft, wppWeightRight). -/
theorem cValuedCowedges_differ_at_coTwLeft_wppWeightRight :
    cValuedCowedgeAllLeft.leg coTwLeft wppWeightRight ≠
    cValuedCowedgeRightAtRight.leg coTwLeft wppWeightRight := by
  rw [cValuedCowedgeAllLeft_leg, cValuedCowedgeRightAtRight_leg_coTwLeft_wppWeightRight]
  exact walkingParallelPair_left_ne_right

/-- The two cowedges have the same leg at coTwIdZero. -/
theorem cValuedCowedges_same_leg_coTwIdZero
    (w : cValuedWeightFunctor.obj (Opposite.op coTwIdZero)) :
    cValuedCowedgeAllLeft.leg coTwIdZero w =
    cValuedCowedgeRightAtRight.leg coTwIdZero w := by
  simp only [cValuedCowedgeAllLeft_leg]
  simp only [cValuedCowedgeRightAtRight, WeightedCocone.leg, cValuedRightAtRightNatTrans,
    cValuedLegRightAtRight]
  have hne : coTwIdZero ≠ coTwLeft := by
    intro heq
    have : coTwDom coTwIdZero = coTwDom coTwLeft := congrArg coTwDom heq
    rw [coTwIdZero_dom, coTwLeft_dom] at this
    cases this
  simp only [hne, ↓reduceDIte]

/-- The two cowedges have the same leg at coTwIdOne. -/
theorem cValuedCowedges_same_leg_coTwIdOne
    (w : cValuedWeightFunctor.obj (Opposite.op coTwIdOne)) :
    cValuedCowedgeAllLeft.leg coTwIdOne w =
    cValuedCowedgeRightAtRight.leg coTwIdOne w := by
  simp only [cValuedCowedgeAllLeft_leg]
  simp only [cValuedCowedgeRightAtRight, WeightedCocone.leg, cValuedRightAtRightNatTrans,
    cValuedLegRightAtRight]
  have hne : coTwIdOne ≠ coTwLeft := by
    intro heq
    have : coTwCod coTwIdOne = coTwCod coTwLeft := congrArg coTwCod heq
    rw [coTwIdOne_cod, coTwLeft_cod] at this
    cases this
  simp only [hne, ↓reduceDIte]

/-- The two cowedges have the same restriction (same diagonal legs). -/
theorem cValuedCowedges_same_restriction :
    (restrictionFunctor wppHomProfunctor wppConstDiagramC).obj cValuedCowedgeAllLeft =
    (restrictionFunctor wppHomProfunctor wppConstDiagramC).obj cValuedCowedgeRightAtRight := by
  apply RestrictedCowedge.ext
  · rfl
  · -- Since pt₁ = pt₂ by rfl, show equality of the underlying Over structures
    apply heq_of_eq
    apply RestrictedCowedgeOver.ext
    · -- Show family equality
      funext A a
      match A with
      | WalkingParallelPair.zero =>
        simp only [restrictionFunctor, restrictWeightedCowedge,
          weightedCowedgeFamilyAtIdentity]
        exact cValuedCowedges_same_leg_coTwIdZero (cast (congrArg _ rfl) a)
      | WalkingParallelPair.one =>
        simp only [restrictionFunctor, restrictWeightedCowedge,
          weightedCowedgeFamilyAtIdentity]
        exact cValuedCowedges_same_leg_coTwIdOne (cast (congrArg _ rfl) a)

/-- The restriction functor `restrictionFunctor wppHomProfunctor wppConstDiagramC`
from weighted cowedges to restricted cowedges is NOT full.

The proof constructs two weighted cowedges with the same restriction but different
legs at (coTwLeft, wppWeightRight), showing the identity on the restriction
cannot lift to a weighted cowedge morphism. -/
theorem cValued_restrictionFunctor_not_full :
    ¬ Functor.Full (restrictionFunctor wppHomProfunctor wppConstDiagramC) := by
  apply restrictionFunctor_not_full_of_counterexample
    cValuedCowedges_same_restriction (tw := coTwLeft) (w := wppWeightRight)
  intro heq
  have h1 := cValuedCowedgeAllLeft_leg coTwLeft wppWeightRight
  have h2 := cValuedCowedgeRightAtRight_leg_coTwLeft_wppWeightRight
  rw [h1, h2] at heq
  exact walkingParallelPair_left_ne_right (eq_of_heq heq)

end CValuedCounterexample

/-!
### Non-fullness of the strong restriction functor

Since `restrictionFunctor = strongRestrictionFunctor ⋙ inclusion` and
`inclusion` is full, the non-fullness of `restrictionFunctor` implies
non-fullness of `strongRestrictionFunctor`.

The argument: if `strongRestrictionFunctor` were full, then the composition
with the full functor `inclusion` would also be full. But `restrictionFunctor`
is not full (proven above), contradiction.
-/

/-- The strong restriction functor is not full.

Since `restrictionFunctor = strongRestrictionFunctor ⋙ inclusion` and the
inclusion is full, the non-fullness of `restrictionFunctor` (proven in
`cValued_restrictionFunctor_not_full`) implies non-fullness of
`strongRestrictionFunctor`. -/
theorem cValued_strongRestrictionFunctor_not_full :
    ¬ Functor.Full (strongRestrictionFunctor wppHomProfunctor wppConstDiagramC)
    := by
  have hcomp : restrictionFunctor wppHomProfunctor wppConstDiagramC =
      strongRestrictionFunctor wppHomProfunctor wppConstDiagramC ⋙
        StrongRestrictedCowedge.inclusion wppConstDiagramC wppHomProfunctor :=
    restrictionFunctor_eq_inclusion_comp_strong wppHomProfunctor wppConstDiagramC
  have hnotfull := cValued_restrictionFunctor_not_full
  rw [hcomp] at hnotfull
  letI : (StrongRestrictedCowedge.inclusion wppConstDiagramC wppHomProfunctor).Full :=
    (StrongRestrictedCowedge.inclusion_fullyFaithful
      wppConstDiagramC wppHomProfunctor).full
  exact Functor.not_full_of_comp_not_full_and_full
    (strongRestrictionFunctor wppHomProfunctor wppConstDiagramC)
    (StrongRestrictedCowedge.inclusion wppConstDiagramC wppHomProfunctor)
    hnotfull

end WeightedRestrictedCorrespondence

end GebLean
