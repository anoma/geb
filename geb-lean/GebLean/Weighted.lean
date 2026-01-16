import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.Shapes.End
import GebLean.Utilities.TwArrPresheaf

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
      twObjMk_dom, Functor.map_id, Category.comp_id]
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

end CowedgeCoconeCorrespondence

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

section RestrictedCowedges

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
An `H`-restricted `G`-cowedge for an endodifunctor `G : Cᵒᵖ ⥤ C ⥤ C` and
restriction functor `H : Cᵒᵖ ⥤ C ⥤ Type w`.

This consists of a carrier object and a family of morphisms parametrized
by diagonal elements of `H`, satisfying a dinaturality condition.
-/
structure RestrictedCowedge (G : Cᵒᵖ ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ Type w) where
  /-- The carrier (summit) object. -/
  pt : C
  /-- For each `A : C` and `a : H(A, A)`, a morphism `G(A, A) → pt`. -/
  family (A : C) : (H.obj (Opposite.op A)).obj A → ((G.obj (Opposite.op A)).obj A ⟶ pt)
  /-- Dinaturality: for `g : A → B` and `x : H(B, A)`, the two paths to `pt`
  from `G(B, A)` agree. -/
  dinaturality {A B : C} (g : A ⟶ B) (x : (H.obj (Opposite.op B)).obj A) :
    (G.map g.op).app A ≫ family A ((H.map g.op).app A x) =
    (G.obj (Opposite.op B)).map g ≫ family B ((H.obj (Opposite.op B)).map g x)

namespace RestrictedCowedge

variable {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type w}

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

/--
The category of `H`-restricted `G`-cowedges.

Objects are restricted cowedges `(C, Φ)` and morphisms are arrows `h : C → D`
compatible with the family structure.
-/
instance RestrictedCowedgeCat (G : Cᵒᵖ ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ Type w) :
    Category (RestrictedCowedge G H) where
  Hom := RestrictedCowedge.Hom
  id := RestrictedCowedge.Hom.id
  comp := RestrictedCowedge.Hom.comp
  id_comp f := by ext; simp [RestrictedCowedge.Hom.comp, RestrictedCowedge.Hom.id]
  comp_id f := by ext; simp [RestrictedCowedge.Hom.comp, RestrictedCowedge.Hom.id]
  assoc f g h := by ext; simp [RestrictedCowedge.Hom.comp]

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
abbrev IsRestrictedCoend (G : Cᵒᵖ ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ Type w)
    (c : RestrictedCowedge G H) :=
  Limits.IsInitial c

namespace IsRestrictedCoend

variable {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type w} {c : RestrictedCowedge G H}

/-- The universal morphism from a restricted coend to any restricted cowedge. -/
noncomputable def desc (hc : IsRestrictedCoend G H c)
    (d : RestrictedCowedge G H) : c ⟶ d :=
  hc.to d

/-- The underlying morphism in `C` from a restricted coend to any cowedge. -/
noncomputable def descHom (hc : IsRestrictedCoend G H c)
    (d : RestrictedCowedge G H) : c.pt ⟶ d.pt :=
  (hc.desc d).hom

/-- Any two morphisms from a restricted coend are equal (uniqueness). -/
theorem homExt (hc : IsRestrictedCoend G H c)
    {d : RestrictedCowedge G H} (f g : c ⟶ d) : f = g :=
  Limits.IsInitial.hom_ext hc f g

/-- Two restricted coends are isomorphic (uniqueness up to isomorphism). -/
noncomputable def toUniqueUpToIso {c c' : RestrictedCowedge G H}
    (hc : IsRestrictedCoend G H c) (hc' : IsRestrictedCoend G H c') :
    c ≅ c' :=
  Limits.IsInitial.uniqueUpToIso hc hc'

end IsRestrictedCoend

/-- A restricted coend exists if there is an initial restricted cowedge. -/
class HasRestrictedCoend (G : Cᵒᵖ ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ Type w) : Prop where
  exists_initial : ∃ c : RestrictedCowedge G H, Nonempty (IsRestrictedCoend G H c)

namespace HasRestrictedCoend

variable (G : Cᵒᵖ ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ Type w) [HasRestrictedCoend G H]

/-- The restricted coend object (carrier of the initial restricted cowedge). -/
noncomputable def restrictedCoend : RestrictedCowedge G H :=
  Classical.choose HasRestrictedCoend.exists_initial

/-- The restricted coend is initial. -/
noncomputable def restrictedCoendIsInitial :
    IsRestrictedCoend G H (restrictedCoend G H) :=
  Classical.choice (Classical.choose_spec HasRestrictedCoend.exists_initial)

end HasRestrictedCoend

end RestrictedCoends

end GebLean
