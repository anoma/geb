import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Cones
import Mathlib.CategoryTheory.Limits.Shapes.End
import GebLean.Paranatural
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
    Wedge P ≌ Cone (profunctorOnTwistedArrow C P) where
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
    Cowedge P ≌ Cocone (profunctorOnCoTwistedArrow C P) where
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

variable {J : Type*} [Category J]

/--
The functor `Hom(X, D(-)) : J ⥤ Type v` for a fixed object `X : C` and
diagram `D : J ⥤ C`. This is the composition `D ⋙ coyoneda.obj (op X)`.
-/
abbrev homFromFunctor (X : C) (D : J ⥤ C) : J ⥤ Type v :=
  D ⋙ coyoneda.obj (Opposite.op X)

/--
The functor `Hom(D(-), X) : Jᵒᵖ ⥤ Type v` for a fixed object `X : C` and
diagram `D : J ⥤ C`. This sends `j` to `Hom(D.obj j, X)` and acts
contravariantly via precomposition.
-/
def homToFunctor (D : J ⥤ C) (X : C) : Jᵒᵖ ⥤ Type v where
  obj j := D.obj j.unop ⟶ X
  map f g := D.map f.unop ≫ g
  map_id _ := by
    funext g
    simp only [unop_id, Functor.map_id, Category.id_comp, types_id_apply]
  map_comp f g := by
    funext h
    simp only [unop_comp, Functor.map_comp, Category.assoc, types_comp_apply]

/--
A weighted cone over a diagram `D : J ⥤ C` with weight `W : J ⥤ Type v`
consists of a cone point `pt` and a natural transformation from `W` to the
functor `Hom(pt, D(-))`.
-/
@[ext]
structure WeightedCone (W : J ⥤ Type v) (D : J ⥤ C) where
  /-- The cone point -/
  pt : C
  /-- The natural transformation from the weight to `Hom(pt, D(-))` -/
  π : W ⟶ homFromFunctor pt D

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
  simp only [Functor.comp_obj, Functor.comp_map] at nat
  exact (congrFun nat w).symm

/--
A weighted cocone over a diagram `D : J ⥤ C` with weight `W : Jᵒᵖ ⥤ Type v`
(a presheaf on `J`) consists of a cocone point `pt` and a natural
transformation from `W` to the functor `Hom(D(-), pt)`.

Note: The weight is contravariant (`Jᵒᵖ ⥤ Type v`) to match the variance
of `Hom(D(-), pt)`.
-/
@[ext]
structure WeightedCocone (W : Jᵒᵖ ⥤ Type v) (D : J ⥤ C) where
  /-- The cocone point -/
  pt : C
  /-- The natural transformation from the weight to `Hom(D(-), pt)` -/
  ι : W ⟶ homToFunctor D pt

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

variable {D : Type w} [Category.{v} D]

/--
A weighted wedge over a profunctor `P : Cᵒᵖ ⥤ C ⥤ D` with weight
`W : TwistedArrow C ⥤ Type v` is a weighted cone over the diagram
`profunctorOnTwistedArrow C P` with the given weight.

This generalizes ordinary wedges: when `W` is the terminal functor (constant
at a singleton), a weighted wedge is exactly an ordinary wedge.
-/
abbrev WeightedWedge (W : TwistedArrow C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) :=
  WeightedCone (J := TwistedArrow C) W (profunctorOnTwistedArrow C P)

/--
A weighted cowedge over a profunctor `P : Cᵒᵖ ⥤ C ⥤ D` with weight
`W : (TwistedArrow C)ᵒᵖ ⥤ Type v` is a weighted cocone over the diagram
`profunctorOnTwistedArrow C P` with the given weight.

The weight is contravariant (a presheaf on `TwistedArrow C`) to match the
variance required by weighted cocones.
-/
abbrev WeightedCowedge (W : (TwistedArrow C)ᵒᵖ ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) :=
  WeightedCocone (J := TwistedArrow C) W (profunctorOnTwistedArrow C P)

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
  π := {
    app := fun j _ => c.π.app j
    naturality := fun j j' f => by
      funext _
      simp only [types_comp_apply, homFromFunctor, Functor.comp_obj, Functor.comp_map,
        unitWeight, Functor.const_obj_obj, Functor.const_obj_map]
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
        homFromFunctor, Functor.comp_obj, Functor.comp_map] at nat
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
  ext
  · rfl
  · apply heq_of_eq
    ext j w
    cases w
    rfl

/--
Convert an ordinary cocone to a weighted cocone with the constant unit weight.

For a cocone over `D : J ⥤ C`, the weighted cocone has:
- The same apex `c.pt`
- For each `j : J`, the unique element of `PUnit` maps to `c.ι.app j`
-/
def coconeToWeightedCocone {D : J ⥤ C} (c : Cocone (J := J) D) :
    WeightedCocone (unitWeightOp J) D where
  pt := c.pt
  ι := {
    app := fun j _ => c.ι.app j.unop
    naturality := fun j j' f => by
      funext _
      simp only [types_comp_apply, homToFunctor, unitWeightOp,
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
  ext
  · rfl
  · apply heq_of_eq
    ext j w
    cases w
    simp only [coconeToWeightedCocone, weightedCoconeToCocone, Opposite.op_unop]

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
Convert a weighted cone to a cone over the category of elements.

Given `c : WeightedCone W D`, define a cone over `CategoryOfElements.π W ⋙ D` with:
- Apex: `c.pt`
- Legs: for `p = ⟨j, w⟩`, the leg is `c.leg j w : c.pt ⟶ D.obj j`
-/
def weightedConeToElementsCone (W : J ⥤ Type v₁) (D : J ⥤ C)
    (c : WeightedCone W D) : Cone (CategoryOfElements.π W ⋙ D) where
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
  π := {
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
  cases c
  rfl

/--
`elementsConeToWeightedCone` and `weightedConeToElementsCone` are inverses (other direction).
-/
theorem elements_weightedCone_roundtrip (W : J ⥤ Type v₁) (D : J ⥤ C)
    (c : Cone (CategoryOfElements.π W ⋙ D)) :
    weightedConeToElementsCone W D (elementsConeToWeightedCone W D c) = c := by
  cases c with
  | mk pt π =>
    rfl

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
    WeightedCone W D ≌ Cone (CategoryOfElements.π W ⋙ D) where
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
  ι := {
    app := fun j_op w => c.ι.app (Opposite.op (Sigma.mk j_op w))
    naturality := fun {j_op j'_op} f => by
      ext w
      dsimp [homToFunctor]
      -- We need: c.ι.app (op ⟨j'_op, W.map f w⟩) = D.map f.unop ≫ c.ι.app (op ⟨j_op, w⟩)
      -- Use cocone naturality for morphism from op ⟨j'_op, W.map f w⟩ to op ⟨j_op, w⟩
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
  | mk pt ι => rfl

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
`(CategoryOfElements.π W).op ⋙ unopUnop J ⋙ D : (W.Elements)ᵒᵖ ⥤ C`.

This is foundational for the theory of weighted colimits: it shows that weighted
colimits can be computed as ordinary colimits over the expanded indexing category.
-/
def weightedCoconeElementsEquiv (W : Jᵒᵖ ⥤ Type v₃) (D : J ⥤ C) :
    WeightedCocone W D ≌ Cocone (weightedCoconeDiagram W D) where
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

For a weight `W : TwistedArrow C ⥤ Type v` and profunctor `P : Cᵒᵖ ⥤ C ⥤ D`,
this gives a functor `W.Elements ⥤ D`.
-/
def weightedWedgeDiagram (W : TwistedArrow C ⥤ Type v₅) (P : Cᵒᵖ ⥤ C ⥤ D) :
    W.Elements ⥤ D :=
  CategoryOfElements.π W ⋙ profunctorOnTwistedArrow C P

/--
The diagram for weighted cowedges: composing the projection from the
opposite category of elements with the profunctor-on-twisted-arrow functor.

For a weight `W : (TwistedArrow C)ᵒᵖ ⥤ Type v` and profunctor
`P : Cᵒᵖ ⥤ C ⥤ D`, this gives a functor `(W.Elements)ᵒᵖ ⥤ D`.
-/
def weightedCowedgeDiagram (W : (TwistedArrow C)ᵒᵖ ⥤ Type v₅)
    (P : Cᵒᵖ ⥤ C ⥤ D) : (W.Elements)ᵒᵖ ⥤ D :=
  weightedCoconeDiagram W (profunctorOnTwistedArrow C P)

/--
Weighted wedges over a profunctor `P : Cᵒᵖ ⥤ C ⥤ D` with weight
`W : TwistedArrow C ⥤ Type v` are categorically equivalent to ordinary
cones over the weighted wedge diagram on `W.Elements`.

This follows by applying `weightedConeElementsEquiv` to the definition
`WeightedWedge W P := WeightedCone W (profunctorOnTwistedArrow C P)`.
-/
def weightedWedgeElementsEquiv (W : TwistedArrow C ⥤ Type v₅)
    (P : Cᵒᵖ ⥤ C ⥤ D) : WeightedWedge W P ≌ Cone (weightedWedgeDiagram W P) :=
  weightedConeElementsEquiv W (profunctorOnTwistedArrow C P)

/--
Weighted cowedges over a profunctor `P : Cᵒᵖ ⥤ C ⥤ D` with weight
`W : (TwistedArrow C)ᵒᵖ ⥤ Type v` are categorically equivalent to ordinary
cocones over the weighted cowedge diagram on `(W.Elements)ᵒᵖ`.

This follows by applying `weightedCoconeElementsEquiv` to the definition
`WeightedCowedge W P := WeightedCocone W (profunctorOnTwistedArrow C P)`.
-/
def weightedCowedgeElementsEquiv (W : (TwistedArrow C)ᵒᵖ ⥤ Type v₅)
    (P : Cᵒᵖ ⥤ C ⥤ D) :
    WeightedCowedge W P ≌ Cocone (weightedCowedgeDiagram W P) :=
  weightedCoconeElementsEquiv W (profunctorOnTwistedArrow C P)

end WeightedWedgeCowedgeEquivalences

section WeightedWedgeAsProfunctor

/-!
## Weighted Wedges and Derived Profunctors: Variance Obstruction

We investigate whether weighted wedges can alternatively be characterized as
ordinary wedges over a profunctor defined on the category of elements.

The naive idea is: given `W : TwistedArrow C ⥤ Type v` and `P : Cᵒᵖ ⥤ C ⥤ D`,
define a profunctor `P' : (W.Elements)ᵒᵖ ⥤ W.Elements ⥤ D` by:

  `P'((tw₁, w₁), (tw₂, w₂)) := P(twDom tw₁, twCod tw₂)`

This satisfies the diagonal condition:
`P'((tw, w), (tw, w)) = P(twDom tw, twCod tw)`, matching weighted wedge targets.

However, there is a variance obstruction for the functorial action:

For a TwistedArrow morphism `f : tw₁ ⟶ tw₂`:
- `twDomArr f : twDom tw₂ ⟶ twDom tw₁` (contravariant in the domain)
- `twCodArr f : twCod tw₁ ⟶ twCod tw₂` (covariant in the codomain)

For `P : Cᵒᵖ ⥤ C ⥤ D` (contravariant in first arg, covariant in second):
- The second argument works: `twCodArr` is covariant, matching P's second slot
- The first argument fails: `twDomArr` is contravariant, but when composed with
  P's contravariance and the opposite category structure, we get the wrong
  direction for the overall morphism

Specifically, for `f : X ⟶ Y` in `(W.Elements)ᵒᵖ`:
- `f.unop.val : Y.unop.fst ⟶ X.unop.fst` in TwistedArrow
- `twDomArr f.unop.val : twDom X.unop.fst ⟶ twDom Y.unop.fst`
- After `.op` and `P.map`: morphism from Y's output to X's output
- But we need: morphism from X's output to Y's output

This means `P(twDom -, twCod -)` does not naturally extend to a profunctor on
W.Elements with the expected variance.

### Deeper Explanation: Promonads

For a weighted wedge to reduce to an ordinary wedge over some profunctor
`P' : C'ᵒᵖ ⥤ C' ⥤ D`, we need `TwistedArrow C' ≅ W.Elements` for some `C'`.
But `TwistedArrow C'` is itself the category of elements of the hom-profunctor
`Hom_{C'} : C'ᵒᵖ × C' → Set`.

So this condition asks that `W` be (isomorphic to) the hom-profunctor of some
category. Not every profunctor is a hom-profunctor - a profunctor needs the
structure of a **promonad** (a monad in the bicategory of profunctors) to
correspond to some category's hom-functor. The variance obstruction is a
symptom of this deeper structural requirement.

The weighted cone/cocone approach (weightedWedgeElementsEquiv and
weightedCowedgeElementsEquiv) remains the canonical reduction. Reduction to
ordinary wedges requires the weight to be a hom-profunctor.
-/

end WeightedWedgeAsProfunctor

section ProfunctorDerivedWeight

/-!
## Weights Derived from Profunctors

When the weight functor `W : TwistedArrow C ⥤ Type v` is itself derived from
a profunctor via `profunctorOnTwistedArrow`, the category of elements has
a richer structure that may avoid the variance obstruction.

For a profunctor `Q : Cᵒᵖ ⥤ C ⥤ Type v`, define:
  `W := profunctorOnTwistedArrow C Q : TwistedArrow C ⥤ Type v`

Then `W.Elements` has objects `(tw, q)` where:
  - `tw : TwistedArrow C` is a morphism `f : A ⟶ B` in C
  - `q : Q.obj (op B).obj A` is an element at the (source, target) pair

The morphisms in `W.Elements` are pairs `(m, hq)` where:
  - `m : tw₁ ⟶ tw₂` in TwistedArrow C
  - `hq : W.map m q₁ = q₂`, i.e., the profunctor action preserves elements

The profunctor action `W.map m = (profunctorOnTwistedArrow C Q).map m` is:
  `Q.map (twCodArr m).op .app (twDom tw₂) ≫ Q.obj (op (twCod tw₂)).map (twDomArr m)`

This combines both the contravariant and covariant actions of Q in a way that
respects the twisted arrow structure.

The question is: does `W.Elements` have a structure compatible with ordinary
wedges, avoiding the variance obstruction?
-/

variable {C : Type u} [Category.{v} C]

/-- When `W = profunctorOnTwistedArrow C Q`, the category of elements consists of
twisted arrows paired with elements of Q at the corresponding positions. -/
abbrev profunctorTwArrElements (Q : Cᵒᵖ ⥤ C ⥤ Type v) :=
  (profunctorOnTwistedArrow C Q).Elements

/-- An object of `profunctorTwArrElements Q` consists of a twisted arrow
`f : A ⟶ B` and an element `q : Q.obj (op A).obj B`.

For `twObjMk f` where `f : A ⟶ B`, we have `twDom = A` and `twCod = B`,
so the profunctor evaluates to `(Q.obj (op A)).obj B`. -/
def profunctorTwArrElements.mk (Q : Cᵒᵖ ⥤ C ⥤ Type v)
    {A B : C} (f : A ⟶ B) (q : (Q.obj (Opposite.op A)).obj B) :
    profunctorTwArrElements Q :=
  ⟨twObjMk f, q⟩

/-- The underlying twisted arrow of an element. -/
def profunctorTwArrElements.tw (Q : Cᵒᵖ ⥤ C ⥤ Type v)
    (x : profunctorTwArrElements Q) : TwistedArrow C :=
  x.fst

/-- The element component. For a twisted arrow `tw`, the element type is
`(Q.obj (op (twDom tw))).obj (twCod tw)`. -/
def profunctorTwArrElements.elem (Q : Cᵒᵖ ⥤ C ⥤ Type v)
    (x : profunctorTwArrElements Q) :
    (Q.obj (Opposite.op (twDom x.fst))).obj (twCod x.fst) :=
  x.snd

/-!
### Variance Analysis for `profunctorTwArrElements`

For a morphism `m : tw₁ ⟶ tw₂` in `TwistedArrow C`, the induced morphism
`(m, hq) : (tw₁, q₁) ⟶ (tw₂, q₂)` in `profunctorTwArrElements Q` satisfies
the condition `(profunctorOnTwistedArrow C Q).map m q₁ = q₂`.

Expanding `profunctorOnTwistedArrow C Q .map m`:
  `(Q.map (twCodArr m).op).app (twDom tw₂) ≫ (Q.obj (op (twCod tw₂))).map (twDomArr m)`

For the diagonal case where `tw₁ = tw₂ = twObjMk (𝟙 A)`:
- `twDom = A`, `twCod = A`
- A morphism to itself requires `twDomArr m : A ⟶ A` and `twCodArr m : A ⟶ A`
  with the twisted arrow coherence condition

`profunctorTwArrElements Q` naturally incorporates both the twisted arrow
structure AND the profunctor structure, potentially allowing a more direct
relationship with ordinary wedges.

However, for expressing weighted wedges as ordinary wedges over a profunctor
on `profunctorTwArrElements Q`, we still need to define a profunctor
`P' : (profunctorTwArrElements Q)ᵒᵖ ⥤ profunctorTwArrElements Q ⥤ D`
with the correct variance.

The investigation continues in the analysis below.
-/

/-!
### Dual: Profunctor-Derived Weight for Co-Twisted Arrows

For weighted cowedges, we use `profunctorOnCoTwistedArrow C Q` where
`Q : Cᵒᵖ ⥤ C ⥤ Type v` is a profunctor to Type. This gives us a copresheaf
`profunctorOnCoTwistedArrow C Q : CoTwistedArrow C ⥤ Type v`.

To get a presheaf (for weighted cowedge weights), we compose with `op`:
`(profunctorOnCoTwistedArrow C Q).op : (CoTwistedArrow C)ᵒᵖ ⥤ Type v`.

The category of elements of this presheaf is
`(profunctorOnCoTwistedArrow C Q).op.ElementsPre ≅ (profunctorOnCoTwistedArrow C Q).Elements`.
-/

/-- When `Q : Cᵒᵖ ⥤ C ⥤ Type v`, the category of elements of
`profunctorOnCoTwistedArrow C Q` consists of co-twisted arrows paired with
elements of Q at the corresponding positions. -/
abbrev profunctorCoTwArrElements (Q : Cᵒᵖ ⥤ C ⥤ Type v) :=
  (profunctorOnCoTwistedArrow C Q).Elements

/-- An object of `profunctorCoTwArrElements Q` consists of a co-twisted arrow
`(dom, cod, f : cod ⟶ dom)` and an element `q : Q.obj (op dom).obj cod`.

For `coTwObjMk g` where `g : A ⟶ B`, we have `coTwDom = B` (target of g) and
`coTwCod = A` (source of g), so the profunctor evaluates to
`(Q.obj (op B)).obj A`. -/
def profunctorCoTwArrElements.mk (Q : Cᵒᵖ ⥤ C ⥤ Type v)
    {A B : C} (g : A ⟶ B) (q : (Q.obj (Opposite.op B)).obj A) :
    profunctorCoTwArrElements Q :=
  ⟨coTwObjMk g, q⟩

/-- The underlying co-twisted arrow of an element. -/
def profunctorCoTwArrElements.coTw (Q : Cᵒᵖ ⥤ C ⥤ Type v)
    (x : profunctorCoTwArrElements Q) : CoTwistedArrow C :=
  x.fst

/-- The element component. For a co-twisted arrow `tw`, the element type is
`(Q.obj (op (coTwDom tw))).obj (coTwCod tw)`. -/
def profunctorCoTwArrElements.elem (Q : Cᵒᵖ ⥤ C ⥤ Type v)
    (x : profunctorCoTwArrElements Q) :
    (Q.obj (Opposite.op (coTwDom x.fst))).obj (coTwCod x.fst) :=
  x.snd

/-!
### Diagonal Elements in Profunctor-Derived Weights

For a profunctor `Q : Cᵒᵖ ⥤ C ⥤ Type v`, the diagonal elements of
`profunctorOnTwistedArrow C Q` at `twObjMk (𝟙 A)` are exactly `diagApp Q A`:

- `(profunctorOnTwistedArrow C Q).obj (twObjMk (𝟙 A))`
- `= (Q.obj (op (twDom (twObjMk (𝟙 A))))).obj (twCod (twObjMk (𝟙 A)))`
- `= (Q.obj (op A)).obj A`
- `= diagApp Q A`

Similarly for co-twisted arrows:
- `(profunctorOnCoTwistedArrow C Q).obj (coTwObjMk (𝟙 A))`
- `= (Q.obj (op (coTwDom (coTwObjMk (𝟙 A))))).obj (coTwCod (coTwObjMk (𝟙 A)))`
- `= (Q.obj (op A)).obj A`
- `= diagApp Q A`

This gives a direct correspondence between diagonal elements of
profunctor-derived weights and diagonal elements of the profunctor itself.
-/

/-- The diagonal element type of `profunctorOnTwistedArrow C Q` at the
identity twisted arrow equals `diagApp Q A`. -/
@[simp]
lemma profunctorOnTwistedArrow_diagElem (Q : Cᵒᵖ ⥤ C ⥤ Type v) (A : C) :
    (profunctorOnTwistedArrow C Q).obj (twObjMk (𝟙 A)) = diagApp Q A := rfl

/-- The diagonal element type of `profunctorOnCoTwistedArrow C Q` at the
identity co-twisted arrow equals `diagApp Q A`. -/
@[simp]
lemma profunctorOnCoTwistedArrow_diagElem (Q : Cᵒᵖ ⥤ C ⥤ Type v) (A : C) :
    (profunctorOnCoTwistedArrow C Q).obj (coTwObjMk (𝟙 A)) = diagApp Q A := rfl

/-!
### Morphisms in Profunctor-Derived Element Categories

A morphism in `profunctorTwArrElements Q` from `(tw₁, q₁)` to `(tw₂, q₂)`
consists of:
- A twisted arrow morphism `m : tw₁ ⟶ tw₂`
- A proof that `(profunctorOnTwistedArrow C Q).map m q₁ = q₂`

The profunctor map `(profunctorOnTwistedArrow C Q).map m` is:
```
(Q.map (twDomArr m).op).app (twCod tw₂) ≫ (Q.obj (op (twDom tw₂))).map (twCodArr m)
```

This combines the contravariant action of Q (via `twDomArr m`) with the
covariant action (via `twCodArr m`).

For diagonal-to-diagonal morphisms `m : twObjMk (𝟙 A) ⟶ twObjMk (𝟙 B)`:
- `twDomArr m : A ⟶ B` and `twCodArr m : A ⟶ B`
- The coherence condition forces `twDomArr m = twCodArr m`
- So `m` is determined by a single morphism `f : A ⟶ B` in C

The profunctor map becomes:
```
(Q.map f.op).app B ≫ (Q.obj (op B)).map f : diagApp Q A → diagApp Q B
```

This is exactly the `DiagCompat` condition: `d₁` and `d₂` are related if
`(Q.obj (op A)).map f d₁ = (Q.map f.op).app B d₂`.

Therefore, morphisms between diagonal elements in `profunctorTwArrElements Q`
correspond exactly to `DiagCompat` pairs in Q.
-/

/-!
### Variance Obstruction for Diagonal Twisted Arrows

A morphism `m : twObjMk (𝟙 A) ⟶ twObjMk (𝟙 B)` in `TwistedArrow C` requires:
- `twDomArr m : B ⟶ A` (domain arrow goes backwards)
- `twCodArr m : A ⟶ B` (codomain arrow goes forwards)
- Coherence: `twDomArr m ≫ 𝟙 A ≫ twCodArr m = 𝟙 B`

The coherence condition simplifies to `twDomArr m ≫ twCodArr m = 𝟙 B`,
requiring `twDomArr m` and `twCodArr m` to form a retraction/section pair.

This is equivalent to having an isomorphism when both compositions are
identities (i.e., `twCodArr m ≫ twDomArr m = 𝟙 A` as well).

Therefore, morphisms between diagonal twisted arrows correspond to
*isomorphisms* in C, not arbitrary morphisms. This is the same variance
obstruction seen in the weighted cowedge embedding analysis.
-/

/-- For the profunctor-derived weight, a morphism between diagonal twisted
arrows requires an isomorphism in C. Given `i : A ≅ B`, we can form a
twisted arrow morphism with `twDomArr = i.inv` and `twCodArr = i.hom`. -/
def diagTwArrMorphismOfIso {A B : C} (i : A ≅ B) :
    twObjMk (𝟙 A) ⟶ twObjMk (𝟙 B) :=
  twHomMk i.inv i.hom (by
    simp only [twObjMk_arr, twObjMk_dom, twObjMk_cod, Category.id_comp, Iso.inv_hom_id])

@[simp]
lemma diagTwArrMorphismOfIso_domArr {A B : C} (i : A ≅ B) :
    twDomArr (diagTwArrMorphismOfIso i) = i.inv := rfl

@[simp]
lemma diagTwArrMorphismOfIso_codArr {A B : C} (i : A ≅ B) :
    twCodArr (diagTwArrMorphismOfIso i) = i.hom := rfl

/-- The profunctor map along a diagonal twisted arrow morphism from an iso.

For `i : A ≅ B`, the formula is:
`(Q.map i.inv.op).app A ≫ (Q.obj (op B)).map i.hom : diagApp Q A ⟶ diagApp Q B`
-/
theorem profunctorOnTwistedArrow_map_diagIso (Q : Cᵒᵖ ⥤ C ⥤ Type v) {A B : C}
    (i : A ≅ B) :
    (profunctorOnTwistedArrow C Q).map (diagTwArrMorphismOfIso i) =
      (Q.map i.inv.op).app A ≫ (Q.obj (Opposite.op B)).map i.hom := by
  simp only [profunctorOnTwistedArrow_map, diagTwArrMorphismOfIso_domArr,
    diagTwArrMorphismOfIso_codArr, twObjMk_cod, twObjMk_dom]

/-!
### Relationship to Paranaturality (Groupoid Case)

When C is a groupoid (all morphisms are isomorphisms), the variance
obstruction disappears. In this case, for any morphism `f : A ⟶ B` in C,
we can form a twisted arrow morphism between the diagonals:

```
diagTwArrMorphismOfIso (asIso f) : twObjMk (𝟙 A) ⟶ twObjMk (𝟙 B)
```

The profunctor map condition becomes: `(Q.map f⁻¹.op).app B ≫ (Q.obj (op B)).map f`

This relates to `DiagCompat` but with the inverse morphism involved.

For a general category C, morphisms in `profunctorTwArrElements Q` between
diagonal elements only exist along isomorphisms, so the paranaturality
relation only holds along isomorphisms (consistent with our earlier finding).

### Summary: Profunctor-Derived Weight Approach

The question was whether using `(profunctorOnTwistedArrow W).Elements` or
`(profunctorOnCoTwistedArrow W).ElementsPre` as the domain category (instead
of `W.Elements`) could avoid the variance obstruction when expressing weighted
wedges/cowedges as ordinary wedges/cowedges.

**Finding**: The variance obstruction persists.

For `profunctorTwArrElements Q`:
- Diagonal elements at `twObjMk (𝟙 A)` correspond to `diagApp Q A`
- Morphisms between diagonals require isomorphisms in C (not arbitrary morphisms)
- The coherence condition `twDomArr ≫ twArr x ≫ twCodArr = twArr y` forces
  `twDomArr` and `twCodArr` to form a retraction/section pair

The same holds dually for `profunctorCoTwArrElements Q`.

**Conclusion**: The profunctor-derived weight approach does not circumvent the
variance obstruction. Weighted wedges/cowedges over general profunctors cannot
be expressed as ordinary wedges/cowedges over an induced presheaf/copresheaf
on the category of elements, except when restricted to isomorphisms (groupoids).

This matches the result from the direct weighted cowedge embedding analysis:
the embedding `StrongResCowedge G c → Cowedge (sliceQ G c) c` requires the
restricted cowedge structure where morphisms only exist along isomorphisms.
-/

end ProfunctorDerivedWeight

section TwCoprArrElemApproach

/-!
## Alternative: Diagonal Elements Category (TwCoprArrElem)

An alternative approach to expressing weighted wedges as ordinary wedges uses
`TwCoprArrElem W` from `Paranatural.lean` - the category of diagonal elements
with compatibility conditions - instead of `W.Elements`.

### The Setup

For a weight `W : TwistedArrow C ⥤ Type v`, `TwCoprArrElem W` has:
- Objects: pairs `(arr : Arrow C, elem : W.obj(arrToTw' arr))`
- Morphisms: `φ : arr₁ → arr₂` satisfying **diagonal compatibility**:
  `W.map(arrToDiagFromSource φ) e₁ = W.map(arrToDiagFromTarget φ) e₂`

The diagonal compatibility condition says that the two ways to transport an
element along an arrow morphism (via source and via target) must agree.

### Proposed Profunctor on TwCoprArrElem

Given `P : Cᵒᵖ ⥤ C ⥤ D`, define `Q : (TwCoprArrElem W)ᵒᵖ ⥤ TwCoprArrElem W ⥤ D`:
  `Q((arr₁, w₁), (arr₂, w₂)) = P(arr₁.right, arr₂.left)`

This is functorial because it factors through the forgetful functor to `Arrow C`:
- Contravariant: `P.map(f.base.right.op)` gives `P(arr₂.right, _) → P(arr₁.right, _)`
- Covariant: `(P.obj _).map(g.base.left)` gives `P(_, arr₂.left) → P(_, arr₃.left)`

On the diagonal: `Q((arr, w), (arr, w)) = P(twDom(arrToTw' arr), twCod(arrToTw' arr))`
matching the weighted wedge target types.

### Analysis

The diagonal compatibility in `TwCoprArrElem W` is a RESTRICTION on morphisms,
not a condition wedges must satisfy. In contrast, `W.Elements` has a morphism
`(tw₁, w₁) → (tw₂, W.map g w₁)` for every twisted arrow morphism `g`.

Weighted wedge naturality requires conditions for ALL twisted arrow morphisms.
Wedge paranaturality over `Q` only requires conditions for diagonal-compatible
morphisms. Since diagonal-compatible morphisms form a subset:

  Wedges over Q impose FEWER conditions than weighted wedges.

This gives an inclusion `WeightedWedge W P → Wedge Q` (every weighted wedge
induces a wedge over Q), but NOT an equivalence. A wedge over Q lacks the full
naturality required by weighted wedges.

### Connection to diagElemIdentityTwCoprEquiv

The equivalence `DiagElem P ≌ IdentityTwCoprArrElem P` shows diagonal profunctor
elements correspond to identity-arrow elements. For wedges, diagonal evaluation
corresponds to identity arrows. However, `TwCoprArrElem W` includes ALL arrows,
not just identities, so the restriction of morphisms still causes the mismatch.

### Conclusion

The `TwCoprArrElem` approach does not yield an equivalence with weighted wedges.
It provides only a forgetful/inclusion functor. The diagonal compatibility
condition restricts morphisms too much - we lose the full naturality conditions
that weighted wedges require.
-/

end TwCoprArrElemApproach

section RestrictedCowedges

/-!
## Slice profunctor

Given an endodifunctor `G : Cᵒᵖ ⥤ C ⥤ C` and an object `c : C`, we define
the *slice profunctor* `G ⇓ c : Cᵒᵖ ⥤ C ⥤ Type` by `(G ⇓ c)(A, B) := Hom(G(B, A), c)`.

Note the argument swap: `G(B, A)` not `G(A, B)`. This ensures the correct
variance for an endoprofunctor to Type.
-/

variable {C : Type u} [Category.{v} C]

/-- The slice profunctor `G ⇓ c` for an endodifunctor `G : Cᵒᵖ ⥤ C ⥤ C` and
object `c : C`. Defined as `(G ⇓ c)(A, B) := Hom_C(G(B, A), c)`.

The covariant action (second argument): for `g : X → Y`, the map
`Hom(G(X, A), c) → Hom(G(Y, A), c)` is precomposition by `G(g, A) : G(Y, A) → G(X, A)`.

The contravariant action (first argument): for `f : A → B`, the map
`Hom(G(X, B), c) → Hom(G(X, A), c)` is precomposition by `G(X, f) : G(X, A) → G(X, B)`.
-/
def sliceProfunctor (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) : Cᵒᵖ ⥤ C ⥤ Type v where
  obj A :=
    { obj := fun X => (G.obj (Opposite.op X)).obj A.unop ⟶ c
      map := fun g m => (G.map g.op).app A.unop ≫ m
      map_id := fun X => by
        funext m
        simp only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp, types_id_apply]
      map_comp := fun f g => by
        funext m
        simp only [op_comp, Functor.map_comp, NatTrans.comp_app, Category.assoc, types_comp_apply] }
  map f :=
    { app := fun X m => (G.obj (Opposite.op X)).map f.unop ≫ m
      naturality := fun X Y g => by
        funext m
        simp only [types_comp_apply]
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        exact (G.map g.op).naturality f.unop }
  map_id := fun A => by
    ext X m
    simp only [unop_id, Functor.map_id, Category.id_comp, NatTrans.id_app, types_id_apply]
  map_comp := fun f g => by
    ext X m
    simp only [unop_comp, Functor.map_comp, Category.assoc, NatTrans.comp_app, types_comp_apply]

/-- Notation for the slice profunctor. -/
scoped infixl:70 " ⇓ " => sliceProfunctor

/-- The slice profunctor construction is itself functorial in `c : C`.
Given `G : Cᵒᵖ ⥤ C ⥤ C`, this defines a functor `C ⥤ (Cᵒᵖ ⥤ C ⥤ Type v)`.

For a morphism `f : c ⟶ c'`, the induced natural transformation
`(G ⇓ c) ⟶ (G ⇓ c')` acts by post-composition with `f`. -/
def sliceProfunctorFunctor (G : Cᵒᵖ ⥤ C ⥤ C) : C ⥤ (Cᵒᵖ ⥤ C ⥤ Type v) where
  obj c := G ⇓ c
  map f :=
    { app := fun A =>
        { app := fun X m => m ≫ f
          naturality := fun X Y g => by
            funext m
            simp only [types_comp_apply, sliceProfunctor, Category.assoc] }
      naturality := fun A B g => by
        ext X m
        simp only [FunctorToTypes.comp, sliceProfunctor, Category.assoc] }
  map_id c := by
    ext A X m
    simp only [Category.comp_id, NatTrans.id_app, types_id_apply]
  map_comp f g := by
    ext A X m
    simp only [FunctorToTypes.comp, Category.assoc, NatTrans.comp_app]

/-- `sliceProfunctor G c` equals the application of `sliceProfunctorFunctor G` at `c`. -/
theorem sliceProfunctor_eq_functor_obj (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) :
    sliceProfunctor G c = (sliceProfunctorFunctor G).obj c := rfl

/-- Given a natural transformation `β : G' ⟹ G`, precomposition induces a natural
transformation `(G ⇓ c) ⟶ (G' ⇓ c)` for each `c`.

At component `(A, B)`, the map `Hom(G(B, A), c) → Hom(G'(B, A), c)` is
precomposition by `(β.app (op B)).app A : G'(B, A) → G(B, A)`. -/
def sliceProfunctorPrecomp {G G' : Cᵒᵖ ⥤ C ⥤ C} (β : G' ⟶ G) (c : C) :
    (G ⇓ c) ⟶ (G' ⇓ c) where
  app A :=
    { app := fun X m => (β.app (Opposite.op X)).app A.unop ≫ m
      naturality := fun X Y g => by
        funext m
        simp only [types_comp_apply, sliceProfunctor]
        -- Goal: β.app (op Y) .app A ≫ G'.map g.op .app A ≫ m
        --     = G.map g.op .app A ≫ β.app (op X) .app A ≫ m
        rw [← Category.assoc, ← Category.assoc]
        congr 1
        -- Need: β.app (op Y) .app A ≫ G'.map g.op .app A
        --     = G.map g.op .app A ≫ β.app (op X) .app A
        -- This is (β.naturality g.op) applied at component A
        exact congrFun (congrArg NatTrans.app (β.naturality g.op).symm) A.unop }
  naturality A B f := by
    ext X m
    simp only [FunctorToTypes.comp, sliceProfunctor]
    -- Goal: β.app (op X) .app B ≫ G'.obj (op X) .map f ≫ m
    --     = G.obj (op X) .map f ≫ β.app (op X) .app A ≫ m
    rw [← Category.assoc, ← Category.assoc]
    congr 1
    -- Need: (β.app (op X)).app B ≫ G'.obj.map f = G.obj.map f ≫ (β.app (op X)).app A
    exact ((β.app (Opposite.op X)).naturality f.unop).symm

/-- Precomposition by the identity is the identity. -/
theorem sliceProfunctorPrecomp_id (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) :
    sliceProfunctorPrecomp (𝟙 G) c = 𝟙 (G ⇓ c) := by
  ext A X m
  simp only [sliceProfunctorPrecomp, NatTrans.id_app, Category.id_comp, types_id_apply]

/-- Precomposition respects composition (contravariantly). -/
theorem sliceProfunctorPrecomp_comp {G G' G'' : Cᵒᵖ ⥤ C ⥤ C}
    (β : G' ⟶ G) (γ : G'' ⟶ G') (c : C) :
    sliceProfunctorPrecomp (γ ≫ β) c =
    sliceProfunctorPrecomp β c ≫ sliceProfunctorPrecomp γ c := by
  ext A X m
  simp only [sliceProfunctorPrecomp, NatTrans.comp_app, Category.assoc, types_comp_apply]

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
  ext A X m
  simp only [sliceProfunctorPrecomp, sliceProfunctorFunctor, NatTrans.comp_app,
    types_comp_apply, Category.assoc]

/-- The slice profunctor construction is bifunctorial: contravariant in `G` and
covariant in `c`.

This functor `(Cᵒᵖ ⥤ C ⥤ C)ᵒᵖ ⥤ C ⥤ (Cᵒᵖ ⥤ C ⥤ Type v)` sends:
- Objects: `op G ↦ (c ↦ G ⇓ c)`, i.e., `sliceProfunctorFunctor G`
- Morphisms: a morphism `op G → op G'` (i.e., `β : G' ⟹ G`) induces precomposition -/
def sliceProfunctorBifunctor : (Cᵒᵖ ⥤ C ⥤ C)ᵒᵖ ⥤ C ⥤ (Cᵒᵖ ⥤ C ⥤ Type v) where
  obj opG := sliceProfunctorFunctor opG.unop
  map {opG opG'} β :=
    -- β : opG ⟶ opG' in the opposite category, i.e., β.unop : G' ⟶ G
    { app := fun c => sliceProfunctorPrecomp β.unop c
      naturality := fun c c' f => (sliceProfunctorPrecomp_natural β.unop f).symm }
  map_id opG := by
    ext c A X m
    simp only [unop_id, sliceProfunctorPrecomp, NatTrans.id_app, Category.id_comp,
      types_id_apply]
  map_comp {opG opG' opG''} β γ := by
    ext c A X m
    simp only [unop_comp, sliceProfunctorPrecomp, NatTrans.comp_app, Category.assoc,
      types_comp_apply]

/-- The slice profunctor at `G` and `c` equals the bifunctor applied to `op G` and `c`. -/
theorem sliceProfunctor_eq_bifunctor (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) :
    G ⇓ c = (sliceProfunctorBifunctor.obj (Opposite.op G)).obj c := rfl

/-- The diagonal of the slice profunctor at `A` is `Hom(G(A, A), c)`. -/
theorem sliceProfunctor_diagApp (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) (A : C) :
    diagApp (G ⇓ c) A = ((G.obj (Opposite.op A)).obj A ⟶ c) := by
  simp only [diagApp, sliceProfunctor, Opposite.unop_op]

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
restriction functor `H : Cᵒᵖ ⥤ C ⥤ Type v`.

This consists of a carrier object and a dinatural transformation from `H` to
the slice profunctor `G ⇓ pt`.

The universe of `H` is `v` (the morphism universe) to match the slice profunctor
`G ⇓ pt : Cᵒᵖ ⥤ C ⥤ Type v`. -/
structure RestrictedCowedge (G : Cᵒᵖ ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ Type v) where
  /-- The carrier (summit) object. -/
  pt : C
  /-- The family of morphisms as a `ParanatSig H (G ⇓ pt)`. -/
  family : ParanatSig H (G ⇓ pt)
  /-- The dinaturality condition on the family. -/
  isDinatural : IsDinatural H (G ⇓ pt) family

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
  family := α.app
  isDinatural := α.dinatural

namespace RestrictedCowedge

variable {G : Cᵒᵖ ⥤ C ⥤ C} {H : Cᵒᵖ ⥤ C ⥤ Type v}

/-- The explicit dinaturality equation: for `g : A → B` and `x : H(B, A)`,
the two paths from `G(B, A)` to `pt` agree. -/
theorem dinaturality' (c : RestrictedCowedge G H) {A B : C} (g : A ⟶ B)
    (x : (H.obj (Opposite.op B)).obj A) :
    (G.map g.op).app A ≫ c.family A ((H.map g.op).app A x) =
    (G.obj (Opposite.op B)).map g ≫ c.family B ((H.obj (Opposite.op B)).map g x) := by
  have dinat := c.isDinatural A B g x
  simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor] at dinat
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
An `H`-restricted `G`-cowedge with the paranaturality condition.

This is the "strong" version of a restricted cowedge, where the family
satisfies the full paranaturality condition rather than just dinaturality.

Structure:
- `pt : C` - the carrier (summit) object
- `family : ParanatSig H (G ⇓ pt)` - the family of morphisms
- `isParanatural : IsParanatural H (G ⇓ pt) family` - the paranaturality condition
-/
structure StrongRestrictedCowedge (G : Cᵒᵖ ⥤ C ⥤ C) (H : Cᵒᵖ ⥤ C ⥤ Type v) where
  /-- The carrier (summit) object. -/
  pt : C
  /-- The family of morphisms as a `ParanatSig H (G ⇓ pt)`. -/
  family : ParanatSig H (G ⇓ pt)
  /-- The paranaturality condition on the family. -/
  isParanatural : IsParanatural H (G ⇓ pt) family

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
  family := α.app
  isParanatural := α.paranatural

/-- Every strong restricted cowedge is a restricted cowedge, since paranaturality
implies dinaturality. -/
def StrongRestrictedCowedge.toRestrictedCowedge {G : Cᵒᵖ ⥤ C ⥤ C}
    {H : Cᵒᵖ ⥤ C ⥤ Type v} (c : StrongRestrictedCowedge G H) :
    RestrictedCowedge G H where
  pt := c.pt
  family := c.family
  isDinatural := paranatural_implies_dinatural H (G ⇓ c.pt) c.family c.isParanatural

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
  simp only [DiagCompat, sliceProfunctor, Opposite.unop_op]
  constructor
  · intro h
    have : ((G ⇓ c).obj (Opposite.op A)).map f m₀ =
           ((G ⇓ c).map f.op).app B m₁ := h
    simp only [sliceProfunctor] at this
    exact this
  · intro h
    exact h

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

/-- Given a weighted cowedge over an endoprofunctor `P`, extract the family
of morphisms at diagonal twisted arrows.

For `A : C` and `w : weightDiagElem W A`, this gives:
`(P.obj (op A)).obj A ⟶ pt`

This matches the signature required for `ParanatSig H (P ⇓ pt)` when we take
`diagApp H A = weightDiagElem W A`. -/
def WeightedCowedge.diagFamily {W : (TwistedArrow C)ᵒᵖ ⥤ Type v}
    {P : Cᵒᵖ ⥤ C ⥤ C} (c : WeightedCowedge W P) (A : C)
    (w : weightDiagElem W A) : (P.obj (Opposite.op A)).obj A ⟶ c.pt :=
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
### Variance Obstruction for Diagonal Restriction

To embed weighted cowedges into strong restricted cowedges, we need to define
a profunctor `H : Cᵒᵖ ⥤ C ⥤ Type v` from a weight `W : (CoTwistedArrow C)ᵒᵖ ⥤ Type v`
such that `diagApp H A = weightDiagElem W A`.

We could define `H.obj (op A).obj B := W.obj (op (diagCoTwArr A))`,
constant in the second argument `B`. For this to be functorial in the first
argument, we need:

For `f : A' ⟶ A` (so `f.op : op A ⟶ op A'`), define:
  `(H.map f.op).app B : H.obj (op A).obj B → H.obj (op A').obj B`
  = `W.obj (op (diagCoTwArr A)) → W.obj (op (diagCoTwArr A'))`

This requires a morphism `W.map m.op` for some `m : diagCoTwArr A' ⟶ diagCoTwArr A`
in `CoTwistedArrow C`.

A morphism `m : diagCoTwArr A' ⟶ diagCoTwArr A` consists of:
- `l : coTwDom (diagCoTwArr A) ⟶ coTwDom (diagCoTwArr A') = A ⟶ A'`
- `r : coTwCod (diagCoTwArr A') ⟶ coTwCod (diagCoTwArr A) = A' ⟶ A`
- Compatibility: `l ≫ coTwArr (diagCoTwArr A') = coTwArr (diagCoTwArr A) ≫ r`
  which simplifies to `l ≫ 𝟙 A' = 𝟙 A ≫ r`, i.e., `l = r`

Since `l : A ⟶ A'` and `r : A' ⟶ A` must satisfy `l = r`, we need `A ≅ A'`
with `l` and `r` being inverse isomorphisms.

This variance obstruction means that a profunctor `H` with the required
diagonal elements can only have non-trivial functorial structure when the
relevant objects are connected by isomorphisms in `C`.
-/

/-- A co-twisted arrow morphism between diagonal co-twisted arrows
`diagCoTwArr A ⟶ diagCoTwArr B` requires both a morphism `B ⟶ A` (for the
domain) and `A ⟶ B` (for the codomain) that are equal. This means
`A` and `B` must be isomorphic. -/
def diagCoTwArrHomOfIso {A B : C} (i : A ≅ B) :
    diagCoTwArr A ⟶ diagCoTwArr B :=
  coTwHomMk i.inv i.hom (by simp)

@[simp]
lemma diagCoTwArrHomOfIso_domArr {A B : C} (i : A ≅ B) :
    coTwDomArr (diagCoTwArrHomOfIso i) = i.inv := rfl

@[simp]
lemma diagCoTwArrHomOfIso_codArr {A B : C} (i : A ≅ B) :
    coTwCodArr (diagCoTwArrHomOfIso i) = i.hom := rfl

/-- The restriction of a weight functor along an isomorphism between objects.
Given `W : (TwistedArrow C)ᵒᵖ ⥤ Type v` and an isomorphism `i : A ≅ B`,
this transports elements from `weightDiagElem W B` to `weightDiagElem W A`. -/
def weightDiagTransport (W : (TwistedArrow C)ᵒᵖ ⥤ Type v) {A B : C} (i : A ≅ B) :
    weightDiagElem W B → weightDiagElem W A :=
  W.map (diagTwArrMorphismOfIso i).op

/-!
### Trivial Profunctor Case

When we use the constant profunctor `constProfunctor T`, the `DiagCompat`
condition becomes equality: `DiagCompat (constProfunctor T) I₀ I₁ f d₀ d₁`
holds iff `d₀ = d₁`.

This is because both the covariant and contravariant actions are identities:
- `(constProfunctor T).obj (op I₀).map f = 𝟙`
- `((constProfunctor T).map f.op).app I₁ = 𝟙`

With this trivial H, the paranaturality condition becomes: for equal input
elements, the output elements must satisfy `DiagCompat` in `G ⇓ pt`.
-/

/-- The covariant action of the constant profunctor is the identity. -/
@[simp]
lemma constProfunctor_map_cov (T : Type v) (A : Cᵒᵖ) {X Y : C} (f : X ⟶ Y) :
    ((constProfunctor (C := C) T).obj A).map f = id := rfl

/-- The contravariant action of the constant profunctor is the identity. -/
@[simp]
lemma constProfunctor_map_con (T : Type v) {A B : Cᵒᵖ} (g : A ⟶ B) (X : C) :
    ((constProfunctor (C := C) T).map g).app X = id := rfl

/-- `DiagCompat` for the constant profunctor reduces to equality. -/
theorem constProfunctor_diagCompat_iff_eq (T : Type v) (I₀ I₁ : C) (f : I₀ ⟶ I₁)
    (d₀ d₁ : T) :
    DiagCompat (constProfunctor (C := C) T) I₀ I₁ f d₀ d₁ ↔ d₀ = d₁ := by
  simp [DiagCompat]

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

/-- Extract the diagonal family signature from a weighted cowedge.
This gives a `ParanatSig` where the source profunctor `H` has
`diagApp H A = weightDiagElem W A`. -/
def WeightedCowedge.diagFamilySig {W : (TwistedArrow C)ᵒᵖ ⥤ Type v}
    {P : Cᵒᵖ ⥤ C ⥤ C} (c : WeightedCowedge W P) :
    (A : C) → weightDiagElem W A → diagApp (P ⇓ c.pt) A :=
  fun A w => c.leg (diagTwArr A) w

/-- The diagonal family signature equals the leg applied at diagonal twisted
arrows. -/
@[simp]
theorem WeightedCowedge.diagFamilySig_eq {W : (TwistedArrow C)ᵒᵖ ⥤ Type v}
    {P : Cᵒᵖ ⥤ C ⥤ C} (c : WeightedCowedge W P) (A : C) (w : weightDiagElem W A) :
    c.diagFamilySig A w = c.leg (diagTwArr A) w := rfl

/-!
### Paranaturality Along Isomorphisms

The weighted cowedge naturality condition implies that the diagonal family
satisfies paranaturality along isomorphisms. Specifically, for an isomorphism
`i : A ≅ B` and elements `wA : weightDiagElem W A`, `wB : weightDiagElem W B`
that are related via `W.map (diagTwArrMorphismOfIso i.symm).op`, the corresponding
legs satisfy the slice profunctor `DiagCompat` condition along `i.hom`.

This is a partial result: full paranaturality would require this condition
along ALL morphisms, but weighted cowedge structure only provides it along
isomorphisms.
-/

/-- The naturality condition for weighted cowedges along a twisted arrow
morphism `m : α ⟶ β` states that transporting via `W.map m.op` and then
taking the leg at `α` equals the leg at `β` precomposed with the profunctor
action. -/
theorem WeightedCowedge.naturality_at {W : (TwistedArrow C)ᵒᵖ ⥤ Type v}
    {P : Cᵒᵖ ⥤ C ⥤ C} (c : WeightedCowedge W P) {α β : TwistedArrow C}
    (m : α ⟶ β) (wβ : W.obj (Opposite.op β)) :
    (profunctorOnTwistedArrow C P).map m ≫ c.leg β wβ =
      c.leg α (W.map m.op wβ) :=
  c.naturality m wβ

/-!
### Paranaturality Along Isomorphisms: Detailed Analysis

When we have an isomorphism `i : A ≅ B`, we can form a twisted arrow morphism
`diagTwArrMorphismOfIso i : diagTwArr A ⟶ diagTwArr B`. The weighted cowedge
naturality along this morphism gives:

```
(profunctorOnTwistedArrow C P).map (diagTwArrMorphismOfIso i) ≫ leg (diagTwArr B) wB
  = leg (diagTwArr A) (W.map (diagTwArrMorphismOfIso i).op wB)
```

The `profunctorOnTwistedArrow` morphism expands to:
```
P.map i.inv.op .app B ≫ (P.obj (op B)).map i.hom
```

This gives us a "paranaturality along isomorphisms" result.
-/

/-- The profunctor action between diagonal twisted arrows along an
isomorphism `i : A ≅ B`. This is the morphism
`(P.obj (op A)).obj A ⟶ (P.obj (op B)).obj B` obtained from the
twisted arrow morphism `diagTwArrMorphismOfIso i`. -/
def profunctorDiagIsoAction {P : Cᵒᵖ ⥤ C ⥤ C} {A B : C} (i : A ≅ B) :
    (P.obj (Opposite.op A)).obj A ⟶ (P.obj (Opposite.op B)).obj B :=
  (profunctorOnTwistedArrow C P).map (diagTwArrMorphismOfIso i)

/-- The profunctor diagonal action along an isomorphism factors through
the covariant and contravariant actions of the profunctor. -/
theorem profunctorDiagIsoAction_eq {P : Cᵒᵖ ⥤ C ⥤ C} {A B : C} (i : A ≅ B) :
    profunctorDiagIsoAction (P := P) i =
      (P.map i.inv.op).app A ≫ (P.obj (Opposite.op B)).map i.hom := by
  simp only [profunctorDiagIsoAction, profunctorOnTwistedArrow_map]
  rfl

/-- Weighted cowedge naturality along a diagonal isomorphism. For an isomorphism
`i : A ≅ B` and weight element `wB : weightDiagElem W B`, the diagram family
satisfies:

```
profunctorDiagIsoAction i ≫ diagFamilySig c B wB
  = diagFamilySig c A (weightDiagTransport W i wB)
```

This is the "paranaturality along isomorphisms" property. -/
theorem WeightedCowedge.diagFamilySig_iso_naturality
    {W : (TwistedArrow C)ᵒᵖ ⥤ Type v} {P : Cᵒᵖ ⥤ C ⥤ C}
    (c : WeightedCowedge W P) {A B : C} (i : A ≅ B)
    (wB : weightDiagElem W B) :
    profunctorDiagIsoAction (P := P) i ≫ c.diagFamilySig B wB =
      c.diagFamilySig A (weightDiagTransport W i wB) := by
  simp only [diagFamilySig, profunctorDiagIsoAction, weightDiagTransport]
  exact c.naturality_at (diagTwArrMorphismOfIso i) wB

/-!
### Trivial Profunctor Case Analysis

When we try to use `constProfunctor T` as the indexing profunctor `H`, we face
a fundamental type mismatch:

1. For weighted cowedges, the diagonal element type `weightDiagElem W A` varies
   with `A`. Different objects have different weight element types.

2. For `constProfunctor T`, the diagonal element type `diagApp (constProfunctor T) A = T`
   is the same for all objects.

For an embedding to exist via constant profunctors, we would need either:
- All `weightDiagElem W A` to be the same type T (requiring W to be constant on
  diagonal co-twisted arrows)
- Or a quotient/coproduct construction that collapses the varying types into one

The first is very restrictive. The second would lose the fine-grained
structure of the weighted cowedge.

### Groupoid Case

When C is a groupoid (all morphisms are isomorphisms), the variance obstruction
disappears. In this case:

1. Every morphism `f : A ⟶ B` has an inverse, so we can form co-twisted arrow
   morphisms between ANY diagonal co-twisted arrows.

2. The weight functor W can have non-trivial functorial structure on diagonal
   co-twisted arrows, allowing us to define a proper profunctor H.

3. The weighted cowedge naturality gives full paranaturality (not just along
   isomorphisms).

### Conclusion

The embedding `WeightedCowedgeCat W P ⥤ StrongRestrictedCowedgeCat P H` exists
in these cases:

1. **C is a groupoid**: The profunctor H can be defined functorially from W by
   using the isomorphism structure. Paranaturality follows from weighted
   cowedge naturality.

2. **W is constant on diagonal co-twisted arrows**: If `weightDiagElem W A = T`
   for all A, we can use `H = constProfunctor T`. However, the paranaturality
   condition in this case is very restrictive.

3. **Single-object category**: When C has only one object, there's effectively
   only one diagonal co-twisted arrow, so the variance obstruction disappears.

For general categories and weights, a direct embedding does not exist due to
the variance obstruction. The relationship between weighted cowedges and strong
restricted cowedges is more subtle and may require additional categorical
machinery (such as enrichment or fibered categories) to formalize properly.
-/

/-!
### Slice-Profunctor-Induced Weight

Instead of trying to derive a profunctor from an arbitrary weight, we consider
the reverse direction: given a slice profunctor `G ⇓ c`, define the induced
weight on co-twisted arrows.

For a co-twisted arrow `f : A ⟶ B`, the slice profunctor evaluates to:
`((G ⇓ c).obj (op A)).obj B = (G.obj (op B)).obj A ⟶ c`

We define `sliceWeight G c : (CoTwistedArrow C)ᵒᵖ ⥤ Type v` such that:
`sliceWeight G c .obj (op (coTwObjMk f)) = (G.obj (op B)).obj A ⟶ c`

For a morphism `m : x ⟶ y` in `CoTwistedArrow C`:
- `coTwDomArr m : coTwDom y ⟶ coTwDom x` (backwards)
- `coTwCodArr m : coTwCod x ⟶ coTwCod y` (forwards)

For `m : opSrc ⟶ opTgt` in `(CoTwistedArrow C)ᵒᵖ`, we have
`m.unop : opTgt.unop ⟶ opSrc.unop`, so:
- `coTwDomArr m.unop : coTwDom opSrc.unop ⟶ coTwDom opTgt.unop`
- `coTwCodArr m.unop : coTwCod opTgt.unop ⟶ coTwCod opSrc.unop`

The profunctor action on `G : Cᵒᵖ ⥤ C ⥤ C`:
- Contravariant in first arg: for `f : A ⟶ B`, `G.map f.op` goes `G(B,-) ⟶ G(A,-)`
- Covariant in second arg: for `g : X ⟶ Y`, `G(-).map g` goes `G(-,X) ⟶ G(-,Y)`

Applying to our morphism arrows:
- `G.map (coTwCodArr m.unop).op` gives `G(coTwCod opSrc,-) ⟶ G(coTwCod opTgt,-)`
- `G(-).map (coTwDomArr m.unop)` gives `G(-,coTwDom opSrc) ⟶ G(-,coTwDom opTgt)`

Combined: `G(coTwCod opSrc, coTwDom opSrc) ⟶ G(coTwCod opTgt, coTwDom opTgt)`

But for a presheaf `W : (CoTwistedArrow C)ᵒᵖ ⥤ Type v`, we need:
- `W.map m : W.obj opSrc → W.obj opTgt`
- i.e., `(G(coTwCod opSrc, coTwDom opSrc) ⟶ c) → (G(coTwCod opTgt, coTwDom opTgt) ⟶ c)`

Given `h : G(opSrc) ⟶ c` and the profunctor action `α : G(opSrc) ⟶ G(opTgt)`,
we cannot compose these to get `G(opTgt) ⟶ c`. The directions do not match.

This is a fundamental variance mismatch: the slice profunctor does not induce
a functorial weight on `(CoTwistedArrow C)ᵒᵖ` via the standard profunctor action.

This suggests that restricted cowedges are not directly equivalent to weighted
colimits in the standard sense. The relationship may require a different
categorical framework (e.g., enriched category theory, or a modified notion
of weighted colimit).
-/

/-- The slice weight as a type family on co-twisted arrows (not functorial).

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

/-!
### Covariant Slice Weight Functor

The variance mismatch with presheaves suggests using a **covariant** functor
(copresheaf) on `CoTwistedArrow C` instead. For a morphism `m : x ⟶ y` in
`CoTwistedArrow C`:

- `coTwDomArr m : coTwDom y ⟶ coTwDom x` (backwards)
- `coTwCodArr m : coTwCod x ⟶ coTwCod y` (forwards)

The profunctor `G : Cᵒᵖ ⥤ C ⥤ C` gives:

- `G.map (coTwCodArr m).op : G(coTwCod y, -) ⟶ G(coTwCod x, -)`
- `G(-).map (coTwDomArr m) : G(-, coTwDom y) ⟶ G(-, coTwDom x)`

Combined action: `G(coTwCod y, coTwDom y) ⟶ G(coTwCod x, coTwDom x)`

Given `h : G(coTwCod x, coTwDom x) ⟶ c`, we can compose:
`profAction ≫ h : G(coTwCod y, coTwDom y) ⟶ c`

This is the correct direction for a covariant functor on `CoTwistedArrow C`!
-/

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

/-- A weighted cowedge where the weight is derived from the slice profunctor
`G ⇓ c`. This takes the same parameters as `RestrictedCowedge` and
`StrongRestrictedCowedge` (an endoprofunctor `G` and an object `c`).

This is a `WeightedCowedge` where:
- The weight is `sliceWeight G c : (TwistedArrow C)ᵒᵖ ⥤ Type v`
- The diagram is `profunctorOnTwistedArrow C G : TwistedArrow C ⥤ C` -/
abbrev SliceWeightedCowedge (G : Cᵒᵖ ⥤ C ⥤ C) (c : C) :=
  WeightedCowedge (sliceWeight G c) G

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

end GebLean
