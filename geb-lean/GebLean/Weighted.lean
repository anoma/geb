import Mathlib.CategoryTheory.Category.Basic
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

/--
Composition of weighted cone morphisms.
-/
def WeightedCone.Hom.comp {W : J ⥤ Type v} {D : J ⥤ C}
    {c₁ c₂ c₃ : WeightedCone W D}
    (f : WeightedCone.Hom c₁ c₂) (g : WeightedCone.Hom c₂ c₃) :
    WeightedCone.Hom c₁ c₃ where
  hom := f.hom ≫ g.hom
  w j w := by simp [f.w, g.w]

instance (W : J ⥤ Type v) (D : J ⥤ C) : Category (WeightedCone W D) where
  Hom := WeightedCone.Hom
  id := WeightedCone.Hom.id
  comp := WeightedCone.Hom.comp
  id_comp f := by ext; simp [WeightedCone.Hom.id, WeightedCone.Hom.comp]
  comp_id f := by ext; simp [WeightedCone.Hom.id, WeightedCone.Hom.comp]
  assoc f g h := by ext; simp [WeightedCone.Hom.comp, Category.assoc]

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

instance (W : Jᵒᵖ ⥤ Type v) (D : J ⥤ C) : Category (WeightedCocone W D) where
  Hom := WeightedCocone.Hom
  id := WeightedCocone.Hom.id
  comp := WeightedCocone.Hom.comp
  id_comp f := by ext; simp [WeightedCocone.Hom.id, WeightedCocone.Hom.comp]
  comp_id f := by ext; simp [WeightedCocone.Hom.id, WeightedCocone.Hom.comp]
  assoc f g h := by ext; simp [WeightedCocone.Hom.comp, Category.assoc]

variable {D : Type w} [Category.{v} D]

/--
A weighted wedge over a profunctor `P : Cᵒᵖ ⥤ C ⥤ D` with weight
`W : TwistedArrow C ⥤ Type v` is a weighted cone over the diagram
`profunctorOnTwistedArrow C P` with the given weight.

This generalizes ordinary wedges: when `W` is the terminal functor (constant
at a singleton), a weighted wedge is exactly an ordinary wedge.
-/
abbrev WeightedWedge (W : TwistedArrow C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) :=
  WeightedCone W (profunctorOnTwistedArrow C P)

/--
A weighted cowedge over a profunctor `P : Cᵒᵖ ⥤ C ⥤ D` with weight
`W : (CoTwistedArrow C)ᵒᵖ ⥤ Type v` is a weighted cocone over the diagram
`profunctorOnCoTwistedArrow C P` with the given weight.

The weight is contravariant (a presheaf on `CoTwistedArrow C`) to match the
variance required by weighted cocones.

This generalizes ordinary cowedges: when `W` is the terminal functor (constant
at a singleton), a weighted cowedge is exactly an ordinary cowedge.
-/
abbrev WeightedCowedge (W : (CoTwistedArrow C)ᵒᵖ ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ D) :=
  WeightedCocone W (profunctorOnCoTwistedArrow C P)

end WeightedLimitColimit

section ConeWeightedConeEquivalence

/-!
## Cones as weighted cones with constant weight

Ordinary cones and cocones are special cases of weighted cones and cocones
where the weight functor is constant at a singleton type. This section
establishes this relationship.
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
def coconeToWeightedCocone {D : J ⥤ C} (c : Cocone D) :
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

end ConeWeightedConeEquivalence

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

end GebLean
