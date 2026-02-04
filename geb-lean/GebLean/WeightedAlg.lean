import GebLean.Weighted
import GebLean.ParanatAlg
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Endofunctor.Algebra

/-!
# Mendler-Lambek Correspondence via Restricted Coends

This module implements the correspondence between Mendler-style algebras
and conventional (Lambek) algebras for difunctors, following Vene's thesis
"Categorical Programming with Inductive and Coinductive Types" (sections
5.3-5.7).

## Overview

For an endodifunctor `G : Cᵒᵖ ⥤ C ⥤ C`:

- A **Mendler-style G-algebra** is a pair `(pt, Φ)` where `pt : C` and
  `Φ : HomToProf pt → G ⇓ pt` is a dinatural transformation. Concretely,
  for each `A`, we have `Φ_A : (A ⟶ pt) → (G(A,A) ⟶ pt)`.

- A **conventional G^e-algebra** is a pair `(pt, φ)` where
  `φ : G^e(pt) ⟶ pt` and `G^e` is defined via restricted coends.

The main result is that the categories of Mendler-style G-algebras and
conventional G^e-algebras are isomorphic (Theorem 5.19 in Vene).

## Definitions

- `HomToProf pt`: The profunctor `(A, B) ↦ (A ⟶ pt)`, constant in `B`
- `MendlerAlgebra G`: Mendler-style algebra for difunctor `G`
- The equivalence between `MendlerAlgebra G` and `RestrictedCowedge G (HomToProf pt)`

## References

* Vene, "Categorical Programming with Inductive and Coinductive Types"
-/

namespace GebLean

open CategoryTheory Limits Opposite

universe u v

variable {C : Type u} [Category.{v} C]

section HomToProfunctor

/-!
## The Hom-To Profunctor

For a fixed object `pt : C`, define the profunctor `HomToProf pt : Cᵒᵖ ⥤ C ⥤ Type v`
where `(HomToProf pt)(A, B) = (A ⟶ pt)`.

This is constant in the second argument and contravariant in the first via
precomposition. A diagonal element at `A` is a morphism `A ⟶ pt`.

This corresponds to Vene's "Id^i/C" (identity restricted to C) profunctor.
-/

/-- The profunctor `HomToProf pt` sends `(A, B)` to `(A ⟶ pt)`.
Contravariant in `A` via precomposition, constant in `B`.

Constructed as the currying of `(Prod.fst Cᵒᵖ C) ⋙ (yoneda.obj pt)`:
- `Prod.fst` projects out the first component
- `yoneda.obj pt` gives the representable presheaf Hom(-, pt)
- Currying converts from `Cᵒᵖ × C ⥤ Type v` to `Cᵒᵖ ⥤ C ⥤ Type v`

This corresponds to Vene's "Id^i/C" (identity restricted to C) profunctor. -/
def HomToProf (pt : C) : Cᵒᵖ ⥤ C ⥤ Type v :=
  Functor.curry.obj (CategoryTheory.Prod.fst Cᵒᵖ C ⋙ yoneda.obj pt)

/-- The object at `(A, B)` in `HomToProf pt` is `(A.unop ⟶ pt)`. -/
@[simp]
theorem HomToProf_obj_obj (pt : C) (A : Cᵒᵖ) (B : C) :
    ((HomToProf pt).obj A).obj B = (A.unop ⟶ pt) := by
  simp only [HomToProf, Functor.curry_obj_obj_obj, Functor.comp_obj,
             CategoryTheory.Prod.fst_obj, yoneda_obj_obj]

/-- The diagonal of `HomToProf pt` at `A` is the hom-set `(A ⟶ pt)`. -/
theorem HomToProf_diag (pt A : C) :
    diagApp (HomToProf pt) A = (A ⟶ pt) := by
  simp only [diagApp, HomToProf_obj_obj]

/-- The map in the first (contravariant) argument: precomposition. -/
@[simp]
theorem HomToProf_map_app (pt : C) {A₁ A₂ : Cᵒᵖ} (f : A₁ ⟶ A₂) (B : C)
    (h : A₁.unop ⟶ pt) :
    ((HomToProf pt).map f).app B h = f.unop ≫ h := by
  simp only [HomToProf, Functor.curry_obj_map_app, Functor.comp_map,
             CategoryTheory.Prod.fst_map, yoneda_obj_map]

/-- The map in the second (covariant) argument is identity. -/
@[simp]
theorem HomToProf_obj_map (pt : C) (A : Cᵒᵖ) {B₁ B₂ : C} (g : B₁ ⟶ B₂)
    (h : A.unop ⟶ pt) :
    ((HomToProf pt).obj A).map g h = h := by
  simp only [HomToProf, Functor.curry_obj_obj_map, Functor.comp_map,
             CategoryTheory.Prod.fst_map, yoneda_obj_map]
  simp [Category.id_comp]

/-- Left action (contravariant): precomposition with `f`. -/
theorem HomToProf_lmap (pt : C) {A B : C} (f : A ⟶ B)
    (h : diagApp (HomToProf pt) B) :
    Profunctor.lmap (HomToProf pt) f h = f ≫ h := by
  simp only [Profunctor.lmap, HomToProf_map_app]
  rfl

/-- Right action (covariant): identity (constant in second argument). -/
theorem HomToProf_rmap (pt : C) {A B : C} (f : A ⟶ B)
    (h : diagApp (HomToProf pt) A) :
    Profunctor.rmap (HomToProf pt) f h = h := by
  simp only [Profunctor.rmap, HomToProf_obj_map]

/-- `HomToProf pt` equals `IdProf ⇓ pt` (the identity profunctor sliced over pt).

This formalizes the connection to Vene's "Id^i/C" notation: the profunctor
sending `(A, B)` to `(A ⟶ pt)` is exactly the slice of the identity
endodifunctor over `pt`. Both are constant in the second argument and
contravariant (via precomposition) in the first. -/
theorem HomToProf_eq_sliceIdProf (pt : C) : HomToProf pt = IdProf ⇓ pt := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro A
    apply CategoryTheory.Functor.ext
    case h_obj => intro B; rfl
    case h_map =>
      intro B₁ B₂ g
      simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
      ext h
      simp only [HomToProf_obj_map,
        sliceProfunctor_obj_map, IdProf,
        Functor.const_obj_obj,
        Functor.const_obj_map, NatTrans.id_app,
        Category.id_comp]
  case h_map =>
    intro A₁ A₂ f
    ext B h
    simp only [NatTrans.comp_app,
      types_comp_apply, HomToProf_map_app,
      sliceProfunctor_map_app, IdProf]
    simp

/-- Given `f : pt ⟶ pt'`, construct a natural transformation
`HomToProf pt ⟶ HomToProf pt'` by postcomposition. -/
def HomToProf.mapPt {pt pt' : C} (f : pt ⟶ pt') : HomToProf pt ⟶ HomToProf pt' where
  app A := {
    app := fun _ γ => γ ≫ f
    naturality := by
      intros B₁ B₂ g
      ext γ
      simp only [HomToProf_obj_map, types_comp_apply]
  }
  naturality := by
    intros A₁ A₂ g
    ext B γ
    simp only [NatTrans.comp_app, types_comp_apply, HomToProf_map_app, Category.assoc]

/-- `HomToProf.mapPt` respects identity. -/
@[simp]
theorem HomToProf.mapPt_id (pt : C) : HomToProf.mapPt (𝟙 pt) = 𝟙 (HomToProf pt) := by
  ext A B γ
  simp only [mapPt, NatTrans.id_app, types_id_apply, Category.comp_id]

/-- `HomToProf.mapPt` respects composition. -/
theorem HomToProf.mapPt_comp {pt pt' pt'' : C} (f : pt ⟶ pt') (g : pt' ⟶ pt'') :
    HomToProf.mapPt (f ≫ g) = HomToProf.mapPt f ≫ HomToProf.mapPt g := by
  ext A B γ
  simp only [mapPt, NatTrans.comp_app, types_comp_apply, Category.assoc]

/-- `HomToProf.mapPt f` equals the map from `sliceProfunctorFunctor IdProf`.

Since `HomToProf pt = IdProf ⇓ pt` (by `HomToProf_eq_sliceIdProf`), the functorial
structure on `HomToProf` in `pt` is inherited from the general `sliceProfunctorFunctor`. -/
theorem HomToProf.mapPt_eq_sliceFunctorMap {pt pt' : C} (f : pt ⟶ pt') :
    HomToProf.mapPt f =
    eqToHom (HomToProf_eq_sliceIdProf pt) ≫
    (sliceProfunctorFunctor IdProf).map f ≫
    eqToHom (HomToProf_eq_sliceIdProf pt').symm := by
  ext A B γ
  simp only [mapPt, NatTrans.comp_app,
    types_comp_apply, eqToHom_app]
  simp only [eqToHom_refl]
  rfl

/-- The functor from `C` to `Cᵒᵖ ⥤ C ⥤ Type v` that maps `pt` to `HomToProf pt`.
This captures the covariant functoriality of `HomToProf` in `pt`. -/
def homToProfFunctor : C ⥤ (Cᵒᵖ ⥤ C ⥤ Type v) where
  obj pt := HomToProf pt
  map f := HomToProf.mapPt f
  map_id _ := HomToProf.mapPt_id _
  map_comp f g := HomToProf.mapPt_comp f g

/-- `homToProfFunctor` at `pt` equals `sliceProfunctorFunctor IdProf` at `pt`. -/
theorem homToProfFunctor_obj_eq (pt : C) :
    homToProfFunctor.obj pt = (sliceProfunctorFunctor IdProf).obj pt := by
  exact HomToProf_eq_sliceIdProf pt

end HomToProfunctor

section MendlerAlgebra

/-!
## Mendler-Style Algebras for Difunctors

A Mendler-style G-algebra for an endodifunctor `G : Cᵒᵖ ⥤ C ⥤ C` is a pair
`(pt, Φ)` where:
- `pt : C` is the carrier object
- `Φ` is a dinatural transformation from `HomToProf pt` to `G ⇓ pt`

Concretely, `Φ` is a family `{Φ_A}_{A : C}` of functions:
  `Φ_A : (A ⟶ pt) → (G(A, A) ⟶ pt)`
satisfying the dinaturality condition: for `g : A ⟶ B` and `β : B ⟶ pt`:
  `Φ_A(β ∘ g) ∘ G(g, id) = Φ_B(β) ∘ G(id, g)`
-/

variable (G : Cᵒᵖ ⥤ C ⥤ C)

/-- A Mendler-style algebra for an endodifunctor `G` over a fixed carrier `pt`.
This contains the algebra data without bundling the carrier object. -/
@[ext]
structure MendlerAlgebraOver (pt : C) where
  /-- The cowedge data over the carrier. -/
  toRestrictedCowedgeOver : RestrictedCowedgeOver G (HomToProf pt) pt

namespace MendlerAlgebraOver

variable {G} {G' : Cᵒᵖ ⥤ C ⥤ C} {pt : C}

/-- The family of algebra operations. -/
abbrev family (m : MendlerAlgebraOver G pt) :
    ParanatSig (HomToProf pt) (G ⇓ pt) :=
  m.toRestrictedCowedgeOver.family

/-- The dinaturality condition. -/
abbrev isDinatural (m : MendlerAlgebraOver G pt) :
    IsDinatural (HomToProf pt) (G ⇓ pt) m.family :=
  m.toRestrictedCowedgeOver.isDinatural

/-- Constructor with explicit family and dinaturality arguments. -/
@[match_pattern]
def mk' (pt : C) (family : ParanatSig (HomToProf pt) (G ⇓ pt))
    (isDinatural : IsDinatural (HomToProf pt) (G ⇓ pt) family) :
    MendlerAlgebraOver G pt :=
  ⟨⟨family, isDinatural⟩⟩

/-- Contravariant action on the G parameter. -/
def mapG (β : G' ⟶ G) (m : MendlerAlgebraOver G pt) : MendlerAlgebraOver G' pt :=
  ⟨RestrictedCowedgeOver.mapG β m.toRestrictedCowedgeOver⟩

/-- `mapG` respects identity. -/
@[simp]
theorem mapG_id (m : MendlerAlgebraOver G pt) : mapG (𝟙 G) m = m := by
  ext
  simp only [mapG, RestrictedCowedgeOver.mapG_id]

/-- `mapG` respects composition (contravariantly). -/
theorem mapG_comp {G'' : Cᵒᵖ ⥤ C ⥤ C} (β : G' ⟶ G) (γ : G ⟶ G'')
    (m : MendlerAlgebraOver G'' pt) :
    mapG (β ≫ γ) m = mapG β (mapG γ m) := by
  ext
  simp only [mapG, RestrictedCowedgeOver.mapG_comp]

end MendlerAlgebraOver

/-- Mendler algebra data as a profunctor in the carrier parameters.

In `MendlerAlgebraOver G pt`, the parameter `pt` appears in two places:
- In `HomToProf pt` (the H parameter), which is contravariant
- As the third parameter of `RestrictedCowedgeOver`, which is covariant

This structure separates these into `ptH` (for HomToProf) and `ptC` (carrier),
making the bifunctorial structure explicit:
- `ptH`: contravariant (via HomToProf.mapPt + RestrictedCowedgeOver.mapH)
- `ptC`: covariant (via RestrictedCowedgeOver.mapPt)

This forms a profunctor `Cᵒᵖ ⥤ C ⥤ Type v` for each fixed `G`.
`MendlerAlgebraOver G pt` is the diagonal case where `ptH = ptC = pt`. -/
@[ext]
structure MendlerAlgProfunctor (ptH ptC : C) where
  /-- The underlying cowedge data. -/
  toRestrictedCowedgeOver : RestrictedCowedgeOver G (HomToProf ptH) ptC

namespace MendlerAlgProfunctor

variable {G}
variable {ptH ptH' ptH'' ptC ptC' ptC'' pt : C}
variable {G' G'' : Cᵒᵖ ⥤ C ⥤ C}

/-- Contravariant action on the G parameter. -/
def mapG (β : G' ⟶ G) (m : MendlerAlgProfunctor G ptH ptC) :
    MendlerAlgProfunctor G' ptH ptC :=
  ⟨RestrictedCowedgeOver.mapG β m.toRestrictedCowedgeOver⟩

/-- `mapG` respects identity. -/
@[simp]
theorem mapG_id (m : MendlerAlgProfunctor G ptH ptC) :
    mapG (𝟙 G) m = m := by
  ext
  simp only [mapG, RestrictedCowedgeOver.mapG_id]

/-- `mapG` respects composition (contravariantly). -/
theorem mapG_comp (β : G' ⟶ G) (γ : G ⟶ G'')
    (m : MendlerAlgProfunctor G'' ptH ptC) :
    mapG (β ≫ γ) m = mapG β (mapG γ m) := by
  ext
  simp only [mapG, RestrictedCowedgeOver.mapG_comp]

/-- Contravariant action on the ptH parameter.
Given `f : ptH' ⟶ ptH`, we map `MendlerAlgProfunctor G ptH ptC` to
`MendlerAlgProfunctor G ptH' ptC` by precomposing via `HomToProf.mapPt f`. -/
def mapPtH (f : ptH' ⟶ ptH) (m : MendlerAlgProfunctor G ptH ptC) :
    MendlerAlgProfunctor G ptH' ptC :=
  ⟨RestrictedCowedgeOver.mapH (HomToProf.mapPt f) m.toRestrictedCowedgeOver⟩

/-- `mapPtH` respects identity. -/
@[simp]
theorem mapPtH_id (m : MendlerAlgProfunctor G ptH ptC) :
    mapPtH (𝟙 ptH) m = m := by
  simp only [mapPtH, HomToProf.mapPt_id, RestrictedCowedgeOver.mapH_id]

/-- `mapPtH` respects composition (contravariantly). -/
theorem mapPtH_comp (f : ptH' ⟶ ptH) (g : ptH'' ⟶ ptH')
    (m : MendlerAlgProfunctor G ptH ptC) :
    mapPtH (g ≫ f) m = mapPtH g (mapPtH f m) := by
  simp only [mapPtH, HomToProf.mapPt_comp, RestrictedCowedgeOver.mapH_comp]

/-- Covariant action on the ptC parameter.
Given `f : ptC ⟶ ptC'`, we map `MendlerAlgProfunctor G ptH ptC` to
`MendlerAlgProfunctor G ptH ptC'` by postcomposition. -/
def mapPtC (f : ptC ⟶ ptC') (m : MendlerAlgProfunctor G ptH ptC) :
    MendlerAlgProfunctor G ptH ptC' :=
  ⟨RestrictedCowedgeOver.mapPt f m.toRestrictedCowedgeOver⟩

/-- `mapPtC` respects identity. -/
@[simp]
theorem mapPtC_id (m : MendlerAlgProfunctor G ptH ptC) :
    mapPtC (𝟙 ptC) m = m := by
  simp only [mapPtC, RestrictedCowedgeOver.mapPt_id]

/-- `mapPtC` respects composition. -/
theorem mapPtC_comp (f : ptC ⟶ ptC') (g : ptC' ⟶ ptC'')
    (m : MendlerAlgProfunctor G ptH ptC) :
    mapPtC (f ≫ g) m = mapPtC g (mapPtC f m) := by
  simp only [mapPtC, RestrictedCowedgeOver.mapPt_comp]

/-- Convert to `MendlerAlgebraOver` when the parameters coincide. -/
def toMendlerAlgebraOver (m : MendlerAlgProfunctor G pt pt) :
    MendlerAlgebraOver G pt :=
  ⟨m.toRestrictedCowedgeOver⟩

/-- Convert from `MendlerAlgebraOver`. -/
def ofMendlerAlgebraOver (m : MendlerAlgebraOver G pt) :
    MendlerAlgProfunctor G pt pt :=
  ⟨m.toRestrictedCowedgeOver⟩

/-- Round-trip from `MendlerAlgebraOver` and back. -/
@[simp]
theorem toMendlerAlgebraOver_ofMendlerAlgebraOver (m : MendlerAlgebraOver G pt) :
    toMendlerAlgebraOver (ofMendlerAlgebraOver m) = m := rfl

/-- Round-trip from `MendlerAlgProfunctor` and back. -/
@[simp]
theorem ofMendlerAlgebraOver_toMendlerAlgebraOver
    (m : MendlerAlgProfunctor G pt pt) :
    ofMendlerAlgebraOver (toMendlerAlgebraOver m) = m := rfl

/-- Naturality: `mapPtH` and `mapPtC` commute.
For `f : ptH' ⟶ ptH` and `g : ptC ⟶ ptC'`:
`mapPtH f (mapPtC g m) = mapPtC g (mapPtH f m)` -/
theorem mapPtH_mapPtC_comm (f : ptH' ⟶ ptH) (g : ptC ⟶ ptC')
    (m : MendlerAlgProfunctor G ptH ptC) :
    mapPtH f (mapPtC g m) = mapPtC g (mapPtH f m) := by
  apply MendlerAlgProfunctor.ext
  apply RestrictedCowedgeOver.ext
  funext A h
  simp only [mapPtH, mapPtC, RestrictedCowedgeOver.mapH, RestrictedCowedgeOver.mapPt]

/-- Naturality: `mapG` and `mapPtH` commute.
For `β : G' ⟶ G` and `f : ptH' ⟶ ptH`:
`mapG β (mapPtH f m) = mapPtH f (mapG β m)` -/
theorem mapG_mapPtH_comm (β : G' ⟶ G) (f : ptH' ⟶ ptH)
    (m : MendlerAlgProfunctor G ptH ptC) :
    mapG β (mapPtH f m) = mapPtH f (mapG β m) := by
  apply MendlerAlgProfunctor.ext
  simp only [mapG, mapPtH]
  exact RestrictedCowedgeOver.mapG_mapH_comm β (HomToProf.mapPt f)
    m.toRestrictedCowedgeOver

/-- Naturality: `mapG` and `mapPtC` commute.
For `β : G' ⟶ G` and `g : ptC ⟶ ptC'`:
`mapG β (mapPtC g m) = mapPtC g (mapG β m)` -/
theorem mapG_mapPtC_comm (β : G' ⟶ G) (g : ptC ⟶ ptC')
    (m : MendlerAlgProfunctor G ptH ptC) :
    mapG β (mapPtC g m) = mapPtC g (mapG β m) := by
  apply MendlerAlgProfunctor.ext
  simp only [mapG, mapPtC]
  exact RestrictedCowedgeOver.mapG_mapPt_comm β g m.toRestrictedCowedgeOver

end MendlerAlgProfunctor

/-- The profunctor `Cᵒᵖ ⥤ C ⥤ Type (max u v)` for Mendler algebra data.
For a fixed endodifunctor `G`, this maps `(ptH, ptC)` to `MendlerAlgProfunctor G ptH ptC`. -/
def mendlerAlgProfunctorFunctor (G : Cᵒᵖ ⥤ C ⥤ C) : Cᵒᵖ ⥤ C ⥤ Type (max u v) where
  obj ptHop := {
    obj := fun ptC => MendlerAlgProfunctor G ptHop.unop ptC
    map := @fun _ _ g m => MendlerAlgProfunctor.mapPtC g m
    map_id := fun _ => by
      ext m
      simp only [types_id_apply, MendlerAlgProfunctor.mapPtC_id]
    map_comp := @fun _ _ _ f g => by
      ext m
      simp only [types_comp_apply, MendlerAlgProfunctor.mapPtC_comp]
  }
  map := @fun _ _ f => {
    app := fun _ m => MendlerAlgProfunctor.mapPtH f.unop m
    naturality := @fun _ _ g => by
      funext m
      simp only [types_comp_apply, MendlerAlgProfunctor.mapPtH_mapPtC_comm]
  }
  map_id := fun _ => by
    ext _ m
    simp only [NatTrans.id_app, types_id_apply, unop_id, MendlerAlgProfunctor.mapPtH_id]
  map_comp := @fun _ _ _ f g => by
    ext _ m
    simp only [NatTrans.comp_app, types_comp_apply, unop_comp, MendlerAlgProfunctor.mapPtH_comp]

/-- `MendlerAlgProfunctor G ptH ptC` equals the application of `mendlerAlgProfunctorFunctor`. -/
theorem mendlerAlgProfunctor_eq_functor_obj (G : Cᵒᵖ ⥤ C ⥤ C) (ptH ptC : C) :
    MendlerAlgProfunctor G ptH ptC =
    ((mendlerAlgProfunctorFunctor G).obj (Opposite.op ptH)).obj ptC := rfl

/-- The trifunctor `(Cᵒᵖ ⥤ C ⥤ C)ᵒᵖ ⥤ Cᵒᵖ ⥤ C ⥤ Type (max u v)`.
This extends `mendlerAlgProfunctorFunctor` to also be (contravariantly) functorial
in the `G` parameter. -/
def mendlerAlgProfunctorTrifunctor :
    (Cᵒᵖ ⥤ C ⥤ C)ᵒᵖ ⥤ Cᵒᵖ ⥤ C ⥤ Type (max u v) where
  obj Gop := mendlerAlgProfunctorFunctor Gop.unop
  map := @fun Gop Gop' β => {
    app := fun ptHop => {
      app := fun ptC m => MendlerAlgProfunctor.mapG β.unop m
      naturality := @fun _ _ g => by
        funext m
        simp only [types_comp_apply, mendlerAlgProfunctorFunctor]
        exact MendlerAlgProfunctor.mapG_mapPtC_comm β.unop g m
    }
    naturality := @fun _ _ f => by
      ext ptC m
      simp only [types_comp_apply, mendlerAlgProfunctorFunctor, NatTrans.comp_app]
      exact MendlerAlgProfunctor.mapG_mapPtH_comm β.unop f.unop m
  }
  map_id := fun Gop => by
    ext ptHop ptC m
    simp only [NatTrans.id_app, types_id_apply, unop_id, MendlerAlgProfunctor.mapG_id]
  map_comp := @fun _ _ _ β γ => by
    ext ptHop ptC m
    simp only [NatTrans.comp_app, types_comp_apply, unop_comp]
    exact MendlerAlgProfunctor.mapG_comp γ.unop β.unop m

/-- `mendlerAlgProfunctorFunctor G` equals the application of
`mendlerAlgProfunctorTrifunctor` at `G`. -/
theorem mendlerAlgProfunctorFunctor_eq_trifunctor_obj (G : Cᵒᵖ ⥤ C ⥤ C) :
    mendlerAlgProfunctorFunctor G =
    mendlerAlgProfunctorTrifunctor.obj (Opposite.op G) := rfl

/-- A Mendler-style algebra for an endodifunctor `G`. -/
@[ext]
structure MendlerAlgebra where
  /-- The carrier object. -/
  pt : C
  /-- The algebra data over the carrier. -/
  toMendlerAlgebraOver : MendlerAlgebraOver G pt

namespace MendlerAlgebra

variable {G}

/-- The family of algebra operations. -/
abbrev family (m : MendlerAlgebra G) : ParanatSig (HomToProf m.pt) (G ⇓ m.pt) :=
  m.toMendlerAlgebraOver.family

/-- The dinaturality condition. -/
abbrev isDinatural (m : MendlerAlgebra G) :
    IsDinatural (HomToProf m.pt) (G ⇓ m.pt) m.family :=
  m.toMendlerAlgebraOver.isDinatural

/-- The underlying RestrictedCowedgeOver. -/
abbrev toRestrictedCowedgeOver (m : MendlerAlgebra G) :
    RestrictedCowedgeOver G (HomToProf m.pt) m.pt :=
  m.toMendlerAlgebraOver.toRestrictedCowedgeOver

/-- Constructor with explicit family and dinaturality arguments. -/
@[match_pattern]
def mk' (pt : C) (family : ParanatSig (HomToProf pt) (G ⇓ pt))
    (isDinatural : IsDinatural (HomToProf pt) (G ⇓ pt) family) : MendlerAlgebra G :=
  ⟨pt, ⟨⟨family, isDinatural⟩⟩⟩

/-- The algebra operation at object `A`: given `γ : A ⟶ pt`, produce
`G(A, A) ⟶ pt`. -/
def algOp (m : MendlerAlgebra G) (A : C) (γ : A ⟶ m.pt) :
    (G.obj (Opposite.op A)).obj A ⟶ m.pt :=
  m.family A γ

/-- The explicit dinaturality condition: for `g : A ⟶ B` and `β : B ⟶ pt`,
the two paths from `G(B, A)` to `pt` agree:
  `G(g, id) ≫ Φ_A(β ∘ g) = G(id, g) ≫ Φ_B(β)` -/
theorem dinaturality (m : MendlerAlgebra G) {A B : C} (g : A ⟶ B)
    (β : B ⟶ m.pt) :
    (G.map g.op).app A ≫ m.family A (g ≫ β) =
    (G.obj (Opposite.op B)).map g ≫ m.family B β := by
  have dinat := m.isDinatural A B g β
  simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor_obj_map,
    sliceProfunctor_map_app, HomToProf_map_app, HomToProf_obj_map,
    Quiver.Hom.unop_op] at dinat
  exact dinat.symm

/-- Convert a Mendler algebra to a restricted cowedge. -/
def toRestrictedCowedge (m : MendlerAlgebra G) :
    RestrictedCowedge G (HomToProf m.pt) where
  pt := m.pt
  toRestrictedCowedgeOver := ⟨m.family, m.isDinatural⟩

/-- Construct a Mendler algebra from a restricted cowedge with HomToProf pt
whose carrier is pt. -/
def ofRestrictedCowedge' (pt : C) (family : ParanatSig (HomToProf pt) (G ⇓ pt))
    (isDinatural : IsDinatural (HomToProf pt) (G ⇓ pt) family) : MendlerAlgebra G :=
  ⟨pt, ⟨⟨family, isDinatural⟩⟩⟩

/-- Construct a Mendler algebra from a point and a RestrictedCowedgeOver. -/
def ofRestrictedCowedgeOver (pt : C) (u : RestrictedCowedgeOver G (HomToProf pt) pt) :
    MendlerAlgebra G :=
  ⟨pt, ⟨u⟩⟩

/-- Construct a Mendler algebra from a point and a MendlerAlgebraOver. -/
def ofMendlerAlgebraOver (pt : C) (m : MendlerAlgebraOver G pt) : MendlerAlgebra G :=
  ⟨pt, m⟩

/-- Round-trip from MendlerAlgebra to MendlerAlgebraOver and back. -/
theorem ofMendlerAlgebraOver_toMendlerAlgebraOver (m : MendlerAlgebra G) :
    ofMendlerAlgebraOver m.pt m.toMendlerAlgebraOver = m := rfl

/-- Round-trip from MendlerAlgebraOver to MendlerAlgebra and back. -/
theorem toMendlerAlgebraOver_ofMendlerAlgebraOver (pt : C)
    (u : MendlerAlgebraOver G pt) :
    (ofMendlerAlgebraOver pt u).toMendlerAlgebraOver = u := rfl

/-- Round-trip from MendlerAlgebra to RestrictedCowedgeOver and back. -/
theorem ofRestrictedCowedgeOver_toRestrictedCowedgeOver (m : MendlerAlgebra G) :
    ofRestrictedCowedgeOver m.pt m.toRestrictedCowedgeOver = m := rfl

/-- Round-trip from RestrictedCowedgeOver to MendlerAlgebra and back. -/
theorem toRestrictedCowedgeOver_ofRestrictedCowedgeOver (pt : C)
    (u : RestrictedCowedgeOver G (HomToProf pt) pt) :
    (ofRestrictedCowedgeOver pt u).toRestrictedCowedgeOver = u := rfl

/-- Contravariant action on the G parameter. -/
def mapG {G' : Cᵒᵖ ⥤ C ⥤ C} (β : G' ⟶ G) (m : MendlerAlgebra G) :
    MendlerAlgebra G' :=
  ⟨m.pt, MendlerAlgebraOver.mapG β m.toMendlerAlgebraOver⟩

/-- `mapG` respects identity. -/
@[simp]
theorem mapG_id (m : MendlerAlgebra G) : mapG (𝟙 G) m = m := by
  simp only [mapG, MendlerAlgebraOver.mapG_id]

/-- `mapG` respects composition (contravariantly). -/
theorem mapG_comp {G' G'' : Cᵒᵖ ⥤ C ⥤ C} (β : G' ⟶ G) (γ : G ⟶ G'')
    (m : MendlerAlgebra G'') :
    mapG (β ≫ γ) m = mapG β (mapG γ m) := by
  simp only [mapG, MendlerAlgebraOver.mapG_comp]

end MendlerAlgebra

/-- A morphism of Mendler algebras. -/
@[ext]
structure MendlerAlgebraHom {G : Cᵒᵖ ⥤ C ⥤ C} (m₁ m₂ : MendlerAlgebra G) where
  /-- The underlying morphism in C. -/
  hom : m₁.pt ⟶ m₂.pt
  /-- The compatibility condition: `h ∘ Φ_A(γ) = Ψ_A(h ∘ γ)`. -/
  comm : ∀ (A : C) (γ : A ⟶ m₁.pt),
    m₁.family A γ ≫ hom = m₂.family A (γ ≫ hom)

namespace MendlerAlgebraHom

variable {G : Cᵒᵖ ⥤ C ⥤ C}

/-- Identity morphism on a Mendler algebra. -/
@[simps]
def id (m : MendlerAlgebra G) : MendlerAlgebraHom m m where
  hom := 𝟙 m.pt
  comm _ _ := by simp

/-- Composition of Mendler algebra morphisms. -/
@[simps]
def comp {m₁ m₂ m₃ : MendlerAlgebra G}
    (f : MendlerAlgebraHom m₁ m₂) (g : MendlerAlgebraHom m₂ m₃) :
    MendlerAlgebraHom m₁ m₃ where
  hom := f.hom ≫ g.hom
  comm A γ := by
    rw [← Category.assoc, f.comm, g.comm]
    simp [Category.assoc]

end MendlerAlgebraHom

/-- The category of Mendler algebras for `G`. -/
instance MendlerAlgebraCat : Category (MendlerAlgebra G) where
  Hom := MendlerAlgebraHom
  id := MendlerAlgebraHom.id
  comp := MendlerAlgebraHom.comp
  id_comp _ := by ext; simp [MendlerAlgebraHom.comp, MendlerAlgebraHom.id]
  comp_id _ := by ext; simp [MendlerAlgebraHom.comp, MendlerAlgebraHom.id]
  assoc _ _ _ := by ext; simp [MendlerAlgebraHom.comp, Category.assoc]

end MendlerAlgebra

section MendlerAlgDiagElemEquiv

/-!
## Mendler Algebras as Diagonal Elements

`MendlerAlgebra G` is isomorphic to `DiagElem (mendlerAlgProfunctorFunctor G)`.
This is because:
- Both consist of a base object and algebra data at the diagonal
- The morphism compatibility conditions match exactly
-/

variable (G : Cᵒᵖ ⥤ C ⥤ C)

/-- Convert a Mendler algebra to a diagonal element of the Mendler algebra
profunctor. -/
@[simps]
def mendlerAlgToDiagElem (m : MendlerAlgebra G) :
    DiagElem (mendlerAlgProfunctorFunctor G) where
  base := m.pt
  elem := ⟨m.toRestrictedCowedgeOver⟩

/-- Convert a diagonal element of the Mendler algebra profunctor to a
Mendler algebra. -/
@[simps]
def diagElemToMendlerAlg (x : DiagElem (mendlerAlgProfunctorFunctor G)) :
    MendlerAlgebra G where
  pt := x.base
  toMendlerAlgebraOver := ⟨x.elem.toRestrictedCowedgeOver⟩

/-- Convert a Mendler algebra morphism to a diagonal element morphism. -/
@[simps]
def mendlerAlgHomToDiagElemHom {m₁ m₂ : MendlerAlgebra G}
    (f : m₁ ⟶ m₂) :
    mendlerAlgToDiagElem G m₁ ⟶ mendlerAlgToDiagElem G m₂ where
  base := f.hom
  compat := by
    simp only [DiagCompat, mendlerAlgToDiagElem_base, mendlerAlgProfunctorFunctor]
    apply MendlerAlgProfunctor.ext
    apply RestrictedCowedgeOver.ext
    funext A h
    simp only [mendlerAlgToDiagElem, MendlerAlgProfunctor.mapPtC,
      MendlerAlgProfunctor.mapPtH, RestrictedCowedgeOver.mapPt,
      RestrictedCowedgeOver.mapH, HomToProf.mapPt]
    exact f.comm A h

/-- Convert a diagonal element morphism to a Mendler algebra morphism. -/
@[simps]
def diagElemHomToMendlerAlgHom {x y : DiagElem (mendlerAlgProfunctorFunctor G)}
    (f : x ⟶ y) :
    diagElemToMendlerAlg G x ⟶ diagElemToMendlerAlg G y where
  hom := f.base
  comm := fun A h => by
    have hcompat := f.compat
    simp only [DiagCompat, mendlerAlgProfunctorFunctor] at hcompat
    have heq := congrArg MendlerAlgProfunctor.toRestrictedCowedgeOver hcompat
    simp only [MendlerAlgProfunctor.mapPtC, MendlerAlgProfunctor.mapPtH,
      RestrictedCowedgeOver.mapPt, RestrictedCowedgeOver.mapH,
      HomToProf.mapPt] at heq
    have h' := congrFun (congrFun (congrArg RestrictedCowedgeOver.family heq) A) h
    exact h'

/-- The functor from Mendler algebras to diagonal elements. -/
@[simps]
def mendlerAlgToDiagElemFunctor :
    MendlerAlgebra G ⥤ DiagElem (mendlerAlgProfunctorFunctor G) where
  obj := mendlerAlgToDiagElem G
  map := mendlerAlgHomToDiagElemHom G
  map_id _ := DiagElem.Hom.ext rfl
  map_comp _ _ := DiagElem.Hom.ext rfl

/-- The functor from diagonal elements to Mendler algebras. -/
@[simps]
def diagElemToMendlerAlgFunctor :
    DiagElem (mendlerAlgProfunctorFunctor G) ⥤ MendlerAlgebra G where
  obj := diagElemToMendlerAlg G
  map := diagElemHomToMendlerAlgHom G
  map_id _ := MendlerAlgebraHom.ext rfl
  map_comp _ _ := MendlerAlgebraHom.ext rfl

/-- `MendlerAlgebra G` is isomorphic to `DiagElem (mendlerAlgProfunctorFunctor G)`. -/
def mendlerAlgDiagElemIsoCat :
    MendlerAlgebra G ≅Cat DiagElem (mendlerAlgProfunctorFunctor G) where
  hom := (mendlerAlgToDiagElemFunctor G).toCatHom
  inv := (diagElemToMendlerAlgFunctor G).toCatHom

/-- The equivalence derived from the isomorphism. -/
def mendlerAlgDiagElemEquiv :
    MendlerAlgebra G ≌ DiagElem (mendlerAlgProfunctorFunctor G) :=
  Cat.equivOfIso (mendlerAlgDiagElemIsoCat G)

end MendlerAlgDiagElemEquiv

section MendlerRestrictedEquivalence

/-!
## Equivalence: Mendler Algebras and Restricted Cowedges

A Mendler algebra `(pt, Φ)` is exactly a `RestrictedCowedge G (HomToProf pt)`.
We establish this correspondence formally.

The relationship is:
- `MendlerAlgebra G` bundles the carrier `pt` with the algebra structure
- `RestrictedCowedge G H` has a fixed restriction profunctor `H`

For each `pt`, `MendlerAlgebra G` restricted to carrier `pt` is equivalent
to `RestrictedCowedge G (HomToProf pt)`.
-/

variable (G : Cᵒᵖ ⥤ C ⥤ C)

/-- A Mendler algebra determines a restricted cowedge with the HomToProf
profunctor for its carrier. -/
def mendlerToRestrictedCowedge (m : MendlerAlgebra G) :
    RestrictedCowedge G (HomToProf m.pt) :=
  m.toRestrictedCowedge

/-- A restricted cowedge with HomToProf pt whose carrier equals pt determines
a Mendler algebra. We use `Eq.rec` on `hpt.symm` to transport from
`HomToProf pt` to `HomToProf rc.pt`, aligning both profunctor arguments
with the carrier. -/
def restrictedCowedgeToMendler (pt : C) (rc : RestrictedCowedge G (HomToProf pt))
    (hpt : rc.pt = pt) : MendlerAlgebra G where
  pt := rc.pt
  toMendlerAlgebraOver := ⟨⟨
    Eq.rec (motive := fun x _ => ParanatSig (HomToProf x) (G ⇓ rc.pt))
      rc.family hpt.symm,
    Eq.rec (motive := fun x h =>
        IsDinatural (HomToProf x) (G ⇓ rc.pt)
          (Eq.rec (motive := fun y _ => ParanatSig (HomToProf y) (G ⇓ rc.pt))
            rc.family h))
      rc.isDinatural hpt.symm⟩⟩

/-- For a Mendler algebra, converting to restricted cowedge and back
preserves the structure. -/
theorem mendler_restrictedCowedge_roundtrip (m : MendlerAlgebra G) :
    restrictedCowedgeToMendler G m.pt (mendlerToRestrictedCowedge G m) rfl = m := by
  cases m with | mk pt u => cases u with | mk r => cases r with | mk fam dinat => rfl

end MendlerRestrictedEquivalence

section WeightedCowedgeCorrespondence

/-!
## WeightedCowedge Correspondence for HomToProf

For the weight profunctor `H = HomToProf pt`, the categories of weighted
cowedges and restricted cowedges are equivalent. This is because the
weight at any co-twisted arrow `(arr : cod ⟶ dom)` is `cod ⟶ pt`, which
depends only on the codomain (source) of the co-twisted arrow.

The weighted cocone naturality condition forces off-diagonal legs to be
uniquely determined by diagonal legs. For a morphism
`m : coTwObjMk arr ⟶ idCoTwistedArrow cod` in CoTwistedArrow:

  D.map m ≫ c.leg (id_{cod}) w = c.leg (coTwObjMk arr) (W.map m.op w)

Since `HomToProf pt` is constant in the covariant position, `W.map m.op`
is identity, so:

  c.leg (coTwObjMk arr) γ = D.map m ≫ c.leg (id_{cod}) γ
                         = (G.map arr.op).app cod ≫ family cod γ

Thus every `RestrictedCowedge G (HomToProf pt)` extends uniquely to a
`WeightedCowedge (HomToProf pt) G`, and vice versa.
-/

variable (G : Cᵒᵖ ⥤ C ⥤ C)

/-- A weighted Mendler cowedge is a WeightedCowedge with weight HomToProf pt
and diagram G. -/
abbrev WeightedMendlerCowedge (pt : C) := WeightedCowedge (HomToProf pt) G

/-!
### Extension from RestrictedCowedge to WeightedCowedge

Given a restricted cowedge with `family : A → (A ⟶ pt) → (G(A,A) ⟶ rc.pt)`,
we extend to all co-twisted arrows via:

  extendLeg (arr : cod ⟶ dom) (γ : cod ⟶ pt) := (G.map arr.op).app cod ≫ family cod γ
-/

/-- The generalized extended leg at an arbitrary co-twisted arrow, with
separate weight point `wpt` and apex point `apt`. For a restricted cowedge
with apex `apt` and weight `HomToProf wpt`, extends the diagonal family to
all co-twisted arrows. The formula is:
  `extendLeg (arr : cod ⟶ dom) (γ : cod ⟶ wpt) := (G.map arr.op).app cod ≫ family cod γ`
-/
def extendMendlerLeg' (wpt apt : C)
    (rc : RestrictedCowedgeOver G (HomToProf wpt) apt)
    (tw : CoTwistedArrow C) :
    (profunctorOnOpCoTwistedArrow C (HomToProf wpt)).obj (Opposite.op tw) →
    ((profunctorOnCoTwistedArrow C G).obj tw ⟶ apt) := fun w =>
  let cod := coTwCod tw
  let dom := coTwDom tw
  let arr := coTwArr tw
  have hWeight : (profunctorOnOpCoTwistedArrow C (HomToProf wpt)).obj (Opposite.op tw) =
      (cod ⟶ wpt) := profunctorOnOpCoTwistedArrow_at_arrow (HomToProf wpt) arr
  let γ : cod ⟶ wpt := cast hWeight w
  have hSlice : diagApp (HomToProf wpt) cod = (cod ⟶ wpt) := HomToProf_diag wpt cod
  let leg_at_cod : (G.obj (Opposite.op cod)).obj cod ⟶ apt :=
    rc.family cod (cast hSlice.symm γ)
  have hDom : (G.obj (Opposite.op dom)).obj cod =
      (profunctorOnCoTwistedArrow C G).obj tw := rfl
  eqToHom hDom ≫ (G.map arr.op).app cod ≫ leg_at_cod

/-- The extended leg at an arbitrary co-twisted arrow, computed from
diagonal family data. For `(arr : cod ⟶ dom)` with weight `γ : cod ⟶ pt`,
this is `(G.map arr.op).app cod ≫ family cod γ : G(dom, cod) ⟶ pt`.
This is the special case where weight point equals apex point. -/
def extendMendlerLeg (pt : C) (rc : RestrictedCowedgeOver G (HomToProf pt) pt)
    (tw : CoTwistedArrow C) :
    (profunctorOnOpCoTwistedArrow C (HomToProf pt)).obj (Opposite.op tw) →
    ((profunctorOnCoTwistedArrow C G).obj tw ⟶ pt) := fun w =>
  let cod := coTwCod tw
  let dom := coTwDom tw
  let arr := coTwArr tw
  have hWeight : (profunctorOnOpCoTwistedArrow C (HomToProf pt)).obj (Opposite.op tw) =
      (cod ⟶ pt) := profunctorOnOpCoTwistedArrow_at_arrow (HomToProf pt) arr
  let γ : cod ⟶ pt := cast hWeight w
  have hSlice : diagApp (G ⇓ pt) cod = ((G.obj (Opposite.op cod)).obj cod ⟶ pt) :=
    sliceProfunctor_obj_obj G pt (Opposite.op cod) cod
  let leg_at_cod : (G.obj (Opposite.op cod)).obj cod ⟶ pt :=
    cast hSlice (rc.family cod (cast (HomToProf_diag pt cod) γ))
  have hDom : (G.obj (Opposite.op dom)).obj cod =
      (profunctorOnCoTwistedArrow C G).obj tw := rfl
  eqToHom hDom ≫ (G.map arr.op).app cod ≫ leg_at_cod

/-- For HomToProf, the weight at any co-twisted arrow depends only on the
codomain (source in C). -/
theorem HomToProf_weight_at_coTw (pt : C) (tw : CoTwistedArrow C) :
    (profunctorOnOpCoTwistedArrow C (HomToProf pt)).obj (Opposite.op tw) =
    (coTwCod tw ⟶ pt) :=
  profunctorOnOpCoTwistedArrow_at_arrow (HomToProf pt) (coTwArr tw)

/-- For HomToProf, the weight map along a CoTwistedArrow morphism is
precomposition by the codomain arrow component. This is because HomToProf
is constant in its covariant position. -/
theorem HomToProf_weight_map_eq (pt : C) {tw tw' : CoTwistedArrow C}
    (f : tw ⟶ tw') (w : coTwCod tw' ⟶ pt) :
    cast (HomToProf_weight_at_coTw pt tw)
      ((profunctorOnOpCoTwistedArrow C (HomToProf pt)).map f.op
        (cast (HomToProf_weight_at_coTw pt tw').symm w)) =
    coTwCodArr f ≫ w := by
  simp only [profunctorOnOpCoTwistedArrow_map, profunctorOnTwistedArrow_map]
  simp only [coTwistedArrowOpEquiv_map_twDomArr, coTwistedArrowOpEquiv_map_twCodArr]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  -- The types are definitionally equal, so we can use congrArg
  have hCod : twCod (coTwistedArrowOpEquivTwistedArrow.functor.obj (op tw')) =
              coTwDom tw' := coTwistedArrowOpEquiv_obj_cod tw'
  have hDom : twDom (coTwistedArrowOpEquivTwistedArrow.functor.obj (op tw)) =
              coTwCod tw := coTwistedArrowOpEquiv_obj_dom tw
  -- Rewrite using the weight definition to get the cast chain
  simp only [cast_eq]
  -- Now simplify the HomToProf behavior
  change (((HomToProf pt).map (coTwCodArr f).op).app _ ≫
          ((HomToProf pt).obj _).map (coTwDomArr f)) w = coTwCodArr f ≫ w
  -- Expand the composition in Type
  change ((HomToProf pt).obj (op (coTwCod tw))).map (coTwDomArr f)
       (((HomToProf pt).map (coTwCodArr f).op).app (coTwDom tw') w) =
       coTwCodArr f ≫ w
  -- HomToProf_obj_map: ((HomToProf pt).obj A).map g h = h
  rw [HomToProf_obj_map]
  -- Now the goal is: ((HomToProf pt).map (coTwCodArr f).op).app (coTwDom tw') w = coTwCodArr f ≫ w
  -- HomToProf_map_app: ((HomToProf pt).map f).app B h = f.unop ≫ h
  rw [HomToProf_map_app, Quiver.Hom.unop_op]

/-!
### Naturality of the extension

The extended legs satisfy weighted cocone naturality. For a morphism
`f : tw ⟶ tw'` in CoTwistedArrow C:

  (profunctorOnCoTwistedArrow C G).map f ≫ extendMendlerLeg tw' w
    = extendMendlerLeg tw (weight.map f.op w)

The proof relies on:
1. For HomToProf, weight transport along `f.op` is precomposition by `coTwCodArr f`
   (proven in `HomToProf_weight_map_eq`)
2. The co-twisted arrow commutator:
   `coTwCodArr f ≫ coTwArr tw' ≫ coTwDomArr f = coTwArr tw`
3. The dinaturality of the restricted cowedge
-/

/-- For HomToProf, the weight map along a CoTwistedArrow morphism equals
precomposition by coTwCodArr f. This is a direct computation without casts. -/
theorem HomToProf_weight_map_eq' (pt : C) {tw tw' : CoTwistedArrow C}
    (f : tw ⟶ tw') (γ : coTwCod tw' ⟶ pt) :
    (profunctorOnOpCoTwistedArrow C (HomToProf pt)).map f.op γ =
    coTwCodArr f ≫ γ := by
  simp only [profunctorOnOpCoTwistedArrow_map, profunctorOnTwistedArrow_map]
  simp only [coTwistedArrowOpEquiv_map_twDomArr, coTwistedArrowOpEquiv_map_twCodArr]
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  -- The composition in Type v is function composition
  simp only [types_comp_apply]
  rw [HomToProf_obj_map, HomToProf_map_app, Quiver.Hom.unop_op]

/-- The extended legs satisfy weighted cocone naturality. -/
theorem extendMendlerLeg_natural (pt : C) (rc : RestrictedCowedgeOver G (HomToProf pt) pt)
    {tw tw' : CoTwistedArrow C} (f : tw ⟶ tw')
    (w' : (profunctorOnOpCoTwistedArrow C (HomToProf pt)).obj (Opposite.op tw')) :
    (profunctorOnCoTwistedArrow C G).map f ≫ extendMendlerLeg (G := G) pt rc tw' w' =
    extendMendlerLeg (G := G) pt rc tw
      ((profunctorOnOpCoTwistedArrow C (HomToProf pt)).map f.op w') := by
  -- Unfold the extended legs and diagram map
  unfold extendMendlerLeg
  rw [profunctorOnCoTwistedArrow_map]
  -- Simplify and normalize - eliminate eqToHom casts and let bindings
  simp only [eqToHom_refl, Category.id_comp, Category.assoc, cast_eq]
  -- Use the weight transport lemma on the RHS
  rw [HomToProf_weight_map_eq' pt f]
  -- The goal is now about rc.family at different positions
  -- Use the co-twisted arrow commutator: coTwCodArr f ≫ coTwArr tw' ≫ coTwDomArr f = coTwArr tw
  have comm := coTwHomComm f
  rw [← comm]
  simp only [op_comp, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  -- Use naturality of G.map (coTwArr tw') - it's a natural transformation
  have nat_arr := (G.map (coTwArr tw').op).naturality (coTwCodArr f)
  -- Goal: (G.map domArr).app cod ≫ G.obj.map codArr ≫ (G.map arr').app cod' ≫ family
  --     = (G.map domArr).app cod ≫ (G.map arr').app cod ≫ (G.map codArr).app cod ≫ family
  -- First use congr to match the first morphism
  congr 1
  -- Now goal: G.obj.map codArr ≫ (G.map arr').app cod' ≫ family w'
  --         = (G.map arr').app cod ≫ (G.map codArr).app cod ≫ family (codArr ≫ w')
  -- Use naturality of G.map (coTwArr tw') to swap
  calc (G.obj (op (coTwDom tw'))).map (coTwCodArr f) ≫
       (G.map (coTwArr tw').op).app (coTwCod tw') ≫ rc.family (coTwCod tw') w'
    = (G.map (coTwArr tw').op).app (coTwCod tw) ≫
      (G.obj (op (coTwCod tw'))).map (coTwCodArr f) ≫ rc.family (coTwCod tw') w' := by
        rw [← Category.assoc, nat_arr, Category.assoc]
  _ = (G.map (coTwArr tw').op).app (coTwCod tw) ≫
      (G.map (coTwCodArr f).op).app (coTwCod tw) ≫ rc.family (coTwCod tw) (coTwCodArr f ≫ w') := by
        congr 1
        -- Use dinaturality of rc.family with g = coTwCodArr f
        have dinat := rc.isDinatural (coTwCod tw) (coTwCod tw') (coTwCodArr f) w'
        simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor_obj_map,
          sliceProfunctor_map_app, Quiver.Hom.unop_op, HomToProf_map_app,
          HomToProf_obj_map] at dinat
        exact dinat

/-- Extends a restricted cowedge to a weighted cowedge over the same point.
This is the inverse direction of `restrictWeightedCowedge` for `HomToProf`. -/
def extendRestrictedCowedge (pt : C) (rc : RestrictedCowedgeOver G (HomToProf pt) pt) :
    WeightedCowedgeOver (HomToProf pt) G pt where
  app := fun tw => extendMendlerLeg (G := G) pt rc tw.unop
  naturality := fun tw tw' f => by
    ext w
    simp only [types_comp_apply]
    -- f : tw ⟶ tw' in (CoTwistedArrow C)ᵒᵖ
    -- f.unop : tw'.unop ⟶ tw.unop in CoTwistedArrow C
    -- extendMendlerLeg_natural gives:
    --   D.map f.unop ≫ leg (tw.unop) w = leg (tw.unop) (W.map f w)
    -- homToFunctor.map f gives: D.map f.unop ≫ -
    -- So we need symm to get the right equation
    exact (extendMendlerLeg_natural (G := G) pt rc f.unop w).symm

/-- Extends a restricted cowedge to a weighted cowedge (bundled with point). -/
def extendRestrictedCowedgeFull (pt : C)
    (rc : RestrictedCowedgeOver G (HomToProf pt) pt) :
    WeightedCowedge (HomToProf pt) G :=
  ⟨pt, extendRestrictedCowedge (G := G) pt rc⟩

/-- Naturality for the generalized extended leg with separate weight and apex. -/
theorem extendMendlerLeg'_natural (wpt apt : C)
    (rc : RestrictedCowedgeOver G (HomToProf wpt) apt)
    {tw tw' : CoTwistedArrow C} (f : tw ⟶ tw')
    (w' : (profunctorOnOpCoTwistedArrow C (HomToProf wpt)).obj (Opposite.op tw')) :
    (profunctorOnCoTwistedArrow C G).map f ≫
      extendMendlerLeg' (G := G) wpt apt rc tw' w' =
    extendMendlerLeg' (G := G) wpt apt rc tw
      ((profunctorOnOpCoTwistedArrow C (HomToProf wpt)).map f.op w') := by
  unfold extendMendlerLeg'
  rw [profunctorOnCoTwistedArrow_map]
  simp only [eqToHom_refl, Category.id_comp, Category.assoc, cast_eq]
  rw [HomToProf_weight_map_eq' wpt f]
  have comm := coTwHomComm f
  rw [← comm]
  simp only [op_comp, Functor.map_comp, NatTrans.comp_app, Category.assoc]
  have nat_arr := (G.map (coTwArr tw').op).naturality (coTwCodArr f)
  congr 1
  calc (G.obj (op (coTwDom tw'))).map (coTwCodArr f) ≫
       (G.map (coTwArr tw').op).app (coTwCod tw') ≫ rc.family (coTwCod tw') w'
    = (G.map (coTwArr tw').op).app (coTwCod tw) ≫
      (G.obj (op (coTwCod tw'))).map (coTwCodArr f) ≫ rc.family (coTwCod tw') w' := by
        rw [← Category.assoc, nat_arr, Category.assoc]
  _ = (G.map (coTwArr tw').op).app (coTwCod tw) ≫
      (G.map (coTwCodArr f).op).app (coTwCod tw) ≫
        rc.family (coTwCod tw) (coTwCodArr f ≫ w') := by
        congr 1
        have dinat := rc.isDinatural (coTwCod tw) (coTwCod tw') (coTwCodArr f) w'
        simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor_obj_map,
          sliceProfunctor_map_app, Quiver.Hom.unop_op, HomToProf_map_app,
          HomToProf_obj_map] at dinat
        exact dinat

/-- Generalized extension with separate weight point and apex point. -/
def extendRestrictedCowedge' (wpt apt : C)
    (rc : RestrictedCowedgeOver G (HomToProf wpt) apt) :
    WeightedCowedgeOver (HomToProf wpt) G apt where
  app := fun tw => extendMendlerLeg' (G := G) wpt apt rc tw.unop
  naturality := fun tw tw' f => by
    ext w
    simp only [types_comp_apply]
    exact (extendMendlerLeg'_natural (G := G) wpt apt rc f.unop w).symm

/-- Generalized extension bundled with apex point. -/
def extendRestrictedCowedgeFull' (wpt : C) (rc : RestrictedCowedge G (HomToProf wpt)) :
    WeightedCowedge (HomToProf wpt) G :=
  ⟨rc.pt, extendRestrictedCowedge' (G := G) wpt rc.pt rc.toRestrictedCowedgeOver⟩

/-- At an identity co-twisted arrow, the extended leg reduces to the original
family (up to canonical casts). -/
theorem extendMendlerLeg_at_identity (pt : C)
    (rc : RestrictedCowedgeOver G (HomToProf pt) pt) (A : C)
    (γ : (profunctorOnOpCoTwistedArrow C (HomToProf pt)).obj
      (Opposite.op (idCoTwistedArrow A))) :
    diagonalToIdentityHom G A ≫
      extendMendlerLeg (G := G) pt rc (idCoTwistedArrow A) γ =
    rc.family A (weightAtIdentityToDiagApp (HomToProf pt) A γ) := by
  unfold extendMendlerLeg idCoTwistedArrow
  simp only [coTwObjMk_arr, coTwObjMk_cod, coTwObjMk_dom]
  simp only [op_id, Functor.map_id, NatTrans.id_app]
  simp only [diagonalToIdentityHom, profunctorOnCoTwistedArrow_at_identity,
    eqToHom_refl, Category.id_comp]
  simp only [weightAtIdentityToDiagApp, cast_eq]
  exact Category.id_comp _

/-- The extend-restrict round-trip is the identity on RestrictedCowedgeOver. -/
theorem restrict_extend_roundtrip (pt : C)
    (rc : RestrictedCowedgeOver G (HomToProf pt) pt) :
    (restrictWeightedCowedge (HomToProf pt) G
      (extendRestrictedCowedgeFull (G := G) pt rc)).toRestrictedCowedgeOver = rc := by
  apply RestrictedCowedgeOver.ext
  funext A h
  simp only [restrictWeightedCowedge, weightedCowedgeFamilyAtIdentity,
    extendRestrictedCowedgeFull, extendRestrictedCowedge, WeightedCocone.leg]
  rw [extendMendlerLeg_at_identity (G := G)]
  simp only [weightAtIdentityToDiagApp_diagAppToWeightAtIdentity]

/-- Generalized identity lemma with separate weight and apex points. -/
theorem extendMendlerLeg'_at_identity (wpt apt : C)
    (rc : RestrictedCowedgeOver G (HomToProf wpt) apt) (A : C)
    (γ : (profunctorOnOpCoTwistedArrow C (HomToProf wpt)).obj
      (Opposite.op (idCoTwistedArrow A))) :
    diagonalToIdentityHom G A ≫
      extendMendlerLeg' (G := G) wpt apt rc (idCoTwistedArrow A) γ =
    rc.family A (weightAtIdentityToDiagApp (HomToProf wpt) A γ) := by
  unfold extendMendlerLeg' idCoTwistedArrow
  simp only [coTwObjMk_arr, coTwObjMk_cod, coTwObjMk_dom]
  simp only [op_id, Functor.map_id, NatTrans.id_app]
  simp only [diagonalToIdentityHom, profunctorOnCoTwistedArrow_at_identity,
    eqToHom_refl, Category.id_comp]
  simp only [weightAtIdentityToDiagApp, cast_eq]
  exact Category.id_comp _

/-- Generalized restrict-extend round-trip. -/
theorem restrict_extend_roundtrip' (wpt : C) (rc : RestrictedCowedge G (HomToProf wpt)) :
    restrictWeightedCowedge (HomToProf wpt) G
      (extendRestrictedCowedgeFull' (G := G) wpt rc) = rc := by
  apply RestrictedCowedge.ext
  · rfl
  · apply heq_of_eq
    apply RestrictedCowedgeOver.ext
    funext A h
    simp only [restrictWeightedCowedge, weightedCowedgeFamilyAtIdentity,
      extendRestrictedCowedgeFull', extendRestrictedCowedge', WeightedCocone.leg]
    rw [extendMendlerLeg'_at_identity (G := G)]
    simp only [weightAtIdentityToDiagApp_diagAppToWeightAtIdentity]

/-- The extended leg at any co-twisted arrow matches the original leg
when starting from a weighted cowedge. This follows from the uniqueness
of extension: the naturality condition forces the leg to be the
composition `(G.map arr.op).app cod ≫ family cod`. -/
-- Helper theorem for the canonical form where tw = coTwObjMk arr
theorem extendMendlerLeg_eq_original_leg_at_coTwObjMk (pt : C)
    (wc : WeightedCoconeOver (profunctorOnOpCoTwistedArrow C (HomToProf pt))
      (profunctorOnCoTwistedArrow C G) pt)
    {cod dom : C} (arr : cod ⟶ dom)
    (γ : (profunctorOnOpCoTwistedArrow C (HomToProf pt)).obj
      (Opposite.op (coTwObjMk arr))) :
    let rc := (restrictWeightedCowedge (HomToProf pt) G
      ⟨pt, wc⟩).toRestrictedCowedgeOver
    extendMendlerLeg (G := G) pt rc (coTwObjMk arr) γ =
    wc.app (Opposite.op (coTwObjMk arr)) γ := by
  intro rc
  unfold extendMendlerLeg
  simp only [coTwObjMk_cod, coTwObjMk_dom, coTwObjMk_arr]
  -- Use weighted cocone naturality with coTwToIdentityAtSource
  have nat := wc.naturality (coTwToIdentityAtSource arr).op
  have natγ := congrFun nat γ
  simp only [types_comp_apply] at natγ
  -- For HomToProf, W.map (coTwToIdentityAtSource arr).op γ = γ
  have weight_map_eq : (profunctorOnOpCoTwistedArrow C (HomToProf pt)).map
      (coTwToIdentityAtSource arr).op γ = γ := by
    simp only [profunctorOnOpCoTwistedArrow_map, profunctorOnTwistedArrow_map,
      equiv_map_coTwToIdentityAtSource_twDomArr, equiv_map_coTwToIdentityAtSource_twCodArr]
    simp only [types_comp_apply]
    simp only [HomToProf_map_app, Quiver.Hom.unop_op, HomToProf_obj_map]
    exact Category.id_comp γ
  rw [weight_map_eq] at natγ
  -- homToFunctor map is precomposition by diagram map
  have homToFunctor_map_form :
      (homToFunctor (profunctorOnCoTwistedArrow C G) pt).map
        (coTwToIdentityAtSource arr).op
        (wc.app (Opposite.op (idCoTwistedArrow cod)) γ) =
      (profunctorOnCoTwistedArrow C G).map (coTwToIdentityAtSource arr) ≫
        wc.app (Opposite.op (idCoTwistedArrow cod)) γ := rfl
  rw [homToFunctor_map_form] at natγ
  rw [diagram_map_coTwToIdentityAtSource] at natγ
  -- natγ: wc.ι(coTwObjMk arr) γ = (G.map arr.op).app cod ≫ wc.ι(id_cod) γ
  rw [natγ]
  -- Show our formula equals (G.map arr.op).app cod ≫ wc.ι(id_cod) γ
  unfold rc restrictWeightedCowedge weightedCowedgeFamilyAtIdentity
  simp only [eqToHom_refl, Category.id_comp]
  congr 1
  simp only [profunctorOnCoTwistedArrow_at_identity]
  simp only [diagAppToWeightAtIdentity, cast_eq]
  -- Need to unfold diagonalToIdentityHom and leg
  simp only [diagonalToIdentityHom, WeightedCocone.leg]
  -- The structure { pt := pt, toWeightedCoconeOver := wc } has
  -- toWeightedCoconeOver = wc
  have h : ({ pt := pt, toWeightedCoconeOver := wc } :
    WeightedCocone (profunctorOnOpCoTwistedArrow C (HomToProf pt))
      (profunctorOnCoTwistedArrow C G)).ι = wc := rfl
  rw [h]
  exact Category.id_comp _

-- General theorem using the canonical form
theorem extendMendlerLeg_eq_original_leg (pt : C)
    (wc : WeightedCoconeOver (profunctorOnOpCoTwistedArrow C (HomToProf pt))
      (profunctorOnCoTwistedArrow C G) pt)
    (tw : CoTwistedArrow C)
    (γ : (profunctorOnOpCoTwistedArrow C (HomToProf pt)).obj (Opposite.op tw)) :
    let rc := (restrictWeightedCowedge (HomToProf pt) G
      ⟨pt, wc⟩).toRestrictedCowedgeOver
    extendMendlerLeg (G := G) pt rc tw γ =
    wc.app (Opposite.op tw) γ := by
  intro rc
  -- A co-twisted arrow is definitionally a triple (cod, dom, arr : cod ⟶ dom)
  -- represented as coTwObjMk arr
  -- Use the specific case theorem which handles the canonical form
  have h := coTw_eq_coTwObjMk tw
  -- Revert γ and tw to substitute together
  revert γ
  rw [h]
  intro γ
  exact extendMendlerLeg_eq_original_leg_at_coTwObjMk (G := G) pt wc (coTwArr tw) γ

/-- The extend-restrict round-trip is the identity on weighted cowedges
with point pt. Starting from a weighted cowedge, restricting to diagonal,
and then extending gives back the original cowedge. -/
theorem extend_restrict_roundtrip (pt : C)
    (wc : WeightedCoconeOver (profunctorOnOpCoTwistedArrow C (HomToProf pt))
      (profunctorOnCoTwistedArrow C G) pt) :
    (extendRestrictedCowedgeFull (G := G) pt
      (restrictWeightedCowedge (HomToProf pt) G ⟨pt, wc⟩).toRestrictedCowedgeOver
    ).toWeightedCoconeOver = wc := by
  ext tw γ
  simp only [extendRestrictedCowedgeFull, extendRestrictedCowedge]
  exact extendMendlerLeg_eq_original_leg (G := G) pt wc tw.unop γ

/-- Helper for extend_restrict_roundtrip': proves equality at coTwObjMk. -/
theorem extendMendlerLeg'_eq_original_leg_at_coTwObjMk (wpt : C)
    (wc : WeightedCowedge (HomToProf wpt) G)
    {cod dom : C} (arr : cod ⟶ dom)
    (γ : (profunctorOnOpCoTwistedArrow C (HomToProf wpt)).obj
      (Opposite.op (coTwObjMk arr))) :
    let rc := (restrictWeightedCowedge (HomToProf wpt) G
      wc).toRestrictedCowedgeOver
    extendMendlerLeg' (G := G) wpt wc.pt rc (coTwObjMk arr) γ =
    wc.toWeightedCoconeOver.app (Opposite.op (coTwObjMk arr)) γ := by
  intro rc
  -- Use weighted cocone naturality with coTwToIdentityAtSource
  have nat := wc.toWeightedCoconeOver.naturality (coTwToIdentityAtSource arr).op
  have natγ := congrFun nat γ
  simp only [types_comp_apply] at natγ
  -- For HomToProf, W.map (coTwToIdentityAtSource arr).op γ = γ
  have weight_map_eq : (profunctorOnOpCoTwistedArrow C (HomToProf wpt)).map
      (coTwToIdentityAtSource arr).op γ = γ := by
    simp only [profunctorOnOpCoTwistedArrow_map, profunctorOnTwistedArrow_map,
      equiv_map_coTwToIdentityAtSource_twDomArr, equiv_map_coTwToIdentityAtSource_twCodArr]
    simp only [types_comp_apply]
    simp only [HomToProf_map_app, Quiver.Hom.unop_op, HomToProf_obj_map]
    exact Category.id_comp γ
  rw [weight_map_eq] at natγ
  -- homToFunctor map is precomposition by diagram map
  have homToFunctor_map_form :
      (homToFunctor (profunctorOnCoTwistedArrow C G) wc.pt).map
        (coTwToIdentityAtSource arr).op
        (wc.toWeightedCoconeOver.app (Opposite.op (idCoTwistedArrow cod)) γ) =
      (profunctorOnCoTwistedArrow C G).map (coTwToIdentityAtSource arr) ≫
        wc.toWeightedCoconeOver.app (Opposite.op (idCoTwistedArrow cod)) γ := rfl
  rw [homToFunctor_map_form] at natγ
  rw [diagram_map_coTwToIdentityAtSource] at natγ
  -- natγ: wc.ι(coTwObjMk arr) γ = (G.map arr.op).app cod ≫ wc.ι(id_cod) γ
  rw [natγ]
  -- Show our formula equals (G.map arr.op).app cod ≫ wc.ι(id_cod) γ
  unfold extendMendlerLeg' rc restrictWeightedCowedge weightedCowedgeFamilyAtIdentity
  simp only [eqToHom_refl, Category.id_comp, cast_eq]
  congr 1
  simp only [profunctorOnCoTwistedArrow_at_identity]
  simp only [diagAppToWeightAtIdentity]
  simp only [diagonalToIdentityHom, WeightedCocone.leg]
  exact Category.id_comp _

/-- Generalized version of extendMendlerLeg_eq_original_leg. -/
theorem extendMendlerLeg'_eq_original_leg (wpt : C)
    (wc : WeightedCowedge (HomToProf wpt) G)
    (tw : CoTwistedArrow C)
    (γ : (profunctorOnOpCoTwistedArrow C (HomToProf wpt)).obj (Opposite.op tw)) :
    let rc := (restrictWeightedCowedge (HomToProf wpt) G wc).toRestrictedCowedgeOver
    extendMendlerLeg' (G := G) wpt wc.pt rc tw γ =
    wc.toWeightedCoconeOver.app (Opposite.op tw) γ := by
  intro rc
  have h := coTw_eq_coTwObjMk tw
  revert γ
  rw [h]
  intro γ
  exact extendMendlerLeg'_eq_original_leg_at_coTwObjMk (G := G) wpt wc (coTwArr tw) γ

/-- Generalized extend-restrict round-trip for arbitrary apex. -/
theorem extend_restrict_roundtrip' (wpt : C) (wc : WeightedCowedge (HomToProf wpt) G) :
    extendRestrictedCowedgeFull' (G := G) wpt
      (restrictWeightedCowedge (HomToProf wpt) G wc) = wc := by
  apply WeightedCocone.ext
  · rfl
  · apply heq_of_eq
    ext tw γ
    simp only [extendRestrictedCowedgeFull', extendRestrictedCowedge']
    exact extendMendlerLeg'_eq_original_leg (G := G) wpt wc tw.unop γ

/-- Restriction from weighted Mendler cowedge to Mendler algebra.
This extracts the diagonal data from a weighted cowedge by composing
`restrictWeightedCowedge` with `restrictedCowedgeToMendler`. -/
def weightedMendlerToMendler (pt : C) (wc : WeightedMendlerCowedge G pt)
    (hpt : wc.pt = pt) : MendlerAlgebra G :=
  let rc := restrictWeightedCowedge (HomToProf pt) G wc
  restrictedCowedgeToMendler G pt rc hpt

end WeightedCowedgeCorrespondence

section MendlerLambekCorrespondence

/-!
## The G^e Functor and Mendler-Lambek Correspondence

Following Vene's thesis (Section 5.5), we define the functor G^e that
mediates between Mendler-style algebras and conventional algebras.

For an endodifunctor G : Cᵒᵖ ⥤ C ⥤ C, assume that for every object pt,
there exists a (HomToProf pt)-restricted G-coend. Then:

- `G^e(pt) = (restrictedCoend G (HomToProf pt)).pt`
- `G^e(h : pt₁ → pt₂)` is defined via the universal property

The correspondence is:
- `floor(Φ)` : MendlerAlg → ConventionalAlg (the universal morphism)
- `ceil(φ)` : ConventionalAlg → MendlerAlg (composition with injection)

Theorem 5.19: These form an isomorphism of categories.
-/

variable {C : Type u} [Category.{v} C]
variable (G : Cᵒᵖ ⥤ C ⥤ C)

/-- For G^e to be defined, we need (HomToProf pt)-restricted G-coends
to exist for all objects pt. This class bundles this assumption. -/
class HasAllHomToProfCoends where
  hasCoend : ∀ (pt : C), HasRestrictedCoend G (HomToProf pt)

namespace HasAllHomToProfCoends

open HasRestrictedCoend

variable [HasAllHomToProfCoends G]

instance instHasRestrictedCoend (pt : C) : HasRestrictedCoend G (HomToProf pt) :=
  HasAllHomToProfCoends.hasCoend pt

/-- The object part of G^e: the carrier of the restricted coend. -/
def GExtObj (pt : C) : C :=
  (restrictedCoend G (HomToProf pt)).pt

/-- The injection family for the restricted coend at pt. -/
def GExtInj (pt : C) (A : C) (γ : A ⟶ pt) :
    (G.obj (Opposite.op A)).obj A ⟶ GExtObj G pt :=
  (restrictedCoend G (HomToProf pt)).family A γ

/-- The universal morphism from restricted coend to any cowedge. -/
def GExtDesc (pt : C) (d : RestrictedCowedge G (HomToProf pt)) :
    GExtObj G pt ⟶ d.pt :=
  (restrictedCoendIsInitial G (HomToProf pt)).descHom d

/-- Given h : pt₁ → pt₂, construct a (HomToProf pt₁)-restricted cowedge
with carrier G^e(pt₂). The family is: for γ : A → pt₁, compose with
the injection at pt₂. -/
def GExtMapCowedge (pt₁ pt₂ : C) (h : pt₁ ⟶ pt₂) :
    RestrictedCowedge G (HomToProf pt₁) where
  pt := GExtObj G pt₂
  toRestrictedCowedgeOver := ⟨fun A γ => GExtInj G pt₂ A (γ ≫ h), by
    intro A B g x
    have dinat := (restrictedCoend G (HomToProf pt₂)).isDinatural A B g (x ≫ h)
    simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor,
      HomToProf_map_app, HomToProf_obj_map, GExtInj, Category.assoc] at dinat ⊢
    exact dinat⟩

/-- The morphism part of G^e: uses the universal property. -/
def GExtMap (pt₁ pt₂ : C) (h : pt₁ ⟶ pt₂) :
    GExtObj G pt₁ ⟶ GExtObj G pt₂ :=
  GExtDesc G pt₁ (GExtMapCowedge G pt₁ pt₂ h)

/-- G^e preserves identity: G^e(id) = id.
Uses uniqueness of the universal morphism from a coend.

The identity on GExtObj G pt and GExtMap G pt pt (𝟙 pt) both satisfy the
same commutativity condition with respect to the coend injection. -/
theorem GExtMap_id (pt : C) :
    GExtMap G pt pt (𝟙 pt) = 𝟙 (GExtObj G pt) := by
  let hmorphId : (restrictedCoend G (HomToProf pt)) ⟶
      (GExtMapCowedge G pt pt (𝟙 pt)) := {
    hom := 𝟙 (GExtObj G pt)
    comm := fun A γ => by
      simp only [GExtMapCowedge, RestrictedCowedge.family, GExtInj, Category.comp_id]
      exact Category.comp_id _
  }
  have heq : hmorphId = (restrictedCoendIsInitial G (HomToProf pt)).to _ :=
    (restrictedCoendIsInitial G (HomToProf pt)).hom_ext hmorphId _
  simp only [GExtMap, GExtDesc, IsRestrictedCoend.descHom, IsRestrictedCoend.desc]
  have step := congrArg RestrictedCowedge.Hom.hom heq.symm
  simp only at step
  exact step

/-- G^e preserves composition: G^e(g ∘ f) = G^e(g) ∘ G^e(f).
Uses uniqueness of the universal morphism. -/
theorem GExtMap_comp (pt₁ pt₂ pt₃ : C) (f : pt₁ ⟶ pt₂) (g : pt₂ ⟶ pt₃) :
    GExtMap G pt₁ pt₃ (f ≫ g) = GExtMap G pt₁ pt₂ f ≫ GExtMap G pt₂ pt₃ g := by
  let hmorphComp : (restrictedCoend G (HomToProf pt₁)) ⟶
      (GExtMapCowedge G pt₁ pt₃ (f ≫ g)) := {
    hom := GExtMap G pt₁ pt₂ f ≫ GExtMap G pt₂ pt₃ g
    comm := fun A γ => by
      simp only [GExtMap, GExtDesc, IsRestrictedCoend.descHom, IsRestrictedCoend.desc,
        GExtMapCowedge, RestrictedCowedge.family, GExtInj]
      have h1 := ((restrictedCoendIsInitial G (HomToProf pt₁)).to
        (GExtMapCowedge G pt₁ pt₂ f)).comm A γ
      have h2 := ((restrictedCoendIsInitial G (HomToProf pt₂)).to
        (GExtMapCowedge G pt₂ pt₃ g)).comm A (γ ≫ f)
      simp only [GExtMapCowedge, RestrictedCowedge.family, GExtInj] at h1 h2
      rw [← Category.assoc, h1, h2, Category.assoc]
  }
  have heq : hmorphComp =
      (restrictedCoendIsInitial G (HomToProf pt₁)).to (GExtMapCowedge G pt₁ pt₃ (f ≫ g)) :=
    (restrictedCoendIsInitial G (HomToProf pt₁)).hom_ext hmorphComp _
  simp only [GExtMap, GExtDesc, IsRestrictedCoend.descHom, IsRestrictedCoend.desc]
  have step := congrArg RestrictedCowedge.Hom.hom heq.symm
  simp only at step
  exact step

/-- The endofunctor G^e : C ⥤ C.
G^e(pt) is the carrier of the (HomToProf pt)-restricted G-coend. -/
@[simps]
def GExtFunctor : C ⥤ C where
  obj := GExtObj G
  map := GExtMap G _ _
  map_id := GExtMap_id G
  map_comp := GExtMap_comp G _ _ _

end HasAllHomToProfCoends

/-!
## Conventional Algebras and Floor/Ceiling Translations

A conventional F-algebra for an endofunctor F : C ⥤ C is a pair (pt, φ)
where φ : F(pt) ⟶ pt.

We define:
- `ConventionalAlgebra F`: the structure of F-algebras
- `floor`: MendlerAlgebra G → ConventionalAlgebra (GExtFunctor G)
- `ceil`: ConventionalAlgebra (GExtFunctor G) → MendlerAlgebra G
-/

/-- A conventional F-algebra for an endofunctor F : C ⥤ C. -/
abbrev ConventionalAlgebra (F : C ⥤ C) := Endofunctor.Algebra F

abbrev ConventionalAlgebra.pt {F : C ⥤ C} (alg : ConventionalAlgebra F) : C := alg.a

/-- A morphism of conventional F-algebras. -/
abbrev ConventionalAlgebraHom {F : C ⥤ C} (a₁ a₂ : ConventionalAlgebra F) :=
  Endofunctor.Algebra.Hom a₁ a₂

abbrev ConventionalAlgebraHom.hom {F : C ⥤ C} {a₁ a₂ : ConventionalAlgebra F}
    (f : ConventionalAlgebraHom a₁ a₂) : a₁.a ⟶ a₂.a := f.f

abbrev ConventionalAlgebraHom.comm {F : C ⥤ C} {a₁ a₂ : ConventionalAlgebra F}
    (f : ConventionalAlgebraHom a₁ a₂) : F.map f.f ≫ a₂.str = a₁.str ≫ f.f := f.h

abbrev ConventionalAlgebraCat (F : C ⥤ C) : Category (ConventionalAlgebra F) :=
  Endofunctor.Algebra.instCategory F

section FloorCeiling

variable (G : Cᵒᵖ ⥤ C ⥤ C) [HasAllHomToProfCoends G]

open HasRestrictedCoend HasAllHomToProfCoends

/-- The floor translation: converts a Mendler algebra (pt, Φ) to a conventional
G^e-algebra (pt, floor(Φ)) where floor(Φ) is the universal morphism from
the restricted coend to pt. -/
def floor (m : MendlerAlgebra G) :
    ConventionalAlgebra (HasAllHomToProfCoends.GExtFunctor G) where
  a := m.pt
  str := HasAllHomToProfCoends.GExtDesc G m.pt m.toRestrictedCowedge

/-- The ceiling translation: converts a conventional G^e-algebra (pt, φ)
to a Mendler algebra (pt, ceil(φ)) where ceil(φ)_A(γ) = φ ∘ inj_A(γ). -/
def ceil (alg : ConventionalAlgebra (HasAllHomToProfCoends.GExtFunctor G)) :
    MendlerAlgebra G where
  pt := alg.a
  toMendlerAlgebraOver := ⟨⟨fun A γ => HasAllHomToProfCoends.GExtInj G alg.a A γ ≫ alg.str, by
    intro A B g x
    simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor_obj_map,
      sliceProfunctor_map_app, Quiver.Hom.unop_op, HomToProf_map_app, HomToProf_obj_map]
    have dinat := (restrictedCoend G (HomToProf alg.a)).isDinatural A B g x
    simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor_obj_map,
      sliceProfunctor_map_app, Quiver.Hom.unop_op, HomToProf_map_app, HomToProf_obj_map,
      HasAllHomToProfCoends.GExtInj] at dinat ⊢
    simp only [← Category.assoc]
    exact congrArg (· ≫ alg.str) dinat⟩⟩

/-- floor(ceil(φ)) = φ (Proposition 5.15 in Vene).
The floor of the ceiling of a conventional algebra structure is the
original structure. -/
theorem floor_ceil (alg : ConventionalAlgebra (HasAllHomToProfCoends.GExtFunctor G)) :
    floor G (ceil G alg) = alg := by
  cases alg with | mk carrier str =>
  simp only [floor, ceil, MendlerAlgebra.toRestrictedCowedge, MendlerAlgebra.family,
    GExtDesc, GExtInj]
  congr 1
  let targetCowedge : RestrictedCowedge G (HomToProf carrier) :=
    ⟨carrier, ⟨fun A γ => (restrictedCoend G (HomToProf carrier)).family A γ ≫ str,
     (ceil G ⟨carrier, str⟩).isDinatural⟩⟩
  let strMorph : RestrictedCowedge.Hom (restrictedCoend G (HomToProf carrier)) targetCowedge := {
    hom := str
    comm := fun _ _ => rfl
  }
  have huniq := (restrictedCoendIsInitial G (HomToProf carrier)).hom_ext
    ((restrictedCoendIsInitial G (HomToProf carrier)).to targetCowedge) strMorph
  simp only [IsRestrictedCoend.descHom, IsRestrictedCoend.desc]
  exact congrArg RestrictedCowedge.Hom.hom huniq

/-- ceil(floor(Φ)) = Φ (Proposition 5.16 in Vene).
The ceiling of the floor of a Mendler algebra is the original algebra. -/
theorem ceil_floor (m : MendlerAlgebra G) :
    ceil G (floor G m) = m := by
  cases m with | mk pt u =>
  cases u with | mk r =>
  cases r with | mk family isDinat =>
  simp only [ceil, floor, MendlerAlgebra.toRestrictedCowedge, MendlerAlgebra.family,
    GExtDesc, GExtInj]
  congr 1
  apply MendlerAlgebraOver.ext
  apply RestrictedCowedgeOver.ext
  funext A γ
  exact ((restrictedCoendIsInitial G (HomToProf pt)).to
    ⟨pt, ⟨family, isDinat⟩⟩).comm A γ

/-- floor preserves morphisms (Proposition 5.18 in Vene).
If h is a Mendler algebra morphism, then h is a conventional G^e-algebra
morphism between the floor algebras. -/
def floorHom {m₁ m₂ : MendlerAlgebra G} (f : m₁ ⟶ m₂) :
    floor G m₁ ⟶ floor G m₂ where
  f := f.hom
  h := by
    simp only [floor, GExtFunctor_map, GExtMap, GExtDesc, GExtMapCowedge,
      MendlerAlgebra.toRestrictedCowedge, IsRestrictedCoend.descHom, IsRestrictedCoend.desc]
    let targetCowedge : RestrictedCowedge G (HomToProf m₁.pt) := {
      pt := m₂.pt
      toRestrictedCowedgeOver := ⟨fun A γ => m₂.family A (γ ≫ f.hom), by
        intro A B g x
        have hdinat := m₂.isDinatural A B g (x ≫ f.hom)
        simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor,
          HomToProf_map_app, HomToProf_obj_map, Category.assoc] at hdinat ⊢
        exact hdinat⟩
    }
    let lhsMorph : RestrictedCowedge.Hom (restrictedCoend G (HomToProf m₁.pt)) targetCowedge := {
      hom := (restrictedCoendIsInitial G (HomToProf m₁.pt)).descHom
          (GExtMapCowedge G m₁.pt m₂.pt f.hom) ≫
        (restrictedCoendIsInitial G (HomToProf m₂.pt)).descHom m₂.toRestrictedCowedge
      comm := fun A γ => by
        simp only [IsRestrictedCoend.descHom, IsRestrictedCoend.desc,
          GExtMapCowedge, GExtInj, MendlerAlgebra.toRestrictedCowedge]
        have h1 := (restrictedCoendIsInitial G (HomToProf m₁.pt)).to
          (GExtMapCowedge G m₁.pt m₂.pt f.hom) |>.comm A γ
        simp only [GExtMapCowedge, GExtInj] at h1
        simp only [← Category.assoc]
        rw [h1]
        have h2 := (restrictedCoendIsInitial G (HomToProf m₂.pt)).to
          m₂.toRestrictedCowedge |>.comm A (γ ≫ f.hom)
        simp only [MendlerAlgebra.toRestrictedCowedge] at h2
        exact h2
    }
    let rhsMorph : RestrictedCowedge.Hom (restrictedCoend G (HomToProf m₁.pt)) targetCowedge := {
      hom := (restrictedCoendIsInitial G (HomToProf m₁.pt)).descHom
          m₁.toRestrictedCowedge ≫ f.hom
      comm := fun A γ => by
        simp only [IsRestrictedCoend.descHom, IsRestrictedCoend.desc,
          MendlerAlgebra.toRestrictedCowedge]
        have h1 := (restrictedCoendIsInitial G (HomToProf m₁.pt)).to
          m₁.toRestrictedCowedge |>.comm A γ
        simp only [MendlerAlgebra.toRestrictedCowedge] at h1
        simp only [← Category.assoc]
        rw [h1]
        exact f.comm A γ
    }
    have huniq := (restrictedCoendIsInitial G (HomToProf m₁.pt)).hom_ext lhsMorph rhsMorph
    exact congrArg RestrictedCowedge.Hom.hom huniq

/-- ceil preserves morphisms (Proposition 5.17 in Vene).
If h is a conventional G^e-algebra morphism, then h is a Mendler algebra
morphism between the ceiling algebras. -/
def ceilHom {a₁ a₂ : ConventionalAlgebra (HasAllHomToProfCoends.GExtFunctor G)}
    (f : a₁ ⟶ a₂) : ceil G a₁ ⟶ ceil G a₂ where
  hom := f.f
  comm := by
    intro A γ
    simp only [ceil, MendlerAlgebra.family, MendlerAlgebraOver.family, GExtInj]
    have hcomm := f.h
    simp only [GExtFunctor_map, GExtMap, GExtDesc, GExtMapCowedge,
      IsRestrictedCoend.descHom, IsRestrictedCoend.desc] at hcomm
    rw [Category.assoc, ← hcomm, ← Category.assoc]
    have hstep := (restrictedCoendIsInitial G (HomToProf a₁.a)).to
      (GExtMapCowedge G a₁.a a₂.a f.f) |>.comm A γ
    simp only [GExtMapCowedge, RestrictedCowedge.family, GExtInj] at hstep ⊢
    rw [hstep]

/-- The floor functor: MendlerAlgebra G ⥤ ConventionalAlgebra (GExtFunctor G). -/
@[simps]
def floorFunctor : MendlerAlgebra G ⥤
    ConventionalAlgebra (HasAllHomToProfCoends.GExtFunctor G) where
  obj := floor G
  map := floorHom G
  map_id := fun _ => Endofunctor.Algebra.Hom.ext rfl
  map_comp := fun _ _ => Endofunctor.Algebra.Hom.ext rfl

/-- The ceiling functor: ConventionalAlgebra (GExtFunctor G) ⥤ MendlerAlgebra G. -/
@[simps]
def ceilFunctor : ConventionalAlgebra (HasAllHomToProfCoends.GExtFunctor G) ⥤
    MendlerAlgebra G where
  obj := ceil G
  map := ceilHom G
  map_id := fun _ => MendlerAlgebraHom.ext rfl
  map_comp := fun _ _ => MendlerAlgebraHom.ext rfl

/-- The .f component of eqToHom in ConventionalAlgebra is eqToHom in C. -/
@[simp]
theorem ConventionalAlgebra.eqToHom_f {F : C ⥤ C} {alg₁ alg₂ : ConventionalAlgebra F}
    (h : alg₁ = alg₂) : (eqToHom h).f = eqToHom (congrArg Endofunctor.Algebra.a h) := by
  subst h
  rfl

/-- The .hom component of eqToHom in MendlerAlgebra is eqToHom in C. -/
@[simp]
theorem MendlerAlgebra.eqToHom_hom' {G' : Cᵒᵖ ⥤ C ⥤ C} {m₁ m₂ : MendlerAlgebra G'}
    (h : m₁ = m₂) : (eqToHom h).hom = eqToHom (congrArg MendlerAlgebra.pt h) := by
  subst h
  rfl

/-- floor ∘ ceil = id on the conventional algebra category. -/
theorem floorFunctor_comp_ceilFunctor :
    ceilFunctor G ⋙ floorFunctor G = 𝟭 _ :=
  Functor.ext (floor_ceil G) (fun a₁ a₂ f => by
    simp only [Functor.comp_map, Functor.id_map, floorFunctor_map, ceilFunctor_map]
    apply Endofunctor.Algebra.Hom.ext
    simp only [floorHom, ceilHom]
    have heq1 : congrArg Endofunctor.Algebra.a (floor_ceil G a₁) = rfl := rfl
    have heq2 : congrArg Endofunctor.Algebra.a (floor_ceil G a₂).symm = rfl := rfl
    rw [show (eqToHom (floor_ceil G a₁) ≫ f ≫ eqToHom (floor_ceil G a₂).symm).f =
        (eqToHom (floor_ceil G a₁)).f ≫ f.f ≫ (eqToHom (floor_ceil G a₂).symm).f
        from rfl]
    rw [ConventionalAlgebra.eqToHom_f, ConventionalAlgebra.eqToHom_f,
        heq1, heq2, eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id])

/-- ceil ∘ floor = id on the Mendler algebra category. -/
theorem ceilFunctor_comp_floorFunctor :
    floorFunctor G ⋙ ceilFunctor G = 𝟭 _ :=
  Functor.ext (ceil_floor G) (fun m₁ m₂ f => by
    simp only [Functor.comp_map, Functor.id_map, floorFunctor_map, ceilFunctor_map]
    apply MendlerAlgebraHom.ext
    simp only [ceilHom, floorHom]
    have heq1 : congrArg MendlerAlgebra.pt (ceil_floor G m₁) = rfl := rfl
    have heq2 : congrArg MendlerAlgebra.pt (ceil_floor G m₂).symm = rfl := rfl
    rw [show (eqToHom (ceil_floor G m₁) ≫ f ≫ eqToHom (ceil_floor G m₂).symm).hom =
        (eqToHom (ceil_floor G m₁)).hom ≫ f.hom ≫ (eqToHom (ceil_floor G m₂).symm).hom
        from rfl]
    rw [MendlerAlgebra.eqToHom_hom', MendlerAlgebra.eqToHom_hom',
        heq1, heq2, eqToHom_refl, eqToHom_refl, Category.id_comp, Category.comp_id])

/-- The Mendler-Lambek correspondence (Theorem 5.19 in Vene):
The categories of Mendler algebras and conventional G^e-algebras are
isomorphic. -/
def mendlerLambekEquiv :
    MendlerAlgebra G ≌ ConventionalAlgebra (HasAllHomToProfCoends.GExtFunctor G) :=
  CategoryTheory.Equivalence.mk (floorFunctor G) (ceilFunctor G)
    (CategoryTheory.Iso.refl _
      |>.symm.trans (CategoryTheory.eqToIso (ceilFunctor_comp_floorFunctor G).symm))
    (CategoryTheory.eqToIso (floorFunctor_comp_ceilFunctor G))

end FloorCeiling

end MendlerLambekCorrespondence

end GebLean
