import GebLean.RestrictedCoendAsColimit
import GebLean.Utilities.EndsAndCoends
import Mathlib.CategoryTheory.Monoidal.Closed.Basic
import Mathlib.CategoryTheory.Monoidal.Braided.Basic
import Mathlib.CategoryTheory.Limits.Shapes.End

/-!
# Mendler-Lambek Equivalence via Ends and Powers

This module re-expresses the `GExtFunctor` (Vene's `G^e`) using
ends and powers instead of restricted coends.

Starting from
`G^e(pt) = restricted coend of G by HomToProf(pt)`,
the derivation proceeds in three steps:

1. Transfer the restricted coend to a copower-profunctor coend
   (done in `RestrictedCoendAsColimit.lean`).
2. Apply coend-end duality:
   `Hom(coend, Y) ≃ typeEnd (P ⇓ Y)`.
3. Replace copowers with powers inside the end via
   `copowerPowerEquiv`.

The final characterization is:
`Hom(G^e(pt), Y) ≃ ∫_A Hom(G(A,A), Y^(A→pt))`.
-/

namespace GebLean

open CategoryTheory
open CategoryTheory.Limits

universe u v w

/-!
## Coend-End Duality for Initial Cowedges

Given a coend cowedge `c` (initial in `Cowedge P`) for a
`D`-valued profunctor, the hom-set `c.pt ⟶ Y` is
isomorphic to the explicit end `typeEnd (P ⇓ Y)`.
-/

section CoendEndDuality

variable
  {C : Type u} [Category.{v} C]
  {D : Type w} [Category.{v} D]

/-- Coend-end duality for initial cowedges:
given a coend cowedge `c` (initial in `Cowedge P`),
`(c.pt ⟶ Y) ≃ typeEnd (P ⇓ Y)`.

The forward direction uses `homOrdinaryWedge` legs
to build the compatible family. The inverse uses
`Wedge.IsLimit.lift` to recover the morphism from
the universal property. -/
def cowedgeHomEndEquiv
    (P : Cᵒᵖ ⥤ C ⥤ D)
    {c : Cowedge (J := C) (C := D) P}
    (hc : IsInitial c) (Y : D) :
    (c.pt ⟶ Y) ≃ typeEnd (P ⇓ Y) :=
  let tw := homOrdinaryWedge P c Y
  let isLim : IsLimit tw :=
    (Cone.isLimitEquivIsTerminal _).symm
      (homOrdinaryWedge_isTerminal P hc Y)
  { toFun := fun f =>
      ⟨fun j => tw.ι j f,
       fun {i} {j} g =>
        congr_fun (tw.condition g) f⟩
    invFun := fun x =>
      Wedge.IsLimit.lift isLim
        (fun j (_ : PUnit.{v + 1}) => x.val j)
        (by intro i j g
            exact funext (fun _ => x.property g))
        PUnit.unit
    left_inv := fun f₀ => by
      dsimp only []
      have h := Multifork.IsLimit.hom_ext
        (hK := isLim)
        (f := Wedge.IsLimit.lift isLim
          (fun j (_ : PUnit.{v + 1}) =>
            tw.ι j f₀)
          (by intro i j g
              exact funext (fun _ =>
                congr_fun (tw.condition g) f₀)))
        (g := fun _ => f₀)
        (h := fun j => by
          ext u; exact congr_fun
            (Wedge.IsLimit.lift_ι isLim _ _ j)
            u)
      exact congr_fun h PUnit.unit
    right_inv := fun x => by
      apply Subtype.ext; ext j
      exact congr_fun
        (Wedge.IsLimit.lift_ι isLim _ _ j)
        PUnit.unit }

end CoendEndDuality

/-!
## End Formula for GExtFunctor

Apply coend-end duality to the copower-profunctor coend
to express the hom from `CopowerGExtObj` as an explicit
end:
`(CopowerGExtObj G pt ⟶ Y) ≃
  typeEnd (copowerProf (HomToProf pt) G ⇓ Y)`.
-/

section EndFormula

variable
  {C : Type u} [Category.{v} C] [HasCopowers C]
  (G : Cᵒᵖ ⥤ C ⥤ C)
  [HasAllCopowerProfCoends G]

open HasAllCopowerProfCoends

/-- The hom from the copower-profunctor coend carrier
to any `Y` is an explicit end of the slice profunctor.

On the diagonal at `A`, the slice profunctor sends
`A` to `(copower (A ⟶ pt) (G(op A, A)) ⟶ Y)`. -/
def copowerGExtHomEndEquiv (pt Y : C) :
    (CopowerGExtObj G pt ⟶ Y) ≃
      typeEnd
        (copowerProf (HomToProf pt) G ⇓ Y) :=
  cowedgeHomEndEquiv
    (copowerProf (HomToProf pt) G)
    (copowerCoendIsInitial G pt) Y

end EndFormula

/-!
## Power-Slice Profunctor

The profunctor `powerSliceProf G pt Y` sends
`(A, B) ↦ (G(op B, A.unop) ⟶ Y^(B ⟶ pt))`.

On the diagonal `(op j, j)` this gives
`G(op j, j) ⟶ Y^(j ⟶ pt)`.

The structure follows `sliceProfunctor` (the
`P ⇓ Y` notation from `Weighted.lean`), with the
constant target `c` replaced by `Y^(B ⟶ pt)` varying
covariantly in `B`.
-/

section PowerEnd

variable
  {C : Type u} [Category.{v} C]
  [HasCopowers C] [HasPowers C]

/-- The power-slice profunctor: sends
`(A, B) ↦ (G(op B, A.unop) ⟶ Y^(B ⟶ pt))`.

Follows the convention of `sliceProfunctor`:
the outer functor is indexed by `A : Cᵒᵖ` and the
inner by `B : C`. The covariant map (in B) precomposes
with `(G.map g.op).app A.unop` and postcomposes with
`HasPowers.mapIdx (g ≫ ·)`. The contravariant map
(in A, given `f : A₁ ⟶ A₂` in `Cᵒᵖ`) precomposes
with `(G.obj (op B)).map f.unop`. -/
def powerSliceProf
    (G : Cᵒᵖ ⥤ C ⥤ C)
    (pt Y : C) : Cᵒᵖ ⥤ C ⥤ Type v where
  obj A := {
    obj := fun B =>
      (G.obj (Opposite.op B)).obj A.unop ⟶
        HasPowers.power Y (B ⟶ pt)
    map := fun {B₁ B₂} g h =>
      (G.map g.op).app A.unop ≫ h ≫
        HasPowers.mapIdx (g ≫ ·)
    map_id := fun B => by
      ext h
      simp only [types_id_apply, op_id,
        CategoryTheory.Functor.map_id,
        NatTrans.id_app, Category.id_comp]
      erw [HasPowers.mapIdx_id, Category.comp_id]
    map_comp := fun {B₁ B₂ B₃} f g => by
      ext h
      simp only [types_comp_apply, op_comp,
        Functor.map_comp, NatTrans.comp_app,
        Category.assoc]
      congr 1; congr 1; congr 1
      exact HasPowers.mapIdx_comp
        (g ≫ ·) (f ≫ ·)
  }
  map {A₁ A₂} f := {
    app := fun B h =>
      (G.obj (Opposite.op B)).map f.unop ≫ h
    naturality := fun {B₁ B₂} g => by
      ext h
      simp only [types_comp_apply, Category.assoc]
      rw [← Category.assoc
        ((G.obj (Opposite.op B₂)).map f.unop)
        ((G.map g.op).app A₁.unop)]
      rw [(G.map g.op).naturality f.unop]
      simp only [Category.assoc]
  }
  map_id := fun A => by
    ext B h
    simp only [NatTrans.id_app, types_id_apply,
      unop_id, CategoryTheory.Functor.map_id,
      Category.id_comp]
  map_comp := fun {A₁ A₂ A₃} f g => by
    ext B h
    simp only [NatTrans.comp_app, types_comp_apply,
      unop_comp, Functor.map_comp, Category.assoc]

end PowerEnd

/-!
## Copower-Power End Equivalence

The componentwise `copowerPowerEquiv` lifts to an
equivalence on ends:
`typeEnd (copowerProf (HomToProf pt) G ⇓ Y) ≃
  typeEnd (powerSliceProf G pt Y)`.
-/

section EndEquiv

variable
  {C : Type u} [Category.{v} C]
  [HasCopowers C] [HasPowers C]
  (G : Cᵒᵖ ⥤ C ⥤ C) (pt Y : C)

open HasCopowers HasPowers

def endCopowerPowerEquiv :
    typeEnd
      (copowerProf (HomToProf pt) G ⇓ Y) ≃
      typeEnd (powerSliceProf G pt Y) where
  toFun x := ⟨
    fun j => copowerPowerEquiv
      (j ⟶ pt) ((G.obj (Opposite.op j)).obj j) Y
      (x.val j),
    fun {i j} f => by
      apply HasPowers.ext; intro s
      simp only [powerSliceProf,
        copowerPowerEquiv_apply]
      simp only [Category.assoc]
      rw [HasPowers.mapIdx_proj]
      rw [HasPowers.fac, HasPowers.fac]
      have wx := x.property f
      simp only [sliceProfunctor, copowerProf,
        copowerProfInner] at wx
      rw [HasCopowers.bimap_eq_mapVal_mapIdx,
        HasCopowers.bimap_eq_mapVal_mapIdx,
        Category.assoc, Category.assoc] at wx
      have h : HasCopowers.inj _ _ s ≫
          HasCopowers.mapVal ((G.map f.op).app i)
          ≫ HasCopowers.mapIdx
            (((HomToProf pt).map f.op).app i)
          ≫ x.val i
        = HasCopowers.inj _ _ s ≫
          HasCopowers.mapVal
            ((G.obj (Opposite.op j)).map
              f.op.unop)
          ≫ HasCopowers.mapIdx
            (((HomToProf pt).obj
              (Opposite.op j)).map f.op.unop)
          ≫ x.val j :=
        congrArg (HasCopowers.inj _ _ s ≫ ·) wx
      rw [← Category.assoc
        (HasCopowers.inj _ _ s)
        (HasCopowers.mapVal _),
        HasCopowers.mapVal_inj,
        ← Category.assoc
          (HasCopowers.inj _ _ s)
          (HasCopowers.mapVal _),
        HasCopowers.mapVal_inj] at h
      simp only [Category.assoc] at h
      rw [← Category.assoc
        (HasCopowers.inj _ _ _)
        (HasCopowers.mapIdx _),
        HasCopowers.mapIdx_inj,
        ← Category.assoc
          (HasCopowers.inj _ _ _)
          (HasCopowers.mapIdx _),
        HasCopowers.mapIdx_inj] at h
      rw [HomToProf_map_app,
        HomToProf_obj_map] at h
      exact h⟩
  invFun y := ⟨
    fun j => (copowerPowerEquiv
      (j ⟶ pt) ((G.obj (Opposite.op j)).obj j) Y
      ).symm (y.val j),
    fun {i j} f => by
      simp only [sliceProfunctor, copowerProf,
        copowerProfInner,
        copowerPowerEquiv_symm_apply]
      apply HasCopowers.ext; intro s
      rw [HasCopowers.bimap_eq_mapVal_mapIdx,
        HasCopowers.bimap_eq_mapVal_mapIdx,
        Category.assoc, Category.assoc]
      rw [← Category.assoc
        (HasCopowers.inj _ _ s)
        (HasCopowers.mapVal _),
        HasCopowers.mapVal_inj]
      rw [← Category.assoc
        (HasCopowers.inj _ _ s)
        (HasCopowers.mapVal _),
        HasCopowers.mapVal_inj]
      simp only [Category.assoc]
      rw [← Category.assoc
        (HasCopowers.inj _ _ _)
        (HasCopowers.mapIdx _),
        HasCopowers.mapIdx_inj]
      rw [← Category.assoc
        (HasCopowers.inj _ _ _)
        (HasCopowers.mapIdx _),
        HasCopowers.mapIdx_inj]
      rw [HomToProf_map_app,
        HomToProf_obj_map]
      rw [HasCopowers.fac, HasCopowers.fac]
      have wy := y.property f
      simp only [powerSliceProf] at wy
      have h := congrArg
        (· ≫ HasPowers.proj _ _ s) wy
      simp only [Category.assoc] at h
      erw [HasPowers.mapIdx_proj] at h
      exact h⟩
  left_inv x := by
    apply Subtype.ext; funext j
    exact (copowerPowerEquiv _ _ _).left_inv
      (x.val j)
  right_inv y := by
    apply Subtype.ext; funext j
    exact (copowerPowerEquiv _ _ _).right_inv
      (y.val j)

end EndEquiv

/-!
## End/Power Characterization

Composing all three steps gives the end-power
characterization of `G^e`:
`Hom(CopowerGExtObj G pt, Y) ≃
  typeEnd (powerSliceProf G pt Y)`.

On the diagonal at `A`, `powerSliceProf G pt Y` gives
`G(A, A) ⟶ Y^(A ⟶ pt)`, so the end is over all `A`
of morphisms `G(A, A) ⟶ Y^(A ⟶ pt)`.
-/

section GExtEndPowerEquiv

variable
  {C : Type u} [Category.{v} C]
  [HasCopowers C] [HasPowers C]
  (G : Cᵒᵖ ⥤ C ⥤ C)
  [HasAllCopowerProfCoends G]

open HasAllCopowerProfCoends

/-- The end-power characterization of `G^e`:
`Hom(CopowerGExtObj G pt, Y) ≃
  typeEnd (powerSliceProf G pt Y)`. -/
def gExtEndPowerEquiv (pt Y : C) :
    (CopowerGExtObj G pt ⟶ Y) ≃
      typeEnd (powerSliceProf G pt Y) :=
  (copowerGExtHomEndEquiv G pt Y).trans
    (endCopowerPowerEquiv G pt Y)

end GExtEndPowerEquiv

/-!
## Power-End Mendler Algebras

A `PowerEndMendlerAlgebra G` packages a carrier `pt` and
an element of `typeEnd (powerSliceProf G pt pt)`, i.e.,
a family `∀ A, G(A,A) ⟶ pt^(A ⟶ pt)` satisfying the
end wedge condition.

This is the power-end counterpart of `MendlerAlgebra G`,
which packages `∀ A (γ : A ⟶ pt), G(A,A) ⟶ pt` with
dinaturality.
-/

section PowerEndMendlerAlg

variable
  {C : Type u} [Category.{v} C]
  [HasCopowers C] [HasPowers C]
  (G : Cᵒᵖ ⥤ C ⥤ C)

/-- A power-end Mendler algebra for an endodifunctor
`G`. The algebra data is an element of
`typeEnd (powerSliceProf G pt pt)`. -/
@[ext]
structure PowerEndMendlerAlgebra where
  /-- The carrier object. -/
  pt : C
  /-- The algebra data: an element of the end
  `∫_A (G(A,A) ⟶ pt^(A ⟶ pt))`. -/
  str : typeEnd (powerSliceProf G pt pt)

namespace PowerEndMendlerAlgebra

variable {G}

/-- The algebra operation at object `A`:
`G(A,A) ⟶ power pt (A ⟶ pt)`. -/
def algOp (m : PowerEndMendlerAlgebra G)
    (A : C) :
    (G.obj (Opposite.op A)).obj A ⟶
      HasPowers.power m.pt (A ⟶ m.pt) :=
  m.str.val A

omit [HasCopowers C] in
/-- The wedge condition extracted from the end data:
for `f : i ⟶ j`, the covariant and contravariant
paths from `G(j, i)` to `power pt (i ⟶ pt)` agree. -/
theorem wedgeCondition (m : PowerEndMendlerAlgebra G)
    {i j : C} (f : i ⟶ j) :
    (G.map f.op).app i ≫ m.algOp i ≫
      HasPowers.mapIdx (f ≫ ·) =
    (G.obj (Opposite.op j)).map f ≫ m.algOp j := by
  change (G.map f.op).app i ≫ m.str.val i ≫
      HasPowers.mapIdx (f ≫ ·) =
    (G.obj (Opposite.op j)).map f.op.unop ≫
      m.str.val j
  have h := m.str.property f
  dsimp only [powerSliceProf] at h
  exact h

end PowerEndMendlerAlgebra

/-- A morphism of power-end Mendler algebras. -/
@[ext]
structure PowerEndMendlerAlgebraHom
    (m₁ m₂ : PowerEndMendlerAlgebra G) where
  /-- The underlying morphism in C. -/
  hom : m₁.pt ⟶ m₂.pt
  /-- The compatibility condition: for each `A`,
  `algOp A ≫ mapVal hom = algOp A ≫ mapIdx (· ≫ hom)`.
  Equivalently, for all `γ : A ⟶ m₁.pt`:
  `algOp A ≫ proj γ ≫ hom = algOp A ≫ proj (γ ≫ hom)`. -/
  comm : ∀ (A : C),
    m₁.algOp A ≫ HasPowers.mapVal hom =
    m₂.algOp A ≫ HasPowers.mapIdx (· ≫ hom)

namespace PowerEndMendlerAlgebraHom

variable {G}

omit [HasCopowers C] in
/-- The elementwise form of the compatibility
condition. -/
theorem comm_proj
    {m₁ m₂ : PowerEndMendlerAlgebra G}
    (f : PowerEndMendlerAlgebraHom G m₁ m₂)
    (A : C) (γ : A ⟶ m₁.pt) :
    m₁.algOp A ≫ HasPowers.proj _ _ γ ≫ f.hom =
    m₂.algOp A ≫
      HasPowers.proj _ _ (γ ≫ f.hom) := by
  have h := congrArg (· ≫ HasPowers.proj _ _ γ)
    (f.comm A)
  simp only [Category.assoc] at h
  rw [HasPowers.mapVal_proj,
    HasPowers.mapIdx_proj] at h
  exact h

/-- Identity morphism on a power-end Mendler algebra. -/
@[simps]
def id (m : PowerEndMendlerAlgebra G) :
    PowerEndMendlerAlgebraHom G m m where
  hom := 𝟙 m.pt
  comm _ := by
    simp only [HasPowers.mapVal_id,
      Category.comp_id]
    symm
    erw [HasPowers.mapIdx_id, Category.comp_id]

/-- Composition of power-end Mendler algebra
morphisms. -/
@[simps]
def comp
    {m₁ m₂ m₃ : PowerEndMendlerAlgebra G}
    (f : PowerEndMendlerAlgebraHom G m₁ m₂)
    (g : PowerEndMendlerAlgebraHom G m₂ m₃) :
    PowerEndMendlerAlgebraHom G m₁ m₃ where
  hom := f.hom ≫ g.hom
  comm A := by
    apply HasPowers.ext; intro γ
    simp only [Category.assoc]
    rw [HasPowers.mapVal_proj,
      HasPowers.mapIdx_proj]
    conv_lhs =>
      rw [← Category.assoc
        (HasPowers.proj _ _ γ) f.hom g.hom,
        ← Category.assoc (m₁.algOp A)
        (HasPowers.proj _ _ γ ≫ f.hom) g.hom]
    rw [f.comm_proj A γ, Category.assoc,
      g.comm_proj A (γ ≫ f.hom)]
    simp only [Category.assoc]

end PowerEndMendlerAlgebraHom

/-- The category of power-end Mendler algebras
for `G`. -/
instance PowerEndMendlerAlgebraCat :
    Category (PowerEndMendlerAlgebra G) where
  Hom := PowerEndMendlerAlgebraHom G
  id := PowerEndMendlerAlgebraHom.id
  comp := PowerEndMendlerAlgebraHom.comp
  id_comp _ := by
    ext; simp [PowerEndMendlerAlgebraHom.comp,
      PowerEndMendlerAlgebraHom.id]
  comp_id _ := by
    ext; simp [PowerEndMendlerAlgebraHom.comp,
      PowerEndMendlerAlgebraHom.id]
  assoc _ _ _ := by
    ext; simp [PowerEndMendlerAlgebraHom.comp,
      Category.assoc]

end PowerEndMendlerAlg

/-!
## Equivalence: MendlerAlgebra ≌ PowerEndMendlerAlgebra

The equivalence applies `copowerPowerEquiv` componentwise:
- Forward: `family j γ ↦ lift (family j)` (currying)
- Backward: `algOp j ↦ (fun γ => algOp j ≫ proj γ)` (uncurrying)
-/

section MendlerPowerEndEquiv

variable
  {C : Type u} [Category.{v} C]
  [HasCopowers C] [HasPowers C]
  (G : Cᵒᵖ ⥤ C ⥤ C)

/-- Convert a Mendler algebra to a power-end Mendler
algebra by lifting the family into a power. -/
def MendlerAlgebra.toPowerEnd
    (m : MendlerAlgebra G) :
    PowerEndMendlerAlgebra G where
  pt := m.pt
  str := ⟨
    fun j => HasPowers.lift (m.family j),
    fun {i j} f => by
      dsimp only [powerSliceProf]
      apply HasPowers.ext; intro s
      simp only [Category.assoc]
      erw [HasPowers.mapIdx_proj]
      rw [HasPowers.fac, HasPowers.fac]
      exact m.dinaturality f s⟩

/-- Convert a power-end Mendler algebra to a
Mendler algebra by projecting from the power. -/
def PowerEndMendlerAlgebra.toMendler
    (m : PowerEndMendlerAlgebra G) :
    MendlerAlgebra G :=
  MendlerAlgebra.mk' m.pt
    (fun j γ => m.algOp j ≫ HasPowers.proj _ _ γ)
    (fun i j f β => by
      simp only [Profunctor.lmap, Profunctor.rmap,
        sliceProfunctor_obj_map,
        sliceProfunctor_map_app,
        HomToProf_map_app, HomToProf_obj_map,
        Quiver.Hom.unop_op]
      have h := m.wedgeCondition f
      have hp := congrArg
        (· ≫ HasPowers.proj _ _ β) h
      simp only [Category.assoc] at hp
      erw [HasPowers.mapIdx_proj] at hp
      exact hp.symm)

omit [HasCopowers C] in
/-- Round-trip: `toPowerEnd` then `toMendler` is the
identity on `MendlerAlgebra`. -/
theorem toPowerEnd_toMendler
    (m : MendlerAlgebra G) :
    (m.toPowerEnd).toMendler = m := by
  cases m with
  | mk pt mao =>
    simp only [MendlerAlgebra.toPowerEnd,
      PowerEndMendlerAlgebra.toMendler,
      MendlerAlgebra.mk']
    congr 1
    cases mao with
    | mk rco =>
      congr 1
      cases rco with
      | mk fam dinat =>
        congr 1
        funext j γ
        exact HasPowers.fac _ γ

omit [HasCopowers C] in
/-- Round-trip: `toMendler` then `toPowerEnd` is the
identity on `PowerEndMendlerAlgebra`. -/
theorem toMendler_toPowerEnd
    (m : PowerEndMendlerAlgebra G) :
    (m.toMendler).toPowerEnd = m := by
  cases m with
  | mk pt str =>
    simp only [MendlerAlgebra.toPowerEnd,
      PowerEndMendlerAlgebra.toMendler,
      MendlerAlgebra.mk',
      PowerEndMendlerAlgebra.algOp]
    congr 1
    apply Subtype.ext; funext j
    apply HasPowers.ext; intro γ
    exact HasPowers.fac _ γ

omit [HasCopowers C] in
/-- The forward functor mapping morphisms of Mendler
algebras to morphisms of power-end Mendler algebras. -/
def MendlerAlgebra.toPowerEndHom
    {m₁ m₂ : MendlerAlgebra G}
    (f : m₁ ⟶ m₂) :
    m₁.toPowerEnd ⟶ m₂.toPowerEnd where
  hom := f.hom
  comm A := by
    apply HasPowers.ext; intro γ
    simp only [Category.assoc]
    dsimp only [MendlerAlgebra.toPowerEnd,
      PowerEndMendlerAlgebra.algOp]
    rw [HasPowers.mapVal_proj,
      HasPowers.mapIdx_proj]
    rw [← Category.assoc, HasPowers.fac,
      HasPowers.fac]
    exact f.comm A γ

omit [HasCopowers C] in
/-- The backward functor mapping morphisms of power-end
Mendler algebras to morphisms of Mendler algebras. -/
def PowerEndMendlerAlgebra.toMendlerHom
    {m₁ m₂ : PowerEndMendlerAlgebra G}
    (f : m₁ ⟶ m₂) :
    m₁.toMendler ⟶ m₂.toMendler where
  hom := f.hom
  comm A γ := by
    simp only [PowerEndMendlerAlgebra.toMendler,
      MendlerAlgebra.mk',
      MendlerAlgebra.family,
      MendlerAlgebraOver.family]
    rw [Category.assoc]
    exact f.comm_proj A γ

omit [HasCopowers C] in
/-- The functor from Mendler algebras to power-end
Mendler algebras. -/
@[simps]
def toPowerEndFunctor :
    MendlerAlgebra G ⥤ PowerEndMendlerAlgebra G where
  obj := MendlerAlgebra.toPowerEnd G
  map := MendlerAlgebra.toPowerEndHom G
  map_id _ := by
    apply PowerEndMendlerAlgebraHom.ext; rfl
  map_comp _ _ := by
    apply PowerEndMendlerAlgebraHom.ext; rfl

omit [HasCopowers C] in
/-- The functor from power-end Mendler algebras to
Mendler algebras. -/
@[simps]
def toMendlerFunctor :
    PowerEndMendlerAlgebra G ⥤ MendlerAlgebra G where
  obj := PowerEndMendlerAlgebra.toMendler G
  map := PowerEndMendlerAlgebra.toMendlerHom G
  map_id _ := by
    apply MendlerAlgebraHom.ext; rfl
  map_comp _ _ := by
    apply MendlerAlgebraHom.ext; rfl

omit [HasCopowers C] [HasPowers C] in
@[simp]
theorem eqToHom_mendler_hom
    {m₁ m₂ : MendlerAlgebra G} (h : m₁ = m₂) :
    (eqToHom h).hom =
      eqToHom (congrArg MendlerAlgebra.pt h) := by
  subst h; rfl

omit [HasCopowers C] in
@[simp]
theorem eqToHom_powerEnd_hom
    {m₁ m₂ : PowerEndMendlerAlgebra G}
    (h : m₁ = m₂) :
    (eqToHom h).hom =
      eqToHom
        (congrArg PowerEndMendlerAlgebra.pt h) := by
  subst h; rfl

omit [HasCopowers C] [HasPowers C] in
@[simp]
theorem comp_mendler_hom
    {m₁ m₂ m₃ : MendlerAlgebra G}
    (f : m₁ ⟶ m₂) (g : m₂ ⟶ m₃) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

omit [HasCopowers C] in
@[simp]
theorem comp_powerEnd_hom
    {m₁ m₂ m₃ : PowerEndMendlerAlgebra G}
    (f : m₁ ⟶ m₂) (g : m₂ ⟶ m₃) :
    (f ≫ g).hom = f.hom ≫ g.hom := rfl

omit [HasCopowers C] in
/-- The equivalence between Mendler algebras and
power-end Mendler algebras. -/
def mendlerAlgPowerEndEquiv :
    MendlerAlgebra G ≌ PowerEndMendlerAlgebra G :=
  CategoryTheory.Equivalence.mk
    (toPowerEndFunctor G)
    (toMendlerFunctor G)
    (NatIso.ofComponents
      (fun m => eqToIso
        (toPowerEnd_toMendler G m).symm)
      (fun {_m₁ _m₂} f => by
        apply MendlerAlgebraHom.ext
        simp only [Functor.id_map, Functor.comp_map,
          Functor.id_obj, Functor.comp_obj,
          comp_mendler_hom, eqToHom_mendler_hom,
          toPowerEndFunctor_obj,
          toPowerEndFunctor_map,
          toMendlerFunctor_obj,
          toMendlerFunctor_map,
          MendlerAlgebra.toPowerEndHom,
          PowerEndMendlerAlgebra.toMendlerHom,
          eqToIso.hom, eqToHom_refl,
          Category.comp_id, Category.id_comp]))
    (NatIso.ofComponents
      (fun m => eqToIso
        (toMendler_toPowerEnd G m))
      (fun {_m₁ _m₂} f => by
        apply PowerEndMendlerAlgebraHom.ext
        simp only [Functor.id_map, Functor.comp_map,
          Functor.id_obj, Functor.comp_obj,
          comp_powerEnd_hom, eqToHom_powerEnd_hom,
          toPowerEndFunctor_obj,
          toPowerEndFunctor_map,
          toMendlerFunctor_obj,
          toMendlerFunctor_map,
          MendlerAlgebra.toPowerEndHom,
          PowerEndMendlerAlgebra.toMendlerHom,
          eqToIso.hom, eqToHom_refl,
          Category.comp_id, Category.id_comp]))

end MendlerPowerEndEquiv

/-!
## Power-End Mendler-Lambek Equivalence

Composition of `mendlerAlgPowerEndEquiv` with
`mendlerLambekEquiv` yields the equivalence between
power-end Mendler algebras and conventional algebras.
-/

section MendlerLambekEndPower

variable
  {C : Type u} [Category.{v} C]
  [HasCopowers C] [HasPowers C]
  (G : Cᵒᵖ ⥤ C ⥤ C)
  [HasAllHomToProfCoends G]

/-- The Mendler-Lambek equivalence expressed via
ends and powers:
`PowerEndMendlerAlgebra G ≌
  ConventionalAlgebra (GExtFunctor G)`. -/
def mendlerLambekEndPowerEquiv :
    PowerEndMendlerAlgebra G ≌
      ConventionalAlgebra
        (HasAllHomToProfCoends.GExtFunctor G) :=
  (mendlerAlgPowerEndEquiv G).symm.trans
    (mendlerLambekEquiv G)

end MendlerLambekEndPower

/-!
## Copower-Coend GExtFunctor

The `CopowerCoendGExtFunctor` is an endofunctor
`C ⥤ C` naturally isomorphic to `GExtFunctor G`, with
its carrier defined as `CopowerGExtObj G` (the
copower-profunctor coend) and its maps defined by
conjugation with `copowerGExtIso`.
-/

section CopowerCoendGExt

open HasAllCopowerProfCoends HasAllHomToProfCoends

variable
  {C : Type u} [Category.{v} C]
  [HasCopowers C] [HasPowers C]
  (G : Cᵒᵖ ⥤ C ⥤ C)
  [HasAllCopowerProfCoends G]

/-- The copower-coend GExtFunctor: an endofunctor
`C ⥤ C` whose object map is `CopowerGExtObj G` (the
copower-profunctor coend carrier). Naturally isomorphic
to the restricted-coend-based `GExtFunctor G`, with
maps defined by conjugation with `copowerGExtIso`. -/
@[simps]
def CopowerCoendGExtFunctor : C ⥤ C where
  obj pt := CopowerGExtObj G pt
  map {pt₁ pt₂} h :=
    (copowerGExtIso G pt₁).hom ≫
      (GExtFunctor G).map h ≫
      (copowerGExtIso G pt₂).inv
  map_id pt := by
    simp only [CategoryTheory.Functor.map_id,
      GExtFunctor_obj]
    simp only [Category.id_comp, Iso.hom_inv_id]
  map_comp {pt₁ pt₂ pt₃} h₁ h₂ := by
    rw [CategoryTheory.Functor.map_comp]
    simp only [Category.assoc]
    congr 1; congr 1
    simp only [← Category.assoc,
      Iso.inv_hom_id, Category.id_comp]

/-- The natural isomorphism between
`CopowerCoendGExtFunctor` and `GExtFunctor`, with
components given by `copowerGExtIso`. -/
def copowerCoendGExtNatIso :
    CopowerCoendGExtFunctor G ≅ GExtFunctor G :=
  NatIso.ofComponents
    (fun pt => copowerGExtIso G pt)
    (fun {pt₁ pt₂} h => by
      simp only [CopowerCoendGExtFunctor_map,
        Category.assoc]
      simp only [Iso.inv_hom_id, Category.comp_id])

/-- The equivalence of power-end Mendler algebras with
conventional algebras of
`CopowerCoendGExtFunctor G`. -/
def mendlerLambekCopowerCoendEquiv :
    PowerEndMendlerAlgebra G ≌
      ConventionalAlgebra
        (CopowerCoendGExtFunctor G) :=
  mendlerLambekEndPowerEquiv G |>.trans
    (Endofunctor.Algebra.equivOfNatIso
      (copowerCoendGExtNatIso G)).symm

end CopowerCoendGExt

/-!
## Power-Slice Profunctor Reindexing

Given `h : pt₁ ⟶ pt₂`, postcomposition with
`HasPowers.mapIdx (· ≫ h)` at each component defines a
natural transformation
`powerSliceProf G pt₂ Y ⟶ powerSliceProf G pt₁ Y`.

This reindexes the power `Y^(B ⟶ pt₂)` to
`Y^(B ⟶ pt₁)` via precomposition with `h`.
-/

section PowerSliceReindex

variable
  {C : Type u} [Category.{v} C]
  [HasCopowers C] [HasPowers C]
  (G : Cᵒᵖ ⥤ C ⥤ C) {pt₁ pt₂ : C}
  (h : pt₁ ⟶ pt₂) (Y : C)

open HasPowers

/-- Reindexing the power-slice profunctor along
`h : pt₁ ⟶ pt₂`: postcomposition with
`mapIdx (· ≫ h)` at each component. -/
def powerSliceProfReindex :
    powerSliceProf G pt₂ Y ⟶
      powerSliceProf G pt₁ Y where
  app A := {
    app := fun B φ => φ ≫ mapIdx (· ≫ h)
    naturality := fun {B₁ B₂} g => by
      ext φ
      simp only [types_comp_apply, powerSliceProf,
        Category.assoc]
      congr 1
      apply HasPowers.ext; intro s
      simp only [Category.assoc, mapIdx_proj]
  }
  naturality {A₁ A₂} f := by
    ext B φ
    simp only [NatTrans.comp_app, types_comp_apply,
      powerSliceProf, Category.assoc]

omit [HasCopowers C] in
/-- Reindexing by the identity is the identity
natural transformation. -/
theorem powerSliceProfReindex_id (pt Y : C) :
    powerSliceProfReindex G (𝟙 pt) Y =
      𝟙 (powerSliceProf G pt Y) := by
  ext A B φ
  simp only [powerSliceProfReindex,
    NatTrans.id_app, types_id_apply]
  have : (· ≫ 𝟙 pt : (B ⟶ pt) → (B ⟶ pt)) = id :=
    funext (fun _ => Category.comp_id _)
  rw [this, mapIdx_id, Category.comp_id]

omit [HasCopowers C] in
/-- Reindexing by a composition decomposes as
the composition of the individual reindexings. -/
theorem powerSliceProfReindex_comp
    {pt₃ : C} (h₁ : pt₁ ⟶ pt₂) (h₂ : pt₂ ⟶ pt₃)
    (Y : C) :
    powerSliceProfReindex G (h₁ ≫ h₂) Y =
      powerSliceProfReindex G h₂ Y ≫
        powerSliceProfReindex G h₁ Y := by
  ext A B φ
  simp only [powerSliceProfReindex,
    NatTrans.comp_app, types_comp_apply,
    Category.assoc]
  congr 1
  have : (· ≫ h₁ ≫ h₂ : (B ⟶ pt₁) → (B ⟶ pt₃)) =
      (· ≫ h₂) ∘ (· ≫ h₁) :=
    funext (fun s => (Category.assoc s h₁ h₂).symm)
  rw [this, mapIdx_comp]

end PowerSliceReindex

/-!
## Power-End GExtFunctor (Impredicative)

The `ImpredicativeGExtFunctor` is an endofunctor `C ⥤ C`
with carrier `CopowerGExtObj G pt` and maps defined
via the end-power characterization
`gExtEndPowerEquiv`, using `powerSliceProfReindex` to
reindex along morphisms. The functor action is defined
impredicatively: for `h : pt₁ ⟶ pt₂`, the map is
`equiv⁻¹(typeEnd.map (reindex h) (equiv(𝟙)))`.
-/

section PowerEndGExt

open HasAllCopowerProfCoends HasAllHomToProfCoends
open HasPowers

variable
  {C : Type u} [Category.{v} C]
  [HasCopowers C] [HasPowers C]
  (G : Cᵒᵖ ⥤ C ⥤ C)
  [HasAllCopowerProfCoends G]

/-- The impredicative map for the power-end
GExtFunctor: given `h : pt₁ ⟶ pt₂`, sends
`𝟙 : CopowerGExtObj G pt₂ ⟶ CopowerGExtObj G pt₂`
through `gExtEndPowerEquiv`, reindexes via
`powerSliceProfReindex G h`, and maps back. -/
def powerEndGExtMap {pt₁ pt₂ : C} (h : pt₁ ⟶ pt₂) :
    CopowerGExtObj G pt₁ ⟶ CopowerGExtObj G pt₂ :=
  (gExtEndPowerEquiv G pt₁
    (CopowerGExtObj G pt₂)).symm
    (typeEnd.map (J := C)
      (powerSliceProfReindex G h
        (CopowerGExtObj G pt₂))
      (gExtEndPowerEquiv G pt₂
        (CopowerGExtObj G pt₂) (𝟙 _)))

theorem powerEndGExtMap_id (pt : C) :
    powerEndGExtMap G (𝟙 pt) = 𝟙 _ := by
  unfold powerEndGExtMap
  rw [powerSliceProfReindex_id]
  have hmid : ∀ (F : Cᵒᵖ ⥤ C ⥤ Type v)
      (x : typeEnd F),
      typeEnd.map (J := C) (𝟙 F) x = x :=
    fun F x => Subtype.ext (funext (fun _ => rfl))
  rw [hmid]
  exact (gExtEndPowerEquiv G pt _).symm_apply_apply
    (𝟙 _)

end PowerEndGExt

/-!
## Impredicative GExtFunctor via Internal Homs and Ends

For a category `C` with `MonoidalClosed` (providing internal
hom `ihom`) and `HasPowers` (providing `power Y S` for
`S : Type v`), we construct `PowerEndGExtObj G pt` as an
object of `C` defined entirely via ends, powers, and internal
homs — without reference to copowers or coends.

The construction has two layers:

1. The inner profunctor `ihomPowerProf G pt Y : Cᵒᵖ ⥤ C ⥤ C`
   sends `(op A, B)` to `G(op B, A) ⟶[C] power Y (B ⟶ pt)`.
   Its end (parameterized via `HasTerminalWedge`) gives, for
   each `Y`, an object `innerEnd Y : C`.

2. The outer profunctor `churchProf : Cᵒᵖ ⥤ C ⥤ C` sends
   `(op Y₁, Y₂)` to `innerEnd Y₁ ⟶[C] Y₂`. Its end gives
   `PowerEndGExtObj G pt : C`.
-/

section ImpredicativeGExt

open MonoidalClosed

variable
  {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [MonoidalClosed C]
  [HasPowers C]

/-- A terminal wedge for a profunctor `F : Jᵒᵖ ⥤ J ⥤ C`
bundles a wedge together with a proof that it is a limit.
This provides a computable end object. -/
structure HasTerminalWedge
    {J : Type u} [Category.{v} J]
    (F : Jᵒᵖ ⥤ J ⥤ C) where
  wedge : Wedge F
  isLimit : IsLimit wedge

/-- The internal-hom power-slice profunctor: sends
`(op A, B)` to `G(op B, A) ⟶[C] power Y (B ⟶ pt)`.

This is the internalization of `powerSliceProf`:
where `powerSliceProf` produces hom-sets in `Type v`,
this produces internal hom objects in `C`. -/
def ihomPowerProf
    (G : Cᵒᵖ ⥤ C ⥤ C)
    (pt Y : C) : Cᵒᵖ ⥤ C ⥤ C where
  obj A := {
    obj := fun B =>
      (ihom ((G.obj (Opposite.op B)).obj A.unop)).obj
        (HasPowers.power Y (B ⟶ pt))
    map := fun {B₁ B₂} g =>
      (MonoidalClosed.pre
        ((G.map g.op).app A.unop)).app _ ≫
        (ihom _).map (HasPowers.mapIdx (g ≫ ·))
    map_id := fun B => by
      change (MonoidalClosed.pre
        ((G.map (𝟙 B).op).app A.unop)).app _ ≫
        (ihom _).map
          (HasPowers.mapIdx (𝟙 B ≫ ·)) = 𝟙 _
      have hG : (G.map (𝟙 B).op).app A.unop =
          𝟙 _ := by
        rw [op_id, G.map_id]
        rfl
      have hIdx : (𝟙 B ≫ · : (B ⟶ pt) →
          (B ⟶ pt)) = _root_.id :=
        funext (fun _ => Category.id_comp _)
      rw [hG, MonoidalClosed.pre_id,
        NatTrans.id_app, Category.id_comp,
        hIdx, HasPowers.mapIdx_id,
        CategoryTheory.Functor.map_id]
    map_comp := fun {B₁ B₂ B₃} f g => by
      have hGcomp :
          (G.map (f ≫ g).op).app A.unop =
          (G.map g.op).app A.unop ≫
            (G.map f.op).app A.unop := by
        rw [op_comp, Functor.map_comp]; rfl
      have hIdx : ((f ≫ g) ≫ · :
          (B₃ ⟶ pt) → (B₁ ⟶ pt)) =
          (f ≫ ·) ∘ (g ≫ ·) :=
        funext (fun s =>
          (Category.assoc f g s))
      rw [hGcomp, MonoidalClosed.pre_map,
        NatTrans.comp_app,
        hIdx, HasPowers.mapIdx_comp,
        CategoryTheory.Functor.map_comp]
      simp only [Category.assoc]
      congr 1
      rw [← Category.assoc, ← Category.assoc]
      congr 1
      exact MonoidalClosed.pre_comm_ihom_map
        ((G.map g.op).app A.unop)
        (HasPowers.mapIdx (f ≫ ·))
  }
  map {A₁ A₂} h := {
    app := fun B =>
      (MonoidalClosed.pre
        ((G.obj (Opposite.op B)).map h.unop)).app _
    naturality := fun {B₁ B₂} g => by
      simp only [Category.assoc]
      slice_lhs 2 3 =>
        rw [← MonoidalClosed.pre_comm_ihom_map]
      rw [← Category.assoc
        ((MonoidalClosed.pre _).app _)
        ((MonoidalClosed.pre _).app _),
        ← NatTrans.comp_app,
        ← MonoidalClosed.pre_map]
      rw [← Category.assoc
        ((MonoidalClosed.pre _).app _)
        ((MonoidalClosed.pre _).app _),
        ← NatTrans.comp_app,
        ← MonoidalClosed.pre_map]
      rw [(G.map g.op).naturality h.unop]
  }
  map_id := fun A => by
    ext B
    change (MonoidalClosed.pre
      ((G.obj (Opposite.op B)).map
        (𝟙 A).unop)).app _ = 𝟙 _
    rw [unop_id, CategoryTheory.Functor.map_id,
      MonoidalClosed.pre_id, NatTrans.id_app]
  map_comp := fun {A₁ A₂ A₃} f g => by
    ext B
    change (MonoidalClosed.pre
      ((G.obj (Opposite.op B)).map
        (f ≫ g).unop)).app _ =
      (MonoidalClosed.pre
        ((G.obj (Opposite.op B)).map
          f.unop)).app _ ≫
      (MonoidalClosed.pre
        ((G.obj (Opposite.op B)).map
          g.unop)).app _
    rw [unop_comp, Functor.map_comp,
      MonoidalClosed.pre_map, NatTrans.comp_app]

/-- Given terminal wedges for `F` and `F'` and a natural
transformation `α : F ⟶ F'`, produce a morphism between
the end objects by composing each projection with the
diagonal component of `α` and lifting. -/
def HasTerminalWedge.map
    {J : Type u} [Category.{v} J]
    {F F' : Jᵒᵖ ⥤ J ⥤ C}
    (tw : HasTerminalWedge F) (tw' : HasTerminalWedge F')
    (α : F ⟶ F') :
    tw.wedge.pt ⟶ tw'.wedge.pt :=
  Wedge.IsLimit.lift tw'.isLimit
    (fun j =>
      tw.wedge.ι j ≫ (α.app (Opposite.op j)).app j)
    (fun i j g => by
      simp only [Category.assoc]
      rw [← (α.app (Opposite.op i)).naturality g,
        ← Category.assoc,
        tw.wedge.condition g,
        Category.assoc]
      congr 1
      exact congr_arg (fun τ => NatTrans.app τ j)
        (α.naturality g.op))

/-- The natural transformation
`ihomPowerProf G pt Y₁ ⟶ ihomPowerProf G pt Y₂`
induced by `f : Y₁ ⟶ Y₂`, given by postcomposing
with `mapVal f` inside the internal hom at each
component. -/
def ihomPowerProfMapY
    (G : Cᵒᵖ ⥤ C ⥤ C)
    (pt : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    ihomPowerProf G pt Y₁ ⟶ ihomPowerProf G pt Y₂ where
  app A := {
    app := fun B =>
      (ihom ((G.obj (Opposite.op B)).obj A.unop)).map
        (HasPowers.mapVal f)
    naturality := fun {B₁ B₂} g => by
      simp only [ihomPowerProf, Category.assoc]
      rw [← (ihom ((G.obj (Opposite.op B₂)).obj
        A.unop)).map_comp,
        ← HasPowers.bimap_eq_mapIdx_mapVal,
        HasPowers.bimap_eq_mapVal_mapIdx,
        (ihom ((G.obj (Opposite.op B₂)).obj
        A.unop)).map_comp]
      rw [← Category.assoc
        ((MonoidalClosed.pre _).app _)
        ((ihom _).map _),
        ← Category.assoc
        ((ihom _).map _)
        ((MonoidalClosed.pre _).app _)]
      congr 1
      exact MonoidalClosed.pre_comm_ihom_map
        ((G.map g.op).app A.unop)
        (HasPowers.mapVal f)
  }
  naturality := fun {A₁ A₂} h => by
    ext B
    simp only [NatTrans.comp_app, ihomPowerProf]
    exact MonoidalClosed.pre_comm_ihom_map
      ((G.obj (Opposite.op B)).map h.unop)
      (HasPowers.mapVal f)

omit [MonoidalCategory C] [MonoidalClosed C]
  [HasPowers C] in
@[simp]
theorem HasTerminalWedge.map_ι
    {J : Type u} [Category.{v} J]
    {F F' : Jᵒᵖ ⥤ J ⥤ C}
    (tw : HasTerminalWedge F) (tw' : HasTerminalWedge F')
    (α : F ⟶ F') (j : J) :
    tw.map tw' α ≫ tw'.wedge.ι j =
      tw.wedge.ι j ≫ (α.app (Opposite.op j)).app j :=
  Wedge.IsLimit.lift_ι _ _ _ _

omit [MonoidalCategory C] [MonoidalClosed C]
  [HasPowers C] in
theorem HasTerminalWedge.hom_ext
    {J : Type u} [Category.{v} J]
    {F : Jᵒᵖ ⥤ J ⥤ C}
    (tw : HasTerminalWedge F)
    {X : C} {f g : X ⟶ tw.wedge.pt}
    (h : ∀ j, f ≫ tw.wedge.ι j = g ≫ tw.wedge.ι j) :
    f = g :=
  Multifork.IsLimit.hom_ext tw.isLimit h

omit [MonoidalCategory C] [MonoidalClosed C]
  [HasPowers C] in
theorem HasTerminalWedge.map_id
    {J : Type u} [Category.{v} J]
    {F : Jᵒᵖ ⥤ J ⥤ C}
    (tw : HasTerminalWedge F) :
    tw.map tw (𝟙 F) = 𝟙 tw.wedge.pt := by
  apply tw.hom_ext
  intro j
  simp

omit [MonoidalCategory C] [MonoidalClosed C]
  [HasPowers C] in
theorem HasTerminalWedge.map_comp
    {J : Type u} [Category.{v} J]
    {F F' F'' : Jᵒᵖ ⥤ J ⥤ C}
    (tw : HasTerminalWedge F) (tw' : HasTerminalWedge F')
    (tw'' : HasTerminalWedge F'')
    (α : F ⟶ F') (β : F' ⟶ F'') :
    tw.map tw'' (α ≫ β) =
      tw.map tw' α ≫ tw'.map tw'' β := by
  apply tw''.hom_ext
  intro j
  calc tw.map tw'' (α ≫ β) ≫ tw''.wedge.ι j
      = tw.wedge.ι j ≫
        ((α ≫ β).app (Opposite.op j)).app j :=
        map_ι tw tw'' (α ≫ β) j
    _ = tw.wedge.ι j ≫
        (α.app (Opposite.op j)).app j ≫
        (β.app (Opposite.op j)).app j := by
        rw [NatTrans.comp_app, NatTrans.comp_app]
    _ = (tw.map tw' α ≫ tw'.wedge.ι j) ≫
        (β.app (Opposite.op j)).app j := by
        rw [← Category.assoc,
          ← map_ι tw tw' α j]
    _ = tw.map tw' α ≫
        (tw'.wedge.ι j ≫
          (β.app (Opposite.op j)).app j) := by
        rw [Category.assoc]
    _ = tw.map tw' α ≫
        (tw'.map tw'' β ≫ tw''.wedge.ι j) := by
        rw [← map_ι tw' tw'' β j]
    _ = (tw.map tw' α ≫ tw'.map tw'' β) ≫
        tw''.wedge.ι j := by
        rw [← Category.assoc]

/-- The inner end functor: for each `Y`, takes the end
of `ihomPowerProf G pt Y` to produce an object of `C`.
This sends `Y` to `∫_A G(A,A) ⟶[C] power Y (A ⟶ pt)`.
-/
def ihomPowerEndFunctor
    (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    (tw : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y)) :
    C ⥤ C where
  obj Y := (tw Y).wedge.pt
  map {Y₁ Y₂} f :=
    (tw Y₁).map (tw Y₂) (ihomPowerProfMapY G pt f)
  map_id Y := by
    rw [show ihomPowerProfMapY G pt (𝟙 Y) = 𝟙 _
      from _]
    · exact (tw Y).map_id
    · ext A B
      simp only [ihomPowerProfMapY, NatTrans.id_app,
        HasPowers.mapVal_id,
        CategoryTheory.Functor.map_id]; rfl
  map_comp {Y₁ Y₂ Y₃} f g := by
    rw [show ihomPowerProfMapY G pt (f ≫ g) =
      ihomPowerProfMapY G pt f ≫
        ihomPowerProfMapY G pt g
      from _]
    · exact (tw Y₁).map_comp (tw Y₂) (tw Y₃) _ _
    · ext A B
      simp only [ihomPowerProfMapY, NatTrans.comp_app,
        HasPowers.mapVal_comp,
        CategoryTheory.Functor.map_comp]

/-- The outer Church-encoding profunctor: sends
`(op Y₁, Y₂)` to
`ihomPowerEndFunctor.obj Y₁ ⟶[C] Y₂`.
Its end gives the impredicative `GExtObj`. -/
def churchProf
    (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    (tw : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y)) :
    Cᵒᵖ ⥤ C ⥤ C where
  obj Y := (ihom ((ihomPowerEndFunctor G pt tw).obj
    Y.unop))
  map {Y₁ Y₂} f :=
    MonoidalClosed.pre
      ((ihomPowerEndFunctor G pt tw).map f.unop)
  map_id Y := by
    rw [unop_id,
      CategoryTheory.Functor.map_id,
      MonoidalClosed.pre_id]
  map_comp {Y₁ Y₂ Y₃} f g := by
    rw [unop_comp,
      CategoryTheory.Functor.map_comp,
      MonoidalClosed.pre_map]

/-- The impredicative `GExtObj` defined entirely via
ends, powers, and internal homs. Given terminal wedges
for the inner profunctor (for each `Y`) and for the
outer Church-encoding profunctor, this is the object
`∫_Y (∫_A G(A,A) ⟶[C] Y^(A→pt)) ⟶[C] Y`. -/
def ImpredicativeGExtObj
    (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    (tw : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : HasTerminalWedge
      (churchProf G pt tw)) : C :=
  twOuter.wedge.pt

/-- The natural transformation
`ihomPowerProf G pt₂ Y ⟶ ihomPowerProf G pt₁ Y`
induced by `h : pt₁ ⟶ pt₂`, given by postcomposing
with `mapIdx (· ≫ h)` inside the internal hom at
each component. This is contravariant in `pt`. -/
def ihomPowerProfMapPt
    (G : Cᵒᵖ ⥤ C ⥤ C)
    {pt₁ pt₂ : C} (h : pt₁ ⟶ pt₂) (Y : C) :
    ihomPowerProf G pt₂ Y ⟶
      ihomPowerProf G pt₁ Y where
  app A := {
    app := fun B =>
      (ihom ((G.obj (Opposite.op B)).obj
        A.unop)).map
        (HasPowers.mapIdx (· ≫ h))
    naturality := fun {B₁ B₂} g => by
      simp only [ihomPowerProf, Category.assoc]
      -- Combine ihom.map on LHS (positions 2+3)
      slice_lhs 2 3 =>
        rw [← CategoryTheory.Functor.map_comp]
      -- Use ← pre_comm on RHS (positions 1+2)
      -- to move ihom.map before pre
      rw [← Category.assoc
        ((ihom _).map (HasPowers.mapIdx _)),
        ← MonoidalClosed.pre_comm_ihom_map
          ((G.map g.op).app A.unop)
          (HasPowers.mapIdx (· ≫ h))]
      simp only [Category.assoc]
      -- Combine ihom.map on RHS (positions 2+3)
      slice_rhs 2 3 =>
        rw [← CategoryTheory.Functor.map_comp]
      -- Both sides: pre(Gg) ≫ ihom(G(B₂,A)).map(...)
      -- Show the arguments are equal
      congr 1
      congr 1
      rw [← HasPowers.mapIdx_comp,
        ← HasPowers.mapIdx_comp]
      congr 1
      funext s
      simp only [Function.comp_apply]
      exact (Category.assoc g s h).symm
  }
  naturality := fun {A₁ A₂} g => by
    ext B
    simp only [NatTrans.comp_app, ihomPowerProf]
    exact MonoidalClosed.pre_comm_ihom_map
      ((G.obj (Opposite.op B)).map g.unop)
      (HasPowers.mapIdx (· ≫ h))

/-- The `ihomPowerProfMapPt` and `ihomPowerProfMapY`
natural transformations commute: changing `pt` and
changing `Y` can be done in either order. At each
component this reduces to the interchange of
`mapIdx` and `mapVal` via `bimap`. -/
theorem ihomPowerProfMapPt_mapY_comm
    (G : Cᵒᵖ ⥤ C ⥤ C)
    {pt₁ pt₂ : C} (h : pt₁ ⟶ pt₂)
    {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    ihomPowerProfMapPt G h Y₁ ≫
      ihomPowerProfMapY G pt₁ f =
    ihomPowerProfMapY G pt₂ f ≫
      ihomPowerProfMapPt G h Y₂ := by
  ext A B
  simp only [NatTrans.comp_app, ihomPowerProfMapPt,
    ihomPowerProfMapY,
    ← CategoryTheory.Functor.map_comp]
  congr 1
  rw [← HasPowers.bimap_eq_mapIdx_mapVal,
    HasPowers.bimap_eq_mapVal_mapIdx]

/-- The natural transformation
`churchProf G pt₁ tw₁ ⟶ churchProf G pt₂ tw₂`
induced by `h : pt₁ ⟶ pt₂`, given by composing
the contravariant inner-end map (via
`ihomPowerProfMapPt`) with `pre`. -/
def churchProfMapPt
    (G : Cᵒᵖ ⥤ C ⥤ C)
    {pt₁ pt₂ : C} (h : pt₁ ⟶ pt₂)
    (tw₁ : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt₁ Y))
    (tw₂ : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt₂ Y)) :
    churchProf G pt₁ tw₁ ⟶
      churchProf G pt₂ tw₂ where
  app Y := {
    app := fun Z =>
      MonoidalClosed.pre
        ((tw₂ Y.unop).map (tw₁ Y.unop)
          (ihomPowerProfMapPt G h Y.unop))
        |>.app Z
    naturality := fun {Z₁ Z₂} f => by
      simp only [churchProf]
      exact (MonoidalClosed.pre_comm_ihom_map
        ((tw₂ Y.unop).map (tw₁ Y.unop)
          (ihomPowerProfMapPt G h Y.unop))
        f).symm
  }
  naturality := fun {Y₁ Y₂} g => by
    ext Z
    simp only [NatTrans.comp_app, churchProf]
    rw [← NatTrans.comp_app, ← NatTrans.comp_app,
      ← MonoidalClosed.pre_map,
      ← MonoidalClosed.pre_map]
    congr 2
    simp only [ihomPowerEndFunctor]
    rw [← HasTerminalWedge.map_comp,
      ← HasTerminalWedge.map_comp]
    congr 1
    exact ihomPowerProfMapPt_mapY_comm G h g.unop

theorem ihomPowerProfMapPt_id
    (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C) (Y : C) :
    ihomPowerProfMapPt G (𝟙 pt) Y =
      𝟙 (ihomPowerProf G pt Y) := by
  ext A B
  simp only [ihomPowerProfMapPt, NatTrans.id_app,
    Category.comp_id]
  change (ihom _).map (HasPowers.mapIdx _root_.id) =
    𝟙 _
  rw [HasPowers.mapIdx_id,
    CategoryTheory.Functor.map_id]

theorem ihomPowerProfMapPt_comp
    (G : Cᵒᵖ ⥤ C ⥤ C)
    {pt₁ pt₂ pt₃ : C}
    (h₁ : pt₁ ⟶ pt₂) (h₂ : pt₂ ⟶ pt₃) (Y : C) :
    ihomPowerProfMapPt G (h₁ ≫ h₂) Y =
    ihomPowerProfMapPt G h₂ Y ≫
      ihomPowerProfMapPt G h₁ Y := by
  ext A B
  simp only [ihomPowerProfMapPt, NatTrans.comp_app,
    ← CategoryTheory.Functor.map_comp]
  congr 1
  rw [← HasPowers.mapIdx_comp]
  congr 1
  funext s
  exact (Category.assoc s h₁ h₂).symm

/-- The impredicative GExt endofunctor, defined
entirely via ends, powers, and internal homs.
Sends `pt` to `∫_Y (∫_A G(A,A) ⟶[C] Y^(A→pt)) ⟶[C] Y`
and acts on morphisms by transporting both the inner
and outer ends. -/
def ImpredicativeGExtFunctor
    (G : Cᵒᵖ ⥤ C ⥤ C)
    (twInner : ∀ (pt Y : C),
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : ∀ (pt : C),
      HasTerminalWedge
        (churchProf G pt (twInner pt))) :
    C ⥤ C where
  obj pt :=
    ImpredicativeGExtObj G pt (twInner pt)
      (twOuter pt)
  map {pt₁ pt₂} h :=
    (twOuter pt₁).map (twOuter pt₂)
      (churchProfMapPt G h (twInner pt₁)
        (twInner pt₂))
  map_id pt := by
    rw [show churchProfMapPt G (𝟙 pt)
        (twInner pt) (twInner pt) = 𝟙 _ from _]
    · exact (twOuter pt).map_id
    · ext Y Z
      simp only [NatTrans.id_app,
        churchProfMapPt, churchProf]
      rw [ihomPowerProfMapPt_id,
        HasTerminalWedge.map_id,
        MonoidalClosed.pre_id]
      rfl
  map_comp {pt₁ pt₂ pt₃} h₁ h₂ := by
    rw [show churchProfMapPt G (h₁ ≫ h₂)
        (twInner pt₁) (twInner pt₃) =
      churchProfMapPt G h₁ (twInner pt₁)
        (twInner pt₂) ≫
      churchProfMapPt G h₂ (twInner pt₂)
        (twInner pt₃) from _]
    · exact (twOuter pt₁).map_comp
        (twOuter pt₂) (twOuter pt₃) _ _
    · ext Y Z
      simp only [NatTrans.comp_app,
        churchProfMapPt, churchProf]
      rw [ihomPowerProfMapPt_comp,
        HasTerminalWedge.map_comp,
        MonoidalClosed.pre_map, NatTrans.comp_app]

end ImpredicativeGExt

/-!
## Morphisms between Impredicative and Copower-Coend GExt

When `C` is a braided monoidal closed category with
copowers and powers, the impredicative GExt object
(defined via internal homs and ends) admits morphisms
to and from the copower-coend GExt object. The
backward direction (`copowerGExt_backward_forward`)
is proved abstractly; the forward composition
(`impredicativeGExtToCopowerGExt`) uses the braiding
to swap tensor factors in the monoidal closed
adjunction.
-/

section ImpredicativeGExtIso

open MonoidalClosed MonoidalCategory
open HasAllCopowerProfCoends HasAllHomToProfCoends

variable
  {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [MonoidalClosed C]
  [BraidedCategory C]
  [HasCopowers C] [HasPowers C]
  (G : Cᵒᵖ ⥤ C ⥤ C)
  [HasAllCopowerProfCoends G]

/-- Evaluate the internal hom `[X, Y]` at a global
element `p : 𝟙_ C ⟶ X`, yielding a morphism
`[X, Y] ⟶ Y`. Uses `MonoidalClosed.pre` composed
with the unit-ihom isomorphism. -/
def ihomEvalAt {X Y : C} (p : 𝟙_ C ⟶ X) :
    (ihom X).obj Y ⟶ Y :=
  (MonoidalClosed.pre p).app Y ≫
    (λ_ ((ihom (𝟙_ C)).obj Y)).inv ≫
    (ihom.ev (𝟙_ C)).app Y

omit [BraidedCategory C] [HasCopowers C]
  [HasPowers C] in
/-- `curry' e ≫ (pre f).app Y = curry' (f ≫ e)`:
precomposition on the internal hom by `f` after
currying is the same as currying the composition. -/
theorem curry'_pre_app
    {X X' Y : C} (e : X ⟶ Y) (f : X' ⟶ X) :
    curry' e ≫ (MonoidalClosed.pre f).app Y =
      curry' (f ≫ e) := by
  simp only [curry']
  rw [curry_pre_app]
  congr 1
  rw [← Category.assoc, rightUnitor_naturality,
    Category.assoc]

omit [BraidedCategory C] [HasCopowers C]
  [HasAllCopowerProfCoends G] in
private theorem typeEndToGlobalSection_wedge
    (pt Y : C)
    (e : typeEnd (powerSliceProf G pt Y))
    {A₁ A₂ : C} (f : A₁ ⟶ A₂) :
    curry' (e.val A₁) ≫
      ((ihomPowerProf G pt Y).obj
        (Opposite.op A₁)).map f =
    curry' (e.val A₂) ≫
      ((ihomPowerProf G pt Y).map f.op).app A₂ := by
  change curry' (e.val A₁) ≫
    (MonoidalClosed.pre
      ((G.map f.op).app A₁)).app _ ≫
    (ihom _).map (HasPowers.mapIdx (f ≫ ·)) =
    curry' (e.val A₂) ≫
    (MonoidalClosed.pre
      ((G.obj (Opposite.op A₂)).map f)).app _
  rw [← Category.assoc,
    curry'_pre_app _ ((G.map f.op).app A₁),
    curry'_ihom_map, curry'_pre_app]
  have h := e.property f
  simp only [powerSliceProf,
    Quiver.Hom.unop_op] at h
  rw [← Category.assoc] at h
  exact congrArg curry' h

def typeEndToGlobalSection
    (pt Y : C)
    (tw : HasTerminalWedge (ihomPowerProf G pt Y))
    (e : typeEnd (powerSliceProf G pt Y)) :
    𝟙_ C ⟶ tw.wedge.pt :=
  tw.isLimit.lift
    (Wedge.mk (𝟙_ C)
      (fun A => curry' (e.val A))
      (fun {_ _} f =>
        typeEndToGlobalSection_wedge G pt Y e f))

/-- The backward map from `ImpredicativeGExtObj` to
`CopowerGExtObj`, constructed via the Church encoding's
universal property. Evaluates the outer end projection
at the copower-coend object using a global section
derived from the identity morphism. -/
def impredicativeGExtToCopowerGExt
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : HasTerminalWedge
      (churchProf G pt twInner)) :
    ImpredicativeGExtObj G pt twInner twOuter ⟶
      CopowerGExtObj G pt :=
  let cge := CopowerGExtObj G pt
  let e := gExtEndPowerEquiv G pt cge (𝟙 cge)
  let gs := typeEndToGlobalSection G pt cge
    (twInner cge) e
  twOuter.wedge.ι cge ≫ ihomEvalAt gs

/-- The curried Church-encoding component: given
`A : C` and `s : A ⟶ pt`, produces a morphism
`G(A,A) ⟶ [twInner(Y).pt, Y]`
by currying the composition of inner end projection,
evaluation, and power projection, using the braiding
to swap tensor factors.

The uncurried version is the chain:
```
  G(A,A) ⊗ twInner(Y).pt
    ⟶ twInner(Y).pt ⊗ G(A,A)              (braiding)
    ⟶ [G(A,A), Y^{A→pt}] ⊗ G(A,A)        (inner end proj ⊗ 𝟙)
    ⟶ Y^{A→pt}                             (evaluation)
    ⟶ Y                                    (power projection at s)
``` -/
def churchComponent
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (Y : C) (A : C) (s : A ⟶ pt) :
    (G.obj (Opposite.op A)).obj A ⟶
      (ihom ((twInner Y).wedge.pt)).obj Y :=
  let GA := (G.obj (Opposite.op A)).obj A
  let YpowA := HasPowers.power Y (A ⟶ pt)
  let innerProj : (twInner Y).wedge.pt ⟶
      (ihom GA).obj YpowA :=
    (twInner Y).wedge.ι A
  curry (innerProj ▷ GA ≫
    (β_ _ GA).hom ≫
    (ihom.ev GA).app YpowA ≫
    HasPowers.proj Y (A ⟶ pt) s)

omit [HasCopowers C]
  [HasAllCopowerProfCoends G] in
theorem churchComponent_wedge
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (A : C) (s : A ⟶ pt)
    {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    churchComponent G pt twInner Y₁ A s ≫
      ((churchProf G pt twInner).obj
        (Opposite.op Y₁)).map f =
    churchComponent G pt twInner Y₂ A s ≫
      ((churchProf G pt twInner).map f.op).app Y₂ :=
  by
  simp only [churchComponent, churchProf,
    ihomPowerEndFunctor]
  rw [← curry_natural_right, curry_pre_app]
  congr 1
  slice_rhs 1 2 =>
    rw [← comp_whiskerRight,
      HasTerminalWedge.map_ι,
      comp_whiskerRight]
  simp only [Category.assoc]
  congr 1
  simp only [ihomPowerProfMapY]
  conv_rhs =>
    rw [BraidedCategory.braiding_naturality_left_assoc]
  rw [ihom.ev_naturality_assoc]
  simp only [Quiver.Hom.unop_op,
    HasPowers.mapVal_proj]
  rfl

omit [HasCopowers C] [HasPowers C]
  [HasAllCopowerProfCoends G] in
private theorem whisker_braided_eval_pre
    {W X X' Y' : C}
    (ι : W ⟶ (ihom X).obj Y') (h : X' ⟶ X) :
    W ◁ h ≫ ι ▷ X ≫
      (β_ ((ihom X).obj Y') X).hom ≫
      (ihom.ev X).app Y' =
    (ι ≫ (MonoidalClosed.pre h).app Y') ▷
        X' ≫
      (β_ ((ihom X').obj Y') X').hom ≫
      (ihom.ev X').app Y' := by
  slice_lhs 1 2 => rw [whisker_exchange]
  slice_lhs 2 3 =>
    rw [BraidedCategory.braiding_naturality_right]
  slice_lhs 3 4 =>
    rw [← id_tensor_pre_app_comp_ev]
  slice_lhs 2 3 =>
    rw [← BraidedCategory.braiding_naturality_left]
  slice_lhs 1 2 => rw [← comp_whiskerRight]
  simp only [Category.assoc]

omit [HasCopowers C]
  [HasAllCopowerProfCoends G] in
theorem churchComponent_dinatural
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (Y : C) {A₁ A₂ : C} (f : A₁ ⟶ A₂)
    (s : A₂ ⟶ pt) :
    (G.map f.op).app A₁ ≫
      churchComponent G pt twInner Y A₁ (f ≫ s) =
    (G.obj (Opposite.op A₂)).map f ≫
      churchComponent G pt twInner Y A₂ s := by
  simp only [churchComponent]
  have wedgeCond := (twInner Y).wedge.condition f
  simp only [ihomPowerProf] at wedgeCond
  simp only [Quiver.Hom.unop_op] at wedgeCond
  rw [← curry_natural_left, ← curry_natural_left]
  congr 1
  rw [← HasPowers.mapIdx_proj]
  slice_lhs 1 4 =>
    rw [whisker_braided_eval_pre]
  slice_lhs 3 4 =>
    rw [← ihom.ev_naturality]
  slice_lhs 2 3 =>
    rw [← BraidedCategory.braiding_naturality_left]
  slice_lhs 1 2 =>
    rw [← comp_whiskerRight]
  simp only [Category.assoc]
  rw [wedgeCond]
  symm
  slice_lhs 1 4 =>
    rw [whisker_braided_eval_pre]
  simp only [Category.assoc]

/-- Given `A : C`, `s : A ⟶ pt`, and the church
component at each `Y`, produce a morphism
`G(A,A) ⟶ ImpredicativeGExtObj G pt twInner twOuter`
by assembling the church components into a wedge for
the outer end and lifting. -/
def churchLift
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : HasTerminalWedge
      (churchProf G pt twInner))
    (A : C) (s : A ⟶ pt) :
    (G.obj (Opposite.op A)).obj A ⟶
      ImpredicativeGExtObj G pt twInner twOuter :=
  twOuter.isLimit.lift
    (Wedge.mk ((G.obj (Opposite.op A)).obj A)
      (fun Y => churchComponent G pt twInner Y A s)
      (fun {_ _} f =>
        churchComponent_wedge G pt twInner A s f))

omit [HasCopowers C]
  [HasAllCopowerProfCoends G] in
private theorem churchLiftPowerEndWedge
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : HasTerminalWedge
      (churchProf G pt twInner))
    {A₁ A₂ : C} (f : A₁ ⟶ A₂) :
    ((powerSliceProf G pt
        (ImpredicativeGExtObj G pt twInner twOuter)
      ).obj (Opposite.op A₁)).map f
      (HasPowers.lift (fun s =>
        churchLift G pt twInner twOuter A₁ s)) =
    ((powerSliceProf G pt
        (ImpredicativeGExtObj G pt twInner twOuter)
      ).map f.op).app A₂
      (HasPowers.lift (fun s =>
        churchLift G pt twInner twOuter A₂ s)) := by
  simp only [powerSliceProf]
  apply HasPowers.ext
  intro s
  simp only [Category.assoc]
  rw [HasPowers.mapIdx_proj]
  simp only [HasPowers.fac]
  simp only [Quiver.Hom.unop_op]
  apply Multifork.IsLimit.hom_ext twOuter.isLimit
  intro Y
  simp only [Category.assoc]
  have fac1 :
      churchLift G pt twInner twOuter A₁ (f ≫ s) ≫
        Multifork.ι twOuter.wedge Y =
      churchComponent G pt twInner Y A₁ (f ≫ s) :=
    twOuter.isLimit.fac
      (Wedge.mk _ (fun Y =>
        churchComponent G pt twInner Y A₁ (f ≫ s))
        (fun {_ _} g =>
          churchComponent_wedge G pt twInner A₁
            (f ≫ s) g))
      (WalkingMulticospan.left Y)
  have fac2 :
      churchLift G pt twInner twOuter A₂ s ≫
        Multifork.ι twOuter.wedge Y =
      churchComponent G pt twInner Y A₂ s :=
    twOuter.isLimit.fac
      (Wedge.mk _ (fun Y =>
        churchComponent G pt twInner Y A₂ s)
        (fun {_ _} g =>
          churchComponent_wedge G pt twInner A₂ s g))
      (WalkingMulticospan.left Y)
  simp only [
    show _ ≫ Multifork.ι twOuter.wedge Y =
      _ from fac1,
    show _ ≫ Multifork.ι twOuter.wedge Y =
      _ from fac2]
  exact churchComponent_dinatural
    G pt twInner Y f s

def copowerGExtToImpredicativeGExt
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : HasTerminalWedge
      (churchProf G pt twInner)) :
    CopowerGExtObj G pt ⟶
      ImpredicativeGExtObj G pt twInner twOuter :=
  (gExtEndPowerEquiv G pt
    (ImpredicativeGExtObj G pt twInner twOuter)).symm
    ⟨fun A =>
      HasPowers.lift (fun s =>
        churchLift G pt twInner twOuter A s),
    fun {_ _} f =>
      churchLiftPowerEndWedge G pt twInner twOuter f⟩

omit [BraidedCategory C] [HasCopowers C]
  [HasPowers C] [HasAllCopowerProfCoends G] in
private theorem curry_ihomEvalAt
    {X Y Z : C} (gs : 𝟙_ C ⟶ X)
    (h : X ⊗ Y ⟶ Z) :
    curry h ≫ ihomEvalAt gs =
      (λ_ Y).inv ≫ gs ▷ Y ≫ h := by
  simp only [ihomEvalAt]
  rw [← Category.assoc (curry h), curry_pre_app,
    ← Category.assoc (curry _),
    leftUnitor_inv_naturality,
    Category.assoc,
    whiskerLeft_curry_ihom_ev_app]

omit [BraidedCategory C] [HasCopowers C]
  [HasPowers C] [HasAllCopowerProfCoends G] in
private theorem curry'_ihomEvalAt
    {X Y : C} (p : 𝟙_ C ⟶ X)
    (f : X ⟶ Y) :
    curry' f ≫ ihomEvalAt p = p ≫ f := by
  rw [show curry' f =
    curry ((ρ_ X).hom ≫ f) from rfl,
    curry_ihomEvalAt]
  simp [← unitors_equal]

private theorem churchComponent_ihomEvalAt_eq
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (A : C) (s : A ⟶ pt) :
    let cge := CopowerGExtObj G pt
    let e := gExtEndPowerEquiv G pt cge (𝟙 cge)
    let gs := typeEndToGlobalSection G pt cge
      (twInner cge) e
    churchComponent G pt twInner cge A s ≫
      ihomEvalAt gs =
    HasCopowers.inj (A ⟶ pt)
      ((G.obj (Opposite.op A)).obj A) s ≫
      CopowerGExtInj G pt A := by
  intro cge e gs
  unfold churchComponent
  rw [curry_ihomEvalAt]
  rw [← comp_whiskerRight_assoc gs
    (Multifork.ι (twInner cge).wedge A)]
  have gs_fac : gs ≫ Multifork.ι (twInner cge).wedge A =
      curry' (e.val A) :=
    (twInner cge).isLimit.fac
      (Wedge.mk (𝟙_ C)
        (fun A => curry' (e.val A))
        (fun {_ _} f =>
          typeEndToGlobalSection_wedge G pt cge e f))
      (WalkingMulticospan.left A)
  rw [gs_fac]
  have braid :=
    BraidedCategory.braiding_naturality_left
      (curry' (e.val A))
      ((G.obj (Opposite.op A)).obj A)
  simp only [Opposite.unop_op] at braid
  rw [reassoc_of% braid, leftUnitor_inv_braiding_assoc]
  have whisk :=
    whiskerLeft_curry'_ihom_ev_app (e.val A)
  simp only [Opposite.unop_op] at whisk
  rw [reassoc_of% whisk, Iso.inv_hom_id_assoc]
  change (gExtEndPowerEquiv G pt cge (𝟙 cge)).val A ≫
    HasPowers.proj cge (A ⟶ pt) s =
    HasCopowers.inj (A ⟶ pt)
      ((G.obj (Opposite.op A)).obj A) s ≫
    CopowerGExtInj G pt A
  change HasPowers.lift
    (fun s => HasCopowers.inj (A ⟶ pt)
      ((G.obj (Opposite.op A)).obj A) s ≫
      (copowerGExtHomEndEquiv G pt cge
        (𝟙 cge)).val A) ≫
    HasPowers.proj cge (A ⟶ pt) s =
    HasCopowers.inj (A ⟶ pt)
      ((G.obj (Opposite.op A)).obj A) s ≫
    CopowerGExtInj G pt A
  rw [HasPowers.fac]
  congr 1
  change (copowerGExtHomEndEquiv G pt cge
    (𝟙 cge)).val A = CopowerGExtInj G pt A
  change (homOrdinaryWedge
    (copowerProf (HomToProf pt) G)
    (copowerCoend G pt) cge).ι A (𝟙 cge) =
    CopowerGExtInj G pt A
  unfold homOrdinaryWedge
  dsimp only [trivialWeightedWedgeWedgeEquiv,
    trivialWeightedCowedgeCowedgeEquiv,
    trivialWeightedWedgeConeEquiv,
    trivialWeightedCowedgeCoconeEquiv]
  simp only [Equivalence.symm_functor,
    Equivalence.symm_inverse,
    Equivalence.trans_functor,
    Equivalence.trans_inverse,
    Functor.comp_obj]
  dsimp only [wedgeConeEquiv, coneWeightedConeEquiv,
    coconeWeightedCoconeEquiv, cowedgeCoconeEquiv,
    Equivalence.symm, Equivalence.trans,
    Functor.comp_obj,
    coneToWedgeFunctor, coneToWedge,
    coneToWedgeComponents,
    weightedConeToConeFunctor,
    weightedConeToCone,
    coconeToWeightedCoconeFunctor,
    coconeToWeightedCocone,
    cowedgeToCoconeFunctor, cowedgeToCocone,
    homWeightedWedge]
  simp only [Wedge.mk_ι]
  erw [Category.comp_id]
  have h := cowedgeToCoconeιApp_at_id
    (copowerProf (HomToProf pt) G)
    (copowerCoend G pt).pt
    (fun j => Multicofork.π (copowerCoend G pt) j) A
  simp only [CopowerGExtInj]
  rw [← h]
  simp
  congr 1

omit [MonoidalCategory C] [MonoidalClosed C]
  [BraidedCategory C] [HasPowers C] in
private theorem copowerGExtHomEndEquiv_val
    (pt Y : C)
    (f : CopowerGExtObj G pt ⟶ Y) (A : C) :
    (copowerGExtHomEndEquiv G pt Y f).val A =
      CopowerGExtInj G pt A ≫ f := by
  change (homOrdinaryWedge
    (copowerProf (HomToProf pt) G)
    (copowerCoend G pt) Y).ι A f =
    CopowerGExtInj G pt A ≫ f
  unfold homOrdinaryWedge
  dsimp only [trivialWeightedWedgeWedgeEquiv,
    trivialWeightedCowedgeCowedgeEquiv,
    trivialWeightedWedgeConeEquiv,
    trivialWeightedCowedgeCoconeEquiv]
  simp only [Equivalence.symm_functor,
    Equivalence.symm_inverse,
    Equivalence.trans_functor,
    Equivalence.trans_inverse,
    Functor.comp_obj]
  dsimp only [wedgeConeEquiv, coneWeightedConeEquiv,
    coconeWeightedCoconeEquiv, cowedgeCoconeEquiv,
    Equivalence.symm, Equivalence.trans,
    Functor.comp_obj,
    coneToWedgeFunctor, coneToWedge,
    coneToWedgeComponents,
    weightedConeToConeFunctor,
    weightedConeToCone,
    coconeToWeightedCoconeFunctor,
    coconeToWeightedCocone,
    cowedgeToCoconeFunctor, cowedgeToCocone,
    homWeightedWedge]
  simp only [Wedge.mk_ι]
  have h := cowedgeToCoconeιApp_at_id
    (copowerProf (HomToProf pt) G)
    (copowerCoend G pt).pt
    (fun j =>
      Multicofork.π (copowerCoend G pt) j) A
  simp only [CopowerGExtInj]
  rw [← h]
  simp
  congr 1

private theorem churchLift_comp_backward
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : HasTerminalWedge
      (churchProf G pt twInner))
    (A : C) (s : A ⟶ pt) :
    churchLift G pt twInner twOuter A s ≫
      impredicativeGExtToCopowerGExt
        G pt twInner twOuter =
    HasCopowers.inj (A ⟶ pt)
      ((G.obj (Opposite.op A)).obj A) s ≫
      CopowerGExtInj G pt A := by
  let cge := CopowerGExtObj G pt
  let e := gExtEndPowerEquiv G pt cge (𝟙 cge)
  let gs := typeEndToGlobalSection G pt cge
    (twInner cge) e
  change churchLift G pt twInner twOuter A s ≫
    twOuter.wedge.ι cge ≫ ihomEvalAt gs =
    HasCopowers.inj (A ⟶ pt)
      ((G.obj (Opposite.op A)).obj A) s ≫
    CopowerGExtInj G pt A
  have fac :
      churchLift G pt twInner twOuter A s ≫
        Multifork.ι twOuter.wedge cge =
      churchComponent G pt twInner cge A s :=
    twOuter.isLimit.fac
      (Wedge.mk _
        (fun Y =>
          churchComponent G pt twInner Y A s)
        (fun {_ _} f =>
          churchComponent_wedge
            G pt twInner A s f))
      (WalkingMulticospan.left cge)
  rw [reassoc_of% fac]
  exact churchComponent_ihomEvalAt_eq
    G pt twInner A s

private theorem inj_comp_forward
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : HasTerminalWedge
      (churchProf G pt twInner))
    (A : C) :
    CopowerGExtInj G pt A ≫
      copowerGExtToImpredicativeGExt
        G pt twInner twOuter =
    HasCopowers.desc (fun s =>
      churchLift G pt twInner twOuter A s) := by
  rw [← copowerGExtHomEndEquiv_val]
  let ImpGExt :=
    ImpredicativeGExtObj G pt twInner twOuter
  change (copowerGExtHomEndEquiv G pt ImpGExt
    (copowerGExtToImpredicativeGExt
      G pt twInner twOuter)).val A = _
  unfold copowerGExtToImpredicativeGExt
    gExtEndPowerEquiv
  simp only [Equiv.symm_trans_apply]
  rw [(copowerGExtHomEndEquiv G pt ImpGExt
    ).apply_symm_apply]
  change (copowerPowerEquiv _ _ _).symm
    (HasPowers.lift
      (fun s => churchLift G pt twInner twOuter A s))
    = _
  simp only [copowerPowerEquiv_symm_apply]
  congr 1
  funext s
  simp only [HasPowers.fac]

theorem copowerGExt_backward_forward
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : HasTerminalWedge
      (churchProf G pt twInner)) :
    copowerGExtToImpredicativeGExt
      G pt twInner twOuter ≫
    impredicativeGExtToCopowerGExt
      G pt twInner twOuter =
    𝟙 (CopowerGExtObj G pt) := by
  apply (copowerGExtHomEndEquiv G pt
    (CopowerGExtObj G pt)).injective
  apply Subtype.ext
  funext A
  simp only [copowerGExtHomEndEquiv_val,
    Category.comp_id]
  apply HasCopowers.ext
  intro s
  rw [← Category.assoc (CopowerGExtInj G pt A),
    inj_comp_forward,
    ← Category.assoc (HasCopowers.inj _ _ s),
    HasCopowers.fac]
  exact churchLift_comp_backward
    G pt twInner twOuter A s

omit [BraidedCategory C] [HasCopowers C]
  [HasPowers C] [HasAllCopowerProfCoends G] in
private theorem ihomEvalAt_natural
    {X Y₁ Y₂ : C} (gs : 𝟙_ C ⟶ X)
    (f : Y₁ ⟶ Y₂) :
    (ihom X).map f ≫ ihomEvalAt gs =
      ihomEvalAt gs ≫ f := by
  simp only [ihomEvalAt]
  slice_lhs 1 2 =>
    rw [(MonoidalClosed.pre gs).naturality f]
  simp only [Category.assoc]
  congr 1
  slice_lhs 1 2 =>
    rw [leftUnitor_inv_naturality
      ((ihom (𝟙_ C)).map f)]
  simp only [Category.assoc]
  congr 1
  exact (ihom.ev (𝟙_ C)).naturality f

omit [HasCopowers C]
  [HasAllCopowerProfCoends G] in
private theorem churchComponent_powerSliceWedge
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (Y : C) {A₁ A₂ : C} (f : A₁ ⟶ A₂) :
    ((powerSliceProf G pt
        ((ihom ((twInner Y).wedge.pt)).obj Y)
      ).obj (Opposite.op A₁)).map f
      (HasPowers.lift (fun s =>
        churchComponent G pt twInner Y A₁ s)) =
    ((powerSliceProf G pt
        ((ihom ((twInner Y).wedge.pt)).obj Y)
      ).map f.op).app A₂
      (HasPowers.lift (fun s =>
        churchComponent G pt twInner Y A₂ s)) := by
  simp only [powerSliceProf]
  apply HasPowers.ext
  intro s
  simp only [Category.assoc]
  rw [HasPowers.mapIdx_proj]
  simp only [HasPowers.fac]
  simp only [Quiver.Hom.unop_op]
  exact churchComponent_dinatural
    G pt twInner Y f s

/-- The leg of a `churchProf`-wedge with apex
`CopowerGExtObj G pt`. For each `Y`, this produces
a morphism
`CopowerGExtObj G pt ⟶ [(twInner Y).pt, Y]`
by lifting the `churchComponent` family through the
coend and power structures. -/
def cgeChurchLeg
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (Y : C) :
    CopowerGExtObj G pt ⟶
      (ihom ((twInner Y).wedge.pt)).obj Y :=
  (gExtEndPowerEquiv G pt
    ((ihom ((twInner Y).wedge.pt)).obj Y)).symm
    ⟨fun A =>
      HasPowers.lift (fun s =>
        churchComponent G pt twInner Y A s),
    fun {_ _} f =>
      churchComponent_powerSliceWedge
        G pt twInner Y f⟩

private theorem fwd_comp_ι_eq_cgeChurchLeg
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : HasTerminalWedge
      (churchProf G pt twInner))
    (Y : C) :
    copowerGExtToImpredicativeGExt
      G pt twInner twOuter ≫
    Multifork.ι twOuter.wedge Y =
    cgeChurchLeg G pt twInner Y := by
  let Z := (ihom ((twInner Y).wedge.pt)).obj Y
  apply (copowerGExtHomEndEquiv G pt Z).injective
  apply Subtype.ext
  funext A
  rw [copowerGExtHomEndEquiv_val]
  rw [← Category.assoc,
    inj_comp_forward G pt twInner twOuter]
  -- LHS: HasCopowers.desc (churchLift A) ≫ ι Y
  -- RHS: CopowerGExtInj A ≫ cgeChurchLeg Y
  -- The cgeChurchLeg side: unfold and use
  -- gExtEndPowerEquiv.symm's defining property
  -- RHS: unfold cgeChurchLeg via gExtEndPowerEquiv
  unfold cgeChurchLeg gExtEndPowerEquiv
  simp only [Equiv.symm_trans_apply]
  rw [(copowerGExtHomEndEquiv G pt Z).apply_symm_apply]
  -- Now RHS is (endCopowerPowerEquiv.symm ⟨...⟩).val A
  -- which is copowerPowerEquiv.symm (HasPowers.lift ...)
  -- = HasCopowers.desc (fun s => HasPowers.lift ... ≫
  --   HasPowers.proj s)
  -- = HasCopowers.desc (fun s => churchComponent Y A s)
  -- RHS is endCopowerPowerEquiv.symm applied at A,
  -- which reduces to
  -- HasCopowers.desc (fun s =>
  --   HasPowers.lift (churchComponent Y A) ≫
  --   HasPowers.proj s)
  -- = HasCopowers.desc (fun s =>
  --   churchComponent Y A s)
  simp only [endCopowerPowerEquiv]
  change (HasCopowers.desc
    (fun s => churchLift G pt twInner twOuter A s)) ≫
    Multifork.ι twOuter.wedge Y =
    HasCopowers.desc (fun s =>
      HasPowers.lift
        (fun s' =>
          churchComponent G pt twInner Y A s') ≫
      HasPowers.proj _ _ s)
  apply HasCopowers.ext
  intro s
  -- LHS: inj(s) ≫ desc(churchLift A) ≫ ι Y
  rw [← Category.assoc, HasCopowers.fac]
  -- LHS: churchLift A s ≫ ι Y
  -- = churchComponent Y A s (by fac)
  have fac : churchLift G pt twInner twOuter A s ≫
      Multifork.ι twOuter.wedge Y =
    churchComponent G pt twInner Y A s :=
    twOuter.isLimit.fac
      (Wedge.mk _
        (fun Y' =>
          churchComponent G pt twInner Y' A s)
        (fun {_ _} f =>
          churchComponent_wedge
            G pt twInner A s f))
      (WalkingMulticospan.left Y)
  rw [fac]
  -- RHS: inj(s) ≫ desc(fun s' =>
  --   lift(churchComponent Y A) ≫ proj s')
  -- = lift(churchComponent Y A) ≫ proj s
  -- = churchComponent Y A s (by HasPowers.fac)
  simp only [HasCopowers.fac, HasPowers.fac]

private theorem cgeChurchLeg_wedge
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : HasTerminalWedge
      (churchProf G pt twInner))
    {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂) :
    cgeChurchLeg G pt twInner Y₁ ≫
      ((churchProf G pt twInner).obj
        (Opposite.op Y₁)).map f =
    cgeChurchLeg G pt twInner Y₂ ≫
      ((churchProf G pt twInner).map f.op).app Y₂ :=
  by
  rw [← fwd_comp_ι_eq_cgeChurchLeg G pt twInner
    twOuter,
    ← fwd_comp_ι_eq_cgeChurchLeg G pt twInner
    twOuter]
  simp only [Category.assoc]
  congr 1
  exact twOuter.wedge.condition f

/-- Type alias for the global section `gs` of the
inner end at `CopowerGExtObj`, derived from the
identity via `gExtEndPowerEquiv`. -/
private abbrev bwdGlobalSection
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y)) :
    𝟙_ C ⟶ (twInner (CopowerGExtObj G pt)).wedge.pt :=
  typeEndToGlobalSection G pt (CopowerGExtObj G pt)
    (twInner (CopowerGExtObj G pt))
    (gExtEndPowerEquiv G pt (CopowerGExtObj G pt)
      (𝟙 (CopowerGExtObj G pt)))

/-- Type alias for the functorial map on inner ends
induced by `cgeChurchLeg Y`. -/
private abbrev innerEndMap
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (Y : C) :
    (twInner (CopowerGExtObj G pt)).wedge.pt ⟶
      (twInner
        ((ihom ((twInner Y).wedge.pt)).obj Y)
      ).wedge.pt :=
  (ihomPowerEndFunctor G pt twInner).map
    (cgeChurchLeg G pt twInner Y)

omit [BraidedCategory C] [HasCopowers C]
  [HasPowers C] [HasAllCopowerProfCoends G] in
/-- `(pre h).app Z ≫ ihomEvalAt gs = ihomEvalAt
(gs ≫ h)` where `pre` is contravariant
precomposition on the internal hom. -/
private theorem pre_comp_ihomEvalAt
    {X X' Y : C} (gs : 𝟙_ C ⟶ X)
    (h : X ⟶ X') :
    (MonoidalClosed.pre h).app Y ≫ ihomEvalAt gs =
      ihomEvalAt (gs ≫ h) := by
  simp only [ihomEvalAt]
  slice_lhs 1 2 =>
    rw [← NatTrans.comp_app,
      ← MonoidalClosed.pre_map]
  simp only [Category.assoc]

/-- The outer wedge condition applied at the
morphism `cgeChurchLeg Y`, relating
`ι cge ≫ (ihom _).map (cgeChurchLeg Y)` to
`ι Z ≫ pre(innerEndMap)`. -/
private theorem ι_cge_ihomMap_cgeChurchLeg
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : HasTerminalWedge
      (churchProf G pt twInner))
    (Y : C) :
    let cge := CopowerGExtObj G pt
    let Z := (ihom ((twInner Y).wedge.pt)).obj Y
    Multifork.ι twOuter.wedge cge ≫
    (ihom (twInner cge).wedge.pt).map
      (cgeChurchLeg G pt twInner Y) =
    Multifork.ι twOuter.wedge Z ≫
    (MonoidalClosed.pre
      (innerEndMap G pt twInner Y)).app Z := by
  intro cge Z
  exact twOuter.wedge.condition
    (cgeChurchLeg G pt twInner Y)

/-- The coend injection at `A`, followed by
the copower injection at `s`, followed by
`cgeChurchLeg Y`, gives the Church component
at `Y`. -/
private theorem inj_inj_cgeChurchLeg
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : HasTerminalWedge
      (churchProf G pt twInner))
    (Y A : C) (s : A ⟶ pt) :
    HasCopowers.inj (A ⟶ pt)
      ((G.obj (Opposite.op A)).obj A) s ≫
    CopowerGExtInj G pt A ≫
    cgeChurchLeg G pt twInner Y =
    churchComponent G pt twInner Y A s := by
  rw [← fwd_comp_ι_eq_cgeChurchLeg G pt twInner
    twOuter Y,
    ← Category.assoc (CopowerGExtInj G pt A),
    inj_comp_forward G pt twInner twOuter A,
    ← Category.assoc, HasCopowers.fac]
  exact twOuter.isLimit.fac
    (Wedge.mk _
      (fun Y' =>
        churchComponent G pt twInner Y' A s)
      (fun {_ _} f =>
        churchComponent_wedge
          G pt twInner A s f))
    (WalkingMulticospan.left Y)

/-- Per-component enriched Yoneda chain: the Church
component at `Z = [(twInner Y).pt, Y]` composed with
`ihomEvalAt(gs ≫ m)` recovers the Church component
at `Y`. -/
private theorem churchComponent_Z_ihomEvalAt
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : HasTerminalWedge
      (churchProf G pt twInner))
    (Y A : C) (s : A ⟶ pt) :
    let Z := (ihom ((twInner Y).wedge.pt)).obj Y
    churchComponent G pt twInner Z A s ≫
    ihomEvalAt (bwdGlobalSection G pt twInner ≫
      innerEndMap G pt twInner Y) =
    churchComponent G pt twInner Y A s := by
  intro Z
  let cge := CopowerGExtObj G pt
  let gs := bwdGlobalSection G pt twInner
  let m := innerEndMap G pt twInner Y
  have expand : ihomEvalAt (gs ≫ m) =
      (MonoidalClosed.pre m).app Z ≫ ihomEvalAt gs :=
    (pre_comp_ihomEvalAt gs m).symm
  have wedge :
      churchComponent G pt twInner Z A s ≫
        (MonoidalClosed.pre m).app Z =
      churchComponent G pt twInner cge A s ≫
        (ihom (twInner cge).wedge.pt).map
          (cgeChurchLeg G pt twInner Y) :=
    (churchComponent_wedge G pt twInner A s
      (cgeChurchLeg G pt twInner Y)).symm
  rw [expand, ← Category.assoc, wedge,
    Category.assoc,
    ihomEvalAt_natural gs
      (cgeChurchLeg G pt twInner Y),
    ← Category.assoc,
    churchComponent_ihomEvalAt_eq G pt twInner A s,
    Category.assoc]
  exact inj_inj_cgeChurchLeg G pt twInner twOuter
    Y A s

/-- Lifting the per-component chain to the coend
level: `cgeChurchLeg Z ≫ ihomEvalAt(gs ≫ m)` equals
`cgeChurchLeg Y`. This is `fwd ≫ (target equation)`,
meaning `fwd` can be factored on the left. -/
private theorem cgeChurchLeg_Z_ihomEvalAt
    (pt : C)
    (twInner : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt Y))
    (twOuter : HasTerminalWedge
      (churchProf G pt twInner))
    (Y : C) :
    let Z := (ihom ((twInner Y).wedge.pt)).obj Y
    cgeChurchLeg G pt twInner Z ≫
    ihomEvalAt (bwdGlobalSection G pt twInner ≫
      innerEndMap G pt twInner Y) =
    cgeChurchLeg G pt twInner Y := by
  intro Z
  apply (copowerGExtHomEndEquiv G pt
    ((ihom ((twInner Y).wedge.pt)).obj Y)).injective
  apply Subtype.ext
  funext A
  simp only [copowerGExtHomEndEquiv_val]
  apply HasCopowers.ext
  intro s
  change HasCopowers.inj (A ⟶ pt) _ s ≫
      CopowerGExtInj G pt A ≫
      cgeChurchLeg G pt twInner Z ≫
      ihomEvalAt (bwdGlobalSection G pt twInner ≫
        innerEndMap G pt twInner Y) =
    HasCopowers.inj (A ⟶ pt) _ s ≫
      CopowerGExtInj G pt A ≫
      cgeChurchLeg G pt twInner Y
  rw [reassoc_of%
    (inj_inj_cgeChurchLeg G pt twInner twOuter
      Z A s),
    inj_inj_cgeChurchLeg G pt twInner twOuter
      Y A s]
  exact churchComponent_Z_ihomEvalAt G pt twInner
    twOuter Y A s

omit [HasCopowers C]
  [HasAllCopowerProfCoends G] in
private theorem churchComponent_churchProfMapPt
    {pt₁ pt₂ : C} (h : pt₁ ⟶ pt₂)
    (tw₁ : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt₁ Y))
    (tw₂ : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt₂ Y))
    (Y A : C) (s : A ⟶ pt₁) :
    churchComponent G pt₁ tw₁ Y A s ≫
      ((churchProfMapPt G h tw₁ tw₂).app
        (Opposite.op Y)).app Y =
    churchComponent G pt₂ tw₂ Y A (s ≫ h) := by
  simp only [churchComponent, churchProfMapPt]
  rw [curry_pre_app]
  congr 1
  slice_lhs 1 2 =>
    rw [← comp_whiskerRight,
      HasTerminalWedge.map_ι,
      comp_whiskerRight]
  simp only [Category.assoc]
  congr 1
  simp only [ihomPowerProfMapPt]
  conv_lhs =>
    rw [BraidedCategory.braiding_naturality_left_assoc]
  rw [ihom.ev_naturality_assoc]
  simp only [HasPowers.mapIdx_proj]
  rfl

omit [MonoidalCategory C] [MonoidalClosed C]
  [BraidedCategory C] [HasPowers C] in
private theorem copowerGExtIso_hom_eq_id
    (pt : C) :
    (copowerGExtIso G pt).hom = 𝟙 _ := by
  simp only [copowerGExtIso, Iso.symm_hom,
    isInitialCowedgeIso]
  have hroundtrip :
      (homRestrictedCopowerEquiv G pt).functor.obj
        (HasRestrictedCoend.restrictedCoend
          G (HomToProf pt)) =
      copowerCoend G pt :=
    restrictedToCopower_copowerToRestricted
      G pt (copowerCoend G pt)
  have h :
      (copowerCoendIsInitial G pt).to
        ((homRestrictedCopowerEquiv G pt).functor.obj
          (HasRestrictedCoend.restrictedCoend
            G (HomToProf pt))) =
      eqToHom hroundtrip.symm :=
    (copowerCoendIsInitial G pt).hom_ext _ _
  rw [h, Limits.Cowedge.eqToHom_hom]
  simp only [eqToHom_refl, CopowerGExtObj]

omit [MonoidalCategory C] [MonoidalClosed C]
  [BraidedCategory C] [HasPowers C] in
private theorem copowerGExtIso_inv_eq_id
    (pt : C) :
    (copowerGExtIso G pt).inv = 𝟙 _ := by
  have := copowerGExtIso_hom_eq_id G pt
  have hinv := (copowerGExtIso G pt).hom_inv_id
  rw [this, Category.id_comp] at hinv
  exact hinv

omit [MonoidalCategory C] [MonoidalClosed C]
  [BraidedCategory C] [HasPowers C] in
private theorem CopowerCoendGExtFunctor_map_eq
    {pt₁ pt₂ : C} (h : pt₁ ⟶ pt₂) :
    (CopowerCoendGExtFunctor G).map h =
    (GExtFunctor G).map h := by
  simp only [CopowerCoendGExtFunctor_map,
    copowerGExtIso_hom_eq_id,
    copowerGExtIso_inv_eq_id,
    Category.id_comp]
  exact Category.comp_id _

omit [MonoidalCategory C] [MonoidalClosed C]
  [BraidedCategory C] [HasPowers C] in
private theorem GExtInj_eq_inj_comp_copowerGExtInj
    (pt : C) (A : C) (s : A ⟶ pt) :
    GExtInj G pt A s =
    HasCopowers.inj (A ⟶ pt)
      ((G.obj (Opposite.op A)).obj A) s ≫
      CopowerGExtInj G pt A := by
  change
    (copowerCowedgeToRestrictedCowedge G pt
      (copowerCoend G pt)).family A s =
    HasCopowers.inj (A ⟶ pt)
      ((G.obj (Opposite.op A)).obj A) s ≫
      CopowerGExtInj G pt A
  simp only [copowerCowedgeToRestrictedCowedge,
    RestrictedCowedge.mk',
    RestrictedCowedge.family,
    copowerFamilyToRestrictedFamily,
    cowedgeToCopowerFamily,
    CopowerGExtInj]
  rfl

private theorem cgeChurchLeg_natural_pt
    {pt₁ pt₂ : C} (h : pt₁ ⟶ pt₂)
    (tw₁ : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt₁ Y))
    (tw₂ : ∀ Y : C,
      HasTerminalWedge (ihomPowerProf G pt₂ Y))
    (twO₁ : HasTerminalWedge
      (churchProf G pt₁ tw₁))
    (twO₂ : HasTerminalWedge
      (churchProf G pt₂ tw₂))
    (Y : C) :
    (GExtFunctor G).map h ≫
      cgeChurchLeg G pt₂ tw₂ Y =
    cgeChurchLeg G pt₁ tw₁ Y ≫
      ((churchProfMapPt G h tw₁ tw₂).app
        (Opposite.op Y)).app Y := by
  apply (copowerGExtHomEndEquiv G pt₁ _).injective
  apply Subtype.ext
  funext A
  simp only [copowerGExtHomEndEquiv_val]
  apply HasCopowers.ext
  intro s
  simp only [← Category.assoc]
  change
    ((HasCopowers.inj (A ⟶ pt₁) _ s ≫
          CopowerGExtInj G pt₁ A) ≫
        (GExtFunctor G).map h) ≫
      cgeChurchLeg G pt₂ tw₂ Y =
    ((HasCopowers.inj (A ⟶ pt₁) _ s ≫
          CopowerGExtInj G pt₁ A) ≫
        cgeChurchLeg G pt₁ tw₁ Y) ≫
      ((churchProfMapPt G h tw₁ tw₂).app
        (Opposite.op Y)).app Y
  rw [← GExtInj_eq_inj_comp_copowerGExtInj]
  simp only [Category.assoc]
  have hcomm :=
    ((HasRestrictedCoend.restrictedCoendIsInitial
        G (HomToProf pt₁)).desc
      (GExtMapCowedge G pt₁ pt₂ h)).comm A s
  change GExtInj G pt₁ A s ≫
    (GExtFunctor G).map h =
    GExtInj G pt₂ A (s ≫ h) at hcomm
  have hlhs :
      GExtInj G pt₁ A s ≫
        (GExtFunctor G).map h ≫
        cgeChurchLeg G pt₂ tw₂ Y =
      churchComponent G pt₂ tw₂ Y A
        (s ≫ h) := by
    rw [← Category.assoc, hcomm,
      GExtInj_eq_inj_comp_copowerGExtInj,
      Category.assoc]
    exact inj_inj_cgeChurchLeg
      G pt₂ tw₂ twO₂ Y A (s ≫ h)
  have step1 :
      GExtInj G pt₁ A s ≫
        cgeChurchLeg G pt₁ tw₁ Y =
      churchComponent G pt₁ tw₁ Y A s := by
    rw [GExtInj_eq_inj_comp_copowerGExtInj,
      Category.assoc]
    exact inj_inj_cgeChurchLeg
      G pt₁ tw₁ twO₁ Y A s
  have hrhs :
      GExtInj G pt₁ A s ≫
        cgeChurchLeg G pt₁ tw₁ Y ≫
        ((churchProfMapPt G h tw₁ tw₂).app
          (Opposite.op Y)).app Y =
      churchComponent G pt₂ tw₂ Y A
        (s ≫ h) := by
    rw [← Category.assoc, step1]
    exact churchComponent_churchProfMapPt
      G h tw₁ tw₂ Y A s
  rw [hlhs, hrhs]

end ImpredicativeGExtIso

/-!
## Power-End GExtFunctor via Coend-End Duality

The `PowerEndGExtFunctor` is an endofunctor `C ⥤ C`
with the same carrier as `CopowerCoendGExtFunctor G`
but with maps defined via the end/power
characterization (`powerEndGExtMap`). It is naturally
isomorphic to `CopowerCoendGExtFunctor G`, yielding
an equivalence
`PowerEndMendlerAlgebra G ≌
  ConventionalAlgebra (PowerEndGExtFunctor G)`.
-/

section PowerEndGExtFunctor

open HasAllCopowerProfCoends HasAllHomToProfCoends
  HasRestrictedCoend

variable
  {C : Type u} [Category.{v} C]
  [HasCopowers C] [HasPowers C]
  (G : Cᵒᵖ ⥤ C ⥤ C)
  [HasAllCopowerProfCoends G]

/-- Projection formula for `gExtEndPowerEquiv`:
at component `A` and projection `s`, the end
element encodes the coend injection.

`(gExtEndPowerEquiv G pt Y f).val A ≫ proj s =
  inj s ≫ CopowerGExtInj G pt A ≫ f` -/
theorem gExtEndPowerEquiv_proj
    (pt Y : C) (f : CopowerGExtObj G pt ⟶ Y)
    (A : C) (s : A ⟶ pt) :
    (gExtEndPowerEquiv G pt Y f).val A ≫
      HasPowers.proj Y (A ⟶ pt) s =
    HasCopowers.inj (A ⟶ pt)
        ((G.obj (Opposite.op A)).obj A) s ≫
      CopowerGExtInj G pt A ≫ f := by
  change copowerPowerEquiv (A ⟶ pt)
    ((G.obj (Opposite.op A)).obj A) Y
    ((copowerGExtHomEndEquiv G pt Y f).val A) ≫
    HasPowers.proj Y (A ⟶ pt) s = _
  simp only [copowerPowerEquiv_apply,
    HasPowers.fac]
  congr 1
  exact copowerGExtHomEndEquiv_val G pt Y f A

/-- The commutativity property of `powerEndGExtMap`
with respect to coend injections: precomposing
`powerEndGExtMap G h` with the coend injection at
`(A, s)` gives the injection at `(A, s ≫ h)` into
`CopowerGExtObj G pt₂`. -/
theorem inj_comp_powerEndGExtMap
    {pt₁ pt₂ : C} (h : pt₁ ⟶ pt₂)
    (A : C) (s : A ⟶ pt₁) :
    HasCopowers.inj (A ⟶ pt₁)
        ((G.obj (Opposite.op A)).obj A) s ≫
      CopowerGExtInj G pt₁ A ≫
      powerEndGExtMap G h =
    HasCopowers.inj (A ⟶ pt₂)
        ((G.obj (Opposite.op A)).obj A) (s ≫ h) ≫
      CopowerGExtInj G pt₂ A := by
  rw [← gExtEndPowerEquiv_proj G pt₁ _ _ A s]
  simp only [powerEndGExtMap,
    Equiv.apply_symm_apply]
  change ((gExtEndPowerEquiv G pt₂ _
    (𝟙 _)).val A ≫ HasPowers.mapIdx (· ≫ h)) ≫
    HasPowers.proj _ _ s = _
  rw [Category.assoc, HasPowers.mapIdx_proj,
    gExtEndPowerEquiv_proj G pt₂ _
      (𝟙 _) A (s ≫ h), Category.comp_id]

/-- `powerEndGExtMap` preserves composition:
`powerEndGExtMap G (h₁ ≫ h₂) =
  powerEndGExtMap G h₁ ≫ powerEndGExtMap G h₂`.
Proved using the coend injection commutativity:
both sides yield the same result after precomposing
with each coend injection. -/
theorem powerEndGExtMap_comp
    {pt₁ pt₂ pt₃ : C}
    (h₁ : pt₁ ⟶ pt₂) (h₂ : pt₂ ⟶ pt₃) :
    powerEndGExtMap G (h₁ ≫ h₂) =
      powerEndGExtMap G h₁ ≫
        powerEndGExtMap G h₂ := by
  apply (gExtEndPowerEquiv G pt₁
    (CopowerGExtObj G pt₃)).injective
  apply Subtype.ext; funext A
  apply HasPowers.ext; intro s
  rw [gExtEndPowerEquiv_proj,
    gExtEndPowerEquiv_proj,
    inj_comp_powerEndGExtMap G (h₁ ≫ h₂) A s]
  symm
  rw [← Category.assoc
    (CopowerGExtInj G pt₁ A)
    (powerEndGExtMap G h₁)
    (powerEndGExtMap G h₂),
    ← Category.assoc
      (HasCopowers.inj _ _ s)
      (CopowerGExtInj G pt₁ A ≫
        powerEndGExtMap G h₁)
      (powerEndGExtMap G h₂),
    inj_comp_powerEndGExtMap G h₁ A s,
    Category.assoc
      (HasCopowers.inj _ _ (s ≫ h₁))
      (CopowerGExtInj G pt₂ A)
      (powerEndGExtMap G h₂),
    inj_comp_powerEndGExtMap G h₂ A (s ≫ h₁),
    Category.assoc s h₁ h₂]

/-- The end-based GExtFunctor: an endofunctor
`C ⥤ C` with the same carrier as
`CopowerCoendGExtFunctor G` but with maps defined
via the end/power characterization
`powerEndGExtMap`. -/
@[simps]
def PowerEndGExtFunctor : C ⥤ C where
  obj pt := CopowerGExtObj G pt
  map h := powerEndGExtMap G h
  map_id pt := powerEndGExtMap_id G pt
  map_comp h₁ h₂ := powerEndGExtMap_comp G h₁ h₂

/-- The end-based map `powerEndGExtMap G h` equals
`(GExtFunctor G).map h`: both are the unique morphism
from the initial restricted coend at `pt₁` to the
cowedge at `pt₂` obtained by reindexing injections
along `h`. -/
private theorem powerEndGExtMap_eq_GExtMap
    {pt₁ pt₂ : C} (h : pt₁ ⟶ pt₂) :
    powerEndGExtMap G h =
      (GExtFunctor G).map h := by
  let hmorphPE :
      (restrictedCoend G (HomToProf pt₁)) ⟶
        (GExtMapCowedge G pt₁ pt₂ h) := {
    hom := powerEndGExtMap G h
    comm := fun A s => by
      change GExtInj G pt₁ A s ≫
        powerEndGExtMap G h =
        GExtInj G pt₂ A (s ≫ h)
      rw [GExtInj_eq_inj_comp_copowerGExtInj
        G pt₁ A s, Category.assoc,
        inj_comp_powerEndGExtMap G h A s,
        ← GExtInj_eq_inj_comp_copowerGExtInj
          G pt₂ A (s ≫ h)]
  }
  have heq : hmorphPE =
      (restrictedCoendIsInitial G
        (HomToProf pt₁)).to
        (GExtMapCowedge G pt₁ pt₂ h) :=
    (restrictedCoendIsInitial G
      (HomToProf pt₁)).hom_ext hmorphPE _
  simp only [GExtFunctor_map, GExtMap,
    GExtDesc, IsRestrictedCoend.descHom,
    IsRestrictedCoend.desc]
  exact congrArg RestrictedCowedge.Hom.hom heq

/-- `PowerEndGExtFunctor G` equals
`CopowerCoendGExtFunctor G` on morphisms: both
conjugate through the (trivial) isomorphism
`copowerGExtIso` and the restricted coend universal
property. -/
private theorem powerEndGExtMap_eq
    {pt₁ pt₂ : C} (h : pt₁ ⟶ pt₂) :
    powerEndGExtMap G h =
      (CopowerCoendGExtFunctor G).map h := by
  rw [powerEndGExtMap_eq_GExtMap,
    ← CopowerCoendGExtFunctor_map_eq]

/-- Natural isomorphism between
`PowerEndGExtFunctor G` and
`CopowerCoendGExtFunctor G`: the component at each
object is `Iso.refl` (both functors have the same
carrier `CopowerGExtObj G pt`). -/
def powerEndGExtNatIso :
    PowerEndGExtFunctor G ≅
      CopowerCoendGExtFunctor G :=
  NatIso.ofComponents
    (fun _ => Iso.refl _)
    (fun h => by
      simp only [PowerEndGExtFunctor_map,
        Iso.refl_hom, Category.id_comp,
        Category.comp_id]
      exact powerEndGExtMap_eq G h)

/-- The equivalence of power-end Mendler algebras
with conventional algebras of
`PowerEndGExtFunctor G`, obtained by composing
`mendlerLambekCopowerCoendEquiv` with the transfer
along `powerEndGExtNatIso`. -/
def mendlerLambekPowerEndGExtEquiv :
    PowerEndMendlerAlgebra G ≌
      ConventionalAlgebra
        (PowerEndGExtFunctor G) :=
  mendlerLambekCopowerCoendEquiv G |>.trans
    (Endofunctor.Algebra.equivOfNatIso
      (powerEndGExtNatIso G).symm)

/-- The full Mendler-Lambek equivalence between
Mendler algebras and conventional algebras of
`PowerEndGExtFunctor G`, obtained by composing
`mendlerAlgPowerEndEquiv` (power-end algebra
equivalence) with `mendlerLambekPowerEndGExtEquiv`
(power-end algebra to conventional algebra). -/
def mendlerLambekGExtEquiv :
    MendlerAlgebra G ≌
      ConventionalAlgebra
        (PowerEndGExtFunctor G) :=
  mendlerAlgPowerEndEquiv G |>.trans
    (mendlerLambekPowerEndGExtEquiv G)

end PowerEndGExtFunctor

/-!
## Internal End Characterization of GExt

The internal end `∫_A (G(A,A) →[C] Y^(A→pt))`,
defined as the terminal wedge of `ihomPowerProf G pt Y`,
gives an object of `C` characterized entirely by ends,
powers, and internal homs — no copowers or coends.

When copowers also exist, this end object is naturally
isomorphic to `ihom(CopowerGExtObj G pt).obj Y`: the
internal hom from the coend to `Y`. The isomorphism
`ihomPowerEndIso` bridges the end-based and coend-based
worlds, and enables transferring the functor structure
from `PowerEndGExtFunctor` to a functor with end-based
carrier.
-/

section IhomPowerEndGExt

variable
  {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [MonoidalClosed C]
  [HasCopowers C] [HasPowers C]
  (G : Cᵒᵖ ⥤ C ⥤ C)
  [HasAllCopowerProfCoends G]

/-- The internal-end based GExt object: the terminal
wedge apex of `ihomPowerProf G pt Y`, giving
`∫_A (G(A,A) →[C] Y^(A→pt))`. This object is defined
entirely via ends, powers, and internal homs. -/
def GExtPowerEndObj
    (pt Y : C)
    (tw : HasTerminalWedge (ihomPowerProf G pt Y)) :
    C :=
  tw.wedge.pt

open MonoidalClosed MonoidalCategory
  HasAllCopowerProfCoends

omit [HasCopowers C] [HasPowers C] in
private theorem uncurry'_pre_comp
    {X X' Z : C}
    (g : 𝟙_ C ⟶ (ihom X).obj Z)
    (h : X' ⟶ X) :
    h ≫ uncurry' g =
      uncurry' (g ≫ (MonoidalClosed.pre h).app Z) := by
  conv_rhs => rw [← curry'_uncurry' g]
  rw [curry'_pre_app, uncurry'_curry']

omit [HasCopowers C] [HasPowers C] in
private theorem uncurry'_ihom_comp
    {X Y Z : C}
    (g : 𝟙_ C ⟶ (ihom X).obj Y)
    (k : Y ⟶ Z) :
    uncurry' g ≫ k =
      uncurry' (g ≫ (ihom X).map k) := by
  conv_rhs => rw [← curry'_uncurry' g]
  rw [curry'_ihom_map, uncurry'_curry']

/-- Global sections of the internal end correspond to
elements of the type-level end: currying components of
a wedge into `ihomPowerProf` yields the corresponding
end element of `powerSliceProf`.
The forward direction uncurries each wedge projection,
and the inverse curries each end component and lifts
via the terminal wedge. -/
def globalSectionsEndEquiv
    (pt Y : C)
    (tw : HasTerminalWedge
      (ihomPowerProf G pt Y)) :
    (𝟙_ C ⟶ tw.wedge.pt) ≃
      typeEnd (powerSliceProf G pt Y) where
  toFun e :=
    ⟨fun A => uncurry' (e ≫ tw.wedge.ι A),
     fun {i j} f => by
       dsimp only [powerSliceProf]
       rw [← Category.assoc,
         uncurry'_pre_comp _ _,
         uncurry'_ihom_comp _ _,
         uncurry'_pre_comp _ _]
       congr 1
       simp only [Category.assoc]
       exact congrArg (e ≫ ·)
         (tw.wedge.condition f)⟩
  invFun x :=
    Wedge.IsLimit.lift tw.isLimit
      (fun A => curry' (x.val A))
      (fun {i j} f => by
        dsimp only []
        simp only [ihomPowerProf]
        rw [← Category.assoc,
          curry'_pre_app,
          curry'_ihom_map,
          curry'_pre_app]
        congr 1
        have h := x.property f
        dsimp only [powerSliceProf] at h
        rw [Category.assoc]
        exact h)
  left_inv e := by
    apply tw.hom_ext
    intro A
    rw [Wedge.IsLimit.lift_ι]
    exact curry'_uncurry' _
  right_inv x := by
    apply Subtype.ext; funext A
    dsimp only []
    rw [Wedge.IsLimit.lift_ι]
    exact uncurry'_curry' _

/-- The global-sections bridge: morphisms into the
internal end (terminal wedge apex) correspond to
morphisms into the internal hom from the coend.
Composes `globalSectionsEndEquiv`,
`gExtEndPowerEquiv.symm`, and `curryHomEquiv'`. -/
def globalSectionsIhomEquiv
    (pt Y : C)
    (tw : HasTerminalWedge
      (ihomPowerProf G pt Y)) :
    (𝟙_ C ⟶ tw.wedge.pt) ≃
      (𝟙_ C ⟶ (ihom (CopowerGExtObj G pt)).obj Y) :=
  (globalSectionsEndEquiv G pt Y tw).trans
    ((gExtEndPowerEquiv G pt Y).symm.trans
      curryHomEquiv')

omit [HasAllCopowerProfCoends G] in
/-- The internal copower-power forward map: sends
`[S . X, Y] ⟶ [X, Y^S]`. For each `s : S`, the
coprojection `ι s : X ⟶ S . X` whiskers with the
evaluation `S . X ⊗ [S . X, Y] ⟶ Y` to give
`X ⊗ [S . X, Y] ⟶ Y`, then the family is
assembled via the power lift and curried. -/
def copowerIhomToPowerIhom
    (S : Type v) (X Y : C) :
    (ihom (HasCopowers.copower S X)).obj Y ⟶
      (ihom X).obj (HasPowers.power Y S) :=
  MonoidalClosed.curry
    (HasPowers.lift (fun s =>
      HasCopowers.inj S X s ▷
        (ihom (HasCopowers.copower S X)).obj Y ≫
        MonoidalClosed.uncurry (𝟙 _)))

omit [HasAllCopowerProfCoends G] in
/-- Naturality of the copower-ihom-to-power-ihom
map: composing with `pre h` and `(ihom X').map
(mapIdx g)` on the codomain equals precomposing
with `bimap g h` on the domain. -/
lemma copowerIhomToPowerIhom_natural
    {S T : Type v} {X X' Y : C}
    (g : T → S) (h : X' ⟶ X) :
    copowerIhomToPowerIhom S X Y ≫
      (MonoidalClosed.pre h).app
        (HasPowers.power Y S) ≫
      (ihom X').map
        (HasPowers.mapIdx g) =
    (MonoidalClosed.pre
      (HasCopowers.bimap g h)).app Y ≫
      copowerIhomToPowerIhom T X' Y := by
  simp only [copowerIhomToPowerIhom]
  rw [← Category.assoc
    (MonoidalClosed.curry _)
    ((MonoidalClosed.pre _).app _),
    MonoidalClosed.curry_pre_app,
    ← MonoidalClosed.curry_natural_right,
    ← MonoidalClosed.curry_natural_left]
  congr 1
  apply HasPowers.ext; intro t
  simp only [Category.assoc,
    HasPowers.mapIdx_proj, HasPowers.fac]
  rw [← Category.assoc
    (h ▷ _) (HasCopowers.inj S X (g t) ▷ _),
    ← comp_whiskerRight,
    ← HasCopowers.bimap_inj, comp_whiskerRight,
    Category.assoc]
  conv_rhs =>
    rw [← Category.assoc, whisker_exchange,
      Category.assoc]
  rw [← MonoidalClosed.uncurry_natural_left,
    Category.comp_id,
    MonoidalClosed.uncurry_pre,
    ← MonoidalClosed.uncurry_id_eq_ev]

omit [HasAllCopowerProfCoends G] in
/-- Precomposition with `copowerIhomToPowerIhom`:
expresses `f ≫ copowerIhomToPowerIhom S X Y` as a
curried power lift where each component whiskers
the copower injection by `Z` and evaluates via
`uncurry f`. -/
lemma comp_copowerIhomToPowerIhom
    {S : Type v} {X Z Y : C}
    (f : Z ⟶
      (ihom (HasCopowers.copower S X)).obj Y) :
    f ≫ copowerIhomToPowerIhom S X Y =
    MonoidalClosed.curry
      (HasPowers.lift (fun t =>
        (HasCopowers.inj S X t) ▷ Z ≫
          MonoidalClosed.uncurry f)) := by
  simp only [copowerIhomToPowerIhom]
  rw [← MonoidalClosed.curry_natural_left]
  congr 1
  apply HasPowers.ext; intro t
  simp only [Category.assoc, HasPowers.fac]
  rw [← Category.assoc,
    whisker_exchange, Category.assoc,
    ← MonoidalClosed.uncurry_natural_left,
    Category.comp_id]

omit [HasAllCopowerProfCoends G] in
/-- Naturality of `copowerIhomToPowerIhom` in the
target object `Y`: the map commutes with applying
`(ihom _).map f` on the domain and
`(ihom X).map (HasPowers.mapVal f)` on the
codomain. -/
lemma copowerIhomToPowerIhom_naturalY
    {S : Type v} {X : C} {Y₁ Y₂ : C}
    (f : Y₁ ⟶ Y₂) :
    (ihom (HasCopowers.copower S X)).map f ≫
      copowerIhomToPowerIhom S X Y₂ =
    copowerIhomToPowerIhom S X Y₁ ≫
      (ihom X).map (HasPowers.mapVal f) := by
  simp only [copowerIhomToPowerIhom]
  rw [← curry_natural_left,
    ← curry_natural_right]
  congr 1
  apply HasPowers.ext; intro t
  simp only [Category.assoc]
  rw [HasPowers.fac, HasPowers.mapVal_proj,
    ← Category.assoc (HasPowers.lift _),
    HasPowers.fac, Category.assoc]
  rw [← Category.assoc
    (X ◁ (ihom (HasCopowers.copower S X)).map f),
    whisker_exchange, Category.assoc]
  congr 1
  rw [← uncurry_natural_left,
    Category.comp_id,
    ← uncurry_natural_right,
    Category.id_comp]

/-- The wedge projection for the internal hom
from the coend: at `A`, precompose with the coend
injection and apply the internal copower-power map.
-/
def ihomCoendWedgeProj
    (pt Y : C) (A : C) :
    (ihom (CopowerGExtObj G pt)).obj Y ⟶
      (ihomPowerProf G pt Y).obj
        (Opposite.op A) |>.obj A :=
  (MonoidalClosed.pre
    (CopowerGExtInj G pt A)).app Y ≫
    copowerIhomToPowerIhom
      (A ⟶ pt)
      ((G.obj (Opposite.op A)).obj A) Y

/-- The internal hom from the coend carries a
wedge structure for `ihomPowerProf G pt Y`. -/
def ihomCoendWedge
    (pt Y : C) :
    Wedge (ihomPowerProf G pt Y) :=
  Wedge.mk
    ((ihom (CopowerGExtObj G pt)).obj Y)
    (ihomCoendWedgeProj G pt Y)
    (fun {i j} f => by
      simp only [ihomCoendWedgeProj,
        ihomPowerProf, Category.assoc]
      rw [copowerIhomToPowerIhom_natural]
      rw [← Category.assoc
        ((MonoidalClosed.pre
          (CopowerGExtInj G pt i)).app Y)
        ((MonoidalClosed.pre _).app Y),
        ← NatTrans.comp_app,
        ← MonoidalClosed.pre_map]
      have cw : HasCopowers.bimap (fun x ↦ f ≫ x)
          ((G.map f.op).app i) ≫
          CopowerGExtInj G pt i =
        HasCopowers.bimap (fun x ↦ x)
          ((G.obj (Opposite.op j)).map f) ≫
          CopowerGExtInj G pt j := by
        apply HasCopowers.ext; intro s
        conv_lhs =>
          rw [← Category.assoc,
            HasCopowers.bimap_inj,
            Category.assoc]
        conv_rhs =>
          rw [← Category.assoc,
            HasCopowers.bimap_inj,
            Category.assoc]
        have h :=
          cowedge_is_copowerCowedgeDinatural
            (HomToProf pt) G
            (copowerCoend G pt) i j f s
        simp only [HomToProf_map_app,
          HomToProf_obj_map,
          Quiver.Hom.unop_op] at h
        exact h.symm
      rw [cw, MonoidalClosed.pre_map,
        NatTrans.comp_app, Category.assoc]
      congr 1
      simp only [Quiver.Hom.unop_op]
      have h_nat :=
        copowerIhomToPowerIhom_natural
          (Y := Y)
          (fun (x : j ⟶ pt) ↦ x)
          ((G.obj (Opposite.op j)).map f)
      have mapIdx_eq :
          HasPowers.mapIdx
            (fun (x : j ⟶ pt) ↦ x) =
          𝟙 (Y ^. (j ⟶ pt)) :=
        HasPowers.mapIdx_id
      rw [mapIdx_eq,
        CategoryTheory.Functor.map_id,
        Category.comp_id] at h_nat
      exact h_nat.symm)

end IhomPowerEndGExt

section IhomPowerEndGExtBraided

variable
  {C : Type u} [Category.{v} C]
  [MonoidalCategory C] [MonoidalClosed C]
  [SymmetricCategory C]
  [HasCopowers C] [HasPowers C]
  (G : Cᵒᵖ ⥤ C ⥤ C)
  [HasAllCopowerProfCoends G]

open MonoidalClosed MonoidalCategory
  HasAllCopowerProfCoends

/-- Given a wedge `s` for `ihomPowerProf G pt Y` with
apex `Z`, this produces for each `A : C` and
`t : A ⟶ pt` a morphism `G(A,A) ⟶ [Z, Y]`. The
construction whiskers the wedge projection, braids to
evaluation position, evaluates, and projects. -/
def ihomCoendLiftComponent
    (pt Y : C) (s : Wedge (ihomPowerProf G pt Y))
    (A : C) (t : A ⟶ pt) :
    (G.obj (Opposite.op A)).obj A ⟶
      (ihom s.pt).obj Y :=
  let GA := (G.obj (Opposite.op A)).obj A
  let YpowA := HasPowers.power Y (A ⟶ pt)
  let sProj : s.pt ⟶ (ihom GA).obj YpowA :=
    s.ι A
  curry (sProj ▷ GA ≫
    (β_ _ GA).hom ≫
    (ihom.ev GA).app YpowA ≫
    HasPowers.proj Y (A ⟶ pt) t)

omit [HasCopowers C] [HasPowers C]
  [HasAllCopowerProfCoends G] in
private theorem whisker_braided_eval_pre'
    {W X X' Y' : C}
    (ι : W ⟶ (ihom X).obj Y') (h : X' ⟶ X) :
    W ◁ h ≫ ι ▷ X ≫
      (β_ ((ihom X).obj Y') X).hom ≫
      (ihom.ev X).app Y' =
    (ι ≫ (MonoidalClosed.pre h).app Y') ▷
        X' ≫
      (β_ ((ihom X').obj Y') X').hom ≫
      (ihom.ev X').app Y' := by
  slice_lhs 1 2 => rw [whisker_exchange]
  slice_lhs 2 3 =>
    rw [BraidedCategory.braiding_naturality_right]
  slice_lhs 3 4 =>
    rw [← id_tensor_pre_app_comp_ev]
  slice_lhs 2 3 =>
    rw [← BraidedCategory.braiding_naturality_left]
  slice_lhs 1 2 => rw [← comp_whiskerRight]
  simp only [Category.assoc]

omit [HasCopowers C]
  [HasAllCopowerProfCoends G] in
/-- Dinaturality of `ihomCoendLiftComponent`: for
`f : A₁ ⟶ A₂` and `t : A₂ ⟶ pt`, precomposing with
`(G.map f.op).app A₁` on one side matches
precomposing with `(G.obj (op A₂)).map f` on the
other. -/
theorem ihomCoendLiftComponent_dinatural
    (pt Y : C) (s : Wedge (ihomPowerProf G pt Y))
    {A₁ A₂ : C} (f : A₁ ⟶ A₂) (t : A₂ ⟶ pt) :
    (G.map f.op).app A₁ ≫
      ihomCoendLiftComponent G pt Y s A₁ (f ≫ t) =
    (G.obj (Opposite.op A₂)).map f ≫
      ihomCoendLiftComponent G pt Y s A₂ t := by
  simp only [ihomCoendLiftComponent]
  have wedgeCond := s.condition f
  simp only [ihomPowerProf] at wedgeCond
  simp only [Quiver.Hom.unop_op] at wedgeCond
  rw [← curry_natural_left, ← curry_natural_left]
  congr 1
  rw [← HasPowers.mapIdx_proj]
  slice_lhs 1 4 =>
    rw [whisker_braided_eval_pre']
  slice_lhs 3 4 =>
    rw [← ihom.ev_naturality]
  slice_lhs 2 3 =>
    rw [←
      BraidedCategory.braiding_naturality_left]
  slice_lhs 1 2 => rw [← comp_whiskerRight]
  simp only [Category.assoc]
  rw [wedgeCond]
  symm
  slice_lhs 1 4 =>
    rw [whisker_braided_eval_pre']
  simp only [Category.assoc]

/-- Assembles the lift components via the copower
universal property: for each `A`, descends the family
`t ↦ ihomCoendLiftComponent G pt Y s A t` to produce
`(A ⟶ pt) · G(A,A) ⟶ [Z, Y]`. -/
def ihomCoendLiftCopowerMap
    (pt Y : C) (s : Wedge (ihomPowerProf G pt Y))
    (A : C) :
    HasCopowers.copower (A ⟶ pt)
      ((G.obj (Opposite.op A)).obj A) ⟶
      (ihom s.pt).obj Y :=
  HasCopowers.desc
    (ihomCoendLiftComponent G pt Y s A)

/-- Cowedge for `copowerProf (HomToProf pt) G` with
apex `(ihom s.pt).obj Y`, assembled from the copower
maps `ihomCoendLiftCopowerMap`. The cowedge condition
follows from `ihomCoendLiftComponent_dinatural`. -/
def ihomCoendLiftCowedge
    (pt Y : C) (s : Wedge (ihomPowerProf G pt Y)) :
    HomCopowerCowedge G pt :=
  Cowedge.mk ((ihom s.pt).obj Y)
    (fun A => ihomCoendLiftCopowerMap G pt Y s A)
    (fun {A₁ A₂} f => by
      simp only [copowerProf_map_app,
        copowerProf_obj_map]
      apply HasCopowers.ext
      intro t
      rw [reassoc_of% HasCopowers.bimap_inj,
        ihomCoendLiftCopowerMap,
        HasCopowers.fac]
      rw [reassoc_of% HasCopowers.bimap_inj,
        ihomCoendLiftCopowerMap,
        HasCopowers.fac]
      simp only [HomToProf_map_app,
        Quiver.Hom.unop_op,
        HomToProf_obj_map]
      exact ihomCoendLiftComponent_dinatural
        G pt Y s f t)

/-- The lift from `CopowerGExtObj G pt` to
`(ihom s.pt).obj Y`, obtained from the coend's
initiality applied to `ihomCoendLiftCowedge`. -/
def ihomCoendLift
    (pt Y : C) (s : Wedge (ihomPowerProf G pt Y)) :
    CopowerGExtObj G pt ⟶ (ihom s.pt).obj Y :=
  ((copowerCoendIsInitial G pt).to
    (ihomCoendLiftCowedge G pt Y s)).hom

/-- The lift for wedge terminality: given a wedge
`s` for `ihomPowerProf G pt Y`, produce
`s.pt ⟶ [CopowerGExtObj G pt, Y]` by swapping
`ihomCoendLift` through the braiding. -/
def ihomCoendWedgeLift
    (pt Y : C)
    (s : Wedge (ihomPowerProf G pt Y)) :
    s.pt ⟶ (ihom (CopowerGExtObj G pt)).obj Y :=
  curry
    ((β_ (CopowerGExtObj G pt) s.pt).hom ≫
    uncurry (ihomCoendLift G pt Y s))

/-- The factorization property: the lift composed
with each wedge projection of `ihomCoendWedge`
recovers the original wedge projection. -/
theorem ihomCoendWedgeLift_fac
    (pt Y : C)
    (s : Wedge (ihomPowerProf G pt Y))
    (A : C) :
    ihomCoendWedgeLift G pt Y s ≫
      (ihomCoendWedge G pt Y).ι A =
    s.ι A := by
  simp only [ihomCoendWedgeLift,
    ihomCoendWedge, Wedge.mk_ι,
    ihomCoendWedgeProj]
  rw [← Category.assoc, curry_pre_app]
  -- Goal:
  -- curry (CopowerGExtInj G pt A ▷ s.pt ≫
  --   β_.hom ≫ uncurry (ihomCoendLift ...))
  -- ≫ copowerIhomToPowerIhom ... = s.ι A
  -- Use braiding naturality:
  -- f ▷ Y ≫ β_.hom = β_.hom ≫ Y ◁ f
  rw [BraidedCategory.braiding_naturality_left_assoc]
  -- Now: curry (β_.hom ≫ s.pt ◁ CopowerGExtInj ...
  --   ≫ uncurry (ihomCoendLift ...)) ≫ ...
  -- Use uncurry_natural_left:
  -- Y ◁ f ≫ uncurry g = uncurry (f ≫ g)
  rw [← uncurry_natural_left]
  -- Now use the coend factorization:
  -- CopowerGExtInj G pt A ≫ ihomCoendLift G pt Y s
  -- = (ihomCoendLiftCowedge G pt Y s).π A
  have coendFac :
      CopowerGExtInj G pt A ≫
        ihomCoendLift G pt Y s =
      ihomCoendLiftCopowerMap G pt Y s A := by
    simp only [ihomCoendLift,
      ihomCoendLiftCowedge]
    exact Multicofork.π_comp_hom
      (copowerCoend G pt)
      (ihomCoendLiftCowedge G pt Y s)
      ((copowerCoendIsInitial G pt).to
        (ihomCoendLiftCowedge G pt Y s)) A
  rw [coendFac]
  simp only [copowerIhomToPowerIhom]
  rw [← curry_natural_left]
  rw [← curry_uncurry (Multifork.ι s A)]
  congr 1
  apply HasPowers.ext; intro t
  simp only [Category.assoc, HasPowers.fac]
  dsimp only [copowerProfInner, HomToProf,
    Functor.curry_obj_obj_obj, Functor.comp_obj,
    CategoryTheory.Prod.fst_obj, yoneda_obj_obj]
  slice_lhs 1 2 => rw [whisker_exchange]
  simp only [Category.assoc]
  rw [← uncurry_natural_left, Category.comp_id,
    uncurry_curry]
  rw [BraidedCategory.braiding_naturality_left_assoc]
  rw [← uncurry_natural_left]
  simp only [ihomCoendLiftCopowerMap, HasCopowers.fac]
  simp only [ihomCoendLiftComponent, uncurry_curry]
  rw [BraidedCategory.braiding_naturality_left_assoc]
  rw [SymmetricCategory.braiding_swap_eq_inv_braiding,
    Iso.inv_hom_id_assoc, ← Category.assoc]
  rfl

omit [SymmetricCategory C] [HasAllCopowerProfCoends G]
  in
/-- The copower injection whisker composed with
uncurry equals uncurry of the composition with
`copowerIhomToPowerIhom` followed by the power
projection. -/
private theorem uncurry_copowerIhomToPowerIhom_proj
    {S : Type v} {X Z Y' : C} (t : S)
    (f : Z ⟶
      (ihom (HasCopowers.copower S X)).obj Y') :
    (HasCopowers.inj S X t) ▷ Z ≫ uncurry f =
    uncurry
      (f ≫ copowerIhomToPowerIhom S X Y') ≫
      HasPowers.proj Y' S t := by
  rw [comp_copowerIhomToPowerIhom, uncurry_curry,
    HasPowers.fac]

/-- Uniqueness: any morphism to the wedge apex
that commutes with all wedge projections equals the
lift produced by `ihomCoendWedgeLift`. -/
theorem ihomCoendWedgeLift_uniq
    (pt Y : C)
    (s : Wedge (ihomPowerProf G pt Y))
    (m : s.pt ⟶ (ihomCoendWedge G pt Y).pt)
    (hm : ∀ A : C,
      m ≫ (ihomCoendWedge G pt Y).ι A = s.ι A) :
    m = ihomCoendWedgeLift G pt Y s := by
  rw [← curry_uncurry m,
    ← curry_uncurry (ihomCoendWedgeLift G pt Y s)]
  simp only [ihomCoendWedgeLift, uncurry_curry]
  congr 1
  suffices h :
      curry ((β_ s.pt (CopowerGExtObj G pt)).hom ≫
        uncurry m) =
      ihomCoendLift G pt Y s by
    rw [SymmetricCategory.braiding_swap_eq_inv_braiding,
      ← h, uncurry_curry, Iso.inv_hom_id_assoc]
  have hK : Limits.IsColimit (copowerCoend G pt) :=
    (Cocone.isColimitEquivIsInitial _).symm
      (copowerCoendIsInitial G pt)
  apply Multicofork.IsColimit.hom_ext hK
  intro A
  have hmA := hm A
  simp only [ihomCoendWedge, Wedge.mk_ι,
    ihomCoendWedgeProj] at hmA
  have coendFac :
      Multicofork.π (copowerCoend G pt) A ≫
        ihomCoendLift G pt Y s =
      ihomCoendLiftCopowerMap G pt Y s A := by
    simp only [ihomCoendLift, ihomCoendLiftCowedge]
    exact Multicofork.π_comp_hom
      (copowerCoend G pt)
      (ihomCoendLiftCowedge G pt Y s)
      ((copowerCoendIsInitial G pt).to
        (ihomCoendLiftCowedge G pt Y s)) A
  rw [coendFac]
  apply HasCopowers.ext; intro t
  rw [ihomCoendLiftCopowerMap, HasCopowers.fac]
  simp only [ihomCoendLiftComponent]
  rw [← Category.assoc]
  rw [← curry_natural_left]
  congr 1
  simp only [CopowerGExtObj] at *
  rw [BraidedCategory.braiding_naturality_right_assoc]
  rw [comp_whiskerRight]
  simp only [Category.assoc]
  rw [← uncurry_pre_app]
  rw [uncurry_copowerIhomToPowerIhom_proj]
  simp only [Category.assoc]
  simp only [CopowerGExtInj] at hmA
  dsimp only [HomToProf,
    Functor.curry_obj_obj_obj, Functor.comp_obj,
    CategoryTheory.Prod.fst_obj, yoneda_obj_obj]
    at hmA ⊢
  rw [hmA, uncurry_eq]
  simp only [Category.assoc]
  rw [← BraidedCategory.braiding_naturality_left_assoc]

/-- The wedge `ihomCoendWedge G pt Y` is a limit
wedge (terminal wedge) for `ihomPowerProf G pt Y`,
assembled from the lift, factorization, and
uniqueness. -/
def ihomCoendWedge_isLimit (pt Y : C) :
    IsLimit (ihomCoendWedge G pt Y) :=
  Multifork.IsLimit.mk _
    (ihomCoendWedgeLift G pt Y)
    (ihomCoendWedgeLift_fac G pt Y)
    (fun s m hm =>
      ihomCoendWedgeLift_uniq G pt Y s m hm)

/-- Packages `ihomCoendWedge` and its limit proof
into a `HasTerminalWedge`. -/
def ihomCoendHasTerminalWedge (pt Y : C) :
    HasTerminalWedge (ihomPowerProf G pt Y) :=
  ⟨ihomCoendWedge G pt Y,
    ihomCoendWedge_isLimit G pt Y⟩

omit [SymmetricCategory C] in
/-- `(ihom X).map f` commutes with the coend wedge
projections, expressing naturality of
`ihomCoendWedgeProj` in `Y`. -/
private theorem ihom_map_comp_ihomCoendWedgeProj
    (pt : C) {Y₁ Y₂ : C} (f : Y₁ ⟶ Y₂)
    (A : C) :
    (ihom (CopowerGExtObj G pt)).map f ≫
      ihomCoendWedgeProj G pt Y₂ A =
    ihomCoendWedgeProj G pt Y₁ A ≫
      ((ihomPowerProfMapY G pt f).app
        (Opposite.op A)).app A := by
  simp only [ihomCoendWedgeProj]
  rw [← Category.assoc
    ((ihom (CopowerGExtObj G pt)).map f),
    (MonoidalClosed.pre
      (CopowerGExtInj G pt A)).naturality f,
    Category.assoc]
  simp only [copowerProfInner]
  dsimp only [HomToProf,
    Functor.curry_obj_obj_obj,
    Functor.comp_obj,
    CategoryTheory.Prod.fst_obj,
    yoneda_obj_obj]
  rw [copowerIhomToPowerIhom_naturalY]
  simp only [Category.assoc]
  congr 2

omit [SymmetricCategory C] in
/-- When the terminal wedges for `ihomPowerProf`
come from the coend construction, the internal-end
functor is naturally isomorphic to `ihom` applied
to the coend carrier. -/
def ihomCoendPowerEndNatIso (pt : C) :
    ihom (CopowerGExtObj G pt) ≅
      ihomPowerEndFunctor G pt
        (fun Y =>
          ihomCoendHasTerminalWedge G pt Y) :=
  NatIso.ofComponents
    (fun _ => Iso.refl _)
    (fun {Y₁ _} f => by
      simp only [Iso.refl_hom,
        Category.comp_id, Category.id_comp,
        ihomPowerEndFunctor]
      apply
        (ihomCoendHasTerminalWedge G pt _).hom_ext
      intro A
      rw [HasTerminalWedge.map_ι]
      exact
        ihom_map_comp_ihomCoendWedgeProj G pt f A)

end IhomPowerEndGExtBraided

/-!
## Type-Valued Impredicative GExt

For a Type-valued profunctor `G : Cᵒᵖ ⥤ C ⥤ Type v`
over an arbitrary category `C`, we define the Mendler
extension profunctor `mendlerTypeProf pt G` sending
`(op A, B) ↦ (A ⟶ pt) × G(A, B)`. Its coend
`typeCoend (mendlerTypeProf pt G)` is the existential
Mendler extension, and by
`typeCoend.endImpredicative` it is unconditionally
equivalent to the universal-only Church encoding
`endLimitFunctor (mendlerTypeProf pt G) ⟶ 𝟭 _`.
-/

section TypeValuedGExt

variable
  {C : Type u} [Category.{v} C]

/-- The Type-valued Mendler extension profunctor:
sends `(op A, B)` to `(A ⟶ pt) × (G.obj (op A)).obj B`.

This is the Type-valued analogue of
`copowerProf (HomToProf pt) G`, which sends
`(op A, B)` to the C-valued copower
`(A ⟶ pt) · G(A, B)`. -/
def mendlerTypeProf
    (pt : C) (G : Cᵒᵖ ⥤ C ⥤ Type v) :
    Cᵒᵖ ⥤ C ⥤ Type v where
  obj A := {
    obj := fun B =>
      (A.unop ⟶ pt) × (G.obj A).obj B
    map := fun g ⟨s, x⟩ =>
      ⟨s, (G.obj A).map g x⟩
    map_id := fun B => by
      funext ⟨s, x⟩
      exact Prod.ext rfl
        (FunctorToTypes.map_id_apply
          (G.obj A) x)
    map_comp := fun f g => by
      funext ⟨s, x⟩
      exact Prod.ext rfl
        (FunctorToTypes.map_comp_apply
          (G.obj A) f g x)
  }
  map {A₁ A₂} f := {
    app := fun B ⟨s, x⟩ =>
      ⟨f.unop ≫ s, (G.map f).app B x⟩
    naturality := fun {B₁ B₂} g => by
      funext ⟨s, x⟩
      exact Prod.ext rfl
        (congr_fun ((G.map f).naturality g) x)
  }
  map_id A := by
    ext B ⟨s, x⟩
    · exact Category.id_comp s
    · exact congr_fun (congr_arg DFunLike.coe
        (congr_fun (congr_arg NatTrans.app
          (G.map_id A)) B)) x
  map_comp {A₁ A₂ A₃} f g := by
    ext B ⟨s, x⟩
    · change (f ≫ g).unop ≫ s =
        g.unop ≫ (f.unop ≫ s)
      rw [unop_comp, Category.assoc]
    · exact congr_fun (congr_arg DFunLike.coe
        (congr_fun (congr_arg NatTrans.app
          (G.map_comp f g)) B)) x

/-- The natural transformation
`mendlerTypeProf pt₁ G ⟶ mendlerTypeProf pt₂ G`
induced by `h : pt₁ ⟶ pt₂`, sending `(s, x)` to
`(s ≫ h, x)` (postcomposition on the hom
component). -/
def mendlerTypeProf.mapPt
    (G : Cᵒᵖ ⥤ C ⥤ Type v)
    {pt₁ pt₂ : C} (h : pt₁ ⟶ pt₂) :
    mendlerTypeProf pt₁ G ⟶
      mendlerTypeProf pt₂ G where
  app A := {
    app := fun B ⟨s, x⟩ => ⟨s ≫ h, x⟩
    naturality := fun {B₁ B₂} g => by
      funext ⟨s, x⟩; rfl
  }
  naturality {A₁ A₂} f := by
    ext B ⟨s, x⟩
    simp only [NatTrans.comp_app,
      types_comp_apply, mendlerTypeProf]
    exact Prod.ext
      (Category.assoc _ _ _) rfl

/-- The Type-valued Mendler extension: the coend
of `mendlerTypeProf pt G` in `Type`.
-/
abbrev mendlerExtType
    (pt : C) (G : Cᵒᵖ ⥤ C ⥤ Type v) :
    Type (max u v) :=
  typeCoend (mendlerTypeProf pt G)

/-- The universal-only Church-encoded Mendler
extension: natural transformations from
`endLimitFunctor (mendlerTypeProf pt G)` to the
identity functor.

When `C = Type v`, this is the impredicative
encoding `∀ D, (∀ A, (A → pt) → G(A,A) → D) → D`.
-/
abbrev mendlerUnivType
    (pt : C) (G : Cᵒᵖ ⥤ C ⥤ Type v) :
    Type (max (u + 1) (v + 1)) :=
  endLimitFunctor (mendlerTypeProf pt G) ⟶
    𝟭 (Type (max u v))

/-- The unconditional equivalence between the
Church-encoded Mendler extension and the coend.
This is `typeCoend.endImpredicative` applied to
`mendlerTypeProf pt G`. -/
def mendlerUnivTypeEquiv
    (pt : C) (G : Cᵒᵖ ⥤ C ⥤ Type v) :
    mendlerUnivType pt G ≃
      mendlerExtType pt G :=
  typeCoend.endImpredicative
    (mendlerTypeProf pt G)

/-- The functorial action on the coend: given
`h : pt₁ ⟶ pt₂`, maps `mendlerExtType pt₁ G` to
`mendlerExtType pt₂ G` by postcomposing the hom
component `(A ⟶ pt₁)` with `h`.
-/
def mendlerExtType.map
    (G : Cᵒᵖ ⥤ C ⥤ Type v)
    {pt₁ pt₂ : C} (h : pt₁ ⟶ pt₂) :
    mendlerExtType pt₁ G →
      mendlerExtType pt₂ G :=
  typeCoend.map C
    (mendlerTypeProf.mapPt G h)

/-- The functorial action on the Church encoding:
given `h : pt₁ ⟶ pt₂`, maps
`mendlerUnivType pt₁ G` to
`mendlerUnivType pt₂ G`.

Obtained by conjugating `mendlerExtType.map G h`
with `mendlerUnivTypeEquiv`.
-/
def mendlerUnivType.map
    (G : Cᵒᵖ ⥤ C ⥤ Type v)
    {pt₁ pt₂ : C} (h : pt₁ ⟶ pt₂) :
    mendlerUnivType pt₁ G →
      mendlerUnivType pt₂ G :=
  fun γ =>
    (mendlerUnivTypeEquiv pt₂ G).symm
      (mendlerExtType.map G h
        (mendlerUnivTypeEquiv pt₁ G γ))

/-- The Mendler algebra characterization: functions
from `mendlerExtType pt G` to a target type `X`
correspond to compatible families
`∀ A, (A ⟶ pt) × G(A,A) → X`.

This is `typeCoend.endEquiv` applied to
`mendlerTypeProf pt G`.

When `X = pt` (with `pt : Type v`), the RHS is
the Mendler algebra structure
`∀ A (γ : A ⟶ pt), G(A,A) → pt` and the LHS is
the conventional F-algebra map
`mendlerExtType pt G → pt`. -/
def mendlerAlgTypeEquiv
    (pt : C) (G : Cᵒᵖ ⥤ C ⥤ Type v)
    (X : Type w) :
    (mendlerExtType pt G → X) ≃
      typeEnd
        (sliceProfunctorPoly
          (mendlerTypeProf pt G) X) :=
  typeCoend.endEquiv
    (mendlerTypeProf pt G) X

theorem mendlerTypeProf.mapPt_id
    (G : Cᵒᵖ ⥤ C ⥤ Type v) (pt : C) :
    mendlerTypeProf.mapPt G (𝟙 pt) =
      𝟙 (mendlerTypeProf pt G) := by
  ext A B ⟨s, x⟩
  all_goals simp [mapPt, Category.comp_id]

theorem mendlerTypeProf.mapPt_comp
    (G : Cᵒᵖ ⥤ C ⥤ Type v)
    {pt₁ pt₂ pt₃ : C}
    (h₁ : pt₁ ⟶ pt₂) (h₂ : pt₂ ⟶ pt₃) :
    mendlerTypeProf.mapPt G (h₁ ≫ h₂) =
      mendlerTypeProf.mapPt G h₁ ≫
        mendlerTypeProf.mapPt G h₂ := by
  ext A B ⟨s, x⟩
  all_goals simp [mendlerTypeProf, mapPt,
    Category.assoc]

theorem mendlerExtType.map_id
    (G : Cᵒᵖ ⥤ C ⥤ Type v) (pt : C) :
    mendlerExtType.map G (𝟙 pt) = id := by
  unfold mendlerExtType.map
  rw [mendlerTypeProf.mapPt_id]
  exact (typeCoendFunctor C).map_id
    (mendlerTypeProf pt G)

theorem mendlerExtType.map_comp
    (G : Cᵒᵖ ⥤ C ⥤ Type v)
    {pt₁ pt₂ pt₃ : C}
    (h₁ : pt₁ ⟶ pt₂) (h₂ : pt₂ ⟶ pt₃) :
    mendlerExtType.map G (h₁ ≫ h₂) =
      mendlerExtType.map G h₂ ∘
        mendlerExtType.map G h₁ := by
  unfold mendlerExtType.map
  rw [mendlerTypeProf.mapPt_comp]
  exact (typeCoendFunctor C).map_comp
    (mendlerTypeProf.mapPt G h₁)
    (mendlerTypeProf.mapPt G h₂)

/-- Algebra characterization for the
Church-encoded Mendler extension: functions from
`mendlerUnivType pt G` to a target type `X`
correspond to elements of
`typeEnd
  (sliceProfunctorPoly
    (mendlerTypeProf pt G) X)`,
which assigns to each `A : C` the function type
`(A ⟶ pt) × G(A,A) → X` (with dinaturality).

Obtained by composing `Equiv.arrowCongr` of the
Church-encoding equivalence `mendlerUnivTypeEquiv`
with the coend algebra characterization
`mendlerAlgTypeEquiv`.
-/
def mendlerUnivAlgTypeEquiv
    (pt : C) (G : Cᵒᵖ ⥤ C ⥤ Type v)
    (X : Type w) :
    (mendlerUnivType pt G → X) ≃
      typeEnd
        (sliceProfunctorPoly
          (mendlerTypeProf pt G) X) :=
  (Equiv.arrowCongr
    (mendlerUnivTypeEquiv pt G)
    (Equiv.refl X)).trans
    (mendlerAlgTypeEquiv pt G X)

/-- The Mendler profunctor as a functor from `C`
to the profunctor category `Cᵒᵖ ⥤ C ⥤ Type v`,
mapping `pt ↦ mendlerTypeProf pt G` and
`h ↦ mendlerTypeProf.mapPt G h`. -/
def mendlerTypeProfFunctor
    (G : Cᵒᵖ ⥤ C ⥤ Type v) :
    C ⥤ (Cᵒᵖ ⥤ C ⥤ Type v) where
  obj pt := mendlerTypeProf pt G
  map h := mendlerTypeProf.mapPt G h
  map_id pt := mendlerTypeProf.mapPt_id G pt
  map_comp h₁ h₂ :=
    mendlerTypeProf.mapPt_comp G h₁ h₂

/-- The Mendler extension as a functor
`C ⥤ Type (max u v)`, defined as
`mendlerTypeProfFunctor G ⋙ typeCoendFunctor C`.
At each object `pt`, the value is
`typeCoend (mendlerTypeProf pt G)`, i.e.,
`mendlerExtType pt G`. -/
def mendlerExtTypeFunctor
    (G : Cᵒᵖ ⥤ C ⥤ Type v) :
    C ⥤ Type (max u v) :=
  mendlerTypeProfFunctor G ⋙ typeCoendFunctor C

end TypeValuedGExt

section TypeValuedMendlerAlgConnection

/-- Uncurrying a Mendler algebra family to a
type end family, for `C = Type v`.

Converts the curried family
`(I : Type v) → (I → pt) → (G(I,I) → pt)`
to the uncurried family
`(I : Type v) → ((I → pt) × G(I,I)) → pt`. -/
def mendlerFamilyUncurry
    (pt : Type v)
    (G : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v)
    (family :
      ParanatSig (HomToProf pt) (G ⇓ pt)) :
    (I : Type v) →
      diagApp
        (sliceProfunctorPoly
          (mendlerTypeProf pt G) pt) I :=
  fun I ⟨γ, g⟩ => family I γ g

/-- Currying a type end family to a Mendler algebra
family, for `C = Type v`.

Converts the uncurried family
`(I : Type v) → ((I → pt) × G(I,I)) → pt`
to the curried family
`(I : Type v) → (I → pt) → (G(I,I) → pt)`. -/
def mendlerFamilyCurry
    (pt : Type v)
    (G : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v)
    (family :
      (I : Type v) →
        diagApp
          (sliceProfunctorPoly
            (mendlerTypeProf pt G) pt) I) :
    ParanatSig (HomToProf pt) (G ⇓ pt) :=
  fun I γ g => family I ⟨γ, g⟩

/-- The uncurried family satisfies the wedge
condition when the original family is dinatural.

The dinaturality condition for the Mendler
algebra family at `(i, j, f, s)`:
  `family j s (G(j,j).map f g) =
   family i (f ≫ s) (G.map f.op .app i g)`
is exactly the wedge condition for the uncurried
family at `(i, j, f)` applied to `(s, g)`. -/
theorem mendlerFamilyUncurry_wedge
    (pt : Type v)
    (G : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v)
    (family :
      ParanatSig (HomToProf pt) (G ⇓ pt))
    (hd :
      IsDinatural (HomToProf pt) (G ⇓ pt)
        family)
    {i j : Type v} (f : i ⟶ j) :
    ((sliceProfunctorPoly
        (mendlerTypeProf pt G) pt).obj
      (Opposite.op i)).map f
      (mendlerFamilyUncurry pt G family i) =
    ((sliceProfunctorPoly
        (mendlerTypeProf pt G) pt).map
      f.op).app j
      (mendlerFamilyUncurry pt G family j) := by
  funext ⟨s, g⟩
  exact (congrFun (hd i j f s) g).symm

/-- The curried family is dinatural when
the uncurried family satisfies the wedge
condition. Inverse of
`mendlerFamilyUncurry_wedge`. -/
theorem mendlerFamilyCurry_isDinatural
    (pt : Type v)
    (G : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v)
    (family :
      (I : Type v) →
        diagApp
          (sliceProfunctorPoly
            (mendlerTypeProf pt G) pt) I)
    (hw : ∀ {i j : Type v} (f : i ⟶ j),
      ((sliceProfunctorPoly
          (mendlerTypeProf pt G) pt).obj
        (Opposite.op i)).map f (family i) =
      ((sliceProfunctorPoly
          (mendlerTypeProf pt G) pt).map
        f.op).app j (family j)) :
    IsDinatural (HomToProf pt) (G ⇓ pt)
      (mendlerFamilyCurry pt G family) := by
  intro i j f s
  exact funext fun g =>
    (congrFun (hw f) ⟨s, g⟩).symm

/-- Equivalence between Mendler algebras over
`pt` and the type end of the uncurried Mendler
profunctor, for `C = Type v`.

The currying isomorphism
`(A → B → C) ≃ (A × B → C)` applied
componentwise converts between the curried
Mendler algebra family
`∀ I, (I → pt) → (G(I,I) → pt)`
and the end of the uncurried profunctor
`∀ I, ((I → pt) × G(I,I)) → pt`,
with the dinaturality condition matching
the wedge condition. -/
def mendlerAlgOverTypeEndEquiv
    (pt : Type v)
    (G : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v) :
    MendlerAlgebraOver G pt ≃
      typeEnd
        (sliceProfunctorPoly
          (mendlerTypeProf pt G) pt) where
  toFun m :=
    ⟨mendlerFamilyUncurry pt G m.family,
     fun f =>
       mendlerFamilyUncurry_wedge
         pt G m.family m.isDinatural f⟩
  invFun e :=
    MendlerAlgebraOver.mk' pt
      (mendlerFamilyCurry pt G e.val)
      (mendlerFamilyCurry_isDinatural
        pt G e.val
        (fun f => e.property f))
  left_inv _ := rfl
  right_inv _ := rfl

/-- Equivalence between Mendler algebras over
`pt` and conventional algebra maps
`mendlerExtType pt G → pt`, for `C = Type v`.

Composes `mendlerAlgOverTypeEndEquiv` (the
currying equivalence) with
`mendlerAlgTypeEquiv` (the coend-end
algebra characterization). -/
def mendlerAlgOverAlgMapEquiv
    (pt : Type v)
    (G : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v) :
    MendlerAlgebraOver G pt ≃
      (mendlerExtType pt G → pt) :=
  (mendlerAlgOverTypeEndEquiv pt G).trans
    (mendlerAlgTypeEquiv pt G pt).symm

/-- The Mendler algebra hom condition implies
the algebra-map commutativity condition.

For `C = Type v`, the Mendler hom condition
`∀ A γ, m₁.family A γ ≫ h =
  m₂.family A (γ ≫ h)`
implies (by extensionality on the coend
quotient)
`h ∘ φ₁ = φ₂ ∘ mendlerExtType.map G h`
where `φ_i = mendlerAlgOverAlgMapEquiv`. -/
theorem mendlerHom_to_algMapComm
    (G : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v)
    (m₁ m₂ : MendlerAlgebra G)
    (h : m₁.pt ⟶ m₂.pt)
    (hc : ∀ (A : Type v) (γ : A ⟶ m₁.pt),
      m₁.family A γ ≫ h =
        m₂.family A (γ ≫ h)) :
    h ∘ (mendlerAlgOverAlgMapEquiv m₁.pt G
        m₁.toMendlerAlgebraOver) =
      (mendlerAlgOverAlgMapEquiv m₂.pt G
        m₂.toMendlerAlgebraOver) ∘
      mendlerExtType.map G h := by
  funext x
  exact Quot.inductionOn x
    fun ⟨j, γ, g⟩ => congrFun (hc j γ) g

/-- The algebra-map commutativity condition
implies the Mendler algebra hom condition. -/
theorem algMapComm_to_mendlerHom
    (G : (Type v)ᵒᵖ ⥤ Type v ⥤ Type v)
    (m₁ m₂ : MendlerAlgebra G)
    (h : m₁.pt ⟶ m₂.pt)
    (hc : h ∘ (mendlerAlgOverAlgMapEquiv m₁.pt G
        m₁.toMendlerAlgebraOver) =
      (mendlerAlgOverAlgMapEquiv m₂.pt G
        m₂.toMendlerAlgebraOver) ∘
      mendlerExtType.map G h) :
    ∀ (A : Type v) (γ : A ⟶ m₁.pt),
      m₁.family A γ ≫ h =
        m₂.family A (γ ≫ h) := by
  intro A γ
  funext g
  exact congrFun hc
    (Quot.mk _ ⟨A, γ, g⟩)

end TypeValuedMendlerAlgConnection

end GebLean
