import GebLean.RestrictedCoendAsColimit
import GebLean.Utilities.EndsAndCoends

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

universe v w

/-!
## Coend-End Duality for Initial Cowedges

Given a coend cowedge `c` (initial in `Cowedge P`) for a
`D`-valued profunctor, the hom-set `c.pt ⟶ Y` is
isomorphic to the explicit end `typeEnd (P ⇓ Y)`.
-/

section CoendEndDuality

variable
  {C : Type v} [Category.{v} C]
  {D : Type w} [Category.{v} D]

/-- Coend-end duality for initial cowedges:
given a coend cowedge `c` (initial in `Cowedge P`),
`(c.pt ⟶ Y) ≃ typeEnd (P ⇓ Y)`.

Combines `ordinaryHomIsoEndApex` (relating the
coend apex hom to any terminal wedge apex) with
`typeEndWedge_isTerminal` (making `typeEnd` the apex
of a terminal wedge). -/
def cowedgeHomEndEquiv
    (P : Cᵒᵖ ⥤ C ⥤ D)
    {c : Cowedge (J := C) (C := D) P}
    (hc : IsInitial c) (Y : D) :
    (c.pt ⟶ Y) ≃ typeEnd (P ⇓ Y) :=
  let iso := ordinaryHomIsoEndApex P hc Y
    (typeEndWedge_isTerminal (P ⇓ Y))
  ⟨iso.hom, iso.inv,
   fun x => congr_fun iso.hom_inv_id x,
   fun x => congr_fun iso.inv_hom_id x⟩

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
  {C : Type v} [Category.{v} C] [HasCopowers C]
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
  {C : Type v} [Category.{v} C]
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
  {C : Type v} [Category.{v} C]
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
## Final Characterization

Composing all three steps gives the end-power
characterization of `G^e`:
`Hom(CopowerGExtObj G pt, Y) ≃
  typeEnd (powerSliceProf G pt Y)`.

On the diagonal at `A`, `powerSliceProf G pt Y` gives
`G(A, A) ⟶ Y^(A ⟶ pt)`, so the end is over all `A`
of morphisms `G(A, A) ⟶ Y^(A ⟶ pt)`.
-/

section FinalEquiv

variable
  {C : Type v} [Category.{v} C]
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

end FinalEquiv

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
  {C : Type v} [Category.{v} C]
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
  {C : Type v} [Category.{v} C]
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
  {C : Type v} [Category.{v} C]
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
  {C : Type v} [Category.{v} C]
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
  {C : Type v} [Category.{v} C]
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

end GebLean
