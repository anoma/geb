import GebLean.Utilities.Skeleton
import GebLean.Utilities.Presheaf
import GebLean.Utilities.DoubleCategory
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes

/-!
# Internal Relations in PSh(C)

The double category of internal relations in the presheaf
category `PSh(C) = Cᵒᵖ ⥤ Type w`.

## Presheaf representation of relations

The presheaf `P × Q` (pointwise product) for
`P Q : Cᵒᵖ ⥤ Type w` represents pairs of generalized
elements of `P` and `Q`.

A proof-relevant relation from `P` to `Q` is a morphism
into `P × Q` in `PSh(C)`, i.e., an object of the over
category `Over (P × Q)`.

## Double category structure

- Objects: presheaves `P : Cᵒᵖ ⥤ Type w`
- Horizontal morphisms: natural transformations
- Vertical morphisms: `PshRel P Q` (isomorphism classes
  of objects over `P × Q`)
- Squares: `pshRelRelated` (`Prop`-valued)
-/

namespace GebLean

open CategoryTheory Limits

universe u v w

variable {C : Type u} [Category.{v} C]

section PshRelations

/-- The product presheaf `P × Q`, constructed as
`FunctorToTypes.prod P Q`. -/
abbrev pshProdPresheaf
    (P Q : Cᵒᵖ ⥤ Type w) : Cᵒᵖ ⥤ Type w :=
  FunctorToTypes.prod P Q

/-- A proof-relevant relation from `P` to `Q` in
`PSh(C)`: an object of the over category
`Over (pshProdPresheaf P Q)`. -/
abbrev PshProdOver
    (P Q : Cᵒᵖ ⥤ Type w) :=
  Over (pshProdPresheaf P Q)

/-- First projection from the product presheaf
`P × Q` to `P`. -/
abbrev pshProdFst
    (P Q : Cᵒᵖ ⥤ Type w) :
    pshProdPresheaf P Q ⟶ P :=
  @FunctorToTypes.prod.fst _ _ P Q

/-- Second projection from the product presheaf
`P × Q` to `Q`. -/
abbrev pshProdSnd
    (P Q : Cᵒᵖ ⥤ Type w) :
    pshProdPresheaf P Q ⟶ Q :=
  @FunctorToTypes.prod.snd _ _ P Q

/-- Pairing of morphisms into `P` and `Q` to a
morphism into the product presheaf `P × Q`. -/
abbrev pshProdLift
    {R P Q : Cᵒᵖ ⥤ Type w}
    (f : R ⟶ P) (g : R ⟶ Q) :
    R ⟶ pshProdPresheaf P Q :=
  FunctorToTypes.prod.lift f g

/-- Two morphisms into `pshProdPresheaf P Q` are
equal iff their compositions with the two projections
agree. -/
theorem pshProdPresheaf_hom_ext
    {R P Q : Cᵒᵖ ⥤ Type w}
    {h₁ h₂ : R ⟶ pshProdPresheaf P Q}
    (hfst : h₁ ≫ pshProdFst P Q =
      h₂ ≫ pshProdFst P Q)
    (hsnd : h₁ ≫ pshProdSnd P Q =
      h₂ ≫ pshProdSnd P Q) :
    h₁ = h₂ := by
  ext T x
  · exact congr_fun
      (NatTrans.congr_app hfst T) x
  · exact congr_fun
      (NatTrans.congr_app hsnd T) x

@[simp]
theorem pshProdLift_fst_snd
    {R P Q : Cᵒᵖ ⥤ Type w}
    (h : R ⟶ pshProdPresheaf P Q) :
    pshProdLift
      (h ≫ pshProdFst P Q)
      (h ≫ pshProdSnd P Q) = h :=
  pshProdPresheaf_hom_ext
    (by simp [pshProdLift])
    (by simp [pshProdLift])

/-- The identity relation on `P` in the over category,
given by the diagonal `P → P × P`. -/
def pshProdOverId
    (P : Cᵒᵖ ⥤ Type w) : PshProdOver P P :=
  Over.mk (pshProdLift (𝟙 P) (𝟙 P))

@[simp]
theorem pshProdOverId_fst
    (P : Cᵒᵖ ⥤ Type w) :
    (pshProdOverId P).hom ≫ pshProdFst P P =
    𝟙 P :=
  rfl

@[simp]
theorem pshProdOverId_snd
    (P : Cᵒᵖ ⥤ Type w) :
    (pshProdOverId P).hom ≫ pshProdSnd P P =
    𝟙 P :=
  rfl

/-- The graph of a natural transformation `α : P ⟶ Q`
as a proof-relevant relation. The underlying presheaf
is `P`, with first projection the identity and second
projection `α`. -/
def pshProdOverGraph
    {P Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    PshProdOver P Q :=
  Over.mk (pshProdLift (𝟙 P) α)

@[simp]
theorem pshProdOverGraph_fst
    {P Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    (pshProdOverGraph α).hom ≫
      pshProdFst P Q =
    𝟙 P :=
  rfl

@[simp]
theorem pshProdOverGraph_snd
    {P Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    (pshProdOverGraph α).hom ≫
      pshProdSnd P Q = α :=
  rfl

theorem pshProdOverGraph_snd_assoc
    {P Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q)
    {R : Cᵒᵖ ⥤ Type w}
    (k : Q ⟶ R) :
    (pshProdOverGraph α).hom ≫
      pshProdSnd P Q ≫ k =
    α ≫ k := by
  rw [← Category.assoc, pshProdOverGraph_snd]

theorem pshProdOverGraph_fst_assoc
    {P Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q)
    {R : Cᵒᵖ ⥤ Type w}
    (k : P ⟶ R) :
    (pshProdOverGraph α).hom ≫
      pshProdFst P Q ≫ k =
    k := by
  rw [← Category.assoc, pshProdOverGraph_fst]
  exact Category.id_comp k

theorem pshProdOverGraph_id
    (P : Cᵒᵖ ⥤ Type w) :
    pshProdOverGraph (𝟙 P) =
      pshProdOverId P := by
  simp [pshProdOverGraph, pshProdOverId]

/-- Composition of proof-relevant relations in the
over category.

Given `R ⟶ P × Q` and `S ⟶ Q × W`, their composite
is obtained by pulling back `R` and `S` over `Q`
(matching the second component of `R` with the first
component of `S`), then projecting the first component
from `R` and the second from `S` into `P × W`. -/
def pshProdOverComp
    {P Q W : Cᵒᵖ ⥤ Type w}
    (R : PshProdOver P Q)
    (S : PshProdOver Q W) :
    PshProdOver P W :=
  Over.mk
    (pshProdLift
      (presheafPullbackFst
          (R.hom ≫ pshProdSnd P Q)
          (S.hom ≫ pshProdFst Q W) ≫
        R.hom ≫ pshProdFst P Q)
      (presheafPullbackSnd
          (R.hom ≫ pshProdSnd P Q)
          (S.hom ≫ pshProdFst Q W) ≫
        S.hom ≫ pshProdSnd Q W))

/-- A relation from `P` to `Q` up to isomorphism:
an isomorphism class in the over category
`Over (pshProdPresheaf P Q)`. -/
abbrev PshRel
    (P Q : Cᵒᵖ ⥤ Type w) :=
  Skeleton (PshProdOver P Q)

/-- The identity relation on `P`, up to
isomorphism. -/
def pshRelId
    (P : Cᵒᵖ ⥤ Type w) : PshRel P P :=
  toSkeleton _ (pshProdOverId P)

/-- `pshProdOverComp` respects isomorphisms: given
isomorphisms `R₁ ≅ R₂` and `S₁ ≅ S₂` in the over
categories, their compositions are isomorphic. -/
def pshProdOverComp_iso
    {P Q W : Cᵒᵖ ⥤ Type w}
    {R₁ R₂ : PshProdOver P Q}
    {S₁ S₂ : PshProdOver Q W}
    (αR : R₁ ≅ R₂) (αS : S₁ ≅ S₂) :
    pshProdOverComp R₁ S₁ ≅
      pshProdOverComp R₂ S₂ := by
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
  simp only [pshProdOverComp, Over.mk_hom]
  apply pshProdPresheaf_hom_ext
  · open Limits in
    simp only [Category.assoc,
      FunctorToTypes.prod.lift_fst]
    rw [presheafPullbackIsoOfIso_hom_fst_assoc]
    simp only [Functor.mapIso_hom, Over.forget_map,
      ← Category.assoc, hR]
  · open Limits in
    simp only [Category.assoc,
      FunctorToTypes.prod.lift_snd]
    rw [presheafPullbackIsoOfIso_hom_snd_assoc]
    simp only [Functor.mapIso_hom, Over.forget_map,
      ← Category.assoc, hS]

/-- Left identity for `pshProdOverComp`: composing
with the identity relation on `P` yields an
isomorphic relation. -/
def pshProdOverComp_id_left
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshProdOver P Q) :
    pshProdOverComp (pshProdOverId P) R ≅ R :=
  Over.isoMk
    (presheafPullbackIdLeftIso
      (R.hom ≫ pshProdFst P Q))
    (by
      simp only [pshProdOverComp, Over.mk_hom]
      apply pshProdPresheaf_hom_ext
      · simp only [Category.assoc,
          presheafPullbackIdLeftIso]
        have := presheafPullbackCondition
          (𝟙 P) (R.hom ≫ pshProdFst P Q)
        simp only [Category.comp_id] at this
        exact this.symm
      · rfl)

/-- Right identity for `pshProdOverComp`: composing
with the identity relation on `Q` yields an
isomorphic relation. -/
def pshProdOverComp_id_right
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshProdOver P Q) :
    pshProdOverComp R (pshProdOverId Q) ≅ R :=
  Over.isoMk
    (presheafPullbackIdRightIso
      (R.hom ≫ pshProdSnd P Q))
    (by
      simp only [pshProdOverComp, Over.mk_hom]
      apply pshProdPresheaf_hom_ext
      · rfl
      · simp only [Category.assoc,
          presheafPullbackIdRightIso]
        exact presheafPullbackCondition _ _)

/-- Associativity for `pshProdOverComp`:
`(R ; S) ; T ≅ R ; (S ; T)`. -/
def pshProdOverComp_assoc
    {P Q W X : Cᵒᵖ ⥤ Type w}
    (R : PshProdOver P Q)
    (S : PshProdOver Q W)
    (T : PshProdOver W X) :
    pshProdOverComp
      (pshProdOverComp R S) T ≅
    pshProdOverComp
      R (pshProdOverComp S T) :=
  Over.isoMk
    (presheafPullbackAssocIso
      (R.hom ≫ pshProdSnd P Q)
      (S.hom ≫ pshProdFst Q W)
      (S.hom ≫ pshProdSnd Q W)
      (T.hom ≫ pshProdFst W X))
    (by
      simp only [pshProdOverComp, Over.mk_hom]
      apply pshProdPresheaf_hom_ext <;> rfl)

/-- The composite of two graph relations
`graph(α) ; graph(β)` is isomorphic to
`graph(α ≫ β)`. -/
def pshProdOverGraph_comp
    {P Q W : Cᵒᵖ ⥤ Type w}
    (α : P ⟶ Q) (β : Q ⟶ W) :
    pshProdOverComp
      (pshProdOverGraph α)
      (pshProdOverGraph β) ≅
    pshProdOverGraph (α ≫ β) :=
  Over.isoMk
    (presheafPullbackIdRightIso α)
    (by
      simp only [pshProdOverComp,
        pshProdOverGraph, Over.mk_hom]
      apply pshProdPresheaf_hom_ext
      · simp [presheafPullbackIdRightIso,
          presheafPullbackLift]
      · simp only [Category.assoc,
          FunctorToTypes.prod.lift_snd,
          FunctorToTypes.prod.lift_fst]
        have hpb := presheafPullbackCondition
          α (𝟙 Q)
        simp only [Category.comp_id] at hpb
        change
          (presheafPullbackFst α (𝟙 Q) ≫
            α) ≫ β = _
        rw [hpb])

/-- Composition of relations up to isomorphism:
applies `pshProdOverComp` via `Skeleton.lift₂`,
using `pshProdOverComp_iso` for
well-definedness. -/
def pshRelComp
    {P Q W : Cᵒᵖ ⥤ Type w} :
    PshRel P Q → PshRel Q W →
    PshRel P W :=
  Skeleton.lift₂
    (fun R S =>
      toSkeleton _ (pshProdOverComp R S))
    (fun _ _ _ _ ⟨αR⟩ ⟨αS⟩ =>
      toSkeleton_eq_iff.mpr
        ⟨pshProdOverComp_iso αR αS⟩)

theorem pshRelComp_id_left
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) :
    pshRelComp (pshRelId P) R = R := by
  induction R using Quotient.inductionOn with
  | h R' =>
    exact toSkeleton_eq_iff.mpr
      ⟨pshProdOverComp_id_left R'⟩

theorem pshRelComp_id_right
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) :
    pshRelComp R (pshRelId Q) = R := by
  induction R using Quotient.inductionOn with
  | h R' =>
    exact toSkeleton_eq_iff.mpr
      ⟨pshProdOverComp_id_right R'⟩

theorem pshRelComp_assoc
    {P Q W X : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q)
    (S : PshRel Q W)
    (T : PshRel W X) :
    pshRelComp (pshRelComp R S) T =
      pshRelComp R (pshRelComp S T) := by
  induction R using Quotient.inductionOn with
  | h R' =>
  induction S using Quotient.inductionOn with
  | h S' =>
  induction T using Quotient.inductionOn with
  | h T' =>
    exact toSkeleton_eq_iff.mpr
      ⟨pshProdOverComp_assoc R' S' T'⟩

/-- The graph of a natural transformation as a
`PshRel` (isomorphism class of `PshProdOver`). -/
def pshRelGraph
    {P Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    PshRel P Q :=
  toSkeleton _ (pshProdOverGraph α)

theorem pshRelGraph_eq_id
    (P : Cᵒᵖ ⥤ Type w) :
    pshRelGraph (𝟙 P) = pshRelId P := by
  simp [pshRelGraph, pshRelId,
    pshProdOverGraph_id]

theorem pshRelGraph_comp
    {P Q W : Cᵒᵖ ⥤ Type w}
    (α : P ⟶ Q) (β : Q ⟶ W) :
    pshRelComp (pshRelGraph α)
      (pshRelGraph β) =
      pshRelGraph (α ≫ β) :=
  toSkeleton_eq_iff.mpr
    ⟨pshProdOverGraph_comp α β⟩

end PshRelations

section PshRelCategory

/-- Wrapper type for presheaves on `C` whose
morphisms are presheaf relations (`PshRel`).
Using a `structure` prevents the existing
`Category` instance on `Cᵒᵖ ⥤ Type w` from
leaking through. -/
@[ext]
structure PshRelCat (C : Type u)
    [Category.{v} C] where
  obj : Cᵒᵖ ⥤ Type w

instance : Category.{max u v (w + 1)}
    (PshRelCat.{u, v, w} (C := C)) where
  Hom X Y := PshRel X.obj Y.obj
  id X := pshRelId X.obj
  comp R S := pshRelComp R S
  id_comp := pshRelComp_id_left
  comp_id := pshRelComp_id_right
  assoc := pshRelComp_assoc

/-- Functor sending each natural transformation
`α : P ⟶ Q` to its graph relation
`pshRelGraph α` in `PshRelCat C`. -/
def pshRelGraphFunctor :
    (Cᵒᵖ ⥤ Type w) ⥤
      PshRelCat.{u, v, w} (C := C) where
  obj P := ⟨P⟩
  map α := pshRelGraph α
  map_id P := pshRelGraph_eq_id P
  map_comp α β := (pshRelGraph_comp α β).symm

end PshRelCategory

section PshRelatedMorphisms

/-- The bifunctorial action of a pair of natural
transformations `(α, β)` on the product presheaf
`P × P'`. At stage `T`, this sends `(a, a')` to
`(α(a), β(a'))`. -/
abbrev pshProdMap
    {P P' Q Q' : Cᵒᵖ ⥤ Type w}
    (α : P ⟶ Q) (β : P' ⟶ Q') :
    pshProdPresheaf P P' ⟶
      pshProdPresheaf Q Q' :=
  pshProdLift
    (pshProdFst P P' ≫ α)
    (pshProdSnd P P' ≫ β)

@[simp]
theorem pshProdMap_fst
    {P P' Q Q' : Cᵒᵖ ⥤ Type w}
    (α : P ⟶ Q) (β : P' ⟶ Q') :
    pshProdMap α β ≫ pshProdFst Q Q' =
      pshProdFst P P' ≫ α := by
  simp [pshProdMap, pshProdLift]

@[simp]
theorem pshProdMap_snd
    {P P' Q Q' : Cᵒᵖ ⥤ Type w}
    (α : P ⟶ Q) (β : P' ⟶ Q') :
    pshProdMap α β ≫ pshProdSnd Q Q' =
      pshProdSnd P P' ≫ β := by
  simp [pshProdMap, pshProdLift]

@[simp]
theorem pshProdMap_id
    (P P' : Cᵒᵖ ⥤ Type w) :
    pshProdMap (𝟙 P) (𝟙 P') =
      𝟙 (pshProdPresheaf P P') := by
  apply pshProdPresheaf_hom_ext <;>
    simp [pshProdMap, pshProdLift]

theorem pshProdMap_comp
    {P P' Q Q' W W' : Cᵒᵖ ⥤ Type w}
    (α : P ⟶ Q) (β : P' ⟶ Q')
    (γ : Q ⟶ W) (δ : Q' ⟶ W') :
    pshProdMap (α ≫ γ) (β ≫ δ) =
      pshProdMap α β ≫
        pshProdMap γ δ := by
  apply pshProdPresheaf_hom_ext <;> {
    simp only [Category.assoc,
      pshProdMap_fst, pshProdMap_snd]
    simp only [← Category.assoc,
      pshProdMap_fst, pshProdMap_snd]
  }

/-- Two natural transformations `α : P ⟶ Q` and
`β : P' ⟶ Q'` are `(R, S)`-related at the
`PshProdOver` level when there exists a lift
`φ : R.left ⟶ S.left` making the square commute:
```
  R.left ---φ---> S.left
    |                |
    R.hom           S.hom
    v                v
  P × P' -------> Q × Q'
       (pshProdMap α β)
```
-/
def PshProdOverRelated
    {P P' Q Q' : Cᵒᵖ ⥤ Type w}
    (R : PshProdOver P P')
    (S : PshProdOver Q Q')
    (α : P ⟶ Q) (β : P' ⟶ Q') : Prop :=
  ∃ (φ : R.left ⟶ S.left),
    φ ≫ S.hom =
      R.hom ≫ pshProdMap α β

/-- `PshProdOverRelated` is invariant under
isomorphism in both relation arguments. -/
theorem pshProdOverRelated_iso
    {P P' Q Q' : Cᵒᵖ ⥤ Type w}
    {R₁ R₂ : PshProdOver P P'}
    {S₁ S₂ : PshProdOver Q Q'}
    (αR : R₁ ≅ R₂) (αS : S₁ ≅ S₂)
    {α : P ⟶ Q} {β : P' ⟶ Q'} :
    PshProdOverRelated R₁ S₁ α β ↔
      PshProdOverRelated R₂ S₂ α β := by
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

/-- Two natural transformations `α : P ⟶ Q` and
`β : P' ⟶ Q'` are `(R, S)`-related (where
`R : PshRel P P'` and `S : PshRel Q Q'`) when
they admit a lifting at the `PshProdOver` level.
This descends through the skeleton quotient via
`Skeleton.lift₂`, using `pshProdOverRelated_iso`
for well-definedness. -/
def pshRelRelated
    {P P' Q Q' : Cᵒᵖ ⥤ Type w}
    (α : P ⟶ Q) (β : P' ⟶ Q') :
    PshRel P P' → PshRel Q Q' → Prop :=
  Skeleton.lift₂
    (fun R S =>
      PshProdOverRelated R S α β)
    (fun _ _ _ _ ⟨αR⟩ ⟨αS⟩ =>
      propext
        (pshProdOverRelated_iso αR αS))

/-- For graph relations, `PshProdOverRelated`
reduces to commutativity of the naturality square.
The forward direction extracts the square from the
lift; the reverse constructs a lift from the
commuting square. -/
theorem pshProdOverRelated_graph_iff
    {P P' Q Q' : Cᵒᵖ ⥤ Type w}
    (α : P ⟶ P') (β : Q ⟶ Q')
    (γ : P ⟶ Q) (δ : P' ⟶ Q') :
    PshProdOverRelated
      (pshProdOverGraph α)
      (pshProdOverGraph β)
      γ δ ↔
    γ ≫ β = α ≫ δ := by
  constructor
  · rintro ⟨φ, hφ⟩
    have hfst :=
      congr_arg (· ≫ pshProdFst Q Q') hφ
    have hsnd :=
      congr_arg (· ≫ pshProdSnd Q Q') hφ
    simp only [Category.assoc,
      pshProdOverGraph_fst,
      pshProdOverGraph_fst_assoc,
      pshProdOverGraph_snd,
      pshProdOverGraph_snd_assoc,
      pshProdMap_fst,
      pshProdMap_snd] at hfst hsnd
    rw [← hfst]
    exact hsnd
  · intro hsq
    refine ⟨γ, ?_⟩
    apply pshProdPresheaf_hom_ext
    · simp only [Category.assoc,
        pshProdOverGraph_fst,
        pshProdOverGraph_fst_assoc,
        pshProdMap_fst]
      exact Category.comp_id _
    · simp only [Category.assoc,
        pshProdOverGraph_snd,
        pshProdOverGraph_snd_assoc,
        pshProdMap_snd]
      exact hsq

end PshRelatedMorphisms

section PshRelDoubleCategory

/-- The square type family for the presheaf relation
double category. -/
abbrev pshRelSQS :
    @SquareSet (Cᵒᵖ ⥤ Type w) PshRel
      (homSetOfQuiver (Cᵒᵖ ⥤ Type w)) :=
  fun R S α β => pshRelRelated α β R S

@[reassoc (attr := simp)]
theorem pshProdOverComp_fst
    {P Q W : Cᵒᵖ ⥤ Type w}
    (R : PshProdOver P Q)
    (S : PshProdOver Q W) :
    (pshProdOverComp R S).hom ≫
      pshProdFst P W =
    presheafPullbackFst
      (R.hom ≫ pshProdSnd P Q)
      (S.hom ≫ pshProdFst Q W) ≫
    R.hom ≫ pshProdFst P Q := by
  simp [pshProdOverComp, pshProdLift]

@[reassoc (attr := simp)]
theorem pshProdOverComp_snd
    {P Q W : Cᵒᵖ ⥤ Type w}
    (R : PshProdOver P Q)
    (S : PshProdOver Q W) :
    (pshProdOverComp R S).hom ≫
      pshProdSnd P W =
    presheafPullbackSnd
      (R.hom ≫ pshProdSnd P Q)
      (S.hom ≫ pshProdFst Q W) ≫
    S.hom ≫ pshProdSnd Q W := by
  simp [pshProdOverComp, pshProdLift]

/-- Horizontal composition of relatedness squares.

Given `pshRelRelated α γ R S` and
`pshRelRelated α' γ' S T`, the composite has
top `α ≫ α'`, bottom `γ ≫ γ'`, left `R`,
right `T`. -/
theorem pshRelRelatedHComp
    {P₁ P₂ P₃ Q₁ Q₂ Q₃ : Cᵒᵖ ⥤ Type w}
    {R : PshRel P₁ Q₁}
    {S : PshRel P₂ Q₂}
    {T : PshRel P₃ Q₃}
    {α : P₁ ⟶ P₂} {α' : P₂ ⟶ P₃}
    {γ : Q₁ ⟶ Q₂} {γ' : Q₂ ⟶ Q₃}
    (sq₁ : pshRelRelated α γ R S)
    (sq₂ : pshRelRelated α' γ' S T) :
    pshRelRelated (α ≫ α') (γ ≫ γ') R T := by
  induction R using Quotient.inductionOn with
  | h R₀ =>
  induction S using Quotient.inductionOn with
  | h S₀ =>
  induction T using Quotient.inductionOn with
  | h T₀ =>
  obtain ⟨φ₁, hφ₁⟩ := sq₁
  obtain ⟨φ₂, hφ₂⟩ := sq₂
  exact ⟨φ₁ ≫ φ₂, by
    rw [Category.assoc, hφ₂,
      ← Category.assoc, hφ₁, Category.assoc,
      pshProdMap_comp]⟩

/-- Horizontal identity square: for each vertical
morphism `R : PshRel P Q`, the pair `(𝟙 P, 𝟙 Q)`
is `(R, R)`-related. -/
theorem pshRelRelatedSqHorId
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) :
    pshRelRelated (𝟙 P) (𝟙 Q) R R := by
  induction R using Quotient.inductionOn with
  | h R₀ =>
  exact ⟨𝟙 R₀.left, by
    simp [pshProdMap_id]⟩

/-- Vertical identity square: for each horizontal
morphism `α : P ⟶ Q`, the pair
`(pshRelId P, pshRelId Q)` is
`(α, α)`-related. -/
theorem pshRelRelatedSqVertId
    {P Q : Cᵒᵖ ⥤ Type w}
    (α : P ⟶ Q) :
    pshRelRelated α α
      (pshRelId P) (pshRelId Q) := by
  change PshProdOverRelated
    (pshProdOverId P) (pshProdOverId Q) α α
  refine ⟨α, ?_⟩
  ext T x
  exact Prod.ext rfl rfl

/-- Vertical composition of relatedness squares.

Given `pshRelRelated α γ R S` and
`pshRelRelated γ δ R' S'`, the composite has
top `α`, bottom `δ`, left `pshRelComp R R'`,
right `pshRelComp S S'`. -/
theorem pshRelRelatedVComp
    {P₁ P₂ P₃ Q₁ Q₂ Q₃ : Cᵒᵖ ⥤ Type w}
    {R : PshRel P₁ P₂}
    {S : PshRel Q₁ Q₂}
    {R' : PshRel P₂ P₃}
    {S' : PshRel Q₂ Q₃}
    {α : P₁ ⟶ Q₁} {γ : P₂ ⟶ Q₂}
    {δ : P₃ ⟶ Q₃}
    (sq₁ : pshRelRelated α γ R S)
    (sq₂ : pshRelRelated γ δ R' S') :
    pshRelRelated α δ (pshRelComp R R')
      (pshRelComp S S') := by
  induction R using Quotient.inductionOn with
  | h R₀ =>
  induction S using Quotient.inductionOn with
  | h S₀ =>
  induction R' using Quotient.inductionOn with
  | h R₀' =>
  induction S' using Quotient.inductionOn with
  | h S₀' =>
  obtain ⟨φ₁, hφ₁⟩ := sq₁
  obtain ⟨φ₂, hφ₂⟩ := sq₂
  have hφ₁_r := reassoc_of% hφ₁
  have hφ₂_r := reassoc_of% hφ₂
  have pbcondR := presheafPullbackCondition
    (R₀.hom ≫ pshProdSnd P₁ P₂)
    (R₀'.hom ≫ pshProdFst P₂ P₃)
  have pbcondR_r := reassoc_of% pbcondR
  refine ⟨presheafPullbackLift
    (S₀.hom ≫ pshProdSnd Q₁ Q₂)
    (S₀'.hom ≫ pshProdFst Q₂ Q₃)
    (presheafPullbackFst
      (R₀.hom ≫ pshProdSnd P₁ P₂)
      (R₀'.hom ≫ pshProdFst P₂ P₃) ≫ φ₁)
    (presheafPullbackSnd
      (R₀.hom ≫ pshProdSnd P₁ P₂)
      (R₀'.hom ≫ pshProdFst P₂ P₃) ≫ φ₂)
    ?_, ?_⟩
  · simp only [Category.assoc, hφ₁_r,
      pshProdMap_snd, hφ₂_r,
      pshProdMap_fst]
    exact pbcondR_r _
  · apply pshProdPresheaf_hom_ext <;>
    simp only [Category.assoc,
      pshProdOverComp_fst,
      pshProdOverComp_fst_assoc,
      pshProdOverComp_snd,
      pshProdOverComp_snd_assoc,
      pshProdMap_fst, pshProdMap_snd,
      PullbackCone.IsLimit.lift_fst_assoc,
      PullbackCone.IsLimit.lift_snd_assoc,
      hφ₁_r, hφ₂_r]

/-- Operations for the presheaf relation double
category on presheaves over `C`. -/
def pshRelDoubleOps :
    DoubleCategoryOps (Cᵒᵖ ⥤ Type w) PshRel
      (homSetOfQuiver (Cᵒᵖ ⥤ Type w))
      pshRelSQS where
  vComp := fun R S => pshRelComp R S
  hComp := fun α β => α ≫ β
  vId := fun P => pshRelId P
  hId := fun P => 𝟙 P
  sqVComp := fun sq₁ sq₂ =>
    pshRelRelatedVComp sq₁ sq₂
  sqHComp := fun sq₁ sq₂ =>
    pshRelRelatedHComp sq₁ sq₂
  sqVertId := fun α => pshRelRelatedSqVertId α
  sqHorId := fun R => pshRelRelatedSqHorId R

/-- Laws for the presheaf relation double category.

The vertical category laws follow from
`pshRelComp_assoc`, `pshRelComp_id_left`,
`pshRelComp_id_right`. The horizontal category
laws follow from `Category.assoc`,
`Category.id_comp`, `Category.comp_id`. All square
laws hold because the square type
`pshRelRelated` is `Prop`-valued. -/
theorem pshRelDoubleLaws :
    DoubleCategoryLaws
      (pshRelDoubleOps (C := C)) where
  vertLaws := {
    assoc := fun R S T =>
      pshRelComp_assoc R S T
    id_laws := {
      id_comp := fun R =>
        pshRelComp_id_left R
      comp_id := fun R =>
        pshRelComp_id_right R
    }
  }
  horLaws := {
    assoc := fun α β γ =>
      Category.assoc α β γ
    id_laws := {
      id_comp := fun α => Category.id_comp α
      comp_id := fun α => Category.comp_id α
    }
  }
  sqLaws := {
    sqVAssoc := fun _ _ _ => by
      simp only [pshRelDoubleOps,
        pshRelComp_assoc]
      exact HEq.rfl
    sqHAssoc := fun _ _ _ => by
      simp only [pshRelDoubleOps,
        Category.assoc]
      exact HEq.rfl
    sqVIdComp := fun _ => by
      simp only [pshRelDoubleOps,
        pshRelComp_id_left]
      exact HEq.rfl
    sqVCompId := fun _ => by
      simp only [pshRelDoubleOps,
        pshRelComp_id_right]
      exact HEq.rfl
    sqHIdComp := fun _ => by
      simp only [pshRelDoubleOps,
        Category.id_comp]
      exact HEq.rfl
    sqHCompId := fun _ => by
      simp only [pshRelDoubleOps,
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

/-- The presheaf relation double category data:
operations and laws bundled together. -/
def pshRelDoubleData :
    DoubleCategoryData (Cᵒᵖ ⥤ Type w) PshRel
      (homSetOfQuiver (Cᵒᵖ ⥤ Type w))
      pshRelSQS where
  toDoubleCategoryOps := pshRelDoubleOps
  laws := pshRelDoubleLaws

end PshRelDoubleCategory

section PshBarrExtension

/-- The Barr extension of a functor `G` applied to a
proof-relevant relation `R : PshProdOver P Q`. The
result is a relation over `G.obj P × G.obj Q` whose
underlying presheaf is `G.obj R.left`, with projections
given by applying `G.map` to the two legs of the span.
-/
def pshBarrLift
    {P Q : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (R : PshProdOver P Q) :
    PshProdOver (G.obj P) (G.obj Q) :=
  Over.mk (pshProdLift
    (G.map (R.hom ≫ pshProdFst P Q))
    (G.map (R.hom ≫ pshProdSnd P Q)))

@[simp]
theorem pshBarrLift_fst
    {P Q : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (R : PshProdOver P Q) :
    (pshBarrLift G R).hom ≫
      pshProdFst (G.obj P) (G.obj Q) =
    G.map (R.hom ≫ pshProdFst P Q) :=
  rfl

@[simp]
theorem pshBarrLift_snd
    {P Q : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (R : PshProdOver P Q) :
    (pshBarrLift G R).hom ≫
      pshProdSnd (G.obj P) (G.obj Q) =
    G.map (R.hom ≫ pshProdSnd P Q) :=
  rfl

/-- The Barr extension preserves isomorphisms in the
Over category: an isomorphism `α : R ≅ S` in
`PshProdOver P Q` induces an isomorphism
`pshBarrLift G R ≅ pshBarrLift G S`. -/
def pshBarrLift_iso
    {P Q : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    {R S : PshProdOver P Q}
    (α : R ≅ S) :
    pshBarrLift G R ≅ pshBarrLift G S :=
  Over.isoMk (G.mapIso
    { hom := α.hom.left,
      inv := α.inv.left,
      hom_inv_id := by
        have := congrArg CommaMorphism.left
          α.hom_inv_id
        dsimp at this; exact this
      inv_hom_id := by
        have := congrArg CommaMorphism.left
          α.inv_hom_id
        dsimp at this; exact this })
    (by
      apply pshProdPresheaf_hom_ext <;> (
        simp only [Category.assoc,
          pshBarrLift_fst, pshBarrLift_snd,
          Functor.mapIso_hom]
        rw [← G.map_comp, ← Category.assoc,
          Over.w α.hom]))

/-- The Barr extension on skeleton-level relations.
Given `G : PSh(C) ⥤ PSh(C)` and `R : PshRel P Q`,
produces `PshRel (G.obj P) (G.obj Q)` by descending
`pshBarrLift` through the skeleton quotient. -/
def pshBarrLiftSkel
    {P Q : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (R : PshRel P Q) :
    PshRel (G.obj P) (G.obj Q) :=
  Skeleton.lift
    (fun R' =>
      toSkeleton _ (pshBarrLift G R'))
    (fun _ _ ⟨α⟩ =>
      toSkeleton_eq_iff.mpr
        ⟨pshBarrLift_iso G α⟩) R

/-- The Barr extension of a graph relation `pshRelGraph α`
equals `pshRelGraph (G.map α)`. -/
theorem pshBarrLiftSkel_graph
    {P Q : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (α : P ⟶ Q) :
    pshBarrLiftSkel G (pshRelGraph α) =
      pshRelGraph (G.map α) := by
  change toSkeleton _ (pshBarrLift G
    (pshProdOverGraph α)) =
    toSkeleton _ (pshProdOverGraph (G.map α))
  rw [toSkeleton_eq_iff]
  exact ⟨Over.isoMk (Iso.refl _) (by
    apply pshProdPresheaf_hom_ext
    · simp [pshBarrLift, pshProdOverGraph,
        pshProdLift, G.map_id]
    · simp [pshBarrLift, pshProdOverGraph,
        pshProdLift])⟩

/-- The Barr extension preserves relatedness: if
`α` and `β` are `(R, S)`-related at the `PshProdOver`
level, then `G.map α` and `G.map β` are
`(pshBarrLift G R, pshBarrLift G S)`-related. -/
theorem pshBarrLift_related
    {P P' Q Q' : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    {R : PshProdOver P P'}
    {S : PshProdOver Q Q'}
    {α : P ⟶ Q} {β : P' ⟶ Q'}
    (h : PshProdOverRelated R S α β) :
    PshProdOverRelated
      (pshBarrLift G R) (pshBarrLift G S)
      (G.map α) (G.map β) := by
  obtain ⟨φ, hφ⟩ := h
  have hfst := congr_arg
    (· ≫ pshProdFst Q Q') hφ
  have hsnd := congr_arg
    (· ≫ pshProdSnd Q Q') hφ
  simp only [Category.assoc, pshProdMap_fst,
    pshProdMap_snd] at hfst hsnd
  refine ⟨G.map φ, pshProdPresheaf_hom_ext ?_ ?_⟩
  · calc G.map φ ≫ G.map
          (S.hom ≫ pshProdFst Q Q')
        = G.map (φ ≫ S.hom ≫ pshProdFst Q Q')
          := by rw [← G.map_comp]
      _ = G.map
          (R.hom ≫ pshProdFst P P' ≫ α)
          := by rw [hfst]
      _ = G.map (R.hom ≫ pshProdFst P P') ≫
          G.map α
          := by rw [← Category.assoc,
                  G.map_comp]
  · calc G.map φ ≫ G.map
          (S.hom ≫ pshProdSnd Q Q')
        = G.map (φ ≫ S.hom ≫ pshProdSnd Q Q')
          := by rw [← G.map_comp]
      _ = G.map
          (R.hom ≫ pshProdSnd P P' ≫ β)
          := by rw [hsnd]
      _ = G.map (R.hom ≫ pshProdSnd P P') ≫
          G.map β
          := by rw [← Category.assoc,
                  G.map_comp]

/-- The skeleton-level version of
`pshBarrLift_related`: relatedness at the `PshRel`
level is preserved by `pshBarrLiftSkel`. -/
theorem pshBarrLiftSkel_related
    {P P' Q Q' : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    {α : P ⟶ Q} {β : P' ⟶ Q'}
    {R : PshRel P P'} {S : PshRel Q Q'}
    (h : pshRelRelated α β R S) :
    pshRelRelated (G.map α) (G.map β)
      (pshBarrLiftSkel G R)
      (pshBarrLiftSkel G S) := by
  revert h
  exact Quotient.ind₂
    (fun R' S' h => pshBarrLift_related G h)
    R S

end PshBarrExtension

section PshInternalHom

universe u₁ v₁

variable {D : Type u₁} [Category.{v₁} D]

/-- The profunctor map for the internal hom
`A.functorHom B`. Given `f : A' ⟶ A` and
`g : B ⟶ B'`, produces
`A.functorHom B ⟶ A'.functorHom B'` by
precomposing with `f` and postcomposing with `g`. -/
def pshIhomProfMap
    {A A' B B' : Dᵒᵖ ⥤ Type (max u₁ v₁)}
    (f : A' ⟶ A) (g : B ⟶ B') :
    A.functorHom B ⟶ A'.functorHom B' where
  app c φ :=
    { app := fun d h a' =>
        g.app d (φ.app d h (f.app d a'))
      naturality := fun {d e} k h => by
        ext a'
        simp only [types_comp_apply]
        have hf := congr_fun
          (f.naturality k) a'
        simp only [types_comp_apply] at hf
        have hφ := congr_fun
          (φ.naturality k h) (f.app d a')
        simp only [types_comp_apply] at hφ
        rw [← hf] at hφ; rw [hφ]
        have hg := congr_fun
          (g.naturality k)
          (φ.app d h (f.app d a'))
        simp only [types_comp_apply] at hg
        exact hg }
  naturality c₁ c₂ k := by
    ext c φ d h; rfl

/-- Identity law for `pshIhomProfMap`. -/
@[simp]
theorem pshIhomProfMap_id
    {A B : Dᵒᵖ ⥤ Type (max u₁ v₁)} :
    pshIhomProfMap (𝟙 A) (𝟙 B) =
      𝟙 (A.functorHom B) := by
  ext c φ d h a; rfl

/-- Composition law for `pshIhomProfMap`. -/
theorem pshIhomProfMap_comp
    {A A' A'' B B' B'' : Dᵒᵖ ⥤ Type (max u₁ v₁)}
    (f₁ : A' ⟶ A) (f₂ : A'' ⟶ A')
    (g₁ : B ⟶ B') (g₂ : B' ⟶ B'') :
    pshIhomProfMap (f₂ ≫ f₁) (g₁ ≫ g₂) =
      pshIhomProfMap f₁ g₁ ≫
        pshIhomProfMap f₂ g₂ := by
  ext c φ d h a; rfl

/-- The predicate defining when a pair of elements
of the internal hom presheaves are related by the
arrow relation. Given relations `R` on inputs and
`S` on outputs, `(g₁, g₂)` are arrow-related at
stage `c` iff for all morphisms `h : c ⟶ d` and
all `w` in the relation `R` at stage `d`, the
outputs `g₁(h, π₁ w)` and `g₂(h, π₂ w)` are
`S`-related. -/
def pshArrowRelPred
    {A₁ A₂ B₁ B₂ : Dᵒᵖ ⥤ Type (max u₁ v₁)}
    (R : PshProdOver A₁ A₂)
    (S : PshProdOver B₁ B₂)
    (c : Dᵒᵖ)
    (g : (A₁.functorHom B₁).obj c ×
         (A₂.functorHom B₂).obj c) :
    Prop :=
  ∀ (d : Dᵒᵖ) (h : c ⟶ d)
    (w : R.left.obj d),
    ∃ s : S.left.obj d,
      S.hom.app d s =
        (g.1.app d h (R.hom.app d w).1,
         g.2.app d h (R.hom.app d w).2)

/-- The presheaf underlying the arrow relation.
At stage `c`, an element is a pair
`(g₁, g₂) ∈ A₁.functorHom B₁ × A₂.functorHom B₂`
satisfying `pshArrowRelPred R S c (g₁, g₂)`. -/
def pshArrowRelPresheaf
    {A₁ A₂ B₁ B₂ : Dᵒᵖ ⥤ Type (max u₁ v₁)}
    (R : PshProdOver A₁ A₂)
    (S : PshProdOver B₁ B₂) :
    Dᵒᵖ ⥤ Type (max u₁ v₁) where
  obj c :=
    { g : (A₁.functorHom B₁).obj c ×
          (A₂.functorHom B₂).obj c //
      pshArrowRelPred R S c g }
  map k g :=
    ⟨((A₁.functorHom B₁).map k g.val.1,
      (A₂.functorHom B₂).map k g.val.2),
     fun d h' w => g.property d (k ≫ h') w⟩
  map_id c := by
    funext g; simp only [types_id_apply]
    apply Subtype.ext; apply Prod.ext <;>
      simp only [FunctorToTypes.map_id_apply]
  map_comp k₁ k₂ := by
    funext g; simp only [types_comp_apply]
    apply Subtype.ext; apply Prod.ext <;>
      simp only
        [FunctorToTypes.map_comp_apply]

/-- The arrow relation as a `PshProdOver`. Given
relations `R` on the inputs and `S` on the outputs,
`pshArrowRel R S` is a relation on the internal hom
presheaves `A₁.functorHom B₁` and
`A₂.functorHom B₂`. The underlying presheaf is
`pshArrowRelPresheaf R S` with projections given
by `.val.1` and `.val.2`. -/
def pshArrowRelFst
    {A₁ A₂ B₁ B₂ : Dᵒᵖ ⥤ Type (max u₁ v₁)}
    (R : PshProdOver A₁ A₂)
    (S : PshProdOver B₁ B₂) :
    pshArrowRelPresheaf R S ⟶ A₁.functorHom B₁
    where
  app c g := g.val.1
  naturality _ _ _ := by funext; rfl

def pshArrowRelSnd
    {A₁ A₂ B₁ B₂ : Dᵒᵖ ⥤ Type (max u₁ v₁)}
    (R : PshProdOver A₁ A₂)
    (S : PshProdOver B₁ B₂) :
    pshArrowRelPresheaf R S ⟶ A₂.functorHom B₂
    where
  app c g := g.val.2
  naturality _ _ _ := by funext; rfl

/-- The arrow relation as a `PshProdOver`. Given
relations `R` on the inputs and `S` on the outputs,
`pshArrowRel R S` is a relation on the internal hom
presheaves `A₁.functorHom B₁` and
`A₂.functorHom B₂`. The underlying presheaf is
`pshArrowRelPresheaf R S` with projections given
by `.val.1` and `.val.2`. -/
def pshArrowRel
    {A₁ A₂ B₁ B₂ : Dᵒᵖ ⥤ Type (max u₁ v₁)}
    (R : PshProdOver A₁ A₂)
    (S : PshProdOver B₁ B₂) :
    PshProdOver (A₁.functorHom B₁)
      (A₂.functorHom B₂) :=
  Over.mk (pshProdLift
    (pshArrowRelFst R S)
    (pshArrowRelSnd R S))

/-- The arrow relation predicate is preserved when
the input and output relations are replaced by
morphic images (via Over morphisms). -/
private theorem pshArrowRelPred_transport
    {A₁ A₂ B₁ B₂ : Dᵒᵖ ⥤ Type (max u₁ v₁)}
    {R₁ R₂ : PshProdOver A₁ A₂}
    {S₁ S₂ : PshProdOver B₁ B₂}
    (αinv : R₂ ⟶ R₁) (βhom : S₁ ⟶ S₂)
    {c : Dᵒᵖ}
    {g : (A₁.functorHom B₁).obj c ×
         (A₂.functorHom B₂).obj c}
    (h : pshArrowRelPred R₁ S₁ c g) :
    pshArrowRelPred R₂ S₂ c g := by
  intro d hd w₂
  have hR : R₁.hom.app d (αinv.left.app d w₂)
      = R₂.hom.app d w₂ :=
    congr_fun (NatTrans.congr_app
      (Over.w αinv) d) w₂
  obtain ⟨s₁, hs₁⟩ :=
    h d hd (αinv.left.app d w₂)
  have hS : S₂.hom.app d (βhom.left.app d s₁)
      = S₁.hom.app d s₁ :=
    congr_fun (NatTrans.congr_app
      (Over.w βhom) d) s₁
  exact ⟨βhom.left.app d s₁,
    by rw [hS, hs₁, hR]⟩

/-- The presheaf isomorphism underlying an arrow
relation isomorphism. Given Over-isomorphisms
`α : R₁ ≅ R₂` and `β : S₁ ≅ S₂`, the arrow
relation presheaf is unchanged (identity on the
`.val` component) with proof transported via
`pshArrowRelPred_transport`. -/
private def pshArrowRelPresheafIso
    {A₁ A₂ B₁ B₂ : Dᵒᵖ ⥤ Type (max u₁ v₁)}
    {R₁ R₂ : PshProdOver A₁ A₂}
    {S₁ S₂ : PshProdOver B₁ B₂}
    (α : R₁ ≅ R₂) (β : S₁ ≅ S₂) :
    pshArrowRelPresheaf R₁ S₁ ≅
      pshArrowRelPresheaf R₂ S₂ where
  hom :=
    { app := fun c g => ⟨g.val,
        pshArrowRelPred_transport
          α.inv β.hom g.property⟩
      naturality := fun _ _ _ => by
        funext; exact Subtype.ext rfl }
  inv :=
    { app := fun c g => ⟨g.val,
        pshArrowRelPred_transport
          α.hom β.inv g.property⟩
      naturality := fun _ _ _ => by
        funext; exact Subtype.ext rfl }
  hom_inv_id := by
    ext c g; exact Subtype.ext rfl
  inv_hom_id := by
    ext c g; exact Subtype.ext rfl

/-- Isomorphic input/output relations yield
isomorphic arrow relations. -/
def pshArrowRel_iso
    {A₁ A₂ B₁ B₂ : Dᵒᵖ ⥤ Type (max u₁ v₁)}
    {R₁ R₂ : PshProdOver A₁ A₂}
    {S₁ S₂ : PshProdOver B₁ B₂}
    (α : R₁ ≅ R₂) (β : S₁ ≅ S₂) :
    pshArrowRel R₁ S₁ ≅
      pshArrowRel R₂ S₂ :=
  Over.isoMk (pshArrowRelPresheafIso α β)
    (by ext c g; rfl)

/-- The arrow relation on skeleton-level relations.
Given `R : PshRel A₁ A₂` and `S : PshRel B₁ B₂`,
produces
`PshRel (A₁.functorHom B₁) (A₂.functorHom B₂)`
by descending `pshArrowRel` through the skeleton
quotient in both arguments. -/
def pshArrowRelSkel
    {A₁ A₂ B₁ B₂ : Dᵒᵖ ⥤ Type (max u₁ v₁)}
    (R : PshRel A₁ A₂)
    (S : PshRel B₁ B₂) :
    PshRel (A₁.functorHom B₁)
      (A₂.functorHom B₂) :=
  Skeleton.lift₂
    (fun R' S' =>
      toSkeleton _ (pshArrowRel R' S'))
    (fun _ _ _ _ ⟨α⟩ ⟨β⟩ =>
      toSkeleton_eq_iff.mpr
        ⟨pshArrowRel_iso α β⟩) R S

/-- The arrow relation preserves relatedness: if
the input morphisms `(α₁, α₂)` are
`(R₂, R₁)`-related (note the reversal from
contravariance) and the output morphisms
`(β₁, β₂)` are `(S₁, S₂)`-related, then
`pshIhomProfMap α₁ β₁` and
`pshIhomProfMap α₂ β₂` are
`(pshArrowRel R₁ S₁, pshArrowRel R₂ S₂)`-related.
-/
theorem pshArrowRel_related
    {A₁ A₂ A₁' A₂' B₁ B₂ B₁' B₂' :
      Dᵒᵖ ⥤ Type (max u₁ v₁)}
    {R₁ : PshProdOver A₁ A₂}
    {R₂ : PshProdOver A₁' A₂'}
    {S₁ : PshProdOver B₁ B₂}
    {S₂ : PshProdOver B₁' B₂'}
    {α₁ : A₁' ⟶ A₁} {α₂ : A₂' ⟶ A₂}
    {β₁ : B₁ ⟶ B₁'} {β₂ : B₂ ⟶ B₂'}
    (hα : PshProdOverRelated R₂ R₁ α₁ α₂)
    (hβ : PshProdOverRelated S₁ S₂ β₁ β₂) :
    PshProdOverRelated
      (pshArrowRel R₁ S₁)
      (pshArrowRel R₂ S₂)
      (pshIhomProfMap α₁ β₁)
      (pshIhomProfMap α₂ β₂) := by
  obtain ⟨φ_α, hα_eq⟩ := hα
  obtain ⟨φ_β, hβ_eq⟩ := hβ
  refine ⟨{
    app := fun c g => ⟨
      ((pshIhomProfMap α₁ β₁).app c g.val.1,
       (pshIhomProfMap α₂ β₂).app c g.val.2),
      fun d h w' => ?_⟩
    naturality := fun c₁ c₂ k => by
      funext g; exact Subtype.ext rfl
  }, ?_⟩
  · obtain ⟨s, hs⟩ :=
      g.property d h (φ_α.app d w')
    refine ⟨φ_β.app d s, ?_⟩
    have hS := congr_fun
      (NatTrans.congr_app hβ_eq d) s
    have hR := congr_fun
      (NatTrans.congr_app hα_eq d) w'
    simp only [NatTrans.comp_app,
      types_comp_apply] at hS hR
    rw [hS, hs, hR]
    simp [pshProdMap, pshProdLift,
      pshIhomProfMap]
  · apply pshProdPresheaf_hom_ext <;>
    (ext c g; rfl)

/-- Skeleton-level version of
`pshArrowRel_related`: the arrow relation
preserves relatedness at the `PshRel` level. -/
theorem pshArrowRelSkel_related
    {A₁ A₂ A₁' A₂' B₁ B₂ B₁' B₂' :
      Dᵒᵖ ⥤ Type (max u₁ v₁)}
    {α₁ : A₁' ⟶ A₁} {α₂ : A₂' ⟶ A₂}
    {β₁ : B₁ ⟶ B₁'} {β₂ : B₂ ⟶ B₂'}
    {R₁ : PshRel A₁ A₂}
    {R₂ : PshRel A₁' A₂'}
    {S₁ : PshRel B₁ B₂}
    {S₂ : PshRel B₁' B₂'}
    (hα : pshRelRelated α₁ α₂ R₂ R₁)
    (hβ : pshRelRelated β₁ β₂ S₁ S₂) :
    pshRelRelated
      (pshIhomProfMap α₁ β₁)
      (pshIhomProfMap α₂ β₂)
      (pshArrowRelSkel R₁ S₁)
      (pshArrowRelSkel R₂ S₂) := by
  revert hα hβ
  exact Quotient.ind₂
    (fun R₁' S₁' =>
      Quotient.ind₂
        (fun R₂' S₂' hα hβ =>
          pshArrowRel_related hα hβ)
        R₂ S₂)
    R₁ S₁

end PshInternalHom

section YonedaPreservesIhom

universe w₁

variable {D : Type w₁} [Category.{w₁} D]

/-- Data witnessing that `E` is an exponential of `A`
and `B` in `D`, in the form of an evaluation function
`evApp` and a currying function `curryApp` satisfying
the expected roundtrip conditions. -/
structure PshExponentialData
    (A B E : D) where
  evApp :
    ∀ {X : D}, (X ⟶ E) → (X ⟶ A) → (X ⟶ B)
  evApp_nat :
    ∀ {X Y : D} (g : Y ⟶ X)
      (e : X ⟶ E) (a : X ⟶ A),
      g ≫ evApp e a = evApp (g ≫ e) (g ≫ a)
  curryApp :
    ∀ (X : D),
      (∀ {Y : D}, (Y ⟶ X) →
        (Y ⟶ A) → (Y ⟶ B)) →
      (X ⟶ E)
  ev_curry :
    ∀ (X : D)
      (f : ∀ {Y : D}, (Y ⟶ X) →
        (Y ⟶ A) → (Y ⟶ B))
      {Z : D} (h : Z ⟶ X) (a : Z ⟶ A),
      evApp (h ≫ curryApp X f) a = f h a
  curry_ev :
    ∀ (X : D) (e : X ⟶ E),
      curryApp X
        (fun h a => evApp (h ≫ e) a) = e

variable {A B E : D}

/-- Forward map: given exponential data for `E` and
a morphism `e : X ⟶ E`, produce an element of
`(yoneda.obj A).functorHom (yoneda.obj B)` at
stage `op X`. -/
def pshIhomYonedaFwd
    (ed : PshExponentialData A B E)
    {X : D} (e : X ⟶ E) :
    ((yoneda.obj A).functorHom
      (yoneda.obj B)).obj (Opposite.op X) :=
  { app := fun d h a =>
      ed.evApp (h.unop ≫ e) a
    naturality := fun {d d'} g h => by
      ext a
      simp only [types_comp_apply,
        yoneda_obj_map]
      rw [ed.evApp_nat g.unop]
      congr 1
      dsimp
      simp only [Category.assoc] }

/-- Backward map: given an element of
`(yoneda.obj A).functorHom (yoneda.obj B)` at
stage `op X`, produce a morphism `X ⟶ E` by
currying the family restricted to the identity. -/
def pshIhomYonedaInv
    (ed : PshExponentialData A B E)
    {X : D}
    (f : ((yoneda.obj A).functorHom
      (yoneda.obj B)).obj (Opposite.op X)) :
    X ⟶ E :=
  ed.curryApp X (fun h a =>
    f.app (Opposite.op _) h.op a)

/-- The presheaf
`(yoneda.obj A).functorHom (yoneda.obj B)` is
representable by the exponential object `E`, given
exponential data `ed`. -/
def pshIhomYonedaRepresentableBy
    (ed : PshExponentialData A B E) :
    ((yoneda.obj A).functorHom
      (yoneda.obj B)).RepresentableBy E where
  homEquiv :=
    { toFun := pshIhomYonedaFwd ed
      invFun := pshIhomYonedaInv ed
      left_inv := fun e => ed.curry_ev _ e
      right_inv := fun f => by
        exact Functor.functorHom_ext
          fun d h => by
          ext a
          exact ed.ev_curry _ _ h.unop a }
  homEquiv_comp := fun f g => by
    exact Functor.functorHom_ext
      fun d h => by
      ext a
      dsimp [pshIhomYonedaFwd,
        Functor.functorHom, Functor.comp_map,
        Functor.homObjFunctor, Functor.rightOp,
        coyoneda]
      simp only [Category.assoc]

/-- The Yoneda embedding preserves exponentials:
`yoneda.obj E ≅ (yoneda.obj A).functorHom (yoneda.obj B)`
when `E` is an exponential of `A` and `B`. -/
def pshIhomYonedaIso
    (ed : PshExponentialData A B E) :
    yoneda.obj E ≅
      (yoneda.obj A).functorHom
        (yoneda.obj B) :=
  (pshIhomYonedaRepresentableBy ed).toIso

end YonedaPreservesIhom

end GebLean
