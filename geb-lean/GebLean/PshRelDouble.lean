import GebLean.Utilities.Skeleton
import GebLean.Utilities.Presheaf
import GebLean.Utilities.DoubleCategory
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes

/-!
# Internal Relations in PSh(C)

The double category of internal relations in the presheaf
category `PSh(C) = Cᵒᵖ ⥤ Type v`.

## Presheaf representation of relations

The presheaf `P × Q` (pointwise product) for
`P Q : Cᵒᵖ ⥤ Type v` represents pairs of generalized
elements of `P` and `Q`.

A proof-relevant relation from `P` to `Q` is a morphism
into `P × Q` in `PSh(C)`, i.e., an object of the over
category `Over (P × Q)`.

## Double category structure

- Objects: presheaves `P : Cᵒᵖ ⥤ Type v`
- Horizontal morphisms: natural transformations
- Vertical morphisms: `PshRel P Q` (isomorphism classes
  of objects over `P × Q`)
- Squares: `pshRelRelated` (`Prop`-valued)
-/

namespace GebLean

open CategoryTheory Limits

universe u v

variable {C : Type u} [Category.{v} C]

section PshRelations

/-- The product presheaf `P × Q`, constructed as
`FunctorToTypes.prod P Q`. -/
abbrev pshProdPresheaf
    (P Q : Cᵒᵖ ⥤ Type v) : Cᵒᵖ ⥤ Type v :=
  FunctorToTypes.prod P Q

/-- A proof-relevant relation from `P` to `Q` in
`PSh(C)`: an object of the over category
`Over (pshProdPresheaf P Q)`. -/
abbrev PshProdOver
    (P Q : Cᵒᵖ ⥤ Type v) :=
  Over (pshProdPresheaf P Q)

/-- First projection from the product presheaf
`P × Q` to `P`. -/
abbrev pshProdFst
    (P Q : Cᵒᵖ ⥤ Type v) :
    pshProdPresheaf P Q ⟶ P :=
  @FunctorToTypes.prod.fst _ _ P Q

/-- Second projection from the product presheaf
`P × Q` to `Q`. -/
abbrev pshProdSnd
    (P Q : Cᵒᵖ ⥤ Type v) :
    pshProdPresheaf P Q ⟶ Q :=
  @FunctorToTypes.prod.snd _ _ P Q

/-- Pairing of morphisms into `P` and `Q` to a
morphism into the product presheaf `P × Q`. -/
abbrev pshProdLift
    {R P Q : Cᵒᵖ ⥤ Type v}
    (f : R ⟶ P) (g : R ⟶ Q) :
    R ⟶ pshProdPresheaf P Q :=
  FunctorToTypes.prod.lift f g

/-- Two morphisms into `pshProdPresheaf P Q` are
equal iff their compositions with the two projections
agree. -/
theorem pshProdPresheaf_hom_ext
    {R P Q : Cᵒᵖ ⥤ Type v}
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
    {R P Q : Cᵒᵖ ⥤ Type v}
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
    (P : Cᵒᵖ ⥤ Type v) : PshProdOver P P :=
  Over.mk (pshProdLift (𝟙 P) (𝟙 P))

@[simp]
theorem pshProdOverId_fst
    (P : Cᵒᵖ ⥤ Type v) :
    (pshProdOverId P).hom ≫ pshProdFst P P =
    𝟙 P :=
  rfl

@[simp]
theorem pshProdOverId_snd
    (P : Cᵒᵖ ⥤ Type v) :
    (pshProdOverId P).hom ≫ pshProdSnd P P =
    𝟙 P :=
  rfl

/-- The graph of a natural transformation `α : P ⟶ Q`
as a proof-relevant relation. The underlying presheaf
is `P`, with first projection the identity and second
projection `α`. -/
def pshProdOverGraph
    {P Q : Cᵒᵖ ⥤ Type v} (α : P ⟶ Q) :
    PshProdOver P Q :=
  Over.mk (pshProdLift (𝟙 P) α)

@[simp]
theorem pshProdOverGraph_fst
    {P Q : Cᵒᵖ ⥤ Type v} (α : P ⟶ Q) :
    (pshProdOverGraph α).hom ≫
      pshProdFst P Q =
    𝟙 P :=
  rfl

@[simp]
theorem pshProdOverGraph_snd
    {P Q : Cᵒᵖ ⥤ Type v} (α : P ⟶ Q) :
    (pshProdOverGraph α).hom ≫
      pshProdSnd P Q = α :=
  rfl

theorem pshProdOverGraph_snd_assoc
    {P Q : Cᵒᵖ ⥤ Type v} (α : P ⟶ Q)
    {R : Cᵒᵖ ⥤ Type v}
    (k : Q ⟶ R) :
    (pshProdOverGraph α).hom ≫
      pshProdSnd P Q ≫ k =
    α ≫ k := by
  rw [← Category.assoc, pshProdOverGraph_snd]

theorem pshProdOverGraph_fst_assoc
    {P Q : Cᵒᵖ ⥤ Type v} (α : P ⟶ Q)
    {R : Cᵒᵖ ⥤ Type v}
    (k : P ⟶ R) :
    (pshProdOverGraph α).hom ≫
      pshProdFst P Q ≫ k =
    k := by
  rw [← Category.assoc, pshProdOverGraph_fst]
  exact Category.id_comp k

theorem pshProdOverGraph_id
    (P : Cᵒᵖ ⥤ Type v) :
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
    {P Q W : Cᵒᵖ ⥤ Type v}
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
    (P Q : Cᵒᵖ ⥤ Type v) :=
  Skeleton (PshProdOver P Q)

/-- The identity relation on `P`, up to
isomorphism. -/
def pshRelId
    (P : Cᵒᵖ ⥤ Type v) : PshRel P P :=
  toSkeleton _ (pshProdOverId P)

/-- `pshProdOverComp` respects isomorphisms: given
isomorphisms `R₁ ≅ R₂` and `S₁ ≅ S₂` in the over
categories, their compositions are isomorphic. -/
def pshProdOverComp_iso
    {P Q W : Cᵒᵖ ⥤ Type v}
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
    {P Q : Cᵒᵖ ⥤ Type v}
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
    {P Q : Cᵒᵖ ⥤ Type v}
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
    {P Q W X : Cᵒᵖ ⥤ Type v}
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
    {P Q W : Cᵒᵖ ⥤ Type v}
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
    {P Q W : Cᵒᵖ ⥤ Type v} :
    PshRel P Q → PshRel Q W →
    PshRel P W :=
  Skeleton.lift₂
    (fun R S =>
      toSkeleton _ (pshProdOverComp R S))
    (fun _ _ _ _ ⟨αR⟩ ⟨αS⟩ =>
      toSkeleton_eq_iff.mpr
        ⟨pshProdOverComp_iso αR αS⟩)

theorem pshRelComp_id_left
    {P Q : Cᵒᵖ ⥤ Type v}
    (R : PshRel P Q) :
    pshRelComp (pshRelId P) R = R := by
  induction R using Quotient.inductionOn with
  | h R' =>
    exact toSkeleton_eq_iff.mpr
      ⟨pshProdOverComp_id_left R'⟩

theorem pshRelComp_id_right
    {P Q : Cᵒᵖ ⥤ Type v}
    (R : PshRel P Q) :
    pshRelComp R (pshRelId Q) = R := by
  induction R using Quotient.inductionOn with
  | h R' =>
    exact toSkeleton_eq_iff.mpr
      ⟨pshProdOverComp_id_right R'⟩

theorem pshRelComp_assoc
    {P Q W X : Cᵒᵖ ⥤ Type v}
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
    {P Q : Cᵒᵖ ⥤ Type v} (α : P ⟶ Q) :
    PshRel P Q :=
  toSkeleton _ (pshProdOverGraph α)

theorem pshRelGraph_eq_id
    (P : Cᵒᵖ ⥤ Type v) :
    pshRelGraph (𝟙 P) = pshRelId P := by
  simp [pshRelGraph, pshRelId,
    pshProdOverGraph_id]

theorem pshRelGraph_comp
    {P Q W : Cᵒᵖ ⥤ Type v}
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
`Category` instance on `Cᵒᵖ ⥤ Type v` from
leaking through. -/
@[ext]
structure PshRelCat (C : Type u)
    [Category.{v} C] where
  obj : Cᵒᵖ ⥤ Type v

instance : Category.{max u (v + 1)}
    (PshRelCat (C := C)) where
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
    (Cᵒᵖ ⥤ Type v) ⥤ PshRelCat (C := C) where
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
    {P P' Q Q' : Cᵒᵖ ⥤ Type v}
    (α : P ⟶ Q) (β : P' ⟶ Q') :
    pshProdPresheaf P P' ⟶
      pshProdPresheaf Q Q' :=
  pshProdLift
    (pshProdFst P P' ≫ α)
    (pshProdSnd P P' ≫ β)

@[simp]
theorem pshProdMap_fst
    {P P' Q Q' : Cᵒᵖ ⥤ Type v}
    (α : P ⟶ Q) (β : P' ⟶ Q') :
    pshProdMap α β ≫ pshProdFst Q Q' =
      pshProdFst P P' ≫ α := by
  simp [pshProdMap, pshProdLift]

@[simp]
theorem pshProdMap_snd
    {P P' Q Q' : Cᵒᵖ ⥤ Type v}
    (α : P ⟶ Q) (β : P' ⟶ Q') :
    pshProdMap α β ≫ pshProdSnd Q Q' =
      pshProdSnd P P' ≫ β := by
  simp [pshProdMap, pshProdLift]

@[simp]
theorem pshProdMap_id
    (P P' : Cᵒᵖ ⥤ Type v) :
    pshProdMap (𝟙 P) (𝟙 P') =
      𝟙 (pshProdPresheaf P P') := by
  apply pshProdPresheaf_hom_ext <;>
    simp [pshProdMap, pshProdLift]

theorem pshProdMap_comp
    {P P' Q Q' W W' : Cᵒᵖ ⥤ Type v}
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
    {P P' Q Q' : Cᵒᵖ ⥤ Type v}
    (R : PshProdOver P P')
    (S : PshProdOver Q Q')
    (α : P ⟶ Q) (β : P' ⟶ Q') : Prop :=
  ∃ (φ : R.left ⟶ S.left),
    φ ≫ S.hom =
      R.hom ≫ pshProdMap α β

/-- `PshProdOverRelated` is invariant under
isomorphism in both relation arguments. -/
theorem pshProdOverRelated_iso
    {P P' Q Q' : Cᵒᵖ ⥤ Type v}
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
    {P P' Q Q' : Cᵒᵖ ⥤ Type v}
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
    {P P' Q Q' : Cᵒᵖ ⥤ Type v}
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
    @SquareSet (Cᵒᵖ ⥤ Type v) PshRel
      (homSetOfQuiver (Cᵒᵖ ⥤ Type v)) :=
  fun R S α β => pshRelRelated α β R S

@[reassoc (attr := simp)]
theorem pshProdOverComp_fst
    {P Q W : Cᵒᵖ ⥤ Type v}
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
    {P Q W : Cᵒᵖ ⥤ Type v}
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
    {P₁ P₂ P₃ Q₁ Q₂ Q₃ : Cᵒᵖ ⥤ Type v}
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
    {P Q : Cᵒᵖ ⥤ Type v}
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
    {P Q : Cᵒᵖ ⥤ Type v}
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
    {P₁ P₂ P₃ Q₁ Q₂ Q₃ : Cᵒᵖ ⥤ Type v}
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
    DoubleCategoryOps (Cᵒᵖ ⥤ Type v) PshRel
      (homSetOfQuiver (Cᵒᵖ ⥤ Type v))
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
    DoubleCategoryData (Cᵒᵖ ⥤ Type v) PshRel
      (homSetOfQuiver (Cᵒᵖ ⥤ Type v))
      pshRelSQS where
  toDoubleCategoryOps := pshRelDoubleOps
  laws := pshRelDoubleLaws

end PshRelDoubleCategory

end GebLean
