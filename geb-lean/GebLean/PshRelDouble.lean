import GebLean.Utilities.DaggerCategory
import GebLean.Utilities.Presheaf
import GebLean.Utilities.DoubleCategory
import Mathlib.CategoryTheory.Limits.Types.Products
import Mathlib.CategoryTheory.Limits.Shapes.FunctorToTypes
import Mathlib.CategoryTheory.Monoidal.Closed.Cartesian
import Mathlib.CategoryTheory.Monoidal.Closed.FunctorToTypes
import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.CategoryTheory.Subfunctor.Image
import Mathlib.CategoryTheory.Comma.Arrow
import Mathlib.CategoryTheory.FiberedCategory.Fibered
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Pullbacks
import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# Internal Relations in PSh(C)

The double category of internal relations in the
presheaf category `PSh(C) = Cᵒᵖ ⥤ Type w`.

This is the presheaf-level generalization of
Wadler's relational interpretation of types
(Section 2 of "Theorems for free!"): types
become presheaves, relations become subfunctors
of products, graphs of functions become graphs
of natural transformations.

## Presheaf representation of relations

The presheaf `P × Q` (pointwise product) for
`P Q : Cᵒᵖ ⥤ Type w` represents pairs of
generalized elements of `P` and `Q`.

A proof-relevant relation from `P` to `Q` is a
morphism into `P × Q` in `PSh(C)`, i.e., an
object of the over category `Over (P × Q)`.

## Double category structure

- Objects: presheaves `P : Cᵒᵖ ⥤ Type w`
- Horizontal morphisms: natural transformations
- Vertical morphisms: `PshRel P Q` (subfunctors
  of `P × Q`)
- Squares: `pshRelRelated` (`Prop`-valued)

## Barr extension and the edge category

The Barr extension (`pshBarrLiftRel`) lifts an
endofunctor `G : PSh(C) ⥤ PSh(C)` to act on
relations: given `R : PshRel P Q`, it produces
`pshBarrLiftRel G R : PshRel (G P) (G Q)`.
This is the presheaf-level analogue of Wadler's
`A* = {(map a x, map a y) | (x,y) in A}`.

The edge category `PshRelEdge C` has objects
`(P, Q, R)` with `R : PshRel P Q` and morphisms
preserving relatedness. The identity section
functor `pshRelIdentFunctor` sends `P` to
`(P, P, pshRelId P)`.
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

set_option backward.isDefEq.respectTransparency false in
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

/-- A relation from `P` to `Q` as a subfunctor
of the product presheaf `P × Q`: a family of
subsets of `P(c) × Q(c)` closed under
restriction. -/
abbrev PshRel
    (P Q : Cᵒᵖ ⥤ Type w) :=
  Subfunctor (pshProdPresheaf P Q)

/-- The identity relation on `P`: the diagonal
subfunctor of `P × P`. -/
def pshRelId
    (P : Cᵒᵖ ⥤ Type w) : PshRel P P where
  obj c := { pp | pp.1 = pp.2 }
  map f := by
    rintro ⟨_, _⟩ h
    exact congrArg (P.map f) h

/-- The diagonal subfunctor `pshRelId P` is
isomorphic to `P` via the first projection.
The inverse sends `a` to the diagonal pair
`(a, a)`. -/
def pshRelIdIso
    (P : Cᵒᵖ ⥤ Type w) :
    (pshRelId P).toFunctor ≅ P where
  hom := (pshRelId P).ι ≫ pshProdFst P P
  inv :=
    { app := fun c a => ⟨(a, a), rfl⟩
      naturality := fun c d f => by
        ext a; apply Subtype.ext
        exact Prod.ext rfl rfl }
  hom_inv_id := by
    ext c ⟨⟨x, y⟩, (h : x = y)⟩
    exact Subtype.ext (Prod.ext rfl h)
  inv_hom_id := by ext; rfl

/-- The two projections from the diagonal
relation `pshRelId P` are equal. -/
theorem pshRelId_fst_eq_snd
    (P : Cᵒᵖ ⥤ Type w) :
    (pshRelId P).ι ≫ pshProdFst P P =
    (pshRelId P).ι ≫ pshProdSnd P P := by
  ext c ⟨⟨_, _⟩, (h : _ = _)⟩
  exact h

/-- Projection from a proof-relevant relation
(span into `P × Q`) to a subfunctor of `P × Q`,
given by the image of the span morphism. -/
def pshProdOverToRel
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshProdOver P Q) : PshRel P Q :=
  Subfunctor.range R.hom

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

set_option backward.isDefEq.respectTransparency false in
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

/-- Composition of relations as subfunctors:
the composite of `R ⊆ P × Q` and `S ⊆ Q × W`
is the subfunctor of `P × W` whose elements
are pairs `(p, w)` such that there exists
`q : Q(c)` with `(p, q) ∈ R` and
`(q, w) ∈ S`. -/
def pshRelComp
    {P Q W : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) (S : PshRel Q W) :
    PshRel P W where
  obj c := { pw |
    ∃ q : Q.obj c,
      (pw.1, q) ∈ R.obj c ∧
        (q, pw.2) ∈ S.obj c }
  map f := by
    rintro ⟨_, _⟩ ⟨q, hR, hS⟩
    exact ⟨Q.map f q,
      R.map f hR, S.map f hS⟩

theorem pshRelComp_id_left
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) :
    pshRelComp (pshRelId P) R = R := by
  ext c x
  change (∃ q, x.1 = q ∧
    (q, x.2) ∈ R.obj c) ↔ _
  constructor
  · rintro ⟨_, rfl, hR⟩
    rwa [Prod.eta] at hR
  · intro hx
    refine ⟨x.1, rfl, ?_⟩
    rw [Prod.eta]; exact hx

theorem pshRelComp_id_right
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) :
    pshRelComp R (pshRelId Q) = R := by
  ext c x
  change (∃ q, (x.1, q) ∈ R.obj c ∧
    q = x.2) ↔ _
  constructor
  · rintro ⟨_, hR, rfl⟩
    rwa [Prod.eta] at hR
  · intro hx
    refine ⟨x.2, ?_, rfl⟩
    rw [Prod.eta]; exact hx

theorem pshRelComp_assoc
    {P Q W X : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q)
    (S : PshRel Q W)
    (T : PshRel W X) :
    pshRelComp (pshRelComp R S) T =
      pshRelComp R (pshRelComp S T) := by
  ext c x
  constructor
  · rintro ⟨w, ⟨q, hR, hS⟩, hT⟩
    exact ⟨q, hR, w, hS, hT⟩
  · rintro ⟨q, hR, w, hS, hT⟩
    exact ⟨w, ⟨q, hR, hS⟩, hT⟩

/-- The graph of a natural transformation as a
subfunctor of `P × Q`: elements `(p, q)` such
that `α(p) = q`. -/
def pshRelGraph
    {P Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    PshRel P Q where
  obj c := { pq | α.app c pq.1 = pq.2 }
  map {c d} f := by
    rintro ⟨p, q⟩ (h : α.app c p = q)
    change α.app d (P.map f p) = Q.map f q
    rw [← h]
    exact congr_fun (α.naturality f) p

theorem pshRelGraph_eq_id
    (P : Cᵒᵖ ⥤ Type w) :
    pshRelGraph (𝟙 P) = pshRelId P := by
  ext c x
  constructor <;> (intro h; exact h)

theorem pshRelGraph_comp
    {P Q W : Cᵒᵖ ⥤ Type w}
    (α : P ⟶ Q) (β : Q ⟶ W) :
    pshRelComp (pshRelGraph α)
      (pshRelGraph β) =
      pshRelGraph (α ≫ β) := by
  ext c x
  change (∃ q, α.app c x.1 = q ∧
    β.app c q = x.2) ↔
    β.app c (α.app c x.1) = x.2
  constructor
  · rintro ⟨_, rfl, hβ⟩; exact hβ
  · intro h; exact ⟨α.app c x.1, rfl, h⟩

/-- The graph construction is injective: if
`pshRelGraph α = pshRelGraph β` then `α = β`. -/
theorem pshRelGraph_injective
    {P Q : Cᵒᵖ ⥤ Type w}
    {α β : P ⟶ Q}
    (h : pshRelGraph α = pshRelGraph β) :
    α = β := by
  ext c p
  have hmem : (⟨p, α.app c p⟩ :
      P.obj c × Q.obj c) ∈
      (pshRelGraph β).obj c := by
    rw [← h]; exact rfl
  exact hmem.symm

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

instance : Category.{max u w}
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

instance : Functor.Faithful
    (pshRelGraphFunctor :
      (Cᵒᵖ ⥤ Type w) ⥤
        PshRelCat.{u, v, w} (C := C)) where
  map_injective := pshRelGraph_injective

end PshRelCategory

section PshRelDagger

/-- The swap natural transformation `P × Q ⟶ Q × P`. -/
def pshProdSwap
    (P Q : Cᵒᵖ ⥤ Type w) :
    pshProdPresheaf P Q ⟶
      pshProdPresheaf Q P :=
  pshProdLift (pshProdSnd P Q) (pshProdFst P Q)

@[simp]
theorem pshProdSwap_fst
    (P Q : Cᵒᵖ ⥤ Type w) :
    pshProdSwap P Q ≫ pshProdFst Q P =
      pshProdSnd P Q := by
  simp [pshProdSwap, pshProdLift]

@[simp]
theorem pshProdSwap_snd
    (P Q : Cᵒᵖ ⥤ Type w) :
    pshProdSwap P Q ≫ pshProdSnd Q P =
      pshProdFst P Q := by
  simp [pshProdSwap, pshProdLift]

@[simp]
theorem pshProdSwap_comp
    (P Q : Cᵒᵖ ⥤ Type w) :
    pshProdSwap P Q ≫ pshProdSwap Q P =
      𝟙 (pshProdPresheaf P Q) := by
  apply pshProdPresheaf_hom_ext <;>
  simp [pshProdSwap, pshProdLift]

/-- The dagger of an object in `PshProdOver P Q`:
reorder the two projections to get an object of
`PshProdOver Q P`. -/
def pshProdOverDagger
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshProdOver P Q) :
    PshProdOver Q P :=
  Over.mk (R.hom ≫ pshProdSwap P Q)

set_option backward.isDefEq.respectTransparency false in
/-- The dagger at the `PshProdOver` level is
involutive. -/
theorem pshProdOverDagger_dagger
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshProdOver P Q) :
    pshProdOverDagger (pshProdOverDagger R) = R := by
  simp only [pshProdOverDagger, Over.mk_hom,
    Category.assoc, pshProdSwap_comp]
  rfl

/-- The dagger operation on `PshRel P Q`:
swaps the two components to give
`PshRel Q P`. -/
def pshRelDagger
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) : PshRel Q P where
  obj c := { qp | (qp.2, qp.1) ∈ R.obj c }
  map f := by rintro ⟨_, _⟩ h; exact R.map f h

theorem pshRelDagger_dagger
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) :
    pshRelDagger (pshRelDagger R) = R := by
  ext c ⟨p, q⟩
  exact Iff.rfl

theorem pshRelDagger_id
    (P : Cᵒᵖ ⥤ Type w) :
    pshRelDagger (pshRelId P) = pshRelId P := by
  ext c x
  simp only [pshRelDagger, pshRelId,
    Set.mem_setOf_eq]
  exact ⟨Eq.symm, Eq.symm⟩

theorem pshRelDagger_comp
    {P Q W : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) (S : PshRel Q W) :
    pshRelDagger (pshRelComp R S) =
      pshRelComp (pshRelDagger S)
        (pshRelDagger R) := by
  ext c x
  simp only [pshRelDagger, pshRelComp,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨q, hR, hS⟩; exact ⟨q, hS, hR⟩
  · rintro ⟨q, hS, hR⟩; exact ⟨q, hR, hS⟩

/-- `PshRelCat C` is a dagger category, with the
dagger given by `pshRelDagger`. -/
instance : DaggerCategory
    (PshRelCat.{u, v, w} (C := C)) where
  dagger R := pshRelDagger R
  dagger_id X := pshRelDagger_id X.obj
  dagger_comp R S := pshRelDagger_comp R S
  dagger_involutive R := pshRelDagger_dagger R

end PshRelDagger

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

/-- The preimage of a relation `R : PshRel P Q`
along morphisms `α : P' ⟶ P` and `β : Q' ⟶ Q`.
A pair `(p', q')` is in the preimage iff
`(α p', β q')` is in `R`. -/
def pshRelPreimage
    {P Q P' Q' : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) (α : P' ⟶ P)
    (β : Q' ⟶ Q) : PshRel P' Q' :=
  R.preimage (pshProdMap α β)

@[simp]
theorem pshRelPreimage_id
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) :
    pshRelPreimage R (𝟙 P) (𝟙 Q) = R := by
  simp [pshRelPreimage]

theorem pshRelPreimage_comp
    {P Q P' Q' P'' Q'' : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q)
    (α : P' ⟶ P) (β : Q' ⟶ Q)
    (α' : P'' ⟶ P') (β' : Q'' ⟶ Q') :
    pshRelPreimage R (α' ≫ α) (β' ≫ β) =
      pshRelPreimage
        (pshRelPreimage R α β) α' β' := by
  simp [pshRelPreimage, pshProdMap_comp,
    Subfunctor.preimage_comp]

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

set_option backward.isDefEq.respectTransparency false in
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
`α` and `β` map `R`-related pairs to
`S`-related pairs. -/
def pshRelRelated
    {P P' Q Q' : Cᵒᵖ ⥤ Type w}
    (α : P ⟶ Q) (β : P' ⟶ Q')
    (R : PshRel P P') (S : PshRel Q Q') :
    Prop :=
  ∀ (c : Cᵒᵖ) (p : P.obj c) (p' : P'.obj c),
    (p, p') ∈ R.obj c →
      (α.app c p, β.app c p') ∈ S.obj c

set_option backward.isDefEq.respectTransparency false in
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

/-- For graph relations, `pshRelRelated` reduces
to commutativity of the naturality square. This
is the subsumptivity result (Hermida/Reddy/
Robinson, Proposition 6.3) stated as a 2-cell
characterization in the double category of
presheaf relations. -/
theorem pshRelRelated_graph_iff
    {P P' Q Q' : Cᵒᵖ ⥤ Type w}
    (α : P ⟶ Q) (β : P' ⟶ Q')
    (f : P ⟶ P') (g : Q ⟶ Q') :
    pshRelRelated f g
      (pshRelGraph α) (pshRelGraph β) ↔
    α ≫ g = f ≫ β := by
  constructor
  · intro h
    ext c p
    exact (h c p (α.app c p) rfl).symm
  · intro h c p q (hα : α.app c p = q)
    change β.app c (f.app c p) = g.app c q
    rw [← hα]
    exact congr_fun (congr_app h c) p |>.symm

/-- The preimage relation is related to the
original: the morphisms `(α, β)` send
`pshRelPreimage R α β`-related pairs to
`R`-related pairs. -/
theorem pshRelPreimage_related
    {P Q P' Q' : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) (α : P' ⟶ P)
    (β : Q' ⟶ Q) :
    pshRelRelated α β
      (pshRelPreimage R α β) R :=
  fun _ _ _ h => h

/-- The preimage is the largest relation on
`(P', Q')` that is `(α, β)`-related to `R`:
any `S` with `pshRelRelated α β S R` satisfies
`S ≤ pshRelPreimage R α β`. -/
theorem pshRelPreimage_universal
    {P Q P' Q' : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) (α : P' ⟶ P)
    (β : Q' ⟶ Q)
    {S : PshRel P' Q'}
    (h : pshRelRelated α β S R) :
    S ≤ pshRelPreimage R α β :=
  (Subfunctor.le_def S _).mpr fun c pp hS =>
    h c pp.1 pp.2 hS

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
    pshRelRelated (α ≫ α') (γ ≫ γ') R T :=
  fun c p q hR =>
    sq₂ c (α.app c p) (γ.app c q) (sq₁ c p q hR)

/-- Horizontal identity square: for each vertical
morphism `R : PshRel P Q`, the pair `(𝟙 P, 𝟙 Q)`
is `(R, R)`-related. -/
theorem pshRelRelatedSqHorId
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) :
    pshRelRelated (𝟙 P) (𝟙 Q) R R :=
  fun _ _ _ h => h

/-- Vertical identity square: for each horizontal
morphism `α : P ⟶ Q`, the pair
`(pshRelId P, pshRelId Q)` is
`(α, α)`-related. -/
theorem pshRelRelatedSqVertId
    {P Q : Cᵒᵖ ⥤ Type w}
    (α : P ⟶ Q) :
    pshRelRelated α α
      (pshRelId P) (pshRelId Q) :=
  fun _ _ _ (h : _ = _) => congrArg (α.app _) h

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
  intro c p p₃ hcomp
  obtain ⟨p₂, hR, hR'⟩ := hcomp
  exact ⟨γ.app c p₂,
    sq₁ c p p₂ hR, sq₂ c p₂ p₃ hR'⟩

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

section PshRelEdgeCategory

/-- The edge category of the double category of
presheaf relations, as an instance of the
horizontal 1-category of vertical edges.
Objects are presheaf relations; morphisms are
pairs of natural transformations with a 2-cell
compatibility condition. -/
abbrev PshRelEdge (C : Type u)
    [Category.{v} C] :=
  VertEdge (Obj := Cᵒᵖ ⥤ Type w) PshRel

/-- Morphisms in the presheaf relation edge
category, as an instance of the general
vertical-edge morphism construction. -/
abbrev PshRelEdgeHom :=
  VertEdgeHom
    (hhs := homSetOfQuiver (Cᵒᵖ ⥤ Type w))
    pshRelSQS

instance pshRelEdgeCategory : Category
    (PshRelEdge.{u, v, w} C) :=
  vertEdgeCategory pshRelSQS pshRelDoubleData

/-- The graph functor from the arrow category of
presheaves to the edge category of the double
category of presheaf relations. Sends a natural
transformation `α : P ⟶ Q` to the edge
`⟨P, Q, pshRelGraph α⟩`. -/
def pshRelEdgeGraphFunctor :
    Arrow (Cᵒᵖ ⥤ Type w) ⥤
    PshRelEdge.{u, v, w} C where
  obj f :=
    { src := f.left
      tgt := f.right
      edge := pshRelGraph f.hom }
  map {f g} sq :=
    { srcMap := sq.left
      tgtMap := sq.right
      sq :=
        (pshRelRelated_graph_iff
          f.hom g.hom sq.left sq.right).mpr
          sq.w.symm }
  map_id _ := VertEdgeHom.ext rfl rfl
  map_comp _ _ := VertEdgeHom.ext rfl rfl

/-- The graph functor to the edge category is
fully faithful: morphisms between graph relations
correspond bijectively to commutative squares. -/
def pshRelEdgeGraphFullyFaithful :
    (pshRelEdgeGraphFunctor :
      Arrow (Cᵒᵖ ⥤ Type w) ⥤
        PshRelEdge.{u, v, w} C
    ).FullyFaithful where
  preimage {f g} h :=
    Arrow.homMk h.srcMap h.tgtMap
      ((pshRelRelated_graph_iff
        f.hom g.hom h.srcMap h.tgtMap).mp
        h.sq).symm
  map_preimage _ :=
    VertEdgeHom.ext rfl rfl
  preimage_map _ := by
    apply CommaMorphism.ext <;> rfl

instance pshRelEdgeGraphFull :
    (pshRelEdgeGraphFunctor :
      Arrow (Cᵒᵖ ⥤ Type w) ⥤
        PshRelEdge.{u, v, w} C).Full :=
  (pshRelEdgeGraphFullyFaithful
    (C := C)).full

instance pshRelEdgeGraphFaithful :
    (pshRelEdgeGraphFunctor :
      Arrow (Cᵒᵖ ⥤ Type w) ⥤
        PshRelEdge.{u, v, w} C).Faithful :=
  (pshRelEdgeGraphFullyFaithful
    (C := C)).faithful

/-- The boundary functor from the edge category
of presheaf relations to the product category
of presheaves. Sends each relation to its
source-target pair. -/
def pshRelBoundaryFunctor :
    PshRelEdge.{u, v, w} C ⥤
    (Cᵒᵖ ⥤ Type w) × (Cᵒᵖ ⥤ Type w) where
  obj R := (R.src, R.tgt)
  map f := (f.srcMap, f.tgtMap)
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The source functor from the edge category
of presheaf relations to the presheaf category.
Sends each relation to its source presheaf. -/
def pshRelSrcFunctor :
    PshRelEdge.{u, v, w} C ⥤
    (Cᵒᵖ ⥤ Type w) where
  obj R := R.src
  map f := f.srcMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The target functor from the edge category
of presheaf relations to the presheaf category.
Sends each relation to its target presheaf. -/
def pshRelTgtFunctor :
    PshRelEdge.{u, v, w} C ⥤
    (Cᵒᵖ ⥤ Type w) where
  obj R := R.tgt
  map f := f.tgtMap
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The identity section functor (Wadler's identity
extension) from the presheaf
category to the edge category of presheaf
relations. Sends each presheaf `P` to the
identity relation `pshRelId P`. -/
def pshRelIdentFunctor :
    (Cᵒᵖ ⥤ Type w) ⥤
    PshRelEdge.{u, v, w} C where
  obj P :=
    { src := P
      tgt := P
      edge := pshRelId P }
  map α :=
    { srcMap := α
      tgtMap := α
      sq := pshRelRelatedSqVertId α }
  map_id _ := VertEdgeHom.ext rfl rfl
  map_comp _ _ := VertEdgeHom.ext rfl rfl

/-- The identity section composed with the source
functor is the identity functor. -/
theorem pshRelIdentFunctor_src :
    pshRelIdentFunctor ⋙ pshRelSrcFunctor =
    (𝟭 (Cᵒᵖ ⥤ Type w) :
      (Cᵒᵖ ⥤ Type w) ⥤ _) :=
  rfl

/-- The identity section composed with the target
functor is the identity functor. -/
theorem pshRelIdentFunctor_tgt :
    pshRelIdentFunctor ⋙ pshRelTgtFunctor =
    (𝟭 (Cᵒᵖ ⥤ Type w) :
      (Cᵒᵖ ⥤ Type w) ⥤ _) :=
  rfl

/-- A relatedness square between identity
relations forces the two maps to be equal. -/
theorem pshRelRelated_id_eq
    {P Q : Cᵒᵖ ⥤ Type w}
    {α β : P ⟶ Q}
    (h : pshRelRelated α β
      (pshRelId P) (pshRelId Q)) :
    α = β := by
  ext c p
  exact h c p p rfl

/-- The identity section functor is fully
faithful. -/
def pshRelIdentFunctor_fullyFaithful :
    (pshRelIdentFunctor :
      (Cᵒᵖ ⥤ Type w) ⥤
        PshRelEdge.{u, v, w} C
    ).FullyFaithful where
  preimage h := h.srcMap
  map_preimage h :=
    VertEdgeHom.ext rfl
      (pshRelRelated_id_eq h.sq)
  preimage_map _ := rfl

/-- The Cartesian lift of a morphism
`(α, β) : (P', Q') ⟶ (R.src, R.tgt)` in the
product category along the boundary functor.
The domain is the preimage relation. -/
def pshRelCartesianLift
    (R : PshRelEdge.{u, v, w} C)
    {P' Q' : Cᵒᵖ ⥤ Type w}
    (α : P' ⟶ R.src) (β : Q' ⟶ R.tgt) :
    PshRelEdge.{u, v, w} C :=
  { src := P'
    tgt := Q'
    edge := pshRelPreimage R.edge α β }

/-- The morphism from the Cartesian lift to the
original edge, with components `α` and `β`. -/
def pshRelCartesianLiftHom
    (R : PshRelEdge.{u, v, w} C)
    {P' Q' : Cᵒᵖ ⥤ Type w}
    (α : P' ⟶ R.src) (β : Q' ⟶ R.tgt) :
    pshRelCartesianLift R α β ⟶ R :=
  { srcMap := α
    tgtMap := β
    sq := pshRelPreimage_related R.edge α β }

/-- The boundary functor maps the Cartesian lift
morphism to `(α, β)`. -/
theorem pshRelCartesianLiftHom_boundary
    (R : PshRelEdge.{u, v, w} C)
    {P' Q' : Cᵒᵖ ⥤ Type w}
    (α : P' ⟶ R.src) (β : Q' ⟶ R.tgt) :
    pshRelBoundaryFunctor.map
      (pshRelCartesianLiftHom R α β) =
    ((α, β) :
      (P', Q') ⟶
        (pshRelBoundaryFunctor.obj R :
          (Cᵒᵖ ⥤ Type w) × _)) :=
  rfl

private instance pshRelBoundaryIsHomLift
    (R : PshRelEdge.{u, v, w} C)
    {P' Q' : Cᵒᵖ ⥤ Type w}
    (α : P' ⟶ R.src) (β : Q' ⟶ R.tgt) :
    pshRelBoundaryFunctor.IsHomLift
      ((α, β) : (P', Q') ⟶
        pshRelBoundaryFunctor.obj R)
      (pshRelCartesianLiftHom R α β) := by
  apply IsHomLift.of_fac
  · rfl
  · rfl
  · simp [pshRelBoundaryFunctor]

instance : (pshRelBoundaryFunctor
    (C := C) :
    PshRelEdge.{u, v, w} C ⥤ _).IsPreFibered where
  exists_isCartesian' := by
    intro R PQ f
    refine ⟨pshRelCartesianLift R f.1 f.2,
      pshRelCartesianLiftHom R f.1 f.2,
      { toIsHomLift :=
          pshRelBoundaryIsHomLift R f.1 f.2
        universal_property := by
          intro S' φ' inst
          have hdom :
              pshRelBoundaryFunctor.obj S' =
              PQ :=
            Functor.IsHomLift.rec
              (motive := fun {R S a b}
                (_ : R ⟶ S) (_ : a ⟶ b) _ =>
                pshRelBoundaryFunctor.obj a = R)
              (fun _ => rfl) inst
          subst hdom
          have hmap_heq :
              HEq f
              (pshRelBoundaryFunctor.map φ') :=
            Functor.IsHomLift.rec
              (motive := fun {R S a b}
                (f : R ⟶ S) (φ : a ⟶ b) _ =>
                HEq f
                  (pshRelBoundaryFunctor.map φ))
              (fun _ => HEq.rfl) inst
          have hmap := eq_of_heq hmap_heq
          subst hmap
          let α := (pshRelBoundaryFunctor.map
            φ').1
          let β := (pshRelBoundaryFunctor.map
            φ').2
          let cart := pshRelCartesianLift R α β
          have hsq : pshRelRelated
              (𝟙 S'.src) (𝟙 S'.tgt)
              S'.edge cart.edge :=
            fun c _ _ hs =>
              pshRelPreimage_universal
                R.edge α β φ'.sq c hs
          let χ : S' ⟶ cart :=
            { srcMap := 𝟙 S'.src
              tgtMap := 𝟙 S'.tgt
              sq := hsq }
          refine ⟨χ, ⟨?_, ?_⟩, ?_⟩
          · exact Functor.IsHomLift.map
              (p := pshRelBoundaryFunctor) χ
          · exact VertEdgeHom.ext
              (Category.id_comp _)
              (Category.id_comp _)
          · intro y ⟨hy_lift, hy_comp⟩
            have hy_heq :
                HEq (𝟙
                  (pshRelBoundaryFunctor.obj
                    S'))
                (pshRelBoundaryFunctor.map y) :=
              Functor.IsHomLift.rec
                (motive := fun {R S a b}
                  (f : R ⟶ S)
                  (φ : a ⟶ b) _ =>
                  HEq f
                    (pshRelBoundaryFunctor.map
                      φ))
                (fun _ => HEq.rfl) hy_lift
            have hy_eq := eq_of_heq hy_heq
            have hsrc :
                y.srcMap = 𝟙 S'.src :=
              congrArg Prod.fst hy_eq.symm
            have htgt :
                y.tgtMap = 𝟙 S'.tgt :=
              congrArg Prod.snd hy_eq.symm
            exact VertEdgeHom.ext
              hsrc htgt }⟩

end PshRelEdgeCategory

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

set_option backward.isDefEq.respectTransparency false in
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

/-- The Barr extension on subfunctor-level
relations. Given `G : PSh(C) ⥤ PSh(C)` and
`R : PshRel P Q`, produces
`PshRel (G.obj P) (G.obj Q)` by applying
`pshBarrLift` to the Over object `Over.mk R.ι`
and projecting to a subfunctor via
`pshProdOverToRel`. -/
def pshBarrLiftRel
    {P Q : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (R : PshRel P Q) :
    PshRel (G.obj P) (G.obj Q) :=
  pshProdOverToRel
    (pshBarrLift G (Over.mk R.ι))

set_option backward.isDefEq.respectTransparency false in
/-- The range of `pshBarrLift G S` is contained
in `pshBarrLiftRel G (pshProdOverToRel S)`:
every element in the image of the Barr lift
is also in the Barr lift of the range. -/
theorem pshProdOverToRel_pshBarrLift_le
    {P Q : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (S : PshProdOver P Q) :
    pshProdOverToRel (pshBarrLift G S) ≤
      pshBarrLiftRel G
        (pshProdOverToRel S) := by
  simp only [pshBarrLiftRel, pshProdOverToRel]
  intro c x hx
  simp only [Subfunctor.range,
    Set.mem_range] at hx ⊢
  obtain ⟨w, hw⟩ := hx
  have hfact : S.hom =
      Subfunctor.toRange S.hom ≫
        (Subfunctor.range S.hom).ι :=
    (Subfunctor.toRange_ι S.hom).symm
  have hlift :
      (pshBarrLift G S).hom =
      G.map (Subfunctor.toRange S.hom) ≫
        (pshBarrLift G (Over.mk
          (Subfunctor.range S.hom).ι)
          ).hom := by
    apply pshProdPresheaf_hom_ext
    · simp only [pshBarrLift_fst,
        Category.assoc, pshBarrLift_fst]
      conv_lhs =>
        rw [hfact, Category.assoc]
      exact G.map_comp _ _
    · simp only [pshBarrLift_snd,
        Category.assoc, pshBarrLift_snd]
      conv_lhs =>
        rw [hfact, Category.assoc]
      exact G.map_comp _ _
  refine ⟨(G.map
    (Subfunctor.toRange S.hom)).app c w,
    ?_⟩
  have step := congr_fun
    (NatTrans.congr_app hlift c) w
  simp only [NatTrans.comp_app,
    types_comp_apply] at step
  exact step ▸ hw

/-- `pshBarrLiftRel G` is monotone with respect
to the `≤` ordering on subfunctors. -/
theorem pshBarrLiftRel_mono
    {P Q : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    {R S : PshRel P Q} (h : R ≤ S) :
    pshBarrLiftRel G R ≤
      pshBarrLiftRel G S := by
  simp only [pshBarrLiftRel, pshProdOverToRel]
  intro c x hx
  simp only [Subfunctor.range,
    Set.mem_range] at hx ⊢
  obtain ⟨w, hw⟩ := hx
  have hι : R.ι = Subfunctor.homOfLe h ≫
      S.ι := Subfunctor.homOfLe_ι h
  have hfst :
      G.map (R.ι ≫ pshProdFst P Q) =
      G.map (Subfunctor.homOfLe h) ≫
        G.map (S.ι ≫ pshProdFst P Q) := by
    rw [hι, Category.assoc, G.map_comp]
  have hsnd :
      G.map (R.ι ≫ pshProdSnd P Q) =
      G.map (Subfunctor.homOfLe h) ≫
        G.map (S.ι ≫ pshProdSnd P Q) := by
    rw [hι, Category.assoc, G.map_comp]
  have hlift :
      (pshBarrLift G (Over.mk R.ι)).hom =
      G.map (Subfunctor.homOfLe h) ≫
        (pshBarrLift G
          (Over.mk S.ι)).hom := by
    apply pshProdPresheaf_hom_ext
    · change G.map (R.ι ≫ pshProdFst P Q) =
        G.map (Subfunctor.homOfLe h) ≫
          G.map (S.ι ≫ pshProdFst P Q)
      exact hfst
    · change G.map (R.ι ≫ pshProdSnd P Q) =
        G.map (Subfunctor.homOfLe h) ≫
          G.map (S.ι ≫ pshProdSnd P Q)
      exact hsnd
  refine ⟨(G.map
    (Subfunctor.homOfLe h)).app c w, ?_⟩
  have step := congr_fun
    (NatTrans.congr_app hlift c) w
  simp only [NatTrans.comp_app,
    types_comp_apply] at step
  exact step ▸ hw

/-- The inclusion of a graph subfunctor composed
with the first projection is an isomorphism: the
graph of `α : P ⟶ Q` projects isomorphically
onto `P`. -/
def pshRelGraph_ι_fst_iso
    {P Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    (pshRelGraph α).toFunctor ≅ P where
  hom := (pshRelGraph α).ι ≫ pshProdFst P Q
  inv :=
    { app := fun c p =>
        ⟨(p, α.app c p), rfl⟩
      naturality := fun c d f => by
        ext p; apply Subtype.ext
        change (P.map f p,
            α.app d (P.map f p)) =
          (P.map f p,
            Q.map f (α.app c p))
        exact Prod.ext rfl
          (congr_fun
            (α.naturality f) p) }
  hom_inv_id := by
    ext c ⟨⟨p, q⟩, (h : α.app c p = q)⟩
    exact Subtype.ext
      (Prod.ext rfl h)
  inv_hom_id := by ext; rfl

/-- A natural transformation `α : P ⟶ Q` is
recovered from `pshRelGraph α` as the composite
of the inverse of the first-projection
isomorphism with the second projection. -/
theorem pshRelGraph_recover
    {P Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    (pshRelGraph_ι_fst_iso α).inv ≫
      ((pshRelGraph α).ι ≫
        pshProdSnd P Q) = α := by
  ext c p; rfl

/-- The inclusion of a graph subfunctor composed
with the second projection equals the first
projection composed with `α`. -/
theorem pshRelGraph_ι_snd
    {P Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    (pshRelGraph α).ι ≫ pshProdSnd P Q =
      ((pshRelGraph α).ι ≫
        pshProdFst P Q) ≫ α := by
  ext c ⟨⟨p, q⟩, (h : α.app c p = q)⟩
  exact h.symm

/-- Isomorphic Over objects have the same range
as subfunctors. -/
theorem pshProdOverToRel_iso
    {P Q : Cᵒᵖ ⥤ Type w}
    {R S : PshProdOver P Q}
    (α : R ≅ S) :
    pshProdOverToRel R =
      pshProdOverToRel S := by
  ext c x
  simp only [pshProdOverToRel,
    Subfunctor.range_obj, Set.mem_range]
  constructor
  · rintro ⟨r, hr⟩
    exact ⟨α.hom.left.app c r, by
      rw [← hr, ← NatTrans.congr_app
        (Over.w α.hom) c]
      rfl⟩
  · rintro ⟨s, hs⟩
    exact ⟨α.inv.left.app c s, by
      rw [← hs, ← NatTrans.congr_app
        (Over.w α.inv) c]
      rfl⟩

/-- The range of the graph Over object equals
the graph subfunctor. -/
theorem pshProdOverToRel_graph
    {P Q : Cᵒᵖ ⥤ Type w} (α : P ⟶ Q) :
    pshProdOverToRel (pshProdOverGraph α) =
      pshRelGraph α := by
  ext c ⟨p, q⟩
  simp only [pshProdOverToRel,
    pshProdOverGraph,
    Subfunctor.range_obj, Set.mem_range,
    pshRelGraph, Set.mem_setOf_eq,
    Over.mk_hom]
  constructor
  · rintro ⟨r, hr⟩
    have h1 := congr_arg Prod.fst hr
    have h2 := congr_arg Prod.snd hr
    dsimp [pshProdLift] at h1 h2
    rw [← h1, ← h2]
  · intro (h : α.app c p = q)
    exact ⟨p, by
      dsimp [pshProdLift]
      exact Prod.ext rfl h⟩

/-- The Barr extension of a graph relation
`pshRelGraph α` equals `pshRelGraph (G.map α)`.
This is the presheaf-level generalization of
Wadler's observation (Section 3.1) that
specializing `A*` to a function `a` gives
`map a`: the relation lifted along a graph
is the graph of the lifted function. -/
theorem pshBarrLiftRel_graph
    {P Q : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (α : P ⟶ Q) :
    pshBarrLiftRel G (pshRelGraph α) =
      pshRelGraph (G.map α) := by
  have hOverIso :
    Over.mk (pshRelGraph α).ι ≅
      pshProdOverGraph α :=
    Over.isoMk
      (pshRelGraph_ι_fst_iso α)
      (by
        ext c ⟨⟨p, q⟩,
          (h : α.app c p = q)⟩
        simp only [Over.mk_hom,
          pshProdOverGraph,
          pshRelGraph_ι_fst_iso,
          NatTrans.comp_app,
          types_comp_apply,
          Subfunctor.ι_app]
        exact Prod.ext rfl h)
  have hBarrIso :
    pshBarrLift G (pshProdOverGraph α) ≅
    pshProdOverGraph (G.map α) :=
    Over.isoMk (Iso.refl _) (by
      apply pshProdPresheaf_hom_ext
      · simp [pshBarrLift,
          pshProdOverGraph,
          pshProdLift, G.map_id]
      · simp [pshBarrLift,
          pshProdOverGraph,
          pshProdLift])
  rw [pshBarrLiftRel,
    pshProdOverToRel_iso
      ((pshBarrLift_iso G hOverIso).trans
        hBarrIso),
    pshProdOverToRel_graph]

/-- The second projection of the Barr extension
of a graph relation equals the first projection
composed with `G.map α`. This avoids the
dependent-type rewriting obstacle that arises
when applying `pshBarrLiftRel_graph`
to membership predicates. -/
theorem pshBarrLiftRel_graph_ι_snd
    {P Q : Cᵒᵖ ⥤ Type w}
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤
        (Cᵒᵖ ⥤ Type w))
    (α : P ⟶ Q) :
    (pshBarrLiftRel G
      (pshRelGraph α)).ι ≫
      pshProdSnd (G.obj P) (G.obj Q) =
    (pshBarrLiftRel G
      (pshRelGraph α)).ι ≫
      pshProdFst (G.obj P) (G.obj Q) ≫
        G.map α := by
  rw [pshBarrLiftRel_graph]
  exact pshRelGraph_ι_snd (G.map α)

/-- The Barr extension maps identity relations to
identity relations. -/
theorem pshBarrLiftRel_id
    {P : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :
    pshBarrLiftRel G (pshRelId P) =
      pshRelId (G.obj P) := by
  rw [← pshRelGraph_eq_id,
    pshBarrLiftRel_graph, G.map_id,
    pshRelGraph_eq_id]

set_option backward.isDefEq.respectTransparency false in
/-- The Barr extension through the identity
functor is the identity: `pshBarrLiftRel (𝟭 _)
R = R`. -/
@[simp]
theorem pshBarrLiftRel_functor_id
    {P Q : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) :
    pshBarrLiftRel (𝟭 _) R = R := by
  simp only [pshBarrLiftRel, pshBarrLift,
    CategoryTheory.Functor.id_map,
    pshProdOverToRel, Over.mk_hom,
    pshProdLift_fst_snd, Subfunctor.range_ι]

set_option backward.isDefEq.respectTransparency false in
theorem pshBarrLiftRel_mem_of_map
    {P Q : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤
         (Cᵒᵖ ⥤ Type w))
    (R : PshRel P Q)
    {c : Cᵒᵖ}
    (z : (G.obj R.toFunctor).obj c) :
    ((G.map (R.ι ≫ pshProdFst P Q)).app c z,
     (G.map (R.ι ≫ pshProdSnd P Q)).app c z)
      ∈ (pshBarrLiftRel G R).obj c := by
  simp only [pshBarrLiftRel, pshBarrLift,
    pshProdOverToRel, Subfunctor.range,
    Set.mem_range, Over.mk_hom]
  exact ⟨z, rfl⟩

set_option backward.isDefEq.respectTransparency false in
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

/-- `pshRelRelated` lifts to `PshProdOverRelated`
for the canonical Over objects. -/
theorem pshRelRelated_toPshProdOverRelated
    {P P' Q Q' : Cᵒᵖ ⥤ Type w}
    {α : P ⟶ Q} {β : P' ⟶ Q'}
    {R : PshRel P P'} {S : PshRel Q Q'}
    (h : pshRelRelated α β R S) :
    PshProdOverRelated (Over.mk R.ι)
      (Over.mk S.ι) α β := by
  refine ⟨{
    app := fun c x => ⟨(α.app c x.val.1,
      β.app c x.val.2), h c _ _ x.prop⟩
    naturality := fun c d f => by
      ext ⟨⟨p, p'⟩, hR⟩
      exact Subtype.ext
        (Prod.ext
          (congr_fun (α.naturality f) p)
          (congr_fun
            (β.naturality f) p')) },
    ?_⟩
  ext c ⟨⟨p, p'⟩, hR⟩
  exact Prod.ext rfl rfl

/-- `PshProdOverRelated` descends to
`pshRelRelated` on ranges. -/
theorem pshProdOverRelated_topshRelRelated
    {P P' Q Q' : Cᵒᵖ ⥤ Type w}
    {R : PshProdOver P P'}
    {S : PshProdOver Q Q'}
    {α : P ⟶ Q} {β : P' ⟶ Q'}
    (h : PshProdOverRelated R S α β) :
    pshRelRelated α β
      (pshProdOverToRel R)
      (pshProdOverToRel S) := by
  obtain ⟨φ, hφ⟩ := h
  intro c p p' ⟨r, hr⟩
  refine ⟨φ.app c r, ?_⟩
  have := congr_fun
    (NatTrans.congr_app hφ c) r
  simp only [NatTrans.comp_app,
    types_comp_apply] at this
  rw [this, hr]
  rfl

/-- The subfunctor-level version of
`pshBarrLift_related`: relatedness at the
`PshRel` level is preserved by
`pshBarrLiftRel`. -/
theorem pshBarrLiftRel_related
    {P P' Q Q' : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    {α : P ⟶ Q} {β : P' ⟶ Q'}
    {R : PshRel P P'} {S : PshRel Q Q'}
    (h : pshRelRelated α β R S) :
    pshRelRelated (G.map α) (G.map β)
      (pshBarrLiftRel G R)
      (pshBarrLiftRel G S) :=
  pshProdOverRelated_topshRelRelated
    (pshBarrLift_related G
      (pshRelRelated_toPshProdOverRelated
        h))

set_option backward.isDefEq.respectTransparency false in
/-- A natural endomorphism of `G` preserves
relatedness at every Barr-lifted relation.
Given `σ : G ⟶ G` and `R : PshRel P Q`,
if `(a, b) ∈ pshBarrLiftRel G R`, then
`(σ a, σ b) ∈ pshBarrLiftRel G R`.

The witness `w ∈ G(R)` mapping to `(a, b)` is
sent to `σ(w) ∈ G(R)`, which maps to
`(σ(a), σ(b))` by naturality of `σ` at the
projection morphisms `R.ι ≫ fst` and
`R.ι ≫ snd`. -/
theorem natTrans_pshRelRelated_barrLiftRel
    {P Q : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (σ : G ⟶ G)
    (R : PshRel P Q) :
    pshRelRelated (σ.app P) (σ.app Q)
      (pshBarrLiftRel G R)
      (pshBarrLiftRel G R) := by
  intro c a b hmem
  simp only [pshBarrLiftRel, pshBarrLift,
    pshProdOverToRel, Subfunctor.range,
    Set.mem_range, Over.mk_hom] at hmem ⊢
  obtain ⟨w, hw⟩ := hmem
  refine ⟨(σ.app R.toFunctor).app c w, ?_⟩
  have nf := congr_fun (congr_app
    (σ.naturality
      (R.ι ≫ pshProdFst P Q)) c) w
  have ns := congr_fun (congr_app
    (σ.naturality
      (R.ι ≫ pshProdSnd P Q)) c) w
  simp only [NatTrans.comp_app,
    types_comp_apply] at nf ns
  have hw₁ := congr_arg Prod.fst hw
  have hw₂ := congr_arg Prod.snd hw
  dsimp [pshProdLift,
    FunctorToTypes.prod] at hw₁ hw₂ ⊢
  exact Prod.ext
    (nf.symm.trans (congr_arg _ hw₁))
    (ns.symm.trans (congr_arg _ hw₂))

/-- Transport a `pshBarrLiftRel` along a
natural transformation `α : G ⟶ H`. Maps
each related pair `(x, y)` in the Barr lift
through `G` to `(α x, α y)` in the Barr lift
through `H`, using `α` on the witness. -/
def pshBarrLiftRelMap
    {P Q : Cᵒᵖ ⥤ Type w}
    {G H :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (α : G ⟶ H)
    (R : PshRel P Q) :
    (pshBarrLiftRel G R).toFunctor ⟶
      (pshBarrLiftRel H R).toFunctor :=
  Subfunctor.lift
    (pshProdLift
      ((pshBarrLiftRel G R).ι ≫
        pshProdFst (G.obj P) (G.obj Q) ≫
        α.app P)
      ((pshBarrLiftRel G R).ι ≫
        pshProdSnd (G.obj P) (G.obj Q) ≫
        α.app Q))
    (by
      intro c _ hx
      simp only [Subfunctor.range_obj,
        Set.mem_range] at hx ⊢
      obtain ⟨⟨pq, hpq⟩, heq⟩ := hx
      obtain ⟨w, hw⟩ := hpq
      simp only [pshBarrLiftRel,
        pshProdOverToRel,
        Subfunctor.range_obj,
        Set.mem_range]
      refine ⟨(α.app R.toFunctor).app c w,
        ?_⟩
      have hw₁ : (G.map (R.ι ≫
          pshProdFst P Q)).app c w = pq.1 :=
        congr_arg Prod.fst hw
      have hw₂ : (G.map (R.ι ≫
          pshProdSnd P Q)).app c w = pq.2 :=
        congr_arg Prod.snd hw
      rw [← heq]
      simp only [pshBarrLift, Over.mk,
        pshProdLift, FunctorToTypes.prod.lift,
        NatTrans.comp_app, types_comp_apply,
        pshBarrLiftRel, pshProdOverToRel,
        Subfunctor.range]
      apply Prod.ext
      · change (H.map (R.ι ≫
              pshProdFst P Q)).app c
            ((α.app R.toFunctor).app c w) =
          (α.app P).app c pq.1
        have nat := congr_fun
          (congr_app
            (α.naturality
              (R.ι ≫ pshProdFst P Q)) c) w
        simp only [NatTrans.comp_app,
          types_comp_apply] at nat
        rw [← nat, hw₁]
      · change (H.map (R.ι ≫
              pshProdSnd P Q)).app c
            ((α.app R.toFunctor).app c w) =
          (α.app Q).app c pq.2
        have nat := congr_fun
          (congr_app
            (α.naturality
              (R.ι ≫ pshProdSnd P Q)) c) w
        simp only [NatTrans.comp_app,
          types_comp_apply] at nat
        rw [← nat, hw₂])

@[simp]
theorem pshBarrLiftRelMap_id
    {P Q : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (R : PshRel P Q) :
    pshBarrLiftRelMap (𝟙 G) R =
      𝟙 (pshBarrLiftRel G R).toFunctor := by
  ext c ⟨x, hx⟩
  simp [pshBarrLiftRelMap, Subfunctor.lift,
    pshProdLift, FunctorToTypes.prod.lift]

@[simp]
theorem pshBarrLiftRelMap_ι_fst
    {P Q : Cᵒᵖ ⥤ Type w}
    {G H :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (α : G ⟶ H)
    (R : PshRel P Q) :
    pshBarrLiftRelMap α R ≫
      (pshBarrLiftRel H R).ι ≫
      pshProdFst (H.obj P) (H.obj Q) =
    (pshBarrLiftRel G R).ι ≫
      pshProdFst (G.obj P) (G.obj Q) ≫
      α.app P := by
  ext c ⟨x, hx⟩
  simp [pshBarrLiftRelMap, Subfunctor.lift,
    pshProdLift, FunctorToTypes.prod.lift]

@[simp]
theorem pshBarrLiftRelMap_ι_snd
    {P Q : Cᵒᵖ ⥤ Type w}
    {G H :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (α : G ⟶ H)
    (R : PshRel P Q) :
    pshBarrLiftRelMap α R ≫
      (pshBarrLiftRel H R).ι ≫
      pshProdSnd (H.obj P) (H.obj Q) =
    (pshBarrLiftRel G R).ι ≫
      pshProdSnd (G.obj P) (G.obj Q) ≫
      α.app Q := by
  ext c ⟨x, hx⟩
  simp [pshBarrLiftRelMap, Subfunctor.lift,
    pshProdLift, FunctorToTypes.prod.lift]

@[simp]
theorem pshBarrLiftRelMap_comp
    {P Q : Cᵒᵖ ⥤ Type w}
    {G H K :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (α : G ⟶ H) (β : H ⟶ K)
    (R : PshRel P Q) :
    pshBarrLiftRelMap (α ≫ β) R =
      pshBarrLiftRelMap α R ≫
        pshBarrLiftRelMap β R := by
  ext c ⟨x, hx⟩
  simp [pshBarrLiftRelMap, Subfunctor.lift,
    pshProdLift, FunctorToTypes.prod.lift]

/-- The Barr extension as an endofunctor on the
edge category `PshRelEdge C`. Given an endofunctor
`G` on `PSh(C)`, produces a functor on the edge
category that applies `G` to both source and target
presheaves and extends `G` to relations via
`pshBarrLiftRel`. -/
def pshBarrLiftEdgeFunctor
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :
    PshRelEdge.{u, v, w} C ⥤
    PshRelEdge.{u, v, w} C where
  obj R :=
    { src := G.obj R.src
      tgt := G.obj R.tgt
      edge := pshBarrLiftRel G R.edge }
  map f :=
    { srcMap := G.map f.srcMap
      tgtMap := G.map f.tgtMap
      sq := pshBarrLiftRel_related G f.sq }
  map_id R :=
    VertEdgeHom.ext
      (G.map_id R.src) (G.map_id R.tgt)
  map_comp f g :=
    VertEdgeHom.ext
      (G.map_comp f.srcMap g.srcMap)
      (G.map_comp f.tgtMap g.tgtMap)

end PshBarrExtension

section PshContraBarrExtension

/-- The contravariant Barr extension (pullback
relation). Given a contravariant endofunctor
`F : (PSh(C))ᵒᵖ ⥤ PSh(C)` and a relation
`R : PshRel P Q`, the pullback relation consists
of pairs `(a, b)` in `F.obj(op P) × F.obj(op Q)`
whose images in `F.obj(op R.toFunctor)` under the
two projection maps agree:
`F.map (R.ι ≫ pshProdFst P Q).op a =
 F.map (R.ι ≫ pshProdSnd P Q).op b`. -/
def pshContraBarrLiftRel
    {P Q : Cᵒᵖ ⥤ Type w}
    (F :
      (Cᵒᵖ ⥤ Type w)ᵒᵖ ⥤
        (Cᵒᵖ ⥤ Type w))
    (R : PshRel P Q) :
    PshRel (F.obj (Opposite.op P))
      (F.obj (Opposite.op Q)) where
  obj c :=
    { x |
      (F.map (R.ι ≫
        pshProdFst P Q).op).app c x.1 =
      (F.map (R.ι ≫
        pshProdSnd P Q).op).app c x.2 }
  map {c d} k := by
    intro ⟨a, b⟩ hx
    change (F.map (R.ι ≫
        pshProdFst P Q).op).app d
        ((F.obj (Opposite.op P)).map k a) =
      (F.map (R.ι ≫
        pshProdSnd P Q).op).app d
        ((F.obj (Opposite.op Q)).map k b)
    have h1 := congr_fun
      ((F.map (R.ι ≫
        pshProdFst P Q).op).naturality k) a
    have h2 := congr_fun
      ((F.map (R.ι ≫
        pshProdSnd P Q).op).naturality k) b
    simp only [types_comp_apply] at h1 h2
    rw [h1, h2, hx]

/-- Transport a `pshContraBarrLiftRel` along
a natural transformation `α : F ⟶ G` between
contravariant endofunctors. Maps each related
pair `(a, b)` in the pullback relation through
`F` to `(α a, α b)` in the pullback relation
through `G`, using naturality of `α`. -/
def pshContraBarrLiftRelMap
    {P Q : Cᵒᵖ ⥤ Type w}
    {F G :
      (Cᵒᵖ ⥤ Type w)ᵒᵖ ⥤
        (Cᵒᵖ ⥤ Type w)}
    (α : F ⟶ G)
    (R : PshRel P Q) :
    (pshContraBarrLiftRel F R).toFunctor ⟶
      (pshContraBarrLiftRel G R).toFunctor
    where
  app c x :=
    ⟨((α.app (Opposite.op P)).app c x.val.1,
      (α.app (Opposite.op Q)).app c x.val.2),
     by
      change (G.map (R.ι ≫
          pshProdFst P Q).op).app c
          ((α.app (Opposite.op P)).app c
            x.val.1) =
        (G.map (R.ι ≫
          pshProdSnd P Q).op).app c
          ((α.app (Opposite.op Q)).app c
            x.val.2)
      have nat₁ := congr_fun (congr_app
        (α.naturality
          (R.ι ≫ pshProdFst P Q).op) c)
        x.val.1
      have nat₂ := congr_fun (congr_app
        (α.naturality
          (R.ι ≫ pshProdSnd P Q).op) c)
        x.val.2
      simp only [NatTrans.comp_app,
        types_comp_apply] at nat₁ nat₂
      rw [← nat₁, ← nat₂, x.property]⟩
  naturality c d k := by
    ext ⟨⟨a, b⟩, _⟩
    simp only [types_comp_apply]
    apply Subtype.ext
    apply Prod.ext
    · exact congr_fun
        ((α.app (Opposite.op P)).naturality
          k) a
    · exact congr_fun
        ((α.app (Opposite.op Q)).naturality
          k) b

@[simp]
theorem pshContraBarrLiftRelMap_ι_fst
    {P Q : Cᵒᵖ ⥤ Type w}
    {F G :
      (Cᵒᵖ ⥤ Type w)ᵒᵖ ⥤
        (Cᵒᵖ ⥤ Type w)}
    (α : F ⟶ G)
    (R : PshRel P Q) :
    pshContraBarrLiftRelMap α R ≫
      (pshContraBarrLiftRel G R).ι ≫
      pshProdFst
        (G.obj (Opposite.op P))
        (G.obj (Opposite.op Q)) =
    (pshContraBarrLiftRel F R).ι ≫
      pshProdFst
        (F.obj (Opposite.op P))
        (F.obj (Opposite.op Q)) ≫
      α.app (Opposite.op P) := by
  ext c ⟨⟨_, _⟩, _⟩
  simp [pshContraBarrLiftRelMap,
    pshContraBarrLiftRel, pshProdFst,
    FunctorToTypes.prod.fst]

@[simp]
theorem pshContraBarrLiftRelMap_ι_snd
    {P Q : Cᵒᵖ ⥤ Type w}
    {F G :
      (Cᵒᵖ ⥤ Type w)ᵒᵖ ⥤
        (Cᵒᵖ ⥤ Type w)}
    (α : F ⟶ G)
    (R : PshRel P Q) :
    pshContraBarrLiftRelMap α R ≫
      (pshContraBarrLiftRel G R).ι ≫
      pshProdSnd
        (G.obj (Opposite.op P))
        (G.obj (Opposite.op Q)) =
    (pshContraBarrLiftRel F R).ι ≫
      pshProdSnd
        (F.obj (Opposite.op P))
        (F.obj (Opposite.op Q)) ≫
      α.app (Opposite.op Q) := by
  ext c ⟨⟨_, _⟩, _⟩
  simp [pshContraBarrLiftRelMap,
    pshContraBarrLiftRel, pshProdSnd,
    FunctorToTypes.prod.snd]

/-- The contravariant Barr lift of a graph
relation `pshRelGraph f` is the dagger of the
graph of `F.map f.op`. -/
theorem pshContraBarrLiftRel_graph
    {P Q : Cᵒᵖ ⥤ Type w}
    (F :
      (Cᵒᵖ ⥤ Type w)ᵒᵖ ⥤
        (Cᵒᵖ ⥤ Type w))
    (f : P ⟶ Q) :
    pshContraBarrLiftRel F (pshRelGraph f) =
      pshRelDagger
        (pshRelGraph (F.map f.op)) := by
  ext c ⟨a, b⟩
  let gIso := pshRelGraph_ι_fst_iso f
  let fst := (pshRelGraph f).ι ≫
    pshProdFst P Q
  let snd := (pshRelGraph f).ι ≫
    pshProdSnd P Q
  have hfst_eq : fst = gIso.hom := rfl
  have hsnd_eq : snd = fst ≫ f :=
    pshRelGraph_ι_snd f
  have hFsnd : F.map snd.op =
      F.map f.op ≫ F.map fst.op := by
    rw [hsnd_eq, op_comp, F.map_comp]
  have hinv : F.map fst.op ≫
      F.map gIso.inv.op = 𝟙 _ := by
    rw [← F.map_comp, ← op_comp,
      hfst_eq,
      (pshRelGraph_ι_fst_iso f).inv_hom_id,
      op_id, F.map_id]
  simp only [pshContraBarrLiftRel,
    pshRelDagger, Set.mem_setOf_eq]
  constructor
  · intro h
    have h' :
        (F.map fst.op).app c a =
        (F.map fst.op).app c
          ((F.map f.op).app c b) := by
      have := congr_fun
        (congr_app hFsnd c) b
      simp only [NatTrans.comp_app,
        types_comp_apply] at this
      rw [this] at h; exact h
    have hinvc :=
      congr_fun (congr_app hinv c)
    simp only [NatTrans.comp_app,
      types_comp_apply, NatTrans.id_app,
      types_id_apply] at hinvc
    change (F.map f.op).app c b = a
    rw [← hinvc a, ← hinvc
      ((F.map f.op).app c b)]
    exact congrArg
      ((F.map gIso.inv.op).app c) h'.symm
  · intro h
    have := congr_fun
      (congr_app hFsnd c) b
    simp only [NatTrans.comp_app,
      types_comp_apply] at this
    rw [this]
    exact congrArg
      ((F.map fst.op).app c) h.symm

theorem pshContraBarrLiftRel_graph_ι_fst
    {P Q : Cᵒᵖ ⥤ Type w}
    (F :
      (Cᵒᵖ ⥤ Type w)ᵒᵖ ⥤
        (Cᵒᵖ ⥤ Type w))
    (f : P ⟶ Q) :
    (pshContraBarrLiftRel F
      (pshRelGraph f)).ι ≫
      pshProdFst
        (F.obj (Opposite.op P))
        (F.obj (Opposite.op Q)) =
    ((pshContraBarrLiftRel F
      (pshRelGraph f)).ι ≫
      pshProdSnd
        (F.obj (Opposite.op P))
        (F.obj (Opposite.op Q))) ≫
        F.map f.op := by
  rw [pshContraBarrLiftRel_graph]
  ext c ⟨⟨_, _⟩, hpf⟩
  simp only [NatTrans.comp_app,
    types_comp_apply]
  dsimp [pshProdFst, pshProdSnd,
    FunctorToTypes.prod.fst,
    FunctorToTypes.prod.snd]
  exact hpf.symm

/-- The contravariant Barr extension maps the
identity relation to the identity relation:
`pshContraBarrLiftRel F (pshRelId P)
= pshRelId (F.obj (op P))`. -/
theorem pshContraBarrLiftRel_id
    {P : Cᵒᵖ ⥤ Type w}
    (F :
      (Cᵒᵖ ⥤ Type w)ᵒᵖ ⥤
        (Cᵒᵖ ⥤ Type w)) :
    pshContraBarrLiftRel F (pshRelId P) =
      pshRelId (F.obj (Opposite.op P)) := by
  rw [← pshRelGraph_eq_id,
    pshContraBarrLiftRel_graph]
  simp only [op_id, F.map_id,
    pshRelGraph_eq_id, pshRelDagger_id]

set_option backward.isDefEq.respectTransparency false in
/-- The contravariant Barr extension preserves
relatedness contravariantly: if `α` and `β`
carry `R`-related pairs to `S`-related pairs,
then `F.map α.op` and `F.map β.op` carry
`pshContraBarrLiftRel F S`-related pairs to
`pshContraBarrLiftRel F R`-related pairs.

Note the contravariance: the direction of both
the morphisms and the relations is flipped. -/
theorem pshContraBarrLiftRel_related
    {P P' Q Q' : Cᵒᵖ ⥤ Type w}
    (F :
      (Cᵒᵖ ⥤ Type w)ᵒᵖ ⥤
        (Cᵒᵖ ⥤ Type w))
    {α : P ⟶ Q} {β : P' ⟶ Q'}
    {R : PshRel P P'} {S : PshRel Q Q'}
    (h : pshRelRelated α β R S) :
    pshRelRelated
      (F.map α.op) (F.map β.op)
      (pshContraBarrLiftRel F S)
      (pshContraBarrLiftRel F R) := by
  obtain ⟨φ, hφ⟩ :=
    pshRelRelated_toPshProdOverRelated h
  change φ ≫ S.ι = R.ι ≫ pshProdMap α β at hφ
  have hfst : φ ≫ (S.ι ≫
      pshProdFst Q Q') =
      (R.ι ≫ pshProdFst P P') ≫ α := by
    simp only [← Category.assoc]
    rw [hφ, Category.assoc,
      pshProdMap_fst, Category.assoc]
  have hsnd : φ ≫ (S.ι ≫
      pshProdSnd Q Q') =
      (R.ι ≫ pshProdSnd P P') ≫ β := by
    simp only [← Category.assoc]
    rw [hφ, Category.assoc,
      pshProdMap_snd, Category.assoc]
  intro c a b hS
  change (F.map (R.ι ≫ pshProdFst P P').op).app
      c ((F.map α.op).app c a) =
    (F.map (R.ι ≫ pshProdSnd P P').op).app
      c ((F.map β.op).app c b)
  have comm_fst :
      α.op ≫ (R.ι ≫
        pshProdFst P P').op =
      (S.ι ≫ pshProdFst Q Q').op ≫
        φ.op := by
    rw [← op_comp, ← op_comp, hfst]
  have comm_snd :
      β.op ≫ (R.ι ≫
        pshProdSnd P P').op =
      (S.ι ≫ pshProdSnd Q Q').op ≫
        φ.op := by
    rw [← op_comp, ← op_comp, hsnd]
  have lhs_eq :
      (F.map (R.ι ≫ pshProdFst P P').op).app
        c ((F.map α.op).app c a) =
      (F.map φ.op).app c
        ((F.map (S.ι ≫
          pshProdFst Q Q').op).app c a) := by
    change (F.map α.op ≫
      F.map (R.ι ≫ pshProdFst P P').op).app
        c a = _
    rw [← F.map_comp, comm_fst, F.map_comp]
    rfl
  have rhs_eq :
      (F.map (R.ι ≫ pshProdSnd P P').op).app
        c ((F.map β.op).app c b) =
      (F.map φ.op).app c
        ((F.map (S.ι ≫
          pshProdSnd Q Q').op).app c b) := by
    change (F.map β.op ≫
      F.map (R.ι ≫ pshProdSnd P P').op).app
        c b = _
    rw [← F.map_comp, comm_snd, F.map_comp]
    rfl
  rw [lhs_eq, rhs_eq]
  exact congrArg
    ((F.map φ.op).app c) hS

/-- The contravariant Barr extension as a functor
from the opposite of the edge category
`PshRelEdge C` to `PshRelEdge C`. Given a
contravariant endofunctor `F` on `PSh(C)`, produces
a functor that applies `F` contravariantly to both
source and target presheaves and extends `F` to
relations via `pshContraBarrLiftRel`. -/
def pshContraBarrLiftEdgeFunctor
    (F :
      (Cᵒᵖ ⥤ Type w)ᵒᵖ ⥤
        (Cᵒᵖ ⥤ Type w)) :
    (PshRelEdge.{u, v, w} C)ᵒᵖ ⥤
    PshRelEdge.{u, v, w} C where
  obj R :=
    { src := F.obj (Opposite.op R.unop.src)
      tgt := F.obj (Opposite.op R.unop.tgt)
      edge :=
        pshContraBarrLiftRel F R.unop.edge }
  map f :=
    { srcMap := F.map f.unop.srcMap.op
      tgtMap := F.map f.unop.tgtMap.op
      sq :=
        pshContraBarrLiftRel_related
          F f.unop.sq }
  map_id R :=
    VertEdgeHom.ext
      (F.map_id (Opposite.op R.unop.src))
      (F.map_id (Opposite.op R.unop.tgt))
  map_comp f g :=
    VertEdgeHom.ext
      (F.map_comp
        f.unop.srcMap.op g.unop.srcMap.op)
      (F.map_comp
        f.unop.tgtMap.op g.unop.tgtMap.op)

end PshContraBarrExtension

section PshProfBarrExtension

def pshProfBarrLiftRel
    {P Q : Cᵒᵖ ⥤ Type w}
    (G :
      (Cᵒᵖ ⥤ Type w)ᵒᵖ ×
        (Cᵒᵖ ⥤ Type w) ⥤
        (Cᵒᵖ ⥤ Type w))
    (R : PshRel P Q) :
    PshRel (G.obj (Opposite.op P, P))
      (G.obj (Opposite.op Q, Q)) where
  obj c :=
    let RT := R.toFunctor
    let fst := R.ι ≫ pshProdFst P Q
    let snd := R.ι ≫ pshProdSnd P Q
    { x |
      ∃ (w : (G.obj
          (Opposite.op RT, RT)).obj c),
        (G.map ((𝟙 (Opposite.op RT), fst) :
            (Opposite.op RT, RT) ⟶
            (Opposite.op RT, P))).app c w =
        (G.map ((fst.op, 𝟙 P) :
            (Opposite.op P, P) ⟶
            (Opposite.op RT, P))).app c x.1 ∧
        (G.map ((𝟙 (Opposite.op RT), snd) :
            (Opposite.op RT, RT) ⟶
            (Opposite.op RT, Q))).app c w =
        (G.map ((snd.op, 𝟙 Q) :
            (Opposite.op Q, Q) ⟶
            (Opposite.op RT, Q))).app c x.2 }
  map {c d} k := by
    intro ⟨a, b⟩ ⟨w, hw₁, hw₂⟩
    let RT := R.toFunctor
    let fst := R.ι ≫ pshProdFst P Q
    let snd := R.ι ≫ pshProdSnd P Q
    change ∃ (w' : (G.obj
        (Opposite.op RT, RT)).obj d),
      (G.map ((𝟙 (Opposite.op RT), fst) :
          (Opposite.op RT, RT) ⟶
          (Opposite.op RT, P))).app d w' =
      (G.map ((fst.op, 𝟙 P) :
          (Opposite.op P, P) ⟶
          (Opposite.op RT, P))).app d
        ((G.obj (Opposite.op P, P)).map
          k a) ∧
      (G.map ((𝟙 (Opposite.op RT), snd) :
          (Opposite.op RT, RT) ⟶
          (Opposite.op RT, Q))).app d w' =
      (G.map ((snd.op, 𝟙 Q) :
          (Opposite.op Q, Q) ⟶
          (Opposite.op RT, Q))).app d
        ((G.obj (Opposite.op Q, Q)).map
          k b)
    refine ⟨(G.obj (Opposite.op RT,
      RT)).map k w, ?_, ?_⟩
    · have n1 := congr_fun
        ((G.map ((𝟙 (Opposite.op RT), fst) :
            (Opposite.op RT, RT) ⟶
            (Opposite.op RT, P))).naturality
          k) w
      have n2 := congr_fun
        ((G.map ((fst.op, 𝟙 P) :
            (Opposite.op P, P) ⟶
            (Opposite.op RT, P))).naturality
          k) a
      simp only [types_comp_apply] at n1 n2
      rw [n1, n2]; exact congrArg _ hw₁
    · have n1 := congr_fun
        ((G.map ((𝟙 (Opposite.op RT), snd) :
            (Opposite.op RT, RT) ⟶
            (Opposite.op RT, Q))).naturality
          k) w
      have n2 := congr_fun
        ((G.map ((snd.op, 𝟙 Q) :
            (Opposite.op Q, Q) ⟶
            (Opposite.op RT, Q))).naturality
          k) b
      simp only [types_comp_apply] at n1 n2
      rw [n1, n2]; exact congrArg _ hw₂

/-- Transport a `pshProfBarrLiftRel` along a
natural transformation `β : G ⟶ H` between
profunctor-valued endofunctors. Maps each related
pair `(a, b)` through `β` componentwise, with the
witness transported by `β.app (op R, R)`. -/
def pshProfBarrLiftRelMap
    {P Q : Cᵒᵖ ⥤ Type w}
    {G H :
      (Cᵒᵖ ⥤ Type w)ᵒᵖ ×
        (Cᵒᵖ ⥤ Type w) ⥤
        (Cᵒᵖ ⥤ Type w)}
    (β : G ⟶ H)
    (R : PshRel P Q) :
    (pshProfBarrLiftRel G R).toFunctor ⟶
      (pshProfBarrLiftRel H R).toFunctor
    where
  app c x :=
    let RT := R.toFunctor
    let fst := R.ι ≫ pshProdFst P Q
    let snd := R.ι ≫ pshProdSnd P Q
    ⟨((β.app (Opposite.op P, P)).app c
        x.val.1,
      (β.app (Opposite.op Q, Q)).app c
        x.val.2),
     by
      obtain ⟨w, hw₁, hw₂⟩ := x.property
      refine ⟨(β.app (Opposite.op RT,
        RT)).app c w, ?_, ?_⟩
      · change
          (H.map ((𝟙 (Opposite.op RT),
            fst) : (Opposite.op RT, RT) ⟶
            (Opposite.op RT, P))).app c
            ((β.app (Opposite.op RT,
              RT)).app c w) =
          (H.map ((fst.op, 𝟙 P) :
            (Opposite.op P, P) ⟶
            (Opposite.op RT, P))).app c
            ((β.app (Opposite.op P,
              P)).app c x.val.1)
        have nat₁ := congr_fun (congr_app
          (β.naturality
            ((𝟙 (Opposite.op RT), fst) :
              (Opposite.op RT, RT) ⟶
              (Opposite.op RT,
                P))).symm c) w
        have nat₂ := congr_fun (congr_app
          (β.naturality
            ((fst.op, 𝟙 P) :
              (Opposite.op P, P) ⟶
              (Opposite.op RT,
                P))).symm c) x.val.1
        simp only [NatTrans.comp_app,
          types_comp_apply] at nat₁ nat₂
        rw [nat₁, nat₂]
        exact congrArg _ hw₁
      · change
          (H.map ((𝟙 (Opposite.op RT),
            snd) : (Opposite.op RT, RT) ⟶
            (Opposite.op RT, Q))).app c
            ((β.app (Opposite.op RT,
              RT)).app c w) =
          (H.map ((snd.op, 𝟙 Q) :
            (Opposite.op Q, Q) ⟶
            (Opposite.op RT, Q))).app c
            ((β.app (Opposite.op Q,
              Q)).app c x.val.2)
        have nat₁ := congr_fun (congr_app
          (β.naturality
            ((𝟙 (Opposite.op RT), snd) :
              (Opposite.op RT, RT) ⟶
              (Opposite.op RT,
                Q))).symm c) w
        have nat₂ := congr_fun (congr_app
          (β.naturality
            ((snd.op, 𝟙 Q) :
              (Opposite.op Q, Q) ⟶
              (Opposite.op RT,
                Q))).symm c) x.val.2
        simp only [NatTrans.comp_app,
          types_comp_apply] at nat₁ nat₂
        rw [nat₁, nat₂]
        exact congrArg _ hw₂⟩
  naturality c d k := by
    ext ⟨⟨a, b⟩, _⟩
    simp only [types_comp_apply]
    apply Subtype.ext
    apply Prod.ext
    · exact congr_fun
        ((β.app (Opposite.op P, P)).naturality
          k) a
    · exact congr_fun
        ((β.app (Opposite.op Q, Q)).naturality
          k) b

@[simp]
theorem pshProfBarrLiftRelMap_ι_fst
    {P Q : Cᵒᵖ ⥤ Type w}
    {G H :
      (Cᵒᵖ ⥤ Type w)ᵒᵖ ×
        (Cᵒᵖ ⥤ Type w) ⥤
        (Cᵒᵖ ⥤ Type w)}
    (β : G ⟶ H)
    (R : PshRel P Q) :
    pshProfBarrLiftRelMap β R ≫
      (pshProfBarrLiftRel H R).ι ≫
      pshProdFst
        (H.obj (Opposite.op P, P))
        (H.obj (Opposite.op Q, Q)) =
    (pshProfBarrLiftRel G R).ι ≫
      pshProdFst
        (G.obj (Opposite.op P, P))
        (G.obj (Opposite.op Q, Q)) ≫
      β.app (Opposite.op P, P) := by
  ext c ⟨⟨_, _⟩, _⟩
  simp [pshProfBarrLiftRelMap,
    pshProfBarrLiftRel, pshProdFst,
    FunctorToTypes.prod.fst]

@[simp]
theorem pshProfBarrLiftRelMap_ι_snd
    {P Q : Cᵒᵖ ⥤ Type w}
    {G H :
      (Cᵒᵖ ⥤ Type w)ᵒᵖ ×
        (Cᵒᵖ ⥤ Type w) ⥤
        (Cᵒᵖ ⥤ Type w)}
    (β : G ⟶ H)
    (R : PshRel P Q) :
    pshProfBarrLiftRelMap β R ≫
      (pshProfBarrLiftRel H R).ι ≫
      pshProdSnd
        (H.obj (Opposite.op P, P))
        (H.obj (Opposite.op Q, Q)) =
    (pshProfBarrLiftRel G R).ι ≫
      pshProdSnd
        (G.obj (Opposite.op P, P))
        (G.obj (Opposite.op Q, Q)) ≫
      β.app (Opposite.op Q, Q) := by
  ext c ⟨⟨_, _⟩, _⟩
  simp [pshProfBarrLiftRelMap,
    pshProfBarrLiftRel, pshProdSnd,
    FunctorToTypes.prod.snd]

/-- The profunctor Barr extension maps the
identity relation to the identity relation:
`pshProfBarrLiftRel G (pshRelId P) =
pshRelId (G.obj (op P, P))`.

The proof uses the isomorphism
`pshRelIdIso : (pshRelId P).toFunctor ≅ P`
to show that: (1) both projections from the
diagonal are equal (`pshRelId_fst_eq_snd`),
collapsing the two witness conditions; (2) the
induced map `G.map (π.op, 𝟙)` is an
isomorphism, making the existential condition
equivalent to `a = b`. -/
theorem pshProfBarrLiftRel_id
    {P : Cᵒᵖ ⥤ Type w}
    (G :
      (Cᵒᵖ ⥤ Type w)ᵒᵖ ×
        (Cᵒᵖ ⥤ Type w) ⥤
        (Cᵒᵖ ⥤ Type w)) :
    pshProfBarrLiftRel G (pshRelId P) =
      pshRelId
        (G.obj (Opposite.op P, P)) := by
  have hfs := pshRelId_fst_eq_snd P
  have hσfst : (pshRelIdIso P).inv ≫
      ((pshRelId P).ι ≫ pshProdFst P P) =
      𝟙 P :=
    (pshRelIdIso P).inv_hom_id
  have hret :
      G.map ((((pshRelId P).ι ≫
          pshProdFst P P).op, 𝟙 P) :
        (Opposite.op P, P) ⟶
        (Opposite.op
          (pshRelId P).toFunctor, P)) ≫
      G.map (((pshRelIdIso P).inv.op,
          𝟙 P) :
        (Opposite.op
          (pshRelId P).toFunctor, P) ⟶
        (Opposite.op P, P)) = 𝟙 _ := by
    rw [← G.map_comp]
    have : ((((pshRelId P).ι ≫
          pshProdFst P P).op, 𝟙 P) :
        (Opposite.op P, P) ⟶
        (Opposite.op
          (pshRelId P).toFunctor, P)) ≫
      (((pshRelIdIso P).inv.op, 𝟙 P) :
        (Opposite.op
          (pshRelId P).toFunctor, P) ⟶
        (Opposite.op P, P)) =
      𝟙 (Opposite.op P, P) := by
      change (((pshRelId P).ι ≫
          pshProdFst P P).op ≫
        (pshRelIdIso P).inv.op,
        𝟙 P ≫ 𝟙 P) = (𝟙 _, 𝟙 _)
      rw [Category.comp_id, ← op_comp, hσfst,
        op_id]
    rw [this, G.map_id]
  ext c ⟨a, b⟩
  constructor
  · intro hmem
    change a = b
    obtain ⟨w, hw₁, hw₂⟩ := hmem
    rw [← pshRelId_fst_eq_snd P] at hw₂
    have heq := hw₁.symm.trans hw₂
    have ha := congr_fun (congr_app hret c) a
    have hb := congr_fun (congr_app hret c) b
    simp only [NatTrans.comp_app,
      NatTrans.id_app, types_comp_apply,
      types_id_apply] at ha hb
    rw [← ha, ← hb]
    exact congrArg _ heq
  · intro hmem
    have hmem' : a = b := hmem
    subst hmem'
    have hσsnd : (pshRelIdIso P).inv ≫
        ((pshRelId P).ι ≫ pshProdSnd P P) =
        𝟙 P := by
      rw [← hfs]; exact hσfst
    change ∃ (w : (G.obj
        (Opposite.op (pshRelId P).toFunctor,
          (pshRelId P).toFunctor)).obj c),
      (G.map ((𝟙 (Opposite.op
            (pshRelId P).toFunctor),
          (pshRelId P).ι ≫
            pshProdFst P P) :
          (Opposite.op
            (pshRelId P).toFunctor,
            (pshRelId P).toFunctor) ⟶
          (Opposite.op
            (pshRelId P).toFunctor,
            P))).app c w =
      (G.map ((((pshRelId P).ι ≫
            pshProdFst P P).op, 𝟙 P) :
          (Opposite.op P, P) ⟶
          (Opposite.op
            (pshRelId P).toFunctor,
            P))).app c a ∧
      (G.map ((𝟙 (Opposite.op
            (pshRelId P).toFunctor),
          (pshRelId P).ι ≫
            pshProdSnd P P) :
          (Opposite.op
            (pshRelId P).toFunctor,
            (pshRelId P).toFunctor) ⟶
          (Opposite.op
            (pshRelId P).toFunctor,
            P))).app c w =
      (G.map ((((pshRelId P).ι ≫
            pshProdSnd P P).op, 𝟙 P) :
          (Opposite.op P, P) ⟶
          (Opposite.op
            (pshRelId P).toFunctor,
            P))).app c a
    refine ⟨(G.map
        ((((pshRelId P).ι ≫
            pshProdFst P P).op,
          (pshRelIdIso P).inv) :
          (Opposite.op P, P) ⟶
          (Opposite.op
            (pshRelId P).toFunctor,
            (pshRelId P).toFunctor))).app
        c a,
      ?_, ?_⟩
    · have step := congr_fun (congr_app
        (show G.map
            ((((pshRelId P).ι ≫
                pshProdFst P P).op,
              (pshRelIdIso P).inv) :
              (Opposite.op P, P) ⟶
              (Opposite.op
                (pshRelId P).toFunctor,
                (pshRelId P).toFunctor)) ≫
          G.map
            ((𝟙 (Opposite.op
                (pshRelId P).toFunctor),
              (pshRelId P).ι ≫
                pshProdFst P P) :
              (Opposite.op
                (pshRelId P).toFunctor,
                (pshRelId P).toFunctor) ⟶
              (Opposite.op
                (pshRelId P).toFunctor,
                P)) =
          G.map
            ((((pshRelId P).ι ≫
                pshProdFst P P).op,
              𝟙 P) :
              (Opposite.op P, P) ⟶
              (Opposite.op
                (pshRelId P).toFunctor,
                P))
        from by
          rw [← G.map_comp]; congr 1)
        c) a
      simp only [NatTrans.comp_app,
        types_comp_apply] at step
      exact step
    · have step := congr_fun (congr_app
        (show G.map
            ((((pshRelId P).ι ≫
                pshProdFst P P).op,
              (pshRelIdIso P).inv) :
              (Opposite.op P, P) ⟶
              (Opposite.op
                (pshRelId P).toFunctor,
                (pshRelId P).toFunctor)) ≫
          G.map
            ((𝟙 (Opposite.op
                (pshRelId P).toFunctor),
              (pshRelId P).ι ≫
                pshProdSnd P P) :
              (Opposite.op
                (pshRelId P).toFunctor,
                (pshRelId P).toFunctor) ⟶
              (Opposite.op
                (pshRelId P).toFunctor,
                P)) =
          G.map
            ((((pshRelId P).ι ≫
                pshProdSnd P P).op,
              𝟙 P) :
              (Opposite.op P, P) ⟶
              (Opposite.op
                (pshRelId P).toFunctor,
                P))
        from by
          rw [← G.map_comp]; congr 1
          change (((pshRelId P).ι ≫
              pshProdFst P P).op ≫ 𝟙 _,
            (pshRelIdIso P).inv ≫
              ((pshRelId P).ι ≫
                pshProdSnd P P)) =
            (((pshRelId P).ι ≫
              pshProdSnd P P).op, 𝟙 P)
          rw [Category.comp_id, hσsnd,
            ← pshRelId_fst_eq_snd])
        c) a
      simp only [NatTrans.comp_app,
        types_comp_apply] at step
      exact step

end PshProfBarrExtension

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
`pshArrowRelOver R S` is a relation on the internal hom
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
`pshArrowRelOver R S` is a relation on the internal hom
presheaves `A₁.functorHom B₁` and
`A₂.functorHom B₂`. The underlying presheaf is
`pshArrowRelPresheaf R S` with projections given
by `.val.1` and `.val.2`. -/
def pshArrowRelOver
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
def pshArrowRelOver_iso
    {A₁ A₂ B₁ B₂ : Dᵒᵖ ⥤ Type (max u₁ v₁)}
    {R₁ R₂ : PshProdOver A₁ A₂}
    {S₁ S₂ : PshProdOver B₁ B₂}
    (α : R₁ ≅ R₂) (β : S₁ ≅ S₂) :
    pshArrowRelOver R₁ S₁ ≅
      pshArrowRelOver R₂ S₂ :=
  Over.isoMk (pshArrowRelPresheafIso α β)
    (by ext c g; rfl)

/-- The arrow relation on subfunctor-level
relations. Given `R : PshRel A₁ A₂` and
`S : PshRel B₁ B₂`, produces
`PshRel (A₁.functorHom B₁)
  (A₂.functorHom B₂)` by applying
`pshArrowRelOver` to the canonical Over objects
and projecting to a subfunctor. -/
def pshArrowRel
    {A₁ A₂ B₁ B₂ :
      Dᵒᵖ ⥤ Type (max u₁ v₁)}
    (R : PshRel A₁ A₂)
    (S : PshRel B₁ B₂) :
    PshRel (A₁.functorHom B₁)
      (A₂.functorHom B₂) :=
  pshProdOverToRel
    (pshArrowRelOver (Over.mk R.ι)
      (Over.mk S.ι))

/-- The arrow relation maps identity relations to
identity relations: when both input and output
relations are diagonals, the arrow relation is
the diagonal on the internal hom presheaf. -/
theorem pshArrowRel_id
    (A B : Dᵒᵖ ⥤ Type (max u₁ v₁)) :
    pshArrowRel (pshRelId A) (pshRelId B) =
      pshRelId (A.functorHom B) := by
  ext c ⟨f₁, f₂⟩
  simp only [pshArrowRel, pshProdOverToRel,
    Subfunctor.range, Set.mem_range,
    pshRelId]
  constructor
  · rintro ⟨⟨⟨g₁, g₂⟩, hg⟩, hpair⟩
    have hg₁ : g₁ = f₁ :=
      congr_arg Prod.fst hpair
    have hg₂ : g₂ = f₂ :=
      congr_arg Prod.snd hpair
    subst hg₁; subst hg₂
    ext d h a
    have hrel := hg d h ⟨(a, a), rfl⟩
    obtain ⟨⟨⟨b₁, b₂⟩, (hb : b₁ = b₂)⟩,
      hs⟩ := hrel
    simp only [Over.mk_hom,
      Subfunctor.ι_app] at hs
    have hfst := congr_arg Prod.fst hs
    have hsnd := congr_arg Prod.snd hs
    simp only at hfst hsnd
    rw [← hfst, ← hsnd]; exact hb
  · intro heq
    change f₁ = f₂ at heq; subst heq
    refine ⟨⟨⟨f₁, f₁⟩, fun d h w => ?_⟩, ?_⟩
    · exact ⟨⟨(f₁.app d h w.val.1,
        f₁.app d h w.val.1), rfl⟩,
        by simp only [Over.mk_hom,
             Subfunctor.ι_app]
           exact Prod.ext rfl
             (congrArg (f₁.app d h)
               w.property)⟩
    · rfl

set_option backward.isDefEq.respectTransparency false in
/-- Membership in the arrow relation at graph
relations: if `(g₁, g₂)` belong to
`pshArrowRel (pshRelGraph α) (pshRelGraph β)`,
then for all stages `d`, morphisms `f : c ⟶ d`,
and elements `x : A₁.obj d`, the equation
`β(g₁(f, x)) = g₂(f, α(x))` holds. -/
theorem pshArrowRel_graph_apply
    {A₁ A₂ B₁ B₂ :
      Dᵒᵖ ⥤ Type (max u₁ v₁)}
    {α : A₁ ⟶ A₂} {β : B₁ ⟶ B₂}
    {c : Dᵒᵖ}
    {g₁ : (A₁.functorHom B₁).obj c}
    {g₂ : (A₂.functorHom B₂).obj c}
    (h : (g₁, g₂) ∈
      (pshArrowRel (pshRelGraph α)
        (pshRelGraph β)).obj c)
    (d : Dᵒᵖ) (f : c ⟶ d)
    (x : A₁.obj d) :
    β.app d (g₁.app d f x) =
      g₂.app d f (α.app d x) := by
  simp only [pshArrowRel, pshProdOverToRel,
    Subfunctor.range, Set.mem_range] at h
  obtain ⟨⟨⟨a₁, a₂⟩, hpred⟩, heq⟩ := h
  have ha₁ : a₁ = g₁ :=
    congr_arg Prod.fst heq
  have ha₂ : a₂ = g₂ :=
    congr_arg Prod.snd heq
  subst ha₁; subst ha₂
  have hspec := hpred d f
    ⟨(x, α.app d x), rfl⟩
  obtain ⟨s, hs⟩ := hspec
  simp only [Over.mk_hom,
    Subfunctor.ι_app] at hs
  have hfst := congr_arg Prod.fst hs
  have hsnd := congr_arg Prod.snd hs
  simp only at hfst hsnd
  rw [← hfst, ← hsnd]; exact s.property

set_option backward.isDefEq.respectTransparency false in
/-- Introduction rule for membership in the arrow
relation between graph relations: a pair `(g₁, g₂)`
belongs to `pshArrowRel (pshRelGraph α)
(pshRelGraph β)` when applying `g₁` and `β` on
domain elements commutes with applying `α` and
`g₂`. This is the converse of
`pshArrowRel_graph_apply`. -/
theorem pshArrowRel_graph_intro
    {A₁ A₂ B₁ B₂ :
      Dᵒᵖ ⥤ Type (max u₁ v₁)}
    {α : A₁ ⟶ A₂} {β : B₁ ⟶ B₂}
    {c : Dᵒᵖ}
    {g₁ : (A₁.functorHom B₁).obj c}
    {g₂ : (A₂.functorHom B₂).obj c}
    (h : ∀ (d : Dᵒᵖ) (k : c ⟶ d)
      (x : A₁.obj d),
      β.app d (g₁.app d k x) =
        g₂.app d k (α.app d x)) :
    (g₁, g₂) ∈
      (pshArrowRel (pshRelGraph α)
        (pshRelGraph β)).obj c := by
  simp only [pshArrowRel, pshProdOverToRel,
    Subfunctor.range, Set.mem_range]
  refine ⟨⟨(g₁, g₂), fun d k w => ?_⟩, rfl⟩
  obtain ⟨⟨x, y⟩, (hxy : α.app d x = y)⟩ := w
  simp only [Over.mk_hom, Subfunctor.ι_app]
  refine ⟨⟨(g₁.app d k x, g₂.app d k y),
    ?_⟩, rfl⟩
  change β.app d (g₁.app d k x) = g₂.app d k y
  rw [h d k x, hxy]

set_option backward.isDefEq.respectTransparency false in
/-- Extraction rule for the arrow relation when
the codomain is a graph relation: given membership
in `pshArrowRel R (pshRelGraph β)` and a related
pair `(w₁, w₂) ∈ R`, applying `g₁` and `β` to
`w₁` equals applying `g₂` to `w₂`. -/
theorem pshArrowRel_graphCod_apply
    {A₁ A₂ B₁ B₂ :
      Dᵒᵖ ⥤ Type (max u₁ v₁)}
    {R : PshRel A₁ A₂}
    {β : B₁ ⟶ B₂}
    {c : Dᵒᵖ}
    {g₁ : (A₁.functorHom B₁).obj c}
    {g₂ : (A₂.functorHom B₂).obj c}
    (h : (g₁, g₂) ∈
      (pshArrowRel R
        (pshRelGraph β)).obj c)
    {d : Dᵒᵖ} (k : c ⟶ d)
    {w₁ : A₁.obj d} {w₂ : A₂.obj d}
    (hw : (w₁, w₂) ∈ R.obj d) :
    β.app d (g₁.app d k w₁) =
      g₂.app d k w₂ := by
  simp only [pshArrowRel, pshProdOverToRel,
    Subfunctor.range, Set.mem_range] at h
  obtain ⟨⟨⟨a₁, a₂⟩, hpred⟩, heq⟩ := h
  have ha₁ : a₁ = g₁ :=
    congr_arg Prod.fst heq
  have ha₂ : a₂ = g₂ :=
    congr_arg Prod.snd heq
  subst ha₁; subst ha₂
  have hspec := hpred d k ⟨(w₁, w₂), hw⟩
  obtain ⟨s, hs⟩ := hspec
  simp only [Over.mk_hom,
    Subfunctor.ι_app] at hs
  have hfst := congr_arg Prod.fst hs
  have hsnd := congr_arg Prod.snd hs
  simp only at hfst hsnd
  rw [← hfst, ← hsnd]; exact s.property

set_option backward.isDefEq.respectTransparency false in
theorem pshArrowRel_intro
    {A₁ A₂ B₁ B₂ :
      Dᵒᵖ ⥤ Type (max u₁ v₁)}
    {R : PshRel A₁ A₂}
    {S : PshRel B₁ B₂}
    {c : Dᵒᵖ}
    {g₁ : (A₁.functorHom B₁).obj c}
    {g₂ : (A₂.functorHom B₂).obj c}
    (h : ∀ (d : Dᵒᵖ) (k : c ⟶ d)
      (a₁ : A₁.obj d) (a₂ : A₂.obj d),
      (a₁, a₂) ∈ R.obj d →
      (g₁.app d k a₁, g₂.app d k a₂) ∈
        S.obj d) :
    (g₁, g₂) ∈
      (pshArrowRel R S).obj c := by
  simp only [pshArrowRel, pshProdOverToRel,
    Subfunctor.range, Set.mem_range]
  refine ⟨⟨(g₁, g₂), fun d k w => ?_⟩, rfl⟩
  simp only [Over.mk_hom, Subfunctor.ι_app]
  exact ⟨⟨(g₁.app d k w.val.1,
    g₂.app d k w.val.2),
    h d k w.val.1 w.val.2 w.property⟩,
    rfl⟩

set_option backward.isDefEq.respectTransparency false in
theorem pshArrowRel_apply
    {A₁ A₂ B₁ B₂ :
      Dᵒᵖ ⥤ Type (max u₁ v₁)}
    {R : PshRel A₁ A₂}
    {S : PshRel B₁ B₂}
    {c : Dᵒᵖ}
    {g₁ : (A₁.functorHom B₁).obj c}
    {g₂ : (A₂.functorHom B₂).obj c}
    (h : (g₁, g₂) ∈
      (pshArrowRel R S).obj c)
    {d : Dᵒᵖ} (k : c ⟶ d)
    {a₁ : A₁.obj d} {a₂ : A₂.obj d}
    (ha : (a₁, a₂) ∈ R.obj d) :
    (g₁.app d k a₁, g₂.app d k a₂) ∈
      S.obj d := by
  simp only [pshArrowRel, pshProdOverToRel,
    Subfunctor.range, Set.mem_range] at h
  obtain ⟨⟨⟨h₁, h₂⟩, hpred⟩, heq⟩ := h
  have hg₁ : h₁ = g₁ :=
    congr_arg Prod.fst heq
  have hg₂ : h₂ = g₂ :=
    congr_arg Prod.snd heq
  subst hg₁; subst hg₂
  have hspec :=
    hpred d k ⟨(a₁, a₂), ha⟩
  simp only [Over.mk_hom,
    Subfunctor.ι_app] at hspec
  obtain ⟨s, hs⟩ := hspec
  have hfst := congr_arg Prod.fst hs
  have hsnd := congr_arg Prod.snd hs
  simp only at hfst hsnd
  rw [← hfst, ← hsnd]
  exact s.property

/-- The range of `pshArrowRelOver R S` is contained
in `pshArrowRel (pshProdOverToRel R)
(pshProdOverToRel S)`. -/
theorem pshProdOverToRel_pshArrowRelOver_le
    {A₁ A₂ B₁ B₂ :
      Dᵒᵖ ⥤ Type (max u₁ v₁)}
    (R : PshProdOver A₁ A₂)
    (S : PshProdOver B₁ B₂) :
    pshProdOverToRel (pshArrowRelOver R S) ≤
      pshArrowRel
        (pshProdOverToRel R)
        (pshProdOverToRel S) := by
  simp only [pshArrowRel, pshProdOverToRel]
  intro c x hx
  simp only [Subfunctor.range,
    Set.mem_range] at hx ⊢
  obtain ⟨⟨g, hg⟩, hw⟩ := hx
  refine ⟨⟨g, fun d hd w' => ?_⟩, ?_⟩
  · obtain ⟨r, hr⟩ := w'.property
    obtain ⟨s, hs⟩ := hg d hd r
    have hw'1 : (R.hom.app d r).1 = w'.val.1 :=
      congr_arg Prod.fst hr
    have hw'2 : (R.hom.app d r).2 = w'.val.2 :=
      congr_arg Prod.snd hr
    rw [hw'1, hw'2] at hs
    exact ⟨⟨S.hom.app d s, ⟨s, rfl⟩⟩, hs⟩
  · exact hw

/-- The arrow relation on `pshProdOverToRel`s
equals the `pshProdOverToRel` of the arrow
relation: the predicate `pshArrowRelPred`
depends only on the ranges of the over-object
hom morphisms. -/
theorem pshArrowRel_pshProdOverToRel
    {A₁ A₂ B₁ B₂ :
      Dᵒᵖ ⥤ Type (max u₁ v₁)}
    (R : PshProdOver A₁ A₂)
    (S : PshProdOver B₁ B₂) :
    pshArrowRel
      (pshProdOverToRel R)
      (pshProdOverToRel S) =
      pshProdOverToRel (pshArrowRelOver R S) := by
  simp only [pshArrowRel, pshProdOverToRel]
  ext c x
  simp only [Subfunctor.range,
    Set.mem_range]
  constructor
  · rintro ⟨⟨g, hg⟩, hw⟩
    refine ⟨⟨g, fun d hd w => ?_⟩, hw⟩
    set w' : (Subfunctor.range R.hom
        ).toFunctor.obj d :=
      ⟨R.hom.app d w, ⟨w, rfl⟩⟩
    obtain ⟨s', hs'⟩ := hg d hd w'
    obtain ⟨s_inner, hs_inner⟩ :=
      s'.property
    exact ⟨s_inner, by
      rw [hs_inner]; exact hs'⟩
  · rintro ⟨⟨g, hg⟩, hw⟩
    refine ⟨⟨g, fun d hd w' => ?_⟩, hw⟩
    obtain ⟨r, hr⟩ := w'.property
    obtain ⟨s, hs⟩ := hg d hd r
    have hw'1 : (R.hom.app d r).1 = w'.val.1 :=
      congr_arg Prod.fst hr
    have hw'2 : (R.hom.app d r).2 = w'.val.2 :=
      congr_arg Prod.snd hr
    rw [hw'1, hw'2] at hs
    exact ⟨⟨S.hom.app d s, ⟨s, rfl⟩⟩, hs⟩

/-- The arrow relation preserves relatedness: if
the input morphisms `(α₁, α₂)` are
`(R₂, R₁)`-related (note the reversal from
contravariance) and the output morphisms
`(β₁, β₂)` are `(S₁, S₂)`-related, then
`pshIhomProfMap α₁ β₁` and
`pshIhomProfMap α₂ β₂` are
`(pshArrowRelOver R₁ S₁, pshArrowRelOver R₂ S₂)`-related.
-/
theorem pshArrowRelOver_related
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
      (pshArrowRelOver R₁ S₁)
      (pshArrowRelOver R₂ S₂)
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

/-- The arrow relation preserves relatedness
at the `PshRel` level. -/
theorem pshArrowRel_related
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
      (pshArrowRel R₁ S₁)
      (pshArrowRel R₂ S₂) :=
  pshProdOverRelated_topshRelRelated
    (pshArrowRelOver_related
      (pshRelRelated_toPshProdOverRelated
        hα)
      (pshRelRelated_toPshProdOverRelated
        hβ))

/-- Arrow relations compose: if `w₁, w₂` are
related by `pshArrowRel R₁ S₁` and `w₂, w₃` by
`pshArrowRel R₂ S₂`, then `w₁, w₃` are related
by `pshArrowRel (pshRelComp R₁ R₂)
(pshRelComp S₁ S₂)`.  The proof decomposes
`pshRelComp`-membership in the domain to
obtain an intermediate element, applies both
hypotheses, and composes the codomain
witnesses. -/
theorem pshArrowRel_comp
    {A₁ A₂ A₃ B₁ B₂ B₃ :
      Dᵒᵖ ⥤ Type (max u₁ v₁)}
    {R₁ : PshRel A₁ A₂}
    {R₂ : PshRel A₂ A₃}
    {S₁ : PshRel B₁ B₂}
    {S₂ : PshRel B₂ B₃}
    {c : Dᵒᵖ}
    {w₁ : (A₁.functorHom B₁).obj c}
    {w₂ : (A₂.functorHom B₂).obj c}
    {w₃ : (A₃.functorHom B₃).obj c}
    (h₁₂ : (w₁, w₂) ∈
      (pshArrowRel R₁ S₁).obj c)
    (h₂₃ : (w₂, w₃) ∈
      (pshArrowRel R₂ S₂).obj c) :
    (w₁, w₃) ∈
      (pshArrowRel (pshRelComp R₁ R₂)
        (pshRelComp S₁ S₂)).obj c := by
  apply pshArrowRel_intro
  intro d k a₁ a₃ hmem
  obtain ⟨a₂, hr₁, hr₂⟩ := hmem
  exact ⟨w₂.app d k a₂,
    pshArrowRel_apply h₁₂ k hr₁,
    pshArrowRel_apply h₂₃ k hr₂⟩

end PshInternalHom

section YonedaPreservesIhom

universe w₁

variable {D : Type w₁} [Category.{w₁} D]
variable [CartesianMonoidalCategory D]
  [MonoidalClosed D]
variable (A B : D)

open CartesianMonoidalCategory MonoidalClosed
open scoped MonoidalCategory

/-- Forward map: given a morphism
`e : X ⟶ (ihom A).obj B`, produce an element of
`(yoneda.obj A).functorHom (yoneda.obj B)` at
stage `op X`, using evaluation of the
exponential. -/
def pshIhomYonedaFwd
    {X : D} (e : X ⟶ (ihom A).obj B) :
    ((yoneda.obj A).functorHom
      (yoneda.obj B)).obj (Opposite.op X) :=
  { app := fun d h a =>
      lift a (h.unop ≫ e) ≫
        (ihom.ev A).app B
    naturality := fun {d d'} g h => by
      ext a
      simp only [types_comp_apply,
        yoneda_obj_map]
      rw [← Category.assoc, comp_lift]
      congr 1
      dsimp
      simp only [Category.assoc] }

/-- Backward map: given an element of
`(yoneda.obj A).functorHom (yoneda.obj B)` at
stage `op X`, produce a morphism
`X ⟶ (ihom A).obj B` by currying the evaluation
at the universal element. -/
def pshIhomYonedaInv
    {X : D}
    (f : ((yoneda.obj A).functorHom
      (yoneda.obj B)).obj (Opposite.op X)) :
    X ⟶ (ihom A).obj B :=
  curry
    (f.app (Opposite.op (A ⊗ X))
      (Quiver.Hom.op (snd A X)) (fst A X))

set_option backward.isDefEq.respectTransparency false in
/-- The presheaf
`(yoneda.obj A).functorHom (yoneda.obj B)` is
representable by `(ihom A).obj B`. -/
def pshIhomYonedaRepresentableBy :
    ((yoneda.obj A).functorHom
      (yoneda.obj B)).RepresentableBy
        ((ihom A).obj B) where
  homEquiv :=
    { toFun := pshIhomYonedaFwd A B
      invFun := pshIhomYonedaInv A B
      left_inv := fun e => by
        dsimp only [pshIhomYonedaInv,
          pshIhomYonedaFwd]
        simp only [Quiver.Hom.unop_op]
        rw [← Category.comp_id (fst A _),
          lift_fst_comp_snd_comp,
          MonoidalCategory.id_tensorHom,
          ← uncurry_eq]
        exact curry_uncurry e
      right_inv := fun f => by
        apply Functor.functorHom_ext
        intro d g
        ext a
        dsimp only [pshIhomYonedaFwd,
          pshIhomYonedaInv]
        rw [← lift_whiskerLeft]
        rw [Category.assoc, ← uncurry_eq,
          uncurry_curry]
        have hnat := congr_fun
          (f.naturality
            (Quiver.Hom.op (lift a g.unop))
            (Quiver.Hom.op (snd A _)))
          (fst A _)
        dsimp at hnat
        simp only [lift_fst, ← op_comp,
          lift_snd, Quiver.Hom.op_unop] at hnat
        exact hnat.symm
    }
  homEquiv_comp := fun f g => by
    apply Functor.functorHom_ext
    intro d h
    ext a
    change (pshIhomYonedaFwd A B (f ≫ g)).app
        d h a =
      (pshIhomYonedaFwd A B g).app d
        (f.op ≫ h) a
    dsimp [pshIhomYonedaFwd]
    simp only [Category.assoc]

/-- The Yoneda embedding preserves exponentials:
`yoneda.obj ((ihom A).obj B) ≅
(yoneda.obj A).functorHom (yoneda.obj B)`. -/
def pshIhomYonedaIso :
    yoneda.obj ((ihom A).obj B) ≅
      (yoneda.obj A).functorHom
        (yoneda.obj B) :=
  (pshIhomYonedaRepresentableBy A B).toIso

end YonedaPreservesIhom

section YonedaPreservesIhomULift

universe u₂ v₂

variable {D : Type u₂} [Category.{v₂} D]
variable [CartesianMonoidalCategory D]
  [MonoidalClosed D]
variable (A B : D)

open CartesianMonoidalCategory MonoidalClosed
open scoped MonoidalCategory

/-- Forward map for the ULift version: given
`⟨e⟩ : ULift (X ⟶ (ihom A).obj B)`, produce an
element of
`(yonedaULift A).functorHom (yonedaULift B)` at
stage `op X`. -/
def pshIhomYonedaULiftFwd
    {X : D}
    (e : ULift (X ⟶ (ihom A).obj B)) :
    ((yonedaULift A).functorHom
      (yonedaULift B)).obj (Opposite.op X) :=
  { app := fun d h a =>
      ⟨lift a.down (h.unop ≫ e.down) ≫
        (ihom.ev A).app B⟩
    naturality := fun {d d'} g h => by
      ext ⟨a⟩
      apply ULift.ext
      simp only [types_comp_apply,
        yonedaULift, Functor.comp_map,
        uliftFunctor_map, yoneda_obj_map]
      rw [← Category.assoc, comp_lift]
      congr 1
      dsimp
      simp only [Category.assoc] }

/-- Backward map for the ULift version: given an
element of
`(yonedaULift A).functorHom (yonedaULift B)` at
stage `op X`, produce `⟨e⟩ : ULift (X ⟶ _)` by
currying the evaluation at the universal element. -/
def pshIhomYonedaULiftInv
    {X : D}
    (f : ((yonedaULift A).functorHom
      (yonedaULift B)).obj (Opposite.op X)) :
    ULift (X ⟶ (ihom A).obj B) :=
  ⟨curry
    ((f.app (Opposite.op (A ⊗ X))
      (Quiver.Hom.op (snd A X))
      ⟨fst A X⟩).down)⟩

set_option backward.isDefEq.respectTransparency false in
/-- `pshIhomYonedaULiftInv ≫ pshIhomYonedaULiftFwd`
is the identity. -/
theorem pshIhomYonedaULift_left_inv
    {X : D}
    (e : ULift (X ⟶ (ihom A).obj B)) :
    pshIhomYonedaULiftInv A B
      (pshIhomYonedaULiftFwd A B e) = e := by
  apply ULift.ext
  dsimp only [pshIhomYonedaULiftInv,
    pshIhomYonedaULiftFwd]
  simp only [Quiver.Hom.unop_op]
  rw [← Category.comp_id (fst A _),
    lift_fst_comp_snd_comp,
    MonoidalCategory.id_tensorHom,
    ← uncurry_eq]
  exact curry_uncurry e.down

set_option backward.isDefEq.respectTransparency false in
/-- `pshIhomYonedaULiftFwd ≫ pshIhomYonedaULiftInv`
is the identity. -/
theorem pshIhomYonedaULift_right_inv
    {X : D}
    (f : ((yonedaULift A).functorHom
      (yonedaULift B)).obj (Opposite.op X)) :
    pshIhomYonedaULiftFwd A B
      (pshIhomYonedaULiftInv A B f) = f := by
  apply Functor.functorHom_ext
  intro d g
  ext ⟨a⟩
  apply ULift.ext
  dsimp only [pshIhomYonedaULiftFwd,
    pshIhomYonedaULiftInv]
  rw [← lift_whiskerLeft]
  rw [Category.assoc, ← uncurry_eq,
    uncurry_curry]
  have hnat := congr_fun
    (f.naturality
      (Quiver.Hom.op (lift a g.unop))
      (Quiver.Hom.op (snd A _)))
    ⟨fst A _⟩
  simp only [types_comp_apply] at hnat
  have hnat' := congrArg ULift.down hnat
  simp only [yonedaULift, Functor.comp_map,
    uliftFunctor_map, yoneda_obj_map] at hnat'
  convert hnat'.symm using 2
  simp [← op_comp, lift_snd]

/-- The Yoneda embedding preserves exponentials
(ULift version):
`yonedaULift ((ihom A).obj B) ≅
(yonedaULift A).functorHom (yonedaULift B)`. -/
def pshIhomYonedaULiftIso :
    yonedaULift ((ihom A).obj B) ≅
      (yonedaULift A).functorHom
        (yonedaULift B) :=
  NatIso.ofComponents
    (fun X => {
      hom := pshIhomYonedaULiftFwd A B
      inv := pshIhomYonedaULiftInv A B
      hom_inv_id := funext
        (pshIhomYonedaULift_left_inv A B)
      inv_hom_id := funext
        (pshIhomYonedaULift_right_inv A B) })
    (fun {X Y} f => funext fun ⟨e⟩ => by
      apply Functor.functorHom_ext
      intro d h
      ext ⟨a⟩
      apply ULift.ext
      dsimp [pshIhomYonedaULiftFwd,
        yonedaULift, Functor.functorHom,
        Functor.homObjFunctor,
        Functor.HomObj.map]
      simp only [Category.assoc])

end YonedaPreservesIhomULift

section BarrLiftComposition

/-!
## Barr lift and relation composition

The composition of presheaf relations can be
defined via existential quantification
(`pshRelComp`) or via a pullback (`pshProdOverComp`).
The two agree at the relation level.

The Barr extension `pshBarrLiftRel G` interacts
with relation composition via the pullback
structure of `pshProdOverComp`: the Barr lift of
the pullback-based composition maps into both
`pshBarrLiftRel G (pshRelComp R S)` and
`pshRelComp (pshBarrLiftRel G R)
  (pshBarrLiftRel G S)`.

Neither containment reverses in general:
`pshBarrLiftRel G (pshRelComp R S) ≤
  pshRelComp (pshBarrLiftRel G R)
    (pshBarrLiftRel G S)` requires decomposing
witnesses in `G((R;S).toFunctor)` into matched
pairs in `G(R.toFunctor)` and `G(S.toFunctor)`,
which needs a natural section of the epi from
the pullback presheaf to the composite relation
presheaf.  The reverse containment requires
combining matched pairs from `G(R.toFunctor)`
and `G(S.toFunctor)` into a single witness in
`G(pullback)`, which needs `G` to preserve the
pullback over `Q`.
-/

variable {C : Type u} [Category.{v} C]

/-- The range of the pullback-based composition
`pshProdOverComp` agrees with the existential-based
composition `pshRelComp`. -/
theorem pshProdOverToRel_comp
    {P Q W : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) (S : PshRel Q W) :
    pshProdOverToRel
      (pshProdOverComp
        (Over.mk R.ι) (Over.mk S.ι)) =
    pshRelComp R S := by
  ext c ⟨p, w'⟩
  simp only [pshProdOverToRel, Subfunctor.range,
    Set.mem_range, pshRelComp]
  constructor
  · rintro ⟨z, hz⟩
    set f := R.ι ≫ pshProdSnd P Q
    set g := S.ι ≫ pshProdFst Q W
    set r := (presheafPullbackFst f g).app c z
    set s := (presheafPullbackSnd f g).app c z
    have heq : f.app c r = g.app c s :=
      congr_fun (congr_app
        (presheafPullbackCondition f g) c) z
    simp only [f, g, NatTrans.comp_app,
      types_comp_apply] at heq
    have hp : (pshProdFst P Q).app c
        (R.ι.app c r) = p := by
      have h := congr_arg Prod.fst hz
      simp only [pshProdOverComp, Over.mk_hom,
        pshProdLift, FunctorToTypes.prod] at h
      exact h
    have hw : (pshProdSnd Q W).app c
        (S.ι.app c s) = w' := by
      have h := congr_arg Prod.snd hz
      simp only [pshProdOverComp, Over.mk_hom,
        pshProdLift, FunctorToTypes.prod] at h
      exact h
    refine ⟨(pshProdSnd P Q).app c
      (R.ι.app c r), ?_, ?_⟩
    · rw [← hp]
      change (R.ι.app c r) ∈ R.obj c
      exact r.prop
    · rw [heq, ← hw]
      change (S.ι.app c s) ∈ S.obj c
      exact s.prop
  · rintro ⟨q, hR, hS⟩
    exact ⟨⟨(⟨(p, q), hR⟩, ⟨(q, w'), hS⟩),
      rfl⟩, rfl⟩

/-- The Barr lift of the pullback-based composition
is contained in the Barr lift of the existential
composition: `pshBarrLift G (pshProdOverComp R S)`
has range in `pshBarrLiftRel G (pshRelComp R S)`.
This follows from the general containment
`pshProdOverToRel_pshBarrLift_le` and the equality
`pshProdOverToRel_comp`. -/
theorem pshBarrLift_comp_le_barrLiftRel_comp
    {P Q W : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (R : PshRel P Q) (S : PshRel Q W) :
    pshProdOverToRel
      (pshBarrLift G
        (pshProdOverComp
          (Over.mk R.ι) (Over.mk S.ι))) ≤
    pshBarrLiftRel G (pshRelComp R S) := by
  rw [← pshProdOverToRel_comp R S]
  exact pshProdOverToRel_pshBarrLift_le G
    (pshProdOverComp (Over.mk R.ι) (Over.mk S.ι))

set_option backward.isDefEq.respectTransparency false in
/-- The Barr lift of the pullback-based composition
is contained in the relational composition of
individual Barr lifts.  From a witness
`z ∈ G(R ×_Q S)`, the pullback projections yield
`G.map(pb_fst)(z) ∈ G(R.toFunctor)` and
`G.map(pb_snd)(z) ∈ G(S.toFunctor)` matching over
`G(Q)` via `presheafPullbackCondition`. -/
theorem pshBarrLift_comp_le_relComp_barrLiftRel
    {P Q W : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (R : PshRel P Q) (S : PshRel Q W) :
    pshProdOverToRel
      (pshBarrLift G
        (pshProdOverComp
          (Over.mk R.ι) (Over.mk S.ι))) ≤
    pshRelComp
      (pshBarrLiftRel G R)
      (pshBarrLiftRel G S) := by
  intro c ⟨a, b⟩ hmem
  simp only [pshProdOverToRel, Subfunctor.range,
    Set.mem_range] at hmem
  obtain ⟨z, hz⟩ := hmem
  set pb_f := R.ι ≫ pshProdSnd P Q
  set pb_g := S.ι ≫ pshProdFst Q W
  -- Witnesses for Barr lift membership
  set wR :=
    (G.map (presheafPullbackFst pb_f pb_g)).app
      c z with hwR
  set wS :=
    (G.map (presheafPullbackSnd pb_f pb_g)).app
      c z with hwS
  -- Extract component equalities from hz
  have ha := congr_arg Prod.fst hz
  dsimp [pshBarrLift,
    FunctorToTypes.prod.lift] at ha
  simp only [pshProdOverComp, Over.mk_hom,
    FunctorToTypes.prod.lift_fst] at ha
  have hb := congr_arg Prod.snd hz
  dsimp [pshBarrLift,
    FunctorToTypes.prod.lift] at hb
  simp only [pshProdOverComp, Over.mk_hom,
    FunctorToTypes.prod.lift_snd] at hb
  refine ⟨(G.map (R.ι ≫ pshProdSnd P Q)).app
    c wR, ?_, ?_⟩
  · -- (a, q) ∈ pshBarrLiftRel G R
    rw [show a = (G.map (R.ι ≫
        pshProdFst P Q)).app c wR from by
      rw [hwR, ← ha]
      simp only [G.map_comp, NatTrans.comp_app,
        types_comp_apply]; rfl]
    exact pshBarrLiftRel_mem_of_map G R wR
  · -- (q, b) ∈ pshBarrLiftRel G S
    rw [show b = (G.map (S.ι ≫
        pshProdSnd Q W)).app c wS from by
      rw [hwS, ← hb]
      simp only [G.map_comp, NatTrans.comp_app,
        types_comp_apply]; rfl]
    rw [show (G.map (R.ι ≫ pshProdSnd P Q)).app
        c wR =
      (G.map (S.ι ≫ pshProdFst Q W)).app
        c wS from by
      rw [hwR, hwS]
      have comm := congr_arg
        (fun f => (G.map f).app c z)
        (presheafPullbackCondition pb_f pb_g)
      simp only [G.map_comp, NatTrans.comp_app,
        types_comp_apply] at comm
      exact comm]
    exact pshBarrLiftRel_mem_of_map G S wS

/-- The pullback-based composition lifts into
the `toFunctor` of the relational composition:
every matching pair `(r, s)` in the pullback
yields a pair in `(pshRelComp R S).toFunctor`. -/
def pullbackToRelCompFunctor
    {P Q W : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) (S : PshRel Q W) :
    presheafPullback
      (R.ι ≫ pshProdSnd P Q)
      (S.ι ≫ pshProdFst Q W) ⟶
    (pshRelComp R S).toFunctor :=
  Subfunctor.lift
    (pshProdLift
      (presheafPullbackFst
        (R.ι ≫ pshProdSnd P Q)
        (S.ι ≫ pshProdFst Q W) ≫
        R.ι ≫ pshProdFst P Q)
      (presheafPullbackSnd
        (R.ι ≫ pshProdSnd P Q)
        (S.ι ≫ pshProdFst Q W) ≫
        S.ι ≫ pshProdSnd Q W))
    (by
      rw [← pshProdOverToRel_comp R S]
      simp only [pshProdOverToRel,
        pshProdOverComp, Over.mk_hom]
      exact le_refl _)

set_option backward.isDefEq.respectTransparency false in
/-- The composition `pullbackToRelCompFunctor ≫
(pshRelComp R S).ι` equals the hom of
`pshProdOverComp`. -/
@[simp]
theorem pullbackToRelCompFunctor_ι
    {P Q W : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) (S : PshRel Q W) :
    pullbackToRelCompFunctor R S ≫
      (pshRelComp R S).ι =
    (pshProdOverComp
      (Over.mk R.ι) (Over.mk S.ι)).hom := by
  simp only [pullbackToRelCompFunctor,
    pshProdOverComp, Over.mk_hom,
    Subfunctor.lift_ι]

set_option backward.isDefEq.respectTransparency false in
/-- If `G` preserves pullbacks, the relational
composition of Barr lifts is contained in the Barr
lift of the relational composition. Together with
`pshBarrLift_comp_le_barrLiftRel_comp` and
`pshBarrLift_comp_le_relComp_barrLiftRel`, this
yields the containment chain
`pshProdOverToRel (pshBarrLift G (comp R S))
≤ pshRelComp (pshBarrLiftRel G R)
            (pshBarrLiftRel G S)
≤ pshBarrLiftRel G (pshRelComp R S)`.
See `barrLiftRel_comp_chain`. -/
theorem relComp_barrLiftRel_le_of_preservesPullbacks
    {P Q W : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    [PreservesLimitsOfShape WalkingCospan G]
    (R : PshRel P Q) (S : PshRel Q W) :
    pshRelComp
      (pshBarrLiftRel G R)
      (pshBarrLiftRel G S) ≤
    pshBarrLiftRel G (pshRelComp R S) := by
  intro c ⟨a, b⟩ hmem
  simp only [pshRelComp] at hmem
  obtain ⟨q, hR, hS⟩ := hmem
  -- Unpack Barr lift membership as range elements
  simp only [pshBarrLiftRel, pshProdOverToRel,
    Subfunctor.range, Set.mem_range] at hR hS ⊢
  obtain ⟨wR, hwR⟩ := hR
  obtain ⟨wS, hwS⟩ := hS
  -- Set up the pullback morphisms
  set pb_f := R.ι ≫ pshProdSnd P Q
  set pb_g := S.ι ≫ pshProdFst Q W
  -- The matching condition: wR and wS agree
  -- over G(Q) via pb_f and pb_g
  have hmatch :
      (G.map pb_f).app c wR =
      (G.map pb_g).app c wS := by
    have haR := congr_arg Prod.snd hwR
    have haS := congr_arg Prod.fst hwS
    dsimp [pshBarrLift,
      FunctorToTypes.prod.lift] at haR haS
    rw [haR, haS]
  -- Compose G with evaluation at c to get
  -- a functor (Cᵒᵖ ⥤ Type w) ⥤ Type w that
  -- preserves pullbacks (via comp_preserves...
  -- and evaluation_preserves...)
  set Gc := G ⋙
    (evaluation Cᵒᵖ (Type w)).obj c with hGc_def
  haveI : HasLimitsOfShape WalkingCospan
      (Type w) := inferInstance
  have hGc_lim :=
    isLimitOfPreserves Gc
      (presheafPullbackIsLimit pb_f pb_g)
  -- Transport the limit across cospanCompIso,
  -- which bridges cospan pb_f pb_g ⋙ Gc and
  -- cospan (Gc.map pb_f) (Gc.map pb_g)
  have hGc_post :=
    (IsLimit.postcomposeHomEquiv
      (cospanCompIso Gc pb_f pb_g) _).symm
      hGc_lim
  -- Build a cone from the compatible pair
  let unitCone : PullbackCone
      (Gc.map pb_f) (Gc.map pb_g) :=
    PullbackCone.mk
      (fun (_ : PUnit) => wR)
      (fun (_ : PUnit) => wS)
      (funext fun _ => hmatch)
  -- Lift through the limit
  let z := hGc_post.lift unitCone PUnit.unit
  -- Extract the projection properties of z
  -- from the limit lift factorization
  have hfst :
      Gc.map (presheafPullbackFst pb_f pb_g)
        z = wR := by
    have hfac := congr_fun
      (hGc_post.fac unitCone
        WalkingCospan.left) PUnit.unit
    simp only [types_comp_apply,
      Functor.mapCone_π_app,
      Cone.postcompose_obj_π,
      NatTrans.comp_app,
      cospanCompIso_hom_app_left,
      Category.comp_id] at hfac
    exact hfac
  have hsnd :
      Gc.map (presheafPullbackSnd pb_f pb_g)
        z = wS := by
    have hfac := congr_fun
      (hGc_post.fac unitCone
        WalkingCospan.right) PUnit.unit
    simp only [types_comp_apply,
      Functor.mapCone_π_app,
      Cone.postcompose_obj_π,
      NatTrans.comp_app,
      cospanCompIso_hom_app_right,
      Category.comp_id] at hfac
    exact hfac
  -- Extract component equalities from hwR, hwS
  have hwR_fst :
      (G.map (R.ι ≫ pshProdFst P Q)).app c
        wR = a := by
    have := congr_arg Prod.fst hwR
    dsimp [pshBarrLift,
      FunctorToTypes.prod.lift] at this
    exact this
  have hwS_snd :
      (G.map (S.ι ≫ pshProdSnd Q W)).app c
        wS = b := by
    have := congr_arg Prod.snd hwS
    dsimp [pshBarrLift,
      FunctorToTypes.prod.lift] at this
    exact this
  refine ⟨(G.map (pullbackToRelCompFunctor R S)
    ).app c z, ?_⟩
  apply Prod.ext
  · dsimp [pshBarrLift, FunctorToTypes.prod.lift]
    change (G.map (pullbackToRelCompFunctor R S) ≫
      G.map (Subfunctor.ι (pshRelComp R S) ≫
        pshProdFst P W)).app c z = a
    rw [← G.map_comp, ← Category.assoc,
      pullbackToRelCompFunctor_ι,
      pshProdOverComp_fst]
    change Gc.map
      (presheafPullbackFst pb_f pb_g ≫
        R.ι ≫ pshProdFst P Q) z = a
    rw [Gc.map_comp, types_comp_apply, hfst]
    exact hwR_fst
  · dsimp [pshBarrLift, FunctorToTypes.prod.lift]
    change (G.map (pullbackToRelCompFunctor R S) ≫
      G.map (Subfunctor.ι (pshRelComp R S) ≫
        pshProdSnd P W)).app c z = b
    rw [← G.map_comp, ← Category.assoc,
      pullbackToRelCompFunctor_ι,
      pshProdOverComp_snd]
    change Gc.map
      (presheafPullbackSnd pb_f pb_g ≫
        S.ι ≫ pshProdSnd Q W) z = b
    rw [Gc.map_comp, types_comp_apply, hsnd]
    exact hwS_snd

/-- If `G` is a right adjoint, the relational
composition of Barr lifts is contained in the Barr
lift of the relational composition.  This follows
from `relComp_barrLiftRel_le_of_preservesPullbacks`
since right adjoints preserve all limits, in
particular pullbacks
(`Adjunction.rightAdjoint_preservesLimits`). -/
theorem relComp_barrLiftRel_le_of_rightAdjoint
    {P Q W : Cᵒᵖ ⥤ Type w}
    {F : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    {G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (adj : F ⊣ G)
    (R : PshRel P Q) (S : PshRel Q W) :
    pshRelComp
      (pshBarrLiftRel G R)
      (pshBarrLiftRel G S) ≤
    pshBarrLiftRel G (pshRelComp R S) :=
  haveI := adj.rightAdjoint_preservesLimits
  relComp_barrLiftRel_le_of_preservesPullbacks
    G R S

/-- When `G` preserves pullbacks, the witnessed
Barr lift of the pullback-based composition, the
relational composition of individual Barr lifts,
and the Barr lift of the relational composition
form a chain of containments:

```text
pshProdOverToRel (pshBarrLift G (comp R S))
  ≤ pshRelComp (pshBarrLiftRel G R)
              (pshBarrLiftRel G S)
  ≤ pshBarrLiftRel G (pshRelComp R S)
```

The first containment is
`pshBarrLift_comp_le_relComp_barrLiftRel`
(no conditions on `G`); the second is
`relComp_barrLiftRel_le_of_preservesPullbacks`
(pullback preservation).

The outer containment
`pshProdOverToRel (...) ≤ pshBarrLiftRel G (...)`
also follows unconditionally from
`pshBarrLift_comp_le_barrLiftRel_comp`. -/
theorem barrLiftRel_comp_chain
    {P Q W : Cᵒᵖ ⥤ Type w}
    (G : (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    [PreservesLimitsOfShape WalkingCospan G]
    (R : PshRel P Q) (S : PshRel Q W) :
    pshProdOverToRel
      (pshBarrLift G
        (pshProdOverComp
          (Over.mk R.ι) (Over.mk S.ι))) ≤
    pshRelComp
      (pshBarrLiftRel G R)
      (pshBarrLiftRel G S) ∧
    pshRelComp
      (pshBarrLiftRel G R)
      (pshBarrLiftRel G S) ≤
    pshBarrLiftRel G (pshRelComp R S) :=
  ⟨pshBarrLift_comp_le_relComp_barrLiftRel G R S,
   relComp_barrLiftRel_le_of_preservesPullbacks
     G R S⟩

end BarrLiftComposition

section BarrLiftDoubleFunctor

/-!
## Barr extension as lax double functor

The Barr extension `pshBarrLiftRel G` together
with `G.map` on horizontal morphisms defines the
combinatorial data of a double endofunctor on the
presheaf relation double category.  The identity
and horizontal composition laws hold strictly, as
does the square map.  Vertical composition is
preserved only up to containment (`≤`), making
this a lax double functor in the direction

```text
  pshRelComp (pshBarrLiftRel G R)
             (pshBarrLiftRel G S)
    ≤ pshBarrLiftRel G (pshRelComp R S)
```

(when `G` preserves pullbacks).

The reverse containment would require `G` to
preserve the surjection
`pullbackToRelCompFunctor`, which right adjoints
do not do in general.
-/

variable {C : Type u} [Category.{v} C]

/-- The four mapping components of the Barr
extension double functor: objects via `G.obj`,
vertical relations via `pshBarrLiftRel G`,
horizontal morphisms via `G.map`, and squares
via `pshBarrLiftRel_related G`. -/
def pshBarrLiftDoubleFunctorOps
    (G : (Cᵒᵖ ⥤ Type w) ⥤
         (Cᵒᵖ ⥤ Type w)) :
    DoubleFunctorOps
      PshRel
      (homSetOfQuiver (Cᵒᵖ ⥤ Type w))
      pshRelSQS
      PshRel
      (homSetOfQuiver (Cᵒᵖ ⥤ Type w))
      pshRelSQS where
  objMap := G.obj
  vertMap := pshBarrLiftRel G
  horMap := G.map
  sqMap := pshBarrLiftRel_related G

/-- The Barr extension preserves vertical
identity relations:
`pshBarrLiftRel G (pshRelId P) = pshRelId (G.obj P)`.
-/
theorem pshBarrLiftDF_preservesVId
    (G : (Cᵒᵖ ⥤ Type w) ⥤
         (Cᵒᵖ ⥤ Type w)) :
    DFPreservesVId
      pshRelDoubleOps pshRelDoubleOps
      (pshBarrLiftDoubleFunctorOps G) :=
  fun _ => pshBarrLiftRel_id G

/-- The Barr extension preserves horizontal
identity morphisms: `G.map (𝟙 P) = 𝟙 (G.obj P)`.
-/
theorem pshBarrLiftDF_preservesHId
    (G : (Cᵒᵖ ⥤ Type w) ⥤
         (Cᵒᵖ ⥤ Type w)) :
    DFPreservesHId
      pshRelDoubleOps pshRelDoubleOps
      (pshBarrLiftDoubleFunctorOps G) :=
  fun _ => G.map_id _

/-- The Barr extension preserves horizontal
composition: `G.map (α ≫ β) = G.map α ≫ G.map β`.
-/
theorem pshBarrLiftDF_preservesHComp
    (G : (Cᵒᵖ ⥤ Type w) ⥤
         (Cᵒᵖ ⥤ Type w)) :
    DFPreservesHComp
      pshRelDoubleOps pshRelDoubleOps
      (pshBarrLiftDoubleFunctorOps G) :=
  fun α β => G.map_comp α β

set_option backward.isDefEq.respectTransparency false in
/-- A natural transformation `σ : F ⟶ G`
between presheaf endofunctors gives a relatedness
square between Barr lifts: `(σ.app P, σ.app Q)`
is `(pshBarrLiftRel F R, pshBarrLiftRel G R)`-
related for any `R : PshRel P Q`.  The witness
in `F(R.toFunctor)` is sent to
`G(R.toFunctor)` via `σ.app R.toFunctor`, and
naturality of `σ` at the projection morphisms
gives the component equalities.

This generalizes `natTrans_pshRelRelated_barrLiftRel`
from endomorphisms `σ : G ⟶ G` to arbitrary
natural transformations `σ : F ⟶ G`. -/
theorem natTrans_barrLiftRel_related
    {P Q : Cᵒᵖ ⥤ Type w}
    {F G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (σ : F ⟶ G)
    (R : PshRel P Q) :
    pshRelRelated (σ.app P) (σ.app Q)
      (pshBarrLiftRel F R)
      (pshBarrLiftRel G R) := by
  intro c a b hmem
  simp only [pshBarrLiftRel, pshBarrLift,
    pshProdOverToRel, Subfunctor.range,
    Set.mem_range, Over.mk_hom] at hmem ⊢
  obtain ⟨w, hw⟩ := hmem
  refine ⟨(σ.app R.toFunctor).app c w, ?_⟩
  have nf := congr_fun (congr_app
    (σ.naturality
      (R.ι ≫ pshProdFst P Q)) c) w
  have ns := congr_fun (congr_app
    (σ.naturality
      (R.ι ≫ pshProdSnd P Q)) c) w
  simp only [NatTrans.comp_app,
    types_comp_apply] at nf ns
  have hw₁ := congr_arg Prod.fst hw
  have hw₂ := congr_arg Prod.snd hw
  dsimp [pshProdLift,
    FunctorToTypes.prod] at hw₁ hw₂ ⊢
  exact Prod.ext
    (nf.symm.trans (congr_arg _ hw₁))
    (ns.symm.trans (congr_arg _ hw₂))

set_option backward.isDefEq.respectTransparency false in
/-- The Barr extension through a composite
`F ⋙ G` is contained in the composed Barr
extensions `pshBarrLiftRel G (pshBarrLiftRel F R)`.
The containment factors the composite `G(F(R))`
through `G(pshBarrLiftRel F R)` using the range
factorization of the Barr lift of `F`. -/
theorem pshBarrLiftRel_comp_functor_le
    {P Q : Cᵒᵖ ⥤ Type w}
    (F G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w))
    (R : PshRel P Q) :
    pshBarrLiftRel (F ⋙ G) R ≤
      pshBarrLiftRel G
        (pshBarrLiftRel F R) := by
  set φ := Subfunctor.lift
    (pshBarrLift F (Over.mk R.ι)).hom
    (le_refl _)
  have hφ_ι :
      φ ≫ (pshBarrLiftRel F R).ι =
      (pshBarrLift F (Over.mk R.ι)).hom :=
    Subfunctor.lift_ι _ _
  have hfactor :
      (pshBarrLift (F ⋙ G)
        (Over.mk R.ι)).hom =
      G.map φ ≫
        (pshBarrLift G
          (Over.mk
            (pshBarrLiftRel F R).ι)).hom :=
    pshProdPresheaf_hom_ext
      (by
        rw [pshBarrLift_fst, Category.assoc,
          pshBarrLift_fst, ← G.map_comp,
          Functor.comp_map]; congr 1)
      (by
        rw [pshBarrLift_snd, Category.assoc,
          pshBarrLift_snd, ← G.map_comp,
          Functor.comp_map]; congr 1)
  simp only [pshBarrLiftRel, pshProdOverToRel]
  rw [hfactor]
  exact Subfunctor.range_comp_le _ _

/-- The unit of an adjunction `F ⊣ G` preserves
Barr-lifted relations: `(η P, η Q)` is
`(R, pshBarrLiftRel (F ⋙ G) R)`-related.

Since `pshBarrLiftRel (𝟭 _) R = R` by
`pshBarrLiftRel_functor_id`, this is an instance
of `natTrans_barrLiftRel_related` applied to the
unit `η : 𝟭 _ ⟶ F ⋙ G`. -/
theorem adjUnit_barrLiftRel_related
    {P Q : Cᵒᵖ ⥤ Type w}
    {F G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (adj : F ⊣ G)
    (R : PshRel P Q) :
    pshRelRelated
      (adj.unit.app P) (adj.unit.app Q)
      R (pshBarrLiftRel (F ⋙ G) R) := by
  have h := natTrans_barrLiftRel_related
    adj.unit R
  simp only [pshBarrLiftRel_functor_id] at h
  exact h

/-- The counit of an adjunction `F ⊣ G`
preserves Barr-lifted relations: `(ε P, ε Q)`
is `(pshBarrLiftRel (G ⋙ F) R, R)`-related.

Since `pshBarrLiftRel (𝟭 _) R = R` by
`pshBarrLiftRel_functor_id`, this is an instance
of `natTrans_barrLiftRel_related` applied to the
counit `ε : G ⋙ F ⟶ 𝟭 _`. -/
theorem adjCounit_barrLiftRel_related
    {P Q : Cᵒᵖ ⥤ Type w}
    {F G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (adj : F ⊣ G)
    (R : PshRel P Q) :
    pshRelRelated
      (adj.counit.app P) (adj.counit.app Q)
      (pshBarrLiftRel (G ⋙ F) R) R := by
  have h := natTrans_barrLiftRel_related
    adj.counit R
  simp only [pshBarrLiftRel_functor_id] at h
  exact h

/-- A natural transformation `σ : F ⟶ G`
between endofunctors of `PSh(C)` lifts to a
natural transformation between the corresponding
Barr extension edge functors. At each edge `R`,
the lifted transformation applies `σ` to source
and target, with the square condition given by
`natTrans_barrLiftRel_related`. -/
def pshBarrLiftEdgeNatTrans
    {F G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (σ : F ⟶ G) :
    pshBarrLiftEdgeFunctor (C := C) F ⟶
      pshBarrLiftEdgeFunctor G where
  app R :=
    { srcMap := σ.app R.src
      tgtMap := σ.app R.tgt
      sq := natTrans_barrLiftRel_related
        σ R.edge }
  naturality _ _ f :=
    VertEdgeHom.ext
      (σ.naturality f.srcMap)
      (σ.naturality f.tgtMap)

/-- The edge-level lifting is functorial: the
identity natural transformation lifts to the
identity. -/
@[simp]
theorem pshBarrLiftEdgeNatTrans_id
    (G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :
    pshBarrLiftEdgeNatTrans (𝟙 G) =
      𝟙 (pshBarrLiftEdgeFunctor
        (C := C) G) := by
  ext R
  exact VertEdgeHom.ext rfl rfl

/-- The edge-level lifting preserves
composition. -/
@[simp]
theorem pshBarrLiftEdgeNatTrans_comp
    {F G H :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (σ : F ⟶ G) (τ : G ⟶ H) :
    pshBarrLiftEdgeNatTrans (σ ≫ τ) =
      pshBarrLiftEdgeNatTrans (C := C) σ ≫
        pshBarrLiftEdgeNatTrans τ := by
  ext R
  exact VertEdgeHom.ext rfl rfl

/-- The edge-level Barr extension is lax monoidal
with respect to functor composition: the Barr
extension of `F ⋙ G` admits a natural comparison
morphism into the composition of the individual
Barr extensions.  The edge comparison has identity
source and target maps (since `(F ⋙ G).obj` equals
`G.obj ∘ F.obj` definitionally), with the edge
containment given by
`pshBarrLiftRel_comp_functor_le`. -/
def pshBarrLiftEdgeCompComparison
    (F G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)) :
    pshBarrLiftEdgeFunctor (C := C) (F ⋙ G) ⟶
      pshBarrLiftEdgeFunctor F ⋙
        pshBarrLiftEdgeFunctor G where
  app R :=
    { srcMap := 𝟙 _
      tgtMap := 𝟙 _
      sq := fun c _ _ h =>
        pshBarrLiftRel_comp_functor_le
          F G R.edge c h }
  naturality _ _ f :=
    VertEdgeHom.ext
      (show (F ⋙ G).map f.srcMap ≫ 𝟙 _ =
        𝟙 _ ≫ G.map (F.map f.srcMap) by
        simp)
      (show (F ⋙ G).map f.tgtMap ≫ 𝟙 _ =
        𝟙 _ ≫ G.map (F.map f.tgtMap) by
        simp)

/-- The edge-level unit of an adjunction
`F ⊣ G`: a natural transformation from `𝟭` to
`pshBarrLiftEdgeFunctor (F ⋙ G)`, obtained by
lifting the unit `η : 𝟭 ⟶ F ⋙ G` via
`pshBarrLiftEdgeNatTrans` and composing with the
identity `pshBarrLiftRel_functor_id`. -/
def adjEdgeUnit
    {F G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (adj : F ⊣ G) :
    pshBarrLiftEdgeFunctor (C := C) (𝟭 _) ⟶
      pshBarrLiftEdgeFunctor (F ⋙ G) :=
  pshBarrLiftEdgeNatTrans adj.unit

/-- The edge-level counit of an adjunction
`F ⊣ G`: a natural transformation from
`pshBarrLiftEdgeFunctor (G ⋙ F)` to `𝟭`,
obtained by lifting the counit `ε : G ⋙ F ⟶ 𝟭`
via `pshBarrLiftEdgeNatTrans` and composing with
the identity `pshBarrLiftRel_functor_id`. -/
def adjEdgeCounit
    {F G :
      (Cᵒᵖ ⥤ Type w) ⥤ (Cᵒᵖ ⥤ Type w)}
    (adj : F ⊣ G) :
    pshBarrLiftEdgeFunctor (C := C) (G ⋙ F) ⟶
      pshBarrLiftEdgeFunctor (𝟭 _) :=
  pshBarrLiftEdgeNatTrans adj.counit

/-- Lax vertical composition: the composition
of Barr-lifted relations is contained in the
Barr lift of the composed relation. This is the
lax version of `DFPreservesVComp`; equality does
not hold in general because `G` need not
preserve the surjection
`pullbackToRelCompFunctor`. -/
theorem pshBarrLiftDF_laxVComp
    (G : (Cᵒᵖ ⥤ Type w) ⥤
         (Cᵒᵖ ⥤ Type w))
    [PreservesLimitsOfShape WalkingCospan G]
    {P Q W : Cᵒᵖ ⥤ Type w}
    (R : PshRel P Q) (S : PshRel Q W) :
    pshRelComp (pshBarrLiftRel G R)
      (pshBarrLiftRel G S) ≤
    pshBarrLiftRel G (pshRelComp R S) :=
  relComp_barrLiftRel_le_of_preservesPullbacks
    G R S

/-- The Barr extension preserves vertical
identity squares. -/
theorem pshBarrLiftDF_preservesSqVertId
    (G : (Cᵒᵖ ⥤ Type w) ⥤
         (Cᵒᵖ ⥤ Type w)) :
    DFPreservesSqVertId
      pshRelDoubleOps pshRelDoubleOps
      (pshBarrLiftDoubleFunctorOps G) := by
  intro _ _ α
  simp only [pshBarrLiftDoubleFunctorOps,
    pshRelDoubleOps, pshBarrLiftRel_id]
  exact HEq.rfl

/-- The Barr extension preserves horizontal
identity squares. -/
theorem pshBarrLiftDF_preservesSqHorId
    (G : (Cᵒᵖ ⥤ Type w) ⥤
         (Cᵒᵖ ⥤ Type w)) :
    DFPreservesSqHorId
      pshRelDoubleOps pshRelDoubleOps
      (pshBarrLiftDoubleFunctorOps G) := by
  intro _ _ R
  simp only [pshBarrLiftDoubleFunctorOps,
    pshRelDoubleOps, G.map_id]
  exact HEq.rfl

/-- The Barr extension preserves horizontal
composition of squares. -/
theorem pshBarrLiftDF_preservesSqHComp
    (G : (Cᵒᵖ ⥤ Type w) ⥤
         (Cᵒᵖ ⥤ Type w)) :
    DFPreservesSqHComp
      pshRelDoubleOps pshRelDoubleOps
      (pshBarrLiftDoubleFunctorOps G) := by
  intro _ _ _ _ _ _ _ _ _ _ _ _ _ α β
  simp only [pshBarrLiftDoubleFunctorOps,
    pshRelDoubleOps, G.map_comp]
  exact HEq.rfl

end BarrLiftDoubleFunctor

section IhomProdFunctors

/-!
## Internal hom and product functors

The covariant internal hom functor `[A, -]`
sending `B` to `A.functorHom B`, and the product
functor `- × A` sending `B` to `B × A`. These
form an adjunction `- × A ⊣ [A, -]` in the
presheaf category.
-/

variable {C : Type u} [Category.{v} C]

/-- The covariant internal hom functor `[A, -]`
in the presheaf category, sending `B` to
`A.functorHom B` and a morphism `f : B ⟶ B'`
to `pshIhomProfMap (𝟙 A) f`. -/
def pshIhomFunctor
    (A : Cᵒᵖ ⥤ Type (max u v)) :
    (Cᵒᵖ ⥤ Type (max u v)) ⥤
      (Cᵒᵖ ⥤ Type (max u v)) where
  obj B := A.functorHom B
  map f := pshIhomProfMap (𝟙 A) f
  map_id _ := pshIhomProfMap_id
  map_comp f g := by
    have := pshIhomProfMap_comp
      (𝟙 A) (𝟙 A) f g
    simp only [Category.comp_id] at this
    exact this

/-- The Barr extension of the internal hom
functor `[A, -]` is contained in the arrow
relation with identity domain relation: every
pair in `pshBarrLiftRel (pshIhomFunctor A) R`
is also in `pshArrowRel (pshRelId A) R`.

The Barr extension constructs witnesses
existentially (a natural family `z` in
`[A, R.toFunctor]` projecting to `(g₁, g₂)`),
while the arrow relation requires relatedness
for all related inputs. A natural witness
provides pointwise witnesses, giving the
containment. -/
theorem pshBarrLiftRel_ihom_le_arrowRel
    (A : Cᵒᵖ ⥤ Type (max u v))
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (R : PshRel P Q) :
    pshBarrLiftRel (pshIhomFunctor A) R ≤
      pshArrowRel (pshRelId A) R := by
  intro c ⟨g₁, g₂⟩ hmem
  simp only [pshBarrLiftRel, pshProdOverToRel,
    Subfunctor.range, Set.mem_range] at hmem
  obtain ⟨z, hz⟩ := hmem
  apply pshArrowRel_intro
  intro d k a₁ a₂ hid
  simp only [pshRelId] at hid
  have hid' : a₁ = a₂ := hid; subst hid'
  suffices hsuff :
      (g₁.app d k a₁, g₂.app d k a₁) =
      (z.app d k a₁).val by
    rw [hsuff]; exact (z.app d k a₁).property
  have hfst := congr_arg
    (fun p => Prod.fst p |>.app d k a₁) hz
  have hsnd := congr_arg
    (fun p => Prod.snd p |>.app d k a₁) hz
  dsimp [pshBarrLift, pshProdLift,
    pshIhomFunctor, pshIhomProfMap,
    Subfunctor.ι] at hfst hsnd
  exact Prod.ext hfst.symm hsnd.symm

set_option backward.isDefEq.respectTransparency false in
/-- The arrow relation with identity domain
is contained in the Barr extension of the
internal hom: every pair in
`pshArrowRel (pshRelId A) R` is also in
`pshBarrLiftRel (pshIhomFunctor A) R`.

The proof constructs a natural witness
`z : (A.functorHom R.toFunctor).obj c` from
the arrow relation predicate. Since `R.ι` is a
subfunctor inclusion, the witness at each
`(d, k, a)` is uniquely determined by
`(g₁, g₂)`, and the naturality of `g₁, g₂`
as `HomObj` elements guarantees the naturality
of `z`. -/
theorem pshArrowRel_le_barrLiftRel_ihom
    (A : Cᵒᵖ ⥤ Type (max u v))
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (R : PshRel P Q) :
    pshArrowRel (pshRelId A) R ≤
      pshBarrLiftRel (pshIhomFunctor A) R := by
  intro c ⟨g₁, g₂⟩ hmem
  simp only [pshBarrLiftRel, pshProdOverToRel,
    Subfunctor.range, Set.mem_range]
  refine ⟨?_, ?_⟩
  · exact
      { app := fun d k a =>
          ⟨(g₁.app d k a, g₂.app d k a),
           pshArrowRel_apply hmem k rfl⟩
        naturality := fun {d e} f k => by
          ext a
          apply Subtype.ext
          exact Prod.ext
            (congr_fun (g₁.naturality f k) a)
            (congr_fun (g₂.naturality f k) a) }
  · apply Prod.ext <;> (
      dsimp [pshBarrLift, pshProdLift,
        pshIhomFunctor, pshIhomProfMap,
        Subfunctor.ι]
      ext d k a; rfl)

/-- The Barr extension of the internal hom
`[A, -]` equals the arrow relation with
identity domain:
`pshBarrLiftRel (pshIhomFunctor A) R =
pshArrowRel (pshRelId A) R`.

The forward direction
(`pshBarrLiftRel_ihom_le_arrowRel`) uses the
natural witness to provide pointwise
witnesses. The reverse direction
(`pshArrowRel_le_barrLiftRel_ihom`) assembles
pointwise witnesses into a natural family,
exploiting the injectivity of `R.ι`. -/
theorem pshBarrLiftRel_ihom_eq_arrowRel
    (A : Cᵒᵖ ⥤ Type (max u v))
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (R : PshRel P Q) :
    pshBarrLiftRel (pshIhomFunctor A) R =
      pshArrowRel (pshRelId A) R :=
  le_antisymm
    (pshBarrLiftRel_ihom_le_arrowRel A R)
    (pshArrowRel_le_barrLiftRel_ihom A R)

/-- The product functor `- × A` in the presheaf
category, sending `B` to `pshProdPresheaf B A`
and a morphism `f : B ⟶ B'` to
`pshProdMap f (𝟙 A)`. -/
def pshProdRightFunctor
    (A : Cᵒᵖ ⥤ Type (max u v)) :
    (Cᵒᵖ ⥤ Type (max u v)) ⥤
      (Cᵒᵖ ⥤ Type (max u v)) where
  obj B := pshProdPresheaf B A
  map f := pshProdMap f (𝟙 A)
  map_id _ := pshProdMap_id _ _
  map_comp f g := by
    have := pshProdMap_comp f (𝟙 A) g (𝟙 A)
    simp only [Category.comp_id] at this
    exact this

/-- Composition preservation for the Barr
extension of the internal hom functor `[A, -]`:
given related pairs in `pshBarrLiftRel
(pshIhomFunctor A) R` and `pshBarrLiftRel
(pshIhomFunctor A) S`, their composite lies in
`pshBarrLiftRel (pshIhomFunctor A) (pshRelComp R S)`.

The proof rewrites the Barr extension as the
arrow relation via `pshBarrLiftRel_ihom_eq_arrowRel`,
applies `pshArrowRel_comp` to compose the arrow
relations, and rewrites `pshRelComp (pshRelId A)
(pshRelId A)` to `pshRelId A` via
`pshRelComp_id_left`. -/
theorem pshBarrLiftRel_ihom_comp
    (A : Cᵒᵖ ⥤ Type (max u v))
    {P Q W : Cᵒᵖ ⥤ Type (max u v)}
    (R : PshRel P Q) (S : PshRel Q W)
    {c : Cᵒᵖ}
    {w₁ : (pshIhomFunctor A |>.obj P).obj c}
    {w₂ : (pshIhomFunctor A |>.obj Q).obj c}
    {w₃ : (pshIhomFunctor A |>.obj W).obj c}
    (h₁₂ : (w₁, w₂) ∈
      (pshBarrLiftRel (pshIhomFunctor A) R).obj c)
    (h₂₃ : (w₂, w₃) ∈
      (pshBarrLiftRel (pshIhomFunctor A) S).obj c) :
    (w₁, w₃) ∈
      (pshBarrLiftRel (pshIhomFunctor A)
        (pshRelComp R S)).obj c := by
  rw [pshBarrLiftRel_ihom_eq_arrowRel] at h₁₂ h₂₃ ⊢
  have h := pshArrowRel_comp h₁₂ h₂₃
  rwa [pshRelComp_id_left] at h

/-- The product of two presheaf relations:
`pshProdRel R S` relates `(p₁, q₁)` to
`(p₂, q₂)` iff `(p₁, p₂) ∈ R` and
`(q₁, q₂) ∈ S`. -/
def pshProdRel
    {P₁ P₂ Q₁ Q₂ : Cᵒᵖ ⥤ Type (max u v)}
    (R : PshRel P₁ P₂)
    (S : PshRel Q₁ Q₂) :
    PshRel (pshProdPresheaf P₁ Q₁)
      (pshProdPresheaf P₂ Q₂) where
  obj c :=
    { pq | (pq.1.1, pq.2.1) ∈ R.obj c ∧
           (pq.1.2, pq.2.2) ∈ S.obj c }
  map f := by
    rintro ⟨_, _⟩ ⟨hR, hS⟩
    exact ⟨R.map f hR, S.map f hS⟩

/-- The Barr extension of the product functor
`- × A` equals the product relation with the
identity on `A`: `pshBarrLiftRel
(pshProdRightFunctor A) R = pshProdRel R
(pshRelId A)`. A pair `((p₁, a₁), (p₂, a₂))`
is in the Barr lift iff there exists a witness
`(r, a)` in `R.toFunctor × A` projecting to
both sides, which forces `(p₁, p₂) ∈ R` and
`a₁ = a = a₂`. -/
theorem pshBarrLiftRel_prod_eq_prodRel
    (A : Cᵒᵖ ⥤ Type (max u v))
    {P Q : Cᵒᵖ ⥤ Type (max u v)}
    (R : PshRel P Q) :
    pshBarrLiftRel (pshProdRightFunctor A) R =
      pshProdRel R (pshRelId A) := by
  ext c ⟨⟨p₁, a₁⟩, ⟨p₂, a₂⟩⟩
  simp only [pshBarrLiftRel, pshProdOverToRel,
    Subfunctor.range, Set.mem_range,
    pshProdRel]
  constructor
  · rintro ⟨⟨r, a⟩, hz⟩
    dsimp [pshBarrLift, pshProdLift,
      pshProdRightFunctor, pshProdMap,
      pshProdFst, pshProdSnd,
      Subfunctor.ι] at hz
    have h₁ := congr_arg (·.1) hz
    have h₂ := congr_arg (·.2) hz
    dsimp at h₁ h₂
    have hp₁ := congr_arg (·.1) h₁
    have ha₁ := congr_arg (·.2) h₁
    have hp₂ := congr_arg (·.1) h₂
    have ha₂ := congr_arg (·.2) h₂
    dsimp at hp₁ ha₁ hp₂ ha₂
    subst hp₁ ha₁ hp₂ ha₂
    exact ⟨r.property, rfl⟩
  · rintro ⟨hR, hid⟩
    dsimp at hR hid
    simp only [pshRelId] at hid
    have hid' : a₁ = a₂ := hid; subst hid'
    refine ⟨(⟨(p₁, p₂), hR⟩, a₁), ?_⟩
    dsimp [pshBarrLift, pshProdLift,
      pshProdRightFunctor, pshProdMap,
      pshProdFst, pshProdSnd,
      Subfunctor.ι]

/-- Composition preservation for the product
relation: given `(x, y) ∈ pshProdRel R₁ S₁` and
`(y, z) ∈ pshProdRel R₂ S₂`, the composite
`(x, z)` lies in
`pshProdRel (pshRelComp R₁ R₂)
  (pshRelComp S₁ S₂)`. -/
theorem pshProdRel_comp
    {P₁ P₂ P₃ Q₁ Q₂ Q₃ :
      Cᵒᵖ ⥤ Type (max u v)}
    {R₁ : PshRel P₁ P₂}
    {R₂ : PshRel P₂ P₃}
    {S₁ : PshRel Q₁ Q₂}
    {S₂ : PshRel Q₂ Q₃}
    {c : Cᵒᵖ}
    {x : (pshProdPresheaf P₁ Q₁).obj c}
    {y : (pshProdPresheaf P₂ Q₂).obj c}
    {z : (pshProdPresheaf P₃ Q₃).obj c}
    (h₁₂ : (x, y) ∈
      (pshProdRel R₁ S₁).obj c)
    (h₂₃ : (y, z) ∈
      (pshProdRel R₂ S₂).obj c) :
    (x, z) ∈
      (pshProdRel (pshRelComp R₁ R₂)
        (pshRelComp S₁ S₂)).obj c := by
  obtain ⟨hR₁, hS₁⟩ := h₁₂
  obtain ⟨hR₂, hS₂⟩ := h₂₃
  exact ⟨⟨y.1, hR₁, hR₂⟩,
         ⟨y.2, hS₁, hS₂⟩⟩

/-- Composition preservation for the Barr
extension of the product functor `- × A`:
given related pairs in
`pshBarrLiftRel (pshProdRightFunctor A) R`
and `pshBarrLiftRel (pshProdRightFunctor A) S`,
the composite lies in
`pshBarrLiftRel (pshProdRightFunctor A)
  (pshRelComp R S)`.

The proof rewrites the Barr extension as the
product relation via
`pshBarrLiftRel_prod_eq_prodRel`, applies
`pshProdRel_comp`, and simplifies
`pshRelComp (pshRelId A) (pshRelId A)` to
`pshRelId A` via `pshRelComp_id_left`. -/
theorem pshBarrLiftRel_prod_comp
    (A : Cᵒᵖ ⥤ Type (max u v))
    {P Q W : Cᵒᵖ ⥤ Type (max u v)}
    (R : PshRel P Q) (S : PshRel Q W)
    {c : Cᵒᵖ}
    {w₁ : (pshProdRightFunctor A |>.obj P).obj c}
    {w₂ : (pshProdRightFunctor A |>.obj Q).obj c}
    {w₃ : (pshProdRightFunctor A |>.obj W).obj c}
    (h₁₂ : (w₁, w₂) ∈
      (pshBarrLiftRel
        (pshProdRightFunctor A) R).obj c)
    (h₂₃ : (w₂, w₃) ∈
      (pshBarrLiftRel
        (pshProdRightFunctor A) S).obj c) :
    (w₁, w₃) ∈
      (pshBarrLiftRel (pshProdRightFunctor A)
        (pshRelComp R S)).obj c := by
  rw [pshBarrLiftRel_prod_eq_prodRel]
    at h₁₂ h₂₃ ⊢
  have h := pshProdRel_comp h₁₂ h₂₃
  rwa [pshRelComp_id_left] at h

end IhomProdFunctors

section TypeRelations

/-!
## Type relations as presheaf relations

`Type v` embeds fully faithfully into
`PSh(Discrete PUnit) = (Discrete PUnit)ᵒᵖ ⥤ Type v`
via the constant-presheaf functor. All presheaf
relation constructions (`PshRel`, `pshRelGraph`,
`pshBarrLiftRel`, `pshArrowRel`, the double
category) specialize to give a double category on
`Type v` with:
- Objects: types in `Type v`
- Horizontal morphisms: functions
- Vertical morphisms: relations (up to iso)
- Squares: relatedness (`Prop`-valued)
-/

/-- The constant-presheaf embedding
`Type v ⥤ (Discrete PUnit)ᵒᵖ ⥤ Type v`,
sending each type to the presheaf constant at
that type. -/
abbrev typeToPsh : Type v ⥤
    ((Discrete PUnit)ᵒᵖ ⥤ Type v) :=
  Functor.const (Discrete PUnit)ᵒᵖ

/-- A proof-relevant relation from type `A` to
type `B`: an object of the over category
`Over (typeToPsh.obj A × typeToPsh.obj B)`. -/
abbrev TypeProdOver (A B : Type v) :=
  PshProdOver (typeToPsh.obj A) (typeToPsh.obj B)

/-- A relation from type `A` to type `B` up to
isomorphism: an isomorphism class of
`TypeProdOver A B`. -/
abbrev TypeRel (A B : Type v) :=
  PshRel (typeToPsh.obj A) (typeToPsh.obj B)

/-- The identity relation on a type. -/
abbrev typeRelId (A : Type v) : TypeRel A A :=
  pshRelId (typeToPsh.obj A)

/-- The graph relation of a function `f : A → B`,
obtained by applying `pshRelGraph` to
`typeToPsh.map f`. -/
abbrev typeRelGraph {A B : Type v}
    (f : A → B) : TypeRel A B :=
  pshRelGraph (typeToPsh.map f)

/-- Composition of type relations, obtained from
`pshRelComp`. -/
abbrev typeRelComp {A B C : Type v} :
    TypeRel A B → TypeRel B C →
    TypeRel A C :=
  pshRelComp

theorem typeRelComp_id_left {A B : Type v}
    (R : TypeRel A B) :
    typeRelComp (typeRelId A) R = R :=
  pshRelComp_id_left R

theorem typeRelComp_id_right {A B : Type v}
    (R : TypeRel A B) :
    typeRelComp R (typeRelId B) = R :=
  pshRelComp_id_right R

theorem typeRelComp_assoc {A B C D : Type v}
    (R : TypeRel A B) (S : TypeRel B C)
    (T : TypeRel C D) :
    typeRelComp (typeRelComp R S) T =
      typeRelComp R (typeRelComp S T) :=
  pshRelComp_assoc R S T

theorem typeRelGraph_eq_id (A : Type v) :
    typeRelGraph (id : A → A) =
      typeRelId A := by
  change pshRelGraph (typeToPsh.map (𝟙 A)) =
    pshRelId (typeToPsh.obj A)
  rw [typeToPsh.map_id]
  exact pshRelGraph_eq_id (typeToPsh.obj A)

theorem typeRelGraph_comp {A B C : Type v}
    (f : A → B) (g : B → C) :
    typeRelComp (typeRelGraph f)
      (typeRelGraph g) =
      typeRelGraph (g ∘ f) :=
  pshRelGraph_comp
    (typeToPsh.map f) (typeToPsh.map g)

/-- The category of types with relations as
morphisms, obtained by specializing `PshRelCat`
to the terminal base category. -/
abbrev TypeRelCat :=
  PshRelCat.{0, 0, v} (C := Discrete PUnit)

/-- Functor sending each function `f : A → B` to
its graph relation in `TypeRelCat`. -/
abbrev typeRelGraphFunctor :
    Type v ⥤ TypeRelCat.{v} :=
  typeToPsh ⋙
    @pshRelGraphFunctor (Discrete PUnit) _

/-- Evaluation at the single object of
`Discrete PUnit`, giving a functor from
presheaves to types. This is a left inverse of
`typeToPsh`. -/
abbrev typeEvalUnit :
    ((Discrete PUnit)ᵒᵖ ⥤ Type v) ⥤ Type v :=
  (evaluation _ _).obj
    (Opposite.op ⟨PUnit.unit⟩)

/-- `typeToPsh` is fully faithful: natural
transformations between constant presheaves
over `Discrete PUnit` correspond to
functions. -/
theorem typeToPsh_map_eq_iff
    {A B : Type v}
    (α : typeToPsh.obj A ⟶ typeToPsh.obj B) :
    typeToPsh.map
      (typeEvalUnit.map α) = α := by
  ext ⟨⟨⟩⟩; rfl

/-- Relatedness of functions by a pair of type
relations: given `R : TypeProdOver A A'` and
`S : TypeProdOver B B'`, `f : A → B` and
`f' : A' → B'` are `(R, S)`-related iff
`pshProdOverRelated` holds. -/
abbrev TypeProdOverRelated
    {A A' B B' : Type v}
    (R : TypeProdOver A A')
    (S : TypeProdOver B B')
    (f : A → B) (f' : A' → B') :=
  PshProdOverRelated R S
    (typeToPsh.map f)
    (typeToPsh.map f')

/-- Given `R : TypeRel A A'` and
`S : TypeRel B B'`, `f` and `f'` are
`(R, S)`-related iff `pshRelRelated` holds. -/
abbrev typeRelRelated
    {A A' B B' : Type v}
    (R : TypeRel A A')
    (S : TypeRel B B')
    (f : A → B) (f' : A' → B') :=
  pshRelRelated
    (typeToPsh.map f)
    (typeToPsh.map f')
    R S

/-- Lift a type endofunctor to a presheaf
endofunctor on `PSh(Discrete PUnit)` via
`typeEvalUnit ⋙ G ⋙ typeToPsh`. -/
abbrev typeFunctorToPsh
    (G : Type v ⥤ Type v) :
    ((Discrete PUnit)ᵒᵖ ⥤ Type v) ⥤
      ((Discrete PUnit)ᵒᵖ ⥤ Type v) :=
  typeEvalUnit ⋙ G ⋙ typeToPsh

/-- `typeFunctorToPsh G` computes correctly on
objects from `typeToPsh`: applying it to a
constant presheaf at `A` gives the constant
presheaf at `G.obj A`. -/
theorem typeFunctorToPsh_obj
    (G : Type v ⥤ Type v) (A : Type v) :
    (typeFunctorToPsh G).obj
      (typeToPsh.obj A) =
    typeToPsh.obj (G.obj A) :=
  rfl

/-- The Barr extension of a type endofunctor
`G : Type v ⥤ Type v` applied to a type
relation `R : TypeRel A B`, producing
`TypeRel (G.obj A) (G.obj B)`. -/
abbrev typeBarrLiftRel
    (G : Type v ⥤ Type v)
    {A B : Type v}
    (R : TypeRel A B) :
    TypeRel (G.obj A) (G.obj B) :=
  pshBarrLiftRel (typeFunctorToPsh G) R

end TypeRelations

end GebLean
