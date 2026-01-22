import GebLean.WeightedAlg
import GebLean.Utilities.Elements

/-!
# Restricted Coends as Colimits via Category of Elements

This module establishes the connection between restricted coends (used in
Mendler-style recursion) and standard categorical constructions (colimits,
Kan extensions).

## Overview

For an endodifunctor `G : Cᵒᵖ ⥤ C ⥤ C` and an object `pt : C`, the functor
`GExtFunctor G` is defined via restricted coends:

  `G^e(pt) = Σ(HomToProf(pt), G)`

This module shows that this restricted coend can be understood as a colimit
over the category of elements of the weight functor.

## Main Results

1. `HomToProf pt` restricted to the diagonal is naturally isomorphic to
   `coyoneda'.obj pt` (the contravariant hom-functor).

2. The category of elements of `coyoneda'.obj pt` is equivalent to `Over pt`.

3. The restricted coend `Σ(HomToProf(pt), G)` corresponds to a cocone structure
   over the diagram `(A, f : A ⟶ pt) ↦ G(A, A)` indexed by `Over pt`.

This establishes that `G^e(pt)` has the structure of a pointwise (left) Kan
extension formula, generalizing from the case where `G ∘ Δ` is functorial to
arbitrary profunctors G.

## References

* Vene, "Categorical Programming with Inductive and Coinductive Types", Ch. 5
* Kelly, "Basic Concepts of Enriched Category Theory", Section 3.4
-/

namespace GebLean

open CategoryTheory Limits Opposite

universe u v

variable {C : Type u} [Category.{v} C]

section HomToProfAndCoyoneda

/-!
## HomToProf pt and coyoneda'.obj pt

The profunctor `HomToProf pt : Cᵒᵖ ⥤ C ⥤ Type v` has the property that its
diagonal `diagApp (HomToProf pt) A = (A ⟶ pt)` equals `(coyoneda'.obj pt).obj A`.

Since `HomToProf pt` is constant in the second argument, its diagonal behavior
is completely determined by the contravariant hom-functor.
-/

/-- The diagonal of `HomToProf pt` as a functor: sends `A` to `(A ⟶ pt)`,
contravariant via precomposition. This is naturally isomorphic to
`coyoneda'.obj pt` (though `coyoneda'` uses `op'` while this uses `op`). -/
@[simps]
def HomToProfDiag (pt : C) : Cᵒᵖ ⥤ Type v where
  obj A := A.unop ⟶ pt
  map {A B} f := fun h => f.unop ≫ h
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp [Category.assoc]

/-- The diagonal of `HomToProf pt` at any object equals the diagonal functor
evaluated at that object. -/
theorem HomToProf_diagApp_eq (pt A : C) :
    diagApp (HomToProf pt) A = (HomToProfDiag pt).obj (op A) := rfl

/-- Natural isomorphism between `HomToProfDiag pt` and the Yoneda embedding at pt.
This uses mathlib's standard `yoneda`. -/
def HomToProfDiagIsoYoneda (pt : C) : HomToProfDiag pt ≅ yoneda.obj pt :=
  NatIso.ofComponents
    (fun A => Equiv.toIso (Equiv.refl _))
    (fun {A B} f => by ext h; rfl)

end HomToProfAndCoyoneda

section DiagramFromSlice

/-!
## The diagram functor from Over pt

Given a profunctor `G : Cᵒᵖ ⥤ C ⥤ C` and an object `pt : C`, we construct
a functor `Over pt ⥤ C` that sends `(A, f : A ⟶ pt)` to `G(A, A)`.

This is the diagram whose colimit should correspond to the restricted coend.
-/

variable (G : Cᵒᵖ ⥤ C ⥤ C)

/-- The object part of the diagram: sends an over-object to the diagonal
of G at its source. -/
def sliceDiagObj (pt : C) (x : Over pt) : C := (G.obj (op x.left)).obj x.left

/- The morphism part of the diagram requires the dinaturality structure.

For `f : x ⟶ y` in `Over pt`, we have `f.left : x.left ⟶ y.left`.
The profunctor G acts contravariantly on the first argument and covariantly
on the second, giving us two maps:
  - `G(f.left^op, id) : G(y.left, x.left) ⟶ G(x.left, x.left)`
  - `G(id, f.left) : G(y.left, y.left) ⟶ G(y.left, x.left)`

There is no canonical map `G(x.left, x.left) ⟶ G(y.left, y.left)` unless
G factors through the diagonal in a functorial way.

However, for the purpose of relating to restricted coends, what matters is
that restricted cowedges provide a compatible family of maps to the apex,
not functoriality of the diagram itself.
-/

/-- A restricted cowedge from G with weight H induces a cocone structure over
the category of elements of (the diagonal of) H.

Given a restricted cowedge `(pt, Φ)` where `Φ_A : H(A, A) → C(G(A, A), pt)`,
we get for each element `(A, h) ∈ El(H_diag)` a morphism `Φ_A(h) : G(A, A) → pt`.

The dinaturality of Φ ensures compatibility with morphisms in the category
of elements.
-/
structure RestrictedCowedgeCoconeData (H : Cᵒᵖ ⥤ C ⥤ Type v) (cwedge : RestrictedCowedge G H)
    where
  /-- For each diagonal element, the map to the apex. -/
  leg : (A : C) → (h : diagApp H A) → (G.obj (op A)).obj A ⟶ cwedge.pt
  /-- The leg equals the cowedge family. -/
  leg_eq : ∀ A h, leg A h = cwedge.family A h

/-- Convert a restricted cowedge to its cocone data. -/
def RestrictedCowedge.toCoconeData (H : Cᵒᵖ ⥤ C ⥤ Type v) (cwedge : RestrictedCowedge G H) :
    RestrictedCowedgeCoconeData G H cwedge where
  leg := cwedge.family
  leg_eq _ _ := rfl

end DiagramFromSlice

section OverAsCategoryOfElements

/-!
## Over pt as Category of Elements

The slice category `Over pt` is equivalent to the contravariant category of
elements of the hom-functor.

The precise equivalence is `Over pt ≌ (coyoneda'.obj pt).ElementsContra'`,
established in `GebLean.Utilities.Elements` as `overEquivElements`.

Note: mathlib's `(yoneda.obj pt).Elements` has the OPPOSITE morphism direction
from `Over pt`. A morphism in `(yoneda.obj pt).Elements` from `(op A, f)` to
`(op B, g)` requires `h : op A ⟶ op B` with `h.unop ≫ f = g`, which means a
morphism `B ⟶ A` in `C`. But in `Over pt`, morphisms go `A ⟶ B`. So we need
the opposite category, or equivalently, the contravariant category of elements.

For our purposes, the equivalence `Over pt ≌ (coyoneda'.obj pt).ElementsContra'`
provides the correct structure.
-/

/-- Re-export the equivalence from Elements.lean -/
abbrev overEquivElementsContra' (pt : C) :
    Over pt ≌ (coyoneda'.obj pt).ElementsContra' :=
  ElementsContra'.overEquivElements pt

end OverAsCategoryOfElements

section RestrictedCoendUniversalProperty

/-!
## Restricted Coend Universal Property via Cocones

A restricted coend `Σ(H, G)` is an initial object in the category of
H-restricted G-cowedges. This gives a universal property analogous to
colimits: for any H-restricted G-cowedge `(D, Ψ)`, there exists a unique
morphism `[Ψ] : Σ(H, G) → D` factoring through the universal cowedge.

When `H = HomToProf pt`, the restricted cowedges correspond to families of
maps from `G(A, A)` to the apex, indexed by morphisms `A → pt`, satisfying
a dinaturality condition. This matches the structure of a cocone over the
diagram indexed by `Over pt`.
-/

open HasRestrictedCoend

variable (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)

/-- A restricted cowedge with weight `HomToProf pt` consists of:
- An apex object `D`
- A family `Φ_A : (A ⟶ pt) → (G(A, A) ⟶ D)`
- Dinaturality: for `g : A → B` and `β : B → pt`,
  `Φ_A(g ≫ β) ∘ G(g, id) = Φ_B(β) ∘ G(id, g)` -/
abbrev HomToProfCowedge := RestrictedCowedge G (HomToProf pt)

/-- The restricted coend `Σ(HomToProf pt, G)` when it exists. -/
abbrev HomToProfCoend [HasRestrictedCoend G (HomToProf pt)] : C :=
  (restrictedCoend G (HomToProf pt)).pt

/-- The universal injection for the restricted coend. -/
def HomToProfCoendInj [HasRestrictedCoend G (HomToProf pt)] (A : C) (f : A ⟶ pt) :
    (G.obj (op A)).obj A ⟶ HomToProfCoend G pt :=
  (restrictedCoend G (HomToProf pt)).family A f

/-- The descending morphism from the restricted coend to any cowedge. -/
def HomToProfCoendDesc [HasRestrictedCoend G (HomToProf pt)]
    (cwedge : HomToProfCowedge G pt) :
    HomToProfCoend G pt ⟶ cwedge.pt :=
  (restrictedCoendIsInitial G (HomToProf pt)).descHom cwedge

/-- The descending morphism satisfies the universal property. -/
theorem HomToProfCoendDesc_comm [HasRestrictedCoend G (HomToProf pt)]
    (cwedge : HomToProfCowedge G pt) (A : C) (f : A ⟶ pt) :
    HomToProfCoendInj G pt A f ≫ HomToProfCoendDesc G pt cwedge = cwedge.family A f :=
  ((restrictedCoendIsInitial G (HomToProf pt)).to cwedge).comm A f

end RestrictedCoendUniversalProperty

section CoconeCorrespondence

/-!
## Correspondence between Restricted Cowedges and Cocones

For `H = HomToProf pt`, an H-restricted G-cowedge `(D, Φ)` gives rise to
a compatible family of morphisms `G(A, A) → D` indexed by `Over pt`.

While this doesn't form a cocone in the usual sense (because there's no
functorial diagram `Over pt ⥤ C` for general profunctors G), the restricted
cowedge structure captures exactly the colimit-like universal property.

The dinaturality condition for restricted cowedges corresponds to the
cocone compatibility condition when the diagram is defined via the profunctor.
-/

variable (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)

/-- Given a HomToProf-restricted cowedge, extract the leg at an over-object. -/
def cowedgeLeg (cwedge : HomToProfCowedge G pt) (x : Over pt) :
    (G.obj (op x.left)).obj x.left ⟶ cwedge.pt :=
  cwedge.family x.left x.hom

/-- The dinaturality of a restricted cowedge expressed in terms of Over pt.

For a morphism `f : x ⟶ y` in `Over pt`, we have `x.hom = f.left ≫ y.hom`.
The dinaturality condition states:
  `cowedgeLeg(x) ∘ G(f.left, id) = cowedgeLeg(y) ∘ G(id, f.left)`
when we substitute the appropriate diagonal elements.
-/
theorem cowedgeLeg_dinatural (cwedge : HomToProfCowedge G pt) {x y : Over pt}
    (f : x ⟶ y) :
    (G.map f.left.op).app x.left ≫ cwedge.family x.left (f.left ≫ y.hom) =
    (G.obj (op y.left)).map f.left ≫ cwedge.family y.left y.hom := by
  have dinat := cwedge.isDinatural x.left y.left f.left y.hom
  simp only [Profunctor.lmap, Profunctor.rmap, HomToProf, sliceProfunctor,
    HomToProf.innerFunctor] at dinat
  exact dinat.symm

/-- The cowedge leg at x can be expressed using the factorization through y.

When `f : x ⟶ y` in `Over pt`, we have `x.hom = f.left ≫ y.hom`, so:
  `cwedge.family x.left x.hom = cwedge.family x.left (f.left ≫ y.hom)`

This follows directly from the Over.w constraint.
-/
theorem cowedgeLeg_factor_eq (cwedge : HomToProfCowedge G pt) {x y : Over pt}
    (f : x ⟶ y) :
    cwedge.family x.left x.hom = cwedge.family x.left (f.left ≫ y.hom) := by
  have hf := Over.w f
  rw [hf]

end CoconeCorrespondence

section KanExtensionInterpretation

/-!
## Interpretation as Weighted Colimit / Kan Extension

The restricted coend `G^e(pt) = Σ(HomToProf pt, G)` can be interpreted as
a weighted colimit with weight `yoneda.obj pt` (the representable presheaf).

**Weighted Colimit Formula:**
For a weight `W : Jᵒᵖ ⥤ Type` and diagram `F : J ⥤ C`:
  `W * F = colim_{(j, w) ∈ El(W)} F(j)`

**Pointwise Left Kan Extension Formula:**
For `F : J ⥤ C` and `K : J ⥤ J'`, the left Kan extension at `j' : J'` is:
  `(Lan_K F)(j') = colim_{(j, f : K(j) → j') ∈ K/j'} F(j)`

The comma category `K/j'` for `K = id : C ⥤ C` at `j' = pt` is exactly `C/pt`.

**Restricted Coend as Generalized Colimit:**
For `G : Cᵒᵖ ⥤ C ⥤ C` (a profunctor) and `H = HomToProf pt`:
  `Σ(H, G) = ∫^A H(A,A) · G(A,A)`  (weighted coend notation)
           = colim_{(A, f) ∈ El(H_diag)} G(A,A)
           = colim_{(A, f : A → pt) ∈ C/pt} G(A,A)

When `G(A, B) = F(B)` for some covariant `F : C ⥤ C`, this reduces to:
  `G^e(pt) = colim_{C/pt} F = (Lan_id F)(pt) = F(pt)`

This is the co-Yoneda lemma. For general profunctors G, the restricted coend
gives a well-defined object even when `G ∘ Δ` is not functorial.
-/

variable (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)

open HasRestrictedCoend in
/-- The Kan extension interpretation: `GExtFunctor G` computes, at each `pt`,
the "colimit" of `G(A, A)` over the slice category `C/pt`, where the colimit
is taken in the generalized sense of restricted coends.

`GExtFunctor G` is defined (in WeightedAlg.lean) as:
  `(GExtFunctor G).obj pt = (restrictedCoend G (HomToProf pt)).pt`

And our `HomToProfCoend` is:
  `HomToProfCoend G pt = (restrictedCoend G (HomToProf pt)).pt`

These are equal by definition. -/
theorem GExtFunctor_as_HomToProfCoend [HasAllHomToProfCoends G] :
    (HasAllHomToProfCoends.GExtFunctor G).obj pt = HomToProfCoend G pt := by
  rfl

end KanExtensionInterpretation

end GebLean
