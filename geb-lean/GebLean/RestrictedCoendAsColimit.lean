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
  simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor_obj_map,
    sliceProfunctor_map_app, Quiver.Hom.unop_op, HomToProf_map_app,
    HomToProf_obj_map] at dinat
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

section CopowerCoendEquivalence

open HasRestrictedCoend

/-!
## Restricted Coends as Ordinary Coends with Copowers

This section establishes the relationship:
```text
Σ(H, G) = ∫^A H(A,A) · G(A,A)
```
where:
- `Σ(H, G)` is the H-restricted G-coend
- `∫^A H(A,A) · G(A,A)` is the ordinary coend of the copower profunctor
- `·` denotes the copower (tensoring with types)

### Copowers (Type-Indexed Coproducts)

For a type `S` and object `X`, the copower `S · X` is characterized by:
```text
Hom(S · X, Y) ≅ (S → Hom(X, Y))
```

When C has copowers, the copower profunctor `(H · G)(A, B) = H(A, B) · G(A, B)` is
an endoprofunctor on C, and:

1. A cowedge from `H · G` to apex `pt` consists of:
   - Family `ω_A : H(A,A) · G(A,A) → pt`
   - Dinaturality condition

2. By the copower adjunction, this is equivalent to:
   - Family `Φ_A : H(A,A) → (G(A,A) → pt)`
   - Dinaturality condition (which matches that of restricted cowedges)

3. This is exactly an H-restricted G-cowedge!

The correspondence extends to an equivalence of categories, so initial objects
(coends) correspond: the coend of `H · G` equals the restricted coend of `(G, H)`.
-/

/-- A category has copowers if for any type S and object X, the copower S · X
exists as a colimit. The copower is characterized by the adjunction:
`Hom(S · X, Y) ≅ (S → Hom(X, Y))`.

For our purposes, we assume copowers exist and work with the universal property.
-/
class HasCopowers (C : Type u) [Category.{v} C] where
  /-- The copower object S · X for a type S and object X. -/
  copower : Type v → C → C
  /-- The family of injections indexed by elements of S. -/
  inj : ∀ (S : Type v) (X : C), S → (X ⟶ copower S X)
  /-- The universal property: any family factors through the copower. -/
  desc : ∀ {S : Type v} {X Y : C}, (S → (X ⟶ Y)) → (copower S X ⟶ Y)
  /-- The family factors through the universal morphism. -/
  fac : ∀ {S : Type v} {X Y : C} (f : S → (X ⟶ Y)) (s : S),
    inj S X s ≫ desc f = f s
  /-- Uniqueness of the factorization. -/
  uniq : ∀ {S : Type v} {X Y : C} (f : S → (X ⟶ Y)) (g : copower S X ⟶ Y),
    (∀ s, inj S X s ≫ g = f s) → g = desc f

namespace HasCopowers

variable {C : Type u} [Category.{v} C] [HasCopowers C]

/-- Notation for the copower. -/
infixl:70 " ·. " => copower

/-- Extensionality for morphisms out of copowers: two morphisms are equal
if they agree on all injections. -/
theorem ext {S : Type v} {X Y : C} (f g : S ·. X ⟶ Y)
    (h : ∀ s, inj S X s ≫ f = inj S X s ≫ g) : f = g := by
  have hf := uniq (fun s => inj S X s ≫ f) f (fun _ => rfl)
  have hg := uniq (fun s => inj S X s ≫ f) g (fun s => (h s).symm)
  rw [hf, hg]

end HasCopowers

/-!
### The Correspondence between Cowedges and Restricted Cowedges

A cowedge from the copower profunctor `H · G` to apex `pt` corresponds
bijectively to an H-restricted G-cowedge with apex `pt`.

The bijection is given by the copower universal property:
- Forward: `ω_A : H(A,A) · G(A,A) → pt` determines `Φ_A : H(A,A) → (G(A,A) → pt)`
  by `Φ_A(h) = inj(h) ≫ ω_A`
- Backward: `Φ_A : H(A,A) → (G(A,A) → pt)` determines `ω_A : H(A,A) · G(A,A) → pt`
  by the universal property of copowers

The dinaturality conditions correspond under this bijection.
-/

/-- Dinaturality condition for a copower cowedge family.

For a family `ω : ∀ A, H(A,A) · G(A,A) → pt` to form a cowedge of the copower
profunctor, it must satisfy: for all `g : A → B` and `x : H(B, A)`, the two
paths from `G(B, A)` to `pt` agree. -/
def IsCopowerCowedgeDinatural [HasCopowers C] (H : Cᵒᵖ ⥤ C ⥤ Type v)
    (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    (ω : ∀ A, HasCopowers.copower (diagApp H A) ((G.obj (op A)).obj A) ⟶ pt) :
    Prop :=
  ∀ (A B : C) (g : A ⟶ B) (x : (H.obj (Opposite.op B)).obj A),
    (G.obj (Opposite.op B)).map g ≫
      HasCopowers.inj _ _ ((H.obj (Opposite.op B)).map g x) ≫ ω B =
    (G.map g.op).app A ≫
      HasCopowers.inj _ _ ((H.map g.op).app A x) ≫ ω A

/-- Given a restricted cowedge, construct the corresponding family of copower
morphisms. This uses the copower universal property to assemble the indexed
family into a single morphism from the copower. -/
def restrictedCowedgeToCopowerFamily [HasCopowers C] (H : Cᵒᵖ ⥤ C ⥤ Type v)
    (G : Cᵒᵖ ⥤ C ⥤ C) (cwedge : RestrictedCowedge G H) (A : C) :
    HasCopowers.copower (diagApp H A) ((G.obj (op A)).obj A) ⟶ cwedge.pt :=
  HasCopowers.desc (cwedge.family A)

/-- Given a family of copower morphisms, extract the corresponding restricted
cowedge family. This uses the copower injections. -/
def copowerFamilyToRestrictedFamily [HasCopowers C] (H : Cᵒᵖ ⥤ C ⥤ Type v)
    (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    (ω : ∀ A, HasCopowers.copower (diagApp H A) ((G.obj (op A)).obj A) ⟶ pt)
    (A : C) : diagApp H A → ((G.obj (op A)).obj A ⟶ pt) :=
  fun h => HasCopowers.inj (diagApp H A) ((G.obj (op A)).obj A) h ≫ ω A

/-- Round-trip: restricted cowedge → copower family → restricted family equals
the original family. -/
theorem restrictedCowedge_roundtrip [HasCopowers C] (H : Cᵒᵖ ⥤ C ⥤ Type v)
    (G : Cᵒᵖ ⥤ C ⥤ C) (cwedge : RestrictedCowedge G H) (A : C) (h : diagApp H A) :
    copowerFamilyToRestrictedFamily H G cwedge.pt
      (restrictedCowedgeToCopowerFamily H G cwedge) A h = cwedge.family A h := by
  simp only [copowerFamilyToRestrictedFamily, restrictedCowedgeToCopowerFamily,
    HasCopowers.fac]

/-- Round-trip: copower family → restricted family → copower family equals
the original family (by uniqueness of copower factorization). -/
theorem copowerFamily_roundtrip [HasCopowers C] (H : Cᵒᵖ ⥤ C ⥤ Type v)
    (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    (ω : ∀ A, HasCopowers.copower (diagApp H A) ((G.obj (op A)).obj A) ⟶ pt)
    (hω : IsCopowerCowedgeDinatural H G pt ω) (A : C) :
    restrictedCowedgeToCopowerFamily H G
      (RestrictedCowedge.mk' pt (copowerFamilyToRestrictedFamily H G pt ω)
       (fun A' B g x => by
         simp only [copowerFamilyToRestrictedFamily, Profunctor.lmap, Profunctor.rmap,
           sliceProfunctor_obj_map, sliceProfunctor_map_app, Quiver.Hom.unop_op]
         exact hω A' B g x)) A = ω A := by
  apply HasCopowers.ext
  intro h
  simp only [restrictedCowedgeToCopowerFamily, RestrictedCowedge.mk',
    RestrictedCowedge.family, copowerFamilyToRestrictedFamily, HasCopowers.fac]

/-- The restricted coend `Σ(H, G)` satisfies the universal property of the coend
of the copower profunctor `∫^A H(A,A) · G(A,A)`.

Assuming copowers exist, the restricted coend is (isomorphic to) the ordinary
coend of `(A, B) ↦ H(A, B) · G(A, B)`. The isomorphism follows from the
equivalence between H-restricted G-cowedges and cowedges of the copower
profunctor, induced by the copower adjunction `Hom(S · X, Y) ≅ (S → Hom(X, Y))`.
-/
theorem restrictedCoend_is_copowerCoend [HasCopowers C] (H : Cᵒᵖ ⥤ C ⥤ Type v)
    (G : Cᵒᵖ ⥤ C ⥤ C) [HasRestrictedCoend G H] :
    ∀ (pt : C) (ω : ∀ A, HasCopowers.copower (diagApp H A)
                         ((G.obj (op A)).obj A) ⟶ pt),
    IsCopowerCowedgeDinatural H G pt ω →
    ∃! f : (restrictedCoend G H).pt ⟶ pt,
      ∀ A (h : diagApp H A),
        (restrictedCoend G H).family A h ≫ f =
        HasCopowers.inj _ _ h ≫ ω A := by
  intro pt ω hω
  let Φ : ∀ A, diagApp H A → ((G.obj (op A)).obj A ⟶ pt) :=
    copowerFamilyToRestrictedFamily H G pt ω
  let targetCwedge : RestrictedCowedge G H := {
    pt := pt
    toRestrictedCowedgeOver := ⟨Φ, by
      intro A B g x
      simp only [Profunctor.lmap, Profunctor.rmap,
        sliceProfunctor_obj_map, sliceProfunctor_map_app, Quiver.Hom.unop_op]
      simp only [Φ, copowerFamilyToRestrictedFamily]
      exact hω A B g x⟩
  }
  use (restrictedCoendIsInitial G H).descHom targetCwedge
  constructor
  · intro A h
    have := ((restrictedCoendIsInitial G H).to targetCwedge).comm A h
    simp only [targetCwedge, Φ] at this
    exact this
  · intro g hg
    let gMor : RestrictedCowedge.Hom (restrictedCoend G H) targetCwedge := {
      hom := g
      comm := fun A h => by
        simp only [targetCwedge, Φ]
        exact hg A h
    }
    have eq := Limits.IsInitial.hom_ext (restrictedCoendIsInitial G H)
      gMor ((restrictedCoendIsInitial G H).to targetCwedge)
    exact congrArg RestrictedCowedge.Hom.hom eq

end CopowerCoendEquivalence

end GebLean
