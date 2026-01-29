import GebLean.Paranatural
import GebLean.WeightedAlg
import GebLean.Utilities.Elements
import GebLean.Utilities.PowersAndCopowers

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

section HomToProfAndYoneda

/-!
## HomToProf pt and yoneda.obj pt

The profunctor `HomToProf pt : Cᵒᵖ ⥤ C ⥤ Type v` is constant in its second
argument. Its diagonal `diagApp (HomToProf pt) A = (A ⟶ pt)` equals
`(yoneda.obj pt).obj (op A)`.

Thus the diagonal of `HomToProf pt` is just `yoneda.obj pt` (the contravariant
hom-functor into pt).
-/

/-- The diagonal of `HomToProf pt` at any object equals the Yoneda embedding
evaluated at that object. -/
theorem HomToProf_diagApp_eq (pt A : C) :
    diagApp (HomToProf pt) A = (yoneda.obj pt).obj (op A) := rfl

end HomToProfAndYoneda

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

/-- A restricted cowedge from G with weight H induces a family of morphisms
indexed by the objects of `DiagElem H`, the category of diagonal elements of H.

For an endoprofunctor `H : Cᵒᵖ ⥤ C ⥤ Type v`, `DiagElem H` is the category
where objects are pairs `(A, h)` with `A : C` and `h : diagApp H A`, and
morphisms are morphisms `f : A → B` in C satisfying the diagonal compatibility
condition.

Given a restricted cowedge `(pt, Φ)` where `Φ_A : H(A, A) → C(G(A, A), pt)`,
we get for each object `x : DiagElem H` a morphism
`Φ x.base x.elem : G(x.base, x.base) → pt`.

The dinaturality of Φ provides a compatibility condition with respect to
morphisms in `DiagElem H`.
-/
structure RestrictedCowedgeCoconeData (H : Cᵒᵖ ⥤ C ⥤ Type v) (cwedge : RestrictedCowedge G H)
    where
  /-- For each object of `DiagElem H`, the map to the apex. -/
  leg : (x : DiagElem H) → (G.obj (op x.base)).obj x.base ⟶ cwedge.pt
  /-- The leg equals the cowedge family. -/
  leg_eq : ∀ x, leg x = cwedge.family x.base x.elem

/-- Convert a restricted cowedge to its cocone data over `DiagElem H`. -/
def RestrictedCowedge.toCoconeData (H : Cᵒᵖ ⥤ C ⥤ Type v) (cwedge : RestrictedCowedge G H) :
    RestrictedCowedgeCoconeData G H cwedge where
  leg x := cwedge.family x.base x.elem
  leg_eq _ := rfl

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

section CopowerProfunctor

/-!
### The Copower Profunctor

For profunctors `H : Cᵒᵖ ⥤ C ⥤ Type v` and `G : Cᵒᵖ ⥤ C ⥤ C`, the copower
profunctor `copowerProf H G : Cᵒᵖ ⥤ C ⥤ C` is defined by:

  `(copowerProf H G)(A, B) = H(A, B) · G(A, B)`

where `·` denotes the copower. The functorial actions are:
- Contravariant in first arg: uses `H.map f.op` on indices, `G.map f.op` on values
- Covariant in second arg: uses `H.obj (op A).map g` on indices, `G.obj (op A).map g` on values
-/

open HasCopowers

variable {C : Type u} [Category.{v} C] [HasCopowers C]

/-- The inner functor of the copower profunctor: for fixed `A`, this is a
functor `C ⥤ C` sending `B` to `H(A, B) · G(A, B)`. -/
def copowerProfInner (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C) (A : Cᵒᵖ) :
    C ⥤ C where
  obj B := copower ((H.obj A).obj B) ((G.obj A).obj B)
  map {B₁ B₂} g := bimap ((H.obj A).map g) ((G.obj A).map g)
  map_id B := by simp only [Functor.map_id]; exact bimap_id
  map_comp {B₁ B₂ B₃} f g := by
    simp only [Functor.map_comp]
    exact bimap_comp _ _ _ _

/-- The copower profunctor `copowerProf H G : Cᵒᵖ ⥤ C ⥤ C` defined by
`(copowerProf H G)(A, B) = H(A, B) · G(A, B)`. -/
def copowerProf (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C) : Cᵒᵖ ⥤ C ⥤ C where
  obj A := copowerProfInner H G A
  map {A₁ A₂} f := {
    app := fun B => bimap ((H.map f).app B) ((G.map f).app B)
    naturality := fun {B₁ B₂} g => by
      apply ext
      intro s
      simp only [copowerProfInner]
      -- Goal: bimap (H_1.map g) (G_1.map g) ≫ bimap (H.map f).app (G.map f).app =
      --       bimap (H.map f).app (G.map f).app ≫ bimap (H_2.map g) (G_2.map g)
      -- where H_1 = H.obj A₁, G_1 = G.obj A₁, H_2 = H.obj A₂, G_2 = G.obj A₂
      rw [← bimap_comp, ← bimap_comp]
      -- Now we need: bimap ((H.map f).app ∘ (H.obj A₁).map g) ((G.obj A₁).map g ≫ (G.map f).app) =
      --              bimap ((H.obj A₂).map g ∘ (H.map f).app) ((G.map f).app ≫ (G.obj A₂).map g)
      have hH : (H.map f).app B₂ ∘ (H.obj A₁).map g = (H.obj A₂).map g ∘ (H.map f).app B₁ := by
        ext x
        exact congrFun ((H.map f).naturality g) x
      have hG : (G.obj A₁).map g ≫ (G.map f).app B₂ = (G.map f).app B₁ ≫ (G.obj A₂).map g :=
        (G.map f).naturality g
      rw [hH, hG]
  }
  map_id A := by
    ext B
    simp only [Functor.map_id, NatTrans.id_app, copowerProfInner]
    exact bimap_id
  map_comp {A₁ A₂ A₃} f g := by
    ext B
    simp only [Functor.map_comp, NatTrans.comp_app, copowerProfInner]
    exact bimap_comp _ _ _ _

@[simp]
theorem copowerProf_obj_obj (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C) (A : Cᵒᵖ) (B : C) :
    ((copowerProf H G).obj A).obj B = copower ((H.obj A).obj B) ((G.obj A).obj B) := rfl

@[simp]
theorem copowerProf_obj_map (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C)
    (A : Cᵒᵖ) {B₁ B₂ : C} (g : B₁ ⟶ B₂) :
    ((copowerProf H G).obj A).map g = bimap ((H.obj A).map g) ((G.obj A).map g) := rfl

@[simp]
theorem copowerProf_map_app (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C)
    {A₁ A₂ : Cᵒᵖ} (f : A₁ ⟶ A₂) (B : C) :
    ((copowerProf H G).map f).app B = bimap ((H.map f).app B) ((G.map f).app B) := rfl

end CopowerProfunctor

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

section CowedgeCorrespondence

/-!
### Correspondence between mathlib Cowedges and IsCopowerCowedgeDinatural

This section establishes the equivalence between:
1. `Cowedge (copowerProf H G)` - mathlib's standard cowedge structure over the
   copower profunctor
2. `IsCopowerCowedgeDinatural H G pt ω` - our ad-hoc dinaturality condition

The correspondence is mediated by copower extensionality: the mathlib dinaturality
condition `bimap f g ≫ ι i = bimap f' g' ≫ ι j` is equivalent to the pointwise
condition `g ≫ inj(f x) ≫ ι i = g' ≫ inj(f' x) ≫ ι j` for all indices `x`.
-/

open HasCopowers Limits

variable {C : Type u} [Category.{v} C] [HasCopowers C]

/-- The mathlib dinaturality condition for `Cowedge (copowerProf H G)` implies
`IsCopowerCowedgeDinatural`. -/
theorem cowedge_dinatural_implies_copowerCowedgeDinatural
    (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    (ω : ∀ A, copower (diagApp H A) ((G.obj (op A)).obj A) ⟶ pt)
    (hω : ∀ ⦃i j : C⦄ (f : i ⟶ j),
      ((copowerProf H G).map f.op).app i ≫ ω i =
      ((copowerProf H G).obj (op j)).map f ≫ ω j) :
    IsCopowerCowedgeDinatural H G pt ω := by
  intro A B g x
  have h := hω g
  simp only [copowerProf_map_app, copowerProf_obj_map] at h
  have lhs : inj _ _ x ≫ bimap ((H.map g.op).app A) ((G.map g.op).app A) ≫ ω A =
      (G.map g.op).app A ≫ inj _ _ ((H.map g.op).app A x) ≫ ω A := by
    rw [← Category.assoc, bimap_inj]
    rw [Category.assoc]
  have rhs : inj _ _ x ≫ bimap ((H.obj (op B)).map g) ((G.obj (op B)).map g) ≫ ω B =
      (G.obj (op B)).map g ≫ inj _ _ ((H.obj (op B)).map g x) ≫ ω B := by
    rw [← Category.assoc, bimap_inj]
    rw [Category.assoc]
  calc (G.obj (op B)).map g ≫ inj _ _ ((H.obj (op B)).map g x) ≫ ω B
      = inj _ _ x ≫ bimap ((H.obj (op B)).map g) ((G.obj (op B)).map g) ≫ ω B := rhs.symm
    _ = inj _ _ x ≫ bimap ((H.map g.op).app A) ((G.map g.op).app A) ≫ ω A := by
        rw [← h]
    _ = (G.map g.op).app A ≫ inj _ _ ((H.map g.op).app A x) ≫ ω A := lhs

/-- `IsCopowerCowedgeDinatural` implies the mathlib dinaturality condition for
`Cowedge (copowerProf H G)`. -/
theorem copowerCowedgeDinatural_implies_cowedge_dinatural
    (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    (ω : ∀ A, copower (diagApp H A) ((G.obj (op A)).obj A) ⟶ pt)
    (hω : IsCopowerCowedgeDinatural H G pt ω) :
    ∀ ⦃i j : C⦄ (f : i ⟶ j),
      ((copowerProf H G).map f.op).app i ≫ ω i =
      ((copowerProf H G).obj (op j)).map f ≫ ω j := by
  intro i j f
  simp only [copowerProf_map_app, copowerProf_obj_map]
  apply ext
  intro x
  have h := hω i j f x
  have lhs_eq : inj _ _ x ≫ bimap ((H.map f.op).app i) ((G.map f.op).app i) ≫ ω i =
      (G.map f.op).app i ≫ inj _ _ ((H.map f.op).app i x) ≫ ω i := by
    rw [← Category.assoc, bimap_inj, Category.assoc]
  have rhs_eq : inj _ _ x ≫ bimap ((H.obj (op j)).map f) ((G.obj (op j)).map f) ≫ ω j =
      (G.obj (op j)).map f ≫ inj _ _ ((H.obj (op j)).map f x) ≫ ω j := by
    rw [← Category.assoc, bimap_inj, Category.assoc]
  rw [lhs_eq, h.symm, ← rhs_eq]

/-- Construct a mathlib `Cowedge (copowerProf H G)` from a family satisfying
`IsCopowerCowedgeDinatural`. -/
def copowerCowedge (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    (ω : ∀ A, copower (diagApp H A) ((G.obj (op A)).obj A) ⟶ pt)
    (hω : IsCopowerCowedgeDinatural H G pt ω) :
    Cowedge (copowerProf H G) :=
  Cowedge.mk pt ω (copowerCowedgeDinatural_implies_cowedge_dinatural H G pt ω hω)

/-- The apex of the cowedge. -/
@[simp]
theorem copowerCowedge_pt (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    (ω : ∀ A, copower (diagApp H A) ((G.obj (op A)).obj A) ⟶ pt)
    (hω : IsCopowerCowedgeDinatural H G pt ω) :
    (copowerCowedge H G pt ω hω).pt = pt := rfl

/-- The legs of the cowedge match the original family. -/
@[simp]
theorem copowerCowedge_π (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    (ω : ∀ A, copower (diagApp H A) ((G.obj (op A)).obj A) ⟶ pt)
    (hω : IsCopowerCowedgeDinatural H G pt ω) (A : C) :
    (copowerCowedge H G pt ω hω).π A = ω A := rfl

/-- Extract a family satisfying `IsCopowerCowedgeDinatural` from a mathlib
`Cowedge (copowerProf H G)`. -/
def cowedgeToCopowerFamily (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C)
    (cw : Cowedge (copowerProf H G)) (A : C) :
    copower (diagApp H A) ((G.obj (op A)).obj A) ⟶ cw.pt :=
  cw.π A

/-- A mathlib cowedge over the copower profunctor satisfies
`IsCopowerCowedgeDinatural`. -/
theorem cowedge_is_copowerCowedgeDinatural (H : Cᵒᵖ ⥤ C ⥤ Type v) (G : Cᵒᵖ ⥤ C ⥤ C)
    (cw : Cowedge (copowerProf H G)) :
    IsCopowerCowedgeDinatural H G cw.pt (cowedgeToCopowerFamily H G cw) :=
  cowedge_dinatural_implies_copowerCowedgeDinatural H G cw.pt
    (cowedgeToCopowerFamily H G cw)
    (fun {_} {_} g => Cowedge.condition cw g)

end CowedgeCorrespondence

section MendlerCowedgeCorrespondence

/-!
### Mendler Algebras as Cowedges over the Copower Profunctor

A `MendlerAlgebra G` with carrier `pt` consists of:
- A family `Φ : ∀ A, (A → pt) → (G(A, A) → pt)`
- A dinaturality condition

This is exactly a `RestrictedCowedge G (HomToProf pt)` where the weight profunctor
is `H = HomToProf pt`.

By the correspondence established above, this is equivalent to a
`Cowedge (copowerProf (HomToProf pt) G)`, where the copower profunctor is:

  `(copowerProf (HomToProf pt) G)(A, B) = (A → pt) · G(A, B)`

The copower `(A → pt) · G(A, B)` can be understood as the coproduct of copies of
`G(A, B)`, one for each morphism `A → pt`.

This provides a direct connection between Mendler algebras and standard categorical
constructions (cowedges over a profunctor).
-/

open HasCopowers Limits

variable {C : Type u} [Category.{v} C] [HasCopowers C]

/-- Convert a restricted cowedge (with weight `HomToProf pt`) to a cowedge over
the copower profunctor. -/
def restrictedCowedgeToCopowerCowedge (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    (rc : RestrictedCowedge G (HomToProf pt)) :
    Cowedge (copowerProf (HomToProf pt) G) :=
  copowerCowedge (HomToProf pt) G rc.pt
    (restrictedCowedgeToCopowerFamily (HomToProf pt) G rc)
    (by
      intro A B g x
      have dinat := rc.isDinatural A B g x
      simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor_obj_map,
        sliceProfunctor_map_app, Quiver.Hom.unop_op] at dinat
      simp only [restrictedCowedgeToCopowerFamily]
      have lhs : (G.obj (op B)).map g ≫
          (inj _ _ (((HomToProf pt).obj (op B)).map g x) ≫ desc (rc.family B)) =
          (G.obj (op B)).map g ≫ rc.family B (((HomToProf pt).obj (op B)).map g x) := by
        rw [fac]
      have rhs : (G.map g.op).app A ≫
          (inj _ _ (((HomToProf pt).map g.op).app A x) ≫ desc (rc.family A)) =
          (G.map g.op).app A ≫ rc.family A (((HomToProf pt).map g.op).app A x) := by
        rw [fac]
      rw [lhs, dinat, ← rhs])

/-- Convert a cowedge over the copower profunctor to a restricted cowedge. -/
def copowerCowedgeToRestrictedCowedge (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    (cw : Cowedge (copowerProf (HomToProf pt) G)) :
    RestrictedCowedge G (HomToProf pt) :=
  RestrictedCowedge.mk' cw.pt
    (copowerFamilyToRestrictedFamily (HomToProf pt) G cw.pt (cowedgeToCopowerFamily _ _ cw))
    (by
      intro A B g x
      have dinat := cowedge_is_copowerCowedgeDinatural (HomToProf pt) G cw A B g x
      simp only [cowedgeToCopowerFamily] at dinat
      simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor_obj_map,
        sliceProfunctor_map_app, Quiver.Hom.unop_op,
        copowerFamilyToRestrictedFamily]
      exact dinat)

/-- The apex of the converted cowedge equals the original. -/
@[simp]
theorem restrictedCowedgeToCopowerCowedge_pt (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    (rc : RestrictedCowedge G (HomToProf pt)) :
    (restrictedCowedgeToCopowerCowedge G pt rc).pt = rc.pt := rfl

/-- The apex of the converted restricted cowedge equals the original. -/
@[simp]
theorem copowerCowedgeToRestrictedCowedge_pt (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    (cw : Cowedge (copowerProf (HomToProf pt) G)) :
    (copowerCowedgeToRestrictedCowedge G pt cw).pt = cw.pt := rfl

namespace Limits.Cocone

@[simp]
theorem category_comp_hom {J : Type*} [Category J] {C' : Type*} [Category C']
    {F : J ⥤ C'} {c₁ c₂ c₃ : Cocone F}
    (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) : (f ≫ g).hom = f.hom ≫ g.hom := rfl

@[simp]
theorem category_id_hom {J : Type*} [Category J] {C' : Type*} [Category C']
    {F : J ⥤ C'} (c : Cocone F) : (𝟙 c : c ⟶ c).hom = 𝟙 c.pt := rfl

/-- The `.hom` field of an `eqToHom` morphism between cocones equals `eqToHom` of
the corresponding equality of apex points. -/
@[simp]
theorem eqToHom_hom {J : Type*} [Category J] {C' : Type*} [Category C']
    {F : J ⥤ C'} {A B : Cocone F} (h : A = B) :
    (eqToHom h).hom = eqToHom (congrArg Cocone.pt h) := by subst h; rfl

end Limits.Cocone

namespace Limits.Cocones

/-- The `.hom` field of an `eqToHom` morphism between cocones equals `eqToHom` of
the corresponding equality of apex points. -/
@[simp]
theorem eqToHom_hom {J : Type*} [Category J] {C' : Type*} [Category C']
    {F : J ⥤ C'} {A B : Cocone F} (h : A = B) :
    (eqToHom h).hom = eqToHom (congrArg Cocone.pt h) := by subst h; rfl

end Limits.Cocones

namespace Limits

@[simp]
theorem Cowedge.category_comp_hom {J : Type*} [Category J] {C' : Type*} [Category C']
    {F : Jᵒᵖ ⥤ J ⥤ C'} {c₁ c₂ c₃ : Cowedge F}
    (f : c₁ ⟶ c₂) (g : c₂ ⟶ c₃) : (f ≫ g).hom = f.hom ≫ g.hom := rfl

@[simp]
theorem Cowedge.category_id_hom {J : Type*} [Category J] {C' : Type*} [Category C']
    {F : Jᵒᵖ ⥤ J ⥤ C'} (c : Cowedge F) : (𝟙 c : c ⟶ c).hom = 𝟙 c.pt := rfl

@[simp]
theorem Cowedge.eqToHom_hom {J : Type*} [Category J] {C' : Type*} [Category C']
    {F : Jᵒᵖ ⥤ J ⥤ C'} {A B : Cowedge F} (h : A = B) :
    (eqToHom h).hom = eqToHom (congrArg Cocone.pt h) := by subst h; rfl

end Limits

/-!
### Categorical Equivalence

The correspondence between restricted cowedges with weight `HomToProf pt` and
cowedges over the copower profunctor extends to a categorical equivalence.
-/

/-- Type alias for restricted cowedges with the Hom-to-pt weight. -/
abbrev HomRestrictedCowedge (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C) :=
  RestrictedCowedge G (HomToProf pt)

/-- Type alias for cowedges over the copower profunctor with Hom-to-pt weight. -/
abbrev HomCopowerCowedge (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C) :=
  Cowedge (copowerProf (HomToProf pt) G)

/-- Convert a morphism of restricted cowedges to a morphism of cowedges. -/
def restrictedCowedgeToCopowerCowedgeHom (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    {rc₁ rc₂ : HomRestrictedCowedge G pt}
    (f : RestrictedCowedge.Hom rc₁ rc₂) :
    (restrictedCowedgeToCopowerCowedge G pt rc₁) ⟶
    (restrictedCowedgeToCopowerCowedge G pt rc₂) where
  hom := f.hom
  w := fun j => by
    rcases j with a | b
    · -- left a case: follows from right case by precomposing with I.fst a
      simp only [Multicofork.fst_app_right, Category.assoc]
      congr 1
      simp only [restrictedCowedgeToCopowerCowedge, copowerCowedge, Cowedge.mk_π,
        restrictedCowedgeToCopowerFamily]
      exact desc_postcomp_eq (rc₁.family a.left) (rc₂.family a.left) f.hom
        (fun x => f.comm a.left x)
    · -- right b case: prove π-commutativity
      simp only [Multicofork.π_eq_app_right, restrictedCowedgeToCopowerCowedge,
        copowerCowedge, Cowedge.mk_π, restrictedCowedgeToCopowerFamily]
      exact desc_postcomp_eq (rc₁.family b) (rc₂.family b) f.hom (fun x => f.comm b x)

/-- Convert a morphism of cowedges to a morphism of restricted cowedges. -/
def copowerCowedgeToRestrictedCowedgeHom (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    {cw₁ cw₂ : HomCopowerCowedge G pt}
    (f : cw₁ ⟶ cw₂) :
    RestrictedCowedge.Hom (copowerCowedgeToRestrictedCowedge G pt cw₁)
      (copowerCowedgeToRestrictedCowedge G pt cw₂) where
  hom := f.hom
  comm := fun A x => by
    simp only [copowerCowedgeToRestrictedCowedge, RestrictedCowedge.mk',
      RestrictedCowedge.family, copowerFamilyToRestrictedFamily,
      cowedgeToCopowerFamily]
    rw [Category.assoc]
    have w := Multicofork.π_comp_hom cw₁ cw₂ f A
    calc inj _ _ x ≫ cw₁.π A ≫ f.hom = inj _ _ x ≫ cw₂.π A := by rw [w]

@[simp]
theorem restrictedCowedgeToCopowerCowedgeHom_hom (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    {rc₁ rc₂ : HomRestrictedCowedge G pt} (f : RestrictedCowedge.Hom rc₁ rc₂) :
    (restrictedCowedgeToCopowerCowedgeHom G pt f).hom = f.hom := rfl

@[simp]
theorem copowerCowedgeToRestrictedCowedgeHom_hom (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    {cw₁ cw₂ : HomCopowerCowedge G pt} (f : cw₁ ⟶ cw₂) :
    (copowerCowedgeToRestrictedCowedgeHom G pt f).hom = f.hom := rfl

/-- The functor from restricted cowedges to cowedges over the copower profunctor. -/
def homRestrictedToCopowerFunctor (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C) :
    HomRestrictedCowedge G pt ⥤ HomCopowerCowedge G pt where
  obj := restrictedCowedgeToCopowerCowedge G pt
  map := restrictedCowedgeToCopowerCowedgeHom G pt
  map_id := fun _ => by
    ext
    simp only [restrictedCowedgeToCopowerCowedgeHom]
    rfl
  map_comp := fun _ _ => by
    ext
    simp only [restrictedCowedgeToCopowerCowedgeHom]
    rfl

/-- The functor from cowedges over the copower profunctor to restricted cowedges. -/
def copowerToHomRestrictedFunctor (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C) :
    HomCopowerCowedge G pt ⥤ HomRestrictedCowedge G pt where
  obj := copowerCowedgeToRestrictedCowedge G pt
  map := copowerCowedgeToRestrictedCowedgeHom G pt
  map_id := fun _ => by
    apply RestrictedCowedge.Hom.ext
    simp only [copowerCowedgeToRestrictedCowedgeHom]
    rfl
  map_comp := fun _ _ => by
    apply RestrictedCowedge.Hom.ext
    simp only [copowerCowedgeToRestrictedCowedgeHom]
    rfl

/-- Round-trip from restricted cowedge to copower cowedge and back gives the
original restricted cowedge. -/
theorem copowerToRestricted_restrictedToCopower (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    (rc : HomRestrictedCowedge G pt) :
    copowerCowedgeToRestrictedCowedge G pt (restrictedCowedgeToCopowerCowedge G pt rc) = rc := by
  apply RestrictedCowedge.ext
  · rfl
  · apply heq_of_eq
    apply RestrictedCowedgeOver.ext
    funext A x
    simp only [copowerCowedgeToRestrictedCowedge, restrictedCowedgeToCopowerCowedge,
      copowerCowedge, RestrictedCowedge.mk', RestrictedCowedge.family,
      copowerFamilyToRestrictedFamily, cowedgeToCopowerFamily, Cowedge.mk_π,
      restrictedCowedgeToCopowerFamily]
    rw [fac]

/-- Round-trip from copower cowedge to restricted cowedge and back gives the
original copower cowedge. -/
theorem restrictedToCopower_copowerToRestricted (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)
    (cw : HomCopowerCowedge G pt) :
    restrictedCowedgeToCopowerCowedge G pt (copowerCowedgeToRestrictedCowedge G pt cw) = cw := by
  have hπ : ∀ A, (restrictedCowedgeToCopowerCowedge G pt
      (copowerCowedgeToRestrictedCowedge G pt cw)).π A = cw.π A := by
    intro A
    simp only [restrictedCowedgeToCopowerCowedge, copowerCowedgeToRestrictedCowedge,
      copowerCowedge, RestrictedCowedge.mk', Cowedge.mk_π, restrictedCowedgeToCopowerFamily]
    change desc (copowerFamilyToRestrictedFamily (HomToProf pt) G cw.pt
      (cowedgeToCopowerFamily (HomToProf pt) G cw) A) = cw.π A
    unfold copowerFamilyToRestrictedFamily cowedgeToCopowerFamily
    simp only [desc_inj]
  have hι : (restrictedCowedgeToCopowerCowedge G pt
      (copowerCowedgeToRestrictedCowedge G pt cw)).ι = cw.ι := by
    apply NatTrans.ext
    funext j
    cases j with
    | left a => simp only [Multicofork.fst_app_right, hπ]
    | right b => simp only [Multicofork.π_eq_app_right, hπ]
  -- Since pt is definitionally equal and ι is proven equal, use eta + hι
  have : (restrictedCowedgeToCopowerCowedge G pt
      (copowerCowedgeToRestrictedCowedge G pt cw)) =
      ⟨cw.pt, (restrictedCowedgeToCopowerCowedge G pt
        (copowerCowedgeToRestrictedCowedge G pt cw)).ι⟩ := rfl
  rw [this, hι]

/-- The unit isomorphism for the equivalence. -/
def homRestrictedCopowerUnitIso (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C) :
    𝟭 (HomRestrictedCowedge G pt) ≅
    homRestrictedToCopowerFunctor G pt ⋙ copowerToHomRestrictedFunctor G pt :=
  NatIso.ofComponents
    (fun rc => eqToIso (copowerToRestricted_restrictedToCopower G pt rc).symm)
    (fun {rc₁ rc₂} f => by
      apply RestrictedCowedge.Hom.ext
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
        homRestrictedToCopowerFunctor, copowerToHomRestrictedFunctor,
        restrictedCowedgeToCopowerCowedgeHom, copowerCowedgeToRestrictedCowedgeHom,
        eqToIso.hom]
      simp only [RestrictedCowedgeCat, RestrictedCowedge.Hom.comp_hom,
        RestrictedCowedge_eqToHom_hom, copowerCowedgeToRestrictedCowedge_pt,
        restrictedCowedgeToCopowerCowedge_pt, eqToHom_refl, Category.id_comp, Category.comp_id])

/-- The counit isomorphism for the equivalence. -/
def homRestrictedCopowerCounitIso (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C) :
    copowerToHomRestrictedFunctor G pt ⋙ homRestrictedToCopowerFunctor G pt ≅
    𝟭 (HomCopowerCowedge G pt) :=
  NatIso.ofComponents
    (fun cw => eqToIso (restrictedToCopower_copowerToRestricted G pt cw))
    (fun {cw₁ cw₂} f => by
      apply Limits.CoconeMorphism.ext
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map,
        copowerToHomRestrictedFunctor, homRestrictedToCopowerFunctor,
        copowerCowedgeToRestrictedCowedgeHom, restrictedCowedgeToCopowerCowedgeHom,
        eqToIso.hom, Limits.Cocone.category_comp_hom, Limits.Cocones.eqToHom_hom,
        copowerCowedgeToRestrictedCowedge_pt, restrictedCowedgeToCopowerCowedge_pt,
        eqToHom_refl, Category.id_comp, Category.comp_id])

/-- The categorical equivalence between restricted cowedges with weight `HomToProf pt`
and cowedges over the copower profunctor. -/
def homRestrictedCopowerEquiv (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C) :
    HomRestrictedCowedge G pt ≌ HomCopowerCowedge G pt where
  functor := homRestrictedToCopowerFunctor G pt
  inverse := copowerToHomRestrictedFunctor G pt
  unitIso := homRestrictedCopowerUnitIso G pt
  counitIso := homRestrictedCopowerCounitIso G pt
  functor_unitIso_comp X := by
    apply Limits.CoconeMorphism.ext
    simp only [homRestrictedCopowerUnitIso, homRestrictedCopowerCounitIso,
      homRestrictedToCopowerFunctor, copowerToHomRestrictedFunctor,
      NatIso.ofComponents_hom_app, eqToIso.hom, Functor.comp_obj,
      restrictedCowedgeToCopowerCowedgeHom, Limits.Cocone.category_comp_hom,
      Limits.Cocone.category_id_hom, Limits.Cocones.eqToHom_hom,
      copowerCowedgeToRestrictedCowedge_pt, restrictedCowedgeToCopowerCowedge_pt,
      eqToHom_refl, Category.comp_id, RestrictedCowedgeCat,
      RestrictedCowedge_eqToHom_hom]
    rfl

/-- The categorical isomorphism between restricted cowedges with weight
`HomToProf pt` and cowedges over the copower profunctor.
This strengthens `homRestrictedCopowerEquiv` from an equivalence to an
isomorphism, which is possible because the round-trips are equalities. -/
def homRestrictedCopowerIso (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C) :
    HomRestrictedCowedge G pt ≅Cat HomCopowerCowedge G pt :=
  Cat.isoOfEquiv (homRestrictedCopowerEquiv G pt)
    (copowerToRestricted_restrictedToCopower G pt)
    (restrictedToCopower_copowerToRestricted G pt)

end MendlerCowedgeCorrespondence

section HomRestrictedWeightedEquivalence

/-!
### Categorical Equivalence between HomRestrictedCowedge and HomWeightedCowedge

The round-trip theorems `restrict_extend_roundtrip` and `extend_restrict_roundtrip`
from `WeightedAlg` establish that restriction and extension are inverse bijections
for cowedges with weight `HomToProf pt`.

For weight `HomToProf pt`, the weight type at any co-twisted arrow is
`cod ⟶ pt`, which is independent of the covariant variable.  This allows
unique extension from diagonal data.
-/

variable {C : Type u} [Category.{v} C]
variable (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)

/-- Type alias for weighted cowedges with the Hom-to-pt weight. -/
abbrev HomWeightedCowedge (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C) :=
  WeightedCowedge (HomToProf pt) G

/-- The point of a restricted-to-weighted extension equals the input point. -/
@[simp]
theorem restrictedCowedgeToWeightedCowedge_pt (rc : HomRestrictedCowedge G pt) :
    (extendRestrictedCowedgeFull' (G := G) pt rc).pt = rc.pt := rfl

/-- The point of a weighted-to-restricted restriction equals the input point. -/
@[simp]
theorem weightedCowedgeToRestrictedCowedge_pt (wc : HomWeightedCowedge G pt) :
    (restrictWeightedCowedge (HomToProf pt) G wc).pt = wc.pt := rfl

/-- Convert a morphism of restricted cowedges to a morphism of weighted cowedges. -/
def restrictedCowedgeToWeightedCowedgeHom
    {rc₁ rc₂ : HomRestrictedCowedge G pt}
    (f : RestrictedCowedge.Hom rc₁ rc₂) :
    (extendRestrictedCowedgeFull' (G := G) pt rc₁) ⟶
    (extendRestrictedCowedgeFull' (G := G) pt rc₂) where
  hom := f.hom
  w := fun tw γ => by
    simp only [extendRestrictedCowedgeFull', extendRestrictedCowedge', WeightedCocone.leg]
    unfold extendMendlerLeg'
    simp only [eqToHom_refl, Category.id_comp, Category.assoc, cast_eq]
    rw [f.comm]

/-- Convert a morphism of weighted cowedges to a morphism of restricted cowedges. -/
def weightedCowedgeToRestrictedCowedgeHom
    {wc₁ wc₂ : HomWeightedCowedge G pt}
    (f : wc₁ ⟶ wc₂) :
    RestrictedCowedge.Hom (restrictWeightedCowedge (HomToProf pt) G wc₁)
      (restrictWeightedCowedge (HomToProf pt) G wc₂) where
  hom := f.hom
  comm := fun A x => by
    simp only [restrictWeightedCowedge, RestrictedCowedge.family,
      weightedCowedgeFamilyAtIdentity, Category.assoc]
    have w := f.w (idCoTwistedArrow A) (diagAppToWeightAtIdentity (HomToProf pt) A x)
    simp only [WeightedCocone.leg] at w
    simp only [WeightedCocone.leg, w]

/-- The functor from restricted cowedges to weighted cowedges. -/
def homRestrictedToWeightedFunctor :
    HomRestrictedCowedge G pt ⥤ HomWeightedCowedge G pt where
  obj rc := extendRestrictedCowedgeFull' (G := G) pt rc
  map := restrictedCowedgeToWeightedCowedgeHom G pt
  map_id := fun _ => by
    apply WeightedCocone.Hom.ext
    simp only [restrictedCowedgeToWeightedCowedgeHom]
    rfl
  map_comp := fun _ _ => by
    apply WeightedCocone.Hom.ext
    simp only [restrictedCowedgeToWeightedCowedgeHom]
    rfl

/-- The functor from weighted cowedges to restricted cowedges. -/
def weightedToHomRestrictedFunctor :
    HomWeightedCowedge G pt ⥤ HomRestrictedCowedge G pt where
  obj wc := restrictWeightedCowedge (HomToProf pt) G wc
  map := weightedCowedgeToRestrictedCowedgeHom G pt
  map_id := fun _ => by
    apply RestrictedCowedge.Hom.ext
    simp only [weightedCowedgeToRestrictedCowedgeHom]
    rfl
  map_comp := fun _ _ => by
    apply RestrictedCowedge.Hom.ext
    simp only [weightedCowedgeToRestrictedCowedgeHom]
    rfl

/-- Round-trip from restricted cowedge to weighted cowedge and back gives the
original restricted cowedge. -/
theorem weightedToRestricted_restrictedToWeighted (rc : HomRestrictedCowedge G pt) :
    restrictWeightedCowedge (HomToProf pt) G
      (extendRestrictedCowedgeFull' (G := G) pt rc) = rc := by
  exact restrict_extend_roundtrip' (G := G) pt rc

/-- Round-trip from weighted cowedge to restricted cowedge and back gives the
original weighted cowedge. -/
theorem restrictedToWeighted_weightedToRestricted (wc : HomWeightedCowedge G pt) :
    extendRestrictedCowedgeFull' (G := G) pt
      (restrictWeightedCowedge (HomToProf pt) G wc) = wc := by
  exact extend_restrict_roundtrip' (G := G) pt wc

/-- The unit isomorphism for the equivalence. -/
def homRestrictedWeightedUnitIso :
    𝟭 (HomRestrictedCowedge G pt) ≅
    homRestrictedToWeightedFunctor G pt ⋙ weightedToHomRestrictedFunctor G pt :=
  NatIso.ofComponents
    (fun rc => eqToIso (weightedToRestricted_restrictedToWeighted G pt rc).symm)
    (fun {rc₁ rc₂} f => by
      apply RestrictedCowedge.Hom.ext
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
        homRestrictedToWeightedFunctor, weightedToHomRestrictedFunctor,
        restrictedCowedgeToWeightedCowedgeHom, weightedCowedgeToRestrictedCowedgeHom,
        eqToIso.hom]
      simp only [RestrictedCowedgeCat, RestrictedCowedge.Hom.comp_hom,
        RestrictedCowedge_eqToHom_hom, weightedCowedgeToRestrictedCowedge_pt,
        restrictedCowedgeToWeightedCowedge_pt, eqToHom_refl, Category.id_comp, Category.comp_id])

/-- The counit isomorphism for the equivalence. -/
def homRestrictedWeightedCounitIso :
    weightedToHomRestrictedFunctor G pt ⋙ homRestrictedToWeightedFunctor G pt ≅
    𝟭 (HomWeightedCowedge G pt) :=
  NatIso.ofComponents
    (fun wc => eqToIso (restrictedToWeighted_weightedToRestricted G pt wc))
    (fun {wc₁ wc₂} f => by
      apply WeightedCocone.Hom.ext
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map,
        weightedToHomRestrictedFunctor, homRestrictedToWeightedFunctor,
        weightedCowedgeToRestrictedCowedgeHom, restrictedCowedgeToWeightedCowedgeHom,
        eqToIso.hom, WeightedCocone.category_comp_hom, WeightedCocone.eqToHom_hom,
        restrictedCowedgeToWeightedCowedge_pt, weightedCowedgeToRestrictedCowedge_pt,
        eqToHom_refl, Category.id_comp, Category.comp_id])

/-- The categorical equivalence between restricted cowedges with weight
`HomToProf pt` and weighted cowedges with the same weight.
This formalizes that for the special case of `HomToProf pt`, restriction
to diagonal elements is an equivalence, not just a faithful functor. -/
def homRestrictedWeightedEquiv :
    HomRestrictedCowedge G pt ≌ HomWeightedCowedge G pt where
  functor := homRestrictedToWeightedFunctor G pt
  inverse := weightedToHomRestrictedFunctor G pt
  unitIso := homRestrictedWeightedUnitIso G pt
  counitIso := homRestrictedWeightedCounitIso G pt
  functor_unitIso_comp X := by
    apply WeightedCocone.Hom.ext
    simp only [homRestrictedWeightedUnitIso, homRestrictedWeightedCounitIso,
      homRestrictedToWeightedFunctor, weightedToHomRestrictedFunctor,
      NatIso.ofComponents_hom_app, eqToIso.hom, Functor.comp_obj, Functor.id_obj,
      restrictedCowedgeToWeightedCowedgeHom, WeightedCocone.category_comp_hom,
      WeightedCocone.category_id_hom, WeightedCocone.eqToHom_hom,
      restrictedCowedgeToWeightedCowedge_pt, weightedCowedgeToRestrictedCowedge_pt,
      eqToHom_refl, Category.comp_id, RestrictedCowedgeCat,
      RestrictedCowedge_eqToHom_hom]

/-- The categorical isomorphism between restricted cowedges with weight
`HomToProf pt` and weighted cowedges with the same weight.
This strengthens `homRestrictedWeightedEquiv` from an equivalence to an
isomorphism, which is possible because the round-trips are equalities. -/
def homRestrictedWeightedIso :
    HomRestrictedCowedge G pt ≅Cat HomWeightedCowedge G pt :=
  Cat.isoOfEquiv (homRestrictedWeightedEquiv G pt)
    (weightedToRestricted_restrictedToWeighted G pt)
    (restrictedToWeighted_weightedToRestricted G pt)

end HomRestrictedWeightedEquivalence

section HomStrongRestrictedEquivalence

/-!
### Categorical Equivalence between HomRestrictedCowedge and HomStrongRestrictedCowedge

For the weight `HomToProf pt`, dinaturality implies paranaturality. This is
because every DiagCompat pair factors through an off-diagonal element:

For `HomToProf pt`:
- The rmap is identity: `((HomToProf pt).obj (op A)).map g h = h`
- The lmap is precomposition: `((HomToProf pt).map f).app B h = f.unop ≫ h`

So `DiagCompat (HomToProf pt) A B f a b` holds iff `a = f ≫ b`, which is exactly
the form that arises from off-diagonal elements in dinaturality. This allows us
to upgrade any `HomRestrictedCowedge` to a `HomStrongRestrictedCowedge`.
-/

variable {C : Type u} [Category.{v} C]
variable (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C)

/-- Type alias for strong restricted cowedges with the Hom-to-pt weight. -/
abbrev HomStrongRestrictedCowedge (G : Cᵒᵖ ⥤ C ⥤ C) (pt : C) :=
  StrongRestrictedCowedge G (HomToProf pt)

/-- For `HomToProf pt`, `DiagCompat` is equivalent to the condition `a = f ≫ b`.
This is because the rmap is identity and the lmap is precomposition. -/
theorem HomToProf_DiagCompat_iff {A B : C} (f : A ⟶ B) (a : A ⟶ pt) (b : B ⟶ pt) :
    DiagCompat (HomToProf pt) A B f a b ↔ a = f ≫ b := by
  constructor
  · intro h
    simp only [DiagCompat, HomToProf_obj_map, HomToProf_map_app, Quiver.Hom.unop_op] at h
    exact h
  · intro h
    simp only [DiagCompat, HomToProf_obj_map, HomToProf_map_app, Quiver.Hom.unop_op]
    exact h

/-- For `HomToProf pt`, every DiagCompat pair factors through an off-diagonal
element. Given `a : A ⟶ pt`, `b : B ⟶ pt`, and `f : A ⟶ B` with `a = f ≫ b`,
the element `b : (B ⟶ pt) = ((HomToProf pt).obj (op B)).obj A` witnesses the
factorization. -/
theorem HomToProf_DiagCompat_factors {A B : C} (f : A ⟶ B) (a : A ⟶ pt) (b : B ⟶ pt)
    (h : DiagCompat (HomToProf pt) A B f a b) :
    ∃ (x : ((HomToProf pt).obj (Opposite.op B)).obj A),
      ((HomToProf pt).map f.op).app A x = a ∧
      ((HomToProf pt).obj (Opposite.op B)).map f x = b := by
  rw [HomToProf_DiagCompat_iff] at h
  use b
  simp only [HomToProf_map_app, Quiver.Hom.unop_op, HomToProf_obj_map, and_true]
  exact h.symm

/-- For `HomToProf pt`, dinaturality implies paranaturality. This holds because
every DiagCompat pair factors through an off-diagonal element, so the
paranaturality condition follows from the dinaturality condition.
The `apex` parameter is the carrier of the cowedge, which is independent of the
`pt` parameter in the weight `HomToProf pt`. -/
theorem HomToProf_dinatural_implies_paranatural (apex : C)
    (family : ParanatSig (HomToProf pt) (G ⇓ apex))
    (hdinat : IsDinatural (HomToProf pt) (G ⇓ apex) family) :
    IsParanatural (HomToProf pt) (G ⇓ apex) family := by
  intro A B f a b hcompat
  obtain ⟨x, ha, hb⟩ := HomToProf_DiagCompat_factors pt f a b hcompat
  have dinat := hdinat A B f x
  simp only [Profunctor.lmap, Profunctor.rmap, HomToProf_map_app, HomToProf_obj_map,
    Quiver.Hom.unop_op, sliceProfunctor_obj_map, sliceProfunctor_map_app] at dinat
  simp only [DiagCompat, sliceProfunctor_obj_map, sliceProfunctor_map_app, Quiver.Hom.unop_op]
  simp only [HomToProf_map_app, HomToProf_obj_map, Quiver.Hom.unop_op] at ha hb
  rw [← ha, ← hb]
  exact dinat.symm

/-- Upgrade a `HomRestrictedCowedge` to a `HomStrongRestrictedCowedge` using the
fact that dinaturality implies paranaturality for `HomToProf pt`. -/
def upgradeToStrongRestrictedCowedge (rc : HomRestrictedCowedge G pt) :
    HomStrongRestrictedCowedge G pt where
  pt := rc.pt
  toStrongRestrictedCowedgeOver := {
    family := rc.family
    isParanatural := HomToProf_dinatural_implies_paranatural G pt rc.pt rc.family rc.isDinatural
  }

/-- The point of an upgraded strong restricted cowedge equals the input point. -/
@[simp]
theorem upgradeToStrongRestrictedCowedge_pt (rc : HomRestrictedCowedge G pt) :
    (upgradeToStrongRestrictedCowedge G pt rc).pt = rc.pt := rfl

/-- The family of an upgraded strong restricted cowedge equals the input family. -/
@[simp]
theorem upgradeToStrongRestrictedCowedge_family (rc : HomRestrictedCowedge G pt) :
    (upgradeToStrongRestrictedCowedge G pt rc).family = rc.family := rfl

/-- Round-trip from restricted cowedge to strong restricted cowedge and back
gives the original restricted cowedge. -/
theorem inclusion_upgrade_roundtrip (rc : HomRestrictedCowedge G pt) :
    (StrongRestrictedCowedge.inclusion G (HomToProf pt)).obj
      (upgradeToStrongRestrictedCowedge G pt rc) = rc := by
  apply RestrictedCowedge.ext
  · rfl
  · apply heq_of_eq
    apply RestrictedCowedgeOver.ext
    rfl

/-- Round-trip from strong restricted cowedge to restricted cowedge and back
gives the original strong restricted cowedge. -/
theorem upgrade_inclusion_roundtrip (src : HomStrongRestrictedCowedge G pt) :
    upgradeToStrongRestrictedCowedge G pt
      ((StrongRestrictedCowedge.inclusion G (HomToProf pt)).obj src) = src := by
  apply StrongRestrictedCowedge.ext
  · rfl
  · apply heq_of_eq
    apply StrongRestrictedCowedgeOver.ext
    rfl

/-- Convert a morphism of restricted cowedges to a morphism of strong
restricted cowedges. -/
def restrictedCowedgeToStrongCowedgeHom
    {rc₁ rc₂ : HomRestrictedCowedge G pt}
    (f : RestrictedCowedge.Hom rc₁ rc₂) :
    StrongRestrictedCowedge.Hom (upgradeToStrongRestrictedCowedge G pt rc₁)
      (upgradeToStrongRestrictedCowedge G pt rc₂) where
  hom := f.hom
  comm := f.comm

/-- Convert a morphism of strong restricted cowedges to a morphism of
restricted cowedges. -/
def strongCowedgeToRestrictedCowedgeHom
    {src₁ src₂ : HomStrongRestrictedCowedge G pt}
    (f : StrongRestrictedCowedge.Hom src₁ src₂) :
    RestrictedCowedge.Hom
      ((StrongRestrictedCowedge.inclusion G (HomToProf pt)).obj src₁)
      ((StrongRestrictedCowedge.inclusion G (HomToProf pt)).obj src₂) where
  hom := f.hom
  comm := f.comm

/-- The functor from restricted cowedges to strong restricted cowedges. -/
def homRestrictedToStrongFunctor :
    HomRestrictedCowedge G pt ⥤ HomStrongRestrictedCowedge G pt where
  obj := upgradeToStrongRestrictedCowedge G pt
  map := restrictedCowedgeToStrongCowedgeHom G pt
  map_id := fun _ => by
    apply StrongRestrictedCowedge.Hom.ext
    simp only [restrictedCowedgeToStrongCowedgeHom]
    rfl
  map_comp := fun _ _ => by
    apply StrongRestrictedCowedge.Hom.ext
    simp only [restrictedCowedgeToStrongCowedgeHom]
    rfl

/-- The functor from strong restricted cowedges to restricted cowedges is
the inclusion. -/
abbrev strongToHomRestrictedFunctor :
    HomStrongRestrictedCowedge G pt ⥤ HomRestrictedCowedge G pt :=
  StrongRestrictedCowedge.inclusion G (HomToProf pt)

/-- The unit isomorphism for the equivalence. -/
def homRestrictedStrongUnitIso :
    𝟭 (HomRestrictedCowedge G pt) ≅
    homRestrictedToStrongFunctor G pt ⋙ strongToHomRestrictedFunctor G pt :=
  NatIso.ofComponents
    (fun rc => eqToIso (inclusion_upgrade_roundtrip G pt rc).symm)
    (fun {rc₁ rc₂} f => by
      apply RestrictedCowedge.Hom.ext
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
        homRestrictedToStrongFunctor, restrictedCowedgeToStrongCowedgeHom,
        StrongRestrictedCowedge.inclusion, eqToIso.hom, RestrictedCowedgeCat,
        RestrictedCowedge.Hom.comp_hom, RestrictedCowedge.Hom.id_hom,
        upgradeToStrongRestrictedCowedge, eqToHom_refl, Category.comp_id,
        Category.id_comp])

/-- The counit isomorphism for the equivalence. -/
def homRestrictedStrongCounitIso :
    strongToHomRestrictedFunctor G pt ⋙ homRestrictedToStrongFunctor G pt ≅
    𝟭 (HomStrongRestrictedCowedge G pt) :=
  NatIso.ofComponents
    (fun src => eqToIso (upgrade_inclusion_roundtrip G pt src))
    (fun {src₁ src₂} f => by
      apply StrongRestrictedCowedge.Hom.ext
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map, Functor.id_map,
        homRestrictedToStrongFunctor, StrongRestrictedCowedge.inclusion,
        restrictedCowedgeToStrongCowedgeHom, eqToIso.hom, StrongRestrictedCowedgeCat,
        StrongRestrictedCowedge.Hom.comp_hom, StrongRestrictedCowedge.Hom.id_hom,
        StrongRestrictedCowedge.toRestrictedCowedge, upgradeToStrongRestrictedCowedge,
        eqToHom_refl, Category.comp_id, Category.id_comp])

/-- The categorical equivalence between restricted cowedges with weight
`HomToProf pt` and strong restricted cowedges with the same weight.
This formalizes that for `HomToProf pt`, dinaturality is equivalent to
paranaturality, so the full subcategory of strong restricted cowedges
is equivalent to the entire category of restricted cowedges. -/
def homRestrictedStrongEquiv :
    HomRestrictedCowedge G pt ≌ HomStrongRestrictedCowedge G pt where
  functor := homRestrictedToStrongFunctor G pt
  inverse := strongToHomRestrictedFunctor G pt
  unitIso := homRestrictedStrongUnitIso G pt
  counitIso := homRestrictedStrongCounitIso G pt
  functor_unitIso_comp X := by
    apply StrongRestrictedCowedge.Hom.ext
    simp only [homRestrictedStrongUnitIso, homRestrictedStrongCounitIso,
      homRestrictedToStrongFunctor, NatIso.ofComponents_hom_app,
      eqToIso.hom, Functor.comp_obj, Functor.id_obj,
      restrictedCowedgeToStrongCowedgeHom, StrongRestrictedCowedge.inclusion]
    simp only [StrongRestrictedCowedgeCat, RestrictedCowedgeCat,
      StrongRestrictedCowedge.Hom.comp_hom, StrongRestrictedCowedge.Hom.id_hom,
      RestrictedCowedge.Hom.id_hom, StrongRestrictedCowedge.toRestrictedCowedge,
      upgradeToStrongRestrictedCowedge, eqToHom_refl, Category.comp_id]

/-- The categorical isomorphism between restricted cowedges with weight
`HomToProf pt` and strong restricted cowedges with the same weight.
This strengthens `homRestrictedStrongEquiv` from an equivalence to an
isomorphism, which is possible because the round-trips are equalities. -/
def homRestrictedStrongIso :
    HomRestrictedCowedge G pt ≅Cat HomStrongRestrictedCowedge G pt :=
  Cat.isoOfEquiv (homRestrictedStrongEquiv G pt)
    (inclusion_upgrade_roundtrip G pt)
    (upgrade_inclusion_roundtrip G pt)

end HomStrongRestrictedEquivalence

section HomRestrictedCowedgeFunctoriality

/-!
### Functoriality of HomRestrictedCowedge in the Weight Parameter

`HomRestrictedCowedge G` is contravariant in the weight parameter `pt`. This
arises from two observations:

1. `HomToProf pt = IdProf ⇓ pt` is covariant in `pt` via `sliceProfunctorFunctor`
2. `RestrictedCowedge G H` is contravariant in the weight `H` (precomposition)

Composing covariant with contravariant gives a contravariant functor:
  `HomRestrictedCowedgeFunctor G : Cᵒᵖ ⥤ Cat`

For a morphism `φ : pt → pt'` in `C`, the induced functor
`HomRestrictedCowedge G pt' ⥤ HomRestrictedCowedge G pt` acts by:
- On objects: precompose the family indexing with `φ`
- On morphisms: the underlying morphism is unchanged
-/

variable {C : Type u} [Category.{v} C]
variable (G : Cᵒᵖ ⥤ C ⥤ C)

/-- Reindex a restricted cowedge along a morphism `φ : pt → pt'`.
Given a cowedge at weight `HomToProf pt'`, produce a cowedge at `HomToProf pt`
by precomposing the family indexing with `φ`. -/
def homRestrictedCowedgeReindex {pt pt' : C} (φ : pt ⟶ pt')
    (rc : HomRestrictedCowedge G pt') : HomRestrictedCowedge G pt where
  pt := rc.pt
  toRestrictedCowedgeOver := {
    family := fun A f => rc.family A (f ≫ φ)
    isDinatural := fun A B g x => by
      have dinat := rc.isDinatural A B g (x ≫ φ)
      simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor_obj_map,
        sliceProfunctor_map_app, Quiver.Hom.unop_op,
        HomToProf_map_app, HomToProf_obj_map, Category.assoc] at dinat ⊢
      exact dinat
  }

/-- The apex of a reindexed cowedge equals the original apex. -/
@[simp]
theorem homRestrictedCowedgeReindex_pt {pt pt' : C} (φ : pt ⟶ pt')
    (rc : HomRestrictedCowedge G pt') :
    (homRestrictedCowedgeReindex G φ rc).pt = rc.pt := rfl

/-- The family of a reindexed cowedge is precomposition with φ. -/
@[simp]
theorem homRestrictedCowedgeReindex_family {pt pt' : C} (φ : pt ⟶ pt')
    (rc : HomRestrictedCowedge G pt') (A : C) (f : A ⟶ pt) :
    (homRestrictedCowedgeReindex G φ rc).family A f = rc.family A (f ≫ φ) := rfl

/-- Reindex a morphism of restricted cowedges along `φ : pt → pt'`. -/
def homRestrictedCowedgeReindexHom {pt pt' : C} (φ : pt ⟶ pt')
    {rc₁ rc₂ : HomRestrictedCowedge G pt'}
    (f : RestrictedCowedge.Hom rc₁ rc₂) :
    RestrictedCowedge.Hom (homRestrictedCowedgeReindex G φ rc₁)
      (homRestrictedCowedgeReindex G φ rc₂) where
  hom := f.hom
  comm := fun A x => by
    simp only [homRestrictedCowedgeReindex_family]
    exact f.comm A (x ≫ φ)

@[simp]
theorem homRestrictedCowedgeReindexHom_hom {pt pt' : C} (φ : pt ⟶ pt')
    {rc₁ rc₂ : HomRestrictedCowedge G pt'} (f : RestrictedCowedge.Hom rc₁ rc₂) :
    (homRestrictedCowedgeReindexHom G φ f).hom = f.hom := rfl

/-- The reindexing functor for a fixed morphism `φ : pt → pt'`. -/
def homRestrictedCowedgeReindexFunctor {pt pt' : C} (φ : pt ⟶ pt') :
    HomRestrictedCowedge G pt' ⥤ HomRestrictedCowedge G pt where
  obj := homRestrictedCowedgeReindex G φ
  map := homRestrictedCowedgeReindexHom G φ
  map_id := fun _ => by
    apply RestrictedCowedge.Hom.ext
    simp only [homRestrictedCowedgeReindexHom]
    rfl
  map_comp := fun _ _ => by
    apply RestrictedCowedge.Hom.ext
    simp only [homRestrictedCowedgeReindexHom]
    rfl

/-- Reindexing by the identity is the identity functor. -/
theorem homRestrictedCowedgeReindex_id (pt : C) (rc : HomRestrictedCowedge G pt) :
    homRestrictedCowedgeReindex G (𝟙 pt) rc = rc := by
  apply RestrictedCowedge.ext
  · rfl
  · apply heq_of_eq
    apply RestrictedCowedgeOver.ext
    funext A f
    simp only [homRestrictedCowedgeReindex_family, Category.comp_id]

/-- Reindexing respects composition (contravariantly). -/
theorem homRestrictedCowedgeReindex_comp {pt pt' pt'' : C}
    (φ : pt ⟶ pt') (ψ : pt' ⟶ pt'') (rc : HomRestrictedCowedge G pt'') :
    homRestrictedCowedgeReindex G φ (homRestrictedCowedgeReindex G ψ rc) =
    homRestrictedCowedgeReindex G (φ ≫ ψ) rc := by
  apply RestrictedCowedge.ext
  · rfl
  · apply heq_of_eq
    apply RestrictedCowedgeOver.ext
    funext A f
    simp only [homRestrictedCowedgeReindex_family, Category.assoc]

/-- The contravariant functor sending `pt` to `HomRestrictedCowedge G pt`.

For `φ : pt → pt'` in `C`, the induced functor goes in the opposite direction:
`HomRestrictedCowedge G pt' ⥤ HomRestrictedCowedge G pt`. -/
def homRestrictedCowedgeFunctor : Cᵒᵖ ⥤ Cat where
  obj pt := Cat.of (HomRestrictedCowedge G pt.unop)
  map {pt pt'} φ := ⟨homRestrictedCowedgeReindexFunctor G φ.unop⟩
  map_id pt := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun rc => ?_) (fun rc₁ rc₂ f => ?_)
    · simp only [Cat.of_α, homRestrictedCowedgeReindexFunctor]
      exact homRestrictedCowedgeReindex_id G pt.unop rc
    · apply RestrictedCowedge.Hom.ext
      simp only [Cat.of_α, Cat.id_eq_id, Functor.id_map,
        homRestrictedCowedgeReindexFunctor, homRestrictedCowedgeReindexHom,
        HomRestrictedCowedge, RestrictedCowedge.category_comp_hom,
        RestrictedCowedge_eqToHom_hom, eqToHom_refl, Category.id_comp, Category.comp_id]
  map_comp {pt pt' pt''} φ ψ := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun rc => ?_) (fun rc₁ rc₂ f => ?_)
    · simp only [Cat.of_α, homRestrictedCowedgeReindexFunctor]
      exact (homRestrictedCowedgeReindex_comp G ψ.unop φ.unop rc).symm
    · apply RestrictedCowedge.Hom.ext
      simp only [Cat.of_α, Cat.comp_eq_comp, Functor.comp_map,
        homRestrictedCowedgeReindexFunctor, homRestrictedCowedgeReindexHom,
        HomRestrictedCowedge, RestrictedCowedge.category_comp_hom,
        RestrictedCowedge_eqToHom_hom, homRestrictedCowedgeReindex_pt,
        eqToHom_refl, Category.id_comp, Category.comp_id]

end HomRestrictedCowedgeFunctoriality

section CowedgeFunctorsAndNatIsos

/-!
### Contravariant Functors for Other Cowedge Types

The contravariance of `HomRestrictedCowedge G` in the weight parameter `pt`
extends to the equivalent cowedge categories. Each functor is defined by
composing through the equivalence with `homRestrictedCowedgeFunctor`.

The existing categorical isomorphisms then assemble into natural isomorphisms
between these functors.
-/

open HasCopowers Limits

variable {C : Type u} [Category.{v} C] [HasCopowers C]
variable (G : Cᵒᵖ ⥤ C ⥤ C)

/-- The contravariant functor sending `pt` to `HomCopowerCowedge G pt`.

Defined by composing through `HomRestrictedCowedge` using the equivalence. -/
def homCopowerCowedgeFunctor : Cᵒᵖ ⥤ Cat where
  obj pt := Cat.of (HomCopowerCowedge G pt.unop)
  map {pt pt'} φ := ⟨copowerToHomRestrictedFunctor G pt.unop ⋙
    homRestrictedCowedgeReindexFunctor G φ.unop ⋙
    homRestrictedToCopowerFunctor G pt'.unop⟩
  map_id pt := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun cw => ?_) (fun cw₁ cw₂ f => ?_)
    · simp only [Functor.comp_obj, copowerToHomRestrictedFunctor,
        homRestrictedCowedgeReindexFunctor, homRestrictedToCopowerFunctor, unop_id]
      rw [homRestrictedCowedgeReindex_id]
      exact restrictedToCopower_copowerToRestricted G pt.unop cw
    · apply Limits.CoconeMorphism.ext
      simp only [Cat.id_eq_id, Functor.id_map, Functor.comp_obj, Functor.comp_map,
        copowerToHomRestrictedFunctor, homRestrictedToCopowerFunctor,
        homRestrictedCowedgeReindexFunctor, homRestrictedCowedgeReindexHom, unop_id,
        copowerCowedgeToRestrictedCowedgeHom, restrictedCowedgeToCopowerCowedgeHom]
      rw [Limits.Cocone.category_comp_hom, Limits.Cocone.category_comp_hom,
        GebLean.Cocone.eqToHom_hom, GebLean.Cocone.eqToHom_hom]
      simp only [copowerCowedgeToRestrictedCowedge_pt,
        restrictedCowedgeToCopowerCowedge_pt, homRestrictedCowedgeReindex_pt,
        eqToHom_refl, Category.id_comp, Category.comp_id]
  map_comp {pt pt' pt''} φ ψ := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun cw => ?_) (fun cw₁ cw₂ f => ?_)
    · simp only [Functor.comp_obj, Cat.comp_eq_comp, copowerToHomRestrictedFunctor,
        homRestrictedCowedgeReindexFunctor, homRestrictedToCopowerFunctor, unop_comp]
      rw [copowerToRestricted_restrictedToCopower, ← homRestrictedCowedgeReindex_comp]
    · apply Limits.CoconeMorphism.ext
      simp only [Cat.comp_eq_comp, Functor.comp_obj, Functor.comp_map,
        copowerToHomRestrictedFunctor, homRestrictedToCopowerFunctor,
        homRestrictedCowedgeReindexFunctor, homRestrictedCowedgeReindexHom, unop_comp,
        copowerCowedgeToRestrictedCowedgeHom, restrictedCowedgeToCopowerCowedgeHom]
      rw [Limits.Cocone.category_comp_hom, Limits.Cocone.category_comp_hom,
        GebLean.Cocone.eqToHom_hom, GebLean.Cocone.eqToHom_hom]
      simp only [copowerCowedgeToRestrictedCowedge_pt,
        restrictedCowedgeToCopowerCowedge_pt, homRestrictedCowedgeReindex_pt,
        eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The contravariant functor sending `pt` to `HomWeightedCowedge G pt`.

Defined by composing through `HomRestrictedCowedge` using the equivalence. -/
def homWeightedCowedgeFunctor : Cᵒᵖ ⥤ Cat where
  obj pt := Cat.of (HomWeightedCowedge G pt.unop)
  map {pt pt'} φ := ⟨weightedToHomRestrictedFunctor G pt.unop ⋙
    homRestrictedCowedgeReindexFunctor G φ.unop ⋙
    homRestrictedToWeightedFunctor G pt'.unop⟩
  map_id pt := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun wc => ?_) (fun wc₁ wc₂ f => ?_)
    · simp only [Functor.comp_obj, weightedToHomRestrictedFunctor,
        homRestrictedCowedgeReindexFunctor, homRestrictedToWeightedFunctor, unop_id]
      rw [homRestrictedCowedgeReindex_id]
      exact restrictedToWeighted_weightedToRestricted G pt.unop wc
    · apply WeightedCocone.Hom.ext
      simp only [Cat.id_eq_id, Functor.id_map, Functor.comp_obj,
        Functor.comp_map, weightedToHomRestrictedFunctor, homRestrictedToWeightedFunctor,
        homRestrictedCowedgeReindexFunctor, homRestrictedCowedgeReindexHom, unop_id,
        weightedCowedgeToRestrictedCowedgeHom, restrictedCowedgeToWeightedCowedgeHom]
      rw [WeightedCocone.category_comp_hom, WeightedCocone.category_comp_hom,
        WeightedCocone.eqToHom_hom, WeightedCocone.eqToHom_hom]
      simp only [weightedCowedgeToRestrictedCowedge_pt,
        restrictedCowedgeToWeightedCowedge_pt, homRestrictedCowedgeReindex_pt,
        eqToHom_refl, Category.id_comp, Category.comp_id]
  map_comp {pt pt' pt''} φ ψ := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun wc => ?_) (fun wc₁ wc₂ f => ?_)
    · simp only [Functor.comp_obj, Cat.comp_eq_comp, weightedToHomRestrictedFunctor,
        homRestrictedCowedgeReindexFunctor, homRestrictedToWeightedFunctor, unop_comp]
      rw [weightedToRestricted_restrictedToWeighted, ← homRestrictedCowedgeReindex_comp]
    · apply WeightedCocone.Hom.ext
      simp only [Cat.comp_eq_comp, Functor.comp_obj, Functor.comp_map,
        weightedToHomRestrictedFunctor, homRestrictedToWeightedFunctor,
        homRestrictedCowedgeReindexFunctor, homRestrictedCowedgeReindexHom, unop_comp,
        weightedCowedgeToRestrictedCowedgeHom, restrictedCowedgeToWeightedCowedgeHom]
      rw [WeightedCocone.category_comp_hom, WeightedCocone.category_comp_hom,
        WeightedCocone.eqToHom_hom, WeightedCocone.eqToHom_hom]
      simp only [weightedCowedgeToRestrictedCowedge_pt,
        restrictedCowedgeToWeightedCowedge_pt, homRestrictedCowedgeReindex_pt,
        eqToHom_refl, Category.id_comp, Category.comp_id]

/-- The contravariant functor sending `pt` to `HomStrongRestrictedCowedge G pt`.

Defined by composing through `HomRestrictedCowedge` using the equivalence. -/
def homStrongRestrictedCowedgeFunctor : Cᵒᵖ ⥤ Cat where
  obj pt := Cat.of (HomStrongRestrictedCowedge G pt.unop)
  map {pt pt'} φ := ⟨strongToHomRestrictedFunctor G pt.unop ⋙
    homRestrictedCowedgeReindexFunctor G φ.unop ⋙
    homRestrictedToStrongFunctor G pt'.unop⟩
  map_id pt := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun src => ?_) (fun src₁ src₂ f => ?_)
    · simp only [Functor.comp_obj, strongToHomRestrictedFunctor,
        homRestrictedCowedgeReindexFunctor, homRestrictedToStrongFunctor, unop_id]
      rw [homRestrictedCowedgeReindex_id]
      exact upgrade_inclusion_roundtrip G pt.unop src
    · apply StrongRestrictedCowedge.Hom.ext
      simp only [Cat.id_eq_id, Functor.id_map, Functor.comp_obj,
        Functor.comp_map, homRestrictedToStrongFunctor,
        homRestrictedCowedgeReindexFunctor, homRestrictedCowedgeReindexHom, unop_id,
        StrongRestrictedCowedge.inclusion, restrictedCowedgeToStrongCowedgeHom]
      rw [StrongRestrictedCowedge.category_comp_hom,
        StrongRestrictedCowedge.category_comp_hom,
        StrongRestrictedCowedge_eqToHom_hom, StrongRestrictedCowedge_eqToHom_hom]
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
  map_comp {pt pt' pt''} φ ψ := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun src => ?_) (fun src₁ src₂ f => ?_)
    · simp only [Functor.comp_obj, Cat.comp_eq_comp, strongToHomRestrictedFunctor,
        homRestrictedCowedgeReindexFunctor, homRestrictedToStrongFunctor, unop_comp]
      rw [← homRestrictedCowedgeReindex_comp]
      congr 1
    · apply StrongRestrictedCowedge.Hom.ext
      simp only [Cat.comp_eq_comp, Functor.comp_obj, Functor.comp_map,
        homRestrictedToStrongFunctor,
        homRestrictedCowedgeReindexFunctor, homRestrictedCowedgeReindexHom, unop_comp,
        StrongRestrictedCowedge.inclusion, restrictedCowedgeToStrongCowedgeHom]
      rw [StrongRestrictedCowedge.category_comp_hom,
        StrongRestrictedCowedge.category_comp_hom,
        StrongRestrictedCowedge_eqToHom_hom, StrongRestrictedCowedge_eqToHom_hom]
      simp only [eqToHom_refl, Category.id_comp, Category.comp_id]

/-- Natural isomorphism between `homRestrictedCowedgeFunctor` and
`homCopowerCowedgeFunctor`, with components given by the per-object
categorical isomorphisms `homRestrictedCopowerIso`. -/
def homRestrictedCopowerNatIso :
    homRestrictedCowedgeFunctor G ≅ homCopowerCowedgeFunctor G :=
  NatIso.ofComponents
    (fun pt => homRestrictedCopowerIso G pt.unop)
    (fun {pt pt'} φ => by
      apply Cat.Hom.ext
      refine CategoryTheory.Functor.ext (fun rc => ?_) (fun rc₁ rc₂ f => ?_)
      · simp only [Cat.comp_eq_comp, homRestrictedCowedgeFunctor,
          homCopowerCowedgeFunctor, homRestrictedCopowerIso, Cat.isoOfEquiv_hom,
          homRestrictedCopowerEquiv, homRestrictedCowedgeReindexFunctor,
          copowerToHomRestrictedFunctor, homRestrictedToCopowerFunctor, Functor.comp_obj]
        change restrictedCowedgeToCopowerCowedge G pt'.unop
            (homRestrictedCowedgeReindex G φ.unop rc) =
          restrictedCowedgeToCopowerCowedge G pt'.unop
            (homRestrictedCowedgeReindex G φ.unop
              (copowerCowedgeToRestrictedCowedge G pt.unop
                (restrictedCowedgeToCopowerCowedge G pt.unop rc)))
        rw [copowerToRestricted_restrictedToCopower]
      · simp only [Cat.comp_eq_comp, homRestrictedCowedgeFunctor,
          homCopowerCowedgeFunctor, homRestrictedCopowerIso, Cat.isoOfEquiv_hom,
          homRestrictedCopowerEquiv, homRestrictedCowedgeReindexFunctor,
          copowerToHomRestrictedFunctor, homRestrictedToCopowerFunctor,
          homRestrictedCowedgeReindexHom, copowerCowedgeToRestrictedCowedgeHom,
          restrictedCowedgeToCopowerCowedgeHom, Functor.comp_obj, Functor.comp_map,
          Functor.toCatHom_toFunctor]
        apply Limits.CoconeMorphism.ext
        rw [Limits.Cocone.category_comp_hom, Limits.Cocone.category_comp_hom,
          GebLean.Cocone.eqToHom_hom, GebLean.Cocone.eqToHom_hom]
        simp only [restrictedCowedgeToCopowerCowedge_pt,
          copowerCowedgeToRestrictedCowedge_pt, homRestrictedCowedgeReindex_pt,
          eqToHom_refl, Category.id_comp, Category.comp_id])

/-- Natural isomorphism between `homRestrictedCowedgeFunctor` and
`homWeightedCowedgeFunctor`, with components given by the per-object
categorical isomorphisms `homRestrictedWeightedIso`. -/
def homRestrictedWeightedNatIso :
    homRestrictedCowedgeFunctor G ≅ homWeightedCowedgeFunctor G :=
  NatIso.ofComponents
    (fun pt => homRestrictedWeightedIso G pt.unop)
    (fun {pt pt'} φ => by
      apply Cat.Hom.ext
      refine CategoryTheory.Functor.ext (fun rc => ?_) (fun rc₁ rc₂ f => ?_)
      · simp only [Cat.comp_eq_comp, homRestrictedCowedgeFunctor,
          homWeightedCowedgeFunctor, homRestrictedWeightedIso, Cat.isoOfEquiv_hom,
          homRestrictedWeightedEquiv, homRestrictedCowedgeReindexFunctor,
          weightedToHomRestrictedFunctor, homRestrictedToWeightedFunctor, Functor.comp_obj]
        change extendRestrictedCowedgeFull' G pt'.unop
            (homRestrictedCowedgeReindex G φ.unop rc) =
          extendRestrictedCowedgeFull' G pt'.unop
            (homRestrictedCowedgeReindex G φ.unop
              (restrictWeightedCowedge (HomToProf pt.unop) G
                (extendRestrictedCowedgeFull' G pt.unop rc)))
        rw [weightedToRestricted_restrictedToWeighted]
      · simp only [Cat.comp_eq_comp, homRestrictedCowedgeFunctor,
          homWeightedCowedgeFunctor, homRestrictedWeightedIso, Cat.isoOfEquiv_hom,
          homRestrictedWeightedEquiv, homRestrictedCowedgeReindexFunctor,
          weightedToHomRestrictedFunctor, homRestrictedToWeightedFunctor,
          homRestrictedCowedgeReindexHom, weightedCowedgeToRestrictedCowedgeHom,
          restrictedCowedgeToWeightedCowedgeHom, Functor.comp_obj, Functor.comp_map,
          Functor.toCatHom_toFunctor]
        apply WeightedCocone.Hom.ext
        rw [WeightedCocone.category_comp_hom, WeightedCocone.category_comp_hom,
          WeightedCocone.eqToHom_hom, WeightedCocone.eqToHom_hom]
        simp only [restrictedCowedgeToWeightedCowedge_pt,
          weightedCowedgeToRestrictedCowedge_pt, homRestrictedCowedgeReindex_pt,
          eqToHom_refl, Category.id_comp, Category.comp_id])

/-- Natural isomorphism between `homRestrictedCowedgeFunctor` and
`homStrongRestrictedCowedgeFunctor`, with components given by the per-object
categorical isomorphisms `homRestrictedStrongIso`. -/
def homRestrictedStrongNatIso :
    homRestrictedCowedgeFunctor G ≅ homStrongRestrictedCowedgeFunctor G :=
  NatIso.ofComponents
    (fun pt => homRestrictedStrongIso G pt.unop)
    (fun {pt pt'} φ => by
      apply Cat.Hom.ext
      refine CategoryTheory.Functor.ext (fun rc => ?_) (fun rc₁ rc₂ f => ?_)
      · simp only [Cat.comp_eq_comp, homRestrictedCowedgeFunctor,
          homStrongRestrictedCowedgeFunctor, homRestrictedStrongIso, Cat.isoOfEquiv_hom,
          homRestrictedStrongEquiv, homRestrictedCowedgeReindexFunctor,
          strongToHomRestrictedFunctor, homRestrictedToStrongFunctor, Functor.comp_obj]
        change upgradeToStrongRestrictedCowedge G pt'.unop
            (homRestrictedCowedgeReindex G φ.unop rc) =
          upgradeToStrongRestrictedCowedge G pt'.unop
            (homRestrictedCowedgeReindex G φ.unop
              ((StrongRestrictedCowedge.inclusion G (HomToProf pt.unop)).obj
                (upgradeToStrongRestrictedCowedge G pt.unop rc)))
        rw [inclusion_upgrade_roundtrip]
      · simp only [Cat.comp_eq_comp, homRestrictedCowedgeFunctor,
          homStrongRestrictedCowedgeFunctor, homRestrictedStrongIso, Cat.isoOfEquiv_hom,
          homRestrictedStrongEquiv, homRestrictedCowedgeReindexFunctor,
          homRestrictedToStrongFunctor, homRestrictedCowedgeReindexHom,
          StrongRestrictedCowedge.inclusion, restrictedCowedgeToStrongCowedgeHom,
          Functor.comp_obj, Functor.comp_map, Functor.toCatHom_toFunctor]
        apply StrongRestrictedCowedge.Hom.ext
        rw [StrongRestrictedCowedge.category_comp_hom,
          StrongRestrictedCowedge.category_comp_hom,
          StrongRestrictedCowedge_eqToHom_hom, StrongRestrictedCowedge_eqToHom_hom]
        simp only [upgradeToStrongRestrictedCowedge_pt,
          StrongRestrictedCowedge.toRestrictedCowedge, homRestrictedCowedgeReindex_pt,
          eqToHom_refl, Category.id_comp, Category.comp_id])

end CowedgeFunctorsAndNatIsos

section KanExtensionConnection

/-!
### Connection to Left Kan Extensions

The restricted coend `Σ(HomToProf pt, G)` has the structure of a pointwise left
Kan extension formula, generalizing from covariant functors to profunctors.

#### Background: Pointwise Left Kan Extensions

For functors `L : C ⥤ D` and `F : C ⥤ H`, the pointwise left Kan extension of `F`
along `L` at an object `Y : D` is:

  `(Lan_L F)(Y) = colim_{g : CostructuredArrow L Y} F(g.left)`

The comma category `CostructuredArrow L Y` has:
- Objects: pairs `(X, f)` where `X : C` and `f : L(X) → Y`
- Morphisms: `g : X₁ → X₂` such that `L(g) ≫ f₂ = f₁`

When `L = 𝟭 C` (the identity functor), `CostructuredArrow (𝟭 C) pt ≃ Over pt`, so:

  `(Lan_id F)(pt) = colim_{(A, f : A → pt) ∈ Over pt} F(A)`

By the co-Yoneda lemma, this equals `F(pt)`.

#### Connection to Restricted Coends

For a profunctor `G : Cᵒᵖ ⥤ C ⥤ C`:

1. The restricted coend `Σ(HomToProf pt, G)` is the initial object in the category
   of `(HomToProf pt)`-restricted `G`-cowedges.

2. The weight `HomToProf pt` restricted to the diagonal equals `coyoneda'.obj pt`,
   and its category of elements is equivalent to `Over pt`.

3. A restricted cowedge provides a compatible family `G(A, A) → apex` indexed by
   `Over pt`, analogous to a cocone in the colimit formula.

4. When `G(A, B) = F(B)` for some covariant `F : C ⥤ C`:
   - The restricted coend reduces to `colim_{Over pt} F`
   - This equals the pointwise Kan extension `(Lan_id F)(pt) = F(pt)`

The restricted coend thus generalizes the Kan extension formula to profunctors
where `G ∘ Δ` is not functorial.
-/

open HasRestrictedCoend

variable {C : Type u} [Category.{v} C]

/-- The diagonal of `constFirstArgProf F` at any object `A` is `F(A)`. -/
theorem constFirstArgProf_diagonal (F : C ⥤ C) (A : C) :
    ((constFirstArgProf F).obj (op A)).obj A = F.obj A := rfl

/-- For a covariant functor `F : C ⥤ C`, the restricted cowedge with weight
`HomToProf pt` and profunctor `constFirstArgProf F` has a canonical structure
from any morphism `F(pt) → apex`.

This shows that `F(pt)` is a candidate for the restricted coend, as it receives
morphisms from all `F(A)` for `A` admitting a map to `pt`. -/
def constFirstArgProfCowedge (F : C ⥤ C) (pt D : C) (morph : F.obj pt ⟶ D) :
    RestrictedCowedge (constFirstArgProf F) (HomToProf pt) :=
  RestrictedCowedge.mk' D
    (fun A f => F.map f ≫ morph)
    (fun A B g β => by
      simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor_obj_map,
        sliceProfunctor_map_app, Quiver.Hom.unop_op, HomToProf_map_app,
        HomToProf_obj_map, constFirstArgProf_map_snd, constFirstArgProf_map_fst,
        Functor.map_comp, Category.assoc]
      simp only [constFirstArgProf, Functor.const_obj_obj, Category.id_comp])

/-- For a covariant functor `F`, the identity morphism on `F(pt)` induces the
universal restricted cowedge. The apex `F(pt)` receives all `F(A)` via the
functorial action of F on morphisms `A → pt`. -/
def constFirstArgProfUniversalCowedge (F : C ⥤ C) (pt : C) :
    RestrictedCowedge (constFirstArgProf F) (HomToProf pt) :=
  constFirstArgProfCowedge F pt (F.obj pt) (𝟙 (F.obj pt))

@[simp]
theorem constFirstArgProfUniversalCowedge_pt (F : C ⥤ C) (pt : C) :
    (constFirstArgProfUniversalCowedge F pt).pt = F.obj pt := rfl

@[simp]
theorem constFirstArgProfUniversalCowedge_family (F : C ⥤ C) (pt : C)
    (A : C) (f : A ⟶ pt) :
    (constFirstArgProfUniversalCowedge F pt).family A f = F.map f := by
  simp only [constFirstArgProfUniversalCowedge, constFirstArgProfCowedge,
    RestrictedCowedge.mk', RestrictedCowedge.family, Category.comp_id]

/-- The universal cowedge for `constFirstArgProf F` is initial: any other
restricted cowedge factors uniquely through it.

This is the co-Yoneda lemma: `Σ(HomToProf pt, constFirstArgProf F) ≅ F(pt)`.
When the profunctor arises from a covariant functor, the restricted coend
equals the value of that functor, recovering the Kan extension formula. -/
theorem constFirstArgProfUniversalCowedge_isInitial (F : C ⥤ C) (pt : C)
    (cwedge : RestrictedCowedge (constFirstArgProf F) (HomToProf pt)) :
    ∃! f : F.obj pt ⟶ cwedge.pt,
      ∀ A (g : A ⟶ pt),
        (constFirstArgProfUniversalCowedge F pt).family A g ≫ f = cwedge.family A g := by
  use cwedge.family pt (𝟙 pt)
  constructor
  · intro A g
    simp only [constFirstArgProfUniversalCowedge_family]
    have dinat := cwedge.isDinatural A pt g (𝟙 pt)
    simp only [Profunctor.lmap, Profunctor.rmap, sliceProfunctor_obj_map,
      sliceProfunctor_map_app, Quiver.Hom.unop_op, HomToProf_map_app,
      HomToProf_obj_map, Category.comp_id,
      constFirstArgProf_map_snd, constFirstArgProf_map_fst] at dinat
    simp only [constFirstArgProf, Functor.const_obj_obj, Category.id_comp] at dinat
    exact dinat
  · intro f hf
    specialize hf pt (𝟙 pt)
    simp only [constFirstArgProfUniversalCowedge_family, Functor.map_id] at hf
    calc f = 𝟙 (F.obj pt) ≫ f := (Category.id_comp f).symm
      _ = cwedge.family pt (𝟙 pt) := hf

end KanExtensionConnection

section CoendAsNatTransformations

/-!
### Coends in Type as Natural Transformations

For endodifunctors on `Type`, we can express the restricted coend (equivalently,
the copower coend) as a set of natural transformations using the Yoneda lemma.

#### Background

For any type `X`, the co-Yoneda lemma states:
  `X ≅ Nat(Hom(X, -), Id)`
where `Id` is the identity functor on `Type` and `Hom(X, -)` is the covariant
hom-functor.

For a coend `∫^A P(A,A)`, the universal property gives:
  `Hom(∫^A P(A,A), Y) ≅ ∫_A Hom(P(A,A), Y)`

The RHS consists of families `(α_A : P(A,A) → Y)_{A∈C}` satisfying the cowedge
condition. This corresponds to a `WeightedCowedgeOver` with trivial weight.

Combining the coend elimination rule with the co-Yoneda lemma:
  `∫^A P(A,A) ≅ Nat(Y ↦ Cowedge_Y P, Id)`

This characterizes the coend as natural transformations from the functor
sending `Y` to cowedges with apex `Y`, to the identity functor on Type.

#### Implementation

We use `WeightedCowedgeOver terminalProfunctor P Y` as the type of cowedges
over `P` with apex `Y`. By `trivialWeightedCowedgeCoconeEquiv`, this is equivalent
to cocones over the co-twisted arrow diagram, which are cowedges of `P`.
-/

universe w

variable {C : Type w} [Category.{w} C]

open Limits

/-- The functor sending each type `Y` to weighted cowedges with trivial weight.

By the coend elimination rule, this is isomorphic to `Hom(∫^A P(A,A), -)`.
This uses `WeightedCowedgeOver terminalProfunctor P Y`, which is equivalent
to cowedges of `P` with apex `Y`. -/
def cowedgeFamilyFunctor (P : Cᵒᵖ ⥤ C ⥤ Type w) : Type w ⥤ Type w :=
  ((weightedCowedgeOverCurriedTrifunctor (C := C) (D := Type w)).obj
    (Opposite.op terminalProfunctor)).obj (Opposite.op P)

/-- Natural transformations from `cowedgeFamilyFunctor P` to the identity.

By the co-Yoneda lemma combined with the coend elimination rule, these
correspond to elements of the coend `∫^A P(A,A)`. -/
def CowedgeNatTrans (P : Cᵒᵖ ⥤ C ⥤ Type w) :=
  cowedgeFamilyFunctor P ⟶ 𝟭 (Type w)

/-!
### Correspondence: Coends and Natural Transformations

The coend of `P` in `Type` can be characterized as natural transformations
from `cowedgeFamilyFunctor P` to the identity functor.

Given an element `x : ∫^A P(A,A)`, we define a natural transformation `τ_x` by:
  `τ_x(Y)(cw) = desc_cw(x)`
where `desc_cw : ∫^A P(A,A) → Y` is the unique map induced by the cowedge `cw`.

Conversely, given a natural transformation `τ`, we recover an element by
applying `τ` to the canonical injection cowedge.
-/

/-- The injection cowedge: the coend injections form a weighted cowedge
with apex equal to the coend itself. For each co-twisted arrow `tw` with
`arr : coTwCod tw ⟶ coTwDom tw`, the leg maps `x : P(dom, cod)` to
`ι dom (P.map arr x)`, where we use the covariant action to transport
to the diagonal, then inject into the coend. -/
def coendInjectionCowedge (P : Cᵒᵖ ⥤ C ⥤ Type w) (coendPt : Type w)
    (ι : ∀ A, diagApp P A → coendPt)
    (hι : ∀ {i j : C} (f : i ⟶ j) (x : (P.obj (op j)).obj i),
      ι i ((P.map f.op).app i x) = ι j ((P.obj (op j)).map f x)) :
    WeightedCowedgeOver terminalProfunctor P coendPt where
  app tw _ :=
    let dom := coTwDom tw.unop
    let arr := coTwArr tw.unop
    fun x => ι dom ((P.obj (op dom)).map arr x)
  naturality {tw tw'} f := by
    funext _
    funext x
    simp only [types_comp_apply, terminalProfunctor, constProfunctor]
    -- homToFunctor.map f g is definitionally D.map f.unop ≫ g
    change ι (coTwDom tw'.unop) ((P.obj (op (coTwDom tw'.unop))).map (coTwArr tw'.unop) x) =
      (fun y => ι (coTwDom tw.unop) ((P.obj (op (coTwDom tw.unop))).map (coTwArr tw.unop) y))
        ((profunctorOnCoTwistedArrow C P).map f.unop x)
    simp only []
    rw [profunctorOnCoTwistedArrow_map]
    -- For m = f.unop : tw'.unop ⟶ tw.unop:
    -- (profunctorOnCoTwistedArrow P).map m =
    --   (P.map (coTwDomArr m).op).app (coTwCod tw'.unop)
    --     ≫ (P.obj (op (coTwDom tw.unop))).map (coTwCodArr m)
    let dom := coTwDom tw.unop
    let dom' := coTwDom tw'.unop
    let cod' := coTwCod tw'.unop
    let arr := coTwArr tw.unop
    let arr' := coTwArr tw'.unop
    let fDom := coTwDomArr f.unop   -- dom → dom'
    let fCod := coTwCodArr f.unop   -- cod' → cod
    -- The commutative square: fCod ≫ arr ≫ fDom = arr'
    have sq := coTwHomComm f.unop
    simp only [types_comp_apply]
    -- Goal: ι dom' ((P.obj (op dom')).map arr' x)
    --     = ι dom ((P.obj (op dom)).map arr
    --         ((P.obj (op dom)).map fCod ((P.map fDom.op).app cod' x)))
    -- Using sq: arr' = fCod ≫ arr ≫ fDom, so:
    -- LHS = ι dom' ((P.obj (op dom')).map (fCod ≫ arr ≫ fDom) x)
    --     = ι dom' ((P.obj (op dom')).map fDom
    --         ((P.obj (op dom')).map arr ((P.obj (op dom')).map fCod x)))
    -- Use dinaturality: ι dom ((P.map fDom.op).app dom z) = ι dom' ((P.obj (op dom')).map fDom z)
    -- And naturality of (P.map fDom.op)
    calc ι dom' ((P.obj (op dom')).map arr' x)
      = ι dom' ((P.obj (op dom')).map (fCod ≫ arr ≫ fDom) x) := by rw [sq]
      _ = ι dom' ((P.obj (op dom')).map fDom
            ((P.obj (op dom')).map arr ((P.obj (op dom')).map fCod x))) := by
          simp only [Functor.map_comp, types_comp_apply]
      _ = ι dom ((P.map fDom.op).app dom
            ((P.obj (op dom')).map arr ((P.obj (op dom')).map fCod x))) := by
          rw [← hι fDom]
      _ = ι dom ((P.obj (op dom)).map arr
            ((P.map fDom.op).app _ ((P.obj (op dom')).map fCod x))) := by
          -- Use naturality of (P.map fDom.op) at morphism arr
          have nat := (P.map fDom.op).naturality arr
          -- nat : (P.obj (op dom')).map arr ≫ (P.map fDom.op).app dom
          --     = (P.map fDom.op).app (coTwCod tw.unop) ≫ (P.obj (op dom)).map arr
          -- In Type: (f ≫ g) z = g (f z), so congrFun nat z gives the equality
          exact congrArg (ι dom) (congrFun nat _)
      _ = ι dom ((P.obj (op dom)).map arr
            ((P.obj (op dom)).map fCod ((P.map fDom.op).app cod' x))) := by
          -- Use naturality of (P.map fDom.op) at morphism fCod
          have nat := (P.map fDom.op).naturality fCod
          exact congrArg (ι dom ∘ (P.obj (op dom)).map arr) (congrFun nat _)

/-- Given an element of a coend, construct the corresponding natural
transformation via the co-Yoneda correspondence.

For `x : coendPt`, the natural transformation `τ_x` is defined by:
  `τ_x.app Y cw = desc cw x`
where `desc cw : coendPt → Y` is the unique map induced by the cowedge `cw`.
-/
def coendToNatTrans (P : Cᵒᵖ ⥤ C ⥤ Type w)
    (coendPt : Type w)
    (ι : ∀ A, diagApp P A → coendPt)
    (_hι : ∀ {i j : C} (f : i ⟶ j) (x : (P.obj (op j)).obj i),
      ι i ((P.map f.op).app i x) = ι j ((P.obj (op j)).map f x))
    (desc : ∀ {Y : Type w}, WeightedCowedgeOver terminalProfunctor P Y → coendPt → Y)
    (fac : ∀ {Y : Type w} (cw : WeightedCowedgeOver terminalProfunctor P Y)
      (A : C) (x : diagApp P A),
      desc cw (ι A x) = cw.app (Opposite.op (diagCoTwArr A)) PUnit.unit x)
    (_unique : ∀ {Y : Type w} (cw : WeightedCowedgeOver terminalProfunctor P Y)
      (f g : coendPt → Y),
      (∀ A x, f (ι A x) = cw.app (Opposite.op (diagCoTwArr A)) PUnit.unit x) →
      (∀ A x, g (ι A x) = cw.app (Opposite.op (diagCoTwArr A)) PUnit.unit x) →
      f = g)
    (x : coendPt) :
    CowedgeNatTrans P where
  app Y cw := desc cw x
  naturality {Y Y'} f := by
    funext cw
    simp only [cowedgeFamilyFunctor, types_comp_apply, Functor.id_obj, Functor.id_map]
    -- The naturality follows from the fact that `desc` is the unique map
    -- induced by the cowedge, and function composition in Type is associative.
    -- For `f : Y → Y'`, `(cowedgeFamilyFunctor P).map f cw` is the cowedge
    -- with legs `f ∘ cw.app tw`. The desc for this cowedge applied to x
    -- equals `f (desc cw x)` by uniqueness.
    -- Let cw' = cowedgeFamilyFunctor.map f cw. We show desc cw' = f ∘ desc cw
    -- by uniqueness, then evaluate at x.
    let cw' := ((weightedCowedgeOverCurriedTrifunctor.obj
        (Opposite.op terminalProfunctor)).obj (Opposite.op P)).map f cw
    have eq : desc cw' = f ∘ desc cw := _unique cw' (desc cw') (f ∘ desc cw)
      (fun A y => fac cw' A y)
      (fun A y => by
        simp only [Function.comp_apply]
        rw [fac]
        -- cw'.app at diagonal = f ∘ cw.app at diagonal, by definition of the map
        rfl)
    exact congrFun eq x

/-- Given a natural transformation, extract an element of the coend by
applying it to the injection cowedge. -/
def natTransToCoend (P : Cᵒᵖ ⥤ C ⥤ Type w) (coendPt : Type w)
    (ι : ∀ A, diagApp P A → coendPt)
    (hι : ∀ {i j : C} (f : i ⟶ j) (x : (P.obj (op j)).obj i),
      ι i ((P.map f.op).app i x) = ι j ((P.obj (op j)).map f x))
    (τ : CowedgeNatTrans P) : coendPt :=
  τ.app coendPt (coendInjectionCowedge P coendPt ι hι)

/-- Round-trip: natTransToCoend ∘ coendToNatTrans = id.

Given an element `x` of the coend, converting it to a natural transformation
and back yields `x`. This uses the factorization property `fac`. -/
theorem natTransToCoend_coendToNatTrans (P : Cᵒᵖ ⥤ C ⥤ Type w)
    (coendPt : Type w)
    (ι : ∀ A, diagApp P A → coendPt)
    (hι : ∀ {i j : C} (f : i ⟶ j) (x : (P.obj (op j)).obj i),
      ι i ((P.map f.op).app i x) = ι j ((P.obj (op j)).map f x))
    (desc : ∀ {Y : Type w}, WeightedCowedgeOver terminalProfunctor P Y →
      coendPt → Y)
    (fac : ∀ {Y : Type w} (cw : WeightedCowedgeOver terminalProfunctor P Y)
      (A : C) (x : diagApp P A),
      desc cw (ι A x) = cw.app (Opposite.op (diagCoTwArr A)) PUnit.unit x)
    (unique : ∀ {Y : Type w} (cw : WeightedCowedgeOver terminalProfunctor P Y)
      (f g : coendPt → Y),
      (∀ A x, f (ι A x) = cw.app (Opposite.op (diagCoTwArr A)) PUnit.unit x) →
      (∀ A x, g (ι A x) = cw.app (Opposite.op (diagCoTwArr A)) PUnit.unit x) →
      f = g)
    (x : coendPt) :
    natTransToCoend P coendPt ι hι
      (coendToNatTrans P coendPt ι hι desc fac unique x) = x := by
  -- natTransToCoend applies τ_x to the injection cowedge
  -- τ_x.app coendPt (injCowedge) = desc injCowedge x
  -- By uniqueness, desc injCowedge = id, so the result is x
  simp only [natTransToCoend, coendToNatTrans]
  -- Goal: desc (coendInjectionCowedge P coendPt ι hι) x = x
  -- We need to show desc injCowedge = id using uniqueness
  have h : desc (coendInjectionCowedge P coendPt ι hι) = id := by
    apply unique (coendInjectionCowedge P coendPt ι hι)
    · intro A y
      exact fac (coendInjectionCowedge P coendPt ι hι) A y
    · intro A y
      simp only [id_eq, coendInjectionCowedge, diagCoTwArr]
      simp only [coTwObjMk_dom, coTwObjMk_arr]
      simp only [(P.obj (op A)).map_id A, types_id_apply]
  exact congrFun h x

/-- Morphism from any co-twisted arrow to the diagonal at its domain.

For `tw = (A, B, f : B ⟶ A)`, there is a canonical morphism to
`diagCoTwArr A = (A, A, 𝟙 A)` with `domArr = 𝟙 A` and `codArr = f`. -/
def coTwToDomDiag (tw : CoTwistedArrow C) : tw ⟶ diagCoTwArr (coTwDom tw) :=
  coTwHomMk (𝟙 (coTwDom tw)) (coTwArr tw) (by simp [diagCoTwArr])

/-- Round-trip: coendToNatTrans ∘ natTransToCoend = id.

Given a natural transformation `τ`, converting it to a coend element
and back yields the same natural transformation. This uses naturality of τ
and the factorization property. -/
theorem coendToNatTrans_natTransToCoend (P : Cᵒᵖ ⥤ C ⥤ Type w)
    (coendPt : Type w)
    (ι : ∀ A, diagApp P A → coendPt)
    (hι : ∀ {i j : C} (f : i ⟶ j) (x : (P.obj (op j)).obj i),
      ι i ((P.map f.op).app i x) = ι j ((P.obj (op j)).map f x))
    (desc : ∀ {Y : Type w}, WeightedCowedgeOver terminalProfunctor P Y →
      coendPt → Y)
    (fac : ∀ {Y : Type w} (cw : WeightedCowedgeOver terminalProfunctor P Y)
      (A : C) (x : diagApp P A),
      desc cw (ι A x) = cw.app (Opposite.op (diagCoTwArr A)) PUnit.unit x)
    (unique : ∀ {Y : Type w} (cw : WeightedCowedgeOver terminalProfunctor P Y)
      (f g : coendPt → Y),
      (∀ A x, f (ι A x) = cw.app (Opposite.op (diagCoTwArr A)) PUnit.unit x) →
      (∀ A x, g (ι A x) = cw.app (Opposite.op (diagCoTwArr A)) PUnit.unit x) →
      f = g)
    (τ : CowedgeNatTrans P) :
    coendToNatTrans P coendPt ι hι desc fac unique
      (natTransToCoend P coendPt ι hι τ) = τ := by
  apply NatTrans.ext
  funext Y
  apply funext
  intro cw
  simp only [natTransToCoend, coendToNatTrans]
  -- Goal: desc cw (τ.app coendPt injCowedge) = τ.app Y cw
  let injCowedge := coendInjectionCowedge P coendPt ι hι
  -- By naturality of τ at `desc cw`:
  --   τ.app Y (map (desc cw) injCowedge) = desc cw (τ.app coendPt injCowedge)
  have nat := τ.naturality (desc cw)
  have nat_at_inj : τ.app Y ((cowedgeFamilyFunctor P).map (desc cw) injCowedge) =
      desc cw (τ.app coendPt injCowedge) := congrFun nat injCowedge
  rw [← nat_at_inj]
  -- Goal: τ.app Y (map (desc cw) injCowedge) = τ.app Y cw
  -- Suffices: (cowedgeFamilyFunctor P).map (desc cw) injCowedge = cw
  have cw_eq : (cowedgeFamilyFunctor P).map (desc cw) injCowedge = cw := by
    -- Both sides are cowedges. We prove they're equal by extensionality.
    apply NatTrans.ext
    funext tw
    apply funext
    intro u
    apply funext
    intro x
    -- Since u : PUnit, we have u = PUnit.unit
    cases u
    -- The functor map postcomposes with desc cw.
    -- LHS = (F.map (desc cw) injCowedge).app tw () x = desc cw (injCowedge.app tw () x)
    -- First show LHS equals desc cw applied to the injection cowedge value
    change desc cw ((coendInjectionCowedge P coendPt ι hι).app tw PUnit.unit x) =
           cw.app tw PUnit.unit x
    -- Unfold injCowedge: its app at tw gives ι dom (P.map x)
    dsimp only [coendInjectionCowedge]
    -- Goal: desc cw (ι dom ((P.obj (op dom)).map arr x)) = cw.app tw () x
    rw [fac]
    -- Goal: cw.app (op (diagCoTwArr dom)) () ((P.obj (op dom)).map arr x) = cw.app tw () x
    -- Use naturality of cw at op(coTwToDomDiag tw.unop)
    have nat_cw := cw.naturality (Opposite.op (coTwToDomDiag tw.unop))
    have eq := congrFun (congrFun nat_cw PUnit.unit) x
    simp only [types_comp_apply] at eq
    -- eq : cw.app tw (W.map f ()) x = H.map f (cw.app source ()) x
    -- For terminal weight, W.map is identity
    -- For the profunctor, H.map f (cw.app source ()) x = cw.app source () (P.map arr x)
    -- The diagonal object representation in eq is defeq to diagCoTwArr
    -- We need: cw.app diag () (P.map arr x) = cw.app tw () x
    -- This is eq with simplified functor applications
    symm
    calc cw.app tw PUnit.unit x
        = cw.app tw ((unop ((profunctorOnOpCoTwistedArrowFunctor C).op.obj
            (op terminalProfunctor))).map (op (coTwToDomDiag tw.unop)) PUnit.unit) x := rfl
      _ = ((homToFunctorBifunctor.obj ((profunctorOnCoTwistedArrowFunctor C).op.obj
            (op P))).obj Y).map (op (coTwToDomDiag tw.unop))
            (cw.app (op (diagCoTwArr (coTwDom tw.unop))) PUnit.unit) x := eq
      _ = cw.app (op (diagCoTwArr (coTwDom tw.unop))) PUnit.unit
            ((P.obj (op (coTwDom tw.unop))).map (coTwArr tw.unop) x) := by
          -- [H, Y].map (op f) is precomposition with H.map f
          -- We need: g (H.map (coTwToDomDiag tw) x) = g (P.map arr x) for g = cw.app diag
          -- This follows from H.map (coTwToDomDiag tw) = P.map arr
          let dom := coTwDom tw.unop
          let arr := coTwArr tw.unop
          let H := profunctorOnCoTwistedArrow C P
          -- First show the internal hom map is precomposition
          have hom_map : ∀ (g : H.obj (diagCoTwArr dom) → Y) (y : H.obj tw.unop),
              ((homToFunctorBifunctor.obj ((profunctorOnCoTwistedArrowFunctor C).op.obj
                (op P))).obj Y).map (op (coTwToDomDiag tw.unop)) g y =
              g (H.map (coTwToDomDiag tw.unop) y) := fun _ _ => rfl
          rw [hom_map]
          -- Now show the profunctor maps agree
          -- H.map (coTwToDomDiag tw) = (P.obj (op dom)).map arr
          have H_map : H.map (coTwToDomDiag tw.unop) x =
              (P.obj (op dom)).map arr x := by
            rw [profunctorOnCoTwistedArrow_map]
            simp only [coTwToDomDiag, coTwDomArr_coTwHomMk, coTwCodArr_coTwHomMk,
              diagCoTwArr_dom, op_id, Functor.map_id, NatTrans.id_app,
              Category.id_comp]
            rfl
          rw [H_map]
  rw [cw_eq]

end CoendAsNatTransformations

end GebLean
