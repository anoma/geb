import GebLean.Paranatural
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

/-- Functorial action of copowers on the base object.
Given `g : X → Y`, we get `mapVal g : S · X → S · Y`. -/
def mapVal {S : Type v} {X Y : C} (g : X ⟶ Y) : copower S X ⟶ copower S Y :=
  desc (fun s => g ≫ inj S Y s)

@[simp]
theorem mapVal_inj {S : Type v} {X Y : C} (g : X ⟶ Y) (s : S) :
    inj S X s ≫ mapVal g = g ≫ inj S Y s := fac _ s

@[simp]
theorem mapVal_id {S : Type v} {X : C} : mapVal (𝟙 X) = 𝟙 (copower S X) := by
  apply ext
  intro s
  rw [mapVal_inj, Category.id_comp, Category.comp_id]

@[simp]
theorem mapVal_comp {S : Type v} {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    mapVal (f ≫ g) = mapVal f ≫ mapVal (S := S) g := by
  apply ext
  intro s
  calc inj S X s ≫ mapVal (f ≫ g) = (f ≫ g) ≫ inj S Z s := mapVal_inj _ s
    _ = f ≫ g ≫ inj S Z s := by rw [Category.assoc]
    _ = f ≫ (inj S Y s ≫ mapVal g) := by rw [← mapVal_inj g s]
    _ = (f ≫ inj S Y s) ≫ mapVal g := by rw [← Category.assoc]
    _ = (inj S X s ≫ mapVal f) ≫ mapVal g := by rw [← mapVal_inj f s]
    _ = inj S X s ≫ mapVal f ≫ mapVal g := by rw [Category.assoc]

/-- Functorial action of copowers on the indexing type.
Given `f : S → T`, we get `mapIdx f : S · X → T · X`. -/
def mapIdx {S T : Type v} {X : C} (f : S → T) : copower S X ⟶ copower T X :=
  desc (fun s => inj T X (f s))

@[simp]
theorem mapIdx_inj {S T : Type v} {X : C} (f : S → T) (s : S) :
    inj S X s ≫ mapIdx f = inj T X (f s) := fac _ s

@[simp]
theorem mapIdx_id {S : Type v} {X : C} : mapIdx (id : S → S) = 𝟙 (copower S X) := by
  apply ext
  intro s
  rw [mapIdx_inj, id_eq, Category.comp_id]

@[simp]
theorem mapIdx_comp {S T U : Type v} {X : C} (f : S → T) (g : T → U) :
    mapIdx (g ∘ f) = mapIdx f ≫ mapIdx (X := X) g := by
  apply ext
  intro s
  calc inj S X s ≫ mapIdx (g ∘ f) = inj U X ((g ∘ f) s) := mapIdx_inj _ s
    _ = inj U X (g (f s)) := rfl
    _ = inj T X (f s) ≫ mapIdx g := (mapIdx_inj g _).symm
    _ = (inj S X s ≫ mapIdx f) ≫ mapIdx g := by rw [← mapIdx_inj f s]
    _ = inj S X s ≫ mapIdx f ≫ mapIdx g := by rw [Category.assoc]

/-- Combined functorial action: given `f : S → T` and `g : X → Y`,
we get `bimap f g : S · X → T · Y`. -/
def bimap {S T : Type v} {X Y : C} (f : S → T) (g : X ⟶ Y) :
    copower S X ⟶ copower T Y :=
  desc (fun s => g ≫ inj T Y (f s))

@[simp]
theorem bimap_inj {S T : Type v} {X Y : C} (f : S → T) (g : X ⟶ Y) (s : S) :
    inj S X s ≫ bimap f g = g ≫ inj T Y (f s) := fac _ s

theorem bimap_eq_mapIdx_mapVal {S T : Type v} {X Y : C} (f : S → T) (g : X ⟶ Y) :
    bimap f g = mapIdx f ≫ mapVal (S := T) g := by
  apply ext
  intro s
  rw [bimap_inj, ← Category.assoc, mapIdx_inj, mapVal_inj]

theorem bimap_eq_mapVal_mapIdx {S T : Type v} {X Y : C} (f : S → T) (g : X ⟶ Y) :
    bimap f g = mapVal g ≫ mapIdx (X := Y) f := by
  apply ext
  intro s
  calc inj S X s ≫ bimap f g = g ≫ inj T Y (f s) := bimap_inj _ _ s
    _ = g ≫ (inj S Y s ≫ mapIdx f) := by rw [← mapIdx_inj f s]
    _ = (g ≫ inj S Y s) ≫ mapIdx f := by rw [← Category.assoc]
    _ = (inj S X s ≫ mapVal g) ≫ mapIdx f := by rw [← mapVal_inj g s]
    _ = inj S X s ≫ mapVal g ≫ mapIdx f := by rw [Category.assoc]

@[simp]
theorem bimap_id {S : Type v} {X : C} : bimap (id : S → S) (𝟙 X) = 𝟙 (copower S X) := by
  apply ext
  intro s
  rw [bimap_inj, id_eq, Category.id_comp, Category.comp_id]

@[simp]
theorem bimap_comp {S T U : Type v} {X Y Z : C}
    (f₁ : S → T) (g₁ : X ⟶ Y) (f₂ : T → U) (g₂ : Y ⟶ Z) :
    bimap (f₂ ∘ f₁) (g₁ ≫ g₂) = bimap f₁ g₁ ≫ bimap f₂ g₂ := by
  apply ext
  intro s
  have step1 : inj S X s ≫ bimap (f₂ ∘ f₁) (g₁ ≫ g₂) =
      (g₁ ≫ g₂) ≫ inj U Z (f₂ (f₁ s)) := bimap_inj _ _ s
  calc inj S X s ≫ bimap (f₂ ∘ f₁) (g₁ ≫ g₂)
      = (g₁ ≫ g₂) ≫ inj U Z (f₂ (f₁ s)) := step1
    _ = g₁ ≫ g₂ ≫ inj U Z (f₂ (f₁ s)) := by rw [Category.assoc]
    _ = g₁ ≫ (inj T Y (f₁ s) ≫ bimap f₂ g₂) := by rw [← bimap_inj f₂ g₂]
    _ = (g₁ ≫ inj T Y (f₁ s)) ≫ bimap f₂ g₂ := by rw [← Category.assoc]
    _ = (inj S X s ≫ bimap f₁ g₁) ≫ bimap f₂ g₂ := by rw [← bimap_inj f₁ g₁]
    _ = inj S X s ≫ bimap f₁ g₁ ≫ bimap f₂ g₂ := by rw [Category.assoc]

/-- Postcomposing desc with a morphism: `desc f ≫ g = desc (fun s => f s ≫ g)`. -/
theorem desc_comp {S : Type v} {X Y Z : C} (f : S → (X ⟶ Y)) (g : Y ⟶ Z) :
    desc f ≫ g = desc (fun s => f s ≫ g) := by
  apply ext
  intro s
  rw [← Category.assoc, fac, ← fac (fun s' => f s' ≫ g) s]

/-- If the families commute with postcomposition, then desc respects it. -/
theorem desc_postcomp_eq {S : Type v} {X Y Z : C} (f : S → (X ⟶ Y)) (h : S → (X ⟶ Z))
    (g : Y ⟶ Z) (hfg : ∀ s, f s ≫ g = h s) :
    desc f ≫ g = desc h := by
  rw [desc_comp]
  congr 1
  funext s
  exact hfg s

/-- Copower round-trip: `desc (fun s => inj s ≫ g) = g`. -/
@[simp]
theorem desc_inj {S : Type v} {X Y : C} (g : copower S X ⟶ Y) :
    desc (fun s => inj S X s ≫ g) = g := by
  apply ext
  intro s
  rw [fac]

end HasCopowers

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

namespace Limits.Cocones

/-- The `.hom` field of an `eqToHom` morphism between cocones equals `eqToHom` of
the corresponding equality of apex points. -/
@[simp]
theorem eqToHom_hom {J : Type*} [Category J] {C' : Type*} [Category C']
    {F : J ⥤ C'} {A B : Cocone F} (h : A = B) :
    (eqToHom h).hom = eqToHom (congrArg Cocone.pt h) := by subst h; rfl

end Limits.Cocones

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

end MendlerCowedgeCorrespondence

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

end GebLean
