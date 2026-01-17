# Weighted Cowedges as Canonical Restricted Cowedge Definition

## Motivation

The current `RestrictedCowedge` definition uses dinaturality conditions
(following Vene's thesis), but there's an alternative using paranaturality.
For ordinary wedges, dinaturality and paranaturality coincide because the
wedge conditions form a commutative square that can be read in either
direction. However, for restricted cowedges, the two choices lead to
potentially different definitions.

This workstream investigates whether weighted colimits provide a
"canonical" definition that resolves this ambiguity.

## Background

### Existing Wedge-to-Cone Correspondence

In `GebLean/Weighted.lean`, we have:

- `coneToWedge` (line ~247): Converts a cone over the twisted arrow diagram
  to a wedge
- `wedgeToCone` (line ~328): Converts a wedge to a cone over the twisted
  arrow diagram
- `coconeToCowedge` (line ~469): Converts a cocone to a cowedge
- `cowedgeToCocone` (line ~455): Converts a cowedge to a cocone

This establishes that wedges over `F : Cᵒᵖ ⥤ C ⥤ D` correspond to
cones over `profunctorOnTwistedArrow C F : TwistedArrow C ⥤ D`.

### Twisted Arrow Infrastructure

In `GebLean/Utilities/TwistedArrow.lean`:

- `twistedArrowForget : TwistedArrow C ⥤ Cᵒᵖ × C` - forgetful functor
- `coTwistedArrowForget : CoTwistedArrow C ⥤ Cᵒᵖᵒᵖ × Cᵒᵖ` - forgetful
  functor for the co-twisted arrow category

In `GebLean/Utilities/TwArrPresheaf.lean`:

- `profunctorOnTwistedArrow` (line ~1590): Pre-composes a profunctor with
  the twisted arrow forgetful functor
- `profunctorOnCoTwistedArrow` (line ~1623): Pre-composes a profunctor with
  the co-twisted arrow forgetful functor

### Weighted Colimits

Mathlib does not currently have explicit weighted limit/colimit definitions.
See `docs/mathlib-limits-colimits-guide.md` for details.

From the documentation:

- Ends and coends are weighted limits/colimits with the hom-functor as weight
- Kan extensions are weighted colimits when computed pointwise

External references:

- [Weighted Limits and Colimits (Riehl)](https://math.jhu.edu/~eriehl/weighted.pdf)
- [nLab: weighted colimit](https://ncatlab.org/nlab/show/weighted+colimit)

### Vene's Restricted Coend

From `docs/restricted-coends.md`:

A restricted cowedge involves:

- An endodifunctor `G : Cᵒᵖ × C → C`
- A difunctor `H : Cᵒᵖ × C → Set`
- A dinatural transformation between `H` and `G/C` (the slice profunctor)

## Tasks

### 1. Define Weighted Cones (General)

A weighted cone over `D : J ⥤ C` with weight `W : J ⥤ Type v` consists of:

- An object `c : C`
- For each `j : J` and `w : W.obj j`, a morphism `π j w : c ⟶ D.obj j`
- Naturality: for `f : j ⟶ j'` and `w : W.obj j`, we have
  `D.map f ∘ π j w = π j' (W.map f w)`

Equivalently: a natural transformation `W ⟶ Hom(c, D(-))`.

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 580)

**Implementation**: `WeightedCone W D` with `π : W ⟶ homFromFunctor pt D`

### 2. Define Weighted Cocones (General)

Dual to weighted cones:

- An object `c : C`
- For each `j : J` and `w : W.obj j`, a morphism `ι j w : D.obj j ⟶ c`
- Naturality: for `f : j ⟶ j'` and `w : W.obj j'`, we have
  `ι j' w ∘ D.map f = ι j (W.map f w)`

Equivalently: a natural transformation `W ⟶ Hom(D(-), c)` where `W : Jᵒᵖ ⥤ Type v`.

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 613)

**Implementation**: `WeightedCocone W D` with `ι : W ⟶ homToFunctor D pt`

### 3. Define Weighted Wedges

A weighted wedge combines the twisted arrow reduction with weighted cones:

Given `P : Cᵒᵖ ⥤ C ⥤ D` and weight `W : TwistedArrow C ⥤ Type v`:

- Reduce `P` to a diagram on `TwistedArrow C` via `profunctorOnTwistedArrow`
- Take a weighted cone with weight `W`

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 648)

**Implementation**:
`WeightedWedge W P := WeightedCone W (profunctorOnTwistedArrow C P)`

### 4. Define Weighted Cowedges

Dual construction using weighted cocones.

For restricted cowedges specifically:

- The weight `W : (CoTwistedArrow C)ᵒᵖ ⥤ Type v` is a presheaf on the
  co-twisted arrow category
- The functor `G : Cᵒᵖ ⥤ C ⥤ C` becomes a diagram via
  `profunctorOnCoTwistedArrow`

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 662)

**Implementation**:
`WeightedCowedge W P := WeightedCocone W (profunctorOnCoTwistedArrow C P)`

### 5. Compare with Vene's Restricted Cowedge (Dinaturality)

The current `RestrictedCowedge` in `GebLean/Weighted.lean` uses:

- `ParanatSig H (G ⇓ pt)` for the family structure
- `IsDinatural H (G ⇓ pt) family` for the dinaturality condition

Compare this with the weighted cowedge definition from Task 4.

Questions to answer:

- Are they equivalent?
- If not, what's the relationship?
- Which captures Vene's original definition more faithfully?

**Status**: In progress

**Findings**:

The two structures are not directly equivalent:

1. **Weighted cowedge** (`WeightedCowedge W G`): Uses a weight functor
   `W : (CoTwistedArrow C)ᵒᵖ ⥤ Type v` and provides data at *all* co-twisted
   arrows (morphisms `f : A ⟶ B` in `C`).

2. **Restricted cowedge** (`RestrictedCowedge G H`): Uses a profunctor
   `H : Cᵒᵖ ⥤ C ⥤ Type v` but only provides data at *diagonal* elements
   (identity morphisms `id_A : A ⟶ A`), with a dinaturality condition
   relating the diagonal data across different objects.

The relationship:

- A restricted cowedge can be seen as specifying the "diagonal restriction"
  of a potential weighted cowedge
- The dinaturality condition ensures consistency of the diagonal data
- To get a weight `W` from `H`, one would compose `H` with the co-twisted
  arrow forgetful functor: `profunctorOnCoTwistedArrow C H`
- The restricted cowedge only uses diagonal values of this composition

Vene's original definition uses dinaturality, so `RestrictedCowedge` is
faithful to Vene's thesis. The weighted formulation is more general but
requires data at all co-twisted arrows, not just diagonals.

### 6. Define Strong Restricted Cowedges

Define `StrongRestrictedCowedge` analogously to `RestrictedCowedge`, but using
`IsParanatural` instead of `IsDinatural`. Paranatural transformations are also
called "strong dinatural transformations", hence the name.

The structure should have:

- `pt : C` - the summit object
- `family : ParanatSig H (G ⇓ pt)` - the family of morphisms
- `isParanatural : IsParanatural H (G ⇓ pt) family` - paranaturality condition

Define the category of strong restricted cowedges with the same notion of
homomorphism as for `RestrictedCowedge` (post-composition commuting with the
family). Verify that this forms a category by proving the identity and
associativity laws.

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 966)

**Implementation**:

- `StrongRestrictedCowedge G H` structure with `pt`, `family`, `isParanatural`
- `StrongRestrictedCowedge.toParanat`: Convert to `Paranat H (G ⇓ pt)`
- `StrongRestrictedCowedge.ofParanat`: Convert from `Paranat H (G ⇓ pt)`
- `StrongRestrictedCowedge.toRestrictedCowedge`: Every strong restricted
  cowedge is a restricted cowedge (paranaturality implies dinaturality)
- `StrongRestrictedCowedge.Hom`: Morphisms between strong restricted cowedges
- `StrongRestrictedCowedge.Hom.id`, `Hom.comp`: Identity and composition
- `StrongRestrictedCowedgeCat`: Category instance for strong restricted cowedges
- `inclusion`: Inclusion functor from strong restricted cowedges to
  restricted cowedges
- `inclusion_fullyFaithful`: Proof that the inclusion is fully faithful,
  making strong restricted cowedges a full subcategory

### 7. Compare with Paranaturality Version

Compare `StrongRestrictedCowedge` (from Task 6) with `RestrictedCowedge` and
with weighted cowedges (from Task 4).

Questions to answer:

- Is `StrongRestrictedCowedge` equivalent to the weighted cowedge?
- Is it equivalent to `RestrictedCowedge` (the dinaturality version)?
- If all three differ, which is "correct"?

**Status**: Completed

**Findings**:

The three definitions form a hierarchy with strict inclusions:

```text
WeightedCowedge  ⊋  StrongRestrictedCowedge  ⊋  RestrictedCowedge
   (most data)         (paranaturality)          (dinaturality)
```

**1. StrongRestrictedCowedge vs RestrictedCowedge**:

- `StrongRestrictedCowedge.toRestrictedCowedge` exists (paranaturality implies
  dinaturality)
- The reverse does NOT hold in general
- Paranaturality tests ALL compatible diagonal pairs `(d₀, d₁)` with
  `DiagCompat F I₀ I₁ f d₀ d₁`
- Dinaturality only tests pairs of the form `(F.lmap f x, F.rmap f x)` for
  off-diagonal elements `x`
- Not every compatible pair arises from an off-diagonal element

**2. WeightedCowedge vs StrongRestrictedCowedge**:

- WeightedCowedge provides data at ALL co-twisted arrows (all morphisms in C)
- StrongRestrictedCowedge provides data only at diagonal elements
- The weighted formulation has strictly more data
- To embed StrongRestrictedCowedge into WeightedCowedge, one would need to
  extend diagonal data to all co-twisted arrows (likely via Kan extension)
- This extension is not generally unique or canonical without additional
  structure

**3. Relationship to Vene's Definition**:

- Vene's original definition uses dinaturality, so `RestrictedCowedge` matches
  Vene's thesis
- `StrongRestrictedCowedge` is a strengthening that uses paranaturality
- `WeightedCowedge` is the most general formulation from first principles

### 8. Determine Canonical Definition

Based on the comparisons in Tasks 5 and 7:

- If all definitions coincide, document this equivalence
- If they differ, determine which is canonical (likely the weighted
  cowedge, as it's derived from first principles)
- Update the codebase accordingly

**Status**: Completed

**Conclusion**:

The three definitions are NOT equivalent and serve different purposes. Which
is "canonical" depends on context:

**For Vene's Mendler-style recursion (original motivation)**:

Use `RestrictedCowedge` (dinaturality). This matches Vene's thesis exactly and
is sufficient for the categorical semantics of inductive and coinductive types.

**For the strongest condition on diagonal data**:

Use `StrongRestrictedCowedge` (paranaturality). This is a natural strengthening
that preserves all compatible diagonal pairs, not just those arising from
off-diagonal elements. Useful when paranaturality is required by the
application.

**For the most general weighted formulation**:

Use `WeightedCowedge`. This is derived from first principles of weighted
colimits and provides data at all morphisms, not just identities. This is the
"correct" categorical formulation when full generality is needed.

**Recommendation**:

Keep all three definitions in the codebase:

1. `RestrictedCowedge`: For Vene-style restricted coends
2. `StrongRestrictedCowedge`: For applications requiring paranaturality
3. `WeightedCowedge`: For general weighted colimit theory

The fully faithful inclusion functor `StrongRestrictedCowedge → RestrictedCowedge`
establishes that strong restricted cowedges form a full subcategory of restricted
cowedges. The relationship between `WeightedCowedge` and the restricted variants
would require additional work (diagonal restriction and Kan extension) to
formalize.

### 9. Upgrade Wedge/Cone Correspondence to Categorical Equivalence

The existing `coneToWedge` and `wedgeToCone` functions establish a correspondence
between cones over `profunctorOnTwistedArrow C F` and wedges over `F`. Mathlib
provides `Category` instances for both `Cone` and `Wedge` (where `Wedge` is an
abbreviation for `Multifork`). We should upgrade this correspondence to a full
categorical equivalence.

Steps:

- Verify mathlib's `Category` instance for `Cone F`
- Verify mathlib's `Category` instance for `Wedge F` (via `Multifork`)
- Define a functor `Wedge F ⥤ Cone (profunctorOnTwistedArrow C F)`
- Define a functor `Cone (profunctorOnTwistedArrow C F) ⥤ Wedge F`
- Prove these form an equivalence of categories

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 400)

**Implementation**:

- `wedgeToConeFunctor`: Functor from wedges to cones
- `coneToWedgeFunctor`: Functor from cones to wedges
- `wedgeConeUnitIso`: Unit natural isomorphism using `eqToIso` and
  `coneToWedge_wedgeToCone`
- `wedgeConeCounitIso`: Counit natural isomorphism using `eqToIso` and
  `wedgeToCone_coneToWedge`
- `wedgeConeEquiv`: The categorical equivalence
  `Wedge P ≌ Cone (profunctorOnTwistedArrow C P)`

Helper lemma `Cone.eqToHom_hom` handles `eqToHom` simplification in
naturality proofs for cone morphisms. The `functor_unitIso_comp` proof uses
`Category.id_comp` to simplify the identity composition.

### 10. Prove Cones Are Weighted Cones with Constant Weight

Ordinary cones should be a special case of weighted cones where the weight
functor is the constant functor returning the terminal object (a singleton type).
Specifically:

- For a cone over `D : J ⥤ C`, the weight is `(const J).obj PUnit`
- The weighted cone structure `W ⟶ Hom(pt, D(-))` specializes to
  `(const J).obj PUnit ⟶ Hom(pt, D(-))`, which is equivalent to picking one
  morphism `pt ⟶ D(j)` for each `j`

This equivalence will validate that our `WeightedCone` definition is correct.

Steps:

- Define `coneToWeightedCone`: Convert a `Cone D` to a `WeightedCone` with
  constant weight
- Define `weightedConeToCone`: Convert a weighted cone with constant weight to
  a `Cone D`
- Prove these are inverse (up to isomorphism)
- Optionally, upgrade to a categorical equivalence

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 690)

**Implementation**:

- `unitWeight J`: Constant functor `(Functor.const J).obj PUnit.{v + 1}`
- `unitWeightOp J`: Contravariant version for cocones
- `coneToWeightedCone`: Converts `Cone D` to `WeightedCone (unitWeight J) D`
- `weightedConeToCone`: Converts weighted cone back to ordinary cone
- `coneToWeightedCone_weightedConeToCone`: Round-trip `rfl`
- `weightedConeToCone_coneToWeightedCone`: Round-trip equality proven via `ext`
- Analogous functions for cocones

### 11. Verify Weighted Cocone Direction

For ordinary cocones, the natural transformation goes `ι : F ⟶ (const J).obj pt`
(from the diagram to the constant functor). For weighted cocones, by the
universal property of weighted colimits:

```text
Hom(colim_W D, c) ≅ Nat(W, Hom(D(-), c))
```

A weighted cocone with apex `c` IS a natural transformation `W ⟶ Hom(D(-), c)`.
This means the natural transformation goes TO the hom-functor, not FROM it.

Our current definition has `ι : W ⟶ homToFunctor D pt`, which matches this.
However, the "direction" interpretation differs from ordinary cocones because:

- Ordinary cocone: `D(j) → pt` for each `j` (morphisms go TO the apex)
- Weighted cocone: For each `j` and `w : W(j)`, a morphism `D(j) → pt`

The weight `W : Jᵒᵖ ⥤ Type v` being contravariant accounts for the direction.

Steps:

- Implement `coconeToWeightedCocone` with constant weight
- Implement `weightedCoconeToCocone` in the opposite direction
- Verify these are inverse to confirm the direction is correct
- If the equivalence fails, diagnose and fix `WeightedCocone`

**Status**: Completed

**Verification**: The round-trip theorems compile and prove that the direction
is correct. The naturality condition in `coconeToWeightedCocone` requires
`.symm` because cocone naturality `D.map f ≫ c.ι.app j' = c.ι.app j` is
opposite to the weighted cocone naturality direction. This asymmetry is
expected because the weight `W : Jᵒᵖ ⥤ Type v` is contravariant.

### 11.5. Define Category Instances for Weighted Cones and Cocones

Before upgrading the cone/weighted-cone correspondence to a categorical
equivalence, we need to define `Category` instances for `WeightedCone` and
`WeightedCocone`.

Steps:

- Define `WeightedCone.Hom W D c₁ c₂`: Morphisms between weighted cones
- Prove identity and composition laws
- Define `Category (WeightedCone W D)` instance
- Repeat for `WeightedCocone`

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 762)

**Implementation**:

- `WeightedCone.Hom`: Morphisms with `hom : c₁.pt ⟶ c₂.pt` and commutativity
  condition `∀ j w, hom ≫ c₂.leg j w = c₁.leg j w`
- `WeightedCone.Hom.id`, `WeightedCone.Hom.comp`: Identity and composition
- `Category (WeightedCone W D)` instance
- `WeightedCocone.Hom`: Dual construction with commutativity
  `∀ j w, c₁.leg j w ≫ hom = c₂.leg j w`
- `Category (WeightedCocone W D)` instance

### 12. Upgrade Cone/Weighted-Cone to Categorical Equivalence

Upgrade the existing `coneToWeightedCone` and `weightedConeToCone` functions
to a full categorical equivalence between `Cone D` and
`WeightedCone (unitWeight J) D`.

Steps:

- Define `coneToWeightedConeFunctor`: Functor from cones to weighted cones
- Define `weightedConeToConeFunctor`: Functor from weighted cones to cones
- Prove unit and counit natural isomorphisms
- Construct `coneWeightedConeEquiv : Cone D ≌ WeightedCone (unitWeight J) D`

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 1270)

**Implementation**:

- `coneToWeightedConeFunctor`: Functor from cones to weighted cones
- `weightedConeToConeFunctor`: Functor from weighted cones to cones
- `coneWeightedConeUnitIso`: Unit natural isomorphism
- `coneWeightedConeCounitIso`: Counit natural isomorphism
- `coneWeightedConeEquiv`: The categorical equivalence
  `Cone D ≌ WeightedCone (unitWeight J) D`

### 13. Upgrade Cocone/Weighted-Cocone to Categorical Equivalence

Dual of Task 12 for cocones.

Steps:

- Define functors between `Cocone D` and `WeightedCocone (unitWeightOp J) D`
- Prove unit and counit natural isomorphisms
- Construct `coconeWeightedCoconeEquiv`

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 1380)

**Implementation**:

- `coconeToWeightedCoconeFunctor`: Functor from cocones to weighted cocones
- `weightedCoconeToCocone Functor`: Functor from weighted cocones to cocones
- `coconeWeightedCoconeUnitIso`: Unit natural isomorphism
- `coconeWeightedCoconeCounitIso`: Counit natural isomorphism
- `coconeWeightedCoconeEquiv`: The categorical equivalence
  `Cocone D ≌ WeightedCocone (unitWeightOp J) D`

### 14. Prove Weighted Cones Are Cones over Category of Elements

A weighted cone with weight `W : J ⥤ Type v` over diagram `D : J ⥤ C` should
be equivalent to an ordinary cone over a functor defined on `W.Elements`, the
covariant category of elements from mathlib.

For `W : J ⥤ Type v`, mathlib defines `W.Elements` (in
`Mathlib/CategoryTheory/Elements.lean` line 48) as a sigma type `Σ j : J, W.obj j`
with morphisms `(j, w) ⟶ (j', w')` being morphisms `f : j ⟶ j'` such that
`W.map f w = w'`.

The idea:

- Define a functor `D' : W.Elements ⥤ C` by `D'(j, w) := D.obj j`
- A weighted cone `W ⟶ Hom(pt, D(-))` corresponds to a cone over `D'`
- The weight element `w : W.obj j` picks out the projection `pt ⟶ D.obj j`

Steps:

- Define functor `weightedDiagram : W.Elements ⥤ C` from `D : J ⥤ C`
- Define `weightedConeToConeElements`: Convert weighted cone to cone over elements
- Define `coneElementsToWeightedCone`: Convert cone over elements to weighted cone
- Prove equivalence
- Upgrade to categorical equivalence

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 1489)

**Implementation**:

- `weightedConeToElementsCone`: Converts weighted cone to cone over elements
- `elementsConeToWeightedCone`: Converts cone over elements to weighted cone
- `weightedConeToElementsConeFunctor`: Functor from weighted cones to cones
- `elementsConeToWeightedConeFunctor`: Functor in the opposite direction
- `weightedConeElementsUnitIso`: Unit natural isomorphism
- `weightedConeElementsCounitIso`: Counit natural isomorphism
- `weightedConeElementsEquiv`: The categorical equivalence
  `WeightedCone W D ≌ Cone (CategoryOfElements.π W ⋙ D)`

**Reference**: `Mathlib/CategoryTheory/Elements.lean` line 48 for `Functor.Elements`

### 15. Prove Weighted Cocones Are Cocones over Contravariant Category of Elements

Dual of Task 14. A weighted cocone with weight `W : Jᵒᵖ ⥤ Type v` over diagram
`D : J ⥤ C` should be equivalent to an ordinary cocone over a functor defined
on `W.ElementsPre`, the contravariant category of elements.

Our codebase defines `F.ElementsPre` (in `GebLean/Utilities/Elements.lean`
line 569) as `F.Elementsᵒᵖ` for presheaves `F : Cᵒᵖ ⥤ Type w`.

Steps:

- Define functor `weightedCoDiagram : W.ElementsPre ⥤ C` from `D : J ⥤ C`
- Define `weightedCoconeToCoconeElements`: Convert weighted cocone to cocone
- Define `coconeElementsToWeightedCocone`: Convert cocone to weighted cocone
- Prove equivalence
- Upgrade to categorical equivalence

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 1660)

**Implementation**:

- `weightedCoconeDiagram`: Functor `(W.Elements)ᵒᵖ ⥤ C` via the projection
- `weightedCoconeToElementsCocone`: Converts weighted cocone to cocone over
  elements
- `elementsCoconeToWeightedCocone`: Converts cocone over elements to weighted
  cocone
- `weightedCoconeToElementsCoconeFunctor`: Functor from weighted cocones to
  cocones
- `elementsCoconeToWeightedCoconeFunctor`: Functor in the opposite direction
- `weightedCoconeElementsUnitIso`: Unit natural isomorphism
- `weightedCoconeElementsCounitIso`: Counit natural isomorphism
- `weightedCoconeElementsEquiv`: The categorical equivalence
  `WeightedCocone W D ≌ Cocone (weightedCoconeDiagram W D)`

**Reference**: Uses mathlib's `CategoryOfElements.π` and `unopUnop` for the
diagram functor construction.

### 16. Compose Equivalences: Weighted Wedges Reduce to Cones

Since weighted wedges are defined as weighted cones over twisted arrow diagrams:

```text
WeightedWedge W P := WeightedCone W (profunctorOnTwistedArrow C P)
```

And by Task 14, weighted cones are equivalent to cones over the category of
elements, we can compose these equivalences to show:

```text
WeightedWedge W P ≌ Cone (weightedDiagram W (profunctorOnTwistedArrow C P))
```

Where the right-hand side is an ordinary cone over a diagram on `W.Elements`.

Steps:

- Apply the equivalence from Task 14 to the weighted wedge case
- Verify that the composition gives the expected result
- Document the full chain of equivalences

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 1701)

**Implementation**:

- `weightedWedgeDiagram`: Functor `W.Elements ⥤ D` via
  `CategoryOfElements.π W ⋙ profunctorOnTwistedArrow C P`
- `weightedWedgeElementsEquiv`: The categorical equivalence
  `WeightedWedge W P ≌ Cone (weightedWedgeDiagram W P)`

This follows directly by applying `weightedConeElementsEquiv` to the definition
of `WeightedWedge` as a `WeightedCone` over the twisted arrow diagram.

### 17. Compose Equivalences: Weighted Cowedges Reduce to Cocones

Dual of Task 16. Since weighted cowedges are defined as weighted cocones:

```text
WeightedCowedge W P := WeightedCocone W (profunctorOnCoTwistedArrow C P)
```

And by Task 15, weighted cocones are equivalent to cocones over the
contravariant category of elements, we can compose to show:

```text
WeightedCowedge W P ≌ Cocone (weightedCoDiagram W (profunctorOnCoTwistedArrow C P))
```

Steps:

- Apply the equivalence from Task 15 to the weighted cowedge case
- Verify the composition
- Document the full chain of equivalences

**Status**: Completed

**Location**: `GebLean/Weighted.lean` (~line 1712)

**Implementation**:

- `weightedCowedgeDiagram`: Functor `(W.Elements)ᵒᵖ ⥤ D` via
  `weightedCoconeDiagram W (profunctorOnCoTwistedArrow C P)`
- `weightedCowedgeElementsEquiv`: The categorical equivalence
  `WeightedCowedge W P ≌ Cocone (weightedCowedgeDiagram W P)`

This follows directly by applying `weightedCoconeElementsEquiv` to the
definition of `WeightedCowedge` as a `WeightedCocone` over the co-twisted
arrow diagram.

### 18. Alternative Characterization: Weighted Wedges as Ordinary Wedges

We defined weighted wedges as weighted cones over twisted arrow diagrams,
which reduces them to ordinary cones. An alternative approach would be to
express weighted wedges as ordinary wedges over a derived profunctor.

**Question**: Given `W : TwistedArrow C ⥤ Type v` and `P : Cᵒᵖ ⥤ C ⥤ D`, is
there a category `C'` and profunctor `P' : C'ᵒᵖ ⥤ C' ⥤ D` such that:

```text
WeightedWedge W P ≌ Wedge P'
```

**Approach**: The chain of equivalences gives us:

```text
WeightedWedge W P ≌ Cone (CategoryOfElements.π W ⋙ profunctorOnTwistedArrow C P)
```

For this to factor through ordinary wedges, we need `TwistedArrow C' ≅ W.Elements`
for some `C'`. A natural candidate:

- Take `C' := W.Elements` as a category
- Define `P' : C'ᵒᵖ ⥤ C' ⥤ D` by `P'((tw₁, w₁), (tw₂, w₂)) := P(tw₁.src, tw₂.tgt)`
- Then diagonal `P'((tw, w), (tw, w)) = P(tw.src, tw.tgt)` matches the weighted
  wedge target

**Status**: Completed (negative result)

**Findings**: Variance Obstruction

The naive approach of defining `P'((tw₁, w₁), (tw₂, w₂)) := P(twDom tw₁, twCod tw₂)`
does NOT extend to a profunctor on `W.Elements` with the correct variance.

For a TwistedArrow morphism `f : tw₁ ⟶ tw₂`:

- `twDomArr f : twDom tw₂ ⟶ twDom tw₁` (contravariant in domain)
- `twCodArr f : twCod tw₁ ⟶ twCod tw₂` (covariant in codomain)

For `P : Cᵒᵖ ⥤ C ⥤ D` (contravariant in first arg, covariant in second):

- The second argument works: `twCodArr` is covariant, matching P's second slot
- The first argument fails: `twDomArr` is contravariant, and when composed with
  P's contravariance and the opposite category structure, we get the wrong
  direction for the overall morphism

Specifically, for `f : X ⟶ Y` in `(W.Elements)ᵒᵖ`:

- We need a morphism from X's output to Y's output
- But `P.map (twDomArr f.unop.val).op` gives Y's output to X's output

**Conclusion**: The weighted cone/cocone approach (Tasks 16-17) remains the
canonical way to reduce weighted wedges to ordinary cones/cocones. The direct
reduction to ordinary wedges over a derived profunctor does not work due to
this variance obstruction.

**Location**: Documented in `GebLean/Weighted.lean` section `WeightedWedgeAsProfunctor`

### 19. Weighted Cowedges as Full Subcategory of Strong Restricted Cowedges

When `D = C` (the endofunctor case), weighted cowedges should relate to
restricted cowedges. Since strong restricted cowedges use paranaturality
(which is stronger than dinaturality), we conjecture that weighted cowedges
embed as a full subcategory of strong restricted cowedges.

**Setup**: For weighted cowedges with `D = C`:

- `W : (CoTwistedArrow C)ᵒᵖ ⥤ Type v` - weight functor
- `P : Cᵒᵖ ⥤ C ⥤ C` - endodifunctor (playing the role of `G`)

For strong restricted cowedges:

- `G : Cᵒᵖ ⥤ C ⥤ C` - endodifunctor
- `H : Cᵒᵖ ⥤ C ⥤ Type v` - restriction profunctor
- `IsParanatural H (G ⇓ pt) family` - paranaturality condition

**Observation**: The "diagonal restriction" of `W` to identity co-twisted
arrows gives a profunctor. Define `H(A, B) := W(op (CoTwistedArrow.mk (𝟙 A)))`
... but this only captures diagonal data.

However, the relationship may be more subtle. A weighted cowedge provides
data at ALL co-twisted arrows, while a strong restricted cowedge only has
data at diagonal elements satisfying paranaturality.

**Conjecture**: There exists a functor

```text
WeightedCowedgeCat W P ⥤ StrongRestrictedCowedgeCat P H
```

where `H` is derived from `W` by diagonal restriction, and this functor is
fully faithful (making weighted cowedges a full subcategory).

Steps:

- Define the diagonal restriction `diagonalRestriction W : Cᵒᵖ ⥤ C ⥤ Type v`
  from a weight `W : (CoTwistedArrow C)ᵒᵖ ⥤ Type v`
- Define `weightedCowedgeToStrongRestricted` converting weighted cowedges to
  strong restricted cowedges
- Verify that weighted cowedge naturality implies paranaturality
- Define the functor on morphisms
- Prove the functor is fully faithful

If successful, the relationship with ordinary restricted cowedges follows by
composing with the inclusion `StrongRestrictedCowedgeCat ⥤ RestrictedCowedgeCat`.

**Status**: Completed (negative result)

**Findings**: Variance Obstruction for Diagonal Restriction

A direct embedding from weighted cowedges to strong restricted cowedges faces a
fundamental variance obstruction, analogous to Task 18's findings.

#### Problem 1: Co-twisted Arrow Morphisms Between Diagonals

To define a profunctor `H : Cᵒᵖ ⥤ C ⥤ Type v` from
`W : (CoTwistedArrow C)ᵒᵖ ⥤ Type v` such that `diagApp H A = weightDiagElem W A`,
we need H to be functorial.

For a morphism `f : A' ⟶ A`, we need `(H.map f.op).app B` which requires
`W.obj (op (diagCoTwArr A)) → W.obj (op (diagCoTwArr A'))`, i.e., a co-twisted
arrow morphism `diagCoTwArr A' ⟶ diagCoTwArr A`.

Such a morphism requires:

- `l : A ⟶ A'` (domain direction)
- `r : A' ⟶ A` (codomain direction)
- `l = r` (compatibility condition)

This means `l` and `r` must be inverse isomorphisms, so morphisms between
diagonal co-twisted arrows only exist when the objects are isomorphic.

#### Problem 2: Trivial Profunctor Case

Using `constProfunctor T` (where `DiagCompat = equality`) doesn't help because:

- Weighted cowedges have varying diagonal types: `weightDiagElem W A` differs
  by A
- Constant profunctors have the same type T at all objects

#### Partial Result: Paranaturality Along Isomorphisms

Weighted cowedge naturality DOES give a "paranaturality along isomorphisms"
result:

```lean
theorem WeightedCowedge.diagFamilySig_iso_naturality
    {W : (CoTwistedArrow C)ᵒᵖ ⥤ Type v} {P : Cᵒᵖ ⥤ C ⥤ C}
    (c : WeightedCowedge W P) {A B : C} (i : A ≅ B)
    (wB : weightDiagElem W B) :
    profunctorDiagIsoAction i ≫ c.diagFamilySig B wB =
      c.diagFamilySig A (weightDiagTransport W i wB)
```

#### Cases Where Embedding Works

1. **Groupoids**: When C is a groupoid, all morphisms are isomorphisms, so the
   variance obstruction disappears and full paranaturality follows.

2. **Constant Weight on Diagonals**: If `weightDiagElem W A = T` for all A,
   we can use `H = constProfunctor T`, but paranaturality is very restrictive.

3. **Single-Object Category**: When C has one object, only one diagonal
   co-twisted arrow exists.

#### Conclusion

The conjectured embedding does not exist for general categories and weights.
The relationship between weighted cowedges and strong restricted cowedges
requires additional categorical structure (groupoid enrichment, fibered
categories) to formalize properly.

**Location**: `GebLean/Weighted.lean` section `WeightedCowedgeEmbedding`

### 20. Profunctor-Derived Weight Approach

This task explored an alternative approach suggested by the user: instead of
using `W.Elements` as the domain category, use `(profunctorOnTwistedArrow W).Elements`
(and dually `(profunctorOnCoTwistedArrow W).ElementsPre` for cowedges).

**Motivation**: The variance obstruction in Tasks 18-19 arose from trying to
match profunctor variance with category-of-elements morphism directions.
The hope was that using the profunctor-on-twisted-arrow construction would
give a domain category with the "correct" morphism directions.

**Analysis**:

For `Q : Cᵒᵖ ⥤ C ⥤ Type v`, the elements category `profunctorTwArrElements Q`
has objects `(tw, q)` where `tw : TwistedArrow C` and
`q : (Q.obj (op (twDom tw))).obj (twCod tw)`.

**Diagonal Elements**: At diagonal twisted arrows `twObjMk (𝟙 A)`:

- `(profunctorOnTwistedArrow C Q).obj (twObjMk (𝟙 A)) = diagApp Q A`
- This correctly captures the diagonal profunctor elements

**Morphisms Between Diagonals**: A morphism `m : twObjMk (𝟙 A) ⟶ twObjMk (𝟙 B)`
requires:

- `twDomArr m : B ⟶ A` (backwards direction)
- `twCodArr m : A ⟶ B` (forwards direction)
- Coherence: `twDomArr m ≫ 𝟙 A ≫ twCodArr m = 𝟙 B`

The coherence condition simplifies to `twDomArr m ≫ twCodArr m = 𝟙 B`,
forcing `twDomArr m` and `twCodArr m` to form a retraction/section pair.

For an isomorphism `i : A ≅ B`, we can define `diagTwArrMorphismOfIso i` with
`twDomArr = i.inv` and `twCodArr = i.hom`.

**Finding**: The variance obstruction persists even with profunctor-derived weights.
Morphisms between diagonal twisted arrows require isomorphisms in C, not
arbitrary morphisms.

**Conclusion**: The profunctor-derived weight approach does not circumvent the
variance obstruction. Weighted wedges/cowedges over general profunctors cannot
be expressed as ordinary wedges/cowedges over an induced presheaf/copresheaf
on the category of elements, except when restricted to groupoids.

**Status**: Completed (negative result)

**Location**: `GebLean/Weighted.lean` section `ProfunctorDerivedWeight`

**Implementation**:

- `profunctorTwArrElements Q`: Category of elements of profunctor on twisted arrows
- `profunctorCoTwArrElements Q`: Dual for co-twisted arrows
- `profunctorOnTwistedArrow_diagElem`: Diagonal elements equal `diagApp Q A`
- `profunctorOnCoTwistedArrow_diagElem`: Dual for co-twisted arrows
- `diagTwArrMorphismOfIso`: Morphism between diagonals requires isomorphism
- Documentation of variance analysis and paranaturality relationship

## References

### Code References

- `GebLean/Weighted.lean`: Weighted limits and restricted cowedges
  - Weighted cones/cocones: `WeightedCone` (~line 580),
    `WeightedCocone` (~line 613)
  - Weighted wedges/cowedges: `WeightedWedge` (~line 648),
    `WeightedCowedge` (~line 661)
  - Slice profunctor: `sliceProfunctor` (~line 689),
    `sliceProfunctorFunctor` (~line 722)
  - Restricted cowedges: `RestrictedCowedge` (~line 840),
    `RestrictedCowedgeCat` (~line 905)
  - Strong restricted cowedges: `StrongRestrictedCowedge` (~line 966),
    `StrongRestrictedCowedgeCat` (~line 1032)
  - Inclusion functor: `inclusion` (~line 1177),
    `inclusion_fullyFaithful` (~line 1189)
  - Wedge/cone equivalences: `coneToWedge` (~line 247), `wedgeToCone` (~line 328)
  - Cone/weighted-cone equivalence: `unitWeight` (~line 690),
    `coneToWeightedCone` (~line 702), `weightedConeToCone` (~line 722)
  - Cocone/weighted-cocone equivalence: `coconeToWeightedCocone` (~line 762),
    `weightedCoconeToCocone` (~line 782)

- `GebLean/Utilities/TwistedArrow.lean`: Twisted arrow infrastructure
  - `twistedArrowForget` functor
  - `coTwistedArrowForget` functor
  - `CoTwistedArrow` definition

- `GebLean/Utilities/TwArrPresheaf.lean`: Pre-composition functors
  - `profunctorOnTwistedArrow` (~line 1590)
  - `profunctorOnCoTwistedArrow` (~line 1623)

- `GebLean/Paranatural.lean`: Paranaturality definitions
  - `ParanatSig` structure (~line 241)
  - `IsParanatural` predicate (~line 248)
  - `IsDinatural` predicate (~line 730)
  - `paranatural_implies_dinatural` theorem (~line 772)

### Documentation References

- `docs/restricted-coends.md`: Vene's restricted coend theory
- `docs/mathlib-limits-colimits-guide.md`: Mathlib limit infrastructure

### External References

- Vene's thesis (2000): Original restricted coend definition
- Riehl's weighted limits paper: General theory
- nLab: weighted colimit article
