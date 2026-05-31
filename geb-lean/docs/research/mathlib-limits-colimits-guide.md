# Mathlib Limits, Colimits, Ends, and Coends Reference

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Module Organization](#module-organization)
- [Cones and Cocones](#cones-and-cocones)
  - [Cones Import](#cones-import)
  - [Cone Structure](#cone-structure)
- [Limits and Colimits](#limits-and-colimits)
  - [Limits Import](#limits-import)
  - [IsLimit and IsColimit Structures](#islimit-and-iscolimit-structures)
  - [HasLimit and HasColimit Classes](#haslimit-and-hascolimit-classes)
  - [Limit Operations](#limit-operations)
- [Terminal and Initial Objects](#terminal-and-initial-objects)
  - [Terminal Import](#terminal-import)
  - [Terminal and Initial Types](#terminal-and-initial-types)
  - [Notation and Terminal Operations](#notation-and-terminal-operations)
  - [IsTerminal and IsInitial Predicates](#isterminal-and-isinitial-predicates)
- [Products and Coproducts](#products-and-coproducts)
  - [Products Import](#products-import)
  - [Binary Product Operations](#binary-product-operations)
  - [Indexed Product Notation](#indexed-product-notation)
- [Pullbacks and Pushouts](#pullbacks-and-pushouts)
  - [Pullbacks Import](#pullbacks-import)
  - [Pullback Types](#pullback-types)
  - [Pullback Operations](#pullback-operations)
  - [Pullback-Product Relationship](#pullback-product-relationship)
- [Equalizers and Coequalizers](#equalizers-and-coequalizers)
  - [Equalizers Import](#equalizers-import)
  - [Equalizer Types](#equalizer-types)
- [Ends and Coends](#ends-and-coends)
  - [Ends Import](#ends-import)
  - [End and Coend Types](#end-and-coend-types)
  - [Wedges and Cowedges](#wedges-and-cowedges)
  - [End and Coend Operations](#end-and-coend-operations)
  - [End Shape Types](#end-shape-types)
- [Kan Extensions](#kan-extensions)
  - [Kan Extensions Import](#kan-extensions-import)
  - [Kan Extension Types](#kan-extension-types)
  - [IsLeftKanExtension and IsRightKanExtension Classes](#isleftkanextension-and-isrightkanextension-classes)
  - [Pointwise Kan Extensions](#pointwise-kan-extensions)
- [Preservation of Limits](#preservation-of-limits)
  - [Preservation Import](#preservation-import)
  - [Preservation Classes](#preservation-classes)
  - [Reflection and Creation Classes](#reflection-and-creation-classes)
- [Weighted Limits and Colimits](#weighted-limits-and-colimits)
- [Usage in This Project](#usage-in-this-project)
  - [Project Imports](#project-imports)
  - [Related Local Modules](#related-local-modules)
  - [Diagonal Elements as Ends](#diagonal-elements-as-ends)
- [References](#references)
  - [Mathlib Documentation Links](#mathlib-documentation-links)
  - [External Reference Links](#external-reference-links)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

This document provides a reference to mathlib's category theory infrastructure for
limits, colimits, ends, coends, and related constructions in Lean 4.

## Module Organization

The limit/colimit infrastructure is organized under `Mathlib.CategoryTheory.Limits`:

```text
Mathlib.CategoryTheory.Limits
├── Cones.lean           -- Cone and Cocone structures
├── IsLimit.lean         -- IsLimit, IsColimit, HasLimit, HasColimit
├── Shapes/              -- Specific limit shapes
│   ├── Terminal.lean    -- Initial and terminal objects
│   ├── Products.lean    -- Binary and indexed products
│   ├── Pullback/        -- Pullbacks and pushouts
│   ├── Equalizers.lean  -- Equalizers and coequalizers
│   └── End.lean         -- Ends and coends
├── Preserves/           -- Limit preservation
├── Constructions/       -- Building limits from other limits
└── Types.lean           -- Limits in the category of types
```

## Cones and Cocones

### Cones Import

```lean
import Mathlib.CategoryTheory.Limits.Cones
```

### Cone Structure

A **cone** over a functor `F : J ⥤ C` consists of:

- A **cone point** `pt : C`
- A natural transformation `π : (const J).obj pt ⟶ F`

The type is `Cone F` with fields:

- `pt : C` -- the cone point
- `π : (const J).obj pt ⟶ F` -- the projection natural transformation

A **cocone** is the dual, with `ι : F ⟶ (const J).obj pt`.

**Cone morphisms** `ConeMorphism s t` consist of a morphism `hom : s.pt ⟶ t.pt`
commuting with the projections.

## Limits and Colimits

### Limits Import

```lean
import Mathlib.CategoryTheory.Limits.IsLimit
```

### IsLimit and IsColimit Structures

```lean
structure IsLimit {J : Type u₁} [Category J] {C : Type u₃} [Category C]
    {F : Functor J C} (t : Cone F) : Type where
  lift : ∀ (s : Cone F), s.pt ⟶ t.pt
  fac : ∀ (s : Cone F) (j : J), lift s ≫ t.π.app j = s.π.app j
  uniq : ∀ (s : Cone F) (m : s.pt ⟶ t.pt),
      (∀ j, m ≫ t.π.app j = s.π.app j) → m = lift s
```

A cone `t` is a **limit cone** when every other cone admits a unique morphism
to `t`. `IsColimit` is the dual for cocones.

### HasLimit and HasColimit Classes

```lean
class HasLimit (F : J ⥤ C) : Prop where
  exists_limit : Nonempty (LimitCone F)

class HasColimit (F : J ⥤ C) : Prop where
  exists_colimit : Nonempty (ColimitCocone F)
```

Use `limit F` and `colimit F` to access the limit/colimit objects when these
instances exist.

### Limit Operations

| Operation | Type | Description |
| --------- | ---- | ----------- |
| `limit F` | `C` | The limit object |
| `limit.π F j` | `limit F ⟶ F.obj j` | Projection to component |
| `limit.lift F c` | `c.pt ⟶ limit F` | Universal morphism from a cone |
| `colimit F` | `C` | The colimit object |
| `colimit.ι F j` | `F.obj j ⟶ colimit F` | Inclusion from component |
| `colimit.desc F c` | `colimit F ⟶ c.pt` | Universal morphism to a cocone |

## Terminal and Initial Objects

### Terminal Import

```lean
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
```

### Terminal and Initial Types

```lean
abbrev HasTerminal (C : Type u₁) [Category C] : Prop :=
  HasLimitsOfShape (Discrete PEmpty) C

abbrev HasInitial (C : Type u₁) [Category C] : Prop :=
  HasColimitsOfShape (Discrete PEmpty) C
```

### Notation and Terminal Operations

| Notation | Description |
| -------- | ----------- |
| `⊤_ C` | The terminal object |
| `⊥_ C` | The initial object |
| `terminal.from X` | The unique morphism `X ⟶ ⊤_ C` |
| `initial.to X` | The unique morphism `⊥_ C ⟶ X` |

### IsTerminal and IsInitial Predicates

```lean
def IsTerminal (T : C) : Prop := ∀ X, Unique (X ⟶ T)
def IsInitial (I : C) : Prop := ∀ X, Unique (I ⟶ X)
```

Construct instances with `hasTerminal_of_unique` or `hasInitial_of_unique`.

## Products and Coproducts

### Products Import

```lean
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
```

### Binary Product Operations

| Notation | Description |
| -------- | ----------- |
| `X ⨯ Y` | Binary product |
| `prod.fst` | First projection `X ⨯ Y ⟶ X` |
| `prod.snd` | Second projection `X ⨯ Y ⟶ Y` |
| `prod.lift f g` | Universal morphism to product |

### Indexed Product Notation

```lean
∏ᶜ F  -- indexed product of F : J → C
```

## Pullbacks and Pushouts

### Pullbacks Import

```lean
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
```

### Pullback Types

```lean
class HasPullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : Prop

def pullback {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) [HasPullback f g] : C
```

### Pullback Operations

| Operation | Type | Description |
| --------- | ---- | ----------- |
| `pullback f g` | `C` | The pullback object |
| `pullback.fst f g` | `pullback f g ⟶ X` | First projection |
| `pullback.snd f g` | `pullback f g ⟶ Y` | Second projection |
| `pullback.condition` | proof | `fst ≫ f = snd ≫ g` |
| `pullback.lift h k w` | `W ⟶ pullback f g` | Universal morphism |

### Pullback-Product Relationship

Products are pullbacks over the terminal object:

```lean
X ⨯ Y ≅ pullback (terminal.from X) (terminal.from Y)
```

## Equalizers and Coequalizers

### Equalizers Import

```lean
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
```

### Equalizer Types

```lean
class HasEqualizer {X Y : C} (f g : X ⟶ Y) : Prop

def equalizer {X Y : C} (f g : X ⟶ Y) [HasEqualizer f g] : C
def equalizer.ι (f g : X ⟶ Y) [HasEqualizer f g] : equalizer f g ⟶ X
```

The equalizer satisfies `equalizer.ι f g ≫ f = equalizer.ι f g ≫ g`.

## Ends and Coends

### Ends Import

```lean
import Mathlib.CategoryTheory.Limits.Shapes.End
```

### End and Coend Types

For a bifunctor `F : Jᵒᵖ ⥤ J ⥤ C`:

- **End**: `end_ F` is defined as a multiequalizer of `(F.obj (op j)).obj j`
- **Coend**: `coend F` is defined as a multicoequalizer

### Wedges and Cowedges

**Wedge**: The cone type for ends, consisting of:

- A point object in `C`
- Morphisms `π j : pt ⟶ (F.obj (op j)).obj j` for each `j`
- Compatibility: for `f : j ⟶ j'`, the diagram commutes

**Cowedge**: The cocone type for coends, with:

- A point object in `C`
- Morphisms `ι j : (F.obj (op j)).obj j ⟶ pt`
- Dual compatibility conditions

### End and Coend Operations

| Operation | Description |
| --------- | ----------- |
| `end_.π F j` | Projection `end_ F ⟶ (F.obj (op j)).obj j` |
| `end_.lift F w` | Universal morphism from a wedge |
| `coend.ι F j` | Inclusion `(F.obj (op j)).obj j ⟶ coend F` |
| `coend.desc F w` | Universal morphism to a cowedge |

### End Shape Types

The underlying diagram shapes:

- `multicospanShapeEnd J` -- for ends
- `multispanShapeCoend J` -- for coends

## Kan Extensions

### Kan Extensions Import

```lean
import Mathlib.CategoryTheory.Functor.KanExtension.Basic
```

### Kan Extension Types

For `L : C ⥤ D` and `F : C ⥤ H`:

```lean
abbrev LeftExtension (L : C ⥤ D) (F : C ⥤ H) :=
  CostructuredArrow (whiskeringLeft C D H).obj F

abbrev RightExtension (L : C ⥤ D) (F : C ⥤ H) :=
  StructuredArrow F (whiskeringLeft C D H).obj
```

### IsLeftKanExtension and IsRightKanExtension Classes

```lean
class IsLeftKanExtension (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H}
    (α : F ⟶ L ⋙ F') : Prop

class IsRightKanExtension (F' : D ⥤ H) {L : C ⥤ D} {F : C ⥤ H}
    (α : L ⋙ F' ⟶ F) : Prop
```

These encode that the extension is initial/terminal in the respective category.

### Pointwise Kan Extensions

```lean
class HasPointwiseLeftKanExtension (L : C ⥤ D) (F : C ⥤ H) : Prop
```

Pointwise Kan extensions are computed as (co)limits at each object.

## Preservation of Limits

### Preservation Import

```lean
import Mathlib.CategoryTheory.Limits.Preserves.Basic
```

### Preservation Classes

```lean
class PreservesLimit (K : J ⥤ C) (F : C ⥤ D) : Prop
class PreservesColimit (K : J ⥤ C) (F : C ⥤ D) : Prop
class PreservesLimitsOfShape (J : Type) [Category J] (F : C ⥤ D) : Prop
class PreservesColimitsOfShape (J : Type) [Category J] (F : C ⥤ D) : Prop
class PreservesLimits (F : C ⥤ D) : Prop
class PreservesColimits (F : C ⥤ D) : Prop
```

### Reflection and Creation Classes

```lean
class ReflectsLimit (K : J ⥤ C) (F : C ⥤ D) : Prop
class CreatesLimit (K : J ⥤ C) (F : C ⥤ D) : Prop
```

- **Reflects**: If `F` maps a cone to a limit cone, then it was already a limit
- **Creates**: `F` both preserves and reflects, and lifts limit cones

## Weighted Limits and Colimits

Mathlib does not currently have explicit weighted limit/colimit definitions
as a general abstraction. However, the concept appears implicitly:

- **Ends and coends** are weighted limits/colimits with the hom-functor as weight
- **Kan extensions** are weighted colimits when computed pointwise
- The presheaf category `Cᵒᵖ ⥤ Type` has colimits computed as weighted colimits

For explicit weighted colimit theory, see:

- [Weighted Limits and Colimits (Riehl)](https://math.jhu.edu/~eriehl/weighted.pdf)
- [nLab: weighted colimit](https://ncatlab.org/nlab/show/weighted+colimit)

## Usage in This Project

### Project Imports

The geb-lean project currently uses:

```lean
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import Mathlib.CategoryTheory.Limits.Shapes.Products
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Over
```

### Related Local Modules

- `GebLean/Paranatural.lean` -- Defines `DiagElem` which is related to ends
- `GebLean/ParanatAlg.lean` -- Uses terminal objects for algebra structures
- `GebLean/Polynomial.lean` -- Uses products for polynomial functor evaluation
- `GebLean/PolyPresentation.lean` -- Uses equalizers for presentations

### Diagonal Elements as Ends

The `DiagElem F` construction in `Paranatural.lean` for an endoprofunctor
`F : Cᵒᵖ ⥤ C ⥤ Type` is related to the end construction: it captures the
"diagonal" elements `F(I, I)` with compatibility conditions that correspond
to wedge conditions.

## References

### Mathlib Documentation Links

- [Limits.IsLimit](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/IsLimit.html)
- [Shapes.Terminal](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Terminal.html)
- [Shapes.End](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/End.html)
- [KanExtension.Basic](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/KanExtension/Basic.html)
- [Pullback.HasPullback](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Pullback/HasPullback.html)

### External Reference Links

- [nLab: weighted colimit](https://ncatlab.org/nlab/show/weighted+colimit)
- [nLab: end](https://ncatlab.org/nlab/show/end)
- [Weighted Limits and Colimits (Riehl)](https://math.jhu.edu/~eriehl/weighted.pdf)
