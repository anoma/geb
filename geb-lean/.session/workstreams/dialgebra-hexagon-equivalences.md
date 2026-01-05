# Dialgebra and Hexagon Category Equivalences

## Status: Complete

## Overview

This workstream established equivalences between:

1. `DiagElem (DialgebraProf F G)` and the `Dialgebra F G` category
2. `HexagonCat` for functor-derived profunctors and `DiagElem (DialgebraProf F G)`
3. Composition giving `HexagonCat` equivalent to `Dialgebra F G`

## Completed Implementation

### In `GebLean/ParanatAlg.lean`

- `Dialgebra F G` - the dialgebra category for functors `F, G : C -> D`
- `Dialgebra.Hom` - morphisms satisfying the dialgebra condition
- `diagElemDialgEquiv : DiagElem (DialgebraProf F G) ≌ Dialgebra F G`

### In `GebLean/HexagonCat.lean`

- `HexagonCat` - named instance for `Category (HexagonObj P Q)`
- `hexagonDiagElemEquiv : HexagonObj P Q ≌ DiagElem (ProfDialgebraProf P Q)`
- `ProjProfF`, `ProjProfG` - projection profunctors for `F, G : C ⥤ Type v`
- `profDialgebraProjProf_eq` - equality of
  `ProfDialgebraProf (ProjProf C F) (ProjProf C G)` with `DialgebraProfType F G`
- `dialgebraProfType_eq_dialgebraProf` - equality of local definition with ParanatAlg's
- `hexagonProjProfDiagElemEquiv` - hexagon to diagonal element equivalence
- `hexagonProjProfDialgEquiv` - the final equivalence
  `HexagonObj (ProjProfF F) (ProjProfG G) ≌ DialgebraType F G`

### In `GebLean/Utilities/Profunctors.lean`

- `ProjProf D F : Dᵒᵖ × C ⥤ Type w` - projection profunctor ignoring
  contravariant argument
- `Prof.map₁`, `Prof.map₂` - partial profunctor maps
- Simp lemmas for `ProjProf_map₁` and `ProjProf_map₂`

## Design Decisions

### Projection Profunctor Approach

For the dialgebra equivalence, we used the "forgetful" projection profunctor approach:

```text
ProjProf D F : Dᵒᵖ × C ⥤ Type w
ProjProf D F (d, c) = F.obj c
```

This ignores the contravariant argument, making `Prof.map₁` trivial (identity).
The hexagon condition then simplifies directly to the dialgebra morphism condition.

The alternative "representable profunctor" approach `D(1,F)(d,c) = Hom(d, F.obj c)`
would have given coalgebra-like structures instead.

### Universe Parameters

For `HexagonObj P Q` with `P Q : Cᵒᵖ × C ⥤ Type v`, the functors must map to
`Type v` (the morphism universe of `C`). This led to defining `DialgebraProfType`
and `DialgebraType` as abbreviations specialized to `F G : C ⥤ Type v`.

## Equivalence Chain

```text
HexagonObj (ProjProfF F) (ProjProfG G)
    ↓  hexagonDiagElemEquiv
DiagElem (ProfDialgebraProf (ProjProf C F) (ProjProf C G))
    =  profDialgebraProjProf_eq
DiagElem (DialgebraProfType F G)
    =  dialgebraProfType_eq_dialgebraProf
DiagElem (DialgebraProf F G)
    ↓  diagElemDialgEquiv
Dialgebra F G
```
