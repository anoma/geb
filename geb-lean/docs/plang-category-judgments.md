# PLang Category Judgments

This document describes the PLang formulation of category-judgment copresheaves
in `GebLean/PLang/CatJudgment.lean`.

## Overview

The PLang module provides a formulation of category-judgment copresheaves that:

1. Specializes the target category to `Type` (for universe `u`)
2. Uses explicit universe parameters throughout
3. Builds structures incrementally via sigma types

## Structure

The table below shows the PLang definitions and their roles:

| PLang Definition | Description |
|------------------|-------------|
| `ObjCopr.{u}` | Type of objects |
| `ObjMorObj.{u,v}` | Objects and morphisms types |
| `ObjMorProj` | Projection function type |
| `ObjMorMor` | Domain and codomain functions |
| `ObjMorCopr` | Bundled quiver data |
| `ObjMorIdObj` | Quiver plus identity type |
| `IdProj` | Identity morphism projection |
| `ObjMorIdMor` | Quiver with identity function |
| `ObjMorIdObjMor` | Bundled identity data (sigma) |
| `ObjMorIdObjMorEndo` | Identity endomorphism condition |
| `ObjMorIdCopr` | Identity copresheaf (subtype) |
| `ObjMorCompObj` | Quiver plus composition type |
| `CompProj` | Composition projection |
| `ObjMorCompProj` | Triple of projections |
| `ObjMorCompMor` | Full composition data |
| `ObjMorCompObjMor` | Bundled composition data (sigma) |
| `ObjMorCompObjMorMatch` | Composability condition |
| `ObjMorCompObjMorCompDom` | Domain preservation |
| `ObjMorCompObjMorCompCod` | Codomain preservation |
| `ObjMorCompObjMorCond` | Conjunction of conditions |
| `ObjMorCompCopr` | Composition copresheaf (subtype) |
| `CatJudgObj` | Full object data |
| `CatJudgMor` | All functions |
| `CatJudgObjMor` | Bundled object-morphism (sigma) |
| `CatJudgObjMorCond` | Identity and composition laws |
| `CatJudgCopr` | Full copresheaf |

## Universe Levels

The PLang formulation uses explicit universe parameters:

```text
CatJudgCopr.{u, v, w, x} : Type (max u v w x + 1)
```

Where:

- `u` controls the objects type (`ObjCopr.{u} = Sort u`)
- `v` controls the morphisms type
- `w` controls the identity type
- `x` controls the composition type

## Incremental Construction

The PLang approach builds structures layer by layer:

```text
ObjCopr           -- just objects
  |
ObjMorObj         -- add morphisms type
  |
ObjMorCopr        -- add dom/cod functions
  |
ObjMorIdObjMor    -- add identity data
  |
ObjMorIdCopr      -- add identity condition
  |
ObjMorCompObjMor  -- add composition data
  |
ObjMorCompCopr    -- add composition conditions
  |
CatJudgCopr       -- combine identity and composition
```

Each layer is a sigma type extending the previous, allowing operations to
be defined at intermediate stages.

## Relationship to the Adjunction

The adjunction `L -| Phi` relates:

- `Cat.{v, u}`: Small categories with morphisms at level `v` and objects
  at level `u`
- Copresheaves valued in `Type u`

The PLang formulation, with its explicit universe parameters, provides a
path toward a more general adjunction:

```text
Cat.{v, u} <-> CatJudgCopr.{u, v, w, x}
```

## Planned Generalization

The eventual goal is to replace the target `Type` with an arbitrary
`CatJudgCopr`, making the definition recursive:

```text
CatJudgCoprRec.{u, v, w, x} (target : CatJudgCoprRec ...) : Type ...
```

This generalization would allow category-judgment copresheaves to be
valued in arbitrary category-judgment copresheaves rather than just
`Type`. Since `Type` itself embeds into `CatJudgCopr` via the discrete
category construction, this strictly generalizes the current formulation.

Properties of this generalization:

1. `CatJudgCopr` forms a topos (as a presheaf category)
2. Categories embed via the adjunction
3. The recursive definition provides internal hom objects
4. Category theory can be rebuilt as embedded in category-judgment theory

## Implementation Notes

The PLang definitions use:

- `Sort` instead of `Type` to include `Prop` at level 0
- Function composition for conditions
- Subtypes (`{x // P x}`) for constrained structures
- Sigma types for dependent bundling

The file is under the `GebLean.PLang.Obj` namespace, with a placeholder
`GebLean.PLang.Mor` namespace for morphisms between `CatJudgCopr` values.

## References

- `docs/categories-as-copresheaves.md`: Mathematical background
