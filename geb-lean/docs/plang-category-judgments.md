# PLang Category Judgments

This document describes the PLang formulation of category-judgment copresheaves
in `GebLean/PLang/CatJudgment.lean`.

## Overview

The PLang module provides a formulation of category-judgment copresheaves that:

1. Uses explicit and maximally flexible universe parameters throughout
2. Builds structures incrementally

## Structure

The table below shows the PLang definitions and their roles:

| PLang Definition | Description |
| ---------------- | ----------- |
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

The adjunction `L ⊣ Φ` establishes a reflective embedding:

- **Left adjoint L**: `CatJudgCopr.{u, v, w, x} ⥤ Cat.{v, u}`
  - Takes a copresheaf and produces its quotient category
- **Right adjoint Φ**: `Cat.{v, u} ⥤ CatJudgCopr.{u, v, w, x}`
  - Embeds a category into the copresheaf structure

### Universe Requirements

The adjunction must have fully independent universe levels:

- `Cat.{v, u}` with object universe `u` and morphism universe `v`
- `CatJudgCopr.{u, v, w, x}` with all four levels independent

The levels `u` and `v` in `CatJudgCopr` correspond exactly to those in
`Cat`. The levels `w` and `x` are additional degrees of freedom for the
identity and composition witness types.

This independence is necessary to embed categories at any universe level
into the copresheaf structure without constraints.

### Mathlib Requirement

All functors, natural transformations, and adjunctions must use standard
mathlib definitions:

- `CategoryTheory.Functor` for `L` and `Φ`
- `CategoryTheory.NatTrans` for unit and counit
- `CategoryTheory.Adjunction` for the reflective adjunction

Custom structures may be used internally for data representation, but the
final constructions must be in mathlib terms.

### Reflective Embedding Requirement

The adjunction must be proven to be a reflective embedding with mathlib
instances:

- `CategoryTheory.Functor.FullyFaithful Φ` - the right adjoint is fully
  faithful, meaning morphisms in `Cat` correspond bijectively to morphisms
  between their images in `CatJudgCopr`
- `CategoryTheory.Reflective Φ` - the adjunction is reflective, establishing
  that `Cat` is a reflective subcategory of the larger category `CatJudgCopr`

These instances are required to complete the workstream.

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

## Implementation Plan

### Phase 1: Equal-Universe Intermediate (Current)

The current implementation in `GebLean/PLang/CatJudgCoprAdjunction.lean`
works with `CatJudgCopr.{u+1, u+1, u+1, u+1}` (all levels equal) to
validate the construction. This uses `PLangQuotientData.{w}` which has
a single universe level for all components.

Remaining work:

- Fix `unit_morMap_natural` proof (nested sigma equality)
- Fix `unit_naturality_PLang` proof (idMap/compMap components)
- Complete mathlib `Adjunction.mkOfUnitCounit` construction

### Phase 2: Universe Generalization (Required)

The constraint source is `PLangQuotientData.{w}`:

```lean
structure PLangQuotientData.{w} where
  quiver : OverQuiver.{w, w}
  IdWitness : Type w
  CompWitness : Type w
```

Resolution:

1. Generalize to `PLangQuotientData.{u, v, w, x}` with independent levels
2. Redefine `toPLangQuotientData` for `C : Cat.{v, u}`
3. Update `LFunctorPLang` and `PhiFunctorPLang` signatures
4. Verify naturality proofs still hold
5. Construct final mathlib adjunction
6. Prove `Functor.FullyFaithful PhiFunctorPLang`
7. Construct `Reflective PhiFunctorPLang` instance

### Alternative: Direct Approach

If the `BundledOverCategoryData` approach proves too constrained, an
alternative is to construct the adjunction directly between `Cat.{v,u}`
and `CatJudgCopr.{u,v,w,x}` without the intermediate quotient data
structure. This would require:

- Defining L directly on `Obj.CatJudgCopr` objects
- Defining Φ directly on `Cat` objects
- Proving functoriality and naturality at the full type level

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
