# Workstream: Polynomial Functor Universal Morphisms

## Status

Active

## Context

Constructing universal morphisms for `PolyBetween` (the vertical category
`PolyFunctorBetweenCat X Y`), which is the category of polynomial functors
`Over X -> Over Y`. This extends the existing polynomial functor
infrastructure in `Polynomial.lean` and `PolyAlg.lean`.

## Goal

For each universal construction, define:

1. The object
2. The universal morphisms (introduction and elimination rules)
3. A proof that the object+morphisms satisfy the universal property
   (using mathlib's `IsLimit`, `IsColimit`, `IsLeftKanExtension`, etc.)

## Constructions to Implement

### Limits (via products + equalizers)

1. **Arbitrary-Type-indexed products**
   - Position: product of all positions (Pi type over index)
   - Direction: coproduct (Sum) of all directions at each position
   - Projection morphisms
   - Universal pairing morphism
   - `IsLimit` proof (via `Fan.IsLimit.mk`)

2. **Binary equalizers**
   - Given `f, g : P => Q`, the equalizer `E` has:
     - Positions: equalizer on positions `{i : pos(P) | f_pos(i) = g_pos(i)}`
     - Directions: coequalizer on directions `Quot` of
       `dir(Q)(f_pos(i))` by identifying `f_dir` and `g_dir` images
   - Inclusion morphism `e : E -> P`
   - `IsLimit` proof (via `Fork.IsLimit.mk`)

3. **HasLimits instance** (derived from products + equalizers)

### Colimits (via coproducts + coequalizers)

1. **Arbitrary-Type-indexed coproducts**
   - Position: coproduct of all positions (Sigma type over index)
   - Direction: projection to the chosen component's directions
   - Injection morphisms
   - Universal copairing morphism
   - `IsColimit` proof (via `Cofan.IsColimit.mk`)

2. **Binary coequalizers**
   - Given `s, t : P => Q`, the coequalizer `Q'` has:
     - Positions: coequalizer on positions, i.e., connected components
       of the graph where vertices are `pos(Q)`, edges are `pos(P)`,
       with source = `s_pos` and target = `t_pos`
     - Directions: at each connected component `c`, a limit of a diagram
       over the category of elements of that component
   - Projection morphism `g : Q -> Q'`
   - `IsColimit` proof (via `Cofork.IsColimit.mk`)

3. **HasColimits instance** (derived from coproducts + coequalizers)

### Exponentials (hom-objects)

1. **Internal hom / exponential objects**
   - `[P, Q]` where `P, Q : PolyFunctorBetweenCat X Y`
   - Evaluation morphism `ev : [P, Q] x P -> Q`
   - Curry/uncurry operations
   - `Closed` / `CartesianClosed` instance

### Kan Extensions

1. **Left Kan extension**
   - Given `q : PolyBetween X Z` and `p : PolyBetween X Y`,
     the left Kan extension `Lan_q(p) : PolyBetween Z Y` has:
     - Positions: same as positions of `p`
     - Directions: `q` applied to the direction-sets of `p`
   - Unit/counit of the adjunction `Lan_q -| q^*`
   - `IsLeftKanExtension` proof

## Implementation Plan

Work in `GebLean/PolyUMorph.lean`, imported from `GebLean.lean`.

Order of implementation:

1. Products (most straightforward)
2. Coproducts (dual of products)
3. Equalizers
4. Coequalizers (most involved construction)
5. HasLimits / HasColimits instances
6. Exponentials
7. Left Kan extensions

## Style Convention: Named Components

All universal constructions should factor their definitions into
named components:

- **For objects**: separate definitions for positions and
  directions (family), then the object as `ccrObjMk` of them.
- **For morphisms**: separate definitions for on-positions
  (reindex) and on-directions (fiber) components, then the
  morphism as `ccrHomMk` of them.

This makes type signatures explicit, enables targeted lemmas
about individual components, and produces clearer proof goals.

Example (products):

- `polyBetweenProdPos` — position type
- `polyBetweenProdDir` — family/direction type
- `polyBetweenProd` — the product object
- `polyBetweenProjReindex` — projection on-positions
- `polyBetweenProjFiber` — projection on-directions
- `polyBetweenProj` — the projection morphism
- `polyBetweenProdLiftReindex` — lift on-positions
- `polyBetweenProdLiftFiber` — lift on-directions
- `polyBetweenProdLift` — the lift morphism

## Reference Materials

- **Idris-2 file**: `.claude/docs/SlicePolyUMorph.idr` contains formulas
  for products, coproducts, hom-objects, and left Kan extensions
- **Polynomial book**: `.claude/docs/poly-book-2024-july-17-limits-colimits-section-5-4.pdf`
  describes equalizers and coequalizers in `Poly` (for `Set`, needs
  adaptation to `Over` categories)
- **Existing codebase patterns**: `PolyAlg.lean` shows how to work with
  `PolyEndo` and `polyEndoFunctor`; `FreeCoequalizerCompletion.lean` and
  `ParanaturalTopos.lean` show how to prove `IsLimit`/`IsColimit`
- **Mathlib**: `Cofork.IsColimit.mk`, `BinaryFan.IsLimit.mk`,
  `Fan.IsLimit.mk`, `Cofan.IsColimit.mk` for universal property proofs

## Codebase Notes

- `PolyFunctorBetweenCat X Y` = `FamilyCat (CoprodCovarRepCat (Over X)) Y`
  = `Y`-indexed families of polynomial functors `Over X -> Type`
- Each polynomial at `y : Y` is `(I_y, F_y)` where `I_y : Type` and
  `F_y : I_y -> Over X`
- Morphisms: at each `y`, a reindexing + backward fiber morphisms
  (contravariant Grothendieck construction)
- `polyBetweenEvalFunctor` converts polynomial data to actual functors
  `Over X ⥤ Over Y`
- The `CoprodData` pattern separates computation from proof

## Research Notes

### Product formula (from Idris)

For a family `sf : b -> SPFData dom cod`:

- Positions: `∀ y, Π (i : b), pos(sf(i))(y)` (dependent product)
- Directions: `∀ y, pos, dir, Σ (i : b), dir(sf(i))(y)(pos(i))(dir)`
  (dependent sum / tagged union)

### Coproduct formula (from Idris)

For a family `sf : b -> SPFData dom cod`:

- Positions: `∀ y, Σ (i : b), pos(sf(i))(y)` (dependent sum)
- Directions: at `(i, p)`, `dir(sf(i))(y)(p)(d)` (project to component)

### Equalizer formula (from book, Thm 5.33)

For `f, g : p => q` (two lenses):

- Positions: `{i : p(1) | f_1(i) = g_1(i)}` (equalizer on positions)
- Directions at `i`: coequalizer of `f^#_i, g^#_i : q[f_1(i)] => p[i]`

### Coequalizer formula (from book, Thm 5.43)

For `s, t : p => q` (two lenses):

- Positions: `C` = connected components of the graph with
  vertices `q(1)`, edges `p(1)`, source `s_1`, target `t_1`
- Directions at `c in C`: limit of a functor `F` from the category
  of elements `∫ G_c` to `Set^op`

### Left Kan extension formula (from Idris)

For `q : SPFData a c`, `p : SPFData a b`:

- `Lan_q(p)` has positions = positions of `p`
- Directions at `(b, p_b)` = `q` applied to `dir(p)(b)(p_b)`

### Exponential formula (from Idris)

The hom-object `[p, q]` is constructed in stages:

1. For representable `p`: `[rep(x), q] = q ∘ flip(x)`
2. For coproduct-of-representables `p`: product over positions of `p`
   of representable hom-objects
3. General case: reduce to the coproduct-of-representables case
   fiberwise

## Tasks

- [x] Create `PolyUMorph.lean` and add import to `GebLean.lean`
- [x] Implement arbitrary-indexed products with `IsLimit` proof
  - [x] Product object (Pos, Dir, Prod)
  - [x] Projection morphism (Reindex, Fiber, Proj)
  - [x] Lift morphism (Reindex, Fiber, Lift)
  - [x] Factorization proof (lift ≫ proj = m)
  - [x] Uniqueness proof
  - [x] `IsLimit` / `Fan` / `mkFanLimit` / `HasProducts` assembly
- [x] Implement arbitrary-indexed coproducts with `IsColimit` proof
- [x] Implement binary equalizers with `IsLimit` proof
- [x] Implement binary coequalizers with `IsColimit` proof
- [x] Derive `HasLimits` / `HasColimits` instances
- [x] Implement exponential objects with `Closed` instance
- [x] Implement left Kan extensions with adjunction proof
