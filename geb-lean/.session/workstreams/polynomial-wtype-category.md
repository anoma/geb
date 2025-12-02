# Workstream: W-Type Category and Equivalence with Grothendieck Approach

## Status

Completed (Phase 1-3). Phase 4 is optional extension.

## Context

This workstream develops a category of polynomial functors expressed as W-type
diagrams, with natural transformations as morphisms, and establishes an
equivalence with the Grothendieck-based `PolyFunctorBetweenCat`.

The `Polynomial.lean` module currently has two representations of polynomial
functors `Over X -> Over Y`:

1. **Grothendieck-based**: `PolyFunctorBetweenCat X Y = FamilyCat (PolyFunctorCat X) Y`
   - Objects: Y-indexed families of polynomial functors `Over X -> Type`
   - Each `P(y)` is `(I_y, F_y)` with `I_y : Type` and `F_y : I_y -> Over X`
   - Morphisms: families of `CoprodCovarRepCat` morphisms at each y

2. **W-type based**: `WTypeDiagram X Y`
   - Objects: diagrams `X <- E -> B -> Y` with `p : E -> B`, `s : E -> X`, `t : B -> Y`
   - B is the base type (all positions), partitioned by t into Y-fibers
   - Currently has identity, composition, and evaluation, but NO morphism structure

The goal is to add morphisms to the W-type representation and prove the two
categories are equivalent.

## Reference Materials

Two Idris 2 files in `.claude/docs/` provide reference implementations:

- **`.claude/docs/IdrisCategories.idr`**: Contains `WTypeFunc` and `WTypeNT`
  definitions using explicit pullbacks and commutative diagrams (lines 5344-5405)
- **`.claude/docs/SlicePolyCat.idr`**: Contains `SPFData` (Grothendieck-style)
  and translation functions `SPFDasWTF`/`WTFasSPFD` between the formulations
  (lines 1959-2018), plus `SPFpoCellToWType*` functions showing how to convert
  between SPF morphisms and W-type morphisms (lines 2934-2998)

These are written in Idris 2 but the categorical structures transfer to Lean 4.

## Design

### W-Type Diagram Morphisms (Category-Theoretic Style)

Rather than using dependent types directly, we use the **category-theoretic
formulation with commutative diagrams** as shown in the Idris `WTypeNT` record.
This approach is more explicit about the categorical structure and more firmly
establishes correspondence with known theory (see ncatlab's "2-category of
polynomial functors").

A morphism `f : W_P -> W_Q` of W-type diagrams consists of:

```lean
-- First, define the pullback type explicitly
-- This is the pullback of Q.p along onPos:
--   Pullback --pbProj1--> Q.E
--      |                   |
--   pbProj2              Q.p
--      |                   |
--      v                   v
--    P.B ----onPos----> Q.B
def WTypePullback (P Q : WTypeDiagram X Y) (onPos : P.B -> Q.B) : Type u :=
  { pair : Q.E × P.B // Q.p pair.1 = onPos pair.2 }

def WTypePullback.proj1 (pb : WTypePullback P Q onPos) : Q.E := pb.val.1
def WTypePullback.proj2 (pb : WTypePullback P Q onPos) : P.B := pb.val.2

-- The morphism structure with explicit commutative diagrams
structure WTypeDiagramHom (P Q : WTypeDiagram X Y) where
  -- Map on positions (base)
  onPos : P.B -> Q.B

  -- Map on directions: takes a pullback element to a direction in P
  onDir : WTypePullback P Q onPos -> P.E

  -- Commutativity 1: position map preserves target (triangle commutes)
  --        P.B --onPos--> Q.B
  --         \            /
  --      P.t \          / Q.t
  --           \        /
  --            v      v
  --               Y
  commPos : forall b, Q.t (onPos b) = P.t b

  -- Commutativity 2: direction map respects the projection p
  -- P.p . onDir = proj2 (pullback second projection)
  commDir : forall pb, P.p (onDir pb) = pb.val.2

  -- Commutativity 3: direction map preserves source/assignment
  --      Pullback --proj1--> Q.E
  --         |                 |
  --      onDir             Q.s
  --         |                 |
  --         v                 v
  --       P.E ----P.s------> X
  commAssign : forall pb, P.s (onDir pb) = Q.s pb.val.1
```

This formulation differs from a naive dependent-types approach:

1. **Explicit pullback**: The domain of `onDir` is the categorical pullback,
   not a dependent fiber type. This makes the universal property explicit.

2. **Three commutative diagrams**: Each commutativity condition corresponds
   to a commutative square or triangle in the category of types.

3. **Matches ncatlab**: This structure matches the "2-category of polynomial
   functors" described at ncatlab, making our proofs directly comparable to
   established theory.

The fiber map going through the pullback (from Q-directions to P-directions)
matches the contravariant structure of `CoprodCovarRepCat`.

### Category Structure

- **Identity**: `id.onBase = id`, `id.onFiber b = id`
- **Composition**: For `f : P -> Q` and `g : Q -> R`:
  - `(g . f).onBase = g.onBase . f.onBase`
  - `(g . f).onFiber b = f.onFiber b . g.onFiber (f.onBase b)`
    (fiber maps compose in reverse order due to contravariance)

### Equivalence Functors

**F : WTypeDiagramCat -> PolyFunctorBetweenCat**

On objects: Given `W : WTypeDiagram X Y`, produce `P : PolyFunctorBetweenCat X Y`:
- For each `y : Y`, `P(y)` has index type `{b : W.B // W.t b = y}`
- Family at `b` is `W.fiberOver b.val`

On morphisms: Given `f : W_P -> W_Q`:
- Reindexing at y: `<b_P, h> |-> <f.onBase b_P, f.target_comm ...>`
- Fiber morphism: `Over.homMk (f.onFiber b_P) (source_comm proof)`

**G : PolyFunctorBetweenCat -> WTypeDiagramCat**

On objects: Given `P : PolyFunctorBetweenCat X Y`, produce `W : WTypeDiagram X Y`:
- `W.B = Sigma y, ccrIndex (P y)` (sigma over all positions)
- `W.E = Sigma (y : Y) (i : ccrIndex (P y)), (ccrFamily (P y) i).left`
- `W.p`, `W.s`, `W.t` defined by projections and structure maps

On morphisms: Given `f : P -> Q` (family of morphisms):
- `onBase <y, i> = <y, ccrReindex (f y) i>`
- `onFiber` uses `ccrFiberMor (f y) i`

### Equivalence Proof Sketch

**Unit (G . F ~ id on WTypeDiagramCat)**:
- `G(F(W)).B = Sigma y, {b : W.B // W.t b = y}` which is equivalent to `W.B`
- The isomorphism is `<y, <b, h>> <-> b` (with `h` reconstructible from `W.t b`)
- Similar equivalences for E, with compatible structure maps

**Counit (F . G ~ id on PolyFunctorBetweenCat)**:
- `F(G(P))(y)` has index `{<y', i> : Sigma y, ccrIndex (P y) // y' = y}`
- This is equivalent to `ccrIndex (P y)` via `<y, i, rfl> <-> i`
- Families correspond directly

## Tasks

### Phase 1: W-Type Diagram Morphisms (COMPLETED)
- [x] Define `WTypePullback` type (categorical pullback of Q.p along onPos)
- [x] Define `WTypeDiagramHom` structure with three commutativity conditions
- [x] Define `WTypeDiagramHom.id`
- [x] Define `WTypeDiagramHom.comp`
- [x] Prove identity laws (`id_comp`, `comp_id`)
- [x] Prove associativity (`comp_assoc`)
- [x] Define `WTypeDiagramCategory` instance
- [x] Define `WTypeDiagramCat X Y` as a `Cat`

### Phase 2: Functors (COMPLETED)
- [x] Define `wTypeToPolyBetweenObj : WTypeDiagram X Y -> PolyFunctorBetweenCat X Y`
- [x] Define `wTypeToPolyBetweenMap` on morphisms
- [x] Prove `wTypeToPolyBetween` preserves id and composition
- [x] Define `polyBetweenToWTypeObj : PolyFunctorBetweenCat X Y -> WTypeDiagram X Y`
- [x] Define `polyBetweenToWTypeMap` on morphisms
- [x] Prove `polyBetweenToWType` preserves id and composition

### Phase 3: Equivalence (COMPLETED)
- [x] Define unit component isomorphism for each W-type diagram
  - `unitHom : G(F(W)) -> W` and `unitInv : W -> G(F(W))`
  - `unitInv_unitHom` and `unitHom_unitInv` proved (isomorphism conditions)
- [x] Prove unit naturality (`unitInv_naturality`)
- [x] Define counit component isomorphism for each PolyFunctorBetween object
  - `counitHom : F(G(P)) -> P` and `counitInv : P -> F(G(P))`
  - `counitInv_counitHom` and `counitHom_counitInv` proved (isomorphism conditions)
- [x] Prove counit naturality (`counitHom_naturality`)
- [x] Prove triangle identities (`functor_unitIso_comp`)
- [x] Package as `wTypePolyBetweenEquiv : WTypeDiagramCat X Y ≌ PolyFunctorBetweenCat X Y`

### Phase 4: Natural Transformation Correspondence (optional extension)
- [ ] Define induced natural transformation from WTypeDiagramHom to NatTrans on eval
- [ ] Prove this correspondence is functorial
- [ ] Show the correspondence is an isomorphism of hom-sets

## Notes

### Contravariance Pattern

The fiber maps go from target to source (`Q.fiber -> P.fiber`) because:
- `CoprodCovarRepCat` uses the Grothendieck construction on `familyFunctor . opFunctor'`
- This makes fiber morphisms contravariant (like presheaf morphisms)
- Matches the polynomial functor semantics: to evaluate P at input A, we compose
  A's structure with the "arity" map that goes backwards from Q to P

### Universe Levels

The existing code uses `universe u` throughout. The equivalence should work at
the same universe level. Care needed with sigma types and their universe
placement.

### Existing Infrastructure to Reuse

- `WTypeDiagram.fiber` and `WTypeDiagram.fiberOver` for fiber access
- `ccrIndex`, `ccrFamily`, `ccrReindex`, `ccrFiberMor` for CoprodCovarRepCat
- `Over.homMk` and `Over.OverMorphism.ext` for morphisms in Over categories
- `polyBetweenEvalFamily` and existing evaluation infrastructure

### Potential Challenges

1. **Dependent type hell**: The sigma types and fiber proofs may require careful
   handling of heterogeneous equality and transport.

2. **Universe constraints**: Ensuring all definitions stay at consistent universe
   levels while working with sigma types.

3. **Definitional vs propositional equality**: The equivalence isomorphisms
   involve rearranging sigma types, which may not be definitionally equal.
   May need to use `Equiv` and transport rather than direct equality.

## References

- ncatlab: polynomial functor (https://ncatlab.org/nlab/show/polynomial+functor)
- Gambino-Kock: Polynomial functors and polynomial monads
- Current codebase: `GebLean/Polynomial.lean`, `GebLean/Utilities/Families.lean`
