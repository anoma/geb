# Workstream: Free Binary Coequalizer Completion

## Status

Completed

## Context

Implementation of the free binary coequalizer completion of a category as
described in section 3 of `docs/yoneda-coproduct-coequalizer-factorization.md`.
This construction freely adjoins coequalizers to a category by representing
objects as parallel pair diagrams.

## Mathematical Background

### Objects

An object in the free coequalizer completion of C consists of:

- Two objects `src` and `tgt` from C
- Two parallel morphisms `left, right : src ⟶ tgt`

This represents the formal coequalizer of `left` and `right`.

### Morphisms

A morphism from `(A, B, f, g)` to `(A', B', f', g')` consists of:

- `srcHom : A ⟶ A'` (morphism between source objects)
- `tgtHom : B ⟶ B'` (morphism between target objects)
- `left_comm : srcHom ≫ f' = f ≫ tgtHom` (left square commutes)
- `right_comm : srcHom ≫ g' = g ≫ tgtHom` (right square commutes)

The commutativity conditions ensure that the morphism is compatible with
the equivalence relations being imposed.

### Coequalizer Construction

For parallel morphisms `h, k : P ⟶ Q` in the completion where:

- `P = (A, B, f, g)`
- `Q = (A', B', f', g')`
- `h = (h_src, h_tgt)`, `k = (k_src, k_tgt)`

The coequalizer is computed pointwise (when C has coequalizers):

- `coeq(h, k).src = coeq(h_src, k_src)` in C
- `coeq(h, k).tgt = coeq(h_tgt, k_tgt)` in C
- The parallel morphisms are induced by the universal property

This shows that the functor category `[WalkingParallelPair, C]` has
coequalizers when C does, computed pointwise.

## References

- `docs/yoneda-coproduct-coequalizer-factorization.md` section 3
- [nLab: free cocompletion](https://ncatlab.org/nlab/show/free+cocompletion)
- [Mathlib: WalkingParallelPair](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Equalizers.html)
- [Mathlib: Cofork.IsColimit.mk](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/Equalizers.html)

## Implementation Summary

The implementation is in `GebLean/FreeCoequalizerCompletion.lean`.

### Structures

- `ParallelPairObj C` - objects (parallel pair diagrams)
- `ParallelPairHom P Q` - morphisms (commuting squares)

### Accessors/Constructors

- Object accessors: `ppSrc`, `ppTgt`, `ppLeft`, `ppRight`
- Object constructor: `ppObjMk`
- Morphism accessors: `ppSrcHom`, `ppTgtHom`
- Morphism constructor: `ppHomMk`
- Commutativity extractors: `ppLeftComm`, `ppRightComm`

### Category Structure

- `ppId`, `ppComp` - identity and composition
- `ppCategory` - Category instance for `ParallelPairObj C`

### Embedding

- `ppEmbedObj` - embed object from C as trivial parallel pair `(c, c, id, id)`
- `ppEmbedHom` - embed morphism
- `ppEmbedding : C -> ParallelPairObj C` - functor

### Coequalizers

Using `CoequalizerData` typeclass (computable coequalizer structure):

- `ppCoequalizerObj` - pointwise coequalizer object
- `ppCoequalizerπ` - projection morphism
- `ppCoequalizerDesc` - universal factorization
- `ppCofork` - the cofork for the coequalizer
- `ppCofork_isColimit` - proof that the cofork is a colimit

## Tasks

- [x] Research and planning (this document)
- [x] Define ParallelPairObj and helpers
- [x] Define ParallelPairHom and helpers
- [x] Define category instance
- [x] Define embedding functor
- [x] Prove HasCoequalizers (via Cofork.IsColimit)
- [x] Run lake build, fix errors
- [x] Run lake test

## Notes

The construction uses `CoequalizerData` typeclass (similar to `CoprodData`
and `ProdData` in Families.lean) for computable coequalizer structure. This
allows requiring noncomputability or excluded middle.

The `FreeCoequalizerCompletionCat` definition as a `Cat` object was removed
due to typeclass resolution issues with universe levels.
