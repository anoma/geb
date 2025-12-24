# Copresheaf Self-Representation Workstream

Status: Phase 1-4 In Progress (2025-12-23)

## Objective

Express the copresheaf topos [J, Type] as an object within itself, enabling
the CatJudgmentAdjunction to be formulated entirely in terms of copresheaves.

## Background

See `docs/copresheaf-self-representation.md` for the theoretical foundation.

## Completed Work (2025-12-23)

### Phase 1-3: JudgmentUniverse Functor and Sections

Implemented in `GebLean/PLang/JudgmentUniverse.lean`:

1. **JudgmentLevel type**: Inductive type with constructors `obj`, `quiv`,
   `cat` representing levels of categorical structure.

2. **Judgment category structure**:
   - `JudgmentLevel.Hom`: morphisms including `id`, `quivToObj`, `catToQuiv`,
     `catToObj`
   - Category instance on `JudgmentLevel`
   - Composition and identity laws proved

3. **JudgmentUniverse functor**: `JudgmentLevel ⥤ Cat` mapping:
   - `obj` to `Cat.of ObjCopr`
   - `quiv` to `Cat.of ObjMorCopr`
   - `cat` to `Cat.of CatJudgCopr`
   - Morphisms to forgetful functors
   - Functoriality proved (map_id, map_comp)

4. **JudgmentSection structure**: Compatible data at all levels with
   coherence conditions via forgetful functors.

5. **Equivalence**: `JudgmentSection.equivCatJudgCopr` proving sections
   are equivalent to `CatJudgCopr` (most refined level determines all).

### Phase 4: Internal Category Structure (Partial)

Also in `GebLean/PLang/JudgmentUniverse.lean`:

1. **Morphism bundles**: Types for bundled morphisms at each level:
   - `ObjMorBundle`: pairs (X, Y, f : X -> Y) of types and functions
   - `QuivMorBundle`: pairs with quiver homomorphisms
   - `CatMorBundle`: pairs with category natural transformations

2. **Source/target projections**: For each bundle type

3. **Identity morphisms**: At each level using existing category structure

4. **Composition**: At each level with explicit type transport

Remaining for Phase 4:

- Prove identity and associativity laws for the bundle operations
- Show that morphism bundles form a category at each level
- Define the morphism copresheaf as a functor

## Research Findings

### Mathlib Infrastructure

1. **Grothendieck construction**: Mathlib provides `Grothendieck F` for
   functors `F : C -> Cat`, with projection functor `Grothendieck.forget`.

2. **Category of elements**: `grothendieckTypeToCat` gives an equivalence
   `Grothendieck (G ⋙ typeToCat) ≃ G.Elements`. This is the "total space"
   view, NOT the sections view we need.

3. **No direct "sections of a fibration"**: Mathlib has `Functor.sections`
   which gives the SET of global sections (dependent functions satisfying
   naturality), but not the CATEGORY of sections as functors `s : B -> E`
   with `π ∘ s = id`.

### Connection to Currying

From `docs/cat-currying-natural-transformations.md`:

The isomorphism `[A × B, C] ≅ [A, [B, C]]` applies to the adjunction:

- Right adjoint `U : Cat → [J, Type]` corresponds to `U' : Cat × J → Type`
- This is a copresheaf on the product category Cat × J
- Internalizing means expressing U' as a section of JudgmentUniverse

## Remaining Phases

### Phase 4 Completion: Internal Category Structure

Complete the internal category [J, Type] within [J, Type (u+1)]:

- Prove category laws for morphism bundles
- Define morphism copresheaf as a functor J -> Type (u+1)
- Establish internal category axioms

### Phase 5: Adjunction via Currying

Using `[Cat × J, Type] ≅ [Cat, [J, Type]]`:

- The right adjoint U : Cat → [J, Type] corresponds to a copresheaf
  U' : Cat × J → Type on the product category
- U'(C, j) = the j-level data of category C
- This connects self-representation to the adjunction

## Success Criteria

Completed:

- [x] Judgment category J is formally defined
- [x] JudgmentUniverse : J -> Cat is a well-defined functor
- [x] Sections of JudgmentUniverse correspond to category specifications

In progress:

- [ ] Internal category structure on [J, Type] is established

Remaining:

- [ ] Connection to CatJudgmentAdjunction via currying is documented

## File Summary

- `GebLean/PLang/JudgmentUniverse.lean`: ~365 lines (Phases 1-4 partial)

Estimated remaining:

- Complete internal category proofs: ~150 lines
- Adjunction connection: ~200 lines
