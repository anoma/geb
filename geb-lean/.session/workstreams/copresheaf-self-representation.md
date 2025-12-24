# Copresheaf Self-Representation Workstream

Status: Phase 5 Complete (2025-12-23)

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

### Phase 4: Internal Category Structure (Complete)

Also in `GebLean/PLang/JudgmentUniverse.lean`:

1. **Morphism bundles**: Types for bundled morphisms at each level:
   - `ObjMorBundle`: sigma type (X, Y, f : X -> Y)
   - `QuivMorBundle`: sigma type with quiver homomorphisms
   - `CatMorBundle`: sigma type with category natural transformations

2. **Source/target projections**: For each bundle type via `.src` and `.tgt`

3. **Identity morphisms**: At each level using existing category structure:
   - `ObjMorBundle.identity`
   - `QuivMorBundle.identity`
   - `CatMorBundle.identity`

4. **Composition**: At each level with explicit type transport:
   - `ObjMorBundle.comp`
   - `QuivMorBundle.comp`
   - `CatMorBundle.comp`

5. **Identity laws**: Proved via `rfl` (definitional equality):
   - `ObjMorBundle.id_comp`, `ObjMorBundle.comp_id`
   - `QuivMorBundle.id_comp`, `QuivMorBundle.comp_id`
   - `CatMorBundle.id_comp`, `CatMorBundle.comp_id`

6. **Associativity laws**: Proved using `obtain` + `subst`:
   - `ObjMorBundle.comp_assoc`
   - `QuivMorBundle.comp_assoc`
   - `CatMorBundle.comp_assoc`

7. **Forgetful maps between bundles**:
   - `forgetQuivBundleToObjBundle`
   - `forgetCatBundleToQuivBundle`
   - `forgetCatBundleToObjBundle`

8. **Morphism bundle copresheaf**: `MorphismBundleCopresheaf : JudgmentLevel ⥤ Type`
   - `toMorBundleType`: maps levels to bundle types
   - `toMorBundleMap`: functorial action via forgetful maps
   - Functoriality proved (map_id, map_comp)

9. **Source/target projections**: `sourceProj` and `targetProj` for each level

### Phase 5: Currying Connection (Complete)

Extended `GebLean/PLang/JudgmentUniverse.lean` with:

1. **Uncurried evaluation**: `JudgmentSection.evalAt` evaluates a section
   at each judgment level, giving the "uncurried" view of sections as
   functions `J × Section → Object`.

2. **Naturality theorems**:
   - `evalAt_quivToObj`: evaluation respects quiv → obj forgetful functor
   - `evalAt_catToQuiv`: evaluation respects cat → quiv forgetful functor
   - `evalAt_catToObj`: evaluation respects cat → obj forgetful functor
   - `evalAt_natural`: general naturality for all morphisms in JudgmentLevel

3. **Type extraction**:
   - `JudgmentSection.objType`: extract object type from section
   - `JudgmentSection.morType`: extract morphism type from section

4. **Product type**: `JudgmentProductType` as base for uncurried perspective

5. **Documentation**: Connection to Mathlib's `CategoryTheory.Functor.currying`
   explaining how the currying isomorphism `[A × B, C] ≅ [A, [B, C]]` relates
   to the adjunction perspective.

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

4. **Currying equivalence**: `CategoryTheory.Functor.currying` provides
   `Functor C (Functor D E) ≌ Functor (Prod C D) E` which connects
   the curried and uncurried views of functors.

### Connection to Currying

From `docs/cat-currying-natural-transformations.md`:

The isomorphism `[A × B, C] ≅ [A, [B, C]]` applies to the adjunction:

- Right adjoint `U : Cat → [J, Type]` corresponds to `U' : Cat × J → Type`
- This is a copresheaf on the product category Cat × J
- Internalizing means expressing U' as a section of JudgmentUniverse
- The `evalAt` function captures the uncurried evaluation
- Naturality of `evalAt` is the functoriality condition for the second argument

## Success Criteria

All completed:

- [x] Judgment category J is formally defined
- [x] JudgmentUniverse : J -> Cat is a well-defined functor
- [x] Sections of JudgmentUniverse correspond to category specifications
- [x] Internal category structure on [J, Type] is established
- [x] Connection to CatJudgmentAdjunction via currying is documented

## File Summary

- `GebLean/PLang/JudgmentUniverse.lean`: ~674 lines (Phases 1-5 complete)

## Future Work

Potential extensions (not currently planned):

- Formal functor `CatJudgCopr ⥤ (JudgmentLevel ⥤ Type)` making the
  currying connection explicit at the functor level
- Connection between `JudgmentLevel` (level-based) and `CategoryJudgments.Obj`
  (component-based) representations
