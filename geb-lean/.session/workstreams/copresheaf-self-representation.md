# Copresheaf Self-Representation Workstream

Status: Research Complete, Implementation Ready (2025-12-23)

## Objective

Express the copresheaf topos [J, Type] as an object within itself, enabling
the CatJudgmentAdjunction to be formulated entirely in terms of copresheaves.

## Background

See `docs/copresheaf-self-representation.md` for the theoretical foundation.

## Research Findings (2025-12-23)

### Mathlib Infrastructure

1. **Grothendieck construction**: Mathlib provides `Grothendieck F` for
   functors `F : C ⥤ Cat`, with projection functor `Grothendieck.forget`.

2. **Category of elements**: `grothendieckTypeToCat` gives an equivalence
   `Grothendieck (G ⋙ typeToCat) ≃ G.Elements`. This is the "total space"
   view, NOT the sections view we need.

3. **No direct "sections of a fibration"**: Mathlib has `Functor.sections`
   which gives the SET of global sections (dependent functions satisfying
   naturality), but not the CATEGORY of sections as functors `s : B ⥤ E`
   with `π ∘ s = id`.

4. **Fibered categories**: `IsFibered` and cartesian lifts exist but focus
   on the fibration structure, not sections.

### Existing Code Analysis

The `CatJudgment.lean` file ALREADY implements the structured universe:

- `ObjCopr` = Type u (object level)
- `ObjMorCopr` = Σ(o : ObjMorObj), ObjMorMor o (quiver level)
- `CatJudgCopr` = full category signature with axioms

The forgetful functors (`forgetCatJudgToObjMor`, etc.) define functoriality.
This IS the JudgmentUniverse structure, just not yet organized as a functor
to Cat.

### Connection to Currying

From `docs/cat-currying-natural-transformations.md`:

The isomorphism `[A × B, C] ≅ [A, [B, C]]` applies to the adjunction:

- Right adjoint `U : Cat → [J, Type]` corresponds to `U' : Cat × J → Type`
- This is a copresheaf on the product category Cat × J
- Internalizing means expressing U' as a section of JudgmentUniverse

### Refined Understanding

The self-representation works as follows:

1. **JudgmentUniverse : J → Cat** where J is the (implicit) judgment category
   - At level j_Obj: Cat.of (Type u)
   - At level j_Quiv: Cat.of ObjMorCopr
   - At level j_Cat: Cat.of CatJudgCopr

2. **Sections vs Elements distinction**:
   - The category of elements ∫JudgmentUniverse has objects (j, x) where
     x is a structure at level j
   - A section s : J → ∫JudgmentUniverse picks compatible structures at
     all levels (this corresponds to a complete category specification)

3. **Copresheaves on J are NOT directly sections**: A general copresheaf
   `F : J → Type u` assigns a type to each level. The JudgmentUniverse
   structure is specifically for category-like copresheaves where the
   types at different levels are related (objects, morphisms, etc.).

## Revised Implementation Strategy

Following the suggestion to specialize to the judgment category first:

### Phase 1: Judgment Category Formalization

Location: `GebLean/PLang/JudgmentCategory.lean` (new file)

The judgment category J has:
- Objects: judgment levels (j_Obj, j_Quiv, j_Cat, etc.)
- Morphisms: refinement/forgetful relations

Currently implicit in CatJudgment.lean; needs explicit definition.

### Phase 2: JudgmentUniverse as Functor

Location: `GebLean/PLang/JudgmentUniverse.lean` (new file)

Organize existing types as a functor:

```lean
/-- The judgment universe functor to Cat. -/
def JudgmentUniverse : JudgmentCat ⥤ Cat where
  obj
  | j_Obj => Cat.of ObjCopr
  | j_Quiv => Cat.of ObjMorCopr
  | j_Cat => Cat.of CatJudgCopr
  map := existing forgetful functors
```

### Phase 3: Sections Category

Location: `GebLean/PLang/JudgmentSections.lean` (new file)

Define what it means to be a "section" of JudgmentUniverse:

```lean
/-- A section of the judgment universe assigns compatible structures
    at each level. -/
structure JudgmentSection where
  objData : ObjCopr
  quivData : ObjMorCopr
  catData : CatJudgCopr
  quiv_obj : forgetObjMorToObj.obj quivData = objData
  cat_quiv : forgetCatJudgToObjMor.obj catData = quivData
```

This is isomorphic to `CatJudgCopr` (the most refined level determines all).

### Phase 4: Internal Category Structure

Build the internal category [J, Type] within [J, Type (u+1)]:

- Object copresheaf: JudgmentUniverse itself (viewed as valued in Type (u+1))
- Morphism copresheaf: natural transformations at each level
- Source/target/identity/composition: derived from category structure on
  each JudgmentUniverse(j)

### Phase 5: Adjunction via Currying

Using `[Cat × J, Type] ≅ [Cat, [J, Type]]`:

- The right adjoint U : Cat → [J, Type] corresponds to a copresheaf
  U' : Cat × J → Type on the product category
- U'(C, j) = the j-level data of category C
- This connects self-representation to the adjunction

## Open Questions (Refined)

1. **Judgment category formalization**: Should J be an inductive type,
   a finite category, or described implicitly via the existing types?

2. **Section vs copresheaf distinction**: For the structured universe,
   sections are NOT arbitrary copresheaves but specifically those with
   compatible data across levels. How to capture this formally?

3. **Universe polymorphism**: The existing code uses multiple universe
   parameters (u, v, w, x). How to organize these for the functor structure?

4. **Forgetful functor composition**: Need to verify the existing forgetful
   functors compose correctly to form a functor from the judgment category.

## Success Criteria

After completion:

- Judgment category J is formally defined
- JudgmentUniverse : J ⥤ Cat is a well-defined functor
- Sections of JudgmentUniverse correspond to category specifications
- Internal category structure on [J, Type] is established
- Connection to CatJudgmentAdjunction via currying is documented

## Estimated Scope (Revised)

- `JudgmentCategory.lean`: ~150 lines (formalize J)
- `JudgmentUniverse.lean`: ~300 lines (functor structure)
- `JudgmentSections.lean`: ~200 lines (section definition)
- `InternalCopresheafCat.lean`: ~400 lines (internal category)

Total: ~1050 lines of new code

## Next Actions

1. **Immediate**: Formalize the judgment category J explicitly
2. Organize existing forgetful functors as a single functor J → Cat
3. Define sections and prove isomorphism with CatJudgCopr
4. Build internal category structure
