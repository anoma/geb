# PLang Category Judgments Workstream

## Status: Active

## Context

This workstream develops a universe-polymorphic formulation of category-judgment
copresheaves in `GebLean/PLang/CatJudgment.lean`. The goal is to port the
adjunction from `CatJudgmentAdjunction.lean` to the PLang form, then generalize
to allow recursive `CatJudgCopr` targets.

## Tasks

### Phase 1: Documentation and Cleanup

- [x] Document PLang approach
- [x] Add docstrings to all definitions in CatJudgment.lean
- [x] Add explicit accessors with natural-language names

### Phase 2: Adjunction Port

- [ ] Define morphisms between CatJudgCopr values in PLang.Mor namespace
- [ ] Port embedding functor Phi to PLang form
- [ ] Port reflection functor L to PLang form
- [ ] Prove adjunction with flexible universe levels
- [ ] Verify adjunction works for Cat.{v,u} and CatJudgCopr.{u,v,w,x}

### Phase 3: Recursive Generalization

- [ ] Define CatJudgCoprRec with CatJudgCopr target instead of Type
- [ ] Prove CatJudgCoprRec still forms a category
- [ ] Show Type embeds via discrete category construction
- [ ] Extend adjunction to recursive form

### Phase 4: Category Theory Embedding

- [ ] Define standard categorical constructions in CatJudgCopr terms
- [ ] Show transfer of constructions via adjunction
- [ ] Demonstrate topos structure of CatJudgCopr

## Technical Notes

### Universe Constraints

The current adjunction is constrained to `{u, u}` because:

1. Copresheaf values are in `Type u`
2. Conversions produce `OverCategoryData.{u, u}`

The PLang formulation uses explicit parameters `{u, v, w, x}` to overcome this.

### Incremental Structure

PLang builds via sigma types:

```text
ObjCopr → ObjMorCopr → ObjMorIdCopr → CatJudgCopr
```

This allows operations at intermediate stages and clearer type signatures.

### Accessor Naming Convention

Accessors should follow the pattern:

- `.obj` for object component
- `.mor` for morphism component
- `.dom`, `.cod` for domain/codomain functions
- `.idMor` for identity morphism function
- `.left`, `.right`, `.comp` for composition components

## Files

- `GebLean/PLang/CatJudgment.lean` - Main definitions
- `docs/plang-category-judgments.md` - Documentation
- `GebLean/CatJudgmentAdjunction.lean` - Adjunction to port
