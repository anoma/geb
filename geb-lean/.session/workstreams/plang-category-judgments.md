# PLang Category Judgments Workstream

## Status: Active

## Context

This workstream develops a universe-polymorphic formulation of category-judgment
copresheaves in `GebLean/PLang/CatJudgment.lean`. The goal is to port the
adjunction from `CatJudgmentAdjunction.lean` to the PLang form, then generalize
to allow recursive `CatJudgCopr` targets.

## Relationship to PolyPresentation

The PolyPresentation work (see `copresheaf-coequalizer-equivalence.md`) provides
a complementary characterization:

- `PolyPresentationLoc D ≃ (D ⥤ Type)` via the density formula
- Every copresheaf is a coequalizer of polynomial functors
- The density presentation functor uses category of elements

The PLang adjunction and PolyPresentation work connect via:

1. Both characterize "category-like structures" from different perspectives
2. The embedding Phi produces a CatJudgCopr which can be evaluated to copresheaf
3. The reflection L takes judgment data and quotients to a category

## Tasks

### Phase 1: Documentation and Cleanup - COMPLETE

- [x] Document PLang approach
- [x] Add docstrings to all definitions in CatJudgment.lean
- [x] Add explicit accessors with natural-language names

### Phase 2A: Embedding Functor Phi_PLang - COMPLETE

- [x] Define `catToCatJudgCopr`:
      `(C : Type u) → [Category.{v} C] → CatJudgCopr.{u, max u v, u, max u v}`
  - obj = C (objects of the category)
  - mor = BundledHom C = Σ (a b : C), (a ⟶ b)
  - idType = C (identity witnesses = objects)
  - compType = ComposablePair C = Σ (a b c : C), (a ⟶ b) × (b ⟶ c)
  - Implemented dom, cod, idMor, left, right, composite
  - Proved id_endo, comp_match, comp_dom, comp_cod coherence conditions

- [x] Define `functorToCatJudgNatTrans`:
      Given F : C ⥤ D, produce CatJudgNatTrans between their CatJudgCopr values
  - Uses functorMapBundledHom and functorMapComposablePair
  - Proved all naturality conditions (dom, cod, idMor, left, right, composite)

- [x] Prove functoriality: functorToCatJudgNatTrans_id, functorToCatJudgNatTrans_comp

- [x] Define `PhiFunctor_PLang`:
      `Cat.{v'+1, u'+1} ⥤ CatJudgCopr.{u'+1, max (u'+1) (v'+1), u'+1, max (u'+1) (v'+1)}`
      (universe shift required for category structure on target)

### Phase 2B: Reflection Functor L_PLang

- [ ] Define `catJudgCoprToOverQuiver`:
      Extract OverQuiver from CatJudgCopr (obj, mor, dom, cod)

- [ ] Define `catJudgCoprToCategoryQuotientData`:
      Package CatJudgCopr into CategoryQuotientData format
  - quiver = catJudgCoprToOverQuiver s
  - IdWitness = s.idType
  - idObj, idMor from s structure
  - CompWitness = s.compType
  - compRight, compLeft, compComposite from s structure

- [ ] Verify FreeMor/FreeMorEquiv work with CatJudgCopr-derived quivers
  - FreeMor already parameterized by OverQuiver, should work
  - FreeMorEquiv uses CategoryQuotientData, should work
  - Check universe level compatibility

- [ ] Define `catJudgCoprToCat`:
      `CatJudgCopr.{u, v, w, x} → Cat.{max v w x, u}`
  - Objects = s.obj
  - Morphisms a b = Quot (FreeMorEquiv between a and b)
  - Identity, composition via FreeMor constructors lifted through Quot
  - Category laws from FreeMorEquiv properties

- [ ] Define morphism mapping for L_PLang
  - Given CatJudgNatTrans f : s → t
  - Induce functor catJudgCoprToCat s ⥤ catJudgCoprToCat t
  - Object map = f.objMap
  - Morphism map = lift FreeMor.map through quotient

- [ ] Prove functoriality: map_id, map_comp

- [ ] Define `LFunctor_PLang : CatJudgCopr.{u, v, w, x} ⥤ Cat.{max v w x, u}`

### Phase 2C: Prove Adjunction

- [ ] Define unit: η : id → Phi ∘ L
  - For each CatJudgCopr s, natural transformation s → Phi(L(s))
  - objMap: s.obj → (L s).obj = id
  - morMap: s.mor → bundled morphisms in L(s), via FreeMor.var
  - idMap, compMap similarly
  - Prove naturality

- [ ] Define counit: ε : L ∘ Phi → id
  - For each category C, functor L(Phi(C)) ⥤ C
  - Object map = id
  - Morphism map: quotient of FreeMor → actual morphisms
  - Prove functoriality (uses FreeMorEquiv respects category structure)

- [ ] Prove triangle identities:
  - ε_Phi ∘ Phi_η = id (for all categories C)
  - L_ε ∘ η_L = id (for all CatJudgCopr s)

- [ ] Construct `adjunction_PLang : LFunctor_PLang ⊣ PhiFunctor_PLang`

### Phase 3: Recursive Generalization

- [ ] Define CatJudgCoprRec with CatJudgCopr target instead of Type
- [ ] Prove CatJudgCoprRec still forms a category
- [ ] Show Type embeds via discrete category construction
- [ ] Extend adjunction to recursive form

### Phase 4: Category Theory Embedding

- [ ] Define standard categorical constructions in CatJudgCopr terms
- [ ] Show transfer of constructions via adjunction
- [ ] Demonstrate topos structure of CatJudgCopr
- [ ] Connect to PolyPresentation via density formula

## Technical Notes

### Universe Level Analysis

For a category C with `C : Type u` and `Category.{v} C`:

- Objects: Type u
- Morphisms: Type v (Hom sets)
- Identity witnesses: same as objects (Type u)
- Composition witnesses: Σ (a b c : C), (a ⟶ b) × (b ⟶ c) : Type (max u v)

This maps to CatJudgCopr.{u+1, v+1, u+1, max u v + 1}:

- CatJudgCopr adds +1 to each universe for the sigma type structure

For the reflection L:

- Input: CatJudgCopr.{u, v, w, x}
- FreeMor Q a b : Type (max v u) for Q : OverQuiver.{v, u}
- Output category morphisms: Quot of FreeMor : Type (max v w x u)

### Structural Correspondence

| CatJudgmentAdjunction.lean | PLang Port |
|---------------------------|------------|
| OverCategoryData | Category C with Category.{v} C |
| CategoryJudgments.FunctorData | CatJudgCopr.{u, v, w, x} |
| CategoryQuotientData | Derived from CatJudgCopr |
| FreeMor | Same, parameterized by OverQuiver |
| FreeMorEquiv | Same, parameterized by CategoryQuotientData |

### Incremental Structure

PLang builds via sigma types:

```text
ObjCopr → ObjMorCopr → ObjMorIdCopr → CatJudgCopr
```

This allows operations at intermediate stages and clearer type signatures.

## Files

- `GebLean/PLang/CatJudgment.lean` - Main definitions (Phase 1 complete)
- `GebLean/PLang/CatJudgmentAdjunction.lean` - New file for adjunction (Phase 2)
- `GebLean/CatJudgmentAdjunction.lean` - Existing adjunction to port from
- `docs/plang-category-judgments.md` - Documentation

## Dependencies

The PLang adjunction port depends on:

- `GebLean/PLang/CatJudgment.lean` - CatJudgCopr, CatJudgNatTrans, forgetful functors
- `GebLean/CategoryJudgments.lean` - May reuse some utilities
- `Mathlib.CategoryTheory.Category.Cat` - Cat category
- `Mathlib.CategoryTheory.Adjunction.Basic` - Adjunction machinery
