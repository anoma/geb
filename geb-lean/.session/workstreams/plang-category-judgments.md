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
      `Cat.{v'+1, u'+1} ⥤ CatJudgCopr.{u'+1, max (u'+1) (v'+1),
       u'+1, max (u'+1) (v'+1)}`
      (universe shift required for category structure on target)

### Phase 2B: Reflection Functor L_PLang - COMPLETE

- [x] Define `catJudgCoprToOverQuiver`:
      Extract OverQuiver from CatJudgCopr (obj, mor, dom, cod)

- [x] Define `catJudgCoprToCategoryQuotientData`:
      Package CatJudgCopr into CategoryQuotientData format
  - quiver = catJudgCoprToOverQuiver s
  - IdWitness = s.idType
  - idObj, idMor from s structure
  - CompWitness = s.compType
  - compRight, compLeft, compComposite from s structure

- [x] Verify FreeMor/FreeMorEquiv work with CatJudgCopr-derived quivers
  - FreeMor already parameterized by OverQuiver, works
  - FreeMorEquiv uses CategoryQuotientData, works
  - Universe restriction: w = x = u required for CategoryQuotientData

- [x] Define `catJudgCoprToCat'`:
      `CatJudgCopr.{u', v', u', u'} → Cat.{max v' u', u'}`
  - Objects = s.obj
  - Morphisms a b = Quot (FreeMorEquiv between a and b)
  - Identity, composition via FreeMor constructors lifted through Quot
  - Category laws from FreeMorEquiv properties

- [x] Define morphism mapping for L_PLang
  - `catJudgNatTransToQuotQuiverMor`: OverQuiverMorphism between quotient quivers
  - `catJudgNatTransToOverFunctorData`: OverFunctorData with id/comp preservation
  - `catJudgNatTransToFunctorData`: FunctorData via toBundledCategoryData_map
  - `catJudgNatTransToCatMor`: morphism in Cat

- [x] Prove functoriality: map_id, map_comp (layered proofs)
  - `catJudgNatTransToOverFunctorData_id/comp`
  - `catJudgNatTransToFunctorData_id/comp`
  - `catJudgNatTransToCatMor_id/comp`

- [x] Define `LFunctor_PLang`:
      `CatJudgCopr.{uL+1, vL+1, uL+1, uL+1} ⥤ Cat.{max (vL+1) (uL+1), uL+1}`

### Phase 2C: Prove Adjunction

- [x] Define unit components: unitObjMap, unitMorMap, unitIdMap, unitCompMap
- [x] Prove unitNaturalityDom, unitNaturalityCod, unitNaturalityIdMor
- [x] Prove unitNaturalityLeft, unitNaturalityRight
- [x] Prove unitNaturalityComposite
- [x] Define unitNaturalityAll, unitCatJudgNatTrans

- [-] Define counit: ε : L ∘ Phi → id (IN PROGRESS)
  - [x] counitSource, counitQuiver, counitCQD abbreviations
  - [x] counitEvalAux: evaluate FreeMor to BundledHom with proofs
  - [x] counitEval: evaluate FreeMor to actual morphism in C
  - [x] counitEval_var, counitEval_id: evaluation of primitives
  - [x] counitEval_comp: evaluation respects composition
  - [x] counitEval_resp_gen, counitEval_resp: evaluation respects FreeMorEquiv
  - [x] counitFunctorMap: lift counitEval through quotient
  - [x] counitFunctorMap_id, counitFunctorMap_comp: functoriality
  - [x] extractQuotMor, counitHomMap: helper functions for HomSet
  - [x] extractQuotMor_id, extractQuotMor_comp: extract lemmas
  - [x] counitFunctor: the actual functor L(Phi(C)) ⥤ C
  - [x] LPhiObj, LPhiFunctor: helper abbreviations
  - [x] counitEval_var_functor_map, counitEval_id_functor_map: basic naturality lemmas
  - [ ] counit naturality: L(Phi(F)) ≫ ε_D = ε_C ≫ F for functors F : C ⥤ D
    - Requires showing counitHomMap commutes with catJudgNatTransToCatMor
    - Pattern: induction on FreeMor, use counitEval commutation lemmas
  - [ ] counitNT_PLang: NatTrans from LFunctor_PLang ⋙ PhiFunctor_PLang to id

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
| ------------------------- | ---------- |
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
