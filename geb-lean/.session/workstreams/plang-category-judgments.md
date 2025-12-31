# PLang Category Judgments Workstream

## Status: Active

## Context

This workstream develops a universe-polymorphic formulation of category-judgment
copresheaves in `GebLean/PLang/CatJudgment.lean`. The primary goal is to
construct a reflective adjunction `L ⊣ Φ` from `Cat.{v,u}` to
`CatJudgCopr.{u,v,w,x}` where all four universe levels are independent and
unconstrained. This allows embedding categories at any universe level into
the copresheaf structure without universe restrictions.

**Universe Flexibility Requirement**: The adjunction must have:

- `Cat.{v,u}` on the left (object universe `u`, morphism universe `v`)
- `CatJudgCopr.{u,v,w,x}` on the right (four independent levels)
- `u` and `v` in `CatJudgCopr` correspond exactly to the Cat levels
- `w` and `x` are unconstrained additional levels for internal structure

**Mathlib Definitions Requirement**: All functors, natural transformations, and
adjunctions must use standard mathlib definitions (e.g., `CategoryTheory.Functor`,
`CategoryTheory.NatTrans`, `CategoryTheory.Adjunction`). Custom structures are
only acceptable for internal data representations that feed into mathlib
constructions.

**Reflective Embedding Requirement**: The adjunction must be proven to be a
reflective embedding with mathlib instances:

- `CategoryTheory.Functor.FullyFaithful Φ` - the right adjoint is fully faithful
- `CategoryTheory.Reflective Φ` - the adjunction is reflective

These instances establish that `Cat` embeds fully and faithfully into
`CatJudgCopr`, making `Cat` a reflective subcategory of `CatJudgCopr`.

The existing adjunction in `CatJudgmentAdjunction.lean` forces all levels equal.
The PLang formulation was designed to overcome this, but the current
implementation via `BundledOverCategoryData` still constrains universes. The
fix requires going directly from `Cat` to `CatJudgCopr` without intermediate
bundled structures that impose universe equality.

A related goal is establishing the categorical equivalence between
`JudgmentSection` and `CatJudgCopr`, and connecting this to the bicategorical
structure of Cat via functor categories.

## Tasks

### Phase 1: Documentation and Cleanup

- [x] Document PLang approach
- [x] Add docstrings to all definitions in CatJudgment.lean
- [x] Add explicit accessors with natural-language names

### Phase 2: Morphisms and Category Structure (Completed)

#### 2.1 JudgmentSection Morphisms

- [x] Define `JudgmentSectionHom s t`
  - Def: `Mor.CatJudgNatTrans s.catData t.catData`
- [x] Define `JudgmentSectionHom.id : JudgmentSectionHom s s`
- [x] Define `JudgmentSectionHom.comp`
  - Type: `JudgmentSectionHom s t → JudgmentSectionHom t u →`
    `JudgmentSectionHom s u`
- [x] Prove `JudgmentSectionHom.id_comp`
- [x] Prove `JudgmentSectionHom.comp_id`
- [x] Prove `JudgmentSectionHom.comp_assoc`
- [x] Define `Category JudgmentSection` instance

#### 2.2 Categorical Equivalence

- [x] Define `JudgmentSection.toCatJudgCoprFunctor : JudgmentSection ⥤ CatJudgCopr`
  - On objects: `s ↦ s.toCatJudgCopr`
  - On morphisms: identity (same type)
- [x] Define `JudgmentSection.ofCatJudgCoprFunctor : CatJudgCopr ⥤ JudgmentSection`
  - On objects: `c ↦ JudgmentSection.ofCatJudgCopr c`
  - On morphisms: identity (since `(ofCatJudgCopr c).catData = c`)
- [x] Prove `unitIso : 𝟭 JudgmentSection ≅ toCatJudgCoprFunctor ⋙ ofCatJudgCoprFunctor`
- [x] Prove `counitIso : ofCatJudgCoprFunctor ⋙ toCatJudgCoprFunctor ≅ 𝟭 CatJudgCopr`
- [x] Construct `JudgmentSection.catEquiv : JudgmentSection ≌ CatJudgCopr`

### Phase 3: Adjunction Port (Current Focus)

#### 3.1 Intermediate Implementation (Equal Universes)

The current implementation works with constrained universes to validate the
approach before generalizing:

- [x] Define morphisms between CatJudgCopr values in PLang.Mor namespace
  - PLangQuotientData represents CatJudgCopr
  - PLangQuotientMorphism represents morphisms (quiver morphism + witness maps)
- [x] Port embedding functor Phi to PLang form
  - EmbeddingPhi section defines the embedding
- [x] Port reflection functor L to PLang form (objects and morphisms)
  - L on objects: PLangQuotientData → Category (quotient category)
  - L on morphisms: quotMapMor with id/comp preservation
  - mapQuiver_respects_equiv for well-definedness on quotient
- [x] Define unit natural transformation for L ⊣ Phi
  - [x] unit_dom, unit_cod: definitional (rfl)
  - [x] unit_idMor: via id_witness and quotMor_heq_of_cast_equiv
  - [x] unit_left, unit_right: definitional (rfl)
  - [x] unit_composite: via comp_subst_tgt_right, congr, and subst_src_eq_cast
  - [x] Combined into `UnitAdjunction.unit : Mor.CatJudgNatTrans C (unitTarget C)`
- [x] Define counit natural transformation
  - [x] counitEvalAux, counitEval: evaluate PFreeMor in category C
  - [x] counitEval_respects_gen/equiv: respects equivalence relation
  - [x] counitEvalQuot: descends to quotient morphisms
  - [x] counitQuiverMor, counit_map_id, counit_map_comp: functor data
  - [x] counitFunctorData: OverFunctorData from L(Phi(C)) to C
  - [x] toPLangQuotientMorphism': OverFunctorData induces PLangQuotientMorphism
  - [x] counitEval_naturality, counitEvalQuot_naturality: counit is natural
- [x] Define triangle identity infrastructure
  - [x] trianglePhiC, triangleUnitPhiC, phiCounit for right triangle
  - [x] unitThenPhiCounit composition
  - [x] rightTriangle: Phi(eps_C) . eta_{Phi(C)} = id_{Phi(C)} proven
  - [x] triangleLX, trianglePhiLX, triangleLPhiLX for left triangle
  - [x] counitAtLX: eps_{L(X)}
  - [x] leftTriangle_obj, leftTriangle_mor: component-wise identities
  - [x] LUnitX: L(η_X) as OverFunctorData (factored lemma approach)
  - [x] leftTriangle: ε_{L(X)} ∘ L(η_X) = id_{L(X)} proven
  - [x] AdjunctionDataAt structure bundling unit, counit, and both triangles
  - [x] mkAdjunctionDataAt: constructor for adjunction data at any X
- [x] Fix unit_morMap_natural proof (sigma equality)
  - Used Sigma.ext + sigma_heq_of_fst_eq_snd_heq pattern
- [x] Fix unit_naturality_PLang proof (idMap/compMap components)
  - Extracted naturality equations as local hypotheses before rewriting
- [ ] Complete mathlib Adjunction construction with equal universes

#### 3.2 Universe-Flexible Adjunction (Required)

After validating the equal-universe version, generalize to fully independent
universe levels. This is the primary goal of this workstream.

- [ ] Identify and remove `PLangQuotientData.{w}` single-level constraint
- [ ] Define `PLangQuotientData.{u,v,w,x}` with four independent levels
- [ ] Redefine `toPLangQuotientData` for `C : Cat.{v,u}` producing
      `PLangQuotientData.{u,v,w,x}`
- [ ] Update `LFunctorPLang : CatJudgCopr.{u,v,w,x} ⥤ Cat.{v,u}`
- [ ] Update `PhiFunctorPLang : Cat.{v,u} ⥤ CatJudgCopr.{u,v,w,x}`
- [ ] Verify unit/counit naturality with flexible universes
- [ ] Construct mathlib `Adjunction L Φ` with full flexibility
- [ ] Remove `AdjunctionDataAt` custom structure (use mathlib throughout)

#### 3.3 Reflective Embedding Instances (Required)

- [ ] Prove `Functor.FullyFaithful PhiFunctorPLang`
  - Φ is fully faithful: `∀ X Y, (X ⟶ Y) ≃ (Φ X ⟶ Φ Y)`
- [ ] Construct `Reflective PhiFunctorPLang` instance
  - Combines the adjunction with full faithfulness

### Phase 4: Functor Categories and Bicategorical Connection

#### 4.1 Functor Category Correspondence

- [ ] Define `JudgmentSectionFunCat C` for sections parameterized by C
- [ ] Show `JudgmentSectionHom` corresponds to functors under the equivalence
- [ ] Define the functor `evalCat : JudgmentSectionCat → Cat` sending a
      section to its underlying category

#### 4.2 2-Cells via Modifications

- [ ] Define `JudgmentSectionModification` between section morphisms
- [ ] Show correspondence with natural transformations in Cat
- [ ] Verify modification composition and identity
- [ ] Show `[J, Cat]` modifications correspond to natural transformations

#### 4.3 Connection to PolyPresentationLoc

- [ ] Show JudgmentSection embeds into `PolyPresentationLoc JudgmentLevel` via Φ
- [ ] Track setoid structure through the embedding
- [ ] Verify pre-quotient morphisms correspond to modifications

### Phase 5: Recursive Generalization

- [ ] Define CatJudgCoprRec with CatJudgCopr target instead of Type
- [ ] Prove CatJudgCoprRec still forms a category
- [ ] Show Type embeds via discrete category construction
- [ ] Extend adjunction to recursive form

### Phase 6: Category Theory Embedding

- [ ] Define standard categorical constructions in CatJudgCopr terms
- [ ] Show transfer of constructions via adjunction
- [ ] Demonstrate topos structure of CatJudgCopr

## Implementation Details

### Phase 2.1: Morphism Definition

The morphism type between judgment sections is defined at the cat level:

```lean
def JudgmentSectionHom (s t : JudgmentSection) :=
  Mor.CatJudgNatTrans s.catData t.catData
```

This works because:

1. Sections at lower levels are uniquely determined by cat-level data
2. Forgetful functors are strict, so compatibility is automatic
3. The type `Mor.CatJudgNatTrans` already has identity and composition

The category instance inherits from `Cat.CatJudgCopr.category`:

```lean
instance : Category JudgmentSection where
  Hom := JudgmentSectionHom
  id s := Cat.CatJudgNatTrans.id s.catData
  comp f g := Cat.CatJudgNatTrans.comp f g
  id_comp := Cat.CatJudgNatTrans.id_comp
  comp_id := Cat.CatJudgNatTrans.comp_id
  assoc := Cat.CatJudgNatTrans.assoc
```

### Phase 2.2: Equivalence Strategy

The type equivalence `JudgmentSection.equivCatJudgCopr` extends to a
categorical equivalence because morphisms are definitionally equal:

```lean
def toCatJudgCoprFunctor : JudgmentSection ⥤ CatJudgCopr where
  obj := JudgmentSection.toCatJudgCopr
  map := id  -- morphisms are the same type
  map_id := rfl
  map_comp := rfl
```

The inverse functor requires transport for morphisms:

```lean
def ofCatJudgCoprFunctor : CatJudgCopr ⥤ JudgmentSection where
  obj := JudgmentSection.ofCatJudgCopr
  map f := by
    -- f : CatJudgNatTrans c d
    -- need: JudgmentSectionHom (ofCatJudgCopr c) (ofCatJudgCopr d)
    -- since (ofCatJudgCopr c).catData = c, this is just f
    exact f
```

### Phase 4: Bicategorical Structure

The correspondence from `docs/judgment-section-equivalence.md`:

| Cat (2-category) | [J, Cat] (2-category) |
| ---------------- | -------------------- |
| Categories | Cat-valued copresheaves |
| Functors | Natural transformations |
| Natural transformations | Modifications |

For JudgmentUniverse (already Cat-valued):

- Sections = 0-cells (categories)
- Section morphisms = 1-cells (functors)
- Modifications between section morphisms = 2-cells (natural transformations)

## Technical Notes

### Universe Constraints and Resolution

**Current State**: The Grothendieck-based implementation in
`CatJudgGrAdjunction.lean` uses four independent universe levels
`{uObj, uMor, uWit, uCWit}`:

- `CompWitGr.{uObj, uMor, uWit, uCWit}` has objects at `Type uObj`
- Quiver morphisms are at `Type uMor`
- Identity witnesses at `Type uWit`, composition witnesses at `Type uCWit`

The L functor constructs the quotient category:

- `LFunctor : CompWitGr.{uObj, uMor, uWit, uCWit} → Cat.{max uObj uMor, uObj}`

**Morphism Universe Analysis**: The morphism universe is `max uObj uMor`
(not just `uMor`) due to a fundamental constraint of the free category
construction:

1. `MorBundle X : Type (max uObj uMor)` bundles endpoints with morphisms
2. Free morphisms reference objects (for composition endpoints)
3. This forces morphisms to be at `max uObj uMor` unless `uObj ≤ uMor`

**FreeMor Redesign (Completed)**: FreeMor was redesigned with bundled morphisms:

```lean
def MorBundle X := Σ (a b : X.objType), X.Hom' a b

inductive FreeMorRaw X : Type (max uObj uMor) where
  | var : MorBundle X → FreeMorRaw X
  | id : FreeMorRaw X
  | comp : FreeMorRaw X → FreeMorRaw X → FreeMorRaw X

inductive ValidFreeMor X : X.objType → X.objType → FreeMorRaw X → Prop where
  | var, | id, | comp : (validity rules)

def FreeMor X a b := { m : FreeMorRaw X // ValidFreeMor X a b m }
```

This separation of raw structure from validity predicate enables
`mapFreeMorRaw` to operate on the non-indexed type, with validity
preserved as a Prop.

### Incremental Structure

PLang builds via sigma types:

```text
ObjCopr → ObjMorCopr → ObjMorIdCopr → CatJudgCopr
```

This allows operations at intermediate stages and clearer type signatures.

### Left Triangle (Completed)

The left triangle identity eps_{L(X)} . L(eta_X) = id_{L(X)} was proven using
a factored lemma approach. The approach breaks down the proof into small lemmas:

1. `quotDataPhiLX_idMor`, `quotDataPhiLX_compMatch`: show that structural
   properties in Phi(L(X)) are reflexivity
2. `embedLXMorAsVar_quotId`: uses `id_witness` from FreeMorEquivGen to show
   that embedding the identity as a variable equals the formal identity
3. `embedLXMorAsVar_quotComp`: uses `comp_witness` to show that embedding
   respects composition
4. `LUnitX_map_id`, `LUnitX_map_comp`: combine the above to prove L(eta_X)
   preserves identity and composition
5. `LUnitX`: the full OverFunctorData for L(eta_X)
6. `leftTriangle`: composition with counit gives identity

The id_witness and comp_witness constructors in FreeMorEquivGen provide the
quotient identities needed. Using `Quotient.sound` and `convert` allowed the
type coercions to be handled one at a time.

### Accessor Naming Convention

Accessors should follow the pattern:

- `.obj` for object component
- `.mor` for morphism component
- `.dom`, `.cod` for domain/codomain functions
- `.idMor` for identity morphism function
- `.left`, `.right`, `.comp` for composition components

## Files

- `GebLean/PLang/CatJudgment.lean` - Main object/morphism definitions
- `GebLean/PLang/JudgmentUniverse.lean` - JudgmentLevel, JudgmentSection
- `docs/plang-category-judgments.md` - Documentation (PLang approach)
- `docs/judgment-section-equivalence.md` - Architecture (bicategorical structure)
- `GebLean/CatJudgmentAdjunction.lean` - Adjunction to port

## Dependencies

- Phase 2 requires: `Mor.CatJudgNatTrans` with identity/composition
- Phase 3 requires: Phase 2 complete
- Phase 4 requires: Phase 2 complete, understanding of [J, Cat] structure
- Phase 5 requires: Phases 2-4 as foundation
