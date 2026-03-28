# Workstream: Presheaf PRA

## Status

Phase 1 complete. Phase 2 complete. Phases 3-5
in progress (Phase 4 partially done).

## Goal

Define polynomial functors between presheaf categories
(parametric right adjoints) in Lean, prove they
generalize slice-polynomial functors, and develop
universal morphisms, composition, and algebraic
structures.

## Design Principles

### One step at a time

Every definition and proof should take exactly one
step beyond the definitions it depends on.  Factor
out intermediate definitions so that each one is
expressed in terms of the layer directly below it.
Use `def`, not `abbrev`.

### Everything is functorial

Every operation must be expressed as a functor, natural
transformation, or other higher-order categorical
construction.

### Use mathlib's `op`, not our `op'`

All new constructions use mathlib's `Opposite` (`ᵒᵖ`)
for interoperability.  No dependence on `op'`-based
constructions.

## Completed Work

### Phase 1: Core Definitions

**File:** `GebLean/PresheafPRA.lean`

Definitions in `PresheafPRA.lean`:

- `catHomProfunctor` — Cat-enriched hom
- `catCovarHomFunctor` / `catContraHomFunctor`
- `presheafCatFunctor` — `I ↦ Iᵒᵖ ⥤ Type`
- `ccrPresheafCatFunctor` — `I ↦ CCR(PSh(I))`
- `presheafPRACatProfunctor` — no free params
- `presheafPRACatFunctor` — fix `J`, vary `I`
- `PresheafPRACat I J` — the PRA category
- `praPositionsFunctor` — positions as functor
- `praDirectionsAtFunctor` — nLab's `E_T`
- `praEvalAtProfunctor` — profunctor form
- `praEvalAtFunctor` — `PSh(I) ⥤ PSh(J)` form
- `praEvalAt P Z j` — pointwise evaluation

Definitions in `Utilities/Category.lean`:

- `catHomProfunctor_eq_internalHom` — equals
  mathlib `internalHom` when universes match
- `Cat.pre_app_eq_whiskeringLeft` — Cat CCC
- `grothendieckFunctor` — Grothendieck as functor
- `pi_eqToHom_apply` etc. — Pi eqToHom utilities

Definitions in `Utilities/Families.lean`:

- `familyFunctor` / `familyBifunctor` — using `op`
- `FreeProdCompletion` / `freeProdCompletionFunctor`
- `CoprodCovarRepCat` / `coprodCovarRepFunctor`
- `ccrNewIndexFunctor` — index projection
- `ccrNewFamilyFunctor` — family extraction
- `ccrNewEvalFunctor` / `ccrNewEvalCatFunctor`
- `ccrNewEvalCatFullyFaithful` — fully faithful

Definitions in `Utilities/Elements.lean`:

- `elementsPrecomp` — precomposition on Elements

### Full Faithfulness

- `ccrNewEvalCatFullyFaithful` — Yoneda argument
- `praEvalAtProfunctorFullyFaithful` — via
  `whiskeringRight`
- `praEvalAtFunctorFullyFaithful` — via
  `Functor.flipping`

### Phase 2: Discrete-Category Equivalence

**File:** `GebLean/PresheafPRADiscrete.lean`

- `overDiscretePresheafEquiv` — `Over X ≌ PSh(Disc X)`
- `ccrMapEquiv` — lift equivalence through CCR'
- `ccrOverDiscreteEquiv` — inner CCR equivalence
- `polyBetweenPresheafPRAEquiv` — full equivalence
  `PolyBetween X Y ≌ PRA(Disc X)(Disc Y)`
- `evalCompatEquiv` — fiber evaluation compat
- `evalCompatFwd_natural` — naturality in `A`
- `evalCompatOverIso` — object-level iso

### Phase 4 (partial): Limits of CoprodCovarRepCat

**File:** `GebLean/PresheafPRAUMorph.lean`

- `piHasColimitsOfShape` — Pi categories have colimits
- `grothendieckFiberHasColimitsOfShape` — fibers ok
- `typeOpHasColimitsOfShape` — `(Type w)ᵒᵖ` ok
- `ccrDiagPosFunctor D` — position diagram
- `ccrLimPosSections D` — compatible families
- `ccrDiagFiberFunctor D z` — fiber diagram
- `ccrHasLimit D` — limits exist (when `C` has
  colimits of `Jᵒᵖ`)
- `ccrHasLimitsOfShape` — typeclass instance
- `ccrHasLimitsOfSize` — all limits of size
  `(w, w)` when `C` has all colimits of that size
- `ccrLimVertexGr` — computable limit vertex
- `ccrLimIotaGr` — injection morphisms
- `ccrLimCoconeGr` — colimit cocone (Grothendieck)
- `ccrLimCoconeGrIsColimit` — universal property
- `ccrLimitCone` — computable `LimitCone`
- `ccrLimFunctor` — computable limit functor
  parameterized by colimit cocone choices
- `ccrConstLimAdj` — `Functor.const J ⊣
  ccrLimFunctor chooseColim` adjunction

### Phase 4 (partial): PRA Reassembly and Products

**File:** `GebLean/PresheafPRAUMorph.lean`

PRA Reassembly (Task A0 — complete):

- `praReassembleFib` — fiber function for
  FunctorToData
- `praReassembleHom` — fiber morphism function
- `praReassembleObjGr` — Grothendieck object
- `praReassembleMapGr` — Grothendieck morphism
- `praReassembleElemMor` — canonical ElementsPre
  morphism
- `praReassembleElemMor_id/comp` — coherence
- `praReassembleMapGr_id/comp` — functor laws
- `praReassembleGr` — `J ⥤ Grothendieck(...)`,
  the covariant functor
- `praReassemble` — `praReassembleGr.op`, the PRA
- `praReassemble_positions` — round-trip (`rfl`)
- `praReassemble_directions` — round-trip
  (`Functor.hext` + `calc` proof)

PRA Products (Task A1 — in progress):

- `praProdPos` — `Jᵒᵖ ⥤ Type w'`, product
  position presheaf (Pi type)
- `praProdDirAt` — `Iᵒᵖ ⥤ Type (max w' w_I)`,
  Sigma-type direction at each element
- `praProdElemProj` — project product-element
  morphism to factor-element morphism
- `praProdElemProj_id/comp` — preserves
  category structure
- `praProdDir` — `praProdPos.ElementsPre ⥤
  (Iᵒᵖ ⥤ Type (max w' w_I))`, functorial
  direction

Remaining for A1:

- Assemble product PRA via `praReassembleGr.op`
  (needs `w' ≤ w_I` for universe match)
- Define cone projections (product → each factor)
- Prove universal property (lift + uniqueness)
- Package as `HasLimit` for `Discrete K`-shaped
  diagrams

Universe constraint: `K : Type w'` and
`max w' w_I = w_I` (i.e., `w' ≤ w_I`) needed
for the product PRA to live in `PresheafPRACat`.

## Planned Work

### Phase 3: Identity and Composition

See `.session/workstreams/pra-universal-morphisms.md`
for the full plan.

- C1: Identity PRA (terminal positions, Yoneda
  directions)
- C2: Composition via Beck-Chevalley
- C3: PRA factorization `π_! ∘ E^*`

### Phase 4 (remaining): Universal Morphisms

- (Co)limits for `PresheafPRACat I J` via
  underlying presheaf categories, not from
  `CoprodCovarRepCat` (co)limits (which do not
  always exist). A PRA decomposes via
  `FunctorToData` into positions (presheaf on
  base) and directions (presheaf on category of
  elements). Both presheaf categories are
  cocomplete. Pattern from `PolyBetween`:
  - Products: `∀` on positions, `Σ` on
    directions
  - Coproducts: `Σ` on positions, selected
    direction
  - Equalizers: subtype on positions,
    coequalizer on directions
  - Coequalizers: quotient on positions,
    product on directions
  - Principle: positions and directions always
    get dual constructions
- Note: `CoprodCovarRepCat C` does have limits
  (proved in `ccrHasLimit`/`ccrHasLimitsOfShape`)
  but colimits depend on properties of `C`.
  `PresheafPRACat` (co)limits bypass this
- Derive `PresheafPRACat I J` limits/colimits from
  functor-category structure
- Cartesian product, internal hom, Dirichlet product

### Phase 5: Algebras and Coalgebras

- Algebra/coalgebra categories for PRA endofunctors
- Initial algebras (W-types in presheaf categories)
- Terminal coalgebras (M-types)
- Free monads, cofree comonads

### Phase 6: Double Category

- Objects: small categories
- Vertical: functors
- Horizontal: PRAs
- Cells: natural transformations

## Files

| File | Contents |
| ---- | -------- |
| `GebLean/PresheafPRA.lean` | Core definitions, evaluation |
| `GebLean/PresheafPRADiscrete.lean` | Discrete equivalence |
| `GebLean/PresheafPRAUMorph.lean` | Limits (in progress) |
| `GebLean/Utilities/Category.lean` | Cat profunctor, eqToHom utilities |
| `GebLean/Utilities/Families.lean` | op-based CCR, functors, full faithfulness |
| `GebLean/Utilities/Elements.lean` | elementsPrecomp |
| `GebLean/Utilities/Grothendieck.lean` | grothendieckFunctor |
| `docs/presheaf-pra.md` | Concept documentation |

## References

- nLab: parametric right adjoint
- Gambino-Kock: Polynomial functors and polynomial
  monads
- Weber: Polynomials in categories with pullbacks
- Berger-Mellies-Weber: Monads with arities
- `.session/workstreams/pra-universal-morphisms.md`
  (detailed Phase 3-6 plan)
