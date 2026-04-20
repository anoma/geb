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
- `praPositionsNat` — positions as functor
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

- `praProd` — assembled product PRA via
  `praReassemble`
- `praProdSigmaInj` — Sigma injection
  (direction embedding, naturality = rfl)
- `praProdProjAt` — CCR-level projection
  at each stage (positions by evaluation,
  directions by Sigma injection)
- `praProdProj` — full projection natural
  transformation (`erw [unop_comp]` proof)
- `praProdLiftAt` — CCR-level lift from a
  cone; base tuples projections, fiber
  Sigma-eliminates
- `praProdLiftAt_fac` — factorization:
  `liftAt ≫ projAt = (s.proj k).app j`
  (`erw [unop_comp]` proof)
- `praProdLift` — full lift natural
  transformation (sorry in fiber naturality)

Task A1 complete. All definitions compile
without sorry or warnings.

PRA Coproducts (Task A2 — in progress):

- `praCoprodPos` — `Jᵒᵖ ⥤ Type w'`, Sigma
  position presheaf
- `praCoprodDirAt` — direction at `⟨k, a⟩`
  is just the k-th direction
- `praCoprodElemFstEq` — Sigma index
  preservation by morphisms
- `praCoprodDir` — direction functor
  (`map_id` done, `map_comp` sorry)
- `praCoprod` — via `praReassemble`
- `praCoprodInjAt` / `praCoprodInj` —
  injection (`erw [unop_comp]`)
- `praCoprodDescAt` / `praCoprodDesc` —
  descent
- `praCoprodDescAt_fac` — beta rule
  (`erw [unop_comp]`)
- `praCoprodMorphExt` — eta rule
  (`rcases; subst; Grothendieck.congr`)
- `praCoprodDesc_naturality` — via `calc`
  through interface
- `praCoprodCofan` / `praCoprodIsColimit` /
  `praHasCoproduct` — full universal property

Task A2 complete. All definitions compile
without sorry or warnings.

Universe: `K : Type` (universe 0) avoids
`Small`/`ULift`. `max 0 w' = w'` and
`max 0 w_I = w_I` hold syntactically.

Proof technique notes:

- CCR morphism equality: use
  `Quiver.Hom.unop_inj` +
  `Grothendieck.ext` (base + fiber)
- Grothendieck base in `(Type w')ᵒᵖ`:
  use `Quiver.Hom.unop_inj` to get Type-level
  function equality, then `funext` + `rfl`
- Grothendieck fiber: has `eqToHom` from
  `Grothendieck.ext`; use `erw` chains with
  `unop_comp`, `comp_fiber`, `comp_val`,
  `eqToHom_unop`, `eqToHom_val` and
  `change .val` to expose `Subtype.val`
- For naturality of projection: the base
  direction is Grothendieck.ext's SECOND goal
  (not first), fiber is FIRST

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

## Directions-Promotion v2 (2026-04-18)

Phase 2.5 (currently in progress at design time): promote
`praDirectionsAtFunctor*` to an `(I, J, P)`-natural flat functor
encoding polynomial-functor-morphism structure (forward on
positions, backward on directions).

### v1 attempt (abandoned; artifacts reusable)

Tried a nat-trans between two `FunctorFromData`-packaged functors.
Blocked twice:

1. Covariant Grothendieck + covariant `FunctorFromData`: source-side
   direction mismatch — elements are contravariant under base
   precomposition in J.
2. Contravariant Grothendieck + `FunctorFromDataContra` (U1/U2
   ported): target-side direction mismatch — `presheafCatFunctor`
   is inherently contravariant in I, no covariant sibling without
   left Kan extension.

Reusable v1 commits (all currently on `terence/grothendieck`):

- `a7574b89` — `presheafPRACatBifunctorUncurried` (base for flat
  source/target construction).
- `19cae701` — U1: `FunctorFromDataContra` infrastructure in
  `Utilities/Grothendieck.lean`.
- `ef8ace94` — U2: `NatTransFromDataContra` infrastructure (not
  used by v2, but valuable standalone).
- `c0468683` — `sourceData` (becomes part of v2's source-total
  Grothendieck).

### v2 design

Flat functor between Grothendiecks, encoding polynomial-functor
morphisms (forward on positions, backward on directions):

- `praPolyDirectionsSource` — covariant Grothendieck of
  `functorFromDataContra sourceData`.  Objects: 4-tuples
  `((J, I), P, element)`.
- `praPolyDirectionsTarget` — `(grothendieckContraFunctor
  Cat.{v_I, u_I}).obj praDirectionsTargetFibre`.  Objects: pairs
  `(I, op_presheaf_on_I)`.  The outer `.op` (at the fibre) encodes
  the backward-on-directions convention.
- `praDirectionsTargetFibre : Cat.{v_I, u_I}ᵒᵖ ⥤ Cat.{…}` —
  three-stage pipeline: `presheafCatFunctor ⋙ catULiftFunctor2 ⋙
  Cat.opFunctor`.  The input Cat already carries the `Iᵒᵖ`
  convention inherited from `presheafPRACatBifunctorUncurriedOp`'s
  base (`(objBase X).2 = Cat.of Iᵒᵖ`), so no additional inner
  op-stage is required; the outer `Cat.opFunctor` encodes
  backward-on-directions for polynomial-functor-morphisms.
- `praPolyDirectionsFunctor` — the main flat functor, built via
  a new utility `FunctorBetweenCovContra` (U3) that mirrors
  `FunctorBetween`'s shape for the mixed covariant-source /
  contravariant-target case.

Spec: `docs/superpowers/specs/2026-04-18-praDirections-naturality-design-v2.md`.
(v1 spec at `2026-04-18-praDirections-naturality-design.md` is
superseded.)

### Known follow-ups (not blocked by Phase 2.5)

- Task #397 — refactor `catULiftFunctor` as specialization of
  `catULiftFunctor2`.
- Task #398 — narrow `uliftCategory` local-instance scope in
  `PresheafPRA.lean`.
- Dirichlet-functor-morphism parallel (forward-on-directions) — a
  distinct, meaningful construction, separate spec if/when wanted.
- `praEvalAt*` promotion — deferred until `praDirections` lands.

### v2 Progress (current, as of 2026-04-20)

All commits on `terence/grothendieck`.  Plan at
`docs/superpowers/plans/2026-04-19-praDirections-naturality-v2.md`
(gitignored).  Spec at
`docs/superpowers/specs/2026-04-18-praDirections-naturality-design-v2.md`
(gitignored).  `lake build` and `lake test` are clean at HEAD.

**Done (plan tasks 1–6, plus partial Task 7):**

| Commit | Task |
|--------|------|
| `b8fef801` | Task 1: `FunctorBetweenCovContra` abbrevs (U3 part 1) |
| `5d26d36b` | Task 2: `FunctorBetweenCovContraData` structure (U3 part 2) |
| `04882518`, `2219249a` | Task 3: `.toFunctor` extractor (U3 part 3) |
| `37b8858d` | Task 4: `praDirectionsTargetFibre` |
| `b0dbd50e` | Task 5: `praPolyDirectionsTarget` |
| `42c75e74` | Task 6: `praPolyDirectionsSource` |
| `aad59f52` | Task 7 helper: `praPolyDirectionsData_baseFib` |
| `0753fd6a` | Pipeline revision: drop inner `Cat.opFunctor.op` |
| `62b18098` | Task 7 helper: `praPolyDirectionsData_fibFib` |

**Deviations from original plan (both intentional, implemented
and committed):**

1. `praPolyDirectionsTarget` and `praPolyDirectionsSource` Cat
   universes widened from the plan's annotations to include
   `(u_I + 1)`, `(v_I + 1)`, `(u_J + 1)`, `(v_J + 1)` where
   required.  `grothendieckContraFunctor` sees `Cat.{v_I, u_I}`
   itself as a type, forcing these +1 levels into the obj-level
   universe.
2. `praDirectionsTargetFibre` pipeline is three-stage
   (`presheafCatFunctor ⋙ catULiftFunctor2 ⋙ Cat.opFunctor`) —
   the plan's inner `Cat.opFunctor.op` was dropped.  Reason: the
   input Cat coming in from `(objBase X).2` already carries the
   `Iᵒᵖ` convention of `presheafPRACatBifunctorUncurriedOp`, so
   the extra op over-applied and landed at `Iᵒᵖᵒᵖ ⥤ Type` rather
   than `Iᵒᵖ ⥤ Type`.  The spec at lines 55–59 and 173–192 now
   reflects the three-stage form.

**Outstanding Task 7 work (remaining helpers + bundle):**

1. `praPolyDirectionsFibHomCrossApp` — the morphism-level
   connecting map.  Endpoints are
   `op (widened (ccrNewFamily (P₁.obj j) a))` on one side and a
   transport through `presheafCatFunctor.map g.op` of
   `op (widened (ccrNewFamily (P₂.obj (f_J.obj j)) ...))` on the
   other.  Key building block:
   `ccrNewFamilyFunctor_naturality` at
   `GebLean/Utilities/Families.lean:3436`.
   `sourceData_base_change_eq` (rfl, in `PresheafPRA.lean:208`)
   preserves `ccrNewIndexFunctor` on the nose across the J-side
   transport.
2. `praPolyDirectionsData_fibHomCrossNat` — naturality of the
   above in the element morphism.
3. `praPolyDirectionsData_baseHomId` — collapse at identity base
   morphism.
4. `praPolyDirectionsData_baseHomComp` — composition coherence.
5. The `praPolyDirectionsData : FunctorBetweenCovContraData …`
   struct literal plugging in all six helpers.

Recommended approach (next session): write the *unwidened* form
of `fibHomCrossApp` first, bridging `elementsPrecomp P ⋙
ccrNewFamilyFunctor` to `ccrNewFamilyNat.app` on widened elements.
Then widen via functoriality of `catULiftFunctor2 ⋙
Cat.opFunctor`.  Task 3's nine-lemma decomposition is the scope
template; expect similar count for each of (1)–(4).

**Outstanding plan tasks after Task 7 completes (tasks 8–22):**

- Task 8: `praPolyDirectionsFunctor :=
  FunctorBetweenCovContraData.toFunctor praPolyDirectionsData`.
- Task 9: three `rfl` bridge lemmas
  (`praPolyDirectionsFunctor_base`, `_fibre`, `_map_app`).  Fall
  back to `simp only` with data-bundle unfolds if `rfl` misses.
- Task 10: rename old `praPositionsPresheaf` →
  `praPositionsUnwidened` (private helper, body unchanged).
- Task 11: rewrite `praPositions` via `praPositionsUnwidened`.
- Task 12: rewrite `praDirectionsAt` via a helper
  `praPolyDirectionsAtSourceObj` and the flat functor.
- Task 13: migrate `PresheafPRAUMorph.lean`'s
  `praReassemble_directions` proof (lines 1230–1310) away from
  the soon-to-be-deleted names.
- Task 14: delete `praDirectionsAtFunctorOp`,
  `praDirectionsAtFunctor`, `praPositionsPresheaf`.
- Task 15: remove `variable (P : PresheafPRACat …)` at
  `PresheafPRA.lean:459`; thread `P` through accessors; audit
  `variable (I …)`/`(J …)`.
- Tasks 16–17: create and register
  `GebLeanTests/Utilities/PresheafPRADirNat.lean`.
- Tasks 18–21: four concrete tests (bridge-lemma collapse,
  pointwise-accessor compatibility, functoriality at a morphism,
  universe polymorphism).
- Task 22: mark this workstream section Complete and clean stale
  references to deleted names.

**Proof-engineering lessons accumulated across the workstream
(preserve across sessions):**

- `ULiftHom.down`'s `C` argument is unsolvable from a
  `Cat.of`-coerced expression.  Fix: prefix the offending
  functor composition with
  `show ULiftHom (ULift _) ⥤ _ from …` to pin the input type.
- `rw` of `(g ≫ h).unop.base = h.unop.base ≫ g.unop.base`
  triggers motive-not-type-correct because other sub-terms
  depend on the rewritten form.  Fix: rewrite the dependent
  sub-term first via a helper like `fibFib_map_comp_fiber`, then
  proceed.
- `rw` does not match `data.fibHomCrossApp f g x` against a goal
  that renders as `(fun {c c'} ↦ data.fibHomCrossApp) f g x`
  after abbrev-implicit expansion.  Fix: `conv_lhs => rw [show
  LHS = RHS from data.baseHomComp …]` with the fully-resolved
  RHS spelled out in the `show`.
- The fused-vs-split `F.map`-transport identity collapses via
  `Functor.congr_hom hF` where `hF : F.map fused.toFunctor =
  F.map A.toFunctor ⋙ F.map B.toFunctor`, proven by
  `rw [baseFib.map_comp, op_comp, F.map_comp]; rfl`.
- `show` with goal-changing intent triggers a lint warning; use
  `change` instead.
- Universe parameters for `catULiftFunctor2` and `Cat.opFunctor`
  bind in declaration order (`u, v, w_v, w_u` for
  `catULiftFunctor2`; `v, u` for `Cat.opFunctor`) — not in the
  order they appear inside `Cat.{v, u}` annotations.  Mirror the
  order already used by `praPositionsNatTarget` in
  `PresheafPRA.lean:412-420`.

## References

- nLab: parametric right adjoint
- Gambino-Kock: Polynomial functors and polynomial
  monads
- Weber: Polynomials in categories with pullbacks
- Berger-Mellies-Weber: Monads with arities
- `.session/workstreams/pra-universal-morphisms.md`
  (detailed Phase 3-6 plan)
