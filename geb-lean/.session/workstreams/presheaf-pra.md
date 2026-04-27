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
- `praDirectionsAt` — nLab's `E_T`, per-component accessor
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

## Directions-Promotion v2 (2026-04-18; complete 2026-04-25)

Phase 2.5: promoted the per-component directions accessor to an
`(I, J, P)`-natural flat functor `praPolyDirectionsFunctor`
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

**Done (plan tasks 1–11, plus partial Phase 3 — through 2026-04-25):**

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
| `c201d619` | Task 7.1: `ccrNewFamilyFunctor_obj_naturality` |
| `ee49bd58` | Task 7.2: `praPolyDirectionsData_unwidenFiber` |
| `4ab23af6` → reverted by `34a0a36d` | Abandoned `elemMor` helper |
| `83444c84` | Task 7.3 (revised): `praPolyDirectionsData_fibHomCrossUnwidened` |
| `8badaeda` | Task 7.3.5: decouple U3 target Cat universe |
| `86712d19`, `de1de0a3` | Task 7.4: `praPolyDirectionsData_fibHomCrossApp` |
| `2c261288` | Task 7.5: `_fibHomCrossNat_unwidened` (+ aux def) |
| `65475a51` | Task 7.6: `_fibHomCrossNat` (widened, compat lemma) |
| `abb076f3` | Task 7.7: `_baseHomId_unwidened` (`rfl` proof) |
| `57b4cae7` | Task 7.8: `_baseHomId` (widened, three-line proof) |
| `19457465` | Task 7.9: `_baseHomComp_unwidened` (with `_aux`) |
| `5b25263f` | Task 7.10: `_baseHomComp` (widened, `rfl` proof) |
| `bca661f5` | Task 7.11: `praPolyDirectionsData` bundle assembly |
| `4e7824f3` | Task 8: `praPolyDirectionsFunctor` |
| `821da820` | Task 9: three `rfl` bridge lemmas |
| `3b46d8b3` | Task 10: `praPositionsUnwidened` private helper |
| `af370475` | Task 11: rewrite `praPositions` via `praPositionsUnwidened` |

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

**v2 status: Complete (2026-04-25).** All plan tasks 1–22 committed.
The flat functor `praPolyDirectionsFunctor` is the canonical
`(I, J, P)`-natural directions construction. The per-component
accessor `praDirectionsAt` is rewritten directly via
`(ccrNewFamilyFunctor _).obj ((elementsPrecomp P).obj ⟨j, a⟩).unop`
(rfl-equivalent to the deleted intermediate `praDirectionsAtFunctor`
form). The deleted definitions are `praPositionsPresheaf`,
`praDirectionsAtFunctor`, `praDirectionsAtFunctorOp`. Tests live in
`GebLeanTests/Utilities/PresheafPRADirNat.lean`.

**Observations from the 7.4 implementation (preserve for next
session):**

1. **U3 generalization trivial.** Adding a `vT, uT` universe pair and
   changing `G : C ⥤ Cat.{vC, uC}` → `G : C ⥤ Cat.{vT, uT}` (and
   likewise for F) in the `variable` declarations was the only change
   needed; all derived abbrevs, lemmas, and the extractor propagated.
2. **No `eqToHom` glue needed for `fibHomCrossApp`.** The endpoint-
   object equalities turned out to hold on the nose via how `fibFib`,
   `sourceDataHomApp`, and the widening interact.  The plan's "two
   `eqToHom` bookends" skeleton was overkill — the direct definition
   `((ULift.upFunctor ⋙ ULiftHom.up).op).map (fibHomCrossUnwidened f
   (unwidenFiber X₁ . obj x))` compiles without any bookends.
3. **Abbrev-form signature gets stuck on universe unification.**
   Writing `: FunctorBetweenCovContraFibHomCrossApp (functorFromData
   Contra sourceData) praDirectionsTargetFibre ... fibFib ...` causes
   Lean to produce a stuck metavar for F despite F being a specific
   argument.  Workaround: write the signature in the fully-unfolded
   `∀ {X₁ X₂} (f : X₁ ⟶ X₂) (x), ... ⟶ ...` form.  Abbrevs are
   reducible, so Lean will still accept this as the `fibHomCrossApp`
   field of the bundle.  Apply the same workaround to Tasks
   7.6, 7.8, 7.10 (widened coherence lemmas).

**Revision note for Tasks 7.5/7.7/7.9 (unwidened-level coherence
proofs):** Their plan skeletons reference an abandoned
`praPolyDirectionsData_elemMor` helper.  Implementers should adapt by
reading `fibHomCrossUnwidened f e` as
`(ccrNewFamilyFunctor _).map ⟨(homFiber f).app e.fst, rfl⟩` and using
`ccrNewFamilyFunctor`'s `map_id`/`map_comp` directly, without any
`NatTrans.mapElements`-level intermediate.  A cross-cutting note at
the top of Task 7 in the plan spells this out.

**Tasks 12–22 (committed 2026-04-25):**

| Commit | Task |
|--------|------|
| `a701d6c5` | Task 12a: `praPositionsPresheaf` → `praPositionsUnwidened` |
| `772e1c0a` | Task 12b: rewrite `praDirectionsAt` body (rfl-equivalent) |
| `7cdea116` | Task 13: inline `praDirectionsAtFunctor*` in `PresheafPRAUMorph` |
| `15497454` | Task 14: delete the three old definitions |
| `d82bd25d` | Task 15: thread `P` through accessors; drop section variable |
| `ffab612d` | Task 16: type-signature sanity tests |
| `7665fead` | Task 17: register `PresheafPRADirNat.lean` |
| `1674aa5f` | Task 18: bridge-lemma collapse tests (un-privates `…Data`) |
| `cc3a397e` | Task 19: pointwise-accessor compatibility tests |
| `c66ec987` | Task 20: functoriality tests |
| `3b23d7cb` | Task 21: universe-polymorphism tests |

**Follow-ups (committed 2026-04-25):**

| Commit | Follow-up |
|--------|-----------|
| `b576efe3` | Tighten `maxHeartbeats` to 400000 (Task 7.9 helpers) |
| `23020778` | Refactor `catULiftFunctor` as `catULiftFunctor2` specialization |
| `f80c2523` | Narrow `uliftCategory` scope to `PresheafPRAAccessors` |
| `ed74a7ff` | Add public `praPolyDirectionsAtSourceObj` helper |
| `b9daaca3` | Add `@[simp] praDirectionsAt_via_praPolyDirectionsFunctor` |

The bridge theorem closed by `rfl` — required explicit universe
annotations on `ULift.down` and `ULiftHom.objDown` to avoid
metavariables.

## praEval Naturality (in progress, 2026-04-26)

Goal: lift `praEvalAtFunctor` to a flat-functor-between-
Grothendiecks form `praPolyEvalFunctor` natural in `(I, J)`,
mirroring `praPolyDirectionsFunctor` in spirit but with inverted
source-side variance.

Spec: `docs/superpowers/specs/2026-04-26-praEval-naturality-design.md`
(gitignored).
Plan: `docs/superpowers/plans/2026-04-26-praEval-naturality.md`
(gitignored).

**Done so far (10 commits):**

| Commit | Phase / Task |
|--------|--------------|
| `81a0369f` | Task 1: `praEvalTargetFibre` (initial) |
| `f9859d89` | Task 2: `praPolyEvalTarget` |
| `21a625f7` → `4203253f` | Task 3 first attempt (reverted) |
| `64162066` | Task A1: `FunctorBetweenContraContra` abbrevs |
| `774ee96e` | Task A2: `FunctorBetweenContraContraData` |
| `d9d08504` | Task A3: `…Data.toFunctor` extractor |
| `46923c37` | Tasks 3+4 (revised): source side |
| `f0f1f208` | Task 8: `praPolyEvalData_baseFib` |
| `d789a2ac` | Fix: drop `Cat.opFunctor` from target fibre |
| `d701b401` | Task 9: `praPolyEvalData_fibFib` |

## praEvalAtI Naturality (in progress, 2026-04-26)

Goal: define `praPolyEvalAtINatTrans` and `praPolyEvalAtIFunctor`
— the I-fixed J-natural evaluation, forming the source-side
fibre functor for the Grothendieck-construction-based
`praPolyEvalAtIFunctor`.

Spec: `docs/superpowers/specs/2026-04-26-praEvalAtI-naturality-design.md`
(gitignored).
Plan: `docs/superpowers/plans/2026-04-26-praEvalAtI-naturality.md`
(gitignored).

**Done:**

| Commit | Task |
|--------|------|
| `93b25d60` | Task 0: revert in-flight source-side |
| `f0f1f208` | Task 1: `praEvalAtBifunctor` |
| `46923c37` | Task 3: `praPolyEvalAtISource` |
| `b8ffe6b7` | Tasks 2+4: `praPolyEvalAtISourceFib` (fix I-arg) + `praPolyEvalAtINatTrans` (with `praEvalAtBifunctorCat` helper) |

**Key design facts (preserve for next session):**

- `praPolyEvalAtISourceFib I opJ` uses
  `Opposite.op (Cat.of (↑I)ᵒᵖ)` (not `Opposite.op I`) as the
  I-argument to `presheafPRACatBifunctor.flip`, giving
  contravariant presheaves.
- `praEvalAtBifunctor` takes TYPE-level `I J` and produces
  `PresheafPRACat I J × PSh(I) ⥤ Jᵒᵖ ⥤ Type`, which does NOT
  match the Cat-object-parameterized types in the fibre functor.
  Resolution: `praEvalAtBifunctorCat I opJ` builds the same
  functor using `Functor.uncurry.obj ((whiskeringRight ↑opJ.unop
  _ _).obj (ccrNewEvalCatFunctor PSh(↑I)) ⋙ Functor.flipping.functor)`;
  this matches definitionally.
- Naturality proof reduces to `rfl`.

**Outstanding tasks (13 remaining of 17):**

- Task 5: `praEvalAtBifunctorCat_natural` bridge lemma
- Task 6: `praPolyEvalAtIFunctor` (Grothendieck construction)
- Task 7: access lemmas
- Tasks 8–17: tests + workstream notes

**Two design pivots during execution:**

1. **Variance flip (commit `4203253f` revert + Phase A
   commits)**: the original plan used the existing
   `FunctorBetweenCovContra` framework with a covariant source
   Grothendieck.  This was rejected: presheaves are
   contravariant in `I`, so `Z`'s natural variance under an
   `I`-morphism is BACKWARD, forcing the source Grothendieck to
   be CONTRAVARIANT in `(J, I, P)`.  Resolution: built new U3
   framework `FunctorBetweenContraContra` (Phase A), used it
   for praEval.
2. **Target `Cat.opFunctor` removal (commit `d789a2ac`)**: the
   original `praEvalTargetFibre` mirrored
   `praDirectionsTargetFibre`'s three-stage pipeline including
   `Cat.opFunctor`.  This was rejected: polynomial-functor
   *evaluation* is COVARIANT in `Z`, so the result-side variance
   matches presheaves' natural contravariance directly.
   Resolution: dropped the final `Cat.opFunctor` stage; the
   target fibre is now `presheafCatFunctor ⋙
   catULiftFunctor2` (two-stage).

**Outstanding tasks (10 remaining):**

- Task 10: `praPolyEvalData_fibHomCrossUnwidened` (cross-fibre
  morphism, unwidened).
- Task 11: `praPolyEvalData_fibHomCrossApp` (widened, with
  target-side `x'` input — note the ContraContra
  `FibHomCrossApp` shape differs from CovContra; see
  `Utilities/Grothendieck.lean` for the abbrev).
- Task 12: `praPolyEvalData_fibHomCrossNat` (naturality).
- Task 13: `praPolyEvalData_baseHomId` (identity coherence).
- Task 14: `praPolyEvalData_baseHomComp` (composition
  coherence).
- Task 15: `praPolyEvalData` bundle assembly.
- Task 16: `praPolyEvalFunctor` via
  `FunctorBetweenContraContraData.toFunctor`.
- Task 17: three `rfl` bridge lemmas.
- Task 18: `praPolyEvalAtSourceObj` helper.
- Task 19: `praEvalAtFunctor_via_praPolyEvalFunctor` bridge
  theorem + test (via simp).
- Tasks 20–25: tests + workstream notes.

**Proof-engineering notes for the remaining tasks
(preserve for next session):**

- The new `FunctorBetweenContraContra` framework's
  `FibHomCrossApp` takes a TARGET-side input `x' : G.obj (op c')`
  rather than CovContra's source-side input.  The cross-fibre
  morphism shape is
  `(fibFib c).obj ((G.map f.op).toFunctor.obj x') ⟶
   (F.map (baseFib.map f).op).toFunctor.obj
     ((fibFib c').obj x')`.
  See `FunctorBetweenContraContraFibHomCrossApp` in
  `Utilities/Grothendieck.lean` (commit `64162066`).
- The framework includes an extra helper not in CovContra:
  `FunctorBetweenContraContraGMapCompEq` /
  `…GMapCompEqProof` — needed because the contravariant source's
  composition coherence requires equating `(G.map f.op) ∘
  (G.map g.op)` with `G.map (f≫g).op`.  This affects the shape
  of `BaseHomComp` and may matter for Task 14.
- The praDirections analog `praPolyDirectionsData_baseHomComp`
  (Task 7.10) closed by `rfl` end-to-end.  It's plausible the
  praEval analog also closes by `rfl` given the structural
  parallel.  Same for `baseHomId` (Task 7.8 → praEval Task 13).
- Task 11 (`fibHomCrossApp` widened) is the most likely place
  for further design subtleties.  The polynomial-functor-
  morphism action `homFiber f : objFiber c ⟶ (presheafPRACat
  Bifunctor.map (homBase f).op).obj (objFiber c')` provides the
  natural transformation between polynomial functors at
  different `P`'s; the cross-fibre app should encode the
  resulting natural transformation between evaluations.
- The fibFib body uses `Functor.whiskeringRight ⋯ |>.flip`
  inline (NOT `praEvalAtFunctor`, because that's defined later
  in the file).  Future tasks may want to refer to this body
  shape — see commit `d701b401`.
- Universe annotations: `praEvalTargetFibre` now uses
  `presheafCatFunctor.{u_J, v_J, max w' u_I w_I}` (not just
  `w'`) to absorb `ccrNewEvalCatFunctor`'s output universe
  inflation.  `praPolyEvalTarget`'s outer Cat universe was
  correspondingly bumped to include `(u_I + 1)`.

**Proof-engineering lessons accumulated across the workstream
(preserve across sessions):**

- **2026-04-25 (Tasks 7.5–7.10) — surprises in the unwidened
  layer.** Tasks 7.7 and 7.10 closed by `rfl` with no tactic
  scaffolding; Task 7.6 reduced to a one-line `rfl` structural
  compat lemma plus a six-tactic naturality proof; Task 7.10's
  widened composition coherence is `rfl` end-to-end. The key
  observation: at the unwidened level, `homFiber f` (built from
  `f.unop.fiber.unop`) decomposes definitionally through
  `Grothendieck.id_fiber`/`comp_fiber` plus the `(homFiber f).app`
  pointwise application. Tactic engineering is needed only at the
  unwidened naturality step (Task 7.5) and at
  `_target_widening_compat` (Task 7.6).
- **2026-04-25 (Task 7.6) — structural compat lemma pattern.**
  `(praDirectionsTargetFibre.map h.op).toFunctor.map ∘
  widening.op.map = widening.op.map ∘
  (presheafCatFunctor.map h.op).toFunctor.op.map` holds by `rfl`.
  The lemma serves as a named rewrite handle; the proof itself is
  trivial. The companion `Families.lean` change un-privates
  `ccrNewFamilyFunctor_naturality` for use in the widened
  naturality proof.
- **2026-04-25 (Task 7.9) — `set_option maxHeartbeats 800000`
  required by linter.** When elevating heartbeats above the
  default 200000, the project's `linter.style.maxHeartbeats`
  rejects the option without an explanatory comment immediately
  above. The smallest sufficient value for Task 7.9 is 400000
  (per code-review measurement); the committed version uses
  800000 and could be tightened in a follow-up cleanup pass.
- **2026-04-25 (Task 12) — definitional-equality cliff at the
  accessor migration.** The new `praDirectionsAt` form (built via
  `praPolyDirectionsFunctor.obj` + an `unwiden` helper) is only
  propositionally equal to the old `(praDirectionsAtFunctor _).obj
  (op ⟨j, a⟩)`. Downstream `PresheafPRAUMorph.lean` proofs
  (`praReassemble_directions`, cofan/coprod constructions) rely
  on the old definitional collapse. The migration must batch
  Tasks 12 and 13 together (or introduce a propositional bridge
  lemma) — see "Outstanding plan tasks (12–22)" above for the
  three candidate paths forward.
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
