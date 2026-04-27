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

## praEvalAtI Naturality (complete, 2026-04-26)

Goal: lift `praEvalAtFunctor I J` to a flat-functor-between-
Grothendiecks form `praPolyEvalAtIFunctor` natural in `(J, P, Z)`
at fixed `I`, built as `(grothendieckContraFunctor Cat).map` of a
NatTrans between two `Catᵒᵖ ⥤ Cat` functors.

Spec:
`docs/superpowers/specs/2026-04-26-praEvalAtI-naturality-design.md`
(gitignored).
Plan: `docs/superpowers/plans/2026-04-26-praEvalAtI-naturality.md`
(gitignored).

The `(I, J)`-naturality variant is deferred to a separate
workstream.  See "Earlier (I, J)-natural attempt" below for why.

### Done

| Commit | Task |
|--------|------|
| `c2672b92` | Task 0: revert in-flight (I, J)-natural source side |
| `08f9b229` | Task 1: `praEvalAtBifunctor` (uncurried form) |
| `12d1be41` | Task 2: `praPolyEvalAtISourceFib` (initial; bug) |
| `5ec0e850` | Task 3: `praPolyEvalAtISource` |
| `b8ffe6b7` | Task 2 fix + Task 4: NatTrans (private helpers) |
| `44bcb90f` | Task 5: `praPolyEvalAtIFunctor` |
| `dcea57fd` | Task 6: three rfl bridge lemmas |
| `02fa0387` | Task 7: `praPolyEvalAtISourceObj` (private helper) |
| `4469b38a` | Task 8: bridge theorem `..._via_praPolyEvalAtIFunctor` |
| `5db45870` | Task 9: create `PresheafPRAEvalAtINat.lean` |
| `6b744c12` | Task 10: register test file |
| `22185830` | Task 11: bridge-lemma collapse tests |
| `25f3cb49` | Task 12: pointwise-accessor compatibility tests |
| `4e046146` | Task 13: functoriality tests |
| `e41b197c` | Task 14: universe polymorphism tests |
| `e3099779` | Task 15: bridge-theorem test (via `simp`) |

### Design notes (preserve for next session)

- `praPolyEvalAtISourceFib I` uses
  `Opposite.op (Cat.of (↑I)ᵒᵖ)` (matching the convention of
  `presheafPRACatFunctor`).  Earlier `Opposite.op I` was a bug;
  fixed in `b8ffe6b7`.
- `praEvalAtBifunctor` (Task 1) is parameterised by *type-level*
  `I J` and uses them inside via `PresheafPRACat I J`.  Lean's
  definitional reduction does not bridge this with the
  *Cat-object-level* parameters in the fibre functor.  Resolution:
  the private helper `praEvalAtBifunctorCat I opJ` (introduced in
  `b8ffe6b7`) builds the same functor using
  `Functor.uncurry.obj ((whiskeringRight ↑opJ.unop _ _).obj
   (ccrNewEvalCatFunctor PSh(↑I)) ⋙ Functor.flipping.functor)`;
  this matches Cat-object-level types definitionally.  The public
  `praEvalAtBifunctor` remains as a public-API artifact.
- The source fibre Cat at `op J` is doubly widened
  (`ULiftHom (ULift (PRACat × ULiftHom (ULift PSh(I))))`): the
  `pshCatW` factor is widened separately for `toCatHom` to apply
  to the product Cat-morphism, and the outer `lift` widens the
  full product into the target Cat universe.  The
  `praPolyEvalAtINatTrans_app` private helper (in `b8ffe6b7`)
  uses a `show ⥤ from` cast and `(Functor.id _).prod (ULiftHom
  .down ⋙ ULift.downFunctor)` to navigate this two-layer
  unwidening.
- All naturality and bridge proofs close by `rfl`; the bridge
  theorem (Task 8) closed by `rfl` after explicit
  `ULift.down`/`ULiftHom.objDown` annotations on the RHS type.
- `ULift.down` (not `CategoryTheory.ULift.down`) is the right
  identifier in RHS type annotations; the latter does not resolve.
- The `|>.obj Z` syntax does not parse cleanly in theorem-type
  position when nested with parens; use `(_.obj Z)` flattened
  on a single line.

### Earlier (I, J)-natural attempt (abandoned)

Before scoping down to fixed `I`, an attempt was made to make the
construction natural in `(I, J)` simultaneously.  This attempt
spanned commits `81a0369f` through `d701b401`, with the source
side reverted by `c2672b92`.  The kept artifacts from that
attempt are:

- `praEvalTargetFibre`, `praPolyEvalTarget` (target Grothendieck;
  parametrised only by `J`, reusable as-is — commits `81a0369f`,
  `f9859d89`, `d789a2ac`).
- `FunctorBetweenContraContra` framework in
  `Utilities/Grothendieck.lean` (general infrastructure parallel
  to `FunctorBetweenCovContra`; useful regardless — commits
  `64162066`, `774ee96e`, `d9d08504`).

The attempt hit a variance mismatch in the framework's cross-
fibre map: the source endpoint involves `Hom_{PSh(I_source)}`
while the target endpoint involves `Hom_{PSh(I_target)}`, related
by the *forward whisker* `Hom_{PSh(I_target)} ↪ Hom_{PSh
(I_source)}`.  This whisker goes from target into source —
opposite of what the framework's `FibHomCrossApp` shape requires.
Investigation showed:

1. Adding `Cat.opFunctor` to the target fibre would fix the
   I-variation case but reintroduce a Z-covariance violation in
   the pure-Z-variation case.
2. Redesigning the target Grothendieck (e.g., a covariant
   Grothendieck or an extended fibre) does not produce a clean
   flat functor — the natural construction yields a *span*
   `praEvalAt P_t Z_t (J-pulled) ↪ middle ← praEvalAt P_s Z_s`
   with no canonical arrow in either direction.

Conclusion: `praEvalAt`'s `(I, J)`-naturality is genuinely lax —
J-naturality is strict but I-naturality is up-to-inclusion via
the forward whisker.  A flat functor between two single-level
Grothendiecks cannot capture both Z-covariance at fixed `I` and
I-pullback-via-whisker simultaneously.  The user's plan: use the
fixed-`I` formula (now built) as a concrete reference for a
later workstream that designs the appropriate `I`-natural
object.  Possibilities to explore: paranatural transformation
between two-variance-in-`I` functors, lax-natural infrastructure,
or restricted-source-mor conventions.

### Follow-up: (I, J)-naturality (deferred)

A separate brainstorm/design session will use the concrete
fixed-`I` formula above to design the appropriate `I`-natural
object.  Directions to consider include paranatural
transformations between two-variance-in-`I` functors, 2-cells
between pseudofunctors, profunctor-style natural transformations
capturing lax `I`-naturality, or restriction of source-mors to
those with fully faithful or equivalence `f_I`.

## References

- nLab: parametric right adjoint
- Gambino-Kock: Polynomial functors and polynomial
  monads
- Weber: Polynomials in categories with pullbacks
- Berger-Mellies-Weber: Monads with arities
- `.session/workstreams/pra-universal-morphisms.md`
  (detailed Phase 3-6 plan)
