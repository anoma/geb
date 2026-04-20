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
  `Cat.opFunctor.op ⋙ presheafCatFunctor ⋙ catULiftFunctor2 ⋙
  Cat.opFunctor`.  Two higher-order op's around `presheafCatFunctor`.
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

### v2 Progress (2026-04-19 session, partial — U3 utility done)

Plan tasks 1-6 complete, Task 7 partial.  Plan tasks 8-22 remain.
All commits on `terence/grothendieck`.

**Task 7 state (2026-04-19, second session):**

- `praPolyDirectionsData_baseFib` is in place (commit `aad59f52`).
- `praDirectionsTargetFibre` pipeline revised to drop the inner
  `Cat.opFunctor.op` stage (commit `0753fd6a`), so
  `praDirectionsTargetFibre.obj (op (Cat.of Iᵒᵖ))` now yields
  `op (widened (Iᵒᵖ ⥤ Type w_I))` matching `sourceDataFib`.
- `praPolyDirectionsData_fibFib` is in place (commit `62b18098`) as
  `ULiftHom.down ⋙ ULift.downFunctor ⋙ elementsPrecomp P ⋙
  ccrNewFamilyFunctor (presheafCat I) ⋙
  (ULift.upFunctor ⋙ ULiftHom.up).op`.  The `show` cast at the
  front explicitly pins the input type to
  `ULiftHom (ULift ((P ⋙ ccrNewIndexFunctor _).Elements))` so
  `ULiftHom.down`'s implicit arg is inferred; without this cast
  typeclass search fails on `Category ↑((functorFromDataContra
  sourceData).obj X)`.

**Remaining Task 7 (fibHomCrossApp + three coherences):**

- `fibHomCrossApp f x` is a morphism in `(widened (I₁ᵒᵖ ⥤ Type
  w_I))ᵒᵖ` from `(fibFib X₁).obj x` to
  `(praDirectionsTargetFibre.map (baseFib.map f).op).obj
  ((fibFib X₂).obj (fFromData.map f x))`.  The two sides are not
  definitionally equal: the LHS is `op (widened (ccrNewFamily of
  (elementsPrecomp P₁ x')))` while the RHS wraps a transport of
  `op (widened (ccrNewFamily of (elementsPrecomp P₂ (f.map x))))`
  through `presheafCatFunctor.map g.op` (where `g := baseFib.map f
  : I₁ ⟶ I₂`).
- The natural building block is `ccrNewFamilyNat.naturality`
  (`GebLean/Utilities/Families.lean:3484`).  On
  `F := presheafCatFunctor.map g.op : presheafCat I₂ ⟶
  presheafCat I₁`, it equates
  `ccrElementsFunctor.map F ⋙ ccrNewFamilyNat.app (presheafCat I₁)`
  with `ccrNewFamilyNat.app (presheafCat I₂) ⋙
  ccrNewFamilyNatTarget.map F`.  But our chain is
  `elementsPrecomp P ⋙ ccrNewFamilyFunctor _`, not directly
  `ccrElementsFunctor`; plugging `ccrNewFamilyNat.naturality` into
  the widened chain requires an intermediate lemma relating
  `elementsPrecomp (P : J ⥤ CCR _)` composed with
  `ccrNewFamilyFunctor` to `ccrNewFamilyNat.app`-application on
  an element obtained by widening.
- The `fibHomCrossNat`, `baseHomId`, `baseHomComp` proofs each
  reduce to multiple small lemmas about how the widening
  `(ULift.upFunctor ⋙ ULiftHom.up).op` commutes with naturality and
  how `ccrNewFamilyNat`'s identity/composition coherence lifts
  through the widening.  Task 3's nine small lemmas give a
  template; expect similar count here.
- Recommended next-session approach: (1) write the unwidened
  version of `fibHomCrossApp` first as a component of
  `ccrNewFamilyNat.naturality` on the `elementsPrecomp`-reindexed
  input, then (2) widen by applying the ULift/ULiftHom up functors
  in `op`.  Factor out one private def for each of the three
  coherence proofs as in Task 3.

**Proof-engineering note (carry over for next session):**

- `show T from body` is necessary (not `body : T`) to pin a
  `Cat`-coerced input type to an explicit `ULiftHom (ULift _)`
  form.  Without this `ULiftHom.down`'s `C` argument is unsolvable
  from `↑(Cat.of _)`.
- The pipeline works with `ULiftHom.down ⋙ ULift.downFunctor` as
  the unwidening inverse of `catULiftFunctor2` (mirrors
  `sourceDataHomApp`'s widened `elementsPrecomp` pattern).

**Done (U3 utility, `GebLean/Utilities/Grothendieck.lean`):**

- `b8fef801` — Task 1: `FunctorBetweenCovContra` abbrevs
  (`FunctorBetweenCovContraBaseFib`, `FunctorBetweenCovContraFibFib`,
  `FunctorBetweenCovContraFibHomCrossApp`,
  `FunctorBetweenCovContraFibHomCrossNat`,
  `FunctorBetweenCovContraBaseHomEqId`,
  `functorBetweenCovContraBaseHomEqIdProof`,
  `FunctorBetweenCovContraBaseHomEqComp`,
  `functorBetweenCovContraBaseHomEqCompProof`,
  `FunctorBetweenCovContraBaseHomId`,
  `FunctorBetweenCovContraBaseHomComp`).  At line ~5137 of
  `Grothendieck.lean`, immediately after `end FunctorBetweenContra`.
- `5d26d36b` — Task 2: `FunctorBetweenCovContraData` structure (same
  section).
- `04882518` and `2219249a` — Task 3: the `toFunctor` extractor.

**Task 3 factoring (all in `Grothendieck.lean`, inside new
`section FunctorBetweenCovContraExtractor` at line ~7370, after the
`GrothendieckContraFunctor` namespace since it uses
`mkObj`/`mkHom`/`objBase`/`objFiber`):**

- `FunctorBetweenCovContraData.toBaseFunc`: `(Grothendieck G)ᵒᵖ ⥤ Dᵒᵖ` =
  `Grothendieck.forget G).op ⋙ data.baseFib.op`.
- `FunctorBetweenCovContraData.toFib`: object fibre =
  `op ((fibFib X.unop.base).obj X.unop.fiber)` in `(F ⋙ Cat.opFunctor).obj _`.
- `FunctorBetweenCovContraData.toHomUnop`: pre-op fibre morphism =
  `fibHomCrossApp g.unop.base Y.unop.fiber ≫ (F.map _).map ((fibFib
  X.unop.base).map g.unop.fiber)`.
- Identity-side lemmas: `toHomUnop_id_fst`, `toHomUnop_id_snd`,
  `toHomUnop_id_endpoints_eq`, `toHomUnop_id` (collapsed form).
- Composition-side lemmas: `unop_comp_base_grothendieck` (rfl),
  `unop_comp_fiber_grothendieck` (rfl),
  `fibFib_map_comp_fiber` (distributes `(fibFib X).map` over the
  three-piece `Grothendieck.comp_fiber`),
  `toHomUnop_comp_endpoints_eq` (split-equals-fused for the outer
  `F.map`-transport via `baseFib.map_comp ∘ op_comp ∘ F.map_comp`),
  `toHomUnop_comp` (the full reshape; uses `baseHomComp`,
  `fibHomCrossNat`, `Functor.congr_hom` against
  `F.map ((baseFib.map (h.unop.base ≫ g.unop.base)).op) =
  F.map (baseFib.map g.unop.base).op ⋙ F.map (baseFib.map h.unop.base).op`).
- `FunctorBetweenCovContraData.toFunctorToData`: the `FunctorToData`
  repackaging (`hom_id` via `toHomUnop_id + eqToHom_op`;
  `hom_comp` via `toHomUnop_comp + op_comp + eqToHom_op +
  Cat.opFunctor_map`, finishing by `rfl`).
- `FunctorBetweenCovContraData.toFunctor`: the main extractor,
  `(Grothendieck.functorTo (F ⋙ Cat.opFunctor) data.toFunctorToData).rightOp`.

**Proof-engineering lessons from Task 3:**

1. `rw` does not match `data.fibHomCrossApp f g x` against a goal
   that renders as `(fun {c c'} ↦ data.fibHomCrossApp) f g x` after
   abbrev-implicit expansion.  Workaround: `conv_lhs =>
   rw [show ... = ... from data.baseHomComp h.unop.base g.unop.base
   Z.unop.fiber]` with the fully-resolved RHS spelled out in the
   `show`.
2. `rw` of `(g ≫ h).unop.base = h.unop.base ≫ g.unop.base` triggers
   motive-not-type-correct because other sub-terms have types that
   depend on the rewritten form.  Workaround: rewrite the dependent
   sub-term *first* via `fibFib_map_comp_fiber` (which uses
   `unop_comp_fiber_grothendieck` internally) to break the
   dependency, then proceed.
3. `change` allows forcing definitional-equality unfoldings that
   `rw` cannot reach.  Used to expose `Grothendieck.id_fiber` and
   `Grothendieck.comp_fiber` on `(𝟙 X).unop.fiber` and
   `(g ≫ h).unop.fiber`.
4. `show` with goal-changing intent triggers a lint warning; use
   `change` instead.
5. The fused-vs-split `F.map`-transport identity collapses via
   `Functor.congr_hom hF` where `hF : F.map (fused).toFunctor =
   F.map A.toFunctor ⋙ F.map B.toFunctor`, proven by `rw
   [baseFib.map_comp, op_comp, F.map_comp]; rfl`.

**Still to do (tasks 4-22, straight from plan):**

- Task 4: `praDirectionsTargetFibre : Cat.{v_I, u_I}ᵒᵖ ⥤ Cat` =
  `Cat.opFunctor.op ⋙ presheafCatFunctor ⋙ catULiftFunctor2 ⋙
  Cat.opFunctor` in `PresheafPRA.lean`.
- Task 5: `praPolyDirectionsTarget`
  = `(grothendieckContraFunctor Cat.{v_I, u_I}).obj
  praDirectionsTargetFibre`.
- Task 6: `praPolyDirectionsSource`
  = `Cat.of (Grothendieck (functorFromDataContra sourceData))`.
- Task 7 (densest): `praPolyDirectionsData :
  FunctorBetweenCovContraData (functorFromDataContra sourceData)
  praDirectionsTargetFibre`.  Six fields including three coherences.
  Use `sourceDataFib` widening (`PresheafPRA.lean:187`) and
  `ccrNewFamilyNat` for the naturality component.  Plan recommends
  factoring into `praPolyDirectionsData_fibFib`,
  `praPolyDirectionsFibHomCrossApp`, `_fibHomCrossNat`,
  `_baseHomId`, `_baseHomComp` as private defs/lemmas outside the
  data bundle.
- Task 8: `praPolyDirectionsFunctor` :=
  `FunctorBetweenCovContraData.toFunctor praPolyDirectionsData`.
- Task 9: three bridge lemmas (`_base`, `_fibre`, `_map_app`) that
  should hold by `rfl` — if not, `simp only` with data-bundle unfolds.
- Task 10: rename old `praPositionsPresheaf` → `praPositionsUnwidened`
  private helper (body identical, just rename).
- Task 11: rewrite `praPositions` to use `praPositionsUnwidened`.
- Task 12: rewrite `praDirectionsAt` to use `praPolyDirectionsFunctor`
  via a helper `praPolyDirectionsAtSourceObj`.
- Task 13: migrate `PresheafPRAUMorph.lean` call sites (specifically
  `praReassemble_directions` at lines 1230-1310) away from deleted
  names.  Drop `private` from `praPositionsUnwidened` if needed for
  cross-file use.
- Task 14: delete `praDirectionsAtFunctorOp`, `praDirectionsAtFunctor`,
  `praPositionsPresheaf`.
- Task 15: remove `variable (P : PresheafPRACat …)` at line 459 of
  `PresheafPRA.lean`; thread `P` as explicit parameter where used;
  audit `variable (I …)` / `variable (J …)`.
- Task 16: create `GebLeanTests/Utilities/PresheafPRADirNat.lean`
  with type-signature sanity tests.
- Task 17: import the new test module from `GebLeanTests.lean`.
- Tasks 18-21: append bridge-collapse, pointwise-accessor,
  functoriality, universe-polymorphism tests.
- Task 22: mark the v2 spec as Complete in `.session/workstreams/`
  and rename stale references.

**Universe parameters to reuse** (from `PresheafPRA.lean:34`):
`u_I v_I u_J v_J w_I w'`.

**Plan location**:
`docs/superpowers/plans/2026-04-19-praDirections-naturality-v2.md`.
**Spec location**:
`docs/superpowers/specs/2026-04-18-praDirections-naturality-design-v2.md`.

## References

- nLab: parametric right adjoint
- Gambino-Kock: Polynomial functors and polynomial
  monads
- Weber: Polynomials in categories with pullbacks
- Berger-Mellies-Weber: Monads with arities
- `.session/workstreams/pra-universal-morphisms.md`
  (detailed Phase 3-6 plan)
