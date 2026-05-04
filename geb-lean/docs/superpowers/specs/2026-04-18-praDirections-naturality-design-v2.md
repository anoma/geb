# Design (v2): Polynomial-Functor-Morphism `(I, J, P)`-Naturality for `praDirectionsAtFunctor*`

## Summary

This spec replaces the v1 design (`2026-04-18-praDirections-naturality-design.md`) after execution
uncovered structural obstructions to the v1 approach.  See "Background: why v2" below for a
full account; the short version is that v1 tried to build a natural transformation between two
`FunctorFromData`-packaged functors on a covariant Grothendieck and hit a fibre-direction mismatch
forced by the inherent contravariance of presheaf categories in their base.  v2 instead builds a
single flat functor between two Grothendiecks — a covariant source (elements of positions over all
`(I, J, P)`) and a contravariant target (presheaves over varying `I`) — explicitly encoding the
polynomial-functor-morphism convention (forward on positions, backward on directions).

## Purpose

Promote `praDirectionsAtFunctorOp` and `praDirectionsAtFunctor` in `GebLean/PresheafPRA.lean` to a
fully-`(I, J, P)`-natural form, delete the old per-`(I, J, P)` definitions plus the transitional
`praPositionsPresheaf`, rewrite pointwise accessors to route through the natural form, and remove
the `variable (P …)` declaration.  Promotion captures the polynomial-functor-morphism structure
(backward on directions); a parallel Dirichlet-functor-morphism construction is out of scope.

## Background: why v2

v1 attempted:
1. Covariant Grothendieck + `FunctorFromData` + nat-trans.  Did not type-check: elements of
   presheaves are contravariant under base precomposition in J; covariant Grothendieck's `hom f`
   wanted covariant fibre transport.  See the v1 commit-graph below.
2. Contravariant Grothendieck + `FunctorFromDataContra` (U1/U2 ported).  Did not type-check:
   the target side required a covariant-in-`I` functor `Cat ⥤ Cat` sending
   `I ↦ presheafCat I`, which does not exist without left Kan extension —
   `presheafCatFunctor` is inherently contravariant in `I`.

v2's identification: the mismatch on the target side *is*
the polynomial-functor-morphism convention (backward on directions) showing up as a fibre-morphism
direction in the target Grothendieck.  Embedding the contravariance directly into the target's
Grothendieck morphism structure (via `grothendieckContraFunctor`) and using a flat functor
(rather than a nat-trans between two `FunctorFromData`-built functors) resolves the obstruction.

v1 artifacts still on the branch that remain useful:
- `a7574b89` — `presheafPRACatBifunctorUncurried` (reused).
- `19cae701` — U1: `FunctorFromDataContra` infrastructure (reused).
- `ef8ace94` — U2: `NatTransFromDataContra` infrastructure (not used by v2 directly, but valuable
  standalone).
- `c0468683` — `sourceData` (reused; forms the basis of `praPolyDirectionsSource`).

## Scope

In scope:

- **U3 (new utility port):** `FunctorBetweenCovContra` in `GebLean/Utilities/Grothendieck.lean`
  — the analog of the existing `FunctorBetween` (covariant-to-covariant) and `FunctorBetweenContra`
  (contravariant-to-contravariant) for the mixed case: covariant-source-Grothendieck /
  contravariant-target-Grothendieck.  Ports the structure shape from `FunctorBetween`, adapted
  to the new mathlib-`op`-based `grothendieckContraFunctor` for the target side.
- `praDirectionsTargetFibre : Cat.{v_I, u_I}ᵒᵖ ⥤ Cat.{…widened}` — the
  target Grothendieck's fibre functor.  The input Cat already carries the
  `Iᵒᵖ` convention from `presheafPRACatBifunctorUncurriedOp`'s base
  (`(objBase X).2 = Cat.of Iᵒᵖ`), so the pipeline is three-stage:
  `presheafCatFunctor ⋙ catULiftFunctor2 ⋙ Cat.opFunctor`.  At an input
  `op (Cat.of Iᵒᵖ)` this yields `op (widened (Iᵒᵖ ⥤ Type w_I))`.
- `praPolyDirectionsSource : Cat.{…}` — covariant Grothendieck of
  `functorFromDataContra sourceData`.  Objects are 4-tuples `((J, I), P, element)`.
- `praPolyDirectionsTarget : Cat.{…}` — `(grothendieckContraFunctor Cat.{v_I, u_I}).obj
  praDirectionsTargetFibre`.  Objects are pairs `(I, op_presheaf_on_I)`.
- `praPolyDirectionsFunctor : praPolyDirectionsSource ⥤ praPolyDirectionsTarget` — the main flat
  polynomial-directions functor, built via `FunctorBetweenCovContra`.  Supporting
  `private` data bundle `praPolyDirectionsData : FunctorBetweenCovContraData …`.
- Bridge lemmas relating `praPolyDirectionsFunctor`'s action on objects and morphisms to the
  familiar `elementsPrecomp P ⋙ ccrNewFamilyFunctor (presheafCat I)` composite plus
  `ccrNewFamilyNat`-level naturality.
- Rewriting pointwise accessors (`praPositions`, `praDirectionsAt`) in `PresheafPRA.lean` to route
  through the flat functor, via a `private` `praPositionsUnwidened` helper for the positions case.
- Deletion of `praDirectionsAtFunctorOp`, `praDirectionsAtFunctor`, and `praPositionsPresheaf`.
- Migration of any downstream references (pre-task grep to determine scope;
  `PresheafPRAUMorph.lean:1236-1238` is the known reference).
- Validation: remove `variable (P : PresheafPRACat …)` and any `variable (I …)` / `variable (J …)`
  that turn out to be unused after the rewrites.
- New test file `GebLeanTests/Utilities/PresheafPRADirNat.lean`, registered in `GebLeanTests.lean`.
- Minimal best-effort updates to `.session/workstreams/*.md` for stale name references.

Out of scope:
- Dirichlet-functor-morphism parallel construction (forward-on-directions structure).  If wanted
  later, it's a separate spec — a parallel `praDirDirichletDirectionsFunctor`.  This spec only
  builds the polynomial (backward-on-directions) form.
- `praEvalAt*` and its surrounding section.
- Follow-ups #397 (`catULiftFunctor` as specialization), #398 (`uliftCategory` scope narrowing).
- Round-trip theorems, category instance, or equivalence API on `FunctorBetweenCovContra` beyond
  what `praPolyDirectionsFunctor`'s direct construction needs.  Deferred.

## Design principles

Consistent with prior specs in the workstream:

1. **Natural / functorial / higher-order by default.**  The flat functor is the canonical form;
   pointwise accessors are thin projections.
2. **Widen naturally.**  Universe-widening via `catULiftFunctor2` matches the universe profile
   already established by `sourceData` and `praPositionsNatTarget`.
3. **One operation per step.**  Target fibre, target total, source total, and the flat functor are
   each a distinct named definition.  Coherence proofs are short and isolated.
4. **Reuse established infrastructure.**  `FunctorFromDataContra` (U1), `grothendieckContraFunctor`,
   mathlib's covariant `Grothendieck`, `FunctorBetween`-style data structures (U3), and the
   `sourceData`/`sourceCatVal` already in the file.  No re-derivation of foundational material.
5. **Commit to polynomial-functor-morphism convention.**  The target fibre's outer `.op` wrapping
   (via `Cat.opFunctor` at the end of `praDirectionsTargetFibre`) is deliberate — it encodes the
   backward-on-directions structure that is standard for polynomial functors.  The spec, docstrings,
   and naming make this explicit.

## Naming conventions

- `praDirectionsTargetFibre : Cat.{v_I, u_I}ᵒᵖ ⥤ Cat.{…}` — the per-`I` target fibre.
- `praPolyDirectionsTarget : Cat.{…}` — total target Grothendieck.
- `praPolyDirectionsSource : Cat.{…}` — total source Grothendieck.
- `praPolyDirectionsFunctor : praPolyDirectionsSource ⥤ praPolyDirectionsTarget` — main flat
  functor.
- `praPolyDirectionsData : FunctorBetweenCovContraData …` — `private` packaged data.
- `praPolyDirectionsFunctor_base`, `praPolyDirectionsFunctor_fibre`,
  `praPolyDirectionsFunctor_map_app` — bridge lemmas, not `@[simp]`.
- `praPositionsUnwidened : Jᵒᵖ ⥤ Type w'` — `private` helper absorbing the ULift/ULiftHom
  unwrap of `praPositionsNat`'s widening.  Same body as the deleted `praPositionsPresheaf`.
- `praPositions`, `praDirectionsAt` — pointwise accessors with unchanged signatures; bodies
  updated to use `praPositionsUnwidened` and `praPolyDirectionsFunctor` respectively.

All five top-level names make the polynomial-functor-morphism nature explicit at the surface
(`Poly` prefix), distinguishing from any hypothetical later Dirichlet construction.

## File placement

Modified:
- `GebLean/Utilities/Grothendieck.lean` — new `FunctorBetweenCovContra` section (U3).
- `GebLean/PresheafPRA.lean` — the bulk of the spec's additions and deletions.
- `GebLean/PresheafPRAUMorph.lean` — call-site migration (scope determined by pre-task grep).
- `GebLeanTests.lean` — one new import line.
- `.session/workstreams/presheaf-pra.md`, `.session/workstreams/pra-universal-morphisms.md` —
  minimal name substitutions.

Created:
- `GebLeanTests/Utilities/PresheafPRADirNat.lean` — new test file.

## Architecture

### The base functor

`presheafPRACatBifunctorUncurried : (Catᵒᵖ × Catᵒᵖ) ⥤ Cat.{…}` is already in the file (commit
`a7574b89`).  Its `(Cat × Cat)ᵒᵖ ⥤ Cat`-form `presheafPRACatBifunctorUncurriedOp` is already in
the file (commit `c0468683`, as part of `sourceData`'s construction).

### U3: `FunctorBetweenCovContra`

Port the `FunctorBetween` structure (`GebLean/Utilities/Grothendieck.lean` starting line 4423) to
the mixed covariant-source / contravariant-target case.  The mixed form:

```lean
variable {C : Type uC} [Category.{vC} C] (G : C ⥤ Cat.{vC, uC})   -- covariant source
variable {D : Type uD} [Category.{vD} D] (F : Dᵒᵖ ⥤ Cat.{vD, uD}) -- contravariant target
```

Fields (analog of `FunctorBetweenData`, lines 4569-4582):

- `baseFib : C ⥤ D` — base functor.  (Note: covariant from `C` to `D`, not `Dᵒᵖ`.  The contravariant
  target's `Cᵒᵖ`-indexing is compensated by the `.op` in `F.map _.op` inside subsequent fields.)
- `fibFib : ∀ c, G.obj c ⥤ F.obj (op (baseFib.obj c))` — per-fibre functor into the target's
  `op`-indexed fibre.
- `fibHomCrossApp : ∀ {c c'} (f : c ⟶ c') (x : G.obj c), …` — cross-fibre morphism for the
  lifted morphism in the target.  The shape mirrors `FunctorBetween`'s `fibHomCrossApp` but with
  `F.map (baseFib.map f).op` in place of `F.map (baseFib.map f)`.
- `fibHomCrossNat`, `baseHomId`, `baseHomComp` — coherences.  Same structural shape as
  `FunctorBetween`, with `.op` applied to the `baseFib.map` where needed.

Extractor `FunctorBetweenCovContra.toFunctor : FunctorBetweenCovContraData G F →
(Grothendieck G ⥤ (grothendieckContraFunctor D).obj F)` built directly, analogous to
`FunctorBetween`'s `toFunctor`.

Scope of U3: structure + extractor only.  No round-trip, no category instance, no equivalence —
add later if needed.

### Target fibre `praDirectionsTargetFibre`

```lean
def praDirectionsTargetFibre :
    Cat.{v_I, u_I}ᵒᵖ ⥤ Cat.{max u_I u_J v_J w_I w',
      max u_I u_J v_I v_J (w_I + 1) (w' + 1)} :=
  presheafCatFunctor.{u_I, v_I, w_I} ⋙
    catULiftFunctor2.{…} ⋙
    Cat.opFunctor.{…}
```

Stages:
1. `presheafCatFunctor : op (Cat.of Iᵒᵖ) ↦ Iᵒᵖ ⥤ Type w_I` — presheaves on I.
   The input Cat already carries the `Iᵒᵖ` convention inherited from
   `presheafPRACatBifunctorUncurriedOp`'s base, so no additional inner op
   is applied.
2. `catULiftFunctor2 : widen to match praPolyDirectionsSource's Cat universe`.
3. `Cat.opFunctor : widened (Iᵒᵖ ⥤ Type w_I) ↦ (widened …)ᵒᵖ` — outer op,
   encoding backward-on-directions.

Exact `catULiftFunctor2` parameters pinned during implementation to match
`praPolyDirectionsSource`'s Cat universe.

### Source total `praPolyDirectionsSource`

```lean
def praPolyDirectionsSource : Cat.{…} :=
  Cat.of (Grothendieck
    (functorFromDataContra sourceData.{u_I, v_I, u_J, v_J, w_I, w'}))
```

Objects: pairs `(X, e)` where `X : (grothendieckContraFunctor (Cat × Cat)).obj
presheafPRACatBifunctorUncurriedOp` (a triple `((J, I), P)`) and `e` is a widened element of
`(P ⋙ ccrNewIndexFunctor (presheafCat I)).Elements`.

### Target total `praPolyDirectionsTarget`

```lean
def praPolyDirectionsTarget : Cat.{…} :=
  (grothendieckContraFunctor Cat.{v_I, u_I}).obj
    praDirectionsTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'}
```

Objects: pairs `(I, op_presheaf)` with `op_presheaf` of `(widened Iᵒᵖ ⥤ Type w_I)ᵒᵖ`.

Morphisms `(I₁, x₁) ⟶ (I₂, x₂)`: `(f : I₁ ⟶ I₂ in Cat, η : x₁ ⟶ (praDirectionsTargetFibre.map
f.op).obj x₂)` where η lives in the target fibre `(widened I₁ᵒᵖ ⥤ Type)ᵒᵖ`.  Unfolded, η is a
nat-trans `(praDirectionsTargetFibre.map f.op).obj x₂ ⟶ x₁` in the ordinary direction in `widened
I₁ᵒᵖ ⥤ Type` — the backward-on-directions shape.

### The flat functor `praPolyDirectionsFunctor`

Data (`private`):

```lean
private def praPolyDirectionsData :
    FunctorBetweenCovContraData
      (functorFromDataContra sourceData.{…})
      praDirectionsTargetFibre.{…} where
  baseFib := _  -- sends ((J, I), P) ↦ I
  fibFib := _   -- at each X = ((J, I), P),
                -- widened (P ⋙ F_I).Elements ⥤ (widened Iᵒᵖ ⥤ Type)ᵒᵖ
                -- = widened (elementsPrecomp P ⋙ ccrNewFamilyFunctor (presheafCat I))
  fibHomCrossApp := _
  fibHomCrossNat := _
  baseHomId := _
  baseHomComp := _
```

Main functor:

```lean
def praPolyDirectionsFunctor :
    praPolyDirectionsSource ⥤ praPolyDirectionsTarget :=
  FunctorBetweenCovContra.toFunctor praPolyDirectionsData.{…}
```

Each field in `praPolyDirectionsData` uses existing infrastructure:
- `baseFib` projects to `I` via the second-component of the uncurried-Cat pair plus a `.unop`.
- `fibFib` is the widened old `praDirectionsAtFunctorOp`'s body.
- `fibHomCrossApp` encodes the polynomial-functor-morphism backward direction: at each base step,
  uses `ccrNewFamilyNat`'s naturality to produce the right cross-fibre morphism.
- Coherences close via short tactic blocks following the patterns established in `sourceData`'s
  helpers and `praPositionsNat`'s coherence proofs.

### Bridge lemmas

Three, all `rfl` (by construction of the data):

1. `praPolyDirectionsFunctor_base` — base projection.
2. `praPolyDirectionsFunctor_fibre` — per-element fibre value agrees with the old per-`(I, J, P)`
   composite.
3. `praPolyDirectionsFunctor_map_app` — morphism action agrees with the expected
   `ccrNewFamilyNat`-naturality-derived nat-trans.

None `@[simp]`.

### Pointwise accessors

`praPositions I J P j`: routes through `praPositionsUnwidened I J P` (a `private` helper with the
same body as the deleted `praPositionsPresheaf`).

`praDirectionsAt I J P j a`: constructs a `praPolyDirectionsSource`-object for the specific
`(I, J, P, j, a)`, applies `praPolyDirectionsFunctor`, extracts the fibre component `.snd`,
applies `.unop` to get a plain presheaf, and unwidens to `Iᵒᵖ ⥤ Type w_I`.  A small private
helper can factor the Grothendieck-object construction + unwidening chain if the inline form is
unwieldy.

## Deletions

After new code is in place and call sites migrate:

- `praDirectionsAtFunctorOp` in `PresheafPRA.lean`.
- `praDirectionsAtFunctor` in `PresheafPRA.lean`.
- `praPositionsPresheaf` in `PresheafPRA.lean` (transitional helper from the positions spec).

## Variable-removal validation

Final task:

- Remove `variable (P : PresheafPRACat …)` in `PresheafPRA.lean`.
- Audit whether `variable (I …)` / `variable (J …)` remain used.  Remove those that don't; leave
  those that do with a brief comment explaining why.

## Testing plan

New file `GebLeanTests/Utilities/PresheafPRADirNat.lean`.  Six test categories:

1. **Type-signature sanity.** `#check`-level for `praPolyDirectionsFunctor`, `praPolyDirectionsSource`,
   `praPolyDirectionsTarget`, `praDirectionsTargetFibre` at universe 0.
2. **Bridge-lemma collapse.** Apply the three bridge lemmas at `I = J = PUnit` and a concrete `P`.
3. **Pointwise-accessor compatibility.** Verify `praPositions` and `praDirectionsAt` produce the
   expected values.
4. **Functoriality at a concrete morphism.** Small `((I₁, J₁, P₁), e₁) ⟶ ((I₂, J₂, P₂), e₂)` map,
   verify `praPolyDirectionsFunctor.map` behaves as expected.
5. **U3 infrastructure sanity.** Verify `FunctorBetweenCovContra.toFunctor` produces the expected
   functor at a tiny example (if the example is constructable without massive setup; otherwise
   skip this category).
6. **Universe polymorphism.** Mixed-universe instantiation.

## Success criteria

- `lake build` and `lake test` clean, zero warnings.
- `#print axioms praPolyDirectionsFunctor` reports only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, `admit`, `axiom`, `noncomputable`, `Classical`, `Quot.out`.
- `praDirectionsAtFunctorOp`, `praDirectionsAtFunctor`, `praPositionsPresheaf` removed from
  `GebLean/`.
- `variable (P …)` removed.
- `variable (I …)` / `variable (J …)` removed unless documentably needed.
- Every new definition has a formal docstring.
- Downstream files build unchanged.

## Non-goals

- Dirichlet-functor-morphism parallel (forward-on-directions).
- `praEvalAt*`.
- Follow-ups #397, #398.
- Any round-trip theorems, category instances, or equivalence-style API on U3's
  `FunctorBetweenCovContra` beyond what this spec's flat functor directly uses.
