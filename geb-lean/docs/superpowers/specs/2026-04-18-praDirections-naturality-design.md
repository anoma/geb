# Design: `(I, J, P)`-Naturality of `praDirectionsAtFunctor*`

## Purpose

Promote `praDirectionsAtFunctorOp` and `praDirectionsAtFunctor` in
`GebLean/PresheafPRA.lean` from per-`(I, J, P)` definitions to natural
transformations between functors out of `Grothendieck
(presheafPRACatBifunctorUncurried)`.  Absorbing `P` into the
Grothendieck base makes the shape a standard nat-trans (between two
functors `Grothendieck(presheafPRACatBifunctorUncurried) ⥤ Cat`),
keeping the pattern uniform with `ccrNewIndexNat`, `ccrNewFamilyNat`,
and `praPositionsNat`.  The transitional `praPositionsPresheaf`
bridge is retired in this spec.  `praEvalAt*` is deferred.

## Scope

In scope:

- `praDirectionsNatOp`, the Op-form natural transformation, built via
  `FunctorFromData` and `NatTransFromData` (`Utilities/
  Grothendieck.lean:1067,1221`).  Each component at a Grothendieck
  object `⟨⟨J, I⟩, P⟩` is the former per-`(I, J, P)`
  `praDirectionsAtFunctorOp`.
- `praDirectionsNat`, the non-Op natural transformation, built as a
  parallel `FunctorFromData`/`NatTransFromData` bundle whose fibres
  use `.ElementsPre` and the non-widened `(Iᵒᵖ ⥤ Type w_I)` target.
- Bridge lemmas relating each per-component to the old per-`(I, J, P)`
  composite, plus a lemma relating the Op and non-Op natural forms.
- Rewriting `praPositions I J P j` and `praDirectionsAt I J P j a`
  bodies (signatures unchanged) to route through the natural forms,
  via a `private` helper (`praPositionsUnwidened` or similar) that
  absorbs the unwidening from `praPositionsNat` to the underlying
  non-widened presheaf.
- Deletion of `praDirectionsAtFunctorOp`, `praDirectionsAtFunctor`,
  and `praPositionsPresheaf`.
- Migration of any downstream references to the three deleted names
  (pre-task grep to determine the scope).
- Validation step: remove `variable (P : PresheafPRACat …)` and any
  `variable (I …)` / `variable (J …)` that turn out to be unused
  after the rewrites.  Any that remain in use stay with a brief
  comment explaining why.
- New test file `GebLeanTests/Utilities/PresheafPRADirNat.lean`,
  registered in `GebLeanTests.lean`.
- Minimal updates to `.session/workstreams/*.md` for stale name
  references.

Out of scope (deferred):

- `praEvalAt*` and its surrounding section in `PresheafPRA.lean`.
- Follow-up #397 (`catULiftFunctor` as a specialization of
  `catULiftFunctor2`).
- Follow-up #398 (narrowing the `uliftCategory` local-instance scope
  in `PresheafPRA.lean`).

## Design principles

Consistent with the preceding specs:

1. **Natural / functorial / higher-order by default.**  The canonical
   form is the natural transformation; pointwise accessors are thin
   projections, not parallel implementations.
2. **Widen naturally.**  The target universe of `praDirectionsNatOp`
   matches the widening used by `ccrNewFamilyNat` and
   `praPositionsNatTarget`, achieved via the existing
   `catULiftFunctor2` or a close variant.
3. **One operation per step.**  `sourceData`, `targetData`, and
   `natData` are each a bundled data structure with explicit fields;
   their coherence proofs are small and isolated.
4. **Reuse established infrastructure.**  Build on mathlib's
   `Functor.uncurry`, `CategoryOfElements.map`, and the project's
   `FunctorFromData` / `NatTransFromData`.  If universes do not
   align, lift first and then compose, rather than rolling our own.

## File placement and naming

Modified:

- `GebLean/PresheafPRA.lean` — the heart of the spec.
  - Additions: the uncurried base functor if not available directly
    via `Functor.uncurry`; two `FunctorFromData` bundles for the Op
    side; two for the non-Op side; two `NatTransFromData` bundles;
    the two extracted nat-transs (`praDirectionsNatOp`,
    `praDirectionsNat`); bridge lemmas; the `private`
    unwidening helper (e.g. `praPositionsUnwidened`).
  - Rewrites: `praPositions`, `praDirectionsAt` bodies (Option B).
  - Deletions: `praDirectionsAtFunctorOp`, `praDirectionsAtFunctor`,
    `praPositionsPresheaf`.
  - `variable` removals as validation.
- `GebLean/PresheafPRAUMorph.lean` — possible call-site migrations;
  scope determined by pre-task grep for `praDirectionsAtFunctor*` or
  `praPositionsPresheaf`.
- `GebLean/Utilities/Grothendieck.lean` — only if a small helper is
  needed (e.g., a lemma about `FunctorFromData` with a constant
  target).  Any helper is additive and placed in a clear section.
- `GebLeanTests.lean` — one new import line.
- `.session/workstreams/presheaf-pra.md`,
  `.session/workstreams/pra-universal-morphisms.md` — minimal name
  substitutions (best-effort).

Created:

- `GebLeanTests/Utilities/PresheafPRADirNat.lean`.

Naming conventions parallel the prior specs:

- `praDirectionsNatOp`, `praDirectionsNat` — the two natural
  transformations.
- `praDirectionsNatOp_app_eq_*`, `praDirectionsNat_app_eq_*`,
  `praDirectionsNat_eq_op_of_praDirectionsNatOp` — bridge lemmas,
  none `@[simp]`.
- `private def praPositionsUnwidened I J P : Jᵒᵖ ⥤ Type w'` — the
  internal unwidening helper.
- Private scaffolding: `sourceData`, `targetData`, `natData` (and the
  non-Op variants `sourceDataPre`, `targetDataPre`, `natDataPre`).
- Private helpers as needed: e.g., `praDirectionsNatOpAppFunctor`,
  `praDirectionsNatOpApp`, paralleling the `praPositionsNatApp*`
  pattern from the positions spec.

## Architecture

### The base

`presheafPRACatBifunctor` is in curried form
`Catᵒᵖ ⥤ (Catᵒᵖ ⥤ Cat)`.  The uncurried form
`presheafPRACatBifunctorUncurried : Catᵒᵖ × Catᵒᵖ ⥤ Cat` is obtained
via mathlib's `Functor.uncurry`.  If universes do not align, apply a
suitable universe-lift and then uncurry; do not reimplement
uncurrying.  The spec commits to using `Functor.uncurry`.

### Op side

`sourceData : FunctorFromData presheafPRACatBifunctorUncurried
(E := Cat)`:

- `fib (J, I) : PresheafPRACat I J ⥤ Cat` sends
  `P ↦ (P ⋙ ccrNewIndexFunctor (presheafCat I)).Elements`.  The
  morphism action on `α : P ⟶ Q` uses mathlib's
  `CategoryOfElements.map` applied to `α` whiskered with
  `ccrNewIndexFunctor (presheafCat I)`.  Factors naturally through
  `ccrElementsFunctor` from the CCR utility spec.
- `hom f`: per-`P` nat-trans transporting elements along the base
  change `f : (J₁, I₁) ⟶ (J₂, I₂)`.  Uses `elementsPrecomp`-style
  base-change + the `ccrNewIndexNat`-level coherence.
- `hom_id`, `hom_comp`: coherence proofs, expected to close with
  `apply Cat.Hom.ext; rfl` or a short `ext`/`simp` block.

`targetData : FunctorFromData presheafPRACatBifunctorUncurried
(E := Cat)`, constant in `P`:

- `fib (J, I) := (Functor.const _).obj (widened (Iᵒᵖ ⥤ Type w_I)ᵒᵖ)`
  where the widening uses `catULiftFunctor2` (or equivalent)
  matching `sourceData`'s Cat universe.
- `hom f`: the constant-target analog; reduces to
  `(Cat.opFunctor ⋙ catULiftFunctor2).map f` applied at the `I`
  projection of `f`.
- `hom_id`, `hom_comp`: from `Cat.opFunctor`'s and
  `catULiftFunctor2`'s functoriality.

`natData : NatTransFromData presheafPRACatBifunctorUncurried sourceData targetData`:

- `fibNat (J, I)` at each `P`: the existing per-`(I, J, P)` composite
  `elementsPrecomp P ⋙ ccrNewFamilyNat.app (presheafCat I)` in widened
  form.
- `coherence f`: the square commutes because `ccrNewFamilyNat`'s
  naturality (the `I`-direction) and `elementsPrecomp`'s compatibility
  with whiskering (the `J`- and `P`-directions) combine to close.
  Expected to close by `rfl` or a short `ext` + `simp` block.

Extracted:

```lean
def praDirectionsNatOp :
    functorFromData presheafPRACatBifunctorUncurried sourceData ⟶
      functorFromData presheafPRACatBifunctorUncurried targetData :=
  natTransFrom _ _ _ natData
```

### Non-Op side

A parallel bundle:

- `sourceDataPre`: like `sourceData` but with the `.ElementsPre`
  shape.
- `targetDataPre`: like `targetData` but with non-Op target
  (`Iᵒᵖ ⥤ Type w_I` widened, no outer `ᵒᵖ`).
- `natDataPre`: parallel `NatTransFromData`.

Extracted:

```lean
def praDirectionsNat :
    functorFromData presheafPRACatBifunctorUncurried sourceDataPre ⟶
      functorFromData presheafPRACatBifunctorUncurried targetDataPre :=
  natTransFrom _ _ _ natDataPre
```

The relationship to `praDirectionsNatOp` is a bridge lemma (see
below), not a direct derivation — the separate-bundle choice avoids
mixed Op/non-Op arrows inside coherence proofs.

### Bridge lemmas

1. `praDirectionsNatOp_app_eq_elementsPrecomp_ccrNewFamilyFunctor`:
   each per-component unfolds to `elementsPrecomp P ⋙
   ccrNewFamilyFunctor (presheafCat I) ⋙ widening`.  Proved by `rfl`
   or a short unfold.

2. `praDirectionsNat_app_eq_elementsPrecomp_ccrNewFamilyFunctor`:
   the non-Op analog.

3. `praDirectionsNat_eq_op_of_praDirectionsNatOp`:
   `(praDirectionsNat.app X).toFunctor = (praDirectionsNatOp.app
   X).toFunctor.op ⋙ unopUnop _`.  Proved by `rfl`.

None marked `@[simp]`.

### Pointwise-accessor rewrites (Option B)

Internal helper:

```lean
/-- Unwidened form of the positions presheaf at a given PRA.
Internal helper absorbing the `ULift`/`ULiftHom` unwrap of
`praPositionsNat`.  Used by `praPositions` and `praDirectionsAt`. -/
private def praPositionsUnwidened
    (I : Type u_I) [Category.{v_I} I]
    (J : Type u_J) [Category.{v_J} J]
    (P : PresheafPRACat.{…} I J) : Jᵒᵖ ⥤ Type w' :=
  /- unwrap praPositionsNat.app's widening at P -/
```

Rewrites (signatures unchanged):

```lean
def praPositions
    (I : Type u_I) [Category.{v_I} I]
    (J : Type u_J) [Category.{v_J} J]
    (P : PresheafPRACat.{…} I J) (j : Jᵒᵖ) : Type w' :=
  (praPositionsUnwidened I J P).obj j

def praDirectionsAt
    (I : Type u_I) [Category.{v_I} I]
    (J : Type u_J) [Category.{v_J} J]
    (P : PresheafPRACat.{…} I J)
    (j : Jᵒᵖ) (a : praPositions I J P j) : Iᵒᵖ ⥤ Type w_I :=
  (praDirectionsNat.{…}.app ⟨⟨_, _⟩, P⟩).toFunctor.obj
    (Opposite.op ⟨j, a⟩)
```

If the Grothendieck-object construction `⟨⟨_, _⟩, P⟩` at the `.app`
site is syntactically awkward, a tiny private helper packages it
(e.g., `private def praDirGrothObj I J P : Grothendieck …`).

### Deletions

After the additions compile and the call sites migrate:

- `praDirectionsAtFunctorOp` (`PresheafPRA.lean:288–294`).
- `praDirectionsAtFunctor` (`PresheafPRA.lean:302–306`).
- `praPositionsPresheaf` (`PresheafPRA.lean` — added in the prior
  spec's Task 1).

### Variable-removal validation

Final task:

- Remove `variable (P : PresheafPRACat …)`.
- Remove `variable (I …)` / `variable (J …)` if unused; leave those
  that remain in use with a short comment explaining why.
- Re-run `lake build` — no warnings.
- `#print axioms praDirectionsNat` / `praDirectionsNatOp` — standard
  three only.

## Testing plan

New file `GebLeanTests/Utilities/PresheafPRADirNat.lean`.  Six test
categories:

1. **Type-signature sanity**: `#check` on `praDirectionsNatOp`,
   `praDirectionsNat`, and any exposed `FunctorFromData` bundles at
   universe 0.
2. **Bridge-lemma collapse** at `I = J = PUnit` with a specific `P`:
   apply `praDirectionsNatOp_app_eq_*` and verify the equation.
3. **Op / non-Op relation**: verify
   `praDirectionsNat_eq_op_of_praDirectionsNatOp` at a concrete
   instantiation.
4. **Pointwise-accessor compatibility**: `praPositions` and
   `praDirectionsAt` produce the same values as direct extraction
   from the nat-trans.  Exercises the Option B rewrites.
5. **Naturality square**: at a concrete base-change in
   `Grothendieck(presheafPRACatBifunctorUncurried)`, verify the
   `NatTransFromData.coherence` yields the expected equation.
6. **Universe polymorphism**: one `#check` at mixed universes
   (`u_I := 1`, others 0).

No Plausible; the content is definitional-equality assertions.

## Success criteria

- `lake build` and `lake test` clean, zero warnings.
- `#print axioms praDirectionsNat` and `praDirectionsNatOp` report
  only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`/`admit`/`axiom`/`noncomputable`/`Classical`/`Quot.out`
  introduced.
- `praDirectionsAtFunctorOp`, `praDirectionsAtFunctor`, and
  `praPositionsPresheaf` fully removed from the codebase.
- `variable (P …)` removed from `PresheafPRA.lean`.
- `variable (I …)` / `variable (J …)` removed unless at least one
  signature genuinely needs them — if so, a comment explains why.
- Every new definition has a formal docstring.

## Non-goals, restated

This spec does not touch `praEvalAt*`, does not resolve follow-ups
#397 and #398, and does not add reusable abstractions beyond those
the spec requires.
