# Design: `(I, J)`-Naturality of `praPositionsFunctor`

## Purpose

Promote `praPositionsFunctor` in `GebLean/PresheafPRA.lean` from a
per-`(I, J)` definition to a natural transformation between bifunctors
`Cat.{v_J, u_J}ᵒᵖ ⥤ (Cat.{v_I, u_I}ᵒᵖ ⥤ Cat.{…})`, and delete the
per-`(I, J)` form. The goal aligns with the stated workstream
motivation: every piece of `PresheafPRA.lean` should be fully
functorial in `(I, J)`, so that the `variable (I …)`, `variable (J …)`
declarations can eventually be removed and new code is not tempted
into non-functorial forms.

This spec covers `praPositionsFunctor` only. `praDirectionsAtFunctor*`,
`praDirectionsAt`, and the `variable` declarations themselves are left
for a follow-up spec; a small temporary bridge `praPositionsPresheaf`
accommodates them until then.

## Scope

In scope:

- `praPositionsNatTarget`, a bifunctor
  `Cat.{v_J, u_J}ᵒᵖ ⥤ (Cat.{v_I, u_I}ᵒᵖ ⥤ Cat.{…})` whose value at
  `(J, I)` is the widened form of `Jᵒᵖ ⥤ Type w'`, constant in `I`.
- `praPositionsNat`, the natural transformation
  `presheafPRACatBifunctor ⟶ praPositionsNatTarget`.
- `praPositionsNat_app_eq_presheafCatFunctor`, the bridge lemma
  relating each `.app` component to the underlying non-widened
  functor.
- `praPositionsPresheaf`, a temporary dependent function
  `(I, J, P) ↦ Jᵒᵖ ⥤ Type w'` that returns the non-widened positions
  presheaf. Its docstring flags it as transitional and slated for
  removal when the directions section is promoted.
- Deletion of the existing `praPositionsFunctor` definition in
  `GebLean/PresheafPRA.lean`.
- Mechanical substitution of the old `(praPositionsFunctor I J).obj P`
  idiom with `praPositionsPresheaf I J P` at all 31 call sites
  across `GebLean/PresheafPRA.lean` and `GebLean/PresheafPRAUMorph.lean`.
- Minimal update to `.session/workstreams/presheaf-pra.md` and
  `.session/workstreams/pra-universal-morphisms.md` to replace the
  name (those files are session notes, not released content).
- Tests in a new `GebLeanTests/Utilities/PresheafPRANat.lean`.

Out of scope (followup specs):

- Promotion of `praDirectionsAtFunctor*` / `praDirectionsAt` to
  `(I, J)`-natural form.
- Removal of the `variable (I …)` / `variable (J …)` /
  `variable (P : PresheafPRACat …)` declarations.
- `praEvalAt*` and its surrounding section.
- Any changes to `Utilities/Families.lean` or other utility-level
  files, beyond potentially adding a small variant of
  `catULiftFunctor` if the single-parameter form does not fit the
  required universe signature.

## Design principles

Consistent with the CCR utility spec:

1. **Natural / functorial / higher-order by default.** The canonical
   form is the natural transformation; convenience wrappers are not
   introduced. `praPositionsPresheaf` is a scope-limited temporary
   accommodation, not a recommended entry point, and is flagged as
   such in its docstring.
2. **Widen naturally.** The target universe of `praPositionsNat`
   matches `presheafPRACatBifunctor`'s target universe, which requires
   widening `presheafCatFunctor.obj J` by the `u_I, v_I, w_I`
   universes. The widening is composed in at the bifunctor level; no
   ULift detritus appears at the nat-trans use sites.
3. **One operation per step.** Each of `praPositionsNatTarget`,
   `praPositionsNat`, and the bridge lemma is a thin composition of
   existing named pieces (`presheafCatFunctor`, `catULiftFunctor`,
   `Functor.const`, `Functor.whiskeringRight`, `ccrNewIndexNat`),
   rather than a monolithic hand-built construction.

## File placement and naming

Modified:

- `GebLean/PresheafPRA.lean` — four new declarations in
  `section PresheafPRAAccessors` (replacing the deleted
  `praPositionsFunctor`). Three call-site updates in the same section.
- `GebLean/PresheafPRAUMorph.lean` — ~28 call-site substitutions of
  `(praPositionsFunctor I J).obj P` → `praPositionsPresheaf I J P`.
  No signatures change.
- `GebLeanTests.lean` — one new import line.
- `.session/workstreams/presheaf-pra.md` — name-only substitutions,
  treated as best-effort.
- `.session/workstreams/pra-universal-morphisms.md` — same.

Created:

- `GebLeanTests/Utilities/PresheafPRANat.lean` — new test file.

Naming conventions parallel the CCR utility spec:

- `praPositionsNatTarget` parallels `ccrNewFamilyNatTarget`.
- `praPositionsNat` parallels `ccrNewIndexNat` / `ccrNewFamilyNat`.
- `praPositionsNat_app_eq_presheafCatFunctor` parallels
  `ccrNewFamilyNat_app_eq_ccrNewFamilyFunctor`. Not `@[simp]`.
- `praPositionsPresheaf` is deliberately not `…Nat…` — its role is
  transitional, not part of the canonical surface.

## Architecture

### Target bifunctor `praPositionsNatTarget`

Shape:

```lean
def praPositionsNatTarget :
    Cat.{v_J, u_J}ᵒᵖ ⥤
      (Cat.{v_I, u_I}ᵒᵖ ⥤
        Cat.{max u_I u_J w_I w',
          max u_I u_J v_I v_J (w_I + 1) (w' + 1)})
```

Value at `J`: a constant (in `I`) functor at the widened form of
`Jᵒᵖ ⥤ Type w'`.

Construction: `presheafCatFunctor.{u_J, v_J, w'}` (which lands in
`Cat.{max u_J w', max v_J (w'+1) u_J}`), composed with a
universe-widening functor to reach the `Cat.{max u_I u_J w_I w',
max u_I u_J v_I v_J (w_I+1) (w'+1)}` universe, composed with
`Functor.const Cat.{v_I, u_I}ᵒᵖ` to extend into a bifunctor constant
in `I`. The widening may use `catULiftFunctor` from the CCR utility
spec; if its single `w`-parameter does not fit the required universe
signature, a small two-parameter variant will be added in
`Utilities/Families.lean`. The plan pins down the concrete form.

**Why the target is constant in `I`.** Naturality of `praPositionsNat`
in `I` requires the target functor to respect how
`presheafPRACatBifunctor.map` acts on `I`-morphisms. That action is
precomposition-with-`F.op` on the inner `CoprodCovarRepCat`, which —
by the index-preservation property of `coprodCovarRepFunctor.map`
established in Task 3 of the utility spec — leaves the positions
presheaf unchanged on the nose. The target must therefore be
independent of `I`.

### Natural transformation `praPositionsNat`

```lean
def praPositionsNat :
    presheafPRACatBifunctor.{u_I, v_I, u_J, v_J, w_I, w'} ⟶
      praPositionsNatTarget.{u_I, v_I, u_J, v_J, w_I, w'}
```

Two-level nat-trans: outer level varies in `J`; each outer component
is a nat-trans varying in `I`.

Each `(praPositionsNat.app J).app I` is the old per-`(I, J)`
`praPositionsFunctor` body —
`(Functor.whiskeringRight Jᵒᵖ _ _).obj (ccrNewIndexFunctor
(presheafCat I))` — post-composed with the universe-widening lifts
into the target's `Cat`-universe, and wrapped via `.toCatHom`.

Naturality:

- In `I` (at fixed `J`): follows from `ccrNewIndexNat.naturality`
  (Task 3 of utility, `rfl`) composed with naturality of
  `presheafCatFunctor` under `I` and whiskered with `Jᵒᵖ`. Expected
  to close by `rfl` plus a narrow `simp` with `whiskeringRight`-level
  lemmas.
- In `J`: uses `Functor.whiskeringRight`'s functoriality on
  `Jᵒᵖ`-morphisms. Since `ccrNewIndexNat` has no `J`-dependence, the
  `J`-side naturality is purely structural.

### Bridge lemma `praPositionsNat_app_eq_presheafCatFunctor`

```lean
theorem praPositionsNat_app_eq_presheafCatFunctor
    (I : Type u_I) [Category.{v_I} I]
    (J : Type u_J) [Category.{v_J} J] :
    ((praPositionsNat.app (Cat.of Jᵒᵖ).op).app
      (Cat.of Iᵒᵖ).op).toFunctor = /- composite: old
      whiskeringRight + ccrNewIndexFunctor form, post-composed
      with the widening -/
```

Proved by `rfl` (by construction). Not `@[simp]`: avoids unfolding
cycles. Intended for downstream users who want to reach through the
widening.

### Temporary bridge `praPositionsPresheaf`

```lean
/--
Temporary bridge to the non-widened form of the positions presheaf.
Consumed by `praPositions` / `praDirectionsAtFunctor*` until the
directions section is promoted; will be removed at that time.
-/
def praPositionsPresheaf
    (I : Type u_I) [Category.{v_I} I]
    (J : Type u_J) [Category.{v_J} J]
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J) :
    Jᵒᵖ ⥤ Type w' :=
  (Functor.whiskeringRight Jᵒᵖ _ _).obj
    (ccrNewIndexFunctor.{max v_I u_I (w_I + 1),
      max u_I w_I, w'}
      (↑(presheafCat.{u_I, v_I, w_I} I))) |>.obj P
```

Body is literally the old `praPositionsFunctor` applied to `P`. Not a
functor on its own — a dependent function returning the presheaf.

## Deletions and call-site updates

Deleted:

- `praPositionsFunctor` at `GebLean/PresheafPRA.lean:149–159`
  (docstring + body).

Call-site substitutions (31 total):

- `GebLean/PresheafPRA.lean`: 3 sites (`praPositions`,
  `praDirectionsAtFunctorOp`, `praDirectionsAtFunctor`).
- `GebLean/PresheafPRAUMorph.lean`: ~28 sites of the pattern
  `(praPositionsFunctor I J).obj …` → `praPositionsPresheaf I J …`.

All substitutions are mechanical. The resulting type of the
expression is unchanged in every case, so downstream uses (`.obj j`,
`.Elements`, `.ElementsPre`, etc.) continue to work with no further
adjustment.

## Testing plan

New file `GebLeanTests/Utilities/PresheafPRANat.lean`, registered in
`GebLeanTests.lean`. Tests cover:

1. Type-signature sanity: `#check`-level instantiations of
   `praPositionsNat` and `praPositionsNatTarget` at universe 0.
2. Collapse via the bridge lemma: for a concrete small base-pair
   (e.g. `I = J = PUnit`), verify the bridge on one instantiation.
3. Naturality in `I`: for a concrete `F : I ⥤ I'` (take
   `F = 𝟭 (PUnit : Cat.{0, 0})`), check naturality on a sample
   object.
4. Naturality in `J`: for a concrete `G : J ⥤ J'`, analogous check.
5. Universe polymorphism: one `#check` at mixed universes
   (e.g. `u_I := 1, v_I := 0, u_J := 0, v_J := 0, w_I := 0,
   w' := 0`).

No Plausible / property-based tests. Content is definitional-equality
assertions.

The downstream call-site substitutions are implicitly tested by
`lake build` completing — `PresheafPRA.lean` and `PresheafPRAUMorph.lean`
must continue to compile after the substitutions.

## Success criteria

- `lake build` and `lake test` both clean, no warnings.
- `#print axioms praPositionsNat` reports only standard axioms
  (`propext`, `Classical.choice`, `Quot.sound`).
- No `sorry`, `admit`, `axiom`, `noncomputable`, `Classical`, or
  `Quot.out` introduced.
- Every new definition carries a formal docstring.
- `praPositionsFunctor` is fully gone; `praPositionsPresheaf` is
  the substitute at all 31 call sites.
- The directions section still builds unchanged at the body level;
  its only edit is the `praPositionsFunctor` → `praPositionsPresheaf`
  rename on three lines.

## Non-goals, restated

This spec does not touch `praDirectionsAt*`, `praEvalAt*`, the
`variable` declarations, or any utility-level files beyond a
possibly-small widening helper. The directions spec handles those,
and in the process removes the `praPositionsPresheaf` bridge.
