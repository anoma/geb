# Design: `C`-Naturality of `ccrNewIndex` and `ccrNewFamily`

## Purpose

Promote `ccrNewIndexFunctor` and `ccrNewFamilyFunctor` in
`GebLean/Utilities/Families.lean` from per-`C` definitions to `Cat`-valued
natural transformations. The result is a utility-level interface whose
pointwise components are functors, assembled so that subsequent specs can
lift `praPositionsFunctor` and `praDirectionsAtFunctor*` in
`GebLean/PresheafPRA.lean` to fully `(I, J)`-natural form.

This spec covers utilities only. Consumer promotion in `PresheafPRA.lean`
is deferred to followup specs.

## Scope

In scope:

- `ccrNewIndexNatFunctor`, a per-`C` functor whose target is a
  universe-widened `Cat.of (Type w)`.
- `ccrNewIndexNat`, the natural transformation assembling those per-`C`
  functors into a morphism between functors `Cat ⥤ Cat`.
- `ccrElementsFunctor`, packaging per-`C` categories-of-elements
  `(ccrNewIndexNatFunctor C).Elements` into a single `Cat ⥤ Cat` functor.
- `ccrNewFamilyNat`, the natural transformation from `ccrElementsFunctor`
  to a universe-widened opposite-category functor.
- Tests in a new `GebLeanTests/Utilities/Families.lean`.

Out of scope (followup specs):

- Promotion of `praPositionsFunctor` to an `(I, J)`-natural transformation.
- Promotion of `praDirectionsAtFunctor*` to an `(I, J)`-natural
  transformation.
- Any changes to `ccrNewEvalCatFunctor` or `praEvalAt*`.
- Removing `variable` declarations at the top of `PresheafPRA.lean`.
- Deprecation or deletion of the existing `ccrNewIndexFunctor` or
  `ccrNewFamilyFunctor`.

## Design principles

Two principles guide every shape decision in this spec:

1. **Functorial / higher-order by default.** Where a choice exists between
   a narrow form that localizes compensation work and a wide form that
   makes the natural / functorial / higher-order interface canonical,
   prefer the wide form, even at the cost of more code volume and
   downstream caller updates. This project is building foundations.
2. **One operation per step.** Avoid entangling multiple layers of
   operation in a single definition. Compose small, focused pieces.

## File placement and naming

All new definitions live in `GebLean/Utilities/Families.lean`, appended
after the existing `ccrNewFamilyFunctor` section. No new source files.

Naming parallels the existing `ccrNew…Functor` conventions. New
identifiers: `ccrNewIndexNatFunctor`, `ccrNewIndexNat`,
`ccrElementsFunctor`, `ccrNewFamilyNat`, `ccrNewFamilyNatTarget`, and any
supporting helpers (`typeCatLift`, `catULiftFunctor`) needed to express
the universe-widened target categories.

## Architecture

### Universe widening

`coprodCovarRepFunctor` has type
`Cat.{v, u} ⥤ Cat.{max w v, max (w+1) u}`. For natural transformations
between functors `Cat.{v, u} ⥤ Cat.{?, ?}` to type-check, the target
functor must land in the same `Cat.{max w v, max (w+1) u}`. Concretely:

- A widened form `typeCatLift : Cat.{max w v, max (w+1) u}` is defined as
  a ULift composition over `Cat.of (Type w)`, using mathlib's object and
  hom universe-lifting machinery. The precise ULift layering is an
  implementation detail fixed by the plan.
- A widening functor
  `catULiftFunctor : Cat.{v, u} ⥤ Cat.{max w v, max (w+1) u}`
  bumps `Cat.opFunctor` outputs into the matching universe for
  `ccrNewFamilyNat`.

Both widenings are localized to these utility definitions; they do not
propagate into the existing `ccrNewIndexFunctor` or `ccrNewFamilyFunctor`
signatures, which remain untouched.

### `ccrNewIndexNatFunctor`

```lean
def ccrNewIndexNatFunctor (C : Type u) [Category.{v} C] :
    CoprodCovarRepCat.{u, v, w} C ⥤ typeCatLift
```

Each object is sent to the ULift-widened form of `ccrNewIndex P`; each
morphism to the widened form of `ccrNewReindex f`. The definition is
obtained by post-composing `ccrNewIndexFunctor C` with the ULift
functor(s) implicit in `typeCatLift`.

### `ccrNewIndexNat`

```lean
def ccrNewIndexNat :
    coprodCovarRepFunctor.{u, v, w} ⟶
      (Functor.const Cat.{v, u}).obj typeCatLift
```

The target is the constant functor at `typeCatLift`. The choice of a
**constant** target is forced by the structure of `coprodCovarRepFunctor`:
on `(X, E)`, `coprodCovarRepFunctor.map F` preserves the index type `X`,
so naturality of `ccrNewIndexNat` at `F : C ⥤ D` requires the target
functor to act as the identity — i.e., to be constant.

Each `ccrNewIndexNat.app C` is `ccrNewIndexNatFunctor C`. Naturality
holds definitionally, because the naturality square reduces to the
equality `(X, F ∘ E) ↦ X = (X, E) ↦ X` on index projection.

### `ccrElementsFunctor`

```lean
def ccrElementsFunctor :
    Cat.{v, u} ⥤ Cat.{max w v, max (w+1) u} where
  obj C := Cat.of (ccrNewIndexNatFunctor C.α).Elements
  map F := /-- the functor lifted from the naturality square at F --/
```

The morphism action on `F : C ⥤ D` sends `⟨P, i_lifted⟩` to
`⟨(coprodCovarRepFunctor.map F).obj P, i_lifted⟩` — the lifted index
component `i_lifted` passes through unchanged, because the naturality
square for `ccrNewIndexNat` at `F` holds definitionally (the index type
is preserved by `coprodCovarRepFunctor.map F`). The `.property` component
of elements morphisms similarly transports along a definitional equality
with no rewriting.

Rationale for a bespoke definition: introducing a general
`elementsFunctorOfConstNat` abstraction would be justified only by
reusable hits against the other accessors (`ccrNewFamily`,
`ccrNewEvalCat`). Neither of those has a constant target, so the
abstraction would not fit them. We therefore write `ccrElementsFunctor`
directly.

### `ccrNewFamilyNatTarget`

```lean
def ccrNewFamilyNatTarget :
    Cat.{v, u} ⥤ Cat.{max w v, max (w+1) u} :=
  Cat.opFunctor ⋙ catULiftFunctor
```

The target sends `C` to a universe-widened form of `Cᵒᵖ`. Both factors
are already-established constructions: `Cat.opFunctor` from mathlib,
`catULiftFunctor` from our universe-widening helper.

### `ccrNewFamilyNat`

```lean
def ccrNewFamilyNat :
    ccrElementsFunctor ⟶ ccrNewFamilyNatTarget
```

Each component `ccrNewFamilyNat.app C` is a functor
`(ccrNewIndexNatFunctor C).Elements ⥤ (widened Cᵒᵖ)`. At an object
`⟨P, i_lifted⟩`:

1. Unlift `i_lifted` to recover `i : ccrNewIndex P`.
2. Apply the existing `ccrNewFamilyFunctor C` to `⟨P, i⟩`.
3. Apply `catULiftFunctor` to the result.

The morphism action follows the same recipe, using `ccrNewFiberMor`
underneath.

Naturality at `F : C ⥤ D`: on an object `⟨P, i_lifted⟩`, both composite
paths reduce to the widened `Opposite.op (F.obj (ccrNewFamily P i))`.
The top-right-then-down path uses the fact that `ccrNewFamilyNatTarget`
applies `F.op` after widening; the down-then-bottom path uses the
definitional identity
`ccrNewFamily ((coprodCovarRepFunctor.map F).obj P) i = F.obj (ccrNewFamily P i)`.
On morphisms, naturality follows from `ccrNewFiberMor_comp`.

### Bridge lemma

```lean
theorem ccrNewFamilyNat_app_eq_ccrNewFamilyFunctor (C : Type u)
    [Category.{v} C] :
    ccrNewFamilyNat.app C = /-- unlift, apply ccrNewFamilyFunctor C, lift --/
```

Not marked `@[simp]`, to avoid unfolding cycles. Serves as a manually-
invoked bridge that makes explicit the relationship between the new
`C`-natural form and the existing per-`C` functor.

## Data flow

No runtime data flow — this is a pure categorical construction. The
structural flow is:

```
coprodCovarRepFunctor  --ccrNewIndexNat-->   (const typeCatLift)
                                             |
                                        (category of elements,
                                         packaged per-C into)
                                             v
                        ccrElementsFunctor  --ccrNewFamilyNat-->  ccrNewFamilyNatTarget
                                                                  (= Cat.opFunctor ⋙ catULiftFunctor)
```

## `@[simp]` lemmas

Exposed by each layer, minimum necessary for clean unfolding:

- `ccrNewIndexNat_app` — identifies `ccrNewIndexNat.app C` with
  `ccrNewIndexNatFunctor C`.
- `ccrElementsFunctor_obj`, `ccrElementsFunctor_map_obj` — and
  `_map_map` if downstream proofs need it.
- `ccrNewFamilyNat_app_obj`, `ccrNewFamilyNat_app_map` — rewrite the
  per-`C` component on objects and morphisms.

The bridge lemma `ccrNewFamilyNat_app_eq_ccrNewFamilyFunctor` is
deliberately **not** `@[simp]`.

## Testing plan

A new file `GebLeanTests/Utilities/Families.lean`, registered in
`GebLeanTests.lean` alongside the existing entries. Tests cover:

1. Type-signature sanity: `#check` on each new top-level definition at a
   specific universe instantiation (all universes `= 0`).
2. Source/target identity: `#check` that per-`C` component types match
   the expected source and target functors' values.
3. Definitional collapse to existing utilities: `#guard` that
   `ccrNewIndexNat.app C` and `ccrNewFamilyNat.app C` agree with
   `ccrNewIndexFunctor C` and `ccrNewFamilyFunctor C` (modulo the ULift)
   for a concrete small base category.
4. Naturality in `C`, small example: `#guard` that
   `ccrNewIndexNat.naturality F` holds on a sample object for a concrete
   `F : C ⥤ D`.
5. Functoriality of `ccrElementsFunctor`: `#guard` on `map_id` and a
   two-step `map_comp` for sample elements.
6. Universe polymorphism: at least one test at non-zero levels
   (e.g. `u := 1, v := 0, w := 0`) to catch accidental universe
   specialization.

No Plausible / property-based tests. The content is predominantly
definitional-equality assertions; Plausible's randomization story does
not fit.

## Success criteria

- `lake build` clean with no warnings, `sorry`, `admit`, or unused
  `variable`.
- `lake test` passes.
- `lake build` time not dominated by the new additions.
- Every new definition carries a docstring stating its role and its
  relationship to the existing `ccrNew…Functor`.

## Non-goals, restated

This spec does not touch `PresheafPRA.lean`, does not remove or
deprecate the existing `ccrNewIndexFunctor` / `ccrNewFamilyFunctor`,
and does not introduce general universe-widening or
`elementsFunctorOfConstNat` abstractions. Followup specs handle
consumer promotion and any eventual deprecation cleanup.
