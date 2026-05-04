# Workstream: Regular Projective Cover by Coproducts of Representables

## Status

Complete — all phases implemented and building.

## Summary

`GebLean/PolyCover.lean` proves that presheaf and
copresheaf categories have enough projectives, with the
projective covers defined via the evaluators of
`FreeCoprodCompletionCat` and `CoprodCovarRepCat`.

### Definitions and instances

**Representable projectivity** (no `u` dependence):

- `uliftYoneda_projective` —
  `Projective (uliftYoneda.{w}.obj X)`
  in `Cᵒᵖ ⥤ Type (max w v)`
- `uliftCoyoneda_projective` —
  `Projective (uliftCoyoneda.{w}.obj X)`
  in `C ⥤ Type (max w v)`

**Presheaf cover** (`P : Cᵒᵖ ⥤ Type (max v w)`):

- `presheafCoverObj P : FreeCoprodCompletionCat C`
  — indexed by `P.ElementsPre`, family via
  `CategoryOfElements.π`
- `presheafCover P = fcToFunctor (presheafCoverObj P)`
  — lands in `Cᵒᵖ ⥤ Type (max u w v)`
- `presheafCoverMap P` — map to
  `P ⋙ uliftFunctor.{u}`
- `presheafCover_projective`,
  `presheafCoverMap_epi`
- `presheafProjectivePresentation P` —
  `ProjectivePresentation (P ⋙ uliftFunctor.{u})`

**Copresheaf cover** (`F : C ⥤ Type (max v w)`):

- `copresheafCoverObj F : CoprodCovarRepCat C`
  — indexed by `F.Elements`, family via
  `CategoryOfElements.π`
- `copresheafCover F = ccrToFunctor (copresheafCoverObj F)`
  — lands in `C ⥤ Type (max u w v)`
- `copresheafCoverMap F` — map to
  `F ⋙ uliftFunctor.{u}`
- `copresheafCover_projective`,
  `copresheafCoverMap_epi`
- `copresheafProjectivePresentation F` —
  `ProjectivePresentation (F ⋙ uliftFunctor.{u})`

**Enough projectives:**

- `presheaf_enoughProjectives` —
  `EnoughProjectives (Cᵒᵖ ⥤ Type (max u w v))`
- `copresheaf_enoughProjectives` —
  `EnoughProjectives (C ⥤ Type (max u w v))`

These compose the projective presentations with
`uliftPresheafIso`/`uliftCopresheafIso`
(`Q ⋙ uliftFunctor ≅ Q` via `ULift.up`/`ULift.down`).

### Universe structure

- Representable projectivity at `Type (max w v)` —
  no `u` dependence.
- Covers absorb `u` from `Ob(C) : Type u` into the
  index type (`P.ElementsPre` / `F.Elements`), landing
  in `Type (max u w v)`.
- The input (co)presheaf stays at `Type (max v w)`;
  the cover map targets the lifted version via
  `uliftFunctor.{u}`.
- `EnoughProjectives` is at `Type (max u w v)`.
  The `u` is intrinsic: the projective cover is an
  unquotiented coproduct over `Ob(C)` and cannot be
  shrunk without losing projectivity.

### Related changes

Renamed in `GebLean/Utilities/Families.lean`:
`ccrDirichletEval` and relatives became `fcEval` etc.,
now defined on `FreeCoprodCompletionCat` (matching the
contravariant functorial action of the Dirichlet
evaluation).  Updated downstream reference in
`GebLean/PolyTwCoprType.lean`.
