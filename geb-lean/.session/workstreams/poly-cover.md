# Workstream: Regular Projective Cover by Coproducts of Representables

## Status

Active — scaffolding complete, implementation not started.

## Goal

Prove that (co)presheaf categories have enough
projectives, with the projective objects being
coproducts of representables.  The development covers
both variances:

- **Presheaf side**: `Cᵒᵖ ⥤ Type (max w v)` has enough
  projectives; the projectives are coproducts of
  contravariant representables `uliftYoneda.obj c`,
  corresponding to objects of `FreeCoprodCompletionCat C`.

- **Copresheaf side**: `C ⥤ Type (max w v)` has enough
  projectives; the projectives are coproducts of
  covariant representables, corresponding to objects of
  `CoprodCovarRepCat C`.

Universe-polymorphic: `C : Type u`, `Category.{v} C`,
target `Type (max w v)` for auxiliary universe `w`.

## File

`GebLean/PolyCover.lean` (already created and building).

Imports:

- `GebLean.Polynomial` (for `CoprodCovarRepCat`)
- `GebLean.Utilities.Presheaf` (for `Copresheaf`,
  `Presheaf`, Yoneda utilities)
- `Mathlib.CategoryTheory.Preadditive.Projective.Basic`
  (for `Projective`, `EnoughProjectives`,
  `ProjectivePresentation`)
- `Mathlib.CategoryTheory.Limits.Presheaf` (for
  `colimitOfRepresentable`, `coconeOfRepresentable`,
  `functorToRepresentables`)

## Research

### Regular projective objects

An object P is *projective* if `Hom(P, -)` preserves
epimorphisms: for every epi `e : E ⟶ X` and every
`f : P ⟶ X`, there exists `g : P ⟶ E` with
`g ≫ e = f`.

In a topos (hence in any presheaf category), every epi
is an effective epi, so "projective" and "regular
projective" coincide.

Mathlib definition:

```lean
class Projective (P : C) : Prop where
  factors : ∀ {E X : C} (f : P ⟶ X) (e : E ⟶ X)
    [Epi e], ∃ f', f' ≫ e = f
```

Mathlib also provides:

- `ProjectivePresentation X` — packages a projective P,
  an epi `f : P ⟶ X`, and proofs
- `EnoughProjectives C` — `∀ X, Nonempty
  (ProjectivePresentation X)`

### Representables are projective

By the Yoneda lemma,
`Hom(uliftYoneda.obj c, F) ≃ F.obj (op c)`.
So `Hom(uliftYoneda.obj c, -)` is (naturally isomorphic
to) the evaluation functor `ev_c`.

Epis in presheaf categories are pointwise surjections,
so `ev_c` preserves epis.  Therefore
`uliftYoneda.obj c` is projective.

The equivalence is `uliftYonedaEquiv`:

```lean
def uliftYonedaEquiv
  {X : C} {F : Cᵒᵖ ⥤ Type (max w v₁)} :
  (uliftYoneda.{w}.obj X ⟶ F) ≃ F.obj (op X)
```

### Density theorem (colimit of representables)

Every presheaf `P : Cᵒᵖ ⥤ Type (max w v)` is a colimit
of representables:

```lean
def colimitOfRepresentable
  (P : Cᵒᵖ ⥤ Type max w v₁) :
  IsColimit (coconeOfRepresentable P)
```

The colimit is over the diagram
`functorToRepresentables P : P.Elementsᵒᵖ ⥤ Cᵒᵖ ⥤ Type (max w v₁)`
which sends each element `(c, x)` of `P` to
`uliftYoneda.obj c`.

The canonical map from `∐_{(c,x)} uliftYoneda.obj c`
to `P` is an epi (it is in fact the colimit cocone),
so it provides a projective presentation.

### Copresheaf case by duality

A copresheaf `F : C ⥤ Type (max w v)` is a presheaf on
`Cᵒᵖ`, since `(Cᵒᵖ)ᵒᵖ ⥤ Type (max w v) ≅ C ⥤ Type (max w v)`.
Applying the presheaf results to `Cᵒᵖ` in place of `C`
gives the copresheaf results.

The contravariant representables on `Cᵒᵖ` are
`yoneda.obj (op c)` which correspond to the covariant
representables `coyoneda.obj (op c)` on `C`.

### Existing GebLean definitions

From `GebLean/Utilities/Families.lean`:

- `FreeCoprodCompletionCat C` — coproducts of
  contravariant representables; contravariant
  Grothendieck construction on `familyFunctor C`.
  Objects: `(X : Type w, F : X → C)`.
  Morphisms: `(X,F) → (Y,G)` are `(f : X → Y)` plus
  `∀ x, F x ⟶ G (f x)`.

- `CoprodCovarRepCat C` — coproducts of covariant
  representables; contravariant Grothendieck
  construction on `familyFunctor C ⋙ Cat.opFunctor'`.
  Objects: `(X : Type w, F : X → Cᵒᵖ')`.
  Morphisms: `(X,F) → (Y,G)` are `(f : X → Y)` plus
  `∀ x, G (f x) ⟶ F x` (reversed).

- `FreeProdCompletionCat C` and
  `ProdContravarRepCat C` — product duals (not needed
  for this development).

### Mathlib gaps

Mathlib does not assemble the following, though all
building blocks exist:

- `Projective (uliftYoneda.obj c)` in `Cᵒᵖ ⥤ Type`
- `EnoughProjectives (Cᵒᵖ ⥤ Type (max w v))`
- The copresheaf analogues

## Implementation Plan

### Phase 1: Presheaf side — representables are projective

Prove `Projective (uliftYoneda.{w}.obj X)` in the
presheaf category `Cᵒᵖ ⥤ Type (max w v)`.

Strategy: Given an epi `e : E ⟶ F` and a morphism
`f : uliftYoneda.obj X ⟶ F`, we need a lift
`g : uliftYoneda.obj X ⟶ E` with `g ≫ e = f`.

Via `uliftYonedaEquiv`, `f` corresponds to an element
`y : F.obj (op X)`.  Since `e` is epi in the presheaf
category (hence pointwise surjective), there exists
`x : E.obj (op X)` with `e.app (op X) x = y`.
The lift is `uliftYonedaEquiv.symm x`.

Subtask: We may need a lemma that epi in a presheaf
category implies pointwise surjectivity, or that the
evaluation functor preserves epis.  Check mathlib.

- [ ] 1a. Prove or locate lemma: epi natural
  transformations in functor categories are pointwise
  epi (or that evaluation preserves epis)
- [ ] 1b. Prove `Projective (uliftYoneda.{w}.obj X)`

### Phase 2: Presheaf side — projective presentation

Construct `ProjectivePresentation P` for an arbitrary
presheaf `P : Cᵒᵖ ⥤ Type (max w v)`.

The projective object is the coproduct (as a
copresheaf) of `uliftYoneda.obj c` over the elements
`(c, x)` of `P`, i.e., the colimit of
`functorToRepresentables P`.

From `colimitOfRepresentable P` we get an `IsColimit`
for `coconeOfRepresentable P`.  We need to show that the
canonical map is epi, and that the colimit object is
projective.

The colimit object is a colimit of projective objects.
In a presheaf category (which has all colimits), the
colimit exists.  We need either:

(a) Coproducts of projectives are projective (mathlib
    has `Projective.instSigmaObj` for sigma-indexed
    coproducts, and more generally colimits of
    projectives may be projective in a presheaf topos),
    or

(b) Direct argument that the specific colimit (a
    coproduct of representables) is projective.

- [ ] 2a. Show the colimit of `functorToRepresentables P`
  exists (it does — presheaf categories are cocomplete)
- [ ] 2b. Show the colimit is projective (via closure
  of projectives under coproducts)
- [ ] 2c. Show the canonical map to `P` is epi
- [ ] 2d. Assemble `ProjectivePresentation P`

### Phase 3: Presheaf side — enough projectives

- [ ] 3a. Assemble `EnoughProjectives (Cᵒᵖ ⥤ Type (max w v))`

### Phase 4: Copresheaf side — by duality

Apply Phases 1-3 to `Cᵒᵖ` in place of `C` to obtain:

- [ ] 4a. `Projective (uliftCoyoneda.{w}.obj (op X))`
  in `C ⥤ Type (max w v)` (or the equivalent via
  `Cᵒᵖ` substitution)
- [ ] 4b. `ProjectivePresentation F` for copresheaves
- [ ] 4c. `EnoughProjectives (C ⥤ Type (max w v))`

### Phase 5: Connection to existing definitions

Connect the abstract projective presentations to the
concrete categories in `Families.lean`:

- [ ] 5a. Show that the projective presentation of a
  presheaf yields an object of
  `FreeCoprodCompletionCat C`
- [ ] 5b. Show that the projective presentation of a
  copresheaf yields an object of
  `CoprodCovarRepCat C`
- [ ] 5c. (Stretch) Construct the "cover functor" from
  `Cᵒᵖ ⥤ Type (max w v)` to `FreeCoprodCompletionCat C`
  (and dually for copresheaves)

## Notes

- The `noncomputable section` in
  `Projective/Basic.lean` means we may need
  `noncomputable` on some definitions.  Per project
  guidelines, we should avoid `noncomputable` if
  possible.  The `Projective` class itself is `Prop`,
  so instances are fine, but constructing actual lifts
  may require `Classical.choice`.  We should see
  whether the proof of `Projective (uliftYoneda.obj X)`
  can be made constructive (it depends on whether we
  can constructively extract a preimage from a
  pointwise-surjective natural transformation).
  If not, we may need to discuss with the project owner.

- Universe levels: `w v u` matching
  `colimitOfRepresentable`'s convention.  Presheaves
  land in `Type (max w v)`, `C : Type u`,
  `Category.{v} C`.
