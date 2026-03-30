# Workstream: PshInternal-Grothendieck Equivalence

## Status: In Progress (inverse functor done, equivalence pending)

## Inverse Functor (Task 9 -- complete)

All definitions in `GebLean/PshInternalGrothendieck.lean`:

- `inverseAction_assoc`: associativity of the inverse action,
  using `grothFiberMor_comp` and the `Sigma.ext + heq_of_cast_eq`
  pattern.
- `inversePresheaf G : PshInternalPresheaf X`: assembles the
  inverse fiber functor, projection, action, and all axioms.
- `inverseNatTrans`: the natural transformation between inverse
  fiber functors induced by a morphism of presheaves on the
  Grothendieck category.
- `inversePresheafHom`: the morphism of internal presheaves
  induced by a natural transformation.
- `inverseFunctor : (X.groth ⥤ Type w) ⥤ PshInternalPresheaf X`:
  the full inverse functor, with `map_id` and `map_comp` proved
  by `rfl`.
- `groth_decompose`: every Grothendieck morphism decomposes as
  `grothBaseMor ≫ grothFiberMor ≫ eqToHom`.

### Remaining for equivalence

- Unit natural isomorphism: `P ≅ inversePresheaf (comparisonPresheaf P)`
  via `e ↦ ⟨projAt e, ⟨e, rfl⟩⟩`.
- Counit natural isomorphism:
  `comparisonPresheaf (inversePresheaf G) ≅ G`
  via `⟨⟨x', ge⟩, hx'⟩ ↦ cast ... ge`.
  The counit naturality requires `groth_decompose`.
  The pointwise bijections (`counitApp`, `counitInvApp`) and
  their inverse properties are straightforward; the naturality
  proof involves reducing `counitApp` applied to a match
  expression, which requires either `native_decide`-style
  evaluation or careful manual unfolding. The main technical
  obstacle is that `counitApp` pattern-matches on a subtype
  and `simp`/`dsimp` cannot reduce the match when the argument
  is a complex expression.
- Assembly into `Equivalence` or `CategoryTheory.Equivalence`.

## Completed (Task 8: Comparison Functor)

The comparison functor
`comparisonFunctor : PshInternalPresheaf X ⥤ (X.groth ⥤ Type w)`
is fully defined and compiles.

### Definitions in `GebLean/PshInternalGrothendieck.lean`

- `comparisonFiber`: the fiber of `P` over a Grothendieck
  object.
- `comparisonPresheafMap`: the action of morphisms on
  comparison fibers.
- `comparisonPresheafMap_id`, `comparisonPresheafMap_comp`:
  functoriality.
- `comparisonPresheaf P`: the presheaf on `X.groth`.
- `comparisonNatTrans`: naturality for morphisms of internal
  presheaves.
- `comparisonFunctor`: the assembled functor.
- `comparisonFib P c`: the fiber functor at a fixed base.
