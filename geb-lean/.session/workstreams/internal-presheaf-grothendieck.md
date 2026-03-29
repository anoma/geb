# Internal Presheaf--Grothendieck Equivalence

## Status: In Progress (Tasks 1-8 complete, Task 9 partial)

## Completed

- **Task 1**: Pointwise category extraction (`fiberObj`, `fiberCategory`)
- **Task 2**: Externalization functor (`externalize : Cᵒᵖ ⥤ Cat`)
- **Task 3**: Discrete Unit compatibility (all `rfl`)
- **Task 4**: `PshInternalPresheaf` structure
- **Task 5**: `PshInternalPresheafHom` and `Category` instance
- **Task 7**: Grothendieck construction via mathlib's `Grothendieck`
- **Task 8**: `comparisonFunctor : PshInternalPresheaf X ⥤ (X.groth ⥤ Type w)`

## Files

- `GebLean/PshInternalExternalize.lean` (~620 lines)
- `GebLean/PshInternalPresheaf.lean` (~270 lines)
- `GebLean/PshInternalGrothendieck.lean` (~570 lines)

## Current blocker: `inverseFiberMap_comp`

The inverse functor's fiber presheaf needs a composition
law.  The map `inverseFiberMap X G f` sends `⟨x, e⟩` to
`⟨restrict(f)(x), G.map (grothBaseMor f x) e⟩`.

The composition law requires:

```lean
grothBaseMor (f ≫ g) x ≫ eqToHom _ =
  grothBaseMor f x ≫ grothBaseMor g (restrict(f)(x))
```

as morphisms in the Grothendieck category.  After
`Grothendieck.ext`, the base component is `rfl`, but the
fiber component involves:

```lean
eqToHom _ ≫ ((externalize X).map g).toFunctor.map
  ((eqToHom _).fiber) ≫ (𝟙 _).fiber ≫ eqToHom _
```

which needs `eqToHom.base = 𝟙` (propositional, not
definitional) followed by `eqToHom_map` and
`Functor.map_id` rewrites.

### Approach for `inverseFiberMap_comp`

The established proof pattern from
`grothBaseMor_id_comp_eqToHom` uses `subst` on the
eqToHom argument.  For composition, consider:

1. Use `Grothendieck.ext` to reduce to base + fiber
2. Base: `rfl` (both are `f.base ≫ g.base`)
3. Fiber: after `eqToHom` rewrites, should reduce to
   identity on identity composition

Alternative: define `grothBaseMor_comp` directly as a
term proof showing the two Grothendieck morphisms are
equal, bypassing `ext`.

## Design decisions

- Used mathlib's standard `Grothendieck` (covariant) on
  `Cᵒᵖ ⥤ Cat`, avoiding the project's `op'` construction
- The equivalence target is `X.groth ⥤ Type w`
  (copresheaves, covariant), matching the LEFT action of
  `PshInternalPresheaf`
- Key proof technique for fiber category functor equality:
  `fiberHom_val_eqToHom_comp` / `fiberHom_val_comp_eqToHom`
  using `subst` to eliminate `eqToHom`

## Remaining tasks

- Task 9: Complete inverse functor and equivalence
  - `inverseFiberMap_comp`
  - Assemble `inverseFiberFunctor : Cᵒᵖ ⥤ Type w`
  - Define `proj`, `action`, axioms
  - Build `inverseFunctor` on morphisms
  - Unit/counit isomorphisms
  - `pshInternalGrothendieckEquiv`
- Task 6: Span-bicategory module interpretation (skipped)
- Tasks 10-12: FunctorData generalization (pending)
- Task 13: Tests and integration (pending)

## Plan document

`docs/superpowers/plans/2026-03-28-internal-presheaf-grothendieck.md`
