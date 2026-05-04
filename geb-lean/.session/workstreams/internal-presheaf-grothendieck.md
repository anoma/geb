# Internal Presheaf--Grothendieck Equivalence

## Status: COMPLETE (equivalence proved)

## Result

```lean
def pshInternalGrothendieckEquiv :
    PshInternalPresheaf X ≌
      (X.groth ⥤ Type w)
```

where `X.groth = Grothendieck (externalize X)`.

## Files

- `GebLean/PshInternalExternalize.lean` (~620 lines)
- `GebLean/PshInternalPresheaf.lean` (~270 lines)
- `GebLean/PshInternalGrothendieck.lean` (~1834 lines)

Total: ~2724 lines, all constructive, no sorry.

## Remaining from original plan

- Task 6: Span-bicategory module interpretation
- Tasks 10-12: FunctorData generalization
- Task 13: Tests and integration
