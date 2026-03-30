# Workstream: PshInternal-Grothendieck Equivalence

## Status: Complete

The categorical equivalence
`PshInternalPresheaf X ≌ (X.groth ⥤ Type w)`
is fully formalized in
`GebLean/PshInternalGrothendieck.lean`.

## Equivalence Components

All definitions in section `Equivalence`:

### Unit (counit in forward direction)

`inverseFunctor X ⋙ comparisonFunctor ≅ 𝟭 _`

- `grothEquivUnitApp`: contracts `{ ⟨x', e⟩ | x' = p.fiber }`
  to `G.obj p`.
- `grothEquivUnitInvApp`: inverse.
- `grothEquivUnitApp_natural`: naturality w.r.t.
  Grothendieck morphisms, using `groth_decompose`.
- `grothEquivUnitIso`: pointwise isomorphism at each `G`.
- `grothEquivUnit`: the full natural isomorphism.

### Counit (unit in forward direction)

`comparisonFunctor ⋙ inverseFunctor X ≅ 𝟭 _`

- `grothEquivCounitFwd`/`grothEquivCounitInv`: forward/backward
  maps extracting/pairing fiber elements.
- `comparisonPresheafMap_grothBaseMor`: the comparison map
  along a `grothBaseMor` acts as `P.fiber.map f`.
- `comparisonPresheafMap_grothFiberMor`: the comparison map
  along a `grothFiberMor` acts as `P.actionAt`.
- `grothEquivCounitFwd_natural`: naturality of forward map.
- `grothEquivCounitHom`/`grothEquivCounitInvHom`:
  `PshInternalPresheafHom` in both directions.
- `grothEquivCounitIso`: pointwise isomorphism at each `P`.
- `grothEquivCounit`: the full natural isomorphism.

### Assembly

- `pshInternalGrothendieckEquiv`:
  `PshInternalPresheaf X ≌ (X.groth ⥤ Type w)`.

## Completed Earlier

### Task 8: Comparison Functor

- `comparisonFiber`, `comparisonPresheafMap`,
  `comparisonPresheafMap_id`, `comparisonPresheafMap_comp`,
  `comparisonPresheaf`, `comparisonNatTrans`,
  `comparisonFunctor`, `comparisonFib`.

### Task 9: Inverse Functor

- `grothBaseMor`, `inverseFiber`, `inverseFiberMap`,
  `inverseFiberFunctor`, `inverseProj`, `grothFiberMor`,
  `inverseActionAt`, `inverseAction`, `inversePresheaf`,
  `inverseNatTrans`, `inversePresheafHom`, `inverseFunctor`,
  `groth_decompose`.
