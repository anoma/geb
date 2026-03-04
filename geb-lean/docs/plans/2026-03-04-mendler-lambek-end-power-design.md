# Mendler-Lambek Equivalence via Ends and Powers

## Goal

Express the `GExtFunctor` from the Mendler-Lambek correspondence
using ends and powers instead of restricted coends. The final
characterization:

```text
Hom(G^e(pt), Y) = end_A Hom(G(A,A), Y^(A->pt))
```

where `Y^S` denotes the power and `end_A` denotes the end in Type.

## Derivation Chain

1. Restricted coend = copower-profunctor coend
   (via `homRestrictedCopowerEquiv`)
2. Coend representably = end of hom-profunctor
   (C-valued representable coend-end duality)
3. Copower elimination via power
   (via `copowerPowerEquiv`)

## Architecture

### Task 1: RestrictedCoendAsColimit.lean

Transfer initial objects across `homRestrictedCopowerEquiv` using
`isInitialOfEquivFunctor`:

- `HasAllCopowerProfCoends` typeclass
- `HasAllHomToProfCoends.toCopowerProfCoends`
- `HasAllCopowerProfCoends.toHomToProfCoends`
- Copower-coend variants of `GExtObj`, `GExtFunctor`
- `mendlerLambekCopowerEquiv`

### Task 2: EndsAndCoends.lean

C-valued representable coend-end duality:

- For a C-valued profunctor `P : C^op x C -> D` with an initial
  cowedge (coend), show:
  `Hom(coend.pt, Y) = typeEnd(sliceProfunctorPoly_hom P Y)`
- This uses the universal property of the initial cowedge directly

### Tasks 3-4: MendlerLambekEndPower.lean

Compose tasks 1 and 2, then apply `copowerPowerEquiv`:

- `Hom(GExtObj(pt), Y) = end_A Hom((A->pt) . G(A,A), Y)`
- `= end_A Hom(G(A,A), Y^(A->pt))`
- `mendlerLambekEndPowerEquiv`

## Dependencies

```text
Task 1 (independent) ──┐
                        ├── Task 3 ── Task 4
Task 2 (independent) ──┘
```
