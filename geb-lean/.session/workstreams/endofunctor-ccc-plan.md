# Workstream: Endofunctor CCC for PshRelEdge

## Status

In progress -- building the powered end with corrected
variance.

## Goal

We need `MonoidalClosed (PshRelEdge C ⥤ PshRelEdge C)` --
the endofunctor category of `PshRelEdge C` is cartesian
closed.

## Corrected Formula (2026-03-18)

The internal hom `[F, G]` of two endofunctors is the
endofunctor sending `E` to the powered end:

```
[F, G](E) = ∫_{(i,c)} [F(y(i,c)), G(y(i,c))]^{Hom(E, y(i,c))}
```

where `y(i,c) = pshRelEdgeRepresentable i c` and the
power is indexed by the external hom SET `Hom(E, y(i,c))`
(morphisms from `E` to the representable in
`PshRelEdge C`).

**Variance**: `Hom(E, y)` is contravariant in `E`
(precomposition), and the power `A^S` is contravariant
in `S`. Double contravariance gives the needed
**covariance** in `E`.

**Previous error**: The plan incorrectly used
`E(c,i) = Hom(y(c,i), E)` (Yoneda evaluation, covariant
in E) as the power index, which gave contravariance.
The Yoneda lemma gives `Hom(y(c), E) = E(c)`, NOT
`Hom(E, y(c)) = E(c)`.

## Mathlib Gap (discovered 2026-03-18)

Mathlib does NOT provide `MonoidalClosed` for ANY
endofunctor category. The generic
`MonoidalClosed (J ⥤ C)` instance requires
`HasEnrichedHom C F₁ F₂` for all functor pairs, which
is `HasEnd (diagram C F₁ F₂)`, requiring a limit
indexed over the `Under j` category -- one universe
level too large.

## Current Construction

All definitions are in `PshRelEdgeSeparation.lean`,
section `EndoIhom`.

### Completed

- `endoIhomComponent F G E i c` -- the powered hom
  `[F(y), G(y)]^{Hom(E, y)}` at a single index
- `endoIhomFamily` -- the family of edges indexed by
  `(i, c, α : E ⟶ y(i,c))`
- `endoIhomProd` -- the dependent product of the family
- `endoDinatCovar`, `endoDinatContra` -- the dinatural
  transformation maps
- `endoDinatSpanCond`, `endoDinatPshCond` -- dinatural
  conditions on source presheaf
- `endoDinatSpanCondTgt`, `endoDinatPshCondTgt` -- same
  for target
- `endoIhomSrc F G E` -- source presheaf (subtype of
  product satisfying dinatural conditions)
- `endoIhomTgt F G E` -- target presheaf (same)

### Remaining Steps

1. `endoIhomRel F G E` -- the relation (restrict product
   relation to the dinatural subtypes)
2. `endoIhomObj F G E : PshRelEdge C` -- assemble
   src/tgt/rel into an edge
3. `endoIhom F G : PshRelEdge C ⥤ PshRelEdge C` --
   functoriality in `E` via precomposition on the
   hom-set index: `g : E₁ ⟶ E₂` gives
   `h ↦ (α₂ ↦ h(g ≫ α₂))`
4. Adjunction: `tensorLeft F ⊣ endoIhom F`
5. `MonoidalClosed` instance

## Dependencies

```text
Power → Diagram → End → Functoriality → MonoidalClosed
                                              ↓
                                        Task #156 → Task #157
```
