# Workstream: Endofunctor CCC for PshRelEdge

## Status

In progress -- endoIhomFunctor complete, adjunction
curry component started.

## Corrected Formula

```text
[F, G](E) = end_{(i,c)} [F(y), G(y)]^{Hom(E, y)}
```

Power indexed by `Hom(E, y(i,c))` (covariant in E).

## Completed Definitions

All in `PshRelEdgeSeparation.lean`, section `EndoIhom`.

- `endoIhomComponent`, `endoIhomFamily`, `endoIhomProd`
- `endoDinatCovar/Contra` (dinatural maps)
- Dinatural conditions: `SpanCond`, `PshCond` (src/tgt)
- `endoIhomSrc/Tgt/Rel/Obj` (presheaves + edge)
- `endoIhomMap` (functoriality in E)
- `endoIhom F G` (the complete endofunctor)
- `endoDinatSpanCond_ihomMap` + three variants
  (bifunctoriality: covar by rfl, contra by
  eta.naturality via Functor.map_comp)
- `endoIhomMapG` (functoriality in G)
- `endoIhomFunctor F` (right adjoint G -> [F, G])
- `endoIhomCurrySrcApp` (curry product component
  using object-level Closed.adj.homEquiv)

## Remaining Steps

### Step 1: Curry dinatural conditions

Show `endoIhomCurrySrcApp` satisfies `endoDinatSpanCond`
and `endoDinatPshCond`. Uses naturality of `eta` at `beta`
lifted through the base CCC adjunction.

### Step 2: Full curry map

Assemble curry as `H -> [F, G]` (natural transformation
of endofunctors). Show naturality in E.

### Step 3: Uncurry map

Given `mu : H -> [F, G]`, produce `eta : F x H -> G`.
At representable `y(i,c)`, evaluate `mu.app(y)(h)(id)`
then uncurry. At general `E`, use naturality of `mu`
and the density property: every element of `F(E)` is
determined by its behavior at representables.

### Step 4: Adjunction

Show curry and uncurry are inverse. Use `mkOfHomEquiv`.

### Step 5: MonoidalClosed instance

Package as `Closed F` with `rightAdj = endoIhomFunctor F`.
