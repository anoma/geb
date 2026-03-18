# Workstream: Endofunctor CCC for PshRelEdge

## Status

In progress -- `endoIhom F G` functor complete; need
functoriality in `G` for the adjunction.

## Corrected Formula

The internal hom `[F, G]` of two endofunctors is the
endofunctor sending `E` to the powered end:

```text
[F, G](E) = end_{(i,c)} [F(y(i,c)), G(y(i,c))]^{Hom(E, y(i,c))}
```

where `y(i,c) = pshRelEdgeRepresentable i c` and the
power is indexed by the external hom SET
`Hom(E, y(i,c))`. This gives covariance in `E` via
double contravariance (hom contra in E, power contra
in S).

## Completed Definitions

All in `PshRelEdgeSeparation.lean`, section `EndoIhom`.

- `endoIhomComponent F G E i c` -- powered hom
  `[F(y), G(y)]^{Hom(E, y)}` at one index
- `endoIhomFamily` -- edge family indexed by
  `(i, c, alpha : E -> y(i,c))`
- `endoIhomProd` -- dependent product of the family
- `endoDinatCovar/Contra` -- dinatural maps
- `endoDinatSpanCond/PshCond` -- dinatural conditions
  (source and target versions)
- `endoIhomSrc/Tgt F G E` -- presheaves with
  dinatural conditions (functorial in presheaf stage)
- `endoIhomRel F G E` -- restricted relation
- `endoIhomObj F G E : PshRelEdge C` -- full edge
- `endoIhomMap F G g` -- functoriality map for
  `g : E1 -> E2` (precomposition on hom-set index)
- `endoIhom F G : PshRelEdge C ==> PshRelEdge C` --
  the complete endofunctor

## Remaining Steps

### Step 1: Bifunctoriality lemma

The internal hom `[A, B]` in `PshRelEdge C` satisfies:
for `f : A' -> A` and `g : B -> B'`,
`ihom.map(g) comp pre(f) = pre(f) comp ihom.map(g)`
(pre and post composition commute). This should be
added to `PshRelEdgeExp.lean` or `Utilities/`.

### Step 2: Functoriality in G

`endoIhomMapG F eta E : endoIhomObj F G1 E -> endoIhomObj F G2 E`
for `eta : G1 -> G2`. Maps by postcomposition with eta
at each representable. The dinatural condition
preservation uses the bifunctoriality lemma (covar) and
the naturality of eta (contra).

### Step 3: Assemble right adjoint functor

`endoIhomFunctor F :
    (PshRelEdge C ==> PshRelEdge C) ==>
    (PshRelEdge C ==> PshRelEdge C)`
sending `G |-> endoIhom F G`, functorial in G.

### Step 4: Adjunction

`tensorLeft F adj endoIhomFunctor F`

The curry direction: `eta : H x F -> G` gives
`mu : H -> [F, G]` where
`mu_E(h)(alpha) = curry(eta_{y(i,c)})(H.map(alpha)(h))`.

The uncurry uses the density theorem: every element
of `F(E)` factors through representables.

### Step 5: MonoidalClosed instance

Package `Closed F` with `rightAdj = endoIhomFunctor F`
and `adj` from step 4.

## Dependencies

```text
Bifunctoriality -> MapG -> Functor -> Adjunction -> MonoidalClosed
```
