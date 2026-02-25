# Polynomial Algebra/Coalgebra Combinators

## Goal

Create `GebLean/PolyAlgUMorph.lean`: a library of combinators for
constructing `Endofunctor.Algebra` and `Endofunctor.Coalgebra` instances
for polynomial endofunctors, built from the universal morphisms in
`PolyUMorph.lean` and the algebra/coalgebra infrastructure in
`PolyAlg.lean`.

## Background

`PolyUMorph.lean` provides universal constructions (products, coproducts,
equalizers, coequalizers, exponentials) for polynomial functors as objects
of `PolyFunctorBetweenCat X Y`. `PolyAlg.lean` provides algebras and
coalgebras for individual polynomial endofunctors. This file bridges the
two: using the universal morphisms between polynomial functors to construct
combinators on their algebra and coalgebra categories.

## Design

### General pullback and pushforward

Any morphism `f : P ⟶ Q` of polynomial endofunctors induces:

- **Algebra pullback** (contravariant): precompose the structure map
  `Q(A) ⟶ A` with `f_A : P(A) ⟶ Q(A)` to get `P(A) ⟶ A`.
- **Coalgebra pushforward** (covariant): postcompose the structure map
  `A ⟶ P(A)` with `f_A : P(A) ⟶ Q(A)` to get `A ⟶ Q(A)`.

All specialized combinators below are instances of these applied to
specific universal morphisms.

### Coproduct algebras

Given `F : I → PolyEndo X` and algebras `a_i : PolyAlg (F i)` sharing
carrier `A : Over X`, construct `PolyAlg (polyBetweenCoprod I F)` via
`polyBetweenCoprodDesc`: the descent morphism assembles the individual
structure maps `F_i(A) ⟶ A` into `(∐ F_i)(A) ⟶ A`.

### Product coalgebras

Given `F : I → PolyEndo X` and coalgebras `c_i : PolyCoalg (F i)`
sharing carrier `A : Over X`, construct
`PolyCoalg (polyBetweenProd I F)` via `polyBetweenProdLift`: the lift
morphism assembles the individual structure maps `A ⟶ F_i(A)` into
`A ⟶ (∏ F_i)(A)`.

### Equalizer algebra restriction

Given `f, g : P ⟶ Q` and `a : PolyAlg P`, restrict to
`PolyAlg (polyBetweenEq f g)` by precomposing with the equalizer
inclusion `polyBetweenEqIncl`. This is `algPullback` applied to the
inclusion.

### Coequalizer coalgebra extension

Given `s, t : P ⟶ Q` and `c : PolyCoalg Q`, extend to
`PolyCoalg (polyBetweenCoeq s t)` by postcomposing with the
coequalizer projection `polyBetweenCoeqProj`. This is
`coalgPushforward` applied to the projection.

### Morphism combinators

For each construction:

- `algPullbackHom` / `coalgPushforwardHom`: if `h` is a morphism of the
  original algebras/coalgebras, the same underlying map is a morphism of
  the constructed algebras/coalgebras.
- `algPullbackFunctor` / `coalgPushforwardFunctor`: functorial versions.
- Specialized versions for each of the four constructions above.

### Exponential/currying

If the exponential adjunction (`pbCurry`/`pbUncurry`) yields a clean
algebra combinator, include it. The candidate: given `Q : PolyEndo X`
and an algebra for `Q × P`, curry the structure map. This is a stretch
goal; include if the construction compiles cleanly.

## Dependencies

- `GebLean/PolyUMorph.lean` (products, coproducts, equalizers,
  coequalizers, exponentials of polynomial functors)
- `GebLean/PolyAlg.lean` (PolyAlg, PolyCoalg, PolyEndo,
  polyEndoFunctor)
- `Mathlib.CategoryTheory.Endofunctor.Algebra`

## File placement

`GebLean/PolyAlgUMorph.lean`, imported from `GebLean.lean`.
