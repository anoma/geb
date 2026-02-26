# Workstream: Coalgebra-Copresheaf Equivalence

## Status

Active

## Context

Proving that for a polynomial endofunctor P on Over X,
the category of P-coalgebras is equivalent to the
category of copresheaves on the cofree category:
`PolyCoalg P ≌ PolyCofreeCat P ⥤ Type u`.

## Mathematical Background

See `.session/docs/coalgebra-copresheaf-math.md` for
detailed mathematical findings from the literature.

## Tasks

### Phase 1: Functor-Coalg ≌ Comonad-Coalg

- [ ] Check mathlib for comonadicity infrastructure
- [ ] `polyCoalgToComonadCoalg` functor
- [ ] `polyComonadCoalgToCoalg` functor
- [ ] Roundtrip isomorphisms
- [ ] `polyCoalgComonadEquiv`

### Phase 1b: Functor-Alg ≌ Monad-Alg (dual)

- [ ] `polyAlgToMonadAlg` functor
- [ ] `polyMonadAlgToAlg` functor
- [ ] Roundtrip isomorphisms
- [ ] `polyAlgMonadEquiv`

### Phase 2: Copresheaf Functor

- [ ] `polyCofreeCopresheafAt` : value at an object
- [ ] `polyCofreeCopresheafMap` : action on morphisms
- [ ] `polyCofreeCopresheaf A` : the copresheaf functor

### Phase 3: Comonad-Coalg ≌ Copresheaves

- [ ] `comonadCoalgToCopresheaf` (Phi)
- [ ] `copresheafToComonadCoalg` (Psi)
- [ ] Roundtrip isomorphisms
- [ ] `comonadCoalgCopresheafEquiv`

### Phase 4: Compose

- [ ] `polyCoalgCopresheafEquiv`
