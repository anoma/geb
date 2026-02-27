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

- [x] Check mathlib for comonadicity infrastructure
  - Mathlib has `Comonad.comparison`,
    `Comonad.Coalgebra`, Beck's theorem
    (`comonadicOfHasPreserves...`)
- [x] `polyCoalgToComonadCoalg` functor
  (via `Comonad.comparison`)
- [x] `polyComonadCoalgToCoalg` functor
  (structure: `k ≫ cofreeStr ≫ P.map(counit)`)
- [x] Forward roundtrip `K⁻¹(K(α)).str = α.str`
  (`polyCoalgComonad_forward_str`)
- [x] Backward roundtrip `K(K⁻¹(c)).a = c.a`
  (`polyCoalgComonad_backward`)
  Proven coinductively using self-consistency
  (`comonadCoalgSelfconsistent`) derived from
  coassociativity.
- [x] `polyCoalgComonadEquiv`

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
