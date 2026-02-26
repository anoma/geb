# Workstream: Cofree Category

## Status

Active

## Context

Constructing the cofree category C_P for a polynomial
endofunctor P, such that the category of P-coalgebras is
equivalent to the copresheaf topos Set^{C_P}.

## Completed

- Comonad from adjunction (`polyCofreeComonad`)
- Natural isomorphism (`polyCofreeComonadIso`)
- Free monad analog (`polyFreeMonad`, `polyFreeMonadIso`)
- Cofree comonoid: subtree, path concat, counit, comult
- Free monoid: graft, leaf split, unit, mult
- Cofree category objects (`PolyCofreeCat`)
- Cofree category morphisms (`PolyCofreeCatHom`)
- All `comp` components factored out as named definitions
- Identity components factored out
- Left identity, right identity, associativity
- `Category` instance on `PolyCofreeCat P`

## Tasks

- [ ] Connection lemmas: hom-sets correspond to
      `PolyCofreeAnnotPos` (the polynomial directions)
- [ ] Show that the comonoid structure (counit, comult)
      evaluates to the comonad's counit and comult
