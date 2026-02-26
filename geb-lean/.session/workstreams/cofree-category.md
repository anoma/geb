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
- All `comp` components factored:
  `polyCofreeCatComp_castPos`,
  `polyCofreeCatComp_subpos`,
  `polyCofreeCatComp_result`,
  `polyCofreeCatComp_depth`,
  `polyCofreeCatComp_pos`,
  `polyCofreeCatComp_fiber_eq`,
  `polyCofreeCatComp_subtree_eq`
- Identity components: `polyCofreeCatId_depth`,
  `polyCofreeCatId_pos`
- Left identity (`id_comp`)
- Right identity (`comp_id`)

## Tasks

- [ ] Associativity (`comp_assoc`)
  Current status: `polyCofreeSubtreeAt_concat` gives
  HEq between shapes at different fibers
  (`PolyCofreeShape P x1` vs `PolyCofreeShape P x2`
  where `x1`, `x2` are both fiber-at-concat results).
  `eq_of_heq` cannot be applied. Need to transport `p3`
  through both `polyCofreeAnnotFiber_concat` (for the
  fiber) and `polyCofreeSubtreeAt_concat` (for the
  shape) simultaneously.  Factoring plan:
  1. Prove `polyCofreeAnnotPosConcat_assoc` as a
     standalone lemma with explicit transport of `p3`
     using both fiber and shape equalities
  2. The transport uses `subst` on
     `polyCofreeAnnotFiber_concat` to equalize fibers,
     THEN `eq_of_heq` on `polyCofreeSubtreeAt_concat`
     to equalize shapes, THEN `▸` to transport `p3`
  3. Base case (`n1 = 0`): transport is identity; `rfl`
  4. Inductive step: `congrArg` wrapping the IH
  5. In `comp_assoc`, `simp ... cast_eq` eliminates
     the `castPos` casts, then `assoc` lemma closes
     the Sigma equality via `ext`
- [ ] Category instance
- [ ] Connection lemmas
