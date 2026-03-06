# Workstream: TermCat — Binary Tree Categories

## Status

Active

## Context

Define categories constructed from binary trees (the free
monad of `polyProd X`) in `GebLean/PLang/TermCat.lean`.

Design document:
`docs/plans/2026-03-06-termcat-design.md`

The design explores six candidate categories (algebra,
Kleisli, Lawvere, coalgebra, lambda-bialgebra, co-Kleisli)
and three layered approaches (PBTO/Lawvere, tree calculus,
hybrid). The recommended starting point is the Kleisli
category of `polyFreeMPoly (polyProd X)`.

## Files

- `GebLean/PLang/TermCat.lean` — primary implementation
  (skeleton created, imports `Syntax.lean`)
- `GebLean/PLang.lean` — index (already imports
  `TermCat`)
- `docs/plans/2026-03-06-termcat-design.md` — design doc

## Dependencies

All of these are in the existing codebase:

- `polyProd X` (`PLang/Syntax.lean:42`)
- `polyFreeMPoly` (`PolyAlg.lean:3642`)
- `polyFreeMPure` (`PolyAlg.lean:3423`)
- `polyFreeMBind` (`PolyAlg.lean:3453`)
- `polyFreeMPolyUnit` (`PolyAlg.lean:8588`)
- `polyFreeMPolyMult` (`PolyAlg.lean:8625`)
- Monad laws: `polyFreeM_pure_bind` (3466),
  `polyFreeM_bind_pure` (3474),
  `polyFreeM_bind_assoc` (3494)
- `polyFixFold` (`PolyAlg.lean:308`)
- `polyFixFoldUnique_at` (`PolyAlg.lean:382`)
- `polyTranslate` (`PolyAlg.lean:2766`)
- `polyBetweenId X` (`Polynomial.lean:1431`)
- `polyCoalgCopresheafEquiv` (`CofreeCategory.lean:3327`)
- `DistributiveLaw` (`Utilities/DistributiveLaw.lean`)
- `LambdaBialgebra` (`Utilities/LambdaBialgebra.lean:26`)

## Tasks

### Phase 1: Kleisli Category and Isomorphism

- [ ] Define `treeFoldAlg` — convenience wrapper: leaf
  map + fork map into `polyTranslate A (polyProd X)`
  algebra
- [ ] Define `treeFold` — parametrized fold specialized
  to `polyProd`
- [ ] Prove `treeFold_unique` — from `polyFixFoldUnique`
- [ ] Prove binary-to-finite-branching isomorphism:
  `polyFreeMCarrier A (polyProd X) ~=`
  `A *_X polyFreeMCarrier T (polyBetweenId X)`.
  Uses fold (forward) and algebra structure (backward).
  Relates free monad of product to free monad of identity
  (list). Provides leaf/stem/fork case analysis by child
  count (0, 1, 2).
- [ ] Define `treeKleisliHom` — morphism type
  `A -> polyFreeMCarrier B (polyProd X)`
- [ ] Define `treeKleisliComp` — composition via
  bind/graft
- [ ] Define `treeKleisliId` — identity via pure/unit
- [ ] Prove category laws (`id_comp`, `comp_id`,
  `comp_assoc`) from monad laws
- [ ] Define `treeKleisliCategory` — the Category instance

### Phase 2: Tree Calculus Reduction

- [ ] Use finite-branching isomorphism to define
  leaf/stem/fork case analysis (child count 0, 1, 2)
- [ ] Define the 5 triage reduction rules as morphisms or
  coalgebra, using child-count cases
- [ ] Show confluence (non-overlapping rules)
- [ ] Define PCA structure (K and S from rules 1-2)
- [ ] Connect to GSOS if infrastructure available

### Phase 3: Lambda-Bialgebra and Topos

- [ ] Specialize distributive law to `polyProd X`
- [ ] Construct lambda-bialgebra from tree calculus
  reduction
- [ ] Explore coalgebra topos structure
- [ ] Investigate realizability connection

### Open design questions

- [ ] Paramorphism vs catamorphism for PBTO universal
  property
- [ ] Triage encoding: GSOS vs direct coalgebra vs
  child-count decomposition via isomorphism
- [ ] Realizability topos vs coalgebra topos relationship
- [ ] Unlabeled trees: use terminal object as generator?
- [ ] Child-count truncation: can 0/1/2 child cases be
  expressed as polynomial equalizer or quotient?

## Notes

- Work in `Over X` throughout; specialize to `Type` (via
  `X = PUnit`) only when useful
- Interact with binary trees only through universal
  morphisms (fold, unfold, bind, pure, etc.)
- Write one definition at a time per CLAUDE.md workflow
- The algebra category `PolyAlg (polyProd X)` is already
  defined; the Kleisli category is new
- The coalgebra category `PolyCoalg (polyProd X)` is
  already defined and known to be a topos
- Binary trees ~= finite-branching trees: the isomorphism
  `T ~= A *_X List(T)` relates free monad of product to
  free monad of identity. This gives leaf (0 children),
  stem (1 child), fork (2 children) classification.
  See design doc section "Binary-to-Finite-Branching
  Isomorphism".
