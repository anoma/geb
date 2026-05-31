# Idris area-partition notes

Records the assignment decisions behind `_coverage.tsv` (77 non-test
modules → 9 areas). The coverage check enforces totality and
disjointness; this file records the judgment calls a reviewer might
question. Each module has the chosen home and the defensible
alternative.

## Rule

Assignment is by dominant import / namespace, except that a module
named explicitly in an area's seed list keeps that placement even when
its dominant import points elsewhere.

## Contested calls

- `SlPolyIntCat.idr` — chosen `internal-cats-profunctors` (it presents
  slice-polynomial functors as internal categories); alternative
  `polynomial-functors`.
- `MLQuivCat.idr`, `MLQuivUniv.idr`, `MLQuivPoly.idr` — chosen
  `foundational-cats` (grouped with `Quiver`); alternative
  `polynomial-functors` for `MLQuivPoly`, which also imports `PolyCat`.
- `FullLanguageDef.idr` — chosen `logic-refinement` (it assembles the
  language atop the logic/effects/refinement substrate it imports);
  alternative `geb-language`.
- `Figures.idr`, `Telescope.idr` — chosen `metaprogramming-syntax` by
  explicit naming, overriding their dominant `PolyCat`/`SlicePolyCat`
  import; alternative `polynomial-functors`.
- `RopeCat.idr`, `FinCatPRA.idr` — chosen `foundational-cats`
  (`RopeCat` builds on `HelixCat`; `FinCatPRA` is finite-category
  parametric-right-adjoint machinery); alternatives
  `polynomial-functors` (`RopeCat` imports `PolyCat`) and
  `recursion-targets` (`FinCatPRA` imports `BinTree`).
- `SlicePolyDifunc.idr` — chosen `polynomial-functors` (dominant
  slice-polynomial imports); alternative `internal-cats-profunctors`
  with the other difunctor modules.
