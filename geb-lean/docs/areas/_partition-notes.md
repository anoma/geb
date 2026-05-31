# Lean area-partition notes

Records the assignment decisions behind `_coverage.tsv` (215 source
files — `GebLean.lean` plus 214 under `GebLean/`, excluding
`GebLeanTests/` — → 10 areas). The coverage check enforces totality and
disjointness; this file records the judgment calls a reviewer might
question.

## Construction

Each area is seeded from the `Source-tree paths` bullet of its
workstream in `docs/index.md` (eight topical workstreams), plus the
files mentioned nowhere in the index, plus one file mentioned only in
the K_sim Dependencies prose. The `nno-arithmetic-topos` and
`utilities` areas have no index workstream and are built entirely from
the index-unmentioned files.

## Utilities split

`utilities` (A10) holds only the `Utilities/*.lean` files **not**
claimed by a topical workstream, plus the two aggregators
(`Utilities.lean`, `GebLean.lean`). Topical workstreams already
enumerate the `Utilities/*` files they document (e.g.
`Utilities/Profunctors.lean` → profunctors-ends,
`Utilities/KArith.lean` → lawvere-er-ksim).

## Disjointness reassignments

These paths are listed under two workstreams in `docs/index.md`; each
is kept in exactly one area, and the other area references it in prose
without a coverage link:

- `Utilities/PolyCombinators.lean` — `polynomial-functors` only
  (also listed under Tree calculus).
- `Paranatural.lean`, `ParanatAlg.lean` — `profunctors-ends` only
  (also listed under Polynomial).

## Index-only mention

- `LawvereTreeER.lean` — a real source file cited only in the K_sim
  workstream's Dependencies prose, not in any `Source-tree paths`
  bullet, and not among the index-unmentioned files. Assigned
  `lawvere-er-ksim`, with its `Arith`/`Interp`/`Quot` siblings.

## Contested calls

- `CategoryPresentation.lean` — chosen `quivers` (presentations by
  generators and relations); alternative `category-judgments`.
- `CatValuedFunctor.lean` — chosen `category-judgments` (supports the
  2-categorical `L ⊣ Φ` analysis); alternative `profunctors-ends`.
- `PLang.lean` (aggregator) — chosen `category-judgments`; the `PLang/`
  directory spans both `category-judgments` and `tree-calculus`.
- `FreeToposBT.lean` — chosen `polynomial-functors`; alternative
  `nno-arithmetic-topos`.
- `DinaturalNumbers.lean` — chosen `profunctors-ends`; alternative
  `nno-arithmetic-topos`.
- Tree split: `TreePER*.lean`, `TypePBTO.lean` → `polynomial-functors`
  (PER/completion side) versus `TreeGoedel.lean`, `TreeEqGoedel.lean`,
  `TreeLogic.lean` → `lawvere-er-ksim` (Gödel-numbering side).
- `GebLean.lean` (root aggregator) — chosen `utilities`.
