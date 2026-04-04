# Workstream: Tree PER Finite Limits

## Status

Active

## Context

Constructing finite limits in the category of partial equivalence
relations (PERs) on the binary tree type T.

## Completed

- Terminal PER (`terminalPERObj`): relation = constant leaf.
  All four fields proved (Boolean, symmetry, transitivity).
- Terminal morphism (`terminalPERPreMor`, `terminalPERMor`):
  map = identity, uses `boolAnd_const_leaf_right`.
- Terminal uniqueness (`terminalPERPreMor_unique`,
  `terminalPERMor_unique`): any two morphisms to terminal are
  equivalent.
- `terminalPERObj_isTerminal`: uses `Limits.IsTerminal.ofUniqueHom`.
- `treePER_hasTerminal`: `Limits.HasTerminal` instance.
- Product PER definition (`prodPERRel`), all axioms, projections,
  pairing, beta laws, eta/uniqueness law.
- `prodPERFst_comp_pair`, `prodPERSnd_comp_pair`: beta laws in
  the quotient category.
- `prodPER_pair_unique`: uniqueness of pairing in the quotient.
- `prodPERFan`, `prodPERFan_isLimit`: `BinaryFan` and `IsLimit`.
- `treePER_hasLimitPair`, `treePER_hasBinaryProducts`:
  `HasBinaryProducts` (parameterized by `hSep`, `hBD`).
- `boolAnd_comm_bool`: commutativity of `boolAnd` for
  Boolean-valued arguments, using separator + dichotomy.
- Equalizer PER definition (`eqPERRel`):
  `boolAnd(X.rel(x,y), boolAnd(eqCheck(x), eqCheck(y)))` where
  `eqCheck(x) = Y.rel(f(x), g(x))`.  Manifestly symmetric up to
  boolAnd commutativity on Boolean arguments.
- `eqPERRel_bool`, `eqPERRel_symm` (using `boolAnd_comm_bool`).
- `eqPERRel_quantTransitive`, `eqPERRel_eqTransitive`.
- `eqPERObj`: equalizer PER object assembly.
- `eqPERInclPreMor`, `eqPERIncl`: inclusion pre-morphism and
  quotient morphism from `eqPERObj` to `X`.
- `eqPER_equalizes`, `eqPER_equalizes_quot`: equalizing
  condition `incl ≫ f = incl ≫ g` in both pre-morphism
  equivalence and quotient equality.

## Tasks

- [ ] Equalizer lift pre-morphism (`eqPERLiftPreMor`): map = `m.map`,
  `map_rel` proof needs `boolAnd_assoc`, `boolAnd_idem`, and the
  equalizing condition to show
  `boolAnd(Z.rel, cfpMap m m ≫ eqPERRel) = Z.rel`.
  After reducing via `boolAnd_assoc` and `m.map_rel`, the remaining
  goal is `boolAnd(Z.rel, m ≫ eqCheck) = Z.rel`, which follows from
  the equalizing condition.  The equational form requires separator +
  dichotomy or a direct `boolAnd_implies_trans`-style argument.
- [ ] Equalizer lift quotient morphism.
- [ ] Equalizer factorization: `lift ≫ incl = m`.
- [ ] Equalizer uniqueness: if `k ≫ incl = m`, then `k = lift`.
- [ ] Fork and IsLimit assembly.
- [ ] `HasEqualizers` instance.
- [ ] `HasFiniteLimits` via
  `hasFiniteLimits_of_hasEqualizers_and_finite_products`.

## Notes

The `eqPERRel` definition uses `boolAnd(X.rel, boolAnd(eqCheck(fst),
eqCheck(snd)))` rather than `boolAnd(X.rel, Y.rel(f, g))` to achieve
equational symmetry.  The symmetry proof uses `boolAnd_comm_bool`
(commutativity for Boolean-valued arguments) to swap the two
`eqCheck` terms.

The `include hSep hBD in` directive is needed before theorems whose
types don't mention the separator/dichotomy but whose proofs use them,
since Lean 4 only auto-includes section variables that appear in the
type signature.
