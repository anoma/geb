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

## `HasTreeEq LawvereBTQuotCat` construction

Status: not started, requires new infrastructure.

The `HasTreeEq` structure in `GebLean/TreePER.lean` asks for a morphism
`treeEq : cfpProd T T ⟶ T` satisfying Boolean-valued output, reflexivity,
symmetry, equational transitivity, and the four computation rules
(`ℓℓ`, `ℓβ`, `βℓ`, `ββ`).  The recursive `ββ` rule
`treeEq(β(a₁, a₂), β(b₁, b₂)) = boolAnd(treeEq(a₁, b₁), treeEq(a₂, b₂))`
is simultaneous (double) structural recursion on two trees.

The `TypePBTO.treeEqBT` construction for `Type u` uses a `BT.fold` with
carrier type `BT → BT` (function type), applied at the end to the second
argument.  This works in any cartesian closed category.  `LawvereBTQuotCat`
is cartesian monoidal only (its objects are the finite products `n : ℕ`
of the generator), so this approach does not transfer directly.

A single `BTMor1.fold` or `HasPBTO.elim` application cannot express
`treeEq`.  The step function `g : Fin m → BTMor1 (m + m)` only sees the
recursive results from the left and right children, not the original
parameter context.  Even with an enhanced variant that exposes the
context (e.g. a syntactic analogue of `btFoldEnhanced`), the recursive
results compare each sub-tree of the folded argument against the FULL
other argument, not against the corresponding sub-tree.  Multi-output
and state-tracking variants do not help because all recursive calls
receive the same parameter context.

Viable routes (all require new infrastructure):

- Build a constructive primitive-recursive completeness theorem for
  `LawvereBTQuotCat` (inverse of `interpU_primrec_of_ctx` in
  `LawvereBTPrimrec.lean`).  Every primitive recursive `BT × BT → BT`
  function would then lift to a `BTMor1 2` term, including the
  semantically-defined `TypePBTO.treeEqBT`.
- Simulate a Goedel encoding `BT ↔ Nat` within the Lawvere theory,
  implement natural-number equality as a `BTMor1`, and compose.  Nat
  equality on a unary encoding has the same double-recursion obstacle,
  so this likely reduces to the same problem.
- Add a primitive to `HasPBTO` or a new typeclass supporting double
  structural recursion directly (equivalent to exponentials or a
  case-analysis primitive combined with recursion).

The `HasTreeEq LawvereBTQuotCat` instance is a prerequisite for
downstream `LawvereBTPER`-specific results that depend on decidable
tree equality.  Work is blocked pending one of the routes above.
