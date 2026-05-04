# Workstream: PER Completion of Lawvere BT Theory

## Status

Finite limits complete.  Finite coproducts and PBTO
preservation are next.

## Two-Layer Architecture

### Layer 1: Decidable PER Category (current focus)

All PER objects require `rel_bool : rel ≫ isLeafEndo = rel`
(Boolean-valued output).  This makes every object a
decidable object in the sense of nLab: the diagonal is
complemented.

Properties:

- Finite limits: PROVED (`HasFiniteLimits`)
- Finite coproducts: IN PROGRESS (initial + binary
  coproducts via tag encoding, no coequalizers needed)
- PBTO preservation: TO DO
- All objects decidable: TO DO (prove the diagonal is
  complemented)
- Coequalizers: NOT EXPECTED (transitive closure of a
  decidable relation is not in general decidable by
  primitive recursive functions)
- Regularity/exactness: NOT EXPECTED (requires
  coequalizers)

This layer constitutes the "syntax category": terms of
unlabeled binary trees with decidable type-checking by
primitive recursive functions.

### Layer 2: General PER Category (future workstream)

Drop `rel_bool`, allowing arbitrary `T`-valued relations
(not just `{leaf, treeFalse}`).  The tree value encodes
a proof witness for relatedness.

Properties gained:

- Coequalizers (transitive closure representable as
  tree-valued witness)
- Regularity and exactness
- Finite colimits

Properties lost:

- Global decidability (equality no longer decidable for
  all objects)

Uses `propAnd`/`treeAnd` (the arithmetic connectives)
instead of `boolAnd` (the Boolean connective) for the
internal logic.

## Completed Work

### TreeLogic.lean (~3043 lines)

Boolean logic on T:

- `isLeafEndo`, `treeNotEndo` (Boolean normalization,
  negation)
- `boolAnd`, `boolOr`, `boolImplies` (shallow Boolean
  connectives via `treeIte`, no recursion)
- `treeAnd` (arithmetic conjunction = grafting)
- `propAnd` (propositional conjunction via `treeIte`)
- `treeLeft`, `treeRight` (shallow destructors via
  fold-with-self trick)
- `treeLeftEndo`, `treeRightEndo` (endomorphism versions)
- `β_treeLeftEndo`, `β_treeRightEndo` (beta-reduction)
- `treeIte_compose` (nested `treeIte` distribution)
- `boolAnd_assoc` (proved from `elim_uniq` via
  `treeIte_compose`, no `IsSeparator` needed)
- `boolAnd_implies_trans` (chain rule for
  `boolAnd`-implication)
- `boolAnd_idem`, `boolAnd_fst_proj`, `boolAnd_snd_proj`
- `boolAnd_comm_bool` (commutativity for Boolean inputs,
  needs `IsSeparator` + `HasBoolDichotomy`)
- `boolAnd_implies_IsLeafConst` (bridge: equational to
  Prop-valued)
- `HasBoolDichotomy` (every Boolean global element is
  `leaf` or `treeFalse`)
- `IsLeafConst` (morphism equals constant `leaf`)

### TreePER.lean (~825 lines)

PER category:

- `EqTransitive`, `QuantTransitive` (named transitivity
  predicates)
- `eqTransitive_implies_quant` (forward bridge, no
  `IsSeparator` needed)
- `TreePERObj` with `rel`, `rel_bool`, `rel_symm`,
  `rel_trans` (all equational via `boolAnd`)
- `TreePERPreMor` with equational `map_rel`
- Identity via `boolAnd_idem`, composition via
  `boolAnd_implies_trans`
- `treePERMorEqv` (Prop-valued morphism equivalence)
- Full quotient category via `Quotient.lift2`
- `treePERCategory` instance

### TreePERLimits.lean (~2859 lines)

Finite limits (parameterized by `IsSeparator` +
`HasBoolDichotomy`):

- Terminal: `terminalPERObj` with `rel = const(leaf)`,
  `IsTerminal`, `HasTerminal`
- Products: `prodPERObj` with `rel = boolAnd(X.rel(l×l),
  Y.rel(r×r))`, projections via `treeLeftEndo`/
  `treeRightEndo`, pairing via `β`, beta/eta laws,
  `HasBinaryProducts`
- Equalizers: `eqPERObj` with `rel = boolAnd(X.rel,
  boolAnd(eqCheck_fst, eqCheck_snd))`, inclusion = `id_T`,
  `Fork`, `IsLimit`, `HasEqualizers`
- `HasFiniteLimits` via
  `hasFiniteLimits_of_hasEqualizers_and_finite_products`

### TreePERLawvereBT.lean (~311 lines)

LawvereBTQuotCat-specific:

- `BT.leaf_or_node` (case analysis for `BT` type, in
  LawvereBT.lean)
- `lawvereBT_bool_dichotomy` (Boolean global elements
  are `leaf` or `treeFalse`)
- `lawvereBTQuotCat_hasBoolDichotomy`
- `quantTransitive_implies_eq_lawvereBT` (converse of
  `eqTransitive_implies_quant` for LawvereBTQuotCat)
- `lawvereBTQuotCat_treePER_hasFiniteLimits`

### LawvereBTInterp.lean (additions)

- `lawvereBTQuotCat_isSeparator`

## Remaining Tasks

### Finite Coproducts (Layer 1)

Initial object + binary coproducts.  Uses tag encoding:
`inl(x) = branch(leaf, x)`, `inr(y) = branch(treeFalse,
y)`.  No coequalizers.

### PBTO Preservation (Layer 1)

Prove `HasPBTO (TreePERObj C)` with `(T, treeEq)` as the
PBTO.  Requires defining `treeEq` (structural tree
equality) as a morphism `T × T → T`.  Existence by
structural induction on domain preservation; uniqueness
by structural induction on `rel_X`-equivalence.

### Decidability of All Objects (Layer 1)

Prove every object in the decidable PER category is a
decidable object (diagonal is complemented).  This
follows from `rel_bool`.

### Faithful Functor Preserves Limits and Colimits

Prove that `interpFunctor : LawvereBTQuotCat ⥤ Type w`
preserves the PER category's finite limits (and later
coproducts).

### LawvereBTQuotCat Coproducts Instance

Instantiate finite coproducts for LawvereBTQuotCat's
PER category (analogous to the finite limits instance).

## Dependencies

- `GebLean/LawvereBT.lean` (HasPBTO, elim, BT)
- `GebLean/LawvereBTQuot.lean` (LawvereBTQuotCat)
- `GebLean/LawvereBTInterp.lean` (interpFunctor,
  separator)
- `GebLean/Utilities/ComputableLimits.lean` (cfpProd,
  cfpSwap, etc.)
- `GebLean/TreeLogic.lean` (Boolean logic, treeIte,
  boolAnd)
- `GebLean/TreePER.lean` (PER category)
- `GebLean/TreePERLimits.lean` (finite limits)
- `GebLean/TreePERLawvereBT.lean` (LawvereBT instances)
