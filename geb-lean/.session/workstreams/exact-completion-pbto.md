# Workstream: PER Completion of Lawvere BT Theory

## Status

Task 2 (TreePER.lean) complete.  The PER category uses
`boolAnd` for all equational conditions:
- `EqTransitive` states `boolAnd(boolAnd(rel(x,z),
  rel(z,y)), rel(x,y)) = boolAnd(rel(x,z), rel(z,y))`
- `TreePERObj` requires `rel_bool : rel ≫ isLeafEndo = rel`
  (Boolean-valued output)
- `TreePERPreMor.map_rel` is equational:
  `cfpLift X.rel (cfpMap map map ≫ Y.rel) ≫ boolAnd = X.rel`
- Identity uses `boolAnd_idem` (proved via `p.elim_uniq`)
- Composition uses `boolAnd_implies_trans`
- `eqTransitive_implies_quant` uses `boolAnd_implies_IsLeafConst`
The bridge from equational to Prop-valued `IsLeafConst`
conditions is one-directional; the converse
(`quantTransitive_implies_eq`) requires case-splitting on
Boolean global elements, which is not available in the
abstract categorical setting.

## Goal

Construct the category of T-valued partial equivalence
relations (PERs) on the binary tree type T within the
Lawvere BT theory, yielding a BT-arithmetic pretopos:
an exact category with finite limits, finite colimits,
distributivity, and a parameterized binary tree object
(PBTO), assuming only primitive recursive computation.

## Approach: T-Valued PERs (Revised)

The original approach (free equalizer completion followed
by ex/lex completion) was abandoned because:

1. The equalizer completion loses the PBTO (Lemma B
   failure: the fold does not land in the equalizer).
2. The ex/lex completion requires pullbacks and has
   complex linking conditions when combined with the
   equalizer completion.

The new approach uses partial equivalence relations on
the binary tree type T, encoded as T-valued predicates
using the leaf-true Boolean logic:

- `leaf` = true, non-leaf = false
- `AND` = grafting (`elim id beta`)
- `NOT` = fold to constant
- `OR` = De Morgan

PER objects are morphisms `T x T -> T` satisfying
equational symmetry and transitivity.  Products come
from the tree encoding (branch = pair, left/right =
projections).  The PBTO is preserved by a clean
structural induction that avoids Lemma B entirely.

## Key Mathematical Results

### PBTO Preservation

The PBTO `(T, treeEq)` is preserved because the domain
condition (the fold maps into the domain of the target
PER) is inductive: if the base and step functions map
domain elements to domain elements, so does the fold.
This replaces the non-inductive equalizer condition from
the Bunge construction.

### Product-Based Transitivity is Safe

PERs have no reflexivity section, so the trivialization
argument for product-based transitivity does not apply.
This allows transitivity to be stated as an equation
between morphisms from `T^3`, using the full product
rather than a pullback.

### Image Factorization Without Existentials

The kernel-pair PER `rel_Y . (f x f)` is directly
definable.  No existential quantification is needed for
the image factorization, making regularity straightforward.

## Implementation Plan

See `docs/superpowers/plans/2026-04-02-exact-completion-pbto.md`

## Dependencies

- `GebLean/LawvereBT.lean` (HasPBTO, elim)
- `GebLean/LawvereBTQuot.lean` (LawvereBTQuotCat)
- `GebLean/Utilities/ComputableLimits.lean` (cfpProd, etc.)
