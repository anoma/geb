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
- Added `boolAnd_snd_const_ℓ` and `boolAnd_const_leaf_right` to
  `TreeLogic.lean` (right-identity for boolAnd with constant leaf).
- Product PER definition (`prodPERRel`): `boolAnd(leftRelCheck,
  rightRelCheck)` without `isBranch` check (avoids needing `boolAnd`
  commutativity).
- Product PER Boolean-valued and symmetry proved.
- Helper: `cfpSwap_cfpMap_diag`, `treeLeftEndo`, `treeRightEndo`.
- `boolAnd_fst_IsLeafConst` and `boolAnd_snd_IsLeafConst` in
  `TreeLogic.lean`: purely equational extraction of `IsLeafConst`
  from a conjunction.  Uses `boolAnd_const_leaf_right` /
  `boolAnd_leaf_left` + `boolAnd_assoc` + `boolAnd_idem` without
  needing `boolAnd` commutativity or `IsSeparator`.
- `HasBoolDichotomy` definition in `TreeLogic.lean`: predicate that
  every Boolean global element is either `ℓ` or `treeFalse`.
- `isLeafConst_terminal_eq_ℓ` and `quantTransitive_implies_eq` in
  `TreePER.lean`: generic conversion from `QuantTransitive` to
  `EqTransitive` under `IsSeparator` + `HasBoolDichotomy`.
- `prodPERRel_quantTransitive` in `TreePERLimits.lean`: quantified
  transitivity for the product PER, proved purely equationally using
  `boolAnd_fst_IsLeafConst`, `boolAnd_snd_IsLeafConst`, and
  component `rel_trans_prop`.
- Helper definitions: `t3Left`, `t3Right` (triple-to-triple maps),
  `factor_l`, `factor_r` (relating leftRelCheck/rightRelCheck to
  X.rel/Y.rel via t3Left/t3Right), various projection lemmas.
- `boolAnd_ℓ_treeFalse` in `TreeLogic.lean`: `boolAnd(ℓ, treeFalse)
  = treeFalse`.
- `boolAnd_fst_proj` and `boolAnd_snd_proj` in `TreeLogic.lean`:
  absorption lemmas `boolAnd(boolAnd(A,B), A) = boolAnd(A,B)` and
  `boolAnd(boolAnd(A,B), B) = boolAnd(A,B)`, using `IsSeparator` +
  `HasBoolDichotomy` + case split.
- `prodPERRel_eqTransitive`: equational transitivity via
  `quantTransitive_implies_eq`.
- `prodPERObj`: product PER object assembly.
- `prodPERFstPreMor`, `prodPERSndPreMor`: projection pre-morphisms
  with `map_rel` proved using `boolAnd_fst_proj`/`boolAnd_snd_proj`.
- `prodPERFst`, `prodPERSnd`: lifted projection morphisms.
- Beta-reduction lemmas:
  - `destructFold_cfpFst`: first projection of `destructFold` is the
    identity, proved by `elim_uniq`.
  - `destructFoldR_cfpFst`: analogous for `destructFoldR`.
  - `β_treeLeftEndo`: `β ≫ treeLeftEndo = cfpFst T T`.
  - `β_treeRightEndo`: `β ≫ treeRightEndo = cfpSnd T T`.
- `cfpMap_comp_comp`: `cfpMap (f ≫ g) (f' ≫ g') = cfpMap f f' ≫
  cfpMap g g'`.
- `prodPERPairPreMor`: pairing pre-morphism with `map_rel` proved
  using `boolAnd_assoc` + `f.map_rel` + `g.map_rel` +
  beta-reduction.
- `prodPERPair`: pairing morphism lifted to the quotient, with
  well-definedness proved using beta-reduction and `boolAnd_ℓ_ℓ`.

## Tasks

- [ ] Product beta laws: `prodPERFst ∘ pair f g = f`,
  `prodPERSnd ∘ pair f g = g`
- [ ] Product eta law: `pair (fst ∘ h) (snd ∘ h) = h`
- [ ] Equalizer PER definition and universal property

## Notes

The `boolAnd` commutativity issue was resolved without needing
commutativity: the extraction lemmas `boolAnd_fst_IsLeafConst` and
`boolAnd_snd_IsLeafConst` use the equational chain
`a = boolAnd(a, ℓ) = boolAnd(a, boolAnd(a, b)) =
boolAnd(boolAnd(a, a), b) = boolAnd(a, b) = ℓ`, which requires only
`boolAnd_const_leaf_right`, `boolAnd_assoc`, and `boolAnd_idem`.

The product transitivity is proved at the quantified (`QuantTransitive`)
level.  Converting to `EqTransitive` requires `IsSeparator cfpTerminal`
and `HasBoolDichotomy C` as hypotheses (proved for `LawvereBTQuotCat`
via `lawvereBTQuotCat_isSeparator` and `lawvereBT_bool_dichotomy`).

The projection absorption lemmas (`boolAnd_fst_proj`, `boolAnd_snd_proj`)
and all product PER constructions that use them require `IsSeparator` +
`HasBoolDichotomy`.

The beta-reduction lemmas `β_treeLeftEndo` and `β_treeRightEndo`
are proved via `destructFold_cfpFst` / `destructFoldR_cfpFst`
(which use `elim_uniq` to show the first projection of the
destructuring fold is the identity) composed with `treeLeft_β` /
`treeRight_β`.
