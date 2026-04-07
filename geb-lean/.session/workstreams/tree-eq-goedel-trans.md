# Workstream: Tree Equality via Goedel Encoding

## Status

Active

## Context

Proving properties of `treeEqG` (tree equality via Goedel
encoding), with the goal of making `treeEqG_ββ` unconditional
(currently depends on `NatEqCantorPair`) and proving
`treeEqG_trans`.

## Completed

In `GebLean/NatArith.lean`:

- `natSucc_isRSpineNatNorm`: `natSucc` preserves right-spine
  normalization.
- `toRSpineNat_step_eq_natSucc`: the step morphism of
  `toRSpineNat` equals `cfpSnd ≫ natSucc`.
- `natSucc_toRSpineNat_comm`: `natSucc` commutes with
  `toRSpineNat`.
- `natPlus_ℓ_left_eq_toRSpineNat`: `natPlus(ℓ, t) =
  toRSpineNat(t)` for all `t`.
- `natPlus_ℓ_left_rsn`: `natPlus(ℓ, m) = m` for right-spine
  normalized `m`.
- `natPlus_toRSpineNat_first`: `cfpMap toRSpineNat (𝟙 T) ≫
  natPlus = natPlus ≫ toRSpineNat`. Post-composing natPlus
  with toRSpineNat equals pre-composing toRSpineNat on the
  first argument.
- `natPlus_rsn_comm_aux`: auxiliary lemma showing
  `cfpLift (cfpSnd ≫ toRSpineNat) (cfpFst ≫ a) ≫ natPlus
  = cfpMap a (𝟙 T) ≫ natPlus` for rsn `a`. Proved via
  `p.elim_uniq`, using `natPlus_ℓ_left_rsn` for the base
  and `toRSpineNat_β` + `natPlus_succ_left` for the step.
- `natPlus_comm_rsn`: commutativity of `natPlus` for
  right-spine normalized inputs:
  `cfpLift c a ≫ natPlus = cfpLift a c ≫ natPlus`
  for rsn `a`, `c`. Uses `natPlus_rsn_comm_aux`.
- `natPlus_cancel_left_rsn`: left cancellation of `natPlus`
  under `natEq` for rsn inputs:
  `natEq(c + a, c + b) = natEq(a, b)`.
  Follows from `natPlus_comm_rsn` + `natPlus_cancel_right`.
- `natPlus_isRSpineNatNorm`: if `a` is rsn, then
  `cfpLift a b ≫ natPlus` is rsn (for any `b`).
  Uses `natPlus_toRSpineNat_first`.
- `β_toRSpineNat_eq`: `β ≫ toRSpineNat =
  cfpSnd ≫ toRSpineNat ≫ natSucc`. The normalization
  of β(l, r) is natSucc(toRSpineNat(r)).
- `natPlus_toRSpineNat_second`:
  `cfpMap (𝟙 T) toRSpineNat ≫ natPlus = natPlus`.
  The fold walks only the right spine, so normalizing the
  second argument has no effect.
- `natTriStepSingle_toRSpineNat_comm`:
  `natTriStepSingle` commutes with
  `cfpMap toRSpineNat toRSpineNat`. Proved by showing
  both projections agree: the first via
  `natSucc_toRSpineNat_comm`, the second via
  `natPlus_toRSpineNat_first` and
  `natPlus_toRSpineNat_second`.
- `natTriStep_toRSpineNat_comm`:
  `natTriStep` commutes with the double-pair normalization
  map. Follows from `natTriStep_factor` (natTriStep uses
  only cfpSnd) and `natTriStepSingle_toRSpineNat_comm`.
- `natTriHelper_isRSpineNatNorm`:
  `natTriHelper ≫ cfpMap toRSpineNat toRSpineNat =
  natTriHelper`. Both components of the triangular
  number helper are rsn. Proved via
  `elim_algebra_morphism` with
  `natTriStep_toRSpineNat_comm` as the algebra morphism
  condition, and `toRSpineNat_ℓ` for the base.
- `natTri_isRSpineNatNorm`:
  `natTri ≫ toRSpineNat = natTri`. The output of
  `natTri` is right-spine normalized. Follows from
  `natTriHelper_isRSpineNatNorm` by projecting the
  second component.
- `cfpMap_id_comp'`: `cfpMap (𝟙 A) (f ≫ g) =
  cfpMap (𝟙 A) f ≫ cfpMap (𝟙 A) g`.
- `cfpMap_id_cfpSnd_eq_cfpAssocSnd`:
  `cfpMap (𝟙 A) (cfpSnd B D) = cfpAssocSnd A B D`.
- `cfpMap_id_cfpLift_cfpAssocSnd`:
  `cfpMap (𝟙 A) (cfpLift f (𝟙 D)) ≫ cfpAssocSnd = 𝟙`.
- `natSucc_natTriHelper`:
  `cfpMap (𝟙 1) natSucc ≫ natTriHelper =
  natTriHelper ≫ natTriStepSingle`.
- `toRSpineNat_natTriHelper`:
  `cfpMap (𝟙 1) toRSpineNat ≫ natTriHelper =
  natTriHelper`. Proved via `p.elim_uniq`.
- `toRSpineNat_natTri`:
  `toRSpineNat ≫ natTri = natTri`.
- `natPlus_toRSpineNat_both`:
  `cfpMap toRSN toRSN ≫ natPlus = natPlus ≫ toRSN`.
- `cantorPair_toRSpineNat_comm`:
  `cfpMap toRSN toRSN ≫ cantorPair =
  cantorPair ≫ toRSpineNat`.

In `GebLean/TreeGoedel.lean`:

- `treeToNatParam_rsn`:
  `treeToNatParam ≫ toRSpineNat = treeToNatParam`.
- `treeToNat_isRSpineNatNorm`:
  `treeToNat ≫ toRSpineNat = treeToNat`.

In `GebLean/TreeGoedel.lean`:

- `natEq_ℓ_right`: `natEq(a, ℓ) = isLeafEndo(a)`.
  Proved by expanding natEq definition and using
  `natTruncSub_ℓ`, `natTruncSub_ℓ_left`, and
  `natPlus_zero`.

In `GebLean/NatArith.lean`:

- `natTruncSub_β_β`:
  `cfpMap p.β p.β ≫ natTruncSub =
  cfpMap (cfpSnd T T) (cfpSnd T T) ≫ natTruncSub`.
  The left children are irrelevant to `natTruncSub`.
  Proof factors `cfpMap p.β p.β` via `cfpMap_comp`,
  applies `natTruncSub_β` to peel the second-argument
  β, then `β_natTruncSub_natPred` to peel the
  first-argument β.
- `natEq_β_β`:
  `cfpMap p.β p.β ≫ natEq =
  cfpMap (cfpSnd T T) (cfpSnd T T) ≫ natEq`.
  The left children are irrelevant to `natEq`.
  Proof unfolds `natEq`, applies `natTruncSub_β_β`
  to both the direct and swapped `natTruncSub`
  components (the swapped case uses
  `cfpSwap_cfpMap_diag`), then recombines via
  `cfpLift_precomp`.

In `GebLean/NatArith.lean` (new definitions and lemmas):

- `cantorNextPair`: the step of the Cantor unpairing
  zig-zag walk. From `(a, b)`: if `b = 0` then `(0, succ(a))`,
  else `(succ(a), pred(b))`.
- `cantorUnpairStep`: `cfpSnd ≫ cantorNextPair`, the
  step morphism for the unpairing catamorphism.
- `cantorUnpairHelper`: parameterized catamorphism computing
  the Cantor unpairing via `p.elim (cfpLift ℓ ℓ)
  cantorUnpairStep`.
- `cantorUnpairFst`, `cantorUnpairSnd`: first and second
  components of the Cantor unpairing.
- `cantorUnpairHelper_ℓ`: base case.
- `cantorUnpairHelper_β`: step case.
- `cantorPair_succ_fst`: `cantorPair(succ(a), b) =
  succ(cantorPair(a, succ(b)))`. Proved using
  `natPlus_succ_left`, `natPlus_succ`.
- `cantorPair_ℓℓ`: `cantorPair(ℓ, ℓ) = ℓ`.

## Remaining

### `cantorPair_cantorNextPair` -- PROVED

`cantorNextPair ≫ cantorPair = cantorPair ≫ natSucc`.

Proved via `paraElim_uniq`.  Both sides satisfy the
same paramorphism base and step equations.  The step
`cantorPairParaStep` extracts `succ(a)` and `r` from
the paramorphism data (ignoring sub-results) and
applies `cantorPair`.  `cantorPairParaStep_precomp`
shows the step pre-composition simplifies.

### `cantorUnpairHelper_cantorPair` -- PROVED

`cantorUnpairHelper ≫ cantorPair =
  p.elim ℓ (cfpSnd T T ≫ natSucc)`.

Proved via `elim_algebra_morphism` using
`cantorPair_cantorNextPair` to verify the algebra
morphism condition.

### `cantorUnpair_cantorPair` -- PROVED

In `GebLean/NatNNO.lean`:

- `cantorUnpair`: `T ⟶ T × T`, defined as
  `cfpLift (cfpTerminalFrom T) (𝟙 T) ≫
  cantorUnpairHelper`.
- `cantorUnpair_cantorPair`:
  `cantorUnpair ≫ cantorPair = toRSpineNat`
  (retraction property).
- `cantorUnpair_ℓ`:
  `ℓ ≫ cantorUnpair = cfpLift ℓ ℓ`.
- `cantorUnpair_natSucc`:
  `natSucc ≫ cantorUnpair =
  cantorUnpair ≫ cantorNextPair`.
- `cantorPair_absorbs_rsn`:
  `cfpMap toRSN toRSN ≫ cantorPair = cantorPair`.
- `cantorPair_absorbs_rsn_fst`:
  `cfpMap toRSN (𝟙 T) ≫ cantorPair = cantorPair`.
- `cantorPair_ℓ_snd`:
  `cfpLift (term ≫ ℓ) (𝟙 T) ≫ cantorPair =
  toRSN ≫ natTri`.

### `cantorPair_cantorUnpair` -- NOT YET PROVED

`cantorPair ≫ cantorUnpair =
cfpMap toRSpineNat toRSpineNat`
(section property).

The proof requires double induction (outer on first
argument `a`, inner on second argument `b` for the
base case).  The step condition for `nnoElim_uniq`
on the second argument is hard because
`cantorPair(a, succ(b))` relates to
`cantorPair(succ(a), b)` via `cantorPair_succ_fst`
rather than to `cantorPair(a, b)` directly.
Approaches attempted:

- Direct `nnoElim_uniq` on second argument: step
  condition is circular.
- `nnoElim_uniq` on first argument via `cfpSwap`:
  requires base case `cantorUnpair(natTri(toRSN(b)))
  = (ℓ, toRSN(b))` which needs inner induction.
- Absorption lemma
  `cfpMap (𝟙 1) toRSN ≫ cantorUnpairHelper =
  cantorUnpairHelper`: in progress.

### `NatEqCantorPair` / unconditional `treeEqG_ββ`

`NatEqCantorPair` remains unproved.

#### Proved lemmas

- `natPlus_cancel_left` (unrestricted):
  `natEq(c + a, c + b) = natEq(a, b)` for all
  `a, b, c` without normalization hypotheses.
  Proof: normalize all three arguments via
  `toRSpineNat`, then apply
  `natPlus_cancel_left_rsn`.  Uses
  `natEq_toRSpineNat`,
  `natPlus_toRSpineNat_first`,
  `natPlus_toRSpineNat_second`, and
  `toRSpineNat_idem`.

- `natTri_isLeafEndo`:
  `natTri ≫ isLeafEndo = isLeafEndo`.
  `natTri` preserves leaf/branch classification.
  Proof via `p.elim_uniq`: both
  `natTriHelper ≫ cfpSnd ≫ isLeafEndo` and
  `cfpSnd ≫ isLeafEndo` have the same base (ℓ)
  and step (`cfpTerminalFrom ≫ treeFalse`).
  The step for the LHS uses `natTriStep_cfpSnd`
  (which has `natPlus(succ(...), ...)` in the
  second component) and `natPlus_succ_left` +
  `natSucc_isLeafEndo` to show the step yields
  `treeFalse`.

- `natSucc_isLeafEndo'` (private, in NatArith):
  `natSucc ≫ isLeafEndo = cfpTerminalFrom T ≫
  treeFalse`.  Duplicates the lemma from
  TreeGoedel for use in NatArith.

- `toRSpineNat_isLeafEndo`:
  `toRSpineNat ≫ isLeafEndo = isLeafEndo`.
  (Proved in a previous session.)

#### Proof analysis

The equation `NatEqCantorPair` states:
`natEq(CP(a,b), CP(c,d)) =
  boolAnd(natEq(a,c), natEq(b,d))`
where `CP(a,b) = natPlus(natTri(a+b), a)`.

By `boolAnd_comm`, it suffices to show BOTH:

- `boolAnd(LHS, RHS) = LHS` (injectivity)
- `boolAnd(RHS, LHS) = RHS` (congruence)

**Congruence direction** (RHS to LHS):
If `natEq(a,c) = ℓ` and `natEq(b,d) = ℓ`, then
`natEq(CP(a,b), CP(c,d)) = ℓ`.  The chain:

1. `natEq(a+b, c+b) = natEq(a, c) = ℓ`
   (by `natPlus_cancel_right`).
2. `natEq(c+b, c+d) = natEq(b, d) = ℓ`
   (by `natPlus_cancel_left`).
3. By transitivity: `natEq(a+b, c+d) = ℓ`.
4. `natTri` preserves natEq equality (since it
   only walks right spines).
5. `natPlus` right-cancellation: equal sums and
   equal left addends give equal totals.

**Injectivity direction** (LHS to RHS):
If `natEq(CP(a,b), CP(c,d)) = ℓ`, then
`natEq(a,c) = ℓ` and `natEq(b,d) = ℓ`.

The congruence direction can be expressed as
categorical morphism equalities using
`boolAnd_implies_trans` and related lemmas.
It requires intermediate lemmas:

- `natEq_natPlus_compat`: compatibility of
  `natPlus` with `natEq` -- if `boolAnd(natEq(a1,
  a2), natEq(b1, b2)) = boolAnd(...)`, then
  `natEq(a1+b1, a2+b2)` follows.
- `natEq_natTri_compat`: compatibility of `natTri`
  with `natEq` -- `natEq(natTri(x), natTri(y)) =
  natEq(x, y)`.

The injectivity direction is harder.  Approaches:

- Prove the section property:
  `cantorPair ≫ unpair = cfpMap toRSN toRSN`
  where `unpair = cfpLift (cfpTerminalFrom T)
  (𝟙 T) ≫ cantorUnpairHelper`.
  Then `natEq(CP(a,b), CP(c,d))` decomposes via
  the unpair section.

- Alternatively, prove
  `natEq(natTri(x), natTri(y)) = natEq(x, y)`
  (natTri cancellation) which handles the base
  case of induction on `a`, and then use
  `cantorPair_succ_fst` + `natEq_succ_cancel`
  for the step case.  The `natTri` cancellation
  itself requires a joint induction on
  `natEq(f(a), f(b)) = natEq(a, b)` and
  `natEq(f(a)+a, f(b)+b) = natEq(a, b)` where
  `f = natTri`, using the triangular number
  recurrence `natTri(succ(a)) =
  succ(natPlus(a, natTri(a)))`.

Both approaches require substantial work (many
intermediate lemmas, each 10-50 lines).

### `treeEqG_trans`

Transitivity of `treeEqG`, using `natTruncSub_fold_comp`
and the right-spine preservation lemmas.
