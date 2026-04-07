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

#### Detailed analysis (session 2026-04-06)

The proof has three main parts:

**Part A: Step case (`a1 = succ, a2 = succ`).**
Using `cantorPair_succ_fst`:
`CP(succ(a1), b1) = succ(CP(a1, succ(b1)))`.
Combined with `natEq_succ_cancel`:
`natEq(succ(CP(a1,s(b1))), succ(CP(a2,s(b2))))
= natEq(CP(a1,s(b1)), CP(a2,s(b2)))`.
By IH (with shifted b1, b2):
`= boolAnd(natEq(a1,a2), natEq(s(b1),s(b2)))
= boolAnd(natEq(a1,a2), natEq(b1,b2))`.
This step works cleanly.

**Part B: Base case (`a1 = ℓ, a2 = ℓ`).**
`natEq(CP(ℓ,b1), CP(ℓ,b2))
= natEq(natTri(b1), natTri(b2))`.
Needs `natTri` cancellation:
`cfpMap natTri natTri ≫ natEq = natEq`.
Base of natTri cancellation works via
`natTri_ℓ`, `natTri_isLeafEndo`, `natEq_ℓ_right`.
Step is problematic: the recurrence
`natTri(s(n)) = natPlus(s(toRSN(n)), natTri(n))`
couples the IH with `natPlus`, and the
`natPlus` components differ between LHS and RHS,
preventing direct cancellation.

**Part C: Cross cases (`a1 = ℓ, a2 = succ` or
vice versa).**
Need: `natEq(natTri(b1),
succ(CP(a2', succ(b2)))) = treeFalse`.
Equivalently: no triangular number equals
`succ(CP(a,succ(b)))` for any `a, b`.
Since `CP(a,s(b))` lies strictly inside
diagonal `a+s(b)`, `succ(CP(a,s(b)))` lies
between consecutive triangular numbers
`natTri(a+s(b))` and `natTri(a+s(b)+1)`.
Proving this categorically requires a "gap"
lemma about triangular number spacing.

**Viable strategies:**

1. **Section property approach**: prove
   `cantorPair ≫ cantorUnpair =
   cfpMap toRSN toRSN` (section), then use it
   to decompose `natEq(CP(x), CP(y))` through
   `cantorUnpair`.  This avoids natTri
   cancellation entirely.  The section property
   requires: (a) base case
   `CU(natTri(n)) = (ℓ, toRSN(n))` by fold
   on `n` via `cantorNextPair`, and (b)
   step case using `cantorPair_succ_fst` +
   `cantorUnpair_natSucc`.

2. **triRoot approach**: define `triRootState`
   as a 1D fold tracking `(diagonal, offset)`,
   prove band property
   `CP ≫ triRootState = cfpLift
   (natPlus ≫ toRSN) (cfpFst ≫ toRSN)`,
   then derive injectivity.  Essentially
   equivalent to the section property but
   with a different state representation.

3. **Cancellation lemma approach**: prove
   `natTruncSub(natPlus(c, a), c) = toRSN(a)`
   by fold on `c` using `natTruncSub_succ_succ`
   and `natPlus_succ_left`.  Then use this to
   derive natTri cancellation and the gap
   property.

Estimated total: 400-600 lines of lemmas.

#### Progress (session 2026-04-06b)

In `GebLean/NatNNO.lean`, defined and proved:

- `triRootStep`: step morphism for the diagonal walk,
  using `iteBranches` on the condition
  `natTruncSub ≫ isLeafEndo`.
- `triRootState`: NNO fold tracking
  `(diagonal, offset)` via `nnoElim` with base
  `(ℓ, ℓ)` and step `triRootStep`.
- `triRoot`, `triRootOffset`: projections of
  `triRootState` to diagonal index and offset.
- `triRootState_ℓ`: base case `(ℓ, ℓ)`.
- `triRootState_s`: step case
  `natSucc ≫ triRootState =
  triRootState ≫ triRootStep`.
- `triRoot_ℓ`, `triRootOffset_ℓ`: base cases
  for projections.
- `triRootStep_diag`: when `s = rem`,
  `triRootStep(s, s) = (s+1, ℓ)`.
- `triRootStep_within`: when
  `natTruncSub(s, rem) = r ≫ β`,
  `triRootStep(s, rem) = (s, rem+1)`.
- `natTruncSub_diag`: `natTruncSub(s, s) =
  cfpTerminalFrom ≫ ℓ` at a general domain.
- `natTruncSub_natPlus_cancel'`:
  `natTruncSub(natPlus(x, a), a) = x` at a
  general domain.
- `triRootStep_natPlus_succ`: when the pair is
  `(natPlus(succ(b), a), a)`, the step stays
  within the diagonal:
  `(natPlus(succ(b), a), succ(a))`.
- `triRootState_toRSpineNat`:
  `toRSpineNat ≫ triRootState = triRootState`.
- `triRoot_toRSpineNat`:
  `toRSpineNat ≫ triRoot = triRoot`.
- `triRootOffset_toRSpineNat`:
  `toRSpineNat ≫ triRootOffset = triRootOffset`.
- `natTri_ℓ_triRoot`:
  `ℓ ≫ natTri ≫ triRoot = ℓ`.
- `natTri_ℓ_triRootOffset`:
  `ℓ ≫ natTri ≫ triRootOffset = ℓ`.

The import was changed from `GebLean.NatArith` to
`GebLean.TreeGoedel` to access
`natSucc_isLeafEndo` and `natEq_ℓ_right`.

#### Progress (session 2026-04-06c)

Additional lemmas proved in `GebLean/NatNNO.lean`:

- `natPlus_triRootState`:
  `natPlus ≫ triRootState =
  nnoElim triRootState triRootStep`.
  Adding `k` to a number and computing
  `triRootState` equals iterating `triRootStep`
  `k` times on the `triRootState` of the original.
  Proved by `nnoElim_uniq`.

- `natTri_succ_eq_succ_cantorPairAt0`:
  `natSucc ≫ natTri =
  (cfpLift (𝟙) (cfpTerminalFrom ≫ ℓ) ≫
  cantorPair) ≫ natSucc`.
  The successor triangular number is one past the
  last point of diagonal n.  Uses
  `natTri_natSucc`, `embed_natTriHelper_cfpFst`,
  `natPlus_succ_left`, `natPlus_comm_rsn`, and
  `natPlus_toRSpineNat_second`.

Made `embed_natTriHelper_cfpFst` non-private in
NatArith.lean so NatNNO.lean can reference it.

#### Analysis of remaining obstacle

The natTri band property
`natTri ≫ triRootState =
cfpLift toRSN (cfpTerminalFrom T ≫ ℓ)`
and the full band property
`cantorPair ≫ triRootState =
cfpLift (natPlus ≫ toRSN) (cfpFst ≫ toRSN)`
are mutually dependent:

- The natTri band step at `succ(n)` requires
  `triRootState(cantorPair(n, 0)) =
  (toRSN(n), toRSN(n))` (the "diagWalkEnd"
  lemma), which is the full band at `(n, 0)`.

- The full band base case at `a = ℓ` requires
  the natTri band for all `b`.

Both require an inner "walk within diagonal"
iteration: starting from
`(toRSN(n), ℓ)` and applying `triRootStep` `n`
times to reach `(toRSN(n), toRSN(n))`.
This inner walk depends on
`triRootStep_natPlus_succ` (proved), but it
cannot be expressed as a simple single fold
because the number of steps equals the diagonal
number (a dependent quantity).

Attempted strategies that did not close:

1. `nnoElim_uniq` on natTri argument: step
   requires diagWalkEnd, which is circular.
2. `nnoElim_uniq` on the first arg of cantorPair
   (swapped): base requires natTri band.
3. Combined fold `natTriBandTarget` tracking both
   `(triRootState(natTri(n)),
   triRootState(cantorPair(n, 0)))`: the step for
   the second component involves
   `cantorPair(n, 1)` (not `cantorPair(n, 0)`),
   so it is not a simple function of the state.
4. PBTO fold approach: `natTriStep ≫ cfpSnd ≫
   triRootState` involves `natPlus ≫ triRootState`
   which again requires the inner walk.

Remaining path forward:

The walk within diagonal n (from offset 0 to
offset n) is an inherently nested iteration.
To prove it, one approach is:

- Define a `pairElim` (F x F algebra fold) that
  tracks `(natTriHelper state,
  triRootState of the second component)`
  simultaneously through the PBTO tree structure.
  The PBTO fold naturally handles the right-spine
  walk (which counts the diagonal), while
  `triRootStep` handles the within-diagonal walk.

- Alternatively, prove a "diagonal walk" lemma
  by strong induction on the natural number value
  (if a strong induction principle is available),
  or by a double fold using an explicit counter
  for the remaining steps within the diagonal.

#### Progress (session 2026-04-06d)

New definitions and lemmas in `GebLean/NatNNO.lean`:

- `simpleTriRootStep`: the offset-incrementing step
  morphism `(s, r) ↦ (s, natSucc(r))`, which always
  increments the second component without checking
  the diagonal boundary.
- `simpleDiagWalk`: the NNO fold with base
  `(s, ℓ)` and step `simpleTriRootStep`.
- `simpleDiagWalk_ℓ`: base case.
- `simpleDiagWalk_s`: step case.
- `simpleDiagWalk_eq`:
  `simpleDiagWalk = cfpLift cfpFst (cfpSnd ≫ toRSN)`.
  The simple walk preserves the first component and
  normalizes the second.  Proved via `nnoElim_uniq`.

#### Updated analysis (session 2026-04-06d)

The `cantorPair_succ_fst` recurrence gives:
`cfpMap natSucc (𝟙 T) ≫ cantorPair ≫ triRootState
= cfpMap (𝟙 T) natSucc ≫ cantorPair ≫ triRootState
  ≫ triRootStep`.
Both the target `cfpLift (natPlus ≫ toRSN)
(cfpFst ≫ toRSN)` and `cantorPair ≫ triRootState`
satisfy this recurrence, verified by
`triRootStep_within` (using `natTruncSub` of
`natSucc(toRSN(a+b))` and `toRSN(a)` being
positive since `a+b+1 > a`).

The recurrence has the form
`X(succ(a), b) = triRootStep(X(a, succ(b)))`,
which couples the fold variable (first arg) with
a shift in the parameter (second arg).  This is
NOT a standard `nnoElim_uniq` pattern (where the
parameter stays fixed).

To break the circularity between Phase 1 and
Stage A, the combined fold step for Stage A at
`succ(n)` requires `triRootState(CP(n, 1))`,
which equals `nnoElim triRootState triRootStep`
at `(CP(n, 0), succ(n))`.  Computing this
involves `succ(n)` triRootSteps from
`triRootState(CP(n, 0))`, expressible as a
fixed morphism `nnoElim triRootState triRootStep`
evaluated at `(CP(n, 0), succ(n))`.

A viable approach: define a combined
`nnoElim` on `n` with enriched state tracking
`(triRootState(natTri(n)), CP(n, 0),
triRootState(CP(n, 0)), triRootState(CP(n, 1)))`,
where the step function uses
`nnoElim triRootState triRootStep` as a
fixed morphism to compute the inner walk,
applied to the tracked `CP(n, 0)` and `succ(n)`
(available via a paramorphism).

The `cantorPair_succ_fst` recurrence directly
gives a "shifted step" equation that both
`cantorPair ≫ triRootState` and the target
`cfpLift (natPlus ≫ toRSN) (cfpFst ≫ toRSN)`
satisfy.  A "shifted step uniqueness" theorem
(`shiftedNnoElim_uniq`) would establish that
any `φ` satisfying the shifted step
`φ(succ(a), b) = g(φ(a, succ(b)))` with a
given base `f = φ(ℓ, ·)` equals
`cfpLift natPlus cfpFst ≫ nnoElim f g`.

The key insight: the change of variables
`Θ(s, a) = φ(a, s - a)` where `s = a + b`
transforms the shifted step into a standard
NNO step `Θ(s, succ(a)) = g(Θ(s, a))`.
This gives `Θ = nnoElim f g`, so
`φ(a, b) = nnoElim f g (a + b, a)`.

The proof of `shiftedNnoElim_uniq` can use
`nnoElim_uniq` on the swapped morphism
`cfpSwap ≫ φ`, showing it equals
`cfpSwap ≫ cfpLift natPlus cfpFst ≫
nnoElim f g`.  The β-step for
`p.elim_uniq` on the first argument of `φ`
uses only the right child (since
`toRSN(β(l, r)) = succ(toRSN(r))`).

With `shiftedNnoElim_uniq`, Stage B reduces to:
1. Verify the shifted step for both sides.
2. Verify the base: `natTri ≫ triRootState =
   cfpLift toRSN (cfpTerminalFrom T ≫ ℓ)`.

The base (Phase 1) itself follows from Stage B
at `a = ℓ` (`CP(ℓ, b) = natTri(b)` since
`natPlus(natTri(b), ℓ) = natTri(b)`).
So once `shiftedNnoElim_uniq` is proved,
`cantorPair_triRootState` follows immediately.

Estimated effort for `shiftedNnoElim_uniq`:
150-250 lines (change of variables,
nnoElim_uniq application, normalization
conditions).

### `treeEqG_trans`

Transitivity of `treeEqG`, using `natTruncSub_fold_comp`
and the right-spine preservation lemmas.
