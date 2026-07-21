# Handoff: ramified-polynomial follow-up work

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [How to use this document](#how-to-use-this-document)
- [State at hand-off](#state-at-hand-off)
- [1. Generic free-monad induction and the native `Tm'.eval_subst`](#1-generic-free-monad-induction-and-the-native-tmeval_subst)
  - [1a. Extract `FreeM.induction`](#1a-extract-freeminduction)
  - [1b. Re-prove `Tm'.eval_subst` natively](#1b-re-prove-tmeval_subst-natively)
- [2. Sorted-signature sum combinator](#2-sorted-signature-sum-combinator)
- [3. Declaration placement](#3-declaration-placement)
- [4. Test strengthening](#4-test-strengthening)
- [5. Watch items (no branch)](#5-watch-items-no-branch)
- [6. Related tracked work](#6-related-tracked-work)
- [Process](#process)

<!-- END doctoc generated TOC -->

## How to use this document

The ramified-on-vendored-polynomial-functors workstream is complete
through Phase C (merged as PR #268). This document carries the work
deferred out of Phase C by its whole-branch review under the
one-concern-per-branch rule, with the file and declaration references
verified against `main` at `fcad5d0c`.

Each section below is one branch. They are independent except where
stated. Section 1 is the ordered one: it precedes both the
`slicew-promotion` item in `TODO.md` and the legacy retirement of
master spec section 10, and its two parts share a tool, so run them
together.

## State at hand-off

- Branch `feat/ramified-poly-er` merged to `main` (PR #268), 31
  commits.
- New modules: `GebLean/SliceW/Reindex.lean` plus additions to
  `GebLean/SliceW/FreeM.lean`; `GebLean/Ramified/SigEquiv.lean`,
  `GebLean/Ramified/PresentationEquiv.lean`; thirteen modules under
  `GebLean/Ramified/Polynomial/`.
- `GebLean/Ramified/FirstOrder.lean` and its test mirror were deleted
  and rebuilt as `GebLean/Ramified/Polynomial/FirstOrder.lean`.
- Endpoints delivered: `rmRecCatSliceEquiv`, `ramified_definability'`,
  `ramified_definability_kSim'`.
- Axiom envelope unchanged: `propext`, `Quot.sound`,
  `Classical.choice`. No `sorry` or `admit`.
- Execution ledger with per-task dispositions:
  `.superpowers/sdd/progress-ramified-poly-er.md` (parent `geb/`
  directory, git-ignored scratch; recover from `git log` if lost).
- Phase C design and sub-plan:
  `docs/superpowers/specs/2026-07-20-ramified-poly-er-design.md`,
  `docs/superpowers/plans/2026-07-19-ramified-poly-er-subplan.md`
  and its two adversarial reviews.

## 1. Generic free-monad induction and the native `Tm'.eval_subst`

Branch suggestion: `refactor/slicew-freem-induction`. Do this section
before the geb-mathlib port, and before legacy retirement.

### 1a. Extract `FreeM.induction`

Three sites inline the same fibrewise `SlicePFunctor.W.induction` over
`translate`-trees with a `Sum.inl` / `Sum.inr` split and fiber-subtype
rewrapping:

- `GebLean/SliceW/FreeM.lean:159` (`bindW_pure`),
- `GebLean/SliceW/FreeM.lean:185` (`bindW_bindW`),
- `GebLean/Ramified/Polynomial/FirstOrder.lean:311` (`foTm_eval`).

Extract a generic `SlicePFunctor.FreeM.induction` into
`GebLean/SliceW/FreeM.lean` (a `Prop`-valued eliminator: a leaf case at
`FreeM.pure`, a node case at `FreeM.node` with the children's induction
hypotheses) and route all three sites through it. Add it to the module
docstring's `## Main statements`.

Ordering: two of the three sites are in `GebLean/SliceW/`, the
legacy-free tree that `TODO.md`'s **slicew-promotion** item schedules
for porting into `geb-mathlib`. Landing the abstraction first means the
port carries the consolidated form rather than three inlined copies,
and means the promotion-time residue list stays as `TODO.md` records
it.

Constraint reminder: `GebLean/SliceW/*` imports the vendored
`Geb.Mathlib.*` tree and mathlib only. `FreeM.induction` is
`Prop`-valued, so `W.induction` is the sanctioned device.

### 1b. Re-prove `Tm'.eval_subst` natively

`Tm'.eval_subst` (`GebLean/Ramified/Polynomial/Interp.lean:168`) is a
native statement — it mentions no legacy object — but its proof is a
rewrite chain through `tmSliceEquiv_eval`, `tmSliceEquiv_subst`, and
the legacy `Tm.eval_subst`. Replace that chain with a raw induction
over the underlying trees, using `FreeM.induction` from 1a: the leaf
case reduces by `FreeM.elim_pure` and `Tm'.eval_transport`, the node
case by `FreeM.bind_node`, `Tm'.eval_op`, and the induction
hypotheses. This is the same raw-then-wrap shape as `bindW_pure` /
`bindW_bindW`, so 1a supplies both the tool and the template;
`Tm'.eval_subst` becomes its fourth consumer.

Update the module docstring at `Interp.lean:51-52`, which currently
records the legacy route, and the declaration docstring at `:166-167`.

Do not touch `tmSliceEquiv_eval` itself: it is a bridge lemma relating
the two stacks, so its legacy-side `PolyFix.ind` auxiliary is
appropriate, and the lemma is deleted rather than re-proved when the
bridge goes.

Motivation: legacy retirement (master spec section 10) is planned. At
retirement every native statement must stand without the bridge;
`Tm'.eval_subst` is the one native lemma in the primed stack whose
proof does not, so it is cheaper to convert now, while the tool is
being built anyway, than to discover it as a retirement blocker.

## 2. Sorted-signature sum combinator

Branch suggestion: `refactor/sorted-sig-equiv-sum`.

`GebLean/Ramified/Polynomial/HigherOrderEquiv.lean:70`
(`higherOrderSigEquiv`) and
`GebLean/Ramified/Polynomial/IdentEquiv.lean:117` (`defnSigEquiv`)
share a three-deep `Equiv.sumCongr` skeleton with byte-identical
`arity_comm` and `result_comm` bodies (`List.map_replicate.symm` at the
constructor summand, `rTypeSliceEquiv_arrow` at application). About
twenty lines are duplicated.

Add a `SortedSigEquiv.sum` combinator to
`GebLean/Ramified/SigEquiv.lean` — given `SortedSigEquiv sig₁ sig₁'`
and `SortedSigEquiv sig₂ sig₂'` at a shared `sortEquiv`, produce
`SortedSigEquiv (sig₁.sum sig₂) (sig₁'.sum sig₂')` — and rebuild both
signature equivalences from it. `SortedSig.sum` is in
`GebLean/Ramified/SortedSig.lean`.

Both rebuilt equivalences must keep their current types: they are
consumed by `higherOrderPresEquiv` and `defnPresEquiv` respectively,
and through those by the phase's endpoints.

## 3. Declaration placement

Branch suggestion: `refactor/ramified-poly-placement`. This branch
touches legacy modules, so it cannot be combined with sections 1 or 2.

Declarations that state facts about one subject but live in another
module:

| Declaration | Currently | Belongs |
| --- | --- | --- |
| `interpCongr_cast` | `Polynomial/IdentEquiv.lean:548` | `GebLean/Ramified/RType.lean`, beside `RType.interpCongr` |
| `interpCongr_arrow` | `Polynomial/IdentEquiv.lean:557` | as above |
| `carrierSliceEquiv_arrow` | `Polynomial/IdentEquiv.lean:566` | `Polynomial/RType.lean`, beside `carrierSliceEquiv` |
| `carrierSliceEquiv_o` | `Polynomial/IdentEquiv.lean:595` | as above |
| `carrierSliceEquiv_cast_heq` | `Polynomial/IdentEquiv.lean:949` | as above |
| `objToNat_heq` | `Polynomial/Collapse.lean:223` | `GebLean/Ramified/Examples.lean`, beside `objToNat_cast` |
| `cast_objFromNat` | `Polynomial/Collapse.lean:231` | `GebLean/Ramified/Definability/Top.lean`, beside `objFromNat` |
| `collapseDenotation_apply` | `Polynomial/Collapse.lean:399` | `GebLean/Ramified/Soundness/Collapse.lean` |
| `arityCongr_trans` | `Polynomial/Characterization.lean:109` | `GebLean/Ramified/Characterization.lean` |

The first two mention no primed object at all. `arityCongr_trans` is
already `_root_.GebLean.Ramified.`-scoped, so only its file placement
is at issue; a legacy consumer currently has to import the primed stack
to reach it.

Not on this list: `Hom'.eval_heq_cast`
(`Polynomial/Collapse.lean:383`). The whole-branch review flagged it as
a phantom-namespace hazard, but it is a statement about the primed
`Hom'`, which is declared in `GebLean.Ramified.Polynomial`, so it
resolves correctly. Leave it.

While in these files: `HomTuple.eval_comp`
(`GebLean/Ramified/PresentationEquiv.lean:79`) reproduces the inner
proof body of `Hom.eval_comp` (`GebLean/Ramified/SynCat.lean:207`) at
the pre-quotient level. Make the representative-level statement the
primitive and derive `Hom.eval_comp` from it.

## 4. Test strengthening

Branch suggestion: `test/ramified-poly-coverage`.

- `GebLeanTests/Ramified/Polynomial/HigherOrderEquiv.lean` exercises
  the hom map at `idZero'`, whose context is empty, so the domain-side
  `unmapEnv` reindexing degenerates. Re-run the same assertion at
  `idVar' : RIdent' A [RType'.o] RType'.o` (declared in the `IdentTest`
  namespace alongside `idZero'`) to exercise it.
- `GebLeanTests/Ramified/Polynomial/FirstOrder.lean` never tests
  `firstOrder_defn`'s fourth conjunct at a real child: every `defn`
  child list in the fixtures is `fun j => j.elim0`. The deleted legacy
  test covered this through `ramMul_fo`, whose hole child was
  `ramAdd_fo`. Restoring the coverage needs primed counterparts of the
  Leivant section 2.4(2) examples (`ramAdd`, `ramMul`), i.e. a primed
  `Examples` layer; treat that as the prerequisite rather than forcing
  a synthetic fixture.

Assertions must discriminate: an `example ... := thm args` form
type-checks whenever the theorem exists and asserts nothing further.
Perturb each new assertion (change an expected value, confirm the build
fails, revert) and record that evidence, as Phase C did.

## 5. Watch items (no branch)

Not defects; revisit if the conditions below are met.

- `set_option maxHeartbeats 1000000` on the `mrecSample'` assertion in
  `GebLeanTests/Ramified/Polynomial/IdentEquiv.lean`. Scoped to one
  declaration and documented. If further nested-recurrence assertions
  need larger bumps, absorb one unfolding layer into a named lemma
  instead.
- Two `erw` uses in `GebLean/Ramified/PresentationEquiv.lean` (unit and
  counit hom conditions). Upstream discourages `erw` as brittle; if
  either breaks under a mathlib bump, replace with targeted
  `rw` / `simp only`.

## 6. Related tracked work

- `TODO.md` § **slicew-promotion**: port `GebLean/SliceW/*` into
  `geb-mathlib`, then refresh the vendored tree and replace the
  originals with the vendored copies. Promotion-time residue is
  recorded there (mark the four `Iso` transport helpers `private`;
  re-check the `uY`-first universe order in `Translate.lean`). Section
  1 above should land first.
- The first-order polynomial-time transcription (Leivant, "Ramified
  recurrence and computational complexity I", Feasible Mathematics II,
  1995, DOI `10.1007/978-1-4612-2566-9_11`) now has a primed
  first-order layer to build on
  (`GebLean/Ramified/Polynomial/FirstOrder.lean`); that was the reason
  Phase C replaced the legacy module rather than mirroring it.
- Legacy retirement (master spec section 10) will need its own scoping
  pass. The distinction that governs it: a declaration mentioning both
  stacks is a bridge and is deleted with the bridge (`tmSliceEquiv`,
  `identSliceEquiv`, `carrierSliceEquiv`, `rmRecCatSliceEquiv`, the
  agreement lemmas, and the whole of `PolyBridge/`); a declaration
  mentioning only primed objects must stand on its own afterwards, so
  any legacy step in its proof is retirement debt. Section 1b clears
  the only instance of the latter found in the primed stack. Every
  module under `GebLean/Ramified/Polynomial/` still imports at least
  one legacy module, but in each case for signature-generic material
  (`SortedSig`, `Presentation`, `SynCat`'s position lemmas,
  `arityCongr`) or for the bridge, not for a native proof — the
  retirement pass should confirm that module by module.

## Process

Sections 1–4 are small enough to execute directly without a
brainstorming or planning phase, subject to the usual gates:
`bash scripts/pre-commit.sh` before each commit touching `.lean`,
`bash scripts/pre-push.sh` before any push, and user line-by-line
review before `jj git push`. Each section is one branch under
one-concern-per-branch; section 3 touches legacy modules and must stay
separate from sections 1 and 2.
