# Adversarial review 1: Phase B free-monad sub-plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Blockers](#blockers)
- [Majors](#majors)
- [Minors](#minors)
- [Nits](#nits)
- [Verified without defect](#verified-without-defect)
- [Disposition](#disposition)
- [Overall](#overall)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Round 1, 2026-07-20. Two fresh-context reviewers (signature
verification and construction feasibility; style, process, and
coverage with the mathlib upstream guides re-fetched) against source
at branch `feat/ramified-poly-freemonad`. Every claim below was
re-verified against source before entry.

## Blockers

None.

## Majors

None.

## Minors

- M1 (Task B.2, `Iso.symm`). "Equivalences reversed" understates the
  `posEquiv` field of `symm`: at `a' : G.A` it must land in
  `F.B (shapeEquiv.symm a')`, but the reversed forward field has
  domain `G.B (shapeEquiv (shapeEquiv.symm a'))`, so stating the field
  requires a transport along `Equiv.apply_symm_apply`, which then
  threads through `symm`'s `r_comm` proof and the round trips. Fix:
  state the transport in the task.
- M2 (Task B.7, Consumes). `Equiv.sumSigmaDistrib` is the
  sigma-indexed-by-a-sum variant and does not fit; the fitting
  composite is `Equiv.sigmaSumDistrib`
  (`(Σ i, α i ⊕ β i) ≃ (Σ i, α i) ⊕ (Σ i, β i)`) with
  `Equiv.sumCongr (Equiv.sigmaFiberEquiv V.hom) (Equiv.refl _)`;
  all three verified present in this checkout's mathlib
  (`Mathlib/Logic/Equiv/Sum.lean`). Fix: name the verified composite,
  drop the wrong pointer and the search instruction.
- M3 (Task B.10, `tmSliceEquiv_subst`). The named transport tools move
  `pure` only; matching the leaf functions across
  `polyFreeMSliceEquiv_bind` needs transport-naturality of the
  equivalence itself, `polyFreeMSliceEquiv V P x' (h ▸ t) =
  h ▸ polyFreeMSliceEquiv V P x t` (one line by `subst`), absent from
  every Produces block. The legacy analogue needed the dedicated
  `polyFreeMBind_transport` at the corresponding step. Fix: add
  `polyFreeMSliceEquiv_transport` to Task B.8's Produces and route
  B.10 through it.
- M4 (Task B.4, lemma names). `pure_val` / `node_val` put the
  projection last; the mathlib convention (left-hand side determines
  the name, projection first, as in `Fin.val_mk` / `Subtype.coe_mk`)
  gives `val_pure` / `val_node`. Fix: rename.
- M5 (Task B.1, acceptance criterion). The design requires the spike
  constructions validated sorry-free; the task's steps do not state
  the criterion. Fix: add "sorry-free" to Steps 1–2.

## Nits

- N1 (Task B.2, `wIndex_wMap`). `W.comp_elim` alone yields the
  statement (`p ∘ elim … = F.wIndex` pointwise); `q_comm` is consumed
  inside `hg`, not in this derivation. Fix: drop "and `q_comm`".
- N2 (Tasks B.2/B.4, Consumes). `Compatible`, `compatible_iff`,
  `rCurried` live in namespace `SliceDomPFunctor`, reached by dot
  notation through `toSliceDomPFunctor`. Fix: attribute them
  correctly.
- N3 (Global constraints). "where frictionless" is a metaphor; the
  design's phrasing is "as far as it compiles". Fix: use the design's
  phrasing.
- N4 (Task B.1, heading and intro). "De-risking" and "throwaway" are
  colloquial. Fix: "validation spike"; "scratch file, deleted before
  any commit".
- N5 (coverage, plan-not-in-design). `Iso.symm`, `wMap_mk`,
  `val_pure`/`val_node`, `FreeM.bind_node`, `Tm'.reind_rfl` are
  consistent elaborations of the design; `bind_node` is load-bearing
  for the Task B.8 bridge proof, so the design document is amended to
  record it. No design deliverable lacks a plan task.
- N6 (filename). The plan file ends `-subplan.md` with date
  2026-07-19 while the design is dated 2026-07-20; the cross-references
  are mutually consistent and the path is fixed by the master plan and
  handoff. No action.

## Verified without defect

- Every consumed declaration exists as cited across the vendored
  `Slice/{Basic,W}.lean`, `GebLean/PolyAlg.lean`,
  `GebLean/Ramified/{Term,SortedSig,AlgSig}.lean`, Phase A modules,
  and the aggregators; `W.elim`'s argument list matches every
  invocation; `Tm.subst`'s leaf function is verbatim
  `fun _ a => a.2 ▸ σ a.1`.
- Load-bearing feasibility: the B.2 `wMap` algebra (node type,
  compatibility re-indexing, `hg`); `wEquivFiber` from `wEquiv` +
  `wIndex_wMap` both ways; B.3 `translate` universe coherence
  (`SlicePFunctor.{max uY uA, uB, uI, uI}`); B.5 `bindW`'s leaf case
  and the definitional `B`/`r` agreement of `translate v F` and
  `translate v' F` at `Sum.inr` (so `hc' := hc`); B.6 `bindW_pure`
  homogeneity at `Y' = Y`, `v' = v`; the B.7 shape computation with
  the fiber witness on the forward field; B.9 `Tm'.op`'s shape
  arithmetic against `SortedSig.polyEndo`; the clone-law mirrors.
- Recursor-only constraint: every construction routes through
  `W.elim` / `W.induction` / `PolyFix.ind`; all `match`es are
  non-recursive shape splits.
- All nine commit subjects: allowed type, imperative present tense,
  lowercase, no trailing period, ≤ 72 characters. All other proposed
  names conform to the upstream naming conventions. Process gates
  (pre-commit per task, pre-push in B.11, push gated on user review),
  aggregator wiring, doctoc/markdownlint steps, and the three DOI
  references are in place. Coverage against the design is complete in
  both directions (modulo N5).

## Disposition

M1–M5, N1–N4 applied to the plan and N5 to the design document in the
same commit as this review. N6 requires no action.

## Overall

0 blockers, 0 majors, 5 minors, 6 nits. Converged pending application
of the disposition.
