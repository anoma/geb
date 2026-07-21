# Handoff: ramified-on-vendored-polynomial-functors, Phase C

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [How to use this document](#how-to-use-this-document)
- [Workstream overview](#workstream-overview)
- [Binding constraints and conventions (all phases)](#binding-constraints-and-conventions-all-phases)
- [Phase A — delivered (PR #265)](#phase-a--delivered-pr-265)
- [Phase B — delivered (PR #267)](#phase-b--delivered-pr-267)
  - [Phase B learnings and idioms (reuse in C)](#phase-b-learnings-and-idioms-reuse-in-c)
  - [Phase B residue (non-blocking, tracked)](#phase-b-residue-non-blocking-tracked)
- [Phase C — inter-definability on the primed type system](#phase-c--inter-definability-on-the-primed-type-system)
  - [The target (what C rebuilds and transfers)](#the-target-what-c-rebuilds-and-transfers)
  - [Design questions for the C.0 sub-plan to resolve](#design-questions-for-the-c0-sub-plan-to-resolve)
- [Process to follow for Phase C](#process-to-follow-for-phase-c)
- [Pointers](#pointers)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

## How to use this document

A fresh session picking up this workstream should read this end to end,
then read the spec and plan (linked below). Phases A and B are merged to
`main`; this document carries the workstream context, the Phase A and B
deliverables and learnings, and the Phase C starting point.

## Workstream overview

Goal: provide a second implementation of the `Ramified` recursive layer
(`FreeAlg`, `RType`, `Tm`) on the vendored geb-mathlib polynomial-functor
stack, connected to the existing `GebLean.PolyAlg`-based implementation
by transport-grade equivalences, and — as the terminal step — to rebuild
the first-order presentation layer on the primed types so the existing
inter-definability with elementary-recursive arithmetic (`ERMor`)
transfers by an equivalence of categories, reusing (not redoing) the ER
definability/soundness proofs.

Authoritative documents (on `main`):

- Master spec: `docs/superpowers/specs/2026-07-19-ramified-polynomial-design.md`
  (revision 4; three adversarial-review rounds).
- Master plan: `docs/superpowers/plans/2026-07-19-ramified-polynomial-plan.md`
  (revision 3; Phase C boundary fixed there, sub-plan mandatory).
- Phase B design: `docs/superpowers/specs/2026-07-20-ramified-poly-freemonad-design.md`
  (one adversarial-review round; its decisions bind Phase C consumers).
- Phase B sub-plan: `docs/superpowers/plans/2026-07-19-ramified-poly-freemonad-subplan.md`
  and its `…review-1.md`.

Phase structure:

- Phase A (DONE, merged as PR #265): the W-type bridge
  (`GebLean/PolyBridge/{Slice,WEquiv}.lean`) and the `FreeAlg'` /
  `RType'` instantiation (`GebLean/Ramified/Polynomial/{FreeAlg,RType}.lean`).
- Phase B (DONE, merged as PR #267): the native slice free monad,
  the free-monad bridge, and `Tm'`.
- Phase C (NEXT, this handoff): inter-definability on the primed type
  system — rebuild the primed `Presentation'` / `SynCatFO'`, relate
  `RMRecCat' ≌ RMRecCat`, transfer the endpoints.

## Binding constraints and conventions (all phases)

- No `noncomputable` anywhere; `Classical.choice` in proofs only. The
  axiom gate (`lake build GebLeanAxiomChecks`) accepts only `propext` /
  `Quot.sound` / `Classical.choice`; `sorryAx` and any other axiom fail.
- Recursor-only elimination of the recursive tree datatypes: on the
  vendored side `SlicePFunctor.W.elim` / `.RecProp` / `.induction`; on
  the legacy side (only where a bridge must consume it) `PolyFix.ind` —
  in Phase B this was confined to one lemma
  (`polyFreeMSliceEquiv_bind`). Forbidden over the tree types: the
  `induction` / `cases` tactics, structural `match`-with-self-calls,
  `termination_by`, well-founded recursion, and `WType.rec` in
  computational content. `Nat.rec` / induction on `Nat` / `Bool` /
  `Fin`, and a non-recursive `match` on a finite shape, are fine.
- `GebLean/SliceW/*` stays legacy-free (vendored stack + mathlib
  imports only); it is intended for later promotion to geb-mathlib.
- No novelty claims in `.lean` comments/docstrings — cite only the
  literature transcribed.
- File headers: plain `import ...`, no `module` keyword, no copyright
  header, mandatory `/-! -/` module docstring (`# Title`, summary,
  `## Main definitions`, `## Main statements`, `## References`,
  `## Tags`); `/-- -/` on every `def`/`theorem`.
- `@[simp]` only on constructor-compatibility and field-characterization
  lemmas; operation/naturality compatibility lemmas are NOT `@[simp]`
  (`simpNF` collisions otherwise).
- Tests: mirror each source module under `GebLeanTests/`, register in
  the aggregators; route numeric/semantic assertions through proven
  lemmas, never kernel reduction of composite `W`-trees.
- Build only with `lake build <Module>` / `lake test`; never
  `lake env lean` or `lake clean`. Pre-commit for any `.lean` commit:
  `bash scripts/pre-commit.sh`; before push: `bash scripts/pre-push.sh`.
- VCS: `jj` (colocated). Commit with `jj commit -m` (mathlib message
  convention). NO `jj git push` without user line-by-line review.

## Phase A — delivered (PR #265)

`toSlice : PolyEndo X → SlicePFunctor X X` with `@[simp]` field lemmas;
`polyFixSliceEquiv (P) (x) : PolyFix P x ≃ { w : (toSlice P).W //
wIndex w = x }` with constructor naturality `polyFixSliceEquiv_mk`;
`FreeAlg' A` (fiber subtype idiom) with `mk` / `tupleFold` / `recurse` /
`recurse_mk`; `freeAlgSliceEquiv` (note the `.symm`); `RType'` with the
ten operations by kind and per-operation compatibility lemmas;
`natFreeAlgEquiv'`. Details and idioms: the Phase B handoff,
`docs/superpowers/notes/2026-07-20-ramified-polynomial-phaseB-handoff.md`.

## Phase B — delivered (PR #267)

Fifteen commits: five documents (handoff, design, design review,
sub-plan, sub-plan review) and ten code commits (tasks B.2–B.10 of the
sub-plan, executed spike-first by subagent-driven development; per-task
ledger at `.superpowers/sdd/progress-ramified-poly-freemonad.md`,
parent `geb/` dir, git-ignored scratch).

New modules:

- `GebLean/SliceW/Iso.lean` — `SlicePFunctor.Iso` (fields `shapeEquiv`,
  `posEquiv`, `q_comm`, `r_comm`), `Iso.symm`, `Iso.wMap` (one
  `W.elim`), `wIndex_wMap`, `@[simp] wMap_mk`, round trips by
  `W.induction`, `Iso.wEquiv`, `Iso.wEquivFiber`, and four transport
  helper theorems used by the round trips.
- `GebLean/SliceW/Translate.lean` — `SlicePFunctor.translate
  (v : Y → I) (F)` (shapes `Y ⊕ F.A`, leaf positions `PEmpty`,
  `q = Sum.elim v F.q`, `r` inherited) with six `@[simp]`
  characterization lemmas.
- `GebLean/SliceW/FreeM.lean` — `FreeM (v) (F) (i)` (fiber of
  `(translate v F).W`), `pure`, `node`, `@[simp] val_pure`/`val_node`,
  `bindW` (one `W.elim`) and `bind` (leaf families `v : Y → I`,
  `v' : Y' → I`, independent leaf types), computation rules `pure_bind`
  / `bind_node`, laws `bind_pure` / `bind_assoc` (raw `bindW_pure` /
  `bindW_bindW` by `W.induction`, then wrapped), transports
  `pure_transport` / `bind_transport`.
- `GebLean/PolyBridge/FreeMEquiv.lean` — `translateSliceIso V P :
  Iso (toSlice (polyTranslate V P)) (translate V.hom (toSlice P))`
  (shape leg: `Equiv.sigmaSumDistrib` then
  `Equiv.sumCongr (Equiv.sigmaFiberEquiv V.hom) (Equiv.refl _)`);
  `polyFreeMSliceEquiv V P x : PolyFreeM V P x ≃ FreeM V.hom (toSlice P) x`
  (Phase A leg `.trans` the `wEquivFiber` leg); naturality lemmas
  `polyFreeMSliceEquiv_transport` / `_pure` / `_node` / `_bind` (the
  last by `PolyFix.ind`, the branch's only legacy elimination).
- `GebLean/Ramified/Polynomial/Term.lean` — `Tm' sig Γ :=
  FreeM Γ.get (toSlice sig.polyEndo)`; `Tm'.var` / `op` / `subst` /
  `reind` / `reind_rfl` / `weaken`, signatures byte-identical to the
  legacy `GebLean/Ramified/Term.lean`; clone laws `subst_id` /
  `subst_subst` / `var_subst` / `subst_reind` as thin instances of the
  native laws; `tmSliceEquiv Γ s : Tm' sig Γ s ≃ Tm sig Γ s`
  (`(polyFreeMSliceEquiv (varOver Γ) sig.polyEndo s).symm`);
  compatibility lemmas `tmSliceEquiv_var` / `_op` / `_subst`.

Tests mirror every module (`GebLeanTests/SliceW/*`,
`GebLeanTests/PolyBridge/FreeMEquiv.lean`,
`GebLeanTests/Ramified/Polynomial/Term.lean` — the last with a
two-sorted mixed-arity smoke signature exercising the clone laws and
all three compatibility lemmas). Area docs updated:
`docs/areas/polynomial-functors.md`, `docs/areas/ramified-recurrence.md`.

### Phase B learnings and idioms (reuse in C)

- The A.0/B.1 spike pattern (validate the hardest constructions
  sorry-free before real files) again removed all mid-phase blockage;
  do the same in C for whatever C.0 identifies as hardest.
- `SliceDomPFunctor.Compatible` is not `@[expose]`: prove `Compatible`
  goals via dot-notation `…toSliceDomPFunctor.compatible_iff` pointwise,
  never by definitional unfolding.
- Elaboration hints: `FreeM.node` / `W.mk` and statements without an
  explicit occurrence of an implicit (`sig`, `Γ`, `F`) need
  `(F := …)` / `(sig := …)` / `(Γ := …)` pins; the pattern recurs at
  every consumer of the FreeM API.
- `rw` fails higher-order matching on `.bind`-headed terms; use
  `exact` / `Eq.trans` chains, or rewrite in a hypothesis
  (`rw … at h`) to dodge `Eq.rec`-motive mismatches.
- `FreeM.bind_transport` is oriented `(h ▸ t).bind f = h ▸ (t.bind f)` —
  the mirror image of the legacy `polyFreeMBind_transport` — so primed
  proofs that mirror legacy ones may need to drop a `.symm`.
- The `W.induction` closing shape (from Phase A, confirmed in B):
  `congrArg W.mk (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext …))))`.
- Re-orienting a `.symm`-defined equivalence's naturality: derive
  through `Equiv.symm_apply_eq` from the forward-direction lemma
  (pattern: `freeAlgSliceEquiv_mk` in
  `GebLean/Ramified/Polynomial/FreeAlg.lean`).

### Phase B residue (non-blocking, tracked)

- A batched docstring-cleanup pass was deferred by the whole-branch
  review: trim trailing proof-method clauses on `bindW_pure` /
  `bindW_bindW` / `polyFreeMSliceEquiv_bind` / the three
  `tmSliceEquiv_*` lemmas; consider a separate
  `## Implementation notes` section in the `Term.lean` module
  docstring. One small `style` commit; any time.
- At geb-mathlib promotion time: mark the four Iso transport helpers
  `private`; re-check the `uY`-first universe declaration order in
  `Translate.lean` against the vendored convention.
- NOT ported to the primed layer (outside the B scope): `Tm.reind_symm`,
  `Tm.reind_symm'`, and `QuotRel` / `QuotRel.rel_reind`. `QuotRel` is
  a parameter of the legacy syntactic-category construction, so C.0
  must decide whether the primed rebuild needs primed counterparts or
  reuses the legacy ones over `Tm'` via the equivalence.
- `Tm'.weaken` has no consumer yet; Phase C is its expected consumer.

## Phase C — inter-definability on the primed type system

Branch (master plan phase-map): `feat/ramified-poly-er`. First task is
C.0: brainstorm the design, write and converge the Phase C sub-plan
(`docs/superpowers/plans/2026-07-19-ramified-poly-er-subplan.md` per
the master plan's naming; confirm the path at C.0), via brainstorming +
writing-plans + adversarial review + user review, THEN execute via
subagent-driven development.

### The target (what C rebuilds and transfers)

The existing endpoints `ramified_definability` /
`ramified_definability_kSim` (`GebLean/Ramified/Characterization.lean`)
quantify over `ObjCtx` (contexts of `RType`) and `SynCatFO` morphisms
(over `Tm`), concluding `collapseDenotation g = arityCongr … f.interp`.
They rest pervasively on `RType` and `Tm`, the recursive types Phases A
and B re-expressed. User-decided (master spec section 6, review-2 P2):
Phase C is a full presentation rebuild, not a free transport —
`SynCat` / `RMRecCat` are parametrized by a whole `Presentation` and
hardwired to legacy `Tm`, so a type equivalence cannot be transported
into a category directly.

**Deliverables (fixed by the master plan):**

- `ObjCtx'` / `SynCatFO'` / `collapseDenotation'` (and `oCtx'`,
  `arityCongr'` as needed) on `RType'` (Phase A) and `Tm'` (Phase B),
  built from a primed `Presentation'` (`higherOrder'` and standard
  model over `RType'`), with `RMRecCat' ≌ RMRecCat` established from
  the A/B equivalences.
- `ramified_definability'` and `ramified_definability_kSim'` over the
  primed stack, proved by transferring the existing theorems across
  `RMRecCat' ≌ RMRecCat`. The ER-side content
  (`erMorN_ramified_definable`, `collapseFunctor` faithfulness,
  `f.interp`) is reused unchanged; transferring the endpoint equation
  additionally needs a lemma that `collapseDenotation'` agrees with
  `collapseDenotation` across the equivalence (a C.0 obligation, not
  free reuse — master plan review-3).

**Consumes:** `rTypeSliceEquiv` and its operation-compatibility lemmas
(Phase A); `tmSliceEquiv` and `tmSliceEquiv_var` / `_op` / `_subst`
(Phase B); the existing `ObjCtx`, `SynCatFO`, `collapseDenotation`,
`arityCongr`, `ramified_definability`, `ramified_definability_kSim`.

### Design questions for the C.0 sub-plan to resolve

1. Whether `SynCat'` uses legacy `Tm` over the primed signature or the
   vendored `Tm'` (a C.0 decision recorded in the master plan). The
   `Tm'` route consumes Phase B's mirror-exact API; the legacy-`Tm`
   route would make Phase B's term layer a dead end for C — expect the
   `Tm'` route unless the `Presentation` plumbing forces otherwise.
2. The quotient layer: does the primed `SynCatFO'` need a primed
   `QuotRel'` (not ported in B), or can the legacy `QuotRel` be pulled
   back across `tmSliceEquiv`? Composition congruence
   (`subst_congr`) must survive whichever route.
3. The shape of `RMRecCat' ≌ RMRecCat`: object and hom transport across
   `rTypeSliceEquiv` / `tmSliceEquiv`, and where `arityCongr'` sits.
4. The `collapseDenotation'`-agreement lemma's statement (the review-3
   obligation) and which side (primed or legacy) hosts the proof.
5. Scope of `Presentation'`: which fields of the legacy `Presentation`
   (`GebLean/Ramified/SynCat.lean` area — read it first) must be
   rebuilt over `RType'` / `Tm'`, and which are signature-generic and
   reusable as-is.

## Process to follow for Phase C

1. `superpowers:brainstorming` (start from the source: read
   `GebLean/Ramified/SynCat.lean`, `FirstOrder.lean`,
   `Characterization.lean`, and the master spec section 6 before
   proposing anything), resolving the design questions above; produce
   the Phase C design document.
2. `superpowers:writing-plans` → the C.0 sub-plan with bite-sized
   tasks, spike-first.
3. Adversarial review of design and sub-plan (fresh-context reviewers
   verifying every named declaration against source; re-fetch the
   mathlib upstream guides) BEFORE the user-review handoff; converge to
   zero-defect.
4. User line-by-line review.
5. `superpowers:subagent-driven-development` — spike first, fresh
   implementer + task review per task, whole-branch review at the end.
   Cheap models for transcription, capable models for the hard proofs
   and the final review.

## Pointers

- Master spec / plan and Phase B design / sub-plan / reviews: see
  "Workstream overview" above.
- Phase B ledger (per-task commits, review dispositions, deferred
  minors): `.superpowers/sdd/progress-ramified-poly-freemonad.md`
  (parent `geb/` dir; git-ignored scratch — recover from `git log` if
  lost). Phase A ledger: `.superpowers/sdd/progress-ramified-polynomial.md`.
- Phase A modules: `GebLean/PolyBridge/{Slice,WEquiv}.lean`,
  `GebLean/Ramified/Polynomial/{FreeAlg,RType}.lean`.
- Phase B modules: `GebLean/SliceW/{Iso,Translate,FreeM}.lean` (index
  `GebLean/SliceW.lean`), `GebLean/PolyBridge/FreeMEquiv.lean`,
  `GebLean/Ramified/Polynomial/Term.lean`, and their tests.
- Legacy targets for C: `GebLean/Ramified/{SynCat,FirstOrder,Characterization}.lean`
  and the `Soundness` / `Definability` trees.
- Vendored stack: `vendor/geb-mathlib/Geb/Mathlib/Data/PFunctor/Slice/
  {Basic,W}.lean`.
