# Architectural pivot handoff: K^sim_2 ⊆ ER via URM simulation

> **Context.**  This document is the handoff record for a fresh
> session.  It captures the finding that the project's current
> `kToER` strategy (direct categorical translation +
> `kSimTowerBound` dominance) is not literature-aligned and has
> failed across five plan iterations.  The fresh session should
> begin with the user reviewing this document.  Once the
> architectural direction is settled, the session writes a
> detailed implementation plan based on the chosen path and
> executes it with subagent-driven development.

## 1. The diagnosis

Tourlakis 2018 §0.1.0.44 states `K^sim_n = E^{n+1}` for n ≥ 2.
Its proof structure routes through:

- **§0.1.0.43 (Ritchie–Cobham)**: `E^n = {functions URM-computable
  in time t ∈ E^n}`.
- **§0.1.0.15**: `K^sim_n = L_n` (loop-program hierarchy).

Both directions of the equivalence go through URM / loop-program
simulation in the literature.

**The project's directions, however, currently differ:**

- `erToK` (`ER ⊆ K^sim_2`): designed via **URM simulation**, per
  `docs/lawvere-k-sim-hierarchy.md` Appendix A (lines 1119+).
  Documented at lines 786-789: "The theorem is proved as a
  corollary of the general result that `ER ⊆ K^sim_2` as
  function classes via URM simulation (Tourlakis 2018 Corollary
  0.1.0.44 transferred to our K^sim)."  Phase 2 closure-proof
  tasks #224, #225, #228, #229 wrote and reviewed this.  Literature-
  aligned.
- `kToER` (`K^sim_2 ⊆ ER`): designed as **direct categorical
  translation** — `kToER : KMor1 → ERMor1` with the simrec case
  translated to `ERMor1.boundedRec base step bound` plus a
  dominance proof via an explicit `kSimTowerBound` ER expression.
  NOT URM simulation.  NOT a transcription of any published
  proof structure.

Five plan iterations (v2 through v5, plus a math-only prose
proof) all attempted to discharge the dominance theorem
`kSimTowerBound_dominates_inline` for the direct kToER strategy.
All failed at related load-bearing claims:

- v2: claimed an impossible `PolyBound` on `kSimTowerBound`
  (which itself contains `towerER`, super-polynomial).
- v3: invented a `TowerBound` type with a tower-iter-tower bound
  that is mathematically false at non-zero step heights.
- v4: glossed `Nat.rec → Nat.iterate` bridging and tried
  `polynomial_iter_tower_bound` directly without addressing
  `kSimPackedStep_polyBound`'s `coefficient = 3^E` field.
- v5: tried to mirror the level-1 chain at level 2, but the
  level-1 chain works only because `level0Shape.linearBound.1 ≤
  1` — at level 1 children, `KMor1.linearBound.1` can be
  arbitrarily large, breaking the iteration.
- Prose proof: hand-waved through `kSimPackedStep_polyBound`'s
  `3^E` coefficient field; adversarial review caught the
  resulting absorption inequality `log_2(C+1) ≤ stepTH + small`
  is false (LHS grows as `4^k`, RHS only linear in `k`).

The pattern across these iterations is now clear: the project's
**bespoke** infrastructure (`kSimTowerBound`,
`KMor1.linearBoundLog_le_towerHeight`'s factor 3,
`kSimPackedStep_polyBound`'s `3^E` coefficient) was built to
support a proof strategy that does not correspond to any
published proof.  The mathematics keeps not closing because the
strategy itself is not how the literature establishes
`K^sim_2 ⊆ ER`.

## 2. What the literature actually does

Tourlakis 2018's proof of `K^sim_2 ⊆ E^3 = ER`:

1. Show `K^sim_2 = L_2` (§0.1.0.15).
2. Each L_2 loop program runs on a URM with bounded runtime;
   the runtime is in `E^3 = ER` (§0.1.0.43 Ritchie-Cobham,
   applied to L_2 / E^3).
3. Therefore each `K^sim_2` function is `URM`-computable in
   `ER` time, hence is in `ER` itself (Ritchie-Cobham
   converse).

Concretely, the published proof:

- Translates each K^sim_2 morphism to a loop program (or a
  concrete URM).
- Bounds the URM's runtime by an ER function.
- Uses Ritchie-Cobham to conclude the function being computed
  is in ER.

There is **no construction** of an explicit `kSimTowerBound`
ER expression that bounds the K^sim_2 function's value
pointwise.  The bound is on the URM RUNTIME, not on the
function's value.

Phase 2's Appendix A (in `docs/lawvere-k-sim-hierarchy.md`)
already contains this structure for the erToK direction.  The
SYMMETRIC direction (kToER via URM simulation) would mirror
Appendix A's structure: build a URM that computes K^sim
functions, bound its runtime in ER, and lift to ER membership.

## 3. The architectural decision

**The decision the fresh session must make** (or surface to the
user for a decision):

### Option A: Pivot kToER to URM simulation

Mirror the erToK direction's strategy.  Specifically:

- Define a URM interpreter for K^sim morphisms (parallel to
  Appendix A's URM interpreter for ER).
- Bound the URM's runtime by an ER function (via loop-program
  complexity analysis).
- Use Ritchie-Cobham (or a project-internal analog) to lift
  to `kToER : KSimCat 2 ⥤ ERCat`.

Substantial rewrite.  Estimated weeks of work.  The existing
direct-translation `kToER` definition (Tasks 9-13, defining
`kToER : KMor1 → ERMor1` via boundedRec) might be kept as a
reference but is not the load-bearing structure under this
option.

The existing infrastructure that's salvageable under Option A:

- Phase 1: KMor1 inductive, level, interp, KMorN, quotient,
  category instance.  All reusable.
- The `ERMor1.PolyBound` type and per-constructor builders.
  Reusable for the runtime-bound part.
- `Nat.polynomial_iter_tower_bound`, the Tower utilities.
  Reusable.
- `Utilities/KSimSzudzikSimrec.lean` (`kSimSzudzikPackList`,
  `kSimSzudzikUnpackAt`): the Szudzik pairing infrastructure
  may or may not be needed under URM simulation, depending on
  how the URM encodes K^sim's multi-output simrec.

The existing infrastructure that is NOT salvageable under
Option A:

- `kSimPackedBase`, `kSimPackedStep`, `kSimStepContext`,
  `kSimTowerBound`, `iterAutoBoundExpr`: built for the
  direct-translation simrec case, not needed for URM
  simulation.  Could be deleted or kept as dead code.
- `KMor1.linearBound`, `KMor1.linearBound_dominates`,
  `KMor1.linearBoundLog_le_towerHeight`,
  `kSimTowerBound_dominates_level_one`: the level-1 dominance
  proof is the work-product of the failed strategy.  Could
  potentially be kept if some URM-simulation-internal lemma
  consumes it, but more likely deleted.
- `kSimPackedBase_polyBound`, `kSimPackedStep_polyBound`,
  `to_iter_step_form`, `le_pow_shift_of_polyBound`: built for
  the failed strategy.  Re-evaluate.

Substantially: of the roughly 30 completed Poly Tasks (#285
through #300, plus #306 and #307) and the kToER Tasks (#253
through #262 plus #265), perhaps half the infrastructure
carries over.  The other half corresponds to the direct-
translation strategy and may be deleted.

### Option B: Adjust the direct-translation infrastructure

Instead of pivoting, ARCHITECTURALLY change the direct-
translation infrastructure to make the dominance proof close.
Possibilities:

- Change `kSimTowerBound`'s shape to use higher tower height
  (`stepTH + 2` or `2·stepTH + 1` instead of `stepTH + 1`).
- Change the linear-inside coefficient (e.g. `3·baseTH +
  3·sumCtx` instead of `2·baseTH + 2·sumCtx`).
- Tighten `KMor1.linearBoundLog_le_towerHeight`'s factor from
  3 to 1 (if a tighter Wong-style derivation works).
- Change `kSimPackedStep_polyBound`'s `coefficient = 3^E`
  formula to a smaller bound (which would require restructuring
  `kSimSzudzikPackList` or its bound).

These are all infrastructure changes to landed code.  Each
requires careful adversarial verification that the new shape
admits a closing absorption inequality.  Without a literature
proof to follow, this risks recreating the same v2-v5 failure
mode with new symptoms.

### Option C: Drop the K^sim_2 ⊆ ER goal

If neither Option A nor B converges, consider whether the
ER ↔ K^sim_2 equivalence is necessary for the broader Geb
project's goals at all.  The project might still be valuable
without this specific bidirectional equivalence.

### Recommendation

**Option A (URM simulation).**  Reasoning:

1. It's literature-aligned — Tourlakis's proof IS via URM
   simulation in both directions, and the erToK direction
   already follows this structure successfully.
2. The pattern of v2-v5 failures suggests the direct-translation
   strategy is fundamentally inadequate, not merely under-
   detailed.  No amount of plan iteration is likely to close
   the gap.
3. The asymmetry (URM for one direction, direct for the other)
   is itself a code smell — symmetry is preferred when
   formalizing a symmetric mathematical equivalence.

But this is a decision for the user, not for the next session
to make autonomously.  The fresh session should present this
diagnosis and these options, and ask the user to decide.

## 4. Artifacts the fresh session inherits

### Documentation

- This handoff document (you are reading it).
- The prose proof attempt:
  `docs/research/2026-05-02-ksim-tower-bound-dominates-inline-prose-proof.md`.
  Contains the math-level argument that failed adversarial
  review.  Useful for understanding the failure mode in detail.
- The level-2 chain investigation:
  `docs/research/2026-05-02-level-2-chain-infrastructure-investigation.md`.
  Catalog of existing project infrastructure for the level-2
  chain.  Mostly useful under Option B; partially useful under
  Option A (the K^sim definition and PolyBound infrastructure
  catalog still apply).
- The polynomial-bound research doc:
  `docs/research/2026-04-30-ksim-polynomial-bound-references.md`.
  Original literature-collation document.  Contains Lemma 1.A,
  Wong's recipe, and other internal lemmas that may or may not
  apply under Option A.

### Failed plans (preserved as records)

- `docs/plans/2026-05-01-poly-bound-task-17c-chain-assembly-plan.md`
  (plan v2, claimed impossible PolyBound).
- `docs/plans/2026-05-02-towerbound-architecture-design.md` and
  `-plan.md` (v3, mathematically false TowerBound).
- `docs/plans/2026-05-02-ksim-tower-bound-dominates-inline-plan.md`
  (v4, glossed Nat.rec→iterate bridge).
- `docs/plans/2026-05-02-ksim-tower-bound-dominates-inline-plan-v5.md`
  (v5, false linear bound at level 1).
- All marked SUPERSEDED at the top of each file.

### Existing K^sim hierarchy design

`docs/lawvere-k-sim-hierarchy.md` (1100+ lines).  The original
design document.  Section 2 covers the categorical
equivalence; Appendix A (line 1119+) is the URM simulation
construction for the erToK direction.  Highly relevant for
understanding the project's current shape and what Option A
would look like.

### kToER design and plan

- `docs/plans/2026-04-29-lawvere-k-sim-ktoer-design.md`
- (kToER implementation plan: superseded by Phase 2 sub-project
  1 task list, see #251).

These document the direct-translation strategy that has been
failing.

### Existing source code

`GebLean/` contains ~5000 lines of Lean code.  Modules:

- Phase 1: `LawvereKSim.lean`, `LawvereKSimInterp.lean`,
  `LawvereKSimQuot.lean`, `LawvereKSimCat.lean`.  Infrastructure
  for the K^sim category.  Reusable under any option.
- Phase 2: `LawvereKSimER.lean` (kToER definition),
  `Utilities/KSimSzudzikSimrec.lean`,
  `LawvereERPolynomialBound.lean`,
  `LawvereKSimPolynomialBound.lean`,
  `Utilities/ComputationalComplexity.lean`.
  Built for the direct-translation strategy.  Some pieces
  reusable under Option A; most of `LawvereKSimPolynomialBound`'s
  level-2 work is the failed strategy and would be deleted.

## 5. The fresh session's first task

The fresh session should:

1. **Read this handoff document end-to-end.**
2. **Read** the K^sim hierarchy design (`docs/lawvere-k-sim-hierarchy.md`),
   particularly Appendix A on URM simulation.
3. **Read** the prose proof
   (`docs/research/2026-05-02-ksim-tower-bound-dominates-inline-prose-proof.md`)
   to understand the failure mode in detail.
4. **Present the diagnosis to the user**: the pattern of v2-v5
   failures, the URM vs direct-translation asymmetry, and the
   three options A/B/C.
5. **Ask the user to choose an option.**

If the user chooses Option A:

- Brainstorm the URM-simulation strategy for kToER.
- Write a design document parallel in structure to Appendix A
  but for the kToER direction.
- Adversarially review the design.
- Write an implementation plan grounded in the design.
- Adversarially review the plan.
- Iterate until convergence.
- Execute via subagent-driven-development.

If the user chooses Option B:

- Identify the specific infrastructure change(s) most likely
  to make the dominance proof close.
- Write a prose proof of the dominance under the proposed
  infrastructure.
- Adversarially review the prose proof.
- Iterate until convergence.
- Then implementation plan + execution.

If the user chooses Option C:

- Discuss what the project should pursue instead.
- Plan the deletion / archival of failed work.
- Update the project's high-level documentation accordingly.

## 6. Status of related items

### Items completed

- Phase 1 (K^sim category infrastructure): COMPLETE, no rework
  needed under any option.
- Phase 2 closure proofs (Appendix A URM simulation for erToK):
  COMPLETE in design; implementation pending.
- Phase 2 sub-project 1 kToER Tasks 1-13 (defining kToER + kToERN
  by direct translation): COMPLETE as definitions, but Tasks
  14+ (kToER_interp, functor laws) depend on the failed
  dominance proof and CANNOT be completed under the current
  strategy.
- Polynomial-bound Module A and B
  (`Utilities/ComputationalComplexity` plus `ERMor1.PolyBound`):
  COMPLETE; reusable under any option.
- Polynomial-bound Module C (`LawvereKSimPolynomialBound`):
  PARTIALLY COMPLETE; the level-1 chain (Tasks 17a, 17b)
  is built and proven, the level-2 chain (Task 17c) is the
  failed work.

### Items pending

- kToER Tasks 14-22 (kToER_interp, kToERN_interp, kToERFunctor,
  functor laws, tests, re-export, final verification).  ALL
  blocked on the dominance proof, which has failed under the
  direct-translation strategy.
- Polynomial-bound Tasks 18-21 (Module C tests, re-exports,
  final verification).  Blocked on the level-2 chain.
- Phase 2 closure-proof IMPLEMENTATION (Appendix A is designed
  but not Lean-realized).  Independent of the kToER blocker.

### Recommended kill list under Option A

If Option A is chosen, the following items become dead:

- All level-2 work in `LawvereKSimPolynomialBound.lean` (the
  Task 17c E-helpers and L-helpers, lines 322-2729).  Roughly
  2000 lines of Lean code.
- `kSimTowerBound`, `iterAutoBoundExpr`, the dominance proof
  scaffolding (Utilities/KSimSzudzikSimrec.lean, ~150 lines
  beyond the seqPack pairing infrastructure).
- The polynomial-bound design doc
  (`docs/plans/2026-04-30-er-polynomial-bound-design.md`) and
  associated plans, except for Modules A and B.
- All five failed plans (already marked SUPERSEDED).

Lines reusable from `LawvereKSimPolynomialBound`:

- The `KMor1.simrecVec` infrastructure (helper for K^sim
  semantics, level-agnostic).
- Possibly the `ConstantOrShiftedProj` shape lemma (Lemma
  1.B), if URM simulation needs it (likely yes for some
  internal complexity bound).

## 7. Open questions for the user

The fresh session should ask the user, after presenting the
diagnosis:

1. Which option (A/B/C) do you want to pursue?
2. Under Option A, do you want to keep the existing direct-
   translation `kToER` definition as a reference (renamed,
   marked deprecated) or delete it entirely?
3. Under Option A, the URM-simulation construction for kToER
   will likely produce a different `kToERFunctor` shape than
   originally designed.  Any constraints on the final shape?
4. Should this pivot decision affect the broader Geb project's
   architectural goals around `K^sim` (e.g., is K^sim still
   the right intermediate language for the broader project, or
   should we use a different intermediate)?

## 8. Brief commit log of relevant recent work

(For the fresh session to read git history if needed.)

```text
93f07a00 Scope CLAUDE.md literature-citation discipline correctly
1d4cf080 Add literature-citation discipline to CLAUDE.md
3c34c33a Investigation doc: level-2 chain infrastructure catalog
f2428500 Add literature citations to level-1/2 chain helpers
4b8c31ed TowerBound v3 architecture design (replaces plan v2)
6bfb9390 TowerBound v3 implementation plan
18dccfb4 Mark TowerBound v3 design + plan as superseded
c5fe1173 Plan v4: literature-aligned level-1-mirror
39c731b1 Plan v5: investigation-driven mirror of level-1 chain
7805d18e Mark plan v5 as superseded
aeeab90f Prose proof of kSimTowerBound_dominates_inline
[the prose proof failed adversarial review on 2026-05-02 evening]
```

## 9. Closing note

Five iterations of plan + adversarial review for the
direct-translation strategy have not converged.  The pattern
is consistent enough that further iteration in the same
strategy is not the right move.  The fresh session's first
duty is the architectural decision, not another planning
attempt.  If the user chooses Option A (most likely), the
next session has substantial groundwork: a new design doc, a
new plan, careful adversarial review at each stage, then
execution.  But the path is, at last, literature-aligned.
