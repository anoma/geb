# Post-T2 handoff — followup branch + T3 brainstorming

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Where we are](#where-we-are)
- [Two next steps](#two-next-steps)
- [Step A — Followup cleanup branch (task #654)](#step-a--followup-cleanup-branch-task-654)
  - [Pure renaming (item batch — 1 commit)](#pure-renaming-item-batch--1-commit)
  - [Dead-code / docstring sweep (~3 small commits)](#dead-code--docstring-sweep-3-small-commits)
  - [Structural extraction (~4 medium commits)](#structural-extraction-4-medium-commits)
  - [Re-`private`-ization (~1 commit, surgical)](#re-private-ization-1-commit-surgical)
  - [Speculative refactor (separate sub-branch if pursued)](#speculative-refactor-separate-sub-branch-if-pursued)
  - [Workflow](#workflow)
- [Step B — T3 brainstorming and spec (Ksim simulator)](#step-b--t3-brainstorming-and-spec-ksim-simulator)
  - [Inputs (binding for T3 brainstorming)](#inputs-binding-for-t3-brainstorming)
  - [Open design questions for brainstorming](#open-design-questions-for-brainstorming)
  - [Brainstorming and spec workflow](#brainstorming-and-spec-workflow)
  - [Expected size](#expected-size)
- [Recommended ordering](#recommended-ordering)
- [Operational rules (carry forward from T2)](#operational-rules-carry-forward-from-t2)
- [Reusable T2 patterns](#reusable-t2-patterns)
- [Resumption prompt](#resumption-prompt)
- [References](#references)

<!-- END doctoc -->

Handoff for the next two work units after T2's completion. T2
landed `compileER_runFor` (the climactic ER → URM correctness
theorem) on 2026-05-20 across nine T2-final commits
(`e09ba15a`, `30f570dd`, `4677a7b5` for this session's three;
the full chain dates back to the T1/T2 plan landing at the
start of the workstream). The next two steps are independent
and can be scheduled in either order.

## Where we are

The ER ↔ K^sim_2 categorical equivalence project decomposes
into a forward direction (`kToER`, complete) and a reverse
direction (`erToK`, T1+T2 complete, T3+T4+T5 remaining), plus
a final categorical-iso packaging. Status at 2026-05-20:

| Workstream | Description | Status |
| --- | --- | --- |
| kToER (Steps 0–5) | Structural-induction proof of `K^sim_2 ⊆ ER` plus `kToERFunctor` | Complete |
| T1 (≈ Step 7) | URM kernel `GebLean/Utilities/ZeroTestURM.lean` | Complete |
| T2 (≈ Steps 6+8) | ER → URM compiler + `compileER_runFor` in `GebLean/LawvereERKSim/` | Complete |
| Followup #654 | Deferred cleanups (naming, refactor, private re-evaluation) | Pending (optional) |
| T3 (≈ Step 9) | K^sim simulator for URM kernel + runtime bound | Pending |
| T4 (≈ Step 10) | `erToK` assembly + `erToKFunctor` | Pending |
| T5 (≈ Step 11) | Strict iso `LawvereERCat ≌ LawvereKSimDCat 2` | Pending |

Binding documents for the landed work:

- Master design:
  `docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
- Spec (T1 + T2):
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.
- T2 plan:
  `docs/superpowers/plans/2026-05-17-step-t2-er-to-urm-compiler.md`.
- T2 Task 11 partial-completion handoff (also the followup
  catalogue):
  `docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md`.

## Two next steps

**Step A — Followup cleanup branch (task #654)**: optional
multi-item cleanup of T2 stylistic / structural debt. Self-
contained; does not require T3 to be designed.

**Step B — T3 brainstorming and spec (K^sim simulator)**: the
next major workstream, building the K^sim simulator that
consumes T2's compiled URM. This is the critical-path piece
for the categorical equivalence.

The two are independent and may run in either order or in
parallel (on separate branches).

## Step A — Followup cleanup branch (task #654)

**Sub-skill**: `superpowers:subagent-driven-development` (some
items individually fit `superpowers:executing-plans` or
`commit-commands:commit`).

**Branch posture**: one fresh topic branch from `main` at T2's
final commit (`4677a7b5` or the chore commit that supersedes
it if any follow-on has landed). The followup work touches
multiple submodules and crosses file-scope boundaries (the
rename items in particular), so the "one concern per branch"
rule says it should not bundle with T3.

**Items (live list in task #654's description; historical
context in `2026-05-18-step-t2-t11-handoff.md` § Followup
branch (post-T2))**. Grouped by character:

### Pure renaming (item batch — 1 commit)

- Rename Prop-valued structures to `UpperCamelCase`:
  `preservingTransferInstrs` → `PreservingTransferInstrs`,
  `transferLoopInstrs` → `TransferLoopInstrs`,
  `subInnerLoopInstrs` → `SubInnerLoopInstrs` (in
  `GebLean/LawvereERKSim/Loops.lean`); `inputCopies_disj` →
  `InputCopiesDisj` (in
  `GebLean/LawvereERKSim/Comp.lean`). Update every reference
  site across `Loops.lean`, `Atoms.lean`, `Comp.lean`,
  `BSum.lean`, `BProd.lean`. ~30 reference sites.
- Rename theorems prefixed by a structure name to
  `snake_case`:
  `PreservingTransferInstrs_compileFrag_comp_inputCopies`,
  `TransferLoopInstrs_compileFrag_comp_outputTransfer`
  (Loops.lean);
  `ProgramEmbedsFragment_compileFrag_comp_fBody`,
  `ProgramEmbedsFragment_compileFrag_comp_gsBody`
  (Comp.lean);
  `ProgramEmbedsFragment_compileFrag_bsum_fBody` (BSum.lean);
  `ProgramEmbedsFragment_compileFrag_bprod_fBody`
  (BProd.lean).
- Rationale: mathlib's `naming.html` requires `UpperCamelCase`
  for structures and `snake_case` for theorems regardless of
  Prop-valued vs Type-valued.

### Dead-code / docstring sweep (~3 small commits)

- Sweep dead `have h_eq` at BSum.lean:3078; dead
  `have h_numRegs_pos` at BSum.lean:3703.
- Audit `## Main definitions` / `## Main statements` sections
  in each submodule docstring; remove private declarations
  that have been incorrectly listed (Compiler.lean was
  flagged in earlier review).
- Update `BSum.lean`'s `## Main statements` to include the
  session-6 additions (`compileFrag_bsum_partial_phase_i2`,
  …, `compileER_pre_stop_correct_bsum`,
  `compileER_runFor_bsum`, …).
- Add `/-! ### ... -/` section markers to `Comp.lean` around
  its six logical phases (length, k=0, sub-block, m-step,
  outer iteration, assembly, runFor wrapper).
- Replace `set sPost := …` / `set sFinal := …` in
  `compileER_pre_stop_correct_bsum` with plain `let` (their
  RHSes are intermediate states not referenced from any
  parameter type).

### Structural extraction (~4 medium commits)

- Extract `gsPrefixSum_mono ≤-form` so phases i.1, i.2, i.3
  can replace their inlined `h_aux_mono` calls.
- Extract `compileFrag_comp_subBlocks_partial_phase_i1_setup`
  shared between phase i.1 preservation and the strict-bound
  helper (~140 LOC dedup).
- Extract `compileFrag_comp_size` and
  `compileFrag_comp_pcOf_top` for bsum/bprod reuse.
- Extract `h_foldl_le`, `h_foldl_map_eq`, `h_outerSum_eq`
  helpers from their inline appearances in BSum.lean and
  Comp.lean into a shared location (`Loops.lean` or
  `Comp.lean`). After `h_outerSum_eq` migrates out of
  `BSum.lean`, restore `private` on `vPrefixSum_succ` and
  `vPrefixSum_eq_foldl_finRange` in `Comp.lean`.
- Extract a shared `compileFrag_bsum_rawList_scaffold` (or
  `compileFrag_bsum_segment_at` parameterised by segment
  offset + extractor) to deduplicate the
  `_zeroSweep_instr_at` / `_prologueBlock_instr_at` /
  `_accUpdateBlock_instr_at` cluster.
- Extract a shared `s0 → s4` prelude step-ladder lemma
  between `compileFrag_bsum_partial_base` and
  `compileFrag_bsum_prelude_pc_strict_bound` (~75%
  duplication).
- Extract an `outside_preserved_at r h_outside` tactic-level
  macro for the 5-line ritual in phase_i2 lemmas across
  BSum, Comp, and BProd.

### Re-`private`-ization (~1 commit, surgical)

- Re-evaluate `private` promotions across submodules.
  `Loops.lean` has 10 declarations promoted to public; each
  has at least one current cross-file consumer. `Embedding.lean`
  has 6 declarations pre-emptively promoted without current
  consumers (`getElem_of_getElem?_some`,
  `stateEmbedsFrag_step`, …). Restore `private` on items
  whose only consumers are now in the same file.

### Speculative refactor (separate sub-branch if pursued)

- Factor the shared outer-iteration scaffolding between
  `BSum.lean` and `BProd.lean` (zero-sweep / prologue /
  phase_i0..i3 / partial_step / partial_aux / partial) into
  a parameterised helper family. The pieces that differ are
  the f-body witness, the accUpdate block, and the
  PC-layout constants. Speculative — may not be cleaner than
  the current duplication. Defer until a concrete
  parameterised helper sketch has been adversarially
  reviewed.

### Workflow

For each commit:

1. Mark the relevant subset of #654 items as the commit's
   scope.
2. Dispatch implementer subagent (or do directly for small
   single-file edits).
3. Run `lake build` (clean) + `mcp__lean-lsp__lean_verify`
   axiom checks on affected declarations.
4. Run `markdownlint-cli2 'docs/**/*.md'` if any docs touched.
5. Commit with conventional commit prefix (`chore(ertok):` or
   `refactor(ertok):` as appropriate).

Open a PR against `main` once the branch is complete; merge
via the merge-commit strategy per the fork–upstream rule.

## Step B — T3 brainstorming and spec (Ksim simulator)

**Sub-skill**: `superpowers:brainstorming` first (per the
project rule "Always-on for any creative work"), then
`superpowers:writing-plans` once a spec converges.

**Goal**: design a K^sim simulator that runs an arbitrary
URM program (compiled by T2's `compileER`) for `t` steps and
extracts the resulting register-bank state. Combined with
T2's `compileER_runFor`, this yields `erToK : ERMor1 a → KMor1 a`
of level ≤ 2 with `(erToK e).interp v = e.interp v`.

### Inputs (binding for T3 brainstorming)

- The shape of `URMProgram a` and `URMState`:
  `GebLean/Utilities/ZeroTestURM.lean`.
- The shape of `URMState.runFor` and the post-stop semantics
  (`URMState.runFor_stop`): same file.
- The output of `compileER` and `compileER_runtime`:
  `GebLean/LawvereERKSim/Compiler.lean`.
- The master design's §6–§7 prose (preserved as
  forward-looking design): `docs/research/2026-05-02-...md`.
- Tourlakis §0.1.0.37 (URM simulation lemma), §0.1.0.42
  (existence of ER-level runtime bound), §0.1.0.43
  (Ritchie–Cobham), §0.1.0.44 proof (URM simulation chain).
  Citations:
  `PR-complexity-topics.pdf` pp. 15–22.
- Existing K^sim composites under
  `GebLean/Utilities/KArith.lean` and the K^sim level
  hierarchy in `GebLean/LawvereKSim*.lean`.
- The K^sim simulator design sketch in
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`
  §6 (which was specified before T2 landed; check whether
  the assumptions about the URM kernel's shape still
  apply — they should, since T2 followed the spec).

### Open design questions for brainstorming

These are the questions the T3 spec must answer:

1. **K^sim representation of URM state.** The URM state is
   `{pc : ℕ, regs : Fin n → ℕ}` (in our `URMState`
   formulation). K^sim values are `ℕ`. The simulator must
   encode the URM state as a `ℕ` via some pairing (Cantor,
   Szudzik, or `Nat.tuplePack`). Which pairing best supports
   level-≤2 simrec arithmetic?
2. **PC-dispatch combinator.** Tourlakis's §0.1.0.37 uses a
   `switch` over the instruction array. The K^sim
   instantiation needs a level-≤2 case-split combinator.
   `KMor1` has the `boundedSearch` and `discrim`-style
   primitives; does an n-way `switch` need to be built or is
   it already present?
3. **Runtime bound expression.** Tourlakis §0.1.0.42 gives a
   tower-of-exponentials bound on URM runtime for ER
   functions. The bound must be realised as a K^sim term of
   level ≤ 2. The kToER side already has
   `KMor1.majorize_by_A_n_iter` etc.; can `boundExprK` be
   constructed dually as `A_n^r v` for an explicit `r` per
   `ERMor1` constructor?
4. **Encoding the instruction array as K^sim data.** Each
   compiled URM program is a finite array of instructions.
   The K^sim simulator must encode this array as `ℕ` (or as
   a structure that K^sim can decode), then index it by PC.
5. **Output register projection.** Once the simulator
   computes the post-runtime state-`ℕ`, extract
   `outputReg`'s value. Trivial in principle (just unpack)
   but must be expressible in K^sim arithmetic.
6. **Correctness theorem shape.** The dual of
   `compileER_runFor` would be:
   `KSimUlate.interp e v = e.interp v`, where
   `KSimUlate e := boundExprK e ≫ simulate (compileER e)`.
   Whether to package this as a single `KSimUlate` named
   composite or as a multi-step pipeline is a design choice.

### Brainstorming and spec workflow

1. Brainstorm using `superpowers:brainstorming`, focusing on
   the six open questions above. Produce a 5–8 page
   spec draft.
2. Self-review (inline).
3. Adversarial-review loop (≥ 3 rounds, fresh-context Agent
   subagents). Aim for zero blocker, zero serious.
4. Hand off to user review.
5. Once approved, write the T3 implementation plan
   (`superpowers:writing-plans`). Adversarial-review the plan
   ≥ 3 rounds.
6. Hand the plan off to the user. Execute via SDD.

### Expected size

Substantial. Tourlakis §0.1.0.37 is 1–2 pages of dense
register-machine simulation; the K^sim instantiation is
likely ≈ 10 000–20 000 LOC at the same level of detail T2
exhibits.

## Recommended ordering

The followup branch (Step A) and T3 (Step B) are
independent. Either order works. Two pragmatic patterns:

- **A → B** (cleanup first): get T2 code as polished as
  possible before T3 starts, so T3's spec/plan citations to
  T2 names are stable. Lowers refactor churn during T3.
- **B brainstorming, A in parallel, B implementation after
  A**: brainstorm T3 immediately while running cleanup on
  the side. T3's brainstorming benefits from looking at T2
  fresh; the cleanup branch can land independently.

Default if uncertain: **A → B**. The cleanup is small
(~10 commits, ~1–2 days at sub-agent throughput) and avoids
T3 spec churn.

## Operational rules (carry forward from T2)

- No `jj git push` without user line-by-line review.
- No raw mutating `git` subcommands.
- No `noncomputable`, no `admit`, minimal `Classical`.
- One concern per branch.
- Markdownlint cleanliness on any `.md` touched.
- `lake build` only (never `lake env lean`, never
  `lake clean`).
- Conventional commits (`feat(ertok):`, `fix(ertok):`,
  `chore(ertok):`, `refactor(ertok):`, etc.).
- Cite literature for every transcribed lemma; cite
  internal reuse points.

## Reusable T2 patterns

For T3 implementation (when it starts), the patterns
catalogued during T2 are worth pre-loading into each
implementer subagent's brief. The canonical list is in
`docs/superpowers/plans/2026-05-20-step-t2-t11-bprod-execution-session3-handoff.md`
§ "Patterns surfaced during session 2" (lines 84–157) and
`2026-05-18-step-t2-t11-handoff.md` § "Patterns learned"
(lines 749+). Key patterns:

- `set_option maxHeartbeats N in` placement is
  linter-enforced.
- Named single-step helper hypotheses for multi-stage
  `runFor` collapses.
- `change` chains are sanctioned for definitional unfolding.
- `set` vs `let` (`set` only when its rewriting side-effect
  is load-bearing).
- `URMState.init` must be inline before regs-projection
  matching (let-bound blocks reduction).
- mathlib `fin_cases` and `by_cases` can pull
  `Classical.choice`.
- `simp only [if_pos h]` leaks `sorryAx` in the current
  toolchain; use `rw [if_pos h]` instead.

## Resumption prompt

To pick up either step:

```text
Read docs/superpowers/plans/2026-05-20-post-t2-handoff.md
and proceed to <Step A | Step B> per the workflow above.
```

For Step A, the implementer should pull the live curated
item list from task #654's description. For Step B, the
brainstorming subagent should start by reading the master
design's §6–§7 prose, then the T2 spec/plan, and only then
the K^sim composites under `GebLean/Utilities/KArith.lean`.

## References

- Master design:
  `docs/research/2026-05-02-er-ksim2-equiv-via-urm-master-design.md`.
- T1/T2 spec:
  `docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`.
- T2 plan:
  `docs/superpowers/plans/2026-05-17-step-t2-er-to-urm-compiler.md`.
- T2 Task 11 handoff (also followup catalogue):
  `docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md`.
- Per-session T2 execution handoffs:
  `docs/superpowers/plans/2026-05-20-step-t2-t11-*.md`.
- Tourlakis 2018 `PR-complexity-topics.pdf` §0.1.0.37
  (URM simulation), §0.1.0.42 (ER runtime bound), §0.1.0.43
  (Ritchie–Cobham), §0.1.0.44 (`K^sim_n = E^{n+1}` proof).
- Project rules: `CLAUDE.md`, `.claude/rules/lean-coding.md`,
  `.claude/rules/markdown-writing.md`,
  `.claude/rules/fork-upstream-flow.md`.
