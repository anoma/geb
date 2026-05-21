# Post-T2 followup branch — session handoff

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Context](#context)
- [Branch posture](#branch-posture)
- [Landed sub-tasks (this session)](#landed-sub-tasks-this-session)
- [Deferred sub-tasks (next followup branch)](#deferred-sub-tasks-next-followup-branch)
- [Verification status](#verification-status)
- [Next steps](#next-steps)
- [References](#references)

<!-- END doctoc -->

## Context

Followup branch executing Step A of the post-T2 handoff
(`2026-05-20-post-t2-handoff.md` § Step A) and task #654.
T2 (`compileER_runFor` correctness theorem) landed on 2026-05-20;
this branch resolves the optional cleanup items catalogued in
task #654 between T2's completion and the start of T3 (K^sim
simulator design).

## Branch posture

One topic branch from the T2 final commit (`5786a81c`). All
commits use the `(ertok)` conventional-commit scope. `lake build`
clean after every commit (verified per commit, not just at end).

## Landed sub-tasks (this session)

| Commit | Sub-task | Scope |
| --- | --- | --- |
| `d3b35d65` | A. Pure renames | `preservingTransferInstrs`, `transferLoopInstrs`, `subInnerLoopInstrs` → `UpperCamelCase`; `inputCopies_disj` → `InputCopiesDisj`; six theorems with structure-name prefix lowercased (mathlib `naming.html` conformance). |
| `56c42df9` | B. Dead `have` sweep | Drop unused `h_numRegs_pos` in `compileFrag_bsum_partial_phase_i3`. |
| `0ec405a5` | C. `set` → `let` | `compileER_pre_stop_correct_bsum`'s two `set` calls reduced to `let` (rewriting side-effect not load-bearing). |
| `bdb7361a` | D. `BSum.lean` Main statements | Expand docstring catalogue to cover phase i.2 entries, `compileFrag_bsum_partial_step` / `_aux` / `_partial`, and the `compileER_runFor_bsum` wrapper. |
| `4cef59c9` | E. `Comp.lean` section markers | Add `/-! ### ... -/` markers around body embeddings, k=0 case, sub-block correctness, outer iteration, final assembly, and runFor wrapper phases. |
| `f2cdaa56` | F. `gsPrefixSum_mono` reuse | Replace four inline reproofs of `gsPrefixSum_mono ≤-form` (`h_aux_mono`) with one-line aliases of the existing `Compiler.lean` lemma. |
| `6f78ebfb` | M. Re-privatize Embedding | Restore `private` on seven `Embedding.lean` declarations whose only consumers are within the same file. |
| `e2f25d50` | G (partial). `h_foldl_map_eq` → mathlib | Replace the three inline `h_foldl_map_eq` proofs with `rw [List.foldl_map]` (mathlib's existing equation). |

Total: eight commits, all `lake build`-clean. Net LOC reduction
on the order of ~160 lines (renames are neutral; `gsPrefixSum_mono`
saved ~40; `List.foldl_map` saved ~108; dead-code and re-privatize
trims complete the count).

## Deferred sub-tasks (next followup branch)

The following items in task #654 are deferred because each
requires a non-trivial signature design and an adversarial-review
round before execution; they are duplication-removal refactors and
do not block T3 brainstorming.

- **G (remaining).** Extract `h_foldl_le` (foldl monotonicity for
  pointwise-≤ summand with monotone accumulator) and
  `h_outerSum_eq` (`vPrefixSum (Fin.cons j (Fin.tail v)) (k + 1)
  = j + outerSum`) into shared helpers. Three inline copies of
  each remain in `BSum.lean`, `BProd.lean`, `Comp.lean`. The
  natural home for `h_foldl_le` is `Compiler.lean` (or a new
  `Utilities/ListSum.lean`); for `h_outerSum_eq`, `Comp.lean`
  itself (since `vPrefixSum` lives there). After `h_outerSum_eq`
  migrates, restore `private` on `vPrefixSum_succ` and
  `vPrefixSum_eq_foldl_finRange` in `Comp.lean`.
- **H.** Extract `compileFrag_comp_size` and
  `compileFrag_comp_pcOf_top` for bsum/bprod reuse. Currently each
  is locally re-derived in the bsum/bprod assembly proofs.
- **I.** Extract
  `compileFrag_comp_subBlocks_partial_phase_i1_setup` shared
  between phase i.1 preservation and the strict-bound helper
  (~140 LOC dedup in `Comp.lean`).
- **J.** Extract a shared
  `compileFrag_bsum_rawList_scaffold` (or
  `compileFrag_bsum_segment_at` parameterised by segment offset +
  extractor) to deduplicate the `_zeroSweep_instr_at` /
  `_prologueBlock_instr_at` / `_accUpdateBlock_instr_at` cluster
  in `BSum.lean` (~70% overlap).
- **K.** Extract a shared `s0 → s4` prelude step-ladder lemma
  between `compileFrag_bsum_partial_base` and
  `compileFrag_bsum_prelude_pc_strict_bound` (~75% duplication).
- **L.** Extract an `outside_preserved_at r h_outside` tactic-
  level macro for the 5-line ritual in phase_i2 lemmas across
  `BSum.lean`, `Comp.lean`, and `BProd.lean`.
- **Speculative (#13).** Factor shared outer-iteration scaffolding
  between `BSum.lean` and `BProd.lean` into a parameterised
  helper family. Defer until a concrete parameterised helper
  sketch has been adversarially reviewed.

Each deferred sub-task is suitable for a fresh followup branch
with its own spec + adversarial-review iteration.

## Verification status

- `lake build` clean after every commit.
- `lake test` not run separately (no tests in this hierarchy
  changed by the cleanup commits).
- Axiom set unchanged: the T2 final commit established
  `[propext, Quot.sound]`-only axiom hygiene for the
  `compileER_runFor` chain. The cleanup commits are pure renames,
  dead-code removals, and proof reuse; none introduces new
  axioms.

## Next steps

Either:

- **Continue cleanup** — open a new followup branch from this
  branch's tip for the deferred sub-tasks above. Each takes a
  short spec + execution.
- **Start T3 brainstorming** — proceed to Step B of
  `2026-05-20-post-t2-handoff.md` (K^sim simulator design).
  T2 names referenced by T3's spec are now stable across the
  followup branch's rename cleanup.

The branch is ready for user line-by-line review and merge to
`origin/main` via the merge-commit strategy per the
fork–upstream rule.

## References

- Plan: `docs/superpowers/plans/2026-05-20-post-t2-handoff.md`.
- Task list: task #654's description and sub-tasks #706–#719.
- T2 plan and final-completion handoffs: see
  `docs/superpowers/plans/2026-05-18-step-t2-t11-handoff.md` and
  the per-session T2 execution handoffs of 2026-05-20.
- Mathlib naming conventions:
  `https://leanprover-community.github.io/contribute/naming.html`.
- Mathlib `List.foldl_map`: `Init.Data.List.Lemmas`.
