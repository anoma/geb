# Potential Port to Lean v4.30.0-rc1

This document captures the state of, and the strategic decision around,
porting the project to `leanprover/lean4:v4.30.0-rc1` against
mathlib master. As of 2026-04-18 the port is paused pending a
decision on whether and how to proceed. The technical details of what
has been investigated live in `lean-430-upgrade.md`; this document
focuses on the high-level options.

## Status snapshot

- Toolchain bumped to `leanprover/lean4:v4.30.0-rc1`; mathlib master
  pinned in `lake-manifest.json`. These changes are committed.
- 18 of 19 affected source files have been migrated to the new mathlib
  API and build clean. The single remaining file is
  `GebLean/Polynomial.lean` (6240 lines).
- Polynomial.lean has approximately 101 reported errors at
  `maxErrors=100`; at least 164 by per-line LSP count. Roughly 30 of
  these are downstream cascading kernel errors that should resolve
  once their upstream definitions elaborate; the remaining ~70 are
  genuine per-proof failures that need fixes.
- Three private `@[simp]` helper lemmas
  (`polynomial_typeCat_{comp,ofHom,eqToHom}_toFun`) plus three
  FunLike-coerced sibling variants
  (`polynomial_typeCat_{comp,ofHom,eqToHom}_apply`) have been added
  at the top of Polynomial.lean. The `_apply` variants are the ones
  that actually fire under the current mathlib simp set.
- One previously broken lemma (`polyCompGObj_iso_inv_hom_base`) has
  been fixed in an earlier agent run; that fix is committed.
- All other proof modifications attempted in this session have been
  reverted; the working tree currently has only the helpers and the
  earlier fix on top of the `869c4800 in-progress 4-30-port` commit.

## Why the port is hard

The driving change is mathlib's PR #36613 (April 14, 2026), which
refactored the category structure on `Type u`:

- Morphisms in `Type u` are no longer raw functions. They are now a
  one-field structure `TypeCat.Hom X Y` wrapping a one-field structure
  `TypeCat.Fun X Y` wrapping `X → Y`.
- The promotion `TypeCat.ofHom : (X → Y) → (X ⟶ Y)` is required
  whenever a function is used as a morphism.
- Specialised lemmas like `FunctorToTypes.map_comp_apply` and
  `types_comp_apply` are deprecated in favour of
  `Functor.map_comp_apply`, `ConcreteCategory.comp_apply`, and the
  generic `elementwise` mechanism.

For mathlib itself the refactor touched 306 files with about
3381 insertions and 2846 deletions; the average per-file diff is
~11 lines added, ~9 removed. Most files needed only mechanical
rewrites: wrapping bare functions with `TypeCat.ofHom`, replacing
`funext` with `ext`, swapping a few lemma names. Mathlib also added
`unif_hint` declarations (notably in `Yoneda.lean`) so that
downstream code writing `Y ⟶ X` continued to elaborate when the
expected type was `(yoneda.obj X).obj (op Y)`.

Polynomial.lean is an outlier in the same sense as mathlib's hardest
files in that PR (e.g. `Sites/Coherent/LocallySurjective.lean`).
It contains roughly 40 dense proofs that compose three or four layers
of dependent Sigma transports through `polyCompGObj_isoHom`/`Inv`,
`ccrFiberMor`, `ccrReindex`, and `αf.hom`/`αf.inv`. The proofs were
written assuming that `Type u` morphisms reduce to bare functions
under `rfl`/`simp`, which is no longer the case.

## What we have learned

Three root causes were identified and verified:

**Root cause A.** Mathlib's `@[simp high] lemma TypeCat.Fun.toFun_apply :
f.toFun x = f x` fires before any local helper that has `.toFun` on
the LHS. The first batch of `_toFun` helpers we added were therefore
silently pre-empted; the `_apply` (FunLike-coerced) variants are the
ones that actually have a chance to fire.

**Root cause B.** The dependent-Sigma shape of our proofs causes
`rw`/`conv` rewrites of the `_apply` helpers to fail with
*"motive is not type correct"*. Lean cannot abstract the rewritten
argument because elsewhere in the goal the same value appears in a
type-determining position. Both `rw` and `conv_lhs => rw` fail;
`simp only` declines to fire silently. Mathlib's typical files do
not encounter this because their proofs are not Sigma-transport heavy.

**Root cause C.** After the two preceding obstacles are worked around
via the morphism-level proof strategy
(`apply Over.OverMorphism.ext` → `apply ConcreteCategory.ext_apply`
→ `rintro ⟨e, ef⟩` → ...), the remaining `erw` chain that closes the
proof passes the LSP's elaborator but fails the kernel batch check
during `lake build`. The LSP runs more liberal defeq tolerance; the
batch check does not. Workarounds require either a custom
`Eq.rec`-based lemma per occurrence or term-mode proofs at the
critical steps.

Two mechanical levers that mathlib used effectively were tested and
do **not** help our case:

- File-level `set_option backward.isDefEq.respectTransparency false`
  resolved zero of our 101 errors. The flag only restores pre-4.30
  defEq behaviour for proofs that relied on it; our failures are
  elsewhere.
- `unif_hint` declarations for our `(ConcreteCategory.hom (TypeCat.ofHom
  f)) x ≟ f x` patterns also resolved zero errors. Unification hints
  help during type-level elaboration; our failures are inside tactic
  blocks at `rfl`/`simp`/`rw` time.

## Calibration: how fast can the work proceed?

Two autonomous-agent runs were used to estimate the steady-state
per-proof rate.

The first agent ran without root-cause knowledge: 100 tool calls,
~100 minutes, fixed one lemma in region 1 with partial progress on
two others.

The second agent ran with both root causes documented in the prompt
and the morphism-level strategy spelled out: 128 tool calls,
107 minutes, claimed four LSP-green lemmas — but the batch kernel
check still rejected them due to root cause C, which we had not
known about going in. Its worktree was cleaned up on termination
because the prompt told it not to commit, so the actual code was
not preserved.

A reasonable steady-state estimate is **~40-45 minutes per complex
proof** including the kernel-residual work. Polynomial.lean has
approximately 40 such proofs, plus ~30 cascading kernel errors that
should resolve as their upstream proofs land. Total expected work to
finish the port: **~25-30 hours** of focused human or agent time.

## Options for proceeding

If we choose to proceed, two paths are reasonable. A third option
(do nothing for now) is also viable.

### Option 1: restructure the definitions

Rewrite the dense Sigma-transport definitions in Polynomial.lean
(`polyCompGObj_isoHom`/`Inv`, `polyComp_fiberMor_roundtrip`,
`polyBetweenToWTypeMap`, `unitBase`/`counitIndex`/`counitFiberMap`,
`polyCell*`, etc.) so that the fiber data is exposed in a form that
does not require the elaborator to abstract through dependent Sigma
positions. Concretely, possibilities include:

- Introducing a named `WTypeIndex` structure (or pair of structures)
  rather than nested `Sigma` types, so that `.fst`/`.snd` projections
  become field accessors that elaborate uniformly.
- Threading the family equality (`ccrReindex_hom_inv_cancel` etc.)
  through an explicit `Eq.rec` motive in the morphism construction,
  so that the resulting equation is over a single canonical type
  rather than a nested cast.
- Moving the morphism-level fiber roundtrip into a category-level
  isomorphism so the `inv ≫ hom = eqToHom _` fact is structural and
  the per-point proofs are unnecessary.

If a restructure of this kind succeeds, most of the per-proof
problems collapse: many of the existing pointwise `Sigma.ext rfl`
patterns become provable with the same one-line tactic mathlib uses.
The downstream regions (5, 6, 7) may also collapse because the
upstream definitions whose elaboration is currently failing would
become tractable.

Cost estimate: **2-4 days of design work** to settle the new
representation, then the per-proof rate falls to mathlib's typical
~5-10 minutes. Risk: the restructure might propagate changes outside
Polynomial.lean (we already moved past 18 sibling files; some may
need to be re-touched). Worst case: the restructure does not
actually simplify the proofs and we have spent the design time
without payoff. Upside: if it works, total time-to-clean is probably
**8-15 hours** rather than 25-30, and the resulting code will be
more robust to future mathlib refactors.

### Option 2: accept the long haul

Keep the existing definitions and grind through the proofs one by
one using the morphism-level strategy plus per-proof workarounds for
the kernel-batch-check residual. Either:

- A series of tightly-scoped sessions in which a human or agent
  fixes 3-5 proofs per session and commits. Expected: **8-10 sessions
  of ~3 hours each**, total **~25-30 hours**.
- A single long-running agent loop that commits incrementally to its
  own branch, with explicit instructions to stop and report after
  each successful proof. Workflow risk: previous attempts have shown
  that long-running agents lose work if they don't commit, and that
  ~20% of "completed" proofs may pass LSP but fail `lake build`.

Cost estimate: the calibrated **~25-30 hours**, distributed across
several sessions. Risk: some proofs in regions 5-7 may need
restructuring anyway because the kernel cascade hides definition-
level failures we have not yet seen. Some may be intractable without
the kind of representation change that Option 1 contemplates.
Upside: incremental progress is visible and committable; no design
risk.

### Option 3: defer or roll back

Hold the toolchain at the version from before the mathlib refactor
until the port is genuinely needed. The 4.30 features that prompted
the upgrade (if any) would need to be enumerated and weighed against
the ~25-30 hour cost. If most ongoing development can proceed on the
older toolchain, this is the cheapest option and buys time for
either mathlib or the Lean elaborator to make subsequent changes
that ease the port.

Cost: zero now; some non-zero future cost when the port is
inevitable. Risk: drifting further from mathlib master makes the
eventual port harder, not easier. Upside: avoids spending 25-30 hours
right now on infrastructure work.

## Recommendation criteria

The choice between Options 1, 2, and 3 turns on three questions:

1. **Is there a 4.30-only feature blocking other work?** If yes,
   Options 1 or 2. If no, Option 3 is most pragmatic.
2. **Is the design-restructure risk acceptable?** If you have a clear
   intuition about how to express the fiber data without nested
   dependent Sigmas, Option 1 is much faster to total completion. If
   the structures feel essential as written, Option 2 is the safer
   bet.
3. **Do we trust async agents to progress incrementally without
   work loss?** If yes, Option 2 with agent dispatch is reasonable.
   If we'd rather do this interactively, Option 2 needs a human at
   the keyboard for ~25-30 hours.

In the absence of a 4.30 feature dependency, my recommendation is
Option 3 in the short term, with an explicit revisit when something
4.30-specific is wanted. If a port is needed, Option 1 has the
better expected value despite higher design risk.

## Pointers

- Technical investigation log: `lean-430-upgrade.md`
- Memory note for cross-session continuity:
  `~/.claude/projects/-home-terence-git-workspaces-geb/memory/project_lean_430_upgrade.md`
- Mathlib refactor PR: #36613, commit `438f134707`, author Dagur
  Asgeirsson. Touches 306 files, 3381 insertions, 2846 deletions.
- New `@[simp]` helpers and the existing fix:
  `GebLean/Polynomial.lean` lines 53-100 and approximately line 3289.
