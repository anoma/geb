# T4 Tasks 9–15 handoff — `erToKFunctor` assembly

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Where we are](#where-we-are)
- [Branch and commit state](#branch-and-commit-state)
- [What the prior session landed (Tasks 5–8)](#what-the-prior-session-landed-tasks-58)
- [What this session must produce (Tasks 9–15)](#what-this-session-must-produce-tasks-915)
  - [Task 9 — `boundExprK` + level + interp + dominates](#task-9--boundexprk--level--interp--dominates)
  - [Task 10 — `ErToK.lean` + `erToK` + level + interp](#task-10--ertoklean--ertok--level--interp)
  - [Task 11 — `ErToKFunctor.lean` + `erToKN`](#task-11--ertokfunctorlean--ertokn)
  - [Task 12 — `erToKFunctor_map` via `Quotient.liftOn`](#task-12--ertokfunctor_map-via-quotientlifton)
  - [Task 13 — `erToKFunctor_map_id` and `_map_comp`](#task-13--ertokfunctor_map_id-and-_map_comp)
  - [Task 14 — `erToKFunctor` assembly](#task-14--ertokfunctor-assembly)
  - [Task 15 — Re-export, axiom audit, lint sweep, tests](#task-15--re-export-axiom-audit-lint-sweep-tests)
  - [Final — Holistic code review](#final--holistic-code-review)
- [Available infrastructure consumed by Tasks 9–15](#available-infrastructure-consumed-by-tasks-915)
- [Axiom envelope expectations](#axiom-envelope-expectations)
- [Subagent-driven-development plan](#subagent-driven-development-plan)
- [Operational rules (carry forward)](#operational-rules-carry-forward)
- [Resumption prompt](#resumption-prompt)
- [References](#references)

<!-- END doctoc -->

Binding handoff for the dedicated follow-up session that
finishes T4 by producing the `erToKFunctor : LawvereERCat ⥤
LawvereKSimDCat 2` functor. The previous session
(2026-05-23, commits up through `3e1dd99`) closed Tasks 0–8
of the T4 plan, leaving Tasks 9–15 plus the holistic final
review for this session.

## Where we are

T4 decomposes into 15 SDD tasks (plus a final holistic
review). Tasks 0–8 are committed; Tasks 9–15 are pending.

| Task | Description | Status |
| --- | --- | --- |
| 0 | Baseline verification | Complete |
| 1 | `KMor1.maxK` in `KArith.lean` | Complete (commit `90f03b1`) |
| 2 | `KMor1.maxOver` in `KArith.lean` | Complete (commit `17dcc48`) |
| 3 | `KMor1.pow2_iter` in `KArith.lean` | Complete (commit `e8c0028` prereq) |
| 4 | `RuntimeBound.lean` scaffold + `boundExprKParams` | Complete (commit `e8c0028`) |
| 5–8 | `boundExprKParams_dominates` (joint commit) | Complete (commit `3e1dd99`) |
| 9 | `boundExprK` + level + interp + dominates | Pending |
| 10 | `ErToK.lean` + `erToK` + level + interp | Pending |
| 11 | `ErToKFunctor.lean` + `erToKN` | Pending |
| 12 | `erToKFunctor_map` via `Quotient.liftOn` | Pending |
| 13 | `erToKFunctor_map_id` and `_map_comp` | Pending |
| 14 | `erToKFunctor` assembly | Pending |
| 15 | Re-export, axiom audit, lint sweep, tests | Pending |
| Final | Holistic code review | Pending |

## Branch and commit state

- Branch: `feat/ertok-runtime-bound` (child of `main`).
- Tip: `uzymllsp 3e1dd99` — `feat(ertok): prove
  boundExprKParams_dominates joint runtime+value bound`.
- Working copy at branch tip: empty change, clean.
- Project-wide `lake build` clean (1533 jobs), `lake test`
  clean, `bash scripts/check-axioms.sh
  GebLean/LawvereERKSim/RuntimeBound.lean` reports only the
  standard allowlist (`propext`, `Quot.sound`,
  `Classical.choice` via the `Fin.lastCases_castSucc`
  AXIOM_ALLOW).

## What the prior session landed (Tasks 5–8)

`GebLean/LawvereERKSim/RuntimeBound.lean` now contains the
post-convergence recipe `boundExprKParams` and the joint
runtime+value bound theorem. The shape (the public surface
downstream tasks consume):

```lean
def boundExprKParams : {a : ℕ} → ERMor1 a → ℕ × ℕ
-- recipe values per spec §4.2; not repeated here

theorem boundExprKParams_dominates {a : ℕ} (e : ERMor1 a) :
    ∀ (v : Fin a → ℕ),
      LawvereERKSim.compileER_runtime e v ≤
          tower (boundExprKParams e).1
                (Fin.maxOfNat _ v + (boundExprKParams e).2) ∧
      e.interp v ≤
          tower (boundExprKParams e).1
                (Fin.maxOfNat _ v + (boundExprKParams e).2)
```

The theorem carries an `AXIOM_ALLOW: Classical.choice`
annotation justified by the `Fin.lastCases_castSucc` simp
route used in the bsum/bprod cases. Downstream tasks may
freely consume both conjuncts; the runtime conjunct will
feed `boundExprK_dominates` (Task 9), and the value conjunct
is not directly used downstream (Task 9 keeps it for
symmetry with the kToER-side `KMor1.majorize` shape).

Helper infrastructure in `RuntimeBound.lean` (`private`,
already proven):

- `cm_le_tower_two`, `foldl_map_le_length_mul`,
  `foldl_finRange_le_mul_maxOfNat`, `Fin.maxOfNat_mono`,
  `natBSum_le_mul_max`, `natBProd_le_pow_max`,
  `two_le_tower`, `foldl_add_mono`, `foldl_add_map_split`,
  `boundExprKParams_mu_ge_two_or_arity_zero`. These may be
  consumed by downstream tasks; if a downstream task needs
  one outside `RuntimeBound.lean`, lift it from `private`
  to `private theorem … :=` in `Utilities/` (with
  reviewer sign-off in the SDD pass).

## What this session must produce (Tasks 9–15)

The spec sections that bind each task are listed under each
task heading. Read the corresponding section of
[`2026-05-22-step-t4-runtime-bound-design.md`](../specs/2026-05-22-step-t4-runtime-bound-design.md)
before dispatching the implementer subagent.

### Task 9 — `boundExprK` + level + interp + dominates

Binding spec section: §6.

Adds three declarations and three theorems to
`GebLean/LawvereERKSim/RuntimeBound.lean` (same file as
the recipe; Task 4's module docstring already names
`boundExprK` in `## Main definitions` and
`boundExprK_dominates` in `## Main statements`):

```lean
def boundExprK : {a : ℕ} → ERMor1 a → KMor1 a := fun e =>
  let p := boundExprKParams e
  KMor1.comp
    (KMor1.pow2_iter p.1)
    (fun _ : Fin 1 =>
      KMor1.comp KMor1.add
        (fun i : Fin 2 =>
          match i with
          | ⟨0, _⟩ => KMor1.maxOver a
          | ⟨1, _⟩ => KMor1.natK' a p.2))

theorem boundExprK_level {a : ℕ} (e : ERMor1 a) :
    (boundExprK e).level ≤ 2

theorem boundExprK_interp {a : ℕ} (e : ERMor1 a)
    (v : Fin a → ℕ) :
    (boundExprK e).interp v
      = tower (boundExprKParams e).1
              (Fin.maxOfNat _ v + (boundExprKParams e).2)

theorem boundExprK_dominates {a : ℕ} (e : ERMor1 a)
    (v : Fin a → ℕ) :
    LawvereERKSim.compileER_runtime e v
      ≤ (boundExprK e).interp v
```

`boundExprK_interp` unfolds via the `@[simp]` interp lemmas
for `pow2_iter`, `maxOver`, `add`, `natK'` (KArith.lean).
`boundExprK_dominates` chains `boundExprK_interp` with
the runtime conjunct of `boundExprKParams_dominates`.
`boundExprK_level` chains the level lemmas of the underlying
composites; the bound is `Nat.max`-fold over component
levels, capped at 2 by `pow2_iter_level`, `maxOver_level`,
and `natK'_level`.

Expected LOC: 80–150 (the def is small; the level and
interp proofs are mechanical chases through `@[simp]`
lemmas; the dominates proof is a one-line rewrite plus
the existing dominates conjunct).

### Task 10 — `ErToK.lean` + `erToK` + level + interp

Binding spec section: §7. Creates the new module
`GebLean/LawvereERKSim/ErToK.lean`.

```lean
def erToK : {a : ℕ} → ERMor1 a → KMor1 a := fun e =>
  KMor1.comp
    (KSimURMSimulator.simulate (compileER e))
    (Fin.cons (boundExprK e) (fun i : Fin a => KMor1.proj i))

theorem erToK_level {a : ℕ} (e : ERMor1 a) :
    (erToK e).level ≤ 2

theorem erToK_interp {a : ℕ} (e : ERMor1 a) (v : Fin a → ℕ) :
    (erToK e).interp v = e.interp v
```

`erToK_level` folds the per-component levels: head
`simulate_level (compileER e) ≤ 2` (T3), `boundExprK_level
e ≤ 2` (Task 9), projections at level 0. `erToK_interp`
chains `KMor1.interp_comp`, T3's `simulate_interp`, and T2's
`compileER_runFor`, with the runtime hypothesis
`(boundExprK e).interp v ≥ compileER_runtime e v`
discharged by `boundExprK_dominates`. This is the central
correctness theorem; expect the proof chain to traverse
both T2 and T3 surfaces.

Expected LOC: 80–180.

Module docstring sketch (per spec §9):

```text
# `erToK` — single-output ER-to-K^sim translator

This module realises the ⊇ direction of Tourlakis 2018
Corollary 0.1.0.44 at `n = 2`: every ER morphism is
representable as a depth-2 K^sim morphism with the same
input/output behaviour. The step-count is bounded by the
runtime-bound recipe from `RuntimeBound.lean`.

## Main definitions

- `erToK` : the single-output translator.

## Main statements

- `erToK_level` : level ≤ 2 for every input ER morphism.
- `erToK_interp` : interp-faithfulness.

## References

- Tourlakis 2018, *Topics in PR Complexity*, §0.1.0.44.
- Spec: `docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`.

## Tags

ertok, simulator, interp, level
```

### Task 11 — `ErToKFunctor.lean` + `erToKN`

Binding spec section: §8.1. Creates the new module
`GebLean/LawvereERKSim/ErToKFunctor.lean`.

```lean
def erToKN {n m : ℕ} (e : ERMorN n m) : KMorN n m :=
  fun j => erToK (e j)

theorem erToKN_interp {n m : ℕ} (e : ERMorN n m)
    (v : Fin n → ℕ) (j : Fin m) :
    (erToKN e j).interp v = (e j).interp v :=
  erToK_interp (e j) v

theorem erToKN_level {n m : ℕ} (e : ERMorN n m)
    (j : Fin m) : (erToKN e j).level ≤ 2 :=
  erToK_level (e j)

theorem erToKN_compat_extEq {n m : ℕ}
    {e₁ e₂ : ERMorN n m}
    (he : ∀ v j, (e₁ j).interp v = (e₂ j).interp v) :
    ∀ v j, (erToKN e₁ j).interp v
            = (erToKN e₂ j).interp v
```

Componentwise applications of Task 10. Expected LOC: 30–60.
The compat lemma's body is a one-liner that rewrites via
`erToKN_interp` twice and applies `he`.

### Task 12 — `erToKFunctor_map` via `Quotient.liftOn`

Binding spec section: §8.2.

```lean
def erToKFunctor_map {n m : ℕ}
    (e : ERMorNQuo n m) : KSimMor 2 n m :=
  Quotient.liftOn e
    (fun rec => ⟨Quotient.mk (kMorNSetoid n m) (erToKN rec),
                 /- depth-2 witness via erToKN_level -/⟩)
    (fun e₁ e₂ h => ...)
```

The lift produces a `KSimMor 2 n m` value packaging:

- a `KMorNQuo n m` term (the quotient class of `erToKN rec`),
- a depth-2 witness `KMorNQuo.atDepth 2 _`, discharged by
  the per-component level lemma `erToKN_level`.

Well-definedness uses `erToKN_compat_extEq`. The shape
mirrors `kToERFunctor_map` at `LawvereKSimER.lean:474`.
Expected LOC: 40–80 (the existence of the kToER mirror keeps
the structure compact).

### Task 13 — `erToKFunctor_map_id` and `_map_comp`

Binding spec section: §8.3.

```lean
theorem erToKFunctor_map_id (n : LawvereERCat) :
    erToKFunctor_map
        (CategoryTheory.CategoryStruct.id
          (obj := LawvereERCat) n)
      = CategoryTheory.CategoryStruct.id
          (obj := LawvereKSimDCat 2)
          (n : LawvereKSimDCat 2)

theorem erToKFunctor_map_comp {n m k : ℕ}
    (e : ERMorNQuo n m) (f : ERMorNQuo m k) :
    erToKFunctor_map
        (CategoryTheory.CategoryStruct.comp
          (obj := LawvereERCat) e f)
      = CategoryTheory.CategoryStruct.comp
          (obj := LawvereKSimDCat 2)
          (erToKFunctor_map e) (erToKFunctor_map f)
```

Both proofs are by `Quotient.inductionOn` (or
`inductionOn₂`) over the ER quotient witnesses, reducing
to `Quotient.sound` steps on the K side discharged by
`erToKN_compat_extEq`. `map_id` uses `erToK_interp` on
`ERMor1.proj` to recognise the all-projections identity.
`map_comp` uses `erToK_interp` on both sides of `e ≫ f` to
recognise the composition. Mirror: `kToERFunctor_map_comp`
at `LawvereKSimER.lean:427-468`.

Expected LOC: 100–200 combined.

### Task 14 — `erToKFunctor` assembly

Binding spec section: §8.4.

```lean
def erToKFunctor : CategoryTheory.Functor
    LawvereERCat (LawvereKSimDCat 2) where
  obj n     := n
  map       := erToKFunctor_map
  map_id    := erToKFunctor_map_id
  map_comp  := erToKFunctor_map_comp
```

`obj n := n` by def-unfolding (`LawvereERCat = ℕ`,
`LawvereKSimDCat 2 = ℕ`). Mirror: `kToERFunctor` at
`LawvereKSimER.lean:476`. Expected LOC: 10–20.

### Task 15 — Re-export, axiom audit, lint sweep, tests

Updates `GebLean.lean` (or whichever umbrella module
re-exports curated downstream content) to expose
`erToKFunctor` and the surrounding theorems. Runs:

- `lake build` (full project).
- `lake test`.
- `bash scripts/check-axioms.sh
  GebLean/LawvereERKSim/RuntimeBound.lean
  GebLean/LawvereERKSim/ErToK.lean
  GebLean/LawvereERKSim/ErToKFunctor.lean` and any other
  touched files.
- `markdownlint-cli2 '**/*.md'` (whole-repo sweep).
- Optional: a small `#guard`-based test of `erToK` on a
  representative ER morphism (e.g. `succ`-of-`proj`) at the
  `GebLeanTests/` level, mirroring T2/T3 closing test
  patterns.

Expected axiom envelope across all new files: `[propext,
Quot.sound, Classical.choice]` (Classical.choice via the
existing AXIOM_ALLOW on `boundExprKParams_dominates`; the
downstream theorems inherit it transitively through
`simulate_interp` and `boundExprKParams_dominates`).

Expected LOC: 20–50 (umbrella re-export plus tests).

### Final — Holistic code review

Send a fresh `feature-dev:code-reviewer` (or equivalent)
over the diff between `e8c0028` and the final tip of
`feat/ertok-runtime-bound`. Apply minor fixes inline.
Reviewer's brief: check the cross-module composition (Task
9's `boundExprK` interp ↔ Task 10's `erToK` proof; Task
12–14's quotient lifts ↔ Task 11's compat infrastructure),
the consumption of T2/T3 surface area, and overall LOC
budget (T4 is expected to add ~2.5–3.5 kLOC across
`RuntimeBound.lean` + `ErToK.lean` + `ErToKFunctor.lean`).

## Available infrastructure consumed by Tasks 9–15

| Surface | Location | Used by |
| --- | --- | --- |
| `boundExprKParams`, `boundExprKParams_dominates` | `GebLean/LawvereERKSim/RuntimeBound.lean` | Task 9 |
| `KMor1.maxK`, `KMor1.maxOver`, `KMor1.pow2_iter` and their interp/level lemmas | `GebLean/Utilities/KArith.lean` | Task 9 |
| `KMor1.add`, `KMor1.natK'`, `KMor1.proj`, `KMor1.comp` and their interp/level lemmas | `GebLean/Utilities/KArith.lean`, `GebLean/LawvereKSim.lean` | Tasks 9, 10 |
| `KSimURMSimulator.simulate`, `simulate_interp`, `simulate_level` | `GebLean/Utilities/KSimURMSimulator.lean` (T3) | Task 10 |
| `LawvereERKSim.compileER`, `compileER_runtime`, `compileER_runFor` | `GebLean/LawvereERKSim/Compiler.lean` (T2) | Tasks 9, 10 |
| `Fin.maxOfNat`, `Fin.le_maxOfNat`, `Fin.maxOfNat_le` | `GebLean/LawvereKSim.lean` | Task 9 |
| `tower`, `tower_zero`, `tower_succ`, `tower_comp`, `tower_mono_right`, `tower_mono_left`, `self_le_tower`, `mul_tower_le_tower_add_two`, `tower_pow_le_tower_add_three` | `GebLean/Utilities/Tower.lean` | Task 9 (interp / level chase; no new tower lemmas expected) |
| `ERMorN`, `ERMorNQuo`, `LawvereERCat`, ER quotient setoid | `GebLean/LawvereER.lean`, `GebLean/LawvereERCat.lean` | Tasks 11–14 |
| `KMorN`, `KMorNQuo`, `KSimMor 2`, `LawvereKSimDCat 2`, `kMorNSetoid` | `GebLean/LawvereKSim.lean`, `GebLean/LawvereKSimDCat.lean` | Tasks 11–14 |
| `kToERFunctor_map`, `kToERFunctor_map_id`, `kToERFunctor_map_comp`, `kToERFunctor` | `GebLean/LawvereKSimER.lean:474–500` | Mirror for Tasks 12–14 |

## Axiom envelope expectations

`boundExprKParams_dominates` carries `Classical.choice` via
the `Fin.lastCases_castSucc` AXIOM_ALLOW. Downstream
theorems inherit it transitively:

- `boundExprK_dominates`: chains `boundExprKParams_dominates`
  ⇒ inherits.
- `erToK_interp`: chains `simulate_interp` (T3, also carries
  Classical.choice via `Fin.lastCases_castSucc`) and
  `compileER_runFor` (T2, which transitively inherits via
  T3's surface). The annotation is already in place on T3
  and T2's load-bearing theorems.
- `erToKFunctor_map_comp` and `_map_id`: chain through
  `erToK_interp` ⇒ inherit.

Per spec §11, the annotation must be carried on **the
specific declarations that transitively depend on
`Classical.choice`**, namely the ones whose proofs traverse
`Fin.cons`/`Fin.tail` simp normalisations. Conservatively:
annotate `boundExprK_dominates`, `erToK_interp`,
`erToK_level` if elaboration drags it through `Fin` simp
(check axiom audit; un-annotate if clean), `erToKN_interp`,
`erToKFunctor_map`, `erToKFunctor_map_id`,
`erToKFunctor_map_comp`. Defer the per-declaration
annotation decision to the implementer subagent's axiom
audit step.

## Subagent-driven-development plan

Sequential dispatch, one focused subagent per task. Each
subagent reads this handoff plus the relevant spec section
plus the task's box above. After each subagent reports
DONE:

1. Main agent verifies LSP + axiom envelope independently.
2. Dispatches spec-compliance reviewer subagent.
3. Dispatches code-quality reviewer subagent.
4. Applies reviewer fixes inline (or re-dispatches the
   implementer for substantial reworks).
5. Marks the task complete; commits per-task or per-pair
   per the plan's commit guidance (Tasks 9–14 can each
   commit individually; Task 15 closeout absorbs final
   touch-ups; Final review may produce a small follow-up
   commit).

Tasks 11–14 share `ErToKFunctor.lean` and can be assigned
to subagents in close succession, but they have data
dependencies (Task 12 consumes Task 11's `erToKN`; Tasks
13–14 consume Task 12's `erToKFunctor_map`). Run them
sequentially; do not parallelise.

Subagent prompt boilerplate:

- Working directory `/home/terence/git-workspaces/geb/geb-lean`.
- Branch `feat/ertok-runtime-bound`. Do not commit, push,
  or modify the spec/plan/handoff docs.
- Reuse the recipe/dominates declarations as-is.
- Read the task's spec section (§6, §7, §8.x) verbatim
  before implementing.
- Self-review against axiom hygiene (no new
  `Classical.choice` introductions outside the
  `Fin.lastCases_castSucc` exception).
- Report DONE / DONE_WITH_CONCERNS / BLOCKED /
  NEEDS_CONTEXT with LSP, axiom audit, and LOC summary.

## Operational rules (carry forward)

- **Working directory**: `/home/terence/git-workspaces/geb/geb-lean`.
- **No `jj git push` without user line-by-line review**.
- **No raw mutating `git` subcommands** (use `jj`).
- **Build with `lake build`. Never `lake env lean`. Never
  `lake clean`.**
- **Avoid bash process substitution `<(...)`/`>(...)`** (they
  trigger manual approval prompts).
- **Markdown lint clean**: run `markdownlint-cli2` on any
  `.md` files touched before committing.
- **Subagent dispatch** is mandatory for each implementation
  task per the SDD plan above.
- **Per-task commits** are allowed for Tasks 9–14 (each
  produces a self-contained landed unit). Tasks 11–14 may
  combine if a smaller closure makes sense after Task 11
  lands. Task 15 lands closeout fixups.

## Resumption prompt

Paste this verbatim into the next Claude Code session:

```text
Continue T4 SDD Tasks 9–15 from a clean `feat/ertok-runtime-bound`
tip.

Start by reading:
  docs/superpowers/plans/2026-05-23-step-t4-tasks-9-15-handoff.md

That document is the binding handoff. It contains:
  - The current branch/commit state (clean working copy on top of
    commit 3e1dd99, Tasks 0–8 landed).
  - A per-task breakdown of Tasks 9–15 with spec section
    references and shape sketches.
  - The available infrastructure (T2 Compiler.lean, T3
    KSimURMSimulator.lean, T4-so-far RuntimeBound.lean, the
    `kToERFunctor` mirror at LawvereKSimER.lean:474).
  - Axiom envelope expectations per declaration.
  - The subagent-driven-development plan (one subagent per task,
    sequential).
  - Operational rules.

The branch is `feat/ertok-runtime-bound`. The working copy at
session start should be empty (the tip is `3e1dd99`). Use the
`superpowers:subagent-driven-development` skill. Dispatch one
focused subagent for each task in order:

  Task 9 (boundExprK + level/interp/dominates in RuntimeBound.lean)
  → Task 10 (new ErToK.lean + erToK + level + interp)
  → Task 11 (new ErToKFunctor.lean + erToKN + compat lemmas)
  → Task 12 (erToKFunctor_map via Quotient.liftOn)
  → Task 13 (erToKFunctor_map_id and _map_comp)
  → Task 14 (erToKFunctor assembly)
  → Task 15 (re-export, axiom audit, lint sweep, tests)
  → Final (holistic code review of the e8c0028..tip diff)

Each task's binding spec section is:
  Task 9  ↔ spec §6
  Task 10 ↔ spec §7
  Task 11 ↔ spec §8.1
  Task 12 ↔ spec §8.2
  Task 13 ↔ spec §8.3
  Task 14 ↔ spec §8.4
  Task 15 ↔ spec §9 (file layout), §11 (axioms), §12 (tests)

After all tasks land:
  - `lake build` clean.
  - `lake test` clean.
  - `bash scripts/check-axioms.sh` across touched files; expected
    envelope `[propext, Quot.sound, Classical.choice]`.
  - `markdownlint-cli2 '**/*.md'` clean.
  - Holistic code review pass.
  - Then T4 is complete and ready for the user to schedule a
    push to origin.
```

## References

- T4 spec (5-round adversarial-converged):
  [`docs/superpowers/specs/2026-05-22-step-t4-runtime-bound-design.md`](../specs/2026-05-22-step-t4-runtime-bound-design.md).
- T4 plan (5-round adversarial-converged, status block
  current as of this handoff):
  [`docs/superpowers/plans/2026-05-22-step-t4-runtime-bound-plan.md`](2026-05-22-step-t4-runtime-bound-plan.md).
- Prior Tasks 5–8 handoff (historical):
  [`docs/superpowers/plans/2026-05-23-step-t4-tasks-5-8-handoff.md`](2026-05-23-step-t4-tasks-5-8-handoff.md).
- Master ER-to-K spec (T1+T2+T3+T4 binding):
  [`docs/superpowers/specs/2026-05-16-er-to-k-via-cslib-urm-design.md`](../specs/2026-05-16-er-to-k-via-cslib-urm-design.md).
- `kToERFunctor` mirror at
  [`GebLean/LawvereKSimER.lean:474`](../../GebLean/LawvereKSimER.lean).
- Joint commit landing Tasks 5–8: `3e1dd99` —
  `feat(ertok): prove boundExprKParams_dominates joint
  runtime+value bound`.
