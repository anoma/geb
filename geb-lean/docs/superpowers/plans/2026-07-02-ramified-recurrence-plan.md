# Ramified recurrence (`RMRec-omega`) implementation plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
  - [Known pitfalls (from project memory; binding on executors)](#known-pitfalls-from-project-memory-binding-on-executors)
- [How to work this plan](#how-to-work-this-plan)
- [Decisions fixed by this plan](#decisions-fixed-by-this-plan)
- [File structure](#file-structure)
- [Phase map](#phase-map)
- [Phase 0 — gates](#phase-0--gates)
  - [Task G1: soundness-route investigation (spec open question 1)](#task-g1-soundness-route-investigation-spec-open-question-1)
  - [Task G2: `LawvereGodelT*` audit (conditional on G1 `bridge-exists`)](#task-g2-lawveregodelt-audit-conditional-on-g1-bridge-exists)
  - [Task G3: syntax-layer spikes, approach A versus B (spec s7)](#task-g3-syntax-layer-spikes-approach-a-versus-b-spec-s7)
  - [Task G4: soundness-landing choice (spec open question 2)](#task-g4-soundness-landing-choice-spec-open-question-2)
  - [Task G5 (non-blocking): Otto thesis acquisition (spec open question 6)](#task-g5-non-blocking-otto-thesis-acquisition-spec-open-question-6)
- [Phase 1 — core layers (branch `feat/ramified-p1-core`)](#phase-1--core-layers-branch-featramified-p1-core)
  - [Task 1.1: `AlgSig` and the free algebra](#task-11-algsig-and-the-free-algebra)
  - [Task 1.2: sorted signatures](#task-12-sorted-signatures)
  - [Task 1.3: the term layer with clone laws](#task-13-the-term-layer-with-clone-laws)
  - [Task 1.4: models, standard interpretation, interpretative setoid](#task-14-models-standard-interpretation-interpretative-setoid)
  - [Task 1.5: the generic syntactic category](#task-15-the-generic-syntactic-category)
- [Phase 2 — higher-order system over `1 + X`](#phase-2--higher-order-system-over-1--x)
  - [Task 2.1: r-types and object sorts](#task-21-r-types-and-object-sorts)
  - [Task 2.2: the higher-order presentation and schema identifiers](#task-22-the-higher-order-presentation-and-schema-identifiers)
  - [Task 2.3: `omegaShift` (sort level) and `kappaHat`](#task-23-omegashift-sort-level-and-kappahat)
  - [Task 2.4: the section 2.4 example ladder](#task-24-the-section-24-example-ladder)
- [Phase 3 — algebra genericity (branch `feat/ramified-p3-generic`)](#phase-3--algebra-genericity-branch-featramified-p3-generic)
  - [Task 3.1: canonical instances](#task-31-canonical-instances)
  - [Task 3.2: algebra-map functoriality](#task-32-algebra-map-functoriality)
- [Phase 4 — first-order sub-theories (branch `feat/ramified-p4-firstorder`)](#phase-4--first-order-sub-theories-branch-featramified-p4-firstorder)
  - [Task 4.1: the restricted signature and sub-theories](#task-41-the-restricted-signature-and-sub-theories)
- [Phase 5 — definability (branch `feat/ramified-p5-definability`; sub-plan)](#phase-5--definability-branch-featramified-p5-definability-sub-plan)
  - [Task 5.0: write and converge the Phase 5 sub-plan](#task-50-write-and-converge-the-phase-5-sub-plan)
  - [Task 5.1: Lemma 2 — simultaneous recurrence reduces to plain](#task-51-lemma-2--simultaneous-recurrence-reduces-to-plain)
  - [Task 5.2: Lemma 1 — flat recurrence versus destructors and case](#task-52-lemma-1--flat-recurrence-versus-destructors-and-case)
  - [Task 5.3: clock-format arithmetic](#task-53-clock-format-arithmetic)
  - [Task 5.4: Lemma 6 — elementary-time machines are ramified-definable](#task-54-lemma-6--elementary-time-machines-are-ramified-definable)
  - [Task 5.5: the definability family](#task-55-the-definability-family)
- [Phase 6 — soundness (branch `feat/ramified-p6-soundness`; sub-plan)](#phase-6--soundness-branch-featramified-p6-soundness-sub-plan)
  - [Task 6.0: write and converge the Phase 6 sub-plan](#task-60-write-and-converge-the-phase-6-sub-plan)
- [Phase 7 — assembly (branch `feat/ramified-p7-assembly`)](#phase-7--assembly-branch-featramified-p7-assembly)
  - [Task 7.1: the two statements](#task-71-the-two-statements)
  - [Task 7.2: the K-sim-2 corollary](#task-72-the-k-sim-2-corollary)
  - [Task 7.3: documentation](#task-73-documentation)
- [Self-review checklist (run before adversarial review)](#self-review-checklist-run-before-adversarial-review)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task. Steps
> use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Formalize `RMRec-omega` (Leivant III, sections 2.3-2.7) as a
multi-sorted Lawvere-style syntactic category with interpretative
equality, generic in the signature functor and instantiated at `1 + X`,
`1 + 2 X`, and `1 + X^2`; prove the two statements of the spec's
section 6.1 over `1 + X` against `LawvereERCat` (`collapseFunctor`
well-defined and faithful; `ramified_definability` quantified over
object-sort contexts), with the K^sim_2 corollary via `erKSimEquiv`.

**Architecture:** A master plan in seven implementation phases
following the spec's section 8, preceded by a gate phase (Phase 0)
that resolves the spec's front-loaded open questions before any
representation commitment. Phases 0-4 carry full step detail here.
Phases 5 and 6 have their boundaries, deliverables, and consumed
interfaces fixed here and their step detail supplied by mandatory
sub-plans (adversarially reviewed, then user-reviewed), because
Phase 6's content branches on the Phase 0 gate outcomes and Phase 5's
steps consume Phase 1-4 artifact shapes. This is the repository's
established master-plan/sub-plan pattern.

**Authoritative spec:**
`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`
(converged through 15 adversarial-review rounds; user-approved
2026-07-02). Section references of the form "spec sN" below refer to
it; "paper" references are to Leivant III (APAL 96 (1999) 209-229,
DOI `10.1016/S0168-0072(98)00040-2`).

**Tech Stack:** Lean 4 (`leanprover/lean4:v4.29.0-rc6`; mathlib and
cslib pinned `v4.29.0-rc6`), Lake, mathlib category theory
(`CartesianMonoidalCategory.ofChosenFiniteProducts`), `jj` VCS,
`markdownlint-cli2`, `doctoc`, `theoremsearch` / `arxiv` MCPs (gate
investigations only).

## Global constraints

Every task's requirements implicitly include this section.

- Toolchain `leanprover/lean4:v4.29.0-rc6`; mathlib/cslib
  `v4.29.0-rc6`. Use only API present at this pin.
- Build with `lake build` / `lake test` / `lake lint` only. Never
  `lake clean`. Never `lake env lean` on project files.
- No `noncomputable` anywhere. `Classical.choice` accepted in proofs
  only. Axiom hygiene: `lake build GebLeanAxiomChecks` must pass
  (permitted axioms `propext`, `Quot.sound`, `Classical.choice`).
- `sorry` only while a skill that needs it is active; never committed.
  `admit` never. Placeholders between skills are underscores (`_`).
- Pre-commit Lean triad before every commit touching a `.lean` file:
  `bash scripts/pre-commit.sh` (`lake test`, `lake lint`,
  `lake build GebLeanAxiomChecks`). `bash scripts/pre-push.sh` before
  every push.
- Markdown: every committed `.md` passes
  `markdownlint-cli2 --config .markdownlint-cli2.jsonc --no-globs
  <file>`; documents with more than one `##` heading carry a doctoc
  TOC (`doctoc --update-only <file>`).
- VCS is `jj` (colocated at parent `geb/`). No raw mutating `git`. No
  `jj git push` without user line-by-line review. Commit messages:
  `<type>(<scope>): <subject>`, imperative, lowercase subject, no
  trailing period, subject <= 72 chars, ending with
  `Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>`.
- Generic user references in committed text ("the user" / "they").
- Prose style: formal, precise, dry; no value-laden adjectives, no
  colloquialisms or metaphors (`CLAUDE.md` section Style guidelines).
- Citations at point of use: every transcribed definition or theorem
  carries its literature reference with a searchable identifier
  (DOI / arXiv id) in the Lean docstring (module docstring
  `## References` section or declaration docstring), naming the
  paper's section/lemma/equation. Each new declaration is marked
  transcription or novel packaging per spec s2.5.
- Binding vocabulary (spec s2.1 glossary; use in all Lean docstrings
  and plan/sub-plan prose): **parameters** (the paper's recurrence
  parameters `x_vec`), **recurrence argument** (the whole constructor
  term `c_i (a_vec)`, the last argument of `f`), **subterms** (its
  immediate components `a_vec`), **recursive results** (the paper's
  critical arguments `phi_j`), **step functions** (the paper's
  recurrence functions `g_ci`). `Omega tau` is described as the
  typing license for base-algebra elements to serve as the recurrence
  argument of a recurrence whose recursive results carry type `tau`;
  semantically every object sort denotes a copy of the algebra's
  carrier (paper section 2.7).
- New Lean source lives under `GebLean/Ramified/` in root namespace
  `GebLean`, sub-namespace `GebLean.Ramified`, with the directory
  index file `GebLean/Ramified.lean` (import block + module
  docstring, following `GebLean/LawvereERKSim.lean`). Tests under
  `GebLeanTests/Ramified/` with index `GebLeanTests/Ramified.lean`,
  imported from `GebLeanTests.lean` so `lake test` covers them.
- Mathlib upstream guides (contribute/commit/style/naming/doc pages)
  bind all `.lean` content and commit messages; adversarial reviewers
  re-fetch them each round.

### Known pitfalls (from project memory; binding on executors)

- Do not `#guard` heavy composite interpretations (Godel-pairing or
  deep recurrence trees expand symbolically); test small terms, or
  state `example : ... := rfl` / proven `@[simp]` lemmas instead.
- `simp only [if_pos h]` can leak `sorryAx`; use `rw [if_pos h]`.
- Mathlib's `fin_cases` tactic pulls `Classical.choice` into proof
  terms; for constructive case splits over `Fin n` use the core
  `Fin.cases` eliminator or explicit matches. (`Classical.choice` is
  permitted in proofs, so this matters only where a definition's
  computability is at stake.)
- Computable terminal/product witnesses: prefer
  `CartesianMonoidalCategory.ofChosenFiniteProducts` and
  `IsTerminal.ofUniqueHom`-style constructions; some mathlib
  `isTerminal*` witnesses are `noncomputable`.
- Avoid bash process substitution (`<(...)`); write intermediate
  output to files under `/tmp`.
- Exemption: commits on Task G3's throwaway spike branch are exempt
  from the pre-commit triad (the branch is never pushed or merged
  and is abandoned once the decision note is written). A spike state
  stopped at a demonstrated blocker is checkpointed with the failing
  fragment commented out and the blocker recorded inline, so the
  checkpoint compiles nothing false and remains inspectable.

## How to work this plan

- **Phase order.** Phase 0 gates G1-G4 close before any Phase 1
  commit (G5 is non-blocking); G3 is the gate whose outcome Phase 1
  consumes, and G1/G2/G4 are front-loaded with it so the route
  record is complete before implementation begins. Phases 1-2-3-4
  are sequential except that Phase 3 and Phase 4 both depend only on
  Phase 2 and may be developed in either order or in parallel
  branches. The Phase 5 sub-plan is written after Phases 2 and 3
  land (it consumes the example ladder and `natFreeAlgEquiv`); the
  Phase 6 sub-plan is written after gates G1/G2/G4 have closed,
  Phases 2 and 3 have landed, and the Phase 5 sub-plan has converged
  (Phase 6's `Collapse.lean` consumes `natFreeAlgEquiv` and states
  `collapseDenotation` against the `ObjCtx` bookkeeping the Phase 5
  sub-plan fixes). Phase 7 consumes Phases 5 and 6.
- **Sub-plans.** Phases 5 and 6 each get a sub-plan at
  `docs/superpowers/plans/<date>-ramified-p<N>-<slug>-subplan.md`,
  adversarially reviewed to convergence and then user-reviewed before
  execution (project process: adversarial review precedes user
  review). Sub-plans elaborate step detail strictly inside the
  boundaries and deliverables fixed by this plan; changing a boundary
  requires revisiting this plan first.
- **Branches.** This plan and the Phase 0 decision note are committed
  on `docs/ramified-recurrence-approaches` (the spec's branch; spec,
  plan, and gate record co-evolve there). Each implementation phase
  is one topic branch `feat/ramified-p<N>-<slug>` (one concern per
  branch), created off the tip that contains the approved spec and
  plan — the docs branch while it is unmerged, `main` afterwards —
  and stacked in phase order while awaiting review.
- **Reviews.** Each phase ends with
  superpowers:requesting-code-review before its branch is offered for
  user review; superpowers:verification-before-completion before any
  completion claim.
- **Task tracking.** Executors work task-by-task with fresh context
  per task where subagent-driven; each task's final step is a commit,
  so the branch is always at a compiling, test-passing state.

## Decisions fixed by this plan

The spec delegates these to the plan phase (spec s5.1, s6.2, s6.4,
s7, s8). Adversarial review of this plan reviews these decisions.

1. **Lemma 6 adaptation format (spec s6.2):** transcribe Lemma 6's
   proof shape directly against the zero-test URM step relation
   (`GebLean.URMState.step`), not via the constant-overhead embedding
   of URM programs into Leivant's register machines. Rationale: the
   embedding route would formalize Leivant's machine family (states,
   three command kinds) as a new formal object used only to be erased
   again; the direct route targets the object `compileER` already
   produces. The spec's s1.2 embedding argument is recorded in the
   transcription's docstring as the fidelity justification, and the
   adaptation is of the presentation kind spec s1.2 permits.
2. **Statement target (spec s5.1):** both s6.1 statements are stated
   against `LawvereERCat`. The definability chain starts ER-side
   (`compileER` + `boundExprKParams_dominates`), which requires no
   K^sim hop. The soundness landing follows gate G4, defaulting to
   the K^sim simulator pattern with transfer across `erKSimEquiv`
   (spec s5.1 recommendation).
3. **Host algebra (spec s5.2):** the in-scope proof is hosted over
   `1 + X`. The `1 + 2 X` and `1 + X^2` instantiations receive
   structure and smoke tests only (Phase 3); the tree-algebra
   corollary is future work (spec s9).
4. **Sub-plan gates:** Phases 5 and 6 execute behind sub-plans as
   described above. Phase 6 is the workstream's dominant cost
   (spec s6.3) and its route is gate-dependent; fabricating its step
   detail now would violate the no-speculation discipline the
   spec's gates exist to enforce.
5. **Naming and file structure:** fixed in the next section. The
   spec's sketch names are kept where present (from s4.2:
   `SortedSig`, `Tm`, `standardModel`, `interpSetoid`, `QuotRel`,
   `SynCat`, `RType`, `higherOrder`; from s6.1: `SynCatFO`,
   `collapseFunctor`, `ramified_definability`); the free-algebra
   signature data is named `AlgSig` (the spec's illustrative `Sig`),
   avoiding a parallel meaning for "signature" against `SortedSig`.
6. **Object-sort structure (spec open question 5), default:**
   `Presentation` carries the sort type `S`, the operation signature,
   and the object-sort predicate `IsObj : S -> Prop` as plain data
   (a structure, not a typeclass). The G3 spikes may overturn this;
   the decision note records the outcome.
7. **Sorted-context indexing (spec open question 4):** answered
   empirically by the G3 spikes per realization; the decision note
   records the choice the winning spike made.

## File structure

| File | Contents | Phase |
| --- | --- | --- |
| `GebLean/Ramified/AlgSig.lean` | `AlgSig`, `FreeAlg`, `natAlgSig` | 1 |
| `GebLean/Ramified/SortedSig.lean` | `SortedSig`, `sum`, `constructorSig` | 1 |
| `GebLean/Ramified/Term.lean` | `Tm`, `var`, `op`, `subst`, clone laws, `QuotRel` | 1 |
| `GebLean/Ramified/Interp.lean` | `SortedModel`, `Tm.eval`, `Presentation`, `standardModel`, `interpSetoid`, `interpQuotRel` | 1 |
| `GebLean/Ramified/SynCat.lean` | `SynCat`, `Category`, `CartesianMonoidalCategory` | 1 |
| `GebLean/Ramified/RType.lean` | `RType`, object sorts, tower sorts | 2 |
| `GebLean/Ramified/HigherOrder.lean` | `appSig`, `RIdent`, `higherOrder`, identifier semantics | 2 |
| `GebLean/Ramified/OmegaShift.lean` | `omegaShift` (sort level), `kappaHat` | 2 |
| `GebLean/Ramified/Examples.lean` | s2.4 ladder: coercions, `+`, `x`, `e`, `2_m`, `sz` | 2 |
| `GebLean/Ramified/Algebras.lean` | `binWordAlgSig`, `treeAlgSig`, `natFreeAlgEquiv`, instantiations, algebra-map functoriality | 3 |
| `GebLean/Ramified/FirstOrder.lean` | restricted signature, sub-theories, inclusion, first-order examples | 4 |
| `GebLean/Ramified/Definability/*.lean` | Lemma 2, Lemma 1, bound arithmetic, Lemma 6, definability family | 5 |
| `GebLean/Ramified/Soundness/*.lean` | route per gates; `Collapse.lean`: `SynCatFO`, `collapseDenotation`, `collapseFunctor`, faithfulness | 6 |
| `GebLean/Ramified/Characterization.lean` | s6.1 statement pair (`ramified_definability`), K^sim_2 corollary | 7 |
| `GebLean/Ramified.lean` | directory index (import block + module docstring) | 1, extended each phase |
| `GebLeanTests/Ramified/*.lean` | per-phase test modules | each |
| `docs/superpowers/notes/2026-07-02-ramified-gates-decisions.md` | gate record (G1-G5) and plan-fixed decisions | 0 |
| `docs/areas/ramified-recurrence.md` | area doc | 7 |

Interface code blocks below are binding for names, arities, and
semantic content; implicit-argument placement and universe
annotations may be adjusted at elaboration time. Where a block is
copied from spec s4.2 it is marked as such.

## Phase map

| Phase | Branch | Depends on | Detail |
| --- | --- | --- | --- |
| 0 gates | `docs/ramified-recurrence-approaches` (notes); `spike/ramified-syntax` (throwaway) | — | full, here |
| 1 core layers | `feat/ramified-p1-core` | G1-G4 closed (G3 decisive) | full, here |
| 2 higher-order over `1 + X` | `feat/ramified-p2-rtype` | 1 | full, here |
| 3 algebra genericity | `feat/ramified-p3-generic` | 2 | full, here |
| 4 first-order sub-theories | `feat/ramified-p4-firstorder` | 2 | full, here |
| 5 definability | `feat/ramified-p5-definability` | 2, 3 (branch stacked after 4) | boundaries here; sub-plan |
| 6 soundness | `feat/ramified-p6-soundness` | 2, 3; G1, G2, G4; Phase 5 sub-plan converged (branch stacked after 5) | boundaries here; sub-plan |
| 7 assembly | `feat/ramified-p7-assembly` | 5, 6 | full, here |

---

## Phase 0 — gates

All gate outcomes are recorded in
`docs/superpowers/notes/2026-07-02-ramified-gates-decisions.md`, one
section per gate, committed as each gate closes (markdownlint-clean,
doctoc'd). The note also restates the seven plan-fixed decisions
above so downstream sub-plans cite one document.

### Task G1: soundness-route investigation (spec open question 1)

**Files:**

- Create: `docs/superpowers/notes/2026-07-02-ramified-gates-decisions.md`
  (section "G1: Beckmann-Weiermann bridge")

**Deliverable:** verdict `bridge-exists` / `no-bridge`, with citations.

- [ ] **Step 1: frame the question.** Under the transcription-only
  policy (spec s1.2), reuse of the repository's Beckmann-Weiermann
  `T*` formalization for the soundness direction requires a
  *published* bridge: a translation from `RMRec-omega` (or from
  `1l(A)`-represented functions, paper sections 4.2-4.3) into `T*`
  or an equivalent lambda-free fragment with Lemma-16-style bounds
  (Beckmann-Weiermann, "Characterizing the elementary recursive
  functions by a fragment of Godel's T", Arch. Math. Logic 39 (2000)
  475-491). An unpublished translation, however plausible, fails the
  policy and yields verdict `no-bridge`.

- [ ] **Step 2: search the citation neighborhood.** Using
  `theoremsearch` (`theorem_search`), the `arxiv-mcp-server` tools,
  and web search: (a) papers citing Beckmann-Weiermann 2000; (b)
  papers citing Leivant III that also cite Godel's T fragments; (c)
  surveys of elementary-recursion characterizations (Schwichtenberg;
  Ostrin-Wainer APAL 133 (2005)). Record every candidate with its
  identifier and the specific claim inspected, including negative
  findings (a candidate inspected and found not to bridge is recorded
  as such).

- [ ] **Step 3: write the G1 section of the decision note.** Verdict
  plus, for `bridge-exists`: the source, the exact statement bridged,
  and which of spec s6.3's steps 1-3 it replaces. For `no-bridge`:
  the searched space, and confirmation that spec s6.3 steps 1-3 (the
  Leivant sections 4-5 transcription) stand as the route.

- [ ] **Step 4: lint and commit.**

```bash
NOTE=docs/superpowers/notes/2026-07-02-ramified-gates-decisions.md
doctoc "$NOTE" && markdownlint-cli2 --config .markdownlint-cli2.jsonc --no-globs "$NOTE"
jj commit -m "docs(ramified): record G1 soundness-route investigation

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>"
```

### Task G2: `LawvereGodelT*` audit (conditional on G1 `bridge-exists`)

**Files:**

- Modify: the decision note (section "G2: LawvereGodelT* audit")

**Deliverable:** verdict `reuse` / `no-reuse`, with a clause-by-clause
discrepancy table. If G1 returned `no-bridge`, write a one-line skip
record and close the gate.

- [ ] **Step 1: audit the reduction relation.** Compare
  `GodelTTerm.Reduces` (`GebLean/LawvereGodelTReduces.lean:21`), its
  `Star` (`:95`) and `Equiv` (`:122`) closures, clause by clause
  against Beckmann-Weiermann 2000 Definition 4 (each reduction rule:
  presence, orientation, side conditions). Record a table: source
  clause, Lean constructor, verbatim-match / deviation / missing.

- [ ] **Step 2: audit the measures.** Compare `GodelTTerm.lh` (:22),
  `.d` (:42), `.G` (:61), and `.bracketLevel*` (:95-:131) — all in
  `GebLean/LawvereGodelTLemma16.lean` — and `GodelTType.level`
  (`GebLean/LawvereGodelT.lean:47`) against the source's
  Definitions 7-10, same table format.

- [ ] **Step 3: audit the Lemma 16 realization.** The repository
  realizes Lemma 16 as a family, not one theorem: the
  `majorizes_red*` case lemmas (`redP_zero` :440, `redP_succ` :466,
  `redK` :527, `redDisc_zero` :582, `redDisc_succ` :652,
  `redTreeIter_leaf` :823, `redIter_zero` :1355, `redIter_succ`
  :1413, `redTreeIter_node` :1818) together with `dominates_app`
  (:926) and the closure lemmas (`dominates_refl/trans`,
  `majorizes_imp_dominates`, `majorizes_app_left/right`), all in
  `GebLean/LawvereGodelTLemma16.lean`. Check: (a) every Definition 4
  reduction rule has a majorization case lemma; (b) each case lemma's
  statement matches the source's Lemma 16 inequality for that rule;
  (c) the composition of the family reproduces the source's Lemma 16
  statement shape (a missing assembly theorem is a finding, not
  necessarily a defect — record what assembly the reuse would need).

- [ ] **Step 4: verdict and commit.** `reuse` only if G1 affirmed and
  the discrepancy table has no unresolved deviation; otherwise
  `no-reuse` (spec s6.3: failing either precondition, the Leivant
  route stands). Lint and commit as in G1 Step 4, message
  `docs(ramified): record G2 LawvereGodelT* audit`.

### Task G3: syntax-layer spikes, approach A versus B (spec s7)

**Files:**

- Throwaway branch `spike/ramified-syntax` off the current tip; spike
  files under `GebLean/Ramified/SpikeA.lean`, `SpikeB.lean` (never
  merged; branch abandoned after the note is written)
- Modify: the decision note (section "G3: representation decision")

**Deliverable:** representation decision A (sorted-Era native
inductives) or B (DTC on the in-repository `PolyFix` stack), with
evidence; C (vendored slice/presheaf functors) is recorded as the
convergence target, not a candidate (not startable: no W-types or
coproducts upstream yet, spec s7).

**Spike target (identical for both):** the monadic first-order
sub-theory over `1 + X` — the smallest restricted signature — carried
through the syntactic-category construction: sorted signature with
tower sorts as `Nat`; terms with `subst` and both clone laws;
standard interpretation; `interpSetoid`; `SynCat` with a `Category`
instance and chosen finite products; one schema-generated identifier
(ramified addition, `+ : o, Omega o -> o`, paper s2.4(2)) with its
interpretation evaluated on two inputs via `example : ... := rfl`.
Everything computable (no `noncomputable`). Timebox: each spike stops
at two working days' effort or at a demonstrated blocker, whichever
is first; partial completion is itself evidence.

- [ ] **Step 1: create the spike branch.**

```bash
jj new -m "chore(ramified): spike syntax layer, A versus B (throwaway)" <tip>
jj bookmark create spike/ramified-syntax -r @
```

(`<tip>` is the revision carrying the approved spec and plan, per
the branch rule in "How to work this plan".)

- [ ] **Step 2: spike A (native inductives).** One file,
  `SpikeA.lean`: sorted signature as a plain structure; `Tm` as a
  native indexed inductive over contexts `List Nat`; `subst` by
  structural recursion; clone laws by `induction t <;> simp`-style
  proofs; interpretation into `Nat`-carriers; setoid; category via
  `GebLean/Utilities/Category.lean` `CategoryData`/`CategoryOfData`
  or a direct instance; products by context concatenation
  (`CartesianMonoidalCategory.ofChosenFiniteProducts`); the ramified
  addition identifier and its `rfl` evaluations. Record per-joint
  friction inline as comments.

- [ ] **Step 3: spike B (`PolyFix` DTC).** One file, `SpikeB.lean`:
  the same target with the term type realized through the
  in-repository polynomial stack —
  `PolyFunctorBetweenCat`/`PolyEndo` (`GebLean/Polynomial.lean:956`,
  `GebLean/PolyAlg.lean:55`), signature summands via
  `polyBetweenCoprod` (`GebLean/PolyUMorph.lean:422`) with
  `algCoprodDesc` (`GebLean/PolyAlgUMorph.lean:418`), terms as
  `PolyFix` (`GebLean/PolyAlg.lean:176`) with `polyFixFold` (:359)
  and initiality (`polyFixAlg_isInitial` :533) for the recursion
  principles. Same acceptance content as spike A.

- [ ] **Step 4: score and decide.** Fill the spec s7 comparison for
  the observed evidence: lines of code, wall-clock build time of each
  spike file, clone-law proof effort, custom-recursor friction
  (B: working through `PolyFix.ind`/`polyFixFold` where A uses
  native `induction`), sorted-context indexing choice each spike was
  forced into (spec open question 4), and where each realization
  put the object-sort structure (spec open question 5, plan default:
  data). Decision rule: the spike that reaches the full target with
  less friction wins; if both reach it and the evidence is
  equivocal, choose B (spec s7 default), recording that C remains
  the convergence target and that B's construction-level
  composability is the tiebreak the spec assigns it.

- [ ] **Step 5: write the G3 note section, abandon the spike branch.**
  The note preserves the decisive code fragments (interface shapes,
  the friction points) as fenced blocks, so no downstream artifact
  depends on the abandoned branch. Then:

```bash
jj abandon -r 'docs/ramified-recurrence-approaches..spike/ramified-syntax'
jj bookmark delete spike/ramified-syntax
```

  Lint and commit the note on the docs branch, message
  `docs(ramified): record G3 syntax-representation decision`.

### Task G4: soundness-landing choice (spec open question 2)

**Files:**

- Modify: the decision note (section "G4: landing choice")

**Deliverable:** landing decision for the spec s6.4 normalizer, taken
after G1/G2 close. This is a recorded decision, not code.

- [ ] **Step 1: apply the decision rule.** Inputs: G1/G2 verdicts.
  Rule fixed here:
  - If G2 = `reuse`: the landing shape follows the bridged route's
    own machine-facing needs; record what remains to land (possibly
    nothing beyond the bridge's own bound arithmetic) and which
    pattern it uses.
  - Otherwise (Leivant route): the landing is a normalizer on term
    codes with a verified elementary clock (spec s6.4). Default:
    K^sim landing — implement the normalization step function on
    term codes as a K-morphism, clock it with a K-expressible bound,
    transfer across `erKSimEquiv`; this is the executed-once pattern
    of `erToKFunctor` with `KSimURMSimulator.simulate`
    (`GebLean/Utilities/KSimURMSimulator.lean:544`) as precedent.
    Choose the ER landing (bounded recursion on Godel codes,
    `EraComplete` precedent) instead only if the Phase 6 sub-plan
    analysis shows the step function's natural presentation is
    ER-side arithmetic rather than a state-transition step; record
    the reason either way.

- [ ] **Step 2: write the G4 section, lint, commit** (message
  `docs(ramified): record G4 landing choice`).

### Task G5 (non-blocking): Otto thesis acquisition (spec open question 6)

**Files:**

- Modify: the decision note (section "G5: Otto 1995")

- [ ] **Step 1: attempt acquisition.** J. R. Otto, "Complexity
  doctrines", PhD thesis, McGill University, 1995 (ProQuest /
  McGill eScholarship / interlibrary channels — record what was
  tried). If the user's assistance is needed (paywalled channels),
  ask once and proceed without blocking.

- [ ] **Step 2: record the outcome.** If obtained: check overlap with
  the multi-sorted packaging (spec s2.5's novelty claims) and record
  what, if anything, must be cited as precedent in Phase 1-2
  docstrings. If not obtained: docstrings claim novelty
  conservatively ("no overlapping formalization known to this
  project; Otto 1995 not yet examined"). Lint, commit (message
  `docs(ramified): record G5 Otto acquisition attempt`).

---

## Phase 1 — core layers (branch `feat/ramified-p1-core`)

Deliverables of spec s8 item 1. All definitions in this phase are
novel packaging (spec s2.5); docstrings mark them so and cite
Leivant III section 2.1 for the free-algebra conventions. The
realization idiom (native inductive versus `PolyFix`) follows the G3
decision note; the interfaces below are the representation-
independent contract (spec s4.2) both realizations satisfy.

### Task 1.1: `AlgSig` and the free algebra

**Files:**

- Create: `GebLean/Ramified/AlgSig.lean`, `GebLean/Ramified.lean`
- Create: `GebLeanTests/Ramified/AlgSig.lean`,
  `GebLeanTests/Ramified.lean`
- Modify: `GebLeanTests.lean` (import the new test index)

**Interfaces (produces):**

```lean
/-- A free-algebra signature: constructor labels with arities
(Leivant III section 2.1; the paper's standing convention — an
infinite algebra has a 0-ary and a positive-arity constructor — is
carried as hypotheses on results that need it, not baked in). -/
structure AlgSig where
  B : Type
  ar : B → Nat

/-- The free algebra over `S` (realization per the G3 note: native
inductive, or `PolyFix` of the corresponding `PolyEndo`). -/
-- FreeAlg (S : AlgSig) : Type
-- FreeAlg.mk (b : S.B) (subterms : Fin (S.ar b) → FreeAlg S) : FreeAlg S

/-- Unramified recurrence (Leivant III section 2.1, eq. (1)): one
step function per constructor, seeing the parameters, the subterms
of the recurrence argument, and the recursive results. -/
-- FreeAlg.recurse {P C : Type}
--   (g : (b : S.B) → P → (Fin (S.ar b) → FreeAlg S) →
--        (Fin (S.ar b) → C) → C) : P → FreeAlg S → C

/-- The 1 + X signature (monadic word algebra): one 0-ary and one
unary constructor. Used from Phase 2 onward; the other canonical
instances arrive in Phase 3. -/
def natAlgSig : AlgSig
```

- [ ] **Step 1: write failing tests.** `GebLeanTests/Ramified/AlgSig.lean`:
  with a local two-constructor signature (the `1 + X` shape:
  `⟨Bool, fun b => cond b 1 0⟩`), `#guard`-check that `recurse`
  computes the length function (base 0, step +1) on a three-element
  value built by `mk`. Add the index files and the `GebLeanTests.lean`
  import so `lake test` sees the module; run `lake test` and confirm
  it fails (missing declarations).

- [ ] **Step 2: implement** `AlgSig`, `FreeAlg`, `FreeAlg.recurse`
  per the G3 realization, with docstrings citing Leivant III
  section 2.1 eq. (1) (DOI `10.1016/S0168-0072(98)00040-2`) and using
  the binding vocabulary. `GebLean/Ramified.lean` starts as the
  directory index importing `AlgSig`.

- [ ] **Step 3: verify.** `lake test` passes; the new `#guard`s run.

- [ ] **Step 4: pre-commit triad and commit.**

```bash
bash scripts/pre-commit.sh
jj commit -m "feat(ramified): add free-algebra signatures and recurrence

Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>"
```

### Task 1.2: sorted signatures

**Files:**

- Create: `GebLean/Ramified/SortedSig.lean`
- Create: `GebLeanTests/Ramified/SortedSig.lean` (+ index imports)

**Interfaces (produces; from spec s4.2):**

```lean
/-- A multi-sorted algebraic signature: operations with sorted
arities. -/
structure SortedSig (S : Type) where
  Op : Type
  arity : Op → List S
  result : Op → S

/-- Signature sum: data-types-a-la-carte assembly. -/
def SortedSig.sum (F G : SortedSig S) : SortedSig S

/-- Constructor summand derived from a free-algebra signature
(shapes = operations, positions = arities), one copy per object
sort: for each object sort `s` and constructor `b`, an operation of
arity `List.replicate (A.ar b) s` and result `s`. -/
def constructorSig (A : AlgSig) (IsObj : S → Prop) : SortedSig S
```

- [ ] **Step 1: write failing tests.** Over `S := Nat` with
  `IsObj := fun _ => True`: `constructorSig` of the `1 + X` shape has,
  at sort 0, a 0-ary and a 1-ary operation (`#guard` on `arity`
  lengths and `result`); `sum` of two one-op signatures exposes both
  ops. Run `lake test`, confirm failure.

- [ ] **Step 2: implement** with docstrings (novel packaging; the
  constructor-summand derivation cites spec s4.1's adoption of the
  Danner-Royer data-system layer, arXiv `1201.4567`).

- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): add sorted signatures and constructor summand`).

### Task 1.3: the term layer with clone laws

**Files:**

- Create: `GebLean/Ramified/Term.lean`
- Create: `GebLeanTests/Ramified/Term.lean` (+ index imports)

**Interfaces (produces; from spec s4.2, representation-independent):**

```lean
-- Ctx S := List S
-- (sig : SortedSig S throughout; Σ is not a legal Lean binder)
-- Tm    : SortedSig S → Ctx S → S → Type
-- Tm.var   : (i : Fin Γ.length) → Tm sig Γ (Γ.get i)
-- Tm.op    : (o : sig.Op) →
--            (args : ∀ i, Tm sig Γ ((sig.arity o).get i)) →
--            Tm sig Γ (sig.result o)
-- Tm.subst : Tm sig Γ s → (∀ i, Tm sig Δ (Γ.get i)) → Tm sig Δ s
-- Tm.subst_id    : t.subst Tm.var = t
-- Tm.subst_subst : (t.subst σ).subst τ
--                    = t.subst (fun i => (σ i).subst τ)
-- Tm.weaken : (f : Fin Γ.length → Fin Δ.length)
--             (h : ∀ i, Δ.get (f i) = Γ.get i) →
--             Tm sig Γ s → Tm sig Δ s

/-- A quotient relation for the syntactic category: a per-hom setoid
family on terms together with the congruence laws composition needs
(substitution respects the relation in both positions). The relation
is a parameter of the syntactic-category construction (spec s4.2);
Task 1.4 supplies the interpretative instantiation and spec s9's
deferred workstream a Derivable-style one. -/
structure QuotRel (sig : SortedSig S) where
  rel : (Γ : Ctx S) → (s : S) → Setoid (Tm sig Γ s)
  subst_congr :
    ∀ {Γ Δ s} (t t' : Tm sig Γ s)
      (σ σ' : ∀ i, Tm sig Δ (Γ.get i)),
      (rel Γ s) t t' → (∀ i, (rel Δ _) (σ i) (σ' i)) →
      (rel Δ s) (t.subst σ) (t'.subst σ')
```

- [ ] **Step 1: write failing tests.** Small concrete signature
  (one binary op over `S := Unit`): build `op f [var 0, var 1]`,
  substitute the swap tuple, `#guard` the result's shape via a
  decidable equality or an `example : ... := rfl`; state one
  `example` instance each of `subst_id` and `subst_subst` on the
  concrete term. Run `lake test`, confirm failure.

- [ ] **Step 2: implement** per the G3 realization. The clone laws
  are the content the syntactic category's composition depends on;
  prove them at full generality, not just on examples.
  Docstrings: novel packaging; the clone-law shape cites the
  repository precedent (`Era.Tm.subst_id`/`subst_subst`,
  `GebLean/Era.lean`) as the pattern source.

- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): add sorted term layer with clone laws`).

### Task 1.4: models, standard interpretation, interpretative setoid

**Files:**

- Create: `GebLean/Ramified/Interp.lean`
- Create: `GebLeanTests/Ramified/Interp.lean` (+ index imports)

**Interfaces (produces; from spec s4.2):**

```lean
/-- A model of a sorted signature: carriers per sort, an operation
interpretation per op; environments over contexts. -/
structure SortedModel (sig : SortedSig S) where
  carrier : S → Type
  interpOp : (o : sig.Op) →
    (∀ i, carrier ((sig.arity o).get i)) → carrier (sig.result o)
-- SortedModel.Env : Ctx S → Type   (per-position carriers)
-- Tm.eval : (M : SortedModel sig) → Tm sig Γ s → M.Env Γ →
--           M.carrier s
-- Tm.eval_subst :
--   (t.subst σ).eval M ρ = t.eval M (fun i => (σ i).eval M ρ)

/-- A presentation: sorts, signature, object-sort predicate as data
(plan decision 6), the algebra the object sorts denote, and the
standard model as data (its construction for the higher-order
system is Phase 2's `RIdent.interp`). -/
structure Presentation where
  S : Type
  sig : SortedSig S
  IsObj : S → Prop
  alg : AlgSig
  std : SortedModel sig

/-- The standard model: object sorts denote the algebra's carrier
(every object sort a copy — Leivant III section 2.7), arrow sorts
function spaces (Phase 2 constructs this for the higher-order
system; Phase 1 exposes the designated-model projection). -/
abbrev standardModel (P : Presentation) : SortedModel P.sig := P.std

/-- Extensional equality of eval at the standard model — the
erMorNSetoid pattern (GebLean/LawvereERQuot.lean:23), sorted. -/
def interpSetoid (P : Presentation) (Γ : Ctx P.S) (s : P.S) :
    Setoid (Tm P.sig Γ s)

/-- The interpretative quotient relation: the interpSetoid family
bundled with its substitution-congruence laws (discharged by
eval_subst) — the in-scope instantiation of the relation-parametric
syntactic category (Task 1.5). -/
def interpQuotRel (P : Presentation) : QuotRel P.sig
```

- [ ] **Step 1: write failing tests.** Evaluate the Task 1.3 concrete
  term in a `Nat` model (`#guard` on values); one `example` of
  `eval_subst`; two extensionally equal terms related by
  `interpSetoid` (an `example` via `fun ρ => rfl` or `simp`).

- [ ] **Step 2: implement.** `eval_subst` is the semantic clone law
  that later makes composition respect the setoid; prove it in full
  generality. Docstring for `interpSetoid` cites the `erMorNSetoid`
  pattern and spec s4.2's note that the model dependence is
  structural.

- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): add sorted models and interpretative setoid`).

### Task 1.5: the generic syntactic category

**Files:**

- Create: `GebLean/Ramified/SynCat.lean`
- Create: `GebLeanTests/Ramified/SynCat.lean` (+ index imports)

**Interfaces (produces; from spec s4.2):**

```lean
-- SynCat (P : Presentation) (r : QuotRel P.sig) : Type
--                                        -- := Ctx P.S
-- instance : Category (SynCat P r)       -- Hom = tuples of terms
--                                        --   modulo r; comp = subst
-- instance : CartesianMonoidalCategory (SynCat P r)
--                                        -- context concatenation
-- The quotient relation is a parameter of the construction
-- (spec s4.2 prose); the in-scope instantiation is
-- interpQuotRel P (Task 1.4), and the deferred equational
-- workstream (spec s9) re-instantiates the same construction with
-- a Derivable-style relation.
```

Assembly plan (spec s4.2): hom-setoids first, quotient last —
morphism data is a tuple of terms `∀ i, Tm P.sig Γ ((Δ).get i)` with
the pointwise `r`; the category laws hold up to the relation by
`Tm.subst_subst`/`subst_id` plus `QuotRel`'s congruence laws
(discharged for the in-scope instantiation by `eval_subst`); the
`Category` instance is on the `Quotient`. Use the seeds:
`GebLean/Utilities/SetoidCat.lean` (`SetoidBundle`, `SetoidHom`,
`quotientFunctor` at :137) and `GebLean/Utilities/Category.lean`
(`CategoryData` :199, `CategoryOfData` :222) where they shorten the
assembly; hand-roll where they do not fit (the spec notes the
construction generalizes what `LawvereERQuot.lean` and
`LawvereKSimQuot.lean` hand-roll; retrofit of those files is out of
scope). Products: chosen finite products by list concatenation via
`CartesianMonoidalCategory.ofChosenFiniteProducts` (spec s3.3);
everything computable.

- [ ] **Step 1: write failing tests.** Over the Task 1.2 concrete
  presentation: `example` proofs that `id ≫ f = f`, `f ≫ id = f` on
  a concrete morphism; the product projections compose correctly on
  a two-sort context (value-level `#guard` via a chosen evaluation,
  or `example ... := rfl`).

- [ ] **Step 2: implement** per the assembly plan.

- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): add generic syntactic category with products`).

- [ ] **Step 4: phase review.** Run
  superpowers:requesting-code-review over the branch; resolve
  findings; offer the branch for user review.

---

## Phase 2 — higher-order system over `1 + X`

Branch `feat/ramified-p2-rtype`. Deliverables of spec s8 item 2.
Transcription tasks cite the paper at point of use as annotated.

### Task 2.1: r-types and object sorts

**Files:**

- Create: `GebLean/Ramified/RType.lean`
- Create: `GebLeanTests/Ramified/RType.lean` (+ index imports)

**Interfaces (produces):**

```lean
/-- Ramified types (Leivant III section 2.3): from the base type `o`
by the binary arrow and the unary `Omega`. Transcription. -/
inductive RType : Type
  | o : RType
  | arrow : RType → RType → RType
  | omega : RType → RType

/-- Object sorts: `o` and every `Omega tau` (paper section 2.3). -/
def RType.IsObj : RType → Prop
/-- Tower sorts `Omega^m o` (paper section 2.4(3)). -/
def RType.tower : Nat → RType
-- with: (RType.tower m).IsObj; DecidableEq RType;
-- DecidablePred RType.IsObj;
-- RType.interp (carrier : Type) : RType → Type
--   (object sorts ↦ carrier, arrows ↦ function spaces;
--    paper section 2.7: every object sort denotes a copy of the
--    carrier — Omega adds typing license only)
```

- [ ] **Step 1: failing tests** (`#guard` on `IsObj` decisions
  (via `decide`) for `o`, `Ω o`, `Ω (o → o)`, `o → o`;
  `RType.tower 2 = Ω (Ω o)` by `rfl`;
  `RType.interp Nat (Ω (o → o)) = Nat` by `rfl`).

- [ ] **Step 2: implement** with the glossary's `Omega`-license
  wording in the docstrings (verbatim discipline: `Omega tau` is the
  sort of base-algebra elements licensed to serve as the recurrence
  argument of a recurrence whose recursive results carry `tau`).

- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): add r-types and object sorts`).

### Task 2.2: the higher-order presentation and schema identifiers

**Files:**

- Create: `GebLean/Ramified/HigherOrder.lean`
- Create: `GebLeanTests/Ramified/HigherOrder.lean` (+ index imports)

**Interfaces (produces; spec s4.2's `appSig`/`RIdent` sketches):**

```lean
/-- Application at arrow sorts (higher-order system only). -/
def appSig : SortedSig RType   -- one op per (σ, τ):
                               -- arity [σ → τ, σ], result τ

/-- Schema-generated identifiers over a base signature: explicit
definitions and ramified monotonic recurrences (eq. (4)) and flat
recurrences (eq. (5)) over previously defined identifiers; the
signature and its defining semantics are generated together, as
`ERMor1` does for its theory (GebLean/LawvereER.lean:36). -/
inductive RIdent (A : AlgSig) : List RType → RType → Type
-- constructors (transcription targets):
--   defn  : a term over already-formed identifiers, abstracted
--   mrec  : eq. (4) — parameters Γ (arbitrary r-types), recurrence
--           argument at Ω τ, output τ; one step function per
--           constructor of A, seeing parameters and recursive
--           results (monotonic: not the subterms)
--   frec  : eq. (5) — flat recurrence: recurrence argument at o,
--           no recursive results (yields case analysis/destructors)

/-- The higher-order presentation over `A`: constructor summand at
every object sort + application + schema identifiers. -/
def higherOrder (A : AlgSig) : Presentation
-- with RIdent.interp : structural recursion into the standard
-- carriers (as ERMor1.interp, GebLean/LawvereER.lean:82), and
-- standardModel (higherOrder A) via RType.interp (FreeAlg A)
```

Semantics of `mrec` (transcription of eq. (4), displayed in the
docstring with the glossary vocabulary):
`f (x_vec, c_i (a_vec)) = g_ci (x_vec, phi_vec)` where
`phi_j = f (x_vec, a_j)` are the recursive results; the recurrence
argument sits at `Ω τ`, the recursive results and output at `τ`.

- [ ] **Step 1: failing tests.** Build the doubling function over
  `1 + X` as an `mrec` identifier (base `0`, step
  `succ ∘ succ` of the recursive result) and `#guard` its
  interpretation at 0, 1, 3 (small inputs only; pitfalls section).
  Build one `frec` case split (predecessor) and `#guard` it.

- [ ] **Step 2: implement.** Note the eq. (4) typing constraint is
  enforced by the `mrec` constructor's indices (recurrence argument
  `Ω τ` against output `τ`) — the strictly-above illustration of the
  spec's orientation is derived later via coercions, not primitive.
  Citations: eq. (4)/(5), paper section 2.3; the monotonic fragment
  note (the step functions do not see the subterms), paper
  section 2.1.

- [ ] **Step 3: the syntactic category of the system.**
  `abbrev RMRecCat (A : AlgSig) :=`
  `SynCat (higherOrder A) (interpQuotRel (higherOrder A))` with the
  Phase 1 instances applying; smoke `example`s of composition.

- [ ] **Step 4: verify, pre-commit triad, commit** (message
  `feat(ramified): add higher-order presentation with schema identifiers`).

### Task 2.3: `omegaShift` (sort level) and `kappaHat`

**Files:**

- Create: `GebLean/Ramified/OmegaShift.lean`
- Create: `GebLeanTests/Ramified/OmegaShift.lean` (+ index imports)

**Interfaces (produces; spec s4.2 ramified-structure paragraph):**

```lean
/-- The Omega shift on sorts: base substitution τ[o := Ω o]
(spec s4.2; NOT postcomposition with Ω, which fails at arrow
sorts). Sort-level only; no endofunctor claim (spec open
question 3). -/
def RType.omegaShift : RType → RType

/-- kappaHat τ : [Ω τ] ⟶ [τ] — the auxiliary coercion of paper
section 2.4(1), extensionally the identity on the carrier;
morphism of RMRecCat at the singleton contexts. -/
def kappaHat (A : AlgSig) (τ : RType) :
    ([RType.omega τ] : RMRecCat A) ⟶ [τ]
-- kappaHat_interp : interpretation is the identity
```

- [ ] **Step 1: failing tests.** `omegaShift` on `o`, `o → o`,
  `Ω o → o` by `rfl`; `kappaHat` interpretation identity on two
  values (`example ... := rfl` on small inputs).

- [ ] **Step 2: implement.** `kappaHat` is defined by ramified
  recurrence (transcription, paper section 2.4(1)); its docstring
  records that no raising coercion exists (constant maps
  `o → Ω o` exist, an identity-realizing one does not — spec s4.2)
  and that endofunctor/copoint assembly is spec open question 3,
  deliberately not claimed here.

- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): add sort-level omega shift and kappaHat`).

### Task 2.4: the section 2.4 example ladder

**Files:**

- Create: `GebLean/Ramified/Examples.lean`
- Create: `GebLeanTests/Ramified/Examples.lean` (+ index imports)

**Interfaces (produces; each a transcription with its paper cite):**

```lean
-- Over natAlgSig (Phase 1, GebLean/Ramified/AlgSig.lean):
-- coercions kappa τ θ, delta θ (paper s2.4(1)), as morphisms with
--   identity interpretation lemmas;
-- ramAdd : + : o, Ω o → o           (s2.4(2))
-- ramMul : x : (Ω o)² → o           (s2.4(2))
-- ramExp : e : Ω(o → o) → (o → o)   (s2.4(3), second-order
--   recurrence — the recurrence argument at Ω(o → o) drives
--   recurrence whose recursive results carry o → o)
-- ramTwoPow (m : Nat) : 2_m at each object type (s2.4(4), induction
--   on m composing second-order recurrences)
-- ramSize : sz (s2.4(6); over 1 + X extensionally the identity)
-- Each with an interpretation lemma:
--   ramAdd_interp : ... = x + y
--   ramMul_interp : ... = x * y
--   ramExp_interp : iteration
--   ramTwoPow_interp : ... = tower m ... -- align with
--     GebLean.tower (GebLean/Utilities/Tower.lean:17): 2_0(x) = x,
--     2_{m+1}(x) = 2^{2_m(x)}; state the exact correspondence as
--     the lemma (this alignment is a Phase 5 ingredient)
--   ramSize_interp : ... = id
```

- [ ] **Step 1: failing tests.** `#guard`/`example ... := rfl` value
  checks on small inputs for each ladder entry (addition at 2+3,
  multiplication at 2\*3, `ramTwoPow 2` at 1, size at 3); the
  interpretation lemmas stated over all inputs are the real
  deliverable and land in `Examples.lean` itself.

- [ ] **Step 2: implement the ladder bottom-up** (coercions, then
  `+`, `x` which use them, then `e`, then `2_m` composing `e`-style
  second-order recurrences, then `sz`). These are both validation
  and Lemma 6 ingredients (spec s8 item 2); the interpretation
  lemmas must be stated in the exact form Phase 5 consumes
  (`tower` on the `2_m` ladder).

- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): transcribe the section 2.4 example ladder`).

- [ ] **Step 4: phase review** (as Phase 1 Step 4).

---

## Phase 3 — algebra genericity (branch `feat/ramified-p3-generic`)

Deliverables of spec s8 item 3. Phases 3 and 4 both depend only on
Phase 2 and may proceed in parallel branches.

### Task 3.1: canonical instances

**Files:**

- Create: `GebLean/Ramified/Algebras.lean`
- Create: `GebLeanTests/Ramified/Algebras.lean` (+ index imports)

**Interfaces (produces):**

```lean
-- natAlgSig is Phase 1's; this task adds:
def binWordAlgSig : AlgSig   -- 1 + 2X  (polyadic word algebra)
def treeAlgSig    : AlgSig   -- 1 + X²  (tree algebra)
-- higherOrder at each; FreeAlg natAlgSig ≃ Nat
--   (natFreeAlgEquiv : FreeAlg natAlgSig ≃ ℕ — the numeric glue the
--    Phase 5/7 statements against LawvereERCat compose with)
-- smoke content per instance: constructors at object sorts; one
-- flat-recurrence case analysis; one mrec (e.g. binary-word
-- concatenation-length over 1 + 2X; tree size over 1 + X²)
```

- [ ] **Step 1: failing tests** (`#guard`s per instance on the smoke
  identifiers at small values; `natFreeAlgEquiv` round-trips 0, 3).

- [ ] **Step 2: implement.** `natFreeAlgEquiv` must be computable
  (an `Equiv` by structural recursion both ways). Instance docstrings
  cite the word/tree algebra definitions and the monadic/polyadic
  subdivision (paper section 2.1; spec s4.1 table).

- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): instantiate the three canonical algebras`).

### Task 3.2: algebra-map functoriality

**Files:**

- Modify: `GebLean/Ramified/Algebras.lean`
- Modify: `GebLeanTests/Ramified/Algebras.lean`

**Interfaces (produces; spec s4.3):**

```lean
/-- A morphism of free-algebra signatures: label map preserving
arities. -/
structure AlgSigHom (A B : AlgSig) where
  onB : A.B → B.B
  ar_eq : ∀ b, B.ar (onB b) = A.ar b

/-- An algebra-signature morphism induces a functor of higher-order
syntactic categories (spec s4.3; e.g. 1 + X into 1 + 2X). -/
def algMapFunctor (h : AlgSigHom A B) :
    RMRecCat A ⥤ RMRecCat B
```

- [ ] **Step 1: failing tests.** The `1 + X → 1 + 2X` instance
  (zero to empty word, successor to one chosen letter): `#guard`
  that a transported doubling identifier interprets correctly on a
  small input via the induced map.

- [ ] **Step 2: implement** (map on sorts is the identity on
  `RType`; on terms, constructor ops map along `onB`; recurrences
  map clause-wise; functor laws are extensional over the setoid).

- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): add algebra-map functoriality`); phase review.

---

## Phase 4 — first-order sub-theories (branch `feat/ramified-p4-firstorder`)

Deliverables of spec s8 item 4. The first-order systems are
restricted sub-theories of the r-type instantiation — restriction on
the signature (identifier formation), not on the objects
(spec s4.1: the tower-context full subcategory is neither the
first-order system nor the collapse).

### Task 4.1: the restricted signature and sub-theories

**Files:**

- Create: `GebLean/Ramified/FirstOrder.lean`
- Create: `GebLeanTests/Ramified/FirstOrder.lean` (+ index imports)

**Interfaces (produces):**

```lean
/-- First-order identifier formation over `A`: identifiers whose
arities and results are tower sorts `Ω^m o`, with recurrence at
tower object sorts only ("recurrence restricted to object types of
the form Omega^m o", paper section 2.4(3), p. 216). Realized as a
predicate on RIdent (the sub-theory keeps the host's term and
category layers). -/
def RIdent.FirstOrder : RIdent A Γ τ → Prop
/-- The monadic first-order sub-theory over 1 + X (the G3 spike's
target, now the committed artifact) and its polyadic sibling. -/
def firstOrderPresentation (A : AlgSig) : Presentation
def foInclusion (A : AlgSig) :
    SynCat (firstOrderPresentation A)
      (interpQuotRel (firstOrderPresentation A)) ⥤ RMRecCat A
```

- [ ] **Step 1: failing tests.** Ramified `+` and `x` at first order
  (the s2.4(2) examples live at tower sorts: `+ : o, Ω o → o`,
  `x : (Ω o)² → o` are already first-order; re-state them inside the
  sub-theory) — `#guard` interpretations at small values through
  `foInclusion`.

- [ ] **Step 2: implement.** Docstrings use the DLMZ tier-vector
  notation (`i < j` tiers) for prose exposition of the sub-theories
  (spec s2.3 adoption: notation only; DOI `10.4204/EPTCS.23.4`), and
  record that the standalone tier-sorted `S = ℕ` instantiation is
  deferred (spec s9).

- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): add first-order sub-theories and inclusion`);
  phase review.

---

## Phase 5 — definability (branch `feat/ramified-p5-definability`; sub-plan)

Spec s6.2 and s8 item 5, all transcription. Boundaries and consumed
interfaces are fixed here; step detail goes to the sub-plan.

### Task 5.0: write and converge the Phase 5 sub-plan

**Files:**

- Create:
  `docs/superpowers/plans/<date>-ramified-p5-definability-subplan.md`

- [ ] **Step 1: write the sub-plan** after Phases 2 and 3 land (its
  branch stacks after Phase 4 in the review queue, but its content
  depends on Phases 2 and 3 only — the example ladder and
  `natFreeAlgEquiv`), elaborating Tasks 5.1-5.5 below into stepwise
  detail with the then-current artifact signatures. The sub-plan
  must preserve the task boundaries, deliverable statements, and the
  Lemma 6 adaptation decision (plan decision 1) unchanged.

- [ ] **Step 2: adversarial review to convergence** (markdownlint-
  clean reviewer output), then user review, then execution.

**Consumed interfaces (verbatim from the repository, current pin):**

```lean
-- GebLean/LawvereERKSim/Compiler.lean:1590
def compileER {a : ℕ} (e : ERMor1 a) : URMProgram a

-- GebLean/LawvereERKSim/Top.lean:55 — pre-stop correctness: ∃ T0 ≤
-- compileER_runtime e v with pc at the stop instruction, output
-- register = e.interp v, and no earlier stop
theorem compileER_pre_stop_correct {a : ℕ} (e : ERMor1 a)
    (v : Fin a → ℕ) : ...

-- GebLean/LawvereERKSim/Top.lean:89
theorem compileER_runFor {a : ℕ} (e : ERMor1 a) (v : Fin a → ℕ)
    (t' : ℕ) (ht' : compileER_runtime e v ≤ t') :
    (URMState.runFor (compileER e)
        (URMState.init (compileER e) v) t').regs
      (compileER e).outputReg = e.interp v

-- GebLean/LawvereERKSim/RuntimeBound.lean:225 — the joint
-- runtime/value tower bound
theorem boundExprKParams_dominates {a : ℕ} (e : ERMor1 a) :
    ∀ (v : Fin a → ℕ),
      LawvereERKSim.compileER_runtime e v ≤
        tower (boundExprKParams e).1
          (Fin.maxOfNat _ v + (boundExprKParams e).2) ∧
      e.interp v ≤
        tower (boundExprKParams e).1
          (Fin.maxOfNat _ v + (boundExprKParams e).2)

-- GebLean/Utilities/Tower.lean:17
def tower : ℕ → ℕ → ℕ    -- tower 0 x = x; tower (k+1) x = 2 ^ tower k x

-- GebLean/Utilities/ZeroTestURM.lean:89,122,143,155,179,254
-- URMInstr (assign/inc/dec/jumpZ/stop), URMProgram (numRegs, instrs,
-- outputReg, inputRegs + injectivity/disjointness), URMState (pc,
-- regs), URMState.step, URMState.runFor, URMState.init
```

### Task 5.1: Lemma 2 — simultaneous recurrence reduces to plain

**Files:** `GebLean/Ramified/Definability/Simultaneous.lean` (+ test)

**Deliverable:** the ramified simultaneous-recurrence schema
(paper section 2.6, eqs. (6)-(7)) as a derived construction over
`higherOrder natAlgSig` — a family of identifiers with the
simultaneous defining equations — with an interpretation lemma
matching the classical simultaneous system (the shape of
`KMor1.simrecVec`, `GebLean/LawvereKSimInterp.lean:66`, restated over
the ramified sorts). Transcription of Lemma 2; cite section 2.6.

### Task 5.2: Lemma 1 — flat recurrence versus destructors and case

**Files:** `GebLean/Ramified/Definability/Flat.lean` (+ test)

**Deliverable:** `dstrCaseSig` produced as a `SortedSig` summand per
the spec s4.2 sketch (`dstrCaseSig (A : AlgSig) (IsObj : S → Prop) :
SortedSig S`), forming the destructor/case presentation variant; and
the two-way definability reduction of paper section 2.5, Lemma 1,
as interpretation-preserving translations between the two variants
(spec s4.3 lists Lemma 1 as a reduction between presentation
variants): one direction realizes the `dstrCaseSig` operations as
derived identifiers by flat recurrence inside the flat-recurrence
presentation; the other realizes each flat recurrence over the
destructor/case operations. This is the `RMRec-omega_o` to
`RMRec-omega` leg the definability chain ends with (spec s6.2
step 3).

### Task 5.3: clock-format arithmetic

**Files:** `GebLean/Ramified/Definability/Bounds.lean` (+ test)

**Deliverable:** the bound conversion of spec s6.2 step 2's clock:
from `tower mu (Fin.maxOfNat _ v + offset)`
(`boundExprKParams_dominates`) to Leivant's `c * 2_q (sz input)`
format — pure `ℕ` inequalities relating `tower` to the `2_m` ladder
(via `ramTwoPow_interp` from Phase 2) and `sz`, monotonicity, and
the componentwise max-over-inputs handling the arity remark needs.
Arithmetic over formalized bounds, not new mathematics (spec s6.2).

### Task 5.4: Lemma 6 — elementary-time machines are ramified-definable

**Files:** `GebLean/Ramified/Definability/Machine.lean` (+ test)

**Deliverable:** the Lemma 6 transcription (paper section 3.2)
against the zero-test URM step relation (plan decision 1): machine
state tracked by functions `stt` and `phi` defined by ramified
simultaneous recurrence (Task 5.1) over `URMState.step`, clocked by
the ramified `2_q` composed with `sz` (Task 5.3, Phase 2 ladder);
the realizer takes its input at the object sort `Ω(η → η)` per
eq. (8) (p. 221). Statement shape: for a `URMProgram a` computing a
function within time `c * 2_q(sz)`, an object-sort context `Γ` and a
morphism of `RMRecCat natAlgSig` whose interpretation matches the
program's input/output convention (`URMState.init`, output register
read-off). The n-input, m-output case is assembled componentwise
with the clock bound taken over all inputs (spec s6.2 arity remark).
Docstring records the s1.2 embedding argument as fidelity
justification for the URM adaptation.

### Task 5.5: the definability family

**Files:** `GebLean/Ramified/Definability/Top.lean` (+ test)

**Deliverable:** for every ER morphism, an object-sort context and a
ramified realizer with matching denotation — chaining
`compileER_pre_stop_correct` / `compileER_runFor` +
`boundExprKParams_dominates` (step 1) into Task 5.4 (step 2) into
Task 5.2 (step 3):

```lean
/-- Object-sort contexts of length n (spec s6.1): sort lists whose
every entry satisfies RType.IsObj — arbitrary object sorts, beyond
the tower sorts (Lemma 6's realizer takes input at Ω(η → η)). -/
def ObjCtx (n : ℕ) : Type
def oCtx (m : ℕ) : ObjCtx m     -- m copies of o

theorem erMor_ramified_definable {a : ℕ} (e : ERMor1 a) :
    ∃ (Γ : ObjCtx a) (g : Γ ⟶ ([RType.o] : RMRecCat natAlgSig)),
      ramifiedDenotation g = fun v => e.interp v
-- ramifiedDenotation: standard-model interpretation read through
-- natFreeAlgEquiv (Phase 3). Phase 7 re-states this family as
-- ramified_definability against collapseDenotation; the sub-plan
-- fixes the exact multi-output form (m outputs componentwise) and
-- the coercion from ObjCtx into the category's objects.
```

---

## Phase 6 — soundness (branch `feat/ramified-p6-soundness`; sub-plan)

Spec s6.3 and s8 item 6 — the workstream's dominant cost. Content
branches on gates G1/G2/G4; boundaries fixed here, step detail in
the sub-plan.

### Task 6.0: write and converge the Phase 6 sub-plan

**Files:**

- Create:
  `docs/superpowers/plans/<date>-ramified-p6-soundness-subplan.md`

- [ ] **Step 1: write the sub-plan** after gates G1/G2/G4 have
  closed, Phases 2 and 3 have landed, and the Phase 5 sub-plan has
  converged (the dependency rationale is in "How to work this
  plan"), selecting route T or route L below per the gate record,
  elaborating its boundary items into stepwise detail.
  The route-selection rule and the boundary items are binding; the
  sub-plan may split items further but not merge or drop them.

- [ ] **Step 2: adversarial review to convergence, user review,
  then execution.**

**Route T (G2 = `reuse`):**

- T1: transcribe the published bridge (G1's source) from
  `RMRec-omega` (or `1l(A)`-represented functions) into `T*`,
  against `GodelTTerm` (`GebLean/LawvereGodelTTerm.lean:26`).
- T2: consume the audited Lemma-16 family
  (`GebLean/LawvereGodelTLemma16.lean`) for the elementary bound,
  adding whatever assembly theorem the G2 audit recorded as missing.
- T3: the landing per G4; `collapseFunctor` substance (below).

**Route L (otherwise; spec s6.3 steps 1-3, all transcription):**

- L1: the applicative calculi `RlMR-omega` and `RlMR-omega_o` as
  proof-internal apparatus (paper section 4.1): intrinsically-typed
  de Bruijn terms with beta/eta plus recurrence and flat reductions;
  templates: the PLFA Lean port (`rami3l/plfl`, DeBruijn and
  Substitution chapters) and the modular metatheory framework of
  arXiv `2512.09280` (availability to be verified by the sub-plan;
  spec s3.3).
- L2: Proposition 7 composite (1) to (3) via the eq. (9) translation
  (p. 223; recurrence with parameters becomes closed `R-tau`
  operators), then (3) to (4) reconstructing the "similar to
  Lemma 1" argument at the applicative level (spec s6.3 step 1).
- L3: `1l(A)` (simply typed lambda calculus with `dstr`/`case`) and
  the Berarducci-Boehm representation: Lemmas 8-10, Proposition 11,
  with the term translation `E` to `E-bar` (paper sections 4.2-4.3).
- L4: Lemma 12 (terms of height `h`, redex rank `q` normalize in
  time `O((2_{q+1}(h))^2)`) and Proposition 13 (represented
  functions elementary-time computable; uses Lemma 4 to reduce to
  target type `o`) — paper section 5.
- L5: the landing normalizer per G4 (spec s6.4): a normalizer on
  term codes with a verified elementary clock, realized K^sim-side
  (default; `KSimURMSimulator` pattern,
  `GebLean/Utilities/KSimURMSimulator.lean:544,:948,:961`, transfer
  across `erKSimEquiv`, `GebLean/LawvereERKSim/Equivalence.lean:183`)
  or ER-side (bounded recursion on Godel codes; `EraComplete` and
  `GebLean/Utilities/Tupling.lean` precedents), per the G4 record.

**Final boundary item, both routes (T3 / after L5):** the collapse
packaging in `GebLean/Ramified/Soundness/Collapse.lean`
(`collapseFunctor` is a Phase 6 deliverable per spec s8 item 6;
Phase 7 consumes it):

```lean
/-- SynCatFO: the full subcategory of the higher-order syntactic
category on contexts of object sorts — o and Omega tau for arbitrary
r-types tau (spec s6.1; paper section 2.7: every object sort's
universe is a copy of the carrier, so morphisms denote functions on
the carrier — numeric, through natFreeAlgEquiv, at the natAlgSig
instantiation). Realized via mathlib
ObjectProperty.FullSubcategory or the repository's established
idiom. -/
def SynCatFO (P : Presentation) (r : QuotRel P.sig) : Type

-- collapseDenotation: the standard-model interpretation of a
-- morphism between object-sort contexts, read through
-- natFreeAlgEquiv into (Fin n → ℕ) → (Fin m → ℕ). The exact
-- argument bookkeeping (the ObjCtx coercion of Task 5.5) is fixed
-- by the Phase 5 sub-plan; this phase's sub-plan states the
-- signature against it.

/-- Soundness packaged as a functor. With interpretative hom-sets it
is well-defined and faithful by construction; the substance — every
denotation is ER-definable — is this phase's route T or L. -/
def collapseFunctor :
    SynCatFO (higherOrder natAlgSig) (interpQuotRel _) ⥤ LawvereERCat

instance : collapseFunctor.Faithful
```

The substance making `collapseFunctor` total: for every tuple of
terms between object-sort contexts of `RMRecCat natAlgSig`, an
`ERMorN` whose interpretation equals the tuple's collapse
denotation. Well-definedness and faithfulness are then by
construction with interpretative hom-sets on both sides (spec s6.1):
equality is interpretation equality in `interpSetoid` and
`erMorNSetoid` (`GebLean/LawvereERQuot.lean:23`) alike.

---

## Phase 7 — assembly (branch `feat/ramified-p7-assembly`)

Spec s6.1 and s8 item 7.

### Task 7.1: the two statements

**Files:**

- Create: `GebLean/Ramified/Characterization.lean`
- Create: `GebLeanTests/Ramified/Characterization.lean` (+ index
  imports)

**Interfaces:**

- Consumes (Phase 6, `Soundness/Collapse.lean`): `SynCatFO`,
  `collapseDenotation`, `collapseFunctor`,
  `instance : collapseFunctor.Faithful`. Consumes (Phase 5,
  `Definability/Top.lean`): `ObjCtx`, `oCtx`,
  `erMor_ramified_definable`.
- Produces (spec s6.1 verbatim modulo the name mapping
  `higherOrder natSig` -> `higherOrder natAlgSig` and the `ObjCtx`
  arity bookkeeping the Phase 5 sub-plan fixed):

```lean
/-- Definability, quantified over object-sort input contexts
(spec s6.1: the quantification must range beyond tower sorts, and it
is an existential, not fullness — sort-uniform hom-sets are strictly
smaller than elementary). -/
theorem ramified_definability {n m}
    (f : (n : LawvereERCat) ⟶ m) :
    ∃ (Γ : ObjCtx n) (g : Γ ⟶ oCtx m),
      collapseDenotation g = f
```

- [ ] **Step 1: failing tests.** `collapseFunctor` on the Phase 2
  doubling morphism yields an ER morphism whose interpretation
  equals doubling — stated as an `example` proved from the
  interpretation lemmas, not `#guard` (the image is a clocked
  route-T/L composite; kernel reduction on it is the pitfalls
  section's first item); faithfulness `example` on a pair of
  distinct-denotation morphisms exercising the Phase 6 instance.

- [ ] **Step 2: implement** `ramified_definability` from the Phase 5
  family (`erMor_ramified_definable`, multi-output assembled
  componentwise per the Phase 5 sub-plan) and the Phase 6 collapse
  artifacts. The module docstring states the pair — `collapseFunctor`
  well-defined and faithful; `ramified_definability` — as the
  denotational form of Theorem 14 items (1)-(2) relative to
  `LawvereERCat` (paper section 6.1; spec s6.1); the categorical
  packaging is spec open question 7 and is **not** asserted (no
  equivalence-of-categories claim).

- [ ] **Step 3: verify, pre-commit triad, commit** (message
  `feat(ramified): assemble the elementary characterization`).

### Task 7.2: the K-sim-2 corollary

**Files:**

- Modify: `GebLean/Ramified/Characterization.lean` (+ tests)

- [ ] **Step 1: state and prove** the transfer of both statements
  across `erKSimEquiv : LawvereERCat ≌ LawvereKSimDCat 2`
  (`GebLean/LawvereERKSim/Equivalence.lean:183`; strict round-trip
  equalities at `:96`, `:126` shorten the transport): the collapse
  functor composed with `erToKFunctor`, and definability for every
  `(n : LawvereKSimDCat 2) ⟶ m` via `kToERFunctor`. Transfer at the
  level of the two statements (spec s6.1).

- [ ] **Step 2: verify, pre-commit triad, commit** (message
  `feat(ramified): transfer the characterization to K^sim_2`).

### Task 7.3: documentation

**Files:**

- Create: `docs/areas/ramified-recurrence.md`
- Modify: `docs/index.md` (workstream entry)

- [ ] **Step 1: write the area doc** (what exists, module map,
  statement inventory, deferred items pointing at spec s9-s10) and
  the `docs/index.md` entry; doctoc + markdownlint both.

- [ ] **Step 2: reconcile.** If any executed decision diverged from
  the spec (route T versus L, landing, representation), add the
  supersession pointers to the spec sections affected (spec and plan
  co-evolve on-branch). Commit (message
  `docs(ramified): add area doc and index entry`); phase review;
  full pre-push before any push.

---

## Self-review checklist (run before adversarial review)

- Every spec s8 item maps to a phase; every spec s6.1/s6.2/s6.3/s6.4
  obligation maps to a task; the three front-loaded gates cover spec
  open questions 1, 2, and the s7 spikes; open questions 4-6 have
  assigned owners (G3/G3/G5); open questions 3 and 7 are explicitly
  not asserted anywhere.
- No placeholder text (TBD/TODO/"add appropriate..."); every code
  step shows content or names the sub-plan that will.
- Names used across phases agree (`AlgSig`, `QuotRel`,
  `interpQuotRel`, `higherOrder`, `RMRecCat`, `natAlgSig`,
  `natFreeAlgEquiv`, `kappaHat`, `ramTwoPow`, `ObjCtx`, `SynCatFO`,
  `collapseDenotation`).
- Repository signatures quoted match the survey of the current pin
  (file:line given at each).
- Glossary vocabulary used throughout; no "critical arguments"
  except when naming the paper's term.

## References

- D. Leivant, "Ramified recurrence and computational complexity III:
  Higher type recurrence and elementary complexity", APAL 96 (1999)
  209-229. DOI `10.1016/S0168-0072(98)00040-2`.
- A. Beckmann, A. Weiermann, "Characterizing the elementary recursive
  functions by a fragment of Godel's T", Arch. Math. Logic 39 (2000)
  475-491.
- U. Dal Lago, S. Martini, M. Zorzi, "General ramified recurrence is
  sound for polynomial time", DICE 2010, EPTCS 23, 47-62.
  DOI `10.4204/EPTCS.23.4` (notation adoption only).
- N. Danner, J. S. Royer, "Ramified structural recursion and
  corecursion", 2012. arXiv `1201.4567` (data-system layer adoption).
- J. R. Otto, "Complexity doctrines", PhD thesis, McGill University,
  1995 (gate G5).
- Spec:
  `docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`
  (full reference list in its References section).
