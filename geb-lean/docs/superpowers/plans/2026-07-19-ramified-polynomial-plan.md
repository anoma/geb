# Ramified on the vendored polynomial-functor stack: implementation plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Global constraints](#global-constraints)
  - [Known pitfalls (from project memory; binding on executors)](#known-pitfalls-from-project-memory-binding-on-executors)
- [How to work this plan](#how-to-work-this-plan)
- [Decisions fixed by this plan](#decisions-fixed-by-this-plan)
- [File structure](#file-structure)
- [Phase map](#phase-map)
- [Phase A — W-type bridge, `FreeAlg'`, `RType'`](#phase-a--w-type-bridge-freealg-rtype)
  - [Task A.0: de-risking spike (fiber fold and tupling paramorphism)](#task-a0-de-risking-spike-fiber-fold-and-tupling-paramorphism)
  - [Task A.1: `toSlice` — translate `PolyEndo X` to `SlicePFunctor X X`](#task-a1-toslice--translate-polyendo-x-to-slicepfunctor-x-x)
  - [Task A.2: the fiberwise W-type equivalence](#task-a2-the-fiberwise-w-type-equivalence)
  - [Task A.3: `FreeAlg'` and the numeric carrier](#task-a3-freealg-and-the-numeric-carrier)
  - [Task A.4: `RType'` and its operations](#task-a4-rtype-and-its-operations)
  - [Task A.5: directory indices, test registration, area documentation](#task-a5-directory-indices-test-registration-area-documentation)
  - [Task A.6: Phase A adversarial review and user review](#task-a6-phase-a-adversarial-review-and-user-review)
- [Phase B — free-monad bridge and `Tm'`](#phase-b--free-monad-bridge-and-tm)
  - [Task B.0: write and converge the Phase B sub-plan](#task-b0-write-and-converge-the-phase-b-sub-plan)
- [Phase C — inter-definability on the primed type system](#phase-c--inter-definability-on-the-primed-type-system)
  - [Task C.0: write and converge the Phase C sub-plan](#task-c0-write-and-converge-the-phase-c-sub-plan)
- [Self-review checklist (run before adversarial review)](#self-review-checklist-run-before-adversarial-review)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Provide a second implementation of the `Ramified` recursive
layer (`FreeAlg`, `RType`, `Tm`) on the vendored geb-mathlib
polynomial-functor stack, connected to the existing implementation by a
transport-grade generic bridge, so that the existing inter-definability
with `ERMor` transfers to the new implementation by composition.

**Architecture:** A generic bridge between the legacy primitives
(`PolyFix`, `PolyFreeM` of `GebLean.PolyAlg`) and the vendored
primitives (`SlicePFunctor.W`, and later the augmented-signature free
monad) is proved once and instantiated at each `Ramified` recursive
type. The bridge is fold-both-ways: each direction is a recursor
application (`PolyFix.ind` legacy-side, `SlicePFunctor.W.elim`
vendored-side), round-trips closed by `PolyFix.ind` and `W.induction`.
Three phases: Phase A
(W-type bridge plus `FreeAlg'` and `RType'`), Phase B (free-monad bridge
plus `Tm'`), Phase C (inter-definability on the primed type system).
Phase A is detailed here; Phases B and C fix boundaries here and receive
step detail from mandatory sub-plans, because their steps consume Phase
A's (and B's) realized shapes.

**Authoritative spec:**
`docs/superpowers/specs/2026-07-19-ramified-polynomial-design.md`
(user-approved 2026-07-19). Section references "spec sN" below refer to
it.

**Tech Stack:** Lean 4 with mathlib and the vendored geb-mathlib
`Geb.Mathlib.Data.PFunctor` stack (`SlicePFunctor`, `SlicePFunctor.W`);
the legacy in-repository polynomial stack `GebLean.PolyAlg`
(`PolyEndo`, `PolyFix`, `PolyFreeM`); Lake; `mathlib`'s `Equiv`.

**Revision:** round 3 — folds in adversarial reviews 1-3
(`2026-07-19-ramified-polynomial-plan.review-1.md`, `.review-2.md`,
`.review-3.md`): the fiber-motive fold, paramorphism-via-tupling with
its reconstruction identity, operation-kind routing, test-driver
registration, and Phase C fixed to the presentation-rebuild scope (a
primed `SynCatFO'` related to the legacy category by an equivalence,
chosen at user review). The review cycle has converged (round 3:
zero-blocker, zero-major).

## Global constraints

Every task's requirements implicitly include this section. Values are
copied verbatim from spec s3.

- No `noncomputable` anywhere. `Classical.choice` is accepted in proofs
  only. `lake build` runs under `-DwarningAsError`, so a `noncomputable`
  obligation is a build failure.
- Recursor-only elimination of the recursive datatypes. Permitted:
  vendored `SlicePFunctor.W.elim`, `SlicePFunctor.W.RecProp`,
  `SlicePFunctor.W.induction`, `recProp_mk`, and (legacy-side, only in
  the bridge) `PolyFix.ind`. Forbidden over these types: the
  `induction` / `cases` / recursive `rcases` tactics, structurally
  recursive definitions (`match` with recursive self-calls),
  `termination_by`, well-founded recursion, and `WType.rec` or a native
  `.rec` in computational (non-erased) content. A non-recursive
  single-level `match`, and the trivial recursors `Eq.rec`,
  `Subtype`/`Sigma` projection, are permitted. The constraint governs
  the recursive tree datatypes (`PolyFix`, `SlicePFunctor.W`,
  `FreeAlg'`, `RType'`, `Tm'`); recursion over other inductives (for
  example `Nat` via `Nat.rec`) is a permitted recursor use.
  `Type`-valued eliminations use `W.elim` at the needed `Type`
  universe, recursive `Prop` ones use `W.RecProp`, and paramorphic ones
  (whose step needs the raw subterms) use the tupling encoding into
  `C × FreeAlg' A`.
- Axiom hygiene: `lake build GebLeanAxiomChecks` must pass
  (`propext`, `Quot.sound`, `Classical.choice` accepted; `sorryAx` and
  every other axiom rejected).
- Documentation: novelty annotations live only in this plan and the
  spec; Lean comments and docstrings cite only transcribed literature
  and make no novelty claim. Module and declaration docstrings are
  mandatory (spec s3, project doc rule).
- Style: mathlib naming and coding style; lines at most 100 characters;
  forward-only (do not reformat untouched code).
- Every source module has a mirrored `GebLeanTests/` module of the same
  name; tests are compositional.

### Known pitfalls (from project memory; binding on executors)

- Build only with `lake build` / `lake test`. Never `lake env lean`
  (it ignores `lakefile.toml` options and reports spurious errors).
  Never `lake clean` (forces a mathlib rebuild).
- The mathlib `fin_cases` tactic pulls in `Classical.choice`; for
  constructive case analysis over `Fin n`, use the Lean-core `Fin.cases`
  eliminator, not `fin_cases`. (Relevant if any position type is a
  `Fin`.)
- `simp only [if_pos h]` can leak `sorryAx`; prefer `rw [if_pos h]`.
- ER / Gödel-numbering interpreters are not safe for `#guard` kernel
  reduction; test numeric behaviour through proven `@[simp]` lemmas,
  not by evaluating composite trees.
- Pre-commit for any `.lean`-touching commit: `bash scripts/pre-commit.sh`
  (`lake test`, `lake lint`, `lake build GebLeanAxiomChecks`).

## How to work this plan

Each task ends with an independently testable deliverable and a commit.
Work one declaration at a time (no underscores or `sorry` at a task's
final commit). Use `_` to reveal a goal type during development; use
`#check` to inspect a signature. When `lake build` reports several
errors, fix the first before the rest. Run `bash scripts/pre-commit.sh`
before each commit; the axiom-checks build is part of it.

## Decisions fixed by this plan

- Directory `GebLean/PolyBridge/` (index `GebLean/PolyBridge.lean`)
  holds the generic bridge; `GebLean/Ramified/Polynomial/` (index
  `GebLean/Ramified/Polynomial.lean`) holds the `Ramified`
  instantiation (spec s1.2).
- The equivalence is transport-grade: a fiberwise `Equiv`, constructor
  naturality, recursor agreement (spec s1.2, s4).
- Phase B starts from the plain augmented `SlicePFunctor.W`; the
  `PresheafPFunctor` presheaf-monad presentation is deferred (spec s11).

## File structure

- `GebLean/PolyBridge.lean` — directory index; `public import`s the
  bridge modules.
- `GebLean/PolyBridge/Slice.lean` — `toSlice : PolyEndo X →
  SlicePFunctor X X` with its shape / position / index `@[simp]`
  characterization lemmas.
- `GebLean/PolyBridge/WEquiv.lean` — the forward and backward maps, the
  round-trip lemmas, the fiberwise `polyFixSliceEquiv`, constructor
  naturality, and recursor agreement.
- `GebLean/Ramified/Polynomial.lean` — directory index.
- `GebLean/Ramified/Polynomial/FreeAlg.lean` — `FreeAlg'`,
  `FreeAlg'.mk`, `FreeAlg'.recurse`, `freeAlgSliceEquiv`,
  `natToFreeAlg'` / `freeAlgToNat'`, `natFreeAlgEquiv'`.
- `GebLean/Ramified/Polynomial/RType.lean` — `RType'` and its
  operations (native on the vendored recursor) with their
  compatibility lemmas and `rTypeSliceEquiv`.
- Mirrored test modules under `GebLeanTests/PolyBridge/` and
  `GebLeanTests/Ramified/Polynomial/`.
- `docs/areas/polynomial-functors.md` and
  `docs/areas/ramified-recurrence.md` — module-list updates (Task A.6).

## Phase map

- Phase A (branch `feat/ramified-poly-bridge`): the W-type bridge and
  the `FreeAlg'` / `RType'` instantiation. Detailed below.
- Phase B (branch `feat/ramified-poly-freemonad`): the free-monad
  bridge and `Tm'`. Boundary fixed here; Task B.0 writes the sub-plan.
- Phase C (branch `feat/ramified-poly-er`): the ER-composition
  restatements. Boundary fixed here; Task C.0 writes the sub-plan.

---

## Phase A — W-type bridge, `FreeAlg'`, `RType'`

Branch `feat/ramified-poly-bridge`.

### Task A.0: de-risking spike (fiber fold and tupling paramorphism)

A short throwaway spike (scratch file, not committed) validating the two
constructions round-1 review flagged as load-bearing, before the real
tasks depend on them. It builds any needed `toSlice` / `FreeAlg'` stubs
inline (they are not yet defined; review Q6).

- [ ] **Step 1:** In a scratch module, build the fiber-motive forward
  fold `PolyFix P x → { w // wIndex w = x }` for
  `P := natAlgSig.polyEndo`, and confirm the `W.mk` compatibility
  discharges (review B1).
- [ ] **Step 2:** Build a paramorphic `FreeAlg'.recurse` by tupling into
  `C × FreeAlg' A` on the same `P`, and validate the reconstruction
  identity `(tupleFold p t).2 = t` and the resulting `recurse_mk`
  equation (reviews M1, P1 — `recurse_mk` is proved, not definitional).
- [ ] **Step 3:** Sketch the `toSliceW_ofSliceW` child-transport
  alignment (review M3) far enough to confirm the cast management
  closes. Record the working shapes in the Task A.2 / A.3 notes; delete
  the scratch module.

### Task A.1: `toSlice` — translate `PolyEndo X` to `SlicePFunctor X X`

**Files:**

- Create: `GebLean/PolyBridge/Slice.lean`
- Create: `GebLeanTests/PolyBridge/Slice.lean`
- Modify: `GebLean/PolyBridge.lean` (create index; `public import` this
  module)

**Interfaces:**

- Consumes: `GebLean.polyBetweenIndex X X P x`,
  `GebLean.polyBetweenFamily X X P x i : Over X` (from
  `GebLean/Polynomial.lean`); `CategoryTheory.Limits.Over`;
  `SlicePFunctor`, `SliceDomPFunctor` (from
  `Geb.Mathlib.Data.PFunctor.Slice.Basic`).
- Produces:
  - `def toSlice {X : Type u} (P : PolyEndo X) : SlicePFunctor.{u, u, u, u} X X`
    with underlying `PFunctor` shapes `A := Σ x : X, polyBetweenIndex X X P x`,
    positions `B ⟨x, i⟩ := (polyBetweenFamily X X P x i).left`, shape-output
    `q ⟨x, i⟩ := x`, direction-input
    `r ⟨⟨x, i⟩, e⟩ := (polyBetweenFamily X X P x i).hom e`.
  - `@[simp] theorem toSlice_A`, `toSlice_B`, `toSlice_q`, `toSlice_r`
    unfolding each component to the expression above.

- [ ] **Step 1: Write the failing test.** In
  `GebLeanTests/PolyBridge/Slice.lean`, import `GebLean.PolyBridge.Slice`
  and state, for `natAlgSig.polyEndo` (a `PolyEndo PUnit`), that the
  shape type `(toSlice natAlgSig.polyEndo).A` is inhabited by the two
  constructor shapes and that `q` of each is `PUnit.unit`. Use `example`
  goals closed by `rfl`/`decide` via the `@[simp]` lemmas.

- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.PolyBridge.Slice`. Expected: failure,
  `toSlice` not found.

- [ ] **Step 3: Implement `toSlice` and its `@[simp]` lemmas.** Write
  the module docstring (title, summary, `## Main definitions`,
  `## Main statements`, `## References` to Gambino–Kock 2013 and
  Abbott–Altenkirch–Ghani 2005; no novelty claim). Define `toSlice` by
  giving the `SlicePFunctor` record
  (`toPFunctor := ⟨_, _⟩`, `r := _`, `q := _`) with the components
  above. Prove each characterization lemma by `rfl`. Before committing
  the `SlicePFunctor.{u, u, u, u}` signature, verify
  `polyBetweenIndex X X P x` lands in `Type u` (not `Type (u+1)`), so
  the shape type stays in `Type u` (review N3).

- [ ] **Step 4: Run to verify it passes.** Run
  `lake build GebLeanTests.PolyBridge.Slice`. Expected: success.

- [ ] **Step 5: Axiom + lint gate.** Run `bash scripts/pre-commit.sh`.
  Expected: `lake test`, `lake lint`, and `lake build
  GebLeanAxiomChecks` all pass.

- [ ] **Step 6: Commit.**

```bash
jj commit -m "feat(polybridge): translate PolyEndo to SlicePFunctor"
```

### Task A.2: the fiberwise W-type equivalence

**Files:**

- Create: `GebLean/PolyBridge/WEquiv.lean`
- Create: `GebLeanTests/PolyBridge/WEquiv.lean`
- Modify: `GebLean/PolyBridge.lean` (`public import` this module)

**Interfaces:**

- Consumes: `toSlice`, `toSlice_*` (Task A.1); `PolyFix`, `PolyFix.mk`,
  `PolyFix.ind`, `PolyFix.index`, `PolyFix.getChildren` (from
  `GebLean/PolyAlg.lean`); `SlicePFunctor.W`, `wIndex`, `W.mk`, `W.dest`,
  `W.elim`, `W.elim_mk`, `W.comp_elim`, `W.RecProp`, `W.recProp_mk`,
  `W.induction` (from `Geb.Mathlib.Data.PFunctor.Slice.W`);
  `Equiv` (mathlib).
- Produces:
  - `def toSliceFib {X} {P : PolyEndo X} {x : X} (t : PolyFix P x) :`
    `{ w : (toSlice P).W // wIndex w = x }` — forward map, by
    `PolyFix.ind` with the **fiber** motive. (A bare-`W` motive cannot
    build `W.mk`: the node needs each child's index-compatibility, which
    only the fiber `.2` supplies — round-1 review B1.)
  - `def toSliceW {X} {P} {x} (t : PolyFix P x) : (toSlice P).W :=`
    `(toSliceFib t).1`; `theorem wIndex_toSliceW : wIndex (toSliceW t)`
    `= x := (toSliceFib t).2` (a projection, not a separate induction).
  - `def ofSliceW {X} (P : PolyEndo X) : (toSlice P).W → Σ x : X, PolyFix P x`
    — backward map, by `W.elim` into `Σ x, PolyFix P x` with
    `p := Sigma.fst`; the algebra reconstructs each child by an `Eq.rec`
    transport along the node's compatibility and `toSlice_r`.
  - `theorem ofSliceW_toSliceW : ofSliceW P (toSliceW t) = ⟨x, t⟩`.
  - `theorem toSliceW_ofSliceW : ∀ w, toSliceW (ofSliceW P w).2 = w`
    (over the fiber; needs `W.comp_elim` to relate `(ofSliceW P w).1`
    to `wIndex w`).
  - `def polyFixSliceEquiv {X} (P : PolyEndo X) (x : X) :`
    `PolyFix P x ≃ { w : (toSlice P).W // wIndex w = x }`, with
    `toFun := toSliceFib`.
  - `theorem polyFixSliceEquiv_mk` — constructor naturality: the image
    of `PolyFix.mk x i children` is the `W.mk` node whose children are
    `polyFixSliceEquiv` of the `children`.
  - `theorem elim_polyFixSliceEquiv` (recursor agreement, optional):
    `W.elim` through the equivalence equals the corresponding
    `PolyFix.ind` fold. Stated only if a downstream consumer needs it;
    the `FreeAlg'` operations reduce via their own `recurse_mk` /
    `W.induction`, so it may be omitted (code-is-cost, review Q1).

- [ ] **Step 1: Write the failing test.** In
  `GebLeanTests/PolyBridge/WEquiv.lean`, state that for a small sample
  tree `t : PolyFix natAlgSig.polyEndo PUnit.unit` (built with
  `PolyFix.mk`), `(polyFixSliceEquiv _ _).symm ((polyFixSliceEquiv _ _) t) = t`,
  and that `wIndex ((polyFixSliceEquiv _ _ t).1) = PUnit.unit`.

- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.PolyBridge.WEquiv`. Expected: failure,
  `polyFixSliceEquiv` not found.

- [ ] **Step 3: Implement the forward map.** Write the module docstring
  (title, summary, `## Main definitions`, `## Main statements`
  (`polyFixSliceEquiv_mk`, recursor agreement), `## References` to
  Abbott–Altenkirch–Ghani 2005 and Gambino–Kock 2013; no novelty
  claim). Define `toSliceFib` by `PolyFix.ind` with motive
  `fun {x} _ => { w : (toSlice P).W // wIndex w = x }`. At a node the IH
  gives, per position `e`, a child in the fiber over
  `(polyBetweenFamily X X P x i).hom e`; its `.2` supplies the `W.mk`
  compatibility, and the parent fiber proof follows from `toSlice_q`.
  Define `toSliceW := Subtype.val ∘ toSliceFib`, `wIndex_toSliceW` the
  `.2` projection.

- [ ] **Step 4: Implement the backward map `ofSliceW`.** By `W.elim`
  into `Σ x : X, PolyFix P x`, `p := Sigma.fst`, algebra
  `g node := ⟨(toSlice P).q node.1.1, PolyFix.mk _ _ (fun e => …)⟩`,
  where each child `(node.1.2 e).2 : PolyFix P (p (node.1.2 e))` is
  transported by `Eq.rec` to `PolyFix P ((polyBetweenFamily …).hom e)`
  along the node compatibility `node.2` and `toSlice_r` (review M3).
  `hg : Sigma.fst ∘ g = (toSlice P).obj p` is `funext (fun _ => rfl)`
  (since `(toSlice P).obj p = fun z => (toSlice P).q z.1.1`, and
  `cod = X`) — not `toSlice_q` (review N1).

- [ ] **Step 5: Prove the round-trips.** `ofSliceW_toSliceW` by
  `PolyFix.ind` and `W.elim_mk`, discharging the child `Eq.rec`
  transports against the compatibility proofs. `toSliceW_ofSliceW` by
  `W.induction` (a `Prop` motive) with `W.elim_mk` / `W.recProp_mk`,
  aligning the child transports against the IH. The cast/`HEq`
  management here is the round's chief difficulty; it is de-risked by
  the Task A.0 spike. No `induction` tactic; only the recursor
  combinators.

- [ ] **Step 6: Assemble `polyFixSliceEquiv`.** `toFun := toSliceFib`;
  `invFun w := (ofSliceW P w.1).2` reindexed along `w.2` and
  `(ofSliceW P w.1).1 = wIndex w.1` (from `W.comp_elim`); `left_inv`,
  `right_inv` from the round-trips.

- [ ] **Step 7: Prove naturality and recursor agreement.**
  `polyFixSliceEquiv_mk` by unfolding `toSliceFib` at a `mk` node
  (definitional via the `ind` step); `elim_polyFixSliceEquiv` from
  `W.elim_mk` and the `mk` naturality.

- [ ] **Step 8: Run tests.** Run `lake build GebLeanTests.PolyBridge.WEquiv`.
  Expected: success.

- [ ] **Step 9: Axiom + lint gate.** Run `bash scripts/pre-commit.sh`.
  Expected: all pass (in particular no `Classical.choice`-outside-proof
  and no `sorryAx`).

- [ ] **Step 10: Commit.**

```bash
jj commit -m "feat(polybridge): add fiberwise PolyFix/SlicePFunctor.W equivalence"
```

### Task A.3: `FreeAlg'` and the numeric carrier

**Files:**

- Create: `GebLean/Ramified/Polynomial/FreeAlg.lean`
- Create: `GebLeanTests/Ramified/Polynomial/FreeAlg.lean`
- Create: `GebLean/Ramified/Polynomial.lean` (directory index)

**Interfaces:**

- Consumes: `polyFixSliceEquiv`, `polyFixSliceEquiv_mk` (Task A.2);
  `AlgSig`, `AlgSig.polyEndo`,
  `natAlgSig`, `natFreeAlgEquiv`, `natToFreeAlg`, `freeAlgToNat` (from
  `GebLean/Ramified/AlgSig.lean`, `GebLean/Ramified/Algebras.lean`);
  `SlicePFunctor.W`, `W.mk`, `W.elim` (vendored).
- Produces:
  - `def FreeAlg' (A : AlgSig) : Type :=`
    `{ w : (toSlice A.polyEndo).W // wIndex w = PUnit.unit }`.
  - `def FreeAlg'.mk {A} (b : A.B)`
    `(subterms : Fin (A.ar b) → FreeAlg' A) : FreeAlg' A`
    — native, via `W.mk`.
  - `def FreeAlg'.tupleFold {A} {P C} (g : …) (p : P) :`
    `FreeAlg' A → C × FreeAlg' A` — the `p`-parametrized `W.elim` fold
    (target `C × FreeAlg' A` for a fixed `p` captured in the algebra,
    not `(P → C) × …`), reconstructing each subterm as the paired `.2`.
  - `def FreeAlg'.recurse {A} {P C} (g : …) : P → FreeAlg' A → C :=`
    `fun p => Prod.fst ∘ FreeAlg'.tupleFold g p` — the native
    paramorphism (step sees the raw subterms and the recursive results,
    as `FreeAlg.recurse` does), since `W.elim` is a catamorphism
    (review M1).
  - `theorem FreeAlg'.tupleFold_snd` — the reconstruction identity
    `(tupleFold p t).2 = t`, by `W.induction` via `mk_dest` (review P1;
    not definitional, since the fold re-wraps each subtree through
    `FreeAlg'.mk`).
  - `theorem FreeAlg'.recurse_mk` — the reduction rule, a theorem from
    `W.elim_mk` **and** `FreeAlg'.tupleFold_snd` (not `W.elim_mk`
    alone).
  - `def freeAlgSliceEquiv (A : AlgSig) : FreeAlg' A ≃ FreeAlg A :=`
    `polyFixSliceEquiv A.polyEndo PUnit.unit` — typechecks by unfolding
    the `def`s `FreeAlg` and `FreeAlg'`; no `Eq.rec` transport
    (review N2).
  - `theorem freeAlgSliceEquiv_mk` — `mk` naturality across the equiv.
  - `def natToFreeAlg' : Nat → FreeAlg' natAlgSig`,
    `def freeAlgToNat' : FreeAlg' natAlgSig → Nat`,
    `def natFreeAlgEquiv' : FreeAlg' natAlgSig ≃ ℕ` (defined as
    `freeAlgSliceEquiv natAlgSig |>.trans natFreeAlgEquiv`).
  - `@[simp] theorem freeAlgToNat'_natToFreeAlg' (n : Nat) :
      freeAlgToNat' (natToFreeAlg' n) = n`.

- [ ] **Step 1: Write the failing test.** In
  `GebLeanTests/Ramified/Polynomial/FreeAlg.lean`, assert
  `freeAlgToNat' (natToFreeAlg' 3) = 3` and
  `natFreeAlgEquiv' (natToFreeAlg' 3) = 3` (through proven `@[simp]`
  lemmas — do not rely on kernel reduction of composite trees; see the
  known-pitfall on Gödel interpreters).

- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.Polynomial.FreeAlg`. Expected:
  failure.

- [ ] **Step 3: Define `FreeAlg'`, `FreeAlg'.mk`, `FreeAlg'.recurse`,
  the reconstruction identity, and `FreeAlg'.recurse_mk`.** Write the
  module docstring (title, summary, `## Main definitions`,
  `## Main statements`, `## References` to Leivant III section 2.1; no
  novelty claim). `mk` via `W.mk` at shape `⟨PUnit.unit, b⟩`. `recurse`
  as a paramorphism via the tupling encoding: `W.elim` into
  `C × FreeAlg' A` whose algebra applies `g` to the parameter, the
  reconstructed subterms (`.2` components), and the recursive results
  (`.1` components); `recurse := Prod.fst ∘ …`. Prove
  `FreeAlg'.tupleFold_snd : (tupleFold p t).2 = t` by `W.induction`
  (`mk_dest`); then `recurse_mk` from `W.elim_mk` and that identity.

- [ ] **Step 4: Define `freeAlgSliceEquiv` and `freeAlgSliceEquiv_mk`.**
  `freeAlgSliceEquiv A := polyFixSliceEquiv A.polyEndo PUnit.unit`
  (typechecks by unfolding `FreeAlg` and `FreeAlg'`; no transport);
  derive `mk` naturality from `polyFixSliceEquiv_mk`.

- [ ] **Step 5: Define the numeric carrier and prove the round-trip.**
  `natFreeAlgEquiv' := (freeAlgSliceEquiv natAlgSig).trans natFreeAlgEquiv`;
  define `natToFreeAlg'`/`freeAlgToNat'` as its two directions (or as
  native `mk`/`recurse` and prove they agree with the transported
  ones). Prove `freeAlgToNat'_natToFreeAlg'` from the `Equiv` laws.

- [ ] **Step 6: Run tests.** Run
  `lake build GebLeanTests.Ramified.Polynomial.FreeAlg`. Expected:
  success.

- [ ] **Step 7: Axiom + lint gate.** Run `bash scripts/pre-commit.sh`.

- [ ] **Step 8: Commit.**

```bash
jj commit -m "feat(ramified): add FreeAlg' on the vendored W-type with numeric carrier"
```

### Task A.4: `RType'` and its operations

**Files:**

- Create: `GebLean/Ramified/Polynomial/RType.lean`
- Create: `GebLeanTests/Ramified/Polynomial/RType.lean`
- Modify: `GebLean/Ramified/Polynomial.lean` (`public import`)

**Interfaces:**

- Consumes: `FreeAlg'`, `FreeAlg'.mk`, `FreeAlg'.recurse`,
  `freeAlgSliceEquiv`, `freeAlgSliceEquiv_mk` (Task A.3); `W.elim`,
  `W.dest`, `wIndex`, `W.RecProp`, `W.induction` (vendored); `rTypeSig`,
  `RType`, `RType.o`,
  `RType.arrow`, `RType.omega`, `RTypeShape`, and the target operations
  by their homes: `RType.shape`, `RType.interp`, `RType.tower`,
  `RType.IsObj`, `RType.IsTower`, `RType.IsSimple`
  (`GebLean/Ramified/RType.lean`); `RType.omegaShift`,
  `RType.objTarget`, `RType.domains`
  (`GebLean/Ramified/OmegaShift.lean`); `RType.ord`
  (`GebLean/Ramified/Soundness/Normalization.lean`).
- Produces:
  - `def RType' : Type := FreeAlg' rTypeSig`.
  - `def RType'.o`, `RType'.arrow`, `RType'.omega` — via `FreeAlg'.mk`.
  - `def rTypeSliceEquiv : RType' ≃ RType := freeAlgSliceEquiv rTypeSig`,
    with constructor `@[simp]` lemmas `rTypeSliceEquiv_o`,
    `rTypeSliceEquiv_arrow`, `rTypeSliceEquiv_omega` (from
    `freeAlgSliceEquiv_mk`).
  - The operations, routed by kind (reviews B2, M1, M2, N5):
    - one-level (no tree recursion): `RType'.shape` via the shape
      index / `W.dest`; `RType'.IsObj` shape-based.
    - `Type`-valued: `RType'.interp` via `W.elim` at `Y := Type`
      (`uY = 1`), `p` into `PUnit` — not `FreeAlg'.recurse`, whose
      `C : Type` cannot hold `Type`.
    - recursive `Prop` predicates: `RType'.IsTower`, `RType'.IsSimple`
      via `W.RecProp` — not `W.elim`.
    - paramorphic data ops (step reads the raw subterm):
      `RType'.objTarget`, `RType'.domains` via the tupling
      `FreeAlg'.recurse`.
    - catamorphic data ops: `RType'.omegaShift`, `RType'.ord` via
      `FreeAlg'.recurse`.
    - `RType'.tower : Nat → RType'` via `Nat.rec` (recurses on `Nat`,
      built from `RType'` constructors; not a tree recursion).
  - Ten operation-compatibility lemmas, each
    `op' t = op (rTypeSliceEquiv t)` (for `tower`, `tower' n = tower n`):
    `rTypeSliceEquiv_shape`, `_omegaShift`, `_objTarget`, `_domains`,
    `_interp`, `_ord`, `_tower`, `_isObj`, `_isTower`, `_isSimple`.

- [ ] **Step 1: Write the failing test.** In
  `GebLeanTests/Ramified/Polynomial/RType.lean`, assert
  `rTypeSliceEquiv (RType'.arrow RType'.o RType'.o) = RType.arrow RType.o RType.o`
  and `RType'.ord (RType'.arrow RType'.o RType'.o)`
  `= RType.ord (RType.arrow RType.o RType.o)`.

- [ ] **Step 2: Run to verify it fails.** Run
  `lake build GebLeanTests.Ramified.Polynomial.RType`. Expected:
  failure.

- [ ] **Step 3: Define `RType'` and its constructors.** Write the
  module docstring (title, summary, `## Main definitions`,
  `## Main statements`, `## References` to Leivant III sections 2.3-2.4;
  no novelty claim). Define `RType'` via `FreeAlg'` and its constructors
  via `FreeAlg'.mk`,
  plus `rTypeSliceEquiv` and the constructor `@[simp]` compatibility
  lemmas (from `freeAlgSliceEquiv_mk`).

- [ ] **Step 4: Re-express each operation natively.** Following the
  by-kind routing in Produces, write each `RType'` operation one at a
  time, each with its docstring: `interp` via a `Type`-universe
  `W.elim`; `IsTower` / `IsSimple` via `W.RecProp`; the paramorphic
  `objTarget` / `domains` via the tupling `FreeAlg'.recurse`; the
  catamorphic `omegaShift` / `ord` via `FreeAlg'.recurse`; `shape` /
  `IsObj` one-level; `tower` via `Nat.rec`. Recursor-only over the tree;
  a non-recursive `match` on the finite `RTypeShape` inside a step is
  permitted.

- [ ] **Step 5: Prove one compatibility lemma per operation.** Each
  `op' t = op (rTypeSliceEquiv t)` by `W.induction` (a `Prop` motive),
  reducing with the operation's computation rule (`FreeAlg'.recurse_mk`
  / `W.recProp_mk` / the `W.elim_mk` for `interp`) and the constructor
  compatibility lemmas, one at a time. `interp`'s is a `Type` equality
  (arrow case needs `→`-former congruence on the two child type
  equalities); `tower`'s is by `Nat.rec`.

- [ ] **Step 6: Run tests.** Run
  `lake build GebLeanTests.Ramified.Polynomial.RType`. Expected:
  success.

- [ ] **Step 7: Axiom + lint gate.** Run `bash scripts/pre-commit.sh`.

- [ ] **Step 8: Commit.**

```bash
jj commit -m "feat(ramified): add RType' on the vendored stack with operation compatibility"
```

### Task A.5: directory indices, test registration, area documentation

**Files:**

- Modify: `GebLean/PolyBridge.lean`, `GebLean/Ramified/Polynomial.lean`
  (ensure every source module is `public import`ed, one-line index
  docstring).
- Create: `GebLeanTests/PolyBridge.lean` (imports
  `GebLeanTests.PolyBridge.Slice`, `.WEquiv`);
  `GebLeanTests/Ramified/Polynomial.lean` (imports
  `GebLeanTests.Ramified.Polynomial.FreeAlg`, `.RType`).
- Modify: `GebLeanTests.lean` (add `import GebLeanTests.PolyBridge`);
  `GebLeanTests/Ramified.lean` (add
  `import GebLeanTests.Ramified.Polynomial`). Without this, `lake test`
  (the `testDriver` aggregator graph) silently skips the new test
  modules (review M5).
- Modify: `docs/areas/polynomial-functors.md` (add `GebLean/PolyBridge/`
  entries), `docs/areas/ramified-recurrence.md` (add the
  `Ramified/Polynomial/` entries and a pointer to this spec/plan).

- [ ] **Step 1: Complete the source and test index files.** Ensure the
  two source indexes list each submodule; create the two test indexes
  and register them in `GebLeanTests.lean` /
  `GebLeanTests/Ramified.lean`.

- [ ] **Step 2: Verify `lake test` now covers the new modules.** Run
  `lake test`; confirm the new `GebLeanTests` modules build in the
  aggregate, not only via per-module `lake build`.

- [ ] **Step 3: Update the area docs.** Add the new modules to the
  module lists; run `doctoc --update-only .` and
  `markdownlint-cli2 '**/*.md'`. Expected: both clean.

- [ ] **Step 4: Full pre-push gate.** Run `bash scripts/pre-push.sh`.
  Expected: all checks pass.

- [ ] **Step 5: Commit.**

```bash
jj commit -m "chore(ramified): wire polynomial-stack modules into indexes and tests"
```

### Task A.6: Phase A adversarial review and user review

- [ ] **Step 1:** Run an adversarial review of the branch against the
  spec and the mathlib upstream guides (re-fetched), markdownlint-clean
  per project rule. Address findings.
- [ ] **Step 2:** Hand the branch to the user for line-by-line review
  before any push (spec s3 gate; no `jj git push` without user review).

---

## Phase B — free-monad bridge and `Tm'`

Branch `feat/ramified-poly-freemonad`. Boundary fixed here; step detail
in a mandatory sub-plan.

**Deliverables (fixed):**

- `polyFreeMSlice` — the free monad as the vendored W-type of the
  augmented signature (signature endofunctor extended by variable
  leaves), on the plain `SlicePFunctor.W` (spec s4.2, s11 resolution).
- `polyFreeMSliceEquiv` — the carrier equivalence, reusing
  `polyFixSliceEquiv` on the augmented pfunctor.
- `Tm'`, `Tm'.var`, `Tm'.op`, `Tm'.subst`; substitution compatibility
  `Tm'.subst ↔ Tm.subst` across the equivalence; the clone laws for
  `Tm'` transported or reproved via the recursor.

**Consumes:** `polyFixSliceEquiv` and `toSlice` (Phase A);
`PolyFreeM`, `polyFreeMPure`, `polyFreeMBind` and the monad laws (from
`GebLean/PolyAlg.lean`); `Tm`, `Tm.var`, `Tm.op`, `Tm.subst` (from
`GebLean/Ramified/Term.lean`).

### Task B.0: write and converge the Phase B sub-plan

- [ ] **Step 1:** Write `docs/superpowers/plans/2026-07-19-ramified-poly-freemonad-subplan.md`
  with bite-sized tasks for the deliverables above, fixing the
  augmented-signature construction against the realized Phase A shapes.
- [ ] **Step 2:** Adversarially review and user-review the sub-plan
  before execution.

---

## Phase C — inter-definability on the primed type system

Branch `feat/ramified-poly-er`. Boundary fixed here; step detail in a
mandatory sub-plan.

The existing endpoints `ramified_definability` /
`ramified_definability_kSim` (`GebLean/Ramified/Characterization.lean`)
quantify over `ObjCtx` (contexts of `RType`) and `SynCatFO` morphisms
(over `Tm`), concluding `collapseDenotation g = arityCongr … f.interp`.
They do not mention the numeric carrier `FreeAlg natAlgSig` (that lives
inside the denotation), but they rest pervasively on `RType` and `Tm` —
the recursive types Phases A and B re-express. Phase C carries the
statements onto the primed types by transport across the equivalences,
reusing the existing ER definability and soundness proofs (spec s6).

> Note (review-2 P2, resolved at user review — rebuild chosen):
> `SynCat` / `RMRecCat` are parametrized by a whole `Presentation` and
> hardwired to legacy `Tm`, so a type equivalence `RType' ≃ RType`
> cannot be transported into a category. The primed `SynCatFO'` is
> therefore a rebuild of a primed `Presentation'` related to the legacy
> one by an equivalence of categories, across which the endpoints
> transfer. Task C.0 settles the rebuild scope, in particular whether
> `SynCat'` uses legacy `Tm` over the primed signature or the vendored
> `Tm'`.

**Deliverables (fixed; rebuild):**

- `ObjCtx'` / `SynCatFO'` / `collapseDenotation'` (and `oCtx'`,
  `arityCongr'` as needed) on `RType'` (Phase A) and `Tm'` (Phase B),
  built from a primed `Presentation'` (`higherOrder'` and standard model
  over `RType'`), with `RMRecCat' ≌ RMRecCat` established from the A/B
  equivalences.
- `ramified_definability'` and `ramified_definability_kSim'` over the
  primed stack, proved by transferring the existing theorems across
  `RMRecCat' ≌ RMRecCat`. The ER-side content
  (`erMorN_ramified_definable`, `collapseFunctor` faithfulness,
  `f.interp`) is reused unchanged; transferring the endpoint equation
  additionally needs a lemma that `collapseDenotation'` agrees with
  `collapseDenotation` across the equivalence (a Task C.0 obligation,
  not free reuse — review-3).

**Consumes:** `rTypeSliceEquiv` and its operation-compatibility lemmas
(Phase A); the `Tm'` equivalence and `Tm'.subst` compatibility
(Phase B); the existing `ObjCtx`, `SynCatFO`, `collapseDenotation`,
`arityCongr`, `ramified_definability`, `ramified_definability_kSim`
(`GebLean/Ramified/`).

### Task C.0: write and converge the Phase C sub-plan

- [ ] **Step 1:** Write
  `docs/superpowers/plans/2026-07-19-ramified-poly-er-subplan.md`
  fixing, against the realized Phase A/B shapes, the rebuild scope
  (which of `RMRecCat`, the `Binding` layer, and `SynCatFO` need a
  primed rebuild; whether `SynCat'` uses legacy `Tm` over the primed
  signature or the vendored `Tm'`), the shape of `RMRecCat' ≌ RMRecCat`,
  the `collapseDenotation'`-across-equivalence compatibility lemma, and
  the final statement shapes of `ramified_definability'` /
  `ramified_definability_kSim'`.
- [ ] **Step 2:** Adversarially review and user-review the sub-plan
  before execution.

---

## Self-review checklist (run before adversarial review)

- Spec coverage: s4.1 W-type bridge (Tasks A.1–A.2); s5 instantiation
  (Tasks A.3–A.4); s4.2 free-monad bridge (Phase B); s6 ER composition
  on the primed type system (Phase C); s3 constraints (Global
  constraints); s9 testing (mirrored test modules per task, registered
  in the `GebLeanTests` aggregators — Task A.5).
- Placeholder scan: no "TBD"/"handle edge cases"; every task names exact
  declarations and files.
- Type consistency: `toSlice`, `polyFixSliceEquiv`, `freeAlgSliceEquiv`,
  `rTypeSliceEquiv`, `natFreeAlgEquiv'` used with the same signatures in
  Consumes/Produces across tasks.
- Constraint check: every elimination step names a recursor combinator
  (`PolyFix.ind`, `W.elim`, `W.RecProp`, `W.induction`); no task uses
  the `induction` tactic or structural recursion. `Type`-valued ops use
  `W.elim`, recursive `Prop` predicates `W.RecProp`, paramorphic ops the
  tupling encoding; `Nat.rec` (non-tree) is permitted for `tower`.

## References

- M. Abbott, T. Altenkirch, N. Ghani, "Containers: constructing
  strictly positive types", Theoretical Computer Science 342 (2005)
  3-27. DOI `10.1016/j.tcs.2005.06.002`.
- N. Gambino, J. Kock, "Polynomial functors and polynomial monads",
  Mathematical Proceedings of the Cambridge Philosophical Society 154
  (2013) 153-192. DOI `10.1017/S0305004112000394`.
- D. Leivant, "Ramified recurrence and computational complexity III:
  Higher type recurrence and elementary complexity", Annals of Pure and
  Applied Logic 96 (1999) 209-229. DOI `10.1016/S0168-0072(98)00040-2`.
