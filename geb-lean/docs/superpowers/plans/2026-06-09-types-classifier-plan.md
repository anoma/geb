# Types-Classifier Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Construct `Classifier (Type u)` with classifying
object `ULift.{u} Prop`, prove the full universal property,
register `HasClassifier (Type u)`, and relate the result to the
presheaf classifier of `GebLean.Utilities.Presheaf` specialized
to the terminal category.

**Architecture:** One new module
`GebLean/Utilities/TypesClassifier.lean`. Core data
(`typesIsTerminalPUnit`, `typesTruth`, `typesCharMap`) are
computable closed terms; the universal property is proved
elementwise via mathlib's `Types.isPullback_iff` and
`Types.exists_of_isPullback`, with `propext` discharging the
uniqueness clause; the `Classifier` is assembled with
`Classifier.mkOfTerminalΩ₀`. A comparison section proves
`Sieve c ≃ ULift Prop` over `Discrete PUnit` and truth-morphism
compatibility with `pshSieveTruth`.

**Tech Stack:** Lean 4, mathlib
`CategoryTheory.Topos.Classifier`,
`CategoryTheory.Limits.Types.Pullbacks`,
`CategoryTheory.Sites.Sieves` (via `Presheaf.lean`);
project-internal `GebLean.Utilities.Presheaf`.

**Spec:**
[`docs/superpowers/specs/2026-06-09-types-classifier-design.md`](../specs/2026-06-09-types-classifier-design.md)
(3-round adversarial-converged).

---

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [File structure](#file-structure)
- [Topic branch](#topic-branch)
- [Common verification commands](#common-verification-commands)
- [Task 0: Baseline verification](#task-0-baseline-verification)
- [Task 1: Module skeleton, core data, `typesCharMap_apply_eq_true`](#task-1-module-skeleton-core-data-typescharmap_apply_eq_true)
- [Task 2: `typesCharMap_isPullback`](#task-2-typescharmap_ispullback)
- [Task 3: `typesCharMap_unique`](#task-3-typescharmap_unique)
- [Task 4: `typesClassifier` and the `HasClassifier` instance](#task-4-typesclassifier-and-the-hasclassifier-instance)
- [Task 5: Comparison with the presheaf classifier](#task-5-comparison-with-the-presheaf-classifier)
- [Task 6: Tests](#task-6-tests)
- [Task 7: Axiom audit and final verification](#task-7-axiom-audit-and-final-verification)
- [Post-implementation](#post-implementation)

<!-- END doctoc -->

## File structure

| File | Change | Task |
| --- | --- | --- |
| `GebLean/Utilities/TypesClassifier.lean` | Create: core construction (Tasks 1–4), comparison section (Task 5) | 1–5 |
| `GebLean/Utilities.lean` | Add `import GebLean.Utilities.TypesClassifier` (anchor in Task 1) | 1 |
| `GebLeanTests/Utilities/TypesClassifier.lean` | Create: `example`-based tests | 6 |
| `GebLeanTests.lean` | Add `import GebLeanTests.Utilities.TypesClassifier` (anchor in Task 6) | 6 |

## Topic branch

All work happens on the existing topic branch
`feat/types-classifier` (the spec and its reviews are already
committed there). The repository uses `jj` in colocated mode at
the parent `geb/` root; never use mutating raw `git`.

## Common verification commands

From `/home/terence/git-workspaces/geb/geb-lean`:

```bash
lake build          # full build; the authoritative check
lake test           # builds GebLeanTests
bash scripts/pre-commit.sh   # lake test + lake lint; required
                             # before every .lean-touching commit
```

Commit recipe (after `bash scripts/pre-commit.sh` passes):

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "<message>"
jj bookmark set feat/types-classifier -r @-
cd /home/terence/git-workspaces/geb/geb-lean
```

Never run `lake env lean <file>` (it drops `lakefile.toml`
options and produces spurious errors). Never run `lake clean`.

If a proof step in this plan fails to elaborate, do not
improvise silently: check the goal with `lean_goal`
(lean-lsp MCP), verify the cited lemma name with
`lean_local_search`, and consult the spec's §6 fallbacks. The
spec's §6 names one sanctioned fallback per proof; anything
beyond that is a plan defect to report, not to patch around.

## Task 0: Baseline verification

**Files:** none modified.

- [ ] **Step 1: Confirm clean working copy on the topic branch**

```bash
cd /home/terence/git-workspaces/geb && jj st
```

Expected: "The working copy has no changes." with the parent
commit at the `feat/types-classifier` bookmark (the branch
head; its description varies as review commits land).

- [ ] **Step 2: Confirm baseline build and tests pass**

```bash
cd /home/terence/git-workspaces/geb/geb-lean && lake build && lake test
```

Expected: both succeed with no errors. If not, halt and report;
do not start Task 1 on a broken baseline.

## Task 1: Module skeleton, core data, `typesCharMap_apply_eq_true`

**Files:**

- Create: `GebLean/Utilities/TypesClassifier.lean`
- Modify: `GebLean/Utilities.lean` (one import line)

Spec reference: §4, §5.1 (data declarations), §6 (first proof
shape).

- [ ] **Step 1: Create the module with docstring, data, and the first lemma**

Create `GebLean/Utilities/TypesClassifier.lean` with exactly
this content:

```lean
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Topos.Classifier

/-!
# Subobject classifier for `Type u` via `Prop`

`ULift.{u} Prop` is a subobject classifier for the category
`Type u`: the characteristic map of a monomorphism `m : U ⟶ X`
sends `x : X` to the proposition `∃ a, m a = x`, and the truth
morphism selects `True`. Impredicativity of `Prop` plays the
role of the propositional-resizing hypothesis of [UF13],
Theorem 10.1.12 (a small type `Ω` of all mere propositions),
and `propext` plays the role of univalence restricted to
propositions; together they discharge the universal property,
including the uniqueness clause.

## Main definitions

- `GebLean.typesClassifier`: `Classifier (Type u)` with
  classifying object `ULift Prop`.
- `GebLean.typesHasClassifier`: the `HasClassifier (Type u)`
  instance.

## References

- [UF13] The Univalent Foundations Program, *Homotopy Type
  Theory: Univalent Foundations of Mathematics*, 2013,
  §10.1.4–10.1.5, Theorem 10.1.12.
- [MM92] S. MacLane and I. Moerdijk, *Sheaves in Geometry and
  Logic*, Springer, 1992, §I.3–I.4.
-/

open CategoryTheory

namespace GebLean

universe u

/-- `PUnit` is terminal in `Type u`. Computable variant of
mathlib's `noncomputable` `Limits.Types.isTerminalPUnit`
(which routes through the choice-based `⊤_ (Type u)`). -/
def typesIsTerminalPUnit :
    Limits.IsTerminal (PUnit.{u + 1} : Type u) :=
  Limits.IsTerminal.ofUniqueHom (fun _ _ => PUnit.unit)
    (fun _ _ => funext fun _ => rfl)

/-- The truth morphism for the subobject classifier of
`Type u`: the point of `ULift Prop` selecting `True`. -/
def typesTruth : PUnit.{u + 1} ⟶ ULift.{u} Prop :=
  fun _ => ULift.up True

/-- The characteristic map of a morphism `m : U ⟶ X` in
`Type u`: membership in the image of `m`. -/
def typesCharMap {U X : Type u} (m : U ⟶ X) :
    X ⟶ ULift.{u} Prop :=
  fun x => ULift.up (∃ a, m a = x)

theorem typesCharMap_apply_eq_true {U X : Type u} (m : U ⟶ X)
    (a : U) : typesCharMap m (m a) = ULift.up True :=
  congrArg ULift.up (eq_true ⟨a, rfl⟩)

end GebLean
```

Notes for the implementer:

- `eq_true ⟨a, rfl⟩ : (∃ a', m a' = m a) = True`; `congrArg
  ULift.up` lifts it, and the left side is definitionally
  `typesCharMap m (m a)`.
- `IsTerminal.ofUnique _` must NOT be used here: typeclass
  resolution does not unfold `X ⟶ PUnit` to `X → PUnit`, so the
  `Unique` instance is not found (spec §5.1).
- The file deliberately omits the `module` keyword of
  `.claude/rules/lean-coding.md` § Lean 4 module system: no
  existing `GebLean` source uses the module system, and a lone
  module-system file would interact with the non-module
  importers through visibility rules none of the surrounding
  code is written for. Repository-wide module-system migration
  is out of scope; this deviation is recorded here so the
  executing agent does not adjudicate the conflict.

- [ ] **Step 2: Wire the module into the Utilities index**

In `GebLean/Utilities.lean`, insert

```lean
import GebLean.Utilities.TypesClassifier
```

between the existing lines
`import GebLean.Utilities.TwistedArrow` and
`import GebLean.Utilities.WSubfunctor` (the file's final two
imports as of the baseline).

- [ ] **Step 3: Build**

```bash
lake build
```

Expected: success, no errors, no warnings (the project builds
with `-DwarningAsError=true`).

- [ ] **Step 4: Verify computability and axioms of the data**

Using the lean-lsp MCP tool `lean_verify` (or a scratch
`#print axioms` that is deleted before commit), check:

- `GebLean.typesIsTerminalPUnit`: axioms within
  {`propext`, `Quot.sound`, `Classical.choice`}; the
  declaration itself is a plain `def` (no `noncomputable`).
- `GebLean.typesTruth`, `GebLean.typesCharMap`: no axioms.
- `GebLean.typesCharMap_apply_eq_true`: `propext` only.

Expected per spec §7. Small deviations within the accepted
axiom set {`propext`, `Quot.sound`, `Classical.choice`} are
acceptable; anything outside it is a failure.

- [ ] **Step 5: Pre-commit checks and commit**

```bash
bash scripts/pre-commit.sh
```

Expected: passes. Then:

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "feat(types-classifier): add classifier data for Type u"
jj bookmark set feat/types-classifier -r @-
cd /home/terence/git-workspaces/geb/geb-lean
```

## Task 2: `typesCharMap_isPullback`

**Files:**

- Modify: `GebLean/Utilities/TypesClassifier.lean` (add one
  theorem before `end GebLean`)

Spec reference: §5.1, §6 (pullback proof shape).

- [ ] **Step 1: Add the pullback theorem**

Insert before `end GebLean`:

```lean
theorem typesCharMap_isPullback {U X : Type u} (m : U ⟶ X)
    [Mono m] :
    IsPullback m (typesIsTerminalPUnit.from U)
      (typesCharMap m) typesTruth := by
  rw [Limits.Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · funext a
    simp only [types_comp_apply]
    exact typesCharMap_apply_eq_true m a
  · rintro a b ⟨hm, -⟩
    exact (mono_iff_injective m).mp inferInstance hm
  · intro x p hx
    obtain ⟨a, ha⟩ := of_eq_true (congrArg ULift.down hx)
    exact ⟨a, ha, Subsingleton.elim _ _⟩
```

Notes for the implementer:

- `Limits.Types.isPullback_iff` reduces the goal to three
  clauses: square commutativity, joint injectivity of the two
  legs, and existence of a preimage for every matching pair
  (spec §6). The corners map as `t := m`,
  `l := typesIsTerminalPUnit.from U`, `r := typesCharMap m`,
  `b := typesTruth`.
- Clause 1: after `types_comp_apply`, the right side
  `typesTruth (typesIsTerminalPUnit.from U a)` is
  definitionally `ULift.up True`, so
  `typesCharMap_apply_eq_true` closes the goal. If the defeq
  is not accepted, insert
  `show typesCharMap m (m a) = ULift.up True` before `exact`.
- Clause 3: `hx : typesCharMap m x = typesTruth p`;
  `congrArg ULift.down hx : (∃ a, m a = x) = True`;
  `of_eq_true` recovers the proposition; the witness
  extraction is `Prop`-to-`Prop` (`Exists.elim` via
  `obtain`), no choice. The `PUnit` component is
  `Subsingleton.elim`.
- Sanctioned fallback (spec §6): if `isPullback_iff` does not
  apply directly, construct the limit cone with
  `Limits.PullbackCone.IsLimit.mk`; the elementwise content is
  identical. Use the fallback only after recording the failure
  mode.

- [ ] **Step 2: Build**

```bash
lake build
```

Expected: success.

- [ ] **Step 3: Verify axioms**

`lean_verify` (or scratch `#print axioms`, deleted before
commit) on `GebLean.typesCharMap_isPullback`: subset of
{`propext`, `Quot.sound`, `Classical.choice`}.

- [ ] **Step 4: Pre-commit checks and commit**

```bash
bash scripts/pre-commit.sh
```

Then:

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "feat(types-classifier): prove pullback square for typesCharMap"
jj bookmark set feat/types-classifier -r @-
cd /home/terence/git-workspaces/geb/geb-lean
```

## Task 3: `typesCharMap_unique`

**Files:**

- Modify: `GebLean/Utilities/TypesClassifier.lean` (add one
  theorem before `end GebLean`)

Spec reference: §5.1, §6 (uniqueness proof shape).

- [ ] **Step 1: Add the uniqueness theorem**

Insert before `end GebLean`:

```lean
theorem typesCharMap_unique {U X : Type u} (m : U ⟶ X)
    [Mono m] (χ' : X ⟶ ULift.{u} Prop)
    (hχ' : IsPullback m (typesIsTerminalPUnit.from U)
      χ' typesTruth) :
    χ' = typesCharMap m := by
  funext x
  have hiff : (χ' x).down ↔ ∃ a, m a = x := by
    constructor
    · intro h
      have hx : χ' x = typesTruth PUnit.unit :=
        congrArg ULift.up (eq_true h)
      obtain ⟨a, ha, -⟩ :=
        Limits.Types.exists_of_isPullback hχ' x PUnit.unit hx
      exact ⟨a, ha⟩
    · rintro ⟨a, rfl⟩
      have hw := congr_fun hχ'.w a
      simp only [types_comp_apply] at hw
      rw [hw]
      exact trivial
  exact congrArg ULift.up (propext hiff)
```

Notes for the implementer:

- The two `congrArg ULift.up` steps rely on definitional
  structure eta: `ULift.up ((χ' x).down)` is definitionally
  `χ' x`, so the produced equalities have the stated types. If
  either is rejected, replace with `ULift.ext`-based forms
  (verify the exact `ULift.ext` signature with
  `lean_local_search` first).
- Forward direction: `Types.exists_of_isPullback hχ' x
  PUnit.unit hx : ∃ a, m a = x ∧
  typesIsTerminalPUnit.from U a = PUnit.unit` — the second
  component is discarded with `-`.
- Backward direction: `hχ'.w : m ≫ χ' =
  typesIsTerminalPUnit.from U ≫ typesTruth`; evaluated at
  `a` and reduced, it rewrites the goal `(χ' (m a)).down` to
  `(typesTruth _).down`, which is definitionally `True`. If
  `exact trivial` is rejected, insert `show True` first.

- [ ] **Step 2: Build**

```bash
lake build
```

Expected: success.

- [ ] **Step 3: Verify axioms**

`lean_verify` on `GebLean.typesCharMap_unique`: subset of
{`propext`, `Quot.sound`, `Classical.choice`}.

- [ ] **Step 4: Pre-commit checks and commit**

```bash
bash scripts/pre-commit.sh
```

Then:

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "feat(types-classifier): prove uniqueness of typesCharMap"
jj bookmark set feat/types-classifier -r @-
cd /home/terence/git-workspaces/geb/geb-lean
```

## Task 4: `typesClassifier` and the `HasClassifier` instance

**Files:**

- Modify: `GebLean/Utilities/TypesClassifier.lean` (add one
  def and one instance before `end GebLean`)

Spec reference: §5.1 (assembly), §7.

- [ ] **Step 1: Add the classifier and instance**

Insert before `end GebLean`:

```lean
/-- `ULift Prop` is a subobject classifier for `Type u`.
Impredicativity of `Prop` provides the propositional resizing
hypothesized by [UF13] Theorem 10.1.12, and `propext` provides
univalence restricted to propositions. -/
def typesClassifier : Classifier (Type u) :=
  Classifier.mkOfTerminalΩ₀
    PUnit.{u + 1}
    typesIsTerminalPUnit
    (ULift.{u} Prop)
    typesTruth
    (χ := fun m _ => typesCharMap m)
    (isPullback := fun m _ => typesCharMap_isPullback m)
    (uniq := fun m _ χ' hχ' => typesCharMap_unique m χ' hχ')

/-- `Type u` has a subobject classifier. -/
instance typesHasClassifier : HasClassifier (Type u) :=
  ⟨⟨typesClassifier⟩⟩
```

Notes for the implementer:

- The named-argument style with an anonymous `Mono` binder
  (`fun m _ => …`) mirrors `pshClassifierData` in
  `GebLean/Utilities/Presheaf.lean`; the anonymous hypothesis
  of class type is picked up by instance resolution inside
  each body.
- `mkOfTerminalΩ₀` derives `mono_truth` via
  `IsTerminal.mono_from`; no separate lemma is needed.
- The result must be a plain `def` — if Lean demands
  `noncomputable`, a data-position dependency is
  noncomputable, which is a defect to fix (spec §10), not to
  mask with the keyword.

- [ ] **Step 2: Build**

```bash
lake build
```

Expected: success, with no `noncomputable` anywhere in the
module.

- [ ] **Step 3: Verify axioms and data transparency**

- `lean_verify` on `GebLean.typesClassifier` and
  `GebLean.typesHasClassifier`: subset of
  {`propext`, `Quot.sound`, `Classical.choice`}.
- Spot-check (scratch, deleted before commit):

```lean
example : (typesClassifier : Classifier (Type u)).Ω =
    ULift.{u} Prop := rfl
example : (typesClassifier : Classifier (Type u)).truth =
    typesTruth.{u} := rfl
```

Both must close by `rfl` (these recur as committed tests in
Task 6).

- [ ] **Step 4: Pre-commit checks and commit**

```bash
bash scripts/pre-commit.sh
```

Then:

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "feat(types-classifier): assemble Classifier (Type u) via ULift Prop"
jj bookmark set feat/types-classifier -r @-
cd /home/terence/git-workspaces/geb/geb-lean
```

## Task 5: Comparison with the presheaf classifier

**Files:**

- Modify: `GebLean/Utilities/TypesClassifier.lean` (add one
  import, extend the module docstring, add one def and one
  theorem before `end GebLean`)

Spec reference: §5.2, §6 (comparison proof shapes).

- [ ] **Step 1: Add the Presheaf import**

Change the import block to:

```lean
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Topos.Classifier
import GebLean.Utilities.Presheaf
```

(`GebLean.Utilities.Presheaf` supplies `pshTerminal`,
`pshSieveFunctor`, and `pshSieveTruth`.)

- [ ] **Step 2: Extend the module docstring**

In the module docstring, append to the `## Main definitions`
list:

```text
- `GebLean.sievePUnitEquiv`, `GebLean.sievePUnitEquiv_truth`:
  comparison with the presheaf classifier of
  `GebLean.Utilities.Presheaf` over the terminal category.
```

- [ ] **Step 3: Add the comparison declarations**

Insert before `end GebLean`:

```lean
/-- A sieve on an object of the terminal category is
determined by whether it contains the identity. This compares
the presheaf classifying object `pshSieveFunctor` at the
terminal category with the `Type u` classifying object
`ULift Prop`. -/
def sievePUnitEquiv (c : Discrete PUnit.{u + 1}) :
    Sieve c ≃ ULift.{u} Prop where
  toFun S := ULift.up (S.arrows (𝟙 c))
  invFun p :=
    { arrows := fun _ _ => p.down
      downward_closed := fun h _ => h }
  left_inv S := by
    obtain ⟨⟨⟩⟩ := c
    ext Y f
    obtain ⟨⟨⟩⟩ := Y
    rw [Subsingleton.elim f (𝟙 _)]
  right_inv p := rfl

/-- The presheaf truth morphism (the maximal sieve at each
stage) corresponds to `typesTruth` under `sievePUnitEquiv`. -/
theorem sievePUnitEquiv_truth
    (c : (Discrete PUnit.{u + 1})ᵒᵖ)
    (x : (pshTerminal (Discrete PUnit.{u + 1})).obj c) :
    sievePUnitEquiv c.unop
      ((pshSieveTruth (Discrete PUnit.{u + 1})).app c x) =
      typesTruth PUnit.unit :=
  congrArg ULift.up (eq_true (Sieve.top_apply _))
```

Notes for the implementer:

- `left_inv`: the two `obtain ⟨⟨⟩⟩` steps destruct
  `Discrete PUnit` objects to the canonical
  `{ as := PUnit.unit }`, after which `f` and `𝟙 _` inhabit
  the same hom-set; `Discrete` hom-sets are subsingletons, so
  `Subsingleton.elim` rewrites `f` to the identity and `rw`
  closes the resulting reflexive iff. This is the
  object-equality transport the spec's §6 names as the
  expected largest step. If `ext Y f` does not produce the
  per-arrow iff (verify `Sieve.ext`'s exact form with
  `lean_local_search`), apply `Sieve.ext` explicitly:
  `apply Sieve.ext; intro Y f`.
- `right_inv p := rfl` relies on `ULift` structure eta.
- `sievePUnitEquiv_truth`: `pshSieveTruth` selects
  `(⊤ : Sieve _)`, and `Sieve.top_apply _` proves membership
  of the identity. Verify the name `Sieve.top_apply` with
  `lean_local_search`; if it differs, `trivial` after
  unfolding `Sieve` top, or `by simp [sievePUnitEquiv,
  pshSieveTruth, typesTruth]`, are the fallbacks.

- [ ] **Step 4: Build**

```bash
lake build
```

Expected: success.

- [ ] **Step 5: Verify axioms**

`lean_verify`:

- `GebLean.sievePUnitEquiv`: subset of
  {`propext`, `Quot.sound`, `Classical.choice`} (the
  round-trip fields are `Prop`-valued; the data fields remain
  computable — confirm no `noncomputable` was needed).
- `GebLean.sievePUnitEquiv_truth`: subset of the same set.

- [ ] **Step 6: Pre-commit checks and commit**

```bash
bash scripts/pre-commit.sh
```

Then:

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "feat(types-classifier): compare with presheaf classifier at the point"
jj bookmark set feat/types-classifier -r @-
cd /home/terence/git-workspaces/geb/geb-lean
```

## Task 6: Tests

**Files:**

- Create: `GebLeanTests/Utilities/TypesClassifier.lean`
- Modify: `GebLeanTests.lean` (one import line)

Spec reference: §8.

- [ ] **Step 1: Create the test module**

Create `GebLeanTests/Utilities/TypesClassifier.lean` with
exactly this content:

```lean
import GebLean.Utilities.TypesClassifier

/-!
# Tests for `GebLean.Utilities.TypesClassifier`
-/

open CategoryTheory
open GebLean

universe u

-- `typesCharMap` of the even-naturals inclusion holds at a
-- member.
example :
    typesCharMap
      (Subtype.val : {n : Nat // n % 2 = 0} → Nat) 4 =
      ULift.up True :=
  typesCharMap_apply_eq_true _
    (⟨4, rfl⟩ : {n : Nat // n % 2 = 0})

-- ... and fails at a non-member.
example :
    typesCharMap
      (Subtype.val : {n : Nat // n % 2 = 0} → Nat) 3 =
      ULift.up False :=
  congrArg ULift.up (propext (iff_false_intro
    fun ⟨a, ha⟩ => Nat.one_ne_zero (by
      have hp := a.property
      rw [ha] at hp
      exact hp)))

-- `mkOfTerminalΩ₀` does not obscure the classifier data.
example : (typesClassifier : Classifier (Type u)).Ω =
    ULift.{u} Prop := rfl

example : (typesClassifier : Classifier (Type u)).truth =
    typesTruth.{u} := rfl

-- `sievePUnitEquiv` round trips on the extreme sieves.
example :
    (sievePUnitEquiv (Discrete.mk PUnit.unit)).symm
      (sievePUnitEquiv (Discrete.mk PUnit.unit) ⊤) = ⊤ :=
  (sievePUnitEquiv _).symm_apply_apply ⊤

example :
    (sievePUnitEquiv (Discrete.mk PUnit.unit)).symm
      (sievePUnitEquiv (Discrete.mk PUnit.unit) ⊥) = ⊥ :=
  (sievePUnitEquiv _).symm_apply_apply ⊥
```

Notes for the implementer:

- No `#guard` anywhere: the classifier's values are `Prop`s
  and are not kernel-reducible test subjects (spec §8).
- The member example's witness carries a type ascription
  because the morphism hole `_` leaves the subtype
  undetermined when the anonymous constructor elaborates;
  naming the morphism instead
  (`typesCharMap_apply_eq_true Subtype.val …`) does not work
  (the predicate is then inferred from the witness).
- The non-member proof: `ha : a.val = 3` and
  `a.property : a.val % 2 = 0` combine (by rewriting `ha`
  into `a.property`) to a proof of `3 % 2 = 0`, which is
  definitionally `1 = 0`, refuted by `Nat.one_ne_zero`. The
  rewrite runs in a `by` block because `▸` cannot infer the
  motive here.

- [ ] **Step 2: Wire the test module into the test index**

In `GebLeanTests.lean`, insert

```lean
import GebLeanTests.Utilities.TypesClassifier
```

immediately after the existing line
`import GebLeanTests.Utilities.SimRec` (the last
`GebLeanTests.Utilities.*` import as of the baseline; the
block is not alphabetized).

- [ ] **Step 3: Run the tests**

```bash
lake test
```

Expected: success.

- [ ] **Step 4: Pre-commit checks and commit**

```bash
bash scripts/pre-commit.sh
```

Then:

```bash
cd /home/terence/git-workspaces/geb
jj commit -m "test(types-classifier): add classifier evaluation and round-trip tests"
jj bookmark set feat/types-classifier -r @-
cd /home/terence/git-workspaces/geb/geb-lean
```

## Task 7: Axiom audit and final verification

**Files:** none modified (verification only; fixes, if any,
are separate commits).

- [ ] **Step 1: Run the repository axiom gate**

```bash
bash scripts/check-axioms.sh
```

Expected: passes (accepts `propext`, `Quot.sound`,
`Classical.choice`; rejects `sorryAx` and any non-standard
axiom).

- [ ] **Step 2: Confirm no `noncomputable` and no `sorry`/`admit`**

```bash
grep -n "noncomputable\|sorry\|admit" \
  GebLean/Utilities/TypesClassifier.lean \
  GebLeanTests/Utilities/TypesClassifier.lean
```

Expected: the only permitted match is the word `noncomputable`
inside the `typesIsTerminalPUnit` docstring (which describes
mathlib's variant); no code occurrences.

- [ ] **Step 3: Full build, test, lint**

```bash
lake build && lake test && lake lint
```

Expected: all pass.

- [ ] **Step 4: Confirm the branch state**

```bash
cd /home/terence/git-workspaces/geb && jj st && jj log -r 'feat/types-classifier::@' --no-pager
```

Expected: clean working copy; the topic branch contains the
spec, plan, and review commits plus the six implementation
commits from Tasks 1–6 (five `feat`, one `test`).

## Post-implementation

- Holistic code-quality review over the full diff (project
  convention; separate session step).
- Branch finishing (PR to `origin/main`) is user-gated: no
  `jj git push` without user line-by-line review; PR title and
  body are user-authored.
