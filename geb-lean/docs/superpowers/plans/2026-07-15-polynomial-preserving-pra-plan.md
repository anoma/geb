# Polynomial-preserving presheaf PRAs implementation plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Global constraints](#global-constraints)
- [Standing decisions recorded by this plan](#standing-decisions-recorded-by-this-plan)
- [Consumed interfaces (verbatim, current pin)](#consumed-interfaces-verbatim-current-pin)
- [File structure](#file-structure)
- [Execution notes](#execution-notes)
  - [Task 1: bundled inclusion `fcEvalCatFunctor` and full faithfulness](#task-1-bundled-inclusion-fcevalcatfunctor-and-full-faithfulness)
  - [Task 2: `fcMap` — the action of `FC` on functors](#task-2-fcmap--the-action-of-fc-on-functors)
  - [Task 3: elements of positions — `FCElem`, its projection, and `elMap`](#task-3-elements-of-positions--fcelem-its-projection-and-elmap)
  - [Task 4: multiadjunction witnesses](#task-4-multiadjunction-witnesses)
  - [Task 5: the formula categories](#task-5-the-formula-categories)
  - [Task 6: spectrum and value functors](#task-6-spectrum-and-value-functors)
  - [Task 7: the comparison functor](#task-7-the-comparison-functor)
  - [Task 8: G2 — full faithfulness of the comparison](#task-8-g2--full-faithfulness-of-the-comparison)
  - [Task 9: G3 — extension to presheaf categories](#task-9-g3--extension-to-presheaf-categories)
  - [Task 10: G4 — the restriction isomorphism](#task-10-g4--the-restriction-isomorphism)
  - [Task 11: G5 — faithfulness into the presheaf functor category](#task-11-g5--faithfulness-into-the-presheaf-functor-category)
  - [Task 12: FCP instantiation](#task-12-fcp-instantiation)
  - [Task 13: instance tests — `Poly` and the identity](#task-13-instance-tests--poly-and-the-identity)
- [Self-review checklist (run before adversarial review)](#self-review-checklist-run-before-adversarial-review)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking. User review of
> this plan precedes any execution.

**Goal:** Implement the converged spec
`docs/superpowers/specs/2026-07-14-polynomial-preserving-pra-design.md`:
the formula category of polynomial-preserving presheaf PRAs
(positions `T1 ∈ FC(D)`, directions `E : el(T1) ⥤ FC(C)`,
multiadjunction witnesses), its value functor
`T = FC(p) ∘ M`, the comparison functors, theorems G2–G5, and the
FCP instantiation.

**Architecture:** Higher-order construction where the existing
machinery applies: the bundled inclusion `FC(C) ⥤ PSh(C)` and the
action of `FC` on functors are built once in `Utilities`; the
formula categories are presented directly by the spec's § 6.2
tower (positions, directions, witnesses), the witness layer an
`InducedCategory` over the witness-free category, making the
forgetful functor fully faithful by construction; the existing
`coprodCovarRepFunctor` / `ccrPresheafCatFunctor` machinery enters
through Task 9's conversion functor into the unrestricted formula
category, with only the elements unpacking of positions written
directly (standing decision 1). All witnesses (multiadjunction
data, factorization assignments) are structure fields, never `∃`.

**Tech Stack:** Lean 4 (current toolchain pin), Lake, mathlib
category theory (`Functor.FullyFaithful`, `InducedCategory`,
`Grothendieck`), the in-repository `Families.lean` /
`PresheafPRA.lean` stacks, `jj`, `markdownlint-cli2`, `doctoc`.

## Global constraints

- No `noncomputable` anywhere; `Classical.choice` accepted in
  proofs only (`CLAUDE.md` § Constructive-only Lean code).
- Axiom gate: `lake build GebLeanAxiomChecks` passes after every
  task.
- Pre-commit Lean triad before every `.lean`-touching commit:
  `bash scripts/pre-commit.sh`.
- `sorry` only transiently inside a task, never committed; `admit`
  never; placeholders are underscores.
- mathlib style, module docstrings with required sections,
  declaration docstrings for every `def`/`structure`/major theorem;
  literature citations in module docstrings' `## References`
  (spec's References section supplies them).
- Universe discipline per spec § 10 item 4: `FP` raises the object
  universe; the `familyNatTrans'` machinery requires shared
  universe pairs; mediate with `catULiftFunctor2` where required
  (as `PresheafPRA.lean` already does). Each task's "Interfaces —
  Produces" block states its universe parameters explicitly, and
  the `ULift` / `catULiftFunctor2` / `uliftFunctor` mediation
  points are identified in Tasks 9, 10, and 12; if a stated
  signature fails universe unification, the executor widens with
  `ULift` mediation rather than weakening the interface, and
  records the deviation for review.
- Commit messages: mathlib convention, imperative, lowercase
  subject, no trailing period; each message ends with the
  repository trailer
  `Co-Authored-By: Claude Fable 5 <noreply@anthropic.com>`
  (the repository git convention);
  commit via `jj commit`.
- One definition at a time; factor helpers into
  `GebLean/Utilities/`.

## Standing decisions recorded by this plan

1. **Spec § 8 deliverable 2 reconciliation (review r1 B1).** The
   `⟨T1, E⟩` structure presentation is the unconditional interface
   of `FCDirPRACat`; Tasks 6–8 consume its accessors directly. The
   higher-order `coprodCovarRepFunctor` / `ccrPresheafCatFunctor`
   machinery has a definite, unconditional role: Task 9's
   conversion functor `fcDirToCCR` into the `FC(C)`-directed CCR
   presentation (elements unpacking on positions; directions the
   direct `P.E.obj` assignment), followed by the
   `coprodCovarRepFunctor.map` whiskering along Task 1's
   inclusion (with `catULiftFunctor2` mediation) — that composite
   with the existing `PresheafPRACat`-side machinery is
   `polyPRAExtend`. The spec's
   § 8 deliverable 2 is amended on this branch to match this
   presentation (direct § 6.2 formula datum plus conversion functor built
   from the existing machinery).
2. **Restriction vocabulary (spec § 10 item 3 / O3).** Resolved as
   the specified-NatIso square: G4 is stated as a `NatIso` between
   the two named composites `FC(C) ⥤ PSh(D)` (Task 10).
   `ObjectProperty.lift`-style lifting is not used.
3. **Elements category (review r1 A5).** The bespoke `FCElem` is
   kept: its flat fields give definitional access to the
   `fcIndex` / `fcFamily` components that Tasks 4–10 consume
   directly, whereas `Functor.ElementsContra` /
   `Functor.ElementsContra'` (`GebLean/Utilities/Elements.lean`,
   stated over `ᵒᵖ'`-presheaves) and mathlib's `Functor.Elements`
   (opposite orientation) would wrap those components in `Σ`-pairs
   and `op`s at every use site. The existing abstractions are
   recorded here as considered and not instantiated.

## Consumed interfaces (verbatim, current pin)

From `GebLean/Utilities/Families.lean`:

- `FreeCoprodCompletionCat.{u', v', w'} (C' : Type u')
  [Category.{v'} C'] : Cat` (below `FC`), with helpers `fcObjMk`,
  `fcIndex`, `fcFamily`, `fcHomMk`, `fcReindex`, `fcFiberMor`,
  `fcHom_ext`, `fcId_mk`, `fcComp_mk`.
- `fcEval (P : FreeCoprodCompletionCat C) (A : C) : Type _` `=`
  `Σ i : fcIndex P, (A ⟶ fcFamily P i)`, with `fcEvalMk`,
  `fcEvalIndex`, `fcEvalMor`, `fcEvalMap`, `fcEval_ext`,
  `fcToFunctor (P) : Cᵒᵖ ⥤ Type _` (per-object presheaf).
- `FreeProdCompletionCat`, `FreeCoprodProdCat.{u', v', w₁', w₂'}`,
  `CoprodCovarRepSquaredCat`, `fcpCcrsIso`, `fcpCcrsEquiv`.
- `CoprodCovarRepCat`, `coprodCovarRepFunctor`,
  `ccrNewEvalCatFunctor`, `ccrNewEvalCatFullyFaithful` (the
  covariant analogue and model for Task 1).
- `familyFunctor'`, `familyNatTrans'`, `familyPostcomp'`.

From `GebLean/Utilities/Grothendieck.lean`:

- `GrothendieckContra'` (`:1567`).

From `GebLean/PresheafPRA.lean`:

- `presheafCatFunctor`, `PresheafPRACat` (`Jᵒᵖ ⥤
  CoprodCovarRepCat (Iᵒᵖ ⥤ Type w_I)`), `ccrPresheafCatFunctor`,
  `catULiftFunctor2`, `praEvalAt*` accessors.
- `praEvalAtFunctor :
  PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J ⥤
  (Iᵒᵖ ⥤ Type w_I) ⥤ (Jᵒᵖ ⥤ Type (max w' u_I w_I))`
  (`GebLean/PresheafPRA.lean:1387`).
- `praEvalAtFunctorFullyFaithful :
  (praEvalAtFunctor I J).FullyFaithful`
  (`GebLean/PresheafPRA.lean:1423`).

From `GebLean/Utilities/Elements.lean` (consulted, not
instantiated — standing decision 3):

- `Functor.ElementsContra'` (`:397`), `sliceEquivPresheaf`
  (`:413`), `Functor.ElementsContra` (`:423`).

## File structure

- Task 1 creates `GebLean/Utilities/FCEval.lean` (Tasks 1–2:
  bundled inclusion, full faithfulness, `fcMap`), the index file
  `GebLean/PolyPRA.lean` (initial content:
  `import GebLean.Utilities.FCEval`), and
  `GebLeanTests/PolyPRA/Basic.lean`, and registers both roots in
  the same commit: the line `import GebLean.PolyPRA` is added to
  `GebLean.lean` and the line
  `import GebLeanTests.PolyPRA.Basic` is added to
  `GebLeanTests.lean`. `lakefile.toml` declares no `globs` for
  either library, so only modules reachable from these roots are
  built; registration at file creation keeps every per-task
  `lake build` / `lake test` / pre-commit / axiom gate
  non-vacuous.
- Create `GebLean/PolyPRA/Elements.lean` — Task 3 (`FCElem`,
  projection, `elMap`, `fcElTerminalHom`).
- Create `GebLean/PolyPRA/Multiadjunction.lean` — Task 4 (witness
  structure).
- Create `GebLean/PolyPRA/Cat.lean` — Task 5 (witness-free and
  witnessed formula categories).
- Create `GebLean/PolyPRA/Value.lean` — Task 6 (spectrum and value
  functors).
- Create `GebLean/PolyPRA/Comparison.lean` — Tasks 7–8 (comparison
  functor, G2).
- Create `GebLean/PolyPRA/Extension.lean` — Tasks 9–11 (G3, G4,
  G5).
- Create `GebLean/PolyPRA/FCP.lean` — Task 12 (FCP instantiation).
- Every task that creates a `GebLean/PolyPRA/<Name>.lean` module
  appends the line `import GebLean.PolyPRA.<Name>` to
  `GebLean/PolyPRA.lean` in the same commit that creates the
  file. Deviation from `.claude/rules/lean-coding.md` § Lean 4
  module system, recorded per review r2: at this pin, `public
  import` requires the importing file to declare `module`, and a
  `module` file cannot import the existing non-`module`
  `GebLean` tree, so plain `import` is used (matching the
  `GebLean/Binding.lean` index precedent); correcting the rule
  is a separate branch per the one-concern rule.
- `GebLeanTests/PolyPRA/Basic.lean` receives each task's test
  declarations and Task 13 (registered in `GebLeanTests.lean` by
  Task 1).

Topic branch: continue `feat/poly-preserving-pra`.

## Execution notes

- Every task follows the same step template; it is spelled out in
  Task 1 and referenced afterwards ("standard step cycle") with the
  task's own declarations, tests, and commit message substituted.
  The cycle is: (1) write the declarations with `_` placeholders
  for proofs (for a module-creating task, also add the
  registration line stated in File structure); (2) `lake build`
  and inspect the goals; (3) fill proofs one declaration at a
  time; (4) add the task's test declarations (the task's "Test"
  contract) under `GebLeanTests/PolyPRA/Basic.lean`; (5) run
  `lake test`; (6) run `bash scripts/pre-commit.sh`; (7) `jj
  commit` with the task's message.
- Proof strategies below cite the spec section that validates the
  statement informally; the executor follows
  `.claude/rules/lean-coding.md` (factoring-out-lemmas,
  one-step-at-a-time) when a strategy stalls, and the
  stuck-and-ask template rather than weakening an interface.
- Universe variables: `C : Type u_C` `[Category.{v_C} C]`,
  `D : Type u_D` `[Category.{v_D} D]`, index universe `w`
  throughout; concrete `max`-expressions are fixed by the executor
  at declaration time under the Global-constraints rule.

### Task 1: bundled inclusion `fcEvalCatFunctor` and full faithfulness

**Files:** Create `GebLean/Utilities/FCEval.lean`,
`GebLean/PolyPRA.lean` (index; initial content
`import GebLean.Utilities.FCEval`), and
`GebLeanTests/PolyPRA/Basic.lean`; add `import GebLean.PolyPRA` to
`GebLean.lean` and `import GebLeanTests.PolyPRA.Basic` to
`GebLeanTests.lean` (File structure).

**Interfaces — Produces** (universes `u_C v_C w`):

```lean
def fcEvalCatFunctor (C : Type u_C) [Category.{v_C} C] :
    FreeCoprodCompletionCat.{u_C, v_C, w} C ⥤
      (Cᵒᵖ ⥤ Type (max w v_C))

def fcEvalCatFullyFaithful (C : Type u_C) [Category.{v_C} C] :
    (fcEvalCatFunctor.{u_C, v_C, w} C).FullyFaithful
```

with `@[simp]` lemmas `fcEvalCatFunctor_obj` (agreement with
`fcToFunctor` up to the universe lift chosen) and
`fcEvalCatFunctor_map_app`.

**Strategy:** transcribe `ccrNewEvalCatFunctor` /
`ccrNewEvalCatFullyFaithful` (same file pattern, contravariant
variance); the preimage of a natural transformation evaluates at
the Yoneda elements `fcEvalMk i (𝟙 _)`; full faithfulness is
Dorta–Jarvis–Niu Proposition 2.4; the hom-set computation is the
distributivity `Π_b Σ_x Hom(G b, F x) ≅ Σ_r Π_b Hom(G b, F(r b))`
(spec § 7 G3; the Set instance of Dorta–Jarvis–Niu
Proposition 2.5, with their Proposition 2.7 the hom-set formula),
which is a `Sigma`/`Pi` `Equiv` in Lean, choice-free.

- [ ] **Step 1:** create the files and registration lines per File
  structure; module docstring for `FCEval.lean` (`## References`:
  Dorta–Jarvis–Niu arXiv:2305.05655 Proposition 2.4 (full
  faithfulness of the inclusion) and Propositions 2.5/2.7
  (distributivity / hom-set formula); spec §§ 2 and 7) and the two
  declarations with `_` proof placeholders.
- [ ] **Step 2:** `lake build` — inspect goals.
- [ ] **Step 3:** prove `fcEvalCatFunctor` functor laws (pointwise,
  via `fcEvalMap_id` / `fcEvalMap_comp`).
- [ ] **Step 4:** prove `fcEvalCatFullyFaithful` (preimage via
  Yoneda elements; `map_preimage` by naturality at
  `fcEvalMk i (𝟙 _)`; `preimage_map` by `fcHom_ext`).
- [ ] **Step 5:** add tests: for `C = Discrete PUnit` and a
  two-element family, compute `fcEval` of the image and `#guard`
  -style decidable checks or `example`-level `rfl` isomorphisms;
  name the two-element family as a `def` for reuse (Tasks 2–3
  tests).
- [ ] **Step 6:** `lake test`; `bash scripts/pre-commit.sh`.
- [ ] **Step 7:** `jj commit -m "feat(polypra): add the bundled
  free-coproduct-completion inclusion"`.

### Task 2: `fcMap` — the action of `FC` on functors

**Files:** Modify `GebLean/Utilities/FCEval.lean`; tests in
`GebLeanTests/PolyPRA/Basic.lean`.

**Interfaces — Produces** (universes `u_A v_A u_B v_B w`):

```lean
def fcMap {A : Type u_A} [Category.{v_A} A] {B : Type u_B}
    [Category.{v_B} B] (p : A ⥤ B) :
    FreeCoprodCompletionCat.{u_A, v_A, w} A ⥤
      FreeCoprodCompletionCat.{u_B, v_B, w} B

@[simp] lemma fcMap_obj_index ...  -- index preserved
@[simp] lemma fcMap_obj_family ... -- family = p ∘ family
@[simp] lemma fcMap_map_reindex ... -- fcReindex preserved
@[simp] lemma fcMap_map_fiberMor ... -- fiber morphism = p.map _
@[simp] lemma fcMap_map_mk ...
  -- (fcMap p).map (fcHomMk r φ) = fcHomMk r (p.map ∘ φ)
lemma fcMap_id : fcMap (𝟭 A) = 𝟭 _
lemma fcMap_comp : fcMap (p ⋙ q) = fcMap p ⋙ fcMap q
```

The pointwise `@[simp]` lemmas (`fcMap_map_reindex`,
`fcMap_map_fiberMor`, `fcMap_map_mk`) are what Tasks 6/10 rewrite
with under `fcMap (fcElProj P.T1) |>.map` occurrences; the functor
equalities `fcMap_id` / `fcMap_comp` are the functoriality record
(rewriting with them through dependent `.map` occurrences would
require `eqToHom` transport).

**Strategy:** object part `fcObjMk (p.obj ∘ fcFamily P)`; morphism
part keeps `fcReindex` and post-composes `p.map` on `fcFiberMor`;
laws by `fcHom_ext`. Construct through `GrothendieckContra'` /
`familyPostcomp'` machinery where universe constraints permit
(Global constraints); otherwise direct with the `fc*` helpers.

**Test:** `fcMap` of the Task 1 named two-element family along the
identity `Discrete PUnit ⥤ Discrete PUnit`, checking index
preservation by `rfl`; return the image object as a `def` for
reuse.

- [ ] Standard step cycle; commit message
  `feat(polypra): add the functorial action of FC on functors`.

### Task 3: elements of positions — `FCElem`, its projection, and `elMap`

**Files:** Create `GebLean/PolyPRA/Elements.lean`; append
`import GebLean.PolyPRA.Elements` to `GebLean/PolyPRA.lean`;
tests in `GebLeanTests/PolyPRA/Basic.lean`.

**Interfaces — Produces** (universes `u_D v_D w`):

```lean
structure FCElem {D : Type u_D} [Category.{v_D} D]
    (P : FreeCoprodCompletionCat.{u_D, v_D, w} D) :
    Type (max u_D v_D w) where
  pt : D
  idx : fcIndex P
  hom : pt ⟶ fcFamily P idx

instance : Category.{v_D} (FCElem P)
  -- morphisms: v : pt ⟶ pt' with idx = idx' and hom = v ≫ hom'

def fcElProj (P : FreeCoprodCompletionCat.{u_D, v_D, w} D) :
    FCElem P ⥤ D

def elMap {T1 T1' : FreeCoprodCompletionCat.{u_D, v_D, w} D}
    (α : T1 ⟶ T1') : FCElem T1 ⥤ FCElem T1'
@[simp] lemma elMap_obj_pt ...   -- pt preserved
@[simp] lemma elMap_obj_idx ...  -- idx = fcReindex α _
@[simp] lemma elMap_map_hom ...  -- underlying D-morphism preserved
lemma elMap_id (T1 : FreeCoprodCompletionCat.{u_D, v_D, w} D) :
    elMap (𝟙 T1) = 𝟭 (FCElem T1)
lemma elMap_comp
    {T1 T1' T1'' : FreeCoprodCompletionCat.{u_D, v_D, w} D}
    (α : T1 ⟶ T1') (α' : T1' ⟶ T1'') :
    elMap (α ≫ α') = elMap α ⋙ elMap α'
```

with `@[ext]` on `FCElem`-morphisms and `@[simp]` projection
lemmas. Orientation: a morphism `e ⟶ e'` lies over `v : e.pt ⟶
e'.pt` with `e.hom = v ≫ e'.hom` and `e.idx = e'.idx` (spec § 6's
elements orientation; the existing elements abstractions are
considered and not instantiated per standing decision 3 — record
the comparison as a lemma only if a later task needs it, YAGNI).
`elMap α` sends `⟨pt, idx, hom⟩` to
`⟨pt, fcReindex α idx, hom ≫ fcFiberMor α idx⟩`; it is consumed
unconditionally by Tasks 5 (morphism layer), 7 (comparison
components), and 8 (recovery).

**Strategy:** direct structure; the slice decomposition
`FCElem P ≅ Σ_s D/k_s` is *not* a deliverable (the later tasks
consume `FCElem` directly); the terminal-per-index objects
`⟨fcFamily P i, i, 𝟙 _⟩` are, with a lemma `fcElTerminalHom`
giving the unique factorization of any element through them —
this is the slice-terminality of the spec's § 6.2 in element
form.

**Test:** `fcElTerminalHom`'s factorization on the Task 1 named
two-element family (`example`-level `rfl` on the factoring
morphism's components); return the terminal-per-index element as
a `def` for reuse.

- [ ] Standard step cycle; commit message
  `feat(polypra): add the elements category of polynomial positions`.

### Task 4: multiadjunction witnesses

**Files:** Create `GebLean/PolyPRA/Multiadjunction.lean`; append
`import GebLean.PolyPRA.Multiadjunction` to
`GebLean/PolyPRA.lean`; tests in `GebLeanTests/PolyPRA/Basic.lean`.

**Interfaces — Produces** (universes `u_C v_C u_D v_D w`):

```lean
structure MultiadjunctionWitnesses
    {C : Type u_C} [Category.{v_C} C]
    {D : Type u_D} [Category.{v_D} D]
    {T1 : FreeCoprodCompletionCat.{u_D, v_D, w} D}
    (E : FCElem T1 ⥤ FreeCoprodCompletionCat.{u_C, v_C, w} C) where
  spec : ∀ Z : FreeCoprodCompletionCat.{u_C, v_C, w} C,
    FreeCoprodCompletionCat.{max u_D v_D w, v_D, w}
      (FCElem T1)                                -- M(Z)
  counit : ∀ (Z : FreeCoprodCompletionCat.{u_C, v_C, w} C)
    (ρ : fcIndex (spec Z)),
    E.obj (fcFamily (spec Z) ρ) ⟶ Z              -- ε_ρ
  factor : ∀ (Z : FreeCoprodCompletionCat.{u_C, v_C, w} C)
    (u : FCElem T1), (E.obj u ⟶ Z) →
    Σ ρ : fcIndex (spec Z), (u ⟶ fcFamily (spec Z) ρ)
  factor_spec : ∀ (Z : FreeCoprodCompletionCat.{u_C, v_C, w} C)
    (u : FCElem T1) (φ : E.obj u ⟶ Z),
    E.map (factor Z u φ).2 ≫ counit Z (factor Z u φ).1 = φ
  factor_unique : ∀ (Z : FreeCoprodCompletionCat.{u_C, v_C, w} C)
    (u : FCElem T1) (φ : E.obj u ⟶ Z)
    (ρ : fcIndex (spec Z)) (v : u ⟶ fcFamily (spec Z) ρ),
    E.map v ≫ counit Z ρ = φ →
    (⟨ρ, v⟩ : Σ ρ : fcIndex (spec Z),
      (u ⟶ fcFamily (spec Z) ρ)) = factor Z u φ
```

(`factor` is data; `factor_spec` / `factor_unique` are the
Prop-valued fields — spec § 6.2 as amended by review r1 F4.)
Derived lemma: `factor_counit : factor Z _ (counit Z ρ) = ⟨ρ, 𝟙 _⟩`
(uniqueness applied to the identity factorization; spec § 6.4's
identity law seed).

**Test:** build the identity-instance witness seed over
`C = D = Discrete PUnit` (`T1` a named two-index family, `E` the
evident functor of Task 13 (b)) as a `def`, and check
`factor_counit` on it by an `example`-level `rfl`; return the
witness for reuse (Tasks 5, 6, 13).

- [ ] Standard step cycle; commit message
  `feat(polypra): add the multiadjunction witness structure`.

### Task 5: the formula categories

**Files:** Create `GebLean/PolyPRA/Cat.lean`; append
`import GebLean.PolyPRA.Cat` to `GebLean/PolyPRA.lean`;
tests in `GebLeanTests/PolyPRA/Basic.lean`.

**Interfaces — Produces** (universes `u_C v_C u_D v_D w`):

```lean
structure FCDirPRACat (C : Type u_C) [Category.{v_C} C]
    (D : Type u_D) [Category.{v_D} D] :
    Type (max u_C u_D v_C v_D (w + 1)) where
  T1 : FreeCoprodCompletionCat.{u_D, v_D, w} D
  E : FCElem T1 ⥤ FreeCoprodCompletionCat.{u_C, v_C, w} C

instance : Category (FCDirPRACat C D)
  -- morphisms (α : P.T1 ⟶ P'.T1, β : elMap α ⋙ P'.E ⟶ P.E)
  -- per spec § 6.3, with whiskered composition

structure PolyPRAObj (C : Type u_C) [Category.{v_C} C]
    (D : Type u_D) [Category.{v_D} D] :
    Type (max u_C u_D v_C v_D (w + 1)) where
  T1 : FreeCoprodCompletionCat.{u_D, v_D, w} D
  E : FCElem T1 ⥤ FreeCoprodCompletionCat.{u_C, v_C, w} C
  witness : MultiadjunctionWitnesses E

def PolyPRAObj.forget
    (P : PolyPRAObj.{u_C, v_C, u_D, v_D, w} C D) :
    FCDirPRACat.{u_C, v_C, u_D, v_D, w} C D  -- ⟨P.T1, P.E⟩

def PolyPRACat (C : Type u_C) [Category.{v_C} C]
    (D : Type u_D) [Category.{v_D} D] :
    Type (max u_C u_D v_C v_D (w + 1)) :=
  InducedCategory (D := FCDirPRACat.{u_C, v_C, u_D, v_D, w} C D)
    PolyPRAObj.forget

def polyPRAForget (C : Type u_C) [Category.{v_C} C]
    (D : Type u_D) [Category.{v_D} D] :
    PolyPRACat.{u_C, v_C, u_D, v_D, w} C D ⥤
      FCDirPRACat.{u_C, v_C, u_D, v_D, w} C D
  -- inducedFunctor PolyPRAObj.forget

def polyPRAForgetFullyFaithful :
    (polyPRAForget C D).FullyFaithful
  -- fullyFaithfulInducedFunctor _
```

**Strategy:** the `⟨T1, E⟩` structure presentation is the
unconditional interface of `FCDirPRACat` (standing decision 1);
the morphism layer is the `(α, β)` pair of spec § 6.3 with
Task 3's `elMap`, and the category laws follow from `elMap_id` /
`elMap_comp` and `fcHom_ext`. The pinned mathlib's
`InducedCategory` takes the function as its single trailing
explicit argument, with the target category a preceding explicit
variable, fillable by name (`D := …`)
(`Mathlib/CategoryTheory/InducedCategory.lean:46`); the forgetful
functor is `inducedFunctor` with `fullyFaithfulInducedFunctor`
(`InducedCategory.lean:106`).

**Test:** package the Task 4 witness seed into a named
`PolyPRAObj (Discrete (Fin 2)) (Discrete (Fin 2))` (the Task 13
identity-instance seed), check `PolyPRAObj.forget`'s image
components (`T1`, `E`) by `rfl`, and return the object as a `def`
for reuse (Tasks 6–13).

- [ ] Standard step cycle; commit message
  `feat(polypra): add the formula categories and forgetful functor`.

### Task 6: spectrum and value functors

**Files:** Create `GebLean/PolyPRA/Value.lean`; append
`import GebLean.PolyPRA.Value` to `GebLean/PolyPRA.lean`;
tests in `GebLeanTests/PolyPRA/Basic.lean`.

**Interfaces — Produces** (universes `u_C v_C u_D v_D w`):

```lean
def polyPRASpectrum {C : Type u_C} [Category.{v_C} C]
    {D : Type u_D} [Category.{v_D} D]
    (P : PolyPRAObj.{u_C, v_C, u_D, v_D, w} C D) :
    FreeCoprodCompletionCat.{u_C, v_C, w} C ⥤
      FreeCoprodCompletionCat.{max u_D v_D w, v_D, w}
        (FCElem P.T1)                            -- M
def polyPRAValue {C : Type u_C} [Category.{v_C} C]
    {D : Type u_D} [Category.{v_D} D]
    (P : PolyPRAObj.{u_C, v_C, u_D, v_D, w} C D) :
    FreeCoprodCompletionCat.{u_C, v_C, w} C ⥤
      FreeCoprodCompletionCat.{u_D, v_D, w} D
-- polyPRAValue P = polyPRASpectrum P ⋙ fcMap (fcElProj P.T1)
@[simp] lemma polyPRAValue_obj
    (Z : FreeCoprodCompletionCat.{u_C, v_C, w} C) :
    (polyPRAValue P).obj Z =
      (fcMap (fcElProj P.T1)).obj (P.witness.spec Z)
```

**Strategy:** `M` on objects is `witness.spec`; on `ζ : Z ⟶ Z'`,
factor `counit Z ρ ≫ ζ` through `witness.factor Z'`; functor laws
from `factor_unique` exactly as spec § 6.4 validates (identity law
via `factor_counit`; composition by exhibiting the composite
factorization and invoking uniqueness). `polyPRAValue :=
polyPRASpectrum P ⋙ fcMap (fcElProj P.T1)` — definitional
composition, no new laws.

**Test:** `polyPRASpectrum` of the Task 13 identity-instance seed
(the Task 5 test object) at a named two-element `Z`, checked
against `Z` (index-level `rfl`); return the value as a `def` for
reuse (Tasks 7, 10, 13).

- [ ] Standard step cycle; commit message
  `feat(polypra): add the spectrum and value functors`.

### Task 7: the comparison functor

**Files:** Create `GebLean/PolyPRA/Comparison.lean`; append
`import GebLean.PolyPRA.Comparison` to
`GebLean/PolyPRA.lean`; tests in `GebLeanTests/PolyPRA/Basic.lean`.

**Interfaces — Produces** (universes `u_C v_C u_D v_D w`):

```lean
def polyPRAComparison (C : Type u_C) [Category.{v_C} C]
    (D : Type u_D) [Category.{v_D} D] :
    PolyPRACat.{u_C, v_C, u_D, v_D, w} C D ⥤
      (FreeCoprodCompletionCat.{u_C, v_C, w} C ⥤
        FreeCoprodCompletionCat.{u_D, v_D, w} D)
-- on objects: polyPRAValue; on (α, β): τ per spec § 6.3/6.4
```

**Strategy:** for a morphism `(α, β) : P ⟶ P'` and
`Z : FreeCoprodCompletionCat C`, the component `τ_Z` at
`ρ : fcIndex (P.witness.spec Z)` is
`P'.witness.factor Z ((elMap α).obj (fcFamily (P.witness.spec Z) ρ))`
applied to the composite
`β.app (fcFamily (P.witness.spec Z) ρ) ≫ P.witness.counit Z ρ`
(spec § 6.4's comparison clause, `ε_ρ ∘ β_{m_Z(ρ)}` in Lean
order; well-typed because `elMap α` preserves the underlying
`D`-object). Naturality in `Z` and functoriality in `(α, β)` are
unique-factorization chases using naturality of `β` — factor each
side and apply `factor_unique` (spec § 6.4, validated informally;
r1/r2 verification records reproduce them).

**Test:** apply `polyPRAComparison` to `𝟙` of the Task 5 test
object and check the resulting transformation's component at the
Task 6 two-element `Z` against `𝟙` (`fcHom_ext`-level `example`);
return the transformation as a `def` for reuse (Task 8).

- [ ] Standard step cycle; commit message
  `feat(polypra): add the comparison functor to the functor category`.

### Task 8: G2 — full faithfulness of the comparison

**Files:** Modify `GebLean/PolyPRA/Comparison.lean`; tests in
`GebLeanTests/PolyPRA/Basic.lean`.

**Interfaces — Produces** (universes `u_C v_C u_D v_D w`):

```lean
def polyPRAComparisonFullyFaithful (C : Type u_C)
    [Category.{v_C} C] (D : Type u_D) [Category.{v_D} D] :
    (polyPRAComparison.{u_C, v_C, u_D, v_D, w} C D).FullyFaithful
```

**Strategy:** recovery by evaluation at `Z = E.obj u` with the
unit-like factorization `𝟙 (E.obj u) = E.map v₀ ≫ counit _ ρ₀`
(spec § 7 G2: generic elements retract identities). `preimage`:
from `τ`, define `α` on the position of `u` via
`τ_{E.obj u}(ρ₀)`'s underlying data and `β_u` as the counit
composite; `map_preimage` / `preimage_map` by `factor_unique` and
`fcHom_ext`. This is the plan's highest-difficulty task; if the
recovery stalls, decompose per the factoring-out-lemmas technique
into: (a) injectivity of `(α, β) ↦ τ` (faithfulness), (b) the
recovery construction, (c) the two round-trips, and land (a)
first as its own commit
(`polyPRAComparison_faithful : Functor.Faithful …`, commit message
`feat(polypra): prove the comparison functor faithful`).

**Test:** check the `preimage` round-trip on the Task 7 test
transformation:
`(polyPRAComparisonFullyFaithful _ _).preimage` of
`(polyPRAComparison _ _).map (𝟙 _)` at the Task 5 test object is
`𝟙 _` (`fcHom_ext`-level `example`); return the preimage as a
`def` for reuse.

- [ ] Standard step cycle; commit message
  `feat(polypra): prove the comparison functor fully faithful`.

### Task 9: G3 — extension to presheaf categories

**Files:** Create `GebLean/PolyPRA/Extension.lean`; append
`import GebLean.PolyPRA.Extension` to
`GebLean/PolyPRA.lean`; tests in `GebLeanTests/PolyPRA/Basic.lean`.

**Interfaces — Produces** (universes `u_C v_C u_D v_D w`;
`PresheafPRACat`'s six parameters `.{u_I, v_I, u_J, v_J, w_I, w'}`
instantiated at `(u_C, v_C, u_D, v_D, max w v_C, max w v_D)` with
`I := C`, `J := D`):

```lean
def fcDirToCCR (C : Type u_C) [Category.{v_C} C]
    (D : Type u_D) [Category.{v_D} D] :
    FCDirPRACat.{u_C, v_C, u_D, v_D, w} C D ⥤
      (Dᵒᵖ ⥤
        CoprodCovarRepCat.{max (w + 1) u_C w, max w v_C, max w v_D}
          (FreeCoprodCompletionCat.{u_C, v_C, w} C))
  -- elements unpacking on positions: stage d ↦ positions
  -- fcEval P.T1 d, directions P.E.obj ⟨d, i, h⟩;
  -- Dᵒᵖ-functoriality from FCElem's morphism structure

def polyPRAExtend (C : Type u_C) [Category.{v_C} C]
    (D : Type u_D) [Category.{v_D} D] :
    PolyPRACat.{u_C, v_C, u_D, v_D, w} C D ⥤
      PresheafPRACat.{u_C, v_C, u_D, v_D, max w v_C, max w v_D} C D
  -- polyPRAForget C D ⋙ fcDirToCCR C D, whiskered with
  -- coprodCovarRepFunctor.map on (fcEvalCatFunctor C)

def polyPRAExtendYonedaEquiv
    (P : PolyPRAObj.{u_C, v_C, u_D, v_D, w} C D)
    (Z : Cᵒᵖ ⥤ Type (max w v_C)) (d : Dᵒᵖ) :
    praEvalAt C D ((polyPRAExtend C D).obj P) Z d ≃
      Σ e : fcEval P.T1 d.unop,
        ∀ b : fcIndex
          (P.E.obj ⟨d.unop, fcEvalIndex e, fcEvalMor e⟩),
          Z.obj (Opposite.op
            (fcFamily
              (P.E.obj ⟨d.unop, fcEvalIndex e, fcEvalMor e⟩) b))
  -- Hom(y i, Z) ≅ Z i collapse on representable directions
```

**Strategy:** `fcDirToCCR` carries the elements unpacking of
positions directly, with its direction layer the direct
`P.E.obj` assignment (its codomain keeps directions in `FC(C)`);
the `coprodCovarRepFunctor.map` whiskering along Task 1's
inclusion belongs to `polyPRAExtend` (standing decision 1);
PRA-ness is by construction (objects of `PresheafPRACat`). Universe mediation:
`FreeCoprodCompletionCat.{u_C, v_C, w} C` is an object of
`Cat.{max w v_C, max (w + 1) u_C w}` while `PresheafPRACat`'s CCR
layer is built over
`presheafCat C : Cat.{max u_C w v_C, max v_C (max w v_C + 1) u_C}`
— a different `Cat` universe pair — so `coprodCovarRepFunctor.map`
is applied to the `catULiftFunctor2`-widened image of
`fcEvalCatFunctor C`; if the stated `PresheafPRACat`
instantiation still fails unification, the executor widens with
`ULift` and records the deviation (Global constraints). The
Yoneda simplification `Equiv` is the hom-set computation from
Task 1 restated at the `praEvalAt` accessors.

**Test:** compute `polyPRAExtend` of the Task 5 test object and
check the position type at the unique stage against the seed's
index type via the `praEvalAt` accessors (`rfl`-level `example`);
return the extension object as a `def` for reuse (Task 10).

- [ ] Standard step cycle; commit message
  `feat(polypra): extend formula data to presheaf PRAs`.

### Task 10: G4 — the restriction isomorphism

**Files:** Modify `GebLean/PolyPRA/Extension.lean`; tests in
`GebLeanTests/PolyPRA/Basic.lean`.

**Interfaces — Produces** (universes `u_C v_C u_D v_D w`; both
legs land in `Dᵒᵖ ⥤ Type (max w u_C v_C v_D)` — the value leg is
lifted there by whiskering with
`uliftFunctor.{max u_C v_C, max w v_D}`, per spec § 10 item 4):

```lean
def polyPRAValuePresheaf {C : Type u_C} [Category.{v_C} C]
    {D : Type u_D} [Category.{v_D} D]
    (P : PolyPRAObj.{u_C, v_C, u_D, v_D, w} C D) :
    FreeCoprodCompletionCat.{u_C, v_C, w} C ⥤
      (Dᵒᵖ ⥤ Type (max w u_C v_C v_D)) :=
  polyPRAValue P ⋙ fcEvalCatFunctor.{u_D, v_D, w} D ⋙
    (Functor.whiskeringRight Dᵒᵖ _ _).obj
      uliftFunctor.{max u_C v_C, max w v_D}

def polyPRAExtendPresheaf {C : Type u_C} [Category.{v_C} C]
    {D : Type u_D} [Category.{v_D} D]
    (P : PolyPRAObj.{u_C, v_C, u_D, v_D, w} C D) :
    FreeCoprodCompletionCat.{u_C, v_C, w} C ⥤
      (Dᵒᵖ ⥤ Type (max w u_C v_C v_D)) :=
  fcEvalCatFunctor.{u_C, v_C, w} C ⋙
    (praEvalAtFunctor.{u_C, v_C, u_D, v_D, max w v_C, max w v_D}
      C D).obj ((polyPRAExtend C D).obj P)

def polyPRARestrictionIso
    (P : PolyPRAObj.{u_C, v_C, u_D, v_D, w} C D) :
    polyPRAValuePresheaf P ≅ polyPRAExtendPresheaf P
```

The G4 square as a `NatIso` between the two named composites
`FC(C) ⥤ PSh(D)` (standing decision 2). The component bijection
sends `(ρ, w : d ⟶ p(m_Z ρ))` to the element it uniquely factors
(spec § 6.4; the discrete-fibration lift is `FCElem`'s morphism
structure).

**Test:** apply the `hom` component of `polyPRARestrictionIso` at
the Task 6 two-element `Z` and the unique stage to a named
`fcEvalMk`-element and check its `praEvalAt_index` by `rfl`;
return the image element as a `def` for reuse.

- [ ] Standard step cycle; commit message
  `feat(polypra): prove the restriction isomorphism`.

### Task 11: G5 — faithfulness into the presheaf functor category

**Files:** Modify `GebLean/PolyPRA/Extension.lean`; tests in
`GebLeanTests/PolyPRA/Basic.lean`.

**Interfaces — Produces** (universes `u_C v_C u_D v_D w`):

```lean
def polyPRAExtendEval (C : Type u_C) [Category.{v_C} C]
    (D : Type u_D) [Category.{v_D} D] :
    PolyPRACat.{u_C, v_C, u_D, v_D, w} C D ⥤
      ((Cᵒᵖ ⥤ Type (max w v_C)) ⥤
        (Dᵒᵖ ⥤ Type (max w u_C v_C v_D))) :=
  polyPRAExtend C D ⋙
    praEvalAtFunctor.{u_C, v_C, u_D, v_D, max w v_C, max w v_D}
      C D

theorem polyPRAExtendEval_faithful (C : Type u_C)
    [Category.{v_C} C] (D : Type u_D) [Category.{v_D} D] :
    (polyPRAExtendEval.{u_C, v_C, u_D, v_D, w} C D).Faithful
```

**Strategy:** the second factor is fully faithful
(`praEvalAtFunctorFullyFaithful`, `GebLean/PresheafPRA.lean:1423`),
so faithfulness of the named composite reduces to faithfulness of
`polyPRAExtend`; that follows through Task 10's isomorphism and
G2's faithfulness (spec § 7 G5: equal presheaf-level
transformations give equal completion-level ones; G2 faithfulness
separates).

**Test:** instantiate the theorem at the test signature:
`lemma`-level
`(polyPRAExtendEval (Discrete PUnit) (Discrete PUnit)).Faithful`
proved by `polyPRAExtendEval_faithful _ _` (single expression;
the instance is the returned value).

- [ ] Standard step cycle; commit message
  `feat(polypra): prove faithfulness of the presheaf comparison`.

### Task 12: FCP instantiation

**Files:** Create `GebLean/PolyPRA/FCP.lean`; append
`import GebLean.PolyPRA.FCP` to `GebLean/PolyPRA.lean`;
tests in `GebLeanTests/PolyPRA/Basic.lean`.

**Interfaces — Produces** (universes `u_I v_I u_J v_J w`; the
instantiation sets `u_C := max (w + 1) u_I w`,
`v_C := max w v_I`, and likewise for `J` — `FP` raises the object
universe (spec § 10 item 4), which `PolyPRACat`'s polymorphism
absorbs):

```lean
abbrev FCPPolyPRACat (I : Type u_I) [Category.{v_I} I]
    (J : Type u_J) [Category.{v_J} J] :=
  PolyPRACat.{max (w + 1) u_I w, max w v_I,
      max (w + 1) u_J w, max w v_J, w}
    (FreeProdCompletionCat.{u_I, v_I, w} I)
    (FreeProdCompletionCat.{u_J, v_J, w} J)
-- plus restatements of the Task 7/9 functors at this signature,
-- and the `fcpCcrsIso`-mediated identification of the domain and
-- codomain with FreeCoprodProdCat I / J
```

The `fcpCcrsIso` identification and the restated functors mediate
residual universe mismatches with `catULiftFunctor2`, recording
any deviation (Global constraints).

**Test:** build a one-position object of
`FCPPolyPRACat (Discrete PUnit) (Discrete PUnit)` (position over
the terminal formal product, empty direction family, witnesses by
the empty-family factorization) as a `def`, check its `T1` index
type by `rfl`, and return it for reuse (Task 13).

- [ ] Standard step cycle; commit message
  `feat(polypra): instantiate at the free coproduct-product completion`.

### Task 13: instance tests — `Poly` and the identity

**Files:** Modify `GebLeanTests/PolyPRA/Basic.lean` (registered in
`GebLeanTests.lean` by Task 1).

**Contents** (universe instantiation: `Discrete PUnit : Type 0`
with `Category.{0}`, index universe `w := 0`): (a)
`C = D = Discrete PUnit`: build a two-position object (`T1` with
two indices, direction families of sizes 0 and 2), evaluate
`polyPRAValue` at a three-element input, and check the index count
by `decide`/`rfl`-level lemmas — the `Σ_a X^{B_a}` polynomial
count; (b) the identity instance: `E` the evident
`FCElem T1 ⥤ FC C` at `T1 = fcObjMk (fun i => c_i)` over a
discrete two-object `C` with witnesses from Task 4's
`factor_counit` seed, and `example : polyPRAValue _ |>.obj Z = Z`
up to `fcHom_ext`-level isomorphism (spec § 8 test criteria;
compositional-test rule: each test returns its value for reuse —
the seeds built by the Tasks 4–6 tests are consumed here).

- [ ] Standard step cycle; commit message
  `test(polypra): add Poly and identity instance tests`.

## Self-review checklist (run before adversarial review)

- Spec § 8 deliverables 1–4 map to Tasks 1, 5+9 (the formula
  category and its conversion functor, per standing decision 1
  and the amended deliverable 2), 2+6+7, 12; theorems G2/G3/G4/G5
  to Tasks 8/9/10/11; tests to the per-task test contracts and
  Task 13. The prerequisite deliverables of spec § 2 are
  Tasks 1–2.
- No placeholders; every interface consumed by a later task is
  produced verbatim by an earlier one, or listed in the
  consumed-interfaces section:
  - `fcEvalCatFunctor` / `fcEvalCatFullyFaithful` (Task 1) →
    Tasks 9, 10;
  - `fcMap` and its pointwise `@[simp]` lemmas (Task 2) →
    Tasks 6, 10;
  - `FCElem` / `fcElProj` (Task 3) → Tasks 4, 5, 6, 10;
  - `elMap` / `elMap_id` / `elMap_comp` (Task 3) → Tasks 5, 7, 8;
  - `fcElTerminalHom` (Task 3) → Task 3's test;
  - `MultiadjunctionWitnesses` fields (Task 4) → Tasks 6, 7, 8;
  - `factor_counit` (Task 4) → Tasks 6, 13;
  - `FCDirPRACat` / `PolyPRAObj` / `PolyPRACat` / `polyPRAForget`
    (Task 5) → Tasks 6–11;
  - `polyPRASpectrum` / `polyPRAValue` (Task 6) → Tasks 7, 10;
  - `polyPRAComparison` (Task 7) → Tasks 8, 11;
  - `polyPRAComparisonFullyFaithful` (Task 8) → Task 11;
  - `fcDirToCCR` (Task 9) → Task 9's `polyPRAExtend`;
    `polyPRAExtend` (Task 9) → Tasks 10, 11;
  - `praEvalAtFunctor` (consumed,
    `GebLean/PresheafPRA.lean:1387`) → Tasks 10, 11;
    `praEvalAtFunctorFullyFaithful` (`:1423`) → Task 11;
  - test seed values (Tasks 1–6 tests) → later tasks' tests
    (compositional-test rule).
- Universe parameters stated in every "Interfaces — Produces"
  block; lift mediation points identified (Tasks 9, 10, 12);
  deviations, if any, recorded per Global constraints.

## References

- Spec: `docs/superpowers/specs/2026-07-14-polynomial-preserving-pra-design.md`
  (§ 6 formula, § 7 strategies, § 8 acceptance criteria) and its
  References section for the literature identifiers.
- Reviews: `…design.review-r1.md`, `…design.review-r2.md`
  (verification records for the arguments Tasks 6–8 formalize).
