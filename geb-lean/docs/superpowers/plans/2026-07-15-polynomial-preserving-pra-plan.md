# Polynomial-preserving presheaf PRAs implementation plan

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Global constraints](#global-constraints)
- [Consumed interfaces (verbatim, current pin)](#consumed-interfaces-verbatim-current-pin)
- [File structure](#file-structure)
- [Execution notes](#execution-notes)
  - [Task 1: bundled inclusion `fcEvalCatFunctor` and full faithfulness](#task-1-bundled-inclusion-fcevalcatfunctor-and-full-faithfulness)
  - [Task 2: `fcMap` — the action of `FC` on functors](#task-2-fcmap--the-action-of-fc-on-functors)
  - [Task 3: elements of positions — `fcEl` and its projection](#task-3-elements-of-positions--fcel-and-its-projection)
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

**Architecture:** Higher-order construction throughout: the bundled
inclusion `FC(C) ⥤ PSh(C)` and the action of `FC` on functors are
built once in `Utilities`; the formula categories are obtained by
applying the existing `coprodCovarRepFunctor` /
`ccrPresheafCatFunctor` machinery to `FC(C)` and whiskering along
the inclusion; the witness layer is an `InducedCategory` over the
witness-free category, making the forgetful functor fully faithful
by construction. All witnesses (multiadjunction data, factorization
assignments) are structure fields, never `∃`.

**Tech Stack:** Lean 4 (current toolchain pin), Lake, mathlib
category theory (`Functor.Elements`, `Functor.FullyFaithful`,
`InducedCategory`, `Grothendieck`), the in-repository
`Families.lean` / `PresheafPRA.lean` stacks, `jj`,
`markdownlint-cli2`, `doctoc`.

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
  (as `PresheafPRA.lean` already does). Each task states its
  universe parameters explicitly; if a stated signature fails
  universe unification, the executor widens with `ULift` mediation
  rather than weakening the interface, and records the deviation
  for review.
- Commit messages: mathlib convention, imperative, lowercase
  subject, no trailing period; commit via `jj commit`.
- One definition at a time; factor helpers into
  `GebLean/Utilities/`.

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
- `familyFunctor'`, `familyNatTrans'`, `familyPostcomp'`,
  `GrothendieckContra'` (via `GebLean/Utilities/Grothendieck.lean`).

From `GebLean/PresheafPRA.lean`:

- `presheafCatFunctor`, `PresheafPRACat` (`Jᵒᵖ ⥤
  CoprodCovarRepCat (Iᵒᵖ ⥤ Type w_I)`), `ccrPresheafCatFunctor`,
  `catULiftFunctor2`, `praEvalAt*` accessors.

## File structure

- Create `GebLean/Utilities/FCEval.lean` — Tasks 1–2 (bundled
  inclusion, full faithfulness, `fcMap`).
- Create `GebLean/PolyPRA/Elements.lean` — Task 3 (`fcEl`,
  projection, slice decomposition).
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
- Create `GebLean/PolyPRA.lean` — index file (public imports).
- Create `GebLeanTests/PolyPRA/Basic.lean` — Task 13 plus per-task
  test additions.
- Modify `GebLean.lean` (or the repository's root index) to import
  `GebLean.PolyPRA`.

Topic branch: continue `feat/poly-preserving-pra`.

## Execution notes

- Every task follows the same step template; it is spelled out in
  Task 1 and referenced afterwards ("standard step cycle") with the
  task's own declarations, tests, and commit message substituted.
  The cycle is: (1) write the declarations with `_` placeholders
  for proofs; (2) `lake build` and inspect the goals; (3) fill
  proofs one declaration at a time; (4) add the task's test
  declarations under `GebLeanTests/PolyPRA/Basic.lean`; (5) run
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

**Files:** Create `GebLean/Utilities/FCEval.lean`; test
`GebLeanTests/PolyPRA/Basic.lean` (create).

**Interfaces — Produces:**

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
the Yoneda elements `fcEvalMk i (𝟙 _)`; the hom-set computation is
the distributivity `Π_b Σ_x Hom(G b, F x) ≅ Σ_r Π_b Hom(G b, F(r
b))` (spec § 7 G3; Dorta–Jarvis–Niu Proposition 2.4), which is a
`Sigma`/`Pi` `Equiv` in Lean, choice-free.

- [ ] **Step 1:** create the file with module docstring
  (`## References`: Dorta–Jarvis–Niu arXiv:2305.05655
  Propositions 2.4/2.7; spec § 6.4) and the two declarations with
  `_` proof placeholders.
- [ ] **Step 2:** `lake build` — inspect goals.
- [ ] **Step 3:** prove `fcEvalCatFunctor` functor laws (pointwise,
  via `fcEvalMap_id` / `fcEvalMap_comp`).
- [ ] **Step 4:** prove `fcEvalCatFullyFaithful` (preimage via
  Yoneda elements; `map_preimage` by naturality at
  `fcEvalMk i (𝟙 _)`; `preimage_map` by `fcHom_ext`).
- [ ] **Step 5:** add tests: for `C = Discrete PUnit` and a
  two-element family, compute `fcEval` of the image and `#guard`
  -style decidable checks or `example`-level `rfl` isomorphisms.
- [ ] **Step 6:** `lake test`; `bash scripts/pre-commit.sh`.
- [ ] **Step 7:** `jj commit -m "feat(polypra): add the bundled
  free-coproduct-completion inclusion"`.

### Task 2: `fcMap` — the action of `FC` on functors

**Files:** Modify `GebLean/Utilities/FCEval.lean`; test file as in
Task 1.

**Interfaces — Produces:**

```lean
def fcMap {A : Type u_A} [Category.{v_A} A] {B : Type u_B}
    [Category.{v_B} B] (p : A ⥤ B) :
    FreeCoprodCompletionCat.{u_A, v_A, w} A ⥤
      FreeCoprodCompletionCat.{u_B, v_B, w} B

@[simp] lemma fcMap_obj_index ...  -- index preserved
@[simp] lemma fcMap_obj_family ... -- family = p ∘ family
lemma fcMap_id : fcMap (𝟭 A) = 𝟭 _
lemma fcMap_comp : fcMap (p ⋙ q) = fcMap p ⋙ fcMap q
```

**Strategy:** object part `fcObjMk (p.obj ∘ fcFamily P)`; morphism
part keeps `fcReindex` and post-composes `p.map` on `fcFiberMor`;
laws by `fcHom_ext`. Construct through `GrothendieckContra'` /
`familyPostcomp'` machinery where universe constraints permit
(Global constraints); otherwise direct with the `fc*` helpers.

- [ ] Standard step cycle; commit message
  `feat(polypra): add the functorial action of FC on functors`.

### Task 3: elements of positions — `fcEl` and its projection

**Files:** Create `GebLean/PolyPRA/Elements.lean`; tests as above.

**Interfaces — Produces:**

```lean
structure FCElem {D : Type u_D} [Category.{v_D} D]
    (P : FreeCoprodCompletionCat.{u_D, v_D, w} D) where
  pt : D
  idx : fcIndex P
  hom : pt ⟶ fcFamily P idx

instance : Category (FCElem P)  -- morphisms: v : pt ⟶ pt' with
                                -- idx' = idx and hom = hom' ∘ v

def fcElProj (P) : FCElem P ⥤ D
```

with `@[ext]` on `FCElem`-morphisms and `@[simp]` projection
lemmas. Orientation: a morphism `e ⟶ e'` lies over `v : e.pt ⟶
e'.pt` with `e.hom = v ≫ e'.hom` and `e.idx = e'.idx` (spec § 6's
elements orientation; mathlib's `Functor.Elements` of the
`fcEvalCatFunctor` image is the opposite — record the comparison
as a lemma only if a later task needs it, YAGNI).

**Strategy:** direct structure; the slice decomposition
`FCElem P ≅ Σ_s D/k_s` is *not* a deliverable (the later tasks
consume `FCElem` directly); the terminal-per-index objects
`⟨fcFamily P i, i, 𝟙 _⟩` are, with a lemma `fcElTerminalHom`
giving the unique factorization of any element through them —
this is the slice-terminality of the spec's § 6.2 in element
form.

- [ ] Standard step cycle; commit message
  `feat(polypra): add the elements category of polynomial positions`.

### Task 4: multiadjunction witnesses

**Files:** Create `GebLean/PolyPRA/Multiadjunction.lean`; tests as
above.

**Interfaces — Produces:**

```lean
structure MultiadjunctionWitnesses
    {C D} [Category C] [Category D]
    {T1 : FreeCoprodCompletionCat D}
    (E : FCElem T1 ⥤ FreeCoprodCompletionCat C) where
  spec : ∀ Z : FreeCoprodCompletionCat C,
    FreeCoprodCompletionCat (FCElem T1)          -- M(Z)
  counit : ∀ Z, ∀ ρ : fcIndex (spec Z),
    E.obj (fcFamily (spec Z) ρ) ⟶ Z              -- ε_ρ
  factor : ∀ Z, ∀ u, (E.obj u ⟶ Z) →
    Σ ρ : fcIndex (spec Z), (u ⟶ fcFamily (spec Z) ρ)
  factor_spec : ∀ Z u (φ : E.obj u ⟶ Z),
    E.map (factor Z u φ).2 ≫ counit Z (factor Z u φ).1 = φ
  factor_unique : ∀ Z u (φ : E.obj u ⟶ Z) ρ
    (v : u ⟶ fcFamily (spec Z) ρ),
    E.map v ≫ counit Z ρ = φ →
    (⟨ρ, v⟩ : Σ ρ, _) = factor Z u φ
```

(`factor` is data; `factor_spec` / `factor_unique` are the
Prop-valued fields — spec § 6.2 as amended by review r1 F4.)
Derived lemma: `factor_counit : factor Z _ (counit Z ρ) = ⟨ρ, 𝟙 _⟩`
(uniqueness applied to the identity factorization; spec § 6.4's
identity law seed).

- [ ] Standard step cycle; commit message
  `feat(polypra): add the multiadjunction witness structure`.

### Task 5: the formula categories

**Files:** Create `GebLean/PolyPRA/Cat.lean`; tests as above.

**Interfaces — Produces:**

```lean
def FCDirPRACat (C D) [Category C] [Category D] : Type _
  -- the witness-free category: positions T1 with directions
  -- functor into FC C; built as a full subcategory-style
  -- structure `⟨T1, E⟩` with morphisms (α, β) per spec § 6.3
structure PolyPRAObj (C D) [Category C] [Category D] where
  T1 : FreeCoprodCompletionCat D
  E : FCElem T1 ⥤ FreeCoprodCompletionCat C
  witness : MultiadjunctionWitnesses E

def PolyPRACat (C D) [Category C] [Category D] : Type _ :=
  InducedCategory (FCDirPRAObj C D) PolyPRAObj.forget
def polyPRAForget : PolyPRACat C D ⥤ FCDirPRACat C D
theorem polyPRAForget_fullyFaithful : ...
```

**Strategy:** for `FCDirPRACat`, first attempt the higher-order
route (spec § 8 deliverable 2): whisker `ccrPresheafCatFunctor`'s
CCR layer at `FC(C)` in place of `PSh(C)`; if universe unification
blocks it at this pin, fall back to the direct `⟨T1, E⟩` structure
with `(α : T1 ⟶ T1', β : (elMap α) ⋙ E' ⟶ E)` morphisms — where
`elMap α : FCElem T1 ⥤ FCElem T1'` is the evident induced functor
(add it to Task 3's file if reached) — and record the deviation.
`InducedCategory` supplies the fully faithful forgetful functor
(mathlib `fullyFaithfulInducedFunctor`).

- [ ] Standard step cycle; commit message
  `feat(polypra): add the formula categories and forgetful functor`.

### Task 6: spectrum and value functors

**Files:** Create `GebLean/PolyPRA/Value.lean`; tests as above.

**Interfaces — Produces:**

```lean
def polyPRASpectrum (P : PolyPRAObj C D) :
    FreeCoprodCompletionCat C ⥤
      FreeCoprodCompletionCat (FCElem P.T1)   -- M
def polyPRAValue (P : PolyPRAObj C D) :
    FreeCoprodCompletionCat C ⥤ FreeCoprodCompletionCat D
-- polyPRAValue P = polyPRASpectrum P ⋙ fcMap (fcElProj P.T1)
@[simp] lemma polyPRAValue_obj ...
```

**Strategy:** `M` on objects is `witness.spec`; on `ζ : Z ⟶ Z'`,
factor `counit Z ρ ≫ ζ` through `witness.factor Z'`; functor laws
from `factor_unique` exactly as spec § 6.4 validates (identity law
via `factor_counit`; composition by exhibiting the composite
factorization and invoking uniqueness). `polyPRAValue :=
polyPRASpectrum P ⋙ fcMap (fcElProj P.T1)` — definitional
composition, no new laws.

- [ ] Standard step cycle; commit message
  `feat(polypra): add the spectrum and value functors`.

### Task 7: the comparison functor

**Files:** Create `GebLean/PolyPRA/Comparison.lean`; tests as
above.

**Interfaces — Produces:**

```lean
def polyPRAComparison (C D) [Category C] [Category D] :
    PolyPRACat C D ⥤
      (FreeCoprodCompletionCat C ⥤ FreeCoprodCompletionCat D)
-- on objects: polyPRAValue; on (α, β): τ per spec § 6.3/6.4
```

**Strategy:** component `τ_Z` at `ρ` is the factorization of
`E.map (…) ≫ counit … ≫ …` composite `counit Z ρ ≫ β`-transport
through the target witnesses (spec § 6.4's comparison clause);
naturality in `Z` and functoriality in `(α, β)` are
unique-factorization chases using naturality of `β` — factor each
side and apply `factor_unique` (spec § 6.4, validated informally;
r1/r2 verification records reproduce them).

- [ ] Standard step cycle; commit message
  `feat(polypra): add the comparison functor to the functor category`.

### Task 8: G2 — full faithfulness of the comparison

**Files:** Modify `GebLean/PolyPRA/Comparison.lean`; tests as
above.

**Interfaces — Produces:**

```lean
def polyPRAComparisonFullyFaithful (C D) [Category C]
    [Category D] : (polyPRAComparison C D).FullyFaithful
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
(`polyPRAComparison_faithful : Functor.Faithful …`).

- [ ] Standard step cycle; commit message
  `feat(polypra): prove the comparison functor fully faithful`.

### Task 9: G3 — extension to presheaf categories

**Files:** Create `GebLean/PolyPRA/Extension.lean`; tests as
above.

**Interfaces — Produces:**

```lean
def polyPRAExtend (C D) [Category C] [Category D] :
    PolyPRACat C D ⥤ PresheafPRACat ...  -- indices per
      -- PresheafPRACat's (I, J) parameters with C = Iᵒᵖ-side
      -- conventions fixed here once, and universe lifts recorded
lemma polyPRAExtend_yoneda_simplification ...
  -- Hom(y i, Z) ≅ Z i collapse on representable directions
```

**Strategy:** whisker along `fcEvalCatFunctor` inside the CCR
layer (`coprodCovarRepFunctor` functoriality on the inclusion) —
the spec § 8 deliverable-2 route; PRA-ness is by construction
(objects of `PresheafPRACat`). The Yoneda simplification lemma is
the `Equiv` from Task 1 restated at the `praEvalAt` accessors.

- [ ] Standard step cycle; commit message
  `feat(polypra): extend formula data to presheaf PRAs`.

### Task 10: G4 — the restriction isomorphism

**Files:** Modify `GebLean/PolyPRA/Extension.lean`; tests as
above.

**Interfaces — Produces:**

```lean
def polyPRARestrictionIso (P : PolyPRAObj C D) :
    fcEvalCatFunctor D ⋙-compatible statement:
    -- fcEval (polyPRAValue P |>.obj Z) d ≃ praEvalAt-of-extension
    -- natural in d and Z; packaged as a NatIso between the two
    -- composites FC(C) ⥤ PSh(D)
```

Exact statement: a `NatIso` between
`polyPRAValue P ⋙ fcEvalCatFunctor D` and
`fcEvalCatFunctor C ⋙ (extension applied)` — the G4 square. The
component bijection sends `(ρ, w : d ⟶ p(m_Z ρ))` to the element
it uniquely factors (spec § 6.4; the discrete-fibration lift is
`FCElem`'s morphism structure).

- [ ] Standard step cycle; commit message
  `feat(polypra): prove the restriction isomorphism`.

### Task 11: G5 — faithfulness into the presheaf functor category

**Files:** Modify `GebLean/PolyPRA/Extension.lean`; tests as
above.

**Interfaces — Produces:**

```lean
theorem polyPRAExtendEval_faithful : ...
-- the composite PolyPRACat C D ⥤ (PSh C ⥤ PSh D) (extension
-- followed by PRA evaluation) is faithful; fullness = G2 (§ 7)
```

**Strategy:** factor through G2's comparison via Task 10's
isomorphism (spec § 7 G5: equal presheaf-level transformations
give equal completion-level ones; G2 faithfulness separates).

- [ ] Standard step cycle; commit message
  `feat(polypra): prove faithfulness of the presheaf comparison`.

### Task 12: FCP instantiation

**Files:** Create `GebLean/PolyPRA/FCP.lean`; index file
`GebLean/PolyPRA.lean`; modify the repository root index; tests as
above.

**Interfaces — Produces:**

```lean
abbrev FCPPolyPRACat (I J) [Category I] [Category J] :=
  PolyPRACat (FreeProdCompletionCat I) (FreeProdCompletionCat J)
-- plus restatements of the Task 7/9 functors at this signature,
-- and the `fcpCcrsIso`-mediated identification of the domain and
-- codomain with FreeCoprodProdCat I / J
```

- [ ] Standard step cycle (index file gets `public import`s per
  the module-system rule); commit message
  `feat(polypra): instantiate at the free coproduct-product completion`.

### Task 13: instance tests — `Poly` and the identity

**Files:** Modify `GebLeanTests/PolyPRA/Basic.lean`; register the
test module in the test index if the repository requires it.

**Contents:** (a) `C = D = Discrete PUnit`: build a two-position
object (`T1` with two indices, direction families of sizes 0 and
2), evaluate `polyPRAValue` at a three-element input, and check
the index count by `decide`/`rfl`-level lemmas — the
`Σ_a X^{B_a}` polynomial count; (b) the identity instance: `E`
the evident `FCElem T1 ⥤ FC C` at `T1 = fcObjMk (fun i => c_i)`
over a discrete two-object `C` with witnesses from Task 4's
`factor_counit` seed, and `example : polyPRAValue _ |>.obj Z = Z`
up to `fcHom_ext`-level isomorphism (spec § 8 test criteria;
compositional-test rule: each test returns its value for reuse).

- [ ] Standard step cycle; commit message
  `test(polypra): add Poly and identity instance tests`.

## Self-review checklist (run before adversarial review)

- Spec § 8 deliverables 1–4 map to Tasks 1, 5, 2+6+7, 12; theorems
  G2/G3/G4/G5 to Tasks 8/9/10/11; tests to Task 13. The
  prerequisite deliverables of spec § 2 are Tasks 1–2.
- No placeholders; every interface consumed by a later task is
  produced verbatim by an earlier one (`fcMap` Task 2 → 6;
  `FCElem`/`fcElProj` Task 3 → 4/5/6/10; `MultiadjunctionWitnesses`
  fields Task 4 → 6/7/8; `polyPRAValue` Task 6 → 7/10;
  `fcEvalCatFunctor` Task 1 → 9/10).
- Universe deviations, if any, recorded per Global constraints.

## References

- Spec: `docs/superpowers/specs/2026-07-14-polynomial-preserving-pra-design.md`
  (§ 6 formula, § 7 strategies, § 8 acceptance criteria) and its
  References section for the literature identifiers.
- Reviews: `…design.review-r1.md`, `…design.review-r2.md`
  (verification records for the arguments Tasks 6–8 formalize).
