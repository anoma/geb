# Adversarial review: polynomial-preserving PRA plan (round 1)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [Spec coverage map](#spec-coverage-map)
- [BLOCKER findings](#blocker-findings)
  - [B1. Task 5's two routes yield incompatible downstream interfaces](#b1-task-5s-two-routes-yield-incompatible-downstream-interfaces)
  - [B2. Modules unregistered until Tasks 12–13; per-task gates vacuous](#b2-modules-unregistered-until-tasks-1213-per-task-gates-vacuous)
- [MAJOR findings](#major-findings)
  - [A1. Task 5's Lean sketch does not elaborate as written](#a1-task-5s-lean-sketch-does-not-elaborate-as-written)
  - [A2. `elMap` is needed unconditionally but produced only conditionally](#a2-elmap-is-needed-unconditionally-but-produced-only-conditionally)
  - [A3. Tasks 9–11 interfaces are placeholders; PRA evaluation unnamed](#a3-tasks-911-interfaces-are-placeholders-pra-evaluation-unnamed)
  - [A4. Universe handling defers spec § 10 item 4 against its own rule](#a4-universe-handling-defers-spec--10-item-4-against-its-own-rule)
  - [A5. Task 3's parallel elements category: reuse decision unrecorded](#a5-task-3s-parallel-elements-category-reuse-decision-unrecorded)
  - [A6. Tasks 2–12 test steps carry no content](#a6-tasks-212-test-steps-carry-no-content)
  - [A7. The self-review checklist's verbatim-interface claim is false](#a7-the-self-review-checklists-verbatim-interface-claim-is-false)
- [MINOR findings](#minor-findings)
  - [M1. Task 7's strategy sentence is garbled; composite order wrong](#m1-task-7s-strategy-sentence-is-garbled-composite-order-wrong)
  - [M2. Task 1 citation drift against spec § 7](#m2-task-1-citation-drift-against-spec--7)
  - [M3. `polyPRAForget_fullyFaithful` must be a `def`, not a `theorem`](#m3-polypraforget_fullyfaithful-must-be-a-def-not-a-theorem)
  - [M4. Task 2's functor-equality laws need pointwise companions](#m4-task-2s-functor-equality-laws-need-pointwise-companions)
  - [M5. Task 4's binder sketch omits types that `autoImplicit = false` requires](#m5-task-4s-binder-sketch-omits-types-that-autoimplicit--false-requires)
  - [M6. The spec § 10 item 3 (O3) resolution is implicit, never recorded](#m6-the-spec--10-item-3-o3-resolution-is-implicit-never-recorded)
  - [M7. Commit-message constraint omits the repository trailer convention](#m7-commit-message-constraint-omits-the-repository-trailer-convention)
  - [M8. Conditional phrasing in file-structure and registration steps](#m8-conditional-phrasing-in-file-structure-and-registration-steps)
- [NIT findings](#nit-findings)
  - [N1. Misplaced provenance parenthetical in the consumed-interfaces list](#n1-misplaced-provenance-parenthetical-in-the-consumed-interfaces-list)
  - [N2. Task 8's fallback commit has no commit message](#n2-task-8s-fallback-commit-has-no-commit-message)
- [Verified without defect](#verified-without-defect)
- [Verification record](#verification-record)
- [Verdict](#verdict)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Verdict: ITERATE (2 BLOCKER, 7 MAJOR, 8 MINOR, 2 NIT).

Target:
`docs/superpowers/plans/2026-07-15-polynomial-preserving-pra-plan.md`.
Spec (converged):
`docs/superpowers/specs/2026-07-14-polynomial-preserving-pra-design.md`
(+ `.review-r1`, `.review-r2`). Format precedent:
`docs/superpowers/plans/2026-07-04-ramified-p6-soundness-subplan.md`.
Scope: the six review dimensions (spec coverage,
consumed-interface accuracy, task-interface consistency,
feasibility and risk ordering, plan-format compliance, process),
verified against the repository at bookmark
`feat/poly-preserving-pra` (`82e6d79a`) and the pinned mathlib
(`v4.29.0-rc6`).

## Summary

The task decomposition is the right shape: the spec's § 8
deliverables and G2–G5 theorems each map to exactly one task, the
witness structure transcribes § 6.2 as amended by spec-review r1
F4, the Task 6/8 strategies match the § 6.4/§ 7 arguments whose
verification records exist in the spec reviews, and Task 8 is
correctly isolated as the highest-difficulty step with a
decomposition fallback. Every consumed identifier the plan lists
exists at the stated location, and all thirteen commit messages
conform to the re-fetched mathlib convention. Two structural
defects block execution as written. First, Task 5's primary
(whiskered) route and its fallback produce categorically different
object presentations, and the plan's later tasks consume
accessors from the fallback shape while Task 9's strategy consumes
the whiskered shape — no single choice satisfies the plan as
written, and the fallback additionally contradicts spec § 8
deliverable 2's construction mandate without acknowledging it.
Second, none of the new modules is imported by any built root
until Tasks 12–13, so the per-task `lake build` / `lake test` /
pre-commit / axiom-gate steps of Tasks 1–11 elaborate none of the
new code. The MAJOR findings are localized and fixable: an
inconsistent Task 5 sketch, a conditionally-produced `elMap` that
is unconditionally needed, placeholder signatures in Tasks 9–11,
universe analysis deferred against the spec's owner assignment,
an unrecorded reuse decision for the elements category, and
content-free test steps.

## Spec coverage map

Spec § 8 acceptance criteria and § 7 obligations against plan
tasks:

| Spec item | Plan task | Status |
| --- | --- | --- |
| § 8 deliverable 1 (bundled inclusion + `FullyFaithful`) | Task 1 | Covered |
| § 8 deliverable 2 (formula category via existing machinery) | Task 5 | Covered with conflict (B1) |
| § 8 deliverable 3 (`FC(p)`, value functor, comparisons) | Tasks 2, 6, 7 | Covered |
| § 8 deliverable 4 (FCP instantiation) | Task 12 | Covered |
| § 8 theorem G2 (full faithfulness) / § 7 G2 strategy | Task 8 | Covered; strategy matches § 7 |
| § 8 theorem G3 (PRA witness, Yoneda simplification) / § 7 G3 | Task 9 | Covered; interface placeholder (A3) |
| § 8 theorem G4 (restriction NatIso) / § 7 G4 | Task 10 | Covered; not statable as written (A3, A4) |
| § 8 theorem G5 (faithfulness) / § 7 G5 | Task 11 | Covered; strategy matches § 7 |
| § 8 tests (`C = D = 1` recovers `Poly`; identity instance) | Task 13 | Covered |
| § 8 constructive + axiom gate | Global constraints | Covered (but see B2) |
| § 2 prerequisite deliverables (inclusion; `FC` on functors) | Tasks 1–2 | Covered |
| § 10 item 3 (restriction vocabulary; owner: planning) | Task 10, implicit | Unrecorded (M6) |
| § 10 item 4 (universe alignment; owner: planning) | Global constraints | Deferred (A4) |

No over-scope found: Task 3's `fcElTerminalHom` and Task 4's
`factor_counit` are consumed by Tasks 6/13, and the slice
decomposition is explicitly excluded.

## BLOCKER findings

### B1. Task 5's two routes yield incompatible downstream interfaces

Task 5 Strategy: "first attempt the higher-order route (spec § 8
deliverable 2): whisker `ccrPresheafCatFunctor`'s CCR layer at
`FC(C)` in place of `PSh(C)`; if universe unification blocks it at
this pin, fall back to the direct `⟨T1, E⟩` structure".

The two routes do not differ merely in implementation; they
differ in the objects of the category produced:

- The whiskered route replicates `PresheafPRACat`'s shape
  (`GebLean/PresheafPRA.lean:139`: objects are functors
  `Jᵒᵖ ⥤ CoprodCovarRepCat (Iᵒᵖ ⥤ Type w_I)`), giving objects
  `Dᵒᵖ ⥤ CoprodCovarRepCat (FC C)`. Its positions component is an
  arbitrary presheaf on `D`, not a polynomial `T1 ∈ FC(D)`, and
  its directions are indexed per stage, not by a functor
  `FCElem T1 ⥤ FC C`. This is not the § 6.2 formula category, and
  it provides none of the accessors Tasks 6–8 consume
  (`P.T1 : FreeCoprodCompletionCat D`,
  `P.E : FCElem P.T1 ⥤ FreeCoprodCompletionCat C`, morphisms
  `(α, β)`).
- The fallback `⟨T1, E⟩` structure matches Tasks 6–8 but leaves
  Task 9's strategy ("whisker along `fcEvalCatFunctor` inside the
  CCR layer") without its input: converting `⟨T1, E⟩` into a
  functor `Dᵒᵖ ⥤ CoprodCovarRepCat (FC C)` (evaluate `T1` at each
  stage via `fcEval`; restrict `E` along each stage's elements) is
  a nontrivial functor assigned to no task.

The fallback also contradicts spec § 8 deliverable 2 verbatim
("built by applying the existing `coprodCovarRepFunctor` /
`ccrPresheafCatFunctor` machinery to `FC(C)` and whiskering along
the inclusion — not by explicit object/morphism maps"), and the
plan's fallback trigger ("if universe unification blocks it")
misses the structural mismatch above, which blocks the primary
route regardless of universes.

Fix: fix the `⟨T1, E⟩` presentation as the unconditional interface
of `FCDirPRACat` (Tasks 6–8 depend on it), and give the
higher-order machinery a definite, unconditional role: Task 9
builds the conversion functor
`FCDirPRACat C D ⥤ (Dᵒᵖ ⥤ CoprodCovarRepCat (FreeCoprodCompletionCat C))`
(elements unpacking on positions;
`coprodCovarRepFunctor.map` applied to Task 1's inclusion on
directions), whose composite with the existing
`PresheafPRACat`-side machinery is `polyPRAExtend`. Record the
reconciliation with spec § 8 deliverable 2 explicitly — either as
a deviation note in the plan or as a spec amendment — rather than
leaving the acceptance criterion silently unsatisfiable.

### B2. Modules unregistered until Tasks 12–13; per-task gates vacuous

File structure: "Modify `GebLean.lean` (or the repository's root
index) to import `GebLean.PolyPRA`" — listed under Task 12; Task
13: "register the test module in the test index if the repository
requires it".

The repository does require it, and earlier than Task 12/13. In
`lakefile.toml` the `GebLean` library declares no `globs`, so lake
builds only the root module `GebLean.lean` and its transitive
imports (the `Geb` library's comment documents exactly this:
`globs = ["Geb.*"]` is needed to "cover the whole vendored
namespace"). `GebLeanTests.lean` (the `testDriver` root) imports
each test module explicitly. As planned, `GebLean/Utilities/
FCEval.lean`, every `GebLean/PolyPRA/*.lean` file, and
`GebLeanTests/PolyPRA/Basic.lean` are imported by no built root
until Task 12 adds `import GebLean.PolyPRA` and Task 13 registers
the test module. Consequently the step cycle's steps 2, 5, and 6
(`lake build`, `lake test`, `bash scripts/pre-commit.sh`) and the
global axiom gate elaborate none of the new code in Tasks 1–11:
eleven commits of unverified Lean would pass every gate.

Fix: register at file creation. Task 1 adds
`import GebLeanTests.PolyPRA.Basic` to `GebLeanTests.lean` (or
creates a `GebLeanTests/PolyPRA.lean` index and registers that,
matching the `GebLeanTests/Binding` pattern) and creates
`GebLean/PolyPRA.lean` with `GebLean.lean` importing it; each
subsequent task appends its new module to `GebLean/PolyPRA.lean`
(`public import`, per the module-system rule) in the same commit
that creates the file. Remove the conditional phrasing from
Task 13.

## MAJOR findings

### A1. Task 5's Lean sketch does not elaborate as written

Task 5 Interfaces:

```lean
def PolyPRACat (C D) [Category C] [Category D] : Type _ :=
  InducedCategory (FCDirPRAObj C D) PolyPRAObj.forget
```

Three defects:

- `FCDirPRAObj` is defined nowhere; the task defines
  `FCDirPRACat`. The self-review checklist's verbatim-interface
  rule is violated within a single task.
- `PolyPRAObj.forget` is referenced but never declared;
  `PolyPRAObj` as sketched has fields `T1`, `E`, `witness` and no
  `forget`.
- The pinned mathlib's `InducedCategory` takes one explicit
  argument (`Mathlib/CategoryTheory/InducedCategory.lean:46`:
  `def InducedCategory (_F : C → D) : Type u₁`, with the target
  category implicit), so the two-argument application does not
  elaborate.

Fix: declare
`def PolyPRAObj.forget (P : PolyPRAObj C D) : FCDirPRACat C D`
(dropping `witness`), then
`def PolyPRACat (C D) ... := InducedCategory (D := FCDirPRACat C D) PolyPRAObj.forget`
(or `InducedCategory (PolyPRAObj.forget (C := C) (D := D))` with
the target inferred), and derive the forgetful functor as
`inducedFunctor` with `fullyFaithfulInducedFunctor` (both verified
present at the pin, `InducedCategory.lean:106`).

### A2. `elMap` is needed unconditionally but produced only conditionally

Task 5 Strategy: "`elMap α : FCElem T1 ⥤ FCElem T1'` is the
evident induced functor (add it to Task 3's file if reached)" —
i.e. only on the fallback route. But Task 7's comparison component
(spec § 6.4) factors `ε_ρ ∘ β_{m_Z(ρ)}` through the target
witnesses at the object `elMap α |>.obj (m_Z ρ)`; `β` itself has
type `(elMap α) ⋙ E' ⟶ E` in the plan's own Task 5 sketch. The
morphism layer of the formula category, the comparison functor,
and G2's recovery all consume `elMap` whichever route Task 5
takes.

Fix: move `elMap` (with its `@[simp]` object/projection lemmas
and at minimum `elMap_id` / `elMap_comp`, which Task 7's
functoriality chase needs) into Task 3 as an unconditional
deliverable, and add it to the self-review checklist's
interface-flow list.

### A3. Tasks 9–11 interfaces are placeholders; PRA evaluation unnamed

Task 9: `PolyPRACat C D ⥤ PresheafPRACat ...` and
`lemma polyPRAExtend_yoneda_simplification ...`; Task 10:
"`fcEvalCatFunctor D ⋙-compatible statement:`" (not Lean); Task
11: `theorem polyPRAExtendEval_faithful : ...`. The plan
convention (cf. the 2026-07-04 sub-plan's "Interfaces — Produces"
blocks) is exact signatures binding names and arities; `...`
bodies and non-Lean text are placeholders.

Additionally, Tasks 10–11 both consume "PRA evaluation" — Task 11
names the composite `PolyPRACat C D ⥤ (PSh C ⥤ PSh D)` — but no
consumed-interface entry or task produces the evaluation functor.
It already exists: `praEvalAtFunctor`
(`GebLean/PresheafPRA.lean:1387`,
`PresheafPRACat I J ⥤ (Iᵒᵖ ⥤ Type w_I) ⥤ (Jᵒᵖ ⥤ Type (max w' u_I w_I))`)
with `praEvalAtFunctorFullyFaithful` (`:1423`). The latter also
strengthens Task 11: with the second factor fully faithful,
faithfulness of the composite reduces to faithfulness of
`polyPRAExtend`.

Fix: list `praEvalAtFunctor` / `praEvalAtFunctorFullyFaithful` in
the consumed interfaces; restate Task 9's signature with
`PresheafPRACat`'s actual `(I J : Cat)` arguments and its six
universe parameters (mediated as needed, see A4); state Task 10's
`NatIso` between the two named composites in Lean; state Task 11's
theorem as `Functor.Faithful` of a named composite.

### A4. Universe handling defers spec § 10 item 4 against its own rule

Global constraints: "Each task states its universe parameters
explicitly". Tasks 4–13's sketches carry no universe annotations
at all, so the plan does not satisfy its own rule. Spec § 10
item 4 assigns universe alignment to "implementation planning"
and names the two concrete risks (`FP` raises the object
universe, so `C = FP(I)` is large and the witnesses'
`∀ Z : FC(C)` quantifies high; `familyNatTrans'` requires a
shared universe pair — confirmed at
`GebLean/Utilities/Families.lean:177`,
`{C D : Type u} [Category.{v} C] [Category.{v} D]`); the plan
answers with a generic executor-widens-with-`ULift` rule only.

One spot is not merely risky but unstatable as sketched: Task
10's `NatIso` legs land in different `Type` universes —
`polyPRAValue P ⋙ fcEvalCatFunctor D` in `Type (max w v_D)`,
the extension-evaluated leg in `Type (max w' u_C w_C)` (per
`praEvalAtFunctor`'s codomain) — so the statement itself needs
`uliftFunctor` / `catULiftFunctor2` mediation, not just its
proof.

Fix: add the universe parameters to each "Interfaces — Produces"
block (Tasks 1–2 already have them), and state where the lift
enters Task 10's two legs and Task 9's/Task 12's parameter
instantiations, per the spec's owner assignment.

### A5. Task 3's parallel elements category: reuse decision unrecorded

Task 3 defines `structure FCElem` with a bespoke category
instance. The spec (§ 6 preamble) prescribes the opposite
convention: "mathlib's `Functor.Elements` yields the opposite
orientation, so Lean statements carry an `op`". Beyond mathlib's
`Functor.Elements`, the repository already has oriented elements
infrastructure the plan neither consumes nor mentions:
`GebLean/Utilities/Elements.lean` defines
`Functor.ElementsContra'` (`:397`), `Functor.ElementsContra`
(`:423`, with `Category` instance), and `sliceEquivPresheaf`
(`:413`). `CLAUDE.md` § Rules ("Reuse existing abstractions.
... Instantiate the existing abstraction rather than defining a
parallel concept") makes silently defining a third elements
category a rule violation.

A bespoke flat structure is defensible here — `FCElem P`'s fields
give definitional access to `fcIndex`/`fcFamily` components that
`(fcToFunctor P).ElementsContra` would wrap in `Σ`-pairs — but
the plan must make the decision visibly, against the existing
alternatives.

Fix: either instantiate `Functor.ElementsContra` (or mathlib's
`Functor.Elements` plus `op`) at `fcToFunctor P` /
`(fcEvalCatFunctor D).obj P`, or keep `FCElem` and add a
standing-decision note recording why the existing abstractions
are not instantiated, adding `GebLean/Utilities/Elements.lean` to
the consumed-interfaces section either way.

### A6. Tasks 2–12 test steps carry no content

The step cycle's step 4 is "add the task's test declarations
under `GebLeanTests/PolyPRA/Basic.lean`", but only Tasks 1 and 13
state what any test declaration is; Tasks 2–12 say "tests as
above", which resolves to a file name, not to content. The format
precedent (2026-07-04 sub-plan) pins per-task test contracts. A
step whose content is unspecified is a placeholder under the
plan-format rules.

Fix: one concrete test expression per task suffices, following
the compositional-test rule — e.g. Task 2: `fcMap` of a named
two-element family along `Discrete PUnit ⥤ Discrete PUnit`,
checking index preservation by `rfl`; Task 3: `fcElTerminalHom`'s
factorization on the same family; Task 6: `polyPRASpectrum` of
the Task 13 identity-instance seed at a two-element `Z`, checked
against `Z` — with each value returned for reuse in Task 13.

### A7. The self-review checklist's verbatim-interface claim is false

Self-review checklist: "every interface consumed by a later task
is produced verbatim by an earlier one", with a flow list. The
claim fails on four names: `FCDirPRAObj` (consumed in Task 5's
own sketch, produced nowhere), `PolyPRAObj.forget` (same),
`elMap` (consumed by Tasks 5/7, produced only conditionally —
A2), and the PRA evaluation functor (consumed by Tasks 10–11,
neither listed nor produced — A3). The checklist also omits
Task 3's `fcElTerminalHom` → Task 13 and `factor_counit` →
Task 6 edges it relies on elsewhere.

Fix: re-run the checklist after B1/A1/A2/A3 are resolved and
extend the flow list to every consumed name.

## MINOR findings

### M1. Task 7's strategy sentence is garbled; composite order wrong

Task 7 Strategy: "component `τ_Z` at `ρ` is the factorization of
`E.map (…) ≫ counit … ≫ …` composite `counit Z ρ ≫ β`-transport
through the target witnesses". The sentence does not parse, the
`(…)` ellipses are placeholders, and `counit Z ρ ≫ β` is
ill-typed in either reading: with
`β_u : E'.obj (elMap α |>.obj u) ⟶ E.obj u` and
`counit Z ρ : E.obj (fcFamily (spec Z) ρ) ⟶ Z`, the spec § 6.4
composite `ε_ρ ∘ β_{m_Z(ρ)}` is, in Lean order,
`β (fcFamily (spec Z) ρ) ≫ counit Z ρ`.

Fix: replace the sentence with the precise composite and its
factorization target
(`witness'.factor Z (elMap α |>.obj (fcFamily (spec Z) ρ))`).

### M2. Task 1 citation drift against spec § 7

Task 1 Strategy: "the hom-set computation is the distributivity
`Π_b Σ_x Hom(G b, F x) ≅ Σ_r Π_b Hom(G b, F(r b))` (spec § 7 G3;
Dorta–Jarvis–Niu Proposition 2.4)". Spec § 7 attributes the
distributivity to "the Set instance of Dorta–Jarvis–Niu
Proposition 2.5; their Proposition 2.7 is the hom-set formula"
and Proposition 2.4 to the full faithfulness of the inclusion.
Step 1's docstring reference "spec § 6.4" also points away from
the inclusion, which the spec treats in §§ 2 and 7.

Fix: cite Proposition 2.4 for `fcEvalCatFullyFaithful`,
Proposition 2.5/2.7 for the distributivity, and spec §§ 2/7 in
the module docstring.

### M3. `polyPRAForget_fullyFaithful` must be a `def`, not a `theorem`

Task 5: "`theorem polyPRAForget_fullyFaithful : ...`".
`Functor.FullyFaithful` is a structure
(`Mathlib/CategoryTheory/Functor/FullyFaithful.lean:122`), i.e.
data, so the declaration must be a `def`, named in
`lowerCamelCase` per the naming conventions and the plan's own
Task 1/8 pattern (`fcEvalCatFullyFaithful`,
`polyPRAComparisonFullyFaithful`).

Fix: `def polyPRAForgetFullyFaithful : polyPRAForget.FullyFaithful
:= fullyFaithfulInducedFunctor _`.

### M4. Task 2's functor-equality laws need pointwise companions

Task 2 produces `fcMap_id : fcMap (𝟭 A) = 𝟭 _` and `fcMap_comp`
as functor equalities. Rewriting with functor equalities through
dependent `.map` occurrences requires `eqToHom` transport (the
repository's Cat-valued-functor pattern), and Tasks 6/10 rewrite
under `fcMap (fcElProj P.T1) |>.map`.

Fix: additionally produce the `@[simp]` pointwise lemmas the
consumers rewrite with (`fcMap_map_reindex`,
`fcMap_map_fiberMor`, or the `fcHomMk`-form
`fcMap p |>.map (fcHomMk r φ) = fcHomMk r (p.map ∘ φ)`), keeping
the equality laws as the functoriality record.

### M5. Task 4's binder sketch omits types that `autoImplicit = false` requires

Task 4: `factor : ∀ Z, ∀ u, (E.obj u ⟶ Z) → ...` and
`factor_spec : ∀ Z u (φ : E.obj u ⟶ Z), ...` leave `u`'s type
(`FCElem T1`) to inference from later use; with
`autoImplicit = false` project-wide, the sketch as written is not
the binding form the executor can transcribe.

Fix: annotate `u : FCElem T1` (and `Z : FreeCoprodCompletionCat
C`) in each field of the sketch.

### M6. The spec § 10 item 3 (O3) resolution is implicit, never recorded

Spec § 10 item 3 assigns "which mathlib mechanism expresses the
G4 restriction" to implementation planning. Task 10 answers it —
"packaged as a NatIso between the two composites
`FC(C) ⥤ PSh(D)`", the spec O3's commuting-square-up-to-NatIso
option — but nowhere says it is resolving that open question.

Fix: add a standing-decisions line (the format precedent has a
"Standing decisions recorded by this sub-plan" section): O3 /
spec § 10 item 3 is resolved as the specified-NatIso square;
`ObjectProperty.lift`-style lifting is not used.

### M7. Commit-message constraint omits the repository trailer convention

Global constraints: "Commit messages: mathlib convention,
imperative, lowercase subject, no trailing period; commit via
`jj commit`." The repository additionally ends commit messages
with a `Co-Authored-By:` trailer (the 2026-07-04 sub-plan's
global constraints spell this out), which executing subagents
will not know from this plan alone.

Fix: append the trailer requirement (with the current model
attribution) or an explicit pointer to the `CLAUDE.md` tooling
rule.

### M8. Conditional phrasing in file-structure and registration steps

"Modify `GebLean.lean` (or the repository's root index)" — the
root index is `GebLean.lean` (verified); the alternative is a
placeholder. "register the test module in the test index if the
repository requires it" — it does (`lakefile.toml`:
`testDriver = "GebLeanTests"`; `GebLeanTests.lean` imports each
test module). Both edits should be stated exactly; their timing
is B2.

Fix: name the files and the exact import lines added, moved to
the tasks B2 assigns them to.

## NIT findings

### N1. Misplaced provenance parenthetical in the consumed-interfaces list

Consumed interfaces: "`familyFunctor'`, `familyNatTrans'`,
`familyPostcomp'`, `GrothendieckContra'` (via
`GebLean/Utilities/Grothendieck.lean`)" — the bullet sits under
"From `GebLean/Utilities/Families.lean`", and only
`GrothendieckContra'` lives in `Grothendieck.lean` (`:1567`); the
other three are in `Families.lean` (`:107`, `:177`, `:129`).

Fix: scope the parenthetical to `GrothendieckContra'` alone.

### N2. Task 8's fallback commit has no commit message

Task 8: "land (a) first as its own commit
(`polyPRAComparison_faithful : Functor.Faithful …`)" gives the
declaration but not the commit message the step cycle
substitutes.

Fix: add it, e.g.
`feat(polypra): prove the comparison functor faithful`.

## Verified without defect

- Consumed-interface existence: every listed identifier resolves
  in the tree — `FreeCoprodCompletionCat`
  (`GebLean/Utilities/Families.lean:732`) with `fcObjMk` (`:807`),
  `fcIndex` (`:813`), `fcFamily` (`:818`), `fcHomMk` (`:836`),
  `fcReindex` (`:845`), `fcFiberMor` (`:853`), `fcHom_ext`
  (`:871`), `fcId_mk` (`:919`), `fcComp_mk` (`:929`); `fcEval`
  (`:1841`) matching the quoted `Σ`-formula, `fcEvalIndex`
  (`:1846`), `fcEvalMor` (`:1851`), `fcEvalMk` (`:1858`),
  `fcEval_ext` (`:1881`), `fcEvalMap` (`:1906`), `fcToFunctor`
  (`:1951`, `Cᵒᵖ ⥤ Type _` as described);
  `FreeProdCompletionCat` (`:745`), `FreeCoprodProdCat`
  (`:2485`), `CoprodCovarRepSquaredCat` (`:2506`), `fcpCcrsIso`
  (`:3010`), `fcpCcrsEquiv` (`:3018`); `CoprodCovarRepCat`
  (`:386`), `coprodCovarRepFunctor` (`:370`, `Cat ⥤ Cat`),
  `ccrNewEvalCatFunctor` (`:611`), `ccrNewEvalCatFullyFaithful`
  (`:676`); `familyFunctor'` (`:107`), `familyNatTrans'`
  (`:177`), `familyPostcomp'` (`:129`); `GrothendieckContra'`
  (`GebLean/Utilities/Grothendieck.lean:1567`, with `.map` used
  downstream); `catULiftFunctor2` (`Families.lean:3309`);
  `presheafCatFunctor` (`GebLean/PresheafPRA.lean:46`),
  `ccrPresheafCatFunctor` (`:65`), `PresheafPRACat` (`:139`,
  objects as the plan quotes), `praEvalAt` (`:1436`) and the
  `praEvalAt_index`/`_mor`/`_mk` accessors (`:1442–:1461`).
- Mathlib names at the pin: `Functor.FullyFaithful`
  (structure), `InducedCategory` (single explicit argument — see
  A1), `inducedFunctor` / `fullyFaithfulInducedFunctor`
  (`InducedCategory.lean:106`), `Functor.Elements`
  (`Elements.lean:48`) all exist.
- Task 1's model claim: `ccrNewEvalCatFunctor` /
  `ccrNewEvalCatFullyFaithful` are Yoneda-element/preimage
  constructions of exactly the shape Task 1 transcribes, and the
  stated codomain `Cᵒᵖ ⥤ Type (max w v_C)` matches the covariant
  model's `C ⥤ Type (max w v)`.
- Task 3's morphism orientation (`e.hom = v ≫ e'.hom`,
  `e.idx = e'.idx`) matches spec § 6's elements orientation.
- Task 4 transcribes spec § 6.2 as amended by spec-review r1 F4
  (verified: r1 F4 is the witness-structure-versus-predicate
  finding); `factor` is data, uniqueness Prop-valued;
  `factor_counit` follows from `factor_unique` at `v = 𝟙`.
- Task 6's strategy matches spec § 6.4 (functor laws of `T`/`M`
  from uniqueness of factorizations; identity via
  `factor_counit`); Task 8's matches § 7 G2 (generic elements
  retract identities), is flagged as the highest-difficulty task,
  and carries a faithfulness-first decomposition fallback — the
  risk ordering asked for. The spec reviews' verification records
  exist (r1 § Verification record, r2 § Verification record) and
  cover the § 6.4 instance checks the plan cites.
- Commit messages: all thirteen task messages scanned against the
  re-fetched mathlib commit convention
  (`leanprover-community.github.io/contribute/commit.html`):
  types `feat`/`test` are in the allowed list; subjects are
  imperative present tense, lowercase first letter, no trailing
  period, under 72 characters ("Poly" in Task 13's message is the
  category's proper name). No violations.
- Plan hygiene: `markdownlint-cli2` reports 0 errors on the plan;
  `doctoc --dryrun --update-only` reports the TOC current; the
  topic branch `feat/poly-preserving-pra` exists at `82e6d79a`.
- Process: pre-commit triad, axiom gate, `sorry`/underscore
  discipline, and the `jj commit` cycle are all present in the
  global constraints and step template (their effectiveness for
  Tasks 1–11 is B2).

## Verification record

- Read in full: the plan; the spec; `CLAUDE.md`;
  `.claude/rules/lean-coding.md`;
  `.claude/rules/markdown-writing.md`; the format precedent
  `docs/superpowers/plans/2026-07-04-ramified-p6-soundness-subplan.md`
  (through Global constraints).
- Re-fetched
  `https://leanprover-community.github.io/contribute/commit.html`
  and scanned all plan commit messages against it.
- Grepped every consumed identifier to its declaration site in
  `GebLean/Utilities/Families.lean`,
  `GebLean/Utilities/Grothendieck.lean`, and
  `GebLean/PresheafPRA.lean` (line numbers above); read the
  declarations of `fcEval`, `fcToFunctor`, `coprodCovarRepFunctor`,
  `PresheafPRACat`, `praEvalAtProfunctor`/`praEvalAtFunctor`/
  `praEvalAtBifunctor` (+ FullyFaithful forms),
  `ccrNewEvalCatFunctor`, and `ccrNewEvalCatFullyFaithful` in
  full.
- Checked the pinned mathlib sources for `InducedCategory`
  (signature and argument order), `fullyFaithfulInducedFunctor`,
  `Functor.FullyFaithful`, and `Functor.Elements` under
  `.lake/packages/mathlib`.
- Inspected `lakefile.toml` (lib roots/globs, `testDriver`),
  `GebLean.lean`, `GebLeanTests.lean`, and the `GebLeanTests/`
  layout for the registration analysis (B2).
- Inspected `GebLean/Utilities/Elements.lean`'s declaration list
  for the existing elements-category infrastructure (A5).
- Confirmed spec-review r1 finding F4 and both reviews'
  verification-record sections; skimmed r2's record for the O7
  and § 6.4 confirmations the plan cites.
- Ran `markdownlint-cli2` and `doctoc --dryrun --update-only` on
  the plan; confirmed `feat/poly-preserving-pra` via
  `jj bookmark list`.
- Not verified: the informal correctness of the § 6.4/§ 7
  mathematics itself (converged at spec review); the buildability
  of any sketched signature (no Lean was elaborated for this
  review).

## Verdict

Another round required. B1 (route/interface incoherence across
Tasks 5–9) and B2 (registration timing nullifying every per-task
gate) must be resolved before execution; the MAJOR findings are
localized rewrites of individual task blocks and the checklist.
