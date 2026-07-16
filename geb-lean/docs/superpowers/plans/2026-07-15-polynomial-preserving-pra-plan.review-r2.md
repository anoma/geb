# Adversarial review: polynomial-preserving PRA plan (round 2)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary](#summary)
- [r1 fix verification](#r1-fix-verification)
- [MAJOR findings](#major-findings)
  - [R2-A1. The `public import` registration lines do not elaborate at this pin](#r2-a1-the-public-import-registration-lines-do-not-elaborate-at-this-pin)
  - [R2-A2. The identity-instance test seed has contradictory base categories](#r2-a2-the-identity-instance-test-seed-has-contradictory-base-categories)
- [MINOR findings](#minor-findings)
  - [R2-M1. Task 5's `InducedCategory` prose claim is false at the pin](#r2-m1-task-5s-inducedcategory-prose-claim-is-false-at-the-pin)
  - [R2-M2. `fcDirToCCR`'s direction layer is misattributed in two places](#r2-m2-fcdirtoccrs-direction-layer-is-misattributed-in-two-places)
- [NIT findings](#nit-findings)
  - [R2-N1. The trailer requirement cites a section that does not contain it](#r2-n1-the-trailer-requirement-cites-a-section-that-does-not-contain-it)
  - [R2-N2. Checklist edge from `fcElTerminalHom` to Task 13 has no consumer](#r2-n2-checklist-edge-from-fcelterminalhom-to-task-13-has-no-consumer)
  - [R2-N3. "§ 6.2 tower" names the packed datum, not § 6.2's tower](#r2-n3--62-tower-names-the-packed-datum-not--62s-tower)
- [Verified without defect](#verified-without-defect)
- [Verification record](#verification-record)
- [Verdict](#verdict)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Verdict: CONVERGED after the listed fixes (0 BLOCKER, 2 MAJOR,
2 MINOR, 3 NIT); no further review round required before user
review, provided the two MAJOR fixes are applied as prescribed.

Target:
`docs/superpowers/plans/2026-07-15-polynomial-preserving-pra-plan.md`
at bookmark `feat/poly-preserving-pra` (`ef0aa3f7`,
`doc(plans): apply adversarial review r1 findings`). Round-1
review:
`docs/superpowers/plans/2026-07-15-polynomial-preserving-pra-plan.review-r1.md`.
Spec (§ 8 deliverable 2 amended on this branch as part of the B1
fix):
`docs/superpowers/specs/2026-07-14-polynomial-preserving-pra-design.md`.
Scope: verification that every r1 finding's fix is correctly and
completely applied, plus a fresh-eyes pass over the reworked
sections for defects introduced by the fixes.

## Summary

The r1 fixes are substantially applied: Task 5 now presents the
`⟨T1, E⟩` structure unconditionally with a correct
`InducedCategory` witness layer, `elMap` is an unconditional
Task 3 deliverable, Tasks 9–11 carry exact Lean signatures with
`praEvalAtFunctor` consumed by name, every task states its
universe parameters (spot-checked coherent against the actual
`Families.lean` / `PresheafPRA.lean` signatures, including the
Task 9 `PresheafPRACat` instantiation, the Task 10 two-leg
alignment at `Type (max w u_C v_C v_D)`, and the Task 12 `FP`
parameter bumps), the standing-decisions section records B1, O3,
and the elements-category reuse decision, per-task test contracts
exist, the checklist is rewritten, and the trailer, citation,
naming, and phrasing corrections (M1–M5, M7–M8, N1–N2) are in
place. The amended spec § 8 deliverable 2 is internally
consistent with §§ 6.2–6.3 and with the plan's standing
decision 1. Two defects introduced by the fixes remain: the
registration lines prescribed by the B2 fix use `public import`,
which does not elaborate at this pin (verified by build — the
new files cannot be `module`s because the module system rejects
imports of the non-module `GebLean` tree, and `public import`
is rejected outside a `module`); and the A6 fix's
identity-instance test seed is stated over two contradictory
base categories, making Task 6's and Task 13 (b)'s expected
values false in one of the two readings. Both fixes are
localized rewrites of the affected lines.

## r1 fix verification

| r1 finding | Status | Notes |
| --- | --- | --- |
| B1 (route/interface incoherence) | Fixed | `⟨T1, E⟩` unconditional in Task 5; `fcDirToCCR` assigned to Task 9; spec § 8 deliverable 2 amended consistently; residual phrasing defect is finding R2-M2 |
| B2 (registration timing) | Fixed incorrectly in one detail | Registration at creation, exact files and lines, per-task gates non-vacuous; but the prescribed `public import` lines do not elaborate — finding R2-A1 |
| A1 (Task 5 sketch) | Fixed | `FCDirPRACat` named consistently; `PolyPRAObj.forget` declared; `InducedCategory (D := …)` elaborates; residual prose error is finding R2-M1 |
| A2 (`elMap` conditional) | Fixed | Unconditional in Task 3 with `@[simp]` lemmas, `elMap_id` / `elMap_comp`; checklist edge present |
| A3 (Tasks 9–11 placeholders) | Fixed | Exact Lean signatures; `praEvalAtFunctor` / `praEvalAtFunctorFullyFaithful` consumed with verified locations (`:1387`, `:1423`) and correct universe instantiation |
| A4 (universe deferral) | Fixed | Per-task universe parameters; Task 10 lift mediation stated and verified statable (`uliftFunctor.{max u_C v_C, max w v_D}` aligns both legs); Task 9/12 mediation points identified |
| A5 (elements reuse) | Fixed | Standing decision 3; `Elements.lean` consulted-not-instantiated entry with verified line numbers (`:397`, `:413`, `:423`) |
| A6 (test steps) | Fixed incompletely | Per-task test contracts present and mostly well-typed-plausible; the identity-seed configuration is self-contradictory — finding R2-A2 |
| A7 (checklist claim) | Fixed | Flow list extended and re-verified; one unconsumed edge remains — finding R2-N2 |
| M1 (Task 7 strategy) | Fixed | Precise composite `β.app (fcFamily (P.witness.spec Z) ρ) ≫ P.witness.counit Z ρ`, factorization target stated; typing re-derived and correct |
| M2 (citation drift) | Fixed | Proposition 2.4 for full faithfulness, 2.5/2.7 for distributivity, spec §§ 2/7 in the docstring |
| M3 (`def` not `theorem`) | Fixed | `def polyPRAForgetFullyFaithful` |
| M4 (pointwise companions) | Fixed | `fcMap_map_reindex` / `fcMap_map_fiberMor` / `fcMap_map_mk` with the `eqToHom` rationale |
| M5 (binder types) | Fixed | All Task 4 fields fully annotated |
| M6 (O3 unrecorded) | Fixed | Standing decision 2 |
| M7 (trailer) | Fixed | Trailer text stated inline; its citation is inaccurate — finding R2-N1 |
| M8 (conditional phrasing) | Fixed | Exact files and import lines; no conditional registration language remains |
| N1 (provenance) | Fixed | `GrothendieckContra'` scoped to `Grothendieck.lean` (`:1567` verified) |
| N2 (fallback commit message) | Fixed | `feat(polypra): prove the comparison functor faithful` |

## MAJOR findings

### R2-A1. The `public import` registration lines do not elaborate at this pin

File structure: "`GebLean/PolyPRA.lean` (initial content:
`public import GebLean.Utilities.FCEval`)"; "Every task that
creates a `GebLean/PolyPRA/<Name>.lean` module appends the line
`public import GebLean.PolyPRA.<Name>` to `GebLean/PolyPRA.lean`";
repeated in Tasks 1, 3, 4, 5, 6, 7, 9, and 12.

Verified by building both variants at the pin
(`leanprover/lean4:v4.29.0-rc6`):

- A file containing `public import GebLean.Utilities.Families`
  without the `module` keyword fails with
  `cannot use 'public', 'meta', or 'all' without 'module'`.
- A file declaring `module` first fails with
  `cannot import non-`module` GebLean.Utilities.Families from
  `module``.

No file under `GebLean/` or `GebLeanTests/` declares `module`
(the four grep hits for `^module` are docstring text), so every
new file in this plan transitively imports non-`module` files
and cannot itself be a `module`; `public import` is therefore
unavailable to it. The `.claude/rules/lean-coding.md` § Lean 4
module system rule the plan cites is unsatisfiable for files
that import the existing `GebLean` tree.

Fix: state the registration lines as plain `import` (matching
the `GebLean/Binding.lean` and `GebLeanTests/Binding.lean` index
precedents and the `GebLean.lean` / `GebLeanTests.lean` roots),
in File structure and in each task's Files block, and record the
deviation from the module-system rule with the one-sentence
reason above (a rule correction, if desired, is a separate
branch per the one-concern rule).

### R2-A2. The identity-instance test seed has contradictory base categories

Task 4 Test: "build the identity-instance witness seed over
`C = D = Discrete PUnit` (`T1` a named two-index family, `E` the
evident functor of Task 13 (b))". Task 13 (b): "`E` the evident
`FCElem T1 ⥤ FC C` at `T1 = fcObjMk (fun i => c_i)` over a
discrete two-object `C` with witnesses from Task 4's
`factor_counit` seed". Task 5 Test packages the Task 4 seed as
"a named `PolyPRAObj (Discrete PUnit) (Discrete PUnit)`";
Task 6 Test checks "`polyPRASpectrum` of the Task 13
identity-instance seed … at a named two-element `Z`, checked
against `Z` (index-level `rfl`)"; Task 13 (b) checks
"`example : polyPRAValue _ |>.obj Z = Z` up to
`fcHom_ext`-level isomorphism".

The two descriptions of the single shared seed disagree on the
base category (`Discrete PUnit` versus a discrete two-object
`C`), and the `Discrete PUnit` reading falsifies the downstream
checks: over the point, a two-index `T1` with the evident
(Yoneda-style) directions is the polynomial `Z ↦ Z ⊔ Z`, not the
identity — its spectrum at a two-element `Z` has four indices
(one per pair of a position and an element of `Z`), so Task 6's
"checked against `Z`" fails, and Task 13 (b)'s
`polyPRAValue _ |>.obj Z = Z` fails. The two-object reading is
the identity instance (`el(T1) ≅ C`, `E = y`, spectrum index
`≅ fcIndex Z`), but then Task 4's and Task 5's stated categories
are wrong and Task 13 (b)'s "witnesses from Task 4's … seed"
is a type mismatch.

Fix: pick one configuration and apply it across Tasks 4, 5, 6,
and 13 (b). Either (a) the two-object form:
`C = D = Discrete (Fin 2)`, `T1 = fcObjMk` enumerating the two
objects, updating Task 4's "over `C = D = Discrete PUnit`" and
Task 5's `PolyPRAObj (Discrete PUnit) (Discrete PUnit)` (the
Task 6 and 13 (b) checks then hold as stated); or (b) the
one-index form over `C = D = Discrete PUnit`
(`T1 = fcObjMk (fun _ : PUnit => ⟨⟨⟩⟩)`), updating Task 4's
"two-index" and Task 13 (b)'s "discrete two-object `C`". Task
13 (a) (the two-position `Poly`-count object over
`Discrete PUnit`) is unaffected either way.

## MINOR findings

### R2-M1. Task 5's `InducedCategory` prose claim is false at the pin

Task 5 Strategy: "The pinned mathlib's `InducedCategory` takes a
single explicit argument with the target category implicit
(`Mathlib/CategoryTheory/InducedCategory.lean:46`)". At the pin
the binder context is
`variable {C : Type u₁} (D : Type u₂) [Category.{v} D]` with
`def InducedCategory (_F : C → D) : Type u₁` — the target
category `D` is an explicit argument (`InducedCategory D F`, as
its docstring writes). The sketched usage
`InducedCategory (D := FCDirPRACat.{u_C, v_C, u_D, v_D, w} C D)
PolyPRAObj.forget` still elaborates (a named argument may fill
an explicit parameter), so only the prose misdescribes the
signature; an executor believing it could omit the argument
where the named form is not used.

Fix: replace "with the target category implicit" with "with the
target category as a preceding explicit variable, fillable by
name (`D := …`)".

### R2-M2. `fcDirToCCR`'s direction layer is misattributed in two places

Standing decision 1: "Task 9's conversion functor `fcDirToCCR`
into the unrestricted formula category (elements unpacking on
positions; `coprodCovarRepFunctor.map` on Task 1's inclusion for
directions)". Task 9 Strategy: "`fcDirToCCR` carries the
elements unpacking of positions directly, and its direction
layer is `coprodCovarRepFunctor.map` applied to Task 1's
inclusion (standing decision 1)".

Both sentences contradict `fcDirToCCR`'s stated signature, whose
codomain is
`Dᵒᵖ ⥤ CoprodCovarRepCat … (FreeCoprodCompletionCat.{u_C, v_C, w} C)`
— directions remain in `FC(C)`, and the signature's own comment
says so ("directions `P.E.obj ⟨d, i, h⟩`"). The
`coprodCovarRepFunctor.map` whiskering along Task 1's inclusion
belongs to `polyPRAExtend` (as its definition comment and the
rest of the Strategy paragraph correctly state). Likewise
"into the unrestricted formula category" misnames `fcDirToCCR`'s
codomain: the unrestricted formula category is `PresheafPRACat`
(directions in `PSh(C)`; spec §§ 6.3, 8); the codomain here is
the `FC(C)`-directed CCR presentation.

Fix: in both places, state `fcDirToCCR` as the conversion into
the `FC(C)`-directed CCR presentation with direction layer the
direct `P.E.obj` assignment, and assign the
`coprodCovarRepFunctor.map`-on-the-inclusion whiskering (with
its `catULiftFunctor2` mediation) to `polyPRAExtend`.

## NIT findings

### R2-N1. The trailer requirement cites a section that does not contain it

Global constraints: "each message ends with the repository
trailer … (see `CLAUDE.md` § Tooling and the repository git
convention)". `CLAUDE.md` § Tooling contains no commit-trailer
rule (no `Co-Authored-By` occurrence in `CLAUDE.md`,
`.claude/rules/*.md`, or `docs/process.md`). The trailer text
itself is stated correctly inline, so only the citation is
inaccurate.

Fix: drop the `CLAUDE.md` § Tooling pointer (the format
precedent `docs/superpowers/plans/2026-07-04-ramified-p6-soundness-subplan.md`
states the trailer inline without one), or cite it as "the
repository git convention" alone.

### R2-N2. Checklist edge from `fcElTerminalHom` to Task 13 has no consumer

Self-review checklist: "`fcElTerminalHom` (Task 3) → Task 13".
Task 13's contents do not mention `fcElTerminalHom`; its only
stated consumer is Task 3's own test. The edge as written
re-introduces (in one entry) the inaccuracy A7 removed.

Fix: either name the Task 13 test step that consumes
`fcElTerminalHom` or re-point the edge to Task 3's test,
retaining the deliverable on its spec § 6.2 (slice-terminality)
justification.

### R2-N3. "§ 6.2 tower" names the packed datum, not § 6.2's tower

Architecture and standing decision 1 (and the amended spec § 8
deliverable 2) say the formula category is "presented directly
by the § 6.2 tower (positions, directions, witnesses)". Spec
§ 6.2 reserves "the tower" for the unpacked per-position form
(`S`, `k`, `B_s`, `G_s`, per-position witnesses); the plan's
`FCDirPRACat` / `PolyPRAObj` implement the packed
`(T1, E, witnesses)` datum, not that unpacking. The
parentheticals make the intent recoverable, so this is
terminology only.

Fix: say "the § 6.2 formula datum (positions, directions,
witnesses)" in the two plan occurrences and, on the same
branch, in the amended spec sentence.

## Verified without defect

- Root registration conventions: `GebLean.lean` and
  `GebLeanTests.lean` import each module explicitly with plain
  `import`; `lakefile.toml` declares no `globs` for either
  library and `testDriver = "GebLeanTests"`; the plan's Task 1
  registration files and lines are exactly right apart from the
  `public` keyword (R2-A1).
- Spec § 8 deliverable 2 amendment: internally consistent with
  §§ 6.2–6.3 (witness layer as an induced category over the
  witness-free presentation matches § 6.3's fully-faithful
  forgetful-functor remark; the conversion-functor clause
  matches standing decision 1 and Task 9's decomposition), and
  with G2–G5 unchanged. Residues are R2-M2 (plan phrasing) and
  R2-N3 (shared terminology).
- Universe annotations, spot-checked against the sources:
  - `FreeCoprodCompletionCat.{u', v', w'} C' :
    Cat.{max w' v', max (w' + 1) u' w'}` (`Families.lean:732`)
    — Task 9's claim that `FC C` is an object of
    `Cat.{max w v_C, max (w + 1) u_C w}` is exact, and the
    `CoprodCovarRepCat.{max (w + 1) u_C w, max w v_C, max w v_D}`
    instantiation matches `CoprodCovarRepCat`'s `(u, v, w)` =
    (object, hom, index) parameter order (`:386`).
  - `presheafCat : Cat.{max u_I w_I, max v_I (w_I + 1) u_I}`
    (`PresheafPRA.lean:55`) — Task 9's
    `Cat.{max u_C w v_C, max v_C (max w v_C + 1) u_C}` at
    `w_I = max w v_C` is exact, and `catULiftFunctor2`
    (`Families.lean:3309`, `Cat.{v, u} ⥤ Cat.{max v w_v, max u w_u}`)
    can bridge the two pairs as the Strategy states.
  - `praEvalAtFunctor` (`PresheafPRA.lean:1387`) and
    `praEvalAtFunctorFullyFaithful` (`:1423`) quoted verbatim;
    at the plan's instantiation
    `(u_C, v_C, u_D, v_D, max w v_C, max w v_D)` the codomain is
    `(Cᵒᵖ ⥤ Type (max w v_C)) ⥤ (Dᵒᵖ ⥤ Type (max w u_C v_C v_D))`,
    matching Tasks 10 and 11 exactly.
  - Task 10's legs: `uliftFunctor.{u, v} : Type v ⥤ Type (max u v)`
    (first parameter the lift amount — confirmed against mathlib
    usage at the pin), so
    `uliftFunctor.{max u_C v_C, max w v_D}` lands the value leg
    in `Type (max w u_C v_C v_D)`, equal to the extension leg's
    universe; the `NatIso` is statable as written.
  - Task 6 against Tasks 2–4: `FCElem P : Type (max u_D v_D w)`
    with `Category.{v_D}` feeds
    `FreeCoprodCompletionCat.{max u_D v_D w, v_D, w} (FCElem P.T1)`
    (spectrum codomain and `witness.spec` agree), and
    `fcMap (fcElProj P.T1)` at `(u_A, v_A) = (max u_D v_D w, v_D)`,
    `(u_B, v_B) = (u_D, v_D)` gives `polyPRAValue` its stated
    signature by composition.
  - Task 12's `u_C := max (w + 1) u_I w`, `v_C := max w v_I`
    match `FreeProdCompletionCat.{u_I, v_I, w} I`'s `Cat` pair
    (`Families.lean:745`).
  - `FCDirPRACat` / `PolyPRAObj` at
    `Type (max u_C u_D v_C v_D (w + 1))` and
    `PolyPRACat := InducedCategory …` at the same universe
    (`InducedCategory (_F : C → D) : Type u₁`) are coherent.
- Task 4's field types, `factor_counit`'s statement, Task 7's
  comparison composite, and Task 9's `polyPRAExtendYonedaEquiv`
  all re-derived as well-typed (the `Equiv` is
  universe-heterogeneous, so the differing sides elaborate);
  `praEvalAt C D P Z d` matches `praEvalAt`'s argument order
  (`PresheafPRA.lean:1436`), and `praEvalAt_index` (`:1442`)
  exists for Task 10's test.
- Per-task test contracts (Tasks 1–3, 7–12, 13 (a)) are
  plausible over `Discrete PUnit`-sized data and follow the
  compositional-test rule; only the identity seed is defective
  (R2-A2).
- Consulted-not-instantiated entries: `Functor.ElementsContra'`
  (`Elements.lean:397`), `sliceEquivPresheaf` (`:413`),
  `Functor.ElementsContra` (`:423`); `GrothendieckContra'`
  (`Grothendieck.lean:1567`).
- The rewritten self-review checklist's deliverable map (Tasks
  1, 5+9, 2+6+7, 12; G2–G5 → Tasks 8–11) and interface-flow
  edges check out against the task blocks, except R2-N2.
- Commit messages: the fourteen messages (thirteen tasks plus
  Task 8's fallback) re-scanned against the re-fetched mathlib
  commit convention; imperative present tense, lowercase
  subjects, no trailing periods, in-list types, under 72
  characters.
- Plan hygiene: `markdownlint-cli2` reports 0 errors on the
  plan; `doctoc --dryrun --update-only` reports the TOC current.
- Style: no colloquialisms, value-laden adjectives, or
  state-judgment words found in the reworked sections; no
  dangling references to the removed Task 5 fallback route; no
  `...`-placeholder regressions beyond the annotated
  `@[simp]`-lemma lists already present at r1 granularity.

## Verification record

- Read in full: the plan; the r1 review; the spec (including the
  amended § 8); `CLAUDE.md`; `.claude/rules/lean-coding.md`;
  `.claude/rules/markdown-writing.md`; `GebLean.lean`;
  `GebLeanTests.lean`; `lakefile.toml`.
- Built two probe files at the pin to test the registration
  mechanism (`module` + `public import` of
  `GebLean.Utilities.Families`, and `public import` without
  `module`); both fail with the errors quoted in R2-A1; probe
  files removed, working copy confirmed clean.
- Read the declarations of `FreeCoprodCompletionCat`,
  `FreeProdCompletionCat`, `CoprodCovarRepCat`,
  `coprodCovarRepFunctor`, `fcObjMk` … `fcFamily`, `fcToFunctor`,
  `catULiftFunctor2` in `GebLean/Utilities/Families.lean`;
  `presheafCatFunctor`, `presheafCat`, `ccrPresheafCatFunctor`,
  `PresheafPRACat`, `praEvalAtProfunctor` / `praEvalAtFunctor`
  (+ FullyFaithful forms), `praEvalAt` and its accessors in
  `GebLean/PresheafPRA.lean`; `GrothendieckContra'` and the
  `Elements.lean` declarations at their cited lines.
- Read the pinned mathlib's `InducedCategory.lean` (binder
  context and `inducedFunctor` / `fullyFaithfulInducedFunctor`)
  and `Types/Basic.lean` (`uliftFunctor`), and grepped mathlib
  and repository usage for `uliftFunctor.{…}` argument order.
- Grepped `GebLean/` and `GebLeanTests/` for `^module` and
  `^public import` (no module-system usage; the four `^module`
  hits are docstring text).
- Re-derived the universe arithmetic for Tasks 3–6, 9–12 and the
  typing of Task 4's fields, Task 7's comparison composite, and
  Task 9's `Equiv`.
- Computed the identity-seed spectra by hand in both readings of
  the seed configuration (R2-A2).
- Ran `markdownlint-cli2` and `doctoc --dryrun --update-only` on
  the plan and on this review.
- Not verified: buildability of the planned signatures beyond
  the two registration probes (no other Lean was elaborated);
  the informal § 6.4/§ 7 mathematics (converged at spec review).

## Verdict

Converged after fixes. R2-A1 and R2-A2 are localized,
mechanically checkable rewrites (import-line keyword; one seed
configuration applied across four task test contracts); the
MINOR and NIT items are single-sentence corrections. None
affects the task decomposition, interfaces, or proof strategies,
so no further adversarial round is required before user review.
