# praDirections v2 Follow-Ups Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Land four small follow-ups deferred from the praDirections
v2 workstream: tighten `maxHeartbeats`, refactor `catULiftFunctor` as
a specialization of `catULiftFunctor2`, narrow `uliftCategory`'s
local-instance scope, and add a propositional bridge theorem
connecting `praDirectionsAt` to `praPolyDirectionsFunctor`.

**Architecture:** Four independent items, each producing a small
focused commit (or two for the bridge theorem to keep diffs small).
The first three are localized refactors; the fourth adds a public
helper plus a `simp` theorem.

**Tech Stack:** Lean 4, mathlib (category theory, presheaf
categories, Grothendieck construction).  Project rules from
`CLAUDE.md` apply throughout (no `sorry`/`admit`/`axiom`/
`noncomputable`/`classical`, lines ≤80, no forbidden style words,
`lake build` + `lake test` clean with zero warnings before each
commit).

**Spec:** `docs/superpowers/specs/2026-04-25-praDirections-followups-design.md`

---

## File Structure

| File | Tasks touched |
| ---- | ------------- |
| `GebLean/PresheafPRA.lean` | 1, 3, 4, 5 |
| `GebLean/Utilities/Families.lean` | 2 |
| `GebLeanTests/Utilities/PresheafPRADirNat.lean` | 5 (test) |

Per-task summary:

- Task 1: `maxHeartbeats` change in `PresheafPRA.lean`.
- Task 2: `catULiftFunctor` body refactor in `Families.lean`.
- Task 3: `uliftCategory` scope narrowing in `PresheafPRA.lean`.
- Task 4: `praPolyDirectionsAtSourceObj` helper in `PresheafPRA.lean`.
- Task 5: bridge theorem in `PresheafPRA.lean` + test in
  `PresheafPRADirNat.lean`.

No new files are created.

---

## Task 1: Tighten `maxHeartbeats` to `400000`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — two `set_option maxHeartbeats
  800000 in` declarations near the Task 7.9 helpers (around lines
  869 and 930).

- [ ] **Step 1: Locate the two declarations**

Run:

```bash
grep -n "set_option maxHeartbeats" GebLean/PresheafPRA.lean
```

Expected: two matches, one above
`praPolyDirectionsData_baseHomComp_unwidened_aux` and one above
`praPolyDirectionsData_baseHomComp_unwidened`.

- [ ] **Step 2: Change both `800000` to `400000`**

For each of the two matches, change `set_option maxHeartbeats 800000
in` to `set_option maxHeartbeats 400000 in`.  The accompanying
linter-required `--`-comment line stays unchanged.

- [ ] **Step 3: Build to verify the new bound suffices**

Run: `lake build`

Expected: clean build (1444 jobs, no warnings).  If a `(deterministic)
timeout at whnf` error appears at one of the two declarations,
escalate that one's value: try `500000` first, then `600000`, and
finally `800000` (revert).  The other should remain at `400000`
unless it also fails.

- [ ] **Step 4: Run tests**

Run: `lake test`

Expected: clean (1467 jobs, exit 0).

- [ ] **Step 5: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: tighten maxHeartbeats to 400000 for Task 7.9 helpers"
```

(No `Co-Authored-By` trailer.)

---

## Task 2: Refactor `catULiftFunctor` as specialization of `catULiftFunctor2`

**Files:**

- Modify: `GebLean/Utilities/Families.lean` — `def catULiftFunctor`
  body at lines 3281–3297.  May also need a localized fix at the
  `unfold catULiftFunctor` proof site at line 3514.
- [ ] **Step 1: Inspect the current body**

Read `GebLean/Utilities/Families.lean` lines 3273–3297.  The current
`catULiftFunctor` body is an explicit `where`-clause definition
with `obj`, `map`, `map_id`, `map_comp` fields.  Note the universe
parameters `w w_v w_u` declared at line 3259 — only `w` is actually
used by this definition.

- [ ] **Step 2: Verify the universe order of `catULiftFunctor2`**

Read lines 3306–3322 of the same file.  `catULiftFunctor2 :
Cat.{v, u} ⥤ Cat.{max v w_v, max u w_u}` — universe parameters in
order `v, u, w_v, w_u` (matching the `universe w w_v w_u` line plus
the `v, u` from the `Cat.{v, u}` annotations earlier in the file).

To recover `catULiftFunctor`'s output `Cat.{max w v, max (w + 1) u}`,
specialize with `w_v := w` and `w_u := w + 1`.

Use `mcp__lean-lsp__lean_hover_info` on `catULiftFunctor2` to
confirm the exact universe-argument order before substituting.

- [ ] **Step 3: Replace the body**

Replace the existing `def catULiftFunctor` body (lines 3281–3297)
with:

```lean
/--
Universe-widening functor from `Cat.{v, u}` to
`Cat.{max w v, max (w+1) u}`.  At each `C`, widens `C` via
`ULift` on objects and `ULiftHom` on morphisms so that the output
universe matches `coprodCovarRepFunctor.{u, v, w}`.  Used as a
post-composition with `Cat.opFunctor` to build
`ccrNewFamilyNatTarget`.

Specialization of `catULiftFunctor2` with `w_v := w` and
`w_u := w + 1`.
-/
def catULiftFunctor :
    Cat.{v, u} ⥤ Cat.{max w v, max (w + 1) u} :=
  catULiftFunctor2.{v, u, w, w + 1}
```

If the universe-argument order in `catULiftFunctor2.{v, u, w, w+1}`
turns out to mismatch (e.g., the order is `w_v, w_u, v, u` or some
other permutation), inspect with the LSP and adjust the
specialization accordingly.

- [ ] **Step 4: Build to verify the refactor and detect any
  downstream breakage**

Run: `lake build`

Expected: success.  Two failure modes are anticipated:

1. **Universe-order mismatch**: the build fails with a universe-level
   error at the `catULiftFunctor` definition.  Fix by adjusting the
   `.{...}` arguments to match the order revealed by
   `mcp__lean-lsp__lean_hover_info`.
2. **Downstream `unfold` failure**: the proof at line 3514 (inside
   `ccrNewFamilyNat_naturality` or similar) used `unfold
   catULiftFunctor` to expose the explicit `obj`/`map` body.  After
   the refactor, that `unfold` exposes a `catULiftFunctor2`
   application instead.  Fix locally:
    - Try adding `catULiftFunctor2` to the same `unfold` block:
      `unfold ccrNewFamilyNatFunctor ccrNewFamilyNatTarget
      catULiftFunctor catULiftFunctor2`.
    - If `unfold` no longer matches the expected pattern, replace
      with `simp only [catULiftFunctor, catULiftFunctor2]`.
    - If neither works, use `mcp__lean-lsp__lean_goal` at the
      proof step to inspect the remaining goal and adjust.

- [ ] **Step 5: Run tests**

Run: `lake test`

Expected: clean (1467 jobs, exit 0).

- [ ] **Step 6: Commit**

```bash
git add GebLean/Utilities/Families.lean
git commit -m "families: refactor catULiftFunctor as specialization of catULiftFunctor2"
```

(No `Co-Authored-By` trailer.)

---

## Task 3: Empirically narrow `uliftCategory` local-instance scope

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — file-scope `attribute [local
  instance]` at line 36; possibly add per-section attribute lines
  inside the existing `section` blocks.
- [ ] **Step 1: Identify the existing sections in `PresheafPRA.lean`**

Run:

```bash
grep -n "^section\|^end \|^attribute \[local instance\]" GebLean/PresheafPRA.lean
```

Expected output indicating: line 36 file-scope attribute; sections
`PresheafPRADef` (84–145), `PresheafPRAAccessors` (149–1264),
`PresheafPRAEvalAt` (1268–1356).

- [ ] **Step 2: Remove the file-scope attribute**

Edit `GebLean/PresheafPRA.lean`, remove the line:

```lean
attribute [local instance] CategoryTheory.uliftCategory
```

(currently at line 36).

- [ ] **Step 3: Build to discover failing sections**

Run: `lake build`

Expected: build fails.  Inspect the error messages to determine
which definitions/sections fail.  Failures will likely manifest as
"failed to synthesize Category (ULift _)" or similar instance-search
errors.

Record the file:line of each failure for the next step.

- [ ] **Step 4: Reintroduce the attribute as section-local
  declarations**

For each section that contains a failing definition (likely a
subset of {pre-section block, `PresheafPRADef`,
`PresheafPRAAccessors`, `PresheafPRAEvalAt`}), add an attribute
line at the top of that section:

```lean
attribute [local instance] CategoryTheory.uliftCategory
```

For pre-section failures (definitions before line 84), add the
attribute back near line 36 BUT precede it with a comment
documenting which definition needs it (e.g., "needed for
`presheafCatFunctor`'s widening").

- [ ] **Step 5: Build to verify all sections pass**

Run: `lake build`

If any section still fails, repeat Step 4 — add another section-
local attribute.  Continue until the build is clean.

- [ ] **Step 6: Confirm narrowing actually happened**

Run:

```bash
grep -n "^attribute \[local instance\] CategoryTheory.uliftCategory" \
  GebLean/PresheafPRA.lean
```

Expected: at least one occurrence, but ideally fewer than the original
(file-scope) one.  If the attribute had to be reintroduced in every
section AND in the pre-section block, the narrowing produced no
practical reduction.  In that case, revert to the original single
file-scope attribute and abandon this task — note the result in the
commit message and in the workstream notes.

- [ ] **Step 7: Run tests**

Run: `lake test`

Expected: clean.

- [ ] **Step 8: Commit**

If narrowing succeeded:

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: narrow uliftCategory scope to sections that need it"
```

If narrowing did not produce a net reduction (every section needed
it), revert and skip the commit:

```bash
git restore GebLean/PresheafPRA.lean
```

Then record in `.session/workstreams/presheaf-pra.md` (under the
follow-up notes) that the empirical experiment confirmed the broad
scope was necessary.

(No `Co-Authored-By` trailer.)

---

## Task 4: Add `praPolyDirectionsAtSourceObj` helper

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert immediately after
  `praDirectionsAt` (which currently ends in `section
  PresheafPRAAccessors` around line 1260).
- [ ] **Step 1: Inspect the source-object structure**

Use `mcp__lean-lsp__lean_hover_info` to inspect the type of
`praPolyDirectionsSource`.  It is `Cat.of (Grothendieck
(functorFromDataContra sourceData))`, so an object is a
`Grothendieck` object — a base `((J, I), P)` paired with a fibre in
the contra-Grothendieck of `(Cat × Cat)` paired with a widened
element.

Read the relevant pieces:

- `praPolyDirectionsSource` at `PresheafPRA.lean:380–385`.
- `sourceData`, `sourceDataFib` at `PresheafPRA.lean:187–333` for
  the widening structure.
- `GrothendieckContraFunctor.mkObj` and `Grothendieck.mk` API in
  `Utilities/Grothendieck.lean` — search via `lean_local_search`.

- [ ] **Step 2: Insert the helper**

Insert after the existing `def praDirectionsAt` (around line 1260,
inside `section PresheafPRAAccessors`):

```lean
/--
Build a `praPolyDirectionsSource` object from a per-component
`(I, J, P, j, a)` triple.  Public packaging: callers can apply
`praPolyDirectionsFunctor` to this object to obtain the directions
presheaf in the natural-functor form.

The base level is the contra-Grothendieck pair
`((Cat.of Jᵒᵖ, Cat.of Iᵒᵖ), P) : (grothendieckContraFunctor
(Cat × Cat)).obj presheafPRACatBifunctorUncurriedOp`.  The fibre is
the widened element corresponding to `⟨j, a⟩ : (P ⋙
ccrNewIndexFunctor _).Elements`, lifted through `catULiftFunctor2`'s
widening to land in the source-data target Cat.
-/
def praPolyDirectionsAtSourceObj
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
    (j : Jᵒᵖ) (a : praPositions I J P j) :
    praPolyDirectionsSource.{u_I, v_I, u_J, v_J, w_I, w'} :=
  ?_
```

The `?_` is intentional — placeholder for the actual body.  Step 3
discovers the type via the LSP, Step 4 fills it.

- [ ] **Step 3: Discover the expected body via LSP**

With the `?_` in place, run `lake build` to see the unfilled-goal
error.  Expected message: "unsolved goals" with the expected type
shown.  This reveals exactly what shape the body must take.

Use `mcp__lean-lsp__lean_goal` at the `?_` position to inspect more
precisely.

- [ ] **Step 4: Fill the body**

The body builds in two layers:

1. The fibre element: `⟨j, a⟩ : (P ⋙ ccrNewIndexFunctor _).Elements`,
   widened via `(catULiftFunctor2 _).map _`-style chain (mirror the
   construction inside `sourceDataFib` at line 187).  Equivalently,
   the unwidening inverse is `praPolyDirectionsData_unwidenFiber` —
   so the widening is its inverse: a chain involving `ULift.up` /
   `ULiftHom.up`.
2. The base: build via `GrothendieckContraFunctor.mkObj` (or
   `Grothendieck.mk`) at the appropriate level, with base
   `((Cat.of Jᵒᵖ, Cat.of Iᵒᵖ), P)` and the fibre from (1).

Concretely (target shape, adjust universe annotations to match
LSP-discovered type):

```lean
def praPolyDirectionsAtSourceObj
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
    (j : Jᵒᵖ) (a : praPositions I J P j) :
    praPolyDirectionsSource.{u_I, v_I, u_J, v_J, w_I, w'} :=
  let basePair :
      (grothendieckContraFunctor
          (Cat.{v_J, u_J} × Cat.{v_I, u_I})).obj
        presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
          w_I, w'} :=
    GrothendieckContraFunctor.mkObj
      (Cat.of Jᵒᵖ, Cat.of Iᵒᵖ) P
  let fibreElem :
      (functorFromDataContra
        sourceData.{u_I, v_I, u_J, v_J, w_I, w'}).obj basePair :=
    ULiftHom.up (ULift.up ⟨j, a⟩)
  Grothendieck.mk basePair fibreElem
```

If `ULiftHom.up (ULift.up _)` doesn't typecheck because of
elaboration-order issues, pin the input type with a `show`:

```lean
show ULiftHom (ULift _) from ULiftHom.up (ULift.up ⟨j, a⟩)
```

If `GrothendieckContraFunctor.mkObj`'s expected argument shape
doesn't match the pair `(Cat.of Jᵒᵖ, Cat.of Iᵒᵖ)`, inspect the
expected type via LSP and adjust (the contra-Grothendieck mkObj API
may take base and fibre separately rather than as a pair).

- [ ] **Step 5: Build to verify**

Run: `lake build`

Expected: clean.  If a universe error appears, adjust the
universe annotations.  If a type mismatch in the fibre construction
appears, the widening chain is wrong — inspect via LSP and adjust.

- [ ] **Step 6: Run tests**

Run: `lake test`

Expected: clean.

- [ ] **Step 7: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyDirectionsAtSourceObj helper"
```

(No `Co-Authored-By` trailer.)

---

## Task 5: Add `praDirectionsAt_via_praPolyDirectionsFunctor` theorem and test

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert immediately after
  `praPolyDirectionsAtSourceObj`.
- Modify: `GebLeanTests/Utilities/PresheafPRADirNat.lean` — append a
  bridge-test section.
- [ ] **Step 1: Discover the RHS shape**

Insert a placeholder theorem in `PresheafPRA.lean`:

```lean
@[simp] theorem praDirectionsAt_via_praPolyDirectionsFunctor
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
    (j : Jᵒᵖ) (a : praPositions I J P j) :
    praDirectionsAt I J P j a = ?_ :=
  rfl
```

Run `lake build` to surface the expected RHS type via the
unsolved-`?_` error.  Use `mcp__lean-lsp__lean_goal` for a precise
view.

The expected RHS is the unwidening of
`(praPolyDirectionsFunctor.obj (praPolyDirectionsAtSourceObj
I J P j a)).fiber.unop` — but the exact unwidening chain depends
on how the widening pieces from `praDirectionsTargetFibre =
presheafCatFunctor ⋙ catULiftFunctor2 ⋙ Cat.opFunctor` collapse.

Likely shape (verify via LSP):

```lean
((praPolyDirectionsFunctor.{u_I, v_I, u_J, v_J, w_I, w'}.obj
    (praPolyDirectionsAtSourceObj I J P j a)).fiber.unop |>
  (CategoryTheory.ULiftHom.down ⋙
    CategoryTheory.ULift.downFunctor)).toFunctor.obj a  -- or similar
```

The actual shape may be cleaner — e.g., just `.fiber.unop` if the
widening machinery already collapses to `Iᵒᵖ ⥤ Type w_I` on the
nose at this composite.  Trust the LSP-revealed type.

- [ ] **Step 2: Fill the RHS and try `rfl`**

Replace the `?_` with the LSP-revealed expected RHS (preserving the
construction so it's structurally connected to
`praPolyDirectionsFunctor.obj`).  Try `rfl` as the proof.

```lean
@[simp] theorem praDirectionsAt_via_praPolyDirectionsFunctor
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
    (j : Jᵒᵖ) (a : praPositions I J P j) :
    praDirectionsAt I J P j a = <discovered-RHS> :=
  rfl
```

- [ ] **Step 3: Build to verify**

Run: `lake build`

If `rfl` succeeds: proceed to Step 5.

If `rfl` fails: try a `simp only` chain:

```lean
@[simp] theorem praDirectionsAt_via_praPolyDirectionsFunctor
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
    (j : Jᵒᵖ) (a : praPositions I J P j) :
    praDirectionsAt I J P j a = <discovered-RHS> := by
  simp only [praDirectionsAt, praPolyDirectionsFunctor,
    praPolyDirectionsAtSourceObj,
    praPolyDirectionsFunctor_fibre,
    praPolyDirectionsFunctor_base]
  rfl
```

- [ ] **Step 4: If `simp only` fails too, escalate**

If neither `rfl` nor the `simp only` chain closes the proof, do
NOT continue trying tactics indefinitely.  Report back with:

- The exact RHS shape discovered.
- The intermediate goal after the `simp only` chain.
- A judgement on whether the proof is doable at greater cost (e.g.,
  via additional bridge lemmas or `Functor.congr_hom`-style
  reasoning) or whether the proof approach is unclear.

The user has explicitly approved escalation in this case.

- [ ] **Step 5: Add the docstring**

Once the proof closes, add the docstring:

```lean
/--
Bridge: `praDirectionsAt I J P j a` agrees with the unwidened-and-
unopped fibre of `praPolyDirectionsFunctor` applied to the
corresponding source object built by
`praPolyDirectionsAtSourceObj`.  Connects the per-component accessor
to the natural-in-`(I, J, P)` functor.

Tagged `@[simp]` so callers can use `simp` to translate per-component
direction expressions into natural-functor form.
-/
```

- [ ] **Step 6: Add the test**

Append to `GebLeanTests/Utilities/PresheafPRADirNat.lean` (after the
existing sections):

```lean
/-! ## Bridge to praPolyDirectionsFunctor -/

section BridgeTest

example (I : Type 0) [Category.{0} I] (J : Type 0) [Category.{0} J]
    (P : PresheafPRACat.{0, 0, 0, 0, 0, 0} I J)
    (j : Jᵒᵖ) (a : praPositions I J P j) :
    praDirectionsAt I J P j a = <discovered-RHS-with-zero-universes> :=
  praDirectionsAt_via_praPolyDirectionsFunctor I J P j a

end BridgeTest
```

The `<discovered-RHS-with-zero-universes>` mirrors the RHS chosen
in Step 2, with all six universe arguments specialized to `0`.

- [ ] **Step 7: Build and run tests**

Run: `lake build && lake test`

Expected: clean.

- [ ] **Step 8: Commit**

```bash
git add GebLean/PresheafPRA.lean GebLeanTests/Utilities/PresheafPRADirNat.lean
git commit -m "presheaf-pra: add praDirectionsAt_via_praPolyDirectionsFunctor + test"
```

(No `Co-Authored-By` trailer.)

---

## Final Validation

After all five tasks:

- [ ] **Run full build and tests**

```bash
lake build
lake test
```

Expected: both clean.

- [ ] **Confirm commit log shape**

Run:

```bash
git log --oneline 14eda770..HEAD
```

Expected: 4–6 commits, each with `presheaf-pra:` or `families:`
prefix and a clear description.  Ordering: maxHeartbeats →
catULiftFunctor → uliftCategory → SourceObj → bridge theorem.

- [ ] **Update workstream notes**

Append a short "Follow-ups complete" entry to
`.session/workstreams/presheaf-pra.md` listing the four new
commits.  Keep entries terse — one line each.

```bash
git add .session/workstreams/presheaf-pra.md
git commit -m "session: record praDirections v2 follow-ups completion"
```

---

## Execution Handoff

Plan complete and saved to
`docs/superpowers/plans/2026-04-25-praDirections-followups.md`.

Two execution options:

1. **Subagent-Driven (recommended)** — fresh subagent per task,
   spec + code-quality review between tasks, fast iteration.
2. **Inline Execution** — execute tasks in this session using
   `superpowers:executing-plans`, batch execution with checkpoints.

The five tasks are mostly mechanical except Tasks 4 and 5, where
the implementer may need to escalate if `rfl` and `simp only` both
fail to close the bridge theorem.  Subagent-driven gives clean
escalation points after each task; inline keeps fewer round-trips
if everything works.
