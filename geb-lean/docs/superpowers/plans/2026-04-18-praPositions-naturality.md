# `(I, J)`-Naturality of `praPositionsFunctor` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Promote `praPositionsFunctor` in `GebLean/PresheafPRA.lean`
to a natural transformation between bifunctors
`Cat.{v_J, u_J}ᵒᵖ ⥤ (Cat.{v_I, u_I}ᵒᵖ ⥤ Cat.{…})`, delete the old
per-`(I, J)` definition, and migrate all 31 downstream call sites to a
temporary `praPositionsPresheaf` bridge. Leave `praDirectionsAt*` and
its surrounding `variable` declarations to a followup spec.

**Architecture:** Introduce one temporary bridge
(`praPositionsPresheaf`) with the same body as the old
`praPositionsFunctor.obj`, use it to sever the 31 downstream
references, delete the old definition, then layer the three new
artifacts (`praPositionsNatTarget`, `praPositionsNat`, the bridge
lemma) on top. Widen the nat-trans target to match
`presheafPRACatBifunctor`'s universe by composing with
`catULiftFunctor` (or a small local variant if needed).

**Tech Stack:** Lean 4, mathlib's
`CategoryTheory.Whiskering` (`Functor.whiskeringRight`,
`Functor.const`), `CategoryTheory.Category.Cat`,
`CategoryTheory.Elements`, project's existing
`presheafCatFunctor`, `presheafPRACatBifunctor`, `presheafCat`,
`coprodCovarRepFunctor`, `ccrNewIndexFunctor`, `ccrNewIndexNat`,
`typeCatLift`, `catULiftFunctor` (the last four from the CCR
utility spec).

**Reference spec:**
`docs/superpowers/specs/2026-04-18-praPositions-naturality-design.md`.

**Project policy reminders:**

- No `sorry`, `admit`, `axiom`, `noncomputable`, `Classical.choice`,
  or `Quot.out`/`Quotient.out`.
- 80-character line limit.
- Build with `lake build`; test with `lake test`. Never `lake clean`
  or `lake env lean`.
- After each definition or edit, re-run `lake build` and `lake test`
  and fix problems before moving on.
- When a proof doesn't close, use `_` to see the goal; never `sorry`.
- No unused `universe` or `variable` declarations.
- If stuck on a proof, try `lean4:sorry-filler-deep` or
  `superpowers:brainstorming`; never commit code that builds with
  warnings.

---

## File Structure

Four files modified plus one created:

**Modified:** `GebLean/PresheafPRA.lean`

- Task 1 inserts `praPositionsPresheaf` just above the existing
  `praPositionsFunctor` in `section PresheafPRAAccessors`.
- Task 2 rewrites three call sites in the same section.
- Task 4 deletes the `praPositionsFunctor` block.
- Tasks 5–7 insert `praPositionsNatTarget`, `praPositionsNat`, and
  the bridge lemma at the top of `section PresheafPRAAccessors`
  (where `praPositionsFunctor` used to be).

**Modified:** `GebLean/PresheafPRAUMorph.lean`

- Task 3 substitutes ~28 instances of
  `(praPositionsFunctor I J).obj P` → `praPositionsPresheaf I J P`
  (and the corresponding patterns with other variables in place of
  `P`). No signatures change.

**Modified:** `GebLeanTests.lean`

- Task 9 adds `import GebLeanTests.Utilities.PresheafPRANat`.

**Modified:** `.session/workstreams/presheaf-pra.md` and
`.session/workstreams/pra-universal-morphisms.md`

- Task 13 updates the name in passing (these are session notes, not
  released content — minimal touch).

**Created:** `GebLeanTests/Utilities/PresheafPRANat.lean`

- Task 8 creates the test file with type-sanity tests; Tasks 10–12
  append further tests.

---

## Task 1: Add `praPositionsPresheaf` temporary bridge

**Files:**
- Modify: `GebLean/PresheafPRA.lean` (insert after line 148,
  i.e. immediately after `section PresheafPRAAccessors` opens and
  just before the existing `praPositionsFunctor`)

- [ ] **Step 1: Locate the insertion point**

Run:
```bash
grep -n "section PresheafPRAAccessors\|def praPositionsFunctor" GebLean/PresheafPRA.lean
```

Expected: `section PresheafPRAAccessors` at line ≈ 147, `def
praPositionsFunctor` at line ≈ 153.

- [ ] **Step 2: Insert `praPositionsPresheaf` immediately after the
      section opens, before `praPositionsFunctor`**

Use the Edit tool. Insert the following block after the
`section PresheafPRAAccessors` line (line ≈ 147), before the
`/--` that starts the `praPositionsFunctor` docstring:

```lean
/--
Temporary bridge to the non-widened form of the positions presheaf.
Consumed by `praPositions` / `praDirectionsAtFunctor*` until the
directions section is promoted; will be removed at that time.
-/
def praPositionsPresheaf
    (I : Type u_I) [Category.{v_I} I]
    (J : Type u_J) [Category.{v_J} J]
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J) :
    Jᵒᵖ ⥤ Type w' :=
  ((Functor.whiskeringRight Jᵒᵖ _ _).obj
    (ccrNewIndexFunctor.{max v_I u_I (w_I + 1),
      max u_I w_I, w'}
      (↑(presheafCat.{u_I, v_I, w_I} I)))).obj P
```

The body is literally the inlined form of
`(praPositionsFunctor I J).obj P`, so at this stage the build sees
two ways to compute the same thing.

- [ ] **Step 3: Build**

Run: `lake build GebLean.PresheafPRA`
Expected: success. No warnings. No `sorry`.

- [ ] **Step 4: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "$(cat <<'EOF'
Add praPositionsPresheaf temporary bridge

Dependent function returning the non-widened positions presheaf.
Temporary accommodation so the directions section can stay in its
current form while praPositionsFunctor is replaced by a natural
transformation; will be removed when directions is promoted.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 2: Migrate three call sites in `PresheafPRA.lean`

**Files:**
- Modify: `GebLean/PresheafPRA.lean` (three occurrences of
  `(praPositionsFunctor I J).obj P` in the same accessor section)

- [ ] **Step 1: Locate the three call sites**

Run:
```bash
grep -n "praPositionsFunctor I J" GebLean/PresheafPRA.lean
```

Expected: three matches, in the bodies of `praPositions` (line
≈ 167), `praDirectionsAtFunctorOp` (line ≈ 175), and
`praDirectionsAtFunctor` (line ≈ 189). Verify each match uses the
pattern `(praPositionsFunctor I J).obj P` followed by `.obj j`,
`.Elements`, or `.ElementsPre` respectively.

- [ ] **Step 2: Replace the first call site — `praPositions`**

Find:

```lean
def praPositions (j : Jᵒᵖ) : Type w' :=
  (praPositionsFunctor I J).obj P |>.obj j
```

Replace with:

```lean
def praPositions (j : Jᵒᵖ) : Type w' :=
  (praPositionsPresheaf I J P).obj j
```

- [ ] **Step 3: Replace the second call site —
      `praDirectionsAtFunctorOp`**

Find:

```lean
def praDirectionsAtFunctorOp :
    ((praPositionsFunctor I J).obj P).Elements ⥤
      (Iᵒᵖ ⥤ Type w_I)ᵒᵖ :=
```

Replace with:

```lean
def praDirectionsAtFunctorOp :
    (praPositionsPresheaf I J P).Elements ⥤
      (Iᵒᵖ ⥤ Type w_I)ᵒᵖ :=
```

- [ ] **Step 4: Replace the third call site — `praDirectionsAtFunctor`**

Find:

```lean
def praDirectionsAtFunctor :
    ((praPositionsFunctor I J).obj P).ElementsPre ⥤
      (Iᵒᵖ ⥤ Type w_I) :=
```

Replace with:

```lean
def praDirectionsAtFunctor :
    (praPositionsPresheaf I J P).ElementsPre ⥤
      (Iᵒᵖ ⥤ Type w_I) :=
```

- [ ] **Step 5: Verify no further occurrences of
      `praPositionsFunctor` exist in bodies (aside from the
      still-present definition)**

Run:
```bash
grep -n "praPositionsFunctor" GebLean/PresheafPRA.lean
```

Expected: one match — the `def praPositionsFunctor` line itself
(which Task 4 will delete). Its docstring and body still exist; no
other bodies reference it.

- [ ] **Step 6: Build**

Run: `lake build GebLean.PresheafPRA`
Expected: success. The body of `praPositionsPresheaf` is
definitionally equal to `(praPositionsFunctor I J).obj P`, so the
downstream `.Elements` / `.ElementsPre` / `.obj j` uses continue to
type-check.

- [ ] **Step 7: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 8: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "$(cat <<'EOF'
Migrate praPositions/praDirectionsAt* to praPositionsPresheaf

Three call sites in the accessor section switch from
(praPositionsFunctor I J).obj P to praPositionsPresheaf I J P.
Same result type in each case; .Elements, .ElementsPre, and .obj j
are unaffected.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 3: Migrate call sites in `PresheafPRAUMorph.lean`

**Files:**
- Modify: `GebLean/PresheafPRAUMorph.lean` (~28 occurrences)

- [ ] **Step 1: Enumerate the occurrences**

Run:
```bash
grep -n "praPositionsFunctor I J" GebLean/PresheafPRAUMorph.lean
```

Expected: around 28 matches. All use the pattern
`(praPositionsFunctor I J).obj <expr>` followed by `.obj j`,
`.Elements`, `.ElementsPre`, or similar.

- [ ] **Step 2: Substitute all occurrences**

For each match, replace the pattern
`(praPositionsFunctor I J).obj <expr>` with
`praPositionsPresheaf I J <expr>`.

Use a single sed-style pass. Example using the Edit tool with
`replace_all: true` per distinct match, or using
`sed -i 's/(praPositionsFunctor I J)\.obj /praPositionsPresheaf I J /g' GebLean/PresheafPRAUMorph.lean` (verify afterwards that no intended
form was missed).

The result should have:
- No remaining `praPositionsFunctor` occurrences in
  `PresheafPRAUMorph.lean`.
- Every former call returning `Jᵒᵖ ⥤ Type w'` now reads
  `praPositionsPresheaf I J <expr>`, yielding the same type.

- [ ] **Step 3: Verify no residual `praPositionsFunctor`**

Run:
```bash
grep -n "praPositionsFunctor" GebLean/PresheafPRAUMorph.lean
```

Expected: no matches.

- [ ] **Step 4: Build**

Run: `lake build GebLean.PresheafPRAUMorph`
Expected: success.

If the substitution missed an occurrence, the build will fail with
"unknown identifier `praPositionsFunctor`" at the exact line. Fix
each by hand by applying the same `→ praPositionsPresheaf I J`
pattern.

- [ ] **Step 5: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 6: Commit**

```bash
git add GebLean/PresheafPRAUMorph.lean
git commit -m "$(cat <<'EOF'
Migrate PresheafPRAUMorph.lean to praPositionsPresheaf

Mechanical substitution: (praPositionsFunctor I J).obj <expr>
becomes praPositionsPresheaf I J <expr> throughout the file.
Same result type in every case.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 4: Delete the old `praPositionsFunctor`

**Files:**
- Modify: `GebLean/PresheafPRA.lean` (remove lines 149–159)

- [ ] **Step 1: Confirm no remaining consumers**

Run:
```bash
grep -rn "praPositionsFunctor" GebLean/
```

Expected: one match — the `def praPositionsFunctor` line and its
body/docstring in `GebLean/PresheafPRA.lean`. No other file
references it.

- [ ] **Step 2: Delete the docstring and definition**

Find the block:

```lean
/--
The positions functor: sends a PRA `P` to the presheaf
on `J` of position types.
-/
def praPositionsFunctor :
    PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'}
      I J ⥤ (Jᵒᵖ ⥤ Type w') :=
  (Functor.whiskeringRight Jᵒᵖ _ _).obj
    (ccrNewIndexFunctor.{max v_I u_I (w_I + 1),
      max u_I w_I, w'}
      (↑(presheafCat.{u_I, v_I, w_I} I)))
```

Delete it entirely (including the preceding blank line if any).

- [ ] **Step 3: Verify the file has no `praPositionsFunctor`**

Run:
```bash
grep -n "praPositionsFunctor" GebLean/PresheafPRA.lean
```

Expected: no matches.

- [ ] **Step 4: Build**

Run: `lake build GebLean.PresheafPRA`
Expected: success.

- [ ] **Step 5: Full build and test**

Run: `lake build && lake test`
Expected: both succeed. The entire project compiles with
`praPositionsFunctor` gone.

- [ ] **Step 6: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "$(cat <<'EOF'
Delete praPositionsFunctor

The per-(I, J) form is replaced by praPositionsPresheaf I J P for
the three call sites that needed a presheaf-valued accessor.  The
natural-transformation form praPositionsNat follows in subsequent
tasks.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 5: Add `praPositionsNatTarget`

**Files:**
- Modify: `GebLean/PresheafPRA.lean` (insert at the top of
  `section PresheafPRAAccessors`, above `praPositionsPresheaf`)

- [ ] **Step 1: Add the bifunctor**

Insert near the top of `section PresheafPRAAccessors`, before
`praPositionsPresheaf`:

```lean
/--
Target bifunctor of `praPositionsNat`.  Sends each
`(J, I) : Cat.{v_J, u_J}ᵒᵖ × Cat.{v_I, u_I}ᵒᵖ` to the
universe-widened form of `Jᵒᵖ ⥤ Type w'`, constant in `I`.

Constant in `I` because the action of `presheafPRACatBifunctor.map`
on `I`-morphisms preserves the index (positions) types on the nose
— the same property of `coprodCovarRepFunctor.map` established in
Task 3 of the CCR utility spec.
-/
def praPositionsNatTarget :
    Cat.{v_J, u_J}ᵒᵖ ⥤
      (Cat.{v_I, u_I}ᵒᵖ ⥤
        Cat.{max u_I u_J w_I w',
          max u_I u_J v_I v_J (w_I + 1) (w' + 1)}) :=
  presheafCatFunctor.{u_J, v_J, w'} ⋙
    catULiftFunctor.{…, …, …} ⋙
    Functor.const Cat.{v_I, u_I}ᵒᵖ
```

Notes for the implementer:

- The universe annotations on `catULiftFunctor` need to be
  instantiated so that the output matches
  `Cat.{max u_I u_J w_I w', max u_I u_J v_I v_J (w_I + 1) (w' + 1)}`.
- `catULiftFunctor.{v, u, w} : Cat.{v, u} ⥤ Cat.{max w v, max (w+1) u}`.
- Applied to `presheafCatFunctor.{u_J, v_J, w'}`'s output
  `Cat.{max u_J w', max v_J (w'+1) u_J}`, the composite lands in
  `Cat.{max w (max u_J w'), max (w+1) (max v_J (w'+1) u_J)}`.
- Choosing `w := max u_I v_I (w_I + 1)` makes the hom-side equal
  `max u_I u_J v_I v_J (w_I+1) (w'+1)` (note: `w_I+1` supplies the
  needed `w_I+1` term). However, `(w+1)` on the obj-side expands to
  `max (u_I+1) (v_I+1) (w_I+2)`, which is strictly larger than the
  needed `max u_I u_J w_I w'` on the obj side.
- This universe mismatch means `catULiftFunctor` alone does not fit.
  Two remediation options, pick whichever elaborates:
  1. **Local variant:** In `GebLean/Utilities/Families.lean`, add a
     sibling to `catULiftFunctor` that takes two widening parameters
     `w_hom` and `w_obj` independently (a 2-level version). Then use
     `catULiftFunctor2.{w_hom := max u_I v_I (w_I + 1),
     w_obj := max u_I w_I}` or similar.
  2. **Inline the widening:** Write the target definition directly
     using `Cat.of (ULiftHom.{…} (ULift.{…, …} (_ : Type w')))`,
     bypassing the named widening functor.

Use `_` in any universe slot where you need to see Lean's expected
level; elaborator errors will print the precise mismatch.

- [ ] **Step 2: Build**

Run: `lake build GebLean.PresheafPRA`
Expected: success. If the universe annotations don't align, iterate
using `_` until they do, or switch to remediation option 2.

If you choose remediation option 1 and add a helper to
`Utilities/Families.lean`, that counts as a scope enlargement
touching the utility spec's file. Note the helper in the commit
message. Do not modify the CCR utility section; the helper should be
a fresh sibling `catULiftFunctor2` (or a similar name) in a new or
existing section of its own.

- [ ] **Step 3: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 4: Commit**

```bash
git add GebLean/PresheafPRA.lean GebLean/Utilities/Families.lean
git commit -m "$(cat <<'EOF'
Add praPositionsNatTarget: widened positions-presheaf bifunctor

Composes presheafCatFunctor with universe-widening and
Functor.const to produce the bifunctor that is constant in the
I-direction and returns the widened Jᵒᵖ ⥤ Type w' at each J.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

(Adjust `git add` to include `Utilities/Families.lean` only if a
helper was added there.)

---

## Task 6: Add `praPositionsNat`

**Files:**
- Modify: `GebLean/PresheafPRA.lean` (insert after
  `praPositionsNatTarget`, still before `praPositionsPresheaf`)

- [ ] **Step 1: Add the natural transformation**

Insert after `praPositionsNatTarget`:

```lean
/--
The natural transformation packaging the positions functors of all
presheaf PRAs, natural in both `I` and `J`.  Source:
`presheafPRACatBifunctor`.  Target: `praPositionsNatTarget`.

Each `(praPositionsNat.app J).app I` is the underlying functor
`PresheafPRACat I J ⥤ (widened Jᵒᵖ ⥤ Type w')` obtained by
whiskering `ccrNewIndexFunctor (presheafCat I)` with `Jᵒᵖ` and
post-composing with the universe-widening lifts used by
`praPositionsNatTarget`.

Naturality in `I` reduces (via `ccrNewIndexNat`) to the
index-preservation property of `coprodCovarRepFunctor.map`.
Naturality in `J` follows from `Functor.whiskeringRight`'s
functoriality; `ccrNewIndexNat` has no `J`-dependence.
-/
def praPositionsNat :
    presheafPRACatBifunctor.{u_I, v_I, u_J, v_J, w_I, w'} ⟶
      praPositionsNatTarget.{u_I, v_I, u_J, v_J, w_I, w'} where
  app J :=
    { app := fun I =>
        /- per-(J, I) component: the whiskered ccrNewIndexFunctor
           composed with the widening lifts, wrapped as .toCatHom -/
        _
      naturality := fun I₁ I₂ F => by
        /- naturality in I; expected to close via ccrNewIndexNat
           naturality + whiskering-right composition -/
        _ }
  naturality J₁ J₂ G := by
    /- naturality in J; expected to close via whiskeringRight
       functoriality on Jᵒᵖ morphisms -/
    _
```

Notes for the implementer:

- The three `_` holes must be filled in with real tactics. Per
  CLAUDE.md, `_` (underscore) is the canonical hole marker for
  in-progress proofs/definitions; `sorry` is forbidden. Replace each
  `_` with the correct body after inspecting the unsolved-goals
  error.
- For the inner `app` field: the per-(J, I) component is the
  composite
  `(Functor.whiskeringRight Jᵒᵖ _ _).obj
  (ccrNewIndexFunctor (presheafCat I))` post-composed with the
  widening lifts, wrapped as `.toCatHom`. Factor into a helper
  `private def praPositionsNatApp (J : Cat.{v_J, u_J}ᵒᵖ)
  (I : Cat.{v_I, u_I}ᵒᵖ) : …` if the inline form is unwieldy.
- For the inner `naturality` in I: the underlying functor equation
  is the whiskered form of
  `ccrNewIndexNat.naturality (F.unop.op.toFunctor)` (or similar —
  the exact form depends on how the widening composes). Expect `rfl`
  to work after `apply Cat.Hom.ext; apply NatTrans.ext`. If not,
  factor out a helper lemma.
- For the outer `naturality` in J: similar — `Functor.whiskeringRight`
  is covariant in its first argument, so naturality in J should be
  close to `rfl` after the widening layers peel off with
  `dsimp only [praPositionsNatTarget]` or similar.
- If a proof doesn't close after 30 minutes of work, factor it out
  into a named helper lemma (following the CLAUDE.md
  factoring-out-lemmas technique).

- [ ] **Step 2: Inspect the three `_` goals**

Run: `lake build GebLean.PresheafPRA`
Expected: "unsolved goals" errors at each `_` site. Read the goals.

- [ ] **Step 3: Fill in the three holes**

Replace each `_` with a proof / definition. Repeat the build until
all holes close cleanly.

- [ ] **Step 4: Verify no `sorry` / `admit` / `_` in the committed
      region**

Run:
```bash
grep -n "sorry\|admit" GebLean/PresheafPRA.lean
```

Expected: no matches.

Run:
```bash
grep -n "^[[:space:]]*_$\|:= _\|by _" GebLean/PresheafPRA.lean
```

Expected: no matches in the `praPositionsNat` block. (The
`ccrNewIndexFunctor … _ _` construction that already exists
elsewhere in the file uses `_` for implicit arguments, which is
fine; we're only concerned with proof-position `_`.)

- [ ] **Step 5: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 6: Axiom check**

Temporarily add `#print axioms praPositionsNat` to the end of
`GebLean/PresheafPRA.lean` and run
`lake build GebLean.PresheafPRA`. Verify the output lists only
`propext`, `Classical.choice`, `Quot.sound`. Remove the temporary
line and rebuild.

- [ ] **Step 7: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "$(cat <<'EOF'
Add praPositionsNat: (I, J)-natural form of the positions functor

Two-level natural transformation assembling the per-(I, J)
positions functors into a nat-trans between bifunctors
Catᵒᵖ ⥤ (Catᵒᵖ ⥤ Cat).  Naturality in I follows from
ccrNewIndexNat; naturality in J follows from whiskeringRight's
functoriality.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 7: Add the bridge lemma

**Files:**
- Modify: `GebLean/PresheafPRA.lean` (insert after `praPositionsNat`,
  still before `praPositionsPresheaf`)

- [ ] **Step 1: Add the bridge lemma**

Insert after `praPositionsNat`:

```lean
/--
Bridge lemma: each `(praPositionsNat.app J).app I`, viewed as an
underlying functor, equals the whiskered `ccrNewIndexFunctor` form
post-composed with the universe-widening lifts used by
`praPositionsNatTarget`.

Not marked `@[simp]` to avoid unfolding cycles.  Intended for
downstream users who want to reach through the widening to the
underlying non-widened form.
-/
theorem praPositionsNat_app_eq_presheafCatFunctor
    (I : Type u_I) [Category.{v_I} I]
    (J : Type u_J) [Category.{v_J} J] :
    ((praPositionsNat.{u_I, v_I, u_J, v_J, w_I, w'}.app
        (Cat.of Jᵒᵖ).op).app
      (Cat.of Iᵒᵖ).op).toFunctor =
      /- RHS: the whiskered ccrNewIndexFunctor composite followed
         by the widening lifts.  Exact form depends on Task 5's
         choice of widening; copy from praPositionsNatTarget's
         unfolding or from praPositionsNat's inner app body. -/
      _ := by
  rfl
```

Notes for the implementer:

- Replace the `_` on the RHS with the concrete expression used in
  `praPositionsNat`'s inner `app` field. Use `#check` or
  `#reduce` (sparingly) to inspect the expression shape.
- If `rfl` does not close the goal, the typical cause is that the
  RHS doesn't match the LHS's normal form exactly. Try `apply
  Cat.Hom.ext; rfl`, or unfold `praPositionsNat` and
  `praPositionsNatTarget` with `unfold`, or massage the RHS to
  match.
- If the bridge doesn't hold definitionally (unlikely, since
  `praPositionsNat.app` is defined directly as that composite), it
  means something upstream has been defined via a non-defeq
  combinator; in that case, write a short `by rfl` substitute, such
  as `by apply Cat.Hom.ext; rfl`.

- [ ] **Step 2: Verify no `_` or `sorry` remains**

Run:
```bash
grep -n "sorry\|admit" GebLean/PresheafPRA.lean
```

Expected: no matches.

- [ ] **Step 3: Build**

Run: `lake build GebLean.PresheafPRA`
Expected: success.

- [ ] **Step 4: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "$(cat <<'EOF'
Add bridge lemma praPositionsNat_app_eq_presheafCatFunctor

Documents that each per-(J, I) component of praPositionsNat unfolds
to the whiskered ccrNewIndexFunctor composite with the widening
lifts.  Not marked @[simp] to avoid unfolding cycles.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 8: Create test file with type-sanity tests

**Files:**
- Create: `GebLeanTests/Utilities/PresheafPRANat.lean`

- [ ] **Step 1: Confirm the test directory exists**

Run:
```bash
ls GebLeanTests/Utilities/
```

Expected: `Tower.lean`, `Families.lean` present.

- [ ] **Step 2: Create the test file**

Create `GebLeanTests/Utilities/PresheafPRANat.lean` with:

```lean
import GebLean.PresheafPRA

/-!
# Tests for (I, J)-Naturality of praPositionsFunctor

Type-signature sanity checks and small-example tests for
`praPositionsNat` and friends in `GebLean.PresheafPRA`.
-/

open GebLean CategoryTheory

/-! ## Type-signature sanity -/

-- praPositionsNat has the expected shape.
example :
    presheafPRACatBifunctor.{0, 0, 0, 0, 0, 0} ⟶
      praPositionsNatTarget.{0, 0, 0, 0, 0, 0} :=
  praPositionsNat.{0, 0, 0, 0, 0, 0}

-- praPositionsNatTarget has the expected shape.
example :
    Cat.{0, 0}ᵒᵖ ⥤
      (Cat.{0, 0}ᵒᵖ ⥤ Cat.{0, 1}) :=
  praPositionsNatTarget.{0, 0, 0, 0, 0, 0}
```

Notes for the implementer:

- The explicit universe annotations `.{0, 0, 0, 0, 0, 0}` are the
  six universe parameters `u_I v_I u_J v_J w_I w'`. The binder order
  is established by the file's top-level `universe` declaration
  (line ≈ 34: `universe u_I v_I u_J v_J w_I w'`).
- The output `Cat.{0, 0}ᵒᵖ ⥤ (Cat.{0, 0}ᵒᵖ ⥤ Cat.{0, 1})` for
  `praPositionsNatTarget` at all-zero universes arises from
  `Cat.{max 0 0 0 0, max 0 0 0 0 1 1} = Cat.{0, 1}` (at
  `w_I = 0, w' = 0`).
- If any of the universe annotations fail to elaborate, adjust —
  the universe-polymorphism test in Task 12 will exercise a
  different instantiation for comparison.

- [ ] **Step 3: Build the new file standalone**

Run: `lake build GebLeanTests.Utilities.PresheafPRANat`
Expected: success.

- [ ] **Step 4: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRANat.lean
git commit -m "$(cat <<'EOF'
Add type-signature sanity tests for praPositionsNat

New test file exercises the type signatures of praPositionsNat and
praPositionsNatTarget at universe level 0.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 9: Register the test file in `GebLeanTests.lean`

**Files:**
- Modify: `GebLeanTests.lean`

- [ ] **Step 1: Add the import line**

Edit `GebLeanTests.lean` and add
`import GebLeanTests.Utilities.PresheafPRANat` after the existing
`import GebLeanTests.Utilities.Families` line.

- [ ] **Step 2: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests.lean
git commit -m "$(cat <<'EOF'
Register GebLeanTests.Utilities.PresheafPRANat test file

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 10: Add the definitional-collapse test

**Files:**
- Modify: `GebLeanTests/Utilities/PresheafPRANat.lean` (append)

- [ ] **Step 1: Add the collapse test**

Append to `GebLeanTests/Utilities/PresheafPRANat.lean`:

```lean
/-! ## Definitional collapse via the bridge lemma -/

section CollapseTest

-- Bridge lemma applies at a concrete small base-pair.
example :
    ((praPositionsNat.{0, 0, 0, 0, 0, 0}.app
        (Cat.of (PUnitᵒᵖ : Type 0)).op).app
      (Cat.of (PUnitᵒᵖ : Type 0)).op).toFunctor =
      /- RHS: the whiskered ccrNewIndexFunctor composite followed
         by the widening lifts, specialized to I = J = PUnit.
         Copy from the bridge lemma in GebLean/PresheafPRA.lean. -/
      _ :=
  praPositionsNat_app_eq_presheafCatFunctor.{0, 0, 0, 0, 0, 0}
    PUnit PUnit

end CollapseTest
```

Notes:

- Fill in the `_` RHS by copying the exact expression from the
  bridge lemma's statement. The bridge lemma is stated for
  arbitrary `I` and `J`; here we instantiate with `PUnit`.
- If the bridge lemma's RHS shape doesn't directly elaborate at
  `PUnit`, use
  `by exact praPositionsNat_app_eq_presheafCatFunctor PUnit PUnit`
  instead of `:=`, and let Lean fill in the RHS via `rfl`.

- [ ] **Step 2: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRANat.lean
git commit -m "$(cat <<'EOF'
Add definitional-collapse test for praPositionsNat

Verifies that the bridge lemma applies at I = J = PUnit, checking
that praPositionsNat's per-(J, I) component unfolds to the
whiskered ccrNewIndexFunctor composite with the widening.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 11: Add naturality tests

**Files:**
- Modify: `GebLeanTests/Utilities/PresheafPRANat.lean` (append)

- [ ] **Step 1: Add the naturality tests**

Append to `GebLeanTests/Utilities/PresheafPRANat.lean`:

```lean
/-! ## Naturality in I and J, small examples -/

section NaturalityTests

-- The identity functor PUnit ⥤ PUnit, packaged as a Cat morphism.
private def baseIdFunctor :
    Cat.of (PUnit : Type 0) ⟶ Cat.of (PUnit : Type 0) :=
  (CategoryTheory.Functor.id _).toCatHom

-- Naturality of praPositionsNat in I at the identity functor.
example :
    (presheafPRACatBifunctor.{0, 0, 0, 0, 0, 0}.obj
      (Cat.of (PUnitᵒᵖ : Type 0)).op).map baseIdFunctor.op ≫
        (praPositionsNat.{0, 0, 0, 0, 0, 0}.app
          (Cat.of (PUnitᵒᵖ : Type 0)).op).app
          (Cat.of (PUnitᵒᵖ : Type 0)).op =
      (praPositionsNat.{0, 0, 0, 0, 0, 0}.app
        (Cat.of (PUnitᵒᵖ : Type 0)).op).app
        (Cat.of (PUnitᵒᵖ : Type 0)).op ≫
        (praPositionsNatTarget.{0, 0, 0, 0, 0, 0}.obj
          (Cat.of (PUnitᵒᵖ : Type 0)).op).map baseIdFunctor.op :=
  (praPositionsNat.{0, 0, 0, 0, 0, 0}.app
    (Cat.of (PUnitᵒᵖ : Type 0)).op).naturality baseIdFunctor.op

-- Naturality of praPositionsNat in J at the identity functor.
example :
    presheafPRACatBifunctor.{0, 0, 0, 0, 0, 0}.map baseIdFunctor.op ≫
      praPositionsNat.{0, 0, 0, 0, 0, 0}.app
        (Cat.of (PUnitᵒᵖ : Type 0)).op =
      praPositionsNat.{0, 0, 0, 0, 0, 0}.app
        (Cat.of (PUnitᵒᵖ : Type 0)).op ≫
        praPositionsNatTarget.{0, 0, 0, 0, 0, 0}.map
          baseIdFunctor.op :=
  praPositionsNat.{0, 0, 0, 0, 0, 0}.naturality baseIdFunctor.op

end NaturalityTests
```

Notes:

- These tests appeal directly to the `naturality` field of
  `praPositionsNat` (outer) and
  `praPositionsNat.app J` (inner), which is just restating what
  Task 6 proved. They serve as `#check`-level smoke tests that the
  naturality square is type-correct.
- If the concrete types don't elaborate exactly as written (e.g.,
  because `.app` takes an `Opposite`-wrapped arg that doesn't match
  `(Cat.of (PUnitᵒᵖ : Type 0)).op` literally), adjust the
  opposite-wrapping. Use `#check` to inspect expected argument
  shapes.

- [ ] **Step 2: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRANat.lean
git commit -m "$(cat <<'EOF'
Add naturality tests for praPositionsNat

Exercises naturality of praPositionsNat in both I and J at the
identity functor on PUnit.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 12: Add a universe-polymorphism test

**Files:**
- Modify: `GebLeanTests/Utilities/PresheafPRANat.lean` (append)

- [ ] **Step 1: Add the test**

Append:

```lean
/-! ## Universe polymorphism -/

section UniversePoly

-- Exercise praPositionsNat at mixed universes
-- (u_I := 1, v_I := 0, u_J := 0, v_J := 0, w_I := 0, w' := 0).
example :
    presheafPRACatBifunctor.{1, 0, 0, 0, 0, 0} ⟶
      praPositionsNatTarget.{1, 0, 0, 0, 0, 0} :=
  praPositionsNat.{1, 0, 0, 0, 0, 0}

end UniversePoly
```

Notes:

- The test instantiates the six universe parameters at
  `{u_I := 1, v_I := 0, u_J := 0, v_J := 0, w_I := 0, w' := 0}`.
  If Lean's universe elaborator reports that a different target
  shape is produced at these levels, adjust the explicit
  `Cat.{?, ?}` annotations in the RHS of the `⟶` to match.

- [ ] **Step 2: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRANat.lean
git commit -m "$(cat <<'EOF'
Add universe-polymorphism test for praPositionsNat

Exercises the definitions at mixed universes to catch accidental
universe specialization across the six parameters.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 13: Update `.session/` notes

**Files:**
- Modify: `.session/workstreams/presheaf-pra.md`
- Modify: `.session/workstreams/pra-universal-morphisms.md`

These are session workstream notes, not released content. Per
CLAUDE.md, `.session/` is transient, so the goal is minimal-touch
correctness: replace the stale `praPositionsFunctor` name with
`praPositionsPresheaf` (or `praPositionsNat` where the reference is
to the naturality rather than the presheaf accessor), without
rewriting or reorganizing the notes.

- [ ] **Step 1: Survey each file**

Run:
```bash
grep -n "praPositionsFunctor" .session/workstreams/presheaf-pra.md \
  .session/workstreams/pra-universal-morphisms.md
```

- [ ] **Step 2: Replace names**

For each match, substitute the name:
- If the reference is to `praPositionsFunctor I J .obj P` or
  similar (the presheaf extraction form), replace with
  `praPositionsPresheaf I J P`.
- If the reference is conceptually to "the positions functor" as a
  whole, replace with `praPositionsNat` (and optionally add a
  parenthetical "via `praPositionsPresheaf` for per-`P` extraction").

Use the Edit tool with `replace_all: true` on each file for the
mechanical `praPositionsFunctor` → `praPositionsPresheaf`
substitution first, then do manual case-by-case rewording only if
an instance is conceptually referring to the functor-valued form
rather than the presheaf-extraction form.

- [ ] **Step 3: Verify**

Run:
```bash
grep -n "praPositionsFunctor" .session/workstreams/presheaf-pra.md \
  .session/workstreams/pra-universal-morphisms.md
```

Expected: no matches (or only matches that are acceptable in
context — e.g., a historical reference explicitly quoting the old
name).

- [ ] **Step 4: Commit**

```bash
git add .session/workstreams/
git commit -m "$(cat <<'EOF'
Update session notes: praPositionsFunctor references

Replace stale praPositionsFunctor references with
praPositionsPresheaf (for per-P accessors) or praPositionsNat
(for the natural-transformation form).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Final Verification

- [ ] **Step 1: Full clean build and test**

Run:
```bash
lake build && lake test
```

Expected: both succeed with no warnings.

- [ ] **Step 2: Placeholder scan**

Run:
```bash
grep -rn "sorry\|admit\|TODO\|TBD" GebLean/PresheafPRA.lean \
  GebLean/PresheafPRAUMorph.lean \
  GebLeanTests/Utilities/PresheafPRANat.lean \
  GebLeanTests.lean
```

Expected: no matches.

- [ ] **Step 3: Confirm the old functor is fully gone**

Run:
```bash
grep -rn "praPositionsFunctor" GebLean/ GebLeanTests/
```

Expected: no matches. (The `.session/` directory may still have
residue; if Task 13 was thorough it will also show no matches
there, but the `.session/` residue is not build-blocking.)

- [ ] **Step 4: Axiom check**

Temporarily append to `GebLean/PresheafPRA.lean`:
```lean
#print axioms GebLean.praPositionsNat
```

Run `lake build GebLean.PresheafPRA`. Verify only `propext`,
`Classical.choice`, `Quot.sound` are reported. Remove the temporary
line.

- [ ] **Step 5: Confirm no unused `variable` declarations**

Run `lake build` and check for "unused variable" or "unused
universe" warnings. None expected. (The top-level `variable (I …)`
and `variable (J …)` remain in use by the directions section, so
they stay.)

---

## Notes for the Executor

- **Universe handling in Task 5** is the main uncertainty in this
  plan. The recommended approach is to try `catULiftFunctor` first
  (matching the CCR utility spec style); if it doesn't fit, add a
  two-parameter sibling in `Utilities/Families.lean`. Either
  resolution is acceptable.
- **If `rfl` fails in the bridge lemma (Task 7)** or in `naturality`
  (Task 6), use the CLAUDE.md factoring-out-lemmas technique:
  factor into a helper lemma, inspect the subgoals with `_`, write
  each sub-proof small enough that tactics can close it.
- **The ~28 substitutions in Task 3** are mechanical — use
  `sed -i`, a single `Edit` with `replace_all`, or a similar bulk
  operation. Verify with a `grep` afterwards.
- **`.session/` edits (Task 13) are best-effort.** If a reference
  is ambiguous and requires non-trivial reword, it is acceptable
  to leave a brief "needs review" comment or simply rename
  mechanically; perfection is not required for transient notes.
- **No mid-task commits.** Each task produces a buildable commit.
  If a task cannot be completed cleanly, do not commit — pause and
  ask for guidance.
