# `(I, J, P)`-Naturality of `praDirectionsAtFunctor*` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Promote `praDirectionsAtFunctorOp` and `praDirectionsAtFunctor`
in `GebLean/PresheafPRA.lean` to natural transformations between
functors out of `Grothendieck(presheafPRACatBifunctorUncurried)`
using `FunctorFromData` / `NatTransFromData`.  Rewrite pointwise
accessors `praPositions` and `praDirectionsAt` to route through the
natural forms.  Delete the old per-`(I, J, P)` forms plus the
transitional `praPositionsPresheaf`.  Remove `variable` declarations
that become unused as a validation step.

**Architecture:** Uncurry `presheafPRACatBifunctor` via
`Functor.uncurry`.  Build `sourceData` / `targetData` /
`natData : NatTransFromData …` for the Op side, extract
`praDirectionsNatOp`.  Build the parallel `…Pre` bundles for the
non-Op side, extract `praDirectionsNat`.  Add bridge lemmas relating
each nat-trans's per-`(J, I, P)` component to the existing
composite.  Rewrite pointwise accessors via a `private
praPositionsUnwidened` helper.  Delete old per-`(I, J, P)` forms,
migrate call sites, remove now-unused `variable` declarations.

**Tech Stack:** Lean 4, mathlib's `CategoryTheory.Functor.Currying`
(`Functor.uncurry`), `CategoryTheory.Elements`
(`CategoryOfElements.map`, `elementsPrecomp`), project's existing
`FunctorFromData` / `NatTransFromData`
(`Utilities/Grothendieck.lean:1067,1221`), `presheafPRACatBifunctor`,
`presheafCat`, `praPositionsNat`, `praPositionsNatTarget`,
`praPositionsNat_app_eq_presheafCatFunctor`, `ccrNewIndexFunctor`,
`ccrNewIndexNat`, `ccrNewFamilyFunctor`, `ccrNewFamilyNat`,
`ccrElementsFunctor`, `catULiftFunctor2`, `typeCatLift`.

**Reference spec:**
`docs/superpowers/specs/2026-04-18-praDirections-naturality-design.md`.

**Project policy reminders:**

- No `sorry`, `admit`, `axiom`, `noncomputable`, `Classical.choice`,
  or `Quot.out`/`Quotient.out`.
- 80-character line limit.
- Build with `lake build`; test with `lake test`.  Never `lake clean`
  or `lake env lean`.
- Re-run `lake build` and `lake test` after each edit.
- When a proof does not close, use `_` to see the goal; never
  `sorry`.
- Factoring-out-lemmas technique for stuck proofs.
- No unused `universe` or `variable` declarations.

---

## File Structure

One file is the heavy lifter; the rest are small updates.

**Modified:** `GebLean/PresheafPRA.lean`

- Tasks 1–6 add the new infrastructure (uncurried base, two
  `FunctorFromData` bundles per side, extracted nat-transs).
- Tasks 7–9 add the three bridge lemmas.
- Task 10 adds `private praPositionsUnwidened`.
- Tasks 11–12 rewrite `praPositions` and `praDirectionsAt` bodies.
- Task 13 migrates any downstream call sites in other `GebLean/`
  files.
- Task 14 deletes `praDirectionsAtFunctorOp`,
  `praDirectionsAtFunctor`, and `praPositionsPresheaf`.
- Task 15 removes unused `variable` declarations (validation).

**Modified:** `GebLean/PresheafPRAUMorph.lean` (only if Task 13 finds
references there).

**Created:** `GebLeanTests/Utilities/PresheafPRADirNat.lean`.

**Modified:** `GebLeanTests.lean` — one new import line (Task 17).

**Modified:** `.session/workstreams/presheaf-pra.md`,
`.session/workstreams/pra-universal-morphisms.md` — best-effort
renames (Task 23).

---

## Task 1: Uncurry `presheafPRACatBifunctor`

**Files:**
- Modify: `GebLean/PresheafPRA.lean` (insert near the top of
  `section PresheafPRAAccessors`, above `praPositionsNatTarget`)

- [ ] **Step 1: Locate the insertion point**

Run:
```bash
grep -n "section PresheafPRAAccessors\|def praPositionsNatTarget" \
  GebLean/PresheafPRA.lean
```

Expected: `section PresheafPRAAccessors` at line ≈ 147,
`praPositionsNatTarget` at line ≈ 161.

- [ ] **Step 2: Add the uncurried bifunctor**

Insert immediately after `section PresheafPRAAccessors`, before
`praPositionsNatTarget`:

```lean
/--
The uncurried form of `presheafPRACatBifunctor`, as a functor
`Catᵒᵖ × Catᵒᵖ ⥤ Cat`.  Used as the base category for the
`Grothendieck`-indexed natural transformations `praDirectionsNatOp`
and `praDirectionsNat`.
-/
def presheafPRACatBifunctorUncurried :
    (Cat.{v_J, u_J}ᵒᵖ × Cat.{v_I, u_I}ᵒᵖ) ⥤
      Cat.{max u_I u_J w_I w',
        max u_I u_J v_I v_J (w_I + 1) (w' + 1)} :=
  Functor.uncurry.obj
    presheafPRACatBifunctor.{u_I, v_I, u_J, v_J, w_I, w'}
```

Notes for the implementer:

- If `Functor.uncurry.obj` does not directly elaborate at these
  universes, try `CategoryTheory.Functor.uncurry` or mathlib's
  `Functor.uncurried`.  The exact name may vary slightly across
  mathlib versions; search with:
  ```bash
  grep -n "def uncurry\|def Functor.uncurry" \
    .lake/packages/mathlib/Mathlib/CategoryTheory/Functor/Currying.lean
  ```
- If universes do not align, apply a universe-lift to
  `presheafPRACatBifunctor` first (e.g., through a composition with
  a `Cat.uliftFunctor2`-style helper in `Utilities/Families.lean`),
  then uncurry.  Do **not** reimplement uncurrying by hand —
  `Functor.uncurry` is foundational.
- The `×` here is `CategoryTheory.Prod` for product categories; if
  the product is already available via `open CategoryTheory` at the
  top of the file, the notation should work.  Otherwise, the
  qualified form `CategoryTheory.Prod _ _` may be needed.

- [ ] **Step 3: Build**

Run: `lake build GebLean.PresheafPRA`
Expected: success.

If the build reports a universe mismatch or unknown identifier,
adjust per the notes above.  Use `_` to see Lean's expected shape.

- [ ] **Step 4: Full build and test**

Run: `lake build && lake test`
Expected: both succeed, no warnings.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "$(cat <<'EOF'
Add presheafPRACatBifunctorUncurried

Uncurried form of presheafPRACatBifunctor, used as the base category
for the Grothendieck-indexed natural transformations that follow.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 2: Op-side `sourceData`

**Files:**
- Modify: `GebLean/PresheafPRA.lean` (append after
  `presheafPRACatBifunctorUncurried`)

- [ ] **Step 1: Add `sourceData`**

Insert after `presheafPRACatBifunctorUncurried`:

```lean
/--
Source data for the Op-form directions natural transformation.

At each pair `(J, I) : Catᵒᵖ × Catᵒᵖ`, the fibre is a functor
`PresheafPRACat I J ⥤ Cat` sending `P` to
`(P ⋙ ccrNewIndexFunctor (presheafCat I)).Elements` — the category
of elements of the presheaf of positions at `P`.

The `hom` field transports these element categories along base
changes in `(J, I)`, using `CategoryOfElements.map` and the
`ccrNewIndexNat` naturality.
-/
private def sourceData :
    FunctorFromData
      presheafPRACatBifunctorUncurried.{u_I, v_I, u_J, v_J, w_I, w'}
      (E := Cat.{max u_I u_J w_I w',
        max u_I u_J v_I v_J (w_I + 1) (w' + 1)})
      where
  fib JI := _
  hom f := _
  hom_id JI := _
  hom_comp f g := _
```

Notes for the implementer:

- Each `_` is a hole to fill in after reading the unsolved-goals
  error from `lake build`.  Do not use `sorry`.
- `fib JI`: at each `JI = (J, I)`, produce a functor
  `PresheafPRACat I J ⥤ Cat` whose `obj P` is
  `Cat.of ((P.toFunctor ⋙ ccrNewIndexFunctor (↑(presheafCat I.unop))).Elements)`
  and whose `map α` is the induced functor on elements (via
  `CategoryOfElements.map` on `α ▷ ccrNewIndexFunctor …`).
- `hom f`: at each `JI₁`, a nat-trans from `fib JI₁` to
  `presheafPRACatBifunctorUncurried.map f ⋙ fib JI₂`.  Each
  component at `P` is the functor on elements induced by `f`'s
  action through `elementsPrecomp` and the `ccrNewIndexNat`
  naturality in `I`.
- `hom_id`, `hom_comp`: coherence.  Expected to close with
  `apply Cat.Hom.ext; rfl` or a short `ext` + `simp` block.
- If the components are unwieldy to inline, factor them into
  `private def` helpers above `sourceData` — e.g.,
  `private def sourceDataFib JI : …`,
  `private def sourceDataHom f : …`.

- [ ] **Step 2: Fill in each hole**

For each `_`, run `lake build GebLean.PresheafPRA`, read the
"unsolved goals" output, and write the expression.  Use `#check` on
the types to verify shape match.

- [ ] **Step 3: Verify no `_` / `sorry` remains**

```bash
grep -n "sorry\|admit" GebLean/PresheafPRA.lean
```
Expected: no matches.

- [ ] **Step 4: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "$(cat <<'EOF'
Add Op-side sourceData for directions natural transformation

FunctorFromData bundle over presheafPRACatBifunctorUncurried whose
fibres are the P-indexed element categories used as the source of
praDirectionsNatOp.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 3: Op-side `targetData`

**Files:**
- Modify: `GebLean/PresheafPRA.lean` (append after `sourceData`)

- [ ] **Step 1: Add `targetData`**

Insert after `sourceData`:

```lean
/--
Target data for the Op-form directions natural transformation.

Constant in `P`: at each `(J, I)`, the fibre is the constant
functor on `PresheafPRACat I J` at the widened
`(Iᵒᵖ ⥤ Type w_I)ᵒᵖ` — the same target shape as
`ccrNewFamilyNatTarget`, independent of `P`.

The `hom` field transports the widened opposite presheaf category
along base changes in the `I` coordinate (the `J` coordinate is
ignored, since the target depends only on `I`).
-/
private def targetData :
    FunctorFromData
      presheafPRACatBifunctorUncurried.{u_I, v_I, u_J, v_J, w_I, w'}
      (E := Cat.{max u_I u_J w_I w',
        max u_I u_J v_I v_J (w_I + 1) (w' + 1)})
      where
  fib JI := _
  hom f := _
  hom_id JI := _
  hom_comp f g := _
```

Notes:

- `fib JI`: at `JI = (J, I)`, return
  `(Functor.const (PresheafPRACat I J)).obj X` where `X` is the
  widened `(Iᵒᵖ ⥤ Type w_I)ᵒᵖ`.  Precisely,
  `X = catULiftFunctor2.{…}.obj (Cat.opFunctor.obj (presheafCatFunctor.obj I))`
  (or equivalent — copy the shape from `praPositionsNatTarget`'s
  body for the universe handling).
- `hom f`: since `fib` is constant in `P`, `hom f` is a nat-trans
  between constant functors, which is the constant-at-each-object
  value of a morphism in `Cat`.  The morphism is
  `(Cat.opFunctor ⋙ catULiftFunctor2).map (f.fst)` if we
  project the `I`-component of `f : (J₁, I₁) ⟶ (J₂, I₂)`, or
  similar — work out the exact expression by following the
  `ccrNewFamilyNatTarget`-style construction adapted to a bifunctor
  base.
- `hom_id`, `hom_comp`: follow from `Cat.opFunctor.map_id`,
  `Cat.opFunctor.map_comp`, and `catULiftFunctor2`'s functoriality.
  Expected to close with `apply Cat.Hom.ext; rfl` / `ext; simp`.

- [ ] **Step 2: Fill in holes**

Same method as Task 2 — inspect, write, repeat.

- [ ] **Step 3: Verify no `sorry`/`admit`**

```bash
grep -n "sorry\|admit" GebLean/PresheafPRA.lean
```
Expected: no matches.

- [ ] **Step 4: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "$(cat <<'EOF'
Add Op-side targetData for directions natural transformation

FunctorFromData bundle whose fibres are constant in P at the widened
(Iᵒᵖ ⥤ Type w_I)ᵒᵖ, used as the target of praDirectionsNatOp.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 4: Op-side `natData` and `praDirectionsNatOp`

**Files:**
- Modify: `GebLean/PresheafPRA.lean` (append after `targetData`)

- [ ] **Step 1: Add `natData` and extract `praDirectionsNatOp`**

Insert after `targetData`:

```lean
/--
`NatTransFromData` linking `sourceData` to `targetData`.

At each `(J, I)`, the fibre nat-trans sends each `P` to the Op-form
directions composite:
  `elementsPrecomp P ⋙ ccrNewFamilyFunctor (presheafCat I)`,
post-composed with the `ULift`/`ULiftHom` widening that matches
`targetData`'s Cat universe.

The coherence condition follows from `ccrNewFamilyNat`'s naturality
in `I` together with `elementsPrecomp`'s compatibility with
whiskering in `J`.
-/
private def natData :
    NatTransFromData
      presheafPRACatBifunctorUncurried.{u_I, v_I, u_J, v_J, w_I, w'}
      sourceData.{u_I, v_I, u_J, v_J, w_I, w'}
      targetData.{u_I, v_I, u_J, v_J, w_I, w'} where
  fibNat JI := _
  coherence f := _

/--
The Op-form natural transformation on directions, natural in
`(J, I, P)` via the Grothendieck of
`presheafPRACatBifunctorUncurried`.  Source:
`functorFromData … sourceData`.  Target:
`functorFromData … targetData`.

Each per-component at `⟨(J, I), P⟩` is the old per-`(I, J, P)`
`praDirectionsAtFunctorOp`, up to the universe-widening lifts
inherited from `ccrNewFamilyNatTarget`.
-/
def praDirectionsNatOp :
    functorFromData presheafPRACatBifunctorUncurried.{…}
        sourceData.{…} ⟶
      functorFromData presheafPRACatBifunctorUncurried.{…}
        targetData.{…} :=
  natTransFrom _ _ _ natData.{…}
```

Notes:

- The two `_` holes in `natData` are the fibre-nat-trans and the
  coherence proof.  Each should be expressible using
  `elementsPrecomp`, `ccrNewFamilyNat`, and the widening composite
  — follow the structure of `sourceData.hom` and `targetData.hom`
  from Tasks 2–3.
- The coherence proof's expected shape: `apply NatTrans.ext;
  funext P; apply Cat.Hom.ext; <rfl or short ext+simp>`.
- If coherence does not close cleanly, factor it into a named
  lemma above `natData` — e.g.,
  `private lemma natData_coherence_aux : … := …`.

- [ ] **Step 2: Inspect goals, fill in holes**

Use `_` + `lake build GebLean.PresheafPRA` to see each unsolved
goal and fill in.

- [ ] **Step 3: Verify no `_` / `sorry`**

```bash
grep -n "sorry\|admit" GebLean/PresheafPRA.lean
```
Expected: no matches.

- [ ] **Step 4: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 5: Axiom check**

Temporarily add to the end of `GebLean/PresheafPRA.lean`:
```lean
#print axioms praDirectionsNatOp
```
Run `lake build GebLean.PresheafPRA`.  Verify output lists only
`propext`, `Classical.choice`, `Quot.sound`.  Remove the line.

- [ ] **Step 6: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "$(cat <<'EOF'
Add praDirectionsNatOp: Op-form (I, J, P)-natural directions

Natural transformation between Grothendieck-indexed functors built
via FunctorFromData / NatTransFromData.  Per-component at
⟨(J, I), P⟩ is the old praDirectionsAtFunctorOp up to widening.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 5: Non-Op side `sourceDataPre`, `targetDataPre`

**Files:**
- Modify: `GebLean/PresheafPRA.lean` (append after
  `praDirectionsNatOp`)

- [ ] **Step 1: Add `sourceDataPre` and `targetDataPre`**

Insert after `praDirectionsNatOp`:

```lean
/--
Source data for the non-Op form.  Like `sourceData` but using the
`.ElementsPre` shape (the opposite of `.Elements`, suited to the
non-Op target).
-/
private def sourceDataPre :
    FunctorFromData
      presheafPRACatBifunctorUncurried.{u_I, v_I, u_J, v_J, w_I, w'}
      (E := Cat.{max u_I u_J w_I w',
        max u_I u_J v_I v_J (w_I + 1) (w' + 1)}) where
  fib JI := _
  hom f := _
  hom_id JI := _
  hom_comp f g := _

/--
Target data for the non-Op form.  Like `targetData` but with the
non-Op target: the widened `(Iᵒᵖ ⥤ Type w_I)` (no outer `ᵒᵖ`).
-/
private def targetDataPre :
    FunctorFromData
      presheafPRACatBifunctorUncurried.{u_I, v_I, u_J, v_J, w_I, w'}
      (E := Cat.{max u_I u_J w_I w',
        max u_I u_J v_I v_J (w_I + 1) (w' + 1)}) where
  fib JI := _
  hom f := _
  hom_id JI := _
  hom_comp f g := _
```

Notes:

- `sourceDataPre.fib (J, I)`'s `obj P` is
  `Cat.of (P.toFunctor ⋙ ccrNewIndexFunctor (↑(presheafCat I.unop))).ElementsPre`.
  `.ElementsPre` differs from `.Elements` by an opposite on the
  category, matching how `praDirectionsAtFunctor` differed from
  `praDirectionsAtFunctorOp`.
- `targetDataPre.fib (J, I) := (Functor.const _).obj X` where `X`
  is the widened `(Iᵒᵖ ⥤ Type w_I)` (no outer `ᵒᵖ`).
- The `hom` fields follow the same patterns as Tasks 2–3 but with
  the opposite-on-one-side replaced.

- [ ] **Step 2: Fill in holes, verify, build**

Same method as Tasks 2–4.  Run `lake build && lake test`.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "$(cat <<'EOF'
Add non-Op sourceDataPre and targetDataPre

Parallel FunctorFromData bundles for the non-Op directions natural
transformation.  Use .ElementsPre source and non-Op target shapes.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 6: Non-Op `natDataPre` and `praDirectionsNat`

**Files:**
- Modify: `GebLean/PresheafPRA.lean` (append after `targetDataPre`)

- [ ] **Step 1: Add `natDataPre` and extract `praDirectionsNat`**

Insert after `targetDataPre`:

```lean
/--
`NatTransFromData` for the non-Op side.  Parallel to `natData`,
sending each `P` to the non-Op form of the directions composite.
-/
private def natDataPre :
    NatTransFromData
      presheafPRACatBifunctorUncurried.{u_I, v_I, u_J, v_J, w_I, w'}
      sourceDataPre.{u_I, v_I, u_J, v_J, w_I, w'}
      targetDataPre.{u_I, v_I, u_J, v_J, w_I, w'} where
  fibNat JI := _
  coherence f := _

/--
The non-Op form natural transformation on directions, natural in
`(J, I, P)`.  Related to `praDirectionsNatOp` by the `.op ⋙
unopUnop` reshape (see `praDirectionsNat_eq_op_of_praDirectionsNatOp`).
-/
def praDirectionsNat :
    functorFromData presheafPRACatBifunctorUncurried.{…}
        sourceDataPre.{…} ⟶
      functorFromData presheafPRACatBifunctorUncurried.{…}
        targetDataPre.{…} :=
  natTransFrom _ _ _ natDataPre.{…}
```

- [ ] **Step 2: Fill in holes, build, test**

Same method.

- [ ] **Step 3: Axiom check**

Temporarily add `#print axioms praDirectionsNat` to the end.  Run
`lake build GebLean.PresheafPRA`.  Verify standard axioms only.
Remove.

- [ ] **Step 4: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "$(cat <<'EOF'
Add praDirectionsNat: non-Op (I, J, P)-natural directions

Parallel natural transformation to praDirectionsNatOp with
.ElementsPre source and non-Op target.  The two nat-transs are
related by a bridge lemma in a subsequent task.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 7: Bridge lemma for `praDirectionsNatOp`

**Files:**
- Modify: `GebLean/PresheafPRA.lean` (append after
  `praDirectionsNat`)

- [ ] **Step 1: Add the Op-side bridge lemma**

Insert after `praDirectionsNat`:

```lean
/--
Bridge lemma: each `praDirectionsNatOp.app` unfolds to the
`elementsPrecomp P ⋙ ccrNewFamilyFunctor (presheafCat I)` composite,
post-composed with the Op-side widening.  Not marked `@[simp]`.
-/
theorem praDirectionsNatOp_app_eq_elementsPrecomp_ccrNewFamilyFunctor
    (I : Type u_I) [Category.{v_I} I]
    (J : Type u_J) [Category.{v_J} J]
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J) :
    (praDirectionsNatOp.{u_I, v_I, u_J, v_J, w_I, w'}.app
      ⟨⟨Opposite.op (Cat.of Jᵒᵖ),
         Opposite.op (Cat.of Iᵒᵖ)⟩, P⟩).toFunctor =
    ((CategoryTheory.elementsPrecomp P) ⋙
      ccrNewFamilyFunctor.{max v_I u_I (w_I + 1),
        max u_I w_I, w'} (↑(presheafCat.{u_I, v_I, w_I} I))) ⋙
      /- widening lifts matching targetData's Cat universe -/ _ := by
  rfl
```

Notes:

- The widening lifts on the RHS must match the widening chosen in
  `targetData.fib` (Task 3).  Copy exactly the widening sequence
  used there.
- If `rfl` does not close, try `apply Cat.Hom.ext; rfl`, or unfold
  `praDirectionsNatOp`, `natTransFrom`, `natData`.
- If the Grothendieck-object constructor shape
  `⟨⟨Opposite.op (Cat.of Jᵒᵖ), Opposite.op (Cat.of Iᵒᵖ)⟩, P⟩` does
  not elaborate exactly as written, adjust to match the shape
  `.app` expects at this call — use `#check` to inspect.

- [ ] **Step 2: Build and verify**

Run: `lake build GebLean.PresheafPRA`
Expected: success.

- [ ] **Step 3: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 4: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "$(cat <<'EOF'
Add praDirectionsNatOp_app_eq_elementsPrecomp_ccrNewFamilyFunctor

Bridge lemma unfolding each per-component of praDirectionsNatOp to
the familiar elementsPrecomp + ccrNewFamilyFunctor composite.  Not
@[simp] to avoid unfolding cycles.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 8: Bridge lemma for `praDirectionsNat`

**Files:**
- Modify: `GebLean/PresheafPRA.lean` (append after the Op bridge
  lemma)

- [ ] **Step 1: Add the non-Op bridge lemma**

Insert:

```lean
/--
Bridge lemma: each `praDirectionsNat.app` unfolds to the non-Op
form of the composite — parallel to the Op-side bridge, with
`.ElementsPre` source and non-Op target.
-/
theorem praDirectionsNat_app_eq_elementsPrecomp_ccrNewFamilyFunctor
    (I : Type u_I) [Category.{v_I} I]
    (J : Type u_J) [Category.{v_J} J]
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J) :
    (praDirectionsNat.{u_I, v_I, u_J, v_J, w_I, w'}.app
      ⟨⟨Opposite.op (Cat.of Jᵒᵖ),
         Opposite.op (Cat.of Iᵒᵖ)⟩, P⟩).toFunctor =
    /- the non-Op analog: elementsPrecomp on .ElementsPre +
       (ccrNewFamilyFunctor).op ⋙ unopUnop, post-composed with
       targetDataPre's widening -/ _ := by
  rfl
```

- [ ] **Step 2: Fill in RHS, build, test**

Copy the exact shape from `targetDataPre` / `natDataPre`.  Close
the `_` on RHS with the correct expression.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "$(cat <<'EOF'
Add praDirectionsNat_app_eq_elementsPrecomp_ccrNewFamilyFunctor

Non-Op bridge lemma, parallel to the Op-side bridge.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 9: Bridge lemma relating `praDirectionsNat` and `praDirectionsNatOp`

**Files:**
- Modify: `GebLean/PresheafPRA.lean` (append after the non-Op
  bridge lemma)

- [ ] **Step 1: Add the Op / non-Op relation lemma**

Insert:

```lean
/--
The non-Op form is the `.op ⋙ unopUnop`-reshape of the Op form at
each per-component level.  Not marked `@[simp]` to avoid unfolding
cycles.
-/
theorem praDirectionsNat_eq_op_of_praDirectionsNatOp
    (X : Grothendieck presheafPRACatBifunctorUncurried.{…}) :
    (praDirectionsNat.{…}.app X).toFunctor =
      (praDirectionsNatOp.{…}.app X).toFunctor.op ⋙
        unopUnop _ := by
  rfl
```

- [ ] **Step 2: Build, verify `rfl` closes**

If not, unfold `natTransFrom` / `natData` / `natDataPre` and try
`apply Cat.Hom.ext; rfl` or a short `ext` + `simp`.

- [ ] **Step 3: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 4: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "$(cat <<'EOF'
Add praDirectionsNat_eq_op_of_praDirectionsNatOp

Relates the non-Op and Op natural forms via .op ⋙ unopUnop at each
per-component level.  Not @[simp].

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 10: Add `private praPositionsUnwidened`

**Files:**
- Modify: `GebLean/PresheafPRA.lean` (append after the relation
  bridge lemma)

- [ ] **Step 1: Add the private helper**

Insert:

```lean
/--
Unwidened form of the positions presheaf at a given PRA.

Internal helper absorbing the `ULift`/`ULiftHom` unwrap of
`praPositionsNat.app`.  Produces the underlying `Jᵒᵖ ⥤ Type w'`
used by `praPositions` and `praDirectionsAt`.
-/
private def praPositionsUnwidened
    (I : Type u_I) [Category.{v_I} I]
    (J : Type u_J) [Category.{v_J} J]
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J) :
    Jᵒᵖ ⥤ Type w' :=
  ((Functor.whiskeringRight Jᵒᵖ _ _).obj
    (ccrNewIndexFunctor.{max v_I u_I (w_I + 1),
      max u_I w_I, w'}
      (↑(presheafCat.{u_I, v_I, w_I} I)))).obj P
```

Notes:

- The body is identical to the current `praPositionsPresheaf`; this
  is the rename-to-`private`-helper that Section 4 of the spec
  anticipated.
- The `private` keyword ensures this is not part of the module's
  public surface.  It's only used by `praPositions` and anywhere
  inside this file that needs the underlying presheaf.

- [ ] **Step 2: Build and verify**

Run: `lake build GebLean.PresheafPRA`
Expected: success.

- [ ] **Step 3: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 4: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "$(cat <<'EOF'
Add private praPositionsUnwidened helper

Internal function returning the non-widened positions presheaf.
Used by praPositions and available inside the file for any
subsequent rewrites that need the underlying non-widened form.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 11: Rewrite `praPositions` to use `praPositionsUnwidened`

**Files:**
- Modify: `GebLean/PresheafPRA.lean` (the `praPositions` def
  currently at lines 279–281)

- [ ] **Step 1: Locate**

```bash
grep -n "def praPositions " GebLean/PresheafPRA.lean
```

- [ ] **Step 2: Rewrite the body**

Find:
```lean
def praPositions (j : Jᵒᵖ) : Type w' :=
  (praPositionsPresheaf I J P).obj j
```

Replace with:
```lean
def praPositions (j : Jᵒᵖ) : Type w' :=
  (praPositionsUnwidened I J P).obj j
```

The signature is unchanged (same explicit `I`, `J`, `P`, `j`
arguments via the surrounding `variable`s, same return type).

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
Rewrite praPositions to use praPositionsUnwidened

Same body, named through the new private helper.  Prepares the way
for deletion of praPositionsPresheaf.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 12: Rewrite `praDirectionsAt` to use `praDirectionsNat`

**Files:**
- Modify: `GebLean/PresheafPRA.lean` (the `praDirectionsAt` def
  currently at lines 311–314)

- [ ] **Step 1: Locate**

```bash
grep -n "def praDirectionsAt " GebLean/PresheafPRA.lean
```

- [ ] **Step 2: Rewrite the body**

Find:
```lean
def praDirectionsAt (j : Jᵒᵖ)
    (a : praPositions I J P j) : Iᵒᵖ ⥤ Type w_I :=
  (praDirectionsAtFunctor I J P).obj
    (Opposite.op ⟨j, a⟩)
```

Replace with:
```lean
def praDirectionsAt (j : Jᵒᵖ)
    (a : praPositions I J P j) : Iᵒᵖ ⥤ Type w_I :=
  (praDirectionsNat.{u_I, v_I, u_J, v_J, w_I, w'}.app
      ⟨⟨Opposite.op (Cat.of Jᵒᵖ),
         Opposite.op (Cat.of Iᵒᵖ)⟩, P⟩).toFunctor.obj
    (Opposite.op ⟨j, a⟩)
```

Notes:

- The `⟨⟨…, …⟩, P⟩` is a `Grothendieck` object constructor: the
  outer pair is the Cat-object pair `(J, I)` in the base, and `P`
  is the fibre.  If the explicit form is awkward, use
  `Grothendieck.mk` if available, or factor into a private helper
  `private def praDirGrothObj I J P : Grothendieck … :=
  ⟨⟨Opposite.op (Cat.of Jᵒᵖ), Opposite.op (Cat.of Iᵒᵖ)⟩, P⟩`.
- The return type `Iᵒᵖ ⥤ Type w_I` is unchanged.  The RHS's
  unwidening happens because `praDirectionsNat` lands in the
  non-widened target `(Iᵒᵖ ⥤ Type w_I)` (no outer `ᵒᵖ`).  If any
  widening-unwidening step is required (unlikely given the non-Op
  `targetDataPre`), use the appropriate `ULiftHom.down` /
  `ULift.downFunctor` at the end.

- [ ] **Step 3: Build**

Run: `lake build GebLean.PresheafPRA`
Expected: success.

If the Grothendieck-object constructor `⟨⟨…⟩, P⟩` doesn't elaborate,
use `#check` on `praDirectionsNat.app` to see the expected input
shape and adjust.

- [ ] **Step 4: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "$(cat <<'EOF'
Rewrite praDirectionsAt to use praDirectionsNat

Routes through the (J, I, P)-natural form.  Signature unchanged.
Prepares the way for deletion of praDirectionsAtFunctor*.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 13: Migrate call sites in other `GebLean/` files

**Files:**
- Inspect (and possibly modify): `GebLean/PresheafPRAUMorph.lean`
  and any other `GebLean/*.lean` files that reference the
  to-be-deleted names.

- [ ] **Step 1: Enumerate call sites**

Run:
```bash
grep -rn "praDirectionsAtFunctorOp\|praDirectionsAtFunctor\|\
praPositionsPresheaf" GebLean/
```

Expected: matches in `PresheafPRA.lean` (the definitions, which
will be deleted in Task 14 — don't migrate those yet); possibly
matches in `PresheafPRAUMorph.lean` or other files.

- [ ] **Step 2: Migrate per call site**

For each external call site:

- A reference to `praDirectionsAtFunctor I J P` becomes
  `(praDirectionsNat.app ⟨⟨Opposite.op (Cat.of Jᵒᵖ),
  Opposite.op (Cat.of Iᵒᵖ)⟩, P⟩).toFunctor`.  Adjust for explicit
  universe annotations as needed.
- A reference to `praDirectionsAtFunctorOp I J P` becomes
  `(praDirectionsNatOp.app ⟨⟨Opposite.op (Cat.of Jᵒᵖ),
  Opposite.op (Cat.of Iᵒᵖ)⟩, P⟩).toFunctor`.
- A reference to `praPositionsPresheaf I J P` becomes
  `praPositionsUnwidened I J P` if it's inside `PresheafPRA.lean`.
  If the reference is in another file, `praPositionsUnwidened` is
  `private` and cannot be used — adjust the calling code to use
  `praPositionsNat.{…}.app ⟨⟨Opposite.op (Cat.of Jᵒᵖ)⟩⟩.app
  ⟨Opposite.op (Cat.of Iᵒᵖ)⟩.toFunctor.obj P` (and the appropriate
  un-widening), OR if the reference is common enough, consider
  promoting the helper to non-private (via a separate `def` with a
  different name and a docstring).

If no external call sites exist, this task is trivial — just
document the grep result in the commit message.

- [ ] **Step 3: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 4: Commit (only if changes were made)**

```bash
git add GebLean/PresheafPRAUMorph.lean  # or whichever
git commit -m "$(cat <<'EOF'
Migrate call sites to praDirectionsNat/praDirectionsNatOp

Replaces references to the to-be-deleted praDirectionsAtFunctor,
praDirectionsAtFunctorOp, and praPositionsPresheaf with the
(I, J, P)-natural forms.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

If the grep showed no external call sites, skip the commit and
note in the plan's self-review that Task 13 was a no-op.

---

## Task 14: Delete the old definitions

**Files:**
- Modify: `GebLean/PresheafPRA.lean`

- [ ] **Step 1: Locate**

```bash
grep -n "def praDirectionsAtFunctorOp\|def praDirectionsAtFunctor \
\|def praPositionsPresheaf " GebLean/PresheafPRA.lean
```

Expected: three matches.

- [ ] **Step 2: Delete `praDirectionsAtFunctorOp`**

Find and delete the block (around lines 283–294):
```lean
/--
The directions functor into `PSh(I)ᵒᵖ`: for a fixed
PRA `P`, sends an element `(j, a)` of the positions
presheaf to `op (E_T(j,a))`.
-/
def praDirectionsAtFunctorOp :
    (praPositionsPresheaf I J P).Elements ⥤
      (Iᵒᵖ ⥤ Type w_I)ᵒᵖ :=
  CategoryTheory.elementsPrecomp P ⋙
    ccrNewFamilyFunctor.{max v_I u_I (w_I + 1),
      max u_I w_I, w'}
      (↑(presheafCat.{u_I, v_I, w_I} I))
```

- [ ] **Step 3: Delete `praDirectionsAtFunctor`**

Find and delete the block (around lines 296–306):
```lean
/--
The directions functor `E_T` from the nLab PRA
formula: sends an element `(j, a)` of the opposite
of the positions presheaf to the directions presheaf
`E_T(j,a) : Iᵒᵖ ⥤ Type w_I`.
-/
def praDirectionsAtFunctor :
    (praPositionsPresheaf I J P).ElementsPre ⥤
      (Iᵒᵖ ⥤ Type w_I) :=
  (praDirectionsAtFunctorOp I J P).op ⋙
    unopUnop _
```

- [ ] **Step 4: Delete `praPositionsPresheaf`**

Find and delete the block (around lines 257–270):
```lean
/--
Bridge to the non-widened form of the positions presheaf.
...
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

- [ ] **Step 5: Verify no references**

```bash
grep -rn "praDirectionsAtFunctorOp\|praDirectionsAtFunctor \
\|praPositionsPresheaf" GebLean/ GebLeanTests/
```

Expected: no matches (Tests don't touch these yet; that's correct).

- [ ] **Step 6: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 7: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "$(cat <<'EOF'
Delete praDirectionsAtFunctor*, praPositionsPresheaf

All three are replaced by the (I, J, P)-natural forms:
- praDirectionsAtFunctorOp → praDirectionsNatOp
- praDirectionsAtFunctor → praDirectionsNat
- praPositionsPresheaf → praPositionsUnwidened (private) +
  praPositionsNat for the public natural form.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 15: Variable-removal validation

**Files:**
- Modify: `GebLean/PresheafPRA.lean`

- [ ] **Step 1: Locate the `variable` declarations**

```bash
grep -n "^variable " GebLean/PresheafPRA.lean
```

Expected: `variable (I : Type u_I) [Category.{v_I} I]`,
`variable (J : Type u_J) [Category.{v_J} J]` near top, plus
`variable (P : PresheafPRACat …)` later (inside a section).

- [ ] **Step 2: Remove `variable (P …)`**

Delete the `variable (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I,
w'} I J)` declaration (around line 274).  `praPositions` and
`praDirectionsAt` already take `P` explicitly via their own
signatures after Tasks 11–12.

- [ ] **Step 3: Check whether `variable (I …)` and `variable (J …)`
      are still needed**

Run:
```bash
lake build GebLean.PresheafPRA
```

If the build succeeds, the `I` and `J` `variable`s are either (a)
still needed by remaining signatures, in which case they stay, or
(b) no longer needed, in which case Lean should emit an
"unused variable" warning — but the project's lakefile may not show
that by default.

Inspect which surviving definitions take `I` and `J` as explicit
parameters.  After Task 14, those should be at least `praPositions`
and `praDirectionsAt`, plus any new accessors.

- [ ] **Step 4: Remove unused `I` and `J` `variable`s, or leave
      them with a comment**

If removal is safe (build still passes), delete.  If they are
still in use, leave them and add a one-line comment above
explaining why they remain:
```lean
-- `I` and `J` remain in scope for the explicit-parameter
-- signatures of `praPositions` and `praDirectionsAt`.
```

- [ ] **Step 5: Full build and test**

Run: `lake build && lake test`
Expected: both succeed, zero warnings.

- [ ] **Step 6: Axiom check on the main nat-transs**

Temporarily append to the file:
```lean
#print axioms praDirectionsNatOp
#print axioms praDirectionsNat
#print axioms praPositionsNat
```
Run `lake build GebLean.PresheafPRA`.  Verify each reports only
`propext`, `Classical.choice`, `Quot.sound`.  Remove the temporary
lines.

- [ ] **Step 7: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "$(cat <<'EOF'
Remove variable (P …); confirm variable (I …)/(J …) status

Variable-removal validation: after the full (I, J, P) promotion of
positions and directions, variable (P …) is unused and removed.
Variable (I …) and (J …) status documented in the file.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 16: Create test file with type-sanity checks

**Files:**
- Create: `GebLeanTests/Utilities/PresheafPRADirNat.lean`

- [ ] **Step 1: Verify directory**

```bash
ls GebLeanTests/Utilities/
```
Expected: `Tower.lean`, `Families.lean`, `PresheafPRANat.lean` all
present.

- [ ] **Step 2: Create the test file**

Create `GebLeanTests/Utilities/PresheafPRADirNat.lean`:

```lean
import GebLean.PresheafPRA

/-!
# Tests for (I, J, P)-Naturality of praDirectionsNat and
  praDirectionsNatOp

Type-signature sanity checks and small-example tests for the
Grothendieck-indexed natural transformations on directions in
`GebLean.PresheafPRA`.
-/

open GebLean CategoryTheory

attribute [local instance] CategoryTheory.uliftCategory

/-! ## Type-signature sanity -/

-- praDirectionsNatOp has the expected shape.
example :
    functorFromData
        presheafPRACatBifunctorUncurried.{0, 0, 0, 0, 0, 0}
        sourceData.{0, 0, 0, 0, 0, 0} ⟶
      functorFromData
        presheafPRACatBifunctorUncurried.{0, 0, 0, 0, 0, 0}
        targetData.{0, 0, 0, 0, 0, 0} :=
  praDirectionsNatOp.{0, 0, 0, 0, 0, 0}

-- praDirectionsNat has the expected shape.
example :
    functorFromData
        presheafPRACatBifunctorUncurried.{0, 0, 0, 0, 0, 0}
        sourceDataPre.{0, 0, 0, 0, 0, 0} ⟶
      functorFromData
        presheafPRACatBifunctorUncurried.{0, 0, 0, 0, 0, 0}
        targetDataPre.{0, 0, 0, 0, 0, 0} :=
  praDirectionsNat.{0, 0, 0, 0, 0, 0}
```

Notes:

- `sourceData`, `targetData`, `sourceDataPre`, `targetDataPre` are
  `private`.  If they cannot be referenced from outside
  `PresheafPRA.lean`, use `@[inline]` or promote them to non-private
  — or alternatively, phrase the `example` types more abstractly
  (e.g., write just the source/target shapes expanded to
  `Grothendieck … ⥤ Cat`).  If private-to-file is insurmountable,
  skip these two examples and use just `#check praDirectionsNat` /
  `#check praDirectionsNatOp` without an ascription.

- [ ] **Step 3: Build the file standalone**

Run: `lake build GebLeanTests.Utilities.PresheafPRADirNat`
Expected: success.

- [ ] **Step 4: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRADirNat.lean
git commit -m "$(cat <<'EOF'
Add type-signature sanity tests for praDirectionsNat*

New test file exercises the type signatures of praDirectionsNatOp
and praDirectionsNat at universe level 0.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 17: Register the test file

**Files:**
- Modify: `GebLeanTests.lean`

- [ ] **Step 1: Add the import line**

Add to `GebLeanTests.lean` after
`import GebLeanTests.Utilities.PresheafPRANat`:

```
import GebLeanTests.Utilities.PresheafPRADirNat
```

- [ ] **Step 2: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests.lean
git commit -m "$(cat <<'EOF'
Register GebLeanTests.Utilities.PresheafPRADirNat test file

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 18: Bridge-lemma collapse test

**Files:**
- Modify: `GebLeanTests/Utilities/PresheafPRADirNat.lean`
  (append)

- [ ] **Step 1: Add the test**

Append:

```lean
/-! ## Definitional collapse via the bridge lemmas -/

section CollapseTest

-- Op-side bridge applies at a concrete small base + PRA.
example (P : PresheafPRACat.{0, 0, 0, 0, 0, 0} PUnit PUnit) :
    (praDirectionsNatOp.{0, 0, 0, 0, 0, 0}.app
      ⟨⟨Opposite.op (Cat.of (PUnitᵒᵖ : Type 0)),
         Opposite.op (Cat.of (PUnitᵒᵖ : Type 0))⟩, P⟩).toFunctor =
      _ :=
  praDirectionsNatOp_app_eq_elementsPrecomp_ccrNewFamilyFunctor.{0, 0, 0, 0, 0, 0}
    PUnit PUnit P

end CollapseTest
```

Notes:

- Replace the RHS `_` with the exact expression from the bridge
  lemma's conclusion, specialized to `PUnit`/`PUnit`.
- If the `_` doesn't elaborate, use `by exact` form:
  ```lean
  example (P : …) : _ := by
    exact praDirectionsNatOp_app_eq_elementsPrecomp_ccrNewFamilyFunctor PUnit PUnit P
  ```

- [ ] **Step 2: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRADirNat.lean
git commit -m "$(cat <<'EOF'
Add bridge-lemma collapse test for praDirectionsNatOp

Verifies praDirectionsNatOp_app_eq_elementsPrecomp_ccrNewFamilyFunctor
at I = J = PUnit.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 19: Op / non-Op relation test

**Files:**
- Modify: `GebLeanTests/Utilities/PresheafPRADirNat.lean`
  (append)

- [ ] **Step 1: Add the test**

Append:

```lean
/-! ## Op / non-Op relation -/

section OpRelation

-- praDirectionsNat equals the .op ⋙ unopUnop-reshape of
-- praDirectionsNatOp at a concrete Grothendieck object.
example (P : PresheafPRACat.{0, 0, 0, 0, 0, 0} PUnit PUnit) :
    (praDirectionsNat.{0, 0, 0, 0, 0, 0}.app
      ⟨⟨Opposite.op (Cat.of (PUnitᵒᵖ : Type 0)),
         Opposite.op (Cat.of (PUnitᵒᵖ : Type 0))⟩, P⟩).toFunctor =
    (praDirectionsNatOp.{0, 0, 0, 0, 0, 0}.app
      ⟨⟨Opposite.op (Cat.of (PUnitᵒᵖ : Type 0)),
         Opposite.op (Cat.of (PUnitᵒᵖ : Type 0))⟩, P⟩).toFunctor.op ⋙
      unopUnop _ :=
  praDirectionsNat_eq_op_of_praDirectionsNatOp.{0, 0, 0, 0, 0, 0} _

end OpRelation
```

- [ ] **Step 2: Build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRADirNat.lean
git commit -m "$(cat <<'EOF'
Add Op / non-Op relation test

Verifies praDirectionsNat_eq_op_of_praDirectionsNatOp at a concrete
PRA over PUnit.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 20: Pointwise-accessor compatibility test

**Files:**
- Modify: `GebLeanTests/Utilities/PresheafPRADirNat.lean`
  (append)

- [ ] **Step 1: Add the test**

Append:

```lean
/-! ## Pointwise-accessor compatibility -/

section AccessorTest

-- praDirectionsAt produces the same value as direct extraction
-- from praDirectionsNat.
example (P : PresheafPRACat.{0, 0, 0, 0, 0, 0} PUnit PUnit)
    (j : (PUnitᵒᵖ : Type 0)ᵒᵖ)
    (a : praPositions PUnit PUnit P j) :
    praDirectionsAt PUnit PUnit P j a =
      (praDirectionsNat.{0, 0, 0, 0, 0, 0}.app
        ⟨⟨Opposite.op (Cat.of (PUnitᵒᵖ : Type 0)),
           Opposite.op (Cat.of (PUnitᵒᵖ : Type 0))⟩, P⟩).toFunctor.obj
        (Opposite.op ⟨j, a⟩) := by
  rfl
```

- [ ] **Step 2: Build and test**

Run: `lake build && lake test`
Expected: both succeed.

If `rfl` fails because the `praDirectionsAt` body doesn't match
verbatim what's on the RHS (e.g., because universe annotations
differ), inspect with `#check` and either: adjust the example to
match, or use `by simp [praDirectionsAt]` to unfold.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRADirNat.lean
git commit -m "$(cat <<'EOF'
Add pointwise-accessor compatibility test

Verifies that praDirectionsAt I J P j a unfolds to the expected
extraction from praDirectionsNat.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 21: Naturality-square test

**Files:**
- Modify: `GebLeanTests/Utilities/PresheafPRADirNat.lean`
  (append)

- [ ] **Step 1: Add the test**

Append:

```lean
/-! ## Naturality square -/

section NaturalitySquare

-- The identity base-change morphism in
-- Grothendieck(presheafPRACatBifunctorUncurried).
-- Naturality at an identity should close by rfl.
example
    (X : Grothendieck presheafPRACatBifunctorUncurried.{0, 0, 0, 0, 0, 0}) :
    (functorFromData presheafPRACatBifunctorUncurried.{0, 0, 0, 0, 0, 0}
      sourceData.{0, 0, 0, 0, 0, 0}).map (𝟙 X) ≫
      praDirectionsNatOp.{0, 0, 0, 0, 0, 0}.app X =
      praDirectionsNatOp.{0, 0, 0, 0, 0, 0}.app X ≫
      (functorFromData presheafPRACatBifunctorUncurried.{0, 0, 0, 0, 0, 0}
        targetData.{0, 0, 0, 0, 0, 0}).map (𝟙 X) :=
  praDirectionsNatOp.{0, 0, 0, 0, 0, 0}.naturality (𝟙 X)

end NaturalitySquare
```

Notes:

- Appeals directly to `praDirectionsNatOp.naturality` applied to
  the identity morphism at `X` — the simplest possible non-trivial
  instantiation.  If Lean complains about the universes or the
  existence of `sourceData`/`targetData` in scope (if they're
  `private`), either promote to non-private or rephrase the test
  using only `functorFromData` applied to `praDirectionsNatOp`'s
  own source/target (extracted via `Functor.obj`-of-a-`Nat-trans` or
  similar).

- [ ] **Step 2: Build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRADirNat.lean
git commit -m "$(cat <<'EOF'
Add naturality-square test for praDirectionsNatOp

Exercises the naturality at an identity morphism in the
Grothendieck base.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 22: Universe-polymorphism test

**Files:**
- Modify: `GebLeanTests/Utilities/PresheafPRADirNat.lean`
  (append)

- [ ] **Step 1: Add the test**

Append:

```lean
/-! ## Universe polymorphism -/

section UniversePoly

-- Exercise at mixed universes: u_I := 1, others 0.
example :
    functorFromData presheafPRACatBifunctorUncurried.{1, 0, 0, 0, 0, 0}
        sourceData.{1, 0, 0, 0, 0, 0} ⟶
      functorFromData presheafPRACatBifunctorUncurried.{1, 0, 0, 0, 0, 0}
        targetData.{1, 0, 0, 0, 0, 0} :=
  praDirectionsNatOp.{1, 0, 0, 0, 0, 0}

end UniversePoly
```

If `sourceData` / `targetData` are `private`, rephrase using
`praDirectionsNatOp`'s own declared type — e.g., via `(_ : _)` or
`#check` without ascription.

- [ ] **Step 2: Build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRADirNat.lean
git commit -m "$(cat <<'EOF'
Add universe-polymorphism test for praDirectionsNatOp

Exercises at mixed universes (u_I := 1, others 0) to catch
accidental universe specialization across six parameters.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 23: Update `.session/` notes

**Files:**
- Modify: `.session/workstreams/presheaf-pra.md`
- Modify: `.session/workstreams/pra-universal-morphisms.md`

These are session workstream notes, not released content.  Minimal
touch: replace stale references to the three deleted names
(`praDirectionsAtFunctorOp`, `praDirectionsAtFunctor`,
`praPositionsPresheaf`) with their replacements
(`praDirectionsNatOp`, `praDirectionsNat`, `praPositionsNat` or
`praPositionsUnwidened` as contextually appropriate).

- [ ] **Step 1: Survey**

```bash
grep -n "praDirectionsAtFunctor\|praPositionsPresheaf" \
  .session/workstreams/presheaf-pra.md \
  .session/workstreams/pra-universal-morphisms.md
```

- [ ] **Step 2: Apply minimal substitutions**

For each match:
- `praDirectionsAtFunctorOp I J P .obj X` → use the
  `(praDirectionsNatOp.app ⟨⟨Opposite.op …, Opposite.op …⟩, P⟩).toFunctor.obj X`
  form, or just refer conceptually to `praDirectionsNatOp`.
- Similar for `praDirectionsAtFunctor`.
- `praPositionsPresheaf I J P` → `praPositionsNat`-via-unwidening
  form, or `praPositionsUnwidened I J P` if the reference is inside
  the file (note: it's `private`, so this substitution only makes
  sense if the text is referring to internal implementation).

Use `Edit` with `replace_all: true` for mechanical replacements.
Do not reorganize the notes.

- [ ] **Step 3: Verify**

```bash
grep -n "praDirectionsAtFunctor\|praPositionsPresheaf" \
  .session/workstreams/presheaf-pra.md \
  .session/workstreams/pra-universal-morphisms.md
```

Expected: no matches, or only acceptable historical mentions.

- [ ] **Step 4: Commit**

```bash
git add .session/workstreams/
git commit -m "$(cat <<'EOF'
Update session notes: praDirectionsAtFunctor*,
  praPositionsPresheaf references

Replace stale references with their post-directions-promotion
replacements (praDirectionsNat*, praPositionsNat).

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
Expected: both succeed, no warnings.

- [ ] **Step 2: Placeholder scan**

Run:
```bash
grep -rn "sorry\|admit\|TODO\|TBD" GebLean/PresheafPRA.lean \
  GebLeanTests/Utilities/PresheafPRADirNat.lean \
  GebLeanTests.lean
```
Expected: no matches.

- [ ] **Step 3: Old names fully removed**

Run:
```bash
grep -rn "praDirectionsAtFunctorOp\|praDirectionsAtFunctor \
\|praPositionsPresheaf" GebLean/ GebLeanTests/
```
Expected: no matches in `GebLean/` or `GebLeanTests/`.  (`.session/`
may have residue, which is acceptable for transient notes.)

- [ ] **Step 4: Axiom check**

Temporarily append `#print axioms praDirectionsNat` and
`#print axioms praDirectionsNatOp` to
`GebLean/PresheafPRA.lean`.  Run `lake build GebLean.PresheafPRA`.
Verify each reports only `propext`, `Classical.choice`,
`Quot.sound`.  Remove the temporary lines.

- [ ] **Step 5: `variable (P …)` fully removed**

Run:
```bash
grep -n "^variable (P " GebLean/PresheafPRA.lean
```
Expected: no matches.

- [ ] **Step 6: Downstream files still build**

Run: `lake build GebLean.PresheafPRAUMorph`
Expected: success.

---

## Notes for the Executor

- **Tasks 2–6 are the heart of the plan.**  Each involves filling in
  `_` holes in `FunctorFromData` / `NatTransFromData` structures.
  The plan's spec has identified that the coherences are likely to
  close by `rfl` or short tactic blocks, following the pattern of
  the CCR utility spec and the positions spec.  If a proof resists
  after ~30 minutes, factor it into a named helper using the
  CLAUDE.md factoring-out-lemmas technique.

- **Grothendieck object constructor shape.**  The `⟨⟨Opposite.op
  (Cat.of Jᵒᵖ), Opposite.op (Cat.of Iᵒᵖ)⟩, P⟩` form may not
  elaborate verbatim at every `.app` call site.  If Lean expects a
  different shape, use `#check praDirectionsNatOp.app` to inspect
  and adjust.  If the construct is awkward and appears at multiple
  call sites, factor it into a small helper
  `private def praDirGrothObj I J P : Grothendieck … := …`.

- **Private helpers vs. exposed `sourceData`.**  Tests may need
  access to `sourceData` / `targetData` / etc.  If the `private`
  modifier prevents the tests from referencing them, either
  promote to non-private (reasonable for scaffolding exposed
  through the nat-transs), or rephrase the tests to use only the
  public surface.  The plan's default is `private`; adjust if
  tests need otherwise.

- **Task 13 may be a no-op.**  If the grep for external references
  to the deleted names returns no matches outside `PresheafPRA.lean`
  itself, Task 13 just records the scan and produces no commit.
  Note this explicitly in the report.

- **No mid-task commits.**  Each task should produce a clean
  buildable commit.  If a task cannot be completed cleanly, do not
  commit — ask for guidance.
