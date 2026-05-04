# `C`-Naturality of `ccrNewIndex` and `ccrNewFamily` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Promote `ccrNewIndexFunctor` and `ccrNewFamilyFunctor` in
`GebLean/Utilities/Families.lean` to `Cat`-valued natural
transformations. Add a supporting `ccrElementsFunctor : Cat ⥤ Cat` and
a bridge lemma to the existing per-`C` functors. Do not touch
`PresheafPRA.lean` — consumer promotion is a followup spec.

**Architecture:** Introduce two universe-widening helpers
(`typeCatLift`, `catULiftFunctor`) that bump `Cat.of (Type w)` and
`Cat.opFunctor` into `Cat.{max w v, max (w+1) u}`, matching the
output universe of `coprodCovarRepFunctor`. Assemble the per-`C`
index and family extractors into nat-transformations between functors
`Cat ⥤ Cat`. Keep the existing `ccrNewIndexFunctor` and
`ccrNewFamilyFunctor` in place; add a bridge lemma relating the new
and old forms.

**Tech Stack:** Lean 4, mathlib's
`CategoryTheory.Category.ULift` (`ULift.upFunctor`,
`ULift.downFunctor`, `ULiftHom.up`, `ULiftHom.down`,
`ULiftHomULiftCategory.equiv`), `CategoryTheory.Category.Cat`
(`Cat.of`, `Cat.opFunctor`), mathlib's
`CategoryTheory.Elements`, and the project's existing
`coprodCovarRepFunctor`, `ccrNewIndexFunctor`, `ccrNewReindex`,
`ccrNewFamilyFunctor`, `ccrNewFamily`, `ccrNewFiberMor`,
`ccrNewFiberMor_comp`.

**Reference spec:**
`docs/superpowers/specs/2026-04-17-ccr-naturality-design.md`.

**Project policy reminders:**

- No `sorry`, `admit`, `axiom`, `noncomputable`, `Classical.choice`,
  or `Quot.out`/`Quotient.out`.
- 80-character line limit.
- Build with `lake build`; test with `lake test`. Never `lake clean`
  or `lake env lean`.
- After each definition or edit, re-run `lake build` and `lake test`
  and fix problems before moving on.
- When replacing a working proof with a different one, use `_` to see
  the goal; do not use `sorry`.
- No unused `universe` or `variable` declarations.
- If stuck on a proof, try `lean4:sorry-filler-deep` or
  `superpowers:brainstorming`; never commit code that builds with
  warnings.

---

## File Structure

Three files are touched:

**Modified:** `GebLean/Utilities/Families.lean` — a new section
appended just before the closing `end GebLean` (currently line 3249).
The new section is:

```
/-! ## C-Natural Packaging of ccrNewIndex and ccrNewFamily -/

section CCRNaturalPackaging

universe u v w

-- definitions added by Tasks 1-7

end CCRNaturalPackaging
```

Added to this section, in order:

1. `typeCatLift` (universe-widened `Cat.of (Type w)`)
2. `catULiftFunctor` (universe-widening `Cat ⥤ Cat`)
3. `ccrNewIndexNatFunctor` (per-`C` widened index functor)
4. `ccrNewIndexNat` (natural transformation)
5. `ccrElementsFunctor` (Cat-valued functor of elements)
6. `ccrNewFamilyNatTarget` (widened opposite-category target)
7. `ccrNewFamilyNat` (natural transformation)
8. `ccrNewFamilyNat_app_eq_ccrNewFamilyFunctor` (bridge lemma)

**Created:** `GebLeanTests/Utilities/Families.lean` — new test file
for the new definitions.

**Modified:** `GebLeanTests.lean` — add one import line.

No changes to any other `.lean` file. No deletions.

---

## Task 1: Add universe-widening helpers

**Files:**
- Modify: `GebLean/Utilities/Families.lean` (append new section
  just before the closing `end GebLean`, currently line 3249)

- [ ] **Step 1: Locate the insertion point**

Run:
```bash
grep -n "^end GebLean" GebLean/Utilities/Families.lean
```

Expected: a single match on line ≈ 3249.

- [ ] **Step 2: Add the new section scaffold and the two
      universe-widening helpers**

Insert the following block **immediately before** the final
`end GebLean` line:

```lean
/-! ## C-Natural Packaging of ccrNewIndex and ccrNewFamily

This section packages `ccrNewIndexFunctor` and `ccrNewFamilyFunctor`
as `Cat`-valued natural transformations on `coprodCovarRepFunctor`.
The existing per-`C` functors remain in place and are not modified.
-/

section CCRNaturalPackaging

universe u v w

/--
Universe-widened form of `Cat.of (Type w)` living at
`Cat.{max w v, max (w+1) u}`.  Used as the constant target of the
natural transformation `ccrNewIndexNat`.
-/
def typeCatLift : Cat.{max w v, max (w+1) u} :=
  Cat.of
    (CategoryTheory.ULiftHom.{max w v}
      (ULift.{max (w+1) u, w+1} (Type w)))

/--
Universe-widening functor from `Cat.{v, u}` to
`Cat.{max w v, max (w+1) u}`.  At each `C`, widens `C` via
`ULift` on objects and `ULiftHom` on morphisms so that the output
universe matches `coprodCovarRepFunctor.{u, v, w}`.  Used as a
post-composition with `Cat.opFunctor` to build
`ccrNewFamilyNatTarget`.
-/
def catULiftFunctor :
    Cat.{v, u} ⥤ Cat.{max w v, max (w+1) u} where
  obj C := Cat.of
    (CategoryTheory.ULiftHom.{max w v}
      (ULift.{max (w+1) u, u} C.α))
  map {C D} F :=
    (CategoryTheory.ULiftHom.down ⋙
      CategoryTheory.ULift.downFunctor ⋙
      F.toFunctor ⋙
      CategoryTheory.ULift.upFunctor ⋙
      CategoryTheory.ULiftHom.up).toCatHom
  map_id C := by
    apply Cat.Hom.ext
    rfl
  map_comp {C D E} F G := by
    apply Cat.Hom.ext
    rfl
```

Notes for the implementer:

- If Lean reports that `rfl` fails for `map_id` or `map_comp`, use
  `_` to inspect the goal and then apply tactics from the project's
  `Utilities/Category.lean` patterns for working with `Cat.Hom.ext`
  (e.g. `simp only [Cat.Hom.comp_toFunctor,
  Functor.toCatHom_toFunctor]` followed by
  `apply CategoryTheory.Functor.ext (fun _ => rfl)`).
- The exact ULift universe annotations may need adjustment if Lean's
  universe elaborator complains. The intent is:
  `ULift.{max (w+1) u, u}` on objects so that `ULift.{r, s} C` with
  `s = u` yields `Type (max u r) = Type (max (w+1) u)`, and
  `ULiftHom.{max w v}` so that the resulting category is at
  `Category.{max w v, max (w+1) u}`.

- [ ] **Step 3: Verify section scaffold and helpers build**

Run: `lake build GebLean.Utilities.Families`
Expected: success. No warnings. No sorry. No admit.

If the build fails, use `_` in place of the failing tactic block,
read the printed goal, and adjust. Do not commit until the build is
clean.

- [ ] **Step 4: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 5: Commit**

```bash
git add GebLean/Utilities/Families.lean
git commit -m "$(cat <<'EOF'
Add universe-widening helpers typeCatLift and catULiftFunctor

These bump Cat.of (Type w) and Cat.opFunctor outputs into
Cat.{max w v, max (w+1) u} so they can serve as targets of
natural transformations on coprodCovarRepFunctor.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 2: Add `ccrNewIndexNatFunctor`

**Files:**
- Modify: `GebLean/Utilities/Families.lean` (append after
  `catULiftFunctor` in the `CCRNaturalPackaging` section)

- [ ] **Step 1: Add the definition**

Insert after `catULiftFunctor`:

```lean
/--
Per-`C` widened index functor.  Obtained by post-composing the
existing `ccrNewIndexFunctor C` with the `ULift`/`ULiftHom` lifts
that take its `Type w` target into `typeCatLift`.
-/
def ccrNewIndexNatFunctor
    (C : Type u) [Category.{v} C] :
    CoprodCovarRepCat.{u, v, w} C ⥤
      typeCatLift.{u, v, w}.α :=
  ccrNewIndexFunctor.{u, v, w} C ⋙
    CategoryTheory.ULift.upFunctor.{max (w+1) u, w+1} ⋙
    CategoryTheory.ULiftHom.up.{max w v,
      max (w+1) u}
```

- [ ] **Step 2: Build**

Run: `lake build GebLean.Utilities.Families`
Expected: success.

If the inferred types don't match `typeCatLift.α`, use `_` to reveal
the goal and adjust the universe annotations. The composition of
`ULift.upFunctor` and `ULiftHom.up` must land in the exact same
category as `typeCatLift` unfolds to.

- [ ] **Step 3: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/Families.lean
git commit -m "$(cat <<'EOF'
Add ccrNewIndexNatFunctor: widened per-C index functor

Post-composes the existing ccrNewIndexFunctor with the
ULift/ULiftHom lifts into typeCatLift.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 3: Add `ccrNewIndexNat`

**Files:**
- Modify: `GebLean/Utilities/Families.lean` (append after
  `ccrNewIndexNatFunctor`)

- [ ] **Step 1: Add the definition**

Insert after `ccrNewIndexNatFunctor`:

```lean
/--
The natural transformation packaging the per-`C` index functors.
Source: `coprodCovarRepFunctor.{u, v, w}`.  Target: the constant
functor at `typeCatLift.{u, v, w}`.

The target is constant because `coprodCovarRepFunctor.map F`
preserves the index type on the nose: `(X, E) ↦ (X, F ∘ E)` leaves
`X` unchanged, so the naturality square collapses to an identity on
index types.
-/
def ccrNewIndexNat :
    coprodCovarRepFunctor.{u, v, w} ⟶
      (Functor.const Cat.{v, u}).obj
        typeCatLift.{u, v, w} where
  app C :=
    (ccrNewIndexNatFunctor.{u, v, w} C.α).toCatHom
  naturality {C D} F := by
    apply Cat.Hom.ext
    rfl
```

Notes for the implementer:

- The naturality square should hold definitionally because
  `coprodCovarRepFunctor.map F` acts on pairs `(X, E)` as
  `(X, F ∘ E)`, preserving the first component which is what
  `ccrNewIndexFunctor` extracts. If `rfl` fails, use `_` to see the
  residual goal and apply `simp` with `ccrNewIndexFunctor`,
  `ccrNewReindex`, `coprodCovarRepFunctor`, and the definitions of
  `ULift.upFunctor` / `ULiftHom.up`.

- [ ] **Step 2: Build**

Run: `lake build GebLean.Utilities.Families`
Expected: success.

- [ ] **Step 3: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/Families.lean
git commit -m "$(cat <<'EOF'
Add ccrNewIndexNat: C-natural packaging of ccrNewIndexFunctor

The target of the natural transformation is constant because
coprodCovarRepFunctor.map preserves the index type on the nose.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 4: Add `ccrElementsFunctor`

**Files:**
- Modify: `GebLean/Utilities/Families.lean` (append after
  `ccrNewIndexNat`)

- [ ] **Step 1: Add the definition**

Insert after `ccrNewIndexNat`:

```lean
/--
Per-`C` categories of elements of `ccrNewIndexNatFunctor C`,
packaged as a single `Cat`-valued functor.  At each `C`, the value
is `(ccrNewIndexNatFunctor C).Elements`.

The morphism action on `F : C ⥤ D` sends `⟨P, i⟩` to
`⟨(coprodCovarRepFunctor.map F).obj P, i⟩`.  The index component `i`
is preserved because `coprodCovarRepFunctor.map F` acts on families
as `(X, E) ↦ (X, F ∘ E)`, leaving `X` unchanged; in particular the
`.property` component of element morphisms transports along a
definitional equality.
-/
def ccrElementsFunctor :
    Cat.{v, u} ⥤ Cat.{max w v, max (w+1) u} where
  obj C :=
    Cat.of (ccrNewIndexNatFunctor.{u, v, w} C.α).Elements
  map {C D} F :=
    { obj := fun p =>
        ⟨(coprodCovarRepFunctor.{u, v, w}.map F).obj p.1,
          p.2⟩
      map := fun {p q} f =>
        ⟨(coprodCovarRepFunctor.{u, v, w}.map F).map f.val,
          by
            have := f.property
            dsimp [ccrNewIndexNatFunctor,
              ccrNewIndexFunctor, ccrNewReindex]
            exact this⟩
      map_id := by
        intro p
        apply CategoryTheory.CategoryOfElements.ext
        dsimp
        rw [Functor.map_id]
      map_comp := by
        intros p q r f g
        apply CategoryTheory.CategoryOfElements.ext
        dsimp
        rw [Functor.map_comp] }.toCatHom
  map_id C := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext
    · intro p
      apply CategoryTheory.CategoryOfElements.ext
      dsimp
      rw [CategoryTheory.Functor.map_id]
      rfl
    · intros p q f
      apply CategoryTheory.CategoryOfElements.ext
      dsimp
      simp
  map_comp {C D E} F G := by
    apply Cat.Hom.ext
    apply CategoryTheory.Functor.ext
    · intro p
      apply CategoryTheory.CategoryOfElements.ext
      dsimp
      rw [CategoryTheory.Functor.map_comp]
      rfl
    · intros p q f
      apply CategoryTheory.CategoryOfElements.ext
      dsimp
      simp
```

Notes for the implementer:

- The `ext` lemma used is whichever is standard in this mathlib
  version; verify with `lean_local_search` for
  `CategoryOfElements.ext`. If the exact lemma name differs, use
  `Subtype.ext` on the `.val` component or use `ext` tactic.
- The `.property` proof in the `map` action may need to pattern-match
  against the structure of `f.property` after unfolding the
  naturality identity for `ccrNewIndexNat`. If `exact this` doesn't
  type-check directly, massage with `simp only [...]` using
  `ccrNewIndexFunctor`, `ccrNewReindex`, and `coprodCovarRepFunctor`
  definitions.
- If any of `map_id` / `map_comp` proofs become long, factor them
  into separate lemmas per the CLAUDE.md factoring-out-lemmas
  technique.

- [ ] **Step 2: Build**

Run: `lake build GebLean.Utilities.Families`
Expected: success.

- [ ] **Step 3: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/Families.lean
git commit -m "$(cat <<'EOF'
Add ccrElementsFunctor: Cat-valued functor of index elements

Packages per-C categories (ccrNewIndexNatFunctor C).Elements into a
single Cat-valued functor.  The morphism action uses the on-the-nose
preservation of index types by coprodCovarRepFunctor.map.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 5: Add `ccrNewFamilyNatTarget`

**Files:**
- Modify: `GebLean/Utilities/Families.lean` (append after
  `ccrElementsFunctor`)

- [ ] **Step 1: Add the definition**

Insert after `ccrElementsFunctor`:

```lean
/--
Target functor of `ccrNewFamilyNat`.  Sends each `C : Cat` to the
universe-widened opposite category.  Obtained by composing
`Cat.opFunctor` with `catULiftFunctor`.
-/
def ccrNewFamilyNatTarget :
    Cat.{v, u} ⥤ Cat.{max w v, max (w+1) u} :=
  Cat.opFunctor.{v, u} ⋙ catULiftFunctor.{v, u, w}
```

- [ ] **Step 2: Build**

Run: `lake build GebLean.Utilities.Families`
Expected: success.

- [ ] **Step 3: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/Families.lean
git commit -m "$(cat <<'EOF'
Add ccrNewFamilyNatTarget: widened-opposite Cat-valued functor

Target functor for ccrNewFamilyNat.  Composes Cat.opFunctor with
catULiftFunctor to land in Cat.{max w v, max (w+1) u}.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 6: Add `ccrNewFamilyNat`

**Files:**
- Modify: `GebLean/Utilities/Families.lean` (append after
  `ccrNewFamilyNatTarget`)

- [ ] **Step 1: Add the definition**

Insert after `ccrNewFamilyNatTarget`:

```lean
/--
The natural transformation packaging the per-`C` family extractors.
Source: `ccrElementsFunctor`.  Target: `ccrNewFamilyNatTarget`.

At each `C`, the component sends `⟨P, i_lifted⟩` to the widened
opposite of `ccrNewFamily P i`, where `i` is `i_lifted` with the
`ULift`/`ULiftHom` layers removed.  On morphisms, the action uses
`ccrNewFiberMor`.

Naturality at `F : C ⥤ D` reduces to the definitional identity
`ccrNewFamily ((coprodCovarRepFunctor.map F).obj P) i =
 F.obj (ccrNewFamily P i)`
on objects, and to `ccrNewFiberMor_comp` on morphisms.
-/
def ccrNewFamilyNat :
    ccrElementsFunctor.{u, v, w} ⟶
      ccrNewFamilyNatTarget.{u, v, w} where
  app C :=
    ({ obj := fun p =>
         CategoryTheory.ULiftHom.objUp
           (ULift.up.{max (w+1) u, u}
             (Opposite.op
               (ccrNewFamily.{u, v, w}
                 p.1 (p.2.down.down))))
       map := fun {p q} f =>
         ⟨ULift.up
           ((ccrNewFiberMor.{u, v, w}
             f.val p.1.2).op)⟩
       map_id := by
         intro p
         apply CategoryTheory.ULift.up.injEq.mpr
         _  -- fill in: use ccrNewFiberMor at identity
       map_comp := by
         intros p q r f g
         _  -- fill in: use ccrNewFiberMor_comp
     }
    : (ccrElementsFunctor.{u, v, w}.obj C).α ⥤
        (ccrNewFamilyNatTarget.{u, v, w}.obj C).α).toCatHom
  naturality {C D} F := by
    apply Cat.Hom.ext
    _  -- fill in: object + morphism parts via Functor.ext
```

Notes for the implementer:

- **The three `_` holes above are where real proofs must go.** Run
  `lake build GebLean.Utilities.Families`, read the "unsolved goals"
  error for each hole, and write the tactic block. Per CLAUDE.md
  rule 7, `_` is the canonical hole marker; `sorry` must never
  appear in any file in this project.
- The `map_id` proof reduces to showing that `ccrNewFiberMor (𝟙 P) i
  = 𝟙 _`, which follows from the definition of `ccrNewFiberMor` and
  the identity case of the underlying morphism structure. Look up
  the existing `ccrNewFiberMor` definition at
  `GebLean/Utilities/Families.lean:473` and unfold.
- The `map_comp` proof uses the existing `@[simp]` lemma
  `ccrNewFiberMor_comp` at line ≈ 481.
- The outer `naturality` proof has two parts: object-equality and
  morphism-equality. The object part is definitional
  (`ccrNewFamily ((coprodCovarRepFunctor.map F).obj P) i =
  F.obj (ccrNewFamily P i)` holds by unfolding
  `coprodCovarRepFunctor.map`). The morphism part follows from the
  interaction of `ccrNewFiberMor` with `coprodCovarRepFunctor.map F`,
  which may require a small new lemma
  `ccrNewFiberMor_coprodCovarRepFunctor_map` that the implementer
  adds locally. If so, place it **before** `ccrNewFamilyNat` in the
  same section.
- The exact structure of the `ULift.up` / `ULiftHom.objUp` wrapping
  may need adjustment to match `ccrNewFamilyNatTarget.obj C` once
  unfolded. Use `_` and `#check` to verify.
- If the proofs get long, factor them out into named lemmas before
  `ccrNewFamilyNat`, following the factoring-out-lemmas technique
  from CLAUDE.md.

- [ ] **Step 2: Inspect the three goals**

Run `lake build GebLean.Utilities.Families`. The build reports
"unsolved goals" for each of the three `_` holes. Read each goal.

- [ ] **Step 3: Write the three proofs**

For each site, replace `_` with a proof. Commit style:

- `map_id`: use `ccrNewFiberMor` unfolding plus `simp` with
  `Opposite.op_id`, `ULift.up_injEq` etc.
- `map_comp`: use `ccrNewFiberMor_comp` and `Opposite.op_comp`.
- Outer `naturality`: `apply CategoryTheory.Functor.ext`, handle
  `obj` and `map` cases. Both should reduce to on-the-nose
  equalities after unfolding.

If a proof does not close with standard tactics, factor it into a
helper lemma before `ccrNewFamilyNat` in this same section, write
the helper using the same `_`-inspection technique, and invoke it
here.

- [ ] **Step 4: Build with no sorry**

Run: `lake build GebLean.Utilities.Families`
Expected: success, no warnings, no `sorry`. Verify with:
```bash
grep -n "sorry\|admit" GebLean/Utilities/Families.lean
```
Expected: no matches (or only inside string literals / comments, but
there shouldn't be any in this section).

- [ ] **Step 5: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 6: Axiom check**

Run:
```bash
grep -n "^def ccrNewFamilyNat " GebLean/Utilities/Families.lean
```
and then add a temporary `#print axioms ccrNewFamilyNat` line at the
end of the file. Run `lake build GebLean.Utilities.Families` and
verify the output lists only standard axioms (`propext`,
`Classical.choice`, `Quot.sound`). Remove the temporary line and
rebuild.

- [ ] **Step 7: Commit**

```bash
git add GebLean/Utilities/Families.lean
git commit -m "$(cat <<'EOF'
Add ccrNewFamilyNat: C-natural packaging of ccrNewFamilyFunctor

Naturality follows from the on-the-nose action of
coprodCovarRepFunctor.map on families plus ccrNewFiberMor_comp for
morphisms.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 7: Add the bridge lemma

**Files:**
- Modify: `GebLean/Utilities/Families.lean` (append after
  `ccrNewFamilyNat`)

- [ ] **Step 1: Add the lemma**

Insert after `ccrNewFamilyNat`, and close the section:

```lean
/--
Bridge lemma: `ccrNewFamilyNat.app C` agrees with
`ccrNewFamilyFunctor C`, modulo the ULift / ULiftHom unwrap at the
source element and wrap at the target opposite category.

Not marked `@[simp]` to avoid unfolding cycles; intended to be
invoked manually by downstream users who want to reach through the
widening.
-/
theorem ccrNewFamilyNat_app_eq_ccrNewFamilyFunctor
    (C : Type u) [Category.{v} C] :
    ccrNewFamilyNat.{u, v, w}.app (Cat.of C) =
      /- the composite: unwrap ULift/ULiftHom on the element index,
         apply ccrNewFamilyFunctor C, wrap in catULiftFunctor -/
      ((fun p =>
          CategoryTheory.ULiftHom.up.{max w v,
            max (w+1) u}.obj
            (CategoryTheory.ULift.upFunctor.{max (w+1) u, u}.obj
              ((ccrNewFamilyFunctor.{u, v, w} C).obj
                ⟨p.1, p.2.down.down⟩))) ∷ _ := by
  -- Definitional collapse; expected to close by rfl, or by
  -- apply Cat.Hom.ext / Functor.ext followed by rfl on cases.
  _

end CCRNaturalPackaging
```

Notes for the implementer:

- The exact target of the equality is tricky to write as a syntactic
  equation because it mixes `Cat.Hom` packaging with the element
  structure. If the statement as written above does not type-check,
  rephrase it using `=` on the underlying `Functor`:

```lean
theorem ccrNewFamilyNat_app_eq_ccrNewFamilyFunctor
    (C : Type u) [Category.{v} C] :
    (ccrNewFamilyNat.{u, v, w}.app (Cat.of C)).toFunctor =
      /- right-hand side written as an explicit Functor -/ := by
  _
```

- If `rfl` does not close the goal, use `apply
  CategoryTheory.Functor.ext` and handle `obj` and `map` cases
  separately; both should be `rfl` (or very close to it) because the
  bridge is a definitional unfolding.
- Read the unsolved-goals error for the `_` hole, then write the
  proof.

- [ ] **Step 2: Inspect the goal**

Run `lake build GebLean.Utilities.Families` and read the unsolved
goal at the `_` hole. Write the proof.

- [ ] **Step 3: Verify no `sorry` remains in source files**

```bash
grep -n "sorry\|admit" GebLean/Utilities/Families.lean
```
Expected: no matches.

- [ ] **Step 4: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 5: Commit**

```bash
git add GebLean/Utilities/Families.lean
git commit -m "$(cat <<'EOF'
Add bridge lemma ccrNewFamilyNat_app_eq_ccrNewFamilyFunctor

Documents that each per-C component of ccrNewFamilyNat collapses to
the existing ccrNewFamilyFunctor up to ULift/ULiftHom wrap/unwrap.
Not marked @[simp] to avoid unfolding cycles.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 8: Create `GebLeanTests/Utilities/Families.lean` with
##          type-sanity tests

**Files:**
- Create: `GebLeanTests/Utilities/Families.lean`

- [ ] **Step 1: Verify the test directory exists**

Run:
```bash
ls GebLeanTests/Utilities/
```
Expected: `Tower.lean` present.

- [ ] **Step 2: Create the test file**

Create `GebLeanTests/Utilities/Families.lean` with:

```lean
import GebLean.Utilities.Families

/-!
# Tests for C-Natural Packaging of ccrNewIndex and ccrNewFamily

Type-signature sanity checks and small-example tests for the
`CCRNaturalPackaging` section of `GebLean.Utilities.Families`.
-/

open GebLean CategoryTheory

/-! ## Type-signature sanity -/

-- ccrNewIndexNat has the expected shape
example : coprodCovarRepFunctor.{0, 0, 0} ⟶
    (Functor.const Cat.{0, 0}).obj typeCatLift.{0, 0, 0} :=
  ccrNewIndexNat.{0, 0, 0}

-- ccrElementsFunctor has the expected shape
example : Cat.{0, 0} ⥤ Cat.{0, 1} :=
  ccrElementsFunctor.{0, 0, 0}

-- ccrNewFamilyNat has the expected shape
example :
    ccrElementsFunctor.{0, 0, 0} ⟶
      ccrNewFamilyNatTarget.{0, 0, 0} :=
  ccrNewFamilyNat.{0, 0, 0}
```

- [ ] **Step 3: Build (expect failure — not yet registered)**

Run: `lake build GebLeanTests.Utilities.Families`
Expected: success. (The file builds standalone even before it is
registered in `GebLeanTests.lean`.)

- [ ] **Step 4: Commit**

```bash
git add GebLeanTests/Utilities/Families.lean
git commit -m "$(cat <<'EOF'
Add type-signature sanity tests for CCRNaturalPackaging

New test file exercises the type signatures of ccrNewIndexNat,
ccrElementsFunctor, and ccrNewFamilyNat at universe level 0.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 9: Register the new test file in `GebLeanTests.lean`

**Files:**
- Modify: `GebLeanTests.lean`

- [ ] **Step 1: Add the import**

Edit `GebLeanTests.lean` and add the line
`import GebLeanTests.Utilities.Families` after the existing
`import GebLeanTests.Utilities.Tower` line (currently line 20).

- [ ] **Step 2: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests.lean
git commit -m "$(cat <<'EOF'
Register GebLeanTests.Utilities.Families test file

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 10: Add definitional-collapse tests

**Files:**
- Modify: `GebLeanTests/Utilities/Families.lean` (append)

- [ ] **Step 1: Add the tests**

Append to `GebLeanTests/Utilities/Families.lean`:

```lean
/-! ## Definitional collapse to existing utilities -/

section CollapseTests

-- The concrete small base category for these tests.
private def baseCat : Cat.{0, 0} := Cat.of PUnit

-- ccrNewIndexNat.app at baseCat equals ccrNewIndexNatFunctor
example :
    (ccrNewIndexNat.{0, 0, 0}.app baseCat).toFunctor =
    ccrNewIndexNatFunctor.{0, 0, 0} baseCat.α := by
  rfl

-- ccrNewFamilyNat.app unfolds via the bridge lemma
example :
    (ccrNewFamilyNat.{0, 0, 0}.app baseCat).toFunctor =
      /- rhs as in the bridge lemma -/ _ := by
  /- use ccrNewFamilyNat_app_eq_ccrNewFamilyFunctor -/
  _

end CollapseTests
```

Notes for the implementer:

- Fill in the `_` on the equation's RHS by copying the expression
  from the bridge lemma statement in Task 7. Fill in the `_` in the
  `by` block by applying the bridge lemma.
- If `rfl` on the first `example` does not work because of
  bundling/unbundling of `Cat.Hom`, use `apply Cat.Hom.ext` followed
  by `rfl`.
- The `.app` expects whatever parameter shape `ccrNewIndexNat` /
  `ccrNewFamilyNat` takes at each component — typically a
  `Cat.{v, u}ᵒᵖ` or `Cat.{v, u}` object; adjust `baseCat` to the
  expected shape (e.g. `Opposite.op baseCat`) if Lean reports a
  type mismatch.

- [ ] **Step 2: Verify no `sorry` remains in the source**

```bash
grep -n "sorry\|admit" GebLeanTests/Utilities/Families.lean
```
Expected: no matches.

- [ ] **Step 3: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 4: Commit**

```bash
git add GebLeanTests/Utilities/Families.lean
git commit -m "$(cat <<'EOF'
Add collapse tests for ccrNewIndexNat and ccrNewFamilyNat

Verify that each nat-trans's component on a concrete small base
category agrees with the existing per-C functor (via the bridge
lemma for the family case).

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 11: Add naturality and functoriality tests

**Files:**
- Modify: `GebLeanTests/Utilities/Families.lean` (append)

- [ ] **Step 1: Add the tests**

Append to `GebLeanTests/Utilities/Families.lean`:

```lean
/-! ## Naturality and functoriality, small examples -/

section NatAndFunctoriality

-- A concrete functor between small base categories.
private def baseFunctor : Cat.of PUnit ⟶ Cat.of PUnit :=
  (CategoryTheory.Functor.id _).toCatHom

-- Naturality of ccrNewIndexNat at baseFunctor holds by rfl
-- because coprodCovarRepFunctor.map preserves the index type.
example :
    (coprodCovarRepFunctor.{0, 0, 0}.map baseFunctor).toFunctor ⋙
      (ccrNewIndexNat.{0, 0, 0}.app _).toFunctor =
    (ccrNewIndexNat.{0, 0, 0}.app _).toFunctor := by
  rfl

-- Functoriality of ccrElementsFunctor: map_id is rfl-style
example :
    ccrElementsFunctor.{0, 0, 0}.map (𝟙 (Cat.of PUnit)) =
      𝟙 (ccrElementsFunctor.{0, 0, 0}.obj (Cat.of PUnit)) := by
  rw [CategoryTheory.Functor.map_id]

-- Functoriality of ccrElementsFunctor: map_comp
example :
    ccrElementsFunctor.{0, 0, 0}.map
      (baseFunctor ≫ baseFunctor) =
    ccrElementsFunctor.{0, 0, 0}.map baseFunctor ≫
      ccrElementsFunctor.{0, 0, 0}.map baseFunctor := by
  rw [CategoryTheory.Functor.map_comp]

end NatAndFunctoriality
```

- [ ] **Step 2: Full build and test**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/Families.lean
git commit -m "$(cat <<'EOF'
Add naturality and functoriality tests for CCRNaturalPackaging

Exercises ccrNewIndexNat.naturality and ccrElementsFunctor map_id /
map_comp on a concrete small base category.

Co-Authored-By: Claude Opus 4.7 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 12: Add a universe-polymorphism test

**Files:**
- Modify: `GebLeanTests/Utilities/Families.lean` (append)

- [ ] **Step 1: Add the test**

Append to `GebLeanTests/Utilities/Families.lean`:

```lean
/-! ## Universe polymorphism -/

section UniversePoly

-- Exercise ccrNewIndexNat at u := 1, v := 0, w := 0
example : coprodCovarRepFunctor.{1, 0, 0} ⟶
    (Functor.const Cat.{0, 1}).obj typeCatLift.{1, 0, 0} :=
  ccrNewIndexNat.{1, 0, 0}

-- Exercise ccrNewFamilyNat at u := 1, v := 0, w := 0
example :
    ccrElementsFunctor.{1, 0, 0} ⟶
      ccrNewFamilyNatTarget.{1, 0, 0} :=
  ccrNewFamilyNat.{1, 0, 0}

end UniversePoly
```

- [ ] **Step 2: Full build and test**

Run: `lake build && lake test`
Expected: both succeed. If universes don't align at `u := 1, v := 0,
w := 0`, adjust the explicit `Cat.{?, ?}` annotations to match what
the definitions produce.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/Families.lean
git commit -m "$(cat <<'EOF'
Add universe-polymorphism test for CCRNaturalPackaging

Exercises the new definitions at u := 1, v := 0, w := 0 to catch
accidental universe specialization.

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

- [ ] **Step 2: Search for any remaining placeholders**

Run:
```bash
grep -n "sorry\|admit\|TODO\|TBD" GebLean/Utilities/Families.lean \
  GebLeanTests/Utilities/Families.lean GebLeanTests.lean
```
Expected: no matches.

- [ ] **Step 3: Check unused variables**

Run: `lake build` and confirm no `unused variable` warnings in the
added code.

- [ ] **Step 4: Axiom check on the top-level new definitions**

Temporarily append to `GebLean/Utilities/Families.lean`:
```lean
#print axioms GebLean.ccrNewIndexNat
#print axioms GebLean.ccrElementsFunctor
#print axioms GebLean.ccrNewFamilyNat
```
Run `lake build GebLean.Utilities.Families`, verify each reports
only `propext`, `Classical.choice`, `Quot.sound` (or a subset).
Remove the temporary lines and rebuild.

- [ ] **Step 5: Confirm downstream files still build unchanged**

Run:
```bash
lake build GebLean.PresheafPRA
```
Expected: success. No code in `PresheafPRA.lean` was modified by
this plan, and the new definitions are purely additive.

---

## Notes for the Executor

- **Proof tactics.** The proofs in Tasks 4 and 6 are the non-trivial
  parts of this plan. Expect to factor them into helper lemmas if
  they run long. Use the CLAUDE.md factoring-out-lemmas technique.
- **If `rfl` does not close a goal** that the plan claims it should,
  use `_` in place of the proof body and read the printed goal. The
  most common cause will be a mismatch in the ULift layering —
  adjust the universe annotations on `ULift.upFunctor` /
  `ULiftHom.up` / similar until the types line up.
- **Universe annotations.** The plan writes explicit
  `{u, v, w}` annotations on most new definitions and on their uses
  in tests. If Lean complains about universe unification, try
  omitting the annotation (letting elaborator infer) first; if that
  doesn't work, add explicit annotations matching what the error
  message reports.
- **No mid-task commits.** Each task is designed to produce a clean
  buildable commit. If you cannot produce a clean build within a
  task, do not commit — ask the user for guidance or invoke
  `superpowers:brainstorming` to reconsider the approach.
