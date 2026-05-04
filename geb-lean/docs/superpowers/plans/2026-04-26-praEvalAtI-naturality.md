# `praEvalAt*` Naturality in `(J, P, Z)` at Fixed `I` Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Lift `praEvalAtFunctor I J : PRACat I J ⥤
(PSh(I) ⥤ PSh(J))` to a flat-functor-between-Grothendiecks form
natural in `(J, P, Z)` at fixed `I`, built as a single
`(grothendieckContraFunctor Cat).map` of a natural transformation
between two `Catᵒᵖ ⥤ Cat` functors.

**Architecture:** Introduce `praEvalAtBifunctor` (uncurried form) as
a public artifact, then construct a `Catᵒᵖ ⥤ Cat`-functor source
fibre and a NatTrans to the existing `praEvalTargetFibre`.  Apply
`grothendieckContraFunctor.map` to lift the NatTrans to a flat
functor between contraGrothendieck Cats.  All cross-fibre / coherence
proofs are vacuous since `praEvalAt`'s J-pullback is strict.

**Tech Stack:** Lean 4, mathlib (category theory, Grothendieck
construction, presheaf categories).  Project rules from `CLAUDE.md`
apply throughout (no `sorry`/`admit`/`axiom`/`noncomputable`/
`classical`, lines ≤80, no forbidden style words, `lake build` +
`lake test` clean with zero warnings before each commit).

**Spec:**
`docs/superpowers/specs/2026-04-26-praEvalAtI-naturality-design.md`

---

## File Structure

| File | Tasks touched |
| ---- | ------------- |
| `GebLean/PresheafPRA.lean` | 0, 1–8 |
| `GebLeanTests/Utilities/PresheafPRAEvalAtINat.lean` | 9 (create), 11–15 |
| `GebLeanTests.lean` | 10 (register) |
| `.session/workstreams/presheaf-pra.md` | 16 |

Per-task summary:

- Task 0 (pre-work): revert in-flight source-side definitions
  (`evalSourceData`, `praPolyEvalSource`, `praPolyEvalData_baseFib`,
  `praPolyEvalData_fibFib`).
- Task 1: `praEvalAtBifunctor` (new public artifact).
- Tasks 2–3: source side (`praPolyEvalAtISourceFib`,
  `praPolyEvalAtISource`).
- Tasks 4–5: NatTrans + final flat functor.
- Task 6: three rfl bridge lemmas.
- Task 7: source-object helper.
- Task 8: bridge theorem.
- Tasks 9–15: tests.
- Task 16: workstream notes update.

---

## Task 0: Revert in-flight source-side definitions

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — remove `evalSourceData`,
  `praPolyEvalSource`, `praPolyEvalData_baseFib`,
  `praPolyEvalData_fibFib`.

**Context:** The previous (I, J)-natural attempt's source side hit a
variance mismatch (see spec).  These four definitions are no longer
used by anything in-tree; reverting them clears space for the
fixed-`I` redesign.  The target side
(`praEvalTargetFibre`, `praPolyEvalTarget`) and the
`FunctorBetweenContraContra` framework are kept.

- [ ] **Step 1: Identify removal range**

The four definitions to remove span lines ~408–508 of
`GebLean/PresheafPRA.lean` (after the existing `praEvalTargetFibre`
and `praPolyEvalTarget`):

```lean
def evalSourceData : ... := ...
def praPolyEvalSource : ... := ...
private def praPolyEvalData_baseFib : ... := ...
private def praPolyEvalData_fibFib (X : ...) : ... := ...
```

Read `GebLean/PresheafPRA.lean` lines 400–510 to confirm exact bounds
before deleting.

- [ ] **Step 2: Delete the four definitions**

Delete the entire blocks corresponding to:

- `def evalSourceData` (~lines 401–434)
- `def praPolyEvalSource` (~lines 436–456)
- `private def praPolyEvalData_baseFib` (~lines 458–472)
- `private def praPolyEvalData_fibFib` (~lines 474–508)

(Use `Edit` with the actual contents from the file.)

After deletion, the `praPolyDirectionsTarget` definition that
previously appeared at line ~518 should immediately follow
`praPolyEvalTarget`.

- [ ] **Step 3: Build and verify**

Run: `lake build`
Expected: completes without errors or warnings.

- [ ] **Step 4: Run tests**

Run: `lake test`
Expected: all tests pass.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: revert (I, J)-natural source side"
```

(No `Co-Authored-By` trailer.)

---

## Task 1: Add `praEvalAtBifunctor`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — add inside
  `section PresheafPRAEvalAt`, after `praEvalAtFunctor`.

**Context:** The uncurried bifunctor `PRACat I J × PSh(I) ⥤ PSh(J)`.
Will be used as the per-J ingredient in `praPolyEvalAtINatTrans`.
This is a new public artifact parallel to `praEvalAtProfunctor` and
`praEvalAtFunctor`.

- [ ] **Step 1: Locate insertion point**

Read `GebLean/PresheafPRA.lean` near `def praEvalAtFunctor` (was at
line ~1489 before Task 0; line numbers may shift after the revert).
The new definition goes immediately after `praEvalAtFunctor`'s
definition and before `praEvalAtProfunctorFullyFaithful`.

- [ ] **Step 2: Insert with `_` placeholder body**

```lean
/--
The evaluation bifunctor: uncurried form of `praEvalAtFunctor`.
Sends a pair `(P, Z)` of a PRA and an `I`-presheaf to the result
presheaf on `J`.
-/
def praEvalAtBifunctor :
    PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J ×
        ↑(presheafCat.{u_I, v_I, w_I} I) ⥤
      ((Cat.of Jᵒᵖ).α ⥤ Type (max w' u_I w_I)) :=
  _
```

Build to surface the expected type.  Run:
`mcp__lean-lsp__lean_goal` at the `_` to see what's expected.

- [ ] **Step 3: Replace `_` with the body**

The body is `Functor.uncurry.obj (praEvalAtFunctor I J)`.  Refine the
universe annotations on `Functor.uncurry` as needed.

```lean
def praEvalAtBifunctor :
    PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J ×
        ↑(presheafCat.{u_I, v_I, w_I} I) ⥤
      ((Cat.of Jᵒᵖ).α ⥤ Type (max w' u_I w_I)) :=
  Functor.uncurry.obj (praEvalAtFunctor.{u_I, v_I, u_J, v_J,
    w_I, w'} I J)
```

- [ ] **Step 4: Build**

Run: `lake build`
Expected: completes without errors or warnings.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praEvalAtBifunctor"
```

(No `Co-Authored-By` trailer.)

---

## Task 2: Add `praPolyEvalAtISourceFib`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — add to a new
  `section PresheafPRAEvalAtINat` placed adjacent to / after
  `section PresheafPRAEvalAt`.

**Context:** The source-side `Catᵒᵖ ⥤ Cat` functor sending `op J` to
the widened product Cat `PRACat I J × PSh(I)`.  As J varies
contravariantly, the PRACat factor pulls back via f_J and the PSh(I)
factor stays constant.

- [ ] **Step 1: Open the new section**

Insert just before `section PresheafPRAEvalAt` ends (or in a new
section adjacent), e.g.:

```lean
section PresheafPRAEvalAtINat

attribute [local instance] CategoryTheory.uliftCategory

variable (I : Cat.{v_I, u_I})
```

(The `local instance` and `variable I` are needed because the source
fibre uses `catULiftFunctor2` widening and references I throughout.)

- [ ] **Step 2: Insert with `_` placeholder body**

```lean
/--
Source-side `Catᵒᵖ ⥤ Cat` functor for `praPolyEvalAtIFunctor` at
fixed `I`.  Sends `op J` to the widened product Cat `PRACat I J ×
PSh(I)`.  The PRACat factor varies contravariantly with J via
`presheafPRACatBifunctor.flip.obj (op (Cat.of Iᵒᵖ))`; the PSh(I)
factor is constant in J.
-/
def praPolyEvalAtISourceFib :
    Cat.{v_J, u_J}ᵒᵖ ⥤
      Cat.{...} :=
  _
```

Use the universe placeholders `Cat.{...}`; build to surface the
expected universes.

- [ ] **Step 3: Construct the body**

Two factors and a product, all widened.  Reference values and
their universes:

- PRACat factor: `presheafPRACatBifunctor.{u_I, v_I, u_J, v_J, w_I,
  w'}.flip.obj (Opposite.op (Cat.of (presheafCatFunctor.{u_I, v_I,
  w_I}.obj (Opposite.op I)))) : Cat.{v_J, u_J}ᵒᵖ ⥤ Cat.{...}`.
  This needs care; `presheafPRACatBifunctor.obj (op
  (Cat.of Jᵒᵖ))` is the form used, and we want J on the OUTER
  variable.  The exact way to extract "fix I, vary J" needs
  inspection.  Likely: `(presheafPRACatBifunctor.flip).obj (op
  (Cat.of Iᵒᵖ))` if we use the same `Cat.of Iᵒᵖ` convention as
  `presheafPRACatFunctor` (line ~120 of PresheafPRA.lean).
- Constant PSh(I) factor: `(Functor.const (Cat.{v_J, u_J})ᵒᵖ).obj
  (presheafCatFunctor.{u_I, v_I, w_I}.obj (Opposite.op I))`.
- Product: combine via `Functor.prod'` or hand-rolled product.
  Both factors are widened to a common Cat universe via
  `catULiftFunctor2`.

Implementation suggestion (Functor.prod' approach):

```lean
def praPolyEvalAtISourceFib :
    Cat.{v_J, u_J}ᵒᵖ ⥤
      Cat.{...} :=
  let praFactor : Cat.{v_J, u_J}ᵒᵖ ⥤ Cat.{...} :=
    (presheafPRACatBifunctor.{u_I, v_I, u_J, v_J, w_I, w'}.flip).obj
      (Opposite.op (Cat.of Iᵒᵖ))
  let pshFactor : Cat.{v_J, u_J}ᵒᵖ ⥤ Cat.{...} :=
    (Functor.const _).obj
      (presheafCatFunctor.{u_I, v_I, w_I}.obj (Opposite.op I))
  -- after universe-aligning both factors via catULiftFunctor2:
  ((Functor.prod' praFactor pshFactor) ⋙ <prod-of-Cats functor>) ⋙
    catULiftFunctor2.{...}
```

If `Functor.prod' + prod-of-Cats functor` doesn't compose cleanly,
fall back to hand-rolled construction:

```lean
def praPolyEvalAtISourceFib :
    Cat.{v_J, u_J}ᵒᵖ ⥤ Cat.{...} where
  obj opJ :=
    Cat.of (widened
      (↑(presheafPRACatBifunctor.{u_I, v_I, u_J, v_J, w_I, w'}.obj
        opJ).obj (Opposite.op (Cat.of Iᵒᵖ))) ×
      ↑(presheafCatFunctor.{u_I, v_I, w_I}.obj (Opposite.op I)))
  map f := <pullback morphism>
  map_id _ := by ...
  map_comp _ _ := by ...
```

The exact form is LSP-discovered.  Take whichever path compiles
first; if the Functor.prod' path works, prefer it for brevity.

- [ ] **Step 4: Build and iterate**

Run: `lake build`
Expected: completes without errors or warnings.  If errors arise,
inspect goals via `mcp__lean-lsp__lean_goal` and fill in universe
annotations or restructure.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalAtISourceFib"
```

(No `Co-Authored-By` trailer.)

---

## Task 3: Add `praPolyEvalAtISource`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyEvalAtISourceFib`.

**Context:** The source contraGrothendieck.  Objects: `(J, (P, Z))`
with `J : Cat`, `P : PRACat I J`, `Z : PSh(I)`.

- [ ] **Step 1: Insert the definition**

```lean
/--
Total source contraGrothendieck for `praPolyEvalAtIFunctor`.

Objects are pairs `(J, (P, Z))` with `J : Cat`,
`P : PresheafPRACat I J`, and `Z : PSh(I)` (all widened).

Morphisms `((J_s, P_s, Z_s)) ⟶ ((J_t, P_t, Z_t))` are triples
`(f_J : J_s ⟶ J_t, f_P : P_s ⟶ f_J^* P_t, η : Z_s ⟶ Z_t)`.
-/
def praPolyEvalAtISource :
    Cat.{...} :=
  (grothendieckContraFunctor Cat.{v_J, u_J}).obj
    (praPolyEvalAtISourceFib.{u_I, v_I, u_J, v_J, w_I, w'} I)
```

The output Cat universe should match `praPolyEvalTarget`'s for the
final functor `praPolyEvalAtIFunctor` to typecheck — universe-pad as
needed.

- [ ] **Step 2: Build**

Run: `lake build`
Expected: completes without errors or warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalAtISource"
```

(No `Co-Authored-By` trailer.)

---

## Task 4: Add `praPolyEvalAtINatTrans`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyEvalAtISource`.

**Context:** The natural transformation `praPolyEvalAtISourceFib I
⟹ praEvalTargetFibre`.  Per-J component is `praEvalAtBifunctor I J`
widened.  Naturality is the strict identity that J-pullback commutes
with bifunctor evaluation.

- [ ] **Step 1: Insert with `_` placeholder app and naturality**

```lean
/--
The J-naturality natural transformation underlying
`praPolyEvalAtIFunctor`.  Per-`op J` component is
`praEvalAtBifunctor I J` lifted through `catULiftFunctor2` to
match the source/target Cat-universe alignment.
-/
def praPolyEvalAtINatTrans :
    praPolyEvalAtISourceFib.{u_I, v_I, u_J, v_J, w_I, w'} I ⟶
      praEvalTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'} where
  app opJ := _
  naturality {opJ_s opJ_t} f := _
```

- [ ] **Step 2: Build to surface the expected `app` type**

Run: `lake build`
Expected: errors at the `_` for `app` showing the expected
Cat-morphism type.  Inspect via `mcp__lean-lsp__lean_goal`.

- [ ] **Step 3: Fill in `app`**

The component is the bifunctor widened.  Assuming
`praPolyEvalAtISourceFib` body uses `catULiftFunctor2` widening and
`praEvalTargetFibre` does too, the app is `catULiftFunctor2.map
(praEvalAtBifunctor.{...} I opJ.unop).toCatHom` or similar.

Body:

```lean
  app opJ :=
    (catULiftFunctor2.{...}).map
      (Cat.Hom.ofFunctor
        (praEvalAtBifunctor.{u_I, v_I, u_J, v_J, w_I, w'} I
          opJ.unop))
```

If the exact `Cat.Hom`-vs-functor coercion mismatches, inspect the
expected type via LSP and adjust.

- [ ] **Step 4: Fill in `naturality`**

The naturality square is the strict identity that J-pullback
commutes with `praEvalAtBifunctor`.  Aim for `rfl`:

```lean
  naturality {opJ_s opJ_t} f := by
    apply Cat.Hom.ext
    rfl
```

If `rfl` fails, fall back to a short `simp only` with
`praEvalAtBifunctor` and `Functor.uncurry` unfolds.

- [ ] **Step 5: Build**

Run: `lake build`
Expected: completes without errors or warnings.

- [ ] **Step 6: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalAtINatTrans"
```

(No `Co-Authored-By` trailer.)

---

## Task 5: Add `praPolyEvalAtIFunctor`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyEvalAtINatTrans`.

**Context:** The final flat functor between contraGrothendiecks,
constructed via `(grothendieckContraFunctor Cat).map` of the
NatTrans.

- [ ] **Step 1: Insert the definition**

```lean
/--
Flat functor `praPolyEvalAtISource I ⥤ praPolyEvalTarget` natural
in `(J, P, Z)` at fixed `I`.  Sends `(J, (P, Z))` to
`(J, praEvalAtBifunctor I J |>.obj (P, Z))` (widened).

Constructed by lifting `praPolyEvalAtINatTrans I` to a flat functor
between contraGrothendiecks via `(grothendieckContraFunctor
Cat).map`.
-/
def praPolyEvalAtIFunctor :
    praPolyEvalAtISource.{u_I, v_I, u_J, v_J, w_I, w'} I ⥤
      praPolyEvalTarget.{u_I, v_I, u_J, v_J, w_I, w'} :=
  ((grothendieckContraFunctor Cat.{v_J, u_J}).map
    (praPolyEvalAtINatTrans.{u_I, v_I, u_J, v_J, w_I, w'} I)
  ).toFunctor
```

- [ ] **Step 2: Build**

Run: `lake build`
Expected: completes without errors or warnings.  If a
universe-misalignment error appears between the source and target
Cats, pad the source's universe annotation in
`praPolyEvalAtISource` (Task 3) and `praPolyEvalAtISourceFib`
(Task 2).

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalAtIFunctor"
```

(No `Co-Authored-By` trailer.)

---

## Task 6: Add three rfl bridge lemmas

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyEvalAtIFunctor`.

**Context:** Three bridge lemmas decomposing
`praPolyEvalAtIFunctor`'s action into its base, fibre, and
morphism-fibre components.  Mirror praDirections's bridge lemmas
(commit `821da820`).

- [ ] **Step 1: Insert `_base` lemma**

```lean
/--
Base of `praPolyEvalAtIFunctor.obj X` agrees with the base of `X`
on the nose: the functor is identity on the J-base.
-/
@[simp] theorem praPolyEvalAtIFunctor_base
    (X : praPolyEvalAtISource.{u_I, v_I, u_J, v_J, w_I, w'} I) :
    GrothendieckContraFunctor.objBase
      ((praPolyEvalAtIFunctor.{u_I, v_I, u_J, v_J, w_I, w'} I).obj
        X) =
    GrothendieckContraFunctor.objBase X :=
  rfl
```

- [ ] **Step 2: Build**

Run: `lake build`
Expected: completes without errors or warnings.

- [ ] **Step 3: Insert `_fibre` lemma**

```lean
/--
Fibre of `praPolyEvalAtIFunctor.obj X` is the
`praPolyEvalAtINatTrans` component applied at the base of `X`,
acting on the fibre of `X`.
-/
@[simp] theorem praPolyEvalAtIFunctor_fibre
    (X : praPolyEvalAtISource.{u_I, v_I, u_J, v_J, w_I, w'} I) :
    GrothendieckContraFunctor.objFiber
      ((praPolyEvalAtIFunctor.{u_I, v_I, u_J, v_J, w_I, w'} I).obj
        X) =
    (praPolyEvalAtINatTrans.{u_I, v_I, u_J, v_J, w_I, w'} I).app
      (Opposite.op (GrothendieckContraFunctor.objBase X)) |>.obj
      (GrothendieckContraFunctor.objFiber X) :=
  rfl
```

- [ ] **Step 4: Build**

Run: `lake build`
Expected: completes without errors or warnings.

- [ ] **Step 5: Insert `_map_homFiber` lemma**

```lean
/--
Fibre component of `praPolyEvalAtIFunctor.map f` equals the
NatTrans's component applied to the source fibre's hom.

Exact RHS shape is determined by `grothendieckContraFunctor.map`'s
morphism action; aim for `rfl` after `simp only` if needed.
-/
@[simp] theorem praPolyEvalAtIFunctor_map_homFiber
    {X Y : praPolyEvalAtISource.{u_I, v_I, u_J, v_J, w_I, w'} I}
    (f : X ⟶ Y) :
    GrothendieckContraFunctor.homFiber
      ((praPolyEvalAtIFunctor.{u_I, v_I, u_J, v_J, w_I, w'} I).map
        f) =
    _ :=
  _
```

Use `_` to surface the RHS shape via LSP.  Then fill in:

```lean
    -- LSP-discovered RHS, likely involves NatTrans.naturality
    -- and the source's homFiber.
    <RHS>
```

Aim for `rfl`.  Fallback: short `simp only` with
`praPolyEvalAtINatTrans`, `praPolyEvalAtIFunctor`,
`grothendieckContraFunctor` unfolds.

- [ ] **Step 6: Build**

Run: `lake build`
Expected: completes without errors or warnings.

- [ ] **Step 7: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalAtIFunctor bridge lemmas"
```

(No `Co-Authored-By` trailer.)

---

## Task 7: Add `praPolyEvalAtISourceObj` helper

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after the bridge
  lemmas.

**Context:** Public helper that constructs a source object from
`(J, P, Z)`.  Mirrors `praPolyDirectionsAtSourceObj` (commit
`ed74a7ff`).

- [ ] **Step 1: Insert with `_` placeholder body**

```lean
/--
Construct a source-object of `praPolyEvalAtISource` from a J Cat,
a PRA `P : PresheafPRACat I J`, and a presheaf `Z : PSh(I)`.

The widening uses `ULiftHom.objUp ∘ ULift.up` to embed `(P, Z)`
into the widened product Cat at `praPolyEvalAtISourceFib I |>.obj
(op (Cat.of Jᵒᵖ))`.
-/
def praPolyEvalAtISourceObj
    (J : Cat.{v_J, u_J})
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
    (Z : ↑(presheafCat.{u_I, v_I, w_I} I)) :
    praPolyEvalAtISource.{u_I, v_I, u_J, v_J, w_I, w'} I :=
  _
```

- [ ] **Step 2: Build to surface expected universes**

Run: `lake build`
Expected: error at `_` showing the expected source-object type.
Inspect via `mcp__lean-lsp__lean_goal`.

- [ ] **Step 3: Fill in body using `mkObj` and widening**

```lean
def praPolyEvalAtISourceObj
    (J : Cat.{v_J, u_J})
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
    (Z : ↑(presheafCat.{u_I, v_I, w_I} I)) :
    praPolyEvalAtISource.{u_I, v_I, u_J, v_J, w_I, w'} I :=
  GrothendieckContraFunctor.mkObj (Cat.of Jᵒᵖ)
    (CategoryTheory.ULiftHom.objUp.{...}
      (CategoryTheory.ULift.up.{...} (P, Z)))
```

Exact universe annotations on `ULiftHom.objUp` and `ULift.up` are
LSP-discovered.  Mirror `praPolyDirectionsAtSourceObj`'s pattern.

- [ ] **Step 4: Build**

Run: `lake build`
Expected: completes without errors or warnings.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalAtISourceObj helper"
```

(No `Co-Authored-By` trailer.)

---

## Task 8: Add `praEvalAtFunctor_via_praPolyEvalAtIFunctor` bridge theorem

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyEvalAtISourceObj`.

**Context:** Bridge theorem stating that the per-component
`praEvalAtFunctor` agrees with the natural form via the source-
object helper.  Mirror praDirections's analog at commit `b9daaca3`.

- [ ] **Step 1: Insert with `_` placeholder body**

```lean
/--
The per-component `praEvalAtFunctor.obj P |>.obj Z` agrees with the
fibre of `praPolyEvalAtIFunctor.obj (praPolyEvalAtISourceObj J P Z)`
after unwidening.

This is the bridge theorem connecting the existing per-component
evaluation to its `(J, P, Z)`-natural form at fixed `I`.
-/
@[simp] theorem praEvalAtFunctor_via_praPolyEvalAtIFunctor
    (J : Cat.{v_J, u_J})
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
    (Z : ↑(presheafCat.{u_I, v_I, w_I} I)) :
    (praEvalAtFunctor.{u_I, v_I, u_J, v_J, w_I, w'} I J).obj P
      |>.obj Z =
    _ :=
  _
```

- [ ] **Step 2: Build to surface expected RHS**

Run: `lake build`
Expected: error at the equation's RHS `_` showing the expected
type.  Inspect via `mcp__lean-lsp__lean_goal`.

- [ ] **Step 3: Fill in RHS via unwiden chain**

The RHS is the unwidening of `praPolyEvalAtIFunctor.obj (...).fiber
.unop`.  Following the praDirections pattern:

```lean
    CategoryTheory.ULift.down.{...}
      (CategoryTheory.ULiftHom.objDown.{...}
        ((praPolyEvalAtIFunctor.{u_I, v_I, u_J, v_J, w_I, w'} I).obj
          (praPolyEvalAtISourceObj.{u_I, v_I, u_J, v_J, w_I, w'} I
            J P Z)
        ).fiber.unop)
```

(Exact chain depends on the widening structure built in Tasks 2–3.)

- [ ] **Step 4: Attempt `rfl` proof**

```lean
  := by rfl
```

Or as a term: just `:= rfl` after the `=`.

- [ ] **Step 5: Build**

Run: `lake build`
Expected: completes without errors or warnings.  If `rfl` fails,
fall back to:

```lean
  := by
    simp only [praPolyEvalAtIFunctor_fibre,
      praPolyEvalAtIFunctor_base,
      praPolyEvalAtINatTrans, praPolyEvalAtISourceObj,
      praEvalAtBifunctor, ...]
```

If that also fails, escalate to the user before continuing.

- [ ] **Step 6: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praEvalAtFunctor_via_praPolyEvalAtIFunctor"
```

(No `Co-Authored-By` trailer.)

---

## Task 9: Create test file with type-signature sanity tests

**Files:**

- Create: `GebLeanTests/Utilities/PresheafPRAEvalAtINat.lean`.

**Context:** Mirror the structure of
`GebLeanTests/Utilities/PresheafPRADirNat.lean` with five test
sections plus a bridge-theorem test.

- [ ] **Step 1: Create the file with header and Section 1
  (type-signature sanity)**

```lean
import GebLean

namespace GebLean

open CategoryTheory

universe u_I v_I u_J v_J w_I w'

/-! ## Section 1: Type-signature sanity -/

section TypeSanity

example : Type :=
  praEvalAtBifunctor.{0, 0, 0, 0, 0, 0}
    (Cat.of PUnit) (Cat.of PUnit)
  |>.obj ⟨_, _⟩ |>.obj _ |>.obj _

example :
    praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0} (Cat.of PUnit) =
    praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0} (Cat.of PUnit) := rfl

example :
    praPolyEvalAtISource.{0, 0, 0, 0, 0, 0} (Cat.of PUnit) =
    praPolyEvalAtISource.{0, 0, 0, 0, 0, 0} (Cat.of PUnit) := rfl

example :
    praPolyEvalAtISourceFib.{0, 0, 0, 0, 0, 0} (Cat.of PUnit) =
    praPolyEvalAtISourceFib.{0, 0, 0, 0, 0, 0} (Cat.of PUnit) := rfl

example :
    praEvalTargetFibre.{0, 0, 0, 0, 0, 0} =
    praEvalTargetFibre.{0, 0, 0, 0, 0, 0} := rfl

example :
    praPolyEvalTarget.{0, 0, 0, 0, 0, 0} =
    praPolyEvalTarget.{0, 0, 0, 0, 0, 0} := rfl

end TypeSanity

end GebLean
```

(Adjust the first `example`'s shape — it should test that the
bifunctor's signature is well-formed.  Use the same patterns from
`PresheafPRADirNat.lean`'s opening section as a template.)

- [ ] **Step 2: Build**

Run: `lake build`
Expected: completes without errors or warnings.  (Until Task 10,
this file is not registered, so `lake test` won't run it yet.)

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRAEvalAtINat.lean
git commit -m "tests: create PresheafPRAEvalAtINat with type-sanity"
```

(No `Co-Authored-By` trailer.)

---

## Task 10: Register test file in `GebLeanTests.lean`

**Files:**

- Modify: `GebLeanTests.lean` — add an `import` for the new test
  file.

- [ ] **Step 1: Locate the existing test imports**

Read `GebLeanTests.lean`; find the `import GebLeanTests.Utilities.
PresheafPRADirNat` line (or similar registration of recent test
files).

- [ ] **Step 2: Add the new import**

Add `import GebLeanTests.Utilities.PresheafPRAEvalAtINat`
alphabetically after the `PresheafPRADirNat` import.

- [ ] **Step 3: Build and run tests**

Run: `lake build && lake test`
Expected: all tests pass, no warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLeanTests.lean
git commit -m "tests: register PresheafPRAEvalAtINat"
```

(No `Co-Authored-By` trailer.)

---

## Task 11: Add bridge-lemma collapse tests

**Files:**

- Modify: `GebLeanTests/Utilities/PresheafPRAEvalAtINat.lean` —
  append Section 2.

**Context:** Verify the three rfl bridges hold at concrete inputs.
Mirror `PresheafPRADirNat.lean`'s bridge-collapse section.

- [ ] **Step 1: Append Section 2**

```lean
/-! ## Section 2: Bridge-lemma collapse -/

section BridgeCollapse

example
    (X : praPolyEvalAtISource.{0, 0, 0, 0, 0, 0} (Cat.of PUnit)) :
    GrothendieckContraFunctor.objBase
      ((praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0} (Cat.of PUnit)).obj
        X) =
    GrothendieckContraFunctor.objBase X := by
  exact praPolyEvalAtIFunctor_base.{0, 0, 0, 0, 0, 0}
    (Cat.of PUnit) X

example
    (X : praPolyEvalAtISource.{0, 0, 0, 0, 0, 0} (Cat.of PUnit)) :
    GrothendieckContraFunctor.objFiber
      ((praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0} (Cat.of PUnit)).obj
        X) =
    (praPolyEvalAtINatTrans.{0, 0, 0, 0, 0, 0}
      (Cat.of PUnit)).app
      (Opposite.op (GrothendieckContraFunctor.objBase X)) |>.obj
      (GrothendieckContraFunctor.objFiber X) := by
  exact praPolyEvalAtIFunctor_fibre.{0, 0, 0, 0, 0, 0}
    (Cat.of PUnit) X

end BridgeCollapse
```

(The `_map_homFiber` test depends on the exact RHS chosen in Task 6
and is added similarly.)

- [ ] **Step 2: Build and test**

Run: `lake build && lake test`
Expected: all tests pass, no warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRAEvalAtINat.lean
git commit -m "tests: PresheafPRAEvalAtINat bridge-lemma collapse"
```

(No `Co-Authored-By` trailer.)

---

## Task 12: Add pointwise-accessor compatibility tests

**Files:**

- Modify: `GebLeanTests/Utilities/PresheafPRAEvalAtINat.lean` —
  append Section 3.

**Context:** Verify `praEvalAtFunctor`, `praEvalAt`,
`praEvalAt_index`, `praEvalAt_mor`, `praEvalAt_mk` still produce
expected shapes (no breakage from `praEvalAtBifunctor` addition).

- [ ] **Step 1: Append Section 3**

```lean
/-! ## Section 3: Pointwise-accessor compatibility -/

section AccessorCompat

example :
    praEvalAtFunctor.{0, 0, 0, 0, 0, 0}
      (Cat.of PUnit) (Cat.of PUnit) =
    praEvalAtFunctor.{0, 0, 0, 0, 0, 0}
      (Cat.of PUnit) (Cat.of PUnit) := rfl

-- Plus per-accessor compatibility tests covering praEvalAt,
-- praEvalAt_index, praEvalAt_mor, praEvalAt_mk at concrete inputs.

end AccessorCompat
```

(Fill in concrete-input tests following
`PresheafPRADirNat.lean`'s analogous section as a template.)

- [ ] **Step 2: Build and test**

Run: `lake build && lake test`
Expected: all tests pass.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRAEvalAtINat.lean
git commit -m "tests: PresheafPRAEvalAtINat accessor compatibility"
```

(No `Co-Authored-By` trailer.)

---

## Task 13: Add functoriality tests

**Files:**

- Modify: `GebLeanTests/Utilities/PresheafPRAEvalAtINat.lean` —
  append Section 4.

**Context:** Verify `(praPolyEvalAtIFunctor I).map_id` and
`.map_comp` at concrete morphisms.

- [ ] **Step 1: Append Section 4**

```lean
/-! ## Section 4: Functoriality -/

section Functoriality

example
    (X : praPolyEvalAtISource.{0, 0, 0, 0, 0, 0} (Cat.of PUnit)) :
    (praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0}
      (Cat.of PUnit)).map (𝟙 X) = 𝟙 _ :=
  Functor.map_id _ X

example
    {X Y Z : praPolyEvalAtISource.{0, 0, 0, 0, 0, 0}
      (Cat.of PUnit)}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    (praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0}
      (Cat.of PUnit)).map (f ≫ g) =
    (praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0}
      (Cat.of PUnit)).map f ≫
      (praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0}
        (Cat.of PUnit)).map g :=
  Functor.map_comp _ f g

end Functoriality
```

- [ ] **Step 2: Build and test**

Run: `lake build && lake test`
Expected: all tests pass.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRAEvalAtINat.lean
git commit -m "tests: PresheafPRAEvalAtINat functoriality"
```

(No `Co-Authored-By` trailer.)

---

## Task 14: Add universe-polymorphism tests

**Files:**

- Modify: `GebLeanTests/Utilities/PresheafPRAEvalAtINat.lean` —
  append Section 5.

**Context:** Verify the construction works at mixed universes such
as `{1, 0, 0, 0, 0, 0}` and `{0, 0, 1, 0, 0, 0}`.  Mirror
`PresheafPRADirNat.lean`'s analogous section.

- [ ] **Step 1: Append Section 5**

```lean
/-! ## Section 5: Universe polymorphism -/

section UniversePolymorphism

example :
    praPolyEvalAtIFunctor.{1, 0, 0, 0, 0, 0} (Cat.of PUnit) =
    praPolyEvalAtIFunctor.{1, 0, 0, 0, 0, 0} (Cat.of PUnit) := rfl

example :
    praPolyEvalAtIFunctor.{0, 0, 1, 0, 0, 0} (Cat.of PUnit) =
    praPolyEvalAtIFunctor.{0, 0, 1, 0, 0, 0} (Cat.of PUnit) := rfl

example :
    praPolyEvalAtIFunctor.{0, 1, 0, 1, 0, 0} (Cat.of PUnit) =
    praPolyEvalAtIFunctor.{0, 1, 0, 1, 0, 0} (Cat.of PUnit) := rfl

end UniversePolymorphism
```

- [ ] **Step 2: Build and test**

Run: `lake build && lake test`
Expected: all tests pass.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRAEvalAtINat.lean
git commit -m "tests: PresheafPRAEvalAtINat universe polymorphism"
```

(No `Co-Authored-By` trailer.)

---

## Task 15: Add bridge-theorem test

**Files:**

- Modify: `GebLeanTests/Utilities/PresheafPRAEvalAtINat.lean` —
  append a final test exercising
  `praEvalAtFunctor_via_praPolyEvalAtIFunctor`.

- [ ] **Step 1: Append the bridge-theorem test**

```lean
/-! ## Bridge-theorem test -/

section BridgeTheorem

example
    (P : PresheafPRACat.{0, 0, 0, 0, 0, 0}
      (Cat.of PUnit) (Cat.of PUnit))
    (Z : ↑(presheafCat.{0, 0, 0} (Cat.of PUnit))) :
    (praEvalAtFunctor.{0, 0, 0, 0, 0, 0}
      (Cat.of PUnit) (Cat.of PUnit)).obj P |>.obj Z =
    _ -- LSP-discovered RHS matching the bridge theorem
  := by
  exact praEvalAtFunctor_via_praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0}
    (Cat.of PUnit) (Cat.of PUnit) P Z

end BridgeTheorem
```

(The `_` for the RHS is filled in via LSP after Task 8 commits.
The `exact` then closes by the simp lemma.)

- [ ] **Step 2: Build and test**

Run: `lake build && lake test`
Expected: all tests pass.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRAEvalAtINat.lean
git commit -m "tests: PresheafPRAEvalAtINat bridge theorem"
```

(No `Co-Authored-By` trailer.)

---

## Task 16: Update `.session/workstreams/presheaf-pra.md`

**Files:**

- Modify: `.session/workstreams/presheaf-pra.md` — add a
  "praEvalAtI Naturality" subsection to the Phase 2.5 area.

**Context:** Document the completed fixed-`I` workstream and the
pending follow-up `(I, J)`-naturality brainstorm/design.

- [ ] **Step 1: Read existing structure**

Read `.session/workstreams/presheaf-pra.md` to find the existing
"praEval Naturality" section (added during the in-flight attempt).
Replace its body to reflect the new fixed-`I` direction and clear
out the now-obsolete in-flight task list.

- [ ] **Step 2: Write the new section**

Replace the existing "praEval Naturality" section with:

```markdown
## praEvalAtI Naturality (complete, 2026-04-26)

Goal: lift `praEvalAtFunctor I J` to a flat-functor-between-
Grothendiecks form `praPolyEvalAtIFunctor` natural in `(J, P, Z)`
at fixed `I`.

The previous (I, J)-natural attempt (commits `81a0369f` through
`d701b401`) hit a variance mismatch in the cross-fibre map (see
`docs/superpowers/specs/2026-04-26-praEvalAtI-naturality-design.md`
"Background and motivation" for the analysis).  Resolution: scope
down to fixed `I` for now; the (I, J)-naturality is genuinely lax
and will be designed in a separate workstream after this fixed-`I`
construction provides a concrete reference formula.

### Done

| Commit | Task |
|--------|------|
| `<commit>` | Task 0: revert in-flight source-side definitions |
| `<commit>` | Task 1: `praEvalAtBifunctor` |
| `<commit>` | Task 2: `praPolyEvalAtISourceFib` |
| `<commit>` | Task 3: `praPolyEvalAtISource` |
| `<commit>` | Task 4: `praPolyEvalAtINatTrans` |
| `<commit>` | Task 5: `praPolyEvalAtIFunctor` |
| `<commit>` | Task 6: bridge lemmas |
| `<commit>` | Task 7: `praPolyEvalAtISourceObj` helper |
| `<commit>` | Task 8: bridge theorem |
| `<commit>` | Tasks 9–15: PresheafPRAEvalAtINat tests |
| `<commit>` | Task 16: workstream notes update |

### Follow-up (separate workstream)

Brainstorm and design the `(I, J)`-natural form, using the
fixed-`I` formula as a guide.  Possibilities include paranatural
transformations between two-variance-in-`I` functors, lax-natural
infrastructure, or restricted source-mor conventions.

### Kept from in-flight attempt

The following commits remain useful and are kept on-branch:

- `81a0369f`, `f9859d89`, `d789a2ac` — target side
  (`praEvalTargetFibre`, `praPolyEvalTarget`).  Parametrised only
  by J; reusable as-is in the fixed-`I` construction.
- `64162066`, `774ee96e`, `d9d08504` — `FunctorBetweenContraContra`
  framework in `Utilities/Grothendieck.lean`.  General-purpose
  infrastructure parallel to `FunctorBetweenCovContra`; useful
  regardless.
```

(Fill in the `<commit>` placeholders with actual commit hashes after
each task is committed during execution.)

- [ ] **Step 3: Commit**

```bash
git add .session/workstreams/presheaf-pra.md
git commit -m "session: praEvalAtI workstream notes"
```

(No `Co-Authored-By` trailer.)

---

## Final Validation

After all tasks complete:

- [ ] **Run full build + tests**

```bash
lake build && lake test
```

Expected: completes without errors or warnings.

- [ ] **Verify no `sorry`/`admit`/`axiom`/`noncomputable`/`classical`
  introduced**

```bash
grep -n 'sorry\|admit\|^axiom\|noncomputable\|classical' \
  GebLean/PresheafPRA.lean \
  GebLeanTests/Utilities/PresheafPRAEvalAtINat.lean
```

Expected: no occurrences from this work.

- [ ] **Verify no forbidden style words in modified source**

```bash
grep -nE \
  'fundamental|actually|\bkey\b|insight|core|advanced' \
  GebLean/PresheafPRA.lean \
  GebLeanTests/Utilities/PresheafPRAEvalAtINat.lean
grep -nE \
  'complex|complicated|simple|advantage|benefit|important|challenge' \
  GebLean/PresheafPRA.lean \
  GebLeanTests/Utilities/PresheafPRAEvalAtINat.lean
```

Expected: no occurrences from this work.

- [ ] **Verify line lengths**

```bash
awk 'length > 80' GebLean/PresheafPRA.lean | head -5
awk 'length > 80' GebLeanTests/Utilities/PresheafPRAEvalAtINat.lean
```

Expected: no output from either.

- [ ] **Spot-check the docstring of `praPolyEvalAtIFunctor`**

Confirms the public-API documentation reads correctly and
references the existing `praEvalAtFunctor` for the per-component
correspondence.

---

## Execution Notes

- **Universe annotations** are LSP-discovered throughout.  Mirror the
  patterns in `praPolyEvalTarget` (already committed) and
  `praPolyDirectionsTarget`.
- **`Functor.prod'` vs hand-rolled product** in Task 2: try
  `Functor.prod'` first; fall back to hand-rolled if universe
  alignment becomes painful.
- **`rfl` fallbacks**: every `rfl` proof in this plan has a
  documented `simp only` fallback.  If the fallback also fails,
  escalate to the user before continuing — the failure may indicate
  a design mismatch similar to the variance mismatch that triggered
  this redesign.
- **No `Co-Authored-By` trailer** on any commit, per project
  convention.
- **Commit scope tags**: `presheaf-pra:` for source changes,
  `tests:` for test files, `session:` for workstream notes.
- **Cleanup**: this plan does not include cleanup of the now-stale
  `2026-04-26-praEval-naturality-design.md` spec file.  Both specs
  remain in `docs/superpowers/specs/` (gitignored).  The new spec
  supersedes the old; future readers should refer to the
  fixed-`I` design.

---

## Future Work (out of scope)

After this plan is fully executed:

- Brainstorm/design session for `(I, J)`-naturality, using the
  concrete formula from `praPolyEvalAtIFunctor` as a reference.
- Possible directions: paranatural transformation between two-
  variance-in-`I` functors, 2-cell between pseudofunctors,
  profunctor-style natural transformation capturing lax
  `I`-naturality, or source-mor restriction to f_I fully faithful
  / equivalence.

These will be planned and executed as separate workstreams.
