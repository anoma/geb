# `praEvalAt*` (I, J)-Naturality (Lax in `I`) Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build `praPolyEvalLaxNatTrans`, a lax natural transformation
bundle representing the type of the unapplied `praEval` operator,
realizing `(I, J, P, Z)`-naturality with strict `J/P/Z`-naturality and
lax (forward-whisker) `I`-naturality.

**Architecture:** Two phases.  Phase A adds new `LaxNatTransContraData`
infrastructure to `Utilities/Grothendieck.lean`, mirroring the existing
`OplaxNatTransContraData` but in the lax comparison direction over
`Cᵒᵖ ⥤ Cat` and without a `.toFunctor` extractor (the lift to a strict
functor between contraGrothendiecks does not exist in this direction).
Phase B adds the praEval-specific construction in `PresheafPRA.lean`:
outer-base source/target bifunctors `Catᵒᵖ ⥤ Cat`, the lax nat trans
bundle whose per-`I` component is the existing `praPolyEvalAtIFunctor I`,
and bridges to the fixed-`I` and per-component forms.  Phase C adds
tests; Phase D updates workstream notes.

**Tech Stack:** Lean 4 + mathlib4.  Existing infrastructure:
`grothendieckContraFunctor`, `presheafPRACatBifunctorUncurriedOp`,
`presheafCatFunctor`, `praPolyEvalAtISource I`, `praPolyEvalAtIFunctor I`,
`praPolyEvalTarget`, `OplaxNatTransContraData`, `LaxNatTransData`
(covariant case).

**Spec:**
[`docs/superpowers/specs/2026-04-27-praEval-IJ-naturality-design.md`](../specs/2026-04-27-praEval-IJ-naturality-design.md).

**Branch:** `terence/grothendieck` (current).  All commits use
`presheaf-pra:` for source, `tests:` for tests, and `session:` for
workstream notes.  No `Co-Authored-By` trailers.  ONE commit per task.

---

## Phase A: New `LaxNatTransContraData` infrastructure

Mirrors the existing `OplaxNatTransContraData` section in
`GebLean/Utilities/Grothendieck.lean` (lines 6673–7010) but for
`G F : Cᵒᵖ ⥤ Cat` (unprimed) with the **lax** comparison direction
(`(F.map f.op).(app c').x ⟶ (app c).(G.map f.op).x`).  Does not
include a `.toFunctor` extractor (impossible in this direction).

### Task 1: Add `LaxNatTransContraApp`, `LaxNatTransContraLaxApp`, `LaxNatTransContraLaxNat` abbrevs

**Files:**
- Modify: `GebLean/Utilities/Grothendieck.lean` (add new section
  immediately after the `OplaxFunctorCat` section, around line 7160)

- [ ] **Step 1: Add the section header and the three field abbrevs**

```lean
/-!
## Lax Natural Transformations Between Contravariant Cat-Valued Functors
   (with `grothendieckContraFunctor` convention)

This section defines lax natural transformations between Cat-valued
functors `G F : Cᵒᵖ ⥤ Cat` (unprimed opposite, matching
`grothendieckContraFunctor`).

A lax natural transformation `α : G ⟹ F` between contra-functors
consists of:

- Component functors `α.app c : G.obj (op c) ⥤ F.obj (op c)` for each
  `c : C`.
- Laxity morphisms `α.laxApp f x : (F.map f.op).obj ((α.app c').obj x)
  ⟶ (α.app c).obj ((G.map f.op).obj x)` for each `f : c ⟶ c'` in `C`
  and `x : G.obj (op c')`.
- Naturality and coherence conditions.

Direction note: the lax comparison goes from
"evaluate-then-pullback" to "pullback-then-evaluate", opposite of the
oplax direction in the parallel `OplaxNatTransContraData` section.

Unlike the covariant `LaxNatTransData` and the primed oplax
`OplaxNatTransData`, this section does NOT provide a `.toFunctor`
extractor: the lift to a strict functor between contraGrothendiecks
in the lax direction does not exist (it would require a section of
the lax comparison map, which is not available in general).
-/

section LaxNatTransContraFunctor

universe vC uC vF uF

variable {C : Type uC} [Category.{vC} C]
variable (G F : Cᵒᵖ ⥤ Cat.{vF, uF})

/-- Component functors for a lax natural transformation between
contravariant Cat-valued functors. -/
abbrev LaxNatTransContraApp :=
  ∀ c : C, G.obj (Opposite.op c) ⥤ F.obj (Opposite.op c)

variable {G F}
variable (app : LaxNatTransContraApp G F)

/-- Laxity morphism for `α : G ⟹ F` between contra-functors.  For
`f : c ⟶ c'` in `C` and `x : G.obj (op c')`, a morphism

  `(F.map f.op).obj ((app c').obj x) ⟶ (app c).obj ((G.map f.op).obj x)`

encoding the comparison from "evaluate-then-pullback" to
"pullback-then-evaluate". -/
abbrev LaxNatTransContraLaxApp :=
  ∀ {c c' : C} (f : c ⟶ c') (x : G.obj (Opposite.op c')),
    (F.map f.op).toFunctor.obj ((app c').obj x) ⟶
    (app c).obj ((G.map f.op).toFunctor.obj x)

variable (laxApp : LaxNatTransContraLaxApp app)

/-- Naturality of laxity morphisms: for each `f : c ⟶ c'` and
`φ : x ⟶ y`, the appropriate square commutes. -/
abbrev LaxNatTransContraLaxNat :=
  ∀ {c c' : C} (f : c ⟶ c') {x y : G.obj (Opposite.op c')} (φ : x ⟶ y),
    (F.map f.op).toFunctor.map ((app c').map φ) ≫ laxApp f y =
    laxApp f x ≫ (app c).map ((G.map f.op).toFunctor.map φ)

end LaxNatTransContraFunctor
```

- [ ] **Step 2: Run `lake build`**

Run: `lake build`
Expected: build succeeds with no errors and no warnings.

- [ ] **Step 3: Run `lake test`**

Run: `lake test`
Expected: tests pass.

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "feat(utilities): add LaxNatTransContra{App,LaxApp,LaxNat} abbrevs"
```

---

### Task 2: Add `LaxNatTransContraIdEq` + proof + `LaxNatTransContraLaxId`

**Files:**
- Modify: `GebLean/Utilities/Grothendieck.lean`
  (extend the `LaxNatTransContraFunctor` section)

- [ ] **Step 1: Add the identity-equation abbrev, its proof, and the laxId abbrev**

Insert before `end LaxNatTransContraFunctor`:

```lean
/-- Equality proof for identity laxity. -/
abbrev LaxNatTransContraIdEq :=
  ∀ (c : C) (x : G.obj (Opposite.op c)),
    (F.map (𝟙 c).op).toFunctor.obj ((app c).obj x) =
    (app c).obj ((G.map (𝟙 c).op).toFunctor.obj x)

/-- Derive the identity equality from functor laws. -/
lemma laxNatTransContraIdEqProof : LaxNatTransContraIdEq app := by
  intro c x
  have hF : (F.map (𝟙 c).op).toFunctor = 𝟭 _ := by
    rw [show (𝟙 c).op = 𝟙 (Opposite.op c) from rfl, F.map_id]
    exact Cat.id_eq_id (F.obj (Opposite.op c))
  have hG : (G.map (𝟙 c).op).toFunctor = 𝟭 _ := by
    rw [show (𝟙 c).op = 𝟙 (Opposite.op c) from rfl, G.map_id]
    exact Cat.id_eq_id (G.obj (Opposite.op c))
  simp only [hF, hG, Functor.id_obj]

/-- Identity coherence: `laxApp (𝟙 c) x` equals the canonical
`eqToHom`. -/
abbrev LaxNatTransContraLaxId :=
  ∀ (c : C) (x : G.obj (Opposite.op c)),
    laxApp (𝟙 c) x = eqToHom (laxNatTransContraIdEqProof app c x)
```

- [ ] **Step 2: Run `lake build` and fix errors**

Run: `lake build`
Expected: build succeeds.  If `Cat.id_eq_id` doesn't apply, mirror the
`oplaxNatTransIdEqProof` proof shape (lines 6753–6759) using
`congrArg Cat.Hom.toFunctor (F.map_id _)` plus `.trans (Cat.id_eq_id _)`.

- [ ] **Step 3: Run `lake test`**

Run: `lake test`
Expected: tests pass.

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "feat(utilities): add LaxNatTransContraIdEq + proof + LaxId abbrev"
```

---

### Task 3: Add `LaxNatTransContraCompEq*` + proofs + `LaxNatTransContraLaxComp`

**Files:**
- Modify: `GebLean/Utilities/Grothendieck.lean`
  (extend the `LaxNatTransContraFunctor` section)

- [ ] **Step 1: Add the composition-equation abbrevs, their proofs, and the laxComp abbrev**

Insert before `end LaxNatTransContraFunctor`:

```lean
/-- Equality proof for composition laxity (left side).  For `f : c ⟶ c'`
and `g : c' ⟶ c''` in `C`, the C-composition is `f ≫ g : c ⟶ c''`,
and `(f ≫ g).op = g.op ≫ f.op` in `Cᵒᵖ`.  By contravariant
functoriality: `F.map (f ≫ g).op = F.map f.op ⋙ F.map g.op`. -/
abbrev LaxNatTransContraCompEq :=
  ∀ {c c' c'' : C} (f : c ⟶ c') (g : c' ⟶ c'')
    (x : G.obj (Opposite.op c'')),
    (F.map (f ≫ g).op).toFunctor.obj ((app c'').obj x) =
    (F.map f.op).toFunctor.obj
      ((F.map g.op).toFunctor.obj ((app c'').obj x))

/-- Derive the left composition equality from functor laws. -/
lemma laxNatTransContraCompEqProof : LaxNatTransContraCompEq app := by
  intro c c' c'' f g x
  have h := congrArg Cat.Hom.toFunctor (F.map_comp g.op f.op)
  exact congrFun (congrArg Functor.obj h) ((app c'').obj x)

/-- Equality proof for composition laxity (right side). -/
abbrev LaxNatTransContraCompEqRight :=
  ∀ {c c' c'' : C} (f : c ⟶ c') (g : c' ⟶ c'')
    (x : G.obj (Opposite.op c'')),
    (app c).obj ((G.map f.op).toFunctor.obj
      ((G.map g.op).toFunctor.obj x)) =
    (app c).obj ((G.map (f ≫ g).op).toFunctor.obj x)

/-- Derive the right composition equality from functor laws. -/
lemma laxNatTransContraCompEqRightProof :
    LaxNatTransContraCompEqRight app := by
  intro c c' c'' f g x
  have h := congrArg Cat.Hom.toFunctor (G.map_comp g.op f.op)
  exact congrArg (app c).obj
    (congrFun (congrArg Functor.obj h.symm) x)

/-- Composition coherence: `laxApp (f ≫ g) x` decomposes stepwise. -/
abbrev LaxNatTransContraLaxComp :=
  ∀ {c c' c'' : C} (f : c ⟶ c') (g : c' ⟶ c'')
    (x : G.obj (Opposite.op c'')),
    laxApp (f ≫ g) x =
    eqToHom (laxNatTransContraCompEqProof app f g x) ≫
    (F.map f.op).toFunctor.map (laxApp g x) ≫
    laxApp f ((G.map g.op).toFunctor.obj x) ≫
    eqToHom (laxNatTransContraCompEqRightProof app f g x)
```

- [ ] **Step 2: Run `lake build` and fix errors**

Run: `lake build`
Expected: build succeeds.  If `F.map_comp g.op f.op` direction-mismatches,
swap argument order — `(f ≫ g).op = g.op ≫ f.op` may need an explicit
`Quiver.Hom.unop_inj`-style rewrite.

- [ ] **Step 3: Run `lake test`**

Run: `lake test`
Expected: tests pass.

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "feat(utilities): add LaxNatTransContraCompEq* + proofs + LaxComp abbrev"
```

---

### Task 4: Add `LaxNatTransContraData` structure

**Files:**
- Modify: `GebLean/Utilities/Grothendieck.lean`
  (extend the `LaxNatTransContraFunctor` section)

- [ ] **Step 1: Add the bundled structure**

Insert before `end LaxNatTransContraFunctor`:

```lean
/-- Bundled data for a lax natural transformation `G ⟹ F` between
contravariant Cat-valued functors `G F : Cᵒᵖ ⥤ Cat`. -/
structure LaxNatTransContraData (G F : Cᵒᵖ ⥤ Cat.{vF, uF}) where
  /-- Component functors. -/
  app : LaxNatTransContraApp G F
  /-- Laxity morphisms. -/
  laxApp : LaxNatTransContraLaxApp app
  /-- Naturality of laxity morphisms. -/
  laxNat : LaxNatTransContraLaxNat app laxApp
  /-- Identity coherence. -/
  laxId : LaxNatTransContraLaxId app laxApp
  /-- Composition coherence. -/
  laxComp : LaxNatTransContraLaxComp app laxApp
```

- [ ] **Step 2: Run `lake build`**

Run: `lake build`
Expected: build succeeds.

- [ ] **Step 3: Run `lake test`**

Run: `lake test`
Expected: tests pass.

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "feat(utilities): add LaxNatTransContraData bundle structure"
```

---

### Task 5: Add `LaxNatTransContraData.id`

**Files:**
- Modify: `GebLean/Utilities/Grothendieck.lean`
  (extend the `LaxNatTransContraFunctor` section)

- [ ] **Step 1: Add the identity lax nat trans**

Insert before `end LaxNatTransContraFunctor`:

```lean
/-- Identity lax natural transformation. -/
def LaxNatTransContraData.id (G : Cᵒᵖ ⥤ Cat.{vF, uF}) :
    LaxNatTransContraData G G where
  app c := 𝟭 (G.obj (Opposite.op c))
  laxApp f x := eqToHom (by simp only [Functor.id_obj])
  laxNat f φ := by
    simp only [Functor.id_map, eqToHom_naturality]
  laxId c x := rfl
  laxComp f g x := by
    simp only [CategoryTheory.Functor.map_id, Category.id_comp,
      eqToHom_trans, eqToHom_refl]
```

- [ ] **Step 2: Run `lake build` and fix errors**

Run: `lake build`
Expected: build succeeds.  If `eqToHom_naturality` or `eqToHom_trans` apply
differently, mirror `OplaxNatTransData.id` proof shape (lines 6845–6853).

- [ ] **Step 3: Run `lake test`**

Run: `lake test`
Expected: tests pass.

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "feat(utilities): add LaxNatTransContraData.id"
```

---

### Task 6: Add `LaxNatTransContraData.comp`

**Files:**
- Modify: `GebLean/Utilities/Grothendieck.lean`
  (extend the `LaxNatTransContraFunctor` section)

- [ ] **Step 1: Add the composition of lax nat transes**

Insert before `end LaxNatTransContraFunctor`:

```lean
/-- Composition of lax natural transformations.

Given `α : G ⟹ H` and `β : H ⟹ K`, their composition `α.comp β : G ⟹ K`
has:
- Component functors: `(α.comp β).app c = α.app c ⋙ β.app c`.
- Laxity: for `f : c ⟶ c'` and `x : G.obj (op c')`,
  `(F.map f.op).map (β.laxApp f ((α.app c').obj x))` followed by
  `β.laxApp f`-style and `α.laxApp f`-style steps.
-/
def LaxNatTransContraData.comp {G H K : Cᵒᵖ ⥤ Cat.{vF, uF}}
    (α : LaxNatTransContraData G H) (β : LaxNatTransContraData H K) :
    LaxNatTransContraData G K where
  app c := α.app c ⋙ β.app c
  laxApp {c c'} f x :=
    β.laxApp f ((α.app c').obj x) ≫ (β.app c).map (α.laxApp f x)
  laxNat {c c'} f {x y} φ := by
    simp only [Functor.comp_obj, Functor.comp_map, Category.assoc]
    have hα : (H.map f.op).toFunctor.map ((α.app c').map φ) ≫
        α.laxApp f y =
        α.laxApp f x ≫
          (α.app c).map ((G.map f.op).toFunctor.map φ) := α.laxNat f φ
    have hβ : (K.map f.op).toFunctor.map
          ((β.app c').map ((α.app c').map φ)) ≫
        β.laxApp f ((α.app c').obj y) =
        β.laxApp f ((α.app c').obj x) ≫
          (β.app c).map
            ((H.map f.op).toFunctor.map ((α.app c').map φ)) :=
        β.laxNat f ((α.app c').map φ)
    rw [← Category.assoc ((K.map f.op).toFunctor.map _) _ _, hβ,
        Category.assoc, ← Functor.map_comp, hα, Functor.map_comp]
  laxId c x := by
    simp only [Functor.comp_obj, α.laxId, eqToHom_map, β.laxId,
      eqToHom_trans]
  laxComp {c c' c''} f g x := by
    simp only [α.laxComp f g x, β.laxComp f g ((α.app c'').obj x)]
    simp only [Functor.map_comp, (β.app c).map_comp, eqToHom_map,
      Category.assoc, eqToHom_trans_assoc]
    have hβ : (K.map f.op).toFunctor.map
            ((β.app c').map (α.laxApp g x)) ≫
          β.laxApp f ((α.app c').obj
            ((G.map g.op).toFunctor.obj x)) =
          β.laxApp f ((H.map g.op).toFunctor.obj
            ((α.app c'').obj x)) ≫
            (β.app c).map ((H.map f.op).toFunctor.map
              (α.laxApp g x)) :=
        β.laxNat f (α.laxApp g x)
    congr 1
    simp only [← Category.assoc]
    congr 1
    simp only [Category.assoc, eqToHom_refl, Category.id_comp]
    congr 1
    simp only [← Category.assoc]
    congr 1
    exact hβ.symm
```

- [ ] **Step 2: Run `lake build` and fix errors**

Run: `lake build`
Expected: build succeeds.  Mirror `LaxNatTransData.comp` (lines 5951–5986)
or `OplaxNatTransData.comp` (lines 6863–6913) for proof shape; the exact
goal may need slight adjustment due to direction-flipped hypothesis names.
If proofs get long, factor into named lemmas using the
factoring-out-lemmas technique (per CLAUDE.md).

- [ ] **Step 3: Run `lake test`**

Run: `lake test`
Expected: tests pass.

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "feat(utilities): add LaxNatTransContraData.comp"
```

---

### Task 7: Add `LaxNatTransContraData.ofNatTrans`

**Files:**
- Modify: `GebLean/Utilities/Grothendieck.lean`
  (extend the `LaxNatTransContraFunctor` section)

- [ ] **Step 1: Add the strict-NatTrans-to-lax promotion**

Insert before `end LaxNatTransContraFunctor`:

```lean
/-- Promote a strict natural transformation to a lax natural
transformation.  The laxity morphisms are derived from the strict
naturality squares as `eqToHom`. -/
def LaxNatTransContraData.ofNatTrans {G H : Cᵒᵖ ⥤ Cat.{vF, uF}}
    (α : NatTrans G H) : LaxNatTransContraData G H where
  app c := α.app (Opposite.op c)
  laxApp {c c'} f x := eqToHom (by
    have h := α.naturality f.op
    have hx := congrFun (congrArg Functor.obj h) x
    exact hx)
  laxNat _ _ := by
    simp only [eqToHom_naturality]
  laxId _ _ := by
    simp only [eqToHom_trans]
  laxComp _ _ _ := by
    simp only [Functor.map_comp, eqToHom_map, eqToHom_trans,
      Category.assoc]
```

- [ ] **Step 2: Run `lake build` and fix errors**

Run: `lake build`
Expected: build succeeds.  Naturality-square translation may need
explicit `Cat.Hom.toFunctor` chasing; mirror the analogous oplax
construction if needed.

- [ ] **Step 3: Run `lake test`**

Run: `lake test`
Expected: tests pass.

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "feat(utilities): add LaxNatTransContraData.ofNatTrans"
```

---

## Phase B: praEval-specific construction

All in `GebLean/PresheafPRA.lean`, in a new section
`PresheafPRAEvalNat` placed immediately after the existing
`PresheafPRAEvalAtINat` section (currently ending at line 1705).

### Task 8: Add `praPolyEvalSourceFibBif` (private bifunctor)

**Files:**
- Modify: `GebLean/PresheafPRA.lean`
  (after line 1705, open new section `PresheafPRAEvalNat`)

- [ ] **Step 1: Open the new section and add the source-fibre bifunctor**

```lean
/-! ## (I, J)-Naturality (Lax in I) -/

section PresheafPRAEvalNat

attribute [local instance] CategoryTheory.uliftCategory

/--
Source fibre bifunctor for the (I, J)-natural praEval lax bundle.
Sends `op (J, I)` to widened `PRACat I J × PSh(I)`.

PRA factor comes from `presheafPRACatBifunctorUncurriedOp`.
PSh(I) factor comes from projecting `op (J, I)` to `op I` and applying
`presheafCatFunctor`.
-/
private def praPolyEvalSourceFibBif :
    (Cat.{v_J, u_J} × Cat.{v_I, u_I})ᵒᵖ ⥤
      Cat.{max u_I u_J v_I w_I w',
        max (u_I + 1) u_J v_I v_J (w_I + 1) (w' + 1)} :=
  let praFactor :=
    presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J, w_I, w'}
  let pshFactor :
      (Cat.{v_J, u_J} × Cat.{v_I, u_I})ᵒᵖ ⥤ Cat.{...} :=
    -- projection to op I component, then presheafCatFunctor, then
    -- catULiftFunctor2 to widen
    _  -- LSP-discovered exact construction
  -- pair via per-fibre Cat.of (× of widened factors), with map by
  -- (praFactor.map ⊗ pshFactor.map).toCatHom, then catULiftFunctor2
  -- to land in unified Cat universe
  _
```

Initially leave universe annotations and `pshFactor` body as `_`
underscores.  Build will produce "unsolved goals" errors that print the
required types — use those to fill in concretely.

- [ ] **Step 2: Iterate on `lake build` errors to fill in the underscores**

Use the underscore-driven discipline from CLAUDE.md item 7.  Pattern
to follow: `praPolyEvalAtISourceFib` (lines 1477–1506 of PresheafPRA.lean).

- [ ] **Step 3: Run `lake build`**

Run: `lake build`
Expected: build succeeds with no errors and no warnings.

- [ ] **Step 4: Run `lake test`**

Run: `lake test`
Expected: tests pass.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalSourceFibBif (private)"
```

---

### Task 9: Add `praPolyEvalSourceOverI`

**Files:**
- Modify: `GebLean/PresheafPRA.lean`
  (extend `PresheafPRAEvalNat` section)

- [ ] **Step 1: Add the I-indexed source bifunctor**

```lean
/--
Source bifunctor over the I-base.  Sends `op I` to
`praPolyEvalAtISource I`, the fixed-`I` source contraGrothendieck.

Constructed by currying `praPolyEvalSourceFibBif` over the I component
(yielding `Catᵒᵖ ⥤ (Catᵒᵖ ⥤ Cat)`), then composing with
`grothendieckContraFunctor Cat`.
-/
def praPolyEvalSourceOverI :
    Cat.{v_I, u_I}ᵒᵖ ⥤ Cat.{...} :=
  _  -- LSP-discovered: curry praPolyEvalSourceFibBif over I,
     -- then ⋙ grothendieckContraFunctor Cat.{v_J, u_J}
```

Use `_` to find the goal type, then construct concretely.

- [ ] **Step 2: Iterate on `lake build` errors to fill in**

The construction is conceptually:
- `praPolyEvalSourceFibBif` is `(Cat × Cat)ᵒᵖ ⥤ Cat`.
- Reorganize as `Catᵒᵖ ⥤ (Catᵒᵖ ⥤ Cat)` with I outer, J inner.  This may
  need going via `(Cat × Cat)ᵒᵖ ≌ Catᵒᵖ × Catᵒᵖ` (via `prodOpEquiv`)
  and then `Functor.curry`.
- Compose with `grothendieckContraFunctor Cat.{v_J, u_J}` to get
  `Catᵒᵖ ⥤ Cat`.

- [ ] **Step 3: Run `lake build`**

Run: `lake build`
Expected: build succeeds.

- [ ] **Step 4: Run `lake test`**

Run: `lake test`
Expected: tests pass.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalSourceOverI"
```

---

### Task 10: Add `praPolyEvalTargetOverI`

**Files:**
- Modify: `GebLean/PresheafPRA.lean`
  (extend `PresheafPRAEvalNat` section)

- [ ] **Step 1: Add the I-indexed target bifunctor (constant)**

```lean
/--
Target bifunctor over the I-base.  Constant at `praPolyEvalTarget`,
the J-only target contraGrothendieck.  Action on Cat-mors is the
identity functor on `praPolyEvalTarget`.
-/
def praPolyEvalTargetOverI :
    Cat.{v_I, u_I}ᵒᵖ ⥤ Cat.{...} :=
  (Functor.const _).obj
    praPolyEvalTarget.{u_I, v_I, u_J, v_J, w_I, w'}
```

- [ ] **Step 2: Run `lake build` and adjust universe annotations**

Run: `lake build`
Expected: build succeeds.  Universe annotations LSP-discovered.

- [ ] **Step 3: Run `lake test`**

Run: `lake test`
Expected: tests pass.

- [ ] **Step 4: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalTargetOverI"
```

---

### Task 11: Add `praPolyEvalLaxNatTrans_app` (private helper)

**Files:**
- Modify: `GebLean/PresheafPRA.lean`
  (extend `PresheafPRAEvalNat` section)

- [ ] **Step 1: Add the per-I component helper**

```lean
/--
Per-`I` component of the lax nat trans: the existing fixed-`I` flat
functor `praPolyEvalAtIFunctor I`, possibly with a curry-bridging
`eqToHom` to align with `praPolyEvalSourceOverI.obj (op I)` and
`praPolyEvalTargetOverI.obj (op I)`.
-/
private def praPolyEvalLaxNatTrans_app (I : Cat.{v_I, u_I}) :
    praPolyEvalSourceOverI.{u_I, v_I, u_J, v_J, w_I, w'}.obj
        (Opposite.op I) ⥤
      praPolyEvalTargetOverI.{u_I, v_I, u_J, v_J, w_I, w'}.obj
        (Opposite.op I) :=
  _  -- LSP-discovered; ideally `praPolyEvalAtIFunctor I` directly,
     -- with `eqToHom`/`Functor.cast` only if curry-bridging is needed
```

- [ ] **Step 2: Iterate on `lake build` to find the right form**

If `praPolyEvalSourceOverI.obj (op I)` is definitionally equal to
`praPolyEvalAtISource I`, the body is just `praPolyEvalAtIFunctor I`.
Otherwise, an `eqToHom` or `Functor` cast is needed.

If the bodies don't match definitionally, factor out a separate
`praPolyEvalSourceOverI_obj_eq (I : Cat) :
praPolyEvalSourceOverI.obj (op I) = praPolyEvalAtISource I` lemma
(possibly `rfl` or via `Cat.ext`) and use `eqToHom` of it.

- [ ] **Step 3: Run `lake build`**

Run: `lake build`
Expected: build succeeds.

- [ ] **Step 4: Run `lake test`**

Run: `lake test`
Expected: tests pass.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalLaxNatTrans_app helper"
```

---

### Task 12: Add `praPolyEvalLaxNatTrans_laxApp` (private helper)

**Files:**
- Modify: `GebLean/PresheafPRA.lean`
  (extend `PresheafPRAEvalNat` section)

- [ ] **Step 1: Add the lax-comparison helper**

```lean
/--
Lax-comparison morphism at `f_I : I_s ⟶ I_t` and
`x : praPolyEvalAtISource I_t`.

Concretely, for `x = mkObj J (P_t, Z_t)`:
- Base part: `𝟙_J` (no J change at the I-laxApp level).
- Fibre part: forward whisker, taking the widened presheaf
  `praEvalAt P_t Z_t` to the widened presheaf
  `praEvalAt (f_I^* P_t) (f_I^* Z_t)`.
-/
private def praPolyEvalLaxNatTrans_laxApp
    {I I' : Cat.{v_I, u_I}} (f : I ⟶ I')
    (x : praPolyEvalSourceOverI.{u_I, v_I, u_J, v_J, w_I, w'}.obj
        (Opposite.op I')) :
    (praPolyEvalTargetOverI.{u_I, v_I, u_J, v_J, w_I, w'}.map
        f.op).toFunctor.obj
      ((praPolyEvalLaxNatTrans_app.{u_I, v_I, u_J, v_J, w_I, w'}
        I').obj x) ⟶
    (praPolyEvalLaxNatTrans_app.{u_I, v_I, u_J, v_J, w_I, w'} I).obj
      ((praPolyEvalSourceOverI.{u_I, v_I, u_J, v_J, w_I, w'}.map
        f.op).toFunctor.obj x) :=
  _  -- LSP-discovered; mkHom 𝟙_J <forward-whisker on widened fibre>
```

- [ ] **Step 2: Iterate on `lake build`**

Construction sketch:
- The base part of the morphism in `praPolyEvalTarget` is `𝟙` on the
  J-component of `x`.
- The fibre part is the forward whisker, which at the unwidened level
  is `Functor.whiskerLeft (f.op : Iᵒᵖ → I'ᵒᵖ)` on a presheaf-on-J
  (constant in I).  Concretely, for a presheaf `R : Jᵒᵖ → Type _`,
  `R = praEvalAt P_t Z_t` and the result is
  `praEvalAt (f_I^* P_t) (f_I^* Z_t)`, with the natural inclusion as
  the forward whisker.
- Use `GrothendieckContraFunctor.mkHom` with the base part `𝟙_J` and
  the fibre being the (widened) forward whisker.

If the forward-whisker construction is non-trivial, factor it out as a
private helper `praPolyEvalForwardWhisker` (e.g.,
`praPolyEvalForwardWhisker f x : (something on widened presheaves)`).

- [ ] **Step 3: Run `lake build`**

Run: `lake build`
Expected: build succeeds.

- [ ] **Step 4: Run `lake test`**

Run: `lake test`
Expected: tests pass.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalLaxNatTrans_laxApp helper"
```

---

### Task 13: Add `praPolyEvalLaxNatTrans` bundle

**Files:**
- Modify: `GebLean/PresheafPRA.lean`
  (extend `PresheafPRAEvalNat` section)

- [ ] **Step 1: Assemble the lax nat trans bundle**

```lean
/--
The (I, J, P, Z)-natural-but-lax bundle representing `praEval` as an
unapplied operator.  The per-`I` component is the existing fixed-`I`
flat functor; the lax structure is the forward-whisker comparison
encoding I-naturality.
-/
def praPolyEvalLaxNatTrans :
    LaxNatTransContraData
      praPolyEvalSourceOverI.{u_I, v_I, u_J, v_J, w_I, w'}
      praPolyEvalTargetOverI.{u_I, v_I, u_J, v_J, w_I, w'} where
  app I :=
    praPolyEvalLaxNatTrans_app.{u_I, v_I, u_J, v_J, w_I, w'} I
  laxApp f x :=
    praPolyEvalLaxNatTrans_laxApp.{u_I, v_I, u_J, v_J, w_I, w'} f x
  laxNat := by
    intros
    -- forward-whisker is functorial in the fibre data (whiskering a
    -- NatTrans by a fixed functor is functorial in the NatTrans).
    -- Should be `rfl` modulo widening or a short Cat.Hom.ext + rfl.
    _
  laxId := by
    intros
    -- f_I = 𝟙: forward whisker by 𝟙.op = 𝟙 is identity, reduces to
    -- eqToHom by laxNatTransContraIdEqProof.
    _
  laxComp := by
    intros
    -- (f_I ≫ g_I).op = g_I.op ≫ f_I.op; whisker composition is strict
    -- via Cat-functor-precomposition functoriality.
    _
```

- [ ] **Step 2: Iterate on the three coherence proofs**

Replace each `_` with the actual proof.  Discovery process:
1. Try `apply Cat.Hom.ext; rfl` first.
2. If that fails, factor out per-step lemmas using the
   factoring-out-lemmas technique.
3. For `laxComp`, the equation has the canonical
   `eqToHom`-bracketed form from the framework; align via
   `eqToHom_trans` and forward-whisker functoriality.

If proofs get long (>20 lines each), factor each into a separate
private lemma `praPolyEvalLaxNatTrans_laxNat`,
`praPolyEvalLaxNatTrans_laxId`, `praPolyEvalLaxNatTrans_laxComp`.

- [ ] **Step 3: Run `lake build`**

Run: `lake build`
Expected: build succeeds with no errors and no warnings.

- [ ] **Step 4: Run `lake test`**

Run: `lake test`
Expected: tests pass.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalLaxNatTrans bundle"
```

---

### Task 14: Add `praPolyEvalSourceOverIObj` (source-object helper)

**Files:**
- Modify: `GebLean/PresheafPRA.lean`
  (extend `PresheafPRAEvalNat` section)

- [ ] **Step 1: Add the source-object helper**

```lean
/--
Build a `praPolyEvalSourceOverI.obj (op I)` object from `(I, J, P, Z)`.
Mirrors `praPolyEvalAtISourceObj`.
-/
def praPolyEvalSourceOverIObj
    (I : Cat.{v_I, u_I}) (J : Cat.{v_J, u_J})
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
    (Z : ↑(presheafCat.{u_I, v_I, w_I} I)) :
    praPolyEvalSourceOverI.{u_I, v_I, u_J, v_J, w_I, w'}.obj
      (Opposite.op I) :=
  praPolyEvalAtISourceObj.{u_I, v_I, u_J, v_J, w_I, w'} I J P Z
  -- (with eqToHom transport if needed; see Task 11 notes)
```

If the source's curry collapse from Task 11 was definitional, the body
is the existing helper directly.  If not, transport via the same
`eqToHom`/`eqToIso` used in Task 11.

- [ ] **Step 2: Run `lake build`**

Run: `lake build`
Expected: build succeeds.

- [ ] **Step 3: Run `lake test`**

Run: `lake test`
Expected: tests pass.

- [ ] **Step 4: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalSourceOverIObj helper"
```

---

### Task 15: Add strong bridge `praPolyEvalAtIFunctor_eq_praPolyEvalLaxNatTrans_app`

**Files:**
- Modify: `GebLean/PresheafPRA.lean`
  (extend `PresheafPRAEvalNat` section)

- [ ] **Step 1: Add the strong bridge theorem**

```lean
/--
Strong bridge: the per-`I` component of the lax bundle is exactly the
fixed-`I` flat functor.

This is trivial by construction (the bundle's `app` field is defined
as `praPolyEvalAtIFunctor I` directly, possibly via an `eqToHom`
transport for curry-bridging).
-/
@[simp] theorem praPolyEvalAtIFunctor_eq_praPolyEvalLaxNatTrans_app
    (I : Cat.{v_I, u_I}) :
    praPolyEvalLaxNatTrans.{u_I, v_I, u_J, v_J, w_I, w'}.app I =
    praPolyEvalAtIFunctor.{u_I, v_I, u_J, v_J, w_I, w'} I := rfl
  -- If body is non-rfl due to curry-bridging eqToHom, the statement
  -- includes the eqToHom on one side and the proof is by
  -- eqToHom-cancellation.
```

- [ ] **Step 2: Run `lake build`**

Run: `lake build`
Expected: build succeeds.  If `rfl` fails due to `eqToHom`, the proof
is `simp [praPolyEvalLaxNatTrans, praPolyEvalLaxNatTrans_app]` or
similar.

- [ ] **Step 3: Run `lake test`**

Run: `lake test`
Expected: tests pass.

- [ ] **Step 4: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add strong bridge theorem"
```

---

### Task 16: Add weak bridge `praEvalAtFunctor_via_praPolyEvalLaxNatTrans`

**Files:**
- Modify: `GebLean/PresheafPRA.lean`
  (extend `PresheafPRAEvalNat` section)

- [ ] **Step 1: Add the weak per-component bridge theorem**

```lean
/--
Weak per-component bridge: the per-component `praEvalAt`-style result
agrees with the unwidened fibre of the bundle's I-component applied to
the source-object helper.

This composes the strong bridge (Task 15) with the existing
`praEvalAtFunctor_via_praPolyEvalAtIFunctor`.
-/
@[simp] theorem praEvalAtFunctor_via_praPolyEvalLaxNatTrans
    (I : Cat.{v_I, u_I}) (J : Cat.{v_J, u_J})
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
    (Z : ↑(presheafCat.{u_I, v_I, w_I} I)) :
    ((praEvalAtFunctor.{u_I, v_I, u_J, v_J, w_I, w'} I J).obj P).obj Z =
    (ULift.down.{max (u_I + 1) u_J v_I v_J (w_I + 1) (w' + 1),
        max v_J u_J (u_I + 1) (w_I + 1) (w' + 1)}
      (ULiftHom.objDown.{max (u_I + 1) u_J v_I v_J (w_I + 1) (w' + 1),
          max u_I u_J v_I v_J (w_I + 1) (w' + 1)}
        (show ULiftHom.{max u_I u_J v_I w_I w'}
            (ULift.{max (u_I + 1) u_J v_I v_J (w_I + 1) (w' + 1),
              max v_J u_J (u_I + 1) (w_I + 1) (w' + 1)}
              (Jᵒᵖ ⥤ Type (max w' u_I w_I))) from
          GrothendieckContraFunctor.objFiber
            ((praPolyEvalLaxNatTrans.{u_I, v_I, u_J, v_J, w_I, w'}.app
                I).obj
              (praPolyEvalSourceOverIObj.{u_I, v_I, u_J, v_J, w_I, w'}
                I J P Z))))) := by
  rw [praPolyEvalAtIFunctor_eq_praPolyEvalLaxNatTrans_app]
  exact praEvalAtFunctor_via_praPolyEvalAtIFunctor I J P Z
```

The exact universe annotations on the RHS mirror those of
`praEvalAtFunctor_via_praPolyEvalAtIFunctor` (PresheafPRA.lean lines
1685–1703).

- [ ] **Step 2: Run `lake build` and adjust if needed**

Run: `lake build`
Expected: build succeeds.  If the `praPolyEvalSourceOverIObj` collapse
to `praPolyEvalAtISourceObj` involved an `eqToHom`, the proof needs to
account for that via additional `eqToHom_*` rewrites.

- [ ] **Step 3: Run `lake test`**

Run: `lake test`
Expected: tests pass.

- [ ] **Step 4: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add weak per-component bridge theorem"
```

---

## Phase C: Tests

### Task 17: Create test file with type-signature sanity tests

**Files:**
- Create: `GebLeanTests/Utilities/PresheafPRAEvalNat.lean`

- [ ] **Step 1: Create the test file with type-signature tests**

```lean
import GebLean

namespace GebLeanTests.Utilities.PresheafPRAEvalNat

open GebLean
open CategoryTheory

/-! ## Type-signature sanity -/

-- LaxNatTransContraData framework signatures
example : ∀ (G F : Cat.{0, 0}ᵒᵖ ⥤ Cat.{0, 0}),
    Type _ := fun G F => LaxNatTransContraData G F

-- praPolyEvalSourceOverI signature
example : Cat.{0, 0}ᵒᵖ ⥤ Cat.{_, _} :=
  praPolyEvalSourceOverI.{0, 0, 0, 0, 0, 0}

-- praPolyEvalTargetOverI signature
example : Cat.{0, 0}ᵒᵖ ⥤ Cat.{_, _} :=
  praPolyEvalTargetOverI.{0, 0, 0, 0, 0, 0}

-- praPolyEvalLaxNatTrans signature
example :
    LaxNatTransContraData
      praPolyEvalSourceOverI.{0, 0, 0, 0, 0, 0}
      praPolyEvalTargetOverI.{0, 0, 0, 0, 0, 0} :=
  praPolyEvalLaxNatTrans.{0, 0, 0, 0, 0, 0}

end GebLeanTests.Utilities.PresheafPRAEvalNat
```

- [ ] **Step 2: Run `lake build` (file not yet registered, so this is just a syntax check via direct compilation)**

The test file will not be picked up until registered in Task 18.  For
this task, manually verify by editing — the `import GebLean` should
make all the new artifacts available.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRAEvalNat.lean
git commit -m "tests: create PresheafPRAEvalNat with type-signature sanity"
```

---

### Task 18: Register test file in `GebLeanTests.lean`

**Files:**
- Modify: `GebLeanTests.lean`

- [ ] **Step 1: Add the import line**

Locate the existing test imports (e.g., `import GebLeanTests.Utilities.PresheafPRAEvalAtINat`) and add the new line in alphabetical/sequential order:

```lean
import GebLeanTests.Utilities.PresheafPRAEvalNat
```

- [ ] **Step 2: Run `lake build`**

Run: `lake build`
Expected: build succeeds.

- [ ] **Step 3: Run `lake test`**

Run: `lake test`
Expected: tests pass; the new file's `example` declarations type-check.

- [ ] **Step 4: Commit**

```bash
git add GebLeanTests.lean
git commit -m "tests: register PresheafPRAEvalNat test file"
```

---

### Task 19: Add framework sanity tests (`id`, `comp`, `ofNatTrans`)

**Files:**
- Modify: `GebLeanTests/Utilities/PresheafPRAEvalNat.lean`

- [ ] **Step 1: Add the framework-level test section**

Append to the test file (after the type-signature tests):

```lean
/-! ## LaxNatTransContraData framework sanity -/

-- Identity lax nat trans on a small Cᵒᵖ ⥤ Cat
example (G : Cat.{0, 0}ᵒᵖ ⥤ Cat.{0, 0}) :
    LaxNatTransContraData G G :=
  LaxNatTransContraData.id G

-- Composition of identities is identity (up to defeq, but at least
-- the type checks)
example (G : Cat.{0, 0}ᵒᵖ ⥤ Cat.{0, 0}) :
    LaxNatTransContraData G G :=
  (LaxNatTransContraData.id G).comp (LaxNatTransContraData.id G)

-- ofNatTrans of an identity NatTrans
example (G : Cat.{0, 0}ᵒᵖ ⥤ Cat.{0, 0}) :
    LaxNatTransContraData G G :=
  LaxNatTransContraData.ofNatTrans (𝟙 G)
```

- [ ] **Step 2: Run `lake build` and `lake test`**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRAEvalNat.lean
git commit -m "tests: add LaxNatTransContraData framework sanity tests"
```

---

### Task 20: Add bridge collapse tests

**Files:**
- Modify: `GebLeanTests/Utilities/PresheafPRAEvalNat.lean`

- [ ] **Step 1: Add the bridge collapse test section**

Append:

```lean
/-! ## Bridge collapse -/

-- Strong bridge: at concrete I = Cat.of Discrete.{0} (Fin 0), the
-- bundle's app component equals praPolyEvalAtIFunctor I.
example :
    praPolyEvalLaxNatTrans.{0, 0, 0, 0, 0, 0}.app
      (Cat.of (CategoryTheory.Discrete (Fin 0))) =
    praPolyEvalAtIFunctor.{0, 0, 0, 0, 0, 0}
      (Cat.of (CategoryTheory.Discrete (Fin 0))) := by
  rw [praPolyEvalAtIFunctor_eq_praPolyEvalLaxNatTrans_app]

-- Weak bridge: the per-component evaluation agrees with the bundle's
-- unwidened fibre at concrete inputs.  Type-checks via the simp
-- bridge.
section WeakBridge
variable (I : Cat.{0, 0}) (J : Cat.{0, 0})
  (P : PresheafPRACat.{0, 0, 0, 0, 0, 0} I J)
  (Z : ↑(presheafCat.{0, 0, 0} I))

example : ((praEvalAtFunctor.{0, 0, 0, 0, 0, 0} I J).obj P).obj Z =
    _ := by
  exact praEvalAtFunctor_via_praPolyEvalLaxNatTrans I J P Z

end WeakBridge
```

(The `_` will be filled in by Lean from the bridge-theorem's RHS.)

- [ ] **Step 2: Run `lake build` and `lake test`**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRAEvalNat.lean
git commit -m "tests: add bridge collapse tests for praPolyEvalLaxNatTrans"
```

---

### Task 21: Add per-component compatibility tests

**Files:**
- Modify: `GebLeanTests/Utilities/PresheafPRAEvalNat.lean`

- [ ] **Step 1: Add per-component accessor tests**

Append:

```lean
/-! ## Per-component accessor compatibility -/

-- praEvalAt produces the same shape after introducing the lax bundle
section PerComponent
variable (I : Cat.{0, 0}) (J : Cat.{0, 0})
  (P : PresheafPRACat.{0, 0, 0, 0, 0, 0} I J)
  (Z : ↑(presheafCat.{0, 0, 0} I))
  (j : Jᵒᵖ)

example : praEvalAt.{0, 0, 0, 0, 0, 0} I J P Z j =
    ((praEvalAtFunctor.{0, 0, 0, 0, 0, 0} I J).obj P).obj Z |>.obj j :=
  rfl

example (a : praPositions.{0, 0, 0, 0, 0, 0} I J P j)
    (η : praDirectionsAt.{0, 0, 0, 0, 0, 0} I J P j a ⟶ Z) :
    praEvalAt_index.{0, 0, 0, 0, 0, 0} I J P Z
      (praEvalAt_mk.{0, 0, 0, 0, 0, 0} I J P Z j a η) = a := rfl

end PerComponent
```

- [ ] **Step 2: Run `lake build` and `lake test`**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRAEvalNat.lean
git commit -m "tests: add per-component accessor compatibility tests"
```

---

### Task 22: Add lax coherence tests

**Files:**
- Modify: `GebLeanTests/Utilities/PresheafPRAEvalNat.lean`

- [ ] **Step 1: Add coherence tests at concrete inputs**

Append:

```lean
/-! ## Lax coherence at concrete inputs -/

-- laxId at the identity I-mor: laxApp 𝟙 x = eqToHom (proof).
section LaxId
variable (I : Cat.{0, 0})
  (x : praPolyEvalSourceOverI.{0, 0, 0, 0, 0, 0}.obj (Opposite.op I))

example :
    praPolyEvalLaxNatTrans.{0, 0, 0, 0, 0, 0}.laxApp (𝟙 I) x =
    eqToHom (laxNatTransContraIdEqProof
      praPolyEvalLaxNatTrans.{0, 0, 0, 0, 0, 0}.app I x) :=
  praPolyEvalLaxNatTrans.{0, 0, 0, 0, 0, 0}.laxId I x

end LaxId
```

- [ ] **Step 2: Run `lake build` and `lake test`**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRAEvalNat.lean
git commit -m "tests: add lax coherence tests for praPolyEvalLaxNatTrans"
```

---

### Task 23: Add universe polymorphism tests

**Files:**
- Modify: `GebLeanTests/Utilities/PresheafPRAEvalNat.lean`

- [ ] **Step 1: Add universe polymorphism tests at mixed universes**

Append:

```lean
/-! ## Universe polymorphism -/

-- Mixed universes: u_I = 1 (others 0)
example :
    LaxNatTransContraData
      praPolyEvalSourceOverI.{0, 1, 0, 0, 0, 0}
      praPolyEvalTargetOverI.{0, 1, 0, 0, 0, 0} :=
  praPolyEvalLaxNatTrans.{0, 1, 0, 0, 0, 0}

-- Mixed universes: w_I = 1 (others 0)
example :
    LaxNatTransContraData
      praPolyEvalSourceOverI.{0, 0, 0, 0, 1, 0}
      praPolyEvalTargetOverI.{0, 0, 0, 0, 1, 0} :=
  praPolyEvalLaxNatTrans.{0, 0, 0, 0, 1, 0}

-- All-zero baseline (already covered by other tests, restate for clarity)
example :
    LaxNatTransContraData
      praPolyEvalSourceOverI.{0, 0, 0, 0, 0, 0}
      praPolyEvalTargetOverI.{0, 0, 0, 0, 0, 0} :=
  praPolyEvalLaxNatTrans.{0, 0, 0, 0, 0, 0}
```

- [ ] **Step 2: Run `lake build` and `lake test`**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRAEvalNat.lean
git commit -m "tests: add universe polymorphism tests for praPolyEvalLaxNatTrans"
```

---

## Phase D: Workstream notes

### Task 24: Update `.session/workstreams/presheaf-pra.md`

**Files:**
- Modify: `.session/workstreams/presheaf-pra.md`

- [ ] **Step 1: Add a new section after the existing "praEvalAtI Naturality" section**

Append (after line 620 of the workstream notes):

```markdown
## praEval (I, J)-Naturality (Lax in I) (complete, 2026-04-27)

Goal: realize the (I, J, P, Z)-natural form of `praEvalAtFunctor` as a
lax natural transformation bundle, with strict J/P/Z-naturality and lax
I-naturality (forward whisker).  Bundle is the type of the unapplied
`praEval` operator.

Spec:
`docs/superpowers/specs/2026-04-27-praEval-IJ-naturality-design.md`
(gitignored).
Plan: `docs/superpowers/plans/2026-04-27-praEval-IJ-naturality.md`
(gitignored).

### Done

| Commit | Task |
|--------|------|
| (TBD) | Task 1: LaxNatTransContra{App,LaxApp,LaxNat} abbrevs |
| (TBD) | Task 2: LaxNatTransContraIdEq + proof + LaxId |
| (TBD) | Task 3: LaxNatTransContraCompEq* + proofs + LaxComp |
| (TBD) | Task 4: LaxNatTransContraData bundle structure |
| (TBD) | Task 5: LaxNatTransContraData.id |
| (TBD) | Task 6: LaxNatTransContraData.comp |
| (TBD) | Task 7: LaxNatTransContraData.ofNatTrans |
| (TBD) | Task 8: praPolyEvalSourceFibBif (private) |
| (TBD) | Task 9: praPolyEvalSourceOverI |
| (TBD) | Task 10: praPolyEvalTargetOverI |
| (TBD) | Task 11: praPolyEvalLaxNatTrans_app helper |
| (TBD) | Task 12: praPolyEvalLaxNatTrans_laxApp helper |
| (TBD) | Task 13: praPolyEvalLaxNatTrans bundle |
| (TBD) | Task 14: praPolyEvalSourceOverIObj helper |
| (TBD) | Task 15: strong bridge theorem |
| (TBD) | Task 16: weak per-component bridge theorem |
| (TBD) | Tasks 17-23: tests |

### Design notes (preserve for future sessions)

- The construction is **lax** in I (forward whisker), strict in J/P/Z.
  The strict-functor lift between contraGrothendiecks does not exist
  in either direction (analyzed in the spec; documented also in
  `Utilities/Grothendieck.lean`'s `LaxNatTransContraFunctor` section
  doc-comment).

- The new infrastructure `LaxNatTransContraData` does NOT have a
  `.toFunctor` extractor — by design, since the lift is impossible.
  The bundle itself is the artifact.

- The bundle's per-`I` component is exactly `praPolyEvalAtIFunctor I`
  (the fixed-`I` form from the praEvalAtI workstream).  Strong bridge
  is `rfl` (or near-`rfl` with `eqToHom` for curry-bridging).

- The `praPolyEvalSourceOverI` is built by curry of an `(I, J)`-bifunctor
  + `grothendieckContraFunctor Cat`.  Whether
  `praPolyEvalSourceOverI.obj (op I) = praPolyEvalAtISource I` is
  definitional or up to `eqToHom` is determined at implementation time
  (Task 11).

### Follow-ups

- Symmetric infrastructure (`OplaxNatTransContraFunctorData` for the
  unprimed contra setting): would complete the four-corner table of
  oplax/lax × cov-base/contra-base.  Not needed for current consumers.

- `praDirections` (I, J)-naturality is already strict; no parallel lax
  workstream needed there.
```

- [ ] **Step 2: Run `markdownlint-cli2`**

Run: `markdownlint-cli2 .session/workstreams/presheaf-pra.md`
Expected: no lint warnings.

- [ ] **Step 3: Commit**

```bash
git add .session/workstreams/presheaf-pra.md
git commit -m "session: praEval (I,J)-naturality workstream complete"
```

---

## Total: 24 tasks across 4 phases

- Phase A (infrastructure): Tasks 1-7 (7 tasks)
- Phase B (praEval-specific): Tasks 8-16 (9 tasks)
- Phase C (tests): Tasks 17-23 (7 tasks)
- Phase D (workstream notes): Task 24 (1 task)

Each task produces ONE commit on `terence/grothendieck`.  Build and
test stay clean (no warnings, no failures) after every task.
