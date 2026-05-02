# Strict Two-Sided Grothendieck Construction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Replace the existing non-slice-refined two-sided Grothendieck constructions in `GebLean/Utilities/Grothendieck.lean` with a single strict construction (Lucyshyn-Wright Def. 7.1 / Stefanich arXiv:2011.03027) landing in `Over (Cat.of (C × D))`, realized via two equivalent compositional orderings plus a natural isomorphism between them.

**Architecture:** Build two reusable slice-preserving Grothendieck primitives — `sliceContraFunctor : (Dᵒᵖ ⥤ Over C) ⥤ Over (Cat.of (C × D))` and `sliceCovFunctor : (C ⥤ Over D) ⥤ Over (Cat.of (C × D))` — then express both two-sided orderings as thin compositions with `whiskeringRight`/`flipFunctor`/`Grothendieck.functor`/`grothendieckContraFunctorOver`, then prove the isomorphism between the two orderings.

**Tech Stack:** Lean 4, mathlib's `CategoryTheory.Grothendieck`, `CategoryTheory.Comma.Over`, `CategoryTheory.Whiskering`, `CategoryTheory.Functor.Category`, `CategoryTheory.Products.Basic`; project's existing `grothendieckFunctorOver`, `grothendieckContraFunctor`, `grothendieckContraFunctorOver`.

**Reference spec:** `docs/superpowers/specs/2026-04-13-strict-two-sided-grothendieck-design.md`.

**Reference math:** `docs/two-sided-grothendieck-construction.md` (Lucyshyn-Wright / Stefanich).

**Project policy reminders:**
- No `sorry`, `admit`, `axiom` — only Lean's native type theory.
- No `noncomputable`.
- 80-character line limit.
- Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).
- When stuck on a proof, invoke `lean4:sorry-filler-deep` agent (project has a precedent for this with the morphism convenience API of `grothendieckContraFunctor`).

---

## File Structure

All changes are to `GebLean/Utilities/Grothendieck.lean`. New code is added in a single new section `StrictTwoSidedGrothendieck` placed **after** the existing `GrothendieckContraFunctorOver` section (line ≈ 7241) and **before** the `CatOverCat` section. Old code is deleted.

**Deleted:**
- `section TwoSidedGrothendieck` and its contents (`twoSidedGrothendieckCovContra`, `twoSidedGrothendieckContraCov`).
- `section StrictTwoSidedViaUncurry` and its contents (`strictTwoSidedGrothendieckUncurried`).

**Added, in order:**
- `section StrictTwoSidedGrothendieck` with:
  - `sliceContraFunctor.projC` (helper functor)
  - `sliceContraFunctor` (main primitive)
  - `sliceCovFunctor.projD` (symmetric helper functor)
  - `sliceCovFunctor` (main primitive)
  - `twoSidedGrothendieckCovContra` (thin composition)
  - `twoSidedGrothendieckContraCov` (thin composition)
  - `twoSidedGrothendieckIso` (natural iso between the two orderings)

---

## Task 1: Remove obsolete two-sided Grothendieck constructions

**Files:**
- Modify: `GebLean/Utilities/Grothendieck.lean` (delete sections at ≈ lines 7260–7330)

- [ ] **Step 1: Locate the sections to delete**

Run:
```bash
grep -n "^section TwoSidedGrothendieck\|^end TwoSidedGrothendieck\|^section StrictTwoSidedViaUncurry\|^end StrictTwoSidedViaUncurry\|^/-! ## Two-Sided\|^/-! ## Strict Two-Sided" GebLean/Utilities/Grothendieck.lean
```

Expected: line numbers for the section boundaries of `TwoSidedGrothendieck` and `StrictTwoSidedViaUncurry` plus their header comments.

- [ ] **Step 2: Delete the `TwoSidedGrothendieck` section**

Using the Edit tool, delete the block from `/-! ## Two-Sided Grothendieck Construction -/` through `end TwoSidedGrothendieck` inclusive. The `twoSidedGrothendieckCovContra` and `twoSidedGrothendieckContraCov` definitions inside go away.

- [ ] **Step 3: Delete the `StrictTwoSidedViaUncurry` section**

Using the Edit tool, delete the block from `/-! ## Strict Two-Sided Grothendieck via Uncurry + Slice Grothendieck -/` through `end StrictTwoSidedViaUncurry` inclusive.

- [ ] **Step 4: Verify no references to deleted names remain in this file**

Run:
```bash
grep -n "twoSidedGrothendieckCovContra\|twoSidedGrothendieckContraCov\|strictTwoSidedGrothendieckUncurried" GebLean/Utilities/Grothendieck.lean
```

Expected: no matches.

- [ ] **Step 5: Full build**

Run: `lake build GebLean.Utilities.Grothendieck`
Expected: success (no errors, no warnings).

- [ ] **Step 6: Full project build + tests**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 7: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "$(cat <<'EOF'
Remove non-slice-refined two-sided Grothendieck constructions

These don't match the standard strict two-sided Grothendieck
construction (Lucyshyn-Wright Def. 7.1). They're being replaced with
a proper slice-refined version landing in Over (Cat.of (C × D)).

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 2: Define `sliceContraFunctor.projC` helper

**Files:**
- Modify: `GebLean/Utilities/Grothendieck.lean` (insert new section `StrictTwoSidedGrothendieck` after `end GrothendieckContraFunctorOver`)

**Mathematical content:** For `G : Dᵒᵖ ⥤ Over C`, define the functor from the contra-Grothendieck total of `G ⋙ Over.forget` to `C`, using `G`'s slice structure (the `.hom` field of each `G.obj d : Over C`).

- [ ] **Step 1: Open the new section and add the helper**

Insert at the location (replacing the existing `/-! ## Total Category of Functors into `Cat` -/` comment line — add the new section *before* it):

```lean
end GrothendieckContraFunctorOver

/-! ## Strict Two-Sided Grothendieck Construction

This section implements the strict two-sided Grothendieck
construction for bifunctors `H : Dᵒᵖ ⥤ C ⥤ Cat` (Lucyshyn-Wright
Def. 7.1 / Stefanich arXiv:2011.03027), landing in
`Over (Cat.of (C × D))` so that the commutativity conditions of
the two-sided construction are encoded by slice morphisms.

Built from two reusable slice-preserving Grothendieck primitives:
`sliceContraFunctor` (contravariant outer) and `sliceCovFunctor`
(covariant outer).  The two-sided construction is then realized
compositionally in two equivalent orderings, related by a natural
isomorphism.
-/

section StrictTwoSidedGrothendieck

universe v_sp u_sp

variable {C D : Cat.{v_sp, u_sp}}

/--
The `C`-direction projection of the slice-preserving contravariant
Grothendieck construction.  Given `G : Dᵒᵖ ⥤ Over C`, maps the
total category of the contravariant Grothendieck of
`G ⋙ Over.forget` to `C` by applying each fibre's slice
projection `(G.obj (op d)).hom` at the appropriate object.
-/
def sliceContraFunctor.projC
    (G : Dᵒᵖ ⥤ Over (T := Cat.{v_sp, u_sp}) C) :
    ((grothendieckContraFunctor D).obj (G ⋙ Over.forget)).α ⥤
      (C : Cat.{v_sp, u_sp}) where
  obj opg :=
    (G.obj opg.unop.base).hom.toFunctor.obj opg.unop.fiber.unop
  map {opg₁ opg₂} f := by
    refine (G.obj opg₁.unop.base).hom.toFunctor.map f.unop.fiber.unop ≫
      eqToHom ?_
    have hw : (G.map f.unop.base).left.toFunctor ⋙
        (G.obj opg₁.unop.base).hom.toFunctor =
        (G.obj opg₂.unop.base).hom.toFunctor := by
      rw [← Cat.Hom.comp_toFunctor]
      exact congrArg _ (Over.w (G.map f.unop.base))
    exact congrArg (fun F => F.obj opg₂.unop.fiber.unop) hw
  map_id opg := by simp
  map_comp f g := by simp

end StrictTwoSidedGrothendieck

/-! ## Total Category of Functors into `Cat` -/
```

**Notes for the implementer:**

1. Do not commit the placeholder `end StrictTwoSidedGrothendieck` if later tasks will reopen the section. Each task inserts new definitions *before* the `end` in the growing section; keep the `end` as the closing marker.

2. If `simp` for `map_id`/`map_comp` doesn't close the goals, invoke the `lean4:sorry-filler-deep` agent with the specific failing goal. The proof is deterministic — functoriality + `eqToHom` coherence. Don't hand-trace more than ~5 minutes before delegating.

3. The signature uses `Cat.{v_sp, u_sp}` for both `C` and `D` plus the fibres, matching the same-universe constraint imposed by slice refinement via `Over`.

- [ ] **Step 2: Build to verify the helper type-checks and proofs close**

Run: `lake build GebLean.Utilities.Grothendieck`
Expected: success.

If `map_id` or `map_comp` fails, invoke `lean4:sorry-filler-deep` with context: this is a direct functor definition; the proofs should follow from `simp [Grothendieck.id_fiber, Grothendieck.comp_fiber]` or similar, plus `eqToHom` manipulation.

- [ ] **Step 3: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "$(cat <<'EOF'
Add sliceContraFunctor.projC helper

The C-direction projection functor used by the slice-preserving
contravariant Grothendieck construction.  Maps the total category
to C using each fibre's slice projection.

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 3: Define `sliceContraFunctor` main primitive

**Files:**
- Modify: `GebLean/Utilities/Grothendieck.lean` (add `sliceContraFunctor` after `projC` in the new section)

**Mathematical content:** Given `G : Dᵒᵖ ⥤ Over C`, produce an `Over (Cat.of (C × D))` object whose underlying Cat is the contra-Grothendieck of `G ⋙ Over.forget` and whose projection is `(projC G, π_D G)` combined.

- [ ] **Step 1: Add `sliceContraFunctor` with obj, map, map_id, map_comp**

Insert immediately after `sliceContraFunctor.projC`:

```lean
/--
The slice-preserving contravariant Grothendieck construction.
Given `G : Dᵒᵖ ⥤ Over C`, produces an `Over (C × D)` object whose
underlying category is the contravariant Grothendieck of
`G ⋙ Over.forget` and whose projection is the pair of
`sliceContraFunctor.projC` (to `C`) and the standard contra-
Grothendieck forgetful (to `D`).
-/
def sliceContraFunctor :
    (Dᵒᵖ ⥤ Over (T := Cat.{v_sp, u_sp}) C) ⥤
      Over (T := Cat.{v_sp, u_sp}) (Cat.of (C × D)) where
  obj G :=
    Over.mk
      (Prod.functor.obj
        ⟨(sliceContraFunctor.projC G),
         ((grothendieckContraFunctorOver D).obj
           (G ⋙ Over.forget)).hom.toFunctor⟩).toCatHom
  map {G G'} ν :=
    Over.homMk
      ((grothendieckContraFunctor D).map
        (whiskerRight ν Over.forget))
      (by
        -- Commutativity with the pair projection.
        -- Split into C-commutativity and D-commutativity.
        apply Cat.Hom.ext
        sorry  -- Invoke sorry-filler-deep for this proof.
      )
  map_id G := by
    ext
    sorry  -- Invoke sorry-filler-deep — should reduce via
           -- grothContraD.map_id + whiskerRight_id.
  map_comp ν₁ ν₂ := by
    ext
    sorry  -- Invoke sorry-filler-deep — should reduce via
           -- grothContraD.map_comp + whiskerRight_comp.
```

**Note to implementer:** `Prod.functor` may need to be replaced with the correct mathlib API for pairing two functors into a product. Check mathlib for `Prod.lift` or `Functor.prod` or `Prod.mk'` — it may be `CategoryTheory.prod'` or similar. If the exact name fails to resolve, try these alternatives:

```lean
-- Alternative 1: use prod.lift if it exists
((sliceContraFunctor.projC G).prod'
  ((grothendieckContraFunctorOver D).obj (G ⋙ Over.forget)).hom.toFunctor)
-- Alternative 2: explicit anonymous constructor
Functor.mk (fun x => (f.obj x, g.obj x)) (fun h => (f.map h, g.map h))
-- Alternative 3: CategoryTheory.prod of functors via uncurry of pair
```

Search with `grep "prod'.*Functor\|prod.*lift\|pair.*Functor" mathlib` to find the right name.

- [ ] **Step 2: Replace the three `sorry`s using `sorry-filler-deep`**

Dispatch a subagent (type: `lean4:sorry-filler-deep`) with the file path and context about what each proof needs. Context to provide:
- The commutativity proof: `grothendieckContraFunctor D .map` acts by `Grothendieck.map`; the pair projection's commutativity splits into two components (C and D). The D-component commutes by the naturality of `Grothendieck.forget`; the C-component commutes by the commutativity of `ν` over C (from the slice structure).
- `map_id`, `map_comp`: should reduce via mathlib's `grothendieckContraFunctor`'s functoriality identities combined with `whiskerRight_id` and `whiskerRight_comp`.

- [ ] **Step 3: Build to verify**

Run: `lake build GebLean.Utilities.Grothendieck`
Expected: success.

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "$(cat <<'EOF'
Add sliceContraFunctor primitive

The slice-preserving contravariant Grothendieck construction,
generalizing grothendieckContraFunctorOver to input functors valued
in Over C. Produces a strict two-sided slice Over (C × D).

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 4: Define `sliceCovFunctor.projD` and `sliceCovFunctor` (symmetric)

**Files:**
- Modify: `GebLean/Utilities/Grothendieck.lean` (add symmetric versions after `sliceContraFunctor` in the new section)

**Mathematical content:** Dual to Task 2+3. Input is `F : C ⥤ Over D`, output is `Over (Cat.of (C × D))`. Uses the covariant outer (mathlib's `Grothendieck.functor`) and the inner slice's D-direction projection.

- [ ] **Step 1: Add `sliceCovFunctor.projD`**

Insert after `sliceContraFunctor`:

```lean
/--
The `D`-direction projection of the slice-preserving covariant
Grothendieck construction.  Dual to `sliceContraFunctor.projC`.
-/
def sliceCovFunctor.projD
    (F : C ⥤ Over (T := Cat.{v_sp, u_sp}) D) :
    ((grothendieckFunctor C).obj (F ⋙ Over.forget)).α ⥤
      (D : Cat.{v_sp, u_sp}) where
  obj g :=
    (F.obj g.base).hom.toFunctor.obj g.fiber
  map {g₁ g₂} f :=
    (F.obj g₁.base).hom.toFunctor.map f.fiber ≫
      eqToHom (by
        have hw : (F.map f.base).left.toFunctor ⋙
            (F.obj g₂.base).hom.toFunctor =
            (F.obj g₁.base).hom.toFunctor := by
          rw [← Cat.Hom.comp_toFunctor]
          exact congrArg _ (Over.w (F.map f.base))
        -- Unfold goal and apply hw.
        sorry)
  map_id := by sorry
  map_comp := by sorry
```

Invoke `lean4:sorry-filler-deep` for the three sorries. Provide context: this is the cov-variance analogue of `sliceContraFunctor.projC`. The Grothendieck of a covariant functor has forward-direction morphisms, and the `.fiber` component of the morphism is at source, with target given by `(F.map base).obj (source fiber)`.

- [ ] **Step 2: Add `sliceCovFunctor`**

```lean
/--
The slice-preserving covariant Grothendieck construction.  Dual to
`sliceContraFunctor`.
-/
def sliceCovFunctor :
    (C ⥤ Over (T := Cat.{v_sp, u_sp}) D) ⥤
      Over (T := Cat.{v_sp, u_sp}) (Cat.of (C × D)) where
  obj F :=
    Over.mk
      (Prod.functor.obj
        ⟨((grothendieckFunctorOver).obj
           (F ⋙ Over.forget)).hom.toFunctor,
         (sliceCovFunctor.projD F)⟩).toCatHom
  map {F F'} ν :=
    Over.homMk
      ((grothendieckFunctor C).map
        (whiskerRight ν Over.forget))
      (by apply Cat.Hom.ext; sorry)
  map_id F := by ext; sorry
  map_comp ν₁ ν₂ := by ext; sorry
```

(`grothendieckFunctorOver` requires `{E : Cat}`; verify the instance resolves correctly — may need `(E := C)` hint.)

Invoke `lean4:sorry-filler-deep` for these sorries. Context: same pattern as Task 3's proofs, with covariant/contravariant roles swapped.

- [ ] **Step 3: Build**

Run: `lake build GebLean.Utilities.Grothendieck`
Expected: success.

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "$(cat <<'EOF'
Add sliceCovFunctor primitive (dual to sliceContraFunctor)

Symmetric slice-preserving covariant Grothendieck. Together with
sliceContraFunctor, these are the two reusable primitives that the
two-sided Grothendieck is composed from.

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 5: Define `twoSidedGrothendieckCovContra` and `twoSidedGrothendieckContraCov`

**Files:**
- Modify: `GebLean/Utilities/Grothendieck.lean` (add compositions after `sliceCovFunctor` in the new section)

**Mathematical content:** One-line compositions using `whiskeringRight`, `flipFunctor`, and the new primitives.

- [ ] **Step 1: Add `twoSidedGrothendieckCovContra`**

```lean
/--
Strict two-sided Grothendieck construction, covariant-then-
contravariant order.  For `H : Dᵒᵖ ⥤ C ⥤ Cat`, first apply
mathlib's slice-refined `Grothendieck.functor` pointwise in `D` to
get `Dᵒᵖ ⥤ Over C`, then apply `sliceContraFunctor` to land in
`Over (Cat.of (C × D))`.

Objects are triples `(c, d, x : H(d, c))` with a strict
commutativity condition on morphisms expressed by the slice
structure over `C × D`.
-/
def twoSidedGrothendieckCovContra :
    (Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}) ⥤
      Over (T := Cat.{v_sp, u_sp}) (Cat.of (C × D)) :=
  (Functor.whiskeringRight _ _ _).obj Grothendieck.functor ⋙
    sliceContraFunctor
```

- [ ] **Step 2: Add `twoSidedGrothendieckContraCov`**

```lean
/--
Strict two-sided Grothendieck construction, contravariant-then-
covariant order.  For `H : Dᵒᵖ ⥤ C ⥤ Cat`, first flip to
`C ⥤ Dᵒᵖ ⥤ Cat`, then apply `grothendieckContraFunctorOver`
pointwise in `C` to get `C ⥤ Over D`, then apply `sliceCovFunctor`
to land in `Over (Cat.of (C × D))`.

Equal — up to a natural isomorphism proven in
`twoSidedGrothendieckIso` — to `twoSidedGrothendieckCovContra`.
-/
def twoSidedGrothendieckContraCov :
    (Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}) ⥤
      Over (T := Cat.{v_sp, u_sp}) (Cat.of (C × D)) :=
  flipFunctor Dᵒᵖ C Cat.{v_sp, u_sp} ⋙
    (Functor.whiskeringRight _ _ _).obj grothendieckContraFunctorOver ⋙
    sliceCovFunctor
```

(Verify `grothendieckContraFunctorOver` resolves its implicit `{E : Cat}` argument to `D`; may need `(E := D)` hint.)

- [ ] **Step 3: Build**

Run: `lake build GebLean.Utilities.Grothendieck`
Expected: success.

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "$(cat <<'EOF'
Add two orderings of the strict two-sided Grothendieck

Compositional definitions using the slice-preserving primitives.
Both land in Over (Cat.of (C × D)).

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 6: Define `twoSidedGrothendieckIso`

**Files:**
- Modify: `GebLean/Utilities/Grothendieck.lean` (add iso at end of the new section)

**Mathematical content:** The two orderings produce naturally isomorphic slices. At each `H`, there's a functor that reshuffles the triple `(d, c, y) ↔ (c, d, y)` through the appropriate `Opposite` unwrappings. This lifts to an iso in `Over (Cat.of (C × D))` because both projections land in the same pair `(c, d)`.

- [ ] **Step 1: Add the iso skeleton**

```lean
/--
The two orderings of the strict two-sided Grothendieck construction
are naturally isomorphic.  At each `H : Dᵒᵖ ⥤ C ⥤ Cat`, the
iso reshuffles the triple-object data between the nested
`(Dᵒᵖ)^op`-wrapping of `CovContra` and the flipped
`C`-outer-wrapping of `ContraCov`.  Both carry the same underlying
Lucyshyn-Wright data `(a, b, x : b!(X) → a*(X'))` — only the
presentation differs.
-/
def twoSidedGrothendieckIso :
    (twoSidedGrothendieckCovContra : (Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}) ⥤ _) ≅
      twoSidedGrothendieckContraCov :=
  NatIso.ofComponents
    (fun H => sorry)  -- per-H iso in Over (C × D)
    (fun α => by sorry)  -- naturality
```

- [ ] **Step 2: Fill in per-H iso components**

The per-H iso is an iso in `Over (Cat.of (C × D))`. Its underlying Cat-iso reshuffles the triple. Two approaches:

1. **Direct functor-level construction** (~50 lines): define `forward H : CovContra.obj H ⟶ ContraCov.obj H` via `Over.homMk` with the underlying reshuffling functor, and `backward H` likewise; prove they're mutual inverses via `ext` + `simp` on the reshuffle.

2. **Via Grothendieck.functor equivalences** (~unknown lines): both orderings factor through `Grothendieck.functor` in ways that may admit an iso via mathlib's `preEquivalence` or naturality lemmas.

Attempt approach 1 first. Invoke `lean4:sorry-filler-deep` for the concrete iso construction, providing:
- The object-level reshuffle: `op ⟨op d, op ⟨c, y⟩⟩ ↦ ⟨c, op ⟨op d, op y⟩⟩` and vice versa.
- The morphism-level reshuffle: `(β, α, φ) ↦ (α, β, φ)` with the appropriate `.op` / `.unop` adjustments.
- Both should compose to identities by structure eta of `Opposite` and of `Grothendieck.Hom`.

- [ ] **Step 3: Fill in naturality**

Naturality follows from the reshuffle respecting morphisms in `(Dᵒᵖ ⥤ C ⥤ Cat)`. Should reduce via `ext` + `Cat.Hom.ext` + unfolding of both composites to the same thing.

Invoke `lean4:sorry-filler-deep` if naturality doesn't close easily. Context: the reshuffle is essentially the identity at the level of underlying data, so naturality should follow from rewrites.

- [ ] **Step 4: Build**

Run: `lake build GebLean.Utilities.Grothendieck`
Expected: success.

- [ ] **Step 5: Close the section**

Ensure the section ends correctly:

```lean
end StrictTwoSidedGrothendieck
```

- [ ] **Step 6: Full build + tests**

Run: `lake build && lake test`
Expected: both succeed.

- [ ] **Step 7: Verify axiom hygiene**

Run:
```bash
lake env lean -e "#print axioms GebLean.twoSidedGrothendieckIso" 2>&1 | head -5
```
(Or use the project's `check_axioms_inline.sh` if available via `$LEAN4_SCRIPTS`.)

Expected: only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

- [ ] **Step 8: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "$(cat <<'EOF'
Add twoSidedGrothendieckIso natural isomorphism

The two compositional orderings of the strict two-sided Grothendieck
construction produce naturally isomorphic slice objects.  Confirms
the two constructions yield the same Lucyshyn-Wright two-sided
Grothendieck up to iso, modulo nested-Opposite presentation.

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Verification Checklist

After all tasks:

- `lake build` passes with no warnings.
- `lake test` passes.
- `grep "twoSidedGrothendieckCovContra\|twoSidedGrothendieckContraCov" GebLean/Utilities/Grothendieck.lean` returns only the new definitions.
- `grep "sliceContraFunctor\|sliceCovFunctor\|twoSidedGrothendieckIso" GebLean/Utilities/Grothendieck.lean` shows the new primitives and iso.
- `grep "strictTwoSidedGrothendieckUncurried" GebLean/Utilities/Grothendieck.lean` returns no matches.
- Axiom check: only `propext`, `Classical.choice`, `Quot.sound`.
- No `sorry`, no `admit`, no custom `axiom`.
