# Two-Sided Grothendieck Equivalence — Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Prove that `twoSidedGrothendieckCovContra` and `twoSidedGrothendieckContraCov` are equivalent as Cat-valued functors at each bifunctor `H : Dᵒᵖ ⥤ C ⥤ Cat`, providing a full `CategoryTheory.Equivalence` between their underlying Cat objects.

**Architecture:** Exploit the symmetric constructor/destructor APIs (`TwoSidedGrothendieckCovContra` and `TwoSidedGrothendieckContraCov` namespaces) to prove API-level theorems (`mkHom_id`, `mkHom_comp`, plus `homFiber_id`, `homFiber_comp` destructor-compatibility lemmas). Each API-level theorem is a **two-layer proof** (within one namespace's encoding), avoiding the three-layer `eqToHom` tangle that blocked three previous attempts. The Cat functors `forward` and `backward` then become thin wrappers whose `map_id` / `map_comp` follow from the API theorems; unit/counit isos follow by structure eta (same as the existing `twoSidedGrothendieckObjEquiv` which is `rfl` roundtrip).

**Tech Stack:** Lean 4, mathlib `CategoryTheory.Grothendieck`, `CategoryTheory.Comma.Over`, `CategoryTheory.Equivalence`, `CategoryTheory.NatIso`; existing project primitives (`sliceContraFunctor`, `sliceCovFunctor`, `twoSidedGrothendieckCovContra`, `twoSidedGrothendieckContraCov`, `TwoSidedGrothendieckCovContra`, `TwoSidedGrothendieckContraCov` namespaces, `twoSidedGrothendieckObjEquiv`).

**Guiding principles (keep these in mind throughout):**
1. **"One composition step at a time / compose only two things at a time."** No proof obligation should juggle three or more layers simultaneously. If it does, split it.
2. **"Everything higher-order, including functoriality of composition."** Use the fact that `Grothendieck.map`, `whiskerRight`, and categorical composition are themselves functorial to inherit proof obligations rather than reprove them.

**Project policies (CRITICAL):**
- No `sorry`, `admit`, `axiom`, `noncomputable`, `Classical`, `lake clean`.
- 80-character line limit.
- `autoImplicit = false`, `relaxedAutoImplicit = false`.
- Build must stay clean (no warnings; `-DwarningAsError=true`).
- Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`).
- When stuck on a proof, invoke `lean4:sorry-filler-deep` via the Agent tool.

---

## Pre-reading for the implementer

Before starting any task, read and understand:

1. `GebLean/Utilities/Grothendieck.lean` section `StrictTwoSidedGrothendieck` (approximately lines 7318–7975), especially:
   - `twoSidedGrothendieckCovContra` / `twoSidedGrothendieckContraCov` compositional definitions.
   - `TwoSidedGrothendieckCovContra` namespace (mkObj, objD, objC, objFiber, mkHom, homD, homC, homFiber, plus 6 roundtrip simp lemmas) and its existing composition/identity helper simp lemmas (`homD_id`, `homC_id`, `homD_comp`, `homC_comp`).
   - `TwoSidedGrothendieckContraCov` namespace (same structure).
   - `twoSidedGrothendieckEquiv.forwardObj` / `forwardMap` / `backwardObj` / `backwardMap` primitives.
   - `twoSidedGrothendieckObjEquiv` (type-level Equiv with `rfl` roundtrips).
2. `docs/two-sided-grothendieck-construction.md` — the mathematical reference (Lucyshyn-Wright Def. 7.1, Stefanich arXiv:2011.03027). Especially the composition formula:
   > `(c ⋅ a, d ⋅ b, a*(y) ⋅ d!(x))`.
3. `.session/workstreams/two-sided-grothendieck-equivalence.md` — project status and history.
4. `docs/superpowers/specs/2026-04-13-strict-two-sided-grothendieck-design.md` — design spec.
5. `docs/superpowers/plans/2026-04-13-strict-two-sided-grothendieck.md` — the original implementation plan (this new plan extends it).

## Structural overview

The Lucyshyn-Wright morphism data at the API level is `(β : D-morph, α : C-morph, φ : fibre-morph)`, and the composition formula is:
```
mkHom β₁ α₁ φ₁ ≫ mkHom β₂ α₂ φ₂ = mkHom (β₁ ≫ β₂) (α₁ ≫ α₂) <composed-φ>
```
where `<composed-φ>` involves `eqToHom` for coherence across `H`'s bifunctoriality.

Once this is proved for each of the two namespaces (CovContra and ContraCov), the forward and backward Cat functors become immediate:
```lean
forward.map f := mkHom_otherSide (homD f) (homC f) (homFiber f)
forward.map_id := by simp [mkHom_id, homD_id, homC_id, homFiber_id]
forward.map_comp := by simp [mkHom_comp, homD_comp, homC_comp, homFiber_comp]
```

And the unit/counit isos reduce to structure-eta rfl because `mkObj (objD x) (objC x) (objFiber x) = x`.

---

## File Structure

All changes in `GebLean/Utilities/Grothendieck.lean` within the existing `StrictTwoSidedGrothendieck` section. New definitions go at the end of the section (before `end StrictTwoSidedGrothendieck`), organized as:

1. **API fibre lemmas** (per namespace): `homFiber_id`, `homFiber_comp` — identifying the canonical form of the fibre component of identity / composition morphisms in each namespace.
2. **API mkHom lemmas** (per namespace): `mkHom_id`, `mkHom_comp` — the two key theorems.
3. **Cat functors**: `twoSidedGrothendieckEquiv.forward` and `.backward`.
4. **Isos**: `twoSidedGrothendieckEquiv.unitIso` and `.counitIso`.
5. **Equivalence**: `twoSidedGrothendieckEquivalence` (per-`H` equivalence of categories).

---

## Task 1: `homFiber_id` and `homFiber_comp` simp lemmas for both namespaces

**Goal:** Add destructor-composition simp lemmas for the fibre part. These are **two-layer** proofs (within a single namespace) that identify the canonical forms of `homFiber (𝟙 x)` and `homFiber (f ≫ g)`.

**Files:**
- Modify: `GebLean/Utilities/Grothendieck.lean` in `TwoSidedGrothendieckCovContra` and `TwoSidedGrothendieckContraCov` namespaces.

- [ ] **Step 1: Find the existing destructor-composition lemmas**

Run:
```bash
grep -n "homD_id\|homC_id\|homD_comp\|homC_comp\|homFiber" GebLean/Utilities/Grothendieck.lean | head -30
```

Confirm that `homD_id`, `homC_id`, `homD_comp`, `homC_comp` exist in both namespaces (from commit `c856de0d`). The new additions go near them.

- [ ] **Step 2: Add `homFiber_id` to `TwoSidedGrothendieckCovContra`**

Insert (after existing destructor-composition lemmas in that namespace):

```lean
@[simp]
theorem homFiber_id {H : Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}}
    (x : (twoSidedGrothendieckCovContra.obj H).left) :
    homFiber (𝟙 x) = eqToHom (by
      -- The identity morphism's fibre is an eqToHom whose
      -- source / target equality unfolds via Grothendieck.id_fiber
      -- across the two nested layers.
      simp [homD_id, homC_id, Functor.map_id,
        CategoryTheory.Functor.id_obj]) := by
  -- Within a single namespace; should close via Grothendieck.id_fiber
  -- at the outer level + Cat.opFunctor / Functor.op coherence.
  simp only [homFiber, homD_id, homC_id, Quiver.Hom.unop_op,
    Grothendieck.id_fiber]
  rfl
```

If `rfl` doesn't close, invoke `lean4:sorry-filler-deep` with context: goal is `homFiber (𝟙 x) = eqToHom ...`, reduce via `Grothendieck.id_fiber` in the (Grothendieck F)^op layer, then `Grothendieck.id_fiber` in the inner layer; `eqToHom_op` / `eqToHom_unop` to cross `Opposite`.

- [ ] **Step 3: Add `homFiber_comp` to `TwoSidedGrothendieckCovContra`**

Insert:

```lean
@[simp]
theorem homFiber_comp {H : Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}}
    {x y z : (twoSidedGrothendieckCovContra.obj H).left}
    (f : x ⟶ y) (g : y ⟶ z) :
    homFiber (f ≫ g) =
      eqToHom (by simp [homD_comp, homC_comp, Functor.map_comp]) ≫
      ((H.obj (Opposite.op (objD x))).map (homC g)).toFunctor.map
        (homFiber f) ≫
      eqToHom (by
        -- Naturality of H.map _ .app _ intermediate.
        simp) ≫
      ((H.map (homD f).op).app (objC z)).toFunctor.map (homFiber g) ≫
      eqToHom (by simp) := by
  -- Unfold homFiber on the LHS via Grothendieck.comp_fiber at the
  -- outer level; the inner fiber unfolds via
  -- Grothendieck.comp_fiber in the (Grothendieck F)^op.
  sorry -- invoke lean4:sorry-filler-deep if needed
```

**Note to implementer:** The exact `eqToHom` bookkeeping will likely be fiddly. If the `sorry` above doesn't close via `simp` + `Grothendieck.comp_fiber` + `Functor.map_comp` + `eqToHom_comp`, delegate to `lean4:sorry-filler-deep` with context:
- This is the Lucyshyn-Wright composition formula at the fibre level: `a*(φ₂) ∘ α₂!(φ₁)` with `eqToHom` for coherence.
- The proof is an unfold of `homFiber (f ≫ g)` using `Grothendieck.comp_fiber` at the two layers.

The EXACT form of the RHS is less important than the proof being provable — if a different-looking RHS is easier to prove, use that, as long as it's a **definite expression** in terms of `mkHom`, `homD`, `homC`, `homFiber`, `eqToHom`, `Functor.map`.

- [ ] **Step 4: Add `homFiber_id` and `homFiber_comp` to `TwoSidedGrothendieckContraCov`**

Dual of Steps 2–3 with the ContraCov namespace structure. The ContraCov encoding has the outer Grothendieck covariant (no top-level op) with inner `Over.forget` pulling in `grothendieckContraFunctorOver`'s structure, so the `eqToHom` shape will be symmetric but differently arranged.

Same templates as above but targeting `TwoSidedGrothendieckContraCov`.

- [ ] **Step 5: Build incrementally**

After each addition, run:
```
lake build GebLean.Utilities.Grothendieck
```
Expected: success.

- [ ] **Step 6: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "$(cat <<'EOF'
Add homFiber_id and homFiber_comp simp lemmas to two-sided APIs

These complete the destructor-composition simp-lemma set for both
TwoSidedGrothendieckCovContra and TwoSidedGrothendieckContraCov
namespaces.  Each proof is a two-layer computation (within one
namespace's encoding) and provides the canonical forms needed to
prove mkHom_id and mkHom_comp in subsequent tasks.

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 2: `mkHom_id` in both namespaces

**Goal:** Prove that identity morphisms in each two-sided Cat object can be expressed via the `mkHom` constructor.

**Files:** Same file, same section.

- [ ] **Step 1: Add `mkHom_id` to `TwoSidedGrothendieckCovContra`**

Insert after `homFiber_id` / `homFiber_comp`:

```lean
/-- Identity morphisms in the covariant-then-contravariant two-
sided Grothendieck expressed via `mkHom`. -/
theorem mkHom_id {H : Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}}
    (x : (twoSidedGrothendieckCovContra.obj H).left) :
    𝟙 x = mkHom (𝟙 (objD x)) (𝟙 (objC x))
      (eqToHom (by
        simp [Functor.map_id, CategoryTheory.Functor.id_obj])) := by
  -- Apply the roundtrip: 𝟙 x = mkHom (homD (𝟙 x)) (homC (𝟙 x))
  --                           (homFiber (𝟙 x))
  -- by the structure-eta `mkHom (homD f) (homC f) (homFiber f) = f`
  -- for morphisms (analogous to mkObj (objD x) (objC x) (objFiber x) = x).
  -- Then simp with homD_id, homC_id, homFiber_id.
  sorry  -- invoke lean4:sorry-filler-deep if not rfl or simple simp
```

**Note:** The morphism-level structure-eta `mkHom (homD f) (homC f) (homFiber f) = f` should hold by `rfl` (analogous to `twoSidedGrothendieckObjEquiv`'s rfl roundtrips). If it does, this proof is essentially one-line: apply that structure-eta, then simp.

- [ ] **Step 2: Add `mkHom_id` to `TwoSidedGrothendieckContraCov`**

Symmetric to Step 1. Same template targeting the ContraCov namespace.

- [ ] **Step 3: Build**

```
lake build GebLean.Utilities.Grothendieck
```

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "$(cat <<'EOF'
Add mkHom_id theorem to two-sided Grothendieck API namespaces

Expresses identity morphisms via the mkHom constructor, enabling
subsequent map_id proofs for the Cat-level forward / backward
functors to close by simp + the existing API lemmas.

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 3: `mkHom_comp` in both namespaces

**Goal:** Prove the composition law for `mkHom` — the Lucyshyn-Wright formula `a*(y) ⋅ d!(x)` — in each namespace.

- [ ] **Step 1: Add `mkHom_comp` to `TwoSidedGrothendieckCovContra`**

Insert:

```lean
/-- Composition of `mkHom`-constructed morphisms in the covariant-
then-contravariant two-sided Grothendieck, following the Lucyshyn-
Wright formula `(c ⋅ a, d ⋅ b, a*(y) ⋅ d!(x))`. -/
theorem mkHom_comp {H : Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}}
    {x y z : (twoSidedGrothendieckCovContra.obj H).left}
    (β₁ : objD x ⟶ objD y) (α₁ : objC x ⟶ objC y)
    (φ₁ : ((H.obj (Opposite.op (objD x))).map α₁).toFunctor.obj
        (objFiber x) ⟶
      ((H.map β₁.op).app (objC y)).toFunctor.obj (objFiber y))
    (β₂ : objD y ⟶ objD z) (α₂ : objC y ⟶ objC z)
    (φ₂ : ((H.obj (Opposite.op (objD y))).map α₂).toFunctor.obj
        (objFiber y) ⟶
      ((H.map β₂.op).app (objC z)).toFunctor.obj (objFiber z)) :
    mkHom β₁ α₁ φ₁ ≫ mkHom β₂ α₂ φ₂ =
      mkHom (β₁ ≫ β₂) (α₁ ≫ α₂)
        (/- Lucyshyn-Wright composed φ: α₂!(φ₁) then β₁*(φ₂),
            with eqToHom for coherence across α₁≫α₂ and β₁≫β₂
            functoriality -/
         eqToHom (by simp [Functor.map_comp]) ≫
         ((H.obj (Opposite.op (objD x))).map α₂).toFunctor.map φ₁ ≫
         eqToHom (by simp) ≫
         ((H.map β₁.op).app (objC z)).toFunctor.map φ₂ ≫
         eqToHom (by simp)) := by
  -- Unfold mkHom (which uses Quiver.Hom.op on explicit data).
  -- Apply Grothendieck composition (Grothendieck.comp_fiber with
  -- eqToHom) at the two layers.
  sorry -- invoke lean4:sorry-filler-deep
```

**Note to implementer:** The exact eqToHom coercions in the RHS will likely need iteration. The KEY IS:
1. The LHS and RHS both have type `mkObj ... ⟶ mkObj ...` in the two-sided Cat.
2. The RHS expresses the fibre morphism as Lucyshyn-Wright's explicit formula.
3. Any valid construction of the RHS that makes the proof go through is acceptable. The RHS isn't used elsewhere directly — only as a simp target.

If the initial form above doesn't work, dispatch `lean4:sorry-filler-deep` and let it find a valid RHS + proof. Alternative forms to consider:
- Rearrange the `eqToHom` placement.
- Swap the order of `β` transport and `α` transport (mathematically they commute by bifunctoriality + naturality).

- [ ] **Step 2: Add `mkHom_comp` to `TwoSidedGrothendieckContraCov`**

Symmetric. Same shape of formula, different underlying encoding.

- [ ] **Step 3: Build**

```
lake build GebLean.Utilities.Grothendieck
```

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "$(cat <<'EOF'
Add mkHom_comp theorem (Lucyshyn-Wright composition formula)

Proves the explicit Lucyshyn-Wright composition formula for
mkHom-constructed morphisms in both two-sided Grothendieck API
namespaces.  This completes the composition-level API needed for
the Cat-level forward/backward functors' map_comp proofs.

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 4: Forward and backward Cat functors

**Goal:** Build `twoSidedGrothendieckEquiv.forward` and `.backward` as full Cat functors with `map_id` and `map_comp`, using the API theorems.

- [ ] **Step 1: Define `twoSidedGrothendieckEquiv.forward`**

Replace (or extend) the existing `forwardObj` / `forwardMap` primitives with:

```lean
/-- Forward Cat functor for the equivalence between the two
orderings of the strict two-sided Grothendieck at a fixed
bifunctor `H`.  Built by composing CovContra-destructors with
ContraCov-constructors, so the data reshuffle is transparent
and functoriality reduces to API-level theorems. -/
def twoSidedGrothendieckEquiv.forward
    (H : Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}) :
    ((twoSidedGrothendieckCovContra.obj H).left : Cat) ⥤
      ((twoSidedGrothendieckContraCov.obj H).left : Cat) where
  obj x := TwoSidedGrothendieckContraCov.mkObj
    (TwoSidedGrothendieckCovContra.objD x)
    (TwoSidedGrothendieckCovContra.objC x)
    (TwoSidedGrothendieckCovContra.objFiber x)
  map {x y} f := TwoSidedGrothendieckContraCov.mkHom
    (TwoSidedGrothendieckCovContra.homD f)
    (TwoSidedGrothendieckCovContra.homC f)
    (TwoSidedGrothendieckCovContra.homFiber f)
  map_id x := by
    -- mkHom with identity-shaped arguments = identity morphism
    -- at the target.  Use mkHom_id of ContraCov + homD_id /
    -- homC_id / homFiber_id of CovContra.
    simp only [TwoSidedGrothendieckCovContra.homD_id,
      TwoSidedGrothendieckCovContra.homC_id,
      TwoSidedGrothendieckCovContra.homFiber_id]
    exact (TwoSidedGrothendieckContraCov.mkHom_id _).symm
  map_comp {x y z} f g := by
    -- mkHom with composition-shaped arguments = mkHom ≫ mkHom
    -- at the target.  Use mkHom_comp of ContraCov + homD_comp /
    -- homC_comp / homFiber_comp of CovContra.
    simp only [TwoSidedGrothendieckCovContra.homD_comp,
      TwoSidedGrothendieckCovContra.homC_comp,
      TwoSidedGrothendieckCovContra.homFiber_comp]
    rw [TwoSidedGrothendieckContraCov.mkHom_comp]
    -- Any residual eqToHom bookkeeping should simp out.
    simp
```

**Note:** The proof body sketches the expected flow. If `simp` / `rw` don't close exactly as written, invoke `lean4:sorry-filler-deep` or iterate. The goal structure is deterministic.

- [ ] **Step 2: Define `twoSidedGrothendieckEquiv.backward`**

Symmetric. Source is ContraCov, target is CovContra; destructors are ContraCov's, constructors are CovContra's.

- [ ] **Step 3: Build**

```
lake build GebLean.Utilities.Grothendieck
```

- [ ] **Step 4: Remove the now-obsolete `forwardObj` / `forwardMap` / `backwardObj` / `backwardMap` primitives.**

These are subsumed by the full Cat functors.

- [ ] **Step 5: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "$(cat <<'EOF'
Define twoSidedGrothendieckEquiv.forward and .backward Cat functors

Full Cat functors with map_id and map_comp proven via the API-level
theorems (mkHom_id, mkHom_comp) and destructor simp lemmas (homD_id,
homC_id, homD_comp, homC_comp, homFiber_id, homFiber_comp).  Each
proof obligation is a two-layer reduction, avoiding the three-layer
eqToHom tangle that blocked earlier direct attempts.

Removes the superseded forwardObj/forwardMap/backwardObj/backwardMap
primitives.

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 5: Unit and counit isos

**Goal:** Show that `forward ⋙ backward ≅ 𝟭` and `backward ⋙ forward ≅ 𝟭`, completing the data for a `CategoryTheory.Equivalence`.

- [ ] **Step 1: Prove `forward ⋙ backward = 𝟭` by `rfl` or simple `Functor.ext`**

Insert:

```lean
/-- The roundtrip `forward ⋙ backward` is the identity functor on
the covariant-then-contravariant two-sided Grothendieck category.
This holds by structure eta of `Opposite` and `Grothendieck`. -/
theorem twoSidedGrothendieckEquiv.forward_backward_eq
    (H : Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}) :
    twoSidedGrothendieckEquiv.forward H ⋙
        twoSidedGrothendieckEquiv.backward H =
      𝟭 _ := by
  -- Object roundtrip: mkObj (objD (mkObj d c y)) ... = mkObj d c y
  -- which simp-reduces to x via objD_mkObj etc., then mkObj (objD x)
  -- (objC x) (objFiber x) = x by structure eta.
  -- Map roundtrip: similar.
  apply Functor.ext
  · intro x y f
    simp [twoSidedGrothendieckEquiv.forward,
      twoSidedGrothendieckEquiv.backward]
  · intro x
    -- should be rfl or close (structure eta)
    rfl
```

If this doesn't close, the object roundtrip likely DOES hold by rfl (our `twoSidedGrothendieckObjEquiv` already proves this), but the morphism roundtrip requires the API lemmas. Invoke `lean4:sorry-filler-deep` if stuck.

- [ ] **Step 2: Derive `unitIso`**

If the functor equality holds:

```lean
/-- Unit iso for the two-sided Grothendieck equivalence:
`𝟭 _ ≅ forward ⋙ backward`. -/
def twoSidedGrothendieckEquiv.unitIso
    (H : Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}) :
    𝟭 _ ≅ twoSidedGrothendieckEquiv.forward H ⋙
      twoSidedGrothendieckEquiv.backward H :=
  eqToIso (twoSidedGrothendieckEquiv.forward_backward_eq H).symm
```

- [ ] **Step 3: Prove `backward ⋙ forward = 𝟭` similarly**

```lean
theorem twoSidedGrothendieckEquiv.backward_forward_eq
    (H : Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}) :
    twoSidedGrothendieckEquiv.backward H ⋙
        twoSidedGrothendieckEquiv.forward H =
      𝟭 _ := by
  apply Functor.ext
  · intro x y f
    simp [twoSidedGrothendieckEquiv.forward,
      twoSidedGrothendieckEquiv.backward]
  · intro x
    rfl
```

- [ ] **Step 4: Derive `counitIso`**

```lean
def twoSidedGrothendieckEquiv.counitIso
    (H : Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}) :
    twoSidedGrothendieckEquiv.backward H ⋙
      twoSidedGrothendieckEquiv.forward H ≅ 𝟭 _ :=
  eqToIso (twoSidedGrothendieckEquiv.backward_forward_eq H)
```

- [ ] **Step 5: Build**

```
lake build GebLean.Utilities.Grothendieck
```

- [ ] **Step 6: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "$(cat <<'EOF'
Add unit/counit isos for the two-sided Grothendieck equivalence

Proves forward ⋙ backward = 𝟭 and backward ⋙ forward = 𝟭 as
functor equalities (both via Functor.ext + structure eta), then
packages as isos for the CategoryTheory.Equivalence record.

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 6: Assemble `CategoryTheory.Equivalence`

**Goal:** Package forward, backward, unitIso, counitIso into a full `CategoryTheory.Equivalence` per `H`.

- [ ] **Step 1: Define `twoSidedGrothendieckEquivalence`**

Insert:

```lean
/-- The full equivalence of categories between the two orderings
of the strict two-sided Grothendieck at a fixed bifunctor `H`.

This confirms the two compositional realizations produce the same
Lucyshyn-Wright construction up to a canonical equivalence of
categories.
-/
def twoSidedGrothendieckEquivalence
    (H : Dᵒᵖ ⥤ C ⥤ Cat.{v_sp, u_sp}) :
    ((twoSidedGrothendieckCovContra.obj H).left : Cat) ≌
      ((twoSidedGrothendieckContraCov.obj H).left : Cat) where
  functor := twoSidedGrothendieckEquiv.forward H
  inverse := twoSidedGrothendieckEquiv.backward H
  unitIso := twoSidedGrothendieckEquiv.unitIso H
  counitIso := twoSidedGrothendieckEquiv.counitIso H
  functor_unitIso_comp := by
    -- Required coherence: standard for equivalences built from
    -- strict equalities; should close via simp or aesop_cat.
    intro x
    simp [twoSidedGrothendieckEquiv.unitIso,
      twoSidedGrothendieckEquiv.counitIso, eqToIso]
```

If the `functor_unitIso_comp` proof doesn't close cleanly, invoke `lean4:sorry-filler-deep`. This is standard for an equivalence built from strict-equality roundtrips.

- [ ] **Step 2: Update the docstring of `twoSidedGrothendieckContraCov`**

Find the docstring ending "A full equivalence of categories is not provided here." and update to refer to `twoSidedGrothendieckEquivalence`.

- [ ] **Step 3: Build and test**

```
lake build && lake test
```

- [ ] **Step 4: Verify axiom hygiene**

```bash
grep -c "sorry\|admit\|axiom " GebLean/Utilities/Grothendieck.lean
```
Expected: only the pre-existing "admits" in an unrelated docstring (so count should equal the baseline count; confirm none of them are `sorry`, `admit`, or a custom `axiom` declaration).

- [ ] **Step 5: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "$(cat <<'EOF'
Add twoSidedGrothendieckEquivalence per-bifunctor equivalence

Packages forward / backward / unitIso / counitIso into a full
CategoryTheory.Equivalence between the two orderings of the
strict two-sided Grothendieck at each bifunctor H.  Closes the
equivalence goal specified in the design spec.

Updates twoSidedGrothendieckContraCov docstring accordingly.

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

---

## Task 7: Update session notes and close out

**Goal:** Document completion; prepare for potential follow-up work (pseudonatural equivalence / naturality in H).

- [ ] **Step 1: Update `.session/workstreams/two-sided-grothendieck-equivalence.md`**

Replace the "Partial" status with "Complete — per-bifunctor equivalence proven". Keep notes on potential follow-up (naturality in H via pseudofunctor framework) as a "possible future extension" section.

Target content for the updated file:

```markdown
# Two-Sided Grothendieck: Equivalence Between Orderings

## Status

**Complete** (per-bifunctor equivalence).

The two orderings `twoSidedGrothendieckCovContra` and
`twoSidedGrothendieckContraCov` are equivalent as categories at
each bifunctor `H : Dᵒᵖ ⥤ C ⥤ Cat`, witnessed by
`twoSidedGrothendieckEquivalence H`.

## What's done

- Object-level type `Equiv` (`twoSidedGrothendieckObjEquiv`) with
  `rfl` roundtrips.
- Symmetric constructor/destructor API namespaces
  (`TwoSidedGrothendieckCovContra` and
  `TwoSidedGrothendieckContraCov`) with matching type signatures.
- Complete API-level composition lemma set: `homD_id`, `homC_id`,
  `homFiber_id`, `homD_comp`, `homC_comp`, `homFiber_comp`,
  `mkHom_id`, `mkHom_comp` in each namespace.
- `twoSidedGrothendieckEquiv.forward` and `.backward` Cat functors.
- Unit and counit isos from `Functor.ext` + structure eta.
- `twoSidedGrothendieckEquivalence H` — the full equivalence.

## Possible future extensions

- **Naturality in H** (pseudonatural equivalence): express the
  family of `twoSidedGrothendieckEquivalence H` as a natural
  transformation-like structure functorially in H.  Likely
  requires promoting both constructions to pseudofunctors and
  using mathlib's `CategoryTheory.Bicategory.NaturalTransformation.Pseudo.StrongTrans`.
- **Strict natural iso** between the functors as Cat-valued
  functors: would require strict isos of Cat objects, which is
  stronger than equivalence and likely not achievable in this
  setting.

## Related files

- `GebLean/Utilities/Grothendieck.lean`, `StrictTwoSidedGrothendieck`
  section.
- `docs/two-sided-grothendieck-construction.md`.
- `docs/superpowers/specs/2026-04-13-strict-two-sided-grothendieck-design.md`.
- `docs/superpowers/plans/2026-04-13-strict-two-sided-grothendieck.md`.
- `docs/superpowers/plans/2026-04-14-two-sided-grothendieck-equivalence.md`
  (this plan).
```

- [ ] **Step 2: Commit session notes**

```bash
git add .session/workstreams/two-sided-grothendieck-equivalence.md
git commit -m "$(cat <<'EOF'
Mark two-sided Grothendieck equivalence workstream complete

Per-bifunctor equivalence is now in place.  Naturality in H
via pseudofunctor framework noted as possible future extension.

Co-Authored-By: Claude Opus 4.6 (1M context) <noreply@anthropic.com>
EOF
)"
```

- [ ] **Step 3: Final build + test sweep**

```
lake build && lake test
```

All green confirms the workstream is done.

---

## Fallback protocol (applies throughout)

If any proof obligation resists standard tactics (`simp`, `rfl`, `aesop_cat`, explicit rewrites), follow this escalation ladder:

1. **Check tactic state** via `mcp__lean-lsp__lean_goal` to understand the unfinished shape.
2. **Try targeted simp sets** using only the directly-relevant API lemmas: `simp only [homD_id, homC_id, ...]`.
3. **Invoke `lean4:sorry-filler-deep`** via the Agent tool with specific context: file path, line range, what the proof needs to show, and lemmas you've already identified.
4. **If `sorry-filler-deep` reports stuck**, reconsider the RHS of the theorem — maybe a different-but-equivalent formulation is easier to prove.
5. **Last resort**: report BLOCKED and escalate to the human with a specific blocker description.

Never commit with a `sorry`. Never add an `axiom`.

## Success criteria

At completion:
- `lake build && lake test` green.
- `twoSidedGrothendieckEquivalence` defined and public.
- `.session/workstreams/two-sided-grothendieck-equivalence.md` updated to "Complete".
- All tasks' commits on `terence/grothendieck` branch.
- No `sorry`/`admit`/custom axiom anywhere in the modified section.
- Only standard axioms in use.
