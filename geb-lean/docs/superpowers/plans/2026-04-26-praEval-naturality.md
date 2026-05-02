# `praEval*` Naturality in `(I, J)` Implementation Plan (SUPERSEDED)

> **Status: SUPERSEDED 2026-04-26.**  This plan was partially
> executed (commits `81a0369f` through `d701b401`) before
> implementation hit a variance mismatch and was scoped down to
> fixed `I`.  Source-side commits were reverted in
> `c2672b92`; target-side and `FunctorBetweenContraContra`
> framework commits were kept.  See the superseded design
> `docs/superpowers/specs/2026-04-26-praEval-naturality-design.md`
> for the full analysis, and
> `docs/superpowers/plans/2026-04-26-praEvalAtI-naturality.md`
> for the realised fixed-`I` plan.
>
> Do NOT execute this plan.  The full `(I, J)`-natural design
> will be redone in a future brainstorm.

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Lift `praEvalAtFunctor` to a natural-in-`(I, J)` form
`praPolyEvalFunctor` built as a flat functor between Grothendieck
constructions, mirroring the praDirections v2 pattern.

**Architecture:** Add a new U3 framework
`FunctorBetweenContraContra` in
`GebLean/Utilities/Grothendieck.lean` (parallel to the existing
`FunctorBetweenCovContra`), then build `praPolyEvalFunctor` on
top of it.  The new framework encodes a covariant flat functor
between two contra-Grothendiecks, which is the right shape for
the praEval naturality (source contravariant in `(J, I, P)`
because of presheaves' contravariance in `I`).  The source
fibre is constant in `P` (encoded via `Functor.const`).
Target Grothendieck and bridge lemmas mirror praDirections's
structure.

**Tech Stack:** Lean 4, mathlib (category theory, Grothendieck
construction, presheaf categories).  Project rules from `CLAUDE.md`
apply throughout (no `sorry`/`admit`/`axiom`/`noncomputable`/
`classical`, lines ≤80, no forbidden style words, `lake build` +
`lake test` clean with zero warnings before each commit).

**Spec:**
`docs/superpowers/specs/2026-04-26-praEval-naturality-design.md`

---

## File Structure

| File | Tasks touched |
| ---- | ------------- |
| `GebLean/Utilities/Grothendieck.lean` | A1, A2, A3 |
| `GebLean/PresheafPRA.lean` | 1–17, 18, 19, 20 |
| `GebLeanTests/Utilities/PresheafPRAEvalNat.lean` | 21 (create), 22, 23, 24 |
| `GebLeanTests.lean` | 22 (register) |
| `.session/workstreams/presheaf-pra.md` | 25 |

Per-task summary:

- Tasks A1–A3 (NEW, framework): U3 abbrevs, structure, extractor
  for `FunctorBetweenContraContra`.
- Tasks 1–2: target Grothendieck (`praEvalTargetFibre`,
  `praPolyEvalTarget`) — already committed.
- Tasks 3–7 (REVISED): source data + source contra-Grothendieck.
- Tasks 8–15: bundle field helpers (`praPolyEvalData_*`).
- Tasks 16–17: bundle assembly + functor extraction.
- Task 18: three `rfl` bridge lemmas.
- Tasks 19–20: source-object helper + bridge theorem + test.
- Tasks 21–24: test file with five test sections.
- Task 25: workstream notes update.

**Status note**: Tasks 1 (commit `81a0369f`) and 2 (commit
`f9859d89`) were committed before the variance-flip revision.
They remain valid because the target Grothendieck shape is
unchanged.  Tasks 3 onwards have been revised; see Phase A
(below) and the revised Tasks 3–7.

---

## Revision History

**2026-04-26 — variance flip**: original plan used
`FunctorBetweenCovContra` framework with a covariant source
Grothendieck.  Rejected after Task 3 hit a fundamental variance
issue (presheaves are contravariant in `I`, so `Z`'s natural
variance under an `I`-morphism is BACKWARD, forcing the source
Grothendieck to be CONTRAVARIANT in `(J, I, P)`).  Resolution:
added new U3 framework `FunctorBetweenContraContra` (Tasks
A1–A3 below).  The wrong-direction Task 3 (commit `21a625f7`)
was reverted in `4203253f`.

**2026-04-26 — target `Cat.opFunctor` removal**: original
`praEvalTargetFibre` mirrored `praDirectionsTargetFibre`'s
three-stage pipeline including `Cat.opFunctor`.  Rejected when
Task 9 (`fibFib`) found that polynomial-functor *evaluation* is
COVARIANT in `Z`, so the result-side variance matches presheaves'
natural contravariance directly.  Resolution: dropped final
`Cat.opFunctor` stage; target fibre is now `presheafCatFunctor ⋙
catULiftFunctor2` (commit `d789a2ac`).

**Status (session pause 2026-04-26)**:

DONE:

- Tasks A1–A3: framework (`64162066`, `774ee96e`, `d9d08504`).
- Tasks 1–2: target side (`81a0369f`, `f9859d89`, with fix
  `d789a2ac`).
- Tasks 3+4 (collapsed): source side (`46923c37`).
- Task 8: `praPolyEvalData_baseFib` (`f0f1f208`).
- Task 9: `praPolyEvalData_fibFib` (`d701b401`).

REMAINING:

- Tasks 10–14: cross-fibre + coherence proofs.
- Task 15: bundle assembly.
- Task 16: `praPolyEvalFunctor`.
- Task 17: three `rfl` bridge lemmas.
- Task 18: `praPolyEvalAtSourceObj` helper.
- Task 19: bridge theorem + test.
- Tasks 20–25: tests + workstream notes.

The revised tasks below incorporate the framework name change
(`FunctorBetweenContraContraData` instead of
`FunctorBetweenCovContraData`), the
`FunctorBetweenContraContraFibHomCrossApp` shape change
(target-side `x'` input rather than source-side `x`), and the
target-fibre `Cat.opFunctor` removal.

The original Tasks 3–7 below are SUPERSEDED by the collapsed
Tasks 3+4 already committed.

---

## Task A1: Add `FunctorBetweenContraContra` U3 abbrevs

**Files:**

- Modify: `GebLean/Utilities/Grothendieck.lean` — add a new
  section parallel to the existing `FunctorBetweenCovContra`
  section (lines 5155–5328).

- [ ] **Step 1: Read the existing CovContra abbrevs**

Read `Utilities/Grothendieck.lean` lines 5155–5328 to internalise
the patterns for `FunctorBetweenCovContraBaseFib`,
`FibFib`, `FibHomCrossApp`, `FibHomCrossNat`,
`BaseHomEqId`/`BaseHomEqIdProof`, `BaseHomEqComp`/
`BaseHomEqCompProof`, `BaseHomId`, `BaseHomComp`.

- [ ] **Step 2: Add the parallel ContraContra abbrevs**

Insert a new section after `end FunctorBetweenCovContra`
(currently line 5328):

```lean
section FunctorBetweenContraContra

universe vC vD uC uD vT uT

variable {C : Type uC} [Category.{vC} C] (G : Cᵒᵖ ⥤ Cat.{vT, uT})
variable {D : Type uD} [Category.{vD} D] (F : Dᵒᵖ ⥤ Cat.{vT, uT})

/--
The base-fibre functor for the contra-contra case: `C ⥤ D`.
-/
abbrev FunctorBetweenContraContraBaseFib := C ⥤ D

/--
The fibre-fibre functor: for each `c : C`, a functor
`G.obj (op c) ⥤ F.obj (op (baseFib.obj c))`.
-/
abbrev FunctorBetweenContraContraFibFib
    (baseFib : FunctorBetweenContraContraBaseFib (C := C)
      (D := D)) :=
  ∀ c, G.obj (Opposite.op c) ⥤
    F.obj (Opposite.op (baseFib.obj c))
```

For the cross-fibre and coherence abbrevs, work out the right
shapes using these guiding facts:

- A morphism in `(grothendieckContraFunctor C).obj G` from
  `(c, x)` to `(c', x')` decomposes via `homBase` (`c ⟶ c'` in
  `C`) and `homFiber` (`x ⟶ (G.map (homBase _).op).obj x'`).
- Similarly on the target side.
- The cross-fibre app for `f : c ⟶ c'` and `x' ∈ G.obj (op c')`:
  produces a morphism from `(fibFib c).obj ((G.map f.op).obj x')`
  to `(F.map (baseFib.map f).op).obj ((fibFib c').obj x')`.
- Naturality, identity, and composition coherence follow the
  CovContra patterns adjusted for the source-side variance.

If a particular abbrev's shape is unclear, write the unfolded
`∀`-form as a working version and refine later.

- [ ] **Step 3: Build**

Run: `lake build`.  Expected: clean.

- [ ] **Step 4: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "grothendieck: add FunctorBetweenContraContra abbrevs"
```

(No `Co-Authored-By` trailer.)

---

## Task A2: Add `FunctorBetweenContraContraData` structure

**Files:**

- Modify: `GebLean/Utilities/Grothendieck.lean` — add the
  bundle structure inside the section started in Task A1.

- [ ] **Step 1: Add the structure**

Mirror `FunctorBetweenCovContraData` (lines 5310–5326).  Six
fields: `baseFib`, `fibFib`, `fibHomCrossApp`, `fibHomCrossNat`,
`baseHomId`, `baseHomComp`.

```lean
structure FunctorBetweenContraContraData where
  baseFib : FunctorBetweenContraContraBaseFib (C := C) (D := D)
  fibFib : FunctorBetweenContraContraFibFib G F baseFib
  fibHomCrossApp :
    FunctorBetweenContraContraFibHomCrossApp G F baseFib fibFib
  fibHomCrossNat :
    FunctorBetweenContraContraFibHomCrossNat G F baseFib fibFib
      fibHomCrossApp
  baseHomId :
    FunctorBetweenContraContraBaseHomId G F baseFib fibFib
      fibHomCrossApp
  baseHomComp :
    FunctorBetweenContraContraBaseHomComp G F baseFib fibFib
      fibHomCrossApp

end FunctorBetweenContraContra
```

- [ ] **Step 2: Build**

Run: `lake build`.

- [ ] **Step 3: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "grothendieck: add FunctorBetweenContraContraData structure"
```

(No `Co-Authored-By` trailer.)

---

## Task A3: Add `FunctorBetweenContraContra.toFunctor` extractor

**Files:**

- Modify: `GebLean/Utilities/Grothendieck.lean` — add a new
  extractor section parallel to lines 7370–7659.

- [ ] **Step 1: Read the existing extractor**

Read `Utilities/Grothendieck.lean` lines 7370–7659 (the
`FunctorBetweenCovContraData.toFunctor` extractor) to internalise
the structure: `toBaseFunc`, `toFib`, `toHomUnop`, `toHomUnop_id`,
`toHomUnop_comp`, `toFunctorToData`, `toFunctor`.

- [ ] **Step 2: Add the parallel extractor**

Define analogs that produce
`(grothendieckContraFunctor C).obj G ⥤ (grothendieckContraFunctor
D).obj F` instead of `Grothendieck G ⥤ ...`.

The internal mechanics will likely use `Grothendieck.functorTo`
on a suitably op-shifted source plus appropriate `.leftOp`/
`.rightOp` adjustments.  If the construction proves complex,
factor smaller helpers, parallel to the CovContra extractor's
pattern of `toHomUnop_id_fst`, `toHomUnop_id_snd`,
`toHomUnop_comp_endpoints_eq`, etc.

The proof of `toHomUnop_comp` in CovContra is the heaviest
part; expect a similar proof for ContraContra.

- [ ] **Step 3: Build**

Run: `lake build`.

- [ ] **Step 4: Run tests**

Run: `lake test`.

- [ ] **Step 5: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "grothendieck: add FunctorBetweenContraContraData.toFunctor"
```

(No `Co-Authored-By` trailer.)

---

## Task 1: Define `praEvalTargetFibre`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after the last existing
  praDirections-related declaration in `section PresheafPRADef`,
  before the section ends.

- [ ] **Step 1: Add the definition**

```lean
/--
Per-`J` target fibre for `praPolyEvalTarget`.  Three-stage pipeline
`presheafCatFunctor ⋙ catULiftFunctor2 ⋙ Cat.opFunctor`, mirroring
`praDirectionsTargetFibre`.  Sends each `J : Catᵒᵖ` to the
universe-widened `op (Jᵒᵖ ⥤ Type w')` Cat — the codomain Cat for
the polynomial-functor evaluation result.
-/
def praEvalTargetFibre :
    Cat.{v_J, u_J}ᵒᵖ ⥤
      Cat.{max u_I u_J v_I w_I w',
        max u_I u_J v_I v_J (w_I + 1) (w' + 1)} :=
  presheafCatFunctor.{u_J, v_J, w'} ⋙
    catULiftFunctor2.{max v_J (w' + 1) u_J, max u_J w',
      max u_I u_J v_I w_I w',
      max u_I u_J v_I v_J (w_I + 1) (w' + 1)} ⋙
    Cat.opFunctor.{max u_I u_J v_I w_I w',
      max u_I u_J v_I v_J (w_I + 1) (w' + 1)}
```

The universe annotations mirror `praDirectionsTargetFibre`'s pattern
but with `J`-universes substituted for `I`-universes.  Verify the
exact widening universes via `mcp__lean-lsp__lean_hover_info` on
`praDirectionsTargetFibre` and adjust to match the `J`-side.

- [ ] **Step 2: Build**

Run: `lake build`.  Expected: clean.  If a universe error appears,
adjust the annotations using LSP-revealed types.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praEvalTargetFibre"
```

(No `Co-Authored-By` trailer.)

---

## Task 2: Define `praPolyEvalTarget`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert immediately after
  `praEvalTargetFibre`.

- [ ] **Step 1: Add the definition**

```lean
/--
Total target Grothendieck for `praPolyEvalFunctor`.

Objects are pairs `(J, x)` where `x : (widened Jᵒᵖ ⥤ Type w')ᵒᵖ`.
Morphisms `(J₁, x₁) ⟶ (J₂, x₂)` are pairs `(f : J₁ ⟶ J₂,
η : x₁ ⟶ (praEvalTargetFibre.map f.op).obj x₂)`, encoding the
polynomial-functor evaluation result's contravariant convention
on `J`.
-/
def praPolyEvalTarget :
    Cat.{max u_I u_J v_I v_J w_I w',
      max u_I (u_J + 1) v_I (v_J + 1) (w_I + 1) (w' + 1)} :=
  (grothendieckContraFunctor Cat.{v_J, u_J}).obj
    praEvalTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'}
```

The universe annotations mirror `praPolyDirectionsTarget` with
`J`-universes substituted for `I`-universes.  Adjust based on
LSP errors.

- [ ] **Step 2: Build**

Run: `lake build`.  Expected: clean.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalTarget"
```

(No `Co-Authored-By` trailer.)

---

## Task 3: Define `evalSourceDataFib`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after `praPolyEvalTarget`.

**Context:** `evalSourceDataFib (JI : Cat × Cat)` returns a functor
`presheafPRACatBifunctorUncurriedOp.obj (op JI) ⥤ Cat` that's
*constant in `P`*.  The constant value is the universe-widened
`presheafCat.{u_I, v_I, w_I}.obj (op I)`.  This factors out the
fibre-side Cat for the source Grothendieck.

- [ ] **Step 1: Add the definition**

```lean
/--
Per-`(J, I)` fibre functor for `evalSourceData`.  Constant in `P`:
sends every PRA at `(I, J)` to the universe-widened presheaf-on-`I`
Cat.

The constant target Cat is
`catULiftFunctor2.obj (presheafCatFunctor.obj (op JI.2))`, the
same widening pipeline used by `sourceDataFib` for the praDirections
elements category — except here the input is `presheafCat I`
itself rather than `(P ⋙ ccrNewIndexFunctor _).Elements`.
-/
private def evalSourceDataFib
    (JI : Cat.{v_J, u_J} × Cat.{v_I, u_I}) :
    ↑(presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'}.obj (Opposite.op JI)) ⥤
      Cat.{max u_I u_J v_I w_I w',
        max u_I u_J v_I v_J (w_I + 1) (w' + 1)} :=
  Functor.const _
    (catULiftFunctor2.{max v_I (w_I + 1) u_I, max u_I w_I,
      max u_I u_J v_I w_I w',
      max u_I u_J v_I v_J (w_I + 1) (w' + 1)}.obj
      (presheafCatFunctor.{u_I, v_I, w_I}.obj
        (Opposite.op JI.2)))
```

The universe annotations match those of `praEvalTargetFibre`.
Adjust if LSP reveals different orderings.

- [ ] **Step 2: Build**

Run: `lake build`.  Expected: clean.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add evalSourceDataFib"
```

(No `Co-Authored-By` trailer.)

---

## Task 4: Define `evalSourceDataHomApp`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `evalSourceDataFib`.

**Context:** `evalSourceDataHomApp f P` is the per-`P` component of
the source-data homomorphism for an `(J, I)`-morphism `f`.  Since
the fibre is constant in `P`, this is essentially a single Cat-
morphism `widenedPSh(I_source) ⥤ widenedPSh(I_target)` (independent
of `P`), but to fit the `FunctorFromDataContra` interface it's
parameterized by `P`.

- [ ] **Step 1: Add the definition**

```lean
/--
Per-morphism component of `evalSourceData.hom`.  For
`f : JI₁ ⟶ JI₂` in `Cat × Cat` and `P : F.obj (op JI₂)`, the
functor `(evalSourceDataFib JI₁).obj _ ⟶ (evalSourceDataFib JI₂)
.obj P`.  Independent of `P` because the fibre is constant.

The underlying Cat-morphism widens `presheafCatFunctor.map f_I.op`
through `catULiftFunctor2`.
-/
private def evalSourceDataHomApp
    {JI₁ JI₂ : Cat.{v_J, u_J} × Cat.{v_I, u_I}} (f : JI₁ ⟶ JI₂)
    (P : ↑(presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'}.obj (Opposite.op JI₂))) :
    (evalSourceDataFib.{u_I, v_I, u_J, v_J, w_I, w'} JI₁).obj
        ((presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
          w_I, w'}.map f.op).toFunctor.obj P) ⟶
      (evalSourceDataFib.{u_I, v_I, u_J, v_J, w_I, w'} JI₂).obj P :=
  (catULiftFunctor2.{max v_I (w_I + 1) u_I, max u_I w_I,
    max u_I u_J v_I w_I w',
    max u_I u_J v_I v_J (w_I + 1) (w' + 1)}.map
    (presheafCatFunctor.{u_I, v_I, w_I}.map
      (Opposite.op f.2))).toCatHom
```

Note: `f : JI₁ ⟶ JI₂` in `Cat × Cat` decomposes as `(f.1 : J₁ ⟶
J₂, f.2 : I₁ ⟶ I₂)`.  The I-component is `f.2`.  Apply
`presheafCatFunctor.map (op f.2) : presheafCat(I₁) ⥤ presheafCat(I₂)`
contravariantly, then widen.

If the universe annotations don't match, use LSP to discover
the correct order.

- [ ] **Step 2: Build**

Run: `lake build`.  Expected: clean.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add evalSourceDataHomApp"
```

(No `Co-Authored-By` trailer.)

---

## Task 5: Define `evalSourceDataHom`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `evalSourceDataHomApp`.

- [ ] **Step 1: Add `evalSourceDataHom`**

```lean
/--
Per-morphism natural-transformation component of `evalSourceData.hom`.
The `app` field is `evalSourceDataHomApp` (independent of `P`);
naturality is by `Cat.Hom.ext` then `rfl` because the underlying
Cat-morphism doesn't depend on `P`.
-/
private def evalSourceDataHom
    {JI₁ JI₂ : Cat.{v_J, u_J} × Cat.{v_I, u_I}} (f : JI₁ ⟶ JI₂) :
    (presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J, w_I,
      w'}.map f.op).toFunctor ⋙
      evalSourceDataFib.{u_I, v_I, u_J, v_J, w_I, w'} JI₁ ⟶
      evalSourceDataFib.{u_I, v_I, u_J, v_J, w_I, w'} JI₂ where
  app P := evalSourceDataHomApp.{u_I, v_I, u_J, v_J, w_I, w'} f P
  naturality _ _ _ := by
    apply Cat.Hom.ext
    rfl
```

- [ ] **Step 2: Build**

Run: `lake build`.  Expected: clean.

- [ ] **Step 3: Add `evalSourceData_hom_id`**

Insert immediately after `evalSourceDataHom`:

```lean
/--
Identity coherence for `evalSourceDataHom`.  Reduces to
functoriality of `presheafCatFunctor` and `catULiftFunctor2` at the
identity `(J, I)`-morphism, plus `Functor.const`-naturality at the
constant fibre value.
-/
private lemma evalSourceData_hom_id
    (JI : Cat.{v_J, u_J} × Cat.{v_I, u_I}) :
    evalSourceDataHom.{u_I, v_I, u_J, v_J, w_I, w'} (𝟙 JI) =
      eqToHom (by
        rw [show (𝟙 JI : JI ⟶ JI).op = 𝟙 (Opposite.op JI) from rfl]
        rw [presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
          w_I, w'}.map_id]
        rfl) := by
  apply NatTrans.ext
  funext P
  simp only [evalSourceDataHom, evalSourceDataHomApp,
    CategoryTheory.eqToHom_app]
  apply Cat.Hom.ext
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro _; rfl
  · intros _ _ _
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
```

(This mirrors `sourceData_hom_id` exactly; the proof should be
identical or near-identical.)

- [ ] **Step 4: Build**

Run: `lake build`.

- [ ] **Step 5: Add `evalSourceData_hom_comp`**

Insert immediately after `evalSourceData_hom_id`:

```lean
/--
Composition coherence for `evalSourceDataHom`.
-/
private lemma evalSourceData_hom_comp
    {JI₁ JI₂ JI₃ : Cat.{v_J, u_J} × Cat.{v_I, u_I}}
    (f : JI₁ ⟶ JI₂) (g : JI₂ ⟶ JI₃) :
    evalSourceDataHom.{u_I, v_I, u_J, v_J, w_I, w'} (f ≫ g) =
      eqToHom (by
        rw [show (f ≫ g : JI₁ ⟶ JI₃).op = g.op ≫ f.op from rfl]
        rw [presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
          w_I, w'}.map_comp]
        rfl) ≫
      Functor.whiskerLeft
        (presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
          w_I, w'}.map g.op).toFunctor
        (evalSourceDataHom.{u_I, v_I, u_J, v_J, w_I, w'} f) ≫
      evalSourceDataHom.{u_I, v_I, u_J, v_J, w_I, w'} g := by
  apply NatTrans.ext
  funext P
  simp only [evalSourceDataHom, evalSourceDataHomApp,
    CategoryTheory.eqToHom_app, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  apply Cat.Hom.ext
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro _; rfl
  · intros _ _ _
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl
```

- [ ] **Step 6: Build**

Run: `lake build`.  Expected: clean.

- [ ] **Step 7: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add evalSourceDataHom + identity/composition coherence"
```

(No `Co-Authored-By` trailer.)

---

## Task 6: Assemble `evalSourceData` bundle

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `evalSourceData_hom_comp`.

- [ ] **Step 1: Add the bundle**

```lean
/--
Source data for the `(I, J, P)`-natural form of polynomial-functor
evaluation.  Parallels `sourceData` but with a constant-in-`P`
fibre Cat (the widened presheaf-on-`I` Cat).
-/
private def evalSourceData :
    FunctorFromDataContra
      presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'}
      (T := Cat.{max u_I u_J v_I w_I w',
        max u_I u_J v_I v_J (w_I + 1) (w' + 1)}) where
  fib JI := evalSourceDataFib.{u_I, v_I, u_J, v_J, w_I, w'} JI
  hom f := evalSourceDataHom.{u_I, v_I, u_J, v_J, w_I, w'} f
  hom_id _ :=
    evalSourceData_hom_id.{u_I, v_I, u_J, v_J, w_I, w'} _
  hom_comp _ _ :=
    evalSourceData_hom_comp.{u_I, v_I, u_J, v_J, w_I, w'} _ _
```

- [ ] **Step 2: Build**

Run: `lake build`.  Expected: clean.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: assemble evalSourceData bundle"
```

(No `Co-Authored-By` trailer.)

---

## Task 7: Define `praPolyEvalSource`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `evalSourceData`.

- [ ] **Step 1: Add the definition**

```lean
/--
Total source Grothendieck for `praPolyEvalFunctor`.

Objects are 4-tuples: a base object of `(grothendieckContraFunctor
(Cat × Cat)).obj presheafPRACatBifunctorUncurriedOp` — a triple
`((J, I), P)` — together with a (widened) presheaf
`Z : Iᵒᵖ ⥤ Type w_I` on `I`.
-/
def praPolyEvalSource :
    Cat.{max u_I u_J v_I v_J w_I w',
      max u_I (u_J + 1) v_I (v_J + 1) (w_I + 1) (w' + 1)} :=
  Cat.of (Grothendieck
    (functorFromDataContra
      evalSourceData.{u_I, v_I, u_J, v_J, w_I, w'}))
```

- [ ] **Step 2: Build**

Run: `lake build`.  Expected: clean.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalSource"
```

(No `Co-Authored-By` trailer.)

---

## Task 8: Add `praPolyEvalData_baseFib`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyEvalSource`.

- [ ] **Step 1: Add the definition**

```lean
/--
Base functor of `praPolyEvalData`.  Projects a source-base object
`((J, I), P)` to its `J`-component and a base morphism `f` to its
`J`-component `f.unop.base.unop.1`.
-/
private def praPolyEvalData_baseFib :
    (grothendieckContraFunctor
        (Cat.{v_J, u_J} × Cat.{v_I, u_I})).obj
      presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'} ⥤
      Cat.{v_J, u_J} where
  obj X := (GrothendieckContraFunctor.objBase X).1
  map f := (GrothendieckContraFunctor.homBase f).1
  map_id _ := rfl
  map_comp _ _ := rfl
```

- [ ] **Step 2: Build**

Run: `lake build`.  Expected: clean.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalData_baseFib"
```

(No `Co-Authored-By` trailer.)

---

## Task 9: Add `praPolyEvalData_fibFib` and `_unwidenFiber`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyEvalData_baseFib`.

**Context:** `fibFib X` for `X = ((J, I), P)` sends `Z` (a widened
presheaf on `I`) to `op widened (praEvalAtFunctor.obj P |>.obj Z)`.
Body unfolds via `ULiftHom.down ⋙ ULift.downFunctor` (unwiden Z),
then applies `(ccrNewEvalCatFunctor _).obj P` (the polynomial
functor at this P), then re-widens via `(ULift.upFunctor ⋙
ULiftHom.up).op`.

`praPolyEvalData_unwidenFiber X` is the projection from widened-Z
back to unwidened-Z, mirroring `praPolyDirectionsData_unwidenFiber`.

- [ ] **Step 1: Add `praPolyEvalData_fibFib`**

```lean
/--
Fibre functor of `praPolyEvalData` at a source-base object
`c = ((J, I), P)`.  Composes the inverse of `catULiftFunctor2`'s
widening on `Z` with `(ccrNewEvalCatFunctor _).obj P` (the
polynomial functor at this `P`), then post-composes with the `op`
of the `catULiftFunctor2` widening on the result side to land in
`praEvalTargetFibre.obj (op J)`.
-/
private def praPolyEvalData_fibFib
    (X : (grothendieckContraFunctor
        (Cat.{v_J, u_J} × Cat.{v_I, u_I})).obj
      presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'}) :
    (functorFromDataContra
        evalSourceData.{u_I, v_I, u_J, v_J, w_I, w'}).obj X ⥤
      praEvalTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'}.obj
        (Opposite.op
          (praPolyEvalData_baseFib.{u_I, v_I, u_J, v_J,
            w_I, w'}.obj X)) :=
  show CategoryTheory.ULiftHom
      (ULift
        ((presheafCatFunctor.{u_I, v_I, w_I}.obj
            (Opposite.op
              (GrothendieckContraFunctor.objBase X).2)) : Type _))
        ⥤ _ from
  CategoryTheory.ULiftHom.down ⋙
    CategoryTheory.ULift.downFunctor ⋙
    (ccrNewEvalCatFunctor.{max v_I u_I (w_I + 1), max u_I w_I, w'}
      (↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
        (Opposite.op
          (GrothendieckContraFunctor.objBase X).2)))).obj
      (GrothendieckContraFunctor.objFiber X) ⋙
    (CategoryTheory.ULift.upFunctor ⋙
      CategoryTheory.ULiftHom.up).op
```

If the inner type ascription doesn't typecheck, follow
`praPolyDirectionsData_fibFib`'s exact `show … ⥤ _ from …` pattern
and adjust.

- [ ] **Step 2: Build**

Run: `lake build`.  Expected: clean.  May need universe-annotation
adjustment.

- [ ] **Step 3: Add `praPolyEvalData_unwidenFiber`**

Insert immediately after `praPolyEvalData_fibFib`:

```lean
/--
Unwiden a widened source-fibre element of `praPolyEvalSource` back
to an unwidened presheaf on `I`.  The inverse of the
`catULiftFunctor2` widening used inside `evalSourceDataFib`.
-/
private def praPolyEvalData_unwidenFiber
    (X : (grothendieckContraFunctor
        (Cat.{v_J, u_J} × Cat.{v_I, u_I})).obj
      presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'}) :
    (functorFromDataContra
        evalSourceData.{u_I, v_I, u_J, v_J, w_I, w'}).obj X ⥤
      ↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
        (Opposite.op (GrothendieckContraFunctor.objBase X).2)) :=
  show CategoryTheory.ULiftHom
      (ULift
        ((presheafCatFunctor.{u_I, v_I, w_I}.obj
            (Opposite.op
              (GrothendieckContraFunctor.objBase X).2)) : Type _))
        ⥤ _ from
  CategoryTheory.ULiftHom.down ⋙
    CategoryTheory.ULift.downFunctor
```

- [ ] **Step 4: Build**

Run: `lake build`.  Expected: clean.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalData_fibFib and _unwidenFiber"
```

(No `Co-Authored-By` trailer.)

---

## Task 10: Add `praPolyEvalData_fibHomCrossUnwidened`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyEvalData_unwidenFiber`.

**Context:** Mirrors `praPolyDirectionsData_fibHomCrossUnwidened`.
For a source-mor `f : X₁ ⟶ X₂` and an unwidened Z (a presheaf on
`I_source`), constructs the unwidened cross-fibre morphism:
applies `(ccrNewMorphEval (homFiber f))` (the polynomial-functor-
morphism action) at the corresponding presheaf transport.

The exact body is LSP-discovered.  Likely shape:

```lean
(ccrNewEvalCatFunctor _).map (homFiber f) |>.app
  (transported Z)
```

with `(homFiber f) : objFiber X₁ ⟶ (F.map (homBase f).op).toFunctor.obj
(objFiber X₂)` providing the polynomial-functor-morphism, and the
`transported Z` coming from the `f_I.op`-precomposition.

- [ ] **Step 1: Insert with `_` placeholder body**

```lean
/--
Unwidened cross-fibre morphism underlying `fibHomCrossApp f x` for
a source-Grothendieck morphism `f : X₁ ⟶ X₂` and unwidened
fibre-element `Z` (a presheaf on `(objBase X₁).2`).

Built by applying `(ccrNewEvalCatFunctor _).map` to the
polynomial-functor-morphism `(homFiber f) : objFiber X₁ ⟶
((presheafPRACatBifunctorUncurriedOp.map (homBase f).op).toFunctor.obj
(objFiber X₂))`, then evaluating at the transported `Z`.
-/
private def praPolyEvalData_fibHomCrossUnwidened
    {X₁ X₂ : (grothendieckContraFunctor
        (Cat.{v_J, u_J} × Cat.{v_I, u_I})).obj
      presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'}}
    (f : X₁ ⟶ X₂)
    (Z : ↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
      (Opposite.op (GrothendieckContraFunctor.objBase X₁).2))) :
    _ ⟶ _ :=
  _
```

Build, inspect the surfaced expected types via
`mcp__lean-lsp__lean_goal`, and fill in:

- The endpoint types should be op-presheaves on `J_source` /
  `J_target` with appropriate widening.
- The body should apply `(ccrNewEvalCatFunctor _).map (homFiber f)`
  at the appropriate object.

If the structure proves more complex, factor a private aux
definition (mirror `praPolyDirectionsData_fibHomCrossNat_unwidened_aux`).

- [ ] **Step 2: Build and iterate**

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalData_fibHomCrossUnwidened"
```

(No `Co-Authored-By` trailer.)

---

## Task 11: Add `praPolyEvalData_fibHomCrossApp` (widened)

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyEvalData_fibHomCrossUnwidened`.

**Context:** Widens the unwidened morphism through `(ULift.upFunctor
⋙ ULiftHom.up).op`.  Mirrors
`praPolyDirectionsData_fibHomCrossApp`.

- [ ] **Step 1: Add the definition**

```lean
/--
Cross-fibre morphism for `praPolyEvalData`.  Widens
`praPolyEvalData_fibHomCrossUnwidened` through `(ULift.upFunctor ⋙
ULiftHom.up).op`.  Endpoint objects coincide with `(fibFib X₁).obj
Z` and `(F.map _).obj ((fibFib X₂).obj ((G.map f).obj Z))` on the
nose, mirroring the `fibHomCrossApp` situation in praDirections.

Stated in the fully-unfolded `∀` form because direct application
of `FunctorBetweenCovContraFibHomCrossApp` gets stuck on universe
unification.
-/
private def praPolyEvalData_fibHomCrossApp
    {X₁ X₂ : (grothendieckContraFunctor
        (Cat.{v_J, u_J} × Cat.{v_I, u_I})).obj
      presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'}}
    (f : X₁ ⟶ X₂)
    (x : (functorFromDataContra
        evalSourceData.{u_I, v_I, u_J, v_J, w_I, w'}).obj X₁) :
    (praPolyEvalData_fibFib.{u_I, v_I, u_J, v_J, w_I, w'} X₁).obj
      x ⟶
      (praEvalTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'}.map
        (praPolyEvalData_baseFib.{u_I, v_I, u_J, v_J, w_I, w'}.map
          f).op).toFunctor.obj
        ((praPolyEvalData_fibFib.{u_I, v_I, u_J, v_J, w_I, w'} X₂)
          .obj
          (((functorFromDataContra evalSourceData.{u_I, v_I, u_J,
              v_J, w_I, w'}).map f).toFunctor.obj x)) :=
  ((CategoryTheory.ULift.upFunctor ⋙
    CategoryTheory.ULiftHom.up).op).map
    (praPolyEvalData_fibHomCrossUnwidened.{u_I, v_I, u_J,
      v_J, w_I, w'} f
      ((praPolyEvalData_unwidenFiber.{u_I, v_I, u_J, v_J,
        w_I, w'} X₁).obj x))
```

- [ ] **Step 2: Build**

If the endpoints don't match definitionally (i.e., the body's
expression doesn't typecheck), apply the praDirections fallback
pattern: extract two `eqToHom` bookend lemmas and bridge.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalData_fibHomCrossApp"
```

(No `Co-Authored-By` trailer.)

---

## Task 12: Add `praPolyEvalData_fibHomCrossNat`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyEvalData_fibHomCrossApp`.

**Context:** Naturality of `fibHomCrossApp` in the source-fibre
morphism `g`.  At the unwidened level: should reduce to
`(homFiber f)` being a NatTrans (its naturality square).

If the simpler-source-fibre-than-praDirections conjecture holds,
this proof may be substantially shorter than praDirections's
Tasks 7.5/7.6 — which used a `_target_widening_compat` helper and
a `Subtype.ext` argument.  For praEval, the source fibre's
morphism action is `presheafCatFunctor.map`-induced (a Cat-
morphism), not an Element-category morphism, so the naturality
chases through more directly.

- [ ] **Step 1: Add the lemma**

```lean
/--
Naturality of `praPolyEvalData_fibHomCrossApp` in the source
fibre morphism `g`.  Stated in fully-unfolded `∀`-form per the
universe-unification workaround.

Reduces to naturality of `(homFiber f)` (a polynomial-functor-
morphism between functors `presheafCat (objBase X) ⥤ presheafCat
(objBase X)`) at `g`-induced presheaf morphisms.
-/
private lemma praPolyEvalData_fibHomCrossNat
    {X₁ X₂ : (grothendieckContraFunctor
        (Cat.{v_J, u_J} × Cat.{v_I, u_I})).obj
      presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'}}
    (f : X₁ ⟶ X₂)
    {x y : (functorFromDataContra
        evalSourceData.{u_I, v_I, u_J, v_J, w_I, w'}).obj X₁}
    (g : x ⟶ y) :
    (praPolyEvalData_fibFib.{u_I, v_I, u_J, v_J, w_I, w'} X₁).map
      g ≫
      praPolyEvalData_fibHomCrossApp.{u_I, v_I, u_J, v_J, w_I, w'}
        f y =
      praPolyEvalData_fibHomCrossApp.{u_I, v_I, u_J, v_J, w_I, w'}
        f x ≫
      (praEvalTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'}.map
        (praPolyEvalData_baseFib.{u_I, v_I, u_J, v_J, w_I, w'}.map
          f).op).toFunctor.map
        ((praPolyEvalData_fibFib.{u_I, v_I, u_J, v_J, w_I, w'} X₂)
          .map
          (((functorFromDataContra evalSourceData.{u_I, v_I, u_J,
              v_J, w_I, w'}).map f).toFunctor.map g)) := by
  _
```

Replace `_` with the proof.  Anticipated strategy:

1. `dsimp only [praPolyEvalData_fibHomCrossApp,
   praPolyEvalData_fibFib, Functor.comp_map]`
2. Possibly a structural compat lemma like
   `praPolyDirectionsData_target_widening_compat` (refactor
   shared if useful) — `rfl`-true.
3. `rw [← Functor.map_comp, ← Functor.map_comp]`
4. `congr 1`
5. Apply naturality of `(homFiber f)` (mathlib's
   `NatTrans.naturality`).

If `rfl` happens to close after just `dsimp`, even better.

- [ ] **Step 2: Build**

If the proof doesn't close in 30 tactic steps, factor smaller
helpers per CLAUDE.md.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalData_fibHomCrossNat"
```

(No `Co-Authored-By` trailer.)

---

## Task 13: Add `praPolyEvalData_baseHomId`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyEvalData_fibHomCrossNat`.

**Context:** Identity coherence.  At `f = 𝟙 X`,
`praPolyEvalData_fibHomCrossApp` reduces to the canonical `eqToHom`.
Likely closes by `rfl` or a 1–3-line tactic chain (mirror
praDirections's Task 7.8).

- [ ] **Step 1: Add the lemma**

```lean
/--
Widened identity coherence for `praPolyEvalData_fibHomCrossApp`.
At `f = 𝟙 X`, equals the canonical `eqToHom`.  Stated in unfolded
`∀`-form per the universe-unification workaround.
-/
private lemma praPolyEvalData_baseHomId
    (X : (grothendieckContraFunctor
        (Cat.{v_J, u_J} × Cat.{v_I, u_I})).obj
      presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'})
    (x : (functorFromDataContra
        evalSourceData.{u_I, v_I, u_J, v_J, w_I, w'}).obj X) :
    praPolyEvalData_fibHomCrossApp.{u_I, v_I, u_J, v_J, w_I, w'}
      (𝟙 X) x =
      eqToHom
        (functorBetweenCovContraBaseHomEqIdProof
          (functorFromDataContra evalSourceData.{u_I, v_I, u_J,
            v_J, w_I, w'})
          praEvalTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'}
          praPolyEvalData_baseFib.{u_I, v_I, u_J, v_J, w_I, w'}
          praPolyEvalData_fibFib.{u_I, v_I, u_J, v_J, w_I, w'}
          X x) := by
  rfl
```

If `rfl` fails, use the praDirections Task 7.8 strategy:

```lean
  dsimp only [praPolyEvalData_fibHomCrossApp]
  rw [praPolyEvalData_fibHomCrossUnwidened_id]   -- if needed
  rw [eqToHom_map]
```

(possibly with an unwidened-identity helper lemma extracted).

- [ ] **Step 2: Build**

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalData_baseHomId"
```

(No `Co-Authored-By` trailer.)

---

## Task 14: Add `praPolyEvalData_baseHomComp`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyEvalData_baseHomId`.

**Context:** Composition coherence.  In praDirections's Task 7.10
this closed by `rfl`.  Anticipated to close similarly here.

- [ ] **Step 1: Add the lemma**

```lean
/--
Widened composition coherence for `praPolyEvalData_fibHomCrossApp`.
Holds by `rfl` because every step in the decomposition reduces
definitionally — the unwidened decomposition is `rfl`, the widening
distributes definitionally, and the structural commutation between
`(praEvalTargetFibre.map h.op).toFunctor.map` and `widening.op.map`
is `rfl`.

Stated in fully-unfolded `∀`-form per the universe-unification
workaround.
-/
private lemma praPolyEvalData_baseHomComp
    {X₁ X₂ X₃ : (grothendieckContraFunctor
        (Cat.{v_J, u_J} × Cat.{v_I, u_I})).obj
      presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'}}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (x : (functorFromDataContra
        evalSourceData.{u_I, v_I, u_J, v_J, w_I, w'}).obj X₁) :
    praPolyEvalData_fibHomCrossApp.{u_I, v_I, u_J, v_J, w_I, w'}
      (f ≫ g) x =
      praPolyEvalData_fibHomCrossApp.{u_I, v_I, u_J, v_J, w_I, w'}
        f x ≫
      (praEvalTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'}.map
        (praPolyEvalData_baseFib.{u_I, v_I, u_J, v_J, w_I, w'}.map
          f).op).toFunctor.map
        (praPolyEvalData_fibHomCrossApp.{u_I, v_I, u_J, v_J,
          w_I, w'} g
          (((functorFromDataContra evalSourceData.{u_I, v_I, u_J,
              v_J, w_I, w'}).map f).toFunctor.obj x)) ≫
      eqToHom
        (functorBetweenCovContraBaseHomEqCompProof
          (functorFromDataContra evalSourceData.{u_I, v_I, u_J,
            v_J, w_I, w'})
          praEvalTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'}
          praPolyEvalData_baseFib.{u_I, v_I, u_J, v_J, w_I, w'}
          praPolyEvalData_fibFib.{u_I, v_I, u_J, v_J, w_I, w'}
          f g x) := by
  rfl
```

If `rfl` fails, apply praDirections's Task 7.10 fallback (which
closed by `rfl` end-to-end).  If still failing, factor an unwidened
composition coherence helper and apply
`Functor.congr_hom`-style reasoning.

- [ ] **Step 2: Build**

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalData_baseHomComp"
```

(No `Co-Authored-By` trailer.)

---

## Task 15: Assemble `praPolyEvalData` bundle

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyEvalData_baseHomComp`.

- [ ] **Step 1: Add the bundle**

```lean
/--
Bundled `FunctorBetweenCovContraData` for `praPolyEvalFunctor`.

The base functor maps `((J, I), P) ↦ J`; the fibre functor maps
widened presheaves `Z` on `I` to widened op-presheaves on `J` via
`(ccrNewEvalCatFunctor _).obj P` (the polynomial functor at this
P) post-composed with the result-side widening.  The cross-fibre
morphism and its three coherence obligations are supplied by
Tasks 11/12/13/14.
-/
def praPolyEvalData :
    FunctorBetweenCovContraData.{_, _, _, _, _, _}
      (functorFromDataContra evalSourceData.{u_I, v_I, u_J, v_J,
        w_I, w'})
      praEvalTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'} where
  baseFib := praPolyEvalData_baseFib.{u_I, v_I, u_J, v_J, w_I, w'}
  fibFib := praPolyEvalData_fibFib.{u_I, v_I, u_J, v_J, w_I, w'}
  fibHomCrossApp := praPolyEvalData_fibHomCrossApp.{u_I, v_I, u_J,
    v_J, w_I, w'}
  fibHomCrossNat := praPolyEvalData_fibHomCrossNat.{u_I, v_I,
    u_J, v_J, w_I, w'}
  baseHomId := praPolyEvalData_baseHomId.{u_I, v_I, u_J, v_J,
    w_I, w'}
  baseHomComp := praPolyEvalData_baseHomComp.{u_I, v_I, u_J, v_J,
    w_I, w'}
```

The bundle is `def` (not `private`) so that tests can reference
its `.fibFib` etc. — mirroring the un-privating done for
`praPolyDirectionsData` during the praDirections test work.

- [ ] **Step 2: Build**

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: assemble praPolyEvalData bundle"
```

(No `Co-Authored-By` trailer.)

---

## Task 16: Define `praPolyEvalFunctor`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyEvalData`.

- [ ] **Step 1: Add the definition**

```lean
/--
The `(I, J, P)`-natural polynomial-functor evaluation, in flat-
functor form between Grothendiecks.  Built via
`FunctorBetweenCovContraData.toFunctor` from `praPolyEvalData`.

Objects of the source are 4-tuples `((J, I), P, Z)`; objects of
the target are pairs `(J, op_presheaf)`.  The functor sends
`((J, I), P, Z) ↦ (J, op (praEvalAtFunctor P Z))` — i.e., the
value of the polynomial functor on `Z` at each stage `j`.
-/
def praPolyEvalFunctor :
    praPolyEvalSource.{u_I, v_I, u_J, v_J, w_I, w'} ⥤
      praPolyEvalTarget.{u_I, v_I, u_J, v_J, w_I, w'} :=
  FunctorBetweenCovContraData.toFunctor
    praPolyEvalData.{u_I, v_I, u_J, v_J, w_I, w'}
```

- [ ] **Step 2: Build**

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalFunctor"
```

(No `Co-Authored-By` trailer.)

---

## Task 17: Add three `rfl` bridge lemmas

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyEvalFunctor`.

- [ ] **Step 1: Add the three lemmas**

```lean
/--
Bridge lemma: `praPolyEvalFunctor`'s action on objects projects to
the `J` component of the source's base.
-/
theorem praPolyEvalFunctor_base
    (X : praPolyEvalSource.{u_I, v_I, u_J, v_J, w_I, w'}) :
    GrothendieckContraFunctor.objBase
      (praPolyEvalFunctor.{u_I, v_I, u_J, v_J, w_I, w'}.obj X) =
    (GrothendieckContraFunctor.objBase X.base).1 :=
  rfl

/--
Bridge lemma: `praPolyEvalFunctor`'s fibre component agrees with
`(praPolyEvalData.fibFib X.base).obj X.fiber`.
-/
theorem praPolyEvalFunctor_fibre
    (X : praPolyEvalSource.{u_I, v_I, u_J, v_J, w_I, w'}) :
    GrothendieckContraFunctor.objFiber
      (praPolyEvalFunctor.{u_I, v_I, u_J, v_J, w_I, w'}.obj X) =
    (praPolyEvalData.{u_I, v_I, u_J, v_J, w_I, w'}.fibFib
      X.base).obj X.fiber :=
  rfl

/--
Bridge lemma: `praPolyEvalFunctor`'s action on morphisms decomposes
as `fibHomCrossApp` composed with the fibre-functor action.
-/
theorem praPolyEvalFunctor_map_app
    {X Y : praPolyEvalSource.{u_I, v_I, u_J, v_J, w_I, w'}}
    (f : X ⟶ Y) :
    GrothendieckContraFunctor.homFiber
      (praPolyEvalFunctor.{u_I, v_I, u_J, v_J, w_I, w'}.map f) =
    praPolyEvalData.{u_I, v_I, u_J, v_J, w_I, w'}.fibHomCrossApp
        f.base X.fiber ≫
      (praEvalTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'}.map
          (praPolyEvalData.baseFib.map f.base).op).toFunctor.map
        ((praPolyEvalData.fibFib Y.base).map f.fiber) :=
  rfl
```

- [ ] **Step 2: Build**

If any `rfl` fails, fall back to a short `simp only` with
`praPolyEvalFunctor`, `FunctorBetweenCovContraData.toFunctor`, and
relevant unfolds.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalFunctor bridge lemmas"
```

(No `Co-Authored-By` trailer.)

---

## Task 18: Add `praPolyEvalAtSourceObj` helper

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after the bridge
  lemmas (still in `section PresheafPRAEvalAt` if that's where the
  per-component accessors live; otherwise just after the bridge
  lemmas).

- [ ] **Step 1: Add the definition**

```lean
/--
Build a `praPolyEvalSource` object from a per-component
`(I, J, P, Z)` triple.  Public packaging: callers can apply
`praPolyEvalFunctor` to this object to obtain the polynomial-
functor evaluation in the natural-functor form.
-/
def praPolyEvalAtSourceObj
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
    (Z : Iᵒᵖ ⥤ Type w_I) :
    praPolyEvalSource.{u_I, v_I, u_J, v_J, w_I, w'} :=
  let base : (grothendieckContraFunctor
      (Cat.{v_J, u_J} × Cat.{v_I, u_I})).obj
        presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
          w_I, w'} :=
    GrothendieckContraFunctor.mkObj (Cat.of Jᵒᵖ, Cat.of Iᵒᵖ) P
  ⟨base,
    (show CategoryTheory.ULiftHom.{...}
        (ULift.{..., ...}
          ↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
            (Opposite.op (Cat.of Iᵒᵖ)))) from
      CategoryTheory.ULiftHom.objUp (ULift.up Z))⟩
```

The exact universe annotations on `ULiftHom.{...}` and
`ULift.{..., ...}` are LSP-discovered; mirror
`praPolyDirectionsAtSourceObj` (commit `ed74a7ff`).

- [ ] **Step 2: Build**

If a universe metavariable surfaces, follow the
`praPolyDirectionsAtSourceObj` pattern: add explicit universe
annotations on `ULiftHom` and the inner `ULift` based on LSP
diagnostics.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyEvalAtSourceObj helper"
```

(No `Co-Authored-By` trailer.)

---

## Task 19: Add `praEvalAtFunctor_via_praPolyEvalFunctor` bridge theorem and test

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyEvalAtSourceObj`.
- Modify: `GebLeanTests/Utilities/PresheafPRAEvalNat.lean` — append a
  bridge-test section (the test file is created in Task 21; if
  that hasn't happened yet, defer the test addition to after
  Task 21).

- [ ] **Step 1: Insert placeholder theorem to discover RHS**

```lean
@[simp] theorem praEvalAtFunctor_via_praPolyEvalFunctor
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
    (Z : Iᵒᵖ ⥤ Type w_I) :
    (praEvalAtFunctor I J).obj P |>.obj Z = _ :=
  rfl
```

Run `lake build` to surface the expected RHS via the unsolved-`_`
error; use `mcp__lean-lsp__lean_goal` for precision.

- [ ] **Step 2: Fill the RHS via LSP discovery**

The expected shape, mirroring
`praDirectionsAt_via_praPolyDirectionsFunctor` (commit
`b9daaca3`):

```lean
ULift.down.{..., ...}
  (CategoryTheory.ULiftHom.objDown.{..., ...}
    (GrothendieckContraFunctor.objFiber
      (praPolyEvalFunctor.{u_I, v_I, u_J, v_J, w_I, w'}.obj
        (praPolyEvalAtSourceObj I J P Z))).unop)
```

Try `rfl` first.  If `rfl` fails, fall back to:

```lean
  := by
  simp only [praEvalAtFunctor, praPolyEvalFunctor,
    praPolyEvalAtSourceObj,
    praPolyEvalFunctor_fibre, praPolyEvalFunctor_base]
  rfl
```

If that also fails, escalate per CLAUDE.md.  The user has
explicitly approved escalation.

- [ ] **Step 3: Add the docstring**

```lean
/--
Bridge: `(praEvalAtFunctor I J).obj P |>.obj Z` agrees with the
unwidened-and-unopped fibre of `praPolyEvalFunctor` applied to the
corresponding source object built by `praPolyEvalAtSourceObj`.
Connects the per-component accessor to the natural-in-`(I, J, P)`
functor.

Tagged `@[simp]` so callers can use `simp` to translate
per-component evaluation expressions into natural-functor form.
-/
```

- [ ] **Step 4: Build and commit (theorem only — test added in
  Task 21)**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praEvalAtFunctor_via_praPolyEvalFunctor"
```

(No `Co-Authored-By` trailer.)  The test addition happens in
Task 21 after the test file is created.

---

## Task 20: Update `section` boundaries in `PresheafPRA.lean`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — adjust section structure if
  needed.

**Context:** The natural-form constructions added in Tasks 1–19
land in or near `section PresheafPRAEvalAt`.  If the section has
grown too large, split into a `section PresheafPRAEvalNat`
subsection.

- [ ] **Step 1: Inspect**

Run:

```bash
grep -n "^section\|^end " GebLean/PresheafPRA.lean
```

Confirm the natural-form definitions are inside an appropriate
section.

- [ ] **Step 2: Adjust if needed**

If the existing `section PresheafPRAEvalAt` ends before the new
natural-form definitions, move the `end PresheafPRAEvalAt` line
appropriately, or add a new `section PresheafPRAEvalNat` block
around the new definitions.

The choice depends on whether the natural-form is conceptually
part of "PresheafPRAEvalAt" (the per-component accessors) or
its own subsystem.  Recommended: **separate subsection**
`section PresheafPRAEvalNat`, placed adjacent to `PresheafPRAEvalAt`.

- [ ] **Step 3: Build**

- [ ] **Step 4: Commit (only if changes made)**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: scope praPolyEval definitions in their own section"
```

(No `Co-Authored-By` trailer.)  If no changes were needed, skip the
commit.

---

## Task 21: Create test file with type-signature sanity tests

**Files:**

- Create: `GebLeanTests/Utilities/PresheafPRAEvalNat.lean`.

- [ ] **Step 1: Create the file**

```lean
import GebLean.PresheafPRA

/-!
# Tests for (I, J, P)-Naturality of praPolyEvalFunctor

Type-signature sanity checks and small-example tests for
`praPolyEvalFunctor` and friends in `GebLean.PresheafPRA`.
-/

open GebLean CategoryTheory

attribute [local instance] CategoryTheory.uliftCategory

/-! ## Type-signature sanity -/

example :
    praPolyEvalSource.{0, 0, 0, 0, 0, 0} ⥤
      praPolyEvalTarget.{0, 0, 0, 0, 0, 0} :=
  praPolyEvalFunctor.{0, 0, 0, 0, 0, 0}

example : Cat.{0, 1} :=
  praPolyEvalSource.{0, 0, 0, 0, 0, 0}

example : Cat.{0, 1} :=
  praPolyEvalTarget.{0, 0, 0, 0, 0, 0}

example : Cat.{0, 0}ᵒᵖ ⥤ Cat.{0, 1} :=
  praEvalTargetFibre.{0, 0, 0, 0, 0, 0}
```

The Cat universes (`{0, 1}` rather than `{0, 0}`) match the pattern
seen in `PresheafPRADirNat.lean` due to the `(w_I + 1)` widenings.
Adjust based on LSP-revealed types of the new declarations.

- [ ] **Step 2: Build**

Run: `lake build`.  Expected: clean.

- [ ] **Step 3: Add the bridge theorem test (deferred from Task 19)**

Append to the file:

```lean
/-! ## Bridge to praPolyEvalFunctor -/

section BridgeTest

example (I : Type 0) [Category.{0} I] (J : Type 0) [Category.{0} J]
    (P : PresheafPRACat.{0, 0, 0, 0, 0, 0} I J)
    (Z : Iᵒᵖ ⥤ Type 0) :
    (praEvalAtFunctor I J).obj P |>.obj Z =
        <discovered-RHS-with-zero-universes> :=
  praEvalAtFunctor_via_praPolyEvalFunctor I J P Z

end BridgeTest
```

The `<discovered-RHS-with-zero-universes>` mirrors the RHS chosen
in Task 19, with all six universe arguments specialized to `0`.

- [ ] **Step 4: Build**

Run: `lake build`.  Expected: clean.

- [ ] **Step 5: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRAEvalNat.lean
git commit -m "tests: add PresheafPRAEvalNat.lean with type-signature sanity tests"
```

(No `Co-Authored-By` trailer.)

---

## Task 22: Register test file in `GebLeanTests.lean`

**Files:**

- Modify: `GebLeanTests.lean`.

- [ ] **Step 1: Add the import**

Locate the existing
`import GebLeanTests.Utilities.PresheafPRADirNat` line and insert
on the next line:

```lean
import GebLeanTests.Utilities.PresheafPRAEvalNat
```

- [ ] **Step 2: Build and run tests**

Run: `lake build && lake test`.  Expected: clean.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests.lean
git commit -m "tests: register PresheafPRAEvalNat test file"
```

(No `Co-Authored-By` trailer.)

---

## Task 23: Add bridge-lemma collapse + functoriality + universe tests

**Files:**

- Modify: `GebLeanTests/Utilities/PresheafPRAEvalNat.lean` — append.

- [ ] **Step 1: Add bridge-lemma collapse tests**

```lean
/-! ## Bridge-lemma collapse at a small concrete base -/

section CollapseTest

example (X : praPolyEvalSource.{0, 0, 0, 0, 0, 0}) :
    GrothendieckContraFunctor.objBase
      (praPolyEvalFunctor.{0, 0, 0, 0, 0, 0}.obj X) =
    (GrothendieckContraFunctor.objBase X.base).1 :=
  praPolyEvalFunctor_base.{0, 0, 0, 0, 0, 0} X

example (X : praPolyEvalSource.{0, 0, 0, 0, 0, 0}) :
    GrothendieckContraFunctor.objFiber
      (praPolyEvalFunctor.{0, 0, 0, 0, 0, 0}.obj X) =
    (praPolyEvalData.{0, 0, 0, 0, 0, 0}.fibFib X.base).obj
      X.fiber :=
  praPolyEvalFunctor_fibre.{0, 0, 0, 0, 0, 0} X

end CollapseTest
```

If `praPolyEvalData` is private, drop the second `example` or
un-private `praPolyEvalData` (mirroring the Task 18 pattern in the
praDirections work).  Per the design, `praPolyEvalData` is a `def`
(not `private`), so this should work as-is.

- [ ] **Step 2: Add functoriality tests**

```lean
/-! ## Functoriality at a concrete morphism -/

section FunctorialityTest

example (X : praPolyEvalSource.{0, 0, 0, 0, 0, 0}) :
    praPolyEvalFunctor.{0, 0, 0, 0, 0, 0}.map (𝟙 X) =
      𝟙 (praPolyEvalFunctor.{0, 0, 0, 0, 0, 0}.obj X) :=
  praPolyEvalFunctor.{0, 0, 0, 0, 0, 0}.map_id X

example {X Y Z : praPolyEvalSource.{0, 0, 0, 0, 0, 0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    praPolyEvalFunctor.{0, 0, 0, 0, 0, 0}.map (f ≫ g) =
      praPolyEvalFunctor.{0, 0, 0, 0, 0, 0}.map f ≫
        praPolyEvalFunctor.{0, 0, 0, 0, 0, 0}.map g :=
  praPolyEvalFunctor.{0, 0, 0, 0, 0, 0}.map_comp f g

end FunctorialityTest
```

- [ ] **Step 3: Add universe-polymorphism tests**

```lean
/-! ## Universe polymorphism -/

section UniversePoly

example :
    praPolyEvalSource.{1, 0, 0, 0, 0, 0} ⥤
      praPolyEvalTarget.{1, 0, 0, 0, 0, 0} :=
  praPolyEvalFunctor.{1, 0, 0, 0, 0, 0}

example :
    praPolyEvalSource.{0, 0, 1, 0, 0, 0} ⥤
      praPolyEvalTarget.{0, 0, 1, 0, 0, 0} :=
  praPolyEvalFunctor.{0, 0, 1, 0, 0, 0}

end UniversePoly
```

- [ ] **Step 4: Build and run tests**

Run: `lake build && lake test`.  Expected: clean.

- [ ] **Step 5: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRAEvalNat.lean
git commit -m "tests: add bridge-lemma, functoriality, universe-poly tests"
```

(No `Co-Authored-By` trailer.)

---

## Task 24: Add pointwise-accessor compatibility test

**Files:**

- Modify: `GebLeanTests/Utilities/PresheafPRAEvalNat.lean` — append.

- [ ] **Step 1: Add the test**

```lean
/-! ## Pointwise-accessor compatibility -/

section AccessorCompat

example (I : Type 0) [Category.{0} I] (J : Type 0) [Category.{0} J]
    (P : PresheafPRACat.{0, 0, 0, 0, 0, 0} I J) :
    (Iᵒᵖ ⥤ Type 0) ⥤ (Jᵒᵖ ⥤ Type 0) :=
  (praEvalAtFunctor.{0, 0, 0, 0, 0, 0} I J).obj P

end AccessorCompat
```

This confirms `praEvalAtFunctor`'s shape is unchanged by the new
natural-form additions.

- [ ] **Step 2: Build and run tests**

Run: `lake build && lake test`.  Expected: clean.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRAEvalNat.lean
git commit -m "tests: add pointwise-accessor compatibility test"
```

(No `Co-Authored-By` trailer.)

---

## Task 25: Update `.session/workstreams/presheaf-pra.md`

**Files:**

- Modify: `.session/workstreams/presheaf-pra.md`.

- [ ] **Step 1: Append a "praEval Naturality (committed
  2026-04-26)" section**

Add a new section under the existing v2 progress section,
listing the new commits.  Mirror the format of the
"Tasks 12–22 (committed 2026-04-25)" section (a markdown table
with commit SHAs and short task descriptions).

Keep entries terse — one line each, ≤80 chars per row (verify
with `markdownlint-cli2`).

- [ ] **Step 2: Update the `## Files` table**

If the test file `GebLeanTests/Utilities/PresheafPRAEvalNat.lean`
should be listed in the "Files" table near line 290, add it.

- [ ] **Step 3: Lint check**

```bash
markdownlint-cli2 .session/workstreams/presheaf-pra.md
```

Expected: zero errors.

- [ ] **Step 4: Commit**

```bash
git add .session/workstreams/presheaf-pra.md
git commit -m "session: record praEval naturality completion"
```

(No `Co-Authored-By` trailer.)

---

## Final Validation

After all 25 tasks:

- [ ] **Run full build and tests**

```bash
lake build
lake test
```

Expected: both clean, zero warnings.

- [ ] **Confirm commit log shape**

Run:

```bash
git log --oneline e23d1dbd..HEAD
```

Expected: ~24 commits with `presheaf-pra:`, `tests:`, or `session:`
prefixes.  Ordering follows the task numbers.

- [ ] **Verify no forbidden tokens**

```bash
grep -rEn "sorry|admit|axiom|noncomputable|classical" \
  GebLean/PresheafPRA.lean GebLeanTests/Utilities/PresheafPRAEvalNat.lean
```

Expected: only the existing legitimate uses (e.g., the literal
string `"sorry"` in docstrings explaining what NOT to do, if any).
No new occurrences from this work.

---

## Next-Session Guidance (added 2026-04-26 at session pause)

When resuming, the original task bodies for Tasks 10–17 below
require adaptation to the revised framework.  Key adjustments:

1. **All `FunctorBetweenCovContraData` references become
   `FunctorBetweenContraContraData`**.
2. **`FibHomCrossApp` shape changed** — the new framework's
   `FunctorBetweenContraContraFibHomCrossApp` takes a TARGET-side
   input `x' : G.obj (op c')` (not source-side `x : G.obj c`):

   ```lean
   ∀ {c c' : C} (f : c ⟶ c') (x' : G.obj (Opposite.op c')),
     (fibFib c).obj ((G.map f.op).toFunctor.obj x') ⟶
       (F.map (baseFib.map f).op).toFunctor.obj
         ((fibFib c').obj x')
   ```

   So Task 10 (`fibHomCrossUnwidened`) and Task 11
   (`fibHomCrossApp` widened) must be parametrised by `x' :
   widenedPSh(I_target)` (the target-side presheaf), not `Z` at
   the source side.  The morphism's source involves the
   *backward-transported* `x'` (via `evalSourceData.map f.op`),
   reflecting the polynomial functor's covariant action on `Z`
   composed with the I-pullback.

3. **`praEvalTargetFibre` no longer has `Cat.opFunctor`**.
   The `fibFib` body's final widening uses just
   `ULift.upFunctor ⋙ ULiftHom.up` (no `.op`).

4. **`evalSourceData` is a direct `Cᵒᵖ ⥤ Cat`** (not a
   `FunctorFromDataContra`-wrapped data shape).  Its `map`
   action uses `presheafCatFunctor.map (Quiver.Hom.op f.2) ⋙
   catULiftFunctor2.map`.

5. **`praPolyEvalSource` is a contraGrothendieck**: built as
   `(grothendieckContraFunctor C).obj evalSourceData` where
   `C := (grothendieckContraFunctor (Cat × Cat)).obj
   presheafPRACatBifunctorUncurriedOp`.

### Pointers to existing code at session pause

- New framework: `GebLean/Utilities/Grothendieck.lean` lines
  ~5330–5524 (abbrevs + structure) and the extractor section
  added by commit `d9d08504`.
- praEval target side: `GebLean/PresheafPRA.lean` lines
  ~360–390 (`praEvalTargetFibre`, `praPolyEvalTarget`).
- praEval source side: `GebLean/PresheafPRA.lean` (search for
  `evalSourceData` and `praPolyEvalSource`).
- `praPolyEvalData_baseFib` and `_fibFib`: same file (commits
  `f0f1f208`, `d701b401`).

### Anticipated patterns for remaining tasks

- **Task 10/11 (`fibHomCrossUnwidened` / `fibHomCrossApp`)**:
  the polynomial-functor-morphism action `homFiber f` provides a
  natural transformation between polynomial functors at
  different `P`'s.  The cross-fibre app encodes the resulting
  natural transformation between evaluations applied to the
  target-side `x'` (a presheaf at `I_target`).
- **Tasks 13, 14 (identity, composition coherence)**: the
  praDirections analogs (Tasks 7.8, 7.10) closed by `rfl`
  end-to-end.  Try `rfl` first.
- **Task 12 (naturality)**: praDirections Task 7.6 needed a
  one-line `rfl` structural compat lemma plus a six-tactic
  proof.  Plausible same shape applies.
- **Task 19 (bridge theorem
  `praEvalAtFunctor_via_praPolyEvalFunctor`)**: praDirections
  analog (commit `b9daaca3`) closed by `rfl` after explicit
  universe annotations on `ULift.down`/`ULiftHom.objDown`.

## Execution Handoff

Plan with revisions saved to
`docs/superpowers/plans/2026-04-26-praEval-naturality.md`.

Spec at
`docs/superpowers/specs/2026-04-26-praEval-naturality-design.md`.

Workstream notes at `.session/workstreams/presheaf-pra.md`
(section "praEval Naturality").

The user has expressed a preference for resuming via
`superpowers:executing-plans` rather than
`superpowers:subagent-driven-development` for the next session.

The remaining tasks (10–25) should adapt the bodies in the
original-numbered tasks below to the new ContraContra framework
and target-fibre shape, per the "Next-Session Guidance" notes
above.  Each task is bite-sized; escalate to user if a coherence
proof resists closure after the standard `rfl` / `simp only`
fallback chain.
