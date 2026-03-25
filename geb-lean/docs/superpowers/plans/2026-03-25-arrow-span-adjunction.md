# Arrow-Span Reflective Adjunction Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Generalize the presheaf-specific functionalization
adjunction `Arrow(PSh(C)) ⊣ PshRelEdge(C)` to an
`Arrow(C) ⊣ (WalkingSpan ⥤ C)` adjunction for any category
`C` with constructive pushouts, then refactor the
presheaf-specific code to use the general construction.

**Architecture:** The construction uses a single pushout per
span diagram. We pass the pushout cocone choice as an
explicit parameter `(pushouts : (S : WalkingSpan ⥤ C) →
ColimitCocone S)`, avoiding both mathlib's `Prop`-valued
`HasColimit` (which requires `Classical.choice`) and
typeclass synthesis issues (the project sets
`maxSynthPendingDepth = 3`). The arrow-span inclusion
sends `f : P ⟶ Q` to `span (𝟙 P) f`; the reflector sends
a span to `Arrow.mk pushout.inl`. The presheaf
instantiation provides `ColimitCocone` via pointwise
`Quot` in `Type`, refactoring the existing `Quot`-based
code from `PshRelEdgeFunctionalize.lean` into
`ColimitCocone` form.

**Tech Stack:** Lean 4, mathlib (`Cocone`, `IsColimit`,
`ColimitCocone`, `PushoutCocone`, `WalkingSpan`, `span`,
`spanHomMk`), project utilities (`Arrow.lean`,
`PshRelEdgeFunctionalize.lean`,
`PshRelEdgeReflectiveChain.lean`)

**Note on vertex names:** WalkingSpan vertices use
mathlib's abbreviations: `.zero` (apex), `.left` (left
foot), `.right` (right foot). Morphisms: `Hom.fst` and
`Hom.snd`.

---

## File Structure

| File | Role |
|------|------|
| `GebLean/Utilities/ArrowSpanAdjunction.lean` (create) | General adjunction parameterized on explicit pushout cocone data; presheaf instantiation |
| `GebLean/PshRelEdgeFunctionalize.lean` (modify) | Redefine `pshRelEdgeFunctionalizeFunctor` as `pshRelEdgeInclusionFunctor ⋙ spanArrowReflector`; rebuild the `PshRelEdge ↔ Arrow` adjunction directly (not via `Adjunction.comp`, since the two inclusion functors `arrowSpanInclusion` and `pshRelEdgeGraphFunctor ⋙ pshRelEdgeInclusionFunctor` are naturally isomorphic but not definitionally equal) |
| `GebLean/PshRelEdgeReflectiveChain.lean` (modify) | Update reflective chain to include `Arrow ↔ Span` step |
| `GebLean.lean` (modify) | Add import for new file |

---

### Task 1: Arrow-Span Inclusion and Pushout Parameter

**Files:**
- Create: `GebLean/Utilities/ArrowSpanAdjunction.lean`
- Modify: `GebLean.lean` (add import)

Define the arrow-span inclusion functor and the
pushout cocone parameter type.

- [ ] **Step 1: Create file with module header,
  imports, and the arrow-span inclusion functor**

  ```lean
  import Mathlib.CategoryTheory.Comma.Arrow
  import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Cospan
  import Mathlib.CategoryTheory.Limits.Shapes.Pullback.PullbackCone
  import Mathlib.CategoryTheory.Adjunction.Reflective

  open CategoryTheory Limits

  namespace GebLean

  universe v u

  variable {C : Type u} [Category.{v} C]
  ```

  Define `arrowSpanInclusion (C : Type u)
  [Category.{v} C] : Arrow C ⥤ (WalkingSpan ⥤ C)`.

  On objects: `f ↦ span (𝟙 f.left) f.hom`.

  On morphisms: use `spanHomMk` with components
  `sq.left` (at `.zero` and `.left`) and `sq.right`
  (at `.right`). Naturality at `Hom.fst` holds by
  `Category.id_comp`/`Category.comp_id`; at
  `Hom.snd` by `sq.w`.

  Prove `map_id` and `map_comp` (both by `ext`
  on span components + `rfl` or `simp`).

  Note: the existing `pshRelEdgeSpan` uses
  `span π₁ π₂` (projections from the relation);
  `arrowSpanInclusion` uses `span (𝟙 P) f`.
  These are different functors — the former starts
  from edges (monic spans), the latter from arrows.

- [ ] **Step 2: Prove full faithfulness**

  Define `arrowSpanInclusion.fullyFaithful`.

  Preimage of `α : span (𝟙 P) f ⟶ span (𝟙 Q) g`
  is `Arrow.homMk (α.app .left) (α.app .right)`,
  with commutativity from naturality of `α` at
  `Hom.snd`.

  Derive `Full` and `Faithful` instances.

- [ ] **Step 3: Add imports to entry modules**

  Add `import GebLean.Utilities.ArrowSpanAdjunction`
  to both `GebLean.lean` (in the Utilities section)
  and `GebLean/Utilities.lean` (the utilities index
  module), per the CLAUDE.md convention.

- [ ] **Step 4: Build and verify**

  Run: `lake build GebLean.Utilities.ArrowSpanAdjunction`

- [ ] **Step 5: Commit**

  ```
  Define arrow-span inclusion functor
  ```

---

### Task 2: Span-Arrow Reflector Functor

**Files:**
- Modify: `GebLean/Utilities/ArrowSpanAdjunction.lean`

Define the left adjoint functor
`(WalkingSpan ⥤ C) ⥤ Arrow C` parameterized on
an explicit pushout cocone assignment.

- [ ] **Step 1: Define the functor on objects**

  The functor is parameterized:
  ```lean
  variable (pushouts :
    (S : WalkingSpan ⥤ C) → ColimitCocone S)
  ```

  Given `S : WalkingSpan ⥤ C`, the pushout cocone
  is `(pushouts S).cocone` with point
  `(pushouts S).cocone.pt`. The arrow is:
  ```
  Arrow.mk ((pushouts S).cocone.ι.app .left)
  ```
  Source = `S.obj .left`, target = pushout point.

- [ ] **Step 2: Define the functor on morphisms**

  Given `α : S₁ ⟶ S₂`, the arrow morphism has:
  - Left: `α.app .left`
  - Right: `(pushouts S₁).isColimit.desc` applied
    to the cocone over `S₁` with point =
    `(pushouts S₂).cocone.pt` and legs =
    `α.app .left ≫ (pushouts S₂).cocone.ι.app .left`
    and
    `α.app .right ≫ (pushouts S₂).cocone.ι.app .right`.

  The cocone over `S₁` is formed by precomposing
  `α` with the `S₂` cocone. Explicitly, define:
  ```lean
  Cocone.mk (pushouts S₂).cocone.pt
    (α ≫ (pushouts S₂).cocone.ι)
  ```

  Commutativity of the arrow square follows from
  `IsColimit.fac` at `.left`.

- [ ] **Step 3: Prove `map_id` and `map_comp`**

  Both follow from `IsColimit.uniq`:

  `map_id`: The identity on the pushout satisfies
  `ι.app j ≫ 𝟙 = ι.app j`, so by `uniq` it
  equals `desc`.

  `map_comp`: The composition `desc₁ ≫ desc₂`
  satisfies the factoring property for the
  composed span morphism, so by `uniq` it equals
  `desc` for the composite.

  For the left component, use `Category.id_comp`
  / `Category.comp_id` / `Category.assoc` and
  `CommaMorphism.ext`.

- [ ] **Step 4: Build and verify**

  Run: `lake build GebLean.Utilities.ArrowSpanAdjunction`

- [ ] **Step 5: Commit**

  ```
  Define span-arrow reflector functor
  ```

---

### Task 3: Arrow-Span Adjunction

**Files:**
- Modify: `GebLean/Utilities/ArrowSpanAdjunction.lean`

Construct `spanArrowReflector pushouts ⊣
arrowSpanInclusion C` via
`Adjunction.mkOfUnitCounit`.

- [ ] **Step 1: Define the unit**

  The unit at span `S` is a morphism
  `S ⟶ (arrowSpanInclusion C).obj
  ((spanArrowReflector pushouts).obj S)`.

  The target is `span (𝟙 (S.obj .left))
  ((pushouts S).cocone.ι.app .left)`.

  Span morphism via `spanHomMk`:
  - `.zero`: `S.map Hom.fst` (the left leg)
  - `.left`: `𝟙 (S.obj .left)`
  - `.right`: `(pushouts S).cocone.ι.app .right`

  Naturality at `Hom.fst`:
  `S.map fst ≫ 𝟙 _ = S.map fst` (by comp_id) ✓

  Naturality at `Hom.snd`:
  `S.map fst ≫ ι.app .left = S.map snd ≫ ι.app .right`
  — this is the pushout/cocone condition
  (`Cocone.w` or direct from cocone naturality) ✓

  Prove naturality as a natural transformation.

- [ ] **Step 2: Define the counit**

  The counit at `f : Arrow C` is a morphism
  `(spanArrowReflector pushouts).obj
  ((arrowSpanInclusion C).obj f) ⟶ f`.

  The source is the pushout of `span (𝟙 f.left) f.hom`.

  Arrow morphism:
  - Left: `𝟙 f.left`
  - Right: `(pushouts (span (𝟙 f.left) f.hom))
    .isColimit.desc` applied to the cocone
    `(f.right, f.hom, 𝟙 f.right)`.
    Condition: `𝟙 ≫ f.hom = f.hom ≫ 𝟙` ✓

  Commutativity: by `IsColimit.fac` at `.left`.

  Prove naturality (requires `IsColimit.uniq`
  for uniqueness of induced maps).

- [ ] **Step 3: Prove the left triangle identity**

  `reflector.map (unit.app S) ≫
  counit.app (reflector.obj S) = 𝟙`

  Use `CommaMorphism.ext`:
  - Left: `𝟙 ≫ 𝟙 = 𝟙` ✓
  - Right: composition is a map
    `pushout → pushout` satisfying
    `ι.app j ≫ comp = ι.app j` for all `j`.
    By `IsColimit.uniq`, this equals `𝟙`.
    (The proof shows the composition satisfies
    `ι.app .left ≫ comp = ι.app .left` and
    `ι.app .right ≫ comp = ι.app .right` using
    `IsColimit.fac`.)

- [ ] **Step 4: Prove the right triangle identity**

  `unit.app (inclusion.obj f) ≫
  inclusion.map (counit.app f) = 𝟙`

  This is a span morphism equality. Check at
  each WalkingSpan vertex:
  - `.zero`: `𝟙 ≫ 𝟙 = 𝟙`
  - `.left`: `𝟙 ≫ 𝟙 = 𝟙`
  - `.right`: `ι.app .right ≫ desc = 𝟙`
    where `desc` maps to `(f.right, f.hom, 𝟙)`.
    By `IsColimit.fac` at `.right`,
    `ι.app .right ≫ desc = 𝟙 f.right` ✓

- [ ] **Step 5: Assemble the adjunction and
  reflective instance**

  ```lean
  def arrowSpanAdj (pushouts : ...) :
      spanArrowReflector pushouts ⊣
        arrowSpanInclusion C := ...

  instance arrowSpanReflective (pushouts : ...) :
      Reflective (arrowSpanInclusion C) where
    L := spanArrowReflector pushouts
    adj := arrowSpanAdj pushouts
  ```

  Note: the `Reflective` instance takes
  `pushouts` as a parameter (not via typeclass).

- [ ] **Step 6: Build and verify**

  Run: `lake build GebLean.Utilities.ArrowSpanAdjunction`

- [ ] **Step 7: Commit**

  ```
  Prove arrow-span reflective adjunction
  ```

---

### Task 4: Presheaf Pushout Instantiation

**Files:**
- Modify: `GebLean/Utilities/ArrowSpanAdjunction.lean`

Provide `ColimitCocone` for presheaf span diagrams
using pointwise `Quot` in `Type w`. This refactors
the existing `Quot`-based code from
`PshRelEdgeFunctionalize.lean` into `ColimitCocone`
form.

- [ ] **Step 1: Define the pointwise pushout in
  `Type w`**

  Given `f : X → Y` and `g : X → Z` in `Type w`:

  Raw relation on `Y ⊕ Z`:
  ```lean
  fun a b => ∃ x, a = .inl (f x) ∧
    b = .inr (g x)
  ```

  Pushout object: `Quot rel`
  - `inl : Y → Quot rel` via `Quot.mk _ ∘ .inl`
  - `inr : Z → Quot rel` via `Quot.mk _ ∘ .inr`
  - Condition: `Quot.sound`
  - `desc`: `Quot.lift (Sum.elim h k) ...`
  - `fac`: by `Quot.lift` computation rule
  - `uniq`: by `funext` + `Quot.ind` + cases

  Package as `ColimitCocone (span f g)` for
  `Type w`.

- [ ] **Step 2: Lift to presheaf categories**

  For `f g : X ⟶ Y, X ⟶ Z` in `Cᵒᵖ ⥤ Type w`:

  The pushout presheaf has:
  - `obj c = Quot (rel c)` (pointwise quotient)
  - `map h = Quot.lift (Quot.mk _ ∘ Sum.map ...)
    (by Quot.sound + subfunctor map)`

  This is the same construction as the existing
  `pshRelFunctionalize` / `pshRelFunctionalizeMap`
  from `PshRelEdgeFunctionalize.lean`, generalized
  from relation projections to arbitrary span legs.

  The cocone legs are the pointwise `inl`/`inr`.

  `IsColimit`: `desc` is pointwise `Quot.lift`,
  `fac` by computation rule, `uniq` by `funext` +
  `Quot.ind` + cases at each stage.

  Package as a function
  `pshSpanPushouts : (S : WalkingSpan ⥤
  (Cᵒᵖ ⥤ Type w)) → ColimitCocone S`.

- [ ] **Step 3: Build and verify**

  Run: `lake build GebLean.Utilities.ArrowSpanAdjunction`

- [ ] **Step 4: Commit**

  ```
  Instantiate constructive pushouts for presheaves
  ```

---

### Task 5: Refactor PshRelEdgeFunctionalize

**Files:**
- Modify: `GebLean/PshRelEdgeFunctionalize.lean`

Replace the `Quot`-based presheaf functionalization
with a composition using the general adjunction.

The `PshRelEdge ↔ Arrow` adjunction CANNOT be
obtained by `Adjunction.comp` from the
`Span ↔ Arrow` and `PshRelEdge ↔ Span` adjunctions,
because `arrowSpanInclusion` and
`pshRelEdgeGraphFunctor ⋙ pshRelEdgeInclusionFunctor`
are naturally isomorphic but not definitionally equal
(the former uses apex = domain with `span (𝟙 P) f`,
the latter uses apex = graph subfunctor with
`span π₁ π₂`). Instead, we define
`pshRelEdgeFunctionalizeFunctor` as the composition
`pshRelEdgeInclusionFunctor ⋙ spanArrowReflector`
and build its adjunction with `pshRelEdgeGraphFunctor`
directly.

- [ ] **Step 1: Update imports**

  Add `import GebLean.Utilities.ArrowSpanAdjunction`
  to `PshRelEdgeFunctionalize.lean`.

- [ ] **Step 2: Remove the `Quot`-based definitions**

  Remove: `pshRelFunctionalizeRel`,
  `pshRelFunctionalizeMap`, `pshRelFunctionalizeMap_mk`,
  `pshRelFunctionalize`, `pshRelFunctionalizeHom`,
  `pshRelFunctionalizeQuotMapApp`,
  `pshRelFunctionalizeQuotMapApp_mk`,
  `pshRelFunctionalizeQuotMap`,
  `pshRelEdgeFunctionalizeUnitComp`,
  `pshRelEdgeFunctionalizeCounitApp`,
  `pshRelEdgeFunctionalizeCounitApp_mk`,
  `pshRelEdgeFunctionalizeCounitRight`,
  `pshRelEdgeFunctionalizeCounitComp`,
  `pshRelEdgeFunctionalizeAdjUnit`,
  `pshRelEdgeFunctionalizeAdjCounit`,
  `left_triangle_right_mk`.

- [ ] **Step 3: Redefine
  `pshRelEdgeFunctionalizeFunctor`**

  ```lean
  abbrev pshRelEdgeFunctionalizeFunctor
      (C : Type u) [Category.{v} C] :
      PshRelEdge.{u, v, w} C ⥤
      Arrow (Cᵒᵖ ⥤ Type w) :=
    pshRelEdgeInclusionFunctor C ⋙
      spanArrowReflector pshSpanPushouts
  ```

- [ ] **Step 4: Rebuild the adjunction**

  Build `pshRelEdgeFunctionalizeAdj :
  pshRelEdgeFunctionalizeFunctor C ⊣
  pshRelEdgeGraphFunctor` via
  `Adjunction.mkOfUnitCounit`, using:

  - Unit: compose `pshRelEdgeSepUnit` (edge → span)
    with the general unit (span → graph-span), then
    use the natural isomorphism between
    `arrowSpanInclusion` and `graph ⋙ inclusion`
    to land in the graph functor's image.

  - Alternatively (and more directly): define the
    unit from scratch as before — `srcMap = 𝟙`,
    `tgtMap = ι.app .right` (the pushout's right
    injection), `sq` by `Quot.sound` / cocone
    condition. The proofs are the same shape as
    the current ones but reference the pushout
    cocone instead of raw `Quot`.

  - Counit: define from scratch using
    `IsColimit.desc` on the graph's pushout.

  - Triangles: use `IsColimit.uniq` for the left
    triangle and `IsColimit.fac` for the right.

  Keep `pshRelEdgeGraphReflective` instance.

- [ ] **Step 5: Check for downstream references**

  ```bash
  grep -rn "pshRelFunctionalizeRel\|pshRelFunctionalize[^A-Z]\|pshRelFunctionalizeMap\|pshRelFunctionalizeHom\|pshRelFunctionalizeQuotMap" GebLean/
  ```

  Fix any references found (likely in
  `PshRelEdgeReflectiveChain.lean`).

- [ ] **Step 6: Build and test**

  Run: `lake build && lake test`

- [ ] **Step 7: Commit**

  ```
  Refactor PshRelEdge functionalization to use
  general arrow-span adjunction
  ```

---

### Task 6: Update Reflective Chain

**Files:**
- Modify: `GebLean/PshRelEdgeReflectiveChain.lean`

The reflective chain now includes the `Arrow ↔ Span`
step as an available adjunction. Update the chain
to reflect this and provide the `Arrow ↔ Span`
composed adjunctions.

- [ ] **Step 1: Add the `Arrow ↔ Span` step**

  Import `ArrowSpanAdjunction` and add:
  ```lean
  abbrev pshArrowSpanInclusion :=
    arrowSpanInclusion (Cᵒᵖ ⥤ Type w)

  def pshArrowSpanAdj :=
    arrowSpanAdj pshSpanPushouts

  instance : Reflective
      (pshArrowSpanInclusion (C := C)) :=
    arrowSpanReflective pshSpanPushouts
  ```

- [ ] **Step 2: Update composed adjunctions**

  The chain is now:
  ```
  PSh(C) ↪ Arrow(PSh(C)) ↪ Span(PSh(C))
  ```
  with `PshRelEdge(C) ↪ Span(PSh(C))` as a
  separate reflective inclusion.

  Update `pshSpanFromArrowInclusion` to use
  `arrowSpanInclusion` instead of
  `pshRelEdgeGraphFunctor ⋙
  pshRelEdgeInclusionFunctor`.

  Update `pshSpanFromArrowReflector` to use
  `spanArrowReflector` instead of
  `pshRelEdgeSepFunctor ⋙
  pshRelEdgeFunctionalizeFunctor`.

  Update the corresponding adjunctions and
  `Reflective` instances.

- [ ] **Step 3: Build and test**

  Run: `lake build && lake test`

- [ ] **Step 4: Commit**

  ```
  Update reflective chain with Arrow-Span step
  ```

---

### Task 7: Final Verification

**Files:**
- All modified files

- [ ] **Step 1: Full build and test**

  Run: `lake build && lake test`

- [ ] **Step 2: Verify axiom hygiene**

  ```bash
  grep -n "Classical\|noncomputable\|axiom\|sorry" \
    GebLean/Utilities/ArrowSpanAdjunction.lean \
    GebLean/PshRelEdgeFunctionalize.lean \
    GebLean/PshRelEdgeReflectiveChain.lean
  ```
  Expected: no matches.

- [ ] **Step 3: Verify no unused universe variables
  or `variable` declarations**

  Check each modified file for unused `universe`
  and `variable` declarations.

- [ ] **Step 4: Commit**

  ```
  Final verification of arrow-span adjunction
  generalization
  ```
