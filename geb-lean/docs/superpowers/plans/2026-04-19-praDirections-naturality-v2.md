# praDirections `(I, J, P)`-Naturality v2 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development
> (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use
> checkbox (`- [ ]`) syntax for tracking.

## Status (2026-04-20, revised)

Tasks 1–6 complete; Task 7 partial (two of six field-helpers committed);
Task 7 expanded into Tasks 7.1–7.12 (Phases 7A–7D) after a focused
subagent run surfaced that `fibHomCrossApp` is not definitionally
equal at its endpoints.  Tasks 8–22 unchanged.  Details and proof-
engineering notes in `.session/workstreams/presheaf-pra.md` under "v2
Progress (current, as of 2026-04-20)".

- **Task 1** — commit `b8fef801` (abbrevs).
- **Task 2** — commit `5d26d36b` (structure).
- **Task 3** — commits `04882518` (scaffold) + `2219249a` (extractor).
  Task 3 took substantial proof engineering: factored into nine small
  lemmas (`toHomUnop_id_fst`, `toHomUnop_id_snd`,
  `toHomUnop_id_endpoints_eq`, `toHomUnop_id`,
  `unop_comp_base_grothendieck`, `unop_comp_fiber_grothendieck`,
  `fibFib_map_comp_fiber`, `toHomUnop_comp_endpoints_eq`,
  `toHomUnop_comp`) with `Functor.congr_hom` as the crucial
  fused-vs-split transport step.  The plan's original Task 3
  `map_id`/`map_comp` proof sketches were not tractable as written;
  the implementation uses `rightOp` of a
  `Grothendieck.functorTo`-built functor instead.  Expect similar
  proof engineering in Task 7.
- **Task 4** — commit `37b8858d`.  Revised to a three-stage pipeline
  (`presheafCatFunctor ⋙ catULiftFunctor2 ⋙ Cat.opFunctor`) in
  commit `0753fd6a`; dropped the inner `Cat.opFunctor.op` stage
  because `(objBase X).2` already carries the `Iᵒᵖ` convention.
- **Task 5** — commit `b0dbd50e`.  Cat universe annotation widened
  to include `(u_I+1)`, `(v_I+1)` in the obj-level max, because
  `grothendieckContraFunctor` sees `Cat.{v_I, u_I}` itself as a
  type.
- **Task 6** — commit `42c75e74`.  Cat universe annotation widened
  analogously with `(u_I+1)`, `(v_I+1)`, `(u_J+1)`, `(v_J+1)`.
- **Task 7 (partial)** — `praPolyDirectionsData_baseFib` committed
  as `aad59f52`; `praPolyDirectionsData_fibFib` as `62b18098`.  Task
  7's remaining work (`fibHomCrossApp`, `fibHomCrossNat`, `baseHomId`,
  `baseHomComp`, and the `praPolyDirectionsData` bundle) is expanded
  into Tasks 7.1–7.12 below.  The expansion follows the
  unwidened-first approach: build the unwidened connecting morphism
  via `ccrNewFamilyFunctor.map` applied to an induced element-
  morphism, then widen via functoriality of `catULiftFunctor2 ⋙
  Cat.opFunctor` glued with `eqToHom`.  A focused subagent run
  stopped on direct construction of `fibHomCrossApp` because the
  endpoint-objects coincide only up to a propositional (not
  definitional) equality, which the expanded plan handles with named
  endpoint-equality lemmas.

**Goal:** Promote `praDirectionsAtFunctorOp` / `praDirectionsAtFunctor` in
`GebLean/PresheafPRA.lean` to a fully `(I, J, P)`-natural flat functor between two
Grothendiecks, delete the old per-`(I, J, P)` definitions plus `praPositionsPresheaf`,
rewrite the pointwise accessors (`praPositions`, `praDirectionsAt`) to route through
the flat functor, and remove the module-level `variable (P : PresheafPRACat …)`
declaration.

**Architecture:** A single flat functor `praPolyDirectionsFunctor :
praPolyDirectionsSource ⥤ praPolyDirectionsTarget` is built via a new utility
`FunctorBetweenCovContra` (U3) that packages data for functors between a
covariant-source Grothendieck and a contravariant-target Grothendieck.  The source is
the covariant Grothendieck of `functorFromDataContra sourceData` (already in the
file; base `(J, I, P)`, fibre widened `(P ⋙ ccrNewIndexFunctor _).Elements`);
the target is `(grothendieckContraFunctor Cat.{v_I, u_I}).obj praDirectionsTargetFibre`
with `praDirectionsTargetFibre : Catᵒᵖ ⥤ Cat` the pipeline
`Cat.opFunctor.op ⋙ presheafCatFunctor ⋙ catULiftFunctor2 ⋙ Cat.opFunctor`.  The
outer `Cat.opFunctor` embeds the polynomial-functor-morphism convention
(backward-on-directions) into the target's inherent contravariance.

**Tech Stack:** Lean 4 + mathlib `CategoryTheory`; `FunctorFromDataContra`,
`grothendieckContraFunctor`, and `FunctorBetween`-style bundled data from
`GebLean/Utilities/Grothendieck.lean`; `catULiftFunctor2` and `ccrNewFamilyNat` from
`GebLean/Utilities/Families.lean`.

## File Structure

**Modified:**

- `GebLean/Utilities/Grothendieck.lean` — adds `section FunctorBetweenCovContra`
  (U3): abbrevs, derived-equality lemmas, structure `FunctorBetweenCovContraData`,
  extractor `FunctorBetweenCovContra.toFunctor`.
- `GebLean/PresheafPRA.lean` — bulk of the change: adds target-fibre and
  total-Grothendieck definitions, the flat functor and its data bundle, the three
  bridge lemmas, rewrites `praPositions` and `praDirectionsAt`, deletes
  `praDirectionsAtFunctorOp`, `praDirectionsAtFunctor`, `praPositionsPresheaf`,
  removes `variable (P …)`, audits `variable (I …)` / `variable (J …)`.
- `GebLean/PresheafPRAUMorph.lean` — one proof block in
  `praReassemble_directions` (lines 1230-1238) to stop `unfold`-ing the deleted
  `praDirectionsAtFunctor` / `praDirectionsAtFunctorOp`.
- `GebLeanTests.lean` — adds one import line.
- `.session/workstreams/presheaf-pra.md`,
  `.session/workstreams/pra-universal-morphisms.md` — rename stale references.

**Created:**

- `GebLeanTests/Utilities/PresheafPRADirNat.lean` — new test file covering
  type-signature sanity, bridge-lemma collapse, pointwise-accessor compatibility,
  functoriality at a concrete morphism, and universe polymorphism.

## Conventions used throughout the plan

Every task ends with a build+test step followed by a commit.  The build and test
commands are:

```bash
lake build
lake test
```

Both must complete with zero warnings (`CLAUDE.md` bans `sorry`, `admit`,
unused-variable warnings, and all other linter warnings).  Never use `lake clean`.
Never use `lake env lean`.  When a step modifies a Lean file, run `lake build` first;
run `lake test` only when the change could affect test output (generally Tasks 16
onward).  Use the following commit-message convention: `<scope>: <summary>` where
`<scope>` is one of `grothendieck`, `presheaf-pra`, `tests`, `session`.

Universe parameters referenced in this plan match the declarations already present
in `GebLean/PresheafPRA.lean:34`:

```lean
universe u_I v_I u_J v_J w_I w'
```

---

## Task 1: Scaffold `FunctorBetweenCovContra` abbrevs (U3 part 1)

**Files:**

- Modify: `GebLean/Utilities/Grothendieck.lean` — append a new section after the
  existing `section FunctorBetweenContra` (ending at line 5137), before the start of
  the following `section NatTransBetweenContra` at line 5148.

**What this task does:** Ports the abbrev-level type signatures from
`FunctorBetween` (lines 4423-4557) to the mixed covariant-source /
contravariant-target case.  No structure or extractor yet — this task only
introduces the abbrevs and two derivation lemmas so that subsequent tasks have a
compiling scaffold to extend.  The covariant source `G : C ⥤ Cat.{vC, uC}` and the
contravariant target `F : Dᵒᵖ ⥤ Cat.{vD, uD}` yield a target-side
`grothendieckContraFunctor`, whose morphism direction flips the fibre direction
relative to `FunctorBetween`.

- [ ] **Step 1: Add the abbrev block in `Grothendieck.lean`**

Insert the following block immediately after the `end FunctorBetweenContra` line
(line 5137 in the current file) and before the blank line preceding
`section NatTransBetweenContra`:

```lean
/-!
## Functors Between Covariant and Contravariant Grothendieck Constructions

This section defines bundled data for functors between a covariant source
Grothendieck and a contravariant target Grothendieck,
`Grothendieck G ⥤ (grothendieckContraFunctor D).obj F`, where `G : C ⥤ Cat` and
`F : Dᵒᵖ ⥤ Cat`.

A functor between these is characterized by:
- A base functor `baseFib : C ⥤ D`.
- For each `c : C`, a functor `fibFib c : G.obj c ⥤ F.obj (op (baseFib.obj c))`.
- Cross-fiber morphisms whose direction is the contravariant-target one:
  `(fibFib c).obj x ⟶ (F.map (baseFib.map f).op).obj ((fibFib c').obj ((G.map f).obj x))`.
-/

section FunctorBetweenCovContra

universe vC vD uC uD

variable {C : Type uC} [Category.{vC} C] (G : C ⥤ Cat.{vC, uC})
variable {D : Type uD} [Category.{vD} D] (F : Dᵒᵖ ⥤ Cat.{vD, uD})

/--
The base-fibre functor for the mixed case: assigns to each `c : C` a base object
in `D`.
-/
abbrev FunctorBetweenCovContraBaseFib := C ⥤ D

/--
The fibre-fibre functor: for each `c : C`, a functor
`G.obj c ⥤ F.obj (op (baseFib.obj c))`.  The `op` reflects the contravariant
target's `Dᵒᵖ`-indexing.
-/
abbrev FunctorBetweenCovContraFibFib
    (baseFib : FunctorBetweenCovContraBaseFib (C := C) (D := D)) :=
  ∀ c, G.obj c ⥤ F.obj (Opposite.op (baseFib.obj c))

/--
The cross-fibre morphism component.  For `f : c ⟶ c'` and `x : G.obj c`,
a morphism from `(fibFib c).obj x` to
`(F.map (baseFib.map f).op).obj ((fibFib c').obj ((G.map f).obj x))`.

This direction is correct for a morphism in `(grothendieckContraFunctor D).obj F`
from `(baseFib.obj c, (fibFib c).obj x)` to
`(baseFib.obj c', (fibFib c').obj ((G.map f).obj x))`.
-/
abbrev FunctorBetweenCovContraFibHomCrossApp
    (baseFib : FunctorBetweenCovContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenCovContraFibFib G F baseFib) :=
  ∀ {c c' : C} (f : c ⟶ c') (x : G.obj c),
    (fibFib c).obj x ⟶
      (F.map (baseFib.map f).op).toFunctor.obj
        ((fibFib c').obj ((G.map f).toFunctor.obj x))

/--
Naturality of `fibHomCrossApp`: for `f : c ⟶ c'` and `g : x ⟶ y` in `G.obj c`,
the square commutes.
-/
abbrev FunctorBetweenCovContraFibHomCrossNat
    (baseFib : FunctorBetweenCovContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenCovContraFibFib G F baseFib)
    (fibHomCrossApp :
      FunctorBetweenCovContraFibHomCrossApp G F baseFib fibFib) :=
  ∀ {c c' : C} (f : c ⟶ c') {x y : G.obj c} (g : x ⟶ y),
    (fibFib c).map g ≫ fibHomCrossApp f y =
      fibHomCrossApp f x ≫
        (F.map (baseFib.map f).op).toFunctor.map
          ((fibFib c').map ((G.map f).toFunctor.map g))

/--
Equality of fibre-fibre values at identity.  Since
`baseFib.map (𝟙 c) = 𝟙 (baseFib.obj c)` and `F.map (𝟙 _).op = 𝟭 _`, the source
and target of `fibHomCrossApp (𝟙 c) x` coincide with `(fibFib c).obj x`.
-/
abbrev FunctorBetweenCovContraBaseHomEqId
    (baseFib : FunctorBetweenCovContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenCovContraFibFib G F baseFib) :=
  ∀ (c : C) (x : G.obj c),
    (fibFib c).obj x =
      (F.map (baseFib.map (𝟙 c)).op).toFunctor.obj
        ((fibFib c).obj ((G.map (𝟙 c)).toFunctor.obj x))

/--
Derive the identity equality from functor laws.
-/
lemma functorBetweenCovContraBaseHomEqIdProof
    (baseFib : FunctorBetweenCovContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenCovContraFibFib G F baseFib) :
    FunctorBetweenCovContraBaseHomEqId G F baseFib fibFib := by
  intro c x
  have hG : (G.map (𝟙 c)).toFunctor = 𝟭 _ :=
    congrArg Cat.Hom.toFunctor (G.map_id c) |>.trans (Cat.id_eq_id _)
  have hF : (F.map (𝟙 (Opposite.op (baseFib.obj c)))).toFunctor = 𝟭 _ :=
    congrArg Cat.Hom.toFunctor (F.map_id _) |>.trans (Cat.id_eq_id _)
  simp only [baseFib.map_id, op_id, hG, hF, Functor.id_obj]

/--
Equality of fibre-fibre values at composition.  For `f : c ⟶ c'` and
`g : c' ⟶ c''`, the two ways of transporting
`(fibFib c'').obj ((G.map (f ≫ g)).obj x)` back to
`F.obj (op (baseFib.obj c))` agree.
-/
abbrev FunctorBetweenCovContraBaseHomEqComp
    (baseFib : FunctorBetweenCovContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenCovContraFibFib G F baseFib) :=
  ∀ {c c' c'' : C} (f : c ⟶ c') (g : c' ⟶ c'') (x : G.obj c),
    (F.map (baseFib.map (f ≫ g)).op).toFunctor.obj
        ((fibFib c'').obj ((G.map (f ≫ g)).toFunctor.obj x)) =
      (F.map (baseFib.map f).op).toFunctor.obj
        ((F.map (baseFib.map g).op).toFunctor.obj
          ((fibFib c'').obj
            ((G.map g).toFunctor.obj ((G.map f).toFunctor.obj x))))

/--
Derive the composition equality from functor laws.
-/
lemma functorBetweenCovContraBaseHomEqCompProof
    (baseFib : FunctorBetweenCovContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenCovContraFibFib G F baseFib) :
    FunctorBetweenCovContraBaseHomEqComp G F baseFib fibFib := by
  intro c c' c'' f g x
  have hbase : (baseFib.map (f ≫ g)).op =
      (baseFib.map g).op ≫ (baseFib.map f).op := by
    rw [baseFib.map_comp]; rfl
  have hF := congrArg Cat.Hom.toFunctor
    (F.map_comp (baseFib.map g).op (baseFib.map f).op)
  have hG := congrArg Cat.Hom.toFunctor (G.map_comp f g)
  rw [hbase, congrFun (congrArg Functor.obj hF) _,
    congrFun (congrArg Functor.obj hG.symm) _]

/--
Identity coherence: `fibHomCrossApp (𝟙 c) x` equals the derived `eqToHom`.
-/
abbrev FunctorBetweenCovContraBaseHomId
    (baseFib : FunctorBetweenCovContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenCovContraFibFib G F baseFib)
    (fibHomCrossApp :
      FunctorBetweenCovContraFibHomCrossApp G F baseFib fibFib) :=
  ∀ (c : C) (x : G.obj c),
    fibHomCrossApp (𝟙 c) x =
      eqToHom
        (functorBetweenCovContraBaseHomEqIdProof G F baseFib fibFib c x)

/--
Composition coherence: `fibHomCrossApp (f ≫ g) x` decomposes as
`fibHomCrossApp f x` followed by transport of `fibHomCrossApp g ((G.map f).obj x)`
through `F.map (baseFib.map f).op`, adjusted by `eqToHom`.
-/
abbrev FunctorBetweenCovContraBaseHomComp
    (baseFib : FunctorBetweenCovContraBaseFib (C := C) (D := D))
    (fibFib : FunctorBetweenCovContraFibFib G F baseFib)
    (fibHomCrossApp :
      FunctorBetweenCovContraFibHomCrossApp G F baseFib fibFib) :=
  ∀ {c c' c'' : C} (f : c ⟶ c') (g : c' ⟶ c'') (x : G.obj c),
    fibHomCrossApp (f ≫ g) x =
      fibHomCrossApp f x ≫
        (F.map (baseFib.map f).op).toFunctor.map
          (fibHomCrossApp g ((G.map f).toFunctor.obj x)) ≫
        eqToHom
          (functorBetweenCovContraBaseHomEqCompProof G F baseFib fibFib f g x)

end FunctorBetweenCovContra
```

- [ ] **Step 2: Build and verify**

Run: `lake build`
Expected: success with zero warnings.  If `functorBetweenCovContraBaseHomEqIdProof`
or `functorBetweenCovContraBaseHomEqCompProof` fails to compile, inspect the goal
state with `mcp__lean-lsp__lean_goal` at the failing `by` block and adjust the
proof.  The proofs must succeed without tactic automation beyond `rfl`, `simp only`
with named lemmas, `rw`, and `show`.

- [ ] **Step 3: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "grothendieck: add FunctorBetweenCovContra abbrevs (U3 part 1)"
```

---

## Task 2: Add `FunctorBetweenCovContraData` structure (U3 part 2)

**Files:**

- Modify: `GebLean/Utilities/Grothendieck.lean` — inside the same
  `section FunctorBetweenCovContra` added in Task 1, immediately before the
  `end FunctorBetweenCovContra` line.

- [ ] **Step 1: Add the structure**

Insert just before `end FunctorBetweenCovContra`:

```lean
/--
Bundled data for a functor between a covariant source and a contravariant target
Grothendieck construction, `Grothendieck G ⥤ (grothendieckContraFunctor D).obj F`.

Objects map `(c, x) ↦ mkObj (baseFib.obj c) ((fibFib c).obj x)`; morphisms compose
`fibHomCrossApp f x` with `(fibFib c').map (Grothendieck.Hom.fiber _)`.
-/
structure FunctorBetweenCovContraData where
  /-- The base functor `C ⥤ D`. -/
  baseFib : FunctorBetweenCovContraBaseFib (C := C) (D := D)
  /-- Fibre functors: `G.obj c ⥤ F.obj (op (baseFib.obj c))`. -/
  fibFib : FunctorBetweenCovContraFibFib G F baseFib
  /-- Cross-fibre morphisms in the contravariant-target direction. -/
  fibHomCrossApp :
    FunctorBetweenCovContraFibHomCrossApp G F baseFib fibFib
  /-- Naturality of cross-fibre morphisms. -/
  fibHomCrossNat :
    FunctorBetweenCovContraFibHomCrossNat G F baseFib fibFib fibHomCrossApp
  /-- Identity coherence. -/
  baseHomId :
    FunctorBetweenCovContraBaseHomId G F baseFib fibFib fibHomCrossApp
  /-- Composition coherence. -/
  baseHomComp :
    FunctorBetweenCovContraBaseHomComp G F baseFib fibFib fibHomCrossApp
```

- [ ] **Step 2: Build and verify**

Run: `lake build`
Expected: success with zero warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "grothendieck: add FunctorBetweenCovContraData structure (U3 part 2)"
```

---

## Task 3: Add `FunctorBetweenCovContra.toFunctor` extractor (U3 part 3)

**Files:**

- Modify: `GebLean/Utilities/Grothendieck.lean` — inside `section
  FunctorBetweenCovContra`, immediately before the `end FunctorBetweenCovContra`
  line (now at the new position after Task 2).

**What this task does:** Constructs the flat functor from
`FunctorBetweenCovContraData` directly, using `mkObj` / `mkHom` from the
`GrothendieckContraFunctor` namespace rather than going through
`FunctorTo`/`pre`/`FunctorFrom` as the existing `toFunctorViaPre` does.  The direct
construction is simpler because the target's morphism structure is already captured
by `mkHom`'s signature.

- [ ] **Step 1: Add the extractor**

Insert just before `end FunctorBetweenCovContra`:

```lean
namespace FunctorBetweenCovContraData

open GrothendieckContraFunctor in
/--
Construct a functor `Grothendieck G ⥤ (grothendieckContraFunctor D).obj F` from
bundled `FunctorBetweenCovContraData`.
-/
def toFunctor (data : FunctorBetweenCovContraData G F) :
    Grothendieck G ⥤ (grothendieckContraFunctor D).obj F where
  obj X :=
    GrothendieckContraFunctor.mkObj
      (F := F) (data.baseFib.obj X.base)
      ((data.fibFib X.base).obj X.fiber)
  map {X Y} f :=
    GrothendieckContraFunctor.mkHom
      (F := F)
      (data.baseFib.map f.base)
      (data.fibHomCrossApp f.base X.fiber ≫
        (F.map (data.baseFib.map f.base).op).toFunctor.map
          ((data.fibFib Y.base).map f.fiber))
  map_id X := by
    refine congrArg (Quiver.Hom.op ∘ fun h => (h : _)) ?_
    -- Unfold mkHom / Grothendieck.id_fiber / baseHomId to reduce to reflexivity.
    apply Grothendieck.ext
    · simp [GrothendieckContraFunctor.mkHom, data.baseFib.map_id,
        Grothendieck.id_base, Grothendieck.id_fiber]
    · simp only [GrothendieckContraFunctor.mkHom, Grothendieck.id_base,
        Grothendieck.id_fiber, data.baseHomId,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id,
        eqToHom_map]
      rfl
  map_comp {X Y Z} f g := by
    apply Grothendieck.ext
    · simp [GrothendieckContraFunctor.mkHom, data.baseFib.map_comp,
        Grothendieck.comp_base]
    · -- The composition coherence reduces to `baseHomComp`, `fibHomCrossNat`,
      -- and `data.fibFib Z.base .map_comp`.  Destructure fibres and close.
      simp only [GrothendieckContraFunctor.mkHom,
        Grothendieck.comp_base, Grothendieck.comp_fiber,
        data.baseFib.map_comp, data.baseHomComp f.base g.base X.fiber,
        CategoryTheory.Functor.map_comp, Category.assoc]
      -- Shift the eqToHom produced by baseHomComp and apply fibHomCrossNat.
      have hnat := data.fibHomCrossNat g.base f.fiber
      -- Remaining tactic plumbing: rewrite with hnat, cancel eqToHom_trans.
      simp only [hnat, Category.assoc, eqToHom_trans, eqToHom_refl,
        Category.comp_id]
      rfl

end FunctorBetweenCovContraData
```

**Note on the proofs:** the proof bodies above are the expected shapes, but during
implementation the subagent may need to adjust specific tactic steps (the order of
`simp only` rewrites, use of `obtain ⟨⟩` to destructure, explicit `Grothendieck.ext`
arguments).  If the proofs fail, split them into named helper lemmas using the
factoring-out technique described in `CLAUDE.md`.  Use
`mcp__lean-lsp__lean_goal` to inspect intermediate goals.

- [ ] **Step 2: Build and verify**

Run: `lake build`
Expected: success with zero warnings.

If the proofs are intractable, factor them into helper lemmas:

```lean
private lemma toFunctor_map_id_fiber
    (data : FunctorBetweenCovContraData G F) (X : Grothendieck G) : … := …
private lemma toFunctor_map_comp_fiber
    (data : FunctorBetweenCovContraData G F)
    {X Y Z : Grothendieck G} (f : X ⟶ Y) (g : Y ⟶ Z) : … := …
```

and reference them inside `toFunctor`.

- [ ] **Step 3: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "grothendieck: add FunctorBetweenCovContra.toFunctor extractor (U3 part 3)"
```

---

## Task 4: Define `praDirectionsTargetFibre`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — append after the existing `sourceData`
  declaration (line 334) and before `praPositionsNatTarget` (line 345).

**What this task does:** Defines the per-`I` target fibre functor as a three-stage
pipeline: `presheafCatFunctor`, `catULiftFunctor2`, and outer `Cat.opFunctor`.  The
outer op embeds the polynomial-functor-morphism backward-on-directions convention
into the target's Grothendieck structure.  The plan's original four-stage form had
an inner `Cat.opFunctor.op` that over-applied op relative to the `(objBase X).2 =
Cat.of Iᵒᵖ` convention carried by `presheafPRACatBifunctorUncurriedOp`'s base; the
inner op was dropped during implementation (commit `0753fd6a`).

- [ ] **Step 1: Add the definition**

Insert after line 334 (after `sourceData`):

```lean
/--
Per-`I` target fibre for `praPolyDirectionsTarget`.  The input Cat
already carries the `Iᵒᵖ` convention coming from
`presheafPRACatBifunctorUncurriedOp`'s base; this pipeline widens the
presheaf category and post-composes with `Cat.opFunctor` to encode the
polynomial-functor-morphism backward-on-directions convention.

Three-stage pipeline: `presheafCatFunctor ⋙ catULiftFunctor2 ⋙
Cat.opFunctor`:
1. `presheafCatFunctor` maps `op (Cat.of Iᵒᵖ)` to the presheaf
   category `Iᵒᵖ ⥤ Type w_I`.
2. `catULiftFunctor2` widens that category's universe to match
   `praPolyDirectionsSource`'s Cat universe.
3. `Cat.opFunctor` takes the opposite, encoding the polynomial-
   functor-morphism backward-on-directions convention.
-/
def praDirectionsTargetFibre :
    Cat.{v_I, u_I}ᵒᵖ ⥤
      Cat.{max u_I u_J v_J w_I w',
        max u_I u_J v_I v_J (w_I + 1) (w' + 1)} :=
  presheafCatFunctor.{u_I, v_I, w_I} ⋙
    catULiftFunctor2.{max v_I (w_I + 1) u_I, max u_I w_I,
      max u_I u_J v_J w_I w',
      max u_I u_J v_I v_J (w_I + 1) (w' + 1)} ⋙
    Cat.opFunctor.{max u_I u_J v_J w_I w',
      max u_I u_J v_I v_J (w_I + 1) (w' + 1)}
```

- [ ] **Step 2: Build and verify**

Run: `lake build`
Expected: success with zero warnings.

If the universe annotations for `catULiftFunctor2` don't align (build error on
universe unification), check `GebLean/Utilities/Families.lean` for the
`catULiftFunctor2` declaration and match its universe parameters to the Cat
universe of `praPositionsNatTarget` (the nearby existing declaration at
PresheafPRA.lean:345).

- [ ] **Step 3: Add a type-check example (inline)**

Add a `#check` directly below the definition to pin the Cat universe signature:

```lean
#check @praDirectionsTargetFibre.{0, 0, 0, 0, 0, 0}
```

- [ ] **Step 4: Build and verify**

Run: `lake build`
Expected: success with zero warnings.  The `#check` should print a clean type.

- [ ] **Step 5: Remove the `#check` and commit**

Remove the `#check` line (it was a sanity probe).

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praDirectionsTargetFibre"
```

---

## Task 5: Define `praPolyDirectionsTarget`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — append immediately after
  `praDirectionsTargetFibre`.

- [ ] **Step 1: Add the definition**

```lean
/--
Total target Grothendieck for `praPolyDirectionsFunctor`.

Objects are pairs `(I, x)` where `x : (widened Iᵒᵖ ⥤ Type w_I)ᵒᵖ`.
Morphisms `(I₁, x₁) ⟶ (I₂, x₂)` are pairs `(f : I₁ ⟶ I₂,
η : x₁ ⟶ (praDirectionsTargetFibre.map f.op).obj x₂)`.  Unfolded, η is a
nat-trans in the opposite direction in `widened I₁ᵒᵖ ⥤ Type w_I` — the
polynomial-functor-morphism backward-on-directions shape.
-/
def praPolyDirectionsTarget :
    Cat.{max u_I u_J v_I v_J w_I w',
      max (u_I + 1) (v_I + 1) u_J v_J (w_I + 1) (w' + 1)} :=
  (grothendieckContraFunctor Cat.{v_I, u_I}).obj
    praDirectionsTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'}
```

- [ ] **Step 2: Build and verify**

Run: `lake build`
Expected: success with zero warnings.  If the Cat universe of
`praPolyDirectionsTarget` doesn't match (because `grothendieckContraFunctor`'s
output universe depends on its input-Cat universe), inspect
`grothendieckContraFunctor`'s definition at `Grothendieck.lean:7082` and adjust
`praPolyDirectionsTarget`'s annotated universe accordingly.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyDirectionsTarget"
```

---

## Task 6: Define `praPolyDirectionsSource`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — append after `praPolyDirectionsTarget`.

**What this task does:** Packages the covariant Grothendieck of
`functorFromDataContra sourceData` as a named Cat-level definition for symmetric
naming with `praPolyDirectionsTarget`.  Objects are 4-tuples `((J, I), P, e)` where
`e : (sourceDataFib (J, I)).obj P`.

- [ ] **Step 1: Add the definition**

```lean
/--
Total source Grothendieck for `praPolyDirectionsFunctor`.

Objects are 4-tuples: a base object `X` of
`(grothendieckContraFunctor (Cat × Cat)).obj presheafPRACatBifunctorUncurriedOp`
— itself a triple `((J, I), P)` — and an element
`e : (sourceDataFib (J, I)).obj P`.
-/
def praPolyDirectionsSource :
    Cat.{max u_I u_J v_I v_J w_I w',
      max (u_I + 1) (v_I + 1) (u_J + 1) (v_J + 1) (w_I + 1)
        (w' + 1)} :=
  Cat.of (Grothendieck
    (functorFromDataContra sourceData.{u_I, v_I, u_J, v_J, w_I, w'}))
```

- [ ] **Step 2: Build and verify**

Run: `lake build`
Expected: success with zero warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyDirectionsSource"
```

---

## Task 7: Build `praPolyDirectionsData` bundle (expanded into Phases 7A–7D)

**Overview.** The `FunctorBetweenCovContraData` bundle has six fields.  Two
have already been committed as named private helpers outside the bundle:
`praPolyDirectionsData_baseFib` (commit `aad59f52`) and
`praPolyDirectionsData_fibFib` (commit `62b18098`).  The remaining four
fields — `fibHomCrossApp`, `fibHomCrossNat`, `baseHomId`, `baseHomComp` —
plus the bundle-assembly step are expanded into the phases and sub-tasks
below.

The main difficulty, surfaced by a prior focused subagent run, is that
`fibHomCrossApp f x` has endpoints that are not definitionally equal:
the LHS is `op(widened(ccrNewFamily P₁ (unwiden x)))` while the RHS is
`(F.map (f_I).op).obj (op(widened(ccrNewFamily P₂ (reindexed x))))`,
which unfolds to `op(widened(f_I.op ⋙ ccrNewFamily P₂ (reindexed x)))`.
These agree on the nose only after applying the object-level naturality
of `ccrNewFamilyFunctor` in its Cat parameter, followed by a widening
interchange.

The expansion uses the **unwidened-first** approach: construct an
unwidened natural transformation via `ccrNewFamilyFunctor.map` applied
to the element-morphism induced by `homFiber f`, then widen through
`catULiftFunctor2 ⋙ Cat.opFunctor` glued with `eqToHom`.

**Phase layout:**

- **Phase 7A — Utility lemma in `Families.lean`** (Task 7.1).
- **Phase 7A' — U3 universe generalization in `Grothendieck.lean`**
  (Task 7.3.5, discovered 2026-04-20).
- **Phase 7B — `fibHomCrossApp` construction** (Tasks 7.2–7.4).
- **Phase 7C — Coherence proofs** (Tasks 7.5–7.10).
- **Phase 7D — Bundle assembly** (Task 7.11).

**Revision history of the expansion:** An earlier revision had a
dedicated sub-task for `praPolyDirectionsData_elemMor`, intended to
package an `(NatTrans.mapElements ...).obj e` call producing an
*object* in a reindexed elements category.  That helper turned out to
be unused downstream: Task 7.3 below builds the cross-fibre morphism
directly from `(homFiber f).app e.fst` as a morphism in
`(ccrNewIndexFunctor _).Elements`, without going through
`NatTrans.mapElements`.  The earlier sub-task was reverted (commit
`34a0a36d`) and merged into the simplified Task 7.3.

**Note for Tasks 7.5, 7.7, 7.9 implementers:** The skeletons for
`fibHomCrossNat_unwidened`, `baseHomId_unwidened`, and
`baseHomComp_unwidened` below were written assuming the `elemMor`
intermediate helper would exist.  Since it does not, adapt each
skeleton by:

- Reading `fibHomCrossUnwidened f e` directly as
  `(ccrNewFamilyFunctor _).map ⟨(homFiber f).app e.fst, rfl⟩`, and
- Deriving the required naturality/identity/composition relations from
  `ccrNewFamilyFunctor`'s functoriality (`map_id`, `map_comp`) combined
  with the `(homFiber f).app`-at-`e.fst` shape.

In practice this simplifies the proofs — no intermediate naturality
of `NatTrans.mapElements` needed.  Use `mcp__lean-lsp__lean_goal` at
each proof step to confirm the expected goal shape.

Each sub-task is self-contained with a file target, code skeleton,
build/commit cycle.  Scoped commit prefix for `Families.lean` edits is
`families`; for `PresheafPRA.lean` edits it is `presheaf-pra`.

**Fallback doctrine for every sub-task.**  If a proof step resists
closure via the tactics spelled out, apply `CLAUDE.md`'s factoring-out-
lemmas technique recursively: replace the unproven step with an
underscore, extract a smaller named helper, dispatch the current goal
by transitivity against the new helper, and prove the helper
separately.  Do not substitute `sorry`, `admit`, or `by exact?`.

---

### Task 7.1: Add `ccrNewFamilyFunctor_obj_naturality` in `Families.lean`

**Files:**

- Modify: `GebLean/Utilities/Families.lean` — insert immediately after
  `ccrNewFamilyFunctor_naturality` (currently at line 3436).

**What this task does:** Adds a public object-level counterpart of the
existing private morphism-level naturality lemma.  The equation is
`rfl`-provable by how `coprodCovarRepFunctor.map F` post-composes
fibres with `F`.  This becomes the bridge that `fibHomCrossApp` uses
to align endpoint objects.

- [ ] **Step 1: Add the lemma**

Insert after `ccrNewFamilyFunctor_naturality`:

```lean
/--
Object-level naturality of `ccrNewFamilyFunctor` in `C`.  For
`F : C ⟶ D` in `Cat` and `e : (ccrNewIndexFunctor C).Elements`,
applying `ccrNewFamilyFunctor D` to the reindexed object equals
applying `F.op` to the result of `ccrNewFamilyFunctor C`.  Holds
by `rfl` because `coprodCovarRepFunctor.map F` post-composes
fibres with `F`.
-/
theorem ccrNewFamilyFunctor_obj_naturality
    {C D : Cat.{v, u}} (F : C ⟶ D)
    (e : (ccrNewIndexFunctor.{u, v, w} C.α).Elements) :
    (ccrNewFamilyFunctor.{u, v, w} D.α).obj
        ((ccrElementsFunctor.map.{u, v, w} F).obj e) =
      (Cat.opFunctor.{v, u}.map F).toFunctor.obj
        ((ccrNewFamilyFunctor.{u, v, w} C.α).obj e) :=
  rfl
```

- [ ] **Step 2: Build**

Run: `lake build`
Expected: success with zero warnings.  If `rfl` fails, inspect the two
sides with `mcp__lean-lsp__lean_goal` and apply `dsimp only
[ccrNewFamilyFunctor, ccrElementsFunctor.map, Cat.opFunctor,
Functor.op_obj, coprodCovarRepFunctor, freeProdCompletionFunctor,
familyBifunctor]` before the `rfl`.  If still not `rfl`, factor out
an intermediate `ccrNewFamily_reindex_eq` helper.

- [ ] **Step 3: Commit**

```bash
git add GebLean/Utilities/Families.lean
git commit -m "families: add ccrNewFamilyFunctor_obj_naturality"
```

---

### Task 7.2: Add unwidened-source accessor for `praPolyDirectionsData_fibFib`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert immediately after
  `praPolyDirectionsData_fibFib` (currently at line 411).

**What this task does:** Introduces a named `private def` that unwraps
the widened fibre element through `ULiftHom.down ⋙ ULift.downFunctor`,
returning a raw `(P ⋙ ccrNewIndexFunctor _).Elements` value.  Used as a
building block for the unwidened connecting morphism in Task 7.3.

- [ ] **Step 1: Add the definition**

Insert after `praPolyDirectionsData_fibFib`:

```lean
/--
Unwiden a widened fibre element of the source Grothendieck back to an
element of `(objFiber X ⋙ ccrNewIndexFunctor (presheafCat (objBase
X).2)).Elements`.  The inverse of the `catULiftFunctor2` widening used
inside `sourceDataFib`.
-/
private def praPolyDirectionsData_unwidenFiber
    (X : (grothendieckContraFunctor
        (Cat.{v_J, u_J} × Cat.{v_I, u_I})).obj
      presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'}) :
    (functorFromDataContra
        sourceData.{u_I, v_I, u_J, v_J, w_I, w'}).obj X ⥤
      (GrothendieckContraFunctor.objFiber X ⋙
        ccrNewIndexFunctor.{max v_I u_I (w_I + 1),
          max u_I w_I, w'}
          (↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
            (Opposite.op
              (GrothendieckContraFunctor.objBase X).2)))).Elements :=
  show CategoryTheory.ULiftHom
      (ULift
        ((GrothendieckContraFunctor.objFiber X ⋙
          ccrNewIndexFunctor.{max v_I u_I (w_I + 1),
            max u_I w_I, w'}
            (↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
              (Opposite.op
                (GrothendieckContraFunctor.objBase X).2)))
        ).Elements)) ⥤ _ from
  CategoryTheory.ULiftHom.down ⋙
    CategoryTheory.ULift.downFunctor
```

- [ ] **Step 2: Build**

Run: `lake build`
Expected: success with zero warnings.  If `ULiftHom.down`'s `C` argument
does not resolve, adjust the leading `show` to mirror the form used at
the start of `praPolyDirectionsData_fibFib`'s body (lines 422-430).

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyDirectionsData_unwidenFiber"
```

---

### Task 7.3: Add `praPolyDirectionsData_fibHomCrossUnwidened`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyDirectionsData_unwidenFiber`.

**What this task does:** Constructs the unwidened cross-fibre morphism
— the pre-widening content of `fibHomCrossApp`.  The construction is
direct: `(ccrNewFamilyFunctor _).map` applied to an
`(ccrNewIndexFunctor _).Elements`-category morphism built from
`(homFiber f).app e.fst` with `rfl` index-preservation proof.

- [ ] **Step 1: Add the definition**

Proposed skeleton (names and destructuring syntax may need minor
adjustment — see Notes):

```lean
/--
Unwidened cross-fibre morphism underlying `fibHomCrossApp f e` for a
source-Grothendieck morphism `f : X₁ ⟶ X₂` and unwidened element `e`
of `(objFiber X₁ ⋙ ccrNewIndexFunctor _).Elements`.

Built by applying `(ccrNewFamilyFunctor _).map` to the
`(ccrNewIndexFunctor _).Elements`-morphism
`⟨(homFiber f).app e.fst, rfl⟩`.  The source endpoint is the
transported element `⟨(objFiber X₁).obj e.fst, e.snd⟩` (obtained
via `(elementsPrecomp (objFiber X₁)).obj e`); the target endpoint
is `⟨((F.map (homBase f).op).obj (objFiber X₂)).obj e.fst,
ccrNewReindex ((homFiber f).app e.fst) e.snd⟩`, where `F` denotes
`presheafPRACatBifunctorUncurriedOp`.
-/
private def praPolyDirectionsData_fibHomCrossUnwidened
    {X₁ X₂ : (grothendieckContraFunctor
        (Cat.{v_J, u_J} × Cat.{v_I, u_I})).obj
      presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'}}
    (f : X₁ ⟶ X₂)
    (e : (GrothendieckContraFunctor.objFiber X₁ ⋙
        ccrNewIndexFunctor.{max v_I u_I (w_I + 1),
          max u_I w_I, w'}
          (↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
            (Opposite.op
              (GrothendieckContraFunctor.objBase X₁).2))))
      .Elements) :
    (ccrNewFamilyFunctor.{max v_I u_I (w_I + 1), max u_I w_I, w'}
        (↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
          (Opposite.op
            (GrothendieckContraFunctor.objBase X₁).2)))).obj
        ⟨(GrothendieckContraFunctor.objFiber X₁).obj e.fst,
          e.snd⟩ ⟶
      (ccrNewFamilyFunctor.{max v_I u_I (w_I + 1), max u_I w_I, w'}
        (↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
          (Opposite.op
            (GrothendieckContraFunctor.objBase X₁).2)))).obj
        ⟨((presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
            w_I, w'}.map
            (GrothendieckContraFunctor.homBase f).op).toFunctor.obj
          (GrothendieckContraFunctor.objFiber X₂)).obj e.fst,
          ccrNewReindex.{max v_I u_I (w_I + 1), max u_I w_I, w'}
            ((GrothendieckContraFunctor.homFiber f).app e.fst)
            e.snd⟩ :=
  (ccrNewFamilyFunctor.{max v_I u_I (w_I + 1), max u_I w_I, w'}
      (↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
        (Opposite.op
          (GrothendieckContraFunctor.objBase X₁).2)))).map
    ⟨(GrothendieckContraFunctor.homFiber f).app e.fst, rfl⟩
```

**Notes on adjustment.**

1. The two endpoint-object expressions use the `⟨_, _⟩` anonymous-
   constructor syntax for `(ccrNewIndexFunctor _).Elements` objects.
   Mathlib's `CategoryOfElements` uses `⟨C, x⟩` with `C : C` and
   `x : F.obj C`; confirm this matches by inspecting with
   `mcp__lean-lsp__lean_hover_info` and adjust if the encoding differs.
2. The morphism-level anonymous constructor `⟨(homFiber f).app e.fst,
   rfl⟩` produces an `(ccrNewIndexFunctor _).Elements`-morphism whose
   `.val` is the underlying `CoprodCovarRepCat` morphism and whose
   `.property` is the index-preservation proof.  The `rfl` works
   because `ccrNewReindex ((homFiber f).app e.fst) e.snd` is
   definitionally the target index by the definition of elements-
   morphisms.  If `rfl` fails, inspect the goal and adjust.
3. The universe annotations on `ccrNewReindex` may need pruning or
   adjustment to match the `ccrNewIndexFunctor` invocation.

**Fallback.** If the endpoint-object expressions don't type-check,
try writing the definition with `let`-bindings for each endpoint to
isolate the issue, or use `show` with the expected return type.

- [ ] **Step 2: Build**

Run: `lake build`
Expected: success with zero warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyDirectionsData_fibHomCrossUnwidened"
```

---

### Task 7.3.5: Generalize U3 abbrevs to decouple target Cat universe

**Files:**

- Modify: `GebLean/Utilities/Grothendieck.lean` — lines 5155–5328
  (section `FunctorBetweenCovContra` with abbrevs, derivations, and
  structure) and lines 7370–7659 (extractor section
  `FunctorBetweenCovContraExtractor`).

**What this task does:** The current U3 abbrevs (from plan Tasks 1–3)
declare `G : C ⥤ Cat.{vC, uC}` and `F : Dᵒᵖ ⥤ Cat.{vD, uD}`, forcing
the fibre-Cat universe to match each source category's own universe.
In the `praPolyDirections` setting, both `G = functorFromDataContra
sourceData` and `F = praDirectionsTargetFibre` target a Cat at a
widened universe (from `sourceData.T`) that differs from the universes
of `C = (grothendieckContraFunctor (Cat × Cat)).obj
presheafPRACatBifunctorUncurriedOp` and `D = Cat.{v_I, u_I}`.  This
task adds a shared target universe pair `(vT, uT)` so that
`G : C ⥤ Cat.{vT, uT}` and `F : Dᵒᵖ ⥤ Cat.{vT, uT}`, while leaving
`(vC, uC, vD, uD)` independently specifying the source-category
universes.  The constraint that `G` and `F` share target universe is
required because `FunctorBetweenCovContraFibFib`'s
`G.obj c ⥤ F.obj _` expression requires both to live in the same
Cat universe.

- [ ] **Step 1: Update the section header in `Grothendieck.lean`**

Replace

```lean
section FunctorBetweenCovContra

universe vC vD uC uD

variable {C : Type uC} [Category.{vC} C] (G : C ⥤ Cat.{vC, uC})
variable {D : Type uD} [Category.{vD} D] (F : Dᵒᵖ ⥤ Cat.{vD, uD})
```

with

```lean
section FunctorBetweenCovContra

universe vC vD uC uD vT uT

variable {C : Type uC} [Category.{vC} C] (G : C ⥤ Cat.{vT, uT})
variable {D : Type uD} [Category.{vD} D] (F : Dᵒᵖ ⥤ Cat.{vT, uT})
```

- [ ] **Step 2: Build and fix downstream references**

Run: `lake build`
Expected: compiler errors at the derived lemmas
`functorBetweenCovContraBaseHomEqIdProof` and
`functorBetweenCovContraBaseHomEqCompProof` plus potentially the
structure `FunctorBetweenCovContraData`.  For each error, adjust
universe annotations by replacing references like
`{vC}` or `{uC}` that should have been `{vT}` / `{uT}` in the context
of `G.map`'s or `F.map`'s output Cats.  The abbrevs themselves
(`FunctorBetweenCovContraBaseFib`, `FibFib`, `FibHomCrossApp`, etc.)
should propagate the new universes automatically, since they reference
`G.obj`, `F.obj`, `F.map`, which resolve to the target-Cat universe.

Common failure and fix pattern:
- Error: "expected type `Cat.{vC, uC}` but got `Cat.{vT, uT}`".
  Fix: the proof's `Cat.id_eq_id _` or similar refers to the wrong
  universe — annotate it explicitly as `Cat.id_eq_id.{vT, uT} _`.

- [ ] **Step 3: Update the `FunctorBetweenCovContraExtractor` section**

In the extractor section (starts at line 7370), the `universe vC vD
uC uD` declaration needs the same extension to `universe vC vD uC uD
vT uT`, and the `variable` declarations for `G, F` need the same
widened target type.  Each helper lemma (`toHomUnop_id_fst` through
`toHomUnop_comp`) plus `toFunctor` itself should then compile; fix any
remaining universe-annotation mismatches.

- [ ] **Step 4: Build clean**

Run: `lake build`
Expected: success with zero warnings.

- [ ] **Step 5: Commit**

```bash
git add GebLean/Utilities/Grothendieck.lean
git commit -m "grothendieck: decouple U3 target Cat universe from source categories"
```

**Note.** This generalization is a prerequisite for Task 7.4.  After
committing, return to Task 7.4 with the newly-generalized U3
infrastructure available.

---

### Task 7.4: Add `praPolyDirectionsData_fibHomCrossApp` (widened main)

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyDirectionsData_fibHomCrossUnwidened`.

**What this task does:** Widens the unwidened morphism from Task 7.3
through `catULiftFunctor2 ⋙ Cat.opFunctor` and glues with `eqToHom`
to bridge the endpoint-object mismatch.  Delivers the full
`fibHomCrossApp` field of the data bundle.

The endpoint-object mismatch arises because `F.map (baseFib.map f).op`
acts on the widened target by the composite `pshCatFunctor.map ⋙
catULiftFunctor2.map ⋙ Cat.opFunctor.map` applied to `f_I.op`.  By
`ccrNewFamilyFunctor_obj_naturality` (Task 7.1), the object-level
image of the RHS fibre under this composite agrees with the
widening of a reindexed `ccrNewFamily` on the nose.

- [ ] **Step 1: Add the definition**

Insert after `praPolyDirectionsData_fibHomCrossUnwidened`:

```lean
/--
Cross-fibre morphism for `praPolyDirectionsData`.  Widens
`praPolyDirectionsData_fibHomCrossUnwidened` through `catULiftFunctor2
⋙ Cat.opFunctor`, adjusted by `eqToHom` at the endpoint equalities
supplied by `ccrNewFamilyFunctor_obj_naturality`.
-/
private def praPolyDirectionsData_fibHomCrossApp :
    FunctorBetweenCovContraFibHomCrossApp
      (functorFromDataContra sourceData.{u_I, v_I, u_J, v_J,
        w_I, w'})
      praDirectionsTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'}
      praPolyDirectionsData_baseFib.{u_I, v_I, u_J, v_J, w_I, w'}
      praPolyDirectionsData_fibFib.{u_I, v_I, u_J, v_J, w_I, w'} :=
  fun {X₁ X₂} f x =>
    -- Bridge: widened unwidened-morphism + two eqToHom.
    eqToHom (by
      -- LHS endpoint: (fibFib X₁).obj x reduces via unwidenFiber + rfl
      -- to widened (ccrNewFamilyFunctor ...).obj (unwiden x).
      rfl) ≫
    (catULiftFunctor2.{max v_I (w_I + 1) u_I, max u_I w_I,
      max u_I u_J v_J w_I w',
      max u_I u_J v_I v_J (w_I + 1) (w' + 1)}.map
      (Cat.opFunctor.{_, _}.map
        (praPolyDirectionsData_fibHomCrossUnwidened.{u_I, v_I,
          u_J, v_J, w_I, w'} f
          ((praPolyDirectionsData_unwidenFiber.{u_I, v_I, u_J,
            v_J, w_I, w'} X₁).obj x)).op)).toFunctor.map
      (𝟙 _) ≫
    eqToHom (by
      -- RHS endpoint: alignment via ccrNewFamilyFunctor_obj_naturality.
      rfl)
```

**Structural note.** The skeleton above uses two `eqToHom` bookends
around the widened unwidened-morphism.  The two `rfl` placeholders
inside `eqToHom (by …)` may not close by `rfl` directly — if they do
not, apply the factoring-out-lemmas technique: extract each
endpoint equality as a named private lemma
`praPolyDirectionsData_fibHomCrossApp_src_eq` /
`_tgt_eq`, prove each via `rfl` after a targeted `dsimp only […]`
unfold, and reference the lemmas here.

The `.map (𝟙 _)` skeleton above is a placeholder; the actual content
is the `.op` of the unwidened morphism from Task 7.3 passed through
`catULiftFunctor2.map ⋙ Cat.opFunctor.map`.  Expand the expression
directly in the extractor position.

- [ ] **Step 2: Build and iterate**

Run: `lake build`
Expected: build may fail on the first pass if the endpoint-equality
`rfl`s do not close.  Iterate:

1. Replace each failing `rfl` with `_` and rebuild to see the exact
   goal.
2. If the goal is definitionally true after an unfolding, use
   `show LHS = RHS from rfl` with LHS/RHS expanded.
3. If it requires `ccrNewFamilyFunctor_obj_naturality`, use
   `exact congrArg Opposite.op (ccrNewFamilyFunctor_obj_naturality …)`
   or similar.
4. If multiple equalities are involved, chain via `.trans`.
5. If stuck, factor each endpoint into a named private lemma.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyDirectionsData_fibHomCrossApp"
```

---

### Task 7.5: Add `praPolyDirectionsData_fibHomCrossNat_unwidened`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyDirectionsData_fibHomCrossApp`.

**What this task does:** Proves naturality of the unwidened cross-
fibre morphism in the element morphism `g : e ⟶ e'` in
`(objFiber X₁ ⋙ ccrNewIndexFunctor _).Elements`.  Reduces to
functoriality of `ccrNewFamilyFunctor` plus the fact that
`praPolyDirectionsData_elemMor` is also a functor in `g`.

- [ ] **Step 1: Add the lemma**

Insert after `praPolyDirectionsData_fibHomCrossApp`:

```lean
/--
Naturality of `praPolyDirectionsData_fibHomCrossUnwidened` in the
element morphism `g`.  Follows from functoriality of
`ccrNewFamilyFunctor` and functoriality of
`NatTrans.mapElements`/`praPolyDirectionsData_elemMor` in `g`.
-/
private lemma praPolyDirectionsData_fibHomCrossNat_unwidened
    {X₁ X₂ : (grothendieckContraFunctor
        (Cat.{v_J, u_J} × Cat.{v_I, u_I})).obj
      presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'}}
    (f : X₁ ⟶ X₂)
    {e e' : (GrothendieckContraFunctor.objFiber X₁ ⋙
        ccrNewIndexFunctor.{max v_I u_I (w_I + 1),
          max u_I w_I, w'}
          (↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
            (Opposite.op
              (GrothendieckContraFunctor.objBase X₁).2))))
      .Elements}
    (g : e ⟶ e') :
    (ccrNewFamilyFunctor.{max v_I u_I (w_I + 1), max u_I w_I, w'}
        (↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
          (Opposite.op
            (GrothendieckContraFunctor.objBase X₁).2)))).map g ≫
      praPolyDirectionsData_fibHomCrossUnwidened.{u_I, v_I, u_J,
        v_J, w_I, w'} f e' =
    praPolyDirectionsData_fibHomCrossUnwidened.{u_I, v_I, u_J,
        v_J, w_I, w'} f e ≫
      (ccrNewFamilyFunctor.{max v_I u_I (w_I + 1), max u_I w_I,
          w'}
          (↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
            (Opposite.op
              (GrothendieckContraFunctor.objBase X₁).2)))).map
        ((praPolyDirectionsData_elemMor.{u_I, v_I, u_J, v_J,
          w_I, w'} f).map g) := by
  unfold praPolyDirectionsData_fibHomCrossUnwidened
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  -- The remaining goal is functoriality of elemMor in g.
  exact ((praPolyDirectionsData_elemMor.{u_I, v_I, u_J, v_J,
    w_I, w'} f).map_comp _ _).symm.trans
    ((praPolyDirectionsData_elemMor.{u_I, v_I, u_J, v_J,
      w_I, w'} f).map_comp _ _)
```

**Note.** The final `exact` is a placeholder — adjust once the exact
goal shape is visible via `mcp__lean-lsp__lean_goal`.  Since Task 7.3
builds `fibHomCrossUnwidened` directly via `ccrNewFamilyFunctor.map
⟨(homFiber f).app e.fst, rfl⟩` (no intermediate `elemMor` helper), the
naturality proof here needs to show that post-composing `.map g` with
`.map ⟨(homFiber f).app e.fst, rfl⟩` equals precomposing with an
appropriate element-morphism — this follows from `ccrNewFamilyFunctor`'s
`map_comp` plus a short element-category equality.

- [ ] **Step 2: Build**

Run: `lake build`
Expected: success with zero warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyDirectionsData_fibHomCrossNat_unwidened"
```

---

### Task 7.6: Add `praPolyDirectionsData_fibHomCrossNat` (widened)

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyDirectionsData_fibHomCrossNat_unwidened`.

**What this task does:** Lifts the unwidened naturality lemma to the
widened form required by the `FibHomCrossNat` abbrev.  Uses
functoriality of `catULiftFunctor2 ⋙ Cat.opFunctor` to carry the
unwidened equation through the widening.

- [ ] **Step 1: Add the lemma**

Insert after `praPolyDirectionsData_fibHomCrossNat_unwidened`:

```lean
/--
Naturality of `praPolyDirectionsData_fibHomCrossApp` in the element
morphism `g`.  Obtained by applying `(catULiftFunctor2 ⋙
Cat.opFunctor).map` to `praPolyDirectionsData_fibHomCrossNat_unwidened`
and threading the `eqToHom` bookends through.
-/
private lemma praPolyDirectionsData_fibHomCrossNat :
    FunctorBetweenCovContraFibHomCrossNat
      (functorFromDataContra sourceData.{u_I, v_I, u_J, v_J,
        w_I, w'})
      praDirectionsTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'}
      praPolyDirectionsData_baseFib.{u_I, v_I, u_J, v_J, w_I, w'}
      praPolyDirectionsData_fibFib.{u_I, v_I, u_J, v_J, w_I, w'}
      praPolyDirectionsData_fibHomCrossApp.{u_I, v_I, u_J, v_J,
        w_I, w'} := by
  intro X₁ X₂ f x y g
  -- Unfold fibHomCrossApp to expose the widened form.
  -- Use functoriality of (catULiftFunctor2 ⋙ Cat.opFunctor).map
  -- combined with fibHomCrossNat_unwidened.
  _  -- PLACEHOLDER: replace with proof per strategy below.
```

**Proof strategy.** The underscore placeholder above is a transient
probe that must be replaced with a real proof; the committed code must
contain no underscores.  Inspect the goal with
`mcp__lean-lsp__lean_goal` and build the proof in stages:

1. Unfold `praPolyDirectionsData_fibHomCrossApp` and
   `praPolyDirectionsData_fibFib` via `unfold` (or targeted `simp
   only`) to expose both sides as widened compositions.
2. Use `Functor.congr_hom` with a hypothesis that the underlying
   unwidened morphisms agree (by
   `praPolyDirectionsData_fibHomCrossNat_unwidened`).
3. Clean up residual `eqToHom`s with `eqToHom_trans` /
   `eqToHom_refl` / `Category.id_comp` / `Category.comp_id`.

If any step blocks, apply the factoring-out-lemmas technique:
extract named sub-lemmas for each sub-equality.

- [ ] **Step 2: Build**

Run: `lake build`
Expected: success with zero warnings and no remaining underscore holes.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyDirectionsData_fibHomCrossNat"
```

---

### Task 7.7: Add `praPolyDirectionsData_baseHomId_unwidened`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyDirectionsData_fibHomCrossNat`.

**What this task does:** Proves that
`praPolyDirectionsData_fibHomCrossUnwidened` at the identity morphism of
the source Grothendieck reduces to `eqToHom` — i.e., at `𝟙 X₁`,
`praPolyDirectionsData_elemMor` is the identity element-morphism (up to
`eqToHom`), and `ccrNewFamilyFunctor.map (𝟙 _) = 𝟙 _`.

- [ ] **Step 1: Add the lemma**

Insert after `praPolyDirectionsData_fibHomCrossNat`:

```lean
/--
Identity coherence for `praPolyDirectionsData_fibHomCrossUnwidened`.
At `f = 𝟙 X`, the unwidened cross-fibre morphism collapses to an
`eqToHom` coming from `praPolyDirectionsData_elemMor (𝟙 X) = 𝟙`
plus `ccrNewFamilyFunctor.map_id`.
-/
private lemma praPolyDirectionsData_baseHomId_unwidened
    (X : (grothendieckContraFunctor
        (Cat.{v_J, u_J} × Cat.{v_I, u_I})).obj
      presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'})
    (e : (GrothendieckContraFunctor.objFiber X ⋙
        ccrNewIndexFunctor.{max v_I u_I (w_I + 1),
          max u_I w_I, w'}
          (↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
            (Opposite.op
              (GrothendieckContraFunctor.objBase X).2))))
      .Elements) :
    praPolyDirectionsData_fibHomCrossUnwidened.{u_I, v_I, u_J,
      v_J, w_I, w'} (𝟙 X) e =
      eqToHom (by
        -- praPolyDirectionsData_elemMor (𝟙 X) e reduces to e up to
        -- an eqToHom from homFiber (𝟙 X) = eqToHom ….  Establish
        -- the object-level equality here by rfl or by rewriting
        -- with GrothendieckContraFunctor.homFiber-identity lemmas.
        rfl) := by
  unfold praPolyDirectionsData_fibHomCrossUnwidened
    praPolyDirectionsData_elemMor
  -- Reduce homFiber (𝟙 X) via GrothendieckContraFunctor lemmas;
  -- then NatTrans.mapElements of the (eqToHom-ed) identity reduces
  -- to an identity up to eqToHom.  Conclude via Functor.map_id /
  -- Functor.map_eqToHom.
  _
```

**Proof strategy.** The underscore placeholder above is a transient
probe that must be replaced with a real proof.  The proof decomposes
into:

1. Simplify `homFiber (𝟙 X)` using whatever
   `GrothendieckContraFunctor.homFiber_id` lemma exists, or derive it
   inline.
2. `NatTrans.mapElements` of an `eqToHom`-like natural transformation
   acts as `eqToHom` on objects.
3. `ccrNewFamilyFunctor.map (eqToHom _) = eqToHom _` via
   `Functor.map_eqToHom`.
4. `eqToHom`-composition collapses the whole expression.

Apply the factoring-out-lemmas technique if any step blocks.

- [ ] **Step 2: Build**

Run: `lake build`
Expected: success with zero warnings and no remaining underscore holes.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyDirectionsData_baseHomId_unwidened"
```

---

### Task 7.8: Add `praPolyDirectionsData_baseHomId` (widened)

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyDirectionsData_baseHomId_unwidened`.

**What this task does:** Lifts the unwidened identity collapse to the
widened form required by the `BaseHomId` abbrev.

- [ ] **Step 1: Add the lemma**

Insert after `praPolyDirectionsData_baseHomId_unwidened`:

```lean
/--
Identity coherence for `praPolyDirectionsData_fibHomCrossApp`.  At
`f = 𝟙 X`, the widened cross-fibre morphism equals the `eqToHom`
supplied by `functorBetweenCovContraBaseHomEqIdProof`.
-/
private lemma praPolyDirectionsData_baseHomId :
    FunctorBetweenCovContraBaseHomId
      (functorFromDataContra sourceData.{u_I, v_I, u_J, v_J,
        w_I, w'})
      praDirectionsTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'}
      praPolyDirectionsData_baseFib.{u_I, v_I, u_J, v_J, w_I, w'}
      praPolyDirectionsData_fibFib.{u_I, v_I, u_J, v_J, w_I, w'}
      praPolyDirectionsData_fibHomCrossApp.{u_I, v_I, u_J, v_J,
        w_I, w'} := by
  intro X x
  -- Unfold fibHomCrossApp; use baseHomId_unwidened for the main
  -- content; collapse eqToHom bookends.
  _
```

**Proof strategy.** Follow Task 7.6's unwidened-lift strategy, but for
identity coherence.  The underscore above is a transient probe.  The
widening preserves `eqToHom`s and identity morphisms via
`Functor.map_id` and `Functor.map_eqToHom`.

- [ ] **Step 2: Build**

Run: `lake build`
Expected: success with zero warnings and no remaining underscore holes.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyDirectionsData_baseHomId"
```

---

### Task 7.9: Add `praPolyDirectionsData_baseHomComp_unwidened`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyDirectionsData_baseHomId`.

**What this task does:** Proves that
`praPolyDirectionsData_fibHomCrossUnwidened` at a composition
`f ≫ g` decomposes as the composition at `f`, transported along
`g`, plus an `eqToHom`.  Reduces to functoriality of
`ccrNewFamilyFunctor` plus `GrothendieckContraFunctor.homFiber_comp`.

- [ ] **Step 1: Add the lemma**

Insert after `praPolyDirectionsData_baseHomId`:

```lean
/--
Composition coherence for
`praPolyDirectionsData_fibHomCrossUnwidened`.  At `f ≫ g`, decomposes
as `f`-component ≫ transport of `g`-component through
`praPolyDirectionsData_elemMor f`, adjusted by `eqToHom`.
-/
private lemma praPolyDirectionsData_baseHomComp_unwidened
    {X₁ X₂ X₃ : (grothendieckContraFunctor
        (Cat.{v_J, u_J} × Cat.{v_I, u_I})).obj
      presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'}}
    (f : X₁ ⟶ X₂) (g : X₂ ⟶ X₃)
    (e : (GrothendieckContraFunctor.objFiber X₁ ⋙
        ccrNewIndexFunctor.{max v_I u_I (w_I + 1),
          max u_I w_I, w'}
          (↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
            (Opposite.op
              (GrothendieckContraFunctor.objBase X₁).2))))
      .Elements) :
    praPolyDirectionsData_fibHomCrossUnwidened.{u_I, v_I, u_J,
      v_J, w_I, w'} (f ≫ g) e =
      praPolyDirectionsData_fibHomCrossUnwidened.{u_I, v_I, u_J,
        v_J, w_I, w'} f e ≫
      (ccrNewFamilyFunctor.{max v_I u_I (w_I + 1), max u_I w_I,
          w'}
          (↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
            (Opposite.op
              (GrothendieckContraFunctor.objBase X₁).2)))).map
        (praPolyDirectionsData_fibHomCrossUnwidened_transport_arg
          f g e) ≫
      eqToHom (praPolyDirectionsData_elemMor_comp_obj_eq f g e) := by
  _
```

**Note.** The above references two further sub-helpers
(`_transport_arg` and `_elemMor_comp_obj_eq`) which are not yet
defined.  If the composition structure turns out to be cleaner than
this sketch (e.g., no intermediate `eqToHom` needed because the
endpoint objects coincide on the nose), simplify accordingly —
remove the `_transport_arg` / `_elemMor_comp_obj_eq` helpers and
state the equation directly.  Use `mcp__lean-lsp__lean_goal` at an
underscore-implementation to discover the exact required shape
before committing.

**Proof strategy.** The leading ingredient is
`GrothendieckContraFunctor.homFiber_comp` (if present; otherwise
derive it) plus `NatTrans.mapElements`-composition and
`ccrNewFamilyFunctor`-functoriality.  Apply the factoring-out-
lemmas technique if the composition reshuffle resists closure.

- [ ] **Step 2: Build**

Run: `lake build`
Expected: success with zero warnings and no remaining underscore holes.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyDirectionsData_baseHomComp_unwidened"
```

---

### Task 7.10: Add `praPolyDirectionsData_baseHomComp` (widened)

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyDirectionsData_baseHomComp_unwidened`.

**What this task does:** Lifts the unwidened composition coherence to
the widened form required by the `BaseHomComp` abbrev.  This is the
step most likely to need the `Functor.congr_hom` fused-vs-split trick
from Task 3's `toHomUnop_comp` proof at `Grothendieck.lean:7559`.

- [ ] **Step 1: Add the lemma**

Insert after `praPolyDirectionsData_baseHomComp_unwidened`:

```lean
/--
Composition coherence for `praPolyDirectionsData_fibHomCrossApp`.
-/
private lemma praPolyDirectionsData_baseHomComp :
    FunctorBetweenCovContraBaseHomComp
      (functorFromDataContra sourceData.{u_I, v_I, u_J, v_J,
        w_I, w'})
      praDirectionsTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'}
      praPolyDirectionsData_baseFib.{u_I, v_I, u_J, v_J, w_I, w'}
      praPolyDirectionsData_fibFib.{u_I, v_I, u_J, v_J, w_I, w'}
      praPolyDirectionsData_fibHomCrossApp.{u_I, v_I, u_J, v_J,
        w_I, w'} := by
  intro X₁ X₂ X₃ f g x
  _
```

**Proof strategy.** Expect this to be the heaviest coherence proof in
Task 7.  Apply Task 3's `toHomUnop_comp` proof strategy
(`Grothendieck.lean:7559–7622`):

1. Unfold `fibHomCrossApp` to expose the widened unwidened-morphism.
2. Apply `baseHomComp_unwidened` under the widening via
   `Functor.map_comp`.
3. Handle the fused-vs-split `F.map`-transport collapse using
   `Functor.congr_hom hF` where `hF : F.map (fused).toFunctor =
   F.map (A).toFunctor ⋙ F.map (B).toFunctor`, proven by
   `rw [baseFib.map_comp, op_comp, F.map_comp]; rfl`.
4. Collapse residual `eqToHom`s.

Apply the factoring-out-lemmas technique if a step resists closure.

- [ ] **Step 2: Build**

Run: `lake build`
Expected: success with zero warnings and no remaining underscore holes.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyDirectionsData_baseHomComp"
```

---

### Task 7.11: Assemble `praPolyDirectionsData` bundle

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — insert after
  `praPolyDirectionsData_baseHomComp`.

**What this task does:** Assembles all six field-helpers into the
`FunctorBetweenCovContraData` struct literal.  No further proof work.

- [ ] **Step 1: Add the definition**

Insert after `praPolyDirectionsData_baseHomComp`:

```lean
/--
Bundled `FunctorBetweenCovContraData` for `praPolyDirectionsFunctor`.

The base functor maps `((J, I), P) ↦ I`; the fibre functor maps
widened elements of the positions presheaf to the opposite of the
widened directions presheaf via `elementsPrecomp P ⋙
ccrNewFamilyFunctor (presheafCat I)` post-composed with widening.
The cross-fibre morphism and its three coherence obligations are
supplied by the Task 7.4/7.6/7.8/7.10 helpers.
-/
private def praPolyDirectionsData :
    FunctorBetweenCovContraData.{_, _, _, _}
      (functorFromDataContra sourceData.{u_I, v_I, u_J, v_J,
        w_I, w'})
      praDirectionsTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'} where
  baseFib := praPolyDirectionsData_baseFib.{u_I, v_I, u_J, v_J,
    w_I, w'}
  fibFib := praPolyDirectionsData_fibFib.{u_I, v_I, u_J, v_J,
    w_I, w'}
  fibHomCrossApp := praPolyDirectionsData_fibHomCrossApp.{u_I,
    v_I, u_J, v_J, w_I, w'}
  fibHomCrossNat := praPolyDirectionsData_fibHomCrossNat.{u_I,
    v_I, u_J, v_J, w_I, w'}
  baseHomId := praPolyDirectionsData_baseHomId.{u_I, v_I, u_J,
    v_J, w_I, w'}
  baseHomComp := praPolyDirectionsData_baseHomComp.{u_I, v_I,
    u_J, v_J, w_I, w'}
```

- [ ] **Step 2: Build**

Run: `lake build`
Expected: success with zero warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyDirectionsData bundle"
```

---

## Task 8: Define `praPolyDirectionsFunctor`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — append after `praPolyDirectionsData` (and
  its helpers).

- [ ] **Step 1: Add the definition**

```lean
/--
The `(I, J, P)`-natural directions functor, in polynomial-functor-morphism form
(backward-on-directions).  Built as a flat functor between two Grothendieck
constructions via `FunctorBetweenCovContra`.

Objects of the source are 4-tuples `((J, I), P, element)`; objects of the target
are pairs `(I, op_presheaf)`.  The functor sends `((J, I), P, element) ↦ (I,
op (directions presheaf of element))`.
-/
def praPolyDirectionsFunctor :
    praPolyDirectionsSource.{u_I, v_I, u_J, v_J, w_I, w'} ⥤
      praPolyDirectionsTarget.{u_I, v_I, u_J, v_J, w_I, w'} :=
  FunctorBetweenCovContraData.toFunctor
    praPolyDirectionsData.{u_I, v_I, u_J, v_J, w_I, w'}
```

- [ ] **Step 2: Build and verify**

Run: `lake build`
Expected: success with zero warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyDirectionsFunctor"
```

---

## Task 9: Add bridge lemmas

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — append after `praPolyDirectionsFunctor`.

**What this task does:** Three bridge lemmas that unfold `praPolyDirectionsFunctor`
on objects and morphisms, showing its action agrees with the familiar
`elementsPrecomp ⋙ ccrNewFamilyFunctor` composite.  All three should hold by `rfl`
(by construction of the data bundle).  If any doesn't reduce by `rfl`, factor out
a small helper lemma and use `simp only` with targeted rewrites.

- [ ] **Step 1: Add the bridge lemmas**

```lean
/--
Bridge lemma: `praPolyDirectionsFunctor`'s action on objects projects to the `I`
component of the source's base.
-/
theorem praPolyDirectionsFunctor_base
    (X : praPolyDirectionsSource.{u_I, v_I, u_J, v_J, w_I, w'}) :
    GrothendieckContraFunctor.objBase
      (praPolyDirectionsFunctor.{u_I, v_I, u_J, v_J, w_I, w'}.obj X) =
    (GrothendieckContraFunctor.objBase X.base).2 :=
  rfl

/--
Bridge lemma: `praPolyDirectionsFunctor`'s fibre component agrees with the
widened form of `elementsPrecomp P ⋙ ccrNewFamilyFunctor (presheafCat I)` applied
to the unwidened element.
-/
theorem praPolyDirectionsFunctor_fibre
    (X : praPolyDirectionsSource.{u_I, v_I, u_J, v_J, w_I, w'}) :
    GrothendieckContraFunctor.objFiber
      (praPolyDirectionsFunctor.{u_I, v_I, u_J, v_J, w_I, w'}.obj X) =
    (praPolyDirectionsData.{u_I, v_I, u_J, v_J, w_I, w'}.fibFib X.base).obj
      X.fiber :=
  rfl

/--
Bridge lemma: `praPolyDirectionsFunctor`'s action on morphisms decomposes as
`fibHomCrossApp` composed with the fibre-functor action.
-/
theorem praPolyDirectionsFunctor_map_app
    {X Y : praPolyDirectionsSource.{u_I, v_I, u_J, v_J, w_I, w'}} (f : X ⟶ Y) :
    GrothendieckContraFunctor.homFiber
      (praPolyDirectionsFunctor.{u_I, v_I, u_J, v_J, w_I, w'}.map f) =
    praPolyDirectionsData.{u_I, v_I, u_J, v_J, w_I, w'}.fibHomCrossApp f.base
        X.fiber ≫
      (praDirectionsTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'}.map
          (praPolyDirectionsData.baseFib.map f.base).op).toFunctor.map
        ((praPolyDirectionsData.fibFib Y.base).map f.fiber) :=
  rfl
```

- [ ] **Step 2: Build and verify**

Run: `lake build`
Expected: success with zero warnings.  If any of the three bridge lemmas does not
close by `rfl`, replace its body with a short tactic block using `simp only
[praPolyDirectionsFunctor, FunctorBetweenCovContraData.toFunctor, …]` targeted at
the relevant definition unfolds.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPolyDirectionsFunctor bridge lemmas"
```

---

## Task 10: Add `praPositionsUnwidened` helper

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — replace the body of `praPositionsPresheaf`
  with a `private` helper named `praPositionsUnwidened`, keeping the body
  identical but with the new name (so the call sites can migrate incrementally).

**What this task does:** Renames the transitional helper without changing its
body.  The old `praPositionsPresheaf` will be deleted in Task 14 after
`praPositions` and call sites migrate to `praPositionsUnwidened`.

- [ ] **Step 1: Add `praPositionsUnwidened` above `praPositionsPresheaf` (line 449)**

Insert immediately before the existing `def praPositionsPresheaf` declaration:

```lean
/--
`private` helper: unwidened form of the positions presheaf, obtained by
absorbing the `ULift`/`ULiftHom` unwrap of `praPositionsNat`'s widening.  Same
body as the old `praPositionsPresheaf` (which this replaces once the pointwise
accessors and call sites migrate).
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

- [ ] **Step 2: Build and verify**

Run: `lake build`
Expected: success with zero warnings.  The existing `praPositionsPresheaf` is
still present.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: add praPositionsUnwidened private helper"
```

---

## Task 11: Rewrite `praPositions` to use `praPositionsUnwidened`

**Files:**

- Modify: `GebLean/PresheafPRA.lean:459-465` — replace the body of `praPositions`.

- [ ] **Step 1: Update the body**

Replace:

```lean
variable (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)

/--
The type of positions at stage `j`.
-/
def praPositions (j : Jᵒᵖ) : Type w' :=
  (praPositionsPresheaf I J P).obj j
```

with:

```lean
variable (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)

/--
The type of positions at stage `j`.

Defined via the `private` `praPositionsUnwidened` helper, which absorbs the
`ULift`/`ULiftHom` unwrap of `praPositionsNat`'s widening.
-/
def praPositions (j : Jᵒᵖ) : Type w' :=
  (praPositionsUnwidened I J P).obj j
```

- [ ] **Step 2: Build and verify**

Run: `lake build`
Expected: success with zero warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: rewrite praPositions via praPositionsUnwidened"
```

---

## Task 12: Rewrite `praDirectionsAt` to use `praPolyDirectionsFunctor`

**Files:**

- Modify: `GebLean/PresheafPRA.lean:495-498` — replace the body of
  `praDirectionsAt`.

**What this task does:** Factors out a `private` helper
`praPolyDirectionsAtSourceObj` that constructs the `praPolyDirectionsSource`
object for a specific `(I, J, P, j, a)`.  Then `praDirectionsAt` applies
`praPolyDirectionsFunctor` to that, extracts the fibre, `.unop`s, and unwidens.

- [ ] **Step 1: Add the private helper and rewrite `praDirectionsAt`**

Replace:

```lean
/--
The directions presheaf at position `a` at stage `j`.
-/
def praDirectionsAt (j : Jᵒᵖ)
    (a : praPositions I J P j) : Iᵒᵖ ⥤ Type w_I :=
  (praDirectionsAtFunctor I J P).obj
    (Opposite.op ⟨j, a⟩)
```

with:

```lean
/--
Construct a `praPolyDirectionsSource` object from a specific `(I, J, P, j, a)`.
The resulting source object packages `((J, I), P, widened element at (j, a))`
so that `praPolyDirectionsFunctor` can be applied to it.
-/
private def praPolyDirectionsAtSourceObj (j : Jᵒᵖ)
    (a : praPositions.{u_I, v_I, u_J, v_J, w_I, w'} I J P j) :
    praPolyDirectionsSource.{u_I, v_I, u_J, v_J, w_I, w'} := …

/--
The directions presheaf at position `a` at stage `j`.

Defined by applying `praPolyDirectionsFunctor` to the `praPolyDirectionsSource`
object at `(I, J, P, j, a)`, extracting the target fibre (a widened op-presheaf
on `I`), and unwidening/unopping to get a `Iᵒᵖ ⥤ Type w_I`.
-/
def praDirectionsAt (j : Jᵒᵖ)
    (a : praPositions.{u_I, v_I, u_J, v_J, w_I, w'} I J P j) :
    Iᵒᵖ ⥤ Type w_I :=
  let Y := praPolyDirectionsFunctor.{u_I, v_I, u_J, v_J, w_I, w'}.obj
    (praPolyDirectionsAtSourceObj I J P j a)
  praPolyDirectionsAtUnwiden (GrothendieckContraFunctor.objFiber Y)
```

Where `praPolyDirectionsAtUnwiden` is a `private def` that inverts the ULift /
ULiftHom widening from `catULiftFunctor2` and applies `.unop` to reach
`Iᵒᵖ ⥤ Type w_I`.

**Implementation notes:**

- `praPolyDirectionsAtSourceObj`'s body builds a Grothendieck object whose base
  is itself a `grothendieckContraFunctor` object over `(Cat × Cat)`.  Use
  `GrothendieckContraFunctor.mkObj` from `Grothendieck.lean:7098` at both levels.
  The fibre is the widened element `(catULiftFunctor2 …).map` applied to
  `⟨j, a⟩ : (P ⋙ ccrNewIndexFunctor _).Elements`.
- `praPolyDirectionsAtUnwiden` inverts `sourceDataFib`'s widening chain.  For
  the exact ULift / ULiftHom API names in mathlib, use
  `mcp__lean-lsp__lean_local_search` (query `"ULiftHom"`) to enumerate the
  available down-functors.
- Use `mcp__lean-lsp__lean_goal` at each `…` to inspect the expected target type.

- [ ] **Step 2: Build and verify**

Run: `lake build`
Expected: success with zero warnings.  If the ULift/ULiftHom unwrap chain doesn't
match, examine `praPositionsUnwidened` above for the exact widening structure and
mirror-invert it.

- [ ] **Step 3: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: rewrite praDirectionsAt via praPolyDirectionsFunctor"
```

---

## Task 13: Migrate `PresheafPRAUMorph.lean` call sites

**Files:**

- Modify: `GebLean/PresheafPRAUMorph.lean` — the `praReassemble_directions` proof
  at lines 1230-1310 uses `unfold praDirectionsAtFunctor praDirectionsAtFunctorOp`,
  which will break once Task 14 deletes those definitions.

- [ ] **Step 1: Grep to confirm the scope**

Run:

```bash
grep -n 'praDirectionsAtFunctor\|praDirectionsAtFunctorOp\|praPositionsPresheaf' \
  GebLean/PresheafPRAUMorph.lean
```

Record every line.  The only Task-14-relevant uses are references to the
soon-to-be-deleted definitions; all references to `praPositionsPresheaf`,
`praDirectionsAtFunctor`, and `praDirectionsAtFunctorOp` need migration.

- [ ] **Step 2: Rewrite call sites**

For each reference:

- `praPositionsPresheaf I J P` → replace with `praPositionsUnwidened I J P` (a
  `private` helper — you may need to temporarily expose it as non-private, or
  inline its body, or create a public alias in `PresheafPRA.lean` if cross-file
  use is needed).  Prefer exposing it as public (drop `private`) in
  `PresheafPRA.lean:praPositionsUnwidened` if it's used outside the module.
- `praDirectionsAtFunctor I J P` → no direct replacement; remove the call entirely
  and restructure the proof using `praPolyDirectionsFunctor` and the bridge
  lemmas.

For the `praReassemble_directions` proof at lines 1230-1238 specifically, the
`unfold praDirectionsAtFunctor praDirectionsAtFunctorOp` step is the specific
blocker.  Replace with:

- A direct proof using `Functor.hext` plus `praPolyDirectionsFunctor_fibre` and
  `praPolyDirectionsFunctor_map_app` (the bridge lemmas from Task 9).

If this restructuring is unclear, consult `mcp__lean-lsp__lean_goal` at the
refactored proof to see the intermediate state.  It may help to commit the Task
10/11/12 changes first, build, and see what `praReassemble_directions` actually
needs to prove now.

- [ ] **Step 3: Build and verify**

Run: `lake build`
Expected: success with zero warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLean/PresheafPRA.lean GebLean/PresheafPRAUMorph.lean
git commit -m "presheaf-pra: migrate PresheafPRAUMorph call sites"
```

---

## Task 14: Delete `praDirectionsAtFunctorOp`, `praDirectionsAtFunctor`, `praPositionsPresheaf`

**Files:**

- Modify: `GebLean/PresheafPRA.lean` — delete the three definitions:
  - `praPositionsPresheaf` (currently at lines 449-457).
  - `praDirectionsAtFunctorOp` (currently at lines 472-479).
  - `praDirectionsAtFunctor` (currently at lines 486-491).

- [ ] **Step 1: Confirm no references remain**

Run:

```bash
grep -rn 'praPositionsPresheaf\|praDirectionsAtFunctor\|praDirectionsAtFunctorOp' \
  GebLean GebLeanTests test
```

Expected: no output (or only output inside the definitions being deleted).

If any call site outside the deletions remains, go back to Task 13 and migrate it.

- [ ] **Step 2: Delete the three definitions**

Open `GebLean/PresheafPRA.lean` and remove:

- The `def praPositionsPresheaf` block (including its docstring).
- The `def praDirectionsAtFunctorOp` block (including its docstring).
- The `def praDirectionsAtFunctor` block (including its docstring).

- [ ] **Step 3: Build and verify**

Run: `lake build`
Expected: success with zero warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: delete praDirectionsAtFunctor{,Op}, praPositionsPresheaf"
```

---

## Task 15: Remove `variable (P : PresheafPRACat …)` and audit remaining variables

**Files:**

- Modify: `GebLean/PresheafPRA.lean:459` — remove the `variable (P …)` line.
- Audit `variable (I …)` at line 38 and `variable (J …)` at line 39.

- [ ] **Step 1: Remove `variable (P …)`**

Delete line 459 (currently
`variable (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)`).

For every declaration that follows and uses `P`, add `P` as an explicit parameter
with the full type signature.  Specifically:

- `praPositions` — add `(P : PresheafPRACat … I J)` before `(j : Jᵒᵖ)`.
- `praDirectionsAt` — same.
- `praPolyDirectionsAtSourceObj` — same.

Similarly for `praEvalAt`, `praEvalAt_index`, `praEvalAt_mor`, `praEvalAt_mk`
(whose `variable (P …)` at line 553 is a separate scope but also worth cleaning
up; confirm the section separation).

- [ ] **Step 2: Build and verify**

Run: `lake build`
Expected: success with zero warnings.

- [ ] **Step 3: Audit `variable (I …)` and `variable (J …)`**

After Task 14 + Step 1 above, check which declarations actually use `I` and `J`
as section variables vs as explicit parameters.

Run:

```bash
grep -n 'variable (I\|variable (J' GebLean/PresheafPRA.lean
```

For any `variable (I …)` or `variable (J …)` whose usage is limited to a handful
of nearby definitions, replace those section-level variables with explicit
parameters on each definition that uses them.  For any that remain used in a
majority of the section's declarations (and deleting them would require
repetition), keep them but add a `--` comment explaining why.

Recommended approach:

- `variable (I : Type u_I) [Category.{v_I} I]` at line 38 and
  `variable (J : Type u_J) [Category.{v_J} J]` at line 39 — likely still useful,
  keep them but verify every section below uses them.  If any section doesn't use
  `I` or `J`, scope them with `section` blocks.

- [ ] **Step 4: Build and verify**

Run: `lake build`
Expected: success with zero warnings.

- [ ] **Step 5: Commit**

```bash
git add GebLean/PresheafPRA.lean
git commit -m "presheaf-pra: remove variable (P …), audit I/J variables"
```

---

## Task 16: Create test file `GebLeanTests/Utilities/PresheafPRADirNat.lean`

**Files:**

- Create: `GebLeanTests/Utilities/PresheafPRADirNat.lean`.

- [ ] **Step 1: Create the file with type-signature sanity tests**

```lean
import GebLean.PresheafPRA

/-!
# Tests for (I, J, P)-Naturality of praPolyDirectionsFunctor

Type-signature sanity checks and small-example tests for
`praPolyDirectionsFunctor` and friends in `GebLean.PresheafPRA`.
-/

open GebLean CategoryTheory

attribute [local instance] CategoryTheory.uliftCategory

/-! ## Type-signature sanity -/

-- praPolyDirectionsFunctor has the expected shape.
example :
    praPolyDirectionsSource.{0, 0, 0, 0, 0, 0} ⥤
      praPolyDirectionsTarget.{0, 0, 0, 0, 0, 0} :=
  praPolyDirectionsFunctor.{0, 0, 0, 0, 0, 0}

-- praPolyDirectionsSource has the expected Cat-level signature.
example :
    Cat.{0, 0} :=
  praPolyDirectionsSource.{0, 0, 0, 0, 0, 0}

-- praPolyDirectionsTarget has the expected Cat-level signature.
example :
    Cat.{0, 0} :=
  praPolyDirectionsTarget.{0, 0, 0, 0, 0, 0}

-- praDirectionsTargetFibre has the expected shape.
example :
    Cat.{0, 0}ᵒᵖ ⥤ Cat.{0, 0} :=
  praDirectionsTargetFibre.{0, 0, 0, 0, 0, 0}
```

If any of the four `example`s has a Cat-universe mismatch (e.g., the
`Cat.{0, 0}` on the RHS), adjust the universe to match the one pinned by the
declaration in `PresheafPRA.lean`.  Use `mcp__lean-lsp__lean_hover_info` on the
definition name to get its exact type signature.

- [ ] **Step 2: Build and verify**

Run: `lake build`
Expected: success with zero warnings.  (Note: file is not yet registered in
`GebLeanTests.lean`, so it won't run as part of `lake test` yet.)

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRADirNat.lean
git commit -m "tests: add PresheafPRADirNat.lean with type-signature sanity tests"
```

---

## Task 17: Register test file in `GebLeanTests.lean`

**Files:**

- Modify: `GebLeanTests.lean:22` — add one import line.

- [ ] **Step 1: Add the import**

After line 22 (`import GebLeanTests.Utilities.PresheafPRANat`), insert:

```lean
import GebLeanTests.Utilities.PresheafPRADirNat
```

- [ ] **Step 2: Build and verify**

Run: `lake build && lake test`
Expected: success with zero warnings, all `#guard` assertions pass.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests.lean
git commit -m "tests: register PresheafPRADirNat test file"
```

---

## Task 18: Add bridge-lemma collapse test

**Files:**

- Modify: `GebLeanTests/Utilities/PresheafPRADirNat.lean` — append.

- [ ] **Step 1: Add the test**

Append after the type-signature sanity section:

```lean
/-! ## Bridge-lemma collapse at a small concrete base -/

section CollapseTest

-- praPolyDirectionsFunctor_base applies at a concrete source object.
example (X : praPolyDirectionsSource.{0, 0, 0, 0, 0, 0}) :
    GrothendieckContraFunctor.objBase
      (praPolyDirectionsFunctor.{0, 0, 0, 0, 0, 0}.obj X) =
    (GrothendieckContraFunctor.objBase X.base).2 :=
  praPolyDirectionsFunctor_base.{0, 0, 0, 0, 0, 0} X

-- praPolyDirectionsFunctor_fibre applies at a concrete source object.
example (X : praPolyDirectionsSource.{0, 0, 0, 0, 0, 0}) :
    GrothendieckContraFunctor.objFiber
      (praPolyDirectionsFunctor.{0, 0, 0, 0, 0, 0}.obj X) =
    (praPolyDirectionsData.{0, 0, 0, 0, 0, 0}.fibFib X.base).obj X.fiber :=
  praPolyDirectionsFunctor_fibre.{0, 0, 0, 0, 0, 0} X

end CollapseTest
```

- [ ] **Step 2: Build and verify**

Run: `lake build && lake test`
Expected: success with zero warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRADirNat.lean
git commit -m "tests: add bridge-lemma collapse tests for praPolyDirectionsFunctor"
```

---

## Task 19: Add pointwise-accessor compatibility test

**Files:**

- Modify: `GebLeanTests/Utilities/PresheafPRADirNat.lean` — append.

- [ ] **Step 1: Add the test**

Append after the bridge-lemma section:

```lean
/-! ## Pointwise-accessor compatibility -/

section AccessorCompat

-- praPositions returns the expected type at a concrete (I, J, P, j).
example (I : Type 0) [Category.{0} I] (J : Type 0) [Category.{0} J]
    (P : PresheafPRACat.{0, 0, 0, 0, 0, 0} I J) (j : Jᵒᵖ) :
    praPositions.{0, 0, 0, 0, 0, 0} I J P j = Type 0 →
    True := fun _ => trivial

-- praDirectionsAt returns a presheaf on `I`.
example (I : Type 0) [Category.{0} I] (J : Type 0) [Category.{0} J]
    (P : PresheafPRACat.{0, 0, 0, 0, 0, 0} I J) (j : Jᵒᵖ)
    (a : praPositions.{0, 0, 0, 0, 0, 0} I J P j) :
    Iᵒᵖ ⥤ Type 0 :=
  praDirectionsAt.{0, 0, 0, 0, 0, 0} I J P j a

end AccessorCompat
```

**Note:** If the first `example` fails type-checking, replace with a simpler
signature probe like `#check @praPositions.{0, 0, 0, 0, 0, 0}`.  The aim is only
to confirm that the signature is unchanged from before the migration.

- [ ] **Step 2: Build and verify**

Run: `lake build && lake test`
Expected: success with zero warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRADirNat.lean
git commit -m "tests: add pointwise-accessor compatibility tests"
```

---

## Task 20: Add functoriality-at-morphism test

**Files:**

- Modify: `GebLeanTests/Utilities/PresheafPRADirNat.lean` — append.

- [ ] **Step 1: Add the test**

Append:

```lean
/-! ## Functoriality at a concrete morphism -/

section FunctorialityTest

-- praPolyDirectionsFunctor preserves identity morphisms.
example (X : praPolyDirectionsSource.{0, 0, 0, 0, 0, 0}) :
    praPolyDirectionsFunctor.{0, 0, 0, 0, 0, 0}.map (𝟙 X) =
      𝟙 (praPolyDirectionsFunctor.{0, 0, 0, 0, 0, 0}.obj X) :=
  praPolyDirectionsFunctor.{0, 0, 0, 0, 0, 0}.map_id X

-- praPolyDirectionsFunctor preserves composition.
example {X Y Z : praPolyDirectionsSource.{0, 0, 0, 0, 0, 0}}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    praPolyDirectionsFunctor.{0, 0, 0, 0, 0, 0}.map (f ≫ g) =
      praPolyDirectionsFunctor.{0, 0, 0, 0, 0, 0}.map f ≫
        praPolyDirectionsFunctor.{0, 0, 0, 0, 0, 0}.map g :=
  praPolyDirectionsFunctor.{0, 0, 0, 0, 0, 0}.map_comp f g

end FunctorialityTest
```

- [ ] **Step 2: Build and verify**

Run: `lake build && lake test`
Expected: success with zero warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRADirNat.lean
git commit -m "tests: add functoriality tests for praPolyDirectionsFunctor"
```

---

## Task 21: Add universe-polymorphism test

**Files:**

- Modify: `GebLeanTests/Utilities/PresheafPRADirNat.lean` — append.

- [ ] **Step 1: Add the test**

Append:

```lean
/-! ## Universe polymorphism -/

section UniversePoly

-- Exercise praPolyDirectionsFunctor at mixed universes
-- (u_I := 1, v_I := 0, u_J := 0, v_J := 0, w_I := 0, w' := 0).
example :
    praPolyDirectionsSource.{1, 0, 0, 0, 0, 0} ⥤
      praPolyDirectionsTarget.{1, 0, 0, 0, 0, 0} :=
  praPolyDirectionsFunctor.{1, 0, 0, 0, 0, 0}

-- Exercise at (u_I := 0, v_I := 0, u_J := 1, v_J := 0, w_I := 0, w' := 0).
example :
    praPolyDirectionsSource.{0, 0, 1, 0, 0, 0} ⥤
      praPolyDirectionsTarget.{0, 0, 1, 0, 0, 0} :=
  praPolyDirectionsFunctor.{0, 0, 1, 0, 0, 0}

end UniversePoly
```

- [ ] **Step 2: Build and verify**

Run: `lake build && lake test`
Expected: success with zero warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLeanTests/Utilities/PresheafPRADirNat.lean
git commit -m "tests: add universe-polymorphism test for praPolyDirectionsFunctor"
```

---

## Task 22: Update `.session/workstreams/*.md`

**Files:**

- Modify: `.session/workstreams/presheaf-pra.md` — mark the praDirections v2 spec
  as Complete; rename stale references to `praDirectionsAtFunctor` →
  `praPolyDirectionsFunctor`, `praPositionsPresheaf` → `praPositionsUnwidened`.
- Modify: `.session/workstreams/pra-universal-morphisms.md` (if present and uses
  any of the renamed names).

- [ ] **Step 1: Grep for stale references**

```bash
grep -rn 'praDirectionsAtFunctor\|praPositionsPresheaf' .session/
```

- [ ] **Step 2: Rewrite each hit**

For each stale reference:

- `praDirectionsAtFunctor` / `praDirectionsAtFunctorOp` → `praPolyDirectionsFunctor`
  (and explain in context that the old per-`(I, J, P)` form is subsumed by the
  flat functor).
- `praPositionsPresheaf` → `praPositionsUnwidened` with a note that it's now
  a `private` helper.

- [ ] **Step 3: Mark the v2 spec complete**

In `.session/workstreams/presheaf-pra.md`, locate the "Directions-Promotion v2"
section and append a "Status: Complete (2026-04-19)" line with a one-sentence
summary.

- [ ] **Step 4: Verify no stale references remain**

```bash
grep -rn 'praDirectionsAtFunctor\|praPositionsPresheaf' .session/
```

Expected: no output.

- [ ] **Step 5: Commit**

```bash
git add .session/
git commit -m "session: update workstreams for praDirections v2 completion"
```

---

## Final Validation

After all tasks complete, run the final validation sequence:

- [ ] **Step 1: Clean build**

```bash
lake build
```

Expected: success with zero warnings.

- [ ] **Step 2: Full test run**

```bash
lake test
```

Expected: all tests pass with zero warnings.

- [ ] **Step 3: Axiom audit**

In a Lean REPL or by adding a temporary `#print axioms` line:

```lean
#print axioms praPolyDirectionsFunctor.{0, 0, 0, 0, 0, 0}
```

Expected output: `propext`, `Classical.choice`, `Quot.sound` only.  No
`Classical.choice` in new code — the only `Classical.choice` dependency should
flow from mathlib's `Grothendieck` construction itself (established baseline).

If additional axioms appear, locate the offending use of `Classical` or `sorry`
(should be impossible given `CLAUDE.md`'s zero-`sorry` / zero-`classical` rule)
and fix.

- [ ] **Step 4: `sorry` / `admit` / `axiom` audit**

```bash
grep -rn 'sorry\|admit\|^axiom \|noncomputable\|open Classical\|classical' \
  GebLean/PresheafPRA.lean GebLean/Utilities/Grothendieck.lean \
  GebLeanTests/Utilities/PresheafPRADirNat.lean
```

Expected: no output (beyond legitimate `classicallyTrue`-style names if any;
inspect each hit).

- [ ] **Step 5: Downstream build verification**

```bash
lake build GebLean.PresheafPRAUMorph
```

Expected: success with zero warnings.

---

## Execution Handoff

**Plan complete and saved to `docs/superpowers/plans/2026-04-19-praDirections-naturality-v2.md`.**

Two execution options:

1. **Subagent-Driven (recommended)** — dispatch a fresh subagent per task, with
   two-stage review (spec compliance + code quality) between tasks, fast iteration.
2. **Inline Execution** — execute tasks in this session using the executing-plans
   skill, batch execution with checkpoints for review.

Given the user's stated preference to "craft a prompt to trigger a fresh session
to execute the plan with superpowers:executing-plans" (from the v2 brainstorm
message), the expected continuation is a fresh-session handoff to
executing-plans.  The brainstorm plan then calls for crafting that handoff
prompt.

**Which approach?**
