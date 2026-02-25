# TypeExprCat Implementation Plan

> **For Claude:** REQUIRED SUB-SKILL: Use
> superpowers:executing-plans to implement this plan
> task-by-task.

**Goal:** Define `TypeExprCat` (a category of type
expressions with parametric morphisms), `ParametricWedge`
(whose terminal object is `ParametricFamily`), and
`TypeExpr.unit` (the representing object).

**Architecture:** Add a new section to
`ParanaturalTopos.lean` after the existing
`ParametricFamily` infrastructure. Define
`ParametricWedge` as a structure, `TypeExprCat` as a
wrapper type with a `Category` instance using
`ParametricFamily (arrow T₁ T₂)` as the hom type, and
prove `ParametricFamily T ≅ Hom(unit, T)`. Restate
existing equivalences as `Hom` computations.

**Tech Stack:** Lean 4, mathlib (`CategoryTheory`).

**Reference:** Design doc at
`docs/plans/2026-02-25-typeexprcat-design.md`.
Read `CLAUDE.md` before starting.

---

## Task 1: Define TypeExpr.unit

**Files:**

- Modify: `GebLean/ParanaturalTopos.lean` (insert after
  `TypeExpr.leaf` definition, around line 3127)

**Step 1:** Define `TypeExpr.unit`:

```lean
/-- The unit type expression: constant at `PUnit`.
`unit.interp I I = PUnit` for all `I`. -/
abbrev TypeExpr.unit : TypeExpr :=
  .app ((Functor.const Type).obj PUnit) .var
```

**Step 2:** Prove `unit.interp I I = PUnit`:

```lean
@[simp]
theorem TypeExpr.unit_interp (I : Type) :
    TypeExpr.unit.interp I I = PUnit :=
  rfl
```

**Step 3:** Prove `fullRelInterp` at unit is trivial:

```lean
@[simp]
theorem TypeExpr.unit_fullRelInterp
    {I₀ I₁ : Type} (R : I₀ → I₁ → Prop)
    (x y : PUnit) :
    TypeExpr.unit.fullRelInterp R x y := by
  simp only [fullRelInterp, functorRelLift]
  exact ⟨PUnit.unit, rfl, rfl⟩
```

**Step 4:** Run `lake build` to verify. Fix any errors.

**Step 5:** Commit: "Define TypeExpr.unit"

---

## Task 2: Define ParametricWedge

**Files:**

- Modify: `GebLean/ParanaturalTopos.lean` (insert a new
  section after the `ParametricFamily` section, before
  `ParametricityDivergence`)

**Step 1:** Define the `ParametricWedge` structure:

```lean
section ParametricWedges

/-- A parametric wedge for `T : TypeExpr` consists of
a vertex type `pt`, a projection family
`proj : (I : Type) → pt → T.interp I I`, and a proof
that every element satisfies the full relational
interpretation condition for all relations. -/
structure ParametricWedge (T : TypeExpr) where
  /-- The vertex type -/
  pt : Type
  /-- The projection family -/
  proj : (I : Type) → pt → T.interp I I
  /-- The parametric condition -/
  parametric :
    ∀ (w : pt) (I₀ I₁ : Type)
      (R : I₀ → I₁ → Prop),
    T.fullRelInterp R (proj I₀ w) (proj I₁ w)
```

**Step 2:** Define the canonical parametric wedge from
`ParametricFamily`:

```lean
/-- `ParametricFamily T` as a parametric wedge. -/
def ParametricFamily.toWedge
    {T : TypeExpr} :
    ParametricWedge T where
  pt := ParametricFamily T
  proj I p := p.app I
  parametric w := w.parametric
```

**Step 3:** Run `lake build`. Fix any errors.

**Step 4:** Commit: "Define ParametricWedge"

---

## Task 3: Prove ParametricFamily is terminal

**Files:**

- Modify: `GebLean/ParanaturalTopos.lean` (continue in
  `ParametricWedges` section)

**Step 1:** Define the unique morphism from any wedge:

```lean
/-- The unique morphism from any parametric wedge
to `ParametricFamily.toWedge`. -/
def ParametricWedge.toParametricFamily
    {T : TypeExpr} (W : ParametricWedge T) :
    W.pt → ParametricFamily T :=
  fun w =>
    { app := fun I => W.proj I w
      parametric := W.parametric w }
```

**Step 2:** Prove the projection condition:

```lean
/-- The morphism `toParametricFamily` commutes with
the projections: `(toParametricFamily w).app I =
W.proj I w`. -/
@[simp]
theorem ParametricWedge.toParametricFamily_app
    {T : TypeExpr} (W : ParametricWedge T)
    (w : W.pt) (I : Type) :
    (W.toParametricFamily w).app I =
      W.proj I w :=
  rfl
```

**Step 3:** Prove uniqueness:

```lean
/-- Any function `f : W.pt → ParametricFamily T`
that commutes with projections equals
`toParametricFamily`. -/
theorem ParametricWedge.toParametricFamily_unique
    {T : TypeExpr} (W : ParametricWedge T)
    (f : W.pt → ParametricFamily T)
    (hf : ∀ (w : W.pt) (I : Type),
      (f w).app I = W.proj I w) :
    f = W.toParametricFamily := by
  funext w
  exact ParametricFamily.ext _ _
    (funext fun I => hf w I)

end ParametricWedges
```

**Step 4:** Run `lake build`. Fix any errors.

**Step 5:** Commit: "Prove ParametricFamily is terminal
parametric wedge"

---

## Task 4: Define TypeExprCat

**Files:**

- Modify: `GebLean/ParanaturalTopos.lean` (new section
  after `ParametricWedges`)

**Step 1:** Define the wrapper type and category instance.
The morphism type `Hom(T₁, T₂) =
ParametricFamily (arrow T₁ T₂)` gives a family
`∀ I, T₁.interp I I → T₂.interp I I` with the
relation-preservation condition.

```lean
section TypeExprCategory

/-- Wrapper type for `TypeExpr` to carry the
`TypeExprCat` category instance. -/
@[ext]
structure TypeExprCat where
  /-- The underlying type expression. -/
  expr : TypeExpr
```

**Step 2:** Define identity and composition. Identity is
the identity function family. Composition is pointwise
function composition with proofs composed by modus ponens.

Define identity:

```lean
/-- The identity morphism in `TypeExprCat`:
the identity function family with the trivial
preservation proof. -/
def typeExprId (T : TypeExpr) :
    ParametricFamily (.arrow T T) where
  app I := id
  parametric I₀ I₁ R x₀ x₁ h := h
```

Define composition:

```lean
/-- Composition of morphisms in `TypeExprCat`:
pointwise function composition. The parametric
condition composes by modus ponens. -/
def typeExprComp {T₁ T₂ T₃ : TypeExpr}
    (η : ParametricFamily (.arrow T₁ T₂))
    (μ : ParametricFamily (.arrow T₂ T₃)) :
    ParametricFamily (.arrow T₁ T₃) where
  app I := μ.app I ∘ η.app I
  parametric I₀ I₁ R x₀ x₁ h :=
    μ.parametric I₀ I₁ R
      (η.app I₀ x₀) (η.app I₁ x₁)
      (η.parametric I₀ I₁ R x₀ x₁ h)
```

**Step 3:** Run `lake build`. The `parametric` field
of `typeExprComp` might need adjustment depending on
how `fullRelInterp` unfolds for `arrow`. Build and check
the exact goal, then fix.

**Step 4:** Commit: "Define TypeExprCat identity and
composition"

---

## Task 5: Category instance for TypeExprCat

**Files:**

- Modify: `GebLean/ParanaturalTopos.lean` (continue in
  `TypeExprCategory` section)

**Step 1:** Define the category instance:

```lean
instance : Category TypeExprCat where
  Hom T₁ T₂ :=
    ParametricFamily (.arrow T₁.expr T₂.expr)
  id T := typeExprId T.expr
  comp η μ := typeExprComp η μ
  id_comp η := by
    exact ParametricFamily.ext _ _
      (funext fun _ => rfl)
  comp_id η := by
    exact ParametricFamily.ext _ _
      (funext fun _ => rfl)
  assoc η μ ν := by
    exact ParametricFamily.ext _ _
      (funext fun _ => rfl)
```

The proofs for `id_comp`, `comp_id`, and `assoc` should
reduce to reflexivity since function composition is
associative and unital definitionally. If `ext` or
`funext` don't suffice, the implementing agent should
use underscores to inspect goals and adjust.

**Step 2:** Run `lake build`. Fix any errors.

**Step 3:** Commit: "Category instance for TypeExprCat"

---

## Task 6: Prove ParametricFamily is representable

**Files:**

- Modify: `GebLean/ParanaturalTopos.lean` (continue in
  `TypeExprCategory` section)

**Step 1:** Define the unit object:

```lean
/-- The unit object of `TypeExprCat`, representing
`ParametricFamily` via `Hom(unit, T) ≅
ParametricFamily T`. -/
def typeExprUnit : TypeExprCat :=
  ⟨TypeExpr.unit⟩
```

**Step 2:** Build the equivalence. A morphism
`typeExprUnit → ⟨T⟩` is a
`ParametricFamily (.arrow .unit T)`, which gives
`∀ I, PUnit → T.interp I I` with the parametric
condition. This is isomorphic to
`ParametricFamily T` via the isomorphism
`(PUnit → X) ≅ X`.

```lean
/-- `Hom(unit, T) ≅ ParametricFamily T`:
the unit object represents `ParametricFamily`. -/
def typeExprHomUnitEquiv (T : TypeExpr) :
    (typeExprUnit ⟶ ⟨T⟩) ≃
      ParametricFamily T where
  toFun η :=
    { app := fun I => η.app I PUnit.unit
      parametric := fun I₀ I₁ R =>
        η.parametric I₀ I₁ R
          PUnit.unit PUnit.unit
          (TypeExpr.unit_fullRelInterp R
            PUnit.unit PUnit.unit) }
  invFun p :=
    { app := fun I _ => p.app I
      parametric := fun I₀ I₁ R _ _ _ =>
        p.parametric I₀ I₁ R }
  left_inv η := by
    exact ParametricFamily.ext _ _
      (funext fun I => funext fun u =>
        by cases u; rfl)
  right_inv p := by
    exact ParametricFamily.ext _ _
      (funext fun _ => rfl)
```

The `left_inv` proof uses `cases u` to eliminate
`PUnit` to `PUnit.unit`. The implementing agent
should check the exact goal shape and adjust.

**Step 3:** Run `lake build`. Fix any errors.

**Step 4:** Commit: "Prove ParametricFamily is
representable in TypeExprCat"

---

## Task 7: Restate existing equivalences

**Files:**

- Modify: `GebLean/ParanaturalTopos.lean` (continue in
  `TypeExprCategory` section)

**Step 1:** Restate `homParametricEquivUnit` as a
`Hom` computation:

```lean
/-- `Hom(var, var) ≅ Unit` in `TypeExprCat`. -/
def typeExprHomVarVar :
    (⟨.var⟩ : TypeExprCat) ⟶ ⟨.var⟩ ≃ Unit :=
  (typeExprHomUnitEquiv _).symm.trans
    homParametricEquivUnit
```

This doesn't work because
`Hom(⟨var⟩, ⟨var⟩) = ParametricFamily (arrow var var) =
ParametricFamily homTypeExpr`, while
`homParametricEquivUnit : ParametricFamily homTypeExpr ≃
Unit`. So the equivalence is direct:

```lean
/-- `Hom(var, var) ≅ Unit` in `TypeExprCat`:
the identity is the unique endomorphism of the
type variable. -/
abbrev typeExprHom_var_var :
    (⟨.var⟩ : TypeExprCat) ⟶ ⟨.var⟩ ≃ Unit :=
  homParametricEquivUnit
```

**Step 2:** Restate `dialgebraParametricEquivNatTrans`:

```lean
/-- `Hom(app F var, app G var) ≅ (F ⟶ G)` in
`TypeExprCat`: morphisms between applied
type variables are natural transformations
between the functors. -/
abbrev typeExprHom_leaf_leaf
    (F G : Type ⥤ Type) :
    (⟨.leaf F⟩ : TypeExprCat) ⟶ ⟨.leaf G⟩ ≃
      (F ⟶ G) :=
  dialgebraParametricEquivNatTrans F G
```

**Step 3:** Add at least one `Hom(unit, T)` equivalence
to demonstrate the representability. For example, the
initial algebra:

```lean
/-- `Hom(unit, algebraTypeExpr F) ≅ μF.a`:
the parametric families for the algebra type
correspond to elements of the initial algebra. -/
abbrev typeExprHomUnit_algebra
    (F : Type ⥤ Type)
    (μF : Endofunctor.Algebra F)
    (hμF : Limits.IsInitial μF) :
    (typeExprUnit ⟶
      ⟨algebraTypeExpr F⟩) ≃ μF.a :=
  (typeExprHomUnitEquiv _).trans
    (initialAlgebraParametricEquiv F μF hμF).symm
```

**Step 4:** Close the section:

```lean
end TypeExprCategory
```

**Step 5:** Run `lake build` and `lake test`. Fix all
errors and warnings.

**Step 6:** Commit: "Restate free theorems as TypeExprCat
Hom computations"

---

## Task 8: Update session workstream documentation

**Files:**

- Modify:
  `.session/workstreams/parametric-generalization.md`

**Step 1:** Add a section recording the completed
`TypeExprCat` infrastructure:

- `TypeExprCat` category instance
- `ParametricWedge` and terminality
- `typeExprHomUnitEquiv` (representability)
- Existing equivalences restated as `Hom` computations

**Step 2:** Note the Phase 2 direction: inductive
characterization `HomInd` of morphisms.
