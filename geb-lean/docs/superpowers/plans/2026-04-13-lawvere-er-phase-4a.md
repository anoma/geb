# Lawvere ER Phase 4a: Category of Decidable ER-Subobjects

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Assemble `LawvereERLexCat` as a `Category`: objects
are pairs of an arity and a Boolean-valued ER predicate;
morphisms are equivalence classes of `ERMorN` tuples that
respect membership, identified when they agree on every
context satisfying the source predicate.

**Architecture:** Objects are a `structure` bundling arity
and a Boolean predicate (no object-level quotient; distinct
but semantically equal predicates yield canonically
isomorphic objects).  Morphisms are built as a subtype of
`ERMorN` witnessing membership preservation, then
quotiented by a source-restricted extensional setoid.
Category laws follow from the `ERMorN` interpretation
lemmas restricted to the source predicate.

**Tech Stack:** Lean 4, Mathlib
(`CategoryTheory.Category.Basic`), depends on
`GebLean.LawvereER` (ERMor1, ERMorN, interp lemmas).

**Scope note:** Phase 4 is broken into stages.  This plan
(Phase 4a) covers only the category skeleton.  Subsequent
plans will add Boolean operations (Phase 4b), finite
products (Phase 4c), equalizers (Phase 4d), and the
full-and-faithful embedding `Δ : LawvereERCat ->
LawvereERLexCat` (Phase 4e).

---

## File Map

| File | Role |
| ---- | ---- |
| Create: `GebLean/LawvereERLex.lean` | `ERBoolPred`, `LexObj`, `ERLexMorN` subtype, setoid, quotient type, id/comp, category laws, `Category` instance |
| Modify: `GebLean.lean` | Add `import GebLean.LawvereERLex` |
| Create: `GebLeanTests/LawvereERLex.lean` | Sanity tests |
| Modify: `GebLeanTests.lean` | Add test import |
| Modify: `.session/workstreams/lawvere-elementary-recursive.md` | Mark Phase 4a complete |

---

## Proof Strategy

Every category law is proved by the same pattern:
unwrap quotients with `Quotient.ind`, reduce the goal to an
equality of function values restricted to contexts where
the source predicate is 1, then close with
`ERMorN.interp_id`, `ERMorN.interp_comp`, or their
consequences.  The source-restricted setoid is exactly
flexible enough: it ignores behavior outside the subobject,
so proofs never need to reason about what happens when the
predicate is 0.

Well-definedness of composition uses the source respect
proofs from the morphism subtypes: given `f` respects
`(src, tgt)` and `g` respects `(tgt, dst)`, the composite
`ERMorN.comp f.val g.val` respects `(src, dst)` because
the intermediate context `f.val.interp ctx` lies inside
`tgt` by `f.property`.

---

### Task 1: Create file with object types

**Files:**

- Create: `GebLean/LawvereERLex.lean`
- Modify: `GebLean.lean`

- [ ] **Step 1: Create `GebLean/LawvereERLex.lean` with
  imports, namespace, and object types**

```lean
import GebLean.LawvereER
import Mathlib.CategoryTheory.Category.Basic

/-!
# Finite-Limit Category of Decidable ER-Subobjects

Defines `LawvereERLexCat`, a category whose objects are
pairs of an arity and a Boolean-valued elementary
recursive predicate, and whose morphisms are equivalence
classes of `ERMorN` tuples respecting membership,
identified when they agree on every context satisfying
the source predicate.

This file covers the category skeleton only.  Finite
products, equalizers, and the full-and-faithful
embedding `LawvereERCat -> LawvereERLexCat` live in
subsequent modules.
-/

namespace GebLean

open CategoryTheory

/-- A Boolean-valued elementary recursive predicate:
an `ERMor1` term whose standard interpretation always
lies in `{0, 1}`.  Convention: `1 = true`, `0 = false`. -/
structure ERBoolPred (n : ℕ) where
  /-- The underlying predicate term. -/
  pred : ERMor1 n
  /-- Proof that the predicate is Boolean-valued. -/
  bool : ∀ ctx : Fin n → ℕ, pred.interp ctx ≤ 1

/-- Object of `LawvereERLexCat`: an arity together with
a Boolean-valued predicate cutting out a decidable
subobject of `Fin arity -> ℕ`. -/
structure LexObj where
  /-- The arity (number of free variables). -/
  arity : ℕ
  /-- The Boolean predicate. -/
  pred : ERBoolPred arity

end GebLean
```

- [ ] **Step 2: Add import to `GebLean.lean`**

Insert `import GebLean.LawvereERLex` alphabetically
after `import GebLean.LawvereERInterp`.

- [ ] **Step 3: Build**

Run: `lake build`
Expected: clean build, no warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereERLex.lean GebLean.lean
git commit -m "Add ERBoolPred and LexObj for LawvereERLex"
```

---

### Task 2: Raw morphism subtype

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Add `ERLexMorN` subtype**

Append before `end GebLean`:

```lean
/-- Raw morphism in `LawvereERLexCat`: an `ERMorN`
tuple that respects membership, that is, maps inputs
satisfying the source predicate to outputs satisfying
the target predicate. -/
def ERLexMorN (src tgt : LexObj) : Type :=
  { f : ERMorN src.arity tgt.arity //
      ∀ ctx : Fin src.arity → ℕ,
        src.pred.pred.interp ctx = 1 →
        tgt.pred.pred.interp (f.interp ctx) = 1 }
```

- [ ] **Step 2: Build**

Run: `lake build`
Expected: clean build.

- [ ] **Step 3: Commit**

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Add ERLexMorN subtype for LawvereERLex"
```

---

### Task 3: Setoid and quotient morphism type

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Add setoid and quotient type**

Append before `end GebLean`:

```lean
/-- The setoid on `ERLexMorN src tgt`: two raw
morphisms are related when their interpretations agree
on every context satisfying the source predicate. -/
def erLexMorNSetoid (src tgt : LexObj) :
    Setoid (ERLexMorN src tgt) where
  r f g :=
    ∀ ctx : Fin src.arity → ℕ,
      src.pred.pred.interp ctx = 1 →
      f.val.interp ctx = g.val.interp ctx
  iseqv := {
    refl := fun _ _ _ => rfl
    symm := fun h ctx hctx => (h ctx hctx).symm
    trans := fun h1 h2 ctx hctx =>
      (h1 ctx hctx).trans (h2 ctx hctx)
  }

/-- Quotient morphism type for `LawvereERLexCat`:
equivalence classes of `ERLexMorN` tuples under
source-restricted extensional equality. -/
def ERLexMorNQuo (src tgt : LexObj) : Type :=
  Quotient (erLexMorNSetoid src tgt)
```

- [ ] **Step 2: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Add erLexMorNSetoid and ERLexMorNQuo"
```

---

### Task 4: Identity morphism

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Define raw identity**

Append before `end GebLean`:

```lean
/-- The raw identity morphism at `obj`: the
underlying tuple is `ERMorN.id obj.arity`, with
membership preserved because the identity function
on contexts fixes everything. -/
def ERLexMorN.id (obj : LexObj) : ERLexMorN obj obj :=
  ⟨ERMorN.id obj.arity, fun ctx hctx => by
    rw [ERMorN.interp_id]
    exact hctx⟩

/-- The identity morphism in the quotient category. -/
def ERLexMorNQuo.id (obj : LexObj) :
    ERLexMorNQuo obj obj :=
  Quotient.mk (erLexMorNSetoid obj obj)
    (ERLexMorN.id obj)
```

Note: the `rw [ERMorN.interp_id]` rewrites
`(ERMorN.id obj.arity).interp ctx` to `ctx`, after
which the goal `obj.pred.pred.interp ctx = 1` is
exactly `hctx`.

- [ ] **Step 2: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Add ERLexMorNQuo.id"
```

---

### Task 5: Composition

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Define raw composition**

Append before `end GebLean`:

```lean
/-- Raw composition of `ERLexMorN` morphisms: the
underlying tuple is the `ERMorN.comp` of the two
underlying tuples; membership follows by chaining the
respective respect proofs through the interpretation
of the composite. -/
def ERLexMorN.comp
    {src mid tgt : LexObj}
    (f : ERLexMorN src mid)
    (g : ERLexMorN mid tgt) :
    ERLexMorN src tgt :=
  ⟨ERMorN.comp f.val g.val, fun ctx hctx => by
    rw [ERMorN.interp_comp]
    exact g.property _ (f.property ctx hctx)⟩
```

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Lift composition to the quotient**

```lean
/-- Composition of quotient morphisms, lifted from
`ERLexMorN.comp` via `Quotient.lift₂`.
Well-definedness: given `f ~ f'` and `g ~ g'` under
the source-restricted setoid, the composites agree on
every context satisfying the source predicate. -/
def ERLexMorNQuo.comp
    {src mid tgt : LexObj}
    (f : ERLexMorNQuo src mid)
    (g : ERLexMorNQuo mid tgt) :
    ERLexMorNQuo src tgt :=
  Quotient.lift₂
    (s₁ := erLexMorNSetoid src mid)
    (s₂ := erLexMorNSetoid mid tgt)
    (fun f' g' =>
      Quotient.mk (erLexMorNSetoid src tgt)
        (ERLexMorN.comp f' g'))
    (fun fa fb ga gb hf hg =>
      Quotient.sound
        (s := erLexMorNSetoid src tgt)
        (fun ctx hctx => by
          simp only [ERLexMorN.comp,
            ERMorN.interp_comp]
          rw [hf ctx hctx]
          exact hg _ (ga.property ctx hctx)))
    f g
```

The proof traces through:
```
(ERMorN.comp fa.val ga.val).interp ctx
  = ga.val.interp (fa.val.interp ctx)    -- interp_comp
  = ga.val.interp (ga.val.interp ctx)    -- hf ctx hctx changes fa to ga
  -- Now apply hg at fa'.interp ctx which is inside mid.pred
```

Wait — the variable naming above is confusing.  Let
me restate with the actual names used in
`Quotient.lift₂` (which passes `fa fb ga gb` where
`fa ≈ ga` under the first setoid and `fb ≈ gb` under
the second):
- `fa, ga : ERLexMorN src mid`
- `fb, gb : ERLexMorN mid tgt`
- `hf : fa ~ ga`
- `hg : fb ~ gb`

Goal (after `Quotient.sound`): show
`(ERLexMorN.comp fa fb) ~ (ERLexMorN.comp ga gb)`,
that is, `∀ ctx, src.pred.interp ctx = 1 →
(ERMorN.comp fa.val fb.val).interp ctx =
(ERMorN.comp ga.val gb.val).interp ctx`.

After `simp only [ERMorN.interp_comp]`:
`fb.val.interp (fa.val.interp ctx) =
gb.val.interp (ga.val.interp ctx)`.

`rw [hf ctx hctx]` rewrites `fa.val.interp ctx` to
`ga.val.interp ctx` on the LHS, giving
`fb.val.interp (ga.val.interp ctx) =
gb.val.interp (ga.val.interp ctx)`.

Then `hg _ h` with `h : mid.pred.interp
(ga.val.interp ctx) = 1` closes it.  The witness `h`
is `ga.property ctx hctx`.

If the `rw [hf ctx hctx]` approach does not
compile, try:

```lean
          congr 1
          · exact hf ctx hctx
          · exact hg _ (ga.property ctx hctx)
```

Or a `calc` block as a fallback.

- [ ] **Step 4: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Add ERLexMorNQuo.comp with quotient lifting"
```

---

### Task 6: Identity laws on the quotient

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Prove `ERLexMorNQuo.id_comp`**

Append before `end GebLean`:

```lean
/-- Left identity: `comp (id src) f = f`. -/
theorem ERLexMorNQuo.id_comp
    {src tgt : LexObj}
    (f : ERLexMorNQuo src tgt) :
    ERLexMorNQuo.comp (ERLexMorNQuo.id src) f = f :=
  Quotient.ind
    (motive := fun f =>
      ERLexMorNQuo.comp
        (ERLexMorNQuo.id src) f = f)
    (fun f_raw =>
      Quotient.sound
        (s := erLexMorNSetoid src tgt)
        (fun ctx _ => by
          simp only [ERLexMorN.comp,
            ERLexMorN.id,
            ERMorN.interp_comp,
            ERMorN.interp_id]))
    f
```

Proof: after unwrapping `f` as
`Quotient.mk _ f_raw`, show that
`ERLexMorN.comp (ERLexMorN.id src) f_raw` is
source-related to `f_raw`.  For any `ctx`, both sides
interpret to `f_raw.val.interp ctx` by `interp_comp`
and `interp_id`.

- [ ] **Step 2: Prove `ERLexMorNQuo.comp_id`**

```lean
/-- Right identity: `comp f (id tgt) = f`. -/
theorem ERLexMorNQuo.comp_id
    {src tgt : LexObj}
    (f : ERLexMorNQuo src tgt) :
    ERLexMorNQuo.comp f (ERLexMorNQuo.id tgt) = f :=
  Quotient.ind
    (motive := fun f =>
      ERLexMorNQuo.comp
        f (ERLexMorNQuo.id tgt) = f)
    (fun f_raw =>
      Quotient.sound
        (s := erLexMorNSetoid src tgt)
        (fun ctx _ => by
          simp only [ERLexMorN.comp,
            ERLexMorN.id,
            ERMorN.interp_comp,
            ERMorN.interp_id]))
    f
```

Same structure as `id_comp`.

- [ ] **Step 3: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Prove identity laws for ERLexMorNQuo"
```

---

### Task 7: Associativity

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Prove `ERLexMorNQuo.comp_assoc`**

```lean
/-- Associativity of composition. -/
theorem ERLexMorNQuo.comp_assoc
    {a b c d : LexObj}
    (f : ERLexMorNQuo a b)
    (g : ERLexMorNQuo b c)
    (h : ERLexMorNQuo c d) :
    ERLexMorNQuo.comp
      (ERLexMorNQuo.comp f g) h =
    ERLexMorNQuo.comp f
      (ERLexMorNQuo.comp g h) :=
  Quotient.ind
    (motive := fun f =>
      ∀ (g : ERLexMorNQuo b c)
        (h : ERLexMorNQuo c d),
        ERLexMorNQuo.comp
          (ERLexMorNQuo.comp f g) h =
        ERLexMorNQuo.comp f
          (ERLexMorNQuo.comp g h))
    (fun f_raw =>
      Quotient.ind
        (motive := fun g =>
          ∀ (h : ERLexMorNQuo c d),
            ERLexMorNQuo.comp
              (ERLexMorNQuo.comp
                (Quotient.mk _ f_raw) g) h =
            ERLexMorNQuo.comp
              (Quotient.mk _ f_raw)
              (ERLexMorNQuo.comp g h))
        (fun g_raw =>
          Quotient.ind
            (motive := fun h =>
              ERLexMorNQuo.comp
                (ERLexMorNQuo.comp
                  (Quotient.mk _ f_raw)
                  (Quotient.mk _ g_raw)) h =
              ERLexMorNQuo.comp
                (Quotient.mk _ f_raw)
                (ERLexMorNQuo.comp
                  (Quotient.mk _ g_raw) h))
            (fun h_raw =>
              Quotient.sound
                (s := erLexMorNSetoid a d)
                (fun ctx _ => by
                  simp only [ERLexMorN.comp,
                    ERMorN.interp_comp]))))
    f g h
```

Proof: triple `Quotient.ind`, then after simp both
sides reduce to
`h_raw.val.interp (g_raw.val.interp (f_raw.val.interp
ctx))`.

- [ ] **Step 2: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Prove ERLexMorNQuo associativity"
```

---

### Task 8: Assemble Category instance

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Define `LawvereERLexCat` and instances**

Append before `end GebLean`:

```lean
/-- The finite-limit category of decidable
ER-subobjects.  Objects are `LexObj`s; morphisms are
equivalence classes of `ERLexMorN` tuples.  Finite
products, equalizers, and the embedding from
`LawvereERCat` are developed in subsequent
modules. -/
@[reducible] def LawvereERLexCat := LexObj

instance : CategoryStruct LawvereERLexCat where
  Hom := ERLexMorNQuo
  id obj := ERLexMorNQuo.id obj
  comp f g := ERLexMorNQuo.comp f g

instance : Category LawvereERLexCat where
  id_comp := ERLexMorNQuo.id_comp
  comp_id := ERLexMorNQuo.comp_id
  assoc := ERLexMorNQuo.comp_assoc
```

- [ ] **Step 2: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Assemble LawvereERLexCat Category instance"
```

---

### Task 9: Sanity tests

**Files:**

- Create: `GebLeanTests/LawvereERLex.lean`
- Modify: `GebLeanTests.lean`

- [ ] **Step 1: Create test file**

```lean
import GebLean.LawvereERLex

/-!
# Tests for LawvereERLex

Sanity tests for the decidable ER-subobject category.
-/

open GebLean
open CategoryTheory

-- The always-one predicate at arity 0: the constant
-- successor applied to zero at the empty context.
private def oneZero : ERMor1 0 :=
  ERMor1.comp ERMor1.succ
    (fun (_ : Fin 1) =>
      ERMor1.comp ERMor1.zero Fin.elim0)

-- oneZero evaluates to 1 at the empty context.
example : oneZero.interp Fin.elim0 = 1 := rfl

-- As a Boolean predicate at arity 0.
private def truePred0 : ERBoolPred 0 :=
  { pred := oneZero
    bool := fun _ => by
      show oneZero.interp _ ≤ 1
      rfl }

-- Construct an object.
private def trueObj0 : LexObj :=
  { arity := 0, pred := truePred0 }

-- Category instance is inferred.
example : Category LawvereERLexCat := inferInstance

-- Identity composed with itself yields identity.
example :
    (𝟙 trueObj0 : trueObj0 ⟶ trueObj0) ≫
    (𝟙 trueObj0) = 𝟙 trueObj0 := by
  rw [Category.id_comp]
```

Note: if the `bool` proof for `truePred0` does not
go through with `show ... ≤ 1; rfl`, try
`fun _ => Nat.le_refl 1` or adapt to the actual
goal.

- [ ] **Step 2: Add import to `GebLeanTests.lean`**

Insert `import GebLeanTests.LawvereERLex` alphabetically
after `import GebLeanTests.LawvereERInterp`.

- [ ] **Step 3: Build and test**

Run: `lake build && lake test`
Expected: clean build, all tests pass.

- [ ] **Step 4: Commit**

```bash
git add GebLeanTests/LawvereERLex.lean \
  GebLeanTests.lean
git commit -m "Add LawvereERLex sanity tests"
```

---

### Task 10: Update workstream tracker

**Files:**

- Modify: `.session/workstreams/lawvere-elementary-recursive.md`

- [ ] **Step 1: Update status section**

Extend the status paragraph to note that Phase 4a is
complete:

"Phase 4a complete: see `GebLean/LawvereERLex.lean` for
`ERBoolPred`, `LexObj`, the subtype-plus-quotient
morphism construction, category laws, and the
`Category` instance on `LawvereERLexCat`.  Subsequent
sub-phases (4b: Boolean operations; 4c: finite
products; 4d: equalizers; 4e: embedding Δ) remain
open."

- [ ] **Step 2: Update task checkboxes**

The existing Phase 4 entry:
```
* [ ] Phase 4: definable-subobject finite-limit category.
```

Replace with:
```
* [ ] Phase 4: definable-subobject finite-limit category.
  * [x] 4a: Objects, morphisms, category structure.
  * [ ] 4b: Boolean operations on ER terms.
  * [ ] 4c: Finite products.
  * [ ] 4d: Equalizers and finite limits.
  * [ ] 4e: Full-and-faithful embedding Δ.
```

- [ ] **Step 3: Commit**

```bash
git add \
  .session/workstreams/lawvere-elementary-recursive.md
git commit -m \
  "Mark ER Phase 4a complete in workstream tracker"
```
