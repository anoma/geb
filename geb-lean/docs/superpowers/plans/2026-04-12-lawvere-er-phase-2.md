# Lawvere ER Phase 2: Extensional-Equality Quotient

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Build the quotient category `LawvereERCat` whose
morphisms are equivalence classes of `ERMorN` tuples under
extensional equality of their standard interpretations.

**Architecture:** Define a setoid on `ERMorN n m` whose
relation is `∀ ctx, f.interp ctx = g.interp ctx`, then
quotient by it.  Lift identity and composition through
`Quotient.mk`/`Quotient.lift₂`, prove category laws via
the `interp_id`/`interp_comp` simp lemmas from Phase 1,
and assemble a Mathlib `Category` instance on `ℕ`.

**Tech Stack:** Lean 4, Mathlib (`CategoryTheory.Category.Basic`,
`Data.Fin.Tuple.Basic`)

---

## File Map

| File | Role |
| ---- | ---- |
| Create: `GebLean/LawvereERQuot.lean` | Setoid, quotient type, lifted operations, category laws, `Category` instance |
| Modify: `GebLean.lean` | Add `import GebLean.LawvereERQuot` |
| Create: `GebLeanTests/LawvereERQuot.lean` | Sanity tests for quotient construction |
| Modify: `GebLeanTests.lean` | Add `import GebLeanTests.LawvereERQuot` |

---

## Proof Strategy

The BT development (`LawvereBTQuot.lean`) quotients by an
inductive congruence relation `btMorRel` and proves
well-definedness of composition via a syntactic lemma
`subst_cong`.  The ER development uses a direct extensional
quotient, so well-definedness and category laws are proved
entirely via the interpretation lemmas from Phase 1.

All proofs go through the same pattern:

1. Unwrap quotients with `Quotient.ind`.
2. Reduce to a statement about `ERMorN.interp` using
   `interp_comp` and/or `interp_id`.
3. Close with `Quotient.sound` (when showing two terms
   are equal in the quotient) or `congrArg` (when
   rewriting under `Quotient.mk`).

---

### Task 1: Create the quotient file with setoid definition

**Files:**

- Create: `GebLean/LawvereERQuot.lean`
- Modify: `GebLean.lean` (add import)

- [ ] **Step 1: Create `GebLean/LawvereERQuot.lean`
  with module header and setoid**

```lean
import GebLean.LawvereER
import Mathlib.CategoryTheory.Category.Basic

/-!
# Quotient Category of Elementary Recursive Functions

Defines the quotient of `ERMorN` tuples by extensional
equality of their standard interpretations, yielding a
category `LawvereERCat` whose morphisms from `n` to `m`
are equivalence classes of `m`-tuples of `n`-ary
elementary recursive functions.
-/

namespace GebLean

open CategoryTheory

/-- The setoid on `ERMorN n m` induced by extensional
equality of interpretations: two morphism tuples are
related when their interpretations agree on every
context. -/
def erMorNSetoid (n m : ℕ) :
    Setoid (ERMorN n m) where
  r f g := ∀ ctx : Fin n → ℕ,
    f.interp ctx = g.interp ctx
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h ctx => (h ctx).symm
    trans := fun h1 h2 ctx =>
      (h1 ctx).trans (h2 ctx)
  }

end GebLean
```

- [ ] **Step 2: Add import to `GebLean.lean`**

Insert `import GebLean.LawvereERQuot` alphabetically
after the `import GebLean.LawvereER` line.

- [ ] **Step 3: Build**

Run: `lake build`
Expected: clean build, no warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereERQuot.lean GebLean.lean
git commit -m "Add erMorNSetoid for ER extensional quotient"
```

---

### Task 2: Define the quotient type, identity, and mk

**Files:**

- Modify: `GebLean/LawvereERQuot.lean`

- [ ] **Step 1: Add quotient type and identity**

Append before `end GebLean`:

```lean
/-- Quotient morphism type for the Lawvere theory of
elementary recursive functions: equivalence classes of
`ERMorN n m` tuples under extensional equality. -/
def ERMorNQuo (n m : ℕ) : Type :=
  Quotient (erMorNSetoid n m)

/-- The identity morphism in the quotient category:
the equivalence class of the tuple of projections. -/
def ERMorNQuo.id (n : ℕ) : ERMorNQuo n n :=
  Quotient.mk (erMorNSetoid n n) (ERMorN.id n)
```

- [ ] **Step 2: Build**

Run: `lake build`
Expected: clean build, no warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLean/LawvereERQuot.lean
git commit -m "Add ERMorNQuo quotient type and identity"
```

---

### Task 3: Lift composition through the quotient

**Files:**

- Modify: `GebLean/LawvereERQuot.lean`

- [ ] **Step 1: Define `ERMorNQuo.comp`**

The well-definedness argument: if `f ~ f'` and `g ~ g'`
(extensionally equal), then `f.comp g ~ f'.comp g'`.  By
`interp_comp`, `(f.comp g).interp ctx = g.interp
(f.interp ctx)`.  Since `f ~ f'`, `f.interp ctx =
f'.interp ctx`.  Since `g ~ g'`, `g.interp (f'.interp
ctx) = g'.interp (f'.interp ctx)`.  Composing gives the
result.

Append before `end GebLean`:

```lean
/-- Composition of quotient morphisms, lifted from
`ERMorN.comp` via `Quotient.lift₂`.  Well-definedness
follows from the fact that extensionally equal tuples
compose to extensionally equal results. -/
def ERMorNQuo.comp {n m k : ℕ}
    (f : ERMorNQuo n m) (g : ERMorNQuo m k) :
    ERMorNQuo n k :=
  Quotient.lift₂
    (s₁ := erMorNSetoid n m)
    (s₂ := erMorNSetoid m k)
    (fun f' g' =>
      Quotient.mk (erMorNSetoid n k)
        (ERMorN.comp f' g'))
    (fun fa fb ga gb hf hg =>
      Quotient.sound
        (s := erMorNSetoid n k)
        (fun ctx => by
          simp [ERMorN.interp_comp]
          rw [hf ctx, hg (fa.interp ctx)]))
    f g
```

Note: the `simp` should unfold `ERMorN.interp_comp` so
the goal becomes about the component interpretations.
If `simp` is too aggressive or insufficient, replace
with explicit `show` and `calc` steps:

```lean
        (fun ctx => by
          show (ERMorN.comp fa ga).interp ctx =
               (ERMorN.comp fb gb).interp ctx
          simp only [ERMorN.interp_comp]
          rw [hf ctx, hg (fa.interp ctx)])
```

The `rw [hf ctx]` rewrites `fa.interp ctx` to
`fb.interp ctx` in the goal, then `rw [hg ...]`
finishes because `ga.interp (fb.interp ctx) =
gb.interp (fb.interp ctx)`.

Wait: the `hg` hypothesis says
`∀ ctx, ga.interp ctx = gb.interp ctx`, so
`hg (fb.interp ctx)` gives
`ga.interp (fb.interp ctx) = gb.interp (fb.interp ctx)`.
But after `rw [hf ctx]`, the LHS has `ga.interp
(fb.interp ctx)` and the RHS has `gb.interp
(fb.interp ctx)`.  So `rw [hg (fb.interp ctx)]` closes
the goal.  But the original form `hg (fa.interp ctx)`
would not work after `rw [hf ctx]` has already changed
`fa` to `fb`.  So the correct sequence is:

```lean
          rw [hf ctx, hg (fb.interp ctx)]
```

or equivalently, use `congr 1` after simp:

```lean
          simp only [ERMorN.interp_comp]
          congr 1
          · exact hf ctx
          · rw [hf ctx]; exact hg (fb.interp ctx)
```

The implementer should try the simplest approach first
(`simp` + `rw`) and fall back to the `congr` approach if
needed.  The proof obligation is:

```
ga.interp (fa.interp ctx) = gb.interp (fb.interp ctx)
```

which factors as:

```
ga.interp (fa.interp ctx)
  = ga.interp (fb.interp ctx)   -- by hf ctx
  = gb.interp (fb.interp ctx)   -- by hg (fb.interp ctx)
```

A `calc` block may be clearest:

```lean
        (fun ctx => by
          simp only [ERMorN.interp_comp]
          calc ga.interp (fa.interp ctx)
              _ = ga.interp (fb.interp ctx) :=
                by rw [hf ctx]
              _ = gb.interp (fb.interp ctx) :=
                hg (fb.interp ctx)))
```

- [ ] **Step 2: Build**

Run: `lake build`
Expected: clean build, no warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLean/LawvereERQuot.lean
git commit -m "Add ERMorNQuo.comp with quotient lifting"
```

---

### Task 4: Prove category laws on the quotient

**Files:**

- Modify: `GebLean/LawvereERQuot.lean`

- [ ] **Step 1: Prove `ERMorNQuo.id_comp`**

Append before `end GebLean`:

```lean
/-- Left identity: `comp (id n) f = f`. -/
theorem ERMorNQuo.id_comp {n m : ℕ}
    (f : ERMorNQuo n m) :
    ERMorNQuo.comp (ERMorNQuo.id n) f = f :=
  Quotient.ind
    (motive := fun f =>
      ERMorNQuo.comp (ERMorNQuo.id n) f = f)
    (fun f_raw =>
      Quotient.sound
        (s := erMorNSetoid n m)
        (fun ctx => by
          simp [ERMorN.interp_comp,
                ERMorN.interp_id]))
    f
```

The proof: unwrap `f` as `Quotient.mk _ f_raw`, then
show `Quotient.mk _ ((ERMorN.id n).comp f_raw) =
Quotient.mk _ f_raw` via `Quotient.sound`, which
requires `∀ ctx, ((ERMorN.id n).comp f_raw).interp ctx =
f_raw.interp ctx`.  By `interp_comp` and `interp_id`,
`((ERMorN.id n).comp f_raw).interp ctx = f_raw.interp
((ERMorN.id n).interp ctx) = f_raw.interp ctx`.

- [ ] **Step 2: Build and check**

Run: `lake build`
Expected: clean build.

- [ ] **Step 3: Prove `ERMorNQuo.comp_id`**

```lean
/-- Right identity: `comp f (id m) = f`. -/
theorem ERMorNQuo.comp_id {n m : ℕ}
    (f : ERMorNQuo n m) :
    ERMorNQuo.comp f (ERMorNQuo.id m) = f :=
  Quotient.ind
    (motive := fun f =>
      ERMorNQuo.comp f (ERMorNQuo.id m) = f)
    (fun f_raw =>
      Quotient.sound
        (s := erMorNSetoid n m)
        (fun ctx => by
          simp [ERMorN.interp_comp,
                ERMorN.interp_id]))
    f
```

The proof: `(f_raw.comp (ERMorN.id m)).interp ctx =
(ERMorN.id m).interp (f_raw.interp ctx) = f_raw.interp
ctx` by `interp_comp` then `interp_id`.

- [ ] **Step 4: Build and check**

Run: `lake build`
Expected: clean build.

- [ ] **Step 5: Prove `ERMorNQuo.comp_assoc`**

```lean
/-- Associativity of composition in the quotient. -/
theorem ERMorNQuo.comp_assoc {n m k l : ℕ}
    (f : ERMorNQuo n m)
    (g : ERMorNQuo m k)
    (h : ERMorNQuo k l) :
    ERMorNQuo.comp (ERMorNQuo.comp f g) h =
      ERMorNQuo.comp f (ERMorNQuo.comp g h) :=
  Quotient.ind
    (motive := fun f =>
      ∀ (g : ERMorNQuo m k)
        (h : ERMorNQuo k l),
        ERMorNQuo.comp
          (ERMorNQuo.comp f g) h =
          ERMorNQuo.comp f
            (ERMorNQuo.comp g h))
    (fun f_raw =>
      Quotient.ind
        (motive := fun g =>
          ∀ (h : ERMorNQuo k l),
            ERMorNQuo.comp
              (ERMorNQuo.comp
                (Quotient.mk _ f_raw) g) h =
              ERMorNQuo.comp
                (Quotient.mk _ f_raw)
                (ERMorNQuo.comp g h))
        (fun g_raw =>
          Quotient.ind
            (motive := fun h =>
              ERMorNQuo.comp
                (ERMorNQuo.comp
                  (Quotient.mk _ f_raw)
                  (Quotient.mk _ g_raw)) h =
                ERMorNQuo.comp
                  (Quotient.mk _ f_raw)
                  (ERMorNQuo.comp
                    (Quotient.mk _ g_raw) h))
            (fun h_raw =>
              Quotient.sound
                (s := erMorNSetoid n l)
                (fun ctx => by
                  simp [ERMorN.interp_comp]))))
    f g h
```

The proof: after three nested `Quotient.ind`s to unwrap
all three quotients, the goal reduces to showing
`((f_raw.comp g_raw).comp h_raw).interp ctx =
(f_raw.comp (g_raw.comp h_raw)).interp ctx`.  After
`simp [ERMorN.interp_comp]`, both sides reduce to
`h_raw.interp (g_raw.interp (f_raw.interp ctx))`.

- [ ] **Step 6: Build and check**

Run: `lake build`
Expected: clean build, no warnings.

- [ ] **Step 7: Commit**

```bash
git add GebLean/LawvereERQuot.lean
git commit -m "Prove category laws for ERMorNQuo"
```

---

### Task 5: Assemble the Category instance

**Files:**

- Modify: `GebLean/LawvereERQuot.lean`

- [ ] **Step 1: Define `LawvereERCat` and `Category` instance**

Append before `end GebLean`:

```lean
/-- The quotient Lawvere theory of elementary recursive
functions.  Objects are natural numbers (arities).
Morphisms are equivalence classes of `ERMorN` tuples
under extensional equality of their standard
interpretations. -/
@[reducible] def LawvereERCat := ℕ

instance : CategoryStruct LawvereERCat where
  Hom := ERMorNQuo
  id n := ERMorNQuo.id n
  comp f g := ERMorNQuo.comp f g

instance : Category LawvereERCat where
  id_comp := ERMorNQuo.id_comp
  comp_id := ERMorNQuo.comp_id
  assoc := ERMorNQuo.comp_assoc
```

- [ ] **Step 2: Build**

Run: `lake build`
Expected: clean build, no warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLean/LawvereERQuot.lean
git commit -m "Add LawvereERCat with Category instance"
```

---

### Task 6: Sanity tests and registration

**Files:**

- Create: `GebLeanTests/LawvereERQuot.lean`
- Modify: `GebLeanTests.lean` (add import)

- [ ] **Step 1: Create test file**

```lean
import GebLean.LawvereERQuot
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for LawvereERQuot

`example` sanity tests verifying quotient
identification and category-law discharge.
-/

open GebLean
open CategoryTheory

-- Two syntactically different ERMorN tuples that
-- are extensionally equal:
-- `comp (proj 0) [sub]` and `sub` are both binary
-- terms computing `ctx 0 - ctx 1`.
private def subDirect : ERMorN 2 1 :=
  fun _ => ERMor1.sub

private def subViaComp : ERMorN 2 1 :=
  fun _ => ERMor1.comp ERMor1.sub
    (fun i => ERMor1.proj i)

-- The two are identified in the quotient.
example : (Quotient.mk (erMorNSetoid 2 1) subDirect :
    ERMorNQuo 2 1) =
    Quotient.mk (erMorNSetoid 2 1) subViaComp :=
  Quotient.sound (s := erMorNSetoid 2 1)
    (fun _ => rfl)

-- Category identity composes correctly
-- (the `Category` instance is well-formed).
example : (𝟙 (2 : LawvereERCat)) ≫
    (𝟙 (2 : LawvereERCat)) =
    𝟙 (2 : LawvereERCat) := by
  rw [Category.id_comp]
```

- [ ] **Step 2: Add import to `GebLeanTests.lean`**

Insert `import GebLeanTests.LawvereERQuot` alphabetically
after the `import GebLeanTests.LawvereER` line.

- [ ] **Step 3: Build and test**

Run: `lake build && lake test`
Expected: clean build, all tests pass, no warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLeanTests/LawvereERQuot.lean GebLeanTests.lean
git commit -m "Add LawvereERQuot sanity tests"
```

---

### Task 7: Update workstream tracker

**Files:**

- Modify: `.session/workstreams/lawvere-elementary-recursive.md`

- [ ] **Step 1: Update status and check off Phase 2**

Update the status line to note Phase 2 is complete and
Phase 3 is unblocked.  Mark the Phase 2 task checkbox
as done.

- [ ] **Step 2: Commit**

```bash
git add .session/workstreams/lawvere-elementary-recursive.md
git commit -m "Mark ER Phase 2 complete in workstream tracker"
```
