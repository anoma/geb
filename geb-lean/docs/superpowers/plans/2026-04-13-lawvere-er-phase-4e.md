# Lawvere ER Phase 4e: Full-and-Faithful Embedding `Δ : LawvereERCat ⥤ LawvereERLexCat`

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Construct the canonical functor
`Δ : LawvereERCat ⥤ LawvereERLexCat` sending arity `n`
to the trivially-cut-out object `(n, ⊤)`, prove it is
full and faithful, and prove it preserves finite
products.  This packages the embedding of the bare
Lawvere theory into its finite-limit completion.

**Architecture:** `Δ.obj n = ⟨n, ERBoolPredE.alwaysTrue
n⟩`.  On morphisms, lift `ERMorNQuo n m` through
`Quotient.lift` to `ERLexMorNQuo (Δ n) (Δ m)`, using
the always-trivial respect proof (target predicate is
`⊤`).  Faithfulness is the converse lift; fullness uses
a preimage construction (well-defined modulo
representatives).  Product preservation is on-the-nose
because `ERBoolPredE.and ⊤ ⊤ = ⊤` literally
(via Phase 4d.2's `eval_injective`), making
`Δ.obj (n + m) = LexObj.prod (Δ.obj n) (Δ.obj m)` an
equality of `LexObj` values.

**Tech Stack:** Lean 4, Mathlib
(`CategoryTheory.Functor.FullyFaithful`,
`CategoryTheory.Limits.Preserves.Basic`,
`CategoryTheory.Limits.Preserves.Shapes.Terminal`,
`CategoryTheory.Limits.Preserves.Shapes.BinaryProducts`,
`CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts`).

---

## File Map

| File | Role |
| ---- | ---- |
| Create: `GebLean/LawvereERDelta.lean` | Δ functor, Faithful/Full instances, preserves-finite-products |
| Modify: `GebLean.lean` | Add `import GebLean.LawvereERDelta` |
| Create: `GebLeanTests/LawvereERDelta.lean` | Sanity tests for Δ |
| Modify: `GebLeanTests.lean` | Add test import |
| Modify: `.session/workstreams/lawvere-elementary-recursive.md` | Mark Phase 4e complete |

---

### Task 1: File creation, imports, `Δ.obj`

**Files:**

- Create: `GebLean/LawvereERDelta.lean`
- Modify: `GebLean.lean`

- [ ] **Step 1: Create the file with header and `Δ` object map**

```lean
import GebLean.LawvereERLex
import GebLean.LawvereERQuot
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Limits.Preserves.Basic
-- 81 chars (external mathlib path)
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Terminal
-- 87 chars (external mathlib path)
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.BinaryProducts
-- 80 chars (external mathlib path)
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Embedding `Δ : LawvereERCat ⥤ LawvereERLexCat`

Defines the canonical embedding of `LawvereERCat`
(the Lawvere theory of elementary recursive
functions) into `LawvereERLexCat` (its finite-limit
completion via decidable subobjects), sending arity
`n` to the object `(n, ⊤)` cut out by the always-true
predicate.

Proves Δ is full and faithful and preserves finite
products.
-/

namespace GebLean

open CategoryTheory

/-- Object map of the embedding: arity `n` is sent to
`(n, ⊤)`, the object whose predicate is the
constantly-true predicate at arity `n`. -/
def erDelta.obj (n : LawvereERCat) : LawvereERLexCat :=
  { arity := n, pred := ERBoolPredE.alwaysTrue n }

end GebLean
```

- [ ] **Step 2: Add import to `GebLean.lean`**

Insert `import GebLean.LawvereERDelta` alphabetically
in `GebLean.lean`.

- [ ] **Step 3: Build**

Run: `lake build`
Expected: clean build.

- [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereERDelta.lean GebLean.lean
git commit -m "Add LawvereERDelta with object map of Δ"
```

---

### Task 2: Raw and quotient morphism lifts

**Files:**

- Modify: `GebLean/LawvereERDelta.lean`

- [ ] **Step 1: Add raw morphism lift `erDeltaRaw`**

Append before `end GebLean`:

```lean
/-- Raw morphism lift: an `ERMorN n m` becomes an
`ERLexMorN` from `(n, ⊤)` to `(m, ⊤)`.  The respect
proof is trivial because the target predicate `⊤`
always evaluates to `1`. -/
def erDeltaRaw {n m : ℕ} (f : ERMorN n m) :
    ERLexMorN (erDelta.obj n) (erDelta.obj m) :=
  ⟨f, fun _ _ => rfl⟩
```

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Add quotient morphism lift `erDelta.map`**

```lean
/-- Morphism map of the embedding: lift through the
quotient.  Well-defined because full extensional
equality of `ERMorN` tuples implies their lifted
forms agree on `⊤`-satisfying contexts (which is
all contexts). -/
def erDelta.map {n m : ℕ} (f : ERMorNQuo n m) :
    ERLexMorNQuo (erDelta.obj n) (erDelta.obj m) :=
  Quotient.lift
    (s := erMorNSetoid n m)
    (fun f' =>
      Quotient.mk
        (erLexMorNSetoid (erDelta.obj n)
          (erDelta.obj m))
        (erDeltaRaw f'))
    (fun _ _ h =>
      Quotient.sound
        (s := erLexMorNSetoid (erDelta.obj n)
          (erDelta.obj m))
        (fun ctx _ => h ctx))
    f
```

- [ ] **Step 4: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERDelta.lean
git commit -m "Add Δ raw and quotient morphism lifts"
```

---

### Task 3: Functor laws

**Files:**

- Modify: `GebLean/LawvereERDelta.lean`

- [ ] **Step 1: Prove `erDelta.map` preserves identity**

Append:

```lean
/-- Δ preserves identity morphisms. -/
theorem erDelta.map_id (n : LawvereERCat) :
    erDelta.map (ERMorNQuo.id n) =
      ERLexMorNQuo.id (erDelta.obj n) := by
  -- Both sides reduce by Quotient.lift / Quotient.mk
  -- to the same quotient class of the identity
  -- ERMorN tuple.
  rfl
```

If `rfl` does not close, the implementer should
unfold via `Quotient.lift` computation:

```lean
  show Quotient.mk _ (erDeltaRaw (ERMorN.id n)) =
       Quotient.mk _ (ERLexMorN.id (erDelta.obj n))
  apply Quotient.sound
  intro _ _
  rfl
```

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Prove `erDelta.map` preserves
  composition**

```lean
/-- Δ preserves composition of morphisms. -/
theorem erDelta.map_comp {n m k : ℕ}
    (f : ERMorNQuo n m) (g : ERMorNQuo m k) :
    erDelta.map (ERMorNQuo.comp f g) =
      ERLexMorNQuo.comp (erDelta.map f)
        (erDelta.map g) := by
  refine Quotient.ind₂ ?_ f g
  intro f_raw g_raw
  rfl
```

If `rfl` does not close at the end, fall back to:

```lean
  apply Quotient.sound
  intro _ _
  rfl
```

- [ ] **Step 4: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERDelta.lean
git commit -m "Prove Δ functor laws (id and comp)"
```

---

### Task 4: Assemble Δ as a `Functor`

**Files:**

- Modify: `GebLean/LawvereERDelta.lean`

- [ ] **Step 1: Define the `erDeltaFunctor`**

Append:

```lean
/-- The full and faithful embedding
`LawvereERCat ⥤ LawvereERLexCat` sending arity `n`
to the object `(n, ⊤)` and morphisms via
`erDelta.map`. -/
def erDeltaFunctor :
    LawvereERCat ⥤ LawvereERLexCat where
  obj := erDelta.obj
  map := erDelta.map
  map_id := erDelta.map_id
  map_comp := erDelta.map_comp
```

- [ ] **Step 2: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERDelta.lean
git commit -m "Assemble erDeltaFunctor as a CategoryTheory.Functor"
```

---

### Task 5: Faithful instance

**Files:**

- Modify: `GebLean/LawvereERDelta.lean`

- [ ] **Step 1: Prove `erDeltaFunctor.Faithful`**

Append:

```lean
/-- Δ is faithful: distinct ER morphism classes give
distinct `LawvereERLexCat` morphism classes.  This
is immediate because the source-restricted setoid on
the always-true predicate `⊤` reduces to full
extensional equality. -/
instance : erDeltaFunctor.Faithful where
  map_injective {n m} {f g} h := by
    revert f g
    refine Quotient.ind₂ ?_
    intro f_raw g_raw heq
    apply Quotient.sound
      (s := erMorNSetoid n m)
    intro ctx
    have hrel := Quotient.exact
      (s := erLexMorNSetoid (erDelta.obj n)
        (erDelta.obj m)) heq
    -- hrel : ∀ ctx, ⊤.eval ctx = 1 → f_raw.interp
    --        ctx = g_raw.interp ctx
    -- Since ⊤.eval is always 1, the precondition
    -- is automatic.
    exact hrel ctx rfl
```

If `rfl` does not satisfy `⊤.eval ctx = 1`, the
implementer should adapt — the Boolean closure of the
constant-1 predicate gives this trivially.

- [ ] **Step 2: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERDelta.lean
git commit -m "Prove erDeltaFunctor.Faithful"
```

---

### Task 6: Full instance

**Files:**

- Modify: `GebLean/LawvereERDelta.lean`

- [ ] **Step 1: Add preimage helper**

Append:

```lean
/-- Preimage of a `LawvereERLexCat` morphism between
trivially-cut-out objects.  Lifts through the
quotient by extracting the underlying `ERMorN` tuple;
well-defined because source-restricted equivalence
under `⊤` reduces to full extensional equality. -/
def erDelta.preimage {n m : ℕ}
    (h : ERLexMorNQuo (erDelta.obj n)
      (erDelta.obj m)) :
    ERMorNQuo n m :=
  Quotient.lift
    (s := erLexMorNSetoid (erDelta.obj n)
      (erDelta.obj m))
    (fun h_raw =>
      Quotient.mk (erMorNSetoid n m) h_raw.val)
    (fun _ _ hrel =>
      Quotient.sound
        (s := erMorNSetoid n m)
        (fun ctx => hrel ctx rfl))
    h
```

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Prove `erDelta.map_preimage`
  (round-trip)**

```lean
/-- The preimage is a section of `Δ.map`: applying
Δ to the preimage of `h` recovers `h`. -/
theorem erDelta.map_preimage {n m : ℕ}
    (h : ERLexMorNQuo (erDelta.obj n)
      (erDelta.obj m)) :
    erDelta.map (erDelta.preimage h) = h := by
  refine Quotient.ind ?_ h
  intro h_raw
  apply Quotient.sound
    (s := erLexMorNSetoid (erDelta.obj n)
      (erDelta.obj m))
  intro ctx _
  rfl
```

- [ ] **Step 4: Build**

Run: `lake build`

- [ ] **Step 5: Prove `erDeltaFunctor.Full`**

```lean
/-- Δ is full: every `LawvereERLexCat` morphism
between trivially-cut-out objects comes from a
unique `LawvereERCat` morphism (uniqueness via
faithfulness; existence via `erDelta.preimage`). -/
instance : erDeltaFunctor.Full where
  map_surjective {n m} h :=
    ⟨erDelta.preimage h, erDelta.map_preimage h⟩
```

- [ ] **Step 6: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERDelta.lean
git commit -m "Prove erDeltaFunctor.Full via preimage construction"
```

---

### Task 7: Preserves terminal

**Files:**

- Modify: `GebLean/LawvereERDelta.lean`

- [ ] **Step 1: Show `Δ.obj 0 = LexObj.terminal`
  literally**

Append a witnessing equality lemma:

```lean
/-- Δ sends the source terminal `0` literally to
the target terminal `LexObj.terminal`. -/
theorem erDelta.obj_terminal :
    erDelta.obj (0 : LawvereERCat) =
      LexObj.terminal :=
  rfl
```

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Prove preservation of the terminal cone**

The mathlib API for terminal preservation uses
`PreservesLimit (Functor.empty C) F` or
`PreservesTerminal F`.  Construct the instance:

```lean
/-- Δ preserves terminal objects.  The image of the
source terminal (object `0`) is exactly the target
chosen terminal `LexObj.terminal`, so the preserved
cone is identical to the chosen one. -/
instance :
    Limits.PreservesLimit
      (Functor.empty LawvereERCat) erDeltaFunctor :=
  Limits.preservesTerminalOfIsIso _

```

If `preservesTerminalOfIsIso` requires more setup,
the implementer may need a more explicit
construction.  Alternative direct proof:

```lean
instance :
    Limits.PreservesLimit
      (Functor.empty LawvereERCat) erDeltaFunctor :=
  ⟨fun {c} hc => by
    -- c is a cone (terminal in source)
    -- Need: erDeltaFunctor.mapCone c is a limit
    apply Limits.IsLimit.ofIsoLimit
      (lawvereERLexTerminal.terminalIsTerminal)
    sorry⟩
```

The implementer should consult mathlib for the
clearest approach — likely `preservesTerminalOfIso`
or `IsTerminal.preservesLimit`.

If a direct instance is hard to find, derive via
`PreservesTerminal`:

```lean
instance : Limits.PreservesTerminal erDeltaFunctor := by
  apply Limits.preservesTerminal_of_iso
  exact Iso.refl _
```

- [ ] **Step 4: Add `PreservesLimitsOfShape (Discrete
  PEmpty)` instance**

For use in `PreservesFiniteProducts`:

```lean
instance :
    Limits.PreservesLimitsOfShape
      (Discrete PEmpty.{1}) erDeltaFunctor :=
  ⟨fun {K} =>
    Limits.preservesLimit_of_preserves_terminal_object
      _ K⟩
```

The exact mathlib name may differ; the implementer
should locate the right combinator.  The intent:
"preserving terminal ⟹ preserving the empty-discrete
limit of any shape `K`".

- [ ] **Step 5: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERDelta.lean
git commit -m "Prove Δ preserves the terminal object"
```

---

### Task 8: Preserves binary products

**Files:**

- Modify: `GebLean/LawvereERDelta.lean`

- [ ] **Step 1: Show `Δ.obj (n + m) = LexObj.prod
  (Δ.obj n) (Δ.obj m)` via `eval_injective`**

The two LexObj values both have arity `n + m`.
Their predicates are `ERBoolPredE.alwaysTrue (n+m)`
and `ERBoolPredE.and (alwaysTrue n) (alwaysTrue m)`
respectively.  These are extensionally equal (eval is
1 in both cases), hence equal as ERBoolPredE values
by `eval_injective`.  Wrapping in LexObj structure
equality:

```lean
/-- Δ sends the source binary product `n + m`
literally to the target chosen product `LexObj.prod
(Δ.obj n) (Δ.obj m)`.  The arities match by
definition; the predicates are equal because
`⊤ ⊓ ⊤ = ⊤` extensionally (Phase 4d.2 makes this
literal equality of `ERBoolPredE` values). -/
theorem erDelta.obj_prod (n m : ℕ) :
    erDelta.obj (n + m) =
      LexObj.prod (erDelta.obj n) (erDelta.obj m) := by
  congr 1
  apply ERBoolPredE.eval_injective
  intro ctx
  show 1 = (ERBoolPredE.alwaysTrue n).eval _ *
    (ERBoolPredE.alwaysTrue m).eval _
  simp only [ERBoolPredE.alwaysTrue_eval]
```

If `congr 1` does not split the LexObj equality,
the implementer should construct the equality
explicitly using `LexObj.mk.injEq` or similar.

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Prove preservation of binary products**

Construct the `PreservesLimit (pair n m)` instance:

```lean
/-- Δ preserves binary products: the image of the
source chosen product cone is the target chosen
product cone (literally, after object_prod). -/
instance preservesPair (n m : LawvereERCat) :
    Limits.PreservesLimit
      (Limits.pair n m) erDeltaFunctor :=
  Limits.preservesLimit_of_preserves_limit_cone
    (lawvereERProduct n m).fst.isLimit -- or similar
    sorry
```

The implementer should consult mathlib for the
cleanest path.  The intent is: "given the source
chosen product is a limit and Δ takes it to the
target chosen product (which is also a limit), Δ
preserves this limit."

If a direct construction proves difficult, use
`preservesLimit_of_evaluation` or derive via
`HasChosenFiniteProducts`-friendly combinators.

- [ ] **Step 4: Add `PreservesLimitsOfShape (Discrete
  WalkingPair)` instance**

```lean
instance :
    Limits.PreservesLimitsOfShape
      (Discrete Limits.WalkingPair) erDeltaFunctor := by
  refine ⟨fun {K} => ?_⟩
  -- K : Discrete WalkingPair ⥤ LawvereERCat
  -- need: PreservesLimit K erDeltaFunctor
  -- K is essentially `pair (K.obj ⟨left⟩) (K.obj ⟨right⟩)`
  sorry
```

- [ ] **Step 5: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERDelta.lean
git commit -m "Prove Δ preserves binary products"
```

---

### Task 9: Derive `PreservesFiniteProducts`

**Files:**

- Modify: `GebLean/LawvereERDelta.lean`

- [ ] **Step 1: Use mathlib's combinator**

```lean
/-- Δ preserves finite products, derived from
preservation of binary products and the terminal
via mathlib's standard combinator. -/
instance :
    Limits.PreservesFiniteProducts erDeltaFunctor :=
  Limits.PreservesFiniteProducts.of_preserves_binary_and_terminal
    erDeltaFunctor
```

- [ ] **Step 2: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERDelta.lean
git commit -m "Derive PreservesFiniteProducts for Δ"
```

---

### Task 10: Tests and workstream tracker

**Files:**

- Create: `GebLeanTests/LawvereERDelta.lean`
- Modify: `GebLeanTests.lean`
- Modify: `.session/workstreams/lawvere-elementary-recursive.md`

- [ ] **Step 1: Create test file**

Create `GebLeanTests/LawvereERDelta.lean`:

```lean
import GebLean.LawvereERDelta

/-!
# Tests for LawvereERDelta

Sanity tests for the embedding `Δ : LawvereERCat ⥤
LawvereERLexCat` and its full/faithful/preserves-
products instances.
-/

open GebLean
open CategoryTheory

-- Faithful instance is available.
example : erDeltaFunctor.Faithful := inferInstance

-- Full instance is available.
example : erDeltaFunctor.Full := inferInstance

-- PreservesFiniteProducts instance is available.
example :
    Limits.PreservesFiniteProducts erDeltaFunctor :=
  inferInstance

-- Δ sends 0 to the terminal LexObj.
example : erDeltaFunctor.obj (0 : LawvereERCat) =
    LexObj.terminal := rfl

-- Δ sends 2 to (2, ⊤).
example :
    (erDeltaFunctor.obj (2 : LawvereERCat)).arity =
      2 := rfl
```

- [ ] **Step 2: Add import to `GebLeanTests.lean`**

Insert `import GebLeanTests.LawvereERDelta` alphabetically.

- [ ] **Step 3: Build and test**

Run: `lake build && lake test`
Expected: clean build, tests pass.

- [ ] **Step 4: Commit tests**

```bash
git add GebLeanTests/LawvereERDelta.lean GebLeanTests.lean
git commit -m "Add Phase 4e Δ functor sanity tests"
```

- [ ] **Step 5: Update workstream tracker**

Append to the status section in
`.session/workstreams/lawvere-elementary-recursive.md`:

"Phase 4e complete: see `GebLean/LawvereERDelta.lean`
for the embedding `erDeltaFunctor : LawvereERCat ⥤
LawvereERLexCat` (sending arity `n` to the
trivially-cut-out object `(n, ⊤)`), with `Faithful`
and `Full` instances and a `PreservesFiniteProducts`
instance derived from preservation of binary
products and the terminal."

Update the task checkbox:

```
  * [ ] 4e: Full-and-faithful embedding Δ.
```

To:

```
  * [x] 4e: Full-and-faithful embedding Δ
    (with PreservesFiniteProducts).
```

- [ ] **Step 6: Commit tracker update**

```bash
git add \
  .session/workstreams/lawvere-elementary-recursive.md
git commit -m "Mark ER Phase 4e complete in workstream tracker"
```
