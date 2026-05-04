# Lawvere ER Phase 4d.3: Mathlib Derivations for Equalizers and Finite Limits

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Derive Mathlib's `Prop`-valued
`Limits.HasEqualizers C` and `Limits.HasFiniteLimits C`
from our `Type`-valued `HasChosenEqualizers C` and
`HasChosenFiniteLimits C`.  This validates that the
chosen versions correctly present the standard
categorical notions, and gives downstream consumers
the standard Mathlib instances automatically.

**Architecture:** Mirrors the existing pattern in
`ComputableLimits.lean` for finite products:
construct a Mathlib limit cone for the parallel-pair
diagram from a `ChosenEqualizer`, prove it is a
limit, and lift to a `HasLimit` instance.  Then
`HasFiniteLimits` follows from `HasFiniteProducts +
HasEqualizers` via Mathlib's standard derivation.

**Tech Stack:** Lean 4, Mathlib
(`CategoryTheory.Limits.Shapes.Equalizers`,
`CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers`).

---

## File Map

| File | Role |
| ---- | ---- |
| Modify: `GebLean/Utilities/ComputableLimits.lean` | Add `chosenEqualizerIsLimit`, `chosenEqualizerToHasLimit`, `chosenToHasEqualizers`, and `chosenToHasFiniteLimits` derivations |

---

### Task 1: Import Mathlib equalizer machinery

**Files:**

- Modify: `GebLean/Utilities/ComputableLimits.lean`

- [ ] **Step 1: Add the equalizer-shape and finite-
  limits-from-products imports**

Edit the top of `GebLean/Utilities/ComputableLimits.lean`:

```lean
import Mathlib.CategoryTheory.Limits.HasLimits
import Mathlib.CategoryTheory.Limits.Shapes.FiniteProducts
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
-- 81 chars (external mathlib path)
import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers
```

- [ ] **Step 2: Build**

Run: `lake build`
Expected: clean build (the new imports are
existing Mathlib modules).

- [ ] **Step 3: Commit**

```bash
git add GebLean/Utilities/ComputableLimits.lean
git commit -m "Import Mathlib equalizer and finite-limits modules"
```

---

### Task 2: ChosenEqualizer gives a Mathlib limit cone

**Files:**

- Modify: `GebLean/Utilities/ComputableLimits.lean`

- [ ] **Step 1: Add `chosenEqualizerIsLimit`**

Append to the `Derivations` section, before the
existing `end Derivations`:

```lean
/-- A `ChosenEqualizer` for `f, g : A ⟶ B` gives
a Mathlib `Limits.IsLimit` for the corresponding
parallel-pair fork. -/
def chosenEqualizerIsLimit
    [HasChosenEqualizers C]
    {A B : C} (f g : A ⟶ B) :
    Limits.IsLimit
      (Limits.Fork.ofι
        (HasChosenEqualizers.equalizer f g).ι
        (HasChosenEqualizers.equalizer f g).ι_eq) :=
  let e := HasChosenEqualizers.equalizer f g
  Limits.Fork.IsLimit.mk _
    (fun s => e.lift s.ι s.condition)
    (fun s => e.lift_ι s.ι s.condition)
    (fun s m hm =>
      e.lift_uniq s.ι s.condition m hm)
```

If the precise form of `Fork.IsLimit.mk` doesn't
match (Mathlib API may use slightly different
argument names), adapt by following the type
signature reported by Lean.

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Commit**

```bash
git add GebLean/Utilities/ComputableLimits.lean
git commit -m "Add chosenEqualizerIsLimit Mathlib bridge"
```

---

### Task 3: HasChosenEqualizers gives HasEqualizers

**Files:**

- Modify: `GebLean/Utilities/ComputableLimits.lean`

- [ ] **Step 1: Add `chosenEqualizerToHasLimit`**

Append after `chosenEqualizerIsLimit`:

```lean
/-- A `ChosenEqualizer` gives `HasLimit` for the
parallel-pair diagram. -/
instance chosenEqualizerToHasLimit
    [HasChosenEqualizers C]
    {A B : C} (f g : A ⟶ B) :
    Limits.HasLimit (Limits.parallelPair f g) :=
  ⟨⟨_, chosenEqualizerIsLimit f g⟩⟩
```

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Add `chosenToHasEqualizers`**

```lean
/-- `HasChosenEqualizers` gives Mathlib's
`HasEqualizers`. -/
instance chosenToHasEqualizers
    [HasChosenEqualizers C] :
    Limits.HasEqualizers C :=
  Limits.hasEqualizers_of_hasLimit_parallelPair C
```

- [ ] **Step 4: Build and commit**

Run: `lake build`

```bash
git add GebLean/Utilities/ComputableLimits.lean
git commit -m "Derive Mathlib HasEqualizers from HasChosenEqualizers"
```

---

### Task 4: HasChosenFiniteLimits gives HasFiniteLimits

**Files:**

- Modify: `GebLean/Utilities/ComputableLimits.lean`

- [ ] **Step 1: Add `chosenToHasFiniteLimits`**

Append after `chosenToHasEqualizers`:

```lean
/-- `HasChosenFiniteLimits` gives Mathlib's
`HasFiniteLimits`.  This combines the existing
finite-products derivation with the new equalizers
derivation via Mathlib's
`hasFiniteLimits_of_hasFiniteProducts_of_hasEqualizers`. -/
instance chosenToHasFiniteLimits
    [HasChosenFiniteLimits C] :
    Limits.HasFiniteLimits C :=
  Limits.hasFiniteLimits_of_hasFiniteProducts_of_hasEqualizers
```

If the lemma name in current Mathlib is different
(common alternatives: `Limits.hasFiniteLimits_of_hasTerminal_and_pullbacks`,
`hasFiniteLimits_iff_hasFiniteProducts_and_hasEqualizers`),
the implementer should search Mathlib for the
appropriate one.  The intent is: "from finite
products and equalizers, derive all finite
limits."

If no such direct lemma exists, derive it manually:
```lean
instance chosenToHasFiniteLimits
    [HasChosenFiniteLimits C] :
    Limits.HasFiniteLimits C := by
  haveI : Limits.HasFiniteProducts C :=
    inferInstance
  haveI : Limits.HasEqualizers C := inferInstance
  exact
    Limits.hasFiniteLimits_of_hasFiniteProducts_of_hasEqualizers
```

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Commit**

```bash
git add GebLean/Utilities/ComputableLimits.lean
git commit -m "Derive Mathlib HasFiniteLimits from HasChosenFiniteLimits"
```

---

### Task 5: Verify on LawvereERLexCat and update tracker

**Files:**

- Modify: `GebLeanTests/LawvereERLex.lean`
- Modify: `.session/workstreams/lawvere-elementary-recursive.md`

- [ ] **Step 1: Add tests asserting Mathlib instances**

Append to `GebLeanTests/LawvereERLex.lean`:

```lean
-- Mathlib's HasEqualizers is now derived
-- automatically.
example : Limits.HasEqualizers LawvereERLexCat :=
  inferInstance

-- Mathlib's HasFiniteLimits is now derived
-- automatically.
example : Limits.HasFiniteLimits LawvereERLexCat :=
  inferInstance
```

- [ ] **Step 2: Build and test**

Run: `lake build && lake test`
Expected: clean build, all tests pass.

- [ ] **Step 3: Commit tests**

```bash
git add GebLeanTests/LawvereERLex.lean
git commit -m "Verify Mathlib HasEqualizers/HasFiniteLimits on LawvereERLexCat"
```

- [ ] **Step 4: Update workstream tracker**

Append to the status section in
`.session/workstreams/lawvere-elementary-recursive.md`:

"Phase 4d.3 complete: see
`GebLean/Utilities/ComputableLimits.lean` extended
with `chosenEqualizerIsLimit`,
`chosenEqualizerToHasLimit`,
`chosenToHasEqualizers`, and
`chosenToHasFiniteLimits`.  These derive Mathlib's
`Limits.HasEqualizers` and `Limits.HasFiniteLimits`
from our `Type`-valued chosen versions, validating
that the chosen-finite-limit definitions correctly
present the standard categorical notions."

Update the task checkbox:

```
  * [x] 4d.2: ERBoolPredE quotient + chosen
    equalizers + HasChosenFiniteLimits.
```

To:

```
  * [x] 4d.2: ERBoolPredE quotient + chosen
    equalizers + HasChosenFiniteLimits.
  * [x] 4d.3: Mathlib HasEqualizers and
    HasFiniteLimits derivations.
```

- [ ] **Step 5: Commit tracker update**

```bash
git add \
  .session/workstreams/lawvere-elementary-recursive.md
git commit -m "Mark ER Phase 4d.3 complete in workstream tracker"
```
