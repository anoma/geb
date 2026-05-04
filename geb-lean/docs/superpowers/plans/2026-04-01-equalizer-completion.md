# Equalizer Completion Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Implement the free equalizer completion of a
category with finite products (the Pitts/Bunge construction),
prove it yields finite limits, apply it to `LawvereBTQuotCat`,
and extend the interpretation functor.

**Architecture:** Objects are coreflexive pairs in the base
category. Morphisms are equivalence classes (via `EqvGen`) of
premorphisms. Finite products lift pointwise from the base
category; equalizers arise from the coreflexive structure
using binary products. The construction is generic over any
category with `HasChosenFiniteProducts`, then instantiated for
`LawvereBTQuotCat`.

**Tech Stack:** Lean 4, mathlib (`EqvGen`,
`CategoryTheory.Limits`, `IsCoreflexivePair`,
`hasFiniteLimits_of_hasEqualizers_and_finite_products`),
project utilities (`HasChosenFiniteProducts`,
`ChosenBinaryProduct`).

---

## File Structure

- `GebLean/EqualizerCompletion.lean` -- Coreflexive pair
  objects, premorphism relation, `EqvGen` equivalence,
  category instance, embedding functor
- `GebLean/EqualizerCompletionLimits.lean` -- Pointwise
  finite products, equalizer construction,
  `HasFiniteLimits` theorem
- `GebLean/LawvereBTEqCompletion.lean` -- Application to
  `LawvereBTQuotCat`: PBTO preservation, interpretation
  functor extension
- `test/TestEqualizerCompletion.lean` -- `#guard` tests

All files import `GebLean.Utilities.ComputableLimits` for
`HasChosenFiniteProducts`. The first two files are generic
(parameterized by `C`). The third specializes to
`LawvereBTQuotCat`.

---

## Mathematical Summary

### Objects

A coreflexive pair in C consists of `(X₀, X₁, ∂₀, ∂₁, ρ)`
where `∂₀ ∂₁ : X₀ ⟶ X₁` and `ρ : X₁ ⟶ X₀` with
`∂₀ ≫ ρ = 𝟙 X₀` and `∂₁ ≫ ρ = 𝟙 X₀`.

### Equivalence relation

For a coreflexive pair X and object V, define a relation
`CoreflexiveRelStep X` on `C(X₀, V)`:
`f₀ ~₁ f₁` iff `∃ h : X₁ ⟶ V, ∂₀ ≫ h = f₀ ∧ ∂₁ ≫ h = f₁`.

This is reflexive (witnessed by `ρ ≫ f`). The morphism
equivalence is `EqvGen (CoreflexiveRelStep X)`.

### Premorphisms

`f : X₀ ⟶ Y₀` is a premorphism `X → Y` if
`f ≫ ∂₀' ~_{EqvGen} f ≫ ∂₁'` in `C(X₀, Y₁)` using X's
coreflexive structure.

### Morphisms

Equivalence classes of premorphisms under
`EqvGen (CoreflexiveRelStep X)` on `C(X₀, Y₀)`.

### Equalizer construction

Given `[f], [g] : X → Y` in the completion, the equalizer
is:

- `E₀ = X₀`
- `E₁ = X₁ × Y₁` (product in C)
- `∂₀ᴱ = ⟨∂₀ˣ, f ≫ ∂₀ʸ⟩ : X₀ ⟶ X₁ × Y₁`
- `∂₁ᴱ = ⟨∂₁ˣ, g ≫ ∂₀ʸ⟩ : X₀ ⟶ X₁ × Y₁`
- `ρᴱ = π₁ ≫ ρˣ : X₁ × Y₁ ⟶ X₀`
- Inclusion: `[id_{X₀}] : E → X`

The equalizing condition `[f ∘ e] = [g ∘ e]` is witnessed by
`π₂ ≫ ρ' : E₁ → Y₀`.

---

## Task 1: Coreflexive Pair Object Structure

**Files:**

- Create: `GebLean/EqualizerCompletion.lean`

- [ ] **Step 1: Module header and imports**

```lean
import GebLean.Utilities.ComputableLimits
import Mathlib.Logic.Relation

namespace GebLean

open CategoryTheory

universe v u
```

- [ ] **Step 2: Define `CoreflexivePairObj`**

```lean
@[ext]
structure CoreflexivePairObj
    (C : Type u) [Category.{v} C] where
  src : C
  tgt : C
  left : src ⟶ tgt
  right : src ⟶ tgt
  retract : tgt ⟶ src
  retract_left : left ≫ retract = 𝟙 src
  retract_right : right ≫ retract = 𝟙 src
```

Field naming: `src` = X₀ (the object being quotiented),
`tgt` = X₁ (the witness space), `left`/`right` = ∂₀/∂₁,
`retract` = ρ.

- [ ] **Step 3: Accessor definitions**

Define `cpSrc`, `cpTgt`, `cpLeft`, `cpRight`, `cpRetract`
accessors with `@[simp]`.

- [ ] **Step 4: Build and verify**

Run: `lake build GebLean.EqualizerCompletion`
Expected: compiles with no warnings.

- [ ] **Step 5: Commit**

```bash
git add GebLean/EqualizerCompletion.lean GebLean.lean
git commit -m "feat: CoreflexivePairObj structure"
```

---

## Task 2: Equivalence Relation and Premorphisms

**Files:**

- Modify: `GebLean/EqualizerCompletion.lean`

- [ ] **Step 1: Define the one-step relation**

```lean
variable {C : Type u} [Category.{v} C]

def CoreflexiveRelStep
    (X : CoreflexivePairObj C) {V : C}
    (f₀ f₁ : X.src ⟶ V) : Prop :=
  ∃ h : X.tgt ⟶ V,
    X.left ≫ h = f₀ ∧ X.right ≫ h = f₁
```

- [ ] **Step 2: Prove reflexivity of the one-step relation**

```lean
theorem CoreflexiveRelStep.rfl
    (X : CoreflexivePairObj C) {V : C}
    (f : X.src ⟶ V) :
    CoreflexiveRelStep X f f :=
  ⟨X.retract ≫ f, by
    rw [Category.assoc, X.retract_left,
      Category.id_comp],
   by rw [Category.assoc, X.retract_right,
      Category.id_comp]⟩
```

Wait -- the coreflexivity conditions are `left ≫ retract =
𝟙` and `right ≫ retract = 𝟙`, so the witness for
reflexivity is `retract ≫ f`:
`left ≫ (retract ≫ f) = (left ≫ retract) ≫ f = 𝟙 ≫ f = f`.

- [ ] **Step 3: Define the generated equivalence**

```lean
def CoreflexiveEqv
    (X : CoreflexivePairObj C) {V : C}
    (f₀ f₁ : X.src ⟶ V) : Prop :=
  EqvGen (CoreflexiveRelStep X) f₀ f₁
```

- [ ] **Step 4: Define premorphism predicate**

```lean
def IsCPPremorphism
    (X Y : CoreflexivePairObj C)
    (f : X.src ⟶ Y.src) : Prop :=
  CoreflexiveEqv X
    (f ≫ Y.left) (f ≫ Y.right)
```

- [ ] **Step 5: Prove identity is a premorphism**

The identity `𝟙 X.src` is a premorphism X → X. Witness:
`id_{X.tgt}` satisfies `left ≫ id = left` and
`right ≫ id = right`, giving a one-step relation
`left ~₁ right`. Thus `id ≫ left = left ~₁ right = id ≫
right`. Use `EqvGen.rel`.

- [ ] **Step 6: Prove composition preserves premorphisms**

Given premorphisms f : X → Y and g : Y → Z, show g ∘ f is
a premorphism X → Z. The proof lifts the Y-witness through
g using `EqvGen.rec` (induction on the zigzag).

- [ ] **Step 7: Prove equivalence respects composition**

If f₁ ~ f₂ in `CoreflexiveEqv X` on `C(X.src, Y.src)` and
g is a premorphism Y → Z, then `g ∘ f₁ ~ g ∘ f₂`. Similarly
for pre-composition. Proof: by induction on `EqvGen`, using
the one-step witness composed with g.

- [ ] **Step 8: Build and verify**

Run: `lake build GebLean.EqualizerCompletion`
Expected: compiles with no warnings.

- [ ] **Step 9: Commit**

```bash
git add GebLean/EqualizerCompletion.lean
git commit -m "feat: coreflexive equivalence relation and premorphisms"
```

---

## Task 3: Quotient Category Instance

**Files:**

- Modify: `GebLean/EqualizerCompletion.lean`

- [ ] **Step 1: Define the morphism setoid**

```lean
def cpMorSetoid
    (X Y : CoreflexivePairObj C) :
    Setoid (X.src ⟶ Y.src) where
  r := CoreflexiveEqv X
  iseqv := EqvGen.setoid.iseqv
```

Filter to premorphisms: the setoid is on the full hom-set,
but morphisms in P\_eq are equivalence classes of
premorphisms. Define:

```lean
def CPMor (X Y : CoreflexivePairObj C) :=
  Quotient (cpMorSetoid X Y)
```

Note: every equivalence class contains a premorphism (since
the relation is reflexive, every element is related to
itself, so every morphism is trivially a premorphism iff it
satisfies the premorphism condition). The premorphism
condition restricts which raw morphisms can represent a
class; within a class, all representatives satisfy it (if one
does). We define `CPMor` as the quotient of all
`X.src ⟶ Y.src` by the equivalence, then restrict to those
classes containing premorphisms. However, the simpler
approach (used in the paper) is to quotient only the
premorphisms. For formalization, quotienting all morphisms
and relying on the premorphism condition for well-definedness
of the category operations is cleaner.

Actually, on reflection, the paper quotes ALL of
`P(X₀, Y₀)`, not just premorphisms. The premorphism
condition is only used to verify that the resulting category
is well-behaved. Let me re-read...

Re-reading the paper: "a morphism X → Y is a
~-equivalence class of such premorphisms." So we DO restrict
to premorphisms first, then quotient. This is the standard
approach.

Define the subtype of premorphisms, then quotient:

```lean
def CPPreMor (X Y : CoreflexivePairObj C) :=
  { f : X.src ⟶ Y.src // IsCPPremorphism X Y f }

def cpPreMorSetoid
    (X Y : CoreflexivePairObj C) :
    Setoid (CPPreMor X Y) where
  r f g := CoreflexiveEqv X f.val g.val
  iseqv := {
    refl := fun f => EqvGen.refl f.val
    symm := fun h => EqvGen.symm _ _ h
    trans := fun h₁ h₂ =>
      EqvGen.trans _ _ _ h₁ h₂
  }

def CPMor (X Y : CoreflexivePairObj C) :=
  Quotient (cpPreMorSetoid X Y)
```

- [ ] **Step 2: Define identity**

```lean
def cpId (X : CoreflexivePairObj C) :
    CPMor X X :=
  Quotient.mk _
    ⟨𝟙 X.src, cpId_isPremorphism X⟩
```

where `cpId_isPremorphism` was proved in Task 2 Step 5.

- [ ] **Step 3: Define composition**

```lean
def cpComp {X Y Z : CoreflexivePairObj C}
    (f : CPMor X Y) (g : CPMor Y Z) :
    CPMor X Z :=
  Quotient.lift₂
    (fun f' g' => Quotient.mk _
      ⟨f'.val ≫ g'.val,
       cpComp_isPremorphism f'.property
         g'.property⟩)
    (fun f₁ g₁ f₂ g₂ hf hg => ...)
    f g
```

Well-definedness uses the composition-respects-equivalence
lemmas from Task 2 Steps 6--7.

- [ ] **Step 4: Prove category laws**

Prove `cpId_comp`, `cpComp_id`, `cpComp_assoc` by
`Quotient.ind` reducing to the underlying category laws in
C. Pattern follows `BTMorNQuo.id_comp` etc. in
`LawvereBTQuot.lean`.

- [ ] **Step 5: Define category instance**

```lean
instance cpCategory :
    Category (CoreflexivePairObj C) where
  Hom := CPMor
  id := cpId
  comp := cpComp
  id_comp := cpId_comp
  comp_id := cpComp_id
  assoc := cpComp_assoc
```

- [ ] **Step 6: Build and verify**

Run: `lake build GebLean.EqualizerCompletion`
Expected: compiles with no warnings.

- [ ] **Step 7: Commit**

```bash
git add GebLean/EqualizerCompletion.lean
git commit -m "feat: category instance for equalizer completion"
```

---

## Task 4: Embedding Functor

**Files:**

- Modify: `GebLean/EqualizerCompletion.lean`

- [ ] **Step 1: Define the trivial coreflexive pair**

```lean
def cpEmbed (c : C) : CoreflexivePairObj C where
  src := c
  tgt := c
  left := 𝟙 c
  right := 𝟙 c
  retract := 𝟙 c
  retract_left := Category.id_comp _
  retract_right := Category.id_comp _
```

- [ ] **Step 2: Prove embedding preserves morphisms**

For the trivial pair, the one-step relation `f₀ ~₁ f₁`
means `∃ h, 𝟙 ≫ h = f₀ ∧ 𝟙 ≫ h = f₁`, which simplifies
to `f₀ = f₁`. So the equivalence is equality, and every
morphism is a premorphism (since `f ≫ 𝟙 = f ≫ 𝟙` trivially).

```lean
theorem cpEmbed_eqv_iff {c d : C}
    (f g : c ⟶ d) :
    CoreflexiveEqv (cpEmbed c) f g ↔ f = g
```

- [ ] **Step 3: Define the embedding functor**

```lean
def cpEmbedding : C ⥤ CoreflexivePairObj C where
  obj := cpEmbed
  map f := Quotient.mk _ ⟨f, ...⟩
  map_id := ...
  map_comp := ...
```

- [ ] **Step 4: Prove full and faithful**

Faithfulness: if `cpEmbedding.map f = cpEmbedding.map g`,
then `f ~ g` in the trivial equivalence, so `f = g` by
`cpEmbed_eqv_iff`.

Fullness: every premorphism `c → d` for trivial pairs is
just a morphism `c ⟶ d`, and its equivalence class is a
singleton.

- [ ] **Step 5: Build and verify**

Run: `lake build GebLean.EqualizerCompletion`
Expected: compiles with no warnings.

- [ ] **Step 6: Commit**

```bash
git add GebLean/EqualizerCompletion.lean
git commit -m "feat: full and faithful embedding into equalizer completion"
```

---

## Task 5: Pointwise Finite Products

**Files:**

- Create: `GebLean/EqualizerCompletionLimits.lean`

- [ ] **Step 1: Module header**

```lean
import GebLean.EqualizerCompletion
import Mathlib.CategoryTheory.Limits.Constructions.LimitsOfProductsAndEqualizers

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]
```

- [ ] **Step 2: Define terminal coreflexive pair**

```lean
def cpTerminal : CoreflexivePairObj C where
  src := cfpTerminal
  tgt := cfpTerminal
  left := 𝟙 cfpTerminal
  right := 𝟙 cfpTerminal
  retract := 𝟙 cfpTerminal
  retract_left := Category.id_comp _
  retract_right := Category.id_comp _
```

This is just `cpEmbed cfpTerminal`.

- [ ] **Step 3: Prove terminality**

Any morphism `X.src ⟶ cfpTerminal` is unique (by
`cfpTerminalFrom` uniqueness). So there is exactly one
premorphism X → cpTerminal, and exactly one equivalence
class.

```lean
def cpTerminalFrom
    (X : CoreflexivePairObj C) :
    CPMor X cpTerminal := ...

theorem cpTerminal_uniq
    (X : CoreflexivePairObj C)
    (f : CPMor X cpTerminal) :
    f = cpTerminalFrom X := ...
```

- [ ] **Step 4: Define product of coreflexive pairs**

```lean
def cpProd
    (X Y : CoreflexivePairObj C) :
    CoreflexivePairObj C where
  src := cfpProd X.src Y.src
  tgt := cfpProd X.tgt Y.tgt
  left := cfpMap X.left Y.left
  right := cfpMap X.right Y.right
  retract := cfpMap X.retract Y.retract
  retract_left := by
    -- cfpMap left retract_left ≫
    -- cfpMap retract retract =
    -- cfpMap (left ≫ retract) (...)
    -- = cfpMap 𝟙 𝟙 = 𝟙
    ...
  retract_right := by ...
```

The coreflexivity proof uses `cfpMap_comp` (that `cfpMap`
preserves composition) and `cfpMap_id` (that `cfpMap 𝟙 𝟙 =
𝟙`). These lemmas may need to be added to
`ComputableLimits.lean` if not already present.

- [ ] **Step 5: Define projections and pairing**

```lean
def cpFst (X Y : CoreflexivePairObj C) :
    CPMor (cpProd X Y) X :=
  Quotient.mk _ ⟨cfpFst X.src Y.src, ...⟩

def cpSnd (X Y : CoreflexivePairObj C) :
    CPMor (cpProd X Y) Y :=
  Quotient.mk _ ⟨cfpSnd X.src Y.src, ...⟩

def cpLift {Z X Y : CoreflexivePairObj C}
    (f : CPMor Z X) (g : CPMor Z Y) :
    CPMor Z (cpProd X Y) := ...
```

The pairing `cpLift` is defined by `Quotient.lift₂` using
`cfpLift` on the underlying morphisms.

- [ ] **Step 6: Prove product laws**

```lean
theorem cpLift_fst ...
theorem cpLift_snd ...
theorem cpLift_uniq ...
```

Each reduces via `Quotient.ind` to the corresponding law in
C (from `ChosenBinaryProduct`).

- [ ] **Step 7: Assemble `HasChosenFiniteProducts`**

```lean
instance cpHasChosenFiniteProducts :
    HasChosenFiniteProducts
      (CoreflexivePairObj C) where
  terminal := {
    obj := cpTerminal
    from_ := cpTerminalFrom
    uniq := cpTerminal_uniq
  }
  product X Y := {
    obj := cpProd X Y
    fst := cpFst X Y
    snd := cpSnd X Y
    lift := cpLift
    lift_fst := cpLift_fst
    lift_snd := cpLift_snd
    lift_uniq := cpLift_uniq
  }
```

- [ ] **Step 8: Build and verify**

Run: `lake build GebLean.EqualizerCompletionLimits`
Expected: compiles with no warnings.

- [ ] **Step 9: Commit**

```bash
git add GebLean/EqualizerCompletionLimits.lean GebLean.lean
git commit -m "feat: finite products in equalizer completion"
```

---

## Task 6: Equalizer Construction

**Files:**

- Modify: `GebLean/EqualizerCompletionLimits.lean`

- [ ] **Step 1: Define the equalizer coreflexive pair**

Given premorphism representatives `f g : X.src ⟶ Y.src` for
two parallel morphisms `[f], [g] : X ⟶ Y`:

```lean
def cpEqualizerObj
    (X Y : CoreflexivePairObj C)
    (f g : X.src ⟶ Y.src) :
    CoreflexivePairObj C where
  src := X.src
  tgt := cfpProd X.tgt Y.tgt
  left := cfpLift X.left (f ≫ Y.left)
  right := cfpLift X.right (g ≫ Y.left)
  retract :=
    cfpFst X.tgt Y.tgt ≫ X.retract
  retract_left := by
    rw [Category.assoc]
    -- cfpLift X.left (f ≫ Y.left) ≫
    --   cfpFst ≫ X.retract
    -- = X.left ≫ X.retract = 𝟙
    ...
  retract_right := by ...
```

Note: `left` uses `Y.left` (= ∂₀ʸ) on both the f and g
sides. The asymmetry between f and g in `left` vs `right` is
what creates the equalizing condition.

- [ ] **Step 2: Define the inclusion morphism**

The inclusion `e : cpEqualizerObj X Y f g ⟶ X` is `[𝟙
X.src]`:

```lean
def cpEqualizerι
    (X Y : CoreflexivePairObj C)
    (f g : X.src ⟶ Y.src) :
    CPMor (cpEqualizerObj X Y f g) X :=
  Quotient.mk _ ⟨𝟙 X.src, ...⟩
```

The premorphism condition: `𝟙 ≫ X.left ~_{EqvGen} 𝟙 ≫
X.right` in `C(X.src, X.tgt)` using the equalizer's
coreflexive structure. Witness:
`cfpFst X.tgt Y.tgt : cfpProd X.tgt Y.tgt ⟶ X.tgt`
satisfies `left ≫ cfpFst = X.left` and
`right ≫ cfpFst = X.right` by `cfpLift_fst`.

- [ ] **Step 3: Prove the equalizing condition**

Show `cpComp (cpEqualizerι ...) [f] =
cpComp (cpEqualizerι ...) [g]`, i.e., `f ~ g` in the
equalizer's equivalence on `C(X.src, Y.src)`.

Witness: `cfpSnd X.tgt Y.tgt ≫ Y.retract` satisfies:

- `left ≫ (cfpSnd ≫ Y.retract)` reduces to
  `f ≫ Y.left ≫ Y.retract = f ≫ 𝟙 = f`
- `right ≫ (cfpSnd ≫ Y.retract)` reduces to
  `g ≫ Y.left ≫ Y.retract = g ≫ 𝟙 = g`

So `f ~₁ g` in one step, giving `EqvGen.rel`.

- [ ] **Step 4: Prove universal property (factorization)**

Given `[t] : Z ⟶ X` with `[f] ∘ [t] = [g] ∘ [t]`, the
factorization `[t] : Z ⟶ cpEqualizerObj X Y f g` uses
the same underlying morphism `t : Z.src ⟶ X.src`.

The premorphism condition for `t : Z → E` requires
`t ≫ E.left ~_{EqvGen} t ≫ E.right` in
`C(Z.src, cfpProd X.tgt Y.tgt)`.

By `cfpLift`:

- `t ≫ E.left = cfpLift (t ≫ X.left) (t ≫ f ≫ Y.left)`
- `t ≫ E.right = cfpLift (t ≫ X.right) (t ≫ g ≫ Y.left)`

These are related via the product structure: compose each
component separately. The X.tgt-component uses t's
premorphism condition (`t ≫ X.left ~ t ≫ X.right`); the
Y.tgt-component uses the equalizing condition
(`f ∘ t ~ g ∘ t`), lifted through `Y.left`.

The proof proceeds by induction on `EqvGen` for the two
components, combining the zigzags using the reflexivity of
the other component (to keep it constant while the first
changes). Each step lifts through `cfpLift` to produce a
one-step witness in the product.

- [ ] **Step 5: Prove universal property (uniqueness)**

Any factorization `[k] : Z → E` with `[e] ∘ [k] = [t]`
satisfies `[k] = [t]` as morphisms Z → E, because `e = 𝟙`
and the morphism equivalence for Z → E is the same as for
Z → X (both quotient `C(Z.src, X.src)` by `CoreflexiveEqv
Z`).

- [ ] **Step 6: Assemble the fork and `IsLimit`**

Using mathlib's `Fork` and `Fork.IsLimit`:

```lean
def cpFork
    (X Y : CoreflexivePairObj C)
    (f g : X.src ⟶ Y.src)
    (hf : IsCPPremorphism X Y f)
    (hg : IsCPPremorphism X Y g) :
    Fork
      (Quotient.mk _ ⟨f, hf⟩ : CPMor X Y)
      (Quotient.mk _ ⟨g, hg⟩) :=
  Fork.ofι (cpEqualizerι X Y f g)
    (cpEqualizer_condition X Y f g)

def cpFork_isLimit ... :
    IsLimit (cpFork X Y f g hf hg) := ...
```

- [ ] **Step 7: Derive `HasEqualizers`**

```lean
instance cpHasEqualizers :
    Limits.HasEqualizers
      (CoreflexivePairObj C) := ...
```

Construct via `HasEqualizer` for each parallel pair,
using `cpFork_isLimit`.

- [ ] **Step 8: Derive `HasFiniteLimits`**

```lean
instance cpHasFiniteLimits :
    Limits.HasFiniteLimits
      (CoreflexivePairObj C) :=
  hasFiniteLimits_of_hasEqualizers_and_finite_products
```

This uses mathlib's theorem
`hasFiniteLimits_of_hasEqualizers_and_finite_products` which
requires `HasFiniteProducts` (derived from
`HasChosenFiniteProducts` via our existing instances in
`ComputableLimits.lean`) and `HasEqualizers`.

- [ ] **Step 9: Build and verify**

Run: `lake build GebLean.EqualizerCompletionLimits`
Expected: compiles with no warnings.

- [ ] **Step 10: Commit**

```bash
git add GebLean/EqualizerCompletionLimits.lean
git commit -m "feat: equalizers and finite limits in the completion"
```

---

## Task 7: Application to LawvereBTQuotCat

**Files:**

- Create: `GebLean/LawvereBTEqCompletion.lean`

- [ ] **Step 1: Module header and type alias**

```lean
import GebLean.EqualizerCompletionLimits
import GebLean.LawvereBTQuot

namespace GebLean

open CategoryTheory

def LawvereBTLexCat :=
  CoreflexivePairObj LawvereBTQuotCat
```

- [ ] **Step 2: Verify finite limits**

Since `LawvereBTQuotCat` has `HasChosenFiniteProducts`
(proved in `LawvereBTQuot.lean`), the generic instances
automatically give:

```lean
-- These should be inferred automatically:
example : Category LawvereBTLexCat := inferInstance
example : Limits.HasFiniteLimits LawvereBTLexCat :=
  inferInstance
```

Add `#check` or `example` statements to verify.

- [ ] **Step 3: Build and verify**

Run: `lake build GebLean.LawvereBTEqCompletion`
Expected: compiles with no warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereBTEqCompletion.lean GebLean.lean
git commit -m "feat: LawvereBTLexCat with finite limits"
```

---

## Task 8: PBTO Preservation

**Files:**

- Modify: `GebLean/LawvereBTEqCompletion.lean`

- [ ] **Step 1: Embed PBTO structure**

The PBTO in `LawvereBTQuotCat` has `T = 1`, `ℓ = btLeafQ`,
`β = btBranchQ`. Under the embedding `cpEmbedding`:

```lean
def lexT : LawvereBTLexCat :=
  cpEmbed (1 : LawvereBTQuotCat)

def lexLeaf : cpTerminal ⟶ lexT :=
  cpEmbedding.map btLeafQ

def lexBranch :
    cpProd lexT lexT ⟶ lexT :=
  cpEmbedding.map btBranchQ
```

Wait -- `cpProd lexT lexT` uses the completion's product,
which is `cpProd (cpEmbed 1) (cpEmbed 1)`. Its `src` is
`cfpProd 1 1 = 2` in `LawvereBTQuotCat`. We need this to
match `cpEmbed 2`. Show `cpProd (cpEmbed 1) (cpEmbed 1) =
cpEmbed 2` or define an isomorphism.

The product of two trivially-embedded objects is the
trivially-embedded product:
`cpProd (cpEmbed A) (cpEmbed B) = cpEmbed (cfpProd A B)`.
This holds definitionally when `cfpMap 𝟙 𝟙 = 𝟙` (which
requires a proof). Define this isomorphism explicitly.

- [ ] **Step 2: Define `elim` in the completion**

For objects A and X in the completion (not just embedded
ones) with `f : A ⟶ X` and `g : cpProd X X ⟶ X`, we need
`φ : cpProd A lexT ⟶ X`.

The construction: use `elimQ` from `LawvereBTQuot.lean` on
the `src`-components, then verify the premorphism condition.

This is the most involved part: the universal property must
hold for arbitrary coreflexive pairs A and X, not just
trivially-embedded ones.

Strategy: define `φ` using `elimQ` on `A.src` and `X.src`,
then verify the premorphism and computation conditions hold
modulo the coreflexive equivalence relation.

- [ ] **Step 3: Prove computation rules**

`elim_ℓ` and `elim_β` lift from the corresponding rules in
`LawvereBTQuotCat` (proved in `LawvereBTQuot.lean`) through
the quotient.

- [ ] **Step 4: Prove uniqueness**

`elim_uniq` lifts from uniqueness in `LawvereBTQuotCat`.
The key argument: if `[φ]` satisfies the computation rules
in the completion, then on the `src`-components, φ satisfies
them in `LawvereBTQuotCat` (modulo the coreflexive
equivalence, which for embedded objects is equality). By
uniqueness in `LawvereBTQuotCat`, all such φ are equal on
`src`-components, hence equivalent in the completion.

- [ ] **Step 5: Assemble `HasPBTO` instance**

```lean
instance : HasPBTO LawvereBTLexCat where
  T := lexT
  ℓ := lexLeaf
  β := lexBranch
  elim f g := ...
  elim_ℓ := ...
  elim_β := ...
  elim_uniq := ...
```

- [ ] **Step 6: Build and verify**

Run: `lake build GebLean.LawvereBTEqCompletion`
Expected: compiles with no warnings.

- [ ] **Step 7: Commit**

```bash
git add GebLean/LawvereBTEqCompletion.lean
git commit -m "feat: PBTO preserved in equalizer completion"
```

---

## Task 9: Interpretation Functor Extension

**Files:**

- Modify: `GebLean/LawvereBTEqCompletion.lean`

- [ ] **Step 1: Define the interpretation on objects**

For a coreflexive pair `X = (n₀, n₁, ∂₀, ∂₁, ρ)` in
`LawvereBTQuotCat`, the interpretation is the equalizer in
`Type u`:

```lean
def lexInterpObj
    (X : LawvereBTLexCat) : Type u :=
  { ctx : interpFunctor.obj X.src //
    interpFunctor.map X.left ctx =
    interpFunctor.map X.right ctx }
```

This is `{ ctx : Fin n₀ → BT |
interpFunctor.map ∂₀ ctx = interpFunctor.map ∂₁ ctx }`.

- [ ] **Step 2: Define the interpretation on morphisms**

For a premorphism `f : X.src ⟶ Y.src`, the interpretation
maps `(ctx, proof) : lexInterpObj X` to
`(interpFunctor.map f ctx, ...)`. The proof obligation
is that `interpFunctor.map Y.left (interpFunctor.map f ctx)
= interpFunctor.map Y.right (interpFunctor.map f ctx)`.

From the premorphism condition and `interpFunctor`'s
faithfulness, this follows.

Show this is well-defined on equivalence classes: if
`f ~ g` in `CoreflexiveEqv X`, then
`interpFunctor.map f ctx = interpFunctor.map g ctx` for all
`ctx` in the equalizer subtype. Proof: by induction on
`EqvGen`, using the coreflexive witness.

```lean
def lexInterpMap
    {X Y : LawvereBTLexCat}
    (f : CPMor X Y) :
    lexInterpObj X → lexInterpObj Y := ...
```

- [ ] **Step 3: Prove functoriality**

```lean
theorem lexInterpMap_id ...
theorem lexInterpMap_comp ...
```

- [ ] **Step 4: Assemble the functor**

```lean
def lexInterpFunctor :
    LawvereBTLexCat ⥤ Type u where
  obj := lexInterpObj
  map := lexInterpMap
  map_id := lexInterpMap_id
  map_comp := lexInterpMap_comp
```

- [ ] **Step 5: Prove compatibility with embedding**

Show that `lexInterpFunctor` extends `interpFunctor` along
`cpEmbedding`:

```lean
theorem lexInterp_extends :
    cpEmbedding ⋙ lexInterpFunctor ≅
      interpFunctor := ...
```

For trivially-embedded objects, the equalizer subtype is
`{ ctx | ctx = ctx }` which is isomorphic to the original
type.

- [ ] **Step 6: Prove faithfulness**

`lexInterpFunctor` is faithful because `interpFunctor` is
faithful and the embedding is full and faithful.

```lean
instance : lexInterpFunctor.Faithful := ...
```

- [ ] **Step 7: Build and verify**

Run: `lake build GebLean.LawvereBTEqCompletion`
Expected: compiles with no warnings.

- [ ] **Step 8: Commit**

```bash
git add GebLean/LawvereBTEqCompletion.lean
git commit -m "feat: interpretation functor for equalizer completion"
```

---

## Task 10: Tests

**Files:**

- Create: `test/TestEqualizerCompletion.lean`

- [ ] **Step 1: Test that trivial coreflexive pairs work**

```lean
import GebLean.LawvereBTEqCompletion

open GebLean CategoryTheory

-- Trivially-embedded object
#guard (cpEmbed (1 : LawvereBTQuotCat)).src = 1
#guard (cpEmbed (1 : LawvereBTQuotCat)).tgt = 1
```

- [ ] **Step 2: Test product structure**

```lean
#guard (cpProd
  (cpEmbed (2 : LawvereBTQuotCat))
  (cpEmbed (3 : LawvereBTQuotCat))).src = 5
```

- [ ] **Step 3: Test equalizer object**

Construct a non-trivial coreflexive pair and verify the
equalizer object has the expected `src` and `tgt` fields.

- [ ] **Step 4: Test interpretation functor**

```lean
-- Interpretation of trivially-embedded 1 is
-- (Fin 1 → BT)
example : lexInterpObj (cpEmbed
  (1 : LawvereBTQuotCat)) =
  { ctx : Fin 1 → BT.{0} // ... } := rfl
```

- [ ] **Step 5: Build and verify**

Run: `lake build` and `lake test`
Expected: all pass with no warnings.

- [ ] **Step 6: Commit**

```bash
git add test/TestEqualizerCompletion.lean
git commit -m "test: equalizer completion tests"
```

---

## Task 11: Register Modules

**Files:**

- Modify: `GebLean.lean`

- [ ] **Step 1: Add imports**

Add the new modules to `GebLean.lean`:

```lean
import GebLean.EqualizerCompletion
import GebLean.EqualizerCompletionLimits
import GebLean.LawvereBTEqCompletion
```

(This should be done incrementally as each module is
completed.)

- [ ] **Step 2: Final build**

Run: `lake build` and `lake test`
Expected: full build passes with no warnings.

- [ ] **Step 3: Commit**

```bash
git add GebLean.lean
git commit -m "feat: register equalizer completion modules"
```

---

## Auxiliary Lemmas Likely Needed

The following lemmas about `HasChosenFiniteProducts` may need
to be added to `GebLean/Utilities/ComputableLimits.lean`:

1. `cfpMap_comp`: `cfpMap (f₁ ≫ f₂) (g₁ ≫ g₂) =
   cfpMap f₁ g₁ ≫ cfpMap f₂ g₂`
2. `cfpMap_id`: `cfpMap (𝟙 A) (𝟙 B) = 𝟙 (cfpProd A B)`
3. `cfpLift_comp`: naturality of `cfpLift` under
   post-composition
4. `cfpFst_naturality`, `cfpSnd_naturality`:
   `cfpMap f g ≫ cfpFst = cfpFst ≫ f` etc.

These follow from the universal property of products and are
used throughout Tasks 5 and 6.

---

## Dependencies

```text
Task 1 → Task 2 → Task 3 → Task 4
                         ↘
Task 5 → Task 6 → Task 7 → Task 8 → Task 9
                                        ↘
                                     Task 10
Task 11 (incremental, after each file is created)
```

Tasks 1--4 (category definition) and Tasks 5--6 (limits) are
sequential. Tasks 7--9 (LawvereBT application) depend on
Tasks 4 and 6. Task 10 (tests) depends on Task 9.

## Risk Assessment

- **Quotient complexity**: The double-quotient structure
  (btMorRel inside CoreflexiveEqv) may create typeclass
  resolution or definitional equality issues. Mitigation:
  define explicit `Quotient.lift` wrappers following the
  pattern in `LawvereBTQuot.lean`.

- **Product lemmas**: The `cfpMap_comp`/`cfpMap_id` lemmas
  are not currently in `ComputableLimits.lean` and will be
  needed. Mitigation: add them in a preliminary commit.

- **Equalizer universal property**: The zigzag lifting
  argument (Task 6 Step 4) requires careful `EqvGen`
  induction with product-component independence. This is
  conceptually clear but may be verbose in Lean.

- **PBTO for non-embedded objects**: Task 8 Step 2 requires
  the PBTO universal property for arbitrary coreflexive
  pairs, not just embedded ones. This may require showing
  that the fold operation commutes with the coreflexive
  equivalence, which is non-trivial.
