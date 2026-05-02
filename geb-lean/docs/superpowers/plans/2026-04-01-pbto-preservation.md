# PBTO Preservation Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Prove that the parameterized binary tree object
(PBTO) universal property of `LawvereBTQuotCat` is preserved
in its equalizer completion `LawvereBTLexCat`, yielding a
`HasPBTO LawvereBTLexCat` instance.

**Architecture:** The proof proceeds in layers: (1) prove
naturality of `elimQ` under parameter pre-composition,
(2) prove an algebra morphism property relating folds
post-composed with coreflexive sections, (3) prove that fold
respects first-argument coreflexive equivalence (Lemma A),
(4) combine these to show `elimQ` yields a premorphism in the
completion, (5) lift computation rules and uniqueness through
the quotient structure.

**Tech Stack:** Lean 4, existing `LawvereBTQuot.lean`
(`elimQ`, `elimQ_ℓ`, `elimQ_β`, `elimQ_uniq`),
`EqualizerCompletion.lean` (`CoreflexiveEqv`,
`IsCPPremorphism`, `cpCategory`),
`EqualizerCompletionLimits.lean` (`cpProd`,
`cpHasChosenFiniteProducts`).

---

## File Structure

- `GebLean/LawvereBTEqCompletion.lean` -- All new
  definitions and proofs go here (modify existing file)

---

## Mathematical Analysis

### The PBTO in `LawvereBTQuotCat`

The PBTO has `T = 1`, `ℓ = btLeafQ : 0 ⟶ 1`,
`β = btBranchQ : 2 ⟶ 1`. The eliminator
`elimQ f g : (n + 1) ⟶ m` satisfies:

- `cfpInsertSnd btLeafQ n ≫ elimQ f g = f`
- `cfpMap (𝟙 n) btBranchQ ≫ elimQ f g =
  cfpLiftAssoc (elimQ f g) (elimQ f g) ≫ g`
- Uniqueness: any `φ` satisfying both equals `elimQ f g`

### The PBTO in the completion

In `LawvereBTLexCat`, `T = cpEmbed 1`. For objects
`A = (n₀, n₁, ∂₀ᴬ, ∂₁ᴬ, ρᴬ)` and
`X = (m₀, m₁, ∂₀ˣ, ∂₁ˣ, ρˣ)` with morphisms
`[f] : A ⟶ X` and `[g] : cpProd X X ⟶ X`, we need
`φ : cpProd A (cpEmbed 1) ⟶ X` in the completion.

The underlying morphism is `elimQ f_rep g_rep : (n₀+1) ⟶ m₀`
for premorphism representatives `f_rep`, `g_rep`.

### Three supporting properties

**Naturality of `elimQ`**: For `h : k ⟶ n` in
`LawvereBTQuotCat`:

```text
cfpMap h (𝟙 1) ≫ elimQ f g = elimQ (h ≫ f) g
```

Proof: both sides satisfy the computation rules for base
`h ≫ f` and step `g`; by `elimQ_uniq`, they are equal.

**Algebra morphism property**: Given a one-step
`CoreflexiveRelStep (cpProd X X) (g ≫ X.left) (g ≫ X.right)`
with witness `w_g : (m₁ + m₁) ⟶ m₁`, both `X.left` and
`X.right` are algebra morphisms from the
`(f, g)`-algebra on `m₀` to the
`(f ≫ X.left, w_g)` resp. `(f ≫ X.right, w_g)`-algebra
on `m₁`:

```text
elimQ (f ≫ X.left) w_g = elimQ f g ≫ X.left
elimQ (f ≫ X.right) w_g = elimQ f g ≫ X.right
```

Proof: `elimQ f g ≫ X.left` satisfies the computation rules
for base `f ≫ X.left` and step `w_g` (the branch equation
uses `cfpMap X.left X.left ≫ w_g = g ≫ X.left`); apply
`elimQ_uniq`.

**Lemma A** (fold respects first-argument equivalence): If
`CoreflexiveRelStep A a b` with witness `w`, then
`CoreflexiveRelStep (cpProd A (cpEmbed 1))
(elimQ a s) (elimQ b s)` with witness `elimQ w s`.

Proof: by naturality,
`cfpMap A.left (𝟙 1) ≫ elimQ w s = elimQ (A.left ≫ w) s
= elimQ a s` and similarly for `A.right`. Extend to `EqvGen`
by induction.

### Premorphism condition: one-step case

When both `f` and `g` have one-step premorphism witnesses
`w_f` and `w_g`, the witness for the premorphism condition
of `elimQ f g` is `elimQ w_f w_g`:

```text
cfpMap A.left (𝟙 1) ≫ elimQ w_f w_g
  = elimQ (A.left ≫ w_f) w_g      (naturality)
  = elimQ (f ≫ X.left) w_g        (w_f witness)
  = elimQ f g ≫ X.left             (algebra morphism)

cfpMap A.right (𝟙 1) ≫ elimQ w_f w_g
  = elimQ (A.right ≫ w_f) w_g
  = elimQ (f ≫ X.right) w_g
  = elimQ f g ≫ X.right
```

### Premorphism condition: general case

For `EqvGen` premorphism conditions, the proof decomposes
into base-change (via Lemma A) and step-change (Lemma B).
Using reflexivity witnesses
`w_refl = cfpMap X.retract X.retract ≫ g ≫ X.left` and
`w_refl' = cfpMap X.retract X.retract ≫ g ≫ X.right`:

```text
elimQ f g ≫ X.left = elimQ (f ≫ X.left) w_refl
  ~  elimQ (f ≫ X.right) w_refl        [Lemma A]
  ~  elimQ (f ≫ X.right) w_refl'       [Lemma B]
  = elimQ f g ≫ X.right
```

**Lemma B** (fold respects step-function change) is the
remaining difficulty. `w_refl` and `w_refl'` differ by
post-composition of `cfpMap X.retract X.retract ≫ g` with
`X.left` vs `X.right`. One approach: structural induction
using the PBTO computation rules (both folds agree at leaf,
and at branch the step-function difference is absorbed by
the g-premorphism condition and an inductive hypothesis).
This approach requires a joint induction -- the fold-level
`CoreflexiveEqv` step at branch depends on the fold-level
`CoreflexiveEqv` at the subtrees.

---

## Task 1: Naturality of elimQ

**Files:**

- Modify: `GebLean/LawvereBTEqCompletion.lean`

- [ ] **Step 1: State and prove naturality**

```lean
theorem elimQ_naturality
    {k n m : ℕ}
    (h : BTMorNQuo k n)
    (f : BTMorNQuo n m)
    (g : BTMorNQuo (m + m) m) :
    cfpMap (C := LawvereBTQuotCat)
      h (𝟙 (1 : ℕ)) ≫ elimQ f g =
    elimQ (h ≫ f) g := by
  -- Both sides satisfy the PBTO computation
  -- rules for base (h ≫ f) and step g.
  -- Apply elimQ_uniq symmetrically.
  symm
  apply elimQ_uniq
  · -- Leaf: cfpInsertSnd btLeafQ k ≫
    --   cfpMap h (𝟙 1) ≫ elimQ f g
    --   = h ≫ f
    -- Use: cfpInsertSnd btLeafQ k ≫ cfpMap h 𝟙
    --   = h ≫ cfpInsertSnd btLeafQ n
    -- Then: ≫ elimQ f g = h ≫ f
    _
  · -- Branch: similar, using cfpMap naturality
    _
```

The leaf case needs the lemma:
`cfpInsertSnd btLeafQ k ≫ cfpMap h (𝟙 1) =
h ≫ cfpInsertSnd btLeafQ n`. This follows from the
product universal property (both sides are `cfpLift` with
the same components). Factor this out as a separate lemma.

The branch case needs:
`cfpMap (𝟙 k) btBranchQ ≫ cfpMap h (𝟙 1) =
cfpMap h (𝟙 1) ≫ cfpMap (𝟙 n) btBranchQ` (naturality
of `cfpMap`). This should follow from `cfpMap_comp`.

Also need: `cfpLiftAssoc` naturality under pre-composition.

- [ ] **Step 2: Factor out auxiliary product lemmas**

Prove any needed lemmas about `cfpInsertSnd` and
`cfpLiftAssoc` naturality under `cfpMap`.

- [ ] **Step 3: Build and verify**

Run: `lake build GebLean.LawvereBTEqCompletion`

- [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereBTEqCompletion.lean
git commit -m "feat: naturality of elimQ"
```

---

## Task 2: Algebra Morphism Property

**Files:**

- Modify: `GebLean/LawvereBTEqCompletion.lean`

- [ ] **Step 1: State the algebra morphism lemma**

```lean
theorem elimQ_algebra_morphism
    {n m : ℕ}
    (X : LawvereBTLexCat)
    (hXsrc : X.src = m)
    (f : BTMorNQuo n m)
    (g : BTMorNQuo (m + m) m)
    (w_g : BTMorNQuo (X.tgt + X.tgt) X.tgt)
    (hw_left :
      cfpMap (C := LawvereBTQuotCat)
        X.left X.left ≫ w_g =
      g ≫ X.left)
    (hw_right :
      cfpMap (C := LawvereBTQuotCat)
        X.right X.right ≫ w_g =
      g ≫ X.right) :
    elimQ f g ≫ X.left =
      elimQ (f ≫ X.left) w_g ∧
    elimQ f g ≫ X.right =
      elimQ (f ≫ X.right) w_g
```

Note: the exact signature may need adjustment depending
on how the universe levels and type coercions work.
The `hXsrc` parameter resolves the potential mismatch
between `X.src` and the natural number `m`.

- [ ] **Step 2: Prove the left algebra morphism**

Show `elimQ f g ≫ X.left = elimQ (f ≫ X.left) w_g` by
applying `elimQ_uniq` to `elimQ f g ≫ X.left`:

Leaf case: `cfpInsertSnd btLeafQ n ≫ (elimQ f g ≫ X.left)
= (cfpInsertSnd btLeafQ n ≫ elimQ f g) ≫ X.left
= f ≫ X.left` ✓

Branch case: `cfpMap (𝟙 n) btBranchQ ≫ (elimQ f g ≫ X.left)
= (cfpLiftAssoc (elimQ f g) (elimQ f g) ≫ g) ≫ X.left
= cfpLiftAssoc (elimQ f g) (elimQ f g) ≫ (g ≫ X.left)
= cfpLiftAssoc (elimQ f g) (elimQ f g) ≫
  (cfpMap X.left X.left ≫ w_g)`

The last step uses `hw_left`. Then rewrite
`cfpLiftAssoc φ φ ≫ cfpMap X.left X.left` as
`cfpLiftAssoc (φ ≫ X.left) (φ ≫ X.left)` using a
product naturality lemma.

- [ ] **Step 3: Prove the right algebra morphism**

Same structure, using `hw_right`.

- [ ] **Step 4: Build and verify**

Run: `lake build GebLean.LawvereBTEqCompletion`

- [ ] **Step 5: Commit**

```bash
git add GebLean/LawvereBTEqCompletion.lean
git commit -m "feat: algebra morphism property for folds"
```

---

## Task 3: Lemma A (Fold Respects Base Equivalence)

**Files:**

- Modify: `GebLean/LawvereBTEqCompletion.lean`

- [ ] **Step 1: One-step version**

```lean
theorem elimQ_base_relStep
    {A : LawvereBTLexCat}
    {m : ℕ}
    {a b : BTMorNQuo A.src m}
    (s : BTMorNQuo (m + m) m)
    (h : CoreflexiveRelStep A a b) :
    CoreflexiveRelStep
      (cpProd A (cpEmbed (1 : LawvereBTQuotCat)))
      (elimQ a s) (elimQ b s)
```

Proof: obtain witness `w` from `h`. The witness for the
conclusion is `elimQ w s`. By `elimQ_naturality`:
`cfpMap A.left (𝟙 1) ≫ elimQ w s = elimQ (A.left ≫ w) s =
elimQ a s`. Similarly for `A.right`.

- [ ] **Step 2: EqvGen version**

```lean
theorem elimQ_base_eqvGen
    {A : LawvereBTLexCat}
    {m : ℕ}
    {a b : BTMorNQuo A.src m}
    (s : BTMorNQuo (m + m) m)
    (h : CoreflexiveEqv A a b) :
    CoreflexiveEqv
      (cpProd A (cpEmbed (1 : LawvereBTQuotCat)))
      (elimQ a s) (elimQ b s)
```

Proof: by induction on `EqvGen`, using
`elimQ_base_relStep` for the `rel` case.

- [ ] **Step 3: Build and verify**

Run: `lake build GebLean.LawvereBTEqCompletion`

- [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereBTEqCompletion.lean
git commit -m "feat: fold respects base equivalence (Lemma A)"
```

---

## Task 4: Premorphism Condition (One-Step Case)

**Files:**

- Modify: `GebLean/LawvereBTEqCompletion.lean`

- [ ] **Step 1: One-step premorphism for elimQ**

When both `f` and `g` have one-step premorphism witnesses:

```lean
theorem elimQ_isPremorphism_oneStep
    (A X : LawvereBTLexCat)
    (f : BTMorNQuo A.src X.src)
    (g : BTMorNQuo (X.src + X.src) X.src)
    (w_f : BTMorNQuo A.tgt X.tgt)
    (hw_f_left :
      A.left ≫ w_f = f ≫ X.left)
    (hw_f_right :
      A.right ≫ w_f = f ≫ X.right)
    (w_g : BTMorNQuo (X.tgt + X.tgt) X.tgt)
    (hw_g_left :
      cfpMap (C := LawvereBTQuotCat)
        X.left X.left ≫ w_g =
      g ≫ X.left)
    (hw_g_right :
      cfpMap (C := LawvereBTQuotCat)
        X.right X.right ≫ w_g =
      g ≫ X.right) :
    CoreflexiveRelStep
      (cpProd A (cpEmbed (1 : LawvereBTQuotCat)))
      (elimQ f g ≫ X.left)
      (elimQ f g ≫ X.right)
```

Proof: the witness is `elimQ w_f w_g`. By naturality +
algebra morphism:
`cfpMap A.left (𝟙 1) ≫ elimQ w_f w_g
= elimQ (A.left ≫ w_f) w_g = elimQ (f ≫ X.left) w_g
= elimQ f g ≫ X.left`. Similarly for `A.right`.

- [ ] **Step 2: Build and verify**

Run: `lake build GebLean.LawvereBTEqCompletion`

- [ ] **Step 3: Commit**

```bash
git add GebLean/LawvereBTEqCompletion.lean
git commit -m "feat: one-step premorphism condition for elimQ"
```

---

## Task 5: General Premorphism Condition

**Files:**

- Modify: `GebLean/LawvereBTEqCompletion.lean`

- [ ] **Step 1: Prove using reflexivity witnesses +
Lemma A**

For `EqvGen` premorphism conditions on `f` and `g`, use
reflexivity witnesses to decompose:

```lean
theorem elimQ_isPremorphism
    (A X : LawvereBTLexCat)
    (f : BTMorNQuo A.src X.src)
    (g : BTMorNQuo (X.src + X.src) X.src)
    (hf : IsCPPremorphism A X f)
    (hg : IsCPPremorphism (cpProd X X) X g) :
    IsCPPremorphism
      (cpProd A (cpEmbed (1 : LawvereBTQuotCat)))
      X (elimQ f g)
```

Proof strategy:

Define `w_refl := cfpMap X.retract X.retract ≫ g ≫ X.left`
and `w_refl' := cfpMap X.retract X.retract ≫ g ≫ X.right`.

Show:
`elimQ f g ≫ X.left = elimQ (f ≫ X.left) w_refl`
(algebra morphism with `w_refl`, using
`cfpMap X.left X.left ≫ w_refl = g ≫ X.left`
by coreflexivity)

`elimQ f g ≫ X.right = elimQ (f ≫ X.right) w_refl'`
(algebra morphism with `w_refl'`, using
`cfpMap X.right X.right ≫ w_refl' = g ≫ X.right`
by coreflexivity)

Then:

```text
elimQ f g ≫ X.left
  = elimQ (f ≫ X.left) w_refl
  ~ elimQ (f ≫ X.right) w_refl     [Lemma A + hf]
  ~ elimQ (f ≫ X.right) w_refl'    [Lemma B]
  = elimQ f g ≫ X.right
```

**Lemma B** (the step-function change) is the remaining
challenge. Two approaches:

**Approach 1**: Structural induction. Define an auxiliary
fold that simultaneously tracks the `w_refl` and `w_refl'`
results, using the g-premorphism condition at branch nodes
to show they stay equivalent. Specifically: define
`CoreflexiveEqv (cpProd A (cpEmbed 1))
(elimQ b w_refl) (elimQ b w_refl')` by induction on the
tree argument via the PBTO computation rules:

- At leaf: both folds give `b`, so reflexivity.
- At branch: the step-function difference
  (`w_refl` vs `w_refl'`) is absorbed by the
  g-premorphism condition, using the inductive hypothesis
  that the recursive calls are already equivalent.

This induction is formalized using `elimQ_uniq`: construct
a morphism that satisfies the computation rules of BOTH
folds (modulo `CoreflexiveEqv`), showing they produce
equivalent results.

**Approach 2**: If structural induction is too involved,
use the interpretation functor semantically. Show that
`elimQ b w_refl` and `elimQ b w_refl'` agree on all
equalizer elements (since `w_refl` and `w_refl'` agree on
equalizer elements where `X.left` and `X.right` agree,
and the fold respects this). Then appeal to a semantic
completeness argument.

- [ ] **Step 2: Implement Lemma B**

This is the step that may require iteration. Begin with
Approach 1. If stuck after substantial effort, document
the difficulty and move to the next task, leaving the
`EqvGen` extension as an open question.

- [ ] **Step 3: Build and verify**

Run: `lake build GebLean.LawvereBTEqCompletion`

- [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereBTEqCompletion.lean
git commit -m "feat: premorphism condition for elimQ"
```

---

## Task 6: Well-Definedness on Equivalence Classes

**Files:**

- Modify: `GebLean/LawvereBTEqCompletion.lean`

- [ ] **Step 1: First argument well-definedness**

If `CoreflexiveEqv A f₁ f₂`, then
`CoreflexiveEqv (cpProd A (cpEmbed 1))
(elimQ f₁ g) (elimQ f₂ g)`.

This is exactly Lemma A (`elimQ_base_eqvGen`).

- [ ] **Step 2: Second argument well-definedness**

If `CoreflexiveEqv (cpProd X X) g₁ g₂`, then
`CoreflexiveEqv (cpProd A (cpEmbed 1))
(elimQ f g₁) (elimQ f g₂)`.

This is Lemma B applied to the step-function change.
If Lemma B is proved in Task 5, this follows. Otherwise
handle as part of the same open question.

- [ ] **Step 3: Combined well-definedness**

Define `elimLC` using `Quotient.lift₂` with the
well-definedness proof:

```lean
def elimLC
    {A X : LawvereBTLexCat}
    (f : A ⟶ X)
    (g : cpProd X X ⟶ X) :
    cpProd A (cpEmbed (1 : LawvereBTQuotCat)) ⟶ X
```

- [ ] **Step 4: Build and verify**

Run: `lake build GebLean.LawvereBTEqCompletion`

- [ ] **Step 5: Commit**

```bash
git add GebLean/LawvereBTEqCompletion.lean
git commit -m "feat: elimLC well-defined on equivalence classes"
```

---

## Task 7: Computation Rules

**Files:**

- Modify: `GebLean/LawvereBTEqCompletion.lean`

- [ ] **Step 1: Leaf computation rule**

```lean
theorem elimLC_ℓ
    {A X : LawvereBTLexCat}
    (f : A ⟶ X) (g : cpProd X X ⟶ X) :
    cfpInsertSnd
      (C := LawvereBTLexCat)
      (cpEmbedding.map btLeafQ) A ≫
      elimLC f g = f
```

Strategy: reduce via `Quotient.ind₂` on `f` and `g`.
At the raw level, the composition is `cfpInsertSnd btLeafQ
A.src ≫ elimQ f_raw g_raw`, which equals `f_raw` by
`elimQ_ℓ`. The result in the quotient follows.

The complication: `cfpInsertSnd` in `LawvereBTLexCat` uses
the completion's product structure (`cpProd`, `cpTerminal`),
which on `src`-components reduces to `cfpInsertSnd` in
`LawvereBTQuotCat`. This reduction step may require
auxiliary lemmas showing that the completion's product
operations on `src`-components match those of the base
category.

- [ ] **Step 2: Branch computation rule**

Similar structure, using `elimQ_β`.

- [ ] **Step 3: Build and verify**

Run: `lake build GebLean.LawvereBTEqCompletion`

- [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereBTEqCompletion.lean
git commit -m "feat: computation rules for elimLC"
```

---

## Task 8: Uniqueness

**Files:**

- Modify: `GebLean/LawvereBTEqCompletion.lean`

- [ ] **Step 1: Prove uniqueness**

```lean
theorem elimLC_uniq
    {A X : LawvereBTLexCat}
    (f : A ⟶ X)
    (g : cpProd X X ⟶ X)
    (φ : cpProd A
      (cpEmbed (1 : LawvereBTQuotCat)) ⟶ X)
    (hℓ : cfpInsertSnd
      (C := LawvereBTLexCat)
      (cpEmbedding.map btLeafQ) A ≫ φ = f)
    (hβ : cfpMap (C := LawvereBTLexCat)
      (𝟙 A)
      (cpEmbedding.map btBranchQ) ≫ φ =
      cfpLiftAssoc
        (C := LawvereBTLexCat) φ φ ≫ g) :
    φ = elimLC f g
```

Strategy: reduce via `Quotient.ind` on all quotient
arguments. At the raw level, extract the computation rules
for `φ_raw` from `hℓ` and `hβ` (modulo the coreflexive
equivalence relation), then apply `elimQ_uniq` to conclude
that `φ_raw` and `elimQ f_raw g_raw` satisfy the same
computation rules, hence are equal in `LawvereBTQuotCat`.
Lift the equality through the completion quotient.

The complication: `hℓ` and `hβ` give equalities of CPMor
(quotient morphisms in the completion), not equalities
of the underlying BTMorNQuo. Extracting raw-level
equations requires `Quotient.exact` and careful unfolding
of the completion's composition.

- [ ] **Step 2: Build and verify**

Run: `lake build GebLean.LawvereBTEqCompletion`

- [ ] **Step 3: Commit**

```bash
git add GebLean/LawvereBTEqCompletion.lean
git commit -m "feat: uniqueness for elimLC"
```

---

## Task 9: HasPBTO Instance

**Files:**

- Modify: `GebLean/LawvereBTEqCompletion.lean`

- [ ] **Step 1: Assemble**

```lean
instance : HasPBTO LawvereBTLexCat where
  T := cpEmbed (1 : LawvereBTQuotCat)
  ℓ := cpEmbedding.map btLeafQ
  β := cpEmbedding.map btBranchQ
  elim f g := elimLC f g
  elim_ℓ f g := elimLC_ℓ f g
  elim_β f g := elimLC_β f g
  elim_uniq f g φ hℓ hβ :=
    elimLC_uniq f g φ hℓ hβ
```

Note: the `β` field has type
`cfpProd (C := LawvereBTLexCat) T T ⟶ T`, which is
`cpProd (cpEmbed 1) (cpEmbed 1) ⟶ cpEmbed 1`. Since
`cpProd (cpEmbed a) (cpEmbed b)` is NOT definitionally
`cpEmbed (cfpProd a b)`, an isomorphism or transport may
be needed. Factor this out as a separate lemma:

```lean
theorem cpProd_cpEmbed_eq
    (a b : LawvereBTQuotCat) :
    cpProd (cpEmbed a) (cpEmbed b) =
      cpEmbed (cfpProd a b)
```

This should hold by `CoreflexivePairObj.ext` + `cfpMap_id`.

- [ ] **Step 2: Build and verify**

Run: `lake build GebLean.LawvereBTEqCompletion`

- [ ] **Step 3: Commit**

```bash
git add GebLean/LawvereBTEqCompletion.lean
git commit -m "feat: HasPBTO LawvereBTLexCat"
```

---

## Dependencies

```text
Task 1 → Task 2, Task 3
Task 2 → Task 4
Task 3 → Task 4, Task 5
Task 4 → Task 5
Task 5 → Task 6
Task 6 → Task 7, Task 8
Task 7 → Task 9
Task 8 → Task 9
```

## Risk Assessment

- **Lemma B (Task 5)**: The step-function change argument
  is the primary risk. If the categorical approach via
  structural induction proves intractable, alternative
  approaches include: (a) proving semantic completeness of
  the coreflexive equivalence, (b) restricting the PBTO to
  the embedded subcategory (weaker result), or (c) using a
  different formulation of the PBTO that avoids the
  step-function change.

- **Product isomorphisms (Task 9)**: The equation
  `cpProd (cpEmbed a) (cpEmbed b) = cpEmbed (cfpProd a b)`
  requires propositional equality via `ext`, not
  definitional equality. This means `β` and `elim` may need
  transports (`eqToHom` or `▸`).

- **Quotient lifting complexity (Tasks 6--8)**: The
  combination of `Quotient.lift₂` (for the coreflexive
  quotient) with `elimQ` (which itself uses
  `Quotient.lift₂` for the `btMorRel` quotient) creates
  nested quotient structures. Definitional unfolding may be
  slow; explicit `change` and `show` tactics help.
