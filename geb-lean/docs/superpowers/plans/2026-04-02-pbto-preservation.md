# PBTO Preservation in the Equalizer Completion

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Prove that the parameterized binary tree object
(PBTO) of `LawvereBTQuotCat` is preserved in its equalizer
completion `LawvereBTLexCat`, yielding a `HasPBTO` instance.

**Architecture:** The proof has two layers.  First, generic
lemmas about how `elim` (the PBTO fold) interacts with the
coreflexive completion structure: naturality under parameter
pre-composition, an algebra morphism property relating folds
to coreflexive sections, and preservation of first-argument
equivalence.  Second, these lemmas are combined to construct
the `HasPBTO` instance, with the premorphism condition for the
fold established via the algebra morphism property and the
one-step witnesses derived from the premorphism conditions of
the inputs.

**Tech Stack:** Lean 4, existing `HasPBTO` typeclass
(`LawvereBT.lean`), `elimQ`/`elimQ_ℓ`/`elimQ_β`/`elimQ_uniq`
(`LawvereBTQuot.lean`), `CoreflexiveEqv`/`IsCPPremorphism`
(`EqualizerCompletion.lean`), `cpProd`/`cpEmbed`
(`EqualizerCompletionLimits.lean`).

---

## File Structure

- `GebLean/EqualizerCompletionPBTO.lean` -- Generic
  supporting lemmas (naturality of `elim`, algebra
  morphism property, Lemma A) for any category with
  `HasChosenFiniteProducts` and `HasPBTO`
- `GebLean/LawvereBTEqCompletion.lean` -- Application:
  `HasPBTO LawvereBTLexCat` instance (modify existing)

---

## Mathematical Overview

### The PBTO universal property

`HasPBTO C` provides `T`, `ℓ`, `β`, and for any
`f : A ⟶ X`, `g : cfpProd X X ⟶ X`:

- `elim f g : cfpProd A T ⟶ X`
- `cfpInsertSnd ℓ A ≫ elim f g = f` (leaf)
- `cfpMap (𝟙 A) β ≫ elim f g =
  cfpLiftAssoc (elim f g) (elim f g) ≫ g` (branch)
- Uniqueness via `elim_uniq`

### Naturality of elim

For `h : B ⟶ A`:
`cfpMap h (𝟙 T) ≫ elim f g = elim (h ≫ f) g`.

Proof: both sides satisfy the computation rules for base
`h ≫ f` and step `g`; uniqueness gives equality.

### Algebra morphism property

Given `w : cfpProd X' X' ⟶ X'` satisfying
`cfpMap p p ≫ w = g ≫ p` for some `p : X ⟶ X'`,
then `p` is an algebra morphism from `(f, g)` to
`(f ≫ p, w)`:

`elim f g ≫ p = elim (f ≫ p) w`

Proof: `elim f g ≫ p` satisfies the computation rules
for base `f ≫ p` and step `w`.  The leaf case is
immediate.  The branch case uses
`cfpLiftAssoc φ φ ≫ cfpMap p p = cfpLiftAssoc (φ ≫ p) (φ ≫ p)`
(a product naturality identity) together with the hypothesis
`cfpMap p p ≫ w = g ≫ p`.  Apply `elim_uniq`.

### Lemma A: fold respects base equivalence

For one-step `CoreflexiveRelStep A a b` with witness `w`:
`CoreflexiveRelStep (cpProd A (cpEmbed T))
  (elim a s) (elim b s)` with witness `elim w s`.

Proof: by naturality,
`cfpMap A.left (𝟙 T) ≫ elim w s = elim (A.left ≫ w) s
= elim a s`. Similarly for `A.right`.
Extends to `EqvGen` by induction.

### One-step premorphism condition

When both `f` and `g` have one-step premorphism witnesses
`w_f` and `w_g`, the premorphism condition for `elim f g`
holds with witness `elim w_f w_g`, combining naturality
with the algebra morphism property.

### Assembling HasPBTO

For the PBTO in the completion:
`T = cpEmbed T_base`, `ℓ = cpEmbedding.map ℓ_base`,
`β = cpEmbedding.map β_base` (via an isomorphism
`cpProd (cpEmbed T) (cpEmbed T) ≅ cpEmbed (cfpProd T T)`).

For `elim`: given `[f] : A ⟶ X` and
`[g] : cpProd X X ⟶ X` in the completion, pick
representatives `f_rep`, `g_rep` and define
`elimLC [f] [g] = [elim f_rep g_rep]`.

The premorphism condition, well-definedness, computation
rules, and uniqueness are proved using the generic lemmas.

---

## Task 1: Product Naturality Lemmas

**Files:**

- Create: `GebLean/EqualizerCompletionPBTO.lean`

- [ ] **Step 1: Module header**

```lean
import GebLean.EqualizerCompletionLimits
import GebLean.LawvereBT

namespace GebLean

open CategoryTheory

universe v u

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C]
  [p : HasPBTO C]
```

- [ ] **Step 2: cfpInsertSnd naturality**

The leaf computation requires:
`cfpInsertSnd ℓ B ≫ cfpMap h (𝟙 T) =
h ≫ cfpInsertSnd ℓ A`.

Proof: both sides are `cfpLift` with the same
components (by product universality).

```lean
theorem cfpInsertSnd_cfpMap
    {A B : C} (h : B ⟶ A)
    (c : cfpTerminal ⟶ p.T) :
    cfpInsertSnd c B ≫ cfpMap h (𝟙 p.T) =
    h ≫ cfpInsertSnd c A
```

- [ ] **Step 3: cfpLiftAssoc naturality**

The branch computation requires:
`cfpLiftAssoc φ φ ≫ cfpMap q q =
cfpLiftAssoc (φ ≫ q) (φ ≫ q)` for
`φ : cfpProd A T ⟶ X` and `q : X ⟶ X'`.

```lean
theorem cfpLiftAssoc_cfpMap
    {A B D E E' : C}
    (f : cfpProd A B ⟶ E)
    (g : cfpProd A D ⟶ E)
    (q : E ⟶ E') :
    cfpLiftAssoc f g ≫ cfpMap q q =
    cfpLiftAssoc (f ≫ q) (g ≫ q)
```

Proof: by `cfpLift_uniq`, showing both sides agree
when composed with `cfpFst` and `cfpSnd`.

- [ ] **Step 4: cfpMap (𝟙 A) β naturality**

`cfpMap (𝟙 B) β ≫ cfpMap h (𝟙 T) =
cfpMap h (𝟙 (cfpProd T T)) ≫ cfpMap (𝟙 A) β`.

This is naturality of `cfpMap` composition.

- [ ] **Step 5: Build and verify**

Run: `lake build GebLean.EqualizerCompletionPBTO`

- [ ] **Step 6: Commit**

```bash
git add GebLean/EqualizerCompletionPBTO.lean GebLean.lean
git commit -m "feat: product naturality lemmas for PBTO"
```

---

## Task 2: Naturality of elim

**Files:**

- Modify: `GebLean/EqualizerCompletionPBTO.lean`

- [ ] **Step 1: State and prove**

```lean
theorem elim_naturality
    {A B X : C}
    (k : B ⟶ A)
    (f : A ⟶ X) (g : cfpProd X X ⟶ X) :
    cfpMap k (𝟙 p.T) ≫ p.elim f g =
    p.elim (k ≫ f) g
```

Proof strategy: apply `p.elim_uniq` to show
`cfpMap k (𝟙 T) ≫ elim f g` satisfies the
computation rules for base `k ≫ f` and step `g`.

Leaf case: uses `cfpInsertSnd_cfpMap`.
Branch case: uses `cfpMap_comp` and the branch
computation rule of `elim f g`.

- [ ] **Step 2: Build and verify**

Run: `lake build GebLean.EqualizerCompletionPBTO`

- [ ] **Step 3: Commit**

```bash
git add GebLean/EqualizerCompletionPBTO.lean
git commit -m "feat: naturality of PBTO elim"
```

---

## Task 3: Algebra Morphism Property

**Files:**

- Modify: `GebLean/EqualizerCompletionPBTO.lean`

- [ ] **Step 1: State and prove**

```lean
theorem elim_algebra_morphism
    {A X X' : C}
    (f : A ⟶ X) (g : cfpProd X X ⟶ X)
    (q : X ⟶ X')
    (w : cfpProd X' X' ⟶ X')
    (hw : cfpMap q q ≫ w = g ≫ q) :
    p.elim f g ≫ q = p.elim (f ≫ q) w
```

Proof: apply `p.elim_uniq` to `elim f g ≫ q`:

Leaf: `cfpInsertSnd ℓ A ≫ (elim f g ≫ q)
= (cfpInsertSnd ℓ A ≫ elim f g) ≫ q = f ≫ q` ✓

Branch: `cfpMap (𝟙 A) β ≫ (elim f g ≫ q)
= (cfpLiftAssoc (elim f g) (elim f g) ≫ g) ≫ q
= cfpLiftAssoc (elim f g) (elim f g) ≫ (g ≫ q)
= cfpLiftAssoc (elim f g) (elim f g) ≫ (cfpMap q q ≫ w)`
  [by `hw`]
`= (cfpLiftAssoc (elim f g) (elim f g) ≫ cfpMap q q) ≫ w
= cfpLiftAssoc (elim f g ≫ q) (elim f g ≫ q) ≫ w` ✓
  [by `cfpLiftAssoc_cfpMap`]

- [ ] **Step 2: Build and verify**

Run: `lake build GebLean.EqualizerCompletionPBTO`

- [ ] **Step 3: Commit**

```bash
git add GebLean/EqualizerCompletionPBTO.lean
git commit -m "feat: algebra morphism property for PBTO elim"
```

---

## Task 4: Lemma A (Fold Respects Base Equivalence)

**Files:**

- Modify: `GebLean/EqualizerCompletionPBTO.lean`

- [ ] **Step 1: One-step version**

```lean
theorem elim_base_relStep
    (A : CoreflexivePairObj C)
    {X : C}
    {a b : A.src ⟶ X}
    (s : cfpProd X X ⟶ X)
    (hab : CoreflexiveRelStep A a b) :
    CoreflexiveRelStep
      (cpProd A (cpEmbed p.T))
      (p.elim a s) (p.elim b s)
```

Proof: obtain witness `w` from `hab`.  The witness
for the conclusion is `p.elim w s`.  By
`elim_naturality`:
`cfpMap A.left (𝟙 T) ≫ elim w s
= elim (A.left ≫ w) s = elim a s`.
Similarly for `A.right`.

- [ ] **Step 2: EqvGen version**

```lean
theorem elim_base_eqvGen
    (A : CoreflexivePairObj C)
    {X : C}
    {a b : A.src ⟶ X}
    (s : cfpProd X X ⟶ X)
    (hab : CoreflexiveEqv A a b) :
    CoreflexiveEqv
      (cpProd A (cpEmbed p.T))
      (p.elim a s) (p.elim b s)
```

Proof: by induction on `Relation.EqvGen`.

- [ ] **Step 3: Build and verify**

Run: `lake build GebLean.EqualizerCompletionPBTO`

- [ ] **Step 4: Commit**

```bash
git add GebLean/EqualizerCompletionPBTO.lean
git commit -m "feat: Lemma A -- fold respects base equivalence"
```

---

## Task 5: One-Step Premorphism Condition

**Files:**

- Modify: `GebLean/EqualizerCompletionPBTO.lean`

- [ ] **Step 1: State and prove**

When both `f` and `g` have one-step premorphism
witnesses:

```lean
theorem elim_isPremorphism_oneStep
    (A X : CoreflexivePairObj C)
    (f : A.src ⟶ X.src)
    (g : cfpProd X.src X.src ⟶ X.src)
    (w_f : A.tgt ⟶ X.tgt)
    (hw_f_left :
      A.left ≫ w_f = f ≫ X.left)
    (hw_f_right :
      A.right ≫ w_f = f ≫ X.right)
    (w_g : cfpProd X.tgt X.tgt ⟶ X.tgt)
    (hw_g_left :
      cfpMap X.left X.left ≫ w_g =
      g ≫ X.left)
    (hw_g_right :
      cfpMap X.right X.right ≫ w_g =
      g ≫ X.right) :
    CoreflexiveRelStep
      (cpProd A (cpEmbed p.T))
      (p.elim f g ≫ X.left)
      (p.elim f g ≫ X.right)
```

Proof: witness is `p.elim w_f w_g`. By
`elim_naturality` + `elim_algebra_morphism`:

`cfpMap A.left (𝟙 T) ≫ elim w_f w_g
= elim (A.left ≫ w_f) w_g` (naturality)
`= elim (f ≫ X.left) w_g` (by `hw_f_left`)
`= elim f g ≫ X.left` (algebra morphism
  with `hw_g_left`).

Similarly for `A.right` using `hw_f_right`
and `hw_g_right`.

- [ ] **Step 2: Build and verify**

Run: `lake build GebLean.EqualizerCompletionPBTO`

- [ ] **Step 3: Commit**

```bash
git add GebLean/EqualizerCompletionPBTO.lean
git commit -m "feat: one-step premorphism for PBTO elim"
```

---

## Task 6: General Premorphism via Reflexivity Witnesses

**Files:**

- Modify: `GebLean/EqualizerCompletionPBTO.lean`

- [ ] **Step 1: Reflexivity witness construction**

For any premorphism `g`, the reflexivity of
`CoreflexiveRelStep` gives a witness `w_g_refl`
satisfying the algebra morphism hypothesis for
a single section:

```lean
def cpReflWitness
    (X : CoreflexivePairObj C)
    {V : C}
    (g : cfpProd X.src X.src ⟶ V)
    (q : X.src ⟶ X.tgt) :
    cfpProd X.tgt X.tgt ⟶ V :=
  cfpMap X.retract X.retract ≫ g
```

Note: `cfpMap X.retract X.retract ≫ g` satisfies
`cfpMap q q ≫ (cfpMap X.retract X.retract ≫ g)
= cfpMap (q ≫ X.retract) (q ≫ X.retract) ≫ g`
which equals `cfpMap 𝟙 𝟙 ≫ g = g` when
`q ≫ X.retract = 𝟙` (i.e., when `q` is `X.left`
or `X.right`).

- [ ] **Step 2: Derive algebra morphism via reflexivity**

Show: for any `g` satisfying `IsCPPremorphism
(cpProd X X) X g`:

`p.elim f g ≫ X.left =
p.elim (f ≫ X.left) (cpReflWitness X g)`

and

`p.elim f g ≫ X.right =
p.elim (f ≫ X.right) (cpReflWitness X g)`

Both follow from `elim_algebra_morphism` with
`q = X.left` (resp. `X.right`) and
`w = cpReflWitness X g`, using
`X.left ≫ X.retract = 𝟙` (resp. `X.right`).

Note: BOTH equations use the SAME `cpReflWitness`.
This is because `cfpMap X.left X.left` and
`cfpMap X.right X.right` both compose with the
retraction to give `𝟙`:
`cfpMap X.left X.left ≫ cfpMap X.retract X.retract
= cfpMap 𝟙 𝟙 = 𝟙`.

- [ ] **Step 3: Combine with Lemma A**

```lean
theorem elim_isPremorphism
    (A X : CoreflexivePairObj C)
    (f : A.src ⟶ X.src)
    (g : cfpProd X.src X.src ⟶ X.src)
    (hf : IsCPPremorphism A X f)
    (hg : IsCPPremorphism (cpProd X X) X g) :
    IsCPPremorphism
      (cpProd A (cpEmbed p.T)) X
      (p.elim f g)
```

Proof:

`p.elim f g ≫ X.left
= p.elim (f ≫ X.left) (cpReflWitness X g)`
  [Step 2, left]

`~  p.elim (f ≫ X.right) (cpReflWitness X g)`
  [Lemma A (`elim_base_eqvGen`), using `hf`]

`= p.elim f g ≫ X.right`
  [Step 2, right]

Combine by `Relation.EqvGen.trans`.

- [ ] **Step 4: Build and verify**

Run: `lake build GebLean.EqualizerCompletionPBTO`

- [ ] **Step 5: Commit**

```bash
git add GebLean/EqualizerCompletionPBTO.lean
git commit -m "feat: general premorphism condition for PBTO elim"
```

---

## Task 7: Well-Definedness and elimLC

**Files:**

- Modify: `GebLean/EqualizerCompletionPBTO.lean`

- [ ] **Step 1: First-argument well-definedness**

If `CoreflexiveEqv A f₁ f₂`, then
`CoreflexiveEqv (cpProd A (cpEmbed T))
(elim f₁ g) (elim f₂ g)`.

This is `elim_base_eqvGen`.

- [ ] **Step 2: Second-argument well-definedness**

If `CoreflexiveEqv (cpProd X X) g₁ g₂`, then
`CoreflexiveEqv (cpProd A (cpEmbed T))
(elim f g₁) (elim f g₂)`.

Proof: by step 2 of Task 6,
`elim f g₁ ≫ X.left
= elim (f ≫ X.left) (cpReflWitness X g₁)`
and
`elim f g₂ ≫ X.right
= elim (f ≫ X.right) (cpReflWitness X g₂)`.

But `cpReflWitness X g₁ = cfpMap X.retract X.retract ≫ g₁`
and `cpReflWitness X g₂ = cfpMap X.retract X.retract ≫ g₂`.

Since the CoreflexiveEqv-quotient is on the CPMor level
(which includes the step-function change), and both
`elim f g₁` and `elim f g₂` must produce the same CPMor
element, the well-definedness follows from showing that
`cfpMap X.retract X.retract ≫ g₁` and
`cfpMap X.retract X.retract ≫ g₂` produce
the same `cpReflWitness`, hence the same fold results.

`cpReflWitness X g₁` and `cpReflWitness X g₂` differ
by pre-composition of the equivalence with
`cfpMap X.retract X.retract`.  Post-composing the
Lemma A argument through the reflexivity-witness
algebra morphism equations, the fold results
`elim f g₁` and `elim f g₂` are connected via:

`elim f g₁ ≫ X.left
= elim (f ≫ X.left) (cpReflWitness X g₁)`
`~ elim (f ≫ X.left) (cpReflWitness X g₂)`
  [since cpReflWitness X g₁ and cpReflWitness X g₂
   differ by post-composing g₁ vs g₂ with
   cfpMap X.retract X.retract, and the fold result
   on the retracted step is determined by Lemma A
   applied via the naturality of the retraction]
`= elim f g₂ ≫ X.left`

**Note**: This step may require factoring out an
additional lemma about how the fold interacts with
pre-composition on the step function through the
retraction.  If the proof becomes too involved,
an alternative is to define `elimLC` by
`Quotient.lift₂` and verify well-definedness
directly by showing the quotient-level fold
is invariant under representative changes, using
the computation rules and uniqueness.

- [ ] **Step 3: Define elimLC**

```lean
def elimLC
    {A X : CoreflexivePairObj C}
    (f : A ⟶ X)
    (g : cpProd X X ⟶ X) :
    cpProd A (cpEmbed p.T) ⟶ X
```

Define using `Quotient.lift₂` on the CPMor inputs,
with the premorphism condition from
`elim_isPremorphism` and well-definedness from
the two lemmas above.

- [ ] **Step 4: Build and verify**

Run: `lake build GebLean.EqualizerCompletionPBTO`

- [ ] **Step 5: Commit**

```bash
git add GebLean/EqualizerCompletionPBTO.lean
git commit -m "feat: elimLC definition"
```

---

## Task 8: Computation Rules and Uniqueness

**Files:**

- Modify: `GebLean/EqualizerCompletionPBTO.lean`

- [ ] **Step 1: cpProd-cpEmbed isomorphism**

Show `cpProd (cpEmbed a) (cpEmbed b) =
cpEmbed (cfpProd a b)` by `CoreflexivePairObj.ext`
and `cfpMap_id`.

- [ ] **Step 2: Leaf computation rule**

```lean
theorem elimLC_ℓ
    {A X : CoreflexivePairObj C}
    (f : A ⟶ X) (g : cpProd X X ⟶ X) :
    cfpInsertSnd
      (cpEmbedding.map p.ℓ) A ≫
      elimLC f g = f
```

Reduce via `Quotient.ind₂` on `f`, `g`.  At the raw
level, use `elim_ℓ` from the base `HasPBTO`, combined
with the product isomorphism.  The composition in the
completion reduces to the composition in the base on
`src`-components.

- [ ] **Step 3: Branch computation rule**

Similar structure, using `elim_β`.

- [ ] **Step 4: Uniqueness**

```lean
theorem elimLC_uniq
    {A X : CoreflexivePairObj C}
    (f : A ⟶ X)
    (g : cpProd X X ⟶ X)
    (φ : cpProd A (cpEmbed p.T) ⟶ X)
    (hℓ : ...) (hβ : ...) :
    φ = elimLC f g
```

Reduce via `Quotient.ind` on all arguments.  Extract
raw-level equations from `hℓ` and `hβ`, then apply
`elim_uniq` from the base.

- [ ] **Step 5: Build and verify**

Run: `lake build GebLean.EqualizerCompletionPBTO`

- [ ] **Step 6: Commit**

```bash
git add GebLean/EqualizerCompletionPBTO.lean
git commit -m "feat: computation rules and uniqueness for elimLC"
```

---

## Task 9: HasPBTO Instance

**Files:**

- Modify: `GebLean/LawvereBTEqCompletion.lean`

- [ ] **Step 1: Instantiate for LawvereBTLexCat**

```lean
instance : HasPBTO LawvereBTLexCat where
  T := cpEmbed (1 : LawvereBTQuotCat)
  ℓ := cpEmbedding.map btLeafQ
  β := eqToHom (cpProd_cpEmbed_eq 1 1).symm ≫
    cpEmbedding.map btBranchQ
  elim f g := elimLC f g
  elim_ℓ f g := elimLC_ℓ f g
  elim_β f g := elimLC_β f g
  elim_uniq f g φ hℓ hβ :=
    elimLC_uniq f g φ hℓ hβ
```

The `β` field uses `eqToHom` to transport across the
`cpProd_cpEmbed_eq` isomorphism.

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
Task 1 → Task 2
Task 1 → Task 3
Task 3 + Task 4 → Task 5
Task 4 + Task 5 → Task 6
Task 4 + Task 6 → Task 7
Task 7 → Task 8
Task 8 → Task 9
```

## Risk Assessment

- **Task 6 (general premorphism)**: The proof that
  `cpReflWitness` gives a valid algebra morphism for
  BOTH `X.left` and `X.right` simultaneously is the
  mathematical linchpin.  The argument uses
  `q ≫ X.retract = 𝟙` (for `q = X.left` or `X.right`)
  to collapse `cfpMap q q ≫ cpReflWitness X g` to `g`.
  This makes BOTH sections algebra morphisms to the SAME
  reflexivity witness, which is the key that avoids
  Lemma B (step-function EqvGen change) entirely.

- **Task 7 (well-definedness)**: The second-argument
  well-definedness (changing `g` within its equivalence
  class) is the most involved step.  The reflexivity
  witness `cpReflWitness X g = cfpMap X.retract X.retract
  ≫ g` changes when `g` changes, so the fold results
  change.  The proof needs to show the fold results stay
  in the same `CoreflexiveEqv` class.  This may require
  an extended argument combining Lemma A with the
  algebra morphism property applied through the
  retraction.  If this step proves intractable, a
  fallback is to define `elimLC` differently (e.g., by
  extracting a canonical representative) or to prove
  well-definedness via the interpretation functor for
  `LawvereBTQuotCat` specifically.

- **Task 8 (computation rules)**: The `β` field requires
  transport across `cpProd_cpEmbed_eq`, which introduces
  `eqToHom` terms.  These can be resolved using `simp`
  with `eqToHom` lemmas, or by defining the computation
  rules with the transport baked in.

- **Task 9 (instantiation)**: The `eqToHom` in the `β`
  definition may cause typeclass resolution to struggle
  if the types don't unify definitionally.  Alternative:
  prove `cpProd_cpEmbed_eq` as a definitional equality
  (which holds if `cfpMap_id` reduces definitionally),
  avoiding transport entirely.
