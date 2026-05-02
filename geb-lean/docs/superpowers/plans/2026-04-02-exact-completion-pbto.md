# PER Completion of the Lawvere BT Theory

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Construct the category of T-valued partial
equivalence relations (PERs) on the binary tree type T
within the Lawvere BT theory, yielding an exact category
with finite limits, finite colimits, distributivity, and a
parameterized binary tree object (PBTO) -- all assuming
only primitive recursive computation.

**Architecture:** The construction exploits the fact that
unlabeled binary trees carry a built-in pairing mechanism
(`branch`) and built-in Boolean logic (`leaf` = true,
non-leaf = false, with `AND` = grafting, `NOT` = fold to
constant, `OR` = De Morgan).  PER objects are morphisms
`T x T -> T` in the Lawvere BT theory satisfying equational
symmetry and transitivity conditions.  Morphisms are
relation-preserving maps `T -> T`.  Products come from the
tree encoding (pairing via `branch`, projections via
fold-derived destructors), coproducts from tag encoding,
and the PBTO is preserved by a clean structural induction
that avoids the Lemma B obstruction from the equalizer
completion approach.

**Tech Stack:** Lean 4, `HasPBTO` / `elim`
(`LawvereBT.lean`), `HasChosenFiniteProducts` / `cfpProd`
/ `cfpMap` (`ComputableLimits.lean`), `LawvereBTQuotCat`
(`LawvereBTQuot.lean`).

---

## Mathematical Overview

### The leaf-true Boolean logic on T

Using the convention `leaf` = true, non-leaf = false:

- **AND** (conjunction) = grafting = `elim id beta`:
  `treeAnd(a, b)` replaces every leaf in `b` with `a`.
  `treeAnd(a, b) = leaf` iff `a = leaf` AND `b = leaf`.
- **NOT** (negation) = `elim (beta(leaf,leaf)) (const leaf)`:
  `treeNot(leaf) = branch(leaf,leaf)`,
  `treeNot(branch(_,_)) = leaf`.
- **OR** (disjunction) = De Morgan:
  `treeOr(a, b) = treeNot(treeAnd(treeNot(a), treeNot(b)))`.
- **IMPLIES**: `treeImplies(a, b) = treeOr(treeNot(a), b)`.
- **IF-THEN-ELSE**: `ite(a, b, cond)` returns `a` when
  `cond = leaf`, `b` otherwise.  Defined via fold into
  pairs: `elim <pi1, pi2> <pi2 . pi1, pi2 . pi1>`.
- **isLeaf**: `elim leaf (const (branch leaf leaf))`.
- **isBranch**: `treeNot . isLeaf`.

### Shallow destructors via the fold-with-self trick

Catamorphisms recurse bottom-up, but shallow one-level
destructors are recoverable by folding into a triple
`(left, right, self)`:

```text
fold_destruct = elim <l, l, l> g : T -> T x T x T
  where g((_, _, a), (_, _, b)) = (a, b, branch(a, b))
```

By structural induction, `fold_destruct(t) = (left(t),
right(t), t)`.  The third component always reconstructs the
original tree, so the step function extracts the original
subtrees (not recursive results) into the first two
positions.

### Tree equality

`treeEq : T x T -> T` is defined by folding over the first
tree with the second as parameter, using the shallow
destructors for case analysis on the second:

```text
treeEq(leaf, y)        = isLeaf(y)
treeEq(branch(a,b), y) = treeAnd(isBranch(y),
                            treeAnd(treeEq(a, left(y)),
                                    treeEq(b, right(y))))
```

This is a single fold over the first tree (the second is
the parameter), with the step function using `isLeaf`,
`isBranch`, `left`, `right` on the second tree.  All
components are morphisms in the Lawvere BT theory,
following the same pattern as PRA's decidable equality on
natural numbers.

### PER objects

A partial equivalence relation on T is a morphism
`rel : T x T -> T` satisfying:

- **Symmetry**: `rel . swap = rel`
  (as morphisms `T^2 -> T`)
- **Transitivity**:
  `treeImplies(treeAnd(rel . pi13, rel . pi32), rel . pi12)
  = const(leaf)` (as morphisms `T^3 -> T`)

where `pi12`, `pi13`, `pi32` are projection pairs from
`T^3`.  No reflexivity section is required -- this is what
makes it "partial."

The **domain** of the PER is `{x in T | rel(x, x) = leaf}`
-- the self-related elements.  The PER restricts to a full
equivalence relation on its domain.

### Why product-based transitivity is safe

The transitivity condition uses all of `T^3`, not a
pullback.  For pseudo-equivalence relations (with a
reflexivity section `i : X -> R`), product-based
transitivity trivializes: `c(i(x), i(y))` witnesses
`x ~ y` for all `x, y`.  PERs have no reflexivity section,
so this trivialization argument does not apply.

### Morphisms

A morphism `f : (T, rel_X) -> (T, rel_Y)` is a morphism
`f : T -> T` in the Lawvere BT theory satisfying:

```text
treeImplies(rel_X, rel_Y . (f x f)) = const(leaf)
```

as a morphism `T^2 -> T` (where `f x f` denotes the
product of `f` with itself).

Two morphisms `f, g` are equivalent when they agree on
the domain modulo the target PER:

```text
treeImplies(rel_X . diag, rel_Y . <f, g>) = const(leaf)
```

as a morphism `T -> T` (where `diag = <id, id>`).

This equivalence is reflexive (from the relation-
preservation condition), symmetric (from symmetry of
`rel_Y`), and transitive (from transitivity of `rel_Y`).

### Finite products from tree encoding

- **Terminal**: `rel_1(x,y) = treeAnd(isLeaf(x), isLeaf(y))`.
  Domain = `{leaf}`.
- **Product**: `rel_{XxY}(t1, t2) =
  treeAnd(isBranch(t1), treeAnd(isBranch(t2),
  treeAnd(rel_X(left(t1), left(t2)),
  rel_Y(right(t1), right(t2)))))`.
  Domain = `{branch(a, b) | a in dom(rel_X),
  b in dom(rel_Y)}`.
- **Projections**: `left`, `right` (the fold-derived
  destructors).
- **Pairing**: `<f, g>(t) = branch(f(t), g(t))`.

### Finite coproducts from tag encoding

- **Initial**: `rel_0(x,y) = branch(leaf, leaf)` (constant
  false).  Domain = empty.
- **Coproduct**: tag with `leaf` (left) or non-leaf
  (right): `inl(x) = branch(leaf, x)`,
  `inr(y) = branch(branch(leaf,leaf), y)`.
- **Case analysis**: `[f,g](t) = ite(f(right(t)),
  g(right(t)), isLeaf(left(t)))`.

### Equalizers

The equalizer of `f, g : (T, rel_X) -> (T, rel_Y)` is the
sub-PER:

```text
rel_E(x1, x2) = treeAnd(rel_X(x1, x2),
  treeAnd(rel_Y(f(x1), g(x1)), rel_Y(f(x2), g(x2))))
```

Domain = `{x in dom(rel_X) | f(x) ~_{rel_Y} g(x)}`.
Inclusion is `id_T`.

### Regularity (image factorization)

Given `f : (T, rel_X) -> (T, rel_Y)`:

- **Kernel pair**: `rel_K(x1, x2) = treeAnd(rel_X(x1, x1),
  treeAnd(rel_X(x2, x2), rel_Y(f(x1), f(x2))))` --
  definable as a composition of `rel_Y` with `f x f`
  restricted to `dom(rel_X)`.
- **Regular epi**: `id_T : (T, rel_X) -> (T, rel_K)`.
  Valid because `rel_X(x1, x2)` implies
  `rel_K(x1, x2)` (since `f` preserves relations).
- **Mono**: `f : (T, rel_K) -> (T, rel_Y)`.  Injective on
  equivalence classes by construction (the kernel pair of
  `f` restricted to the image IS `rel_K`).

No existential quantification is needed.  The kernel pair
PER is directly definable as a composition of morphisms.

### Exactness (effective equivalence relations)

Given an equivalence relation `E` on `(T, rel_X)` in the
PER category (encoded as a sub-PER of `rel_{XxX}`), the
quotient PER is:

```text
rel_Q(x1, x2) = treeAnd(rel_X(x1, x1),
  treeAnd(rel_X(x2, x2),
  rel_E(branch(x1, x2), branch(x1, x2))))
```

The last factor is the self-relatedness of `branch(x1, x2)`
under `rel_E`, which encodes `x1 E x2`.  The quotient map
is `id_T : (T, rel_X) -> (T, rel_Q)`.  The kernel pair of
this map is `E` itself: two elements are identified in the
quotient iff they are `E`-related.  So every equivalence
relation is effective.

### Distributivity

Products distribute over coproducts via tree rearrangement:
`branch(a, branch(tag, bc)) <-> branch(tag, branch(a, bc))`
-- both directions are definable morphisms `T -> T`.

### PBTO preservation (the main result)

The PBTO in the PER category is `(T, treeEq)` -- trees
related iff structurally equal.  Domain = all of T.

Given base `f : (T, rel_1) -> (T, rel_X)` and step
`g : (T, rel_{XxX}) -> (T, rel_X)`, the fold is
`phi = elim f0 g0 : T -> T` where `f0` and `g0` are the
underlying Lawvere-theory morphisms.

**Existence (phi is relation-preserving):** Since
`treeEq(t1, t2) = leaf` iff `t1 = t2`, we need
`rel_X(phi(t), phi(t)) = leaf` for all `t` -- that is,
`phi(t)` is in `dom(rel_X)`.  By structural induction:

- *Leaf*: `phi(leaf) = f0(leaf)`.  Since `f` is a PER
  morphism from `rel_1` and `leaf in dom(rel_1)`, we get
  `f0(leaf) in dom(rel_X)`.
- *Branch*: `phi(branch(t1,t2)) = g0(branch(phi(t1),
  phi(t2)))`.  By induction, `phi(t1), phi(t2) in
  dom(rel_X)`, so `branch(phi(t1), phi(t2)) in
  dom(rel_{XxX})`.  Since `g` is a PER morphism,
  `g0(branch(phi(t1), phi(t2))) in dom(rel_X)`.

**Uniqueness (up to `rel_X`):** If `phi` and `psi` both
satisfy the fold equations modulo `rel_X`, then
`rel_X(phi(t), psi(t)) = leaf` for all `t`, by structural
induction:

- *Leaf*: both are `rel_X`-equivalent to `f0(leaf)`, so
  they are `rel_X`-related by transitivity.
- *Branch*: by induction, `phi(ti) rel_X psi(ti)`.  So
  `branch(phi(t1), phi(t2)) rel_{XxX} branch(psi(t1),
  psi(t2))`.  Since `g` preserves relations,
  `g0(branch(phi(...))) rel_X g0(branch(psi(...)))`.
  By transitivity with the fold equations:
  `phi(branch(t1,t2)) rel_X psi(branch(t1,t2))`.

**Why Lemma B does not arise:** In the equalizer
completion, the fold must land in an EQUALIZER (a subset
defined by `f >> left = f >> right`), which is not an
inductive condition.  In the PER completion, the fold must
land in the DOMAIN of a PER (defined by self-relatedness),
which IS inductive: if `f` and `g` map domain elements to
domain elements, then `elim f g` does too.

---

## Summary of Properties and Justifications

**Category:** Composition of relation-preserving maps
preserves relations; equivalence is compatible with
composition.

**Finite products:** Terminal = leaf PER; products =
branch encoding with left/right projections.

**Equalizers:** Sub-PER where `f ~ g`; inclusion = `id_T`.

**Finite limits:** Products + equalizers.

**Initial object:** Empty PER (constant false).

**Coproducts:** Tag encoding with leaf/non-leaf index;
case analysis via `ite`.

**Coequalizers:** Kernel-pair coequalizers from PER
coarsening; general coequalizers via iteration.

**Finite colimits:** Coproducts + coequalizers.

**Regular:** Image factorization via kernel-pair PER; no
existential quantification needed.

**Exact:** Equivalence relations are effective: quotient
PER = E-relation; kernel pair = E itself.

**Distributive:** Tree rearrangement isomorphisms.

**PBTO:** `(T, treeEq)`; fold = `elim`; existence by
structural induction on domain preservation; uniqueness by
structural induction on `rel_X`-equivalence; avoids
Lemma B.

**Primitive recursive only:** All operations defined via
the PBTO's `elim`; no classical axioms, no higher-order
types.

---

## File Structure

- Create: `GebLean/TreeLogic.lean` -- Boolean logic on T,
  shallow destructors, tree equality
- Create: `GebLean/TreePER.lean` -- PER objects, morphisms,
  equivalence, category instance
- Create: `GebLean/TreePERLimits.lean` -- Terminal,
  products, equalizers, `HasFiniteLimits`
- Create: `GebLean/TreePERColimits.lean` -- Initial,
  coproducts, coequalizers
- Create: `GebLean/TreePERExact.lean` -- Regularity,
  exactness, distributivity
- Create: `GebLean/TreePERPBTO.lean` -- PBTO preservation
- Modify: `GebLean.lean` -- Add imports for new modules

---

## Phase A: Tree Logic Primitives

### Task 1: Boolean Logic on T

**Files:**

- Create: `GebLean/TreeLogic.lean`

Define the leaf-true Boolean logic and shallow destructors
within the Lawvere BT theory.  Each definition is a
morphism in `LawvereBTQuotCat` (or equivalently, a
`BTMorN`/`BTMor1` term).

- [ ] **Step 1: Define `isLeaf` and `treeNot`**

```lean
import GebLean.LawvereBTQuot

namespace GebLean

open CategoryTheory

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C] [p : HasPBTO C]

def isLeaf : cfpProd cfpTerminal p.T ⟶ p.T :=
  p.elim p.l
    (cfpTerminalFrom (cfpProd p.T p.T) ≫ p.l)

-- treeNot(leaf) = branch(leaf, leaf)
-- treeNot(branch(_, _)) = leaf
def treeNot :
    cfpProd cfpTerminal p.T ⟶ p.T :=
  p.elim
    (cfpTerminalFrom cfpTerminal ≫ p.l ≫ _)
    -- step: const leaf
    _
```

Define one definition at a time.  Build after each.
Use underscores to check goal types before filling in.

- [ ] **Step 2: Define `treeAnd` (grafting)**

```lean
-- treeAnd(a, b) = b with every leaf replaced by a
-- treeAnd = elim id beta
-- As a morphism: cfpProd T T -> T
def treeAnd :
    cfpProd p.T p.T ⟶ p.T :=
  p.elim (cfpSnd _ _) p.beta  -- placeholder
```

Wait -- we need to be precise about the types.
`elim f g : cfpProd A T -> X`.  For treeAnd with
`A = T, X = T`:

- `f = id_T : T -> T` (at a leaf of the second tree,
  return the first tree)
- `g = beta : T x T -> T` (at a branch, recombine)

Verify the types match the PBTO signature.  Build.

- [ ] **Step 3: Define `treeOr` and `treeImplies`**

Via De Morgan:

- `treeOr(a, b) = treeNot(treeAnd(treeNot(a), treeNot(b)))`
- `treeImplies(a, b) = treeOr(treeNot(a), b)`

These are compositions of existing morphisms.

- [ ] **Step 4: Define `ite` (if-then-else)**

`ite(a, b, cond)` returns `a` when `cond = leaf`,
`b` otherwise.  Fold into `T x T`:

```lean
-- elim <pi1, pi2> <pi2.pi1, pi2.pi1>
-- : (T x T) x T -> T x T
-- then project first component
def ite_fold :
    cfpProd (cfpProd p.T p.T) p.T ⟶
      cfpProd p.T p.T :=
  p.elim
    (𝟙 (cfpProd p.T p.T))
    (cfpLift
      (cfpSnd _ _ ≫ cfpFst _ _)
      (cfpSnd _ _ ≫ cfpFst _ _))

def ite :
    cfpProd (cfpProd p.T p.T) p.T ⟶ p.T :=
  ite_fold ≫ cfpFst _ _
```

Build and verify: `ite(a, b, leaf) = a` and
`ite(a, b, branch(_, _)) = b`.

- [ ] **Step 5: Define `left` and `right` (shallow
destructors)**

Fold into `T x T x T` using the fold-with-self trick:

```lean
def fold_destruct :
    cfpProd cfpTerminal p.T ⟶
      cfpProd p.T (cfpProd p.T p.T) :=
  p.elim
    (cfpLift p.l (cfpLift p.l p.l))
    -- g((_, _, a), (_, _, b)) = (a, b, branch(a, b))
    _

def treeLeft :
    cfpProd cfpTerminal p.T ⟶ p.T :=
  fold_destruct ≫ cfpFst _ _

def treeRight :
    cfpProd cfpTerminal p.T ⟶ p.T :=
  fold_destruct ≫ cfpSnd _ _ ≫ cfpFst _ _
```

Build and verify by checking the step function
types carefully.  The step function `g` for
`fold_destruct` receives two triples
`(r_a, (l_a, self_a))` and `(r_b, (l_b, self_b))`
packed as `(T x T x T) x (T x T x T)`, and must
produce `(self_a, (self_b, branch(self_a, self_b)))`.

- [ ] **Step 6: Prove computation rules**

For each operation, prove the leaf and branch cases:

- `treeAnd(a, leaf) = a`
- `treeAnd(leaf, b) = b`
- `treeNot(leaf) = branch(leaf, leaf)`
- `treeNot(branch(a, b)) = leaf`
- `ite(a, b, leaf) = a`
- `ite(a, b, branch(_, _)) = b`
- `treeLeft(leaf) = leaf`
- `treeLeft(branch(a, b)) = a`
- `treeRight(leaf) = leaf`
- `treeRight(branch(a, b)) = b`

Each proof uses `elim_l` (leaf case) and `elim_beta`
(branch case) from `HasPBTO`.

- [ ] **Step 7: Define `treeEq`**

```lean
-- treeEq(leaf, y) = isLeaf(y)
-- treeEq(branch(a,b), y) = treeAnd(isBranch(y),
--     treeAnd(treeEq(a, left(y)),
--             treeEq(b, right(y))))
def treeEq : cfpProd p.T p.T ⟶ p.T :=
  p.elim
    isLeaf  -- base: isLeaf(y)
    _       -- step: combine recursive results
            -- with isBranch and left/right
```

The step function takes two recursive results
(comparisons of left and right subtrees with y)
and combines them.  The types need to work out
with the parametric structure of `elim`.

- [ ] **Step 8: Prove treeEq computation rules**

- `treeEq(leaf, leaf) = leaf`
- `treeEq(leaf, branch(a,b)) = branch(leaf, leaf)`
- `treeEq(branch(a,b), leaf) = branch(leaf, leaf)`
- `treeEq(branch(a1,b1), branch(a2,b2)) =
  treeAnd(treeEq(a1, a2), treeEq(b1, b2))`

- [ ] **Step 9: Build, verify, commit**

Run `lake build` and `lake test`.

```bash
git add GebLean/TreeLogic.lean
git commit -m "feat: Boolean logic and destructors on T"
```

---

### Task 2: PER Objects and Morphisms

**Files:**

- Create: `GebLean/TreePER.lean`

Define PER objects, morphisms, their equivalence relation,
and the category instance.

- [ ] **Step 1: Define `TreePERObj`**

```lean
import GebLean.TreeLogic

namespace GebLean

open CategoryTheory

variable {C : Type u} [Category.{v} C]
  [h : HasChosenFiniteProducts C] [p : HasPBTO C]

@[ext]
structure TreePERObj
    (C : Type u) [Category.{v} C]
    [HasChosenFiniteProducts C]
    [HasPBTO C] where
  rel : cfpProd p.T p.T ⟶ p.T
  symm_ :
    cfpMap (cfpSnd p.T p.T) (cfpFst p.T p.T) ≫ rel
    = rel
  trans_ :
    -- treeImplies(
    --   treeAnd(rel . pi13, rel . pi32),
    --   rel . pi12)
    -- = const(leaf)
    -- (as a morphism T^3 -> T)
    _  -- exact type TBD during implementation
```

The exact formulation of the transitivity condition
depends on how `T^3` projections are expressed using
`cfpProd` and `cfpFst`/`cfpSnd`.  Use underscores
to determine the types, then fill in.

Build and verify.

- [ ] **Step 2: Define `TreePERMor` (pre-morphisms)**

```lean
structure TreePERPreMor
    (X Y : TreePERObj C) where
  map : p.T ⟶ p.T
  preserves :
    treeImplies ≫ cfpLift
      (X.rel)
      (cfpMap map map ≫ Y.rel)
    = cfpTerminalFrom _ ≫ p.l
    -- i.e., for all (x1, x2),
    -- treeImplies(X.rel(x1,x2),
    --   Y.rel(map(x1), map(x2))) = leaf
```

The exact encoding of the preservation condition
needs care with the product structure.  Build one
definition at a time.

- [ ] **Step 3: Define morphism equivalence**

```lean
def TreePERMorEquiv
    {X Y : TreePERObj C}
    (f g : TreePERPreMor X Y) : Prop :=
  -- treeImplies(X.rel . diag,
  --   Y.rel . <f.map, g.map>) = const(leaf)
  _
```

- [ ] **Step 4: Prove equivalence relation properties**

- Reflexivity: from the relation-preservation condition
  applied to `(x, x)`.
- Symmetry: from symmetry of `Y.rel`.
- Transitivity: from transitivity of `Y.rel`.

- [ ] **Step 5: Define Setoid and quotient**

```lean
def treePERSetoid (X Y : TreePERObj C) :
    Setoid (TreePERPreMor X Y) := ...

def TreePERMor (X Y : TreePERObj C) :=
  Quotient (treePERSetoid X Y)
```

- [ ] **Step 6: Prove composition respects equivalence**

If `f1 ~ f2` and `g1 ~ g2`, then `g1 . f1 ~ g2 . f2`.
Decompose as `g1 . f1 ~ g1 . f2 ~ g2 . f2`:

- First: `f1(x) rel_Y f2(x)` (from `f1 ~ f2`), so
  `g1(f1(x)) rel_Z g1(f2(x))` (g1 preserves).
- Second: `f2(x) in dom(rel_Y)` (f2 preserves domain),
  so `g1(f2(x)) rel_Z g2(f2(x))` (from `g1 ~ g2`).
- Combine by transitivity of `rel_Z`.

- [ ] **Step 7: Assemble category instance**

```lean
instance treePERCategory :
    Category (TreePERObj C) where
  Hom := TreePERMor
  id X := ...   -- id_T
  comp := ...   -- composition, lifted through quotient
  id_comp := ...
  comp_id := ...
  assoc := ...
```

- [ ] **Step 8: Build, verify, commit**

```bash
git add GebLean/TreePER.lean
git commit -m "feat: PER category on T"
```

---

## Phase B: Limits and Colimits

### Task 3: Finite Products

**Files:**

- Create: `GebLean/TreePERLimits.lean`

- [ ] **Step 1: Define terminal PER**

```lean
def treePERTerminal : TreePERObj C where
  rel := treeAnd_of_isLeaf  -- treeAnd(isLeaf(x), isLeaf(y))
  symm_ := _  -- isLeaf is symmetric in arguments
  trans_ := _  -- trivial: domain is singleton
```

Prove the unique morphism property: for any PER X,
`const(leaf) : (T, rel_X) -> (T, rel_1)` is the
unique morphism.

- [ ] **Step 2: Define product PER**

```lean
def treePERProd
    (X Y : TreePERObj C) : TreePERObj C where
  rel := -- treeAnd(isBranch(t1),
         --   treeAnd(isBranch(t2),
         --     treeAnd(X.rel(left(t1), left(t2)),
         --             Y.rel(right(t1), right(t2)))))
    _
  symm_ := _
  trans_ := _
```

- [ ] **Step 3: Define projections and pairing**

Projections are `treeLeft` and `treeRight`.
Pairing of `f, g` is `branch . <f, g>`.

Prove the product laws (beta and eta).

- [ ] **Step 4: Assemble `HasChosenFiniteProducts`**

- [ ] **Step 5: Define equalizer PER**

```lean
def treePEREqualizer
    {X Y : TreePERObj C}
    (f g : TreePERMor X Y) : TreePERObj C where
  rel := -- treeAnd(X.rel(x1, x2),
         --   treeAnd(Y.rel(f(x1), g(x1)),
         --           Y.rel(f(x2), g(x2))))
    _
  symm_ := _
  trans_ := _
```

Prove the universal property: inclusion = `id_T`
equalizes `f` and `g`, and any equalizing morphism
factors through uniquely.

- [ ] **Step 6: Derive `HasFiniteLimits`**

- [ ] **Step 7: Build, verify, commit**

```bash
git add GebLean/TreePERLimits.lean GebLean.lean
git commit -m "feat: finite limits in PER category"
```

---

### Task 4: Finite Colimits

**Files:**

- Create: `GebLean/TreePERColimits.lean`

- [ ] **Step 1: Define initial PER**

```lean
def treePERInitial : TreePERObj C where
  rel := cfpTerminalFrom _ ≫ p.l ≫ p.beta
    -- constant non-leaf; domain = empty
  symm_ := _
  trans_ := _
```

Prove uniqueness of morphism from initial.

- [ ] **Step 2: Define coproduct PER**

The tag encoding: `inl(x) = branch(leaf, x)`,
`inr(y) = branch(branch(leaf,leaf), y)`.

```lean
def treePERCoprod
    (X Y : TreePERObj C) : TreePERObj C where
  rel := -- treeOr(
         --   treeAnd(isLeaf(left(t1)),
         --     treeAnd(isLeaf(left(t2)),
         --       X.rel(right(t1), right(t2)))),
         --   treeAnd(isBranch(left(t1)),
         --     treeAnd(isBranch(left(t2)),
         --       Y.rel(right(t1), right(t2)))))
    _
  symm_ := _
  trans_ := _
```

- [ ] **Step 3: Define injections and case analysis**

Injections: `inl = branch(leaf, -)`,
`inr = branch(branch(leaf,leaf), -)`.

Case analysis: `[f, g](t) = ite(f(right(t)),
g(right(t)), isLeaf(left(t)))`.

Prove the coproduct laws.

- [ ] **Step 4: Prove disjointness and universality**

- Disjoint: pullback of `inl` and `inr` is initial.
- Universal: coproducts stable under pullback.

- [ ] **Step 5: Define coequalizers of kernel pairs**

Given a kernel pair `(pi1, pi2)` of `f : X -> Y`,
the coequalizer PER coarsens `rel_X` to identify
elements with the same `f`-image:

```lean
def treePERCoeqKernelPair
    {X Y : TreePERObj C}
    (f : TreePERMor X Y) : TreePERObj C where
  rel := -- treeAnd(dom_X(x1), treeAnd(dom_X(x2),
         --   Y.rel(f(x1), f(x2))))
    _
```

- [ ] **Step 6: Build, verify, commit**

```bash
git add GebLean/TreePERColimits.lean GebLean.lean
git commit -m "feat: finite colimits in PER category"
```

---

## Phase C: Exactness and PBTO

### Task 5: Regularity and Exactness

**Files:**

- Create: `GebLean/TreePERExact.lean`

- [ ] **Step 1: Prove image factorization (regularity)**

Every morphism `f : X -> Y` factors as regular epi
followed by mono:

- `e = id_T : (T, rel_X) -> (T, rel_K)`
  where `rel_K` is the kernel-pair PER
- `m = f : (T, rel_K) -> (T, rel_Y)`

Prove `e` is a regular epi and `m` is a mono.

- [ ] **Step 2: Prove regular epis stable under pullback**

- [ ] **Step 3: Prove every equivalence relation is
effective**

Given equivalence relation `E` on `(T, rel_X)`:

- Quotient PER: `rel_Q(x1, x2) = treeAnd(dom_X(x1),
  treeAnd(dom_X(x2), rel_E(branch(x1,x2),
  branch(x1,x2))))`
- Quotient map: `id_T : (T, rel_X) -> (T, rel_Q)`
- Kernel pair of quotient map = `E`

- [ ] **Step 4: Prove extensivity**

Coproducts are disjoint (pullback of `inl` and `inr`
is initial) and universal (stable under pullback).
Together with exactness, this makes the category a
pretopos.

- [ ] **Step 5: Prove distributivity**

`A x (B + C) ~= (A x B) + (A x C)` via:
`branch(a, branch(tag, bc)) <-> branch(tag, branch(a, bc))`

- [ ] **Step 6: Build, verify, commit**

```bash
git add GebLean/TreePERExact.lean GebLean.lean
git commit -m "feat: regularity, exactness, distributivity"
```

---

### Task 6: PBTO Preservation

**Files:**

- Create: `GebLean/TreePERPBTO.lean`

- [ ] **Step 1: Define the PBTO object**

```lean
def treePERBTO : TreePERObj C where
  rel := treeEq
  symm_ := _  -- treeEq(x,y) = treeEq(y,x)
  trans_ := _  -- structural transitivity of equality
```

- [ ] **Step 2: Define leaf and branch morphisms**

- `l = const(leaf) : (T, rel_1) -> (T, treeEq)`
- `beta = branch : (T, rel_{TxT}) -> (T, treeEq)`

Prove these are relation-preserving.

- [ ] **Step 3: Define the fold (existence)**

Given base `f : (T, rel_1) -> (T, rel_X)` and step
`g : (T, rel_{XxX}) -> (T, rel_X)`:

```lean
def treePERElim (f : ...) (g : ...) :
    TreePERMor treePERBTO X :=
  ⟦{ map := elim f.map g.map
     preserves := _ }⟧
```

Prove `preserves` by structural induction:

- Leaf: `f` maps `dom(rel_1)` into `dom(rel_X)`.
- Branch: by induction hypothesis, `phi(t1)` and
  `phi(t2)` are in `dom(rel_X)`, so
  `branch(phi(t1), phi(t2)) in dom(rel_{XxX})`, and
  `g` maps this into `dom(rel_X)`.

- [ ] **Step 4: Prove fold equations**

Fold computation rules:

- Leaf: `phi . l ~ f` (in the PER category)
- Branch: `phi . beta ~ <phi, phi> . g` (modulo
  product encoding)

These follow from `elim_l` and `elim_beta` in the
underlying Lawvere theory.

- [ ] **Step 5: Prove uniqueness**

If `phi` and `psi` both satisfy the fold equations,
show `phi ~ psi` (equivalent modulo `rel_X`):

By structural induction on `t`:

- Leaf: `phi(leaf) rel_X f0(leaf) rel_X psi(leaf)`.
- Branch: by induction, `phi(ti) rel_X psi(ti)`.
  Then `branch(phi(t1), phi(t2)) rel_{XxX}
  branch(psi(t1), psi(t2))`.  Since `g` preserves
  relations: `g0(branch(phi(...))) rel_X
  g0(branch(psi(...)))`.  Combine with fold equations
  by transitivity.

- [ ] **Step 6: Assemble `HasPBTO` instance**

```lean
instance treePERHasPBTO :
    HasPBTO (TreePERObj C) where
  T := treePERBTO
  l := treePERLeaf
  beta := treePERBranch
  elim := treePERElim
  elim_l := _
  elim_beta := _
  elim_uniq := _
```

- [ ] **Step 7: Build, verify, commit**

```bash
git add GebLean/TreePERPBTO.lean GebLean.lean
git commit -m \
  "feat: PBTO preserved in PER category"
```

---

## Phase D: Integration

### Task 7: Module Integration and Testing

**Files:**

- Modify: `GebLean.lean`

- [ ] **Step 1: Add all new imports to `GebLean.lean`**

```lean
import GebLean.TreeLogic
import GebLean.TreePER
import GebLean.TreePERLimits
import GebLean.TreePERColimits
import GebLean.TreePERExact
import GebLean.TreePERPBTO
```

- [ ] **Step 2: Full build and test**

```bash
lake build && lake test
```

- [ ] **Step 3: Update session workstream**

Update `.session/workstreams/exact-completion-pbto.md`
with the results.

- [ ] **Step 4: Commit**

```bash
git add GebLean.lean \
  .session/workstreams/exact-completion-pbto.md
git commit -m "feat: PER completion integrated"
```

---

## Dependencies

```text
Task 1 (tree logic)
  └── Task 2 (PER category)
        ├── Task 3 (limits)
        ├── Task 4 (colimits)
        └── Task 6 (PBTO)
              └── Task 5 (exactness)
                    └── Task 7 (integration)
```

Tasks 3, 4, and 6 are independent of each other and
can proceed in parallel after Task 2.  Task 5 may
depend on Tasks 3 and 4 for the limit/colimit
infrastructure.

---

## Risk Assessment

### High confidence

- Task 1 (tree logic): standard fold constructions
- Task 2 (PER category): well-understood PER semantics
- Task 3 (limits): products from tree encoding, equalizers
  from sub-PERs
- Task 6 (PBTO): clean structural induction, no Lemma B

### Medium confidence

- Task 4 (colimits): coproducts should work; general
  coequalizers may need iteration via fold
- Task 5 (exactness): image factorization works without
  existential quantification; stability of regular epis
  under pullback needs careful verification

### Design notes

- This category is intentionally NOT a topos (no Ackermann
  function, no higher-order arithmetic).  It is a syntactic
  category meant to represent things using only primitive
  recursive computation.
- The target properties (finite limits + colimits, regular,
  exact, distributive, PBTO) make it a "BT-arithmetic
  pretopos" -- the binary-tree analogue of Maietti's
  list-arithmetic pretopos.
- Further categories (including topoi) will be built on top
  of this as a foundation.
