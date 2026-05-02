# Tree Calculus Phase 2 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Formalize tree calculus reduction as a
coalgebraic process on a two-sorted polynomial system,
building the PCA structure, confluence proof,
primitive-recursive fragment, and self-recognizer.

**Architecture:** Two-sorted slice polynomial on
`Over (Fin 2)` separating values (sort 0:
leaf/stem/fork) from computations (sort 1:
embed/app).  Coalgebraic evaluation via the cofree
comonad of a behavior polynomial.  Generic combinator
library for assembling slice polynomials.

**Tech Stack:** Lean 4, mathlib, GebLean polynomial
functor infrastructure (`PolyAlg.lean`, `PolyGSOS.lean`,
`Polynomial.lean`).

**Spec:** `docs/superpowers/specs/2026-03-22-tree-calculus-phase2-design.md`

---

## File Structure

### New files

- **Create:** `GebLean/Utilities/PolyCombinators.lean`
  Generic combinators for slice polynomial construction.
  Imported by `GebLean/Utilities.lean`.

- **Create:** `GebLean/PLang/TreeCalcPoly.lean`
  Value polynomial, computation polynomial, behavior
  polynomial, rose-tree polynomial.  Imports
  `PolyCombinators.lean` and `PLang/Syntax.lean`.

- **Create:** `GebLean/PLang/TreeCalcReduction.lean`
  One-step reduction coalgebra, GSOS rule, triage
  verification.  Imports `TreeCalcPoly.lean`.

- **Create:** `GebLean/PLang/TreeCalcPrograms.lean`
  Derived combinators (K, S, I, etc.), abstraction,
  fixpoints.  Imports `TreeCalcReduction.lean`.

- **Create:** `GebLean/PLang/TreeCalcMeta.lean`
  PCA structure, confluence, primitive-recursive
  fragment, termination, self-recognizer.  Imports
  `TreeCalcPrograms.lean`.

- **Create:** `GebLeanTests/TestTreeCalc.lean`
  Tests for reduction, combinators, and self-recognizer.
  Add `import GebLeanTests.TestTreeCalc` to
  `GebLeanTests.lean`.

### Modified files

- **Modify:** `GebLean/Utilities.lean`
  Add `import GebLean.Utilities.PolyCombinators`.

- **Modify:** `GebLean/PLang.lean`
  Add imports for `TreeCalcPoly`, `TreeCalcReduction`,
  `TreeCalcPrograms`, `TreeCalcMeta`.

- **Modify:** `GebLean.lean`
  Ensure `PLang` is exported (already should be).

---

## Task 1: Polynomial Combinator Library Foundation

**Files:**

- Create: `GebLean/Utilities/PolyCombinators.lean`
- Modify: `GebLean/Utilities.lean`

This task builds the generic infrastructure that all
subsequent tasks depend on.  Each combinator is one
definition with its type signature making the
intent explicit.

- [ ] **Step 1: Create file with module header**

Create `GebLean/Utilities/PolyCombinators.lean` with
imports of `GebLean.PolyAlg` and
`GebLean.Utilities.Slice`.  Add the file to
`GebLean/Utilities.lean`.

Run: `lake build`
Expected: compiles with no errors.

- [ ] **Step 2: Define `polyEmpty`**

The empty polynomial endofunctor on `Over X`: no
positions at any fiber.

```lean
def polyEmpty (X : Type u) : PolyEndo X :=
  fun _ => ccrObjMk
    (fun (_ : Empty) => Over.mk (fun (_ : Empty) => _))
```

This is the identity element for coproducts.  Verify
it compiles.

Run: `lake build`

- [ ] **Step 3: Define `polyFiberReindex`**

Given `f : X -> Y` and `P : PolyEndo X`, produce
`P' : PolyEndo Y` by reindexing fibers.  At fiber
`y : Y`, the positions of `P'` are the disjoint union
of positions of `P` over all `x` in the preimage of
`y`.  Directions are reindexed through `f`.

This is the base change / pullback-pushforward
operation on polynomial functors along a map of base
types.

```lean
def polyFiberReindex {X : Type u} {Y : Type u}
    (f : X -> Y) (P : PolyEndo X) : PolyEndo Y
```

Run: `lake build`

- [ ] **Step 4: Define `polyFiberEmbed`**

Given an injection `f : Fin m -> Fin n` and
`P : PolyEndo (Fin m)`, produce
`P' : PolyEndo (Fin n)` that acts like `P` on fibers
in the image of `f` and is empty on others.

This can be built from `polyFiberReindex` and
`polyEmpty`, or defined directly.

```lean
def polyFiberEmbed {m n : Nat}
    (f : Fin m -> Fin n) (P : PolyEndo (Fin m)) :
    PolyEndo (Fin n)
```

Run: `lake build`

- [ ] **Step 5: Define `polyFiberCoprod`**

Pointwise coproduct of two polynomials on the same
base: at each fiber, take the coproduct of position
types.

```lean
def polyFiberCoprod {X : Type u}
    (P Q : PolyEndo X) : PolyEndo X
```

At fiber `x`, positions are
`polyBetweenIndex P x + polyBetweenIndex Q x`,
directions inherited from whichever summand.

Run: `lake build`

- [ ] **Step 6: Define `polyCrossSortCtor`**

A polynomial on `Over (Fin n)` with a single
constructor at fiber `j` whose `k` directions all
map to fiber `i`.  This is the building block for
cross-sort constructors like `embed`.

```lean
def polyCrossSortCtor {n : Nat}
    (j i : Fin n) (k : Nat) : PolyEndo (Fin n)
```

At fiber `j`: one position with `Fin k` directions,
all mapping to `i`.  At all other fibers: empty.

Run: `lake build`

- [ ] **Step 7: Define `polyNatIndexed`**

A polynomial with `Nat`-indexed positions.  At fiber
`x`, positions are `Nat`, and at position `n` the
directions are `Fin n`, all mapping to a given
target fiber.

```lean
def polyNatIndexed {X : Type u}
    (x : X) (target : X) : PolyEndo X
```

At fiber `x`: positions are `Nat`, directions at
position `n` are `Fin n` mapping to `target`.
At other fibers: empty.

Run: `lake build`

- [ ] **Step 8: Commit**

```bash
git add GebLean/Utilities/PolyCombinators.lean \
  GebLean/Utilities.lean
git commit -m "feat: polynomial combinator library \
  (fiber reindex, embed, coprod, cross-sort, \
  Nat-indexed)"
```

---

## Task 2: Value Polynomial and Value Type

**Files:**

- Create: `GebLean/PLang/TreeCalcPoly.lean`
- Modify: `GebLean/PLang.lean`

- [ ] **Step 1: Create file with module header**

Create `GebLean/PLang/TreeCalcPoly.lean` importing
`GebLean.PolyAlg`, `GebLean.Utilities.PolyCombinators`,
and `GebLean.PLang.Syntax`.  Add to `GebLean/PLang.lean`.

Run: `lake build`

- [ ] **Step 2: Define `polyValue`**

The value polynomial as a `PolyEndo PUnit`:
three-summand coproduct of leaf (0 dirs), stem (1 dir),
fork (2 dirs).

```lean
def polyValue : PolyEndo PUnit.{u + 1}
```

Build as a coproduct:
`polyTranslate (overTerminal PUnit) (polyTranslate
  (polyBetweenId PUnit) (polyProd PUnit))`.
Or define directly via `ccrObjMk` with `Fin 3`
positions and `Empty / Unit / (PUnit + PUnit)`
directions.

Run: `lake build`

- [ ] **Step 3: Define `Value` type and constructors**

```lean
abbrev Value : Type u :=
  PolyFix polyValue PUnit.unit

def Value.leaf : Value := ...
def Value.stem (x : Value) : Value := ...
def Value.fork (l r : Value) : Value := ...
```

Construct using `polyFixStr` with the appropriate
injections into the coproduct.

Run: `lake build`

- [ ] **Step 4: Define `Value.fold`**

The catamorphism (universal property of the initial
algebra):

```lean
def Value.fold {A : Type u}
    (onLeaf : A) (onStem : A -> A)
    (onFork : A -> A -> A)
    (v : Value) : A
```

Built from `polyFixFold polyValue` with an algebra
mapping the three summands.

Run: `lake build`

- [ ] **Step 5: Test value constructors**

Add tests in `GebLeanTests/TestTreeCalc.lean`:

```lean
#guard Value.leaf.fold 0 (· + 1) (· + · + 1) == 0
#guard (Value.stem Value.leaf).fold 0
  (· + 1) (· + · + 1) == 1
#guard (Value.fork Value.leaf Value.leaf).fold 0
  (· + 1) (· + · + 1) == 1
```

Run: `lake build && lake test`

- [ ] **Step 6: Commit**

```bash
git add GebLean/PLang/TreeCalcPoly.lean \
  GebLean/PLang.lean GebLeanTests/TestTreeCalc.lean
git commit -m "feat: value polynomial and Value type \
  with leaf/stem/fork constructors and fold"
```

---

## Task 3: Rose-Tree Polynomial and Isomorphism

**Files:**

- Modify: `GebLean/Utilities/PolyCombinators.lean`
  or `GebLean/PLang/TreeCalcPoly.lean`

- [ ] **Step 1: Define `polyRoseTree`**

```lean
def polyRoseTree (A : Over X) : PolyEndo X :=
  fun x => ccrObjMk
    (fun (p : { a : A.left // A.hom a = x } ×
              Nat) =>
      Over.mk (fun (_ : Fin p.2) => x))
```

Positions at fiber `x`: pairs `(label, n)`.
Directions at position `(a, n)`: `Fin n`, all
mapping to `x`.

Run: `lake build`

- [ ] **Step 2: Define the forward map (binary to rose)**

Using `polyFixFold` on `polyTranslate A (polyProd X)`,
fold a labeled binary tree into a rose tree.  The fold
decomposes the left spine: `leaf(a)` maps to `(a, [])`,
`node(t1, t2)` maps to `(a, cs ++ [t2])` where
`(a, cs) = forward(t1)`.

```lean
def binaryToRose (A : Over X) :
    PolyFix (polyTranslate A (polyProd X)) ⟶
    PolyFix (polyRoseTree A)
```

Run: `lake build`

- [ ] **Step 3: Define the backward map (rose to binary)**

Fold a rose tree into a binary tree: `(a, [])` maps to
`leaf(a)`, `(a, [c1, ..., cn])` maps to
`foldl node (leaf(a)) [c1, ..., cn]`.

```lean
def roseToBinary (A : Over X) :
    PolyFix (polyRoseTree A) ⟶
    PolyFix (polyTranslate A (polyProd X))
```

Run: `lake build`

- [ ] **Step 4: Prove round-trip identities**

```lean
theorem binaryRoseRoundTrip (A : Over X) (t : ...) :
    roseToBinary A (binaryToRose A t) = t

theorem roseBinaryRoundTrip (A : Over X) (t : ...) :
    binaryToRose A (roseToBinary A t) = t
```

The first uses uniqueness of fold
(`polyFixFoldUnique_at`).  The second uses induction
on the rose tree.

Run: `lake build`

- [ ] **Step 5: Commit**

```bash
git add GebLean/Utilities/PolyCombinators.lean \
  GebLean/PLang/TreeCalcPoly.lean
git commit -m "feat: rose-tree polynomial and \
  binary <-> rose-tree isomorphism"
```

---

## Task 4: Two-Sorted Computation Polynomial

**Files:**

- Modify: `GebLean/PLang/TreeCalcPoly.lean`

- [ ] **Step 1: Define `polyComputation`**

Assemble the two-sorted polynomial on
`Over (Fin 2)` using the combinators from Task 1:

```lean
def polyComputation : PolyEndo (Fin 2) :=
  polyFiberCoprod
    (polyFiberEmbed
      (fun _ => (0 : Fin 2)) polyValue)
    (polyFiberCoprod
      (polyCrossSortCtor 1 0 1)
      (polyNatIndexed 1 1))
```

Note: `polyFiberEmbed` takes a map from the source
base (`PUnit`) to the target base (`Fin 2`).  Here
`fun _ => 0` embeds the single-sorted value polynomial
into fiber 0 of the two-sorted system.

Fiber 0: value polynomial (leaf/stem/fork).
Fiber 1: embed (1 dir -> sort 0) + app(n) (Fin n
dirs -> sort 1).

Verify the position and direction types match the
spec.

Run: `lake build`

- [ ] **Step 2: Define `CompTree` and constructors**

```lean
abbrev CompTree : Type u :=
  PolyFix polyComputation (1 : Fin 2)

def CompTree.embed (v : Value) : CompTree := ...
def CompTree.app (children : List CompTree) :
    CompTree := ...
```

The `app` constructor packs a `List CompTree` into
the Nat-indexed position: `children.length` as the
position, list indexing as the direction function.

Run: `lake build`

- [ ] **Step 3: Verify fiber-0 equivalence and
  establish canonical Value**

Establish that `PolyFix polyComputation (0 : Fin 2)`
is equivalent to `PolyFix polyValue PUnit.unit`.
This follows from the fiber-embedding combinator
preserving the polynomial structure at fiber 0.

```lean
def valueEquiv :
    PolyFix polyComputation (0 : Fin 2) ≃
    PolyFix polyValue PUnit.unit
```

After proving this, redefine `Value` as an
abbreviation for the two-sorted version:

```lean
abbrev Value : Type u :=
  PolyFix polyComputation (0 : Fin 2)
```

All subsequent tasks (5-11) use this two-sorted
`Value`.  The single-sorted `PolyFix polyValue`
serves as the construction tool and reference for
the equivalence.  The constructors `Value.leaf`,
`Value.stem`, `Value.fork`, and `Value.fold`
are redefined or transported through `valueEquiv`.

Run: `lake build`

- [ ] **Step 4: Test computation constructors**

```lean
#guard (CompTree.embed Value.leaf) matches ...
#guard (CompTree.app [
  CompTree.embed Value.leaf,
  CompTree.embed Value.leaf]) matches ...
```

Run: `lake build && lake test`

- [ ] **Step 5: Commit**

```bash
git commit -m "feat: two-sorted computation \
  polynomial with CompTree type and constructors"
```

---

## Task 5: Behavior Polynomial and Reduction Coalgebra

**Files:**

- Modify: `GebLean/PLang/TreeCalcPoly.lean` (for Q)
- Create: `GebLean/PLang/TreeCalcReduction.lean`

- [ ] **Step 1: Define behavior polynomial `Q`**

```lean
def polyBehavior : PolyEndo (Fin 2)
```

Fiber 0: identity polynomial (one position, one
direction mapping to 0).
Fiber 1: value-shaped observation (leaf: 0 dirs,
stem: 1 dir -> 1, fork: 2 dirs -> 1).

Run: `lake build`

- [ ] **Step 2: Create TreeCalcReduction.lean with
  module header**

Import `TreeCalcPoly`.  Add to `PLang.lean`.

Run: `lake build`

- [ ] **Step 3: Define helper: child-count dispatch**

Given a `Value`, dispatch on its constructor
(leaf/stem/fork) to determine the reduction rule.
This is `Value.fold` specialized to return a sum
type or match result.

```lean
def Value.cases {A : Type u}
    (onLeaf : A)
    (onStem : Value -> A)
    (onFork : Value -> Value -> A)
    (v : Value) : A
```

Run: `lake build`

- [ ] **Step 4: Define partial-application rules**

When an application has fewer arguments than the
head value needs:

```lean
def partialApp (head : Value)
    (args : List CompTree) :
    Option CompTree
```

- `app([leaf, x1])` -> `embed(stem(x1'))` where
  `x1'` is the value of `x1` (requires `x1` to be
  an embedded value).
- `app([stem(a), x1])` -> `embed(fork(a, x1'))`.

Returns `none` if the application is not a partial
application (enough arguments for a rule to fire).

Run: `lake build`

- [ ] **Step 5: Define one-step triage reduction**

The one-step function on application nodes:

```lean
def triageStep (head : Value)
    (args : List CompTree) :
    CompTree
```

Dispatches on `head`:

- leaf, 2+ args: K rule (return second arg)
- stem(a), 2+ args: S rule (distribute)
- fork(w, x), 1+ args: triage on first arg's
  structure (rules 3a/3b/3c)

Remaining arguments are wrapped in further `app`
nodes.

Run: `lake build`

- [ ] **Step 6: Define the step coalgebra**

```lean
def stepCoalg :
    PolyCoalg polyBehavior
```

The carrier at fiber 1 is `CompTree`.  The
structure map examines the root:

- `embed(v)`: observe `v`'s structure
  (leaf/stem/fork) with sub-computations that are
  themselves `embed`-wrapped sub-values.
- `app(children)`: evaluate the head, apply
  `triageStep`, observe the result.

The carrier at fiber 0 is `Value` with the identity
coalgebra (values are already observed).

Run: `lake build`

- [ ] **Step 7: Define full evaluation anamorphism**

```lean
def eval : CompTree -> PolyCofix polyBehavior 1 :=
  polyCofixUnfold polyBehavior stepCoalg
```

(Applied at fiber 1.)

Run: `lake build`

- [ ] **Step 8: Define multi-step reduction**

Define the reflexive-transitive closure of one-step
reduction as a relation on `CompTree`:

```lean
def reduces (t1 t2 : CompTree) : Prop := ...
```

Also define `IsFinite` on `PolyCofix polyBehavior`
elements, characterizing elements whose approximation
chain stabilizes (finite computation traces):

```lean
def IsFinite : PolyCofix polyBehavior 1 -> Prop := ...
```

Run: `lake build`

- [ ] **Step 9: Test reduction on ground terms**

```lean
-- K rule: app([leaf, x, y]) reduces to x
-- (via partial app: app([leaf, x]) -> stem(x),
--  then app([stem(x), y]) -> fork(x, y),
--  then... )
-- Test the 5 rules individually
```

Run: `lake build && lake test`

- [ ] **Step 10: Commit**

```bash
git commit -m "feat: behavior polynomial and \
  one-step triage reduction coalgebra"
```

---

## Task 6: Derived Combinators

**Files:**

- Create: `GebLean/PLang/TreeCalcPrograms.lean`

- [ ] **Step 1: Create file with module header**

Import `TreeCalcReduction`.  Add to `PLang.lean`.

Run: `lake build`

- [ ] **Step 2: Define the standard combinators**

Following `docs/tree-calculus.md` "Derived
Combinators" section:

```lean
def tcK : Value := Value.fork Value.leaf Value.leaf
def tcI : Value :=
  Value.fork
    (Value.fork Value.leaf Value.leaf)
    (Value.fork Value.leaf Value.leaf
      |>.stem)  -- adjust to match △(△△)(△△△)
def tcD : Value := ...
def tcS : Value := ...
```

Each combinator is a `Value` term defined by its
tree structure from the book/specification.

Run: `lake build`

- [ ] **Step 3: Define boolean and arithmetic
  combinators**

```lean
def tcTrue : Value := tcK
def tcFalse : Value := ...  -- K I
def tcSuccessor : Value := tcK  -- successor = K
def tcIsZero : Value := ...
def tcPredecessor : Value := ...
```

Run: `lake build`

- [ ] **Step 4: Define query combinators**

```lean
def tcQuery (is0 is1 is2 : Value) : Value := ...
def tcIsLeaf : Value := tcQuery tcK tcFalse tcFalse
def tcIsStem : Value := ...
def tcIsFork : Value := ...
def tcTriage (f0 f1 f2 : Value) : Value := ...
```

Run: `lake build`

- [ ] **Step 5: Define bracket and star abstraction**

Functions that take a variable index and a `Value`
term and produce the abstracted `Value`:

```lean
def bracketAbstract (x : Nat) : Value -> Value
def starAbstract (x : Nat) : Value -> Value
```

Following the definitions in `docs/tree-calculus.md`
"Abstraction" section.

Run: `lake build`

- [ ] **Step 6: Define fixpoint combinators**

```lean
def tcSelfApply : Value := ...  -- d{I} I
def tcZ (f : Value) : Value := ...
def tcSwap (f : Value) : Value := ...
def tcY2 (f : Value) : Value := ...
```

Run: `lake build`

- [ ] **Step 7: Test combinator reductions**

Verify reduction behavior:

```lean
-- K x y reduces to x
-- I x reduces to x
-- S x y z reduces to x z (y z)
-- isLeaf leaf reduces to true
-- isLeaf (stem x) reduces to false
```

Run: `lake build && lake test`

- [ ] **Step 8: Commit**

```bash
git commit -m "feat: derived tree calculus \
  combinators, abstraction, and fixpoints"
```

---

## Task 7: PCA Structure

**Files:**

- Create: `GebLean/PLang/TreeCalcMeta.lean`

- [ ] **Step 1: Create file with module header**

Import `TreeCalcPrograms`.  Add to `PLang.lean`.

Run: `lake build`

- [ ] **Step 2: Define partial application**

A partial application function that represents
applying one value to another via the reduction
coalgebra:

```lean
def Value.papp (f x : Value) : CompTree :=
  CompTree.app [CompTree.embed f, CompTree.embed x]
```

Run: `lake build`

- [ ] **Step 3: Define the PCA structure**

Following Bauer's PCA formalization as reference,
define the PCA on `Value`:

```lean
structure TreeCalcPCA where
  app : Value -> Value -> CompTree
  k : Value
  s : Value
  k_axiom : forall x y,
    reduces (app (app k x) y) (embed x)
  s_axiom : forall x y z,
    reduces (app (app (app s x) y) z)
      (app (app x z) (app y z))
```

The exact formulation depends on how `reduces`
(multi-step reduction) is defined -- either as a
proposition on `CompTree` or via the coalgebra.

Run: `lake build`

- [ ] **Step 4: Prove K axiom**

Show `K x y` reduces to `x`.  This follows from
the definition of `triageStep` for the leaf/K case.

Run: `lake build`

- [ ] **Step 5: Prove S axiom**

Show `S x y z` reduces to `x z (y z)`.  This
follows from the stem/S case of `triageStep`.

Run: `lake build`

- [ ] **Step 6: Construct the PCA instance**

```lean
def treeCalcPCA : TreeCalcPCA := { ... }
```

Run: `lake build`

- [ ] **Step 7: Commit**

```bash
git commit -m "feat: partial combinatory algebra \
  structure for tree calculus"
```

---

## Task 8: Confluence

**Files:**

- Modify: `GebLean/PLang/TreeCalcMeta.lean`

- [ ] **Step 1: Define parallel reduction**

A relation where multiple independent redexes can
be contracted simultaneously:

```lean
inductive ParRed : CompTree -> CompTree -> Prop where
  | refl : ParRed t t
  | embed : ParRed (embed v) (embed v)
  | app : (forall i, ParRed (cs i) (cs' i)) ->
      ParRed (app cs) (app cs')
  | step : ... -> ParRed t t'
```

Run: `lake build`

- [ ] **Step 2: Define complete development**

The "complete development" function contracts all
redexes in a term simultaneously.  This is a
function `CompTree -> CompTree` defined by
structural recursion.

```lean
def completeDev : CompTree -> CompTree
```

Run: `lake build`

- [ ] **Step 3: Prove parallel reduction to
  complete development**

Show that any term parallel-reduces to its complete
development:

```lean
theorem parRed_to_completeDev (t : CompTree) :
    ParRed t (completeDev t)
```

Run: `lake build`

- [ ] **Step 4: Prove complete development absorbs
  parallel reduction**

Show that if `t` parallel-reduces to `u`, then
`completeDev u` parallel-reduces from
`completeDev t`:

```lean
theorem completeDev_mono :
    ParRed t u ->
    ParRed (completeDev t) (completeDev u)
```

Run: `lake build`

- [ ] **Step 5: Assemble the diamond property**

Combine Steps 3-4:

```lean
theorem parRed_diamond :
    ParRed t u -> ParRed t v ->
    Sigma (fun w => ParRed u w × ParRed v w)
```

Note: uses `Sigma` and product (`×`) instead of
`Exists` and `And` to stay constructive (no
`Classical.choice` needed to extract the witness).

Run: `lake build`

- [ ] **Step 6: Prove confluence**

```lean
theorem confluence :
    ReflTransClosure ParRed t u ->
    ReflTransClosure ParRed t v ->
    Sigma (fun w =>
      ReflTransClosure ParRed u w ×
      ReflTransClosure ParRed v w)
```

Standard: diamond property of parallel reduction
implies confluence of single-step reduction, since
single-step is contained in parallel which is
contained in multi-step.

Run: `lake build`

- [ ] **Step 7: Commit**

```bash
git commit -m "feat: confluence of tree calculus \
  reduction via parallel reduction diamond property"
```

---

## Task 9: GSOS Rule and Distributive Law

**Files:**

- Modify: `GebLean/PLang/TreeCalcReduction.lean`

This task is contingent on Open Question 1 from the
spec (whether the GSOS format accommodates the
two-level triage observation).  If the standard format
is insufficient, this task defines the coalgebra
directly and defers the GSOS encoding.

- [ ] **Step 1: Define the GSOS rule**

Add `import GebLean.PolyGSOS` to
`TreeCalcReduction.lean` (needed for `PolyGSOSRule`
and related definitions).

```lean
def triageGSOS :
    PolyGSOSRule polyComputation polyBehavior
```

The rule encodes the triage reduction as a
polynomial morphism
`polyComputation . (Id * polyBehavior)
  -> polyBehavior . T_polyComputation`.

Run: `lake build`

- [ ] **Step 2: Verify agreement with direct
  reduction**

Show that the GSOS fold (catamorphism on cofree
comonad elements) reproduces the same reduction
as `triageStep`:

```lean
theorem gsos_agrees_with_step : ...
```

Run: `lake build`

- [ ] **Step 3: Extract the distributive law**

```lean
def triageDistLaw :=
  polyGSOSDistributiveLaw
    polyComputation polyBehavior triageGSOS
```

This is a single definition -- all four coherence
axioms are proved by the GSOS machinery.

Run: `lake build`

- [ ] **Step 4: Extract the operational monad**

```lean
def triageOpMonad :=
  polyGSOSOperationalMonad
    polyComputation polyBehavior triageGSOS
```

Run: `lake build`

- [ ] **Step 5: Commit**

```bash
git commit -m "feat: GSOS rule for triage \
  reduction with distributive law and \
  operational monad"
```

---

## Task 10: Primitive-Recursive Fragment

**Files:**

- Modify: `GebLean/PLang/TreeCalcMeta.lean`

- [ ] **Step 1: Define the syntactic criterion**

A decidable predicate on `Value` terms that
identifies the primitive-recursive fragment.  The
criterion excludes terms containing the `omega_2`
/ `self_apply` pattern (general fixpoint
combinators) while allowing:

- Leaf, stem, fork constructors
- Triage (case analysis)
- Fold (primitive recursion over trees, implemented
  via bounded recursion patterns)

```lean
def isPrimRec : Value -> Bool
```

The exact criterion will be refined during
implementation.

Run: `lake build`

- [ ] **Step 2: Define the primitive-recursive
  fragment type**

```lean
def PrimRecValue : Type u :=
  { v : Value // isPrimRec v = true }
```

Run: `lake build`

- [ ] **Step 3: Define a recursion measure**

Define a well-founded measure on `PrimRecValue`
terms that decreases with each reduction step.
The measure should reflect that primitive-recursive
terms consume their input structurally (the input
tree shrinks at each recursive call).

```lean
def primRecMeasure : PrimRecValue -> Value -> Nat
```

Run: `lake build`

- [ ] **Step 4: Prove measure decreases**

Show that each triage reduction step on a
primitive-recursive term decreases the measure:

```lean
theorem primRec_measure_decreasing
    (v : PrimRecValue) (x : Value)
    (h : not (isValue (Value.papp v.val x))) :
    primRecMeasure v (stepResult ...) <
      primRecMeasure v x
```

Run: `lake build`

- [ ] **Step 5: Assemble the termination proof**

Combine the measure and its decrease to show
termination:

```lean
theorem primRec_terminates (v : PrimRecValue)
    (x : Value) :
    IsFinite (eval (Value.papp v.val x))
```

The proof uses well-founded recursion on
`primRecMeasure`.

This is the most mathematically involved proof
in Phase 2.

Run: `lake build`

- [ ] **Step 6: Commit**

```bash
git commit -m "feat: primitive-recursive fragment \
  with termination proof"
```

---

## Task 11: Self-Recognizer

**Files:**

- Modify: `GebLean/PLang/TreeCalcMeta.lean`

- [ ] **Step 1: Build the self-recognizer as a
  Value term**

Construct a `Value` term `recognizer` that, when
applied to another `Value` term `v`, reduces to
`tcTrue` if `isPrimRec v = true` and `tcFalse`
otherwise.

The recognizer uses triage to inspect the tree
structure of its argument and check for the absence
of fixpoint combinator patterns.  It is itself
in the primitive-recursive fragment.

```lean
def recognizer : Value := ...
```

Run: `lake build`

- [ ] **Step 2: Prove the recognizer is in the
  fragment**

```lean
theorem recognizer_isPrimRec :
    isPrimRec recognizer = true
```

Run: `lake build`

- [ ] **Step 3: Prove soundness**

```lean
theorem recognizer_sound (v : Value) :
    reduces (Value.papp recognizer v)
      (embed tcTrue) ->
    isPrimRec v = true
```

Run: `lake build`

- [ ] **Step 4: Prove completeness**

```lean
theorem recognizer_complete (v : Value) :
    isPrimRec v = true ->
    reduces (Value.papp recognizer v)
      (embed tcTrue)
```

Run: `lake build`

- [ ] **Step 5: Prove the recognizer terminates**

```lean
theorem recognizer_terminates (v : Value) :
    IsFinite (eval (Value.papp recognizer v))
```

This follows from `recognizer_isPrimRec` and
`primRec_terminates`.

Run: `lake build`

- [ ] **Step 6: Commit**

```bash
git commit -m "feat: self-recognizer for \
  primitive-recursive fragment with correctness \
  proof"
```

---

## Task 12: Final Integration and Tests

**Files:**

- Modify: `GebLeanTests/TestTreeCalc.lean`
- Modify: `GebLean.lean` (if needed)

- [ ] **Step 1: Comprehensive test suite**

Add tests covering:

- Each triage rule individually
- Each derived combinator
- Multi-step reductions (K, S, I applied to various
  arguments)
- The self-recognizer accepting a known
  primitive-recursive term
- The self-recognizer rejecting a term containing
  a fixpoint combinator
- The rose-tree isomorphism on sample trees

Run: `lake build && lake test`

- [ ] **Step 2: Verify full build**

Run: `lake build`
Expected: no warnings, no sorry, no admit.

- [ ] **Step 3: Update session workstream**

Update
`.session/workstreams/termcat-binary-tree-category.md`
to mark Phase 2 tasks as complete and record any
new open questions discovered during implementation.

- [ ] **Step 4: Final commit**

```bash
git commit -m "feat: tree calculus Phase 2 complete \
  -- reduction, PCA, confluence, bootstrapping"
```
