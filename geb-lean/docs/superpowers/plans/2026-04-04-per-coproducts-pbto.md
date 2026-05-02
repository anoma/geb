# PER Category: Coproducts, PBTO, Decidability

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Complete the decidable PER category (Layer 1)
by adding finite coproducts, proving PBTO preservation,
and establishing that all objects are decidable.

**Architecture:** The decidable PER category has
`rel_bool : rel ≫ isLeafEndo = rel` on all objects,
ensuring Boolean-valued equality.  Coproducts use
tag encoding (`branch(leaf, x)` for left,
`branch(treeFalse, y)` for right).  The PBTO is
`(T, treeEq)` where `treeEq` is structural tree
equality.  No coequalizers are attempted (transitive
closure of decidable relations is not in general
decidable by primitive recursive functions).

**Tech Stack:** Lean 4, `HasPBTO` / `elim`
(`LawvereBT.lean`), `boolAnd` / `isLeafEndo` /
`treeIte` (`TreeLogic.lean`), `TreePERObj` /
`treePERCategory` (`TreePER.lean`), `HasFiniteLimits`
(`TreePERLimits.lean`).

---

## File Structure

- Create: `GebLean/TreePERColimits.lean` -- Initial
  object, binary coproducts, `HasFiniteCoproducts`
- Create: `GebLean/TreePERPBTO.lean` -- PBTO
  preservation (`HasPBTO` instance)
- Modify: `GebLean/TreeLogic.lean` -- Add `treeEq`
  (structural tree equality)
- Modify: `GebLean/TreePERLawvereBT.lean` -- Add
  coproduct + PBTO instances for LawvereBTQuotCat
- Modify: `GebLean.lean` -- Add imports

---

## Task 1: Finite Coproducts

**Files:**

- Create: `GebLean/TreePERColimits.lean`

### Step 1: Initial PER

The initial PER has empty domain:

```text
rel_0(x, y) = treeFalse (constantly false)
```

No element is related to any other.

- [ ] Define `initialPERRel : cfpProd T T ⟶ T` as
  `cfpTerminalFrom (cfpProd T T) ≫ treeFalse`

- [ ] Prove `initialPERRel_bool`, `initialPERRel_symm`,
  `initialPERRel_trans`

- [ ] Define `initialPERObj : TreePERObj`

- [ ] Prove `IsInitial initialPERObj`: for any PER X,
  there exists a unique morphism `initialPERObj ⟶ X`.
  The morphism is `𝟙 T` (or any map — since the
  domain is empty, `map_rel` is vacuously true:
  `boolAnd(treeFalse, anything) = treeFalse`).
  Uniqueness: any two morphisms agree on the empty
  domain (vacuously).

- [ ] Derive `HasInitial`

### Step 2: Binary Coproduct PER

Given PERs X and Y, the coproduct encodes elements
via a tag:

- `inl(x) = branch(leaf, x)` (left injection)
- `inr(y) = branch(treeFalse, y)` (right injection)

The coproduct relation:

```text
rel_{X+Y}(t1, t2) = boolOr(
  boolAnd(boolAnd(isLeafEndo(left(t1)),
                   isLeafEndo(left(t2))),
           X.rel(right(t1), right(t2))),
  boolAnd(boolAnd(isLeafEndo(treeNotEndo(left(t1))),
                   isLeafEndo(treeNotEndo(left(t2)))),
           Y.rel(right(t1), right(t2))))
```

This checks: both tags are leaf (left-tagged) and
the payloads are X-related, OR both tags are non-leaf
(right-tagged) and the payloads are Y-related.

- [ ] Define helper morphisms:
  `tagIsLeft`, `tagIsRight`, `payload` (endomorphisms
  extracting the tag test and payload from a tagged
  tree)

- [ ] Define `coprodPERRel`

- [ ] Prove `coprodPERRel_bool`, `coprodPERRel_symm`,
  `coprodPERRel_quantTransitive`,
  `coprodPERRel_eqTransitive`

- [ ] Define `coprodPERObj : TreePERObj`

### Step 3: Injections

- [ ] Define `coprodPERInlPreMor` with
  `map = cfpLift (cfpTerminalFrom T ≫ ℓ) (𝟙 T) ≫ β`
  (maps `x` to `branch(leaf, x)`)

- [ ] Prove `map_rel` for inl: X-related elements
  map to coproduct-related elements (both left-tagged)

- [ ] Define `coprodPERInrPreMor` similarly with
  `map = cfpLift (cfpTerminalFrom T ≫ treeFalse) (𝟙 T) ≫ β`

- [ ] Prove `map_rel` for inr

- [ ] Lift to `TreePERMor`

### Step 4: Case Analysis (Copairing)

Given `f : X ⟶ Z` and `g : Y ⟶ Z`, the copairing
`[f, g] : X + Y ⟶ Z` maps:

- Left-tagged `branch(leaf, x)` to `f(x)`
- Right-tagged `branch(treeFalse, y)` to `g(y)`

Implementation: `treeIte((f(right(t)), g(right(t))),
isLeafEndo(left(t)))`.

- [ ] Define `coprodPERCopairPreMor`

- [ ] Prove `map_rel`: tagged elements that are
  coproduct-related map to Z-related elements

- [ ] Lift to `TreePERMor` (well-defined on quotient)

### Step 5: Coproduct Laws

- [ ] Beta laws: `inl ≫ [f, g] = f` and
  `inr ≫ [f, g] = g` (in the quotient)

- [ ] Eta/uniqueness: if `h` satisfies
  `inl ≫ h = f` and `inr ≫ h = g`, then `h = [f, g]`
  (in the quotient)

- [ ] Construct `BinaryCofan` + `IsColimit`

- [ ] Derive `HasBinaryCoproducts`

### Step 6: HasFiniteCoproducts

- [ ] Combine `HasInitial` and `HasBinaryCoproducts`
  via mathlib's
  `hasFiniteCoproducts_of_has_binary_and_initial`

### Step 7: Instantiate for LawvereBTQuotCat

- [ ] Add to `TreePERLawvereBT.lean`:
  `lawvereBTQuotCat_treePER_hasFiniteCoproducts`

### Step 8: Build, verify, commit

```bash
lake build && lake test
```

---

## Task 2: treeEq (Structural Tree Equality)

**Files:**

- Modify: `GebLean/TreeLogic.lean`

Define `treeEq : cfpProd T T ⟶ T` returning `leaf`
when two trees are structurally equal, `treeFalse`
otherwise.

- [ ] Define `treeEq` by folding over the first tree
  with the second as parameter, using shallow
  destructors for case analysis on the second:

  ```text
  treeEq(leaf, y) = isLeafEndo(y)
  treeEq(branch(a,b), y) = boolAnd(
    isLeafEndo(treeNotEndo(y)),
    boolAnd(treeEq(a, left(y)),
            treeEq(b, right(y))))
  ```

- [ ] Prove computation rules:
  `treeEq_leaf_leaf`, `treeEq_leaf_branch`,
  `treeEq_branch_leaf`, `treeEq_branch_branch`

- [ ] Prove `treeEq_bool : treeEq ≫ isLeafEndo = treeEq`

- [ ] Prove `treeEq_symm : cfpSwap T T ≫ treeEq = treeEq`

- [ ] Prove `treeEq_refl :
  cfpLift (𝟙 T) (𝟙 T) ≫ treeEq = cfpTerminalFrom T ≫ ℓ`
  (reflexivity: `treeEq(t, t) = leaf` for all t)

- [ ] Prove `EqTransitive treeEq` (transitivity)

---

## Task 3: PBTO Preservation

**Files:**

- Create: `GebLean/TreePERPBTO.lean`

Prove `HasPBTO (TreePERObj C)` with `(T, treeEq)` as
the PBTO.

- [ ] Define `treePERBTO : TreePERObj` with
  `rel = treeEq`

- [ ] Define leaf and branch morphisms:
  `treePERLeaf : terminalPERObj ⟶ treePERBTO` with
  `map = ℓ`
  `treePERBranch : prodPERObj treePERBTO treePERBTO ⟶ treePERBTO`
  with `map = β`

- [ ] Prove `map_rel` for leaf and branch

- [ ] Define the fold:
  `treePERElim f g : prodPERObj A treePERBTO ⟶ X`
  with `map = elim f.map g.map`

- [ ] Prove fold existence (phi is
  relation-preserving): by structural induction on
  the domain, the fold maps `treeEq`-related elements
  to `X.rel`-related elements.  This avoids Lemma B
  because the domain condition (`treeEq(t1, t2) = leaf`
  iff `t1 = t2`) is inductive.

- [ ] Prove fold computation rules (leaf and branch
  cases)

- [ ] Prove fold uniqueness (up to morphism
  equivalence): any two folds agreeing on base and
  step are `X.rel`-equivalent on all inputs.

- [ ] Assemble `HasPBTO (TreePERObj C)` instance

---

## Task 4: Decidability of All Objects

**Files:**

- Create: `GebLean/TreePERDecidable.lean` or add to
  `TreePER.lean`

Prove every object in the decidable PER category is a
decidable object: the diagonal `Δ : X → X × X` is
complemented.

- [ ] Define the complement of the diagonal:
  `relNot : cfpProd T T ⟶ T` as
  `rel ≫ treeNotEndo` (the negation of the relation)

- [ ] Prove `relNot` is Boolean-valued

- [ ] Prove `boolAnd(rel, relNot) = treeFalse`
  (conjunction with complement is false)

- [ ] Prove `boolOr(rel, relNot) = leaf` on the
  domain (disjunction with complement is true) --
  this follows from `rel_bool` (rel is already
  Boolean, so exactly one of rel and relNot is leaf
  at each point)

- [ ] State and prove the decidability condition
  using mathlib's formulation (if one exists) or
  as a direct construction

---

## Task 5: Faithful Functor Preserves Limits

**Files:**

- Modify: `GebLean/TreePERLawvereBT.lean` or new file

- [ ] Prove `interpFunctor` preserves the terminal
  object

- [ ] Prove `interpFunctor` preserves binary products

- [ ] Prove `interpFunctor` preserves equalizers

- [ ] Derive `PreservesFiniteLimits`

- [ ] Similarly for coproducts when available

---

## Dependencies

```text
Task 1 (coproducts)
  ├── Task 3 (PBTO) -- needs prodPERObj from limits
  └── Task 5 (preservation) -- needs coproducts

Task 2 (treeEq) -- independent, needed by Task 3

Task 4 (decidability) -- independent

Task 5 depends on Tasks 1 and 3
```

Tasks 1, 2, and 4 are independent and can proceed
in parallel.  Task 3 depends on Task 2.  Task 5
depends on Tasks 1 and 3.

---

## Risk Assessment

### High confidence

- Task 1 (coproducts): tag encoding is straightforward;
  follows the same pattern as products
- Task 4 (decidability): follows directly from
  `rel_bool`

### Medium confidence

- Task 2 (treeEq): defining structural equality via
  fold requires simultaneous recursion on two trees.
  The fold-with-destructors approach (fold over first
  tree, case-split on second via `isLeafEndo` /
  `treeLeftEndo` / `treeRightEndo`) should work.
  Earlier attempts were blocked; needs careful
  implementation.

### Research frontier

- Task 3 (PBTO): the existence proof (fold preserves
  domain) should work by structural induction.  The
  uniqueness proof requires `treeEq` properties.
  The avoidance of Lemma B is the main architectural
  insight.
- Task 5 (preservation): standard categorical
  construction, but may require significant
  infrastructure for the specific interpretation
  functor.

---

## Design Notes

### Why no coequalizers (Layer 1)

The coequalizer of `f, g : X → Y` quotients Y by the
equivalence relation GENERATED by `f(x) ~ g(x)`.  The
generated relation is the transitive closure of the
one-step relation.  Even if the one-step relation is
decidable (checkable by a morphism `T × T → {leaf,
treeFalse}`), the transitive closure requires unbounded
search through chains of identifications.  Unbounded
search is not primitive recursive (only recursively
enumerable), so the transitive closure's relation
cannot be computed by a `T × T → T` morphism returning
Boolean values.

### The syntax category interpretation

The decidable PER category is the category of types
whose equality is decidable by primitive recursive
tree functions.  An object `(T, rel)` with
`rel_bool` represents a type where membership and
equality are mechanically checkable.  A morphism
`f : X → Y` with equational `map_rel` represents a
function that provably preserves typing.

This is the right notion of "typecheckable syntax":
every type judgment `a : X` (membership in the domain)
and every equality judgment `a = b : X` (relatedness)
can be verified by a primitive recursive computation.

### Layer 2 extension (future)

Dropping `rel_bool` allows relations whose truth value
is an arbitrary tree (a "proof witness").  This is
analogous to:

- Realizability: the tree is a realizer witnessing
  relatedness
- Proof-relevant equality: the tree encodes HOW two
  elements are equal

In this extension, coequalizers exist because the
transitive closure can be represented as a tree-valued
witness (encoding the chain of identifications).
The category becomes regular and exact, gaining
quotient types at the cost of decidability.
