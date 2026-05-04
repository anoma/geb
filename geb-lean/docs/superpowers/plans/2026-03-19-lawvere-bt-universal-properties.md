# Lawvere BT Universal Properties Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended)
> or superpowers:executing-plans to implement this plan
> task-by-task.  Steps use checkbox (`- [ ]`) syntax
> for tracking.

**Goal:** Complete the Lawvere theory of binary trees
with the full universal property, Category instance,
HasFiniteProducts, and HasPBTO.

**Architecture:** Build on the existing polynomial
BTMor1 infrastructure in LawvereBT.lean.  Use
polyFixFold for semantic operations and
polyFixFoldUnique for proofs.  Define proof schemes
(induction principles) for BTMor1 that mirror the
computation schemes, providing induction steps without
explicit recursion.

**Tech Stack:** Lean 4, mathlib CategoryTheory,
GebLean polynomial infrastructure (PolyAlg,
PolyUMorph, PolyAlgUMorph)

---

## Background

LawvereBT.lean currently has:

- BT (binary tree type via PolyFreeM)
- BTMor1 = PolyFix btMorPoly (morphisms n -> 1)
- BTMorN n m = Fin m -> BTMor1 n (morphisms n -> m)
- btFold : BTMorN n 1 -> BTMorN 2 1 -> BTMorN (n+1) 1
  (simple universal property with X = 1)
- HasNNO and HasPBTO classes
- interp, rename, subst via polyFixFold

Analysis: the simple fold (X = 1) is
NOT sufficient to derive the full universal property
(arbitrary X = m) within the Lawvere theory morphisms,
because mutual recursion for binary trees requires
access to subtree structure (paramorphisms), which
catamorphisms alone cannot provide.  The full universal
property must be implemented SEMANTICALLY using the
polynomial fold infrastructure, not composed from the
X = 1 syntactic fold.

---

### Task 1: btFoldFull (full simple universal property)

**Files:**

- Modify: `GebLean/LawvereBT.lean`

**Goal:** Define btFoldFull : BTMorN n m ->
BTMorN (m + m) m -> BTMorN (n + 1) m using
polyFixFoldAtWithProof with an m-tuple carrier.

The carrier stores (N -> BT) -> (Fin m -> BT):
a function from a full context to an m-tuple of BT
values.  This generalizes the interp carrier from
producing a single BT to producing m values.

- [x] **Step 1: Define btFoldFullCarrier** (done)
- [x] **Step 2: Define btFoldFull algebra** (done)
- [x] **Step 3: Define btFoldFull** (done)
  Implemented directly using `BT.fold` with carrier
  `Fin m → BT.{0}`.
- [x] **Step 4: Update btFold** (done)
  `btFold` defined independently using
  `BTMor1.fold`.

---

### Task 2: Enhanced btFold (g with context access)

**Files:**

- Modify: `GebLean/LawvereBT.lean`

**Goal:** Define btFoldEnhanced where g has access to
the parameter A:
  f : BTMorN n m,
  g : BTMorN (n + m + m) m,
  result : BTMorN (n + 1) m

Derived from btFoldFull by folding into T^(n + m)
(tracking both context and result), then projecting.

- [x] **Step 1: Define btFoldEnhanced** (done)
- [x] **Step 2: Build and verify** (done)

---

### Task 3: Category instance + proof schemes

**Files:**

- Modify: `GebLean/LawvereBT.lean`
- Modify: `GebLean/PolyAlg.lean` (Layer 1 lemmas)
- Modify: `GebLean/PolyAlgUMorph.lean` (Layer 2)

**Goal:** Define the Lawvere theory as a Category.

**Architecture (established):**

Induction principles (all completed):

- `PolyFix.ind` (PolyAlg.lean): general, Sort-valued
- `PolyFixCoprod.ind` (PolyAlgUMorph.lean): per
  component step for coproduct polynomials
- `BTMor1.ind` (LawvereBT.lean): raw coproduct
  interface for btMorPoly

Round-trip lemmas (all completed):

- Layer 1: `polyFixStrFamily_mk`,
  `polyFixChildAt_rfl`, `polyFixChildAt_homMk`
- Layer 2: `polyFixCoprodStr_inj`,
  `polyFixCoprodStr_inj_child`
- Layer 3: `btMorInject_eq`

Definitions (all completed):

- `rename` and `subst` via `BTMor1.ind` with
  motive parameterized by renaming/substitution
- Constructors via `btMorInject`

**Proof technique for subst_id/subst_comp:**

Use the factoring-out-lemmas technique from
CLAUDE.md.  Write each intermediate equality step
as a named `have` or separate lemma, each provable
by `rfl` (or a single named lemma application).
Never let the elaborator see anything bigger than
one step at a time.  Do not use tactics that
attempt to reduce large terms (no `simp` on huge
goals, no `split_ifs` through deep layers).  Each
layer's lemmas provide the building blocks;
compose them step by step.

The existing round-trip lemmas give:

- `btMorInject_eq`: named constructor = PolyFix.mk
  with polyFixChildAt-wrapped children
- `polyFixCoprodStr_inj_child`: child extraction
  through injection = component child extraction
- `polyFixChildAt_homMk`: child extraction from
  Over.homMk = rfl

Composing these step by step should give: for each
constructor, `subst (constructor args) proj =
constructor args`.

#### Subtask 3a: subst_id

- [x] **Step 1: Proj/leaf/branch cases** (done)
  3 of 4 cases proved in the existing code.

- [x] **Step 2: Fold case via rfl chain** (done)
  Proved via `subst_id_fold_case` helper with
  `polyFixCoprodRoundTrip` and transport lemmas.

#### Subtask 3b: subst_comp

- [x] **Step 3: Prove subst_comp** (done)
  Proved via `subst_comp_fold_case` and
  `fold_subst_eq` helpers.

#### Subtask 3c: Category instance

- [x] **Step 4: Prove category laws** (done)
  - `BTMor1.subst_proj`: `rfl`
  - `BTMorN.id_comp`: from `subst_id`
  - `BTMorN.comp_id`: from `subst_proj`
  - `BTMorN.comp_assoc`: from `subst_comp`

- [x] **Step 5: Define LawvereBTCat** (done)
  `LawvereBTCat := ℕ` with `CategoryStruct` and
  `Category` instances.

- [x] **Step 9: Build and verify** (done)

---

### Task 4: HasFiniteProducts + HasPBTO

**Files:**

- Modify: `GebLean/LawvereBT.lean`

**Goal:** Show LawvereBTCat has finite products and a
parameterized binary tree object.

#### Subtask 4a: HasFiniteProducts

- [ ] **Step 1: Define terminal object**
  Terminal = 0.  Unique morphism: BTMorN.terminal.

- [ ] **Step 2: Define binary products**
  Product of n and m is n + m.
  Projections: BTMorN.fst, BTMorN.snd.
  Pairing: BTMorN.pair.
  Prove universal property.

- [ ] **Step 3: HasFiniteProducts instance**

#### Subtask 4b: HasPBTO

- [ ] **Step 4: Define the BTO data**
  T = 1, l = btLeaf, beta = btBranch.

- [ ] **Step 5: Define elim = btFoldFull**

- [ ] **Step 6: Prove computation rules**
  elim_l and elim_beta using the fold algebra's
  computation rules.

- [ ] **Step 7: Prove uniqueness**
  Using polyFixFoldUnique (the fold is the unique
  algebra homomorphism).

- [ ] **Step 8: HasPBTO instance**

- [ ] **Step 9: Full build and tests**
