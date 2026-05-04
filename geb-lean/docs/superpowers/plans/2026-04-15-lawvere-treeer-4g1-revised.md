# Lawvere Tree-ER 4g.1 Revised Plan (Tasks 2–17)

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Complete Sub-project 4g.1 after the design revision: define
`TreeMor1` as a new 5-constructor inductive (leaf, branch, proj, comp,
fold), with `TreeERMor1` as the depth-≤-2 subtype.  Build the Lawvere
theory, faithful interp functor, faithful inclusion into
`LawvereBTQuotCat`.

**Architecture:** `TreeMor1 n` is a standard Lean inductive (NOT a
`PolyFix`), so `foldDepth`, `interp`, and all reduction lemmas are
plain structural recursion with `rfl` proofs.  `comp`'s foldDepth is
`max(f.depth, sup g_i.depth)`, ensuring the depth-≤-2 subtype is
closed under all constructors.  Connection to `BTMor1` is via a
translation function `TreeMor1.toBTMor1` mapping `comp` to
`BTMor1.subst`.

**Tech Stack:** Lean 4 + Mathlib.

**Supersedes:** The original plan at `2026-04-15-lawvere-treeer-
subproject-4g1.md`, Tasks 2–17.  Task 1 (BTMor1.foldDepth) from the
original plan is retained as ancillary BT infrastructure (commits
`7c10adae`, `73f6b6bf`, `d634cb9f`).

---

## Context: what's already done

Task 1 of the original plan landed `BTMor1.foldDepth` and four
reduction lemmas in `GebLean/LawvereTreeER.lean`.  This file now
exists with ~152 lines of BT infrastructure.  The revised tasks
below ADD to this file (for the `TreeMor1` inductive + subtypes) and
create two new files (`LawvereTreeERQuot.lean`,
`LawvereTreeERInterp.lean`) following the original plan's module
layout.

---

## Task 2: Define `TreeMor1` inductive + `foldDepth` + interp

**Files:**

* Modify: `GebLean/LawvereTreeER.lean`

- [ ] **Step 1: Add the `TreeMor1` inductive**

Insert after the existing `BTMor1.foldDepth` block, inside
`namespace GebLean`:

```lean
/-- Tree morphism with explicit composition: a 5-constructor
inductive paralleling `BTMor1` but with a `comp` constructor
whose fold-nesting depth is the max (not additive) of its
arguments.  The depth-≤-2 subtype `TreeERMor1` characterizes
the elementary recursive fragment (Leivant 1999). -/
inductive TreeMor1 : ℕ → Type
  | leaf {n : ℕ} : TreeMor1 n
  | branch {n : ℕ} (l r : TreeMor1 n) : TreeMor1 n
  | proj {n : ℕ} (i : Fin n) : TreeMor1 n
  | comp {n k : ℕ} (f : TreeMor1 k)
      (g : Fin k → TreeMor1 n) : TreeMor1 n
  | fold {n : ℕ} (m : ℕ)
      (f : Fin m → TreeMor1 n)
      (g : Fin m → TreeMor1 (m + m))
      (tree : TreeMor1 n)
      (j : Fin m) : TreeMor1 n
```

- [ ] **Step 2: Add `TreeMor1.foldDepth`**

```lean
/-- Maximum nesting depth of `fold` constructors in a
`TreeMor1` term.  `comp` takes the max of its arguments
(not additive), ensuring the depth-≤-2 subtype is closed
under composition. -/
def TreeMor1.foldDepth : {n : ℕ} → TreeMor1 n → ℕ
  | _, .leaf => 0
  | _, .branch l r => max l.foldDepth r.foldDepth
  | _, .proj _ => 0
  | _, .comp f g =>
      max f.foldDepth
        ((Finset.univ : Finset (Fin _)).sup
          (fun i => (g i).foldDepth))
  | _, .fold _ f g tree _ =>
      1 + max (max
        ((Finset.univ : Finset (Fin _)).sup
          (fun i => (f i).foldDepth))
        ((Finset.univ : Finset (Fin _)).sup
          (fun i => (g i).foldDepth)))
        tree.foldDepth
```

- [ ] **Step 3: Add `@[simp]` reduction lemmas (all `rfl`)**

```lean
@[simp] theorem TreeMor1.foldDepth_leaf {n : ℕ} :
    (@TreeMor1.leaf n).foldDepth = 0 := rfl

@[simp] theorem TreeMor1.foldDepth_branch {n : ℕ}
    (l r : TreeMor1 n) :
    (TreeMor1.branch l r).foldDepth =
      max l.foldDepth r.foldDepth := rfl

@[simp] theorem TreeMor1.foldDepth_proj {n : ℕ}
    (i : Fin n) :
    (TreeMor1.proj i).foldDepth = 0 := rfl

@[simp] theorem TreeMor1.foldDepth_comp {n k : ℕ}
    (f : TreeMor1 k) (g : Fin k → TreeMor1 n) :
    (TreeMor1.comp f g).foldDepth =
      max f.foldDepth
        ((Finset.univ : Finset (Fin k)).sup
          (fun i => (g i).foldDepth)) := rfl

@[simp] theorem TreeMor1.foldDepth_fold {n m : ℕ}
    (f : Fin m → TreeMor1 n)
    (g : Fin m → TreeMor1 (m + m))
    (tree : TreeMor1 n) (j : Fin m) :
    (TreeMor1.fold m f g tree j).foldDepth =
      1 + max (max
        ((Finset.univ : Finset (Fin m)).sup
          (fun i => (f i).foldDepth))
        ((Finset.univ : Finset (Fin m)).sup
          (fun i => (g i).foldDepth)))
        tree.foldDepth := rfl
```

- [ ] **Step 4: Add `TreeMor1.interp`**

```lean
/-- Standard interpretation of a `TreeMor1 n` as a function
`(Fin n → BT) → BT`. -/
def TreeMor1.interp :
    {n : ℕ} → TreeMor1 n → (Fin n → BT.{u}) → BT.{u}
  | _, .leaf, _ => BT.leaf
  | _, .branch l r, ctx =>
      BT.node (l.interp ctx) (r.interp ctx)
  | _, .proj i, ctx => ctx i
  | _, .comp f g, ctx =>
      f.interp (fun i => (g i).interp ctx)
  | _, .fold _ f g tree j, ctx =>
      (tree.interp ctx).fold
        (fun _ => (Fin.cons · (Fin.cons · ·)))
        (fun i => (f i).interp ctx)
        (fun left right => fun i =>
          (g i).interp (Fin.append left right))
        j
```

Note: the `fold` case's interpretation must match `BTMor1.interpU`'s
fold semantics exactly.  The tree is folded using `BT.fold` with
carrier `Fin m → BT`; at each leaf the base children `f` produce
the initial values; at each node the step children `g` combine left
and right results.  Use the BT fold infrastructure from
`GebLean/LawvereBT.lean` (`BT.fold` or `BTMor1.interpU_fold`
pattern).

If `BT.fold` is not directly available as a function on `BT`
values (it may be a `BTMor1`-level concept only), interpret the
fold case via `TreeMor1.toBTMor1` + `BTMor1.interpU` instead:

```lean
  | _, .fold m f g tree j, ctx =>
      (BTMor1.fold m
        (fun i => (f i).toBTMor1)
        (fun i => (g i).toBTMor1)
        tree.toBTMor1 j).interpU ctx
```

This requires `TreeMor1.toBTMor1` (Step 5) to be defined first.
Reorder Steps 4 and 5 if needed: define `toBTMor1` first, then
define `interp` via it.

- [ ] **Step 5: Add `TreeMor1.toBTMor1`**

```lean
/-- Translate a `TreeMor1` to `BTMor1`, mapping `comp` to
`BTMor1.subst`. -/
def TreeMor1.toBTMor1 : {n : ℕ} → TreeMor1 n → BTMor1 n
  | _, .leaf => BTMor1.leaf
  | _, .branch l r =>
      BTMor1.branch l.toBTMor1 r.toBTMor1
  | _, .proj i => BTMor1.proj i
  | _, .comp f g =>
      f.toBTMor1.subst (fun i => (g i).toBTMor1)
  | _, .fold m f g tree j =>
      BTMor1.fold m
        (fun i => (f i).toBTMor1)
        (fun i => (g i).toBTMor1)
        tree.toBTMor1 j
```

- [ ] **Step 6: Define `TreeMor1.interp` via `toBTMor1`**

If the direct interp from Step 4 is hard (because `BT.fold` isn't
available at the value level), use:

```lean
def TreeMor1.interp {n : ℕ}
    (t : TreeMor1 n) (ctx : Fin n → BT.{u}) : BT.{u} :=
  t.toBTMor1.interpU ctx
```

This is the cleanest approach: it reuses all of `BTMor1`'s existing
computation infrastructure and guarantees interpretation agreement
with `BTMor1.interpU` by definition.

- [ ] **Step 7: Add `@[simp]` interpretation reduction lemmas**

```lean
@[simp] theorem TreeMor1.interp_leaf {n : ℕ}
    (ctx : Fin n → BT.{u}) :
    TreeMor1.leaf.interp ctx = BT.leaf := by
  simp [TreeMor1.interp, TreeMor1.toBTMor1]

@[simp] theorem TreeMor1.interp_branch {n : ℕ}
    (l r : TreeMor1 n) (ctx : Fin n → BT.{u}) :
    (TreeMor1.branch l r).interp ctx =
      BT.node (l.interp ctx) (r.interp ctx) := by
  simp [TreeMor1.interp, TreeMor1.toBTMor1]

@[simp] theorem TreeMor1.interp_proj {n : ℕ}
    (i : Fin n) (ctx : Fin n → BT.{u}) :
    (TreeMor1.proj i).interp ctx = ctx i := by
  simp [TreeMor1.interp, TreeMor1.toBTMor1]

@[simp] theorem TreeMor1.interp_comp {n k : ℕ}
    (f : TreeMor1 k) (g : Fin k → TreeMor1 n)
    (ctx : Fin n → BT.{u}) :
    (TreeMor1.comp f g).interp ctx =
      f.interp (fun i => (g i).interp ctx) := by
  simp [TreeMor1.interp, TreeMor1.toBTMor1]
```

The fold case's reduction lemma may need more work depending on
how `BTMor1.interpU_fold` unfolds.  Add it if tractable; defer
if not (it can be proved later when needed).

- [ ] **Step 8: Build and verify**

Run: `lake build GebLean.LawvereTreeER`
Expected: PASS, no warnings, no `sorry`.

- [ ] **Step 9: Commit**

```bash
git add GebLean/LawvereTreeER.lean
git commit -m "Define TreeMor1 inductive with foldDepth, interp, toBTMor1"
```

---

## Task 3: Subtype aliases + widening lifts + smart constructors

**Files:**

* Modify: `GebLean/LawvereTreeER.lean`

- [ ] **Step 1: Add subtype aliases**

```lean
def TreeERMor1_0 (n : ℕ) : Type :=
  { t : TreeMor1 n // t.foldDepth = 0 }

def TreeERMor1_1 (n : ℕ) : Type :=
  { t : TreeMor1 n // t.foldDepth ≤ 1 }

def TreeERMor1 (n : ℕ) : Type :=
  { t : TreeMor1 n // t.foldDepth ≤ 2 }
```

- [ ] **Step 2: Add widening lifts**

```lean
def TreeERMor1_0.toDepth1 {n : ℕ}
    (t : TreeERMor1_0 n) : TreeERMor1_1 n :=
  ⟨t.val, by have := t.property; omega⟩

def TreeERMor1_1.toDepth2 {n : ℕ}
    (t : TreeERMor1_1 n) : TreeERMor1 n :=
  ⟨t.val, by have := t.property; omega⟩

def TreeERMor1_0.toDepth2 {n : ℕ}
    (t : TreeERMor1_0 n) : TreeERMor1 n :=
  t.toDepth1.toDepth2
```

- [ ] **Step 3: Add depth-0 smart constructors**

```lean
def TreeERMor1_0.leaf {n : ℕ} : TreeERMor1_0 n :=
  ⟨.leaf, rfl⟩

def TreeERMor1_0.proj {n : ℕ} (i : Fin n) :
    TreeERMor1_0 n :=
  ⟨.proj i, rfl⟩

def TreeERMor1_0.branch {n : ℕ}
    (l r : TreeERMor1_0 n) : TreeERMor1_0 n :=
  ⟨.branch l.val r.val, by
    simp [TreeMor1.foldDepth, l.property, r.property]⟩

def TreeERMor1_0.comp {n k : ℕ}
    (f : TreeERMor1_0 k)
    (g : Fin k → TreeERMor1_0 n) : TreeERMor1_0 n :=
  ⟨.comp f.val (fun i => (g i).val), by
    simp [TreeMor1.foldDepth, f.property]
    apply Finset.sup_le
    intro i _
    exact le_of_eq (g i).property⟩
```

- [ ] **Step 4: Add depth-1 smart constructors (including fold)**

```lean
def TreeERMor1_1.leaf {n : ℕ} : TreeERMor1_1 n :=
  TreeERMor1_0.leaf.toDepth1

def TreeERMor1_1.proj {n : ℕ} (i : Fin n) :
    TreeERMor1_1 n :=
  (TreeERMor1_0.proj i).toDepth1

def TreeERMor1_1.branch {n : ℕ}
    (l r : TreeERMor1_1 n) : TreeERMor1_1 n :=
  ⟨.branch l.val r.val, by
    simp [TreeMor1.foldDepth]
    exact max_le l.property r.property⟩

def TreeERMor1_1.comp {n k : ℕ}
    (f : TreeERMor1_1 k)
    (g : Fin k → TreeERMor1_1 n) : TreeERMor1_1 n :=
  ⟨.comp f.val (fun i => (g i).val), by
    simp [TreeMor1.foldDepth]
    exact ⟨f.property, Finset.sup_le
      (fun i _ => (g i).property)⟩⟩

def TreeERMor1_1.fold {n m : ℕ}
    (f : Fin m → TreeERMor1_0 n)
    (g : Fin m → TreeERMor1_0 (m + m))
    (tree : TreeERMor1_0 n) (j : Fin m) :
    TreeERMor1_1 n :=
  ⟨.fold m (fun i => (f i).val) (fun i => (g i).val)
    tree.val j, by
    simp [TreeMor1.foldDepth]
    constructor
    · exact ⟨Finset.sup_le (fun i _ =>
        le_of_eq (f i).property),
        Finset.sup_le (fun i _ =>
          le_of_eq (g i).property)⟩
    · exact le_of_eq tree.property⟩
```

- [ ] **Step 5: Add depth-2 smart constructors (including fold)**

Same pattern: leaf/proj/branch/comp via widening or direct; fold
takes depth-1 arguments and produces depth-2.

```lean
def TreeERMor1.leaf {n : ℕ} : TreeERMor1 n :=
  TreeERMor1_0.leaf.toDepth2

def TreeERMor1.proj {n : ℕ} (i : Fin n) :
    TreeERMor1 n :=
  (TreeERMor1_0.proj i).toDepth2

def TreeERMor1.branch {n : ℕ}
    (l r : TreeERMor1 n) : TreeERMor1 n :=
  ⟨.branch l.val r.val, by
    simp [TreeMor1.foldDepth]
    exact max_le l.property r.property⟩

def TreeERMor1.comp {n k : ℕ}
    (f : TreeERMor1 k)
    (g : Fin k → TreeERMor1 n) : TreeERMor1 n :=
  ⟨.comp f.val (fun i => (g i).val), by
    simp [TreeMor1.foldDepth]
    exact ⟨f.property, Finset.sup_le
      (fun i _ => (g i).property)⟩⟩

def TreeERMor1.fold {n m : ℕ}
    (f : Fin m → TreeERMor1_1 n)
    (g : Fin m → TreeERMor1_1 (m + m))
    (tree : TreeERMor1_1 n) (j : Fin m) :
    TreeERMor1 n :=
  ⟨.fold m (fun i => (f i).val) (fun i => (g i).val)
    tree.val j, by
    simp [TreeMor1.foldDepth]
    constructor
    · exact ⟨Finset.sup_le (fun i _ =>
        (f i).property),
        Finset.sup_le (fun i _ =>
          (g i).property)⟩
    · exact tree.property⟩
```

- [ ] **Step 6: Add fold1 and mutuFold convenience wrappers**

```lean
def TreeERMorN_1 (n m : ℕ) : Type :=
  Fin m → TreeERMor1_1 n

def TreeERMorN (n m : ℕ) : Type :=
  Fin m → TreeERMor1 n

def TreeERMor1_1.fold1 {n : ℕ}
    (base : TreeERMor1_0 n)
    (step : TreeERMor1_0 2)
    (tree : TreeERMor1_0 n) : TreeERMor1_1 n :=
  TreeERMor1_1.fold
    (fun _ => base) (fun _ => step) tree 0

def TreeERMor1.fold1 {n : ℕ}
    (base : TreeERMor1_1 n)
    (step : TreeERMor1_1 2)
    (tree : TreeERMor1_1 n) : TreeERMor1 n :=
  TreeERMor1.fold
    (fun _ => base) (fun _ => step) tree 0

def TreeERMor1_1.mutuFold {n m : ℕ}
    (f : Fin m → TreeERMor1_0 n)
    (g : Fin m → TreeERMor1_0 (m + m))
    (tree : TreeERMor1_0 n) : TreeERMorN_1 n m :=
  fun j => TreeERMor1_1.fold f g tree j

def TreeERMor1.mutuFold {n m : ℕ}
    (f : Fin m → TreeERMor1_1 n)
    (g : Fin m → TreeERMor1_1 (m + m))
    (tree : TreeERMor1_1 n) : TreeERMorN n m :=
  fun j => TreeERMor1.fold f g tree j
```

- [ ] **Step 7: Add interpretation at each tier**

```lean
def TreeERMor1_0.interp {n : ℕ}
    (t : TreeERMor1_0 n) (ctx : Fin n → BT.{u}) :
    BT.{u} :=
  t.val.interp ctx

def TreeERMor1_1.interp {n : ℕ}
    (t : TreeERMor1_1 n) (ctx : Fin n → BT.{u}) :
    BT.{u} :=
  t.val.interp ctx

def TreeERMor1.interp {n : ℕ}
    (t : TreeERMor1 n) (ctx : Fin n → BT.{u}) :
    BT.{u} :=
  t.val.interp ctx
```

- [ ] **Step 8: Add TreeERMorN operations**

```lean
def TreeERMorN.interp {n m : ℕ}
    (f : TreeERMorN n m) (ctx : Fin n → BT.{u}) :
    Fin m → BT.{u} :=
  fun i => (f i).interp ctx

def TreeERMorN.id (n : ℕ) : TreeERMorN n n :=
  fun i => TreeERMor1.proj i

def TreeERMorN.comp {n m k : ℕ}
    (f : TreeERMorN n m) (g : TreeERMorN m k) :
    TreeERMorN n k :=
  fun i => TreeERMor1.comp (g i) f
```

- [ ] **Step 9: Build and verify**

Run: `lake build GebLean.LawvereTreeER`
Expected: PASS, no warnings.

- [ ] **Step 10: Commit**

```bash
git add GebLean/LawvereTreeER.lean
git commit -m "Add TreeERMor1 subtypes, smart constructors, and tuple ops"
```

---

## Tasks 4–9: Quotient, Category, Products, Interp, Inclusion, Tests

These follow the SAME structure as the original plan's Tasks 9–17,
with one change: the `treeErInclusion` functor now maps via
`TreeMor1.toBTMor1` on each `.val` component (rather than direct
`.val` unwrap, since `TreeMor1 ≠ BTMor1`).

Specifically:

### Task 4: Quotient + identity + composition

Same as original Task 9. Create `GebLean/LawvereTreeERQuot.lean`
with `treeErMorNSetoid`, `TreeERMorNQuo`, id, comp, interp.

### Task 5: Category instance

Same as original Task 10. Category laws, `LawvereTreeERCat := ℕ`,
`CategoryStruct`, `Category`.

### Task 6: HasChosenFiniteProducts

Same as original Task 11. Terminal, products, pairing, laws.
Register `LawvereTreeERQuot` in `GebLean.lean`.

### Task 7: Interp functor + Faithful

Same as original Task 12 but create `LawvereTreeERInterp.lean`.

### Task 8: Inclusion into LawvereBTQuotCat + Faithful

Same as original Task 13 but map morphisms via:

```lean
def TreeERMorN.toBTMorN {n m : ℕ}
    (f : TreeERMorN n m) : BTMorN n m :=
  fun i => (f i).val.toBTMor1
```

Register `LawvereTreeERInterp` in `GebLean.lean`.

### Task 9: Tests

Three test files, same as original Tasks 14–16.  Register in
`GebLeanTests.lean`.

### Task 10: Workstream tracker update

Mark 4g.1 complete.

---

For Tasks 4–10, use the corresponding original-plan task text as the
implementation template — the code is identical modulo replacing
`(f i).val` (subtype of BTMor1) with `(f i).val.toBTMor1` (TreeMor1
→ BTMor1 translation) in the inclusion functor.  All other code
(setoid, quotient, category, products) is unchanged because it
operates on `TreeERMor1` interpretation, not on `BTMor1` directly.
