# Lawvere Tree-ER Sub-project 4g.1 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Establish `LawvereTreeERCat`, the tree-native elementary
recursive Lawvere theory, as a subtype of `BTMor1` with fold-nesting
depth at most 2.  Ship its `HasChosenFiniteProducts` instance, its
faithful interpretation functor into `Type`, and its faithful inclusion
into `LawvereBTQuotCat`.

**Architecture:** Represent `TreeERMor1 n` as
`{ t : BTMor1 n // t.foldDepth ≤ 2 }`, with tier aliases
`TreeERMor1_0 n` (depth = 0) and `TreeERMor1_1 n` (depth ≤ 1) for
static depth-tracking at the smart-constructor level.  Every
`BTMor1` computation lemma lifts to `TreeERMor1` via `.val` unwrapping;
`TreeERMorN n m` tuples are `Fin m → TreeERMor1 n`.  Category structure
and finite products mirror `LawvereERQuot.lean` / `LawvereBTQuot.lean`.

**Tech Stack:** Lean 4 + Mathlib, `PolyFix` / `BTMor1.ind` polynomial-
functor machinery from `GebLean/LawvereBT.lean`, and the finite-products
infrastructure in `GebLean/Utilities/ComputableLimits.lean`.

**Design spec:** `docs/superpowers/specs/2026-04-15-lawvere-treeer-subproject-4g1-design.md`.
**Workstream tracker entry:**
`.session/workstreams/lawvere-elementary-recursive.md` — "Phase 4g"
section.

---

## File structure

Files to create:

* `GebLean/LawvereTreeER.lean` — `BTMor1.foldDepth`, subtype aliases,
  smart constructors, convenience wrappers, `TreeERMor1.interp`,
  `TreeERMorN` and its operations.  (~350 lines.)
* `GebLean/LawvereTreeERQuot.lean` — `treeErMorNSetoid`,
  `TreeERMorNQuo`, quotient identity/composition, `Category`
  instance on `LawvereTreeERCat`, `HasChosenFiniteProducts`.  (~250
  lines.)
* `GebLean/LawvereTreeERInterp.lean` — `treeErInterpFunctor`,
  `treeErInclusion`, their `Faithful` instances.  (~100 lines.)
* `GebLeanTests/LawvereTreeER.lean` — `#guard` tests for smart
  constructors, mutumorphism worked example, depth-tier type-checks.
* `GebLeanTests/LawvereTreeERQuot.lean` — category-law and finite-
  product sanity.
* `GebLeanTests/LawvereTreeERInterp.lean` — functor faithfulness
  type-checks, inclusion-functor faithfulness.

Files to modify:

* `GebLean.lean` — three `import` additions (one per new library
  module), in alphabetical slots after `LawvereBTPrimrec`.
* `GebLeanTests.lean` — three `import` additions for the new test
  modules.
* `.session/workstreams/lawvere-elementary-recursive.md` — mark 4g.1
  complete in the tracker's task list and append a completion
  paragraph to the Status section.

---

## Key infrastructure references

These are the existing project definitions this plan consumes:

* `GebLean/LawvereBT.lean`:
  * `BTMor1 n : Type := PolyFix btMorPoly n` (line 420).
  * Smart constructors `BTMor1.proj`, `BTMor1.leaf`, `BTMor1.branch`,
    `BTMor1.fold` (lines 469–507).
  * `BTMor1.ind` induction principle (line 828) — this is the main
    recursion tool for the four cases (proj, leaf, branch, fold),
    indexed by `Fin 4`.
  * `BTMor1.rename` (line 881) — canonical template for defining a
    function on `BTMor1` via `BTMor1.ind`.
  * `BTMor1.subst {n m : ℕ} (t : BTMor1 n) (σ : Fin n → BTMor1 m) :
    BTMor1 m` — substitution.
  * `BTMor1.interp` and `BTMor1.interpU` — standard interpretation.
  * `BTMorN n m := Fin m → BTMor1 n` and `BTMorN.comp` (line 1072) =
    `fun j => (g j).subst f`.
* `GebLean/LawvereBTQuot.lean`:
  * `btMorNSetoid`, `BTMorNQuo`, category instance,
    `HasChosenFiniteProducts` — our mirrors for the Quot and Interp
    modules.
* `GebLean/LawvereBTInterp.lean`:
  * `interpFunctor : LawvereBTQuotCat ⥤ Type` pattern.
* `GebLean/Utilities/ComputableLimits.lean`:
  * `ChosenBinaryProduct`, `ChosenTerminal`, `HasChosenFiniteProducts`.
* `GebLean/LawvereERQuot.lean`, `GebLean/LawvereERInterp.lean`:
  * Parallel patterns on the ℕ-based side that we mirror here.

---

## Task 1: `BTMor1.foldDepth` and reduction lemmas

**Files:**

* Create: `GebLean/LawvereTreeER.lean`

This task introduces the depth function.  Because `BTMor1` is defined
as `PolyFix btMorPoly n`, functions on it are built via `BTMor1.ind`
with a four-way `match i : Fin 4` on the polynomial component.  Use
`BTMor1.rename` (`LawvereBT.lean:881`) as the template for the
induction structure.  The motive is the simplest possible: `fun {k} _
=> ℕ`, returning a single natural number.

- [ ] **Step 1: Create the file with header, imports, namespace**

Create `/home/terence/git-workspaces/geb-syntax/geb-lean/GebLean/LawvereTreeER.lean`:

```lean
import GebLean.LawvereBT

/-!
# Tree-Native Elementary Recursive Morphisms

Depth-2-bounded fragment of `BTMor1`, presenting elementary recursive
functions in their tree-native form (Leivant 1999; Beckmann-Weiermann
2000).  Subtype over `BTMor1` so that every BT computation lemma
applies after `.val` unwrapping; tier aliases
`TreeERMor1_0`, `TreeERMor1_1`, `TreeERMor1` give static depth-
tracking at the smart-constructor level.
-/

namespace GebLean

end GebLean
```

- [ ] **Step 2: Build to confirm the scaffold**

Run: `lake build GebLean.LawvereTreeER`
Expected: PASS, no warnings.

- [ ] **Step 3: Add `BTMor1.foldDepth` via `BTMor1.ind`**

Insert inside the `namespace GebLean` block.  Follow the case
decomposition of `BTMor1.rename` in `GebLean/LawvereBT.lean:881`:

```lean
/-- Maximum nesting depth of `fold` constructors in a `BTMor1` term.
Used to carve out depth-bounded subtypes for the tree-native
elementary-recursive Lawvere theory. -/
def BTMor1.foldDepth : ∀ {n : ℕ}, BTMor1 n → ℕ := fun {_} t =>
  BTMor1.ind
    (motive := fun {_} _ => ℕ)
    (step := fun i => match i with
      | ⟨0, _⟩ => fun _ _ _ => 0
      | ⟨1, _⟩ => fun _ _ _ => 0
      | ⟨2, _⟩ => fun _ _ ih =>
          max (ih (Sum.inl PUnit.unit))
              (ih (Sum.inr PUnit.unit))
      | ⟨3, _⟩ => fun pos _ ih =>
          let pm := pos.1
          have hlb (i : Fin pm) :
              i.val < pm + pm + 1 :=
            Nat.lt_of_lt_of_le i.isLt
              (Nat.le_add_right pm (pm + 1))
          have hls (i : Fin pm) :
              pm + i.val < pm + pm + 1 := by
            have := i.isLt; omega
          have hlt : pm + pm < pm + pm + 1 :=
            Nat.lt_succ_self _
          1 + max (max
            ((Finset.univ : Finset (Fin pm)).sup
              (fun i => ih ⟨i.val, hlb i⟩))
            ((Finset.univ : Finset (Fin pm)).sup
              (fun i => ih ⟨pm + i.val, hls i⟩)))
            (ih ⟨pm + pm, hlt⟩))
    t
```

Note: the fold-case step receives 2m+1 children (m base, m step, 1
tree).  The `hlb`/`hls`/`hlt` helper bounds replicate the ones used
in `BTMor1.rename`'s fold case (`LawvereBT.lean:904–915`) to pick out
each child slot.

- [ ] **Step 4: Build and expect the definition to compile**

Run: `lake build GebLean.LawvereTreeER`
Expected: PASS, no warnings.

If the `Finset.univ.sup` form doesn't elaborate as written, use
`Finset.univ (α := Fin pm)` instead of the type ascription.  If the
fold arity calculation is off, cross-reference
`LawvereBT.lean:904–915`'s structure and mirror exactly.

- [ ] **Step 5: Add reduction lemmas (one per smart constructor)**

Insert after the `BTMor1.foldDepth` definition:

```lean
@[simp] theorem BTMor1.foldDepth_proj {n : ℕ} (i : Fin n) :
    (BTMor1.proj i).foldDepth = 0 := by
  unfold BTMor1.foldDepth BTMor1.proj
  simp [BTMor1.ind, btMorInject_eq]

@[simp] theorem BTMor1.foldDepth_leaf {n : ℕ} :
    (@BTMor1.leaf n).foldDepth = 0 := by
  unfold BTMor1.foldDepth BTMor1.leaf
  simp [BTMor1.ind, btMorInject_eq]

@[simp] theorem BTMor1.foldDepth_branch {n : ℕ}
    (l r : BTMor1 n) :
    (BTMor1.branch l r).foldDepth =
      max l.foldDepth r.foldDepth := by
  unfold BTMor1.foldDepth BTMor1.branch
  simp [BTMor1.ind, btMorInject_eq]

@[simp] theorem BTMor1.foldDepth_fold {n m : ℕ}
    (f : Fin m → BTMor1 n)
    (g : Fin m → BTMor1 (m + m))
    (tree : BTMor1 n) (j : Fin m) :
    (BTMor1.fold m f g tree j).foldDepth =
      1 + max (max
        ((Finset.univ : Finset (Fin m)).sup
          (fun i => (f i).foldDepth))
        ((Finset.univ : Finset (Fin m)).sup
          (fun i => (g i).foldDepth)))
        tree.foldDepth := by
  unfold BTMor1.foldDepth BTMor1.fold
  simp [BTMor1.ind, btMorInject_eq]
```

The `simp` tactic here may need additional unfolding lemmas
(`polyFixStrFamily`, `polyEndoMorphEvalAt` etc.) depending on how
`BTMor1.ind` reduces on each smart-constructor shape.  If `simp`
leaves residual goals, use `rfl` directly or `decide` for small
cases.  If `BTMor1.ind`'s reduction behavior isn't `rfl`-level, follow
how `BTMor1.rename` is verified for structural compliance (search for
existing lemmas of the form `rename_proj`, `rename_leaf`, etc.; if
they don't exist, this plan is establishing the first such pattern).

- [ ] **Step 6: Build and verify reduction lemmas pass**

Run: `lake build GebLean.LawvereTreeER`
Expected: PASS, no warnings.

If any reduction lemma fails to close, investigate with
`lean_goal` / `lean_hover_info` on the residual goal.  The polynomial-
functor computation is deterministic, so `rfl` should work for each
case; `simp` is a fallback if `rfl` has elaboration issues.

- [ ] **Step 7: Register the module in `GebLean.lean`**

Read `GebLean.lean` to find the alphabetical slot.  Insert:

```lean
import GebLean.LawvereTreeER
```

Insert immediately after `import GebLean.LawvereBTPrimrec` and before
`import GebLean.LawvereER`.

- [ ] **Step 8: Full build to catch regressions**

Run: `lake build`
Expected: PASS, no warnings.

- [ ] **Step 9: Commit**

```bash
git add GebLean/LawvereTreeER.lean GebLean.lean
git commit -m "Add BTMor1.foldDepth function and reduction lemmas"
```

---

## Task 2: `BTMor1.subst` depth preservation

**Files:**

* Modify: `GebLean/LawvereTreeER.lean`

Substitution combines a term's structure with substituted projections.
If the term and all substitutions have depth ≤ d, the result has
depth ≤ d.  This lemma is needed by every smart-constructor `comp`
that uses substitution to build the underlying `BTMor1`.

- [ ] **Step 1: State the lemma with a placeholder `sorry`**

Insert after the foldDepth reduction lemmas, inside the namespace:

```lean
/-- Substitution preserves depth upper bounds.  If the target term
has depth ≤ d and every substituted function has depth ≤ d, the
substituted term has depth ≤ d. -/
theorem BTMor1.subst_foldDepth_le {n m d : ℕ}
    (t : BTMor1 n) (σ : Fin n → BTMor1 m)
    (ht : t.foldDepth ≤ d)
    (hσ : ∀ i, (σ i).foldDepth ≤ d) :
    (t.subst σ).foldDepth ≤ d := by
  sorry
```

- [ ] **Step 2: Confirm the build fails on `sorry`**

Run: `lake build GebLean.LawvereTreeER`
Expected: FAIL with "declaration uses 'sorry'".

- [ ] **Step 3: Fill in the proof by `BTMor1.ind`**

Replace the `sorry` with an induction on `t` matching the `rename`
pattern.  The motive threads the substitution through the induction:

```lean
  revert σ
  refine BTMor1.ind
    (motive := fun {k} (t' : BTMor1 k) =>
      ∀ (σ : Fin k → BTMor1 m),
        t'.foldDepth ≤ d →
        (∀ i, (σ i).foldDepth ≤ d) →
        (t'.subst σ).foldDepth ≤ d)
    (step := fun i => match i with
      | ⟨0, _⟩ => fun _ _ _ σ _ hσ => by
          simp [BTMor1.subst_proj]; exact hσ _
      | ⟨1, _⟩ => fun _ _ _ σ _ _ => by
          simp [BTMor1.subst_leaf]
      | ⟨2, _⟩ => fun _ _ ih σ ht hσ => by
          simp [BTMor1.subst_branch,
            BTMor1.foldDepth_branch] at *
          refine ⟨?_, ?_⟩
          · exact ih (Sum.inl PUnit.unit) σ
              (by omega_or_expand_ht) hσ
          · exact ih (Sum.inr PUnit.unit) σ
              (by omega_or_expand_ht) hσ
      | ⟨3, _⟩ => fun pos _ ih σ ht hσ => by
          -- The fold case substitutes into base children
          -- and tree child (each at fiber n_inner), but
          -- NOT into step children (at fiber m+m,
          -- fold-bound).  Depth bound of the result equals
          -- 1 + max of depths, each of which is bounded by
          -- d via ih and the ht decomposition.
          sorry) t
  exact this ht hσ
```

Note: the `omega_or_expand_ht` placeholder is where `ht` (the depth
bound on the branch) is decomposed into bounds on left and right
children via `BTMor1.foldDepth_branch` and `omega`.  The fold case's
`sorry` is a placeholder to fill with the analogous branch/fold
unpacking.

This is a genuinely nontrivial proof.  Reduction lemmas for
`BTMor1.subst` (`subst_proj`, `subst_leaf`, `subst_branch`,
`subst_fold`) may or may not be in the project already; if not, add
them as local private lemmas first, following the pattern of the
`foldDepth_*` reduction lemmas from Task 1.

If the proof proves intractable in one commit, escalate to the
controller.  This lemma is a prerequisite for every subsequent
smart-constructor `comp`, so it cannot be skipped.

- [ ] **Step 4: Build and confirm the proof closes**

Run: `lake build GebLean.LawvereTreeER`
Expected: PASS, no warnings, no `sorry`.

- [ ] **Step 5: Commit**

```bash
git add GebLean/LawvereTreeER.lean
git commit -m "Prove BTMor1.subst preserves fold-depth upper bounds"
```

---

## Task 3: Subtype aliases and widening lifts

**Files:**

* Modify: `GebLean/LawvereTreeER.lean`

- [ ] **Step 1: Add the three subtype aliases**

Insert after the subst lemma, inside the namespace:

```lean
/-- Depth-0 fragment of `BTMor1 n`: no fold constructors. -/
def TreeERMor1_0 (n : ℕ) : Type :=
  { t : BTMor1 n // t.foldDepth = 0 }

/-- Depth-≤-1 fragment of `BTMor1 n`: at most one level of folds. -/
def TreeERMor1_1 (n : ℕ) : Type :=
  { t : BTMor1 n // t.foldDepth ≤ 1 }

/-- Depth-≤-2 fragment of `BTMor1 n`: at most two levels of folds.
Corresponds to the elementary recursive fragment of the binary-tree
Lawvere theory (Leivant 1999). -/
def TreeERMor1 (n : ℕ) : Type :=
  { t : BTMor1 n // t.foldDepth ≤ 2 }
```

- [ ] **Step 2: Add widening lifts**

Insert after the subtype aliases:

```lean
/-- Widen a depth-0 term to the depth-1 tier. -/
def TreeERMor1_0.toDepth1 {n : ℕ}
    (t : TreeERMor1_0 n) : TreeERMor1_1 n :=
  ⟨t.val, by have := t.property; omega⟩

/-- Widen a depth-1 term to the depth-2 tier. -/
def TreeERMor1_1.toDepth2 {n : ℕ}
    (t : TreeERMor1_1 n) : TreeERMor1 n :=
  ⟨t.val, by have := t.property; omega⟩

/-- Widen a depth-0 term directly to the depth-2 tier. -/
def TreeERMor1_0.toDepth2 {n : ℕ}
    (t : TreeERMor1_0 n) : TreeERMor1 n :=
  t.toDepth1.toDepth2
```

- [ ] **Step 3: Build and verify**

Run: `lake build GebLean.LawvereTreeER`
Expected: PASS, no warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereTreeER.lean
git commit -m "Add TreeERMor1 subtype aliases and widening lifts"
```

---

## Task 4: Depth-0 smart constructors

**Files:**

* Modify: `GebLean/LawvereTreeER.lean`

- [ ] **Step 1: Add the four depth-0 smart constructors**

Insert after the widening lifts:

```lean
/-- Leaf constant at the depth-0 tier. -/
def TreeERMor1_0.leaf {n : ℕ} : TreeERMor1_0 n :=
  ⟨BTMor1.leaf, BTMor1.foldDepth_leaf⟩

/-- Projection at the depth-0 tier. -/
def TreeERMor1_0.proj {n : ℕ} (i : Fin n) : TreeERMor1_0 n :=
  ⟨BTMor1.proj i, BTMor1.foldDepth_proj i⟩

/-- Branch constructor at the depth-0 tier. -/
def TreeERMor1_0.branch {n : ℕ}
    (l r : TreeERMor1_0 n) : TreeERMor1_0 n :=
  ⟨BTMor1.branch l.val r.val, by
    rw [BTMor1.foldDepth_branch, l.property, r.property]; rfl⟩

/-- Composition at the depth-0 tier: substitute `f`'s projections
with `g`. -/
def TreeERMor1_0.comp {n k : ℕ}
    (f : TreeERMor1_0 k)
    (g : Fin k → TreeERMor1_0 n) : TreeERMor1_0 n :=
  ⟨BTMor1.subst f.val (fun i => (g i).val), by
    apply Nat.le_antisymm
    · apply BTMor1.subst_foldDepth_le
      · exact f.property.le
      · intro i; exact (g i).property.le
    · exact Nat.zero_le _⟩
```

- [ ] **Step 2: Build and verify**

Run: `lake build GebLean.LawvereTreeER`
Expected: PASS, no warnings.

If `BTMor1.subst_foldDepth_le` requires different hypothesis shapes,
adjust the `by` block in `.comp`; the goal "result = 0" needs both
upper-bound (from subst_foldDepth_le with d = 0) and lower-bound
(`Nat.zero_le`).

- [ ] **Step 3: Commit**

```bash
git add GebLean/LawvereTreeER.lean
git commit -m "Add depth-0 smart constructors for TreeERMor1"
```

---

## Task 5: Depth-1 smart constructors (including fold)

**Files:**

* Modify: `GebLean/LawvereTreeER.lean`

- [ ] **Step 1: Add non-fold smart constructors at depth-1 tier**

Insert after the depth-0 constructors:

```lean
/-- Leaf at the depth-1 tier. -/
def TreeERMor1_1.leaf {n : ℕ} : TreeERMor1_1 n :=
  TreeERMor1_0.leaf.toDepth1

/-- Projection at the depth-1 tier. -/
def TreeERMor1_1.proj {n : ℕ} (i : Fin n) : TreeERMor1_1 n :=
  (TreeERMor1_0.proj i).toDepth1

/-- Branch at the depth-1 tier. -/
def TreeERMor1_1.branch {n : ℕ}
    (l r : TreeERMor1_1 n) : TreeERMor1_1 n :=
  ⟨BTMor1.branch l.val r.val, by
    rw [BTMor1.foldDepth_branch]
    exact max_le l.property r.property⟩

/-- Composition at the depth-1 tier. -/
def TreeERMor1_1.comp {n k : ℕ}
    (f : TreeERMor1_1 k)
    (g : Fin k → TreeERMor1_1 n) : TreeERMor1_1 n :=
  ⟨BTMor1.subst f.val (fun i => (g i).val),
    BTMor1.subst_foldDepth_le _ _ f.property
      (fun i => (g i).property)⟩
```

- [ ] **Step 2: Add the `fold` smart constructor at depth-1 tier**

Insert immediately after:

```lean
/-- Fold at the depth-1 tier: arguments are depth-0, result is
depth-1 (one fold layer). -/
def TreeERMor1_1.fold {n m : ℕ}
    (f : Fin m → TreeERMor1_0 n)
    (g : Fin m → TreeERMor1_0 (m + m))
    (tree : TreeERMor1_0 n) (j : Fin m) : TreeERMor1_1 n :=
  ⟨BTMor1.fold m (fun i => (f i).val)
    (fun i => (g i).val) tree.val j, by
    rw [BTMor1.foldDepth_fold]
    -- foldDepth of fold is 1 + max (sup f-depths, sup g-depths,
    -- tree-depth).  Each sub-depth is 0 (from depth-0 tier), so
    -- the result is 1 + max (0, 0, 0) = 1, which is ≤ 1.
    simp only [Finset.sup_le_iff, Finset.mem_univ, forall_true_iff]
    constructor
    · intro i; rw [(f i).property]
    · constructor
      · intro i; rw [(g i).property]
      · rw [tree.property]
    -- Close the `1 + 0 ≤ 1` obligation
    all_goals omega⟩
```

The exact form of the depth-bound proof depends on how `Finset.sup`
unfolds; adapt the tactic block as needed to discharge
"1 + max (sup = 0) (sup = 0) 0 ≤ 1".

- [ ] **Step 3: Build and verify**

Run: `lake build GebLean.LawvereTreeER`
Expected: PASS, no warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereTreeER.lean
git commit -m "Add depth-1 smart constructors including fold"
```

---

## Task 6: Depth-2 smart constructors (including fold)

**Files:**

* Modify: `GebLean/LawvereTreeER.lean`

- [ ] **Step 1: Add non-fold smart constructors at depth-2 tier**

Insert after the depth-1 constructors:

```lean
/-- Leaf at the depth-2 tier. -/
def TreeERMor1.leaf {n : ℕ} : TreeERMor1 n :=
  TreeERMor1_0.leaf.toDepth2

/-- Projection at the depth-2 tier. -/
def TreeERMor1.proj {n : ℕ} (i : Fin n) : TreeERMor1 n :=
  (TreeERMor1_0.proj i).toDepth2

/-- Branch at the depth-2 tier. -/
def TreeERMor1.branch {n : ℕ}
    (l r : TreeERMor1 n) : TreeERMor1 n :=
  ⟨BTMor1.branch l.val r.val, by
    rw [BTMor1.foldDepth_branch]
    exact max_le l.property r.property⟩

/-- Composition at the depth-2 tier. -/
def TreeERMor1.comp {n k : ℕ}
    (f : TreeERMor1 k)
    (g : Fin k → TreeERMor1 n) : TreeERMor1 n :=
  ⟨BTMor1.subst f.val (fun i => (g i).val),
    BTMor1.subst_foldDepth_le _ _ f.property
      (fun i => (g i).property)⟩
```

- [ ] **Step 2: Add the `fold` smart constructor at depth-2 tier**

Insert immediately after:

```lean
/-- Fold at the depth-2 tier: arguments are depth-≤-1, result is
depth-≤-2 (two fold layers). -/
def TreeERMor1.fold {n m : ℕ}
    (f : Fin m → TreeERMor1_1 n)
    (g : Fin m → TreeERMor1_1 (m + m))
    (tree : TreeERMor1_1 n) (j : Fin m) : TreeERMor1 n :=
  ⟨BTMor1.fold m (fun i => (f i).val)
    (fun i => (g i).val) tree.val j, by
    rw [BTMor1.foldDepth_fold]
    -- Depth = 1 + max (sup f-depths ≤ 1, sup g-depths ≤ 1,
    -- tree-depth ≤ 1), each ≤ 1, so result ≤ 2.
    have hf : ((Finset.univ : Finset (Fin m)).sup
        (fun i => (f i).val.foldDepth)) ≤ 1 := by
      apply Finset.sup_le; intro i _; exact (f i).property
    have hg : ((Finset.univ : Finset (Fin m)).sup
        (fun i => (g i).val.foldDepth)) ≤ 1 := by
      apply Finset.sup_le; intro i _; exact (g i).property
    omega⟩
```

- [ ] **Step 3: Build and verify**

Run: `lake build GebLean.LawvereTreeER`
Expected: PASS, no warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereTreeER.lean
git commit -m "Add depth-2 smart constructors including fold"
```

---

## Task 7: `fold1` and `mutuFold` convenience wrappers

**Files:**

* Modify: `GebLean/LawvereTreeER.lean`

- [ ] **Step 1: Add `fold1` at depth-1 tier**

Insert after the depth-2 smart constructors:

```lean
/-- Single-recursion fold at the depth-1 tier: `m = 1` case of
`fold`, for non-mutumorphic tree recursion.  `base` is the value at
leaves; `step` combines two recursive results at internal nodes. -/
def TreeERMor1_1.fold1 {n : ℕ}
    (base : TreeERMor1_0 n)
    (step : TreeERMor1_0 2)
    (tree : TreeERMor1_0 n) : TreeERMor1_1 n :=
  TreeERMor1_1.fold
    (f := fun _ => base)
    (g := fun _ => step)
    tree 0
```

- [ ] **Step 2: Add `fold1` at depth-2 tier**

```lean
/-- Single-recursion fold at the depth-2 tier. -/
def TreeERMor1.fold1 {n : ℕ}
    (base : TreeERMor1_1 n)
    (step : TreeERMor1_1 2)
    (tree : TreeERMor1_1 n) : TreeERMor1 n :=
  TreeERMor1.fold
    (f := fun _ => base)
    (g := fun _ => step)
    tree 0
```

- [ ] **Step 3: Forward-declare `TreeERMorN_1` and `TreeERMorN`**

Insert after `fold1` (these tuple types will be elaborated in Task 8
but need to exist as abbreviations for `mutuFold` now):

```lean
/-- Tuple of m n-ary depth-1 tree-ER terms. -/
def TreeERMorN_1 (n m : ℕ) : Type := Fin m → TreeERMor1_1 n

/-- Tuple of m n-ary depth-2 tree-ER terms. -/
def TreeERMorN (n m : ℕ) : Type := Fin m → TreeERMor1 n
```

- [ ] **Step 4: Add `mutuFold` at both tiers**

```lean
/-- Full m-slot mutumorphism at the depth-1 tier: returns a tuple of
m mutually-recursive functions computed simultaneously from the tree. -/
def TreeERMor1_1.mutuFold {n m : ℕ}
    (f : Fin m → TreeERMor1_0 n)
    (g : Fin m → TreeERMor1_0 (m + m))
    (tree : TreeERMor1_0 n) : TreeERMorN_1 n m :=
  fun j => TreeERMor1_1.fold f g tree j

/-- Full m-slot mutumorphism at the depth-2 tier. -/
def TreeERMor1.mutuFold {n m : ℕ}
    (f : Fin m → TreeERMor1_1 n)
    (g : Fin m → TreeERMor1_1 (m + m))
    (tree : TreeERMor1_1 n) : TreeERMorN n m :=
  fun j => TreeERMor1.fold f g tree j
```

- [ ] **Step 5: Build and verify**

Run: `lake build GebLean.LawvereTreeER`
Expected: PASS, no warnings.

- [ ] **Step 6: Commit**

```bash
git add GebLean/LawvereTreeER.lean
git commit -m "Add fold1 and mutuFold convenience helpers"
```

---

## Task 8: Interpretation and tuple operations

**Files:**

* Modify: `GebLean/LawvereTreeER.lean`

- [ ] **Step 1: Add `TreeERMor1.interp` at each tier**

Insert after the tuple type declarations:

```lean
/-- Interpretation at the depth-0 tier: inherited from `BTMor1`. -/
def TreeERMor1_0.interp {n : ℕ}
    (t : TreeERMor1_0 n) (ctx : Fin n → BT.{u}) : BT.{u} :=
  t.val.interpU ctx

@[simp] theorem TreeERMor1_0.interp_val {n : ℕ}
    (t : TreeERMor1_0 n) (ctx : Fin n → BT.{u}) :
    t.interp ctx = t.val.interpU ctx := rfl

/-- Interpretation at the depth-1 tier. -/
def TreeERMor1_1.interp {n : ℕ}
    (t : TreeERMor1_1 n) (ctx : Fin n → BT.{u}) : BT.{u} :=
  t.val.interpU ctx

@[simp] theorem TreeERMor1_1.interp_val {n : ℕ}
    (t : TreeERMor1_1 n) (ctx : Fin n → BT.{u}) :
    t.interp ctx = t.val.interpU ctx := rfl

/-- Interpretation at the depth-2 tier. -/
def TreeERMor1.interp {n : ℕ}
    (t : TreeERMor1 n) (ctx : Fin n → BT.{u}) : BT.{u} :=
  t.val.interpU ctx

@[simp] theorem TreeERMor1.interp_val {n : ℕ}
    (t : TreeERMor1 n) (ctx : Fin n → BT.{u}) :
    t.interp ctx = t.val.interpU ctx := rfl
```

- [ ] **Step 2: Add `TreeERMorN` interpretation, identity, composition**

Insert after the interp definitions:

```lean
/-- Tuple interpretation: apply each component's interp. -/
def TreeERMorN.interp {n m : ℕ}
    (f : TreeERMorN n m) (ctx : Fin n → BT.{u}) : Fin m → BT.{u} :=
  fun i => (f i).interp ctx

/-- Identity tuple: projections at each index. -/
def TreeERMorN.id (n : ℕ) : TreeERMorN n n :=
  fun i => TreeERMor1.proj i

/-- Composition of tree-ER tuples via substitution. -/
def TreeERMorN.comp {n m k : ℕ}
    (f : TreeERMorN n m) (g : TreeERMorN m k) :
    TreeERMorN n k :=
  fun i => TreeERMor1.comp (g i) f
```

- [ ] **Step 3: Add `@[simp]` lemmas for tuple identity and composition**

```lean
@[simp] theorem TreeERMorN.interp_id {n : ℕ}
    (ctx : Fin n → BT.{u}) :
    (TreeERMorN.id n).interp ctx = ctx := by
  funext i
  simp [TreeERMorN.interp, TreeERMorN.id, TreeERMor1.interp,
    TreeERMor1.proj, TreeERMor1_0.proj, TreeERMor1_0.toDepth2,
    TreeERMor1_0.toDepth1]
  rfl

@[simp] theorem TreeERMorN.interp_comp {n m k : ℕ}
    (f : TreeERMorN n m) (g : TreeERMorN m k)
    (ctx : Fin n → BT.{u}) :
    (f.comp g).interp ctx = g.interp (f.interp ctx) := by
  funext i
  simp [TreeERMorN.interp, TreeERMorN.comp, TreeERMor1.interp,
    TreeERMor1.comp]
  -- Reduces to BTMor1.subst_interpU-style equation on the .val level
  exact (BTMor1.subst_interpU _ _ _).symm
```

The final `exact` references a substitution-interpretation lemma
that should exist in `LawvereBT.lean`.  If the name is different,
search for `subst_interp`, `interpU_subst`, or similar in
`LawvereBT.lean` and use the correct name.  If no such lemma exists,
add it as a private helper here or fall back to a direct unfolding
proof.

- [ ] **Step 4: Build and verify**

Run: `lake build GebLean.LawvereTreeER`
Expected: PASS, no warnings.

- [ ] **Step 5: Full-project build**

Run: `lake build`
Expected: PASS, no warnings.

- [ ] **Step 6: Commit**

```bash
git add GebLean/LawvereTreeER.lean
git commit -m "Add TreeERMor1 interpretation and TreeERMorN operations"
```

---

## Task 9: `treeErMorNSetoid`, `TreeERMorNQuo`, and quotient identity/composition

**Files:**

* Create: `GebLean/LawvereTreeERQuot.lean`

- [ ] **Step 1: Create the file with header and imports**

```lean
import GebLean.LawvereTreeER
import GebLean.Utilities.ComputableLimits
import Mathlib.CategoryTheory.Category.Basic

/-!
# Quotient Category for Tree-Native Elementary Recursive Morphisms

The quotient of `TreeERMorN n m` tuples by extensional equality of
interpretation, yielding the category `LawvereTreeERCat` with
`HasChosenFiniteProducts`.  Mirrors the structure of `LawvereERQuot`
on the ℕ-encoded side and of `LawvereBTQuot` on the tree side.
-/

namespace GebLean

open CategoryTheory

end GebLean
```

- [ ] **Step 2: Define the setoid**

Insert inside the namespace:

```lean
/-- The setoid on `TreeERMorN n m` induced by extensional equality
of interpretations over `Fin n → BT.{0}`. -/
def treeErMorNSetoid (n m : ℕ) : Setoid (TreeERMorN n m) where
  r f g := ∀ ctx : Fin n → BT.{0},
    f.interp ctx = g.interp ctx
  iseqv :=
    { refl := fun _ _ => rfl
      symm := fun h ctx => (h ctx).symm
      trans := fun h₁ h₂ ctx => (h₁ ctx).trans (h₂ ctx) }
```

- [ ] **Step 3: Define the quotient**

```lean
/-- Quotient type of `TreeERMorN n m` tuples modulo extensional
equality of their interpretations.  Morphisms of
`LawvereTreeERCat`. -/
def TreeERMorNQuo (n m : ℕ) : Type :=
  Quotient (treeErMorNSetoid n m)
```

- [ ] **Step 4: Define identity and composition on the quotient**

```lean
/-- Identity quotient morphism: class of the projections tuple. -/
def TreeERMorNQuo.id (n : ℕ) : TreeERMorNQuo n n :=
  Quotient.mk (treeErMorNSetoid n n) (TreeERMorN.id n)

/-- Composition of quotient morphisms, lifted from `TreeERMorN.comp`
via `Quotient.lift₂`. -/
def TreeERMorNQuo.comp {n m k : ℕ}
    (f : TreeERMorNQuo n m) (g : TreeERMorNQuo m k) :
    TreeERMorNQuo n k :=
  Quotient.lift₂
    (s₁ := treeErMorNSetoid n m)
    (s₂ := treeErMorNSetoid m k)
    (fun f' g' =>
      Quotient.mk (treeErMorNSetoid n k)
        (TreeERMorN.comp f' g'))
    (fun fa fb ga gb hf hg =>
      Quotient.sound
        (s := treeErMorNSetoid n k)
        (fun ctx => by
          simp only [TreeERMorN.interp_comp]
          rw [hf ctx, hg (ga.interp ctx)]))
    f g
```

- [ ] **Step 5: Define `TreeERMorNQuo.interp`**

```lean
/-- Interpretation lifted to the quotient. -/
def TreeERMorNQuo.interp {n m : ℕ}
    (f : TreeERMorNQuo n m) :
    (Fin n → BT.{0}) → (Fin m → BT.{0}) :=
  Quotient.lift
    (s := treeErMorNSetoid n m)
    TreeERMorN.interp
    (fun _ _ h => funext h)
    f
```

- [ ] **Step 6: Add `@[simp]` for the `Quotient.mk` case**

```lean
@[simp] theorem TreeERMorNQuo.interp_mk {n m : ℕ}
    (f : TreeERMorN n m) :
    TreeERMorNQuo.interp
      (Quotient.mk (treeErMorNSetoid n m) f) =
      f.interp :=
  rfl
```

- [ ] **Step 7: Build and verify**

Run: `lake build GebLean.LawvereTreeERQuot`
Expected: PASS, no warnings.

- [ ] **Step 8: Commit**

```bash
git add GebLean/LawvereTreeERQuot.lean
git commit -m "Add TreeERMorNQuo setoid, identity, composition"
```

---

## Task 10: Category instance on `LawvereTreeERCat`

**Files:**

* Modify: `GebLean/LawvereTreeERQuot.lean`

- [ ] **Step 1: Prove the three category laws**

Insert after the `interp_mk` lemma:

```lean
/-- Left identity: `id ∘ f = f`. -/
theorem TreeERMorNQuo.id_comp {n m : ℕ}
    (f : TreeERMorNQuo n m) :
    TreeERMorNQuo.comp (TreeERMorNQuo.id n) f = f := by
  refine Quotient.ind (motive := fun f =>
    TreeERMorNQuo.comp (TreeERMorNQuo.id n) f = f) ?_ f
  intro f_raw
  apply Quotient.sound
  intro ctx
  simp [TreeERMorN.interp_comp, TreeERMorN.interp_id]

/-- Right identity: `f ∘ id = f`. -/
theorem TreeERMorNQuo.comp_id {n m : ℕ}
    (f : TreeERMorNQuo n m) :
    TreeERMorNQuo.comp f (TreeERMorNQuo.id m) = f := by
  refine Quotient.ind (motive := fun f =>
    TreeERMorNQuo.comp f (TreeERMorNQuo.id m) = f) ?_ f
  intro f_raw
  apply Quotient.sound
  intro ctx
  simp [TreeERMorN.interp_comp, TreeERMorN.interp_id]

/-- Associativity. -/
theorem TreeERMorNQuo.comp_assoc {n m k l : ℕ}
    (f : TreeERMorNQuo n m) (g : TreeERMorNQuo m k)
    (h : TreeERMorNQuo k l) :
    TreeERMorNQuo.comp (TreeERMorNQuo.comp f g) h =
      TreeERMorNQuo.comp f (TreeERMorNQuo.comp g h) := by
  refine Quotient.ind (motive := fun f =>
    TreeERMorNQuo.comp (TreeERMorNQuo.comp f g) h =
      TreeERMorNQuo.comp f (TreeERMorNQuo.comp g h)) ?_ f
  intro f_raw
  refine Quotient.ind (motive := fun g =>
    TreeERMorNQuo.comp (TreeERMorNQuo.comp
      (Quotient.mk _ f_raw) g) h =
      TreeERMorNQuo.comp (Quotient.mk _ f_raw)
        (TreeERMorNQuo.comp g h)) ?_ g
  intro g_raw
  refine Quotient.ind (motive := fun h =>
    TreeERMorNQuo.comp (TreeERMorNQuo.comp
      (Quotient.mk _ f_raw) (Quotient.mk _ g_raw)) h =
      TreeERMorNQuo.comp (Quotient.mk _ f_raw)
        (TreeERMorNQuo.comp (Quotient.mk _ g_raw) h)) ?_ h
  intro h_raw
  apply Quotient.sound
  intro ctx
  simp [TreeERMorN.interp_comp]
```

- [ ] **Step 2: Add the `LawvereTreeERCat` abbreviation and instances**

```lean
/-- The category of tree-native elementary recursive morphisms.
Objects are natural-number arities.  Morphisms are equivalence
classes of `TreeERMorN` tuples under extensional equality of
interpretation. -/
@[reducible] def LawvereTreeERCat : Type := ℕ

instance : CategoryStruct LawvereTreeERCat where
  Hom := TreeERMorNQuo
  id := TreeERMorNQuo.id
  comp := TreeERMorNQuo.comp

instance : Category LawvereTreeERCat where
  id_comp := TreeERMorNQuo.id_comp
  comp_id := TreeERMorNQuo.comp_id
  assoc := TreeERMorNQuo.comp_assoc
```

- [ ] **Step 3: Build and verify**

Run: `lake build GebLean.LawvereTreeERQuot`
Expected: PASS, no warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereTreeERQuot.lean
git commit -m "Add Category instance on LawvereTreeERCat"
```

---

## Task 11: `HasChosenFiniteProducts` on `LawvereTreeERCat`

**Files:**

* Modify: `GebLean/LawvereTreeERQuot.lean`

- [ ] **Step 1: Define terminal and projection morphisms**

Insert after the Category instance:

```lean
/-- Terminal morphism: the unique morphism to the empty arity. -/
def TreeERMorNQuo.terminal (n : ℕ) : TreeERMorNQuo n 0 :=
  Quotient.mk (treeErMorNSetoid n 0) (fun i => i.elim0)

/-- First projection from the product arity. -/
def TreeERMorNQuo.fst {n m : ℕ} : TreeERMorNQuo (n + m) n :=
  Quotient.mk (treeErMorNSetoid (n + m) n)
    (fun i => TreeERMor1.proj ⟨i.val, by omega⟩)

/-- Second projection. -/
def TreeERMorNQuo.snd {n m : ℕ} : TreeERMorNQuo (n + m) m :=
  Quotient.mk (treeErMorNSetoid (n + m) m)
    (fun i => TreeERMor1.proj ⟨n + i.val, by omega⟩)

/-- Pairing: given morphisms to `n` and to `m`, produce a morphism
to `n + m`. -/
def TreeERMorNQuo.pair {k n m : ℕ}
    (f : TreeERMorNQuo k n) (g : TreeERMorNQuo k m) :
    TreeERMorNQuo k (n + m) :=
  Quotient.lift₂
    (s₁ := treeErMorNSetoid k n)
    (s₂ := treeErMorNSetoid k m)
    (fun f' g' =>
      Quotient.mk (treeErMorNSetoid k (n + m))
        (fun i =>
          if h : i.val < n then f' ⟨i.val, h⟩
          else g' ⟨i.val - n, by omega⟩))
    (fun fa fb ga gb hf hg =>
      Quotient.sound
        (s := treeErMorNSetoid k (n + m))
        (fun ctx => by
          funext i
          simp [TreeERMorN.interp]
          split
          · exact congrFun (hf ctx) _
          · exact congrFun (hg ctx) _))
    f g
```

- [ ] **Step 2: Build to verify the basic product operators**

Run: `lake build GebLean.LawvereTreeERQuot`
Expected: PASS, no warnings.

- [ ] **Step 3: Add the `HasChosenFiniteProducts` instance**

```lean
/-- Chosen terminal for `LawvereTreeERCat`: the natural number 0. -/
def lawvereTreeERTerminal : ChosenTerminal LawvereTreeERCat where
  obj := 0
  isTerminal :=
    { lift := fun c => TreeERMorNQuo.terminal c.obj
      fac := fun c j => j.elim0
      uniq := fun c m _ => by
        refine Quotient.ind (motive := fun m => _) ?_ m
        intro m_raw
        apply Quotient.sound
        intro ctx
        funext i
        exact i.elim0 }

/-- Chosen binary product: arity `n + m`. -/
def lawvereTreeERProduct (n m : LawvereTreeERCat) :
    ChosenBinaryProduct n m where
  obj := n + m
  fst := TreeERMorNQuo.fst
  snd := TreeERMorNQuo.snd
  lift := TreeERMorNQuo.pair
  fac_fst := by
    intros k f g
    refine Quotient.ind (motive := fun f => _) ?_ f
    refine Quotient.ind (motive := fun g => _) ?_ g
    intros f_raw g_raw
    apply Quotient.sound
    intro ctx
    funext i
    simp [TreeERMorN.interp, TreeERMorNQuo.comp,
      TreeERMorNQuo.pair, TreeERMorNQuo.fst,
      TreeERMor1.interp, TreeERMor1.proj]
    -- Unpack the pair projection; since i < n, the `dite` evaluates
    -- to `f_raw ⟨i.val, i.isLt⟩`.
    rfl
  fac_snd := by
    intros k f g
    refine Quotient.ind (motive := fun f => _) ?_ f
    refine Quotient.ind (motive := fun g => _) ?_ g
    intros f_raw g_raw
    apply Quotient.sound
    intro ctx
    funext i
    simp [TreeERMorN.interp, TreeERMorNQuo.comp,
      TreeERMorNQuo.pair, TreeERMorNQuo.snd,
      TreeERMor1.interp, TreeERMor1.proj]
    -- i maps to n + i.val which is ≥ n, so `dite` falls through
    -- to `g_raw ⟨i.val, ...⟩`.
    rfl
  uniq := by
    intros k f g m hfst hsnd
    refine Quotient.ind (motive := fun m => _) ?_ m
    refine Quotient.ind (motive := fun f => _) ?_ f
    refine Quotient.ind (motive := fun g => _) ?_ g
    intros g_raw f_raw m_raw
    apply Quotient.sound
    intro ctx
    funext i
    -- Compose hfst and hsnd at appropriate indices to recover
    -- m_raw from f_raw and g_raw.
    sorry -- fill via case-split on `i.val < n`
```

The `sorry` in `uniq` is a placeholder.  The proof proceeds by
case-splitting on `i.val < n`: in one case use `hfst`, in the other
use `hsnd`.  Replace with the actual case-split once the build
confirms the earlier goals.

- [ ] **Step 4: Build and iterate on the uniq proof**

Run: `lake build GebLean.LawvereTreeERQuot`
Expected: FAIL with `sorry` warning in `uniq`.

Fill in the case-split:

```lean
    by_cases h : i.val < n
    · have := congrFun (Quotient.exact hfst ctx) ⟨i.val, h⟩
      simp [TreeERMorN.interp, TreeERMorNQuo.comp,
        TreeERMorNQuo.fst, TreeERMor1.interp,
        TreeERMor1.proj] at this
      simpa [TreeERMorNQuo.pair, TreeERMorN.interp]
        using this
    · have := congrFun (Quotient.exact hsnd ctx)
        ⟨i.val - n, by omega⟩
      simp [TreeERMorN.interp, TreeERMorNQuo.comp,
        TreeERMorNQuo.snd, TreeERMor1.interp,
        TreeERMor1.proj] at this
      -- bookkeeping on index arithmetic
      sorry
```

The second `sorry` here is where the index arithmetic on `i.val - n`
gets translated back to `i.val`.  Fill via additional `omega` +
`rfl`.

- [ ] **Step 5: Complete the `uniq` proof**

Iterate on the second `sorry` by examining the goal with
`lean_goal`.  Expected to reduce to a straightforward arithmetic
equation resolvable by `omega` plus a `simp` normalization.

- [ ] **Step 6: Add the `HasChosenFiniteProducts` instance**

```lean
instance : HasChosenFiniteProducts LawvereTreeERCat where
  terminal := lawvereTreeERTerminal
  binaryProduct := lawvereTreeERProduct
```

- [ ] **Step 7: Final build**

Run: `lake build GebLean.LawvereTreeERQuot`
Expected: PASS, no warnings, no `sorry`.

- [ ] **Step 8: Register in `GebLean.lean`**

Insert:

```lean
import GebLean.LawvereTreeERQuot
```

after `import GebLean.LawvereTreeER`.

- [ ] **Step 9: Full build**

Run: `lake build`
Expected: PASS, no warnings.

- [ ] **Step 10: Commit**

```bash
git add GebLean/LawvereTreeERQuot.lean GebLean.lean
git commit -m "Add HasChosenFiniteProducts on LawvereTreeERCat"
```

---

## Task 12: Interpretation functor and faithfulness

**Files:**

* Create: `GebLean/LawvereTreeERInterp.lean`

- [ ] **Step 1: Create the file**

```lean
import GebLean.LawvereTreeERQuot
import GebLean.LawvereBTInterp
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Interpretation Functor for LawvereTreeERCat

Defines the faithful interpretation functor
`treeErInterpFunctor : LawvereTreeERCat ⥤ Type` sending arity `n` to
`Fin n → BT`, and the faithful inclusion functor
`treeErInclusion : LawvereTreeERCat ⥤ LawvereBTQuotCat` that realizes
tree-ER morphisms as BT morphisms via `.val` unwrapping.  The
inclusion functor is the bootstrapping tool for the "prove in
`LawvereBTQuotCat`, lift via faithfulness" transport pattern.
-/

namespace GebLean

open CategoryTheory

end GebLean
```

- [ ] **Step 2: Add lifted interpretation simp lemmas**

Insert inside the namespace:

```lean
@[simp] theorem TreeERMorNQuo.interp_id {n : ℕ}
    (ctx : Fin n → BT.{0}) :
    (TreeERMorNQuo.id n).interp ctx = ctx := by
  unfold TreeERMorNQuo.id TreeERMorNQuo.interp
  simp [TreeERMorN.interp_id]

@[simp] theorem TreeERMorNQuo.interp_comp {n m k : ℕ}
    (f : TreeERMorNQuo n m) (g : TreeERMorNQuo m k)
    (ctx : Fin n → BT.{0}) :
    (TreeERMorNQuo.comp f g).interp ctx =
      g.interp (f.interp ctx) := by
  refine Quotient.ind (motive := fun f =>
    (TreeERMorNQuo.comp f g).interp ctx =
      g.interp (f.interp ctx)) ?_ f
  refine Quotient.ind (motive := fun g =>
    (TreeERMorNQuo.comp _ g).interp ctx =
      g.interp _) ?_ g
  intros g_raw f_raw
  rfl
```

- [ ] **Step 3: Define `treeErInterpFunctor` and prove it faithful**

```lean
/-- The interpretation functor from `LawvereTreeERCat` into `Type`.
Sends arity `n` to `Fin n → BT` and each morphism class to the
extensional function it computes. -/
def treeErInterpFunctor : LawvereTreeERCat ⥤ Type where
  obj n := Fin n → BT.{0}
  map f := f.interp
  map_id n := by
    funext ctx
    exact TreeERMorNQuo.interp_id ctx
  map_comp f g := by
    funext ctx
    exact TreeERMorNQuo.interp_comp f g ctx

/-- `treeErInterpFunctor` is faithful: the setoid relation on
morphism tuples is precisely the kernel of the interpretation, so
equal interpretations force equal quotient classes. -/
instance : treeErInterpFunctor.Faithful where
  map_injective {n m} {f g} h := by
    refine Quotient.ind₂ (motive := fun f g =>
      treeErInterpFunctor.map f = treeErInterpFunctor.map g →
        f = g) ?_ f g
    intros f_raw g_raw heq
    exact Quotient.sound
      (s := treeErMorNSetoid n m)
      (fun ctx => congrFun heq ctx)
    exact h
```

- [ ] **Step 4: Build to verify**

Run: `lake build GebLean.LawvereTreeERInterp`
Expected: PASS, no warnings.

- [ ] **Step 5: Commit**

```bash
git add GebLean/LawvereTreeERInterp.lean
git commit -m "Add treeErInterpFunctor with Faithful instance"
```

---

## Task 13: Faithful inclusion into `LawvereBTQuotCat`

**Files:**

* Modify: `GebLean/LawvereTreeERInterp.lean`

- [ ] **Step 1: Define the inclusion on tuples**

Insert after the functor definitions:

```lean
/-- Unwrap a tree-ER tuple into a raw BT tuple. -/
def TreeERMorN.toBTMorN {n m : ℕ}
    (f : TreeERMorN n m) : BTMorN n m :=
  fun i => (f i).val

/-- Wrapping preserves the setoid relation: if two tree-ER tuples
are extensionally equal at every context (as tree-ER functions),
their BT unwraps are extensionally equal as BT functions. -/
theorem TreeERMorN.toBTMorN_sound {n m : ℕ}
    (f g : TreeERMorN n m)
    (h : ∀ ctx : Fin n → BT.{0},
      f.interp ctx = g.interp ctx) :
    ∀ ctx : Fin n → BT.{0},
      (f.toBTMorN).interpU ctx =
        (g.toBTMorN).interpU ctx := by
  intro ctx
  funext i
  exact congrFun (h ctx) i
```

- [ ] **Step 2: Lift to the quotient**

```lean
/-- The functor forgetting the depth-≤-2 constraint on tree-ER
morphisms, landing in `LawvereBTQuotCat`. -/
def TreeERMorNQuo.toBTMorNQuo {n m : ℕ}
    (f : TreeERMorNQuo n m) : BTMorNQuo n m :=
  Quotient.lift
    (s := treeErMorNSetoid n m)
    (fun f' => Quotient.mk _ f'.toBTMorN)
    (fun _ _ h =>
      Quotient.sound
        (fun ctx => funext (fun i => congrFun (h ctx) i)))
    f
```

- [ ] **Step 3: Build intermediate**

Run: `lake build GebLean.LawvereTreeERInterp`
Expected: PASS, no warnings.

- [ ] **Step 4: Define the inclusion functor**

```lean
/-- Inclusion of `LawvereTreeERCat` into `LawvereBTQuotCat`.
Forgets the depth bound; morphisms of tree-ER are realized as
morphisms of BT.  Faithful (Step 5). -/
def treeErInclusion : LawvereTreeERCat ⥤ LawvereBTQuotCat where
  obj n := n
  map := TreeERMorNQuo.toBTMorNQuo
  map_id n := by
    refine Quotient.ind (motive := fun _ => _) ?_
      (TreeERMorNQuo.id n)
    intro raw
    rfl
  map_comp f g := by
    refine Quotient.ind (motive := fun f => _) ?_ f
    refine Quotient.ind (motive := fun g => _) ?_ g
    intros g_raw f_raw
    rfl
```

The `map_id` and `map_comp` proofs may need additional `rfl`-chaining
via explicit computation.  If they don't close by `rfl` alone, unfold
via `unfold TreeERMorNQuo.toBTMorNQuo BTMorNQuo.id BTMorNQuo.comp`
and simplify.

- [ ] **Step 5: Prove faithfulness of the inclusion**

```lean
instance : treeErInclusion.Faithful where
  map_injective {n m} {f g} h := by
    refine Quotient.ind₂ (motive := fun f g =>
      treeErInclusion.map f = treeErInclusion.map g →
        f = g) ?_ f g
    intros f_raw g_raw heq
    apply Quotient.sound
    intro ctx
    funext i
    -- The quotient-equality `heq` on BTMorNQuo gives an
    -- extensional equality on BT-interpretation, which unpacks to
    -- the required tree-ER interpretation equality.
    have hbt := Quotient.exact heq ctx
    exact congrFun hbt i
    exact h
```

- [ ] **Step 6: Build and verify**

Run: `lake build GebLean.LawvereTreeERInterp`
Expected: PASS, no warnings.

- [ ] **Step 7: Register in `GebLean.lean`**

Insert `import GebLean.LawvereTreeERInterp` after
`import GebLean.LawvereTreeERQuot`.

- [ ] **Step 8: Full-project build**

Run: `lake build`
Expected: PASS, no warnings.

- [ ] **Step 9: Commit**

```bash
git add GebLean/LawvereTreeERInterp.lean GebLean.lean
git commit -m "Add faithful inclusion LawvereTreeERCat to LawvereBTQuotCat"
```

---

## Task 14: Tests for `LawvereTreeER.lean`

**Files:**

* Create: `GebLeanTests/LawvereTreeER.lean`

- [ ] **Step 1: Write the test file with smart-constructor `#guard`s**

```lean
import GebLean.LawvereTreeER

/-!
# Tests for LawvereTreeER

Sanity tests for the tree-native ER smart constructors, the
mutumorphism primitive, and the depth-tier widening lifts.
-/

open GebLean

-- Depth-0 smart constructors compute as expected.
#guard (TreeERMor1_0.leaf (n := 0)).interp
  (fun i : Fin 0 => i.elim0) = BT.leaf

#guard (@TreeERMor1_0.proj 2 0).interp
  (fun i : Fin 2 => if i.val = 0 then BT.leaf
                     else BT.node BT.leaf BT.leaf) =
  BT.leaf

#guard (TreeERMor1_0.branch
          TreeERMor1_0.leaf TreeERMor1_0.leaf
            (n := 0)).interp
  (fun i : Fin 0 => i.elim0) =
  BT.node BT.leaf BT.leaf

-- Widening lifts preserve interpretation.
#guard (TreeERMor1_0.leaf (n := 1)).toDepth2.interp
  (fun _ => BT.leaf) = BT.leaf
```

- [ ] **Step 2: Add the mutumorphism worked example**

Append:

```lean
-- Mutumorphism example: simultaneously compute tree-size and
-- tree-height via `mutuFold` at depth-1.
--
-- At a leaf:      both slots are 0, represented as BT.leaf.
-- At a node l r:  size = 1 + size(l) + size(r), height = 1 +
--                  max(height(l), height(r)).  We encode
--                  0 as `leaf`, and n+1 as `node leaf <n>` (tally).

-- Base function: at leaves, both size and height are "0" (leaf).
def sizeHeightBase : Fin 2 → TreeERMor1_0 1 :=
  fun _ => TreeERMor1_0.leaf

-- Step function (arity 4: left-size, left-height,
-- right-size, right-height): produce (1 + lsize + rsize,
-- 1 + max(lheight, rheight)).  For a sanity test we simplify
-- this to `node leaf <old>` on each slot (i.e., both slots
-- increment by one), ignoring differences between slots.
def sizeHeightStep : Fin 2 → TreeERMor1_0 4 :=
  fun _ => TreeERMor1_0.branch TreeERMor1_0.leaf
    (TreeERMor1_0.proj 0)

def sizeHeightTree : TreeERMor1_0 1 := TreeERMor1_0.proj 0

def sizeHeightMutuFold : TreeERMorN_1 1 2 :=
  TreeERMor1_1.mutuFold sizeHeightBase sizeHeightStep
    sizeHeightTree

-- On the tree `node leaf leaf`, the mutumorphism computes both
-- slots via the step function.
#check
  let tree := BT.node BT.leaf BT.leaf
  (sizeHeightMutuFold 0).interp (fun _ => tree)
```

- [ ] **Step 3: Add depth-tier type-checks**

Append:

```lean
-- A leaf at the depth-0 tier type-checks.
example : TreeERMor1_0 3 := TreeERMor1_0.leaf

-- A leaf widened to depth-1 type-checks.
example : TreeERMor1_1 3 := TreeERMor1_0.leaf.toDepth1

-- A leaf widened to depth-2 type-checks.
example : TreeERMor1 3 := TreeERMor1_0.leaf.toDepth2

-- A fold at depth-1 takes depth-0 arguments and lands in depth-1.
example : TreeERMor1_1 1 :=
  TreeERMor1_1.fold1 TreeERMor1_0.leaf
    (TreeERMor1_0.proj 0) (TreeERMor1_0.proj 0)

-- A nested fold at depth-2 takes depth-1 arguments.
example : TreeERMor1 1 :=
  TreeERMor1.fold1
    (TreeERMor1_1.fold1 TreeERMor1_0.leaf
      (TreeERMor1_0.proj 0) (TreeERMor1_0.proj 0))
    (TreeERMor1_1.proj 0)
    (TreeERMor1_1.proj 0)
```

- [ ] **Step 4: Register in `GebLeanTests.lean`**

Insert `import GebLeanTests.LawvereTreeER` in alphabetical order
after `import GebLeanTests.LawvereBT*` imports and before
`LawvereERArith` or similar.

- [ ] **Step 5: Build and test**

Run: `lake build && lake test`
Expected: PASS, no warnings, all `#guard` checks pass.

- [ ] **Step 6: Commit**

```bash
git add GebLeanTests/LawvereTreeER.lean GebLeanTests.lean
git commit -m "Add LawvereTreeER sanity tests with mutumorphism example"
```

---

## Task 15: Tests for `LawvereTreeERQuot.lean`

**Files:**

* Create: `GebLeanTests/LawvereTreeERQuot.lean`

- [ ] **Step 1: Write the test file**

```lean
import GebLean.LawvereTreeERQuot

/-!
# Tests for LawvereTreeERQuot

Sanity tests for the Category instance and HasChosenFiniteProducts
on LawvereTreeERCat.
-/

open GebLean CategoryTheory

-- Category instance type-checks.
example : Category LawvereTreeERCat := inferInstance

-- HasChosenFiniteProducts type-checks.
example : HasChosenFiniteProducts LawvereTreeERCat := inferInstance

-- Identity composition reduces to identity on a specific example.
example (f : TreeERMorNQuo 2 1) :
    TreeERMorNQuo.comp (TreeERMorNQuo.id 2) f = f :=
  TreeERMorNQuo.id_comp f

-- Right identity holds symmetrically.
example (f : TreeERMorNQuo 2 1) :
    TreeERMorNQuo.comp f (TreeERMorNQuo.id 1) = f :=
  TreeERMorNQuo.comp_id f

-- First projection of a pair on specific inputs.
example (f : TreeERMorNQuo 3 2) (g : TreeERMorNQuo 3 4) :
    TreeERMorNQuo.comp
      (TreeERMorNQuo.pair f g) TreeERMorNQuo.fst = f := by
  -- The fac_fst law on the product, transported to raw composition.
  have := (lawvereTreeERProduct 2 4).fac_fst 3 f g
  convert this using 1
```

- [ ] **Step 2: Register in `GebLeanTests.lean`**

Insert `import GebLeanTests.LawvereTreeERQuot` after the test
module added in Task 14.

- [ ] **Step 3: Build and test**

Run: `lake build && lake test`
Expected: PASS, no warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLeanTests/LawvereTreeERQuot.lean GebLeanTests.lean
git commit -m "Add LawvereTreeERQuot sanity tests"
```

---

## Task 16: Tests for `LawvereTreeERInterp.lean`

**Files:**

* Create: `GebLeanTests/LawvereTreeERInterp.lean`

- [ ] **Step 1: Write the test file**

```lean
import GebLean.LawvereTreeERInterp

/-!
# Tests for LawvereTreeERInterp

Sanity tests for the interpretation functor's faithfulness and the
inclusion functor's faithfulness into `LawvereBTQuotCat`.
-/

open GebLean CategoryTheory

-- Interpretation functor type-checks.
example : LawvereTreeERCat ⥤ Type := treeErInterpFunctor

-- Faithful instance is available.
example : treeErInterpFunctor.Faithful := inferInstance

-- Inclusion functor type-checks.
example : LawvereTreeERCat ⥤ LawvereBTQuotCat :=
  treeErInclusion

-- Inclusion is faithful.
example : treeErInclusion.Faithful := inferInstance

-- Interpretation at arity 1 on a leaf returns leaf.
#guard (treeErInterpFunctor.map
  (Quotient.mk _ (fun _ : Fin 1 =>
    (TreeERMor1.proj (0 : Fin 1))))
  (fun _ => BT.leaf) : Fin 1 → BT.{0}) 0 = BT.leaf
```

- [ ] **Step 2: Register in `GebLeanTests.lean`**

Insert `import GebLeanTests.LawvereTreeERInterp` after
`LawvereTreeERQuot`.

- [ ] **Step 3: Build and test**

Run: `lake build && lake test`
Expected: PASS, no warnings.

- [ ] **Step 4: Commit**

```bash
git add GebLeanTests/LawvereTreeERInterp.lean GebLeanTests.lean
git commit -m "Add LawvereTreeERInterp sanity tests"
```

---

## Task 17: Workstream tracker update

**Files:**

* Modify: `.session/workstreams/lawvere-elementary-recursive.md`

- [ ] **Step 1: Append Phase 4g.1 completion paragraph to Status**

Read the Status section and append (just before the `## Phase 4g`
subsection, or at the very end of the Status section — whichever
preserves the ordering "oldest first"):

```markdown
Phase 4g.1 complete: see `GebLean/LawvereTreeER.lean` for the
depth-stratified `TreeERMor1` subtype family over `BTMor1` with
smart constructors at each tier and mutumorphism exposure via
`mutuFold`; `GebLean/LawvereTreeERQuot.lean` for the quotient
category `LawvereTreeERCat` with `HasChosenFiniteProducts`; and
`GebLean/LawvereTreeERInterp.lean` for the faithful interpretation
functor `treeErInterpFunctor : LawvereTreeERCat ⥤ Type` and the
faithful inclusion `treeErInclusion : LawvereTreeERCat ⥤
LawvereBTQuotCat` that bootstraps the transport-via-faithfulness
pattern for later sub-projects.
```

- [ ] **Step 2: Mark 4g.1 complete in the task checklist**

Find the line `* [ ] 4g.1: Tree-ER core Lawvere theory.` and change
it to:

```markdown
  * [x] 4g.1: Tree-ER core Lawvere theory.
```

- [ ] **Step 3: Build sanity (no-op for the tracker)**

Run: `lake build && lake test`
Expected: PASS.

- [ ] **Step 4: Commit**

```bash
git add .session/workstreams/lawvere-elementary-recursive.md
git commit -m "Mark ER Phase 4g.1 complete in workstream tracker"
```

---

## Self-Review

**Spec coverage:**

- [x] `BTMor1.foldDepth` + reduction lemmas — Task 1.
- [x] `BTMor1.subst_foldDepth_le` lemma (needed for smart-constructor
      comp) — Task 2.
- [x] Three subtype aliases `TreeERMor1_0`, `TreeERMor1_1`,
      `TreeERMor1` + widening lifts — Task 3.
- [x] Depth-0 smart constructors (leaf, branch, proj, comp) — Task 4.
- [x] Depth-1 smart constructors + fold — Task 5.
- [x] Depth-2 smart constructors + fold — Task 6.
- [x] `fold1` + `mutuFold` convenience helpers — Task 7.
- [x] `TreeERMor1.interp` + `TreeERMorN` + operations — Task 8.
- [x] `treeErMorNSetoid`, `TreeERMorNQuo`, identity, composition —
      Task 9.
- [x] `Category LawvereTreeERCat` instance — Task 10.
- [x] `HasChosenFiniteProducts LawvereTreeERCat` — Task 11.
- [x] `treeErInterpFunctor` + Faithful — Task 12.
- [x] `treeErInclusion` + Faithful — Task 13.
- [x] Test module for LawvereTreeER (smart constructors,
      mutumorphism) — Task 14.
- [x] Test module for LawvereTreeERQuot — Task 15.
- [x] Test module for LawvereTreeERInterp — Task 16.
- [x] Tracker update — Task 17.

**Placeholder scan:**

* Task 2's `Step 3` leaves one `sorry` in the fold-case substitution
  proof; this is explicitly flagged as a placeholder the implementer
  must fill by following the decomposition pattern described.  The
  `sorry` must be eliminated before committing Task 2.
* Task 11's `Step 3` has a `sorry` in the `uniq` proof, explicitly
  flagged as a placeholder to be filled by case-splitting on
  `i.val < n`.  Step 4–5 spell out how to eliminate it.  Same
  commitment policy: must be gone before the Task 11 commit.
* Task 14's mutumorphism worked-example code includes a `#check` on
  a substantive expression rather than a `#guard`.  This is
  intentional — we verify type-checking and delegate runtime
  verification to other `#guard`s in the file — but an implementer
  may optionally promote the `#check` to a `#guard` with a concrete
  expected value if tractable.

**Type consistency:**

* `TreeERMor1_0`, `TreeERMor1_1`, `TreeERMor1` have stable signatures
  `ℕ → Type`.
* Smart-constructor names follow a uniform pattern `<Tier>.<op>` with
  `leaf`, `branch`, `proj`, `comp`, `fold`, `fold1`, `mutuFold` used
  consistently across tiers.
* `TreeERMorN`, `TreeERMorN_1` are distinguished by tier; `TreeERMorN`
  (no tier subscript) means the depth-≤-2 tuple type at the top
  level.
* `LawvereTreeERCat := ℕ` used consistently.
* `treeErInterpFunctor` and `treeErInclusion` (lowercase `er`)
  consistent with the existing project convention (`erInterpFunctor`,
  etc.).

No inconsistencies flagged.
