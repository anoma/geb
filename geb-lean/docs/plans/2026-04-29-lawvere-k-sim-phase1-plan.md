# Lawvere K^sim Hierarchy: Phase 1 Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Implement the foundational structures of the K^sim
simultaneous-recursion hierarchy in Lean 4 — the term language
`KMor1` / `KMorN`, the level function, the interpretation into
ℕ, the extensional-equality quotient with `Category` instance,
the Lawvere-theory finite-product structure, and the
depth-restricted full subcategory `KSimMor d`.

**Architecture:** Three new files paralleling the existing
`LawvereER*` family. `GebLean/LawvereKSim.lean` defines the
term language and the level function.
`GebLean/LawvereKSimInterp.lean` defines the interpretation
into ℕ-valued functions and the standard `@[simp]` lemmas.
`GebLean/LawvereKSimQuot.lean` defines the
extensional-equality quotient, the `Category` instance, the
Lawvere finite-product structure, and the depth-restricted
subcategory `KSimMor d`.  Tests live under `GebLeanTests/`.

**Tech Stack:** Lean 4, mathlib, `lake build`, `lake test`.
Project conventions per `CLAUDE.md`: no `sorry`, no
`admit`, no warnings, `autoImplicit = false`,
`relaxedAutoImplicit = false`, no `noncomputable`, no
`Classical`.  Bottom-up named-composite discipline; P10
interpret-and-verify discipline.

---

## Reference

- **Design document:** `docs/lawvere-k-sim-hierarchy.md`.
  Sections of particular relevance: "Lean Structural
  Design" (file layout, `KMor1` grammar, level computation,
  interpretation, quotient), "Phase 1 — The K^sim
  Hierarchy as a Category" (deliverable specification), and
  the design principles **P1 – P10**.
- **Parallel implementation:** `GebLean/LawvereER.lean`,
  `GebLean/LawvereERInterp.lean`,
  `GebLean/LawvereERQuot.lean`.  Mirror these where the
  design doc says "parallel to ERMor1 / ERMorN".  In
  particular: `ERMorN n m := Fin m → ERMor1 n` is the
  shape we mirror as `KMorN n m := Fin m → KMor1 n`.
- **Project conventions:** `CLAUDE.md`.  Specifically the
  "Workflow" and "Code Style" sections; the workflow
  rule "Always run `lake build` after edits" applies to
  every step.  Tests live under `GebLeanTests/`; the test
  driver registered in `lakefile.toml` runs them via
  `lake test`.
- **Worktree:** This plan is intended to be executed in a
  dedicated worktree.  Create one before starting via
  `superpowers:using-git-worktrees`; the base branch is
  `terence/develop`.

## File Structure

- **Create:** `GebLean/LawvereKSim.lean` — `KMor1`
  inductive, `KMorN` abbreviation, `KMor1.level`,
  `KMorN.levelN`, monotonicity lemmas, derived
  instances (`Inhabited`, `DecidableEq`, `Repr`).  Plus
  `KMorN.id`, `KMorN.terminal`, `KMorN.fst`, `KMorN.snd`,
  `KMorN.pair`, `KMorN.comp` per the `ERMorN` pattern.

- **Create:** `GebLean/LawvereKSimInterp.lean` —
  `KMor1.interp`, `KMorN.interp`, `@[simp]` interp lemmas
  for each `KMor1` constructor.

- **Create:** `GebLean/LawvereKSimQuot.lean` —
  `KMor1.ExtEq`, the equivalence-relation proof,
  `KMor1.QuotCat`, the `Category` instance, the Lawvere
  finite-product structure, `KSimMor d`, the inclusion
  functors `KSimMor d → KSimMor (d+1)`.

- **Create:** `GebLeanTests/LawvereKSim.lean`,
  `GebLeanTests/LawvereKSimInterp.lean`,
  `GebLeanTests/LawvereKSimQuot.lean` — `#guard`
  arithmetic-function checks and (optionally) Plausible
  property tests.

- **Modify:** `GebLean.lean` — re-export the three new
  modules so the public surface includes them.

---

## Tasks

### Task 1: `KMor1` inductive type with derived instances

**Files:**

- Create: `GebLean/LawvereKSim.lean`

- [ ] **Step 1: Create the module skeleton.**

```lean
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic

/-!
# Lawvere theory of the K^sim hierarchy: term language

This module defines `KMor1 : ℕ → Type`, the type family of
K^sim single-output morphisms (one per arity), together with
`KMorN`, the multi-output Lawvere-theory wrapper.  The level
function `KMor1.level` and its `KMorN`-counterpart
`KMor1.levelN` are also defined here.  Interpretation into
`ℕ` lives in `LawvereKSimInterp.lean`; the extensional
quotient in `LawvereKSimQuot.lean`.

See `docs/lawvere-k-sim-hierarchy.md` for the canonical
mathematical reference and design principles P1 – P10.
-/

namespace GebLean
```

- [ ] **Step 2: Define `KMor1` inductive.**

Add the inductive definition immediately after the
`namespace GebLean` line.  The shape mirrors §"Lean
Structural Design" / "Generator inventory for `KMor1`" of
the design doc.

```lean
/-- The K^sim term language at arity `n`: K^sim
single-output morphisms representing functions `ℕ^n → ℕ`.

Generators per `docs/lawvere-k-sim-hierarchy.md`:
`zero`, `succ`, `proj`, `comp`, `simrec`, `raise`.  Per P8,
`simrec` carries an output index plus base and step
families written as `KMorN`-shaped values; the families
are unfolded inline as `Fin (k+1) → KMor1 _` because
`KMorN` itself is defined later as an abbreviation. -/
inductive KMor1 : ℕ → Type where
  /-- Constant `0` at any arity. -/
  | zero {n : ℕ} : KMor1 n
  /-- Successor function (arity `1`). -/
  | succ : KMor1 1
  /-- The `i`-th projection out of `n` arguments. -/
  | proj {n : ℕ} (i : Fin n) : KMor1 n
  /-- Composition: apply a `b`-ary morphism to the
  results of `b` `a`-ary morphisms. -/
  | comp {a b : ℕ} (f : KMor1 b)
      (gs : Fin b → KMor1 a) : KMor1 a
  /-- Simultaneous primitive recursion at output index
  `i`, with system size `k+1`, base-case family `h`,
  and step-function family `g`.  Produces a morphism
  of arity `a+1` (one slot for the recursion variable
  followed by `a` slots for the parameter list). -/
  | simrec {a k : ℕ}
      (i : Fin (k+1))
      (h : Fin (k+1) → KMor1 a)
      (g : Fin (k+1) → KMor1 (a + 1 + (k + 1))) :
      KMor1 (a + 1)
  /-- Level-bumping marker (no operational effect on
  `interp`; lifts a term's structural level by one). -/
  | raise {n : ℕ} (f : KMor1 n) : KMor1 n
  deriving Inhabited, DecidableEq, Repr
```

- [ ] **Step 3: Close the namespace.**

Add at the end of the file:

```lean
end GebLean
```

- [ ] **Step 4: Run `lake build` to verify the module
  compiles cleanly.**

Run: `lake build GebLean.LawvereKSim`
Expected: success, no warnings.

If `deriving Repr` or `deriving DecidableEq` fails for
indexed-inductive reasons, drop the failing one from the
`deriving` clause and add a manual instance after the
declaration.  Repr in particular is sometimes finicky for
indexed inductives; if unavoidable, define a
`KMor1.repr` helper and tag with `instance : Repr
(KMor1 n) := ⟨KMor1.repr⟩`.

- [ ] **Step 5: Add the `@[ext]` attribute for the
  inductive.**

`KMor1` is an inductive, so `@[ext]` would normally apply
to a structure rather than the inductive itself.  For
`KMor1`, what we typically want is an extensionality
*lemma* characterizing equality of two terms with the same
constructor.  Skip this step if the auto-derived
`DecidableEq` already provides what we need.

- [ ] **Step 6: Run `lake build` once more.**

Run: `lake build GebLean.LawvereKSim`
Expected: success, no warnings.

- [ ] **Step 7: Commit.**

```bash
git add GebLean/LawvereKSim.lean
git commit -m "Add KMor1 inductive for K^sim hierarchy"
```

---

### Task 2: `KMorN` abbreviation and basic operations

**Files:**

- Modify: `GebLean/LawvereKSim.lean`

- [ ] **Step 1: Add `KMorN` abbreviation and basic
  operations under the `namespace GebLean` block, after
  the `KMor1` inductive.**

```lean
/-- Multi-output K^sim Lawvere-theory wrapper:
`KMorN n m` represents a morphism `ℕ^n → ℕ^m` as a
family of `m` single-output morphisms.  Mirrors
`ERMorN`'s definition. -/
abbrev KMorN (n m : ℕ) : Type := Fin m → KMor1 n

/-- Identity morphism on `n` arguments: the family of
`n` projections. -/
def KMorN.id (n : ℕ) : KMorN n n :=
  fun i => KMor1.proj i

/-- Terminal morphism `ℕ^n → ℕ^0`: the empty family. -/
def KMorN.terminal (n : ℕ) : KMorN n 0 :=
  Fin.elim0

/-- First projection `ℕ^(n+m) → ℕ^n`. -/
def KMorN.fst {n m : ℕ} : KMorN (n + m) n :=
  fun i => KMor1.proj (Fin.castAdd m i)

/-- Second projection `ℕ^(n+m) → ℕ^m`. -/
def KMorN.snd {n m : ℕ} : KMorN (n + m) m :=
  fun i => KMor1.proj (Fin.natAdd n i)

/-- Pairing of two morphisms with shared domain: given
`f : KMorN k n` and `g : KMorN k m`, produce
`⟨f, g⟩ : KMorN k (n + m)`. -/
def KMorN.pair {k n m : ℕ}
    (f : KMorN k n) (g : KMorN k m) : KMorN k (n + m) :=
  fun i =>
    if h : i.val < n then
      f ⟨i.val, h⟩
    else
      g ⟨i.val - n, by
        rcases i with ⟨v, hv⟩
        omega⟩

/-- Composition of multi-output morphisms: `f ∘ g`
where `g : KMorN n m` and `f : KMorN m k`. -/
def KMorN.comp {n m k : ℕ}
    (f : KMorN m k) (g : KMorN n m) : KMorN n k :=
  fun i => KMor1.comp (f i) g
```

The `KMorN.pair` definition requires `omega` to discharge
the index arithmetic; if the project's `omega` is
unavailable here, replace with an explicit `Nat.sub_lt`
proof.

- [ ] **Step 2: Run `lake build`.**

Run: `lake build GebLean.LawvereKSim`
Expected: success, no warnings.

- [ ] **Step 3: Commit.**

```bash
git add GebLean/LawvereKSim.lean
git commit -m "Add KMorN abbreviation and basic operations"
```

---

### Task 3: `KMor1.level` and `KMorN.levelN` functions

**Files:**

- Modify: `GebLean/LawvereKSim.lean`

- [ ] **Step 1: Add the `level` function under the
  existing definitions in the `namespace GebLean`
  block.**

```lean
/-- Structural level of a `KMor1` term per design
principle **P2**: `simrec` and `raise` each add one
to the maximum-children level; composition takes the
maximum without adding. -/
def KMor1.level : {n : ℕ} → KMor1 n → ℕ
  | _, .zero        => 0
  | _, .succ        => 0
  | _, .proj _      => 0
  | _, .comp f gs   =>
      max (KMor1.level f)
        (Finset.univ.sup (fun i => (gs i).level))
  | _, .simrec _ h g =>
      max (Finset.univ.sup (fun i => (h i).level))
          (Finset.univ.sup (fun i => (g i).level)) + 1
  | _, .raise f      => f.level + 1

/-- Level of a multi-output `KMorN` family: the
maximum level over the family. -/
def KMorN.levelN {n m : ℕ} (f : KMorN n m) : ℕ :=
  Finset.univ.sup (fun i => (f i).level)
```

- [ ] **Step 2: Run `lake build`.**

Run: `lake build GebLean.LawvereKSim`
Expected: success, no warnings.

- [ ] **Step 3: Add a depth-monotonicity lemma.**

Per design principle **P4**, the depth-restricted
subcategory `KSimMor d` is the *quotient image*; the
underlying syntactic notion `level f ≤ d` is monotone
under `≤` on `d`.  Add the lemma:

```lean
theorem KMor1.level_le_succ {n : ℕ} (f : KMor1 n)
    {d : ℕ} (h : f.level ≤ d) : f.level ≤ d + 1 := by
  exact Nat.le_succ_of_le h

theorem KMorN.levelN_le_succ {n m : ℕ}
    (f : KMorN n m) {d : ℕ} (h : f.levelN ≤ d) :
    f.levelN ≤ d + 1 :=
  Nat.le_succ_of_le h
```

- [ ] **Step 4: Run `lake build`.**

Run: `lake build GebLean.LawvereKSim`
Expected: success, no warnings.

- [ ] **Step 5: Commit.**

```bash
git add GebLean/LawvereKSim.lean
git commit -m "Add KMor1.level and KMorN.levelN with monotonicity"
```

---

### Task 4: Interpretation module skeleton

**Files:**

- Create: `GebLean/LawvereKSimInterp.lean`

- [ ] **Step 1: Create the module skeleton with imports
  and namespace.**

```lean
import GebLean.LawvereKSim
import Mathlib.Data.Fin.VecNotation

/-!
# Interpretation of K^sim morphisms into ℕ

This module defines `KMor1.interp` (and `KMorN.interp`),
mapping each K^sim morphism to its corresponding
ℕ-valued function.  Standard `@[simp]` lemmas characterize
the interpretation per generator.  Per design principle
**P10**, every named composite is paired with an interp
lemma; this discipline begins here for the constructors
themselves and continues through the entire downstream
development.
-/

namespace GebLean
```

- [ ] **Step 2: Add `KMor1.interp` definition.**

```lean
/-- Standard interpretation of a `KMor1` term as a
function `(Fin n → ℕ) → ℕ`.  Each constructor is
interpreted pointwise; `simrec` runs the simultaneous
recursion straightforwardly via `Nat.rec` on the
recursion variable, building the (k+1)-vector of
intermediate values and selecting the requested
output. -/
def KMor1.interp : {n : ℕ} → KMor1 n →
    (Fin n → ℕ) → ℕ
  | _, .zero,   _   => 0
  | _, .succ,   ctx => (ctx 0).succ
  | _, .proj i, ctx => ctx i
  | _, .comp f gs, ctx =>
      f.interp (fun i => (gs i).interp ctx)
  | _, .simrec (a := a) (k := k) i h g, ctx =>
      let recVar : ℕ := ctx 0
      let params : Fin a → ℕ :=
        fun j => ctx (Fin.succ j)
      let stepVec : ℕ → (Fin (k+1) → ℕ) :=
        Nat.rec
          (fun j => (h j).interp params)
          (fun n prev =>
            fun j =>
              let stepCtx : Fin (a + 1 + (k + 1)) → ℕ :=
                fun idx =>
                  if h₁ : idx.val < a + 1 then
                    if h₂ : idx.val = 0 then
                      n
                    else
                      params ⟨idx.val - 1, by
                        rcases idx with ⟨v, hv⟩
                        omega⟩
                  else
                    prev ⟨idx.val - (a + 1), by
                      rcases idx with ⟨v, hv⟩
                      omega⟩
              (g j).interp stepCtx)
      stepVec recVar i
  | _, .raise f, ctx => f.interp ctx
```

The simrec interp computes the vector of intermediate
values via `Nat.rec` on the recursion variable, then
selects the requested output.  The step's context
arrangement places (recursion-variable-value, parameters,
prev-vector) in slots `[0]`, `[1..a]`, `[a+1..a+1+(k+1)]`
respectively.

If the slot-arrangement arithmetic gets thorny, factor the
step's context construction into a separate helper
function and prove its properties incrementally.

- [ ] **Step 3: Close the namespace.**

```lean
end GebLean
```

- [ ] **Step 4: Run `lake build`.**

Run: `lake build GebLean.LawvereKSimInterp`
Expected: success, no warnings.

- [ ] **Step 5: Commit.**

```bash
git add GebLean/LawvereKSimInterp.lean
git commit -m "Add KMor1.interp definition"
```

---

### Task 5: Standard simp interp lemmas (atomic constructors)

**Files:**

- Modify: `GebLean/LawvereKSimInterp.lean`

- [ ] **Step 1: Add `@[simp]` lemmas for the atomic
  constructors `zero`, `succ`, `proj`, `raise`.**

```lean
/-- Interpretation of `zero`. -/
@[simp] theorem KMor1.interp_zero {n : ℕ}
    (ctx : Fin n → ℕ) :
    (KMor1.zero (n := n)).interp ctx = 0 :=
  rfl

/-- Interpretation of `succ`. -/
@[simp] theorem KMor1.interp_succ
    (ctx : Fin 1 → ℕ) :
    KMor1.succ.interp ctx = (ctx 0).succ :=
  rfl

/-- Interpretation of `proj`. -/
@[simp] theorem KMor1.interp_proj {n : ℕ}
    (i : Fin n) (ctx : Fin n → ℕ) :
    (KMor1.proj i).interp ctx = ctx i :=
  rfl

/-- Interpretation of `raise` is identity on the
underlying interp; `raise` is a level marker only. -/
@[simp] theorem KMor1.interp_raise {n : ℕ}
    (f : KMor1 n) (ctx : Fin n → ℕ) :
    (KMor1.raise f).interp ctx = f.interp ctx :=
  rfl
```

- [ ] **Step 2: Run `lake build`.**

Run: `lake build GebLean.LawvereKSimInterp`
Expected: success, no warnings.

- [ ] **Step 3: Commit.**

```bash
git add GebLean/LawvereKSimInterp.lean
git commit -m "Add atomic interp simp lemmas (zero, succ, proj, raise)"
```

---

### Task 6: `comp` interp simp lemma

**Files:**

- Modify: `GebLean/LawvereKSimInterp.lean`

- [ ] **Step 1: Add the `comp` interp lemma.**

```lean
/-- Interpretation of composition: apply `f`'s
interpretation to the family of `gs`'s interpretations
at the given context. -/
@[simp] theorem KMor1.interp_comp
    {a b : ℕ} (f : KMor1 b) (gs : Fin b → KMor1 a)
    (ctx : Fin a → ℕ) :
    (KMor1.comp f gs).interp ctx
      = f.interp (fun i => (gs i).interp ctx) :=
  rfl
```

- [ ] **Step 2: Run `lake build`.**

Run: `lake build GebLean.LawvereKSimInterp`
Expected: success, no warnings.

- [ ] **Step 3: Commit.**

```bash
git add GebLean/LawvereKSimInterp.lean
git commit -m "Add KMor1.interp_comp simp lemma"
```

---

### Task 7: `simrec` interp simp lemma

**Files:**

- Modify: `GebLean/LawvereKSimInterp.lean`

- [ ] **Step 1: Add a definitional unfolding theorem
  for `simrec`'s interp.**

The full simrec interp is intricate; rather than `rfl`,
we expose its behaviour at the recursion-variable
boundary via two equations.  Add helper definitions
plus the boundary equations:

```lean
/-- Helper: the (k+1)-component vector of intermediate
values produced by simrec when the recursion variable
is `n`.  Defined by structural recursion on `n`. -/
def KMor1.simrecVec {a k : ℕ}
    (h : Fin (k+1) → KMor1 a)
    (g : Fin (k+1) → KMor1 (a + 1 + (k + 1)))
    (params : Fin a → ℕ) : ℕ → (Fin (k+1) → ℕ)
  | 0 => fun j => (h j).interp params
  | n + 1 =>
    let prev := KMor1.simrecVec h g params n
    fun j =>
      let stepCtx : Fin (a + 1 + (k + 1)) → ℕ :=
        fun idx =>
          if h₁ : idx.val < a + 1 then
            if h₂ : idx.val = 0 then
              n
            else
              params ⟨idx.val - 1, by
                rcases idx with ⟨v, hv⟩
                omega⟩
          else
            prev ⟨idx.val - (a + 1), by
              rcases idx with ⟨v, hv⟩
              omega⟩
      (g j).interp stepCtx

/-- The simrec's interp expressed via `simrecVec`. -/
@[simp] theorem KMor1.interp_simrec
    {a k : ℕ}
    (i : Fin (k+1))
    (h : Fin (k+1) → KMor1 a)
    (g : Fin (k+1) → KMor1 (a + 1 + (k + 1)))
    (ctx : Fin (a + 1) → ℕ) :
    (KMor1.simrec i h g).interp ctx
      = KMor1.simrecVec h g
          (fun j => ctx (Fin.succ j))
          (ctx 0) i := by
  rfl
```

The `rfl` may not type-check directly if the original
`KMor1.interp` definition for `simrec` doesn't share
exactly the same shape as `KMor1.simrecVec`.  In that
case, refactor the original `KMor1.interp` to call
`KMor1.simrecVec` and the boundary equations become
`rfl`.  This refactoring is preferred (DRY) — the same
helper computation should not be defined in two places.

- [ ] **Step 2: Run `lake build`.**

Run: `lake build GebLean.LawvereKSimInterp`
Expected: success, no warnings.

If the refactor is required: edit the `simrec` case of
`KMor1.interp` to read

```lean
  | _, .simrec (a := a) (k := k) i h g, ctx =>
      KMor1.simrecVec h g
        (fun j => ctx (Fin.succ j))
        (ctx 0) i
```

and rerun `lake build`.

- [ ] **Step 3: Add boundary equations for `simrecVec`.**

```lean
@[simp] theorem KMor1.simrecVec_zero
    {a k : ℕ}
    (h : Fin (k+1) → KMor1 a)
    (g : Fin (k+1) → KMor1 (a + 1 + (k + 1)))
    (params : Fin a → ℕ) (j : Fin (k+1)) :
    KMor1.simrecVec h g params 0 j
      = (h j).interp params := rfl

@[simp] theorem KMor1.simrecVec_succ
    {a k : ℕ}
    (h : Fin (k+1) → KMor1 a)
    (g : Fin (k+1) → KMor1 (a + 1 + (k + 1)))
    (params : Fin a → ℕ) (n : ℕ) (j : Fin (k+1)) :
    KMor1.simrecVec h g params (n + 1) j
      = (g j).interp
          (fun idx =>
            if h₁ : idx.val < a + 1 then
              if h₂ : idx.val = 0 then
                n
              else
                params ⟨idx.val - 1, by
                  rcases idx with ⟨v, hv⟩
                  omega⟩
            else
              KMor1.simrecVec h g params n
                ⟨idx.val - (a + 1), by
                  rcases idx with ⟨v, hv⟩
                  omega⟩) := rfl
```

- [ ] **Step 4: Run `lake build`.**

Run: `lake build GebLean.LawvereKSimInterp`
Expected: success, no warnings.

- [ ] **Step 5: Commit.**

```bash
git add GebLean/LawvereKSimInterp.lean
git commit -m "Add KMor1.simrecVec helper and interp_simrec lemma"
```

---

### Task 8: `KMorN.interp` and its operation lemmas

**Files:**

- Modify: `GebLean/LawvereKSimInterp.lean`

- [ ] **Step 1: Add `KMorN.interp` definition.**

```lean
/-- Multi-output interpretation: apply each component's
interp at the given context. -/
def KMorN.interp {n m : ℕ} (f : KMorN n m)
    (ctx : Fin n → ℕ) : Fin m → ℕ :=
  fun i => (f i).interp ctx
```

- [ ] **Step 2: Add interp lemmas for `KMorN.id`,
  `.terminal`, `.fst`, `.snd`, `.pair`, `.comp`.**

```lean
@[simp] theorem KMorN.interp_id (n : ℕ)
    (ctx : Fin n → ℕ) :
    (KMorN.id n).interp ctx = ctx := by
  funext i
  simp [KMorN.id, KMorN.interp]

@[simp] theorem KMorN.interp_terminal (n : ℕ)
    (ctx : Fin n → ℕ) :
    (KMorN.terminal n).interp ctx = Fin.elim0 := by
  funext i
  exact i.elim0

@[simp] theorem KMorN.interp_fst {n m : ℕ}
    (ctx : Fin (n + m) → ℕ) :
    (KMorN.fst (n := n) (m := m)).interp ctx
      = fun i => ctx (Fin.castAdd m i) := by
  funext i
  simp [KMorN.fst, KMorN.interp]

@[simp] theorem KMorN.interp_snd {n m : ℕ}
    (ctx : Fin (n + m) → ℕ) :
    (KMorN.snd (n := n) (m := m)).interp ctx
      = fun i => ctx (Fin.natAdd n i) := by
  funext i
  simp [KMorN.snd, KMorN.interp]

@[simp] theorem KMorN.interp_comp
    {n m k : ℕ}
    (f : KMorN m k) (g : KMorN n m)
    (ctx : Fin n → ℕ) :
    (KMorN.comp f g).interp ctx
      = (f.interp (g.interp ctx)) := by
  funext i
  simp [KMorN.comp, KMorN.interp]
```

- [ ] **Step 3: Run `lake build`.**

Run: `lake build GebLean.LawvereKSimInterp`
Expected: success, no warnings.

- [ ] **Step 4: Commit.**

```bash
git add GebLean/LawvereKSimInterp.lean
git commit -m "Add KMorN.interp and operation lemmas"
```

---

### Task 9: `#guard` tests for KMor1 / KMorN interp

**Files:**

- Create: `GebLeanTests/LawvereKSimInterp.lean`

- [ ] **Step 1: Create the test module.**

```lean
import GebLean.LawvereKSimInterp
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for LawvereKSimInterp

`#guard` sanity tests covering the interpretation of each
`KMor1` generator and `KMorN` operation.
-/

open GebLean

private def ctx0 : Fin 0 → ℕ := Fin.elim0
private def ctx1 (x : ℕ) : Fin 1 → ℕ := fun _ => x
private def ctx2 (x y : ℕ) : Fin 2 → ℕ := ![x, y]
private def ctx3 (x y z : ℕ) : Fin 3 → ℕ := ![x, y, z]

-- zero at the empty context.
#guard (KMor1.zero (n := 0)).interp ctx0 == 0

-- zero at higher arity (P-rule: KMor1.zero is at any arity).
#guard (KMor1.zero (n := 2)).interp (ctx2 5 7) == 0

-- succ of 5.
#guard KMor1.succ.interp (ctx1 5) == 6

-- proj 0 out of (7, 3).
#guard (KMor1.proj (0 : Fin 2)).interp (ctx2 7 3) == 7

-- proj 1 out of (7, 3).
#guard (KMor1.proj (1 : Fin 2)).interp (ctx2 7 3) == 3

-- raise is the same as the underlying term.
#guard (KMor1.raise KMor1.succ).interp (ctx1 5) == 6

-- comp (succ ∘ proj 0) on (7, 3) yields succ 7 = 8.
#guard
  (KMor1.comp KMor1.succ
    (fun _ : Fin 1 => KMor1.proj (0 : Fin 2))).interp
    (ctx2 7 3) == 8
```

- [ ] **Step 2: Run `lake test` to verify the guards.**

Run: `lake test`
Expected: all tests pass.

- [ ] **Step 3: Commit.**

```bash
git add GebLeanTests/LawvereKSimInterp.lean
git commit -m "Add KMor1 interp #guard tests"
```

---

### Task 10: Build a level-1 simrec test (`+`) and verify

**Files:**

- Modify: `GebLeanTests/LawvereKSimInterp.lean`

- [ ] **Step 1: Add a named `+` composite as a
  level-1 simrec, and verify its interpretation.**

```lean
/-- Addition `λ x y. x + y` as a level-1 K^sim
composite: simrec on the second argument with base =
proj 0 (returns x at y = 0) and step = succ ∘ proj
of the previous value. -/
private def addK : KMor1 2 :=
  KMor1.simrec (k := 0) (a := 1)
    (0 : Fin 1)
    (fun _ : Fin 1 => KMor1.proj (0 : Fin 1))
    (fun _ : Fin 1 =>
      KMor1.comp KMor1.succ
        (fun _ : Fin 1 => KMor1.proj (2 : Fin 3)))

#guard addK.interp (ctx2 3 5) == 8
#guard addK.interp (ctx2 0 0) == 0
#guard addK.interp (ctx2 7 1) == 8
#guard addK.level == 1
```

The simrec's recursion variable is the *first* argument of
`addK : KMor1 2`, and per `KMor1.interp`'s convention the
context's slot 0 is the recursion variable.  In the step,
the previous-value vector occupies slots `[a+1 .. a+1+(k+1))`
(here slots `[2 .. 3)`), so `proj 2` picks the previous
value of the single-output simrec.

- [ ] **Step 2: Run `lake test`.**

Run: `lake test`
Expected: all tests pass.  In particular,
`addK.interp (ctx2 3 5) == 8` exercises the `simrec`
interp at non-zero recursion-variable values.

- [ ] **Step 3: Commit.**

```bash
git add GebLeanTests/LawvereKSimInterp.lean
git commit -m "Add addK level-1 simrec test in LawvereKSimInterp tests"
```

---

### Task 11: Module skeleton for `LawvereKSimQuot.lean`

**Files:**

- Create: `GebLean/LawvereKSimQuot.lean`

- [ ] **Step 1: Create the module skeleton.**

```lean
import GebLean.LawvereKSimInterp
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts

/-!
# Extensional-equality quotient and Lawvere structure

This module defines the extensional-equality relation
`KMor1.ExtEq` on K^sim morphisms, the quotient category
`KMor1.QuotCat`, the Lawvere finite-product structure, and
the depth-restricted full subcategory `KSimMor d` per
design principle **P4**.
-/

namespace GebLean
```

- [ ] **Step 2: Add the closing `end GebLean`.**

```lean
end GebLean
```

- [ ] **Step 3: Run `lake build`.**

Run: `lake build GebLean.LawvereKSimQuot`
Expected: success, no warnings.

- [ ] **Step 4: Commit.**

```bash
git add GebLean/LawvereKSimQuot.lean
git commit -m "Add LawvereKSimQuot module skeleton"
```

---

### Task 12: `KMorN.ExtEq` setoid (multi-output)

**Files:**

- Modify: `GebLean/LawvereKSimQuot.lean`

The Lawvere-theory quotient is built at the *multi-output*
level, not per `KMor1` arity, mirroring the existing
`erMorNSetoid` in `GebLean/LawvereERQuot.lean`.  The
single setoid lifts cleanly under `Quotient.lift₂` for
composition; per-component setoids would require
non-constructive `Quotient.choice` for the family-to-
quotient swap.

- [ ] **Step 1: Add `kMorNSetoid` defining extensional
  equality on multi-output K^sim morphisms.**

```lean
/-- Extensional equality on multi-output K^sim
morphisms.  Two `f, g : KMorN n m` are equivalent iff
their interpretations agree at every context (and so
agree component-wise). -/
def kMorNSetoid (n m : ℕ) : Setoid (KMorN n m) where
  r f g := ∀ ctx : Fin n → ℕ, f.interp ctx = g.interp ctx
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h ctx => (h ctx).symm
    trans := fun h1 h2 ctx =>
      (h1 ctx).trans (h2 ctx)
  }
```

- [ ] **Step 2: Run `lake build`.**

Run: `lake build GebLean.LawvereKSimQuot`
Expected: success, no warnings.

- [ ] **Step 3: Commit.**

```bash
git add GebLean/LawvereKSimQuot.lean
git commit -m "Add kMorNSetoid for K^sim quotient category"
```

---

### Task 13: `KMorNQuo` quotient type with `id` and `comp`

**Files:**

- Modify: `GebLean/LawvereKSimQuot.lean`

- [ ] **Step 1: Define `KMorNQuo` and lifted operations.**

```lean
/-- Quotient morphism type for the K^sim Lawvere theory:
equivalence classes of `KMorN n m` tuples under
extensional equality. -/
def KMorNQuo (n m : ℕ) : Type :=
  Quotient (kMorNSetoid n m)

/-- The identity morphism in the quotient category: the
equivalence class of the tuple of projections. -/
def KMorNQuo.id (n : ℕ) : KMorNQuo n n :=
  Quotient.mk (kMorNSetoid n n) (KMorN.id n)

/-- Composition of quotient morphisms, lifted from
`KMorN.comp` via `Quotient.lift₂`.  Well-definedness
follows from the fact that extensionally equal tuples
compose to extensionally equal results. -/
def KMorNQuo.comp {n m k : ℕ}
    (f : KMorNQuo n m) (g : KMorNQuo m k) :
    KMorNQuo n k :=
  Quotient.lift₂
    (s₁ := kMorNSetoid n m)
    (s₂ := kMorNSetoid m k)
    (fun f' g' =>
      Quotient.mk (kMorNSetoid n k)
        (KMorN.comp g' f'))
    (fun fa fb ga gb hf hg =>
      Quotient.sound
        (s := kMorNSetoid n k)
        (fun ctx => by
          simp only [KMorN.interp_comp]
          rw [hf ctx, hg (fa.interp ctx)]))
    f g
```

The pattern mirrors `ERMorNQuo.comp` in
`GebLean/LawvereERQuot.lean`.  The argument order to
`KMorN.comp` is `g' f'` (post-composition) because the
underlying `KMorN.comp` is defined as `f ∘ g` for
`g : KMorN n m`, `f : KMorN m k`.

- [ ] **Step 2: Run `lake build`.**

Run: `lake build GebLean.LawvereKSimQuot`
Expected: success, no warnings.

- [ ] **Step 3: Add the category laws as theorems.**

```lean
/-- Left identity: `comp (id n) f = f`. -/
theorem KMorNQuo.id_comp {n m : ℕ}
    (f : KMorNQuo n m) :
    KMorNQuo.comp (KMorNQuo.id n) f = f :=
  Quotient.ind
    (motive := fun f =>
      KMorNQuo.comp (KMorNQuo.id n) f = f)
    (fun f_raw =>
      Quotient.sound
        (s := kMorNSetoid n m)
        (fun ctx => by
          funext i
          simp [KMorN.interp_comp,
                KMorN.interp_id, KMorN.comp]))
    f

/-- Right identity: `comp f (id m) = f`. -/
theorem KMorNQuo.comp_id {n m : ℕ}
    (f : KMorNQuo n m) :
    KMorNQuo.comp f (KMorNQuo.id m) = f :=
  Quotient.ind
    (motive := fun f =>
      KMorNQuo.comp f (KMorNQuo.id m) = f)
    (fun f_raw =>
      Quotient.sound
        (s := kMorNSetoid n m)
        (fun ctx => by
          funext i
          simp [KMorN.interp_comp,
                KMorN.interp_id, KMorN.comp]))
    f

/-- Associativity of composition. -/
theorem KMorNQuo.comp_assoc {n m k l : ℕ}
    (f : KMorNQuo n m) (g : KMorNQuo m k)
    (h : KMorNQuo k l) :
    KMorNQuo.comp (KMorNQuo.comp f g) h
      = KMorNQuo.comp f (KMorNQuo.comp g h) :=
  Quotient.ind
    (motive := fun f =>
      KMorNQuo.comp (KMorNQuo.comp f g) h
        = KMorNQuo.comp f (KMorNQuo.comp g h))
    (fun f_raw =>
      Quotient.ind
        (motive := fun g =>
          KMorNQuo.comp (KMorNQuo.comp
            (Quotient.mk _ f_raw) g) h
          = KMorNQuo.comp (Quotient.mk _ f_raw)
              (KMorNQuo.comp g h))
        (fun g_raw =>
          Quotient.ind
            (motive := fun h =>
              KMorNQuo.comp (KMorNQuo.comp
                (Quotient.mk _ f_raw)
                (Quotient.mk _ g_raw)) h
              = KMorNQuo.comp (Quotient.mk _ f_raw)
                  (KMorNQuo.comp
                    (Quotient.mk _ g_raw) h))
            (fun h_raw =>
              Quotient.sound
                (s := kMorNSetoid n l)
                (fun ctx => by
                  funext i
                  simp [KMorN.interp_comp,
                        KMorN.comp]))
            h)
        g)
    f
```

These three theorems mirror `ERMorNQuo.id_comp`,
`ERMorNQuo.comp_id`, `ERMorNQuo.comp_assoc` in
`GebLean/LawvereERQuot.lean`.  Use that file as a
reference if any of the proof tactics need adjustment.

- [ ] **Step 4: Run `lake build`.**

Run: `lake build GebLean.LawvereKSimQuot`
Expected: success, no warnings.

- [ ] **Step 5: Commit.**

```bash
git add GebLean/LawvereKSimQuot.lean
git commit -m "Add KMorNQuo with id, comp, and category laws"
```

---

### Task 14: Category instance via `LawvereKSimCat = ℕ`

**Files:**

- Modify: `GebLean/LawvereKSimQuot.lean`

- [ ] **Step 1: Define the category-objects type and
  register the `Category` instance, mirroring
  `LawvereERCat` in `LawvereERQuot.lean`.**

```lean
/-- The Lawvere theory of K^sim functions.  Objects
are natural numbers (arities); morphisms are
equivalence classes of `KMorN` tuples under
extensional equality. -/
def LawvereKSimCat := ℕ

instance (n : ℕ) : OfNat LawvereKSimCat n := ⟨(n : ℕ)⟩

instance : BEq LawvereKSimCat :=
  inferInstanceAs (BEq ℕ)

instance : DecidableEq LawvereKSimCat :=
  inferInstanceAs (DecidableEq ℕ)

instance : CategoryTheory.CategoryStruct LawvereKSimCat where
  Hom := KMorNQuo
  id n := KMorNQuo.id n
  comp f g := KMorNQuo.comp f g

instance : CategoryTheory.Category LawvereKSimCat where
  id_comp := KMorNQuo.id_comp
  comp_id := KMorNQuo.comp_id
  assoc := KMorNQuo.comp_assoc
```

- [ ] **Step 2: Run `lake build`.**

Run: `lake build GebLean.LawvereKSimQuot`
Expected: success, no warnings.

- [ ] **Step 3: Commit.**

```bash
git add GebLean/LawvereKSimQuot.lean
git commit -m "Add Category instance for LawvereKSimCat"
```

---

### Task 15: Lawvere finite-product structure on `LawvereKSimCat`

**Files:**

- Modify: `GebLean/LawvereKSimQuot.lean`
- Modify: `GebLean/LawvereKSimInterp.lean`
  (only if `KMorN.interp_pair` is missing)

- [ ] **Step 1: Verify `KMorN.interp_pair` exists in
  `LawvereKSimInterp.lean`; add it if it does not.**

The lemma should read:

```lean
@[simp] theorem KMorN.interp_pair
    {k n m : ℕ}
    (f : KMorN k n) (g : KMorN k m)
    (ctx : Fin k → ℕ) :
    (KMorN.pair f g).interp ctx
      = fun i =>
          if h : i.val < n then
            f.interp ctx ⟨i.val, h⟩
          else
            g.interp ctx ⟨i.val - n, by
              rcases i with ⟨v, hv⟩
              omega⟩ := by
  funext i
  simp [KMorN.pair, KMorN.interp]
  split_ifs <;> rfl
```

If absent, add it.  Run `lake build GebLean.LawvereKSimInterp`
and commit it as a small atomic change.

- [ ] **Step 2: Add terminal, fst, snd in
  `LawvereKSimQuot.lean`, mirroring `ERMorNQuo`.**

```lean
/-- Terminal morphism in the quotient: equivalence
class of the empty tuple. -/
def KMorNQuo.terminal (n : ℕ) : KMorNQuo n 0 :=
  Quotient.mk (kMorNSetoid n 0) (KMorN.terminal n)

/-- Uniqueness of the morphism to the terminal. -/
theorem KMorNQuo.terminal_uniq {n : ℕ}
    (f : KMorNQuo n 0) : f = KMorNQuo.terminal n :=
  Quotient.ind
    (motive := fun f => f = KMorNQuo.terminal n)
    (fun _ => Quotient.sound
      (s := kMorNSetoid n 0)
      (fun _ => funext (fun i => Fin.elim0 i)))
    f

/-- First projection in the quotient. -/
def KMorNQuo.fst {n m : ℕ} : KMorNQuo (n + m) n :=
  Quotient.mk (kMorNSetoid (n + m) n) KMorN.fst

/-- Second projection in the quotient. -/
def KMorNQuo.snd {n m : ℕ} : KMorNQuo (n + m) m :=
  Quotient.mk (kMorNSetoid (n + m) m) KMorN.snd
```

- [ ] **Step 3: Add the pairing operation lifted via
  `Quotient.lift₂`.**

```lean
/-- Pairing in the quotient. -/
def KMorNQuo.pair {k n m : ℕ}
    (f : KMorNQuo k n) (g : KMorNQuo k m) :
    KMorNQuo k (n + m) :=
  Quotient.lift₂
    (s₁ := kMorNSetoid k n)
    (s₂ := kMorNSetoid k m)
    (fun f' g' =>
      Quotient.mk (kMorNSetoid k (n + m))
        (KMorN.pair f' g'))
    (fun fa fb ga gb hf hg =>
      Quotient.sound
        (s := kMorNSetoid k (n + m))
        (fun ctx => by
          simp only [KMorN.interp_pair]
          funext i
          split_ifs with h
          · exact congrFun (hf ctx) ⟨i.val, h⟩
          · exact congrFun (hg ctx)
              ⟨i.val - n, by
                rcases i with ⟨v, hv⟩
                omega⟩))
    f g
```

- [ ] **Step 4: Add the universal-property theorems
  for the binary product.**

```lean
/-- Pair followed by `fst` recovers the first
component. -/
theorem KMorNQuo.pair_fst {k n m : ℕ}
    (f : KMorNQuo k n) (g : KMorNQuo k m) :
    KMorNQuo.comp (KMorNQuo.pair f g)
        (KMorNQuo.fst (n := n) (m := m)) = f :=
  Quotient.ind₂
    (motive := fun f g =>
      KMorNQuo.comp (KMorNQuo.pair f g)
          (KMorNQuo.fst (n := n) (m := m)) = f)
    (fun f_raw g_raw =>
      Quotient.sound
        (s := kMorNSetoid k n)
        (fun ctx => by
          simp [KMorN.interp_comp, KMorN.interp_pair,
                KMorN.interp_fst, KMorN.comp,
                KMorN.fst]))
    f g

/-- Pair followed by `snd` recovers the second
component. -/
theorem KMorNQuo.pair_snd {k n m : ℕ}
    (f : KMorNQuo k n) (g : KMorNQuo k m) :
    KMorNQuo.comp (KMorNQuo.pair f g)
        (KMorNQuo.snd (n := n) (m := m)) = g :=
  Quotient.ind₂
    (motive := fun f g =>
      KMorNQuo.comp (KMorNQuo.pair f g)
          (KMorNQuo.snd (n := n) (m := m)) = g)
    (fun f_raw g_raw =>
      Quotient.sound
        (s := kMorNSetoid k m)
        (fun ctx => by
          simp [KMorN.interp_comp, KMorN.interp_pair,
                KMorN.interp_snd, KMorN.comp,
                KMorN.snd]))
    f g

/-- Uniqueness: any morphism `h : k → n + m` whose
projections recover `f` and `g` equals `pair f g`. -/
theorem KMorNQuo.pair_uniq {k n m : ℕ}
    (f : KMorNQuo k n) (g : KMorNQuo k m)
    (h : KMorNQuo k (n + m))
    (hf : KMorNQuo.comp h
            (KMorNQuo.fst (n := n) (m := m)) = f)
    (hg : KMorNQuo.comp h
            (KMorNQuo.snd (n := n) (m := m)) = g) :
    h = KMorNQuo.pair f g := by
  refine Quotient.ind ?_ h
  intro h_raw
  rcases f with ⟨f_raw⟩
  rcases g with ⟨g_raw⟩
  apply Quotient.sound
  intro ctx
  funext i
  by_cases hi : i.val < n
  · have := congrArg (fun q : KMorNQuo k n =>
      Quotient.lift (β := Fin n → ℕ)
        (fun f' => f'.interp ctx) (fun _ _ h => by
          funext j; exact congrFun (h ctx) j) q) hf
    sorry  -- finish via congrFun and the equation
  · sorry  -- symmetric
```

The two `sorry`s in `pair_uniq` must be replaced with
real proofs.  The structure is parallel to
`ERMorNQuo.pair_uniq` in `LawvereERQuot.lean`; consult
that file for the exact lemma names and the correct
`Quotient.lift` plumbing.

- [ ] **Step 5: Add `lawvereKSimProduct`,
  `lawvereKSimTerminal`, and the
  `HasChosenFiniteProducts` instance.**

```lean
/-- The chosen binary-product cone for `n` and `m`. -/
def lawvereKSimProduct (n m : LawvereKSimCat) :
    CategoryTheory.Limits.LimitCone
      (CategoryTheory.Limits.pair n m) :=
  sorry  -- mirror lawvereERProduct in LawvereERQuot.lean

/-- The chosen terminal cone. -/
def lawvereKSimTerminal :
    CategoryTheory.Limits.LimitCone
      (Functor.empty.{0} _) :=
  sorry  -- mirror lawvereERTerminal in LawvereERQuot.lean

instance :
    CategoryTheory.Limits.HasChosenFiniteProducts
      LawvereKSimCat where
  product n m := lawvereKSimProduct n m
  terminal := lawvereKSimTerminal
```

The two `sorry`s must be replaced with concrete cones.
Use `lawvereERProduct` and `lawvereERTerminal` in
`GebLean/LawvereERQuot.lean` (around lines 350–400) as
direct templates: substitute `KMorNQuo` for `ERMorNQuo`,
`kMorNSetoid` for `erMorNSetoid`, `KMorN.fst` for
`ERMorN.fst`, etc.

- [ ] **Step 6: Run `lake build`.**

Run: `lake build GebLean.LawvereKSimQuot`
Expected: success, no warnings.  No `sorry`s remain.

- [ ] **Step 7: Commit.**

```bash
git add GebLean/LawvereKSimQuot.lean \
        GebLean/LawvereKSimInterp.lean
git commit -m "Add Lawvere finite-product structure on LawvereKSimCat"
```

---

### Task 16: `KSimMor d` as full subcategory + inclusions

**Files:**

- Modify: `GebLean/LawvereKSimQuot.lean`

- [ ] **Step 1: Define the depth predicate on
  `KMorNQuo`.**

Per design principle **P4**, a quotient class `q :
KMorNQuo n m` is *at depth d* iff some representative
`f : KMorN n m` has every component at level ≤ d.

```lean
/-- The `KMorNQuo n m` class admits a syntactic
representative at depth ≤ d iff some `KMorN n m`
representative has each of its components at
`KMor1.level ≤ d`. -/
def KMorNQuo.atDepth {n m : ℕ} (d : ℕ)
    (q : KMorNQuo n m) : Prop :=
  ∃ f : KMorN n m,
    (∀ i : Fin m, (f i).level ≤ d) ∧
    Quotient.mk (kMorNSetoid n m) f = q
```

- [ ] **Step 2: Prove the depth predicate is preserved
  by `id` and `comp`.**

```lean
theorem KMorNQuo.id_atDepth {n d : ℕ} :
    KMorNQuo.atDepth d (KMorNQuo.id n) := by
  refine ⟨KMorN.id n, ?_, rfl⟩
  intro i
  simp [KMorN.id, KMor1.level]

theorem KMorNQuo.comp_atDepth
    {n m k d : ℕ}
    (f : KMorNQuo n m) (g : KMorNQuo m k)
    (hf : KMorNQuo.atDepth d f)
    (hg : KMorNQuo.atDepth d g) :
    KMorNQuo.atDepth d (KMorNQuo.comp f g) := by
  obtain ⟨f', hf_lvl, hf_eq⟩ := hf
  obtain ⟨g', hg_lvl, hg_eq⟩ := hg
  refine ⟨KMorN.comp g' f', ?_, ?_⟩
  · intro i
    -- (KMorN.comp g' f') i = KMor1.comp (g' i) f'
    -- level (KMor1.comp ...) = max (level (g' i))
    --   (sup level (f' j)) ≤ d, since each is ≤ d.
    simp [KMorN.comp, KMor1.level]
    refine ⟨hg_lvl i, ?_⟩
    apply Finset.sup_le
    intro j _
    exact hf_lvl j
  · -- The composition's quotient class equals
    -- KMorNQuo.comp of the quotient classes of f' and g'.
    rw [← hf_eq, ← hg_eq]
    rfl
```

If the `simp` and `Finset.sup_le` plumbing differs in
your mathlib version, adjust the proof with whatever
lemmas establish `level f ≤ d → level (KMor1.comp …) ≤ d`.

- [ ] **Step 3: Define `KSimMor d` as a structure
  packaging a `KMorNQuo` with its depth witness.**

```lean
/-- The K^sim_d category at depth d: morphisms are
`KMorNQuo` quotient classes admitting a level-≤-d
representative.  Per design principle P4. -/
structure KSimMor (d : ℕ) (n m : ℕ) where
  hom : KMorNQuo n m
  depth_witness : KMorNQuo.atDepth d hom
```

- [ ] **Step 4: Add the `Category` instance for
  `KSimMor d`, again using a wrapper type for the
  objects.**

```lean
/-- The depth-d K^sim category has the same objects as
`LawvereKSimCat` but restricts to KSimMor d morphisms. -/
def LawvereKSimDCat (d : ℕ) := ℕ

instance (d n : ℕ) : OfNat (LawvereKSimDCat d) n :=
  ⟨(n : ℕ)⟩

instance (d : ℕ) : DecidableEq (LawvereKSimDCat d) :=
  inferInstanceAs (DecidableEq ℕ)

instance (d : ℕ) :
    CategoryTheory.CategoryStruct
      (LawvereKSimDCat d) where
  Hom n m := KSimMor d n m
  id n := ⟨KMorNQuo.id n, KMorNQuo.id_atDepth⟩
  comp f g :=
    ⟨KMorNQuo.comp f.hom g.hom,
     KMorNQuo.comp_atDepth f.hom g.hom
       f.depth_witness g.depth_witness⟩

/-- An extensionality lemma reducing `KSimMor`
equality to `hom`-field equality (since `depth_witness`
is `Prop`-valued and proof-irrelevant). -/
@[ext] theorem KSimMor.ext {d n m : ℕ}
    {x y : KSimMor d n m} (h : x.hom = y.hom) :
    x = y := by
  cases x; cases y
  congr

instance (d : ℕ) :
    CategoryTheory.Category (LawvereKSimDCat d) where
  id_comp f := by
    apply KSimMor.ext
    exact KMorNQuo.id_comp f.hom
  comp_id f := by
    apply KSimMor.ext
    exact KMorNQuo.comp_id f.hom
  assoc f g h := by
    apply KSimMor.ext
    exact KMorNQuo.comp_assoc f.hom g.hom h.hom
```

- [ ] **Step 5: Add the inclusion functor
  `LawvereKSimDCat d → LawvereKSimDCat (d+1)`.**

```lean
/-- The inclusion functor weakening the depth from
`d` to `d+1`.  On objects it is the identity (both
categories have the same `ℕ`-shaped object collection);
on morphisms it forwards the underlying `KMorNQuo` and
weakens the depth witness via monotonicity. -/
def KSimMor.includeSucc (d : ℕ) :
    CategoryTheory.Functor
      (LawvereKSimDCat d) (LawvereKSimDCat (d+1)) where
  obj n := n
  map {n m} h :=
    ⟨h.hom, by
      obtain ⟨f, hf_lvl, hf_eq⟩ := h.depth_witness
      exact ⟨f,
        fun i => Nat.le_succ_of_le (hf_lvl i),
        hf_eq⟩⟩
  map_id _ := KSimMor.ext rfl
  map_comp _ _ := KSimMor.ext rfl
```

- [ ] **Step 6: Run `lake build`.**

Run: `lake build GebLean.LawvereKSimQuot`
Expected: success, no warnings.

- [ ] **Step 7: Commit.**

```bash
git add GebLean/LawvereKSimQuot.lean
git commit -m "Add KSimMor d full subcategory and inclusion functors"
```

---

### Task 17: `#guard` tests for the quotient and category

**Files:**

- Create: `GebLeanTests/LawvereKSimQuot.lean`

- [ ] **Step 1: Create the test module.**

```lean
import GebLean.LawvereKSimQuot
import Mathlib.Data.Fin.VecNotation

/-!
# Tests for LawvereKSimQuot

Sanity tests verifying that the quotient-category
machinery operates correctly on small inputs.
-/

open GebLean

private def ctx0 : Fin 0 → ℕ := Fin.elim0
private def ctx1 (x : ℕ) : Fin 1 → ℕ := fun _ => x
private def ctx2 (x y : ℕ) : Fin 2 → ℕ := ![x, y]

-- Two different syntactic forms of "constantly 5" at
-- arity 1 have the same interpretation (one uses
-- `raise` for level padding; both should evaluate to
-- 5 at every input).
private def five₁ : KMor1 1 :=
  KMor1.comp KMor1.succ (fun _ =>
    KMor1.comp KMor1.succ (fun _ =>
      KMor1.comp KMor1.succ (fun _ =>
        KMor1.comp KMor1.succ (fun _ =>
          KMor1.comp KMor1.succ (fun _ =>
            KMor1.zero (n := 1)))))) 

private def five₂ : KMor1 1 :=
  KMor1.comp KMor1.succ (fun _ =>
    KMor1.comp KMor1.succ (fun _ =>
      KMor1.comp KMor1.succ (fun _ =>
        KMor1.comp KMor1.succ (fun _ =>
          KMor1.comp KMor1.succ (fun _ =>
            KMor1.raise (KMor1.zero (n := 1))))))) 

-- Both interpret to 5.
#guard five₁.interp (ctx1 0) == 5
#guard five₂.interp (ctx1 0) == 5
#guard five₁.interp (ctx1 0) == five₂.interp (ctx1 0)

-- The KMorN identity wrapper: id at arity 2 produces
-- (proj 0, proj 1), which interp returns the input.
#guard
  let idHom : KMorN 2 2 := KMorN.id 2
  idHom.interp (ctx2 5 7) 0 == 5

#guard
  let idHom : KMorN 2 2 := KMorN.id 2
  idHom.interp (ctx2 5 7) 1 == 7
```

`ExtEq` itself is not always computable, so we test it
via underlying-interp comparisons rather than via
direct `KMor1.ExtEq` `Prop`-evaluation.

- [ ] **Step 2: Run `lake test`.**

Run: `lake test`
Expected: all tests pass.

- [ ] **Step 3: Commit.**

```bash
git add GebLeanTests/LawvereKSimQuot.lean
git commit -m "Add LawvereKSimQuot #guard tests"
```

---

### Task 18: Re-export new modules from `GebLean.lean`

**Files:**

- Modify: `GebLean.lean`

- [ ] **Step 1: Add re-exports for the new modules.**

Locate the section of `GebLean.lean` that imports the
existing `LawvereER*` family.  Add the new modules
there:

```lean
import GebLean.LawvereKSim
import GebLean.LawvereKSimInterp
import GebLean.LawvereKSimQuot
```

Place these next to the existing `LawvereER*`
imports for consistency.

- [ ] **Step 2: Run `lake build` for the full project.**

Run: `lake build`
Expected: success, no warnings.

- [ ] **Step 3: Commit.**

```bash
git add GebLean.lean
git commit -m "Re-export new K^sim modules from GebLean.lean"
```

---

### Task 19: Final verification

**Files:**

- (no edits; verification only)

- [ ] **Step 1: Run a full clean build of the project.**

Run: `lake build`
Expected: success, no warnings, no errors.

- [ ] **Step 2: Run the full test suite.**

Run: `lake test`
Expected: all tests pass.

- [ ] **Step 3: Confirm there are no `sorry` or `admit`
  occurrences in any of the new files.**

Run:

```bash
grep -nE "\b(sorry|admit)\b" GebLean/LawvereKSim.lean \
  GebLean/LawvereKSimInterp.lean \
  GebLean/LawvereKSimQuot.lean \
  GebLeanTests/LawvereKSim*.lean
```

Expected: no output.

- [ ] **Step 4: Confirm there are no banned words in
  comments per `CLAUDE.md` Code Style.**

Run:

```bash
grep -nEf <(echo 'fundamental|actually|key|insight|core
advanced|complex|complicated|simple|advantage|benefit
important|challenge|careful|difficult|blocked
incomplete|future|issue|problem' | tr '\n' '|') \
  GebLean/LawvereKSim*.lean
```

(or, equivalently, run the same regex as in
`docs/lawvere-k-sim-hierarchy.md`'s self-review.)

Expected: no output (or only legitimate domain terms;
review hits manually).

- [ ] **Step 5: Confirm line lengths ≤ 80.**

Run:

```bash
awk '{ if (length($0) > 80) print FILENAME":"NR": "length($0)" chars" }' \
  GebLean/LawvereKSim.lean \
  GebLean/LawvereKSimInterp.lean \
  GebLean/LawvereKSimQuot.lean
```

Expected: no output.

- [ ] **Step 6: Verify the public surface.**

```bash
grep -nE \
  "^(def|theorem|abbrev|inductive|structure|instance) (KMor1|KMorN|KSim)" \
  GebLean/LawvereKSim.lean \
  GebLean/LawvereKSimInterp.lean \
  GebLean/LawvereKSimQuot.lean | head -30
```

Confirm that the listed public definitions match the
inventory in §"Lean Structural Design" of the design
doc: `KMor1`, `KMorN`, `KMor1.level`, `KMorN.levelN`,
`KMor1.interp`, `KMorN.interp`, `kMorNSetoid`,
`KMorNQuo`, `LawvereKSimCat`, `LawvereKSimDCat`,
`KSimMor`, `KSimMor.includeSucc`.

- [ ] **Step 7: Final commit with a phase-1 summary.**

```bash
git commit --allow-empty -m \
  "Phase 1 complete: K^sim hierarchy as a category"
```

---

## Spec Coverage Summary

This plan implements the Phase 1 deliverables enumerated
in §1.1 of the design document.  Mapping:

| Design-doc deliverable          | Tasks       |
|---------------------------------|-------------|
| `KMor1` term language           | Task 1      |
| `KMorN` wrapper + ops           | Task 2      |
| `KMor1.level` / `KMorN.levelN`  | Task 3      |
| Depth-monotonicity lemmas       | Task 3      |
| `KMor1.interp`                  | Tasks 4, 7  |
| `@[simp]` interp lemmas         | Tasks 5–8   |
| `KMorN.interp` + ops lemmas     | Tasks 8, 15 |
| `kMorNSetoid` extensional eq    | Task 12     |
| `KMorNQuo` quotient + ops       | Task 13     |
| `Category` instance             | Task 14     |
| Lawvere finite-product structure| Task 15     |
| `KSimMor d` full subcategory    | Task 16     |
| `KSimMor d → KSimMor (d+1)`     | Task 16     |
| Tests with `#guard`             | Tasks 9, 10, 17 |
| `GebLean.lean` re-exports       | Task 18     |
| Final verification              | Task 19     |

The Phase-1 implementation plan does **not** cover Phase
2 (`K^sim_2 ≌ ER`) or Phase 3 (`⋃_n K^sim_n ⊆ Primrec`);
those are scheduled as separate plans, written after
Phase 1 lands.

## Open Implementation Questions

The design doc §"Phase 1 — open issues" lists three
implementation choices left to discretion:

- **(i) Universe polymorphism** of `KMor1` — this plan
  uses `Type` (no universe parameter), matching
  `ERMor1`'s convention.  If a downstream use requires
  `Type u`, revisit.

- **(ii) `ExtEq` decidability** — this plan does not
  provide a `Decidable` instance for `ExtEq`.  The
  test for "two K^sim morphisms are extensionally
  equal" is performed via interp comparison at
  specific contexts (Task 16 uses this pattern).

- **(iii) `KSimMor d` packaging shape** — this plan
  uses a `structure` with a `hom` field plus a
  `depth_witness` propositional field (Task 15).  An
  alternative would be to package as a `Subtype`; the
  structure approach is preferred for clarity of the
  Category instance.
