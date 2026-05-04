# LawvereNatBT Two-Stage Equivalence Chain Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan task-by-task.
> Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Factor the equivalence `LawvereERCat ≃ LawvereNatBT` into a
two-stage chain `LawvereERCat ≃ LawvereNatBT_bounded ≃
LawvereNatBT_ramified`, resolving the E_3 strength mismatch that
arose from non-ramified tree recursion.

**Architecture:** First stage modifies the existing `LawvereNatBT`
into a provably-E_3 bounded theory by adding explicit bound
parameters to fold constructors and a `boundedNatRec` constructor
(equivalence 1 uses existing `foldBTLOnCode` and `boundedRec`
infrastructure).  Second stage defines a new ramified theory with
tier-disciplined mutual-recursion destructor (Leivant tier-2) and
proves equivalence with the bounded theory via a computable
`towerHeight`-based bound derivation.

**Tech Stack:** Lean 4 with mathlib.  Builds on
`GebLean/LawvereER.lean`, `GebLean/LawvereERQuot.lean`,
`GebLean/Utilities/ERArith.lean`, `GebLean/Utilities/ERTreeArith.lean`,
`GebLean/LawvereERBoundComputable.lean`, `GebLean/LawvereNatBT.lean`,
`GebLean/LawvereNatBTBackTrans.lean`.

**Design spec:**
`docs/superpowers/specs/2026-04-18-lawvere-natbt-two-stage-design.md`.

**Workstream tracker entry:**
`.session/workstreams/lawvere-elementary-recursive.md`.

---

## Project rules

Every task obeys the project rules documented in `CLAUDE.md`:

* Build + test after every code change via `lake build` and
  `lake test`.  Never `lake clean`; never `lake env lean`.
* Zero warnings, zero `sorry` (including in `.lean` prose), zero
  `admit`.  80-char line limit.  No `Classical`, `noncomputable`, no
  `axiom`.  All code inside `namespace GebLean … end GebLean`.
* Forbidden words in persistent writing (comments, docstrings,
  commit messages): fundamental, actually, key, insight, core,
  advanced, complex, complicated, simple, advantage, benefit,
  important, challenge, yes, wait, hmm, sorry (in prose), careful,
  difficult, blocked, incomplete, future, issue, problem, block.
  No emojis.
* Structures get `@[ext]` where applicable.  Standard derived
  instances (`DecidableEq`, `Repr`, `Inhabited`) where they apply.

---

## File structure

### Modified files (bounded theory)

| File | Role |
|---|---|
| `GebLean/LawvereNatBT.lean` | `BTL`, `NatBTMor1` inductive, `interp`, per-constructor `@[simp]` lemmas.  Adds bound parameters and `boundedNatRec`. |
| `GebLean/LawvereNatBTInterp.lean` | Interp functor.  Minor update for new constructor. |
| `GebLean/LawvereNatBTQuot.lean` | `NatBTMorN`, quotient, category.  Minor update. |
| `GebLean/LawvereNatBT0.lean` | `FullSubcategory` on `m = 0`.  Minor update. |
| `GebLean/LawvereNatBTBackTrans.lean` | Task 14a's back-translation.  Extended to cover `foldBTNat`, `foldBTBT`, `boundedNatRec`. |

### New files (equivalence 1)

| File | Role |
|---|---|
| `GebLean/LawvereNatBTBoundedEquivER.lean` | Equivalence `LawvereERCat ≃ LawvereNatBT_bounded` (embedding functor, categorical equivalence). |

### New files (ramified theory)

| File | Role |
|---|---|
| `GebLean/LawvereNatBTRamified.lean` | `Tier`, `NatBTMor1Ramified` inductive, `interp`. |
| `GebLean/LawvereNatBTRamifiedInterp.lean` | Interp functor; faithful. |
| `GebLean/LawvereNatBTRamifiedQuot.lean` | Quotient and category. |

### New files (equivalence 2)

| File | Role |
|---|---|
| `GebLean/LawvereNatBTRamifiedEquivBounded.lean` | Back-translation `F21`, forward `F12`, both-directions identity lemmas. |
| `GebLean/LawvereNatBTRamifiedEquivER.lean` | Transitive composition of equivalences 1 and 2. |

### Test modules

| File | Role |
|---|---|
| `GebLeanTests/LawvereNatBTBackTrans.lean` | Existing; extend with fold-case tests. |
| `GebLeanTests/LawvereNatBTRamified.lean` | New; tests for ramified theory. |
| `GebLeanTests/LawvereNatBTRamifiedEquiv.lean` | New; tests for equivalence 2. |

### Registration

`GebLean.lean` adds imports for each new module in alphabetical
position.  `GebLeanTests.lean` similarly.

---

## Stage β.a: Bounded-theory refactor

### Task 1: Add header comments documenting bounded theory

**Files:**

* Modify: `GebLean/LawvereNatBT.lean` — header docstring.
* Modify: `GebLean/LawvereNatBT0.lean` — header docstring.
* Modify: `GebLean/LawvereNatBTInterp.lean` — header docstring.
* Modify: `GebLean/LawvereNatBTQuot.lean` — header docstring.
* Modify: `GebLean/LawvereNatBTBackTrans.lean` — header docstring.

- [ ] **Step 1: Update docstrings**

At the top of each file, add or extend the `/-! -/` docstring to
note that the file defines or operates on the bounded variant of
the theory:

```lean
/-!
# [Existing title]

[Existing description]

**Version note**: this file defines/operates on the *bounded*
variant of the two-sort theory.  `foldBTNat` and `foldBTBT`
carry explicit `bound` parameters; the ramified variant is in
`LawvereNatBTRamified*.lean`.  The two-stage equivalence
`LawvereERCat ≃ LawvereNatBT_bounded ≃ LawvereNatBT_ramified`
is documented in
`docs/superpowers/specs/2026-04-18-lawvere-natbt-two-stage-design.md`.
-/
```

- [ ] **Step 2: Build and commit**

```bash
lake build
git add GebLean/LawvereNatBT.lean GebLean/LawvereNatBT0.lean \
        GebLean/LawvereNatBTInterp.lean GebLean/LawvereNatBTQuot.lean \
        GebLean/LawvereNatBTBackTrans.lean
git commit -m "Document LawvereNatBT as the bounded theory variant"
```

---

### Task 2: Add bound parameter to `foldBTNat`

**Files:**

* Modify: `GebLean/LawvereNatBT.lean`.

- [ ] **Step 1: Modify the `foldBTNat` constructor signature**

Find the current `foldBTNat` constructor (around line 186).
Change from:

```lean
| foldBTNat {nm : ℕ × ℕ}
    (baseLeaf : NatBTMor1 (nm.1 + 1, nm.2) .nat)
    (stepNode : NatBTMor1 (nm.1 + 2, nm.2) .nat)
    (tree : NatBTMor1 nm .bt) :
    NatBTMor1 nm .nat
```

to:

```lean
| foldBTNat {nm : ℕ × ℕ}
    (baseLeaf : NatBTMor1 (nm.1 + 1, nm.2) .nat)
    (stepNode : NatBTMor1 (nm.1 + 2, nm.2) .nat)
    (tree : NatBTMor1 nm .bt)
    (bound : NatBTMor1 (nm.1 + 1, nm.2) .nat) :
    NatBTMor1 nm .nat
```

- [ ] **Step 2: Update the `foldBTNat` interp case**

Find the existing `foldBTNat` case in
`NatBTMor1.interp`.  Change the semantics from unbounded fold to
min-truncated:

```lean
| _, _, NatBTMor1.foldBTNat baseLeaf stepNode tree bound, ctxN,
      ctxB =>
    let t := NatBTMor1.interp tree ctxN ctxB
    let boundVal :=
      NatBTMor1.interp bound (Fin.cons t.encode ctxN) ctxB
    Nat.min (Nat.foldBTLOnCode
      (fun lbl =>
        NatBTMor1.interp baseLeaf (Fin.cons lbl ctxN) ctxB)
      (fun a b =>
        NatBTMor1.interp stepNode
          (Fin.cons a (Fin.cons b ctxN)) ctxB)
      t.encode) boundVal
```

- [ ] **Step 3: Update the `interp_foldBTNat` simp lemma**

Find `@[simp] theorem NatBTMor1.interp_foldBTNat`.  Update its
statement and proof to match the new semantics:

```lean
@[simp] theorem NatBTMor1.interp_foldBTNat
    {nm : ℕ × ℕ}
    (baseLeaf : NatBTMor1 (nm.1 + 1, nm.2) .nat)
    (stepNode : NatBTMor1 (nm.1 + 2, nm.2) .nat)
    (tree : NatBTMor1 nm .bt)
    (bound : NatBTMor1 (nm.1 + 1, nm.2) .nat)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1.foldBTNat baseLeaf stepNode tree bound).interp
        ctxN ctxB =
      Nat.min (Nat.foldBTLOnCode
        (fun lbl => baseLeaf.interp (Fin.cons lbl ctxN) ctxB)
        (fun a b =>
          stepNode.interp (Fin.cons a (Fin.cons b ctxN)) ctxB)
        (tree.interp ctxN ctxB).encode)
        (bound.interp
          (Fin.cons (tree.interp ctxN ctxB).encode ctxN) ctxB)
  := rfl
```

- [ ] **Step 4: Build and fix call-site errors**

```bash
lake build
```

Expected: compilation errors at every existing use of
`NatBTMor1.foldBTNat` (missing bound argument).  Fix each by
supplying a bound argument — for initial migration, use
`NatBTMor1.zero` as a placeholder bound.  Downstream work in
later tasks will replace placeholders with adequate bounds.

List of known use sites:

* `GebLean/LawvereNatBTInterp.lean`
* `GebLean/LawvereNatBTQuot.lean`
* `GebLean/LawvereNatBT0.lean`
* `GebLean/LawvereNatBTBackTrans.lean`
* `GebLeanTests/LawvereNatBT.lean`
* Any other test modules that exercise `foldBTNat`.

Find each usage via:

```bash
grep -rn "NatBTMor1.foldBTNat" GebLean/ GebLeanTests/
```

- [ ] **Step 5: Build and verify**

```bash
lake build
lake test
```

Expected: build succeeds with zero warnings; tests pass.  Any
test whose semantics specifically required unbounded fold output
is noted as `TODO` — these will be updated in Task 5.

- [ ] **Step 6: Commit**

```bash
git add GebLean/LawvereNatBT.lean GebLean/LawvereNatBTInterp.lean \
        GebLean/LawvereNatBTQuot.lean GebLean/LawvereNatBT0.lean \
        GebLean/LawvereNatBTBackTrans.lean GebLeanTests/
git commit -m "Add bound parameter to NatBTMor1.foldBTNat"
```

---

### Task 3: Add bound parameter to `foldBTBT`

**Files:**

* Modify: `GebLean/LawvereNatBT.lean`.

- [ ] **Step 1: Modify the `foldBTBT` constructor signature**

Change from the current signature to:

```lean
| foldBTBT {nm : ℕ × ℕ}
    (baseLeaf : NatBTMor1 (nm.1 + 1, nm.2) .bt)
    (stepNode : NatBTMor1 (nm.1, nm.2 + 2) .bt)
    (tree : NatBTMor1 nm .bt)
    (bound : NatBTMor1 (nm.1 + 1, nm.2) .nat) :
    NatBTMor1 nm .bt
```

The bound parameter is ℕ-valued; the fold output stays BT-valued
but its encoding is bounded.

- [ ] **Step 2: Update the `foldBTBT` interp case**

The semantics clips the encoded fold result at `bound` before
decoding back to BT:

```lean
| _, _, NatBTMor1.foldBTBT baseLeaf stepNode tree bound, ctxN,
      ctxB =>
    let t := NatBTMor1.interp tree ctxN ctxB
    let traceVal := ...  -- (existing fold semantics inlined)
    let boundVal :=
      NatBTMor1.interp bound
        (Fin.cons t.encode ctxN) ctxB
    BTL.decode (Nat.min traceVal.encode boundVal)
```

(The implementer fills in the `...` from the existing semantics,
then wraps the BT-valued result's encoding in `Nat.min` before
decoding.)

- [ ] **Step 3: Update `interp_foldBTBT` simp lemma**

Mirror the interp case.

- [ ] **Step 4: Fix call sites, build, test, commit**

Same pattern as Task 2, Steps 4-6.

```bash
lake build
lake test
git add GebLean/LawvereNatBT.lean (all affected files)
git commit -m "Add bound parameter to NatBTMor1.foldBTBT"
```

---

### Task 4: Add `boundedNatRec` constructor

**Files:**

* Modify: `GebLean/LawvereNatBT.lean`.

- [ ] **Step 1: Add new constructor**

After `foldBTBT`, add:

```lean
| boundedNatRec {nm : ℕ × ℕ}
    (base : NatBTMor1 nm .nat)
    (step : NatBTMor1 (nm.1 + 2, nm.2) .nat)
    (n : NatBTMor1 nm .nat)
    (bound : NatBTMor1 (nm.1 + 1, nm.2) .nat) :
    NatBTMor1 nm .nat
```

- [ ] **Step 2: Add interp case**

In `NatBTMor1.interp`:

```lean
| _, _, NatBTMor1.boundedNatRec base step n bound, ctxN, ctxB =>
    let nVal := NatBTMor1.interp n ctxN ctxB
    let boundVal :=
      NatBTMor1.interp bound (Fin.cons nVal ctxN) ctxB
    Nat.min
      (Nat.rec (NatBTMor1.interp base ctxN ctxB)
        (fun j prev =>
          NatBTMor1.interp step
            (Fin.cons j (Fin.cons prev ctxN)) ctxB)
        nVal)
      boundVal
```

- [ ] **Step 3: Add `@[simp] interp_boundedNatRec` lemma**

Mirror the interp case; the statement is the equation above
unfolded.

- [ ] **Step 4: Build and test**

```bash
lake build
lake test
```

- [ ] **Step 5: Commit**

```bash
git add GebLean/LawvereNatBT.lean
git commit -m "Add NatBTMor1.boundedNatRec constructor to bounded theory"
```

---

### Task 5: Extend `NatBTMor1.toERUniform` for fold cases

**Files:**

* Modify: `GebLean/LawvereNatBTBackTrans.lean`.

- [ ] **Step 1: Remove `isFoldFree` requirement from the mutual
      correctness theorem**

The existing `toERUniform` function handles all constructors but
placeholder-outputs `ERMor1.zeroN _` for the three fold cases
(`foldBTNat`, `foldBTBT`, placeholder — `boundedNatRec` is new
and not yet handled).  Replace the placeholder outputs with real
translations.

For `foldBTNat baseLeaf stepNode tree bound`:

```lean
| _, _, NatBTMor1.foldBTNat baseLeaf stepNode tree bound =>
    ERMor1.comp
      (ERMor1.foldBTLOnCode baseLeaf.toERUniform
        stepNode.toERUniform bound.toERUniform)
      (Fin.cons tree.toERUniform
        (fun i => ERMor1.proj (⟨i.val + 1, by omega⟩ : Fin _)))
```

Analogous for `foldBTBT` (with BT-valued output handled via
encoded round-trip) and `boundedNatRec` (using
`ERMor1.boundedRec` directly).

- [ ] **Step 2: Adjust `isFoldFree` predicate**

Since all constructors now translate, `isFoldFree` becomes
trivially `True`.  Either:

* Remove `isFoldFree` and its uses; `toER_interp` becomes
  unconditional.
* Keep `isFoldFree` for documentation but set it to always
  `True`.

Recommended: remove `isFoldFree` entirely.  Update the
`NatBTMor1.toER_interp` theorem's signature to drop the
`isFoldFree` hypothesis.

- [ ] **Step 3: Update correctness proofs**

For each fold case, extend the `toERUniform_interp_aux` induction:

* `foldBTNat`: use `ERMor1.interp_foldBTLOnCode_of_bounded` with
  the supplied bound's adequacy (which follows from the
  min-truncation in the bounded theory's interp: the truncation
  IS the adequacy witness).
* `foldBTBT`: similar with BT-valued output.
* `boundedNatRec`: use `ERMor1.interp_boundedRec_of_bounded`.

For min-truncation: the bounded theory's semantics IS
`min (unbounded_fold) (bound)`.  The ER back-translation's
semantics under `foldBTLOnCode` is also `min (unbounded_fold)
(bound)` (under adequacy — but here the bounded theory has
equality by construction of its interp).  Adequacy follows from
the bound being the same term in both interpretations; details
in the proof.

Budget: ~1-2 sessions for the correctness proofs.

- [ ] **Step 4: Build and test**

```bash
lake build
lake test
```

- [ ] **Step 5: Commit**

```bash
git add GebLean/LawvereNatBTBackTrans.lean
git commit -m "Complete toERUniform for bounded fold cases"
```

---

## Stage β.b: LawvereERCat ≃ LawvereNatBT_bounded

### Task 6: Create `LawvereNatBTBoundedEquivER.lean` skeleton

**Files:**

* Create: `GebLean/LawvereNatBTBoundedEquivER.lean`.
* Modify: `GebLean.lean` — add import.

- [ ] **Step 1: Create file skeleton**

```lean
import GebLean.LawvereERQuot
import GebLean.LawvereNatBT0
import GebLean.LawvereNatBTBackTrans
import Mathlib.CategoryTheory.Equivalence

/-!
# Equivalence `LawvereERCat ≃ LawvereNatBT_bounded`

The first stage of the two-stage chain.  Builds the equivalence
between `LawvereERCat` (Wikipedia-literal ER) and
`LawvereNatBT_bounded` (our two-sort theory with explicit bound
parameters on fold constructors).

Design:
`docs/superpowers/specs/2026-04-18-lawvere-natbt-two-stage-design.md`.
-/

namespace GebLean

end GebLean
```

- [ ] **Step 2: Register import in GebLean.lean**

Add in alphabetical position:

```lean
import GebLean.LawvereNatBTBoundedEquivER
```

- [ ] **Step 3: Build and commit**

```bash
lake build
git add GebLean/LawvereNatBTBoundedEquivER.lean GebLean.lean
git commit -m "Skeleton for LawvereNatBT_bounded ≃ LawvereERCat equivalence"
```

---

### Task 7: Define embedding functor `F : LawvereERCat → LawvereNatBT_bounded`

**Files:**

* Modify: `GebLean/LawvereNatBTBoundedEquivER.lean`.

- [ ] **Step 1: Define the translation on term generators**

```lean
def ERMor1.toNatBT {n : ℕ} : ERMor1 n → NatBTMor1 (n, 0) .nat
  | ERMor1.zero => NatBTMor1.zero
  | ERMor1.succ => NatBTMor1.succ (NatBTMor1.natProj 0)
  | ERMor1.proj i => NatBTMor1.natProj i
  | ERMor1.sub =>
      NatBTMor1.sub (NatBTMor1.natProj 0) (NatBTMor1.natProj 1)
  | ERMor1.comp f g =>
      NatBTMor1.compNat f.toNatBT
        (fun i => (g i).toNatBT)
        (fun i => Fin.elim0 i)
  | ERMor1.bsum f => NatBTMor1.bsum f.toNatBT
  | ERMor1.bprod f => NatBTMor1.bprod f.toNatBT
```

- [ ] **Step 2: Prove extensional agreement of interp**

```lean
theorem ERMor1.toNatBT_interp {n : ℕ}
    (t : ERMor1 n) (ctx : Fin n → ℕ) :
    t.toNatBT.interp ctx Fin.elim0 = t.interp ctx := by
  induction t
  all_goals (simp [ERMor1.toNatBT, NatBTMor1.interp]; rfl)
  -- or a more detailed case analysis per constructor
```

- [ ] **Step 3: Lift to tuples and quotient**

```lean
def ERMorN.toNatBT {n m : ℕ} (f : ERMorN n m) :
    NatBTMorN (n, 0) (m, 0) :=
  { natComps := fun i => (f i).toNatBT
    btComps := fun i => Fin.elim0 i }

theorem ERMorN.toNatBT_interp {n m : ℕ}
    (f : ERMorN n m) (ctx : Fin n → ℕ) :
    (ERMorN.toNatBT f).interp ctx Fin.elim0 = (f.interp ctx, Fin.elim0)
  := ...
```

- [ ] **Step 4: Define functor on the quotient**

```lean
def erToNatBTBoundedFunctor :
    LawvereERCat ⥤ LawvereNatBTCat := {
  obj := fun n => (n, 0)
  map := fun (f : n ⟶ m) =>
    Quotient.map ERMorN.toNatBT
      (fun a b h => ... -- extensionality preservation
      ) f
  map_id := ...
  map_comp := ...
}
```

- [ ] **Step 5: Build and commit**

```bash
lake build
lake test
git add GebLean/LawvereNatBTBoundedEquivER.lean
git commit -m "Add LawvereERCat → LawvereNatBT_bounded embedding functor"
```

---

### Task 8: Define back-translation functor `G : LawvereNatBT_bounded → LawvereERCat`

**Files:**

* Modify: `GebLean/LawvereNatBTBoundedEquivER.lean`.

- [ ] **Step 1: Lift `NatBTMor1.toERUniform` to tuples**

Use `toERUniform` from Task 5 (now total after the fold cases
are handled).

```lean
def NatBTMorN.toER {n m : ℕ} :
    NatBTMorN (n, 0) (m, 0) → ERMorN n m :=
  fun f i => (f.natComps i).toERUniform
```

(Note: the `.bt`-component handling: since `m = 0`, there are no
BT components.  For general `(n, m) → (n', m')` morphisms, we'd
need to handle BT-valued outputs via encoding — defer for now
since we're focused on the (n, 0) objects.)

- [ ] **Step 2: Prove interp agreement**

```lean
theorem NatBTMorN.toER_interp {n m : ℕ}
    (f : NatBTMorN (n, 0) (m, 0)) (ctx : Fin n → ℕ) :
    (f.toER.interp ctx) = (f.interp ctx Fin.elim0).1
```

- [ ] **Step 3: Define the functor**

```lean
def natBTBoundedToERFunctor :
    LawvereNatBTCat ⥤ LawvereERCat := ...
```

On objects: `(n, m) ↦ n + m` (with the `m = 0` restriction
corresponding to the (n, 0) full subcategory).  Alternatively:
restrict the domain to `LawvereNatBT0Cat` (the `m = 0`
subcategory) so objects are just ℕ-arities.

Decision: restrict the functor's domain to `LawvereNatBT0Cat` for
the equivalence proof.  BT-valued morphisms require more machinery
and aren't needed for the main equivalence result.

- [ ] **Step 4: Build and commit**

```bash
lake build
git add GebLean/LawvereNatBTBoundedEquivER.lean
git commit -m "Add LawvereNatBT_bounded → LawvereERCat back-translation functor"
```

---

### Task 9: Prove `F ∘ G ≃ id` and `G ∘ F ≃ id`

**Files:**

* Modify: `GebLean/LawvereNatBTBoundedEquivER.lean`.

- [ ] **Step 1: Prove `G ∘ F = id` on ER**

```lean
theorem natBTBoundedToERFunctor_toNatBT_id {n m : ℕ}
    (f : ERMorN n m) :
    (ERMorN.toNatBT f).toER.interp =
    (fun _ => f.interp) := by
  -- induction / interp-agreement argument
```

- [ ] **Step 2: Prove `F ∘ G ≃ id` on NatBT_bounded (up to
      extensional equivalence)**

For each NatBTMor1 constructor, show that
`(t.toERUniform).toNatBT` interprets the same as `t`.  Sufficient:
show interp agrees, since the quotient is by extensional
equality.

```lean
theorem toNatBT_toERUniform_interp_agree {n : ℕ}
    (t : NatBTMor1 (n, 0) .nat) (ctx : Fin n → ℕ) :
    ((t.toERUniform).toNatBT).interp ctx Fin.elim0 =
      t.interp ctx Fin.elim0 := ...
```

- [ ] **Step 3: Assemble into natural isomorphism / equivalence**

Using `CategoryTheory.Equivalence.mk'` or similar:

```lean
def lawvereNatBTBoundedERCatEquivalence :
    LawvereNatBT0Cat ≌ LawvereERCat := {
  functor := natBTBoundedToERFunctor
  inverse := erToNatBTBoundedFunctor ∘ ...
  unitIso := NatIso.ofComponents ...
  counitIso := NatIso.ofComponents ...
}
```

- [ ] **Step 4: Build, test, commit**

```bash
lake build
lake test
git add GebLean/LawvereNatBTBoundedEquivER.lean
git commit -m "Prove LawvereNatBT_bounded ≃ LawvereERCat equivalence"
```

---

## Stage δ.a: Ramified-theory definition

### Task 10: Define `Tier` and inductive `NatBTMor1Ramified`

**Files:**

* Create: `GebLean/LawvereNatBTRamified.lean`.
* Modify: `GebLean.lean` — add import.

- [ ] **Step 1: Create file with `Tier`**

```lean
import GebLean.LawvereER
import GebLean.LawvereNatBT
import GebLean.Utilities.ERArith
import GebLean.Utilities.ERTreeArith

/-!
# Ramified Two-Sort Lawvere Theory

...
-/

namespace GebLean

inductive Tier : Type where
  | nonRec : Tier
  | mayRec : Tier
  deriving DecidableEq, Repr, Inhabited

def Tier.max : Tier → Tier → Tier
  | .nonRec, .nonRec => .nonRec
  | _, _ => .mayRec

@[simp] theorem Tier.max_nonRec_nonRec :
    Tier.max .nonRec .nonRec = .nonRec := rfl

-- ... similar simp lemmas for other combinations

end GebLean
```

- [ ] **Step 2: Define the ramified morphism inductive**

```lean
inductive NatBTMor1Ramified :
    (dom : ℕ × ℕ) → (cod : NatBTSort) → Tier → Type
  -- Non-recursive primitives (tier = NonRec)
  | zero {nm : ℕ × ℕ} :
      NatBTMor1Ramified nm .nat .nonRec
  | succ {nm : ℕ × ℕ} :
      NatBTMor1Ramified (nm.1 + 1, nm.2) .nat .nonRec
  | natProj {nm : ℕ × ℕ} (i : Fin nm.1) :
      NatBTMor1Ramified nm .nat .nonRec
  | sub {nm : ℕ × ℕ} :
      NatBTMor1Ramified (nm.1 + 2, nm.2) .nat .nonRec
  | add {nm : ℕ × ℕ} :  -- NEW
      NatBTMor1Ramified (nm.1 + 2, nm.2) .nat .nonRec
  | mul {nm : ℕ × ℕ} :  -- NEW
      NatBTMor1Ramified (nm.1 + 2, nm.2) .nat .nonRec
  | leafBT {nm : ℕ × ℕ} :
      NatBTMor1Ramified (nm.1 + 1, nm.2) .bt .nonRec
  | nodeBT {nm : ℕ × ℕ} :
      NatBTMor1Ramified (nm.1, nm.2 + 2) .bt .nonRec
  | btProj {nm : ℕ × ℕ} (i : Fin nm.2) :
      NatBTMor1Ramified nm .bt .nonRec
  -- Case destructors (tier = max of handlers)
  | natMatch {nm : ℕ × ℕ} {σ : NatBTSort} {t1 t2 : Tier}
      (zeroCase : NatBTMor1Ramified nm σ t1)
      (succCase : NatBTMor1Ramified (nm.1 + 2, nm.2) σ t2)
      (n : NatBTMor1Ramified (nm.1 + 1, nm.2) .nat .nonRec) :
      NatBTMor1Ramified (nm.1 + 1, nm.2) σ
        (Tier.max t1 t2)
  | btMatch {nm : ℕ × ℕ} {σ : NatBTSort} {t1 t2 : Tier}
      (leafCase : NatBTMor1Ramified (nm.1 + 1, nm.2) σ t1)
      (nodeCase :
        NatBTMor1Ramified (nm.1, nm.2 + 2) σ t2)
      (tree : NatBTMor1Ramified nm .bt .nonRec) :
      NatBTMor1Ramified nm σ (Tier.max t1 t2)
  -- Composition propagates tier
  | comp {a b c : ℕ × ℕ} {σ : NatBTSort} {t1 t2 : Tier}
      (f : NatBTMor1Ramified b σ t1)
      (gNat : Fin b.1 → NatBTMor1Ramified a .nat t2)
      (gBT : Fin b.2 → NatBTMor1Ramified a .bt t2) :
      NatBTMor1Ramified a σ (Tier.max t1 t2)
  -- Recursive destructor (always MayRec)
  | foldMutNat {dom : ℕ × ℕ} {σ : NatBTSort} {tb ts : Tier}
      (base : NatBTMor1Ramified dom σ tb)
      (step : NatBTMor1Ramified (dom.1 + 2, dom.2) σ .nonRec)
      (n : NatBTMor1Ramified dom .nat ts) :
      NatBTMor1Ramified dom σ .mayRec
  | foldMutBT {dom : ℕ × ℕ} {σ : NatBTSort} {tb ts : Tier}
      (base : NatBTMor1Ramified (dom.1 + 1, dom.2) σ tb)
      (step :
        NatBTMor1Ramified (dom.1, dom.2 + 2) σ .nonRec)
      (tree : NatBTMor1Ramified dom .bt ts) :
      NatBTMor1Ramified dom σ .mayRec
```

- [ ] **Step 3: Register import and build**

```bash
lake build
```

- [ ] **Step 4: Commit**

```bash
git add GebLean/LawvereNatBTRamified.lean GebLean.lean
git commit -m "Define Tier and NatBTMor1Ramified inductive"
```

---

### Task 11: Define `NatBTMor1Ramified.interp`

**Files:**

* Modify: `GebLean/LawvereNatBTRamified.lean`.

- [ ] **Step 1: Add `interp` function**

```lean
def NatBTMor1Ramified.interp :
    {nm : ℕ × ℕ} → {σ : NatBTSort} → {t : Tier} →
    NatBTMor1Ramified nm σ t →
    (Fin nm.1 → ℕ) → (Fin nm.2 → BTL) →
    σ.carrier
  | _, _, _, NatBTMor1Ramified.zero, _, _ => 0
  | _, _, _, NatBTMor1Ramified.succ, ctxN, _ => (ctxN 0).succ
  | _, _, _, NatBTMor1Ramified.natProj i, ctxN, _ => ctxN i
  | _, _, _, NatBTMor1Ramified.sub, ctxN, _ =>
      (ctxN 0).sub (ctxN 1)
  | _, _, _, NatBTMor1Ramified.add, ctxN, _ =>
      (ctxN 0) + (ctxN 1)
  | _, _, _, NatBTMor1Ramified.mul, ctxN, _ =>
      (ctxN 0) * (ctxN 1)
  | _, _, _, NatBTMor1Ramified.leafBT, ctxN, _ =>
      BTL.leaf (ctxN 0)
  | _, _, _, NatBTMor1Ramified.nodeBT, _, ctxB =>
      BTL.node (ctxB 0) (ctxB 1)
  | _, _, _, NatBTMor1Ramified.btProj i, _, ctxB => ctxB i
  | _, _, _,
      NatBTMor1Ramified.natMatch zeroC succC n,
      ctxN, ctxB =>
    -- Corrected form below: natMatch handles one-level pattern
    -- match on the predecessor, not full recursion.  Only the
    -- corrected form is used.
  | _, _, _,
      NatBTMor1Ramified.natMatch zeroC succC n,
      ctxN, ctxB =>
    match n.interp ctxN ctxB with
    | 0 => zeroC.interp ctxN ctxB
    | k + 1 =>
        succC.interp (Fin.cons k (Fin.cons 0 ctxN)) ctxB
        -- (the k slot is the predecessor; the 0 is a placeholder
        -- since natMatch doesn't have a prev argument)
```

(Implementer: clarify the `natMatch` signature and interp to
match what's used downstream.  The `natMatch` destructor gives
access to the predecessor only — it's one-level pattern match,
not primitive recursion.)

- [ ] **Step 2: BtMatch case**

```lean
  | _, _, _,
      NatBTMor1Ramified.btMatch leafC nodeC tree,
      ctxN, ctxB =>
    match tree.interp ctxN ctxB with
    | BTL.leaf lbl =>
        leafC.interp (Fin.cons lbl ctxN) ctxB
    | BTL.node l r =>
        nodeC.interp ctxN (Fin.cons l (Fin.cons r ctxB))
```

- [ ] **Step 3: comp case**

```lean
  | _, _, _, NatBTMor1Ramified.comp f gNat gBT, ctxN, ctxB =>
    f.interp
      (fun i => (gNat i).interp ctxN ctxB)
      (fun i => (gBT i).interp ctxN ctxB)
```

- [ ] **Step 4: foldMutNat case**

```lean
  | _, _, _,
      NatBTMor1Ramified.foldMutNat base step n,
      ctxN, ctxB =>
    Nat.rec (base.interp ctxN ctxB)
      (fun j prev =>
        step.interp (Fin.cons j (Fin.cons prev ctxN)) ctxB)
      (n.interp ctxN ctxB)
```

Note: unbounded `Nat.rec` here.  Correctness (that this stays in
E_3) relies on tier discipline.

- [ ] **Step 5: foldMutBT case**

```lean
  | _, _, _,
      NatBTMor1Ramified.foldMutBT base step tree,
      ctxN, ctxB =>
    BTL.fold
      (fun lbl => base.interp (Fin.cons lbl ctxN) ctxB)
      (fun a b =>
        step.interp ctxN (Fin.cons a (Fin.cons b ctxB)))
      (tree.interp ctxN ctxB)
```

- [ ] **Step 6: Build and add per-constructor `@[simp]` lemmas**

For each constructor, add an `@[simp]` theorem of the form:

```lean
@[simp] theorem NatBTMor1Ramified.interp_zero
    {nm : ℕ × ℕ}
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    (NatBTMor1Ramified.zero (nm := nm)).interp ctxN ctxB = 0 :=
  rfl

@[simp] theorem NatBTMor1Ramified.interp_succ ...
-- ... one per constructor
```

Implementer: add all ~13 `@[simp]` lemmas.

- [ ] **Step 7: Build, test, commit**

```bash
lake build
lake test
git add GebLean/LawvereNatBTRamified.lean
git commit -m "Add NatBTMor1Ramified.interp with per-constructor simp lemmas"
```

---

### Task 12: Define the interp functor for the ramified theory

**Files:**

* Create: `GebLean/LawvereNatBTRamifiedInterp.lean`.
* Modify: `GebLean.lean` — add import.

- [ ] **Step 1: Create file**

```lean
import GebLean.LawvereNatBTRamified
import Mathlib.CategoryTheory.Types

/-!
# Interpretation Functor for `LawvereNatBT_ramified`
-/

namespace GebLean

def natBTRamifiedInterpFunctor :
    LawvereNatBTRamifiedCat ⥤ Type := {
  obj := fun (n, m) => (Fin n → ℕ) × (Fin m → BTL)
  map := fun f => ... -- interp-lift
  ...
}
```

- [ ] **Step 2: Prove faithful**

```lean
instance : Functor.Faithful natBTRamifiedInterpFunctor := ...
```

Mirrors the existing `natBTInterpFunctor` faithfulness proof in
`LawvereNatBTInterp.lean`.

- [ ] **Step 3: Build, commit**

```bash
lake build
git add GebLean/LawvereNatBTRamifiedInterp.lean GebLean.lean
git commit -m "Add interp functor for ramified theory; prove faithful"
```

---

### Task 13: Define the quotient category for ramified

**Files:**

* Create: `GebLean/LawvereNatBTRamifiedQuot.lean`.
* Modify: `GebLean.lean` — add import.

- [ ] **Step 1: Create file with setoid and quotient**

Mirrors `LawvereNatBTQuot.lean`:

```lean
import GebLean.LawvereNatBTRamified
import Mathlib.CategoryTheory.Category.Basic
-- ...

namespace GebLean

def NatBTMor1RamifiedSetoid (n m : ℕ × ℕ) : Setoid (... ) := ...

def NatBTMorNRamifiedQuo (nm nm' : ℕ × ℕ) : Type := ...

-- Identity, composition, category instance
```

Category instance with associativity, identity laws proved over
the quotient.

- [ ] **Step 2: Prove `HasChosenFiniteProducts`**

Mirror existing proof structure.

- [ ] **Step 3: Build, test, commit**

```bash
lake build
lake test
git add GebLean/LawvereNatBTRamifiedQuot.lean GebLean.lean
git commit -m "Add category and products for ramified theory"
```

---

## Stage δ.b: Back-translation F21 (ramified → bounded)

### Task 14: Bound-derivation helper

**Files:**

* Modify: `GebLean/LawvereERBoundComputable.lean` — extend with
  ramified-specific helper.
* Create: `GebLean/LawvereNatBTRamifiedBackTrans.lean`.

- [ ] **Step 1: Add `natBTRamifiedBound` function**

Given a ramified step term of tier `NonRec` with tower height
`h_s`, compute an adequate bound as an ERMor1 term whose tower
height is `h_s + const`.

```lean
def NatBTMor1Ramified.siteBound
    (step : NatBTMor1Ramified _ _ .nonRec) : ERMor1 _ := ...
```

- [ ] **Step 2: Prove adequacy**

```lean
theorem NatBTMor1Ramified.siteBound_dominates ...
```

This is analogous to `ERMor1.lt_tower_towerHeight` but applied
at the NatBT level.

- [ ] **Step 3: Build and commit**

```bash
lake build
git add GebLean/LawvereERBoundComputable.lean \
        GebLean/LawvereNatBTRamifiedBackTrans.lean
git commit -m "Add bound-derivation helper for ramified back-translation"
```

---

### Task 15: Define `F21 : Ramified → Bounded`

**Files:**

* Modify: `GebLean/LawvereNatBTRamifiedBackTrans.lean`.

- [ ] **Step 1: Structural translation**

```lean
def NatBTMor1Ramified.toBounded :
    {nm : ℕ × ℕ} → {σ : NatBTSort} → {t : Tier} →
    NatBTMor1Ramified nm σ t → NatBTMor1 nm σ
  | _, _, _, .zero => NatBTMor1.zero
  | _, _, _, .succ => NatBTMor1.succ (NatBTMor1.natProj 0)
  | _, _, _, .natProj i => NatBTMor1.natProj i
  | _, _, _, .sub =>
      NatBTMor1.sub (NatBTMor1.natProj 0) (NatBTMor1.natProj 1)
  | _, _, _, .add =>
      -- Derive addition from bsum of 1
      NatBTMor1.bsum (NatBTMor1.succ (NatBTMor1.natProj 0)) |>.comp ...
  | _, _, _, .mul =>
      -- Derive multiplication from bprod
      ...
  -- ... etc
  | _, _, _, .foldMutNat base step n =>
      NatBTMor1.boundedNatRec
        base.toBounded step.toBounded n.toBounded
        (step.siteBound -- via Task 14
          -- wrapped as NatBTMor1 (nm.1 + 1, nm.2) .nat
          ...)
  | _, _, _, .foldMutBT base step tree =>
      NatBTMor1.foldBTNat -- or foldBTBT depending on σ
        base.toBounded step.toBounded tree.toBounded
        (tree.siteBound ...)
```

- [ ] **Step 2: Lift to NatBTMorN tuples**

- [ ] **Step 3: Define the functor**

```lean
def ramifiedToBoundedFunctor :
    LawvereNatBTRamifiedCat ⥤ LawvereNatBTCat := ...
```

- [ ] **Step 4: Build, test, commit**

```bash
lake build
lake test
git add GebLean/LawvereNatBTRamifiedBackTrans.lean
git commit -m "Define F21 : ramified → bounded back-translation"
```

---

### Task 16: Prove `F21` interp-preservation

**Files:**

* Modify: `GebLean/LawvereNatBTRamifiedBackTrans.lean`.

- [ ] **Step 1: Mutual induction over ramified morphisms**

```lean
theorem NatBTMor1Ramified.toBounded_interp
    {nm σ t} (r : NatBTMor1Ramified nm σ t)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    r.toBounded.interp ctxN ctxB = r.interp ctxN ctxB := ...
```

Base cases: direct.
Inductive cases for `comp`, `natMatch`, `btMatch`: recursive.
Inductive cases for `foldMutNat`, `foldMutBT`: use
`interp_boundedNatRec` and `interp_foldBTNat` from the bounded
theory + bound-adequacy from Task 14.

- [ ] **Step 2: Build, test, commit**

```bash
lake build
lake test
git add GebLean/LawvereNatBTRamifiedBackTrans.lean
git commit -m "Prove F21 interp preservation"
```

---

## Stage δ.c: Forward translation F12 (bounded → ramified)

### Task 17: Define `F12`

**Files:**

* Modify: `GebLean/LawvereNatBTRamifiedBackTrans.lean`.

- [ ] **Step 1: Structural translation**

```lean
def NatBTMor1.toRamified :
    {nm : ℕ × ℕ} → {σ : NatBTSort} →
    NatBTMor1 nm σ → NatBTMor1Ramified nm σ _
  | _, _, .zero => .zero
  | _, _, .succ x => .succ.comp ![x.toRamified]
  -- ... etc
  | _, _, .bsum f =>
      -- Derive bsum via foldMutNat with arithmetic step
      .foldMutNat .zero
        (.add.comp ![.natProj 1, f.toRamified.comp ![.natProj 0, ...]])
        (.natProj 0)
  | _, _, .bprod f => -- similar with mul
      ...
  | _, _, .foldBTNat base step tree bound =>
      .foldMutBT base.toRamified step.toRamified tree.toRamified
      -- Bound is dropped; ramified theory doesn't need it.
  -- ... etc
```

- [ ] **Step 2: Lift and functor**

- [ ] **Step 3: Build, commit**

```bash
lake build
git add GebLean/LawvereNatBTRamifiedBackTrans.lean
git commit -m "Define F12 : bounded → ramified forward translation"
```

---

### Task 18: Prove `F12` interp-preservation

**Files:**

* Modify: `GebLean/LawvereNatBTRamifiedBackTrans.lean`.

- [ ] **Step 1: Mutual induction**

```lean
theorem NatBTMor1.toRamified_interp {nm σ}
    (t : NatBTMor1 nm σ)
    (ctxN : Fin nm.1 → ℕ) (ctxB : Fin nm.2 → BTL) :
    t.toRamified.interp ctxN ctxB = t.interp ctxN ctxB := ...
```

For fold cases: the bounded theory's interp is `min (unbounded)
(bound)`.  The ramified theory's interp is unbounded.  These
agree only when the bound dominates the unbounded value.

Question for implementer: does this conditional correctness
require an adequacy hypothesis?  In the bounded theory, the
bound is part of the constructor, so interp always uses it.  In
the ramified theory, there's no bound.  If the bounded bound is
ALWAYS adequate (because it was supplied correctly at
construction), we're fine.  If not, we need either:

(a) A precondition on the bounded theory's constructors that
    bound is adequate.
(b) State `F12`'s correctness with a bound-adequacy hypothesis.

Decision: state a correctness theorem with adequacy hypothesis
explicitly; the implementer can discharge adequacy in specific
use cases.

- [ ] **Step 2: Build, test, commit**

```bash
lake build
lake test
git add GebLean/LawvereNatBTRamifiedBackTrans.lean
git commit -m "Prove F12 interp preservation (conditional on bound adequacy)"
```

---

## Stage δ.d: Assemble equivalence 2

### Task 19: Assemble `LawvereNatBT_bounded ≃ LawvereNatBT_ramified`

**Files:**

* Create: `GebLean/LawvereNatBTRamifiedEquivBounded.lean`.

- [ ] **Step 1: Create file and prove natural isomorphism**

```lean
import GebLean.LawvereNatBTRamifiedBackTrans

/-!
# Equivalence `LawvereNatBT_bounded ≃ LawvereNatBT_ramified`
-/

namespace GebLean

theorem f21_f12_id : ∀ t, ... := ...
theorem f12_f21_id : ∀ r, ... := ...

def lawvereBoundedRamifiedEquivalence :
    LawvereNatBTCat ≌ LawvereNatBTRamifiedCat := ...

end GebLean
```

- [ ] **Step 2: Register, build, test, commit**

```bash
lake build
lake test
git add GebLean/LawvereNatBTRamifiedEquivBounded.lean GebLean.lean
git commit -m "Prove LawvereNatBT_bounded ≃ LawvereNatBT_ramified equivalence"
```

---

## Stage δ.e: Compose and finalize

### Task 20: Transitive composition

**Files:**

* Create: `GebLean/LawvereNatBTRamifiedEquivER.lean`.

- [ ] **Step 1: Compose the two equivalences**

```lean
def lawvereRamifiedERCatEquivalence :
    LawvereNatBTRamifiedCat ≌ LawvereERCat :=
  lawvereBoundedRamifiedEquivalence.symm.trans
    lawvereNatBTBoundedERCatEquivalence
```

- [ ] **Step 2: Build, commit**

```bash
lake build
git add GebLean/LawvereNatBTRamifiedEquivER.lean GebLean.lean
git commit -m "Compose chain: LawvereERCat ≃ LawvereNatBT_ramified"
```

---

### Task 21: Transport Phase 4f results

**Files:**

* Modify: `GebLean/LawvereNatBTRamifiedEquivER.lean`.

- [ ] **Step 1: Transport Ackermann non-fullness**

```lean
theorem ackermann_not_ramified_definable : ...
```

Via the equivalence from Task 20 and the existing
`erInterpFunctor_not_full` result.

- [ ] **Step 2: Transport tetration non-elementarity**

```lean
theorem tetration_not_ramified_definable : ...
```

- [ ] **Step 3: Build, commit**

```bash
lake build
git add GebLean/LawvereNatBTRamifiedEquivER.lean
git commit -m "Transport Phase 4f non-fullness results to ramified"
```

---

### Task 22: Tests

**Files:**

* Create: `GebLeanTests/LawvereNatBTRamified.lean`.
* Create: `GebLeanTests/LawvereNatBTRamifiedEquiv.lean`.
* Modify: `GebLeanTests.lean` — add imports.

- [ ] **Step 1: Tests for ramified theory interp**

```lean
-- Sanity checks: basic arithmetic, fold on small trees, etc.
example : (NatBTMor1Ramified.add (nm := (2, 0))).interp ![3, 5] Fin.elim0 = 8
  := rfl
-- ... etc
```

- [ ] **Step 2: Tests for equivalence**

Show that specific ER morphisms translate round-trip through
the equivalence and give the same interp.

- [ ] **Step 3: Build, test, commit**

```bash
lake build
lake test
git add GebLeanTests/ GebLeanTests.lean
git commit -m "Add tests for ramified theory and equivalence"
```

---

### Task 23: Workstream tracker update

**Files:**

* Modify: `.session/workstreams/lawvere-elementary-recursive.md`.

- [ ] **Step 1: Record two-stage completion**

Add entries for each committed task.  Mark Stage β and Stage δ
complete.  Update the "Current resume point" to point at
deferred work (Task 14.5-extended for BT-only adequacy
research, and Stage γ for lex completion).

- [ ] **Step 2: Commit**

```bash
git add .session/workstreams/lawvere-elementary-recursive.md
git commit -m "Workstream tracker: Stage β and Stage δ complete"
```

---

## Self-Review

**Spec coverage:**

* D1 (LawvereER fixed baseline): preserved throughout; no tasks
  modify `LawvereERQuot.lean`.
* D2 (priority order): Tasks 14, 15, 17 use tier discipline to
  preserve strength match; no bound required at client sites in
  the ramified theory.
* D3 (two-stage chain): Stages β.a-β.b for equivalence 1;
  δ.a-δ.d for equivalence 2; δ.e for composition.
* D4 (pairing in equivalence 1): Task 8 uses
  `toERUniform`/`btlEncodeNode`; Tasks 14-19 avoid pairing.
* D5 (Leivant-standard primitives): Task 10 adds `add`/`mul` as
  NonRec.
* D6 (3-indexed syntactic inductive): Task 10.
* D7 (single recursive destructor): Task 10 defines `foldMutNat`
  and `foldMutBT`.
* D8 (pair-structured objects): preserved throughout; objects
  remain `(n, m) : ℕ × ℕ`.

**Placeholder scan:** several tasks have `...` in code sketches;
implementer fills in following the established patterns.  No
"TBD" or "TODO".

**Type consistency:** the names used across tasks (`toERUniform`,
`toBounded`, `toRamified`, `foldMutNat`, `foldMutBT`,
`siteBound`) are consistent throughout.

---

## Completion criteria

The plan is complete when:

1. Stage β.a-β.b: `LawvereERCat ≃ LawvereNatBT_bounded` proved
   and committed.
2. Stage δ.a-δ.d: `LawvereNatBT_bounded ≃ LawvereNatBT_ramified`
   proved and committed.
3. Stage δ.e: composed equivalence proved.
4. Phase 4f results transported.
5. `lake build` and `lake test` pass with zero warnings.
6. Workstream tracker reflects completion.

After completion, Task 14.5-extended (BT-only adequacy research)
and Stage γ (lex completion of ramified theory) become
candidates.
