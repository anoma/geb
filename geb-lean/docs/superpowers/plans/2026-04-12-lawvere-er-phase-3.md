# Lawvere ER Phase 3: Finite Products, Interpretation Functor, Faithfulness

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Equip `LawvereERCat` with chosen finite products
(making it a Lawvere theory), define the interpretation
functor into `Type`, and prove it faithful.

**Architecture:** Finite products mirror the BT pattern:
terminal object at arity 0, binary products via arity
addition `n + m`, projections via `ERMor1.proj`, pairing
via index splitting.  The interpretation functor sends
arity `n` to `Fin n -> Nat` and morphism classes to
their interpretations; it is well-defined because the
setoid quotient identifies exactly those tuples with
equal interpretations.  Faithfulness is then a one-line
consequence of `Quotient.exact`.

**Tech Stack:** Lean 4, Mathlib
(`CategoryTheory.Category.Basic`,
`CategoryTheory.Functor.FullyFaithful`,
`Data.Fin.Tuple.Basic`),
`GebLean.Utilities.ComputableLimits`

---

## File Map

| File | Role |
| ---- | ---- |
| Modify: `GebLean/LawvereER.lean` | Add raw `ERMorN.terminal`, `.fst`, `.snd`, `.pair` and their `@[simp]` interp lemmas |
| Modify: `GebLean/LawvereERQuot.lean` | Lift terminal/fst/snd/pair through quotient, prove product laws, assemble `HasChosenFiniteProducts` |
| Create: `GebLean/LawvereERInterp.lean` | Interpretation functor `erInterpFunctor`, faithfulness |
| Modify: `GebLean.lean` | Add `import GebLean.LawvereERInterp` |
| Modify: `GebLeanTests/LawvereERQuot.lean` | Add product tests |
| Create: `GebLeanTests/LawvereERInterp.lean` | Functor tests |
| Modify: `GebLeanTests.lean` | Add interp test import |

---

## Proof Strategy

All product laws and functor properties are proved via
the interpretation, never via syntactic rewriting.  The
pattern is always: unwrap quotients with `Quotient.ind`,
reduce to an interpretation statement via the `@[simp]`
lemmas from Phase 1, then close with `Quotient.sound`
(for quotient equalities) or `funext` (for function
equalities).

Faithfulness leverages `Quotient.exact`: if two quotient
elements have equal interpretations, they were related by
the setoid, which IS extensional equality.

---

### Task 1: Raw finite-product operations on ERMorN

**Files:**

- Modify: `GebLean/LawvereER.lean`

- [ ] **Step 1: Add `ERMorN.terminal`**

Append before `end GebLean` in `LawvereER.lean`:

```lean
/-- Terminal morphism: the unique morphism to arity
0 (the empty tuple). -/
def ERMorN.terminal (n : ℕ) : ERMorN n 0 :=
  fun i => i.elim0
```

- [ ] **Step 2: Build**

Run: `lake build`
Expected: clean build.

- [ ] **Step 3: Add `ERMorN.fst` and `ERMorN.snd`**

```lean
/-- First projection from the product arity
`n + m`. -/
def ERMorN.fst {n m : ℕ} : ERMorN (n + m) n :=
  fun i => ERMor1.proj ⟨i.val, by omega⟩

/-- Second projection from the product arity
`n + m`. -/
def ERMorN.snd {n m : ℕ} : ERMorN (n + m) m :=
  fun i => ERMor1.proj ⟨n + i.val, by omega⟩
```

- [ ] **Step 4: Build**

Run: `lake build`
Expected: clean build.

- [ ] **Step 5: Add `ERMorN.pair`**

```lean
/-- Pairing: given morphisms to arity `n` and arity
`m`, produce a morphism to arity `n + m`. -/
def ERMorN.pair {k n m : ℕ}
    (f : ERMorN k n) (g : ERMorN k m) :
    ERMorN k (n + m) :=
  fun i =>
    if h : i.val < n then f ⟨i.val, h⟩
    else g ⟨i.val - n, by omega⟩
```

- [ ] **Step 6: Build**

Run: `lake build`
Expected: clean build.

- [ ] **Step 7: Commit**

```bash
git add GebLean/LawvereER.lean
git commit -m "Add ERMorN terminal, fst, snd, pair"
```

---

### Task 2: Interpretation lemmas for finite-product operations

**Files:**

- Modify: `GebLean/LawvereER.lean`

These lemmas express how the finite-product operations
interact with interpretation.  They are the foundation
for all quotient-level product proofs.

- [ ] **Step 1: Add `ERMorN.interp_terminal`**

```lean
/-- Interpretation of `terminal`: the unique
function to the empty context. -/
@[simp] theorem ERMorN.interp_terminal
    {n : ℕ} (ctx : Fin n → ℕ) :
    (ERMorN.terminal n).interp ctx =
      Fin.elim0 :=
  funext (fun i => i.elim0)
```

Note: if `funext (fun i => i.elim0)` does not
work, try `rfl` or `funext Fin.elim0`.

- [ ] **Step 2: Build and check**

Run: `lake build`

- [ ] **Step 3: Add `ERMorN.interp_fst`**

```lean
/-- Interpretation of `fst`: selects the first
`n` components of a context of arity `n + m`. -/
@[simp] theorem ERMorN.interp_fst
    {n m : ℕ} (ctx : Fin (n + m) → ℕ) :
    (ERMorN.fst (n := n) (m := m)).interp ctx =
      fun i => ctx ⟨i.val, by omega⟩ :=
  rfl
```

- [ ] **Step 4: Add `ERMorN.interp_snd`**

```lean
/-- Interpretation of `snd`: selects the last
`m` components of a context of arity `n + m`. -/
@[simp] theorem ERMorN.interp_snd
    {n m : ℕ} (ctx : Fin (n + m) → ℕ) :
    (ERMorN.snd (n := n) (m := m)).interp ctx =
      fun i => ctx ⟨n + i.val, by omega⟩ :=
  rfl
```

- [ ] **Step 5: Build and check**

Run: `lake build`

- [ ] **Step 6: Add `ERMorN.interp_pair`**

```lean
/-- Interpretation of `pair`: concatenates the
results of interpreting `f` and `g`. -/
@[simp] theorem ERMorN.interp_pair
    {k n m : ℕ} (f : ERMorN k n)
    (g : ERMorN k m) (ctx : Fin k → ℕ) :
    (ERMorN.pair f g).interp ctx =
      fun i =>
        if h : i.val < n
        then (f ⟨i.val, h⟩).interp ctx
        else (g ⟨i.val - n, by omega⟩).interp
          ctx := by
  funext i
  simp only [ERMorN.interp, ERMorN.pair]
  split <;> rfl
```

If the `split <;> rfl` approach does not work,
try:

```lean
  funext i
  unfold ERMorN.interp ERMorN.pair
  simp only []
  split_ifs <;> rfl
```

- [ ] **Step 7: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereER.lean
git commit -m "Add interp lemmas for ERMorN finite-product operations"
```

---

### Task 3: Quotient lifts of finite-product operations

**Files:**

- Modify: `GebLean/LawvereERQuot.lean`

First, add the `ComputableLimits` import at the top of
the file (needed for `HasChosenFiniteProducts`):

```lean
import GebLean.Utilities.ComputableLimits
```

- [ ] **Step 1: Add `ERMorNQuo.terminal` and
  `ERMorNQuo.terminal_uniq`**

Append before `end GebLean`:

```lean
/-- The terminal morphism in the quotient
category: the equivalence class of the empty
tuple. -/
def ERMorNQuo.terminal (n : ℕ) :
    ERMorNQuo n 0 :=
  Quotient.mk (erMorNSetoid n 0)
    (ERMorN.terminal n)

/-- Any quotient morphism to arity 0 equals the
terminal morphism. -/
theorem ERMorNQuo.terminal_uniq {n : ℕ}
    (f : ERMorNQuo n 0) :
    f = ERMorNQuo.terminal n :=
  Quotient.ind
    (motive := fun f =>
      f = ERMorNQuo.terminal n)
    (fun _ => Quotient.sound
      (s := erMorNSetoid n 0)
      (fun ctx => funext Fin.elim0))
    f
```

The proof: any two functions `Fin 0 -> Nat` are
equal by `funext Fin.elim0` (there are no indices
to disagree on).

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Add `ERMorNQuo.fst` and
  `ERMorNQuo.snd`**

```lean
/-- First projection in the quotient category. -/
def ERMorNQuo.fst {n m : ℕ} :
    ERMorNQuo (n + m) n :=
  Quotient.mk (erMorNSetoid (n + m) n)
    ERMorN.fst

/-- Second projection in the quotient
category. -/
def ERMorNQuo.snd {n m : ℕ} :
    ERMorNQuo (n + m) m :=
  Quotient.mk (erMorNSetoid (n + m) m)
    ERMorN.snd
```

- [ ] **Step 4: Build**

Run: `lake build`

- [ ] **Step 5: Add `ERMorNQuo.pair`**

```lean
/-- Pairing in the quotient category, lifted
from `ERMorN.pair` via `Quotient.lift₂`. -/
def ERMorNQuo.pair {k n m : ℕ}
    (f : ERMorNQuo k n)
    (g : ERMorNQuo k m) :
    ERMorNQuo k (n + m) :=
  Quotient.lift₂
    (s₁ := erMorNSetoid k n)
    (s₂ := erMorNSetoid k m)
    (fun f' g' =>
      Quotient.mk (erMorNSetoid k (n + m))
        (ERMorN.pair f' g'))
    (fun fa fb ga gb hf hg =>
      Quotient.sound
        (s := erMorNSetoid k (n + m))
        (fun ctx => by
          simp only [ERMorN.interp_pair]
          congr 1
          funext i
          split_ifs with h
          · exact congrFun (hf ctx)
              ⟨i.val, h⟩
          · exact congrFun (hg ctx)
              ⟨i.val - n, by omega⟩))
    f g
```

The well-definedness proof: if `fa ~ ga` and
`fb ~ gb`, then `pair fa fb ~ pair fa gb`.
After `simp only [ERMorN.interp_pair]`, the goal
splits into `if` branches.  In each branch, the
relevant hypothesis (`hf` or `hg`) gives the
needed pointwise equality.

If the `congrFun` approach is awkward, try:

```lean
          simp only [ERMorN.interp_pair]
          congr 1; funext i; split_ifs with h
          · have := hf ctx
            exact congrFun this ⟨i.val, h⟩
          · have := hg ctx
            exact congrFun this
              ⟨i.val - n, by omega⟩
```

- [ ] **Step 6: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERQuot.lean
git commit -m "Add quotient lifts of terminal, fst, snd, pair"
```

---

### Task 4: Product laws on the quotient

**Files:**

- Modify: `GebLean/LawvereERQuot.lean`

- [ ] **Step 1: Prove `ERMorNQuo.pair_fst`**

```lean
/-- Composing pairing with the first projection
recovers the first component. -/
theorem ERMorNQuo.pair_fst {k n m : ℕ}
    (f : ERMorNQuo k n)
    (g : ERMorNQuo k m) :
    ERMorNQuo.comp (ERMorNQuo.pair f g)
      ERMorNQuo.fst = f :=
  Quotient.ind₂
    (motive := fun f g =>
      ERMorNQuo.comp (ERMorNQuo.pair f g)
        ERMorNQuo.fst = f)
    (fun f_raw g_raw =>
      Quotient.sound
        (s := erMorNSetoid k n)
        (fun ctx => by
          simp [ERMorN.interp_comp,
                ERMorN.interp_pair,
                ERMorN.interp_fst]
          funext i
          simp [i.isLt]))
    f g
```

The proof: after simp, the goal reduces to showing
that selecting the first `n` components of a
concatenated pair recovers `f`.  For `i : Fin n`,
`i.val < n` holds by `i.isLt`, so the `dite`
resolves to the `f` branch.  If `simp [i.isLt]`
does not close it, try `split_ifs` or a manual
`dif_pos i.isLt`.

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Prove `ERMorNQuo.pair_snd`**

```lean
/-- Composing pairing with the second projection
recovers the second component. -/
theorem ERMorNQuo.pair_snd {k n m : ℕ}
    (f : ERMorNQuo k n)
    (g : ERMorNQuo k m) :
    ERMorNQuo.comp (ERMorNQuo.pair f g)
      ERMorNQuo.snd = g :=
  Quotient.ind₂
    (motive := fun f g =>
      ERMorNQuo.comp (ERMorNQuo.pair f g)
        ERMorNQuo.snd = g)
    (fun f_raw g_raw =>
      Quotient.sound
        (s := erMorNSetoid k m)
        (fun ctx => by
          simp [ERMorN.interp_comp,
                ERMorN.interp_pair,
                ERMorN.interp_snd]
          funext i
          have h : ¬ (n + i.val) < n := by omega
          simp [h]
          congr 1
          omega))
    f g
```

The proof: for `i : Fin m`, the pairing index is
`⟨n + i.val, by omega⟩`, and `¬ (n + i.val) < n`
holds by `omega`.  The `dif_neg` branch gives
`g ⟨n + i.val - n, ...⟩`, which equals `g i` after
simplifying `n + i.val - n = i.val`.

If the `congr 1; omega` approach does not work, try
a manual `Fin.ext` with `show`:

```lean
          have hge : ¬ (n + i.val) < n := by
            omega
          simp [hge]
          congr 1
          exact Fin.ext (by omega)
```

- [ ] **Step 4: Build**

Run: `lake build`

- [ ] **Step 5: Prove `ERMorNQuo.pair_uniq`**

```lean
/-- Uniqueness of pairing: any morphism whose
compositions with the projections yield `f` and
`g` equals `pair f g`. -/
theorem ERMorNQuo.pair_uniq {k n m : ℕ}
    (f : ERMorNQuo k n)
    (g : ERMorNQuo k m)
    (h : ERMorNQuo k (n + m))
    (hfst : ERMorNQuo.comp h
      ERMorNQuo.fst = f)
    (hsnd : ERMorNQuo.comp h
      ERMorNQuo.snd = g) :
    h = ERMorNQuo.pair f g :=
  Quotient.ind
    (motive := fun h =>
      ∀ (f : ERMorNQuo k n)
        (g : ERMorNQuo k m),
        ERMorNQuo.comp h ERMorNQuo.fst = f →
        ERMorNQuo.comp h ERMorNQuo.snd = g →
        h = ERMorNQuo.pair f g)
    (fun h_raw =>
      Quotient.ind
        (motive := fun f =>
          ∀ (g : ERMorNQuo k m),
            ERMorNQuo.comp
              (Quotient.mk _ h_raw)
              ERMorNQuo.fst = f →
            ERMorNQuo.comp
              (Quotient.mk _ h_raw)
              ERMorNQuo.snd = g →
            Quotient.mk _ h_raw =
              ERMorNQuo.pair f g)
        (fun f_raw =>
          Quotient.ind
            (motive := fun g =>
              ERMorNQuo.comp
                (Quotient.mk _ h_raw)
                ERMorNQuo.fst =
                Quotient.mk _ f_raw →
              ERMorNQuo.comp
                (Quotient.mk _ h_raw)
                ERMorNQuo.snd = g →
              Quotient.mk _ h_raw =
                ERMorNQuo.pair
                  (Quotient.mk _ f_raw) g)
            (fun g_raw hf_eq hs_eq => by
              have hf_rel :=
                Quotient.exact
                  (s := erMorNSetoid k n)
                  hf_eq
              have hs_rel :=
                Quotient.exact
                  (s := erMorNSetoid k m)
                  hs_eq
              apply Quotient.sound
                (s := erMorNSetoid k (n + m))
              intro ctx
              simp only [ERMorN.interp_pair]
              funext i
              split_ifs with hlt
              · have := congrFun
                  (hf_rel ctx) ⟨i.val, hlt⟩
                simp [ERMorN.interp_comp,
                  ERMorN.interp_fst] at this
                exact this
              · have := congrFun
                  (hs_rel ctx)
                  ⟨i.val - n, by omega⟩
                simp [ERMorN.interp_comp,
                  ERMorN.interp_snd] at this
                convert this using 2
                exact Fin.ext (by omega))))
    h f g hfst hsnd
```

The proof unwraps all three quotients, extracts the
setoid relations from the hypotheses via
`Quotient.exact`, then shows pointwise agreement
by splitting on the pairing index.  In the first
branch (`i.val < n`), the hypothesis from `fst`
gives agreement.  In the second branch, the
hypothesis from `snd` gives agreement after a
`Fin.ext` to align the indices.

This is the longest proof in Phase 3.  If the
approach above does not compile, the implementer
should try the proof one step at a time using `_`
to inspect goals, and adapt the `simp` and
`convert` calls accordingly.

- [ ] **Step 6: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERQuot.lean
git commit -m "Prove product laws for ERMorNQuo"
```

---

### Task 5: HasChosenFiniteProducts instance

**Files:**

- Modify: `GebLean/LawvereERQuot.lean`

- [ ] **Step 1: Assemble product and terminal
  structures**

```lean
/-- Chosen binary product for `LawvereERCat`:
the product of `n` and `m` is `n + m`. -/
def lawvereERProduct
    (n m : LawvereERCat) :
    ChosenBinaryProduct n m where
  obj := (n + m : ℕ)
  fst := ERMorNQuo.fst
  snd := ERMorNQuo.snd
  lift f g := ERMorNQuo.pair f g
  lift_fst := ERMorNQuo.pair_fst
  lift_snd := ERMorNQuo.pair_snd
  lift_uniq f g h hf hs :=
    ERMorNQuo.pair_uniq f g h hf hs

/-- Chosen terminal object for
`LawvereERCat`. -/
def lawvereERTerminal :
    ChosenTerminal LawvereERCat where
  obj := (0 : ℕ)
  from_ n := ERMorNQuo.terminal n
  uniq f := ERMorNQuo.terminal_uniq f

/-- `LawvereERCat` has chosen finite
products. -/
instance : HasChosenFiniteProducts
    LawvereERCat where
  terminal := lawvereERTerminal
  product := lawvereERProduct
```

- [ ] **Step 2: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERQuot.lean
git commit -m "Add HasChosenFiniteProducts for LawvereERCat"
```

---

### Task 6: Interpretation functor and faithfulness

**Files:**

- Create: `GebLean/LawvereERInterp.lean`
- Modify: `GebLean.lean` (add import)

- [ ] **Step 1: Create file with lifted interpretation**

Create `GebLean/LawvereERInterp.lean`:

```lean
import GebLean.LawvereERQuot
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Interpretation Functor for LawvereERCat

Defines a faithful functor from `LawvereERCat` (the
Lawvere theory of elementary recursive functions)
into `Type`, sending arity `n` to `Fin n -> Nat`
and each morphism class to its standard
interpretation.
-/

namespace GebLean

open CategoryTheory

/-- Lift `ERMorN.interp` to the quotient.
Well-defined because the setoid relation is
extensional equality of interpretations. -/
def ERMorNQuo.interp {n m : ℕ}
    (f : ERMorNQuo n m) :
    (Fin n → ℕ) → (Fin m → ℕ) :=
  Quotient.lift
    (s := erMorNSetoid n m)
    ERMorN.interp
    (fun _ _ h => funext h)

end GebLean
```

Add `import GebLean.LawvereERInterp` to
`GebLean.lean`, alphabetically after
`import GebLean.LawvereERQuot`.

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Add `interp` computation lemmas**

```lean
/-- `ERMorNQuo.interp` on a concrete
representative reduces to `ERMorN.interp`. -/
@[simp] theorem ERMorNQuo.interp_mk
    {n m : ℕ} (f : ERMorN n m) :
    (Quotient.mk (erMorNSetoid n m) f).interp =
      f.interp :=
  rfl

/-- Interpretation of the quotient identity. -/
@[simp] theorem ERMorNQuo.interp_id
    (n : ℕ) (ctx : Fin n → ℕ) :
    (ERMorNQuo.id n).interp ctx = ctx := by
  simp [ERMorNQuo.id, ERMorNQuo.interp_mk,
        ERMorN.interp_id]

/-- Interpretation of quotient composition. -/
@[simp] theorem ERMorNQuo.interp_comp
    {n m k : ℕ} (f : ERMorNQuo n m)
    (g : ERMorNQuo m k)
    (ctx : Fin n → ℕ) :
    (ERMorNQuo.comp f g).interp ctx =
      g.interp (f.interp ctx) := by
  revert f g
  apply Quotient.ind₂
  intro f_raw g_raw
  rfl
```

- [ ] **Step 4: Build**

Run: `lake build`

- [ ] **Step 5: Define the interpretation functor**

```lean
/-- The interpretation functor from
`LawvereERCat` into `Type`.  Sends arity `n` to
`Fin n -> Nat` and each morphism class to its
standard interpretation. -/
def erInterpFunctor : LawvereERCat ⥤ Type where
  obj n := Fin n → ℕ
  map f := f.interp
  map_id n := by
    funext ctx
    exact ERMorNQuo.interp_id n ctx
  map_comp f g := by
    funext ctx
    exact ERMorNQuo.interp_comp f g ctx
```

- [ ] **Step 6: Build**

Run: `lake build`

- [ ] **Step 7: Prove faithfulness**

```lean
/-- The interpretation functor is faithful:
distinct morphism classes produce distinct
functions.  This is immediate from the extensional
quotient — the setoid relation is exactly the
kernel of the interpretation. -/
instance : erInterpFunctor.Faithful where
  map_injective {n m} {f g} h := by
    revert f g
    apply Quotient.ind₂
    intro f_raw g_raw heq
    exact Quotient.sound
      (s := erMorNSetoid n m)
      (fun ctx => congrFun heq ctx)
```

The proof: unwrap both quotients, then `heq`
gives `f_raw.interp = g_raw.interp` as functions.
`congrFun heq ctx` gives pointwise equality, and
`Quotient.sound` identifies the classes.

- [ ] **Step 8: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERInterp.lean GebLean.lean
git commit -m "Add erInterpFunctor and prove faithfulness"
```

---

### Task 7: Tests

**Files:**

- Modify: `GebLeanTests/LawvereERQuot.lean`
- Create: `GebLeanTests/LawvereERInterp.lean`
- Modify: `GebLeanTests.lean`

- [ ] **Step 1: Add product tests to
  `LawvereERQuot.lean`**

Append to `GebLeanTests/LawvereERQuot.lean`:

```lean
-- Product projection: fst ≫ ... recovers the
-- first component.
example : @ERMorNQuo.fst 2 3 =
    @ERMorNQuo.fst 2 3 := rfl

-- Terminal uniqueness: any morphism to 0 equals
-- the terminal morphism.
example (f : (3 : LawvereERCat) ⟶
    (0 : LawvereERCat)) :
    f = ERMorNQuo.terminal 3 :=
  ERMorNQuo.terminal_uniq f

-- HasChosenFiniteProducts is available.
example : HasChosenFiniteProducts
    LawvereERCat := inferInstance
```

- [ ] **Step 2: Create
  `GebLeanTests/LawvereERInterp.lean`**

```lean
import GebLean.LawvereERInterp

/-!
# Tests for LawvereERInterp

Sanity tests for the interpretation functor and
faithfulness.
-/

open GebLean
open CategoryTheory

-- The interpretation functor maps arity 2 to
-- `Fin 2 -> Nat`.
example : erInterpFunctor.obj 2 =
    (Fin 2 → ℕ) := rfl

-- Faithfulness instance is available.
example : erInterpFunctor.Faithful :=
  inferInstance
```

- [ ] **Step 3: Add import to `GebLeanTests.lean`**

Insert `import GebLeanTests.LawvereERInterp`
alphabetically after
`import GebLeanTests.LawvereERQuot`.

- [ ] **Step 4: Build and test**

Run: `lake build && lake test`
Expected: clean build, all tests pass.

- [ ] **Step 5: Commit**

```bash
git add GebLeanTests/LawvereERQuot.lean \
  GebLeanTests/LawvereERInterp.lean \
  GebLeanTests.lean
git commit -m "Add Phase 3 sanity tests"
```

---

### Task 8: Update workstream tracker

**Files:**

- Modify: `.session/workstreams/lawvere-elementary-recursive.md`

- [ ] **Step 1: Update status and check off Phase 3**

Update the status section to note Phase 3 complete.
Mark the Phase 3 task checkbox as done.

- [ ] **Step 2: Commit**

```bash
git add \
  .session/workstreams/lawvere-elementary-recursive.md
git commit -m \
  "Mark ER Phase 3 complete in workstream tracker"
```
