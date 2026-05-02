# Lawvere ER Phase 4c: Finite Products on LawvereERLexCat

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Equip `LawvereERLexCat` with chosen finite
products — a terminal object `(0, ⊤)` and binary products
`(n, p) × (m, q) = (n + m, p ⊓ q)` — and assemble the
`HasChosenFiniteProducts` instance.

**Architecture:** The terminal object has arity `0` and
the constant-`1` predicate.  Binary products conjoin the
two predicates (extended to the larger arity via
projections) using the Phase 4b `boolAnd`.  Projections
and pairing are inherited from the Phase 3 raw operations
`ERMorN.fst`, `ERMorN.snd`, `ERMorN.pair`.  Respect-of-
membership proofs use the fact that for naturals
`a * b = 1 ↔ a = 1 ∧ b = 1` (Mathlib's
`Nat.mul_eq_one`).

**Tech Stack:** Lean 4, Mathlib
(`CategoryTheory.Category.Basic`, `Nat.mul_eq_one`).
Depends on Phases 4a (`LawvereERLex.lean`) and 4b
(`LawvereERBool.lean`).

---

## File Map

| File | Role |
| ---- | ---- |
| Modify: `GebLean/LawvereERLex.lean` | Add import of `LawvereERBool`, `ERBoolPred.and`, terminal and product object constructors, raw and quotient pi1/pi2/pair morphisms, universal-property theorems, `HasChosenFiniteProducts` instance |
| Modify: `GebLeanTests/LawvereERLex.lean` | Add product-structure sanity tests |
| Modify: `.session/workstreams/lawvere-elementary-recursive.md` | Mark Phase 4c complete |

---

## Proof Strategy

Respect-of-membership proofs rely on `Nat.mul_eq_one`:
from `(a.pred.and b.pred).interp ctx = 1`, unfold through
`interp_boolAnd` to get a product, then split via
`Nat.mul_eq_one`.  Conversely, to establish
`(a.pred.and b.pred).interp ctx = 1` from two membership
hypotheses, show both factors are `1` and multiply.

Category laws at the quotient level (`pair_pi1`,
`pair_pi2`, `pair_uniq`) follow the Phase 2 pattern:
unwrap quotients with `Quotient.ind` (or `Quotient.ind₂`
for the two-variable cases), reduce to interpretation
equalities restricted to source-satisfying contexts,
then close with `simp` over the interpretation lemmas.

---

### Task 1: Import `LawvereERBool` and add helper interp lemma

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Add import at top of file**

Edit the top of `GebLean/LawvereERLex.lean`:

```lean
import GebLean.LawvereER
import GebLean.LawvereERBool
import Mathlib.CategoryTheory.Category.Basic
```

- [ ] **Step 2: Build to verify import**

Run: `lake build`
Expected: clean build.

- [ ] **Step 3: Commit**

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Import LawvereERBool in LawvereERLex"
```

---

### Task 2: `ERBoolPred.and` conjunction

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Add `ERBoolPred.and` definition**

Append before `end GebLean` (but before `LexObj` is
used — actually, place right after the `ERBoolPred`
structure definition, before `LexObj`):

Find `LexObj` in `LawvereERLex.lean`.  Insert before
`/-- Object of `LawvereERLexCat`...`:

```lean
/-- Conjunction of two Boolean predicates at arities
`n` and `m`: yields a Boolean predicate at arity
`n + m` that holds when `p` holds on the first `n`
coordinates and `q` holds on the last `m`. -/
def ERBoolPred.and {n m : ℕ}
    (p : ERBoolPred n) (q : ERBoolPred m) :
    ERBoolPred (n + m) where
  pred :=
    ERMor1.comp ERMor1.boolAnd fun i =>
      match i with
      | ⟨0, _⟩ =>
          ERMor1.comp p.pred ERMorN.fst
      | ⟨1, _⟩ =>
          ERMor1.comp q.pred ERMorN.snd
  bool := fun ctx => by
    change ERMor1.boolAnd.interp _ ≤ 1
    rw [ERMor1.interp_boolAnd]
    exact
      (Nat.mul_le_mul
        (p.bool _) (q.bool _)).trans
        (Nat.le_refl 1)
```

The `change ... boolAnd.interp _ ≤ 1` matches the
definition of `.pred` through the `comp` unfolding.
If `change` does not match, try:

```lean
  bool := fun ctx => by
    show ERMor1.boolAnd.interp _ ≤ 1
    rw [ERMor1.interp_boolAnd]
    have h1 : _ ≤ 1 := p.bool _
    have h2 : _ ≤ 1 := q.bool _
    exact (Nat.mul_le_mul h1 h2).trans
      (Nat.le_refl 1)
```

If linter complains about `show`, replace with
`change`.

- [ ] **Step 2: Build**

Run: `lake build`
Expected: clean build.

- [ ] **Step 3: Add interp lemma**

Append after the `ERBoolPred.and` definition:

```lean
/-- Interpretation of `ERBoolPred.and`: product of
the two predicates evaluated on the respective
coordinate slices. -/
@[simp] theorem ERBoolPred.and_interp
    {n m : ℕ} (p : ERBoolPred n)
    (q : ERBoolPred m)
    (ctx : Fin (n + m) → ℕ) :
    (ERBoolPred.and p q).pred.interp ctx =
      p.pred.interp (ERMorN.fst.interp ctx) *
      q.pred.interp (ERMorN.snd.interp ctx) := by
  change ERMor1.boolAnd.interp _ = _
  rw [ERMor1.interp_boolAnd]
  rfl
```

- [ ] **Step 4: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Add ERBoolPred.and conjunction with interp"
```

---

### Task 3: Terminal object and terminal morphism

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Add terminal object**

Append after the `Category LawvereERLexCat` instance
(at the end of file, before `end GebLean`):

```lean
/-- Terminal object of `LawvereERLexCat`: arity `0`
with the constant-`1` predicate. -/
def LexObj.terminal : LexObj where
  arity := 0
  pred :=
    { pred := ERMor1.oneN 0
      bool := fun _ => Nat.le_refl 1 }
```

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Add terminal morphism**

```lean
/-- The raw terminal morphism from any object to
`LexObj.terminal`: underlying tuple is the empty
tuple; membership is trivially preserved because
the target predicate is always `1`. -/
def ERLexMorN.toTerminal (obj : LexObj) :
    ERLexMorN obj LexObj.terminal :=
  ⟨ERMorN.terminal obj.arity, fun _ _ => rfl⟩

/-- The terminal morphism in the quotient category. -/
def ERLexMorNQuo.toTerminal (obj : LexObj) :
    ERLexMorNQuo obj LexObj.terminal :=
  Quotient.mk (erLexMorNSetoid obj LexObj.terminal)
    (ERLexMorN.toTerminal obj)
```

The respect proof `fun _ _ => rfl` works because the
target predicate `ERMor1.oneN 0` always evaluates to
`1`, so `(ERMor1.oneN 0).interp _ = 1` by `rfl`.

- [ ] **Step 4: Build**

Run: `lake build`

- [ ] **Step 5: Prove uniqueness of terminal morphism**

```lean
/-- Uniqueness of the terminal morphism: any quotient
morphism to `LexObj.terminal` equals
`ERLexMorNQuo.toTerminal`. -/
theorem ERLexMorNQuo.toTerminal_uniq
    {obj : LexObj}
    (f : ERLexMorNQuo obj LexObj.terminal) :
    f = ERLexMorNQuo.toTerminal obj :=
  Quotient.ind
    (motive := fun f =>
      f = ERLexMorNQuo.toTerminal obj)
    (fun _ => Quotient.sound
      (s := erLexMorNSetoid obj LexObj.terminal)
      (fun _ _ => funext Fin.elim0))
    f
```

The proof: for any raw representative `f_raw`, we
need to show `f_raw ~ ERLexMorN.toTerminal obj`
under the source-restricted setoid.  Both underlying
tuples are elements of `ERMorN obj.arity 0 = Fin 0 →
ERMor1 obj.arity`, so they are equal as functions
(`funext Fin.elim0`), hence their interpretations
are equal at every context.

- [ ] **Step 6: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Add terminal object and terminal morphism"
```

---

### Task 4: Binary product object

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Add `LexObj.prod`**

Append after the terminal uniqueness theorem:

```lean
/-- Binary product object in `LawvereERLexCat`: the
product of `(n, p)` and `(m, q)` is `(n + m, p ⊓ q)`
where `⊓` is the conjunction of predicates extended
along the projections. -/
def LexObj.prod (a b : LexObj) : LexObj where
  arity := a.arity + b.arity
  pred := ERBoolPred.and a.pred b.pred
```

- [ ] **Step 2: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Add LexObj.prod binary product object"
```

---

### Task 5: Projections `pi1` and `pi2`

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Add raw `pi1`**

Append after `LexObj.prod`:

```lean
/-- First projection from the product `a × b` to `a`.
Underlying tuple: `ERMorN.fst`.  Membership
preservation: from `(a.pred ⊓ b.pred)(ctx) = 1`,
deduce `a.pred(first n of ctx) = 1` via
`Nat.mul_eq_one`. -/
def ERLexMorN.pi1 (a b : LexObj) :
    ERLexMorN (LexObj.prod a b) a :=
  ⟨ERMorN.fst, fun ctx hctx => by
    rw [ERBoolPred.and_interp] at hctx
    exact (Nat.mul_eq_one.mp hctx).1⟩
```

The `hctx` has type
`(ERBoolPred.and a.pred b.pred).pred.interp ctx = 1`.
After `rw [ERBoolPred.and_interp]`, it becomes
`a.pred.pred.interp (ERMorN.fst.interp ctx) *
b.pred.pred.interp (ERMorN.snd.interp ctx) = 1`.
`Nat.mul_eq_one` gives both factors equal `1`; `.1`
projects the first.

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Add raw `pi2`**

```lean
/-- Second projection from the product `a × b` to
`b`. -/
def ERLexMorN.pi2 (a b : LexObj) :
    ERLexMorN (LexObj.prod a b) b :=
  ⟨ERMorN.snd, fun ctx hctx => by
    rw [ERBoolPred.and_interp] at hctx
    exact (Nat.mul_eq_one.mp hctx).2⟩
```

- [ ] **Step 4: Build**

Run: `lake build`

- [ ] **Step 5: Add quotient versions**

```lean
/-- First projection in the quotient category. -/
def ERLexMorNQuo.pi1 (a b : LexObj) :
    ERLexMorNQuo (LexObj.prod a b) a :=
  Quotient.mk (erLexMorNSetoid (LexObj.prod a b) a)
    (ERLexMorN.pi1 a b)

/-- Second projection in the quotient category. -/
def ERLexMorNQuo.pi2 (a b : LexObj) :
    ERLexMorNQuo (LexObj.prod a b) b :=
  Quotient.mk (erLexMorNSetoid (LexObj.prod a b) b)
    (ERLexMorN.pi2 a b)
```

- [ ] **Step 6: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Add raw and quotient projections pi1, pi2"
```

---

### Task 6: Pairing `pair`

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Add raw `pair`**

Append after the projections:

```lean
/-- Pairing in `LawvereERLexCat`: given `f : z → a`
and `g : z → b`, produces the universal arrow
`z → a × b`.  Underlying tuple: `ERMorN.pair f.val
g.val`.  Membership preservation: when `z.pred(ctx)
= 1`, both `a.pred(f.val.interp ctx) = 1` and
`b.pred(g.val.interp ctx) = 1`, so their product is
`1`. -/
def ERLexMorN.pair {z a b : LexObj}
    (f : ERLexMorN z a) (g : ERLexMorN z b) :
    ERLexMorN z (LexObj.prod a b) :=
  ⟨ERMorN.pair f.val g.val, fun ctx hctx => by
    rw [ERBoolPred.and_interp]
    have hf : a.pred.pred.interp
        (ERMorN.fst.interp
          ((ERMorN.pair f.val g.val).interp ctx)) =
        1 := by
      have step : ERMorN.fst.interp
          ((ERMorN.pair f.val g.val).interp ctx) =
          f.val.interp ctx := by
        funext i
        rw [ERMorN.interp_fst,
            ERMorN.interp_pair]
        have : i.val < a.arity := i.isLt
        rw [dif_pos this]
      rw [step]
      exact f.property ctx hctx
    have hg : b.pred.pred.interp
        (ERMorN.snd.interp
          ((ERMorN.pair f.val g.val).interp ctx)) =
        1 := by
      have step : ERMorN.snd.interp
          ((ERMorN.pair f.val g.val).interp ctx) =
          g.val.interp ctx := by
        funext i
        rw [ERMorN.interp_snd,
            ERMorN.interp_pair]
        have : ¬ (a.arity + i.val) < a.arity := by
          omega
        rw [dif_neg this]
        congr 1
        exact Fin.ext (by omega)
      rw [step]
      exact g.property ctx hctx
    rw [hf, hg]
    exact Nat.one_mul 1⟩
```

The proof is substantive: we need to show that
selecting the first `a.arity` coordinates of
`ERMorN.pair f.val g.val` interpreted at `ctx`
yields `f.val.interp ctx`, and similarly for the
second `b.arity` coordinates yielding
`g.val.interp ctx`.  Then by the respect proofs of
`f` and `g`, both parts are `1`.

If any of the `funext`/`rw` steps fail, the
implementer should work through the goal step by
step, using the `@[simp]` lemmas `ERMorN.interp_fst`,
`ERMorN.interp_snd`, `ERMorN.interp_pair`.

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Add quotient `pair` via Quotient.lift₂**

```lean
/-- Pairing of quotient morphisms, lifted from
`ERLexMorN.pair` via `Quotient.lift₂`.
Well-definedness follows from source-restricted
extensional equality of components. -/
def ERLexMorNQuo.pair {z a b : LexObj}
    (f : ERLexMorNQuo z a)
    (g : ERLexMorNQuo z b) :
    ERLexMorNQuo z (LexObj.prod a b) :=
  Quotient.lift₂
    (s₁ := erLexMorNSetoid z a)
    (s₂ := erLexMorNSetoid z b)
    (fun f' g' =>
      Quotient.mk
        (erLexMorNSetoid z (LexObj.prod a b))
        (ERLexMorN.pair f' g'))
    (fun fa fb ga gb hf hg =>
      Quotient.sound
        (s := erLexMorNSetoid z (LexObj.prod a b))
        (fun ctx hctx => by
          change (ERMorN.pair fa.val fb.val).interp
            ctx = (ERMorN.pair ga.val gb.val).interp
            ctx
          funext i
          rw [ERMorN.interp_pair,
              ERMorN.interp_pair]
          split_ifs with h
          · exact congrFun (hf ctx hctx)
              ⟨i.val, h⟩
          · exact congrFun (hg ctx hctx)
              ⟨i.val - a.arity, by omega⟩))
    f g
```

- [ ] **Step 4: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Add raw and quotient pairing for LawvereERLex"
```

---

### Task 7: Product universal property (pair ∘ pi1, pair ∘ pi2)

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Prove `pair_pi1`**

Append after the pairing definition:

```lean
/-- Composing pairing with the first projection
recovers the first component. -/
theorem ERLexMorNQuo.pair_pi1 {z a b : LexObj}
    (f : ERLexMorNQuo z a)
    (g : ERLexMorNQuo z b) :
    ERLexMorNQuo.comp (ERLexMorNQuo.pair f g)
      (ERLexMorNQuo.pi1 a b) = f :=
  Quotient.ind₂
    (motive := fun f g =>
      ERLexMorNQuo.comp (ERLexMorNQuo.pair f g)
        (ERLexMorNQuo.pi1 a b) = f)
    (fun f_raw g_raw =>
      Quotient.sound
        (s := erLexMorNSetoid z a)
        (fun ctx _ => by
          change (ERMorN.comp
              (ERMorN.pair f_raw.val g_raw.val)
              ERMorN.fst).interp ctx =
              f_raw.val.interp ctx
          funext i
          simp only [ERMorN.interp_comp,
            ERMorN.interp_fst,
            ERMorN.interp_pair]
          rw [dif_pos i.isLt]))
    f g
```

The proof: after unwrapping quotients and simplifying
interp of the composite, each component selects
from the paired tuple at an index `< a.arity`, which
hits the `f` branch of the `dite`.

If `rw [dif_pos i.isLt]` does not close, the step can
be split:

```lean
          simp only [ERMorN.interp_comp,
            ERMorN.interp_fst,
            ERMorN.interp_pair]
          have h : (⟨i.val, by omega⟩ : Fin
              (a.arity + b.arity)).val < a.arity :=
            i.isLt
          rw [dif_pos h]
```

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Prove `pair_pi2`**

```lean
/-- Composing pairing with the second projection
recovers the second component. -/
theorem ERLexMorNQuo.pair_pi2 {z a b : LexObj}
    (f : ERLexMorNQuo z a)
    (g : ERLexMorNQuo z b) :
    ERLexMorNQuo.comp (ERLexMorNQuo.pair f g)
      (ERLexMorNQuo.pi2 a b) = g :=
  Quotient.ind₂
    (motive := fun f g =>
      ERLexMorNQuo.comp (ERLexMorNQuo.pair f g)
        (ERLexMorNQuo.pi2 a b) = g)
    (fun f_raw g_raw =>
      Quotient.sound
        (s := erLexMorNSetoid z b)
        (fun ctx _ => by
          change (ERMorN.comp
              (ERMorN.pair f_raw.val g_raw.val)
              ERMorN.snd).interp ctx =
              g_raw.val.interp ctx
          funext i
          simp only [ERMorN.interp_comp,
            ERMorN.interp_snd,
            ERMorN.interp_pair]
          have h : ¬ (a.arity + i.val) < a.arity :=
            by omega
          rw [dif_neg h]
          congr 1
          exact Fin.ext (by omega)))
    f g
```

The second projection selects indices `≥ a.arity`,
hitting the `g` branch.  The `congr 1; Fin.ext` step
aligns the index `⟨a.arity + i.val - a.arity, ...⟩`
with `i : Fin b.arity`.

- [ ] **Step 4: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Prove pair_pi1 and pair_pi2"
```

---

### Task 8: Pairing uniqueness

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Prove `pair_uniq`**

Append after `pair_pi2`:

```lean
/-- Uniqueness of pairing: any morphism `h : z →
a × b` whose compositions with the projections yield
`f` and `g` equals `pair f g`. -/
theorem ERLexMorNQuo.pair_uniq {z a b : LexObj}
    (f : ERLexMorNQuo z a)
    (g : ERLexMorNQuo z b)
    (h : ERLexMorNQuo z (LexObj.prod a b))
    (hf : ERLexMorNQuo.comp h
      (ERLexMorNQuo.pi1 a b) = f)
    (hg : ERLexMorNQuo.comp h
      (ERLexMorNQuo.pi2 a b) = g) :
    h = ERLexMorNQuo.pair f g :=
  Quotient.ind
    (motive := fun h =>
      ∀ (f : ERLexMorNQuo z a)
        (g : ERLexMorNQuo z b),
        ERLexMorNQuo.comp h
          (ERLexMorNQuo.pi1 a b) = f →
        ERLexMorNQuo.comp h
          (ERLexMorNQuo.pi2 a b) = g →
        h = ERLexMorNQuo.pair f g)
    (fun h_raw =>
      Quotient.ind
        (motive := fun f =>
          ∀ (g : ERLexMorNQuo z b),
            ERLexMorNQuo.comp
              (Quotient.mk _ h_raw)
              (ERLexMorNQuo.pi1 a b) = f →
            ERLexMorNQuo.comp
              (Quotient.mk _ h_raw)
              (ERLexMorNQuo.pi2 a b) = g →
            Quotient.mk _ h_raw =
              ERLexMorNQuo.pair f g)
        (fun f_raw =>
          Quotient.ind
            (motive := fun g =>
              ERLexMorNQuo.comp
                (Quotient.mk _ h_raw)
                (ERLexMorNQuo.pi1 a b) =
                Quotient.mk _ f_raw →
              ERLexMorNQuo.comp
                (Quotient.mk _ h_raw)
                (ERLexMorNQuo.pi2 a b) = g →
              Quotient.mk _ h_raw =
                ERLexMorNQuo.pair
                  (Quotient.mk _ f_raw) g)
            (fun g_raw hf_eq hg_eq => by
              have hf_rel :=
                Quotient.exact
                  (s := erLexMorNSetoid z a)
                  hf_eq
              have hg_rel :=
                Quotient.exact
                  (s := erLexMorNSetoid z b)
                  hg_eq
              apply Quotient.sound
                (s := erLexMorNSetoid z
                  (LexObj.prod a b))
              intro ctx hctx
              funext i
              rw [ERMorN.interp_pair]
              split_ifs with h
              · have := congrFun
                  (hf_rel ctx hctx)
                  ⟨i.val, h⟩
                simp only [ERMorN.interp_comp,
                  ERMorN.interp_fst] at this
                exact this
              · have := congrFun
                  (hg_rel ctx hctx)
                  ⟨i.val - a.arity, by omega⟩
                simp only [ERMorN.interp_comp,
                  ERMorN.interp_snd] at this
                convert this using 2
                exact Fin.ext (by omega)))
    h f g hf hg
```

This is the longest proof in Phase 4c.  Strategy:
triple `Quotient.ind` to unwrap all three variables
(h, f, g), extract setoid relations via
`Quotient.exact`, then show pointwise agreement on
source-satisfying contexts by splitting on the
pairing index.  In the `< a.arity` branch, use the
hypothesis coming from `pi1`; in the other branch,
use the `pi2` hypothesis with `Fin.ext` to align
indices.

If this proof does not compile exactly, the
implementer should adapt the `simp`/`convert` calls
using `_` to inspect goals.

- [ ] **Step 2: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Prove ERLexMorNQuo.pair_uniq"
```

---

### Task 9: HasChosenFiniteProducts instance

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Add import for ComputableLimits and instance**

First add to the top of the file (if not already
imported):

```lean
import GebLean.Utilities.ComputableLimits
```

Then append at the end (before `end GebLean`):

```lean
/-- Chosen binary product structure for
`LawvereERLexCat`: the product of `a` and `b` is
`LexObj.prod a b`. -/
def lawvereERLexProduct
    (a b : LawvereERLexCat) :
    ChosenBinaryProduct a b where
  obj := LexObj.prod a b
  fst := ERLexMorNQuo.pi1 a b
  snd := ERLexMorNQuo.pi2 a b
  lift f g := ERLexMorNQuo.pair f g
  lift_fst := ERLexMorNQuo.pair_pi1
  lift_snd := ERLexMorNQuo.pair_pi2
  lift_uniq f g h hf hs :=
    ERLexMorNQuo.pair_uniq f g h hf hs

/-- Chosen terminal object for `LawvereERLexCat`. -/
def lawvereERLexTerminal :
    ChosenTerminal LawvereERLexCat where
  obj := LexObj.terminal
  from_ obj := ERLexMorNQuo.toTerminal obj
  uniq f := ERLexMorNQuo.toTerminal_uniq f

/-- `LawvereERLexCat` has chosen finite products. -/
instance : HasChosenFiniteProducts
    LawvereERLexCat where
  terminal := lawvereERLexTerminal
  product := lawvereERLexProduct
```

- [ ] **Step 2: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Add HasChosenFiniteProducts for LawvereERLexCat"
```

---

### Task 10: Tests and workstream tracker

**Files:**

- Modify: `GebLeanTests/LawvereERLex.lean`
- Modify: `.session/workstreams/lawvere-elementary-recursive.md`

- [ ] **Step 1: Add product-structure tests**

Append to `GebLeanTests/LawvereERLex.lean`:

```lean
-- Terminal uniqueness: any morphism to terminal
-- equals the terminal morphism.
example (obj : LexObj)
    (f : obj ⟶ (LexObj.terminal :
        LawvereERLexCat)) :
    f = ERLexMorNQuo.toTerminal obj :=
  ERLexMorNQuo.toTerminal_uniq f

-- HasChosenFiniteProducts is available for
-- LawvereERLexCat.
example : HasChosenFiniteProducts LawvereERLexCat :=
  inferInstance

-- Product of the trivial object with itself has
-- arity 0.
example : (LexObj.prod LexObj.terminal
    LexObj.terminal).arity = 0 := rfl
```

- [ ] **Step 2: Build and test**

Run: `lake build && lake test`
Expected: clean build, all tests pass.

- [ ] **Step 3: Commit tests**

```bash
git add GebLeanTests/LawvereERLex.lean
git commit -m "Add Phase 4c product-structure tests"
```

- [ ] **Step 4: Update workstream tracker**

Edit the status section in
`.session/workstreams/lawvere-elementary-recursive.md`
to note Phase 4c complete.  Add after the Phase 4b
description:

"Phase 4c complete: see `GebLean/LawvereERLex.lean`
extended with `ERBoolPred.and`, `LexObj.terminal`,
`LexObj.prod`, projections `pi1`/`pi2`, pairing,
universal-property theorems, and the
`HasChosenFiniteProducts LawvereERLexCat` instance."

Also update the task checkbox:

```
  * [ ] 4c: Finite products.
```

to:

```
  * [x] 4c: Finite products.
```

- [ ] **Step 5: Commit tracker update**

```bash
git add \
  .session/workstreams/lawvere-elementary-recursive.md
git commit -m \
  "Mark ER Phase 4c complete in workstream tracker"
```
