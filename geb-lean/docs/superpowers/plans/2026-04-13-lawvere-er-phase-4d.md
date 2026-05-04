# Lawvere ER Phase 4d: Equalizers on LawvereERLexCat

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Construct equalizers for parallel morphisms in
`LawvereERLexCat`.  For raw representatives `f, g :
ERLexMorN a b`, build an equalizer object
`LexObj.equalizer f g : LexObj`, an inclusion morphism
`E → a`, and prove it satisfies the universal property at
the quotient-morphism level.

**Architecture:** The equalizer of `f, g : (n, p) →
(m, q)` is `(n, p ⊓ allEq f g)` where `allEq` is a
recursive componentwise equality predicate built from
`boolEqNat` and `boolAnd`.  The equalizer morphism has
the identity tuple; its respect proof uses the equalizer
predicate to witness both source membership and
componentwise equality.

**Tech Stack:** Lean 4, Mathlib; depends on Phases 4a, 4b,
4c.

**Scope note:** This plan does NOT build a
`HasChosenEqualizers` or `HasFiniteLimits` instance.  The
equalizer construction is parameterized by raw
`ERLexMorN` representatives (not quotient classes),
because different representatives yield different
syntactic objects.  The universal property is
nevertheless stated and proved at the quotient level.  A
chosen-equalizers instance (requiring representative
choice) and `HasFiniteLimits` can be added in a
subsequent plan.

---

## File Map

| File | Role |
| ---- | ---- |
| Modify: `GebLean/LawvereERLex.lean` | Add `ERBoolPred.alwaysTrueN`, `ERBoolPred.andSameArity`, `ERBoolPred.allEq`, `LexObj.equalizer`, equalizer morphism, equalization theorem, lift construction and universal property theorems |
| Modify: `GebLean/LawvereERBool.lean` | Add `ERMor1.boolEqAt` helper (Boolean equality of two ERMor1 terms at the same arity) |
| Modify: `GebLeanTests/LawvereERLex.lean` | Add equalizer sanity tests |
| Modify: `.session/workstreams/lawvere-elementary-recursive.md` | Mark Phase 4d complete |

---

## Proof Strategy

`allEq f g` is defined by structural recursion on `m`:
empty when `m = 0`, otherwise `boolEqNat(f 0, g 0) AND
allEq(tail f, tail g)`.  Its interpretation lemma states
`(allEq f g).pred.interp ctx = 1 ↔ f.interp ctx = g.interp
ctx`.

The equalizer predicate combines the source's `a.pred`
with `allEq f g` via `andSameArity`.  Membership in the
equalizer therefore witnesses both `a.pred = 1` and
componentwise agreement of `f` and `g`.

For the universal property:
- **Equalization**: `equalizerMap ≫ [f] = equalizerMap ≫ [g]` follows from unfolding and noting that on
  `E.pred`-satisfying contexts, both sides equal `f.interp
  (ctx) = g.interp (ctx)`.
- **Lift**: given `h : z → a` with `[h] ≫ [f] = [h] ≫ [g]`,
  set `h'.val = h.val`; the respect proof chains `a.pred`
  (from `h.property`) with the equalization hypothesis
  (applied via `Quotient.exact` + `interp_comp`).
- **Uniqueness**: `equalizerMap` has underlying identity,
  so `h₁' ≫ equalizerMap` unfolds to `h₁'.val` itself,
  and the hypothesis gives pointwise equality on
  `z.pred`-satisfying contexts, closing via
  `Quotient.sound`.

---

### Task 1: `ERBoolPred.alwaysTrueN` and `ERBoolPred.andSameArity`

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Add `ERBoolPred.alwaysTrueN`**

Append before `LexObj` (near `ERBoolPred.and`):

```lean
/-- The always-true predicate at arity `n`: the
constant `1` function, trivially Boolean-valued. -/
def ERBoolPred.alwaysTrueN (n : ℕ) :
    ERBoolPred n where
  pred := ERMor1.oneN n
  bool := fun _ => Nat.le_refl 1

/-- Interpretation of `alwaysTrueN`: always `1`. -/
@[simp] theorem ERBoolPred.alwaysTrueN_interp
    (n : ℕ) (ctx : Fin n → ℕ) :
    (ERBoolPred.alwaysTrueN n).pred.interp ctx =
      1 :=
  rfl
```

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Add `ERBoolPred.andSameArity`**

```lean
/-- Conjunction of two Boolean predicates at the
same arity: composes `boolAnd` with the two
predicates as its inputs. -/
def ERBoolPred.andSameArity {n : ℕ}
    (p q : ERBoolPred n) : ERBoolPred n where
  pred :=
    ERMor1.comp ERMor1.boolAnd fun i =>
      match i with
      | ⟨0, _⟩ => p.pred
      | ⟨1, _⟩ => q.pred
  bool := fun ctx => by
    change ERMor1.boolAnd.interp _ ≤ 1
    rw [ERMor1.interp_boolAnd]
    exact
      (Nat.mul_le_mul
        (p.bool _) (q.bool _)).trans
        (Nat.le_refl 1)

/-- Interpretation of `andSameArity`: product of
the two predicate interpretations. -/
@[simp] theorem ERBoolPred.andSameArity_interp
    {n : ℕ} (p q : ERBoolPred n)
    (ctx : Fin n → ℕ) :
    (ERBoolPred.andSameArity p q).pred.interp
        ctx =
      p.pred.interp ctx * q.pred.interp ctx := by
  change ERMor1.boolAnd.interp _ = _
  rw [ERMor1.interp_boolAnd]
  rfl
```

- [ ] **Step 4: Refactor `LexObj.terminal` and
  `lawvereERLexTerminal` bool proofs to use
  `alwaysTrueN`**

Replace the inline predicate in `LexObj.terminal`:

```lean
def LexObj.terminal : LexObj where
  arity := 0
  pred := ERBoolPred.alwaysTrueN 0
```

- [ ] **Step 5: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Add alwaysTrueN and andSameArity helpers"
```

---

### Task 2: `ERMor1.boolEqAt` helper

**Files:**

- Modify: `GebLean/LawvereERBool.lean`

- [ ] **Step 1: Add `boolEqAt` definition and interp
  lemma**

Append before `end GebLean`:

```lean
/-- Boolean equality of two arity-`n` ER terms:
returns `1` iff `x.interp ctx = y.interp ctx`.
Definable as `boolEqNat` composed with the pair
`(x, y)`. -/
def ERMor1.boolEqAt {n : ℕ} (x y : ERMor1 n) :
    ERMor1 n :=
  ERMor1.comp ERMor1.boolEqNat fun i =>
    match i with
    | ⟨0, _⟩ => x
    | ⟨1, _⟩ => y

/-- Interpretation of `boolEqAt`: the Boolean
equality of the two interpretations. -/
@[simp] theorem ERMor1.interp_boolEqAt
    {n : ℕ} (x y : ERMor1 n)
    (ctx : Fin n → ℕ) :
    (ERMor1.boolEqAt x y).interp ctx =
      (1 - (x.interp ctx - y.interp ctx)) *
      (1 - (y.interp ctx - x.interp ctx)) := by
  change ERMor1.boolEqNat.interp _ = _
  rw [ERMor1.interp_boolEqNat]
  rfl

/-- `boolEqAt` always returns a Boolean value. -/
theorem ERMor1.boolEqAt_le_one {n : ℕ}
    (x y : ERMor1 n) (ctx : Fin n → ℕ) :
    (ERMor1.boolEqAt x y).interp ctx ≤ 1 := by
  change ERMor1.boolEqNat.interp _ ≤ 1
  exact ERMor1.boolEqNat_le_one _

/-- `boolEqAt x y = 1` iff `x.interp ctx =
y.interp ctx`. -/
theorem ERMor1.boolEqAt_eq_one_iff {n : ℕ}
    (x y : ERMor1 n) (ctx : Fin n → ℕ) :
    (ERMor1.boolEqAt x y).interp ctx = 1 ↔
      x.interp ctx = y.interp ctx := by
  rw [ERMor1.interp_boolEqAt]
  constructor
  · intro h
    -- (1 - d) * (1 - d') = 1 implies d = d' = 0
    -- where d = x.interp - y.interp,
    -- d' = y.interp - x.interp
    have h1 : 1 - (x.interp ctx - y.interp ctx) ≤
        1 := Nat.sub_le _ _
    have h2 : 1 - (y.interp ctx - x.interp ctx) ≤
        1 := Nat.sub_le _ _
    have hxy : x.interp ctx - y.interp ctx = 0 := by
      rcases Nat.eq_or_lt_of_le h1 with heq | hlt
      · -- first factor is 1, so subtraction is 0
        omega
      · -- first factor is 0, product is 0 ≠ 1
        omega
    have hyx : y.interp ctx - x.interp ctx = 0 := by
      rcases Nat.eq_or_lt_of_le h2 with heq | hlt
      · omega
      · omega
    omega
  · intro h
    rw [h]
    simp
```

The `boolEqAt_eq_one_iff` proof may need refinement
— if the `rcases` + `omega` approach does not
work, try:

```lean
  · intro h
    by_contra hneq
    -- x ≠ y means one of the subs is positive
    rcases Nat.lt_or_gt_of_ne hneq with h1 | h1
    · have hsub : y.interp ctx - x.interp ctx ≥ 1 :=
        Nat.sub_pos_of_lt h1
      have : 1 - (y.interp ctx - x.interp ctx) = 0 :=
        by omega
      rw [this] at h
      simp at h
    · have hsub : x.interp ctx - y.interp ctx ≥ 1 :=
        Nat.sub_pos_of_lt h1
      have : 1 - (x.interp ctx - y.interp ctx) = 0 :=
        by omega
      rw [this] at h
      simp at h
```

- [ ] **Step 2: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERBool.lean
git commit -m "Add ERMor1.boolEqAt helper with interp and closure"
```

---

### Task 3: `ERBoolPred.allEq`

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Add `allEq` recursive definition**

Append after `andSameArity` (before `LexObj`):

```lean
/-- Componentwise Boolean equality of two `ERMorN`
tuples at arity `n`: returns a Boolean predicate
at arity `n` that holds iff the two tuples have
equal interpretations. -/
def ERBoolPred.allEq {n : ℕ} :
    ∀ {m : ℕ}, ERMorN n m → ERMorN n m →
      ERBoolPred n
  | 0, _, _ => ERBoolPred.alwaysTrueN n
  | _ + 1, f, g =>
      ERBoolPred.andSameArity
        { pred := ERMor1.boolEqAt (f 0) (g 0)
          bool := ERMor1.boolEqAt_le_one _ _ }
        (ERBoolPred.allEq
          (fun i => f i.succ)
          (fun i => g i.succ))
```

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Add forward and backward interp
  characterizations**

```lean
/-- `allEq f g .interp ctx = 1` implies `f.interp
ctx = g.interp ctx` as functions. -/
theorem ERBoolPred.allEq_eq_one_imp
    {n : ℕ} : ∀ {m : ℕ} (f g : ERMorN n m)
      (ctx : Fin n → ℕ),
      (ERBoolPred.allEq f g).pred.interp ctx = 1 →
        f.interp ctx = g.interp ctx
  | 0, _, _, _, _ => by
      funext i; exact i.elim0
  | _ + 1, f, g, ctx, h => by
      simp only [ERBoolPred.allEq,
        ERBoolPred.andSameArity_interp] at h
      have h01 : (ERMor1.boolEqAt (f 0)
          (g 0)).interp ctx ≤ 1 :=
        ERMor1.boolEqAt_le_one _ _ _
      have htail_le : (ERBoolPred.allEq
          (fun i => f i.succ)
          (fun i => g i.succ)).pred.interp ctx ≤
          1 :=
        _ -- via allEq_le_one below
      sorry -- replace with full proof
```

Note: the proof above references `allEq_le_one`
which we should prove separately.  The final form
should use `Nat.mul_eq_one` to split the
conjunction's product form, then derive agreement
on index 0 via `boolEqAt_eq_one_iff` and on
remaining indices via the inductive hypothesis.

Given complexity, implement with cleaner structure:

```lean
/-- Boolean closure: `allEq f g` is always Boolean. -/
theorem ERBoolPred.allEq_le_one {n : ℕ} :
    ∀ {m : ℕ} (f g : ERMorN n m)
      (ctx : Fin n → ℕ),
      (ERBoolPred.allEq f g).pred.interp ctx ≤ 1
  | 0, _, _, _ => by simp [ERBoolPred.allEq]
  | _ + 1, f, g, ctx => by
      simp only [ERBoolPred.allEq,
        ERBoolPred.andSameArity_interp]
      have h1 : (ERMor1.boolEqAt (f 0)
          (g 0)).interp ctx ≤ 1 :=
        ERMor1.boolEqAt_le_one _ _ _
      have h2 : (ERBoolPred.allEq
          (fun i => f i.succ)
          (fun i => g i.succ)).pred.interp ctx ≤ 1 :=
        ERBoolPred.allEq_le_one _ _ _
      calc (ERMor1.boolEqAt (f 0) (g 0)).interp
             ctx *
           (ERBoolPred.allEq
               (fun i => f i.succ)
               (fun i => g i.succ)).pred.interp ctx
          _ ≤ 1 * _ := Nat.mul_le_mul_right _ h1
          _ ≤ 1 * 1 := Nat.mul_le_mul_left _ h2
          _ = 1 := Nat.one_mul 1

/-- Forward direction: if `allEq f g` evaluates to
`1` on a context, then `f` and `g` interpret to the
same function at that context. -/
theorem ERBoolPred.allEq_eq_one_imp
    {n : ℕ} : ∀ {m : ℕ} (f g : ERMorN n m)
      (ctx : Fin n → ℕ),
      (ERBoolPred.allEq f g).pred.interp ctx = 1 →
        f.interp ctx = g.interp ctx
  | 0, _, _, _, _ => funext (fun i => i.elim0)
  | _ + 1, f, g, ctx, h => by
      simp only [ERBoolPred.allEq,
        ERBoolPred.andSameArity_interp] at h
      have h_split := mul_eq_one.mp h
      have h_head := h_split.1
      have h_tail := h_split.2
      have eq_head :
          (f 0).interp ctx = (g 0).interp ctx :=
        (ERMor1.boolEqAt_eq_one_iff _ _ _).mp h_head
      have eq_tail :
          (fun i => f i.succ).interp ctx =
          (fun i => g i.succ).interp ctx :=
        ERBoolPred.allEq_eq_one_imp _ _ _ h_tail
      funext i
      induction i using Fin.cases with
      | zero => exact eq_head
      | succ j =>
        have := congrFun eq_tail j
        exact this

/-- Backward direction: if `f` and `g` interpret to
the same function at a context, then `allEq f g`
evaluates to `1` there. -/
theorem ERBoolPred.allEq_of_eq
    {n : ℕ} : ∀ {m : ℕ} (f g : ERMorN n m)
      (ctx : Fin n → ℕ),
      f.interp ctx = g.interp ctx →
        (ERBoolPred.allEq f g).pred.interp ctx = 1
  | 0, _, _, _, _ => by simp [ERBoolPred.allEq]
  | _ + 1, f, g, ctx, h => by
      simp only [ERBoolPred.allEq,
        ERBoolPred.andSameArity_interp]
      have eq0 : (f 0).interp ctx = (g 0).interp
          ctx := congrFun h 0
      have eq_tail : (fun i => f i.succ).interp
          ctx = (fun i => g i.succ).interp ctx := by
        funext j
        exact congrFun h j.succ
      rw [(ERMor1.boolEqAt_eq_one_iff _ _ _).mpr
          eq0]
      rw [ERBoolPred.allEq_of_eq _ _ _ eq_tail]
      rfl
```

- [ ] **Step 4: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Add ERBoolPred.allEq with forward/backward characterizations"
```

---

### Task 4: Equalizer object and morphism (raw)

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Add `LexObj.equalizer` and
  `ERLexMorN.equalizerMap`**

Append after `pair_uniq` (before `lawvereERLexProduct`):

```lean
/-- Equalizer object for parallel morphisms
`f, g : a → b` (at the raw `ERLexMorN` level):
the same arity as `a`, with predicate augmented
by componentwise equality of `f` and `g`. -/
def LexObj.equalizer {a b : LexObj}
    (f g : ERLexMorN a b) : LexObj where
  arity := a.arity
  pred :=
    ERBoolPred.andSameArity a.pred
      (ERBoolPred.allEq f.val g.val)

/-- The equalizer inclusion morphism: underlying
tuple is the identity, with respect proof
extracting `a.pred = 1` from the equalizer
predicate. -/
def ERLexMorN.equalizerMap {a b : LexObj}
    (f g : ERLexMorN a b) :
    ERLexMorN (LexObj.equalizer f g) a :=
  ⟨ERMorN.id a.arity, fun ctx hctx => by
    change (ERBoolPred.andSameArity a.pred
        (ERBoolPred.allEq f.val g.val)).pred.interp
        ctx = 1 at hctx
    rw [ERBoolPred.andSameArity_interp] at hctx
    rw [ERMorN.interp_id]
    exact (mul_eq_one.mp hctx).1⟩
```

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Add quotient-level equalizer
  morphism**

```lean
/-- The equalizer inclusion morphism in the
quotient category. -/
def ERLexMorNQuo.equalizerMap {a b : LexObj}
    (f g : ERLexMorN a b) :
    ERLexMorNQuo (LexObj.equalizer f g) a :=
  Quotient.mk
    (erLexMorNSetoid (LexObj.equalizer f g) a)
    (ERLexMorN.equalizerMap f g)
```

- [ ] **Step 4: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Add LexObj.equalizer and ERLexMorN.equalizerMap"
```

---

### Task 5: Equalization theorem

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Prove the quotient-level
  equalization theorem**

Append after the equalizer morphism definitions:

```lean
/-- The equalizer morphism equalizes `f` and `g`
at the quotient level: composing
`equalizerMap f g` with `[f]` equals composing with
`[g]`. -/
theorem ERLexMorNQuo.equalizerMap_eq
    {a b : LexObj} (f g : ERLexMorN a b) :
    ERLexMorNQuo.comp
      (ERLexMorNQuo.equalizerMap f g)
      (Quotient.mk (erLexMorNSetoid a b) f) =
    ERLexMorNQuo.comp
      (ERLexMorNQuo.equalizerMap f g)
      (Quotient.mk (erLexMorNSetoid a b) g) :=
  Quotient.sound
    (s := erLexMorNSetoid
      (LexObj.equalizer f g) b)
    (fun ctx hctx => by
      change (ERLexMorN.comp
          (ERLexMorN.equalizerMap f g) f).val.interp
          ctx =
        (ERLexMorN.comp
          (ERLexMorN.equalizerMap f g) g).val.interp
          ctx
      simp only [ERLexMorN.comp,
        ERLexMorN.equalizerMap,
        ERMorN.interp_comp,
        ERMorN.interp_id]
      change (ERBoolPred.andSameArity a.pred
          (ERBoolPred.allEq f.val g.val)).pred.interp
          ctx = 1 at hctx
      rw [ERBoolPred.andSameArity_interp] at hctx
      have h_allEq :=
        (mul_eq_one.mp hctx).2
      exact ERBoolPred.allEq_eq_one_imp
        f.val g.val ctx h_allEq)
```

- [ ] **Step 2: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Prove equalizer morphism equalizes parallel morphisms"
```

---

### Task 6: Lift construction (raw)

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Add the raw lift**

Append after the equalization theorem:

```lean
/-- Lift of an equalizing morphism through the
equalizer (raw level).  Given `h : z → a` whose
compositions with `f` and `g` agree on
source-satisfying contexts, produces the morphism
into the equalizer with the same underlying
tuple. -/
def ERLexMorN.equalizerLift {z a b : LexObj}
    {f g : ERLexMorN a b} (h : ERLexMorN z a)
    (heq : ∀ ctx : Fin z.arity → ℕ,
      z.pred.pred.interp ctx = 1 →
      f.val.interp (h.val.interp ctx) =
        g.val.interp (h.val.interp ctx)) :
    ERLexMorN z (LexObj.equalizer f g) :=
  ⟨h.val, fun ctx hctx => by
    change (ERBoolPred.andSameArity a.pred
        (ERBoolPred.allEq f.val g.val)).pred.interp
        _ = 1
    rw [ERBoolPred.andSameArity_interp]
    have h1 : a.pred.pred.interp (h.val.interp
        ctx) = 1 := h.property ctx hctx
    have h2 : (ERBoolPred.allEq f.val
        g.val).pred.interp (h.val.interp ctx) = 1 :=
      ERBoolPred.allEq_of_eq _ _ _ (heq ctx hctx)
    rw [h1, h2]
    rfl⟩
```

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Add the quotient lift**

```lean
/-- Quotient-level lift.  Takes a quotient
equalizing morphism `[h]` and produces the
quotient-lifted morphism into the equalizer. -/
def ERLexMorNQuo.equalizerLift {z a b : LexObj}
    {f g : ERLexMorN a b} (h : ERLexMorNQuo z a)
    (heq :
      ERLexMorNQuo.comp h
        (Quotient.mk (erLexMorNSetoid a b) f) =
      ERLexMorNQuo.comp h
        (Quotient.mk (erLexMorNSetoid a b) g)) :
    ERLexMorNQuo z (LexObj.equalizer f g) :=
  Quotient.hrecOn
    (motive := fun h =>
      (heq :
        ERLexMorNQuo.comp h
          (Quotient.mk (erLexMorNSetoid a b) f) =
        ERLexMorNQuo.comp h
          (Quotient.mk (erLexMorNSetoid a b) g)) →
      ERLexMorNQuo z (LexObj.equalizer f g))
    h
    (fun h_raw heq_raw =>
      Quotient.mk
        (erLexMorNSetoid z
          (LexObj.equalizer f g))
        (ERLexMorN.equalizerLift h_raw
          (fun ctx hctx => by
            have := Quotient.exact
              (s := erLexMorNSetoid z b) heq_raw
            have step := this ctx hctx
            simp only [ERLexMorN.comp,
              ERMorN.interp_comp] at step
            exact step)))
    (by
      intros ha hb hab
      funext heq'
      -- Well-definedness: different raw reps
      -- give setoid-equal lifts
      apply Quotient.sound
        (s := erLexMorNSetoid z
          (LexObj.equalizer f g))
      intro ctx hctx
      exact hab ctx hctx)
    heq
```

Note: `Quotient.hrecOn` may not be the cleanest
approach here.  If the above is too complex,
simplify by proving well-definedness outside as a
separate lemma and use `Quotient.liftOn` with a
proof that different raw `h` choices produce
equivalent results.

Alternative cleaner form:

```lean
def ERLexMorNQuo.equalizerLift {z a b : LexObj}
    {f g : ERLexMorN a b} :
    (h : ERLexMorNQuo z a) →
    (heq :
      ERLexMorNQuo.comp h
        (Quotient.mk (erLexMorNSetoid a b) f) =
      ERLexMorNQuo.comp h
        (Quotient.mk (erLexMorNSetoid a b) g)) →
    ERLexMorNQuo z (LexObj.equalizer f g) :=
  Quotient.ind
    (motive := fun h =>
      ERLexMorNQuo.comp h
        (Quotient.mk (erLexMorNSetoid a b) f) =
      ERLexMorNQuo.comp h
        (Quotient.mk (erLexMorNSetoid a b) g) →
      ERLexMorNQuo z (LexObj.equalizer f g))
    (fun h_raw heq_raw =>
      Quotient.mk
        (erLexMorNSetoid z
          (LexObj.equalizer f g))
        (ERLexMorN.equalizerLift h_raw
          (fun ctx hctx => by
            have := Quotient.exact
              (s := erLexMorNSetoid z b) heq_raw
            have step := this ctx hctx
            simp only [ERLexMorN.comp,
              ERMorN.interp_comp] at step
            exact step)))
```

This uses `Quotient.ind` which doesn't produce a
proof obligation for well-definedness because it's
into a type that depends only on the quotient class
in its motive.  Try this approach first.

- [ ] **Step 4: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Add raw and quotient equalizer lift"
```

---

### Task 7: Universal property theorems

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Prove the lift factors correctly**

Append:

```lean
/-- The equalizer lift composed with the equalizer
inclusion recovers the original morphism. -/
theorem ERLexMorNQuo.equalizerLift_map
    {z a b : LexObj} {f g : ERLexMorN a b}
    (h : ERLexMorNQuo z a)
    (heq :
      ERLexMorNQuo.comp h
        (Quotient.mk (erLexMorNSetoid a b) f) =
      ERLexMorNQuo.comp h
        (Quotient.mk (erLexMorNSetoid a b) g)) :
    ERLexMorNQuo.comp
      (ERLexMorNQuo.equalizerLift h heq)
      (ERLexMorNQuo.equalizerMap f g) = h :=
  Quotient.ind
    (motive := fun h' =>
      (heq' : _ = _) →
      ERLexMorNQuo.comp
        (ERLexMorNQuo.equalizerLift h' heq')
        (ERLexMorNQuo.equalizerMap f g) = h')
    (fun h_raw _ =>
      Quotient.sound
        (s := erLexMorNSetoid z a)
        (fun ctx _ => by
          simp only [ERLexMorN.comp,
            ERLexMorN.equalizerMap,
            ERLexMorN.equalizerLift,
            ERMorN.interp_comp,
            ERMorN.interp_id]))
    h heq
```

The motive annotation needs adjustment for the
hypothesis type — adapt as needed based on
inference messages.

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Prove uniqueness of the lift**

```lean
/-- Uniqueness: any morphism `h' : z → equalizer`
whose composition with the equalizer inclusion
equals `h` must equal the equalizer lift. -/
theorem ERLexMorNQuo.equalizerLift_uniq
    {z a b : LexObj} {f g : ERLexMorN a b}
    (h : ERLexMorNQuo z a)
    (heq :
      ERLexMorNQuo.comp h
        (Quotient.mk (erLexMorNSetoid a b) f) =
      ERLexMorNQuo.comp h
        (Quotient.mk (erLexMorNSetoid a b) g))
    (h' : ERLexMorNQuo z (LexObj.equalizer f g))
    (hmap :
      ERLexMorNQuo.comp h'
        (ERLexMorNQuo.equalizerMap f g) = h) :
    h' = ERLexMorNQuo.equalizerLift h heq :=
  Quotient.ind
    (motive := fun h' =>
      ERLexMorNQuo.comp h'
        (ERLexMorNQuo.equalizerMap f g) = h →
      h' = ERLexMorNQuo.equalizerLift h heq)
    (fun h'_raw hmap_eq => by
      -- h' ≫ equalizerMap has underlying h'_raw.val
      -- (since equalizerMap.val is identity).
      -- So hmap_eq says h'_raw ~ h on z-satisfying
      -- contexts (after lifting through Quotient).
      revert hmap_eq
      refine Quotient.inductionOn h ?_
      intro h_raw hmap_eq
      apply Quotient.sound
        (s := erLexMorNSetoid z
          (LexObj.equalizer f g))
      intro ctx hctx
      have hrel := Quotient.exact
        (s := erLexMorNSetoid z a) hmap_eq
      have step := hrel ctx hctx
      simp only [ERLexMorN.comp,
        ERLexMorN.equalizerMap,
        ERMorN.interp_comp,
        ERMorN.interp_id] at step
      exact step)
    h' hmap
```

- [ ] **Step 4: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Prove equalizer lift correctness and uniqueness"
```

---

### Task 8: Tests and workstream tracker

**Files:**

- Modify: `GebLeanTests/LawvereERLex.lean`
- Modify: `.session/workstreams/lawvere-elementary-recursive.md`

- [ ] **Step 1: Add sanity test for equalizer**

Append to `GebLeanTests/LawvereERLex.lean`:

```lean
-- Equalizer of a morphism with itself is the
-- source (modulo predicate strengthening).  Here
-- we just verify the type checks.
example (a b : LawvereERLexCat)
    (f : ERLexMorN a b) :
    LawvereERLexCat :=
  LexObj.equalizer f f

-- Equalizer morphism types correctly.
example (a b : LawvereERLexCat)
    (f g : ERLexMorN a b) :
    ERLexMorNQuo (LexObj.equalizer f g) a :=
  ERLexMorNQuo.equalizerMap f g
```

- [ ] **Step 2: Build and test**

Run: `lake build && lake test`
Expected: clean build, tests pass.

- [ ] **Step 3: Commit tests**

```bash
git add GebLeanTests/LawvereERLex.lean
git commit -m "Add Phase 4d equalizer sanity tests"
```

- [ ] **Step 4: Update workstream tracker**

Edit the status section in
`.session/workstreams/lawvere-elementary-recursive.md`
to note Phase 4d complete.  Append after the Phase
4c description:

"Phase 4d complete: see `GebLean/LawvereERLex.lean`
extended with `ERBoolPred.alwaysTrueN`,
`ERBoolPred.andSameArity`, `ERBoolPred.allEq`,
`LexObj.equalizer`, equalizer morphism,
equalization theorem, and the raw/quotient lift
constructions with the universal-property
theorems `equalizerLift_map` and
`equalizerLift_uniq`.  A `HasChosenEqualizers` /
`HasFiniteLimits` instance is deferred to a
subsequent plan because chosen-equalizer objects
depend on representative choice."

Update the task checkbox:

```
  * [ ] 4d: Equalizers and finite limits.
```

To:

```
  * [x] 4d: Equalizers (raw construction and
    universal property).  HasFiniteLimits deferred.
```

- [ ] **Step 5: Commit tracker update**

```bash
git add \
  .session/workstreams/lawvere-elementary-recursive.md
git commit -m \
  "Mark ER Phase 4d complete in workstream tracker"
```
