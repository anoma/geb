# Lawvere ER Phase 4d.2: Quotient Predicates and Chosen Equalizers

> **For agentic workers:** REQUIRED SUB-SKILL: Use
> superpowers:subagent-driven-development (recommended) or
> superpowers:executing-plans to implement this plan
> task-by-task. Steps use checkbox (`- [ ]`) syntax for
> tracking.

**Goal:** Refactor `LexObj` to use `ERBoolPredE` —
the quotient of `ERBoolPred` by extensional equality
of the underlying interpretation.  This makes
extensionally equal predicates literally equal as
`LexObj.pred` values, enabling a constructive
`HasChosenEqualizers` instance and a
`HasFiniteLimits` instance for `LawvereERLexCat`
without `Quotient.out` or `Classical.choice`.

**Architecture:** Quotient `ERBoolPred n` by the
setoid `p ~ q ↔ ∀ ctx, p.pred.interp ctx = q.pred.interp
ctx`.  Replace `LexObj.pred : ERBoolPred arity` with
`pred : ERBoolPredE arity`.  All membership conditions
(`pred.interp ctx = 1`) become `pred.eval ctx = 1`,
where `eval` is `ERBoolPred.pred.interp` lifted through
the quotient.  The conjoined predicate `a.pred ⊓ allEq f
g` is well-defined modulo morphism representatives
(off-subobject contexts contribute `0` to the
conjunction), so it lifts cleanly through `Quotient.lift₂`
on the morphism quotients to give a chosen equalizer.

**Tech Stack:** Lean 4, Mathlib (`Quotient` API,
`Quotient.lift`, `Quotient.lift₂`, `Quotient.sound`).
Depends on Phases 4a–4d.

---

## File Map

| File | Role |
| ---- | ---- |
| Modify: `GebLean/LawvereERLex.lean` | Add `ERBoolPred.ExtEq` setoid, `ERBoolPredE`, `eval` lift, Boolean closure; refactor `LexObj`, `ERLexMorN`, all setoids and morphism layer to use `eval`; provide `ERBoolPredE` versions of all helper combinators (`alwaysTrueE`, `andSameArityE`, `andE`, `allEqE`); add `LexObj.equalizerQ` taking quotient morphisms; add `HasChosenEqualizers` and `HasFiniteLimits` instances |
| Modify: `GebLeanTests/LawvereERLex.lean` | Update tests for refactored types; add chosen-equalizer test |
| Modify: `.session/workstreams/lawvere-elementary-recursive.md` | Mark Phase 4d.2 complete |

---

## Strategy Notes

This refactor is necessarily a bit invasive because
`LexObj.pred`'s type changes.  Strategy: introduce
`ERBoolPredE` and the lifted operations alongside the
existing `ERBoolPred` machinery, then switch `LexObj`
in a single coordinated commit that updates all
membership-checking sites at once.  After that, add
the new chosen-equalizer infrastructure on top.

Throughout: every occurrence of
`obj.pred.pred.interp ctx` becomes `obj.pred.eval ctx`.
The `eval` projection lifts cleanly via `Quotient.lift`
because `ERMor1.interp` is well-defined modulo
extensional equality of the term (this is the very
relation the setoid identifies).

---

### Task 1: ERBoolPredE quotient and `eval`

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Add `ERBoolPred.ExtEq` setoid**

Append after the `ERBoolPred` structure definition
(after the existing `ERBoolPred` block, before
`ERBoolPred.alwaysTrueN`):

```lean
/-- Extensional equality on `ERBoolPred n`: two
predicates are related when their underlying
interpretations agree on every context.  This is
the relation we quotient by to obtain a predicate
type whose equality matches the categorical notion
of "same subobject". -/
def ERBoolPred.ExtEq (n : ℕ) :
    Setoid (ERBoolPred n) where
  r p q := ∀ ctx : Fin n → ℕ,
    p.pred.interp ctx = q.pred.interp ctx
  iseqv := {
    refl := fun _ _ => rfl
    symm := fun h ctx => (h ctx).symm
    trans := fun h1 h2 ctx =>
      (h1 ctx).trans (h2 ctx)
  }

/-- Quotient of `ERBoolPred n` by extensional
equality.  Used as the predicate type of `LexObj`
so that semantically equal predicates yield equal
objects. -/
def ERBoolPredE (n : ℕ) : Type :=
  Quotient (ERBoolPred.ExtEq n)
```

- [ ] **Step 2: Build**

Run: `lake build`
Expected: clean build.

- [ ] **Step 3: Add `eval` and Boolean closure**

```lean
/-- Lift the interpretation through the quotient:
evaluate a `ERBoolPredE` predicate on a context.
Well-defined because the setoid identifies
predicates with equal interpretations. -/
def ERBoolPredE.eval {n : ℕ}
    (p : ERBoolPredE n) (ctx : Fin n → ℕ) : ℕ :=
  Quotient.liftOn p
    (fun p' => p'.pred.interp ctx)
    (fun _ _ h => h ctx)

/-- The eval of a `ERBoolPredE` is bounded by `1`:
this is the lifted Boolean property. -/
theorem ERBoolPredE.eval_le_one {n : ℕ}
    (p : ERBoolPredE n) (ctx : Fin n → ℕ) :
    p.eval ctx ≤ 1 := by
  induction p using Quotient.ind with
  | _ p_raw => exact p_raw.bool ctx

/-- Computation lemma: `eval` on a concrete
representative reduces to the underlying
`ERBoolPred.pred.interp`. -/
@[simp] theorem ERBoolPredE.eval_mk
    {n : ℕ} (p : ERBoolPred n)
    (ctx : Fin n → ℕ) :
    (Quotient.mk (ERBoolPred.ExtEq n) p).eval
      ctx = p.pred.interp ctx :=
  rfl
```

- [ ] **Step 4: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Add ERBoolPredE quotient and eval"
```

---

### Task 2: `ERBoolPredE` versions of helper combinators

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Add `ERBoolPredE.alwaysTrue`**

Append after the `eval_mk` lemma:

```lean
/-- The always-true predicate at arity `n` in the
quotient form. -/
def ERBoolPredE.alwaysTrue (n : ℕ) :
    ERBoolPredE n :=
  Quotient.mk (ERBoolPred.ExtEq n)
    (ERBoolPred.alwaysTrueN n)

/-- Eval of `alwaysTrue` is always `1`. -/
@[simp] theorem ERBoolPredE.alwaysTrue_eval
    (n : ℕ) (ctx : Fin n → ℕ) :
    (ERBoolPredE.alwaysTrue n).eval ctx = 1 :=
  rfl
```

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Add `ERBoolPredE.andSameArity`**

```lean
/-- Conjunction of two same-arity quotient
predicates, lifted from the raw `andSameArity` via
`Quotient.lift₂`. -/
def ERBoolPredE.andSameArity {n : ℕ}
    (p q : ERBoolPredE n) : ERBoolPredE n :=
  Quotient.lift₂
    (s₁ := ERBoolPred.ExtEq n)
    (s₂ := ERBoolPred.ExtEq n)
    (fun p' q' =>
      Quotient.mk (ERBoolPred.ExtEq n)
        (ERBoolPred.andSameArity p' q'))
    (fun pa pb qa qb hp hq =>
      Quotient.sound
        (s := ERBoolPred.ExtEq n)
        (fun ctx => by
          simp only
            [ERBoolPred.andSameArity_interp]
          rw [hp ctx, hq ctx]))
    p q

/-- Eval of `andSameArity` is the product of the
two evals. -/
@[simp] theorem ERBoolPredE.andSameArity_eval
    {n : ℕ} (p q : ERBoolPredE n)
    (ctx : Fin n → ℕ) :
    (ERBoolPredE.andSameArity p q).eval ctx =
      p.eval ctx * q.eval ctx := by
  induction p using Quotient.ind with
  | _ p_raw =>
    induction q using Quotient.ind with
    | _ q_raw =>
      change (ERBoolPred.andSameArity p_raw
          q_raw).pred.interp ctx = _
      rw [ERBoolPred.andSameArity_interp]
      rfl
```

- [ ] **Step 4: Build**

Run: `lake build`

- [ ] **Step 5: Add `ERBoolPredE.and` (binary product)**

```lean
/-- Conjunction of two different-arity quotient
predicates, yielding a quotient predicate at arity
`n + m`. -/
def ERBoolPredE.and {n m : ℕ}
    (p : ERBoolPredE n) (q : ERBoolPredE m) :
    ERBoolPredE (n + m) :=
  Quotient.lift₂
    (s₁ := ERBoolPred.ExtEq n)
    (s₂ := ERBoolPred.ExtEq m)
    (fun p' q' =>
      Quotient.mk (ERBoolPred.ExtEq (n + m))
        (ERBoolPred.and p' q'))
    (fun pa pb qa qb hp hq =>
      Quotient.sound
        (s := ERBoolPred.ExtEq (n + m))
        (fun ctx => by
          simp only [ERBoolPred.and_interp]
          rw [hp _, hq _]))
    p q

/-- Eval of `and`: product of the two evals at the
respective coordinate slices. -/
@[simp] theorem ERBoolPredE.and_eval
    {n m : ℕ} (p : ERBoolPredE n)
    (q : ERBoolPredE m)
    (ctx : Fin (n + m) → ℕ) :
    (ERBoolPredE.and p q).eval ctx =
      p.eval (ERMorN.fst.interp ctx) *
      q.eval (ERMorN.snd.interp ctx) := by
  induction p using Quotient.ind with
  | _ p_raw =>
    induction q using Quotient.ind with
    | _ q_raw =>
      change (ERBoolPred.and p_raw
          q_raw).pred.interp ctx = _
      rw [ERBoolPred.and_interp]
      rfl
```

- [ ] **Step 6: Add `ERBoolPredE.allEq`**

```lean
/-- Componentwise equality of two raw `ERMorN`
tuples, packaged as a quotient predicate. -/
def ERBoolPredE.allEq {n m : ℕ}
    (f g : ERMorN n m) : ERBoolPredE n :=
  Quotient.mk (ERBoolPred.ExtEq n)
    (ERBoolPred.allEq f g)

/-- Eval of `allEq` matches the underlying
`ERBoolPred.allEq` interpretation. -/
@[simp] theorem ERBoolPredE.allEq_eval
    {n m : ℕ} (f g : ERMorN n m)
    (ctx : Fin n → ℕ) :
    (ERBoolPredE.allEq f g).eval ctx =
      (ERBoolPred.allEq f g).pred.interp ctx :=
  rfl
```

- [ ] **Step 7: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Add ERBoolPredE versions of predicate helpers"
```

---

### Task 3: Refactor `LexObj` and morphism layer

This is the largest task — switching `LexObj.pred`'s
type breaks compilation everywhere it's used.  We
update all dependents in one coordinated change.

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Change `LexObj.pred` to `ERBoolPredE`**

Replace the `LexObj` definition:

```lean
/-- Object of `LawvereERLexCat`: an arity together
with a Boolean-valued *quotient* predicate cutting
out a decidable subobject of `Fin arity -> ℕ`.
Using the quotient `ERBoolPredE` (rather than raw
`ERBoolPred`) means semantically equal predicates
yield literally equal objects. -/
structure LexObj where
  /-- The arity (number of free variables). -/
  arity : ℕ
  /-- The Boolean predicate (quotient class). -/
  pred : ERBoolPredE arity
```

- [ ] **Step 2: Update `ERLexMorN` to use `eval`**

Replace the `ERLexMorN` definition:

```lean
/-- Raw morphism in `LawvereERLexCat`: an `ERMorN`
tuple that respects membership.  Membership is now
expressed via the lifted `eval`. -/
def ERLexMorN (src tgt : LexObj) : Type :=
  { f : ERMorN src.arity tgt.arity //
      ∀ ctx : Fin src.arity → ℕ,
        src.pred.eval ctx = 1 →
        tgt.pred.eval (f.interp ctx) = 1 }
```

- [ ] **Step 3: Update `erLexMorNSetoid` to use `eval`**

Replace the setoid definition:

```lean
/-- The setoid on `ERLexMorN src tgt`: source-
restricted extensional equality, with membership
checked via `eval`. -/
def erLexMorNSetoid (src tgt : LexObj) :
    Setoid (ERLexMorN src tgt) where
  r f g :=
    ∀ ctx : Fin src.arity → ℕ,
      src.pred.eval ctx = 1 →
      f.val.interp ctx = g.val.interp ctx
  iseqv := {
    refl := fun _ _ _ => rfl
    symm := fun h ctx hctx => (h ctx hctx).symm
    trans := fun h1 h2 ctx hctx =>
      (h1 ctx hctx).trans (h2 ctx hctx)
  }
```

- [ ] **Step 4: Update `ERLexMorN.id` respect proof**

The id respect proof needs to use eval instead of
the old `pred.pred.interp`.  Replace:

```lean
def ERLexMorN.id (obj : LexObj) :
    ERLexMorN obj obj :=
  ⟨ERMorN.id obj.arity, fun ctx hctx => by
    rw [ERMorN.interp_id]
    exact hctx⟩
```

- [ ] **Step 5: Update `ERLexMorN.comp` respect proof**

```lean
def ERLexMorN.comp
    {src mid tgt : LexObj}
    (f : ERLexMorN src mid)
    (g : ERLexMorN mid tgt) :
    ERLexMorN src tgt :=
  ⟨ERMorN.comp f.val g.val, fun ctx hctx => by
    rw [ERMorN.interp_comp]
    exact g.property _ (f.property ctx hctx)⟩
```

(This may not need any changes structurally; only
the type signature of `f.property` / `g.property`
changes.  Verify it compiles.)

- [ ] **Step 6: Build**

Run: `lake build`
Expected: this likely cascades errors through the
file.  Each error site needs `pred.pred.interp`
replaced with `eval`, or the structure literal for
LexObj's `pred` field updated to use `ERBoolPredE`.

- [ ] **Step 7: Update `LexObj.terminal`**

Replace:

```lean
def LexObj.terminal : LexObj where
  arity := 0
  pred := ERBoolPredE.alwaysTrue 0
```

- [ ] **Step 8: Update `ERLexMorN.toTerminal`**

Replace the respect proof to use eval:

```lean
def ERLexMorN.toTerminal (obj : LexObj) :
    ERLexMorN obj LexObj.terminal :=
  ⟨ERMorN.terminal obj.arity, fun _ _ => by
    show (LexObj.terminal.pred).eval _ = 1
    rw [LexObj.terminal]
    exact ERBoolPredE.alwaysTrue_eval _ _⟩
```

If `show` is not accepted, use `change`.

- [ ] **Step 9: Update `LexObj.prod` to use `ERBoolPredE.and`**

Replace:

```lean
def LexObj.prod (a b : LexObj) : LexObj where
  arity := a.arity + b.arity
  pred := ERBoolPredE.and a.pred b.pred
```

- [ ] **Step 10: Update product `pi1`/`pi2`/`pair`/
  laws/instance**

These respect proofs and theorems all use
`obj.pred.pred.interp` → `obj.pred.eval`.  Walk
through each one mechanically:

- `ERLexMorN.pi1`: change `hctx` rewrite from
  `ERBoolPred.and_interp` to use `ERBoolPredE`-level
  `and_eval`.  The structure: `change (a.prod
  b).pred.eval ctx = 1 at hctx; rw
  [ERBoolPredE.and_eval]; ...`.

- `ERLexMorN.pi2`: analogous.

- `ERLexMorN.pair`: respect proof uses `eval` on
  the conjoined predicate.  The proof structure
  becomes:

```lean
def ERLexMorN.pair {z a b : LexObj}
    (f : ERLexMorN z a) (g : ERLexMorN z b) :
    ERLexMorN z (LexObj.prod a b) :=
  ⟨ERMorN.pair f.val g.val, fun ctx hctx => by
    show (LexObj.prod a b).pred.eval _ = 1
    rw [show (LexObj.prod a b).pred =
        ERBoolPredE.and a.pred b.pred from rfl,
        ERBoolPredE.and_eval]
    have hf : a.pred.eval
        (ERMorN.fst.interp
          ((ERMorN.pair f.val g.val).interp ctx)) =
        1 := by
      have step : ERMorN.fst.interp
          ((ERMorN.pair f.val g.val).interp ctx) =
          f.val.interp ctx := by
        funext i
        simp only [ERMorN.interp_fst,
          ERMorN.interp_pair]
        rw [dif_pos i.isLt]
        rfl
      rw [step]
      exact f.property ctx hctx
    have hg : b.pred.eval
        (ERMorN.snd.interp
          ((ERMorN.pair f.val g.val).interp ctx)) =
        1 := by
      have step : ERMorN.snd.interp
          ((ERMorN.pair f.val g.val).interp ctx) =
          g.val.interp ctx := by
        funext i
        simp only [ERMorN.interp_snd,
          ERMorN.interp_pair]
        have h : ¬ (a.arity + i.val) < a.arity := by
          omega
        rw [dif_neg h]
        have idx_eq :
            (⟨a.arity + i.val - a.arity, by omega⟩
              : Fin b.arity) = i := by
          apply Fin.ext
          change a.arity + i.val - a.arity = i.val
          omega
        rw [idx_eq]
        rfl
      rw [step]
      exact g.property ctx hctx
    rw [hf, hg]⟩
```

(Mostly structural rewriting — `pred.pred.interp`
becomes `pred.eval`.)

- `pair_pi1`, `pair_pi2`, `pair_uniq`: these don't
  reach into the predicate structure, so they
  should compile after the type changes propagate.

- `lawvereERLexProduct`, `lawvereERLexTerminal`,
  `HasChosenFiniteProducts` instance: should
  compile unchanged once the types match.

- [ ] **Step 11: Update equalizer infrastructure
  (Phase 4d items)**

- `LexObj.equalizer (raw)`: predicate becomes
  `ERBoolPredE.andSameArity a.pred (ERBoolPredE.allEq
  f.val g.val)`.

- `ERLexMorN.equalizerMap`: respect proof uses
  `eval` and `ERBoolPredE.andSameArity_eval`.

- `equalizerMap_eq`: similar update.

- `ERLexMorN.equalizerLift`: respect proof uses
  `eval`.

- `equalizerLift_map`, `equalizerLift_uniq`: should
  compile after type changes.

- [ ] **Step 12: Build and commit**

Run: `lake build`
Expected: clean build, all existing functionality
preserved.

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Refactor LexObj to use ERBoolPredE quotient"
```

---

### Task 4: Chosen equalizer taking quotient morphisms

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

The chosen equalizer object is parameterized by
quotient morphisms `f, g : a ⟶ b` (now well-typed
as `ERLexMorNQuo a b`), and produces a `LexObj`.
Well-definedness: the predicate `a.pred ⊓ allEq f g`
is the same `ERBoolPredE` value for any choice of
representatives `f, g`, because off-`a.pred=1`
contexts the conjunction is `0` regardless.

- [ ] **Step 1: Add a well-definedness lemma**

Insert near `LexObj.equalizer`:

```lean
/-- The combined equalizer predicate is well-
defined modulo morphism representatives.  This is
the lemma that lets us define the chosen equalizer
at the quotient level. -/
theorem ERBoolPredE.equalizerPred_wd
    {a b : LexObj} {f₁ f₂ g₁ g₂ : ERLexMorN a b}
    (hf : (erLexMorNSetoid a b).r f₁ f₂)
    (hg : (erLexMorNSetoid a b).r g₁ g₂) :
    ERBoolPredE.andSameArity a.pred
        (ERBoolPredE.allEq f₁.val g₁.val) =
      ERBoolPredE.andSameArity a.pred
        (ERBoolPredE.allEq f₂.val g₂.val) := by
  induction a.pred using Quotient.ind with
  | _ a_pred_raw =>
    apply Quotient.sound
      (s := ERBoolPred.ExtEq a.arity)
    intro ctx
    show (ERBoolPred.andSameArity a_pred_raw
        (ERBoolPred.allEq f₁.val
          g₁.val)).pred.interp ctx =
      (ERBoolPred.andSameArity a_pred_raw
        (ERBoolPred.allEq f₂.val
          g₂.val)).pred.interp ctx
    rw [ERBoolPred.andSameArity_interp,
        ERBoolPred.andSameArity_interp]
    by_cases h0 : a_pred_raw.pred.interp ctx = 0
    · rw [h0]; ring
    · have h1 : a_pred_raw.pred.interp ctx = 1 := by
        have := a_pred_raw.bool ctx
        omega
      rw [h1]
      have hctx_e :
          (Quotient.mk (ERBoolPred.ExtEq a.arity)
            a_pred_raw : ERBoolPredE a.arity).eval
            ctx = 1 := h1
      have hf_at : f₁.val.interp ctx =
          f₂.val.interp ctx := hf ctx hctx_e
      have hg_at : g₁.val.interp ctx =
          g₂.val.interp ctx := hg ctx hctx_e
      have eq1 : (ERBoolPred.allEq f₁.val
          g₁.val).pred.interp ctx =
        (ERBoolPred.allEq f₂.val
          g₂.val).pred.interp ctx := by
        by_cases heq : f₁.val.interp ctx =
            g₁.val.interp ctx
        · have heq2 : f₂.val.interp ctx =
              g₂.val.interp ctx := by
            rw [← hf_at, ← hg_at]; exact heq
          rw [ERBoolPred.allEq_of_eq _ _ _ heq,
              ERBoolPred.allEq_of_eq _ _ _ heq2]
        · have heq2 : f₂.val.interp ctx ≠
              g₂.val.interp ctx := by
            rw [← hf_at, ← hg_at]; exact heq
          have hne1 : (ERBoolPred.allEq f₁.val
              g₁.val).pred.interp ctx ≠ 1 :=
            fun h => heq
              (ERBoolPred.allEq_eq_one_imp _ _ _ h)
          have hne2 : (ERBoolPred.allEq f₂.val
              g₂.val).pred.interp ctx ≠ 1 :=
            fun h => heq2
              (ERBoolPred.allEq_eq_one_imp _ _ _ h)
          have hle1 : (ERBoolPred.allEq f₁.val
              g₁.val).pred.interp ctx ≤ 1 :=
            (ERBoolPred.allEq f₁.val g₁.val).bool _
          have hle2 : (ERBoolPred.allEq f₂.val
              g₂.val).pred.interp ctx ≤ 1 :=
            (ERBoolPred.allEq f₂.val g₂.val).bool _
          omega
      rw [eq1]
```

If parts of the proof don't go through, the
implementer should adapt — the structure is: case
on `a.pred = 0 vs 1`, in the 0 case both products
are 0, in the 1 case use `hf, hg` to get
extensional agreement and split on `f₁ = g₁` at
ctx vs not.

- [ ] **Step 2: Build**

Run: `lake build`

- [ ] **Step 3: Define `LexObj.equalizerQ`**

```lean
/-- Chosen equalizer object for parallel quotient
morphisms `f, g : a ⟶ b`.  Well-defined modulo
representatives by `equalizerPred_wd`. -/
def LexObj.equalizerQ {a b : LexObj}
    (f g : ERLexMorNQuo a b) : LexObj where
  arity := a.arity
  pred := Quotient.liftOn₂
    (s₁ := erLexMorNSetoid a b)
    (s₂ := erLexMorNSetoid a b)
    f g
    (fun f' g' =>
      ERBoolPredE.andSameArity a.pred
        (ERBoolPredE.allEq f'.val g'.val))
    (fun _ _ _ _ hf hg =>
      ERBoolPredE.equalizerPred_wd hf hg)
```

- [ ] **Step 4: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Add chosen equalizer object LexObj.equalizerQ"
```

---

### Task 5: Chosen equalizer morphism and universal property

**Files:**

- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Add chosen equalizer morphism**

```lean
/-- The chosen equalizer inclusion morphism, taking
quotient morphisms as parameters. -/
def ERLexMorNQuo.equalizerQMap {a b : LexObj}
    (f g : ERLexMorNQuo a b) :
    ERLexMorNQuo (LexObj.equalizerQ f g) a :=
  Quotient.liftOn₂
    (s₁ := erLexMorNSetoid a b)
    (s₂ := erLexMorNSetoid a b)
    f g
    (fun f' g' => by
      -- The underlying object equals
      -- LexObj.equalizer f' g' for the chosen reps.
      exact Quotient.mk
        (erLexMorNSetoid (LexObj.equalizerQ f g) a)
        ⟨ERMorN.id a.arity, fun ctx hctx => by
          -- hctx : (LexObj.equalizerQ f g).pred.eval
          --       ctx = 1
          -- Unfold equalizerQ.pred to
          -- andSameArity a.pred (allEq f' g')
          change (ERBoolPredE.andSameArity a.pred
              (ERBoolPredE.allEq f'.val
                g'.val)).eval ctx = 1 at hctx
          rw [ERBoolPredE.andSameArity_eval]
              at hctx
          rw [ERMorN.interp_id]
          exact (mul_eq_one.mp hctx).1⟩)
    (fun _ _ _ _ _ _ => by
      -- The morphism quotient class doesn't depend
      -- on representatives because the underlying
      -- raw morphism is always ERMorN.id, and the
      -- target type is the same LexObj.equalizerQ
      sorry)
```

This task is delicate — the well-definedness has
type-dependency issues because the source object
`LexObj.equalizerQ f g` is defined via lift on
`f, g`, and we're again lifting via `f', g'`.  The
implementer may need to use `Quotient.hrec` or a
manual fixed-representative approach.

ALTERNATE APPROACH: Define the chosen equalizer
morphism directly as a quotient class of the
identity-tuple `ERLexMorN`, since the underlying
tuple is always `ERMorN.id a.arity`:

```lean
def ERLexMorNQuo.equalizerQMap {a b : LexObj}
    (f g : ERLexMorNQuo a b) :
    ERLexMorNQuo (LexObj.equalizerQ f g) a :=
  Quotient.mk
    (erLexMorNSetoid (LexObj.equalizerQ f g) a)
    ⟨ERMorN.id a.arity, fun ctx hctx => by
      -- hctx : (LexObj.equalizerQ f g).pred.eval
      --       ctx = 1
      -- We need to extract a.pred.eval ctx = 1
      -- from this.  Unfold equalizerQ.pred via
      -- Quotient.ind on f and g.
      revert hctx
      refine Quotient.ind₂ ?_ f g
      intro f' g' hctx
      change (ERBoolPredE.andSameArity a.pred
          (ERBoolPredE.allEq f'.val
            g'.val)).eval ctx = 1 at hctx
      rw [ERBoolPredE.andSameArity_eval] at hctx
      rw [ERMorN.interp_id]
      exact (mul_eq_one.mp hctx).1⟩
```

The `revert hctx; refine Quotient.ind₂ ...` pattern
unfolds the quotient under the type dependency.

- [ ] **Step 2: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Add chosen equalizer morphism equalizerQMap"
```

- [ ] **Step 3: Add chosen equalizer equalization theorem**

```lean
/-- The chosen equalizer morphism equalizes `f`
and `g`. -/
theorem ERLexMorNQuo.equalizerQMap_eq
    {a b : LexObj} (f g : ERLexMorNQuo a b) :
    ERLexMorNQuo.comp
      (ERLexMorNQuo.equalizerQMap f g) f =
    ERLexMorNQuo.comp
      (ERLexMorNQuo.equalizerQMap f g) g := by
  refine Quotient.ind₂ ?_ f g
  intro f' g'
  -- After unwrapping quotients, this reduces to the
  -- raw equalization, which is exactly Phase 4d's
  -- equalizerMap_eq.
  exact ERLexMorNQuo.equalizerMap_eq f' g'
```

- [ ] **Step 4: Build**

Run: `lake build`

- [ ] **Step 5: Add chosen equalizer lift and uniqueness**

```lean
/-- Chosen equalizer lift: given `h : z → a` whose
compositions with the quotient morphisms `f`, `g`
agree, produces a lift to `equalizerQ f g`. -/
def ERLexMorNQuo.equalizerQLift {z a b : LexObj}
    (f g : ERLexMorNQuo a b)
    (h : ERLexMorNQuo z a)
    (heq : ERLexMorNQuo.comp h f =
           ERLexMorNQuo.comp h g) :
    ERLexMorNQuo z (LexObj.equalizerQ f g) :=
  Quotient.liftOn h
    (fun h_raw =>
      Quotient.mk _
        ⟨h_raw.val, fun ctx hctx => by
          -- The respect proof: need
          -- (equalizerQ f g).pred.eval
          --   (h_raw.val.interp ctx) = 1
          revert heq
          refine Quotient.ind₂ ?_ f g
          intro f' g' heq
          change (ERBoolPredE.andSameArity a.pred
              (ERBoolPredE.allEq f'.val
                g'.val)).eval _ = 1
          rw [ERBoolPredE.andSameArity_eval]
          have h1 : a.pred.eval
              (h_raw.val.interp ctx) = 1 :=
            h_raw.property ctx hctx
          have h2 : (ERBoolPredE.allEq f'.val
              g'.val).eval (h_raw.val.interp
              ctx) = 1 := by
            apply ERBoolPred.allEq_of_eq
            -- Need: f'.val.interp (h_raw.val.interp
            --       ctx) = g'.val.interp (...)
            have hcomp := Quotient.exact
              (s := erLexMorNSetoid z b) heq
            have step := hcomp ctx hctx
            simp only [ERLexMorN.comp,
              ERMorN.interp_comp] at step
            exact step
          rw [h1, h2]⟩)
    (fun h₁ h₂ hrel =>
      Quotient.sound (fun ctx hctx =>
        hrel ctx hctx))
```

If there are issues with the dependent types in the
`Quotient.liftOn` (because the target type depends
on `f, g`), the implementer should use
`Quotient.hrecOn` instead, or precompute the
respect proof outside the lift.

- [ ] **Step 6: Build**

Run: `lake build`

- [ ] **Step 7: Prove equalizerQLift universal property**

```lean
/-- The lift, composed with the equalizer
inclusion, recovers `h`. -/
theorem ERLexMorNQuo.equalizerQLift_map
    {z a b : LexObj} (f g : ERLexMorNQuo a b)
    (h : ERLexMorNQuo z a)
    (heq : ERLexMorNQuo.comp h f =
           ERLexMorNQuo.comp h g) :
    ERLexMorNQuo.comp
      (ERLexMorNQuo.equalizerQLift f g h heq)
      (ERLexMorNQuo.equalizerQMap f g) = h := by
  refine Quotient.ind ?_ h
  intro h_raw
  apply Quotient.sound
    (s := erLexMorNSetoid z a)
  intro ctx _
  show (ERMorN.comp h_raw.val
      (ERMorN.id a.arity)).interp ctx =
    h_raw.val.interp ctx
  rw [ERMorN.interp_comp]
  rfl

/-- Uniqueness: the lift is unique. -/
theorem ERLexMorNQuo.equalizerQLift_uniq
    {z a b : LexObj} (f g : ERLexMorNQuo a b)
    (h : ERLexMorNQuo z a)
    (heq : ERLexMorNQuo.comp h f =
           ERLexMorNQuo.comp h g)
    (h' : ERLexMorNQuo z (LexObj.equalizerQ f g))
    (hmap : ERLexMorNQuo.comp h'
        (ERLexMorNQuo.equalizerQMap f g) = h) :
    h' = ERLexMorNQuo.equalizerQLift f g h heq := by
  refine Quotient.ind ?_ h'
  intro h'_raw
  refine Quotient.ind ?_ h
  intro h_raw hmap
  -- Same uniqueness reasoning as Phase 4d
  -- equalizerLift_uniq, just lifted to use the
  -- quotient morphisms.
  apply Quotient.sound
    (s := erLexMorNSetoid z (LexObj.equalizerQ f g))
  intro ctx hctx
  have hrel := Quotient.exact
    (s := erLexMorNSetoid z a) hmap
  have step := hrel ctx hctx
  change (ERMorN.comp h'_raw.val
      (ERMorN.id a.arity)).interp ctx =
    h_raw.val.interp ctx at step
  simp only [ERMorN.interp_comp] at step
  change h'_raw.val.interp ctx = h_raw.val.interp
    ctx
  exact step
```

The `Quotient.ind` on the dependent `h` may need
adjustment if the motive isn't inferring correctly.

- [ ] **Step 8: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean
git commit -m "Prove chosen equalizer universal property"
```

---

### Task 6: HasChosenEqualizers and HasFiniteLimits

**Files:**

- Modify: `GebLean/Utilities/ComputableLimits.lean` (if it doesn't already have these classes)
- Modify: `GebLean/LawvereERLex.lean`

- [ ] **Step 1: Check if ComputableLimits has equalizer
  structures**

Run: `grep -n "ChosenEqualizer\|HasChosenEqualizers" /home/terence/git-workspaces/geb-syntax/geb-lean/GebLean/Utilities/ComputableLimits.lean`

If absent, add minimal structures for chosen
equalizers.  If present, skip to Step 3.

- [ ] **Step 2: Add ChosenEqualizer structures (if needed)**

If ComputableLimits doesn't have these, add to
`GebLean/Utilities/ComputableLimits.lean`:

```lean
/-- Chosen computable equalizer data for parallel
morphisms `f, g : A ⟶ B`. -/
structure ChosenEqualizer
    {C : Type u} [Category.{v} C]
    {A B : C} (f g : A ⟶ B) where
  /-- The equalizer object. -/
  obj : C
  /-- The equalizer inclusion morphism. -/
  ι : obj ⟶ A
  /-- The inclusion equalizes f and g. -/
  ι_eq : ι ≫ f = ι ≫ g
  /-- Universal lift. -/
  lift : ∀ {Z : C} (h : Z ⟶ A), h ≫ f = h ≫ g →
    (Z ⟶ obj)
  /-- Lift composed with inclusion recovers h. -/
  lift_ι : ∀ {Z : C} (h : Z ⟶ A)
    (heq : h ≫ f = h ≫ g),
    lift h heq ≫ ι = h
  /-- Uniqueness of lift. -/
  lift_uniq : ∀ {Z : C} (h : Z ⟶ A)
    (heq : h ≫ f = h ≫ g) (h' : Z ⟶ obj),
    h' ≫ ι = h → h' = lift h heq

/-- A category with chosen computable equalizers
for every parallel pair. -/
class HasChosenEqualizers
    (C : Type u) [Category.{v} C] where
  equalizer : ∀ {A B : C} (f g : A ⟶ B),
    ChosenEqualizer f g

/-- A category with chosen computable finite
limits: chosen finite products and chosen
equalizers. -/
class HasChosenFiniteLimits
    (C : Type u) [Category.{v} C] extends
    HasChosenFiniteProducts C,
    HasChosenEqualizers C
```

- [ ] **Step 3: Build (if ComputableLimits modified)**

Run: `lake build`

- [ ] **Step 4: Add `HasChosenEqualizers` instance**

Append to `GebLean/LawvereERLex.lean`:

```lean
/-- Chosen equalizer for parallel morphisms in
`LawvereERLexCat`. -/
def lawvereERLexEqualizer
    {a b : LawvereERLexCat}
    (f g : a ⟶ b) :
    ChosenEqualizer f g where
  obj := LexObj.equalizerQ f g
  ι := ERLexMorNQuo.equalizerQMap f g
  ι_eq := ERLexMorNQuo.equalizerQMap_eq f g
  lift h heq :=
    ERLexMorNQuo.equalizerQLift f g h heq
  lift_ι h heq :=
    ERLexMorNQuo.equalizerQLift_map f g h heq
  lift_uniq h heq h' hmap :=
    ERLexMorNQuo.equalizerQLift_uniq f g h heq h'
      hmap

/-- `LawvereERLexCat` has chosen equalizers. -/
instance : HasChosenEqualizers LawvereERLexCat where
  equalizer f g := lawvereERLexEqualizer f g

/-- `LawvereERLexCat` has chosen finite limits. -/
instance : HasChosenFiniteLimits
    LawvereERLexCat where
```

- [ ] **Step 5: Build and commit**

Run: `lake build`

```bash
git add GebLean/LawvereERLex.lean \
  GebLean/Utilities/ComputableLimits.lean
git commit -m "Add HasChosenEqualizers and HasFiniteLimits instances"
```

---

### Task 7: Tests

**Files:**

- Modify: `GebLeanTests/LawvereERLex.lean`

- [ ] **Step 1: Update existing tests for new types**

Existing test code that constructs `LexObj` with an
inline `ERBoolPred` predicate field needs updating
to use `ERBoolPredE.alwaysTrue` or similar.  Walk
through the file and update:

```lean
private def truePred0 : ERBoolPred 0 :=
  { pred := oneZero
    bool := fun _ => by
      show oneZero.interp _ ≤ 1
      rfl }

private def trueObj0 : LexObj :=
  { arity := 0, pred := truePred0 }
```

becomes:

```lean
private def trueObj0 : LexObj :=
  { arity := 0
    pred := ERBoolPredE.alwaysTrue 0 }
```

- [ ] **Step 2: Add chosen equalizer test**

Append to `GebLeanTests/LawvereERLex.lean`:

```lean
-- Chosen equalizer instance is available.
example : HasChosenEqualizers LawvereERLexCat :=
  inferInstance

-- Chosen finite limits instance is available.
example : HasChosenFiniteLimits LawvereERLexCat :=
  inferInstance

-- Chosen equalizer of identity with itself produces
-- a well-typed object.
example (a b : LawvereERLexCat)
    (f : a ⟶ b) : LawvereERLexCat :=
  (HasChosenEqualizers.equalizer f f).obj
```

- [ ] **Step 3: Build and test**

Run: `lake build && lake test`
Expected: clean build, all tests pass.

- [ ] **Step 4: Commit**

```bash
git add GebLeanTests/LawvereERLex.lean
git commit -m "Update tests for ERBoolPredE and add chosen equalizer test"
```

---

### Task 8: Workstream tracker update

**Files:**

- Modify: `.session/workstreams/lawvere-elementary-recursive.md`

- [ ] **Step 1: Add Phase 4d.2 description to status
  section**

Append after the existing Phase 4d description:

"Phase 4d.2 complete: see `GebLean/LawvereERLex.lean`
extended with `ERBoolPred.ExtEq` setoid and the
quotient `ERBoolPredE`, lifted `eval`/`eval_le_one`
operations, `ERBoolPredE` versions of the predicate
combinators (`alwaysTrue`, `andSameArity`, `and`,
`allEq`); `LexObj.pred` now has type `ERBoolPredE
arity` (extensionally equal predicates yield equal
objects); chosen equalizer `LexObj.equalizerQ`
(parameterized by quotient morphisms),
`equalizerQMap`, `equalizerQLift` with universal
property; `HasChosenEqualizers` and
`HasChosenFiniteLimits` instances on
`LawvereERLexCat`.  Approach avoids `Quotient.out`
and `Classical.choice` entirely."

- [ ] **Step 2: Add Phase 4d.2 to task list**

Replace the existing Phase 4d entry's sub-bullets:

```
  * [x] 4d: Equalizers (raw construction and
    universal property).  HasFiniteLimits deferred.
```

with:

```
  * [x] 4d: Equalizers (raw construction and
    universal property).
  * [x] 4d.2: ERBoolPredE quotient + chosen
    equalizers + HasFiniteLimits.
```

- [ ] **Step 3: Commit**

```bash
git add \
  .session/workstreams/lawvere-elementary-recursive.md
git commit -m "Mark ER Phase 4d.2 complete in workstream tracker"
```
