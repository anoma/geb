# TowerBound architecture for K^sim_2 ⊆ ER formalization (v3 design)

> **SUPERSEDED 2026-05-02**.  The TowerBound architecture proposed
> here introduced novelty (a new bound type generalizing `PolyBound`)
> not present in the published K^sim_2 ⊆ ER proof.  Adversarial
> review identified the resulting `Nat.tower_iter_tower_bound` as
> mathematically false at non-zero step heights.  Re-reading the
> research doc (`docs/research/2026-04-30-ksim-polynomial-bound-references.md`)
> confirmed the published proof (Recursion Class Ch. 4 Prop. 4.7,
> n=2 case) routes through polynomial bounds on level-1 K^sim
> children combined with the existing `polynomial_iter_tower_bound`,
> not a new bound type.  The correct level-2 dominance proof is a
> structural mirror of the existing `kSimTowerBound_dominates_level_one`
> (`LawvereKSimPolynomialBound.lean:2578`); see plan v4 at
> `docs/plans/2026-05-02-ksim-tower-bound-dominates-inline-plan.md`.
>
> This document is preserved as a record of the design exploration.
> The PolyBound ↔ TowerBound injection idea remains valid as a
> general structural observation but is not load-bearing for the
> current scope.

## Context and motivation

The Phase IV-B headline theorem `kSimTowerBound_dominates_inline`
expresses that the level-2 K^sim simrec's iterated packed step is
dominated by `kSimTowerBound`'s closed-form tower expression at every
iteration counter and parameter context.  It is the load-bearing
dependency for kToER Tasks 14-22 (the `KSimCat 2 ⥤ ERCat` functor and
its laws).

Two prior plans (v1 and v2) proposed discharging this theorem via a
recursive `kToER_polyBound_of_level_one` builder producing
`ERMor1.PolyBound` instances.  Adversarial review during implementation
of plan v2 identified a structural impossibility:

- `ERMor1.PolyBound f` carries fields `(degree d, coefficient c,
  constant k)` and asserts `f.interp ctx ≤ c · (maxCtx ctx + 1)^d + k`
  (polynomial in `maxCtx ctx`).
- `ERMor1.expER.interp ctx = (ctx 1)^(ctx 0)` (verified in
  `LawvereERArith.lean:25-43`); setting `ctx 0 = ctx 1 = n` yields
  `n^n`, super-polynomial in `maxCtx ctx`.
- `ERMor1.towerER k` for `k ≥ 1` is super-exponential.
- `kSimTowerBound = iterAutoBoundExpr a stepTH baseTH` involves
  `towerER`; therefore `PolyBound (kSimTowerBound h_ER g_ER)` is
  uninhabited.

`kToER`'s simrec case (`LawvereKSimER.lean:58-93`) translates a
`KMor1.simrec` to a `comp (kSimSzudzikUnpackAt) (boundedRec
(kSimPackedBase) (kSimPackedStep) (kSimTowerBound))`; building a
`PolyBound` on this comp via `ERMor1.PolyBound.ofBoundedRec` requires a
`PolyBound` on the bound argument (`kSimTowerBound`), which does not
exist.

The `LawvereKSimPolynomialBound.lean` module docstring (lines 27-47)
documents that the original `Poly Task 15` (the recursive
`kToER_polyBound_of_level_one` bridge) was deferred for exactly this
reason.  Plan v2 re-introduced the bridge and the audit failed to
recognize the contradiction.

This spec proposes a `TowerBound` architecture that:

- generalizes `PolyBound` to admit tower-shaped majorants;
- preserves all landed `PolyBound` infrastructure (17 builders + the
  packed bound apparatus + 10 D.0.A atomic builders) via a definitional
  injection from `PolyBound` to `TowerBound`;
- supports a recursive `kToER_towerBound_of_level_one` bridge whose
  simrec case produces a `TowerBound` at height 2 (rather than an
  uninhabited `PolyBound`);
- closes the headline `kSimTowerBound_dominates_inline` chain.

## Scope

`K^sim_2 = ER` is the categorical equivalence formalized by this
project.  K^sim_d for d ≥ 3 lies outside ER (in PR), so the TowerBound
architecture is permanently scoped to `f.level ≤ 2`.  The design does
not anticipate level-3 extensions.

## Architecture

### §1. The TowerBound type

```lean
namespace ERMor1

/-- A polynomial-times-tower bound on an `ERMor1`'s interpretation:
`f.interp ctx ≤ tower towerHeight (coefficient · (maxCtx ctx + 1)^degree
+ constant)`.

`PolyBound f` is exactly `TowerBound f` at `towerHeight = 0` (since
`tower 0 x = x` by `tower_zero`); the injection is definitional. -/
structure TowerBound {n : ℕ} (f : ERMor1 n) where
  towerHeight : ℕ
  degree      : ℕ
  coefficient : ℕ
  constant    : ℕ
  bounds : ∀ ctx,
    f.interp ctx ≤
      GebLean.tower towerHeight
        (coefficient * (maxCtx ctx + 1) ^ degree + constant)

end ERMor1
```

Definitional fact: `TowerBound f` at `towerHeight = 0` is exactly the
`PolyBound f` shape, because `GebLean.tower 0 x = x` is the
`@[simp] theorem tower_zero` (`Utilities/Tower.lean:21`).

### §2. PolyBound ↔ TowerBound conversion

```lean
namespace ERMor1.TowerBound

/-- Lift any `PolyBound` to `TowerBound` at height 0.  Preserves all
fields (degree, coefficient, constant); the bounds proof goes through
since `tower 0 = id`. -/
def ofPolyBound {n : ℕ} {f : ERMor1 n}
    (pb : PolyBound f) : TowerBound f where
  towerHeight := 0
  degree      := pb.degree
  coefficient := pb.coefficient
  constant    := pb.constant
  bounds := fun ctx => by
    rw [GebLean.tower_zero]
    exact pb.bounds ctx

/-- Convert a `TowerBound` of height 0 back to `PolyBound`.  This and
`ofPolyBound` make the two types equivalent at height 0 (no information
loss either direction). -/
def toPolyBound {n : ℕ} {f : ERMor1 n}
    (tb : TowerBound f) (h_zero : tb.towerHeight = 0) :
    PolyBound f where
  degree      := tb.degree
  coefficient := tb.coefficient
  constant    := tb.constant
  bounds := fun ctx => by
    have hb := tb.bounds ctx
    rw [h_zero, GebLean.tower_zero] at hb
    exact hb

/-- Lift a `TowerBound` to a higher tower height.  Used to harmonize
heights across siblings in `ofComp` and similar combinators. -/
def liftHeight {n : ℕ} {f : ERMor1 n}
    (tb : TowerBound f) (extra : ℕ) : TowerBound f where
  towerHeight := tb.towerHeight + extra
  degree      := tb.degree
  coefficient := tb.coefficient
  constant    := tb.constant
  bounds := fun ctx => by
    have hb := tb.bounds ctx
    -- tower (h + extra) X ≥ tower h X by tower monotonicity in
    -- height (`Utilities/Tower.lean:65` `tower_mono_left`).
    _

end ERMor1.TowerBound
```

The `liftHeight` operation is needed because `ofComp_tower` must
combine `TowerBound`s of differing heights into a uniform-height result;
the natural way is to lift each sibling to the maximum height before
combining.

### §3. TowerBound builders

In `GebLean/LawvereERPolynomialBound.lean` (or a new sibling
`LawvereERTowerBound.lean` if the module size warrants split):

#### §3.a Composition

```lean
/-- TowerBound for `comp f gs`.  Heights add: if `f` has height `h_f`
and each `g i` has height ≤ `h_g`, then `comp f gs` has height
`h_f + h_g`.  Justified by `tower_comp` (`Utilities/Tower.lean:51`):
`tower (h_f + h_g) x = tower h_f (tower h_g x)`.  Polynomial degree,
coefficient, and constant fields combine analogously to
`PolyBound.ofComp` (`LawvereERPolynomialBound.lean:180`). -/
def TowerBound.ofComp {k n : ℕ} {f : ERMor1 k}
    {g : Fin k → ERMor1 n}
    (tb_f : TowerBound f)
    (tb_g : (i : Fin k) → TowerBound (g i)) :
    TowerBound (ERMor1.comp f g) := ...
```

When all `tb_g i` and `tb_f` have height 0, this specializes to
`PolyBound.ofComp` lifted via `ofPolyBound`.

#### §3.b Bounded recursion

```lean
/-- TowerBound for `boundedRec base step bound`.  Output is bounded by
`bound`'s interp (the existing `interp_boundedRec_le_bound` lemma), so
the TowerBound on the wrapped `boundedRec` equals the TowerBound on
`bound`.  Crucially, `bound` may now have ARBITRARY tower height
(plan v2's blocker was that this required `PolyBound bound`, which did
not exist for `kSimTowerBound`). -/
def TowerBound.ofBoundedRec {k : ℕ} {base : ERMor1 k}
    {step : ERMor1 (k + 2)} {bound : ERMor1 (k + 1)}
    (tb_bound : TowerBound bound) :
    TowerBound (ERMor1.boundedRec base step bound) where
  towerHeight := tb_bound.towerHeight
  degree      := tb_bound.degree
  coefficient := tb_bound.coefficient
  constant    := tb_bound.constant
  bounds := fun ctx =>
    le_trans
      (ERMor1.interp_boundedRec_le_bound base step bound ctx)
      (tb_bound.bounds ctx)
```

This is the load-bearing fix vs. plan v2.

#### §3.c Atomic tower-bumping builders

`PolyBound`-impossible atoms become buildable as `TowerBound` at
non-zero height:

- `TowerBound.ofExpER` — height 1.  `expER.interp ctx = (ctx 1)^(ctx 0)`,
  bounded by `2^(maxCtx · log_2(maxCtx) + 1) ≤ tower 1 (linear in
  maxCtx)`.
- `TowerBound.ofTowerER (k : ℕ)` — height `k + 1` (or `k`; settled by
  the chain).  `towerER k.interp` is a tower of fixed height `k`
  applied to the input; lifts to a `TowerBound` at height `k + 1` by
  the standard `tower_succ` algebra.
- `TowerBound.ofBprod` — optional, only if a use site needs it.  The
  `bprod` constructor is parallel to `bsum` but multiplicative; its
  bound is `tower 1 (linear)`-shaped.

### §4. Generalized chain primitives

#### §4.a Tower-iterated step bound

In `GebLean/Utilities/ComputationalComplexity.lean`:

```lean
/-- Generalization of `polynomial_iter_tower_bound` to a tower-bounded
step.  When `step v x ≤ tower h_step ((max v x + 1)^D)` and `j` is
bounded by some context-derived linear quantity, the j-iterated step
starting from a tower-h_base-bounded base satisfies a tower bound of
height `max h_step h_base + c_iter` (where `c_iter` is the constant
height bump introduced by iteration; consistent with the existing
`polynomial_iter_tower_bound`'s height-2 output for all-polynomial
inputs, the bump is `c_iter = 2`).  The polynomial degree is
absorbed into the linear inside. -/
theorem Nat.tower_iter_tower_bound
    (step : ℕ → ℕ → ℕ) (h_step D : ℕ)
    (h_step_form : ∀ v x, step v x ≤
      GebLean.tower h_step ((max v x + 1) ^ D))
    (v_0 : ℕ → ℕ) (h_base D_base : ℕ)
    (h_base_form : ∀ x, v_0 x ≤
      GebLean.tower h_base ((x + 1) ^ D_base))
    (j x : ℕ) :
    Nat.iterate (fun v => step v x) j (v_0 x) ≤
      GebLean.tower (max h_step h_base + 2)
        ((Nat.log 2 D + Nat.log 2 D_base + 2) * (j + 1) +
         x + 2) := _
```

The exact constants in the linear-inside are settled by the proof.
The boundedness of `j` (via the dominance hypothesis
`j ≤ kSimTowerBound.interp`) is what closes the chain inside the
headline; this lemma's job is to give the right tower-height-bumped
output for tower-bounded inputs.

When `h_step = h_base = 0`, this lemma reduces to the existing
`polynomial_iter_tower_bound` (output height 2, matching the existing
behavior).

#### §4.b TowerBound chain adapters

In `LawvereERPolynomialBound.lean` (or sibling), parallel to
`PolyBound.to_iter_step_form` (line 503) and `log_le_towerHeight`
(Poly Task 9):

- `TowerBound.to_iter_step_form` — TowerBound → single-power form
  `tower towerHeight ((max v x sp + 2) ^ (degree + log
  (coefficient + 1) + log (constant + 1) + 3))`.  Subsumes both
  `to_iter_step_form` (Poly Task 10) and the would-be sharper
  `to_iter_step_form_log` (plan v2's D.0.B).
- `TowerBound.log_le_towerHeight` — analog of `PolyBound.log_le_towerHeight`
  (Poly Task 9), now accounting for the `towerHeight` field.

### §5. K^sim-side replumbing

In `GebLean/LawvereKSimPolynomialBound.lean`, parallel to existing
`kSimPackedBase_polyBound` (line 738) and `kSimPackedStep_polyBound`
(line 817):

```lean
/-- TowerBound for the packed simrec base, taking per-l TowerBounds
on the level-≤-1 K^sim children's ER translations.  Output height is
the maximum of input heights (the packed-base ER term is itself a
polynomial expression in the children, no height bump). -/
def kSimPackedBase_towerBound {a k : ℕ}
    (h_ER : Fin (k + 1) → ERMor1 a)
    (tb_h : (l : Fin (k + 1)) → ERMor1.TowerBound (h_ER l)) :
    ERMor1.TowerBound (kSimPackedBase h_ER) := ...

/-- Analogous to kSimPackedBase_towerBound, on the packed step. -/
def kSimPackedStep_towerBound {a k : ℕ}
    (g_ER : Fin (k + 1) → ERMor1 (a + 1 + (k + 1)))
    (tb_g : (l : Fin (k + 1)) → ERMor1.TowerBound (g_ER l)) :
    ERMor1.TowerBound (kSimPackedStep g_ER) := ...
```

Existing `kSimPackedBase_polyBound` / `kSimPackedStep_polyBound` are
retained unchanged.  When all input children have PolyBounds, the
TowerBound output specializes (via height-0 injection) to the existing
PolyBound output.

### §6. Recursive bridge

```lean
/-- Recursive TowerBound builder for level-≤-1 K^sim translations.
At level 0 (atomic / comp / raise / no top-level simrec) produces a
height-0 TowerBound (i.e., a PolyBound).  At top-level simrec of
level-0 children, produces a height-2 TowerBound via the
`polynomial_iter_tower_bound` chain on the level-0 children's
PolyBounds.

Used by `kSimTowerBound_dominates_inline` (D.5) to feed
`kSimPackedBase_towerBound` and `kSimPackedStep_towerBound` with per-l
TowerBounds for the headline assembly. -/
def KMor1.kToER_towerBound_of_level_one :
    {a : ℕ} → (f : KMor1 a) → (h : f.level ≤ 1) →
    ERMor1.TowerBound (kToER f (Nat.le_succ_of_le h))
  | _, .zero,         _ =>
      .ofPolyBound (.ofZeroN _)
  | _, .succ,         _ =>
      .ofPolyBound .ofSucc
  | _, .proj _,       _ =>
      .ofPolyBound (.ofProj _)
  | _, .comp f gs,    h =>
      ERMor1.TowerBound.ofComp
        (kToER_towerBound_of_level_one f ...)
        (fun i => kToER_towerBound_of_level_one (gs i) ...)
  | _, .raise f,      h =>
      kToER_towerBound_of_level_one f ...
  | _, .simrec h_lvl0 g_lvl0 i, h =>
      -- Level-0 children → PolyBound on each kToER child via
      -- inline structural construction.
      -- → kSimPackedBase_polyBound / kSimPackedStep_polyBound
      --   (existing infrastructure, used at height 0).
      -- → polynomial_iter_tower_bound (existing, height 0 → 2).
      -- → wrap as TowerBound of comp(kSimSzudzikUnpackAt,
      --   boundedRec ...).
      -- Resulting height: 2.
      ...
```

The simrec case's inner construction reuses **existing** infrastructure
(`kSimPackedBase_polyBound`, `kSimPackedStep_polyBound`,
`polynomial_iter_tower_bound`) — no new tower-iter-tower lemma is
required at this level, because the children are level 0
(polynomially bounded).

### §7. Headline theorem

```lean
/-- Phase IV-B headline: level-2 simrec dominance via the polynomial-
iteration chain through TowerBound.  The iterated packed value of
`kSimPackedStep` over `kSimPackedBase` is dominated by
`kSimTowerBound`'s closed-form tower at every iteration counter and
parameter context, when both base and step families consist of
level-≤-1 K^sim terms.

Replaces the impossible PolyBound-based formulation of plan v2.

Used by `kToER_interp` at level ≤ 2 (kToER plan Task 14). -/
theorem kSimTowerBound_dominates_inline {a k : ℕ}
    (h_fam : Fin (k + 1) → KMor1 a)
    (g_fam : Fin (k + 1) → KMor1 (a + 1 + (k + 1)))
    (h_h : ∀ l, (h_fam l).level ≤ 1)
    (h_g : ∀ l, (g_fam l).level ≤ 1)
    (j : ℕ) (params : Fin a → ℕ) :
    Nat.rec
      ((kSimPackedBase
        (fun l => kToER (h_fam l)
          (Nat.le_succ_of_le (h_h l)))).interp params)
      (fun i prev =>
        (kSimPackedStep
          (fun l => kToER (g_fam l)
            (Nat.le_succ_of_le (h_g l)))).interp
        (Fin.cons i (Fin.cons prev params)))
      j ≤
      (kSimTowerBound
        (fun l => kToER (h_fam l)
          (Nat.le_succ_of_le (h_h l)))
        (fun l => kToER (g_fam l)
          (Nat.le_succ_of_le (h_g l)))).interp
        (Fin.cons j params)
```

Proof structure mirrors level-1's `kSimTowerBound_dominates_level_one`
(`LawvereKSimPolynomialBound.lean:2578`):

1. Build per-l TowerBounds via `kToER_towerBound_of_level_one`
   (yields heights ≤ 2 — height 0 if the child is atomic/comp/raise,
   height 2 if the child is a top-level simrec at level 1).
2. Build packed TowerBounds via `kSimPackedBase_towerBound` /
   `kSimPackedStep_towerBound` (output heights at the max of input
   heights, ≤ 2).
3. Apply `TowerBound.to_iter_step_form` to convert to single-power
   form.
4. Apply `Nat.tower_iter_tower_bound` to bound the j-iterated trace
   by `tower (max(h_step, h_base) + 2) (linear)` — i.e., at most
   `tower 4 (linear)` when both inputs are at maximum height 2.
5. Bump to `tower (stepTH + 1)` via `tower_mono_left` (using
   `kSimPackedStep_towerHeight_ge_succ_k` plus an analogous tH lower
   bound that accounts for the increased input heights).
6. Absorb the linear argument into `kSimTowerBound.interp`'s closed
   form via `tower_mono_right` and the chain-closing log-vs-tH
   lemma (level-2 analog of plan v2's D.3.2, now using
   `TowerBound.log_le_towerHeight`).

### §8. Salvage of D.0.A's 10 landed builders

All 10 `PolyBound` builders landed at commits `5e25b66f` and
`cfc19369` (Task 17c D.0.A.2 and D.0.A.3) remain in place unchanged.
They lift to `TowerBound` at height 0 via `ofPolyBound` with zero
modification.  No commits revert.

The deferred `ofExpER` / `ofTowerER` / `ofBprod` from plan v2's D.0.A
are reborn as `TowerBound` builders at non-zero heights, addressing
the original mathematical impossibility.

## File organization

- `GebLean/Utilities/ComputationalComplexity.lean` — add
  `Nat.tower_iter_tower_bound`.
- `GebLean/LawvereERPolynomialBound.lean` — add `TowerBound` type,
  injection from PolyBound, builders for `ofComp`, `ofBoundedRec`,
  `ofExpER`, `ofTowerER`, `ofBprod`; chain adapters
  `to_iter_step_form` and `log_le_towerHeight` for TowerBound.
  (If size grows beyond ~1000 lines, split into sibling
  `LawvereERTowerBound.lean`.)
- `GebLean/LawvereKSimPolynomialBound.lean` — add
  `kSimPackedBase_towerBound`, `kSimPackedStep_towerBound`,
  `KMor1.kToER_towerBound_of_level_one`, headline theorem
  `kSimTowerBound_dominates_inline`.

## Testing

- `#guard` tests for `TowerBound.ofPolyBound` round-tripping a
  PolyBound.
- `#guard` tests for `TowerBound.ofExpER` and `TowerBound.ofTowerER`
  at small heights.
- `#guard` test for `kToER_towerBound_of_level_one` on `KMor1.addK`
  (the level-1 simrec witness used by existing tests).
- `#guard` for the headline at a level-2 witness (e.g., a nested-simrec
  test or an `addK²` analog if one is in scope).

Existing PolyBound tests stay unchanged.

## Estimated effort

| Component | Lines |
|---|---|
| TowerBound type + injection + liftHeight | 50 |
| TowerBound builders (ofComp, ofBoundedRec, ofExpER, ofTowerER) | 250 |
| TowerBound chain adapters (to_iter_step_form, log_le_towerHeight) | 200 |
| Nat.tower_iter_tower_bound | 200 |
| kSimPackedBase_towerBound + kSimPackedStep_towerBound | 200 |
| kToER_towerBound_of_level_one | 200 |
| kSimTowerBound_dominates_inline (headline) | 250 |
| Tests | 50 |
| **Total** | **~1400** |

This is comparable to plan v2's estimate (~700-1200), with the extra
~200-300 lines being the new TowerBound type, builders, and
`tower_iter_tower_bound`.  No PolyBound infrastructure is removed or
rewritten.

## Out-of-scope

- Generalizing the existing `kSimPackedBase_polyBound` /
  `kSimPackedStep_polyBound` in-place to TowerBound.  The PolyBound
  versions stay; the TowerBound versions are added in parallel.
- K^sim_d for d ≥ 3.  These leave ER and belong to a separate
  PR-targeted project.
- A `MonoidalClosed` or category-theoretic abstraction over TowerBound.
  TowerBound is a proof-engineering convenience, not a mathematical
  object.

## Mathematical justification

K^sim_d ⊆ ER (Tourlakis 2018 §0.1.0.27; Wagner-Wong; Grzegorczyk
hierarchy).  At level d, K^sim functions are bounded by tower of
fixed height O(d) applied to a polynomial in the inputs.  TowerBound's
shape `tower towerHeight (coefficient · (maxCtx + 1)^degree + constant)`
captures exactly this growth class.  The recursive bridge
`kToER_towerBound_of_level_one` exhibits, for every level-≤-1 K^sim
term, a witness of this bound; the headline theorem composes such
witnesses across the level-2 simrec to land in `kSimTowerBound`'s
closed form.

The mathematical content is unchanged from plan v2; only the bound
type used to express it is generalized.
