# ER polynomial-bound infrastructure: design

## Status

Design document for the polynomial-bound infrastructure
sub-project, a prerequisite of the K^sim → ER forward
translation's interp-preservation theorem.

**Amendment (2026-04-30, second)**: after Tasks 1–16 of
the implementation plan landed, Task 17
(`kSimTowerBound_dominates_inline`) was found to require
a recursive bootstrap by K^sim level (matching Tourlakis
CN §4.2.2's induction-on-n structure for K^sim_n closure
proofs).  See the implementation plan at
`docs/plans/2026-04-30-er-polynomial-bound-plan.md`,
"Plan amendment (2026-04-30, second)" section, for the
revised three-task structure (Tasks 17a/17b/17c).
The design's Module C contents below are unchanged in
spirit — the dominance assembly at the level-2 case (the
original Task 17 deliverable) is now Task 17c, building
on Tasks 17a (level 0) and 17b (level 1) per the
literature.

## Scope

Three new Lean modules establish:

1. Generic Nat-arithmetic primitives for polynomial and
   tower bounds (`Utilities/ComputationalComplexity.lean`).
2. ER-side polynomial-bound predicate and the structural
   `towerHeight` lemma (`LawvereERPolynomialBound.lean`).
3. K^sim-side linear-bound for level-1 K^sim
   (`LawvereKSimPolynomialBound.lean`), and the dominance
   assembly that discharges `boundedRec_eq_natRec_of_bounded`
   for the simrec case of `kToER_interp`.

The deliverable is the dominance witness needed by Task
14 of the kToER plan (`docs/plans/2026-04-29-lawvere-k-sim-ktoer-plan.md`).

## References

- `docs/research/2026-04-30-ksim-polynomial-bound-references.md`
  — research document with literature citations for the
  seven sub-claims.
- `docs/plans/2026-04-29-lawvere-k-sim-ktoer-plan.md` —
  parent kToER plan; this sub-project is a prerequisite
  of its Task 14.
- Tourlakis 2018, Tourlakis CN, Damnjanovic 1994,
  Recursion Class Ch. 4 (per research doc).

### Related concepts

The Lean construction uses simultaneous primitive
recursion (Tourlakis CN Theorem 4.2.2's "Hilbert–Bernays
reduction") encoded via Szudzik pairing (project plan
§2.3.1).  This is the **fixed-arity** version: step reads
the (k+1)-vector at the previous iteration.

A related but distinct operation is **course-of-values
recursion** (PlanetMath:
`https://planetmath.org/courseofvaluesrecursion`), where
the step reads the entire prior trace as a growing
sequence encoded via Gödel multiplicative coding.  Our
infrastructure does not implement course-of-values
recursion; the `Nat.seqPack` / `Nat.seqAt` primitives in
`Utilities/SzudzikSeq.lean` are sequence-encoding tools
common to both notions, but our use is for fixed-length
vector packing (simultaneous PR), not for growing-trace
encoding (course-of-values).

## Architecture

Three Lean modules organized bottom-up by dependency.

### Module A — `GebLean/Utilities/ComputationalComplexity.lean`

**Purpose**: generic Nat-arithmetic primitives for
polynomial bounds and tower bounds.  No `ERMor1` /
`KMor1` references.

**Contents**:

- `Nat.pair_le_sq` — mathlib `Nat.pair x y ≤ (x + y + 1)^2`.
  FOLKLORE 1 from research doc.
- `Nat.seqPackBound` (closed-form `(m + 1)^D`-style upper
  bound on `Nat.seqPack`) and the dominance lemma.
- Polynomial-iter analytic lemma:

  ```lean
  theorem Nat.polynomial_iter_tower_two_bound
      (step : ℕ → ℕ → ℕ) (D m : ℕ)
      (h_step : ∀ v x, step v x ≤ (max v x + 1) ^ D)
      (v_0 : ℕ → ℕ) (h_base : ∀ x, v_0 x ≤ m * x + m)
      (j x : ℕ) :
      Nat.iterate (step · x) j (v_0 x) ≤
        tower 2 (m_step * j + m * x + m_step + m)
    where m_step := Nat.log 2 D + 1
  ```

  Uses `tower h x = 2^(2^...^x)` (h twos applied to x)
  from `Utilities/Tower.lean`.

### Module B — `GebLean/LawvereERPolynomialBound.lean`

**Purpose**: ER-side polynomial-bound predicate and the
structural `towerHeight` lemma.  References `ERMor1` but
not `KMor1`.

**Contents**:

- `ERMor1.PolyBound` data-bearing structure (no Setoid
  wrapper):

  ```lean
  structure ERMor1.PolyBound (f : ERMor1 n) where
    degree : ℕ
    bounds : ∀ ctx, f.interp ctx ≤ (max ctx + 1) ^ degree
  ```

- Structural `towerHeight` lemma (FOLKLORE 4 from research
  doc):

  ```lean
  theorem ERMor1.PolyBound.log_le_towerHeight {f : ERMor1 n}
      (pb : PolyBound f) :
      Nat.log 2 pb.degree ≤ f.towerHeight
  ```

- Adapter from `PolyBound` to Module A's polynomial-iter
  step shape: given a `PolyBound` on a `(k+2)`-arity ER
  term (i.e. with the right shape for `boundedRec`'s
  step), exhibit the polynomial-iter input.

### Module C — `GebLean/LawvereKSimPolynomialBound.lean`

**Purpose**: K^sim-side proofs.  References both `KMor1`
and `ERMor1`.

**Contents**:

- `ConstantOrShiftedProj : ℕ → Type` inductive (Lemma 1.B's
  shape):

  ```lean
  inductive ConstantOrShiftedProj : ℕ → Type
    | const   {a : ℕ} (k : ℕ) : ConstantOrShiftedProj a
    | shifted {a : ℕ} (i : Fin a) (k : ℕ) :
        ConstantOrShiftedProj a

  def ConstantOrShiftedProj.interp :
      ConstantOrShiftedProj a → (Fin a → ℕ) → ℕ
    | .const k,        _   => k
    | .shifted i k,    ctx => ctx i + k
  ```

- Lemma 1.B (`KMor1.level0Shape`):

  ```lean
  def KMor1.level0Shape :
      (f : KMor1 a) → f.level ≤ 0 → ConstantOrShiftedProj a

  theorem KMor1.level0Shape_interp (f : KMor1 a)
      (h : f.level ≤ 0) (ctx : Fin a → ℕ) :
      f.interp ctx = (KMor1.level0Shape f h).interp ctx
  ```

- Lemma 1.A (`KMor1.linearBound`):

  ```lean
  def KMor1.linearBound :
      (f : KMor1 a) → f.level ≤ 1 → ℕ × ℕ

  theorem KMor1.linearBound_dominates (f : KMor1 a)
      (h : f.level ≤ 1) (ctx : Fin a → ℕ) :
      f.interp ctx ≤
        (KMor1.linearBound f h).1 *
          (Finset.univ : Finset (Fin a)).sup ctx +
        (KMor1.linearBound f h).2
  ```

- Bridge: level-1 K^sim's `kToER` image has a `PolyBound`:

  ```lean
  def kToER_polyBound_of_level_one
      (f : KMor1 a) (h : f.level ≤ 1) :
      PolyBound (kToER f (Nat.le_succ_of_le h))
  ```

- Specialization to `kSimPackedStep` (degree
  `D_step = 2^k * D_g` per research doc).

- Final dominance assembly:

  ```lean
  theorem kSimTowerBound_dominates_inline {a k : ℕ}
      (h_fam : Fin (k+1) → KMor1 a)
      (g_fam : Fin (k+1) → KMor1 (a + 1 + (k+1)))
      (h_h : ∀ j, (h_fam j).level ≤ 1)
      (h_g : ∀ j, (g_fam j).level ≤ 1)
      (j : ℕ) (params : Fin a → ℕ) (h_j : j ≤ params 0) :
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
        (kSimTowerBound _ _).interp
          (Fin.cons j params)
  ```

Module C also exports a `boundedRec_eq_natRec_of_bounded`
adapter that combines `kSimTowerBound_dominates_inline`
with `kSimTowerBound_mono_counter` (already in
`Utilities/KSimSzudzikSimrec.lean`) into the form
expected by Task 14 of the kToER plan.

### Integration in `LawvereKSimER.lean`

Task 14 of the kToER plan (`kToER_interp`'s simrec case)
becomes:

```lean
  | _, .simrec (a := a) (k := k) i h_fam g_fam, hyp, ctx => by
      have hh : ∀ j, (h_fam j).level ≤ 1 := …
      have hg : ∀ j, (g_fam j).level ≤ 1 := …
      have h_dom := kSimTowerBound_dominates_inline
        h_fam g_fam hh hg (ctx 0)
        (fun j => ctx (Fin.succ j)) (Nat.le_refl _)
      have h_mono := kSimTowerBound_mono_counter
        (fun l => kToER (h_fam l) _)
        (fun l => kToER (g_fam l) _)
        … …
      simp only [kToER, ERMor1.interp_comp]
      rw [boundedRec_eq_natRec_of_bounded
        … h_dom h_mono]
      -- ... matches Nat.rec to KMor1.simrecVec via
      -- kSimPackedBase_interp / kSimPackedStep_interp +
      -- recursive interp hypotheses
      …
      rw [kSimSzudzikUnpackAt_packList]
      rfl
```

## Components and data flow

### Module A: `Utilities/ComputationalComplexity.lean`

**`Nat.pair_le_sq`** (FOLKLORE 1).  Proof by case
analysis on `x < y`.  ~5 lines.

**`Nat.seqPackBound`**.  Closed form `(max + 1)^D` for a
list whose components are bounded by `(max + 1)^d_i`
with `D ≥ 2^k * max d_i`.  Uses `Nat.pair_le_sq` per
list element.  ~30 lines.

**`Nat.polynomial_iter_tower_two_bound`** (Module A's
main result, deriving from research doc Claim 4).
Pseudocode:

```text
By induction on j:
  j = 0: Nat.iterate step 0 (v_0 x) = v_0 x ≤ m * x + m
         ≤ tower 2 (linear) since m * x + m ≤ tower 2 (linear).
  j = j' + 1: by IH, prev ≤ tower 2 (m_step * j' + m * x + ...)
         step prev x ≤ (max prev x + 1)^D
                     ≤ (tower 2 (m_step * j' + ...) + 1)^D
                     ≤ tower 2 (m_step * j + m * x + ...)
         using tower-arithmetic: (tower 2 X + 1)^D ≤ tower 2 (X + log_2 D + 1)
         which is the inequality e_3(X+1) ≥ (e_2(X) + 1)^D for D ≤ 2^...
```

The closing inequality `(tower 2 X + 1)^D ≤ tower 2 (X + log_2 D + 1)`
is the heart.  Needs to be proven using tower
properties from `Utilities/Tower.lean`.  ~80 lines.

### Module B: `LawvereERPolynomialBound.lean`

**`ERMor1.PolyBound`**.  Structure with two fields.
Trivial to define.  ~10 lines.

**`ERMor1.PolyBound.log_le_towerHeight`** (FOLKLORE 4).
Approach: structural induction on `f : ERMor1 n`.

Pseudocode:

```text
Read ERMor1.towerHeight's definition first
(in GebLean/LawvereERBoundComputable.lean line 34).

For each ER constructor (zero, succ, proj, sub, comp,
bsum, bprod):
  - Compute structural towerHeight per constructor.
  - Compute the polynomial degree of f.interp per
    constructor (as a function of children's degrees).
  - Show that towerHeight ≥ Nat.log 2 (degree).

Cases:
  zero, succ, proj: towerHeight = 0; their interp is
    degree-0 polynomial (i.e. linear, possibly constant).
    Nat.log 2 1 = 0 ≤ 0. ✓
  sub: towerHeight = 0; degree of sub is 1 (linear).
    Nat.log 2 1 = 0 ≤ 0. ✓
  comp f g: towerHeight = max towerHeight f, towerHeight g.
    Degree of (comp f g).interp ≤ degree(f) * max degree(g_i).
    Use Nat.log 2 (a * b) ≤ Nat.log 2 a + Nat.log 2 b.
    By IH, the towerHeights bound each log; max bounds the
    sum since max(a,b) ≥ (a + b) / 2 plus log-subadditivity.
    Specifically: max_i (log) ≤ log of max_i
    ≤ Nat.log 2 (a * b) via the multiplicative log bound.
    The arithmetic of this case is delicate; the
    implementation plan should reverify before committing.
  bsum f, bprod f: towerHeight = towerHeight f + 1.
    bsum/bprod produce values bounded polynomially of
    degree degree f + 1 (very rough; bsum sums up to
    bound, multiplying by degree-1 sum factor).
    Nat.log 2 (degree f + 1) ≤ towerHeight f + 1.

Estimated: 60-100 lines, including auxiliary degree-
of-comp and degree-of-bsum lemmas.
```

**`ERMor1.PolyBound.to_iter_step_form`**.  Adapter
turning a `PolyBound` on a `(k+2)`-arity ER term into
the polynomial-iter step form Module A consumes.
~20 lines.

### Module C: `LawvereKSimPolynomialBound.lean`

**`ConstantOrShiftedProj`**.  Two-constructor inductive.
Trivial.  ~15 lines.

**`KMor1.level0Shape`** (Lemma 1.B).  Pseudocode (from
research doc):

```text
Structural recursion on f : KMor1 a with f.level ≤ 0.
  zero:    .const 0
  succ:    .shifted 0 1
  proj i:  .shifted i 0
  comp f gs:
    let g_shape := level0Shape f (...)
    match g_shape with
    | .const k_g     => .const k_g
        -- result is independent of gs; substitution
        -- of constants doesn't change.
    | .shifted i k_g =>
        -- look up the i-th element of gs, recurse
        let gs_i_shape := level0Shape (gs i) (...)
        match gs_i_shape with
        | .const c          => .const (c + k_g)
        | .shifted j k_gs   => .shifted j (k_gs + k_g)
  raise / simrec: impossible at level 0
```

Estimated: 30 lines for the def + 30 lines for the
interp-equality theorem.

**`KMor1.linearBound`** (Lemma 1.A).  Pseudocode (using
Lemma 1.B as helper):

```text
Structural recursion on f : KMor1 a with f.level ≤ 1.
  zero:    (0, 0)
  succ:    (1, 1)
  proj i:  (1, 0)
  comp f gs:
    let (c_g, k_g) := linearBound f (Nat.max_le.mp _).1
    -- max over gs's multipliers, dotted with c_g
    let cs := List.ofFn (fun i => (linearBound (gs i) _).1)
    let ks := List.ofFn (fun i => (linearBound (gs i) _).2)
    let c := c_g * (cs.maximum?.getD 0)
    let k := c_g * (ks.sum) + k_g
    (c, k)
  raise f:
    -- f.level ≤ 0; use level0Shape
    let s := level0Shape f (le_of_le_succ _)
    (s.linearBound)
    where ConstantOrShiftedProj.linearBound :
      | .const k       => (0, k)
      | .shifted _ k   => (1, k)
  simrec i h_fam g_fam:
    -- All h_l, g_l are level 0 ⇒ ConstantOrShiftedProj
    -- The simrec at iter j for output l can grow at
    -- most by max-step-constant per iteration.
    let h_shapes := Fin.map (fun l => level0Shape (h_fam l) _) ...
    let g_shapes := Fin.map (fun l => level0Shape (g_fam l) _) ...
    let baseConsts := h_shapes.toList.map ...
    let stepConsts := g_shapes.toList.map ...
    let c := 1 + (k+1) * (max stepConsts)
    let k := (max baseConsts) + (k+1) * (max stepConsts)
    -- (Conservative; per Question 8 (i)-α.)
    (c, k)
```

Estimated: 80–150 lines for def + dominance proof,
including all six structural cases.  The simrec case
is the trickiest.

**`kToER_polyBound_of_level_one`**.  Bridges Lemma 1.A's
`(c, k) : ℕ × ℕ` to a `PolyBound (kToER f h)`:

```text
Given (c, k) = linearBound f h_lvl,
  ∀ ctx, (kToER f _).interp ctx
       = f.interp ctx                      -- by kToER_interp
       ≤ c * sum ctx + k                   -- by linearBound_dominates
       ≤ (c + k) * (max ctx + 1)^1          -- raise to polynomial form
Set degree = 1 and adjust constants.
```

**Circularity warning**: we cannot use `kToER_interp`
here because it is not yet proven (it is what Task 14 of
the kToER plan proves, which DEPENDS on this).
Resolution: prove `kToER_polyBound_of_level_one`
**directly** by structural induction on `f`, paralleling
`KMor1.linearBound` but producing an `ERMor1`-side bound.
This avoids circularity.

Estimated: 50 lines.

**`kSimPackedStep_polyBound`**.  Combines per-component
`kToER_polyBound_of_level_one` of each `g_l` with the
`Nat.seqPack`-bound from Module A:

```text
Each kToER (g_l) has PolyBound with degree ≤ 1
  (since each g_l is level ≤ 1, hence linear).
seqPack of (k+1) such bounds has degree at most
  D_pack(k) = 2^k * 1 = 2^k.
The kSimStepContext substitution doesn't change the
overall polynomial degree of the composite (it just
re-indexes inputs).
So the kSimPackedStep has PolyBound with degree 2^k.
```

Estimated: 30 lines.

**`kSimTowerBound_dominates_inline`** (the assembly).
Pseudocode:

```text
Use Module A's polynomial_iter_tower_two_bound with:
  step    = (kSimPackedStep g_ER).interp pre-curried over params
  D       = 2^k (from kSimPackedStep_polyBound)
  m       = max baseConst, etc. (from kSimPackedBase
            polynomial bound, derived analogously)
  v_0     = (kSimPackedBase h_ER).interp params
  h_step  = via kSimPackedStep_polyBound
  h_base  = via kSimPackedBase polynomial bound
Conclude: trace at iter j ≤ tower 2 (linear).

Then show this is ≤ kSimTowerBound's interp at
(Fin.cons j params) (which is iterAutoBoundExpr with
appropriate (d, lh) parameters).  Specifically:
  - kSimTowerBound's d = (kSimPackedStep g_ER).towerHeight
  - kSimTowerBound's lh = (kSimPackedBase h_ER).towerHeight
  - By Module B's log_le_towerHeight, d ≥ Nat.log 2 (2^k) = k
  - With d ≥ k, tower (d+1) (linear) ≥ tower 2 (linear)
    (provided d + 1 ≥ 2, i.e. d ≥ 1, which holds since
    k ≥ 0 and structurally towerHeight ≥ 0)
  - Edge case: if k = 0 (single-output simrec, like addK),
    then 2^k = 1 and Nat.log 2 1 = 0, so d ≥ 0 only,
    but d + 1 ≥ 2 requires d ≥ 1 (failing the dominance
    inequality).
  - Resolution: even when degree = 1 (linear), the
    structural towerHeight of (kSimPackedStep g_ER) is
    at least 1 because the term contains at least one
    level of comp/seqPack, which adds 1 to towerHeight
    (per ER's structural recursion).
  - Cross-check with Utilities/KSimSzudzikSimrec.lean:
    kSimPackedStep wraps Nat.seqPack of children, which
    composes ERMor1.natPair (towerHeight 0) under at
    least one comp.  towerHeight of comp = max children's
    towerHeights; doesn't add 1.  So towerHeight may be 0
    for the addK-style single-output case.
  - Resolution: use d ≥ Nat.log 2 D + 1 from Module B's
    lemma, where D = 2^k * D_g and D_g ≥ 1.  Then
    d ≥ k + 0 + 1 = k + 1.  With d + 1 ≥ k + 2,
    tower (k+2) (linear) ≥ tower 2 (linear) for k ≥ 0. ✓
```

Estimated: 100–200 lines for the full assembly,
including arithmetic massaging.  This is the largest
single proof.

## Tower-arithmetic facts needed

Several inequalities about `tower h x` are used.  All are
provable from `tower 0 x = x` and
`tower (h+1) x = 2^(tower h x)` plus standard `Nat`
arithmetic:

- `tower h x ≤ tower (h+1) x` (height-monotonicity).
- `tower h x ≤ tower h y` when `x ≤ y` (input-monotonicity).
  Already in `Utilities/Tower.lean` as `tower_mono_right`.
- `(tower h x + 1)^D ≤ tower (h+1) (x + Nat.log 2 D + 1)`
  (the heart of polynomial-iter; ~10 lines).
- `tower h x ≤ tower h (linear-in-x)` for linear functions
  with positive coefficients.

These are added as helper lemmas in Module A near
`polynomial_iter_tower_two_bound`.

## Testing strategy

### Module A tests

`GebLeanTests/Utilities/ComputationalComplexity.lean`:

- `#guard Nat.pair 3 5 ≤ 9 * 9`.
- `#guard` for `seqPackBound` on small concrete lists.
- `#guard` for `polynomial_iter_tower_two_bound` on
  `step v x = (v + x + 1)^2`, iterate 3 times.

### Module B tests

`GebLeanTests/LawvereERPolynomialBound.lean`:

- Construct `PolyBound` for `ERMor1.zeroN`,
  `ERMor1.succ`, `ERMor1.proj 0`; check
  `Nat.log 2 degree ≤ towerHeight`.
- Construct `PolyBound` for a polynomial-degree-2 ER
  term (e.g. `bsum (proj 0)`); verify the bound holds.

### Module C tests

`GebLeanTests/LawvereKSimPolynomialBound.lean`:

- `level0Shape` test on `KMor1.zero`, `succ`, `proj`,
  small `comp`s; verify shape and `level0Shape_interp`.
- `linearBound` test on `addK`; verify dominance for
  small contexts.
- End-to-end: apply
  `kSimTowerBound_dominates_inline` to `addK` (level-1
  simrec); verify trace at iter 5 ≤ bound.

## Re-export and integration

After Module A, B, C are built:

- Add to `GebLean.lean` (alphabetical order): the three
  new modules.
- Add to `GebLeanTests.lean`: the three new test modules.
- Update kToER plan
  (`docs/plans/2026-04-29-lawvere-k-sim-ktoer-plan.md`):
  - Annotate Task 14's prompt to use Module C's
    `kSimTowerBound_dominates_inline`.
  - Update plan amendment dated 2026-04-30 to reflect
    that the polynomial-bound sub-project has landed.
- Resume Task 14 of the kToER plan with the new
  infrastructure available.

## Out of scope

- Course-of-values recursion as a stand-alone construction
  (different from simultaneous PR; not needed for kToER).
- Sub-project 2 (URM concrete instructions and K^sim
  simulator term).
- Sub-project 3 (Ackermann/runtime bound for the URM
  simulator).
- Sub-project 4 (backward translation `erToK` and the
  Phase 2 categorical equivalence packaging).
- Phase 3 (⋃_n K^sim_n ⊆ Primrec).

## Open questions

None at design time.  The implementation plan's tasks
will surface specific tactic-level questions
(particularly for Module B's structural towerHeight
lemma, where the per-constructor degree-of-interp
calculation is the most involved part).

## Compositional discipline

Every named construct in Modules A, B, C carries:

- A precise type signature.
- A docstring stating its mathematical content with
  literature reference.
- An `@[simp]`-tagged interp lemma (where applicable)
  characterising its closed-form behaviour.

This matches the bottom-up named-composite discipline
from `CLAUDE.md` and the project's existing conventions
in `LawvereERBoundComputable.lean` and
`Utilities/SzudzikSeq.lean`.
