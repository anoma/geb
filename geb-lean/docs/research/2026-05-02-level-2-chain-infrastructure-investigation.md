# Level-2 chain infrastructure investigation

This document catalogs the level-1 dominance chain, maps each
helper to literature, identifies what is missing for the level-2
analog, and proposes the shortest sound path to
`kSimTowerBound_dominates_inline`.

The cataloging draws on three authoritative sources:

- `docs/research/2026-04-30-ksim-polynomial-bound-references.md`
  for citation network (Claims 1-7, plus Lemma 1.A and Lemma 1.B).
- `GebLean/LawvereKSimPolynomialBound.lean` lines 1-2890
  (level-1 chain plus per-level utilities).
- `GebLean/Utilities/ComputationalComplexity.lean` and
  `GebLean/Utilities/KSimSzudzikSimrec.lean` for the supporting
  arithmetic and packed-simrec primitives.

All file paths are absolute relative to the repository root.
"L.K.P.B" abbreviates `LawvereKSimPolynomialBound.lean`.

## Part 1: Level-1 chain dependency catalog

### Entry point

`kSimTowerBound_dominates_level_one`

- **Location**: L.K.P.B lines 2578-2703.
- **Privacy**: `private`.
- **Signature**:
  `{a k : ℕ} (h_fam : Fin (k+1) → KMor1 a)`
  `(g_fam : Fin (k+1) → KMor1 (a+1+(k+1)))`
  `(h_h : ∀ l, (h_fam l).level ≤ 0)`
  `(h_g : ∀ l, (g_fam l).level ≤ 0)`
  `(j : ℕ) (params : Fin a → ℕ)` →
  `Nat.rec ((kSimPackedBase _).interp params)`
  `(fun i prev => (kSimPackedStep _).interp _) j ≤`
  `(kSimTowerBound _ _).interp (Fin.cons j params)`.
- **What it proves**: at level 1, the iterated value of the
  packed step over the packed base is dominated by the tower
  bound, for every iteration counter and parameter context.
- **Literature**: composes Claim 3 (seqPack polynomial closure),
  Claim 4 (polynomial-iter tower bound, Recursion Class Ch. 4
  Prop. 4.7 specialized to n = 1 → polynomial output), and
  Claim 7 (tower bound for ER).
- **Level-0 specificity**: assumes `level (h_fam l) ≤ 0` and
  `level (g_fam l) ≤ 0`.  This is load-bearing: the proof
  routes the children's bounds through `KMor1.level0Shape`
  (Lemma 1.B) and uses `kToER_level0_towerHeight_ge_const` to
  match each child's `linearBound.2` against
  `kToER`-`towerHeight + 1`.  At level 2 the children may be
  level-1 K^sim, whose bounds are linear (Lemma 1.A) but no
  longer of `ConstantOrShiftedProj` shape.
- **Level-2 needs**: the level-2 analog must invoke
  `KMor1.linearBound` (Lemma 1.A) for level-1 children and
  `KMor1.linearBoundLog_le_towerHeight` to absorb its constants
  into `(kToER child).towerHeight`.  See Part 4.

### Direct dependencies of the entry point

`packed_iteration_matches_simrecVec`

- **Location**: L.K.P.B lines 1126-1287.
- **Privacy**: `private`.
- **Signature**:
  `{a k : ℕ} (h_fam g_fam) (h_h h_g) (params : Fin a → ℕ)`
  `(j : ℕ)` → equality between the `Nat.rec` of packed step
  over packed base and `Nat.seqPack` of `KMor1.simrecVec`.
- **What it proves**: the iterated packed value at iteration
  `j` equals the seqPack encoding of the K^sim simrec trace.
- **Literature**: project-internal accounting (encodes the
  trace via `Nat.seqPack` and asserts that the ER and K^sim
  traces agree at level 1).  The agreement at every iteration
  rests on `kToER_interp_level_zero` for the children.
- **Level-0 specificity**: the equality holds because
  `kToER_interp_level_zero` is invoked on each `g_fam l` and
  `h_fam l` in the induction's step and base cases.
- **Level-2 needs**: a level-1 analog with
  `kToER_interp_level_one` substituted for
  `kToER_interp_level_zero`.  Pattern is identical.

`KMor1.simrecVec_seqPack_le_pow`

- **Location**: L.K.P.B lines 2509-2566.
- **Privacy**: `private`.
- **Signature**: takes `S` upper-bounding the params and
  iteration counter, returns
  `Nat.seqPack ((finRange).map simrecVec) ≤ (CC*S+KK+2)^(6*4^(k+1))`,
  with `CC, KK` extracted from `level0Shape.linearBound` of the
  children via foldr-max.
- **What it proves**: the seqPack of all simrecVec components
  is dominated by a fixed polynomial of degree
  `6 * 4^(k+1)` in the linearly-bounded uniform value.
- **Literature**: Claim 3 (Tourlakis 2018 §0.1.0.34 plus
  Damnjanovic Lemma 6.1) — iterated pairing of polynomially
  bounded components is polynomially bounded.  Project-side
  realization via `Nat.seqPack_le_seqPackBound`.
- **Level-0 specificity**: invokes `level0Shape.linearBound`
  on the children, which only applies at level ≤ 0.  The
  uniform-linear-bound value `CC * S + KK` is built from the
  level-0 shape constants.
- **Level-2 needs**: a level-1 analog using `KMor1.linearBound`
  (Lemma 1.A).  The polynomial argument's degree is the same
  (`(d+5) * 4^(k+1)` with `d = 1` for linear bounds), so the
  exponent `6 * 4^(k+1)` carries; the `(C, K)` constants are
  the level-1 versions extracted from `KMor1.linearBound`.

`KMor1.simrecVec_uniform_linear_bound`

- **Location**: L.K.P.B lines 2427-2503.
- **Privacy**: `private`.
- **Signature**: at iteration `n ≤ S`, every simrecVec
  component is bounded by `CC * S + KK`.
- **What it proves**: uniform linear bound on the trace.
- **Literature**: Lemma 1.A specialized to the simrec case
  per the research doc Lemma 1.A's simrec sub-proof.
- **Level-0 specificity**: as for `simrecVec_seqPack_le_pow`,
  the constants come from `level0Shape`.
- **Level-2 needs**: replace level-0 shapes with level-1
  `KMor1.linearBound`.  The conclusion shape `≤ CC*S + KK` is
  inherited (linear in the iteration counter, with linear
  coefficients).

`KMor1.simrecVec_linear_bound_aux`

- **Location**: L.K.P.B lines 322-503.
- **Privacy**: `private`.
- **Signature**: structural induction on iteration counter
  `n`, proving `simrecVec h_fam g_fam params n j ≤
  (step_c+step_k+1)*S + base_max + step_k*n` for level-0
  families.
- **What it proves**: per-iteration linear bound that drives
  the uniform linear bound.
- **Literature**: Lemma 1.A simrec case, with explicit
  per-iteration accounting.
- **Level-0 specificity**: each step adds at most `step_k`,
  matching Lemma 1.B's "no multiplicative coefficient on max"
  property.  At level 1, a step `g_fam l` may have a
  multiplicative coefficient on the inputs, so each iteration
  could multiply rather than add a constant.
- **Level-2 needs**: a polynomial-iter bound replacement (NOT
  a linear-bound replacement).  The level-1 step's linear
  bound, iterated `n` times, gives a polynomial-degree bound;
  see Part 4.

`stepTH_baseTH_dominates_arg`

- **Location**: L.K.P.B lines 2226-2421.
- **Privacy**: `private`.
- **Signature**: returns
  `Nat.log 2 (CC + 1) + Nat.log 2 (KK + Nat.log 2 E + 4) ≤`
  `(kSimPackedStep g_ER).towerHeight +`
  `2 * (kSimPackedBase h_ER).towerHeight + 1`.
- **What it proves**: the log-sums in the dominance chain's
  RHS are dominated by `stepTH + 2*baseTH + 1`.
- **Literature**: Wong's Prop. 4.6 inductive recipe applied
  to the specific seqPack-encoded structure (research doc
  "Update 2026-05-01 literature re-review" subsection).  The
  factor-of-2 on `baseTH` comes from the towerHeight
  bookkeeping for the `iterAutoBoundExpr` substructure.
- **Level-0 specificity**: routes through
  `kToER_level0_towerHeight_ge_const` (level-0 only).
- **Level-2 needs**: replace `kToER_level0_towerHeight_ge_const`
  with `KMor1.linearBoundLog_le_towerHeight` for level-1
  children.  This already exists at line 1828.

`kToER_level0_towerHeight_ge_const`

- **Location**: L.K.P.B lines 1031-1122.
- **Privacy**: `private`.
- **Signature**: `(f : KMor1 a) → (h : f.level ≤ 0) →`
  `(level0Shape f h).linearBound.2 ≤ (kToER f _).towerHeight + 1`.
- **What it proves**: at level 0, the additive constant in the
  linear bound is dominated by the kToER-image's tower height.
- **Literature**: Lemma 1.B-derived structural result; the
  exposition is in the research doc "Implication for the
  level-2 dominance chain" callout.
- **Level-0 specificity**: explicit (level 0 only).
- **Level-2 needs**: at level 1+, the level-0 helper does not
  apply to children with level 1.  The level-1 analog is
  `KMor1.linearBoundLog_le_towerHeight` (line 1828), which
  bounds `Nat.log 2` of the linear-bound sum by
  `3 * towerHeight + 1`.  That lemma exists and is ready.

`kSimPackedStep_towerHeight_ge_propagate`

- **Location**: L.K.P.B lines 1506-1516.
- **Privacy**: `private`.
- **Signature**: `(g : Fin (k+1) → ERMor1 (a+1+(k+1)))` →
  `natPair.tH + 2 + sup_l ((g l).comp kSimStepContext).tH ≤`
  `(kSimPackedStep g).towerHeight`.
- **What it proves**: structural propagation of children's
  tower heights through the packed step.
- **Literature**: project-internal accounting (recursion on
  `kSimSzudzikPackList` adds two structural levels per layer;
  see the docstring at line 1383).
- **Level-0 specificity**: none — purely about ER-side
  packing.  Level-agnostic.
- **Level-2 needs**: reusable as-is.

`kSimPackedBase_towerHeight_ge_propagate`

- **Location**: L.K.P.B lines 1495-1504.
- **Privacy**: `private`.
- **Signature**: same shape as the step version.
- **What it proves / literature / specificity / needs**: as
  for the step version; level-agnostic, reusable as-is.

`kSimPackedStep_towerHeight_ge_succ_k`

- **Location**: L.K.P.B lines 1376-1381.
- **Privacy**: `private`.
- **Signature**: `(g : Fin (k+1) → ERMor1 (a+1+(k+1)))` →
  `k + 2 ≤ (kSimPackedStep g).towerHeight`.
- **What it proves**: at system size `k+1` the packed step has
  tower height at least `k+2`.
- **Literature**: project-internal accounting (each pairing
  layer in `kSimSzudzikPackList` contributes one level).
- **Level-0 specificity**: none.  Level-agnostic.
- **Level-2 needs**: reusable as-is.

`kSimPackedBase_towerHeight_ge_succ_k`

- **Location**: L.K.P.B lines 2204-2209.
- **Privacy**: `private`.
- **Signature / proof / literature / specificity**: as for the
  step version.  Level-agnostic; reusable as-is.

`kSimPackedStep_polyBound`, `kSimPackedBase_polyBound`

- **Location**: L.K.P.B lines 738-806 (base), 817-957 (step).
- **Privacy**: public `def`.
- **Signature**:
  `(h_ER) (pb_h : per-component PolyBound) →`
  `ERMor1.PolyBound (kSimPackedBase h_ER)`
  (and step analog).
- **What it proves**: assembles a polynomial bound for the
  packed simrec base / step from per-component polynomial
  bounds.
- **Literature**: Claim 3 (seqPack polynomial closure) at
  general degree `D`, projected onto the `ERMor1.PolyBound`
  structure.
- **Level-0 specificity**: none — input `pb_h`, `pb_g` may be
  PolyBounds at any level.  Level-agnostic.
- **Level-2 needs**: NOT used by the level-1 chain (the
  level-1 chain bypasses `PolyBound` and uses
  `Nat.seqPack_le_seqPackBound` directly via
  `KMor1.simrecVec_seqPack_le_pow`).  Document for level-2:
  potentially usable, but the existing direct route via
  `Nat.seqPack_le_seqPackBound` is shorter.

`KMor1.linearBound`

- **Location**: L.K.P.B lines 207-277.
- **Privacy**: public `def`.
- **Signature**: `(f : KMor1 a) → f.level ≤ 1 → ℕ × ℕ`,
  returning `(c, k)` such that
  `f.interp ctx ≤ c * sup ctx + k`.
- **What it proves**: Lemma 1.A constants.
- **Literature**: research doc Lemma 1.A.
- **Level-0 specificity**: defined at level ≤ 1.  Used at
  every level when invoked on level-1 children.
- **Level-2 needs**: applied to level-1 children of a
  level-2 simrec.  Already in place.

`KMor1.linearBound_dominates`

- **Location**: L.K.P.B lines 507-733.
- **Privacy**: public `def`.
- **Signature**: `(f : KMor1 a) (h : f.level ≤ 1) (ctx) →`
  `f.interp ctx ≤ (linearBound f h).1 * sup ctx +`
  `(linearBound f h).2`.
- **What it proves**: dominance of the K^sim interp by the
  linear bound at level 1.
- **Literature**: Lemma 1.A's dominance statement.
- **Level-0 specificity**: defined at level ≤ 1.
- **Level-2 needs**: not directly used — level-2 children at
  level 1 are bounded via this lemma, then composed with
  `kToER_interp_level_one`.

`KMor1.linearBoundLog_le_towerHeight`

- **Location**: L.K.P.B lines 1828-2200.
- **Privacy**: public.
- **Signature**: `(f : KMor1 a) (h : f.level ≤ 1) →`
  `Nat.log 2 ((linearBound f h).1 + (linearBound f h).2 + 1)`
  `≤ 3 * (kToER f _).towerHeight + 1`.
- **What it proves**: structural bound matching the linear
  bound's log-sum to the towerHeight, with multiplicative
  slack 3 and additive 1.
- **Literature**: Wong's Prop. 4.6 exponent-tracking recipe
  (research doc "Update 2026-05-01" subsection); the
  `comp f gs` clause matches Wong's `m + max(j(1), …, j(k))`
  with `+1` per `comp` wrapping; the simrec clause uses
  `kToER_simrec_towerHeight_ge_max_child_tH`.
- **Level-0 specificity**: defined at level ≤ 1, with
  level-0 sub-cases routing through
  `linearBoundLog_le_towerHeight_level_zero`.
- **Level-2 needs**: this is the bridge that the level-2
  chain wants to consume on level-1 children.  Used directly.

### Tower-arithmetic dependencies

`Nat.pow_le_tower_two_with_shift`

- **Location**: `Utilities/ComputationalComplexity.lean`
  lines 606-631.
- **Privacy**: public theorem.
- **Signature**: `(CC S KK E : ℕ) →`
  `(CC*S + KK + 2)^E ≤ tower 2 (CC*S + KK + 1 + log 2 E + 2)`.
- **What it proves**: a polynomial of degree `E` is dominated
  by `tower 2 (linear + log E)`.
- **Literature**: Recursion Class Ch. 4 Prop. 4.7 specialized
  to n = 2 (research doc Claim 4 Fix B part 2).
- **Level-0/1/2 specificity**: none.  Level-agnostic
  arithmetic.  Reusable.

`Nat.tower_two_le_tower_three_linear`

- **Location**: `Utilities/ComputationalComplexity.lean`
  lines 548-604.
- **Privacy**: public theorem.
- **Signature**: `(C D X : ℕ) →`
  `tower 2 (C*X + D) ≤ tower 3 (X + log 2 (C+1) + log 2 (D+1) + 2)`.
- **What it proves**: a `tower 2`-of-linear bound is dominated
  by a `tower 3`-of-linear-log bound.
- **Literature**: Recursion Class Ch. 4 §4.4 "composed
  exponentials are all elementary"; folklore tower-shift.
- **Level-0/1/2 specificity**: none.  Reusable.

`tower_mono_left`, `tower_mono_right`

- **Location**: `Utilities/Tower.lean`.
- **Privacy**: public.
- **Signature / proof / literature / specificity**:
  monotonicity of the tower function in height (left) and
  argument (right).  Foundational.  Level-agnostic.

`kSimTowerBound_interp` (= `interp_iterAutoBoundExpr`)

- **Location**: `Utilities/KSimSzudzikSimrec.lean`
  lines 423-434.
- **Privacy**: public theorem (`@[simp]`).
- **What it proves**: closed-form for `kSimTowerBound`'s
  interp as `tower (stepTH + 1) (...)`.
- **Literature**: research doc Claim 4 Fix B part 2's
  `iterAutoBoundExpr` definition.
- **Level-0/1/2 specificity**: none.  Reusable.

`ERMor1.interp_sumCtxER`

- **Location**: project utilities (search:
  `LawvereERPolynomialBound.lean` line 471 calls).
- **Privacy**: public theorem.
- **Signature**: `(ERMor1.sumCtxER (a+1)).interp ctx =`
  `Finset.univ.sum ctx`.
- **Level-0/1/2 specificity**: none.  Reusable.

`Nat.seqPack_le_seqPackBound`

- **Location**: `Utilities/ComputationalComplexity.lean`
  lines 239-252.
- **Privacy**: public.
- **Signature**: `(vs : List ℕ) (k d m : ℕ) (hlen : vs.length ≤ k+1)`
  `(h_bounds : ∀ v ∈ vs, v ≤ (m+1)^d) →`
  `Nat.seqPack vs ≤ seqPackBound k d m`.
- **Literature**: Claim 3 (seqPack polynomial closure).
- **Level-0/1/2 specificity**: none.  Reusable.

`Nat.polynomial_iter_tower_bound`

- **Location**: `Utilities/ComputationalComplexity.lean`
  lines 466-546.
- **Privacy**: public.
- **Signature**: see file.  Bounds an iterated polynomial step
  by `tower 2 (linear + log D)`.
- **Literature**: Claim 4 (polynomial-iter tower bound,
  Prop. 4.7 for n = 1).
- **Level-0/1/2 specificity**: none — but its assumed
  hypothesis (`step v x ≤ (max v x + 1)^D`) is exactly the
  level-1-iterated form.  Already documented in the research
  doc as Module A Poly Task 5.
- **Level-2 needs**: directly relevant.  At level 2, the step
  is polynomial in the inputs, so the iterated bound is
  `tower 2`-of-(linear + log D); composed with
  `tower_two_le_tower_three_linear` gives `tower 3`-of-linear.

### Children of level-1 simrec proof

`kToER_interp_level_zero`

- **Location**: L.K.P.B lines 966-1007.
- **Privacy**: public theorem.
- **Signature**: `∀ {a} (f) (h : f.level ≤ 0) (ctx) →`
  `(kToER f _).interp ctx = f.interp ctx`.
- **What it proves**: kToER preserves interpretation at
  level 0.
- **Literature**: Claim 5 (K^sim_n = E^{n+1}, n ≥ 2)
  specialized to level 0; the level-0 case is by direct
  structural recursion (no simrec to discharge).
- **Level-0 specificity**: explicit.
- **Level-2 needs**: replaced by `kToER_interp_level_one`
  for level-2's level-1 children.

`kToER_interp_level_one`

- **Location**: L.K.P.B lines 2711-2875.
- **Privacy**: `private`.
- **Signature**: as for level-zero, at level ≤ 1.  Recurses
  through atomics, comp, raise, and simrec; the simrec case
  uses `kSimTowerBound_dominates_level_one` to discharge the
  bounded-recursion dominance hypothesis.
- **Literature**: Claim 5 specialized to level 1.
- **Level-1 specificity**: explicit; uses the level-1
  dominance theorem.
- **Level-2 needs**: a level-2 analog `kToER_interp_level_two`
  is the final goal of Task 17c (currently in progress).
  Its simrec case will use `kSimTowerBound_dominates_inline`.

`kToER_simrec_h_side_bound`, `kToER_simrec_g_side_bound`,
`kToER_simrec_towerHeight_ge_max_child_tH`

- **Location**: L.K.P.B lines 1553-1731.
- **Privacy**: `private`.
- **Signature**: bounds the maximum-over-children towerHeight
  by the simrec's towerHeight.
- **What it proves**: at level 2 (input families at level
  ≤ 1), the simrec's kToER image's towerHeight dominates the
  max of the children's.
- **Literature**: Wong's Prop. 4.6 inductive case for bounded
  recursion (research doc "Update 2026-05-01").
- **Level-1 specificity**: hypothesis is `level (h/g_fam l) ≤ 1`
  with conclusion at `level (simrec) ≤ 2`.
- **Level-2 needs**: this is exactly the level-2 helper
  already in place; it consumes by L.K.P.B's
  `linearBoundLog_le_towerHeight` simrec case (line 2033+).

### Helpers without literature reference

`Fin.foldr_max_ge`, `Fin.foldr_max_le`

- **Location**: L.K.P.B lines 299-314 and 1806-1821.
- **Privacy**: `private`.
- **What it proves**: bracketing of foldr-max by individual
  components.
- **Literature**: project-internal accounting (Lean foldr
  manipulation).
- **Level-2 needs**: reusable as-is.

`Nat.add_three_lt_two_pow_succ_succ`,
`Nat.three_mul_add_six_lt_two_pow_three_mul_add_two`

- **Location**: L.K.P.B lines 1733-1745, 1789-1804.
- **Privacy**: `private`.
- **What it proves**: arithmetic helpers feeding
  `Nat.log_lt_of_lt_pow`.
- **Literature**: project-internal accounting (Nat.log
  monotonicity infrastructure).
- **Level-2 needs**: reusable as-is.

### Items not in the direct chain but used at level 1

`KMor1.level0Shape`, `KMor1.level0Shape_interp`

- **Location**: L.K.P.B lines 81-171.
- **What it proves**: Lemma 1.B (level-0 shape lemma).
- **Literature**: research doc Lemma 1.B; corresponds to
  Recursion Class Ch. 4 Prop. 4.3.
- **Level-2 needs**: invoked indirectly via
  `KMor1.linearBound`'s level-0 fallback at the `comp ≤ 0`
  branch.  Reusable as a sub-component.

`ConstantOrShiftedProj`, `interp`, `linearBound`,
`linearBound_dominates`

- **Location**: L.K.P.B lines 60-297.
- **What it proves**: Lemma 1.B's data type and bound.
- **Level-2 needs**: same as above.

`linearBoundLog_le_towerHeight_level_zero`

- **Location**: L.K.P.B lines 1753-1787.
- **Privacy**: `private`.
- **What it proves**: level-0 specialization of the
  linearBound-log-vs-towerHeight inequality.
- **Literature**: as for `linearBoundLog_le_towerHeight`.
- **Level-2 needs**: indirect dependency through the
  level-1 bridge.

### Helpers DEFINED but NOT used by the level-1 chain

`kSimPackedStep_polyBound`, `kSimPackedBase_polyBound` —
constructed for general level-1+ children; the level-1 chain
uses `Nat.seqPack_le_seqPackBound` directly without going
through `PolyBound`.  These exist for future level-2 use.

## Part 2: Mapping to literature

For each helper: the citation and a confidence level (HIGH if a
direct transcription, MEDIUM if a generalization, LOW if
project-internal accounting).

- `kSimTowerBound_dominates_level_one` —
  Composition of Claims 3, 4, 7 at level 1 — HIGH.
- `packed_iteration_matches_simrecVec` —
  Project-internal trace agreement (rests on Claim 5 at
  level 0) — MEDIUM.
- `KMor1.simrecVec_seqPack_le_pow` —
  Claim 3 (Tourlakis 2018 §0.1.0.34, Damnjanovic Lem 6.1)
  — HIGH.
- `KMor1.simrecVec_uniform_linear_bound` —
  Lemma 1.A simrec case — HIGH.
- `KMor1.simrecVec_linear_bound_aux` —
  Lemma 1.A simrec case, per-iter form — HIGH.
- `stepTH_baseTH_dominates_arg` —
  Wong Prop. 4.6 exponent-tracking — MEDIUM.
- `kToER_level0_towerHeight_ge_const` —
  Project-internal, Lemma 1.B-derived — MEDIUM.
- `kSimPackedStep_towerHeight_ge_propagate` —
  Project-internal (kSimSzudzikPackList structure) — LOW.
- `kSimPackedBase_towerHeight_ge_propagate` —
  Project-internal (kSimSzudzikPackList structure) — LOW.
- `kSimPackedStep_towerHeight_ge_succ_k` —
  Project-internal (per-layer pairing accounting) — LOW.
- `kSimPackedBase_towerHeight_ge_succ_k` —
  Project-internal (per-layer pairing accounting) — LOW.
- `kSimPackedStep_polyBound` —
  Claim 3 generalized to PolyBound — MEDIUM.
- `kSimPackedBase_polyBound` —
  Claim 3 generalized to PolyBound — MEDIUM.
- `KMor1.linearBound` — Lemma 1.A — HIGH.
- `KMor1.linearBound_dominates` — Lemma 1.A dominance — HIGH.
- `KMor1.linearBoundLog_le_towerHeight` —
  Wong Prop. 4.6 exponent-tracking — HIGH.
- `kToER_interp_level_zero` — Claim 5 at level 0 — HIGH.
- `kToER_interp_level_one` — Claim 5 at level 1 — HIGH.
- `kToER_linearBound_dominates_level_one` —
  Composition of `linearBound_dominates` and
  `interp_level_one` — HIGH.
- `kToER_simrec_h_side_bound` —
  Wong Prop. 4.6 (boundedRec inductive case) — HIGH.
- `kToER_simrec_g_side_bound` —
  Wong Prop. 4.6 (boundedRec inductive case) — HIGH.
- `kToER_simrec_towerHeight_ge_max_child_tH` —
  Wong Prop. 4.6 (boundedRec inductive case) — HIGH.
- `Nat.pow_le_tower_two_with_shift` —
  Recursion Class Prop. 4.7 (n = 2) — HIGH.
- `Nat.tower_two_le_tower_three_linear` —
  Recursion Class §4.4 / folklore — MEDIUM.
- `Nat.polynomial_iter_tower_bound` —
  Recursion Class Prop. 4.7 (n = 1) — HIGH.
- `Nat.seqPack_le_seqPackBound` — Claim 3 — HIGH.
- `kSimTowerBound`, `kSimTowerBound_interp`,
  `kSimTowerBound_mono_counter` —
  Claim 4 Fix B part 2 (`iterAutoBoundExpr`) — HIGH.
- `KMor1.level0Shape` — Lemma 1.B — HIGH.
- `KMor1.level0Shape_interp` — Lemma 1.B agreement — HIGH.
- `ConstantOrShiftedProj` and friends — Lemma 1.B data — HIGH.
- `linearBoundLog_le_towerHeight_level_zero` —
  Wong Prop. 4.6 specialized to level 0 — MEDIUM.
- `Fin.foldr_max_ge`, `Fin.foldr_max_le` —
  Project-internal — LOW.
- `Nat.add_three_lt_two_pow_succ_succ` and similar —
  Project-internal — LOW.

## Part 3: What's missing for level 2

### Level-0-specific helpers needing level-2 analogs

1. `KMor1.simrecVec_linear_bound_aux` — at level 2 the step is
   level 1, so per-iteration the bound is no longer linear-in-S
   plus additive.  The level-2 analog must take a polynomial
   per-iteration bound (linear coefficient on inputs ⇒ degree-1
   polynomial on outputs after composition with level-0+...).
   In fact, the level-2 step's iterate is bounded directly via
   `Nat.polynomial_iter_tower_bound`, bypassing this helper
   entirely.  Recommendation: SKIP a structural per-iteration
   bound; route through `polynomial_iter_tower_bound` directly.

2. `KMor1.simrecVec_uniform_linear_bound` — at level 2 the
   uniform bound on every component is no longer linear; it
   is polynomial in the inputs (coming from
   `polynomial_iter_tower_bound` applied to the level-1 step).
   Recommendation: build a uniform polynomial bound rather
   than a uniform linear bound; signature shape
   `simrecVec h_fam g_fam params n l ≤ tower 2 (poly in
   max(params, n))`.

3. `KMor1.simrecVec_seqPack_le_pow` — adapt to take in a
   tower-2 per-component bound (rather than a linear bound)
   and produce a tower-2 bound on the seqPack.  But seqPack
   of polynomially-bounded values is polynomially bounded
   (Claim 3); composing a polynomial bound with `tower 2` of
   linear gives `tower 2` of (linear with larger
   coefficient).  Recommendation: derive a level-2 variant
   that takes the tower-2 bound directly.

4. `kToER_level0_towerHeight_ge_const` — replaced at level 2
   by `KMor1.linearBoundLog_le_towerHeight` for level-1
   children.  No new helper required.

5. `packed_iteration_matches_simrecVec` — needs a level-1
   variant; substitute `kToER_interp_level_one` for
   `kToER_interp_level_zero`.  Routine adaptation.

### Possibly missing infrastructure (verified by inspection)

- `Nat.polynomial_iter_tower_bound`: EXISTS at
  `Utilities/ComputationalComplexity.lean` lines 466-546.
  Hypothesis is precisely the polynomial-step shape needed.
- `Nat.tower_two_le_tower_three_linear`: EXISTS at
  `Utilities/ComputationalComplexity.lean` lines 548-604.
- `Nat.pow_le_tower_two_with_shift`: EXISTS at
  `Utilities/ComputationalComplexity.lean` lines 606-631.
- A polynomial-bounded base / step builder for level-1 K^sim
  children (Lemma 1.A composed with `kToER_interp_level_one`):
  the function `kToER_linearBound_dominates_level_one`
  (L.K.P.B line 2880) covers the level-1 children directly.
- `kSimPackedStep_polyBound` / `kSimPackedBase_polyBound`:
  EXIST.  Could be invoked directly with level-1 PolyBounds
  for the children.  But the level-1 chain bypasses these in
  favor of direct `seqPack_le_seqPackBound`.

- A `Nat.rec → Nat.iterate` bridge (for invoking
  `polynomial_iter_tower_bound` on the iterated packed step):
  needed at the level-2 dominance assembly.  Mathlib has
  `Function.iterate_succ`, `Nat.iterate`-`Nat.rec` agreement
  via `Function.iterate_succ_apply`.  Project may need a
  small adapter.  Verifying:
  `Function.iterate` and `Nat.rec` agree pointwise; converting
  between them is `Function.iterate_succ_apply` /
  `Function.iterate_zero` plus induction.  Recommendation:
  inline the conversion in the level-2 proof.

### Possibly redundant or already-present work

- Plan v4's `T1` (proposing a level-1 dominance bridge) is
  duplicated by the existing `kToER_linearBound_dominates_level_one`
  at L.K.P.B line 2880.  Plan v5 should drop this task.
- `kSimPackedStep_polyBound` / `kSimPackedBase_polyBound` are
  unused by the level-1 chain but ready for level-2 use; they
  can be invoked instead of re-deriving polynomial bounds.

## Part 4: Recommended level-2 chain structure

Goal: prove `kSimTowerBound_dominates_inline` for level-1
children.

### Reusable unchanged

- `kSimTowerBound_interp` and `kSimTowerBound_mono_counter`
  (closed-form interp / monotonicity in counter slot).
- `kSimPackedStep_towerHeight_ge_propagate`,
  `kSimPackedBase_towerHeight_ge_propagate`,
  `kSimPackedStep_towerHeight_ge_succ_k`,
  `kSimPackedBase_towerHeight_ge_succ_k`.
- `Nat.pow_le_tower_two_with_shift`,
  `Nat.tower_two_le_tower_three_linear`,
  `tower_mono_left`, `tower_mono_right`.
- `Nat.polynomial_iter_tower_bound` (the level-2-iterate
  closed form).
- `KMor1.linearBound`, `KMor1.linearBound_dominates`.
- `KMor1.linearBoundLog_le_towerHeight`.
- `kToER_interp_level_one`,
  `kToER_linearBound_dominates_level_one`.
- `kSimPackedStep_polyBound`, `kSimPackedBase_polyBound`.
- `kToER_simrec_towerHeight_ge_max_child_tH`.
- `Nat.seqPack_le_seqPackBound`.

### New helpers for level 2

**L2-1**: `packed_iteration_matches_simrecVec_level_one` —
level-1 analog of `packed_iteration_matches_simrecVec`.

- Signature: same as the level-0 version but with
  `(h_h : ∀ l, level (h_fam l) ≤ 1)`,
  `(h_g : ∀ l, level (g_fam l) ≤ 1)`.
- Citation: project-internal trace agreement (Claim 5 at
  level 1, via `kToER_interp_level_one`).

**L2-2**: `kToER_polyBound_of_level_one` —
bridges `KMor1.linearBound` (level-1 K^sim) into an
`ERMor1.PolyBound` on the kToER image.

- Signature:
  `(f : KMor1 a) (h : f.level ≤ 1) →`
  `ERMor1.PolyBound (kToER f (Nat.le_succ_of_le h))`,
  where the `degree` is 1 and the `coefficient`/`constant`
  come from `KMor1.linearBound f h`.
- Citation: research doc Lemma 1.A (linear bound), composed
  with the project-side `PolyBound` structure (Module B).
- Note: a partial form of this already exists as Poly
  Task 15 (#299 in tasks); it bridges level-1 to PolyBound.

**L2-3**: `KMor1.simrecVec_seqPack_le_pow_level_one` —
level-1 analog of `KMor1.simrecVec_seqPack_le_pow`.

- Signature: `(h_h : ∀ l, (h_fam l).level ≤ 1)`,
  `(h_g : ∀ l, (g_fam l).level ≤ 1)`, `n ≤ S`, →
  seqPack ≤ `(CC*S + KK + 2)^E` for `E = 6 * 4^(k+1)`
  where `CC, KK` are extracted from `KMor1.linearBound`
  (rather than `level0Shape.linearBound`).
- Citation: Claim 3 (Tourlakis 2018 §0.1.0.34), at the
  level-1 polynomial degree.
- Realization: parallel to the level-0 version; substitute
  `linearBound` for `level0Shape.linearBound`.

**L2-4**: `stepTH_baseTH_dominates_arg_level_one` —
level-1 analog of `stepTH_baseTH_dominates_arg`.

- Signature: same shape, but invokes
  `KMor1.linearBoundLog_le_towerHeight` rather than
  `kToER_level0_towerHeight_ge_const`.
- Citation: Wong Prop. 4.6 inductive recipe.

**L2-5**: `kSimTowerBound_dominates_inline` — the goal.

- Signature: parallel to `kSimTowerBound_dominates_level_one`
  but with `(h_h : ∀ l, (h_fam l).level ≤ 1)`,
  `(h_g : ∀ l, (g_fam l).level ≤ 1)`.
- Realization: assemble L2-1, L2-3, L2-4 with the reusable
  arithmetic helpers, in the same calc-chain pattern as
  `kSimTowerBound_dominates_level_one`.
- Citation: the assembly mirrors Wong's chain Claim 3 +
  Claim 4 + Claim 7 at level 2 (rather than level 1).

### Highest-confidence ordering

1. L2-1 (level-1 trace agreement, routine adaptation).
2. L2-3 (level-1 seqPack bound, mirrors level-0 with
   `linearBound` substituted).
3. L2-4 (level-1 stepTH/baseTH dominance, mirrors level-0
   with `linearBoundLog_le_towerHeight` substituted).
4. L2-5 (final assembly, mirrors level-0).

L2-2 is optional: it is a standalone bridge that may be
useful in places but is not strictly required.  The level-1
chain's analogous bridge is the implicit composition of
`KMor1.linearBound_dominates` and `kToER_interp_level_one`,
which suffices for the dominance assembly without explicit
construction of an `ERMor1.PolyBound`.

The total new content is four lemmas, each a structural
mirror of an existing level-1 helper.  Each cites a specific
literature proposition or project-internal lemma.  Total
size is comparable to the existing level-1 chain; structural
risk is low because each lemma's shape is already validated
in the level-1 case.

## Part 5: Source-code citation additions

Constructions found WITHOUT a literature citation in their
docstring:

- `Fin.foldr_max_ge` (L.K.P.B line 299): docstring covers
  the mathematical content; project-internal accounting.
  No citation suggestion (it is generic foldr manipulation).
- `Fin.foldr_max_le` (L.K.P.B line 1806): same.
- `Nat.add_three_lt_two_pow_succ_succ` (line 1733): same;
  arithmetic helper.
- `Nat.three_mul_add_six_lt_two_pow_three_mul_add_two`
  (line 1789): same.

Constructions where a citation comment would clarify the
literature reference:

- `KMor1.linearBound` (line 207) — covered by docstring
  reference to Lemma 1.A in line 173.
- `KMor1.level0Shape` (line 81) — covered by docstring
  reference to Lemma 1.B in line 78.
- `kSimTowerBound_dominates_level_one` (line 2578) —
  composition of A.2 / A.3 / A.4 / A.5.1 / A.5.2.2 cited in
  the docstring; literature reference (Claims 3, 4, 7) not
  surfaced.
- `KMor1.simrecVec_seqPack_le_pow` (line 2509) — references
  `Nat.seqPack_le_seqPackBound`, but Claim 3 (Tourlakis 2018
  §0.1.0.34) is not surfaced.
- `KMor1.linearBound_dominates` (line 507) — covered by
  comment-thread reference to Lemma 1.A.
- `KMor1.linearBoundLog_le_towerHeight` (line 1828) —
  references Phase IV-B but not the literature recipe
  (Wong Prop. 4.6).
- `kSimTowerBound` (`Utilities/KSimSzudzikSimrec.lean`
  line 415) — references `iterAutoBoundExpr` but not
  Claim 4 Fix B part 2.
- `Nat.polynomial_iter_tower_bound`
  (`Utilities/ComputationalComplexity.lean` line 466-546)
  — references the iterate-tower bound but not Recursion
  Class Ch. 4 Prop. 4.7 explicitly.
- `Nat.seqPack_le_seqPackBound` (line 239-252) —
  references seqPack but not Claim 3 (Tourlakis 2018
  §0.1.0.34, Damnjanovic Lemma 6.1).

The citation additions are made as docstring augmentations
in the source files; see the corresponding commit.
