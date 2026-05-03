# Step 4 Spec — Adversarial Review, Round 1

Adversarial review of
`docs/superpowers/specs/2026-05-03-step-4-ksim-majorization-design.md`
(K^sim majorization theorems, Tourlakis 2018 §0.1.0.10).
The spec contains one mathematical gap large enough to block
the level-2 simrec case as written, several type-signature
corrections, missing-API risks for proof tactics, and a
handful of style/test-discipline points.

## Findings

### 1. Level-2 simrec → A_2 reduction does not telescope through γ.3 as outlined

- **Severity**: blocker.
- **Location**: §6.3 simrec bullet (lines 539–544) and §4
  cross-family chain (γ.2 + γ.3 + corollary at §4.4).
- **Issue**: `simrecVec_le_A_one_iter` (§6.2) bounds each
  component by
  `A_1^{r_H + n·r_G}(max n (vMax params) + o_H + n·o_G)`.
  The simrec proof outline (§6.3) then converts to A_2 by
  `A_one_iter_le_A_two_iter_two`, whose statement is
  `A_1^k(x) ≤ A_2^2(x + k + 2)` (§4.4).  Specialising at
  `n = v 0` and `k = r_H + n·r_G` yields
  `A_2^2(x + r_H + n·r_G + 2)` — i.e. the offset still
  carries the multiplicative term `n·r_G`.  Bounding `n` by
  `vMax v` gives an offset linear in `vMax v` with
  coefficient `(1 + r_G)`, NOT a constant offset.  The
  spec's claimed `(2, r_H + r_G + o_H + o_G + 2)` cannot
  dominate that.
- The master design (lines 1015–1029) handles this by
  collapsing the `n`-dependent coefficient and the
  `n`-dependent input into a single `2^{(r_H+r_G+2)·(m+1)}`
  via the bound `r_H + m·r_G + 1 ≤ (r_H+r_G+2)·(m+1)`,
  then applies `k·(m+1) ≤ 2^{m+log k + 2}` to absorb the
  coefficient INTO the input.  γ.3 as stated
  (`2^{k+1}·(x+1) ≤ tower 2 (x+k+2)`) corresponds to the
  second step but NOT the first.
- **Proposed fix**: add a γ.3.5 / γ.4 lemma transcribing
  master design line 1027 explicitly:
  `A_1^{r_H + m·r_G}(m+1) ≤ A_2^2(m + r_H + r_G + 2)`
  (or the analogous form with the o_H/o_G offsets folded
  in).  Or weaken §6.2's IH so that the iteration count
  is `(r_H + r_G + 2)·(n + 1)` from the outset, matching
  the master-design absorption.  Either way, §4 needs a
  lemma that operates on the *family* shape
  `2^{r_H + m·r_G + 1}·(m + offset)`, not on a fixed `k`.

### 2. `simrecVec_le_A_one_iter`'s bound depends on `n`, but §6.3's goal is constant-offset

- **Severity**: blocker (subsumed by 1).
- **Location**: §6.2 conclusion (lines 478–482).
- **Issue**: the statement
  `simrecVec ... n j ≤ A_1^(r_H + n·r_G)(max n (vMax params) + o_H + n·o_G)`
  is correct but is the wrong form to feed into the
  level-2 majorize.  Calling `majorize_by_A_two_iter` at
  the simrec case with `n = v 0` produces an offset that
  is linear in `vMax v` after specialising `n ≤ vMax v`.
  The §6.3 simrec bullet glosses this with "Bound `n` by
  `vMax v`. Convert ... via `A_one_iter_le_A_two_iter_two`.
  Collect into `tower 2 (vMax v + r_H + r_G + o_H + o_G + 2)`."
  — the conversion as stated is exactly what fails.
- **Proposed fix**: state §6.2 in the master-design form
  *before* converting: e.g.
  `M_n ≤ A_2^2(max n (vMax params) + r_H + r_G + 2)`
  directly, with the A_1-staircase derivation private.
  Alternatively, expose a separate
  `simrecVec_le_A_two_iter` whose conclusion is already in
  A_2 form, and have the level-2 majorize call that.

### 3. `simrecVec_le_A_one_iter` IH step does not fold cleanly with `o_H + n·o_G`

- **Severity**: major.
- **Location**: §6.2 step bullet (lines 491–499).
- **Issue**: master design lines 985–1007 prove the M_n
  closed form for *r_H, r_G* only; the master design's
  M_n bound is `A_1^(r_H + n·r_G)(max(n, max x⃗))` — no
  o_H or o_G term.  The spec adds `o_H + n·o_G` to the
  input.  The step case then needs:
  `A_1^{r_G}(max(n, A_1^{r_H + n·r_G}(max n (vMax params) + o_H + n·o_G)) + o_G)`
  ≤ `A_1^{r_H + (n+1)·r_G}(max (n+1) (vMax params) + o_H + (n+1)·o_G)`.
  The o_G term *outside* the A_1 needs to commute past
  the outer A_1 application via `A_1` monotonicity, but
  also needs to combine with the A_1 input — this works
  ONLY if `A_1^{r_G}(y + o_G) ≤ A_1^{r_G}(y) + (something)`
  type reasoning fails (A_1 is not subadditive in that
  direction).  More delicately, `n·o_G` must absorb into
  the fresh layer `A_1^{r_G}` *and* survive the IH —
  these require the input shape to remain
  `(value) + o_H + (count)·o_G`.
- **Proposed fix**: state the proof in two steps —
  (a) IH with offsets folded in: prove instead
  `M_n ≤ A_1^{r_H + n·r_G}(max n (vMax params + o_H + n·o_G))`
  by absorbing offsets into the *input* before iterating,
  using `A_1^k(x + d) ≤ A_1^k(x) + 2^k·d` if needed; or
  (b) move the offset accumulation to a post-step:
  prove the no-offset M_n bound first, then derive the
  with-offset bound at the very end.  Either way, the
  step-case algebra needs an explicit offset-handling
  argument that the spec does not currently have.

### 4. `KMor1.linearBound` interface mismatch in `majorize_one`

- **Severity**: blocker (typecheck).
- **Location**: §5.1 (lines 358–365).
- **Issue**: `KMor1.linearBound`'s domination theorem
  (existing `KMor1.linearBound_dominates`,
  `LawvereKSimPolynomialBound.lean` line ~507) gives
  `f.interp ctx ≤ c · sup ctx + k`, where
  `sup ctx = (Finset.univ : Finset (Fin a)).sup ctx`.
  The spec's `vMax` private abbreviation isn't defined in
  the spec, but the theorems at §6.1 / §6.3 use `vMax v`
  uniformly.  Match must be exact: if `vMax v` is defined
  as `(Finset.univ : Finset (Fin a)).sup v`, fine; but
  the spec doesn't pin this down.  Mismatch will silently
  break `majorize_by_A_one_iter`'s proof unfolding.
- **Proposed fix**: in §2.1 imports list, declare the
  private abbreviation explicitly:
  `private abbrev vMax {a : ℕ} (v : Fin a → ℕ) : ℕ :=
   (Finset.univ : Finset (Fin a)).sup v`.
  Make the dependency on `KMor1.linearBound_dominates`'s
  exact `Finset.sup` form load-bearing in §6.1's proof
  outline.

### 5. `A_one_iter_le_two_pow_succ` falsely claims `1 ≤ 2^k`-only side condition

- **Severity**: minor (correctness).
- **Location**: §4.2 (lines 284–292).
- **Issue**: Claimed inequality:
  `2^k · x + (2^{k+1} − 2) ≤ 2^{k+1} · x + 2^{k+1}`,
  i.e. `0 ≤ 2^k · x + 2`.  This holds unconditionally,
  no `1 ≤ 2^k` needed.  But if `k = 0`, `2^{k+1} - 2 = 0`,
  RHS = `2x + 2`, LHS = `x + 0 = x`, valid.  For
  `Nat.sub` truncation of `2^{k+1} − 2`: at `k = 0` the
  subtraction gives `0` (correct).  At `k ≥ 1`,
  `2^{k+1} ≥ 4`, no truncation.  The proof outline
  introduces `1 ≤ 2^k` as a side condition; it's not
  strictly required.  Harmless slack but the proof
  hint is misleading.
- **Proposed fix**: drop the `Nat.one_le_pow` hint or
  rephrase — `omega` plus `pow_succ` should close it
  directly.

### 6. `two_pow_succ_mul_succ_le_tower_two` proof chain has an arithmetic error

- **Severity**: major (provability).
- **Location**: §4.3 proof chain (lines 305–314).
- **Issue**: the proof goes
  `2^{k+1} · (x+1) ≤ 2^{k+1} · 2^{x+1} = 2^{k+x+2}`.
  Step 2 should be `= 2^{(k+1)+(x+1)} = 2^{k+x+2}`, fine.
  Then `≤ 2^{2^{x+k+2}}` "by `le_two_pow_self` on
  `k+x+2`" — that needs `k+x+2 ≤ 2^{x+k+2}`, true.  But
  the conclusion uses `tower_succ twice`:
  `tower 2 (x+k+2) = 2^(2^(x+k+2))`, agreeing with the
  RHS of step 3.  So the chain is correct *as math*.
  The real risk is `(x+1) ≤ 2^{x+1}`: this is
  `Nat.lt_two_pow_self` weakened by `Nat.le_of_lt`
  (Tower.lean's `le_two_pow_self`).  Confirm in proof.
- More serious: the derivation
  `2^{k+1} · 2^{x+1} = 2^{k+1+x+1}` uses `pow_add` —
  available in mathlib (`Nat.pow_add`) — but the spec
  doesn't list it among hint lemmas; a reader might
  assume `pow_add` works for `Nat` directly (it does,
  via `Nat.pow_add` or the `Monoid.npow`-based lemma).
- **Proposed fix**: list `Nat.pow_add` (or `pow_add`)
  in §4.3's hint list explicitly.  Confirm during
  implementation.

### 7. §6.3 `comp` uses `tower_compose_offsets`; the inequality is too strong

- **Severity**: major.
- **Location**: §6.4 last bullet (lines 559–562).
- **Issue**: claimed:
  `tower a (tower b (x + c) + d) ≤ tower (a + b) (x + c + d)`.
  At `a = 0`: LHS = `tower b (x+c) + d`, RHS =
  `tower b (x+c+d)`.  Need
  `tower b (x+c) + d ≤ tower b (x+c+d)`.  That holds
  for `b ≥ 1` (since tower is then convex) but at
  `b = 0` it asks `(x+c) + d ≤ x + c + d`, fine, =.
  At `a = 1, b = 0`: LHS = `tower 1 (x+c+d) = 2^{x+c+d}`,
  RHS = `tower 1 (x+c+d) = 2^{x+c+d}`, equality.
  Generally, what we want for the `comp` case is
  `f.interp(gs.interp v) ≤ tower(p_f.1)(vMax(gs.interp v) + p_f.2)`.
  Each `gs i.interp v ≤ tower r_g (vMax v + o_g)`, so
  `vMax(gs.interp v) ≤ tower r_g (vMax v + o_g)` —
  which then forms the input to the outer tower.
  The naive bound is
  `tower (p_f.1) (tower r_g (vMax v + o_g) + p_f.2)`.
  We want this ≤ `tower (p_f.1 + r_g) (vMax v + p_f.2 + o_g)`.
  The aux lemma asks
  `tower a (tower b (x+c) + d) ≤ tower (a+b) (x+c+d)` —
  i.e. eat `+d` as a tower-input shift.  This is NOT
  obvious; at `a = 1, b = 1` it asks
  `2^(2^(x+c) + d) ≤ tower 2 (x+c+d) = 2^(2^(x+c+d))`,
  i.e. `2^(x+c) + d ≤ 2^(x+c+d)`.  If `d = 0`, fine.
  If `d = 1`, `2^(x+c)+1 ≤ 2·2^(x+c) = 2^(x+c+1)`, fine.
  In general we need `2^(x+c) + d ≤ 2^(x+c) · 2^d`,
  which holds for `d ≥ 1` since
  `2^d ≥ d+1` and `2^(x+c) · 2^d ≥ 2^(x+c) + 2^(x+c)·d ≥ 2^(x+c) + d`.
  At `d = 0` it's equality.  So the inequality DOES
  hold but the justification is non-trivial — a single
  `tower_comp + tower_mono_right` chain doesn't close
  it; we need the auxiliary
  `n + d ≤ tower a (n + d)` and a cross term.
- **Proposed fix**: spell out a sub-lemma
  `tower b x + d ≤ tower b (x + d)` (provable by
  induction on `b`; at `b = 0`, trivial; at `b+1`,
  `2^{tower b x} + d ≤ 2^{tower b x + d}` requires
  `2^N + d ≤ 2^{N+d}` for `N ≥ 1`).  Add this to §6.4
  explicitly.  Verify that the `b = 0, d ≥ 1, x = 0`
  edge case (`tower 0 0 + d = d`, RHS `tower 0 d = d`)
  goes through.

### 8. `Nat.lt_pow_succ_log_self` requires base ≥ 2 — edge-case slack at `c = 0`

- **Severity**: minor.
- **Location**: §4.1 proof (line 277).
- **Issue**: mathlib's
  `Nat.lt_pow_succ_log_self : 1 < b → x < b^(Nat.log b x + 1)`
  requires the argument to be positive.  `c + 1 ≥ 1` — if
  `c + 1 = 0` impossible, so `c + 1 ≥ 1` is OK only when
  `Nat.log` is defined; mathlib's `Nat.log b 0 = 0` and
  `Nat.log b 1 = 0` for `b ≥ 2`, then `2^(0 + 1) = 2 > 1 = c + 1`
  at `c = 0`, fine.  At `c = 0, d = 0`: `r = max 1 1 = 1`,
  `A_1^1(x) = 2x + 2 ≥ 0 = 0·x + 0`, fine.  But the spec's
  `linearBound_le_A_one_iter` uses `Nat.log 2 (c+1) + 1` and
  `Nat.log 2 (d+2) + 1`; at `d = 0`, `d + 2 = 2`,
  `Nat.log 2 2 = 1`, so `r ≥ 2`, giving `A_1^2(x) = 4x + 6 ≥ 0`,
  also fine.
  No actual edge-case bug, but the proof outline
  doesn't mention the `1 < 2` precondition for
  `Nat.lt_pow_succ_log_self`.
- **Proposed fix**: add the explicit precondition
  hypothesis `(by decide : 1 < 2)` in §4.1's proof
  hint list.

### 9. Fin.foldr over child majorize results — reverse-direction max lemma needed

- **Severity**: major (provability).
- **Location**: §6.3 comp bullet (lines 528–532); §9.3.
- **Issue**: §6.3 cites `Fin.foldr_max_ge` only.  But to
  prove `f.interp(gs.interp v) ≤ A_2^{r_f + max_g r_gs}(...)`,
  we also need the *reverse* direction: every child
  bound is dominated by the foldr-max.  That's
  `Fin.foldr_max_ge`.  But to bound `vMax(gs.interp v)`
  from above by something depending on the foldr-max,
  we need to combine `gs i.interp v ≤ A_2^{r_gs}(vMax v + o_gs)`
  with `r_gs ≤ max_g r_gs`, requiring monotonicity of
  `tower` in the height index — i.e.
  `tower_mono_left`, which exists.  But the spec also
  needs `Fin.foldr_max_le` (reverse direction for
  closing the `vMax(gs.interp v) ≤ tower max_g_r ...`
  step) — that one is `private` in
  `LawvereKSimPolynomialBound.lean` line 1808.
- **Proposed fix**: import / re-export
  `Fin.foldr_max_le` from
  `LawvereKSimPolynomialBound.lean`, or restate it
  locally.  Mention this in §9.3's mitigation.

### 10. Atomic `r = 2` choice fails the dominance theorem at `succ.interp ![0]`

- **Severity**: minor (test, not spec correctness).
- **Location**: §5.2 (line 388) and §8.1 test (lines 642–644).
- **Issue**: spec assigns `succ ↦ (2, 3)`.  Domination:
  `succ.interp ![3] = 4 ≤ A_2^2(3 + 3) = tower 2 6 = 2^64`.
  Trivially fine.  But at `succ.interp ![0] = 1`,
  bound is `A_2^2(0 + 3) = tower 2 3 = 2^8 = 256`.  Also
  fine.  No actual problem.  However, `(2, 2)` for `succ`
  *also* works (`tower 2 (x + 2) ≥ x + 1`).  The choice
  of `3` over `2` is arbitrary and the docstring at
  §5.2 lines 380–384 doesn't justify why `succ` gets `+3`
  while `zero`/`proj` get `+2`.  Risk: implementer may
  pick a different value during proof and the `#guard`
  test in §8.1 (which doesn't check `succ`'s `.2`)
  doesn't lock this down.
- **Proposed fix**: either (a) document why
  `succ ↦ (2, 3)` (or change to `(2, 2)`); (b) add an
  `#guard` for `(KMor1.majorize KMor1.succ _).2 = 3` to
  pin the choice; (c) per §1.3 "Lean-side flexible",
  remove specific atomic offsets from the spec and
  defer to implementation.

### 11. `KMor1.majorize`'s `comp` case `level` propagation is hand-waved

- **Severity**: minor.
- **Location**: §5.2 (lines 391–392).
- **Issue**: `have hf : f.level ≤ 2 := /- from level/comp -/`
  and `have hgs : ∀ i, (gs i).level ≤ 2 := /- ditto -/`
  are placeholders.  `KMor1.linearBound`'s comp case
  (LawvereKSimPolynomialBound.lean lines 213–225) does
  this exact derivation; the spec should cite it as the
  template explicitly.
- **Proposed fix**: replace placeholder with explicit
  `unfold KMor1.level at h; ...` derivation, or note
  "follows the pattern in `KMor1.linearBound`'s comp
  case at LawvereKSimPolynomialBound.lean:213–225".

### 12. `KMor1.majorize`'s `simrec` case derivation likewise hand-waved

- **Severity**: minor.
- **Location**: §5.2 (lines 406–409).
- **Issue**: `(h_fam j).level ≤ 1` and
  `(g_fam j).level ≤ 1` from `simrec.level ≤ 2`.
  `simrec`'s level adds `+1` to the max-children, so
  `≤ 2` ⟹ `max(...) ≤ 1`.  The spec's comment "simrec
  adds 1 to max-children" is correct but the actual
  Lean derivation needs `unfold KMor1.level at hyp;
  Nat.le_of_succ_le_succ; le_trans (le_max_left ...) ...`.
  Use the existing
  `LawvereKSimPolynomialBound.lean` simrec case (lines
  239–268) as template.
- **Proposed fix**: replace placeholder with explicit
  derivation as in finding 11.

### 13. Atomic `level` hypothesis at `KMor1.zero (n := 1)` test

- **Severity**: minor (test correctness).
- **Location**: §8.1 (lines 611–615, 622–626).
- **Issue**: `(KMor1.zero (n := 1)).level` needs to
  reduce to a concrete `Nat` for `by decide` to close
  `... ≤ 1`.  `KMor1.level` for `zero` is `0`, fine.
  But `KMor1.proj (0 : Fin 2)` similarly: level 0, fine.
  `KMor1.succ` arity is `1`, level `0`, fine.
  However, `addK : KMor1 2` is `KMor1.simrec ⟨0, by decide⟩ ...`
  — its level depends on the children's levels.  The
  step is `KMor1.comp KMor1.succ (fun _ => KMor1.proj ⟨2, by decide⟩)`
  but `KMor1.proj ⟨2, _⟩` only typechecks if the simrec's
  step arity is `≥ 3`, i.e. `a + 1 + (k+1) ≥ 3` with
  `a = 1, k = 0` ⟹ `1 + 1 + 1 = 3` exactly.  Good, but
  `Fin 3` requires `2 < 3`.  `⟨2, by decide⟩` works.
  However, the spec writes `addK : KMor1 2` but the
  `simrec` constructor takes `KMor1 (a+1) = KMor1 2`, fine.
- More: `addK.level` reduces by `decide` only because
  level computes by recursion on the inductive
  structure with `Finset.univ.sup` which IS decidable
  for finite types but might be slow.  At `k = 0`,
  `Finset.univ : Finset (Fin 1)` has a single element,
  so `sup` is a single function call — fine.
  `Finset.univ.sup (fun _ : Fin 1 => succ_term.level)`
  reduces.
- **Proposed fix**: none (no actual bug), but the
  implementer should verify `decide` terminates
  quickly on `addK.level = 1` — if it stalls, replace
  with `by simp [KMor1.level, ...]; decide` or an
  explicit `rfl`.

### 14. §8.1 final concrete-input `#guard` runtime risk

- **Severity**: blocker (test feasibility).
- **Location**: §8.1 lines 635–644.
- **Issue**: per CLAUDE.md memory note "ER /
  Gödel-numbering interp not safe for `#guard`":
  `(ERMor1.A_two_iter p.1).interp ![max 1 1 + p.2]`
  with `p.1 = 2` and `p.2 ≥ 2` reduces to
  `tower 2 (vMax + p.2) = 2^(2^(vMax + p.2))`.  At
  `addK`'s majorize, `p.2` is some accumulated value
  ≥ 4 (from r_H + r_G + o_H + o_G + 2) — so the kernel
  has to evaluate `2^(2^6) = 2^64`, which is a
  64-bit-sized Nat literal.  Then the `≤` decide
  comparison against `2` is fast in principle.  But
  `interp_A_two_iter` is a simp lemma, not a definitional
  unfolding — `decide` does NOT use simp.  The kernel
  evaluation goes through `A_two_iter = ERMor1.towerER`,
  which expands `expER`-style ER trees.  The expansion
  size at `r = 2` is bounded but not small, and the
  kernel evaluator on ER tree structures is the exact
  thing the memory note flags as "ran for ages".
- **Proposed fix**: replace concrete-input `#guards`
  with `example : ... := by ...` proof terms that go
  through `interp_A_two_iter`'s simp lemma.  Or pin
  inputs so small (`vMax = 0, p.2 = 0`) that the
  tower evaluates quickly.  Master design's existing
  `addK`-level test in `LawvereKSimInterp.lean` should
  be checked for whether it uses concrete inputs and
  succeeds — if not, the spec's #guard pattern will
  hang the build.

### 15. `vMax_cons` lemma may not exist with that signature

- **Severity**: minor.
- **Location**: §6.4 third bullet (lines 554–558); §9.6.
- **Issue**: `Fin.cons` returns a `Fin (a+1) → ℕ`.
  Mathlib's `Finset.sup`-of-`Fin.cons` is not a
  standard lemma name.  `Fin.sup_cons` doesn't exist
  in mathlib (I cannot confirm via this review but
  loogle would).  Manual proof via
  `Finset.sup_insert` + `Fin.univ_succ` might work,
  but indexing `Fin (a+1)` by 0 vs by `succ` requires
  care.
- **Proposed fix**: write the manual proof as the
  baseline and treat any mathlib lemma as a bonus —
  the spec already says "fall back to manual induction
  if no direct mathlib lemma applies" (line 730), so
  this is acknowledged but worth pinning down: state
  the lemma's manual-proof outline explicitly.

### 16. §7 step-5 bridge lemma's `comp` arity

- **Severity**: blocker (typecheck).
- **Location**: §7 (lines 572–579).
- **Issue**: claimed:
  `ERMor1.comp (ERMor1.A_two_iter p.1) ![ERMor1.sumCtxERPlusOffset a p.2]`.
  `ERMor1.A_two_iter p.1 : ERMor1 1`, so the family
  `gs : Fin 1 → ERMor1 a` is the singleton
  `![ERMor1.sumCtxERPlusOffset a p.2]`.  But
  `sumCtxERPlusOffset a p.2 : ERMor1 a` matches the
  ambient arity. Good.  However `ERMor1.comp` likely
  expects `gs : Fin b → ERMor1 a` where `b` is the
  arity of the outer morphism — `b = 1` here.
  `![...] : Fin 1 → ERMor1 a` requires the entry to
  have type `ERMor1 a`.  `sumCtxERPlusOffset a p.2`
  has type `ERMor1 a` (where `a` is the original arity
  passed to majorize) — but the spec's signature
  `(v : Fin a → ℕ)` matches.  Looks correct.
- However: the existing `ERMor1.comp` signature in
  this codebase needs verification — confirm whether
  it's curried `comp f gs` or `comp gs f`, and confirm
  `![...]`-syntax produces a `Fin n → ERMor1 a` or a
  different type.  `Fin.cons`-based vector-literal
  syntax is the canonical Lean 4 way, but
  `![ERMor1.sumCtxERPlusOffset a p.2]` for a length-1
  vector might be ambiguous (the elaborator may
  prefer `Fin (n+1) → α` shape).
- **Proposed fix**: spell out the type ascription:
  `(fun _ : Fin 1 => ERMor1.sumCtxERPlusOffset a p.2)`,
  which avoids any `![...]` elaboration risk.  Apply
  the same ascription throughout §3 / §7.

### 17. `sumCtxER (n+1)` constructor uses `match i with | ⟨0, _⟩ | ⟨1, _⟩` — exhaustiveness

- **Severity**: minor.
- **Location**: §3.1 (lines 195–203).
- **Issue**: `addN`'s arity is 2, so `gs : Fin 2 → ERMor1 (n+1)`.
  The pattern match handles `⟨0, _⟩` and `⟨1, _⟩`; Lean's
  exhaustiveness check accepts this for `Fin 2` (both
  values exhausted).  Fine.  But the construction
  `comp (sumCtxER n) (fun j : Fin n => proj (Fin.castSucc j))`
  recursively builds an `ERMor1 (n+1)` from
  `sumCtxER n : ERMor1 n` — termination check on
  `n + 1 → n` is structural, fine.
- However: at the `n = 0` clause `zeroN 0 : ERMor1 0`,
  the type is `ERMor1 0`, NOT `ERMor1 0`.  Is `zeroN 0`
  defined?  `zeroN n : ERMor1 n` is the constant-zero
  morphism of arity `n`.  At `n = 0`, that's a function
  `Fin 0 → ℕ → ℕ` = `Fin 0 → ℕ`, an `ERMor1 0` — fine.
  `interp_zeroN` should give `(zeroN 0).interp v = 0`
  for any `v : Fin 0 → ℕ` = `Fin.elim0`-typed.  At `n = 0`
  the sum is `∑ i : Fin 0, v i = 0`.  Equality holds.
  No bug here, just confirm `zeroN 0` is in
  `ERArith.lean` (or similar) — search shows `zeroN`
  exists.
- **Proposed fix**: confirm `ERMor1.zeroN` is indeed
  defined for arity `0` (search shows `interp_zeroN`
  exists; check `def zeroN : (n : ℕ) → ERMor1 n` is
  total — likely yes).

### 18. Spec uses banned word "key" once

- **Severity**: nit.
- **Location**: §9.6 line 728 — "interacts cleanly
  with `Finset.univ.sup`".  Actually no — re-checking:
  no banned word here.
- Re-scan: §1.2 line 65 "no anyone's job" — fine.
  §3.1 lines 187–192 — fine.  §6.2 line 461 "M_n
  closed-form inductive proof" — fine.  §6.2 line 462
  "the level-2 case" — fine.  §6.4 line 559
  `tower_compose_offsets` — fine.
- However: §9.4 line 698 "`simrecVec_le_A_one_iter`'s
  succ-case proof is the largest single proof in the
  cycle" — "largest" is fine.  No banned-word
  violation found.
- **Proposed fix**: none.  The spec passes the
  banned-word check.

### 19. §3.1 `interp_sumCtxER` proof outline cites the wrong sum-induction lemma

- **Severity**: minor.
- **Location**: §3.1 lines 211–212.
- **Issue**: the recursive structure puts
  `proj (Fin.last n)` first and `sumCtxER n ∘ castSucc`
  second.  `interp_sumCtxER (n+1)` reduces to
  `v (Fin.last n) + (sumCtxER n).interp (v ∘ castSucc)`
  = `v (Fin.last n) + ∑ j : Fin n, v (castSucc j)`.
  This matches `Fin.sum_univ_castSucc` (which is
  `∑ i : Fin (n+1), f i = ∑ i : Fin n, f (castSucc i) + f (Fin.last n)`),
  not `Fin.sum_univ_succ`.  Both are listed; the
  first is the relevant one.
- **Proposed fix**: in §3.1 line 211 hint, drop
  `Fin.sum_univ_succ` and keep `Fin.sum_univ_castSucc`
  to avoid confusion.

### 20. §1.2 list of helpers includes `vMax_le_sumCtxER` but signature uses `Finset.sup`

- **Severity**: minor (consistency).
- **Location**: §1.2 line 45 vs §3.1 lines 215–218.
- **Issue**: §1.2 names the helper `vMax_le_sumCtxER`
  but §3.1's signature is in terms of
  `(Finset.univ : Finset (Fin n)).sup v`, NOT `vMax v`.
  If `vMax` is defined exactly as that `Finset.sup`
  expression, the two are interchangeable — but the
  spec doesn't define `vMax` (see finding 4).
- **Proposed fix**: see finding 4.  Pin `vMax`'s
  definition in §2.1 and use it consistently.

### 21. §6.2 hypothesis `(g_fam j).interp y` when `y : Fin (a + 1 + (k+1)) → ℕ`

- **Severity**: blocker (typecheck).
- **Location**: §6.2 lines 474–476.
- **Issue**: `g_fam j : KMor1 (a + 1 + (k + 1))`, so
  `(g_fam j).interp y` requires
  `y : Fin (a + 1 + (k + 1)) → ℕ`.  The spec writes
  `∀ j y, (g_fam j).interp y ≤ A_one_iter r_G ![vMax y + o_G]`.
  `vMax y` then uses
  `(Finset.univ : Finset (Fin (a + 1 + (k + 1)))).sup y`.
  Fine in principle.  But the level-1 hypothesis `hg j`
  produces a level-1 bound at the *full* arity
  `a + 1 + (k + 1)`, which is not the same as the
  outer `KMor1 a` arity.  When the simrec proof
  applies `hstep j` at the `stepCtx` constructed inside
  `simrecVec_succ`, the `stepCtx` has arity
  `a + 1 + (k + 1)`, fine.
- However: the `r_G, o_G` produced by `majorize_one`
  on `g_fam j` are obtained inside `KMor1.majorize`'s
  simrec case at lines 416–421 — but those calls
  feed `g_fam j : KMor1 (a + 1 + (k + 1))` into
  `majorize_one`, which produces `(r, offset)`
  appropriate for that *higher* arity.  The
  `simrecVec_le_A_one_iter` lemma threads
  `r_G, o_G` correctly.  Looks consistent.
- **Proposed fix**: none (no bug), but call out
  in §6.2's docstring that `r_G`/`o_G` are the
  level-1 majorants of `g_fam j` at arity
  `a + 1 + (k + 1)`, NOT at arity `a`.

### 22. §8.2 re-export ordering at skeleton-creation time risks build break

- **Severity**: minor.
- **Location**: §2.3 + §8.2 (lines 156–164, 658–663).
- **Issue**: spec mandates registering imports in
  `GebLean.lean` and `GebLeanTests.lean` at
  skeleton-creation, before any code is added.
  This works only if the empty module typechecks —
  `import` lines plus `namespace GebLean` should be
  enough.  But Lean elaborates imports eagerly; if
  any of the listed imports fail to resolve (e.g.
  `Mathlib.Algebra.BigOperators.Fin` may not be the
  exact module path), the empty file fails build,
  and so does every module that imports it
  transitively.
- **Proposed fix**: in §2.1, verify each mathlib
  import path against the current toolchain's
  mathlib.  At least
  `Mathlib.Algebra.BigOperators.Fin` is correct;
  `Mathlib.Data.Nat.Log` is correct (in current
  mathlib).  Confirm at task-1 implementation time
  via `lake build`.

### 23. Master-design citation precision

- **Severity**: nit.
- **Location**: §3.1 line 190 ("Master design §3.5
  lines 1108–1113").
- **Issue**: lines 1108–1113 of master design are the
  `kToER` simrec case's prose comment about
  `sumCtxER` dominating `maxCtx` pointwise.  That's
  the right citation for `sumCtxER`'s purpose, but
  the actual `sumCtxER` named composite is built in
  step 4 — there's no master-design definition of
  `sumCtxER` itself.  Citation is for the consumer
  context, not the definition.  Acceptable per
  literature-citation discipline ("cite the
  proposition the construct corresponds to") since
  master design §3.5 is the only place `sumCtxER`
  appears in the literature pipeline.
- **Proposed fix**: none, but during implementation,
  cross-reference to a step-4 spec/plan section in
  the docstring as well as the master design line
  range.

### 24. §6.3 `raise` case proof — hides `interp_raise` reduction

- **Severity**: minor.
- **Location**: §6.3 raise bullet (lines 533–538).
- **Issue**: `(raise f).interp = f.interp` per
  `interp_raise` (existing `@[simp]` at
  `LawvereKSimInterp.lean` line 104).  The proof
  outline says "transfers the bound directly" — but
  needs to match the `KMor1.majorize` def's `raise`
  branch output `(2, p.2 + p.1 + 2)` against the
  conversion via `A_one_iter_le_A_two_iter_two`.  At
  `raise f` with `p = (k, o)`, the level-1
  bound is `f.interp v ≤ A_1^k(vMax v + o)`.  By
  γ corollary, `A_1^k(x) ≤ A_2^2(x + k + 2)`.  At
  `x = vMax v + o`, get `A_2^2(vMax v + o + k + 2)`.
  Spec assigns `(2, o + k + 2)` — matches.  But
  the spec writes `(2, p.2 + p.1 + 2)` —
  `p.2 + p.1 = o + k`, `+ 2` gives `o + k + 2`,
  consistent.
- **Proposed fix**: none, but spec should verify
  `interp_raise` is a `@[simp]` lemma in scope (it
  is, per LawvereKSimInterp.lean:104).

## Summary

- Blockers: 5 (findings 1, 2, 4, 14, 16, 21 — finding 21 is
  conditional; counted: 1, 2, 4, 14, 16 = 5).
- Major: 4 (findings 3, 6, 7, 9).
- Minor: 11 (findings 5, 8, 10, 11, 12, 13, 15, 17, 19, 20,
  22, 24 = 12; recount).
- Nit: 2 (findings 18, 23).

Recount:

- Blocker: 1, 2, 4, 14, 16 = **5**.
- Major: 3, 6, 7, 9 = **4**.
- Minor: 5, 8, 10, 11, 12, 13, 15, 17, 19, 20, 21, 22, 24 = **13**.
- Nit: 18, 23 = **2**.
- Total: 24.

The dominant blocker is finding 1 (level-2 simrec → A_2
reduction): the spec's γ.3 chain doesn't perform the
master-design absorption step that turns the
`n`-dependent A_1 exponent into a constant-offset A_2
bound.  Without that, the level-2 majorization theorem
cannot close.  The fix is a new γ-family lemma matching
master-design line 1027 directly, plus restating §6.2's
conclusion in the absorbed form.

Findings 2, 3 are downstream consequences of finding 1 and
should be re-evaluated after the §6.2 conclusion is
restated.

Findings 4 (vMax pin), 14 (decide on tower 2 6), 16
(comp arity ascription) are independent typecheck/runtime
risks the implementer will hit on first build.

Findings 9, 11, 12 are proof-tactic gaps that need
explicit lemma references; they will surface during
implementation and should be filled in advance for
smooth execution.
