# Adversarial review (round 3) of the ER ↔ K^sim_2 master design

> Reviewer's stance: fresh adversarial reading after round-2
> revisions, with no acceptance of design framing on faith.
> Source materials re-checked: master design end-to-end (current
> revision), `LawvereKSim.lean:50-54` (simrec arity), Tourlakis
> 2018 pp. 21-22 (the ⊆ proof), `Utilities/ERArith.lean` (named
> composites), `Utilities/ComputationalComplexity.lean` (tower
> lemmas), `LawvereERBoundComputable.lean` (`sumCtxER`
> existence), `GebLean/` grep for `maxCtxER` and other
> referenced entities.

## Overall assessment

**The design is now sound and is ready to begin step 1's
cycle.** All six round-2 defects (G1-G6) and the F7 prose
loose-end have been correctly addressed. The §3.4 level-2
prose proof remains arithmetically valid on independent
re-verification, the §3.5 simrec case correctly uses
`KMor1.majorize_r f h` (constructive, no `.choose`), and the
§3.2 `simultaneousBoundedRec` bound contract is now
explicitly specified as "component bound, with the
implementation deriving the packed-state bound internally"
— matching what §3.5 supplies.

Two small residual issues remain (H1, H2 below) — both
naming/reference defects that can be folded into step 1's
preamble without affecting any substantive design decision.
Neither blocks the start of step 1's cycle.

**No further round of adversarial review needed before step 1
begins.**

---

## Round-2 fix verification

### G1 (dangling §6.3, §7.3, §9.4 references) — FIXED

`grep` for `§6\.3`, `§7\.3`, `§9\.4` returns no hits in the
master design. All six dangling references identified in
round 2 have been removed or re-pointed. Verdict: **correct**.

### G2 (`boundExpr f` in §13.1) — FIXED

§13.1 line 1903-1906 now reads:
"`LawvereERPolynomialBound.lean`'s `ERMor1.PolyBound` and
builders — used by Path 2 kToER for the `A_n^r` named
composites (§3.3) and for ER expressions internal to
`boundExprK e`'s K^sim construction (§9)."

The Path-1 entity name `boundExpr f` appears once at line
1581 inside §9's prose — there it correctly identifies the
**retired** Path-1 entity ("The Path-1 `boundExpr f : ERMor1
a` ... is no longer built"), not as a load-bearing
reference. Verdict: **correct**.

### G3 (`.choose` against split theorem) — FIXED

§3.5 line 990 now reads `let r := KMor1.majorize_r f h`,
matching the §3.4 split into `def KMor1.majorize_r` and
`theorem KMor1.majorize_by_A_two_iter`. No `.choose`
remains in the §3.5 simrec case. Constructive discipline is
preserved. Verdict: **correct**.

### G4 (`simultaneousBoundedRec` bound contract) — FIXED

§3.2 lines 628-639 now explicitly state:

> **Bound-input contract.** `componentBound` is a bound on
> each individual component value at every iteration: `f_j(n,
> x⃗) ≤ componentBound.interp (n, x⃗)` for all `j`. The
> implementation derives the packed-state bound internally
> (by composing with the §3.1 `tuplePack` polynomial bound:
> packed state `≤ (componentBound + c_{k+1})^{2^{k+1}}`), so
> callers do NOT need to provide a packed-state bound. This
> matches the F2-fixed `Nat.tuplePack_le` formula and is what
> the level-2 majorization in §3.4 supplies (the `A_2^2(vMax v
> + offset)` bound is on each component, not on the packed
> tuple).

The implementation outline (lines 657-675) now derives the
packed-state bound from `componentBound` in step 2 of the
outline, before applying `boundedRec`. The tower-height
arithmetic (lines 681-688) verifies that for `componentBound`
at height ≥ 2, the packed-state bound stays at the same
height by `tower_succ_pow_bound_strong`.

Independent arithmetic check: with `componentBound = 2^{2^N}`
(height 2) and packed bound shape `(componentBound +
c_{k+1})^{2^{k+1}}`, we get
`(2^{2^N} + c)^{2^{k+1}} ≤ 2^{(2^N + 1)·2^{k+1}}
≤ 2^{2^{N+k+2}}` (the last step uses
`(2^N + 1)·2^{k+1} ≤ 2^{N+k+2}` which holds for `N ≥ 1` since
`2^N + 1 ≤ 2^{N+1}`). So packed bound stays at height 2
with offset shift `+ k + 2`. ✓

Verdict: **correct**.

### G5 (§15.12 sync with §3.1) — FIXED

§15.12 line 2258 now reads:
> `tuplePack k v ≤ (M + c_k)^{2^k}` for `M = max v` and
> explicit constants `c_k` derived by the recurrence
> `B_{k+1} ≤ (M + B_k + 2)^2` (per §3.1).

This matches §3.1 line 543-553. Verdict: **correct**.

### G6 (§16.4 typo `§15.1-14.10`) — FIXED

§16.4 line 2370-2371 now reads "§15.1 through §15.16".
Verdict: **correct**.

### F7 (prose loose-end, c=d=0 saying r=0) — FIXED

§3.4 lines 792-794 now reconcile the formula and the
boundary case explicitly:
> `c = 0, d = 0`: the formula gives `r = max 0 1 = 1`
> (`A_1^1(x) = 2x + 2 ≥ 0`); `r = 0` would also be valid
> (`A_1^0(x) = x ≥ 0`) but the formula picks `r = 1`.

Verdict: **correct**.

---

## New issues from round 2 edits

### H1 — `ERMor1.maxCtxER` referenced in §3.5 but not defined anywhere (minor defect)

**Claim.** §3.5 line 992-993 builds the `bound` as:
```
ERMor1.comp (ERMor1.A_two_iter r) ![ERMor1.maxCtxER (a + 1)]
```

**Verification.**  `grep -rn "maxCtxER" /home/terence/git-workspaces/geb/geb-lean/GebLean/`
returns no hits. The codebase has `sumCtxER` (in
`LawvereERBoundComputable.lean:277`) but not `maxCtxER`.
The §3.5 simrec case introduces `maxCtxER` as a named
composite without specifying its construction or which
step's cycle builds it.

**Why this matters.** The `bound` argument to
`simultaneousBoundedRec` per §3.2's contract is
`componentBound`, which must dominate each `F_j(n, x⃗)`. The
level-2 majorization theorem in §3.4 gives
`F_j(n, x⃗) ≤ A_2^r(vMax v)` (where `vMax v = max_i (v i)`,
i.e., the maximum component of the input vector — for the
inner simrec view, `v = (n, x⃗)`). So
`componentBound = A_2^r ∘ maxCtxER` is the right shape, but
`maxCtxER` as such is not a named composite that exists
yet, and the current `sumCtxER` (which dominates
`maxCtx`) would also work and is an acceptable substitute
since `A_2^r` is monotone.

**Verdict.** Minor defect. Either add `maxCtxER` to step 1's
cycle as a new named composite (with `interp =
Fin.foldr max 0`), or change §3.5 to use `sumCtxER` and
note the looseness is absorbed into `A_2^r`'s monotonicity.

**Recommended action.** Add a one-line note to step 1's
cycle (or the §3.7 module layout) clarifying which named
composite is built. Not a blocker for step 1 starting.

### H2 — `polynomial_iter_tower_two_bound` reference name does not exist (minor defect)

**Claim.** §13.1 line 1900-1902:
> `Utilities/ComputationalComplexity.lean`'s
> `polynomial_iter_tower_two_bound` — `urmLoop` tower
> arithmetic (§5.3).

**Verification.**  `grep -n "polynomial_iter_tower" Utilities/
ComputationalComplexity.lean` shows the actual theorem name
is `polynomial_iter_tower_bound` (line 483), not
`polynomial_iter_tower_two_bound`. The latter appears only
in a docstring comment (line 342).

**Verdict.** Minor naming defect (carried forward from
earlier design revisions, not introduced by round 2 edits;
prior reviews missed it).

**Recommended action.** Update §13.1 line 1901 to
`polynomial_iter_tower_bound`.

---

## Issues missed by prior rounds

### J1 — `r := majorize_r f h` produces an `r` for `A_2^r(vMax v)`, not `A_2^2(vMax v + offset_2)` (needs-clarification, not a defect)

**Claim being challenged.** §3.4's prose proof concludes
`f.interp v ≤ A_2^2(vMax v + offset_2)` with `r_2 = 2,
offset_2 = r_H + r_G + 2`. But the Lean theorem statement
(lines 812-815) reads:
```
f.interp v ≤ (ERMor1.A_two_iter (KMor1.majorize_r f h)).interp ![vMax v]
```
i.e., `A_2^{majorize_r f h}(vMax v)` with no explicit
offset. The translation from `A_2^2(y + c)` to `A_2^r(y)`
absorbs the offset into the iteration count.

**Verification.** For `c ≥ 0` and `y ≥ 1`,
`A_2^2(y + c) = 2^{2^{y+c}} = 2^{2^c · 2^y}`. We have
`2^c · 2^y ≤ 2^{2^{y}}` for `y` large enough that `2^y ≥ c
+ y` (true for `y ≥ ⌈log_2 c⌉ + 1`). So
`A_2^2(y+c) ≤ 2^{2^{2^y}} = A_2^3(y)` for `y ≥ ⌈log_2 c⌉ +
1`. For small `y`, take a larger `r` to dominate: there
exists a Lean-`Nat` `r := r(c)` such that `A_2^2(y + c) ≤
A_2^r(y)` for all `y`. This is the absorbed `r =
majorize_r f h`.

**Verdict.** Not a defect. The design defers the precise
absorption formula to step 4's cycle ("Concrete formulas:
step 4's cycle"). The prose proof produces a witness shape
`A_2^2(y + offset)`, and absorbing `offset` into the
iteration count to land at `A_2^r(y)` is mechanical.

But step 4's adversarial review must explicitly verify the
absorption goes through at the boundary `y = 0` (where
`A_2^r(0) = ?`). Note: `A_2(0) = 2^0 = 1`, `A_2^2(0) =
2^1 = 2`, ..., `A_2^r(0) = ⏟tower of 2's of height
r-1⏟`. So `A_2^r(0)` grows fast in `r`, and absorbing any
fixed offset into `r` gives a valid dominating bound at
all inputs ≥ 0.

**Recommended action.** Step 4's cycle must include an
explicit `Nat`-valued absorption helper
`A_2_iter_offset_absorb (offset : ℕ) : ℕ` such that for all
`y`, `A_2^2(y + offset) ≤ A_2^{2 + A_2_iter_offset_absorb
offset}(y)` (or some similar concrete shape). The current
design's deferral is acceptable but step 4 must surface
this absorption as a named lemma.

### J2 — §3.2 implementation outline assumes `componentBound`'s tower height ≥ 2 (needs-clarification)

**Claim being challenged.** §3.2 lines 681-688:
> If `componentBound` is at ER tower height `h_c`, the
> packed-state bound (derived in step 2) is at most height
> `max(h_c, 2) + 0` once `h_c ≥ 2`.

**Verification.** This is the strong height-fixed property
of `tower_succ_pow_bound_strong`. For `h_c < 2`, the bound
might bump up. The §3.5 simrec case always supplies
`componentBound = A_2^r ∘ maxCtxER` at height 2 (since
`A_2 = expER` which raises height by 1 above its argument's
height; iterated to height 2 from height-0 `maxCtxER`).

**Verdict.** Not a defect at the call site, but the §3.2
contract doesn't formally exclude callers from passing
height-0 or height-1 component bounds. The interface
should clarify: either the contract requires `h_c ≥ 2`
(and `kToER`'s call site verifies it), or the
implementation must handle the height-bump case.

**Recommended action.** Step 2's cycle should explicitly
document whether `simultaneousBoundedRec` requires
`componentBound` at height ≥ 2, or whether it handles
lower heights via an extra inflation. Not a blocker.

### J3 — Level-2 `comp` and `raise` cases of `majorize_by_A_two_iter` are deferred (acceptable but flagged)

**Claim being challenged.** §3.4 line 947-951:
> **Recursive comp / raise cases.** For `comp f gs` and
> `raise f`: the bound is built bottom-up from children's
> bounds, with the height staying at 2 (or below) by Module
> A's `tower_succ_pow_bound_strong` (height-fixed for
> `h ≥ 2`). Concrete formulas: step 4's cycle.

**Verification.** The `comp` and `raise` cases are
substantive (especially `comp` of `A_2^r`-bounded children).
For `raise f` with `f : KMor1 a` of level ≤ 1, we pass
through to the level-1 majorant `A_1^{r_1}`, then apply
`linearBound_le_A_one_iter`-equivalent bridge to get
`A_2^?`. For `comp f gs` at level 2 with level-2 `f` and
level ≤ 2 `gs` children, we compose two `A_2^r`-bounded
expressions, requiring something like `A_2^{r_1}(A_2^{r_2}(y))
≤ A_2^{r_1 + r_2}(y)` (which holds by definition).

**Verdict.** Not a defect; the algebra is straightforward.
Step 4's adversarial review must verify each constructor
case yields a valid `r`-bound and that the recursion
terminates at the level-0/level-1 base cases via
`linearBound_le_A_one_iter`. The bottom-up structural
induction shape is well-specified by §3.4.

### J4 — §3.4 prose proof's "n ≥ max x⃗" regime restriction is not maintained in formal statement (cosmetic)

**Claim being challenged.** §3.4 line 867-869:
> For `n ≥ max x⃗` (the only regime that matters; smaller
> inputs give smaller bounds), we have `max(n, max x⃗) =
> n`, so `M_{n+1} ≤ A_1^{r_G}(max(n, M_n))`.

**Verification.** This restriction is a prose
simplification. The formal Lean statement of
`majorize_by_A_two_iter` makes no such restriction — it
holds for all `v`. The full proof must therefore handle
`n < max x⃗` separately, which the prose elides. Round 2's
verification noted this and confirmed the stronger formula
holds without the restriction:
> `max(n, max x⃗, M_n) ≤ max(n, max x⃗,
> A_1^{r_H+n·r_G}(max(n, max x⃗))) = A_1^{r_H+n·r_G}(max(n,
> max x⃗))` because the third term dominates.

So the prose's regime-restriction is a presentation
shortcut, not a logical gap. The full formal proof
naturally handles all `n, max x⃗`.

**Verdict.** Cosmetic. Step 4's Lean realization should
either (a) handle the general case directly via the
"max-of-three dominated by A_1^k" argument, or (b)
explicitly do a case split on `n vs max x⃗` and reduce
both to the regime-restricted argument.

### J5 — erToK side (§4-§9) self-consistency under Path 2

**Spot-check.** Tracing the erToK chain:

- §4-§5 (URM kernel + combinators): unchanged from prior
  designs; `URMComputes` structure is constructive,
  combinator arithmetic is well-defined.
- §6.1 (URMSubroutinesER): URM realizations of ER atoms.
  Local per-entry `URMComputes`. ✓
- §6.2 (KSimSubroutinesURM): K^sim realizations of URM
  primitives. PC-dispatch via `switch` (Tourlakis
  §0.1.0.17 (6), level 1). Per-instruction step at level
  ≤ 1. Total simulator level ≤ 2 (simrec at level 2). ✓
- §7.1 (`simulateInKSim`): K^sim simrec over time, level
  ≤ 2. ✓
- §8.1 (`compileER`): one-line match per ER constructor,
  invoking §6.1 entries. ✓
- §9.1 (`boundExprK e`): K^sim_2 expression bounding the
  URM compiled stepBound. Uses `2^x ∈ K^sim_2` per
  §0.1.0.17 (c). ✓
- §10.2 (`erToK`): `simulateInKSim (compileER e)` wired
  with `boundExprK e` as the time bound. ✓

The erToK chain is self-consistent. The level grading
(K^sim_2 = level ≤ 2) is preserved at every step. The
only place where the erToK side could trip is if
`switch` (Tourlakis §0.1.0.17 (6)) is genuinely K^sim_1
— which the design asserts but does not realize as a
Lean named composite in this design. Step 9's cycle is
where this gets built.

**Verdict.** No issues found. The erToK side is
self-consistent under Path 2.

---

## Implementability assessment

A reader who knows Lean 4 + mathlib + the existing codebase
should be able to start step 1's cycle from this design.
The ingredients for step 1 are:

1. **`Nat.tuplePack`, `Nat.tupleAt`** — standard k-tuple
   Cantor pairing, recursively defined (§3.1 lines 533-538).
2. **Bijection theorems** (`Nat.tupleAt_tuplePack`,
   `Nat.tuplePack_tupleAt`) — by induction on `k`.
3. **`Nat.tuplePack_le`** — the polynomial value bound;
   the recurrence `B_{k+1} ≤ (M + B_k + 2)^2` reduces to
   `Nat.pair_le_sq` (already in
   `Utilities/ComputationalComplexity.lean`).
4. **`ERMor1.tuplePack`, `ERMor1.tupleAt`** — built from
   `ERMor1.natPair` and `ERMor1.natUnpair*` (existing).
5. **`PolyBound` builders** — using existing per-constructor
   builders.
6. **(Step 1 may also build `ERMor1.maxCtxER` per H1.)**

These are all mechanical given the existing infrastructure.
No architectural questions remain.

---

## Top items the author MUST still address

**None blocking step 1's start.** Two minor housekeeping
items can be folded into step 1's cycle:

1. **H1**: clarify `ERMor1.maxCtxER` (build it as a step-1
   named composite, or substitute `sumCtxER` in §3.5).
2. **H2**: fix §13.1's reference to
   `polynomial_iter_tower_two_bound` →
   `polynomial_iter_tower_bound` (the actual mathlib-
   adjacent name in
   `Utilities/ComputationalComplexity.lean`).

The level-2 prose proof (§3.4), the §3.2
`simultaneousBoundedRec` contract, the §3.5 `kToER`
definition with `KMor1.majorize_r f h` constructive
extraction, and the F2-fixed tuplePack bound formula
`(M + c_k)^{2^k}` are all internally consistent and
mathematically correct.

The Path 2 design is sound and ready for implementation.

**No further round of adversarial review needed before step
1 begins.**

End of round-3 adversarial review.
