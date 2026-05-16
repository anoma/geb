# Round-5 adversarial review — erToK via Tourlakis URM simulation

Reviewer: fresh-context `general-purpose` Agent (round 5).
Artefact under review:
[`2026-05-16-er-to-k-via-cslib-urm-design.md`](2026-05-16-er-to-k-via-cslib-urm-design.md).
Prior rounds:
[`.review-1.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-1.md),
[`.review-2.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-2.md),
[`.review-3.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-3.md),
[`.review-4.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-4.md).

## Citation verification log

All twelve external Tourlakis citations (§0.1.0.2, .4,
.7, .9, .17 with subitems 1/3/4/6/a/b/c, .20, .27, .36,
.37, .42, .43, .44, plus pp. 19–21 worked examples)
verified at the cited pages of the PDF. All PASS.

All internal `File.lean:line` references verified at the
cited line numbers. All PASS.

## Other verification log

**Constructive discipline.** `Fin.find`-based
`URMState.init`; no `noncomputable` or `Classical.choose`.
PASS.

**Level arithmetic.** §6.2 step at level 1; outer simrec
adds 1 → level 2. `boundExprK e` at level 2. `erToK e`
at level 2 by composition (max rule). PASS.

**Per-template walkthroughs.** `sub` at `[5, 3] → 2` ✓.
`bsum (succ ∘ proj 0)` at `[2] → 3` ✓.

**§6.1 vs Tourlakis p. 16.** Recursion equations match
under 0-indexed PC shift. PASS.

**§8.1 vs Tourlakis p. 22.** Matches `f = λx⃗.v_1(A^r_n
(max x⃗), x⃗)`. PASS.

**Dependency graph (§9.1).** Independent of kToER.
PASS.

## Findings

### Blocker

(None.)

### Serious

#### S1. §12.11 vs §5.1 contradiction over reserved-zero register `V_z`

§12.11 asserts that `Z0`/"reserved zero register" appears
only in §2.1's deleted-narrative; the adversary is told
to "expect zero matches". But §5.1 introduces a "reserved
register `V_z` always holding `0`" as the formal encoding
of Tourlakis's informal `goto l`, and this `V_z` is
load-bearing on the §8.3 trace. Internal contradiction.

**Response:** fix. Relax §12.11's grep target list to
exclude `V_z` (which is the §5.1 formal encoding of
`goto l`, materially distinct from round-1's `Z0`
reserved-register-for-equality-jumps over CSLib URM).
The round-1 `Z0` was a workaround for CSLib's
equality-only jump; the round-2+ `V_z` is the standard
formal encoding of Tourlakis's `goto l` shorthand and
is referenced by Tourlakis indirectly (the implicit
"V_z held at 0" convention behind `goto l` patterns in
the M URM, p. 19). Add a §5.1 note: "The `V_z ← 0`
prelude is emitted once at PC 0 in every compiled URM;
no later instruction writes `V_z`. This is the project's
formal encoding of Tourlakis's informal `goto l`
shorthand."

#### S2. §5.1.1 step 2 wording "excluding the bound variable"

`f`'s slot 0 receives the iteration counter `i` (not the
loop's upper bound, which is `ctx 0` of the outer `bsum`
context). The phrase "outer-parameter input slot of `f`
… excluding the bound variable" suggests `f`'s slot 0 is
the bound variable. Admits an off-by-one slot
interpretation.

**Response:** fix. Reword §5.1.1 step 2: "For each
outer-parameter input slot of `f` (slots `1..arity(f) −
1`, i.e. all slots except `f`'s slot 0 which receives
the iteration counter `i` per step 1), re-clone…".

#### S3. §7.3 missing intermediate claim

The proof sketch "combines `compileER_runFor` (§5.2)
with the bound on the runtime witness" requires the
intermediate inequality `t_e(v) ≤ (boundExprK e).interp
v` where `t_e(v)` is the runtime witness from §5.2.
The spec does not name this lemma.

**Response:** fix. Add a §7.3 introductory paragraph
naming the lemma:

> The proof depends on an intermediate
> `boundExprK_majorizes_witness : ∀ v,
> (compileER_runFor e v).choose ≤ (boundExprK e).interp v`
> stating that the K^sim-side bound exceeds the
> Nat-level runtime witness from §5.2. The witness's
> existence is `compileER_runFor`'s `∃ t : ℕ, …`; pin
> the witness by `Classical.choose` (with constructive
> replacement via the explicit recursive bound
> computed during `compileER`'s structural traversal,
> per §7.2's recursion shape).

Actually — strike that response. The whole point of
the spec's constructive discipline is to avoid
`Classical.choose`. The fix is rather to restate §5.2
to return an explicit `t : ℕ` as a Lean-level function
(no ∃), and then §7.3's intermediate inequality
becomes `t_e(v) ≤ (boundExprK e).interp v` with both
sides explicit. Apply this restatement.

### Minor

#### M1. §3.1 `maxOver a` levelling

At `a = 0`, `maxOver 0 = zero` has level 0. Claim
"`maxOver` is level 2" should be "level ≤ 2".

**Response:** fix.

#### M2. §5.1 `bprod` decomposition pointer

Add a one-line note that bprod's per-iteration step
`z ← z · f(i, y⃗)` uses the same loop-to-URM expansion
as bsum's accumulator update, with multiplication
replacing addition.

**Response:** fix.

#### M3. §5.1 bsum row "Outer Loop over the bound variable"

Two registers (loop count `x = ctx 0` and iteration
index `i`); spec conflates them. §5.1.1 distinguishes
them; §5.1 should too.

**Response:** fix.

#### M4. §4.1 invariants

`inputRegs_inj` and `outputReg_not_input` are
independent constraints. Add a comment.

**Response:** fix.

#### M5. §4.3 `URMState.init.pc := 0` comment

Add inline note "Tourlakis I(0) = 1 mapped to 0" for
symmetry with §6.1.

**Response:** fix.

#### M6. §7.1 forward-reference "details in §7.2"

§7.2 defers concretes to implementation. §7.1's promise
should match.

**Response:** fix. Reword §7.1 to say "recursion shape
in §7.2".

### Cosmetic-taste

#### C1. §5.2 wording around §0.1.0.42 vs §0.1.0.43

Spec text "Per Tourlakis §0.1.0.42 (p. 18): …
(Tourlakis §0.1.0.43, p. 21, is the Ritchie–Cobham
equivalence containing this Lemma.)" — concise but
slightly awkward.

**Response:** fix (small wording polish).

#### C2. §8.4 `map_id := /- via erToK_interp -/` placeholder

Spec-level pseudocode placeholder is fine; level
witness is also load-bearing.

**Response:** reject-as-cosmetic-taste (spec form is
appropriate; the level-witness handling is implementation
detail).

#### C3. §13.1 worked-examples bullet terser than §-level bullets

Break into sub-bullets for M, N, R, loop-to-URM, and
bounded-recursion templates.

**Response:** fix.

#### C4. §3 table missing line citation for `cond.level = 1`

Add line 264 alongside line 222 in the `KMor1.cond`
row.

**Response:** fix.

## Convergence assessment

Round 5 finds 0 blockers, 3 serious findings, 6 minor,
4 cosmetic. Citations all check out. Convergence is
close; the three serious items are localised wording
or single-lemma additions, not structural changes. If
round 6 verifies the fixes, the spec is convergent.

Round does NOT converge: 0 blocker(s), 3 serious
finding(s).
