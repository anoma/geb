# Round-4 adversarial review — erToK via Tourlakis URM simulation

Reviewer: fresh-context `general-purpose` Agent (round 4).
Artefact under review:
[`2026-05-16-er-to-k-via-cslib-urm-design.md`](2026-05-16-er-to-k-via-cslib-urm-design.md).
Prior rounds:
[`.review-1.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-1.md),
[`.review-2.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-2.md),
[`.review-3.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-3.md).

Author response convention as in prior rounds.

## Citation verification log

External (Tourlakis 2018) verified at PDF for every
section cited (§0.1.0.2, .4, .7, .9, .17 (subitems
1/3/4/6/a/b/c), .20, .27, .36, .37, .42, .43, .44 plus
pp. 19–21 worked examples). All PASS.

Internal repository line references: all verified.
`signum` cited at `KArith.lean:420` is `private` — see
Minor M4 below.

## Other verification log

**Constructive discipline** preserved (`Fin.find`, no
`Classical.choose`). PASS.

**§6.2 / §7.1 level claims** verified via `KMor1.level`
trace at `LawvereKSim.lean:105`. Step at level 1; simrec
adds 1 → level 2. `boundExprK` is composition of level-2
terms → level 2. PASS.

**§5.1 walkthrough for `comp sub [proj 0, proj 0]` at
arity 1, input `v = [3]`.** With `k_0 = 2` pre-clones,
both `proj 0` consumers read 3 destructively from
distinct scratch registers; outer `sub` computes 3 − 3
= 0. ✓

**§6.1 recursion equations vs Tourlakis p. 16.** Match
under 1-indexed → 0-indexed PC shift. PASS.

**§8.1 erToK formula vs §0.1.0.44 p. 22.** Matches.
PASS.

**No leftover round-1 references** on the load-bearing
path. PASS.

## Findings

### Blocker

(None.)

### Serious

#### S1. §5.1 `ERMor1.sub` template has wrong loop variable

Spec text: "Derived Loop program `Loop X { Z ← Z ∸ 1 }
end` with Z initialised to X". The §0.1.0.17(a)
recursion `x ∸ 0 = x`, `x ∸ (y+1) = (x ∸ y) ∸ 1`
recurses on the *second* argument `y`. The natural
loop-program realisation is `Z := x; Loop Y { Z ← Z
∸ 1 } end`, looping `y` times. The spec writes `Loop
X`, which would loop `x` times — wrong for `λxy.x ∸ y`
when `y < x`.

**Response:** fix. Replace `Loop X` with `Loop Y` and
note Z is initialised from X (the first argument).

#### S2. §5.1 `bsum`/`bprod` per-iteration plumbing under-specified

Inside `bsum f`'s outer loop, on each iteration: (a)
`f`'s slot-0 input must be set to the current loop
index, and (b) `f`'s outer-parameter input slots must
be re-prepared (since `compileER f`'s body consumes
them destructively). The pre-clone-at-prelude
discipline runs once at PC 0; it does not re-clone
across iterations of an outer loop. Without explicit
per-iteration setup, the second iteration reads zeroed
registers.

**Response:** fix. Add a per-iteration prologue to
`bsum f`'s outer-loop body: at the top of each
iteration, (i) write the current iteration counter
into `f`'s slot-0 scratch, (ii) re-clone any
outer-parameter input slots by emitting per-iteration
preserving-transfer blocks (analogous to the prelude
clones but inside the outer loop). Same for `bprod f`.
Specify in §5.1 that the per-iteration prologue is
part of the `bsum`/`bprod` template, not delegated to
`compileER f`.

### Minor

#### M1. §5.1 "two-loop pattern" overstates the cited source

PDF pp. 19–20 contain analogous decoupling tricks (the
per-Loop scratch B on p. 20) but not the literal
preserving-transfer idiom claimed.

**Response:** fix. Reword to "standard register-machine
idiom; the decoupling pattern is analogous to
Tourlakis's per-Loop scratch register B (p. 20)".

#### M2. §7.3 statement form

`∃ t, … = t ∧ ∀ s ≥ t, …` is equivalent to a direct
universal. Tighten.

**Response:** fix. Rewrite as `∀ s ≥ (boundExprK
e).interp v, …`.

#### M3. §8.3 step 1 parenthesisation ambiguous

`(simulate ...).interp (Fin.cons (boundExprK e).interp
v, v)` reads as a pair. Clarify.

**Response:** fix. Replace with explicit application:
`(simulate (compileER e)).interp (Fin.cons
((boundExprK e).interp v) v) = ...`.

#### M4. §3 row for `KMor1.signum` (private)

Cited at `KArith.lean:420`, which is `private`. Either
omit from the inventory or annotate.

**Response:** fix. Annotate "(private; internal
helper)".

#### M5. §3.1 `KMor1.natK` arity coercion implicit

`natK c : KMor1 0` is used inside `KMor1`-valued
contexts of arity > 0 (e.g. branches inside the
simrec's step function). The implicit arity lift via
`KMor1.comp` is mechanical and level-preserving but
unnamed in the spec.

**Response:** fix. Add a one-line note: "When used
inside a `KMor1 n`-valued context, `natK c` is lifted
via `KMor1.comp (natK c) Fin.elim0`; the lift is level
0."

### Cosmetic-taste

#### C1. §6.1 alternative-route note for §0.1.0.20

§0.1.0.20 establishes the predicate; §6.2 realises PC
dispatch via `pred^k`. Move §0.1.0.20 reference to the
ambient citation list.

**Response:** fix. Mention §0.1.0.20 as alternative
once; otherwise leave §6.2's `pred^k` route as the
primary.

#### C2. §3.1 `pow2_iter` entry's defensive metacommentary

"the Ackermann iteration is referenced in Tourlakis
outside the 25-page PDF excerpt the project has" reads
defensively.

**Response:** fix. Replace with neutral phrasing.

#### C3. §11 cross-reference to master design

A one-line T-to-old-step mapping table would aid
navigation.

**Response:** reject-as-cosmetic-taste (current prose
suffices; the master design's step numbering is
referenced once in §1's scope statement, not
load-bearing for §11 to repeat).

## Convergence assessment

Round does NOT converge: 0 blocker(s), 2 serious
finding(s).
