# Round-2 adversarial review — erToK via Tourlakis URM simulation

Reviewer: fresh-context `general-purpose` Agent (round 2).
Artefact under review:
[`2026-05-16-er-to-k-via-cslib-urm-design.md`](2026-05-16-er-to-k-via-cslib-urm-design.md).
Round-1 review:
[`2026-05-16-er-to-k-via-cslib-urm-design.review-1.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-1.md).

Author response convention: each finding is followed by a
single-line `**Response:**` entry recording one of `fix`,
`defer-with-rationale`, or `reject-as-cosmetic-taste`
(cosmetic only). Per
[`docs/process.md` § Adversarial review](../../process.md),
blocker and serious findings cannot be deferred without an
explicit out-of-scope rationale that withstands a later
adversarial round.

## Citation verification log

### §3 inventory table

- `KMor1.zero` cited at `LawvereKSim.lean:36`, Tourlakis
  §0.1.0.2. Verified: file line 36 has `| zero {n : ℕ} :
  KMor1 n`. Tourlakis p. 1 §0.1.0.2 defines K_0 as
  closure of `{λx.x, λx.x+1}`; "zero" arises as a
  derived constant from substitution operations on K_0.
  PASS (with imprecision: §0.1.0.2 names `λx.x+1`, not
  zero).
- `KMor1.succ` at `LawvereKSim.lean:38`, §0.1.0.2
  (`λx.x+1`). PASS.
- `KMor1.proj` at `LawvereKSim.lean:40`. Citation column
  "(proj, std.)". PASS (standard universal-algebra
  atom).
- `KMor1.one` at `KArith.lean:31`. PASS.
- `KMor1.pred` at `KArith.lean:44`, §0.1.0.17(4).
  Verified. Note: Geb's `level = 1` vs Tourlakis's K_0
  placement reflects a systematic counting convention
  difference (Geb counts `rec1` invocations
  structurally; Tourlakis closes K_0 under substitution
  and bounded sums). Not a citation defect.
- `KMor1.isZero` at `KArith.lean:78`, §0.1.0.17(3). PASS.
- `KMor1.signum` at `KArith.lean:414`. PASS.
- `KMor1.add` at `KArith.lean:111`, §0.1.0.17(1). PASS.
- `KMor1.cond` at `KArith.lean:222`, §0.1.0.17(6). PASS.
- `KMor1.mult` at `KArith.lean:301`, §0.1.0.17(b). PASS.
- `KMor1.monus` at `KArith.lean:403`, §0.1.0.17(a). PASS.
- `KMor1.pow2` at `KArith.lean:500`, §0.1.0.17(c). PASS.
- `KMor1.rec1` at `LawvereKSim.lean:137`. PASS.
- `KMor1.permArgs` at `LawvereKSim.lean:154`. PASS.
- `KMor1.interp_cond` at `KArith.lean:249`. PASS.

### §3.1 composites that need to be built

- `KMor1.natK`. Citation: "Master-design level-0
  construction". Acceptable; see Minor M1.
- `KMor1.maxK = (x ∸ y) + y`. Citation: "§0.1.0.27 proof
  (p. 9)". **FAIL on two counts**: page (§0.1.0.27 is
  on p. 10) and content (§0.1.0.27 is the Bounding
  Lemma; it does not construct `max(x,y) = (x∸y)+y`).
  Tourlakis pp. 6–22 do not contain this construction.
  Blocker B1.
- `KMor1.maxOver`. Citation: "§0.1.0.44 proof uses
  `max(x⃗)` as the bound argument (p. 22)". *Use*
  citation, not *construction* citation. Serious S1.
- `KMor1.A_two_iter`. Citation: §0.1.0.9, §0.1.0.17(c),
  §0.1.0.44 proof. §0.1.0.9 is about Ackermann at level
  n (not r-fold iteration). Mathematically the
  construction is correct (`A_2 = λx.2^x` per §0.1.0.4
  combined with §0.1.0.17(c); iterate r times).
  Serious S2.

### §4.1 URM instruction cases

All five (`assign`, `inc`, `dec`, `jumpZ`, `stop`) cited
to §0.1.0.37 p. 16. Verified line-by-line against
Tourlakis's case analysis on p. 16. PASS.

### §5.1 per-ER-constructor templates

- `ERMor1.zero`: trivial. PASS.
- `ERMor1.succ`: encoded via M-template + extra inc. PASS.
- `ERMor1.proj i`: Tourlakis M template (p. 19). PASS
  (with redundant "zero V_out" preamble; Cosmetic C1).
- `ERMor1.sub`: spec cites §0.1.0.17(a) as source for a
  Loop program. §0.1.0.17(a) gives K^sim recursion
  equations, not a Loop program. Serious S3.
- `ERMor1.comp f gs`: Tourlakis p. 21 "We can
  (essentially) concatenate M_g and M_f". PASS.
- `ERMor1.bsum f`, `ERMor1.bprod f`: Tourlakis p. 21
  bounded-recursion template specialised. PASS.

### §6.2 K^sim atoms in step function

- `cond` (level 1): verified `KArith.lean:264`. PASS.
- `pred` (level 1): verified `KArith.lean:72`. PASS.
- `succ`, `proj`, `natK c` (level 0): structural. PASS.
- `pred^k(I_prev)` composition: level 1. PASS.

### §13.1 Tourlakis citations

All 11 cited sections (§0.1.0.2, .4, .7, .9, .17, .20,
.27, .36, .37, .42, .43, .44) verified against PDF at
their stated pages. PASS.

### §13.2 Internal repository references

All verified except `LawvereKSimInterp.lean:23` (actual
location is line 22, off-by-one). Minor M2.

## Other verification log

**Constructive discipline (§10, §12.1).** §4.3 uses
`Fin.find` (constructive); the `Classical.choose`
alternative shown above it is a contrast, not the
committed version. PASS.

**§6.2 level claim.** Trace: leaf branches ≤ level 1;
PC-dispatch chain level 1; step function level 1; outer
simrec adds 1 → level 2. Per `KMor1.level`'s `simrec`
case at `LawvereKSim.lean:112–114`. PASS.

**§7.1 level for `boundExprK`.** `pow2.level = 2`;
`A_two_iter r` is composition of `pow2`'s, level 2.
`maxOver a` built from `maxK` (level 2), level 2. Final
composition stays at level 2. PASS.

**§5.1 templates — walk-through.** For `ERMor1.succ` with
`v = ![3]`: V_out goes 0 → 3 → 4 = succ 3. Correct
modulo the destructive-V_in concern, which the spec
acknowledges via the clone-source-at-compile-time
discipline (under-committed; Serious S5).

**§6.1 recursion equations vs Tourlakis p. 16.** Spec's
0-indexed PC vs Tourlakis's 1-indexed; shift consistent
across base and step. PASS.

**§8.1 `erToK` matches Tourlakis p. 22 formula.** Spec
matches `f = λx⃗.v_1(A^r_n(max x⃗), x⃗)` line-by-line
with n=2. PASS.

**§9.1 dependency graph.** `URMTourlakis.lean` listing
`Tower` is questionable; M3.

## Findings

### Blocker

#### B1. §3.1 `maxK` citation wrong on page and content

§3.1 cites "§0.1.0.27 proof (p. 9) `max(x, y) = x ∸ y + y,
… in E^2`". §0.1.0.27 is on p. 10 (not p. 9), and is the
Bounding Lemma — it does not construct `max(x,y) = (x∸y)+y`.
Tourlakis pp. 6–22 do not contain this construction
anywhere on or near the cited location; §0.1.0.29 (p. 11)
is an Exercise stating `max ∉ E^0`. Per the user's named
rule "every cited claim is verifiable at the cited
source", this is a wrong-citation defect.

**Response:** fix. Replace `maxK`'s citation with: cite
§0.1.0.17(1) (`+`) and §0.1.0.17(a) (`∸`) for the
constituent operations; mark the identity `max(x, y) =
(x ∸ y) + y` as a one-line lemma derived in
`LawvereERKSim.lean` (or `Utilities/KArith.lean`) with
no specific Tourlakis source, since the identity is
elementary and not stated by Tourlakis. The level claim
(level 2) follows from `comp add ⟨monus, proj 1⟩` having
max level 2.

#### S2-promotion check

Round-2 reviewer flagged only one blocker. Verified no
other findings warrant promotion.

### Serious

#### S1. §3.1 `maxOver` recursion is uncited

Citation "§0.1.0.44 proof uses `max(x⃗)` as the bound
argument (p. 22)" is a *use* citation. The construction
itself (recursion `maxOver 0 = zero`, `maxOver (a+1) =
maxK ∘ ⟨proj_0, maxOver a ∘ shift⟩`) is uncited.

**Response:** fix. Re-label `maxOver`'s entry: the
construction is folklore (associative-binary-op
extended to n-ary). Add a note that no Tourlakis
location establishes the n-ary recursion; the use of
`max(x⃗)` as a bound argument in §0.1.0.44 proof is a
*use* citation, not a *construction* citation. The
recursion's correctness is a one-line induction on `a`
to be proved alongside `maxOver`'s definition.

#### S2. §3.1 `A_two_iter` citation footprint inflated

§0.1.0.9 is about Ackermann at level n, not r-fold
iteration. The accurate citation is §0.1.0.4 (p. 2:
defines `A_{n+1}(x) = A_n^r(x)` as r-fold iteration)
plus §0.1.0.17(c) for `A_2 = λx.2^x`. §0.1.0.44 proof
uses `A^r_n(max x⃗)` as a runtime majorant; that part is
correct.

**Response:** fix. Replace §0.1.0.9 with §0.1.0.4 in the
citation. The Lean construction is r-fold composition
of `pow2` (which realises `A_2 = λx.2^x` per
§0.1.0.17(c)); level proof is by induction on `r` using
`comp`'s max rule.

#### S3. §5.1 `ERMor1.sub` template misattributes the Loop program

§0.1.0.17(a) (p. 6) gives K^sim recursion equations for
`λxy.x ∸ y`, not a Loop program. Tourlakis p. 19 provides
Loop programs only for `λxy.xy` (`R^{XY}_Z`). For sub,
the implementer must construct the Loop program from
the §0.1.0.17(a) equations.

**Response:** fix. Rewrite the sub row as: "Derived
from §0.1.0.17(a) recursion equations: Loop X { Z ← Z
∸ 1 } end, with Z initialised to X. Translate to URM
via the Loop-to-URM template (p. 20)." The Loop program
itself is a one-line specialisation of the §0.1.0.17(a)
recursion shape; no Tourlakis source provides it
verbatim but the derivation is elementary.

#### S4. §7.2's `r_e` recursion under-specified

The table contains placeholder constants ("r_zero := 1,
…, r_proj := 2, r_sub := 3, …") marked "to be tightened
during implementation." §7.3's `boundExprK_dominates`
depends on `r_e` exceeding the runtime witness from
§5.2. As written, §7.2 admits an interpretation where
the placeholders do not bound the runtime.

**Response:** fix. Restructure §7.2: `r_e` is defined
*as* the function that makes `boundExprK_dominates`
hold; concrete constants emerge during implementation
by structural induction on `e` following Tourlakis
§0.1.0.42 proof (pp. 18–21). The spec commits only to
the recursion *shape*: r_e is non-decreasing in e's
subexpression r's, and increases by a constant at
`bsum`/`bprod` (the bounded-recursion case). Concrete
values are computed by the implementation, not pinned
by the spec. The level claim (level 2) is independent
of the specific constants.

#### S5. §5.1 register-allocation discipline under-committed

Two alternative strategies are described ("clone the
source register at compile time" vs "use a fresh
scratch register V_tmp"). Without committing to one,
the per-template correctness proofs in §5.2 are
ambiguous.

**Response:** fix. Commit to **clone-source-at-compile-
time**: every `proj i` template allocates a fresh
scratch register `V_src_i` at compile time, copies
input register `V_{inputRegs i}` into `V_src_i` via the
M-template (zero V_src_i; loop V_{inputRegs i} times
{V_src_i ← V_src_i + 1}), then transfers V_src_i into
V_out destructively. The original input register is
re-cloned for each consuming subexpression in `comp`,
preserving its value across the composition. This is
the simpler discipline and avoids the in-template
restoration step.

### Minor

#### M1. §3.1 `natK` citation could be cleaner

Add a §0.1.0.2 citation: K_0's closure under
substitution yields all constants via repeated
application of `λx.x+1` to `λx.x`'s output, starting
from the input.

**Response:** fix.

#### M2. §13.2 `LawvereKSimInterp.lean:23` off by one

Actual: line 22.

**Response:** fix.

#### M3. §9.1 lists `Tower` as import of `URMTourlakis.lean`

Tower is needed only by `LawvereERKSim.lean` (level
proofs). Remove from `URMTourlakis.lean`'s imports in
the dependency graph.

**Response:** fix.

#### M4. §6.2 step_{j+1} prose conflates PC dispatch with register dispatch

The per-PC branch is selected by `I_prev = k`; within
that branch, the question is whether the static
instruction at PC k mutates register j or not. Clarify
the prose.

**Response:** fix. Rewrite §6.2's step_{j+1} display to
make the two-level dispatch explicit: outer dispatch
on `I_prev` selects a PC k; inner per-PC branch
inspects `instrs[k]` and returns either an updated
value or `v_j_prev` (for instructions not touching
register j).

#### M5. §3.1 `maxK` level reasoning wording

"Level 2 by composition of `monus` and `add`" is
slightly imprecise: `comp` takes max, so level 2 comes
from `monus`. Clarify.

**Response:** fix. Reword to "Level 2 by `comp` taking
max of `monus` (level 2) and `add` (level 1)."

#### M6. §5.1 redundant zero-V_out preamble

`URMState.init` already zeroes non-input registers.

**Response:** fix. Drop the redundant preamble from
proj and succ templates.

#### M7. §2.2 phrasing about derived instructions

Slightly Geb-centric. Reword for clarity.

**Response:** fix.

#### M8. §13.1 §0.1.0.17 numbering scheme note

Numbering (1)–(6) for K^sim_1 functions vs (a)–(c) for
K^sim_2; spec correctly distinguishes. Note from
reviewer: spec's level placement of `λx.1 ∸ x` (isZero)
at "Level 1" differs from Tourlakis's K^sim_0
placement. This is the systematic Geb counting
convention difference, not a citation error.

**Response:** reject-as-cosmetic-taste (verified
correct given the convention difference; no fix
needed).

### Cosmetic-taste

#### C1. §5.1 "zero V_out" preamble gratuitous

Subsumed by M6.

**Response:** fix (via M6).

#### C2. §3 inventory table citation column inconsistent

Mix of external and internal citation styles.

**Response:** fix. Use a uniform format: external
citation `(Tourlakis §X)` or internal citation
`(folklore / from previous row)` or `(initial fn)` for
universal-algebra atoms.

#### C3. §6.2 "Level total" subsection ends with checkmark

Remove the `✓`.

**Response:** fix.

#### C4. "load-bearing" register

Borderline; spec uses it as a structural label, not as
a value-laden adjective. Verified: `CLAUDE.md` § Style
guidelines warns against "key", "important",
"crucial", etc.; "load-bearing" is structural. Reject
as cosmetic-taste.

**Response:** reject-as-cosmetic-taste.

#### C5. §2.1 cross-reference to round-1 finding B3

Readers without round-1's review cannot dereference.

**Response:** fix. Either explain the reference inline
or remove. Will remove the explicit B3 reference and
expand the prose to be self-contained.

## Convergence assessment

Round does NOT converge: 1 blocker, 5 serious findings.
