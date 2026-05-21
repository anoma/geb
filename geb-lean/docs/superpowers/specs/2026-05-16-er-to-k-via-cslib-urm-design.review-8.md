# Round-8 adversarial review — erToK via zero-test URM simulation

Reviewer: fresh-context `general-purpose` Agent (round 8;
post-convergence cleanup verification).
Artefact under review:
[`2026-05-16-er-to-k-via-cslib-urm-design.md`](2026-05-16-er-to-k-via-cslib-urm-design.md).
Prior rounds:
[`.review-1.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-1.md),
[`.review-2.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-2.md),
[`.review-3.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-3.md),
[`.review-4.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-4.md),
[`.review-5.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-5.md),
[`.review-6.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-6.md),
[`.review-7.md`](2026-05-16-er-to-k-via-cslib-urm-design.review-7.md).

## Citation verification log

External (Tourlakis 2018) and internal `File.lean:line`
references verified for the §2.1 CSLib-vs-ZeroTestURM
rationale's technical claims:

- `KMor1.cond` at `KArith.lean:222` ✓; level proof
  `KMor1.cond.level = 1 := by decide` at `KArith.lean:264`
  ✓.
- `KMor1.eq` at `KArith.lean:445` ✓; level proof
  `KMor1.eq.level = 2 := by decide` at `KArith.lean:469`
  ✓.
- §0.1.0.37 (p. 15–16), §0.1.0.42 (p. 18), §0.1.0.44
  (p. 22) verified against PDF.

§2.1's technical core is citationally correct.

## Cleanup verification

1. **"load-bearing" removal.** **NOT clean.** §12.1
   lines 966–967 still contain the phrase broken across
   a line wrap (`load-\nbearing path`). See Blocker B1.
2. **`URMTourlakis` → `ZeroTestURM` rename.** Clean.
3. **Historical "Round 1 mistakes" section removed.**
   Clean.
4. **§2.1 rationale present, technically accurate.**
   ✓.
5. **Cross-references intact after deletion.** ✓.

## Other verification log

§6.1 vs Tourlakis p. 16: match modulo 0/1-indexed PC
shift. §6.2 level argument sound (uses `cond`, not
`eq`). §7.1 `boundExprK` level 2 by `comp` max rule.
§8.1 erToK formula matches §0.1.0.44 p. 22.
Dependency graph (§9.1) correctly excludes
`LawvereKSimER` / `LawvereKSimMajorization` and CSLib
URM. No internal contradictions.

## Findings

### Blocker

#### B1. "load-bearing" phrase still present at §12.1

§12.1 lines 966–967 reads
`no \`Classical.*\` or \`noncomputable\` on the load-\nbearing path`
(line-wrapped, escaping single-line greps). The user
has banned this phrase.

**Response:** fix. Replace with `no \`Classical.*\` or
\`noncomputable\` in any committed declaration or
proof`.

### Serious

None.

### Minor

#### M1. §6.1 predicate-level citation vs §6.2 realisation

§6.1 cites §0.1.0.20 for `λx.x = a ∈ K^sim_{1,*}` as
predicate-level reasoning. §6.2 realises PC dispatch
via `pred^k`-chain, not via this predicate. A
half-sentence noting the shift would aid coherence.

**Response:** fix. Add the bridging sentence.

#### M2. §3.1 `KMor1.signum` "not used in §3.1–§8"

The annotation is technically accurate (signum appears
inside the body of `KMor1.eq`, which itself is unused
in §3.1–§8). Worth noting in case a reader wonders why
a private helper appears in the catalogue.

**Response:** reject-as-cosmetic-taste (existing
annotation is sufficient).

### Cosmetic-taste

#### C1. §13.2 round-2 attribution to Appendix A

Single-line process-history attribution in citations
section. Could trim.

**Response:** reject-as-cosmetic-taste (the attribution
is a citation-provenance note, not a retrospective
section; one line is acceptable).

#### C2. §2.1 quantitative estimate "50–100-line URM"

Estimate may not survive implementation.

**Response:** reject-as-cosmetic-taste (an estimate in
a rationale paragraph is acceptable; if implementation
diverges substantially, the spec can be updated then).

#### C3. §13.2 master-design reference lacks anchor

Trivial; current form is readable.

**Response:** reject-as-cosmetic-taste.

## Convergence assessment

Round does NOT converge: 1 blocker, 0 serious findings.

The one remaining blocker is a single-edit cleanup of
the line-wrapped "load-bearing" phrase at §12.1. After
that edit, the spec is convergent.
