# Step 3 plan adversarial review — round 1

## Summary

The plan tracks the spec faithfully on substance — all
ten tasks correspond to spec deliverables, code blocks
match the spec for the load-bearing definitions and
proofs (Tasks 5 and 8 are character-identical mod
line-wrapping; Task 7 deviates by a documented
adjustment), and the dependency order is sound. The
banned-words discipline is clean. Risk: the plan
contains two **incorrect import-position hints**
(GebLean.lean and GebLeanTests.lean) that would land
new imports in the wrong alphabetical position relative
to existing entries — a competent implementer will
notice on a quick `sort -c`, but a literal subagent may
not. There is one minor drift in the Task 7 proof from
the spec's empirically-verified shape, and one small
under-specification in Task 10.7's reviewer brief.

Total findings: 1 substantive, 4 minor. Recommendation:
**revision (round 2)** — substantive finding 1 needs a
one-line correction so the implementer doesn't insert
imports into a non-alphabetical position.

## Findings (severity-ordered)

### Finding 1: Wrong "near" anchor for `GebLean.lean` and `GebLeanTests.lean` imports (severity: substantive)

**Location:** Plan §1.2 (lines 201-209) and §9.2 (lines
708-717).

**Issue:** The plan instructs the implementer to add
the new import "in alphabetical order, near the
existing `import GebLean.Utilities.ERSimultaneousBoundedRec`
line" (and analogously for the test counterpart). But
`ERAMajorants` sorts alphabetically **before** `ERArith`
— i.e. it should be the first `Utilities/ER*` import,
not adjacent to `ERSimultaneousBoundedRec`. Sorted:
`ERAMajorants < ERArith < ERPackedBound <
ERSimultaneousBoundedRec < ERTreeArith < ERTupling`
(M = 0x4d < r = 0x72 in `ERAMajorants` vs `ERArith`).

If the implementer follows the hint literally, the new
line lands between `ERSimultaneousBoundedRec` (line
150) and `ERTreeArith` (line 151) — out of alphabetical
order, which violates the surrounding convention and
will be flagged in the cycle-end code review (Task
10.7).

**Evidence:** From the current `GebLean.lean` (lines
148-153):

```text
import GebLean.Utilities.ERArith
import GebLean.Utilities.ERPackedBound
import GebLean.Utilities.ERSimultaneousBoundedRec
import GebLean.Utilities.ERTreeArith
import GebLean.Utilities.ERTupling
```

`ERAMajorants` belongs **above** `ERArith` (line 148),
not near `ERSimultaneousBoundedRec` (line 150).
Same situation in `GebLeanTests.lean` lines 29-33:
the new test import belongs above `ERArith` (line
29), not near `ERSimultaneousBoundedRec` (line 31).

**Proposed fix:** In Plan §1.2 replace "near the
existing `import GebLean.Utilities.ERSimultaneousBoundedRec`
line" with "immediately above the existing
`import GebLean.Utilities.ERArith` line". Same
substitution in Plan §9.2 with the test counterpart.

### Finding 2: Task 7 proof deviates from the round-4-empirically-verified spec text (severity: minor)

**Location:** Plan Task 7 Step 7.1 (lines 538-553).

**Issue:** Plan Task 7's `bounds` proof is structurally
similar to spec §5.1 but not character-identical:

- Spec §5.1: introduces `h_ctx0 : ctx 0 ≤ sup ctx + 0`
  with a nested `have ... ; omega`, then a final
  `omega`.
- Plan Task 7: introduces `h_ctx0_le_sup : ctx 0 ≤ sup
  ctx` directly, with `Finset.le_sup ... (Finset.mem_univ
  _)`, then a final `omega`.

The plan claims (line 555) "This proof was empirically
verified during round-4 adversarial review". But the
round-4 reviewer transcribed the spec **literally** (per
round-4 §"Empirical Lean verification of §4 and §5
proofs") — the spec §5.1 text, not Plan Task 7's
adjusted text. So the empirical-verification claim
attached to Plan Task 7 is technically false: only the
spec §5.1 form was verified. Both forms should compile
(the cleaned-up form is closer to `ofAddN`'s style
in `LawvereERPolynomialBound.lean:448-460` and uses
mathlib idioms), but the implementer relying on
"empirically verified" as a load-bearing assurance
should know that the verified form is the spec's form.

**Evidence:** Round-4 review (`docs/research/
2026-05-03-step-3-spec-adversarial-review-round-4.md`)
§"Empirical Lean verification of §4 and §5 proofs"
lines 64-67 says transcription was of the spec's §3.1
/ §3.2 / §3.3 definitions and §4.1 / §4.2 / §4.3 / §5.1
/ §5.2 proofs.

**Proposed fix:** Either (a) restore the spec's exact
§5.1 text in Plan Task 7.1 to preserve the
empirical-verification anchor, or (b) keep the
cleaner Plan Task 7.1 form but soften the line "This
proof was empirically verified during round-4
adversarial review" to acknowledge the cleanup —
e.g. "The spec §5.1 form was empirically verified
during round-4; this is a stylistic cleanup that
removes the `+ 0` indirection and replaces `(by simp)`
with `(Finset.mem_univ _)`. Both forms close on the
same `omega` after the `Finset.le_sup` step." Option
(a) is safer for a literal subagent; option (b) is
fine if the implementer is allowed to adjust under
spec §1.3's flexibility clause.

### Finding 3: Task 10.7 cycle-end-review brief under-specifies the criteria (severity: minor)

**Location:** Plan §10.7 (lines 898-916).

**Issue:** The brief says "verify the spec §10
acceptance criteria against the actual code, not the
plan" but does not enumerate them in the brief.
If the reviewer subagent reads only the brief (a
common pattern for delegated subagents), it has to
chase the spec to find §10. That's fine when §10 is
one short list and the subagent will read the spec
anyway — and §10 is indeed short — but for symmetry
with the rest of the plan and to make the dispatch
self-contained, the brief should at least list the
six §10 numbered items inline (or copy them, the way
Step 10.3 already does).

Additionally, "code reviewer subagent" is used without
specifying which review skill — `code-review:code-review`,
`lean4:review`, or `superpowers:requesting-code-review`
— and the diff-range argument
`origin/terence/develop..HEAD` assumes the subagent
will be told a base ref.

**Evidence:** Plan lines 898-913.

**Proposed fix:** Either inline the six §10 acceptance
criteria from the spec (or refer to Step 10.3's
checklist, which already lists them), and pick a
specific review skill. E.g.:

> Dispatch `superpowers:requesting-code-review` (or
> `lean4:review`) covering the diff
> `origin/terence/develop..HEAD` after the spec/plan
> commits land. Reviewer brief: verify the six
> acceptance criteria from spec §10 against the
> actual code (not the plan): (1) module file with
> the named composites and interp lemmas; (2) `#guard`
> tests file; (3) `GebLean.lean` import; (4)
> `GebLeanTests.lean` import; (5) no regressions; (6)
> `markdownlint-cli2` clean on the touched docs.
> Output to `docs/research/
> 2026-05-03-step-3-cycle-end-review.md`. Address
> substantive findings before declaring step 3 done.

### Finding 4: Plan does not list `Utilities/Tower.lean` or `LawvereERPolynomialBound` as `GebLean.lean` import additions, but ERAMajorants imports them directly (severity: minor / cosmetic)

**Location:** Plan File-structure section (lines 51-71)
and Task 1.

**Issue:** The plan's `ERAMajorants.lean` imports
`GebLean.LawvereERPolynomialBound` and
`GebLean.Utilities.Tower` directly. Neither is
currently in `GebLean.lean`. This is consistent with
how the existing tree handles those modules (they
reach `GebLean.lean` transitively via `LawvereERBound`
on line 46), so no `GebLean.lean` change is required
for those — and the plan correctly says only the
`ERAMajorants` line is added to `GebLean.lean`.

This is fine, but worth noting that the new module
**directly** depends on a non-`GebLean.lean`-listed
module (`Utilities/Tower`). If a future cleanup pass
removes a transitive import or rearranges the index,
the direct import on `Utilities/Tower` keeps things
working. No fix needed; flagged for the reviewer's
mental model only.

**Evidence:** `GebLean.lean` does not contain
`GebLean.Utilities.Tower` or
`GebLean.LawvereERPolynomialBound`; both are
transitively reachable via `GebLean.LawvereERBound`
(line 46) and `GebLean.LawvereERBoundComputable`
(line 47). The plan's Task 1.1 imports both directly
without adding a `GebLean.lean` line for them.

**Proposed fix:** None needed. The plan's behaviour
is correct. (One-line note in plan §1.2: "Only
`GebLean.Utilities.ERAMajorants` is added to
`GebLean.lean`; `LawvereERPolynomialBound` and
`Utilities.Tower` are reached transitively via the
existing `LawvereERBoundComputable` line.")

### Finding 5: Step 9.4's `#guard` line for `A_one_iter 2` may be slow due to nested `addN`-via-`mulN`-via-`bsum` expansion (severity: minor / pre-flagged)

**Location:** Plan Step 9.4 (lines 728-754) and Step
9.5 (lines 757-769).

**Issue:** The plan and spec both note `A_one_iter`'s
`#guard`s are bprod-free and "bsum size scales
linearly". But `addN` is built via `mulN` (=
`boolAnd`) which uses `bsum` — and `A_one_iter 2`
nests three layers of `addN` (one for each composition
plus the outermost). Empirically the spec discipline
warned about kernel reduction through `bsum`. The plan
includes a fallback: "If any individual `A_one_iter 2`
`#guard` is observed to dominate the runtime (e.g.
takes more than a couple of seconds), drop that line".
This is correct discipline.

The `#guard (ERMor1.A_one_iter 2).interp ![3] = 18`
line (input `x = 3`, kernel must reduce two stacked
`addN` calls each of which evaluates two
`bsum`-via-`mulN` instances over arguments `4`, `4`,
`8`, `8`) is the most likely candidate for slowdown.
The fallback is present, so this is non-blocking, but
worth tracking on the implementer's checklist.

**Evidence:** `addN`'s definition in
`GebLean/Utilities/ERArith.lean:42-55` shows nested
`mulN` (which is `boolAnd` per
`ERArith.lean:32`). `boolAnd` uses `bsum` per the
`LawvereERBool.lean` infrastructure. The kernel
reduction depth at `(A_one_iter 2).interp ![3]` is
non-trivial.

**Proposed fix:** The plan's fallback (Step 9.5,
lines 763-769) handles this. No action needed unless
the implementer hits the slowdown — in which case
they should drop the `#guard` per the existing
discipline. The closed-form `interp_A_one_iter` is
the canonical correctness witness.

## Items checked and confirmed correct

- File paths: `GebLean/Utilities/ERAMajorants.lean`
  and `GebLeanTests/Utilities/ERAMajorants.lean` are
  correct (under `Utilities/`, not bare).
- Task ordering: each task references only previously
  defined entities. Task 7 uses `interp_A_one` from
  Task 3; Task 8 uses `interp_A_one_iter` from Task 5
  and `A_one_iter` from Task 4 (not "A_one_iter
  builder name" the prompt asked about — Task 8 builds
  `ofA_one_iter`, which depends on `A_one_iter` and
  `interp_A_one_iter`, both present).
- Build-order: each `lake build` step works with the
  preceding state (e.g. Task 2 commits `A_one`
  unproven w.r.t. interp; the lemma in Task 3 proves
  it later — definitions can build standalone).
- `PolyBound` structure signature: confirmed at
  `LawvereERPolynomialBound.lean:42-50`. Plan Task
  7's `where ... bounds := ...` shape matches the
  field signature (`∀ ctx, f.interp ctx ≤ coefficient
  * (sup + 1) ^ degree + constant`).
- `addN`, `succ`, `proj`, `comp` arities and
  signatures match what Task 2's construction
  expects.
- `ERMor1.towerER` and `ERMor1.interp_towerER` exist
  in `LawvereERBoundComputable.lean` (Task 6 routes
  through them). Task 6's proof `unfold A_two_iter;
  exact ERMor1.interp_towerER r ctx` is correct.
- Spec §4.2's `interp_A_one_iter` proof is
  character-identical to Plan Task 5 mod a single
  line wrap.
- Spec §5.2's `ofA_one_iter` proof is
  character-identical to Plan Task 8 mod nothing.
- Banned-word discipline (CLAUDE.md): clean across
  the plan body and commit messages. The two
  `sorry` matches are in the legitimate
  meta-discussion "no `sorry`".
- Markdown discipline: docstrings and module
  docstrings carry the required Tourlakis 2018 +
  master-design §3.3 citations per spec §7.
- `Fin 1` index convention (use `0` in lemma RHS,
  `(0 : Fin 1)` in constructions): observed in plan
  Task 2 (`ERMor1.proj (0 : Fin 1)`) and Task 5
  (`ERMor1.proj (0 : Fin 1)`); lemma RHSs in Tasks
  3, 5, 6 use `ctx 0`.
- Workstream entry format (Plan §10.4): matches
  existing `er-ksim2-equiv-via-urm.md` Step 1 and
  Step 2 entries.
- Test-discipline `#guard` selection: `A_one`,
  `A_one_iter` at small `r`, `A_two_iter` only at
  `r = 0` — matches the discipline established in
  steps 1 and 2.
- Out-of-scope (Plan §"Out of scope") matches spec §8
  list verbatim.
- Final-verification acceptance-criteria checklist
  in Step 10.3 is faithful to spec §10's six-point
  list.

## Open questions for the plan author

None. The plan's structure is straightforward and
the issues identified are local fixes.

## Recommendation

**Round 2.** Finding 1 is the only must-fix; it is a
two-word edit to two locations (the "near …" anchors
in §1.2 and §9.2) and a corresponding rewording so
the literal subagent doesn't insert misordered
imports. Findings 2-5 are minor and could be
addressed at the author's discretion in the same
round.
