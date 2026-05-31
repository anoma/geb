# Adversarial review 5: novelty/provenance addition (confirmation pass)

## Verdict

The "Novelty and prior-formalization status" addition has **converged.**
All five review-4 findings are genuinely resolved by the edits, and the
fixes are sound and mutually consistent. The MAJOR search-effort gap is
closed by a dedicated **"The search is time-boxed."** paragraph that
gives each headline result a small fixed search budget, stops at the
first decisive hit, falls back to **"provenance unverified"** on
budget exhaustion, and explicitly ties total search effort to the
`1`–`3`-headline-declarations depth budget — executable, not merely
aspirational, with the concrete query count deferred to the plan
(an appropriate level of detail for a design spec). The four MINORs are
each addressed at the right altitude: the category framing is now a
two-axis decision tree with an explicit novelty-axis-wins precedence
and "categories 2–4 apply only to *known* mathematics," the calibration
step now targets the `L ⊣ Φ` area so a category-1/2 exemplar is
guaranteed, and the template **Provenance** bullet now carries both the
date/scope stamp and the prose-only-empty carve-out inline. No
regression: markdownlint is clean (0 errors), every `##`/`###` heading
matches its TOC entry, all in-body anchors (`#novelty-and-prior-formalization-status`,
`#parallel-formulations`, `#coverage-discipline`) resolve, and the new
precedence/decision-tree wording does not contradict the Idris
adaptation (cats 1–2 + Lean cross-links) or the
external-vs-internal split with Parallel formulations (category 4 still
explicitly excludes our own Idris-then-Lean re-formulations). No new
defect found.

## Verification performed

- `markdownlint-cli2` against `geb-lean/.markdownlint-cli2.jsonc`:
  0 errors on the spec.
- Heading/TOC cross-check: all 19 `##`/`###` headings present and each
  matches a TOC line; the provenance slug
  `#novelty-and-prior-formalization-status` is used identically in the
  TOC (line 16) and at every in-body reference (lines 83, 264, 387).
  No MD051 fragment mismatch.
- Read the **Provenance** template bullet (lines 261–266), the whole
  "Novelty and prior-formalization status" section (lines 332–412),
  the Goal provenance bullet (lines 79–85), Process steps 3 and 7
  (lines 533–538, 544–548), and the Risks "Over-claimed novelty"
  bullet (lines 572–580).

## Per-finding confirmation

| # | Severity | Status | Where fixed |
| --- | --- | --- | --- |
| 1 | MAJOR | Fixed | "The search is time-boxed." para, lines 374–384 |
| 2 | MINOR | Fixed | Decision-tree framing 339–341; cat 1 precedence 346–350 |
| 3 | MINOR | Fixed | Process step 3, lines 533–538 |
| 4 | MINOR | Fixed | Template **Provenance** bullet, lines 262–263 |
| 5 | MINOR | Fixed | Template **Provenance** bullet, lines 265–266 |

### 1 — MAJOR, search effort (Fixed)

The new paragraph (lines 374–384) states the search is open-ended in
principle, names it as the largest potential time cost, then bounds it:
"each headline result gets a small fixed search budget (the ordered
targets above, stopping at the first decisive hit, and otherwise a
bounded handful of queries per axis)." Budget exhaustion routes to
"provenance unverified" and the author moves on. It explicitly ties the
budget to depth: "keeps total search effort proportional to the
`1`–`3`-headline-declarations-per-module depth budget rather than
unbounded; the plan fixes the concrete query count." This is the exact
shape review-4 asked for, the fallback is now operational, and the
effort is tied to the depth budget. Deferring the exact integer to the
plan is correct for a design spec.

### 2 — MINOR, category exclusivity (Fixed)

The section now frames the four categories as "a decision tree on two
axes — first the *mathematics* axis, then, only for known mathematics,
the *prior-formalization* axis" (lines 339–341). Category 1 explicitly
resolves the concurrent-formalization ambiguity: "The novelty axis
takes precedence: a result we judge novel stays category 1 even if an
external formalization … turns up, with that formalization noted in the
tag. Categories 2–4 apply only to *known* mathematics" (lines 346–350).
Cats 2/3/4 each begin "Known maths …". The overlap review-4 flagged is
now unambiguous, and cats 2–4 are restricted to known maths.

### 3 — MINOR, calibration exemplar (Fixed)

Process step 3 (lines 533–538) now reads: "Calibrate on an area
expected to contain the highest-stakes provenance categories — the
category-judgment / `L ⊣ Φ` area, which
`geb-lean/docs/novelty-analysis.md` already analyses — so a worked
category-1 or category-2 **Provenance** tag exists as an exemplar."
This is review-4's preferred (simpler) remedy and uses material that
already exists.

### 4 — MINOR, date/scope stamp in template (Fixed)

The template **Provenance** bullet now reads "a one-line
novelty-and-prior-formalization tag stamped with its search date and
scope" (lines 262–263). The honesty requirement now travels with the
instruction the author writes against, not only the Status paragraph
and Risk.

### 5 — MINOR, prose-only areas (Fixed)

The same bullet now adds "Empty for prose-only areas with no headline
declarations (e.g. Idris area 7), mirroring the coverage carve-out"
(lines 265–266). This mirrors the coverage discipline's prose-only
tolerance, as suggested.

## No-regression check

- Doctoc TOC: matches headings exactly; no orphaned or stale entries.
- Markdownlint: 0 errors; no over-length lines introduced (the new
  time-box paragraph wraps within the project width).
- Idris adaptation (lines 394–400) unchanged and still coherent: Idris
  uses categories 1–2 with Lean cross-links and skips the 3/4 external
  search — the new "categories 2–4 apply only to known mathematics"
  clause does not disturb this, since the Idris first-formalization
  question is asked "against *any* system including this Idris code."
- Parallel-formulations separation intact: category 4 still reads
  "never our own Idris-then-Lean re-formulation, which is a parallel
  formulation," and the "Relation to parallel formulations" paragraph
  (lines 386–392) is unchanged.

## Counts by severity

- BLOCKER: 0
- MAJOR: 0
- MINOR: 0
- New defects: 0
