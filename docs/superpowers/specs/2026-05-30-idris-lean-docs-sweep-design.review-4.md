# Adversarial review 4: novelty/provenance addition

## Verdict

The new "Novelty and prior-formalization status" element is
substantially sound and well-integrated: it carves its online-search
scope into the Goal explicitly so it does not contradict the
"no proof or build work" Non-goal; it is consistently declared
best-effort and non-gated (matching the parallel-formulations
precedent it cites); it correctly separates category 4 (external Lean
formalizations) from our own internal re-formulations (the
Parallel-formulations element); the Idris adaptation is coherent with
the prose-only area 7; the referenced `geb-lean/docs/novelty-analysis.md`
exists and genuinely reads as a per-result provenance starting input;
and the doctoc TOC, anchors, and markdownlint are clean. The remaining
issues are one MAJOR (the per-result external-search effort is not
reconciled with the spec's "overview depth, not an enormous diff"
effort framing, and is the most likely source of scope blow-up) and a
few MINORs around category edge cases and the calibration-step wording.
None blocks the plan stage, but the MAJOR should get one sentence of
explicit bounding before hand-off.

## Verification performed

- Heading slug: `## Novelty and prior-formalization status` (line 329)
  generates `#novelty-and-prior-formalization-status`; the TOC entry
  (line 16) and all three in-body anchor references (lines 83, 263,
  364) use that exact slug. Exact match, no MD051 risk.
- `markdownlint-cli2` against `geb-lean/.markdownlint-cli2.jsonc`:
  0 errors on the spec.
- Over-length scan of the new section (lines 329-389): no prose line
  exceeds 72 columns; no new unbreakable-link issue.
- `geb-lean/docs/novelty-analysis.md` exists (177 lines); its content
  is a literature comparison of the `L ⊣ Φ` finite-copresheaf
  adjunction (the area-2 / area-8 result) against nerve-realization,
  essentially-algebraic theories, walking structures, and polynomial
  functors, concluding a conservative "appears novel." This is exactly
  the kind of category-1/2 antecedent-citation material the new section
  asks for, so "starting input, not a substitute for per-result search"
  (line 553-555) is accurate.
- Confirmed via the prior reviews that "no proof or build work"
  (Non-goals) and "overview depth" were settled before this addition,
  so the tension in finding 1 is a genuine interaction of the new
  element with already-converged text, not a re-litigation.

## Findings

### 1. MAJOR — per-result external search vs. "overview depth"

(The addition's open-ended per-result search is not reconciled with
the converged "overview depth, not an enormous diff" effort framing.)

Problem. The spec's effort model is "overview depth"
(lines 53, 72, 98) and bounded prose ("a large but bounded body of
prose", Risks/Scale, line 537). The new element adds, for *each*
headline declaration in *each* module across ~19 areas, a search
sweep over a long list of sources: Mathlib docs plus
`leansearch`/`Moogle`/`loogle`, the mathlib4 repo, Lean Zulip and
reservoir, then Coq stdlib/mathcomp, Agda stdlib/1lab, Isabelle AFP,
Rocq, and for novelty nLab/arXiv/standard references (lines 355-361).
The *prose* added per result is one line, and that is bounded by the
1-3-headline-decls budget — but the *work* to produce a defensible
one-line negative ("no prior Lean formalization found") is an
open-ended literature/formalization search that the rest of the spec's
effort framing does not account for. A reader budgeting the sweep from
the "overview depth, bounded prose" framing will under-estimate it;
the search is plausibly the single largest time cost in the whole
sweep, dwarfing the prose authoring.

Evidence. Goal bullet lines 79-85 and per-area **Provenance** bullet
lines 261-263 attach a tag to every headline result; the depth budget
(lines 269-277) bounds the *number of headline decls* and the *prose
length* but says nothing about research effort; Risks/Scale (line 537)
counts only "a large but bounded body of prose."

Why it matters. It is the one place the addition can silently break
the converged effort/scope contract. It does not make the element
unsound (best-effort + "provenance unverified" + non-gated give a
legitimate escape hatch), but the escape hatch is exactly what a plan
author needs told explicitly, or the search will either balloon or be
done so shallowly that category-1/2 claims are unjustified (see
finding 4).

Fix. Add one sentence to the depth budget or to Risks/Scale bounding
the *search* effort, not just the prose — e.g. "Provenance search is
time-boxed per headline result; when a confident classification is not
reached within that box, the tag is `provenance unverified` rather than
a deeper search." This converts the open-ended search into a bounded
one and makes the non-gated escape hatch operational rather than
aspirational.

### 2. MINOR — "one of four" vs. the underlying two axes

(The categories are presented as "one of four" but are really a
two-axis classification, and the concurrent-novel case is ambiguous.)

Problem. The element opens by placing each result "on two axes — is the
*mathematics* known, and does a prior *machine-checked formalization*
exist" (lines 333-335), which is the sound framing. But the Goal bullet
(line 80-81) and the surrounding prose describe picking "one of four
categories," and the four categories as written are not a clean product
of the two axes: categories 2/3/4 all presuppose "known maths," while
category 1 ("novel mathematics") says nothing about whether a
formalization exists. A result that is *novel maths* but has a
*concurrent external Lean formalization* (someone formalized the same
new idea independently) fits the spirit of both category 1 (novel) and
category 4 (existing Lean formalization elsewhere), and the four-way
"pick one" framing does not say which wins. This is not hypothetical
for an exploratory repo whose lead result (the `L ⊣ Φ` adjunction) is
claimed novel.

Evidence. Two-axis statement lines 333-335 vs. four-category list lines
337-353 (each of 2/3/4 begins "known maths"/"the result is established
in the literature"); category 4 (lines 350-353) is defined purely by
"a Lean formalization already exists elsewhere," with no "known maths"
qualifier, so it overlaps category 1 for a concurrently-formalized
novel result.

Fix. State that the two axes are recorded independently and the four
labels are the common combinations, not a forced single bucket — or add
one clause to category 1 covering "novel maths for which an external
formalization (concurrent or independent) is nonetheless found, cite it
and note concurrency." A half-sentence resolves it.

### 3. MINOR — calibration step may lack a category-1/2 exemplar

(The calibration step cannot guarantee a worked exemplar of the
most error-prone categories.)

Problem. Process step 3 (lines 511-513) requires the single
calibration area document to include "at least one worked **Provenance**
tag of each category encountered." Because "encountered" is scoped to
that one calibration area, and categories 1 (novel) and 2 (first
formalization anywhere) are precisely the rare, high-stakes labels, the
calibration doc may legitimately contain zero category-1/2 tags — so the
calibration reference, whose purpose is to set the standard before the
rest are authored, may set no standard for the two categories the spec
itself flags as "most costly to get wrong" (line 388-389) and routes to
the user (line 388). The wording is internally consistent (it only
demands categories actually encountered), but the calibration value is
weakest exactly where it is most needed.

Evidence. Step 3 lines 511-513 ("each category encountered") vs. the
Status paragraph's special treatment of categories 1/2 (lines 386-389)
and Risk lines 547-555 routing strong claims to the user.

Fix. Either pick a calibration area known to contain a category-1 or
-2 result (area 2 or 8, given `novelty-analysis.md` already covers the
`L ⊣ Φ` result), or add to step 3 "and, if no category-1/2 result falls
in the calibration area, a single worked example tag drawn from
elsewhere, so the conservative phrasing for those categories is
calibrated." The former is simpler and uses material that already
exists.

### 4. MINOR — date/scope stamp not carried in the template bullet

(The honesty hedge is stated, but the confidence-vs-evidence gap for
category-1/2 is only partially closed at the template level.)

Problem. The Status paragraph (lines 379-389) does the right things:
categories 1-3 are framed as negatives that "cannot be proven
exhaustively," each tag is implicitly date+scope stamped, "provenance
unverified" is the fallback, and category-1/2 claims are routed to the
user. The residual gap is that the *area documents themselves* are
reader-facing overview docs; a one-line "novel mathematics" tag in an
area doc reads as an assertion regardless of the meta-policy in the
spec. The spec requires the date+scope stamp (Risk line 551-552
"stamping each tag with its date and search scope") but the per-area
**Provenance** template bullet (lines 261-263) does not itself restate
that each tag must carry the date+scope stamp inline; a reader
following only the template could emit a bare "novel" tag.

Evidence. Template bullet lines 261-263 names only "a one-line
novelty-and-prior-formalization tag" with no stamping requirement; the
stamping requirement lives only in the Status paragraph (line 383-384)
and the Risk (line 551-552), one level removed from the template an
author writes against.

Fix. Add "(stamped with the search date and scope; see Status)" to the
template's **Provenance** bullet so the honesty requirement travels
with the instruction an author actually follows.

### 5. MINOR (non-gating) — prose-only areas carry no Provenance

(The Idris adaptation and prose-only area 7 interact correctly, but
the template should note Provenance is empty for prose-only areas.)

Problem. The Idris adaptation (lines 371-377) restricts Idris to
categories 1-2 with Lean cross-links, skipping the 3/4 search — coherent.
Area 7 (circuit frontend) is prose-only and owns no `.idr` file, hence
has no **Modules** entries and no headline declarations, hence no
**Provenance** tags. This is self-consistent because the Provenance
bullet is defined "for each headline definition/result named in
**Modules**" (line 261-262), and a prose-only area names none. But the
per-area template (lines 247-267) lists **Provenance** as a section
without noting it is absent/empty for prose-only areas, exactly as the
coverage discipline had to call out that a prose-only area contributes
no source link.

Evidence. Template section list lines 247-267; prose-only area 7 lines
207-221; coverage discipline's explicit prose-only tolerance lines
458-461.

Fix. Mirror the coverage note: add to the **Provenance** bullet or the
aggregator clause that prose-only areas (and pure aggregators) carry no
Provenance entries. Optional; the conditional "for each ... named in
Modules" already implies it.

## Counts by severity

- BLOCKER: 0
- MAJOR: 1 (finding 1: per-result external-search effort vs. the
  "overview depth / bounded prose" framing)
- MINOR: 4 (findings 2-5)

## Most important finding

Finding 1 (MAJOR): the addition imports an open-ended,
multi-database literature/formalization search for every headline
declaration, which the spec's converged "overview depth, not an
enormous diff" effort framing does not budget for. Bound the search
explicitly (time-box → `provenance unverified` fallback) so the
non-gated escape hatch is operational, otherwise the search either
balloons the sweep or is done too shallowly to justify the category-1/2
"novel"/"first" claims.
