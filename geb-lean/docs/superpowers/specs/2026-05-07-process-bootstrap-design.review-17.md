# Adversarial review cycle 17 — author responses

Review dispatched: fresh-context Agent against the
post-cycle-16 spec. **Reviewer's executive summary**:
*"Recommend approval. The cycle-16 fixes were applied
correctly; the residual minor findings are local
imprecisions that a careful implementer can resolve without
spec re-architecture and that do not break the design
intent."*

## Findings

### Blocker / Serious

**None.**

### Minor

**Min1 — On-boarding step 4 redundancy claim contradicted
the S2 "load-bearing" framing.**
The S2 paragraph called `fetch-tags` the load-bearing
mechanism for cutover-tag mirroring; step 4 said the fetch
is "functionally redundant for tag presence" because
`git clone` already mirrors all tags. The two paragraphs
disagreed about whether `fetch-tags` does anything in the
dominant on-boarding case.

*Fixed.* Reworded the S2 paragraph to call `fetch-tags` the
durable mechanism for ongoing cutover-tag mirroring, with
explicit framing: `git clone` mirrors tags one-shot at
clone time; `fetch-tags` keeps later `jj git fetch` calls
in sync as additional `cutover-*` tags appear, and covers
non-clone entry paths (e.g. `jj git remote add` against an
existing checkout). Step 4 was updated symmetrically: the
redundancy claim is preserved (correct in the dominant
case) and the durable role of `fetch-tags` is named
explicitly as forward-protection.

**Min2 — `check-jj-setup.sh` assertion form was specified
in changelog only; spec prose said only "shows" the
expected value.**
A "shows" assertion can be either string equality or
substring match; the changelog's regex
`glob:.*cutover-\*` would also match `glob:bug-cutover-*`,
which is broader than the spec's intent. The persistent
artefact left this looseness implicit.

*Fixed.* Both the script-description paragraph and
verification item 11 now state "output equals
`<expected>` exactly (anchored, not substring)". The
script-description paragraph also adds an example
counter-case for each of the two `jj config list`
assertions to make the intent unmistakeable: a
configuration of e.g. `conflicts() | description("private")`
correctly fails (a) and a configuration of e.g.
`glob:bug-cutover-*` correctly fails (b). The signing-check
clause (c) is unchanged; it remains a disjunction over two
authoritative paths.

**Min3 — Item 17 cross-reference to "user-direct push form,
distinct from any hook-allowlisted refspec".**
Reviewer marked optional. *Rejected (rationale).* Item 17
already says the tag-push commands are "performed in the
user's own terminal outside Claude Code (per § Hooks)";
that explicit cross-reference to § Hooks already covers
the user-direct distinction, since § Hooks documents the
no-tag-push-allowlist policy in detail. Adding a
parenthetical at item 17 would duplicate that pointer.

### Cosmetic-taste

**Cos1** — `refs/heads/feat-*` aesthetics.
*Rejected (cosmetic-taste, with rationale agreement.)*
Reviewer says "pure aesthetics". The C1 fix in cycle 16
chose `refs/heads/feat-*` deliberately as a neutral example;
no project-allowlisted refspec uses this form, so the
example does not collide with anything actually
configured.

**Cos2** — En-dash in section title.
*Rejected (cosmetic-taste, with rationale agreement.)*
Reviewer says "pure aesthetics". The en-dash matches
existing usage elsewhere in the spec.

## Convergence

Per the spec's own definition (*"all open findings are
cosmetic-taste, OR rejected with rationale, OR the reviewer
concludes the goal is unachievable"*) — the spec has
reached convergence:

- Zero blocker / serious findings.
- Two minor findings fixed (Min1 textual reconciliation;
  Min2 assertion-form tightening).
- One minor finding (Min3) rejected with rationale; the
  reviewer themselves marked it optional.
- Two cosmetic-taste findings rejected with rationale; the
  reviewer themselves identified them as pure aesthetics.

The cycle-17 fixes were textual refinements pre-suggested
by the reviewer, not new content. A further cold-context
cycle would re-read the same passages with no new material
to evaluate, so it is omitted.

## Cumulative status (cycles 1–17)

- Cycles 1–15: spec went from 1024 → 1625 lines through 15
  cold-context rounds; converged at cycle 15 with reviewer
  saying "the spec has converged".
- Cycle 16: jj 0.41 release prompted material spec edits;
  cycle 16 caught two serious + three minor + one
  cosmetic-taste defects, all fixed.
- Cycle 17: post-cycle-16 verification; zero serious;
  two minor fixed; one minor + two cosmetic-taste rejected
  with rationale.

Lint status: `markdownlint-cli2` against the spec file
is clean. The spec is at 1694 lines.
