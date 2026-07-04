# Adversarial review 9 — ramified-recurrence approaches survey (terminology glossary)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verification status](#verification-status)
  - [1. The glossary against Leivant III p. 212](#1-the-glossary-against-leivant-iii-p-212)
  - [2. Compilation](#2-compilation)
  - [3. Consistency](#3-consistency)
  - [4. Gates](#4-gates)
- [Findings](#findings)
  - [Minor](#minor)
    - [R9-m1 — "is easy to misread" (style)](#r9-m1--is-easy-to-misread-style)
    - [R9-m2 — flat gloss "only case analysis on the recurrence argument"](#r9-m2--flat-gloss-only-case-analysis-on-the-recurrence-argument)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewed document:
`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`.
Scope of this round, per the review brief: the terminology-glossary
revision inside section 2.1's "Orientation: recursion versus
recurrence" only — the revised intro paragraph of the
unramified-recurrence part, the renamed code identifiers
(`FreeAlg`'s field and `recurse`'s binder now `subterms`;
`natRecurse`'s binder now `results`), the eq. (1) display in the
paper's phi form, the five-row terminology glossary table, and the
revised fragments sentence; plus the two one-word consistency
changes elsewhere ("recursive results" in section 2.3's DLMZ bullet
and in section 6.1's flat-recurrence sentence). Content converged
in rounds 1-8 was not re-reviewed.

Sources consulted this round: Leivant III (PDF pages 3-7, i.e.
journal pp. 211-215, re-read as page images) and a compile check of
the orientation's illustrative Lean code.

## Verification status

| Check | Result |
| --- | --- |
| 1a. Glossary row: recurrence parameters = `x_vec` | Pass — verbatim |
| 1b. Glossary row: recurrence argument = the whole term `c_i (a_1 ... a_{r_i})` | Pass — the reading is unambiguous from (1) and corroborated by pp. 214-215 |
| 1c. Glossary row: `a_1 ... a_{r_i}` have no dedicated name | Pass — pp. 211-213 name them only descriptively |
| 1d. Glossary row: critical arguments; the eq. (1) display | Pass — verbatim; argument order and the phi letter match |
| 1e. Glossary row: recurrence functions = the `g_ci` | Pass — verbatim |
| 1f. Ramified cross-reference (`Omega tau` argument, eq. (4), p. 215) | Pass |
| 2. Compilation of the three Lean blocks | Pass — zero diagnostics; scratch deleted |
| 3. Consistency (identifiers, code references, one-word changes, fragments sentence) | Pass, with one wording finding (R9-m2) |
| 4. Gates: markdownlint, doctoc, style | markdownlint and doctoc pass; one style finding (R9-m1) |

### 1. The glossary against Leivant III p. 212

The paper's terminology sentence, immediately after display (1)
(p. 212), reads: "The functions g_{c_i} are the *recurrence
functions*, the variables x̄ are the *recurrence parameters*, the
argument of f exhibited last in (1) is the *recurrence argument*,
and the last r_i arguments of g_{c_i} are the *critical
arguments*." The paper's display (1) is

```text
f(x̄, c_i(a_1 ... a_{r_i})) = g_{c_i}(x̄, ā, φ_1, ..., φ_{r_i})
    where φ_j =_df f(x̄, a_j)
    i = 1 ... k
```

Row-by-row adjudication:

- (a) Recurrence parameters. The paper assigns the name to "the
  variables x̄". The glossary's row and role gloss (carried
  unchanged through every recursive call — in (1) the φ-clause
  passes `x_vec` intact to `f (x_vec, a_j)`) match. Pass.
- (b) Recurrence argument. The document asserts that "the argument
  of `f` exhibited last in (1)" denotes the whole constructor term
  `c_i (a_1 ... a_{r_i})`, not the components `a_j`. This reading
  is unambiguous from the display: the defining equation's
  left-hand side is `f(x̄, c_i(a_1 ... a_{r_i}))`, so the argument
  of `f` exhibited last is the whole term. The only competing
  reading — the `a_j` in the φ-clause's `f(x̄, a_j)` — fails on
  grammatical number (the sentence defines a single definite
  "recurrence argument", while the `a_j` are `r_i`-many per
  clause) and is excluded by every later use of the term:
  "Ωτ is intended as the type of those base objects that support
  recurrence with critical arguments of type τ" (p. 214, where the
  Ωτ-typed object is the recurrence input); eq. (4)'s typing
  `f : σ̄, Ωτ → τ` (p. 215), in which the last argument of `f` is
  the Ωτ one; "this reduction requires changing the type of the
  recurrence argument from Ωτ to Ω(σ̄ → τ)" (p. 215); and "(Note
  that we do not stipulate flat recurrence for recurrence
  arguments of Ω-type.)" (p. 215). Had "recurrence argument" meant
  the components `a_j`, none of these typings would parse. The
  row's role gloss ("the input being destructed, the last argument
  of `f`", matched as `.mk b subterms` in `recurse`) is exact.
  Pass.
- (c) No dedicated name for `a_1 ... a_{r_i}`. The terminology
  sentence names exactly four items (recurrence functions,
  recurrence parameters, recurrence argument, critical arguments)
  and none of them is the component vector. Searching pp. 211-213:
  the height clause writes `|c_i(a_1 ... a_{r_i})| =
  1 + max(|a_1| ... |a_{r_i}|)` (p. 211); the monotonic sentence
  refers to them descriptively as "the arguments ā" (p. 212),
  which corroborates the row's parenthetical "written `a_vec`";
  the destructor equations return `a_j` without naming the vector
  (p. 212); eq. (3) writes `(ā)` (p. 213). No dedicated term
  exists in the surrounding text. Pass.
- (d) Critical arguments. The paper's phrase "the last r_i
  arguments of g_{c_i}" is quoted verbatim (modulo ASCII
  transliteration `g_ci`), and the paper's φ-clause
  `φ_j =_df f(x̄, a_j)` identifies them as the recursive results.
  The document's eq. (1) display matches the paper's in argument
  order (`x_vec`, `a_vec`, `phi_1, ..., phi_{r_i}`) and in the
  letter phi (the paper uses φ, not ψ). Deviations are
  transliteration only, plus two absorbed conventions: the paper's
  "=_df" is rendered "=", and the display line "i = 1 ... k" is
  carried by the document's prose quantifier "for each constructor
  `c_i` of arity `r_i`". Pass.
- (e) Recurrence functions. The paper: "The functions g_{c_i} are
  the recurrence functions." The row and its "one per constructor"
  gloss match. Pass.
- (f) Ramified cross-reference. Eq. (4) is on p. 215 with typing
  `f : σ̄, Ωτ → τ` and `g_{c_i} : σ̄, (Ωτ)^{r_i}, τ^{r_i} → τ`;
  the recurrence argument is the Ωτ-typed one, as row (b) states,
  and the document's closing eq.-(4) paragraph reproduces both
  typings. Pass.

### 2. Compilation

The three standalone code blocks (the `Sig` / `FreeAlg` /
`FreeAlg.recurse` block, the `natSig` / `natZero` / `natSucc` /
`natRecurse` block, and the `TieredFn` / `TieredFn.interp` block;
the `KMor1.simrec` block is an excerpt of an existing repository
inductive and is not standalone) were concatenated in document
order into a scratch file with no imports and checked with the Lean
language server's diagnostics. Result: zero errors, zero warnings,
zero infos (`"items": []`, no failed dependencies). The scratch
file was deleted after the check.

### 3. Consistency

- No occurrence of "recursive values" remains anywhere in the
  document.
- No occurrence of the old binder names remains in the
  orientation: `recs` does not occur in the document; the only
  `args` occurrence is section 4.2's `Tm` interface (`op`
  constructor), which is outside this round's scope and correct
  there.
- The glossary's code references match the blocks as printed:
  `recurse` binds `x` (of type `P`) and matches `.mk b subterms`;
  `natRecurse` binds `results` in its `true` branch.
- The two one-word changes are in place and read consistently with
  the glossary: section 2.3's DLMZ bullet ("subterms at the high
  tier and recursive results at the low tier") and section 6.1's
  flat-recurrence sentence ("passes no recursive results").
- The fragments sentence matches the paper's definitions (p. 212:
  monotonic = the arguments ā all absent; closed = the parameters
  x̄ all absent; flat = all critical arguments missing) and the
  glossary's terms (subterms / parameters / recursive results),
  with one wording finding on the flat gloss (R9-m2).

### 4. Gates

- `npx markdownlint-cli2` on the reviewed document: 0 errors.
- `npx doctoc --update-only` on the reviewed document: no change
  (`git diff` empty afterward); the TOC is current.
- Style on the new text: the glossary's role glosses and the
  revised intro paragraph are dry and neutral; one phrase falls
  short of the bar (R9-m1). No colloquialisms or metaphors found
  in the revised fragments sentence or the two one-word changes.

## Findings

No blockers. No majors.

### Minor

#### R9-m1 — "is easy to misread" (style)

The glossary's introductory sentence reads: "The paper's naming
(its section 2.1, the sentence after eq. (1)) is easy to misread,
so the correspondence with the code above is fixed here piece by
piece". "Easy to misread" is a difficulty judgment about the
reader, and the preceding paragraph already states the operative
fact ("The paper's names for these pieces differ from the ones
used here"). A neutral form carries the same content, e.g.:
"Terminology glossary. The correspondence between the paper's
naming (its section 2.1, the sentence after eq. (1)) and the code
above, piece by piece:".

#### R9-m2 — flat gloss "only case analysis on the recurrence argument"

The fragments sentence glosses flat recurrence as "no critical
arguments, i.e. no recursive results - only case analysis on the
recurrence argument". In the paper's own vocabulary, "case" names
the branching function `case_A`, which selects among `x_1 ... x_k`
by main constructor and discards the subterms; flat recurrence is
strictly stronger — the paper's two examples of flat-recurrence
definitions are the branching function and the destructors
(p. 212), and the document's own section 6.1 says "case analysis
and destructors only". Under a pattern-matching reading of "case
analysis" (a match that binds the subterms, as `recurse` does) the
gloss is defensible, but the glossary passage exists to remove
exactly this kind of ambiguity. Suggested alignment with section
6.1: "only case analysis and destructors on the recurrence
argument" (or "the clause still sees the parameters and
subterms").

## Convergence verdict

Converged for this scoped round. Every glossary row is verified
against Leivant III p. 212, with the recurrence-argument reading
(row b) corroborated by the paper's later uses on pp. 214-215; the
eq. (1) display matches the paper's phi form; the renamed
identifiers, code references, and the two one-word consistency
changes check out; the three Lean blocks compile with zero
diagnostics; markdownlint and doctoc pass. The two minor findings
(R9-m1 style phrase, R9-m2 flat gloss) are wording-level, do not
affect the correctness of the glossary, and can be adopted or
declined without a further review round.
