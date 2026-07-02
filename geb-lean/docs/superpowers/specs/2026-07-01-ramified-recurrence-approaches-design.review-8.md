# Adversarial review 8 — ramified-recurrence approaches survey (orientation passage)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verification status](#verification-status)
  - [1. Compilation](#1-compilation)
  - [2. Quotation and line references](#2-quotation-and-line-references)
  - [3. Displayed equations vs `KMor1.simrecVec`](#3-displayed-equations-vs-kmor1simrecvec)
  - [4. Faithfulness to Leivant III](#4-faithfulness-to-leivant-iii)
  - [5. Illustrative-code honesty flags](#5-illustrative-code-honesty-flags)
- [Findings](#findings)
  - [Minor](#minor)
    - [R8-m1 — "strictly above" vs eq. (4)'s exact `Omega tau`](#r8-m1--strictly-above-vs-eq-4s-exact-omega-tau)
  - [Nit](#nit)
    - [R8-n1 — `r` vs `r_i` in the eq. (1) rendering](#r8-n1--r-vs-r_i-in-the-eq-1-rendering)
    - [R8-n2 — word-algebra equivalence rests on an unstated convention](#r8-n2--word-algebra-equivalence-rests-on-an-unstated-convention)
    - [R8-n3 — "the same idea"](#r8-n3--the-same-idea)
- [Gates](#gates)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc -->

Reviewed document:
`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`.
Scope of this round, per the review brief: the newly added
material in section 2.1 only — the "Orientation: recursion versus
recurrence" passage (between the Leivant III citation paragraph
and "Definitions and results to transcribe") and the reworked
free-algebra table row ("Free algebra; word algebra
(monadic/polyadic); tree algebra"). Content converged in rounds
1-7 was not re-reviewed.

Sources consulted this round: Leivant III (PDF pages 3-8, i.e.
journal pp. 211-216, re-read as page images),
`GebLean/LawvereKSim.lean`, `GebLean/LawvereKSimInterp.lean`, and
a compile check of the orientation's illustrative Lean code.

## Verification status

| Check | Result |
| --- | --- |
| 1. Compilation of the three Lean blocks | Pass — zero diagnostics |
| 2. `KMor1.simrec` quotation and line references | Pass — verbatim; both line numbers exact |
| 3. Displayed simrec equations vs `KMor1.simrecVec`; `k = 0` claim | Pass |
| 4a. Eq. (1) template; critical/monotonic/closed/flat terminology | Pass — matches the source verbatim |
| 4b. Eq. (4) typing in the closing paragraph | Pass |
| 4c. Recurrence/ramified-recurrence framing | Fair, with one minor caveat (R8-m1) |
| 4d. Word/tree algebra row vs p. 212 | Pass — equivalent given the paper's standing convention (R8-n2) |
| 5. Illustrative-code honesty flags | Adequate; residual nuance folded into R8-m1 |
| 6. Gates: markdownlint, doctoc, style | Pass |

### 1. Compilation

The three code blocks (the `Sig`/`FreeAlg`/`FreeAlg.recurse`
block, the `natSig`/`natZero`/`natSucc`/`natRecurse` block, and
the `TieredFn`/`TieredFn.interp` block) were concatenated in
document order into a scratch file with no imports and checked
with the Lean language server's diagnostics. Result: zero errors,
zero warnings, zero infos (`"items": []`, no failed
dependencies). The document's claim "illustrative and verified to
compile" holds. The scratch file was deleted after the check.

### 2. Quotation and line references

The quoted `simrec` block (document code fence following
"`GebLean/LawvereKSim.lean:50`") was diffed against
`GebLean/LawvereKSim.lean` lines 45-54 (docstring plus
constructor): byte-identical, including the two-space docstring
continuation indentation and the double space after
"family `g`.".

Line references: `| simrec {a k : ℕ}` is at
`GebLean/LawvereKSim.lean:50`; `def KMor1.simrecVec` is at
`GebLean/LawvereKSimInterp.lean:66`. Both citations are exact.

### 3. Displayed equations vs `KMor1.simrecVec`

`KMor1.simrecVec` (`GebLean/LawvereKSimInterp.lean:66-83`):

- Base case (`0`): each output is `(h j).interp params` —
  matches `f_j (0, x_1 ... x_a) = h_j (x_1 ... x_a)`.
- Step case (`n + 1`): `stepCtx` places `n` in slot `0`
  (`idx.val = 0`), `params ⟨idx.val - 1, _⟩` in slots `1, ..., a`
  (`idx.val < a + 1`, nonzero), and
  `prev ⟨idx.val - (a + 1), _⟩` — the vector
  `simrecVec h g params n`, i.e. all `k + 1` values at `n` — in
  the last `k + 1` slots. This matches
  `f_j (n + 1, x) = g_j (n, x, f_1 (n, x), ..., f_{k+1} (n, x))`
  in both content and argument order.

The claim "Ordinary (non-simultaneous) primitive recursion is the
case `k = 0`" is corroborated by the repository source itself:
`KMor1.rec1`'s docstring (`GebLean/LawvereKSim.lean`, lines
172-177) reads "Definitional reduction to `KMor1.simrec` with
`k = 0`, `i = 0`" and "the non-simultaneous case is the `k = 0`
specialization", and the definition instantiates
`KMor1.simrec (k := 0) (i := ⟨0, _⟩)`.

### 4. Faithfulness to Leivant III

(a) Eq. (1) and terminology (p. 212). The paper's template is
`f(x-vec, c_i(a_1 ... a_{r_i})) = g_{c_i}(x-vec, a-vec, phi_1,
..., phi_{r_i})` where `phi_j = f(x-vec, a_j)`, `i = 1 ... k`.
The terminology sentence reads, verbatim: "The functions
`g_{c_i}` are the *recurrence functions*, the variables `x-vec`
are the *recurrence parameters*, the argument of `f` exhibited
last in (1) is the *recurrence argument*, and the last `r_i`
arguments of `g_{c_i}` are the *critical arguments*." The
document's labeling — critical arguments = the last `r_i`
arguments of `g_ci`, i.e. the recursive values `phi_j` — is
correct. The fragment names also match the source exactly:
"If the arguments `a-vec` are all absent, then the recurrence is
*monotonic*. If the parameters `x-vec` are all absent, then the
recurrence is *closed*. If all critical arguments are missing,
then the recurrence is *flat*." The document's glosses (monotonic
= subterms absent, closed = parameters absent, flat = critical
arguments absent) are settled as correct against the source.

(b) Eq. (4) typing (p. 215). The paper displays
`f : sigma-vec, Omega tau -> tau` and
`g_{c_i} : sigma-vec, (Omega tau)^{r_i}, tau^{r_i} -> tau`,
`i = 1, ..., k`. The closing paragraph's rendering matches.

(c) Framing. "Recurrence is Leivant's name for the elimination
schema of a free algebra" is a fair gloss: eq. (1) is one clause
per constructor with recursive calls on the immediate subterms
(the step also sees the subterms — the paramorphism form — and
`FreeAlg.recurse` reproduces exactly that). "The same schema with
a sorting layer and nothing else ... the only change is a typing
constraint" is a fair summary of section 2.3: the eq. (4) display
is the eq. (3) display with the recurrence argument's type
changed from `o` to `Omega tau`, the r-types and the constructor
copies `c_i^theta` at every object type constitute the sorting
layer (and the document's own RRec-omega table row records the
constructor replication), and "every sort denotes a copy of the
same algebra" matches the paper's "extensionally,
`A^{Omega tau} = A^o`". One precision caveat is filed as R8-m1.

(d) Word/tree row (pp. 211-212). The paper sets
`r = max(r_1 ... r_k)` under the standing convention that `A` is
an infinite free algebra (hence has at least one constructor of
arity 0 and at least one of arity > 0), and defines: word algebra
iff `r = 1`, tree algebra iff `r > 1`, "A word algebra is
*monadic* if it has one unary constructor, *polyadic* if it has
several." Given the convention, "all arities at most 1" is
equivalent to `r = 1` (the positive-arity constructor forces
`r = 1` rather than `r = 0`), and "at least one constructor of
arity at least 2" is equivalent to `r > 1`. The row's closing
sentence — the monadic/polyadic distinction subdivides word
algebras only — matches the paper's phrasing, which defines
monadic/polyadic for word algebras. The row is faithful; a nit
on the unstated convention is filed as R8-n2.

### 5. Illustrative-code honesty flags

The three declared flags check out: `FreeAlg`'s docstring defers
to the polynomial-functor W-type implementation; `natRecurse`
states `P := Unit`; `TieredFn`'s docstring states monotonic,
without parameters or simultaneity. Candidate omissions were
judged as follows:

- `prec` taking a constant `base : Nat`: covered by the declared
  flags. With no parameters and the monotonic restriction, the
  base clause of eq. (1) over the unary naturals is a closed
  0-ary instance, i.e. a constant.
- `zeroConst` at arbitrary tier pairs: faithful. The 0-ary
  constructor exists at every object type (`c_i^theta`), and a
  constant function of any input tier is an explicit definition.
- `ident` only at equal tiers: faithful, and correctly so —
  cross-tier identities are Leivant's coercions (section 2.4
  (1)), which are defined by ramified recurrence rather than
  primitive, and are derivable in `TieredFn` as
  `prec (base := 0) (step := .succ)`.
- `prec` demanding `i < j` rather than exactly one tier: the one
  nuance the flags do not cover; filed as R8-m1.

## Findings

No blocker or major findings this round.

### Minor

#### R8-m1 — "strictly above" vs eq. (4)'s exact `Omega tau`

Eq. (4) fixes the recurrence argument's type at exactly
`Omega tau` for output type `tau` — one `Omega` above, not merely
above. The orientation states the constraint as "the recurrence
argument must carry a sort strictly above the output's", and
`TieredFn.prec` accordingly demands `i < j` (any strictly higher
tier); yet the closing paragraph describes the relation as "one
sort above", generated by `Omega` in place of "the successor on
tier numbers". The two glosses (strictly-above vs
successor/one-above) sit side by side without reconciliation, and
neither is flagged as diverging from eq. (4)'s exact form. The
divergence is harmless — the `i < j` former is the composite of
the one-step schema with the section 2.4 (1) coercions, which are
extensionally the identity and are derivable in `TieredFn` itself
(`prec 0 .succ`) — but the text should either state `prec`'s
`i < j` as folding in the coercions, or use `j = i + 1` in the
illustration to match the closing paragraph's "successor on tier
numbers".

### Nit

#### R8-n1 — `r` vs `r_i` in the eq. (1) rendering

The equational display for eq. (1) writes `c_i (a_1 ... a_r)` and
`f (x_vec, a_r)` with an unsubscripted `r`, although the
surrounding prose correctly says "for each constructor `c_i` of
arity `r_i`" and "the last `r_i` arguments". In the paper, `r`
without a subscript is reserved for the global maximum arity
`max(r_1 ... r_k)` (p. 211), so the display's `a_r` collides with
that convention. Write `a_{r_i}`.

#### R8-n2 — word-algebra equivalence rests on an unstated convention

"All arities at most 1" is equivalent to the paper's `r = 1` only
under the paper's standing convention that `A` is infinite (hence
has a constructor of positive arity); for a degenerate signature
of 0-ary constructors only, the two definitions differ. The
convention appears in the document only inside the section 2.4
(5) row ("arbitrary infinite `A`"). A parenthetical in the
free-algebra row (or a sentence in the orientation) recording the
infinite-algebra convention would close the gap.

#### R8-n3 — "the same idea"

"Unramified recurrence ... is the same idea over an arbitrary
free algebra": "idea" is loose where the exact word is available;
"the same schema" matches the sentence's content and the
surrounding usage.

## Gates

- `npx markdownlint-cli2` on the reviewed document: 0 errors.
- `npx doctoc --dryrun --update-only` on the reviewed document:
  "Everything is OK"; the new h4 heading "Orientation: recursion
  versus recurrence" is present in the TOC.
- Style sweep of the new text: no all-caps words, no value-laden
  adjectives, no emojis; the single looseness found is R8-n3.

## Convergence verdict

Converged for this scoped round. All six verification targets
pass: the illustrative code compiles with zero diagnostics, the
`simrec` quotation and both line references are exact, the
displayed equations match `KMor1.simrecVec`'s slot layout and the
repository's own `k = 0` statement, the critical-argument and
fragment terminology is settled as correct against the paper's
terminology sentence, the eq. (4) typing and the word/tree-algebra
row are faithful, and the lint gates are clean. The one minor
finding (R8-m1) and three nits are wording-level and do not
affect the section's mathematical content or the survey's
conclusions; they can be folded into the next editing pass
without a further review round.
