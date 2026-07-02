# Adversarial review 11 — ramified-recurrence survey (round-10 fix verification)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verification status](#verification-status)
- [Evidence](#evidence)
  - [1. R10-M1 — the `Omega tau` row](#1-r10-m1--the-omega-tau-row)
  - [2. R10-m1 — the `tau` row's paper-name column](#2-r10-m1--the-tau-rows-paper-name-column)
  - [3. Gates](#3-gates)
- [Resolution table](#resolution-table)
- [Findings](#findings)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewed document:
`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`.
Scope of this round, per the review brief: minimal verification of
the fixes applied for round 10's two findings (R10-M1 major,
R10-m1 minor), both on the two glossary rows appended in
section 2.1's orientation (the `tau` and `Omega tau` rows,
lines 242-243). The commit history confirms the diff since the
round-10 fix commit is confined to exactly those two rows; no
other passage of the document changed, so material converged in
rounds 1-10 was not re-reviewed.

Sources consulted this round: the round-10 review's transcribed
page evidence (Leivant III p. 214's `Omega`-introduction sentence,
eq. (4) p. 215, eq. (5) p. 215 with its flat-recurrence note, and
the section 2.3 r-type definition), against the document at
lines 228-243, 282-323, and 935-945.

## Verification status

| Check | Result |
| --- | --- |
| 1a. R10-M1 fix present: "critical arguments (recursive results) carry type `tau`" | Pass |
| 1b. Faithful to the paper's p. 214 sentence | Pass |
| 1c. Flat-recurrence sentence against eq. (5) and the paper's note | Pass |
| 1d. The row now singles out `Omega tau` (uniqueness restored) | Pass |
| 1e. No remaining conflict with section 6.1's flat-recurrence remark | Pass |
| 2a. "(recursive results)" cross-reference against glossary row four | Pass |
| 2b. Residue grep for the replaced phrasing; orientation consistency | Pass |
| 3. Gates: markdownlint, doctoc | Pass |

## Evidence

### 1. R10-M1 — the `Omega tau` row

The row's revised opening (line 243) now reads:

> `Omega` is a unary type constructor with no semantic content of
> its own: `Omega tau` is the type of base-algebra elements
> permitted to serve as the recurrence argument of a recurrence
> whose critical arguments (recursive results) carry type `tau`
> (paraphrasing the paper's p. 214; in eq. (4) the output is then
> also `tau`). Flat recurrence, having no critical arguments,
> takes its recurrence argument at `o` instead.

The remainder of the row (copy-of-carrier semantics, the iterate
example, section 2.4(3)) is unchanged from the text round 10
verified.

- (1b) The paper's sentence (p. 214, as transcribed in review 10):
  "We introduce a type-constructor, Omega, where Omega tau is
  intended as the type of those base objects that support
  recurrence with critical arguments of type tau." The row now
  characterizes `Omega tau` by the type of the critical arguments,
  matching the paper's chosen wording; "base-algebra elements" for
  "base objects" was already adjudicated faithful in round 10.
  The adopted text is the fix R10-M1 proposed, including its
  optional clause: the parenthetical "in eq. (4) the output is
  then also `tau`" is correct against eq. (4)'s
  `f : sigma-vec, Omega tau -> tau`.
- (1c) The added sentence matches eq. (5)'s typing (p. 215):
  `f : sigma-vec, o -> tau`,
  `g_{c_i} : sigma-vec, o^{r_i} -> tau` — recurrence argument at
  `o`, and no `tau^{r_i}` slots, hence no critical arguments. It
  is also consistent with the paper's adjacent note ("we do not
  stipulate flat recurrence for recurrence arguments of
  Omega-type"): flat recurrence is stipulated at `o` only, which
  is what "takes its recurrence argument at `o` instead" asserts.
- (1d) Uniqueness, the substance of R10-M1, is restored: an
  `o`-typed element can serve as the recurrence argument only of a
  flat recurrence (eq. (5)), which has no critical arguments; the
  only schema with critical arguments is eq. (4), whose recurrence
  argument carries `Omega tau`. The typing license the row
  describes is therefore uniquely `Omega tau`'s.
- (1e) Section 6.1 (lines 941-945): "no monotonic recurrence
  applies to the input (its recurrence argument must sit at an
  Omega-sort), and flat recurrence, which is available at sort
  `o`, passes no recursive results". The glossary row and this
  sentence now state the same division — monotonic recurrence at
  `Omega tau` with critical arguments at `tau`; flat recurrence at
  `o` with none — with matched vocabulary ("recursive results" /
  "critical arguments" via the row's parenthetical). The
  round-10 tension is gone.

Cross-reference check (2a): the glossary's fourth row (line 240)
gives the paper's name "critical arguments" and the document's
name "recursive results" for `phi_1 ... phi_{r_i}`; the revised
row's "critical arguments (recursive results)" pairs the same two
names in the same correspondence.

Residue and consistency checks (2b): the replaced phrase "whose
output type is `tau`" no longer occurs in the document. The
remaining "output type `tau`" occurrences (lines 319-321 in the
orientation's ramified paragraph; line 333 in the survey table)
state eq. (4)'s typing — recurrence argument `Omega tau` and
output `tau` together — not a definitional characterization of
`Omega`, so they neither duplicate the corrected error nor
conflict with the row. The recurrence-argument row's "(last two
rows)" pointer (line 238) still points at the `tau` and
`Omega tau` rows.

### 2. R10-m1 — the `tau` row's paper-name column

The column (line 242) now reads: r-type ("ramified functional
type"). This matches the paper's expansion "ramified functional
types (r-types for short)" (p. 214, as transcribed in review 10).
The finding's optional disambiguation clause (noting the paper's
second, narrower use of "functional") was not adopted; round 10
marked adopting or declining it as wording-level either way, and
the Role column of the same row already exhibits the narrower use
("all other r-types are functional"), so a reader can resolve the
overload in place. Resolved as adopted.

### 3. Gates

- `npx markdownlint-cli2` on the reviewed document: 0 errors.
- `npx doctoc --dryrun --update-only` on the reviewed document:
  no TOC change required.

## Resolution table

| Finding | Severity | Fix applied | Verdict |
| --- | --- | --- | --- |
| R10-M1 | Major | `Omega tau` row recharacterized by critical arguments ("critical arguments (recursive results) carry type `tau`"), with the eq. (4) output note and an added flat-recurrence sentence | Resolved — faithful to p. 214 and eq. (5); consistent with section 6.1 |
| R10-m1 | Minor | `tau` row's paper-name column: r-type ("ramified functional type") | Resolved — matches the paper's phrase |

## Findings

None. No new findings this round.

## Convergence verdict

Converged. Both round-10 findings are resolved by the applied
fixes: the `Omega tau` row now paraphrases the paper's p. 214
sentence by its own chosen characterization (critical arguments
of type `tau`), the added flat-recurrence sentence matches
eq. (5) and the paper's note and removes the tension with
section 6.1, and the `tau` row's paper-name column gives the
paper's phrase. The diff since round 10 is confined to the two
rows, all cross-references check, and both gates pass. No further
round is requested.
