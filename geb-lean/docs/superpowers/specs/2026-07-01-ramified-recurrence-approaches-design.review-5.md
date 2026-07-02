# Adversarial review 5 — ramified-recurrence approaches survey (round-4 fixes)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Verification performed](#verification-performed)
- [Resolution of round-4 findings](#resolution-of-round-4-findings)
  - [R4-M1 fix verification against the paper](#r4-m1-fix-verification-against-the-paper)
  - [R4-M2 fix verification against the URM and the paper](#r4-m2-fix-verification-against-the-urm-and-the-paper)
- [New findings](#new-findings)
  - [Minor](#minor)
    - [R5-m1 — The composite's item labels misplace the soundness route's start](#r5-m1--the-composites-item-labels-misplace-the-soundness-routes-start)
  - [Nit](#nit)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewed document:
`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`,
revision 2 with the round-4 fixes applied. This is a focused
convergence round: it verifies each round-4 fix against the current
document and the primary sources, and hunts for defects introduced
by those edits. Matters settled in round 4 were not re-litigated.

## Verification performed

- The current document was read in full; each edited region was
  checked against the corresponding round-4 finding.
- Leivant III PDF (journal pp. 220-223, read as page images):
  Proposition 7's statement with its four numbered items (p. 222),
  its proof paragraph and eq. (9) (p. 223), the section 4.1 calculi
  definitions and `RlMR-omega_o` reduction rules (p. 222), the
  section 4.2 `E` to `E-bar` mapping (p. 223), Lemma 6's statement
  and proof (p. 221), and the section 3.1 command definitions with
  the end-state convention (p. 220).
- `GebLean/Utilities/ZeroTestURM.lean`: the `URMInstr` constructors
  and `URMState.step` semantics (`assign i c` writes the constant
  `c`; `inc`/`dec` act in place, `dec` truncated at zero; `jumpZ`
  is the two-target zero-test jump; `stop` self-loops).
- Lint gates on the reviewed document: `markdownlint-cli2`
  0 errors; `doctoc --dryrun --update-only` "Everything is OK".

## Resolution of round-4 findings

| Finding | Status | Verification |
| --- | --- | --- |
| R4-M1 | Resolved (option (a)), with one residual relabeling defect (R5-m1) | Composite and both-calculi scoping present in sections 1.1, 2.1, 6.3, 8; legs match the p. 223 proof (detail below) |
| R4-M2 | Resolved | One-directional constant-overhead embedding in sections 1.2, 5.2, 6.2; checked against `ZeroTestURM.lean` and p. 220 (detail below) |
| R4-m1 | Resolved | Section 6.3 step 2 names Lemmas 8-10, the Berarducci-Boehm representation, and "the section 4.2 term translation `E` to `E-bar`"; step 3 adds "whose proof also uses Lemma 4 to reduce to target type `o`"; the 2.1 representation row carries the translation |
| R4-m2 | Resolved | Section 2.3 now reads "An unramified base calculus `S-minus` ... and its two-sorted (normal/safe) ramification `RS1-minus` (the 2022 paper renames the base `S1-minus`)" |
| R4-m3 | Resolved | Both copies of the quotation (sections 2.2 and 2.3) restore "(nat x ... x nat -> nat)-functions"; the two copies are word-identical |
| R4-m4 | Resolved | Section 3.3 restores the templates ("the PLFA Lean port (`rami3l/plfl`, DeBruijn and Substitution chapters) and the modular metatheory framework of arXiv `2512.09280` (availability unverified)"); section 6.3 now points at section 3.3; no reference to a revision-1 syntax survey remains |
| R4-m5 | Resolved | Phase 5's deliverable is "the pre-functor surjectivity family"; phase 7 reads "Assembly: `collapseFunctor_full` from phase 5's family and phase 6's functor"; the dependency order now holds |
| R4-n1 | Resolved | The 2.1 row reads "Lemmas 8-10 and Proposition 11" |
| R4-n2 | Resolved | `kappa-hat` and clocked-self-interpreter glosses marked "in this document's terms"; "poly-heap" attributed to the 2012 paper with Scholium 32 stating the polymax-versus-additive comparison; the incompleteness conjecture cited to pp. 15, 28 |
| R4-n3 | Resolved | None of "cleanest", "massaged", "issue", "heaviest" occurs; replacements ("avoids a type grammar entirely", "must be converted", "where this does not arise", "the largest single deliverable") conform |
| R4-n4 | Resolved | Phase 4 reads "the paper's section 2.4 example ladder" |
| R4-n5 | Resolved | `PolyAlgUMorph.lean` appears in the section 3.3 file list |

### R4-M1 fix verification against the paper

The fix implements round 4's option (a). The Proposition 7 row now
reads: "In scope as soundness apparatus: the composite (2) to (1)
(Lemma 1), (1) to (3) (eq. (9), p. 223), (3) to (4) (stated
'similar' to Lemma 1; its transcription reconstructs the indicated
argument). The remaining directions are deferred." Section 1.1
reads "both calculi return as proof apparatus for the soundness
direction, whose literature route runs through them
(section 6.3)"; section 6.3 step 1 spells out the same three legs
and concludes "Both applicative calculi therefore enter as
proof-internal apparatus"; section 8 phase 6 lists "the
`RlMR-omega`/`RlMR-omega_o`/`1l(A)`/Lemma 12 transcription".

Re-checked against the PDF: Proposition 7 (p. 222) has exactly the
four items (1) definable in `RMRec-omega`, (2) definable in
`RMRec-omega_o`, (3) defined by a term of `RlMR-omega`, (4) defined
by a term of `RlMR-omega_o`. The proof (p. 223) reads "(1) and (2)
are equivalent by Lemma 1, and the equivalence of (3) and (4) is
similar. (3) implies (1) trivially. The only observation of
interest is the implication from (1) to (3)", with eq. (9) and the
term `F = lambda x-bar. R-tau (G_1(x-bar)) ... (G_k(x-bar))`
landing in `RlMR-omega` (the `G_i` are `RlMR-omega` terms; the
motivation sentence contrasts recurrence with parameters against
the closed `R-tau` operators, as the document states). The three
legs, their instruments, and the flag on the unspelled (3)-(4) leg
therefore all match the paper. One residual defect in the item
numbering survives the fix; see R5-m1.

### R4-M2 fix verification against the URM and the paper

Section 1.2 now claims only: "Each instruction of the repository's
zero-test URM ... is a single command or a constant-length command
block of Leivant III's register machines over the unary algebra
(section 3.1 of the paper): `inc`/`dec` are in-place constructor
assignment and destructor, `assign i c` is a zero assignment
followed by `c` increments, `jumpZ` is the two-way branch, `stop`
is the end-state convention, and PC values are states," with the
reverse direction expressly disclaimed ("Leivant's cross-register
assignment and destructor commands have no single-instruction URM
counterpart; that direction is not needed"). Section 5.2 reads
"zero-test URM programs embed into Leivant's register machines
over the unary algebra with constant overhead (section 1.2)" (the
round-4 identity claim is gone); section 6.2 offers the two
adaptation shapes ("either the constant-overhead embedding of URM
programs into Leivant machines (section 1.2) followed by the
verbatim transcription, or the transcription of Lemma 6's proof
shape directly against the URM step relation; the plan phase picks
one").

Sanity checks, all passing. Against `ZeroTestURM.lean`:
`assign i c` writes the constant `c`, `inc`/`dec` act in place
(`dec` truncated at zero), `jumpZ i l_1 l_2` is a two-target
zero-test, `stop` self-loops — matching the instruction list the
document names. Against Leivant p. 220: the assignment command
`s -> s' | phi_0 := c_i phi_1 ... phi_{r_i}` includes the 0-ary
constructor case, and the unary algebra has a 0-ary constructor
(p. 220's configuration semantics fixes "some fixed 0-ary
constructor of A" as the input padding), so the zero assignment
exists as a single command and `assign i c` is a `c + 1`-command
block, constant-length for fixed program text. In-place `inc` is
the assignment with `phi_0 = phi_1` (the command grammar imposes
no distinctness). The destructor matches `dec` including the zero
case (`dstr_j(c_i(a-bar))` yields the argument unchanged when
`j > r_i`, p. 222, so `dstr_1(0) = 0` — truncation agrees). The
branch command `s(phi_0) -> s_1 ... s_k` with the unary algebra's
two constructors is the two-way zero-test, matching `jumpZ`. The
end-state convention ("we stipulate that every machine allows for
an idempotent repetition of the end state", p. 220) matches
`stop`'s self-loop. The claimed direction is the one Lemma 6's
transcription uses (elementary-time machine computation implies
ramified definability, applied to URM-computed functions through
the embedding).

## New findings

No blocker and no major findings. The new-defect hunt covered:
consistency of the edited scoping across sections 1.1, 2.1, 2.5,
6.3, 8, and 9; the two copies of the `E_2` quotation (word-
identical); the reworded CEK description against the unedited
cross-check summary sentence ("completeness arguments in this
family are machine simulations (CEK there, register machines in
Leivant III)" — consistent); cross-references (the section 3.3
template pointer is referenced by section 6.3; no dangling
references found); and the lint gates (both clean).

### Minor

#### R5-m1 — The composite's item labels misplace the soundness route's start

Location: section 2.1, applicative-calculi row ("since the paper's
route from (2) to (4) passes through `RlMR-omega`") and
Proposition 7 row ("the composite (2) to (1) (Lemma 1), (1) to
(3) ..."); section 6.3 step 1 ("From `RMRec-omega` to
`RlMR-omega_o`, as the paper's composite through Proposition 7
(p. 223): (2) to (1) by Lemma 1; ...").

Defect: Proposition 7 numbers the document's formalized system
`RMRec-omega` as item (1) and `RMRec-omega_o` as item (2). The
soundness direction starts from the formalized system, so the
composite it needs is (1) to (3) (eq. (9)) to (4) (the "similar"
leg). The "(2) to (1) by Lemma 1" leg belongs to a route starting
at `RMRec-omega_o` and is not part of the soundness direction;
prefixing it makes 6.3 step 1 internally inconsistent ("From
`RMRec-omega`" followed by a composite that starts at item (2)).
The mislabel originates in the pre-fix text's "the direction (2)
implies (4)" (quoted in R4-M1's location line) and was carried
into round 4's suggested wording; the fix's spelled-out legs make
it visible. Consequences are contained: the apparatus set is
unchanged (the (1)-(3) leg already lands in `RlMR-omega`, so both
calculi remain required; Lemma 1 remains in scope via the fullness
route, section 6.2 step 3), and the stated composite is valid as a
route from (2) — but the item labels would propagate as
citation errors into the design spec and docstrings.

Suggested fix: in the three locations, relabel the composite as
(1) to (3) (eq. (9), p. 223) to (4) (the "similar" leg), drop the
"(2) to (1) (Lemma 1)" leg from the soundness apparatus (noting,
if desired, that Lemma 1 is in scope through the fullness route),
and reword "the paper's route from (2) to (4)" to "the paper's
route from (1) to (4)".

### Nit

None.

## Convergence verdict

Converged. All twelve round-4 findings are resolved in the current
document; the two majors are fixed in the literature-faithful form
round 4 prescribed, and both fixes verify against the primary
sources (Leivant III pp. 220-223; `ZeroTestURM.lean`). The single
new finding, R5-m1, is a minor item-relabeling inside the R4-M1
fix with no effect on apparatus scope or proof route; it can be
folded into the next editing pass without a further adversarial
round.

Finding counts: 0 blocker, 0 major, 1 minor (R5-m1), 0 nit.
