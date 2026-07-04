# Adversarial review 3 — ramified-recurrence approaches survey

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Round-2 finding resolution](#round-2-finding-resolution)
- [Verification of the R2-M1 fix](#verification-of-the-r2-m1-fix)
  - [The substitution-fixed-point claim](#the-substitution-fixed-point-claim)
  - [The copoint scoping](#the-copoint-scoping)
  - [Residual assumptions sweep](#residual-assumptions-sweep)
- [New findings](#new-findings)
  - [Minor](#minor)
    - [R3-m1 — Unqualified "no term of type o -> Omega o exists" is literally false](#r3-m1--unqualified-no-term-of-type-o---omega-o-exists-is-literally-false)
  - [Nit](#nit)
    - [R3-n1 — "First-order systems" versus the first-order subcategory left implicit](#r3-n1--first-order-systems-versus-the-first-order-subcategory-left-implicit)
- [Lint gates](#lint-gates)
- [Convergence verdict](#convergence-verdict)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Reviewed document:
`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`.
Round-2 review:
`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.review-2.md`.
This is a focused convergence round: it verifies that each round-2
finding is resolved, re-checks the mathematics of the R2-M1 fix
against the Leivant III PDF (pp. 213-218 were re-read for this
round), checks the mutual consistency of the edited regions
(sections 4.4, 4.5, 7.1) with sections 1.4 and 4.6, and re-runs the
lint gates. Matters settled in rounds 1-2 were not re-litigated.

## Round-2 finding resolution

| Finding | Status | Evidence |
| --- | --- | --- |
| R2-M1 (`kappaHat` typed against `omegaShift.obj [τ]`) | Resolved | Section 4.4 now declares `def kappaHat (τ) : (([RType.omega τ] : SynCat Σ E) ⟶ [τ])`, with the docstring "This is a morphism at the sort Omega tau, not at omegaShift.obj [tau]: the two agree exactly on the first-order sorts (tau[o := Omega o] = Omega tau iff tau = Omega^m o), so kappaHat supplies a copoint for omegaShift on the first-order systems only." Section 4.5 lists "`kappaHat` at every r-type; the copoint `omegaShift ⟹ Id` it induces on the first-order systems (section 4.4). No copoint is expected on the higher-order system." Open question 7.1 scopes the copointed reading: "supported by `kappaHat` on the first-order systems, where the shift's image sorts are Omega-sorts; not expected on the higher-order system, whose arrow sorts admit no raising term - section 4.4". Mathematics verified below; one residual precision defect in a supporting clause (R3-m1). |
| R2-m1 (stale "section 7.5" in 3.2) | Resolved | Section 3.2 now reads "Open sub-question (spike candidate, section 7.3): which combinator basis suffices for the fullness proof", matching section 6 item 5 and open question 3. |
| R2-n1 (all-caps emphasis) | Resolved | Section 4.4: "Postcomposition with Omega is not a signature morphism"; section 4.6: "bsum, bprod by novel constructions in the style of sections 2.4(2) and 2.6". No all-caps non-acronym words remain in either docstring. |
| R2-n2 ("the last three rows" miscount) | Resolved | Section 1.1 now names the rows: "except as annotated in the rows for the applicative calculi, Proposition 7, and Theorem 14 (the lambda-calculus content is transcription only under option C of section 3.2)". |
| R2-n3 (unhedged universal negative in 1.4) | Resolved | The final 1.4 bullet now reads "no formalization of ramified recurrence, the Grzegorczyk hierarchy, or a Kalmar-elementary characterization was found in any proof assistant (section 2.2)", aligned with section 2.2's hedged phrasing. |
| R2-n4 (split code span in the Tourlakis reference) | Resolved | The References entry renders the path as a single code span: "The verified quotations are recorded in `docs/research/2026-04-30-ksim-polynomial-bound-references.md`." The copy-paste defect is gone. (The round-2 suggestion of a repo-relative link was one option; a single code span equally resolves the defect, and a code-span path is not a link, so the link conventions of `.claude/rules/markdown-writing.md` are not implicated.) |

## Verification of the R2-M1 fix

### The substitution-fixed-point claim

The docstring's parenthetical
"`tau[o := Omega o] = Omega tau` iff `tau = Omega^m o`" is correct.
Writing `S(tau)` for the base substitution (a total structural
recursion on the free generation of r-types from `o` by `->` and
`Omega`, Leivant III p. 214):

- If `tau = Omega^m o` then
  `S(tau) = Omega^m (Omega o) = Omega^{m+1} o = Omega tau`.
- Conversely, by structural induction: for `tau = o`,
  `S(o) = Omega o` (the case `m = 0`); for `tau = arrow sigma rho`,
  `S(tau)` is an arrow type while `Omega tau` is an `Omega`-type,
  and the two constructors of the free generation are distinct, so
  equality is impossible; for `tau = Omega sigma`, injectivity of
  `Omega` reduces `Omega (S(sigma)) = Omega (Omega sigma)` to
  `S(sigma) = Omega sigma`, whence `sigma = Omega^m o` by induction
  and `tau = Omega^{m+1} o`.

The arrow case disposes of both probe instances: `tau = arrow σ ρ`
directly, and `tau = Omega (arrow σ ρ)` via the induction (its shift
is `Omega (arrow (S σ) (S ρ))`, not `Omega Omega (arrow σ ρ)`).

### The copoint scoping

The scoping is coherent. A copoint component at object `[tau]` has
type `[S(tau)] ⟶ [tau]`; at a first-order sort `tau = Omega^m o`
the fixed-point claim gives `S(tau) = Omega tau`, so the component
type is exactly `kappaHat`'s declared type there
(`Omega^{m+1} o -> Omega^m o`). At every other sort — including
object sorts such as `Omega (arrow o o)` — the two types differ, so
`kappaHat` supplies copoint components on the first-order sorts and
nowhere else, as the docstring states.

Against the source: Leivant III p. 216(1) defines a coercion
function as "a function between object types, that is extensionally
the identity", introduces the auxiliary
`kappa-hat_tau : Omega tau -> tau` for every r-type `tau`, and sets
`kappa_tau(a) = kappa-hat_tau(a)(C^{sigma-vector})` — confirming
both the `[Omega tau] ⟶ [tau]` typing at every r-type and the
document's naming note that the paper reserves `kappa_tau` for the
composite into the output object type. All coercions of
section 2.4(1) go downward (`Omega tau -> theta`, `theta -> o`);
nothing in the paper provides an upward map inside the system. The
section 2.7 raising `G -> G^{+tau}` is a discourse-level mapping
(p. 218: "defined jointly by discourse-level recurrence on tau"),
not a term of the calculus, so it does not supply a raising term
either. The absence of a raising coercion is not stated as a result
in the paper — it follows from Theorem 14 (a level-preserving
coercion `o -> Omega o` extensionally the identity would let
second-order recurrence iterate `exp` at a fixed tier, breaking the
elementary bound) — so the document's presentation of the
higher-order non-copoint as an expectation feeding open question
7.1, rather than a citable fact, is the appropriate register.

### Residual assumptions sweep

All occurrences of `kappaHat`, copoint, and `omegaShift` were
checked. Section 4.4 (both docstrings), section 4.5 (three bullets),
section 4.6 ("comp by level alignment - via omegaShift where
available, otherwise via object-type-indexed families of
realizers"), section 6 item 2 (first-order deliverables), and open
question 7.1 are mutually consistent: the endofunctor is
unconditional only on the first-order systems, the higher-order
existence is routed through 7.1, the copoint is claimed on the
first-order side only, and no passage still assumes a higher-order
copoint or the old `kappaHat` typing. Section 1.4's novelty list
("the `Omega`-shift functor ... and the analysis of its structure
(section 7.1)") covers the copoint analysis; `kappaHat` itself
remains transcription under the section 1.1 coercion row, correctly.
The 4.6 fullness sketch depends on `omegaShift` only conditionally
("where available") with the paper's own object-type-indexed
fallback (p. 216(3)), so the in-scope theorem does not rest on the
open question.

## New findings

### Minor

#### R3-m1 — Unqualified "no term of type o -> Omega o exists" is literally false

Location: section 4.4, `kappaHat` docstring: "On the higher-order
system a copoint component at an arrow sort would need a raising
term, and no term of type o -> Omega o exists, so no copoint of
omegaShift is expected there".

Defect: read literally, the middle clause asserts that the hom-set
`[o] ⟶ [Omega o]` is empty, which is false: constructor constants
are posited at every object type (p. 214, "for each object type
theta and each constructor c_i of A we posit a constant c_i^theta"),
`Omega o` is an object type, and explicit definitions may ignore
arguments, so a constant term of type `o -> Omega o` exists. The
true and intended claim is that no raising term — a coercion
extensionally the identity, in the p. 216(1) sense — exists at that
type (a constant component also cannot form a copoint, since
naturality against, e.g., the successor fails). Open question 7.1
already carries the qualified form ("whose arrow sorts admit no
raising term"); only the 4.4 clause overclaims.

Suggested fix: qualify the clause, e.g. "and no raising term of
type o -> Omega o exists (constant inhabitants exist, but no term
extensionally the identity)", or simply "and no such raising term
exists".

### Nit

#### R3-n1 — "First-order systems" versus the first-order subcategory left implicit

Sections 4.4 and 4.5 say `kappaHat` "supplies a copoint for
omegaShift on the first-order systems", but the declared `kappaHat`
lives at `RType` sorts, i.e. in the higher-order syntactic category;
restricted to the sorts `Omega^m o` it gives copoint components on
`SynCatFO` (section 4.6), while the first-order presentations
(`S = N`, section 3.6) need the transcribed tier-indexed analogue
`[m+1] ⟶ [m]` — definable there, since `kappa-hat`'s defining
recurrence at `Omega^m o` mentions only object sorts, but a
different declaration. The transfer mechanism ("the copoint ... it
induces on the first-order systems", section 4.5) is left implicit.
Acceptable at survey granularity; the design spec should distinguish
the `SynCatFO` restriction from the `S = N` analogues when it fixes
the deliverable.

## Lint gates

`npx markdownlint-cli2` on the reviewed document: 0 errors.
`npx doctoc --dryrun --update-only` on the reviewed document:
"Everything is OK".

## Convergence verdict

Converged. All six round-2 findings (1 MAJOR, 1 MINOR, 4 NIT) are
resolved; the R2-M1 fix is mathematically sound in its typing,
fixed-point claim, and scoping. New findings this round: 0 BLOCKER,
0 MAJOR, 1 MINOR (R3-m1, a supporting clause that overclaims and
should be qualified), 1 NIT. The MINOR item is a one-phrase edit and
does not require a further review round.
