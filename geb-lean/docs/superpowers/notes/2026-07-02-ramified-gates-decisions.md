# Ramified recurrence gate decisions (Phase 0)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Plan-fixed decisions (restated)](#plan-fixed-decisions-restated)
- [G1: Beckmann-Weiermann bridge](#g1-beckmann-weiermann-bridge)
  - [Framing (spec s1.2)](#framing-spec-s12)
  - [Searched space](#searched-space)
  - [Consequence](#consequence)
- [G2: LawvereGodelT* audit](#g2-lawveregodelt-audit)
- [G3: landing choice](#g3-landing-choice)
- [G4: Otto 1995](#g4-otto-1995)
  - [Acquisition](#acquisition)
  - [Overlap with spec s2.5 novelty claims](#overlap-with-spec-s25-novelty-claims)
  - [Docstring precedent for Phases 1-2](#docstring-precedent-for-phases-1-2)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

This note records the Phase 0 gate outcomes for the ramified-recurrence
workstream, one section per gate, and restates the plan-fixed decisions
so downstream sub-plans cite a single document. It accompanies the plan
[`docs/superpowers/plans/2026-07-02-ramified-recurrence-plan.md`](../plans/2026-07-02-ramified-recurrence-plan.md)
and the spec
[`docs/superpowers/specs/2026-07-01-ramified-recurrence-approaches-design.md`](../specs/2026-07-01-ramified-recurrence-approaches-design.md).

The workstream formalizes Leivant's higher-order ramified recurrence
system `RMRec-omega` as a multi-sorted Lawvere theory and proves an
elementary-recursion definability correspondence against
`LawvereERCat`. The source is Leivant, "Ramified recurrence and
computational complexity III: Higher type recurrence and elementary
complexity", Annals of Pure and Applied Logic 96 (1-3) (1999) 209-229,
DOI 10.1016/S0168-0072(98)00040-2.

## Plan-fixed decisions (restated)

The spec delegates the following to the plan phase (spec s5.1, s6.2,
s6.4, s7, s8). Adversarial review of the plan reviews these decisions.
Numbering matches the plan appendix. Where the spec offers alternatives,
the decision below is faithful semantics with prose adapted to this
note's context.

1. Lemma 6 adaptation format (spec s6.2): transcribe Lemma 6's proof
   shape directly against the zero-test URM step relation
   (`GebLean.URMState.step`), not via the constant-overhead embedding of
   URM programs into Leivant's register machines. The embedding route
   would formalize Leivant's machine family (states, three command
   kinds) as a new formal object used only to be erased again; the
   direct route targets the object `compileER` already produces. The
   spec s1.2 embedding argument is recorded in the transcription's
   docstring as the fidelity justification, and the adaptation is of the
   presentation kind spec s1.2 permits.
2. Statement target (spec s5.1): both s6.1 statements are stated against
   `LawvereERCat`. The definability chain starts ER-side (`compileER`
   plus `boundExprKParams_dominates`), which requires no K^sim hop. The
   soundness landing follows gate G3, defaulting to the K^sim simulator
   pattern with transfer across `erKSimEquiv` (spec s5.1
   recommendation).
3. Host algebra (spec s5.2): the in-scope proof is hosted over `1 + X`.
   The `1 + 2 X` and `1 + X^2` instantiations receive structure and
   smoke tests only (Phase 3); the tree-algebra corollary is future work
   (spec s9).
4. Sub-plan gates: Phases 5 and 6 execute behind sub-plans. Phase 6 is
   the workstream's dominant cost (spec s6.3) and its route is
   gate-dependent; fabricating its step detail before the gates close
   would violate the no-speculation discipline the spec's gates enforce.
5. Naming and file structure: fixed in the plan's structure section. The
   spec's sketch names are kept where present (from s4.2: `SortedSig`,
   `Tm`, `standardModel`, `interpSetoid`, `QuotRel`, `SynCat`, `RType`,
   `higherOrder`; from s6.1: `SynCatFO`, `collapseFunctor`,
   `ramified_definability`); the free-algebra signature data is named
   `AlgSig` (the spec's illustrative `Sig`), avoiding a parallel meaning
   for "signature" against `SortedSig`.
6. Object-sort structure (spec open question 5): `Presentation` carries
   the sort type `S`, the operation signature, and the object-sort
   predicate `IsObj : S -> Prop` as plain data (a structure, not a
   typeclass).
7. Sorted-context indexing (spec open question 4): contexts are
   parameters, not index components. The sort type `S` is the domain and
   codomain of the slice polynomial endofunctor, and a context `Gamma`
   enters as the `S`-indexed variable family the free monad is taken
   over. Decision 8's free-monad substitution requires variables to
   occupy the monad's unit positions, which is the contexts-as-parameters
   form; `Tm.subst` is then bind along a map of variable families.
8. Representation (spec s7, s1.1; user decision 2026-07-02): every
   recursive type in this development is a W-type (`PolyFix`) of a
   `PolyEndo`; Lean-native recursive inductive types are not used
   anywhere in it. This is the spec's approach B chosen under s7's
   no-spike default, strengthened from s1.1's "syntax as W-types where
   practicable" to unconditional. Grounds: `PolyEndo` supplies limits,
   colimits, hom-objects, initial algebras, terminal coalgebras, and
   universal properties on algebras, coalgebras, and the functors
   themselves; substitution and its laws come from free-monad structure
   (bind) rather than per-system proofs; and multi-sorted signatures are
   subsumed by taking the sort type as the domain and codomain of the
   slice polynomial endofunctor. The free-monad structure already exists
   in the repository (`PolyFreeM`, `polyFreeMBind`, and its monad laws,
   `GebLean/PolyAlg.lean:3344,:3980,:3993-:4021`; the adjunction monad
   `polyFreeMonad` at `:9615`) and is consumed, not rebuilt. For binder
   calculi (Phase 6 route L), whose contexts index the syntax so
   variables do not occupy the monad's unit positions, substitution is
   instead defined by the corresponding indexed folds. Approach C (the
   vendored slice/presheaf functors) remains the convergence target; the
   migration replaces the underlying polynomial-functor stack under the
   same construction. The ergonomics cost the spec's s7 table assigns to
   B (custom recursors: `PolyFix.ind`, `polyFixFold` in place of native
   `induction`) is accepted and absorbed by Phase 1, with no native
   fallback.

## G1: Beckmann-Weiermann bridge

Verdict: `no-bridge`.

### Framing (spec s1.2)

The soundness direction (spec s6.3) collapses `RMRec-omega`-definable
functions to the elementary recursive functions via a normalization
argument. The repository already carries a partial formalization of the
Beckmann-Weiermann `T*` fragment of Godel's T (Beckmann, Weiermann,
"Characterizing the elementary recursive functions by a fragment of
Godel's T", Archive for Mathematical Logic 39 (2000) 475-491, DOI
10.1007/s001530050160), including a lambda-free typed combinatory
calculus, a reduction relation, and the Lemma 16 tower bound
(`GebLean/LawvereGodelT*`). Reusing that asset for the soundness
direction, rather than developing a new normalization proof, requires a
translation from `RMRec-omega` (or from the `1l(A)`-represented
functions of Leivant III sections 4.2-4.3) into `T*` or an equivalent
lambda-free fragment with Lemma-16-style bounds.

Under the transcription-only policy (spec s1.2), such a translation may
be transcribed only if it is a published result. An unpublished
translation, however plausible, fails the policy. The question G1
answers is therefore whether a published bridge exists, not whether one
could be constructed.

### Searched space

Search performed 2026-07-02 with `theorem_search` (theoremsearch MCP),
the arxiv-mcp-server tools, and web search. Each candidate is recorded
with its identifier and the specific claim inspected. All were found not
to supply the required bridge.

| Candidate | Identifier | Claim inspected | Bridges `RMRec-omega`/`1l(A)` into `T*`? |
| --- | --- | --- | --- |
| Beckmann, Weiermann, "Characterizing the elementary recursive functions by a fragment of Godel's T", Arch. Math. Logic 39 (2000) 475-491 | DOI 10.1007/s001530050160 | Defines `T*` (recursor/iterator applied only to type-0 arguments); proves `T*`-representable = elementary recursive via Howard-Schutte derivation-length bounds (the Lemma 16 tower). Independent characterization; abstract and body target the fragment directly, not Leivant's system. | No. Source of `T*`; no Leivant translation. |
| Leivant, "Ramified recurrence and computational complexity III", APAL 96 (1999) 209-229 | DOI 10.1016/S0168-0072(98)00040-2 | Own soundness route: applicative calculi `RlMR-omega`/`RlMR-omega_o`, Berarducci-Boehm `1l(A)` representation, normalization-time Lemma 12 / Proposition 13. Lands in elementary time by its own normalization argument, not by any translation into `T*`. | No. This is the route spec s6.3 steps 1-3 transcribe. |
| Kristiansen, Voda, "The Surprising Power of Restricted Programs and Godel's Functionals", CSL 2003, LNCS 2803, pp. 345-358 | DOI 10.1007/978-3-540-45220-1_28 | Restricted imperative programs and Godel functionals; elementary and related characterizations. Cites Leivant's intrinsic-theories line generally; no term-level translation of `RMRec-omega`/`1l(A)` into `T*`. | No. |
| Ostrin, Wainer, "Proof theoretic complexity", in Schwichtenberg, Steinbruggen (eds.), Proof and System-Reliability, Kluwer, Dordrecht (2002), 369-397 | DOI 10.1007/978-94-010-0413-8_12 | `EA(I;O)` predicative-arithmetic route: provably recursive functions are the elementary functions; slow-growing hierarchy analysis yielding epsilon_0 pointwise. Independent proof-theoretic characterization, arithmetic-side; no translation of Leivant's calculus into `T*`. | No. |
| Ostrin, Wainer, "Elementary arithmetic", APAL 133 (2005) 275-292 | DOI 10.1016/j.apal.2004.10.012 | Abstract and introduction: imposes the Bellantoni-Cook safe/normal variable discipline on arithmetical theories (quantify over safes, induct on normals), reworking and extending Leivant's earlier results to give proof-theoretic characterizations, by induction level, of complexity classes between Grzegorczyk's `E2` and `E3`. An arithmetic-theoretic (`EA(I;O)`) predicative-induction characterization of elementary-type function classes, not a term-level translation of `RMRec-omega` or `1l(A)` into `T*` or any lambda-free fragment of Godel's T. | No. |
| Wainer, Williams, "Inductive definitions over a predicative arithmetic", APAL 136 (2005) 175-188 | DOI 10.1016/j.apal.2005.05.011 | Extends the `EA(I;O)` predicative-arithmetic framework by inductive definitions; recaptures stronger systems in the slow-growing setting. Arithmetic-side; no `RMRec-omega`-to-`T*` translation. (Distinct from Cagman, Ostrin, Wainer, "Proof theoretic complexity of low subrecursive classes", in Foundations of Secure Computation, NATO Sci. Ser. F vol. 175, IOS Press (2000) 249-285, an earlier paper by different authors on a related theme.) | No. |
| Schwichtenberg, "Classifying recursive functions", in Griffor (ed.), Handbook of Computability Theory, Studies in Logic and the Foundations of Mathematics vol. 140, North-Holland (1999) 533-586 | DOI 10.1016/S0049-237X(99)80032-9 | Full text inspected (converted from the author's PostScript source). Surveys classification of the recursive functions by transfinite recursion and by recursion in higher types, including the Grzegorczyk hierarchy, the fast-growing hierarchy, and higher-type iteration functionals as a source of the latter; cites Leivant only via Fortune, Leivant, O'Donnell, "The expressiveness of simple and second-order type structures" (JACM 1983), an unrelated paper on type-structure expressiveness. No occurrence of "ramified", "Beckmann", or Leivant's 1999 ramified-recurrence paper; no translation of `RMRec-omega`/`1l(A)` into `T*` or any Godel's T fragment. | No. |
| Danner, "Ramified Recurrence with Dependent Types", TLCA 2001, LNCS 2044, pp. 91-105 | DOI 10.1007/3-540-45413-6_11 | Godel's T with Leivant-style ramified types plus dependent typing; a subsystem characterizes primitive recursive, and ramified finite-type recurrence characterizes functions computable in elementary steps in input size. A distinct dependent-typed system with its own elementary characterization; not a translation of `RMRec-omega`/`1l(A)` into Beckmann-Weiermann `T*`. | No. |
| Szudzik, "On the definability of functionals in Godel's theory T" | arXiv 1011.6353 | Characterizes `T`-definable functionals via `<epsilon_0`-recursive encodings of normal forms. Full `T` and epsilon_0, not the elementary `T*` fragment; no Leivant/`1l(A)` translation. | No. |
| Eguchi, "Predicative Lexicographic Path Orders" | arXiv 1308.0247 | Term-rewriting (PLPO) characterization of the primitive recursive functions. Not elementary, not `T*`, not `RMRec-omega`. | No. |
| Buchholtz, Schipp von Branitz, "Primitive Recursive Dependent Type Theory" | arXiv 2404.01011 | `T_pr`-definable functions are primitive recursive. Primitive-recursion level, not elementary; no bridge to `T*` or Leivant. | No. |

No candidate provides a published translation from `RMRec-omega`, or
from Leivant III's `1l(A)`-represented functions, into `T*` or an
equivalent lambda-free fragment with Lemma-16-style bounds. The
Beckmann-Weiermann `T*` characterization and Leivant III's higher-type
recurrence characterization are two independent routes to the same
function class (the elementary recursive functions); the literature
inspected connects them only at the level of the characterized class,
never by a term-level translation of one calculus into the other.

### Consequence

The reuse of the repository's `LawvereGodelT*` asset for the soundness
direction is not admissible under the transcription-only policy: its
sole precondition, a published bridge, does not hold. Spec s6.3 steps
1-3 (the Leivant III sections 4-5 transcription: `RMRec-omega` to
`RlMR-omega_o` via Proposition 7's composite; the `1l(A)`
representation of Lemmas 8-10 and Proposition 11; the normalization-time
bound of Lemma 12 and Proposition 13) stand as the soundness route. The
`LawvereGodelT*` formalization is not consumed by this workstream.

## G2: LawvereGodelT* audit

Verdict: `no-reuse`.

G2's precondition, G1 verdict `bridge-exists`, does not hold (G1 closed
`no-bridge`; see above). The clause-by-clause audit of the
`LawvereGodelT*` formalization (`GebLean/LawvereGodelTReduces.lean`,
`GebLean/LawvereGodelTLemma16.lean`, `GebLean/LawvereGodelT.lean`)
against Beckmann-Weiermann 2000 Definitions 4 and 7-10 and Lemma 16 is
therefore not performed, per spec s6.3 (failing either precondition, the
Leivant route stands). Gate closed.

## G3: landing choice

Decision rule inputs: G1 verdict `no-bridge` and G2 verdict `no-reuse`
(see the G1 and G2 sections above). Per the plan-fixed rule (spec open
question 2), G2 is not `reuse`, so the "Otherwise (Leivant route)" arm
applies.

Landing: the spec s6.4 normalizer on term codes lands with a verified
elementary clock, by default in `K^sim`. The normalization step
function on term codes is implemented as a K-morphism, clocked with a
K-expressible bound, and transferred across `erKSimEquiv`; precedent is
the executed-once pattern of `erToKFunctor` with
`KSimURMSimulator.simulate`
(`GebLean/Utilities/KSimURMSimulator.lean:544`).

Caveat: the ER landing (bounded recursion on Godel codes, the
`EraComplete` precedent) is chosen instead only if the Phase 6 sub-plan
analysis shows the step function's natural presentation is ER-side
arithmetic rather than a state-transition step; the reason for whichever
landing is chosen is recorded at sub-plan time.

## G4: Otto 1995

Non-blocking gate (spec open question 6): obtain J. R. Otto,
"Complexity Doctrines", and, if obtained, record its overlap with the
multi-sorted packaging that spec s2.5 marks novel, fixing the precedent
line for Phase 1-2 docstrings.

Outcome: `obtained`; overlap `partial`.

### Acquisition

James R. Otto, Jr., "Complexity Doctrines", PhD thesis, Department of
Mathematics and Statistics, McGill University, Montreal, June 13, 1995
(supervisor M. Barr; ISBN 0-612-08143-5). Open access, no paywall or
user assistance required. Located and retrieved 2026-07-02 via web
search to McGill's institutional repository (the legacy eScholarship
record `escholarship.mcgill.ca/concern/theses/8623j0800` redirects to
the current Scholaris item
`mcgill.scholaris.ca/items/23ac9a69-d406-4181-9e12-dda3e7c5c137`), DOI
10.82308/7828. The item serves a 137-page OCR-layered scan produced
from the National Library of Canada microform. ProQuest, WorldCat, and
Internet Archive were not queried; the repository copy superseded them.
No standalone published article by Otto restating the thesis was found.

### Overlap with spec s2.5 novelty claims

Structure of the thesis (from its table of contents and per-chapter
introductions): a doctrine is "the models of a theory of theories";
complexity classes are recovered as images, in the functor categories
`set^2`, `set^V` (`V` the poset `→ ←`), or `set^3`, of categories
initial in a complexity doctrine. Chapter 1 (linear time) works over
the symmetric-monoidal (SM) doctrine and introduces height-graded
sketch theories; Chapter 2 (P space) and Chapter 4 (Kalmar elementary)
work over the finite-product (FP) doctrine extended by V- and
3-comprehensions; Chapter 3 extends the locally-cartesian-closed (LCC)
doctrine. All positive characterizations are first-order. The machine
model throughout is the constant-tape multi-tape Turing machine.

Two cross-cutting differences bear on every claim below. First, Otto's
tiered systems are first-order: he characterizes linear time, linear
space, P time, P space, and Kalmar elementary, descending (Chapter 4
introduction, thesis p. 101; general introduction pp. xi-xii) from
Bellantoni-Cook, Bellantoni, Cobham, Ritchie, and the Leivant-Marion
poly-time/poly-space line ([Lei94] = Leivant, "Ramified recurrence and
computational complexity I: Word algebras and poly-time", Feasible
Mathematics II, Birkhauser 1994; [LM92], [LM95]). Leivant's higher-type
system (Leivant III, APAL 96 (1999) 209-229, DOI
10.1016/S0168-0072(98)00040-2), the object this workstream formalizes,
postdates the 1995 thesis and is neither cited nor treated. Second,
Otto's one higher-type experiment is a negative result: using Church
numerals he shows (Abstract, thesis p. ix; introduction pp. xi-xii;
Chapter 3) that LCC comprehensions "do not provide enough control over
higher order types to characterize complexity classes". Otto therefore
does not anticipate the workstream's central object, a positive
higher-type (`RMRec-omega`) characterization of elementary complexity;
he characterizes the same class (Kalmar elementary) by a first-order
route.

| s2.5 novelty claim | Otto 1995 | Pointer |
| --- | --- | --- |
| Multi-sorted presentation of `RMRec-omega` and its syntactic category (interpretative equality) | Partial precedent for the general device, not the object | Height-graded multi-sorted equational theory: sketch theory with `height : sorts -> N`, unary operators strictly decreasing height, finitely many per sort; models are set-valued sketches; almost-equational specification via sketches and orthogonality; initial models (§1.1.1, thesis pp. 3-4; §1.A "Sketches as Presheaves" p. 34; §1.B "Initial Models" p. 35). Differs: Otto's operators are unary with no constants and the grading is a well-founded height on sorts; for the higher doctrines tiers are separate FP-category copies glued by a comprehension 2-functor, not sorts within one theory; the workstream uses general finite-product arities and a syntactic category (`SynCat`) under interpretative equality, not set-valued sketch models. |
| Theorem 14 (1)-(2) as an object-sort-quantified definability theorem plus a soundness functor into `LawvereERCat` | Methodological precedent; the specific statement not touched | Complexity classes as images of initial doctrine-categories; the Kalmar-elementary case (the class this workstream targets) is a completeness/soundness pair: doctrines `R`, `C`, `C'` (§4.2, thesis pp. 107-112), "Enough Maps" (definability: the image is big enough to include E space, §4.3 p. 113), "Not Too Many Maps" (soundness: the image in `set^3` of an initial category in `C'` is within E space, §4.4 p. 114). Differs: Otto's target is the functor category `set^3` and an E-space multi-tape-Turing-machine model, not a Lawvere theory of ER functions; there is no object-sort-quantified definability statement in Leivant's Theorem-14 form and no soundness functor into a Lawvere theory, only a containment of images. |
| Data-types-a-la-carte factoring of signatures and the W-type realization of syntax | Not touched | Otto's syntax is sketch-theoretic and 2-categorical (sketches; comprehensions as 2-functors; LCC sketches, §3.1.2). No coproduct-of-signature-functors factoring (Swierstra, "Data types a la carte", JFP 18 (2008) 423-436, DOI 10.1017/S0956796808006758) and no initial-algebra/W-type realization of terms. No citation required. |
| Omega-shift functor and analysis of its structure (optional, statement-level) | Structural precedent in the comprehension apparatus | Comprehensions are 2-functors from `end(n)°` on a finite poset (`M_3 = end(3)°`) into the 2-category of FP categories, with tier-raising 1-cell generators `T_i`, tier-lowering `G_i`, and unit/counit 2-cells `G_i -> id -> T_i` (§4.1.1, thesis p. 103; §1.3, §2.1.5), descending from Lawvere's comprehension-as-adjoint ([Law70], "Equality in hyperdoctrines and comprehension schema as an adjoint functor", Applications of Categorical Algebra, AMS 1970) and Pavlovic fibrations. Differs: Otto's shift is a modality/comodality pair internal to one ambient FP/SM/LCC category indexed by a finite poset (closer to a graded (co)monad or a Lawvere comprehension) and is load-bearing for his whole construction; the workstream's Omega-shift is a statement-level functor on the `RMRec-omega` syntactic category, inherited optional from spec revision 1. |

### Docstring precedent for Phases 1-2

The precedent line below is placed in the `## References` section of
the Phase 1 presentation / syntactic-category module and the Phase 2
definability-statement module (the two carrying the s2.5-novel
packaging).

Categorical/doctrinal treatment of tiered (ramified) recurrence via
height-graded multi-sorted equational theories, with complexity classes
as images of initial doctrine-categories: J. R. Otto, "Complexity
Doctrines", PhD thesis, McGill University, 1995, DOI 10.82308/7828
(§1.1 sketch theories; Chapter 4 the Kalmar-elementary doctrines
`R`/`C`/`C'` with the enough-maps / not-too-many-maps pair). The present
development differs in: (i) it formalizes Leivant's higher-type system
`RMRec-omega` (Leivant III, APAL 96 (1999) 209-229, DOI
10.1016/S0168-0072(98)00040-2), which postdates Otto and which Otto does
not treat, his positive characterizations being first-order and his
higher-type LCC-comprehension attempt a negative result; (ii) it uses a
multi-sorted Lawvere theory with a syntactic category under
interpretative equality and a soundness functor into `LawvereERCat`,
rather than set-valued sketch models and images in `set^2`/`set^V`/
`set^3`; (iii) it realizes syntax as W-types of polynomial endofunctors,
a device with no counterpart in Otto.

The data-types-a-la-carte / W-type packaging (s2.5 claim 3) carries no
Otto precedent and is cited to its own source at point of use.
