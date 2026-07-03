# Ramified recurrence gate decisions (Phase 0)

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Plan-fixed decisions (restated)](#plan-fixed-decisions-restated)
- [G1: Beckmann-Weiermann bridge](#g1-beckmann-weiermann-bridge)
  - [Framing (spec s1.2)](#framing-spec-s12)
  - [Searched space](#searched-space)
  - [Consequence](#consequence)

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
| Ostrin, Wainer, "Proof theoretic complexity" (in Proof and System-Reliability, NATO Sci. Ser. II vol. 62, 2002; preprint, Univ. Bern) | Univ. Bern LTG preprint 2002 (home.inf.unibe.ch/ltg/publications/2002/ow02.pdf) | `EA(I;O)` predicative-arithmetic route: provably recursive functions are the elementary functions; slow-growing hierarchy analysis yielding epsilon_0 pointwise. Independent proof-theoretic characterization, arithmetic-side; no translation of Leivant's calculus into `T*`. | No. |
| Cagman, Ostrin, Wainer, "Inductive definitions over a predicative arithmetic", APAL 136 (2005) 175-188 | ScienceDirect S0168007205000588 | Extends the `EA(I;O)` predicative-arithmetic framework by inductive definitions; recaptures stronger systems in the slow-growing setting. Arithmetic-side; no `RMRec-omega`-to-`T*` translation. (The spec brief's "Ostrin-Wainer APAL 133 (2005)" is this predicative-arithmetic line; the volume located in search is 136.) | No. |
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
