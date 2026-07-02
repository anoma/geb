# Ramified recurrence as equational Lawvere theories: approaches

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [1. Sources and transcription targets](#1-sources-and-transcription-targets)
  - [1.1 Leivant III (the primary source)](#11-leivant-iii-the-primary-source)
  - [1.2 First-order cell provenance](#12-first-order-cell-provenance)
  - [1.3 A caution on the simultaneous-recursion hierarchy](#13-a-caution-on-the-simultaneous-recursion-hierarchy)
  - [1.4 Transcription versus novel](#14-transcription-versus-novel)
- [2. Research summary](#2-research-summary)
  - [2.1 Categorical and type-theoretic literature](#21-categorical-and-type-theoretic-literature)
  - [2.2 Mechanization prior art](#22-mechanization-prior-art)
  - [2.3 Lean infrastructure verdicts](#23-lean-infrastructure-verdicts)
- [3. Design axes](#3-design-axes)
  - [3.1 Term representation](#31-term-representation)
  - [3.2 Higher-order syntax style](#32-higher-order-syntax-style)
  - [3.3 Objects of the syntactic category](#33-objects-of-the-syntactic-category)
  - [3.4 Equational rule menu](#34-equational-rule-menu)
  - [3.5 Recurrence: operator family versus schema symbols](#35-recurrence-operator-family-versus-schema-symbols)
  - [3.6 Sort universes per system](#36-sort-universes-per-system)
- [4. Layered architecture and interfaces](#4-layered-architecture-and-interfaces)
  - [4.1 Signatures](#41-signatures)
  - [4.2 Term layer (representation-independent API)](#42-term-layer-representation-independent-api)
  - [4.3 Equational theory and syntactic category](#43-equational-theory-and-syntactic-category)
  - [4.4 Ramified structure](#44-ramified-structure)
  - [4.5 Inter-system functors (deliverables for all three cells)](#45-inter-system-functors-deliverables-for-all-three-cells)
  - [4.6 Characterization interfaces (higher-order cell)](#46-characterization-interfaces-higher-order-cell)
- [5. Candidate approaches](#5-candidate-approaches)
  - [5.1 Approach A: sorted-Era native inductives](#51-approach-a-sorted-era-native-inductives)
  - [5.2 Approach B: DTC on the in-repository PolyFix stack](#52-approach-b-dtc-on-the-in-repository-polyfix-stack)
  - [5.3 Approach C: DTC on the vendored slice/presheaf functors](#53-approach-c-dtc-on-the-vendored-slicepresheaf-functors)
  - [5.4 Comparison and migration](#54-comparison-and-migration)
- [6. Theorem targets and phasing](#6-theorem-targets-and-phasing)
- [7. Open questions](#7-open-questions)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Status: brainstorming-phase approaches survey. This document records
the research underlying a planned formalization and lays out candidate
approaches with interfaces and trade-offs. It is not a converged design
specification; a follow-up spec will fix one approach after review and
(optionally) implementation spikes.

Scope fixed during brainstorming:

- The subject is the three ramified-recurrence systems of Table 1 of
  Leivant, "Ramified recurrence and computational complexity III"
  (APAL 96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`;
  henceforth "Leivant III"): first-order monadic (linear space),
  first-order polyadic (polynomial time), higher-order (Kalmar
  elementary).
- Presentation style: multi-sorted Lawvere-theory syntactic categories
  with equational (inductively derivable) equality, as in `Era.lean`'s
  `Derivable`, not the interpretative setoids of `LawvereERQuot.lean`.
- Pluggability along both axes: the free algebra `A` (constructor
  signature) and the type discipline (first-order object types versus
  all ramified types) are parameters of a shared core.
- Data structures follow the data-types-a-la-carte discipline where
  practicable: signatures as polynomial functors, syntax as W-types
  (initial algebras), features as coproduct summands.
- Theorem target in scope: a characterization of the higher-order
  system against the existing `LawvereERCat`, denotationally, without
  machine models. The complexity characterizations of the two
  first-order cells are deferred; those cells receive structures and
  inter-system functors only.

## 1. Sources and transcription targets

### 1.1 Leivant III (the primary source)

Daniel Leivant, "Ramified recurrence and computational complexity III:
Higher type recurrence and elementary complexity", Annals of Pure and
Applied Logic 96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`.

Definitions and results to transcribe, with locations:

| Item | Location | Content |
| --- | --- | --- |
| Free algebra, word algebra, monadic/polyadic | section 2.1 | constructors `c_1 ... c_k`, arity `r_i`; word algebra: all arities at most 1; monadic: one unary constructor; polyadic: several |
| Recurrence over `A`; monotonic, closed, flat variants | section 2.1, eq. (1) | the unramified schema; `case` and destructor functions `dstr_j` by flat recurrence |
| Simple types, `Rec-omega(A)` | section 2.2, eq. (3) | recurrence in all finite types (Godel's T over `A`) |
| Ramified types (r-types) | section 2.3 | types from base `o` by binary `->` and unary `Omega`; object types are `o` and `Omega tau` |
| `RRec-omega(A)`, ramified recurrence for type `tau` | section 2.3, eq. (4) | constructors `c_i` at every object type; recurrence argument of type `Omega tau`, output type `tau` |
| Flat recurrence, `RMRec-omega` (monotonic fragment) | section 2.3, eq. (5) | the fragment the paper works in |
| Coercions `kappa_tau : Omega tau -> theta`, `delta_theta : theta -> o` | section 2.4 (1) | defined by ramified recurrence, extensionally the identity |
| Ramified addition, multiplication | section 2.4 (2) | `+ : o, Omega o -> o`; `x : (Omega o)^2 -> o` |
| First-order = object-type recurrence | section 2.4 (3), p. 216 | "ramified recurrence in first-order types ... is the same as recurrence restricted to object types of the form `Omega^m o`" |
| Exponentiation via second-order recurrence | section 2.4 (3) | `e : Omega(o -> o) -> (o -> o)` by recurrence in `o -> o` |
| Iterated exponentials `2_m` at each object type | section 2.4 (4) | induction on `m`, composing second-order recurrences |
| Simulation of `exp`, `2_m` in arbitrary infinite `A` | section 2.4 (5) | constants `alpha`, `beta` in place of `0`, `s` |
| Size function `sz` | section 2.4 (6) | ramified size measurement |
| Lemma 1: flat recurrence versus destructors and case | section 2.5 | `RRec-omega_o` generates the same functions |
| Simultaneous recurrence; Lemma 2 | section 2.6, eqs. (6), (7) | ramified simultaneous recurrence reduces to plain ramified recurrence |
| Collapse `f-minus`, raising `G-plus-tau`; Lemmas 3, 4 | section 2.7 | erasing ramification; `(f-)+ = f`, `(F+)- = F`; definability of unramified functions |
| Applicative calculi `RlMR-omega`, `RlMR-omega_o` | section 4.1 | applied lambda calculi: constants `c_i`, `R-tau`, `F-tau` (or `dstr`, `case`); beta and eta reductions plus recurrence reduction and flat reduction. Transcription only under option C (section 3.2); options A/B formalize a combinatory analogue, a novel adaptation |
| Proposition 7: equational and applicative agree | section 4.1 | four-way definability equivalence. Same caveat: items (3)-(4) quantify over lambda terms; under options A/B only a combinatory analogue is stateable |
| Theorem 14: elementary characterization | section 6.1 | elementary time = `RMRec-omega` = `RlMR-omega` = `RlMR-omega_o` = represented in `1l(A)`. In-scope transcription is limited to the equivalence of (1)-(2) relative to `LawvereERCat`; items (3)-(5) enter only via the combinatory analogue or option C |
| Multi-sorted generalization sketch | section 6.2 | several free algebras as sorts; `Omega^beta` per base sort |

All of the above are transcription, except as annotated in the rows
for the applicative calculi, Proposition 7, and Theorem 14 (the
lambda-calculus content is transcription only under option C of
section 3.2). The categorical packaging in sections 4
and 5 of this document (syntactic categories, the `Omega`-shift
functor, the collapse functor and its fullness, the
hereditary-majorization model) is novel; see section 1.4.

Register machines over `A` (Leivant III section 3) and the
lambda-representation and normalization-bound route (sections 4.2-5)
are intentionally out of scope: the in-scope characterization route is
denotational, against `LawvereERCat`.

### 1.2 First-order cell provenance

The two first-order cells of Table 1 are established in companion
sources, not in Leivant III itself.

Polyadic (polynomial time):

- Daniel Leivant, "Ramified recurrence and computational complexity I:
  Word recurrence and poly-time", in Feasible Mathematics II,
  Birkhauser, 1995, pp. 320-343, DOI `10.1007/978-1-4612-2566-9_11`.
  Tiered recurrence over free word algebras; two tiers suffice;
  computability in time `O(n^k)` corresponds to `k` nestings of
  ramified simultaneous recurrence. Full text is paywalled; the
  abstract and bibliography were verified via the publisher page.
- Stephen Bellantoni and Stephen Cook, "A new recursion-theoretic
  characterization of the polytime functions", Computational
  Complexity 2(2) (1992) 97-110, DOI `10.1007/BF01201998`. Full text
  verified. The class `B`: normal/safe argument split `f(x...; y...)`;
  initial functions constant, projections, binary successors
  `s_i(;a) = 2a + i`, predecessor, conditional; predicative recursion
  on notation (recursive value in safe position); safe composition.
  Main theorem: polytime = functions of `B` with all-normal inputs
  (Theorems 3.3 and 4.2; Lemma 4.1 gives the "polymax" bound
  `|f(x; y)| <= q_f(|x|) + max_i |y_i|`).
- Correspondence between the two: tier 1 = normal, tier 0 = safe
  (Clote, survey cited below, p. 50).

Monadic (linear space, Grzegorczyk `E^2`):

- The result was never published as a standalone paper. Independent
  sources: Stephen Bellantoni, "Predicative recursion and computational
  complexity", PhD thesis, University of Toronto, Technical Report
  264/92, 1992; W. G. Handley, "Bellantoni and Cook's characterization
  of polynomial time functions", manuscript, 1993 (unpublished; closest
  published descendant: Handley and Wainer, "Complexity of Primitive
  Recursion", in Computational Logic, Springer, 1999,
  DOI `10.1007/978-3-642-58622-4_8`); A. P. Nguyen, "A formal system
  for linear space reasoning", MSc thesis, University of Toronto, 1993.
- Citable published statement: Peter Clote, "Computation models and
  function algebras", in Handbook of Computability Theory,
  North-Holland, 1999, pp. 589-681,
  DOI `10.1016/S0049-237X(99)80033-0`. Definition 3.100 (safe
  recursion over unary numerals) and Theorem 3.101:
  `E^2 = normal cap [0, I, S, Pr, K; scomp, sr]`, attributed to
  Bellantoni's thesis with Handley and Leivant as independent
  discoverers.
- Complexity grounding: R. W. Ritchie, "Classes of predictably
  computable functions", Transactions of the AMS 106 (1963) 139-173.
  Full text verified. Theorem 5 with its corollary (p. 153):
  `E^2 = F'`, where `F'` is the class of functions computable in
  space linear in the binary input length (FLINSPACE). The predicate
  version is Clote's Corollary 3.37.

Out of scope but recorded for completeness: Leivant and Marion,
"Ramified recurrence and computational complexity II: Substitution and
poly-space", CSL '94, LNCS 933, DOI `10.1007/BFb0022277` (parameter
substitution lifts ramified word recurrence from polytime to
poly-space); Meyer and Ritchie, "The complexity of loop programs",
Proc. ACM National Meeting 1967 (loop hierarchy versus Grzegorczyk
from depth 2 upward).

### 1.3 A caution on the simultaneous-recursion hierarchy

The repository's `LawvereKSimDCat` hierarchy realizes Tourlakis's
`K-sim` classes, with the formalized equivalence
`erKSimEquiv : LawvereERCat ~ LawvereKSimDCat 2` (Tourlakis 2018,
Corollary 0.1.0.44: `K-sim_n = E^{n+1}` for `n >= 2`). The
correspondence does not extend to level 1: `K-sim_1` is strictly
contained in `E^2` (level-1 functions are linearly value-bounded, so
multiplication is in `E^2 \ K-sim_1`), and `E^2` sits strictly between
levels 1 and 2. Consequently `LawvereKSimDCat 1` is not a linear-space
reference category, and no existing category in the repository serves
that role. This supports deferring the first-order complexity
characterizations (fixed during brainstorming) and records the gap a
future linear-space workstream must fill.

### 1.4 Transcription versus novel

Transcription (cite at point of use): everything in the tables and
lists above.

Novel (no published precedent found; see sections 2.1-2.2):

- The multi-sorted Lawvere-theory packaging of the three systems as
  syntactic categories with equational equality.
- The `Omega`-shift functor on those categories (by base
  substitution; section 4.4) and the analysis of its structure
  (section 7.1).
- The combinatory analogue of the applicative calculi under options
  A/B (section 3.2).
- The collapse functor to `LawvereERCat` and the statement of the
  elementary characterization as fullness of that functor.
- The bounded-sum and bounded-product realizers in the fullness
  proof (section 4.6): Leivant III contains no such constructions
  (its completeness route is the excluded machine simulation,
  Lemma 6), so these are novel, built in the style of its sections
  2.4(2) and 2.6.
- The hereditary-majorization model as the soundness mechanism.
- The mechanization itself: no formalization of ramified recurrence,
  the Grzegorczyk hierarchy, or a Kalmar-elementary characterization
  was found in any proof assistant (section 2.2).

## 2. Research summary

### 2.1 Categorical and type-theoretic literature

Direct precedents for syntactic categories of complexity classes:

- J. R. Otto, "Complexity doctrines", PhD thesis, McGill University,
  1995 (eScholarship id 8623j0800). Characterizes linear time, linear
  space, PTIME, PSPACE, and Kalmar-elementary as images of categories
  initial in suitable doctrines (2-categorical sketches). The closest
  published relative of the present program; the thesis should be
  obtained before the design spec is finalized.
- A. Burroni, "Recursivite graphique (1ere partie)", Cahiers de
  Topologie et Geometrie Differentielle Categoriques 27(1) (1986)
  49-79 (Numdam `CTGDC_1986__27_1_49_0`). Free cartesian category with
  parametrized NNO, presented inductively; its image is primitive
  recursion.
- M.-F. Thibault, "Pre-recursive categories", Journal of Pure and
  Applied Algebra 24 (1982) 79-93,
  DOI `10.1016/0022-4049(82)90060-3`. Maps `N^k -> N` representable in
  the free cartesian NNO category are exactly the primitive recursive
  functions. Together with Burroni this is the baseline the present
  design refines: replacing "cartesian + NNO" by "cartesian +
  `A`-object + `Omega` discipline" is intended to cut primitive
  recursion down to the three Table-1 classes.
- S. Cook and A. Urquhart, "Functional interpretations of feasibly
  constructive arithmetic", APAL 63 (1993) 103-200,
  DOI `10.1016/0168-0072(93)90044-E`. PV: the canonical equational
  theory of a complexity class (polytime), with inductively derivable
  equations.
- M. Hofmann, "An application of category-theoretic semantics to the
  characterisation of complexity classes using higher-order function
  algebras", Bulletin of Symbolic Logic 3(4) (1997) 469-486.
  Presheaves over the category of polytime functions model `PV-omega`;
  the precedent for treating higher types over a first-order theory by
  presheaf methods.

Modal and linear accounts of the safe/normal (tier) discipline:

- M. Hofmann, "A mixed modal/linear lambda calculus with applications
  to Bellantoni-Cook safe recursion", CSL 1997, LNCS 1414,
  DOI `10.1007/BFb0028020`; "Semantics of linear/modal lambda
  calculus", JFP 9(3) (1999); "Safe recursion with higher types and
  BCK-algebra", APAL 104 (2000) 113-166. SLR: the normal sort as an
  S4-style modality plus linearity; realizability over an affine
  combinatory algebra of polytime algorithms.
- S. Bellantoni, K.-H. Niggl, H. Schwichtenberg, "Higher type
  recursion, ramification and polynomial time", APAL 104 (2000) 17-30;
  U. Dal Lago, S. Martini, L. Roversi, "Higher-order linear ramified
  recurrence", TYPES 2003, LNCS 3085,
  DOI `10.1007/978-3-540-24849-1_12`. Both show that imposing
  linearity on recurrence arguments drops higher-type ramification
  from elementary to polytime. These delimit the present design: the
  formalized theory must admit contraction on `Omega`-typed arguments,
  or it characterizes the wrong class.
- V. Danos and J.-B. Joinet, "Linear logic and elementary time",
  Information and Computation 183(1) (2003) 123-137; O. Laurent, "On
  the categorical semantics of elementary linear logic", Theory and
  Applications of Categories 22(10) (2009). Elementary Seely
  categories: the ELL exponential is a symmetric monoidal endofunctor
  with neither counit (dereliction) nor comultiplication (digging).
  The only fully worked-out categorical axiomatization of an
  elementary-complexity modality found.
- Graded-modality line: Brunel, Gaboardi, Mazza, Zdancewic, "A core
  quantitative coeffect calculus", ESOP 2014,
  DOI `10.1007/978-3-642-54833-8_19`, and successors (Gaboardi et al.
  ICFP 2016; Orchard et al. ICFP 2019): semiring-graded exponential
  comonads. Negative finding: no publication identifies
  Bellantoni-Cook's safe/normal or Leivant's tiers as a graded
  (co)monad. Section 7.1 states the resulting open question.
- Alternative reading: M. Burrell, J. R. B. Cockett, B. F. Redmond,
  "Safe recursion revisited I", Theoretical Computer Science (2014),
  DOI `10.1016/j.tcs.2013.09.034`, and Cockett-Redmond (MFPS 2010,
  Pola FICS 2009): safe/normal as polarities - two categories with
  coercion functors between them - rather than a modality on one
  category.
- Proof-theoretic mirror: G. E. Ostrin and S. S. Wainer, "Elementary
  arithmetic", APAL 133 (2005) 275-292: two-sorted arithmetic
  `EA(I;O)` whose provably recursive functions are Kalmar elementary.
- Extensions and duals (for scope delimitation): N. Danner, "Ramified
  recurrence with dependent types", TLCA 2001, LNCS 2044 (dependent
  typing recovers primitive recursion, i.e. breaks the bound);
  Leivant and Ramyaa on ramified corecurrence (logspace over streams;
  arXiv `1201.4567`); Hainry, Kapron, Marion, Pechoux, "A tier-based
  typed programming language characterizing feasible functionals",
  LICS 2020, DOI `10.1145/3373718.3394768` (tiers at type 2);
  U. Dal Lago and M. Hofmann, "Quantitative models and implicit
  complexity", FSTTCS 2005, arXiv `cs/0506079` (resource monoids: one
  realizability scheme whose instances cover polytime and elementary -
  a candidate uniform semantics if the majorization route fails).

### 2.2 Mechanization prior art

- No formalization of Leivant ramified/tiered recurrence was found in
  any proof assistant, nor of the Grzegorczyk hierarchy or of a
  Kalmar-elementary characterization. Subject to the limits of the
  search, the present workstream would be first of its kind on both
  counts.
- S. Heraud and D. Nowak, "A formalization of polytime functions",
  ITP 2011, LNCS 6898, arXiv `1102.5495`, Coq
  (github `davidnowak/bellantonicook`). Deep embedding of Cobham's `C`
  and Bellantoni-Cook's `B` over bitstrings; certified compilers both
  ways. Design lessons: (i) the two-sorted discipline was extrinsic
  (an arity checker returning a normal/safe arity pair), which
  intrinsically sorted hom-sets would replace; (ii) the soundness
  direction rests on the polymax bound (safe arguments contribute only
  additively via their maximum) - the first-order instance of the
  hereditary-majorization invariant of section 4.6; (iii) the
  completeness direction needs a syntactic "padding fuel" argument
  that appears as a family of morphisms, not an equation.
- Feree, Hym, Mayero, Moyen, Nowak, "Formal proof of polynomial-time
  complexity with quasi-interpretations", CPP 2018, Coq: the main
  non-sorted alternative (per-symbol polynomial annotations).
- Nearest Lean work: P. Kolichala's Lean 3 `polytime_trees`
  (unpublished, unported): machine-free polytime over binary trees as
  an inductively generated class with closure-rule automation.
  Evidence that inductive-class membership proofs automate well in
  Lean.
- Cost datum: fully machine-grounded developments (Cook-Levin in Coq,
  ITP 2021; in Isabelle, AFP 2023) required large compiler and
  automation layers; the machine-free equational route avoids that
  cost, consistent with the in-scope characterization strategy.

### 2.3 Lean infrastructure verdicts

Mathlib (pinned checkout inspected):

- No Lawvere theories, algebraic theories, clones, or operads.
- `ModelTheory` terms are single-sorted (`Language.Functions : N ->
  Type u`); no multi-sorted variant; `Term.subst` exists but without
  identity or composition laws. Usable as a template, not as a base.
- Finite-product infrastructure is adequate:
  `CartesianMonoidalCategory.ofChosenFiniteProducts` supports
  computable chosen products; `Limits.PreservesFiniteProducts` is the
  model-functor ingredient.
- `Nat.Primrec'` (vector arities) is the closest clone-style inductive
  class; polytime Turing-machine content is a stub.

CSLib (pin `v4.29.0-rc6`):

- URMs (Cutland-style) and time/space-bounded single-tape Turing
  machines exist; no complexity classes. Not needed in scope (machine
  models excluded), but recorded: the repository's own
  `Utilities/RegisterMachine.lean` and CSLib's URM differ, and any
  future machine work should reconcile them.
- Locally nameless untyped and simply-typed lambda calculi with
  substitution infrastructure (extrinsic typing, no products). If the
  lambda-calculus presentation (section 3.2, option C) is ever
  pursued, intrinsically-typed de Bruijn templates exist externally
  (the PLFA Lean port `rami3l/plfl`; arXiv `2512.09280`).

In-repository assets:

- `GebLean/Era.lean`: the equational-theory pattern to generalize -
  `Tm B ar n` (no binders, variables as projections), `Eqn`, `Defs`,
  `Derivable` (rules `ax`, `refl`, `euclid`, merged congruence
  `subst`, and the Goodstein uniqueness rule `uniq`), with the clone
  laws `Tm.subst_id` and `Tm.subst_subst` as one-line meta-theorems.
- `GebLean/LawvereER*.lean`, `GebLean/LawvereKSim*.lean`: the
  interpretative Lawvere categories, including `LawvereERCat` (the
  characterization target), `ERMor1` (whose generators drive the
  fullness induction), the polynomial-bound and majorization
  machinery, and `erKSimEquiv`.
- `GebLean/Utilities/SetoidCat.lean`: category of setoids with a
  quotient functor - the pre-quotient hom-setoid layer for syntactic
  categories.
- `GebLean/Utilities/Category.lean`: typeclass-free category-from-data
  assembly (`CategoryData`, `CategoryOfData`), suited to "morphisms =
  terms modulo derivability, composition = substitution".
- Two disjoint polynomial-functor stacks:
  - Vendored `vendor/geb-mathlib/` (`SliceDomPFunctor`,
    `SlicePFunctor`, `PresheafDomPFunctor`, `PresheafPFunctor`):
    Gambino-Hyland slice polynomials and Weber parametric right
    adjoints, choice-hygienic, functor-level only - no W-types, no
    coproducts, no composition. W-types for these are under active
    development in the upstream geb-mathlib repository.
  - In-repository `GebLean/Polynomial.lean`, `PolyAlg.lean`,
    `PolyUMorph.lean`, `PolyAlgUMorph.lean` (`PolyEndo`, `PolyFix`):
    initial algebras with initiality (`polyFixAlg_isInitial`), Lambek,
    catamorphism uniqueness, indexed coproducts (`polyBetweenCoprod`,
    `algCoprodDesc`), and prior art using them for syntax
    (`PLang/TreeCalcPoly.lean`) and for equational quotients of
    W-type carriers (`PLang/IndexedEAT.lean`, `PolyFixRel`). The
    equivalence `polyEndoEquiv : WTypeEndo X ~ PolyEndo X` connects
    representation styles.

## 3. Design axes

Each axis is independent of the others except where noted. Section 5
bundles positions on these axes into named approaches.

### 3.1 Term representation

- Native inductives (Era pattern): a sorted generalization of `Tm`.
  Contexts become sort lists; variables become typed de Bruijn
  indices; operations carry sorted arities. The clone laws remain
  one-line structural inductions. Full equation-compiler and `simp`
  ergonomics.
- W-types of polynomial functors (data types a la carte): the term
  functor is an indexed polynomial endofunctor assembled as a
  coproduct of feature summands; terms are its initial algebra
  (`PolyFix` today; vendored slice/presheaf W-types when available).
  The clone laws are proven once, generically in the signature
  functor. Costs: custom recursors instead of the equation compiler;
  more setup per feature.

A shared abstract interface (section 4.2) keeps this axis reversible:
both representations expose the same `var`/`op`/`subst` API and
meta-theorems, so downstream layers do not depend on the choice.

### 3.2 Higher-order syntax style

- (A) Schematic/equational (Leivant's `RMRec-omega`): function symbols
  introduced by definitional schemas; the signature is generated
  inductively together with its defining equations. No binders; needs
  application operations at arrow sorts.
- (B) Applicative/combinatory (Leivant's `RlMR-omega` without
  lambda): constants `R-tau`, `c_i`, plus a combinator basis replacing
  abstraction; equality includes recurrence reduction and (optionally)
  extensionality. No binders; a first-order multi-sorted theory whose
  sorts include arrow types.
- (C) Typed lambda calculus (`RlMR-omega` proper): intrinsically-typed
  de Bruijn terms; equality includes beta/eta. Requires binder and
  substitution metatheory that `Era.lean` deliberately avoids.

Options A and B collapse into one framework: a multi-sorted theory
whose sort set includes arrow sorts and whose operations include
application. Option C is required only for Leivant III's
lambda-representation and normalization route (sections 4.2-5), which
is out of scope. Recommendation: A/B unified; record C as a possible
later addition with the external templates of section 2.3.

Open sub-question (spike candidate, section 7.3): which combinator
basis suffices for the fullness proof - Leivant's explicit-definition
schema is itself lambda-free, so a small fixed basis (projections,
composition at arrow sorts, currying combinators) is expected to
suffice, but this must be verified on the ramified addition and
exponentiation examples before the design spec is fixed.

### 3.3 Objects of the syntactic category

- Contexts as objects (multi-sorted Lawvere theory): objects are sort
  lists, morphisms are term tuples, composition is substitution.
  Directly generalizes `ERMorN`/`LawvereERCat` (whose objects are
  `N`, i.e. lists over one sort). Finite products are concatenation -
  no product types needed, matching Leivant's product-free r-types.
- Types as objects with internalized products/exponentials (CCC
  style): closer to the models literature, but adds type formers
  Leivant does not have and complicates the transcription claim.

Recommendation: contexts as objects.

### 3.4 Equational rule menu

Base rules (from `Era.lean`, re-sorted): axiom instantiation `ax`,
reflexivity, the Euclidean rule (symmetry and transitivity derived),
and the merged substitution-congruence rule. Optional additions, each
a trade-off:

- Extensionality at arrow sorts (`f x = g x` for fresh `x` implies
  `f = g`): needed if combinatory equality is to coincide with
  lambda-style equality; harmless for the in-scope theorems but
  enlarges the theory. Leivant's applicative calculi include eta.
- A Goodstein-style uniqueness rule (`uniq`) per object sort: gives
  categoricity-style results as in `Era.lean` (`eraInterp_unique`),
  and is the natural equational form of induction. Not required for
  soundness or fullness as stated in section 6; required if a future
  workstream wants provable (not just denotational) equivalences.

Both options should be carried as parameters of the theory
description (axiom-set membership), not baked into `Derivable`, so a
single derivability inductive serves all variants.

### 3.5 Recurrence: operator family versus schema symbols

- Operator family: one constant `R-tau` per admissible `tau` (per
  Leivant's applicative calculi), an operation of the signature with
  two (per-constructor) defining equations.
- Schema symbols: a new function symbol per recurrence instance (per
  `RMRec-omega`), i.e. the signature is inductively generated. This is
  how `ERMor1` works (its `bsum`/`bprod` formers).

With contexts-as-objects and application operations available, the
operator family is smaller and makes the recurrence equations uniform;
schema symbols avoid application at arrow sorts entirely for the
first-order systems. The two-axis pluggability suggests: operator
family in the shared core, with the first-order instantiations able to
restrict `tau` to object sorts (where `R-tau`'s arrow-sorted arguments
degenerate to context extension).

### 3.6 Sort universes per system

The sort set `S` is a parameter carrying designated structure:

- First-order systems: `S = N` (tiers), read as `Omega^m o`. Every
  sort is an object sort; the successor on `N` is the `Omega` shift.
- Higher-order system: `S = RType`, the inductive of r-types
  (`o`, `arrow`, `Omega`); object sorts are `o` and `Omega tau`.

The `A`-constructor summand and the recurrence summand are generic in
`(S, objectSort predicate, Omega : S -> S)`; the application summand
exists only when `S` has arrow structure. This is the concrete form of
"both axes pluggable".

## 4. Layered architecture and interfaces

Interface sketches use Lean-style signatures; names are provisional.
`S` is the sort type; `Ctx S := List S`.

### 4.1 Signatures

```lean
/-- A multi-sorted algebraic signature: operations with sorted
arities. The DTC realization represents the same data as an indexed
polynomial functor; the native realization consumes it directly. -/
structure SortedSig (S : Type) where
  Op : Type
  arity : Op → List S   -- argument sorts
  result : Op → S

/-- Signature sum: data-types-a-la-carte assembly. -/
def SortedSig.sum (F G : SortedSig S) : SortedSig S
```

Feature summands (each generic in the parameters shown):

```lean
/-- Constructors of the free algebra A, one copy per object sort.
Parameters: constructor set B with arities, object-sort predicate. -/
def constructorSig (B : Type) (ar : B → Nat)
    (isObj : S → Prop) [DecidablePred isObj] : SortedSig S

/-- Application at arrow sorts (higher-order systems only). -/
def appSig (arrow : S → S → Option S) : SortedSig S

/-- Ramified recursors R_tau. Parameters: Omega shift, admissible
motive predicate (all sorts, or object sorts only). -/
def recSig (B : Type) (ar : B → Nat) (Omega : S → S)
    (admissible : S → Prop) : SortedSig S

/-- Destructors and case (the RRec_o variants; Lemma 1 target). -/
def dstrCaseSig (B : Type) (ar : B → Nat)
    (isObj : S → Prop) : SortedSig S
```

### 4.2 Term layer (representation-independent API)

Both realizations (native inductive; `PolyFix` of the signature's
polynomial functor) must provide:

```lean
Tm    : SortedSig S → Ctx S → S → Type
var   : (i : Fin Γ.length) → Tm Σ Γ (Γ.get i)
op    : (o : Σ.Op) → (args : ∀ i, Tm Σ Γ (Σ.arity o).get i) →
        Tm Σ Γ (Σ.result o)
subst : Tm Σ Γ s → (∀ i, Tm Σ Δ (Γ.get i)) → Tm Σ Δ s
-- meta-theorems (the clone laws / category laws):
subst_id    : t.subst var = t
subst_subst : (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ)
-- evaluation into a model (sorted carriers with operations):
eval : (M : SortedModel Σ) → Tm Σ Γ s → M.Env Γ → M.carrier s
```

Because the syntax has no binders (section 3.2), `subst` is plain
structural recursion in either realization, and the meta-theorems stay
one-line inductions (native) or single catamorphism arguments (DTC).

### 4.3 Equational theory and syntactic category

```lean
structure Eqn (Σ : SortedSig S) (Γ : Ctx S) (s : S) where
  lhs rhs : Tm Σ Γ s

/-- Axiom families. Era's `Defs` is a List; schema-generated theories
(recurrence equations for every instance) need a predicate. -/
def AxiomSet (Σ : SortedSig S) :=
  ∀ (Γ : Ctx S) (s : S), Eqn Σ Γ s → Prop

inductive Derivable (E : AxiomSet Σ) :
    ∀ {Γ s}, Eqn Σ Γ s → Prop
  | ax     : E Γ s e → Derivable E e
  | refl   : Derivable E ⟨t, t⟩
  | euclid : Derivable E ⟨a, b⟩ → Derivable E ⟨a, c⟩ →
             Derivable E ⟨b, c⟩
  | subst  : Derivable E ⟨F, G⟩ → (∀ i, Derivable E ⟨σ i, σ' i⟩) →
             Derivable E ⟨F.subst σ, G.subst σ'⟩
  -- optional, parameterized via E rather than new rules where
  -- possible: ext (arrow sorts), uniq (object sorts)
```

```lean
/-- The syntactic category of a theory: objects are contexts,
morphisms are substitutions modulo derivable equality. -/
def SynCat (Σ : SortedSig S) (E : AxiomSet Σ) : Type := Ctx S
-- Hom Γ Δ := (∀ i, Tm Σ Γ (Δ.get i)) quotiented by pointwise
-- Derivable; composition = subst; laws = subst_id, subst_subst.
instance : Category (SynCat Σ E)
instance : CartesianMonoidalCategory (SynCat Σ E)  -- concatenation
```

Assembly plan: hom-setoids first (`SetoidCat` shapes), quotient last,
so pre-quotient statements (categoricity, normal forms) remain
stateable - the pattern that served `Era.lean`. The construction also
subsumes, in principle, the boilerplate duplicated by
`LawvereERQuot.lean` and `LawvereKSimQuot.lean` (with interpretative
setoids in place of `Derivable`); retrofit is out of scope but the
interface should not preclude it (the quotient relation is a
parameter).

### 4.4 Ramified structure

```lean
/-- r-types (higher-order sort universe). Transcription:
Leivant III section 2.3. -/
inductive RType | o | arrow (σ τ : RType) | omega (τ : RType)

/-- A presentation bundles: a sort type S with designated structure
(object-sort predicate, Omega shift, optional arrow structure), a
signature (sum of feature summands), and an axiom set. -/
structure Presentation

/-- The three systems as theory presentations. -/
def monadicFO  : Presentation      -- S := N, A := (unary succ, zero)
def polyadicFO (B ar) : Presentation  -- S := N, A polyadic word alg
def higherOrder (B ar) : Presentation -- S := RType, full summand sum

/-- Omega shift. Postcomposition with Omega is not a signature
morphism on the higher-order presentation: application at
(arrow σ τ, σ) -> τ has no image, since Omega (arrow σ τ) is an
object sort, not arrow (Omega σ) (Omega τ) (compare Leivant III
p. 214 on iterates). The candidate that does respect the signature
is base substitution, tau -> tau[o := Omega o]: it commutes with
arrow, Omega, the constructor copies, application, and the R-tau
family. On first-order sorts it is the tier successor m -> m + 1,
where it is a signature endomorphism outright. Functoriality on the
higher-order syntactic category (in particular closure of the axiom
set under the shift) is unverified; see open question 7.1. -/
def omegaShift : SynCat Σ E ⥤ SynCat Σ E   -- by base substitution
/-- Coercion at the Omega-sort: Leivant III's auxiliary kappa-hat
(section 2.4(1)); the paper reserves kappa_tau for the composite
Omega tau -> theta. This is a morphism at the sort Omega tau, not
at omegaShift.obj [tau]: the two agree exactly on the first-order
sorts (tau[o := Omega o] = Omega tau iff tau = Omega^m o), so
kappaHat supplies a copoint for omegaShift on the first-order
systems only. On the higher-order system a copoint component at an
arrow sort would need a raising term, and no term of type
o -> Omega o exists, so no copoint of omegaShift is expected there;
see open question 7.1. -/
def kappaHat (τ) : (([RType.omega τ] : SynCat Σ E) ⟶ [τ])
```

### 4.5 Inter-system functors (deliverables for all three cells)

- Theory-inclusion functors: first-order into higher-order (sort map
  `m ↦ Omega^m o`, operation-preserving).
- Algebra-map functoriality: a morphism of constructor signatures
  (e.g. monadic into polyadic) induces a functor of syntactic
  categories.
- `omegaShift` as an endofunctor: unconditional deliverable for the
  first-order systems (where the shift is a signature endomorphism);
  for the higher-order system contingent on the base-substitution
  functoriality of section 4.4 (open question 7.1).
- `kappaHat` at every r-type; the copoint `omegaShift ⟹ Id` it
  induces on the first-order systems (section 4.4). No copoint is
  expected on the higher-order system.
- Lemma 1 and Lemma 2 as equivalences/reductions between presentation
  variants (flat versus destructor-case; simultaneous versus plain).

### 4.6 Characterization interfaces (higher-order cell)

Soundness carrier (hereditary majorization over ER; novel, but with
the mechanism of `LawvereKSimMajorization` one type level up, and the
polymax bound of Heraud-Nowak as its first-order instance):

```lean
/-- Interpretation of each r-type as: a ground denotation together
with an ER-morphism majorant/realizer, hereditarily in tau. -/
def MajCarrier : RType → Type
-- MajCarrier o := codes with an ERMor1 bound;
-- MajCarrier (arrow σ τ) := maps preserving majorized-ness;
-- MajCarrier (omega τ) := MajCarrier τ (levels are proof-relevant
--   only through admissibility of R).
/-- The majorization model: a SortedModel of the higher-order
presentation with carriers MajCarrier; the recurrence operations
must be shown to preserve majorization. -/
def majModel : SortedModel (higherOrder B ar).sig
```

Statements:

```lean
/-- SynCatFO: the full subcategory of the higher-order syntactic
category on contexts of object sorts Omega^m o (the first-order
collapse objects). -/
def SynCatFO (P : Presentation) : Type

/-- Collapse/soundness: the denotation of every morphism between
first-order-collapse objects is ER-definable. Packaged as a functor
once soundness is proven. -/
def collapseFunctor : SynCatFO (higherOrder B ar) ⥤ LawvereERCat

/-- Fullness = the elementary characterization (in-scope theorem).
Proof by structural induction on ERMor1: zero, succ, proj immediate;
sub by monotonic recurrence with a dstr-defined predecessor step;
comp by level alignment - via omegaShift where available, otherwise
via object-type-indexed families of realizers, the paper's own
device ("for each object type theta there is a copy of exp",
section 2.4(3)); bsum, bprod by novel constructions in the style of
sections 2.4(2) and 2.6 (the step needs the loop index, so ramified
simultaneous recurrence, Lemma 2, or an equivalent device, plus tier
alignment for the asymmetric ramified addition). Leivant III's own
completeness route is the excluded machine simulation (Lemma 6), so
no construction here is a transcription. Machine-free. -/
theorem collapseFunctor_full : collapseFunctor.Full
```

The two statements together are the denotational form of Leivant III
Theorem 14 relative to `LawvereERCat` as the reference definition of
"elementary". They deliberately do not assert an equivalence of
categories: the equational category has finer hom-sets (soundness of
`Derivable` for the standard interpretation gives well-definedness of
`collapseFunctor`; its faithfulness is neither expected nor needed).

## 5. Candidate approaches

### 5.1 Approach A: sorted-Era native inductives

Realize sections 4.1-4.4 with hand-written inductives, generalizing
`Era.lean` exactly as its own design anticipated (variables as
projections, no binders, meta-level clone laws). Signature summands
are plain data (`SortedSig.sum` is list-like); DTC appears only as
this data-level composition.

- For: proven pattern in this repository; best proof ergonomics
  (equation compiler, `simp`, structural induction); shortest path to
  the in-scope theorem; no dependency on polynomial-functor W-types.
- Against: composability is shallow - induction principles and
  helper lemmas are per-inductive, so feature reuse across the three
  systems is by parameter, not by construction; no contribution to the
  geb-mathlib polynomial-functor program.

### 5.2 Approach B: DTC on the in-repository PolyFix stack

Terms as `PolyFix` of an indexed polynomial endofunctor assembled by
`polyBetweenCoprod` from feature summands; equational layer via the
`IndexedEAT` pattern (`PolyFixRel`); catamorphisms (`polyFixFold`) for
`subst` and `eval`, with the clone laws proven once against
initiality.

- For: genuine construction-level composability (the three systems
  are literally coproducts of shared summands); the generic clone
  laws are proven once; direct continuity with existing in-repository
  W-type infrastructure and its `PLang` prior art; exercises and
  stresses the machinery the geb-mathlib program is developing.
- Against: W-type ergonomics (custom recursors, no equation compiler,
  `Sum`-shaped positions in every case split - visible in
  `TreeCalcPoly.lean`); the sorted-context indexing
  (`X = Ctx S × S` or contexts as parameters) needs a design of its
  own; slower to the in-scope theorem.

### 5.3 Approach C: DTC on the vendored slice/presheaf functors

As B, but with signatures as `SlicePFunctor` (or `PresheafPFunctor`
for the PRA generality) and terms as their W-types, once fixpoints and
coproducts for these exist (under active development upstream in
geb-mathlib; absent from the vendored snapshot).

- For: the most direct correspondence with the cited constructions
  (Gambino-Hyland polynomials, Weber PRAs) and the strongest
  alignment with the geb-mathlib upstreaming program; presheaf
  polynomials are the applicable representation if the syntax is
  ever indexed over a nontrivial category (e.g. sorts with coercion
  morphisms rather than a discrete sort set).
- Against: not startable today - requires W-types, coproducts, and
  composition for the vendored functors first; otherwise inherits B's
  ergonomics costs.

### 5.4 Comparison and migration

| Dimension | A (native) | B (PolyFix) | C (vendored) |
| --- | --- | --- | --- |
| Startable today | yes | yes | no (needs W-types, coproducts) |
| Time to in-scope theorem | shortest | medium | longest |
| Construction-level composability | no (parameter-level) | yes | yes |
| Clone laws | per-system, trivial | once, generic | once, generic |
| Proof ergonomics | best | costs (custom recursors) | costs (same) |
| geb-mathlib program alignment | none | indirect | direct |
| Dependency risk | none | low (in-repo, stable) | high (WIP upstream) |

Migration paths: the representation-independent API of section 4.2
mediates all of them. A-to-B (or -C) migration replaces the
realization of one
interface; B-to-C is a change of polynomial-functor representation,
mediated by a `polyEndoEquiv`-style equivalence. The equational and
categorical layers (sections 4.3-4.6) are unaffected in either case.

Recommendation: fix the section-4.2 interface first; run two small
spikes on the monadic first-order system (the smallest instantiation),
one native and one `PolyFix`, through the syntactic-category
construction; decide the default realization on that evidence, with C
recorded as the convergence target as upstream W-type support arrives.
If a single default must be chosen without spikes, B, on the grounds
that the composability requirement is explicit in the project
direction and the `PLang` prior art bounds the ergonomic risk.

## 6. Theorem targets and phasing

Deliverables, in dependency order (phase boundaries to be fixed by the
implementation plan, not here):

1. Core: sorted signature, term, and equational layers (sections
   4.1-4.3), with the clone laws and the generic syntactic-category
   construction, plus finite products.
2. Monadic first-order system: presentation, syntactic category,
   `omegaShift`, `kappaHat`, ramified addition/multiplication examples
   (transcriptions validating the encoding).
3. Polyadic first-order system: same, over a polyadic word algebra;
   algebra-map and theory-inclusion functors; Lemma 1 and Lemma 2
   analogues.
4. Higher-order system: `RType` sorts, application summand, `R-tau`
   family; the exponentiation and iterated-exponential examples
   (Leivant III section 2.4 (3)-(4)) as well-typedness evidence.
5. Fullness data: ER-basis definability (zero, succ, proj, sub, comp,
   bsum, bprod as ramified terms with denotation proofs) - stateable
   before the collapse functor exists, as an existence-of-realizer
   family. The bsum/bprod realizers are novel constructions (section
   4.6) and carry the main risk of this deliverable; section 7.3
   schedules them for a spike.
6. Soundness: the hereditary-majorization model, `collapseFunctor`,
   and `collapseFunctor_full` (assembling 5 into fullness).

Deferred (recorded, not planned): first-order complexity
characterizations (linear-space reference definition does not yet
exist in the repository - section 1.3 - and polytime would need a
Cobham/Bellantoni-Cook-style reference theory); poly-space via
parameter substitution (Leivant-Marion II); corecursive duals;
lambda-calculus presentation and normalization bounds; retrofit of
`LawvereERQuot`/`LawvereKSimQuot` onto the generic construction;
relation between the higher-order theory and `Era.lean`'s single-sorted
E3 basis.

## 7. Open questions

1. Existence and structure of the `Omega` shift on the higher-order
   system. Existence first: the base-substitution definition of
   section 4.4 must be shown functorial (signature endomorphism plus
   axiom-set closure under the shift); for the first-order systems
   existence is unproblematic. Structure second: Leivant's system has
   derivable coercions `kappaHat_tau : Omega tau -> tau` (the paper's
   auxiliary; its `kappa_tau` targets the output object type) -
   unlike elementary linear logic, whose exponential has no
   dereliction - yet characterizes the same class. Candidate
   readings: copointed monoidal endofunctor (supported by `kappaHat`
   on the first-order systems, where the shift's image sorts are
   Omega-sorts; not expected on the higher-order system, whose
   arrow sorts admit no raising term - section 4.4); graded
   (co)monad with grades = tiers (no publication makes this
   identification - a precise statement either way is publishable
   novel content); Cockett-Redmond-style polarity (two categories
   with coercion functors). The formalization should state and
   prove whichever structure each syntactic category actually
   carries; naturality of `kappaHat` on the first-order systems is
   the first test.
2. Rule menu: include extensionality and/or `uniq` in the default
   presentations, or keep both as axiom-set extensions? (Section 3.4;
   affects how close combinatory equality is to lambda equality, and
   whether categoricity results are available.)
3. Combinator basis sufficiency for the fullness constructions
   (section 3.2), and the bsum/bprod realizers themselves (novel;
   section 4.6): both to be settled by a spike, on ramified addition
   and exponentiation for the former and on a bounded sum via
   simultaneous recurrence for the latter. The fullness proof
   depends on both.
4. Sorted-context indexing for the DTC realizations: contexts as
   index components versus contexts as parameters (affects the shape
   of the signature functors and of `PolyFixRel` usage).
5. Whether `Presentation` should carry the object-sort predicate and
   `Omega` as structure on `S` (section 3.6) or as a typeclass on the
   sort type; interaction with the theory-inclusion functors.
6. Obtain Otto's thesis (section 2.1) and check for overlap before
   the design spec claims novelty for the initial-category
   formulations.

## References

Anchor and companion papers:

- D. Leivant, "Ramified recurrence and computational complexity III:
  Higher type recurrence and elementary complexity", APAL 96 (1999)
  209-229. DOI `10.1016/S0168-0072(98)00040-2`.
- D. Leivant, "Ramified recurrence and computational complexity I:
  Word recurrence and poly-time", Feasible Mathematics II, Birkhauser,
  1995, 320-343. DOI `10.1007/978-1-4612-2566-9_11`.
- D. Leivant, J.-Y. Marion, "Ramified recurrence and computational
  complexity II: Substitution and poly-space", CSL '94, LNCS 933,
  1995, 486-500. DOI `10.1007/BFb0022277`.
- S. Bellantoni, S. Cook, "A new recursion-theoretic characterization
  of the polytime functions", Computational Complexity 2(2) (1992)
  97-110. DOI `10.1007/BF01201998`.
- P. Clote, "Computation models and function algebras", Handbook of
  Computability Theory, North-Holland, 1999, 589-681.
  DOI `10.1016/S0049-237X(99)80033-0`.
- R. W. Ritchie, "Classes of predictably computable functions",
  Trans. AMS 106 (1963) 139-173.
- W. G. Handley, S. S. Wainer, "Complexity of primitive recursion",
  Computational Logic, Springer, 1999, 273-300.
  DOI `10.1007/978-3-642-58622-4_8`.

Categorical and type-theoretic:

- J. R. Otto, "Complexity doctrines", PhD thesis, McGill, 1995.
- A. Burroni, "Recursivite graphique (1ere partie)", CTGDC 27(1)
  (1986) 49-79.
- M.-F. Thibault, "Pre-recursive categories", JPAA 24 (1982) 79-93.
  DOI `10.1016/0022-4049(82)90060-3`.
- S. Cook, A. Urquhart, "Functional interpretations of feasibly
  constructive arithmetic", APAL 63 (1993) 103-200.
  DOI `10.1016/0168-0072(93)90044-E`.
- M. Hofmann, BSL 3(4) (1997) 469-486; CSL 1997 (LNCS 1414,
  DOI `10.1007/BFb0028020`); JFP 9(3) (1999); APAL 104 (2000) 113-166.
- S. Bellantoni, K.-H. Niggl, H. Schwichtenberg, APAL 104 (2000)
  17-30.
- U. Dal Lago, S. Martini, L. Roversi, TYPES 2003, LNCS 3085.
  DOI `10.1007/978-3-540-24849-1_12`.
- V. Danos, J.-B. Joinet, Information and Computation 183(1) (2003)
  123-137.
- O. Laurent, "On the categorical semantics of elementary linear
  logic", TAC 22(10) (2009).
- A. Brunel, M. Gaboardi, D. Mazza, S. Zdancewic, ESOP 2014.
  DOI `10.1007/978-3-642-54833-8_19`.
- M. Burrell, J. R. B. Cockett, B. F. Redmond, TCS (2014).
  DOI `10.1016/j.tcs.2013.09.034`.
- G. E. Ostrin, S. S. Wainer, "Elementary arithmetic", APAL 133 (2005)
  275-292.
- N. Danner, TLCA 2001, LNCS 2044. DOI `10.1007/3-540-45413-6_11`.
- E. Hainry, B. Kapron, J.-Y. Marion, R. Pechoux, LICS 2020.
  DOI `10.1145/3373718.3394768`.
- U. Dal Lago, M. Hofmann, FSTTCS 2005. arXiv `cs/0506079`.
- P. Hofstra, P. Scott, "Aspects of categorical recursion theory",
  arXiv `2001.05778`.

Mechanization:

- S. Heraud, D. Nowak, "A formalization of polytime functions",
  ITP 2011, LNCS 6898. arXiv `1102.5495`.
- H. Feree, S. Hym, M. Mayero, J.-Y. Moyen, D. Nowak, "Formal proof of
  polynomial-time complexity with quasi-interpretations", CPP 2018.
  DOI `10.1145/3167097`.

Hierarchy background:

- G. Tourlakis, "Primitive recursive complexity topics", lecture
  notes, 2018. The verified quotations are recorded in
  `docs/research/2026-04-30-ksim-polynomial-bound-references.md`.
- A. R. Meyer, D. M. Ritchie, "The complexity of loop programs",
  Proc. ACM National Meeting 1967, 465-469.
