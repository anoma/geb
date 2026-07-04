# Ramified recurrence as Lawvere theories: approaches

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [1. Scope and policy](#1-scope-and-policy)
  - [1.1 Decisions fixed during brainstorming and user review](#11-decisions-fixed-during-brainstorming-and-user-review)
  - [1.2 Transcription-only policy](#12-transcription-only-policy)
- [2. Sources and transcription targets](#2-sources-and-transcription-targets)
  - [2.1 Leivant III (the primary source)](#21-leivant-iii-the-primary-source)
    - [Orientation: recursion versus recurrence](#orientation-recursion-versus-recurrence)
  - [2.2 First-order cell provenance](#22-first-order-cell-provenance)
  - [2.3 Further sources (added 2026-07-02)](#23-further-sources-added-2026-07-02)
  - [2.4 A caution on the simultaneous-recursion hierarchy](#24-a-caution-on-the-simultaneous-recursion-hierarchy)
  - [2.5 Transcription versus novel](#25-transcription-versus-novel)
- [3. Research summary](#3-research-summary)
  - [3.1 Categorical and type-theoretic literature](#31-categorical-and-type-theoretic-literature)
  - [3.2 Mechanization prior art](#32-mechanization-prior-art)
  - [3.3 Lean and in-repository infrastructure](#33-lean-and-in-repository-infrastructure)
- [4. The system: `RMRec-omega` as a multi-sorted Lawvere theory](#4-the-system-rmrec-omega-as-a-multi-sorted-lawvere-theory)
  - [4.1 Presentation choices](#41-presentation-choices)
  - [4.2 Interfaces](#42-interfaces)
  - [4.3 Inter-system functors](#43-inter-system-functors)
- [5. Reference target and algebra choice for the equivalence](#5-reference-target-and-algebra-choice-for-the-equivalence)
  - [5.1 `LawvereERCat` versus `LawvereKSimDCat 2`](#51-lawvereercat-versus-lawvereksimdcat-2)
  - [5.2 Which algebra hosts the proof](#52-which-algebra-hosts-the-proof)
- [6. The theorem and its proof-route map](#6-the-theorem-and-its-proof-route-map)
  - [6.1 Statement shape](#61-statement-shape)
  - [6.2 Definability: the machine route (all transcription)](#62-definability-the-machine-route-all-transcription)
  - [6.3 Soundness: the normalization route](#63-soundness-the-normalization-route)
  - [6.4 Landing elementary computation in the reference category](#64-landing-elementary-computation-in-the-reference-category)
- [7. Candidate approaches for the syntax layer](#7-candidate-approaches-for-the-syntax-layer)
- [8. Deliverables and phasing](#8-deliverables-and-phasing)
- [9. Deferred and future work](#9-deferred-and-future-work)
- [10. Open questions](#10-open-questions)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Status: brainstorming-phase approaches survey, revision 3. Revision 1
went through adversarial review rounds 1-3 and user review; revision 2
(reviews 4-5) incorporated that review's structural decisions;
revision 3 incorporates a further user decision - interpretative
equality now, the equational presentation deferred (section 1.1) -
and receives its own adversarial-review cycle. The `review-N` files
sit alongside this document. This document records the research
underlying a planned formalization and lays out the design with
interfaces and trade-offs. It is not yet a converged design
specification.

## 1. Scope and policy

### 1.1 Decisions fixed during brainstorming and user review

- The subject is the ramified-recurrence programme of Table 1 of
  Leivant, "Ramified recurrence and computational complexity III"
  (APAL 96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`;
  henceforth "Leivant III"): first-order monadic (linear space),
  first-order polyadic (polynomial time), higher-order types
  (Kalmar elementary).
- Presentation style: multi-sorted Lawvere-theory syntactic
  categories whose morphisms are terms modulo extensional equality of
  their standard interpretation in Lean - the interpretative-setoid
  style of `LawvereERQuot.lean` and `LawvereKSimQuot.lean`. The
  equational (inductively derivable) presentation in the style of
  `Era.lean`'s `Derivable` is deferred to a future workstream
  (section 9): the reference `LawvereERCat` is itself interpretative,
  an equational reworking of it would gate the in-scope proof, and
  the standard interpretation built here is a prerequisite of the
  future workstream's soundness proof in any case.
- A single form of the calculus is formalized: `RMRec-omega`
  (Leivant III sections 2.3-2.7), under the interpretative equality
  above. The applicative
  calculi `RlMR-omega` and `RlMR-omega_o` and their equivalence with
  `RMRec-omega` (Proposition 7) are deferred as goals; both calculi
  return as proof apparatus for the soundness direction, whose
  literature route runs through them (section 6.3).
- Pluggability along both axes via data types a la carte: the free
  algebra `A` and the type discipline are parameters; data structures
  are defined through the repository's dependent polynomial functors,
  with syntax as W-types where practicable. Canonical algebra
  instances: unary naturals (signature functor `1 + X`, monadic),
  binary words (`1 + 2X`, polyadic), unlabeled binary trees
  (`1 + X^2`, tree algebra). One system is built - the higher-order
  presentation, generic in the signature functor - and instantiated
  at all three; the first-order systems are realized, where needed,
  as restricted sub-theories of that presentation rather than as
  separate implementations (section 4.1). See section 5.2 for which
  algebra hosts the one in-scope proof.
- One theorem is in scope: the equivalence of the higher-order-typed
  system's first-order collapse with the repository's existing
  elementary-recursive reference class - `LawvereERCat`, or
  equivalently `LawvereKSimDCat 2` through `erKSimEquiv`
  (`GebLean/LawvereERKSim/Equivalence.lean`). Section 5.1 compares
  the two landing points. The complexity characterizations of the
  two first-order cells (linear space, polynomial time) are
  deferred; those cells receive sub-theory definitions and
  inclusion functors only.
- Transcription-only policy (section 1.2): machine models are used
  wherever the literature's proofs use them.

### 1.2 Transcription-only policy

This workstream transcribes known mathematics. Novelty is permitted
only at the level of packaging: the multi-sorted presentation, the
syntactic-category construction, the statement of
known results against the repository's categories, and naming. It is
not permitted at the level of proof routes: where the literature
proves a result by a machine simulation, the formalization
transcribes the machine simulation rather than substituting an
unpublished argument.

Consequences, superseding revision 1:

- Machine models are in scope. Each instruction of the repository's
  zero-test URM (`GebLean/Utilities/ZeroTestURM.lean`: `assign`,
  `inc`, `dec`, `jumpZ`, `stop`) is a single command or a
  constant-length command block of Leivant III's register machines
  over the unary algebra (section 3.1 of the paper): `inc`/`dec`
  are in-place constructor assignment and destructor, `assign i c`
  is a zero assignment followed by `c` increments, `jumpZ` is the
  two-way branch, `stop` is the end-state convention, and PC values
  are states. URM computations are therefore Leivant-machine
  computations with constant time overhead, which is the direction
  the Lemma 6 transcription uses. (Leivant's cross-register
  assignment and destructor commands have no single-instruction URM
  counterpart; that direction is not needed.)
- Revision 1's machine-free proposals for the two directions of the
  main theorem are withdrawn: the bounded-sum/bounded-product
  realizers (completeness) and the hereditary-majorization model
  (soundness) were novel proof routes. Definability now follows the
  literature's machine route (section 6.2); soundness follows the
  literature's normalization route (section 6.3).

## 2. Sources and transcription targets

### 2.1 Leivant III (the primary source)

Daniel Leivant, "Ramified recurrence and computational complexity III:
Higher type recurrence and elementary complexity", Annals of Pure and
Applied Logic 96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`.

#### Orientation: recursion versus recurrence

"Recurrence" is Leivant's name for the elimination schema of a free
algebra: definition of a function by one clause per constructor,
with recursive calls on the immediate subterms. Over the unary
naturals it is primitive recursion; over a general free algebra it
is the same schema with that algebra's constructor clauses. This
orientation fixes the schema concretely before the survey table.
The Lean code below is illustrative and verified to compile. The
signature, free-algebra, and recurrence code corresponds to
implementation inductives realized as W-types of polynomial
functors (mathlib's `PFunctor` or the repository's slice polynomial
and presheaf parametric-right-adjoint functors), per sections 4 and
7; the tier illustration further below is notation only (sections
2.3 and 4.1).

Recursion as already formalized: the repository's K^sim theory
carries simultaneous primitive recursion as the term former
`KMor1.simrec` (`GebLean/LawvereKSim.lean:50`):

```lean
  /-- Simultaneous primitive recursion at output index
  `i`, with system size `k+1`, base-case family `h`,
  and step-function family `g`.  Produces a morphism
  of arity `a+1` (one slot for the recursion variable
  followed by `a` slots for the parameter list). -/
  | simrec {a k : ℕ}
      (i : Fin (k+1))
      (h : Fin (k+1) → KMor1 a)
      (g : Fin (k+1) → KMor1 (a + 1 + (k + 1))) :
      KMor1 (a + 1)
```

Its semantics (`KMor1.simrecVec`,
`GebLean/LawvereKSimInterp.lean:66`) is the classical system of
equations, for `j = 1, ..., k + 1`:

```text
f_j (0,     x_1 ... x_a) = h_j (x_1 ... x_a)
f_j (n + 1, x_1 ... x_a) = g_j (n, x_1 ... x_a,
                                f_1 (n, x_1 ... x_a),
                                ...,
                                f_{k+1} (n, x_1 ... x_a))
```

Ordinary (non-simultaneous) primitive recursion is the case
`k = 0`.

Unramified recurrence (Leivant III section 2.1, eq. (1)) is the
same schema over an arbitrary free algebra. A signature lists
constructors with arities; the free algebra is the inductive type
they generate; recurrence supplies one clause per constructor, in
which the step sees the parameters, the subterms of the input being
destructed, and the results of the recursive calls on those
subterms. The paper's names for these pieces differ from the ones
used here; the glossary after the equations fixes the
correspondence exactly.

```lean
/-- A constructor signature: constructor names with arities. -/
structure Sig where
  B : Type
  ar : B → Nat

/-- The free algebra over a signature (illustrative; the
implementation represents this as a polynomial-functor W-type). -/
inductive FreeAlg (S : Sig) : Type
  | mk (b : S.B) (subterms : Fin (S.ar b) → FreeAlg S) : FreeAlg S

/-- Unramified recurrence over `S` (Leivant III eq. (1)): one step
function per constructor `b`, seeing the parameters `x : P`, the
subterms of the recurrence argument, and the recursive results
(the paper's critical arguments). -/
def FreeAlg.recurse {S : Sig} {P C : Type}
    (g : (b : S.B) → P → (Fin (S.ar b) → FreeAlg S) →
      (Fin (S.ar b) → C) → C) :
    P → FreeAlg S → C
  | x, .mk b subterms =>
      g b x subterms fun i => FreeAlg.recurse g x (subterms i)
```

Equationally, for each constructor `c_i` of arity `r_i`, exactly as
the paper displays eq. (1):

```text
f (x_vec, c_i (a_1 ... a_{r_i})) =
  g_ci (x_vec, a_vec, phi_1, ..., phi_{r_i})
where phi_j = f (x_vec, a_j)
```

Terminology glossary. The correspondence between the paper's
naming (its section 2.1, the sentence after eq. (1)) and the code
above, fixed piece by piece. The first five rows are eq. (1)'s
pieces; the last two define the types of the ramified schema
(eq. (4), the paper's section 2.3), which the second row mentions
and the ramified paragraph below uses:

| Symbol in eq. (1) | The paper's name | Name here | Role |
| --- | --- | --- | --- |
| `x_vec` | recurrence parameters | parameters (`x : P` in `recurse`) | Carried unchanged through every recursive call; they parameterize the single recursive definition and are never modified by it. |
| `c_i (a_1 ... a_{r_i})` | recurrence argument ("the argument of `f` exhibited last in (1)") | recurrence argument | The whole constructor term the recursion consumes - the input being destructed, the last argument of `f`. In the ramified schema (eq. (4)) it is the argument of sort `Omega tau` (last two rows). In `recurse` it is the matched value `.mk b subterms`. |
| `a_1 ... a_{r_i}` | no dedicated name (written `a_vec`; the components of the recurrence argument) | subterms (`subterms` in `recurse`) | The immediate subterms of the recurrence argument. Note the paper's "recurrence argument" is the whole term `c_i (a_vec)`, not these components; the paper's terminology sentence assigns them no name of their own. |
| `phi_1 ... phi_{r_i}`, where `phi_j = f (x_vec, a_j)` | critical arguments ("the last `r_i` arguments of `g_ci`") | recursive results (`results` in `natRecurse`) | The results of the recursive calls on the subterms, passed up to the current step - the values flowing back from one level deeper in the recursion. |
| `g_ci` | recurrence functions | step functions | One per constructor `c_i`: the body of the definition at that constructor. |
| `tau` (also `sigma`; eq. (4)) | r-type ("ramified functional type") | r-type / sort | A variable ranging over the ramified types (the paper's section 2.3): the grammar generated from the single base type `o` by the binary arrow `sigma -> tau` and the unary constructor `Omega`. `o` is a syntactic symbol whose standard interpretation is the carrier of the plugged-in free algebra - unary naturals for `1 + X`, binary words for `1 + 2X`, unlabeled binary trees for `1 + X^2` (section 4.2's `standardModel`). The object types are `o` and every `Omega tau` - here `tau` itself ranges over all r-types, functional ones included, so `Omega (o -> o)` is an object type; all r-types other than the object types are functional. In this document's higher-order system the sorts are exactly the r-types (`RType`, section 4.1); the first-order tiers `m : N` are the tower `Omega^m o`. |
| `Omega tau` (eq. (4)) | Omega-type | Omega-sort | `Omega` is a unary type constructor with no semantic content of its own: `Omega tau` is the type of base-algebra elements permitted to serve as the recurrence argument of a recurrence whose critical arguments (recursive results) carry type `tau` (paraphrasing the paper's p. 214; in eq. (4) the output is then also `tau`). Flat recurrence, having no critical arguments, takes its recurrence argument at `o` instead. Semantically every object type - `o` and each `Omega tau` alike - denotes a copy of the algebra's carrier (the paper's section 2.7), so an element of `Omega (o -> o)` is an element of the base algebra - a number over `1 + X` or `1 + 2X`, an unlabeled binary tree over `1 + X^2` - never a function; what `Omega` adds is purely the typing license to drive recurrence at `tau`. Over the unary naturals, for example, iterating an `o -> o` function requires the iteration count at `Omega (o -> o)` (the paper's p. 214 iterate example and section 2.4(3) exponentiation). |

Over the unary naturals this is primitive recursion again - the two
constructor clauses are the base and step equations:

```lean
/-- The monadic word algebra of signature functor `1 + X`: one
0-ary constructor (`false`, zero) and one unary constructor
(`true`, successor). -/
def natSig : Sig := ⟨Bool, fun b => cond b 1 0⟩

def natZero : FreeAlg natSig := .mk false Fin.elim0

def natSucc (n : FreeAlg natSig) : FreeAlg natSig :=
  .mk true fun _ => n

/-- Recurrence over `natSig` is primitive recursion: the two
constructor clauses of eq. (1) are the base and step equations
(shown without parameters: `P := Unit`). -/
def natRecurse (base : Nat) (step : Nat → Nat) :
    FreeAlg natSig → Nat :=
  FreeAlg.recurse (P := Unit)
    (fun b => match b with
      | false => fun _ _ _ => base
      | true => fun _ _ results => step (results ⟨0, by decide⟩))
    ()
```

So recurrence relates to the recursion of K^sim as follows: it
generalizes the algebra (any signature in place of the unary
naturals) and drops simultaneity (Leivant handles the simultaneous
variant separately; his Lemma 2, section 2.6, reduces it to the
plain form). The paper names fragments by which arguments the step
may see (section 2.1): monotonic (the step does not see the
subterms `a_vec`), closed (no parameters `x_vec`), flat (no
critical arguments, i.e. no recursive results - it yields case
analysis and the destructors, p. 212). The system formalized here
is the monotonic fragment, `RMRec-omega`.

Ramified recurrence (Leivant III section 2.3, eq. (4)) is the same
schema with a sorting layer and nothing else: every sort denotes a
copy of the same algebra, the equations are unchanged, and the only
change is a typing constraint on the recurrence argument's sort.
Leivant's schema fixes it at exactly one sort above the output
(`Omega tau` against `tau`, eq. (4)); the strictly-above form
`i < j` in the illustration below is the composite of that schema
with the downward coercions of section 2.4(1), which lower any
higher sort to `Omega tau`. First-order illustration over the unary
naturals, with tiers as natural numbers:

```lean
/-- First-order ramified (tiered) recurrence, illustrated over the
unary naturals with tier annotations: `TieredFn j i` names a unary
function whose input carries tier `j` and output tier `i`. The
`prec` former demands `i < j`. Monotonic, without parameters or
simultaneity, for brevity. -/
inductive TieredFn : Nat → Nat → Type
  | ident {i} : TieredFn i i
  | zeroConst {j i} : TieredFn j i
  | succ {i} : TieredFn i i
  | comp {k j i} : TieredFn j i → TieredFn k j → TieredFn k i
  | prec {j i} (base : Nat) (step : TieredFn i i) : i < j →
      TieredFn j i

/-- Tier erasure: every tiered function denotes a plain function on
the carrier; tiers restrict definability, not semantics. -/
def TieredFn.interp {j i : Nat} : TieredFn j i → Nat → Nat
  | .ident => fun n => n
  | .zeroConst => fun _ => 0
  | .succ => fun n => n + 1
  | .comp f g => fun n => f.interp (g.interp n)
  | .prec base step _ =>
      fun n => Nat.rec base (fun _ v => step.interp v) n
```

In the higher-order system the tiers `i < j` become r-types: the
recurrence argument carries `Omega tau` and the output `tau`
(eq. (4): `f : sigma_vec, Omega tau -> tau`, with each step
`g_ci : sigma_vec, (Omega tau)^{r_i}, tau^{r_i} -> tau`), so the
"one sort above" relation is generated by the type constructor
`Omega` rather than by the successor on tier numbers.

Definitions and results to transcribe, with locations and scope
annotations:

| Item | Location | Content and scope |
| --- | --- | --- |
| Free algebra; word algebra (monadic/polyadic); tree algebra | section 2.1 | constructors `c_1 ... c_k`, arity `r_i`; the paper's standing convention: the algebra is infinite, so it has a constructor of arity 0 and one of positive arity. Word algebra: all arities at most 1 (subdivided: monadic = one unary constructor, polyadic = several); tree algebra: at least one constructor of arity at least 2. The monadic/polyadic distinction subdivides word algebras only |
| Recurrence over `A`; monotonic, closed, flat variants | section 2.1, eq. (1) | the unramified schema; `case` and destructor functions `dstr_j` by flat recurrence |
| Ramified types (r-types) | section 2.3 | types from base `o` by binary `->` and unary `Omega`; object types are `o` and `Omega tau` |
| `RRec-omega(A)`, ramified recurrence for type `tau` | section 2.3, eq. (4) | constructors `c_i` at every object type; recurrence argument of type `Omega tau`, output type `tau` |
| Flat recurrence, `RMRec-omega` (monotonic fragment) | section 2.3, eq. (5) | the system formalized here |
| Coercions `kappa_tau : Omega tau -> theta`, auxiliary `kappa-hat_tau : Omega tau -> tau`, `delta_theta : theta -> o` | section 2.4 (1) | defined by ramified recurrence, extensionally the identity |
| Ramified addition, multiplication | section 2.4 (2) | `+ : o, Omega o -> o`; `x : (Omega o)^2 -> o` |
| First-order = object-type recurrence | section 2.4 (3), p. 216 | "ramified recurrence in first-order types ... is the same as recurrence restricted to object types of the form `Omega^m o`" |
| Exponentiation via second-order recurrence | section 2.4 (3) | `e : Omega(o -> o) -> (o -> o)` by recurrence in `o -> o` |
| Iterated exponentials `2_m` at each object type | section 2.4 (4) | induction on `m`, composing second-order recurrences; used by Lemma 6 |
| Simulation of `exp`, `2_m` in arbitrary infinite `A` | section 2.4 (5) | constants `alpha`, `beta` in place of `0`, `s`; needed only for non-numeric `A` |
| Size function `sz` | section 2.4 (6) | ramified size measurement; used by Lemma 6 |
| Lemma 1: flat recurrence versus destructors and case | section 2.5 | `RRec-omega_o` generates the same functions; connects the machine lemma's target to `RMRec-omega` |
| Simultaneous recurrence; Lemma 2 | section 2.6, eqs. (6), (7) | ramified simultaneous recurrence reduces to plain ramified recurrence; used by Lemma 6 |
| Collapse `f-minus`, raising `G-plus-tau`; Lemmas 3, 4 | section 2.7 | erasing ramification; `(f-)+ = f`, `(F+)- = F`; the collapse defines what the main theorem characterizes |
| Register machines over `A`; Lemma 5 | section 3.1 | states, registers holding `A`-elements, commands: constructor assignment, branch on main constructor, destructor; reducibilities to Turing machines |
| Lemma 6: elementary-time machines are ramified-definable | section 3.2 | the completeness direction; simultaneous-recurrence simulation of machine steps, clocked by `2_q(sz)`; in scope as the definability route (section 6.2) |
| Applicative calculi `RlMR-omega`, `RlMR-omega_o` | section 4.1 | applied lambda calculi: constants `c_i`, `R-tau`, `F-tau` (or `dstr`, `case`); beta and eta reductions plus recurrence and flat reduction. In scope as soundness apparatus (section 6.3): both calculi, since the paper's route from (1) to (4) passes through `RlMR-omega` |
| Proposition 7: equational and applicative agree | section 4.1 | four-way definability equivalence, items (1) `RMRec-omega`, (2) `RMRec-omega_o`, (3) `RlMR-omega`, (4) `RlMR-omega_o`. In scope as soundness apparatus: the composite (1) to (3) (eq. (9), p. 223), (3) to (4) (stated "similar" to Lemma 1; its transcription reconstructs the indicated argument). The remaining directions are deferred; Lemma 1's (1)-(2) equivalence is in scope on the definability side |
| Lambda-representation in `1l(A)`; Lemmas 8-10 and Proposition 11 | sections 4.2-4.3 | Berarducci-Boehm-style representation of `A` in the simply typed lambda calculus with `dstr`/`case`, with the term translation `E` to `E-bar`; soundness apparatus |
| Lemma 12, Proposition 13: normalization bound | section 5 | terms of height `h`, redex rank `q` normalize in time `O((2_{q+1}(h))^2)`; hence represented functions are elementary-time computable; soundness apparatus |
| Theorem 14: elementary characterization | section 6.1 | the in-scope theorem is the equivalence of items (1) and (2), stated against the repository's reference class; items (3)-(5) are deferred with the applicative calculi |
| Multi-sorted generalization sketch | section 6.2 | several free algebras as sorts; recorded for future work |

### 2.2 First-order cell provenance

The two first-order cells of Table 1 are established in companion
sources, not in Leivant III itself. No complexity proof for these
cells is in scope; the provenance is recorded for the sub-theory
definitions' docstrings and for future workstreams.

Polyadic (polynomial time):

- Daniel Leivant, "Ramified recurrence and computational complexity I:
  Word recurrence and poly-time", in Feasible Mathematics II,
  Birkhauser, 1995, pp. 320-343, DOI `10.1007/978-1-4612-2566-9_11`.
  Tiered recurrence over free word algebras; two tiers suffice;
  computability in time `O(n^k)` corresponds to `k` nestings of
  ramified simultaneous recurrence. Full text paywalled; abstract and
  bibliography verified via the publisher page.
- Stephen Bellantoni and Stephen Cook, "A new recursion-theoretic
  characterization of the polytime functions", Computational
  Complexity 2(2) (1992) 97-110, DOI `10.1007/BF01201998`. Full text
  verified. Safe/normal split; predicative recursion on notation;
  safe composition; polytime = all-normal-input functions of `B`
  (Theorems 3.3, 4.2; Lemma 4.1 gives the polymax bound).
- Tier dictionary: tier 1 = normal, tier 0 = safe (Clote, survey
  below, p. 50).
- Cost-model caution for tree algebras (from the 2026-07-02 sources,
  section 2.3): first-order tiered recursion over an algebra with a
  constructor of arity above one can produce outputs of exponential
  term size (full binary tree from a binary word), so polytime
  soundness at first order over tree algebras holds only under
  DAG/graph representation of values. The polyadic cell is stated
  over binary words with string sizes, where this does not
  arise.

Monadic (linear space, Grzegorczyk `E^2`):

- Never published standalone. Sources: Stephen Bellantoni,
  "Predicative recursion and computational complexity", PhD thesis,
  University of Toronto, TR 264/92, 1992; W. G. Handley, manuscript,
  1993 (unpublished; published descendant: Handley and Wainer,
  "Complexity of Primitive Recursion", Computational Logic, Springer,
  1999, DOI `10.1007/978-3-642-58622-4_8`); A. P. Nguyen, MSc thesis,
  University of Toronto, 1993.
- Citable statements: Peter Clote, "Computation models and function
  algebras", Handbook of Computability Theory, North-Holland, 1999,
  pp. 589-681, DOI `10.1016/S0049-237X(99)80033-0` (Definition 3.100,
  Theorem 3.101). Also Danner and Royer 2012 (section 2.3):
  "the RS1-[nat]-computable (nat x ... x nat -> nat)-functions =
  E_2, the second Grzegorczyk class (aka, the linear-space
  computable functions)" (p. 7 there, following Bellantoni's thesis
  and Leivant I).
- Complexity grounding: R. W. Ritchie, "Classes of predictably
  computable functions", Transactions of the AMS 106 (1963) 139-173.
  Full text verified: Theorem 5 with corollary (p. 153), `E^2 = F'`
  (FLINSPACE, space linear in binary input length).

Out of scope, recorded: Leivant and Marion, "Ramified recurrence II:
Substitution and poly-space", CSL '94, LNCS 933,
DOI `10.1007/BFb0022277`; Meyer and Ritchie, "The complexity of loop
programs", Proc. ACM National Meeting 1967.

### 2.3 Further sources (added 2026-07-02)

Three papers were added to the reference set after revision 1. All
three are future work, not formalization targets of this workstream;
they also serve as cross-checks of the revision-1 reading of the
landscape. A correction they force: revision 1 attributed
arXiv `1201.4567` to Ramyaa and Leivant; it is by Danner and Royer.
The Ramyaa-Leivant corecurrence papers are that paper's references
("Feasible functions over co-inductive data", WoLLIC 2010, LNCS 6188;
"Ramified corecurrence and logspace", MFPS XXVII, ENTCS 276 (2011)
247-261).

Dal Lago, Martini, Zorzi, "General Ramified Recurrence is Sound for
Polynomial Time", DICE 2010, EPTCS 23, pp. 47-62,
DOI `10.4204/EPTCS.23.4` (full text read):

- First-order, soundness only, arbitrary free algebras, tiers as
  bare natural-number vectors `(i_1, ..., i_n) -> i` with recursion
  requiring the recurrence tier strictly above the result tier. The
  proof compiles tiering derivations to term-graph rewriting and
  bounds steps and DAG sizes by tier-indexed counting - no lambda
  calculus, no normalization argument. It documents that Leivant's
  POPL '93 polytime claim for arbitrary algebras holds only for word
  algebras under string representation (the full-binary-tree
  counterexample, p. 48), the origin of the cost-model caution in
  section 2.2. It does not cite Leivant III and says nothing about
  higher-order ramification or the elementary class.
- Adoption: its tier-vector presentation (no type grammar, per-
  constructor recursion cases with subterms at the high tier and
  recursive results at the low tier, separate untiered conditional)
  is adopted as notation only - in prose, docstrings, and the
  orientation's illustration - not as an implementation
  (section 4.1); a standalone tier-sorted instantiation is deferred
  to the first-order characterization workstreams (section 9).
- Future work: formalizing its soundness theorem would require the
  term-graph cost model first.

Danner and Royer, "Ramified Structural Recursion and Corecursion",
arXiv `1201.4567v2`, 2012 (extended abstract; full text read):

- An unramified base calculus `S-minus` for structural recursion
  and its two-sorted (normal/safe) ramification `RS1-minus` (the
  2022 paper renames the base `S1-minus`), over inductive data
  `data tau = mu t. sigma` with an explicit polynomial signature
  functor `F_tau`, constructor, destructor, and recursor
  `fold_tau : (F sigma -> sigma) -> tau -> sigma` satisfying the
  initial-algebra equation; worked examples are exactly `1 + X`
  (nat) and `1 + X^2` (tree). Cost model: cons-cell DAGs with
  sharing and memoized folds. The ramification has a definable
  coercion `up_tau` (in this document's terms, the analogue of
  Leivant's `kappa-hat`) and a `lower` typing rule adapting
  Bellantoni-Cook's raising. Characterizations: FP over data and
  codata under the DAG model; "the RS1-[nat]-computable
  (nat x ... x nat -> nat)-functions = E_2, the second Grzegorczyk
  class (aka, the linear-space computable functions)" (p. 7);
  stream restrictions match the Ramyaa-Leivant logspace results.
  Not equational: semantics is operational plus set-theoretic;
  there is no inductively derivable program equality.
- Adoption: the data-system layer (datatype = initial algebra of a
  named polynomial signature functor with `fold`) is adopted as the
  presentation of the algebra axis (section 4.1); it coincides with
  the repository's W-type plan. The two-sorted ramification and the
  DAG cost model are not adopted (the Omega tower comes from
  Leivant III; equational equality belongs to the deferred
  workstream, section 9).
- Future work: ramified corecursion over the final coalgebras
  (M-types) of the same signature functors, with observed-size
  bounds; logspace stream characterizations.

Danner and Royer, "General Ramified Recurrence and Polynomial-time
Completeness (Preliminary Draft)", arXiv `2205.10348v1`, 2022 (full
text read):

- The completeness counterpart over general free algebras: with
  DAG-shared tree data, `RS1-minus` is sound (Theorem 10) but
  apparently cannot combine safe results of sibling recursive calls
  (tree height; incompleteness of `RS1-minus` is conjectured,
  pp. 15, 28); adding
  compressed-size functions `cs_delta` (computed by
  Downey-Sethi-Tarjan DAG compression) restores completeness
  (`RS1.1-minus`, Theorems 22, 23, 25), via serialization into
  hereditarily sequential representations and a CEK-machine
  interpreter of the base calculus, iterated a bounded number of
  steps (in this document's terms, a clocked self-interpreter; a
  machine simulation, with Jones's influence credited there,
  p. 4). Scholium 35 notes the same
  architecture scales to Kalmar-elementary `E^3` and higher
  Grzegorczyk levels by swapping the closed class of size-bound
  terms. It cites Leivant I and Dal Lago-Martini-Zorzi, not
  Leivant III.
- Cross-check value: independently confirms that completeness
  arguments in this family are machine simulations (CEK there,
  register machines in Leivant III), and that additive bounds (the
  2012 paper's "poly-heap" style) compose better than polymax
  bounds under pairing (Scholium 32) - relevant if bound
  bookkeeping ever needs choosing.
- Future work: completeness over general algebras with sharing;
  strong inductive types containing function spaces; sharing-based
  versus sharing-free cost models (Pola comparison).

Cross-check summary: none of the three papers engages Leivant III's
Omega tower, its equational calculus, or the elementary class by
higher-order ramification; all three confirm the two-ingredient
reading of first-order ramification (recursion on notation plus
tiers) and the coercion phenomena (definable upward/downward
casts). The Leivant III reading of revision 1 stands unmodified;
the tree-algebra cost caution and the presentation adoptions above
are the changes they force.

### 2.4 A caution on the simultaneous-recursion hierarchy

`erKSimEquiv : LawvereERCat ~ LawvereKSimDCat 2` realizes Tourlakis
2018, Corollary 0.1.0.44 (`K-sim_n = E^{n+1}` for `n >= 2`). The
correspondence does not extend to level 1: `K-sim_1` is strictly
contained in `E^2` (level-1 functions are linearly value-bounded), and
`E^2` sits strictly between levels 1 and 2. `LawvereKSimDCat 1` is
therefore not a linear-space reference category, and no category in
the repository currently is; this supports deferring the first-order
complexity characterizations.

### 2.5 Transcription versus novel

Transcription (cite at point of use): everything in section 2.1's
table within its scope annotations; the machine lemmas against the
zero-test URM (presentation adaptation only, section 1.2).

Novel packaging (permitted; no novel proof routes):

- The multi-sorted presentation of `RMRec-omega` and its syntactic
  category (interpretative equality; the equational variant is the
  deferred workstream of section 9).
- The statement of Theorem 14 (1)-(2) as an object-sort-quantified
  definability theorem plus a soundness functor into `LawvereERCat`;
  a categorical packaging of the pair is an open question
  (section 6.1).
- The data-types-a-la-carte factoring of signatures and the W-type
  realization of syntax.
- Optional, statement-level only: the Omega-shift functor and the
  analysis of its structure (section 9), inherited from revision 1.

Withdrawn from revision 1 (novel proof routes): hereditary-
majorization soundness; bounded-sum/product completeness
realizers.

## 3. Research summary

### 3.1 Categorical and type-theoretic literature

Unchanged from revision 1 except the attribution correction noted in
section 2.3. Anchors: J. R. Otto, "Complexity doctrines", PhD thesis,
McGill, 1995 (initial categories for linear time, linear space,
PTIME, PSPACE, Kalmar-elementary; closest precedent; to be obtained
before the design spec finalizes); A. Burroni, CTGDC 27(1) (1986)
49-79, and M.-F. Thibault, JPAA 24 (1982) 79-93,
DOI `10.1016/0022-4049(82)90060-3` (free cartesian NNO category =
primitive recursion, the baseline this design refines); Cook and
Urquhart's PV, APAL 63 (1993) 103-200,
DOI `10.1016/0168-0072(93)90044-E`, with Hofmann, BSL 3(4) (1997)
469-486 (presheaves over the polytime theory); Hofmann's SLR line
(CSL 1997, LNCS 1414, DOI `10.1007/BFb0028020`; JFP 9(3) 1999; APAL
104 (2000) 113-166); Bellantoni-Niggl-Schwichtenberg, APAL 104
(2000) 17-30, and Dal Lago-Martini-Roversi, TYPES 2003, LNCS 3085,
DOI `10.1007/978-3-540-24849-1_12` (linearity on recurrence
arguments drops higher-type ramification from elementary to
polytime - the theory formalized here must admit contraction on
Omega-typed arguments); Danos-Joinet, Information and Computation
183(1) (2003) 123-137, with Laurent, TAC 22(10) (2009) (elementary
Seely categories: monoidal endofunctor without counit or
comultiplication); the graded-modality line (Brunel-Gaboardi-Mazza-
Zdancewic, ESOP 2014, DOI `10.1007/978-3-642-54833-8_19`, and
successors) with the negative finding that no publication identifies
tiers as a graded (co)monad; Cockett-Redmond polarity (TCS 2014,
DOI `10.1016/j.tcs.2013.09.034`); Ostrin-Wainer, APAL 133 (2005)
275-292 (two-sorted arithmetic with elementary provably recursive
functions); Danner, TLCA 2001, LNCS 2044 (dependent typing recovers
primitive recursion); Hainry-Kapron-Marion-Pechoux, LICS 2020,
DOI `10.1145/3373718.3394768` (tiers at type 2); Dal Lago-Hofmann
resource monoids, FSTTCS 2005, arXiv `cs/0506079`.

Additional anchor surfaced in revision 2: Beckmann and Weiermann,
"Characterizing the elementary recursive functions by a fragment of
Godel's T", Archive for Mathematical Logic 39 (2000) 475-491 - an
elementary characterization via a combinatory (lambda-free) fragment
`T*`, partially formalized in this repository (section 3.3); its
role as candidate soundness apparatus is assessed in section 6.3.

### 3.2 Mechanization prior art

Unchanged from revision 1: no formalization of Leivant
ramified/tiered recurrence, of the Grzegorczyk hierarchy, or of a
Kalmar-elementary characterization was found in any proof assistant;
the genuine ICC mechanizations are Heraud-Nowak (ITP 2011, Coq,
arXiv `1102.5495`; Bellantoni-Cook and Cobham with certified
compilers both ways, extrinsic arity checking) and the
quasi-interpretation line (CPP 2018, Coq). Nearest Lean work:
Kolichala's Lean 3 polytime-over-binary-trees (unported). Machine-
grounded developments (Cook-Levin in Coq and Isabelle) show the cost
of fully explicit machine work at scale; the machine content in
scope here (section 6.2) is narrow by comparison and mostly already
formalized in-repository.

### 3.3 Lean and in-repository infrastructure

Mathlib and CSLib verdicts unchanged from revision 1: no Lawvere
theories, algebraic theories, or multi-sorted term infrastructure in
mathlib (`ModelTheory` is single-sorted; `Term.subst` lacks identity
and composition laws); CSLib provides Cutland-style URMs and
locally nameless lambda calculi but no complexity classes.
`CartesianMonoidalCategory.ofChosenFiniteProducts` supports
computable chosen products. For intrinsically-typed de Bruijn
lambda terms (needed by the soundness apparatus, section 6.3) the
templates identified in revision 1 remain the starting points: the
PLFA Lean port (`rami3l/plfl`, DeBruijn and Substitution chapters)
and the modular metatheory framework of arXiv `2512.09280`
(availability unverified).

In-repository assets, extended in revision 2 by the machine- and
normalization-facing items:

- `GebLean/Era.lean`: the equational-theory pattern for the deferred
  equational workstream (section 9)
  (`Tm`/`Eqn`/`Defs`/`Derivable`; clone laws `Tm.subst_id`,
  `Tm.subst_subst` as one-line meta-theorems). Its term-layer shape
  informs the present design regardless of the equality choice.
- `GebLean/LawvereER*.lean`: `ERMor1`, `LawvereERCat` (the reference
  class), tower bounds (`ERMor1.exists_lt_tower`, constructive
  `towerBound`).
- `GebLean/LawvereERKSim/*`: `compileER : ERMor1 a -> URMProgram a`
  (`Compiler.lean:1590`) with correctness (`Top.lean`:
  `compileER_pre_stop_correct`, `compileER_runFor`) and the joint
  runtime/value bound `boundExprKParams_dominates` /
  `boundExprK_dominates` (`RuntimeBound.lean`): the URM runtime of
  every ER morphism is dominated by `tower mu_e (max v + offset_e)`,
  realized as a level-<= 2 K-morphism. Together: every ER function is
  elementary-time URM-computable, formalized.
- `GebLean/Utilities/ZeroTestURM.lean` (`URMProgram`, `URMInstr`,
  `URMState.runFor`) and `GebLean/Utilities/KSimURMSimulator.lean`
  (`simulate : URMProgram a -> KMor1 (a+1)`, `simulate_interp`,
  `simulate_level <= 2`): bounded URM simulation inside K^sim,
  realizing Tourlakis section 0.1.0.37.
- `GebLean/LawvereGodelT*.lean`: a partial formalization of
  Beckmann-Weiermann `T*` - `GodelTType S` (base types `nat` and
  opt-in `tree`, arrows, the level measure of their Definition 7),
  `GodelTTerm S n sigma` (typed combinatory terms: abstraction via
  `K` and `S_comb`, no lambda), the reduction relation of their
  Definition 4 with interpretation invariance
  (`LawvereGodelTReduces.lean`), and the structural tower bound of
  their Lemma 16 (`LawvereGodelTLemma16.lean`, following pp.
  480-484, with the majorization apparatus `dominates_app`,
  `majorizes_redIter_*`). The area doc
  (`docs/areas/lawvere-er-ksim.md`) records it as an adjacent
  development; no connection to `LawvereERCat` is proven yet. Its
  test coverage is thin (a smoke test,
  `GebLeanTests/LawvereGodelTTerm.lean`: numeral guards, one redex
  reduction, an application of interpretation invariance) and
  nothing downstream consumes it, so its fidelity to the source is
  not established; it is treated as such until the audit of
  section 6.3.
- Tree-coding assets for the tree algebra: `GebLean/LawvereNatBT*`
  and `GebLean/LawvereTreeERArith.lean`, including
  `erToNatBTV2Functor` (equivalence of `LawvereERCat` with the
  `m = 0` subcategory of a binary-tree-naturals theory) - the
  beginnings of the tree-to-numbers coding layer (section 5.2).
- `GebLean/Utilities/SetoidCat.lean` and `Utilities/Category.lean`:
  hom-setoid categories with a quotient functor, and typeclass-free
  category-from-data assembly - the syntactic-category construction
  seeds.
- Two polynomial-functor stacks: vendored
  `vendor/geb-mathlib/` (`SlicePFunctor`, `PresheafPFunctor`;
  functor-level only - no W-types, coproducts, or composition;
  W-types under active development upstream) and in-repository
  `GebLean/Polynomial.lean`/`PolyAlg.lean`/`PolyUMorph.lean`/
  `PolyAlgUMorph.lean`
  (`PolyFix` initial algebras with initiality, Lambek, catamorphism
  uniqueness; indexed coproducts `polyBetweenCoprod` with
  `algCoprodDesc`; syntax-as-W-type prior art in
  `PLang/TreeCalcPoly.lean` and equational quotients in
  `PLang/IndexedEAT.lean`; `polyEndoEquiv : WTypeEndo X ~ PolyEndo
  X`).

## 4. The system: `RMRec-omega` as a multi-sorted Lawvere theory

### 4.1 Presentation choices

Form of the calculus. `RMRec-omega`'s syntax follows Leivant's own
schematic style: function identifiers introduced by schemas
(explicit definition; ramified monotonic recurrence). There are no
lambda binders and no combinator basis in the system itself; terms
are applicative (variables, constructor constants, defined
identifiers, application), and identifiers form an inductively
generated signature, as `ERMor1` and `KMor1` already do for their
theories. Program equality is extensional equality of the standard
interpretation: each identifier's interpretation is defined by
structural recursion in Lean (as `ERMor1.interp` is), and two
morphisms are equal when their interpretations agree on every
environment. The inductively derivable equational form of the same
theory (Leivant's defining equations as a `Derivable`-style axiom
set) is the deferred workstream of section 9. The typed lambda
calculus appears only inside the soundness apparatus
(section 6.3).

Algebra axis (adopted from Danner-Royer 2012, coinciding with the
repository's W-type plan): a free algebra is presented by its
polynomial signature functor; the datatype is its initial algebra;
the constructor summand of the theory's signature is derived from
the same functor, one copy per object sort. Canonical instances:

| Instance | Signature functor | Datatype |
| --- | --- | --- |
| Monadic word algebra | `1 + X` | unary naturals |
| Polyadic word algebra | `1 + 2 X` | binary words |
| Tree algebra | `1 + X^2` | unlabeled binary trees |

One presentation is implemented: the higher-order system, with
sorts Leivant III's r-types (`RType`), generic in the signature
functor and instantiated at the three canonical algebras. The
first-order systems are not separate implementations. Where a
first-order system is needed as an object of study, it is a
restricted sub-theory of the r-type instantiation: the same term
and category layers, with identifier formation restricted to
first-order arities over the tower sorts `Omega^m o` and recurrence
at object sorts of the form `Omega^m o`. The full subcategory of
the higher-order syntactic category on tower-sort contexts is not
the first-order system: fullness admits every higher-order-formed
morphism with tower-sorted endpoints (a recurrence at a tower sort
takes parameters of arbitrary r-types, eq. (4), and closed
higher-order terms occur internally), and the source defines
first-order by restricting the schema - "recurrence restricted to
object types of the form `Omega^m o`" (section 2.4(3), p. 216) -
not by restricting the endpoints; no conservativity statement in
the paper identifies the two. (Those hom-sets are in any case
strictly smaller than the collapse: exponentiation has no realizer
over any tower-sort context, section 6.1.) The restriction is
therefore on the signature, not on the objects. The DLMZ
tier-vector notation of section 2.3 (`i < j` in place of
`Omega tau` against `tau`) is used for these sub-theories
in prose and docstrings, and a standalone tier-sorted (`S = N`)
instantiation of the same generic core is deferred to the
first-order characterization workstreams (section 9), which can
weigh its citation fit then. Note the class boundary: the
elementary class arises from the higher-order type discipline over
any non-trivial free algebra (Theorem 14), not from the choice of a
tree algebra; first-order recurrence over tree algebras is the
polytime-with-DAG-representation territory of section 2.3 and is
not treated here.

Objects of each syntactic category are contexts (sort lists);
morphisms are tuples of terms modulo the interpretative setoid;
composition is substitution. The rule-menu questions of the
equational presentation (extensionality at arrow sorts;
Goodstein-style uniqueness) move to the deferred workstream
(section 9).

### 4.2 Interfaces

Interface sketches; names provisional. `S` is the sort type;
`Ctx S := List S`.

```lean
/-- A multi-sorted algebraic signature: operations with sorted
arities. The DTC realization represents the same data as an indexed
polynomial functor; the native realization consumes it directly. -/
structure SortedSig (S : Type) where
  Op : Type
  arity : Op → List S
  result : Op → S

/-- Signature sum: data-types-a-la-carte assembly. -/
def SortedSig.sum (F G : SortedSig S) : SortedSig S

/-- Constructor summand, derived from the algebra's polynomial
signature functor (shapes = operations, positions = arities), one
copy per object sort. -/
def constructorSig (F : PolyFunctorData) (isObj : S → Prop) :
    SortedSig S

/-- Application at arrow sorts (higher-order system only). -/
def appSig (arrow : S → S → Option S) : SortedSig S

/-- Schema-generated identifiers: explicit definitions and ramified
monotonic recurrences over previously defined identifiers. The
signature and its defining equations are generated together, as in
ERMor1. -/
inductive RIdent (base : SortedSig S) : List S → S → Type

/-- Destructors and case (the flat-recurrence replacements of
Lemma 1; needed by the definability route). -/
def dstrCaseSig (F : PolyFunctorData) (isObj : S → Prop) :
    SortedSig S
```

Term layer (representation-independent; both the native-inductive
and the `PolyFix` realizations must provide it):

```lean
Tm    : SortedSig S → Ctx S → S → Type
var   : (i : Fin Γ.length) → Tm Σ Γ (Γ.get i)
op    : (o : Σ.Op) → (args : ∀ i, Tm Σ Γ (Σ.arity o).get i) →
        Tm Σ Γ (Σ.result o)
subst : Tm Σ Γ s → (∀ i, Tm Σ Δ (Γ.get i)) → Tm Σ Δ s
subst_id    : t.subst var = t
subst_subst : (t.subst σ).subst τ = t.subst (fun i => (σ i).subst τ)
eval : (M : SortedModel Σ) → Tm Σ Γ s → M.Env Γ → M.carrier s
```

Interpretation and syntactic category. The quotient relation is a
parameter of the construction, instantiated in this workstream with
the interpretative setoid; the deferred equational workstream
(section 9) re-instantiates the same construction with a
`Derivable`-style relation.

```lean
/-- The standard model: object sorts interpret as the algebra's
carrier (the PolyFix of the signature functor; for 1 + X, N), arrow
sorts as function spaces. -/
def standardModel (P : Presentation) : SortedModel P.sig

/-- Extensional equality of eval at standardModel P - the
erMorNSetoid pattern, sorted. The model dependence is structural:
erMorNSetoid needs no such parameter only because ERMorN.interp is
globally fixed. -/
def interpSetoid (P : Presentation) (Γ : Ctx S) (s : S) :
    Setoid (Tm P.sig Γ s)

def SynCat (Σ : SortedSig S) (r : QuotRel Σ) : Type := Ctx S
instance : Category (SynCat Σ r)          -- comp = subst
instance : CartesianMonoidalCategory (SynCat Σ r)  -- concatenation
```

Assembly plan: hom-setoids first (`SetoidCat` shapes), quotient
last, so pre-quotient statements remain stateable. Instantiated at
the interpretative setoid, the construction directly generalizes the
boilerplate that `LawvereERQuot.lean` and `LawvereKSimQuot.lean`
each hand-roll (retrofit of those files remains out of scope).

Ramified structure (revision 1's section 4.4 carries over):
`RType`; the presentation `higherOrder (F)`, generic in the
signature functor, with the first-order sub-theories as restricted
signatures inside it (section 4.1);
the Omega shift by base substitution `tau[o := Omega o]`
(postcomposition with Omega is not a signature morphism at arrow
sorts; on first-order sorts the shift is the tier successor);
`kappaHat (τ) : [RType.omega τ] ⟶ [τ]` at the Omega-sort, supplying
copoint components at the Omega-sorts (no raising coercion exists;
constant maps of type `o -> Omega o` exist, an identity-realizing
one does not); their assembly into a copoint depends on open
question 3.

### 4.3 Inter-system functors

- Sub-theory inclusions: each first-order sub-theory includes into
  its host r-type instantiation by construction (same sorts, larger
  signature); no sort translation is involved. The tier-to-r-type
  functor (`m` to `Omega^m o`) is deferred with the standalone
  tier-sorted instantiation (section 9).
- Algebra-map functoriality: a morphism of signature functors (e.g.
  `1 + X` into `1 + 2 X`) induces a functor of syntactic categories.
- `omegaShift`: the sort shift maps the constructor summand
  (present at every object sort) and eq. (4) monotonic recurrences
  to schema instances, but not the flat-recurrence and destructor
  summand, whose scrutinee is pinned at sort `o` (eq. (5) and the
  p. 215 note; destructors are `o -> o`, section 2.5) - the shifted
  destructor at `[Omega o]` has no evident realizer. Endofunctor
  status, for the sub-theories as for the full system, is open
  question 3.
- `kappaHat` at every r-type; whether its components assemble into
  a copoint of a shift endofunctor depends on open question 3.
- Lemma 1 and Lemma 2 as reductions between presentation variants
  (flat versus destructor-case; simultaneous versus plain) - both
  are also ingredients of the definability route.

## 5. Reference target and algebra choice for the equivalence

### 5.1 `LawvereERCat` versus `LawvereKSimDCat 2`

The two are equivalent (`erKSimEquiv`), so the choice is of proof
economy, not content; whichever is proven, the other follows by
composing with the equivalence.

- Definability direction (reference contained in `RMRec-omega`): the
  machine route starts from "the reference function is elementary-
  time URM-computable". For ER this is exactly `compileER` +
  `boundExprK_dominates`, already formalized; for K^sim_2 one first
  crosses `kToERFunctor`. ER is the shorter path by one existing
  hop.
- Soundness direction (collapse of `RMRec-omega` contained in the
  reference): both landings need "elementary-time computation is
  reference-definable" (section 6.4). The K^sim landing has the
  formalized simulator (`KSimURMSimulator.simulate` clocked by a
  K-expressible bound - the exact pattern of `erToKFunctor`); the ER
  landing would compose that with `kToERFunctor`, or use ER-side
  bounded recursion on Godel codes directly.
- The stratified, recursion-primitive character of K^sim (the user
  review's observation) shows up here: K^sim absorbs "run this
  machine for a bounded number of steps" natively, which is the
  shape of both machine-facing steps.

Recommendation: state the theorem against `LawvereERCat` (the
project's canonical elementary reference), but route the machine-
facing legs through the existing K^sim simulator infrastructure and
transfer across `erKSimEquiv` where that is shorter. The plan phase
fixes the exact factoring.

### 5.2 Which algebra hosts the proof

Theorem 14 holds for every non-trivial free algebra, in particular
for the unary naturals. Two options for the one in-scope proof:

- Over `1 + X` (unary naturals, higher-order types). The collapse
  functions are numeric; the reference (`LawvereERCat`) is numeric;
  zero-test URM programs embed into Leivant's register machines
  over the unary algebra with constant overhead (section 1.2). No
  coding layer at all.
- Over `1 + X^2` (binary trees, higher-order types). Faithful to the
  user review's canonical tree instance, but every leg acquires a
  tree-to-numbers coding layer (Leivant's Lemma 5 concerns exactly
  this reducibility, with an exponential-time factor that elementary
  absorbs), and register machines over the tree algebra (registers
  holding trees, constructor/destructor commands) do not yet exist
  in the repository or CSLib. Partial coding assets exist
  (`LawvereNatBT*`, `erToNatBTV2Functor`).

Recommendation: instantiate the generic higher-order presentation
at all three signature functors (a small step, since the
presentation is generic in the functor); host the
in-scope equivalence proof over `1 + X`; record "the tree-algebra
higher-order system also characterizes elementary" as a future
corollary, with the coding-based route sketched in section 9. This
keeps the proof free of coding while preserving the
canonical-instances plan.

## 6. The theorem and its proof-route map

### 6.1 Statement shape

```lean
/-- SynCatFO: the full subcategory of the higher-order syntactic
category on contexts of object sorts - o and Omega tau for
arbitrary r-types tau. Every object sort's universe is a copy of
the base carrier (Leivant III section 2.7: "the universe of sort
theta is a copy A^theta of A"), so morphisms between object-sort
contexts denote numeric functions. -/
def SynCatFO (P : Presentation) : Type

/-- Soundness packaged as a functor. With interpretative hom-sets
it is well-defined and faithful by construction; the substance is
that every denotation is ER-definable (section 6.3). natSig is the
1 + X signature functor of the unary naturals (section 5.2). -/
def collapseFunctor : SynCatFO (higherOrder natSig) ⥤ LawvereERCat

/-- Definability (the completeness direction, section 6.2),
quantified over object-sort input contexts, rendering Leivant's
f-minus definability (section 2.7 of the paper: a function over A
is defined in RMRec-omega when it is the collapse f-minus of some
ramified f). ObjCtx n is the type of object-sort contexts of
length n; oCtx m is the context of m copies of o. -/
theorem ramified_definability {n m} (f : (n : LawvereERCat) ⟶ m) :
    ∃ (Γ : ObjCtx n) (g : Γ ⟶ oCtx m),
      collapseDenotation g = f
```

The quantification over object-sort contexts is required by the
source. It must range beyond the tower sorts `Omega^k o`: Lemma 6's
own realizer (eq. (8), p. 221) takes its input at the object sort
`Omega(eta -> eta)`, the coercions of section 2.4(1) run downward
only, and tower-sorted inputs drive object-type recurrence alone
(the first-order fragment), so, e.g., exponentiation has no
realizer over any tower-sort context. It must also be an
existential and not fullness of `collapseFunctor` (revision 2
asserted that fullness; it is false): sort-uniform hom-sets are
strictly smaller than elementary - at `[o] -> [o]` no monotonic
recurrence applies to the input (its recurrence argument must sit
at an Omega-sort), and flat recurrence, which is available at sort
`o`, passes no recursive results and so yields case analysis and
destructors only; doubling has no realizer there.

Together the two statements are the denotational form of
Leivant III Theorem 14, items (1)-(2), relative to `LawvereERCat`
as the reference definition of elementary. The K^sim_2 corollary
transfers at the level of these statements across `erKSimEquiv`.

A categorical packaging - a single category collecting ramified
morphisms across object-sort contexts, coercion-mediated, equivalent
to `LawvereERCat` - is an investigation item (open question 7), not
an assertion: over general object sorts the coercion diagram is not
directed as a tower-indexed colimit would require, composition on
classes carries a well-definedness obligation, and any
`omegaShift`-based alignment depends on open question 3. The
theorem content is the two statements above either way.

### 6.2 Definability: the machine route (all transcription)

Chain, for an arbitrary ER morphism `e`:

1. `compileER e : URMProgram a` computes `e.interp` within runtime
   `tower mu_e (max v + offset_e)` - formalized
   (`compileER_pre_stop_correct`, `boundExprK_dominates`).
2. Leivant III Lemma 6, transcribed against the zero-test URM over
   the unary algebra: a function computed by a register machine in
   time `c * 2_q(sz(input))` is definable in `RMRec-omega_o` - the
   machine state is tracked by functions `stt` and `[phi]` defined
   by ramified simultaneous recurrence over the step relation,
   clocked by the ramified `2_q` composed with `sz` and `x`.
   Ingredients, each a transcription: coercions (2.4(1)), `+`/`x`
   (2.4(2)), `2_m` (2.4(4)), `sz` (2.4(6)), simultaneous recurrence
   (Lemma 2), `case`/`dstr`. The tower bound of step 1 must be
   converted to Leivant's `c * 2_q` clock format - arithmetic over
   formalized bounds, not new mathematics.
3. Lemma 1, transcribed: `RMRec-omega_o` definability yields
   `RMRec-omega` definability.

Arity remark: Lemma 6's statement covers p-ary functions, but its
proof is displayed for a unary input (single loading clause, unary
eq. (8)); the transcription assembles the n-input, m-output case
componentwise, with the clock bound taken over all inputs.

The adaptation of Lemma 6 from Leivant's machine format
(begin/end states, three command kinds) to the zero-test URM's
(PC-indexed instruction list) is a presentation adaptation of the
kind section 1.2 permits: either the constant-overhead embedding of
URM programs into Leivant machines (section 1.2) followed by the
verbatim transcription, or the transcription of Lemma 6's proof
shape directly against the URM step relation; the plan phase picks
one.

### 6.3 Soundness: the normalization route

The literature route (Leivant III sections 4-5), all transcription:

1. From `RMRec-omega` (Proposition 7's item (1)) to `RlMR-omega_o`
   (item (4)), as the paper's composite through Proposition 7
   (p. 223): (1) to (3) by the translation of eq. (9), which lands
   in the full calculus `RlMR-omega` (recurrence with parameters
   becomes closed `R-tau` operators); (3) to (4), which the paper
   states is "similar" to Lemma 1 - its transcription reconstructs
   that indicated argument at the applicative level. Both
   applicative calculi therefore enter as proof-internal apparatus.
2. Lemmas 8-10 and Proposition 11: closed `RlMR-omega_o` terms are
   represented in `1l(A)` (simply typed lambda calculus with
   `dstr`/`case` constants) via the Berarducci-Boehm representation
   and the section 4.2 term translation `E` to `E-bar`.
3. Lemma 12: a term of height `h` and redex rank `q` normalizes in
   time `O((2_{q+1}(h))^2)`; Proposition 13 (whose proof also uses
   Lemma 4 to reduce to target type `o`): represented functions are
   computable in elementary time.
4. Landing (section 6.4): elementary-time computation is
   reference-definable.

Steps 1-3 require formalizing typed lambda terms with binders
(intrinsically-typed de Bruijn representations; templates in
section 3.3) and the normalization-bound argument; this is the
workstream's dominant cost.

Candidate reuse to be investigated before the plan phase: the
repository's Beckmann-Weiermann `T*` formalization (section 3.3)
already provides a lambda-free typed combinatory calculus with a
reduction relation and the Lemma 16 tower bound, transcribed from a
published elementary characterization. If the literature supports a
translation from `RMRec-omega` (or from `1l(A)`-represented
functions) into `T*` - to be checked in Beckmann-Weiermann 2000 and
its citation neighborhood - the soundness route could reuse that
asset in place of a new normalization development. Two
preconditions gate the reuse. First, under the transcription-only
policy the substitution is admissible only if the bridge itself is
literature. Second, the `LawvereGodelT*` formalization has only
thin test coverage and no downstream consumers, so before any
reliance it must be audited clause by clause against
Beckmann-Weiermann 2000 (their Definition 4 reduction relation, the
Definitions 7-10 measures, and the Lemma 16 statement and proof
structure); until that audit it is treated as not established to
represent its source. Failing either precondition, route 1-3
stands.

### 6.4 Landing elementary computation in the reference category

Both directions' machine-facing legs end at "a computation clocked
by a tower bound"; the remaining step is that such computation is
reference-definable. Options, using existing assets:

- K^sim landing: implement the relevant step function (URM step for
  section 6.2 - already done as `KSimURMSimulator`; normalization
  step on term codes for section 6.3 - new) and clock it with a
  K-expressible bound; transfer to ER across `erKSimEquiv`. This is
  the pattern already executed once (`erToKFunctor`).
- ER landing: bounded recursion on Godel codes ER-side (the
  repository has Godel-numbering and bounded-recursion machinery in
  the `LawvereER*`/`Utilities` layers and precedent in
  `EraComplete`).

For section 6.2 nothing new is needed (the chain lands directly in
`RMRec-omega`). For section 6.3 the landing means implementing a
normalizer on term codes with a verified elementary clock - the
largest single deliverable of the workstream whichever landing is
chosen; the plan phase decides between the two after the
Beckmann-Weiermann investigation.

## 7. Candidate approaches for the syntax layer

Unchanged from revision 1 in substance; the interpretation and
categorical layers above are representation-independent.

- Approach A: sorted-Era native inductives. Proven pattern, best
  ergonomics, shallow composability.
- Approach B: DTC on the in-repository `PolyFix` stack
  (`polyBetweenCoprod` summands, `IndexedEAT`-style equational
  quotients). Construction-level composability; startable today;
  W-type ergonomics cost.
- Approach C: DTC on the vendored slice/presheaf functors once
  W-types and coproducts land upstream in geb-mathlib; migration
  from B via a `polyEndoEquiv`-style bridge.

| Dimension | A (native) | B (PolyFix) | C (vendored) |
| --- | --- | --- | --- |
| Startable today | yes | yes | no (needs W-types, coproducts) |
| Time to in-scope theorem | shortest | medium | longest |
| Construction-level composability | no (parameter-level) | yes | yes |
| Clone laws | per-system, trivial | once, generic | once, generic |
| Proof ergonomics | best | costs (custom recursors) | costs (same) |
| geb-mathlib program alignment | none | indirect | direct |
| Dependency risk | none | low (in-repo, stable) | high (WIP upstream) |

Recommendation: fix the section-4.2 interface first; spike the
monadic first-order sub-theory (the smallest restricted signature
over `1 + X`) through the syntactic-category construction in both A
and B - the spikes are throwaway prototypes of the phase-4
artifact, run before phase 1 commits to a representation; decide on
that evidence, with C the convergence target. If a default must be
chosen without spikes: B.

## 8. Deliverables and phasing

In dependency order (phase boundaries fixed by the plan, not here):

1. Core layers: sorted signatures (with `constructorSig` from
   polynomial signature functors), term layer with clone laws, the
   standard interpretation with its extensional setoid, generic
   syntactic category with finite products.
2. Higher-order system over `1 + X` (r-type sorts, schema-generated
   identifiers): category; `omegaShift` at the sort level
   (endofunctor status per open question 3); `kappaHat`; the paper's
   section 2.4 example ladder (coercions, `+`, `x`, `e`, `2_m`,
   `sz`) - both validation and Lemma 6 ingredients.
3. Algebra genericity: the presentation as a function of the
   signature functor; instantiations at `1 + 2 X` and `1 + X^2`;
   algebra-map functoriality.
4. First-order sub-theories: the restricted signature over the
   tower sorts, with its inclusion into the host theory; the monadic
   sub-theory doubles as the section-7 spike vehicle and hosts the
   ramified `+`/`x` examples at first order.
5. Definability data (section 6.2): Lemma 2 and Lemma 1
   transcriptions; Lemma 6 transcription against `ZeroTestURM`;
   bound-format arithmetic; deliverable: for every ER morphism, an
   object-sort context and a ramified realizer with matching
   denotation (the `ramified_definability` family).
6. Soundness route (section 6.3): Beckmann-Weiermann bridge
   investigation gate; then either the `T*` reuse or the
   `RlMR-omega`/`RlMR-omega_o`/`1l(A)`/Lemma 12 transcription; the
   landing normalizer (section 6.4); `collapseFunctor`.
7. Assembly: `ramified_definability` from phase 5's family,
   `collapseFunctor` from phase 6; the categorical packaging only if
   open question 7 resolves it; Theorem 14 (1)-(2); K^sim_2
   corollary via `erKSimEquiv`.

## 9. Deferred and future work

- The equational presentation (its own future workstream): re-
  instantiate the section-4.2 syntactic-category construction with a
  `Derivable`-style relation over Leivant's defining equations
  (Era-pattern rules: `ax`, `refl`, `euclid`, congruence `subst`;
  rule-menu decisions - extensionality at arrow sorts,
  Goodstein-style uniqueness - and categoricity questions live
  there), prove its soundness against the standard interpretation
  built in this workstream, and restate the in-scope equivalence
  equationally. The interpretation layer of this workstream is a
  prerequisite of that soundness proof.
- First-order complexity characterizations: linear space (monadic;
  no reference category exists yet - section 2.4) and polynomial
  time (polyadic; reference theory to be chosen; note Heraud-Nowak
  as mechanization precedent). Those workstreams also decide
  whether to build the standalone tier-sorted (`S = N`)
  instantiation of the generic core - the DLMZ presentation, with
  its tier-to-r-type inclusion functor - for citation fit, or to
  keep working with the sub-theories of section 4.1. Over tree
  algebras at first order, any future result must first build a
  DAG/graph cost model
  (Dal Lago-Martini-Zorzi; Danner-Royer 2022's compressed-size
  device for completeness).
- The applicative calculi `RlMR-omega`/`RlMR-omega_o` as goals
  (Proposition 7 in full; Theorem 14 items (3)-(5)).
- Arbitrary infinite free algebras, including the tree-algebra
  corollary for `1 + X^2`: the intended route is a categorical
  equivalence, proven entirely within the ramified framework,
  between the collapse-relevant fragment of `RMRec-omega` over an
  arbitrary infinite free algebra and the same fragment over
  `1 + X`; composing with this workstream's `1 + X`
  characterization against `LawvereERCat` (section 6.1) then yields
  the ER characterization for every algebra, with all machine
  involvement confined to the `1 + X` case. The two directions are
  definability transports across a coding bijection between the
  algebra and `N` - taken to be the same term coding the
  section-6.4 landing uses, so no further coding-compatibility
  step arises. From `1 + X` into the algebra: the unary
  sub-algebra of an infinite algebra - generated by a 0-ary and a
  positive-arity constructor, the alpha/beta device of the paper's
  section 2.4(5) - carries a translation of the `1 + X` system
  (constructors map to derived operations, `s` to
  `beta(-, alpha, ..., alpha)`, and recurrence transports with
  arbitrary clauses for the remaining constructors, as in the
  paper's footnote 9; a derived-operation map, beyond the plain
  signature-functor morphisms of section 4.3), together with
  encoding and decoding between the algebra and its unary
  sub-algebra, built by ramified structural recursion from pairing
  functions whose arithmetic lives in the free algebra of `1 + X`
  (the repository's Szudzik machinery,
  `GebLean/Utilities/Tupling.lean`, on the ER side), with
  elementary code growth. From the algebra into `1 + X`: the coded
  conjugate of every algebra-definable function has elementary
  denotation by the algebra-generic soundness route (section 6.3
  applied at that algebra), hence is `1 + X`-definable by this
  workstream's definability theorem (section 6.2) - no new
  ingredient beyond the two already planned. With interpretative
  hom-sets the functor laws are extensional, so the packaging is
  the `erKSimEquiv` pattern. A design point for that workstream: state the
  equivalence on the object-sort fragments (sufficient for the
  corollary) or strengthen it to the full categories by conjugating
  arrow sorts through the bijection. Status: Leivant III proves the
  general-algebra theorem by per-algebra register machines
  (Lemma 6, proved in full) and never compares two ramified systems
  directly, so the categorical route is a novel assembly; its
  paper-anchored ingredients are section 2.4(5) and Lemma 5 (used
  only as motivation for the coded viewpoint; the paper declares
  Lemma 5's proof straightforward and omits it), and the
  transcription-faithful fallback is Lemma 6 transcribed over
  register machines for the given algebra (which exist in neither
  the repository nor CSLib - section 5.2 - a cost signal for the
  choice). The future workstream chooses between the two and marks
  accordingly.
- Ramified corecursion over the final coalgebras (M-types) of the
  same signature functors (Danner-Royer 2012; Ramyaa-Leivant
  logspace streams).
- The Omega-shift structure analysis (the copoint question of
  open question 3; the graded-(co)monad question; the polarity
  alternative) - statement-level novelty, optional, inherited from
  revision 1.
- Retrofit of `LawvereERQuot`/`LawvereKSimQuot` onto the generic
  syntactic-category construction; relation of the higher-order
  theory to `Era.lean`'s single-sorted basis; multi-sorted data
  systems (Leivant III section 6.2).

## 10. Open questions

1. Soundness-route gate (first investigation of the plan phase):
   does the literature provide a bridge from `RMRec-omega` or
   `1l(A)` to Beckmann-Weiermann `T*` (section 6.3)? Check
   Beckmann-Weiermann 2000 and its citation neighborhood. Reuse of
   `LawvereGodelT*` requires both an affirmative answer and the
   section-6.3 audit of that formalization against the source;
   failing either, the Leivant III sections 4-5 transcription
   stands.
2. Landing choice for the soundness normalizer (section 6.4): K^sim
   simulator pattern versus ER-side bounded recursion on codes.
3. The Omega shift as an endofunctor. For the full higher-order
   system: base-substitution functoriality (interpretation
   compatibility). For the first-order sub-theories: the
   flat-recurrence and destructor summand blocks the sort shift
   from being a signature endomorphism (scrutinee pinned at `o`;
   the shifted destructor at `[Omega o]` has no evident realizer),
   so no fragment's endofunctor is currently established; the
   copoint statements of sections 4.2 and 4.3 are conditioned on
   this question.
4. Sorted-context indexing for the DTC realizations (contexts as
   index components versus parameters).
5. Whether `Presentation` carries object-sort structure as data or
   as a typeclass; interaction with theory-inclusion functors.
6. Obtain Otto's thesis and check overlap before the design spec
   claims novelty for the packaging (section 2.5).
7. Whether a categorical packaging of section 6.1's two statements
   exists on transcription-compatible terms: the coercion diagram
   over object-sort contexts is not directed, composition on classes
   needs well-definedness, and `omegaShift`-based alignment depends
   on question 3. If none does, the two statements stand alone.

## References

Primary and companion:

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

Added 2026-07-02 (section 2.3):

- U. Dal Lago, S. Martini, M. Zorzi, "General ramified recurrence is
  sound for polynomial time", DICE 2010, EPTCS 23, 47-62.
  DOI `10.4204/EPTCS.23.4`.
- N. Danner, J. S. Royer, "Ramified structural recursion and
  corecursion", 2012. arXiv `1201.4567`.
- N. Danner, J. S. Royer, "General ramified recurrence and
  polynomial-time completeness", preliminary draft, 2022.
  arXiv `2205.10348`.
- R. Ramyaa, D. Leivant, "Ramified corecurrence and logspace",
  MFPS XXVII, ENTCS 276 (2011) 247-261.

Normalization-bound reuse candidate:

- A. Beckmann, A. Weiermann, "Characterizing the elementary recursive
  functions by a fragment of Godel's T", Archive for Mathematical
  Logic 39 (2000) 475-491.

Categorical and type-theoretic (section 3.1): Otto (McGill thesis,
1995); Burroni (CTGDC 27(1), 1986); Thibault (JPAA 24, 1982,
DOI `10.1016/0022-4049(82)90060-3`); Cook-Urquhart (APAL 63, 1993,
DOI `10.1016/0168-0072(93)90044-E`); Hofmann (BSL 3(4), 1997;
CSL 1997, LNCS 1414, DOI `10.1007/BFb0028020`; JFP 9(3), 1999;
APAL 104, 2000); Bellantoni-Niggl-Schwichtenberg (APAL 104, 2000);
Dal Lago-Martini-Roversi (TYPES 2003, LNCS 3085,
DOI `10.1007/978-3-540-24849-1_12`); Danos-Joinet (Information and
Computation 183(1), 2003); Laurent (TAC 22(10), 2009);
Brunel-Gaboardi-Mazza-Zdancewic (ESOP 2014,
DOI `10.1007/978-3-642-54833-8_19`); Burrell-Cockett-Redmond (TCS,
2014, DOI `10.1016/j.tcs.2013.09.034`); Ostrin-Wainer (APAL 133,
2005); Danner (TLCA 2001, LNCS 2044); Hainry-Kapron-Marion-Pechoux
(LICS 2020, DOI `10.1145/3373718.3394768`); Dal Lago-Hofmann
(FSTTCS 2005, arXiv `cs/0506079`); Hofstra-Scott (arXiv
`2001.05778`).

Mechanization: Heraud-Nowak (ITP 2011, LNCS 6898, arXiv `1102.5495`);
Feree-Hym-Mayero-Moyen-Nowak (CPP 2018, DOI `10.1145/3167097`).

Hierarchy background: Tourlakis, "Primitive recursive complexity
topics", lecture notes, 2018 (verified quotations recorded in
`docs/research/2026-04-30-ksim-polynomial-bound-references.md`);
Meyer-Ritchie (Proc. ACM National Meeting 1967, 465-469).
