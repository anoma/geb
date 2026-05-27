<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Lawvere Theory of the K^sim Hierarchy](#lawvere-theory-of-the-k%5Esim-hierarchy)
  - [Status](#status)
  - [Overview](#overview)
  - [Motivation](#motivation)
  - [Mathematical Setting](#mathematical-setting)
    - [Definition (Tourlakis 2018)](#definition-tourlakis-2018)
    - [Equivalent characterizations](#equivalent-characterizations)
    - [Required theorems](#required-theorems)
  - [Design Principles](#design-principles)
    - [P1 — Non-dependent term type](#p1--non-dependent-term-type)
    - [P2 — Minimal-level assignment](#p2--minimal-level-assignment)
    - [P3 — Explicit `raise` constructor](#p3--explicit-raise-constructor)
    - [P4 — Depth restriction via quotient image](#p4--depth-restriction-via-quotient-image)
    - [P5 — Most-general induction principle first](#p5--most-general-induction-principle-first)
    - [P6 — Layered recursion schemes](#p6--layered-recursion-schemes)
    - [P7 — Lawvere-theory shape](#p7--lawvere-theory-shape)
    - [P8 — `simrec` lives in `KMor1` with output index](#p8--simrec-lives-in-kmor1-with-output-index)
    - [P9 — KMorN-to-KMor1 collapse via pairing](#p9--kmorn-to-kmor1-collapse-via-pairing)
    - [P10 — Interpret-and-verify discipline](#p10--interpret-and-verify-discipline)
  - [Lean Structural Design](#lean-structural-design)
    - [File layout](#file-layout)
    - [Generator inventory for `KMor1`](#generator-inventory-for-kmor1)
    - [Level computation](#level-computation)
    - [Interpretation](#interpretation)
    - [Quotient by extensional equality](#quotient-by-extensional-equality)
  - [Phase 1 — The K^sim Hierarchy as a Category](#phase-1--the-k%5Esim-hierarchy-as-a-category)
    - [1.1 Deliverables](#11-deliverables)
    - [1.2 Term language](#12-term-language)
    - [1.3 Interpretation](#13-interpretation)
    - [1.4 Extensional-equality quotient](#14-extensional-equality-quotient)
    - [1.5 Lawvere-theory product structure](#15-lawvere-theory-product-structure)
    - [1.6 K^sim_d realization](#16-k%5Esim_d-realization)
    - [1.7 Tests](#17-tests)
    - [1.8 Open issues for the Phase-1 implementation](#18-open-issues-for-the-phase-1-implementation)
  - [Phase 2 — K^sim_2 ≌ LawvereER](#phase-2--k%5Esim_2-%E2%89%8C-lawvereer)
    - [2.1 Theorem statement](#21-theorem-statement)
    - [2.2 Strategy](#22-strategy)
    - [2.3 Forward translation `kToER`](#23-forward-translation-ktoer)
      - [2.3.1 simrec via Szudzik pairing](#231-simrec-via-szudzik-pairing)
      - [2.3.2 Szudzik pairing in ER](#232-szudzik-pairing-in-er)
      - [2.3.3 Bounded primitive recursion in ER](#233-bounded-primitive-recursion-in-er)
      - [2.3.4 Interpretation-preservation lemma](#234-interpretation-preservation-lemma)
    - [2.4 Backward translation `erToK`](#24-backward-translation-ertok)
      - [2.4.0 `sub` translation](#240-sub-translation)
      - [2.4.1 `bsum` translation](#241-bsum-translation)
      - [2.4.2 `bprod` translation](#242-bprod-translation)
      - [2.4.3 Interpretation-preservation lemma](#243-interpretation-preservation-lemma)
      - [2.4.4 Quotient-class level lemma](#244-quotient-class-level-lemma)
    - [2.5 Round-trip identities](#25-round-trip-identities)
    - [2.6 Categorical packaging](#26-categorical-packaging)
    - [2.7 Worked examples](#27-worked-examples)
    - [2.8 Open issues for the Phase-2 implementation](#28-open-issues-for-the-phase-2-implementation)
  - [Phase 3 — ⋃_n K^sim_n ⊆ Primrec](#phase-3--%E2%8B%83_n-k%5Esim_n-%E2%8A%86-primrec)
    - [3.1 Theorem statement](#31-theorem-statement)
    - [3.2 Encoding the input vector](#32-encoding-the-input-vector)
    - [3.3 Translation `kToPrimrec`](#33-translation-ktoprimrec)
    - [3.4 simrec via Szudzik trace](#34-simrec-via-szudzik-trace)
    - [3.5 Functor / certificate packaging](#35-functor--certificate-packaging)
    - [3.6 Tests](#36-tests)
    - [3.7 Open issues for the Phase-3 implementation](#37-open-issues-for-the-phase-3-implementation)
  - [Open Questions](#open-questions)
  - [References](#references)
    - [Primary sources](#primary-sources)
    - [Supporting sources](#supporting-sources)
    - [Lean infrastructure](#lean-infrastructure)
    - [Project context](#project-context)
    - [External context (consulted)](#external-context-consulted)
  - [Appendix A — Closure proofs via URM simulation](#appendix-a--closure-proofs-via-urm-simulation)
    - [A.0 Why a naive transcription fails](#a0-why-a-naive-transcription-fails)
    - [A.1 Overview](#a1-overview)
    - [A.2 The concrete URM](#a2-the-concrete-urm)
    - [A.3 The K^sim simulator term](#a3-the-k%5Esim-simulator-term)
    - [A.4 The compiler ER → URM](#a4-the-compiler-er-%E2%86%92-urm)
    - [A.5 The runtime bound `A_2^e ∈ K_2^sim`](#a5-the-runtime-bound-a_2%5Ee-%E2%88%88-k_2%5Esim)
    - [A.6 The composite `erToK`](#a6-the-composite-ertok)
    - [A.7 Theorems 2.4.A and 2.4.B as corollaries](#a7-theorems-24a-and-24b-as-corollaries)
    - [A.8 Generalisation to K_n^sim = E^{n+1}](#a8-generalisation-to-k_n%5Esim--e%5En1)
    - [A.9 Implementation note: file layout](#a9-implementation-note-file-layout)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

# Lawvere Theory of the K^sim Hierarchy

## Status

Design document — drafted and awaiting user review.  All
three phase sections are populated; Phase 2 carries the
mathematical detail required for the K^sim_2 ≌ ER
equivalence proof, with bounded-recursion-closure theorems
(§2.4) stated explicitly.  Once approved, this document
serves as the canonical mathematical reference for the
Phase 1 / 2 / 3 implementation plans.

## Overview

This document describes a planned formalization of the
*K^sim_n* hierarchy of primitive-recursive functions stratified
by simultaneous-recursion depth, mirroring the existing
`LawvereER*` family of modules.  The deliverables are:

1. The K^sim hierarchy realized as a Lawvere-theory category
   parameterized by depth, parallel to `LawvereER*`.
2. A categorical equivalence (or, where achievable, an
   isomorphism) between the K^sim_2 quotient category and the
   `LawvereER` quotient category.
3. A faithful interpretation of the union ⋃_n K^sim_n into
   `mathlib`'s primitive-recursive functions, parallel to
   `LawvereERPrimrec`.

The work is deliberately staged: Phase 1 (the K^sim hierarchy as
a category) lands first; Phase 2 (the K^sim_2 ≌ ER equivalence)
follows; Phase 3 (the embedding into `mathlib.Primrec`) follows
that.  Each phase has its own implementation plan; this design
document is the shared mathematical and structural reference.

## Motivation

The existing `LawvereER` development gives a categorical
formalization of the elementary-recursive functions following
the standard Wikipedia presentation: closed under composition,
bounded sum, and bounded product over the base functions
(zero, successor, projections).  That formalization is suited
to *mathematical* reasoning — bounded sum and bounded product
are elegant generators that admit clean inductive proofs.

The K^sim hierarchy provides a complementary presentation
suited to *programming-style* reasoning: K^sim is closed under
composition and *simultaneous primitive recursion* (a vector of
mutually-recursive functions defined together), which is the
construction programmers reach for when writing loops in the
most direct style.
The hierarchy stratifies by recursion-nesting depth, with
K^sim_2 corresponding (as a function class) to the elementary
recursive functions and ⋃_n K^sim_n corresponding to the
primitive-recursive functions.

A computable categorical equivalence

  K^sim_2 ≌ LawvereER

would let theorems be developed naturally on the
mathematician-friendly ER side while programs are written
naturally on the programmer-friendly K^sim_2 side, with the
equivalence acting as a bidirectional translator.

The development supersedes the earlier `LawvereGodelT` and
`LawvereGodelTTerm` exploration, which used a different
stratification (Gödel's T restricted to type-0 iteration) and
encountered structural obstructions.  If the K^sim_2 ≌ ER
equivalence is proved, `LawvereGodelTTerm` is expected to be
retired.

## Mathematical Setting

### Definition (Tourlakis 2018)

The canonical reference is Tourlakis's lecture notes
*Primitive Recursive Complexity Topics* (2018), available in
the project as `.claude/docs/arithmetic-hierarchies/PR-complexity-topics.pdf`.
There, Definition 0.1.0.7 gives:

  K^sim_0  =  closure of {λx.x, λx.x+1} under substitution
  K^sim_{n+1}  =  closure of K^sim_n ∪ R^sim_{n+1}
                  under substitution
  R^sim_{n+1} =  {f : f arises from `simprim`(h,g) with
                  h, g ∈ K^sim_n}

The schema `simprim` (Tourlakis 4.2.1) is the simultaneous
primitive-recursion schema:

  Given total functions h_0, ..., h_k : ℕ^a → ℕ
  and g_0, ..., g_k : ℕ^{a+1+(k+1)} → ℕ,
  define f_0, ..., f_k : ℕ^{a+1} → ℕ jointly by
    f_i(0,    y⃗) = h_i(y⃗)
    f_i(x+1,  y⃗) = g_i(x, y⃗, f_0(x,y⃗), ..., f_k(x,y⃗))

The schema produces a vector of k+1 mutually-recursive
functions sharing a recursion variable x and accessing each
other's previous-step values.

The Tourlakis-2018 word "substitution" denotes Grzegorczyk
substitution (a restricted form of composition: variable
renaming, dummy-variable introduction, substitution of
constants for variables, and substitution of single
earlier-defined functions for variables); §0.1.0.3 there
explicitly distinguishes it from the standard PR
"composition" rule.  Iterated Grzegorczyk substitution
generates the same function class as full composition (a
standard result endorsed in Tourlakis §0.1.0.5), so both
choices of generators produce the same K^sim hierarchy as a
function class.  The Lean development chooses *full
composition* as a constructor (matching `ERMor1`) and proves
the function-class equivalence with Tourlakis's definition as
a separate proposition.

### Equivalent characterizations

The same hierarchy of function classes appears in the
literature under several equivalent presentations:

* The Grzegorczyk hierarchy E^n: closed under bounded
  recursion over a sequence of fast-growing functions.
  E^{n+1} = K^sim_n as function classes; E^3 = K^sim_2 = ER.
* The Meyer-Ritchie LOOP hierarchy L_n: programs in a
  small imperative language with at most n levels of
  bounded loop nesting.  L_n = K^sim_n; L_2 = ER;
  ⋃_n L_n = PR.
* The Damnjanovic L_2^k refinement of the LOOP-2 layer.

Tourlakis 2018 §0.1.0.15 supplies a constructive proof that
K^sim_n = L_n (program-transcription in both directions).
Meyer-Ritchie 1967 supplies the proof that L_2 = ER and
⋃_n L_n = PR.  The Grzegorczyk-hierarchy chapter
(Tourlakis Computability Notes ch. 4) supplies bsum/bprod
↔ bounded recursion bridges within E^3.

### Required theorems

The Lean formalization needs three function-class
identifications and one proper-hierarchy fact:

* (A) ⋃_n K^sim_n ⊆ PR.  Phase 3 deliverable.  Direct
  by induction over the K^sim constructors using the
  Hilbert–Bernays Gödel-encoding translation
  (Tourlakis 4.2.2).
* (B) ER ⊆ K^sim_2 (function-class inclusion).  Half of
  Phase 2.  Translates each ER generator into a K^sim_2
  morphism.
* (C) K^sim_2 ⊆ ER (function-class inclusion).  Other
  half of Phase 2.  Translates each K^sim_2 morphism into
  an ER morphism by induction on the K^sim_2 syntax.
* (D) K^sim_n ⊊ K^sim_{n+1} (proper hierarchy).  Out of
  scope for the present formalization but stated as a
  proposition for follow-on work.

The detailed mathematical proofs of (A), (B), (C) are
developed in the relevant phase sections below.

## Design Principles

These principles govern the Lean formalization choices.  They
follow from the project conventions in `CLAUDE.md` and from
the design discussion that produced this document.

### P1 — Non-dependent term type

`KMor1` is *not* dependently indexed by recursion depth.
Depth is recovered via a structural function
`level : KMor1 n → ℕ`, not encoded into the type.

### P2 — Minimal-level assignment

`level` is structural and returns the minimum level
inhabited by the term: zero for atomic constructors,
recursive maxima for compositions, and structural
increments for `simrec` and `raise`.

### P3 — Explicit `raise` constructor

Level-bumping is a syntactic operation of the term language,
not implicit subsumption.  A term of structural level k is
moved to level k+1 only by an explicit `raise` constructor.

### P4 — Depth restriction via quotient image

The category K^sim_d is realized as the full subcategory of
the extensional-equality quotient `KMor1.QuotCat` whose
morphisms admit *at least one* syntactic representative at
level ≤ d:

    KSimMor (d a b : ℕ)
      := { [f]_ext : KMor1.QuotCat.Hom a b
         // ∃ f' : KMor1 a, level f' ≤ d ∧
            ⟦f'⟧ = [f]_ext }

The depth restriction is therefore a property of the
quotient class rather than of any single representative.
This formulation is required for the K^sim_2 ≌ ER
equivalence in Phase 2: the naive simultaneous-recursion
representation of `bsum` applied to a level-2 function
inflates the syntactic level by one, while the resulting
extensional-equality class admits an alternative
level-≤-2 representative by the bounded-recursion-closure
theorem (Phase 2 §2.4).

A purely syntactic auxiliary type

    KMor1.atDepth (a d : ℕ) : Type
      :=  { f : KMor1 a // level f ≤ d }

is also defined; it is used to *state* closure lemmas
("for every quotient class with a level-≤-d representative,
the closure under …") but does not itself carry the K^sim_d
category structure.

### P5 — Most-general induction principle first

For each new structure, the Prop-induction principle
(non-recursive hypotheses) is defined first.  All subsequent
recursion schemes for that structure are derived from it.

### P6 — Layered recursion schemes

Sophisticated recursion schemes are built on top of the
primary induction principle.  Consumers of the structure
do not write structural recursion directly.

### P7 — Lawvere-theory shape

The morphism category follows the existing `ERMor1` /
`ERMorN` pattern:

    KMor1 : ℕ → Type           (single-output morphisms)
    KMorN n m := Fin m → KMor1 n  (multi-output wrapper)
    levelN (f : KMorN n m) : ℕ
      := Finset.univ.sup (fun i => (f i).level)

The objects of the Lawvere theory are the natural numbers,
each `n` representing the product object ℕ^n.

### P8 — `simrec` lives in `KMor1` with output index

The `simrec` constructor has shape

    simrec
      (k : ℕ)            -- (k+1) is the system size
      (a : ℕ)            -- arity of the parameter list y⃗
      (i : Fin (k+1))    -- which f_i is being expressed
      (h : KMorN a (k+1))           -- base-case family
      (g : KMorN (a+1+(k+1)) (k+1)) -- step-function family
      : KMor1 (a+1)

placing the Tourlakis-`simprim` schema as a single constructor
on KMor1 selecting one component of the simultaneously-defined
vector.  This mirrors classical mathematical presentations
(which describe the system but treat each f_i individually) and
keeps the Lawvere-theory shape parallel to `ERMor1`.

### P9 — KMorN-to-KMor1 collapse via pairing

At level ≥ 2 the K^sim hierarchy contains a primitive-recursive
pairing function and its inverses; consequently, for d ≥ 2,
KMorN n m at depth d is equivalent to KMor1 n at depth d via
encoding the m-tuple output as a single natural number.  This
collapse is stated and proved as a proposition; it validates
the Lawvere-theory wrapper as a presentation convenience at
levels where it is essential (depth 0 and 1) and as a
notational convenience above.

### P10 — Interpret-and-verify discipline

Every named composite written in either `ERMor1`/`ERMorN`
or `KMor1`/`KMorN` is accompanied, in the same module, by
an interp-lemma that states the composite's interpretation
into Lean's ℕ-valued functions in closed form.  The lemma
is `@[simp]`-tagged and proved against the standard interp
rewriting set.

For example, defining `KMor1.add : KMor1 2` is paired with

    @[simp] theorem KMor1.interp_add (ctx : Fin 2 → ℕ) :
        KMor1.add.interp ctx = ctx 0 + ctx 1 := by
      ...

The discipline is an extension of the bottom-up named-
composite principle in `CLAUDE.md`: a composite without a
verified interpretation is unfinished, because nothing
ties the syntactic term back to the Lean function the
mathematician intended.  The interp-lemmas accumulate into
a rewriting set that lets later proofs reduce computations
to plain arithmetic on ℕ, and they are the bridge by which
proofs developed in Lean's interpretation layer transfer
back to the ER/K categories via the faithfulness of the
interpretation functors.

## Lean Structural Design

### File layout

The development is parallel to the `LawvereER*` family:

    GebLean/LawvereKSim.lean         -- KMor1, KMorN, level
    GebLean/LawvereKSimInterp.lean   -- interpretation into ℕ
    GebLean/LawvereKSimQuot.lean     -- extensional quotient
    GebLean/LawvereKSimPrimrec.lean  -- ⋃_n K^sim_n ⊆ Primrec

A separate module hosts the Phase 2 deliverable:

    GebLean/LawvereKSimER.lean       -- K^sim_2 ≌ LawvereER

Auxiliary developments (the K^sim_2 pairing function, the
Hilbert–Bernays Gödel encoding, the bsum/bprod ↔ simrec
translations) live under `GebLean/Utilities/` per the
bottom-up named-composite discipline.

### Generator inventory for `KMor1`

    inductive KMor1 : ℕ → Type
    | zero  : ∀ {n : ℕ}, KMor1 n              -- constant 0
    | succ  : KMor1 1                          -- successor
    | proj  : ∀ {n : ℕ}, Fin n → KMor1 n       -- projections
    | comp  : ∀ {a b : ℕ},                     -- composition
              KMor1 b → (Fin b → KMor1 a) → KMor1 a
    | simrec : ∀ {a k : ℕ},                    -- simrec
               Fin (k+1) → KMorN a (k+1) →
               KMorN (a+1+(k+1)) (k+1) → KMor1 (a+1)
    | raise : ∀ {n : ℕ}, KMor1 n → KMor1 n     -- level bump

with `KMorN n m := Fin m → KMor1 n`.

### Level computation

    def level : ∀ {n : ℕ}, KMor1 n → ℕ
    | _, zero        => 0
    | _, succ        => 0
    | _, proj _      => 0
    | _, comp f gs   =>
        max (level f)
            (Finset.univ.sup (fun i => level (gs i)))
    | _, simrec _ h g =>
        max (Finset.univ.sup (fun i => level (h i)))
            (Finset.univ.sup (fun i => level (g i))) + 1
    | _, raise f      => level f + 1

### Interpretation

`KMor1.interp : KMor1 n → (Fin n → ℕ) → ℕ` interprets each
constructor pointwise into Lean's natural numbers, mirroring
`ERMor1.interp`.  `KMorN.interp` lifts to product codomains
via the family wrapper.

### Quotient by extensional equality

`KMor1.ExtEq` is the extensional-equality relation on
single-output morphisms; `KMor1.QuotCat n` is the resulting
quotient.  `KMor1.QuotCat` is the ambient category in which
each `KSimMor d` is realized as a full subcategory per P4 —
the morphisms of `KSimMor d` are exactly the quotient
classes admitting at least one level-≤-d syntactic
representative.

## Phase 1 — The K^sim Hierarchy as a Category

Phase 1 lands the foundational structures: the term
language `KMor1`/`KMorN`, the level function, the
interpretation into ℕ, the extensional-equality quotient,
the Lawvere-theory product structure, and the K^sim_d
sub-categories indexed by depth.  No equivalence with ER
is proved here; that is Phase 2.

### 1.1 Deliverables

Phase 1 produces a type family `KMor1 : ℕ → Type` with
constructors per the inventory in §"Lean Structural
Design", together with:

* an interpretation `KMor1.interp : KMor1 a →
  (Fin a → ℕ) → ℕ` and standard interp-lemmas;
* an extensional-equality relation `KMor1.ExtEq` and
  its quotient `KMor1.QuotCat` carrying a Lean
  `Category` instance;
* a Lawvere-theory product structure on `KMor1.QuotCat`
  (terminal object, products, projections, pairings);
* for each `d : ℕ`, a full subcategory
  `KSimMor d ⊆ KMor1.QuotCat` per P4, with the
  inclusion functors `KSimMor d → KSimMor (d+1)`.

### 1.2 Term language

The constructors of `KMor1` are listed in §"Lean
Structural Design" (`zero`, `succ`, `proj`, `comp`,
`simrec`, `raise`).  Phase 1 defines them in
`GebLean/LawvereKSim.lean` together with:

* `KMor1` carries `@[ext]`, `Inhabited`, `DecidableEq`,
  and `Repr` instances (mirroring `ERMor1`).
* `KMorN n m := Fin m → KMor1 n`; `KMorN.id`,
  `KMorN.terminal`, `KMorN.fst`, `KMorN.snd`,
  `KMorN.pair`, `KMorN.comp` defined as derived
  operations following the `ERMorN` pattern.
* The level functions `KMor1.level` and `KMorN.levelN`
  defined per §"Lean Structural Design".
* The depth-monotonicity lemmas:
  `level f ≤ d → level f ≤ d + 1` (transitivity of `≤`)
  and the corresponding statement at the level of
  `KMorN`.

### 1.3 Interpretation

`KMor1.interp` is defined by structural recursion,
mirroring `ERMor1.interp` for the shared constructors and
implementing the simultaneous-recursion semantics for
`simrec`.  The simrec interpretation runs the mutual
recursion straightforwardly: build the entire (k+1)-vector
of intermediate values by stepping x times, and select the
i-th component at the end.

`KMorN.interp` lifts to product codomains:
`KMorN.interp (f : KMorN n m) v := fun i => (f i).interp v`.

The standard interp-lemmas are proved at this stage:
`interp_zero`, `interp_succ`, `interp_proj`, `interp_comp`,
`interp_raise` (which is identity), `interp_simrec`.  Each
lemma is `@[simp]` and forms the basic rewriting set for
later proofs.

### 1.4 Extensional-equality quotient

`KMor1.ExtEq` is defined by

    f ExtEq g  ↔  ∀ v, f.interp v = g.interp v

and proved to be an equivalence relation on each
`KMor1 a`.  The quotient

    KMor1.QuotCat (a : ℕ) := Quot KMor1.ExtEq

carries the obvious category structure (objects = ℕ, hom
a b = `Fin b → KMor1.QuotCat a` via the Lawvere wrapper).
The `Category` instance is verified directly:
identities, composition, and the category laws follow
from the corresponding `KMor1` operations on
representatives, all preserved by `ExtEq`.

### 1.5 Lawvere-theory product structure

`KMor1.QuotCat` carries a finite-product structure where
the product object `n × m` is `n + m`, terminals are `0`,
projections come from `KMor1.proj`, and pairing comes
from concatenation in `KMorN`.  The product-universal
property is proved by reducing to extensional equality at
the function level, mirroring the `LawvereER` proof.

### 1.6 K^sim_d realization

The depth-restricted full subcategory `KSimMor d` is
defined per P4: morphisms are quotient classes admitting
some level-≤-d representative.  At this phase the
membership predicate is given by a Σ-type ("there exists a
representative at level ≤ d"), not by a stronger structural
characterization; the structural characterizations come
later (Phase 2's Theorems 2.4.A, 2.4.B for the K^sim_2
boundary).

The inclusion `KSimMor d → KSimMor (d+1)` is induced by
the depth-monotonicity lemma from §1.2: any quotient class
with a level-≤-d representative also has a level-≤-(d+1)
representative (the same one).

### 1.7 Tests

Following the `LawvereER` testing pattern, `LawvereKSim`
includes a `test/` companion with:

* `#guard` checks that `KMor1.interp` evaluates the
  standard arithmetic functions (`add`, `pred`, `mult`,
  `exp`) to expected values for small inputs;
* Plausible properties: associativity of composition,
  identity laws, level-monotonicity-under-substitution.

The arithmetic-function definitions are placed in
`GebLean/Utilities/KSimArith.lean` per the bottom-up
named-composite discipline; each is a named `KMor1`
composite whose `level` is computed and `@[simp]`-tagged.

### 1.8 Open issues for the Phase-1 implementation

* (i) Universe polymorphism: `KMor1` is in `Type` (since
  `ERMor1` is in `Type`).  If a need for `Type u`
  generality emerges later, the constructors need
  universe annotation; this is deferred until a concrete
  use case requires it.
* (ii) The decidability of `ExtEq` is not provided: it is
  an extensional property, not decidable in general.
  Phase 1 only exposes the relation, not a `Decidable`
  instance; downstream proofs use `KMor1.interp` directly
  instead of relying on quotient decidability.
* (iii) Whether `KSimMor d` should be packaged as a
  Lean-level structure carrying its level-≤-d witness, or
  as a propositional sub-property of `KMor1.QuotCat`, is
  left to the Phase-1 implementation plan.

## Phase 2 — K^sim_2 ≌ LawvereER

This section develops the bidirectional translation in full
mathematical detail.  Phase 2 is the central deliverable of
the development: it makes the K^sim_2 syntax usable as a
"programmer's tool" by exhibiting the equivalence with the
established `LawvereER` category, allowing theorems proved on
the ER side to be transferred to the K^sim_2 side and vice
versa.

### 2.1 Theorem statement

  Theorem 2.1 (Phase-2 Equivalence).
  There exist computable functors

      F : KSimMor 2  →  LawvereER.QuotCat
      G : LawvereER.QuotCat  →  KSimMor 2

  each preserving the interpretation into ℕ-valued
  functions, such that F ∘ G and G ∘ F are naturally
  isomorphic to the identity functors.  Both natural
  isomorphisms collapse to identities, so F and G witness
  an isomorphism of categories.

The collapse to identities arises because the morphism
quotient on each side is by extensional equality.  Once F
and G preserve interpretations, the round-trip composites
have the same Lean interpretation as the original morphism
and therefore land in the same extensional-equality class.

### 2.2 Strategy

The proof has four steps.

* (1) Define a syntactic translation `kToER` from
      *level-≤-2* K^sim morphisms to ER morphisms, preserving
      the interpretation.  No translation to ER exists at
      higher levels: K^sim_n for n > 2 is strictly larger
      than ER as a function class (the union over all n is
      Primrec).  Lift `kToER` to a functor on quotient
      categories; the domain is KSimMor 2, whose morphisms
      are precisely the quotient classes admitting some
      level-≤-2 representative.
* (2) Define a syntactic translation `erToK` from ER
      morphisms to K^sim morphisms, preserving the
      interpretation, and prove that every output morphism
      has level ≤ 2 in the extensional-quotient sense
      (i.e. the resulting quotient class contains a
      level-≤-2 representative).  Lift to a functor.
* (3) Prove the round-trip identities at the level of
      extensional-equality classes — both follow from
      interpretation preservation.
* (4) Package as `Equivalence` and, where achievable, as
      `Isomorphism` of categories.

The non-trivial mathematical work concentrates in step (2),
specifically in the level-tracking analysis of the
ER-generators `bsum` and `bprod`.

### 2.3 Forward translation `kToER`

The forward direction translates K^sim morphisms into ER
morphisms by structural recursion on `KMor1`.  Each
constructor maps to a named ER composite (per the
bottom-up named-composite discipline of the `CLAUDE.md`
project conventions); the mapping table is:

| `KMor1` constructor | ER target                             |
|---------------------|---------------------------------------|
| `zero`              | `ERMor1.zeroN`                        |
| `succ`              | `ERMor1.succ`                         |
| `proj i`            | `ERMor1.proj i`                       |
| `comp f gs`         | `ERMor1.comp (kToER f) (kToER ∘ gs)`  |
| `raise f`           | `kToER f`                             |
| `simrec i h g`      | (built via §2.3.1 below)              |

`raise` is metadata in the term language; `kToER` discards
it because ER does not record level annotations.

#### 2.3.1 simrec via Szudzik pairing

The non-direct case is `simrec`.  Tourlakis's `simprim`
schema defines a vector $f_0, …, f_k$ of mutually-recursive
functions sharing a recursion variable.  In ER we encode
this vector as a single function via Szudzik elegant
pairing — the same pairing the project already uses
throughout `LawvereER` and which is implemented both in
the project's `NatElegantPair` utility and in `mathlib`.

Iterated Szudzik pairing yields an encoding
$\langle \cdot \rangle : ℕ^{k+1} → ℕ$ with elementary
inverses $π_j : ℕ → ℕ$.  Given the bases $h_0, …, h_k$ and
steps $g_0, …, g_k$ from `simrec`, define the packed
function

    F(x, ȳ) := ⟨f_0(x, ȳ), …, f_k(x, ȳ)⟩

via *bounded* primitive recursion in ER (see §2.3.3):

    F(0,    ȳ)  =  ⟨h_0(ȳ), …, h_k(ȳ)⟩
    F(x+1,  ȳ)  =  ⟨g_0(x, ȳ, π_0(F(x,ȳ)),
                          …, π_k(F(x,ȳ))),
                      …,
                    g_k(x, ȳ, π_0(F(x,ȳ)),
                          …, π_k(F(x,ȳ)))⟩

Recover the i-th component as `π_i ∘ F`.

The construction is the Hilbert–Bernays Gödel encoding
from Tourlakis Theorem 4.2.2, transferred from plain PR
to ER and re-coded via Szudzik instead of prime-power
encoding: ER's closure under bounded primitive recursion
(§2.3.3) replaces plain PR's recursion-as-generator, and
Szudzik pairing replaces the prime-power encoding.  The
restriction to level-≤-2 inputs guarantees that the
recursion's output trace is bounded by an ER function, as
required for §2.3.3 to apply.

#### 2.3.2 Szudzik pairing in ER

The Szudzik elegant pairing

    ⟨x, y⟩ := if x < y then y² + x else x² + x + y

is in ER: it is built from `max`, `min`, comparison,
multiplication, and addition, all of which are elementary.
Its component projections $π_0, π_1$ are similarly
elementary (using integer square root, which is bounded by
the input and definable via bounded minimisation in ER).
Iterated pairing $\langle x_0, …, x_k \rangle$ for $k+1$
arguments is a left-fold of the binary pairing; each
projection $π_j$ is the corresponding sequence of left or
right components.  The project's `NatElegantPair` utility
already implements these constructions; the Phase 2
deliverable reuses them rather than defining new pairing
primitives.

#### 2.3.3 Bounded primitive recursion in ER

ER is *not* closed under unbounded primitive recursion:
unbounded primitive recursion of ER functions can produce
functions outside ER (the elementary functions are a strict
sub-class of the primitive recursive functions).  ER is
closed under *bounded* primitive recursion: given total
$h : ℕ^a → ℕ$ and $g : ℕ^{a+2} → ℕ$ in ER, and an
elementary bound $B : ℕ^{a+1} → ℕ$ such that the recursion's
result satisfies $f(x, \vec{y}) ≤ B(x, \vec{y})$, the
function

    f(0,    ȳ) = h(ȳ)
    f(x+1,  ȳ) = g(x, ȳ, f(x, ȳ))

is in ER.  This is the classical Kalmár result, reviewed in
the Grzegorczyk-hierarchy chapter (Exercise 4.2).  The
construction recovers $f(x, \vec{y})$ via bounded
minimisation:

    f(x, ȳ)  =  μ y ≤ B(x, ȳ).
                 PR-trace(h, g, x, ȳ)
                   matches y at step x

where `μ` is bounded minimisation, itself elementary.  The
project already provides `ERMor1.boundedSearch` in
`GebLean/Utilities/ERArith.lean` as a bounded-search
combinator; the bounded-minimisation construction needed
here is built from `boundedSearch` together with `bsum`,
which encodes the trace via Szudzik pairing.

In Lean we package this as a named composite

    ERMor1.boundedRec : ERMor1 a → ERMor1 (a+2)
                       → ERMor1 (a+1) → ERMor1 (a+1)

(taking `h`, `g`, and the bound `B` as inputs, returning
the recursion result), placed under
`GebLean/Utilities/ERPrimrec.lean` per the bottom-up
named-composite discipline.  The name `boundedRec` is used
in preference to `primrec` to keep the bounded character
explicit at every call site; using `primrec` alone would
falsely suggest closure under the unbounded schema.

The required bound $B$ for the §2.3.1 trace function exists
because every level-≤-2 K^sim morphism is bounded by an
elementary function (the majorisation lemma for ER); since
the trace `F(x, ȳ)` packs $k+1$ such bounded values via
Szudzik pairing, `F` itself is bounded by an elementary
function — which is exactly what §2.3.3 requires.  This
also pinpoints why §2.3.1 only applies at level ≤ 2: at
higher K^sim levels, the trace would be bounded by a
primitive-recursive but non-elementary function, putting it
outside ER.

#### 2.3.4 Interpretation-preservation lemma

  Lemma 2.3.4 (`kToER_interp`).
  For every f : KMor1 a and every environment v : Fin a → ℕ,

      (kToER f).interp v  =  f.interp v

The proof is by structural induction on f.  Each
constructor's case follows from the definition of `kToER`
on that constructor and the interpretation rules.  The
non-trivial induction step is `simrec`, where the
correctness of the Szudzik encoding-then-decoding is what
is being verified.

### 2.4 Backward translation `erToK`

The backward direction translates ER morphisms into K^sim
morphisms.  Each ER constructor maps to a named K^sim
composite.  The mapping table is:

| `ERMor1` constructor | K^sim target                          |
|----------------------|---------------------------------------|
| `zero`               | `KMor1.zero`                          |
| `succ`               | `KMor1.succ`                          |
| `proj i`             | `KMor1.proj i`                        |
| `sub`                | (built via §2.4.0 below)              |
| `comp f gs`          | `KMor1.comp (erToK f) (erToK ∘ gs)`   |
| `bsum f`             | (built via §2.4.1 below)              |
| `bprod f`            | (built via §2.4.2 below)              |

The atomic and `comp` cases are direct.  The `sub`, `bsum`,
and `bprod` cases require small construction.  `sub` is
straightforward (a level-≤-2 composite from `pred`); `bsum`
and `bprod` are where the central technical content lies.

#### 2.4.0 `sub` translation

Cut-off subtraction `sub : ℕ² → ℕ`,
$x \mathbin{\dot-} y = \max(0, x - y)$, is an atomic
generator in `ERMor1` but a composite in K^sim.  It is
defined from the predecessor function `pred` by

    sub(x, 0)    = x
    sub(x, y+1)  = pred(sub(x, y))

`pred` itself is a simrec at level 1 (a system-size-1 simrec
with base $0$ and step $g(z, p) = z$, producing the
function $\text{pred}(0) = 0$ and $\text{pred}(n+1) = n$).
The outer simrec defining `sub` has level
$\max(0, \text{level}(\text{pred})) + 1 = 2$, so the
translation lands directly in the K^sim_2 syntactic
subtype with no closure-theorem appeal needed.

#### 2.4.1 `bsum` translation

Given `f : ERMor1 (a+1)` representing
$f(i, \vec{y}) : ℕ^{a+1} → ℕ$, define

    Sf(z, ȳ) := Σ_{i ≤ z} f(i, ȳ)

via simultaneous primitive recursion of system-size 1:

    Sf(0,    ȳ) = f(0, ȳ)
    Sf(z+1,  ȳ) = Sf(z, ȳ) + f(z+1, ȳ)

Translating: define `bsumK : KMor1 (a+1) → KMor1 (a+1)`
on K^sim morphisms by the simrec constructor with `k = 0`,
output index `0`, base $h = $ erToK $\langle f \circ \text{cons}\,0 \rangle$,
and step $g = $ erToK $\langle \lambda z\, \vec{y}\, p.\
p + f(z+1, \vec{y}) \rangle$.

The base $h$ has level equal to the level of `erToK f`.
The step $g$ uses addition (level 1 in K^sim) and `f`
(level equal to `erToK f`); composed, $g$ has level
$\max(1, \text{level}(\text{erToK}\,f))$.  The simrec then
has syntactic level
$\max(1, \text{level}(\text{erToK}\,f)) + 1$.

For `f` translated from a level-≤-1 ER morphism (the only
case that arises in `erToK ∘ erToK`-free use), the
syntactic simrec level is 2.  However, `erToK` is applied
recursively to ER morphisms whose own `erToK` images may
have level 2.  In that case the naive bsumK construction
above produces a level-3 syntactic term.  Phase 2's
correctness therefore requires the following theorem:

  Theorem 2.4.A (bsum closure).
  For every quotient class ⟦f⟧ ∈ KSimMor 2 (a+1),
  the quotient class ⟦bsumK f⟧ also has a level-≤-2
  representative — i.e. ⟦bsumK f⟧ ∈ KSimMor 2 (a+1).

The theorem is proved as a corollary of the general
result that ER ⊆ K^sim_2 as function classes via URM
simulation (Tourlakis 2018 Corollary 0.1.0.44 transferred
to our K^sim).  The full construction is developed in
Appendix A §A.6 with §A.7 specialising to bsum.

#### 2.4.2 `bprod` translation

Bounded product is treated symmetrically with `+` replaced
by `*`.  Multiplication is at level 2 in K^sim, so the
naive simrec representation has syntactic level 3.

  Theorem 2.4.B (bprod closure).
  For every quotient class ⟦f⟧ ∈ KSimMor 2 (a+1),
  the quotient class ⟦bprodK f⟧ ∈ KSimMor 2 (a+1).

The proof is the symmetric corollary of the general URM
simulation result.  See Appendix A §A.6 with §A.7
specialising to bprod.

#### 2.4.3 Interpretation-preservation lemma

  Lemma 2.4.3 (`erToK_interp`).
  For every f : ERMor1 a and every environment v : Fin a → ℕ,

      (erToK f).interp v  =  f.interp v

By structural induction on f.

#### 2.4.4 Quotient-class level lemma

  Lemma 2.4.4 (`erToK_in_KSim2`).
  For every f : ERMor1 a, the quotient class
  ⟦erToK f⟧ has a level-≤-2 representative.

By structural induction on f, applying Theorems 2.4.A and
2.4.B at the `bsum` and `bprod` cases.

### 2.5 Round-trip identities

  Lemma 2.5.A (forward then backward).
  For every f : KMor1 a with level f ≤ 2,

      ⟦erToK (kToER f)⟧  =  ⟦f⟧  in KMor1.QuotCat.

Proof.  By Lemmas 2.3.4 and 2.4.3, both sides interpret to
the same Lean function.  Since the quotient is by
extensional equality, the classes coincide.

  Lemma 2.5.B (backward then forward).
  For every f : ERMor1 a,

      ⟦kToER (erToK f)⟧  =  ⟦f⟧  in ERMor1.QuotCat.

Symmetric.

### 2.6 Categorical packaging

Define the functors

    F : KSimMor 2  →  LawvereER.QuotCat
    F.obj a := a
    F.map ⟦f⟧ := ⟦kToER f⟧

    G : LawvereER.QuotCat  →  KSimMor 2
    G.obj a := a
    G.map ⟦f⟧ := ⟦erToK f⟧

Both maps are well-defined on quotients by Lemmas 2.3.4
and 2.4.3.  G's image lands in KSimMor 2 by Lemma 2.4.4.
Functoriality (preservation of identities and composition)
is direct from the per-constructor translations of `id`
and `comp`.

The natural isomorphisms F ∘ G ≃ id and G ∘ F ≃ id are
identities by Lemmas 2.5.A and 2.5.B, so F and G witness
an *isomorphism* of categories — the iso outcome
preferred over an `Equivalence` wherever achievable.

### 2.7 Worked examples

The following table records the K^sim level (syntactic, in
the sense of `level f`) of selected functions on each
side, for sanity-checking the design.  Levels marked with
`*` are syntactic levels of the *naive* simrec
construction; they collapse to the function-class level via
Theorems 2.4.A / 2.4.B.

| function       | K^sim form                | syn level   |
|----------------|---------------------------|-------------|
| `0`            | zero                      | 0           |
| `succ x`       | succ                      | 0           |
| `λx. x + k`    | comp of succ              | 0           |
| `x + y`        | simrec, base id, step succ| 1           |
| `pred`         | simrec on cases           | 1           |
| `x ∸ y`        | simrec using pred         | 2           |
| `x · y`        | simrec, step uses +       | 2           |
| `2^x`          | simrec, step uses doubling| 2           |
| `a^b`          | bounded-rec via §2.4      | 3* → 2      |
| `factorial(x)` | bounded-rec via §2.4      | 3* → 2      |

The `3* → 2` entries are exactly the cases where the
bounded-recursion-closure theorems (Theorems 2.4.A and
2.4.B and their generalizations) reduce a syntactic
level-3 term to a level-2 representative.  Worked Lean
proofs of the `3* → 2` collapse for `a^b` and
`factorial` are scheduled as part of the Phase 2
implementation plan; they exercise the closure theorems
on representative cases.

### 2.8 Open issues for the Phase-2 implementation

* (i) The bounded-recursion-closure theorems (Theorems
  2.4.A, 2.4.B, and their generalisations to arbitrary
  ER-bounded recursion) are the technical pivot of Phase 2.
  Their proofs rely on the majorisation lemma for ER and on
  Gödel-encoding tricks within ER.  The detailed proof
  outline is captured in the Phase-2 implementation plan
  but not transcribed in this design document.
* (ii) The categorical isomorphism (rather than mere
  equivalence) is contingent on the round-trip identities
  being literal equalities of quotient classes.  If a
  quotient-class equality turns out to require an explicit
  natural isomorphism (e.g. because of universe-handling
  artifacts), Phase 2 falls back to producing only an
  `Equivalence` instance.

## Phase 3 — ⋃_n K^sim_n ⊆ Primrec

Phase 3 establishes that every K^sim morphism, at any
depth, interprets to a primitive-recursive function in the
sense of `mathlib.Nat.Primrec`.  This validates the K^sim
syntax against the established notion of primitive
recursiveness and provides downstream consumers with a
direct route from a K^sim term to a `Nat.Primrec`
certificate.

### 3.1 Theorem statement

  Theorem 3.1 (Phase-3 deliverable).
  For every f : KMor1 a, there is a corresponding
  `Nat.Primrec` certificate witnessing that the function
  represented by f.interp is primitive-recursive.
  Concretely: a function `kToPrimrec : KMor1 a →
  Nat.Primrec`-shape such that the certificate's
  underlying ℕ-valued function agrees with f.interp under
  Szudzik-encoding of the input vector.

The converse direction `Primrec ⊆ ⋃_n K^sim_n` is *not* a
deliverable of this development.

### 3.2 Encoding the input vector

`mathlib.Nat.Primrec` certifies primitive-recursiveness of
unary functions ℕ → ℕ.  Multivariate K^sim morphisms
ℕ^a → ℕ are matched to unary functions via Szudzik
encoding of the input tuple: define
`encodeArgs : (Fin a → ℕ) → ℕ` as the iterated Szudzik
pairing of the components, and certify the unary function
`fun n => f.interp (decodeArgs a n)` as primitive-
recursive.  The encoding/decoding utilities are reused
from `NatElegantPair` (mathlib's Nat-pairing
infrastructure also suffices).

### 3.3 Translation `kToPrimrec`

The translation proceeds by structural induction on the
`KMor1` constructor:

| `KMor1` constructor | `Nat.Primrec` target           |
|---------------------|--------------------------------|
| `zero`              | `Nat.Primrec.zero`             |
| `succ`              | `Nat.Primrec.succ`             |
| `proj i`            | composition with Szudzik       |
|                     | projection `π_i ∘ decodeArgs`  |
| `comp f gs`         | `Nat.Primrec.comp` of the      |
|                     | recursively-translated terms   |
| `raise f`           | `kToPrimrec f`                 |
| `simrec i h g`      | (built via §3.4 below)         |

`raise` is metadata and does not affect the underlying
function; the translation drops it.  The atomic, comp, and
proj cases are direct.

### 3.4 simrec via Szudzik trace

The `simrec` case is the substantive content of Phase 3.
The construction is the same Hilbert–Bernays Gödel
encoding from §2.3.1, transferred from the ER setting to
the unrestricted Primrec setting.  The trace function

    F(x, ȳ) := ⟨f_0(x, ȳ), …, f_k(x, ȳ)⟩

is built using *unbounded* primitive recursion in
`Nat.Primrec` (which is closed under unbounded primitive
recursion, in contrast to ER).  The base case packs the
initial vector via Szudzik; the step case decodes,
applies the step functions, and re-packs.  Component
recovery is `π_i ∘ F`.

The construction does not use any level information — it
applies uniformly to all K^sim morphisms regardless of
depth.  This is what makes Phase 3 a unified statement
across the entire hierarchy ⋃_n K^sim_n.

### 3.5 Functor / certificate packaging

`kToPrimrec` is exposed in two forms:

* a direct certificate-producing function
  `kToPrimrec : KMor1 a → Nat.Primrec`-shape returning
  the primrec witness for the encoded unary function;
* a quotient-respecting predicate
  `KSimMor.IsPrimrec : KMor1.QuotCat.Hom a b → Prop`
  computing the disjunction over representatives.  Since
  the quotient is by extensional equality and `Nat.Primrec`
  closure depends only on the function, the predicate is
  well-defined on quotient classes.

A natural transformation
`KMor1.QuotCat ⥤ <Primrec-as-category>` packaging the
above is desirable as documentation but is not a Phase-3
deliverable; the translation function itself is the
primary artifact.

### 3.6 Tests

Following `LawvereERPrimrec`'s pattern,
`LawvereKSimPrimrec` includes a `test/` companion with:

* `#guard` checks that `kToPrimrec` produces certificates
  whose computed values agree with `KMor1.interp` for
  small inputs across the standard arithmetic functions
  defined in `GebLean/Utilities/KSimArith.lean` (the
  level-≤-2 set: `add`, `mult`, `exp`, `factorial`,
  `pred`, `monus`) and at least one level-≥-3 example
  (e.g. iterated tetration) to exercise the Szudzik
  trace at non-trivial depth.
* Plausible properties relating `kToPrimrec` output to
  the K^sim-side `interp` evaluation.

### 3.7 Open issues for the Phase-3 implementation

* (i) `mathlib`'s `Primrec` typeclass infrastructure
  (Carneiro 2019) wraps primrec witnesses in
  `Primcodable` instances.  Phase 3 needs to decide
  whether to produce raw `Nat.Primrec` witnesses (simpler)
  or `Primrec`-typeclass witnesses on encoded
  multivariate inputs (more idiomatic for downstream
  mathlib use).  The decision is recorded in the
  Phase-3 implementation plan.
* (ii) The Szudzik trace at `simrec` involves repeated
  encoding/decoding within the recursion step; performance
  is not a Phase-3 concern but the design plan should note
  that direct execution of the certificate may be slow on
  deep simrec terms.

## Open Questions

* Whether the equivalence in Phase 2 is achievable as an
  isomorphism of categories or only as an
  `Equivalence` instance.  Both are acceptable; isomorphism
  is the preferred outcome.
* The exact statement of Phase 1's depth-monotonicity
  packaging — whether `KMor1.atDepth` is a subtype, a
  proposition, or a separate inductive — to be settled in
  the Phase 1 implementation plan.

## References

### Primary sources

* Tourlakis, *Primitive Recursive Complexity Topics* (2018) —
  `.claude/docs/arithmetic-hierarchies/PR-complexity-topics.pdf`.
  Definition 0.1.0.7 (K^sim_n); §0.1.0.15 (constructive proof
  K^sim_n = L_n); §0.1.0.17 (worked examples per level).
* Meyer & Ritchie, *The Complexity of Loop Programs* (1967).
  L_n hierarchy, L_2 = ER, ⋃_n L_n = PR.  Available as
  `computational-complexity-program-structure-MeyerAndRitchie-67-ocr.rtf`
  in the references directory.
* Tourlakis, *Computability Notes* —
  `.claude/docs/arithmetic-hierarchies/tourlakis-Computability-Notes-ROOT.pdf`.
  Definition 10.2.7 (K^sim_n in larger context); Theorem 4.2.2
  (Hilbert–Bernays Gödel-encoding for simrec → single PR).

### Supporting sources

* Damnjanovic, *Elementary Functions and Loop Programs*
  (1994).  L_2^k refinement; bsum/bprod ↔ ELP translations.
  Available as `elementary-functions-and-loop-programs.pdf`
  in the references directory.
* Tourlakis, *Recursion Class Chapter 4* (Grzegorczyk
  hierarchy).  E^n hierarchy; Exercise 4.2 (closure of E^3
  under bounded simultaneous recursion).  Available as
  `grzegorczyk-hierarchy-recursion-class-chapter-4.pdf`
  in the references directory.
* Tourlakis, *Recursion Class Chapter 2* (Primitive
  Recursion).  PR foundations; worked construction of
  standard arithmetic functions.  Available as
  `primitive-recursion-recursion-class-chapter-2.pdf`
  in the references directory.

### Lean infrastructure

* `Mathlib.Computability.Primrec` — primitive-recursive
  function infrastructure (Carneiro, ITP 2019).  Phase 3
  target.
* `Mathlib.Computability.Partrec` — partial-recursive
  function infrastructure.  Background only.

### Project context

* `GebLean/LawvereER.lean`, `LawvereERInterp.lean`,
  `LawvereERQuot.lean`, `LawvereERPrimrec.lean` — the
  pattern that this development mirrors.
* `GebLean/LawvereGodelTTerm.lean` and related modules — a
  prior stratified-recursion attempt; expected to be
  retired once Phase 2 of this development lands.

### External context (consulted)

* PlanetMath, *Mutual recursion*:
  <https://planetmath.org/mutualrecursion>.
* PlanetMath, *Course-of-values recursion*:
  <https://planetmath.org/courseofvaluesrecursion>.
* Wikipedia, *LOOP (programming language)*:
  <https://en.wikipedia.org/wiki/LOOP_(programming_language)>.
* Wikipedia, *Grzegorczyk hierarchy*:
  <https://en.wikipedia.org/wiki/Grzegorczyk_hierarchy>.
* Wikipedia, *Primitive recursive function*:
  <https://en.wikipedia.org/wiki/Primitive_recursive_function>.
* Bauer, *Primitive recursive functions in Agda* (gist) —
  stylistic precedent for the arity-indexed inductive shape.

## Appendix A — Closure proofs via URM simulation

Theorems 2.4.A (`bsum` closure) and 2.4.B (`bprod` closure)
are corollaries of a stronger result: the entire ER class
embeds into K^sim_2 as a function class via URM simulation.
This appendix develops the construction in detail.

### A.0 Why a naive transcription fails

A structural recursion `erToK : ERMor1 → KMor1` that maps
each ER constructor to its naive K^sim composite produces,
for ER inputs whose `bsum` or `bprod` is applied to
level-≥-2 ER subexpressions, K^sim terms whose syntactic
level rises above 2.  The reason is structural: ER's `bsum`
and `bprod` are *generators* of ER, so they are at the same
level as their argument inside ER; in K^sim, they are *not*
generators — they must be expressed via `simrec`, which
adds one to the level under P2.  The level rule of K^sim
matches Tourlakis's K^sim_n hierarchy (Tourlakis 2018
§0.1.0.7) exactly; the structural mismatch is intrinsic to
the difference between ER's syntactic generators and
K^sim's.

The textbook proof of `E^{n+1} ⊆ K_n^sim` (Tourlakis 2018
Corollary 0.1.0.44) does *not* proceed by structural
transcription.  It proceeds via **URM simulation**: each
E^{n+1} function is computed by a URM (unlimited register
machine) running in time bounded by an Ackermann-style
function `A_n^r ∈ K_n^sim`; a fixed K_n^sim simulator,
constructed per-program by structural recursion on the
URM's instruction list, runs the URM for that bounded
number of steps and returns the output register.

This appendix transcribes that construction into our K^sim
formalism.  The composite is

    erToK e := λ x⃗.
      simulator(compile e)(A_2^r(max x⃗), encode_inputs(x⃗))

and lies in K_2^sim because composition is level-preserving
and each piece is in K_2^sim.

### A.1 Overview

The construction has four layers, each at K^sim level
within K_2^sim:

* **Compile** (§A.4): a Lean-side function
  `compile : ERMor1 a → URMProgram` producing a finite
  register-machine program implementing the ER expression's
  function.  This is metadata, not a K^sim term.
* **Simulate** (§A.3): a Lean-side function
  `simulate : URMProgram → KMor1 (1 + numRegs)` producing
  a K_2^sim simrec term.  The simrec has system size
  `numRegs + 1` (one component per register, plus the
  program counter); its step is a level-1 K^sim composite
  performing one URM transition.
* **Bound** (§A.5): a fixed K_2^sim term `A_2 ∈ KMor1 1`
  giving an exponential-tower bound on URM runtime as a
  function of input size.
* **Compose** (§A.6): assemble `erToK e` as a K^sim
  composition of the three pieces.

The simulator is *not* a single universal K^sim term — it
is built per-URM by structural recursion on the
program's finite instruction list.  The "universality" lies
in the construction being uniform: every URM yields its own
K_2^sim simulator via the same algorithm.

### A.2 The concrete URM

The abstract `RegisterMachine` structure in
`GebLean/Utilities/RegisterMachine.lean` already provides
the semantic backstop: states, registers, a transition
function, and `step` / `run` / `runReg` operations with
their reduction lemmas.  Phase 2 adds a concrete URM with
a finite instruction set:

    inductive URMInstr (r : ℕ) : Type
    | zeroReg  (i : Fin r)        : URMInstr r
    | incReg   (i : Fin r)        : URMInstr r
    | copyReg  (i j : Fin r)      : URMInstr r
    | condJump (i : Fin r) (t : ℕ) : URMInstr r
    | halt                          : URMInstr r

    structure URMProgram where
      numRegs       : ℕ
      instrs        : List (URMInstr numRegs)
      outputReg     : Fin numRegs

A URM program compiles to an abstract `RegisterMachine`
whose states are program counters (0 … instrs.length) and
whose transition function dispatches on the instruction at
the current PC: `zeroReg i` clears register i and advances
PC; `incReg i` increments register i and advances PC;
`copyReg i j` copies register i to register j and advances
PC; `condJump i t` branches to PC = t if register i is
zero, otherwise advances PC; `halt` is a self-loop.

The denotation of a URM program at runtime bound `n` is
`runReg (toRegisterMachine prog) initRegs n prog.outputReg`
— the value of the output register after running the
machine for `n` steps from the initial register vector.

### A.3 The K^sim simulator term

For a URM program `prog` with `r` registers and `s`
instructions, define

    simulate prog : KMor1 (1 + r)

(the recursion variable is the time bound, the parameters
are the initial register values) by a single `simrec` of
system size `r + 1` whose components track the program
counter and each register:

* **Base** (at recursion variable = 0): the PC is 0, each
  register is the corresponding parameter input.  Each
  base function is at K^sim level 0 (constants and
  projections).
* **Step** at recursion variable t+1: dispatch on the
  instruction at the previous PC, with each branch
  performing the corresponding register update.

The dispatch is a finite `switch`-tree.  `switch` is a
fixed K_1 function per Tourlakis §0.1.0.17 (6) — defined
as `simrec` on its first argument with base = `proj` of
the second argument and step = `proj` of the third
argument; level 1 with both base and step at level 0.
Crucially, `switch x y z` returns y if x = 0 and z
otherwise; the zero-test is built into `switch`'s
semantics.  No general equality function (which would
require `∸` and live at K_2^sim) is needed.

The dispatch on PC across `s` instructions is a nested
`switch` tree using *iterated `pred`* as the
discriminator — `pred^k(PC)` is 0 iff PC ≤ k, and
combined with sequential testing this isolates the
PC = k case at each level of nesting:

    step_dispatch(PC, regs) :=
      switch(PC,
        instruction-update-for-instr-0,
        switch(pred(PC),
          instruction-update-for-instr-1,
          switch(pred(pred(PC)),
            instruction-update-for-instr-2,
            ... )))

Each `switch` invocation is a composition with the K_1
`switch` primitive applied to a level-1 dispatcher
(iterated `pred` of `PC`, which is a comp of K_1 `pred`
with itself a fixed number of times) and level-≤-1
branches.  `pred` is K_1, and composition is
level-preserving, so iterated `pred` stays at level 1.
Each `switch` therefore composes K_1 with K_1 inputs and
remains at level 1.  The full dispatch tree is a
composition of these — also level 1.

Each instruction-update is a level-≤-1 K^sim composite:
`zeroReg i` writes 0 to register i (level 0); `incReg i`
applies `succ` (level 0); `copyReg i j` is a projection
(level 0); `condJump i t` uses one `switch` on the value
of register i (level 1); `halt` keeps PC unchanged (level
0).  The PC update for non-jump instructions is `succ`
(level 0); for `condJump`, it is a level-1 `switch`
choosing between the jump target and `succ PC_prev`.

The whole step is a composition of K_1 `switch` functions
applied to level-0 projections, constants, and `pred`
applications (themselves K_1).  Composition preserves
level, so the step is at K^sim level 1.  The simrec on
time with level-0 base and level-1 step has level
max(0, 1) + 1 = **2**.  Hence
`simulate prog ∈ KMor1.atDepth (1 + r) 2`.

The interpretation lemma (per P10):

    @[simp] theorem simulate_interp
        (prog : URMProgram)
        (ctx : Fin (1 + prog.numRegs) → ℕ) :
      (simulate prog).interp ctx
        = (run (toRegisterMachine prog)
                (fun i => ctx (Fin.succ i))
                (ctx 0)).2 prog.outputReg := by ...

stating that the K^sim simulator's interpretation equals
the abstract register machine's `runReg` at the given
time bound.  The proof is a structural induction on the
time bound, using `run_succ` from
`RegisterMachine.lean` and the per-instruction
correctness lemmas (one per `URMInstr` constructor).

### A.4 The compiler ER → URM

Define `compile : ERMor1 a → URMProgram` by structural
recursion on the ER expression.  The compiler reserves a
fixed pool of registers: `a` for input arguments, one for
the output, and a small bounded number for working storage
that grows with the ER expression's size.

**Register allocation pattern.**  The compiler maintains
two pieces of state during the structural recursion: a
"next free register" counter and a "next free PC" counter.
Each subexpression's compilation increments these as it
allocates working storage and emits instructions; on
return, the caller knows where the subexpression's output
sits and can plumb it into surrounding code.  Total
register count and instruction count are O(size of e) for
the ER input e.  The Lean implementation may use a state
monad or an explicit accumulator pattern; either is fine.

Each constructor compiles to a small instruction pattern:

* **`zero`**: write 0 to the output register; halt.
* **`succ`**: copy input to output; increment output; halt.
* **`proj i`**: copy input register `i` to output; halt.
* **`sub`**: copy arg 0 to output; loop arg 1 times, each
  iteration replacing output with `pred(output)`; halt.
  The `pred` is implemented via inner conditional decrement
  on a working register.
* **`comp f gs`**: for each `gs[i]`, invoke
  `compile gs[i]` with its result stored in temporary
  register `t_i`; then invoke `compile f` with input
  registers `t_0, …, t_{k-1}`; copy `f`'s result to
  output.  Subroutine invocation is by inlining with
  appropriate register renaming and PC offset.
* **`bsum f`**: initialise accumulator register to 0; loop
  over the bound register, at each step invoking
  `compile f` and adding its result to the accumulator;
  copy accumulator to output.
* **`bprod f`**: initialise accumulator to 1; loop over
  the bound register, at each step invoking `compile f`
  and multiplying the accumulator by its result; copy
  accumulator to output.  Multiplication is itself an
  inlined inner loop adding the multiplicand to a fresh
  result register a multiplier-many times.

**Subroutine inlining.**  Each "invoke `compile g`" in
the constructions above is implemented by *inlining*
`compile g`'s instruction list into the calling program.
The Lean implementation provides a helper

    URMProgram.inline
      (caller : URMProgram) (callee : URMProgram)
      (regMap : Fin callee.numRegs → Fin caller.numRegs)
      (pcOffset : ℕ) : URMProgram

which renames the callee's registers via `regMap` and
shifts its `condJump` targets by `pcOffset` so that the
callee's instructions can be appended to (or spliced
into) the caller's program with consistent semantics.

The "loop … times" idiom is implemented in URM via a
`condJump` testing a counter register and a `decrement`
sequence (using `pred` via repeated dec-test).  Subroutine
invocation (for `comp`, `bsum`, `bprod`) is implemented by
inlining the subroutine's instructions with appropriate
register renaming and PC offset.

The compiler's output is a finite list of URM instructions;
its size is polynomial in the size of the ER input.  For
each ER constructor, the compilation produces a small,
fixed pattern of instructions that operates on a bounded
set of registers.

The interpretation lemma:

    theorem compile_interp
        (e : ERMor1 a)
        (regs : Fin (compile e).numRegs → ℕ)
        (n : ℕ) (h : n ≥ runtimeBound e regs) :
      runReg (toRegisterMachine (compile e)) regs n
              (compile e).outputReg
        = e.interp (inputRegistersOf regs)

states that, given a runtime budget at least the URM's
runtime bound, the URM's output register holds the value
of the ER expression's interpretation.

### A.5 The runtime bound `A_2^e ∈ K_2^sim`

Throughout this subsection and §A.6–A.8, **`e` denotes
the input ER expression** being translated by `erToK` —
i.e. an arbitrary `e : ERMor1 a` for some arity `a`.
Quantities subscripted with `e` (such as `A_2^e`, `h_e`,
`p_e`) are constructed *from `e`'s syntactic structure*
during compilation; they are not universal constants.

The runtime of `compile e` on input `x⃗` is bounded by an
elementary function depending on `e`:

    runtimeBound e regs  ≤  tower h_e (max regs + p_e)

where `h_e` is a tower height and `p_e` is a polynomial
shift, both determined by `e`'s structure (specifically
by the depth of `bsum`/`bprod` nesting in `e` and by
auxiliary constants in `e`'s compilation).  For ER
inputs (which is the K_2^sim = E^3 case), the structure
of E^3 guarantees that every function is bounded by such
a tower.

The bound is *per-`e`*: for each ER input `e`, the K^sim
term

    A_2^e : KMor1 1
    A_2^e := λ x. tower h_e (x + p_e)

is a specific level-2 K^sim term.  The construction is a
Lean function `runtimeBoundK : ERMor1 a → KMor1 1` that
inspects `e`'s structure to compute the appropriate tower
height and polynomial shift, then assembles the K^sim
term from `2^x` (which is K_2^sim per §0.1.0.17 (c)),
addition with the constant shift, and iterated function
composition.

The crucial point: for *any* specific `e`, `tower h_e`
is a finite composition of `2^x` with itself (h_e times),
and composition is level-preserving in K^sim.  Therefore
`A_2^e` is at K^sim level 2 for every `e`.

There is no single uniform K^sim term that bounds runtimes
across *all* `e` — that would require a bound on `h_e`
valid for every ER expression, but `h_e` grows without
bound as `e`'s `bsum`/`bprod` nesting deepens.  This is the
Ackermann-hierarchy obstruction: in classical recursion
theory, the Ackermann function `A(n, x)` grows faster than
every primitive-recursive function, and the same shape of
obstruction applies inside ER (every individual ER
function is bounded by some `tower h x` at fixed `h`, but
no single `tower h x` bounds every ER function).
Consequently, `erToK` is a *Lean-level* uniform function on
ER expressions that produces a *K^sim term* whose specific
form (especially the bound `A_2^e`) varies with `e`.

The `ElementaryBound` structure already in
`GebLean/Utilities/RegisterMachine.lean` is the Lean-side
formalisation of this bound.  Its `tower`-based
`dominated` predicate is the technical statement; its
`ofExp` constructor builds the exponential case.  Phase 2
constructs `A_2` as a K^sim term and shows it dominates
the runtime of every `compile e` for `e : ERMor1 a` with
`a` and ER-size bounded by some constants.

### A.6 The composite `erToK`

For each ER expression `e : ERMor1 a`, the simulator
expects `1 + numRegs` inputs (one for the time bound
followed by one per register).  But `e`'s ER signature
provides only `a` inputs: the original ER arguments.  The
URM allocates additional registers for working storage
and the output, all of which start at 0 (their
"uninitialised" value).  The composition therefore wires
inputs as:

    inputs to simulator
      [0]                         := A_2^e ∘ inputMaxer
      [1] … [a]                   := proj_0 args, …,
                                       proj_{a-1} args
      [a + 1] … [numRegs]         := zero, zero, …, zero

The first `a + 1` slots use values supplied by `e`'s
arguments and the runtime bound; remaining slots are
zero-padded constants (level 0).  The full composition:

    erToK e : KMor1 a
    erToK e :=
      KMor1.comp
        (simulate (compile e))
        (KMorN-tuple of:
          A_2^e ∘ inputMaxer,     -- runtime bound (lvl 2)
          proj_0,                  -- input arg 0 (lvl 0)
          ⋮
          proj_{a-1},              -- input arg a-1 (lvl 0)
          zero,                    -- working register
          ⋮
          zero)                    -- output register init

where:

* `simulate (compile e)` is the K_2^sim simulator
  (system size `1 + (compile e).numRegs`, level 2);
* `A_2^e ∘ inputMaxer` is the per-`e` runtime bound
  applied to the maximum of the input arguments (level 2);
* the input-arg projections lift the original ER inputs
  into the URM register vector (level 0);
* trailing `zero` constants initialise working and output
  registers (level 0).

The composition is at K^sim level max(2, 2, 0) = 2.  Hence
`erToK e ∈ KMor1.atDepth a 2`.

The interpretation-preservation lemma:

    theorem erToK_interp
        (e : ERMor1 a)
        (v : Fin a → ℕ) :
      (erToK e).interp v = e.interp v := by ...

is proved by combining `simulate_interp` (the URM
simulator matches `runReg`) and `compile_interp` (the URM
output matches `e.interp`) at the runtime bound.

### A.7 Theorems 2.4.A and 2.4.B as corollaries

  Theorem 2.4.A (`bsum` closure).  Restated:
  For every ⟦f⟧ ∈ KSimMor 2 (a+1), the quotient class
  ⟦bsumK f⟧ ∈ KSimMor 2 (a+1).

Proof.  Pick a level-≤-2 representative f' of ⟦f⟧.  Apply
§A.6 to the ER expression `ERMor1.bsum (kToER f')`,
obtaining a K^sim term at level ≤ 2 whose interpretation
equals `bsum f` of the function `f'.interp`.  By interp
preservation of `kToER` and `erToK`, this term lies in
the same extensional-equality class as `bsumK f`. ∎

  Theorem 2.4.B (`bprod` closure).  Restated:
  For every ⟦f⟧ ∈ KSimMor 2 (a+1), the quotient class
  ⟦bprodK f⟧ ∈ KSimMor 2 (a+1).

Proof.  Symmetric, with `bprod` substituted for `bsum`
in the appeal to §A.6. ∎

### A.8 Generalisation to K_n^sim = E^{n+1}

The same URM-simulation construction works for any n ≥ 2,
giving K_n^sim = E^{n+1} as function classes (Tourlakis
2018 Corollary 0.1.0.44).  The pieces are:

* `simulate (compile e)` is at K_2^sim ⊆ K_n^sim for any
  n ≥ 2 (same simulator term; level inclusion lifts it).
* The per-`e` runtime bound `A_n^e` for `e ∈ E^{n+1}`
  uses a deeper tower of exponentials: the height
  `h_e` may grow with `e`'s `bsum`/`bprod` nesting at
  the new level.  For each *specific* `e ∈ E^{n+1}`,
  `A_n^e` is a finite composition of exponentiations
  (and additions of constants), so as a *fixed*
  K^sim term it remains at level 2.  However, because
  `h_e` can grow unboundedly with `e`'s structure, no
  single uniform K^sim term bounds every `e ∈ E^{n+1}` —
  the bounding is per-`e`.
* `erToK_n e ∈ KMor1.atDepth a 2` by composition (using
  the per-`e` bound).  Crucially, the *output level* in
  K^sim is 2 for every individual `e`, even for E^{n+1}
  inputs with n > 2: the function class K_2^sim already
  contains all of E^{n+1}'s individual functions.

The theorem K_n^sim = E^{n+1} holds at the *function
class* level: every E^{n+1} function has a K_n^sim
representative.  For the function class equality, having
K_2^sim representatives for each individual e is
sufficient (since K_2^sim ⊆ K_n^sim for n ≥ 2).  No
deeper-level construction is needed for the function
classes; what changes with n is the level at which the
bound is *uniformly* bounded as e varies (which is at
K_n^sim, not K_2^sim).

For n = 0 or 1, the URM-simulation technique does *not*
apply: the simulator's `switch`-tree dispatch and the
runtime-bound construction together require K_2^sim
machinery (specifically `2^x ∈ K_2^sim`).  K_0^sim and
K_1^sim are characterised directly: K_0^sim is the
constant-shift functions; K_1^sim is functions definable
by a single round of simultaneous PR over K_0^sim, e.g.
`+` and `pred`.

### A.9 Implementation note: file layout

The Lean implementation builds in layers, reusing the
abstract foundation already in
`GebLean/Utilities/RegisterMachine.lean`:

* **`GebLean/Utilities/RegisterMachine.lean`** (already
  present, 166 lines) — abstract `RegisterMachine`,
  `step`, `run`, `runReg`, `runFromConfig`, with reduction
  lemmas; `ElementaryBound` for runtime bounds.
  *No changes.*

* **`GebLean/Utilities/URMConcrete.lean`** (new) —
  `URMInstr` inductive (zero, inc, copy, condJump, halt);
  `URMProgram` structure (numRegs, instrs, outputReg);
  function `toRegisterMachine : URMProgram →
  RegisterMachine` linking concrete to abstract;
  `runProgram` shorthand.

* **`GebLean/Utilities/URMSimulator.lean`** (new) — the
  K^sim term construction `simulate : URMProgram →
  KMor1 (1 + numRegs)`; interp lemma (`simulate_interp`)
  relating to abstract `runReg`; level lemma stating
  `level (simulate prog) ≤ 2`.

* **`GebLean/Utilities/AckermannBound.lean`** (new, may be
  an extension to `Tower.lean`) — `ackermann_K_n :
  KMor1 1` for each n ≥ 2; `level (ackermann_K_n) ≤ n`;
  domination lemmas relating `ackermann_K_n` to `tower`.

* **`GebLean/LawvereKSimER.lean`** (new, the Phase 2
  module) — `compile : ERMor1 a → URMProgram` per §A.4;
  `runtimeBound : ERMor1 a → ℕ → ℕ` and its K^sim term
  realisation; `erToK : ERMor1 a → KMor1 a` per §A.6;
  interp-preservation `erToK_interp`; level lemma
  `level (erToK e) ≤ 2`; the equivalence packaging from
  §2.6.

The split keeps `RegisterMachine.lean` reusable for other
formalizations (e.g. Turing-machine-style developments)
while building URM-and-K^sim machinery in dedicated files.
The abstract structure and the concrete URM are linked but
separable; the K^sim simulator's correctness reduces to
the abstract structure's `runReg` semantics through
`simulate_interp`.

The Phase 2 implementation plan (a separate document
written via `superpowers:writing-plans`) sequences these
tasks per the dependency order: `URMConcrete`, then
`URMSimulator`, then `AckermannBound`, then the compiler
and `erToK` in `LawvereKSimER`.
