# LawvereGodelT typed-term design

A paper-faithful Lean 4 formalization of Beckmann-Weiermann's T\*
(Gödel's T fragment characterizing the elementary-recursive
functions), structured as a categorically-extensible nucleus with
a binary-tree-extended stratum, and equivalent to the existing
`LawvereERCat` (Wikipedia-style elementary recursive functions).

## Motivation

The previously-shipped `LawvereGodelTCat` (Stages A-D, ledger
through commit `c47c1f5a`) presents `GodelTMor1` as a fresh
inductive paralleling `ERMor1` with constructors
`zero` / `succ` / `pred` / `proj` / `sub` / `disc` / `bsum` /
`bprod` / `comp`.  This rebuild was the result of a 2026-04-21
design correction (commit `58922a2a`) that replaced a generic
base-typed `iter` constructor with `bsum` / `bprod`.  At the time
the correction was justified by observing that a generic
base-typed `iter step base` admits the tetration counterexample
`step = λx. 2^x`.

The correction was a misdiagnosis.  The constructor set obtained
from the correction is identical to `ERMor1`'s constructor set up
to the two ER-derivable extras (`pred`, `disc`).  The categorical
equivalence `LawvereGodelTCat ≌ LawvereERCat` proved by Stage C
is therefore trivial by construction, not by Beckmann-Weiermann's
theorem.

The actual Beckmann-Weiermann theorem (and the actual reason T\*
excludes tetration) lives in T\*'s type stratification together
with its restricted reduction calculus.  In particular, T\* is not
closed under translated λ-abstraction (Beckmann-Weiermann
2000, p. 477): `λx . . . I_ρ t^0 . . .` is not a valid T\* term
formation when `x` occurs in `t^0`.  This restriction is what
prevents constructing `step = λx . 2^x` as a T\* term and is the
load-bearing content of the equivalence with the
elementary-recursive functions.

This document presents a redesign that places the typed-term
representation at the categorical layer, preserves
Beckmann-Weiermann's typing discipline structurally, and
formalizes the full paper-faithful equivalence including
Lemma 16, strong normalization, Church-Rosser, and the
numeral-normal-form result.

## Non-negotiable interface contracts

The mathematical content is a fixed contract from the
Beckmann-Weiermann paper.  The Lean realization may evolve in
implementation strategy, but the following interfaces are
non-negotiable:

* `LawvereGodelTCat` (the nucleus): morphisms quotient
  `Reduces.equiv`-classes of `GodelTTerm S n .baseN` for
  `S = {.nat}`.  Constructor set of `GodelTTerm` exactly matches
  Beckmann-Weiermann's Definition 2 primitive set
  (`zero`, `succ`, `pred`, `K_στ`, `S_ρστ`, `disc_σ`, `iter`,
  `app`).
* `LawvereGodelTBTCat`: the same construction at
  `S = {.nat, .tree}`, extending the constructor set with
  `leaf`, `node`, and `treeIter`, all gated by `tree ∈ S`.
* `LawvereGodelTCat ≌ LawvereERCat`: a categorical equivalence
  realizing the Beckmann-Weiermann theorem.
* `LawvereGodelTBTCat ≌ LawvereGodelTCat`: a categorical
  equivalence realized by a Szudzik encoding/decoding written as
  nuclear morphisms (i.e. internally to the nucleus).  This
  equivalence is demonstrative; client implementations are free
  to render binary trees natively.

## Modularity architecture

The data structures are parameterized by a `Set GodelTBase`
selecting which base types are available.  This admits the
nucleus and the tree extension as specializations of a single
parametric framework; the substitution / reduction / Lemma 16 /
strong normalization / Church-Rosser machinery is proven once
parametrically and instantiated at each setting.  This is
"data-types-à-la-carte"-flavored modularity expressed inside
Lean's standard inductive-types framework, without requiring
polynomial-functor fixpoints.

Adding a base type later (for example a labeled-tree or a stream
type) consists of: extending `GodelTBase`; adding new
constructors gated by membership of the new base in `S`;
extending Lemma 16's structural induction with cases for the new
constructors.  The existing nucleus and binary-tree-extended
proofs are unchanged.

## Data structures

### Base types and types

```lean
inductive GodelTBase : Type
  | nat
  | tree

inductive GodelTType (S : Set GodelTBase) : Type
  | base (b : GodelTBase) (h : b ∈ S) : GodelTType S
  | arrow : GodelTType S → GodelTType S → GodelTType S
```

### Terms

Terms are indexed by an arity `n : ℕ` (the number of base-typed
free variables) and a type `σ : GodelTType S`.  Free variables
are base-typed only and indexed by `Fin n`.  Higher-typed terms
are always closed (built from the K/S/disc/iter combinators) —
there is no λ-abstraction at the term level.

```lean
inductive GodelTTerm (S : Set GodelTBase) :
    ℕ → GodelTType S → Type
  | var {n : ℕ} (i : Fin n)
      : GodelTTerm S n (.base .nat _)
  | app {n : ℕ} {σ τ : GodelTType S}
      (f : GodelTTerm S n (.arrow σ τ))
      (a : GodelTTerm S n σ)
      : GodelTTerm S n τ
  -- ℕ-side primitives.  Each is an arity-0 closed atom whose
  -- type encodes its arity via repeated `.arrow`.
  | zero : GodelTTerm S 0 (.base .nat _)
  | succ : GodelTTerm S 0 (.arrow (.base .nat _) (.base .nat _))
  | pred : GodelTTerm S 0 (.arrow (.base .nat _) (.base .nat _))
  | K (σ τ : GodelTType S)
      : GodelTTerm S 0 (.arrow σ (.arrow τ σ))
  | S_comb (ρ σ τ : GodelTType S)
      : GodelTTerm S 0
          (.arrow (.arrow ρ (.arrow σ τ))
            (.arrow (.arrow ρ σ) (.arrow ρ τ)))
  | disc (σ : GodelTType S)
      : GodelTTerm S 0
          (.arrow (.base .nat _) (.arrow σ (.arrow σ σ)))
  | iter
      : GodelTTerm S 0
          (.arrow (.base .nat _)
            (.arrow (.arrow (.base .nat _) (.base .nat _))
              (.arrow (.base .nat _) (.base .nat _))))
  -- Tree primitives, gated by `tree ∈ S`.
  | leaf (h : .tree ∈ S)
      : GodelTTerm S 0 (.base .tree h)
  | node (h : .tree ∈ S)
      : GodelTTerm S 0
          (.arrow (.base .tree h)
            (.arrow (.base .tree h) (.base .tree h)))
  | treeIter (h : .tree ∈ S) (σ : GodelTType S)
      : GodelTTerm S 0
          (.arrow (.base .tree h)
            (.arrow σ (.arrow (.arrow σ (.arrow σ σ)) σ)))
```

The membership proofs in `.base .nat _` are inhabitants of a
fixed assumption that `.nat ∈ S` for every `S` we consider; we
package this as a class to keep terms readable.  In particular
the nucleus and binary-tree-extended specializations both
guarantee `.nat ∈ S`.

### Specializations

```lean
abbrev GodelTNucleusType (n : ℕ) := GodelTType {GodelTBase.nat}
abbrev GodelTNucleus (n : ℕ) (σ : GodelTNucleusType) :=
  GodelTTerm {GodelTBase.nat} n σ

abbrev GodelTBTType :=
  GodelTType {GodelTBase.nat, GodelTBase.tree}
abbrev GodelTBTTerm (n : ℕ) (σ : GodelTBTType) :=
  GodelTTerm {GodelTBase.nat, GodelTBase.tree} n σ

abbrev GodelTMor1 (n : ℕ) :=
  GodelTNucleus n (.base GodelTBase.nat ⟨⟩)
```

A client application of `LawvereGodelTBTCat` operates on
`GodelTBTTerm`-flavor morphisms; arities are pairs `(n_nat,
n_tree)` accommodating both kinds of free variables.  The
`Fin n_nat + Fin n_tree` view of variables is encoded into the
single-arity `GodelTTerm`'s `Fin (n_nat + n_tree)` parameter
together with a conventional split of the index space.  Details
follow in the categorical-structure section.

## Substitution and interpretation

Substitution is a structural recursion over `GodelTTerm` taking
a map `Fin n → GodelTTerm S m (.base .nat _)` and producing the
substituted term.  No binders, no capture.

```lean
def GodelTTerm.subst {S} {n m : ℕ} :
    {σ : GodelTType S} →
    (Fin n → GodelTTerm S m (.base .nat _)) →
    GodelTTerm S n σ → GodelTTerm S m σ
  | _, ε, .var i        => ε i
  | _, ε, .app f a      => .app (f.subst ε) (a.subst ε)
  | _, _, .zero         => .zero
  | _, _, .succ         => .succ
  | _, _, .pred         => .pred
  | _, _, .K σ τ        => .K σ τ
  | _, _, .S_comb ρ σ τ => .S_comb ρ σ τ
  | _, _, .disc σ       => .disc σ
  | _, _, .iter         => .iter
  | _, _, .leaf h       => .leaf h
  | _, _, .node h       => .node h
  | _, _, .treeIter h σ => .treeIter h σ
```

Standard interpretation:

```lean
def GodelTBase.carrier : GodelTBase → Type
  | .nat => ℕ
  | .tree => GebLean.BTL  -- existing unlabeled binary tree

def GodelTType.interp : {S : Set GodelTBase} → GodelTType S → Type
  | _, .base b _ => b.carrier
  | _, .arrow σ τ => σ.interp → τ.interp

def GodelTTerm.interp : {S : Set GodelTBase} → {n : ℕ} →
    {σ : GodelTType S} → GodelTTerm S n σ →
    (Fin n → ℕ) → σ.interp
  -- one case per constructor matching its standard semantics
```

Two structural identities:

```lean
theorem GodelTTerm.interp_subst {S} {n m σ}
    (ε : Fin n → GodelTTerm S m (.base .nat _))
    (t : GodelTTerm S n σ) (env : Fin m → ℕ) :
    (t.subst ε).interp env =
      t.interp (fun i => (ε i).interp env)
```

```lean
theorem GodelTTerm.subst_var {S n σ} (t : GodelTTerm S n σ) :
    t.subst (fun i => .var i) = t
```

## Reduction relation

The reduction relation `▷` is an inductive `Prop` indexed by
`GodelTTerm S n σ`, with one constructor per Beckmann-Weiermann
Definition 4 reduction rule plus congruence rules.

```lean
inductive GodelTTerm.Reduces {S n} :
    {σ : GodelTType S} →
    GodelTTerm S n σ → GodelTTerm S n σ → Prop
  | redP_zero    : Reduces (.app .pred .zero) .zero
  | redP_succ t  : Reduces (.app .pred (.app .succ t)) t
  | redK σ τ a b : Reduces (.app (.app (.K σ τ) a) b) a
  | redS ρ σ τ f g x :
      Reduces (.app (.app (.app (.S_comb ρ σ τ) f) g) x)
        (.app (.app f x) (.app g x))
  | redDisc_zero σ a b :
      Reduces (.app (.app (.app (.disc σ) .zero) a) b) a
  | redDisc_succ σ t a b :
      Reduces
        (.app (.app (.app (.disc σ) (.app .succ t)) a) b) b
  | redIter_zero a b :
      Reduces (.app (.app (.app .iter .zero) a) b) b
  | redIter_succ t a b :
      Reduces (.app (.app (.app .iter (.app .succ t)) a) b)
        (.app (.app a t) (.app (.app (.app .iter t) a) b))
  -- tree analogues for treeIter when tree ∈ S
  | redTreeIter_leaf h σ a b :
      Reduces (.app (.app (.app (.treeIter h σ)
        (.leaf h)) a) b) a
  | redTreeIter_node h σ l r a b :
      Reduces (.app (.app (.app (.treeIter h σ)
        (.app (.app (.node h) l) r)) a) b)
        (.app (.app b
          (.app (.app (.app (.treeIter h σ) l) a) b))
          (.app (.app (.app (.treeIter h σ) r) a) b))
  -- congruence rules
  | redApp_left  {σ τ} {f g : GodelTTerm S n (.arrow σ τ)}
      (h : Reduces f g) (a : GodelTTerm S n σ) :
      Reduces (.app f a) (.app g a)
  | redApp_right {σ τ} (f : GodelTTerm S n (.arrow σ τ))
      {a b : GodelTTerm S n σ} (h : Reduces a b) :
      Reduces (.app f a) (.app f b)
```

`▷*` is the reflexive-transitive closure; `≈` is the
equivalence (symmetric-transitive-reflexive) closure.

Soundness: `Reduces.interp_invariance`:

```lean
theorem GodelTTerm.Reduces.interp_invariance {S n σ}
    {t s : GodelTTerm S n σ} (h : t.Reduces s)
    (env : Fin n → ℕ) :
    t.interp env = s.interp env
```

By induction on `h`'s constructors.  Each base-rule case is an
unfolding equation against `interp`'s definition.

## Mathematical content

### Tower bound (paper-faithful Lemma 16)

Per Beckmann-Weiermann Definitions 7-8, p. 480:

* `g : GodelTType S → ℕ`: type level.  `g (.base _) = 0`;
  `g (.arrow σ τ) = max (g σ + 1) (g τ)`.
* `[ ]_i : GodelTTerm S n σ → ℕ` for each `i ≤ g σ`: the
  level-i value associated to a term.  Atomic constructors take
  the constants from Definition 8; `app`-of-non-iter uses the
  multiplicative formula
  `[a^{στ} b^σ]_i := 2^{[a^{στ}b^σ]_{i+1}} * ([a^{στ}]_i + [b^σ]_i)`;
  iter's level-1 case takes a `+1` from rule 11.
* `G : GodelTTerm S n σ → ℕ`: maximum type level appearing as a
  sub-term.
* `d : GodelTTerm S n σ → ℕ`: iter-nesting depth.
* `lh : GodelTTerm S n σ → ℕ`: term tree size (constants and
  variables count as 1; `app` adds the sub-sizes plus 1).

Lemma 16 (Beckmann-Weiermann, p. 484):

```lean
theorem GodelTTerm.lemma_sixteen {S n}
    (t : GodelTTerm S n σ) (i : ℕ) (hi : i ≤ g σ) :
    t.bracketLevel i ≤
      tower ((G t + 1) * d t + G t + 1 - i)
            ((G t + 1) * d t + G t + 1 - i + 2 * lh t)
```

By structural induction on `t` following Beckmann-Weiermann
Lemmas 5-15.  Tree primitives appear as additional cases gated
by `tree ∈ S`.  Lemma 17 (substitution of numerals into
variables) is a corollary: under `t.subst ε` where `ε i = numeral
m_i`, `lh (t.subst ε) ≤ lh t + Σ m_i` and the bound grows
linearly in inputs.

### Strong normalization

Corollary of Lemma 16 + a strict-decrease lemma (Lemma 13 in the
paper):

```lean
theorem GodelTTerm.Reduces.bracketLevel_strict {S n σ}
    {t s : GodelTTerm S n σ} (h : t.Reduces s) :
    s.bracketLevel 0 < t.bracketLevel 0
```

Combined with Lemma 16, every reduction sequence from a fixed
term has length bounded by `tower ((G t + 1) * d t + G t + 1)
((G t + 1) * d t + G t + 1 + 2 * lh t)`, hence is finite.
Strong normalization yields a total `normalize : GodelTTerm S n
σ → GodelTTerm S n σ` returning the unique normal form.

### Confluence

Beckmann-Weiermann Lemma 1.2.  Proven by the Tait-Martin-Löf
parallel-reduction technique: define a parallel reduction
`▷ₚ : GodelTTerm S n σ → GodelTTerm S n σ → Prop` admitting all
single redexes simultaneously; prove the diamond property
`t ▷ₚ s₁` and `t ▷ₚ s₂` imply existence of common `s` with
`s₁ ▷ₚ s` and `s₂ ▷ₚ s`; relate `▷ₚ` and `▷*`.  Standard.

### Numeral normal form

For `S` containing `.nat`: every `t : GodelTTerm S 0 (.base .nat
_)` in normal form equals `numeral n` for some `n : ℕ`, where
`numeral n = .app .succ (.app .succ . . . (.app .succ .zero))` is
n applications of `succ` to `zero`.  Beckmann-Weiermann
Lemma 1.3.  Proven by induction on the term structure of normal
forms: applications cannot have constants whose reduction rules
match in the head position; the only normal head form at base
type is `succ ∘ . . . ∘ succ ∘ zero`.  Tree analogue: closed
normal-form `tree`-typed terms are tree-numerals built from
`leaf` and `node` only.

### Completeness of `≈` for extensional equality

Substantive consequence of strong normalization + confluence +
numeral normal form: for closed base-typed terms,

```lean
theorem GodelTTerm.equiv_iff_interp_eq_closed {S}
    [hN : .nat ∈ S]
    (t s : GodelTTerm S 0 (.base .nat _)) :
    t ≈ s ↔ t.interp Fin.elim0 = s.interp Fin.elim0
```

For open base-typed terms, Beckmann-Weiermann Definition 6 +
Section 4: the substitution-of-numerals technique extends
completeness to the open case.

## Equivalence functors

### Nucleus ≌ LawvereERCat

Forward `erToGodelT : ERMor1 n → GodelTNucleus n .baseN`: each
`ERMor1` constructor maps to a specific T\* derived term;
composition translates via `GodelTTerm.subst`.  Each derived
def lives in `Utilities/GodelTERTranslate.lean` with its own
`@[simp] interp_*` lemma.

```lean
def ERMor1.toGodelT : ERMor1 n → GodelTNucleus n .baseN
  | .zero    => .zero
  | .succ    => composedSucc  -- .app .succ (.var 0) etc.
  | .proj i  => .var i
  | .sub     => subT  -- iterated pred derived term
  | .bsum f  => bsumT f.toGodelT
  | .bprod f => bprodT f.toGodelT
  | .comp f g => f.toGodelT.subst (fun i => (g i).toGodelT)
```

Back `godelTToER : GodelTNucleus n .baseN → ERMor1 n`: a
logical-relations interpretation into ER expressions.  Define

```lean
def GodelTRep : {S : Set GodelTBase} → GodelTType S → ℕ → Type
  | _, .base .nat _, n => ERMor1 n
  | _, .arrow σ τ, n => GodelTRep σ n → GodelTRep τ n
```

and translate each constructor of `GodelTNucleus n σ` to a
`GodelTRep σ n`.  The `iter` case uses
`ERMor1.iterT` (already in the codebase from Task E.2,
commit `4346b496`) with adequacy supplied by Lemma 16.

Both directions extend componentwise to tuples; both descend
through the `≈`-quotient on the GodelT side and the
extensional-equality quotient on the ER side via the
completeness theorem.  Round-trip identities at the term level
exhibit `≈`-chains in the nucleus and ext-eq on the ER side.

### BT ≌ Nucleus via Szudzik

Two ingredients written as nuclear morphisms (i.e. inside
`GodelTNucleus`):

* `treeCode : GodelTNucleus 1 .baseN`: encodes a binary tree
  presented as an integer code into a single ℕ.  Built from
  Szudzik pairing primitives.
* `treeDecode : GodelTNucleus 1 .baseN`: inverse encoding.

The functor `btToNucleus : LawvereGodelTBTCat →
LawvereGodelTCat` operates on each morphism by:

* Replacing each tree slot in the arity by a single ℕ slot
  carrying the encoded tree.
* Replacing each `leaf` / `node` / `treeIter` constructor with
  its Szudzik-coded analogue defined in pure nucleus.

The functor `nucleusToBT : LawvereGodelTCat →
LawvereGodelTBTCat` is the inclusion: every nuclear morphism
lifts to a binary-tree-extended morphism by re-interpreting at
`S = {.nat, .tree}`.  Round-trip identities:

* `nucleusToBT ∘ btToNucleus ≅ id` exhibits an `≈`-chain
  reducing `treeDecode (treeCode τ)` to `τ` for tree-typed
  morphisms.
* `btToNucleus ∘ nucleusToBT = id` literally — both directions
  are inclusions.

The equivalence is demonstrative: implementations of
`LawvereGodelTBTCat` are free to render binary trees natively
without going through Szudzik internally.

## Stages

Each stage commits cleanly with passing build and tests.

* **α — Cleanup.**  Mark superseded the 2026-04-19 design and the
  2026-04-21 stages-E-J plan.  Tear down the existing
  fresh-inductive `GodelTMor1` and its scaffolding in
  `LawvereGodelTQuot.lean`; the existing `LawvereGodelT.lean`
  retains its `GodelTType` / `GodelTTerm` skeleton with the
  constructors revised per this design.  Update workstream
  tracker.
* **β — Scaffolding.**  `GodelTBase`, `GodelTType S`,
  `GodelTTerm S n σ`, `interp`, `subst`, `interp_subst`.
  Per-constructor simp lemmas.
* **γ — Reduction relation.**  `Reduces` (`▷`), `Reduces.star`
  (`▷*`), `Reduces.equiv` (`≈`).  Soundness
  `Reduces.interp_invariance`.  Tree rules gated by
  `.tree ∈ S`.
* **δ — Tower-bound infrastructure.**  `g`, `[ ]_i`, `G`, `d`,
  `lh`.  Lemma 16's full paper-faithful proof following
  Beckmann-Weiermann Lemmas 5-15.  Substitution Lemma 17.
  Largest single body of proof work.
* **ε — Strong normalization.**  Strict-decrease of `[ ]_0`
  under `▷`.  Total `normalize` returning the unique normal
  form.
* **ζ — Confluence.**  Tait-Martin-Löf parallel-reduction proof.
  Diamond property and relation to `▷*`.
* **η — Numeral normal form.**  For closed base-typed terms.
  Completeness corollary `t ≈ s ↔ t.interp = s.interp` on
  closed and open base-typed terms.
* **θ — Categorical structure.**  `GodelTMor1`, tuples,
  `≈`-equivalence setoid, quotient, `Category LawvereGodelTCat`,
  `HasChosenFiniteProducts`.
* **ι — Equivalence Nucleus ≌ LawvereERCat.**  `erToGodelT`,
  `godelTToER`, tuple lifts, quotient lifts, equivalence
  functors + units/counits.  Tests covering sample programs
  (factorial, exponential).
* **κ — Binary-tree extension.**  Specialize at
  `S = {.nat, .tree}`.  Extended `interp` / `subst` / `▷` /
  Lemma 16 / SN / completeness with tree primitive cases.
  `LawvereGodelTBTCat` setup.
* **λ — Szudzik-encoded equivalence BT ≌ Nucleus.**  `treeCode`,
  `treeDecode`, `btToNucleus`, `nucleusToBT`.  Equivalence
  proof.
* **μ — Cross-stage tests.**  Property-based tests on tree
  round-trips, sample tree-recursive functions (size, depth,
  mirror, fold).
* **ν — Programmer ergonomics (deferred polish).**  Adapted
  bracket abstraction utility for the variable-aware
  representation.

## Existing code disposition

Survives intact:

* All of `LawvereERCat` infrastructure and `Utilities/ERArith.lean`
  (including `ERMor1.iterT` / `iterAutoBoundExpr` / `natN` from
  Task E.2, commit `4346b496`).
* `Utilities/Tower.lean`, `LawvereERBoundComputable.lean`,
  `Utilities/SzudzikSeq.lean`, `Utilities/RegisterMachine.lean`.
* The structural-measures file `Utilities/GodelTBound.lean`
  (Task E.1, commit `215b4a25`) survives with its definitions
  re-targeted to the new typed `GodelTTerm S n σ` signature;
  these become inputs to `d` and `lh` of Lemma 16.

Adapts to the new representation:

* `LawvereGodelT.lean`: extend `GodelTTerm` per this design.
  The existing `GodelTPure` predicate either drops or
  reformulates as "no iter constructor in any sub-term" against
  the `S`-parameterized form.
* `Utilities/GodelTBracket.lean`: rebuilt for the
  variable-aware terms in stage ν.

Deleted:

* The fresh-inductive `GodelTMor1` and its tuple / quotient /
  category scaffolding in `LawvereGodelTQuot.lean`.
* The previous `LawvereGodelTERCatEquiv.lean`'s `toER` and
  `toGodelT` definitions and their tuple / quotient lifts.
* The previous `LawvereGodelTInterp.lean`'s functor (rebuilt at
  stage θ).

## Testing strategy

`#guard`-style assertions at each stage:

* β-γ: substitution and interpretation produce the expected ℕ
  values for sample base-typed nucleus terms (factorial,
  exponential).  Reduction relation closes specified redex
  patterns.
* δ-ζ: Lemma 16 instances match hand-computed bounds for sample
  terms; `normalize` returns expected normal forms.
* η: open-term completeness on small examples.
* ι: round-trip from `LawvereERCat` morphisms back to themselves
  through `erToGodelT ∘ godelTToER` returns extensionally-equal
  results.
* κ-λ: BT round-trips (tree-encode-decode) and sample
  tree-recursive functions (size, depth, mirror, fold).

Plausible-style property-based tests where natural (random
trees up to depth 5).

## Mathlib upstreaming opportunities

The mathematical content of stages δ-η is independently
worthwhile.  Mathlib does not contain a typed-T\*-style fragment
of Gödel's T, the Howard-Schütte tower-of-twos strong
normalization technique, or a Kalmár-elementary characterization
beyond `Mathlib.Computability.Primrec`.  Candidate-for-upstream
files include:

* The `GodelTTerm` term/type infrastructure as a typed CL
  formalization.
* Lemma 16's tower bound as
  `Mathlib.Computability.Elementary.TowerBound`.
* The categorical Lawvere theory of ER as
  `Mathlib.CategoryTheory.ElementaryRecursive`.
* The Szudzik-coded tree extension as a separate file.

Each is self-contained and references only existing mathlib
infrastructure.  Earmark candidate files with a docstring noting
upstream candidacy.

## Decision log

The design choices recorded here are derived from a 2026-04-25
brainstorming session.  The questions and the chosen options:

* Q1.  Free-variable representation.  Option: base-typed-only
  `var (i : Fin n) : GodelTTerm S n (.base .nat _)`.  Higher-typed
  terms always closed.  Matches Beckmann-Weiermann Definition 6
  exactly.
* Q2.  Existing `GodelTTerm` reorganization.  Option: replace
  outright; extend with arity index and `var` constructor.
* Q3.  Constructor set for the nucleus.  Option: pure rebuild on
  Beckmann-Weiermann's Definition 2 primitives.  No
  `sub` / `bsum` / `bprod` / `proj` constructors; these live in
  `Utilities/GodelTERTranslate.lean` as derived defs used by
  `erToGodelT`.
* Q4.  Substitution / composition.  Option: direct structural
  recursion `GodelTTerm.subst`.  No binders ⇒ no capture.
* Q5.  `toER` strategy.  Option: logical-relations interpretation
  via `GodelTRep`.  The `iter` case uses `ERMor1.iterT` with
  adequacy from Lemma 16.
* Q6.  Quotient relation and Lemma 16 location.  Option:
  paper-faithful Lemma 16 + Church-Rosser + numeral normal form +
  completeness; quotient by `≈` (the equivalence closure of
  `▷`).  Reasoning: extensional equality involves universal
  quantification over Lean function types and is therefore
  metalogical; `≈` is purely syntactic and admits an
  ER-internal-implementable normalization algorithm derivable
  from Lemma 16's bounds.  This choice makes
  `LawvereGodelTCat`'s categorical equality directly checkable by
  an internal type-checker, supporting the longer-term goal of
  formalizing the elementary-recursive function category internal
  to itself.
* Q7.  Tree extension.  Option: trees as a first-class base type
  added to `GodelTType` with `tree`-gated constructors.  Type
  stratification + reduction + Lemma 16 + Church-Rosser extend
  uniformly.
* Q8.  Modularity architecture.  Option: signature-parameterized
  inductives over `Set GodelTBase`, with each base type's
  primitives gated by membership in `S`.  Single parametric
  framework, two specializations.  Forward-compatible with later
  refactoring to polynomial-functor fixpoints if desired.
