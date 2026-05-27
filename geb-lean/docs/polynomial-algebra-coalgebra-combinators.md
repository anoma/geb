# Polynomial Algebra/Coalgebra Combinators

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Existing Infrastructure](#existing-infrastructure)
- [G. Fixed Points as Chain (Co)limits](#g-fixed-points-as-chain-colimits)
  - [G: References](#g-references)
  - [G: Mathematical Background](#g-mathematical-background)
    - [The iteration chain](#the-iteration-chain)
    - [Directed and filtered (co)limits](#directed-and-filtered-colimits)
    - [Preservation consequences](#preservation-consequences)
  - [G: Relation to Our Codebase](#g-relation-to-our-codebase)
  - [G: Mathlib Infrastructure](#g-mathlib-infrastructure)
  - [G: Proposals](#g-proposals)
- [A. Colimits for Polynomial Algebras](#a-colimits-for-polynomial-algebras)
  - [A: References](#a-references)
  - [A: Mathematical Background](#a-mathematical-background)
    - [Limits (all polynomial functors)](#limits-all-polynomial-functors)
    - [Beck coequalizer (all polynomial functors)](#beck-coequalizer-all-polynomial-functors)
    - [Filtered colimit creation (finitary only)](#filtered-colimit-creation-finitary-only)
    - [Linton's theorem (cocompleteness from parts)](#lintons-theorem-cocompleteness-from-parts)
    - [Summary](#summary)
  - [A: Finitariness of Polynomial Functors](#a-finitariness-of-polynomial-functors)
  - [A: Application to Our Setting](#a-application-to-our-setting)
    - [Finitariness of the free monad (finitary only)](#finitariness-of-the-free-monad-finitary-only)
  - [A: Mathlib Infrastructure](#a-mathlib-infrastructure)
  - [A: Proposals](#a-proposals)
- [H. Connected Limit Preservation](#h-connected-limit-preservation)
  - [H: References](#h-references)
  - [H: Mathematical Background](#h-mathematical-background)
    - [Products preserve connected limits (all functors)](#products-preserve-connected-limits-all-functors)
    - [Coproducts preserve connected limits (extensive)](#coproducts-preserve-connected-limits-extensive)
    - [Polynomial functors preserve connected limits](#polynomial-functors-preserve-connected-limits)
    - [Consequences for our setting](#consequences-for-our-setting)
  - [H: Mathlib Infrastructure](#h-mathlib-infrastructure)
  - [H: Proposals](#h-proposals)
- [B. The Algebra-Coalgebra-Presheaf Triangle](#b-the-algebra-coalgebra-presheaf-triangle)
  - [B: References](#b-references)
  - [B: Mathematical Background](#b-mathematical-background)
  - [B: Relation to Our Codebase](#b-relation-to-our-codebase)
  - [B: Proposals](#b-proposals)
- [C. Distributive Laws and Bialgebras](#c-distributive-laws-and-bialgebras)
  - [C: References](#c-references)
  - [C: Mathematical Background](#c-mathematical-background)
  - [C: Mathlib Status](#c-mathlib-status)
  - [C: Proposals](#c-proposals)
- [D. Interaction Laws ("Pattern Runs on Matter")](#d-interaction-laws-pattern-runs-on-matter)
  - [D: References](#d-references)
  - [D: Mathematical Background](#d-mathematical-background)
  - [D: Relation to Our Codebase](#d-relation-to-our-codebase)
  - [D: Proposals](#d-proposals)
- [E. Operational Semantics via Abstract GSOS](#e-operational-semantics-via-abstract-gsos)
  - [E: References](#e-references)
  - [E: Mathematical Background](#e-mathematical-background)
  - [E: Relation to Our Codebase](#e-relation-to-our-codebase)
  - [E: Proposals](#e-proposals)
- [F. Stone Topology and Second Topos](#f-stone-topology-and-second-topos)
  - [F: References](#f-references)
  - [F: Mathematical Background](#f-mathematical-background)
  - [F: Relation to Our Codebase](#f-relation-to-our-codebase)
  - [F: Proposals](#f-proposals)
- [References](#references)
  - [Papers in `.claude/docs/`](#papers-in-claudedocs)
  - [External References](#external-references)
  - [Mathlib Modules](#mathlib-modules)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

This document surveys constructions from the literature that can be
built on our polynomial endofunctor infrastructure on slice
categories, with references to both the mathematical sources and
the corresponding code in our codebase.

## Existing Infrastructure

Our codebase provides the following for polynomial endofunctors
`P : PolyEndo X` on slice categories `Over X`:

**In `PolyAlg.lean`:**

- `PolyEndo X`, `polyEndoFunctor` -- polynomial endofunctors
- `WTypeEndo X`, `wTypeEndoFunctor` -- W-type diagrams
- `PolyAlg P` -- algebra category
- `PolyCoalg P` -- coalgebra category
- `PolyFix`, `polyFixAlg`, `polyFixAlg_isInitial` --
  initial algebra (W-type)
- `polyFixStr_iso` -- Lambek's lemma
- `PolyCofix`, `polyCofixCoalg` -- terminal coalgebra (M-type)
- `polyFreeMonad` -- free monad
- `polyCofreeComonad` -- cofree comonad
- `polyAlgMonadEquiv` -- monad algebra equivalence
- `polyCoalgComonadEquiv` -- comonad coalgebra equivalence
- `polyAlgHasLimitsOfSize` -- limits for algebras

**In `CofreeCategory.lean`:**

- `PolyCofreeCat P` -- cofree category (category instance)
- `polyCoalgCopresheafEquiv` -- copresheaf equivalence
- `polyCoalgHasLimitsOfSize` -- limits for coalgebras
- `polyCoalgHasColimitsOfSize` -- colimits for coalgebras

**In `PolyAlgUMorph.lean`:**

- `algPullback`, `algPullbackFunctor` -- algebra pullback
- `coalgPushforward`, `coalgPushforwardFunctor` --
  coalgebra pushforward
- `algCoprodDesc` -- coproduct algebras
- `coalgProdLift` -- product coalgebras
- `algEqRestrict` -- equalizer algebras
- `coalgCoeqExtend` -- coequalizer coalgebras

**In `Polynomial.lean`:**

- `polyToOverComp` -- polynomial composition

---

## G. Fixed Points as Chain (Co)limits

### G: References

- Adamek, "Free algebras and automata realizations in the
  language of categories and functors" (CMJ 1974)
- [nLab: initial algebra of an endofunctor](https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor)
- [nLab: terminal coalgebra for an endofunctor](https://ncatlab.org/nlab/show/terminal+coalgebra+for+an+endofunctor)
- [1Lab: Adamek's fixpoint theorem](https://1lab.dev/Cat.Functor.Algebra.html#ad%C3%A1meks-fixpoint-theorem)
  (Agda/Cubical formalization; usable as a guide for our
  Lean formalization)

### G: Mathematical Background

#### The iteration chain

Given an endofunctor `F : C -> C` and an initial object
`0 : C`, the *iteration chain* is the diagram
`ℕ -> C` defined by:

- `F^0(0) = 0`
- `F^{n+1}(0) = F(F^n(0))`

with connecting morphisms `F^n(!) : F^n(0) -> F^{n+1}(0)`,
where `! : 0 -> F(0)` is the unique morphism from the initial
object.

**Theorem (Adamek).** If `C` has colimits of ω-chains and `F`
preserves them, then the colimit of the iteration chain
`0 -> F(0) -> F^2(0) -> ...` carries a canonical F-algebra
structure, and this algebra is the initial F-algebra.

Dually, given a terminal object `1 : C`, the *coiteration
chain* is the diagram `ℕ^op -> C`:

- `F^0(1) = 1`
- `F^{n+1}(1) = F(F^n(1))`

with connecting morphisms `F^n(!) : F^{n+1}(1) -> F^n(1)`.

**Dual theorem.** If `C` has limits of ω^op-chains and `F`
preserves them, then the limit of the coiteration chain
`... -> F^2(1) -> F(1) -> 1` carries a canonical F-coalgebra
structure, and this coalgebra is the terminal F-coalgebra.

#### Directed and filtered (co)limits

A directed colimit is indexed by a directed poset: a
nonempty partially ordered set in which every pair of
elements has an upper bound.

A filtered colimit is indexed by a filtered category:
a nonempty category where every finite diagram has a cocone.

Every directed poset is a filtered category (mathlib:
`isFiltered_of_directed_le_nonempty`). Conversely, every
filtered category has a cofinal directed poset (mathlib:
`IsFiltered.exists_directed`, the Deligne construction from
SGA 4 I 8.1.6). So for purposes of computing colimits,
directed and filtered are equivalent.

The poset `(ℕ, ≤)` is directed and nonempty. Therefore:

- The iteration chain `0 -> F(0) -> F^2(0) -> ...` is a
  **filtered colimit** (equivalently, a directed colimit).
- The coiteration chain `... -> F^2(1) -> F(1) -> 1` is a
  **cofiltered limit** (equivalently, a codirected limit).

#### Preservation consequences

**Theorem.** If `G` preserves filtered colimits and `A` is
the initial algebra of `F` (expressed as the colimit of the
iteration chain), then `G` preserves `A` — that is,
`G(A) ≅ colim G(F^n(0))`.

This does not say that `G(A)` is an initial algebra of
anything; it says that `G` commutes with the colimit
construction that produces `A`. The practical consequence
is: functors that preserve filtered colimits (in particular,
finitary polynomial endofunctors) commute with initial
algebra constructions. This applies to our pullback,
pushforward, and composition functors.

Dually, functors preserving cofiltered limits commute
with terminal coalgebra constructions.

### G: Relation to Our Codebase

Our `PolyFix P` is defined as an inductive type (W-type),
and `PolyCofix P` is defined via depth-indexed approximations
(`PolyCofixApprox`) with a consistency relation. Neither is
currently expressed as a categorical (co)limit of an iteration
chain.

Bridging this gap requires:

1. Constructing the iteration chain as a functor
   `ℕ ⥤ Over X` using `polyEndoFunctor P` applied
   iteratively to the initial object of `Over X`.
2. Proving that `polyFixAlg P` (our initial algebra) is
   the colimit of this chain.
3. Dually, constructing the coiteration chain as a functor
   `ℕᵒᵖ ⥤ Over X` and proving that `polyCofixCoalg P`
   is the limit.

Step 2 connects the inductive definition to the categorical
colimit, and step 3 connects the coinductive definition to
the categorical limit. Once established, the preservation
theorems above apply automatically.

### G: Mathlib Infrastructure

- `Mathlib.CategoryTheory.Functor.OfSequence`:
  `Functor.ofSequence` builds `ℕ ⥤ C` from a sequence of
  morphisms `X n ⟶ X (n + 1)`
- `Mathlib.CategoryTheory.Filtered.Basic`:
  `isFiltered_of_directed_le_nonempty` (directed => filtered),
  `IsFiltered.isDirectedOrder` (filtered => directed for
  preorders)
- `Mathlib.CategoryTheory.Presentable.Directed`:
  `IsFiltered.exists_directed` (every filtered category has a
  cofinal directed poset)
- `Mathlib.CategoryTheory.Limits.Preserves.Filtered`:
  `PreservesFilteredColimitsOfSize`
- `Mathlib.CategoryTheory.Endofunctor.Algebra`:
  `Algebra.Initial.str_isIso` (Lambek's lemma for initial
  algebras), `Coalgebra.Terminal.str_isIso` (dual)

### G: Proposals

**G0. Iteration chain functor.** Construct the functor
`polyIterChain P : ℕ ⥤ Over X` sending
`n ↦ (polyEndoFunctor P)^n(initial)`, using
`Functor.ofSequence`. Dually, construct the coiteration
chain `polyCoiterChain P : ℕᵒᵖ ⥤ Over X` sending
`n ↦ (polyEndoFunctor P)^n(terminal)`.

**G1. Initial algebra as chain colimit.** Prove that
`polyFixAlg P` is the colimit of `polyIterChain P`.
This connects our inductive W-type definition to the
categorical colimit construction.

**G2. Terminal coalgebra as chain limit.** Prove that
`polyCofixCoalg P` is the limit of `polyCoiterChain P`.
This connects our coinductive M-type definition to the
categorical limit construction.

**G3. Preservation corollaries.** Derive that any functor
preserving filtered colimits preserves our initial algebras,
and any functor preserving cofiltered limits preserves our
terminal coalgebras. Instantiate for finitary polynomial
endofunctors.

---

## A. Colimits for Polynomial Algebras

### A: References

- [nLab: colimits in categories of algebras](https://ncatlab.org/nlab/show/colimits+in+categories+of+algebras)
- Borceux, *Handbook of Categorical Algebra* Vol. 2, Prop 4.3.2
- Barr-Wells, *Toposes, Triples, and Theories*, Thm 3.9

### A: Mathematical Background

#### Limits (all polynomial functors)

The forgetful functor `U : C^T -> C` creates all limits that
exist in `C`. This holds for any monad `T` on any category `C`,
with no finitariness hypothesis. We already have this via
`polyAlgHasLimitsOfSize`.

#### Beck coequalizer (all polynomial functors)

Every T-algebra is a reflexive coequalizer of free T-algebras.
Concretely, for any `(c, xi : Tc -> c)`, there is a reflexive
fork `FUFUc => FUc -> (c, xi)` whose underlying fork in `C` is a
split coequalizer (hence absolute, preserved by any functor).

This holds for any monad `T`, with no finitariness hypothesis.
In particular, `C^T` always has reflexive coequalizers.

#### Filtered colimit creation (finitary only)

If the monad `T` preserves `J`-shaped colimits and `C` has
`J`-shaped colimits, then `U : C^T -> C` creates `J`-shaped
colimits.

In particular, if `T` preserves filtered colimits (i.e. `T` is
finitary), then `C^T` has filtered colimits (created by `U`).

This is the step that requires finitariness: a polynomial
endofunctor preserves filtered colimits if and only if all its
direction-set fibers are finite.

#### Linton's theorem (cocompleteness from parts)

**Theorem.** If `C^T` has reflexive coequalizers **and** `C^T`
has filtered colimits, then `C^T` has all colimits.

The construction: an arbitrary colimit is built from filtered
colimits and finite colimits; finite colimits are built from
finite coproducts and coequalizers; coequalizers are reflexive
coequalizers of reflexive pairs.

For the algebra category of any monad over a cocomplete base:

- Reflexive coequalizers: provided by Beck (all monads).
- Finite coproducts: created by `U` (all monads over
  cocomplete base).
- Filtered colimits: created by `U` **only if `T` is
  finitary**.

So the chain is: Beck gives reflexive coequalizers for free,
but getting from reflexive coequalizers to all colimits still
requires filtered colimits, which is where finitariness enters.

#### Summary

| Property | Requires finitariness? |
| - | - |
| All limits | N |
| Reflexive coequalizers | N |
| Finite coproducts | N |
| Filtered colimits | Y |
| All colimits | Y |

### A: Finitariness of Polynomial Functors

A polynomial functor `P : Over X -> Over Y` given by the diagram
`X <-s E ->pi B ->t Y` acts by:

```text
P(A) at fiber y = Sigma (b : t^{-1}(y)),
                    Pi (e : pi^{-1}(b)), A_{s(e)}
```

The coproduct over positions `b` always commutes with filtered
colimits. The product `Pi (e : pi^{-1}(b))` commutes with
filtered colimits in `Set` if and only if the indexing set
`pi^{-1}(b)` is finite. So `P` preserves filtered colimits
iff every direction set is finite. The base types `X`, `Y`,
the position set `B`, and the total space `E` can all be
infinite; only the fibers of `pi : E -> B` matter.

This motivates the finitariness predicate, defined for
arbitrary polynomial functors between slices (not just
endofunctors):

```lean
def PolyBetweenFinitary
    (P : PolyFunctorBetweenCat X Y) : Prop :=
  forall (y : Y) (i : polyBetweenIndex X Y P y),
    Finite (polyBetweenFamily X Y P y i)

abbrev PolyEndoFinitary (P : PolyEndo X) : Prop :=
  PolyBetweenFinitary P
```

### A: Application to Our Setting

**All polynomial endofunctors `P : PolyEndo X`** (no
finitariness hypothesis):

- `PolyAlg P` has all limits (via `polyAlgHasLimitsOfSize`)
- `PolyAlg P` has reflexive coequalizers (Beck)
- `PolyAlg P` has finite coproducts (created by forgetful
  functor from `Over X`)

**Finitary polynomial endofunctors** (those satisfying
`PolyEndoFinitary P`, meaning all direction-set fibers are
finite):

- `PolyAlg P` has filtered colimits
- `PolyAlg P` has all colimits

The derivation chain for all colimits in the finitary case:

1. `PolyEndoFinitary P` (hypothesis: each `pi^{-1}(b)` is
   finite)
2. `polyEndoFunctor P` preserves filtered colimits (finite
   products commute with filtered colimits in `Set`)
3. `polyFreeMonad X P` preserves filtered colimits (free
   monad on a filtered-colimit-preserving functor inherits
   the property)
4. `(polyFreeMonad X P).Algebra` has filtered colimits
   (created by the forgetful functor, since the monad
   preserves them)
5. `(polyFreeMonad X P).Algebra` has reflexive coequalizers
   (Beck, no finitariness needed)
6. `(polyFreeMonad X P).Algebra` has all colimits (Linton,
   combining steps 4 and 5)
7. `PolyAlg P` has all colimits (transferred via
   `polyAlgMonadEquiv`)

Step 4 is the only step requiring finitariness. Without it,
the chain stops: we have reflexive coequalizers but not
filtered colimits, and Linton's theorem cannot be applied.

#### Finitariness of the free monad (finitary only)

Step 3 above asserts that the free monad on a finitary
functor is itself finitary. This is a general fact: if
`F` preserves filtered colimits, then the free monad
`T_F` on `F` also preserves filtered colimits.

The argument: `T_F` is the colimit of the iteration chain
`Id → Id + F → Id + F + F² → ...` in the functor category.
Each finite iterate `Id + F + ... + F^n` preserves filtered
colimits (since `F` does, and composition and finite
coproducts of filtered-colimit-preserving functors are
filtered-colimit-preserving). The colimit of the chain is
a filtered colimit (indexed by ℕ), and filtered colimits
commute with filtered colimits. So `T_F` preserves
filtered colimits.

Mathlib provides:

- `comp_preservesFilteredColimits`: composition of
  filtered-colimit-preserving functors preserves filtered
  colimits
- `PreservesFilteredColimitsOfSize`: the typeclass for
  filtered colimit preservation

The main work for proving this in our setting is showing
that `polyFreeMonad X P` (as a monad on `Over X`) preserves
filtered colimits when `P` satisfies `PolyEndoFinitary P`.
This can be done either by the iteration argument above
or by showing that the underlying functor of the monad
agrees with the filtered colimit of the iteration chain
and applying the preservation results.

### A: Mathlib Infrastructure

- `Mathlib.CategoryTheory.Limits.Shapes.Reflexive`:
  `IsReflexivePair`, `HasReflexiveCoequalizers`
- `Mathlib.CategoryTheory.Monad.Coequalizer`:
  `beckAlgebraCoequalizer`, `beckSplitCoequalizer`
- `Mathlib.CategoryTheory.Monad.Monadicity`: Beck's monadicity
  theorem uses reflexive coequalizers

### A: Proposals

**A0. Finitariness predicate.** Define `PolyBetweenFinitary`
for arbitrary polynomial functors between slices, and
`PolyEndoFinitary` as the specialization to endofunctors.

**A1. `HasColimitsOfSize (PolyAlg P)` for finitary `P`.**
Prove cocompleteness of the polynomial algebra category under
the hypothesis `[PolyEndoFinitary P]`. The main work is showing
that a finitary polynomial endofunctor preserves filtered
colimits (finite products commute with filtered colimits).

**A2. Beck coequalizer instantiation.** Specialize
`beckAlgebraCoequalizer` to our polynomial free monad to get:
for any `alpha : PolyAlg P`, there is a reflexive coequalizer
diagram `F(F(U(alpha))) => F(U(alpha)) -> alpha` in
`PolyAlg P`. (This does not require finitariness.)

**A3. Finitary free monad.** Prove that if
`PolyEndoFinitary P`, then `polyFreeMonad X P` (viewed as a
functor on `Over X`) preserves filtered colimits. This is
step 3 in the colimit derivation chain and a reusable result
for any construction that needs the free monad to be
finitary.

---

## H. Connected Limit Preservation

### H: References

- Carboni, Lack, and Walters, "Introduction to extensive
  and distributive categories" (JPAA 1993)
- [nLab: connected limit](https://ncatlab.org/nlab/show/connected+limit)
- [nLab: extensive category](https://ncatlab.org/nlab/show/extensive+category)

### H: Mathematical Background

A *connected limit* is a limit indexed by a connected
category (nonempty, and every pair of objects is joined by
a zigzag of morphisms). Examples:

- Equalizers (indexed by `WalkingParallelPair`)
- Pullbacks and wide pullbacks
  (indexed by `WidePullbackShape`)
- Kernel pairs

Connected limits exclude:

- Terminal objects (empty indexing category)
- Binary products (discrete 2-element indexing category)

#### Products preserve connected limits (all functors)

In any category, the product functor `(X × -)` preserves
all connected limits. This holds without any hypothesis on
the category or the functor.

#### Coproducts preserve connected limits (extensive)

In a finitary extensive category (one where finite
coproducts are van Kampen colimits — `Type u` is the
primary example), coproducts commute with connected limits.
That is, if `f_i : J → C` is a family of diagrams indexed
by `i : I` and `J` is connected, then
`lim_j (Sigma_i f_i(j)) ≅ Sigma_i (lim_j f_i(j))`.

#### Polynomial functors preserve connected limits

**Theorem.** Every polynomial functor on a slice of `Type u`
preserves connected limits. No finitariness hypothesis is
needed.

**Proof sketch.** A polynomial functor
`P(A)_y = Sigma_{b : t^{-1}(y)} Pi_{e : pi^{-1}(b)} A_{s(e)}`
is composed of:

1. The product `Pi_{e : pi^{-1}(b)} A_{s(e)}` — a limit
   of representables, hence preserves all limits (including
   connected ones).
2. The coproduct `Sigma_{b : t^{-1}(y)}` — preserves
   connected limits because `Type u` is finitary extensive.

The composition preserves connected limits.

#### Consequences for our setting

Since all polynomial endofunctors preserve connected
limits, they preserve in particular:

| Shape | Connected? | Preserved? |
| - | - | - |
| Equalizers | Y | Y |
| Pullbacks | Y | Y |
| Weak pullbacks | Y | Y |
| Wide pullbacks | Y | Y |
| Terminal object | N | Not in general |
| Binary products | N | Not in general |

The weak pullback preservation is directly relevant to
the distributive law framework (section C): Turi-Plotkin's
full abstraction result (Corollary 7.4) requires the
behavior functor to preserve weak pullbacks. For
polynomial behavior functors, this holds automatically.

### H: Mathlib Infrastructure

- `Mathlib.CategoryTheory.IsConnected`:
  `IsConnected`, `IsPreconnected`
- `Mathlib.CategoryTheory.Limits.Connected`:
  `prod_preservesConnectedLimits`
- `Mathlib.CategoryTheory.Limits.Shapes.Connected`:
  `widePullbackShape_connected`,
  `parallel_pair_connected`
- `Mathlib.CategoryTheory.Limits.Constructions.Over.Connected`:
  `preservesLimitsOfShape_forget_of_isConnected`
  (Over category forgetful functor preserves connected
  limits)
- `Mathlib.CategoryTheory.Extensive`:
  `FinitaryExtensive` (Type is an instance)
- `Mathlib.CategoryTheory.Limits.VanKampen`:
  `IsVanKampenColimit` (coproducts commute with
  connected limits in extensive categories)
- `Mathlib.CategoryTheory.Limits.Preserves.Filtered`:
  `PreservesLimitsOfShape J F` with `[IsConnected J]`
  (no standalone `PreservesConnectedLimits` typeclass;
  expressed via shape-indexed preservation)

### H: Proposals

**H0. Polynomial functors preserve connected limits.**
Prove `PreservesLimitsOfShape J (polyEndoFunctor P)` for
any `[IsConnected J]`, using the extensive property of
`Type u` and the product/coproduct decomposition. This
requires no finitariness hypothesis.

**H1. Weak pullback preservation corollary.** Instantiate
H0 for `WidePullbackShape` to get pullback preservation,
and derive the weak pullback preservation needed by the
Turi-Plotkin results in section C.

---

## B. The Algebra-Coalgebra-Presheaf Triangle

### B: References

- Adamek, "The intersection of algebra and coalgebra" (TCS 366,
  2006, pp. 82-97)
  - Full paper at `.claude/docs/intersection-algebra-coalgebra-equals-presheaves.pdf`
  - Conference version at `.claude/docs/algebra-intersect-coalgebra-equals-presheaves.pdf`
- Worrell, "A note on coalgebras and presheaves" (MSCS 2005)

### B: Mathematical Background

**Theorem (Adamek 5.2).** For a concrete category V over S-sorted
sets, the following are equivalent:

1. V is concretely equivalent both to a variety and to a covariety.
2. V is concretely equivalent to `Set^{A^op}` for a small category
   A with `S = obj A`.

The paper establishes three layers of results:

**Coalgebra side (Theorem 3.4).** For every signature Sigma, the
category of Sigma-coalgebras is concretely equivalent to the
presheaf category on the *tree category* `T_Sigma`:

> `Coalg H_Sigma ≃ Set^{T_Sigma^op}`

The tree category has Sigma-trees as objects and subtree inclusions
as morphisms. The equivalence functor sends a coalgebra `A` to the
presheaf `t ↦ h_A^{-1}(t)`, decomposing `A` into fibers over the
terminal coalgebra.

**Algebra side (Remark 4.2).** The presheaf category `Set^{A^op}` is
a variety of unary algebras: one unary operation per morphism of A,
with equations encoding identity and composition.

**Characterization (Theorem 3.9).** For a set functor H, `Coalg H`
is concretely equivalent to a presheaf category if and only if H
is a reduction of a polynomial functor (agrees with a polynomial
functor on all nonempty sets).

### B: Relation to Our Codebase

Our `PolyCofreeCat P` is the tree category `T_Sigma` (with the
convention that morphisms go from parent to child rather than child
to parent, so we get copresheaves rather than presheaves). The
objects are fiber+shape pairs (trees), and the morphisms are
depth+position pairs (subtree inclusions via `polyCofreeAnnotPos`).

Our `polyCoalgCopresheafEquiv` is the coalgebra-copresheaf
equivalence `PolyCoalg P ≌ (PolyCofreeCat P ⥤ Type u)`, which is
the covariant analogue of Adamek's Theorem 3.4.

### B: Proposals

**B1. Copresheaves as variety of unary algebras.** Show that
`(PolyCofreeCat P ⥤ Type u)` is equivalent to a variety of unary
algebras (one operation per morphism of the cofree category). This
completes the algebra side of the intersection theorem.

**B2. Fiber decomposition over terminal coalgebra.** Make explicit
that the copresheaf functor factors through the anamorphism to the
terminal coalgebra, giving the Adamek decomposition
`E(A)(t) = h_A^{-1}(t)`.

---

## C. Distributive Laws and Bialgebras

### C: References

- Turi and Plotkin, "Towards a mathematical operational semantics"
  (LICS 1997)
  - PDF at `.claude/docs/towards-mathematical-operational-semantics.pdf`
- Beck, "Distributive laws" (1969)

### C: Mathematical Background

**Distributive law.** Given a monad `T` and a comonad `D` on the
same category `C`, a distributive law is a natural transformation
`lambda : T . D => D . T` satisfying four coherence axioms:

1. `lambda . eta_D = D(eta)` (unit)
2. `lambda . mu_D = D(mu) . lambda_T . T(lambda)` (multiplication)
3. `T(epsilon) = epsilon_T . lambda` (counit)
4. `D(lambda) . lambda_D . T(delta) = delta_T . lambda` (comultiplication)

**Theorem (Turi-Plotkin 7.1).** The following are in bijection:

- Distributive laws `lambda : TD => DT`
- Liftings of T to D-coalgebras
- Liftings of D to T-algebras

**lambda-Bialgebras.** Given a distributive law lambda, a
lambda-bialgebra is a triple `(X, h : TX -> X, k : X -> DX)` where
`h` is a T-algebra, `k` is a D-coalgebra, and the pentagonal
compatibility law holds: `k . h = D(h) . lambda_X . T(k)`.

**Theorem (Turi-Plotkin 7.2, 7.3).** The category of
lambda-bialgebras has:

- An initial object (operational model): `F^lambda(0)`, the free
  bialgebra on the initial D-coalgebra
- A final object (denotational model): `G_lambda(1)`, the cofree
  bialgebra on the final T-algebra

The unique homomorphism from initial to final is *universal
semantics*: simultaneously initial algebra semantics and final
coalgebra semantics (Corollary 7.3). If B preserves weak pullbacks,
this semantics is fully abstract (Corollary 7.4) and bisimulation
is a congruence (Corollary 7.5).

### C: Mathlib Status

Mathlib has `Monad` and `Comonad` (`Monad.Basic`), and
`Monad.Algebra` and `Comonad.Coalgebra` (`Monad.Algebra`), but no
distributive law structure and no bialgebra structure. These would
be built from scratch.

### C: Proposals

**C1. Distributive law structure.** Define
`DistributiveLaw (T : Monad C) (D : Comonad C)` with the four
coherence axioms. This is the foundational structure.

**C2. lambda-Bialgebra category.** Given a distributive law, define
the category of lambda-bialgebras with the pentagonal compatibility
law. Construct the initial and final objects via the free/cofree
adjunctions.

**C3. Distributive law for poly free monad / cofree comonad.**
Construct the canonical distributive law
`lambda : polyFreeMonad X P . polyCofreeComonad X P =>
polyCofreeComonad X P . polyFreeMonad X P`
for our polynomial endofunctors. This gives every polynomial
endofunctor its canonical bialgebraic semantics.

---

## D. Interaction Laws ("Pattern Runs on Matter")

### D: References

- Libkind and Spivak, "Pattern runs on matter: The free monad monad
  as a module over the cofree comonad comonad" (arXiv:2404.16321v2,
  July 2024)
  - PDF at `.claude/docs/pattern-runs-on-matter-free-monad-cofree-comonad-polynomial-functors.pdf`

### D: Mathematical Background

The paper works in the category **Poly** of polynomial functors on
Set with two monoidal products: substitution `◁` (whose monoids
are monads) and the Dirichlet/parallel product `⊗` (pointwise).

**Free monad `m_p`.** For a kappa-small polynomial `p`, the free
monad is constructed by transfinite induction:

- `p_(0) = y` (identity)
- `p_(alpha+1) = y + p ◁ p_(alpha)`
- `p_(alpha) = colim_{alpha' < alpha} p_(alpha')` at limits

The inclusions are all cartesian. For finitary polynomials, the
construction stabilizes at omega.

**Cofree comonad `c_q`.** Constructed as a limit:

- `q^(0) = y`
- `q^(1+i) = y × (q ◁ q^(i))`
- `c_q = lim(... -> q^(2) -> q^(1) -> q^(0))`

Positions of `c_q` are possibly-infinite q-behavior trees.

**The interaction map (Proposition 3.3).** Natural transformations
`Xi_{p,q} : m_p ⊗ c_q -> m_{p ⊗ q}` pair a finite p-tree (from
the free monad, representing a program/pattern) with an infinite
q-tree (from the cofree comonad, representing an
environment/matter) to produce a finite (p⊗q)-tree (representing
the execution trace).

**Module structure (Theorem 3.4).** The free monad functor `m_-` is
a left module over the cofree comonad functor `c_-` via the
Dirichlet product, satisfying unit and associativity coherences.

### D: Relation to Our Codebase

Our `PolyFix P` corresponds to the positions of `m_p` (finite
P-trees), and our `PolyCofreeShape P` / `PolyCofix P` corresponds
to the positions of `c_p` (infinite P-trees). Our polynomial
composition infrastructure (`polyToOverComp`) handles the
substitution product. The Dirichlet product would be new.

### D: Proposals

**D1. Dirichlet/parallel product of polynomial endofunctors.** Define
`P ⊗ Q` for `P Q : PolyEndo X` where positions pair and directions
come from both.

**D2. Interaction map Xi.** Construct the map pairing free monad
elements with cofree comonad elements to produce execution traces.

**D3. Module structure.** Verify the unit and associativity
coherences for the module structure of `m_-` over `c_-`.

---

## E. Operational Semantics via Abstract GSOS

### E: References

- Turi and Plotkin, "Towards a mathematical operational semantics"
  (LICS 1997), Sections 1, 3, 5

### E: Mathematical Background

**Abstract GSOS rules.** A natural transformation
`rho : Sigma(Id × B) => B . T` where Sigma is the signature
endofunctor, B is the behavior endofunctor, and T is the free monad
on Sigma. The naturality condition accounts for syntactic
restrictions on meta-variables.

**Theorem 1.1.** There is a 1-1 correspondence between natural
transformations of type `Sigma(Id × B) => B . T` and image-finite
sets of GSOS rules for a signature Sigma.

**Operational monad (Proposition 5.1).** Given abstract rules rho,
the construction `k ↦ T_rho(k)` extends to a monad T_rho lifting T
to B-coalgebras. This uses structural recursion with accumulators
(Theorem 5.1).

**Structural recursion (Theorem 5.1).** For the free monad T on
Sigma over a cartesian category, given `f : X -> Y` and
`h : Sigma(TX × Y) -> Y`, there exists a unique `f^# : TX -> Y`
satisfying the structural recursion diagram. This generalizes
primitive recursion by allowing terms as parameters.

### E: Relation to Our Codebase

Our `polyFixFoldHom` is the catamorphism (fold) for the initial
algebra. The structural recursion with accumulators is an extension
that takes a product `TX × Y` rather than just `TX`. Our
`polyFixFold` could serve as the base for this extension.

### E: Proposals

**E1. Abstract GSOS rules.** Define the type of abstract GSOS rules
as natural transformations `rho : Sigma(Id × B) => B . T` for
given signature and behavior endofunctors.

**E2. Operational monad.** Construct the lifting of the syntax monad
to B-coalgebras via structural recursion with accumulators.

---

## F. Stone Topology and Second Topos

### F: References

- "Two topoi associated with polynomials" (notes from Spivak 2022
  lecture and "All Concepts are Cat" by Lynch, Shapiro, Spivak)
  - Markdown at `.claude/docs/two-topoi-associated-with-polynomials.md`

### F: Mathematical Background

Given a polynomial p, there are two topoi:

**First topos (copresheaf topos).** The copresheaf category
`Set^{C_p}` where `C_p` is the cofree category. Encodes
"combinatorial or algebraic aspects" of the polynomial. We have this
via `polyCoalgCopresheafEquiv`.

**Second topos (sheaf topos).** Constructed by:

1. The carrier `c_p(1)` of the cofree comonad (infinite p-trees)
   is given a topology whose basis of opens is determined by finite
   p-trees from `m_p(1)` (the initial algebra carrier).
2. Each finite tree t determines a basic open: the set of all
   infinite trees agreeing with t up to its leaves.
3. For finite polynomials, this is a Stone space (compact, totally
   disconnected, Hausdorff).
4. The sheaf topos `Sh(c_p(1))` encodes "dynamical or spatial
   aspects" of the polynomial.

### F: Relation to Our Codebase

We have `PolyFix P x` (finite trees) and `PolyCofreeShape P x`
(infinite trees). Mathlib has `TopologicalSpace` and
`Topology.Sheaves.Sheaf`.

### F: Proposals

**F1. Stone topology on M-types.** Define a `TopologicalSpace`
instance on `PolyCofreeShape P x` using finite tree approximations.

**F2. Stone space property.** For finite polynomials, prove
compactness, total disconnectedness, and the Hausdorff property.

**F3. Sheaf topos.** Construct `Sh(c_P(1))` and study its
relationship to the copresheaf topos.

---

## References

### Papers in `.claude/docs/`

- `intersection-algebra-coalgebra-equals-presheaves.pdf` -- Adamek,
  "The intersection of algebra and coalgebra" (TCS 2006)
- `algebra-intersect-coalgebra-equals-presheaves.pdf` -- Adamek,
  conference version (CALCO 2005)
- `pattern-runs-on-matter-free-monad-cofree-comonad-polynomial-functors.pdf`
  -- Libkind and Spivak (arXiv 2024)
- `towards-mathematical-operational-semantics.pdf` -- Turi and
  Plotkin (LICS 1997)
- `two-topoi-associated-with-polynomials.md` -- Notes from Spivak
  lecture / "All Concepts are Cat"

### External References

- [nLab: initial algebra of an endofunctor](https://ncatlab.org/nlab/show/initial+algebra+of+an+endofunctor)
- [nLab: terminal coalgebra for an endofunctor](https://ncatlab.org/nlab/show/terminal+coalgebra+for+an+endofunctor)
- [1Lab: Adamek's fixpoint theorem](https://1lab.dev/Cat.Functor.Algebra.html#ad%C3%A1meks-fixpoint-theorem)
  (Agda/Cubical formalization)
- [nLab: connected limit](https://ncatlab.org/nlab/show/connected+limit)
- [nLab: extensive category](https://ncatlab.org/nlab/show/extensive+category)
- [nLab: colimits in categories of algebras](https://ncatlab.org/nlab/show/colimits+in+categories+of+algebras)
- [nLab: reflexive coequalizer](https://ncatlab.org/nlab/show/reflexive+coequalizer)
- [nLab: sifted colimit](https://ncatlab.org/nlab/show/sifted+colimit)
- [nLab: finitary monad](https://ncatlab.org/nlab/show/finitary+monad)
- [nLab: polynomial monad](https://ncatlab.org/nlab/show/polynomial+monad)
- Adamek, "Free algebras and automata realizations in the
  language of categories and functors" (CMJ 1974)
- Carboni, Lack, and Walters, "Introduction to extensive
  and distributive categories" (JPAA 1993)
- Borceux, *Handbook of Categorical Algebra* Vol. 2
- Barr and Wells, *Toposes, Triples, and Theories*
- Adamek and Rosicky, *Locally Presentable and Accessible
  Categories*
- Adamek, Rosicky, and Vitale, "What are sifted colimits?"
  (TAC 2010)

### Mathlib Modules

- `Mathlib.CategoryTheory.Functor.OfSequence` --
  `Functor.ofSequence` (build `ℕ ⥤ C` from morphism sequence)
- `Mathlib.CategoryTheory.Filtered.Basic` --
  `IsFiltered`, `isFiltered_of_directed_le_nonempty`
- `Mathlib.CategoryTheory.Presentable.Directed` --
  `IsFiltered.exists_directed` (Deligne construction)
- `Mathlib.CategoryTheory.Limits.Preserves.Filtered` --
  `PreservesFilteredColimitsOfSize`
- `Mathlib.CategoryTheory.IsConnected` --
  `IsConnected`, `IsPreconnected`
- `Mathlib.CategoryTheory.Limits.Connected` --
  `prod_preservesConnectedLimits`
- `Mathlib.CategoryTheory.Limits.Shapes.Connected` --
  `widePullbackShape_connected`,
  `parallel_pair_connected`
- `Mathlib.CategoryTheory.Limits.Constructions.Over.Connected`
  -- `preservesLimitsOfShape_forget_of_isConnected`
- `Mathlib.CategoryTheory.Extensive` --
  `FinitaryExtensive`
- `Mathlib.CategoryTheory.Limits.VanKampen` --
  `IsVanKampenColimit`
- `Mathlib.CategoryTheory.Monad.Basic` -- Monad, Comonad
- `Mathlib.CategoryTheory.Monad.Algebra` -- Monad.Algebra,
  Comonad.Coalgebra
- `Mathlib.CategoryTheory.Monad.Coequalizer` --
  `beckAlgebraCoequalizer`, `beckSplitCoequalizer`
- `Mathlib.CategoryTheory.Monad.Limits` -- `forgetCreatesLimits`,
  `hasLimits_of_reflective`
- `Mathlib.CategoryTheory.Monad.Monadicity` -- Beck's monadicity
  theorem
- `Mathlib.CategoryTheory.Limits.Shapes.Reflexive` --
  `IsReflexivePair`, `HasReflexiveCoequalizers`
- `Mathlib.CategoryTheory.Limits.Sifted` -- `IsSifted`
- `Mathlib.CategoryTheory.Adjunction.Limits` --
  `has_limits_of_equivalence`, `has_colimits_of_equivalence`
- `Mathlib.CategoryTheory.Limits.FunctorCategory.Basic` --
  `functorCategoryHasLimitsOfSize`
- `Mathlib.CategoryTheory.Limits.Creates` --
  `hasLimits_of_hasLimits_createsLimits`
