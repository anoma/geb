# Strongest provenance claims, organized by result

These are the strongest novelty claims in the `geb-lean`
development: results that are either new mathematics, or the first
machine-checked formalization (in any system) of known
mathematics. Each claim asserts a
negative — that no prior published result or formalization of the
stated kind exists — which an online search cannot establish
exhaustively. Every entry is therefore dated and scoped to the
search that backs it (2026-05-31 unless noted), phrased as "no
prior … found" rather than as an absolute, and is revisable as
further prior art surfaces.

This document is organized by mathematical result, not by file. A
single result is often realized by several modules — different
presentations, universe regimes, or proof routes of one
construction — and several file-level tags that are facets of one
result are collapsed into one entry here. The per-module tags,
with their individual citations and search scopes, remain in the
linked area documents.

## Reflective embedding of `Cat` into copresheaves on a finite category

**Result.** There is a reflective adjunction `L ⊣ Φ : Cat ⇄
[J, Type]`, where `J` is an explicit finite index category (four
objects `obj`, `mor`, `id`, `comp`; ten non-identity generating
morphisms). The embedding `Φ` records a category's objects,
morphisms, identity witnesses, and composition witnesses as a
copresheaf on `J`; the reflection `L` reconstructs a category from
such a copresheaf; the counit `L(Φ C) → C` is an isomorphism, so
`Φ` is fully faithful and `Cat` is reflective in the copresheaf
category.

**Context.** There are known reflective adjunctions from `Cat`
into (co)presheaf categories — the nerve–realization adjunction
`τ₁ ⊣ N : Cat ⇄ [Δᵒᵖ, Set]` is the standard example — but in the
cases found, the index category is infinite (e.g. the simplex
category `Δ`), and the nerve in particular is not reflective,
since it is not fully faithful. Here the index category `J` is
finite. The copresheaf over `J` is a proof-relevant, relational
specification of a category: composition and identity are recorded
as relations, not yet required to be total, single-valued, or
lawful. The reflector `L` derives the corresponding category by
making the relation total (extending it with the free category),
then functional and faithful to the category laws (quotienting by
the equivalence closure under identity, composition, and
associativity). Independently, `Cat` is known to be the category
of models of an essentially algebraic theory / finite-limit sketch
(Johnstone, *Sketches of an Elephant* II; Adámek–Rosický, *Locally
Presentable and Accessible Categories*, 1994), and `J` is such a
sketch whose `Set`-models are exactly these specifications; but
those treatments present `Cat` theoretically rather than
exhibiting a concrete finite index category together with an
explicit reflective adjunction and counit isomorphism. Mathlib
formalizes only the infinite-index nerve analogue
(`CategoryTheory.instReflectiveSSetCatNerveFunctor`). No prior
formalization of this finite-index copresheaf encoding or its
reflective adjunction was found. The full prior-art analysis
(nerve–realization, essentially algebraic theories, walking
structures, polynomial functors) is at
[`docs/research/novelty-analysis.md`](../research/novelty-analysis.md).

**Formalized in.**
[category-judgments](category-judgments.md). The index category
and copresheaf data are in `GebLean/CategoryJudgments.lean`; the
direct `Type`-valued adjunction, counit isomorphism, and
universal-property preservation in
`GebLean/CatJudgmentAdjunction.lean`;
the universe-polymorphic and PLang formulations in
`GebLean/PLang/CatJudgment.lean`,
`GebLean/PLang/CatJudgmentAdjunction.lean`, and
`GebLean/PLang/CatJudgCoprAdjunction.lean`; the Grothendieck-route
presentation and adjunction in
`GebLean/PLang/CatJudgGrothendieck.lean` and
`GebLean/PLang/CatJudgGrAdjunction.lean`; the lift to functor
categories `(L ∘ −) ⊣ (Φ ∘ −) : [C, Cat] ⇄ [C, [J, Type]]` in
`GebLean/CatValuedFunctor.lean`.

**Status.** Novel mathematics; the functor-category lift applies a
standard lifting principle to this novel `Φ`. Searched 2026-05-31,
scope Mathlib (leansearch/loogle), nLab, the cited literature;
revisable.

## Dependently-typed presentation of `Cat`, equivalent to the copresheaf form

**Result.** The same data admits a dependently-typed presentation
`DepCategoryData` (sorts `objT`, `morT` and dependent identity and
composition sorts `idT`, `compT` indexed by the morphisms they
constrain), equivalent to the copresheaf presentation on `J`.
`Cat` is the full subcategory of `DepCategoryData` cut out by the
category-like conditions, and its reflectivity is reached by
composing per-property reflective inclusions (witness-subsingleton
truncation, then existence/uniqueness/law layers).

**Context.** This is the dependently-typed counterpart of the
copresheaf result above; its nearest antecedent is the general
"models of a sketch" / essentially-algebraic reading of `Cat`
(Adámek–Rosický 1994) and the general theory of reflective
subcategories (mathlib `CategoryTheory.Reflective`). The specific
dependent/copresheaf correspondence for this `J`, the
full-subcategory characterization, and the staged reflective-
inclusion decomposition were not found formalized elsewhere.

**Formalized in.**
[category-judgments](category-judgments.md). The dependent
presentation and the equivalence with copresheaves on `J` are in
`GebLean/DepCategoryJudgments.lean` (`depCatCopresheafEquiv`); the
full-subcategory equivalence in `GebLean/DepCategoryCat.lean`
(`catDepCategoryCatEquiv`); the layered reflective adjunction in
`GebLean/DepCategoryAdjunction.lean`. A pedagogically simplified
two-object variant is `GebLean/LayeredEquivalence.lean`.

**Status.** Novel mathematics. Searched 2026-05-31,
scope Mathlib (leansearch/loogle), nLab; revisable.

## Categorical equivalence `LawvereERCat ≌ LawvereKSimDCat 2`

**Result.** The elementary-recursive functions and Tourlakis's
`K^sim` functions at simultaneous-recursion nesting depth 2 are
each presented as a Lawvere category (finite-product category
whose object `n` is the `n`-fold power of a generic object and
whose morphisms `n ⟶ m` are `m`-tuples of term functions of `n`
inputs, modulo extensional equality of their standard
interpretation in `ℕ`). The two are packaged as a categorical
equivalence `erKSimEquiv : LawvereERCat ≌ LawvereKSimDCat 2`, with
functors `kToERFunctor` (forward inclusion `K^sim_2 ⊆ ER`) and
`erToKFunctor` (the converse, via a URM simulation of ER programs
by `K^sim_2` morphisms with a bounded-search runtime budget).

**Context.** The set-level equality of the two function classes is
Tourlakis, *Theory of Computation* (Wiley 2012), Corollary
0.1.0.44 at `n = 2`; the underlying URM-simulation argument is
classical (Wagner–Wong; Cutland, *Computability*, CUP 1980). What
appears novel is casting this coincidence as a categorical
equivalence of Lawvere categories — and proving it in a proof
assistant — rather than as an equality of subsets of the
recursive functions. No prior formalization of the `K^sim`
hierarchy, of either function class as a Lawvere category, or of
their coincidence as a categorical equivalence was found.

**Formalized in.** [lawvere-er-ksim](lawvere-er-ksim.md). The two
Lawvere categories are in `GebLean/LawvereER.lean` and
`GebLean/LawvereKSim.lean`; the compiler, URM simulator, runtime
bound, translators, and the packaged equivalence are in the
`GebLean/LawvereERKSim/` modules (`Compiler.lean`, `Embedding.lean`,
`Loops.lean`, `ErToK.lean`/`ErToKFunctor.lean`, and
`Equivalence.lean`, where `erKSimEquiv` is assembled).

**Status.** The categorical-equivalence packaging is novel
(`unverified`); the formalization of the Tourlakis coincidence and
the URM-simulation argument in this packaging is the first in Lean.
Searched 2026-05-31, scope Mathlib (leansearch/loogle),
then the cited literature; revisable.

## Lawvere-category presentations of the ER and `K^sim` classes

**Result.** The elementary-recursive functions, the `K^sim`
hierarchy, and (tree-natively) elementary recursion over binary
trees are each presented as a Lawvere category, with class-specific
results proved categorically: `erInterpFunctor_not_full` and
`tetration_not_ER` (the interpretation functor of the ER category
is not full, and tetration lies outside ER), and a tree-native ER
category with a Gödel numbering of trees built from Szudzik's
elegant pairing function. A bespoke two-sort Lawvere theory of
naturals and binary trees (`NatBT`) is shown equivalent to ER on
its `m = 0` subcategory.

**Context.** The elementary-recursive functions and the `K^sim`
hierarchy are standard recursion theory (Kalmár; Tourlakis 2012);
Szudzik's pairing is from *An Elegant Pairing Function* (2006).
What appears novel is the packaging of each function class as a
Lawvere category and the categorical proofs of the class-specific
properties (non-fullness, the tetration separation), together with
the tree-native ER realization and the two-sort `NatBT` theory. No
prior Lean formalization of these classes, in this Lawvere
packaging or tree-native form, was found.

**Formalized in.** [lawvere-er-ksim](lawvere-er-ksim.md). The ER
category and its ER-specific results are in the `GebLean/LawvereER*`
modules; the `K^sim` hierarchy in the `GebLean/LawvereKSim*`
modules; tree-native ER and tree Gödel numbering in
`GebLean/LawvereTreeER*`, `GebLean/TreeGoedel*`, and
`GebLean/NatElegantPair.lean`; the two-sort theory in
`GebLean/LawvereNatBT*`/`GebLean/LawvereNatBTV2*` with the `m = 0`
equivalence in `GebLean/LawvereERNatBTV2Equiv.lean`.

**Status.** The Lawvere and tree-native packagings are novel
(`unverified`), built on components that are themselves known
mathematics first formalized in Lean here (the function classes and
the pairing function). Searched 2026-05-31, scope Mathlib
(leansearch/loogle), then the cited literature; revisable.

## Dialgebra-of-profunctor "hexagon" category

**Result.** For profunctors `P`, `Q` there is a "hexagon"
category `HexagonObj P Q`, identified with the category of
diagonal elements of the profunctor-dialgebra profunctor
`ProfDialgebraProf P Q : (a, b) ↦ P(b, a) ⟶ Q(a, b)`, via
`hexagonCatEquivDiagElem : HexagonObj P Q ≌ DiagElem
(ProfDialgebraProf P Q)`.

**Context.** The nearest antecedent is the dialgebra category for
ordinary functors (Uustalu; nLab "dialgebra"). The hexagon
category and its identification with diagonal elements of a
profunctor-dialgebra profunctor were not found in the published
literature (including Loregian, *Coend Calculus*, 2021).

**Formalized in.** [profunctors-ends](profunctors-ends.md), in the
hexagon-category module (`HexagonObj`, `ProfDialgebraProf`,
`hexagonCatEquivDiagElem`).

**Status.** Novel mathematics (`unverified`). Searched
2026-05-31, scope Mathlib (leansearch), nLab, Loregian 2021;
revisable.

## Wedge-weight construction representing paranatural transformations

**Result.** A wedge-weight construction sends diagonal elements to
the wedge weight at identity twisted arrows, with
`wedgeWeightIdentityMap_injective` establishing injectivity and
`paranatWeightedLimitEquiv` representing paranatural
transformations as a weighted limit; concrete `diagApp`
descriptions are given for algebra, coalgebra, and hom
profunctors.

**Context.** The nearest antecedents are the weighted-limit
characterization of ends (Kelly, *Basic Concepts of Enriched
Category Theory*, 1982, §3; Loregian, *Coend Calculus*, 2021). The
wedge-weight construction and its role in representing paranatural
transformations via `paranatWeightedLimitEquiv` were not found in
the standard literature on ends.

**Formalized in.** [profunctors-ends](profunctors-ends.md), in the
wedge-weight module (`wedgeWeightIdentityMap_injective`,
`paranatWeightedLimitEquiv`, `diagApp` for `AlgProf`, `CoalgProf`,
`HomProf`).

**Status.** Novel mathematics (`unverified`). Searched
2026-05-31, scope Mathlib (leansearch), nLab; revisable.

## Paranatural-topos assembly functor and diagonal-determinedness

**Result.** A paranatural topos is assembled via an assembly
functor from endoprofunctor data, with explicit terminal object
and binary products (`endoProfTerminal_isTerminal`,
`endoProfBinaryFan_isLimit`) and a diagonal equalizer
(`diagEqualizer`), under a diagonal-determinedness condition.

**Context.** The assembly-functor approach to a paranatural topos
and the diagonal-determinedness condition were not found in prior
literature or mathlib. Related background is in
[`docs/research/paranatural-topos-research.md`](../research/paranatural-topos-research.md)
and
[`docs/research/parametric-copresheaf-topos.md`](../research/parametric-copresheaf-topos.md).

**Formalized in.** [nno-arithmetic-topos](nno-arithmetic-topos.md),
in `GebLean/ParanaturalTopos.lean`.

**Status.** Novel mathematics. Searched 2026-05-31,
scope nLab, Mathlib (leansearch/loogle); revisable.

## Parametric-right-adjoint presheaf category

**Result.** Parametric right adjoints (PRAs) in the
Weber/Gambino–Kock sense are realized as a bifunctor-assembled
presheaf category, with positions-and-directions accessors
(`praPositions`, `praDirectionsAt`, `praEvalAtFunctor`) and a
Grothendieck-based limit construction (`CoprodCovarRepCat`) in
which a PRA's data is reassembled (`praReassemble`).

**Context.** The PRA theory itself is known mathematics (Weber
2004; Gambino–Kock 2013), and the limit techniques are standard
mathlib material. Its formalization as a bifunctor-assembled
presheaf category, and the specific Grothendieck-route limit
construction for `CoprodCovarRepCat`, were not found in prior work.
Background is in
[`docs/research/presheaf-pra.md`](../research/presheaf-pra.md).

**Formalized in.** [nno-arithmetic-topos](nno-arithmetic-topos.md),
in `GebLean/PresheafPRA.lean` and `GebLean/PresheafPRAUMorph.lean`.

**Status.** The underlying parametric-right-adjoint theory is known
mathematics; the bifunctor-assembled presheaf-category
formalization and the Grothendieck-route limit construction are
novel at the formalization level. Searched 2026-05-31, scope
Mathlib (leansearch/loogle), nLab, Weber 2004, Gambino–Kock 2013;
revisable.

## Categorical NNO interface and arithmetic from a PBTO

**Result.** From a parameterized-binary-tree-object (PBTO) bearing
category, a natural-numbers-object interface and recursive-function
arithmetic are derived categorically: a natural-numbers object via
right-spine normalization, with the Cantor pairing/unpairing
retraction `cantorUnpair ; cantorPair = toRSpineNat` proved
categorically; the arithmetic operations (`natPlus`, `natEq`) as
morphisms in the abstract category with their exact computation
rules, including a commutative cancellative monoid structure and an
equality test; and a parameterized-list-object (PSO) interface
`X ↦ 1 + X × B` with an `nnoToIsPSO` instance and a cons-list
paramorphism variant.

**Context.** The NNO universal property is standard, Cantor
pairing is classical, and parameterized list objects appear in
categorical type theory (Uustalu–Vene, *Primitive (co)recursion
and course-of-value (co)iteration*, 1999). The derivation of the
NNO interface from a PBTO via right-spine normalization, the
categorical proof of the pairing retraction, the realization of
recursive-function arithmetic as morphisms in an abstract
PBTO-bearing category with these exact computation rules, and the
specific `X ↦ 1 + X × B`-algebra interface with the NNO-to-PSO
instance were not found in the literature, in mathlib, or in prior
formalizations.

**Formalized in.** [nno-arithmetic-topos](nno-arithmetic-topos.md),
in the NNO-arithmetic, Cantor-retraction, PSO-interface, and
PSTO-recursion modules of the area.

**Status.** Known mathematics, first machine-checked formalization
anywhere; the categorical presentations are novel at the
formalization level. Searched 2026-05-31, scope Mathlib
(leansearch/loogle), nLab, Lambek–Scott; revisable.
