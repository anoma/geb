# Possible novelties

Here we index possible novelties in the code in this
repository:  constructions which we have not been able to find
in published mathematics, or are known in published mathematics
but for which we have not been able to find software
formalizations, or specifically Lean formalizations.

## Reflective embedding of `Cat` into copresheaves on a finite category

**Result:** There is a reflective adjunction `L ⊣ Φ : Cat ⇄
[J, Type]`, where `J` is a finite category (four
objects `obj`, `mor`, `id`, `comp`; ten non-identity generating
morphisms). The embedding `Φ` records a category's objects,
morphisms, identity witnesses, and composition witnesses as a
copresheaf on `J`; the reflection `L` reconstructs a category from
such a copresheaf; the counit `L(Φ C) → C` is an isomorphism, so
`Φ` is fully faithful and `Cat` is reflective in the copresheaf
category.

**Context:.** There are known reflective adjunctions from `Cat`
into (co)presheaf categories — the nerve–realization adjunction
`τ₁ ⊣ N : Cat ⇄ [Δᵒᵖ, Set]` is a standard example — but in the
cases we have found, the index category is infinite (e.g. the simplex
category `Δ`).  Here the index category `J` is finite.
The copresheaf over `J` is a proof-relevant, relational
specification of a category: composition and identity are recorded
as relations, not required to be total, single-valued, or
lawful. The reflector `L` derives the corresponding category by
making the relation total (extending it with the free category),
then functional and faithful to the category laws (quotienting by
the equivalence closure under identity, composition, and
associativity).

`Cat` is known to be the category
of models of an essentially algebraic theory / finite-limit sketch
(Johnstone, *Sketches of an Elephant* II; Adámek–Rosický, *Locally
Presentable and Accessible Categories*, 1994).
Mathlib formalizes the infinite-index nerve analogue
(`CategoryTheory.instReflectiveSSetCatNerveFunctor`). No
mathematical construction corresponding to this finite-index
copresheaf encoding and its reflective adjunction was found in the
literature, let alone a machine-checked formalization or one in
Lean. The full prior-art analysis
(nerve–realization, essentially algebraic theories, walking
structures, polynomial functors) is at
[`docs/research/novelty-analysis.md`](../research/novelty-analysis.md).

**Formalized in:**
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

**Application:** The reflective embedding into a topos allows
the use of the category of PRA functors on that topos as the
category of "categories a la carte", while the finite index
category allows decidable type-checking of ASTs as objects
and morphisms of the category.

## Dependently-typed presentation of `Cat`, equivalent to the copresheaf form

**Result:** The same data admits a dependently-typed presentation
`DepCategoryData` (sorts `objT`, `morT` and dependent identity and
composition sorts `idT`, `compT` indexed by the morphisms they
constrain), equivalent to the copresheaf presentation on `J`.
`Cat` is the full subcategory of `DepCategoryData` cut out by the
category-like conditions, and its reflectivity is reached by
composing per-property reflective inclusions (witness-subsingleton
truncation, then existence/uniqueness/law layers).

**Context:** This is the dependently-typed counterpart of the
copresheaf result above; its nearest antecedent is the general
"models of a sketch" / essentially-algebraic reading of `Cat`
(Adámek–Rosický 1994) and the general theory of reflective
subcategories (mathlib `CategoryTheory.Reflective`). The specific
dependent/copresheaf correspondence for this `J`, the
full-subcategory characterization, and the staged reflective-
inclusion decomposition were not found in the literature,
formalized or otherwise.

**Formalized in:**
[category-judgments](category-judgments.md). The dependent
presentation and the equivalence with copresheaves on `J` are in
`GebLean/DepCategoryJudgments.lean` (`depCatCopresheafEquiv`); the
full-subcategory equivalence in `GebLean/DepCategoryCat.lean`
(`catDepCategoryCatEquiv`); the layered reflective adjunction in
`GebLean/DepCategoryAdjunction.lean`.

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
might be slightly novel in the presentation is casting this
coincidence as a categorical equivalence of Lawvere categories —
and proving it in a proof assistant — rather than as an equality
of subsets of the recursive functions. We have not found
other mechanical formalizations of the `K^sim`
hierarchy, of either function class as a Lawvere category, or of
their coincidence as a categorical equivalence.

**Formalized in.** [lawvere-er-ksim](lawvere-er-ksim.md). The two
Lawvere categories are in `GebLean/LawvereER.lean` and
`GebLean/LawvereKSim.lean`; the compiler, URM simulator, runtime
bound, translators, and the packaged equivalence are in the
`GebLean/LawvereERKSim/` modules (`Compiler.lean`, `Embedding.lean`,
`Loops.lean`, `ErToK.lean`/`ErToKFunctor.lean`, and
`Equivalence.lean`, where `erKSimEquiv` is assembled).

## Lawvere-category presentations of the ER and `K^sim` classes

**Result.** The elementary-recursive functions, the `K^sim`
hierarchy, and (tree-natively) elementary recursion over binary
trees are each presented as a Lawvere category, with class-specific
results proved categorically: `erInterpFunctor_not_full` and
`tetration_not_ER` (the interpretation functor of the ER category
is not full, and tetration lies outside ER), and a tree-native ER
category with a Gödel numbering of trees built from Szudzik's
elegant pairing function.

**Context.** The elementary-recursive functions and the `K^sim`
hierarchy are standard recursion theory (Kalmár; Tourlakis 2012);
Szudzik's pairing is from *An Elegant Pairing Function* (2006).
Again there might be slight novelty in the presentation of the
function classes as Lawvere categories and the categorical proofs
of the class-specific properties (non-fullness, the tetration
separation), together with the tree-native ER realization and the
two-sort `NatBT` theory.

**Formalized in.** [lawvere-er-ksim](lawvere-er-ksim.md). The ER
category and its ER-specific results are in the `GebLean/LawvereER*`
modules; the `K^sim` hierarchy in the `GebLean/LawvereKSim*`
modules; tree-native ER and tree Gödel numbering in
`GebLean/LawvereTreeER*`, `GebLean/TreeGoedel*`, and
`GebLean/NatElegantPair.lean`; the two-sort theory in
`GebLean/LawvereNatBT*`/`GebLean/LawvereNatBTV2*` with the `m = 0`
equivalence in `GebLean/LawvereERNatBTV2Equiv.lean`.

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

## Polynomial functors between arbitrary slice categories, with the Spivak–Niu operations

**Result.** `PolyFunctorBetweenCat X Y` formalizes polynomial
functors between arbitrary slice categories (`Over X → Over Y`), not
merely polynomial endofunctors of `Type`, together with a broad range
of the operations of Spivak–Niu's *Polynomial Functors*: composition,
products and coproducts, the `Σ_f ⊣ f* ⊣ Π_f` adjoint triple, the
density / copresheaf-presentation equivalence
`PolyPresentationLoc D ≌ (D ⥤ Type)`, and the limit and colimit
structure of the algebra and coalgebra categories. The
parametric-right-adjoint generalization to arbitrary presheaf
categories is recorded separately (the
parametric-right-adjoint presheaf-category entry below).

**Context.** None of this mathematics is novel: polynomial functors
and their categories are standard (Gambino–Kock, *Polynomial functors
and polynomial monads*, 2013; Spivak–Niu, *Polynomial Functors*, 2024;
nLab, "polynomial functor"). Only the formalization in a formal
programming language, at this generality, is in question. Lean already
formalizes polynomial functors in two more restricted forms —
mathlib's container-style `PFunctor` / `MvPFunctor` over `Type`, and
the `Poly` library's univariate and multivariate theory within a
locally Cartesian closed framework (<https://github.com/sinhp/Poly>) —
but neither exposes polynomial functors between arbitrary slice
categories, and we have not found the breadth of Spivak–Niu operations
realized here in any Lean or Idris formalization.

**Formalized in.** [polynomial-functors](polynomial-functors.md):
`PolyFunctorBetweenCat` in `GebLean/Polynomial.lean`, with the
operations distributed across the area's modules (`PolyAdjunctions`,
`PolyUMorph`, `Utilities/PolyCombinators`, the `PolyPresentation*` and
`PolyAlg*` modules). The Idris predecessor develops the same material
(`geb-idris/docs/areas/polynomial-functors.md`).

## Parametric-right-adjoint presheaf category

Parametric right adjoint functors between presheaf categories
are well-known, but we have not found mechanical formalizations
elsewhere.  We have also not found another explicit
construction of the operation of generating PRA functor
categories as itself functorial (a funtor into `Cat`).

## Paranatural transformations as natural transformations

We have not found elsewhere a reduction of paranatural
(AKA strong dinatural) transformations to natural
transformations, as we do in `paranatWeightedLimitEquiv`.

## Parametric polymorphism on arbitrary categories

We have not found elsewhere a generalization of parametric
polymorphism to arbitrary categories, as we have done using
the double category of relations on the presheaf category
of the given category.  This makes parametric transformations
into a quasitopos with a reflective inclusion into a topos
(the topos of spans in the presheaf category).  We show
that this agrees with paranatural transformations between
profunctors when the two profunctors are dialgebra profunctors,
but disagrees in general.  In particular in the example
which Neumann gives in which paranatural transformations
do not produce the guarantee expected from parametric
polymorphism, our formulation agrees with the parametric
expectation, not the inadequate paranatural one.
