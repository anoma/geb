# Lean 4 library and categorical theory resources

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Searchable](#searchable)
- [Lean language](#lean-language)
- [CSLib](#cslib)
- [General mathematics](#general-mathematics)
- [General category theory](#general-category-theory)
- [Opposite categories](#opposite-categories)
- [Comma / slice (over) / coslice (under) categories](#comma--slice-over--coslice-under-categories)
- [Polynomial functors](#polynomial-functors)
- [Profunctors](#profunctors)
- [Parametricity and Free Theorems](#parametricity-and-free-theorems)
- [Computability](#computability)
- [Monad algebra](#monad-algebra)
- [Kan extensions](#kan-extensions)
- [Grothendieck Construction](#grothendieck-construction)
- [Simplicial Sets and Nerves](#simplicial-sets-and-nerves)
- [Quotients](#quotients)
- [Topos Theory](#topos-theory)
- [Presheaf/Copresheaf Universal Properties](#presheafcopresheaf-universal-properties)
- [Subobject Classifiers and Related](#subobject-classifiers-and-related)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Links to mathematical concepts available in Lean 4 libraries (particularly
`mathlib`). In this repository, only standard libraries are used in code,
but external libraries may be examined for ideas. This list was lifted
from the prior `CLAUDE.md`; it is preserved here as a reference document
so that `CLAUDE.md` itself can stay short.

## Searchable

- [Loogle](https://loogle.lean-lang.org/)
  - A searchable reference to the Lean standard libraries -- consult it
    to look up standard implementations of concepts not already known.
- [Reservoir](https://reservoir.lean-lang.org/)
- The remote-index search tools (Loogle, `lean_leansearch`,
  `lean_leanfinder`, `lean_state_search`, `lean_hammer_premise`)
  index mathlib + Lean core + batteries; **none currently index
  CSLib**. For CSLib content, use the CSLib API docs site
  (<https://api.cslib.io/docs/>) or grep the CSLib source under
  `.lake/packages/cslib/Cslib/`.
- When introducing a new computational construct (register
  machine, Turing machine, automaton, λ-calculus variant,
  programming-language semantics, etc.), search CSLib first, just
  as mathlib is searched for general mathematical concepts.

## Lean language

- [The Lean 4 Theorem Prover and Programming Language
  (conference paper)][lean4-paper]
- [Functional Programming in Lean: Structures and
  Inheritance][fpil-inheritance]
- [Lean Language Reference: Type Classes][lean-ref-typeclasses]
- [Theorem Proving in Lean 4][tpil4]
- [Theorem Proving in Lean 4: Type Classes][tpil4-typeclasses]
- [Functional Programming in Lean: Type Classes and
  Polymorphism][fpil-polymorphism]
- [Tabled Typeclass Resolution](https://arxiv.org/pdf/2001.04301)
- [Use and abuse of instance parameters in the Lean mathematical
  library](https://arxiv.org/pdf/2202.01629.pdf)
- [Lean projects and build process][lean-project-build]
- [A Beginner's Guide to Theorem Proving in Lean 4][beginner-tpil]

[lean4-paper]: https://link.springer.com/content/pdf/10.1007/978-3-030-79876-5_37.pdf?pdf=inline%20link
[fpil-inheritance]: https://leanprover.github.io/functional_programming_in_lean/functor-applicative-monad/inheritance.html
[lean-ref-typeclasses]: https://lean-lang.org/doc/reference/latest/Type-Classes/
[tpil4]: https://leanprover.github.io/theorem_proving_in_lean4/
[tpil4-typeclasses]: https://lean-lang.org/theorem_proving_in_lean4/Type-Classes/
[fpil-polymorphism]: https://leanprover.github.io/functional_programming_in_lean/type-classes/polymorphism.html
[lean-project-build]: https://leanprover-community.github.io/install/project.html
[beginner-tpil]: https://emallson.net/blog/a-beginners-companion-to-theorem-proving-in-lean/

## CSLib

- [Homepage](https://www.cslib.io/) and
  [whitepaper (arXiv:2602.04846)](https://arxiv.org/abs/2602.04846)
- [API docs](https://api.cslib.io/docs/)
- [Repository](https://github.com/leanprover/cslib)
- Top-level directory layout under `Cslib/` (snapshot at
  `v4.29.0-rc6`; verify against the pinned tag when bumping):
  - `Algorithms/` — algorithm/data-structure formalizations.
  - `Computability/` — `Automata/`, `Languages/`, `Machines/`,
    `URM/` (Unlimited Register Machine; namespace `Cslib.URM`).
  - `Foundations/` — `Combinatorics/`, `Control/`, `Data/`,
    `Lint/`, `Logic/`, `Semantics/` (including `LTS/` and
    `FLTS/`), `Syntax/`.
  - `Languages/` — `Boole/`, `CCS/`, `CombinatoryLogic/`,
    `LambdaCalculus/`.
  - `Logics/` — `HML/`, `LinearLogic/` (plural directory name).
- Constructive discipline: importing CSLib is fine in the same
  sense that importing mathlib is fine, but the project rule that
  bans `Classical`, `noncomputable`, and `axiom` applies to any
  *transitive* axiom dependency too: a GebLean term that depends
  on a CSLib (or mathlib) lemma using `Classical.choice` will
  surface that axiom under `#print axioms`. For results that must
  remain constructive, run `#print axioms` and refactor if a
  non-pure axiom appears.
- Reuse discipline: prefer CSLib typeclasses and abstract
  structures (e.g. `LTS`, `HasFresh`) over reaching into concrete
  instances, so internal CSLib changes do not break dependent code.

## General mathematics

- [Lean's "mathlib" page][mathlib-overview]

[mathlib-overview]: https://leanprover-community.github.io/mathlib-overview.html

## General category theory

- [Lean's "category theory" page][lean-cat-theory]

[lean-cat-theory]: https://leanprover-community.github.io/theories/category_theory.html

## Opposite categories

- [Mathlib.CategoryTheory.Opposites][cat-opposites]
- [Mathlib.CategoryTheory.Category.Cat.Op][cat-cat-op]

[cat-opposites]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Opposites.html
[cat-cat-op]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Category/Cat/Op.html

## Comma / slice (over) / coslice (under) categories

- [Mathlib.CategoryTheory.Comma.Basic][comma-basic]
- [PLMlab's `Over.lean`][plmlab-over]
- [CategoryTheory.Arrow][cat-arrow]

[comma-basic]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Comma/Basic.html
[plmlab-over]: https://plmlab.math.cnrs.fr/nuccio/mathlib4/-/blob/master/Mathlib/CategoryTheory/Over.lean?ref_type=heads
[cat-arrow]: https://leanprover-community.github.io/mathlib_docs/category_theory/arrow.html

## Polynomial functors

- [mathlib4's univariate polynomial functors][pfunctor-univariate]
- [mathlib4's multivariate polynomial functors][pfunctor-multivariate]
- [mathlib4's W-types][w-types]
- [mathlib4's M-types][m-types]
- [mathlib4's univariate QPFs (quotients of polynomial
  functors)][qpf-univariate]
- [mathlib4's multivariate QPFs (quotients of polynomial
  functors)][qpf-multivariate]

[pfunctor-univariate]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/PFunctor/Univariate/Basic.html
[pfunctor-multivariate]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/PFunctor/Multivariate/Basic.html
[w-types]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/PFunctor/Multivariate/W.html
[m-types]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/PFunctor/Multivariate/M.html
[qpf-univariate]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/QPF/Univariate/Basic.html
[qpf-multivariate]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/QPF/Multivariate/Basic.html

## Profunctors

- [Mathlib.CategoryTheory.Limits.Shapes.End (ends and
  coends)][limits-end]

[limits-end]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Shapes/End.html

## Parametricity and Free Theorems

- [Wadler, Theorems for free! (1989)](.claude/wadler89-theorems-for-free.pdf)
  - Types read as relations; parametricity proposition: (t,t) in
    the relational interpretation of T. Application to rearrangement,
    fold, sort, filter, map. Connection to lax natural
    transformations noted.
- [Reasonably Polymorphic: Review of Theorems for
  Free](https://reasonablypolymorphic.com/blog/theorems-for-free/)
  - Relations specialized to functions become bifunctors;
    function relation becomes naturality square f' . g = h . f;
    conjecture: all Haskell laws are category laws in different
    categories.

## Computability

- [Mathlib.Computability.Primrec][computability-primrec]
- [Mathlib.Computability.TMComputable][computability-tm]
- [Mathlib.Computability.TuringMachine][computability-turing]

[computability-primrec]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/Primrec.html
[computability-tm]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/TMComputable.html
[computability-turing]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Computability/TuringMachine.html

## Monad algebra

- [mathlib4's Monad.Algebra][monad-algebra]

[monad-algebra]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Monad/Algebra.html

## Kan extensions

- [mathlib4's KanExtension][kan-extension]
- [mathlib4's CategoryTheory.Bicategory.KanExtension.Adjunction][kan-bicat]

[kan-extension]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Functor/KanExtension/Basic.html
[kan-bicat]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Bicategory/Kan/Adjunction.html

## Grothendieck Construction

- [Mathlib.CategoryTheory.Grothendieck][grothendieck]
  - Provides Lean formalization of the Grothendieck construction for
    functors valued in categories (\(C \to Cat\)), including morphisms
    and universal properties.

- [Mathlib.CategoryTheory.Bicategory.Grothendieck][grothendieck-bicat]
  - Bicategorical generalization of the Grothendieck construction.

[grothendieck]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Grothendieck.html
[grothendieck-bicat]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Bicategory/Grothendieck.html

## Simplicial Sets and Nerves

- [Mathlib.AlgebraicTopology.SimplicialSet.Basic][sset-basic]
- [Mathlib.AlgebraicTopology.SimplicialSet.Nerve][sset-nerve]
- [Mathlib.AlgebraicTopology.SimplicialSet.NerveAdjunction][sset-nerve-adj]

[sset-basic]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplicialSet/Basic.html
[sset-nerve]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplicialSet/Nerve.html
[sset-nerve-adj]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/AlgebraicTopology/SimplicialSet/NerveAdjunction.html

## Quotients

- [Init.Prelude.Quot][init-prelude-quot]
  - Other operations on `Quot` follow
- [Init.Core.Quot.recOn][init-core-quot-recon]
  - Other operations on `Quot` precede and follow
- [Init.Core.Quotient][init-core-quotient]
- [Mathlib.Data.Fintype.Quotient][fintype-quotient]

[init-prelude-quot]: https://leanprover-community.github.io/mathlib4_docs/Init/Prelude.html#Quot
[init-core-quot-recon]: https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#Quot.recOn
[init-core-quotient]: https://leanprover-community.github.io/mathlib4_docs/Init/Core.html#Quotient
[fintype-quotient]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Data/Fintype/Quotient.html

## Topos Theory

- [Mathlib.CategoryTheory.Topos.Classifier][topos-classifier]
- [b-mehta/topos: Topos theory in Lean](https://github.com/b-mehta/topos)
  - Independent repository formalizing foundational aspects of topos
    theory, including subobject classifiers, Lawvere-Tierney
    topologies, and categorical theorems.

[topos-classifier]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Topos/Classifier.html

## Presheaf/Copresheaf Universal Properties

- [Mathlib.CategoryTheory.Limits.Presheaf][limits-presheaf]
  - Formalizes limits and colimits within presheaf categories,
    including the colimit-of-representables theorem.

- [Mathlib.CategoryTheory.Comma.Presheaf.Colimit][comma-presheaf-colimit]
  - Addresses colimit structures in comma categories related to
    presheaf categories.

- [Mathlib.Topology.Sheaves.Sheaf][topology-sheaf]
  - Implementation of sheaf theory, with presheaves and categorical
    structures detailed for topological spaces.

- [Mathlib.Topology.Sheaves.Presheaf][topology-presheaf]
  - Documents presheaf categories for sheaf-theoretic constructions.

[limits-presheaf]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Limits/Presheaf.html
[comma-presheaf-colimit]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Comma/Presheaf/Colimit.html
[topology-sheaf]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Sheaves/Sheaf.html
[topology-presheaf]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/Topology/Sheaves/Presheaf.html

## Subobject Classifiers and Related

- [Mathlib.CategoryTheory.Topos.Classifier][topos-classifier-2]
  - Detailed formalization of subobject classifiers in category theory,
    including construction for presheaf categories.

- [Mathlib.CategoryTheory.Subpresheaf.Subobject][subpresheaf-subobject]
  - Focuses on subobjects and subpresheaf categories, relevant to
    classifier theory and morphism structure.

- [Mathlib/CategoryTheory/Sites/Closed.lean][sites-closed]
  - Code and theory for closed sites, relevant for power objects and
    classifier constructions.

[topos-classifier-2]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Topos/Classifier.html
[subpresheaf-subobject]: https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Subpresheaf/Subobject.html
[sites-closed]: https://plmlab.math.cnrs.fr/nuccio/octonions/-/blob/add-vector-api-alt/Mathlib/CategoryTheory/Sites/Closed.lean
