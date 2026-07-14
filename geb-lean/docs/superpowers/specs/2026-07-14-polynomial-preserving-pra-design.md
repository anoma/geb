# Polynomial-preserving presheaf PRAs: design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [1. Background](#1-background)
  - [1.1 Existing infrastructure](#11-existing-infrastructure)
  - [1.2 Terminology](#12-terminology)
- [2. Goals](#2-goals)
- [3. Intended method](#3-intended-method)
- [4. Transcription and novelty](#4-transcription-and-novelty)
- [5. Open questions and consistency checks](#5-open-questions-and-consistency-checks)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Status: brainstorming phase, part 1 (goals). This part records
the goals of the workstream and the consistency checks they must
pass. Later parts (the formula computation, design alternatives,
acceptance criteria, and non-goals) follow once the goals are
approved.

## 1. Background

### 1.1 Existing infrastructure

Two pieces of this repository ground the workstream:

- `GebLean/PresheafPRA.lean` implements parametric right adjoint
  (PRA) functors between presheaf categories in the standard form
  ([nLab: parametric right adjoint](https://ncatlab.org/nlab/show/parametric+right+adjoint)):

  ```text
  P(Z)(j) = ∐_{a ∈ A(j)} Hom_{PSh(I)}(E_j(a), Z)
  ```

  A presheaf PRA `PSh(I) ⥤ PSh(J)` is represented as an object of
  `PresheafPRACat`, that is, a functor
  `Jᵒᵖ ⥤ CoprodCovarRepCat (Iᵒᵖ ⥤ Type w_I)`: at each `j : J` a
  polynomial `(A(j), E_j)` whose directions `E_j(a)` are arbitrary
  presheaves on `I`, with the `Jᵒᵖ`-functoriality supplying
  reindexing on positions and precomposition on directions.

- `GebLean/Utilities/Families.lean` implements the free coproduct
  completion `FreeCoprodCompletionCat C` (below `FC(C)`): objects
  are pairs `(X : Type w, F : X → C)`; morphisms are a reindexing
  function together with fiberwise morphisms. Its evaluation
  `fcEval P A = Σ i : fcIndex P, (A ⟶ fcFamily P i)` realizes each
  object as a coproduct of contravariant representables, i.e. as a
  presheaf on `C` (`fcToFunctor`).

Two distinct coproduct completions therefore appear, and the
distinction is load-bearing throughout:

1. `FC(I)`, embedded in `PSh(I)` by coproducts of **contravariant
   representables of `I`** (via `fcEval` / `fcToFunctor`);
2. `CoprodCovarRepCat (PSh I)`, coproducts of **covariant
   representables of the presheaf category**, which encode the PRA
   formula's positions and directions.

Supporting facts already available: `ccrNewEvalCatFullyFaithful`
exhibits the covariant completion's evaluation as fully faithful;
`GebLean/PolyCover.lean` identifies coproducts of contravariant
representables with the regular projective objects of the
presheaf category.

### 1.2 Terminology

Throughout this document, a presheaf is **polynomial** when it is
isomorphic to a coproduct of representables — equivalently, when
it is isomorphic to a presheaf in the image of
`FC(I) → PSh(I)`. (The literature calls such presheaves
*familially representable*; see Carboni–Johnstone,
"Connected limits, familial representability and Artin glueing",
Math. Proc. Camb. Phil. Soc. 117 (1995).) A functor
`PSh(I) ⥤ PSh(J)` **preserves polynomials** when it sends
polynomial presheaves to polynomial presheaves.

## 2. Goals

The workstream aims at a restricted class of PRA functors
`PSh(I) ⥤ PSh(J)` that preserve polynomials, presented by a
positions/directions-style formula that simultaneously presents
functors `FC(I) ⥤ FC(J)`.

Per the resolutions of O5 and O6, the target signature is
`FCP(I) ⥤ FCP(J)`, where `FCP(−) = FC(FP(−))` is the free
coproduct completion of the free product completion
(`FreeCoprodProdCat`). Because `FCP` is `FC` applied to
`FP(I)`, the goals below remain stated in terms of `FC` over
general index categories; the headline instantiation takes the
index categories to be `FP(I)` and `FP(J)`, which have terminal
objects (and all small products) — the property O6 shows the
signature needs. Concretely:

- **G1 (formula category).** Define a category of
  positions/directions-style formula data — in the style of the
  polynomial-functor formula, with a shapes/positions component
  and a directions component — together with a formula for the
  morphisms (corresponding to natural transformations) between
  two such data.

- **G2 (characterization of PRA functors `FC(I) ⥤ FC(J)`).**
  Prove that the formula category of G1 is equivalent to the
  category of *PRA* functors `FC(I) ⥤ FC(J)` — not of all
  functors of that signature, which no such formula captures
  (see O1). As with polynomial functors between slice
  categories, the PRA functors form a category with a fully
  faithful inclusion into the full functor category; the
  comparison functor from the formula category to
  `FC(I) ⥤ FC(J)` is accordingly expected to be fully faithful.
  Per the resolution of O1a, the PRA subcategory is *defined* as
  the essential image of this comparison — the full subcategory
  of functors naturally isomorphic to formula-defined ones — so
  the mathematical content of G2 is the full faithfulness of the
  comparison, and the equivalence onto the PRA subcategory
  follows by definition of essential image.

- **G3 (extension to presheaf categories).** Show that each
  formula datum of G1 also induces a functor `PSh(I) ⥤ PSh(J)`,
  and that this induced functor is provably a PRA (an object of
  the `PresheafPRA.lean` infrastructure's class). The induced
  formula should simplify via the Yoneda lemma: when a direction
  is representable, `Hom_{PSh(I)}(y(i), Z) ≅ Z(i)`, collapsing
  the PRA formula's hom-objects to evaluations.

- **G4 (polynomial preservation and restriction).** Prove that
  the induced functor of G3 preserves polynomials, and that its
  restriction along the inclusions `FC(I) → PSh(I)` and
  `FC(J) → PSh(J)` recovers (up to the appropriate natural
  isomorphism) the functor `FC(I) ⥤ FC(J)` that the same datum
  presents under G2. The restriction should be expressed with
  mathlib's existing functor-restriction / lifting vocabulary
  rather than ad-hoc constructions (see O3).

- **G5 (faithfulness of the comparison).** Prove that the
  resulting comparison from the functor category
  `FC(I) ⥤ FC(J)` to the functor category `PSh(I) ⥤ PSh(J)`
  (equivalently, from the formula category into presheaf-PRAs)
  is faithful. Investigate whether it is *fully* faithful; the
  expectation is faithful with full faithfulness plausible but
  less certain, so fullness is recorded as a question to resolve,
  not a committed claim.

A prerequisite deliverable surfaced by G4/G5: `fcToFunctor` is
currently defined per object only; the workstream needs the
bundled inclusion functor `FC(C) ⥤ PSh(C)` (the contravariant
analogue of `ccrNewEvalCatFunctor`), presumably with its own
fully-faithfulness witness analogous to
`ccrNewEvalCatFullyFaithful`.

## 3. Intended method

The first task is to compute the formula of G1, guided by:

1. the nLab PRA formula, examining which constraints on its data
   (in particular on the directions `E_j(a)`) allow the induced
   functor to restrict along the `FC` inclusions; and
2. the general shape of functors between contravariant
   Grothendieck constructions (`FC` is one, by construction:
   `GrothendieckContra'` applied to `familyFunctor'`), which
   suggests what data a functor `FC(I) ⥤ FC(J)` decomposes into.

The natural first candidate for the constraint in (1) is to
require each direction `E_j(a)` to be a polynomial presheaf,
i.e. to lie in (the image of) `FC(I)` — replacing
`CoprodCovarRepCat (PSh I)` by a version whose directions range
over `FC(I)` rather than all of `PSh(I)`. Under this constraint
the Yoneda simplification of G3 applies directionwise. Whether a
further condition on the `J`-side structure is needed for the
*values* of the induced functor to be polynomial presheaves on
`J` is part of the formula computation, not settled here; see O5
for a contingency this computation may trigger.

Once the formula and its morphism formula are fixed, the order of
work is: prove the G2 equivalence; construct the G3 extension and
its PRA witness; prove G4 preservation and restriction; prove G5
faithfulness and resolve fullness.

## 4. Transcription and novelty

Per the project's citation rule, the anticipated classification
of the main definitions:

- **Transcription:** the PRA formula and its specialization
  (nLab: parametric right adjoint); familial representability and
  its relation to connected-limit preservation
  (Carboni–Johnstone 1995, above; Diers, "Catégories localisables",
  1977; Weber, "Familial 2-functors and parametric right
  adjoints", TAC 18 (2007)); the free coproduct completion
  ([nLab: free coproduct completion](https://ncatlab.org/nlab/show/free+coproduct+completion)).
- **Novel (composed from established concepts):** the specific
  formula category of G1 for functors `FC(I) ⥤ FC(J)`, its
  equivalence proof (G2), and the polynomial-preservation and
  restriction statements (G4, G5) in the forms stated here. If
  the literature search (theoremsearch, during the next part)
  finds published forms of these, they move to the transcription
  column and carry citations.

## 5. Open questions and consistency checks

- **O1 (degeneracy check on G2 + G3 — resolved).** A draft of G2
  claimed the formula captures *all* functors `FC(I) ⥤ FC(J)`.
  That fails a degeneracy check: at `I = J = 1` (the terminal
  category), `FC(1) ≃ Type w` and the inclusion
  `FC(1) → PSh(1) ≃ Type w` is an equivalence (every presheaf on
  the point is a coproduct of representables), so together with
  G3 ("every formula datum induces a PRA") every endofunctor of
  `Type w` would be isomorphic to a PRA endofunctor. That is
  false: PRAs preserve pullbacks, and the symmetric-square
  functor `X ↦ X²/σ` does not (`|Sym²(4)| = 10` against
  `|Sym²(2) × Sym²(2)| = 9` for the pullback of `2 → 1 ← 2`).
  G2 as now stated restricts the claim to PRA functors, which
  passes the check: at `I = J = 1` the PRA endofunctors of
  `Type w` are exactly the polynomial (familially representable)
  ones, matching the § 3 candidate formula's restrictions.

- **O1a (formal content of "PRA" in G2 — resolved).** The
  repository encodes presheaf PRAs by their formula data
  (`PresheafPRACat`), not as a predicate on functors; G2's
  essential-surjectivity claim ("captures all PRA functors
  `FC(I) ⥤ FC(J)`") therefore needs a definition of PRA-ness for
  such functors. Candidates considered:
  1. local right adjoint: each slice functor
     `FC(I)/x ⥤ FC(J)/F(x)` is a right adjoint — this form does
     not require a terminal object in `FC(I)` (which exists only
     for particular `I`, e.g. discrete ones);
  2. the over-a-terminal-object PRA definition, where
     applicable;
  3. defining the PRA subcategory as the essential image of the
     formula-induced comparison functor — the full subcategory
     of functors naturally isomorphic to formula-defined ones —
     proving full faithfulness only.

  Decision: candidate 3, at each level. The PRA subcategory of
  `PSh(I) ⥤ PSh(J)` is the essential image of the
  `PresheafPRACat` evaluation; the PRA subcategory of
  `FC(I) ⥤ FC(J)` is the essential image of the G1 comparison.
  G2 is thereby a fully-faithful-comparison statement. A
  predicate-based characterization (candidate 1) is out of scope
  for this workstream and available as future work.

- **O2 (fullness).** Is the comparison of G5 full as well as
  faithful? The Sym²-style examples do not decide this: fullness
  concerns natural transformations between functors already in
  the image, not the essential image.

- **O3 (restriction vocabulary).** Which mathlib mechanism
  expresses "restricts to a functor between the subcategories":
  `Functor.FullyFaithful` liftings, `ObjectProperty.lift` /
  `FullSubcategory.lift` through an essential-image property, or
  a commuting square up to a specified natural isomorphism. To be
  fixed during the next part, after checking what mathlib
  provides at the pinned version.

- **O4 (universe alignment).** `FC` carries an index universe `w`
  independent of the presheaf value universe `w_I`; the
  degeneracy check of O1 and the inclusion of G4 require these to
  be aligned (or mediated by `ULift`, as `PresheafPRA.lean`
  already does via `catULiftFunctor2`). The universe parameters
  of the formula category are part of the formula computation.

- **O5 (`FC` versus `FCP` as domain and codomain — resolved).**
  The candidate formula may produce a product that reduces to a
  coproduct of representables only when `I` (respectively `J`)
  has products, suggesting replacing `FC(−)` as domain and
  codomain by the free coproduct completion of the free product
  completion, `FreeCoprodProdCat` (below `FCP(−)`), which the
  repository already implements together with its isomorphism
  `fcpCcrsIso` to the twice-iterated covariant-representable
  construction `CoprodCovarRepSquaredCat`
  (`GebLean/Utilities/Families.lean`). `FCP` is studied in the
  literature as the category of *generalized polynomials*: free
  coproduct completions of free product completions
  (Dorta–Jarvis–Niu, arXiv:2305.05655). Decision: adopt the
  `FCP` signature as the working target. The deciding argument
  is O6 (identities force index categories with terminal
  objects, which `FP(−)` adjoins); the product-reduction concern
  above is addressed by the same move, since `FP(−)` adjoins all
  small products. To be revisited only if the `FCP` formula
  computation fails.

- **O6 (identities force the `FCP` signature — resolved).** For
  the formula-generated functors to form a category, the class
  must contain the identity functors. The identity on `PSh(I)`
  is a PRA whose positions presheaf is the terminal presheaf
  `1`. A presheaf is a coproduct of representables iff every
  connected component of its category of elements has a terminal
  object; since `el(1) ≅ I`, the terminal presheaf is polynomial
  iff every connected component of `I` has a terminal object.
  Over `I = (ℕ, ≤)` it is not, so the identity is a
  polynomial-preserving PRA violating the candidate positions
  condition ("positions in `FC(J)`"), which is therefore not
  necessary for polynomial preservation over general index
  categories. Conversely, when every component of the index
  category has a terminal object, `1` is polynomial and
  evaluation at `1` makes the positions condition exact: every
  polynomial-preserving PRA has polynomial positions. The free
  product completion adjoins a terminal object (the empty
  formal product) and all small products, so instantiating the
  index categories at `FP(I)`, `FP(J)` — the `FCP` signature —
  places the development where the positions condition is
  necessary and the identities are expressible. Composition
  closure holds on the class: `(Q ∘ P)(1) = Q(P(1))` is
  polynomial whenever both factors have polynomial positions and
  preserve polynomials. The conditions on the *directions*
  remain the open part of the formula computation.
  Implementation check recorded: audit the orientation
  convention of `FreeProdCompletionCat` against the standard
  free product completion (the terminal-object claim depends on
  the morphism direction; `FreeCoprodProdCat`'s documented
  morphism structure matches the standard generalized-polynomial
  convention).

## References

- nLab, *parametric right adjoint*:
  <https://ncatlab.org/nlab/show/parametric+right+adjoint>
- nLab, *free coproduct completion*:
  <https://ncatlab.org/nlab/show/free+coproduct+completion>
- A. Carboni, P. T. Johnstone, *Connected limits, familial
  representability and Artin glueing*, Math. Proc. Camb. Phil.
  Soc. 117 (1995), 117–158.
- Y. Diers, *Catégories localisables*, thèse, Université Paris VI
  (1977).
- M. Weber, *Familial 2-functors and parametric right adjoints*,
  Theory Appl. Categ. 18 (2007), no. 22, 665–732.
- N. Gambino, J. Kock, *Polynomial functors and polynomial
  monads*, Math. Proc. Camb. Phil. Soc. 154 (2013), 153–192.
- J. Dorta, S. Jarvis, N. Niu, *Monoidal structures on
  generalized polynomial categories*, arXiv:2305.05655 (2023).
  <https://arxiv.org/abs/2305.05655>
