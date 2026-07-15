# Polynomial-preserving presheaf PRAs: design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [1. Background](#1-background)
  - [1.1 Existing infrastructure](#11-existing-infrastructure)
  - [1.2 Terminology](#12-terminology)
- [2. Goals](#2-goals)
- [3. Method](#3-method)
- [4. Transcription and novelty](#4-transcription-and-novelty)
- [5. Decision record](#5-decision-record)
- [6. The formula](#6-the-formula)
  - [6.1 Criterion](#61-criterion)
  - [6.2 Objects](#62-objects)
  - [6.3 Morphisms](#63-morphisms)
  - [6.4 The value functor and the comparison](#64-the-value-functor-and-the-comparison)
  - [6.5 Bridge form and elementary conditions](#65-bridge-form-and-elementary-conditions)
- [7. Proof obligations and strategies](#7-proof-obligations-and-strategies)
- [8. Acceptance criteria](#8-acceptance-criteria)
- [9. Non-goals](#9-non-goals)
- [10. Open questions](#10-open-questions)
- [References](#references)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Status: brainstorming phase, complete draft. Part 1 (goals,
§§ 1–5) is user-approved; part 2 (the formula and its
validation, §§ 6–10) is computed and promoted from working
notes. Pending: adversarial review, then user review, before an
implementation plan is written.

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
distinction is used throughout:

1. `FC(I)`, embedded in `PSh(I)` by coproducts of **contravariant
   representables of `I`** (via `fcEval` / `fcToFunctor`);
2. `CoprodCovarRepCat (PSh I)`, coproducts of **covariant
   representables of the presheaf category**, which encode the PRA
   formula's positions and directions.

Supporting facts already available: `ccrNewEvalCatFullyFaithful`
exhibits the covariant completion's evaluation as fully faithful;
`GebLean/PolyCover.lean` exhibits coproducts of contravariant
representables as regular projective objects covering the
presheaf category (projectivity and enough-projectives; the
converse identification is not formalized).

### 1.2 Terminology

Throughout this document, a presheaf is **polynomial** when it is
isomorphic to a coproduct of representables — equivalently, when
it is isomorphic to a presheaf in the image of
`FC(I) → PSh(I)`. (The literature calls such presheaves
*familially representable*; see Carboni–Johnstone,
"Connected limits, familial representability and Artin glueing",
Math. Structures Comput. Sci. 5 (1995), no. 4, 441–459.) A functor
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
general index categories; the principal instantiation takes the
index categories to be `FP(I)` and `FP(J)`, which have terminal
objects (and all small products) — the property O6 shows the
signature needs. Concretely:

- **G1 (formula category).** Define a category of
  positions/directions-style formula data — in the style of the
  polynomial-functor formula, with a shapes/positions component
  and a directions component — together with a formula for the
  morphisms (corresponding to natural transformations) between
  two such data. The computed formula and its validation are in
  § 6.

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
  follows by definition of essential image; that equivalence
  remains a Prop-level remark (mathlib's essential-image
  machinery is Prop-valued, and a bundled equivalence would
  require carried witnesses), and § 8 lists only the full
  faithfulness as a theorem.

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
  functor from the formula category to the functor category
  `PSh(I) ⥤ PSh(J)` given by G3's extension is faithful, and
  that it factors through G2's comparison via the G4 restriction
  isomorphism. Investigate whether it is *fully* faithful;
  fullness coincides with G2's computation (§ 7).

Two prerequisite deliverables surfaced by the goals:
`fcToFunctor` is currently defined per object only, and the
workstream needs the bundled inclusion functor `FC(C) ⥤ PSh(C)`
(the contravariant analogue of `ccrNewEvalCatFunctor`) with a
fully-faithfulness witness analogous to
`ccrNewEvalCatFullyFaithful`; and the action of `FC` on functors,
`FC(p) : FC(A) ⥤ FC(B)` for `p : A ⥤ B`, consumed by the value
functor of § 6.4 (constructible from `GrothendieckContra'.map`
and the `familyNatTrans'` machinery, subject to that machinery's
same-universe constraints; see § 10 item 4).

## 3. Method

The derivation of § 6 draws on three sources:

1. the nLab PRA formula, examining which constraints on its data
   (in particular on the directions `E_j(a)`) allow the induced
   functor to restrict along the `FC` inclusions; and
2. the general shape of functors between contravariant
   Grothendieck constructions (`FC` is one, by construction:
   `GrothendieckContra'` applied to `familyFunctor'`), which
   suggests what data a functor `FC(I) ⥤ FC(J)` decomposes
   into; and
3. the bicomodule packaging of the unrestricted class
   (Spivak–Garner–Fairbanks, arXiv:2111.10968): its
   composite-carrier formula (their Remark 5.19) locates where
   composition can leave the restricted class — directions of
   composites are colimits, not mere coproducts, of direction
   presheaves — and its bridge decomposition of every PRA as
   `Σ_T ∘ Π_π ∘ Δ_S` along `c ← e → b → d` with `T` étale
   (their Proposition 3.20, after Weber 2007) offers a
   compositional presentation on which the restriction may be
   expressible as a condition on the bridge.

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

The proof obligations that remain after the derivation, with
their strategies, are collected in § 7.

## 4. Transcription and novelty

Per the project's citation rule, the anticipated classification
of the main definitions:

- **Transcription:** the PRA formula and its specialization
  (nLab: parametric right adjoint); familial representability and
  its relation to connected-limit preservation
  (Carboni–Johnstone 1995, above; Diers, "Catégories localisables",
  1977; Weber, "Familial 2-functors and parametric right
  adjoints", TAC 18 (2007)); the free coproduct completion
  ([nLab: free coproduct completion](https://ncatlab.org/nlab/show/free+coproduct+completion));
  the *unrestricted* formula category and its equivalence with
  the category of PRA functors between copresheaf categories,
  with all natural transformations, as a full subcategory of the
  functor category (Spivak–Garner–Fairbanks, arXiv:2111.10968:
  Definition 3.7, Propositions 3.6, 3.8, 3.9, Theorem 4.28 —
  this repository's `PresheafPRACat` matches their functors
  `d → Fam((c-Set)ᵒᵖ)` under the dualization `c = Iᵒᵖ`,
  `d = Jᵒᵖ`); their Proposition 3.11 end formula is the
  candidate transcription source for the natural-transformation
  formula of G1.
- **Novel (composed from established concepts):** the
  polynomial-preservation refinement — the restricted formula
  category of G1, its equivalence proof (G2), and the
  preservation and restriction statements (G4, G5). Literature
  search (2026-07-14): the refinement, and the restriction of
  the argument categories to free completions, are absent from
  arXiv:2305.05655 and arXiv:2111.10968 and from their
  bibliographies (neither cites Carboni–Johnstone or Diers);
  they remain novel in the forms stated here.

## 5. Decision record

This section records the questions raised during goal-setting
and their dispositions. O1, O1a, O5, and O6 are resolved below;
O2 is subsumed by the G2 obligation (§ 7, where G2's and G5's
fullness are identified); O3 and O4 are carried forward as § 10
items 3 and 4.

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
  Audit result (review r1): `FreeProdCompletionCat` implements
  the standard free product completion (backward reindexing,
  covariant fibers; the empty family is terminal, so the
  terminal-object claim above holds for the actual
  construction), but its docstring describes the opposite data
  and contradicts `FreeCoprodProdCat`'s docstring, which matches
  Dorta–Jarvis–Niu Definition 2.6; the docstring correction is
  deferred to a separate branch per the one-concern rule.

- **O7 (relation to positive inductive-recursive definitions —
  resolved: distinct classes).** Ghani–Malatesta–Nordvall
  Forsberg (LMCS 11(1:13), 2015) define IR⁺ codes decoding to
  endofunctors of `Fam(C) = FC(C)` for arbitrary `C` (their
  Definition 3.1, Theorem 3.3), generalizing Dybjer–Setzer's
  discrete theory, with initial algebras under a Mahlo
  assumption when `C` has connected colimits (their
  Theorem 7.2). Comparison with this workstream's class:
  1. The `δ`-clause `Σ_{g : A→X} ⟦F(P∘g)⟧(X,P)` extends to
     presheaves by a coend over the label category,
     `∫^{ℓ∈C^A} Π_a Z(ℓ(a)) × ⟦F(ℓ)⟧⁺(Z)`, and co-Yoneda shows
     this extension restricts to the paper's semantics on
     `FC(C)`, on objects and on morphisms.
  2. The extension is not PRA in general, and some IR⁺ functors
     admit no PRA extension at all: over `C = BG` (`|G| ≥ 2`)
     the code `δ_1(const(ι ⋆))` decodes to the label-erasing
     functor `free ∘ π₀`, while every PRA acts on morphisms by
     post-composition, so naturality against right translations
     forces `g = e`. The classes therefore diverge; this answers
     a question the paper's § 8 lists as future work (the
     relationship of IR⁺ to Weber's familial 2-functors).
  3. Composition of IR⁺ codes is an open problem (their § 8),
     and the interpretation `⟦−⟧` is not full and faithful for
     non-discrete `C` (their § 3) — both properties the G1
     formula is designed to have.
  4. At discrete index categories the two theories coincide on
     the polynomial core (their Proposition 6.2);
     initial-algebra existence (their Theorem 7.2) is an
     accessibility property and does not certify polynomiality.

  Decision: the G1 formula remains the definition; IR⁺ is
  recorded as a companion theory, with the hom-labelled
  sub-syntax question carried as § 10 item 5. The discrete IR
  syntax formalized in `geb-mathlib`
  (`Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`) is related
  infrastructure for the shared polynomial core.

## 6. The formula

Index categories are written `C`, `D`; the principal instantiation
is `C = FP(I)`, `D = FP(J)` (§ 2). The elements category `el(W)`
of a presheaf `W` is oriented so that a morphism
`(d', w·v) → (d, w)` lies over `v : d' → d`; mathlib's
`Functor.Elements` yields the opposite orientation, so Lean
statements carry an `op` that cancels nLab's `el(T1)ᵒᵖ`
convention.

### 6.1 Criterion

A presheaf is polynomial iff every connected component of its
category of elements has a terminal object (a *universal
element*); a chosen family of universal elements determines the
decomposition into representables. All constructions below carry
chosen witnesses; nothing appeals to mere existence, keeping the
development constructive.

### 6.2 Objects

A formula datum consists of:

- **Positions** `T1 ∈ FC(D)` (nLab's naming; `T1` is § 1.1's
  `A`, and the name records that it is the value of the induced
  functor at the terminal presheaf), `T1 = (S, k : S → D)`;
- **Directions** `E : el(T1) ⥤ FC(C)`, equipped with
- **multiadjunction witnesses** `(M, ε)`: for each `Z ∈ FC(C)`,
  an object `M(Z) = (R(Z), m_Z : R(Z) → el(T1))` of
  `FC(el(T1))`, counits `ε_ρ : E(m_Z(ρ)) → Z`, and a
  factorization assignment sending each `φ : E(u) → Z` to a pair
  `(ρ, v : u → m_Z(ρ))` with `φ = ε_ρ ∘ E(v)`, together with
  Prop-valued fields stating that the assignment is the unique
  such factorization. The factorization assignment is a
  structure field (data), not an `∃!`: it is consumed by the
  value functor, the comparison, and the restriction isomorphism
  (§ 6.4).

Terminology. This counit-sided data is dual to Diers's left
multiadjoint: equivalently (duality paragraph below), `Eᵒᵖ`
admits a left multiadjoint (Diers 1977). Osmond
(arXiv:2012.00853) calls a functor admitting a left multiadjoint
a *right multi-adjoint*; to avoid collision with that noun usage
this document says *multiadjunction witnesses* for the data and
*multiadjunction condition* for their existence, and does not
use "parametric left adjoint", which is not established usage.

Since `T1` is polynomial, `el(T1) ≅ ∐_{s∈S} D/k_s` is a coproduct
of slices, and a functor into the Grothendieck construction
`FC(C)` is a base copresheaf with a `C`-valued functor on its
elements, so the datum unpacks to the tower

```text
S : Type w,  k : S → D
per s ∈ S:  B_s : D/k_s → Set,   G_s : el(B_s) ⥤ C,
            multiadjunction witnesses for E_s = (B_s, G_s)
```

with the multiadjunction condition decomposing per position (comma
categories decompose over the components of `el(T1)`).

Rationale (derivation summary). With `P` the induced presheaf
functor (§ 6.4), the category of elements of the `s`-summand of
`P(Z)` is the comma category `(E_s ↓ Z)` over `D/k_s`, and a
universal element `(u₀ : d₀ → k_s, φ₀)` is the terminal object
of a component isomorphic to `y_D(d₀)`; hence `P` preserves polynomials iff each
presheaf `Hom(E_s(−), Z)` is polynomial over its slice. The slice
has a terminal object (`id_{k_s}`), so this says the
positions-trivial PRA `Z ↦ Hom(E_s(−), Z)` is
polynomial-preserving, and that condition — every component of
`(E_s ↓ Z)` has a terminal object, for every `Z ∈ FC(C)` — is
verbatim the multiadjunction condition for `E_s`. No
"restricted to polynomials" qualifier arises: `FC(C)` is the
codomain of `E_s`. Verified instances: `E = y` (the identity
functor; `(y ↓ Z) ≅ el(Z)`), constant `E`, and arrow-like slices
(where the condition reduces to epimorphy of `B`'s transitions).

Duality: `(E ↓ Z)ᵒᵖ ≅ (Z ↓ Eᵒᵖ)` exchanges terminal with initial
objects, so the multiadjunction condition for `E` says exactly that
`Eᵒᵖ : el(T1)ᵒᵖ ⥤ FC(C)ᵒᵖ = FP(Cᵒᵖ)` admits a left multiadjoint (Diers);
the codomain identification is the `FC`/`FP` duality implemented
in the `geb-idris` prototype (`IntUFamIsOpEFamOp`,
`geb-idris/src/LanguageDef/IntEFamCat.idr`, whose comment at
lines 152–157 proposes the witness packaging adopted here).

### 6.3 Morphisms

A morphism `(T1, E, M) ⟶ (T1', E', M')` is a pair

- `α : T1 → T1'` in `FC(D)` (forward on positions), and
- `β : E' ∘ el(α) ⟶ E`, natural over `el(T1)` (backward on
  directions, componentwise in `FC(C)`, which is full in
  `PSh(C)`),

with whiskered composition. The multiadjunction witnesses do not
occur in morphisms: they are terminal objects, unique up to
unique isomorphism, hence property-like. The objects nonetheless
carry the witnesses as structure (§ 6.2) — a Prop-valued
existence predicate would force choice in the § 6.4 value
functor — so the formula category relates to the intermediate
category of `FC(C)`-directed data without witnesses (the
unrestricted formula category with directions constrained along
`FC(C) ⥤ PSh(C)`) by a fully faithful forgetful functor, not by
a full-subcategory inclusion. At `C = D = 1` the morphism
formula reduces to `Poly`-morphisms, and the discrete
instantiation recovers Gambino–Kock's morphisms of polynomials.
Transcription anchor: Spivak–Garner–Fairbanks Proposition 3.11.

### 6.4 The value functor and the comparison

The datum induces:

- **On presheaf categories** (G3):
  `P(Z)(d) = Σ_{a ∈ T1(d)} Hom(E(d,a), Z)` — the unrestricted PRA
  formula with directions included along `FC(C) ⥤ PSh(C)`.
- **On the completions** (G2), with `p : el(T1) ⥤ D` the
  projection:

  `T(Z) = (R(Z), p ∘ m_Z)`, i.e. `T = FC(p) ∘ M`,

  where for `ζ : Z → Z'` each `ζ ∘ ε_ρ` factors uniquely as
  `ε'_{ρ'} ∘ E(v_ρ)` and `T(ζ) = (ρ ↦ ρ', p(v_ρ))`. The functor
  laws for `T` (hence the functoriality of `M`, which is derived,
  not assumed) follow from uniqueness of factorizations.

- **The comparison** sends a formula morphism `(α, β)` to
  `τ : T ⟹ T'` with `τ_Z(ρ)` the unique factorization of
  `ε_ρ ∘ β_{m_Z(ρ)}` through `M'`'s generics (well-typed because
  `el(α)` preserves the underlying `D`-object); naturality in `Z`
  and functoriality in `(α, β)` again follow from uniqueness of
  factorizations, using the naturality of `β` essentially.

- **The restriction isomorphism** (G4):
  `fcEval(T(Z))(d) ≅ P(Z)(d)`, sending `(ρ, w : d → p(m_Z(ρ)))`
  to the element `(u, φ)` it uniquely factors — a bijection
  natural in both `d` and `Z`, validated by the same
  factorization algebra. The identity instance (`E = y`) gives
  `M(Z) ≅ Z` and `T ≅ Id`.

### 6.5 Bridge form and elementary conditions

Assembling projections exhibits a formula datum as the bridge

```text
C  ⟵G—  el(B)  —π⟶  el(T1)  —p⟶  D
```

with `p` a discrete fibration whose domain has a terminal object
in each connected component (the fibration property makes `T1` a
presheaf — it holds for every PRA; the componentwise terminals
are what make `T1` polynomial) and `π` a discrete opfibration
(equivalent to directions valued in `FC(C)`). Relative to
Weber's / Spivak–Garner–Fairbanks's bridge presentation of PRAs
(their Proposition 3.20), the refinements are therefore the
componentwise-terminal condition on `p`'s domain, the `π`
condition, and the multiadjunction condition; the last is not
implied by the first two (arrow-like slices with non-epi
`B`-transitions fail).

Elementary necessary conditions on the tower, on the FCP
signature (`C = FP(I)` has a terminal object `1_C`):

- **Dual-polynomiality of `B_s`** (`G`-independent): the test
  objects `Z = X·y(1_C)` collapse the evaluation to
  `X^{B_s(−)}`, so the presheaf `X^{B_s(−)}` on `D/k_s` must be
  polynomial for every set `X`. On arrow-like slices this reads
  "transitions of `B_s` are epi"; its `X = ∅` case says the
  sub-sieve `{u : B_s(u) = ∅}` has component-terminals. `B_s`
  being a coproduct of corepresentables is neither necessary
  (the passing `B = (2 → 1)` has a non-injective transition)
  nor sufficient (`B = Hom(T, −)` fails).
- **Epi conditions on `G_s`**: with `B = 1` over an arrow-like
  slice and `G = (g : c_a → c_T)`, the representable tests
  `Z = y(c)` force `g` to be an epimorphism in `C`.

Whether these two test families jointly generate the full
multiadjunction condition is open (§ 10); no purely morphismwise
closed form exists (the Yoneda instance passes while violating
injectivity of restrictions, and uniqueness constraints apply only
at the chosen generic elements).

## 7. Proof obligations and strategies

- **G2 (full faithfulness of the comparison).** Strategy:
  recover `(α, β)` from `τ : T ⟹ T'` by evaluating at the
  objects `Z = E(u)` (available at the completion level) and
  using the unit-like factorization `id_{E(u)} = ε_{ρ₀} ∘ E(v₀)`
  — generic elements retract identities. G2's fullness and G5's
  fullness are the same computation (this subsumes O2).
- **G3 (extension and PRA witness).** The extension is the same
  datum read in the unrestricted formula category via
  `FC(C) ⥤ PSh(C)`; PRA-ness holds by construction under the
  essential-image definition (O1a). The Yoneda simplification is
  the distributivity
  `Π_b Σ_x Hom(G b, F x) ≅ Σ_{r} Π_b Hom(G b, F(r b))`
  (the Set instance of Dorta–Jarvis–Niu Proposition 2.5; their
  Proposition 2.7 is the hom-set formula); the full faithfulness
  of the bundled inclusion `FC(C) ⥤ PSh(C)` is their
  Proposition 2.4 and is proved by the same computation.
- **G4 (restriction isomorphism).** Validated at the formula
  level (§ 6.4); to be formalized with mathlib's restriction /
  lifting vocabulary (§ 10, item 4).
- **G5 (faithfulness).** The G3 functor out of the formula
  category factors, via the G4 restriction isomorphism, through
  the G2 comparison; if two formula morphisms induce equal
  presheaf-level transformations, the restriction isomorphism
  gives equal completion-level transformations, and G2's
  faithfulness separates them. Fullness is G2's computation.

## 8. Acceptance criteria

- Lean deliverables, all constructive (no `noncomputable`) and
  passing the axiom gate (`lake build GebLeanAxiomChecks`):
  1. the bundled inclusion functor `FC(C) ⥤ PSh(C)` with a
     `Functor.FullyFaithful` witness (the contravariant analogue
     of `ccrNewEvalCatFunctor` / `ccrNewEvalCatFullyFaithful`);
  2. the formula category of § 6.2–6.3, built by applying the
     existing `coprodCovarRepFunctor` / `ccrPresheafCatFunctor`
     machinery to `FC(C)` and whiskering along the inclusion —
     not by explicit hand-written object/morphism maps;
  3. the action of `FC` on functors
     (`FC(p) : FC(A) ⥤ FC(B)` for `p : A ⥤ B`, via
     `GrothendieckContra'.map` on a `familyNatTrans'`-style
     transformation), the value functor `T = FC(p) ∘ M`, and the
     comparison functors of § 6.4;
  4. the instantiation at `C = FP(I)`, `D = FP(J)` via
     `FreeCoprodProdCat`.
- Theorems: G2 full faithfulness; G3 PRA witness and Yoneda
  simplification; G4 restriction natural isomorphism; G5
  faithfulness.
- Tests under `GebLeanTests/` exercising the `C = D = 1`
  instance (recovering `Poly`) and the identity instance.
- This spec passes adversarial review before an implementation
  plan is written.

## 9. Non-goals

- A predicate-based (local-right-adjoint) characterization of
  PRA-ness: excluded by the O1a decision; future work.
- Composition and bicategory structure of the formula categories
  across three index categories (the framed-bicategory analogue
  of Spivak–Garner–Fairbanks): the composition-closure argument
  is recorded (O6) but no bicategorical structure is a
  deliverable.
- The test-family generation theorem (§ 10, item 1): an
  optimization of the witness structure, not required for
  G1–G5.
- Monoidal structures on `FCP` (Dorta–Jarvis–Niu's `⊗`, `◁`).

## 10. Open questions

1. **Test-family generation**: whether the multiadjunction
   condition's `∀ Z` reduces to the families `{X·y(1_C)}`
   (isolating `B_s`) and `{y(c)}` (isolating `G_s`), turning the
   condition into a finite elementary checklist; over arrow-like
   slices with `C = 1` the full condition is already detected by
   `Z ∈ {∅, 2}`. Owner: implementation phase (pursue if the
   witness structure proves heavy).
2. **Bridge-intrinsic multiadjunction condition**: a statement
   of the multiadjunction condition in terms of the bridge legs
   alone. Owner: future work.
3. **Restriction vocabulary** (formerly O3): which mathlib
   mechanism expresses the G4 restriction (lifting through
   `Functor.FullyFaithful` / essential-image machinery). Owner:
   implementation planning.
4. **Universe parameters** (formerly O4): alignment of the `FC`
   index universe with the presheaf value universe across the
   tower and the `FP` instantiation. Two concrete risks from the
   present signatures: `FreeProdCompletionCat` raises the object
   universe (`Cat.{max w' v', max (w' + 1) u' w'}`), so
   `C = FP(I)` is a large category and the multiadjunction
   witnesses' `∀ Z ∈ FC(C)` quantifies one universe above
   `PresheafPRACat`'s parameters; and the `familyNatTrans'` /
   `familyBifunctor'` machinery behind `FC(p)` requires both
   categories in the same universe pair, which `el(T1)` and `D`
   in general share only after `ULift` mediation
   (`catULiftFunctor2`, as `PresheafPRA.lean` already uses).
   Owner: implementation planning.

5. **Hom-labelled IR⁺ sub-syntax** (from O7): whether
   restricting IR⁺ `δ`-continuations to hom-labelled forms —
   label consumption through `Hom_C(c, −)` filters and
   hom-arities, or covariant pass-through to outputs, with no
   label discarding — yields a witness-free inductive
   presentation of a PRA-extendable subclass of the G1 class.
   Classification so far: the restriction admits identities,
   constants, coproducts, products, evaluations, the
   container/nested-type apparatus (their § 5), and the
   Σ-universe examples over `Set` and `Setᵒᵖ` (bare
   element-choice acquires a hom-surrogate at an initial
   object); it rules out label-discarding `π₀`-nodes over
   categories without componentwise initial objects — hence the
   groupoid-based examples (their § 4.1 normal-forms universe
   over `Fam(Set≅)`) and the Π-universe. Bare element-choice
   has a hom-surrogate agreeing on polynomials iff every
   connected component of `C` has an initial object (the dual
   of the O6 terminal condition); `FP(I)` does not supply this
   automatically, so over the FCP signature the sub-syntax is
   strictly weaker than IR⁺ — as required, since the excluded
   functors are not PRA. Owner: future work.

The terminology question formerly listed here (Diers's usage for
the dual notion) was resolved during adversarial review r1; the
resolution is recorded in § 6.2.

## References

- nLab, *parametric right adjoint*:
  <https://ncatlab.org/nlab/show/parametric+right+adjoint>
- nLab, *free coproduct completion*:
  <https://ncatlab.org/nlab/show/free+coproduct+completion>
- A. Carboni, P. T. Johnstone, *Connected limits, familial
  representability and Artin glueing*, Math. Structures Comput.
  Sci. 5 (1995), no. 4, 441–459; *Corrigenda*, Math. Structures
  Comput. Sci. 14 (2004), no. 1, 185–187.
- Y. Diers, *Catégories localisables*, thèse, Université Paris VI
  (1977).
- M. Weber, *Familial 2-functors and parametric right adjoints*,
  Theory Appl. Categ. 18 (2007), no. 22, 665–732.
- N. Gambino, J. Kock, *Polynomial functors and polynomial
  monads*, Math. Proc. Camb. Phil. Soc. 154 (2013), 153–192.
- J. Dorta, S. Jarvis, N. Niu, *Monoidal structures on
  generalized polynomial categories*, arXiv:2305.05655 (2023).
  <https://arxiv.org/abs/2305.05655>
- D. I. Spivak, R. Garner, A. D. Fairbanks, *Functorial
  aggregation*, J. Pure Appl. Algebra (2025),
  doi:10.1016/j.jpaa.2025.107883. arXiv:2111.10968.
  <https://arxiv.org/abs/2111.10968>
- A. Osmond, *On Diers theory of Spectrum I: stable functors and
  right multi-adjoints*, arXiv:2012.00853 (2020).
  <https://arxiv.org/abs/2012.00853>
- N. Ghani, L. Malatesta, F. Nordvall Forsberg, *Positive
  inductive-recursive definitions*, Log. Methods Comput. Sci. 11
  (2015), no. 1:13. doi:10.2168/LMCS-11(1:13)2015.
- P. Dybjer, A. Setzer, *Induction–recursion and initial
  algebras*, Ann. Pure Appl. Logic 124 (2003), no. 1–3, 1–47.
