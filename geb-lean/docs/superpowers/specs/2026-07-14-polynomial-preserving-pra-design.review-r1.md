# Adversarial review r1: polynomial-preserving presheaf PRAs design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [Summary of findings](#summary-of-findings)
- [Findings](#findings)
  - [F1 (MAJOR, § 6.5): the discrete-fibration parenthetical is false](#f1-major--65-the-discrete-fibration-parenthetical-is-false)
  - [F2 (MAJOR, § 1.1): overclaimed description of `PolyCover.lean`](#f2-major--11-overclaimed-description-of-polycoverlean)
  - [F3 (MAJOR, § 1.2 and References): wrong venue for Carboni–Johnstone](#f3-major--12-and-references-wrong-venue-for-carbonijohnstone)
  - [F4 (MAJOR, §§ 6.2–6.3): witness structure versus full-subcategory phrasing](#f4-major--6263-witness-structure-versus-full-subcategory-phrasing)
  - [F5 (MINOR, § 7): DJN citation for full faithfulness](#f5-minor--7-djn-citation-for-full-faithfulness)
  - [F6 (MINOR, §§ 2, 7): G5 phrased over whole functor categories](#f6-minor--2-7-g5-phrased-over-whole-functor-categories)
  - [F7 (MINOR, § 6.2): `S : Set`](#f7-minor--62-s--set)
  - [F8 (MINOR, §§ 6.2, 10): terminology resolution for § 10 item 3](#f8-minor--62-10-terminology-resolution-for--10-item-3)
  - [F9 (MINOR, § 5 O6): audit closable; a docstring conflict surfaces](#f9-minor--5-o6-audit-closable-a-docstring-conflict-surfaces)
  - [F10 (MINOR, §§ 6.4, 8): `FC(p)` is an unlisted prerequisite](#f10-minor--64-8-fcp-is-an-unlisted-prerequisite)
  - [F11 (MINOR, § 10 item 5): universe risks can be concretized](#f11-minor--10-item-5-universe-risks-can-be-concretized)
  - [F12 (MINOR, style): colloquialisms and metaphors](#f12-minor-style-colloquialisms-and-metaphors)
  - [F13 (NIT, §§ 1.1, 6): positions notation drift](#f13-nit--11-6-positions-notation-drift)
  - [F14 (NIT, References): uncited entries](#f14-nit-references-uncited-entries)
  - [F15 (NIT, § 2 G2): essential-image equivalence and computability](#f15-nit--2-g2-essential-image-equivalence-and-computability)
- [Verification record](#verification-record)
  - [Code identifiers](#code-identifiers)
  - [(a) Criterion (§ 6.1)](#a-criterion--61)
  - [(b) O6 identity-functor argument](#b-o6-identity-functor-argument)
  - [(c) O1 symmetric-square computation](#c-o1-symmetric-square-computation)
  - [(d) § 6.2 slicing reduction](#d--62-slicing-reduction)
  - [(e) No "restricted to polynomials" qualifier](#e-no-restricted-to-polynomials-qualifier)
  - [(f) Duality](#f-duality)
  - [(g) § 6.4 value-functor laws and restriction isomorphism](#g--64-value-functor-laws-and-restriction-isomorphism)
  - [(h) § 6.5 counterexamples](#h--65-counterexamples)
  - [(i) Dual-polynomiality necessity](#i-dual-polynomiality-necessity)
  - [(j) Bridge identifications](#j-bridge-identifications)
  - [Citations](#citations)
  - [Style and document mechanics](#style-and-document-mechanics)
- [Verdict](#verdict)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Review of
`docs/superpowers/specs/2026-07-14-polynomial-preserving-pra-design.md`,
round 1. Dimensions: mathematical correctness, internal
consistency, citations, constructive/formalization feasibility,
style. Sources consulted: the four referenced code files;
arXiv:2111.10968 v7 (full text); arXiv:2305.05655 (full text);
the nLab pages *parametric right adjoint* and *multi-adjoint*;
Osmond, arXiv:2012.00853; the published record of
Carboni–Johnstone 1995.

## Summary of findings

| ID | Severity | Section | Description |
| --- | --- | --- | --- |
| F1 | MAJOR | 6.5 | "p a discrete fibration (equivalent to T1 polynomial)" is false: the elements projection is a discrete fibration for every presheaf |
| F2 | MAJOR | 1.1 | Misdescribes `PolyCover.lean`: the file proves projectivity and enough-projectives, not the identification with regular projectives |
| F3 | MAJOR | 1.2, References | Carboni–Johnstone venue is wrong (MSCS 5 (1995) 441–459, not Math. Proc. Camb. Phil. Soc. 117) |
| F4 | MAJOR | 6.2, 6.3 | "Full subcategory on the multiadjoint-admitting objects" conflicts with witness-as-structure; a Prop-valued predicate would force choice in the value functor |
| F5 | MINOR | 7 | DJN Proposition 2.5 is the object-level distributive law; full faithfulness of the inclusion is DJN Proposition 2.4 |
| F6 | MINOR | 2, 7 | G5 is phrased as a comparison between whole functor categories; no such functor is defined |
| F7 | MINOR | 6.2 | `S : Set` names mathlib's subset type; the intended reading is `S : Type w` |
| F8 | MINOR | 6.2, 10 | Terminology (resolves § 10 item 3): "right multiadjoint" as a noun collides with Diers/Osmond usage; "parametric left adjoint" is not established |
| F9 | MINOR | 5 (O6) | Audit result: `FreeProdCompletionCat` matches the standard convention, but its docstring contradicts `FreeCoprodProdCat`'s |
| F10 | MINOR | 6.4, 8 | `T = FC(p) ∘ M` needs functoriality of `FC` in its argument; not listed as a prerequisite deliverable |
| F11 | MINOR | 10 | Universe risks can be concretized from the actual `Families.lean` signatures |
| F12 | MINOR | 1.1, 2, 6.2, 6.5, 8 | Colloquialisms/metaphors: "load-bearing", "headline", "heads a component", "bite", "hand-rolled" |
| F13 | NIT | 1.1, 6 | Notation drift: positions are `A(j)` in § 1.1 and `T1` in § 6 without an explicit identification |
| F14 | NIT | References | Gambino–Kock and Ahman–Uustalu are listed but never cited in the body |
| F15 | NIT | 2 (G2) | The equivalence-by-essential-image remark is only constructively harmless while it stays a Prop-level statement |

## Findings

### F1 (MAJOR, § 6.5): the discrete-fibration parenthetical is false

Quote:

> with `p` a discrete fibration (equivalent to `T1` polynomial) and
> `π` a discrete opfibration (equivalent to directions valued in
> `FC(C)`): the class refines Weber's / Spivak–Garner–Fairbanks's
> bridge presentation of PRAs (their Proposition 3.20) by making
> both inner legs discrete (op)fibrations

Problem. The projection `el(W) ⥤ D` is a discrete fibration for
*every* presheaf `W`; that is the standard equivalence between
presheaves and discrete fibrations, and it is independent of `W`
being polynomial. Spivak–Garner–Fairbanks's Proposition 3.20
itself takes `b := El_d p(1)` and `T : b → d` "the usual (étale)
projection from the category of elements" for an *arbitrary*
prafunctor — under the spec's dualization (`d = Jᵒᵖ`,
presheaves), the `p`-leg of the *general* bridge is already a
discrete fibration. Consequently:

1. "(equivalent to `T1` polynomial)" is wrong. `T1` polynomial is
   equivalent to the *further* condition that every connected
   component of the domain of `p` has a terminal object (§ 6.1
   applied to `el(T1)`), which is strictly stronger than `p`
   being a discrete fibration.
2. "refines ... by making both inner legs discrete
   (op)fibrations" misstates the refinement. Relative to the
   general presentation, only the `π`-leg condition (plus the
   right multiadjoint) is new; the `p`-leg condition changes from
   "discrete fibration" (automatic) to "discrete fibration with
   componentwise terminal domain". This also contradicts § 3
   item 3, which correctly reports that `T` is étale already in
   the general presentation.

The `π` half of the sentence is correct: for a middle leg
`e ⥤ el(T1)`, being a discrete opfibration is equivalent to the
encoded directions being coproducts of representables, i.e.
valued in `FC(C)` (a discrete opfibration over `el(T1)` is a
covariant Set-valued functor `B`, and the induced direction at
`u` is the coproduct `∐_{b ∈ B(u)} y(G(u, b))`; a general leg
yields a colimit instead, matching Remark 5.19's composite
carrier).

Suggested fix. Replace the parenthetical for `p` with: "with `p`
a discrete fibration whose domain has a terminal object in each
connected component (the fibration property makes `T1` a
presheaf; the componentwise terminals make it polynomial)", and
reword the refinement sentence to claim only the `π` condition
and the multiadjoint as refinements of Proposition 3.20.

### F2 (MAJOR, § 1.1): overclaimed description of `PolyCover.lean`

Quote:

> `GebLean/PolyCover.lean` identifies coproducts of contravariant
> representables with the regular projective objects of the
> presheaf category.

Problem. `GebLean/PolyCover.lean` proves one direction plus a
cover: `uliftYoneda_projective` (representables are projective),
`presheafCover_projective` / `presheafCoverMap_epi` /
`presheaf_enoughProjectives` (each presheaf has a projective
cover by a coproduct of representables), and the copresheaf
duals. It contains no statement that every (regular) projective
object *is* a coproduct of representables — and that converse is
not even true for general index categories without a
Cauchy-completeness hypothesis (projectives are retracts of
coproducts of representables). As grounding for a workstream
about polynomial objects, the overclaim could mislead the
implementation plan.

Suggested fix. Reword to: "`GebLean/PolyCover.lean` exhibits
coproducts of contravariant representables as regular projective
objects covering the presheaf category (projectivity and
enough-projectives; the converse identification is not
formalized)".

### F3 (MAJOR, § 1.2 and References): wrong venue for Carboni–Johnstone

Quote (References; § 1.2 carries the same venue):

> A. Carboni, P. T. Johnstone, *Connected limits, familial
> representability and Artin glueing*, Math. Proc. Camb. Phil.
> Soc. 117 (1995), 117–158.

Problem. The paper appeared in Mathematical Structures in
Computer Science 5 (1995), no. 4, 441–459 (with *Corrigenda* in
MSCS 14 (2004)). The cited venue, volume, and pages are those of
a different journal; Math. Proc. Camb. Phil. Soc. is the venue of
the (correctly cited) Gambino–Kock paper, suggesting a copy
error. Under the project's citation rule the identifier must be
searchable and correct.

Suggested fix. Replace with: "Math. Structures Comput. Sci. 5
(1995), no. 4, 441–459"; consider adding the 2004 Corrigenda,
since the corrected statements concern exactly the familial
representability material this workstream transcribes.

### F4 (MAJOR, §§ 6.2–6.3): witness structure versus full-subcategory phrasing

Quote (§ 6.3):

> The multiadjoint witnesses do not occur in morphisms: they are
> terminal objects, unique up to unique isomorphism, hence
> property-like. The formula category is therefore a full
> subcategory of the unrestricted formula category
> (`PresheafPRACat` with directions constrained to `FC(C)`) on
> the multiadjoint-admitting objects.

Problem. Two constructive hazards:

1. If "full subcategory ... on the multiadjoint-admitting
   objects" is formalized as an `ObjectProperty` /
   `FullSubcategory` over a Prop-valued predicate ("a
   multiadjoint exists"), then the value functor
   `T = FC(p) ∘ M` of § 6.4 — whose definition consumes `M` —
   cannot be defined without extracting data from a Prop,
   i.e. without `Classical.choice` in a definition, which the
   project forbids. The objects must carry the witnesses as
   structure, with the comparison to the unrestricted formula
   category a (fully faithful, generally non-injective-on-objects)
   forgetful functor rather than a subcategory inclusion. § 6.1's
   blanket "all constructions below carry chosen witnesses" says
   the right thing; § 6.3's sentence contradicts it and is the
   one an implementation plan would follow.
2. § 6.2 states the universal property as "every `φ : E(u) → Z`
   factors as `ε_ρ ∘ E(v)` for a unique pair `(ρ, v)`". Read as
   `∃!`, this is a Prop; but the factorization *assignment*
   `φ ↦ (ρ, v)` is consumed by `T(ζ)`, by `τ_Z`, and by the
   restriction isomorphism of § 6.4. The spec should say
   explicitly that the factorization map is a structure field
   (data), with the factorization equation and uniqueness as
   Prop-valued fields.

Also, the parenthetical "(`PresheafPRACat` with directions
constrained to `FC(C)`)" glosses "the unrestricted formula
category" with a phrase that itself names a restriction; name
the intermediate category (FC-directions, no multiadjoint)
explicitly.

Suggested fix. Replace the quoted sentence with a statement that
the formula category's objects are tuples carrying the
multiadjoint data, that morphisms do not mention the data, and
that the forgetful functor to the FC-directions formula category
is fully faithful (witnesses being property-like *up to unique
isomorphism* justifies fullness/faithfulness, not a subcategory
presentation). Add one sentence to § 6.2 making the factorization
assignment a field.

### F5 (MINOR, § 7): DJN citation for full faithfulness

Quote:

> the distributivity
> `Π_b Σ_x Hom(G b, F x) ≅ Σ_{r} Π_b Hom(G b, F(r b))`
> (Dorta–Jarvis–Niu Proposition 2.5), which doubles as the full
> faithfulness of the bundled inclusion `FC(C) ⥤ PSh(C)`.

Problem. DJN Proposition 2.5 states the distributive law
`Π_i Σ_j c_{i,j} ≅ Σ_{j ∈ Π J_i} Π_i c_{i,j_i}` for *objects* of
`ΣC` when `C` has products; the hom-set-level distributivity the
spec uses is the Set instance noted inside its proof. The full
faithfulness of `FC(C) ⥤ PSh(C)` is DJN Proposition 2.4 (`ΣC` is
equivalent to the full subcategory of `[Cᵒᵖ, Set]` spanned by
coproducts of representables); the hom-set formula is
Proposition 2.7.

Suggested fix. Cite Proposition 2.4 for the full faithfulness
and keep 2.5 (Set instance of Eq. (1)) for the distributivity,
or cite 2.7 for the hom-set computation.

### F6 (MINOR, §§ 2, 7): G5 phrased over whole functor categories

Quote (§ 2, G5):

> Prove that the resulting comparison from the functor category
> `FC(I) ⥤ FC(J)` to the functor category `PSh(I) ⥤ PSh(J)` ...

Problem. No functor from the full functor category
`[FC(I), FC(J)]` to `[PSh(I), PSh(J)]` is constructed anywhere in
the spec; only the composite out of the formula category exists
(as the parenthetical "(equivalently, from the formula category
into presheaf-PRAs)" concedes). § 7's chain "formula category →
`[FC(C), FC(D)]` → `[PSh(C), PSh(D)]`" has the same issue in its
second arrow. The faithfulness argument itself is sound when
stated for the composite: if two formula morphisms induce equal
presheaf-level transformations, the G4 restriction isomorphism
gives equal completion-level transformations, and G2 faithfulness
separates them.

Suggested fix. State G5 with the formula category as domain, and
present the § 7 chain as a factorization of that single functor
through its G2 image, not as composable functors between full
functor categories.

### F7 (MINOR, § 6.2): `S : Set`

Quote:

> ```text
> S : Set,  k : S → D
> ```

Problem. In this repository's Lean context `Set` is mathlib's
`Set α`. The positions object is `T1 = (S, k) ∈ FC(D)` with
`S : Type w` (`fcIndex` has type `Type w`). The code block is
informal, but the spec elsewhere tracks universes carefully
(O4, § 10 item 5), and `Type w` is what the implementation must
use.

Suggested fix. Write `S : Type w`.

### F8 (MINOR, §§ 6.2, 10): terminology resolution for § 10 item 3

Quote (§ 6.2):

> a right multiadjoint `(M, ε)` (Diers): for each `Z ∈ FC(C)`,
> an object `M(Z) = (R(Z), m_Z : R(Z) → el(T1))` of
> `FC(el(T1))` and counits `ε_ρ : E(m_Z(ρ)) → Z` ...

§ 10 item 3 assigns the terminology question to adversarial
review; findings of the literature check:

- Diers (thèse 1977; *Catégories localement multiprésentables*,
  Arch. Math. 34 (1980)) introduced the unit-sided notion: a
  functor `U` *admits a left multiadjoint* when each object under
  `U` has a small cone of local units with unique factorization.
- Osmond (arXiv:2012.00853, *On Diers theory of Spectrum I:
  stable functors and right multi-adjoints*) names such a `U` a
  *right multi-adjoint* (noun applied to the functor, as in
  "right adjoint"). The nLab page *multi-adjoint* follows the
  "admits a left multi-adjoint" phrasing.
- The equivalence with parametric right adjoints (domain with a
  terminal object, locally small codomain) is on the nLab
  *parametric right adjoint* page and the n-Category Café post
  *Parametric adjoints = multi-adjoints* (2021), after Weber
  (2007).
- *Parametric left adjoint* is not established usage in this
  literature; it occurs in the `geb-idris` comment
  (`IntEFamCat.idr` lines 152–157) as a proposed dualization,
  not as a citation.

Consequences for the spec. The spec's counit-sided data is the
dual of Diers's notion, and § 6.2's own duality paragraph
("`E` admits a right multiadjoint iff `Eᵒᵖ` admits a left
multiadjoint") is the correct bridge. However, "a right
multiadjoint" as a noun for the counit data collides with
Osmond's established noun usage, in which a *right
multi-adjoint* is the unit-sided (PRA-side) functor. A reader of
Osmond would parse the spec's term backwards.

Suggested fix. Keep the counit-sided packaging, but add a
terminological note: state the condition primarily as "`Eᵒᵖ`
admits a left multiadjoint (Diers)", record that Osmond calls
such an `Eᵒᵖ` a right multi-adjoint, avoid "parametric left
adjoint", and close § 10 item 3.

### F9 (MINOR, § 5 O6): audit closable; a docstring conflict surfaces

Quote:

> Implementation check recorded: audit the orientation
> convention of `FreeProdCompletionCat` against the standard
> free product completion ...

Resolution (from the code). `FreeProdCompletionCat` is the
covariant Grothendieck construction on
`familyFunctor' : Type w'ᵒᵖ' ⥤ Cat`, and `CategoryOp'` defines
`Hom X Y := Quiver.Hom C Y X`, so a morphism `(X, F) → (Y, G)`
unwinds to a function `u : Y → X` with fiber components
`∀ y, F(u y) ⟶ G(y)`. That is the standard free product
completion (backward reindexing, covariant fibers): the empty
family is terminal and small formal products exist, so the O6
terminal-object claim holds for the actual construction.
However, the docstring of `FreeProdCompletionCat`
(`GebLean/Utilities/Families.lean`, "Morphisms `(X, F) → (Y, G)`
consist of a function `f : X → Y` and a family of morphisms
`G(f(x)) → F(x)`") describes the *opposite* data (it is
`Hom((Y,G),(X,F))` relabelled), and contradicts the (correct)
morphism description in `FreeCoprodProdCat`'s docstring, which
matches Dorta–Jarvis–Niu Definition 2.6.

Suggested fix. Record the audit result in O6 (close the check),
and file the `FreeProdCompletionCat` docstring correction as a
separate branch per the one-concern rule.

### F10 (MINOR, §§ 6.4, 8): `FC(p)` is an unlisted prerequisite

Quote (§ 6.4):

> `T(Z) = (R(Z), p ∘ m_Z)`, i.e. `T = FC(p) ∘ M`,

Problem. `FC(p)` presupposes functoriality of the free coproduct
completion in its argument category (postcomposition on
families). The repository has `freeProdCompletionFunctor` for the
covariant completion and `GrothendieckContra'.map` for
base-preserving natural transformations — the ingredients exist
(`FC(p)` is `GrothendieckContra'.map` applied to a
`familyNatTrans'`-style transformation, subject to that
machinery's same-universe constraints) — but no bundled
`FC : Cat ⥤ Cat` or per-functor `FC(p)` is present, and § 2's
prerequisite note lists only the bundled inclusion
`FC(C) ⥤ PSh(C)`.

Suggested fix. Add `FC`'s action on functors (at least the
object-level `FC(p) : FC(A) ⥤ FC(B)` for `p : A ⥤ B`) to the
prerequisite list in § 2 or the deliverables in § 8, noting the
intended construction path.

### F11 (MINOR, § 10 item 5): universe risks can be concretized

Quote:

> **Universe parameters** (formerly O4): alignment of the `FC`
> index universe with the presheaf value universe across the
> tower and the `FP` instantiation.

Problem. Deferral to implementation planning is reasonable, but
the actual signatures already pin down two specific risks the
item could name: (a) `FreeProdCompletionCat` lands in
`Cat.{max w' v', max (w' + 1) u' w'}` — the `FP` instantiation
raises the object universe, so `C = FP(I)` is a large category
and every `∀ Z ∈ FC(C)` in the multiadjoint witnesses quantifies
over a large type, one universe above `PresheafPRACat`'s `w_I`
parameters; (b) `familyNatTrans'` / `familyBifunctor'` (the
`FC(p)` route of F10) require both categories in the same
universe pair, which `el(T1)` and `D` will generally not share
without `ULift` mediation (`catULiftFunctor2`, as
`PresheafPRA.lean` already does).

Suggested fix. Add these two concrete risk notes to item 5.

### F12 (MINOR, style): colloquialisms and metaphors

Quotes: "the distinction is load-bearing throughout" (§ 1.1);
"the headline instantiation" (§ 2 and § 6 preamble); "a universal
element `(u₀ : d₀ → k_s, φ₀)` heads a component" (§ 6.2);
"uniqueness constraints bite only at the chosen generic
elements" (§ 6.5); "not by hand-rolled object/morphism maps"
(§ 8).

Problem. `CLAUDE.md` § Style guidelines: avoid colloquialisms and
metaphors; only standard technical terms.

Suggested fix. Substitutions such as: "the distinction is used
throughout"; "the principal instantiation"; "is the terminal
object of a component isomorphic to `y_D(d₀)`"; "uniqueness
constraints apply only at the chosen generic elements"; "not by
explicit object/morphism maps".

### F13 (NIT, §§ 1.1, 6): positions notation drift

§ 1.1 writes the positions presheaf `A(j)` (following
`PresheafPRA.lean`'s docstring) and § 6 writes `T1` (following
the nLab). § 6's "(nLab's naming)" flags the switch but does not
identify the two. One sentence — "`T1` is § 1.1's `A`; the nLab
name records `T1 = T(1)`" — would remove the ambiguity.

### F14 (NIT, References): uncited entries

Gambino–Kock and Ahman–Uustalu appear in the References but are
cited nowhere in the body. Either connect them to the text (e.g.
Gambino–Kock at the polynomial-functor comparisons in G1/§ 6.3,
Ahman–Uustalu at the directed-container/`Poly` degenerate case)
or drop them.

### F15 (NIT, § 2 G2): essential-image equivalence and computability

Quote:

> the equivalence onto the PRA subcategory follows by definition
> of essential image.

This is harmless while it remains a remark: § 8 lists only full
faithfulness as a theorem. If a later plan promotes the
equivalence to a Lean `def`, mathlib's essential-image machinery
is Prop-valued and the standard fully-faithful-plus-essentially-
surjective inverse is noncomputable; the equivalence would have
to stay a Prop-level statement or carry witnesses. Worth one
clause so the implementation plan does not trip on it.

## Verification record

Claims independently checked and confirmed, with the reasoning
summarized. Item labels follow the review brief.

### Code identifiers

All identifiers cited by the spec exist and are described
accurately (except F2): `fcEval`, `fcIndex`, `fcFamily`,
`fcToFunctor` (per-object, as the spec says), `fcObjMk`,
`FreeCoprodCompletionCat`, `FreeProdCompletionCat`,
`FreeCoprodProdCat`, `CoprodCovarRepSquaredCat`, `fcpCcrsIso`,
`fcpCcrsEquiv` (`GebLean/Utilities/Families.lean`);
`coprodCovarRepFunctor`, `CoprodCovarRepCat`,
`ccrNewEvalCatFunctor`, `ccrNewEvalCatFullyFaithful` (same
file); `PresheafPRACat`, `ccrPresheafCatFunctor`,
`catULiftFunctor2` (`GebLean/PresheafPRA.lean`; the `Jᵒᵖ ⥤
CoprodCovarRepCat (Iᵒᵖ ⥤ Type w_I)` description matches the
module docstring); `GrothendieckContra'`
(`GebLean/Utilities/Grothendieck.lean`); `IntUFamIsOpEFamOp`
(`geb-idris/src/LanguageDef/IntEFamCat.idr` line 72), and the
comment at lines 152–157 does propose the right-multiadjoint /
dualization packaging the spec adopts. The `fcEval` formula
quoted in § 1.1 matches the source exactly.

### (a) Criterion (§ 6.1)

Confirmed. With the spec's orientation, `el(y(d₀))` is `D/d₀`
with terminal object `(d₀, id)`; conversely, componentwise
terminal elements `(d_k, w_k)` give a natural bijection
`W(d) ≅ ∐_k Hom_D(d, d_k)` via unique factorization through the
terminals. Smallness of the component family is carried by the
`FC` index universe, consistent with § 1.2's definition of
polynomial as "in the image of `FC(I) → PSh(I)`".

### (b) O6 identity-functor argument

Confirmed. `el(1) ≅ I` (one element per object, all morphisms).
Over `(ℕ, ≤)`: a coproduct `∐_s y(n_s)` evaluates at `m` to
`#{s : m ≤ n_s}`, which cannot be constantly 1 as `m` grows, so
`1` is not polynomial; the identity is a polynomial-preserving
PRA with non-polynomial positions, refuting necessity of the
positions condition over general index categories. With
componentwise terminals, `1` is polynomial and `P ↦ P(1)` makes
the condition exact. Composition closure: `(Q ∘ P)(1) = Q(P(1))`
is polynomial when `P(1)` is polynomial and `Q` preserves
polynomials; composites of PRAs are PRAs (Weber). Confirmed.

### (c) O1 symmetric-square computation

Confirmed. `|Sym²(n)| = n(n+1)/2`; the pullback of `2 → 1 ← 2`
is `4`, `|Sym²(4)| = 10`, while
`|Sym²(2) ×_{Sym²(1)} Sym²(2)| = 3 · 3 = 9`; the comparison map
identifies `[(0,0),(1,1)]` and `[(0,1),(1,0)]`, so pullbacks are
not preserved; PRAs preserve pullbacks (connected limits).

### (d) § 6.2 slicing reduction

Confirmed. The category of elements of the `s`-summand of `P(Z)`
has objects `(u : d → k_s, φ : E_s(u) → Z)` and morphisms over
`v` with `φ' = φ ∘ E_s(v̄)`, which is precisely the comma
`(E_s ↓ Z)`; a terminal object `(u₀ : d₀ → k_s, φ₀)` of a
component yields, by unique factorization over the discrete
fibration, a component isomorphic to `y_D(d₀)`. The reduction of
"`P(Z)` polynomial for all `Z ∈ FC(C)`" to a per-summand
condition (coproducts decompose `el` componentwise) and the
identification of that condition with the right multiadjoint
(smallness included, since `R(Z) : Type w` is part of the
structure) are correct.

### (e) No "restricted to polynomials" qualifier

Confirmed. `E_s` lands in `FC(C)`, whose objects are exactly the
(chosen-form) polynomials; polynomial presheaves in `PSh(C)` are
those isomorphic to images of `FC(C)`, and the componentwise-
terminal condition on `(E_s ↓ Z)` is invariant under isomorphism
of `Z`, so quantifying over `Z ∈ FC(C)` is equivalent to
quantifying over polynomial `Z ∈ PSh(C)`.

### (f) Duality

Confirmed. `(F ↓ G)ᵒᵖ ≅ (Gᵒᵖ ↓ Fᵒᵖ)` is the standard comma
duality; it exchanges terminal and initial objects. For the
codomain: `FC(C)ᵒᵖ`-morphisms `(X,F) → (Y,G)` are
`(g : Y → X, ∀ y, G(y) → F(g y))` in `C`, which are exactly
`FP(Cᵒᵖ)`-morphisms under the standard product-completion
convention — the convention the repository's construction
actually implements (see F9 for the docstring discrepancy).

### (g) § 6.4 value-functor laws and restriction isomorphism

Confirmed by redoing the factorization arguments. Identity law:
`id ∘ ε_ρ = ε_ρ ∘ E(id)` is a factorization, hence by uniqueness
the factorization, so `T(id) = id`. Composition: substituting
the factorization of `ζ ε_ρ` into `ζ' (ζ ε_ρ)` and factoring
again gives `(ρ'', v'_{ρ'} ∘ v_ρ)`, matching `FC`-composition
(`fcComp_fiberMor`), so `T(ζ' ζ) = T(ζ') T(ζ)`; the same
computation makes `M` functorial. Comparison morphism: the
composite `ε_ρ ∘ β_{m_Z(ρ)}` has domain `E'(el(α)(m_Z ρ))`, and
`el(α)` preserves the underlying `D`-object, so `p(v)` has the
required source; naturality reduces to uniqueness plus
naturality of `β`. Restriction isomorphism: `(ρ, w)` lifts along
the discrete fibration to `w̄ : u → m_Z(ρ)` and maps to
`(u, ε_ρ ∘ E(w̄))`; the inverse factors `(a, φ)` and projects
`p(v)`; round trips are the uniqueness clauses. The identity
instance gives `M(Z) ≅ Z`, `T ≅ Id`. All confirmed (modulo F4:
each "unique factorization" must be a data-valued field).

### (h) § 6.5 counterexamples

All recomputed and confirmed, over the arrow category
`𝟚 = {a → b}` (slice with terminal `b`):

- A presheaf `W` on `𝟚` is polynomial iff its restriction
  `W(b) → W(a)` is injective (coproducts of `y(a)`, `y(b)`
  give `B ↪ A ⊔ B`).
- `Hom_{FC(C)}(E_s(u), X·y(1_C)) ≅ X^{B_s(u)}` (the fiber
  components into a terminal object contribute nothing), so the
  test family isolates `B_s`; `X^{B(b)} → X^{B(a)}` is
  precomposition with the transition `t : B(a) → B(b)` and is
  injective for all `X` iff `t` is surjective (epi). The
  `X = ∅` case gives the characteristic presheaf of the
  downward-closed `{u : B(u) = ∅}`, polynomial iff that
  subcategory has componentwise terminals.
- `B = (2 → 1)` passes: the transition is epi, and the full
  multiadjoint condition holds (with `C = 1`: non-constant
  `(a, φ)` are their own components' terminals; each `(b, z)`
  is terminal in the component `{(a, const_z), (b, z)}`).
  Coproducts of corepresentables on `𝟚` are `m·Hom(a,−) ⊔
  n·Hom(b,−)` with injective transition `m ↪ m + n`, so
  `B = (2 → 1)` is not one: coproduct-of-corepresentables is
  not necessary.
- `B = Hom(T,−) = Hom(b,−) = (∅ → 1)` fails: for `|Z| ≥ 2` the
  single component of `(B ↓ Z)` contains `(a, !)` mapping to
  every `(b, z)` with no terminal object (equivalently the
  `X`-test fails: `X → 1` non-injective); so
  coproduct-of-corepresentables is not sufficient.
- `B = 1`, `G = (g : c_a → c_T)`: testing with `Z = y(c)` gives
  the presheaf `(Hom(c_T, c) → Hom(c_a, c))` by precomposition
  with `g`, injective for all `c` iff `g` is epi.

### (i) Dual-polynomiality necessity

Confirmed (part of (h)): `X·y(1_C) ∈ FC(C)` requires `1_C`,
which the FCP signature supplies, and the evaluation collapse
`Hom(E_s(u), X·y(1_C)) ≅ X^{B_s(u)}` holds because the direction
components map into a terminal object.

### (j) Bridge identifications

`π` a discrete opfibration ⟺ directions valued in `FC(C)`:
confirmed (fiberwise-discrete middle leg makes the encoded
direction a coproduct of representables; a general leg gives a
colimit, per SGF Remark 5.19). `p` a discrete fibration ⟺
positions polynomial: refuted; see F1.

### Citations

- SGF arXiv:2111.10968 (v7, matching JPAA 2025,
  doi:10.1016/j.jpaa.2025.107883): Proposition 3.6 (Set[c] ≃
  Fam((c-Set)ᵒᵖ) ≃ CLP ≃ PRA), Definition 3.7, Proposition 3.8,
  Proposition 3.9 (item (3) is "functors d → Fam((c-Set)ᵒᵖ)",
  matching § 4's `PresheafPRACat` claim), Proposition 3.11
  (combinatorial description of natural transformations; a sum
  over `φ1 : p(1) → q(1)` of an end over `El p(1)` — the § 6.3
  transcription anchor is apt), Proposition 3.20 (bridge
  `Σ_T ∘ Π_π ∘ Δ_S`, `T` étale, citing [10] = Weber TAC 18
  (2007) 665–732), Theorem 4.28 (equipment equivalence
  `Cat♯ ≃ Comod(Poly)`), Remark 5.19 (composite carrier with a
  `colim`, supporting § 3 item 3). All verified against the
  paper text.
- § 4's novelty check "neither cites Carboni–Johnstone or
  Diers": verified for both arXiv:2111.10968 and
  arXiv:2305.05655 bibliographies.
- DJN arXiv:2305.05655: Proposition 2.5 verified (see F5 for
  the sharper attribution); Definition 2.6's morphism structure
  matches `FreeCoprodProdCat`'s documented structure, as O6
  states.
- nLab *parametric right adjoint*: uses `T1` and
  `E_T : el(T1)ᵒᵖ → [Iᵒᵖ, Set]`, so § 6's "op that cancels
  nLab's `el(T1)ᵒᵖ` convention" is accurate.
- Weber TAC 18 (2007), no. 22, 665–732: matches SGF's [10].
- Carboni–Johnstone: venue wrong; see F3.
- Diers terminology: see F8 (resolves § 10 item 3).

### Style and document mechanics

Doctoc TOC present and current (all `##`/`###` headings listed).
No placeholder text. No lines over 80 columns except
doctoc-generated lines and long URLs (exempt in practice). No
value-laden adjectives found; colloquialisms listed in F12.
Generic user references maintained ("user-approved").

## Verdict

The core mathematics — the criterion, the slicing reduction to a
right multiadjoint, the value functor and restriction
isomorphism, the counterexample suite, and the FCP-signature
argument — is correct as stated and was reproduced independently.
The four MAJOR findings are localized: one false parenthetical in
the descriptive bridge subsection (F1), one overclaimed
description of existing code (F2), one wrong bibliographic venue
(F3), and one phrasing whose literal formalization would violate
the constructive rule (F4). Concrete replacement text is supplied
for each. The spec is ready for user review after the listed
findings are fixed, with a targeted re-check of the amended
§ 6.3 and § 6.5 paragraphs; a full second adversarial round is
not required.
