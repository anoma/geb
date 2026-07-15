# Adversarial review r2: polynomial-preserving presheaf PRAs design

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Summary of findings](#summary-of-findings)
- [Findings](#findings)
  - [F16 (MAJOR, § 5 O7): the duality parenthetical misassigns the input-side repair](#f16-major--5-o7-the-duality-parenthetical-misassigns-the-input-side-repair)
  - [F17 (MAJOR, § 5 O7 item 2): the counterexample argument omits empty directions](#f17-major--5-o7-item-2-the-counterexample-argument-omits-empty-directions)
  - [F18 (MINOR, § 10 item 5): non-PRA claim over `FP(I)` exceeds the recorded arguments](#f18-minor--10-item-5-non-pra-claim-over-fpi-exceeds-the-recorded-arguments)
  - [F19 (MINOR, § 5 preamble): O7 missing from the disposition list](#f19-minor--5-preamble-o7-missing-from-the-disposition-list)
  - [F20 (MINOR, §§ 5, 8, style): colloquialisms and metaphors in the new text](#f20-minor--5-8-style-colloquialisms-and-metaphors-in-the-new-text)
  - [F21 (NIT, § 5 O7): "§ 4.1" is not a subsection of the paper](#f21-nit--5-o7--41-is-not-a-subsection-of-the-paper)
  - [F22 (NIT, § 5 O7 item 3): full-faithfulness attribution and its contingency](#f22-nit--5-o7-item-3-full-faithfulness-attribution-and-its-contingency)
  - [F23 (NIT, § 5 O7 item 2): "answers a question" overstates](#f23-nit--5-o7-item-2-answers-a-question-overstates)
- [Verification record](#verification-record)
  - [(a) Paper attributions in O7](#a-paper-attributions-in-o7)
  - [(b) O7 item 1: coend extension and co-Yoneda restriction](#b-o7-item-1-coend-extension-and-co-yoneda-restriction)
  - [(c) O7 item 2: the BG counterexample](#c-o7-item-2-the-bg-counterexample)
  - [(d) O7 classification paragraph](#d-o7-classification-paragraph)
  - [(e) Duality remark and § 10 item 5's caveat](#e-duality-remark-and--10-item-5s-caveat)
  - [(f) New references](#f-new-references)
  - [(g) r1 fixes (F1–F15)](#g-r1-fixes-f1f15)
  - [(h) Whole-document consistency](#h-whole-document-consistency)
- [Verdict](#verdict)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

Review of
`docs/superpowers/specs/2026-07-14-polynomial-preserving-pra-design.md`,
round 2. Primary focus: the material added after round 1 —
§ 5 entry O7 (positive inductive-recursive definitions), § 10
item 5, and the two new references. Secondary focus: verification
of the r1 fixes (F1–F15) and a whole-document consistency pass.
Sources consulted: Ghani–Malatesta–Nordvall Forsberg,
*Positive inductive-recursive definitions*, LMCS 11(1:13), 2015
(full text of the paper PDF, pp. 1–21, below "GMNF");
`GebLean/Utilities/Families.lean`; `GebLean/PresheafPRA.lean`;
`geb-idris/src/LanguageDef/IntEFamCat.idr`;
`geb-mathlib/Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean`; the
r1 review file. Finding numbers continue r1's sequence.

## Summary of findings

| ID | Severity | Section | Description |
| --- | --- | --- | --- |
| F16 | MAJOR | 5 (O7) | The duality parenthetical claims each completion in `FCP` repairs one side of the dual criterion pair; `FC` repairs neither side, and § 10 item 5 states the input side is unrepaired |
| F17 | MAJOR | 5 (O7 item 2) | The recorded counterexample argument omits the empty-direction case, for which post-composition is vacuous and no `g = e` is forced |
| F18 | MINOR | 10 (item 5) | "the excluded functors are not PRA" over `C = FP(I)` asserts more than the recorded arguments establish |
| F19 | MINOR | 5 (preamble) | The disposition list omits O7 |
| F20 | MINOR | 5 (O7), 8 | Colloquialisms/metaphors in the new text: "quotient-flavored", "habitat", "canon", "survives"; residual "hand-written" |
| F21 | NIT | 5 (O7) | "§ 4.1 normal-forms universe": the paper has no § 4.1; the material is Example 4.1 in § 4 |
| F22 | NIT | 5 (O7 item 3) | Full-faithfulness attribution: the passage is in the paper's § 2 (p. 5), and Remark 3.4 makes the property contingent on the morphism collection |
| F23 | NIT | 5 (O7 item 2) | "answers a question the paper's § 8 lists as future work" overstates: the counterexample settles one direction of the listed relationship |

## Findings

### F16 (MAJOR, § 5 O7): the duality parenthetical misassigns the input-side repair

Quote:

> This is the input-side dual of the O6 component-terminal
> condition (each of the two completions in `FCP` repairs one
> side: `FP` adjoins terminals, `FC` adjoins initials).

Problem. In the FCP signature the index categories are
`C = FP(I)` and `D = FP(J)`; the O6 (output-side) condition
consumes terminal objects of `D`, and the new input-side
criterion consumes componentwise initial objects of `C`. `FP`
applied to `J` repairs the output side. `FC` is the *outer*
completion: its adjoined initial object (the empty family) lies
in `FCP(I) = FC(FP(I))`, the domain category of the functors,
not in the index category `C = FP(I)` that the criterion
quantifies over — and the initial object of `FC(C)` is of no use
to the surrogate in any case, since `Hom(∅, Z) ≅ 1` is exactly
the non-surrogate. So in the FCP signature only the output side
is repaired, which is what § 10 item 5 correctly states
("componentwise initial objects are not automatic, so the
fragment is strictly weaker than IR⁺ there"). The parenthetical,
read as a claim about the FCP signature, contradicts item 5; the
two constituent facts ("`FP` adjoins terminals", "`FC` adjoins
initials") are true of the completions in isolation but neither
completion in `FCP` acts on the input-side index category.

Suggested fix. Replace the parenthetical with an explicit
one-sided statement, e.g.: "This is the input-side dual of the
O6 component-terminal condition. In the FCP signature only the
output side is repaired: `FP(J)` supplies the terminal objects
O6 needs, while the input side would need componentwise initial
objects in `C = FP(I)`, which the signature does not supply
(§ 10 item 5). (`FC` adjoins an initial object, but to `FCP(I)`
itself, not to the index category the criterion consumes.)"

### F17 (MAJOR, § 5 O7 item 2): the counterexample argument omits empty directions

Quote:

> over `C = BG` (`|G| ≥ 2`) the code `δ_1(const(ι ⋆))` decodes
> to the label-erasing functor `free ∘ π₀`, while every PRA acts
> on morphisms by post-composition, so naturality against right
> translations forces `g = e`.

Problem. The decode claim and the conclusion are correct (see
verification record, item (c)), but the recorded argument has a
gap. Naturality of the comparison isomorphism against the right
translations `r_g : G → G` forces `T(r_g) = id`, i.e.
`r_g ∘ φ = φ` for every direction map `φ : E_a → G` in the
support of `T(G)`; evaluating `φ` at an element then forces
`g = e` — but only when `E_a` is nonempty. For `E_a = ∅` one has
`Hom(∅, G) ≅ 1` and post-composition is vacuously the identity,
so no constraint on `g` arises; the argument as stated does not
exclude a PRA supported entirely on empty directions (for which
`T` is constant in the morphism argument). The escape is closed
by one further test: `T(∅) ≅ free(π₀(∅)) = ∅` forces
`Hom(E_a, ∅) = ∅` for every position `a`, i.e. every direction
is nonempty; then the recorded step applies and `|G| ≥ 2` gives
the contradiction.

Suggested fix. Insert the nonemptiness step, e.g.: "... while
every PRA acts on morphisms by post-composition; the test
`T(∅) ≅ ∅` forces every direction to be nonempty, and then
naturality against right translations forces `g = e`."

### F18 (MINOR, § 10 item 5): non-PRA claim over `FP(I)` exceeds the recorded arguments

Quote:

> so the fragment is strictly weaker than IR⁺ there (as
> required — the excluded functors are not PRA)

Problem. The strict-weakness claim is established: `FP(I)` can
lack componentwise initial objects (verification record, item
(e)), so by the O7 criterion the fragment cannot express bare
element-choice, which IR⁺ expresses. The parenthetical gloss,
however, asserts that bare element-choice over `C = FP(I)` is
not PRA-extendable, and the recorded arguments do not establish
that in general: O7 item 2 proves non-PRA-extendability over
groupoid components with nontrivial automorphisms, and the O7
criterion governs expressibility *within the fragment* (arities
that are coproducts of representables), whereas a PRA's
directions are arbitrary presheaves. Re-running the converse
argument at the PRA level yields, per component, a connected
presheaf `E` with `Hom(E, y(c)) ≅ 1` for all `c` in the
component together with an idempotent on a supporting object;
extracting an initial object from that data uses idempotent
splitting, so the general non-PRA conclusion is available under
Cauchy completeness of the component but is not proved for
arbitrary `FP(I)`. The corresponding claim in O7's closing
paragraph is correctly scoped ("the excluded functors" there are
the paper's § 4 groupoid examples, for which item 2's argument
applies componentwise).

Suggested fix. Scope the gloss, e.g. "(as required — the
functors excluded in the verified groupoid cases are not PRA;
whether bare element-choice over `FP(I)` is ever PRA-extendable
is part of this item's question)", or drop the parenthetical.

### F19 (MINOR, § 5 preamble): O7 missing from the disposition list

Quote:

> O1, O1a, O5, and O6 are resolved below; O2 is subsumed by the
> G2 obligation (§ 7, where G2's and G5's fullness are
> identified); O3 and O4 are carried forward as § 10 items 3
> and 4.

Problem. O7 is resolved below ("resolved: distinct classes") and
carries a residue to § 10 item 5, but the preamble does not
mention it, and its opening sentence ("questions raised during
goal-setting") no longer covers the section's contents.

Suggested fix. Extend the preamble: "... items 3 and 4; O7 is
resolved below, with its sub-syntax question carried forward as
§ 10 item 5", and widen "goal-setting" if O7 arose later.

### F20 (MINOR, §§ 5, 8, style): colloquialisms and metaphors in the new text

Quotes (all § 5 O7 except the last): "genuine
induction-recursion survives"; "its remaining habitat `Set≅`";
"choosing representatives of isomorphism classes is
quotient-flavored computation"; "retains the container and
Σ-universe canon"; "each of the two completions in `FCP` repairs
one side" (also F16); § 8: "not by explicit hand-written
object/morphism maps" ("hand-rolled" was replaced but
"hand-written" remains).

Problem. `CLAUDE.md` § Style guidelines and
`.claude/rules/markdown-writing.md`: avoid colloquialisms and
metaphors; only standard technical terms.

Suggested fix. Substitutions such as: "the induction-recursion
content is retained"; "its remaining domain of applicability
`Set≅`"; "computation on isomorphism classes that no PRA
expresses"; "retains the container and Σ-universe examples";
"supplies the object required on one side" (subsumed by F16's
rewrite); "not by explicit object/morphism maps".

### F21 (NIT, § 5 O7): "§ 4.1" is not a subsection of the paper

The ruled-out list cites "the § 4.1 normal-forms universe over
`Fam(Set≅)`". GMNF § 4 ("Stronger elimination principles") has
no numbered subsections; the normal-forms universe is
Example 4.1. Under the citation rule (searchable identifiers),
write "Example 4.1".

### F22 (NIT, § 5 O7 item 3): full-faithfulness attribution and its contingency

The spec cites "their § 3" for "the interpretation `⟦−⟧` is not
full and faithful for non-discrete `C`". The explicit statement
("we lose the full and faithfulness of the interpretation
functor `⟦−⟧`") is on p. 5, in the paper's § 2, previewing the
§ 3 development; and Remark 3.4 (§ 3) records that the property
depends on the chosen collection of code morphisms — taking
`Hom(x, y) = ⟦x⟧ → ⟦y⟧` restores full faithfulness by
definition, at the cost of an inductive-recursive metatheory.
Cite "p. 5 and Remark 3.4" and, optionally, note the
contingency, since the spec uses the point as a contrast with
the G1 formula.

### F23 (NIT, § 5 O7 item 2): "answers a question" overstates

GMNF § 8 lists as future work "to investigate the relationship
between the theory of IR⁺ and the theory of familial 2-functors
introduced by Weber". The BG counterexample establishes that the
classes diverge — a substantive but partial answer (one
direction of a relationship left open in both directions).
"bears on" or "settles the containment direction of" would be
exact.

## Verification record

Claims independently checked and confirmed, with the reasoning
summarized. Item labels (a)–(e) follow the review brief's
primary focus; the r1-fix and whole-document items follow.

### (a) Paper attributions in O7

All checked against the paper text and confirmed:

- **Definition 3.1**: simultaneous (inductive-inductive)
  definition of IR⁺(ℂ) codes (`ι c`, `σ_A f`, `δ_A F` with
  `F : (A → ℂ) → IR⁺(ℂ)` a functor) and code morphisms
  (`ι⇒ι`, `σ⇒σ` with covariant `α : A → B`, `δ⇒δ` with the
  contravariant twist `α : B → A`). Matches "Definition 3.1
  (IR⁺ codes and code morphisms)".
- **Theorem 3.3**: every code decodes to a functor
  `Fam(ℂ) → Fam(ℂ)` and every code morphism to a natural
  transformation; the object action is Theorem 2.4's, with
  δ-clause `⟦δ_A F⟧(X,P) = Σ_{g:A→X} ⟦F(P∘g)⟧(X,P)` — exactly
  the spec's quoted clause; the morphism action's δ-clause is
  `[in_{h∘g} ∘ ⟦F(Q∘h∘g)⟧(h,k) ∘ ⟦F_→(g*(k))⟧_{(X,P)}]_{g:A→X}`
  with `g*(k) : P∘g → Q∘h∘g` the reindexed label tuple.
- **Proposition 6.2**: the functor `ψ : IR⁺(ℂ) → IR|ℂ|` with
  `Fam(ε) ∘ ⟦ψ(γ)⟧ ≅ ⟦γ⟧ ∘ Fam(ε)` and `ψ ∘ φ = id`; the proof
  ends "since ε is the identity on discrete categories the two
  schemas agree on discrete categories". "Discrete collapse" is
  accurate; the admitted-list use ("at discrete index categories
  everything is admitted") is supported both by 6.2 (labels are
  identities in `Fam|ℂ|`) and directly by the criterion (each
  component of a discrete category is a single object, trivially
  initial).
- **Theorem 7.2**: "Assume that a Mahlo cardinal exists in the
  meta-theory. If ℂ has connected colimits, then every functor
  `⟦γ⟧` for `γ : IR⁺(ℂ)` has an initial algebra." Hypotheses as
  the spec states them; the Mahlo cardinal is a meta-theoretic
  assumption (§ 1: "does not play any computational role").
- **§ 8 statements**: "An open problem for both IR⁺ and IR is
  the question whether the definable functors are closed under
  composition" (also stated in § 5, p. 16, where composition of
  *uniform* codes is constructed); and the closing sentence
  lists investigating "the relationship between the theory of
  IR⁺ and the theory of familial 2-functors introduced by Weber
  [Web07]" as future work. Both match; see F23 for the strength
  of "answers".
- **Full faithfulness**: the loss for non-discrete ℂ is stated
  on p. 5 (paper's § 2) with the § 3 nuance in Remark 3.4; see
  F22.
- **`Fam(ℂ) = FC(ℂ)`**: Remarks 2.3 states `Fam(ℂ)` is the free
  set-indexed coproduct completion, matching the spec's
  identification, and cites [CJ95] for cocompleteness iff
  connected colimits — consistent with the spec's
  Carboni–Johnstone usage elsewhere.

### (b) O7 item 1: coend extension and co-Yoneda restriction

Confirmed by redoing the computation. The integrand pairs the
contravariant factor `ℓ ↦ Π_a Z(ℓ(a))` with the covariant factor
`ℓ ↦ ⟦F(ℓ)⟧⁺(Z)` (covariance is exactly what Definition 3.1's
functorial `F` supplies, decoded by Theorem 3.3(ii)), so the
coend over `C^A` is well-formed; the value is a presheaf via the
copower, and the whole is functorial in `Z`. Restriction: for
`Z = ∐_{x∈X} y(P x)`,

```text
Π_a Z(ℓ a) = Π_a Σ_x Hom(ℓ a, P x)
           = Σ_{g:A→X} Hom_{C^A}(ℓ, P∘g),
```

a choice-free distributivity since `A` is a set; coends commute
with the outer `Σ_g`, and co-Yoneda
(`∫^ℓ Hom(ℓ, m) × H(ℓ) ≅ H(m)` for covariant `H`) collapses each
summand to `⟦F(P∘g)⟧⁺(Z)`, recovering Theorem 3.3's object
clause. On morphisms: `incl(h,k)` acts on the `Hom_{C^A}` factor
by the tuple `g*(k) = (k_{g a})_a : P∘g → Q∘h∘g` and reindexes
`g ↦ h∘g`; transporting the co-Yoneda representative
`(ℓ = P∘g, id)` along `g*(k)` inserts `⟦F_→(g*(k))⟧` by the
coend relation, and the decode-naturality square (Theorem
3.3(ii)) commutes it past the `Z`-action — reproducing the
morphism clause `in_{h∘g} ∘ ⟦F(Q∘h∘g)⟧(h,k) ∘ ⟦F_→(g*(k))⟧`.
The claim "restricts ... on objects and on morphisms" is
correct. (The `ι`/`σ` clauses extend by `⟦ι c⟧⁺(Z) = y(c)` and
coproducts; the record leaves them implicit, which is
acceptable.)

### (c) O7 item 2: the BG counterexample

- **Decode**: for `A = 1`, `F = const(ι ⋆)`, the object clause
  gives `Σ_{x:X} (1, λ_.⋆) ≅ (X, const ⋆)`; in the morphism
  clause `F_→(g*(k))` is the identity code morphism (constant
  functor), so `⟦δ_1 F⟧(h,k) = (h, x ↦ e)`. A constant `F` does
  discard `g*(k)`, exactly as the spec claims.
- **`free ∘ π₀`**: `Fam(BG)` is equivalent to the category of
  free right `G`-sets (`(X, k : X → G)`-morphisms correspond to
  equivariant maps of `G × X`); the index functor is the orbit
  (connected-components) functor `π₀`, and the decoded functor
  is `(X, P) ↦ (X, const ⋆)`, `(h, k) ↦ (h, e)`, which is
  `free ∘ π₀`. Accurate.
- **Non-PRA-extendability**: redone from scratch. Naturality of
  a comparison `ν : T|_{FC} ≅ free∘π₀` at `r_g` forces
  `T(r_g) = id`; a PRA acts by fixing positions and
  post-composing on `Hom(E_a, −)`; with every supporting
  direction nonempty, evaluating any `φ : E_a → G` at an element
  gives `φ(x)·g = φ(x)`, so `g = e`, contradicting `|G| ≥ 2`.
  The nonemptiness premise is where the recorded argument has a
  gap (F17); it follows from `T(∅) ≅ ∅` (positions are
  independent of `Z`, and an empty direction would contribute
  `Hom(∅, ∅) ≅ 1` to `T(∅)`). With F17's clause added the
  argument is complete. The weaker claim "the extension is not
  PRA in general" also checks directly: the coend extension of
  the BG code is `free ∘ orbits` on `G`-sets, which fails to
  preserve the connected limit `eq(id, σ) = ∅` for `G = ℤ/2`
  (orbits sends both maps to `id`), and PRAs preserve connected
  limits.

### (d) O7 classification paragraph

- **Criterion, forward direction**: with componentwise initial
  objects `0_i`, `Σ_i Z(0_i) ≅ X` for `Z = ∐_x y(P x)` (each `x`
  contributes `Hom(0_i, P x) ≅ 1` exactly for the component of
  `P x`), naturally in objects and in `Fam`-morphisms (the label
  action on a singleton hom-set is the identity of the
  identification), so the hom-labelled surrogate agrees with
  bare element-choice on polynomials, on objects and morphisms.
  Confirmed.
- **Criterion, converse**: a surrogate within the fragment
  computes `X ≅ ∐_j Hom(E_j, Z)` with `E_j ∈ FC(C)`; testing at
  `Z = X·y(c)` and letting `X` vary forces, per component,
  exactly one supporting `j` with `E_j` a single representable
  `y(c_i)` and `Hom(c_i, c) ≅ 1` for every `c` in the component
  — an initial object of the component. Confirmed for the
  fragment (the caveat that PRA-level directions are arbitrary
  presheaves is F18's subject).
- **Admitted list**: Lemma 5.3(i) is
  `⟦δ_1((X : 1 → Setᵒᵖ) ↦ ι(X∗))⟧C ≅ C` — the identity via a
  label-passing continuation ("ι ∘ eval") — and Lemma 5.3(ii) is
  `⟦σ_S(s ↦ ι P(s))⟧C ≅ (S, P)`, δ-free constants; Lemma 5.4 is
  `+_IR`; Lemma 5.5 is `×_G` (with `G(X,Y) = X + Y` recovering
  the container product, matching the spec's
  `Hom(E,Z) × Hom(E',Z) = Hom(E ⊔ E', Z)` mechanism);
  exponentiation `K → γ` and composition `•` are constructed for
  uniform codes in § 5, culminating in Theorem 5.7 (every nested
  type is a container functor). Evaluations: the filter
  `σ_{Hom(c, ℓ)}` has the covariant variance the `σ⇒σ` rule
  requires and decodes to `Z(c) × (−)`; labels act by
  post-composition, consistent with PRAs. Example 2.5 is the
  Σ-universe over `IR(Set)` (discrete); Example 3.5 is its
  IR⁺(Setᵒᵖ) extension, where `X∗ ≅ Hom_{Setᵒᵖ}(X, 1)` (the
  singleton set `1` is `Setᵒᵖ`'s initial object; the hom is
  contravariant in the label `X`, matching the `δ⇒δ` twist that
  Example 3.5 itself exercises with `α = f∗`); Example 4.2 is
  the universe-to-universe map example in `Fam(Setᵒᵖ)`. All
  attributions and mechanisms confirmed.
- **Ruled-out list**: the normal-forms universe is Example 4.1
  (see F21), over `Fam(Set≅)`; in `Set≅`,
  `|Hom_{Set≅}(c, X)| ∈ {0, |c|!}` (empty unless `|c| = |X|`),
  so no representable — nor coproduct of representables — has
  `X`-many elements naturally in `X`: the element-arity is not a
  hom-arity, confirmed. The Π-universe: the contravariance
  obstruction ("impossible if e.g. `X' = 0`, `X = 1`, and
  `Y∗ = 0`") is on p. 10, ruling out IR⁺(Set) and IR⁺(Setᵒᵖ)
  codes for Example 2.6's `γ_{ℕ,Π}`, with Example 3.6 living in
  `Fam(Set≅)` — matching "already excluded over `Set` and
  `Setᵒᵖ` ... its remaining habitat `Set≅`". The closing scope
  ("costs exactly the groupoid fragment ... the excluded
  functors are not PRA") is sound for the § 4 examples: `Set≅`
  is a coproduct of `BS_n`'s and item 2's argument applies to
  every component with `n ≥ 2`.

### (e) Duality remark and § 10 item 5's caveat

The input-side/output-side duality itself is confirmed: O6's
condition (componentwise terminal objects in the output index
category, from `P ↦ P(1)`) dualizes to componentwise initial
objects in the input index category (from element-choice /
`π₀ = colim`). The parenthetical's assignment of repairs is F16.
The § 10 item 5 claim "`FP(I)` lacks automatic componentwise
initial objects" is true: `FP(I)` has a terminal object (the
empty family), hence is connected, and an initial object of
`FP(I)` is precisely a small multi-initial family in `I`
(`Hom_{FP}((X,F),(Y,G)) = Π_y Σ_x Hom_I(F x, G y)`, so
initiality at singletons says every `i ∈ I` admits a unique pair
`(x, F x → i)`). For `I = (ℤ, ≤)` no such family exists (any
two candidate members share upper bounds, forcing a singleton,
i.e. a least element, which `ℤ` lacks), so `FP((ℤ,≤))` is a
connected category with no initial object. Conversely `FP(I)`
does have one when `I` is discrete or has an initial object, so
"not automatic" is the correct strength.

### (f) New references

- GMNF front matter: "Logical Methods in Computer Science
  Vol. 11(1:13)2015, pp. 1–21", "DOI:10.2168/LMCS-11(1:13)2015",
  published Mar. 27, 2015; authors and title as cited. The
  spec's entry matches.
- Dybjer–Setzer: the paper's [DS03] is "Induction–recursion and
  initial algebras. Annals of Pure and Applied Logic,
  124(1-3):1–47, 2003", matching the spec's entry; it is the
  right anchor for "Dybjer–Setzer's discrete theory" as decoded
  functors (GMNF Theorem 2.4 cites [DS03]).
- `Geb/Mathlib/Data/PFunctor/IndRec/Basic.lean` exists and is
  the discrete IR code syntax (module docstring: "follows
  [GhaniNordvallForsbergMalatesta2015], Section 2 ... the theory
  of [DybjerSetzer1999]"), as O7's closing sentence describes.

### (g) r1 fixes (F1–F15)

Each verified in the current text; no fix introduced a
contradiction:

- F1: § 6.5 now conditions `p`'s *domain* (componentwise
  terminals) and claims as refinements only the
  componentwise-terminal condition, the `π` condition, and the
  multiadjunction condition — consistent with § 3 item 3's
  "`T` étale".
- F2: § 1.1 now says "exhibits ... as regular projective objects
  covering the presheaf category (... the converse
  identification is not formalized)".
- F3: Carboni–Johnstone venue corrected in § 1.2 and References,
  with the 2004 Corrigenda added; consistent with GMNF's own
  [CJ95] entry (MSCS 5(04):441–459, 1995).
- F4: § 6.2 makes the factorization assignment a data field with
  Prop-valued uniqueness; § 6.3 replaces the full-subcategory
  phrasing with the fully faithful forgetful functor to the
  named intermediate category.
- F5: § 7 cites DJN 2.5 (Set instance) for distributivity, 2.7
  for the hom-set formula, 2.4 for full faithfulness.
- F6: G5 (§ 2 and § 7) is stated with the formula category as
  domain, factoring through G2's comparison.
- F7: the tower reads `S : Type w`.
- F8: § 6.2's terminology paragraph states the condition as
  "`Eᵒᵖ` admits a left multiadjoint (Diers)", records Osmond's
  noun usage, avoids "parametric left adjoint", and fixes the
  document's own terms as "multiadjunction witnesses/condition";
  § 10's closing note records the resolution. A grep for
  `multiadjoint|multi-adjoint|multiadjunction|parametric left`
  confirms no stray occurrence of the old noun usage remains
  (the two "left multiadjoint" occurrences are the Diers
  attributions; "right multi-adjoint" occurs only as the quoted
  Osmond term and in his cited title).
- F9: O6 carries the audit result, with the docstring correction
  deferred to a separate branch.
- F10: `FC(p)` is listed in § 2's prerequisites and § 8's
  deliverable 3, with the intended construction path.
- F11: § 10 item 4 names the two concrete universe risks
  (`Cat.{max w' v', max (w' + 1) u' w'}`; `familyNatTrans'`
  same-universe constraints with `catULiftFunctor2` mediation).
- F12: all five quoted colloquialisms replaced ("used
  throughout", "principal instantiation", "is the terminal
  object of a component", "apply only", "explicit hand-written"
  — the residual "hand-written" is noted in F20).
- F13: § 6.2 identifies `T1` with § 1.1's `A`.
- F14: Ahman–Uustalu dropped; Gambino–Kock now cited in § 6.3.
- F15: § 2 G2 notes the equivalence remains a Prop-level remark
  with the computability rationale.

### (h) Whole-document consistency

- Cross-references: § 5 preamble ↔ § 10 items 3 and 4 consistent
  after the r1 renumbering; O7 ↔ § 10 item 5 mutually
  consistent (modulo F16/F18); § 2's prerequisite note points to
  § 10 item 4; § 9's third entry points to § 10 item 1. The
  § 5 preamble's omission of O7 is F19.
- O7 versus §§ 6–9: no contradiction found. § 6's derivation and
  § 7's obligations are unaffected by O7 (the decision keeps the
  G1 formula as the definition and adds no deliverables); § 8
  needs no IR⁺ entry; § 9 needs no new non-goal, since § 10
  item 5 carries the owner ("future work") in the same manner as
  § 10 item 2 — the split between §§ 9 and 10 is already used
  this way for the bridge-intrinsic condition.
- Notation: the `T1 = A` identification is present (§ 6.2); O7
  writes `Fam(C) = FC(C)`, consistent with § 1.1.
- Document mechanics: `doctoc --dryrun --update-only` reports
  the TOC current; `markdownlint-cli2` reports 0 errors on the
  spec; the `IntEFamCat.idr` citation (lines 152–157) matches
  the file (the dualization comment spans those lines).
- Style of the new text: findings F20/F21; otherwise compliant
  (no value-laden adjectives, generic user references
  maintained).

## Verdict

The new O7/§ 10-item-5 material is substantively correct: the
paper attributions are accurate (with the two citation nits F21
and F22), the coend-extension and restriction claims were
reproduced independently, the counterexample's conclusion and
the classification criterion hold in both directions, and the
`FP(I)` caveat is true with a concrete witness (`I = (ℤ, ≤)`).
The two MAJOR findings are localized sentences in the decision
record: a misassigned repair in the duality parenthetical (F16,
contradicting § 10 item 5 as written) and a one-clause gap in
the recorded counterexample argument (F17); replacement text is
supplied for both and the corrected content was verified here.
F18–F23 are scoping, bookkeeping, and style items with concrete
fixes. Converged: ready for user review once the listed fixes
are applied; no further adversarial round is required.
