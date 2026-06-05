# Weighted limits reduce to ordinary limits via the category of elements

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->
**Table of Contents**  *generated with [DocToc](https://github.com/thlorenz/doctoc)*

- [The precise theorem for weighted limits](#the-precise-theorem-for-weighted-limits)
  - [**{W, F} iso lim(F o pi : El(W) -> C)**](#w-f-iso-limf-o-pi--elw---c)
  - [**W * F iso colim(F o pi : El(W) -> C)**](#w--f-iso-colimf-o-pi--elw---c)
- [Ends as limits over twisted arrow categories](#ends-as-limits-over-twisted-arrow-categories)
  - [**int_c P(c, c) iso {Hom_C, P}**](#int_c-pc-c-iso-hom_c-p)
  - [**int_c P(c, c) iso lim(P o pi : Tw(C) -> D)**](#int_c-pc-c-iso-limp-o-pi--twc---d)
  - [**int_c P(c, c) iso colim(P o pi' : Tw(C_op)_op -> D)**](#int_c-pc-c-iso-colimp-o-pi--twc_op_op---d)
- [Why this reduction only works for V = Set](#why-this-reduction-only-works-for-v--set)
- [The equivalence of weighted cones and ordinary cones](#the-equivalence-of-weighted-cones-and-ordinary-cones)
- [References and locations](#references-and-locations)
- [Collage construction for profunctors](#collage-construction-for-profunctors)
- [Conclusion](#conclusion)

<!-- END doctoc generated TOC please keep comment here to allow auto update -->

The central result sought is well-established in enriched category theory:
for Set-weighted limits, **{W, F} ≅ lim(F ∘ π)** where π : El(W) → J is the
canonical projection from the category of elements. This formula has no
standard name but is commonly attributed to Kelly's framework and Dubuc's
detailed treatment. The reduction works because the category of elements
"unfolds" the weight, replacing each object j with |W(j)| copies,
transforming weighted cones into ordinary cones over an expanded diagram.

## The precise theorem for weighted limits

For a weight W : J → **Set** and a diagram F : J → C, let El(W) denote the
**category of elements** with objects consisting of pairs (j, w) where
j ∈ ob(J) and w ∈ W(j), and morphisms f : (j, w) → (j', w') being morphisms
f : j → j' in J such that W(f)(w) = w'. The projection functor π : El(W) → J
sends (j, w) to j.

The fundamental isomorphism states:

### **{W, F} iso lim(F o pi : El(W) -> C)**

where the left side is the W-weighted limit of F, characterized by
C(A, {W, F}) ≅ [J, **Set**](W, C(A, F−)), and the right side is the ordinary
conical limit over the category of elements. The unit of the weighted limit
representation ξ : W ⇒ C({W, F}, F−) corresponds precisely to the universal
cone over F ∘ π.

The **dual statement for weighted colimits** follows the same pattern.
For W : J^op → **Set** and F : J → C, the weighted colimit satisfies:

### **W * F iso colim(F o pi : El(W) -> C)**

This result is foundational: Wikipedia's article on the category of elements
explicitly notes its appearance "in the proof that every weighted
colimit can be expressed as an ordinary colimit, which is in turn necessary
for the basic results in theory of pointwise left Kan extensions."

## Ends as limits over twisted arrow categories

The twisted arrow category provides a canonical example of this reduction.
For a category C, the **twisted arrow category** Tw(C) has morphisms
f : a → b as objects, with a morphism from (f : a → b) to (g : c → d) being
a pair (p : c → a, q : b → d) making the square commute: q ∘ f ∘ p = g.
The "twist" refers to p going in the reverse direction.

The connecting observation is that **Tw(C) ≅ El(Hom_C)** where
Hom_C : C^op × C → **Set** is the hom-functor. This isomorphism holds because
objects of El(Hom_C) are triples (a, b, f) with f ∈ C(a, b)—precisely the
morphisms f : a → b that form objects of Tw(C). The contravariance in the
first argument and covariance in the second produce the twisted morphism
directions.

The **end** ∫_c P(c, c) for a bifunctor P : C^op × C → D is the
**Hom_C-weighted limit** of P:

### **int_c P(c, c) iso {Hom_C, P}**

Applying the general reduction theorem:

### **int_c P(c, c) iso lim(P o pi : Tw(C) -> D)**

where the functor P' = P ∘ π sends an object (f : a → b) ∈ Tw(C) to
P(a, b) ∈ D. Loregian's "Coend Calculus" (Section 1.2) provides the clearest
modern exposition of this formula. The dual statement for **coends** is:

### **int_c P(c, c) iso colim(P o pi' : Tw(C_op)_op -> D)**

## Why this reduction only works for V = Set

A crucial caveat explains why weighted limits are essential in enriched
category theory. As Kelly emphasizes in Section 3.9 of his book (aptly titled
"The inadequacy of conical limits"), when V ≠ **Set**, ordinary conical
limits are insufficient for developing a complete theory. The category of
elements construction fundamentally relies on the ability to "decompose" a
set W(j) into its elements—a process without a direct analogue in general
enriched settings.

Christina Vasilakopoulou, in her n-Category Café exposition, quotes a
conversation with André Joyal: "I had a pleasant conversation about this
with A. Joyal which made me wonder why in an enriched setting we lack a
'category of elements' construction; can this be viewed as implying that we
are forced to allow the existence of weighted (co)limits?"

Recent work by **Moser, Sarazola, and Verdugo** (arXiv:2308.14455, 2023)
introduces an internal category of elements for V-categories and proves
"a novel result describing weighted V-limits as certain conical internal
limits," extending the `Set`-based reduction to enriched contexts using
internal category theory.

## The equivalence of weighted cones and ordinary cones

The bijection between W-weighted cones and ordinary cones over
F ∘ π : El(W) → C can be stated precisely. A **W-weighted cone** from an
object A ∈ C to the diagram F consists of a natural transformation
ρ : W ⇒ C(A, F−), which assigns to each j ∈ J and each w ∈ W(j) a morphism
ρ_j(w) : A → F(j), compatibly with morphisms in J.

An **ordinary cone** from A to F ∘ π consists of morphisms
λ_{(j,w)} : A → F(j) for each (j, w) ∈ El(W), compatible with morphisms in
El(W). The correspondence is immediate: given ρ, define λ_{(j,w)} = ρ_j(w);
conversely, given λ, define ρ_j(w) = λ_{(j,w)}. The naturality conditions
correspond exactly under this bijection.

For **colimits**, the dual statement involves weighted cocones. A W-weighted
cocone from F to A (for W : J^op → **Set**) corresponds to an ordinary
cocone from F ∘ π to A over El(W), where now El(W) is constructed from the
presheaf W : J^op → **Set**.

## References and locations

The primary reference is **Kelly's "Basic Concepts of Enriched Category
Theory"** (1982, reprinted TAC Reprints No. 10, 2005). The relevant sections
are:

- **Section 3.1** (p. 37): Definition of indexed (weighted) limits
- **Section 3.4**: contains the reduction result
- **Proposition 3.33**: The formal statement of the reduction
- **Section 3.9**: "The inadequacy of conical limits"—explains why enriched
  settings require weighted limits

Additional authoritative sources include:

- **Dubuc, E.**: "Kan Extensions in Enriched Category Theory" (Lecture Notes
  in Mathematics 145, Springer, 1970)—contains the detailed proof of the
  reduction
- **Borceux, F.**: "Handbook of Categorical Algebra Vol. 2" (Cambridge,
  1994), §6.6—Definition 6.6.8 and surrounding material
- **Riehl, E.**: "Categorical Homotopy Theory" (Cambridge, 2014),
  Chapters 6–7, and her lecture notes "Weighted Limits and Colimits"
  available at emilyriehl.github.io
- **Loregian, F.**: "Coend Calculus" (Cambridge, 2021; arXiv:1501.02503)—
  Section 1.2 on twisted arrow categories
- **Mac Lane, S.**: "Categories for the Working Mathematician" (2nd ed.,
  1998), Exercise IX.6.3

## Collage construction for profunctors

The **collage** (or **cograph**) of a profunctor H : C ⇸ D provides a
related construction. The category Collage(H) has objects ob(C) ⊔ ob(D),
with Hom(c, c') = C(c, c'), Hom(d, d') = D(d, d'), Hom(c, d) = H(c, d), and
Hom(d, c) = ∅. This is the **lax colimit** of H viewed as a 1-cell in the
bicategory **Prof**, also characterized as a **two-sided codiscrete
cofibration** by Carboni, Johnson, Street, and Verity in "Modulated
bicategories." The construction appears in Street's "Fibrations in
bicategories" and is detailed in Fong & Spivak's "Seven Sketches in
Compositionality" (Chapter 4).

## Conclusion

For formal verification purposes, the precise statements are:

1. **{W, F} ≅ lim(F ∘ π)** for W : J → **Set**, F : J → C,
   π : El(W) → J the projection
2. **W * F ≅ colim(F ∘ π)** for W : J^op → **Set**, F : J → C
3. **∫_c P(c,c) ≅ lim(P ∘ π : Tw(C) → D)** where Tw(C) = El(Hom_C)
4. The equivalence between W-weighted cones over F and ordinary cones over
   F ∘ π is a natural bijection

These results appear unnamed in the literature but are standard consequences
of Kelly's enriched category theory framework (Section 3.4) and Dubuc's 1970
monograph. The category of elements construction is the essential tool, with
Tw(C) ≅ El(Hom_C) providing the connection to ends and coends.
