# Profunctors and end machinery

<!-- START doctoc generated TOC please keep comment here to allow auto update -->
<!-- DON'T EDIT THIS SECTION, INSTEAD RE-RUN doctoc TO UPDATE -->

- [Purpose](#purpose)
- [Mathematical context](#mathematical-context)
- [Modules](#modules)
- [Alternative formulations](#alternative-formulations)
- [Dependencies](#dependencies)
- [Pointers](#pointers)

<!-- END doctoc -->

## Purpose

This area contains the foundational machinery for profunctors, ends,
coends, (co)wedges, weighted (co)limits, twisted-arrow categories,
the Street–Walters comprehensive factorization, paranatural
transformations, and the Mendler–Lambek correspondence between
Mendler-style and conventional algebras via restricted coends and
end powers. It supplies the ambient combinatorial infrastructure on
which the polynomial-functors area's parametric constructions
ultimately rest.

## Mathematical context

A profunctor from `C` to `D` is a functor `Cᵒᵖ × D ⥤ Type`;
the codebase works primarily with endoprofunctors `Cᵒᵖ × C ⥤ D`
for varying target categories `D`. The end of a profunctor
`F : Cᵒᵖ × C ⥤ Type` is a universal wedge — a family of maps
`∫ F → F(c,c)` satisfying a naturality ("wedge") condition;
dually, a coend is a universal cowedge. Both are characterized as
(co)limits over the twisted-arrow category `Tw(C)` whose objects
are morphisms of `C` (Loregian, *Coend Calculus*, Cambridge 2021;
nLab "twisted arrow category"). A weighted (co)limit generalizes
this: a weight `W : Cᵒᵖ ⥤ Type` and a diagram `G : C ⥤ D`
combine to a representing object for `Nat(W, Hom(X, G-))`.

Paranatural transformations (Neumann, "Paranatural Category
Theory", 2023) are families indexed by objects of `C` that satisfy
a compatibility condition weaker than naturality: they commute with
morphisms only at diagonal elements, not across the full bifunctor.
They arise as the morphisms of the category of diagonal elements of
a profunctor.

The comprehensive factorization of a functor `F : C ⥤ D` (Street
and Walters, "The comprehensive factorization of a functor", 1973)
is the unique (up to isomorphism) factorization `F = m ∘ e` where
`e` is a final functor and `m` is a discrete fibration; dually
through a discrete opfibration. It passes through a presheaf on `D`
whose value at `d` is the set of connected components of the
structured-arrow category `d ↓ F`.

The Mendler–Lambek correspondence (Vene, "Categorical Programming
with Inductive and Coinductive Types", Tartu 2000, sections 5.3–5.7;
Uustalu, cited by Neumann) relates Mendler-style algebras for a
difunctor `G` — dinatural transformations out of the hom-profunctor
`Hom(-,pt)` — to conventional algebras for the `G`-extension
functor `G^e`, defined via a restricted coend of `G` weighted by
`HomToProf(pt)`. The equivalence can be re-expressed using
end-power duality: `Hom(G^e(pt), Y) ≃ ∫_A Hom(G(A,A), Y^{A→pt})`.

Mathlib contains `CategoryTheory.Limits.Shapes.End` with
`end_`/`coend` (as (co)limits over twisted-arrow categories) but
they are noncomputable; the twisted-arrow category itself appears
as `CategoryTheory.TwistedArrow` in recent mathlib, though the
codebase predates that addition and builds its own.

## Modules

- [`GebLean/Utilities/Profunctors.lean`](../../GebLean/Utilities/Profunctors.lean)
  — foundational profunctor infrastructure. Defines `opProd`,
  `opProdSym`, and a suite of reindexing equivalences;
  `Prof.map₁`/`Prof.map₂` for the partial actions of a bifunctor
  `Cᵒᵖ × C ⥤ D`; composition laws `Prof.map₁_comp`,
  `Prof.map₂_comp`; bifunctor naturality `Prof.map_comm`; the
  projection profunctor `ProjProf`; constant and forgetful
  profunctors `constProfunctor`/`covProfunctor`/`contravProfunctor`;
  the `Collage` category of a profunctor; and the hom-bifunctor
  variants `homFromFunctorBifunctor`/`homToFunctorBifunctor`.
  Profunctors are textbook (Loregian 2021; nLab "profunctor");
  the `D`-valued partial-map API and `Collage` are original
  packaging over mathlib's `CategoryTheory.Functor.Hom`.

- [`GebLean/Utilities/TwistedArrow.lean`](../../GebLean/Utilities/TwistedArrow.lean)
  — twisted-arrow and co-twisted-arrow categories. Defines
  `TwistedArrow C` (= `Elements(Functor.hom C)`), `CoTwistedArrow C`
  (= `ElementsPre(homPreOp)`), and their primed variants over
  `ᵒᵖ'`; establishes `twistedArrowEquivTwistedArrowOp` (self-duality
  `Tw(C) ≌ Tw(Cᵒᵖ)`), the categorical isomorphism
  `(TwistedArrow C)ᵒᵖ ≅ CoTwistedArrow C`, and helper accessors
  `twObjMk`/`twDom`/`twCod`/`twArr`/`twHomMk`. The twisted-arrow
  category is described in Loregian 2021 §1; mathlib later added
  `CategoryTheory.TwistedArrow` (post this code).

- [`GebLean/Utilities/EndsAndCoends.lean`](../../GebLean/Utilities/EndsAndCoends.lean)
  — computable ends and coends for `Type`-valued profunctors.
  `typeEnd F` is the subtype of compatible families satisfying the
  wedge condition; `typeCoend F` is a quotient by the cowedge
  relation `typeCoendRel`; `typeEndWedge_isLimit` and
  `typeCoendCowedge_isColimit` show these coincide with mathlib's
  noncomputable constructions. Also defines `typeEndFunctor` and
  `typeCoendFunctor`. The end/coend theory is classical (Mac Lane;
  Loregian 2021); mathlib's `end_`/`coend` are noncomputable. The
  computable subtype/quotient implementations are original.

- [`GebLean/Utilities/PowersAndCopowers.lean`](../../GebLean/Utilities/PowersAndCopowers.lean)
  — type-indexed (co)powers for categories. The typeclass
  `HasCopowers` bundles the copower object `S ·. X` with
  injections, a universal `desc` map, and laws `fac`/`uniq`;
  functoriality in both argument positions via `mapVal`/`mapIdx`;
  dual `HasPowers` and `X ^. S`. Used throughout the area to
  state end-power duality. Type-indexed (co)powers are described
  in Kelly, *Basic Concepts of Enriched Category Theory* (1982),
  §3.

- [`GebLean/Utilities/ConnectedComponents.lean`](../../GebLean/Utilities/ConnectedComponents.lean)
  — connected-component utilities. `connectedComponentsOpEquiv`
  is the equivalence `ConnectedComponents Jᵒᵖ ≃
  ConnectedComponents J`; `IsInhabitedConnected` is the
  data-level strengthening of `IsConnected` with an `Inhabited`
  instance rather than a mere `Nonempty`. Used by the
  comprehensive-factorization construction. The op-equivalence
  of connected components is folklore; mathlib has `IsConnected`.

- [`GebLean/Utilities/TwArrPresheaf.lean`](../../GebLean/Utilities/TwArrPresheaf.lean)
  — functor categories over the twisted-arrow category. Defines
  `TwArrCopresheaf C` (= `TwistedArrow' C ⥤ Type v`) and its
  `TwArrPresheaf`/`TwArrOpCopresheaf`/`TwArrOpPresheaf` variants;
  `sliceEquivTwArrCopresheaf : Over hom' ≌ TwArrCopresheaf C`
  via the slice–copresheaf equivalence; and the slice presheaf
  induced by a `TwArrCopresheaf` via `slicePresheaf`. The
  slice-over-hom equivalence to copresheaves on the twisted-arrow
  category is noted in Loregian 2021 §1.

- [`GebLean/Paranatural.lean`](../../GebLean/Paranatural.lean)
  — category of diagonal elements and paranatural transformations.
  `DiagElem F` is the structure of a diagonal element of an
  endoprofunctor; `DiagCompat` is the compatibility condition for
  morphisms; `DiagElem.category` assembles the category of diagonal
  elements; `Paranat F G` is the type of paranatural transformations
  from `F` to `G`, with `Paranat.comp` and the `parana tCategory`.
  Follows Definition 2.7 in Neumann 2023. Paranatural
  transformations appear in Neumann 2023 and Uustalu.

- [`GebLean/ParanatAlg.lean`](../../GebLean/ParanatAlg.lean)
  — paranatural transformations and initial algebras. Defines
  `AlgProf F` (the algebra profunctor `(x,y) ↦ F(x) ⟶ y`) and
  `CoalgProf F`; establishes `DiagElem (AlgProf F) ≌
  Endofunctor.Algebra F`; `HomToProf pt` (the profunctor
  `(A,B) ↦ A ⟶ pt`); `DiagElem IdProf ≌ Pointed C`; and the
  bijection `Paranat (AlgProf F) IdProf ≃ μF` when `F` has an
  initial algebra. Follows Neumann 2023 §4, citing Uustalu. Also
  defines `MendlerAlgebra G`, the restricted cowedge
  `RestrictedCowedge G W`, and `GExtFunctor G` (via restricted
  coend). The algebra-profunctor equivalence and Mendler algebra
  formulation follow Vene 2000 §5 and Neumann 2023.

- [`GebLean/HexagonCat.lean`](../../GebLean/HexagonCat.lean)
  — the hexagon category of bifunctor transformations.
  `HexagonObj P Q` (pairs `(c, f : P(c,c) ⟶ Q(c,c))`) with
  `HexagonCondition` (the hexagon commutativity constraint on
  morphisms `m : c ⟶ d`) assemble into `HexagonCat`; the module
  also defines `ProfDialgebraProf P Q` (the profunctor
  `(a,b) ↦ P(b,a) ⟶ Q(a,b)`) and establishes
  `hexagonCatEquivDiagElem : HexagonObj P Q ≌ DiagElem
  (ProfDialgebraProf P Q)`.
  This dialgebra-like category was an exploration of dual-variance
  transformations (paranatural transformations); it is superseded by
  the parametric-transformation approach (the polynomial-functors
  area's `ParamPoly.lean`), which generalizes those notions.

- [`GebLean/Weighted.lean`](../../GebLean/Weighted.lean)
  — weighted limits and colimits via the twisted-arrow category.
  `profunctorOnTwistedArrow C P` is the functor `TwistedArrow C ⥤ D`
  induced by `P : Cᵒᵖ ⥤ C ⥤ D`; `coneToWedgeComponents` converts
  cones over this functor to wedge projections; and
  `cone_determined_by_wedge_components` shows a cone is determined
  by its diagonal components. Also defines `weightedCoconeDiagram`
  and the `profPullback` of a profunctor along a functor. The
  characterization of wedges as cones over the twisted-arrow
  category is in Loregian 2021 §1 and Riehl, "Weighted Limits
  and Colimits" (2014).

- [`GebLean/WeightedAlg.lean`](../../GebLean/WeightedAlg.lean)
  — Mendler–Lambek correspondence via restricted coends. Defines
  `HomToProf pt` (reused from `ParanatAlg`), `MendlerAlgebra G`,
  `PowerEndMendlerAlgebra G` (using end powers instead of
  paranatural transformations), `ConventionalAlgebra`, and
  `mendlerAlgPowerEndEquiv : MendlerAlgebra G ≌
  PowerEndMendlerAlgebra G`. Implements Theorem 5.19 of Vene 2000.
  This follows Vene 2000 §5.3–5.7.

- [`GebLean/DinaturalNumbers.lean`](../../GebLean/DinaturalNumbers.lean)
  — endo-paranatural transformations of the hom-profunctor on
  `Type` are natural numbers. `HomProf` is the curried hom-functor;
  `iterateN n f` iterates `f` exactly `n` times; `natToParanat`
  sends `n` to the "iterate n times" transformation; the round-trip
  bijection `paranatNatEquiv : Paranat HomProf HomProf ≃ ℕ` is the
  main result. The characterization of paranatural endo-
  transformations of the hom functor as `ℕ` is noted in Neumann
  2023 and attributed to the classical "Hom(Id,Id) ≅ ℕ" result
  (Freyd–Scedrov).

- [`GebLean/ProfAlg.lean`](../../GebLean/ProfAlg.lean)
  — polynomial profunctors and their algebras. `PolyProf` packages
  a type `B` of positions and two arity families `arity_neg`/
  `arity_pos`; `PolyProf.eval V W` is
  `Σ_b ((arity_neg b → V) → (arity_pos b → W))`;
  `PolyProf.DiagElem` are the diagonal elements, generalizing
  algebras for endofunctors; and `PolyProf.toCatProf` embeds a
  polynomial profunctor as a categorical profunctor. This module
  bridges the polynomial-functors area (which assigns the file
  there via dependency on `Polynomial.lean` and `PolyAlg.lean`)
  with the profunctor layer.

- [`GebLean/Factorization.lean`](../../GebLean/Factorization.lean)
  — factorization categories and their relation to twisted arrows.
  Re-exports mathlib's `Factorisation f` and adds
  `factorisationFunctor : TwistedArrow C ⥤ Cat` (sending each
  arrow to its factorization category), the opposite equivalence
  `factorisationOpEquiv : (Factorisation f)ᵒᵖ ≌ Factorisation (f.op)`,
  `TotalFactObj` (the total factorization category),
  `factorisationUnderOverEquiv`/`factorisationOverUnderEquiv`,
  and the reflective inclusion `factorisationToOverTw ⊣
  overTwToFactorisation`. The factorization category is classical
  (nLab "factorization category"); we are not aware of any
  other formulations of the aggregation of factorization
  categories into a `Cat`-valued functor and the consequent
  possibility of using the "connected Grothendieck construction"
  (which might also be new to this codebase) on it.

- [`GebLean/ComprehensiveFactorization.lean`](../../GebLean/ComprehensiveFactorization.lean)
  — the Street–Walters comprehensive factorization. Defines
  `IsDiscreteFibration`/`IsDiscreteOpfibration`; the intermediate
  presheaf `K(d) = ConnectedComponents(StructuredArrow d F)` and
  its copresheaf dual; the comprehensive functor
  `comprehensiveE : C ⥤ Gr(K)` and `comprehensiveM : Gr(K) ⥤ D`; proves
  `comprehensiveE` final and `comprehensiveM` a discrete fibration
  (`comprehensiveM_isDiscreteFibration`); and the strict factorization
  `comprehensiveFactorization_comm : comprehensiveE ⋙ comprehensiveM = F`.
  Street and Walters 1973; also Johnstone, *Sketches of an Elephant*
  B2.5.

- [`GebLean/ComprehensiveWeighted.lean`](../../GebLean/ComprehensiveWeighted.lean)
  — compatibility between the comprehensive factorization and
  weighted cocones. Proves `profOnCoTwArr_profPullback` and
  `profOnTwArr_profPullback` (that pulling back a profunctor
  commutes with the twisted-arrow map);
  `weightedCoconeDiagram_eq` (the weighted cocone diagram equals
  `elementsPre_π W ⋙ G`); and `comprehensiveCoconeEquiv`
  (the equivalence between cocones for `F ⋙ G` and weighted
  cocones over the comprehensive factorization). The connection
  between the comprehensive factorization and colimit formulas is
  noted in Street 1980 and Loregian 2021.

- [`GebLean/WedgeWeightComputation.lean`](../../GebLean/WedgeWeightComputation.lean)
  — concrete descriptions of the wedge weight functor. The wedge
  weight `wedgeWeight H : TwistedArrow C ⥤ Type v` represents
  the paranatural-transformation weight; `wedgeWeightIdentityMap`
  sends diagonal elements to the wedge weight at identity twisted
  arrows; `wedgeWeightIdentityMap_injective` proves injectivity;
  concrete `diagApp` descriptions for `AlgProf`, `CoalgProf`, and
  `HomProf`. The wedge weight construction and its role in
  representing paranatural transformations via
  `paranatWeightedLimitEquiv` are not in the standard literature
  on ends; the nearest antecedents are the weighted-limit
  characterization of ends (Kelly 1982, §3; Loregian 2021).
  (Unverified.)

- [`GebLean/RestrictedCoendAsColimit.lean`](../../GebLean/RestrictedCoendAsColimit.lean)
  — restricted coends as colimits over the category of elements.
  Identifies `diagApp (HomToProf pt) A ≅ (yoneda.obj pt).obj (op A)`;
  shows that the category of elements of `coyoneda'.obj pt` is
  equivalent to `Over pt`; constructs the diagram functor
  `Over pt ⥤ C` sending `(A, f : A ⟶ pt)` to `G(A,A)`; and
  establishes the colimit formula `G^e(pt) ≅ colim_{Over pt} G(-,-)`.
  Follows Kelly 1982 §3.4 and Vene 2000. The Kan extension/colimit
  interpretation of restricted coends follows Kelly 1982.

- [`GebLean/MendlerLambekEndPower.lean`](../../GebLean/MendlerLambekEndPower.lean)
  — Mendler–Lambek equivalence via ends and powers.
  `cowedgeHomEndEquiv` establishes coend-end duality: given an
  initial cowedge `c`, `(c.pt ⟶ Y) ≃ typeEnd (P ⇓ Y)`;
  `copowerPowerEquiv` converts copowers to powers inside the end;
  the combined characterization `Hom(G^e(pt), Y) ≃ ∫_A
  Hom(G(A,A), Y^{A→pt})` is the main result, as
  `mendlerAlgPowerEndEquiv : MendlerAlgebra G ≌
  PowerEndMendlerAlgebra G`. The end-power re-expression of the
  Mendler–Lambek equivalence follows Vene 2000 §5 and Kelly 1982
  §3.

- [`GebLean/MendlerLambekPresheaf.lean`](../../GebLean/MendlerLambekPresheaf.lean)
  — Mendler–Lambek equivalence for presheaf categories.
  Instantiates the end-power framework for `E ⥤ Type w`, where
  monoidal closure, copowers, and powers are all automatic;
  `presheafMendlerAlgPowerEndEquiv : MendlerAlgebra G ≌
  PowerEndMendlerAlgebra G` holds unconditionally, and
  `presheafMendlerLambekEndPowerEquiv : PowerEndMendlerAlgebra G
  ≌ ConventionalAlgebra (GExtFunctor G)` under
  `HasAllHomToProfCoends G`. The presheaf-category instantiation
  is implicit in Vene 2000.

## Alternative formulations

There is a single underlying concept — the computation of ends and
coends as (co)limits, the paranatural-transformation weight, and the
Mendler–Lambek equivalence — but the machinery develops in two
partially redundant directions. The `Type`-valued end/coend
constructions in `EndsAndCoends.lean` are computable, while
mathlib's `end_`/`coend` are noncomputable; the two are related
by `typeEndWedge_isLimit` and `typeCoendCowedge_isColimit`. The
Mendler–Lambek equivalence is expressed first in terms of restricted
cowedges (`WeightedAlg.lean`), then re-expressed via ends and
powers (`MendlerLambekEndPower.lean`), and instantiated for
presheaves (`MendlerLambekPresheaf.lean`); the three are
mathematically equivalent steps in a single derivation rather than
independent constructions.

## Dependencies

This area builds on the polynomial-functors area for `ProfAlg.lean`
(which imports `GebLean/Polynomial.lean` and `GebLean/PolyAlg.lean`).
The `Utilities/Elements.lean` and `Utilities/Grothendieck.lean`
modules (assigned to the internal-presheaf area) supply the
category-of-elements and Grothendieck-construction machinery used
throughout.

- [polynomial-functors area](polynomial-functors.md) — for
  `ProfAlg.lean` and the polynomial side of the parametric
  constructions.

## Pointers

- [`_provenance-claims.md`](_provenance-claims.md) — the consolidated,
  dated statement of this area's strongest novelty claim (the
  wedge-weight construction representing paranatural transformations).
- [`docs/research/coend-formulas-research.md`](../research/coend-formulas-research.md)
  — notes on coend calculus and the wedge/cowedge formalism.
- [`docs/research/weighted-cones-cocones-limits-colimits-ends-coends.md`](../research/weighted-cones-cocones-limits-colimits-ends-coends.md)
  — weighted (co)limit theory and the ends-as-weighted-limits perspective.
- [`docs/research/restricted-coends.md`](../research/restricted-coends.md)
  — restricted coends and their relation to Kan extensions.
- [`docs/research/wedge-cone-equivalence.md`](../research/wedge-cone-equivalence.md)
  — equivalence between wedges and cones over the twisted-arrow category.
- [`docs/research/wedge-weight-factorization-analysis.md`](../research/wedge-weight-factorization-analysis.md)
  — analysis of the wedge-weight factorization.
- [`docs/research/restricted-weighted-wedge-hierarchy.md`](../research/restricted-weighted-wedge-hierarchy.md)
  — the hierarchy of restricted weighted wedge structures.
- [`docs/research/weighted-vs-paranatural-algebra.md`](../research/weighted-vs-paranatural-algebra.md)
  — comparison of the weighted and paranatural algebra perspectives.
- [`docs/research/vene-mendler-style-sections-5.3-5.7.md`](../research/vene-mendler-style-sections-5.3-5.7.md)
  — detailed notes on Vene 2000 §5.3–5.7 (Mendler–Lambek correspondence).
- [`docs/research/comprehensive-factorization-research.md`](../research/comprehensive-factorization-research.md)
  — prior-art and implementation notes for the Street–Walters
  comprehensive factorization.
- [`docs/research/paranatural-topos-research.md`](../research/paranatural-topos-research.md)
  — notes on paranatural transformations in topos contexts.
- [`docs/superpowers/specs/2026-04-13-strict-two-sided-grothendieck-design.md`](../superpowers/specs/2026-04-13-strict-two-sided-grothendieck-design.md)
  — design spec for the strict two-sided Grothendieck construction,
  which underpins the twisted-arrow and comprehensive-factorization
  constructions.
