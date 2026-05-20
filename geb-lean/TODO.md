# TODO

Active workstreams in this repository. Hierarchical,
topological: parents listed first, children indented under
them. A workstream is removed from this file when its work
is complete or when it moves into the "to be done in
geb-mathlib" section. Completed content's documentation
lands in `docs/index.md`.

## Active in geb-lean

### lawvere-elementary-recursive

- **Status**: Phase 4g.2 in progress as the `LawvereNatBT`
  sub-project; the `er-ksim2-equiv-via-urm` sub-project has
  the forward direction `kToER` complete through Step 5 and
  the reverse direction `erToK` partially complete: the URM
  kernel (T1, ≈ Step 7) and the ER → URM compiler with
  correctness theorem `compileER_runFor` (T2, ≈ Steps 6+8)
  have landed. T3 (K^sim simulator for URM, ≈ Step 9), T4
  (`erToK`/`erToKFunctor` assembly, ≈ Step 10), and the
  categorical iso (≈ Step 11) remain. A post-T2 follow-up
  branch (task #654) tracks deferred cleanups (naming
  sweeps, structural extraction, private-promotion
  re-evaluation).
- **Scope**: Continue Phase 4g.2 (the
  `LawvereERCat ≃ LawvereNatBTCat` three-stage equivalence
  via `LawvereNatBT0Cat` and `LawvereNatBTPureCat`), then
  Phase 4g.3-4g.5 (transport of non-fullness results and
  Lex-level parity) and Phase 5 (internal-category
  structure inside `LawvereTreeERLexCat`). The
  `er-ksim2-equiv-via-urm` sub-project formalises the
  categorical equivalence `LawvereKSimDCat 2 ≌ LawvereERCat`;
  Steps 0-5 (master design, ER tupling, ER simultaneous
  bounded recursion, Tourlakis A-majorants, K^sim
  majorization, and the `kToERFunctor : LawvereKSimDCat 2 ⥤
  LawvereERCat`) are complete. T1 (URM kernel in
  `GebLean/Utilities/ZeroTestURM.lean`) and T2 (ER → URM
  compiler in `GebLean/LawvereERKSim/{Compiler,Embedding,Loops,Atoms,Comp,BSum,BProd,Top}.lean`,
  ≈ 28 000 LOC, `[propext, Quot.sound]`-only) are
  complete. The next workstream is T3: a K^sim simulator
  for the URM kernel, whose output combined with T2's
  `compileER` will yield the `erToK` morphism (T4) and the
  categorical iso (T5).
- **Scope (natEq / elegant pairing arithmetic
  pipeline)**: Prove `natEq` transitivity and
  `elegantPair` injectivity so that `treeEqG_ββ` becomes
  unconditional. Carries through the integer-square-root
  pipeline (`isqrtStep`, `isqrtState`, `isqrt`,
  `elegantPair`, `elegantUnpair`) on the parameterized
  NNO side, including within-level stability for
  `isqrtState` and the level-transition lemma
  `natSquare ≫ isqrtState = isqrtLevelState`.
- **Scope (term-cat / binary-tree-category
  substrate)**: the Lawvere theory of binary trees and
  the tree-calculus Phase 2 layer underpinning the ER /
  K^sim pipeline, comprising the `LawvereBT*` /
  `LawvereNatBT*` material in `GebLean/` and the
  tree-calculus modules in `GebLean/PLang/` (value
  polynomial, two-sorted computation polynomial,
  behaviour polynomial and reduction coalgebra, derived
  combinators, PCA structure, confluence). Remaining
  Phase 2 tasks: the GSOS rule and distributive law for
  triage, the primitive-recursive fragment with
  syntactic criterion, the self-recognizer, and the
  final integration test suite.
- **Scope (Gödel-numbering tree-equality
  pipeline)**: the categorical Gödel-encoding of binary
  trees as natural numbers and the derivation of
  decidable tree equality via natural-number equality
  (`treeToNat`, `treeEqG`, `natEq`, the Cantor-pairing
  / triangular-number infrastructure, `triRootState`
  and the shifted-NNO recurrences). Supports the
  reverse direction `erToK` by providing the
  arithmetic substrate for tree-side encodings.
  Remaining items: closing `NatEqCantorPair` (the
  Cantor-pair injectivity statement under `natEq`)
  to make `treeEqG_ββ` unconditional, and
  `treeEqG_trans` via the addition-subtraction
  identity and `natTruncSub_fold_comp`.
- **Files**: `GebLean/LawvereER*.lean`,
  `GebLean/LawvereTreeER*.lean`,
  `GebLean/LawvereNatBT*.lean`,
  `GebLean/LawvereKSim*.lean`,
  `GebLean/PLang/TreeCalc*.lean`,
  `GebLean/PLang/TermCat.lean`,
  `GebLean/PLang/Syntax.lean`,
  `GebLean/Utilities/ER*.lean`,
  `GebLean/Utilities/KArith.lean`,
  `GebLean/Utilities/RegisterMachine.lean`,
  `GebLean/Utilities/SzudzikSeq.lean`,
  `GebLean/Utilities/KSimSzudzikSimrec.lean`,
  `GebLean/Utilities/Tower.lean`,
  `GebLean/Utilities/Tupling.lean`,
  `GebLean/Utilities/SimRec.lean`,
  `GebLean/Utilities/ComputationalComplexity.lean`,
  `GebLean/NatElegantPair.lean`,
  `GebLean/NatArith.lean`,
  `GebLean/NatNNO.lean`,
  `GebLean/TreeGoedel.lean`,
  `GebLean/TreeEqGoedel.lean`,
  `GebLean/TreeLogic.lean`.

### 2026-05-09 process-bootstrap monorepo refactor

- **Status**: executing
- **Spec**:
  `docs/superpowers/specs/2026-05-09-process-bootstrap-monorepo-design.md`
- **Plan**: `plans/2026-05-09-process-bootstrap-monorepo-plan.md`
- **Scope**: Stand up the monorepo-aware process scaffolding
  (CLAUDE.md split, `.claude/rules/`, `docs/process.md`,
  `docs/index.md`, this `TODO.md`, hooks, jj layout) under
  Milestone A; perform `.session/` triage and removal under
  Milestone B.
- **Next**: Continue Milestone A task execution per the plan.
- **Note**: Status advances to `awaiting-Milestone-B-completion`
  once Milestone A is signed off (Task A34); the entry is
  removed from `TODO.md` once Milestone B concludes.

## To be done in geb-mathlib (not pending here)

Items intentionally deferred until after migration to the
new repository, where the curated context there applies.
**None of the items in this section are pending in the
present repository.** Listed here so the work is not lost.

- **generic-eat-embedding**: generalise the
  `CategoryJudgments` construction to embed any
  essentially algebraic theory `T` into a copresheaf
  category `[J_T, Type]` via a two-stage adjunction
  (completion plus quotient).
- **higher-categorical-structure**: investigate whether the
  iterated copresheaf category `[J^n, Type]` provides a
  natural home for n-categorical and ω-categorical
  structure, including the cubical and globular variants.
- **lean-430-upgrade**: deferred because `geb-mathlib` will
  track mathlib releases closely from the start, so the
  `Polynomial.lean` `TypeCat.Hom` migration work owed by the
  `v4.30.0-rc1` upgrade is undertaken in that repository
  rather than carried forward here. Absorbs the earlier
  `potential-lean-430-port` strategic-decision investigation
  (restructure-vs-grind-vs-defer options, calibrated
  ~25-30 hour cost estimate, root-cause analysis of the
  `TypeCat.Fun.toFun_apply` simp priority and the
  Sigma-transport motive-not-type-correct failures), now
  resolved in favour of deferral to `geb-mathlib`.
- **indexed-eat-implementation**: instantiate the
  `EATHasQuotient` typeclass on non-trivial essentially
  algebraic theories (starting with the category EAT) so the
  combined `L ⊣ Φ` adjunction applies beyond the trivial
  case currently in `GebLean/PLang/IndexedEAT.lean`.
- **grothendieck-refactoring**: refactor polynomial functor
  operations to work at the categorical level via double
  Grothendieck constructions, replacing low-level
  dependent-type transport proofs with `functorFrom`,
  `functorTo`, and `functorBetween` universal-property
  interfaces. Absorbs the earlier
  `polynomial-functor-extensions` line of investigation (free
  monad monad, cofree comonad comonad, small adjunctions with
  `Type`, epi/mono and vertical/cartesian factorisations,
  universal morphisms, dual-variance polynomial functors, and
  the polynomial double category), all of which depend on the
  Grothendieck-construction reformulation rather than the
  current low-level Sigma-transport encoding.
- **plang-category-judgments**: complete the
  universe-polymorphic `L ⊣ Φ` adjunction between
  `Cat.{v,u}` and `CatJudgCopr.{u,v,w,x}` with all four
  universe levels independent, including the reflective
  embedding instances (`FullyFaithful Φ`, `Reflective Φ`),
  triangle identities, and the recursive generalization
  `CatJudgCoprRec`. Deferred so the work proceeds on top of
  Geb-native category-theory foundations rather than the
  current Lean encoding; an earlier draft was set aside in
  favour of the current Phase-3 universe-flexible formulation,
  which is the version carried forward.
- **poly-distributive-law**: complete the GSOS-rule phase
  (Steps 10-14) on top of the distributive law
  `λ : T·D ⟶ D·T` between the free monad and cofree comonad
  of a polynomial endofunctor, including the fiberwise
  product, the `GSOSRule` structure, the canonical GSOS, and
  the construction of a distributive law from a GSOS rule.
  Deferred so the GSOS layer is built on top of Geb-native
  polynomial-functor foundations rather than the present Lean
  encoding.
- **poly-native-replacement**: complete Phase 2 of the
  replacement programme, substituting Lean-native inductive
  types in `GebLean/PolyAlg.lean` (W-types, M-types, free
  monad, cofree comonad approximations and agreements) with
  the proven-isomorphic polynomial fixed-point versions, so
  that `PolyFix` is the sole consumer of Lean's native
  inductive-type machinery. Deferred so the replacement is
  carried out atop Geb-native polynomial-functor foundations
  rather than the current Lean encoding.
- **poly-presheaf-ccc**: generalise the polynomial-functor
  category `PolyFunctorBetweenCat` from slice categories
  `Over X` to presheaf categories `PSh(D)` via parametric
  right adjoints, and prove the resulting category of
  polynomial functors on presheaves is cartesian closed
  (prerequisite for the endofunctor CCC structure on
  `PshRelEdge C`). Deferred so the construction is built on
  Geb-native polynomial and presheaf foundations rather than
  the current Lean encoding.
- **poly-presheaf-equivalence**: prove the equivalence
  `PolyFunctorBetweenCat X Y ≌ PresheafPRACat (Discrete X)
  (Discrete Y)` between polynomial functors over slice
  categories and presheaf-parametric-right-adjoint functors
  on discrete bases, assembled as a composition of four
  named categorical equivalences with explicit universe
  annotations. Deferred so the equivalence is constructed on
  Geb-native polynomial and presheaf-PRA foundations rather
  than the current Lean encoding.
- **polynomial-adjunctions**: complete the suite of
  adjunctions between polynomial-functor categories and
  `Type` (or slice categories): the free/forgetful adjunction
  for polynomial functors over `Type`, slice-based
  adjunctions relating `PolyFunctorBetweenCat X Y` to slice
  categories, the cofree/forgetful adjunction, and the
  adjunctions arising from the family-slice equivalence.
  Deferred so the adjunction layer is built on Geb-native
  polynomial-functor foundations rather than the current Lean
  encoding.
- **cat-depcategorydata-reflective**: complete the reflective
  inclusion `Cat ↪ DepCategoryData` by reflecting the
  `Exists`, `CategoryLaws`, and `Unique` properties along the
  stacked subcategory chain `DepCategoryData ⊃ DepCompleteObj
  ⊃ DepCompleteCL ⊃ DepCompleteUCL ⊃ DepCategoryCat`.
- **exact-completion-pbto**: complete the PER-based exact /
  ex-lex completion of `LawvereBTQuotCat`, including the
  remaining Layer-1 tasks (finite coproducts via the
  `inl/inr` tag encoding, PBTO preservation with `(T,
  treeEq)` as the PBTO, decidability of every object, and
  preservation of limits and colimits by `interpFunctor`),
  the LawvereBTQuotCat coproducts instance, and the
  prospective Layer-2 general PER category that drops
  `rel_bool` to gain coequalizers, regularity, and exactness.
- **endofunctor-ccc**: complete `MonoidalClosed (PshRelEdge C
  ⥤ PshRelEdge C)` (the endofunctor category of
  `PshRelEdge C` is cartesian closed). The general
  endofunctor formulation has a universe gap that polynomial
  endofunctors are expected to bridge.
- **endofunctor-ccc-adjunction**: build the
  `tensorLeft F ⊣ endoIhomFunctor F` adjunction underlying
  the `MonoidalClosed` instance above, including the
  representable-density infrastructure, the end projection at
  representables, the full curry, the uncurry via density and
  the round-trip proofs.
- **double-categories**: complete the strict double-category
  layer, including the uniqueness isomorphism of companions
  (mate correspondence, connections, or universal-property
  characterisation), and supply further examples beyond
  `YonedaRel` (spans, commutative squares in a category,
  quintets in a 2-category), tabulators, weak double
  categories, double limits and colimits, and the connection
  to 2-categories and bicategories.
- **copresheaf-coequalizer-equivalence**: complete the
  equivalence `PolyPresentationLoc D ≌ (D ⥤ Type)` between
  the localised category of polynomial presentations and the
  category of copresheaves, including essential surjectivity
  via the density formula, comparison-morphism inversion in
  the localised category, and the assembled equivalence; or
  alternatively the fully constructive setoid-valued variant
  `PolyPresentationLoc D ≌ (D ⥤ SetoidCat)` that avoids
  quotient choice.
- **paranatural-investigations**: investigate the
  paranatural / strong-dinatural structure including
  the dialgebra category and its diagonal-element
  equivalence, the presentation of structure /
  costructure integrals as Type-valued ends and
  coends, wedges and cowedges as diagonal-element
  categories, the parametricity / paranaturality
  divergence at higher kinds (`updates-on-paranatural`
  slides), and slice-presheaf equivalences for
  diagonal elements.
- **parametricity-free-theorems**: formalise Wadler's
  "Theorems for free!" (1989) and Reasonably Polymorphic
  blog-post correspondences in a generalised
  categorical setting. The track has a type-level
  System F layer (`ParanaturalTopos.lean`,
  `RelSpanDiagram.lean`, etc.) serving as the
  `C = Discrete PUnit` specialisation, and a
  presheaf-level layer based on `PshRelEdge C`
  (`PshRelDouble.lean`, `PshRelEdge*.lean`,
  `PshRelEdgeInclusion.lean`). Absorbs the earlier
  `parametric-generalization` line of investigation, the
  earlier `polynomial-profunctors` line of investigation
  (`PolyProf` / `GenPolyProf` for dual-variance datatypes such
  as PHOAS, with diagonal-element categories generalising
  algebras and coalgebras), now subsumed by the
  `PshRelEdge`-based formulation of parametric polymorphism,
  and the earlier `psh-parametric-free-theorems` line of
  investigation (the presheaf-level free-theorems layer
  `PshRelEdge C`), now treated as a sub-layer of the present
  workstream, the earlier `weighted-vs-paranatural-algebra`
  investigation of whether weighted (co)ends provide equivalent
  formalisations of the three algebraic justifications for
  paranatural transformations (initial-algebra carrier,
  terminal-coalgebra carrier, Church numerals), and the earlier
  `yoneda-rel-parametricity` line on `YonedaRel`-mediated
  parametric relations, both subsumed by the present
  `PshRelEdge`-based formulation of parametric polymorphism.
- **parametric-copresheaf-topos**: develop the general
  theory of parametric polymorphism via the edge
  category `PshRelEdge C` and its reflective embedding
  into the presheaf topos `[WalkingSpan, PSh(C)]`,
  including the three-layer
  `[WalkingSpan, PSh(C)] -> PshRelEdge C -> Sh_J(C × I^op)`
  presentation, the match against Wadler's
  "Theorems for free!" framework, and the conjectural
  sheafification step.
- **parameterized-list-object**: investigate a
  PSTO → PBTO construction in
  `GebLean/PSTOtoPBTO.lean`. The five direct approaches
  attempted there (enriched-carrier catamorphism, PSO
  paramorphism, fixed-point equation, double PSO fold,
  product carrier) all stall at the same point: the
  PSO/PSTO fold does not provide a recursive result on
  the right subtree. A construction likely requires
  additional structure beyond the PBTO universal
  property (internal fixed-point operator, parameterized
  NNO, or exponential objects).
- **over-category-equiv**: complete Phase 8 of the
  Over/Arrow-based category-equivalence programme in
  `GebLean/Utilities/OverCategoryEquiv.lean` and
  `GebLean/CatJudgmentAdjunction.lean`: respect of
  `FreeMor.mapQuiver` for the free-morphism equivalence,
  universe generalisation to `{v, u}`, unit and counit
  natural transformations, triangle identities, and the
  mathlib `Adjunction` integration. Phase 6d natural
  isomorphisms for the over/cat round-trip also fall
  here.
- **mendler-lambek-correspondence**: extend the existing
  `MendlerAlgebra G ≌ ConventionalAlgebra (GExtFunctor G)`
  correspondence (Vene 2000, §5.3-5.7) along the lines
  opened in `GebLean/WeightedAlg.lean` and
  `GebLean/MendlerLambekPresheaf.lean`, including the
  open question of whether weighted Mendler coends agree
  with restricted Mendler coends when both exist.
- **mendler-lambek-end-power-formulation**: complete the
  Phase-6 end-based reformulation of the Mendler-Lambek
  equivalence in `GebLean/MendlerLambekEndPower.lean`,
  including enriched Yoneda factorisation under the
  `ihomCoendHasTerminalWedge` specialisation, the
  `HasAllHomToProfCoends G` instance for `C = Type v`,
  and the presheaf instantiation
  `C = E ⥤ Type v`.
- **polynomial-algebra-coalgebra-combinators**: complete the
  polynomial-algebra/coalgebra combinator library, including the
  outstanding Phase-4 items (interaction map
  `Xi : m_P ⊗ c_Q → m_{P ⊗ Q}` and the module structure of the
  free monad functor over the cofree comonad functor), the
  remainder of Phase-5 (the operational monad lifting syntax to
  behaviour coalgebras), and the deferred B1/B2/F1-F3 items
  (copresheaves as a variety of unary algebras, fiber
  decomposition over the terminal coalgebra, Stone topology on
  M-types, and the sheaf topos
  `Sh(c_P(1))`). Deferred so the
  construction is built on Geb-native polynomial-functor
  foundations rather than the current Lean encoding.
- **polynomial-double-category**: complete Phase 5 of the
  polynomial double-category construction (the adjunction
  bijection between the pushout-based 2-cell formulation
  `SPFnt (Sigma . f . BaseChange bcl) g` and the
  natural-transformation formulation
  `SPFnt (Sigma . f) (g . Sigma bcr)`, formalised as an
  equivalence of types via the sigma / base-change adjunction).
  Deferred so the bijection is established on Geb-native
  polynomial-functor foundations rather than the current Lean
  encoding.
- **pra-universal-morphisms**: complete the universal-morphisms,
  composition, algebra, and double-category structure for
  presheaf-PRA functors, generalising the existing
  polynomial-functor infrastructure from slice categories to
  presheaf categories. Includes Phase A (limits and colimits via
  the position/direction decomposition), Phase B (closed
  monoidal structure: cartesian product, internal hom,
  Dirichlet product and closure), Phase C (identity, composition,
  PRA factorisation `π_! ∘ E^*`), Phase D (algebras and
  coalgebras, W- and M-types, free monads, cofree comonads), and
  Phase E (the double category with small categories as objects,
  functors as vertical morphisms, PRAs as horizontal morphisms,
  and natural transformations as cells). Deferred so the
  construction proceeds on Geb-native presheaf-PRA foundations
  rather than the current Lean encoding.
- **presheaf-pra**: complete the presheaf-PRA programme started
  in `GebLean/PresheafPRA.lean` and continued in
  `PresheafPRADiscrete.lean`, `PresheafPRAUMorph.lean`,
  `PresheafPRADirNat.lean`, and `PresheafPRAEvalAtINat.lean`,
  including Phase 3 (identity and composition via
  Beck-Chevalley, PRA factorisation), the remaining Phase 4
  items (universal morphisms for `PresheafPRACat I J` via the
  underlying presheaf categories, the cartesian product,
  internal hom, and Dirichlet product), Phase 5 (algebras and
  coalgebras for PRA endofunctors, initial algebras as W-types
  in presheaf categories, terminal coalgebras as M-types, free
  monads, cofree comonads), Phase 6 (the double category with
  small categories as objects, functors as vertical morphisms,
  PRAs as horizontal morphisms, natural transformations as
  cells), and the deferred
  `praEvalAtFunctor` `(I, J)`-naturality follow-up (a separate
  brainstorm using the fixed-`I` formula as a concrete reference
  for the appropriate `I`-natural object via paranatural
  transformations, lax-natural infrastructure, or
  restricted-source-mor conventions). Deferred so the
  construction proceeds on Geb-native presheaf-PRA foundations
  rather than the current Lean encoding.
- **connected-grothendieck**: complete the connected
  Grothendieck construction
  `E : Fun(Tw(C), Cat) ⥤ Cat/Arr(C)`, including the universal
  properties for the copresheaf and presheaf variants, the
  equivalence between `ConnectedGrothendieckContra` and
  `ConnectedGrothendieckAlt`, universe-level generalisation of
  `ConnGrothendieckObj` to `Cat.{w, w'}` so that
  `TwGrothendieckObj` accepts `factorisationFunctor`, and the
  `FunctorToConnGrothendieckData` /
  `FunctorFromConnGrothendieckData` characterisations of
  functors to and from the connected Grothendieck
  construction.
- **reflective-subcategory-conjectures**: prove the
  conjectured additional preservation properties of the
  `LFunctor ⊣ PhiFunctor` reflective adjunction documented
  in `GebLean/CatJudgmentAdjunction.lean` § `PreservationInstances`:
  binary-coproduct preservation by `PhiFunctor`, binary-product
  preservation by `LFunctor`, and exponential preservation by
  `PhiFunctor` (conditional on product preservation, via the
  exponential-ideal characterisation).
- **terminal-preservation-strategy**: carry the terminal-object
  preservation proof for `LFunctor` (the `TerminalAndInitial`
  section of `GebLean/CatJudgmentAdjunction.lean`) into
  geb-mathlib alongside the rest of the `L ⊣ Φ` adjunction,
  including the `terminal_freemor_equiv_id` induction, the
  `terminalToLFunctor` inverse, and the
  `lTerminal_roundtrip_*` lemmas.
- **tree-per-finite-limits**: complete finite limits in the
  category of partial equivalence relations on the binary-tree
  type, building on the existing terminal and binary-product
  PER infrastructure. Outstanding items: the equalizer lift
  pre-morphism and quotient morphism, the equalizer
  factorisation and uniqueness, the `Fork` / `IsLimit`
  assembly, and the `HasEqualizers` instance feeding
  `hasFiniteLimits_of_hasEqualizers_and_finite_products`.
  The `HasTreeEq LawvereBTQuotCat` construction (a
  prerequisite for downstream `LawvereBTPER` results) is
  recorded as needing one of three routes: a primitive-
  recursive completeness theorem, a Gödel-encoded reduction
  via `treeToNat` + `natEq`, or an axiomatic extension of
  `HasPBTO` supporting double structural recursion.
- **two-sided-grothendieck-equivalence**: complete the
  `CategoryTheory.Equivalence` between
  `twoSidedGrothendieckCovContra` and
  `twoSidedGrothendieckContraCov` in
  `GebLean/Utilities/Grothendieck.lean`, beyond the object-level
  `twoSidedGrothendieckObjEquiv`, the symmetric
  constructor / destructor namespaces, and the primitive
  `forwardObj` / `forwardMap` / `backwardObj` / `backwardMap`
  functions. The remaining items are the `forward` and
  `backward` Cat functors with `map_id` and `map_comp`,
  `unitIso` and `counitIso`, and the assembled
  `twoSidedGrothendieckEquivalence`. The `w_fiber` sub-goal of
  the functor laws requires motive-dependent `eqToHom` rewrites
  across three nested `Grothendieck` plus `Opposite` layers;
  three resumption strategies are recorded (bicategorical
  `Pseudofunctor` plus `StrongTrans` framework, an explicit
  intermediate "direct" form factoring the equivalence through
  a third presentation, or a hom-set bijection
  `∀ H x y, (x ⟶ y) ≃ (forwardObj x ⟶ forwardObj y)` weaker
  than `Equivalence`).
