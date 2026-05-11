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
  sub-project.
- **Scope**: Continue Phase 4g.2 (the
  `LawvereERCat ≃ LawvereNatBTCat` three-stage equivalence
  via `LawvereNatBT0Cat` and `LawvereNatBTPureCat`), then
  Phase 4g.3-4g.5 (transport of non-fullness results and
  Lex-level parity) and Phase 5 (internal-category
  structure inside `LawvereTreeERLexCat`).
- **Files**: `GebLean/LawvereER*.lean`,
  `GebLean/LawvereTreeER*.lean`,
  `GebLean/LawvereNatBT*.lean`,
  `GebLean/Utilities/ER*.lean`.

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
  rather than carried forward here.
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
  interfaces.
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
