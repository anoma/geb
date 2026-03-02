# Workstream: Polynomial Algebra/Coalgebra Combinators

## Status

Active

## Context

Building on the existing polynomial endofunctor infrastructure
(`PolyAlg`, `PolyCoalg`, `polyAlgMonadEquiv`,
`polyCoalgCopresheafEquiv`, limit/colimit instances), this
workstream adds further categorical combinators for algebras
and coalgebras of polynomial endofunctors on slice categories.

Mathematical details and references are in
`docs/polynomial-algebra-coalgebra-combinators.md`.

## Difficulty/Usefulness Estimates

Each item is rated on a 1-5 scale for difficulty (Diff) and
usefulness (Use).

| ID | Proposal | Diff | Use |
| -- | -------- | ---- | --- |
| G0 | Iteration/coiteration chain functors | 2 | 4 |
| G1 | Initial algebra as chain colimit | 3 | 5 |
| G2 | Terminal coalgebra as chain limit | 3 | 5 |
| G3 | Preservation corollaries | 2 | 5 |
| A0 | Finitariness predicate for polynomials | 1 | 4 |
| A1 | `HasColimitsOfSize (PolyAlg P)` (finitary) | 3 | 5 |
| A2 | Beck coequalizer for PolyAlg | 1 | 3 |
| A3 | Finitary free monad preservation | 3 | 5 |
| H0 | Poly functors preserve connected limits | 3 | 5 |
| H1 | Weak pullback preservation corollary | 1 | 4 |
| B1 | Copresheaves as unary algebra variety | 3 | 4 |
| B2 | Fiber decomposition over terminal coalgebra | 2 | 2 |
| C1 | Distributive law structure (monad/comonad) | 2 | 5 |
| C2 | lambda-Bialgebra category | 3 | 5 |
| C3 | Distributive law for poly free/cofree | 4 | 4 |
| D1 | Dirichlet product of polynomials | 2 | 3 |
| D2 | Interaction map Xi (pattern runs on matter) | 4 | 4 |
| D3 | Module structure of m over c | 4 | 3 |
| E1 | Abstract GSOS rules | 3 | 4 |
| E2 | Operational monad | 4 | 4 |
| F1 | Stone topology on M-types | 3 | 2 |
| F2 | Stone space property (finite polynomials) | 4 | 2 |
| F3 | Sheaf topos Sh(c_P(1)) | 5 | 2 |

## Tasks

### Phase 1: Fixed Points and Algebra Colimits

Express initial algebras and terminal coalgebras as chain
(co)limits, then build on the limit instances to complete
the (co)limit picture for finitary polynomial algebras.

- [x] G0: Construct `polyIterChain P : ℕ ⥤ Over X` sending
  `n ↦ P^n(initial)` via `Functor.ofSequence`, and dually
  `polyCoiterChain P : ℕᵒᵖ ⥤ Over X` sending
  `n ↦ P^n(terminal)`.  Also added `overInitial_isInitial`,
  `overTerminal_isTerminal`, `polyIterCocone` (cocone over
  the iteration chain with apex the W-type carrier), and
  `polyIterCoconeMap_naturality`.
- [x] G1: Prove `polyFixAlg P` (our W-type initial algebra)
  is the colimit of `polyIterChain P`.  Requires
  `PolyBetweenFinitary X X P` (strengthened to use `Fintype`).
  Done: `polyIterCocone_isColimit` in `PolyAlg.lean`.
- [x] G2: Prove `polyCofixCoalg P` (our M-type terminal
  coalgebra) is the limit of `polyCoiterChain P`.
  Done: `polyCofixCone_isLimit` in `PolyAlg.lean`.
- [x] G3: Preservation corollaries: six definitions at three
  levels of generality (specific diagram, shape,
  filtered/cofiltered) for both colimit and limit directions.
  Uses explicit preservation-evidence parameters (not
  mathlib's `PreservesColimit` typeclass) to remain
  constructive.  Part 2 (showing `polyEndoFunctor X P`
  preserves filtered colimits under finitarity) deferred to
  A3.  In `PolyAlg.lean`, section `PreservationCorollaries`.
- [x] A0: Define `PolyBetweenFinitary` for arbitrary polynomial
  functors between slices (all direction-set fibers are finite),
  and `PolyEndoFinitary` as the endofunctor specialization
- [x] A2: Instantiate Beck coequalizer (`beckAlgebraCoequalizer`)
  for `polyFreeMonad X P` to show every P-algebra is a reflexive
  coequalizer of free P-algebras (no finitariness needed);
  also added `OfAlg` variants taking `PolyAlg P` and
  transferring via `polyAlgMonadEquiv`
- [ ] A3: Prove that `polyFreeMonad X P` preserves filtered
  colimits when `PolyEndoFinitary P` holds (the free monad
  on a finitary functor is finitary)
- [ ] A1: Prove `HasColimitsOfSize.{u, u} (PolyAlg P)` under the
  hypothesis `[PolyEndoFinitary P]`, by showing a finitary
  polynomial endofunctor preserves filtered colimits (finite
  products commute with filtered colimits), then applying
  Linton's theorem via the monad equivalence
- [x] H0: Prove `PreservesLimitsOfShape J (polyEndoFunctor P)`
  for any `[IsConnected J]` (polynomial functors preserve
  connected limits; no finitariness needed).  Proved for all
  polynomial functors between slices, not just endofunctors.
  In `GebLean/PolyLimits.lean`.
- [x] H1: Instantiate H0 for wide pullbacks
  (`polyBetweenPreservesWidePullbacks`).  The `WalkingCospan`
  specialization is omitted due to a universe constraint:
  `WalkingCospan : Type 0` while the theorem chain requires
  `J : Type u` matching the category universe (from
  `Pi.coneOfConeEvalIsLimit`).
  In `GebLean/PolyLimits.lean`.

### Phase 2: Distributive Law Framework

Define the abstract categorical structures for distributive
laws and bialgebras (not specific to polynomial functors).

- [x] C1: Define `DistributiveLaw (T : Monad C) (D : Comonad C)`
  with four coherence axioms (unit, multiplication, counit,
  comultiplication).  In `GebLean/Utilities/DistributiveLaw.lean`.
- [x] C2: Define the category of lambda-bialgebras for a given
  distributive law, with the pentagonal compatibility law;
  includes `LambdaBialgebra` structure, `Hom` with `@[ext]`,
  `Category` instance, forgetful functor to `C` (faithful),
  and conversions to `T.Algebra`/`D.Coalgebra`.
  Also: `liftedComonad : Comonad T.Algebra` (lifting D
  through the distributive law) and
  `liftedMonad : Monad D.Coalgebra` (lifting T through the
  distributive law), with all endofunctor, unit/counit, and
  multiplication/comultiplication components.
  Category equivalence
  `lambdaBialgebraEquivLiftedComonadCoalgebra :
  LambdaBialgebra law ≌ (liftedComonad law).Coalgebra`.
  In `GebLean/Utilities/LambdaBialgebra.lean`.
- [x] C2a: Construct initial and final lambda-bialgebra
  objects (operational and denotational models).  Includes
  `freeBialgebra` / `cofreeBialgebra` (free bialgebra on a
  D-coalgebra / cofree bialgebra on a T-algebra),
  `freeBialgebraHom` / `cofreeBialgebraHom` (functoriality),
  `initialCoalgebra` / `terminalAlgebra` with initiality /
  terminality proofs, `initialBialgebra` /
  `finalBialgebra` with `IsInitial` / `IsTerminal` proofs,
  `universalSemantics` (unique morphism from operational to
  denotational model), and `universalSemantics_eq` (the
  morphism obtained via initiality equals the one via
  terminality).  Parameterized by `IsInitial` / `IsTerminal`
  witnesses rather than `HasInitial` / `HasTerminal` to
  remain constructive.
  In `GebLean/Utilities/LambdaBialgebra.lean`.

### Phase 3: Polynomial Distributive Law

Instantiate the distributive law framework for our polynomial
endofunctors.

- [ ] C3: Construct the canonical distributive law between
  `polyFreeMonad X P` and `polyCofreeComonad X P`
- [ ] E1: Define abstract GSOS rules as natural transformations
  `rho : Sigma(Id x B) => B . T` for polynomial signature and
  behavior endofunctors

### Deferred

These are documented for future consideration but not
currently planned for implementation.

- [ ] B1: Show `(PolyCofreeCat P ⥤ Type u)` is a variety of
  unary algebras (algebra side of Adamek intersection theorem)
- [ ] B2: Make explicit the fiber decomposition of the copresheaf
  functor over the terminal coalgebra anamorphism
- [x] D1: Define Dirichlet/parallel product `P ⊗ Q` of polynomial
  endofunctors (in `GebLean/Utilities/SlicePolynomial.lean`)
- [ ] D2: Construct interaction map
  `Xi : m_P ⊗ c_Q -> m_{P ⊗ Q}` (pattern runs on matter)
- [ ] D3: Verify module structure of free monad functor over
  cofree comonad functor
- [ ] E2: Construct operational monad (lifting syntax monad to
  B-coalgebras via structural recursion with accumulators)
- [ ] F1: Define Stone topology on `PolyCofreeShape P x` using
  finite tree approximations from `PolyFix P x`
- [ ] F2: Prove Stone space properties for finite polynomials
  (compact, totally disconnected, Hausdorff)
- [ ] F3: Construct sheaf topos `Sh(c_P(1))` and relate to
  copresheaf topos

## Notes

- Phase 1 items G0-G3 use `Functor.ofSequence` and the
  directed/filtered equivalence from mathlib; G1 and G2
  connect our inductive/coinductive definitions to
  categorical (co)limits
- G1 requires `PolyEndoFinitary P` (König's lemma argument);
  G2 should hold unconditionally but needs fiber equivalences
  between `PolyCofixApprox` and iterated functor evaluation
- Phase 1 items A0-A2 depend on mathlib's reflexive
  coequalizer infrastructure
  (`Monad.Coequalizer`, `Limits.Shapes.Reflexive`)
- Phase 2 is entirely new category theory (no mathlib precedent
  for distributive laws of monads over comonads)
- Phase 3 connects the abstract framework to our concrete
  polynomial endofunctors
- D1 (Dirichlet product) is now available; D2/D3 can build
  on it.  The Deferred items from F (two topoi) require
  topology on tree spaces not yet in our codebase
