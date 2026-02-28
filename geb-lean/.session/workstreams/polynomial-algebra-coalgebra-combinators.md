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
|----|----------|------|-----|
| A1 | `HasColimitsOfSize (PolyAlg P)` | 3 | 5 |
| A2 | Beck coequalizer for PolyAlg | 1 | 3 |
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

### Phase 1: Algebra Colimits

Build on the limit instances just added to complete the
(co)limit picture for polynomial algebras.

- [ ] A2: Instantiate Beck coequalizer (`beckAlgebraCoequalizer`)
  for `polyFreeMonad X P` to show every P-algebra is a reflexive
  coequalizer of free P-algebras
- [ ] A1: Prove `HasColimitsOfSize.{u, u} (PolyAlg P)` by showing
  `polyEndoFunctor` preserves filtered colimits (finitary), then
  applying Linton's theorem via the monad equivalence

### Phase 2: Distributive Law Framework

Define the abstract categorical structures for distributive
laws and bialgebras (not specific to polynomial functors).

- [ ] C1: Define `DistributiveLaw (T : Monad C) (D : Comonad C)`
  with four coherence axioms (unit, multiplication, counit,
  comultiplication)
- [ ] C2: Define the category of lambda-bialgebras for a given
  distributive law, with the pentagonal compatibility law.
  Construct initial object (operational model) and final object
  (denotational model) via the free/cofree adjunctions

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
- [ ] D1: Define Dirichlet/parallel product `P ⊗ Q` of polynomial
  endofunctors
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

- Phase 1 depends on mathlib's reflexive coequalizer
  infrastructure (`Monad.Coequalizer`, `Limits.Shapes.Reflexive`)
- Phase 2 is entirely new category theory (no mathlib precedent
  for distributive laws of monads over comonads)
- Phase 3 connects the abstract framework to our concrete
  polynomial endofunctors
- The Deferred items from D (Libkind-Spivak) and F (two topoi)
  require infrastructure not yet in our codebase (Dirichlet
  product, topology on tree spaces)
