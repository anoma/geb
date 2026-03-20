# Workstream: TermCat — Binary Tree Categories

## Status

Active

## Context

Define categories constructed from binary trees (the free
monad of `polyProd X`) in `GebLean/PLang/TermCat.lean`.

Design document:
`docs/plans/2026-03-06-termcat-design.md`

**Bootstrapping strategy (decided 2026-03-07)**: Start
with tree calculus (Turing-complete, self-reflective),
carve out a terminating primitive-recursive subset, prove
termination in Lean, and write a self-recognizer within
that subset. The self-recognizer serves as a gatekeeper
for type-checkers of further language layers. This
reverses the original plan of building a weak language
first and extending upward. See design doc section
"Bootstrapping Strategy: Tree Calculus First".

The design explores six candidate categories (algebra,
Kleisli, Lawvere, coalgebra, lambda-bialgebra, co-Kleisli)
and three layered approaches (PBTO/Lawvere, tree calculus,
hybrid). The Kleisli category of
`polyFreeMPoly (polyProd X)` provides the categorical
framework; tree calculus provides the computational
starting point.

The theory should be self-reflective both computationally
(tree calculus: programs computing on programs) and
logically (the theory can reason about its own morphisms,
propositions, and proofs). Three candidate "internal
universes" are under consideration: the coalgebra topos,
the realizability topos of the tree calculus PCA, and the
free topos with binary tree object. See design doc
section "Internal Logic and Self-Reflection".

At least two possibilities exist for recognizing terminating
programs: (1) syntactic criterion — decidable membership in
a syntactic fragment (starting point); (2) proof-carrying
code — programs accompanied by termination proofs as
trees (later extension, built within the language on
top of Option 1). See design doc section "Design
Principles".

## Files

- `GebLean/PLang/TermCat.lean` — primary implementation
  (skeleton created, imports `Syntax.lean`)
- `GebLean/PLang.lean` — index (already imports
  `TermCat`)
- `docs/plans/2026-03-06-termcat-design.md` — design doc
- `docs/tree-calculus.md` — tree calculus reference
  (syntax, reduction rules, PCA structure,
  self-reflection, type system (detailed), external
  references)
- `docs/polynomial-algebra-coalgebra-categories.md` —
  reference document on universal properties of P-Alg
  and P-Coalg, base category requirements, and
  candidate base categories (Sections 10-11)

## Dependencies

All of these are in the existing codebase:

- `polyProd X` (`PLang/Syntax.lean:42`)
- `polyFreeMPoly` (`PolyAlg.lean:3642`)
- `polyFreeMPure` (`PolyAlg.lean:3423`)
- `polyFreeMBind` (`PolyAlg.lean:3453`)
- `polyFreeMPolyUnit` (`PolyAlg.lean:8588`)
- `polyFreeMPolyMult` (`PolyAlg.lean:8625`)
- Monad laws: `polyFreeM_pure_bind` (3466),
  `polyFreeM_bind_pure` (3474),
  `polyFreeM_bind_assoc` (3494)
- `polyFixFold` (`PolyAlg.lean:308`)
- `polyFixFoldUnique_at` (`PolyAlg.lean:382`)
- `polyTranslate` (`PolyAlg.lean:2766`)
- `polyBetweenId X` (`Polynomial.lean:1431`)
- `polyCoalgCopresheafEquiv` (`CofreeCategory.lean:3327`)
- `DistributiveLaw` (`Utilities/DistributiveLaw.lean`)
- `LambdaBialgebra` (`Utilities/LambdaBialgebra.lean:26`)

## Tasks

### Phase 0.5: Lawvere Theory of Binary Trees

Implementation plan:
`docs/superpowers/plans/2026-03-19-lawvere-bt-universal-properties.md`

Primary file: `GebLean/LawvereBT.lean`
Supporting: `GebLean/PLang/Syntax.lean`,
`GebLean/PolyUMorph.lean`,
`GebLean/Utilities/Slice.lean`

Completed (2026-03-19):

- [x] HasNNO and HasPBTO classes (simple universal
  property, transcribed from nLab)
- [x] BT type via PolyFreeM with convenience wrappers
  (polyProdFreeMNode, polyProdFreeMFoldAt)
- [x] BTMor1 = PolyFix btMorPoly (polynomial type)
  with four-component coproduct (proj, leaf, branch,
  fold)
- [x] Constructors via polyFixStrFamily + polyBetweenInj
- [x] interp via polyFixFoldAtWithProof + algCoprodDesc
- [x] rename, subst via polyFixFoldAtWithProof
- [x] btFold (simple, X = 1)
- [x] Infrastructure: Over.Fiber, polyBetweenRepr,
  polyProdAlgStr, polyProdEvalOfPair/ToPair

In progress:

- [x] btFoldFull (full simple universal property,
  arbitrary X = m) — defined as a semantic function
  `(Fin (n+1) → BT) → (Fin m → BT)` using BT.fold
  with carrier `Fin m → BT`.  The BTMor1.fold
  constructor's step child has only 2 recursive-result
  variables, which is insufficient for coupled mutual
  recursion with m > 1 components.  The semantic
  definition avoids this limitation.  btFold (m = 1)
  remains syntactic.
- [x] btFoldEnhanced (enhanced version, g with context
  access, derived from btFoldFull)
- [ ] Category instance for LawvereBTCat
  - Proof schemes (induction principles) for BTMor1
  - subst identity and composition laws
  - Category laws from subst laws
- [ ] HasFiniteProducts instance
- [ ] HasPBTO instance
  - Computation rules
  - Uniqueness via polyFixFoldUnique

Future:

- [ ] PolyEndoFinitary btMorPoly instance
- [ ] polyBetweenRepr used to refactor btMorFoldPoly
  and polyShift

### Phase 1: Kleisli Category and Isomorphism

- [ ] Define `treeFoldAlg` — convenience wrapper: leaf
  map + fork map into `polyTranslate A (polyProd X)`
  algebra
- [ ] Define `treeFold` — parametrized fold specialized
  to `polyProd`
- [ ] Prove `treeFold_unique` — from `polyFixFoldUnique`
- [ ] Prove binary-to-finite-branching isomorphism:
  `polyFreeMCarrier A (polyProd X) ~=`
  `A *_X polyFreeMCarrier T (polyBetweenId X)`.
  Uses fold (forward) and algebra structure (backward).
  Relates free monad of product to free monad of identity
  (list). Provides leaf/stem/fork case analysis by child
  count (0, 1, 2).
- [ ] Define `treeKleisliHom` — morphism type
  `A -> polyFreeMCarrier B (polyProd X)`
- [ ] Define `treeKleisliComp` — composition via
  bind/graft
- [ ] Define `treeKleisliId` — identity via pure/unit
- [ ] Prove category laws (`id_comp`, `comp_id`,
  `comp_assoc`) from monad laws
- [ ] Define `treeKleisliCategory` — the Category instance

### Phase 0: Base Category Selection

Analysis in `docs/polynomial-algebra-coalgebra-categories.md`
Sections 10-11. Findings:

- P-Coalg(E) is a topos when E has: finite limits,
  finite colimits, NNO (or countable limits for the
  approximation chain), and P preserves connected limits.
- E does NOT need exponentials or a subobject classifier;
  those are outputs of the topos construction.
- For finitary P(X) = A + X^2, the M-type construction
  requires only finite products (X^2 = X * X), not
  exponentials.
- The codebase M-type construction (`PolyCofixApprox`,
  `PolyCofixAgree` in `PolyAlg.lean`) uses countable
  limits (inverse limit of truncated approximations).

Three candidate base categories:

1. PER(tree calc.) — regular, locally cartesian closed,
   has NNO, but not exact (not a topos). Its ex/reg
   completion is the realizability topos RT(tree calc.).
2. Parametric relations (`PshRelCat`, `TypeExprCat`,
   `ParametricFamily` in codebase) — presheaf-like,
   has limits/colimits, represents functions as
   functional relations.
3. Hybrid: PER(tree calc.) as computational base,
   parametric relations derived as reflexive graph
   structure. Recommended approach.

- [ ] Decide on base category (PER, parametric, or
  hybrid)
- [ ] Verify chosen base category has the required
  universal properties (finite limits, finite colimits,
  NNO, countable limits)
- [ ] Construct P-Coalg over chosen base and confirm
  topos structure

### Phase 1.5: Internal Representation

- [ ] Define `Omega` concretely as a coalgebra of
  `polyProd X` — the subobject classifier of the
  coalgebra topos
- [ ] Compute sieves on `PolyCofreeCat (polyProd X)`
  concretely (downward-closed sets of tree paths)
- [ ] Define exponential `[A, B]` concretely for specific
  coalgebras A, B
- [ ] Represent the Kleisli category (or its morphism
  set) as a coalgebra/copresheaf within the topos

### Phase 2: Tree Calculus Reduction and Bootstrapping

- [ ] Choose the behavior polynomial `Q` for triage
  calculus (see design doc section "GSOS Infrastructure
  and Triage Reduction")
- [ ] Use finite-branching isomorphism to define
  leaf/stem/fork case analysis (child count 0, 1, 2)
- [ ] Define the 5 triage reduction rules as a GSOS rule
  `rho : PolyGSOSRule (polyProd X) Q`
- [ ] Verify that the GSOS fold on ground terms
  reproduces the triage reduction rules
- [ ] Show confluence (non-overlapping rules)
- [ ] Define PCA structure (K and S from rules 1-2)
- [ ] Define the primitive-recursive syntactic fragment:
  terms computing only via `polyFixFold` into algebras,
  excluding general fixed-point combinators
- [ ] Prove in Lean that all terms in the syntactic
  fragment terminate
- [ ] Implement the self-recognizer: a tree-calculus
  program, itself in the primitive-recursive fragment,
  that decides membership in the fragment
- [ ] Prove in Lean that the self-recognizer is correct
  (sound and complete) and terminates

### Phase 3: Lambda-Bialgebra and Topos

- [ ] Obtain distributive law from
  `polyGSOSDistributiveLaw (polyProd X) Q rho`
  (all coherence axioms proved by GSOS machinery)
- [ ] Obtain operational monad from
  `polyGSOSOperationalMonad (polyProd X) Q rho`
- [ ] Study the Eilenberg-Moore category of the
  operational monad (= lambda-bialgebras)
- [ ] Connect to coalgebra topos via
  `polyCoalgCopresheafEquiv`
- [ ] Investigate realizability topos and its
  relationship to the coalgebra topos

### Phase 4: Language Tower and Proof-Carrying Code

- [ ] Use the primitive-recursive self-recognizer as a
  gatekeeper for type-checker eligibility
- [ ] Define richer type systems (System T, System F
  analogues) as tree-calculus programs, type-checked by
  the primitive-recursive layer
- [ ] Investigate proof-carrying code (Option 2): extend
  the recognizer to accept programs accompanied by
  termination proofs expressed as trees
- [ ] Investigate the free topos with binary tree object
- [ ] Compare its internal logic with the free topos with
  NNO — are they logically equivalent?
- [ ] Relate the free topos to the coalgebra topos and/or
  the realizability topos
- [ ] Study how polynomials expressed internally provide
  inductive/coinductive type formation within the topos

### Open design questions

- [ ] Paramorphism vs catamorphism for PBTO universal
  property
- [ ] Triage encoding: GSOS vs direct coalgebra vs
  child-count decomposition via isomorphism
- [ ] Are the coalgebra topos and realizability topos
  equivalent for the tree calculus PCA?
- [ ] Is the free topos with binary tree object logically
  equivalent to the free topos with NNO?
- [ ] Concrete subobject classifier: what does Omega look
  like as a coalgebra of `polyProd X`?
- [ ] Can the external Kleisli category be represented
  internally as a coalgebra/copresheaf?
- [ ] Unlabeled trees: use terminal object as generator?
- [ ] Child-count truncation: can 0/1/2 child cases be
  expressed as polynomial equalizer or quotient?
- [ ] Base category choice: PER(tree calc.) vs parametric
  relations vs hybrid — see Section 11 of the reference
  document for detailed comparison
- [ ] Does PER(tree calc.) satisfy countable-limit
  requirement for M-type construction?
- [ ] Can the ex/reg completion (PER -> RT) be avoided
  by working directly in P-Coalg(PER)?
- [ ] Self-representability: can the base category
  represent its own morphisms internally?
- [ ] Primitive-recursive fragment definition: precise
  syntactic criterion, decidable by a program within
  the fragment itself
- [ ] Self-recognizer expressibility: can the recognizer
  be written within the fragment it recognizes?
- [ ] Proof-carrying code format: what constitutes a
  valid termination proof as a tree? (ordinal notations,
  well-founded recursion witnesses, sized-type
  annotations)
- [ ] Language tower granularity: what layers sit between
  primitive recursion and full tree calculus? (multiply
  recursive, System T, System F, bar recursion)

## Notes

- Work in `Over X` throughout; specialize to `Type` (via
  `X = PUnit`) only when useful
- Interact with binary trees only through universal
  morphisms (fold, unfold, bind, pure, etc.)
- Write one definition at a time per CLAUDE.md workflow
- The algebra category `PolyAlg (polyProd X)` is already
  defined; the Kleisli category is new
- The coalgebra category `PolyCoalg (polyProd X)` is
  already defined and known to be a topos
- Binary trees ~= finite-branching trees: the isomorphism
  `T ~= A *_X List(T)` relates free monad of product to
  free monad of identity. This gives leaf (0 children),
  stem (1 child), fork (2 children) classification.
  See design doc section "Binary-to-Finite-Branching
  Isomorphism".
- The theory needs two levels: external (Lean) and
  internal (within the topos). Polynomials provide
  internal type formation (inductive/coinductive types)
  but not full internal logic (polynomial category is
  not a topos). The topos structure from the coalgebra
  category provides the full internal logic.
  See design doc section "Internal Logic and
  Self-Reflection".
- The coalgebra topos construction is a "topos
  generator": it takes a non-topos base E (needing
  only finite (co)limits and NNO) and produces a
  topos P-Coalg(E) with subobject classifier and
  exponentials. See reference document Section 10.
- For finitary polynomials (like polyProd), exponentials
  are NOT needed in E; X^2 is a finite product.
- The copresheaf equivalence (`polyCoalgCopresheafEquiv`)
  provides independent confirmation of coalgebraic
  constructions via Set^C for path category C.
- Bootstrapping strategy: tree calculus first, carve out
  primitive-recursive subset, prove termination, write
  self-recognizer. Lean verifies assumptions against
  standard mathematics but does not interpret the
  language. Goal: minimal code to self-description.
- Syntactic criterion (Option 1) is the starting point
  for recognizing terminating programs. Proof-carrying
  code (Option 2) is a later extension built within
  the language itself using tree calculus's reflective
  capabilities.
- Termination witnesses built for the primitive-recursive
  subset are the realizers needed for the realizability
  topos — this work is not scaffolding but directly
  constructs assembly structure.
- The primitive-recursive subset corresponds to functions
  definable via `polyFixFold` into suitable algebras
  (the PBTO / Lawvere theory from Approach A, now
  situated within tree calculus rather than developed
  independently).
