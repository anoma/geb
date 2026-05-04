# Tree Calculus Phase 2: Reduction and Bootstrapping

## Goal

Formalize tree calculus reduction as a coalgebraic process
on a two-sorted polynomial system in Lean 4, using the
existing polynomial functor infrastructure.  Build the
partial combinatory algebra (PCA) structure, prove
confluence, define a primitive-recursive fragment, prove
its termination, and implement a self-recognizer within
that fragment.

## Architecture

### Representation: Two-Sorted Slice Polynomial

Tree calculus operates on binary trees, but conflates three
distinct roles into a single type: the ambient space of
trees, the values that computation produces, and the
computation process itself.  This design separates them
using a two-sorted polynomial on `Over (Fin 2)`:

- **Sort 0 (Value):** Fully reduced binary trees.  Every
  node has at most two children in the finite-branching
  view (leaf, stem, or fork).
- **Sort 1 (Computation):** Pending computations.
  Application nodes have a list of sub-computations;
  embed nodes wrap a value.

The sort determines the child type: value nodes have
value children; application nodes have computation
children.  This dependency is expressed through the
slice structure of `PolyEndo (Fin 2)`, where the
direction fibers at each position map to the
appropriate sort.

### Three Polynomials

**1. Value polynomial** (`polyValue : PolyEndo PUnit`)

A three-summand coproduct encoding leaf, stem, and fork:

| Position | Directions | Fiber map |
|----------|-----------|-----------|
| leaf     | `Empty`   | --        |
| stem     | `Unit`    | -> PUnit  |
| fork     | `Fin 2`   | -> PUnit  |

The initial algebra `PolyFix polyValue` is the type of
values (programs) in tree calculus.  This polynomial is
self-contained and single-sorted; it is embedded into
the two-sorted system via a combinator.

This is equivalent to
`polyTranslate (overTerminal PUnit)
  (polyTranslate (polyBetweenId PUnit)
    (polyProd PUnit))`
-- a coproduct of the terminal (leaf), identity (stem),
and product (fork) polynomials.

**2. Computation polynomial**
(`polyComputation : PolyEndo (Fin 2)`)

A two-sorted polynomial assembled from combinators:

Fiber 0 (Value sort):

| Position | Directions | Fiber map      |
|----------|-----------|----------------|
| leaf     | `Empty`   | --             |
| stem     | `Unit`    | -> 0 (Value)   |
| fork     | `Fin 2`   | both -> 0      |

Fiber 1 (Computation sort):

| Position   | Directions | Fiber map       |
|------------|-----------|-----------------|
| embed      | `Unit`    | -> 0 (Value)    |
| app(n : N) | `Fin n`   | all -> 1 (Comp) |

`PolyFix polyComputation` at fiber 0 gives the Value
type.  `PolyFix polyComputation` at fiber 1 gives
CompTree:

```text
Value    = leaf | stem(Value) | fork(Value, Value)
CompTree = embed(Value) | app(List CompTree)
```

The `embed` constructor bridges the two sorts.  The
`app(n)` positions use `Nat`-indexed position families
with `Fin n` directions, giving variable-width branching
for application nodes.

**3. Rose-tree polynomial**
(`polyRoseTree A : PolyEndo X`)

A polynomial for labeled finite-branching trees:

- Positions at fiber x:
  `{ a : A.left // A.hom a = x } * Nat`
- Directions at position (a, n): `Fin n`, all mapping
  to x

The initial algebra gives labeled finite-branching trees.
An isomorphism connects these to labeled binary trees:

```text
PolyFix (polyTranslate A (polyProd X))
  ~= PolyFix (polyRoseTree A X)
```

This isomorphism is independently useful and is also
being developed in the Phase 1 thread.

### Computation as Coalgebra

Tree calculus is Turing-complete: evaluation is a partial
function.  There is no total evaluator `CompTree -> Value`
in Lean.  Instead, computation is represented
coalgebraically.

**Behavior polynomial** (`Q : PolyEndo (Fin 2)`):

Fiber 0 (Value sort): Identity polynomial.  Values
are already fully observed; no further computation.

Fiber 1 (Computation sort): Value-shaped observation:

| Position | Directions | Fiber map       |
|----------|-----------|-----------------|
| obs-leaf | `Empty`   | --              |
| obs-stem | `Unit`    | -> 1 (Comp)     |
| obs-fork | `Fin 2`   | both -> 1       |

The observation at each step is: "what does this
computation look like right now?" -- leaf, stem, or fork
with sub-computations as children.

**One-step reduction** is a Q-coalgebra:

```text
step : CompTree -> Q(1)(CompTree)
```

Examine the root of the computation tree:

- If `embed(v)`: observe `v`'s structure (leaf/stem/fork)
  with trivially-done sub-computations.
- If `app([f, x1, ..., xn])`: perform one triage
  reduction step, produce the value-observation of the
  result.

**Full evaluation** is the anamorphism:

```text
eval : CompTree -> PolyCofix Q (1)
```

via `polyCofixUnfold`.  The result is a potentially
infinite tree with <=2 branching at each level.  Finite
elements correspond to terminating computations (and are
isomorphic to values).  Infinite elements correspond to
diverging computations.

### Triage Reduction Rules

The five triage rules operate on application nodes in the
finite-branching view.  Given `app([f, x1, ..., xn])`
where `f` is a value:

**Rule 1 (K):** `f = leaf`, n >= 2.
Result: `x1`.  (If n > 2, remaining arguments form
further applications.)

**Rule 2 (S):** `f = stem(a)`, n >= 2.
Result: `app([a, x2, app([x1, x2])])`.  (Distribute
the third argument.)

**Rules 3-5 (triage):** `f = fork(w, x_f)`, n >= 1.
Examine `x1`:

- Rule 3a: `x1` is a value-leaf.  Result: `w`.
- Rule 3b: `x1` is a value-stem `stem(u)`.
  Result: `app([x_f, u])`.
- Rule 3c: `x1` is a value-fork `fork(u, v)`.
  Result: `app([y, u, v])` where `y` is the argument
  after `x1` in the original application (i.e., `x2`
  from `app([f, x1, x2, ...])`).  In the standard
  tree calculus notation: `fork(w, x_f) y fork(u, v)`
  reduces to `y u v`.

(Remaining arguments xn for n >= 2 or 3 form further
applications.)

Partial applications (n < the arity needed for the rule
to fire) produce values:

- `app([leaf, x1])` produces `stem(x1)` (a value).
- `app([stem(a), x1])` produces `fork(a, x1)` (a value).

### GSOS Rule

The triage rules are encoded as a `PolyGSOSRule`:

```text
rho : PolyGSOSRule polyComputation Q
```

This is a polynomial morphism:

```text
polyComputation . (Id * Q) -> Q . T_polyComputation
```

Given a computation node whose children carry both their
current state and their value-observation, `rho` produces
a value-observation of free-monad terms (new computation
trees).

The GSOS machinery automatically produces:

- `polyGSOSDistributiveLaw polyComputation Q rho`:
  the distributive law between the free monad of
  `polyComputation` and the cofree comonad of `Q`,
  with all four coherence axioms proved.
- `polyGSOSOperationalMonad polyComputation Q rho`:
  a monad on Q-coalgebras.
- Lambda-bialgebras as Eilenberg-Moore algebras of the
  operational monad (Phase 3 deliverable).

### Combinator Library

A new file `GebLean/Utilities/PolyCombinators.lean`
provides generic combinators for constructing slice
polynomials.  The initial set, discovered during the
tree calculus implementation:

- **Fiber embedding**: lift `PolyEndo (Fin m)` to
  `PolyEndo (Fin n)` via an injection `Fin m -> Fin n`.
  At fibers in the image, use the source polynomial;
  at fibers outside the image, use the empty polynomial.

- **Cross-sort constructor**: add a constructor at fiber
  j whose directions point to fiber i (i != j).  The
  `embed` constructor (Value -> Computation bridge) is
  an instance.

- **Fiber-indexed coproduct**: combine polynomials
  covering different fibers into one polynomial on the
  union.  Pointwise coproduct of position types.

- **Rose-tree polynomial**: `polyRoseTree A X` with
  `(label, Nat)` positions and `Fin n` directions.

- **Nat-indexed family**: a polynomial with `Nat`-indexed
  positions and `Fin n` directions, parameterized by
  the direction-to-fiber map.

Additional combinators are added as the implementation
reveals the need.

### Extensibility

The polynomial representation is automatically a "data
types a la carte" system.  Adding a new constructor or
label (e.g., a third computation sort for suspended
computations, or a new evaluation strategy) is a
coproduct extension of the existing polynomial.  Existing
code working with the current constructors is unaffected.

## Deliverables

### Prerequisite infrastructure

1. `GebLean/Utilities/PolyCombinators.lean` -- generic
   combinator library for slice polynomials
2. `polyValue : PolyEndo PUnit` -- value polynomial
   (leaf/stem/fork)
3. `polyRoseTree A : PolyEndo X` -- rose-tree polynomial
4. Rose-tree isomorphism:
   `PolyFix (polyTranslate A (polyProd X))
     ~= PolyFix (polyRoseTree A X)`

### Tree calculus types and reduction

1. `polyComputation : PolyEndo (Fin 2)` -- two-sorted
   computation polynomial, assembled from combinators
1. Value type = `PolyFix polyComputation` at fiber 0,
   with equivalence to `PolyFix polyValue`
1. CompTree type = `PolyFix polyComputation` at fiber 1
1. Behavior polynomial `Q : PolyEndo (Fin 2)` -- value-
   shaped observation
1. One-step reduction coalgebra:
   `step : CompTree -> Q(1)(CompTree)`.
   Package as a `PolyCoalg Q` for use with
   `polyCofixUnfold`.
1. GSOS rule `rho : PolyGSOSRule polyComputation Q`
   (contingent on Open Question 1; fallback is direct
   coalgebra without GSOS)
1. Verification: the GSOS fold on ground terms
   reproduces the five triage rules

### Tree calculus programs

1. Derived combinators as Value terms: K, I, D, S,
   triage, true, false, successor, predecessor, isZero,
   isLeaf, isStem, isFork
1. Bracket abstraction and star abstraction
1. Fixpoint combinators: self_apply, Z, swap, Y_2

### Metatheory

1. PCA structure: K and S combinators, partial
   application via the reduction coalgebra, verification
   of the PCA axioms
1. Confluence: parallel reduction relation, diamond
   property, confluence theorem
1. Distributive law from GSOS:
   `polyGSOSDistributiveLaw polyComputation Q rho`
1. Operational monad:
   `polyGSOSOperationalMonad polyComputation Q rho`

### Bootstrapping

1. Primitive-recursive fragment: syntactic criterion on
   Value terms (absence of fixpoint combinator patterns,
   restricted to fold-definable functions)
1. Termination proof: terms in the fragment produce
   finite elements of `PolyCofix Q`
1. Self-recognizer: a Value term, itself in the
   primitive-recursive fragment, that decides membership
1. Self-recognizer correctness: sound and complete with
   respect to the syntactic criterion, and terminates

## File Structure

```text
GebLean/
  Utilities/
    PolyCombinators.lean   -- generic combinator library
  PLang/
    TreeCalcPoly.lean      -- polyValue, polyComputation,
                              polyRoseTree, Q
    TreeCalcReduction.lean -- step coalgebra, GSOS rule,
                              triage verification
    TreeCalcPrograms.lean  -- combinators, abstraction,
                              fixpoints
    TreeCalcMeta.lean      -- PCA, confluence, fragment,
                              termination, recognizer
```

Alternatively, if files grow large, TreeCalcMeta can be
split into TreeCalcPCA, TreeCalcConfluence, and
TreeCalcBootstrap.

## Dependencies

### From existing codebase

- `PolyGSOSRule`, `polyGSOSDistributiveLaw`,
  `polyGSOSOperationalMonad` (`PolyGSOS.lean`)
- `PolyFix`, `polyFixFold`, `polyFixFoldUnique_at`
  (`PolyAlg.lean`)
- `PolyCofix`, `polyCofixUnfold` (`PolyAlg.lean`)
- `polyTranslate`, `polyProd`, `polyBetweenId`,
  `polyBetweenCoprod` (`PolyAlg.lean`, `Polynomial.lean`)
- `LambdaBialgebra`, `DistributiveLaw`
  (`Utilities/LambdaBialgebra.lean`,
   `Utilities/DistributiveLaw.lean`)
- `overTerminal` (`PolyAlg.lean`),
  `Over.Fiber` (`Utilities/Slice.lean`)

### From Phase 0.5/1 (parallel thread)

- The rose-tree isomorphism is also a Phase 1 task.
  If Phase 1 completes it first, Phase 2 imports it.
  If Phase 2 needs it first, it builds it in
  PolyCombinators or TreeCalcPoly and Phase 1 reuses.
- `BT`, `BT.leaf`, `BT.node`, `BT.fold`
  (`LawvereBT.lean`) -- not strictly required, but the
  relationship `BT ~= PolyFix polyValue` should be
  established.

### External references

- Andrej Bauer's PCA formalization in Lean 4:
  `github.com/andrejbauer/partial-combinatory-algebras`
  -- reference for PCA structure definitions and axioms
- Metatheory library (arthuraa/metatheory): SK
  combinatory logic confluence proof (~285 lines) --
  structural template for parallel reduction and diamond
  property
- Barry Jay's Coq formalization:
  `github.com/barry-jay-personal/tree-calculus` --
  reference for derived combinators and theorem statements

## Open Questions

1. **GSOS two-level observation**: the triage rules
   require examining two levels of value structure (the
   applied function AND its argument).  The GSOS rule
   format provides `Id * Q` -- one level of identity and
   one level of observation.  Whether this suffices for
   all five triage rules, or whether a richer observation
   is needed, will be determined during implementation.

2. **Nat-indexed positions and finiteness**: the `app(n)`
   positions are indexed by `Nat`, giving infinitely many
   positions.  This is valid in the polynomial framework
   but may interact with decidability or computability
   requirements.  To be investigated.

3. **Rose-tree isomorphism coordination**: this is needed
   by both Phase 1 and Phase 2.  The first thread to
   complete it provides the definition; the other imports.

4. **Primitive-recursive fragment criterion**: the precise
   syntactic criterion must be defined during
   implementation.  The design principle is: terms
   definable via `polyFixFold` into suitable algebras,
   excluding general fixpoint combinators.  The boundary
   may need adjustment based on what the self-recognizer
   can express.

5. **Self-recognizer expressibility**: whether a correct
   and complete recognizer for the primitive-recursive
   fragment can be written within the fragment itself is
   a mathematical question that will be resolved during
   implementation.  If the fragment is too narrow, it
   must be widened.
