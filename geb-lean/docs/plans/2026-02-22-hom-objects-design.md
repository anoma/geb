# Hom-Objects (Exponentials) for PolyFunctorBetweenCat

## Goal

Define internal hom-objects `[Q, R]` for
`PolyFunctorBetweenCat.{u, u} X Y` and prove `CartesianClosed`,
establishing that the category of polynomial functors between
slice categories is cartesian closed.

## Three-Layer Construction

Following the Idris source (`.claude/docs/SlicePolyUMorph.idr`),
the construction has three layers, each built from the previous.

### Layer 0: Primitive Components

**Constant endofunctor** (`polyBetweenConst`):
Given `a : Over X`, define `polyBetweenConst a :
PolyFunctorBetweenCat X X` as the constant endofunctor at `a`.
Constructed by factoring through the terminal CCR object: at each
`x : X`, the positions are `{ b : a.left // a.hom b = x }`
(the fiber of `a` over `x`), each mapping to the terminal CCR
object, yielding `Hom(terminal, A) = PUnit` so the evaluation
is constant at `a` regardless of input.

**FlipEither** (`polyBetweenFlipEither`):
Given `a : Over X`, define `polyBetweenFlipEither a =
polyBetweenId X + polyBetweenConst a` (coproduct in
`PolyFunctorBetweenCat X X`). This represents the endofunctor
`A |-> A + a` on `Over X`. Built using the existing coproduct
infrastructure (`HasFiniteCoproducts` instance).

### Layer 1: Representable Hom

**`ccrRepHom`**: Given `a : Over X` and `r :
CoprodCovarRepCat (Over X)`, define `ccrRepHom a r =
ccrComp r (polyBetweenFlipEither a)`. This reuses
`polyBetweenComp` (or rather its CCR-level component).

The adjunction `ccrRepHom a - dashv forget` (i.e., rep-level
currying) comes from `polyBetweenLKanAdj` applied to
`q = polyBetweenFlipEither a`, after establishing the
isomorphism `Lan_{flipEither(a)}(p) = p * yoneda(a)`.

### Layer 2: Copresheaf Hom

**`ccrCoprHom`**: Given `q, r : CoprodCovarRepCat (Over X)`,
define `ccrCoprHom q r = Pi_{i : ccrIndex q} ccrRepHom
(ccrFamily q i) r`. This is a set-indexed product using the
existing `ccrProdData` infrastructure.

The adjunction `ccrCoprHom q - dashv (- * q)` at the copresheaf
level follows from the chain:
`Hom(p * q, r) = Hom(coprod_i (p * yoneda(q_i)), r)`
(by product-as-coproduct-of-representables)
`= Prod_i Hom(p * yoneda(q_i), r)` (coproduct-hom adjunction)
`= Prod_i Hom(p, repHom(q_i, r))` (rep-level currying)
`= Hom(p, Prod_i repHom(q_i, r))` (product-hom adjunction)
`= Hom(p, coprHom(q, r))`.

### Layer 3: General Hom

**`polyBetweenHomObj`**: Given `Q, R :
PolyFunctorBetweenCat X Y`, define `[Q, R](y) =
ccrCoprHom (Q y) (R y)` pointwise.

The adjunction `polyBetweenHomObj Q - dashv (- * Q)` follows
from the pointwise adjunction at each `y : Y`.

## Adjunction Proof Strategy

The currying adjunction decomposes into a chain of adjunctions,
each with known universal properties:

1. **Product decomposition**: `P * Q` at each `y` decomposes as
   `coprod_{i : ccrIndex (Q y)} (P y * yoneda(ccrFamily (Q y) i))`
2. **Coproduct-hom**: `Hom(coprod_i F_i, R) = Prod_i Hom(F_i, R)`
3. **Rep currying** (via `polyBetweenLKanAdj`):
   `Hom(P * yoneda(a), R) = Hom(P, repHom(a, R))`
4. **Product-hom**: `Prod_i Hom(P, G_i) = Hom(P, Prod_i G_i)`

The overall adjunction is the composition of these four natural
isomorphisms.

For step 3, we need the isomorphism
`Lan_{flipEither(a)}(p) = p * yoneda(a)`. This states that
the left Kan extension along `A |-> A + a` of `p` is the
product of `p` with the representable at `a`. The proof
constructs explicit maps in both directions and verifies they
are inverse.

## Existing Infrastructure

| Component | Location |
|-----------|----------|
| `polyBetweenId` | `Polynomial.lean:1289` |
| `polyBetweenComp` | `Polynomial.lean:1394` |
| `polyBetweenLKanAdj` | `PolyUMorph.lean:2290` |
| `HasFiniteProducts` | `PolyUMorph.lean:1485` |
| `HasFiniteCoproducts` | `PolyUMorph.lean:1489` |
| `ccrProdData` | `Families.lean:1006` |
| `ccrCoprodData` | `Families.lean:1433` |

## Deliverables

1. `polyBetweenConst : Over X -> PolyFunctorBetweenCat X X`
2. `polyBetweenFlipEither : Over X -> PolyFunctorBetweenCat X X`
3. `ccrRepHom : Over X -> CCR (Over X) -> CCR (Over X)`
4. `ccrCoprHom : CCR (Over X) -> CCR (Over X) -> CCR (Over X)`
5. `polyBetweenHomObj : PFB X Y -> PFB X Y -> PFB X Y`
6. `Lan_{flipEither(a)}(p) = p * yoneda(a)` isomorphism
7. Rep-level currying adjunction (from 6 + `polyBetweenLKanAdj`)
8. Copresheaf-level currying adjunction (from 7 + limits)
9. General currying adjunction (pointwise from 8)
10. `CartesianClosed` instance for `PolyFunctorBetweenCat X Y`
