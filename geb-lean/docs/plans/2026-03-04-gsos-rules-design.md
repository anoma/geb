# Abstract GSOS Rules and Operational Monad (E1/E2)

## Overview

Define abstract GSOS rules as natural transformations and construct
the induced distributive law and operational monad for polynomial
endofunctors.

## E1: Abstract GSOS Rules (General)

**File**: `GebLean/Utilities/GSOSRule.lean`

### Abstract GSOS Definitions

**`idBehaviorFunctor`**: Given an endofunctor `B : C ⥤ C` on a
category with binary products, the functor `X ↦ X × B(X)`.
Constructed using `Limits.prod.functor` from mathlib.

**`GSOSRule`**: A structure parameterized by:

- `Sigma : C ⥤ C` (signature endofunctor)
- `B : C ⥤ C` (behavior endofunctor)
- `T : Monad C` (syntax monad, intended to be the free monad
  on Sigma)
- `[HasBinaryProducts C]`

with a single field:

- `rule : idBehaviorFunctor B ⋙ Sigma ⟶ T.toFunctor ⋙ B`

This is the natural transformation
`Sigma(X × B(X)) → B(T(X))`.  No additional coherence axioms
beyond naturality (which is automatic from the `⟶` type).

## E2: Polynomial GSOS Distributive Law and Operational Monad

**File**: `GebLean/PolyGSOS.lean`

### Dependencies

- `polyFreeForgetAdjunction P` from `PolyAlg.lean`
  (free monad adjunction)
- `polyFixFold` from `PolyAlg.lean` (catamorphism)
- `polyCofreeComonad` from `PolyAlg.lean` (cofree comonad)
- `DistributiveLaw` from `Utilities/DistributiveLaw.lean`
- `liftedMonad` from `Utilities/LambdaBialgebra.lean`
- `overPullback` from `Utilities/Slice.lean` (binary products
  in `Over X`)

### Polynomial GSOS Definitions

**`polyGSOSRule P Q`**: A `GSOSRule` specialized to polynomial
endofunctors `P` (signature) and `Q` (behavior) on `Over X`.
Uses `overPullback` for the binary product rather than assuming
`HasBinaryProducts`.

**`polyGSOSDistLaw rho`**: Given a `polyGSOSRule P Q`, constructs
a `DistributiveLaw (polyFreeMonad X P) (polyCofreeComonad X Q)`.

Construction outline:

1. Define `lambda_X : T(B(X)) → B(T(X))` by parameterized
   recursion on `T(B(X))` (a `PolyFreeM` tree with `B(X)`-leaves
   and `P`-branching):
   - Leaf case: `B(eta_X)` maps `B(X)` to `B(T(X))`
   - Node case: given children `(t_i, y_i)` where
     `t_i : T(B(X))` (original subterm) and
     `y_i = lambda(t_i) : B(T(X))` (recursive result):
     - Map `t_i` to `T(X)` via `T(epsilon_X)` where
       `epsilon : B → Id` is the comonad counit
     - Form pairs `(T(epsilon)(t_i), y_i) : T(X) × B(T(X))`
     - Apply `rho` at `T(X)` to get `B(T(T(X)))`
     - Compose with `B(mu_X)` to get `B(T(X))`
2. Parameterized recursion is derived from `polyFixFold` by
   folding into the product `T(B(X)) × B(T(X))`:
   - First component reconstructs the term (identity fold)
   - Second component computes `lambda`
   - By initiality, the first component equals the identity
3. Extend to the full cofree comonad by anamorphism (unfold
   into `PolyCofix`)
4. Prove the four coherence axioms of `DistributiveLaw`:
   unit, multiplication, counit, comultiplication

**`polyGSOSOperationalMonad rho`**: The operational monad, defined
as `liftedMonad (polyGSOSDistLaw rho)`.  This is a monad on the
category of `polyCofreeComonad`-coalgebras.

**Canonical GSOS rule**: When `P = Q`, define the canonical GSOS
rule and show the induced distributive law agrees with the
existing `polyDistributiveLaw P`.

## References

- Turi and Plotkin, "Towards a mathematical operational
  semantics" (LICS 1997), Sections 1, 3-5
- Bartels, "On generalised coinduction and probabilistic
  specification formats" (PhD thesis, 2004), Chapter 4
