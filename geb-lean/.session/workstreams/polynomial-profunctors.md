# Polynomial Profunctors Workstream

## Status: Active

## Goal

Define polynomial profunctors and their algebras, establishing conditions
under which the category of diagonal elements has initial and terminal
objects. This generalizes the theory of polynomial functors to handle
dual-variance datatypes like PHOAS (Parametric Higher-Order Abstract Syntax).

## Completed Work

### ProfAlg.lean Module

Created `GebLean/ProfAlg.lean` with the following definitions:

#### Core Structure

- `PolyProf`: A polynomial profunctor on `Type` with:
  - `B`: Type of positions (constructors)
  - `arity_neg`: Negative (contravariant) arity at each position
  - `arity_pos`: Positive (covariant) arity at each position

- `PolyProf.eval V W`: Evaluation formula
  `P(V,W) = Σ_{b : B} ((arity_neg b → V) → (arity_pos b → W))`

#### Functorial Structure

- `covAction`: Covariant action via postcomposition
- `contravAction`: Contravariant action via precomposition
- `bimap`: Combined bifunctorial action (universe-polymorphic)
- `toFunctor`: Convert to actual functor `(Type u)ᵒᵖ × Type u ⥤ Type u`
  (universe-polymorphic)
- `toCurriedFunctor`: Curried bifunctor using mathlib's `Functor.curry`,
  compatible with `DiagElem` from `Paranatural.lean`
- Proved identity and composition laws
- Proved interchange law: `covAction` and `contravAction` commute

#### Diagonal Elements

Uses `DiagElem`, `DiagElem.Hom`, and `diagElemCategory` from `Paranatural.lean`
applied to `P.toCurriedFunctor`:

- `DiagElem`: Abbreviation to `GebLean.DiagElem P.toCurriedFunctor`
- `DiagElemHom`: Abbreviation to `GebLean.DiagElem.Hom P.toCurriedFunctor`
- `diagElemCategory`: Category instance from `Paranatural.lean`
- `DiagCompat`: Compatibility condition `covAction f d₀ = contravAction f d₁`
- `diagCompat_eq_paranatural`: Equivalence with `GebLean.DiagCompat`

#### Special Cases

- `hom`: The hom-profunctor (identity polynomial profunctor)
- `homEvalEquiv`: `hom.eval V W ≃ (V → W)`
- `coprod`: Coproduct of polynomial profunctors
- `coprodEvalEquiv`: Evaluation preserves coproducts

#### Initial/Terminal Theory

- `diagElemIsInitial`: Abbreviation for `Nonempty (IsInitial x)` using mathlib
- `diagElemIsTerminal`: Abbreviation for `Nonempty (IsTerminal x)` using mathlib
- `emptyDiagElem`: Diagonal element with empty carrier at a given position
- `emptyDiagElemHom`: Morphism from empty carrier (requires matching position)
- `emptyDiagElemHom_unique`: Uniqueness proof for matching-position morphisms

#### Purely Covariant Case

- `IsPurelyCovariant`: All negative arities are empty
- `purelyCovariantEvalEquiv`: Simplification when purely covariant
- `toPFunctor`: Convert to mathlib's `PFunctor` when purely covariant

#### PHOAS Example

- `PHOASConstructor`: Constructor type (var, app, lam)
- `phoas`: The PHOAS polynomial profunctor at universe 0
- `PHOASExpr`: Recursive PHOAS expression type
- `phoasAlgMap`: Algebra structure map

## Architecture Notes

The polynomial profunctor `P(V,W) = Σ_b ((arity_neg b → V) → (arity_pos b → W))`
captures datatypes where each constructor has both contravariant inputs
and covariant outputs. For example:

- PHOAS lambda terms: `P(V,W) = W + W×W + (V → W)`
  - `var`: No neg arities, one pos arity (just W)
  - `app`: No neg arities, two pos arities (W × W)
  - `lam`: One neg arity, one pos arity (V → W)

The diagonal elements generalize F-algebras/coalgebras:

- For `AlgProf F`, diagonal elements are exactly F-algebras
- For `CoalgProf F`, diagonal elements are exactly F-coalgebras
- For general polynomial profunctors, they capture "bi-algebras"

## Connection to Existing Code

- `GebLean/Paranatural.lean`: Provides `DiagElem`, `DiagCompat`, `Paranat` -
  now used directly via `P.toCurriedFunctor`
- `GebLean/ParanatAlg.lean`: Shows `DiagElem (AlgProf F) ≌ Algebra F`
- `GebLean/Polynomial.lean`: Defines `WTypeDiagram`, `PolyFunctorBetweenCat`
- `GebLean/PolyAlg.lean`: Defines `PolyFix`, `PolyCofix`
- `Mathlib.CategoryTheory.Functor.Currying`: Provides `Functor.curry` for
  converting uncurried to curried functors
- `Mathlib.Data.PFunctor.Univariate.Basic`: Provides `PFunctor` for the purely
  covariant case

## Future Work

1. Prove that PHOAS diagonal elements form the initial/terminal structure
2. Connect to `PolyFix`/`PolyCofix` for concrete W-type/M-type constructions
3. Establish closure properties (composition, exponentials)
4. Prove cartesian closure of polynomial profunctor category
