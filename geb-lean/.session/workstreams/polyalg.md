# Polynomial Endofunctor Algebras and Coalgebras

Status: Completed

## Objective

Formalize algebras and coalgebras of polynomial endofunctors on slice
categories `Over X`, including the construction of initial algebras (W-types)
and terminal coalgebras (M-types).

## Completed Work

### Module: GebLean/PolyAlg.lean

Built on the polynomial functor infrastructure in `Polynomial.lean` to define:

1. **PolyEndo X** - Polynomial endofunctors on `Over X` (via Grothendieck)
2. **WTypeEndo X** - Polynomial endofunctors on `Over X` (via W-type diagrams)
3. **polyEndoEquiv** - Equivalence between the two representations
4. **polyEndoFunctor** / **wTypeEndoFunctor** - Convert representations to
   actual functors

### Algebras

Using mathlib's `Endofunctor.Algebra` for structure:

- **PolyAlg P** - Algebras of polynomial endofunctor P
- **WTypeAlg W** - Algebras of W-type endofunctor W
- Category instances inherited from mathlib
- Forgetful functors to `Over X`

### Initial Algebra (W-types)

The main result establishes `PolyFix P` as the initial algebra:

1. **PolyFix P** - Inductive type representing W-type trees indexed by X
2. **polyFixCarrier** - The carrier as an object of `Over X`
3. **polyFixStr** - The structure map `P(PolyFix) -> PolyFix`
4. **polyFixAlg** - The algebra structure combining carrier and structure map
5. **polyFixFold** - Catamorphism from PolyFix to any algebra
6. **polyFixFoldHom** - The fold as an algebra homomorphism
7. **polyFixFoldHom_unique** - Uniqueness of the catamorphism
8. **polyFixAlg_isInitial** - The IsInitial instance via
   `IsInitial.ofUniqueHom`

### Coalgebras

Using mathlib's `Endofunctor.Coalgebra` for structure:

- **PolyCoalg P** - Coalgebras of polynomial endofunctor P
- Category instance inherited from mathlib
- Forgetful functor to `Over X`

### Terminal Coalgebra (M-types)

The construction of M-types as consistent sequences of approximations:

1. **PolyCofix_Approx P n x** - Finite approximations of M-type trees at depth n
2. **PolyCofix_Agree P** - Agreement relation between successive approximations
3. **PolyCofix P x** - M-type as consistent chain of approximations
4. **PolyCofix.ext** - Extensionality: M-types are equal iff all approximations
   agree
5. **polyCofixCarrier** - The carrier as an object of `Over X`
6. **polyCofixStr** - The structure map `PolyCofix -> P(PolyCofix)`
7. **polyCofixCoalg** - The coalgebra structure
8. **polyCofixUnfold** - Anamorphism from any coalgebra to PolyCofix
9. **polyCofixUnfoldHom** - The unfold as a coalgebra homomorphism
10. **polyCofixUnfoldHom_unique** - Uniqueness via approximation induction
11. **polyCofixCoalg_isTerminal** - The IsTerminal instance via
    `IsTerminal.ofUniqueHom`

## Technical Approach

### Type Transport

Working with dependent types in `Over X` required transporting values between
fibers. The pattern used throughout:

```lean
def polyFixChildAt {P : PolyEndo X} {x : X} (i : polyBetweenIndex X X P x)
    (h : polyBetweenFamily X X P x i ⟶ polyFixCarrier P)
    (e : (polyBetweenFamily X X P x i).left) :
    PolyFix P ((polyBetweenFamily X X P x i).hom e) :=
  let result := h.left e
  have heq : result.1 = (polyBetweenFamily X X P x i).hom e :=
    congrFun (Over.w h) e
  heq ▸ result.2
```

### Structural Recursion

The fold function required tracking fiber membership proofs alongside values:

```lean
def polyFixFoldAtWithProof (P : PolyEndo X) (α : PolyAlg P) (x : X) :
    (t : PolyFix P x) -> { y : α.a.left // α.a.hom y = x }
  | PolyFix.mk _ i children => ...
```

This approach avoids issues with dependent elimination that arise from using
`induction` tactics directly.

### M-type Uniqueness

The uniqueness proof for coalgebra homomorphisms to the terminal coalgebra
required:

- Induction on approximation depth
- Helper lemmas for relating coalgebra structure to M-type structure:
  - `coalg_hom_fiber_eq` - Fiber equality preservation
  - `coalg_hom_index_heq` - Index HEq preservation
  - `coalg_hom_children_heq_core` - Children HEq through morphism composition
- Helper lemmas for heterogeneous equality:
  - `over_mor_left_heq` - HEq for Over morphism applications
  - `cast_sigma_snd_heq` - HEq for sigma snd after casting
  - `sigma_snd_heq_of_eq` - HEq extraction from sigma equality

## Dependencies

- `GebLean.Polynomial` for `polyBetweenIndex`, `polyBetweenFamily`,
  `polyBetweenEvalFunctor`, `familySliceForward`
- `Mathlib.CategoryTheory.Endofunctor.Algebra` for `Endofunctor.Algebra` and
  `Endofunctor.Coalgebra`
- `Mathlib.CategoryTheory.Limits.Shapes.IsTerminal` for `IsInitial.ofUniqueHom`
  and `IsTerminal.ofUniqueHom`

## References

1. Abbott, Altenkirch, Ghani (2005). "Containers: Constructing strictly
   positive types" - Proposition 4.1 gives M-type construction from W-types
2. Avigad, Carneiro, Hudon (2019). "Data Types as Quotients of Polynomial
   Functors" - Section on M-types with Lean-specific implementation
3. mathlib `Mathlib.Data.PFunctor.Univariate.M` - `CofixA`, `Agree`, `M`

## Future Directions

- Lambek's Lemma: show that the structure map is an isomorphism for
  initial algebras and terminal coalgebras
- Connection to QPF (quotients of polynomial functors)
