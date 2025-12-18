# Polynomial Endofunctor Algebras

Status: Completed

## Objective

Formalize algebras of polynomial endofunctors on slice categories `Over X`,
including the construction of initial algebras (W-types).

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

### Homomorphism Proofs

The algebra homomorphism condition required:

- Helper lemma `polyEndoFunctor_map_at` to characterize functor action
- Transport lemma `polyFixFoldAtWithProof_transport` for independence of
  proof paths
- Morphism composition lemma `fold_comp_morphism_eq`

## Dependencies

- `GebLean.Polynomial` for `polyBetweenIndex`, `polyBetweenFamily`,
  `polyBetweenEvalFunctor`, `familySliceForward`
- `Mathlib.CategoryTheory.Endofunctor.Algebra` for `Endofunctor.Algebra`
- `Mathlib.CategoryTheory.Limits.Shapes.IsTerminal` for `IsInitial.ofUniqueHom`

## Future Directions

- Lambek's Lemma: show that the structure map is an isomorphism for
  initial algebras
- Coalgebras and terminal coalgebras (M-types)
- Connection to QPF (quotients of polynomial functors)
