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

### Free Monad and Cofree Comonad

Extended the polynomial endofunctor framework to define free monads and
cofree comonads:

1. **polyTranslate A P** - Coproduct polynomial `Y ↦ A + P(Y)`, representing
   "leaves from A or nodes from P"
2. **polyScale A P** - Product polynomial `Y ↦ A × P(Y)`, representing
   "label from A paired with node from P"
3. **PolyFreeM A P** - Free monad carrier as `PolyFix (polyTranslate A P)`,
   giving trees with A-labeled leaves
4. **PolyCofreeM A P** - Cofree comonad carrier as `PolyCofix (polyScale A P)`,
   giving streams with A-annotations
5. **polyFixEquivPolyFreeM** - Equivalence `PolyFix P ≃ PolyFreeM Empty P`
6. **polyCofixEquivPolyCofreeM** - Equivalence `PolyCofix P ≃ PolyCofreeM
   Terminal P`

Monad structure on PolyFreeM:

- **polyFreeMPure** - Creates a leaf
- **polyFreeMBind** - Substitutes at leaves
- **polyFreeM_pure_bind** - Left identity law
- **polyFreeM_bind_pure** - Right identity law
- **polyFreeM_bind_assoc** - Associativity

Comonad structure on PolyCofreeM:

- **polyCofreeExtract** - Extracts the root annotation
- **polyCofreeExtend** - Recomputes annotations via a function on subtrees

### Polynomial Representation of Free Monad (Completed)

The free monad functor `A ↦ PolyFreeM A P` is itself a polynomial functor on
`Over X`. Implemented as:

1. **PolyFreeMShape P x** - Tree shapes as `PolyFreeM (overTerminal X) P x`
2. **PolyFreeMLeafPos P shape** - Leaf positions as directions in each shape
3. **PolyFreeMLeafFiber P shape pos** - Fiber at each leaf position
4. **PolyFreeMPolyEval A P x** - Sigma type of shape and leaf data function
5. **polyFreeM_to_polyFreeMPolyEval** - Forward direction: extract shape and
   leaf data
6. **polyFreeMPolyEval_to_polyFreeM** - Backward direction: reconstruct tree
7. **polyFreeM_roundtrip** - Left inverse (start from tree)
8. **polyFreeMPolyEval_roundtrip** - Right inverse (start from polynomial eval)
9. **polyFreeMEquivPolyEval** - The full equivalence

The proofs use helper lemmas for working with dependent types:

- `sigma_subtype_fun_app_eq` - Extract function values from sigma equalities
- `sigma_cast_eq_mk` - Decompose sigma casts into component casts
- `subtype_fun_heq'` - HEq of subtypes of function types

## In Progress

### Polynomial Representation of Cofree Comonad (Partial)

The cofree comonad polynomial representation has the following infrastructure:

1. **PolyCofreeShape P x** - Shapes as M-types with unit annotations
2. **PolyCofreeAnnotPosAt P s n** - Positions at depth n in a shape
3. **PolyCofreeAnnotPos P s** - All positions in a shape (sigma of depth)
4. **PolyCofreeAnnotFiber P s pos** - Fiber at each position
5. **PolyCofreePolyEval A P x** - The polynomial evaluation type
6. **polyCofreeApproxToShape** - Convert approximations to shape approximations
7. **polyCofreeToShape** - Extract shape from a cofree comonad value
8. **polyCofreeToShape_head_index** - Head index is preserved
9. **polyCofreeShapePosToMPos** - Convert shape positions to M-type positions
10. **polyCofreeGetRoot** - Extract root annotation

The full equivalence `PolyCofreeM A P ≃ PolyCofreePolyEval A P` remains to be
proven. The challenge is navigating positions in M-type structure: the shape
of a child is not definitionally equal to the child of the shape, requiring
careful type transport.

### Free ⊣ Forget Adjunction (Partial)

The Free ⊣ Forget adjunction has the following implemented:

1. **polyFreeAlg A P** - Free P-algebra on A (carrier = trees with A-leaves)
2. **polyFreeAlgMap** - Functorial action: maps leaves via morphism in Over X
3. **polyFreeFunctor P** - Free functor `Over X ⥤ PolyAlg P`
4. **polyForgetFunctor P** - Forgetful functor `PolyAlg P ⥤ Over X`
5. **polyFreeUnit A P** - Unit morphism: embeds A into Free(A)
6. **polyFreeUnitNat P** - Unit as natural transformation `𝟭 ⟶ Free ⋙ Forget`
7. **polyFreeCounitFoldAt** - Fold function with fiber proofs
8. **polyFreeCounitFoldAt_cast** - Transport lemma for folding
9. **polyFreeCounitFold P α** - Counit morphism from Free(Forget(α)) to α
10. **polyFreeCounitFold_comm** - Commutativity for algebra homomorphism
11. **polyFreeCounitHom P α** - Counit as algebra homomorphism

Remaining work:

- Counit naturality (natural transformation `Free ⋙ Forget ⟶ 𝟭`)
- Triangle identities
- Construct the `Adjunction` instance

### Forget ⊣ Cofree Adjunction (In Progress)

For coalgebras:

- Cofree: `Over X → Coalg(P)` sends A to the cofree P-coalgebra on A
- Forget: `Coalg(P) → Over X` extracts the carrier
- Bijection: `Hom_Over(Forget(β), A) ≅ Hom_Coalg(β, Cofree(A))`
- The bijection sends f to the anamorphism computing annotations from
  f at each step

Implemented:

1. **polyCofreeCoalg A P** - Cofree P-coalgebra on A (carrier = M-type with
   A-annotations)
2. **polyCofreeCoalgMap A B P f** - Coalgebra homomorphism for morphism f
3. **polyCofreeFunctor P** - Cofree functor `Over X ⥤ PolyCoalg P`
4. **polyCoalgForgetFunctor P** - Forgetful functor `PolyCoalg P ⥤ Over X`
5. **polyCofreeCounit A P** - Counit morphism `Cofree(A) → A` (extracts root)
6. **polyCofreeCounit_naturality** - Naturality of counit
7. **polyCofreeCounitNat P** - Counit as natural transformation
8. **polyCoalgUnitApprox P β n x s** - Approximations for unit anamorphism
9. **polyCoalgUnitApprox_consistent** - Successive approximations agree
10. **polyCoalgUnitAt P β x s** - M-type for unit construction
11. **polyCoalgUnit P β** - Unit morphism `β.V → Cofree(β.V)` in Over X

Remaining work:

- Prove unit is coalgebra homomorphism (structure maps commute)
- Unit naturality (natural transformation `𝟭 ⟶ Forget ⋙ Cofree`)
- Triangle identities
- Construct the `Adjunction` instance

## Future Directions

- Lambek's Lemma: show that the structure map is an isomorphism for
  initial algebras and terminal coalgebras
- Connection to QPF (quotients of polynomial functors)
