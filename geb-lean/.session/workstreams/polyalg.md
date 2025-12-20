# Polynomial Endofunctor Algebras and Coalgebras

Status: In Progress

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

### Polynomial Representation of Cofree Comonad (Completed)

The cofree comonad polynomial representation has been fully implemented, mirroring
the free monad structure using standard `Over.Hom` (CategoryTheory.CommaMorphism)
for the annotation morphisms:

1. **PolyCofreeShape P x** - Shapes as M-types with unit annotations
2. **PolyCofreeAnnotPosAt P s n** - Positions at depth n in a shape
3. **PolyCofreeAnnotPos P s** - All positions in a shape (sigma of depth)
4. **PolyCofreeAnnotFiber P s pos** - Fiber at each position
5. **PolyCofreePolyEval A P x** - The polynomial evaluation type using `Over.Hom`
6. **polyCofreeM_to_polyCofreePolyEval** - Extract shape and annotation data
7. **polyCofreePolyEval_to_polyCofreeM** - Backward: reconstruct M-type
8. **polyCofreeM_roundtrip** - Left inverse
9. **polyCofreePolyEval_roundtrip** - Right inverse
10. **polyCofreeEquivPolyEval** - The full equivalence

The proofs use the same patterns as the free monad:

- `Over.homMk` for constructing annotation morphisms
- `overMor_w` for extracting the commutativity condition
- `sigma_cast_eq_mk` for relating casts of sigmas to component casts
- `over_cast_left` for relating casts of Over morphisms to position casts

### Free ⊣ Forget Adjunction

The Free ⊣ Forget adjunction between `Over X` and `PolyAlg P`:

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

### Forget ⊣ Cofree Adjunction

The Forget ⊣ Cofree adjunction between `PolyCoalg P` and `Over X`:

- Cofree: `Over X → Coalg(P)` sends A to the cofree P-coalgebra on A
- Forget: `Coalg(P) → Over X` extracts the carrier
- Bijection: `Hom_Over(Forget(β), A) ≅ Hom_Coalg(β, Cofree(A))`
- The bijection sends f to the anamorphism computing annotations from
  f at each step

Components:

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

## Remaining Work

### Adjunction Completion

The unit and counit natural transformations are defined. Remaining:

1. **polyCoalgUnitNat** - Unit for Forget ⊣ Cofree as natural transformation
   (naturality proof needed for existing `polyCoalgUnit`)
2. **Triangle identities** for Free ⊣ Forget
3. **Triangle identities** for Forget ⊣ Cofree
4. **Adjunction structures** - Construct `Adjunction` instances

### Future Directions

- Lambek's Lemma: show that the structure map is an isomorphism for
  initial algebras and terminal coalgebras

See also: `.session/workstreams/qpf-connection.md` for QPF investigation

## Declaration Index

A reference index of all definitions, lemmas, and theorems in PolyAlg.lean,
organized by category. Line numbers are approximate.

### Polynomial Endofunctors (Lines 36-130)

| Name | Type | Description |
|------|------|-------------|
| `PolyEndo` | Def | Polynomial endofunctor on `Over X` |
| `WTypeEndo` | Def | W-type diagram endofunctor on `Over X` |
| `polyEndoEquiv` | Def | Equivalence `WTypeEndo ≌ PolyEndo` |
| `polyEndoFunctor` | Def | Convert `PolyEndo` to functor `Over X ⥤ Over X` |
| `wTypeEndoFunctor` | Def | Convert `WTypeEndo X` to actual functor |
| `PolyAlg` | Def | Algebras of polynomial endofunctor P |
| `WTypeAlg` | Def | Algebras of W-type endofunctor W |
| `PolyAlg.forget` | Def | Forgetful functor `PolyAlg P ⥤ Over X` |
| `WTypeAlg.forget` | Def | Forgetful functor `WTypeAlg W ⥤ Over X` |

### Initial Algebra / W-types (Lines 145-443)

| Name | Type | Description |
|------|------|-------------|
| `PolyFix` | Inductive | W-type: inductive type for initial algebra carrier |
| `PolyFix.index` | Def | Extract index from PolyFix node |
| `PolyFix.getChildren` | Def | Get children function from PolyFix node |
| `polyFixCarrier` | Def | Carrier of initial algebra as `Over X` object |
| `polyFixChildAt` | Def | Extract child at position with fiber transport |
| `polyFixStrFamily` | Def | Structure map on families |
| `polyFixStrLeft` | Def | Structure map on left component |
| `polyFixStr_comm` | Lemma | Structure map commutes with fiber projection |
| `polyFixStr` | Def | Structure map `P(PolyFix) ⟶ PolyFix` |
| `polyFixAlg` | Def | Initial algebra structure |
| `polyFixFoldAtWithProof` | Def | Catamorphism with fiber proofs |
| `polyFixFoldLeft` | Def | Fold on left component |
| `polyFixFoldLeft_fiber` | Lemma | Fold preserves fibers |
| `polyFixFold` | Def | Full catamorphism morphism |
| `polyEndoFunctor_map_at` | Lemma | Functor action on specific elements |
| `polyFixFoldAtWithProof_transport` | Lemma | Fold with transport |
| `fold_comp_morphism_eq` | Lemma | Fold composition equality |
| `polyFixFold_comm` | Lemma | Fold is algebra homomorphism |
| `polyFixFoldHom` | Def | Fold as algebra homomorphism |
| `polyFixChildAt_rfl` | Lemma | Child extraction simplification |
| `polyFixFoldUnique_at` | Lemma | Fold uniqueness at specific point |
| `polyFixFoldHom_unique` | Lemma | Fold homomorphism uniqueness |
| `polyFixAlg_isInitial` | Def | `PolyFix` is initial algebra |

### Coalgebras (Lines 461-499)

| Name | Type | Description |
|------|------|-------------|
| `PolyCoalg` | Def | Coalgebras of polynomial endofunctor P |
| `WTypeCoalg` | Def | Coalgebras of W-type endofunctor W |
| `PolyCoalg.forget` | Def | Forgetful functor `PolyCoalg P ⥤ Over X` |
| `WTypeCoalg.forget` | Def | Forgetful functor `WTypeCoalg W ⥤ Over X` |

### M-type Approximations (Lines 516-625)

| Name | Type | Description |
|------|------|-------------|
| `PolyCofixApprox` | Inductive | Finite approximations at depth n |
| `PolyCofixApprox.getIndex` | Def | Extract index from approximation |
| `PolyCofixApprox.getChildren` | Def | Extract children function |
| `PolyCofixAgree` | Inductive | Agreement between successive depths |
| `PolyCofixApprox.continue_cast` | Lemma | Transport of `.continue` |
| `PolyCofixApprox.continue_cast'` | Lemma | Reverse transport of `.continue` |
| `PolyCofixApprox.continue_heq` | Lemma | HEq for `.continue` |
| `PolyCofixApprox.intro_cast_heq` | Lemma | HEq for transported `.intro` |
| `PolyCofixApprox.approx_zero_eq_continue` | Lemma | Depth 0 is `.continue` |
| `PolyCofix` | Structure | M-type: consistent chain of approximations |

### M-type Operations (Lines 632-920)

| Name | Type | Description |
|------|------|-------------|
| `PolyCofix.head` | Def | Index at depth 1 (the "head") |
| `PolyCofixAgree.index_eq` | Lemma | Agreement implies index equality |
| `PolyCofix.index_eq_head` | Lemma | Approximation index equals head |
| `PolyCofix.childApproxAt_zero` | Def | Child approx at depth 0 |
| `PolyCofix.childApproxAt_succ_aux` | Def | Child approx extraction via recOn |
| `PolyCofix.childApproxAt_succ` | Def | Child approx at depth n+1 |
| `PolyCofix.childApproxAt` | Def | Child approx at any depth |
| `PolyCofixAgree.children_agree` | Lemma | Agreement passes to children |
| `PolyCofix.childApprox_consistent_zero` | Lemma | Child consistency at 0 |
| `PolyCofix.childApproxAt_succ_aux_intro` | Lemma | `.intro` simp |
| `PolyCofix.childApproxAt_succ_aux_cast` | Lemma | `.intro` cast |
| `PolyCofix.childApproxAt_succ_aux_proof_irrel` | Lemma | Proof irrelevance |
| `PolyCofix.childApproxAt_succ_aux_heq` | Lemma | HEq when all arguments HEq |
| `PolyCofix.childApprox_consistent_aux` | Lemma | Consistency auxiliary |
| `PolyCofix.childApprox_consistent_succ` | Lemma | Consistency at successor |
| `PolyCofix.childApprox_consistent` | Lemma | Full consistency |
| `PolyCofix.children` | Def | Child M-type at position |
| `PolyCofix.ext` | Lemma | M-types equal iff all approx equal |
| `PolyCofix.approx_cast` | Lemma | Transport preserves approximations |
| `PolyCofix.approx_heq` | Lemma | HEq for approximations |
| `PolyCofix.heq_of_approx_heq` | Lemma | M-type HEq from approx HEq |

### Terminal Coalgebra (Lines 916-1100)

| Name | Type | Description |
|------|------|-------------|
| `polyCofixCarrier` | Def | Carrier as `Over X` object |
| `polyCofixChildrenMor` | Def | Children function as Over morphism |
| `polyCofixChildrenMor_snd` | Lemma | Second component of children mor |
| `polyCofixDestFamily` | Def | Destructor on families |
| `polyCofixDestLeft` | Def | Destructor on left component |
| `polyCofixDest_comm` | Lemma | Destructor commutes |
| `polyCofixDest` | Def | Structure map `PolyCofix ⟶ P(PolyCofix)` |
| `polyCofixChildAt` | Def | Extract child with fiber transport |
| `polyCofixMkApprox_zero` | Def | Make approx at depth 0 |
| `polyCofixMkApprox_succ` | Def | Make approx at depth n+1 |
| `polyCofixMkApprox` | Def | Make approx at any depth |
| `polyCofixMkApprox_consistent_*` | Lemmas | Consistency of construction |
| `polyCofixMkFamily` | Def | Constructor on families |
| `polyCofixMkLeft` | Def | Constructor on left component |
| `polyCofixMk_comm` | Lemma | Constructor commutes |
| `polyCofixMk` | Def | Structure map `P(PolyCofix) ⟶ PolyCofix` |
| `polyCofixCoalg` | Def | Terminal coalgebra structure |

### Anamorphism (Lines 1104-1678)

| Name | Type | Description |
|------|------|-------------|
| `polyCofixUnfoldApprox` | Def | Build approximations from coalgebra |
| `PolyCofixAgree.transport` | Lemma | Agreement transports across fibers |
| `polyCofixUnfoldApprox_consistent` | Lemma | Unfold approx is consistent |
| `polyCofixUnfoldApprox_proof_irrel` | Lemma | Proof irrelevance |
| `polyCofixUnfoldApprox_cast` | Lemma | Transport of unfold |
| `polyCofixUnfoldAt` | Def | Anamorphism at specific fiber |
| `polyCofixUnfoldLeft` | Def | Anamorphism on left |
| `polyCofixUnfold_comm` | Lemma | Unfold commutes |
| `polyCofixUnfold` | Def | Full anamorphism morphism |
| `polyCofixUnfold_coalg_comm_*` | Lemmas | Coalgebra homomorphism proofs |
| `polyCofixUnfoldHom` | Def | Anamorphism as coalgebra hom |

### Anamorphism Uniqueness (Lines 1688-2156)

| Name | Type | Description |
|------|------|-------------|
| `coalg_hom_at` | Lemma | Coalgebra hom at specific point |
| `coalg_hom_fiber_eq` | Lemma | Fiber equality for coalg hom |
| `coalg_hom_at_normalized` | Lemma | Normalized form |
| `coalg_hom_index_heq_*` | Lemmas | Index HEq lemmas |
| `coalg_hom_index_eq` | Lemma | Index equality |
| `cast_sigma_snd_heq` | Lemma | Cast of sigma snd gives HEq |
| `over_mor_left_heq` | Lemma | HEq for Over morphism left |
| `coalg_hom_children_heq_core` | Lemma | Children HEq through composition |
| `coalg_hom_children_heq` | Lemma | Full children HEq |
| `polyCofixUnfold_unique_approx_succ` | Lemma | Uniqueness at succ |
| `polyCofixUnfold_unique_approx` | Lemma | Full uniqueness |
| `polyCofixUnfoldHom_unique` | Lemma | Coalg hom uniqueness |
| `polyCofixCoalg_isTerminal` | Def | `PolyCofix` is terminal coalgebra |

### Generic HEq Helpers (Lines 1327-1455)

| Name | Type | Description |
|------|------|-------------|
| `heq_eqRec` | Lemma | HEq for Eq.rec application |
| `polyBetweenEvalFamily_heq` | Lemma | Family HEq for fiber equality |
| `polyBetweenFamily_mor_heq` | Lemma | Morphism HEq |
| `polyBetweenFamily_heq` | Lemma | Family HEq |
| `polyBetweenFamily_left_heq` | Lemma | Left component HEq |
| `polyBetweenFamily_hom_eq_of_heq` | Lemma | Fiber equality from HEq |
| `funext_heq` | Lemma | Function extensionality with HEq |
| `funext_heq_dep` | Lemma | Dependent funext with HEq |
| `overType_hom_heq` | Lemma | HEq for Over hom applications |

### Polynomial Constructions (Lines 2186-2314)

| Name | Type | Description |
|------|------|-------------|
| `overEmpty` | Def | Empty Over object |
| `polyTranslateIndex` | Def | Index for coproduct polynomial |
| `polyTranslateFamily` | Def | Family for coproduct polynomial |
| `polyTranslateAt` | Def | Coproduct polynomial at fiber |
| `polyTranslate` | Def | Coproduct polynomial `A + P` |
| `polyScaleIndex` | Def | Index for product polynomial |
| `polyScaleFamily` | Def | Family for product polynomial |
| `polyScaleAt` | Def | Product polynomial at fiber |
| `polyScale` | Def | Product polynomial `A × P` |
| `PolyFreeM` | Def | Free monad carrier `PolyFix (polyTranslate A P)` |
| `polyFreeMCarrier` | Def | Free monad as Over object |
| `PolyCofreeM` | Def | Cofree comonad carrier `PolyCofix (polyScale A P)` |
| `polyCofreeCarrier` | Def | Cofree comonad as Over object |
| `overInitial` | Def | Initial Over object (Empty) |
| `overTerminal` | Def | Terminal Over object (Unit) |

### Free Monad / W-type Equivalence (Lines 2323-2603)

| Name | Type | Description |
|------|------|-------------|
| `overInitialFiberIsEmpty` | Lemma | Initial fiber is empty |
| `overInitialFiberEmpty` | Def | Equivalence to PEmpty |
| `overTerminalFiberUnique` | Def | Equivalence to PUnit |
| `polyTranslateIndexInitialEquiv` | Def | Index equiv for initial |
| `polyScaleIndexTerminalEquiv` | Def | Index equiv for terminal |
| `polyFixToPolyFreeM` | Def | Convert W-type to free monad |
| `polyFreeMToPolyFix` | Def | Convert free monad to W-type |
| `polyFreeMToPolyFix_polyFixToPolyFreeM` | Thm | Left inverse |
| `polyFixToPolyFreeM_polyFreeMToPolyFix` | Thm | Right inverse |
| `polyFixEquivPolyFreeM` | Def | `PolyFix P ≃ PolyFreeM Empty P` |
| `polyCofixApproxToPolyCofreeM` | Def | Approx conversion |
| `polyCofreeApproxToPolyCofix` | Def | Reverse approx conversion |
| `polyCofixApproxToPolyCofreeM_agree` | Thm | Agreement preserves |
| `polyCofixToPolyCofreeM` | Def | M-type to cofree |
| `polyCofreeApproxToPolyCofix_agree` | Thm | Agreement preserves |
| `polyCofreeToPolyCofix` | Def | Cofree to M-type |
| `polyCofreeApprox_roundtrip_l/r` | Thms | Roundtrip for approx |
| `polyCofix_roundtrip_l/r` | Thms | Roundtrip for M-types |
| `polyCofixEquivPolyCofreeM` | Def | `PolyCofix P ≃ PolyCofreeM Unit P` |

### Free Monad Operations (Lines 2612-2752)

| Name | Type | Description |
|------|------|-------------|
| `polyFreeMPure` | Def | Create leaf (return) |
| `polyFreeMPure_fiber_heq` | Lemma | Pure fiber HEq |
| `polyFreeMBind` | Def | Substitute at leaves (bind) |
| `polyFreeM_pure_bind` | Thm | Left identity: `pure a >>= f = f a` |
| `polyFreeM_bind_pure` | Thm | Right identity: `m >>= pure = m` |
| `polyFreeM_bind_assoc` | Thm | Associativity |
| `polyCofreeExtract` | Def | Extract root annotation |
| `polyCofreeHead` | Def | Get head (annotation + index) |
| `polyCofreeExtendApprox` | Def | Extend approximations |
| `polyCofreeExtendAgree` | Def | Extend preserves agreement |
| `polyCofreeExtend` | Def | Comonad extend operation |

### Free Monad Polynomial Form (Lines 2762-3004)

| Name | Type | Description |
|------|------|-------------|
| `PolyFreeMShape` | Def | Shape = tree with unit leaves |
| `PolyFreeMLeafPos` | Def | Leaf positions in shape |
| `PolyFreeMLeafFiber` | Def | Fiber at leaf position |
| `polyFreeMFamily` | Def | Family from shape |
| `polyFreeMPoly` | Def | Free monad as polynomial |
| `polyFreeMFromShape` | Def | Reconstruct from shape + data |
| `polyFreeMToShape` | Def | Extract shape |
| `polyFreeMLeafData` | Def | Extract leaf data |
| `polyFreeMFromShape_toShape` | Thm | Shape is preserved |
| `polyFreeM_roundtrip` | Thm | Full roundtrip |
| `PolyFreeMPolyEval` | Def | Polynomial evaluation type |
| `polyFreeMPolyEval_to_polyFreeM` | Def | Backward direction |
| `polyFreeM_to_polyFreeMPolyEval` | Def | Forward direction |
| `polyFreeMPolyEval_roundtrip` | Thm | Roundtrip |
| `polyFreeMEquivPolyEval` | Def | Full equivalence |

### Cofree Comonad Shapes (Lines 3013-3143)

| Name | Type | Description |
|------|------|-------------|
| `PolyCofreeShape` | Def | Shape = M-type with unit annotations |
| `PolyCofreePathSeg` | Structure | Path segment (fiber + index) |
| `PolyCofreeAnnotPosAt` | Def | Positions at depth n |
| `PolyCofreeAnnotPos` | Def | All positions (sigma of depth) |
| `PolyCofreeAnnotFiberAt` | Def | Fiber at depth-n position |
| `PolyCofreeAnnotFiber` | Def | Fiber at any position |
| `PolyCofreePolyEval` | Def | Polynomial evaluation type |
| `polyCofreeApproxToShape` | Def | Convert approx to shape approx |
| `polyCofreeApproxToShape_agree` | Thm | Agreement preserves |
| `polyCofreeToShape` | Def | Extract shape from M-type |
| `polyCofreeApproxToShape_index` | Lemma | Index preserved |
| `polyCofreeToShape_head_index` | Lemma | Head index preserved |
| `polyCofreeShapePosToMPos` | Def | Convert shape pos to M-type pos |
| `polyCofreeGetRoot` | Def | Extract root annotation |

### Shape Position Lemmas (Lines 3148-3280)

| Name | Type | Description |
|------|------|-------------|
| `polyBetweenFamily_hom_transport` | Lemma | Hom transport lemma |
| `polyCofreeShapePosToMPos_fiber` | Lemma | Fiber preserved by pos conversion |
| `polyCofreeShapePosToMPos_heq` | Lemma | HEq for pos conversion |
| `polyCofixApprox_continue_heq` | Lemma | Continue HEq for equal fibers |
| `polyCofreeApproxToShape_childApproxAt_succ_aux_heq` | Lemma | Child commutes |
| `polyCofreeToShape_children_heq` | Thm | Shape children ≍ child shapes |

### M-type Based Positions (Lines 3290-3476)

| Name | Type | Description |
|------|------|-------------|
| `PolyCofreeAnnotPosAtM` | Def | Positions on M-type at depth n |
| `PolyCofreeAnnotFiberAtM` | Def | Fiber at M-type position |
| `polyCofreeGetAnnotAtM` | Def | Get annotation at M-type position |
| `polyScaleFamily_eq_P_family` | Lemma | polyScale family equals P family |
| `polyCofreeShape_eq_of_heq_fiber` | Lemma | Shape eq from fiber eq + HEq |
| `polyCofreeAnnotPosAt_cast` | Lemma | Position cast lemma |
| `polyCofreeAnnotPosAt_cast_fiber` | Lemma | Cast preserves fiber |
| `polyCofreeAnnotFiberAt_transport` | Lemma | Fiber transport |
| `polyCofreeToShape_children_eq` | Lemma | Shape children equality |
| `polyCofreeShapePosToMPosAt` | Def | Depth-n version of pos conversion |
| `polyCofreeAnnotFiber_eq` | Lemma | Fiber equality via conversion |
| `polyCofreeGetAnnotAt` | Def | Get annotation via shape pos |
| `polyCofreeGetAnnot` | Def | Get annotation at any position |
| `polyCofreeM_to_polyCofreePolyEval` | Def | Forward: M-type to poly eval |

### Shape Data Reconstruction (Lines 3491-3665)

| Name | Type | Description |
|------|------|-------------|
| `polyCofreeChildAnnotFn` | Def | Child annotation function |
| `polyCofreeChildAnnotFn_fiber` | Lemma | Fiber preserved |
| `polyCofreeChildAnnotFn_zero_eq_childRoot` | Lemma | Zero = child root |
| `polyCofreeFromShapeAndDataApprox` | Def | Build approx from shape + data |
| `polyCofreeFromShapeAndDataApprox_agree` | Lemma | Agreement |
| `polyCofreeFromShapeAndData` | Def | Build M-type from shape + data |
| `polyCofreePolyEval_to_polyCofreeM` | Def | Backward: poly eval to M-type |
| `polyCofreeFromShapeAndDataApprox_toShape` | Lemma | Shape preserved |
| `polyCofreePolyEval_roundtrip_shape` | Lemma | Shape roundtrip |
| `PolyCofix.children_heq` | Lemma | Children HEq for HEq positions |

### Annotation Extraction Lemmas (Lines 3683-4216)

| Name | Type | Description |
|------|------|-------------|
| `polyCofreeGetAnnotAtM_val_of_eqRec` | Lemma | Extract val via eqRec |
| `polyCofreeGetAnnotAtM_val_of_eq` | Lemma | Val equality |
| `polyCofreeGetAnnotAtM_fromShapeAndData_succ` | Lemma | Succ reconstruction |
| `polyCofreeGetAnnotAtM_fromShapeAndData` | Lemma | Full reconstruction lemma |
| `polyCofreePolyEval_roundtrip` | Lemma | Poly eval roundtrip |

### M-type Roundtrip Helpers (Lines 4216-4350)

| Name | Type | Description |
|------|------|-------------|
| `polyBetweenFamily_hom_eq_of_index_eq` | Lemma | Hom eq from index eq |
| `polyCofreeM_roundtrip_codomain_eq` | Lemma | Codomain eq for roundtrip |
| `prod_mk_heq` | Lemma | Product HEq |
| `subtype_heq_of_val_eq_pred_heq` | Lemma | Subtype HEq |
| `polyCofix_head_heq` | Lemma | Head HEq for HEq M-types |
| `polyCofreeShape_head_snd_heq` | Lemma | Shape head snd HEq |
| `polyCofixApprox_intro_heq_of_fiber_eq` | Lemma | Intro HEq |
| `polyCofreeFromShapeAndDataApprox_heq_of_shapes_heq` | Lemma | Approx HEq |

### Parent-Child Annotation Lemmas (Lines 4350-4573)

| Name | Type | Description |
|------|------|-------------|
| `polyCofreeAnnotPos_fiber_eq` | Lemma | Fiber equality for parent position |
| `polyCofreeAnnotPos_head2_heq` | Lemma | Head P-index HEq |
| `polyCofreeAnnotPos_grandchild_fiber_eq` | Lemma | Grandchild fiber equality |
| `polyCofreeAnnotPos_grandchild_shape_heq` | Lemma | Grandchild shape HEq |
| `polyCofreeAnnotPos_grandchild_type_eq` | Lemma | Grandchild type equality |
| `polyCofreeAnnotPosAt_family_eq` | Lemma | Position family equality |
| `polyCofreeChildren_eq_of_fiber_eq` | Lemma | Children M-type equality |
| `polyCofreeGetAnnot_parent_child_eq` | Lemma | Parent-child annot eq |

### M-type Roundtrip (Lines 4647-4862)

| Name | Type | Description |
|------|------|-------------|
| `polyCofreeFromShapeAndData_children_approx_heq` | Lemma | Children HEq |
| `polyCofreeM_roundtrip_children_heq` | Lemma | Roundtrip children HEq |
| `polyCofreeM_roundtrip` | Lemma | Full M-type roundtrip |

### Free Algebra Functor (Lines 4862-5099)

| Name | Type | Description |
|------|------|-------------|
| `polyFreeMStrFamily` | Def | Free algebra str on families |
| `polyFreeMStrLeft` | Def | Free algebra str on left |
| `polyFreeMStr_comm` | Lemma | Str commutes |
| `polyFreeMStr` | Def | Free algebra structure map |
| `polyFreeAlg` | Def | Free P-algebra on A |
| `polyFreeMap_fiber_eq` | Lemma | Map preserves fiber |
| `polyFreeMapAt` | Def | Map at specific fiber |
| `polyFreeMapLeft` | Def | Map on left component |
| `polyFreeMap_comm` | Lemma | Map commutes |
| `polyFreeMap` | Def | Free monad map morphism |
| `polyFreeMapAt_transport` | Lemma | Map with transport |
| `polyFreeMBind_transport` | Lemma | Bind with transport |
| `sigma_match_snd` | Lemma | Match on sigma snd |
| `polyFreeMapAt_as_bind` | Lemma | Map equals bind with pure |
| `polyFreeMapHom_comm` | Lemma | Map is algebra hom |
| `polyFreeAlgMap` | Def | Free algebra homomorphism |
| `polyFreeMapAt_id` | Lemma | Map id = id |
| `polyFreeMap_id` | Lemma | Map preserves identity |
| `polyFreeMapAt_comp` | Lemma | Map preserves composition |
| `polyFreeMap_comp` | Lemma | Map preserves composition |
| `polyFreeAlgMap_id` | Lemma | Alg map id = id |
| `polyFreeAlgMap_comp` | Lemma | Alg map preserves comp |
| `polyFreeFunctor` | Def | Free functor `Over X ⥤ PolyAlg P` |

### Free/Forget Adjunction (Lines 5120-5269)

| Name | Type | Description |
|------|------|-------------|
| `polyFreeUnitLeft` | Def | Unit on left component |
| `polyFreeUnit_comm` | Lemma | Unit commutes |
| `polyFreeUnit` | Def | Unit `A ⟶ Free(A)` |
| `polyFreeUnit_naturality` | Lemma | Unit is natural |
| `polyFreeUnitNat` | Def | Unit as nat trans |
| `polyFreeCounitFoldAt` | Def | Counit fold at fiber |
| `polyFreeCounitFoldAt_cast` | Lemma | Fold with cast |
| `polyFreeCounitFoldLeft` | Def | Fold on left |
| `polyFreeCounitFoldLeft_fiber` | Lemma | Fold fiber |
| `polyFreeCounitFold` | Def | Counit morphism |
| `polyFreeCounitFold_comm` | Lemma | Counit is alg hom |
| `polyFreeCounitHom` | Def | Counit as alg hom |
| `polyFreeCounitHom_natural` | Lemma | Counit naturality |
| `polyFreeCounitNat` | Def | Counit as nat trans |

### Cofree Coalgebra Functor (Lines 5270-5737)

| Name | Type | Description |
|------|------|-------------|
| `polyCofreeChildrenMor` | Def | Children as morphism |
| `polyCofreeStrFamily` | Def | Str on families |
| `polyCofreeStrLeft` | Def | Str on left |
| `polyCofreeStr_comm` | Lemma | Str commutes |
| `polyCofreeStr` | Def | Structure map |
| `polyCofreeCoalg` | Def | Cofree P-coalgebra on A |
| `polyCofreeMap_fiber_eq` | Lemma | Map preserves fiber |
| `polyCofreeMapApprox` | Def | Map on approximations |
| `polyCofreeMapApprox_agree` | Thm | Map preserves agreement |
| `polyCofreeMapAt` | Def | Map at fiber |
| `polyCofreeMapLeft` | Def | Map on left |
| `polyCofreeMap_comm` | Lemma | Map commutes |
| `polyCofreeMap` | Def | Map morphism |
| `polyCofreeMapApprox_index_snd` | Lemma | Map preserves index snd |
| `polyCofreeMapApprox_getIndex` | Lemma | Map preserves getIndex |
| `polyCofreeMapAt_head_snd` | Lemma | Map preserves head snd |
| `polyCofreeMapApprox_childApproxAt_succ_aux_eq` | Lemma | Map child aux |
| `polyCofreeMapApprox_childApproxAt_zero_heq` | Lemma | Map children at 0 |
| `polyCofreeMapApprox_childApproxAt_succ_heq` | Lemma | Map children at succ |
| `polyCofreeMapAt_children_heq` | Lemma | Map preserves children |
| `polyCofreeChildrenMor_map_heq` | Lemma | Children mor and map |
| `polyCofreeMapHom_comm` | Lemma | Map is coalg hom |
| `polyCofreeCoalgMap` | Def | Coalgebra homomorphism |
| `polyCofreeMapApprox_id` | Lemma | Map id on approx |
| `polyCofreeMapAt_id` | Lemma | Map id = id |
| `polyCofreeMap_id` | Lemma | Map identity |
| `polyCofreeMapApprox_comp` | Lemma | Map composition on approx |
| `polyCofreeMapAt_comp` | Lemma | Map composition |
| `polyCofreeMap_comp` | Lemma | Map preserves comp |
| `polyCofreeCoalgMap_id` | Lemma | Coalg map id |
| `polyCofreeCoalgMap_comp` | Lemma | Coalg map comp |
| `polyCofreeFunctor` | Def | Cofree functor `Over X ⥤ PolyCoalg P` |

### Forget/Cofree Adjunction (Lines 5752-5871)

| Name | Type | Description |
|------|------|-------------|
| `polyCofreeCounitLeft` | Def | Counit on left |
| `polyCofreeCounit_comm` | Lemma | Counit commutes |
| `polyCofreeCounit` | Def | Counit `Cofree(A) ⟶ A` |
| `polyCofreeCounit_naturality` | Lemma | Counit natural |
| `polyCofreeCounitNat` | Def | Counit as nat trans |
| `polyCoalgUnitApprox` | Def | Unit approx |
| `polyCoalgUnitApprox_consistent` | Lemma | Unit approx consistent |
| `polyCoalgUnitAt` | Def | Unit at fiber |
| `polyCoalgUnitLeft` | Def | Unit on left |
| `polyCoalgUnit_comm` | Lemma | Unit commutes |
| `polyCoalgUnit` | Def | Unit `β.V ⟶ Cofree(β.V)` |
