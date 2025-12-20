# Indexed EAT Implementation

## Status: Refactoring to Generic Quotient Construction

## Goal

Implement a generic essentially algebraic theory (EAT) embedding framework that:

1. Takes an EAT specification (polynomial endofunctor + equations)
2. Produces an adjunction L ⊣ Φ embedding models into copresheaves
3. Decomposes as two adjunctions: completion and quotient
4. **Requires minimal client effort**: clients should only specify the polynomial
   and equations, and the full adjunction should be derived automatically

## Architecture Problem (Current State)

The current implementation has a structural problem:

### What Should Be Generic (in IndexedEAT.lean)

1. `FreeAlgEquiv` - the equivalence relation on free algebras induced by EAT equations
2. `FreeAlgQuot` - the quotient type
3. **Quotient algebra structure** - lifting structure maps through quotients
4. **Quotient homomorphism** - the quotient map as an algebra homomorphism
5. **Functoriality** - quotient respects morphisms in Over X
6. **Universal property** - factorization through quotient for model targets
7. The full `EATHasQuotient` instance should be derivable generically

### What Should Be Client-Specific (in CatIndexedEAT.lean)

1. `catPoly : PolyEndo Obj` - the polynomial encoding category operations (~100 lines)
2. `CatEquiv/catEquations` - the generating relations and their closure (~100 lines)
3. `catEAT : IndexedEAT Obj` - bundling poly + equations (~5 lines)

### Current Problem

`CatIndexedEAT.lean` is ~1500 lines, with ~1000 lines devoted to constructing
the `EATHasQuotient` instance. This includes:

- `catQuotientStrAt` - lifting structure through quotients (6 cases by position)
- `catQuotientAlg` - the quotient P-algebra
- `catQuotientHom` - quotient homomorphism proof
- `catQuotientAlgMap` - functoriality construction
- `catQuotientFactor` - universal property factorization (~400 lines of proof!)
- Naturality and uniqueness proofs

All of this work is **polynomial-independent** and should be generic.

## Refactoring Plan

### Step 1: Generic Quotient Structure Map

The quotient structure map needs to lift through products of quotients. Currently
`catQuotientStrAt` handles this case-by-case for catPoly's positions. The generic
version should:

1. For each position p with arity family F, define the structure map by nested
   `Quot.lift` applications
2. The number of nestings equals the cardinality of F.left (the arity)
3. The congruence property `FreeAlgEquiv.cong` ensures each lift is well-defined

Key observation: the arity types in catPoly are Unit (arity 1) or Bool (arity 2).
For finite arities, we can define a generic lifting combinator.

### Step 2: Generic Quotient Algebra

Once the structure map lifts generically, define:

```lean
def genericQuotientAlg (T : IndexedEAT X) (A : Over X) : PolyAlg T.poly
```

This replaces the client-specific `catQuotientAlg`.

### Step 3: Generic Quotient Homomorphism

Prove generically that the quotient map is an algebra homomorphism:

```lean
def genericQuotientHom (T : IndexedEAT X) (A : Over X) :
    polyFreeAlg A T.poly ⟶ genericQuotientAlg T A
```

### Step 4: Generic Functoriality

Show the quotient construction is functorial in A:

```lean
def genericQuotientAlgMap (T : IndexedEAT X) (A B : Over X) (f : A ⟶ B) :
    genericQuotientAlg T A ⟶ genericQuotientAlg T B
```

### Step 5: Generic Universal Property

The factorization proof (`catQuotientFactor`) is the largest piece (~400 lines).
It should be generic because:

1. It uses `Quot.lift` which is independent of the specific polynomial
2. The algebra homomorphism property uses the generic structure

### Step 6: Generic EATHasQuotient Instance

Provide a default instance:

```lean
instance (T : IndexedEAT X) : EATHasQuotient T := ...
```

This should work for ANY IndexedEAT without client code.

### Step 7: Simplify CatIndexedEAT

After refactoring, `CatIndexedEAT.lean` should shrink to ~200-300 lines containing:

1. `CatPolyPosition`, `CatPolyArity`, `CatPolyPosition.family` (~80 lines)
2. `catPoly` construction (~20 lines)
3. `CatEquivGen`, `CatEquiv`, `catEquations` (~80 lines)
4. `catEAT : IndexedEAT Obj` (~10 lines)
5. Documentation and correspondence with FreeMor (~50 lines)

## Technical Challenges

### Finite Arity Lifting

The main challenge is lifting through products of quotients generically. Options:

1. **Induction on arity type**: If the arity type is Fintype, we can induct
2. **Dependent function space**: Use `∀ e, FreeAlgQuot T A (family.hom e)` directly
3. **Choice principle**: For mere existence, use Quot.choice (but we avoid this)

The current catPoly uses Unit and Bool arities. A generic solution might:

- Require `[Fintype (family.left)]` for each position
- Or work with the function space directly via dependent `Quot.lift`

### Algebra Homomorphism Proof

The proof that the quotient map is an algebra homomorphism requires showing
the structure map on representatives followed by quotient equals quotient followed
by structure. This is where `catQuotientStrAt_mk` comes in - it should be generic.

## Code References

- `GebLean/PolyAlg.lean` - polynomial algebra infrastructure
- `GebLean/PLang/IndexedEAT.lean` - current generic EAT framework
- `GebLean/PLang/CatIndexedEAT.lean` - category instance (to be simplified)

## Completed Work

### PLang/IndexedEAT.lean

Core Definitions:

- `IndexedEAT X` - core structure with poly + equations + equivalence proof
- `PolyFixRel` - indexed equivalence relation on initial algebra
- `FreeAlgEquiv` - congruence closure on free algebra
- `FreeAlgQuot` - quotient type for free algebra
- `IsEATModel` - model predicate via fold

EAT Adjunction (via EATHasQuotient):

- `EATHasQuotient` - typeclass (to be replaced with generic instance)
- `eatAdjunctionUnit` / `eatAdjunctionCounit` - adjunction data
- `eatAdjunction` - the full L ⊣ Φ adjunction

Generic Quotient Infrastructure (new):

- `QuotLiftable` - typeclass for lifting through products of quotients
- `QuotLiftable Unit` / `QuotLiftable Bool` - instances for common arities
- `boolProd` - helper for constructing Bool-indexed products
- `quotLiftBool` - lifting through two quotients
- `PolyHasLiftableArities` - constraint for polynomials with liftable arities
- `genericQuotientStrAt` - structure map at a position using QuotLiftable
- `genericQuotientStrAt_mk` - computation rule for representatives
- `genericQuotientStrLeft` / `genericQuotientStr` - full structure map
- `genericQuotientAlg` - the generic quotient P-algebra
- `quot_mk_transport_eq` - transport commutes with Quot.mk
- `genericExtractQuotChildren` - extract children from morphism to quotient carrier
- `genericExtractQuotChildren_comp_quotient` - composition with quotient map lemma
- `genericQuotientHom` - quotient map as algebra homomorphism (done)

### PLang/CatIndexedEAT.lean

Category-specific (to keep):

- `CatPolyPosition` / `CatPolyArity` / `CatPolyPosition.family`
- `catPoly : PolyEndo Obj`
- `CatEquivGen` / `CatEquiv` / `catEquations`
- `catEAT : IndexedEAT Obj`

To be made generic (in progress):

- `catQuotientStrAt` -> `genericQuotientStrAt` (done)
- `catQuotientAlg` -> `genericQuotientAlg` (done)
- `catQuotientHom` -> `genericQuotientHom` (done)
- `catQuotientAlgMap` -> `genericQuotientAlgMap` (next)
- `catQuotientFactor` -> `genericQuotientFactor`
- `EATHasQuotient catEAT` instance -> generic instance

Current state: CatIndexedEAT.lean has cascading errors from the refactoring.
The duplicate `quot_mk_transport_eq` was removed; remaining errors are in
the `catQuotientFactor` proof which will be replaced by a generic version.

## Design Decisions

1. **No Quotient.choice**: Use fold predicate and explicit lifting
2. **Generic quotients**: The quotient construction should work for any EAT
3. **Finite arities**: May require Fintype constraint on arity types
4. **Full subcategory**: EATModel remains a full subcategory via bundling
