# WeightedCowedge vs StrongRestrictedCowedge Investigation

## Goal

Determine the precise categorical relationship between `WeightedCowedge` and
`StrongRestrictedCowedge`. The possibilities are:

1. An inclusion `WeightedCowedge → StrongRestrictedCowedge` (one direction)
2. An inclusion `StrongRestrictedCowedge → WeightedCowedge` (other direction)
3. Inclusions in both directions (possibly an equivalence)
4. No inclusion in either direction

For any inclusions that exist, determine whether they are:

- Faithful
- Full
- Fully faithful

## Definitions

### WeightedCowedge

```lean
abbrev WeightedCowedge (W : Cᵒᵖ ⥤ C ⥤ Type v) (P : Cᵒᵖ ⥤ C ⥤ Type v) :=
  WeightedCocone (profunctorOnOpCoTwistedArrow C W)
    (profunctorOnCoTwistedArrow C P)
```

A `WeightedCocone` over `CoTwistedArrow C` where:

- Weight: `profunctorOnOpCoTwistedArrow C H` evaluates `H` at co-twisted arrow
  endpoints
- Diagram: `profunctorOnCoTwistedArrow C G` evaluates `G` at co-twisted arrow
  endpoints

Naturality condition (for `f : j ⟶ j'` in `CoTwistedArrow C`):

```text
D.map f ≫ c.leg j' w = c.leg j (W.map f.op w)
```

### StrongRestrictedCowedge

```lean
structure StrongRestrictedCowedge where
  pt : D
  family : ParanatSig H (G ⇓ pt)
  isParanatural : IsParanatural H (G ⇓ pt) family
```

Components:

- `pt`: apex object in D
- `family`: for each `A : C` and `x : H(A,A)`, a morphism `G(A,A) → pt`
- `isParanatural`: the family preserves `DiagCompat` pairs

### RestrictedCowedge

```lean
structure RestrictedCowedge where
  pt : D
  family : ParanatSig H (G ⇓ pt)
  isDinatural : IsDinatural H (G ⇓ pt) family
```

Same as `StrongRestrictedCowedge` but with weaker `IsDinatural` condition.

## Results Summary

### Final Results

1. **WeightedCowedge → StrongRestrictedCowedge**: Faithful but NOT full
   (`strongRestrictionFunctor`)
   - The extracted family at identity co-twisted arrows is paranatural
   - Proven via `weightedCowedgeFamilyAtIdentity_paranatural`
   - Faithful: different weighted cowedges give different strong restricted
     cowedges
   - NOT full: proven via factorization argument

2. **StrongRestrictedCowedge → RestrictedCowedge**: Fully faithful inclusion
   (`StrongRestrictedCowedge.inclusion`)
   - Every paranatural transformation is dinatural
   - The inclusion functor is identity on morphisms

3. **WeightedCowedge → RestrictedCowedge**: Faithful but NOT full
   (`restrictionFunctor`)
   - Factors as: `strongRestrictionFunctor ⋙ StrongRestrictedCowedge.inclusion`
   - Not full: there exist restricted cowedge morphisms that don't lift

4. **RestrictedCowedge → StrongRestrictedCowedge**: No inclusion exists
   - Dinaturality is strictly weaker than paranaturality

5. **StrongRestrictedCowedge → WeightedCowedge**: No inclusion exists
   - Insufficient data at off-diagonal co-twisted arrows

### Direction: WeightedCowedge → StrongRestrictedCowedge (PROVEN)

**Discovery**: WeightedCowedge naturality implies paranaturality of the
extracted family.

**Reasoning**:
For `DiagCompat H A B f x y` (meaning `H.rmap f x = H.lmap f y`):

1. Both elements map to the same `z` at the off-diagonal co-twisted arrow
   `coTwObjMk f`:
   - `profunctor_map_coTwToIdentityAtSource_diag`: maps `x` to `z`
   - `profunctor_map_coTwToIdentityAtTarget_diag`: maps `y` to `z`

2. WeightedCowedge naturality along `coTwToIdentityAtSource f`:

   ```text
   (G.map f.op).app A ≫ family(A)(x) = wc.leg(coTwObjMk f)(z)
   ```

3. WeightedCowedge naturality along `coTwToIdentityAtTarget f`:

   ```text
   (G.obj (op B)).map f ≫ family(B)(y) = wc.leg(coTwObjMk f)(z)
   ```

4. Since RHS are equal, LHS are equal:

   ```text
   (G.map f.op).app A ≫ family(A)(x) = (G.obj (op B)).map f ≫ family(B)(y)
   ```

This is exactly the `DiagCompat` condition for the slice profunctor `(G ⇓ pt)`,
proving paranaturality.

**Implementation**:

- `weight_map_coTwToIdentity_from_diagCompat`: Helper lemma showing compatible
  elements map to the same weight
- `weightedCowedgeFamilyAtIdentity_paranatural`: Main paranaturality theorem
- `strongRestrictionFunctor`: The functor `WeightedCowedge H G ⥤
  StrongRestrictedCowedge G H`
- `strongRestrictionFunctor_faithful`: Proof of faithfulness
- `restrictionFunctor_eq_inclusion_comp_strong`: Factorization theorem

### Direction: StrongRestrictedCowedge → WeightedCowedge (NO INCLUSION)

**Result**: No inclusion exists.

**Obstruction Analysis**:
To extend a paranatural family to a weighted cowedge, we need legs at ALL
co-twisted arrows, not just identities. The naturality equations constrain:

```text
leg(coTwObjMk f)(W.map(coTwToIdentityAtSource f).op w) =
  (G.map f.op).app I₀ ≫ leg(id I₀)(w)
leg(coTwObjMk f)(W.map(coTwToIdentityAtTarget f).op w') =
  (G.obj (op I₁)).map f ≫ leg(id I₁)(w')
```

The problem: not every element of `W(coTwObjMk f)` is in the image of these
maps from identity co-twisted arrows!

For the Hom profunctor, `W(coTwObjMk f) = H(I₀, I₁)`. Elements in the image:

- From `H(I₁, I₁)`: elements of form `H(f, I₁)(y)` (contravariant action)
- From `H(I₀, I₀)`: elements of form `H(I₀, f)(x)` (covariant action)

If there are elements of `H(I₀, I₁)` not in either image, there's no
canonical way to define the leg there.

### Fullness of Strong Restriction Functor (NOT FULL)

**Result**: `strongRestrictionFunctor` is NOT full.

**Proof**: By the factorization
`restrictionFunctor = strongRestrictionFunctor ⋙ StrongRestrictedCowedge.inclusion`

Since:

- `StrongRestrictedCowedge.inclusion` is full (only fullness is required, not
  full faithfulness)
- `restrictionFunctor` is NOT full (proven via `WalkingParallelPair`
  counterexample)

If `strongRestrictionFunctor` were full, the composition with a full functor
would also be full. Contradiction.

**Implementation**:

- `Functor.not_full_of_comp_not_full_and_full` (in `Utilities/Category.lean`):
  General contrapositive lemma
- `cValued_strongRestrictionFunctor_not_full`: Application to strong restriction

## Tasks

- [x] Investigate relationship structure
- [x] Prove `weightedCowedgeFamilyAtIdentity_paranatural`
- [x] Construct strong restriction functor: `WeightedCowedge →
  StrongRestrictedCowedge`
- [x] Prove faithfulness of strong restriction functor
- [x] Investigate `StrongRestrictedCowedge → WeightedCowedge` direction (NO
  inclusion)
- [x] Determine if strong restriction functor is full (NOT full)

## Answered Questions

1. **Is the strong restriction functor full?**
   NO. The proof uses the factorization through
   `StrongRestrictedCowedge.inclusion` and the non-fullness of
   `restrictionFunctor`. Implemented in
   `cValued_strongRestrictionFunctor_not_full`.

2. **Does an inclusion StrongRestrictedCowedge → WeightedCowedge exist?**
   NO. Paranatural families only provide data at identity co-twisted arrows,
   but weighted cowedges require legs at all co-twisted arrows. Elements of the
   weight at off-diagonal positions may not be reachable from identity
   positions.

## Related Files

- `GebLean/Weighted.lean`: Main definitions and existing functors
- `GebLean/Utilities/TwArrPresheaf.lean`: Profunctor constructions on twisted
  arrows
- `.session/workstreams/paranatural-investigations.md`: Background on
  paranaturality
