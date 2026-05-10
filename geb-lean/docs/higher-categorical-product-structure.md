# Higher Categorical Structure via Product Categories

This document investigates whether iterated products of the judgment category J
provide a natural home for n-categorical and ∞-categorical structure.

## The Question

Given:

- [J, Type] embeds Cat (1-categories)
- [J × J, Type] may encode 2-categorical structure
- [J × J, Type] ≅ [2 → J, Type] (functors from the walking arrow to J?)

**Questions**:

1. How precisely do natural transformations between functors correspond to
   transformations between [J, Type]-valued copresheaves, hence [C × J, Type]?

2. If [J × J, Type] is natural for 2-categories:
   - Is [J × J × J, Type] ≅ [3 → J, Type] natural for 3-categories?
   - Is [Nat → J, Type] natural for ∞-categories?

## The Pattern

|n|Category|Copresheaf Target|
|---|---|---|
|1|Cat|[J, Type]|
|2|2-Cat|[J², Type] = [J × J, Type]|
|3|3-Cat|[J³, Type] = [J × J × J, Type]|
|ω|ω-Cat|[J^ω, Type] = ???|

## Analysis

### Two Distinct Generalizations

There are two natural ways to generalize the [J, Type] construction to higher
categorical structure:

**Path 1: Products [J^n, Type] - Cubical Approach**

- J × J has 4² = 16 objects
- J × J × J has 4³ = 64 objects
- J^n has 4^n objects (exponential growth)
- Structure: n orthogonal copies of the J structure

**Path 2: Hierarchy [J_n, Type] - Globular Approach**

- J_n has O(n) objects (linear growth)
- Objects for k-cells at each level k = 0, 1, ..., n
- Source/target maps between adjacent levels
- Matches the standard globular definition of n-category

### The Cubical Path: [J^n, Type]

For [J × J, Type], the 16 objects can be interpreted as:

|First factor|Second factor|Interpretation|
|---|---|---|
|Obj|Obj|0-cells|
|Mor|Obj|Horizontal 1-cells|
|Obj|Mor|Vertical 1-cells|
|Mor|Mor|2-cells|
|Id|*|Horizontal identity data|
|*|Id|Vertical identity data|
|Comp|*|Horizontal composition data|
|*|Comp|Vertical composition data|

This structure is natural for DOUBLE CATEGORIES, which have:

- Two orthogonal category structures (horizontal and vertical)
- 2-cells filling squares
- Interchange law relating the two compositions

The product [J × J, Type] may embed double categories rather than globular
2-categories.

### The Globular Path: [J_n, Type]

For globular n-categories, define J_n with:

**Objects:**

- Obj_k for k = 0, 1, ..., n (k-cells)
- Id_k for k = 0, 1, ..., n (identity witnesses)
- Comp_k for k = 1, ..., n (composition witnesses)
- Exch_k for k = 2, ..., n (interchange witnesses)

**Morphisms:**

- source_k, target_k : Obj_k → Obj_{k-1} for k > 0
- Globularity: source_{k-1} ∘ source_k = source_{k-1} ∘ target_k
- Globularity: target_{k-1} ∘ source_k = target_{k-1} ∘ target_k
- Identity and composition witness projections

This gives approximately 4n objects for n-categories.

### Relationship to Simplicial Sets

The standard approach to ∞-categories uses simplicial sets [Δ^op, Set] where
Δ is the simplex category with:

- Objects: [n] = {0, 1, ..., n} for n ≥ 0
- Morphisms: order-preserving maps

Comparing approaches:

|Approach|Index category|Object count|Geometric flavor|
|---|---|---|---|
|[J^n, Type]|J^n (product)|4^n|Cubical|
|[J_n, Type]|J_n (hierarchy)|O(n)|Globular|
|[Δ^op, Set]|Δ|Infinite|Simplicial|

**Observations:**

- J^ω = colim_n J^n would be infinite with cubical structure
- J_ω (infinite hierarchy) is closer to the globe category
- Neither is precisely Δ, but J_ω may be a finite presentation thereof

### The n = 2 Case in Detail

For 2-categories, the correspondence depends on which path we take:

**Cubical (J × J):**

A copresheaf X : J × J → Type encodes:

- X(Obj, Obj) = 0-cells
- X(Mor, Obj) = horizontal 1-cells with dom/cod in X(Obj, Obj)
- X(Obj, Mor) = vertical 1-cells with dom/cod in X(Obj, Obj)
- X(Mor, Mor) = 2-cells with horizontal and vertical boundaries

The embedding Φ₂ : 2-Cat → [J × J, Type] would identify horizontal and
vertical morphisms (since in a 2-category, there is only one kind of 1-cell).

**Globular (J_2):**

A copresheaf X : J_2 → Type encodes:

- X(Obj_0) = 0-cells
- X(Obj_1) = 1-cells
- X(Obj_2) = 2-cells
- Source and target maps at each level
- Composition and identity data

This directly matches the standard definition of (strict) 2-category.

### Natural Transformations and C × J

For natural transformations between functors F, G : C → Cat:

1. By embedding: F, G become F', G' : C → [J, Type]
2. Natural transformations F ⇒ G correspond to F' ⇒ G'
3. By currying: both F' and G' correspond to copresheaves on C × J

The natural transformation data appears as additional structure relating
the two copresheaves on C × J.

### Conclusions

1. **[J × J, Type] for 2-categories**: Works, but naturally encodes double
   categories; globular 2-categories require identifying horizontal = vertical

2. **[J^n, Type] for n-categories**: Encodes cubical n-categories with
   exponential object count

3. **[J_n, Type] for globular n-categories**: More natural encoding with
   linear object count

4. **[J^ω, Type] or [J_ω, Type] for ∞-categories**: Both are possible; J_ω
   is closer to standard approaches via globular sets or simplicial sets

## References

- Johnson, N., & Yau, D. (2020). 2-Dimensional Categories.
- Lurie, J. Higher Topos Theory.
- nLab: n-category, simplicial set
