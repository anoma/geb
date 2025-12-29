# Higher Categorical Structure via J^n

## Status: Active Research

## The Question

Does [J^n, Type] provide a natural home for n-categorical structure?

## Observations

- [J, Type] embeds Cat (1-categories)
- [J², Type] may embed 2-Cat
- Pattern: [J^n, Type] for n-Cat?
- Limit: [J^ω, Type] for ω-Cat?

## Findings

### Two Paths to Higher Categories

1. **Cubical Path [J^n, Type]**: Products give 4^n objects with orthogonal
   composition directions. Natural for DOUBLE categories and cubical structures.

2. **Globular Path [J_n, Type]**: Hierarchy gives O(n) objects with source/target
   maps between levels. Natural for standard globular n-categories.

### [J × J, Type] Structure

The 16 objects of J × J naturally encode double category structure:

- (Obj, Obj) = 0-cells
- (Mor, Obj) = horizontal 1-cells
- (Obj, Mor) = vertical 1-cells
- (Mor, Mor) = 2-cells

For globular 2-categories, must identify horizontal = vertical.

### Natural Transformations

For F, G : C → Cat, natural transformations F ⇒ G correspond to structure
relating two copresheaves on C × J (after embedding and currying).

### Relationship to Δ

- J^ω (cubical limit) is infinite with cubical flavor
- J_ω (globular limit) is closer to the globe category
- Neither is precisely Δ, but J_ω may be a finite presentation

## Sub-Questions (Resolved)

1. Natural transformations ↔ [C × J, Type]: Confirmed via currying
2. [J × J, Type] structure: Double categories; 16 objects
3. J^n growth: Confirmed 4^n objects (exponential)
4. J^ω notion: Two choices - cubical (colimit) or globular (hierarchy limit)
5. Relation to Δ: Different geometric flavor; J_ω is closer

## Code References

- `GebLean/CategoryJudgments.lean` - Definition of J

## External References

- Simplicial sets and Δ
- n-categories and ω-categories
- Grothendieck's homotopy hypothesis
