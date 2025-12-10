# Workstream: Connected Grothendieck Construction

## Status

In Progress - Category structure defined, associativity proof has a sorry

## Context

The connected Grothendieck construction defines a functor
`E : Fun(Tw(C), Cat) -> Cat/Arr(C)` that assigns to each functor
`F : TwistedArrow C -> Cat` a category `E(F)` over the arrow category.

See `docs/connected-grothendieck-construction.md` for the mathematical
specification.

## Implementation

File: `GebLean/Utilities/ConnectedGrothendieck.lean`

### Completed

1. Object type `ConnGrothendieckObj` - pairs (arrow, fiber element)
2. Morphism type `ConnGrothendieckHom` - arrow squares with fiber morphisms
3. Diagonal constructions `W1`, `W2`, `W3`, `W4` for composition
4. Transport morphisms `morphW1W3`, `morphW2W3` for fiber transport
5. Transport morphisms `morphW1W4`, `morphW2W4` for triple composition
6. Composition operation `connGrothendieckComp`
7. Identity operation `connGrothendieckId`
8. Extensionality lemma `connGrothendieckHom_ext`
9. Left identity proof `connGrothendieckId_comp`
10. Right identity proof `connGrothendieckComp_id`
11. Helper lemmas for identity laws using HEq peeling technique
12. Coherence lemmas for associativity:
    - `connGrothendieckMorphW1W3_comp_left` - LHS path for f.fiberMorph
    - `connGrothendieckMorphW1W3_comp_right` - RHS path for f.fiberMorph
    - `connGrothendieckMorphW2W3_comp_left` - LHS path for h.fiberMorph
    - `connGrothendieckMorphW2W3_comp_right` - RHS path for h.fiberMorph
    - `connGrothendieckMorphMiddle_coherence` - middle coherence for g.fiberMorph
13. Projection functor `connGrothendieckProjection : E(F) => Arrow C`
14. Object over Arrow C: `connGrothendieckOver : Over (Cat.of (Arrow C))`

### Remaining

1. Associativity proof `connGrothendieckComp_assoc` - has a sorry

   The fiber HEq goal requires showing that two different orderings of
   fiber morphism composition via transport functors are HEq.

   **Structure of the problem:**
   - LHS: `((f >> g) >> h).fiberMorph` expands to transport of `(f>>g).fiberMorph`
     followed by `h.fiberMorph`
   - RHS: `(f >> (g >> h)).fiberMorph` expands to `f.fiberMorph` followed by
     transport of `(g>>h).fiberMorph`

   **Type mismatch:**
   - LHS is in `F(DiagCod w.arrow ((f.codArr >> g.codArr) >> h.codArr))`
   - RHS is in `F(DiagCod w.arrow (f.codArr >> g.codArr >> h.codArr))`
   - These types differ only by `Category.assoc`

   **Available coherence infrastructure:**
   - `connGrothendieckW3_assoc` - W3((f>>g), h) = W3(f, (g>>h))
   - `connGrothendieckW3_comp_left_eq_W4` - W3((f>>g), h) = W4
   - `connGrothendieckW3_comp_right_eq_W4` - W3(f, (g>>h)) = W4
   - `connGrothendieckMorphW1W3_comp_left/right` - f transport paths equal
   - `connGrothendieckMorphW2W3_comp_left/right` - h transport paths equal
   - `connGrothendieckMorphMiddle_coherence` - g transport paths equal

   **Technical challenge:**
   The goal after `simp only [connGrothendieckComp]` is a deeply nested HEq
   between compositions involving:
   - Multiple `eqToHom` terms
   - Functor maps `F.map(morphW1W3(...)).map(...)` with different arguments
   - Nested fiberMorph chains from the inner compositions

   **Key insight:**
   The `morphW1W3` and `morphW2W3` twisted arrow morphisms only depend on
   `domArr` and `codArr` components, not on `fiberMorph`. This means:
   - `morphW1W3({domArr := a, codArr := c, fiberMorph := φ}, n)` equals
     `morphW1W3({domArr := a, codArr := c, fiberMorph := ψ}, n)` for any φ, ψ
   - Both sides ultimately transport f.fiberMorph, g.fiberMorph, h.fiberMorph
     to F(W4) via different intermediate paths that are equal by coherence

   **Attempted approaches:**
   1. HEq peeling with `comp_eqToHom_heq` - works but goal remains complex
   2. `heq_of_cast_eq` with type equality proof - type goals become complex
   3. `Functor.map_comp` distribution - increases goal complexity
   4. Direct `native_decide` - fails due to free variables
   5. Defining `morphW1W3_irrel_fiberMorph` lemmas - type mismatches with
      anonymous structure fields
   6. Defining `morphW1W3_eq_of_eq` lemmas - proof obligations fail to unify

   **Root cause:**
   The fundamental difficulty is that morphW1W3/morphW2W3 appear in the goal
   with **anonymous structure arguments** like:
   ```
   { domArr := f.domArr ≫ g.domArr, codArr := f.codArr ≫ g.codArr,
     square_comm := ⋯, fiberMorph := ⟨complex nested term⟩ }
   ```
   These do not unify with `connGrothendieckComp C F f g` even though they are
   definitionally equal, because Lean sees the structure fields explicitly.

   This means lemmas like `morphW1W3 (connGrothendieckComp f g) h = ...` cannot
   be applied directly via `rw` since the goal has the expanded form.

   **Possible solutions:**
   1. Use `change` or `show` to coerce the goal to use named terms
   2. Define simp lemmas that match the anonymous structure pattern
   3. Use `congr_arg` with explicit structure equality proofs
   4. Define a specialized HEq lemma for the exact goal structure

   **Mathematical validity:**
   The theorem is mathematically valid by standard coherence for
   lax/oplax functors. The proof would be routine in a proof assistant
   with better support for heterogeneous equality over dependent types.

2. Functoriality in `F` - showing `E` is a functor `Fun(Tw(C), Cat) -> Cat/Arr(C)`

## Technical Notes

### HEq Proof Technique

For proving fiber morphism HEq, the following pattern works:

1. Left-associate using `conv_lhs => rw [<- Category.assoc, ...]`
2. Peel trailing eqToHom using `apply HEq.trans (comp_eqToHom_heq _ _)`
3. Simplify inner structure with `simp only [connGrothendieckId, eqToHom_map]`
4. Peel leading eqToHom using `apply HEq.trans; apply eqToHom_comp_heq`
5. Use `change` to fold back unfolded definitions
6. Rewrite with identity lemmas like `connGrothendieckMorphW1W3_id_right`
7. Finish with `Cat.eqToHom_map_heq`

### Key Lemmas (Identity Laws)

- `connGrothendieckMorphW2W3_id_left` - morphW2W3(id, m) = eqToHom
- `connGrothendieckMorphW1W3_id_right` - morphW1W3(m, id) = eqToHom
- `connGrothendieckW3_id_left` - W3(id, m) = W1(m)
- `connGrothendieckW3_id_right` - W3(m, id) = W1(m)
- `Cat.eqToHom_map_heq` - (eqToHom h).map f ~~~ f

### Key Lemmas (Associativity)

- `connGrothendieckW3_assoc` - W3((f>>g), h) = W3(f, (g>>h))
- `connGrothendieckW1_comp` - W1(f>>g) = W3(f, g)
- `connGrothendieckW3_comp_left_eq_W4` - W3((f>>g), h) = W4
- `connGrothendieckW3_comp_right_eq_W4` - W3(f, (g>>h)) = W4
- `connGrothendieckMorphW1W3_comp_left` - morphW1W3(f,g) >> ... = morphW1W4
- `connGrothendieckMorphW1W3_comp_right` - morphW1W3(f,(g>>h)) >> eqToHom = morphW1W4
- `connGrothendieckMorphW2W3_comp_left` - morphW2W3((f>>g),h) >> eqToHom = morphW2W4
- `connGrothendieckMorphW2W3_comp_right` - morphW2W3(g,h) >> ... = morphW2W4
- `connGrothendieckMorphMiddle_coherence` - LHS g-path = RHS g-path

## References

- `docs/connected-grothendieck-construction.md` - Mathematical specification
- `GebLean/Utilities/Grothendieck.lean` - Standard Grothendieck construction
- `GebLean/Utilities/TwistedArrow.lean` - Twisted arrow category definitions
