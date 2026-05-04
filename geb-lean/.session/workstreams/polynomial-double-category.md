# Workstream: Polynomial Double Category

## Status

Complete (Phases 1-4)

## Context

The 2-category (bicategory) of polynomial functors, as described at
<https://ncatlab.org/nlab/show/polynomial+functor#the_2category_of_polynomial_functors>,
extends to a double category (and indeed a framed bicategory). This
workstream implements that double category in Lean, adapting from the
Idris-2 implementation in `.claude/docs/SlicePolyCat.idr` (see
`SPFpoDoubleCat`).

### Double category structure

Following the Idris code and the nCat Lab description:

- **Objects**: `Type u`
- **Vertical morphisms**: functions `X -> Y` (ordinary function
  composition, strictly associative/unital)
- **Horizontal morphisms**: polynomial functors, represented as
  elements of `PolyFunctorBetweenCat X Y` (arena/Grothendieck
  representation); for the strict double category laws, we use
  `PolyHorizontalHom X Y` (skeleton quotient)
- **2-cells (squares)**: given vertical morphisms `bcl : X -> X'` and
  `bcr : Y -> Y'` and horizontal morphisms `f : PolyFunctorBetweenCat
  X Y`, `g : PolyFunctorBetweenCat X' Y'`, a 2-cell is a natural
  transformation `SPFnt (polyPushout bcl bcr f) g`

The 2-cell definition uses `polyPushout`, the pushforward of a
polynomial along functions on domain and codomain. This corresponds to
`spfPushout` in the Idris code.

### Relationship to existing code

- `PolyBetweenCat X Y` (= `PolyFunctorBetweenCat X Y`) provides the
  morphism structure for 2-cells: when both vertical morphisms are
  identities, a 2-cell reduces to a morphism of `PolyBetweenCat`
  (natural transformation between polynomial functors).
- `PolyHorizontalCat` provides the horizontal edge category: objects
  are types, morphisms are isomorphism classes of polynomial functors
  with composition via `polyHorizComp`.
- `DoubleCategoryOps` / `DoubleCategoryLaws` / `DoubleCategoryData`
  from `GebLean/Utilities/DoubleCategory.lean` provide the framework.
- `YonedaRelDouble.lean` provides an example of instantiating
  `DoubleCategoryData`.

### Design decisions

Polynomial composition (`polyBetweenComp`) is only associative and
unital up to isomorphism (due to nested Sigma types). For a strict
`DoubleCategoryData`, horizontal morphisms use `PolyHorizontalHom`
(skeleton quotient), which is strictly associative. The 2-cell type
is `Prop`-valued (`Nonempty` of the concrete cell), making all square
laws hold by proof irrelevance/subsingleton elimination.

The concrete (`Type`-valued) 2-cell operations (vertical/horizontal
composition, identities) are defined separately on
`PolyFunctorBetweenCat` objects, preserving the mathematical content
for use outside the strict double category framework.

### Idris reference

The Idris implementation is in `.claude/docs/SlicePolyCat.idr`:

- `SPFpoCell` (line 2923): 2-cell definition via pushout
- `spocVid` (line 3033): vertical identity 2-cell
- `spocHid` (line 3041): horizontal identity 2-cell
- `spocVcomp` (line 3050): vertical composition of 2-cells
- `spocHcomp` (line 3112): horizontal composition of 2-cells
- `SPFpoDoubleCat` (line 3161): the assembled double category

## Tasks

### Phase 1: Pushout and 2-cell definitions

- [x] Define `polyPushout bcl bcr f` (pushforward of polynomial along
      domain/codomain functions); corresponds to `spfPushout` in Idris
- [x] Define `PolyCell bcl bcr f g` (2-cell as morphism from pushout
      to target); corresponds to `SPFpoCell`

### Phase 2: Concrete 2-cell operations

- [x] Define `polyCellVId f` (vertical identity: cell with both
      vertical morphisms = id); corresponds to `spocVid`
- [x] Define `polyCellHId bcw` (horizontal identity: cell with both
      horizontal morphisms = polyBetweenId); corresponds to `spocHid`
- [x] Define `polyCellVComp` (vertical composition of cells);
      corresponds to `spocVcomp`
- [x] Define `polyCellHComp` (horizontal composition of cells);
      corresponds to `spocHcomp`

### Phase 3: DoubleCategoryOps

- [x] Define the `Prop`-valued square type on `PolyHorizontalHom`
      (lifting through the skeleton quotient)
- [x] Define `polyDoubleOps : DoubleCategoryOps (Type u)
      (fun X Y => X -> Y) (fun X Y => PolyHorizontalHom X Y) sqs`

### Phase 4: DoubleCategoryLaws

- [x] Prove vertical category laws (functions: `rfl`)
- [x] Prove horizontal category laws (`polyHorizComp_assoc` etc.)
- [x] Prove square laws (`proof_irrel_heq` for HEq laws,
      `Subsingleton.elim` for Eq laws)
- [x] Assemble `polyDoubleData : DoubleCategoryData`

### Phase 5: Adjunction bijection (stretch goal)

- [ ] Show that a 2-cell defined as `SPFnt (Sigma . f . BaseChange
      bcl) g` (the Idris formulation) bijects with `SPFnt (Sigma . f)
      (g . Sigma bcr)` (natural transformation from `Sigma . f` to
      `g . Sigma`) via the sigma/base-change adjunction
- [ ] Formalize this as an equivalence of types

## Notes

### polyPushout construction

Given `bcl : X -> X'`, `bcr : Y -> Y'`, and `f : PolyFunctorBetweenCat X Y`:

`polyPushout bcl bcr f : PolyFunctorBetweenCat X' Y'` is defined at
each `y' : Y'` by:

- Index type: `Sigma (y : Y) (_ : bcr y = y'), ccrIndex (f y)`
- Family at `(y, _, i)`: `Over.mk (bcl . (ccrFamily (f y) i).hom)`

This pushes positions forward along `bcr` and post-composes fiber maps
with `bcl`.

### Factoring-out-lemmas technique

Per CLAUDE.md, proofs in these categories should use the
factoring-out-lemmas technique: break proofs into named lemmas of at
most five tactics each, compose via transitivity, and recurse on
difficult lemmas. The proofs in `PolyBetweenCat` and
`PolyHorizontalCat` provide examples of this pattern.

### Proof strategy for Prop-valued squares

With `Prop`-valued 2-cells (existentials over concrete cells), the
square laws split into two categories:

- **HEq laws** (sqVAssoc, sqHAssoc, sqVIdComp, sqVCompId, sqHIdComp,
  sqHCompId): Use `proof_irrel_heq _ _`, which establishes
  `HEq hp hq` for any proofs `hp : p` and `hq : q` of any two
  propositions, via propositional extensionality and proof
  irrelevance.
- **Eq laws** (interchange, vertIdVComp, horIdHComp, idOnId): Use
  `Subsingleton.elim _ _`, since both sides have the same type and
  `Prop` is a subsingleton.
