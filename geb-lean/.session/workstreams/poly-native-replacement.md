# Workstream: Replace Native Lean Types with Polynomial Versions

## Status

Active

## Context

Several types in `GebLean/PolyAlg.lean` are defined using Lean's native
type-forming mechanisms (inductive types, structures, recursive defs
producing types) rather than as polynomial fixed points (`PolyFix`).
The goal is to define isomorphic polynomial versions of each and
eventually replace the Lean versions entirely, so that `PolyFix` is the
sole use of Lean's native inductive types in our type system.

The M-type construction (`PolyCofix`) is built from `PolyCofixApprox`
(finite-depth approximations) and `PolyCofixAgree` (consistency between
levels), following the approach described in
`docs/m-types-from-w-types-walkthrough.md`.  The cofree comonad
annotations use `PolyCofreeAnnotPosAt` (and its variant
`PolyCofreeAnnotPosAtM`) to describe positions in M-type trees.
The free monad uses `PolyFreeMLeafPos` for leaf positions in tree
shapes.

The procedure for each type is:

1. Identify the base type `B` that the type family is indexed over.
   When a type has multiple indices (e.g. `Nat → X → Type`),
   uncurry to a single index type (e.g. `Nat × X`).  The
   equivalence `familySliceEquiv` (in `Polynomial.lean`) witnesses
   that families of types over `B` correspond to objects of
   `Over B`.
2. Define a `PolyEndo B` whose constructors at each base point
   match those of the Lean type.  Each constructor becomes a
   position (index) of the polynomial; each recursive argument
   becomes a child in the family.  Non-recursive types use empty
   families.
3. Prove `PolyFix` of that `PolyEndo` is isomorphic to the Lean
   type.
4. Replace all uses of the Lean type with the `PolyFix` version
   and remove the Lean type.

For `Prop`-valued types, produce a `Type`-valued `PolyFix` and
quotient by `trueSetoid` to obtain a subsingleton, then show
logical equivalence with the `Prop` version.

The detailed plan with polynomial definitions is in
`docs/plans/2026-03-07-poly-native-replacement.md`.

For each type below, the work has two phases:

1. Define a `PolyEndo` whose `PolyFix` is isomorphic to the Lean
   version, and prove the isomorphism.
2. Replace all uses of the Lean version with the polynomial version
   and remove the Lean version.

## Types to Replace

### M-type construction types

These three types together constitute the M-type construction.
`PolyCofixApprox` and `PolyCofixAgree` are the structural components;
`PolyCofix` combines them.

#### PolyCofixApprox (line 645)

Lean inductive indexed by `Nat × X`.  At depth 0, a single trivial
constructor `continue`.  At depth `n + 1`, a constructor `intro`
carrying an index `i : polyBetweenIndex X X P x` and children
`∀ e, PolyCofixApprox P n (fiber e)`.

This is a W-type over the base `Nat × X`.  The polynomial
`P_approx : PolyEndo (Nat × X)` would have:

- At `(0, x)`: one position (unit index), empty family (no children).
- At `(n + 1, x)`: positions are `polyBetweenIndex X X P x`;
  at position `i`, the children are indexed by
  `(polyBetweenFamily X X P x i).left`, each mapping to
  `(n, (polyBetweenFamily X X P x i).hom e)`.

- [ ] Polynomial version defined and proven isomorphic
- [ ] Lean version replaced and removed

#### PolyCofixAgree (line 677)

Lean inductive producing `Prop`, indexed by `n`, `x`, and two
approximations at depths `n` and `n + 1`.  Two constructors:
`continue` (any depth-0 approximation agrees with any depth-1
approximation) and `intro` (two intro nodes agree when they have
the same index and all children agree).

This is `Prop`-valued, so expressing it as a `PolyFix` (which produces
`Type u`) requires care.  One approach: define a `Type`-valued version
as a `PolyFix` (which will be a subsingleton by construction) and
then show it is logically equivalent to the `Prop`-valued version.
Alternatively, define it as a predicate on the polynomial version
of `PolyCofixApprox`.

- [ ] Polynomial version defined and proven isomorphic
- [ ] Lean version replaced and removed

#### PolyCofix (line 783)

Lean structure combining `approx : ∀ n, PolyCofixApprox P n x` and
`consistent : ∀ n, PolyCofixAgree P (approx n) (approx (n + 1))`.

This is a dependent record (sigma type), not an inductive type.  It
cannot be directly expressed as a `PolyFix` because it involves an
infinite product (`∀ n`).  Once `PolyCofixApprox` and `PolyCofixAgree`
have polynomial versions, `PolyCofix` should be redefined in terms
of those polynomial versions (keeping the same structure-of-sequences
form, but with polynomial components).

- [ ] Polynomial version defined and proven isomorphic
- [ ] Lean version replaced and removed

### Cofree comonad annotation types

These types describe positions and fibers in cofree comonad
(M-type) trees, used for the polynomial representation of the
cofree comonad.

#### PolyCofreeAnnotPosAt (line 3989)

Recursive def producing `Type u`, indexed by a shape
`s : PolyCofreeShape P x` and a depth `n : Nat`.  At depth 0,
`PUnit`.  At depth `n + 1`, `Σ (e : children_index), rec (s.children e) n`.

This computes the type of paths of length `n` from the root of the
shape tree `s`.  It can be expressed as a `PolyFix` over a base type
that tracks both the current node in the shape and the remaining
depth.

- [ ] Polynomial version defined and proven isomorphic
- [ ] Lean version replaced and removed

#### PolyCofreeAnnotPosAtM (line 4273)

Variant of `PolyCofreeAnnotPosAt` operating on
`PolyCofreeM A P x` (for arbitrary `A`) rather than
`PolyCofreeShape P x` (which specializes `A` to
`overTerminal X`).  Same recursive structure.

- [ ] Polynomial version defined and proven isomorphic
- [ ] Lean version replaced and removed

### Free monad leaf position type

#### PolyFreeMLeafPos (line 3612)

Recursive def producing `Type u`, defined by structural recursion
on a `PolyFreeMShape P x` (a W-type term).  At a leaf node
(`Sum.inl`), `PUnit`.  At an internal node (`Sum.inr p`), a sigma
of a child index and a recursive call on that child.

This computes the leaf positions of a free monad tree shape.  It
can be expressed as a `PolyFix` over a base type that tracks the
current subtree of the shape.

- [ ] Polynomial version defined and proven isomorphic
- [ ] Lean version replaced and removed

### Path segment type

#### PolyCofreePathSeg (line 3979)

Lean structure with three fields: `fiber : X`,
`idx : polyBetweenIndex X X P fiber`, and
`childIdx : (polyBetweenFamily X X P fiber idx).left`.

This is a non-recursive product type (a sigma type).  It can be
expressed as a degenerate polynomial with the appropriate index
type and an empty family (no recursive children), making
`PolyFix` of that polynomial isomorphic to the sigma type.

- [ ] Polynomial version defined and proven isomorphic
- [ ] Lean version replaced and removed

## Prop-valued Types and Subsingleton Quotients

`PolyCofixAgree` is `Prop`-valued, while `PolyFix` produces `Type u`.
To obtain a subsingleton `Type`-valued version, quotient by
`trueSetoid`.  References for this technique:

- `Quotient.trueSetoid_subsingleton` in
  `GebLean/Utilities/SetoidCat.lean` (line 25): the instance
  showing that `Quotient trueSetoid` is a subsingleton for any type.
- `DepCategoryData.truncateWitnesses` in
  `GebLean/DepCategoryAdjunction.lean` (line 58): applies
  `trueSetoid` quotients to identity and composition witnesses,
  producing a `WitnessSubsingleton` version of a
  `DepCategoryData`.  The associated proofs
  (`truncateWitnesses_idSubsingleton`,
  `truncateWitnesses_compSubsingleton`,
  `truncateWitnesses_witnessSubsingleton`) demonstrate the
  pattern.
- `GebLean/Utilities/Skeleton.lean`: quotients by the existence
  of isomorphisms, with `Skeleton`, `toSkeleton`,
  `toSkeleton_eq_iff`, and `Skeleton.lift₂`.  Used in the
  horizontal category of `GebLean/Polynomial.lean` (line 3273
  onward) to quotient polynomial composition by isomorphism.

## Notes

- `PolyFix` itself (line 175) is excluded: it is our one permitted
  use of Lean's native inductive types, providing W-types to the
  system.
- The types `PolyFreeMLeafFiber` (line 3623),
  `PolyCofreeAnnotFiberAt` (line 4007), and
  `PolyCofreeAnnotFiberAtM` (line 4283) are recursive defs
  producing values (elements of `X`), not types.  They are
  structural companions of the type-producing defs above and
  will need corresponding updates when the types they operate
  on are replaced, but they are not themselves types requiring
  polynomial replacements.
- Several `abbrev` definitions (`PolyFreeM`, `PolyCofreeM`,
  `PolyFreeMShape`, `PolyCofreeShape`, `PolyFreeMPolyEval`,
  `PolyCofreePolyEval`) are defined in terms of `PolyFix` or
  `PolyCofix` and will be updated once their underlying types
  are polynomialized.
