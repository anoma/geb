# PshRel Subobject Refactoring

## Motivation

`PshRel P Q` is the type of relations from presheaf `P` to presheaf
`Q` in `PSh(C)`.  It is used throughout the presheaf relation double
category (`PshRelDouble.lean`), the Yoneda relation double category
(`YonedaRelDouble.lean`), and the parametricity infrastructure
(`PshTypeExpr.lean`, `ParanaturalTopos.lean`).

The current definition is `Skeleton (PshProdOver P Q)`, i.e.,
isomorphism classes of objects in `Over (P x Q)`.  This quotients
spans by isomorphism of the total space, but does not quotient
further to the image (subobject) level.

Making `TypeExpr.profRelInterp` into a functor on `TypeRelCat`
requires the subobject-level quotient, because:

- The arrow relation (`pshArrowRelSkel`) and Barr extension
  (`pshBarrLiftSkel`) produce mono spans (subobjects).
- Their composition laws hold at the subobject level (where
  composition is existential quantification over the intermediate
  element) but not at the span-iso-class level (where composition
  retains fiber multiplicity).
- All relational interpretations (`fullRelInterp`, `biRelInterp`,
  `profRelInterp`) are `Prop`-valued and insensitive to fiber
  multiplicity.

## Design

### New definition of `PshRel`

Replace:

```lean
abbrev PshRel (P Q : Cop => Type w) :=
  Skeleton (PshProdOver P Q)
```

with:

```lean
abbrev PshRel (P Q : Cop => Type w) :=
  Subfunctor (pshProdPresheaf P Q)
```

where `Subfunctor` is mathlib's `CategoryTheory.Subfunctor`
(in `Mathlib.CategoryTheory.Subfunctor.Basic`), the type of
subfunctors of a `Type w`-valued functor.  A `Subfunctor F`
consists of:

- `obj : forall U, Set (F.obj U)` -- a family of subsets
- `map : forall {U V} (i : U -> V), obj U <= F.map i ^-1 obj V`
  -- closure under the functorial action

For `F = pshProdPresheaf P Q`, an element of `PshRel P Q` is a
family of subsets of `P(c) x Q(c)` closed under restriction -- a
subpresheaf of `P x Q`.

`Subfunctor` provides:

- `@[ext]` (two subfunctors are equal iff they agree pointwise)
- `CompleteLattice` instance (meets, joins, etc.)
- `toFunctor` (the underlying presheaf of the subobject)
- `ι` (the inclusion mono `G.toFunctor -> F`)
- `range` (image of a natural transformation)
- `lift` (factoring through a subfunctor)

### Composition

```lean
def pshRelComp (R : PshRel P Q) (S : PshRel Q W) :
    PshRel P W where
  obj c := { pw : P.obj c x W.obj c |
    exists q : Q.obj c,
      (pw.1, q) in R.obj c and (q, pw.2) in S.obj c }
  map f _ <q, hr, hs> :=
    <Q.map f q, R.map f hr, S.map f hs>
```

### Identity

```lean
def pshRelId (P : Cop => Type w) : PshRel P P where
  obj c := { pp | pp.1 = pp.2 }
  map f _ h := congrArg (P.map f) h
```

### Graph

```lean
def pshRelGraph (alpha : P -> Q) : PshRel P Q where
  obj c := { pq | alpha.app c pq.1 = pq.2 }
  map f _ h := ...  -- from naturality of alpha
```

### Dagger

```lean
def pshRelDagger (R : PshRel P Q) : PshRel Q P where
  obj c := { qp | (qp.2, qp.1) in R.obj c }
  map f _ h := R.map f h
```

### Relatedness (double category squares)

```lean
def pshRelRelated (alpha : P -> Q) (beta : P' -> Q')
    (R : PshRel P P') (S : PshRel Q Q') : Prop :=
  forall (c : Cop) (p : P.obj c) (p' : P'.obj c),
    (p, p') in R.obj c ->
    (alpha.app c p, beta.app c p') in S.obj c
```

### Barr extension

```lean
def pshBarrLiftSkel
    (G : PSh(C) => PSh(C)) (R : PshRel P Q) :
    PshRel (G.obj P) (G.obj Q) :=
  Subfunctor.range (pshBarrLift G R.toFunctor R.ι).hom
```

where `pshBarrLift` applies `G` to the span `R.toFunctor`
(the underlying presheaf of the subfunctor) with projections
obtained from `R.ι` composed with product projections.
The image (`Subfunctor.range`) of the resulting span is the
subobject-level Barr extension.

### Arrow relation

The arrow relation `pshArrowRelSkel R S` is defined by the
predicate `pshArrowRelPred`, which is already propositional
(it quantifies over witnesses existentially).  For the new
definition, `pshArrowRelPred` takes membership predicates from
`R.obj` and `S.obj` directly, producing a `Subfunctor` of the
internal-hom product.

### Projection from PshProdOver

```lean
def pshProdOverToRel (R : PshProdOver P Q) :
    PshRel P Q :=
  Subfunctor.range R.hom
```

This maps a span `R -> P x Q` to its image subfunctor.  Isomorphic
spans have equal images, so this factors through the old skeleton:

```lean
theorem pshProdOverToRel_iso_eq (alpha : R1 ~= R2) :
    pshProdOverToRel R1 = pshProdOverToRel R2
```

### Category laws

- **Associativity**: `pshRelComp (pshRelComp R S) T =
  pshRelComp R (pshRelComp S T)` follows from `Subfunctor.ext`
  plus propositional logic (associativity of existential
  quantification).
- **Left identity**: `pshRelComp (pshRelId P) R = R` follows from
  substituting the equality witness.
- **Right identity**: `pshRelComp R (pshRelId Q) = R` likewise.

These proofs are direct propositional reasoning, using
`Subfunctor.ext` (or `Set.ext` pointwise) to reduce to
membership equivalences.

### PshProdOver as internal proof infrastructure

`PshProdOver`, `pshProdOverComp`, and the associated isomorphisms
(`pshProdOverComp_assoc`, `pshProdOverComp_id_left`, etc.) are
retained as internal definitions.  They serve as proof tools:

- `pshBarrLift` is naturally defined at the span level (apply
  `G` to the total space), then projected to `PshRel` via
  `Subfunctor.range`.
- `pshArrowRel` is naturally defined at the span level (the
  subtype presheaf), which happens to already be mono, so its
  image equals itself.
- Properties like `pshBarrLiftSkel_graph` and
  `pshRelGraph_comp` can be proved by constructing span-level
  witnesses and projecting.

### Downstream changes

**YonedaRelDouble.lean**: `YonedaRel X Y` changes from
`Skeleton (YonedaProdOver X Y)` to
`Subfunctor (yonedaProdPresheaf X Y)` (or equivalently,
`PshRel (yoneda.obj X) (yoneda.obj Y)`).  All operations
(`relComp`, `relId`, `relGraph`, `relRelated`) adapt by the
same pattern as `PshRel`.

**PshTypeExpr.lean**: Uses `PshRel`, `pshBarrLiftSkel`,
`pshArrowRelSkel`, `pshRelGraph`.  The API is unchanged;
only the internal representation differs.

**ParanaturalTopos.lean**: Light usage of `toSkeleton` and
`pshRelRelated`.  Adapts to the new `PshRel` definition.

**TypeRelCat specialization**: `TypeRel A B` becomes
`Subfunctor (pshProdPresheaf (typeToPsh.obj A) (typeToPsh.obj B))`.
For `C = Discrete PUnit`, this is a subset of `A x B`, i.e.,
`A -> B -> Prop` (up to currying).

### What is removed

- `Skeleton`-based `PshRel` definition
- `Skeleton.lift` / `Skeleton.lift₂` usage in `pshRelComp`,
  `pshRelRelated`, `pshRelDagger`, `pshBarrLiftSkel`,
  `pshArrowRelSkel`
- `pshProdOverComp_iso` (no longer needed for well-definedness
  of composition)
- `Quotient.inductionOn` patterns in category-law proofs

The `Skeleton` module itself is retained (used by
`Polynomial.lean` and `ParamPoly.lean`).

### What is added

- Import of `Mathlib.CategoryTheory.Subfunctor.Basic` (and
  possibly `Subfunctor.Image` for `Subfunctor.range`)
- `pshProdOverToRel : PshProdOver P Q -> PshRel P Q` projection
- Adapted definitions and proofs for all `PshRel` operations
