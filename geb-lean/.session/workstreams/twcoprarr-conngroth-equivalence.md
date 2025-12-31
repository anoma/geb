# TwCoprArrElem ↔ ConnGrothendieck Equivalence

## Goal

Prove that `TwCoprArrElem F` is categorically equivalent to
`ConnGrothendieck (F ⋙ typeToCat)` for `F : TwistedArrow' C ⥤ Type u`.

This establishes that the category of elements for a twisted arrow
copresheaf (over Arrow C) is the same as the connected Grothendieck
construction applied to the composition with `typeToCat`.

## Location

All code is in `GebLean/Paranatural.lean` in the section
`ConnGrothendieckEquiv` (starting around line 1633).

## Universe Constraints

The equivalence requires `v = u` (same universe for morphisms and objects)
because `typeToCat : Type u ⥤ Cat.{u, u}` produces categories where both
universe parameters are `u`.

## Completed Work

### 1. Object Correspondence

Defined bijection between objects:

```lean
def twCoprArrElemToConnGrothendieckObj (x : TwCoprArrElem F) :
    ConnGrothendieckObj C (typeToCatF F)

def connGrothendieckObjToTwCoprArrElem
    (x : ConnGrothendieckObj C (typeToCatF F)) : TwCoprArrElem F

def twCoprArrElemObjEquiv :
    TwCoprArrElem F ≃ ConnGrothendieckObj C (typeToCatF F)
```

Round-trip lemmas prove these are inverses:

- `connGrothendieckObj_roundtrip`
- `twCoprArrElemObj_roundtrip`

### 2. Morphism Correspondence Lemmas

Established relationships between twisted arrow morphisms:

```lean
lemma connGrothendieckDiagCod_eq_arrDiagTw
lemma connGrothendieckTwMorphCod_eq_arrToDiagFromSource
lemma connGrothendieckTwMorphDom_eq_arrToDiagFromTarget
```

These show:

- `connGrothendieckTwMorphCod` equals `arrToDiagFromSource` (up to eqToHom)
- `connGrothendieckTwMorphDom` equals `arrToDiagFromTarget` (up to eqToHom)

### 3. Fiber Correspondence (In Progress)

Started defining fiber source/target for discrete categories:

```lean
def twCoprArrElemFiberSource  -- fiber transported via codomain arrow
def twCoprArrElemFiberTarget  -- fiber transported via domain arrow
lemma twCoprArrElemFiber_eq   -- equality via TwArrCompat (has errors)
```

## Current Errors

The `twCoprArrElemFiber_eq` lemma has build errors:

1. **Parameter order issue**: The definitions use `F` implicitly from
   `TwCoprArrElem F`, but the lemma tries to pass `C` and `F` explicitly
   in the wrong positions.

2. **Missing lemma**: `connGrothendieckDiagEq'` doesn't exist. Need to use
   `connGrothendieckDiagEq` from ConnectedGrothendieck.lean, which takes
   `ConnGrothendieckObj` arguments rather than raw arrows. Will need to
   adapt or create a version for raw Arrow morphisms.

## Remaining Work

### 1. Fix Fiber Equality Lemma

Need to fix `twCoprArrElemFiber_eq` by:

- Correcting parameter order in function calls
- Using correct diagonal equality lemma (may need to define
  `connGrothendieckDiagEq'` for Arrow morphisms, or adapt existing lemma)

### 2. Define Functor TwCoprArrElem → ConnGrothendieck

```lean
def twCoprArrElemToConnGrothendieck :
    TwCoprArrElem F ⥤ ConnGrothendieck (typeToCatF F)
```

Object map: `twCoprArrElemToConnGrothendieckObj`

Morphism map needs `ConnGrothendieckHom` with:

- `domArr = f.base.left`
- `codArr = f.base.right`
- `square_comm` from Arrow morphism `f.base.w`
- `fiberMorph` = identity (via `eqToHom`) since fibers are discrete

For discrete categories, `fiberMorph` is just `eqToHom` witnessing that
the transported fibers are equal, which follows from `TwArrCompat`.

### 3. Define Inverse Functor

```lean
def connGrothendieckToTwCoprArrElem :
    ConnGrothendieck (typeToCatF F) ⥤ TwCoprArrElem F
```

### 4. Prove Categorical Equivalence

Show the functors form an equivalence:

- Unit natural isomorphism
- Counit natural isomorphism

## Technical Notes

### TwArrCompat Condition

For `TwCoprArrElem.Hom`, the `compat` field states:

```lean
F.map (arrToDiagFromSource φ) e₁ = F.map (arrToDiagFromTarget φ) e₂
```

This corresponds exactly to the fiber compatibility needed for
`ConnGrothendieckHom` when fibers are discrete (only identity morphisms).

### Discrete Category Simplification

Since `typeToCat X = Cat.of (Discrete X)`, morphisms in fibers are just
identities. This means `fiberMorph` in `ConnGrothendieckHom` is always
an `eqToHom`, and the equality it witnesses comes from `TwArrCompat`.

### Relevant Definitions from ConnectedGrothendieck.lean

- `ConnGrothendieckObj`: object with `arrow` and `fiber` fields
- `ConnGrothendieckHom`: morphism with `domArr`, `codArr`, `square_comm`,
  `fiberMorph`
- `connGrothendieckDiagCod/Dom`: the diagonal twisted arrows
- `connGrothendieckTwMorphCod/Dom`: twisted arrow morphisms to diagonal
- `connGrothendieckDiagEq`: equality between two diagonal representations

## Dependencies

- `GebLean/Utilities/ConnectedGrothendieck.lean` - ConnGrothendieck
- `Mathlib.CategoryTheory.Category.Cat` - `typeToCat` functor
- `GebLean/Paranatural.lean` - TwCoprArrElem, TwArrCompat, arr/tw conversions
