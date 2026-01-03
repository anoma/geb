# TwCoprArrElem ↔ ConnGrothendieck Equivalence

## Status

COMPLETED. The categorical equivalence is fully defined and compiles.

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

```lean
def twCoprArrElemToConnGrothendieckObj (x : TwCoprArrElem F) :
    ConnGrothendieckObj C (typeToCatF F)

def connGrothendieckObjToTwCoprArrElem
    (x : ConnGrothendieckObj C (typeToCatF F)) : TwCoprArrElem F

def twCoprArrElemObjEquiv :
    TwCoprArrElem F ≃ ConnGrothendieckObj C (typeToCatF F)
```

### 2. Forward Functor

```lean
def twCoprArrElemToConnGrothendieck :
    TwCoprArrElem F ⥤ ConnGrothendieck (typeToCatF F)
```

Maps morphisms to `ConnGrothendieckHom` with fiber morphisms as `eqToHom`.

### 3. Inverse Functor

```lean
def connGrothendieckToTwCoprArrElem :
    ConnGrothendieck (typeToCatF F) ⥤ TwCoprArrElem F
```

Maps `ConnGrothendieckHom` back to `TwCoprArrElem.Hom`.

### 4. Unit Natural Isomorphism

```lean
def twCoprArrConnGrothUnitIso :
    𝟭 (TwCoprArrElem F) ≅
      twCoprArrElemToConnGrothendieck F ⋙ connGrothendieckToTwCoprArrElem F
```

Components are `eqToIso` from the object round-trip equality.

### 5. Counit Natural Isomorphism

```lean
def twCoprArrConnGrothCounitIso :
    connGrothendieckToTwCoprArrElem F ⋙ twCoprArrElemToConnGrothendieck F ≅
      𝟭 (ConnGrothendieck (typeToCatF F))
```

Naturality proof uses `Grothendieck.ext` and `GrothendieckContra'.ext`.
The fiber case relies on `Discrete.instSubsingletonDiscreteHom` (discrete
categories have at most one morphism between any two objects).

### 6. Triangle Identities

```lean
lemma twCoprArrConnGroth_functor_unitIso_comp
lemma twCoprArrConnGroth_inverse_counitIso_comp
```

### 7. Equivalence Definition

```lean
def twCoprArrConnGrothEquiv :
    TwCoprArrElem F ≌ ConnGrothendieck (typeToCatF F)
```

## Technical Notes

### TwArrCompat Condition

For `TwCoprArrElem.Hom`, the `compat` field states:

```lean
F.map (arrToDiagFromSource φ) e₁ = F.map (arrToDiagFromTarget φ) e₂
```

This corresponds exactly to the fiber compatibility needed for
`ConnGrothendieckHom` when fibers are discrete.

### Discrete Category Simplification

Since `typeToCat X = Cat.of (Discrete X)`, morphisms in fibers are just
identities. This means `fiberMorph` in `ConnGrothendieckHom` is always
an `eqToHom`, and naturality for fiber morphisms follows from the
subsingleton property of discrete category hom-sets.

### Proof Techniques

The counit naturality proof uses:

- `grothendieckContra'_comp_base_left` to decompose compositions
- `fiberFunctorContra_map_base_left` to strip transition functor
- `GrothendieckContra'.base_eqToHom` and `Over.eqToHom_left` to
  transform `eqToHom` terms to the base category
- `conv` tactics to work around dependent type issues with `rw`
- `Discrete.instSubsingletonDiscreteHom` for fiber morphism equality

## Dependencies

- `GebLean/Utilities/ConnectedGrothendieck.lean` - ConnGrothendieck
- `Mathlib.CategoryTheory.Category.Cat` - `typeToCat` functor
- `GebLean/Paranatural.lean` - TwCoprArrElem, TwArrCompat, arr/tw conversions
