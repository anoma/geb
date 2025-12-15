# Reflective Subcategory Properties Investigation

## Status: Complete

Investigation of mathlib's reflective subcategory support and additional
properties of our Cat-Copresheaf adjunction.

## Background

We have established:

- `catCopresheafMathlibAdjunction : LFunctor ⊣ PhiFunctor`
- The counit is a natural isomorphism (`adjunctionCounit_isIso`)
- PhiFunctor is fully faithful (`phiFunctorFullyFaithful`)

This means we have a reflective adjunction, where `BundledOverCategoryData`
is a reflective subcategory of `FunctorData (Type u)`.

## Summary of Findings

### 1. Mathlib Reflective Subcategory Code

**Key Structures in `Mathlib.CategoryTheory.Adjunction.Reflective`:**

- `CategoryTheory.Reflective` class: A functor `R : D ⥤ C` is reflective when
  it is fully faithful and right adjoint. Fields:
  - `toFull : R.Full`
  - `toFaithful : R.Faithful`
  - `L : C ⥤ D` (the reflector/left adjoint)
  - `adj : L ⊣ R`

- `CategoryTheory.Coreflective` class: Dual - fully faithful left adjoint.

- `reflector` / `reflectorAdjunction`: Extract left adjoint from Reflective.

- `CategoryTheory.instIsRightAdjointOfReflective`: Instance showing a
  Reflective functor is a right adjoint.

- `CategoryTheory.Functor.fullyFaithfulOfReflective`: Get FullyFaithful from
  Reflective.

**Properties proven for Reflective functors:**

- The unit is an isomorphism when restricted to objects in the essential image
- `unitCompPartialBijective`: Precomposing with unit gives bijection on
  hom-sets when codomain is in essential image
- Reflective functors compose to give reflective functors
- A reflective functor induces an equivalence between D and the essential
  image subcategory of C

**Related files:**

- `Mathlib/CategoryTheory/Adjunction/Reflective.lean`
- `Mathlib/CategoryTheory/Monad/Adjunction.lean` (monadic properties)
- `Mathlib/CategoryTheory/Adjunction/FullyFaithful.lean`

### 2. Limit/Colimit Preservation (Implemented)

**Key theorems in `Mathlib.CategoryTheory.Adjunction.Limits`:**

- `CategoryTheory.Adjunction.rightAdjoint_preservesLimits`:
  For `adj : F ⊣ G`, we get `PreservesLimitsOfSize G`

- `CategoryTheory.Adjunction.leftAdjoint_preservesColimits`:
  For `adj : F ⊣ G`, we get `PreservesColimitsOfSize F`

**Instances added to CatJudgmentAdjunction.lean:**

```lean
instance phiFunctor_isRightAdjoint : PhiFunctor.IsRightAdjoint
instance lFunctor_isLeftAdjoint : LFunctor.IsLeftAdjoint
instance phiFunctor_reflective : Reflective PhiFunctor
instance phiFunctor_full : PhiFunctor.Full
instance phiFunctor_faithful : PhiFunctor.Faithful
```

The preservation instances are now automatically derived by mathlib:

- `PreservesLimitsOfShape J PhiFunctor` for any J
- `PreservesColimitsOfShape J LFunctor` for any J

### 3. Coproduct Preservation by Right Adjoint

**Analysis:**

From nLab: "a reflective subcategory is always closed under limits which
exist in the ambient category...and inherits colimits from the larger
category by application of the reflector."

This means:

- The subcategory (categories) inherits colimits from the ambient category
  (copresheaves) by first taking the colimit in copresheaves, then applying
  the reflector L
- The inclusion Φ does NOT preserve colimits in general

**Hypothesis for binary coproducts:**

PhiFunctor may preserve binary coproducts specifically because:

- For categories: the coproduct of C and D is their disjoint union
- For copresheaves: the coproduct is computed pointwise
- Φ(C ⊔ D) should equal Φ(C) ⊔ Φ(D) since disjoint union of categories maps
  to pointwise disjoint union of the represented copresheaves

**Status:** Conjectured, not proven. Would require constructing an explicit
isomorphism.

### 4. Product Preservation by Left Adjoint

**Analysis:**

From nLab: "If C is cartesian closed, and D ⊆ C is a reflective subcategory,
then the reflector L : C → D preserves finite products if and only if D is
an exponential ideal."

The category of copresheaves `[J, Type]` is cartesian closed (presheaf
categories have exponentials given by internal hom).

**Hypothesis:**

LFunctor may preserve binary products because:

- Products in copresheaf category are computed pointwise
- L(F × G) has objects (F × G)(Obj) = F(Obj) × G(Obj)
- L(F) × L(G) has objects F(Obj) × G(Obj)
- Morphisms in L(F × G) are built componentwise from pairs

**Status:** Conjectured, not proven. Would require constructing an explicit
isomorphism and understanding the relationship between the quotients.

### 5. Exponential Preservation

**From nLab Theorem 4.1:**

If L preserves finite products, then:

- Φ preserves exponentials
- The subcategory of categories is cartesian closed

**Status:** Conditional on proving L preserves products.

## Implemented Code

The following was added to `CatJudgmentAdjunction.lean`:

1. Imports:
   - `Mathlib.CategoryTheory.Adjunction.Limits`
   - `Mathlib.CategoryTheory.Adjunction.Reflective`

2. Instances in `MathlibReflectivity` section:
   - `phiFunctor_full`
   - `phiFunctor_faithful`
   - `phiFunctor_isRightAdjoint`
   - `lFunctor_isLeftAdjoint`
   - `phiFunctor_reflective`

3. `PreservationInstances` section with examples demonstrating that the
   preservation instances are automatically derived, plus documentation of
   the conjectured additional preservation properties.

## References

- [nLab: reflective subcategory](https://ncatlab.org/nlab/show/reflective+subcategory)
- [Mathlib Adjunction.Reflective](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Adjunction/Reflective.html)
- [Mathlib Adjunction.Limits](https://leanprover-community.github.io/mathlib4_docs/Mathlib/CategoryTheory/Adjunction/Limits.html)
- [mathlib3 adjunction.reflective](https://leanprover-community.github.io/mathlib_docs/category_theory/adjunction/reflective.html)
