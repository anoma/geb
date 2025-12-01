# Workstream: Grothendieck Functor Factorization

## Status

Active

## Context

This workstream explores refactoring the `FunctorToData`, `FunctorFromData`,
and `FunctorBetweenData` structures in `GebLean/Utilities/Grothendieck.lean`
to expose orthogonal factorizations via pullbacks (`pre`) and related
constructions.

The goal is to understand whether functors into/from/between Grothendieck
constructions can be decomposed into simpler, more modular components.

## Analysis Summary

### FunctorTo: Functors INTO Grothendieck Constructions

**Current structure** (`FunctorToData F (D := E)`):

- `baseFunc : E ⥤ C`
- `fib : ∀ e, F.obj (baseFunc.obj e)` (fiber elements)
- `hom : ∀ g : e ⟶ e', (F.map (baseFunc.map g)).obj (fib e) ⟶ fib e'`
- Coherence conditions

**Factorization via pullback:**

A functor `H : E ⥤ Grothendieck F` can be factored as:

```text
E --section--> Grothendieck (baseFunc ⋙ F) --pre F baseFunc--> Grothendieck F
```

where:

1. `baseFunc := H ⋙ forget F : E ⥤ C`
2. The "section" is a functor `s : E ⥤ Grothendieck (baseFunc ⋙ F)` such that
   `s ⋙ forget (baseFunc ⋙ F) = 𝟭 E`
3. `pre F baseFunc : Grothendieck (baseFunc ⋙ F) ⥤ Grothendieck F` is the
   standard pullback functor from mathlib

**Insight:** Sections of `forget (G ⋙ F) : Grothendieck (G ⋙ F) ⥤ D` are a
constrained class of functors. They are determined by:

- A choice of fiber element for each object in D
- Coherent fiber morphisms for each morphism in D

This is equivalent to the fiber data in `FunctorToData`.

**Implemented structure:**

```lean
structure SectionData (F : C ⥤ Cat) where
  fib : ∀ c, F.obj c
  hom : ∀ {c c'} (f : c ⟶ c'), (F.map f).obj (fib c) ⟶ fib c'
  hom_id : ∀ c, hom (𝟙 c) = eqToHom ...
  hom_comp : ∀ f g, hom (f ≫ g) = ...
```

This is the intrinsic notion of a section of `forget F : Grothendieck F ⥤ C`,
independent of any incoming functor.

**Equivalence (implemented):**

```lean
FunctorToData F (D := D) ≃ Σ (baseFunc : D ⥤ C), SectionData (baseFunc ⋙ F)
```

**Explicit factorization via `pre` (implemented):**

```lean
def FunctorToData.toFunctorViaPre
    (baseFunc : D ⥤ C) (sec : SectionData (baseFunc ⋙ F)) : D ⥤ Grothendieck F :=
  sec.toFunctor ⋙ Grothendieck.pre F baseFunc

theorem FunctorToData.functorTo_eq_toFunctorViaPre (data : FunctorToData F (D := D)) :
    functorTo F data = FunctorToData.toFunctorViaPre F data.baseFunc
        (FunctorToData.toSigmaSectionData F data).2
```

This makes `pre` central to the factorization.

### FunctorFrom: Functors FROM Grothendieck Constructions

**Current structure** (`FunctorFromData F (E := T)`):

- `fib : ∀ c, F.obj c ⥤ T`
- `hom : ∀ f : c ⟶ c', fib c ⟶ F.map f ⋙ fib c'`
- Coherence conditions

**Analysis:**

There is no dual "pushforward" operation analogous to `pre`. The `pre`
operation pulls back along a functor on the base category; there is no
simple operation that pushes forward the total space.

The structure of `FunctorFromData` is already canonical:

- It describes the functor in terms of restrictions to fibers
- The `fib c` functors are exactly `ι F c ⋙ H` where `H` is the original
  functor
- The `hom f` natural transformations encode coherence across base morphisms

**Conclusion:** No significant refactoring recommended. The current structure
is already in atomic form.

### FunctorBetween: Functors BETWEEN Grothendieck Constructions

**Current structure** (`FunctorBetweenData G F` for `G : C ⥤ Cat`, `F : D ⥤ Cat`):

- `baseFib : C ⥤ D`
- `fibFib : ∀ c, G.obj c ⥤ F.obj (baseFib.obj c)`
- `fibHomCrossApp : ∀ f x, (F.map (baseFib.map f)).obj ((fibFib c).obj x) ⟶
  (fibFib c').obj ((G.map f).obj x)`
- Naturality and coherence conditions

**Factorization via pullback:**

A functor `H : Grothendieck G ⥤ Grothendieck F` factors as:

```text
Grothendieck G --H'--> Grothendieck (baseFib ⋙ F) --pre F baseFib-->
  Grothendieck F
```

where:

1. `baseFib : C ⥤ D` is the induced map on base categories
2. `H' : Grothendieck G ⥤ Grothendieck (baseFib ⋙ F)` is identity on base
3. Both source and target of H' have base category C

**Connection to lax natural transformations:**

The functor H' (identity on base, arbitrary on fibers) corresponds to a
**lax natural transformation** `G ⟹ baseFib ⋙ F`:

- Component functors: `α_c : G.obj c ⥤ F.obj (baseFib.obj c)`
- Laxity morphisms: for `f : c ⟶ c'`, natural transformations relating
  `α_c ⋙ F.map (baseFib.map f)` to `G.map f ⋙ α_c'`

**Implemented structure:**

```lean
structure LaxNatTransData (G F : C ⥤ Cat) where
  app : ∀ c, G.obj c ⥤ F.obj c
  laxApp : ∀ {c c'} (f : c ⟶ c') (x : G.obj c),
    (F.map f).obj ((app c).obj x) ⟶ (app c').obj ((G.map f).obj x)
  laxNat : ∀ {c c'} (f : c ⟶ c') {x y} (φ : x ⟶ y),
    (F.map f).map ((app c).map φ) ≫ laxApp f y =
      laxApp f x ≫ (app c').map ((G.map f).map φ)
  laxId : ∀ c x, laxApp (𝟙 c) x = eqToHom (...)
  laxComp : ∀ {c c' c''} (f : c ⟶ c') (g : c' ⟶ c'') (x : G.obj c),
    laxApp (f ≫ g) x = eqToHom (...) ≫
      (F.map g).map (laxApp f x) ≫ laxApp g ((G.map f).obj x)
```

**Equivalence (implemented):**

```lean
def FunctorBetweenData.equivSigmaLaxNatTrans :
    FunctorBetweenData G F ≃
      Σ (baseFib : C ⥤ D), LaxNatTransData G (baseFib ⋙ F)
```

### Contravariant Versions

All of the above applies to `GrothendieckContra'` with the following changes:

- Fiber morphisms go in the opposite direction
- "Lax" becomes "oplax" (the coherence morphisms reverse direction)
- `pre` becomes the contravariant version already implemented

## Implementation Plan

### Phase 1: Covariant FunctorTo refactoring

- [x] Define `SectionData F` for sections of `forget F : Grothendieck F ⥤ C`
      (intrinsic definition, no incoming functor parameter)
- [x] Prove `FunctorToData F ≃ Σ (baseFunc : D ⥤ C), SectionData (baseFunc ⋙ F)`
      via `FunctorToData.equivSigmaSectionData`
- [x] Construct `SectionData.toFunctor : SectionData F → (C ⥤ Grothendieck F)`
- [x] Define `FunctorToData.toFunctorViaPre` showing explicit factorization
      via `sec.toFunctor ⋙ pre F baseFunc`
- [x] Prove `functorTo F data = toFunctorViaPre F baseFunc sec`

### Phase 2: Covariant FunctorBetween refactoring

- [x] Define `LaxNatTransData G F` for lax natural transformations between
      Cat-valued functors
- [x] Construct the functor `Grothendieck G ⥤ Grothendieck F` from
      `LaxNatTransData G F` (identity on base) via `LaxNatTransData.toFunctor`
- [x] Define `LaxNatTransData.id` and `LaxNatTransData.comp` for composition
- [x] Prove that `FunctorBetweenData G F` decomposes as base functor plus
      lax natural transformation via `FunctorBetweenData.equivSigmaLaxNatTrans`
- [x] Define `LaxFunctorCat C` wrapper type with category instance for
      lax morphisms
- [x] Implement embedding `natToLaxFunctor : (C ⥤ Cat) ⥤ LaxFunctorCat C`
- [ ] Show that the decomposition commutes with `pre`

### Phase 3: Contravariant versions

- [x] Define `SectionDataContra F'` for sections of contravariant Grothendieck
- [x] Prove contravariant `FunctorToContraData` factorization via sections
      via `FunctorToContraData.toFunctorViaPreContra`
- [x] Define `OplaxNatTransData G' F'` for oplax natural transformations between
      contravariant Cat-valued functors
- [x] Define `OplaxNatTransData.id` and `OplaxNatTransData.comp` for composition
- [x] Prove composition laws (`comp_assoc`, `id_comp`, `comp_id`)
- [x] Define `OplaxFunctorCat C` wrapper type with category instance for
      oplax morphisms

### Phase 4: Integration and documentation

- [ ] Update existing code to use factorized forms where appropriate
- [ ] Add examples demonstrating the factorization
- [ ] Document the mathematical interpretation

## Mathematical Background

### Sections of fibrations

Given a functor `p : E ⥤ B` (viewed as a fibration), a **section** of p is
a functor `s : B ⥤ E` such that `s ⋙ p = 𝟭 B`. Sections pick out a choice
of object in each fiber.

For Grothendieck constructions, `forget (G ⋙ F) : Grothendieck (G ⋙ F) ⥤ D`
is the canonical projection. Sections of this correspond to choosing fiber
elements coherently.

### Lax natural transformations

For functors `G, F : C ⥤ Cat`, a lax natural transformation `α : G ⟹ F`
consists of:

- For each `c : C`, a functor `α_c : G.obj c ⥤ F.obj c`
- For each `f : c ⟶ c'`, a natural transformation
  `α_f : α_c ⋙ F.map f ⟹ G.map f ⋙ α_c'`
- Coherence axioms for identities and compositions

The direction of `α_f` distinguishes lax from oplax: in oplax, the direction
is reversed.

### The pre functor

Mathlib's `Grothendieck.pre F G : Grothendieck (G ⋙ F) ⥤ Grothendieck F`
is the pullback functor induced by `G : D ⥤ C`. It acts as:

- On objects: `(d, x) ↦ (G.obj d, x)`
- On morphisms: `(g, φ) ↦ (G.map g, φ)`

This is the key component enabling the factorizations.

## Notes

- The factorization for FunctorTo is similar to the universal property of
  the Grothendieck construction: functors into it correspond to sections
  of the pullback
- The lax natural transformation perspective for FunctorBetween connects
  to the theory of 2-categories and bicategories
- These factorizations may simplify proofs by separating base-level concerns
  from fiber-level concerns
