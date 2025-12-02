# Proof Strategy for counitHom_counitInv

## Goal Structure

After `funext y`, `GrothendieckContra'.ext`, `funext ⟨⟨y', i⟩, h⟩`, `subst h`,
and `ext e`:

```lean
((((counitHom P ≫ counitInv P) y).fiber ≫ eqToHom _) ⟨⟨y', i⟩, rfl⟩).left e
  = ((𝟙 (wTypeToPolyBetween.obj (polyBetweenToWType.obj P)) y).fiber
      ⟨⟨y', i⟩, rfl⟩).left e
```

where `y = (polyBetweenToWType.obj P).t ⟨y', i⟩`.

## Key Observations

1. **RHS structure**: `id.fiber` in GrothendieckContra' is `eqToHom (id_base_eq X).symm`,
   which is transport along the proof that `id.base x = x`.

2. **LHS structure**: `comp.fiber` in GrothendieckContra' is
   `f.fiber ≫ (F'.map f.base).map g.fiber ≫ eqToHom (comp_fiber_cod_eq f g)`

3. **The problem**: The LHS has `comp.fiber ≫ eqToHom _` where the outer
   eqToHom comes from `GrothendieckContra'.ext` requiring fiber equality after
   composing with eqToHom.

## High-Level Proof Steps

### Step 1: Unfold the LHS composition

Show what `(counitHom P ≫ counitInv P) y` evaluates to at the fiber level.

### Step 2: Understand the element-level computation

The `.left e` extracts the left component of an Over morphism. Need to trace
how `e` transforms through the composition.

### Step 3: Show the eqToHom terms collapse

Both sides involve eqToHom (transport) along equal types. The claim is that
transporting `e` through the LHS composition gives the same result as
transporting through the RHS identity's eqToHom.

### Step 4: Use existing helper lemma

We have `counitInvFiberMap_counitFiberMap` which proves:

```lean
counitInvFiberMap P y i ∘ counitFiberMap P y i = id
```

This is the computational content - the functions compose to identity.

## Approach: Show eqToHom preserves the element

The core insight is that `eqToHom` on Over morphisms acts on `.left` by
transporting the left component. If we can show:

1. The actual computation on `e.left` is identity
   (from counitInvFiberMap_counitFiberMap)
2. The eqToHom transport is trivial on the value

Then we can prove the goal.

## Next Step to Try

Start by using `simp only [GrothendieckContra'.comp_fiber, GrothendieckContra'.id_fiber]`
to unfold the fiber definitions, then see what we have.
