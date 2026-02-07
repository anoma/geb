# map_comp fiberMorph HEq proof plan

## Status: IN PROGRESS

## Problem

Need to complete `totalDecFact_map_comp_fiberMorph_heq` in
`GebLean/Factorization.lean` (~line 3283). This is the last
remaining hole for the `totalDecFactToGrothendieck` functor's
`map_comp` proof.

## Current errors

1. `decFact_fiveChain_fiberMorph_heq` (line ~2579): TYPE
   ERROR - uses `ψ.factHom.h` where `ψ : c ⟶ d`, but the
   `decFactComp_*` helpers need `b.fact.mid` source, not
   `c.fact.mid`. Need `(q ▸ ψ)` in the type AND a working
   proof.

2. `totalDecFact_map_comp_fiberMorph_heq` (line ~3283):
   references the broken lemma.

## Factoring-out-lemmas plan

### Step 1: Fix decFact_fiveChain_fiberMorph_heq

- Change RHS to use `(q ▸ ψ).factHom.h` and `(q ▸ ψ).fiberMorph`
- Fix proof using `have/▸` approach (same as
  `decFact_fiveChain_vs_comp_fiberMorph_heq`):

  ```text
  subst p; subst r; subst q
  have h : eqToHom rfl ≫ φ ≫ eqToHom rfl ≫ ψ ≫ eqToHom rfl
         = φ ≫ ψ := by
    simp [eqToHom_refl, Category.id_comp, Category.comp_id]
  exact h ▸ HEq.rfl
  ```

- Status: NOT STARTED

### Step 2: Replace totalDecFact_map_comp_fiberMorph_heq body

  with `_` to see exact goal

- Status: NOT STARTED

### Step 3: Factor into lemmas based on the goal

- Lemma A: Relate LHS to some computable intermediate
- Lemma B: Relate intermediate to RHS
- Combine with HEq.trans
- Status: NOT STARTED

### Step 4: Implement each lemma

- Use `have/▸` trick or existing lemmas
- Status: NOT STARTED

### Step 5: Fix remaining warnings

- `show` -> `change` at line ~3353
- Any unused simp args
- Status: NOT STARTED

## Technique notes

The `have/▸` approach works because:

- `subst` eliminates equality proofs, making eqToHom trivial
- `have h : 5-chain = simple` proves at the DecFactHom level
  (not under .fiberMorph)
- `h ▸ HEq.rfl` rewrites the LHS under .fiberMorph via the
  DecFactHom-level equality
- After rewrite, both sides are definitionally equal

The challenge at the call site: the ConnGrothendieck 5-chain's
equality proofs are COMPUTED (not free variables), so `subst`
cannot be used directly. Instead, intermediate lemmas must
bridge between the two representations.
