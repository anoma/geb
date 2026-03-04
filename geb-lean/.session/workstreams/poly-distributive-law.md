# Workstream: Polynomial Distributive Law (C3 + E1)

## Status

Active

## Context

Constructing the canonical distributive law
`lambda : T . D --> D . T` where `T = polyFreeMonad X P` and
`D = polyCofreeComonad X P`, and abstract GSOS rules (E1).

## Completed

- [x] Step 1: P-coalgebra on free monad trees
  (`polyFreeMCoalgStrAt`, `polyFreeMCoalgStr`, `polyFreeMCoalg`)
- [x] Step 2: polyScale coalgebra on T(D(A))
  (`polyDistLawScaleCoalgStrAt`, `polyDistLawScaleCoalgStr`,
  `polyDistLawScaleCoalg`)
- [x] Step 3: Distributive law morphism via anamorphism
  (`polyDistLawMor`)
- [x] Step 5: Counit coherence
  (`polyDistLawMor_head_fst`, `polyDistLaw_counit`)
- [x] Step 6: Unit coherence
  (`polyFreeMPure_proof_irrel`,
  `polyDistLaw_unit_approx`, `polyDistLaw_unit`)
- [x] Step 4: Naturality of `polyDistLawMor`
  (`polyDistLaw_annot_natural`,
  `polyCofixApprox_intro_polyScale_congr`,
  `polyDistLaw_naturality_approx_leaf`,
  `polyDistLaw_naturality_approx`,
  `polyDistLaw_naturality`)
- [x] Import added to `GebLean.lean`

## Remaining Tasks

- [ ] Step 7: Comultiplication coherence
  - Both sides map `T(D(A)) --> D(D(T(A)))`
  - Proof by approximation-level induction; node and
    leaf cases separated
  - Node case: annotation match via
    `polyDistLaw_comul_annot_eq`, P-index match by
    `congr`, children by `ih(ch e)` after
    `erw [polyScaleReindex_approx, ih (ch e)]`.
    Remaining subgoal requires
    `polyCofixUnfoldAt_children_heq` (M-type children
    = recursive anamorphism application)
  - `polyCofixUnfoldAt_children_heq` added to
    PolyAlg.lean (general anamorphism children lemma)
  - Node case fully proved using `Sigma.ext hfst hch`
    to close the M-type children subgoal
  - Leaf case: same structure but `polyFreeMCoalgStrAt`
    at `Sum.inl c` applies cofree structure map and
    wraps children in `polyFreeMPure`; needs analogous
    proof with the same `Sigma.ext` pattern
  - Helper lemmas: `polyDistLaw_hx_rfl`,
    `polyDistLaw_comul_head_snd_node`,
    `polyDistLaw_comul_family_eq_node`
- [ ] Step 8: Multiplication coherence
  - Both sides map `T(T(D(A))) --> D(T(A))`
  - Similar approach to Step 7 with
    `polyCofixUnfoldHom_unique`
- [ ] Step 9: Package as `DistributiveLaw`
  - Requires Steps 4-8
- [ ] Steps 10-14: GSOS rules (E1)
  - `PolyGSOS.lean` (new file)
  - Fiberwise product, `GSOSRule` structure,
    canonical GSOS, distributive law from GSOS

## Notes

### Proof strategy for coherence axioms

The coherence proofs require one of two approaches:

1. **Direct approximation induction**: Show equality of
   `PolyCofixApprox` values at every depth by induction.
   Pattern: `polyCofree_right_triangle_approx` in
   PolyAlg.lean (lines 7334-7395). Each proof is 40-80
   lines due to index matching and transport handling.

2. **Terminal coalgebra uniqueness**: Use
   `polyCofixUnfoldHom_unique` (PolyAlg.lean:2296) to
   reduce to showing both sides are coalgebra
   homomorphisms from the same source. Requires defining
   the source coalgebra and proving the homomorphism
   conditions.

Approach (2) is preferred for Steps 7-8 since the
compositions are long, while approach (1) may be more
direct for Steps 4 and 6.

### Transport considerations

The leaf case of `polyFreeMCoalgStrAt` uses `hfib ▸` to
transport results. For our coalgebra
`polyDistLawScaleCoalg`, this transport is trivially
`rfl` since the structure map preserves fibers. The
anamorphism's `polyCofixUnfoldApprox` also uses `hx ▸`,
which is `rfl` for the same reason. This simplifies
the counit coherence proof (Step 5) but the other
coherence proofs involve compositions where the
transport is non-trivial.

### Monad/comonad functor actions

The monad `polyFreeMonad X P` has
`T.toFunctor.map f = polyFreeMap ... f` and
`T.toFunctor.obj A = polyFreeMCarrier A P` (literally,
through the adjunction). Similarly
`D.toFunctor.map f = polyCofreeMap ... f`. So the
distributive law at the abstract level uses the
same concrete morphisms.
