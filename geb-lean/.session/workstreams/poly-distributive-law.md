# Workstream: Polynomial Distributive Law (C3 + E1)

## Status

Distributive law complete (Steps 1-9). GSOS rules
(Steps 10-14) remain.

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

- [x] Step 7: Comultiplication coherence (approx level)
  - `polyDistLaw_comul_approx` proved via induction
    on depth n, dispatching to node and leaf cases
  - Node case uses `Sigma.ext` with
    `polyCofixUnfoldAt_children_heq` (in PolyAlg.lean)
  - Leaf case uses `polyFreeMPure_cofree_sigma_eq`
    helper and `polyCoalgUnitAt_children_heq`
  - Leaf case: `obtain ⟨c_val, hc⟩ := c; subst hc`
    eliminates the cofree fiber transport. After that,
    the match on `polyFreeMPure` must be reduced
    (add `polyFreeMPure` to simp). The match on
    `polyCoalgUnit.left c_val` also needs reduction.
    Once matches reduce, the proof follows the same
    `congr 1; funext e; erw [polyScaleReindex_approx];
    erw [ih (ch e)]; congr 1; Subtype.ext; Sigma.ext`
    pattern as the node case.
  - Helper lemmas: `polyDistLaw_hx_rfl`,
    `polyDistLaw_comul_head_snd_node`,
    `polyDistLaw_comul_family_eq_node`,
    `polyCofixUnfoldAt_children_heq` (in PolyAlg.lean)
- [x] Step 8: Multiplication coherence
  - `polyDistLaw_mul` proved via terminal coalgebra
    uniqueness (`polyCofixUnfold_precomp`).
  - Defined `polyDistLaw_mul_srcCoalg` and
    `polyDistLaw_mul_rhsCoalg` as the source and target
    coalgebras on `T(T(D(A)))`.
  - Both sides shown equal as anamorphisms of
    `polyDistLaw_mul_srcCoalg` using coalgebra
    homomorphism precomposition.
  - Node/leaf cases of `tdist_hom_h` proved;
    the leaf case avoids inner case splitting on
    `t_a` by working at the abstract anamorphism level.
- [x] Step 9: Package as `DistributiveLaw`
  - `polyDistLawNat`: natural transformation
    `D . T --> T . D`
  - `polyDistributiveLaw`: full `DistributiveLaw`
    structure with all four coherence conditions
  - Translation lemmas (`polyFreeMonad_eta_eq`,
    `polyFreeMonad_mu_eq`, `polyFreeMonad_map_eq`,
    `polyCofreeComonad_eps_eq`,
    `polyCofreeComonad_delta_eq`,
    `polyCofreeComonad_map_eq`) bridge between
    categorical and concrete formulations
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
