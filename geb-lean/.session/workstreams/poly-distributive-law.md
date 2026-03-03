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
- [x] Import added to `GebLean.lean`

## Remaining Tasks

- [ ] Step 4: Naturality of `polyDistLawMor`
  - Need `NatTrans` construction
  - Both sides produce `PolyCofreeM` values; equality requires
    `PolyCofix.ext` and induction on approximation depth
  - Uses `polyCofreeCounit_naturality` (exists in PolyAlg.lean)
    and functoriality of `polyFreeMap`
  - Alternative: use `polyCofixUnfoldHom_unique` to reduce to
    showing both sides are coalgebra homomorphisms from
    a common `polyScale(T(B), P)`-coalgebra on `T(D(A))`
- [ ] Step 6: Unit coherence
  (`T.eta.app (D.obj A) >> dist.app A = D.map (T.eta.app A)`)
  - LHS: embed in leaf then unfold via anamorphism
  - RHS: map annotations by `polyFreeUnit`
  - Both produce same cofree element at each approx depth
  - Similar proof structure to `polyCofree_right_triangle_approx`
- [ ] Step 7: Comultiplication coherence
  - Both sides map `T(D(A)) --> D(D(T(A)))`
  - Use `polyCofixUnfoldHom_unique`: show both are coalgebra
    homomorphisms from the same source to the terminal
    `polyScale(D(T(A)), P)`-coalgebra
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
