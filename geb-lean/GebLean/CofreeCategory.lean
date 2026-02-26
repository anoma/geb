import GebLean.PolyAlg

/-!
# Cofree Category of a Polynomial Endofunctor

For a polynomial endofunctor `P : PolyEndo X`, the cofree
category `C_P` is the category corresponding to the cofree
comonoid on `P`.  It is constructed from the comonad
arising from the `Forget ⊣ Cofree` adjunction on
P-coalgebras, transported through the equivalence between
the cofree comonad and polynomial evaluation.

The category of P-coalgebras is equivalent to the
copresheaf topos `Set^{C_P}` (Adamek-Porst 2005/2006,
Spivak 2021).

## Construction

The comonad-first approach:
1. Derive `Comonad (Over X)` from
   `polyForgetCofreeAdjunction P`
   via `Adjunction.toComonad`.
2. Show the comonad's underlying functor is naturally
   isomorphic to `polyEndoFunctor X (polyCofreeMPoly P)`.
3. Transport the comonad structure to a comonoid in the
   monoidal category of polynomial endofunctors.
4. Extract the cofree category from the comonoid.

The comonad and natural isomorphism are defined in
`PolyAlg.lean` (`polyCofreeComonad`, `polyCofreeComonadIso`)
as they apply to all cofree comonads.
-/

namespace GebLean

open CategoryTheory

universe u

variable (X : Type u)

end GebLean
