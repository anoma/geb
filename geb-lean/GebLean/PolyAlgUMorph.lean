import GebLean.PolyAlg
import GebLean.PolyUMorph

/-!
# Algebra and Coalgebra Combinators for Polynomial
# Endofunctors

Combinators that construct `Endofunctor.Algebra` and
`Endofunctor.Coalgebra` instances for polynomial
endofunctors, using the universal morphisms from
`PolyUMorph.lean`.

## Main definitions

### General combinators

* `polyEndoMorphEvalAt` - Pointwise evaluation of a
  morphism of polynomial endofunctors
* `polyEndoMorphEval` - Natural transformation induced
  by a morphism of polynomial endofunctors
* `algPullback` - Pull back an algebra along a morphism
  of polynomial endofunctors
* `coalgPushforward` - Push forward a coalgebra along a
  morphism of polynomial endofunctors

### Coproduct algebras

* `algCoprodDesc` - Algebra for a coproduct of
  endofunctors from algebras of each component
* `algCoprodDescHom` - Algebra homomorphism combinator
  for coproduct algebras

### Product coalgebras

* `coalgProdLift` - Coalgebra for a product of
  endofunctors from coalgebras of each component
* `coalgProdLiftHom` - Coalgebra homomorphism combinator
  for product coalgebras

### Equalizer algebras

* `algEqRestrict` - Restrict an algebra to an equalizer
  subfunctor
* `algEqRestrictHom` - Algebra homomorphism combinator
  for equalizer algebras

### Coequalizer coalgebras

* `coalgCoeqExtend` - Extend a coalgebra to a coequalizer
  quotient functor
* `coalgCoeqExtendHom` - Coalgebra homomorphism combinator
  for coequalizer coalgebras

### Functorial combinators

* `algPullbackFunctor` - Functor from Q-algebras to
  P-algebras given `P ⟶ Q`
* `coalgPushforwardFunctor` - Functor from P-coalgebras
  to Q-coalgebras given `P ⟶ Q`
-/

namespace GebLean

open CategoryTheory

universe u

end GebLean
