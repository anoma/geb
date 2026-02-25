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

section PolyEndoMorphEval

variable {X : Type u}

/--
Pointwise evaluation of a polynomial endofunctor morphism
at a fiber. Given `α : P ⟶ Q` and `A : Over X`, at
fiber `x` the map sends `(i, f)` to
`(ccrReindex (α x) i, ccrFiberMor (α x) i ≫ f)`.
-/
def polyEndoMorphEvalAt
    {P Q : PolyEndo X} (α : P ⟶ Q) (A : Over X)
    (x : X) :
    polyBetweenEvalFamily X X P A x →
    polyBetweenEvalFamily X X Q A x :=
  fun ev => ptoefMk X
    (ccrReindex (α x) (ptoefIndex X ev))
    (ccrFiberMor (α x) (ptoefIndex X ev) ≫
      ptoefMor X ev)

/--
Evaluation of a polynomial endofunctor morphism. Given
`α : P ⟶ Q` and `A : Over X`, produce
`(polyEndoFunctor X P).obj A ⟶
  (polyEndoFunctor X Q).obj A`.
-/
def polyEndoMorphEval
    {P Q : PolyEndo X} (α : P ⟶ Q) (A : Over X) :
    (polyEndoFunctor X P).obj A ⟶
    (polyEndoFunctor X Q).obj A :=
  (familySliceForward X).map
    (fun x => polyEndoMorphEvalAt α A x)

theorem polyEndoMorphEval_natural
    {P Q : PolyEndo X} (α : P ⟶ Q)
    {A B : Over X} (f : A ⟶ B) :
    polyEndoMorphEval α A ≫
      (polyEndoFunctor X Q).map f =
    (polyEndoFunctor X P).map f ≫
      polyEndoMorphEval α B := by
  apply Over.OverMorphism.ext
  funext ⟨x, i, g⟩
  dsimp [polyEndoMorphEval, polyEndoMorphEvalAt,
    polyEndoFunctor, polyBetweenEvalFunctor,
    polyToOverFunctor, polyToOverEvalMap,
    familySliceForward, familySliceForwardMap,
    polyToOverEvalFamilyMap,
    ptoefMk, ptoefIndex, ptoefMor,
    ccrEvalMap, ccrEvalMk, ccrEvalIndex,
    ccrEvalMor, Over.comp_left]
  simp only [Category.assoc]

end PolyEndoMorphEval

end GebLean
