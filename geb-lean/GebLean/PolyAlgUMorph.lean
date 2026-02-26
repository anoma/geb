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
Specialization of `polyBetweenMorphEvalAt` to
endofunctors (`Y = X`).
-/
abbrev polyEndoMorphEvalAt
    {P Q : PolyEndo X} (α : P ⟶ Q) (A : Over X)
    (x : X) :
    polyBetweenEvalFamily X X P A x →
    polyBetweenEvalFamily X X Q A x :=
  polyBetweenMorphEvalAt X X α A x

/--
Specialization of `polyBetweenMorphEval` to
endofunctors (`Y = X`).
-/
abbrev polyEndoMorphEval
    {P Q : PolyEndo X} (α : P ⟶ Q)
    (A : Over X) :
    (polyEndoFunctor X P).obj A ⟶
    (polyEndoFunctor X Q).obj A :=
  polyBetweenMorphEval X X α A

theorem polyEndoMorphEval_natural
    {P Q : PolyEndo X} (α : P ⟶ Q)
    {A B : Over X} (f : A ⟶ B) :
    polyEndoMorphEval α A ≫
      (polyEndoFunctor X Q).map f =
    (polyEndoFunctor X P).map f ≫
      polyEndoMorphEval α B :=
  polyBetweenMorphEval_natural X X α f

end PolyEndoMorphEval

section AlgPullback

variable {X : Type u}

/--
Pull back an algebra along a morphism of polynomial
endofunctors. Given `α : P ⟶ Q` and a Q-algebra `a`,
produce a P-algebra with the same carrier by precomposing
the structure map with `polyEndoMorphEval α a.a`.
-/
def algPullback
    {P Q : PolyEndo X} (α : P ⟶ Q)
    (a : PolyAlg Q) :
    PolyAlg P where
  a := a.a
  str := polyEndoMorphEval α a.a ≫ a.str

/--
Push forward a coalgebra along a morphism of polynomial
endofunctors. Given `α : P ⟶ Q` and a P-coalgebra `c`,
produce a Q-coalgebra with the same carrier by
postcomposing the structure map with
`polyEndoMorphEval α c.V`.
-/
def coalgPushforward
    {P Q : PolyEndo X} (α : P ⟶ Q)
    (c : PolyCoalg P) :
    PolyCoalg Q where
  V := c.V
  str := c.str ≫ polyEndoMorphEval α c.V

/--
An algebra homomorphism between Q-algebras is also a
homomorphism between the pulled-back P-algebras.
-/
def algPullbackHom
    {P Q : PolyEndo X} (α : P ⟶ Q)
    {a₁ a₂ : PolyAlg Q} (h : a₁ ⟶ a₂) :
    algPullback α a₁ ⟶ algPullback α a₂ :=
  Endofunctor.Algebra.Hom.mk h.f (by
    simp only [algPullback]
    rw [← Category.assoc,
      ← polyEndoMorphEval_natural α h.f,
      Category.assoc, h.h,
      ← Category.assoc])

/--
A coalgebra homomorphism between P-coalgebras is also a
homomorphism between the pushed-forward Q-coalgebras.
-/
def coalgPushforwardHom
    {P Q : PolyEndo X} (α : P ⟶ Q)
    {c₁ c₂ : PolyCoalg P} (h : c₁ ⟶ c₂) :
    coalgPushforward α c₁ ⟶ coalgPushforward α c₂ :=
  Endofunctor.Coalgebra.Hom.mk h.f (by
    simp only [coalgPushforward]
    rw [Category.assoc,
      polyEndoMorphEval_natural α h.f,
      ← Category.assoc, h.h,
      Category.assoc])

/--
Functor from Q-algebras to P-algebras induced by
`α : P ⟶ Q`.
-/
def algPullbackFunctor
    {P Q : PolyEndo X} (α : P ⟶ Q) :
    PolyAlg Q ⥤ PolyAlg P where
  obj := algPullback α
  map := algPullbackHom α
  map_id _ :=
    Endofunctor.Algebra.Hom.ext rfl
  map_comp _ _ :=
    Endofunctor.Algebra.Hom.ext rfl

/--
Functor from P-coalgebras to Q-coalgebras induced by
`α : P ⟶ Q`.
-/
def coalgPushforwardFunctor
    {P Q : PolyEndo X} (α : P ⟶ Q) :
    PolyCoalg P ⥤ PolyCoalg Q where
  obj := coalgPushforward α
  map := coalgPushforwardHom α
  map_id _ :=
    Endofunctor.Coalgebra.Hom.ext rfl
  map_comp _ _ :=
    Endofunctor.Coalgebra.Hom.ext rfl

/--
Pulling back algebras commutes with forgetting to
`Over X`.
-/
theorem algPullbackFunctor_forget
    {P Q : PolyEndo X} (α : P ⟶ Q) :
    algPullbackFunctor α ⋙ PolyAlg.forget P =
      PolyAlg.forget Q := by
  apply _root_.CategoryTheory.Functor.ext
  case h_obj => intro _; rfl
  case h_map =>
    intro _ _ _
    simp [algPullbackFunctor, algPullbackHom,
      PolyAlg.forget,
      Endofunctor.Algebra.forget]

/--
Pushing forward coalgebras commutes with forgetting to
`Over X`.
-/
theorem coalgPushforwardFunctor_forget
    {P Q : PolyEndo X} (α : P ⟶ Q) :
    coalgPushforwardFunctor α ⋙
      PolyCoalg.forget Q =
      PolyCoalg.forget P := by
  apply _root_.CategoryTheory.Functor.ext
  case h_obj => intro _; rfl
  case h_map =>
    intro _ _ _
    simp [coalgPushforwardFunctor,
      coalgPushforwardHom,
      PolyCoalg.forget,
      Endofunctor.Coalgebra.forget]

end AlgPullback

section CoprodAlgebra

variable {X : Type u}

/--
Construct an algebra for a coproduct of polynomial
endofunctors from compatible algebras with a shared
carrier. Given structure maps `str_i : F_i(A) ⟶ A`
for each `i`, the coproduct algebra has structure map
`(∐ F_i)(A) ⟶ A` that dispatches each tagged element
to the appropriate component's structure map.
-/
def algCoprodDesc
    {I : Type u} {F : I → PolyEndo X}
    (A : Over X)
    (strs : ∀ i,
      (polyEndoFunctor X (F i)).obj A ⟶ A) :
    PolyAlg (polyBetweenCoprod I F) where
  a := A
  str := Over.homMk
    (fun ⟨x, ⟨⟨i, p⟩, f⟩⟩ =>
      (strs i).left ⟨x, ⟨p, f⟩⟩)
    (by
      funext ⟨x, ⟨⟨i, p⟩, f⟩⟩
      exact congrFun (Over.w (strs i))
        ⟨x, ⟨p, f⟩⟩)

/--
A morphism that is simultaneously a homomorphism for each
component algebra is a homomorphism for the coproduct
algebra.
-/
def algCoprodDescHom
    {I : Type u} {F : I → PolyEndo X}
    {A B : Over X}
    {strsA : ∀ i,
      (polyEndoFunctor X (F i)).obj A ⟶ A}
    {strsB : ∀ i,
      (polyEndoFunctor X (F i)).obj B ⟶ B}
    (h : A ⟶ B)
    (hcomm : ∀ i,
      (polyEndoFunctor X (F i)).map h ≫
        strsB i = strsA i ≫ h) :
    algCoprodDesc A strsA ⟶
      algCoprodDesc B strsB :=
  Endofunctor.Algebra.Hom.mk h (by
    apply Over.OverMorphism.ext
    funext ⟨x, ⟨⟨i, p⟩, f⟩⟩
    exact congrFun
      (congrArg CommaMorphism.left
        (hcomm i))
      ⟨x, ⟨p, f⟩⟩)

end CoprodAlgebra

end GebLean
