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

section ProdCoalgebra

variable {X : Type u}

/--
Assemble component evaluations into a product
evaluation. Given evaluations `evs i : ccrEval (F_i x) A`
for each `i`, produce `ccrEval ((∏ F_i) x) A`.
-/
private def coalgProdLiftAt
    {I : Type u} {F : I → PolyEndo X}
    {A : Over X} (x : X)
    (evs : ∀ i, ccrEval ((F i) x) A) :
    ccrEval ((polyBetweenProd I F) x) A :=
  ⟨fun i => (evs i).fst,
    Over.homMk
      (fun ⟨i, e⟩ => (evs i).snd.left e)
      (by
        funext ⟨i, e⟩
        exact congrFun
          (Over.w (evs i).snd) e)⟩

/--
Construct a coalgebra for a product of polynomial
endofunctors from compatible coalgebras with a shared
carrier. Given structure maps `str_i : A ⟶ F_i(A)` for
each `i`, the product coalgebra has structure map
`A ⟶ (∏ F_i)(A)` that tuples the component structure
maps.
-/
def coalgProdLift
    {I : Type u} {F : I → PolyEndo X}
    (A : Over X)
    (strs : ∀ i,
      A ⟶ (polyEndoFunctor X (F i)).obj A) :
    PolyCoalg (polyBetweenProd I F) where
  V := A
  str := Over.homMk
    (fun a =>
      ⟨A.hom a,
        coalgProdLiftAt (A.hom a)
          (fun i =>
            cast
              (congrArg
                (fun y => ccrEval ((F i) y) A)
                (congrFun
                  (Over.w (strs i)) a))
              ((strs i).left a).snd)⟩)
    (by funext _; rfl)


private lemma ccrEvalMap_cast_comm
    {I : Type u} {F : I → PolyEndo X}
    {A B : Over X} (h : A ⟶ B)
    (i : I) {x₁ x₂ : X} (hx : x₁ = x₂)
    (ev : ccrEval ((F i) x₁) A) :
    ccrEvalMap h
      (cast
        (congrArg
          (fun y => ccrEval ((F i) y) A) hx)
        ev) =
    cast
      (congrArg
        (fun y => ccrEval ((F i) y) B) hx)
      (ccrEvalMap h ev) := by
  cases hx; rfl

private lemma coalgProdLiftAt_ccrEvalMap
    {I : Type u} {F : I → PolyEndo X}
    {A B : Over X} (h : A ⟶ B)
    (x : X)
    (evs : ∀ i, ccrEval ((F i) x) A) :
    ccrEvalMap h (coalgProdLiftAt x evs) =
      coalgProdLiftAt x
        (fun i => ccrEvalMap h (evs i)) := by
  simp only [ccrEvalMap, coalgProdLiftAt]
  congr 1

private lemma coalgProdLiftAt_heq
    {I : Type u} {F : I → PolyEndo X}
    {A : Over X} {x₁ x₂ : X} (hx : x₁ = x₂)
    {evs₁ : ∀ i, ccrEval ((F i) x₁) A}
    {evs₂ : ∀ i, ccrEval ((F i) x₂) A}
    (hevs : ∀ i, evs₁ i ≍ evs₂ i) :
    coalgProdLiftAt x₁ evs₁ ≍
      coalgProdLiftAt x₂ evs₂ := by
  cases hx
  have : evs₁ = evs₂ :=
    funext (fun i => eq_of_heq (hevs i))
  cases this
  rfl

private lemma hcomm_component_cast_heq
    {I : Type u} {F : I → PolyEndo X}
    {A B : Over X}
    {strsA : ∀ i,
      A ⟶ (polyEndoFunctor X (F i)).obj A}
    {strsB : ∀ i,
      B ⟶ (polyEndoFunctor X (F i)).obj B}
    (h : A ⟶ B)
    (hcomm : ∀ i,
      strsA i ≫ (polyEndoFunctor X (F i)).map h =
        h ≫ strsB i)
    (i : I) (a : A.left) :
    cast
      (congrArg
        (fun y => ccrEval ((F i) y) B)
        (congrFun (Over.w (strsA i)) a))
      (ccrEvalMap h ((strsA i).left a).snd)
    ≍ cast
      (congrArg
        (fun y => ccrEval ((F i) y) B)
        (congrFun (Over.w (strsB i))
          (h.left a)))
      ((strsB i).left (h.left a)).snd := by
  have happ :=
    congrFun
      (congrArg CommaMorphism.left (hcomm i)) a
  simp only [Over.comp_left,
    types_comp_apply] at happ
  have hsnd := sigma_snd_heq_of_eq happ
  exact (cast_heq _ _).trans
    (hsnd.trans (cast_heq _ _).symm)

private lemma coalgProdLiftHom_snd_heq
    {I : Type u} {F : I → PolyEndo X}
    {A B : Over X}
    {strsA : ∀ i,
      A ⟶ (polyEndoFunctor X (F i)).obj A}
    {strsB : ∀ i,
      B ⟶ (polyEndoFunctor X (F i)).obj B}
    (h : A ⟶ B)
    (hcomm : ∀ i,
      strsA i ≫ (polyEndoFunctor X (F i)).map h =
        h ≫ strsB i)
    (a : A.left) :
    ccrEvalMap h
      (coalgProdLiftAt (A.hom a)
        (fun i =>
          cast
            (congrArg
              (fun y => ccrEval ((F i) y) A)
              (congrFun (Over.w (strsA i)) a))
            ((strsA i).left a).snd))
    ≍ coalgProdLiftAt (B.hom (h.left a))
        (fun i =>
          cast
            (congrArg
              (fun y => ccrEval ((F i) y) B)
              (congrFun (Over.w (strsB i))
                (h.left a)))
            ((strsB i).left (h.left a)).snd) := by
  have step1 :=
    heq_of_eq
      (coalgProdLiftAt_ccrEvalMap h (A.hom a)
        (fun i =>
          cast
            (congrArg
              (fun y => ccrEval ((F i) y) A)
              (congrFun (Over.w (strsA i)) a))
            ((strsA i).left a).snd))
  have step2 :=
    heq_of_eq
      (congrArg
        (coalgProdLiftAt (A.hom a))
        (funext (fun i =>
          ccrEvalMap_cast_comm h i
            (congrFun (Over.w (strsA i)) a)
            ((strsA i).left a).snd)))
  have step3 :=
    coalgProdLiftAt_heq
      (congrFun (Over.w h) a).symm
      (fun i =>
        hcomm_component_cast_heq h hcomm i a)
  exact step1.trans (step2.trans step3)

/--
A morphism that is simultaneously a homomorphism for each
component coalgebra is a homomorphism for the product
coalgebra.
-/
def coalgProdLiftHom
    {I : Type u} {F : I → PolyEndo X}
    {A B : Over X}
    {strsA : ∀ i,
      A ⟶ (polyEndoFunctor X (F i)).obj A}
    {strsB : ∀ i,
      B ⟶ (polyEndoFunctor X (F i)).obj B}
    (h : A ⟶ B)
    (hcomm : ∀ i,
      strsA i ≫ (polyEndoFunctor X (F i)).map h =
        h ≫ strsB i) :
    coalgProdLift A strsA ⟶
      coalgProdLift B strsB :=
  Endofunctor.Coalgebra.Hom.mk h (by
    apply Over.OverMorphism.ext
    funext a
    simp only [Over.comp_left, types_comp_apply,
      coalgProdLift, Over.homMk_left]
    exact sigma_eq_of_fst_eq_snd_heq
      (congrFun (Over.w h) a).symm
      (coalgProdLiftHom_snd_heq h hcomm a))

end ProdCoalgebra

section EqAlgebra

variable {X : Type u}

/--
Restrict an algebra to an equalizer subfunctor. Given
`f, g : P ⟶ Q` and a P-algebra, produce an algebra for
`polyBetweenEq f g` by pulling back along the equalizer
inclusion.
-/
def algEqRestrict
    {P Q : PolyEndo X} {f g : P ⟶ Q}
    (a : PolyAlg P) :
    PolyAlg (polyBetweenEq f g) :=
  algPullback (polyBetweenEqIncl f g) a

/--
An algebra homomorphism between P-algebras restricts to a
homomorphism between the equalizer algebras.
-/
def algEqRestrictHom
    {P Q : PolyEndo X} {f g : P ⟶ Q}
    {a₁ a₂ : PolyAlg P} (h : a₁ ⟶ a₂) :
    algEqRestrict (f := f) (g := g) a₁ ⟶
      algEqRestrict (f := f) (g := g) a₂ :=
  algPullbackHom (polyBetweenEqIncl f g) h

end EqAlgebra

section CoeqCoalgebra

variable {X : Type u}

/--
Extend a coalgebra to a coequalizer quotient functor.
Given `s, t : P ⟶ Q` and a Q-coalgebra, produce a
coalgebra for `polyBetweenCoeq s t` by pushing forward
along the coequalizer projection.
-/
def coalgCoeqExtend
    {P Q : PolyEndo X} {s t : P ⟶ Q}
    (c : PolyCoalg Q) :
    PolyCoalg (polyBetweenCoeq s t) :=
  coalgPushforward (polyBetweenCoeqProj s t) c

/--
A coalgebra homomorphism between Q-coalgebras extends to
a homomorphism between the coequalizer coalgebras.
-/
def coalgCoeqExtendHom
    {P Q : PolyEndo X} {s t : P ⟶ Q}
    {c₁ c₂ : PolyCoalg Q} (h : c₁ ⟶ c₂) :
    coalgCoeqExtend (s := s) (t := t) c₁ ⟶
      coalgCoeqExtend (s := s) (t := t) c₂ :=
  coalgPushforwardHom
    (polyBetweenCoeqProj s t) h

end CoeqCoalgebra

end GebLean
