import GebLean.Polynomial
import GebLean.Utilities.Presheaf
import GebLean.Utilities.Elements
import GebLean.Utilities.Families
import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Functor.FullyFaithful
import Mathlib.CategoryTheory.Functor.Currying

/-!
# Polynomial Functors Between Presheaf Categories

This module defines polynomial functors (parametric right
adjoints) between presheaf categories using the formula:

```
P(Z)(j) = ∐_{a ∈ A(j)} Hom_{PSh(I)}(E_j(a), Z)
```

A presheaf PRA `PSh(I) → PSh(J)` is represented as a functor
`Jᵒᵖ ⥤ CoprodCovarRepCat (Iᵒᵖ ⥤ Type w_I)`.  At each
`j : J`, this gives a polynomial `(A(j), E_j)` from
`CoprodCovarRepCat`, and the functor action provides the
restriction maps that make the evaluation a presheaf on `J`.

## References

* <https://ncatlab.org/nlab/show/parametric+right+adjoint>
-/

namespace GebLean

open CategoryTheory

universe u_I v_I u_J v_J w_I w'

attribute [local instance] CategoryTheory.uliftCategory

variable (I : Type u_I) [Category.{v_I} I]
variable (J : Type u_J) [Category.{v_J} J]

/-! ## Presheaf Category Functor -/

/--
The functor `Catᵒᵖ ⥤ Cat` sending `C` to the presheaf
category `C ⥤ Type w_I`.
-/
def presheafCatFunctor :
    Cat.{v_I, u_I}ᵒᵖ ⥤
      Cat.{max u_I w_I, max v_I (w_I + 1) u_I} :=
  catContraHomFunctor.{v_I, u_I, w_I, w_I + 1}
    (Cat.of (Type w_I))

/--
The presheaf category `Iᵒᵖ ⥤ Type w_I` as an object of `Cat`.
-/
def presheafCat : Cat.{max u_I w_I, max v_I (w_I + 1) u_I} :=
  presheafCatFunctor.{u_I, v_I, w_I}.obj
    (Opposite.op (Cat.of Iᵒᵖ))

/-! ## CoprodCovarRepCat of the Presheaf Category -/

/--
The functor `Catᵒᵖ ⥤ Cat` sending `C` to
`CoprodCovarRepCat (C ⥤ Type w_I)`.
-/
def ccrPresheafCatFunctor :
    Cat.{v_I, u_I}ᵒᵖ ⥤
    Cat.{max w' u_I w_I, max (w' + 1) (w_I + 1) v_I u_I} :=
  presheafCatFunctor.{u_I, v_I, w_I} ⋙
    coprodCovarRepFunctor.{max v_I (w_I + 1) u_I,
      max u_I w_I, w'}

/--
The category of coproducts of covariant representables on
the presheaf category of `I`, as an object of `Cat`.
-/
def ccrPresheafCat :
    Cat.{max w' u_I w_I, max (w' + 1) (w_I + 1) v_I u_I} :=
  ccrPresheafCatFunctor.{u_I, v_I, w_I, w'}.obj
    (Opposite.op (Cat.of Iᵒᵖ))

/-! ## The Category of Presheaf PRAs -/

section PresheafPRADef

/--
Precomposition with `ccrPresheafCatFunctor`: turns a
functor `Cat ⥤ Cat` into a functor `Catᵒᵖ ⥤ Cat`.
-/
def ccrPresheafWhiskerLeft :
    (Cat.{max w' u_I w_I,
        max (w' + 1) (w_I + 1) v_I u_I} ⥤
      Cat.{max u_I u_J w_I w',
        max u_I u_J v_I v_J (w_I + 1) (w' + 1)}) ⥤
    (Cat.{v_I, u_I}ᵒᵖ ⥤
      Cat.{max u_I u_J w_I w',
        max u_I u_J v_I v_J (w_I + 1) (w' + 1)}) :=
  (Functor.whiskeringLeft _ _ _).obj
    ccrPresheafCatFunctor.{u_I, v_I, w_I, w'}

/--
The bifunctor sending `(J, I)` to the presheaf PRA
category `Jᵒᵖ ⥤ CoprodCovarRepCat (Iᵒᵖ ⥤ Type w_I)`.
This can be viewed (when uncurried) as a `Cat`-valued
presheaf on `Cat x Cat`.
-/
def presheafPRACatBifunctor :
    Cat.{v_J, u_J}ᵒᵖ ⥤
      (Cat.{v_I, u_I}ᵒᵖ ⥤
        Cat.{max u_I u_J w_I w',
          max u_I u_J v_I v_J (w_I + 1) (w' + 1)}) :=
  catHomProfunctor.{v_J, u_J,
      max w' u_I w_I,
      max (w' + 1) (w_I + 1) v_I u_I} ⋙
    ccrPresheafWhiskerLeft.{u_I, v_I, u_J, v_J, w_I, w'}

/--
The functor `Catᵒᵖ ⥤ Cat` sending `I` to the category
of presheaf PRAs from `Iᵒᵖ ⥤ Type w_I` to a presheaf
category on `J`.
-/
def presheafPRACatFunctor :
    Cat.{v_I, u_I}ᵒᵖ ⥤
    Cat.{max u_I u_J w_I w', max u_I u_J v_I v_J (w_I + 1) (w' + 1)} :=
  (presheafPRACatBifunctor.{u_I, v_I, u_J, v_J, w_I, w'}).obj
    (Opposite.op (Cat.of Jᵒᵖ))

/--
The category of presheaf polynomial functors (parametric
right adjoints) from `Iᵒᵖ ⥤ Type w_I` to a presheaf
category on `J`.

An object is a functor
`Jᵒᵖ ⥤ CoprodCovarRepCat (Iᵒᵖ ⥤ Type w_I)`.
At each `j : Jᵒᵖ`, this gives a polynomial
`(A(j), E_j : A(j) → (Iᵒᵖ ⥤ Type w_I))`.  The functor
action on morphisms in `Jᵒᵖ` provides reindexing on
positions and precomposition maps on directions.
-/
def PresheafPRACat :
    Cat.{max u_I u_J w_I w', max u_I u_J v_I v_J (w_I + 1) (w' + 1)} :=
  (presheafPRACatFunctor.{u_I, v_I, u_J, v_J, w_I, w'} (J := J)).obj
    (Opposite.op (Cat.of Iᵒᵖ))

end PresheafPRADef

/-! ## Accessors -/

section PresheafPRAAccessors

/--
The uncurried form of `presheafPRACatBifunctor`, as a functor
`Catᵒᵖ × Catᵒᵖ ⥤ Cat`.  Used as the base category for the
`Grothendieck`-indexed natural transformations `praDirectionsNatOp`
and `praDirectionsNat`.
-/
def presheafPRACatBifunctorUncurried :
    (Cat.{v_J, u_J}ᵒᵖ × Cat.{v_I, u_I}ᵒᵖ) ⥤
      Cat.{max u_I u_J w_I w',
        max u_I u_J v_I v_J (w_I + 1) (w' + 1)} :=
  Functor.uncurry.obj
    presheafPRACatBifunctor.{u_I, v_I, u_J, v_J, w_I, w'}

/--
The `(Cat × Cat)ᵒᵖ`-indexed form of `presheafPRACatBifunctorUncurried`,
obtained by precomposing with `prodOpEquiv.functor :
(Cat × Cat)ᵒᵖ ≌ Catᵒᵖ × Catᵒᵖ`.  Used as the base functor for
`FunctorFromDataContra`-based natural transformations.
-/
def presheafPRACatBifunctorUncurriedOp :
    (Cat.{v_J, u_J} × Cat.{v_I, u_I})ᵒᵖ ⥤
      Cat.{max u_I u_J w_I w',
        max u_I u_J v_I v_J (w_I + 1) (w' + 1)} :=
  (prodOpEquiv (C := Cat.{v_J, u_J})
      (D := Cat.{v_I, u_I})).functor ⋙
    presheafPRACatBifunctorUncurried.{u_I, v_I, u_J, v_J, w_I, w'}

/--
Per-`(J, I)` fibre functor for `sourceData`.  Sends
`P : J ⥤ CoprodCovarRepCat (presheafCatFunctor.obj (op I))` to the
category of elements of its positions presheaf
`P ⋙ ccrNewIndexFunctor _`, universe-widened so that all fibres live
in the same `Cat` universe.

Factored out so that its universe annotations are visible.
-/
private def sourceDataFib
    (JI : Cat.{v_J, u_J} × Cat.{v_I, u_I}) :
    ↑(presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J, w_I, w'}.obj
        (Opposite.op JI)) ⥤
      Cat.{max u_I u_J v_J w_I w',
        max u_I u_J v_I v_J (w_I + 1) (w' + 1)} :=
  (Functor.whiskeringRight JI.1.α _ _).obj
      (ccrNewIndexFunctor.{max v_I u_I (w_I + 1),
        max u_I w_I, w'}
        (↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
          (Opposite.op JI.2)))) ⋙
    Functor.elementsFunctor ⋙
    catULiftFunctor2.{max u_J w', v_J, max u_I u_J w_I w',
      max u_I v_I v_J (w_I + 1) (w' + 1)}

/--
The composite `(F.map f.op).obj P ⋙ ccrNewIndexFunctor _` equals
`f_J ⋙ P ⋙ ccrNewIndexFunctor _` definitionally — the I-side
transport on PRAs preserves `ccrNewIndexFunctor` on the nose, by the
same property underlying `ccrNewIndexNat`.
-/
private theorem sourceData_base_change_eq
    {JI₁ JI₂ : Cat.{v_J, u_J} × Cat.{v_I, u_I}}
    (f : JI₁ ⟶ JI₂)
    (P : ↑(presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'}.obj (Opposite.op JI₂))) :
    ((presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'}.map f.op).toFunctor.obj P) ⋙
        ccrNewIndexFunctor.{max v_I u_I (w_I + 1), max u_I w_I, w'}
          (↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
            (Opposite.op JI₁.2))) =
      f.1.toFunctor ⋙ P ⋙
        ccrNewIndexFunctor.{max v_I u_I (w_I + 1), max u_I w_I, w'}
          (↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
            (Opposite.op JI₂.2))) :=
  rfl

/--
Per-morphism component of `sourceData.hom`.  For `f : JI₁ ⟶ JI₂`
in `Cat × Cat` and `P : F.obj (op JI₂)`, the functor
`(sourceDataFib JI₁).obj ((F.map f.op).obj P) ⟶ (sourceDataFib JI₂).obj P`
obtained by widening `elementsPrecomp f.1.toFunctor`.
-/
private def sourceDataHomApp
    {JI₁ JI₂ : Cat.{v_J, u_J} × Cat.{v_I, u_I}} (f : JI₁ ⟶ JI₂)
    (P : ↑(presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'}.obj (Opposite.op JI₂))) :
    (sourceDataFib.{u_I, v_I, u_J, v_J, w_I, w'} JI₁).obj
        ((presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
          w_I, w'}.map f.op).toFunctor.obj P) ⟶
      (sourceDataFib.{u_I, v_I, u_J, v_J, w_I, w'} JI₂).obj P :=
  (catULiftFunctor2.{max u_J w', v_J, max u_I u_J w_I w',
    max u_I v_I v_J (w_I + 1) (w' + 1)}).map
      (CategoryTheory.elementsPrecomp
        (F := P ⋙ ccrNewIndexFunctor.{max v_I u_I (w_I + 1),
          max u_I w_I, w'}
          (↑(presheafCatFunctor.{u_I, v_I, w_I}.obj
            (Opposite.op JI₂.2))))
        f.1.toFunctor).toCatHom

/--
Per-morphism natural-transformation component of `sourceData.hom`.
-/
private def sourceDataHom
    {JI₁ JI₂ : Cat.{v_J, u_J} × Cat.{v_I, u_I}} (f : JI₁ ⟶ JI₂) :
    (presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J, w_I,
      w'}.map f.op).toFunctor ⋙
      sourceDataFib.{u_I, v_I, u_J, v_J, w_I, w'} JI₁ ⟶
      sourceDataFib.{u_I, v_I, u_J, v_J, w_I, w'} JI₂ where
  app P := sourceDataHomApp.{u_I, v_I, u_J, v_J, w_I, w'} f P
  naturality _ _ _ := by
    apply Cat.Hom.ext
    rfl

/--
Identity coherence for `sourceDataHom`.
-/
private lemma sourceData_hom_id
    (JI : Cat.{v_J, u_J} × Cat.{v_I, u_I}) :
    sourceDataHom.{u_I, v_I, u_J, v_J, w_I, w'} (𝟙 JI) =
      eqToHom (by
        rw [show (𝟙 JI : JI ⟶ JI).op = 𝟙 (Opposite.op JI) from rfl]
        rw [presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
          w_I, w'}.map_id]
        rfl) := by
  apply NatTrans.ext
  funext P
  simp only [sourceDataHom, sourceDataHomApp,
    CategoryTheory.eqToHom_app]
  apply Cat.Hom.ext
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro _; rfl
  · intros _ _ _
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/--
Composition coherence for `sourceDataHom`.
-/
private lemma sourceData_hom_comp
    {JI₁ JI₂ JI₃ : Cat.{v_J, u_J} × Cat.{v_I, u_I}}
    (f : JI₁ ⟶ JI₂) (g : JI₂ ⟶ JI₃) :
    sourceDataHom.{u_I, v_I, u_J, v_J, w_I, w'} (f ≫ g) =
      eqToHom (by
        rw [show (f ≫ g : JI₁ ⟶ JI₃).op = g.op ≫ f.op from rfl]
        rw [presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
          w_I, w'}.map_comp]
        rfl) ≫
      Functor.whiskerLeft
        (presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
          w_I, w'}.map g.op).toFunctor
        (sourceDataHom.{u_I, v_I, u_J, v_J, w_I, w'} f) ≫
      sourceDataHom.{u_I, v_I, u_J, v_J, w_I, w'} g := by
  apply NatTrans.ext
  funext P
  simp only [sourceDataHom, sourceDataHomApp,
    CategoryTheory.eqToHom_app, NatTrans.comp_app,
    Functor.whiskerLeft_app]
  apply Cat.Hom.ext
  refine CategoryTheory.Functor.ext ?_ ?_
  · intro _; rfl
  · intros _ _ _
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    rfl

/--
Source data for the directions natural transformation, packaged via
the contravariant `FunctorFromDataContra` infrastructure.

At each pair `(J, I) : Cat × Cat`, the fibre is a functor
`PresheafPRACat I J ⥤ Cat` sending `P` to
`(P ⋙ ccrNewIndexFunctor (presheafCat I)).Elements` universe-widened
to land in a common `Cat`.  The morphism action on `f : (J₁, I₁) ⟶
(J₂, I₂)` reduces — via the on-the-nose collapse of the I-side
transport underlying `ccrNewIndexNat` — to `elementsPrecomp f.1`
widened through `catULiftFunctor2`.
-/
private def sourceData :
    FunctorFromDataContra
      presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J, w_I, w'}
      (T := Cat.{max u_I u_J v_J w_I w',
        max u_I u_J v_I v_J (w_I + 1) (w' + 1)}) where
  fib JI := sourceDataFib.{u_I, v_I, u_J, v_J, w_I, w'} JI
  hom f := sourceDataHom.{u_I, v_I, u_J, v_J, w_I, w'} f
  hom_id _ := sourceData_hom_id.{u_I, v_I, u_J, v_J, w_I, w'} _
  hom_comp _ _ :=
    sourceData_hom_comp.{u_I, v_I, u_J, v_J, w_I, w'} _ _

/--
Per-`I` target fibre for `praPolyDirectionsTarget`.  Sends `op I` to
the universe-widened opposite of presheaves on `I`.

The four-stage pipeline is `Cat.opFunctor.op ⋙ presheafCatFunctor ⋙
catULiftFunctor2 ⋙ Cat.opFunctor`, where the outer `Cat.opFunctor`
encodes the polynomial-functor-morphism backward-on-directions
convention.
-/
def praDirectionsTargetFibre :
    Cat.{v_I, u_I}ᵒᵖ ⥤
      Cat.{max u_I u_J v_J w_I w',
        max u_I u_J v_I v_J (w_I + 1) (w' + 1)} :=
  Cat.opFunctor.{v_I, u_I}.op ⋙
    presheafCatFunctor.{u_I, v_I, w_I} ⋙
    catULiftFunctor2.{max v_I (w_I + 1) u_I, max u_I w_I,
      max u_I u_J v_J w_I w',
      max u_I u_J v_I v_J (w_I + 1) (w' + 1)} ⋙
    Cat.opFunctor.{max u_I u_J v_J w_I w',
      max u_I u_J v_I v_J (w_I + 1) (w' + 1)}

/--
Total target Grothendieck for `praPolyDirectionsFunctor`.

Objects are pairs `(I, x)` where `x : (widened Iᵒᵖ ⥤ Type w_I)ᵒᵖ`.
Morphisms `(I₁, x₁) ⟶ (I₂, x₂)` are pairs `(f : I₁ ⟶ I₂,
η : x₁ ⟶ (praDirectionsTargetFibre.map f.op).obj x₂)`, encoding the
polynomial-functor-morphism backward-on-directions convention.
-/
def praPolyDirectionsTarget :
    Cat.{max u_I u_J v_I v_J w_I w',
      max (u_I + 1) (v_I + 1) u_J v_J (w_I + 1) (w' + 1)} :=
  (grothendieckContraFunctor Cat.{v_I, u_I}).obj
    praDirectionsTargetFibre.{u_I, v_I, u_J, v_J, w_I, w'}

/--
Total source Grothendieck for `praPolyDirectionsFunctor`.

Objects are 4-tuples: a base object of
`(grothendieckContraFunctor (Cat × Cat)).obj
presheafPRACatBifunctorUncurriedOp` — itself a triple `((J, I), P)` —
together with an element of the widened `(P ⋙ ccrNewIndexFunctor
_).Elements`.
-/
def praPolyDirectionsSource :
    Cat.{max u_I u_J v_I v_J w_I w',
      max (u_I + 1) (v_I + 1) (u_J + 1) (v_J + 1) (w_I + 1)
        (w' + 1)} :=
  Cat.of (Grothendieck
    (functorFromDataContra sourceData.{u_I, v_I, u_J, v_J, w_I, w'}))

/--
Base functor of `praPolyDirectionsData`.  Projects a source-base
object `((J, I), P)` to its `I`-component and a base morphism `f`
to its `I`-component `f.unop.base.unop.2`.
-/
private def praPolyDirectionsData_baseFib :
    (grothendieckContraFunctor
        (Cat.{v_J, u_J} × Cat.{v_I, u_I})).obj
      presheafPRACatBifunctorUncurriedOp.{u_I, v_I, u_J, v_J,
        w_I, w'} ⥤
      Cat.{v_I, u_I} where
  obj X := (GrothendieckContraFunctor.objBase X).2
  map f := (GrothendieckContraFunctor.homBase f).2
  map_id _ := rfl
  map_comp _ _ := rfl

/--
Target bifunctor of `praPositionsNat`.  Sends each
`(J, I) : Cat.{v_J, u_J}ᵒᵖ × Cat.{v_I, u_I}ᵒᵖ` to the
universe-widened form of `Jᵒᵖ ⥤ Type w'`, constant in `I`.

Constant in `I` because the action of `presheafPRACatBifunctor.map`
on `I`-morphisms preserves the positions types on the nose — the
same property of `coprodCovarRepFunctor.map` established in
`ccrNewIndexNat`.
-/
def praPositionsNatTarget :
    Cat.{v_J, u_J}ᵒᵖ ⥤
      (Cat.{v_I, u_I}ᵒᵖ ⥤
        Cat.{max u_I u_J w_I w',
          max u_I u_J v_I v_J (w_I + 1) (w' + 1)}) :=
  presheafCatFunctor.{u_J, v_J, w'} ⋙
    catULiftFunctor2.{max v_J (w' + 1) u_J, max u_J w',
      max u_I w_I, max u_I v_I (w_I + 1)} ⋙
    Functor.const Cat.{v_I, u_I}ᵒᵖ

/--
Per-`(J, I)` component of `praPositionsNat`.  Factored out so that
its universe annotations are visible.  Sends a PRA
`P : J.unop ⥤ CoprodCovarRepCat (presheafCat I.unop)` to the
widened presheaf of positions, by whiskering
`ccrNewIndexFunctor (presheafCat I.unop)` over `J.unop` and then
post-composing with the `ULift`/`ULiftHom` widening lifts.
-/
private def praPositionsNatAppFunctor
    (J : Cat.{v_J, u_J}ᵒᵖ) (I : Cat.{v_I, u_I}ᵒᵖ) :
    (↑J.unop ⥤ ↑(ccrPresheafCatFunctor.{u_I, v_I, w_I, w'}.obj I)) ⥤
      ↑(catULiftFunctor2.{max v_J (w' + 1) u_J, max u_J w',
          max u_I w_I,
          max u_I v_I (w_I + 1)}.obj
        (presheafCatFunctor.{u_J, v_J, w'}.obj J)) :=
  (Functor.whiskeringRight ↑J.unop _ _).obj
    (ccrNewIndexFunctor.{max v_I u_I (w_I + 1),
      max u_I w_I, w'}
      ↑(presheafCatFunctor.{u_I, v_I, w_I}.obj I)) ⋙
    CategoryTheory.ULift.upFunctor ⋙
    CategoryTheory.ULiftHom.up

private def praPositionsNatApp
    (J : Cat.{v_J, u_J}ᵒᵖ) (I : Cat.{v_I, u_I}ᵒᵖ) :
    (presheafPRACatBifunctor.{u_I, v_I, u_J, v_J, w_I, w'}.obj
        J).obj I ⟶
      (praPositionsNatTarget.{u_I, v_I, u_J, v_J, w_I, w'}.obj
        J).obj I :=
  (praPositionsNatAppFunctor.{u_I, v_I, u_J, v_J, w_I, w'}
    J I).toCatHom

/--
The natural transformation packaging the positions functors of all
presheaf PRAs, natural in both `I` and `J`.  Source:
`presheafPRACatBifunctor`.  Target: `praPositionsNatTarget`.

Each `(praPositionsNat.app J).app I` is the underlying functor
`PresheafPRACat I J ⥤ (widened Jᵒᵖ ⥤ Type w')` obtained by
whiskering `ccrNewIndexFunctor (presheafCat I)` with `Jᵒᵖ` and
post-composing with the universe-widening lifts used by
`praPositionsNatTarget`.

Naturality in `I` reduces (via `ccrNewIndexNat`) to the
index-preservation property of `coprodCovarRepFunctor.map`.
Naturality in `J` follows from `Functor.whiskeringRight`'s
functoriality; `ccrNewIndexNat` has no `J`-dependence.
-/
def praPositionsNat :
    presheafPRACatBifunctor.{u_I, v_I, u_J, v_J, w_I, w'} ⟶
      praPositionsNatTarget.{u_I, v_I, u_J, v_J, w_I, w'} where
  app J :=
    { app := fun I =>
        praPositionsNatApp.{u_I, v_I, u_J, v_J, w_I, w'} J I
      naturality := fun I₁ I₂ F => by
        apply Cat.Hom.ext
        rfl }
  naturality J₁ J₂ G := by
    apply NatTrans.ext
    funext I
    apply Cat.Hom.ext
    rfl

/--
Bridge lemma: each `(praPositionsNat.app J).app I`, viewed as an
underlying functor, equals the whiskered `ccrNewIndexFunctor` form
post-composed with the universe-widening lifts used by
`praPositionsNatTarget`.

Not marked `@[simp]` to avoid unfolding cycles.  Intended for
downstream users who want to reach through the widening to the
underlying non-widened form.
-/
theorem praPositionsNat_app_eq_presheafCatFunctor
    (I : Type u_I) [Category.{v_I} I]
    (J : Type u_J) [Category.{v_J} J] :
    ((praPositionsNat.{u_I, v_I, u_J, v_J, w_I, w'}.app
        (Opposite.op (Cat.of Jᵒᵖ))).app
      (Opposite.op (Cat.of Iᵒᵖ))).toFunctor =
      (Functor.whiskeringRight Jᵒᵖ _ _).obj
        (ccrNewIndexFunctor.{max v_I u_I (w_I + 1),
          max u_I w_I, w'}
          (↑(presheafCat.{u_I, v_I, w_I} I))) ⋙
        CategoryTheory.ULift.upFunctor ⋙
        CategoryTheory.ULiftHom.up := by
  rfl

/--
Bridge to the non-widened form of the positions presheaf.
Equivalent to `(praPositionsNat.app (Opposite.op (Cat.of Jᵒᵖ))).app
(Opposite.op (Cat.of Iᵒᵖ)) |>.toFunctor.obj P` composed with the
`ULift`/`ULiftHom`-unwrap that reverses the widening used in
`praPositionsNatTarget`.  Serves `praDirectionsAtFunctor*` and
`praDirectionsAt`, which need the underlying `Jᵒᵖ ⥤ Type w'` form.
-/
def praPositionsPresheaf
    (I : Type u_I) [Category.{v_I} I]
    (J : Type u_J) [Category.{v_J} J]
    (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J) :
    Jᵒᵖ ⥤ Type w' :=
  ((Functor.whiskeringRight Jᵒᵖ _ _).obj
    (ccrNewIndexFunctor.{max v_I u_I (w_I + 1),
      max u_I w_I, w'}
      (↑(presheafCat.{u_I, v_I, w_I} I)))).obj P

variable (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)

/--
The type of positions at stage `j`.
-/
def praPositions (j : Jᵒᵖ) : Type w' :=
  (praPositionsPresheaf I J P).obj j

/--
The directions functor into `PSh(I)ᵒᵖ`: for a fixed
PRA `P`, sends an element `(j, a)` of the positions
presheaf to `op (E_T(j,a))`.
-/
def praDirectionsAtFunctorOp :
    (praPositionsPresheaf I J P).Elements ⥤
      (Iᵒᵖ ⥤ Type w_I)ᵒᵖ :=
  CategoryTheory.elementsPrecomp P ⋙
    ccrNewFamilyFunctor.{max v_I u_I (w_I + 1),
      max u_I w_I, w'}
      (↑(presheafCat.{u_I, v_I, w_I} I))

/--
The directions functor `E_T` from the nLab PRA
formula: sends an element `(j, a)` of the opposite
of the positions presheaf to the directions presheaf
`E_T(j,a) : Iᵒᵖ ⥤ Type w_I`.
-/
def praDirectionsAtFunctor :
    (praPositionsPresheaf I J P).ElementsPre ⥤
      (Iᵒᵖ ⥤ Type w_I) :=
  (praDirectionsAtFunctorOp I J P).op ⋙
    unopUnop _

/--
The directions presheaf at position `a` at stage `j`.
-/
def praDirectionsAt (j : Jᵒᵖ)
    (a : praPositions I J P j) : Iᵒᵖ ⥤ Type w_I :=
  (praDirectionsAtFunctor I J P).obj
    (Opposite.op ⟨j, a⟩)

end PresheafPRAAccessors

/-! ## Pointwise Evaluation -/

section PresheafPRAEvalAt

/--
The evaluation profunctor: sends a PRA `P` to the
functor `Jᵒᵖ ⥤ (PSh(I) ⥤ Type _)` that at each `j`
evaluates the polynomial `P(j)`.
-/
def praEvalAtProfunctor :
    PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J ⥤
    Jᵒᵖ ⥤ (Iᵒᵖ ⥤ Type w_I) ⥤ Type (max w' u_I w_I) :=
  (Functor.whiskeringRight Jᵒᵖ _ _).obj
    (ccrNewEvalCatFunctor.{max v_I u_I (w_I + 1),
      max u_I w_I, w'}
      (↑(presheafCat.{u_I, v_I, w_I} I)))

/--
The evaluation functor: sends a PRA `P` to the functor
`PSh(I) ⥤ PSh(J)` (in the `Type _` form
`(Iᵒᵖ ⥤ Type w_I) ⥤ (Jᵒᵖ ⥤ Type _)`).
-/
def praEvalAtFunctor :
    PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J ⥤
    (Iᵒᵖ ⥤ Type w_I) ⥤ (Jᵒᵖ ⥤ Type (max w' u_I w_I)) :=
  praEvalAtProfunctor I J ⋙
    Functor.flipping.functor

/--
`praEvalAtProfunctor` is fully faithful: every natural
transformation between evaluation profunctors arises
from a unique PRA morphism.
-/
def praEvalAtProfunctorFullyFaithful :
    (praEvalAtProfunctor I J).FullyFaithful :=
  Functor.FullyFaithful.whiskeringRight
    (ccrNewEvalCatFullyFaithful.{max v_I u_I (w_I + 1),
      max u_I w_I, w'}
      (↑(presheafCat.{u_I, v_I, w_I} I)))
    Jᵒᵖ

/--
`praEvalAtFunctor` is fully faithful: every natural
transformation between PRA evaluation functors
`PSh(I) ⥤ PSh(J)` arises from a unique PRA morphism.
-/
def praEvalAtFunctorFullyFaithful :
    (praEvalAtFunctor I J).FullyFaithful :=
  (praEvalAtProfunctorFullyFaithful I J).comp
    Functor.flipping.fullyFaithfulFunctor

variable (P : PresheafPRACat.{u_I, v_I, u_J, v_J, w_I, w'} I J)
variable (Z : Iᵒᵖ ⥤ Type w_I)

/--
Pointwise evaluation of a presheaf PRA at a presheaf `Z` and
stage `j`.  The result is
`Σ_{a : praPositions P j} (praDirectionsAt P j a ⟶ Z)`.
-/
def praEvalAt (j : Jᵒᵖ) : Type (max w' u_I w_I) :=
  ((praEvalAtProfunctor I J).obj P).obj j |>.obj Z

/--
Extract the position index from an evaluation element.
-/
def praEvalAt_index {j : Jᵒᵖ}
    (x : praEvalAt I J P Z j) :
    praPositions I J P j :=
  x.1

/--
Extract the natural transformation from an evaluation
element.
-/
def praEvalAt_mor {j : Jᵒᵖ}
    (x : praEvalAt I J P Z j) :
    praDirectionsAt I J P j
      (praEvalAt_index I J P Z x) ⟶ Z :=
  x.2

/--
Construct an evaluation element from a position and a
natural transformation.
-/
def praEvalAt_mk (j : Jᵒᵖ)
    (a : praPositions I J P j)
    (η : praDirectionsAt I J P j a ⟶ Z) :
    praEvalAt I J P Z j :=
  ⟨a, η⟩

end PresheafPRAEvalAt

end GebLean
