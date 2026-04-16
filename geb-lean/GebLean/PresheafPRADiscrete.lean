import GebLean.Polynomial
import GebLean.PresheafPRA
import Mathlib.CategoryTheory.Discrete.Basic

/-!
# Over X as a Presheaf Category on Discrete X

The slice category `Over X` for a type `X` is equivalent to
the presheaf category `(Discrete X)ᵒᵖ ⥤ Type u`.  The
equivalence composes three steps:

1. `familySliceEquiv.symm : Over X ≌ (X → Type u)`
2. `piEquivalenceFunctorDiscrete X (Type u) :
     (X → Type u) ≌ (Discrete X ⥤ Type u)`
3. `(Discrete.opposite X).symm.congrLeft :
     (Discrete X ⥤ Type u) ≌ ((Discrete X)ᵒᵖ ⥤ Type u)`
-/

namespace GebLean

open CategoryTheory

universe u

/--
The equivalence between `Over X` and the presheaf
category `(Discrete X)ᵒᵖ ⥤ Type u`.

Composes `familySliceEquiv.symm`, which identifies
`Over X` with `X`-indexed families of types, with
`piEquivalenceFunctorDiscrete`, which identifies
families with functors out of `Discrete X`, and finally
precomposition by `(Discrete.opposite X).symm` to pass
from `Discrete X` to `(Discrete X)ᵒᵖ`.
-/
def overDiscretePresheafEquiv (X : Type u) :
    Over X ≌ ((Discrete X)ᵒᵖ ⥤ Type u) :=
  (familySliceEquiv X).symm |>.trans
    (piEquivalenceFunctorDiscrete X (Type u))
    |>.trans
    ((Discrete.opposite X).symm.congrLeft)

section CcrMapEquiv

variable {C : Type (u + 1)} [Category.{u} C]
  {D : Type (u + 1)} [Category.{u} D]
  (e : C ≌ D)

set_option backward.isDefEq.respectTransparency false in
/--
Forward functor from `CoprodCovarRepCat' C` to
`CoprodCovarRepCat' D` induced by an equivalence
`e : C ≌ D`.  Applies `e.functor` to each element
of the family.
-/
def ccrMapEquivFwd :
    CoprodCovarRepCat'.{u + 1, u, u} C ⥤
      CoprodCovarRepCat'.{u + 1, u, u} D where
  obj P := ccrObjMk (e.functor.obj ∘ ccrFamily P)
  map {P Q} f :=
    ccrHomMk (f.base) (fun i =>
      e.functor.map (ccrFiberMor f i))
  map_id P := by
    simp only [ccrId_mk, ccrHomMk, ccrFiberMor,
      ccrObjMk_family, Function.comp]
    congr 1
    funext i
    exact e.functor.map_id _
  map_comp {P Q R} f g := by
    simp only [ccrComp_mk,
      ccrHomMk_reindex, ccrHomMk_fiberMor,
      ccrComp_fiberMor, ccrReindex,
      Functor.map_comp]
    congr 1

/--
Inverse functor from `CoprodCovarRepCat' D` to
`CoprodCovarRepCat' C` induced by an equivalence
`e : C ≌ D`.  Applies `e.inverse` to each element
of the family.
-/
def ccrMapEquivInv :
    CoprodCovarRepCat'.{u + 1, u, u} D ⥤
      CoprodCovarRepCat'.{u + 1, u, u} C :=
  ccrMapEquivFwd e.symm

set_option backward.isDefEq.respectTransparency false in
/--
Component of the unit natural isomorphism for
`ccrMapEquiv` at object `P`.
-/
def ccrMapEquivUnitApp
    (P : CoprodCovarRepCat'.{u + 1, u, u} C) :
    P ≅ (ccrMapEquivFwd e ⋙
      ccrMapEquivInv e).obj P where
  hom := ccrHomMk id
    (fun i => e.unitIso.inv.app (ccrFamily P i))
  inv := ccrHomMk id
    (fun i => e.unitIso.hom.app (ccrFamily P i))
  hom_inv_id := by
    simp only [ccrComp_mk, ccrHomMk_reindex,
      ccrHomMk_fiberMor, ccrId_mk,
      Function.comp_id]
    congr 1
    funext i
    exact e.unitIso.hom_inv_id_app _
  inv_hom_id := by
    simp only [ccrComp_mk, ccrHomMk_reindex,
      ccrHomMk_fiberMor, ccrId_mk,
      Function.comp_id]
    congr 1
    funext i
    exact e.unitIso.inv_hom_id_app _

set_option backward.isDefEq.respectTransparency false in
/--
Component of the counit natural isomorphism for
`ccrMapEquiv` at object `Q`.
-/
def ccrMapEquivCounitApp
    (Q : CoprodCovarRepCat'.{u + 1, u, u} D) :
    (ccrMapEquivInv e ⋙
      ccrMapEquivFwd e).obj Q ≅ Q where
  hom := ccrHomMk id
    (fun i => e.counitIso.inv.app (ccrFamily Q i))
  inv := ccrHomMk id
    (fun i => e.counitIso.hom.app (ccrFamily Q i))
  hom_inv_id := by
    simp only [ccrComp_mk, ccrHomMk_reindex,
      ccrHomMk_fiberMor, ccrId_mk,
      Function.comp_id]
    congr 1
    funext i
    exact e.counitIso.hom_inv_id_app _
  inv_hom_id := by
    simp only [ccrComp_mk, ccrHomMk_reindex,
      ccrHomMk_fiberMor, ccrId_mk,
      Function.comp_id]
    congr 1
    funext i
    exact e.counitIso.inv_hom_id_app _

set_option backward.isDefEq.respectTransparency false in
/--
The unit natural isomorphism for `ccrMapEquiv`.
-/
def ccrMapEquivUnit :
    𝟭 (CoprodCovarRepCat'.{u + 1, u, u} C) ≅
      ccrMapEquivFwd e ⋙ ccrMapEquivInv e :=
  NatIso.ofComponents (ccrMapEquivUnitApp e)
    (fun {P Q} f => by
      simp only [ccrComp_mk, Functor.id_map,
        Functor.comp_map, ccrMapEquivFwd,
        ccrMapEquivInv, ccrMapEquivFwd,
        ccrHomMk_reindex, ccrHomMk_fiberMor,
        ccrMapEquivUnitApp, ccrObjMk_family,
        Function.comp]
      congr 1
      funext i
      exact (e.unitIso.inv.naturality
        (ccrFiberMor f i)).symm)

set_option backward.isDefEq.respectTransparency false in
/--
The counit natural isomorphism for `ccrMapEquiv`.
-/
def ccrMapEquivCounit :
    ccrMapEquivInv e ⋙ ccrMapEquivFwd e ≅
      𝟭 (CoprodCovarRepCat'.{u + 1, u, u} D) :=
  NatIso.ofComponents (ccrMapEquivCounitApp e)
    (fun {P Q} f => by
      simp only [ccrComp_mk, Functor.id_map,
        Functor.comp_map, ccrMapEquivFwd,
        ccrMapEquivInv, ccrMapEquivFwd,
        ccrHomMk_reindex, ccrHomMk_fiberMor,
        ccrMapEquivCounitApp, ccrObjMk_family,
        Function.comp]
      congr 1
      funext i
      exact (e.counitIso.inv.naturality
        (ccrFiberMor f i)).symm)

set_option backward.isDefEq.respectTransparency false in
/--
The equivalence `CoprodCovarRepCat' C ≌
CoprodCovarRepCat' D` induced by `e : C ≌ D`.
Applies `e.functor` / `e.inverse` pointwise to each
family element.
-/
def ccrMapEquiv :
    CoprodCovarRepCat'.{u + 1, u, u} C ≌
      CoprodCovarRepCat'.{u + 1, u, u} D where
  functor := ccrMapEquivFwd e
  inverse := ccrMapEquivInv e
  unitIso := ccrMapEquivUnit e
  counitIso := ccrMapEquivCounit e
  functor_unitIso_comp P := by
    simp only [ccrComp_mk, ccrMapEquivFwd,
      ccrHomMk_reindex, ccrHomMk_fiberMor,
      ccrMapEquivUnit, ccrMapEquivUnitApp,
      ccrMapEquivCounit, ccrMapEquivCounitApp,
      NatIso.ofComponents, ccrObjMk_family,
      Function.comp, ccrId_mk]
    congr 1
    funext i
    simp only [ccrHomMk, id]
    let x := ccrFamily P i
    have h := e.functor_unitIso_comp x
    rw [← cancel_mono
      (e.functor.map (e.unitIso.hom.app x) ≫
        e.counitIso.hom.app
          (e.functor.obj x))]
    simp [h]

end CcrMapEquiv

/--
The equivalence between `CoprodCovarRepCat' (Over X)`
and `CoprodCovarRepCat ((Discrete X)ᵒᵖ ⥤ Type u)`.

Composes three equivalences:
1. `ccrMapEquiv (overDiscretePresheafEquiv X)`
   transfers from `Over X` families to presheaf families
   at the `CoprodCovarRepCat'` level.
2. `ccrOp'OpEquiv` transfers from the `op'`-based to
   the `op`-based coproduct-of-covariant-representables
   category.
-/
def ccrOverDiscreteEquiv (X : Type u) :
    CoprodCovarRepCat'.{u + 1, u, u} (Over X) ≌
      CoprodCovarRepCat.{u + 1, u, u}
        ((Discrete X)ᵒᵖ ⥤ Type u) :=
  (ccrMapEquiv (overDiscretePresheafEquiv X)).trans
    (ccrOp'OpEquiv ((Discrete X)ᵒᵖ ⥤ Type u))

section PolyPresheafEquiv

variable (X Y : Type u)

/--
The equivalence between `PolyFunctorBetweenCat X Y`
and `PresheafPRACat (Discrete X) (Discrete Y)`.

Composes three categorical equivalences:
1. `piEquivalenceFunctorDiscrete Y` converts
   `Y`-indexed families to functors out of
   `Discrete Y`.
2. `(Discrete.opposite Y).symm.congrLeft` converts
   functors out of `Discrete Y` to functors out
   of `(Discrete Y)^op`.
3. `(ccrOverDiscreteEquiv X).congrRight` applies
   the inner equivalence
   `CoprodCovarRepCat' (Over X) ≌
     CoprodCovarRepCat ((Discrete X)^op ⥤ Type u)`
   pointwise.
-/
def polyBetweenPresheafPRAEquiv :
    PolyFunctorBetweenCat.{u} X Y ≌
      PresheafPRACat.{u, u, u, u, u, u}
        (Discrete X) (Discrete Y) :=
  (piEquivalenceFunctorDiscrete Y
    (↑(CoprodCovarRepCat'.{u + 1, u, u}
      (Over X)))).trans
    (((Discrete.opposite Y).symm.congrLeft).trans
      ((ccrOverDiscreteEquiv X).congrRight))

end PolyPresheafEquiv

/-! ## Evaluation Compatibility

The equivalence `polyBetweenPresheafPRAEquiv` is compatible
with evaluation: the polynomial evaluation
`polyBetweenEvalFunctor` on `Over X ⥤ Over Y` corresponds
to the presheaf PRA evaluation `praEvalAtFunctor` on
`PSh(Discrete X) ⥤ PSh(Discrete Y)`, conjugated by the
presheaf equivalences `overDiscretePresheafEquiv` on domain
and codomain.

We state this compatibility at the level of individual
fibers:  for each `P : PolyFunctorBetweenCat X Y`,
`A : Over X`, and `y : Y`, the type
`polyBetweenEvalFamily X Y P A y` (the fiber of the
polynomial evaluation at `y`) is equivalent to the
corresponding presheaf PRA evaluation fiber.
-/

section EvalCompat

variable (X Y : Type u)

/--
The presheaf PRA obtained from a polynomial
`P : PolyFunctorBetweenCat X Y` under the equivalence
`polyBetweenPresheafPRAEquiv`.
-/
abbrev polyToPRA (P : PolyFunctorBetweenCat.{u} X Y) :
    PresheafPRACat.{u, u, u, u, u, u}
      (Discrete X) (Discrete Y) :=
  (polyBetweenPresheafPRAEquiv X Y).functor.obj P

/--
The presheaf obtained from `A : Over X` under the
equivalence `overDiscretePresheafEquiv`.
-/
abbrev overToPSh (A : Over X) :
    (Discrete X)ᵒᵖ ⥤ Type u :=
  (overDiscretePresheafEquiv X).functor.obj A

variable (P : PolyFunctorBetweenCat.{u} X Y)
  (A : Over X) (y : Y)

/--
The fiber of the polynomial evaluation at `y` maps
to the corresponding presheaf PRA evaluation fiber
via the equivalences.  This is the forward direction
of the fiber-level compatibility between
`polyBetweenEvalFamily` and `praEvalAt`.

The polynomial evaluation fiber is
`Σ i : ccrIndex (P y), (ccrFamily (P y) i ⟶ A)`.
The presheaf PRA evaluation fiber is
`Σ i : ccrNewIndex Q, (ccrNewFamily Q i ⟶ Z)`
where `Q` is the translated polynomial at `y` and
`Z` is the translated presheaf.
-/
def evalCompatFwd :
    polyBetweenEvalFamily X Y P A y →
    praEvalAt (Discrete X) (Discrete Y)
      (polyToPRA X Y P) (overToPSh X A)
      (Opposite.op (Discrete.mk y)) := by
  intro ⟨i, f⟩
  exact ⟨i, (overDiscretePresheafEquiv X).functor.map
    f⟩

/--
The presheaf PRA evaluation fiber at `y` is in
bijection with the polynomial evaluation fiber at
`y`.  The bijection maps index components by the
identity and morphism components via the functor
`(overDiscretePresheafEquiv X).functor`.
-/
def evalCompatEquiv :
    polyBetweenEvalFamily X Y P A y ≃
    praEvalAt (Discrete X) (Discrete Y)
      (polyToPRA X Y P) (overToPSh X A)
      (Opposite.op (Discrete.mk y)) where
  toFun := evalCompatFwd X Y P A y
  invFun := fun ⟨i, f⟩ =>
    let ff := Equivalence.fullyFaithfulFunctor
      (overDiscretePresheafEquiv X)
    ⟨i, ff.preimage f⟩
  left_inv := by
    intro ⟨i, f⟩
    simp only [evalCompatFwd]
    congr 1
  right_inv := by
    intro ⟨i, f⟩
    simp only [evalCompatFwd]
    congr 1
    exact Functor.FullyFaithful.map_preimage
      (Equivalence.fullyFaithfulFunctor
        (overDiscretePresheafEquiv X)) f

/--
Naturality of `evalCompatFwd` in `A`: for a morphism
`f : A ⟶ B` in `Over X`, the square

```
  polyBetweenEvalFamily P A y --evalCompatFwd-> praEvalAt ... A y
           |                                       |
  polyBetweenEvalFamilyMap    praEvalAt ... (map f)
           |                                       |
           v                                       v
  polyBetweenEvalFamily P B y --evalCompatFwd-> praEvalAt ... B y
```

commutes.
-/
lemma evalCompatFwd_natural
    {A B : Over X} (f : A ⟶ B)
    (x : polyBetweenEvalFamily X Y P A y) :
    evalCompatFwd X Y P B y
      (polyBetweenEvalFamilyMap X Y P f y x) =
    ccrNewEvalMap
      ((overDiscretePresheafEquiv X).functor.map
        f)
      (evalCompatFwd X Y P A y x) := by
  obtain ⟨i, g⟩ := x
  simp only [evalCompatFwd,
    polyBetweenEvalFamilyMap,
    polyToOverEvalFamilyMap, ccrEvalMap,
    ccrNewEvalMap]
  congr 1

/--
The `Y`-indexed family of presheaf PRA evaluation
fibers, obtained by evaluating the translated
polynomial `polyToPRA X Y P` at the translated
presheaf `overToPSh X A` for each `y : Y`.
-/
def praEvalFamily :
    Y → Type u :=
  fun y => praEvalAt (Discrete X) (Discrete Y)
    (polyToPRA X Y P) (overToPSh X A)
    (Opposite.op (Discrete.mk y))

/--
Object-level compatibility: the polynomial evaluation
`polyBetweenEval X Y P A : Over Y` is isomorphic (in
`Over Y`) to the object obtained from the presheaf PRA
evaluation fibers via `familySliceForward`.

The isomorphism is induced by the fiberwise
equivalence `evalCompatEquiv`.
-/
def evalCompatOverIso :
    polyBetweenEval X Y P A ≅
    (familySliceForward Y).obj
      (praEvalFamily X Y P A) := by
  unfold polyBetweenEval polyToOverEval
    praEvalFamily
  exact (familySliceForward Y).mapIso
    (Pi.isoMk (fun y =>
      (evalCompatEquiv X Y P A y).toIso))

end EvalCompat

end GebLean
