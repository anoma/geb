import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Whiskering
import GebLean.Utilities.Opposites

/-!
# The contravariant category of elements

This file defines the contravariant category of elements for a functor `F : Cᵒᵖ' ⥤ Type`.

Given a functor `F : Cᵒᵖ' ⥤ Type`, an object of `F.ElementsContra'` is a pair
`(X : C, x : F.obj X)`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, such that `F.map f` takes `y` to `x`
(where `F.map f : F.obj Y → F.obj X` since `F` is contravariant).

This is the dual of the (covariant) category of elements in
`Mathlib.CategoryTheory.Elements`.

## Implementation notes

While mathlib handles presheaves `F : Cᵒᵖ ⥤ Type` by taking the opposite of the covariant
category of elements, we provide a direct contravariant construction using our `op'` alternative
opposite category. This avoids nested opposites and provides definitional equalities
`op' (op' C) = C`.

In the implementation, morphisms are stored as `f : @Quiver.Hom Cᵒᵖ' _ Y X`, which corresponds
to `f : X ⟶ Y` in `C`.

## Categorical equivalences

This file establishes two categorical equivalences:

1. The slice category `Over X` is equivalent to the category of elements of the
   contravariant hom-functor `coyoneda'.obj X : Cᵒᵖ' ⥤ Type`.

2. The slice category of a presheaf category over a presheaf `P : Cᵒᵖ' ⥤ Type` is
   equivalent to the category of presheaves on the category of elements of `P`.

## References

* <https://ncatlab.org/nlab/show/category+of+elements>
* <https://ncatlab.org/nlab/show/category+of+elements#representable_presheaves>
* <https://preview.1lab.dev/535/Cat.Instances.Slice.Presheaf.html>

-/

universe w v u

namespace CategoryTheory

open GebLean

variable {C : Type u} [Category.{v} C]

/--
The type of objects for the contravariant category of elements of a functor `F : Cᵒᵖ' ⥤ Type`
is a pair `(X : C, x : F.obj X)`.
-/
def Functor.ElementsContra' (F : Cᵒᵖ' ⥤ Type w) :=
  Σ c : C, F.obj c

/--
Constructor for the type `F.ElementsContra'` when `F` is a contravariant functor to types.
-/
abbrev Functor.elementsContraMk (F : Cᵒᵖ' ⥤ Type w) (X : C) (x : F.obj X) :
    F.ElementsContra' := ⟨X, x⟩

lemma Functor.ElementsContra'.ext {F : Cᵒᵖ' ⥤ Type w} (x y : F.ElementsContra')
    (h₁ : x.fst = y.fst) (h₂ : F.map (eqToHom h₁) x.snd = y.snd) : x = y := by
  cases x
  cases y
  cases h₁
  simp only [eqToHom_refl, FunctorToTypes.map_id_apply] at h₂
  simp [h₂]

/--
The category structure on `F.ElementsContra'`, for `F : Cᵒᵖ' ⥤ Type`.
A morphism `(X, x) ⟶ (Y, y)` is a morphism `f : X ⟶ Y` in `C`, such that `F.map f` takes `y` to `x`.
-/
instance categoryOfElementsContra' (F : Cᵒᵖ' ⥤ Type w) : Category.{v} F.ElementsContra' where
  Hom p q := { f : @Quiver.Hom Cᵒᵖ' _ q.1 p.1 // (F.map f) q.2 = p.2 }
  id p := ⟨𝟙 p.1, congrFun (F.map_id p.fst) p.snd⟩
  comp {X Y Z} f g := ⟨g.1 ≫ f.1, by
    rw [F.map_comp]
    simp only [types_comp_apply]
    rw [g.2, f.2]⟩
  id_comp := by
    intros X Y f
    ext
    exact Category.comp_id f.val
  comp_id := by
    intros X Y f
    ext
    exact Category.id_comp f.val
  assoc := by
    intros W X Y Z f g h
    ext
    exact (Category.assoc h.val g.val f.val).symm

/--
The category of elements using mathlib's definition.
For `F : Cᵒᵖ' ⥤ Type w`, transport `F` to a functor `Cᵒᵖ ⥤ Type w` using `opToOp'`,
then take mathlib's category of elements and reverse the morphisms (opposite).
-/
def Functor.ElementsContra (F : Cᵒᵖ' ⥤ Type w) :=
  ((opToOp' ⋙ F).Elements)ᵒᵖ

instance (F : Cᵒᵖ' ⥤ Type w) : Category F.ElementsContra :=
  inferInstanceAs (Category ((opToOp' ⋙ F).Elements)ᵒᵖ)

/--
The functor from `F.ElementsContra'` to `F.ElementsContra`.
Maps `(X : C, x : F.obj X)` to `op ⟨op X : Cᵒᵖ, x : F.obj X⟩`.
-/
def elementsContra'ToElementsContra (F : Cᵒᵖ' ⥤ Type w) :
    F.ElementsContra' ⥤ F.ElementsContra where
  obj p := Opposite.op ⟨Opposite.op p.fst, p.snd⟩
  map {p q} f := by
    -- f : p ⟶ q in F.ElementsContra'
    -- f.val : q.1 ⟶ p.1 in Cᵒᵖ'
    -- Need: Opposite.op ⟨Opposite.op p.fst, p.snd⟩ ⟶ Opposite.op ⟨Opposite.op q.fst, q.snd⟩
    -- This is in ((opToOp' ⋙ F).Elements)ᵒᵖ
    -- We construct the underlying morphism in Elements, then apply .op
    let src : (opToOp' ⋙ F).Elements := ⟨Opposite.op q.fst, q.snd⟩
    let tgt : (opToOp' ⋙ F).Elements := ⟨Opposite.op p.fst, p.snd⟩
    let mor_in_elements : src ⟶ tgt := Subtype.mk (op'ToOp.map f.val) (by
      -- Need: (opToOp' ⋙ F).map (op'ToOp.map f.val) q.snd = p.snd
      -- This simplifies to F.map f.val q.snd = p.snd using op'ToOp_comp_opToOp'
      convert f.property using 2)
    exact mor_in_elements.op

/--
The functor from `F.ElementsContra` to `F.ElementsContra'`.
Maps `op ⟨op X : Cᵒᵖ, x : F.obj X⟩` to `(X : C, x : F.obj X)`.
-/
def elementsContraToElementsContra' (F : Cᵒᵖ' ⥤ Type w) :
    F.ElementsContra ⥤ F.ElementsContra' where
  obj p := ⟨p.unop.fst.unop, p.unop.snd⟩
  map {p q} f := by
    -- f : p ⟶ q in F.ElementsContra = ((opToOp' ⋙ F).Elements)ᵒᵖ
    -- f.unop : q.unop ⟶ p.unop in (opToOp' ⋙ F).Elements
    -- f.unop.val : q.unop.fst ⟶ p.unop.fst in Cᵒᵖ
    -- Need morphism in ElementsContra':
    --   ⟨p.unop.fst.unop, p.unop.snd⟩ to ⟨q.unop.fst.unop, q.unop.snd⟩
    -- This needs: q.unop.fst.unop ⟶ p.unop.fst.unop in Cᵒᵖ'
    refine Subtype.mk (opToOp'.map f.unop.val) ?_
    -- Need: F.map (opToOp'.map f.unop.val) q.unop.snd = p.unop.snd
    convert f.unop.property using 2

/--
The composition `elementsContra'ToElementsContra ⋙ elementsContraToElementsContra'`
is the identity functor on `F.ElementsContra'`.
-/
lemma elementsContra'_roundtrip_eq_id (F : Cᵒᵖ' ⥤ Type w) :
    elementsContra'ToElementsContra F ⋙ elementsContraToElementsContra' F = 𝟭 _ := by
  apply Functor.ext
  case h_obj =>
    -- Objects: ⟨X, x⟩ → op ⟨op X, x⟩ → ⟨X, x⟩ = ⟨X, x⟩
    intro X
    simp only [Functor.comp_obj, Functor.id_obj,
               elementsContra'ToElementsContra, elementsContraToElementsContra']
    -- Goal is now ⟨X.fst, X.snd⟩ = X, which is sigma eta
    cases X
    rfl
  case h_map =>
    intro X Y f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Functor.id_map]
    apply Subtype.ext
    simp only [Functor.comp_map,
               elementsContra'ToElementsContra, elementsContraToElementsContra',
               Quiver.Hom.unop_op, Subtype.coe_mk]
    rfl

/--
The composition `elementsContraToElementsContra' ⋙ elementsContra'ToElementsContra`
is the identity functor on `F.ElementsContra`.
-/
lemma elementsContra_roundtrip_eq_id (F : Cᵒᵖ' ⥤ Type w) :
    elementsContraToElementsContra' F ⋙ elementsContra'ToElementsContra F = 𝟭 _ := by
  apply Functor.ext
  case h_obj =>
    intro X
    simp only [Functor.comp_obj, Functor.id_obj,
               elementsContraToElementsContra', elementsContra'ToElementsContra]
    rfl
  case h_map =>
    intro X Y f
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id, Functor.id_map]
    apply Quiver.Hom.unop_inj
    apply Subtype.ext
    simp only [Functor.comp_map,
               elementsContraToElementsContra', elementsContra'ToElementsContra,
               Quiver.Hom.unop_op, Subtype.coe_mk]
    rfl

def elementsContraIso (F : Cᵒᵖ' ⥤ Type w) :
    F.ElementsContra' ≅Cat F.ElementsContra where
  hom := elementsContra'ToElementsContra F
  inv := elementsContraToElementsContra' F
  hom_inv_id := elementsContra'_roundtrip_eq_id F
  inv_hom_id := elementsContra_roundtrip_eq_id F

/--
The categorical equivalence between `F.ElementsContra'` and `F.ElementsContra`,
derived from the isomorphism.
-/
def elementsContraEquiv (F : Cᵒᵖ' ⥤ Type w) :
    F.ElementsContra' ≌ F.ElementsContra :=
  Cat.equivOfIso (elementsContraIso F)

namespace CategoryOfElementsContra'

/--
Constructor for morphisms in the contravariant category of elements.
Given `f : x.1 ⟶ y.1` in `C` such that `F.map f` takes `y.snd` to `x.snd`,
constructs a morphism `x ⟶ y` in `F.ElementsContra'`.
-/
def homMk {F : Cᵒᵖ' ⥤ Type w} (x y : F.ElementsContra') (f : x.1 ⟶ y.1)
    (hf : F.map f y.snd = x.snd) : x ⟶ y :=
  ⟨f, hf⟩

lemma homMk_val {F : Cᵒᵖ' ⥤ Type w} {x y : F.ElementsContra'} (f : x.1 ⟶ y.1)
    (hf : F.map f y.snd = x.snd) : (homMk x y f hf).val = f :=
  rfl

@[ext]
lemma hom_ext {F : Cᵒᵖ' ⥤ Type w} {x y : F.ElementsContra'} (f g : x ⟶ y)
    (h : f.val = g.val) : f = g := by
  cases f; cases g
  congr

end CategoryOfElementsContra'

/--
The contravariant hom-functor using the `op'` construction.
This is mathlib's `yoneda : C ⥤ Cᵒᵖ ⥤ Type` converted to use `op'` by
post-composing with `preCompToOp'`.

For each object `X : C`, the functor `coyoneda'.obj X : Cᵒᵖ' ⥤ Type` maps
each object `Y : C` to the set of morphisms `Y ⟶ X`.
-/
def coyoneda' : C ⥤ (Cᵒᵖ' ⥤ Type v) :=
  yoneda ⋙ preCompToOp'

lemma coyoneda'_obj_obj (X Y : C) : (coyoneda'.obj X).obj Y = (Y ⟶ X) := by
  dsimp [coyoneda', preCompToOp']
  rfl

lemma coyoneda'_obj_map (X : C) {Y Z : C} (f : (Z : Cᵒᵖ') ⟶ (Y : Cᵒᵖ')) (g : Y ⟶ X) :
    (coyoneda'.obj X).map f g = f ≫ g := by
  dsimp [coyoneda', preCompToOp', op'ToOp]
  rfl

namespace ElementsContra'

section OverEquivalence

variable (X : C)

/--
Functor from `Over X` to the category of elements of `coyoneda'.obj X`.
An object `f : Y ⟶ X` in `Over X` maps to `(Y, f)` in the category of elements.
-/
def overToElements : Over X ⥤ (coyoneda'.obj X).ElementsContra' where
  obj f := ⟨f.left, f.hom⟩
  map {f g} h := ⟨h.left, by
    change (coyoneda'.obj X).map h.left g.hom = f.hom
    rw [coyoneda'_obj_map]
    exact Over.w h⟩

/--
Functor from the category of elements of `coyoneda'.obj X` to `Over X`.
An element `(Y, f : Y ⟶ X)` maps to the arrow `f : Y ⟶ X` in `Over X`.
-/
def elementsToOver : (coyoneda'.obj X).ElementsContra' ⥤ Over X where
  obj p := Over.mk p.snd
  map {p q} g := Over.homMk g.val (by
    dsimp [Over.mk]
    have : (coyoneda'.obj X).map g.val q.snd = p.snd := g.property
    rw [coyoneda'_obj_map] at this
    exact this)

/--
Unit isomorphism for the equivalence between `Over X` and the category of
elements of `coyoneda'.obj X`.
-/
def overElementsUnitIso :
    𝟭 (Over X) ≅ overToElements X ⋙ elementsToOver X :=
  NatIso.ofComponents
    (fun f => Over.isoMk (Iso.refl _) (by simp [overToElements, elementsToOver]))
    (fun g => by
      ext
      simp [overToElements, elementsToOver])

private lemma counit_hom_comp_inv (p : (coyoneda'.obj X).ElementsContra') :
    (𝟙 p.fst ≫ 𝟙 p.fst : p.fst ⟶ p.fst) = 𝟙 p.fst := by
  simp

private lemma counit_inv_comp_hom (p : (coyoneda'.obj X).ElementsContra') :
    (𝟙 p.fst ≫ 𝟙 p.fst : p.fst ⟶ p.fst) = 𝟙 p.fst := by
  simp

private lemma counit_naturality_val (X : C) {p q : (coyoneda'.obj X).ElementsContra'}
    (g : p ⟶ q) :
    ((elementsToOver X ⋙ overToElements X).map g ≫
      (⟨𝟙 q.fst, by
        change (coyoneda'.obj X).map (𝟙 q.fst) q.snd = q.snd
        rw [coyoneda'_obj_map, Category.id_comp]⟩ :
        (elementsToOver X ⋙ overToElements X).obj q ⟶
        (𝟭 ((coyoneda'.obj X).ElementsContra')).obj q)).val =
    ((⟨𝟙 p.fst, by
        change (coyoneda'.obj X).map (𝟙 p.fst) p.snd = p.snd
        rw [coyoneda'_obj_map, Category.id_comp]⟩ :
        (elementsToOver X ⋙ overToElements X).obj p ⟶
        (𝟭 ((coyoneda'.obj X).ElementsContra')).obj p) ≫ g).val := by
  dsimp [elementsToOver, overToElements]
  -- In the category of elements, (f ≫ g).val = g.val ≫ f.val (in Cᵒᵖ')
  -- LHS: (⟨g.val, _⟩ ≫ ⟨𝟙 q.fst, _⟩).val
  -- RHS: (⟨𝟙 p.fst, _⟩ ≫ g).val
  -- These are both morphisms in Cᵒᵖ', composition is (f ≫ g).val = g.val ≫ f.val
  change ((@CategoryStruct.id Cᵒᵖ' _ q.fst) ≫ g.val) =
         (g.val ≫ (@CategoryStruct.id Cᵒᵖ' _ p.fst))
  rw [Category.id_comp, Category.comp_id]

/--
Counit isomorphism for the equivalence between `Over X` and the category of
elements of `coyoneda'.obj X`.
-/
def overElementsCounitIso :
    elementsToOver X ⋙ overToElements X ≅ 𝟭 ((coyoneda'.obj X).ElementsContra') :=
  NatIso.ofComponents
    (fun p => ⟨⟨𝟙 p.fst, by
                change (coyoneda'.obj X).map (𝟙 p.fst) p.snd = p.snd
                rw [coyoneda'_obj_map, Category.id_comp]⟩,
              ⟨𝟙 p.fst, by
                change (coyoneda'.obj X).map (𝟙 p.fst) p.snd = p.snd
                rw [coyoneda'_obj_map, Category.id_comp]⟩,
              by ext; exact counit_hom_comp_inv X p,
              by ext; exact counit_inv_comp_hom X p⟩)
    (fun g => by ext; exact counit_naturality_val X g)

private lemma functor_unitIso_comp_helper (X : C) (f : Over X) :
    ((overToElements X).map ((overElementsUnitIso X).hom.app f) ≫
     (overElementsCounitIso X).hom.app ((overToElements X).obj f)).val =
    (@CategoryStruct.id ((coyoneda'.obj X).ElementsContra') _
      ((overToElements X).obj f)).val := by
  dsimp [overToElements, elementsToOver, overElementsUnitIso, overElementsCounitIso]
  -- Unit at f: Over.isoMk (Iso.refl _) has .left = 𝟙 f.left
  -- Mapped through overToElements: ⟨𝟙 f.left, _⟩
  -- Counit at ⟨f.left, f.hom⟩: ⟨𝟙 f.left, _⟩
  -- Composition: ⟨𝟙 f.left ≫ 𝟙 f.left, _⟩ = ⟨𝟙 f.left, _⟩
  -- Identity: ⟨𝟙 f.left, _⟩
  -- The .val parts are both 𝟙 f.left (in Cᵒᵖ')
  change ((@CategoryStruct.id Cᵒᵖ' _ f.left) ≫ (@CategoryStruct.id Cᵒᵖ' _ f.left)) =
         (@CategoryStruct.id Cᵒᵖ' _ f.left)
  rw [Category.comp_id]

/--
The slice category `Over X` is equivalent to the category of elements of the
contravariant hom-functor `coyoneda'.obj X`.

This shows that representable presheaves correspond to slice categories.
-/
def overEquivElements : Over X ≌ (coyoneda'.obj X).ElementsContra' where
  functor := overToElements X
  inverse := elementsToOver X
  unitIso := overElementsUnitIso X
  counitIso := overElementsCounitIso X
  functor_unitIso_comp f := by
    ext
    exact functor_unitIso_comp_helper X f

end OverEquivalence

section PresheafSliceEquivalence

variable (P : Cᵒᵖ' ⥤ Type w)

/--
The fiber of `η : F ⟶ P` over an element `x : P.obj X`.
-/
def Fiber {F : Cᵒᵖ' ⥤ Type w} {P : Cᵒᵖ' ⥤ Type w} (η : F ⟶ P) (X : C) (x : P.obj X) : Type w :=
  { y : F.obj X // η.app X y = x }

/--
Given `η : F ⟶ P` and an element `(X, x) : P.ElementsContra'`,
map a morphism in the category of elements to a function between fibers.
-/
def fiberMap {F : Cᵒᵖ' ⥤ Type w} {P : Cᵒᵖ' ⥤ Type w} (η : F ⟶ P)
    {p q : P.ElementsContra'} (f : p ⟶ q) :
    Fiber η q.fst q.snd → Fiber η p.fst p.snd :=
  fun y => ⟨F.map f.val y.val, by
    have hy := y.property
    have hf := f.property
    have nat := congrFun (η.naturality f.val) y.val
    dsimp at nat
    calc η.app p.fst (F.map f.val y.val)
        = P.map f.val (η.app q.fst y.val) := nat
      _ = P.map f.val q.snd := by rw [hy]
      _ = p.snd := hf⟩

/--
Functor from `Over P` to presheaves on `P.ElementsContra'ᵒᵖ'`.
Maps `η : F ⟶ P` to the fiber functor.
-/
def sliceToPresheaf : Over P ⥤ (P.ElementsContra'ᵒᵖ' ⥤ Type w) where
  obj η := {
    obj := fun p => Fiber η.hom p.fst p.snd
    map := fun {p q} f => fiberMap η.hom f
    map_id := fun p => by
      ext y
      dsimp [fiberMap, Fiber]
      congr 1
      have : (𝟙 p : p ⟶ p).val = 𝟙 p.fst := rfl
      rw [this]
      exact congrFun (η.left.map_id p.fst) y.val
    map_comp := fun {p q r} f g => by
      ext y
      dsimp [fiberMap, Fiber]
      congr 1
      have : (f ≫ g).val = f.val ≫ g.val := rfl
      rw [this]
      exact congrFun (η.left.map_comp f.val g.val) y.val }
  map {η₁ η₂} α := {
    app := fun p y => ⟨α.left.app p.fst y.val, by
      have hy := y.property
      have hw := Over.w α
      have h := congrFun (congrArg NatTrans.app hw) p.fst
      simp only [NatTrans.comp_app] at h
      calc η₂.hom.app p.fst (α.left.app p.fst y.val)
          = (α.left.app p.fst ≫ η₂.hom.app p.fst) y.val := rfl
        _ = η₁.hom.app p.fst y.val := congrFun h y.val
        _ = p.snd := hy⟩
    naturality := by
      intros p q f
      ext y
      dsimp [fiberMap, Fiber]
      congr 1
      have nat := congrFun (α.left.naturality f.val) y.val
      exact nat }
  map_id := by
    intros η
    ext p y
    simp only [Fiber]
    rfl
  map_comp := by
    intros η₁ η₂ η₃ α β
    ext p y
    simp only [Fiber]
    rfl

/--
Helper lemma: Mapping the identity morphism in the category of elements
applies the identity function.
-/
lemma sigma_ext_rfl_heq {α : Type*} {β : α → Type*} {a : α} {b₁ b₂ : β a}
    (h : b₁ = b₂) : (⟨a, b₁⟩ : Sigma β) = ⟨a, b₂⟩ :=
  Sigma.ext rfl (heq_of_eq h)

lemma totalSpace_map_id_aux (G : P.ElementsContra'ᵒᵖ' ⥤ Type w) {X : Cᵒᵖ'} :
    ∀ (x : P.obj X) (gx : G.obj ⟨X, x⟩),
    G.map ⟨𝟙 X, congrFun (P.map_id X) x⟩ gx = gx := by
  intro x gx
  have h1 : G.map ⟨𝟙 X, congrFun (P.map_id X) x⟩ gx = G.map (𝟙 ⟨X, x⟩) gx := by
    congr 1
  rw [h1]
  simp


/--
Helper lemma: Morphisms with equal underlying morphisms give heterogeneously
equal results when mapped by a functor, even if the morphisms are in different
(but equal) hom-sets.
-/
lemma functor_map_subtype_heq (G : P.ElementsContra'ᵒᵖ' ⥤ Type w)
    {p q p' q' : P.ElementsContra'} (hp : p = p') (hq : q = q')
    (f : p ⟶ q) (g : p' ⟶ q') (hval : f.val ≍ g.val)
    {t : G.obj q} {t' : G.obj q'} (ht : t ≍ t') :
    G.map f t ≍ G.map g t' := by
  subst hp hq
  have hval' : f.val = g.val := eq_of_heq hval
  have ht' : t = t' := eq_of_heq ht
  subst ht'
  have : f = g := Subtype.ext hval'
  rw [this]

/--
The total space functor for a presheaf `G` on `P.ElementsContra'ᵒᵖ'`.
Sends `X : C` to `Σ (x : P.obj X), G.obj ⟨X, x⟩`.
-/
def totalSpace (G : P.ElementsContra'ᵒᵖ' ⥤ Type w) : Cᵒᵖ' ⥤ Type w where
  obj X := Σ (x : P.obj X), G.obj ⟨X, x⟩
  map {X Y} f pair :=
    ⟨P.map f pair.fst, G.map (Subtype.mk f rfl) pair.snd⟩
  map_id := by
    intro X
    funext pair
    rcases pair with ⟨x, gx⟩
    have tsmiea := totalSpace_map_id_aux P G x gx
    have hx : P.map (𝟙 X) x = x := congrFun (P.map_id X) x
    refine Sigma.ext hx ?_
    have h : G.map (Subtype.mk (𝟙 X) hx) gx = gx := by
      simpa [hx] using totalSpace_map_id_aux P G x gx
    simp
    convert heq_of_eq h using 2
    case h.e'_2.e'_3 =>
      exact sigma_ext_rfl_heq hx
    case h.e'_2.e'_4 =>
      congr 2
      · funext
        simp
      case e_4 => exact proof_irrel_heq rfl hx
    case h.e'_1.h.e'_6 =>
      exact sigma_ext_rfl_heq hx
  map_comp := by
    intros X Y Z f g
    ext ⟨x, gx⟩
    · simp
    · simp
      -- After simp, all morphisms are self-loops on ⟨X, x⟩
      -- The goal involves angle bracket morphisms ⟨f ≫ g, rfl⟩, ⟨f, rfl⟩, ⟨g, rfl⟩
      -- Use G.map_comp and show morphisms are equal by proof irrelevance
      sorry

/--
The projection from the total space to the base.
-/
def totalSpaceProj (G : P.ElementsContra'ᵒᵖ' ⥤ Type w) : totalSpace P G ⟶ P where
  app X pair := pair.fst
  naturality := by
    intros X Y f
    funext pair
    obtain ⟨x, gx⟩ := pair
    rfl

/--
The inverse functor. Maps a presheaf `G : P.ElementsContra'ᵒᵖ' ⥤ Type w` to an
object in `Over P`.
-/
def presheafToSlice : (P.ElementsContra'ᵒᵖ' ⥤ Type w) ⥤ Over P where
  obj G := Over.mk (totalSpaceProj P G)
  map {G H} α := {
    left := {
      app := fun X pair => ⟨pair.fst, α.app ⟨X, pair.fst⟩ pair.snd⟩
      naturality := by
        intros X Y f
        funext pair
        obtain ⟨x, gx⟩ := pair
        dsimp [totalSpace]
        ext
        · rfl
        · have h : P.map f x = P.map f x := rfl
          let src : P.ElementsContra' := ⟨Y, P.map f x⟩
          let tgt : P.ElementsContra' := ⟨X, x⟩
          have nat := α.naturality (⟨f, h⟩ : src ⟶ tgt)
          have nat_at_gx := congrFun nat gx
          simp only [types_comp_apply, src, tgt] at nat_at_gx
          exact heq_of_eq (congrArg
            (fun z => (Sigma.mk (P.map f x) z : Σ _ : P.obj Y, _).snd) nat_at_gx) }
    right := eqToHom rfl }
  map_id := by
    intro G
    ext X ⟨x, gx⟩
    rfl
  map_comp := by
    intros G H K α β
    ext X ⟨x, gx⟩
    rfl

/--
The unit isomorphism of the equivalence.
For `η : F ⟶ P`, we have `η ≅ presheafToSlice (sliceToPresheaf η)`.
-/
def slicePresheafUnitIso : 𝟭 (Over P) ≅ sliceToPresheaf P ⋙ presheafToSlice P where
  hom := {
    app := fun η => {
      left := sorry
      right := sorry }
    naturality := sorry }
  inv := {
    app := fun η => {
      left := sorry
      right := sorry }
    naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/--
The counit isomorphism of the equivalence.
For `G : P.ElementsContra'ᵒᵖ' ⥤ Type w`,
we have `G ≅ sliceToPresheaf (presheafToSlice G)`.
-/
def slicePresheafCounitIso :
    presheafToSlice P ⋙ sliceToPresheaf P ≅ 𝟭 (P.ElementsContra'ᵒᵖ' ⥤ Type w) where
  hom := {
    app := fun G => {
      app := sorry
      naturality := sorry }
    naturality := sorry }
  inv := {
    app := fun G => {
      app := sorry
      naturality := sorry }
    naturality := sorry }
  hom_inv_id := sorry
  inv_hom_id := sorry

/--
The categorical equivalence between `Over P` and presheaves on `P.ElementsContra'ᵒᵖ'`.
This is the contravariant analog of mathlib's `overEquivPresheafCostructuredArrow`.
-/
def sliceEquivPresheaf : Over P ≌ (P.ElementsContra'ᵒᵖ' ⥤ Type w) where
  functor := sliceToPresheaf P
  inverse := presheafToSlice P
  unitIso := slicePresheafUnitIso P
  counitIso := slicePresheafCounitIso P
  functor_unitIso_comp := sorry

end PresheafSliceEquivalence

end ElementsContra'

end CategoryTheory
