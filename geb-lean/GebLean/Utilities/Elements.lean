import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.Category.Cat.Op
import GebLean.Utilities.Equalities
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

section CopresheafSliceEquivalence

variable (F : C ⥤ Type w)

/--
The fiber of `η : G ⟶ F` over an element `x : F.obj X`.
-/
def Fiber {G F : C ⥤ Type w} (η : G ⟶ F) (X : C) (x : F.obj X) : Type w :=
  { y : G.obj X // η.app X y = x }

/--
Map a morphism in the category of elements to a function between fibers.
For covariant functors, morphisms `f : (X, x) → (Y, y)` satisfy `F.map f x = y`.
-/
def fiberMap {G F : C ⥤ Type w} (η : G ⟶ F)
    {p q : F.Elements} (f : p ⟶ q) :
    Fiber η p.fst p.snd → Fiber η q.fst q.snd :=
  fun y => ⟨G.map f.val y.val, by
    have hy := y.property
    have hf := f.property
    have nat := congrFun (η.naturality f.val) y.val
    calc η.app q.fst (G.map f.val y.val)
        = F.map f.val (η.app p.fst y.val) := nat
      _ = F.map f.val p.snd := by rw [hy]
      _ = q.snd := hf⟩

/--
Functor from `Over F` to copresheaves on `F.Elements`.
Maps `η : G ⟶ F` to the fiber functor.
-/
def sliceToCopresheaf : Over F ⥤ (F.Elements ⥤ Type w) where
  obj η := {
    obj := fun p => Fiber η.hom p.fst p.snd
    map := fun {p q} f => fiberMap η.hom f
    map_id := by
      intro p
      ext y
      dsimp [fiberMap, Fiber]
      congr 1
      exact congrFun (η.left.map_id p.fst) y.val
    map_comp := by
      intros p q r f g
      ext y
      dsimp [fiberMap, Fiber]
      congr 1
      exact congrFun (η.left.map_comp f.val g.val) y.val }
  map {η₁ η₂} α := {
    app := fun p y => ⟨α.left.app p.fst y.val, by
      have hy := y.property
      have h : α.left.app p.fst ≫ η₂.hom.app p.fst = η₁.hom.app p.fst :=
        congrFun (congrArg NatTrans.app α.w) p.fst
      calc η₂.hom.app p.fst (α.left.app p.fst y.val)
          = (α.left.app p.fst ≫ η₂.hom.app p.fst) y.val := rfl
        _ = η₁.hom.app p.fst y.val := congrFun h y.val
        _ = p.snd := hy⟩
    naturality := by
      intros p q f
      ext y
      dsimp [fiberMap, Fiber]
      congr 1
      exact congrFun (α.left.naturality f.val) y.val
  }
  map_id := by
    intro η
    ext p y
    simp [Fiber]
  map_comp := by
    intros η₁ η₂ η₃ α β
    ext p y
    simp [Fiber]

/--
The total space copresheaf for a copresheaf `G` on `F.Elements`.
Sends `X : C` to `Σ (x : F.obj X), G.obj ⟨X, x⟩`.
-/
def totalSpace (G : F.Elements ⥤ Type w) : C ⥤ Type w where
  obj X := Σ (x : F.obj X), G.obj ⟨X, x⟩
  map {X Y} f pair :=
    ⟨F.map f pair.fst, G.map ⟨f, rfl⟩ pair.snd⟩
  map_id := by
    intro X
    funext ⟨x, gx⟩
    have hx : F.map (𝟙 X) x = x := congrFun (F.map_id X) x
    have h : G.map ⟨𝟙 X, hx⟩ gx = gx := by
      have : G.map ⟨𝟙 X, hx⟩ gx = G.map (𝟙 ⟨X, x⟩) gx := by
        congr 1
      rw [this]
      simp only [CategoryTheory.Functor.map_id, types_id_apply]
    refine Sigma.ext hx ?_
    simp only [types_id_apply]
    convert heq_of_eq h using 2 <;> try exact sigma_ext_rfl_heq hx
    congr 2
    · funext; rw [hx]
    exact proof_irrel_heq rfl hx
  map_comp := by
    intros X Y Z f g
    ext ⟨x, gx⟩
    · simp only [Functor.map_comp, types_comp_apply]
    · simp only [types_comp_apply]
      have h := congrFun (@Functor.map_comp _ _ _ _ G ⟨X, x⟩ ⟨Y, F.map f x⟩ ⟨Z, F.map g (F.map f x)⟩
        ⟨f, rfl⟩ ⟨g, rfl⟩) gx
      simp only [types_comp_apply] at h
      have hcomp : F.map (f ≫ g) x = F.map g (F.map f x) := by
        rw [F.map_comp]; rfl
      convert heq_of_eq h using 2 <;> try exact sigma_ext_rfl_heq hcomp
      congr 2
      · funext; rw [hcomp]
      exact proof_irrel_heq _ _

/--
The projection from the total space to the base.
-/
def totalSpaceProj (G : F.Elements ⥤ Type w) : totalSpace F G ⟶ F where
  app X pair := pair.fst
  naturality := by
    intros X Y f
    funext pair
    obtain ⟨x, gx⟩ := pair
    rfl

/--
The inverse functor. Maps a copresheaf `G : F.Elements ⥤ Type w` to an
object in `Over F`.
-/
def copresheafToSlice : (F.Elements ⥤ Type w) ⥤ Over F where
  obj G := Over.mk (totalSpaceProj F G)
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
        · have h : F.map f x = F.map f x := rfl
          let src : F.Elements := ⟨X, x⟩
          let tgt : F.Elements := ⟨Y, F.map f x⟩
          have nat := α.naturality (⟨f, h⟩ : src ⟶ tgt)
          have nat_at_gx := congrFun nat gx
          simp only [types_comp_apply, src, tgt] at nat_at_gx
          exact heq_of_eq (congrArg
            (fun z => (Sigma.mk (F.map f x) z : Σ _ : F.obj Y, _).snd) nat_at_gx)
    }
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
For `η : G ⟶ F`, we have `η ≅ copresheafToSlice (sliceToCopresheaf η)`.
-/
def sliceCopresheafUnitIso : 𝟭 (Over F) ≅ sliceToCopresheaf F ⋙ copresheafToSlice F :=
  NatIso.ofComponents
    (fun η => Over.isoMk
      { hom := {
          app := fun X fx => ⟨η.hom.app X fx, ⟨fx, rfl⟩⟩
          naturality := by
            intros X Y f
            funext fx
            dsimp [totalSpace, copresheafToSlice, sliceToCopresheaf, Fiber, fiberMap]
            ext
            · exact congrFun (η.hom.naturality f) fx
            · dsimp
            }
        inv := {
          app := fun X pair => pair.snd.val
          naturality := by
            intros X Y f
            funext pair
            obtain ⟨x, ⟨fx, hfx⟩⟩ := pair
            dsimp [totalSpace, Fiber, fiberMap]
            rfl }
        hom_inv_id := by
          ext X fx
          rfl
        inv_hom_id := by
          ext X ⟨x, ⟨fx, hfx⟩⟩
          dsimp [Fiber]
          refine Sigma.ext hfx ?_
          dsimp only []
          congr 1
          · funext y
            rw [hfx]
          · exact proof_irrel_heq _ _ }
      (by ext X x; rfl))
    (fun {η₁ η₂} α => by
      ext X fx
      dsimp [sliceToCopresheaf, copresheafToSlice, totalSpace, Fiber]
      refine Sigma.ext (congrFun (congrFun (congrArg NatTrans.app α.w) X) fx) ?_
      dsimp only []
      congr 1
      · funext y
        have h := congrFun (congrFun (congrArg NatTrans.app α.w) X) fx
        dsimp at h
        simp only [h]
      · exact proof_irrel_heq _ _)

/--
The counit isomorphism of the equivalence.
For `G : F.Elements ⥤ Type w`,
we have `G ≅ sliceToCopresheaf (copresheafToSlice G)`.
-/
def sliceCopresheafCounitIso :
    copresheafToSlice F ⋙ sliceToCopresheaf F ≅ 𝟭 (F.Elements ⥤ Type w) :=
  NatIso.ofComponents
    (fun G => NatIso.ofComponents
      (fun p => {
        hom := fun y => by
          dsimp [sliceToCopresheaf, copresheafToSlice, Fiber, totalSpace, totalSpaceProj] at y
          have hp : (⟨p.fst, y.val.fst⟩ : F.Elements) = p := by
            ext
            · rfl
            · exact heq_of_eq y.property
          exact hp ▸ y.val.snd
        inv := fun gx => by
          dsimp [sliceToCopresheaf, copresheafToSlice, Fiber, totalSpace, totalSpaceProj]
          exact ⟨⟨p.snd, gx⟩, rfl⟩
        hom_inv_id := by
          ext ⟨⟨x, gx⟩, hx⟩
          dsimp [Fiber, totalSpace, totalSpaceProj]
          apply Subtype.ext
          refine Sigma.ext hx.symm ?_
          simp
        inv_hom_id := by
          ext gx
          dsimp [Fiber, totalSpace, totalSpaceProj]})
      (fun {p q} f => by
        ext ⟨⟨x, gx⟩, hx⟩
        dsimp [sliceToCopresheaf, copresheafToSlice, Fiber, fiberMap, totalSpace,
          totalSpaceProj] at hx ⊢
        have hp : (⟨p.fst, x⟩ : F.Elements) = p := by
          ext
          · rfl
          · exact heq_of_eq hx
        have hq : (⟨q.fst, F.map f.val x⟩ : F.Elements) = q := by
          ext
          · rfl
          · have fprop : F.map f.val p.snd = q.snd := f.property
            have : F.map f.val x = q.snd := by
              rw [hx, fprop]
            exact heq_of_eq this
        subst hx
        apply transport_heq
        cases f with
        | mk fval fprop =>
          generalize totalSpace._proof_1 F G fval ⟨p.snd, gx⟩ = proof
          cases proof
          simp only [Subtype.coe_mk]
          cases p with | mk p₁ p₂ =>
          cases q with | mk q₁ q₂ =>
          dsimp only [] at fprop gx ⊢
          cases hp
          injection hq with hq₁ hq₂
          grind
        ))
    (fun {G H} α => by
      ext p ⟨⟨x, gx⟩, hx⟩
      dsimp [sliceToCopresheaf, copresheafToSlice, Fiber, totalSpace, totalSpaceProj] at hx ⊢
      have hp : (⟨p.fst, x⟩ : F.Elements) = p := by
        ext
        · rfl
        · exact heq_of_eq hx
      subst hx
      simp_all only []
      generalize hp_eq : hp = hp'
      cases hp'
      simp_all only []
      rfl)

/--
For the specific pattern in the triangle identity: when transporting a subtype
built from a coercion along a sigma equality, the outer coercion is preserved.
-/
lemma triangle_identity_transport_aux {G F : C ⥤ Type w} (η : G ⟶ F)
    (pfst : C) (psnd : F.obj pfst)
    (aval : G.obj pfst) (aproof : η.app pfst aval = psnd)
    (pf₂ : (⟨pfst, η.app pfst aval⟩ : (c : C) × F.obj c) = ⟨pfst, psnd⟩) :
    (@Eq.rec ((c : C) × F.obj c) ⟨pfst, η.app pfst aval⟩
      (fun s _ => {y : G.obj s.fst // η.app s.fst y = s.snd})
      (⟨aval, rfl⟩ : {y : G.obj pfst // η.app pfst y = η.app pfst aval})
      (⟨pfst, psnd⟩ : (c : C) × F.obj c) pf₂).val = aval := by
  obtain ⟨h₁, h₂⟩ := Sigma.mk.inj_iff.mp pf₂
  cases h₁
  cases pf₂
  rfl

lemma triangle_identity_transport {G F : C ⥤ Type w} (η : G ⟶ F)
    (p : (c : C) × F.obj c)
    (a : {y : G.obj p.fst // η.app p.fst y = p.snd})
    (pf₁ : η.app p.fst a.val = η.app p.fst a.val)
    (pf₂ : ⟨p.fst, η.app p.fst a.val⟩ = p) :
    (@Eq.rec ((c : C) × F.obj c) ⟨p.fst, η.app p.fst a.val⟩
      (fun s _ => {y : G.obj s.fst // η.app s.fst y = s.snd})
      ⟨a.val, pf₁⟩ p pf₂).val = a.val := by
  obtain ⟨aval, aproof⟩ := a
  obtain ⟨pfst, psnd⟩ := p
  simp only [Subtype.coe_mk]
  cases pf₁ with
    | refl =>
      exact triangle_identity_transport_aux η pfst psnd aval aproof pf₂

private lemma sliceCopresheafFunctorUnitIso (η : Over F) :
    (sliceToCopresheaf F).map ((sliceCopresheafUnitIso F).hom.app η) ≫
    (sliceCopresheafCounitIso F).hom.app ((sliceToCopresheaf F).obj η) =
    𝟙 ((sliceToCopresheaf F).obj η) := by
  -- This is the triangle identity
  ext p a
  dsimp [sliceToCopresheaf, sliceCopresheafUnitIso, sliceCopresheafCounitIso]
  -- Use Subtype.ext to reduce to showing coercions equal
  apply Subtype.ext
  simp only [Fiber]
  -- Goal: ↑(⋯ ▸ ⟨↑a, ⋯⟩) = ↑a
  generalize_proofs pf₁ pf₂
  exact triangle_identity_transport η.hom p a pf₁ pf₂

/--
The categorical equivalence between `Over F` and copresheaves on `F.Elements`.
-/
def sliceEquivCopresheaf :
    Equivalence.{max u w, max u w, max u v (w + 1), max u v (w + 1)}
      (Over F) (F.Elements ⥤ Type w) where
  functor := sliceToCopresheaf F
  inverse := copresheafToSlice F
  unitIso := sliceCopresheafUnitIso F
  counitIso := sliceCopresheafCounitIso F
  functor_unitIso_comp η := sliceCopresheafFunctorUnitIso F η

end CopresheafSliceEquivalence

/--
The contravariant category of elements for a functor `F : Cᵒᵖ' ⥤ Type`.
This is simply the opposite of mathlib's covariant category of elements
of `F` viewed as a copresheaf on `Cᵒᵖ'`.
-/
def Functor.ElementsContra' (F : Cᵒᵖ' ⥤ Type w) := F.Elementsᵒᵖ'

instance ElementsContraCat' (F : Cᵒᵖ' ⥤ Type w) :
  Category.{v, max u w} F.ElementsContra' :=
    inferInstanceAs (Category F.Elementsᵒᵖ')

/--
For a presheaf `F`, `F.Elements` is `F.ElementsContra'ᵒᵖ'`.
-/
def elementsToElementsContraOpEq (F : Cᵒᵖ' ⥤ Type w) :
  F.Elements = F.ElementsContra'ᵒᵖ' :=
    rfl

/--
The categorical equivalence between `Over F` and presheaves on `F.ElementsContra'`.
-/
def sliceEquivPresheaf (F : Cᵒᵖ' ⥤ Type w) :
  Over F ≌ (F.ElementsContra'ᵒᵖ' ⥤ Type w) :=
    sliceEquivCopresheaf F

/--
The category of elements of a presheaf using mathlib's definition of `op`
(as opposed to our `op'`).
For `F : Cᵒᵖ' ⥤ Type w`, transport `F` to a functor `Cᵒᵖ ⥤ Type w` using `opToOp'`,
then take mathlib's category of elements and reverse the morphisms (opposite).
-/
def Functor.ElementsContra (F : Cᵒᵖ' ⥤ Type w) :=
  ((opToOp' ⋙ F).Elements)ᵒᵖ

instance (F : Cᵒᵖ' ⥤ Type w) : Category F.ElementsContra :=
  inferInstanceAs (Category ((opToOp' ⋙ F).Elements)ᵒᵖ)

/--
The functor from `F.ElementsContra'` to `F.ElementsContra`.
-/
def elementsContra'ToElementsContra (F : Cᵒᵖ' ⥤ Type w) :
    F.ElementsContra' ⥤ F.ElementsContra where
  obj p := Opposite.op ⟨op'ToOp.obj p.fst, p.snd⟩
  map {p q} f := Opposite.op ⟨op'ToOp.map f.val, f.property⟩

/--
The functor from `F.ElementsContra` to `F.ElementsContra'`.
-/
def elementsContraToElementsContra' (F : Cᵒᵖ' ⥤ Type w) :
    F.ElementsContra ⥤ F.ElementsContra' where
  obj p := ⟨opToOp'.obj p.unop.fst, p.unop.snd⟩
  map {p q} f := ⟨opToOp'.map f.unop.val, f.unop.property⟩

/--
The composition `elementsContra'ToElementsContra ⋙ elementsContraToElementsContra'`
is the identity functor on `F.ElementsContra'`.
-/
lemma elementsContra'_roundtrip_eq_id (F : Cᵒᵖ' ⥤ Type w) :
    elementsContra'ToElementsContra F ⋙ elementsContraToElementsContra' F = 𝟭 _ := by
  apply _root_.CategoryTheory.Functor.ext
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
               elementsContra'ToElementsContra, elementsContraToElementsContra']
    rfl

/--
The composition `elementsContraToElementsContra' ⋙ elementsContra'ToElementsContra`
is the identity functor on `F.ElementsContra`.
-/
lemma elementsContra_roundtrip_eq_id (F : Cᵒᵖ' ⥤ Type w) :
    elementsContraToElementsContra' F ⋙ elementsContra'ToElementsContra F = 𝟭 _ := by
  apply _root_.CategoryTheory.Functor.ext
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
               elementsContraToElementsContra', elementsContra'ToElementsContra]
    rfl

def elementsContraIso (F : Cᵒᵖ' ⥤ Type w) :
    F.ElementsContra' ≅Cat F.ElementsContra where
  hom := (elementsContra'ToElementsContra F).toCatHom
  inv := (elementsContraToElementsContra' F).toCatHom
  hom_inv_id := by
    apply Cat.Hom.ext
    exact elementsContra'_roundtrip_eq_id F
  inv_hom_id := by
    apply Cat.Hom.ext
    exact elementsContra_roundtrip_eq_id F

/--
The categorical equivalence between `F.ElementsContra'` and `F.ElementsContra`,
derived from the isomorphism.
-/
def elementsContraEquiv (F : Cᵒᵖ' ⥤ Type w) :
    F.ElementsContra' ≌ F.ElementsContra :=
  Cat.equivOfIso (elementsContraIso F)

instance (F : Cᵒᵖ' ⥤ Type w) : (elementsContra'ToElementsContra F).Faithful :=
  inferInstanceAs (elementsContraEquiv F).functor.Faithful

instance (F : Cᵒᵖ' ⥤ Type w) : (elementsContraToElementsContra' F).Faithful :=
  inferInstanceAs (elementsContraEquiv F).inverse.Faithful

instance (F : Cᵒᵖ' ⥤ Type w) :
    (elementsContra'ToElementsContra F).ReflectsIsomorphisms :=
  inferInstanceAs (elementsContraEquiv F).functor.ReflectsIsomorphisms

instance (F : Cᵒᵖ' ⥤ Type w) :
    (elementsContraToElementsContra' F).ReflectsIsomorphisms :=
  inferInstanceAs (elementsContraEquiv F).inverse.ReflectsIsomorphisms

/-! ### ElementsPre: category of elements for presheaves using mathlib's op

For a presheaf `F : Cᵒᵖ ⥤ Type w` (using mathlib's opposite), the category of
elements treats `F` as a copresheaf on `Cᵒᵖ`. The standard "contravariant
category of elements" for presheaves reverses morphism direction.
-/

/-- The functorial contravariant category of elements:
sends a copresheaf `F : D ⥤ Type w` to the opposite of
its (covariant) category of elements.  This is the
composition of mathlib's `elementsFunctor` with the
oppositization endofunctor on `Cat`. -/
def ElementsPreF (D : Type*) [Category D] :
    (D ⥤ Type w) ⥤ Cat :=
  Functor.elementsFunctor ⋙ Cat.opFunctor

/--
The (contravariant) category of elements for a presheaf
`F : Cᵒᵖ ⥤ Type w`.

This is the standard construction: take mathlib's category
of elements (which treats `F` as a copresheaf on `Cᵒᵖ`),
then take its opposite to get the conventional presheaf
category of elements where:
- Objects: pairs `(X, x)` with `X : C` and
  `x : F.obj (op X)`
- Morphisms `(X, x) → (Y, y)`: maps `f : X ⟶ Y` in `C`
  with `F.map f.op y = x`
-/
def Functor.ElementsPre (F : Cᵒᵖ ⥤ Type w) := F.Elementsᵒᵖ

instance (F : Cᵒᵖ ⥤ Type w) : Category F.ElementsPre :=
  inferInstanceAs (Category F.Elementsᵒᵖ)

theorem elementsPreF_obj (F : Cᵒᵖ ⥤ Type w) :
    (ElementsPreF Cᵒᵖ).obj F =
    Cat.of F.ElementsPre :=
  rfl

/--
`ElementsPre F` equals `ElementsContra (op'ToOp ⋙ F)` definitionally.

This follows from `opToOp' ⋙ op'ToOp = 𝟭 Cᵒᵖ` (which holds by `rfl`):
- `ElementsContra (op'ToOp ⋙ F) = ((opToOp' ⋙ (op'ToOp ⋙ F)).Elements)ᵒᵖ`
- Since `opToOp' ⋙ op'ToOp = 𝟭`, the composition `opToOp' ⋙ (op'ToOp ⋙ F)`
  equals `F` on objects and morphisms
- Therefore `(opToOp' ⋙ (op'ToOp ⋙ F)).Elements = F.Elements`
- And `ElementsPre F = F.Elementsᵒᵖ = ElementsContra (op'ToOp ⋙ F)`
-/
theorem elementsPreEqElementsContra (F : Cᵒᵖ ⥤ Type w) :
    F.ElementsPre = (op'ToOp ⋙ F).ElementsContra := rfl

/-- The forgetful functor from the contravariant category
of elements of a presheaf `F : Cᵒᵖ ⥤ Type w` to `C`.
Sends `op ⟨op c, x⟩` to `c` and morphisms to their
underlying morphism in `C` (reversing twice). -/
def elementsPre_π (F : Cᵒᵖ ⥤ Type w) :
    F.ElementsPre ⥤ C :=
  (CategoryOfElements.π F).op ⋙
    (opOpEquivalence C).functor

@[simp]
theorem elementsPre_π_obj (F : Cᵒᵖ ⥤ Type w)
    (p : F.ElementsPre) :
    (elementsPre_π F).obj p = p.unop.fst.unop :=
  rfl

@[simp]
theorem elementsPre_π_map (F : Cᵒᵖ ⥤ Type w)
    {p q : F.ElementsPre} (f : p ⟶ q) :
    (elementsPre_π F).map f = f.unop.val.unop :=
  rfl

def sliceEquivPre (F : Cᵒᵖ ⥤ Type w) :
    Over F ≌ (F.ElementsPreᵒᵖ ⥤ Type w) :=
  (sliceEquivCopresheaf (C := Cᵒᵖ) F).trans
    (opOpEquivalence F.Elements).congrLeft.symm

section CovariantCategoryOfElements

variable {D : Type u} [Category.{v} D]

@[simp]
theorem CategoryOfElements.eqToHom_val {F : D ⥤ Type w} {p q : F.Elements}
    (h : p = q) : (eqToHom h).val = eqToHom (congrArg Sigma.fst h) := by
  cases h; rfl

/--
If a morphism `f` in the category of elements has `f.val = eqToHom h` for some
equality `h`, then its inverse has value `eqToHom h.symm`.
-/
theorem CategoryOfElements.val_inv_of_val_eq_eqToHom {F : D ⥤ Type w}
    {p q : F.Elements} (f : p ⟶ q) [IsIso f] (h : p.fst = q.fst)
    (hf : f.val = eqToHom h) :
    (inv f).val = eqToHom h.symm := by
  have inv_f_val : (inv f).val ≫ f.val = (inv f ≫ f).val := rfl
  simp only [IsIso.inv_hom_id] at inv_f_val
  have id_val : (𝟙 q : q ⟶ q).val = 𝟙 q.fst := rfl
  rw [id_val, hf] at inv_f_val
  calc (inv f).val = (inv f).val ≫ 𝟙 p.fst := by rw [Category.comp_id]
    _ = (inv f).val ≫ eqToHom h ≫ eqToHom h.symm := by rw [eqToHom_trans, eqToHom_refl]
    _ = ((inv f).val ≫ eqToHom h) ≫ eqToHom h.symm := by rw [Category.assoc]
    _ = 𝟙 q.fst ≫ eqToHom h.symm := by rw [inv_f_val]
    _ = eqToHom h.symm := by rw [Category.id_comp]

end CovariantCategoryOfElements

namespace CategoryOfElementsContra'

/--
Constructor for morphisms in the contravariant category of elements.
Given `f : x.1 ⟶ y.1` in `C` such that `F.map f` takes `y.snd` to `x.snd`,
constructs a morphism `x ⟶ y` in `F.ElementsContra'`.

This is defined using mathlib's `CategoryOfElements.homMk` transferred through
the opposite construction.
-/
def homMk {F : Cᵒᵖ' ⥤ Type w} (x y : F.ElementsContra')
    (f : @Quiver.Hom C _ x.fst y.fst)
    (hf : F.map f y.snd = x.snd) : x ⟶ y :=
  CategoryOfElements.homMk y x f hf

lemma homMk_val {F : Cᵒᵖ' ⥤ Type w} {x y : F.ElementsContra'}
    (f : @Quiver.Hom C _ x.fst y.fst)
    (hf : F.map f y.snd = x.snd) : (homMk x y f hf).val = f :=
  rfl

@[ext]
lemma hom_ext {F : Cᵒᵖ' ⥤ Type w} {x y : F.ElementsContra'} (f g : x ⟶ y)
    (h : f.val = g.val) : f = g := by
  cases f; cases g
  congr

/--
For the contravariant category of elements, composition of morphisms results
in composition in the opposite order in the base category.
-/
@[simp]
theorem comp_val {F : Cᵒᵖ' ⥤ Type w} {p q r : F.ElementsContra'}
    {f : p ⟶ q} {g : q ⟶ r} :
    (f ≫ g).val = g.val ≫ f.val :=
  rfl

/--
The underlying morphism of the identity in the contravariant category of
elements is the identity in `Cᵒᵖ'`.
-/
@[simp]
theorem id_val {F : Cᵒᵖ' ⥤ Type w} {p : F.ElementsContra'} :
    (𝟙 p : p ⟶ p).val = 𝟙 p.1 :=
  rfl

/--
The underlying morphism of `eqToHom` in the contravariant category of elements
is `eqToHom` of the symmetric of the base equality, since morphism `.val`
components go in the opposite direction.
-/
@[simp]
theorem eqToHom_val {F : Cᵒᵖ' ⥤ Type w} {p q : F.ElementsContra'}
    (h : p = q) : (eqToHom h).val = eqToHom (congrArg Sigma.fst h).symm :=
  by cases h; rfl

/--
For a morphism in the contravariant category of elements, the functor maps
the element at the codomain to the element at the domain.
-/
@[simp]
theorem map_snd {F : Cᵒᵖ' ⥤ Type w} {p q : F.ElementsContra'}
    (f : p ⟶ q) :
    (F.map f.val) q.2 = p.2 :=
  f.property

/--
The forgetful functor from the contravariant category of elements,
transferred from mathlib's `CategoryOfElements.π` through the categorical
isomorphisms.
-/
@[simp]
def π (F : Cᵒᵖ' ⥤ Type w) : F.ElementsContra' ⥤ C :=
  Functor.op' (CategoryOfElements.π F)

instance π_faithful (F : Cᵒᵖ' ⥤ Type w) : (π F).Faithful := by
  unfold π
  exact op'_faithful (CategoryOfElements.π F)

/--
The contravariant projection functor reflects isomorphisms.
-/
instance π_reflects_isomorphisms (F : Cᵒᵖ' ⥤ Type w) :
    (π F).ReflectsIsomorphisms := by
  unfold π
  exact op'_reflects_isomorphisms (CategoryOfElements.π F)

/--
Constructor for isomorphisms in the contravariant category of elements.
Given an isomorphism `e : x.1 ≅ y.1` in `C` and proof that `F.map e.hom`
maps `y.snd` to `x.snd`, constructs an isomorphism in `F.ElementsContra'`.

This is defined using mathlib's `CategoryOfElements.isoMk` transferred through
the opposite construction.
-/
def isoMk {F : Cᵒᵖ' ⥤ Type w} (x y : F.ElementsContra')
    (e : @Iso C _ x.1 y.1)
    (he : F.map e.hom y.snd = x.snd) :
    x ≅ y :=
  Iso.symm <|
    (CategoryOfElements.isoMk (C := Cᵒᵖ') (F := F) y x (Iso.symm e))
    (by unfold isoToOp'
        simp only [CategoryOp'.eq_1, CategoryOp'Inst.eq_1, CategoryOpQuivInst.eq_1, Iso.symm_mk]
        exact he)

end CategoryOfElementsContra'

/--
Natural transformations between contravariant functors induce functors between
their categories of elements.

This is defined using mathlib's `NatTrans.mapElements` transferred through
the opposite construction.
-/
def NatTrans.mapElementsContra' {F G : Cᵒᵖ' ⥤ Type w} (φ : F ⟶ G) :
    F.ElementsContra' ⥤ G.ElementsContra' :=
  Functor.op' (φ.mapElements)

namespace CategoryOfElementsContra'

/--
Alias for `NatTrans.mapElementsContra'`.
-/
abbrev map {F G : Cᵒᵖ' ⥤ Type w} (α : F ⟶ G) :
    F.ElementsContra' ⥤ G.ElementsContra' :=
  NatTrans.mapElementsContra' α

@[simp]
theorem map_π {F G : Cᵒᵖ' ⥤ Type w} (α : F ⟶ G) :
    map α ⋙ π G = π F := by
  unfold map NatTrans.mapElementsContra' π
  rw [← Functor.op'_comp]
  rfl

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
        rw [coyoneda'_obj_map]
        exact Category.id_comp q.snd⟩ :
        (elementsToOver X ⋙ overToElements X).obj q ⟶
        (𝟭 ((coyoneda'.obj X).ElementsContra')).obj q)).val =
    ((⟨𝟙 p.fst, by
        change (coyoneda'.obj X).map (𝟙 p.fst) p.snd = p.snd
        rw [coyoneda'_obj_map]
        exact Category.id_comp p.snd⟩ :
        (elementsToOver X ⋙ overToElements X).obj p ⟶
        (𝟭 ((coyoneda'.obj X).ElementsContra')).obj p) ≫ g).val := by
  dsimp [elementsToOver, overToElements]
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
                simp only [(coyoneda'.obj X).map_id, types_id_apply]⟩,
              ⟨𝟙 p.fst, by
                change (coyoneda'.obj X).map (𝟙 p.fst) p.snd = p.snd
                simp only [(coyoneda'.obj X).map_id, types_id_apply]⟩,
              by ext; exact counit_hom_comp_inv X p,
              by ext; exact counit_inv_comp_hom X p⟩)
    (fun g => by ext; exact counit_naturality_val X g)

private lemma functor_unitIso_comp_helper (X : C) (f : Over X) :
    ((overToElements X).map ((overElementsUnitIso X).hom.app f) ≫
     (overElementsCounitIso X).hom.app ((overToElements X).obj f)).val =
    (@CategoryStruct.id ((coyoneda'.obj X).ElementsContra') _
      ((overToElements X).obj f)).val := by
  dsimp [overToElements, elementsToOver, overElementsUnitIso, overElementsCounitIso]
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

end ElementsContra'

section ElementsEquivIso

/-!
## Recovering functors from categories of elements

This section proves that an equivalence of categories of elements that commutes
with the projections to the base category induces a natural isomorphism of the
underlying functors.

Given functors `F, G : J ⥤ Type v` and an equivalence `e : F.Elements ≃ G.Elements`,
if the equivalence commutes with projections (i.e., `e.functor ⋙ π_G = π_F`), then
`F ≅ G`.

The construction works by:
1. The projection-commuting condition ensures the equivalence preserves fibers
2. Restricting to each fiber gives bijections `F.obj j ≃ G.obj j`
3. Functoriality of the equivalence implies naturality of these bijections
-/

variable {J : Type u} [Category.{v} J]

/--
An equivalence of categories of elements over `J`, meaning an equivalence that
commutes with the projections to the base category in both directions, and
whose counit projects to `eqToHom` (identity modulo the base object equality).

The `counit_proj` condition ensures that the counit isomorphism projects to
identity morphisms (via `eqToHom`) when we apply the projection functor. This
is needed to show that the induced natural transformation is indeed a natural
isomorphism (not just a natural transformation between isomorphic objects).
-/
structure ElementsEquivOver (F G : J ⥤ Type w) where
  /-- The underlying equivalence of categories of elements -/
  equiv : F.Elements ≌ G.Elements
  /-- The forward functor commutes with projections -/
  commutes : equiv.functor ⋙ CategoryOfElements.π G = CategoryOfElements.π F
  /-- The inverse functor commutes with projections -/
  commutes_inv : equiv.inverse ⋙ CategoryOfElements.π F = CategoryOfElements.π G
  /-- The counit projects to eqToHom -/
  counit_proj : ∀ q : G.Elements, (equiv.counitIso.hom.app q).val =
      eqToHom (by
        have h1 := congrFun (congrArg Functor.obj commutes) (equiv.inverse.obj q)
        simp only [Functor.comp_obj, CategoryOfElements.π_obj] at h1
        have h2 := congrFun (congrArg Functor.obj commutes_inv) q
        simp only [Functor.comp_obj, CategoryOfElements.π_obj] at h2
        exact h1.trans h2)
  /-- The unit projects to eqToHom -/
  unit_proj : ∀ p : F.Elements, (equiv.unitIso.hom.app p).val =
      eqToHom (by
        have h1 := congrFun (congrArg Functor.obj commutes) p
        simp only [Functor.comp_obj, CategoryOfElements.π_obj] at h1
        have h2 := congrFun (congrArg Functor.obj commutes_inv) (equiv.functor.obj p)
        simp only [Functor.comp_obj, CategoryOfElements.π_obj] at h2
        exact h1.symm.trans h2.symm)

namespace ElementsEquivOver

variable {F G : J ⥤ Type w}

/--
The equivalence preserves the base object: if `e.equiv.functor` sends `⟨j, x⟩`
to some element, that element must be over `j`.
-/
theorem functor_base_eq (e : ElementsEquivOver F G) (p : F.Elements) :
    (e.equiv.functor.obj p).fst = p.fst := by
  have h := congrFun (congrArg Functor.obj e.commutes) p
  simp only [Functor.comp_obj, CategoryOfElements.π_obj] at h
  exact h

/--
The inverse equivalence also preserves the base object.
-/
theorem inverse_base_eq (e : ElementsEquivOver F G) (q : G.Elements) :
    (e.equiv.inverse.obj q).fst = q.fst := by
  have h := congrFun (congrArg Functor.obj e.commutes_inv) q
  simp only [Functor.comp_obj, CategoryOfElements.π_obj] at h
  exact h

/--
The equality proof used in `counit_proj`: the base of `functor.obj (inverse.obj q)`
equals the base of `q`.
-/
def counit_proj_eq (e : ElementsEquivOver F G) (q : G.Elements) :
    (e.equiv.functor.obj (e.equiv.inverse.obj q)).fst = q.fst := by
  have h1 := congrFun (congrArg Functor.obj e.commutes) (e.equiv.inverse.obj q)
  simp only [Functor.comp_obj, CategoryOfElements.π_obj] at h1
  have h2 := congrFun (congrArg Functor.obj e.commutes_inv) q
  simp only [Functor.comp_obj, CategoryOfElements.π_obj] at h2
  exact h1.trans h2

/--
The equality proof used in `unit_proj`: the base of `p` equals the base of
`inverse.obj (functor.obj p)`.
-/
def unit_proj_eq (e : ElementsEquivOver F G) (p : F.Elements) :
    p.fst = (e.equiv.inverse.obj (e.equiv.functor.obj p)).fst := by
  have h1 := congrFun (congrArg Functor.obj e.commutes) p
  simp only [Functor.comp_obj, CategoryOfElements.π_obj] at h1
  have h2 := congrFun (congrArg Functor.obj e.commutes_inv) (e.equiv.functor.obj p)
  simp only [Functor.comp_obj, CategoryOfElements.π_obj] at h2
  exact h1.symm.trans h2.symm

/--
The component of the natural transformation at `j`, sending `x : F.obj j` to
the corresponding element of `G.obj j`.
-/
def natTransApp (e : ElementsEquivOver F G) (j : J) (x : F.obj j) : G.obj j :=
  cast (congrArg G.obj (e.functor_base_eq ⟨j, x⟩)) (e.equiv.functor.obj ⟨j, x⟩).snd

/--
The component of the inverse natural transformation at `j`.
-/
def natTransInvApp (e : ElementsEquivOver F G) (j : J) (y : G.obj j) : F.obj j :=
  cast (congrArg F.obj (e.inverse_base_eq ⟨j, y⟩)) (e.equiv.inverse.obj ⟨j, y⟩).snd

/--
In the Types category, `eqToHom h` equals `cast h` as functions.
This connects the categorical morphism with the type-theoretic cast.
-/
private lemma eqToHom_eq_cast {X Y : Type w} (h : X = Y) (x : X) :
    eqToHom h x = cast h x := by subst h; rfl

/--
Helper lemma for naturality proof: relates cast and functor map.
Uses `Functor.congr_hom` to handle the dependent type equality from `commutes`.
-/
private theorem natTrans_naturality_aux (e : ElementsEquivOver F G) {j k : J}
    (f : j ⟶ k) (x : F.obj j) :
    let pj : F.Elements := ⟨j, x⟩
    let pk : F.Elements := ⟨k, F.map f x⟩
    let qj := e.equiv.functor.obj pj
    let qk := e.equiv.functor.obj pk
    let hj := e.functor_base_eq pj
    let hk := e.functor_base_eq pk
    let morphF : pj ⟶ pk := ⟨f, rfl⟩
    let _morphG := e.equiv.functor.map morphF
    cast (congrArg G.obj hk) qk.snd = G.map f (cast (congrArg G.obj hj) qj.snd) := by
  intro pj pk qj qk hj hk morphF _morphG
  have morphG_val_eq : _morphG.val = eqToHom hj ≫ f ≫ eqToHom hk.symm := by
    have h := Functor.congr_hom e.commutes morphF
    simp only [Functor.comp_map, CategoryOfElements.π_map] at h
    exact h
  have morphG_prop := _morphG.property
  calc cast (congrArg G.obj hk) qk.snd
      = cast (congrArg G.obj hk) (G.map _morphG.val qj.snd) := by rw [morphG_prop]
    _ = G.map (eqToHom hk) (G.map _morphG.val qj.snd) := by
        rw [eqToHom_map G hk, eqToHom_eq_cast]
    _ = G.map (_morphG.val ≫ eqToHom hk) qj.snd := by
        rw [← FunctorToTypes.map_comp_apply]
    _ = G.map (eqToHom hj ≫ f ≫ eqToHom hk.symm ≫ eqToHom hk) qj.snd := by
        rw [morphG_val_eq]; simp only [Category.assoc]
    _ = G.map (eqToHom hj ≫ f) qj.snd := by
        simp only [eqToHom_trans, eqToHom_refl, Category.comp_id]
    _ = G.map f (G.map (eqToHom hj) qj.snd) := by
        rw [FunctorToTypes.map_comp_apply]
    _ = G.map f (cast (congrArg G.obj hj) qj.snd) := by
        rw [eqToHom_map G hj, eqToHom_eq_cast]

/--
The forward map preserves morphisms: functoriality of the equivalence implies
naturality of the induced transformation.
-/
theorem natTrans_naturality (e : ElementsEquivOver F G) {j k : J}
    (f : j ⟶ k) (x : F.obj j) :
    e.natTransApp k (F.map f x) = G.map f (e.natTransApp j x) := by
  simp only [natTransApp]
  exact natTrans_naturality_aux e f x

/--
The inverse naturality: functoriality of the inverse implies naturality.
-/
theorem natTransInv_naturality (e : ElementsEquivOver F G) {j k : J}
    (f : j ⟶ k) (y : G.obj j) :
    e.natTransInvApp k (G.map f y) = F.map f (e.natTransInvApp j y) := by
  simp only [natTransInvApp]
  let qj : G.Elements := ⟨j, y⟩
  let qk : G.Elements := ⟨k, G.map f y⟩
  let pj := e.equiv.inverse.obj qj
  let pk := e.equiv.inverse.obj qk
  have hj : pj.fst = j := e.inverse_base_eq qj
  have hk : pk.fst = k := e.inverse_base_eq qk
  let morphG : qj ⟶ qk := ⟨f, rfl⟩
  let morphF := e.equiv.inverse.map morphG
  have morphF_prop := morphF.property
  have morphF_val_eq : morphF.val = eqToHom hj ≫ f ≫ eqToHom hk.symm := by
    have h := Functor.congr_hom e.commutes_inv morphG
    simp only [Functor.comp_map, CategoryOfElements.π_map] at h
    exact h
  calc cast (congrArg F.obj hk) pk.snd
      = cast (congrArg F.obj hk) (F.map morphF.val pj.snd) := by rw [morphF_prop]
    _ = F.map (eqToHom hk) (F.map morphF.val pj.snd) := by
        rw [eqToHom_map F hk, eqToHom_eq_cast]
    _ = F.map (morphF.val ≫ eqToHom hk) pj.snd := by
        rw [← FunctorToTypes.map_comp_apply]
    _ = F.map (eqToHom hj ≫ f ≫ eqToHom hk.symm ≫ eqToHom hk) pj.snd := by
        rw [morphF_val_eq]; simp only [Category.assoc]
    _ = F.map (eqToHom hj ≫ f) pj.snd := by
        simp only [eqToHom_trans, eqToHom_refl, Category.comp_id]
    _ = F.map f (F.map (eqToHom hj) pj.snd) := by
        rw [FunctorToTypes.map_comp_apply]
    _ = F.map f (cast (congrArg F.obj hj) pj.snd) := by
        rw [eqToHom_map F hj, eqToHom_eq_cast]

/--
The natural transformation from F to G induced by the equivalence.
-/
def toNatTrans (e : ElementsEquivOver F G) : F ⟶ G where
  app j := e.natTransApp j
  naturality j k f := by
    funext x
    exact e.natTrans_naturality f x

/--
The inverse natural transformation from G to F.
-/
def toNatTransInv (e : ElementsEquivOver F G) : G ⟶ F where
  app j := e.natTransInvApp j
  naturality j k f := by
    funext y
    exact e.natTransInv_naturality f y

/--
Helper lemma: composition of casts equals cast of transitive equality.
-/
private lemma cast_trans_eq {X Y Z : Type w} (h1 : X = Y) (h2 : Y = Z) (x : X) :
    cast h2 (cast h1 x) = cast (h1.trans h2) x := by
  subst h1; subst h2; rfl

/--
Helper lemma: an element with cast second component equals the original element.
For `p : Σ j, H.obj j` with `h : p.fst = j`, we have `⟨j, cast h' p.snd⟩ = p`
where `h' = congrArg H.obj h`.
-/
private lemma sigma_cast_snd_eq {H : J ⥤ Type w} (p : H.Elements) {k : J}
    (h : p.fst = k) : (⟨k, cast (congrArg H.obj h) p.snd⟩ : H.Elements) = p := by
  subst h; rfl

/--
When two values are HEq and we cast both to the same target type, the results
are equal. The proofs used for casting may differ but both point to the same
target type.
-/
private lemma cast_heq_cast {A B T : Type w} {a : A} {b : B}
    (hab : a ≍ b) (ha : A = T) (hb : B = T) :
    cast ha a = cast hb b := by
  cases ha; cases hb
  exact eq_of_heq hab

/--
The forward and inverse natural transformations compose to the identity on G.
-/
theorem natTrans_inv_comp (e : ElementsEquivOver F G) :
    e.toNatTransInv ≫ e.toNatTrans = 𝟙 G := by
  ext j y
  simp only [NatTrans.comp_app, types_comp_apply, NatTrans.id_app, types_id_apply,
    toNatTrans, toNatTransInv, natTransApp, natTransInvApp]
  let q : G.Elements := ⟨j, y⟩
  have counit_prop := (e.equiv.counitIso.hom.app q).property
  have counit_val := e.counit_proj q
  simp only [counit_val, eqToHom_map, Functor.comp_obj, Functor.id_obj] at counit_prop
  rw [← eqToHom_eq_cast]
  have hp : (e.equiv.inverse.obj q).fst = j := e.inverse_base_eq q
  have hp' : (⟨j, cast (congrArg F.obj hp) (e.equiv.inverse.obj q).snd⟩ : F.Elements) =
      e.equiv.inverse.obj q := sigma_cast_snd_eq (e.equiv.inverse.obj q) hp
  have functor_eq := congrArg e.equiv.functor.obj hp'
  convert counit_prop using 2
  exact (Sigma.mk.inj_iff.mp functor_eq).2

/--
The inverse and forward natural transformations compose to the identity on F.
This mirrors the structure of `natTrans_inv_comp` but uses the unit property.
-/
theorem natTrans_comp_inv (e : ElementsEquivOver F G) :
    e.toNatTrans ≫ e.toNatTransInv = 𝟙 F := by
  ext j x
  simp only [NatTrans.comp_app, types_comp_apply, NatTrans.id_app, types_id_apply,
    toNatTrans, toNatTransInv, natTransApp, natTransInvApp]
  let p : F.Elements := ⟨j, x⟩
  let q := e.equiv.functor.obj p
  have hq : q.fst = j := e.functor_base_eq p
  have hp : (e.equiv.inverse.obj q).fst = j := (e.inverse_base_eq q).trans hq
  have q_eq : (⟨j, cast (congrArg G.obj hq) q.snd⟩ : G.Elements) = q := sigma_cast_snd_eq q hq
  have inverse_eq : e.equiv.inverse.obj ⟨j, cast (congrArg G.obj hq) q.snd⟩ =
      e.equiv.inverse.obj q := congrArg e.equiv.inverse.obj q_eq
  have snd_heq : (e.equiv.inverse.obj ⟨j, cast (congrArg G.obj hq) q.snd⟩).snd ≍
      (e.equiv.inverse.obj q).snd := (Sigma.mk.inj_iff.mp inverse_eq).2
  have hp_nested : (e.equiv.inverse.obj ⟨j, cast (congrArg G.obj hq) q.snd⟩).fst = j := by
    rw [inverse_eq]; exact hp
  have goal_eq : cast (congrArg F.obj hp_nested)
      (e.equiv.inverse.obj ⟨j, cast (congrArg G.obj hq) q.snd⟩).snd =
      cast (congrArg F.obj hp) (e.equiv.inverse.obj q).snd :=
    cast_heq_cast snd_heq (congrArg F.obj hp_nested) (congrArg F.obj hp)
  rw [goal_eq]
  have unit_inv_prop := (e.equiv.unitIso.inv.app p).property
  simp only [Functor.comp_obj, Functor.id_obj] at unit_inv_prop
  have morph_eq : (e.equiv.unitIso.inv.app p).val = eqToHom hp := by
    have unit_hom_val := e.unit_proj p
    have cat_inv_val : (inv (e.equiv.unitIso.hom.app p)).val =
        eqToHom (e.unit_proj_eq p).symm :=
      CategoryOfElements.val_inv_of_val_eq_eqToHom
        (e.equiv.unitIso.hom.app p) (e.unit_proj_eq p) unit_hom_val
    have inv_eq : inv (e.equiv.unitIso.hom.app p) = e.equiv.unitIso.inv.app p := by
      simp only [← Iso.app_hom, IsIso.Iso.inv_hom, Iso.app_inv]
    rw [inv_eq] at cat_inv_val
    convert cat_inv_val using 1
  calc cast (congrArg F.obj hp) (e.equiv.inverse.obj q).snd
      = F.map (eqToHom hp) (e.equiv.inverse.obj q).snd := by
          rw [eqToHom_map, eqToHom_eq_cast]
    _ = F.map (e.equiv.unitIso.inv.app p).val (e.equiv.inverse.obj q).snd := by
          rw [morph_eq]
    _ = p.snd := unit_inv_prop
    _ = x := rfl

/--
The natural isomorphism from F to G induced by an equivalence of their
categories of elements that commutes with projections.
-/
def toNatIso (e : ElementsEquivOver F G) : F ≅ G where
  hom := e.toNatTrans
  inv := e.toNatTransInv
  hom_inv_id := e.natTrans_comp_inv
  inv_hom_id := e.natTrans_inv_comp

end ElementsEquivOver

variable (F G : J ⥤ Type w)

/--
Given an equivalence of categories of elements that commutes with the
projections to the base category, the underlying functors are naturally
isomorphic.
-/
def elementsEquivOverToNatIso (e : ElementsEquivOver F G) : F ≅ G :=
  e.toNatIso

end ElementsEquivIso

section ElementsEquivOfNatIso

variable {J : Type u} [Category.{v} J]
  {F G : J ⥤ Type w}

/-- A natural transformation `F ⟶ G` induces a
functor `F.Elements ⥤ G.Elements` that preserves
the base object and applies the component at each
fiber. -/
def elementsMapFunctor (α : F ⟶ G) :
    F.Elements ⥤ G.Elements where
  obj p := ⟨p.1, α.app p.1 p.2⟩
  map {p q} f := ⟨f.val, by
    have nat :=
      congrFun (α.naturality f.val) p.2
    simp only [types_comp_apply] at nat
    rw [f.property] at nat
    exact nat.symm⟩
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

@[simp]
theorem elementsMapFunctor_proj (α : F ⟶ G) :
    elementsMapFunctor α ⋙
      CategoryOfElements.π G =
    CategoryOfElements.π F :=
  rfl

/-- A natural isomorphism `F ≅ G` induces an
equivalence of categories of elements. -/
def elementsEquivOfNatIso (α : F ≅ G) :
    F.Elements ≌ G.Elements :=
  { functor := elementsMapFunctor α.hom
    inverse := elementsMapFunctor α.inv
    unitIso := NatIso.ofComponents
      (fun p => {
        hom := ⟨𝟙 p.1, by
          dsimp [elementsMapFunctor]
          simp only [CategoryTheory.Functor.map_id, types_id_apply]
          change p.snd =
            (α.hom ≫ α.inv).app p.fst p.snd
          simp⟩
        inv := ⟨𝟙 p.1, by
          dsimp [elementsMapFunctor]
          simp only [CategoryTheory.Functor.map_id, types_id_apply]
          change
            (α.hom ≫ α.inv).app p.fst p.snd =
            p.snd
          simp⟩
        hom_inv_id :=
          Subtype.ext (Category.id_comp _)
        inv_hom_id :=
          Subtype.ext (Category.id_comp _) })
      (fun f => Subtype.ext (by
        dsimp [elementsMapFunctor]
        simp [Category.id_comp, Category.comp_id]))
    counitIso := NatIso.ofComponents
      (fun q => {
        hom := ⟨𝟙 q.1, by
          dsimp [elementsMapFunctor]
          simp only [CategoryTheory.Functor.map_id, types_id_apply]
          change
            (α.inv ≫ α.hom).app q.fst q.snd =
            q.snd
          simp⟩
        inv := ⟨𝟙 q.1, by
          dsimp [elementsMapFunctor]
          simp only [CategoryTheory.Functor.map_id, types_id_apply]
          change q.snd =
            (α.inv ≫ α.hom).app q.fst q.snd
          simp⟩
        hom_inv_id :=
          Subtype.ext (Category.id_comp _)
        inv_hom_id :=
          Subtype.ext (Category.id_comp _) })
      (fun g => Subtype.ext (by
        dsimp [elementsMapFunctor]
        simp [Category.id_comp, Category.comp_id]))
    functor_unitIso_comp := fun p =>
      Subtype.ext (Category.id_comp _) }

end ElementsEquivOfNatIso

end CategoryTheory
