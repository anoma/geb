import Mathlib.CategoryTheory.Elements
import Mathlib.CategoryTheory.Yoneda
import Mathlib.CategoryTheory.Comma.Over.Basic
import Mathlib.CategoryTheory.Whiskering
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
      simp
    refine Sigma.ext hx ?_
    simp
    convert heq_of_eq h using 2 <;> try exact sigma_ext_rfl_heq hx
    congr 2
    · funext; simp
    exact proof_irrel_heq rfl hx
  map_comp := by
    intros X Y Z f g
    ext ⟨x, gx⟩
    · simp
    · simp
      have h := congrFun (@Functor.map_comp _ _ _ _ G ⟨X, x⟩ ⟨Y, F.map f x⟩ ⟨Z, F.map g (F.map f x)⟩
        ⟨f, rfl⟩ ⟨g, rfl⟩) gx
      simp only [types_comp_apply] at h
      have hcomp : F.map (f ≫ g) x = F.map g (F.map f x) := by
        rw [F.map_comp]; rfl
      convert heq_of_eq h using 2 <;> try exact sigma_ext_rfl_heq hcomp
      congr 2
      · funext; simp
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
          simp
          congr 1
          · funext y
            rw [hfx]
          · exact proof_irrel_heq _ _ }
      (by ext X x; rfl))
    (fun {η₁ η₂} α => by
      ext X fx
      dsimp [sliceToCopresheaf, copresheafToSlice, totalSpace, Fiber]
      refine Sigma.ext (congrFun (congrFun (congrArg NatTrans.app α.w) X) fx) ?_
      simp
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
          -- y : { z : Σ (x : F.obj p.fst), G.obj ⟨p.fst, x⟩ // z.fst = p.snd }
          have hp : (⟨p.fst, y.val.fst⟩ : F.Elements) = p := by
            ext
            · rfl
            · exact heq_of_eq y.property
          exact hp ▸ y.val.snd
        inv := fun gx => by
          dsimp [sliceToCopresheaf, copresheafToSlice, Fiber, totalSpace, totalSpaceProj]
          -- gx : G.obj p
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
        -- hx : x = p.snd
        -- Define the equality proofs explicitly
        have hp : (⟨p.fst, x⟩ : F.Elements) = p := by
          ext
          · rfl
          · exact heq_of_eq hx
        have hq : (⟨q.fst, F.map f.val x⟩ : F.Elements) = q := by
          ext
          · rfl
          · -- Need: F.map f.val x ≍ q.snd
            -- Since f : p ⟶ q in F.Elements, we have F.map f.val p.snd = q.snd
            have fprop : F.map f.val p.snd = q.snd := f.property
            -- x = p.snd by hx, so F.map f.val x = q.snd
            have : F.map f.val x = q.snd := by
              rw [hx, fprop]
            exact heq_of_eq this
        -- Component naturality
        subst hx
        -- Now apply transport_heq to eliminate the Sigma.ext transport
        apply transport_heq
        -- Goal: G.map ⟨↑f, proof⟩ gx ≍ G.map f gx where proof is some equality
        -- Use cases on f to destructure it into its morphism and property
        cases f with
        | mk fval fprop =>
          -- Now f = ⟨fval, fprop⟩ definitionally
          -- Use cases on the proof from totalSpace
          generalize totalSpace._proof_1 F G fval ⟨p.snd, gx⟩ = proof
          cases proof
          -- After cases, the LHS has ⟨↑⟨fval, fprop⟩, Eq.refl ...⟩
          -- Simplify ↑⟨fval, fprop⟩ to fval
          simp only [Subtype.coe_mk]
          -- Use cases on p and q to eliminate eta-expansions
          cases p with | mk p₁ p₂ =>
          cases q with | mk q₁ q₂ =>
          -- Simplify projections but keep hq as an equation between Sigmas
          simp at fprop gx ⊢
          -- Use cases on hp
          cases hp
          -- Use injection on hq to get q₂ = F.map fval p₂
          injection hq with hq₁ hq₂
          -- We have destructed too much - the types no longer align
          -- The morphisms live in different hom-sets after all the cases
          -- But they should be related through the equalities hp, hq
          -- Try using funext or other extensionality principles
          -- Or use grind to solve this automatically
          grind
        ))
    (fun {G H} α => by
      ext p ⟨⟨x, gx⟩, hx⟩
      dsimp [sliceToCopresheaf, copresheafToSlice, Fiber, totalSpace, totalSpaceProj] at hx ⊢
      -- hx : x = p.snd
      have hp : (⟨p.fst, x⟩ : F.Elements) = p := by
        ext
        · rfl
        · exact heq_of_eq hx
      -- Outer naturality
      subst hx
      simp_all only []
      -- Use the same generalize + cases approach
      generalize hp_eq : hp = hp'
      cases hp'
      -- After cases, p is in canonical form
      simp_all only []
      -- The goal should now simplify
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
  simp
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
  simp [Fiber]
  -- Goal: ↑(⋯ ▸ ⟨↑a, ⋯⟩) = ↑a
  generalize_proofs pf₁ pf₂
  exact triangle_identity_transport η.hom p a pf₁ pf₂

/--
The categorical equivalence between `Over F` and copresheaves on `F.Elements`.
-/
def sliceEquivCopresheaf : Over F ≌ (F.Elements ⥤ Type w) where
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

instance (F : Cᵒᵖ' ⥤ Type w) : Category F.ElementsContra' :=
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
               elementsContra'ToElementsContra, elementsContraToElementsContra']
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
               elementsContraToElementsContra', elementsContra'ToElementsContra]
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

namespace CategoryOfElementsContra'

/--
Constructor for morphisms in the contravariant category of elements.
Given `f : x.1 ⟶ y.1` in `C` such that `F.map f` takes `y.snd` to `x.snd`,
constructs a morphism `x ⟶ y` in `F.ElementsContra'`.

This is defined using mathlib's `CategoryOfElements.homMk` transferred through
the opposite construction.
-/
def homMk {F : Cᵒᵖ' ⥤ Type w} (x y : F.ElementsContra')
    (f : @Quiver.Hom C _ x.1 y.1)
    (hf : F.map f y.snd = x.snd) : x ⟶ y :=
  CategoryOfElements.homMk y x f hf

lemma homMk_val {F : Cᵒᵖ' ⥤ Type w} {x y : F.ElementsContra'}
    (f : @Quiver.Hom C _ x.1 y.1)
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
    (by unfold isoToOp' ; simp ; exact he)

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
  rw [← op'_comp]
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

end ElementsContra'

end CategoryTheory
