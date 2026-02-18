import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.EqToHom
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Category.Cat.Op
import Mathlib.CategoryTheory.Products.Basic
import GebLean.Utilities.Category

/-!
# Alternative opposite category construction

This module defines an alternative opposite category construction `op'` that
provides definitional equality `op' (op' C) = C`, unlike mathlib's structural
wrapper `Opposite` which only provides propositional equality.

The difference is that `op'` represents opposite categories directly:

- Objects are identical to the original category
- Morphisms are reversed

We then provide isomorphisms and equivalences between our `op'` construction
and mathlib's `Opposite` construction, along with functorial transformations.

-/

universe v u v₁ u₁ v₂ u₂

namespace GebLean

open CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {D : Type u₁} [Category.{v₁} D]

/--
An alternative opposite category that uses the same type for objects but
reverses morphisms. This gives definitional equality `op' (op' C) = C`.
-/
@[simp]
def CategoryOp' (C : Type u) : Type u := C

notation:max C "ᵒᵖ'" => CategoryOp' C

@[simp]
instance CategoryOpQuivInst [Quiver.{v, u} C] : Quiver.{v, u} (CategoryOp' C) where
  Hom X Y := @Quiver.Hom C _ Y X

@[simp]
instance CategoryOp'Inst [CI : Category.{v, u} C] : Category.{v, u} (CategoryOp' C) where
  id X := @CategoryStruct.id C _ X
  comp f g := @CategoryStruct.comp C _ _ _ _ g f
  id_comp f := @Category.comp_id C _ _ _ f
  comp_id f := @Category.id_comp C _ _ _ f
  assoc f g h := (@Category.assoc C _ _ _ _ _ h g f).symm

@[simp]
def op_comp_eq {C : Type u} [CI : Category.{v, u} C] {X Y Z : Cᵒᵖ'}
  (f : @Quiver.Hom Cᵒᵖ' _ X Y) (g : @Quiver.Hom Cᵒᵖ' _ Y Z) :
    f ≫ g =
    @CategoryStruct.comp C _ _ _ _
      (g : @Quiver.Hom C _ Z Y)
      (f : @Quiver.Hom C _ Y X) :=
  rfl

/--
Composition in the opposite of a Pi category, evaluated at an index, equals
the reversed composition at that index.
-/
@[simp]
lemma piOp'_comp_at_idx {I : Type*} {C : I → Type*} [∀ i, Category (C i)]
    {X Y Z : (∀ i, C i)ᵒᵖ'}
    (f : X ⟶ Y) (g : Y ⟶ Z) (i : I) :
    (f ≫ g) i = g i ≫ f i :=
  rfl

/--
Composition with `eqToHom` in the opposite of a Pi category at an index.
In the opposite Pi category, composition is reversed, and `eqToHom` at an
index uses the symmetric equality.
-/
@[simp]
lemma piOp'_fiber_comp_eqToHom_at_idx {I : Type*} {C : I → Type*} [∀ i, Category (C i)]
    {X Y Z : (∀ i, C i)ᵒᵖ'}
    (f : X ⟶ Y) (h : Y = Z) (i : I) :
    (f ≫ eqToHom h) i = eqToHom (congrFun h i).symm ≫ f i := by
  simp only [piOp'_comp_at_idx]
  congr 1
  subst h
  rfl

/--
Definitional equality: `op' (op' C) = C` in one direction.
-/
theorem op'_op'_eq (C : Type u) : (CategoryOp' (CategoryOp' C)) = C := rfl

/--
Definitional equality: `C = op' (op' C)` in the other direction.
-/
theorem eq_op'_op' (C : Type u) : C = (CategoryOp' (CategoryOp' C)) := rfl

/--
The functor from `Cᵒᵖ` to `Cᵒᵖ'` that converts between mathlib's opposite
and our opposite.
-/
@[simp]
def opToOp' : Cᵒᵖ ⥤ Cᵒᵖ' where
  obj X := X.unop
  map f := f.unop
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The `Cat.Hom` version of `opToOp'`. -/
@[simp]
def catOfOpToOp' : Cat.of Cᵒᵖ ⟶ Cat.of Cᵒᵖ' := ⟨opToOp'⟩

/--
The functor from `Cᵒᵖ'` to `Cᵒᵖ` that converts between our opposite and
mathlib's opposite.
-/
@[simp]
def op'ToOp : Cᵒᵖ' ⥤ Cᵒᵖ where
  obj := Opposite.op
  map f := f.op
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The `Cat.Hom` version of `op'ToOp`. -/
@[simp]
def catOfOp'ToOp : Cat.of Cᵒᵖ' ⟶ Cat.of Cᵒᵖ := op'ToOp.toCatHom

/--
The two functors compose to the identity on the nose (actual equality, not just
natural isomorphism).
-/
theorem opToOp'_comp_op'ToOp : opToOp' ⋙ op'ToOp = 𝟭 Cᵒᵖ := rfl

theorem op'ToOp_comp_opToOp' : op'ToOp ⋙ opToOp' = 𝟭 Cᵒᵖ' := rfl

/--
Natural isomorphisms derived from the equalities (for use in contexts requiring
isomorphisms rather than equalities).
-/
@[simp]
def opToOp'Iso : opToOp' ⋙ op'ToOp ≅ 𝟭 Cᵒᵖ :=
  eqToIso opToOp'_comp_op'ToOp

@[simp]
def op'ToOpIso : op'ToOp ⋙ opToOp' ≅ 𝟭 Cᵒᵖ' :=
  eqToIso op'ToOp_comp_opToOp'

/--
Categorical isomorphism between `Cᵒᵖ` and `Cᵒᵖ'` in the category of categories.
-/
@[simp]
def opIsoOp' : Cᵒᵖ ≅Cat Cᵒᵖ' where
  hom := catOfOpToOp'
  inv := catOfOp'ToOp
  hom_inv_id := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor]
    rfl
  inv_hom_id := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor]
    rfl

/--
The categorical equivalence induced by the isomorphism of categories.
-/
@[simp]
def opEquivOp' : Cᵒᵖ ≌ Cᵒᵖ' := Cat.equivOfIso opIsoOp'

@[simp]
instance : Coe Cᵒᵖ Cᵒᵖ' where
  coe := opToOp'.obj

@[simp]
instance : Coe Cᵒᵖ' Cᵒᵖ where
  coe := op'ToOp.obj

/--
Functor-category isomorphisms induced by precomposition and
postcomposition with the isomorphism between `Cᵒᵖ` and `Cᵒᵖ'`.
-/
@[simp]
def preCompToOp : (Cᵒᵖ' ⥤ D) ⥤ (Cᵒᵖ ⥤ D) :=
  (Functor.whiskeringLeft Cᵒᵖ Cᵒᵖ' D).obj opToOp'

@[simp]
def preCompToOp' : (Cᵒᵖ ⥤ D) ⥤ (Cᵒᵖ' ⥤ D) :=
  (Functor.whiskeringLeft Cᵒᵖ' Cᵒᵖ D).obj op'ToOp

@[simp]
def postCompToOp : (C ⥤ Dᵒᵖ') ⥤ (C ⥤ Dᵒᵖ) :=
  (Functor.whiskeringRight C Dᵒᵖ' Dᵒᵖ).obj op'ToOp

@[simp]
def postCompToOp' : (C ⥤ Dᵒᵖ) ⥤ (C ⥤ Dᵒᵖ') :=
  (Functor.whiskeringRight C Dᵒᵖ Dᵒᵖ').obj opToOp'

@[simp]
def biCompToOp : (Cᵒᵖ' ⥤ Dᵒᵖ') ⥤ (Cᵒᵖ ⥤ Dᵒᵖ) :=
  preCompToOp ⋙ postCompToOp

@[simp]
def biCompToOp' : (Cᵒᵖ ⥤ Dᵒᵖ) ⥤ (Cᵒᵖ' ⥤ Dᵒᵖ') :=
  preCompToOp' ⋙ postCompToOp'

/--
Isomorphism of functor categories induced by precomposition with the categorical
isomorphism.
-/
@[simp]
def functorOpIsoOp' : (Cᵒᵖ ⥤ D) ≅Cat (Cᵒᵖ' ⥤ D) where
  hom := preCompToOp'.toCatHom
  inv := preCompToOp.toCatHom
  hom_inv_id := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor,
      Functor.toCatHom_toFunctor]
    rfl
  inv_hom_id := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor,
      Functor.toCatHom_toFunctor]
    rfl

/--
The equivalence of functor categories induced by the isomorphism.
-/
@[simp]
def functorOpEquivOp' : (Cᵒᵖ ⥤ D) ≌ (Cᵒᵖ' ⥤ D) :=
  Cat.equivOfIso functorOpIsoOp'

@[simp]
instance : Coe (Cᵒᵖ ⥤ D) (Cᵒᵖ' ⥤ D) where
  coe := preCompToOp'.obj

@[simp]
instance : Coe (Cᵒᵖ' ⥤ D) (Cᵒᵖ ⥤ D) where
  coe := preCompToOp.obj

/--
Isomorphism of functor categories induced by postcomposition with the categorical
isomorphism.
-/
@[simp]
def functorToOpIsoToOp' : (C ⥤ Dᵒᵖ) ≅Cat (C ⥤ Dᵒᵖ') where
  hom := postCompToOp'.toCatHom
  inv := postCompToOp.toCatHom
  hom_inv_id := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor,
      Functor.toCatHom_toFunctor]
    rfl
  inv_hom_id := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor,
      Functor.toCatHom_toFunctor]
    rfl

/--
The equivalence of functor categories induced by the isomorphism.
-/
@[simp]
def functorToOpEquivToOp' : (C ⥤ Dᵒᵖ) ≌ (C ⥤ Dᵒᵖ') :=
  Cat.equivOfIso functorToOpIsoToOp'

@[simp]
instance : Coe (C ⥤ Dᵒᵖ) (C ⥤ Dᵒᵖ') where
  coe := postCompToOp'.obj

@[simp]
instance : Coe (C ⥤ Dᵒᵖ') (C ⥤ Dᵒᵖ) where
  coe := postCompToOp.obj

/--
Isomorphism of functor categories induced by pre- and postcomposition with the
categorical isomorphisms.
-/
@[simp]
def functorOpOpIsoOp'Op' : (Cᵒᵖ ⥤ Dᵒᵖ) ≅Cat (Cᵒᵖ' ⥤ Dᵒᵖ') :=
  functorOpIsoOp' ≪≫ functorToOpIsoToOp'

/--
The equivalence of functor categories induced by the isomorphism.
-/
@[simp]
def functorOpOpEquivOp'Op' : (Cᵒᵖ ⥤ Dᵒᵖ) ≌ (Cᵒᵖ' ⥤ Dᵒᵖ') :=
  Cat.equivOfIso functorOpOpIsoOp'Op'

@[simp]
instance : Coe (Cᵒᵖ ⥤ Dᵒᵖ) (Cᵒᵖ' ⥤ Dᵒᵖ') where
  coe := biCompToOp'.obj

@[simp]
instance : Coe (Cᵒᵖ' ⥤ Dᵒᵖ') (Cᵒᵖ ⥤ Dᵒᵖ) where
  coe := biCompToOp.obj

/--
An isomorphism in `C` is an isomorphism in `Cᵒᵖ'`.
-/
@[simp]
def isoToOp' {X Y : C} (i : @Iso C _ X Y) : @Iso Cᵒᵖ' _ X Y where
  hom := i.inv
  inv := i.hom
  hom_inv_id := i.hom_inv_id
  inv_hom_id := i.inv_hom_id

@[simp]
def isoFromOp' {X Y : Cᵒᵖ'} (i : @Iso Cᵒᵖ' _ X Y) : @Iso C _ X Y where
  hom := i.inv
  inv := i.hom
  hom_inv_id := i.hom_inv_id
  inv_hom_id := i.inv_hom_id

@[simp]
instance {X Y : C} : Coe (@Iso C _ X Y) (@Iso Cᵒᵖ' _ X Y) where
  coe := isoToOp'

@[simp]
instance {X Y : Cᵒᵖ'} : Coe (@Iso Cᵒᵖ' _ X Y) (@Iso C _ X Y) where
  coe := isoFromOp'

variable {D : Type u₁} [Category.{v₁} D]

def prodOpToOpProd : (C × D)ᵒᵖ' ⥤ (Cᵒᵖ' × Dᵒᵖ') :=
  {
    obj p := (p.1, p.2)
    map f := (f.1, f.2)
  }

def opProdToProdOp : (Cᵒᵖ' × Dᵒᵖ') ⥤ (C × D)ᵒᵖ' :=
  {
    obj p := (p.1, p.2)
    map f := (f.1, f.2)
  }

def prodOpIso : (C × D)ᵒᵖ' ≅Cat (Cᵒᵖ' × Dᵒᵖ') where
  hom := prodOpToOpProd.toCatHom
  inv := opProdToProdOp.toCatHom
  hom_inv_id := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor,
      Functor.toCatHom_toFunctor]
    rfl
  inv_hom_id := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor, Cat.Hom.id_toFunctor,
      Functor.toCatHom_toFunctor]
    rfl

def prodOpEquiv' : (C × D)ᵒᵖ' ≌ (Cᵒᵖ' × Dᵒᵖ') :=
  Cat.equivOfIso prodOpIso

/--
Maps a functor `C ⥤ D` to a functor `Cᵒᵖ' ⥤ Dᵒᵖ'`.
This is the `op'` analogue of `Functor.op` as an operation on objects.
-/
@[simp]
def functorOp'Obj (G : C ⥤ D) : Cᵒᵖ' ⥤ Dᵒᵖ' where
  obj X := G.obj X
  map f := G.map f
  map_id X := G.map_id X
  map_comp f g := G.map_comp g f

/--
The functor `(C ⥤ D)ᵒᵖ' ⥤ (Cᵒᵖ' ⥤ Dᵒᵖ')` mapping functors to their `op'` versions.
This is analogous to mathlib's `opHom : (C ⥤ D)ᵒᵖ ⥤ Cᵒᵖ ⥤ Dᵒᵖ`.
-/
@[simp]
def functorOp' : (C ⥤ D)ᵒᵖ' ⥤ (Cᵒᵖ' ⥤ Dᵒᵖ') where
  obj G := functorOp'Obj G
  map {G H} α := {
    app := fun X => α.app X
    naturality := fun X Y f => (α.naturality f).symm
  }
  map_id G := by
    ext X
    rfl
  map_comp {G H K} α β := by
    ext X
    rfl

/--
The `functorOp'Obj` is equal to composing through the standard opposite.
-/
theorem functorOp'Obj_eq_comp (G : C ⥤ D) :
    functorOp'Obj G = op'ToOp ⋙ G.op ⋙ opToOp' := rfl

namespace Equivalence

/--
Maps an equivalence `C ≌ D` to an equivalence `Cᵒᵖ' ≌ Dᵒᵖ'`.

This composes the standard `Equivalence.op` (which gives `Cᵒᵖ ≌ Dᵒᵖ`) with
the equivalences `opEquivOp'` to get `Cᵒᵖ' ≌ Dᵒᵖ'`.
-/
def op' {C : Type*} [Category C] {D : Type*} [Category D]
    (e : C ≌ D) : Cᵒᵖ' ≌ Dᵒᵖ' :=
  (opEquivOp' (C := C)).symm.trans (e.op.trans (opEquivOp' (C := D)))

end Equivalence

/--
The opposite of a functor `F : C ⥤ D` using the `op'` construction.
For a functor between categories, the opposite functor goes between the
opposite categories.

Since morphisms in `Cᵒᵖ'` from `X` to `Y` are morphisms from `Y` to `X` in `C`,
and composition is reversed, the functor naturally maps them correctly.
-/
@[simp]
def Functor.op' {C D : Type*} [Category C] [Category D] (F : C ⥤ D) :
    Cᵒᵖ' ⥤ Dᵒᵖ' :=
  functorOp'Obj F

/--
For morphisms, isomorphisms transfer between a category and its `op'` opposite.
If `f : Y ⟶ X` is an isomorphism in `C`, then `f : X ⟶ Y` is an isomorphism
in `Cᵒᵖ'` (where the morphism is viewed as going in the opposite direction).
-/
lemma isIso_op'_of_isIso {C : Type*} [Category C] {X Y : C} (f : Y ⟶ X)
    [h : IsIso f] : @IsIso Cᵒᵖ' _ X Y f :=
  ⟨@inv C _ Y X f h, IsIso.inv_hom_id f, IsIso.hom_inv_id f⟩

def opIso {C : Type*} [Category C] {X Y : C}
    (e : Iso (C := C) X Y) : Iso (C := Cᵒᵖ') X Y :=
  {
    hom := e.inv
    inv := e.hom
    hom_inv_id := e.hom_inv_id
    inv_hom_id := e.inv_hom_id
  }

/--
Conversely, if `f` is an isomorphism in `Cᵒᵖ'`, then it is also an isomorphism
in `C`.
-/
lemma isIso_of_isIso_op' {C : Type*} [Category C] {X Y : C} (f : Y ⟶ X)
    [h : @IsIso Cᵒᵖ' _ X Y f] : IsIso f :=
  ⟨@inv Cᵒᵖ' _ X Y f _, @IsIso.inv_hom_id Cᵒᵖ' _ X Y f _, @IsIso.hom_inv_id Cᵒᵖ' _ X Y f _⟩

@[simp]
instance op'_faithful (F : C ⥤ D) [F.Faithful] : (Functor.op' F).Faithful where
  map_injective {X Y} {f g} h := by
    unfold Functor.op' at h
    unfold functorOp'Obj at h
    simp only at h
    exact F.map_injective h

@[simp]
instance op'_reflects_isomorphisms (F : C ⥤ D) [F.ReflectsIsomorphisms] :
    (Functor.op' F).ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    unfold Functor.op' at hf
    unfold functorOp'Obj at hf
    simp only at hf
    haveI h1 : @IsIso D _ _ _ (F.map f) := isIso_of_isIso_op' (F.map f)
    haveI h2 : @IsIso C _ Y X f := Functor.ReflectsIsomorphisms.reflects F f
    exact @isIso_op'_of_isIso C _ X Y f h2

namespace Functor

/--
`Functor.op'` maps the identity functor to the identity functor.
-/
@[simp]
theorem op'_id : Functor.op' (𝟭 C) = 𝟭 Cᵒᵖ' :=
  rfl

/--
`Functor.op'` preserves composition of functors.
-/
theorem op'_comp {E : Type u₂} [Category.{v₂} E]
    (F : C ⥤ D) (G : D ⥤ E) :
    Functor.op' (F ⋙ G) = Functor.op' F ⋙ Functor.op' G :=
  rfl

/--
A natural transformation `α : F ⟶ G` induces a natural transformation
`Functor.op' G ⟶ Functor.op' F` (in the opposite direction) by mapping through `opHom'`.
Since `opHom'` is contravariant, it reverses the direction of natural transformations.
-/
def op'_mapNatTrans {F G : C ⥤ D} (α : F ⟶ G) :
    Functor.op' G ⟶ Functor.op' F :=
  {
    app := fun X => α.app X
    naturality := fun _ _ f => (α.naturality f).symm
  }

/--
The functor `(C ⥤ D)ᵒᵖ' ⥤ (Cᵒᵖ' ⥤ Dᵒᵖ')` that makes "taking the opposite
of a functor" functorial. This is the `op'` analogue of mathlib's `Functor.opHom`.
-/
def opHom' : (C ⥤ D)ᵒᵖ' ⥤ (Cᵒᵖ' ⥤ Dᵒᵖ') where
  obj G := _root_.GebLean.Functor.op' G
  map α := op'_mapNatTrans α
  map_id G := by
    ext X
    rfl
  map_comp {G H K} α β := by
    ext X
    rfl

def op'_mapIso {F G : C ⥤ D} (e : F ≅ G) :
    Functor.op' F ≅ Functor.op' G :=
  Functor.mapIso opHom' e

/--
Natural isomorphism showing that `opHom'` is naturally isomorphic to the
composition that converts through mathlib's `opHom`. This demonstrates that
our `opHom'` is compatible with mathlib's `opHom` via the categorical
isomorphisms between `op` and `op'`.
-/
def opHomIsoOpHom' :
    (op'ToOp ⋙ CategoryTheory.Functor.opHom C D ⋙ biCompToOp' :
      (C ⥤ D)ᵒᵖ' ⥤ (Cᵒᵖ' ⥤ Dᵒᵖ')) ≅ opHom' where
  hom := {
    app := fun F => 𝟙 _
    naturality := by
      intros X Y f
      have h1 := Category.comp_id
        ((op'ToOp ⋙ Functor.opHom C D ⋙
          biCompToOp').map f)
      have h2 := Category.id_comp (opHom'.map f)
      exact h1.trans ((by ext Z; rfl : _ = _).trans
        h2.symm)
  }
  inv := {
    app := fun F => 𝟙 _
    naturality := by
      intros X Y f
      have h1 := Category.comp_id (opHom'.map f)
      have h2 := Category.id_comp
        ((op'ToOp ⋙ Functor.opHom C D ⋙
          biCompToOp').map f)
      exact h1.trans ((by ext Z; rfl : _ = _).trans
        h2.symm)
  }
  hom_inv_id := by
    ext F Z
    simp only [NatTrans.comp_app,
      CategoryTheory.NatTrans.id_app]
    exact Category.comp_id _
  inv_hom_id := by
    ext F Z
    simp only [NatTrans.comp_app,
      CategoryTheory.NatTrans.id_app]
    exact Category.comp_id _

end Functor

namespace Cat

/--
The endofunctor `Cat ⥤ Cat` assigning to each category its opposite category
using the `op'` construction.
-/
def opFunctorObj' (E : Cat.{v, u}) : Cat.{v, u} := .of Eᵒᵖ'

@[simp]
def opFunctor' : Cat.{v, u} ⥤ Cat.{v, u} where
  obj := opFunctorObj'
  map F := (_root_.GebLean.Functor.op' F.toFunctor).toCatHom
  map_id X := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.id_toFunctor, Functor.toCatHom_toFunctor]
    rfl
  map_comp F G := by
    apply Cat.Hom.ext
    simp only [Cat.Hom.comp_toFunctor, Functor.toCatHom_toFunctor]
    rfl

/--
`Functor.op'` maps `eqToHom` functors to `eqToHom` functors.
-/
@[simp]
theorem Functor.op'_eqToHom {C D : Cat.{v, u}} (h : C = D) :
    _root_.GebLean.Functor.op' (eqToHom h).toFunctor =
      (eqToHom (congrArg opFunctorObj' h)).toFunctor := by
  cases h
  rfl

/--
The double application of `Cat.opFunctor'` is equal to the identity functor
on `Cat`. Unlike mathlib's `opFunctor` which is only involutive up to natural
isomorphism, our `opFunctor'` is involutive on the nose because
`(Cᵒᵖ')ᵒᵖ' = C` definitionally.
-/
theorem opFunctor'_comp_self_eq_id : opFunctor'.{v, u} ⋙ opFunctor'.{v, u} = 𝟭 _ := by
  apply _root_.CategoryTheory.Functor.ext
  case h_obj => intro C; rfl
  case h_map =>
    intros C D F
    apply Cat.Hom.ext
    simp only [Functor.comp_map, Functor.id_map]
    rfl

/--
The natural isomorphism between the double application of `Cat.opFunctor'` and
the identity functor on `Cat`, derived from the equality
`opFunctor'_comp_self_eq_id`.
-/
@[simp]
def opFunctor'Involutive : opFunctor'.{v, u} ⋙ opFunctor'.{v, u} ≅ 𝟭 _ :=
  eqToIso opFunctor'_comp_self_eq_id

/--
The isomorphism `Cat ≌ Cat` associating each category with its opposite
category using `op'`. Both the unit and counit are derived from the equality
`opFunctor'_comp_self_eq_id`, showing that this isomorphism is an
equality (strict involution), not only an equivalence.
-/
@[simp]
def opCatIso' : Cat.{v, u} ≅Cat Cat.{v, u} where
  hom := opFunctor'.{v, u}.toCatHom
  inv := opFunctor'.{v, u}.toCatHom

@[simp]
def opEquivalence' : Cat.{v, u} ≌ Cat.{v, u} := Cat.equivOfIso opCatIso'

/--
Natural isomorphism between mathlib's `opFunctor` and our `opFunctor'` as
endofunctors on `Cat`. The components at each category `C` are the categorical
isomorphisms `catOfOpToOp' : Cᵒᵖ ⟶ Cᵒᵖ'`.
-/
@[simp]
def opFunctorIsoOpFunctor' : Cat.opFunctor.{v, u} ≅ opFunctor'.{v, u} where
  hom := {
    app := fun C => catOfOpToOp'
    naturality := by
      intros C D F
      apply Cat.Hom.ext
      apply _root_.CategoryTheory.Functor.ext
      case h_obj =>
        intro X
        rfl
      case h_map =>
        intros X Y f
        change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
        simp only [Category.comp_id, Category.id_comp]
        rfl
  }
  inv := {
    app := fun C => catOfOp'ToOp
    naturality := by
      intros C D F
      apply Cat.Hom.ext
      apply _root_.CategoryTheory.Functor.ext
      case h_obj =>
        intro X
        rfl
      case h_map =>
        intros X Y f
        change _ = 𝟙 _ ≫ _ ≫ 𝟙 _
        simp only [Category.comp_id, Category.id_comp]
        rfl
  }
  hom_inv_id := by
    ext C
    simp only [NatTrans.comp_app, NatTrans.id_app]
    rfl
  inv_hom_id := by
    ext C
    simp only [NatTrans.comp_app, NatTrans.id_app]
    rfl

/--
Functor-category endofunctors induced by precomposition and
postcomposition with `opFunctor'`.
-/
@[simp]
def preCompOpFunctor' : (Cat ⥤ D) ⥤ (Cat ⥤ D) :=
  (Functor.whiskeringLeft Cat Cat D).obj opFunctor'

@[simp]
def postCompOpFunctor' : (C ⥤ Cat) ⥤ (C ⥤ Cat) :=
  (Functor.whiskeringRight C Cat Cat).obj opFunctor'

@[simp]
def biCompOpFunctor : (Cat ⥤ Cat) ⥤ (Cat ⥤ Cat) :=
  preCompOpFunctor' ⋙ postCompOpFunctor'

/--
For a functor `F : Cᵒᵖ' ⥤ Cat`, the object `(Cat.postCompOpFunctor'.obj F).obj X`
is the opposite category of `F.obj X`.
-/
theorem postCompOpFunctor'_obj_eq (F : Cᵒᵖ' ⥤ Cat.{v₁, u₁}) (X : C) :
    (Cat.postCompOpFunctor'.obj F).obj X = Cat.opFunctorObj' (F.obj X) := rfl

/--
An equality proof in an opposite category corresponds to an equality proof in
the reverse direction in the original category. When converting between a
category and its opposite, `eqToHom p` in the opposite category equals
`eqToHom q` in the original category when `p` and `q` are equal object
equalities in opposite directions.
-/
theorem eqToHom_op'_eq {E : Type u₁} [Category.{v₁} E]
    {A B : E} (p : A = B) (q : B = A) :
    @eqToHom (Cat.opFunctorObj' (Cat.of E)) _ A B p =
    @eqToHom E _ B A q := by
  subst q
  rfl

/--
For a functor `F : Cᵒᵖ' ⥤ Cat`, an `eqToHom` in the fiber category of
`postCompOpFunctor'.obj F` (which is opposite) equals an `eqToHom` in the
fiber category of `F` itself (non-opposite) with reversed direction.
-/
theorem eqToHom_postCompOp_eq {C : Type u} [Category.{v} C]
    (F : Cᵒᵖ' ⥤ Cat.{v₁, u₁}) (X : C)
    {A B : F.obj X} (p : A = B) (q : B = A) :
    @eqToHom ((Cat.postCompOpFunctor'.obj F).obj X) _ A B p =
    @eqToHom (F.obj X) _ B A q := by
  subst p
  rfl

/--
For a functor `F : Cᵒᵖ' ⥤ Cat`, the morphism function
`(postCompOpFunctor'.obj F).map φ` equals the opposite functor `(F.map φ).op'`.
-/
@[simp]
theorem postCompOpFunctor'_map_eq {C : Type u} [Category.{v} C]
    (F : Cᵒᵖ' ⥤ Cat.{v₁, u₁}) {X Y : C} (φ : X ⟶ Y) :
    ((Cat.postCompOpFunctor'.obj F).map φ).toFunctor =
      Functor.op' (F.map φ).toFunctor := rfl

end Cat

namespace Functor

namespace MathlibExt

/--
Functor from `Xᵒᵖ ⥤ Y` constructed by taking the opposite of a functor
`G : X ⥤ Yᵒᵖ` and postcomposing with the involutive isomorphism `unopUnop`.
This is the composition `G.op ⋙ unopUnop Y`.
-/
@[simp]
def unopFunctor {X Y : Type _} [Category X] [Category Y] (G : X ⥤ Yᵒᵖ) :
    Xᵒᵖ ⥤ Y :=
  G.op ⋙ unopUnop Y

@[simp]
instance unopFunctor_faithful {X Y : Type _} [Category X] [Category Y]
    (G : X ⥤ Yᵒᵖ) [G.Faithful] : (unopFunctor G).Faithful := by
  unfold unopFunctor
  infer_instance

end MathlibExt

end Functor

section CategoryOpPi

universe w

variable {I : Type*} {C : Type w} [Category C]

/--
In a `Cat.of (CategoryOp' (I → C))` category, `eqToHom` of a function equality
evaluated at an index. In `CategoryOp'`, morphisms go in the opposite direction,
so `eqToHom h` at `i` gives `eqToHom` of the symmetric pointwise equality.
-/
lemma eqToHom_catOp_pi_apply {F G : (Cat.of (CategoryOp' (I → C))).α}
    (h : F = G) (i : I) :
    ((eqToHom h : F ⟶ G) i : G i ⟶ F i) =
      (eqToHom (congrFun h i).symm : G i ⟶ F i) := by
  subst h
  rfl

/--
Evaluating `eqToHom` on a function equality at an index in `CategoryOp'` gives
`eqToHom` of the pointwise equality (with direction reversed).
When applied to an index where types are definitionally equal, this reduces to
identity.
-/
lemma eqToHom_catOp_pi_at_idx {F G : I → C} (h : F = G) (i : I) :
    (eqToHom (C := CategoryOp' (I → C)) h) i =
      (eqToHom (congrFun h i).symm : G i ⟶ F i) :=
  Eq.recOn (motive := fun G' (h' : F = G') =>
    (eqToHom (C := CategoryOp' (I → C)) h') i =
      (eqToHom (congrFun h' i).symm : G' i ⟶ F i)) h rfl

end CategoryOpPi

end GebLean
