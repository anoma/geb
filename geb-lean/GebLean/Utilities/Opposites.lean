import Mathlib.CategoryTheory.Opposites
import Mathlib.CategoryTheory.Equivalence
import Mathlib.CategoryTheory.Whiskering
import Mathlib.CategoryTheory.EqToHom
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

universe v u v₁ u₁

namespace GebLean

open CategoryTheory

variable {C : Type u} [Category.{v} C]
variable {D : Type u₁} [Category.{v₁} D]

/--
An alternative opposite category that uses the same type for objects but
reverses morphisms. This gives definitional equality `op' (op' C) = C`.
-/
def CategoryOp' (C : Type u) : Type u := C

notation:max C "ᵒᵖ'" => CategoryOp' C

instance [Quiver.{v} C] : Quiver.{v} (CategoryOp' C) where
  Hom X Y := @Quiver.Hom C _ Y X

instance [Category.{v} C] : Category.{v} (CategoryOp' C) where
  id X := @CategoryStruct.id C _ X
  comp f g := @CategoryStruct.comp C _ _ _ _ g f
  id_comp f := @Category.comp_id C _ _ _ f
  comp_id f := @Category.id_comp C _ _ _ f
  assoc f g h := (@Category.assoc C _ _ _ _ _ h g f).symm

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
def catOfOpToOp' : Cat.of Cᵒᵖ ⟶ Cat.of Cᵒᵖ' where
  obj X := X.unop
  map f := f.unop
  map_id _ := rfl
  map_comp _ _ := rfl

def opToOp' : Cᵒᵖ ⥤ Cᵒᵖ' := catOfOpToOp'

/--
The functor from `Cᵒᵖ'` to `Cᵒᵖ` that converts between our opposite and
mathlib's opposite.
-/
def catOfOp'ToOp : Cat.of Cᵒᵖ' ⟶ Cat.of Cᵒᵖ where
  obj := Opposite.op
  map f := f.op
  map_id _ := rfl
  map_comp _ _ := rfl

def op'ToOp : Cᵒᵖ' ⥤ Cᵒᵖ := catOfOp'ToOp

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
def opToOp'Iso : opToOp' ⋙ op'ToOp ≅ 𝟭 Cᵒᵖ :=
  eqToIso opToOp'_comp_op'ToOp

def op'ToOpIso : op'ToOp ⋙ opToOp' ≅ 𝟭 Cᵒᵖ' :=
  eqToIso op'ToOp_comp_opToOp'

/--
Categorical isomorphism between `Cᵒᵖ` and `Cᵒᵖ'` in the category of categories.
-/
def opIsoOp' : Cᵒᵖ ≅Cat Cᵒᵖ' where
  hom := catOfOpToOp'
  inv := catOfOp'ToOp
  hom_inv_id := rfl
  inv_hom_id := rfl

/--
The categorical equivalence induced by the isomorphism of categories.
-/
def opEquivOp' : Cᵒᵖ ≌ Cᵒᵖ' := Cat.equivOfIso opIsoOp'

instance : Coe Cᵒᵖ Cᵒᵖ' where
  coe := opToOp'.obj

instance : Coe Cᵒᵖ' Cᵒᵖ where
  coe := op'ToOp.obj

/--
Functor-category isomorphisms induced by precomposition and
postcomposition with the isomorphism between `Cᵒᵖ` and `Cᵒᵖ'`.
-/
def preCompToOp : (Cᵒᵖ' ⥤ D) ⥤ (Cᵒᵖ ⥤ D) :=
  (Functor.whiskeringLeft Cᵒᵖ Cᵒᵖ' D).obj catOfOpToOp'

def preCompToOp' : (Cᵒᵖ ⥤ D) ⥤ (Cᵒᵖ' ⥤ D) :=
  (Functor.whiskeringLeft Cᵒᵖ' Cᵒᵖ D).obj catOfOp'ToOp

def postCompToOp : (C ⥤ Dᵒᵖ') ⥤ (C ⥤ Dᵒᵖ) :=
  (Functor.whiskeringRight C Dᵒᵖ' Dᵒᵖ).obj catOfOp'ToOp

def postCompToOp' : (C ⥤ Dᵒᵖ) ⥤ (C ⥤ Dᵒᵖ') :=
  (Functor.whiskeringRight C Dᵒᵖ Dᵒᵖ').obj catOfOpToOp'

def biCompToOp : (Cᵒᵖ' ⥤ Dᵒᵖ') ⥤ (Cᵒᵖ ⥤ Dᵒᵖ) :=
  preCompToOp ⋙ postCompToOp

def biCompToOp' : (Cᵒᵖ ⥤ Dᵒᵖ) ⥤ (Cᵒᵖ' ⥤ Dᵒᵖ') :=
  preCompToOp' ⋙ postCompToOp'

/--
Isomorphism of functor categories induced by precomposition with the categorical
isomorphism.
-/
def functorOpIsoOp' : (Cᵒᵖ ⥤ D) ≅Cat (Cᵒᵖ' ⥤ D) where
  hom := preCompToOp'
  inv := preCompToOp
  hom_inv_id := rfl
  inv_hom_id := rfl

/--
The equivalence of functor categories induced by the isomorphism.
-/
def functorOpEquivOp' : (Cᵒᵖ ⥤ D) ≌ (Cᵒᵖ' ⥤ D) :=
  Cat.equivOfIso functorOpIsoOp'

instance : Coe (Cᵒᵖ ⥤ D) (Cᵒᵖ' ⥤ D) where
  coe := preCompToOp'.obj

instance : Coe (Cᵒᵖ' ⥤ D) (Cᵒᵖ ⥤ D) where
  coe := preCompToOp.obj

/--
Isomorphism of functor categories induced by postcomposition with the categorical
isomorphism.
-/
def functorToOpIsoToOp' : (C ⥤ Dᵒᵖ) ≅Cat (C ⥤ Dᵒᵖ') where
  hom := postCompToOp'
  inv := postCompToOp
  hom_inv_id := rfl
  inv_hom_id := rfl

/--
The equivalence of functor categories induced by the isomorphism.
-/
def functorToOpEquivToOp' : (C ⥤ Dᵒᵖ) ≌ (C ⥤ Dᵒᵖ') :=
  Cat.equivOfIso functorToOpIsoToOp'

instance : Coe (C ⥤ Dᵒᵖ) (C ⥤ Dᵒᵖ') where
  coe := postCompToOp'.obj

instance : Coe (C ⥤ Dᵒᵖ') (C ⥤ Dᵒᵖ) where
  coe := postCompToOp.obj

/--
Isomorphism of functor categories induced by pre- and postcomposition with the
categorical isomorphisms.
-/
def functorOpOpIsoOp'Op' : (Cᵒᵖ ⥤ Dᵒᵖ) ≅Cat (Cᵒᵖ' ⥤ Dᵒᵖ') :=
  functorOpIsoOp' ≪≫ functorToOpIsoToOp'

/--
The equivalence of functor categories induced by the isomorphism.
-/
def functorOpOpEquivOp'Op' : (Cᵒᵖ ⥤ Dᵒᵖ) ≌ (Cᵒᵖ' ⥤ Dᵒᵖ') :=
  Cat.equivOfIso functorOpOpIsoOp'Op'

instance : Coe (Cᵒᵖ ⥤ Dᵒᵖ) (Cᵒᵖ' ⥤ Dᵒᵖ') where
  coe := biCompToOp'.obj

instance : Coe (Cᵒᵖ' ⥤ Dᵒᵖ') (Cᵒᵖ ⥤ Dᵒᵖ) where
  coe := biCompToOp.obj

/--
An isomorphism in `C` is an isomorphism in `Cᵒᵖ'`.
-/
def isoToOp' {X Y : C} :
  ((X : C) ≅ (Y : C)) -> ((X : Cᵒᵖ') ≅ (Y : Cᵒᵖ')) := id
def isoFromOp' {X Y : Cᵒᵖ'} :
  ((X : Cᵒᵖ') ≅ (Y : Cᵒᵖ')) -> ((X : C) ≅ (Y : C)) := id

instance {X Y : C} : Coe ((X : C) ≅ (Y : C)) ((X : Cᵒᵖ') ≅ (Y : Cᵒᵖ')) where
  coe := isoToOp'

instance {X Y : Cᵒᵖ'} : Coe ((X : Cᵒᵖ') ≅ (Y : Cᵒᵖ')) ((X : C) ≅ (Y : C)) where
  coe := isoFromOp'

variable {D : Type u₁} [Category.{v₁} D]

/--
The contravariant opposite functor, mapping `C ⥤ D` to `Cᵒᵖ' ⥤ Dᵒᵖ'`.
This is the `op'` analogue of `Functor.op`.
-/
def functorOp' (G : C ⥤ D) : Cᵒᵖ' ⥤ Dᵒᵖ' where
  obj X := G.obj X
  map f := G.map f
  map_id X := G.map_id X
  map_comp f g := G.map_comp g f

/--
The `functorOp'` is equal to composing through the standard opposite.
-/
theorem functorOp'_eq_comp (G : C ⥤ D) :
    functorOp' G = op'ToOp ⋙ G.op ⋙ opToOp' := rfl

end GebLean
