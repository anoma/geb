import GebLean.PshRelDouble
import GebLean.Utilities.Profunctors
import Mathlib.CategoryTheory.Functor.FullyFaithful

/-!
# Presheaf Relational Span Category

The diagram category `PshRelSpanObj` generalizes
`RelSpanObj` from `Type`/`Prop` to presheaves on
an arbitrary category `C`, using `PshRel P Q`
(subfunctors of the product presheaf) as
relations.

`RelSpanObj` is the special case where `C` is the
terminal category.
-/

open CategoryTheory

namespace GebLean

universe u v w u' v' w'

variable (C : Type u) [Category.{v} C]

/-- Objects of the presheaf relational span
category: either a type-node for a presheaf
`P : Cᵒᵖ ⥤ Type w`, or a relation-node for a
pair of presheaves with a `PshRel` between
them. -/
inductive PshRelSpanObj :
    Type (max u v (w + 1)) where
  | typeNode : (Cᵒᵖ ⥤ Type w) → PshRelSpanObj
  | relNode :
    (P Q : Cᵒᵖ ⥤ Type w) →
    PshRel P Q → PshRelSpanObj

/-- Morphisms of the presheaf relational span
category: identity morphisms for each object,
and a pair of projections from each
relation-node to its endpoint type-nodes. -/
inductive PshRelSpanHom :
    PshRelSpanObj C →
    PshRelSpanObj C →
    Type (max u v (w + 1)) where
  | id : (X : PshRelSpanObj C) →
    PshRelSpanHom X X
  | fstProj :
    (P Q : Cᵒᵖ ⥤ Type w) →
    (R : PshRel P Q) →
    PshRelSpanHom (.relNode P Q R)
      (.typeNode P)
  | sndProj :
    (P Q : Cᵒᵖ ⥤ Type w) →
    (R : PshRel P Q) →
    PshRelSpanHom (.relNode P Q R)
      (.typeNode Q)

/-- Composition of morphisms in
`PshRelSpanObj`. No composable pair of
non-identity morphisms exists, since all
generators map from relation-nodes to
type-nodes. -/
def PshRelSpanHom.comp :
    {X Y Z : PshRelSpanObj C} →
    PshRelSpanHom C X Y →
    PshRelSpanHom C Y Z →
    PshRelSpanHom C X Z
  | _, _, _, .id _, g => g
  | _, _, _, f, .id _ => f

instance PshRelSpanCatStruct :
    CategoryStruct
      (PshRelSpanObj.{u, v, w} C) where
  Hom := PshRelSpanHom C
  id X := PshRelSpanHom.id X
  comp := PshRelSpanHom.comp C

theorem PshRelSpanHom.id_comp
    {X Y : PshRelSpanObj C}
    (f : PshRelSpanHom C X Y) :
    PshRelSpanHom.comp C (.id X) f = f := by
  cases f <;> rfl

theorem PshRelSpanHom.comp_id
    {X Y : PshRelSpanObj C}
    (f : PshRelSpanHom C X Y) :
    PshRelSpanHom.comp C f (.id Y) = f := by
  cases f <;> rfl

theorem PshRelSpanHom.assoc
    {W X Y Z : PshRelSpanObj C}
    (f : PshRelSpanHom C W X)
    (g : PshRelSpanHom C X Y)
    (h : PshRelSpanHom C Y Z) :
    PshRelSpanHom.comp C
      (PshRelSpanHom.comp C f g) h =
    PshRelSpanHom.comp C f
      (PshRelSpanHom.comp C g h) := by
  cases f <;> cases g <;> cases h <;> rfl

instance PshRelSpanCat :
    SmallCategory.{max u v (w + 1)} (PshRelSpanObj.{u, v, w} C) where
  id_comp := PshRelSpanHom.id_comp C
  comp_id := PshRelSpanHom.comp_id C
  assoc := PshRelSpanHom.assoc C

/-- Presheaf-valued parametric functors on
`PshRelSpanObj C`: functors from
`PshRelSpanObj C` to the presheaf category
`Dᵒᵖ ⥤ Type w'`.

By uncurrying, this is equivalent to
`(PshRelSpanObj C × D)ᵒᵖ ⥤ Type w'`, a
presheaf topos. The case `D` = discrete
unit category recovers `Type w'`-valued
parametric functors. -/
abbrev PshParametricFunctor
    (D : Type u') [Category.{v'} D] :=
  PshRelSpanObj.{u, v, w} C ⥤
    (Dᵒᵖ ⥤ Type w')

/-- The currying equivalence identifying
presheaf-valued parametric functors with
copresheaves on the product category
`PshRelSpanObj C × Dᵒᵖ`. -/
def pshParametricCatAsCopresheaf
    (D : Type u') [Category.{v'} D] :
    (PshParametricFunctor.{u, v, w, u', v', w'} C D) ≌
    (PshRelSpanObj.{u, v, w} C × Dᵒᵖ ⥤ Type w') :=
  Functor.currying

/-- The presheaf-category equivalence: the
category of presheaf-valued parametric
functors is equivalent to a presheaf
topos on `(PshRelSpanObj C)ᵒᵖ × D`.

Constructed by composing the currying
equivalence with precomposition by
`pshRelSpanProdOpFwd`. -/
def pshParametricCatAsPresheaf
    (D : Type u') [Category.{v'} D] :
    (PshParametricFunctor.{u, v, w, u', v', w'} C D) ≌
    (((PshRelSpanObj.{u, v, w} C)ᵒᵖ × D)ᵒᵖ ⥤ Type w') :=
  CategoryTheory.Equivalence.trans
    (pshParametricCatAsCopresheaf C D)
    ((opProdOpProdOpEquiv.{max u v (w + 1), max u v (w + 1), v', u'}
      (PshRelSpanObj C) D).congrLeft (E := Type w')).symm

end GebLean
