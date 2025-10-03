import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.FinCategory.Basic

/-!
# Category Judgments

This file defines a finite category whose objects represent the components
needed to specify a category, and whose morphisms represent the
relationships between them.

A category can be defined as a copresheaf (covariant functor to Type)
on this category, where:
- The object `Obj` maps to the type of objects
- The object `Mor` maps to the type of morphisms
- The object `Id` maps to the type of identity judgments
- The object `Comp` maps to the type of composition judgments

The morphisms encode the structure:
- `dom, cod : Mor → Obj` give domain and codomain of morphisms
- `idObj : Id → Obj` and `idMor : Id → Mor` specify which morphism is
  identity for which object
- `left, right, composite : Comp → Mor` specify composition triples
  (where left and right compose to give composite)
- `intermediate, compositeDom, compositeCod : Comp → Obj` specify the
  relevant objects

The categorical structure encodes type correctness constraints:
- `idMor ≫ dom = idObj` and `idMor ≫ cod = idObj` ensure identities
  are endomorphisms
- `right ≫ cod = intermediate` and `left ≫ dom = intermediate` ensure
  composable morphisms share an intermediate object
- `right ≫ dom = compositeDom` and `composite ≫ dom = compositeDom`
  ensure domain is preserved
- `left ≫ cod = compositeCod` and `composite ≫ cod = compositeCod`
  ensure codomain is preserved
-/

namespace CategoryJudgments

/-- The objects of the category judgment category -/
inductive Obj : Type where
  | obj  : Obj  -- represents the type of objects
  | mor  : Obj  -- represents the type of morphisms
  | id   : Obj  -- represents identity judgments
  | comp : Obj  -- represents composition judgments
  deriving DecidableEq, Inhabited

/-- The morphisms of the category judgment category -/
inductive Hom : Obj → Obj → Type where
  -- Identity morphisms
  | identity (X : Obj) : Hom X X

  -- Morphisms from Mor to Obj (domain and codomain)
  | dom : Hom Obj.mor Obj.obj
  | cod : Hom Obj.mor Obj.obj

  -- Morphisms from Id
  | idObj : Hom Obj.id Obj.obj  -- which object this is an identity for
  | idMor : Hom Obj.id Obj.mor  -- which morphism is the identity

  -- Morphisms from Comp to Mor
  | left      : Hom Obj.comp Obj.mor  -- morphism being post-composed
  | right     : Hom Obj.comp Obj.mor  -- morphism being pre-composed
  | composite : Hom Obj.comp Obj.mor  -- resulting composite

  -- Morphisms from Comp to Obj
  | intermediate  : Hom Obj.comp Obj.obj  -- shared intermediate object
  | compositeDom  : Hom Obj.comp Obj.obj  -- domain of composite
  | compositeCod  : Hom Obj.comp Obj.obj  -- codomain of composite
  deriving DecidableEq

/-- Composition of morphisms in the category judgment category -/
def Hom.comp : ∀ {X Y Z : Obj}, Hom X Y → Hom Y Z → Hom X Z
  -- Identity laws
  | _, _, _, identity _, f => f
  | _, _, _, f, identity _ => f

  -- Compositions from Id to Obj (idMor ≫ dom/cod = idObj)
  | _, _, _, idMor, dom => idObj
  | _, _, _, idMor, cod => idObj

  -- Compositions from Comp to Obj via Mor
  | _, _, _, left, dom => intermediate
  | _, _, _, left, cod => compositeCod
  | _, _, _, right, dom => compositeDom
  | _, _, _, right, cod => intermediate
  | _, _, _, composite, dom => compositeDom
  | _, _, _, composite, cod => compositeCod

/-- Left identity law for composition -/
theorem Hom.id_comp : ∀ {X Y : Obj} (f : Hom X Y),
    (identity X).comp f = f
  | _, _, identity _ => rfl
  | _, _, dom => rfl
  | _, _, cod => rfl
  | _, _, idObj => rfl
  | _, _, idMor => rfl
  | _, _, left => rfl
  | _, _, right => rfl
  | _, _, composite => rfl
  | _, _, intermediate => rfl
  | _, _, compositeDom => rfl
  | _, _, compositeCod => rfl

/-- Right identity law for composition -/
theorem Hom.comp_id : ∀ {X Y : Obj} (f : Hom X Y),
    f.comp (identity Y) = f
  | _, _, identity _ => rfl
  | _, _, dom => rfl
  | _, _, cod => rfl
  | _, _, idObj => rfl
  | _, _, idMor => rfl
  | _, _, left => rfl
  | _, _, right => rfl
  | _, _, composite => rfl
  | _, _, intermediate => rfl
  | _, _, compositeDom => rfl
  | _, _, compositeCod => rfl

/-- Associativity of composition -/
theorem Hom.assoc : ∀ {W X Y Z : Obj} (f : Hom W X) (g : Hom X Y)
    (h : Hom Y Z), (f.comp g).comp h = f.comp (g.comp h) := by
  intros W X Y Z f g h
  -- All paths have length at most 2, so we check all cases
  cases f <;> cases g <;> (try cases h) <;> rfl

/-- The category structure on CategoryJudgments -/
instance : CategoryTheory.CategoryStruct Obj where
  Hom := Hom
  id := Hom.identity
  comp := Hom.comp

instance : CategoryTheory.Category Obj where
  id_comp := Hom.id_comp
  comp_id := Hom.comp_id
  assoc := Hom.assoc

/-- Fintype instance for objects -/
instance : Fintype Obj where
  elems := {Obj.obj, Obj.mor, Obj.id, Obj.comp}
  complete := by intro x; cases x <;> simp

/-- Fintype instance for morphisms -/
instance : ∀ (X Y : Obj), Fintype (Hom X Y)
  | .obj, .obj => ⟨{.identity .obj}, by intro f; cases f; simp⟩
  | .obj, .mor => ⟨∅, by intro f; cases f⟩
  | .obj, .id => ⟨∅, by intro f; cases f⟩
  | .obj, .comp => ⟨∅, by intro f; cases f⟩
  | .mor, .obj => ⟨{.dom, .cod}, by intro f; cases f <;> simp⟩
  | .mor, .mor => ⟨{.identity .mor}, by intro f; cases f; simp⟩
  | .mor, .id => ⟨∅, by intro f; cases f⟩
  | .mor, .comp => ⟨∅, by intro f; cases f⟩
  | .id, .obj => ⟨{.idObj}, by intro f; cases f; simp⟩
  | .id, .mor => ⟨{.idMor}, by intro f; cases f; simp⟩
  | .id, .id => ⟨{.identity .id}, by intro f; cases f; simp⟩
  | .id, .comp => ⟨∅, by intro f; cases f⟩
  | .comp, .obj => ⟨{.intermediate, .compositeDom, .compositeCod},
                    by intro f; cases f <;> simp⟩
  | .comp, .mor => ⟨{.left, .right, .composite},
                    by intro f; cases f <;> simp⟩
  | .comp, .id => ⟨∅, by intro f; cases f⟩
  | .comp, .comp => ⟨{.identity .comp}, by intro f; cases f; simp⟩

/-- Fintype instance for category theory morphisms -/
instance (X Y : Obj) : Fintype (X ⟶ Y) :=
  inferInstanceAs (Fintype (Hom X Y))

/-- The category of category judgments is a finite category -/
instance : CategoryTheory.FinCategory Obj where

end CategoryJudgments
