import GebLean.PLang.CatJudgment
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Functor.Currying
import Mathlib.CategoryTheory.Products.Basic

/-!
# The Judgment Universe

This module defines the judgment universe functor, which organizes the
hierarchy of categorical structures (objects, quivers, categories) as a
functor from a small index category to Cat.

The judgment category J has three objects representing levels of
categorical structure:
- `obj`: just a type (objects of a would-be category)
- `quiv`: a quiver (objects + morphisms + domain/codomain)
- `cat`: a full category (quiver + identity + composition + axioms)

The judgment universe functor `JudgmentUniverse : J ⥤ Cat` maps:
- `obj` ↦ ObjCopr (the category of types)
- `quiv` ↦ ObjMorCopr (the category of quivers)
- `cat` ↦ CatJudgCopr (the category of category-structures)

Sections of this functor correspond to complete category specifications.
-/

namespace GebLean

namespace PLang

open CategoryTheory

universe u v w x

/-- The objects of the judgment category: levels of categorical structure. -/
inductive JudgmentLevel : Type where
  | obj : JudgmentLevel
  | quiv : JudgmentLevel
  | cat : JudgmentLevel
  deriving DecidableEq, Repr

namespace JudgmentLevel

/-- Morphisms in the judgment category represent forgetful relations.
    A morphism `j → j'` means there's a forgetful functor from j-structures
    to j'-structures (j has more structure than j'). -/
inductive Hom : JudgmentLevel → JudgmentLevel → Type where
  | id (j : JudgmentLevel) : Hom j j
  | quivToObj : Hom quiv obj
  | catToQuiv : Hom cat quiv
  | catToObj : Hom cat obj
  deriving DecidableEq, Repr

/-- Composition of morphisms in the judgment category. -/
def Hom.comp : {j₁ j₂ j₃ : JudgmentLevel} → Hom j₁ j₂ → Hom j₂ j₃ → Hom j₁ j₃
  | _, _, _, .id _, g => g
  | _, _, _, f, .id _ => f
  | .cat, .quiv, .obj, .catToQuiv, .quivToObj => .catToObj

/-- Left identity law for composition. -/
theorem Hom.id_comp {j₁ j₂ : JudgmentLevel} (f : Hom j₁ j₂) :
    Hom.comp (.id j₁) f = f := by
  cases f <;> rfl

/-- Right identity law for composition. -/
theorem Hom.comp_id {j₁ j₂ : JudgmentLevel} (f : Hom j₁ j₂) :
    Hom.comp f (.id j₂) = f := by
  cases f <;> rfl

/-- Associativity of composition. -/
theorem Hom.comp_assoc {j₁ j₂ j₃ j₄ : JudgmentLevel}
    (f : Hom j₁ j₂) (g : Hom j₂ j₃) (h : Hom j₃ j₄) :
    Hom.comp (Hom.comp f g) h = Hom.comp f (Hom.comp g h) := by
  cases f <;> cases g <;> cases h <;> rfl

end JudgmentLevel

/-- The judgment category has judgment levels as objects and refinement
    morphisms as arrows. -/
instance : Category JudgmentLevel where
  Hom := JudgmentLevel.Hom
  id := JudgmentLevel.Hom.id
  comp := JudgmentLevel.Hom.comp
  id_comp := JudgmentLevel.Hom.id_comp
  comp_id := JudgmentLevel.Hom.comp_id
  assoc := JudgmentLevel.Hom.comp_assoc

/-! ## JudgmentUniverse functor

The judgment universe maps each judgment level to the corresponding category
of structures. Due to universe constraints, we work with fixed universe levels.
-/

/-- The type at each judgment level, with fixed universe uJ.
    All three levels produce types in Type (uJ + 2). -/
def JudgmentLevel.StructType.{uJ} : JudgmentLevel → Type (uJ + 2)
  | .obj => Obj.ObjCopr.{uJ + 2}
  | .quiv => Obj.ObjMorCopr.{uJ + 1, uJ + 1}
  | .cat => Obj.CatJudgCopr.{uJ + 1, uJ + 1, uJ + 1, uJ + 1}

/-- Category instance for StructType at the obj level. -/
instance JudgmentLevel.StructType.catObj.{uJ} :
    LargeCategory.{uJ + 1} (JudgmentLevel.StructType.{uJ} .obj) :=
  Cat.ObjCopr.category.{uJ + 1}

/-- Category instance for StructType at the quiv level. -/
instance JudgmentLevel.StructType.catQuiv.{uJ} :
    LargeCategory.{uJ + 1} (JudgmentLevel.StructType.{uJ} .quiv) :=
  Cat.ObjMorCopr.category.{uJ, uJ}

/-- Category instance for StructType at the cat level. -/
instance JudgmentLevel.StructType.catCat.{uJ} :
    LargeCategory.{uJ + 1} (JudgmentLevel.StructType.{uJ} .cat) :=
  Cat.CatJudgCopr.category.{uJ, uJ, uJ, uJ}

/-- The forgetful functor from quiv to obj level. -/
def JudgmentLevel.forgetQuivToObj.{uJ} :
    JudgmentLevel.StructType.{uJ} .quiv ⥤ JudgmentLevel.StructType.{uJ} .obj :=
  Cat.forgetObjMorToObj.{uJ, uJ}

/-- The forgetful functor from cat to quiv level. -/
def JudgmentLevel.forgetCatToQuiv.{uJ} :
    JudgmentLevel.StructType.{uJ} .cat ⥤ JudgmentLevel.StructType.{uJ} .quiv :=
  Cat.forgetCatJudgToObjMor.{uJ, uJ, uJ, uJ}

/-- The forgetful functor from cat to obj level. -/
def JudgmentLevel.forgetCatToObj.{uJ} :
    JudgmentLevel.StructType.{uJ} .cat ⥤ JudgmentLevel.StructType.{uJ} .obj :=
  Cat.forgetCatJudgToObj.{uJ, uJ, uJ, uJ}

/-- Convert a judgment level to an object of Cat. -/
def JudgmentLevel.toCat.{uJ} : JudgmentLevel → Cat.{uJ + 1, uJ + 2}
  | .obj => Cat.of (Obj.ObjCopr.{uJ + 2})
  | .quiv => Cat.of (Obj.ObjMorCopr.{uJ + 1, uJ + 1})
  | .cat => Cat.of (Obj.CatJudgCopr.{uJ + 1, uJ + 1, uJ + 1, uJ + 1})

/-- The functor associated with the quivToObj morphism. -/
def JudgmentLevel.forgetQuivToObjAsCat.{uJ} :
    JudgmentLevel.toCat.{uJ} .quiv ⥤ JudgmentLevel.toCat.{uJ} .obj :=
  Cat.forgetObjMorToObj.{uJ, uJ}

/-- The functor associated with the catToQuiv morphism. -/
def JudgmentLevel.forgetCatToQuivAsCat.{uJ} :
    JudgmentLevel.toCat.{uJ} .cat ⥤ JudgmentLevel.toCat.{uJ} .quiv :=
  Cat.forgetCatJudgToObjMor.{uJ, uJ, uJ, uJ}

/-- The functor associated with the catToObj morphism. -/
def JudgmentLevel.forgetCatToObjAsCat.{uJ} :
    JudgmentLevel.toCat.{uJ} .cat ⥤ JudgmentLevel.toCat.{uJ} .obj :=
  Cat.forgetCatJudgToObj.{uJ, uJ, uJ, uJ}

/-- The functor associated with each morphism in the judgment category,
    as a morphism in Cat. -/
def JudgmentLevel.Hom.toCatHom.{uJ} : {j₁ j₂ : JudgmentLevel} →
    JudgmentLevel.Hom j₁ j₂ →
    (JudgmentLevel.toCat.{uJ} j₁ ⟶ JudgmentLevel.toCat.{uJ} j₂)
  | .obj, .obj, .id .obj => (𝟭 _).toCatHom
  | .quiv, .quiv, .id .quiv => (𝟭 _).toCatHom
  | .cat, .cat, .id .cat => (𝟭 _).toCatHom
  | .quiv, .obj, .quivToObj => JudgmentLevel.forgetQuivToObjAsCat.{uJ}.toCatHom
  | .cat, .quiv, .catToQuiv => JudgmentLevel.forgetCatToQuivAsCat.{uJ}.toCatHom
  | .cat, .obj, .catToObj => JudgmentLevel.forgetCatToObjAsCat.{uJ}.toCatHom

/-- Identity morphisms map to identity morphisms in Cat. -/
theorem JudgmentLevel.Hom.toCatHom_id.{uJ} (j : JudgmentLevel) :
    JudgmentLevel.Hom.toCatHom.{uJ} (.id j) = 𝟙 (JudgmentLevel.toCat.{uJ} j) := by
  cases j <;> rfl

/-- The composition of forgetful functors catToQuiv and quivToObj equals catToObj. -/
theorem JudgmentLevel.forgetCatToObj_eq_comp.{uJ} :
    JudgmentLevel.forgetCatToObjAsCat.{uJ} =
    JudgmentLevel.forgetCatToQuivAsCat.{uJ} ⋙ JudgmentLevel.forgetQuivToObjAsCat.{uJ} := by
  apply _root_.CategoryTheory.Functor.ext
  · intro X Y f
    rfl
  · intro X
    rfl

/-- Composition of morphisms maps to composition of morphisms in Cat. -/
theorem JudgmentLevel.Hom.toCatHom_comp.{uJ} : {j₁ j₂ j₃ : JudgmentLevel} →
    (f : JudgmentLevel.Hom j₁ j₂) → (g : JudgmentLevel.Hom j₂ j₃) →
    JudgmentLevel.Hom.toCatHom.{uJ} (JudgmentLevel.Hom.comp f g) =
    JudgmentLevel.Hom.toCatHom.{uJ} f ≫ JudgmentLevel.Hom.toCatHom.{uJ} g
  | .obj, .obj, .obj, .id .obj, .id .obj => by
      apply Cat.Hom.ext
      simp only [Hom.comp, Hom.toCatHom, Functor.toCatHom_toFunctor,
        Cat.Hom.comp_toFunctor]
      exact (Functor.id_comp _).symm
  | .quiv, .quiv, .quiv, .id .quiv, .id .quiv => by
      apply Cat.Hom.ext
      simp only [Hom.comp, Hom.toCatHom, Functor.toCatHom_toFunctor,
        Cat.Hom.comp_toFunctor]
      exact (Functor.id_comp _).symm
  | .quiv, .quiv, .obj, .id .quiv, .quivToObj => by
      apply Cat.Hom.ext
      simp only [Hom.comp, Hom.toCatHom, Functor.toCatHom_toFunctor,
        Cat.Hom.comp_toFunctor]
      exact (Functor.id_comp _).symm
  | .quiv, .obj, .obj, .quivToObj, .id .obj => by
      apply Cat.Hom.ext
      simp only [Hom.comp, Hom.toCatHom, Functor.toCatHom_toFunctor,
        Cat.Hom.comp_toFunctor]
      exact (Functor.comp_id _).symm
  | .cat, .cat, .cat, .id .cat, .id .cat => by
      apply Cat.Hom.ext
      simp only [Hom.comp, Hom.toCatHom, Functor.toCatHom_toFunctor,
        Cat.Hom.comp_toFunctor]
      exact (Functor.id_comp _).symm
  | .cat, .cat, .quiv, .id .cat, .catToQuiv => by
      apply Cat.Hom.ext
      simp only [Hom.comp, Hom.toCatHom, Functor.toCatHom_toFunctor,
        Cat.Hom.comp_toFunctor]
      exact (Functor.id_comp _).symm
  | .cat, .cat, .obj, .id .cat, .catToObj => by
      apply Cat.Hom.ext
      simp only [Hom.comp, Hom.toCatHom, Functor.toCatHom_toFunctor,
        Cat.Hom.comp_toFunctor]
      exact (Functor.id_comp _).symm
  | .cat, .quiv, .quiv, .catToQuiv, .id .quiv => by
      apply Cat.Hom.ext
      simp only [Hom.comp, Hom.toCatHom, Functor.toCatHom_toFunctor,
        Cat.Hom.comp_toFunctor]
      exact (Functor.comp_id _).symm
  | .cat, .quiv, .obj, .catToQuiv, .quivToObj => by
      apply Cat.Hom.ext
      simp only [Hom.comp, Hom.toCatHom, Functor.toCatHom_toFunctor,
        Cat.Hom.comp_toFunctor]
      exact JudgmentLevel.forgetCatToObj_eq_comp.{uJ}
  | .cat, .obj, .obj, .catToObj, .id .obj => by
      apply Cat.Hom.ext
      simp only [Hom.comp, Hom.toCatHom, Functor.toCatHom_toFunctor,
        Cat.Hom.comp_toFunctor]
      exact (Functor.comp_id _).symm

/-- The judgment universe functor from the judgment category to Cat. -/
def JudgmentUniverse.{uJ} : JudgmentLevel ⥤ Cat.{uJ + 1, uJ + 2} where
  obj := JudgmentLevel.toCat.{uJ}
  map := JudgmentLevel.Hom.toCatHom.{uJ}
  map_id := JudgmentLevel.Hom.toCatHom_id.{uJ}
  map_comp := JudgmentLevel.Hom.toCatHom_comp.{uJ}

/-! ## Sections of JudgmentUniverse

A section of JudgmentUniverse assigns compatible structures at each level.
The compatibility conditions ensure that forgetful functors relate the data
at different levels. Since each level adds structure to the previous one,
a section is determined by its value at the most refined level (cat).
-/

/-- A section of the judgment universe assigns compatible structures at each
    level. The compatibility is expressed via the forgetful functors. -/
structure JudgmentSection.{uJ} where
  /-- Data at the obj level (a type). -/
  objData : Obj.ObjCopr.{uJ + 2}
  /-- Data at the quiv level (a quiver). -/
  quivData : Obj.ObjMorCopr.{uJ + 1, uJ + 1}
  /-- Data at the cat level (a category structure). -/
  catData : Obj.CatJudgCopr.{uJ + 1, uJ + 1, uJ + 1, uJ + 1}
  /-- The quiver projects to the object type. -/
  quiv_to_obj : Cat.forgetObjMorToObj.{uJ, uJ}.obj quivData = objData
  /-- The category projects to the quiver. -/
  cat_to_quiv : Cat.forgetCatJudgToObjMor.{uJ, uJ, uJ, uJ}.obj catData = quivData

/-- Construct a JudgmentSection from a CatJudgCopr object. The forgetful
    functors determine the data at lower levels. -/
def JudgmentSection.ofCatJudgCopr.{uJ}
    (c : Obj.CatJudgCopr.{uJ + 1, uJ + 1, uJ + 1, uJ + 1}) :
    JudgmentSection.{uJ} where
  objData := Cat.forgetCatJudgToObj.{uJ, uJ, uJ, uJ}.obj c
  quivData := Cat.forgetCatJudgToObjMor.{uJ, uJ, uJ, uJ}.obj c
  catData := c
  quiv_to_obj := rfl
  cat_to_quiv := rfl

/-- Extract the CatJudgCopr from a JudgmentSection. -/
def JudgmentSection.toCatJudgCopr.{uJ} (s : JudgmentSection.{uJ}) :
    Obj.CatJudgCopr.{uJ + 1, uJ + 1, uJ + 1, uJ + 1} :=
  s.catData

/-- Round-trip: constructing from CatJudgCopr and extracting gives identity. -/
theorem JudgmentSection.toCatJudgCopr_ofCatJudgCopr.{uJ}
    (c : Obj.CatJudgCopr.{uJ + 1, uJ + 1, uJ + 1, uJ + 1}) :
    (JudgmentSection.ofCatJudgCopr.{uJ} c).toCatJudgCopr = c := rfl

/-- Round-trip: extracting to CatJudgCopr and constructing gives original
    section (up to equality proofs). -/
theorem JudgmentSection.ofCatJudgCopr_toCatJudgCopr.{uJ}
    (s : JudgmentSection.{uJ}) :
    JudgmentSection.ofCatJudgCopr.{uJ} s.toCatJudgCopr = s := by
  cases s with
  | mk objData quivData catData quiv_to_obj cat_to_quiv =>
    simp only [ofCatJudgCopr, toCatJudgCopr]
    congr 1
    -- Show forgetCatJudgToObj.obj catData = objData
    simp only [Cat.forgetCatJudgToObj]
    rw [← quiv_to_obj, ← cat_to_quiv]
    rfl

/-- The equivalence between JudgmentSection and CatJudgCopr.
    This formalizes the notion that sections are determined by the
    most refined level. -/
def JudgmentSection.equivCatJudgCopr.{uJ} :
    JudgmentSection.{uJ} ≃
    Obj.CatJudgCopr.{uJ + 1, uJ + 1, uJ + 1, uJ + 1} where
  toFun := JudgmentSection.toCatJudgCopr.{uJ}
  invFun := JudgmentSection.ofCatJudgCopr.{uJ}
  left_inv := JudgmentSection.ofCatJudgCopr_toCatJudgCopr.{uJ}
  right_inv := JudgmentSection.toCatJudgCopr_ofCatJudgCopr.{uJ}

/-! ## Internal Category Structure

To express [J, Type] as an internal category in [J, Type (u+1)], we define:
- An object copresheaf: types at each judgment level
- A morphism copresheaf: morphisms between structures at each level
- Source, target, identity, and composition operations

For the obj level, morphisms are `Mor.ObjMap` (plain functions).
For quiv level, morphisms are `Mor.ObjMorCoprMap` (quiver homomorphisms).
For cat level, morphisms are `Mor.CatJudgNatTrans` (category natural transformations).
-/

/-- The morphism type at the obj level (plain functions). -/
def JudgmentLevel.ObjMorBundle.{uJ} :=
  Σ (X Y : Obj.ObjCopr.{uJ + 2}), Mor.ObjMap.{uJ + 2, uJ + 2} X Y

/-- The morphism type at the quiv level (quiver homomorphisms). -/
def JudgmentLevel.QuivMorBundle.{uJ} :=
  Σ (X Y : Obj.ObjMorCopr.{uJ + 1, uJ + 1}),
    Mor.ObjMorCoprMap.{uJ + 1, uJ + 1, uJ + 1, uJ + 1} X Y

/-- The morphism type at the cat level (category natural transformations). -/
def JudgmentLevel.CatMorBundle.{uJ} :=
  Σ (X Y : Obj.CatJudgCopr.{uJ + 1, uJ + 1, uJ + 1, uJ + 1}),
    Mor.CatJudgNatTrans.{uJ + 1, uJ + 1, uJ + 1, uJ + 1,
                         uJ + 1, uJ + 1, uJ + 1, uJ + 1} X Y

/-- Source of an obj-level morphism bundle. -/
def JudgmentLevel.ObjMorBundle.src.{uJ} (m : ObjMorBundle.{uJ}) :
    Obj.ObjCopr.{uJ + 2} := m.1

/-- Target of an obj-level morphism bundle. -/
def JudgmentLevel.ObjMorBundle.tgt.{uJ} (m : ObjMorBundle.{uJ}) :
    Obj.ObjCopr.{uJ + 2} := m.2.1

/-- Source of a quiv-level morphism bundle. -/
def JudgmentLevel.QuivMorBundle.src.{uJ} (m : QuivMorBundle.{uJ}) :
    Obj.ObjMorCopr.{uJ + 1, uJ + 1} := m.1

/-- Target of a quiv-level morphism bundle. -/
def JudgmentLevel.QuivMorBundle.tgt.{uJ} (m : QuivMorBundle.{uJ}) :
    Obj.ObjMorCopr.{uJ + 1, uJ + 1} := m.2.1

/-- Source of a cat-level morphism bundle. -/
def JudgmentLevel.CatMorBundle.src.{uJ} (m : CatMorBundle.{uJ}) :
    Obj.CatJudgCopr.{uJ + 1, uJ + 1, uJ + 1, uJ + 1} := m.1

/-- Target of a cat-level morphism bundle. -/
def JudgmentLevel.CatMorBundle.tgt.{uJ} (m : CatMorBundle.{uJ}) :
    Obj.CatJudgCopr.{uJ + 1, uJ + 1, uJ + 1, uJ + 1} := m.2.1

/-- Identity at obj level. -/
def JudgmentLevel.ObjMorBundle.identity.{uJ} (X : Obj.ObjCopr.{uJ + 2}) :
    ObjMorBundle.{uJ} := ⟨X, X, Cat.ObjMap.id X⟩

/-- Identity at quiv level. -/
def JudgmentLevel.QuivMorBundle.identity.{uJ}
    (X : Obj.ObjMorCopr.{uJ + 1, uJ + 1}) : QuivMorBundle.{uJ} :=
  ⟨X, X, Cat.ObjMorCoprMap.id X⟩

/-- Identity at cat level. -/
def JudgmentLevel.CatMorBundle.identity.{uJ}
    (X : Obj.CatJudgCopr.{uJ + 1, uJ + 1, uJ + 1, uJ + 1}) : CatMorBundle.{uJ} :=
  ⟨X, X, Cat.CatJudgNatTrans.id X⟩

/-- Composition at obj level. -/
def JudgmentLevel.ObjMorBundle.comp.{uJ}
    (f g : ObjMorBundle.{uJ}) (h : f.tgt = g.src) : ObjMorBundle.{uJ} :=
  let g' : Mor.ObjMap.{uJ + 2, uJ + 2} f.tgt g.tgt := by
    rw [h]; exact g.2.2
  ⟨f.src, g.tgt, Cat.ObjMap.comp f.2.2 g'⟩

/-- Composition at quiv level. -/
def JudgmentLevel.QuivMorBundle.comp.{uJ}
    (f g : QuivMorBundle.{uJ}) (h : f.tgt = g.src) : QuivMorBundle.{uJ} :=
  let g' : Mor.ObjMorCoprMap.{uJ + 1, uJ + 1, uJ + 1, uJ + 1} f.tgt g.tgt := by
    rw [h]; exact g.2.2
  ⟨f.src, g.tgt, Cat.ObjMorCoprMap.comp f.2.2 g'⟩

/-- Composition at cat level. -/
def JudgmentLevel.CatMorBundle.comp.{uJ}
    (f g : CatMorBundle.{uJ}) (h : f.tgt = g.src) : CatMorBundle.{uJ} :=
  let g' : Mor.CatJudgNatTrans.{uJ + 1, uJ + 1, uJ + 1, uJ + 1,
                                uJ + 1, uJ + 1, uJ + 1, uJ + 1} f.tgt g.tgt := by
    rw [h]; exact g.2.2
  ⟨f.src, g.tgt, Cat.CatJudgNatTrans.comp f.2.2 g'⟩

/-! ### Identity Laws for Morphism Bundles -/

/-- Left identity for obj-level composition. -/
theorem JudgmentLevel.ObjMorBundle.id_comp.{uJ}
    (f : ObjMorBundle.{uJ}) :
    ObjMorBundle.comp (ObjMorBundle.identity f.src) f rfl = f := rfl

/-- Right identity for obj-level composition. -/
theorem JudgmentLevel.ObjMorBundle.comp_id.{uJ}
    (f : ObjMorBundle.{uJ}) :
    ObjMorBundle.comp f (ObjMorBundle.identity f.tgt) rfl = f := rfl

/-- Left identity for quiv-level composition. -/
theorem JudgmentLevel.QuivMorBundle.id_comp.{uJ}
    (f : QuivMorBundle.{uJ}) :
    QuivMorBundle.comp (QuivMorBundle.identity f.src) f rfl = f := rfl

/-- Right identity for quiv-level composition. -/
theorem JudgmentLevel.QuivMorBundle.comp_id.{uJ}
    (f : QuivMorBundle.{uJ}) :
    QuivMorBundle.comp f (QuivMorBundle.identity f.tgt) rfl = f := rfl

/-- Left identity for cat-level composition. -/
theorem JudgmentLevel.CatMorBundle.id_comp.{uJ}
    (f : CatMorBundle.{uJ}) :
    CatMorBundle.comp (CatMorBundle.identity f.src) f rfl = f := rfl

/-- Right identity for cat-level composition. -/
theorem JudgmentLevel.CatMorBundle.comp_id.{uJ}
    (f : CatMorBundle.{uJ}) :
    CatMorBundle.comp f (CatMorBundle.identity f.tgt) rfl = f := rfl

/-! ### Associativity Laws for Morphism Bundles -/

/-- Associativity for obj-level composition. -/
theorem JudgmentLevel.ObjMorBundle.comp_assoc.{uJ}
    (f g h : ObjMorBundle.{uJ})
    (hfg : f.tgt = g.src) (hgh : g.tgt = h.src) :
    ObjMorBundle.comp (ObjMorBundle.comp f g hfg) h hgh =
    ObjMorBundle.comp f (ObjMorBundle.comp g h hgh) hfg := by
  obtain ⟨srcF, tgtF, morF⟩ := f
  obtain ⟨srcG, tgtG, morG⟩ := g
  obtain ⟨srcH, tgtH, morH⟩ := h
  simp only [ObjMorBundle.tgt, ObjMorBundle.src] at hfg hgh
  subst hfg hgh
  rfl

/-- Associativity for quiv-level composition. -/
theorem JudgmentLevel.QuivMorBundle.comp_assoc.{uJ}
    (f g h : QuivMorBundle.{uJ})
    (hfg : f.tgt = g.src) (hgh : g.tgt = h.src) :
    QuivMorBundle.comp (QuivMorBundle.comp f g hfg) h hgh =
    QuivMorBundle.comp f (QuivMorBundle.comp g h hgh) hfg := by
  obtain ⟨srcF, tgtF, morF⟩ := f
  obtain ⟨srcG, tgtG, morG⟩ := g
  obtain ⟨srcH, tgtH, morH⟩ := h
  simp only [QuivMorBundle.tgt, QuivMorBundle.src] at hfg hgh
  subst hfg hgh
  rfl

/-- Associativity for cat-level composition. -/
theorem JudgmentLevel.CatMorBundle.comp_assoc.{uJ}
    (f g h : CatMorBundle.{uJ})
    (hfg : f.tgt = g.src) (hgh : g.tgt = h.src) :
    CatMorBundle.comp (CatMorBundle.comp f g hfg) h hgh =
    CatMorBundle.comp f (CatMorBundle.comp g h hgh) hfg := by
  obtain ⟨srcF, tgtF, morF⟩ := f
  obtain ⟨srcG, tgtG, morG⟩ := g
  obtain ⟨srcH, tgtH, morH⟩ := h
  simp only [CatMorBundle.tgt, CatMorBundle.src] at hfg hgh
  subst hfg hgh
  rfl

/-! ### Forgetful Maps Between Morphism Bundles -/

/-- Forget from quiv-level bundle to obj-level bundle. -/
def JudgmentLevel.forgetQuivBundleToObjBundle.{uJ}
    (m : QuivMorBundle.{uJ}) : ObjMorBundle.{uJ} :=
  ⟨Cat.forgetObjMorToObj.{uJ, uJ}.obj m.src,
   Cat.forgetObjMorToObj.{uJ, uJ}.obj m.tgt,
   Cat.forgetObjMorToObj.{uJ, uJ}.map m.2.2⟩

/-- Forget from cat-level bundle to quiv-level bundle. -/
def JudgmentLevel.forgetCatBundleToQuivBundle.{uJ}
    (m : CatMorBundle.{uJ}) : QuivMorBundle.{uJ} :=
  ⟨Cat.forgetCatJudgToObjMor.{uJ, uJ, uJ, uJ}.obj m.src,
   Cat.forgetCatJudgToObjMor.{uJ, uJ, uJ, uJ}.obj m.tgt,
   Cat.forgetCatJudgToObjMor.{uJ, uJ, uJ, uJ}.map m.2.2⟩

/-- Forget from cat-level bundle to obj-level bundle. -/
def JudgmentLevel.forgetCatBundleToObjBundle.{uJ}
    (m : CatMorBundle.{uJ}) : ObjMorBundle.{uJ} :=
  ⟨Cat.forgetCatJudgToObj.{uJ, uJ, uJ, uJ}.obj m.src,
   Cat.forgetCatJudgToObj.{uJ, uJ, uJ, uJ}.obj m.tgt,
   Cat.forgetCatJudgToObj.{uJ, uJ, uJ, uJ}.map m.2.2⟩

/-- The composition of forgetful maps equals the direct forgetful map. -/
theorem JudgmentLevel.forgetCatBundleToObjBundle_eq_comp.{uJ}
    (m : CatMorBundle.{uJ}) :
    forgetCatBundleToObjBundle m =
    forgetQuivBundleToObjBundle (forgetCatBundleToQuivBundle m) := rfl

/-! ### Morphism Bundle Copresheaf

The morphism bundle copresheaf assigns to each judgment level the type
of morphism bundles at that level. Morphisms in the judgment category
induce forgetful maps between bundle types.
-/

/-- Map each judgment level to its morphism bundle type. -/
def JudgmentLevel.toMorBundleType.{uJ} : JudgmentLevel → Type (uJ + 2)
  | .obj => ObjMorBundle.{uJ}
  | .quiv => QuivMorBundle.{uJ}
  | .cat => CatMorBundle.{uJ}

/-- The functorial action on morphisms: forgetful maps between bundle types. -/
def JudgmentLevel.Hom.toMorBundleMap.{uJ} : {j₁ j₂ : JudgmentLevel} →
    JudgmentLevel.Hom j₁ j₂ →
    (JudgmentLevel.toMorBundleType.{uJ} j₁ → JudgmentLevel.toMorBundleType.{uJ} j₂)
  | .obj, .obj, .id .obj => _root_.id
  | .quiv, .quiv, .id .quiv => _root_.id
  | .cat, .cat, .id .cat => _root_.id
  | .quiv, .obj, .quivToObj => forgetQuivBundleToObjBundle
  | .cat, .quiv, .catToQuiv => forgetCatBundleToQuivBundle
  | .cat, .obj, .catToObj => forgetCatBundleToObjBundle

/-- Identity morphisms map to identity functions. -/
theorem JudgmentLevel.Hom.toMorBundleMap_id.{uJ} (j : JudgmentLevel) :
    JudgmentLevel.Hom.toMorBundleMap.{uJ} (.id j) = _root_.id := by
  cases j <;> rfl

/-- Composition of morphisms maps to composition of forgetful maps. -/
theorem JudgmentLevel.Hom.toMorBundleMap_comp.{uJ} : {j₁ j₂ j₃ : JudgmentLevel} →
    (f : JudgmentLevel.Hom j₁ j₂) → (g : JudgmentLevel.Hom j₂ j₃) →
    JudgmentLevel.Hom.toMorBundleMap.{uJ} (JudgmentLevel.Hom.comp f g) =
    JudgmentLevel.Hom.toMorBundleMap.{uJ} g ∘ JudgmentLevel.Hom.toMorBundleMap.{uJ} f
  | .obj, .obj, .obj, .id .obj, .id .obj => rfl
  | .quiv, .quiv, .quiv, .id .quiv, .id .quiv => rfl
  | .quiv, .quiv, .obj, .id .quiv, .quivToObj => rfl
  | .quiv, .obj, .obj, .quivToObj, .id .obj => rfl
  | .cat, .cat, .cat, .id .cat, .id .cat => rfl
  | .cat, .cat, .quiv, .id .cat, .catToQuiv => rfl
  | .cat, .cat, .obj, .id .cat, .catToObj => rfl
  | .cat, .quiv, .quiv, .catToQuiv, .id .quiv => rfl
  | .cat, .quiv, .obj, .catToQuiv, .quivToObj => rfl
  | .cat, .obj, .obj, .catToObj, .id .obj => rfl

/-- The morphism bundle copresheaf as a functor from JudgmentLevel to Type.
    This assigns to each judgment level its morphism bundle type. -/
def MorphismBundleCopresheaf.{uJ} : JudgmentLevel ⥤ Type (uJ + 2) where
  obj := JudgmentLevel.toMorBundleType.{uJ}
  map := JudgmentLevel.Hom.toMorBundleMap.{uJ}
  map_id := JudgmentLevel.Hom.toMorBundleMap_id.{uJ}
  map_comp := JudgmentLevel.Hom.toMorBundleMap_comp.{uJ}

/-! ### Source and Target Natural Transformations

For the internal category structure, we need source and target maps that
are natural with respect to the forgetful functors.
-/

/-- Source projection for each level's bundle type. -/
def JudgmentLevel.sourceProj.{uJ} :
    (j : JudgmentLevel) → JudgmentLevel.toMorBundleType.{uJ} j →
      JudgmentLevel.toCat.{uJ} j
  | .obj => ObjMorBundle.src
  | .quiv => QuivMorBundle.src
  | .cat => CatMorBundle.src

/-- Target projection for each level's bundle type. -/
def JudgmentLevel.targetProj.{uJ} :
    (j : JudgmentLevel) → JudgmentLevel.toMorBundleType.{uJ} j →
      JudgmentLevel.toCat.{uJ} j
  | .obj => ObjMorBundle.tgt
  | .quiv => QuivMorBundle.tgt
  | .cat => CatMorBundle.tgt

/-! ## Category of Judgment Sections

Morphisms between judgment sections are morphisms at the cat level.
Since lower levels are uniquely determined by the cat level, a morphism
at the cat level determines compatible morphisms at all lower levels,
so we define `JudgmentSectionHom` as `CatJudgNatTrans` on the cat data.
-/

/-- Morphisms between judgment sections: natural transformations at the
    cat level. Since lower levels are determined by the cat level, this
    is the complete morphism data. -/
def JudgmentSectionHom.{uJ} (s t : JudgmentSection.{uJ}) : Type (uJ + 1) :=
  Mor.CatJudgNatTrans.{uJ + 1, uJ + 1, uJ + 1, uJ + 1,
                       uJ + 1, uJ + 1, uJ + 1, uJ + 1} s.catData t.catData

/-- Identity morphism for judgment sections. -/
def JudgmentSectionHom.id.{uJ} (s : JudgmentSection.{uJ}) :
    JudgmentSectionHom s s :=
  Cat.CatJudgNatTrans.id s.catData

/-- Composition of judgment section morphisms. -/
def JudgmentSectionHom.comp.{uJ} {s t u : JudgmentSection.{uJ}}
    (f : JudgmentSectionHom s t) (g : JudgmentSectionHom t u) :
    JudgmentSectionHom s u :=
  Cat.CatJudgNatTrans.comp f g

/-- Left identity law for judgment section morphisms. -/
theorem JudgmentSectionHom.id_comp.{uJ} {s t : JudgmentSection.{uJ}}
    (f : JudgmentSectionHom s t) :
    JudgmentSectionHom.comp (JudgmentSectionHom.id s) f = f :=
  Cat.CatJudgNatTrans.id_comp f

/-- Right identity law for judgment section morphisms. -/
theorem JudgmentSectionHom.comp_id.{uJ} {s t : JudgmentSection.{uJ}}
    (f : JudgmentSectionHom s t) :
    JudgmentSectionHom.comp f (JudgmentSectionHom.id t) = f :=
  Cat.CatJudgNatTrans.comp_id f

/-- Associativity of judgment section morphism composition. -/
theorem JudgmentSectionHom.comp_assoc.{uJ}
    {s t u v : JudgmentSection.{uJ}}
    (f : JudgmentSectionHom s t) (g : JudgmentSectionHom t u)
    (h : JudgmentSectionHom u v) :
    JudgmentSectionHom.comp (JudgmentSectionHom.comp f g) h =
    JudgmentSectionHom.comp f (JudgmentSectionHom.comp g h) :=
  Cat.CatJudgNatTrans.comp_assoc f g h

/-- Category instance for JudgmentSection. This inherits the category
    structure from CatJudgCopr via the equivalence. -/
instance JudgmentSection.category.{uJ} :
    LargeCategory.{uJ + 1} (JudgmentSection.{uJ}) where
  Hom := JudgmentSectionHom
  id := JudgmentSectionHom.id
  comp := fun f g => JudgmentSectionHom.comp f g
  id_comp := JudgmentSectionHom.id_comp
  comp_id := JudgmentSectionHom.comp_id
  assoc := JudgmentSectionHom.comp_assoc

/-! ## Categorical Equivalence with CatJudgCopr

The type equivalence `JudgmentSection.equivCatJudgCopr` extends to a
categorical equivalence. Since `JudgmentSectionHom` is defined as
`CatJudgNatTrans` on the `catData` fields, the functors are nearly
definitional.
-/

/-- The functor from JudgmentSection to CatJudgCopr.
    On objects: extracts the cat-level data.
    On morphisms: identity (same type by definition). -/
def JudgmentSection.toCatJudgCoprFunctor.{uJ} :
    JudgmentSection.{uJ} ⥤ Obj.CatJudgCopr.{uJ + 1, uJ + 1, uJ + 1, uJ + 1} where
  obj := JudgmentSection.toCatJudgCopr
  map := fun f => f
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- The functor from CatJudgCopr to JudgmentSection.
    On objects: constructs a section from cat-level data.
    On morphisms: identity (since (ofCatJudgCopr c).catData = c). -/
def JudgmentSection.ofCatJudgCoprFunctor.{uJ} :
    Obj.CatJudgCopr.{uJ + 1, uJ + 1, uJ + 1, uJ + 1} ⥤ JudgmentSection.{uJ} where
  obj := JudgmentSection.ofCatJudgCopr
  map := fun f => f
  map_id := fun _ => rfl
  map_comp := fun _ _ => rfl

/-- The composition `toCatJudgCoprFunctor ⋙ ofCatJudgCoprFunctor` is
    naturally isomorphic to the identity on JudgmentSection. -/
def JudgmentSection.unitIso.{uJ} :
    𝟭 JudgmentSection.{uJ} ≅
    toCatJudgCoprFunctor.{uJ} ⋙ ofCatJudgCoprFunctor.{uJ} :=
  NatIso.ofComponents
    (fun s => eqToIso (ofCatJudgCopr_toCatJudgCopr s).symm)
    (fun {s t} f => by
      simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map,
        Functor.comp_map, toCatJudgCoprFunctor, ofCatJudgCoprFunctor]
      simp only [eqToIso]
      rfl)

/-- The composition `ofCatJudgCoprFunctor ⋙ toCatJudgCoprFunctor` is
    naturally isomorphic to the identity on CatJudgCopr. -/
def JudgmentSection.counitIso.{uJ} :
    ofCatJudgCoprFunctor.{uJ} ⋙ toCatJudgCoprFunctor.{uJ} ≅
    𝟭 (Obj.CatJudgCopr.{uJ + 1, uJ + 1, uJ + 1, uJ + 1}) :=
  NatIso.ofComponents
    (fun c => eqToIso (toCatJudgCopr_ofCatJudgCopr c))
    (fun {c d} f => by
      simp only [Functor.comp_obj, Functor.id_obj, Functor.comp_map,
        Functor.id_map, ofCatJudgCoprFunctor, toCatJudgCoprFunctor]
      simp only [eqToIso]
      rfl)

/-- The categorical equivalence between JudgmentSection and CatJudgCopr.
    This lifts the type equivalence `equivCatJudgCopr` to categories. -/
def JudgmentSection.catEquiv.{uJ} :
    JudgmentSection.{uJ} ≌
    Obj.CatJudgCopr.{uJ + 1, uJ + 1, uJ + 1, uJ + 1} where
  functor := toCatJudgCoprFunctor
  inverse := ofCatJudgCoprFunctor
  unitIso := unitIso
  counitIso := counitIso
  functor_unitIso_comp := fun s => by
    simp only [unitIso, counitIso, NatIso.ofComponents_hom_app,
      toCatJudgCoprFunctor, eqToIso]
    simp only [Functor.comp_obj, ofCatJudgCoprFunctor, toCatJudgCopr,
      ofCatJudgCopr]
    rfl

/-! ## Connection to Currying and the CatJudgment Adjunction

The isomorphism [A × B, C] ≅ [A, [B, C]] (currying in Cat) connects the
self-representation to an adjunction perspective:

- A copresheaf F : J → Type corresponds to an "uncurried" function
  F' : J × (data source) → Type
- For the CatJudgment adjunction, the right adjoint U : Cat → [J, Type]
  can be viewed as U' : Cat × J → Type where U'(C, j) = j-level data of C

JudgmentSection captures this: a section assigns compatible data at each
judgment level, determined by the cat-level data (the full specification).
-/

/-- Evaluate a JudgmentSection at a given judgment level to get the
    corresponding object in that level's category. This is the uncurried
    view of the section as a function J × Section → Object. -/
def JudgmentSection.evalAt.{uJ} (s : JudgmentSection.{uJ}) :
    (j : JudgmentLevel) → JudgmentLevel.toCat.{uJ} j
  | .obj => s.objData
  | .quiv => s.quivData
  | .cat => s.catData

/-- Evaluation respects the forgetful structure: evaluating at obj equals
    applying the forgetful functor to the quiv-level evaluation. -/
theorem JudgmentSection.evalAt_quivToObj.{uJ} (s : JudgmentSection.{uJ}) :
    Cat.forgetObjMorToObj.{uJ, uJ}.obj (s.evalAt .quiv) = s.evalAt .obj :=
  s.quiv_to_obj

/-- Evaluation respects the forgetful structure: evaluating at quiv equals
    applying the forgetful functor to the cat-level evaluation. -/
theorem JudgmentSection.evalAt_catToQuiv.{uJ} (s : JudgmentSection.{uJ}) :
    Cat.forgetCatJudgToObjMor.{uJ, uJ, uJ, uJ}.obj (s.evalAt .cat) =
    s.evalAt .quiv :=
  s.cat_to_quiv

/-- Evaluation respects the forgetful structure: evaluating at obj equals
    applying the composed forgetful functor to the cat-level evaluation. -/
theorem JudgmentSection.evalAt_catToObj.{uJ} (s : JudgmentSection.{uJ}) :
    Cat.forgetCatJudgToObj.{uJ, uJ, uJ, uJ}.obj (s.evalAt .cat) =
    s.evalAt .obj := by
  simp only [evalAt, Cat.forgetCatJudgToObj]
  rw [← s.quiv_to_obj, ← s.cat_to_quiv]
  rfl

/-- For any JudgmentLevel morphism, evaluating at the source and applying
    the forgetful functor equals evaluating at the target. This is the
    naturality condition connecting the section to the uncurried view. -/
theorem JudgmentSection.evalAt_natural.{uJ} (s : JudgmentSection.{uJ})
    {j₁ j₂ : JudgmentLevel} (f : JudgmentLevel.Hom j₁ j₂) :
    (JudgmentLevel.Hom.toCatHom.{uJ} f).toFunctor.obj (s.evalAt j₁) = s.evalAt j₂ := by
  match j₁, j₂, f with
  | .obj, .obj, .id .obj => rfl
  | .quiv, .quiv, .id .quiv => rfl
  | .cat, .cat, .id .cat => rfl
  | .quiv, .obj, .quivToObj => exact s.evalAt_quivToObj
  | .cat, .quiv, .catToQuiv => exact s.evalAt_catToQuiv
  | .cat, .obj, .catToObj => exact s.evalAt_catToObj

/-! ## Product Category and Uncurried Evaluation

The currying isomorphism `[A × B, C] ≅ [A, [B, C]]` from
`CategoryTheory.Functor.currying` connects our structures:

- A functor `F : Cat → [JudgmentLevel, Type]` (sending a category to its
  judgment copresheaf) corresponds to an uncurried functor
  `F' : Cat × JudgmentLevel → Type`

- The uncurried evaluation `F'(C, j) = F(C)(j)` extracts the j-level
  data from category C

The product `Cat × JudgmentLevel` is a category via
`CategoryTheory.prod`, and evaluation at a judgment level provides
the uncurried perspective.

The type of pairs (CatJudgCopr, JudgmentLevel) with evaluation gives
the uncurried data type at each point.
-/

/-- Extract the object type from a judgment section. This is the
    "value" at the obj level. -/
def JudgmentSection.objType.{uJ} (s : JudgmentSection.{uJ}) : Type (uJ + 1) :=
  s.objData

/-- Extract the morphism type from a judgment section. This is
    derived from the quiv level data. -/
def JudgmentSection.morType.{uJ} (s : JudgmentSection.{uJ}) : Type (uJ + 1) :=
  s.quivData.mor

/-- The product of CatJudgCopr with JudgmentLevel, as a base for
    the uncurried functor perspective. -/
abbrev JudgmentProductType.{uJ} : Type (uJ + 2) :=
  Obj.CatJudgCopr.{uJ+1, uJ+1, uJ+1, uJ+1} × JudgmentLevel

/-! ### Connection to the Currying Equivalence

Mathlib provides `CategoryTheory.Functor.currying`:

```
currying : Functor C (Functor D E) ≌ Functor (Prod C D) E
```

For our setting with `C = Cat`, `D = JudgmentLevel`, `E = Type`:
- A right adjoint `U : Cat → [JudgmentLevel, Type]` sending each category
  to its judgment copresheaf
- Uncurries to `U' : Cat × JudgmentLevel → Type` via
  `Functor.uncurry.obj U`
- The evaluation `U'(C, j)` gives the j-level data of category C

The `JudgmentSection.evalAt` function captures this uncurried evaluation
when restricted to sections (which are equivalent to CatJudgCopr objects).

The naturality theorem `evalAt_natural` shows that evaluation respects
the morphisms in JudgmentLevel, which is the functoriality condition
for the uncurried functor in its second argument.
-/

/-- The category structure on JudgmentLevel paired with any category
    follows from the Mathlib product instance. This allows forming
    the product `C × JudgmentLevel` for any category C.

    Note: `CategoryTheory.prod` provides the category instance on
    `Prod C D` for any categories C and D. Since we have
    `Category JudgmentLevel` above, `Prod C JudgmentLevel` is
    automatically a category via this instance. -/
example (C : Type*) [Category C] : Category (C × JudgmentLevel) :=
  inferInstance

end PLang

end GebLean
