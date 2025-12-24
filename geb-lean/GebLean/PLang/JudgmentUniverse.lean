import GebLean.PLang.CatJudgment
import Mathlib.CategoryTheory.Category.Cat

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
  | .obj, .obj, .id .obj => 𝟭 _
  | .quiv, .quiv, .id .quiv => 𝟭 _
  | .cat, .cat, .id .cat => 𝟭 _
  | .quiv, .obj, .quivToObj => JudgmentLevel.forgetQuivToObjAsCat.{uJ}
  | .cat, .quiv, .catToQuiv => JudgmentLevel.forgetCatToQuivAsCat.{uJ}
  | .cat, .obj, .catToObj => JudgmentLevel.forgetCatToObjAsCat.{uJ}

/-- Identity morphisms map to identity functors. -/
theorem JudgmentLevel.Hom.toCatHom_id.{uJ} (j : JudgmentLevel) :
    JudgmentLevel.Hom.toCatHom.{uJ} (.id j) = 𝟭 (JudgmentLevel.toCat.{uJ} j) := by
  cases j <;> rfl

/-- The composition of forgetful functors catToQuiv and quivToObj equals catToObj. -/
theorem JudgmentLevel.forgetCatToObj_eq_comp.{uJ} :
    JudgmentLevel.forgetCatToObjAsCat.{uJ} =
    JudgmentLevel.forgetCatToQuivAsCat.{uJ} ⋙ JudgmentLevel.forgetQuivToObjAsCat.{uJ} := by
  apply Functor.ext
  · intro X Y f
    rfl
  · intro X
    rfl

/-- Composition of morphisms maps to composition of functors. -/
theorem JudgmentLevel.Hom.toCatHom_comp.{uJ} : {j₁ j₂ j₃ : JudgmentLevel} →
    (f : JudgmentLevel.Hom j₁ j₂) → (g : JudgmentLevel.Hom j₂ j₃) →
    JudgmentLevel.Hom.toCatHom.{uJ} (JudgmentLevel.Hom.comp f g) =
    JudgmentLevel.Hom.toCatHom.{uJ} f ⋙ JudgmentLevel.Hom.toCatHom.{uJ} g
  | .obj, .obj, .obj, .id .obj, .id .obj => by
      simp only [Hom.comp, Hom.toCatHom, Functor.id_comp]
  | .quiv, .quiv, .quiv, .id .quiv, .id .quiv => by
      simp only [Hom.comp, Hom.toCatHom, Functor.id_comp]
  | .quiv, .quiv, .obj, .id .quiv, .quivToObj => by
      simp only [Hom.comp, Hom.toCatHom, Functor.id_comp]
  | .quiv, .obj, .obj, .quivToObj, .id .obj => by
      simp only [Hom.comp, Hom.toCatHom, Functor.comp_id]
  | .cat, .cat, .cat, .id .cat, .id .cat => by
      simp only [Hom.comp, Hom.toCatHom, Functor.id_comp]
  | .cat, .cat, .quiv, .id .cat, .catToQuiv => by
      simp only [Hom.comp, Hom.toCatHom, Functor.id_comp]
  | .cat, .cat, .obj, .id .cat, .catToObj => by
      simp only [Hom.comp, Hom.toCatHom, Functor.id_comp]
  | .cat, .quiv, .quiv, .catToQuiv, .id .quiv => by
      simp only [Hom.comp, Hom.toCatHom, Functor.comp_id]
  | .cat, .quiv, .obj, .catToQuiv, .quivToObj =>
      JudgmentLevel.forgetCatToObj_eq_comp.{uJ}
  | .cat, .obj, .obj, .catToObj, .id .obj => by
      simp only [Hom.comp, Hom.toCatHom, Functor.comp_id]

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

end PLang

end GebLean
