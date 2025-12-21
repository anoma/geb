import Mathlib.CategoryTheory.Category.Basic
import Mathlib.CategoryTheory.Category.Cat
import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
import GebLean.Utilities.Families

/-!
# The free binary coequalizer completion

This module defines the free binary coequalizer completion of a category.

An object in this completion consists of two objects from the underlying
category C together with two parallel morphisms between them. This represents
a formal coequalizer diagram. Morphisms are commuting squares that respect
both parallel arrows.

When the underlying category C has coequalizer data (computable coequalizers),
the free coequalizer completion also has coequalizers, computed pointwise.

## References

* `docs/yoneda-coproduct-coequalizer-factorization.md` section 3
-/

namespace GebLean

open CategoryTheory
open CategoryTheory.Limits

universe v u w

variable (C : Type u) [Category.{v} C]

/-! ## Objects of the free coequalizer completion -/

section ParallelPairObj

/--
An object in the free coequalizer completion of C. This consists of two objects
`src` and `tgt` from C together with two parallel morphisms `left` and `right`
from `src` to `tgt`. The object represents the formal coequalizer of `left`
and `right`.
-/
@[ext]
structure ParallelPairObj where
  /-- The source object of the parallel pair. -/
  src : C
  /-- The target object of the parallel pair. -/
  tgt : C
  /-- The first (left) morphism of the parallel pair. -/
  left : src ⟶ tgt
  /-- The second (right) morphism of the parallel pair. -/
  right : src ⟶ tgt

variable {C}

/--
Construct an object of `ParallelPairObj C` from source, target, and two
parallel morphisms.
-/
@[simp]
def ppObjMk {src tgt : C} (left right : src ⟶ tgt) : ParallelPairObj C :=
  ⟨src, tgt, left, right⟩

/-- Extract the source object from a parallel pair. -/
@[simp]
def ppSrc (P : ParallelPairObj C) : C := P.src

/-- Extract the target object from a parallel pair. -/
@[simp]
def ppTgt (P : ParallelPairObj C) : C := P.tgt

/-- Extract the left morphism from a parallel pair. -/
@[simp]
def ppLeft (P : ParallelPairObj C) : ppSrc P ⟶ ppTgt P := P.left

/-- Extract the right morphism from a parallel pair. -/
@[simp]
def ppRight (P : ParallelPairObj C) : ppSrc P ⟶ ppTgt P := P.right

@[simp]
lemma ppObjMk_src {src tgt : C} (left right : src ⟶ tgt) :
    ppSrc (ppObjMk left right) = src := rfl

@[simp]
lemma ppObjMk_tgt {src tgt : C} (left right : src ⟶ tgt) :
    ppTgt (ppObjMk left right) = tgt := rfl

@[simp]
lemma ppObjMk_left {src tgt : C} (left right : src ⟶ tgt) :
    ppLeft (ppObjMk left right) = left := rfl

@[simp]
lemma ppObjMk_right {src tgt : C} (left right : src ⟶ tgt) :
    ppRight (ppObjMk left right) = right := rfl

/-- Reconstructing a parallel pair object from its components. -/
@[simp]
lemma ppObjMk_eta (P : ParallelPairObj C) :
    ppObjMk (ppLeft P) (ppRight P) = P := by
  cases P; rfl

end ParallelPairObj

/-! ## Morphisms in the free coequalizer completion -/

section ParallelPairHom

variable {C}

/--
A morphism in the free coequalizer completion from P to Q. This consists of
morphisms on sources and targets that make both squares commute:
```
  P.src --P.left--> P.tgt
    |                 |
  srcHom            tgtHom
    |                 |
    v                 v
  Q.src --Q.left--> Q.tgt
```
and similarly for the right morphisms.
-/
@[ext]
structure ParallelPairHom (P Q : ParallelPairObj C) where
  /-- The morphism between source objects. -/
  srcHom : P.src ⟶ Q.src
  /-- The morphism between target objects. -/
  tgtHom : P.tgt ⟶ Q.tgt
  /-- The left square commutes. -/
  left_comm : srcHom ≫ Q.left = P.left ≫ tgtHom
  /-- The right square commutes. -/
  right_comm : srcHom ≫ Q.right = P.right ≫ tgtHom

/--
Construct a morphism in the free coequalizer completion from component
morphisms and commutativity proofs.
-/
@[simp]
def ppHomMk {P Q : ParallelPairObj C}
    (srcHom : P.src ⟶ Q.src) (tgtHom : P.tgt ⟶ Q.tgt)
    (left_comm : srcHom ≫ Q.left = P.left ≫ tgtHom)
    (right_comm : srcHom ≫ Q.right = P.right ≫ tgtHom) :
    ParallelPairHom P Q :=
  ⟨srcHom, tgtHom, left_comm, right_comm⟩

/-- Extract the source morphism from a parallel pair morphism. -/
@[simp]
def ppSrcHom {P Q : ParallelPairObj C} (f : ParallelPairHom P Q) :
    P.src ⟶ Q.src :=
  f.srcHom

/-- Extract the target morphism from a parallel pair morphism. -/
@[simp]
def ppTgtHom {P Q : ParallelPairObj C} (f : ParallelPairHom P Q) :
    P.tgt ⟶ Q.tgt :=
  f.tgtHom

/-- The left square commutes. -/
lemma ppLeftComm {P Q : ParallelPairObj C} (f : ParallelPairHom P Q) :
    ppSrcHom f ≫ Q.left = P.left ≫ ppTgtHom f :=
  f.left_comm

/-- The right square commutes. -/
lemma ppRightComm {P Q : ParallelPairObj C} (f : ParallelPairHom P Q) :
    ppSrcHom f ≫ Q.right = P.right ≫ ppTgtHom f :=
  f.right_comm

@[simp]
lemma ppHomMk_srcHom {P Q : ParallelPairObj C}
    (srcHom : P.src ⟶ Q.src) (tgtHom : P.tgt ⟶ Q.tgt)
    (left_comm : srcHom ≫ Q.left = P.left ≫ tgtHom)
    (right_comm : srcHom ≫ Q.right = P.right ≫ tgtHom) :
    ppSrcHom (ppHomMk srcHom tgtHom left_comm right_comm) = srcHom := rfl

@[simp]
lemma ppHomMk_tgtHom {P Q : ParallelPairObj C}
    (srcHom : P.src ⟶ Q.src) (tgtHom : P.tgt ⟶ Q.tgt)
    (left_comm : srcHom ≫ Q.left = P.left ≫ tgtHom)
    (right_comm : srcHom ≫ Q.right = P.right ≫ tgtHom) :
    ppTgtHom (ppHomMk srcHom tgtHom left_comm right_comm) = tgtHom := rfl

/-- Reconstructing a morphism from its components. -/
@[simp]
lemma ppHomMk_eta {P Q : ParallelPairObj C} (f : ParallelPairHom P Q) :
    ppHomMk (ppSrcHom f) (ppTgtHom f) (ppLeftComm f) (ppRightComm f) = f := by
  cases f; rfl

end ParallelPairHom

/-! ## Category structure -/

section CategoryStructure

variable {C}

/-- The identity morphism in the free coequalizer completion. -/
@[simp]
def ppId (P : ParallelPairObj C) : ParallelPairHom P P :=
  ⟨𝟙 P.src, 𝟙 P.tgt, by simp, by simp⟩

/-- Composition of morphisms in the free coequalizer completion. -/
@[simp]
def ppComp {P Q R : ParallelPairObj C}
    (f : ParallelPairHom P Q) (g : ParallelPairHom Q R) :
    ParallelPairHom P R :=
  ⟨f.srcHom ≫ g.srcHom, f.tgtHom ≫ g.tgtHom,
   by rw [Category.assoc, g.left_comm, ← Category.assoc, f.left_comm,
          Category.assoc],
   by rw [Category.assoc, g.right_comm, ← Category.assoc, f.right_comm,
          Category.assoc]⟩

@[simp]
lemma ppId_srcHom (P : ParallelPairObj C) :
    ppSrcHom (ppId P) = 𝟙 P.src := rfl

@[simp]
lemma ppId_tgtHom (P : ParallelPairObj C) :
    ppTgtHom (ppId P) = 𝟙 P.tgt := rfl

@[simp]
lemma ppComp_srcHom {P Q R : ParallelPairObj C}
    (f : ParallelPairHom P Q) (g : ParallelPairHom Q R) :
    ppSrcHom (ppComp f g) = ppSrcHom f ≫ ppSrcHom g := rfl

@[simp]
lemma ppComp_tgtHom {P Q R : ParallelPairObj C}
    (f : ParallelPairHom P Q) (g : ParallelPairHom Q R) :
    ppTgtHom (ppComp f g) = ppTgtHom f ≫ ppTgtHom g := rfl

lemma ppComp_assoc {P Q R S : ParallelPairObj C}
    (f : ParallelPairHom P Q) (g : ParallelPairHom Q R)
    (h : ParallelPairHom R S) :
    ppComp (ppComp f g) h = ppComp f (ppComp g h) := by
  apply ParallelPairHom.ext <;> simp [Category.assoc]

lemma ppId_comp {P Q : ParallelPairObj C} (f : ParallelPairHom P Q) :
    ppComp (ppId P) f = f := by
  apply ParallelPairHom.ext <;> simp

lemma ppComp_id {P Q : ParallelPairObj C} (f : ParallelPairHom P Q) :
    ppComp f (ppId Q) = f := by
  apply ParallelPairHom.ext <;> simp

/-- The category instance for `ParallelPairObj C`. -/
instance ppCategory : Category (ParallelPairObj C) where
  Hom := ParallelPairHom
  id := ppId
  comp := ppComp
  id_comp := ppId_comp
  comp_id := ppComp_id
  assoc := ppComp_assoc

@[simp]
lemma ppHom_id_eq (P : ParallelPairObj C) : 𝟙 P = ppId P := rfl

@[simp]
lemma ppHom_comp_eq {P Q R : ParallelPairObj C}
    (f : P ⟶ Q) (g : Q ⟶ R) : f ≫ g = ppComp f g := rfl

end CategoryStructure


/-! ## Embedding functor -/

section Embedding

variable {C}

/--
The embedding of an object from C into the free coequalizer completion.
An object c is embedded as the trivial parallel pair (c, c, id, id).
-/
@[simp]
def ppEmbedObj (c : C) : ParallelPairObj C :=
  ⟨c, c, 𝟙 c, 𝟙 c⟩

/--
The embedding of a morphism from C into the free coequalizer completion.
-/
@[simp]
def ppEmbedHom {c d : C} (f : c ⟶ d) : ppEmbedObj c ⟶ ppEmbedObj d :=
  ⟨f, f, by simp, by simp⟩

@[simp]
lemma ppEmbedHom_srcHom {c d : C} (f : c ⟶ d) :
    ppSrcHom (ppEmbedHom f) = f := rfl

@[simp]
lemma ppEmbedHom_tgtHom {c d : C} (f : c ⟶ d) :
    ppTgtHom (ppEmbedHom f) = f := rfl

lemma ppEmbedHom_id (c : C) : ppEmbedHom (𝟙 c) = 𝟙 (ppEmbedObj c) := by
  apply ParallelPairHom.ext <;> simp

lemma ppEmbedHom_comp {c d e : C} (f : c ⟶ d) (g : d ⟶ e) :
    ppEmbedHom (f ≫ g) = ppEmbedHom f ≫ ppEmbedHom g := by
  apply ParallelPairHom.ext <;> simp

variable (C)

/--
The embedding functor from C to its free coequalizer completion.
-/
@[simp]
def ppEmbedding : C ⥤ ParallelPairObj C where
  obj := ppEmbedObj
  map := ppEmbedHom
  map_id := ppEmbedHom_id
  map_comp := ppEmbedHom_comp

end Embedding

/-! ## Coequalizer data

Similar to `CoprodData` and `ProdData` in Families.lean, we define
`CoequalizerData` to provide computable coequalizer structure.
-/

section CoequalizerData

/--
`CoequalizerData` provides computable coequalizer structure for a category.
This includes the coequalizer object and projection for any parallel pair.
-/
class CoequalizerData (D : Type*) [Category D] where
  /-- The coequalizer object for a parallel pair of morphisms. -/
  coeq : {X Y : D} → (f g : X ⟶ Y) → D
  /-- The projection from Y to the coequalizer. -/
  π : {X Y : D} → (f g : X ⟶ Y) → (Y ⟶ coeq f g)
  /-- The coequalizer condition: π coequalizes f and g. -/
  condition : {X Y : D} → (f g : X ⟶ Y) → f ≫ π f g = g ≫ π f g
  /-- The universal property: factorization through the coequalizer. -/
  desc : {X Y Z : D} → (f g : X ⟶ Y) → (h : Y ⟶ Z) → (f ≫ h = g ≫ h) →
    (coeq f g ⟶ Z)
  /-- Factorization property: π ≫ desc = h. -/
  fac : {X Y Z : D} → (f g : X ⟶ Y) → (h : Y ⟶ Z) → (w : f ≫ h = g ≫ h) →
    π f g ≫ desc f g h w = h
  /-- Uniqueness: any morphism with π ≫ m = h equals desc. -/
  uniq : {X Y Z : D} → (f g : X ⟶ Y) → (h : Y ⟶ Z) → (w : f ≫ h = g ≫ h) →
    (m : coeq f g ⟶ Z) → π f g ≫ m = h → m = desc f g h w

end CoequalizerData

/-! ## Helper lemmas for morphism components -/

section MorphismHelpers

variable {C}

/--
Helper lemma: extracting the src component condition from h ≫ π' = k ≫ π'.
-/
lemma ppHom_eq_srcHom_aux {P Q R : ParallelPairObj C} {h k : P ⟶ Q}
    {π' : Q ⟶ R} (hπ' : h ≫ π' = k ≫ π') :
    ppSrcHom h ≫ ppSrcHom π' = ppSrcHom k ≫ ppSrcHom π' := by
  have := congrArg ppSrcHom hπ'
  simp only [ppHom_comp_eq, ppComp_srcHom] at this
  exact this

/--
Helper lemma: extracting the tgt component condition from h ≫ π' = k ≫ π'.
-/
lemma ppHom_eq_tgtHom_aux {P Q R : ParallelPairObj C} {h k : P ⟶ Q}
    {π' : Q ⟶ R} (hπ' : h ≫ π' = k ≫ π') :
    ppTgtHom h ≫ ppTgtHom π' = ppTgtHom k ≫ ppTgtHom π' := by
  have := congrArg ppTgtHom hπ'
  simp only [ppHom_comp_eq, ppComp_tgtHom] at this
  exact this

end MorphismHelpers

/-! ## Coequalizers in the free coequalizer completion

When the underlying category C has `CoequalizerData`, the free coequalizer
completion also has coequalizers, computed pointwise.
-/

section Coequalizers

variable {C}
variable [CoequalizerData C]

/--
The coequalizer object for two parallel morphisms h, k : P ⟶ Q in the free
coequalizer completion. Computed pointwise using `CoequalizerData`.
-/
@[simp]
def ppCoequalizerObj {P Q : ParallelPairObj C} (h k : P ⟶ Q) :
    ParallelPairObj C where
  src := CoequalizerData.coeq (ppSrcHom h) (ppSrcHom k)
  tgt := CoequalizerData.coeq (ppTgtHom h) (ppTgtHom k)
  left := CoequalizerData.desc (ppSrcHom h) (ppSrcHom k)
    (Q.left ≫ CoequalizerData.π (ppTgtHom h) (ppTgtHom k))
    (by rw [← Category.assoc, ← Category.assoc, ppLeftComm h, ppLeftComm k,
            Category.assoc, Category.assoc, CoequalizerData.condition])
  right := CoequalizerData.desc (ppSrcHom h) (ppSrcHom k)
    (Q.right ≫ CoequalizerData.π (ppTgtHom h) (ppTgtHom k))
    (by rw [← Category.assoc, ← Category.assoc, ppRightComm h, ppRightComm k,
            Category.assoc, Category.assoc, CoequalizerData.condition])

/--
The coequalizer projection from Q to the coequalizer of h and k.
-/
@[simp]
def ppCoequalizerπ {P Q : ParallelPairObj C} (h k : P ⟶ Q) :
    Q ⟶ ppCoequalizerObj h k where
  srcHom := CoequalizerData.π (ppSrcHom h) (ppSrcHom k)
  tgtHom := CoequalizerData.π (ppTgtHom h) (ppTgtHom k)
  left_comm := by simp only [ppCoequalizerObj, CoequalizerData.fac]
  right_comm := by simp only [ppCoequalizerObj, CoequalizerData.fac]

/--
The coequalizer condition: the projection coequalizes h and k.
-/
lemma ppCoequalizer_condition {P Q : ParallelPairObj C} (h k : P ⟶ Q) :
    h ≫ ppCoequalizerπ h k = k ≫ ppCoequalizerπ h k := by
  apply ParallelPairHom.ext
  · simp only [ppHom_comp_eq, ppComp, ppCoequalizerπ]
    exact CoequalizerData.condition (ppSrcHom h) (ppSrcHom k)
  · simp only [ppHom_comp_eq, ppComp, ppCoequalizerπ]
    exact CoequalizerData.condition (ppTgtHom h) (ppTgtHom k)

/--
Morphisms out of a coequalizer are equal if they agree when precomposed with π.
-/
lemma CoequalizerData.eq_of_π_comp {D : Type*} [Category D] [CoequalizerData D]
    {X Y Z : D} (f g : X ⟶ Y) (m₁ m₂ : CoequalizerData.coeq f g ⟶ Z)
    (heq : CoequalizerData.π f g ≫ m₁ = CoequalizerData.π f g ≫ m₂) : m₁ = m₂ := by
  have w : f ≫ (CoequalizerData.π f g ≫ m₂) = g ≫ (CoequalizerData.π f g ≫ m₂) := by
    rw [← Category.assoc, ← Category.assoc, CoequalizerData.condition]
  have h₁ := CoequalizerData.uniq f g (CoequalizerData.π f g ≫ m₂) w m₁ heq
  have h₂ := CoequalizerData.uniq f g (CoequalizerData.π f g ≫ m₂) w m₂ rfl
  rw [h₁, ← h₂]

/--
For any cocone (R, π') with π' : Q ⟶ R such that h ≫ π' = k ≫ π',
there exists a morphism from the coequalizer to R.
-/
@[simp]
def ppCoequalizerDesc {P Q R : ParallelPairObj C} (h k : P ⟶ Q)
    (π' : Q ⟶ R) (hπ' : h ≫ π' = k ≫ π') : ppCoequalizerObj h k ⟶ R where
  srcHom := CoequalizerData.desc (ppSrcHom h) (ppSrcHom k) (ppSrcHom π')
    (ppHom_eq_srcHom_aux hπ')
  tgtHom := CoequalizerData.desc (ppTgtHom h) (ppTgtHom k) (ppTgtHom π')
    (ppHom_eq_tgtHom_aux hπ')
  left_comm := by
    simp only [ppCoequalizerObj]
    apply CoequalizerData.eq_of_π_comp
    rw [← Category.assoc, CoequalizerData.fac]
    rw [← Category.assoc, CoequalizerData.fac]
    rw [Category.assoc, CoequalizerData.fac]
    exact ppLeftComm π'
  right_comm := by
    simp only [ppCoequalizerObj]
    apply CoequalizerData.eq_of_π_comp
    rw [← Category.assoc, CoequalizerData.fac]
    rw [← Category.assoc, CoequalizerData.fac]
    rw [Category.assoc, CoequalizerData.fac]
    exact ppRightComm π'

lemma ppCoequalizer_π_desc {P Q R : ParallelPairObj C} (h k : P ⟶ Q)
    (π' : Q ⟶ R) (hπ' : h ≫ π' = k ≫ π') :
    ppCoequalizerπ h k ≫ ppCoequalizerDesc h k π' hπ' = π' := by
  apply ParallelPairHom.ext
  · simp only [ppHom_comp_eq, ppComp, ppCoequalizerπ, ppCoequalizerDesc]
    exact CoequalizerData.fac (ppSrcHom h) (ppSrcHom k) (ppSrcHom π') _
  · simp only [ppHom_comp_eq, ppComp, ppCoequalizerπ, ppCoequalizerDesc]
    exact CoequalizerData.fac (ppTgtHom h) (ppTgtHom k) (ppTgtHom π') _

lemma ppCoequalizer_desc_unique {P Q R : ParallelPairObj C} (h k : P ⟶ Q)
    (π' : Q ⟶ R) (hπ' : h ≫ π' = k ≫ π')
    (m : ppCoequalizerObj h k ⟶ R)
    (hm : ppCoequalizerπ h k ≫ m = π') :
    m = ppCoequalizerDesc h k π' hπ' := by
  apply ParallelPairHom.ext
  · have hsrc : ppSrcHom (ppCoequalizerπ h k ≫ m) = ppSrcHom π' := by rw [hm]
    simp only [ppHom_comp_eq, ppComp, ppCoequalizerπ] at hsrc
    simp only [ppCoequalizerDesc]
    apply CoequalizerData.uniq
    exact hsrc
  · have htgt : ppTgtHom (ppCoequalizerπ h k ≫ m) = ppTgtHom π' := by rw [hm]
    simp only [ppHom_comp_eq, ppComp, ppCoequalizerπ] at htgt
    simp only [ppCoequalizerDesc]
    apply CoequalizerData.uniq
    exact htgt

/--
The cofork for the coequalizer of h and k in the free coequalizer completion.
-/
def ppCofork {P Q : ParallelPairObj C} (h k : P ⟶ Q) :
    Cofork h k :=
  Cofork.ofπ (ppCoequalizerπ h k) (ppCoequalizer_condition h k)

/--
The cofork is a colimit (i.e., the coequalizer).
-/
def ppCofork_isColimit {P Q : ParallelPairObj C} (h k : P ⟶ Q) :
    IsColimit (ppCofork h k) :=
  Cofork.IsColimit.mk (ppCofork h k)
    (fun s => ppCoequalizerDesc h k s.π s.condition)
    (fun s => ppCoequalizer_π_desc h k s.π s.condition)
    (fun s m hm => ppCoequalizer_desc_unique h k s.π s.condition m hm)

end Coequalizers

end GebLean
