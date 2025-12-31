import GebLean.PLang.CatJudgGrothendieck
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Reflective

/-!
# Adjunction between Cat and CompWitGr

This module constructs the reflective embedding adjunction L ⊣ Φ where:
- Φ : Cat.{v, u} ⥤ CompWitGr.{u, v, w, x} is the embedding functor
- L : CompWitGr.{u, v, w, x} ⥤ Cat.{v, u} is the reflection functor

The adjunction has fully independent universe levels:
- `u` : universe of objects in Cat
- `v` : universe of morphisms in Cat
- `w` : universe of identity witnesses in CompWitGr
- `x` : universe of composition witnesses in CompWitGr

The embedding Φ sends a category C to the CompWitGr structure encoding:
- Objects and morphisms from C as the quiver
- Identity witnesses: one per object, recording the identity morphism
- Composition witnesses: one per composable pair, recording the composite

The reflection L constructs the quotient category from a CompWitGr:
- Same objects as the underlying quiver
- Morphisms are equivalence classes of free morphism expressions
- Quotient by relations from identity/composition witnesses
-/

namespace GebLean

namespace PLang

open CategoryTheory

namespace GrAdjunction

universe u v w x

/-! ## Embedding Functor Φ : Cat → CompWitGr

For a category C, we construct:
1. QuiverGr: objects = C.Obj, morphisms = C.Hom
2. IdWitBundle: witness type = C.Obj, witness data = identity morphisms
3. CompWitBundle: witness type = composable pairs, witness data = compositions
-/

section PhiObjects

variable (C : Cat.{v, u})

/-- The quiver structure from a category: objects and morphisms. -/
def categoryToQuiver : Groth.QuiverGr.{u, v} :=
  Groth.QuiverGr.mk C.α (fun p => p.1 ⟶ p.2)

@[simp]
theorem categoryToQuiver_objType : (categoryToQuiver C).objType = C.α := rfl

@[simp]
theorem categoryToQuiver_Hom (x y : C.α) :
    (categoryToQuiver C).Hom x y = (x ⟶ y) := rfl

/-- The identity witness bundle from a category.
    Each object witnesses its own identity morphism. -/
def categoryIdWitBundle :
    Groth.IdWitBundle.{u, v, u} (categoryToQuiver C) where
  witType := C.α
  witObj := id
  witMor := fun x => 𝟙 x

/-- The IdWitGr structure from a category. -/
def categoryToIdWitGr : Groth.IdWitGr.{u, v, u} :=
  ⟨categoryToQuiver C, categoryIdWitBundle C⟩

@[simp]
theorem categoryToIdWitGr_quiver :
    (categoryToIdWitGr C).quiver = categoryToQuiver C := rfl

/-- The witness type for composition: triples of composable morphisms.
    We use the type of composable pairs (x → y → z) with a morphism x → z. -/
def CompWitType : Type (max u v) :=
  Σ (x y z : C.α), (x ⟶ y) × (y ⟶ z)

/-- The composition witness bundle from a category.
    Each composable pair (f, g) witnesses that f ≫ g is the composite. -/
def categoryCompWitBundle :
    Groth.CompWitBundle.{u, v, u, max u v} (categoryToIdWitGr C) where
  witType := CompWitType C
  witSrc := fun ⟨x, _, _, _, _⟩ => x
  witMid := fun ⟨_, y, _, _, _⟩ => y
  witTgt := fun ⟨_, _, z, _, _⟩ => z
  witLeft := fun ⟨_, _, _, f, _⟩ => f
  witRight := fun ⟨_, _, _, _, g⟩ => g
  witComp := fun ⟨_, _, _, f, g⟩ => f ≫ g

/-- The CompWitGr structure from a category: the full embedding target. -/
def categoryToCompWitGr : Groth.CompWitGr.{u, v, u, max u v} :=
  ⟨categoryToIdWitGr C, categoryCompWitBundle C⟩

@[simp]
theorem categoryToCompWitGr_objType :
    (categoryToCompWitGr C).objType = C.α := rfl

end PhiObjects

/-! ### Φ on Morphisms (Functors) -/

section PhiMorphisms

variable {C D : Cat.{v, u}} (F : C ⥤ D)

/-- The quiver morphism induced by a functor. -/
def functorToQuiverHom :
    categoryToQuiver C ⟶ categoryToQuiver D where
  base := F.obj
  fiber := fun ⟨_, _⟩ f => F.map f

/-- The IdWitBundle morphism induced by a functor. -/
def functorToIdWitBundleHom :
    Groth.IdWitBundle.Hom
      (Groth.IdWitBundle.pushforward (functorToQuiverHom F) (categoryIdWitBundle C))
      (categoryIdWitBundle D) where
  witMap := F.obj
  witObj_eq := fun _ => rfl
  witMor_eq := fun x => by
    simp only [Groth.IdWitBundle.pushforward, categoryIdWitBundle, functorToQuiverHom]
    exact heq_of_eq (F.map_id x).symm

/-- The IdWitGr morphism induced by a functor. -/
def functorToIdWitGrHom :
    categoryToIdWitGr C ⟶ categoryToIdWitGr D :=
  ⟨functorToQuiverHom F, functorToIdWitBundleHom F⟩

/-- The CompWitBundle morphism induced by a functor. -/
def functorToCompWitBundleHom :
    Groth.CompWitBundle.Hom
      (Groth.CompWitBundle.pushforward (functorToIdWitGrHom F) (categoryCompWitBundle C))
      (categoryCompWitBundle D) where
  witMap := fun ⟨x, y, z, f, g⟩ => ⟨F.obj x, F.obj y, F.obj z, F.map f, F.map g⟩
  witSrc_eq := fun _ => rfl
  witMid_eq := fun _ => rfl
  witTgt_eq := fun _ => rfl
  witLeft_eq := fun _ => HEq.rfl
  witRight_eq := fun _ => HEq.rfl
  witComp_eq := fun ⟨_, _, _, f, g⟩ => by
    simp only [Groth.CompWitBundle.pushforward, categoryCompWitBundle, functorToIdWitGrHom,
      functorToQuiverHom]
    exact heq_of_eq (F.map_comp f g).symm

/-- The CompWitGr morphism induced by a functor: Φ(F). -/
def functorToCompWitGrHom :
    categoryToCompWitGr C ⟶ categoryToCompWitGr D :=
  ⟨functorToIdWitGrHom F, functorToCompWitBundleHom F⟩

end PhiMorphisms

/-! ### Φ Functor Definition -/

/-- The identity functor maps to the identity morphism. -/
theorem functorToCompWitGrHom_id (C : Cat.{v, u}) :
    functorToCompWitGrHom (𝟭 C) = 𝟙 (categoryToCompWitGr C) := by
  simp only [functorToCompWitGrHom, functorToIdWitGrHom, functorToQuiverHom,
    functorToIdWitBundleHom, functorToCompWitBundleHom]
  rfl

/-- Composition of functors maps to composition of morphisms. -/
theorem functorToCompWitGrHom_comp {A B E : Cat.{v, u}}
    (F : A ⥤ B) (G : B ⥤ E) :
    (functorToCompWitGrHom (F.comp G) :
      categoryToCompWitGr A ⟶ categoryToCompWitGr E) =
    functorToCompWitGrHom F ≫ functorToCompWitGrHom G := by
  simp only [functorToCompWitGrHom, functorToIdWitGrHom, functorToQuiverHom,
    functorToIdWitBundleHom, functorToCompWitBundleHom]
  rfl

/-- The embedding functor Φ : Cat → CompWitGr.
    Sends categories to their canonical CompWitGr encoding. -/
def PhiFunctor : Cat.{v, u} ⥤ Groth.CompWitGr.{u, v, u, max u v} where
  obj C := categoryToCompWitGr C
  map F := functorToCompWitGrHom F
  map_id C := functorToCompWitGrHom_id C
  map_comp F G := functorToCompWitGrHom_comp F G

/-! ## Reflection Functor L : CompWitGr → Cat

For a CompWitGr X, we construct the quotient category L(X):
1. Objects = X.objType (objects of the underlying quiver)
2. Morphisms = Quot(FreeMor) by identity and composition witness relations
3. Category structure from FreeMor's identity/composition quotiented
-/

universe uObj uMor uWit uCWit

/-- Free morphisms over a quiver: formal expressions built from variables,
    identity, and composition. -/
inductive FreeMor (X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}) :
    X.objType → X.objType → Type (max uObj uMor) where
  /-- A variable morphism from the underlying quiver. -/
  | var {a b : X.objType} : X.Hom' a b → FreeMor X a b
  /-- The formal identity at an object. -/
  | id (a : X.objType) : FreeMor X a a
  /-- Composition of free morphisms. -/
  | comp {a b c : X.objType} : FreeMor X b c → FreeMor X a b → FreeMor X a c

namespace FreeMor

variable {X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}}

/-- Cast a free morphism along object equalities. -/
def castEq {a b a' b' : X.objType} (ha : a = a') (hb : b = b')
    (f : FreeMor X a b) : FreeMor X a' b' :=
  ha ▸ hb ▸ f

@[simp]
theorem castEq_rfl {a b : X.objType} (f : FreeMor X a b) :
    f.castEq rfl rfl = f := rfl

theorem castEq_trans {a b a' b' a'' b'' : X.objType}
    (ha : a = a') (hb : b = b') (ha' : a' = a'') (hb' : b' = b'')
    (f : FreeMor X a b) :
    (f.castEq ha hb).castEq ha' hb' = f.castEq (ha.trans ha') (hb.trans hb') := by
  subst ha hb ha' hb'; rfl

/-- HEq lifts through the var constructor with heterogeneous endpoint equalities. -/
theorem var_heq' {a₁ b₁ a₂ b₂ : X.objType} {m₁ : X.Hom' a₁ b₁} {m₂ : X.Hom' a₂ b₂}
    (ha : a₁ = a₂) (hb : b₁ = b₂)
    (hm : HEq m₁ m₂) : HEq (FreeMor.var m₁) (FreeMor.var m₂) := by
  subst ha hb
  exact heq_of_eq (congrArg FreeMor.var (eq_of_heq hm))

end FreeMor

/-- Generating relations for the free morphism equivalence.
    These come from the category axioms plus witness relations. -/
inductive FreeMorEquivGen (X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}) :
    {a b : X.objType} → FreeMor X a b → FreeMor X a b → Prop where
  /-- Left identity: id ∘ f ~ f -/
  | id_left {a b : X.objType} (f : FreeMor X a b) :
      FreeMorEquivGen X (.comp (.id b) f) f
  /-- Right identity: f ∘ id ~ f -/
  | id_right {a b : X.objType} (f : FreeMor X a b) :
      FreeMorEquivGen X (.comp f (.id a)) f
  /-- Associativity: (h ∘ g) ∘ f ~ h ∘ (g ∘ f) -/
  | assoc {a b c d : X.objType}
      (h : FreeMor X c d) (g : FreeMor X b c) (f : FreeMor X a b) :
      FreeMorEquivGen X (.comp (.comp h g) f) (.comp h (.comp g f))
  /-- Identity witness: var(witMor i) ~ id(witObj i). -/
  | id_witness (i : X.idBundle.witType) :
      FreeMorEquivGen X
        (.var (X.idBundle.witMor i))
        (.id (X.idBundle.witObj i))
  /-- Composition witness: var(left) ∘ var(right) ~ var(composite). -/
  | comp_witness (c : X.bundle.witType) :
      FreeMorEquivGen X
        (.comp (.var (X.bundle.witRight c)) (.var (X.bundle.witLeft c)))
        (.var (X.bundle.witComp c))

/-- The equivalence relation on free morphisms. -/
inductive FreeMorEquiv (X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}) :
    {a b : X.objType} → FreeMor X a b → FreeMor X a b → Prop where
  /-- Include generating relations. -/
  | rel {a b : X.objType} {f g : FreeMor X a b} :
      FreeMorEquivGen X f g → FreeMorEquiv X f g
  /-- Reflexivity. -/
  | refl {a b : X.objType} (f : FreeMor X a b) : FreeMorEquiv X f f
  /-- Symmetry. -/
  | symm {a b : X.objType} {f g : FreeMor X a b} :
      FreeMorEquiv X f g → FreeMorEquiv X g f
  /-- Transitivity. -/
  | trans {a b : X.objType} {f g h : FreeMor X a b} :
      FreeMorEquiv X f g → FreeMorEquiv X g h → FreeMorEquiv X f h
  /-- Left congruence: f ~ g implies h ∘ f ~ h ∘ g. -/
  | cong_left {a b c : X.objType}
      (h : FreeMor X b c) {f g : FreeMor X a b} :
      FreeMorEquiv X f g → FreeMorEquiv X (.comp h f) (.comp h g)
  /-- Right congruence: f ~ g implies f ∘ h ~ g ∘ h. -/
  | cong_right {a b c : X.objType}
      {f g : FreeMor X b c} (h : FreeMor X a b) :
      FreeMorEquiv X f g → FreeMorEquiv X (.comp f h) (.comp g h)

theorem FreeMorEquiv.isEquiv (X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit})
    {a b : X.objType} :
    Equivalence (FreeMorEquiv X (a := a) (b := b)) where
  refl := FreeMorEquiv.refl
  symm := FreeMorEquiv.symm
  trans := FreeMorEquiv.trans

/-- The setoid on free morphisms. -/
def freeMorSetoid (X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit})
    (a b : X.objType) : Setoid (FreeMor X a b) where
  r := FreeMorEquiv X
  iseqv := FreeMorEquiv.isEquiv X

/-- The quotient type of morphisms in L(X). -/
def QuotMor (X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit})
    (a b : X.objType) : Type (max uObj uMor) :=
  Quotient (freeMorSetoid X a b)

namespace QuotMor

variable {X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}}

/-- The identity quotient morphism. -/
def id (a : X.objType) : QuotMor X a a :=
  Quotient.mk (freeMorSetoid X a a) (.id a)

/-- Composition of quotient morphisms. -/
def comp {a b c : X.objType} (g : QuotMor X b c) (f : QuotMor X a b) :
    QuotMor X a c :=
  Quotient.lift₂
    (fun g' f' => Quotient.mk _ (.comp g' f'))
    (fun _ _ _ _ hg hf => Quotient.sound
      (FreeMorEquiv.trans (FreeMorEquiv.cong_left _ hf)
        (FreeMorEquiv.cong_right _ hg)))
    g f

theorem id_comp {a b : X.objType} (f : QuotMor X a b) :
    comp (id b) f = f := by
  induction f using Quotient.ind
  apply Quotient.sound
  exact FreeMorEquiv.rel (FreeMorEquivGen.id_left _)

theorem comp_id {a b : X.objType} (f : QuotMor X a b) :
    comp f (id a) = f := by
  induction f using Quotient.ind
  apply Quotient.sound
  exact FreeMorEquiv.rel (FreeMorEquivGen.id_right _)

theorem comp_assoc {a b c d : X.objType}
    (h : QuotMor X c d) (g : QuotMor X b c) (f : QuotMor X a b) :
    comp (comp h g) f = comp h (comp g f) := by
  induction h using Quotient.ind
  induction g using Quotient.ind
  induction f using Quotient.ind
  apply Quotient.sound
  exact FreeMorEquiv.rel (FreeMorEquivGen.assoc _ _ _)

end QuotMor

/-- The category structure on L(X) with QuotMor morphisms. -/
instance instCategoryLX (X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}) :
    Category.{max uObj uMor} X.objType where
  Hom := QuotMor X
  id := QuotMor.id
  comp f g := QuotMor.comp g f
  id_comp := QuotMor.comp_id
  comp_id := QuotMor.id_comp
  assoc f g h := (QuotMor.comp_assoc h g f).symm

/-- L(X) as an object in Cat. -/
def LObj (X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}) :
    Cat.{max uObj uMor, uObj} :=
  Cat.of X.objType

/-! ### L on Morphisms -/

/-- The object map of L(F). -/
def LMorObj {X Y : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}} (F : X ⟶ Y) :
    X.objType → Y.objType :=
  F.base.base.base

/-- Map a free morphism along a CompWitGr morphism. -/
def mapFreeMor {X Y : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}} (F : X ⟶ Y) :
    {a b : X.objType} → FreeMor X a b → FreeMor Y (LMorObj F a) (LMorObj F b)
  | _, _, .var f => .var (F.base.base.fiber ⟨_, _⟩ f)
  | _, _, .id a => .id (LMorObj F a)
  | _, _, .comp g f => .comp (mapFreeMor F g) (mapFreeMor F f)

/-- mapFreeMor respects the generating equivalence relation. -/
theorem mapFreeMor_respects_gen {X Y : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}}
    (F : X ⟶ Y) {a b : X.objType} {f g : FreeMor X a b}
    (h : FreeMorEquivGen X f g) :
    FreeMorEquiv Y (mapFreeMor F f) (mapFreeMor F g) := by
  cases h with
  | id_left f' =>
    exact FreeMorEquiv.rel (FreeMorEquivGen.id_left _)
  | id_right f' =>
    exact FreeMorEquiv.rel (FreeMorEquivGen.id_right _)
  | assoc h' g' f' =>
    exact FreeMorEquiv.rel (FreeMorEquivGen.assoc _ _ _)
  | id_witness i =>
    have hobj := F.base.fiber.witObj_eq i
    have hmor := F.base.fiber.witMor_eq i
    simp only [mapFreeMor, LMorObj]
    have h := FreeMorEquiv.rel (FreeMorEquivGen.id_witness (F.base.fiber.witMap i))
    simp only [Groth.CompWitGr.idBundle] at h
    convert h using 2
    case h.e'_2 => exact hobj.symm
    case h.e'_3 => exact hobj.symm
    case h.e'_4.e'_4 => exact hmor.symm
  | comp_witness c =>
    have hsrc := F.fiber.witSrc_eq c
    have hmid := F.fiber.witMid_eq c
    have htgt := F.fiber.witTgt_eq c
    have hleft := F.fiber.witLeft_eq c
    have hright := F.fiber.witRight_eq c
    have hcomp := F.fiber.witComp_eq c
    simp only [Groth.compWitFunctor, Groth.CompWitBundle.pushforwardFunctor,
      Groth.CompWitBundle.pushforward] at hsrc hmid htgt hleft hright hcomp
    simp only [mapFreeMor, LMorObj]
    have h := FreeMorEquiv.rel (FreeMorEquivGen.comp_witness (F.fiber.witMap c))
    simp only [Groth.CompWitGr.bundle] at h
    convert h using 2
    case h.e'_2 => exact hsrc.symm
    case h.e'_3 => exact htgt.symm
    case h.e'_4.e'_3 => exact hmid.symm
    case h.e'_4.e'_5 =>
      simp only [Groth.CompWitGr.bundle]
      exact FreeMor.var_heq' hmid.symm htgt.symm hright.symm
    case h.e'_4.e'_6 =>
      simp only [Groth.CompWitGr.bundle]
      exact FreeMor.var_heq' hsrc.symm hmid.symm hleft.symm
    case h.e'_5.e'_4 => exact hcomp.symm

/-- mapFreeMor respects the full equivalence relation. -/
theorem mapFreeMor_respects {X Y : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}}
    (F : X ⟶ Y) {a b : X.objType} {f g : FreeMor X a b}
    (h : FreeMorEquiv X f g) :
    FreeMorEquiv Y (mapFreeMor F f) (mapFreeMor F g) := by
  induction h with
  | rel hr => exact mapFreeMor_respects_gen F hr
  | refl _ => exact FreeMorEquiv.refl _
  | symm _ ih => exact FreeMorEquiv.symm ih
  | trans _ _ ih1 ih2 => exact FreeMorEquiv.trans ih1 ih2
  | cong_left h' _ ih => exact FreeMorEquiv.cong_left _ ih
  | cong_right h' _ ih => exact FreeMorEquiv.cong_right _ ih

/-- L(F) on morphisms descends to the quotient. -/
def LMorHom {X Y : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}} (F : X ⟶ Y)
    {a b : X.objType} (f : QuotMor X a b) :
    QuotMor Y (LMorObj F a) (LMorObj F b) :=
  Quotient.lift
    (fun f' => Quotient.mk (freeMorSetoid Y _ _) (mapFreeMor F f'))
    (fun _ _ h => Quotient.sound (mapFreeMor_respects F h))
    f

theorem LMorHom_id {X Y : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}} (F : X ⟶ Y)
    (a : X.objType) :
    LMorHom F (QuotMor.id a) = QuotMor.id (LMorObj F a) := by
  simp only [LMorHom, QuotMor.id, Quotient.lift_mk, mapFreeMor]

theorem LMorHom_comp {X Y : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}} (F : X ⟶ Y)
    {a b c : X.objType} (g : QuotMor X b c) (f : QuotMor X a b) :
    LMorHom F (QuotMor.comp g f) = QuotMor.comp (LMorHom F g) (LMorHom F f) := by
  induction g using Quotient.ind
  induction f using Quotient.ind
  rfl

/-- L(F) as a functor L(X) ⥤ L(Y). -/
def LMorFunctor {X Y : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}} (F : X ⟶ Y) :
    LObj X ⥤ LObj Y where
  obj := LMorObj F
  map := LMorHom F
  map_id := LMorHom_id F
  map_comp f g := LMorHom_comp F g f

/-- Helper: mapFreeMor with identity morphism is equivalent to the original. -/
theorem mapFreeMor_id_equiv {X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}}
    {a b : X.objType} (m : FreeMor X a b) :
    FreeMorEquiv X (mapFreeMor (𝟙 X) m) m := by
  induction m with
  | var v =>
    simp only [mapFreeMor]
    apply FreeMorEquiv.refl
  | id a =>
    simp only [mapFreeMor]
    apply FreeMorEquiv.refl
  | comp g f ihg ihf =>
    simp only [mapFreeMor]
    exact FreeMorEquiv.trans
      (FreeMorEquiv.cong_left _ ihf)
      (FreeMorEquiv.cong_right _ ihg)

/-- L preserves identity morphisms: L(id_X) = id_{L(X)}. -/
theorem LMorFunctor_id (X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}) :
    LMorFunctor (𝟙 X) = 𝟙 (LObj X) := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro a
    rfl
  case h_map =>
    intro a b f
    simp only [CategoryTheory.eqToHom_refl,
      CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp]
    induction f using Quotient.ind
    simp only [LMorFunctor, LMorHom, Quotient.lift_mk]
    apply Quotient.sound
    exact mapFreeMor_id_equiv _

/-- Helper: mapFreeMor distributes over composition of morphisms in CompWitGr. -/
theorem mapFreeMor_comp_equiv {X Y Z : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}}
    (F : X ⟶ Y) (G : Y ⟶ Z) {a b : X.objType} (m : FreeMor X a b) :
    FreeMorEquiv Z (mapFreeMor (F ≫ G) m) (mapFreeMor G (mapFreeMor F m)) := by
  induction m with
  | var v =>
    simp only [mapFreeMor]
    apply FreeMorEquiv.refl
  | id a =>
    simp only [mapFreeMor]
    apply FreeMorEquiv.refl
  | comp g f ihg ihf =>
    simp only [mapFreeMor]
    exact FreeMorEquiv.trans
      (FreeMorEquiv.cong_left _ ihf)
      (FreeMorEquiv.cong_right _ ihg)

/-- L preserves composition: L(G ∘ F) = L(G) ∘ L(F). -/
theorem LMorFunctor_comp {X Y Z : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}}
    (F : X ⟶ Y) (G : Y ⟶ Z) :
    LMorFunctor (F ≫ G) = LMorFunctor F ⋙ LMorFunctor G := by
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro a
    rfl
  case h_map =>
    intro a b f
    simp only [CategoryTheory.eqToHom_refl,
      CategoryTheory.Category.comp_id, CategoryTheory.Category.id_comp,
      CategoryTheory.Functor.comp_map]
    induction f using Quotient.ind
    simp only [LMorFunctor, LMorHom, Quotient.lift_mk]
    apply Quotient.sound
    exact mapFreeMor_comp_equiv F G _

/-- The reflection functor L : CompWitGr ⥤ Cat. -/
def LFunctor : Groth.CompWitGr.{uObj, uMor, uWit, uCWit} ⥤ Cat.{max uObj uMor, uObj} where
  obj := fun X => LObj X
  map := fun F => LMorFunctor F
  map_id := fun X => LMorFunctor_id X
  map_comp := fun F G => LMorFunctor_comp F G

end GrAdjunction

end PLang

end GebLean
