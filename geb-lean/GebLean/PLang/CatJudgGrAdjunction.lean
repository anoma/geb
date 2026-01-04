import GebLean.PLang.CatJudgGrothendieck
import Mathlib.CategoryTheory.Adjunction.Basic
import Mathlib.CategoryTheory.Adjunction.Reflective

/-!
# Adjunction between Cat and CompWitGr

This module constructs the reflective embedding adjunction L ⊣ Φ where:
- Φ : Cat.{v, u} ⥤ CompWitGr.{u, v, u, max u v} is the embedding functor
- L : CompWitGr.{uObj, uMor, uWit, uCWit} ⥤ Cat.{max uObj uMor, uObj} is the
  reflection functor

Universe parameters:
- `u` / `uObj` : universe of objects
- `v` / `uMor` : universe of morphisms
- `uWit` : universe of identity witnesses (Φ sets this to u)
- `uCWit` : universe of composition witnesses (Φ sets this to max u v)

The morphism universe of L(X) is `max uObj uMor` rather than `uMor` due to a
fundamental constraint: free morphisms must reference intermediate objects
for composition, bundling object data (at uObj) with morphism data (at uMor).

For the adjunction L ⊣ Φ to compose cleanly (L ∘ Φ : Cat.{v,u} → Cat.{v,u}),
we require `u ≤ v` so that `max u v = v`.

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

@[simp]
theorem categoryToIdWitGr_fiber_witType :
    (categoryToIdWitGr C).fiber.witType = C.α := rfl

@[simp]
theorem categoryToCompWitGr_base_fiber_witType :
    (categoryToCompWitGr C).base.fiber.witType = C.α := rfl

@[simp]
theorem categoryIdWitBundle_witMor (x : C.α) :
    (categoryIdWitBundle C).witMor x = 𝟙 x := rfl

@[simp]
theorem categoryToCompWitGr_base_fiber_witMor (x : C.α) :
    (categoryToCompWitGr C).base.fiber.witMor x = 𝟙 x := rfl

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
  map F := functorToCompWitGrHom F.toFunctor
  map_id C := functorToCompWitGrHom_id C
  map_comp F G := functorToCompWitGrHom_comp F.toFunctor G.toFunctor

/-! ## Reflection Functor L : CompWitGr → Cat

For a CompWitGr X, we construct the quotient category L(X):
1. Objects = X.objType (objects of the underlying quiver)
2. Morphisms = Quot(FreeMor) by identity and composition witness relations
3. Category structure from FreeMor's identity/composition quotiented

The construction uses bundled morphisms to achieve proper universe polymorphism.
The free morphism expressions are defined without object indices, with a separate
validity predicate (as a Prop) tracking the typing. This allows the morphism
universe to be independent of the object universe.
-/

universe uObj uMor uWit uCWit

/-! ### Bundled Morphism Type -/

/-- The total space of morphisms in a CompWitGr: pairs of objects with a
    morphism between them. Using a flat structure (rather than nested sigma)
    enables dependent pattern matching in validity proofs. -/
@[ext]
structure MorBundle (X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}) :
    Type (max uObj uMor) where
  /-- Source object -/
  src : X.objType
  /-- Target object -/
  tgt : X.objType
  /-- The morphism from source to target -/
  mor : X.Hom' src tgt

namespace MorBundle

variable {X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}}

@[simp]
theorem mk_src (a b : X.objType) (f : X.Hom' a b) : (MorBundle.mk a b f).src = a := rfl

@[simp]
theorem mk_tgt (a b : X.objType) (f : X.Hom' a b) : (MorBundle.mk a b f).tgt = b := rfl

@[simp]
theorem mk_mor (a b : X.objType) (f : X.Hom' a b) :
    (MorBundle.mk a b f).mor = f := rfl

end MorBundle

/-! ### Free Morphism Expressions (Non-indexed) -/

/-- Free morphisms over a quiver: formal expressions built from variables,
    identity, and composition. This type is NOT indexed by source/target;
    instead, validity is tracked by a separate Prop predicate.

    Objects are stored in id and comp to enable evaluation without needing
    to extract data from validity proofs (which are Props). -/
inductive FreeMorRaw (X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}) :
    Type (max uObj uMor) where
  /-- A variable morphism from the underlying quiver (bundled with endpoints). -/
  | var : MorBundle X → FreeMorRaw X
  /-- The formal identity at a given object. -/
  | id : X.objType → FreeMorRaw X
  /-- Composition with intermediate object stored for evaluation. -/
  | comp : X.objType → FreeMorRaw X → FreeMorRaw X → FreeMorRaw X

/-- Validity predicate for free morphisms - indicates a raw morphism
    represents a valid morphism from a to b. This is a Prop for proof irrelevance. -/
inductive ValidFreeMor (X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}) :
    X.objType → X.objType → FreeMorRaw X → Prop where
  /-- A variable is valid if it matches the bundled endpoints. -/
  | var (m : MorBundle X) : ValidFreeMor X m.src m.tgt (.var m)
  /-- Identity is valid when stored object matches endpoints. -/
  | id (a : X.objType) : ValidFreeMor X a a (.id a)
  /-- Composition valid when stored intermediate matches and both parts valid. -/
  | comp {a b c : X.objType} {g f : FreeMorRaw X}
      (hg : ValidFreeMor X b c g) (hf : ValidFreeMor X a b f) :
      ValidFreeMor X a c (.comp b g f)

/-- Free morphisms with tracked validity: a raw expression paired with
    a validity witness that it represents a valid morphism from a to b.
    Uses Subtype since ValidFreeMor is a Prop. -/
def FreeMor (X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit})
    (a b : X.objType) : Type (max uObj uMor) :=
  { m : FreeMorRaw X // ValidFreeMor X a b m }

namespace FreeMor

variable {X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}}

/-- Construct a variable free morphism from endpoints and a quiver morphism. -/
def var (a b : X.objType) (f : X.Hom' a b) : FreeMor X a b :=
  ⟨.var (MorBundle.mk a b f), ValidFreeMor.var (MorBundle.mk a b f)⟩

/-- The identity free morphism at an object. -/
def id (a : X.objType) : FreeMor X a a :=
  ⟨.id a, ValidFreeMor.id a⟩

/-- Composition of free morphisms. -/
def comp {a b c : X.objType} (g : FreeMor X b c) (f : FreeMor X a b) :
    FreeMor X a c :=
  ⟨.comp b g.1 f.1, ValidFreeMor.comp g.2 f.2⟩

/-- Extract the raw free morphism. -/
def raw {a b : X.objType} (f : FreeMor X a b) : FreeMorRaw X := f.1

/-- The validity witness for a free morphism. -/
def valid {a b : X.objType} (f : FreeMor X a b) : ValidFreeMor X a b f.raw :=
  f.2

/-- Cast a free morphism along object equalities. -/
def castEq {a b a' b' : X.objType} (ha : a = a') (hb : b = b')
    (f : FreeMor X a b) : FreeMor X a' b' :=
  ⟨f.1, ha ▸ hb ▸ f.2⟩

@[simp]
theorem castEq_rfl {a b : X.objType} (f : FreeMor X a b) :
    f.castEq rfl rfl = f := rfl

theorem castEq_trans {a b a' b' a'' b'' : X.objType}
    (ha : a = a') (hb : b = b') (ha' : a' = a'') (hb' : b' = b'')
    (f : FreeMor X a b) :
    (f.castEq ha hb).castEq ha' hb' = f.castEq (ha.trans ha') (hb.trans hb') := by
  subst ha hb ha' hb'; rfl

/-- HEq for var when endpoints and morphisms are heterogeneously equal. -/
theorem var_heq' {a₁ b₁ a₂ b₂ : X.objType} {m₁ : X.Hom' a₁ b₁} {m₂ : X.Hom' a₂ b₂}
    (ha : a₁ = a₂) (hb : b₁ = b₂)
    (hm : HEq m₁ m₂) : HEq (var a₁ b₁ m₁) (var a₂ b₂ m₂) := by
  subst ha hb
  have : m₁ = m₂ := eq_of_heq hm
  subst this
  rfl

/-- Extensionality for FreeMor: equal raw parts implies equal FreeMors.
    This follows from Subtype.ext since ValidFreeMor is a Prop. -/
theorem ext {a b : X.objType} {m1 m2 : FreeMor X a b}
    (h : m1.1 = m2.1) : m1 = m2 :=
  Subtype.ext h

end FreeMor

/-- Generating relations for the free morphism equivalence.
    These come from the category axioms plus witness relations.
    Relations are defined on the raw representations. -/
inductive FreeMorEquivGen (X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}) :
    {a b : X.objType} → FreeMor X a b → FreeMor X a b → Prop where
  /-- Left identity: id ∘ f ~ f -/
  | id_left {a b : X.objType} (f : FreeMor X a b) :
      FreeMorEquivGen X (FreeMor.comp (FreeMor.id b) f) f
  /-- Right identity: f ∘ id ~ f -/
  | id_right {a b : X.objType} (f : FreeMor X a b) :
      FreeMorEquivGen X (FreeMor.comp f (FreeMor.id a)) f
  /-- Associativity: (h ∘ g) ∘ f ~ h ∘ (g ∘ f) -/
  | assoc {a b c d : X.objType}
      (h : FreeMor X c d) (g : FreeMor X b c) (f : FreeMor X a b) :
      FreeMorEquivGen X
        (FreeMor.comp (FreeMor.comp h g) f)
        (FreeMor.comp h (FreeMor.comp g f))
  /-- Identity witness: var(witMor i) ~ id(witObj i). -/
  | id_witness (i : X.idBundle.witType) :
      FreeMorEquivGen X
        (FreeMor.var (X.idBundle.witObj i) (X.idBundle.witObj i) (X.idBundle.witMor i))
        (FreeMor.id (X.idBundle.witObj i))
  /-- Composition witness: var(right) ∘ var(left) ~ var(composite). -/
  | comp_witness (c : X.bundle.witType) :
      FreeMorEquivGen X
        (FreeMor.comp
          (FreeMor.var (X.bundle.witMid c) (X.bundle.witTgt c) (X.bundle.witRight c))
          (FreeMor.var (X.bundle.witSrc c) (X.bundle.witMid c) (X.bundle.witLeft c)))
        (FreeMor.var (X.bundle.witSrc c) (X.bundle.witTgt c) (X.bundle.witComp c))

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
      FreeMorEquiv X f g →
      FreeMorEquiv X (FreeMor.comp h f) (FreeMor.comp h g)
  /-- Right congruence: f ~ g implies f ∘ h ~ g ∘ h. -/
  | cong_right {a b c : X.objType}
      {f g : FreeMor X b c} (h : FreeMor X a b) :
      FreeMorEquiv X f g →
      FreeMorEquiv X (FreeMor.comp f h) (FreeMor.comp g h)

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

@[simp]
theorem LMorObj_id {X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}} (a : X.objType) :
    LMorObj (𝟙 X) a = a := rfl

@[simp]
theorem LMorObj_comp {X Y Z : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}}
    (F : X ⟶ Y) (G : Y ⟶ Z) (a : X.objType) :
    LMorObj (F ≫ G) a = LMorObj G (LMorObj F a) := rfl

/-- Map a raw free morphism along a CompWitGr morphism. -/
def mapFreeMorRaw {X Y : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}} (F : X ⟶ Y) :
    FreeMorRaw X → FreeMorRaw Y
  | .var m => .var (MorBundle.mk (LMorObj F m.src) (LMorObj F m.tgt)
                     (F.base.base.fiber ⟨m.src, m.tgt⟩ m.mor))
  | .id a => .id (LMorObj F a)
  | .comp b g f => .comp (LMorObj F b) (mapFreeMorRaw F g) (mapFreeMorRaw F f)

/-- Validity is preserved by mapping. -/
def mapFreeMorRaw_valid {X Y : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}} (F : X ⟶ Y)
    {a b : X.objType} {m : FreeMorRaw X} :
    ValidFreeMor X a b m → ValidFreeMor Y (LMorObj F a) (LMorObj F b) (mapFreeMorRaw F m)
  | .var bundle =>
    ValidFreeMor.var (MorBundle.mk (LMorObj F bundle.src) (LMorObj F bundle.tgt)
      (F.base.base.fiber ⟨bundle.src, bundle.tgt⟩ bundle.mor))
  | .id a => ValidFreeMor.id (LMorObj F a)
  | .comp hg hf => ValidFreeMor.comp (mapFreeMorRaw_valid F hg) (mapFreeMorRaw_valid F hf)

/-- Map a free morphism along a CompWitGr morphism. -/
def mapFreeMor {X Y : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}} (F : X ⟶ Y)
    {a b : X.objType} (m : FreeMor X a b) : FreeMor Y (LMorObj F a) (LMorObj F b) :=
  ⟨mapFreeMorRaw F m.1, mapFreeMorRaw_valid F m.2⟩

@[simp]
theorem mapFreeMor_var {X Y : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}} (F : X ⟶ Y)
    (a b : X.objType) (f : X.Hom' a b) :
    mapFreeMor F (FreeMor.var a b f) =
      FreeMor.var (LMorObj F a) (LMorObj F b) (F.base.base.fiber ⟨a, b⟩ f) := rfl

@[simp]
theorem mapFreeMor_id {X Y : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}} (F : X ⟶ Y)
    (a : X.objType) :
    mapFreeMor F (FreeMor.id a) = FreeMor.id (LMorObj F a) := rfl

@[simp]
theorem mapFreeMor_comp {X Y : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}} (F : X ⟶ Y)
    {a b c : X.objType} (g : FreeMor X b c) (f : FreeMor X a b) :
    mapFreeMor F (FreeMor.comp g f) = FreeMor.comp (mapFreeMor F g) (mapFreeMor F f) := rfl

/-- mapFreeMor respects the generating equivalence relation. -/
theorem mapFreeMor_respects_gen {X Y : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}}
    (F : X ⟶ Y) {a b : X.objType} {f g : FreeMor X a b}
    (h : FreeMorEquivGen X f g) :
    FreeMorEquiv Y (mapFreeMor F f) (mapFreeMor F g) := by
  cases h with
  | id_left f' =>
    simp only [mapFreeMor_comp, mapFreeMor_id]
    exact FreeMorEquiv.rel (FreeMorEquivGen.id_left _)
  | id_right f' =>
    simp only [mapFreeMor_comp, mapFreeMor_id]
    exact FreeMorEquiv.rel (FreeMorEquivGen.id_right _)
  | assoc h' g' f' =>
    simp only [mapFreeMor_comp]
    exact FreeMorEquiv.rel (FreeMorEquivGen.assoc _ _ _)
  | id_witness i =>
    have hobj := F.base.fiber.witObj_eq i
    have hmor := F.base.fiber.witMor_eq i
    simp only [mapFreeMor_var, mapFreeMor_id, LMorObj]
    have h := FreeMorEquiv.rel (FreeMorEquivGen.id_witness (F.base.fiber.witMap i))
    simp only [Groth.CompWitGr.idBundle] at h
    convert h using 2
    case h.e'_2 => exact hobj.symm
    case h.e'_3 => exact hobj.symm
    case h.e'_4 =>
      simp only [Groth.CompWitGr.idBundle]
      exact hmor.symm
  | comp_witness c =>
    have hsrc := F.fiber.witSrc_eq c
    have hmid := F.fiber.witMid_eq c
    have htgt := F.fiber.witTgt_eq c
    have hleft := F.fiber.witLeft_eq c
    have hright := F.fiber.witRight_eq c
    have hcomp := F.fiber.witComp_eq c
    simp only [Groth.compWitFunctor,
      Groth.CompWitBundle.pushforwardFunctor] at hsrc hmid htgt hleft hright hcomp
    simp only [mapFreeMor_var, mapFreeMor_comp, LMorObj]
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
    case h.e'_5 =>
      simp only [Groth.CompWitGr.bundle]
      exact hcomp.symm

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
  | cong_left h' _ ih =>
    simp only [mapFreeMor_comp]
    exact FreeMorEquiv.cong_left _ ih
  | cong_right h' _ ih =>
    simp only [mapFreeMor_comp]
    exact FreeMorEquiv.cong_right _ ih

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
  simp only [LMorHom, QuotMor.id, Quotient.lift_mk, mapFreeMor_id]

theorem LMorHom_comp {X Y : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}} (F : X ⟶ Y)
    {a b c : X.objType} (g : QuotMor X b c) (f : QuotMor X a b) :
    LMorHom F (QuotMor.comp g f) = QuotMor.comp (LMorHom F g) (LMorHom F f) := by
  induction g using Quotient.ind
  induction f using Quotient.ind
  simp only [QuotMor.comp, LMorHom, Quotient.lift_mk, mapFreeMor_comp]

/-- L(F) as a functor L(X) ⥤ L(Y). -/
def LMorFunctor {X Y : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}} (F : X ⟶ Y) :
    LObj X ⥤ LObj Y where
  obj := LMorObj F
  map := LMorHom F
  map_id := LMorHom_id F
  map_comp f g := LMorHom_comp F g f

/-- Helper: mapFreeMorRaw with identity morphism equals the original. -/
theorem mapFreeMorRaw_id {X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}}
    (m : FreeMorRaw X) :
    mapFreeMorRaw (𝟙 X) m = m := by
  induction m with
  | var v => rfl
  | id a => rfl
  | comp b g f ihg ihf => simp only [mapFreeMorRaw, LMorObj_id, ihg, ihf]

/-- Mapping by identity gives the same raw morphism. -/
theorem mapFreeMor_id_raw {X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}}
    {a b : X.objType} (m : FreeMor X a b) :
    (mapFreeMor (𝟙 X) m).1 = m.1 := mapFreeMorRaw_id m.1

/-- Helper: mapFreeMor with identity is the same up to equivalence. -/
theorem mapFreeMor_id_equiv {X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}}
    {a b : X.objType} (m : FreeMor X a b) :
    FreeMorEquiv X (mapFreeMor (𝟙 X) m) m := by
  have h : mapFreeMor (𝟙 X) m = m := FreeMor.ext (mapFreeMor_id_raw m)
  rw [h]
  exact FreeMorEquiv.refl m

/-- L preserves identity morphisms: L(id_X) = id_{L(X)}. -/
theorem LMorFunctor_id (X : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}) :
    LMorFunctor (𝟙 X) = Cat.Hom.toFunctor (𝟙 (LObj X)) := by
  unfold Cat.Hom.toFunctor
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

/-- Helper: mapFreeMorRaw distributes over composition of morphisms. -/
theorem mapFreeMorRaw_comp {X Y Z : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}}
    (F : X ⟶ Y) (G : Y ⟶ Z) (m : FreeMorRaw X) :
    mapFreeMorRaw (F ≫ G) m = mapFreeMorRaw G (mapFreeMorRaw F m) := by
  induction m with
  | var v => rfl
  | id a => rfl
  | comp b g f ihg ihf => simp only [mapFreeMorRaw, LMorObj_comp, ihg, ihf]

/-- Helper: mapFreeMor distributes over composition of morphisms in CompWitGr. -/
theorem mapFreeMor_comp_equiv {X Y Z : Groth.CompWitGr.{uObj, uMor, uWit, uCWit}}
    (F : X ⟶ Y) (G : Y ⟶ Z) {a b : X.objType} (m : FreeMor X a b) :
    FreeMorEquiv Z (mapFreeMor (F ≫ G) m) (mapFreeMor G (mapFreeMor F m)) := by
  have h : mapFreeMor (F ≫ G) m = mapFreeMor G (mapFreeMor F m) :=
    FreeMor.ext (mapFreeMorRaw_comp F G m.1)
  rw [h]
  exact FreeMorEquiv.refl _

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
  map := fun F => (LMorFunctor F).toCatHom
  map_id := fun X => Cat.Hom.ext (LMorFunctor_id X)
  map_comp := fun F G => Cat.Hom.ext (LMorFunctor_comp F G)

end GrAdjunction

/-! ## Counit: L ∘ Φ ⟶ Id

The counit evaluates free morphisms in the actual category.
For C : Cat, the counit at C is a functor εC : L(Φ(C)) → C that:
- On objects: identity (both have objects = C.α)
- On morphisms: evaluates formal expressions using C's composition

The counit is defined on QuotMor (the quotient of free morphisms) since
the morphisms in L(Φ(C)) are QuotMor values, not FreeMor values.
-/
section Counit

open GrAdjunction

universe uC vC

variable (C : Cat.{vC, uC})

/-- The CompWitGr structure from a category (alias for cleaner notation). -/
abbrev ΦC := categoryToCompWitGr C

/-- Extract the stored source from a FreeMorRaw.
    This matches the source we'd expect from validity. -/
def storedSrc : FreeMorRaw (ΦC C) → C.α
  | .var bundle => bundle.src
  | .id a => a
  | .comp _ _ f => storedSrc f

/-- Extract the stored target from a FreeMorRaw.
    This matches the target we'd expect from validity. -/
def storedTgt : FreeMorRaw (ΦC C) → C.α
  | .var bundle => bundle.tgt
  | .id a => a
  | .comp _ g _ => storedTgt g

/-- For valid FreeMor, stored source equals the actual source. -/
theorem storedSrc_valid {a b : (ΦC C).objType} {m : FreeMorRaw (ΦC C)}
    (h : ValidFreeMor (ΦC C) a b m) : storedSrc C m = a := by
  induction h with
  | var _ => rfl
  | id _ => rfl
  | comp _ _ _ ihf => exact ihf

/-- For valid FreeMor, stored target equals the actual target. -/
theorem storedTgt_valid {a b : (ΦC C).objType} {m : FreeMorRaw (ΦC C)}
    (h : ValidFreeMor (ΦC C) a b m) : storedTgt C m = b := by
  induction h with
  | var _ => rfl
  | id _ => rfl
  | comp _ _ ihg _ => exact ihg

/-- Extract sub-validity for the left part of a composition. -/
theorem ValidFreeMor.comp_left {a c mid : (ΦC C).objType}
    {g f : FreeMorRaw (ΦC C)} (h : ValidFreeMor (ΦC C) a c (.comp mid g f)) :
    ValidFreeMor (ΦC C) a mid f := by
  cases h; assumption

/-- Extract sub-validity for the right part of a composition. -/
theorem ValidFreeMor.comp_right {a c mid : (ΦC C).objType}
    {g f : FreeMorRaw (ΦC C)} (h : ValidFreeMor (ΦC C) a c (.comp mid g f)) :
    ValidFreeMor (ΦC C) mid c g := by
  cases h; assumption

/-- Evaluate a FreeMorRaw with validity witness. We recurse on the raw morphism
    and use validity-derived equalities to type the result.
    The result is a morphism in the original category C (via ΦC C's Hom type). -/
def evalFreeMorRaw : (m : FreeMorRaw (ΦC C)) → (a b : (ΦC C).objType) →
    ValidFreeMor (ΦC C) a b m → (ΦC C).Hom' a b
  | .var bundle, _, _, h =>
      (storedSrc_valid C h) ▸ (storedTgt_valid C h) ▸ bundle.mor
  | .id c, _, _, h =>
      (storedSrc_valid C h) ▸ (storedTgt_valid C h) ▸
        @CategoryStruct.id C.α C.str.toCategoryStruct c
  | .comp mid g f, a, c, h =>
      let hf := ValidFreeMor.comp_left C h
      let hg := ValidFreeMor.comp_right C h
      @CategoryStruct.comp C.α C.str.toCategoryStruct a mid c
        (evalFreeMorRaw f a mid hf) (evalFreeMorRaw g mid c hg)

/-- Evaluate a FreeMor (with validity) to an actual morphism in C. -/
def evalFreeMor {a b : (ΦC C).objType} (m : FreeMor (ΦC C) a b) :
    (ΦC C).Hom' a b :=
  evalFreeMorRaw C m.1 a b m.2

/-- Evaluation of the identity FreeMor gives the identity morphism. -/
theorem evalFreeMor_id (a : (ΦC C).objType) :
    evalFreeMor C (FreeMor.id a) =
      @CategoryStruct.id C.α C.str.toCategoryStruct a := rfl

/-- Evaluation of composition of FreeMors gives composition of morphisms. -/
theorem evalFreeMor_comp {a b c : (ΦC C).objType}
    (g : FreeMor (ΦC C) b c) (f : FreeMor (ΦC C) a b) :
    evalFreeMor C (FreeMor.comp g f) =
      @CategoryStruct.comp C.α C.str.toCategoryStruct a b c
        (evalFreeMor C f) (evalFreeMor C g) := rfl

/-- Evaluation of a variable gives the stored morphism. -/
theorem evalFreeMor_var (a b : (ΦC C).objType) (f : (ΦC C).Hom' a b) :
    evalFreeMor C (FreeMor.var a b f) = f := rfl

/-- Evaluation respects the generating equivalence relation. -/
theorem evalFreeMor_respects_gen {a b : (ΦC C).objType}
    {m n : FreeMor (ΦC C) a b} (h : FreeMorEquivGen (ΦC C) m n) :
    evalFreeMor C m = evalFreeMor C n := by
  cases h with
  | id_left _ =>
    simp only [evalFreeMor_comp, evalFreeMor_id]
    exact C.str.comp_id (evalFreeMor C n)
  | id_right _ =>
    simp only [evalFreeMor_comp, evalFreeMor_id]
    exact C.str.id_comp (evalFreeMor C n)
  | assoc _ _ _ =>
    simp only [evalFreeMor_comp]
    exact (C.str.assoc _ _ _).symm
  | id_witness _ =>
    rfl
  | comp_witness _ =>
    rfl

/-- Evaluation respects the full equivalence relation. -/
theorem evalFreeMor_respects {a b : (ΦC C).objType}
    {m n : FreeMor (ΦC C) a b} (h : FreeMorEquiv (ΦC C) m n) :
    evalFreeMor C m = evalFreeMor C n := by
  induction h with
  | rel h => exact evalFreeMor_respects_gen C h
  | refl _ => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih1 ih2 => exact ih1.trans ih2
  | cong_left h _ ih =>
    simp only [evalFreeMor_comp, ih]
  | cong_right h _ ih =>
    simp only [evalFreeMor_comp, ih]

/-- Evaluation respects the setoid equivalence. -/
theorem evalFreeMor_respects' {a b : (ΦC C).objType}
    (m n : FreeMor (ΦC C) a b) (h : (freeMorSetoid (ΦC C) a b).r m n) :
    evalFreeMor C m = evalFreeMor C n :=
  evalFreeMor_respects C h

/-- Evaluation on QuotMor: descends to the quotient. -/
def evalQuotMor {a b : (ΦC C).objType} (m : QuotMor (ΦC C) a b) :
    (ΦC C).Hom' a b :=
  Quotient.lift (evalFreeMor C) (evalFreeMor_respects' C) m

/-- Evaluation preserves identity: evalQuotMor (id a) = 𝟙 a. -/
theorem evalQuotMor_id (a : (ΦC C).objType) :
    evalQuotMor C (QuotMor.id a) =
      @CategoryStruct.id C.α C.str.toCategoryStruct a := by
  simp only [QuotMor.id, evalQuotMor, Quotient.lift_mk, evalFreeMor_id]

/-- Evaluation preserves composition: evalQuotMor (g ∘ f) = evalQuotMor f ≫ evalQuotMor g. -/
theorem evalQuotMor_comp {a b c : (ΦC C).objType}
    (g : QuotMor (ΦC C) b c) (f : QuotMor (ΦC C) a b) :
    evalQuotMor C (QuotMor.comp g f) =
      @CategoryStruct.comp C.α C.str.toCategoryStruct a b c
        (evalQuotMor C f) (evalQuotMor C g) := by
  induction g using Quotient.ind
  induction f using Quotient.ind
  simp only [QuotMor.comp, evalQuotMor, Quotient.lift_mk, evalFreeMor_comp]

/-- The counit functor at C: L(Φ(C)) ⥤ C.
    This evaluates formal morphism expressions in the actual category. -/
def counitGr : (LObj (ΦC C)) ⥤ C where
  obj := id
  map := fun f => evalQuotMor C f
  map_id := fun a => evalQuotMor_id C a
  map_comp := fun f g => evalQuotMor_comp C g f

end Counit

namespace GrAdjunction

/-! ### Unit η : Id ⟶ Φ ∘ L

For X : CompWitGr, the unit η_X : X ⟶ Φ(L(X)) embeds generators into the
free category and views the result through Φ.

The universe configuration for the adjunction requires uMor = max uObj uMor
(i.e., uObj ≤ uMor). This section works with this constraint. -/

section Unit

universe uObj uMor

/-- CompWitGr with universes suitable for the adjunction: morphisms already at
    max uObj uMor, witnesses at uObj and max uObj uMor respectively. -/
abbrev AdjCompWitGr :=
  Groth.CompWitGr.{uObj, max uObj uMor, uObj, max uObj uMor}

variable (X : AdjCompWitGr.{uObj, uMor})

/-- The target of the unit at X: Φ(L(X)).
    With the constrained universes, this lands in the same category as X. -/
abbrev ΦLX : AdjCompWitGr.{uObj, uMor} :=
  PhiFunctor.obj (LObj X)

/-- Embed a generator morphism as a quotient class. -/
def embedAsQuot {a b : X.objType} (f : X.Hom' a b) : QuotMor X a b :=
  @Quotient.mk' _ (freeMorSetoid X a b) (FreeMor.var a b f)

/-- LMorHom applied to an embedded generator equals embedding the mapped
    generator. This is definitional because mapFreeMor preserves variables. -/
@[simp]
theorem LMorHom_embedAsQuot {X' Y' : AdjCompWitGr.{uObj, uMor}}
    (F : X' ⟶ Y') {a b : X'.objType} (m : X'.Hom' a b) :
    LMorHom F (embedAsQuot X' m) = embedAsQuot Y' (F.base.base.fiber ⟨a, b⟩ m) :=
  rfl

/-- Embedding as quotient preserves heterogeneous equality.
    Explicit endpoint equalities are needed to guide the subst. -/
theorem embedAsQuot_heq {X' : AdjCompWitGr.{uObj, uMor}}
    {a₁ b₁ a₂ b₂ : X'.objType}
    (ha : a₁ = a₂) (hb : b₁ = b₂)
    {m₁ : X'.Hom' a₁ b₁} {m₂ : X'.Hom' a₂ b₂}
    (hm : m₁ ≍ m₂) : embedAsQuot X' m₁ ≍ embedAsQuot X' m₂ := by
  subst ha hb
  exact heq_of_eq (congrArg (embedAsQuot X') (eq_of_heq hm))

/-- HEq of product pairs from HEq of components. -/
theorem prod_mk_heq'.{u, v} {A₁ A₂ : Type u} {B₁ B₂ : Type v}
    {a₁ : A₁} {a₂ : A₂} (ha : a₁ ≍ a₂)
    {b₁ : B₁} {b₂ : B₂} (hb : b₁ ≍ b₂) :
    (a₁, b₁) ≍ (a₂, b₂) := by
  cases ha
  cases hb
  rfl

/-- Round-trip for the unit-counit: evaluating an embedded morphism returns
    the original. This applies when X is the embedding of a category. -/
@[simp]
theorem evalQuotMor_embedAsQuot (C : Cat.{max uObj uMor, uObj})
    {a b : (categoryToCompWitGr C).objType}
    (f : (categoryToCompWitGr C).Hom' a b) :
    evalQuotMor C (embedAsQuot (categoryToCompWitGr C) f) = f := rfl

/-- The quiver morphism component of the unit: identity on objects,
    embedding on morphisms. -/
def unitQuiverMor : X.quiver ⟶ categoryToQuiver (LObj X) where
  base := id
  fiber := fun _ f => embedAsQuot X f

/-- The identity witness bundle morphism component of the unit.
    Maps identity witnesses in X to identity witnesses in Φ(L(X)).
    The pushforward of X.idBundle along unitQuiverMor has:
    - witType = X.idBundle.witType
    - witObj w = unitQuiverMor.base (X.idBundle.witObj w) = X.idBundle.witObj w
    - witMor w = unitQuiverMor.fiber (X.idBundle.witMor w) = ⟦var (X.idBundle.witMor w)⟧
    The target categoryIdWitBundle (LObj X) has:
    - witType = X.objType
    - witObj = id
    - witMor x = QuotMor.id x = ⟦FreeMor.id x⟧ -/
def unitIdWitBundleMor :
    Groth.IdWitBundle.Hom
      (Groth.IdWitBundle.pushforward (unitQuiverMor X) X.idBundle)
      (categoryIdWitBundle (LObj X)) where
  witMap := fun w => X.idBundle.witObj w
  witObj_eq := fun _ => rfl
  witMor_eq := fun w => by
    simp only [Groth.IdWitBundle.pushforward, categoryIdWitBundle, unitQuiverMor]
    apply heq_of_eq
    apply Quotient.sound
    exact FreeMorEquiv.symm (FreeMorEquiv.rel (FreeMorEquivGen.id_witness w))

/-- The IdWitGr morphism component of the unit: combines the quiver morphism
    with the identity witness bundle morphism. -/
def unitIdWitGrMor : X.idWitGr ⟶ categoryToIdWitGr (LObj X) :=
  ⟨unitQuiverMor X, unitIdWitBundleMor X⟩

/-- The composition witness bundle morphism component of the unit.
    Maps composition witnesses in X to composition witnesses in Φ(L(X)).
    comp_witness in FreeMorEquivGen establishes that
    var(right).comp(var(left)) ~ var(composite). -/
def unitCompWitBundleMor :
    Groth.CompWitBundle.Hom
      (Groth.CompWitBundle.pushforward (unitIdWitGrMor X) X.bundle)
      (categoryCompWitBundle (LObj X)) where
  witMap := fun w => ⟨X.bundle.witSrc w,
                      X.bundle.witMid w,
                      X.bundle.witTgt w,
                      embedAsQuot X (X.bundle.witLeft w),
                      embedAsQuot X (X.bundle.witRight w)⟩
  witSrc_eq := fun _ => rfl
  witMid_eq := fun _ => rfl
  witTgt_eq := fun _ => rfl
  witLeft_eq := fun w => by
    simp only [Groth.CompWitBundle.pushforward, unitIdWitGrMor, unitQuiverMor,
      categoryCompWitBundle]
    rfl
  witRight_eq := fun w => by
    simp only [Groth.CompWitBundle.pushforward, unitIdWitGrMor, unitQuiverMor,
      categoryCompWitBundle]
    rfl
  witComp_eq := fun w => by
    simp only [Groth.CompWitBundle.pushforward, unitIdWitGrMor, unitQuiverMor,
      categoryCompWitBundle, Groth.CompWitGr.bundle, Groth.sqFunctorOp', id]
    apply heq_of_eq
    apply Quotient.sound
    have h := FreeMorEquiv.rel (FreeMorEquivGen.comp_witness w)
    simp only [Groth.CompWitGr.bundle] at h
    exact h

/-- The full unit morphism η_X : X ⟶ Φ(L(X)) in CompWitGr. -/
def unitGr : X ⟶ ΦLX X :=
  ⟨unitIdWitGrMor X, unitCompWitBundleMor X⟩

end Unit

section Triangles

/-! ### Triangle Identities for L ⊣ Φ

The adjunction L ⊣ Φ requires two triangle identities:

1. Right triangle (for C : Cat): η_{Φ(C)} ≫ Φ(ε_C) = 𝟙_{Φ(C)}
   - Unit at Φ(C), then apply Φ to the counit at C
   - Shows round-trip from Φ(C) through Φ(L(Φ(C))) back to Φ(C) is identity

2. Left triangle (for X : CompWitGr): L(η_X) ≫ ε_{L(X)} = 𝟙_{L(X)}
   - Apply L to the unit at X, then counit at L(X)
   - Shows round-trip from L(X) through L(Φ(L(X))) back to L(X) is identity
-/

universe uObj uMor

variable (C : Cat.{max uObj uMor, uObj})

/-- The right triangle: η_{Φ(C)} ≫ Φ(ε_C) = 𝟙_{Φ(C)}.

For a category C, composing the unit at Φ(C) with Φ applied to the counit
gives the identity on Φ(C). This shows that embedding C into CompWitGr,
then taking the free category and embedding back, then evaluating, is the
identity.

Notes:
- η_{Φ(C)} embeds generators (morphisms of C) as quotient classes
- ε_C evaluates quotient classes back to actual morphisms
- Φ(ε_C) applies this pointwise in the CompWitGr structure
- Composing: a morphism f becomes [var f] then evaluates back to f -/
theorem rightTriangle :
    unitGr (categoryToCompWitGr C) ≫ PhiFunctor.map (counitGr C).toCatHom = 𝟙 _ := by
  -- CompWitGr is Grothendieck compWitFunctor, so morphisms have base (IdWitGr) and fiber
  refine Grothendieck.ext _ _ ?hbase ?hfiber
  case hbase =>
    -- Need to show IdWitGr morphisms are equal
    refine Grothendieck.ext _ _ ?_ ?_
    case _ =>
      -- QuiverGr base.base: id on objects
      rfl
    case _ =>
      -- IdWitBundle morphism equality
      simp only [unitGr, PhiFunctor, counitGr, functorToCompWitGrHom,
        functorToIdWitGrHom, functorToIdWitBundleHom, unitIdWitGrMor,
        unitIdWitBundleMor, categoryToCompWitGr, categoryToIdWitGr]
      apply Groth.IdWitBundle.Hom.ext
      intro w
      simp only [Groth.CompWitGr.idBundle, categoryCompWitBundle,
        categoryIdWitBundle, id]
      rfl
  case hfiber =>
    -- CompWitBundle morphism equality
    simp only [unitGr, PhiFunctor, counitGr, functorToCompWitGrHom,
      functorToIdWitGrHom, functorToCompWitBundleHom, unitIdWitGrMor,
      unitCompWitBundleMor, categoryToCompWitGr, categoryToIdWitGr]
    apply Groth.CompWitBundle.Hom.ext
    intro w
    simp only [categoryCompWitBundle, categoryIdWitBundle, id]
    rfl

variable (X : AdjCompWitGr.{uObj, uMor})

/-- Evaluating a mapped FreeMor through the unit gives back the original
    quotient class. This is the main lemma for the left triangle identity. -/
theorem evalQuotMor_mapFreeMor_unit {a b : X.objType} (m : FreeMor X a b) :
    evalQuotMor (LObj X) ⟦mapFreeMor (unitGr X) m⟧ = ⟦m⟧ := by
  -- Induct on the raw structure of m
  obtain ⟨raw, valid⟩ := m
  induction raw generalizing a b with
  | var bundle =>
    -- var case: unitGr.base.base.fiber gives embedAsQuot X bundle.mor
    -- which equals ⟦FreeMor.var bundle.src bundle.tgt bundle.mor⟧
    -- The valid predicate tells us a = bundle.src, b = bundle.tgt
    cases valid
    -- Now valid is ValidFreeMor.var bundle
    simp only [evalQuotMor, Quotient.lift_mk, mapFreeMor, mapFreeMorRaw]
    simp only [evalFreeMor, evalFreeMorRaw]
    -- Goal: (unitGr X).base.base.fiber ... = ⟦...⟧
    simp only [unitGr, unitIdWitGrMor, unitQuiverMor]
    -- The fiber is embedAsQuot X bundle.mor
    simp only [embedAsQuot, FreeMor.var]
    rfl
  | id obj =>
    -- id case: mapFreeMor preserves id, evalQuotMor of id gives ⟦id⟧
    cases valid
    simp only [evalQuotMor, Quotient.lift_mk, mapFreeMor, mapFreeMorRaw]
    simp only [evalFreeMor, evalFreeMorRaw]
    rfl
  | comp mid g f ihg ihf =>
    -- comp case: use the induction hypotheses on the components
    -- ValidFreeMor.comp takes validg first, then validf
    cases valid
    rename_i validg validf
    -- The quotient of a FreeMor.comp evaluates as composition in the target
    -- evalQuotMor respects composition via evalQuotMor_comp
    -- mapFreeMor of comp is comp of mapFreeMor: ⟦comp (map g) (map f)⟧
    simp only [mapFreeMor, mapFreeMorRaw]
    -- Now the argument is ⟦FreeMor.comp (mapFreeMor g) (mapFreeMor f)⟧
    -- Use that quotient of comp = QuotMor.comp of quotients
    simp only [evalQuotMor, Quotient.lift_mk]
    simp only [evalFreeMor, evalFreeMorRaw]
    -- Goal: evalFreeMorRaw f' ≫ evalFreeMorRaw g' = ⟦comp g f⟧
    -- Fold back to evalFreeMor for each component
    change evalFreeMor (LObj X) (mapFreeMor (unitGr X) ⟨f, validf⟩) ≫
           evalFreeMor (LObj X) (mapFreeMor (unitGr X) ⟨g, validg⟩) =
      ⟦⟨FreeMorRaw.comp mid g f, ValidFreeMor.comp validg validf⟩⟧
    -- The IH gives evalQuotMor ⟦...⟧ = ⟦...⟧
    -- evalQuotMor ⟦m⟧ = Quotient.lift evalFreeMor ... ⟦m⟧ = evalFreeMor m
    -- So evalFreeMor (mapFreeMor f) = evalQuotMor ⟦mapFreeMor f⟧ = ⟦f⟧
    have hf : evalFreeMor (LObj X) (mapFreeMor (unitGr X) ⟨f, validf⟩) =
        ⟦⟨f, validf⟩⟧ := by
      have := ihf validf
      simp only [evalQuotMor, Quotient.lift_mk] at this
      exact this
    have hg : evalFreeMor (LObj X) (mapFreeMor (unitGr X) ⟨g, validg⟩) =
        ⟦⟨g, validg⟩⟧ := by
      have := ihg validg
      simp only [evalQuotMor, Quotient.lift_mk] at this
      exact this
    rw [hf, hg]
    -- Goal: ⟦f⟧ ≫ ⟦g⟧ = ⟦comp g f⟧
    -- In Category X.objType: f ≫ g = QuotMor.comp g f = ⟦FreeMor.comp g f⟧
    rfl

/-- The left triangle: L(η_X) ≫ ε_{L(X)} = 𝟙_{L(X)}.

For X : CompWitGr, applying L to the unit at X, then the counit at L(X),
gives the identity functor on L(X). This shows that taking the free category,
embedding generators, taking free category again, then evaluating, is the
identity.

Notes:
- η_X embeds generators as quotient classes of single-variable expressions
- L(η_X) maps quotient classes in L(X) to quotient classes in L(Φ(L(X)))
- ε_{L(X)} evaluates these back by treating [var [f]] as just [f]
- Composing gives the identity because evaluation undoes embedding -/
theorem leftTriangle :
    LFunctor.map (unitGr X) ≫ (counitGr (LObj X)).toCatHom = 𝟙 (LObj X) := by
  apply Cat.Hom.ext
  apply Functor.ext
  case h_obj =>
    intro a
    -- Goal: (LFunctor.map (unitGr X) ≫ counitGr (LObj X)).obj a = (𝟙 (LObj X)).obj a
    rfl
  case h_map =>
    intro a b f
    -- Since h_obj was rfl, eqToHom simplifies to identities
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    -- Goal: (LFunctor.map (unitGr X) ≫ counitGr (LObj X)).map f = (𝟙 (LObj X)).map f
    -- Both sides should reduce to f
    change evalQuotMor (LObj X) (LMorHom (unitGr X) f) = f
    -- Proceed by induction on the quotient representative
    induction f using Quotient.ind
    rename_i m
    -- Goal: evalQuotMor (LObj X) (LMorHom (unitGr X) ⟦m⟧) = ⟦m⟧
    simp only [LMorHom, Quotient.lift_mk]
    -- Goal: evalQuotMor (LObj X) ⟦mapFreeMor (unitGr X) m⟧ = ⟦m⟧
    exact evalQuotMor_mapFreeMor_unit X m

end Triangles

/-! ## Full Faithfulness of Φ

Φ : Cat → CompWitGr is fully faithful: every CompWitGr morphism between
category encodings comes from a unique functor. The inverse map extracts
functor data from the quiver morphism component and uses the witness
morphisms to establish the functor laws.
-/

section FullFaithfulness

universe u v

variable {C D : Cat.{v, u}}

/-- Extract the object function from a CompWitGr morphism between categories.
    The base.base.base component gives the function on objects. -/
def compWitGrHomObjMap (φ : categoryToCompWitGr C ⟶ categoryToCompWitGr D) :
    C.α → D.α :=
  φ.base.base.base

/-- Extract the morphism function from a CompWitGr morphism between categories.
    The base.base.fiber component gives the function on morphisms. -/
def compWitGrHomMorMap (φ : categoryToCompWitGr C ⟶ categoryToCompWitGr D)
    {a b : C.α} (f : a ⟶ b) : compWitGrHomObjMap φ a ⟶ compWitGrHomObjMap φ b :=
  φ.base.base.fiber ⟨a, b⟩ f

/-- The IdWitBundle.Hom component witnesses that morphisms preserve identity.
    From this we extract the proof that map respects identity.

    The witness structure is:
    - `φ.base.fiber.witObj_eq a : witMap a = φ.base.base.base a`
    - `φ.base.fiber.witMor_eq a : 𝟙 (witMap a) ≍ φ.base.base.fiber (a,a) (𝟙 a)`
    Substituting the first into the second and flipping gives the result. -/
theorem compWitGrHomMapId (φ : categoryToCompWitGr C ⟶ categoryToCompWitGr D)
    (a : C.α) :
    compWitGrHomMorMap φ (𝟙 a) = 𝟙 (compWitGrHomObjMap φ a) := by
  unfold compWitGrHomMorMap compWitGrHomObjMap
  have hObj : φ.base.fiber.witMap a = φ.base.base.base a := φ.base.fiber.witObj_eq a
  have hMor := φ.base.fiber.witMor_eq a
  simp only [categoryToCompWitGr, categoryToIdWitGr, categoryIdWitBundle,
    Groth.idWitFunctor, Groth.IdWitBundle.pushforwardFunctor] at hMor
  apply eq_of_heq
  apply HEq.trans hMor.symm
  rw [hObj]

/-- The CompWitBundle.Hom component witnesses that morphisms preserve
    composition. From this we extract the proof that map respects comp.

    The witnesses `witLeft_eq`, `witRight_eq`, and `witComp_eq` together give:
    - witComp : `(witLeft) ≫ (witRight) ≍ map (f ≫ g)`
    - witLeft : `witLeft ≍ map f`
    - witRight : `witRight ≍ map g`
    Combining these yields `map f ≫ map g = map (f ≫ g)`. -/
theorem compWitGrHomMapComp (φ : categoryToCompWitGr C ⟶ categoryToCompWitGr D)
    {a b c : C.α} (f : a ⟶ b) (g : b ⟶ c) :
    compWitGrHomMorMap φ (f ≫ g) =
      compWitGrHomMorMap φ f ≫ compWitGrHomMorMap φ g := by
  unfold compWitGrHomMorMap compWitGrHomObjMap
  let w : CompWitType C := ⟨a, b, c, f, g⟩
  have hComp := φ.fiber.witComp_eq w
  have hLeft := φ.fiber.witLeft_eq w
  have hRight := φ.fiber.witRight_eq w
  have hSrc := φ.fiber.witSrc_eq w
  have hMid := φ.fiber.witMid_eq w
  have hTgt := φ.fiber.witTgt_eq w
  simp only [categoryToCompWitGr, categoryCompWitBundle, categoryToIdWitGr,
    categoryIdWitBundle, categoryToQuiver, Groth.compWitFunctor,
    Groth.CompWitBundle.pushforwardFunctor, CompWitType] at hComp hLeft hRight hSrc hMid hTgt
  -- Unfold w in hypotheses to get (a, b, c, f, g)
  simp only [w] at hComp hLeft hRight hSrc hMid hTgt
  -- Direct approach: convert through witness morphisms
  -- The types are definitionally equal once we unfold categoryToCompWitGr
  apply eq_of_heq
  apply HEq.trans hComp.symm
  -- Goal: witL ≫ witR ≍ map(f) ≫ map(g)
  -- Both sides are compositions in D, just with different type paths
  -- Since hSrc, hMid, hTgt prove object equality, the types are equal
  -- We need to work in D explicitly to avoid CategoryStruct synthesis issues
  -- The witness morphism types are definitionally D-morphisms, but Lean sees
  -- the Grothendieck layer wrapper. We convert using heq_iff_comp_eqToHom_comp.
  -- Since hSrc, hMid, hTgt are reflexive (same underlying objects in D), we can
  -- show the witness morphisms equal the phi-mapped morphisms directly.
  -- heq_iff_comp_eqToHom_comp: f ≍ g ↔ eqToHom p ≫ f ≫ eqToHom q = g
  -- where f : X ⟶ Y, g : W ⟶ Z, p : W = X, q : Y = Z
  -- For hLeft: witL : witSrc ⟶ witMid, mapF : φ.base a ⟶ φ.base b
  -- So p : φ.base a = witSrc = hSrc.symm, q : witMid = φ.base b = hMid
  have hLEq : @eqToHom D _ _ _ hSrc.symm ≫
      (φ.fiber.witMap ⟨a, ⟨b, ⟨c, (f, g)⟩⟩⟩).2.2.2.1 ≫
        @eqToHom D _ _ _ hMid = φ.base.base.fiber (a, b) f := by
    rw [← @heq_iff_comp_eqToHom_comp D _ _ _ _ _
      (φ.fiber.witMap ⟨a, ⟨b, ⟨c, (f, g)⟩⟩⟩).2.2.2.1
      (φ.base.base.fiber (a, b) f) hSrc.symm hMid]
    exact hLeft
  have hREq : @eqToHom D _ _ _ hMid.symm ≫
      (φ.fiber.witMap ⟨a, ⟨b, ⟨c, (f, g)⟩⟩⟩).2.2.2.2 ≫
        @eqToHom D _ _ _ hTgt = φ.base.base.fiber (b, c) g := by
    rw [← @heq_iff_comp_eqToHom_comp D _ _ _ _ _
      (φ.fiber.witMap ⟨a, ⟨b, ⟨c, (f, g)⟩⟩⟩).2.2.2.2
      (φ.base.base.fiber (b, c) g) hMid.symm hTgt]
    exact hRight
  -- Now compose the two equations
  -- Goal: witL ≫ witR ≍ mapF ≫ mapG
  -- We have hLEq: eqToHom ≫ witL ≫ eqToHom = mapF
  -- and hREq: eqToHom ≫ witR ≫ eqToHom = mapG
  -- Use heq_iff_comp_eqToHom_comp in reverse
  rw [@heq_iff_comp_eqToHom_comp D _ _ _ _ _
    ((φ.fiber.witMap ⟨a, ⟨b, ⟨c, (f, g)⟩⟩⟩).2.2.2.1 ≫
      (φ.fiber.witMap ⟨a, ⟨b, ⟨c, (f, g)⟩⟩⟩).2.2.2.2)
    (φ.base.base.fiber (a, b) f ≫ φ.base.base.fiber (b, c) g)
    hSrc.symm hTgt]
  -- Now need: eqToHom hSrc.symm ≫ (witL ≫ witR) ≫ eqToHom hTgt = mapF ≫ mapG
  calc @eqToHom D _ _ _ hSrc.symm ≫
        ((φ.fiber.witMap ⟨a, ⟨b, ⟨c, (f, g)⟩⟩⟩).2.2.2.1 ≫
         (φ.fiber.witMap ⟨a, ⟨b, ⟨c, (f, g)⟩⟩⟩).2.2.2.2) ≫ @eqToHom D _ _ _ hTgt
      = @eqToHom D _ _ _ hSrc.symm ≫ (φ.fiber.witMap ⟨a, ⟨b, ⟨c, (f, g)⟩⟩⟩).2.2.2.1 ≫
          (φ.fiber.witMap ⟨a, ⟨b, ⟨c, (f, g)⟩⟩⟩).2.2.2.2 ≫ @eqToHom D _ _ _ hTgt := by
        simp only [Category.assoc]
    _ = @eqToHom D _ _ _ hSrc.symm ≫ (φ.fiber.witMap ⟨a, ⟨b, ⟨c, (f, g)⟩⟩⟩).2.2.2.1 ≫
          (@eqToHom D _ _ _ hMid ≫ @eqToHom D _ _ _ hMid.symm) ≫
          (φ.fiber.witMap ⟨a, ⟨b, ⟨c, (f, g)⟩⟩⟩).2.2.2.2 ≫ @eqToHom D _ _ _ hTgt := by
        simp only [eqToHom_trans, eqToHom_refl, Category.id_comp]
    _ = (@eqToHom D _ _ _ hSrc.symm ≫ (φ.fiber.witMap ⟨a, ⟨b, ⟨c, (f, g)⟩⟩⟩).2.2.2.1 ≫
          @eqToHom D _ _ _ hMid) ≫ (@eqToHom D _ _ _ hMid.symm ≫
          (φ.fiber.witMap ⟨a, ⟨b, ⟨c, (f, g)⟩⟩⟩).2.2.2.2 ≫ @eqToHom D _ _ _ hTgt) := by
        simp only [Category.assoc]
    _ = φ.base.base.fiber (a, b) f ≫ φ.base.base.fiber (b, c) g := by
        rw [hLEq, hREq]

/-- Extract a functor from a CompWitGr morphism between category encodings.
    This is the inverse of PhiFunctor.map. -/
def compWitGrHomToFunctor
    (φ : categoryToCompWitGr C ⟶ categoryToCompWitGr D) : C ⥤ D where
  obj := compWitGrHomObjMap φ
  map := compWitGrHomMorMap φ
  map_id := compWitGrHomMapId φ
  map_comp := compWitGrHomMapComp φ

/-- PhiFunctor.map followed by compWitGrHomToFunctor is the identity. -/
theorem preimage_map (F : C ⥤ D) :
    compWitGrHomToFunctor (PhiFunctor.map F.toCatHom) = F := by
  apply Functor.ext
  case h_obj => intro a; rfl
  case h_map =>
    intro a b f
    simp only [eqToHom_refl, Category.comp_id, Category.id_comp]
    simp only [compWitGrHomToFunctor, compWitGrHomMorMap, compWitGrHomObjMap]
    simp only [PhiFunctor, functorToCompWitGrHom, functorToIdWitGrHom,
      functorToQuiverHom]
    unfold Functor.toCatHom Cat.Hom.toFunctor
    rfl

/-- compWitGrHomToFunctor followed by PhiFunctor.map is the identity. -/
theorem map_preimage (φ : categoryToCompWitGr C ⟶ categoryToCompWitGr D) :
    PhiFunctor.map (compWitGrHomToFunctor φ).toCatHom = φ := by
  apply Grothendieck.ext
  case w_base =>
    apply Grothendieck.ext
    case w_base =>
      apply GrothendieckContra'.ext
      case w_base => rfl
      case w_fiber =>
        simp only [eqToHom_refl, Category.comp_id]
        funext ⟨a, b⟩ f; rfl
    case w_fiber =>
      simp only [eqToHom_refl, Category.id_comp]
      apply Groth.IdWitBundle.Hom.ext
      intro x
      simp only [PhiFunctor, functorToCompWitGrHom, functorToIdWitGrHom,
        functorToIdWitBundleHom, compWitGrHomToFunctor, compWitGrHomObjMap,
        Groth.idWitFunctor, Groth.IdWitBundle.pushforwardFunctor,
        Groth.IdWitBundle.pushforward, categoryToCompWitGr, categoryToIdWitGr,
        categoryIdWitBundle]
      exact (φ.base.fiber.witObj_eq x).symm
  case w_fiber =>
    simp only [eqToHom_refl, Category.id_comp]
    apply Groth.CompWitBundle.Hom.ext
    intro ⟨x, y, z, f, g⟩
    simp only [PhiFunctor, functorToCompWitGrHom, functorToCompWitBundleHom,
      compWitGrHomToFunctor, compWitGrHomObjMap, compWitGrHomMorMap,
      Groth.compWitFunctor, Groth.CompWitBundle.pushforwardFunctor,
      Groth.CompWitBundle.pushforward, categoryToCompWitGr, categoryToIdWitGr,
      categoryCompWitBundle]
    -- Use coherence conditions from φ.fiber
    have hSrc := φ.fiber.witSrc_eq ⟨x, y, z, f, g⟩
    have hMid := φ.fiber.witMid_eq ⟨x, y, z, f, g⟩
    have hTgt := φ.fiber.witTgt_eq ⟨x, y, z, f, g⟩
    have hLeft := φ.fiber.witLeft_eq ⟨x, y, z, f, g⟩
    have hRight := φ.fiber.witRight_eq ⟨x, y, z, f, g⟩
    -- Unfold and simplify to get projection equalities
    unfold categoryToCompWitGr categoryCompWitBundle at hSrc hMid hTgt hLeft hRight
    simp only [Groth.compWitFunctor, Groth.CompWitBundle.pushforwardFunctor,
      Groth.CompWitBundle.pushforward, categoryToIdWitGr] at hSrc hMid hTgt hLeft hRight
    -- Prove by destructing the witMap result and substituting
    symm
    rcases hw : φ.fiber.witMap ⟨x, ⟨y, ⟨z, (f, g)⟩⟩⟩ with ⟨x', ⟨y', ⟨z', ⟨f', g'⟩⟩⟩⟩
    -- Rewrite hypotheses using hw to substitute the destructed form
    rw [hw] at hSrc hMid hTgt hLeft hRight
    simp only at hSrc hMid hTgt hLeft hRight
    -- Now hSrc : x' = φ.base.base.base x, etc.
    subst hSrc hMid hTgt
    simp only [heq_eq_eq] at hLeft hRight
    subst hLeft hRight
    rfl

/-- PhiFunctor is fully faithful: the embedding Cat → CompWitGr is an
    equivalence on hom-sets. -/
def phiFunctorFullyFaithful : PhiFunctor.{v, u}.FullyFaithful :=
  Functor.FullyFaithful.mk
    (preimage := fun φ => (compWitGrHomToFunctor φ).toCatHom)
    (map_preimage := map_preimage)
    (preimage_map := fun _ => by rfl)

end FullFaithfulness

/-! ## Naturality and Adjunction Construction

To construct the mathlib Adjunction L ⊣ Φ, we need to prove that unitGr and counitGr
are natural transformations, then package them with the triangle identities.
-/

section Adjunction

universe uObj uMor

/-- The restricted category for the adjunction: CompWitGr where morphisms are
    already at the level that L produces. -/
abbrev AdjCat := Cat.{max uObj uMor, uObj}

/-- The restricted CompWitGr for the adjunction. -/
abbrev AdjGr := Groth.CompWitGr.{uObj, max uObj uMor, uObj, max uObj uMor}

/-- L restricted to the adjunction universe levels. -/
abbrev LAdjFunctor : AdjGr.{uObj, uMor} ⥤ AdjCat.{uObj, uMor} := LFunctor

/-- Φ restricted to the adjunction universe levels. -/
abbrev ΦAdjFunctor : AdjCat.{uObj, uMor} ⥤ AdjGr.{uObj, uMor} := PhiFunctor

/-- Helper lemma for fiber naturality: the CompWitBundle fiber condition. -/
lemma compWitFiber_naturality {X Y : AdjCompWitGr.{uObj, uMor}} (f : X ⟶ Y) :
    (Groth.compWitFunctor.map (PhiFunctor.map (LFunctor.map f)).base).toFunctor.map
      (unitGr X).fiber ≫ (PhiFunctor.map (LFunctor.map f)).fiber =
    (Groth.compWitFunctor.map (unitGr Y).base).toFunctor.map f.fiber ≫ (unitGr Y).fiber := by
  apply Groth.CompWitBundle.Hom.ext
  intro w
  simp only [unitGr, unitCompWitBundleMor, PhiFunctor, LFunctor,
    LMorFunctor, functorToCompWitGrHom, functorToCompWitBundleHom,
    Groth.compWitFunctor, Groth.CompWitBundle.pushforwardFunctor,
    Groth.CompWitBundle.Hom.pushforward, Groth.CompWitGr.bundle]
  rw [Groth.CompWitBundle.Hom.category_comp_witMap,
      Groth.CompWitBundle.Hom.category_comp_witMap]
  simp only [LMorObj, LMorHom_embedAsQuot, Groth.CompWitBundle.pushforward,
    Groth.compWitFunctor]
  -- Extract the coherence equalities from f.fiber in expanded form
  have hSrc : f.base.base.base (X.fiber.witSrc w) =
      Y.fiber.witSrc (f.fiber.witMap w) := (f.fiber.witSrc_eq w).symm
  have hMid : f.base.base.base (X.fiber.witMid w) =
      Y.fiber.witMid (f.fiber.witMap w) := (f.fiber.witMid_eq w).symm
  have hTgt : f.base.base.base (X.fiber.witTgt w) =
      Y.fiber.witTgt (f.fiber.witMap w) := (f.fiber.witTgt_eq w).symm
  -- The nested sigma structure: ⟨src, ⟨mid, ⟨tgt, (left, right)⟩⟩⟩
  -- First level: witSrc
  apply sigma_eq_of_fst_eq_snd_heq hSrc
  -- Second level: witMid
  refine sigma_heq_of_fst_eq_snd_heq (I := Y.base.objType)
    (β := fun src mid => Σ (tgt : Y.base.objType),
      (QuotMor Y src mid × QuotMor Y mid tgt))
    hSrc hMid ?_
  -- Third level: witTgt. Product type depends on (src, mid) pair.
  have hSrcMid : (f.base.base.base (X.fiber.witSrc w),
                  f.base.base.base (X.fiber.witMid w)) =
                 (Y.fiber.witSrc (f.fiber.witMap w),
                  Y.fiber.witMid (f.fiber.witMap w)) := Prod.ext hSrc hMid
  refine sigma_heq_of_fst_eq_snd_heq (α := Y.base.objType × Y.base.objType)
    (I := Y.base.objType)
    (β := fun sm tgt => QuotMor Y sm.1 sm.2 × QuotMor Y sm.2 tgt)
    hSrcMid hTgt ?_
  -- Final level: morphism pair HEq.
  -- The coherence conditions relate pushed morphisms to Y's morphisms.
  -- f.fiber.witLeft_eq w : HEq (Y.fiber.witLeft (f.fiber.witMap w))
  --                            (f.base.base.fiber (...) (X.fiber.witLeft w))
  have hLeft : embedAsQuot Y (f.base.base.fiber (X.fiber.witSrc w, X.fiber.witMid w)
      (X.fiber.witLeft w)) ≍ embedAsQuot Y (Y.fiber.witLeft (f.fiber.witMap w)) :=
    embedAsQuot_heq hSrc hMid (f.fiber.witLeft_eq w).symm
  have hRight : embedAsQuot Y (f.base.base.fiber (X.fiber.witMid w, X.fiber.witTgt w)
      (X.fiber.witRight w)) ≍ embedAsQuot Y (Y.fiber.witRight (f.fiber.witMap w)) :=
    embedAsQuot_heq hMid hTgt (f.fiber.witRight_eq w).symm
  exact prod_mk_heq' hLeft hRight

/-- Unit naturality: for f : X ⟶ Y in CompWitGr,
    η_X ≫ Φ(L(f)) = f ≫ η_Y.

    This says that embedding generators then mapping through the free category
    commutes with mapping through the original structure. -/
theorem unitGr_naturality (X Y : AdjCompWitGr.{uObj, uMor}) (f : X ⟶ Y) :
    unitGr X ≫ PhiFunctor.map (LFunctor.map f) = f ≫ unitGr Y := by
  -- Morphisms in CompWitGr are Grothendieck morphisms with base and fiber
  refine Grothendieck.ext _ _ ?hbase ?hfiber
  case hbase =>
    -- Base is IdWitGr morphism, also Grothendieck
    refine Grothendieck.ext _ _ ?_ ?_
    case _ =>
      -- QuiverGr base: both sides reduce to f.base.base
      simp only [Grothendieck.comp_base]
      simp only [unitGr, unitIdWitGrMor, unitQuiverMor, PhiFunctor, LFunctor,
        LMorFunctor, functorToCompWitGrHom, functorToIdWitGrHom, functorToQuiverHom]
      -- Use extensionality for GrothendieckContra' morphisms
      apply GrothendieckContra'.ext
      case w_base =>
        rfl
      case w_fiber =>
        funext ⟨a, b⟩ g
        -- Both sides embed a generator morphism, then map through f
        simp only [GrothendieckContra'.cat_comp_fiber, eqToHom_refl, Category.comp_id]
        simp only [embedAsQuot, LMorHom, mapFreeMor, FreeMor.var]
        rfl
    case _ =>
      -- IdWitBundle fiber case
      simp only [eqToHom_refl, Category.id_comp]
      apply Groth.IdWitBundle.Hom.ext
      intro x
      simp only [Grothendieck.comp_fiber, Grothendieck.comp_base]
      simp only [unitGr, unitIdWitGrMor, unitIdWitBundleMor, PhiFunctor, LFunctor,
        LMorFunctor, functorToCompWitGrHom, functorToIdWitGrHom, functorToIdWitBundleHom,
        Groth.idWitFunctor, Groth.IdWitBundle.pushforwardFunctor, Groth.IdWitBundle.pushforward,
        Groth.IdWitBundle.Hom.pushforward, Groth.CompWitGr.idBundle]
      simp only [CategoryStruct.comp, Groth.IdWitBundle.instCategory,
        Groth.IdWitBundle.Hom.comp, Groth.CompWitGr.idWitGr]
      -- LHS: f.base.base.base (X.base.fiber.witObj x)
      -- RHS: Y.base.fiber.witObj (f.base.fiber.witMap x)
      -- f.base.fiber.witObj_eq gives the pushforward-based equality
      simp only [LMorObj]
      exact (f.base.fiber.witObj_eq x).symm
  case hfiber =>
    -- CompWitBundle fiber: composition witnesses
    simp only [Grothendieck.comp_fiber, Grothendieck.comp_base]
    simp only [eqToHom_refl, Category.id_comp]
    exact compWitFiber_naturality f

/-- Helper: naturality of evaluation for free morphisms.
    Inducting on validity gives proper typing for composition cases. -/
theorem evalFreeMor_naturality (C D : AdjCat.{uObj, uMor}) (f : C ⟶ D)
    {a b : (ΦC C).objType} (m : FreeMor (ΦC C) a b) :
    f.toFunctor.map (evalFreeMor C m) =
      evalFreeMor D ⟨mapFreeMorRaw (PhiFunctor.map f) m.1,
        mapFreeMorRaw_valid (PhiFunctor.map f) m.2⟩ := by
  -- Induct on validity proof which has proper endpoint typing
  obtain ⟨raw, valid⟩ := m
  induction valid with
  | var m =>
    simp only [evalFreeMor, evalFreeMorRaw, mapFreeMorRaw]
    simp only [PhiFunctor, functorToCompWitGrHom, functorToIdWitGrHom,
               functorToQuiverHom]
  | id a' =>
    simp only [evalFreeMor, evalFreeMorRaw, mapFreeMorRaw]
    simp only [PhiFunctor, functorToCompWitGrHom, functorToIdWitGrHom,
               functorToQuiverHom, LMorObj]
    exact f.toFunctor.map_id a'
  | comp hg hf ihg ihf =>
    simp only [evalFreeMor, evalFreeMorRaw, mapFreeMorRaw, f.toFunctor.map_comp]
    simp only [evalFreeMor] at ihg ihf
    exact congrArg₂ (· ≫ ·) ihf ihg

/-- Counit naturality: for f : C ⥤ D between categories,
    ε_C ≫ f = L(Φ(f)) ≫ ε_D.

    This says that evaluating free morphisms then applying f
    equals mapping through L(Φ(f)) then evaluating. -/
theorem counitGr_naturality (C D : AdjCat.{uObj, uMor}) (f : C ⟶ D) :
    counitGr C ≫ f = LFunctor.map (PhiFunctor.map f) ≫ counitGr D := by
  -- Both sides are functors L(Φ(C)) ⥤ D
  -- Use functor extensionality: check on objects and morphisms
  apply CategoryTheory.Functor.ext
  case h_obj =>
    intro a
    -- Objects: both reduce to f.obj a
    simp only [counitGr, LFunctor, categoryToCompWitGr]
    rfl
  case h_map =>
    intro a b g
    -- Morphisms: both evaluate and apply f.map
    -- LHS: f.map (counitGr C).map g = f.map (evalQuotMor C g)
    -- RHS: (counitGr D).map (LMorHom (PhiFunctor.map f) g) = evalQuotMor D (...)
    simp only [counitGr, LFunctor, LMorFunctor]
    -- Induct on the quotient morphism g : QuotMor (categoryToCompWitGr C) a b
    induction g using Quotient.ind with | _ g' =>
    -- g' : FreeMor (categoryToCompWitGr C) a b
    -- First handle the eqToHom terms
    simp only [eqToHom_refl, Category.id_comp, Category.comp_id]
    -- Unfold the functor compositions in Cat
    -- (F ≫ G).map f = G.map (F.map f) definitionally
    change f.map ((counitGr C).map ⟦g'⟧) =
      (counitGr D).map ((LMorFunctor (PhiFunctor.map f)).map ⟦g'⟧)
    -- Expand counitGr.map and LMorFunctor.map
    simp only [counitGr, LMorFunctor, evalQuotMor, LMorHom, mapFreeMor]
    -- RHS simplifies via Quotient.lift_mk
    simp only [Quotient.lift_mk]
    -- Goal: f.map (evalFreeMor C g') = Quotient.lift (evalFreeMor D) ⋯ ⟦...⟧
    -- Use erw to handle Quotient.mk' vs Quotient.mk definitional difference
    erw [Quotient.lift_mk]
    -- Goal: f.map (evalFreeMor C g') = evalFreeMor D ⟨mapFreeMorRaw ... g'.val, ⋯⟩
    exact evalFreeMor_naturality C D f g'

/-- The unit as a natural transformation: 𝟭 AdjGr ⟶ LFunctor ⋙ PhiFunctor. -/
def unitNatTrans : 𝟭 AdjGr.{uObj, uMor} ⟶ LAdjFunctor ⋙ ΦAdjFunctor where
  app := unitGr
  naturality := fun X Y f => (unitGr_naturality X Y f).symm

/-- The counit as a natural transformation: PhiFunctor ⋙ LFunctor ⟶ 𝟭 AdjCat. -/
def counitNatTrans : ΦAdjFunctor ⋙ LAdjFunctor ⟶ 𝟭 AdjCat.{uObj, uMor} where
  app := counitGr
  naturality := fun C D f => (counitGr_naturality C D f).symm

/-- Core adjunction data with unit, counit, and triangle identities. -/
def coreUnitCounit : Adjunction.CoreUnitCounit LAdjFunctor ΦAdjFunctor where
  unit := unitNatTrans
  counit := counitNatTrans
  left_triangle := by
    ext X
    simp only [NatTrans.comp_app, Functor.comp_obj, Functor.whiskerRight_app,
      Functor.id_obj, Functor.associator_hom_app, Functor.whiskerLeft_app]
    exact leftTriangle X
  right_triangle := by
    ext C
    simp only [NatTrans.comp_app, Functor.comp_obj, Functor.whiskerLeft_app,
      Functor.id_obj, Functor.associator_inv_app, Functor.whiskerRight_app]
    exact rightTriangle C

/-- The L ⊣ Φ adjunction between CompWitGr and Cat. -/
def grAdjunction : LAdjFunctor ⊣ ΦAdjFunctor :=
  Adjunction.mkOfUnitCounit coreUnitCounit

/-- ΦAdjFunctor is full. -/
instance phiAdjFunctor_full : ΦAdjFunctor.Full :=
  phiFunctorFullyFaithful.full

/-- ΦAdjFunctor is faithful. -/
instance phiAdjFunctor_faithful : ΦAdjFunctor.Faithful :=
  phiFunctorFullyFaithful.faithful

/-- Cat is a reflective subcategory of CompWitGr via the embedding Φ. -/
instance phiReflective : Reflective ΦAdjFunctor where
  L := LAdjFunctor
  adj := grAdjunction

end Adjunction

end GrAdjunction

end PLang

end GebLean
