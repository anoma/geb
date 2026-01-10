import GebLean.Utilities.Category

/-!
# Double Category Theory Utilities

Strict double categories as categories internal to Cat.

## Main definitions

### Basic type families

* `VertHomSet`: Vertical morphism type family
* `HorHomSet`: Horizontal morphism type family
* `SquareSet`: Square (2-cell) type family

### Operations

* `SquareVCompStruct`: Vertical composition of squares
* `SquareHCompStruct`: Horizontal composition of squares
* `SquareVertIdStruct`: Vertical identity squares
* `SquareHorIdStruct`: Horizontal identity squares
* `SquareOps`: All square operations bundled
* `DoubleCategoryOps`: All operations (vertical/horizontal categories + squares)

### Laws

* `SquareVAssocLaw`: Associativity of vertical square composition
* `SquareHAssocLaw`: Associativity of horizontal square composition
* `SquareVIdLaws`: Identity laws for vertical square composition
* `SquareHIdLaws`: Identity laws for horizontal square composition
* `InterchangeLaw`: Coherence between horizontal and vertical composition
* `DoubleCategoryLaws`: All laws bundled

### Data

* `DoubleCategoryData`: Operations and laws for a strict double category
* `DoubleCategoryData.vertCategoryData`: Vertical morphisms form a category
* `DoubleCategoryData.horCategoryData`: Horizontal morphisms form a category
-/

namespace GebLean

open CategoryTheory

universe u vMor hMor sq u₃ vMor₃ hMor₃ sq₃

/-- Vertical morphism type family.

In a double category, vertical morphisms go "up and down" in diagrams.
They form a category structure with their own composition and identities. -/
abbrev VertHomSet (Obj : Type u) := Obj → Obj → Sort vMor

/-- Horizontal morphism type family.

In a double category, horizontal morphisms go "left to right" in diagrams.
They form a category structure with their own composition and identities. -/
abbrev HorHomSet (Obj : Type u) := Obj → Obj → Sort hMor

/-- Square (2-cell) type family.

A square fills a boundary of four morphisms:
```
  A ──h₁──▶ B
  │         │
  v₁        v₂
  ▼         ▼
  C ──h₂──▶ D
```
The type `SquareSet vhs hhs A B C D v₁ v₂ h₁ h₂` represents the squares
filling boundaries with left vertical v₁, right vertical v₂,
top horizontal h₁, and bottom horizontal h₂. -/
abbrev SquareSet {Obj : Type u}
    (vhs : VertHomSet Obj)
    (hhs : HorHomSet Obj) :=
  ∀ {A B C D : Obj}, vhs A C → vhs B D → hhs A B → hhs C D → Sort sq

section SquareOperations

variable {Obj : Type u}
variable (vhs : VertHomSet Obj) (hhs : HorHomSet Obj)
variable (sqs : SquareSet vhs hhs)
variable (vcomp : CompositionalStruct vhs) (hcomp : CompositionalStruct hhs)

/-- Vertical composition of squares.

Given two squares α and β that share a horizontal edge:
```
  A ──h₁──▶ B
  │         │
  v₁   α    v₂
  ▼         ▼
  C ──h₂──▶ D
  │         │
  v₁'  β    v₂'
  ▼         ▼
  E ──h₃──▶ F
```
their vertical composite `α ⬝ᵥ β` fills:
```
  A ────h₁────▶ B
  │             │
  v₁ ≫ v₁'     v₂ ≫ v₂'
  ▼             ▼
  E ────h₃────▶ F
```
-/
abbrev SquareVCompStruct :=
  ∀ {A B C D E F : Obj}
    {v₁ : vhs A C} {v₂ : vhs B D} {v₁' : vhs C E} {v₂' : vhs D F}
    {h₁ : hhs A B} {h₂ : hhs C D} {h₃ : hhs E F},
    sqs v₁ v₂ h₁ h₂ → sqs v₁' v₂' h₂ h₃ → sqs (vcomp v₁ v₁') (vcomp v₂ v₂') h₁ h₃

/-- Horizontal composition of squares.

Given two squares α and β that share a vertical edge:
```
  A ──h₁──▶ B ──h₂──▶ C
  │         │         │
  v₁   α    v₂   β    v₃
  ▼         ▼         ▼
  D ──h₃──▶ E ──h₄──▶ F
```
their horizontal composite `α ⬝ₕ β` fills:
```
  A ───h₁ ≫ h₂───▶ C
  │                │
  v₁               v₃
  ▼                ▼
  D ───h₃ ≫ h₄───▶ F
```
-/
abbrev SquareHCompStruct :=
  ∀ {A B C D E F : Obj}
    {v₁ : vhs A D} {v₂ : vhs B E} {v₃ : vhs C F}
    {h₁ : hhs A B} {h₂ : hhs B C} {h₃ : hhs D E} {h₄ : hhs E F},
    sqs v₁ v₂ h₁ h₃ → sqs v₂ v₃ h₂ h₄ → sqs v₁ v₃ (hcomp h₁ h₂) (hcomp h₃ h₄)

variable (vid : IdentityStruct vhs) (hid : IdentityStruct hhs)

/-- Vertical identity squares.

For each horizontal morphism h : A →ₕ B, there is an identity square:
```
  A ──h──▶ B
  ‖        ‖
  1_A      1_B
  ‖        ‖
  A ──h──▶ B
```
This is the identity for vertical composition of squares. -/
abbrev SquareVertIdStruct :=
  ∀ {A B : Obj} (h : hhs A B), sqs (vid A) (vid B) h h

/-- Horizontal identity squares.

For each vertical morphism v : A →ᵥ C, there is an identity square:
```
  A ═══1_A═══▶ A
  │            │
  v            v
  ▼            ▼
  C ═══1_C═══▶ C
```
This is the identity for horizontal composition of squares. -/
abbrev SquareHorIdStruct :=
  ∀ {A C : Obj} (v : vhs A C), sqs v v (hid A) (hid C)

end SquareOperations

/-- All operations for a strict double category.

This bundles:
- Category operations for vertical morphisms
- Category operations for horizontal morphisms
- Square operations (compositions and identities)

The square operations depend on the morphism operations (for composition of
boundary morphisms). -/
structure DoubleCategoryOps (Obj : Type u)
    (vhs : VertHomSet Obj) (hhs : HorHomSet Obj) (sqs : SquareSet vhs hhs) where
  /-- Vertical composition of morphisms -/
  vComp : CompositionalStruct vhs
  /-- Horizontal composition of morphisms -/
  hComp : CompositionalStruct hhs
  /-- Vertical identity morphisms -/
  vId : IdentityStruct vhs
  /-- Horizontal identity morphisms -/
  hId : IdentityStruct hhs
  /-- Vertical composition of squares -/
  sqVComp : SquareVCompStruct vhs hhs sqs vComp
  /-- Horizontal composition of squares -/
  sqHComp : SquareHCompStruct vhs hhs sqs hComp
  /-- Vertical identity squares -/
  sqVertId : SquareVertIdStruct vhs hhs sqs vId
  /-- Horizontal identity squares -/
  sqHorId : SquareHorIdStruct vhs hhs sqs hId

namespace DoubleCategoryOps

variable {Obj : Type u} {vhs : VertHomSet Obj} {hhs : HorHomSet Obj}
variable {sqs : SquareSet vhs hhs}
variable (ops : DoubleCategoryOps Obj vhs hhs sqs)

/-- Vertical category operations extracted from double category operations -/
def vertCategoryOps : CategoryOps vhs where
  comp := ops.vComp
  id := ops.vId

/-- Horizontal category operations extracted from double category operations -/
def horCategoryOps : CategoryOps hhs where
  comp := ops.hComp
  id := ops.hId

end DoubleCategoryOps

section SquareLaws

variable {Obj : Type u} {vhs : VertHomSet Obj} {hhs : HorHomSet Obj}
variable {sqs : SquareSet vhs hhs}
variable (ops : DoubleCategoryOps Obj vhs hhs sqs)

/-- Associativity of vertical composition of squares.

For three vertically composable squares α, β, γ:
```
  (α ⬝ᵥ β) ⬝ᵥ γ = α ⬝ᵥ (β ⬝ᵥ γ)
```
-/
abbrev SquareVAssocLaw : Prop :=
  ∀ {A B C D E F G H : Obj}
    {v₁ : vhs A C} {v₂ : vhs B D}
    {v₁' : vhs C E} {v₂' : vhs D F}
    {v₁'' : vhs E G} {v₂'' : vhs F H}
    {h₁ : hhs A B} {h₂ : hhs C D} {h₃ : hhs E F} {h₄ : hhs G H}
    (α : sqs v₁ v₂ h₁ h₂) (β : sqs v₁' v₂' h₂ h₃) (γ : sqs v₁'' v₂'' h₃ h₄),
    HEq (ops.sqVComp (ops.sqVComp α β) γ) (ops.sqVComp α (ops.sqVComp β γ))

/-- Associativity of horizontal composition of squares.

For three horizontally composable squares α, β, γ:
```
  (α ⬝ₕ β) ⬝ₕ γ = α ⬝ₕ (β ⬝ₕ γ)
```
-/
abbrev SquareHAssocLaw : Prop :=
  ∀ {A B C D E F G H : Obj}
    {v₁ : vhs A E} {v₂ : vhs B F} {v₃ : vhs C G} {v₄ : vhs D H}
    {h₁ : hhs A B} {h₂ : hhs B C} {h₃ : hhs C D}
    {h₅ : hhs E F} {h₆ : hhs F G} {h₇ : hhs G H}
    (α : sqs v₁ v₂ h₁ h₅) (β : sqs v₂ v₃ h₂ h₆) (γ : sqs v₃ v₄ h₃ h₇),
    HEq (ops.sqHComp (ops.sqHComp α β) γ) (ops.sqHComp α (ops.sqHComp β γ))

/-- Left identity law for vertical composition of squares.

Composing with the vertical identity square on top gives the original:
```
  id_h ⬝ᵥ α = α
```
-/
abbrev SquareVIdCompLaw : Prop :=
  ∀ {A B C D : Obj} {v₁ : vhs A C} {v₂ : vhs B D} {h₁ : hhs A B} {h₂ : hhs C D}
    (α : sqs v₁ v₂ h₁ h₂),
    HEq (ops.sqVComp (ops.sqVertId h₁) α) α

/-- Right identity law for vertical composition of squares.

Composing with the vertical identity square on bottom gives the original:
```
  α ⬝ᵥ id_h = α
```
-/
abbrev SquareVCompIdLaw : Prop :=
  ∀ {A B C D : Obj} {v₁ : vhs A C} {v₂ : vhs B D} {h₁ : hhs A B} {h₂ : hhs C D}
    (α : sqs v₁ v₂ h₁ h₂),
    HEq (ops.sqVComp α (ops.sqVertId h₂)) α

/-- Left identity law for horizontal composition of squares.

Composing with the horizontal identity square on left gives the original:
```
  1_v ⬝ₕ α = α
```
-/
abbrev SquareHIdCompLaw : Prop :=
  ∀ {A B C D : Obj} {v₁ : vhs A C} {v₂ : vhs B D} {h₁ : hhs A B} {h₂ : hhs C D}
    (α : sqs v₁ v₂ h₁ h₂),
    HEq (ops.sqHComp (ops.sqHorId v₁) α) α

/-- Right identity law for horizontal composition of squares.

Composing with the horizontal identity square on right gives the original:
```
  α ⬝ₕ 1_v = α
```
-/
abbrev SquareHCompIdLaw : Prop :=
  ∀ {A B C D : Obj} {v₁ : vhs A C} {v₂ : vhs B D} {h₁ : hhs A B} {h₂ : hhs C D}
    (α : sqs v₁ v₂ h₁ h₂),
    HEq (ops.sqHComp α (ops.sqHorId v₂)) α

/-- The interchange law.

For a 2x2 grid of squares:
```
  α  | α'
  ───┼────
  β  | β'
```
the two ways to compose are equal:
```
  (α ⬝ₕ α') ⬝ᵥ (β ⬝ₕ β') = (α ⬝ᵥ β) ⬝ₕ (α' ⬝ᵥ β')
```

This is the coherence condition for double categories. -/
abbrev InterchangeLaw : Prop :=
  ∀ {A B C D E F G H I : Obj}
    {v₁ : vhs A D} {v₂ : vhs B E} {v₃ : vhs C F}
    {v₁' : vhs D G} {v₂' : vhs E H} {v₃' : vhs F I}
    {h₁ : hhs A B} {h₂ : hhs B C}
    {h₃ : hhs D E} {h₄ : hhs E F}
    {h₅ : hhs G H} {h₆ : hhs H I}
    (α : sqs v₁ v₂ h₁ h₃) (α' : sqs v₂ v₃ h₂ h₄)
    (β : sqs v₁' v₂' h₃ h₅) (β' : sqs v₂' v₃' h₄ h₆),
    ops.sqVComp (ops.sqHComp α α') (ops.sqHComp β β') =
      ops.sqHComp (ops.sqVComp α β) (ops.sqVComp α' β')

/-- Vertical identity squares compose to vertical identity.

For composable vertical morphisms v : A →ᵥ C and v' : C →ᵥ E:
```
  1ᵥ(v) ⬝ᵥ 1ᵥ(v') = 1ᵥ(v ≫ v')
```
-/
abbrev VertIdVCompLaw : Prop :=
  ∀ {A C E : Obj} (v : vhs A C) (v' : vhs C E),
    ops.sqVComp (ops.sqHorId v) (ops.sqHorId v') =
      ops.sqHorId (ops.vComp v v')

/-- Horizontal identity squares compose to horizontal identity.

For composable horizontal morphisms h : A →ₕ B and h' : B →ₕ C:
```
  idₕ(h) ⬝ₕ idₕ(h') = idₕ(h ≫ h')
```
-/
abbrev HorIdHCompLaw : Prop :=
  ∀ {A B C : Obj} (h : hhs A B) (h' : hhs B C),
    ops.sqHComp (ops.sqVertId h) (ops.sqVertId h') =
      ops.sqVertId (ops.hComp h h')

/-- The identity on identity square.

At any object A, the vertical identity square on the horizontal identity
equals the horizontal identity square on the vertical identity:
```
  1ᵥ(idₕ A) = idₕ(1ᵥ A)
```
-/
abbrev IdOnIdLaw : Prop :=
  ∀ (A : Obj), ops.sqHorId (ops.vId A) = ops.sqVertId (ops.hId A)

end SquareLaws

/-- All laws for square operations in a double category. -/
structure SquareLaws {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs) : Prop where
  /-- Associativity of vertical square composition -/
  sqVAssoc : SquareVAssocLaw ops
  /-- Associativity of horizontal square composition -/
  sqHAssoc : SquareHAssocLaw ops
  /-- Left identity for vertical square composition -/
  sqVIdComp : SquareVIdCompLaw ops
  /-- Right identity for vertical square composition -/
  sqVCompId : SquareVCompIdLaw ops
  /-- Left identity for horizontal square composition -/
  sqHIdComp : SquareHIdCompLaw ops
  /-- Right identity for horizontal square composition -/
  sqHCompId : SquareHCompIdLaw ops
  /-- The interchange law -/
  interchange : InterchangeLaw ops
  /-- Vertical identity squares compose -/
  vertIdVComp : VertIdVCompLaw ops
  /-- Horizontal identity squares compose -/
  horIdHComp : HorIdHCompLaw ops
  /-- Identity on identity -/
  idOnId : IdOnIdLaw ops

/-- All laws for a strict double category.

This bundles:
- Category laws for vertical morphisms
- Category laws for horizontal morphisms
- Square laws (associativity, identity, interchange) -/
structure DoubleCategoryLaws {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs) : Prop where
  /-- Vertical category laws -/
  vertLaws : CategoryLaws vhs ops.vertCategoryOps
  /-- Horizontal category laws -/
  horLaws : CategoryLaws hhs ops.horCategoryOps
  /-- Square laws -/
  sqLaws : SquareLaws ops

/-- Data for a strict double category.

This bundles all operations and laws for a strict double category. -/
structure DoubleCategoryData (Obj : Type u)
    (vhs : VertHomSet Obj) (hhs : HorHomSet Obj)
    (sqs : SquareSet vhs hhs) extends DoubleCategoryOps Obj vhs hhs sqs where
  /-- All laws hold -/
  laws : DoubleCategoryLaws toDoubleCategoryOps

namespace DoubleCategoryData

variable {Obj : Type u} {vhs : VertHomSet Obj} {hhs : HorHomSet Obj}
variable {sqs : SquareSet vhs hhs}
variable (data : DoubleCategoryData Obj vhs hhs sqs)

/-- Extract the vertical category data from a double category. -/
def vertCategoryData : CategoryData Obj vhs where
  comp := data.vComp
  id := data.vId
  laws := data.laws.vertLaws

/-- Extract the horizontal category data from a double category. -/
def horCategoryData : CategoryData Obj hhs where
  comp := data.hComp
  id := data.hId
  laws := data.laws.horLaws

end DoubleCategoryData

/-- Build a mathlib `Category` instance for vertical morphisms.

This requires the vertical hom-set to produce `Type` (not `Prop`). -/
def VertCategoryOfDoubleCategoryData {Obj : Type u}
    {vhs : Obj → Obj → Type vMor} {hhs : HorHomSet Obj}
    {sqs : SquareSet vhs hhs}
    (data : DoubleCategoryData Obj vhs hhs sqs) : Category.{vMor, u} Obj :=
  CategoryOfData data.vertCategoryData

/-- Build a mathlib `Category` instance for horizontal morphisms.

This requires the horizontal hom-set to produce `Type` (not `Prop`). -/
def HorCategoryOfDoubleCategoryData {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : Obj → Obj → Type hMor}
    {sqs : SquareSet vhs hhs}
    (data : DoubleCategoryData Obj vhs hhs sqs) : Category.{hMor, u} Obj :=
  CategoryOfData data.horCategoryData

/-! ## Double Functors

Strict double functors preserve all structure of double categories. -/

universe u₁ vMor₁ hMor₁ sq₁ u₂ vMor₂ hMor₂ sq₂ u₄ vMor₄ hMor₄ sq₄

/-- Operations for a strict double functor.

Bundles the four mapping components: objects, vertical morphisms,
horizontal morphisms, and squares.

A double functor F : D → E maps:
- Objects of D to objects of E
- Vertical morphisms v : A →ᵥ B to F(v) : F(A) →ᵥ F(B)
- Horizontal morphisms h : A →ₕ B to F(h) : F(A) →ₕ F(B)
- Squares α to F(α) with corresponding boundary -/
structure DoubleFunctorOps
    {Obj₁ : Type u₁} (vhs₁ : VertHomSet Obj₁) (hhs₁ : HorHomSet Obj₁)
    (sqs₁ : SquareSet vhs₁ hhs₁)
    {Obj₂ : Type u₂} (vhs₂ : VertHomSet Obj₂) (hhs₂ : HorHomSet Obj₂)
    (sqs₂ : SquareSet vhs₂ hhs₂) where
  /-- Object map -/
  objMap : Obj₁ → Obj₂
  /-- Vertical morphism map -/
  vertMap : ∀ {A B : Obj₁}, vhs₁ A B → vhs₂ (objMap A) (objMap B)
  /-- Horizontal morphism map -/
  horMap : ∀ {A B : Obj₁}, hhs₁ A B → hhs₂ (objMap A) (objMap B)
  /-- Square map -/
  sqMap : ∀ {A B C D : Obj₁} {v₁ : vhs₁ A C} {v₂ : vhs₁ B D}
    {h₁ : hhs₁ A B} {h₂ : hhs₁ C D},
    sqs₁ v₁ v₂ h₁ h₂ → sqs₂ (vertMap v₁) (vertMap v₂) (horMap h₁) (horMap h₂)

/-- Law that the double functor preserves vertical identity morphisms. -/
abbrev DFPreservesVId {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (fops : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂) : Prop :=
  ∀ (A : Obj₁), fops.vertMap (ops₁.vId A) = ops₂.vId (fops.objMap A)

/-- Law that the double functor preserves horizontal identity morphisms. -/
abbrev DFPreservesHId {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (fops : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂) : Prop :=
  ∀ (A : Obj₁), fops.horMap (ops₁.hId A) = ops₂.hId (fops.objMap A)

/-- Law that the double functor preserves vertical composition of morphisms. -/
abbrev DFPreservesVComp {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (fops : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂) : Prop :=
  ∀ {A B C : Obj₁} (v : vhs₁ A B) (v' : vhs₁ B C),
    fops.vertMap (ops₁.vComp v v') = ops₂.vComp (fops.vertMap v) (fops.vertMap v')

/-- Law that the double functor preserves horizontal composition of morphisms. -/
abbrev DFPreservesHComp {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (fops : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂) : Prop :=
  ∀ {A B C : Obj₁} (h : hhs₁ A B) (h' : hhs₁ B C),
    fops.horMap (ops₁.hComp h h') = ops₂.hComp (fops.horMap h) (fops.horMap h')

/-- Law that the double functor preserves vertical identity squares. -/
abbrev DFPreservesSqVertId {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (fops : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂) : Prop :=
  ∀ {A B : Obj₁} (h : hhs₁ A B),
    HEq (fops.sqMap (ops₁.sqVertId h)) (ops₂.sqVertId (fops.horMap h))

/-- Law that the double functor preserves horizontal identity squares. -/
abbrev DFPreservesSqHorId {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (fops : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂) : Prop :=
  ∀ {A C : Obj₁} (v : vhs₁ A C),
    HEq (fops.sqMap (ops₁.sqHorId v)) (ops₂.sqHorId (fops.vertMap v))

/-- Law that the double functor preserves vertical composition of squares. -/
abbrev DFPreservesSqVComp {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (fops : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂) : Prop :=
  ∀ {A B C D E F : Obj₁}
    {v₁ : vhs₁ A C} {v₂ : vhs₁ B D} {v₁' : vhs₁ C E} {v₂' : vhs₁ D F}
    {h₁ : hhs₁ A B} {h₂ : hhs₁ C D} {h₃ : hhs₁ E F}
    (α : sqs₁ v₁ v₂ h₁ h₂) (β : sqs₁ v₁' v₂' h₂ h₃),
    HEq (fops.sqMap (ops₁.sqVComp α β))
      (ops₂.sqVComp (fops.sqMap α) (fops.sqMap β))

/-- Law that the double functor preserves horizontal composition of squares. -/
abbrev DFPreservesSqHComp {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (fops : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂) : Prop :=
  ∀ {A B C D E F : Obj₁}
    {v₁ : vhs₁ A D} {v₂ : vhs₁ B E} {v₃ : vhs₁ C F}
    {h₁ : hhs₁ A B} {h₂ : hhs₁ B C} {h₃ : hhs₁ D E} {h₄ : hhs₁ E F}
    (α : sqs₁ v₁ v₂ h₁ h₃) (β : sqs₁ v₂ v₃ h₂ h₄),
    HEq (fops.sqMap (ops₁.sqHComp α β))
      (ops₂.sqHComp (fops.sqMap α) (fops.sqMap β))

/-- Laws for a strict double functor.

Bundles all preservation laws for morphisms and squares. -/
structure DoubleFunctorLaws {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (fops : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂) : Prop where
  /-- Preserves vertical identity morphisms -/
  map_vId : DFPreservesVId ops₁ ops₂ fops
  /-- Preserves horizontal identity morphisms -/
  map_hId : DFPreservesHId ops₁ ops₂ fops
  /-- Preserves vertical composition of morphisms -/
  map_vComp : DFPreservesVComp ops₁ ops₂ fops
  /-- Preserves horizontal composition of morphisms -/
  map_hComp : DFPreservesHComp ops₁ ops₂ fops
  /-- Preserves vertical identity squares -/
  map_sqVertId : DFPreservesSqVertId ops₁ ops₂ fops
  /-- Preserves horizontal identity squares -/
  map_sqHorId : DFPreservesSqHorId ops₁ ops₂ fops
  /-- Preserves vertical composition of squares -/
  map_sqVComp : DFPreservesSqVComp ops₁ ops₂ fops
  /-- Preserves horizontal composition of squares -/
  map_sqHComp : DFPreservesSqHComp ops₁ ops₂ fops

/-- Data for a strict double functor.

Bundles the operations and laws for a double functor between double categories.
This follows the pattern of `FunctorData` in Category.lean. -/
structure DoubleFunctorData {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (data₁ : DoubleCategoryData Obj₁ vhs₁ hhs₁ sqs₁)
    (data₂ : DoubleCategoryData Obj₂ vhs₂ hhs₂ sqs₂)
    extends DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂ where
  /-- Double functor laws -/
  laws : DoubleFunctorLaws data₁.toDoubleCategoryOps data₂.toDoubleCategoryOps
    toDoubleFunctorOps

namespace DoubleFunctorData

variable {Obj₁ : Type u₁} {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁}
variable {sqs₁ : SquareSet vhs₁ hhs₁}
variable {Obj₂ : Type u₂} {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂}
variable {sqs₂ : SquareSet vhs₂ hhs₂}
variable {data₁ : DoubleCategoryData Obj₁ vhs₁ hhs₁ sqs₁}
variable {data₂ : DoubleCategoryData Obj₂ vhs₂ hhs₂ sqs₂}

/-- Extract the vertical functor data from a double functor. -/
def vertFunctorData (F : DoubleFunctorData data₁ data₂) :
    FunctorData data₁.vertCategoryData data₂.vertCategoryData where
  obj := F.objMap
  map := F.vertMap
  laws := {
    map_id := F.laws.map_vId
    map_comp := F.laws.map_vComp
  }

/-- Extract the horizontal functor data from a double functor. -/
def horFunctorData (F : DoubleFunctorData data₁ data₂) :
    FunctorData data₁.horCategoryData data₂.horCategoryData where
  obj := F.objMap
  map := F.horMap
  laws := {
    map_id := F.laws.map_hId
    map_comp := F.laws.map_hComp
  }

end DoubleFunctorData

/-! ## Vertical Natural Transformations

A vertical transformation between double functors assigns to each object a
vertical morphism, with squares filling the naturality diagrams for horizontal
morphisms.

Given double functors F, G : D → E, a vertical transformation τ : F ⟹ᵥ G
consists of:
- For each object A : D, a vertical morphism τ_A : F(A) →ᵥ G(A)
- For each horizontal morphism h : A →ₕ B, a square:
  ```
  F(A) ──F(h)──▶ F(B)
   │              │
  τ_A            τ_B
   ▼              ▼
  G(A) ──G(h)──▶ G(B)
  ```
-/

/-- Operations for a vertical transformation between double functors. -/
@[ext]
structure VertTransOps {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂) where
  /-- Component vertical morphisms -/
  app : ∀ (A : Obj₁), vhs₂ (F.objMap A) (G.objMap A)
  /-- Naturality squares for horizontal morphisms -/
  natSquare : ∀ {A B : Obj₁} (h : hhs₁ A B),
    sqs₂ (app A) (app B) (F.horMap h) (G.horMap h)

/-- Naturality condition: components compose with vertical morphism maps.

For each vertical morphism v : A →ᵥ B in D:
  τ_A ≫ G(v) = F(v) ≫ τ_B
-/
abbrev VertTransNaturality {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (τ : VertTransOps F G) : Prop :=
  ∀ {A B : Obj₁} (v : vhs₁ A B),
    ops₂.vComp (τ.app A) (G.vertMap v) = ops₂.vComp (F.vertMap v) (τ.app B)

/-- Square naturality condition: naturality squares commute with functor maps.

For a transformation σ : K ⟹ᵥ L and any square α with horizontal boundaries
h₁ (top) and h₂ (bottom), we have:
  K(α) ⬝ᵥ σ.natSquare(h₂) ≅ σ.natSquare(h₁) ⬝ᵥ L(α)
(up to HEq because the vertical boundaries differ by morphism naturality).

This is a higher coherence condition needed for the interchange law. -/
abbrev VertTransSquareNaturality {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    {K L : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (σ : VertTransOps K L) : Prop :=
  ∀ {A B C D : Obj₁} {v₁ : vhs₁ A C} {v₂ : vhs₁ B D}
    {h₁ : hhs₁ A B} {h₂ : hhs₁ C D}
    (α : sqs₁ v₁ v₂ h₁ h₂),
    HEq (ops₂.sqVComp (K.sqMap α) (σ.natSquare h₂))
        (ops₂.sqVComp (σ.natSquare h₁) (L.sqMap α))

/-- Coherence: naturality squares compose with horizontal identity squares.

For each object A, the naturality square of the horizontal identity h = id_A
should equal the horizontal identity square on τ_A (up to HEq because
functor laws change the boundary types). -/
abbrev VertTransIdCoherence {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (_flaws : DoubleFunctorLaws ops₁ ops₂ F)
    (_glaws : DoubleFunctorLaws ops₁ ops₂ G)
    (τ : VertTransOps F G) : Prop :=
  ∀ (A : Obj₁), HEq (τ.natSquare (ops₁.hId A)) (ops₂.sqHorId (τ.app A))

/-- Coherence: naturality squares compose horizontally.

For composable horizontal morphisms h : A →ₕ B and h' : B →ₕ C:
  natSquare(h ≫ h') = natSquare(h) ⬝ₕ natSquare(h')
(up to HEq because functor laws change the boundary types).
-/
abbrev VertTransCompCoherence {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (_flaws : DoubleFunctorLaws ops₁ ops₂ F)
    (_glaws : DoubleFunctorLaws ops₁ ops₂ G)
    (τ : VertTransOps F G) : Prop :=
  ∀ {A B C : Obj₁} (h : hhs₁ A B) (h' : hhs₁ B C),
    HEq (τ.natSquare (ops₁.hComp h h'))
      (ops₂.sqHComp (τ.natSquare h) (τ.natSquare h'))

/-- Laws for a vertical transformation. -/
structure VertTransLaws {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (flaws : DoubleFunctorLaws ops₁ ops₂ F)
    (glaws : DoubleFunctorLaws ops₁ ops₂ G)
    (τ : VertTransOps F G) : Prop where
  /-- Naturality for vertical morphisms -/
  naturality : VertTransNaturality ops₂ τ
  /-- Naturality for squares -/
  squareNaturality : VertTransSquareNaturality ops₂ τ
  /-- Identity coherence -/
  idCoherence : VertTransIdCoherence ops₁ ops₂ flaws glaws τ
  /-- Composition coherence -/
  compCoherence : VertTransCompCoherence ops₁ ops₂ flaws glaws τ

/-- Data for a vertical transformation between double functors. -/
structure VertTransData {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {data₁ : DoubleCategoryData Obj₁ vhs₁ hhs₁ sqs₁}
    {data₂ : DoubleCategoryData Obj₂ vhs₂ hhs₂ sqs₂}
    (F G : DoubleFunctorData data₁ data₂)
    extends VertTransOps F.toDoubleFunctorOps G.toDoubleFunctorOps where
  /-- Vertical transformation laws -/
  laws : VertTransLaws data₁.toDoubleCategoryOps data₂.toDoubleCategoryOps
    F.laws G.laws toVertTransOps

/-! ## Horizontal Natural Transformations

A horizontal transformation between double functors assigns to each object a
horizontal morphism, with squares filling the naturality diagrams for vertical
morphisms.

Given double functors F, G : D → E, a horizontal transformation τ : F ⟹ₕ G
consists of:
- For each object A : D, a horizontal morphism τ_A : F(A) →ₕ G(A)
- For each vertical morphism v : A →ᵥ C, a square:
  ```
  F(A) ──τ_A──▶ G(A)
   │              │
  F(v)          G(v)
   ▼              ▼
  F(C) ──τ_C──▶ G(C)
  ```
-/

/-- Operations for a horizontal transformation between double functors. -/
@[ext]
structure HorTransOps {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂) where
  /-- Component horizontal morphisms -/
  app : ∀ (A : Obj₁), hhs₂ (F.objMap A) (G.objMap A)
  /-- Naturality squares for vertical morphisms -/
  natSquare : ∀ {A C : Obj₁} (v : vhs₁ A C),
    sqs₂ (F.vertMap v) (G.vertMap v) (app A) (app C)

/-- Naturality condition: components compose with horizontal morphism maps.

For each horizontal morphism h : A →ₕ B in D:
  τ_A ≫ G(h) = F(h) ≫ τ_B
-/
abbrev HorTransNaturality {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (τ : HorTransOps F G) : Prop :=
  ∀ {A B : Obj₁} (h : hhs₁ A B),
    ops₂.hComp (τ.app A) (G.horMap h) = ops₂.hComp (F.horMap h) (τ.app B)

/-- Square naturality condition: naturality squares commute with functor maps.

For a transformation σ : K ⟹ₕ L and any square α with vertical boundaries
v₁ (left) and v₂ (right), we have:
  K(α) ⬝ₕ σ.natSquare(v₂) ≅ σ.natSquare(v₁) ⬝ₕ L(α)
(up to HEq because the horizontal boundaries differ by morphism naturality).

This is a higher coherence condition needed for the interchange law. -/
abbrev HorTransSquareNaturality {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    {K L : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (σ : HorTransOps K L) : Prop :=
  ∀ {A B C D : Obj₁} {v₁ : vhs₁ A C} {v₂ : vhs₁ B D}
    {h₁ : hhs₁ A B} {h₂ : hhs₁ C D}
    (α : sqs₁ v₁ v₂ h₁ h₂),
    HEq (ops₂.sqHComp (K.sqMap α) (σ.natSquare v₂))
        (ops₂.sqHComp (σ.natSquare v₁) (L.sqMap α))

/-- Coherence: naturality squares compose with vertical identity squares.

For each object A, the naturality square of the vertical identity v = id_A
should equal the vertical identity square on τ_A (up to HEq). -/
abbrev HorTransIdCoherence {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (_flaws : DoubleFunctorLaws ops₁ ops₂ F)
    (_glaws : DoubleFunctorLaws ops₁ ops₂ G)
    (τ : HorTransOps F G) : Prop :=
  ∀ (A : Obj₁), HEq (τ.natSquare (ops₁.vId A)) (ops₂.sqVertId (τ.app A))

/-- Coherence: naturality squares compose vertically.

For composable vertical morphisms v : A →ᵥ C and v' : C →ᵥ E:
  natSquare(v ≫ v') = natSquare(v) ⬝ᵥ natSquare(v')
(up to HEq because functor laws change the boundary types).
-/
abbrev HorTransCompCoherence {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (_flaws : DoubleFunctorLaws ops₁ ops₂ F)
    (_glaws : DoubleFunctorLaws ops₁ ops₂ G)
    (τ : HorTransOps F G) : Prop :=
  ∀ {A C E : Obj₁} (v : vhs₁ A C) (v' : vhs₁ C E),
    HEq (τ.natSquare (ops₁.vComp v v'))
      (ops₂.sqVComp (τ.natSquare v) (τ.natSquare v'))

/-- Laws for a horizontal transformation. -/
structure HorTransLaws {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (flaws : DoubleFunctorLaws ops₁ ops₂ F)
    (glaws : DoubleFunctorLaws ops₁ ops₂ G)
    (τ : HorTransOps F G) : Prop where
  /-- Naturality for horizontal morphisms -/
  naturality : HorTransNaturality ops₂ τ
  /-- Naturality for squares -/
  squareNaturality : HorTransSquareNaturality ops₂ τ
  /-- Identity coherence -/
  idCoherence : HorTransIdCoherence ops₁ ops₂ flaws glaws τ
  /-- Composition coherence -/
  compCoherence : HorTransCompCoherence ops₁ ops₂ flaws glaws τ

/-- Data for a horizontal transformation between double functors. -/
structure HorTransData {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {data₁ : DoubleCategoryData Obj₁ vhs₁ hhs₁ sqs₁}
    {data₂ : DoubleCategoryData Obj₂ vhs₂ hhs₂ sqs₂}
    (F G : DoubleFunctorData data₁ data₂)
    extends HorTransOps F.toDoubleFunctorOps G.toDoubleFunctorOps where
  /-- Horizontal transformation laws -/
  laws : HorTransLaws data₁.toDoubleCategoryOps data₂.toDoubleCategoryOps
    F.laws G.laws toHorTransOps

/-! ## Composition of Transformations -/

/-! ### Vertical Composition of Vertical Transformations

Given vertical transformations τ : F ⟹ᵥ G and σ : G ⟹ᵥ H, their vertical
composition σ ⬝ᵥ τ : F ⟹ᵥ H has:
- Components: (σ ⬝ᵥ τ)_A = τ_A ⬝ᵥ σ_A
- Naturality squares: vertical composition of the naturality squares
-/

/-- Vertical composition of vertical transformation operations. -/
def VertTransOps.vComp {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    {F G H : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (τ : VertTransOps F G) (σ : VertTransOps G H) : VertTransOps F H where
  app := fun A => ops₂.vComp (τ.app A) (σ.app A)
  natSquare := fun h => ops₂.sqVComp (τ.natSquare h) (σ.natSquare h)

/-! ### Horizontal Composition of Horizontal Transformations

Given horizontal transformations τ : F ⟹ₕ G and σ : G ⟹ₕ H, their horizontal
composition σ ⬝ₕ τ : F ⟹ₕ H has:
- Components: (σ ⬝ₕ τ)_A = τ_A ⬝ₕ σ_A
- Naturality squares: horizontal composition of the naturality squares
-/

/-- Horizontal composition of horizontal transformation operations. -/
def HorTransOps.hComp {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    {F G H : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (τ : HorTransOps F G) (σ : HorTransOps G H) : HorTransOps F H where
  app := fun A => ops₂.hComp (τ.app A) (σ.app A)
  natSquare := fun v => ops₂.sqHComp (τ.natSquare v) (σ.natSquare v)

/-! ### Identity Transformations -/

/-- Identity vertical transformation on a double functor. -/
def VertTransOps.id {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (F : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂) : VertTransOps F F where
  app := fun A => ops₂.vId (F.objMap A)
  natSquare := fun h => ops₂.sqVertId (F.horMap h)

/-- Identity horizontal transformation on a double functor. -/
def HorTransOps.id {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (F : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂) : HorTransOps F F where
  app := fun A => ops₂.hId (F.objMap A)
  natSquare := fun v => ops₂.sqHorId (F.vertMap v)

/-! ### Double Functor Composition

To define the full "horizontal composition of vertical transformations"
(Godement product), we first need composition of double functors.
-/

/-- Composition of double functor operations. -/
def DoubleFunctorOps.comp {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {Obj₃ : Type u₃}
    {vhs₃ : VertHomSet Obj₃} {hhs₃ : HorHomSet Obj₃} {sqs₃ : SquareSet vhs₃ hhs₃}
    (F : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂)
    (G : DoubleFunctorOps vhs₂ hhs₂ sqs₂ vhs₃ hhs₃ sqs₃) :
    DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₃ hhs₃ sqs₃ where
  objMap := G.objMap ∘ F.objMap
  vertMap := fun v => G.vertMap (F.vertMap v)
  horMap := fun h => G.horMap (F.horMap h)
  sqMap := fun α => G.sqMap (F.sqMap α)

/-- Identity double functor operations. -/
def DoubleFunctorOps.id {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs} :
    DoubleFunctorOps vhs hhs sqs vhs hhs sqs where
  objMap := _root_.id
  vertMap := fun v => v
  horMap := fun h => h
  sqMap := fun α => α

/-- Applying sqMap to HEq squares with equal boundaries gives HEq results. -/
theorem sqMap_heq {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂)
    {A B C D : Obj₁}
    {v₁ v₁' : vhs₁ A C} {v₂ v₂' : vhs₁ B D} {h₁ h₁' : hhs₁ A B} {h₂ h₂' : hhs₁ C D}
    {α : sqs₁ v₁ v₂ h₁ h₂} {β : sqs₁ v₁' v₂' h₁' h₂'}
    (heq : HEq α β)
    (hv₁ : v₁ = v₁') (hv₂ : v₂ = v₂') (hh₁ : h₁ = h₁') (hh₂ : h₂ = h₂') :
    HEq (G.sqMap α) (G.sqMap β) := by
  subst hv₁ hv₂ hh₁ hh₂
  cases heq
  rfl

/-- Right identity for double functor composition. -/
@[simp]
theorem DoubleFunctorOps.comp_id_right {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (F : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂) :
    DoubleFunctorOps.comp F DoubleFunctorOps.id = F := rfl

/-- Left identity for double functor composition. -/
@[simp]
theorem DoubleFunctorOps.comp_id_left {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (F : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂) :
    DoubleFunctorOps.comp DoubleFunctorOps.id F = F := rfl

/-- Associativity of double functor composition. -/
@[simp]
theorem DoubleFunctorOps.comp_assoc {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {Obj₃ : Type u₃}
    {vhs₃ : VertHomSet Obj₃} {hhs₃ : HorHomSet Obj₃} {sqs₃ : SquareSet vhs₃ hhs₃}
    {Obj₄ : Type u₄}
    {vhs₄ : VertHomSet Obj₄} {hhs₄ : HorHomSet Obj₄} {sqs₄ : SquareSet vhs₄ hhs₄}
    (F : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂)
    (G : DoubleFunctorOps vhs₂ hhs₂ sqs₂ vhs₃ hhs₃ sqs₃)
    (H : DoubleFunctorOps vhs₃ hhs₃ sqs₃ vhs₄ hhs₄ sqs₄) :
    DoubleFunctorOps.comp (DoubleFunctorOps.comp F G) H =
    DoubleFunctorOps.comp F (DoubleFunctorOps.comp G H) := rfl

/-- Composed double functors preserve double category structure.

If F : D → E and G : E → E' both satisfy DoubleFunctorLaws, then G ∘ F does too.
Each preservation law follows by composing the individual preservation laws. -/
theorem DoubleFunctorLaws.comp {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {Obj₃ : Type u₃}
    {vhs₃ : VertHomSet Obj₃} {hhs₃ : HorHomSet Obj₃} {sqs₃ : SquareSet vhs₃ hhs₃}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (ops₃ : DoubleCategoryOps Obj₃ vhs₃ hhs₃ sqs₃)
    {F : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    {G : DoubleFunctorOps vhs₂ hhs₂ sqs₂ vhs₃ hhs₃ sqs₃}
    (flaws : DoubleFunctorLaws ops₁ ops₂ F)
    (glaws : DoubleFunctorLaws ops₂ ops₃ G) :
    DoubleFunctorLaws ops₁ ops₃ (F.comp G) where
  map_vId := fun A =>
    calc G.vertMap (F.vertMap (ops₁.vId A))
        = G.vertMap (ops₂.vId (F.objMap A)) := by rw [flaws.map_vId]
      _ = ops₃.vId (G.objMap (F.objMap A)) := by rw [glaws.map_vId]
  map_hId := fun A =>
    calc G.horMap (F.horMap (ops₁.hId A))
        = G.horMap (ops₂.hId (F.objMap A)) := by rw [flaws.map_hId]
      _ = ops₃.hId (G.objMap (F.objMap A)) := by rw [glaws.map_hId]
  map_vComp := fun v₁ v₂ =>
    calc G.vertMap (F.vertMap (ops₁.vComp v₁ v₂))
        = G.vertMap (ops₂.vComp (F.vertMap v₁) (F.vertMap v₂)) := by
            rw [flaws.map_vComp]
      _ = ops₃.vComp (G.vertMap (F.vertMap v₁)) (G.vertMap (F.vertMap v₂)) := by
            rw [glaws.map_vComp]
  map_hComp := fun h₁ h₂ =>
    calc G.horMap (F.horMap (ops₁.hComp h₁ h₂))
        = G.horMap (ops₂.hComp (F.horMap h₁) (F.horMap h₂)) := by rw [flaws.map_hComp]
      _ = ops₃.hComp (G.horMap (F.horMap h₁)) (G.horMap (F.horMap h₂)) := by
            rw [glaws.map_hComp]
  map_sqVertId := fun {A B} h => by
    simp only [DoubleFunctorOps.comp]
    have step1 := flaws.map_sqVertId h
    have step2 := glaws.map_sqVertId (F.horMap h)
    have mid := sqMap_heq G step1 (flaws.map_vId A) (flaws.map_vId B) rfl rfl
    exact HEq.trans mid step2
  map_sqHorId := fun {A C} v => by
    simp only [DoubleFunctorOps.comp]
    have step1 := flaws.map_sqHorId v
    have step2 := glaws.map_sqHorId (F.vertMap v)
    have mid := sqMap_heq G step1 rfl rfl (flaws.map_hId A) (flaws.map_hId C)
    exact HEq.trans mid step2
  map_sqVComp := fun {A B C D E F'} {v₁ v₂ v₁' v₂'} {h₁ h₂ h₃} α β => by
    simp only [DoubleFunctorOps.comp]
    have step1 := flaws.map_sqVComp α β
    have step2 := glaws.map_sqVComp (F.sqMap α) (F.sqMap β)
    have mid := sqMap_heq G step1 (flaws.map_vComp v₁ v₁') (flaws.map_vComp v₂ v₂')
        rfl rfl
    exact HEq.trans mid step2
  map_sqHComp := fun {A B C D E' F'} {v₁ v₂ v₃} {h₁ h₂ h₃ h₄} α β => by
    simp only [DoubleFunctorOps.comp]
    have step1 := flaws.map_sqHComp α β
    have step2 := glaws.map_sqHComp (F.sqMap α) (F.sqMap β)
    have mid := sqMap_heq G step1 rfl rfl (flaws.map_hComp h₁ h₂) (flaws.map_hComp h₃ h₄)
    exact HEq.trans mid step2

/-- Identity double functor satisfies DoubleFunctorLaws. -/
theorem DoubleFunctorLaws.id {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs) :
    DoubleFunctorLaws ops ops DoubleFunctorOps.id where
  map_vId := fun _ => rfl
  map_hId := fun _ => rfl
  map_vComp := fun _ _ => rfl
  map_hComp := fun _ _ => rfl
  map_sqVertId := fun _ => HEq.rfl
  map_sqHorId := fun _ => HEq.rfl
  map_sqVComp := fun _ _ => HEq.rfl
  map_sqHComp := fun _ _ => HEq.rfl

/-- Identity double functor data. -/
def DoubleFunctorData.id {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (data : DoubleCategoryData Obj vhs hhs sqs) :
    DoubleFunctorData data data where
  toDoubleFunctorOps := DoubleFunctorOps.id
  laws := DoubleFunctorLaws.id data.toDoubleCategoryOps

/-- Composition of double functor data. -/
def DoubleFunctorData.comp {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {Obj₃ : Type u₃}
    {vhs₃ : VertHomSet Obj₃} {hhs₃ : HorHomSet Obj₃} {sqs₃ : SquareSet vhs₃ hhs₃}
    {data₁ : DoubleCategoryData Obj₁ vhs₁ hhs₁ sqs₁}
    {data₂ : DoubleCategoryData Obj₂ vhs₂ hhs₂ sqs₂}
    {data₃ : DoubleCategoryData Obj₃ vhs₃ hhs₃ sqs₃}
    (F : DoubleFunctorData data₁ data₂)
    (G : DoubleFunctorData data₂ data₃) :
    DoubleFunctorData data₁ data₃ where
  toDoubleFunctorOps := F.toDoubleFunctorOps.comp G.toDoubleFunctorOps
  laws := DoubleFunctorLaws.comp data₁.toDoubleCategoryOps data₂.toDoubleCategoryOps
      data₃.toDoubleCategoryOps F.laws G.laws

/-- Right identity for double functor data composition. -/
@[simp]
theorem DoubleFunctorData.comp_id_right {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {data₁ : DoubleCategoryData Obj₁ vhs₁ hhs₁ sqs₁}
    {data₂ : DoubleCategoryData Obj₂ vhs₂ hhs₂ sqs₂}
    (F : DoubleFunctorData data₁ data₂) :
    DoubleFunctorData.comp F (DoubleFunctorData.id data₂) = F := rfl

/-- Left identity for double functor data composition. -/
@[simp]
theorem DoubleFunctorData.comp_id_left {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {data₁ : DoubleCategoryData Obj₁ vhs₁ hhs₁ sqs₁}
    {data₂ : DoubleCategoryData Obj₂ vhs₂ hhs₂ sqs₂}
    (F : DoubleFunctorData data₁ data₂) :
    DoubleFunctorData.comp (DoubleFunctorData.id data₁) F = F := rfl

/-- Associativity of double functor data composition. -/
@[simp]
theorem DoubleFunctorData.comp_assoc {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {Obj₃ : Type u₃}
    {vhs₃ : VertHomSet Obj₃} {hhs₃ : HorHomSet Obj₃} {sqs₃ : SquareSet vhs₃ hhs₃}
    {Obj₄ : Type u₄}
    {vhs₄ : VertHomSet Obj₄} {hhs₄ : HorHomSet Obj₄} {sqs₄ : SquareSet vhs₄ hhs₄}
    {data₁ : DoubleCategoryData Obj₁ vhs₁ hhs₁ sqs₁}
    {data₂ : DoubleCategoryData Obj₂ vhs₂ hhs₂ sqs₂}
    {data₃ : DoubleCategoryData Obj₃ vhs₃ hhs₃ sqs₃}
    {data₄ : DoubleCategoryData Obj₄ vhs₄ hhs₄ sqs₄}
    (F : DoubleFunctorData data₁ data₂)
    (G : DoubleFunctorData data₂ data₃)
    (H : DoubleFunctorData data₃ data₄) :
    DoubleFunctorData.comp (DoubleFunctorData.comp F G) H =
    DoubleFunctorData.comp F (DoubleFunctorData.comp G H) := rfl

/-! ### Cross Compositions of Transformations

The "horizontal composition of vertical transformations" is the Godement
product: given τ : F ⟹ᵥ G (between D → E) and σ : H ⟹ᵥ K (between E → E'),
we get (σ * τ) : (H ∘ F) ⟹ᵥ (K ∘ G) (between D → E').

At each object A, the component is: H(τ_A) ⬝ᵥ σ_{G(A)} = σ_{F(A)} ⬝ᵥ K(τ_A)
(these are equal by naturality of σ).
-/

/-- Horizontal composition (Godement product) of vertical transformations.

Given τ : F ⟹ᵥ G between D → E and σ : H ⟹ᵥ K between E → E',
the composite (σ * τ) : (H ∘ F) ⟹ᵥ (K ∘ G) has components:
  (σ * τ)_A = H(τ_A) ⬝ᵥ σ_{G(A)}
-/
def VertTransOps.hComp {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {Obj₃ : Type u₃}
    {vhs₃ : VertHomSet Obj₃} {hhs₃ : HorHomSet Obj₃} {sqs₃ : SquareSet vhs₃ hhs₃}
    (ops₃ : DoubleCategoryOps Obj₃ vhs₃ hhs₃ sqs₃)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    {H K : DoubleFunctorOps vhs₂ hhs₂ sqs₂ vhs₃ hhs₃ sqs₃}
    (τ : VertTransOps F G) (σ : VertTransOps H K) :
    VertTransOps (F.comp H) (G.comp K) where
  app := fun A => ops₃.vComp (H.vertMap (τ.app A)) (σ.app (G.objMap A))
  natSquare := fun h =>
    ops₃.sqVComp (H.sqMap (τ.natSquare h)) (σ.natSquare (G.horMap h))

/-- Vertical composition (Godement product) of horizontal transformations.

Given τ : F ⟹ₕ G between D → E and σ : H ⟹ₕ K between E → E',
the composite (σ * τ) : (H ∘ F) ⟹ₕ (K ∘ G) has components:
  (σ * τ)_A = H(τ_A) ⬝ₕ σ_{G(A)}
-/
def HorTransOps.vComp {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {Obj₃ : Type u₃}
    {vhs₃ : VertHomSet Obj₃} {hhs₃ : HorHomSet Obj₃} {sqs₃ : SquareSet vhs₃ hhs₃}
    (ops₃ : DoubleCategoryOps Obj₃ vhs₃ hhs₃ sqs₃)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    {H K : DoubleFunctorOps vhs₂ hhs₂ sqs₂ vhs₃ hhs₃ sqs₃}
    (τ : HorTransOps F G) (σ : HorTransOps H K) :
    HorTransOps (F.comp H) (G.comp K) where
  app := fun A => ops₃.hComp (H.horMap (τ.app A)) (σ.app (G.objMap A))
  natSquare := fun v =>
    ops₃.sqHComp (H.sqMap (τ.natSquare v)) (σ.natSquare (G.vertMap v))

/-! ## Category Axioms for Transformation Composition

The composition operations on transformations satisfy the category axioms
when the target double category satisfies its laws.
-/

/-! ### Vertical Composition of Vertical Transformations -/

/-- Heterogeneous equality of VertTransOps from component-wise HEq.

This is useful when proving laws about transformation composition, where the
square type depends on the vertical morphism type. -/
theorem VertTransOps.heq_mk {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    {app₁ app₂ : ∀ (A : Obj₁), vhs₂ (F.objMap A) (G.objMap A)}
    {natSquare₁ : ∀ {A B : Obj₁} (h : hhs₁ A B),
      sqs₂ (app₁ A) (app₁ B) (F.horMap h) (G.horMap h)}
    {natSquare₂ : ∀ {A B : Obj₁} (h : hhs₁ A B),
      sqs₂ (app₂ A) (app₂ B) (F.horMap h) (G.horMap h)}
    (h_app : ∀ A, app₁ A = app₂ A)
    (h_natSquare : ∀ {A B : Obj₁} (h : hhs₁ A B),
      HEq (natSquare₁ h) (natSquare₂ h)) :
    HEq (VertTransOps.mk app₁ natSquare₁) (VertTransOps.mk app₂ natSquare₂) := by
  have app_eq : app₁ = app₂ := funext h_app
  subst app_eq
  have natSquare_eq : @natSquare₁ = @natSquare₂ := by
    funext A B h
    exact eq_of_heq (h_natSquare h)
  subst natSquare_eq
  rfl

/-- Helper lemma: vertical morphism composition associativity. -/
theorem vComp_assoc {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs)
    (laws : DoubleCategoryLaws ops)
    {A B C D : Obj} (f : vhs A B) (g : vhs B C) (h : vhs C D) :
    ops.vComp (ops.vComp f g) h = ops.vComp f (ops.vComp g h) :=
  laws.vertLaws.assoc f g h

/-- Helper lemma: horizontal morphism composition associativity. -/
theorem hComp_assoc {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs)
    (laws : DoubleCategoryLaws ops)
    {A B C D : Obj} (f : hhs A B) (g : hhs B C) (h : hhs C D) :
    ops.hComp (ops.hComp f g) h = ops.hComp f (ops.hComp g h) :=
  laws.horLaws.assoc f g h

/-- Helper lemma: vertical identity square law (HEq version). -/
theorem sqVIdComp_heq {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs)
    (laws : DoubleCategoryLaws ops)
    {A B C D : Obj} {v₁ : vhs A C} {v₂ : vhs B D} {h₁ : hhs A B} {h₂ : hhs C D}
    (α : sqs v₁ v₂ h₁ h₂) :
    HEq (ops.sqVComp (ops.sqVertId h₁) α) α :=
  laws.sqLaws.sqVIdComp α

/-- Helper lemma: vertical right identity square law (HEq version). -/
theorem sqVCompId_heq {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs)
    (laws : DoubleCategoryLaws ops)
    {A B C D : Obj} {v₁ : vhs A C} {v₂ : vhs B D} {h₁ : hhs A B} {h₂ : hhs C D}
    (α : sqs v₁ v₂ h₁ h₂) :
    HEq (ops.sqVComp α (ops.sqVertId h₂)) α :=
  laws.sqLaws.sqVCompId α

/-- Helper lemma: vertical associativity square law (HEq version). -/
theorem sqVAssoc_heq {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs)
    (laws : DoubleCategoryLaws ops)
    {A B C D E F G H : Obj}
    {v₁ : vhs A C} {v₂ : vhs B D}
    {v₁' : vhs C E} {v₂' : vhs D F}
    {v₁'' : vhs E G} {v₂'' : vhs F H}
    {h₁ : hhs A B} {h₂ : hhs C D} {h₃ : hhs E F} {h₄ : hhs G H}
    (α : sqs v₁ v₂ h₁ h₂) (β : sqs v₁' v₂' h₂ h₃) (γ : sqs v₁'' v₂'' h₃ h₄) :
    HEq (ops.sqVComp (ops.sqVComp α β) γ) (ops.sqVComp α (ops.sqVComp β γ)) :=
  laws.sqLaws.sqVAssoc α β γ

/-- Left identity law for vertical composition of vertical transformations.

Note: This holds as heterogeneous equality because the natSquare field's type
depends on the app field, and composition with the identity transformation
changes the types of the squares. -/
theorem VertTransOps.vComp_id_left_heq {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (laws₂ : DoubleCategoryLaws ops₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (τ : VertTransOps F G) :
    HEq (VertTransOps.vComp ops₂ (VertTransOps.id ops₂ F) τ) τ := by
  simp only [VertTransOps.vComp, VertTransOps.id]
  apply VertTransOps.heq_mk
  · intro A
    exact laws₂.vertLaws.id_laws.id_comp _
  · intro A B h
    exact sqVIdComp_heq ops₂ laws₂ _

/-- Right identity law for vertical composition of vertical transformations. -/
theorem VertTransOps.vComp_id_right_heq {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (laws₂ : DoubleCategoryLaws ops₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (τ : VertTransOps F G) :
    HEq (VertTransOps.vComp ops₂ τ (VertTransOps.id ops₂ G)) τ := by
  simp only [VertTransOps.vComp, VertTransOps.id]
  apply VertTransOps.heq_mk
  · intro A
    exact laws₂.vertLaws.id_laws.comp_id _
  · intro A B h
    exact sqVCompId_heq ops₂ laws₂ _

/-- Associativity law for vertical composition of vertical transformations. -/
theorem VertTransOps.vComp_assoc_heq {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (laws₂ : DoubleCategoryLaws ops₂)
    {F G H K : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (τ : VertTransOps F G) (σ : VertTransOps G H) (ρ : VertTransOps H K) :
    HEq (VertTransOps.vComp ops₂ (VertTransOps.vComp ops₂ τ σ) ρ)
        (VertTransOps.vComp ops₂ τ (VertTransOps.vComp ops₂ σ ρ)) := by
  simp only [VertTransOps.vComp]
  apply VertTransOps.heq_mk
  · intro A
    exact laws₂.vertLaws.assoc _ _ _
  · intro A B h
    exact sqVAssoc_heq ops₂ laws₂ _ _ _

/-! ### Category Axioms for HorTransOps.hComp -/

/-- Helper for constructing HEq of HorTransOps from component-wise HEq. -/
theorem HorTransOps.heq_mk {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    {app₁ app₂ : ∀ (A : Obj₁), hhs₂ (F.objMap A) (G.objMap A)}
    {natSquare₁ : ∀ {A C : Obj₁} (v : vhs₁ A C),
      sqs₂ (F.vertMap v) (G.vertMap v) (app₁ A) (app₁ C)}
    {natSquare₂ : ∀ {A C : Obj₁} (v : vhs₁ A C),
      sqs₂ (F.vertMap v) (G.vertMap v) (app₂ A) (app₂ C)}
    (h_app : ∀ A, app₁ A = app₂ A)
    (h_natSquare : ∀ {A C : Obj₁} (v : vhs₁ A C),
      HEq (natSquare₁ v) (natSquare₂ v)) :
    HEq (HorTransOps.mk app₁ natSquare₁) (HorTransOps.mk app₂ natSquare₂) := by
  have app_eq : app₁ = app₂ := funext h_app
  subst app_eq
  have natSquare_eq : @natSquare₁ = @natSquare₂ := by
    funext A C v
    exact eq_of_heq (h_natSquare v)
  subst natSquare_eq
  rfl

/-- Horizontal identity-composition law for squares (HEq version). -/
theorem sqHIdComp_heq {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs)
    (laws : DoubleCategoryLaws ops)
    {A B C D : Obj} {v₁ : vhs A B} {v₂ : vhs C D} {h₁ : hhs A C} {h₂ : hhs B D}
    (α : sqs v₁ v₂ h₁ h₂) :
    HEq (ops.sqHComp (ops.sqHorId v₁) α) α :=
  laws.sqLaws.sqHIdComp α

/-- Horizontal composition-identity law for squares (HEq version). -/
theorem sqHCompId_heq {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs)
    (laws : DoubleCategoryLaws ops)
    {A B C D : Obj} {v₁ : vhs A B} {v₂ : vhs C D} {h₁ : hhs A C} {h₂ : hhs B D}
    (α : sqs v₁ v₂ h₁ h₂) :
    HEq (ops.sqHComp α (ops.sqHorId v₂)) α :=
  laws.sqLaws.sqHCompId α

/-- Horizontal associativity law for squares (HEq version). -/
theorem sqHAssoc_heq {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs)
    (laws : DoubleCategoryLaws ops)
    {A B C D E F G H : Obj}
    {v₁ : vhs A E} {v₂ : vhs B F} {v₃ : vhs C G} {v₄ : vhs D H}
    {h₁ : hhs A B} {h₂ : hhs B C} {h₃ : hhs C D}
    {h₅ : hhs E F} {h₆ : hhs F G} {h₇ : hhs G H}
    (α : sqs v₁ v₂ h₁ h₅) (β : sqs v₂ v₃ h₂ h₆) (γ : sqs v₃ v₄ h₃ h₇) :
    HEq (ops.sqHComp (ops.sqHComp α β) γ) (ops.sqHComp α (ops.sqHComp β γ)) :=
  laws.sqLaws.sqHAssoc α β γ

/-- Left identity law for horizontal composition of horizontal transformations. -/
theorem HorTransOps.hComp_id_left_heq {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (laws₂ : DoubleCategoryLaws ops₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (τ : HorTransOps F G) :
    HEq (HorTransOps.hComp ops₂ (HorTransOps.id ops₂ F) τ) τ := by
  simp only [HorTransOps.hComp, HorTransOps.id]
  apply HorTransOps.heq_mk
  · intro A
    exact laws₂.horLaws.id_laws.id_comp _
  · intro A C v
    exact sqHIdComp_heq ops₂ laws₂ _

/-- Right identity law for horizontal composition of horizontal transformations. -/
theorem HorTransOps.hComp_id_right_heq {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (laws₂ : DoubleCategoryLaws ops₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (τ : HorTransOps F G) :
    HEq (HorTransOps.hComp ops₂ τ (HorTransOps.id ops₂ G)) τ := by
  simp only [HorTransOps.hComp, HorTransOps.id]
  apply HorTransOps.heq_mk
  · intro A
    exact laws₂.horLaws.id_laws.comp_id _
  · intro A C v
    exact sqHCompId_heq ops₂ laws₂ _

/-- Associativity law for horizontal composition of horizontal transformations. -/
theorem HorTransOps.hComp_assoc_heq {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (laws₂ : DoubleCategoryLaws ops₂)
    {F G H K : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (τ : HorTransOps F G) (σ : HorTransOps G H) (ρ : HorTransOps H K) :
    HEq (HorTransOps.hComp ops₂ (HorTransOps.hComp ops₂ τ σ) ρ)
        (HorTransOps.hComp ops₂ τ (HorTransOps.hComp ops₂ σ ρ)) := by
  simp only [HorTransOps.hComp]
  apply HorTransOps.heq_mk
  · intro A
    exact laws₂.horLaws.assoc _ _ _
  · intro A C v
    exact sqHAssoc_heq ops₂ laws₂ _ _ _

/-! ### Interchange Law for Transformations

The interchange law relates the Godement product (horizontal composition) and
vertical composition of vertical transformations. Given transformations
τ : F ⟹ᵥ G, τ' : G ⟹ᵥ H (between D and E) and σ : K ⟹ᵥ L, σ' : L ⟹ᵥ M
(between E and E'), the interchange law states:

  (τ ⬝ᵥ τ') ⬝ₕ (σ ⬝ᵥ σ') = (τ ⬝ₕ σ) ⬝ᵥ (τ' ⬝ₕ σ')

This requires:
- K preserves vertical composition (DoubleFunctorLaws)
- σ satisfies naturality with respect to vertical morphisms (VertTransNaturality)
- Associativity of vertical composition in the target category
-/

/-- HEq congruence for sqVComp in the first argument (left square). -/
theorem sqVComp_heq_left {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs)
    {A B C D E F : Obj}
    {v₁ v₁' : vhs A C} {v₂ v₂' : vhs B D} {v₃ : vhs C E} {v₄ : vhs D F}
    {h₁ : hhs A B} {h₂ : hhs C D} {h₃ : hhs E F}
    {α : sqs v₁ v₂ h₁ h₂} {α' : sqs v₁' v₂' h₁ h₂}
    (β : sqs v₃ v₄ h₂ h₃)
    (heq : HEq α α') (hv₁ : v₁ = v₁') (hv₂ : v₂ = v₂') :
    HEq (ops.sqVComp α β) (ops.sqVComp α' β) := by
  subst hv₁ hv₂
  exact heq_of_eq (congrArg (ops.sqVComp · β) (eq_of_heq heq))

/-- HEq congruence for sqVComp in the second argument (right square). -/
theorem sqVComp_heq_right {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs)
    {A B C D E F : Obj}
    {v₁ : vhs A C} {v₂ : vhs B D} {v₃ v₃' : vhs C E} {v₄ v₄' : vhs D F}
    {h₁ : hhs A B} {h₂ : hhs C D} {h₃ : hhs E F}
    (α : sqs v₁ v₂ h₁ h₂)
    {β : sqs v₃ v₄ h₂ h₃} {β' : sqs v₃' v₄' h₂ h₃}
    (heq : HEq β β') (hv₃ : v₃ = v₃') (hv₄ : v₄ = v₄') :
    HEq (ops.sqVComp α β) (ops.sqVComp α β') := by
  subst hv₃ hv₄
  exact heq_of_eq (congrArg (ops.sqVComp α) (eq_of_heq heq))

/-- HEq congruence for sqVComp in both arguments with changing horizontal
boundaries. This handles the case where both squares change and the horizontal
boundaries also change (via functor preservation laws). -/
theorem sqVComp_heq_both {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs)
    {A B C D E F : Obj}
    {v₁ : vhs A C} {v₂ : vhs B D} {v₃ : vhs C E} {v₄ : vhs D F}
    {h₁ h₁' : hhs A B} {h₂ h₂' : hhs C D} {h₃ h₃' : hhs E F}
    {α : sqs v₁ v₂ h₁ h₂} {α' : sqs v₁ v₂ h₁' h₂'}
    {β : sqs v₃ v₄ h₂ h₃} {β' : sqs v₃ v₄ h₂' h₃'}
    (hα : HEq α α') (hβ : HEq β β')
    (htop : h₁ = h₁') (hmid : h₂ = h₂') (hbot : h₃ = h₃') :
    HEq (ops.sqVComp α β) (ops.sqVComp α' β') := by
  subst htop hmid hbot
  cases hα
  cases hβ
  rfl

/-- Helper lemma for interchange: the natSquare component HEq.

This proves the square-level interchange law. Given squares α, β in the source,
and transformations σ, σ' in the target, we show that the two ways of composing
(using klaws, associativity, and σSqNat) produce HEq squares. -/
theorem interchange_natSquare {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {Obj₃ : Type u₃}
    {vhs₃ : VertHomSet Obj₃} {hhs₃ : HorHomSet Obj₃} {sqs₃ : SquareSet vhs₃ hhs₃}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (ops₃ : DoubleCategoryOps Obj₃ vhs₃ hhs₃ sqs₃)
    (laws₃ : DoubleCategoryLaws ops₃)
    {F G H : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    {K L M : DoubleFunctorOps vhs₂ hhs₂ sqs₂ vhs₃ hhs₃ sqs₃}
    (klaws : DoubleFunctorLaws ops₂ ops₃ K)
    (τ : VertTransOps F G) (τ' : VertTransOps G H)
    (σ : VertTransOps K L) (σ' : VertTransOps L M)
    (σNat : VertTransNaturality ops₃ σ)
    (σSqNat : VertTransSquareNaturality ops₃ σ)
    {A B : Obj₁} (h : hhs₁ A B) :
    HEq (ops₃.sqVComp (K.sqMap (ops₂.sqVComp (τ.natSquare h) (τ'.natSquare h)))
           (ops₃.sqVComp (σ.natSquare (H.horMap h)) (σ'.natSquare (H.horMap h))))
        (ops₃.sqVComp (ops₃.sqVComp (K.sqMap (τ.natSquare h)) (σ.natSquare (G.horMap h)))
           (ops₃.sqVComp (L.sqMap (τ'.natSquare h)) (σ'.natSquare (H.horMap h)))) := by
  -- Abbreviations for readability
  let α := τ.natSquare h
  let β := τ'.natSquare h
  let γ := σ.natSquare (H.horMap h)
  let δ := σ'.natSquare (H.horMap h)
  let γ' := σ.natSquare (G.horMap h)
  have kpres := klaws.map_sqVComp α β
  have σsqnat := σSqNat β
  -- Chain of HEq transformations
  -- Step 1: Apply K preserves sqVComp
  have s1 : HEq (ops₃.sqVComp (K.sqMap (ops₂.sqVComp α β)) (ops₃.sqVComp γ δ))
                (ops₃.sqVComp (ops₃.sqVComp (K.sqMap α) (K.sqMap β)) (ops₃.sqVComp γ δ)) :=
    sqVComp_heq_left ops₃ (ops₃.sqVComp γ δ) kpres (klaws.map_vComp _ _) (klaws.map_vComp _ _)
  -- Step 2: Associativity on outer
  have s2 : HEq (ops₃.sqVComp (ops₃.sqVComp (K.sqMap α) (K.sqMap β)) (ops₃.sqVComp γ δ))
                (ops₃.sqVComp (K.sqMap α) (ops₃.sqVComp (K.sqMap β) (ops₃.sqVComp γ δ))) :=
    sqVAssoc_heq ops₃ laws₃ (K.sqMap α) (K.sqMap β) (ops₃.sqVComp γ δ)
  -- Step 3: Associativity on inner
  have s3 : HEq (ops₃.sqVComp (K.sqMap α) (ops₃.sqVComp (K.sqMap β) (ops₃.sqVComp γ δ)))
                (ops₃.sqVComp (K.sqMap α) (ops₃.sqVComp (ops₃.sqVComp (K.sqMap β) γ) δ)) :=
    sqVComp_heq_right ops₃ (K.sqMap α)
      (HEq.symm (sqVAssoc_heq ops₃ laws₃ (K.sqMap β) γ δ))
      (Eq.symm (vComp_assoc ops₃ laws₃ _ _ _))
      (Eq.symm (vComp_assoc ops₃ laws₃ _ _ _))
  -- Step 4: Apply σSqNat to swap (K.sqMap β) ⬝ᵥ γ with γ' ⬝ᵥ (L.sqMap β)
  -- Boundary equalities from VertTransNaturality: σ(X) ⬝ᵥ L(v) = K(v) ⬝ᵥ σ(Y)
  have s4 : HEq (ops₃.sqVComp (K.sqMap α) (ops₃.sqVComp (ops₃.sqVComp (K.sqMap β) γ) δ))
                (ops₃.sqVComp (K.sqMap α) (ops₃.sqVComp (ops₃.sqVComp γ' (L.sqMap β)) δ)) :=
    sqVComp_heq_right ops₃ (K.sqMap α)
      (sqVComp_heq_left ops₃ δ σsqnat (Eq.symm (σNat (τ'.app A))) (Eq.symm (σNat (τ'.app B))))
      (congrArg (ops₃.vComp · (σ'.app (H.objMap A))) (Eq.symm (σNat (τ'.app A))))
      (congrArg (ops₃.vComp · (σ'.app (H.objMap B))) (Eq.symm (σNat (τ'.app B))))
  -- Step 5: Associativity on inner again
  have s5 : HEq (ops₃.sqVComp (K.sqMap α) (ops₃.sqVComp (ops₃.sqVComp γ' (L.sqMap β)) δ))
                (ops₃.sqVComp (K.sqMap α) (ops₃.sqVComp γ' (ops₃.sqVComp (L.sqMap β) δ))) :=
    sqVComp_heq_right ops₃ (K.sqMap α)
      (sqVAssoc_heq ops₃ laws₃ γ' (L.sqMap β) δ)
      (vComp_assoc ops₃ laws₃ _ _ _)
      (vComp_assoc ops₃ laws₃ _ _ _)
  -- Step 6: Associativity on outer to get final form
  have s6 : HEq (ops₃.sqVComp (K.sqMap α) (ops₃.sqVComp γ' (ops₃.sqVComp (L.sqMap β) δ)))
                (ops₃.sqVComp (ops₃.sqVComp (K.sqMap α) γ') (ops₃.sqVComp (L.sqMap β) δ)) :=
    HEq.symm (sqVAssoc_heq ops₃ laws₃ (K.sqMap α) γ' (ops₃.sqVComp (L.sqMap β) δ))
  -- Chain all HEq steps
  exact HEq.trans s1 (HEq.trans s2 (HEq.trans s3 (HEq.trans s4 (HEq.trans s5 s6))))

/-- Helper lemma for interchange: the app component equality. -/
theorem interchange_app {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {Obj₃ : Type u₃}
    {vhs₃ : VertHomSet Obj₃} {hhs₃ : HorHomSet Obj₃} {sqs₃ : SquareSet vhs₃ hhs₃}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (ops₃ : DoubleCategoryOps Obj₃ vhs₃ hhs₃ sqs₃)
    (laws₃ : DoubleCategoryLaws ops₃)
    {F G H : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    {K L M : DoubleFunctorOps vhs₂ hhs₂ sqs₂ vhs₃ hhs₃ sqs₃}
    (klaws : DoubleFunctorLaws ops₂ ops₃ K)
    (τ : VertTransOps F G) (τ' : VertTransOps G H)
    (σ : VertTransOps K L) (σ' : VertTransOps L M)
    (σNat : VertTransNaturality ops₃ σ)
    (A : Obj₁) :
    ((τ.vComp ops₂ τ').hComp ops₃ (σ.vComp ops₃ σ')).app A
    = ((τ.hComp ops₃ σ).vComp ops₃ (τ'.hComp ops₃ σ')).app A := by
  simp only [VertTransOps.hComp, VertTransOps.vComp]
  rw [klaws.map_vComp]
  rw [vComp_assoc ops₃ laws₃ (K.vertMap (τ.app A)) (K.vertMap (τ'.app A))
        (ops₃.vComp (σ.app (H.objMap A)) (σ'.app (H.objMap A)))]
  rw [← vComp_assoc ops₃ laws₃ (K.vertMap (τ'.app A)) (σ.app (H.objMap A))
        (σ'.app (H.objMap A))]
  rw [← σNat (τ'.app A)]
  rw [vComp_assoc ops₃ laws₃ (σ.app (G.objMap A)) (L.vertMap (τ'.app A))
        (σ'.app (H.objMap A))]
  rw [← vComp_assoc ops₃ laws₃ (K.vertMap (τ.app A)) (σ.app (G.objMap A))
        (ops₃.vComp (L.vertMap (τ'.app A)) (σ'.app (H.objMap A)))]

theorem VertTransOps.interchange {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {Obj₃ : Type u₃}
    {vhs₃ : VertHomSet Obj₃} {hhs₃ : HorHomSet Obj₃} {sqs₃ : SquareSet vhs₃ hhs₃}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (ops₃ : DoubleCategoryOps Obj₃ vhs₃ hhs₃ sqs₃)
    (laws₃ : DoubleCategoryLaws ops₃)
    {F G H : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    {K L M : DoubleFunctorOps vhs₂ hhs₂ sqs₂ vhs₃ hhs₃ sqs₃}
    (klaws : DoubleFunctorLaws ops₂ ops₃ K)
    (llaws : DoubleFunctorLaws ops₂ ops₃ L)
    (τ : VertTransOps F G) (τ' : VertTransOps G H)
    (σ : VertTransOps K L) (σ' : VertTransOps L M)
    (σlaws : VertTransLaws ops₂ ops₃ klaws llaws σ) :
    (τ.vComp ops₂ τ').hComp ops₃ (σ.vComp ops₃ σ')
    = (τ.hComp ops₃ σ).vComp ops₃ (τ'.hComp ops₃ σ') := by
  have h_app : ∀ A, ((τ.vComp ops₂ τ').hComp ops₃ (σ.vComp ops₃ σ')).app A
      = ((τ.hComp ops₃ σ).vComp ops₃ (τ'.hComp ops₃ σ')).app A :=
    interchange_app ops₂ ops₃ laws₃ klaws τ τ' σ σ' σlaws.naturality
  apply eq_of_heq
  apply VertTransOps.heq_mk h_app
  intro A B h
  simp only [VertTransOps.vComp, VertTransOps.hComp]
  exact interchange_natSquare ops₂ ops₃ laws₃ klaws τ τ' σ σ'
    σlaws.naturality σlaws.squareNaturality h

/-- HEq congruence for sqHComp in the first argument (left square).

For horizontal composition with this layout:
```
A ─h₁─▶ B ─h₂─▶ C
│       │       │
v₁      v₂      v₃
▼       ▼       ▼
D ─h₃─▶ E ─h₄─▶ F
```
The squares share the middle vertical boundary v₂. -/
theorem sqHComp_heq_left {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs)
    {A B C D E F : Obj}
    {v₁ : vhs A D} {v₂ : vhs B E} {v₃ : vhs C F}
    {h₁ h₁' : hhs A B} {h₂ : hhs B C} {h₃ h₃' : hhs D E} {h₄ : hhs E F}
    {α : sqs v₁ v₂ h₁ h₃} {α' : sqs v₁ v₂ h₁' h₃'}
    (β : sqs v₂ v₃ h₂ h₄)
    (heq : HEq α α') (hh₁ : h₁ = h₁') (hh₃ : h₃ = h₃') :
    HEq (ops.sqHComp α β) (ops.sqHComp α' β) := by
  subst hh₁ hh₃
  exact heq_of_eq (congrArg (ops.sqHComp · β) (eq_of_heq heq))

/-- HEq congruence for sqHComp in the second argument (right square).

For horizontal composition with the layout shown in `sqHComp_heq_left`, squares share
the middle vertical boundary v₂. -/
theorem sqHComp_heq_right {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs)
    {A B C D E F : Obj}
    {v₁ : vhs A D} {v₂ : vhs B E} {v₃ : vhs C F}
    {h₁ : hhs A B} {h₂ h₂' : hhs B C} {h₃ : hhs D E} {h₄ h₄' : hhs E F}
    (α : sqs v₁ v₂ h₁ h₃)
    {β : sqs v₂ v₃ h₂ h₄} {β' : sqs v₂ v₃ h₂' h₄'}
    (heq : HEq β β') (hh₂ : h₂ = h₂') (hh₄ : h₄ = h₄') :
    HEq (ops.sqHComp α β) (ops.sqHComp α β') := by
  subst hh₂ hh₄
  exact heq_of_eq (congrArg (ops.sqHComp α) (eq_of_heq heq))

/-- HEq congruence for sqHComp when both squares change with equal vertical boundaries.

For horizontal composition:
```text
  α   ⬝ₕ   β
  ↓        ↓
  α'  ⬝ₕ   β'
```
If α ≅ α' and β ≅ β' via HEq, and the left/middle/right vertical morphisms are equal,
then sqHComp α β ≅ sqHComp α' β'. -/
theorem sqHComp_heq_both {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs)
    {A B C D E F : Obj}
    {v₁ v₁' : vhs A D} {v₂ v₂' : vhs B E} {v₃ v₃' : vhs C F}
    {h₁ : hhs A B} {h₂ : hhs B C} {h₃ : hhs D E} {h₄ : hhs E F}
    {α : sqs v₁ v₂ h₁ h₃} {α' : sqs v₁' v₂' h₁ h₃}
    {β : sqs v₂ v₃ h₂ h₄} {β' : sqs v₂' v₃' h₂ h₄}
    (hα : HEq α α') (hβ : HEq β β')
    (hleft : v₁ = v₁') (hmid : v₂ = v₂') (hright : v₃ = v₃') :
    HEq (ops.sqHComp α β) (ops.sqHComp α' β') := by
  subst hleft hmid hright
  cases hα
  cases hβ
  rfl

/-- Helper lemma for horizontal interchange: the natSquare component HEq.

This proves the square-level interchange law for horizontal transformations.
Given squares α, β in the source, and transformations σ, σ' in the target,
we show that the two ways of composing produce HEq squares. -/
theorem interchange_natSquare_hor {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {Obj₃ : Type u₃}
    {vhs₃ : VertHomSet Obj₃} {hhs₃ : HorHomSet Obj₃} {sqs₃ : SquareSet vhs₃ hhs₃}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (ops₃ : DoubleCategoryOps Obj₃ vhs₃ hhs₃ sqs₃)
    (laws₃ : DoubleCategoryLaws ops₃)
    {F G H : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    {K L M : DoubleFunctorOps vhs₂ hhs₂ sqs₂ vhs₃ hhs₃ sqs₃}
    (klaws : DoubleFunctorLaws ops₂ ops₃ K)
    (τ : HorTransOps F G) (τ' : HorTransOps G H)
    (σ : HorTransOps K L) (σ' : HorTransOps L M)
    (σNat : HorTransNaturality ops₃ σ)
    (σSqNat : HorTransSquareNaturality ops₃ σ)
    {A B : Obj₁} (v : vhs₁ A B) :
    HEq (ops₃.sqHComp (K.sqMap (ops₂.sqHComp (τ.natSquare v) (τ'.natSquare v)))
           (ops₃.sqHComp (σ.natSquare (H.vertMap v)) (σ'.natSquare (H.vertMap v))))
        (ops₃.sqHComp (ops₃.sqHComp (K.sqMap (τ.natSquare v)) (σ.natSquare (G.vertMap v)))
           (ops₃.sqHComp (L.sqMap (τ'.natSquare v)) (σ'.natSquare (H.vertMap v)))) := by
  let α := τ.natSquare v
  let β := τ'.natSquare v
  let γ := σ.natSquare (H.vertMap v)
  let δ := σ'.natSquare (H.vertMap v)
  let γ' := σ.natSquare (G.vertMap v)
  have kpres := klaws.map_sqHComp α β
  have σsqnat := σSqNat β
  -- Step 1: Apply K preserves sqHComp
  have s1 : HEq (ops₃.sqHComp (K.sqMap (ops₂.sqHComp α β)) (ops₃.sqHComp γ δ))
                (ops₃.sqHComp (ops₃.sqHComp (K.sqMap α) (K.sqMap β)) (ops₃.sqHComp γ δ)) :=
    sqHComp_heq_left ops₃ (ops₃.sqHComp γ δ) kpres (klaws.map_hComp _ _) (klaws.map_hComp _ _)
  -- Step 2: Associativity on outer
  have s2 : HEq (ops₃.sqHComp (ops₃.sqHComp (K.sqMap α) (K.sqMap β)) (ops₃.sqHComp γ δ))
                (ops₃.sqHComp (K.sqMap α) (ops₃.sqHComp (K.sqMap β) (ops₃.sqHComp γ δ))) :=
    sqHAssoc_heq ops₃ laws₃ (K.sqMap α) (K.sqMap β) (ops₃.sqHComp γ δ)
  -- Step 3: Associativity on inner
  have s3 : HEq (ops₃.sqHComp (K.sqMap α) (ops₃.sqHComp (K.sqMap β) (ops₃.sqHComp γ δ)))
                (ops₃.sqHComp (K.sqMap α) (ops₃.sqHComp (ops₃.sqHComp (K.sqMap β) γ) δ)) :=
    sqHComp_heq_right ops₃ (K.sqMap α)
      (HEq.symm (sqHAssoc_heq ops₃ laws₃ (K.sqMap β) γ δ))
      (Eq.symm (hComp_assoc ops₃ laws₃ _ _ _))
      (Eq.symm (hComp_assoc ops₃ laws₃ _ _ _))
  -- Step 4: Apply σSqNat to swap (K.sqMap β) ⬝ₕ γ with γ' ⬝ₕ (L.sqMap β)
  have s4 : HEq (ops₃.sqHComp (K.sqMap α) (ops₃.sqHComp (ops₃.sqHComp (K.sqMap β) γ) δ))
                (ops₃.sqHComp (K.sqMap α) (ops₃.sqHComp (ops₃.sqHComp γ' (L.sqMap β)) δ)) :=
    sqHComp_heq_right ops₃ (K.sqMap α)
      (sqHComp_heq_left ops₃ δ σsqnat (Eq.symm (σNat (τ'.app A))) (Eq.symm (σNat (τ'.app B))))
      (congrArg (ops₃.hComp · (σ'.app (H.objMap A))) (Eq.symm (σNat (τ'.app A))))
      (congrArg (ops₃.hComp · (σ'.app (H.objMap B))) (Eq.symm (σNat (τ'.app B))))
  -- Step 5: Associativity on inner again
  have s5 : HEq (ops₃.sqHComp (K.sqMap α) (ops₃.sqHComp (ops₃.sqHComp γ' (L.sqMap β)) δ))
                (ops₃.sqHComp (K.sqMap α) (ops₃.sqHComp γ' (ops₃.sqHComp (L.sqMap β) δ))) :=
    sqHComp_heq_right ops₃ (K.sqMap α)
      (sqHAssoc_heq ops₃ laws₃ γ' (L.sqMap β) δ)
      (hComp_assoc ops₃ laws₃ _ _ _)
      (hComp_assoc ops₃ laws₃ _ _ _)
  -- Step 6: Associativity on outer to get final form
  have s6 : HEq (ops₃.sqHComp (K.sqMap α) (ops₃.sqHComp γ' (ops₃.sqHComp (L.sqMap β) δ)))
                (ops₃.sqHComp (ops₃.sqHComp (K.sqMap α) γ') (ops₃.sqHComp (L.sqMap β) δ)) :=
    HEq.symm (sqHAssoc_heq ops₃ laws₃ (K.sqMap α) γ' (ops₃.sqHComp (L.sqMap β) δ))
  exact HEq.trans s1 (HEq.trans s2 (HEq.trans s3 (HEq.trans s4 (HEq.trans s5 s6))))

/-- Helper lemma for horizontal interchange: the app component equality. -/
theorem interchange_app_hor {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {Obj₃ : Type u₃}
    {vhs₃ : VertHomSet Obj₃} {hhs₃ : HorHomSet Obj₃} {sqs₃ : SquareSet vhs₃ hhs₃}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (ops₃ : DoubleCategoryOps Obj₃ vhs₃ hhs₃ sqs₃)
    (laws₃ : DoubleCategoryLaws ops₃)
    {F G H : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    {K L M : DoubleFunctorOps vhs₂ hhs₂ sqs₂ vhs₃ hhs₃ sqs₃}
    (klaws : DoubleFunctorLaws ops₂ ops₃ K)
    (τ : HorTransOps F G) (τ' : HorTransOps G H)
    (σ : HorTransOps K L) (σ' : HorTransOps L M)
    (σNat : HorTransNaturality ops₃ σ)
    (A : Obj₁) :
    ((τ.hComp ops₂ τ').vComp ops₃ (σ.hComp ops₃ σ')).app A
    = ((τ.vComp ops₃ σ).hComp ops₃ (τ'.vComp ops₃ σ')).app A := by
  simp only [HorTransOps.vComp, HorTransOps.hComp]
  rw [klaws.map_hComp]
  rw [hComp_assoc ops₃ laws₃ (K.horMap (τ.app A)) (K.horMap (τ'.app A))
        (ops₃.hComp (σ.app (H.objMap A)) (σ'.app (H.objMap A)))]
  rw [← hComp_assoc ops₃ laws₃ (K.horMap (τ'.app A)) (σ.app (H.objMap A))
        (σ'.app (H.objMap A))]
  rw [← σNat (τ'.app A)]
  rw [hComp_assoc ops₃ laws₃ (σ.app (G.objMap A)) (L.horMap (τ'.app A))
        (σ'.app (H.objMap A))]
  rw [← hComp_assoc ops₃ laws₃ (K.horMap (τ.app A)) (σ.app (G.objMap A))
        (ops₃.hComp (L.horMap (τ'.app A)) (σ'.app (H.objMap A)))]

/-- Interchange law for horizontal transformations.

For horizontal transformations τ, τ' (between F, G, H in D) and σ, σ'
(between K, L, M from E to E'), the interchange law states:

  (τ ⬝ₕ τ') ⬝ᵥ (σ ⬝ₕ σ') = (τ ⬝ᵥ σ) ⬝ₕ (τ' ⬝ᵥ σ')

This requires:
- K preserves horizontal composition (DoubleFunctorLaws)
- σ satisfies naturality with respect to horizontal morphisms (HorTransNaturality)
- σ satisfies square naturality (HorTransSquareNaturality)
- Associativity of horizontal composition in the target category -/
theorem HorTransOps.interchange {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {Obj₃ : Type u₃}
    {vhs₃ : VertHomSet Obj₃} {hhs₃ : HorHomSet Obj₃} {sqs₃ : SquareSet vhs₃ hhs₃}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (ops₃ : DoubleCategoryOps Obj₃ vhs₃ hhs₃ sqs₃)
    (laws₃ : DoubleCategoryLaws ops₃)
    {F G H : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    {K L M : DoubleFunctorOps vhs₂ hhs₂ sqs₂ vhs₃ hhs₃ sqs₃}
    (klaws : DoubleFunctorLaws ops₂ ops₃ K)
    (llaws : DoubleFunctorLaws ops₂ ops₃ L)
    (τ : HorTransOps F G) (τ' : HorTransOps G H)
    (σ : HorTransOps K L) (σ' : HorTransOps L M)
    (σlaws : HorTransLaws ops₂ ops₃ klaws llaws σ) :
    (τ.hComp ops₂ τ').vComp ops₃ (σ.hComp ops₃ σ')
    = (τ.vComp ops₃ σ).hComp ops₃ (τ'.vComp ops₃ σ') := by
  have h_app : ∀ A, ((τ.hComp ops₂ τ').vComp ops₃ (σ.hComp ops₃ σ')).app A
      = ((τ.vComp ops₃ σ).hComp ops₃ (τ'.vComp ops₃ σ')).app A :=
    interchange_app_hor ops₂ ops₃ laws₃ klaws τ τ' σ σ' σlaws.naturality
  apply eq_of_heq
  apply HorTransOps.heq_mk h_app
  intro A B v
  simp only [HorTransOps.hComp, HorTransOps.vComp]
  exact interchange_natSquare_hor ops₂ ops₃ laws₃ klaws τ τ' σ σ'
    σlaws.naturality σlaws.squareNaturality v

/-! ## Transformation Composition Laws

The following theorems prove that the identity and composition operations on
transformations satisfy the transformation laws.
-/

/-! ### Laws for Identity Vertical Transformation -/

/-- The identity vertical transformation satisfies VertTransLaws. -/
theorem VertTransOps.id_laws {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (_laws₁ : DoubleCategoryLaws ops₁)
    (laws₂ : DoubleCategoryLaws ops₂)
    (F : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂)
    (flaws : DoubleFunctorLaws ops₁ ops₂ F) :
    VertTransLaws ops₁ ops₂ flaws flaws (VertTransOps.id ops₂ F) where
  naturality := by
    intro A B v
    simp only [VertTransOps.id]
    have h1 := laws₂.vertLaws.id_laws.id_comp (F.vertMap v)
    have h2 := laws₂.vertLaws.id_laws.comp_id (F.vertMap v)
    simp only [DoubleCategoryOps.vertCategoryOps] at h1 h2
    exact h1.trans h2.symm
  squareNaturality := by
    intro A B C D v₁ v₂ h₁ h₂ α
    simp only [VertTransOps.id]
    exact HEq.trans (sqVCompId_heq ops₂ laws₂ (F.sqMap α))
      (HEq.symm (sqVIdComp_heq ops₂ laws₂ (F.sqMap α)))
  idCoherence := by
    intro A
    simp only [VertTransOps.id]
    have h1 : F.horMap (ops₁.hId A) = ops₂.hId (F.objMap A) := flaws.map_hId A
    have h2 := laws₂.sqLaws.idOnId (F.objMap A)
    exact h1.symm.recOn (motive := fun h' _ =>
        HEq (ops₂.sqVertId h') (ops₂.sqHorId (ops₂.vId (F.objMap A))))
      (heq_of_eq h2.symm)
  compCoherence := by
    intro A B C h h'
    simp only [VertTransOps.id]
    have h1 : F.horMap (ops₁.hComp h h') = ops₂.hComp (F.horMap h) (F.horMap h') :=
      flaws.map_hComp h h'
    have h2 := laws₂.sqLaws.horIdHComp (F.horMap h) (F.horMap h')
    exact h1.symm.recOn (motive := fun hx _ => HEq (ops₂.sqVertId hx)
        (ops₂.sqHComp (ops₂.sqVertId (F.horMap h)) (ops₂.sqVertId (F.horMap h'))))
      (heq_of_eq h2.symm)

/-- Vertical composition of vertical transformations satisfies VertTransLaws. -/
theorem VertTransOps.vComp_laws {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (_laws₁ : DoubleCategoryLaws ops₁)
    (laws₂ : DoubleCategoryLaws ops₂)
    {F G H : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (flaws : DoubleFunctorLaws ops₁ ops₂ F)
    (glaws : DoubleFunctorLaws ops₁ ops₂ G)
    (hlaws : DoubleFunctorLaws ops₁ ops₂ H)
    (τ : VertTransOps F G) (σ : VertTransOps G H)
    (τlaws : VertTransLaws ops₁ ops₂ flaws glaws τ)
    (σlaws : VertTransLaws ops₁ ops₂ glaws hlaws σ) :
    VertTransLaws ops₁ ops₂ flaws hlaws (VertTransOps.vComp ops₂ τ σ) where
  naturality := by
    intro A B v
    simp only [VertTransOps.vComp]
    have assoc := @laws₂.vertLaws.assoc
    simp only [DoubleCategoryOps.vertCategoryOps] at assoc
    calc ops₂.vComp (ops₂.vComp (τ.app A) (σ.app A)) (H.vertMap v)
        _ = ops₂.vComp (τ.app A) (ops₂.vComp (σ.app A) (H.vertMap v)) :=
            assoc (τ.app A) (σ.app A) (H.vertMap v)
        _ = ops₂.vComp (τ.app A) (ops₂.vComp (G.vertMap v) (σ.app B)) := by
            rw [σlaws.naturality]
        _ = ops₂.vComp (ops₂.vComp (τ.app A) (G.vertMap v)) (σ.app B) :=
            (assoc (τ.app A) (G.vertMap v) (σ.app B)).symm
        _ = ops₂.vComp (ops₂.vComp (F.vertMap v) (τ.app B)) (σ.app B) := by
            rw [τlaws.naturality]
        _ = ops₂.vComp (F.vertMap v) (ops₂.vComp (τ.app B) (σ.app B)) :=
            assoc (F.vertMap v) (τ.app B) (σ.app B)
  squareNaturality := by
    intro A B C D v₁ v₂ h₁ h₂ α
    simp only [VertTransOps.vComp]
    -- Goal: HEq (sqVComp (F.sqMap α) (sqVComp (τ.natSquare h₂) (σ.natSquare h₂)))
    --           (sqVComp (sqVComp (τ.natSquare h₁) (σ.natSquare h₁)) (H.sqMap α))
    -- Step 1: LHS associativity
    have s1 : HEq (ops₂.sqVComp (F.sqMap α) (ops₂.sqVComp (τ.natSquare h₂)
                      (σ.natSquare h₂)))
                  (ops₂.sqVComp (ops₂.sqVComp (F.sqMap α) (τ.natSquare h₂))
                      (σ.natSquare h₂)) :=
      HEq.symm (sqVAssoc_heq ops₂ laws₂ (F.sqMap α) (τ.natSquare h₂)
          (σ.natSquare h₂))
    -- Step 2: Apply τ's squareNaturality
    have s2 : HEq (ops₂.sqVComp (ops₂.sqVComp (F.sqMap α) (τ.natSquare h₂))
                      (σ.natSquare h₂))
                  (ops₂.sqVComp (ops₂.sqVComp (τ.natSquare h₁) (G.sqMap α))
                      (σ.natSquare h₂)) :=
      sqVComp_heq_left ops₂ (σ.natSquare h₂) (τlaws.squareNaturality α)
          (τlaws.naturality v₁).symm (τlaws.naturality v₂).symm
    -- Step 3: Associativity in middle
    have s3 : HEq (ops₂.sqVComp (ops₂.sqVComp (τ.natSquare h₁) (G.sqMap α))
                      (σ.natSquare h₂))
                  (ops₂.sqVComp (τ.natSquare h₁) (ops₂.sqVComp (G.sqMap α)
                      (σ.natSquare h₂))) :=
      sqVAssoc_heq ops₂ laws₂ (τ.natSquare h₁) (G.sqMap α) (σ.natSquare h₂)
    -- Step 4: Apply σ's squareNaturality
    have s4 : HEq (ops₂.sqVComp (τ.natSquare h₁) (ops₂.sqVComp (G.sqMap α)
                      (σ.natSquare h₂)))
                  (ops₂.sqVComp (τ.natSquare h₁) (ops₂.sqVComp (σ.natSquare h₁)
                      (H.sqMap α))) :=
      sqVComp_heq_right ops₂ (τ.natSquare h₁) (σlaws.squareNaturality α)
          (σlaws.naturality v₁).symm (σlaws.naturality v₂).symm
    -- Step 5: RHS associativity
    have s5 : HEq (ops₂.sqVComp (τ.natSquare h₁) (ops₂.sqVComp (σ.natSquare h₁)
                      (H.sqMap α)))
                  (ops₂.sqVComp (ops₂.sqVComp (τ.natSquare h₁) (σ.natSquare h₁))
                      (H.sqMap α)) :=
      HEq.symm (sqVAssoc_heq ops₂ laws₂ (τ.natSquare h₁) (σ.natSquare h₁)
          (H.sqMap α))
    exact HEq.trans s1 (HEq.trans s2 (HEq.trans s3 (HEq.trans s4 s5)))
  idCoherence := by
    intro A
    simp only [VertTransOps.vComp]
    have step1 := sqVComp_heq_both ops₂
        (τlaws.idCoherence A) (σlaws.idCoherence A)
        (flaws.map_hId A) (glaws.map_hId A) (hlaws.map_hId A)
    have step2 : ops₂.sqVComp (ops₂.sqHorId (τ.app A)) (ops₂.sqHorId (σ.app A)) =
        ops₂.sqHorId (ops₂.vComp (τ.app A) (σ.app A)) :=
      laws₂.sqLaws.vertIdVComp (τ.app A) (σ.app A)
    exact HEq.trans step1 (heq_of_eq step2)
  compCoherence := by
    intro A B C h h'
    simp only [VertTransOps.vComp]
    have step1 := sqVComp_heq_both ops₂
        (τlaws.compCoherence h h') (σlaws.compCoherence h h')
        (flaws.map_hComp h h') (glaws.map_hComp h h') (hlaws.map_hComp h h')
    have step2 : ops₂.sqVComp (ops₂.sqHComp (τ.natSquare h) (τ.natSquare h'))
                              (ops₂.sqHComp (σ.natSquare h) (σ.natSquare h')) =
                 ops₂.sqHComp (ops₂.sqVComp (τ.natSquare h) (σ.natSquare h))
                              (ops₂.sqVComp (τ.natSquare h') (σ.natSquare h')) :=
      laws₂.sqLaws.interchange (τ.natSquare h) (τ.natSquare h')
          (σ.natSquare h) (σ.natSquare h')
    exact HEq.trans step1 (heq_of_eq step2)

/-- Godement product (horizontal composition) of vertical transformations satisfies
VertTransLaws. -/
theorem VertTransOps.hComp_laws {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {Obj₃ : Type u₃}
    {vhs₃ : VertHomSet Obj₃} {hhs₃ : HorHomSet Obj₃} {sqs₃ : SquareSet vhs₃ hhs₃}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (ops₃ : DoubleCategoryOps Obj₃ vhs₃ hhs₃ sqs₃)
    (_laws₁ : DoubleCategoryLaws ops₁)
    (_laws₂ : DoubleCategoryLaws ops₂)
    (laws₃ : DoubleCategoryLaws ops₃)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    {H K : DoubleFunctorOps vhs₂ hhs₂ sqs₂ vhs₃ hhs₃ sqs₃}
    (flaws : DoubleFunctorLaws ops₁ ops₂ F)
    (glaws : DoubleFunctorLaws ops₁ ops₂ G)
    (hlaws : DoubleFunctorLaws ops₂ ops₃ H)
    (klaws : DoubleFunctorLaws ops₂ ops₃ K)
    (τ : VertTransOps F G) (σ : VertTransOps H K)
    (τlaws : VertTransLaws ops₁ ops₂ flaws glaws τ)
    (σlaws : VertTransLaws ops₂ ops₃ hlaws klaws σ) :
    VertTransLaws ops₁ ops₃
        (DoubleFunctorLaws.comp ops₁ ops₂ ops₃ flaws hlaws)
        (DoubleFunctorLaws.comp ops₁ ops₂ ops₃ glaws klaws)
        (VertTransOps.hComp ops₃ τ σ) where
  naturality := by
    intro A B v
    simp only [VertTransOps.hComp, DoubleFunctorOps.comp]
    -- Goal: (H.vertMap (τ.app A) ⬝ σ.app (G A)) ⬝ K(G(v)) =
    --       H(F(v)) ⬝ (H.vertMap (τ.app B) ⬝ σ.app (G B))
    have assoc := @laws₃.vertLaws.assoc
    simp only [DoubleCategoryOps.vertCategoryOps] at assoc
    calc ops₃.vComp (ops₃.vComp (H.vertMap (τ.app A)) (σ.app (G.objMap A)))
                    (K.vertMap (G.vertMap v))
        _ = ops₃.vComp (H.vertMap (τ.app A))
                       (ops₃.vComp (σ.app (G.objMap A)) (K.vertMap (G.vertMap v))) :=
            assoc _ _ _
        _ = ops₃.vComp (H.vertMap (τ.app A))
                       (ops₃.vComp (H.vertMap (G.vertMap v)) (σ.app (G.objMap B))) := by
            rw [σlaws.naturality (G.vertMap v)]
        _ = ops₃.vComp (ops₃.vComp (H.vertMap (τ.app A)) (H.vertMap (G.vertMap v)))
                       (σ.app (G.objMap B)) :=
            (assoc _ _ _).symm
        _ = ops₃.vComp (H.vertMap (ops₂.vComp (τ.app A) (G.vertMap v)))
                       (σ.app (G.objMap B)) := by
            rw [hlaws.map_vComp]
        _ = ops₃.vComp (H.vertMap (ops₂.vComp (F.vertMap v) (τ.app B)))
                       (σ.app (G.objMap B)) := by
            rw [τlaws.naturality v]
        _ = ops₃.vComp (ops₃.vComp (H.vertMap (F.vertMap v)) (H.vertMap (τ.app B)))
                       (σ.app (G.objMap B)) := by
            rw [hlaws.map_vComp]
        _ = ops₃.vComp (H.vertMap (F.vertMap v))
                       (ops₃.vComp (H.vertMap (τ.app B)) (σ.app (G.objMap B))) :=
            assoc _ _ _
  squareNaturality := by
    intro A B C D v₁ v₂ h₁ h₂ α
    simp only [VertTransOps.hComp, DoubleFunctorOps.comp]
    -- Goal: HEq (sqVComp (H.sqMap (F.sqMap α))
    --                     (sqVComp (H.sqMap (τ.natSquare h₂))
    --                              (σ.natSquare (G.horMap h₂))))
    --            (sqVComp (sqVComp (H.sqMap (τ.natSquare h₁))
    --                              (σ.natSquare (G.horMap h₁)))
    --                     (K.sqMap (G.sqMap α)))
    -- Step 1: Reassociate LHS - ((H(F(α)) ⬝ H(τ.natSq h₂)) ⬝ σ.natSq(G(h₂)))
    have s1 : HEq (ops₃.sqVComp (H.sqMap (F.sqMap α))
                      (ops₃.sqVComp (H.sqMap (τ.natSquare h₂))
                          (σ.natSquare (G.horMap h₂))))
                  (ops₃.sqVComp (ops₃.sqVComp (H.sqMap (F.sqMap α))
                      (H.sqMap (τ.natSquare h₂))) (σ.natSquare (G.horMap h₂))) :=
      HEq.symm (sqVAssoc_heq ops₃ laws₃ _ _ _)
    -- Step 2: Use H preserves sqVComp (reversed) to get H(F(α) ⬝ τ.natSq h₂)
    have s2 : HEq (ops₃.sqVComp (ops₃.sqVComp (H.sqMap (F.sqMap α))
                      (H.sqMap (τ.natSquare h₂))) (σ.natSquare (G.horMap h₂)))
                  (ops₃.sqVComp (H.sqMap (ops₂.sqVComp (F.sqMap α) (τ.natSquare h₂)))
                      (σ.natSquare (G.horMap h₂))) :=
      sqVComp_heq_left ops₃ _ (HEq.symm (hlaws.map_sqVComp (F.sqMap α)
          (τ.natSquare h₂))) (hlaws.map_vComp _ _).symm (hlaws.map_vComp _ _).symm
    -- Step 3: Use τ's squareNaturality (via H.sqMap)
    have s3 : HEq (ops₃.sqVComp (H.sqMap (ops₂.sqVComp (F.sqMap α) (τ.natSquare h₂)))
                      (σ.natSquare (G.horMap h₂)))
                  (ops₃.sqVComp (H.sqMap (ops₂.sqVComp (τ.natSquare h₁) (G.sqMap α)))
                      (σ.natSquare (G.horMap h₂))) := by
      have τnat := τlaws.squareNaturality α
      have heq_inner := sqMap_heq H τnat (τlaws.naturality v₁).symm
          (τlaws.naturality v₂).symm rfl rfl
      exact sqVComp_heq_left ops₃ _ heq_inner
          (congrArg H.vertMap (τlaws.naturality v₁).symm)
          (congrArg H.vertMap (τlaws.naturality v₂).symm)
    -- Step 4: Use H preserves sqVComp to expand
    have s4 : HEq (ops₃.sqVComp (H.sqMap (ops₂.sqVComp (τ.natSquare h₁) (G.sqMap α)))
                      (σ.natSquare (G.horMap h₂)))
                  (ops₃.sqVComp (ops₃.sqVComp (H.sqMap (τ.natSquare h₁))
                      (H.sqMap (G.sqMap α))) (σ.natSquare (G.horMap h₂))) :=
      sqVComp_heq_left ops₃ _ (hlaws.map_sqVComp (τ.natSquare h₁) (G.sqMap α))
          (hlaws.map_vComp _ _) (hlaws.map_vComp _ _)
    -- Step 5: Reassociate to get H(τ.natSq h₁) ⬝ (H(G(α)) ⬝ σ.natSq(G(h₂)))
    have s5 : HEq (ops₃.sqVComp (ops₃.sqVComp (H.sqMap (τ.natSquare h₁))
                      (H.sqMap (G.sqMap α))) (σ.natSquare (G.horMap h₂)))
                  (ops₃.sqVComp (H.sqMap (τ.natSquare h₁))
                      (ops₃.sqVComp (H.sqMap (G.sqMap α))
                          (σ.natSquare (G.horMap h₂)))) :=
      sqVAssoc_heq ops₃ laws₃ _ _ _
    -- Step 6: Apply σ's squareNaturality
    have s6 : HEq (ops₃.sqVComp (H.sqMap (τ.natSquare h₁))
                      (ops₃.sqVComp (H.sqMap (G.sqMap α))
                          (σ.natSquare (G.horMap h₂))))
                  (ops₃.sqVComp (H.sqMap (τ.natSquare h₁))
                      (ops₃.sqVComp (σ.natSquare (G.horMap h₁))
                          (K.sqMap (G.sqMap α)))) :=
      sqVComp_heq_right ops₃ _ (σlaws.squareNaturality (G.sqMap α))
          (σlaws.naturality (G.vertMap v₁)).symm (σlaws.naturality (G.vertMap v₂)).symm
    -- Step 7: Final reassociation
    have s7 : HEq (ops₃.sqVComp (H.sqMap (τ.natSquare h₁))
                      (ops₃.sqVComp (σ.natSquare (G.horMap h₁))
                          (K.sqMap (G.sqMap α))))
                  (ops₃.sqVComp (ops₃.sqVComp (H.sqMap (τ.natSquare h₁))
                      (σ.natSquare (G.horMap h₁))) (K.sqMap (G.sqMap α))) :=
      HEq.symm (sqVAssoc_heq ops₃ laws₃ _ _ _)
    exact HEq.trans s1 (HEq.trans s2 (HEq.trans s3 (HEq.trans s4
        (HEq.trans s5 (HEq.trans s6 s7)))))
  idCoherence := by
    intro A
    simp only [VertTransOps.hComp, DoubleFunctorOps.comp]
    have ghid : G.horMap (ops₁.hId A) = ops₂.hId (G.objMap A) := glaws.map_hId A
    have fhid : F.horMap (ops₁.hId A) = ops₂.hId (F.objMap A) := flaws.map_hId A
    have hghid : H.horMap (G.horMap (ops₁.hId A)) = H.horMap (ops₂.hId (G.objMap A)) :=
      congrArg H.horMap ghid
    have hhfid : H.horMap (ops₂.hId (F.objMap A)) = ops₃.hId (H.objMap (F.objMap A)) :=
      hlaws.map_hId (F.objMap A)
    have hhgid : H.horMap (ops₂.hId (G.objMap A)) = ops₃.hId (H.objMap (G.objMap A)) :=
      hlaws.map_hId (G.objMap A)
    have kghid : K.horMap (G.horMap (ops₁.hId A)) = K.horMap (ops₂.hId (G.objMap A)) :=
      congrArg K.horMap ghid
    have kkgid : K.horMap (ops₂.hId (G.objMap A)) = ops₃.hId (K.objMap (G.objMap A)) :=
      klaws.map_hId (G.objMap A)
    -- Step 1: Transport σ's argument via ghid (dependent HEq)
    have σarg : HEq (σ.natSquare (G.horMap (ops₁.hId A)))
                    (σ.natSquare (ops₂.hId (G.objMap A))) :=
      Eq.rec (motive := fun h _ => HEq (σ.natSquare (G.horMap (ops₁.hId A)))
                                       (σ.natSquare h))
             HEq.rfl ghid
    -- Step 2: Apply τ's idCoherence through sqMap
    have τidcoh : HEq (H.sqMap (τ.natSquare (ops₁.hId A)))
                      (H.sqMap (ops₂.sqHorId (τ.app A))) :=
      sqMap_heq H (τlaws.idCoherence A) rfl rfl fhid ghid
    -- Step 3: Combine steps 1 and 2
    have s12 := sqVComp_heq_both ops₃ τidcoh σarg
        (congrArg H.horMap fhid) hghid kghid
    -- Step 4: Convert H.sqMap (sqHorId τ) to sqHorId (H.vert τ) and apply σ's idCoherence
    have hpres : HEq (H.sqMap (ops₂.sqHorId (τ.app A)))
                     (ops₃.sqHorId (H.vertMap (τ.app A))) :=
      hlaws.map_sqHorId (τ.app A)
    have σidcoh : HEq (σ.natSquare (ops₂.hId (G.objMap A)))
                      (ops₃.sqHorId (σ.app (G.objMap A))) :=
      σlaws.idCoherence (G.objMap A)
    have s34 := sqVComp_heq_both ops₃ hpres σidcoh hhfid hhgid kkgid
    -- Step 5: Use vertIdVComp
    have s5 : ops₃.sqVComp (ops₃.sqHorId (H.vertMap (τ.app A)))
                           (ops₃.sqHorId (σ.app (G.objMap A))) =
              ops₃.sqHorId (ops₃.vComp (H.vertMap (τ.app A)) (σ.app (G.objMap A))) :=
      laws₃.sqLaws.vertIdVComp _ _
    exact HEq.trans s12 (HEq.trans s34 (heq_of_eq s5))
  compCoherence := by
    intro A B C h h'
    simp only [VertTransOps.hComp, DoubleFunctorOps.comp]
    -- Goal: HEq (sqVComp (H.sqMap (τ.natSquare (hComp h h')))
    --                    (σ.natSquare (G.horMap (hComp h h'))))
    --           (sqHComp (sqVComp (H.sqMap (τ.natSquare h)) (σ.natSquare (G.horMap h)))
    --                    (sqVComp (H.sqMap (τ.natSquare h')) (σ.natSquare (G.horMap h'))))
    -- Step 1: Apply τ's compCoherence through H.sqMap
    have τcomp : HEq (H.sqMap (τ.natSquare (ops₁.hComp h h')))
                     (H.sqMap (ops₂.sqHComp (τ.natSquare h) (τ.natSquare h'))) :=
      sqMap_heq H (τlaws.compCoherence h h')
          rfl rfl (flaws.map_hComp h h') (glaws.map_hComp h h')
    -- Step 2: Apply H preserves sqHComp
    have hcomp : HEq (H.sqMap (ops₂.sqHComp (τ.natSquare h) (τ.natSquare h')))
                     (ops₃.sqHComp (H.sqMap (τ.natSquare h)) (H.sqMap (τ.natSquare h'))) :=
      hlaws.map_sqHComp (τ.natSquare h) (τ.natSquare h')
    have s12 : HEq (H.sqMap (τ.natSquare (ops₁.hComp h h')))
                   (ops₃.sqHComp (H.sqMap (τ.natSquare h)) (H.sqMap (τ.natSquare h'))) :=
      HEq.trans τcomp hcomp
    -- Step 3: Transport σ's argument via G preserves hComp
    have gcomp : G.horMap (ops₁.hComp h h') = ops₂.hComp (G.horMap h) (G.horMap h') :=
      glaws.map_hComp h h'
    have σtrans : HEq (σ.natSquare (G.horMap (ops₁.hComp h h')))
                      (σ.natSquare (ops₂.hComp (G.horMap h) (G.horMap h'))) :=
      Eq.rec (motive := fun x _ => HEq (σ.natSquare (G.horMap (ops₁.hComp h h')))
                                       (σ.natSquare x))
             HEq.rfl gcomp
    -- Step 4: Apply σ's compCoherence
    have σcomp : HEq (σ.natSquare (ops₂.hComp (G.horMap h) (G.horMap h')))
                     (ops₃.sqHComp (σ.natSquare (G.horMap h)) (σ.natSquare (G.horMap h'))) :=
      σlaws.compCoherence (G.horMap h) (G.horMap h')
    have s34 : HEq (σ.natSquare (G.horMap (ops₁.hComp h h')))
                   (ops₃.sqHComp (σ.natSquare (G.horMap h)) (σ.natSquare (G.horMap h'))) :=
      HEq.trans σtrans σcomp
    -- Step 5: Combine using sqVComp_heq_both
    have hghcomp : H.horMap (G.horMap (ops₁.hComp h h')) =
                   ops₃.hComp (H.horMap (G.horMap h)) (H.horMap (G.horMap h')) :=
      (congrArg H.horMap gcomp).trans (hlaws.map_hComp (G.horMap h) (G.horMap h'))
    have kghcomp : K.horMap (G.horMap (ops₁.hComp h h')) =
                   ops₃.hComp (K.horMap (G.horMap h)) (K.horMap (G.horMap h')) :=
      (congrArg K.horMap gcomp).trans (klaws.map_hComp (G.horMap h) (G.horMap h'))
    have hfhcomp : H.horMap (F.horMap (ops₁.hComp h h')) =
                   ops₃.hComp (H.horMap (F.horMap h)) (H.horMap (F.horMap h')) :=
      (congrArg H.horMap (flaws.map_hComp h h')).trans
        (hlaws.map_hComp (F.horMap h) (F.horMap h'))
    have s5 := sqVComp_heq_both ops₃ s12 s34 hfhcomp hghcomp kghcomp
    -- Step 6: Apply interchange law
    have s6 : ops₃.sqVComp (ops₃.sqHComp (H.sqMap (τ.natSquare h))
                                         (H.sqMap (τ.natSquare h')))
                           (ops₃.sqHComp (σ.natSquare (G.horMap h))
                                         (σ.natSquare (G.horMap h'))) =
              ops₃.sqHComp (ops₃.sqVComp (H.sqMap (τ.natSquare h))
                                         (σ.natSquare (G.horMap h)))
                           (ops₃.sqVComp (H.sqMap (τ.natSquare h'))
                                         (σ.natSquare (G.horMap h'))) :=
      laws₃.sqLaws.interchange _ _ _ _
    exact HEq.trans s5 (heq_of_eq s6)

/-! ### Laws for Identity Horizontal Transformation -/

/-- The identity horizontal transformation satisfies HorTransLaws. -/
theorem HorTransOps.id_laws {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (_laws₁ : DoubleCategoryLaws ops₁)
    (laws₂ : DoubleCategoryLaws ops₂)
    (F : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂)
    (flaws : DoubleFunctorLaws ops₁ ops₂ F) :
    HorTransLaws ops₁ ops₂ flaws flaws (HorTransOps.id ops₂ F) where
  naturality := by
    intro A B h
    simp only [HorTransOps.id]
    have h1 := laws₂.horLaws.id_laws.id_comp (F.horMap h)
    have h2 := laws₂.horLaws.id_laws.comp_id (F.horMap h)
    simp only [DoubleCategoryOps.horCategoryOps] at h1 h2
    exact h1.trans h2.symm
  squareNaturality := by
    intro A B C D v₁ v₂ h₁ h₂ α
    simp only [HorTransOps.id]
    exact HEq.trans (sqHCompId_heq ops₂ laws₂ (F.sqMap α))
      (HEq.symm (sqHIdComp_heq ops₂ laws₂ (F.sqMap α)))
  idCoherence := by
    intro A
    simp only [HorTransOps.id]
    have h1 : F.vertMap (ops₁.vId A) = ops₂.vId (F.objMap A) := flaws.map_vId A
    have h2 := laws₂.sqLaws.idOnId (F.objMap A)
    exact h1.symm.recOn (motive := fun v' _ =>
        HEq (ops₂.sqHorId v') (ops₂.sqVertId (ops₂.hId (F.objMap A))))
      (heq_of_eq h2)
  compCoherence := by
    intro A C E v v'
    simp only [HorTransOps.id]
    have h1 : F.vertMap (ops₁.vComp v v') = ops₂.vComp (F.vertMap v) (F.vertMap v') :=
      flaws.map_vComp v v'
    have h2 := laws₂.sqLaws.vertIdVComp (F.vertMap v) (F.vertMap v')
    exact h1.symm.recOn (motive := fun vx _ => HEq (ops₂.sqHorId vx)
        (ops₂.sqVComp (ops₂.sqHorId (F.vertMap v)) (ops₂.sqHorId (F.vertMap v'))))
      (heq_of_eq h2.symm)

/-- Horizontal composition of horizontal transformations satisfies HorTransLaws. -/
theorem HorTransOps.hComp_laws {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (_laws₁ : DoubleCategoryLaws ops₁)
    (laws₂ : DoubleCategoryLaws ops₂)
    {F G H : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (flaws : DoubleFunctorLaws ops₁ ops₂ F)
    (glaws : DoubleFunctorLaws ops₁ ops₂ G)
    (hlaws : DoubleFunctorLaws ops₁ ops₂ H)
    (τ : HorTransOps F G) (σ : HorTransOps G H)
    (τlaws : HorTransLaws ops₁ ops₂ flaws glaws τ)
    (σlaws : HorTransLaws ops₁ ops₂ glaws hlaws σ) :
    HorTransLaws ops₁ ops₂ flaws hlaws (HorTransOps.hComp ops₂ τ σ) where
  naturality := by
    intro A B h
    simp only [HorTransOps.hComp]
    have assoc := @laws₂.horLaws.assoc
    simp only [DoubleCategoryOps.horCategoryOps] at assoc
    calc ops₂.hComp (ops₂.hComp (τ.app A) (σ.app A)) (H.horMap h)
        _ = ops₂.hComp (τ.app A) (ops₂.hComp (σ.app A) (H.horMap h)) :=
            assoc (τ.app A) (σ.app A) (H.horMap h)
        _ = ops₂.hComp (τ.app A) (ops₂.hComp (G.horMap h) (σ.app B)) := by
            rw [σlaws.naturality]
        _ = ops₂.hComp (ops₂.hComp (τ.app A) (G.horMap h)) (σ.app B) :=
            (assoc (τ.app A) (G.horMap h) (σ.app B)).symm
        _ = ops₂.hComp (ops₂.hComp (F.horMap h) (τ.app B)) (σ.app B) := by
            rw [τlaws.naturality]
        _ = ops₂.hComp (F.horMap h) (ops₂.hComp (τ.app B) (σ.app B)) :=
            assoc (F.horMap h) (τ.app B) (σ.app B)
  squareNaturality := by
    intro A B C D v₁ v₂ h₁ h₂ α
    simp only [HorTransOps.hComp]
    have s1 : HEq (ops₂.sqHComp (F.sqMap α) (ops₂.sqHComp (τ.natSquare v₂)
                      (σ.natSquare v₂)))
                  (ops₂.sqHComp (ops₂.sqHComp (F.sqMap α) (τ.natSquare v₂))
                      (σ.natSquare v₂)) :=
      HEq.symm (sqHAssoc_heq ops₂ laws₂ (F.sqMap α) (τ.natSquare v₂) (σ.natSquare v₂))
    have s2 : HEq (ops₂.sqHComp (ops₂.sqHComp (F.sqMap α) (τ.natSquare v₂))
                      (σ.natSquare v₂))
                  (ops₂.sqHComp (ops₂.sqHComp (τ.natSquare v₁) (G.sqMap α))
                      (σ.natSquare v₂)) :=
      sqHComp_heq_left ops₂ (σ.natSquare v₂) (τlaws.squareNaturality α)
          (τlaws.naturality h₁).symm (τlaws.naturality h₂).symm
    have s3 : HEq (ops₂.sqHComp (ops₂.sqHComp (τ.natSquare v₁) (G.sqMap α))
                      (σ.natSquare v₂))
                  (ops₂.sqHComp (τ.natSquare v₁) (ops₂.sqHComp (G.sqMap α)
                      (σ.natSquare v₂))) :=
      sqHAssoc_heq ops₂ laws₂ (τ.natSquare v₁) (G.sqMap α) (σ.natSquare v₂)
    have s4 : HEq (ops₂.sqHComp (τ.natSquare v₁) (ops₂.sqHComp (G.sqMap α)
                      (σ.natSquare v₂)))
                  (ops₂.sqHComp (τ.natSquare v₁) (ops₂.sqHComp (σ.natSquare v₁)
                      (H.sqMap α))) :=
      sqHComp_heq_right ops₂ (τ.natSquare v₁) (σlaws.squareNaturality α)
          (σlaws.naturality h₁).symm (σlaws.naturality h₂).symm
    have s5 : HEq (ops₂.sqHComp (τ.natSquare v₁) (ops₂.sqHComp (σ.natSquare v₁)
                      (H.sqMap α)))
                  (ops₂.sqHComp (ops₂.sqHComp (τ.natSquare v₁) (σ.natSquare v₁))
                      (H.sqMap α)) :=
      HEq.symm (sqHAssoc_heq ops₂ laws₂ (τ.natSquare v₁) (σ.natSquare v₁) (H.sqMap α))
    exact HEq.trans s1 (HEq.trans s2 (HEq.trans s3 (HEq.trans s4 s5)))
  idCoherence := by
    intro A
    simp only [HorTransOps.hComp]
    have step1 := sqHComp_heq_both ops₂
        (τlaws.idCoherence A) (σlaws.idCoherence A)
        (flaws.map_vId A) (glaws.map_vId A) (hlaws.map_vId A)
    have step2 : ops₂.sqHComp (ops₂.sqVertId (τ.app A)) (ops₂.sqVertId (σ.app A)) =
        ops₂.sqVertId (ops₂.hComp (τ.app A) (σ.app A)) :=
      laws₂.sqLaws.horIdHComp (τ.app A) (σ.app A)
    exact HEq.trans step1 (heq_of_eq step2)
  compCoherence := by
    intro A C E v v'
    simp only [HorTransOps.hComp]
    have step1 := sqHComp_heq_both ops₂
        (τlaws.compCoherence v v') (σlaws.compCoherence v v')
        (flaws.map_vComp v v') (glaws.map_vComp v v') (hlaws.map_vComp v v')
    have step2 : ops₂.sqHComp (ops₂.sqVComp (τ.natSquare v) (τ.natSquare v'))
                              (ops₂.sqVComp (σ.natSquare v) (σ.natSquare v')) =
                 ops₂.sqVComp (ops₂.sqHComp (τ.natSquare v) (σ.natSquare v))
                              (ops₂.sqHComp (τ.natSquare v') (σ.natSquare v')) :=
      (laws₂.sqLaws.interchange (τ.natSquare v) (σ.natSquare v)
          (τ.natSquare v') (σ.natSquare v')).symm
    exact HEq.trans step1 (heq_of_eq step2)

/-! ### Laws for Godement Product of Horizontal Transformations -/

/-- The Godement product (vertical composition) of horizontal transformations
satisfies HorTransLaws.

For horizontal transformations τ : F ⟹ₕ G between double categories D₁ and D₂,
and σ : H ⟹ₕ K between D₂ and D₃, the Godement product (vComp τ σ) is a
horizontal transformation (F ∘ H) ⟹ₕ (G ∘ K). -/
theorem HorTransOps.vComp_laws {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {Obj₃ : Type u₃}
    {vhs₃ : VertHomSet Obj₃} {hhs₃ : HorHomSet Obj₃} {sqs₃ : SquareSet vhs₃ hhs₃}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (ops₃ : DoubleCategoryOps Obj₃ vhs₃ hhs₃ sqs₃)
    (_laws₁ : DoubleCategoryLaws ops₁)
    (_laws₂ : DoubleCategoryLaws ops₂)
    (laws₃ : DoubleCategoryLaws ops₃)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    {H K : DoubleFunctorOps vhs₂ hhs₂ sqs₂ vhs₃ hhs₃ sqs₃}
    (flaws : DoubleFunctorLaws ops₁ ops₂ F)
    (glaws : DoubleFunctorLaws ops₁ ops₂ G)
    (hlaws : DoubleFunctorLaws ops₂ ops₃ H)
    (klaws : DoubleFunctorLaws ops₂ ops₃ K)
    (τ : HorTransOps F G) (σ : HorTransOps H K)
    (τlaws : HorTransLaws ops₁ ops₂ flaws glaws τ)
    (σlaws : HorTransLaws ops₂ ops₃ hlaws klaws σ) :
    HorTransLaws ops₁ ops₃
        (DoubleFunctorLaws.comp ops₁ ops₂ ops₃ flaws hlaws)
        (DoubleFunctorLaws.comp ops₁ ops₂ ops₃ glaws klaws)
        (HorTransOps.vComp ops₃ τ σ) where
  naturality := by
    intro A B h
    simp only [HorTransOps.vComp, DoubleFunctorOps.comp]
    have assoc := @laws₃.horLaws.assoc
    simp only [DoubleCategoryOps.horCategoryOps] at assoc
    calc ops₃.hComp (ops₃.hComp (H.horMap (τ.app A)) (σ.app (G.objMap A)))
                    (K.horMap (G.horMap h))
        _ = ops₃.hComp (H.horMap (τ.app A))
                       (ops₃.hComp (σ.app (G.objMap A)) (K.horMap (G.horMap h))) :=
            assoc _ _ _
        _ = ops₃.hComp (H.horMap (τ.app A))
                       (ops₃.hComp (H.horMap (G.horMap h)) (σ.app (G.objMap B))) := by
            rw [σlaws.naturality (G.horMap h)]
        _ = ops₃.hComp (ops₃.hComp (H.horMap (τ.app A)) (H.horMap (G.horMap h)))
                       (σ.app (G.objMap B)) :=
            (assoc _ _ _).symm
        _ = ops₃.hComp (H.horMap (ops₂.hComp (τ.app A) (G.horMap h)))
                       (σ.app (G.objMap B)) := by
            rw [← hlaws.map_hComp]
        _ = ops₃.hComp (H.horMap (ops₂.hComp (F.horMap h) (τ.app B)))
                       (σ.app (G.objMap B)) := by
            rw [τlaws.naturality h]
        _ = ops₃.hComp (ops₃.hComp (H.horMap (F.horMap h)) (H.horMap (τ.app B)))
                       (σ.app (G.objMap B)) := by
            rw [hlaws.map_hComp]
        _ = ops₃.hComp (H.horMap (F.horMap h))
                       (ops₃.hComp (H.horMap (τ.app B)) (σ.app (G.objMap B))) :=
            assoc _ _ _
  squareNaturality := by
    intro A B C D v₁ v₂ h₁ h₂ α
    simp only [HorTransOps.vComp, DoubleFunctorOps.comp]
    -- HorTransOps.natSquare takes a vertical morphism, so use v₁, v₂
    have s1 : HEq (ops₃.sqHComp (H.sqMap (F.sqMap α))
                      (ops₃.sqHComp (H.sqMap (τ.natSquare v₂))
                          (σ.natSquare (G.vertMap v₂))))
                  (ops₃.sqHComp (ops₃.sqHComp (H.sqMap (F.sqMap α))
                      (H.sqMap (τ.natSquare v₂))) (σ.natSquare (G.vertMap v₂))) :=
      HEq.symm (sqHAssoc_heq ops₃ laws₃ _ _ _)
    have s2 : HEq (ops₃.sqHComp (ops₃.sqHComp (H.sqMap (F.sqMap α))
                      (H.sqMap (τ.natSquare v₂))) (σ.natSquare (G.vertMap v₂)))
                  (ops₃.sqHComp (H.sqMap (ops₂.sqHComp (F.sqMap α) (τ.natSquare v₂)))
                      (σ.natSquare (G.vertMap v₂))) :=
      sqHComp_heq_left ops₃ _ (HEq.symm (hlaws.map_sqHComp (F.sqMap α)
          (τ.natSquare v₂))) (hlaws.map_hComp _ _).symm (hlaws.map_hComp _ _).symm
    have s3 : HEq (ops₃.sqHComp (H.sqMap (ops₂.sqHComp (F.sqMap α) (τ.natSquare v₂)))
                      (σ.natSquare (G.vertMap v₂)))
                  (ops₃.sqHComp (H.sqMap (ops₂.sqHComp (τ.natSquare v₁) (G.sqMap α)))
                      (σ.natSquare (G.vertMap v₂))) := by
      have τnat := τlaws.squareNaturality α
      have heq_inner := sqMap_heq H τnat rfl rfl
          (τlaws.naturality h₁).symm (τlaws.naturality h₂).symm
      exact sqHComp_heq_left ops₃ _ heq_inner
          (congrArg H.horMap (τlaws.naturality h₁).symm)
          (congrArg H.horMap (τlaws.naturality h₂).symm)
    have s4 : HEq (ops₃.sqHComp (H.sqMap (ops₂.sqHComp (τ.natSquare v₁) (G.sqMap α)))
                      (σ.natSquare (G.vertMap v₂)))
                  (ops₃.sqHComp (ops₃.sqHComp (H.sqMap (τ.natSquare v₁))
                      (H.sqMap (G.sqMap α))) (σ.natSquare (G.vertMap v₂))) :=
      sqHComp_heq_left ops₃ _ (hlaws.map_sqHComp (τ.natSquare v₁) (G.sqMap α))
          (hlaws.map_hComp _ _) (hlaws.map_hComp _ _)
    have s5 : HEq (ops₃.sqHComp (ops₃.sqHComp (H.sqMap (τ.natSquare v₁))
                      (H.sqMap (G.sqMap α))) (σ.natSquare (G.vertMap v₂)))
                  (ops₃.sqHComp (H.sqMap (τ.natSquare v₁))
                      (ops₃.sqHComp (H.sqMap (G.sqMap α))
                          (σ.natSquare (G.vertMap v₂)))) :=
      sqHAssoc_heq ops₃ laws₃ _ _ _
    have s6 : HEq (ops₃.sqHComp (H.sqMap (τ.natSquare v₁))
                      (ops₃.sqHComp (H.sqMap (G.sqMap α))
                          (σ.natSquare (G.vertMap v₂))))
                  (ops₃.sqHComp (H.sqMap (τ.natSquare v₁))
                      (ops₃.sqHComp (σ.natSquare (G.vertMap v₁))
                          (K.sqMap (G.sqMap α)))) :=
      sqHComp_heq_right ops₃ _ (σlaws.squareNaturality (G.sqMap α))
          (σlaws.naturality (G.horMap h₁)).symm (σlaws.naturality (G.horMap h₂)).symm
    have s7 : HEq (ops₃.sqHComp (H.sqMap (τ.natSquare v₁))
                      (ops₃.sqHComp (σ.natSquare (G.vertMap v₁))
                          (K.sqMap (G.sqMap α))))
                  (ops₃.sqHComp (ops₃.sqHComp (H.sqMap (τ.natSquare v₁))
                      (σ.natSquare (G.vertMap v₁))) (K.sqMap (G.sqMap α))) :=
      HEq.symm (sqHAssoc_heq ops₃ laws₃ _ _ _)
    exact HEq.trans s1 (HEq.trans s2 (HEq.trans s3 (HEq.trans s4
        (HEq.trans s5 (HEq.trans s6 s7)))))
  idCoherence := by
    intro A
    simp only [HorTransOps.vComp, DoubleFunctorOps.comp]
    have gvid : G.vertMap (ops₁.vId A) = ops₂.vId (G.objMap A) := glaws.map_vId A
    have fvid : F.vertMap (ops₁.vId A) = ops₂.vId (F.objMap A) := flaws.map_vId A
    have hgvid : H.vertMap (G.vertMap (ops₁.vId A)) = H.vertMap (ops₂.vId (G.objMap A)) :=
      congrArg H.vertMap gvid
    have hhfid : H.vertMap (ops₂.vId (F.objMap A)) = ops₃.vId (H.objMap (F.objMap A)) :=
      hlaws.map_vId (F.objMap A)
    have hhgid : H.vertMap (ops₂.vId (G.objMap A)) = ops₃.vId (H.objMap (G.objMap A)) :=
      hlaws.map_vId (G.objMap A)
    have kgvid : K.vertMap (G.vertMap (ops₁.vId A)) = K.vertMap (ops₂.vId (G.objMap A)) :=
      congrArg K.vertMap gvid
    have kkgid : K.vertMap (ops₂.vId (G.objMap A)) = ops₃.vId (K.objMap (G.objMap A)) :=
      klaws.map_vId (G.objMap A)
    have σarg : HEq (σ.natSquare (G.vertMap (ops₁.vId A)))
                    (σ.natSquare (ops₂.vId (G.objMap A))) :=
      Eq.rec (motive := fun v _ => HEq (σ.natSquare (G.vertMap (ops₁.vId A)))
                                       (σ.natSquare v))
             HEq.rfl gvid
    have τidcoh : HEq (H.sqMap (τ.natSquare (ops₁.vId A)))
                      (H.sqMap (ops₂.sqVertId (τ.app A))) :=
      sqMap_heq H (τlaws.idCoherence A) fvid gvid rfl rfl
    have s12 := sqHComp_heq_both ops₃ τidcoh σarg
        (congrArg H.vertMap fvid) hgvid kgvid
    have hpres : HEq (H.sqMap (ops₂.sqVertId (τ.app A)))
                     (ops₃.sqVertId (H.horMap (τ.app A))) :=
      hlaws.map_sqVertId (τ.app A)
    have σidcoh : HEq (σ.natSquare (ops₂.vId (G.objMap A)))
                      (ops₃.sqVertId (σ.app (G.objMap A))) :=
      σlaws.idCoherence (G.objMap A)
    have s34 := sqHComp_heq_both ops₃ hpres σidcoh hhfid hhgid kkgid
    have s5 : ops₃.sqHComp (ops₃.sqVertId (H.horMap (τ.app A)))
                           (ops₃.sqVertId (σ.app (G.objMap A))) =
              ops₃.sqVertId (ops₃.hComp (H.horMap (τ.app A)) (σ.app (G.objMap A))) :=
      laws₃.sqLaws.horIdHComp _ _
    exact HEq.trans s12 (HEq.trans s34 (heq_of_eq s5))
  compCoherence := by
    intro A B C v v'
    simp only [HorTransOps.vComp, DoubleFunctorOps.comp]
    have τcomp : HEq (H.sqMap (τ.natSquare (ops₁.vComp v v')))
                     (H.sqMap (ops₂.sqVComp (τ.natSquare v) (τ.natSquare v'))) :=
      sqMap_heq H (τlaws.compCoherence v v')
          (flaws.map_vComp v v') (glaws.map_vComp v v') rfl rfl
    have hvcomp : HEq (H.sqMap (ops₂.sqVComp (τ.natSquare v) (τ.natSquare v')))
                      (ops₃.sqVComp (H.sqMap (τ.natSquare v)) (H.sqMap (τ.natSquare v'))) :=
      hlaws.map_sqVComp (τ.natSquare v) (τ.natSquare v')
    have s12 : HEq (H.sqMap (τ.natSquare (ops₁.vComp v v')))
                   (ops₃.sqVComp (H.sqMap (τ.natSquare v)) (H.sqMap (τ.natSquare v'))) :=
      HEq.trans τcomp hvcomp
    have gvcomp : G.vertMap (ops₁.vComp v v') = ops₂.vComp (G.vertMap v) (G.vertMap v') :=
      glaws.map_vComp v v'
    have σtrans : HEq (σ.natSquare (G.vertMap (ops₁.vComp v v')))
                      (σ.natSquare (ops₂.vComp (G.vertMap v) (G.vertMap v'))) :=
      Eq.rec (motive := fun x _ => HEq (σ.natSquare (G.vertMap (ops₁.vComp v v')))
                                       (σ.natSquare x))
             HEq.rfl gvcomp
    have σcomp : HEq (σ.natSquare (ops₂.vComp (G.vertMap v) (G.vertMap v')))
                     (ops₃.sqVComp (σ.natSquare (G.vertMap v)) (σ.natSquare (G.vertMap v'))) :=
      σlaws.compCoherence (G.vertMap v) (G.vertMap v')
    have s34 : HEq (σ.natSquare (G.vertMap (ops₁.vComp v v')))
                   (ops₃.sqVComp (σ.natSquare (G.vertMap v)) (σ.natSquare (G.vertMap v'))) :=
      HEq.trans σtrans σcomp
    have hgvcomp : H.vertMap (G.vertMap (ops₁.vComp v v')) =
                   ops₃.vComp (H.vertMap (G.vertMap v)) (H.vertMap (G.vertMap v')) :=
      (congrArg H.vertMap gvcomp).trans (hlaws.map_vComp (G.vertMap v) (G.vertMap v'))
    have kgvcomp : K.vertMap (G.vertMap (ops₁.vComp v v')) =
                   ops₃.vComp (K.vertMap (G.vertMap v)) (K.vertMap (G.vertMap v')) :=
      (congrArg K.vertMap gvcomp).trans (klaws.map_vComp (G.vertMap v) (G.vertMap v'))
    have hfvcomp : H.vertMap (F.vertMap (ops₁.vComp v v')) =
                   ops₃.vComp (H.vertMap (F.vertMap v)) (H.vertMap (F.vertMap v')) :=
      (congrArg H.vertMap (flaws.map_vComp v v')).trans
        (hlaws.map_vComp (F.vertMap v) (F.vertMap v'))
    have s5 := sqHComp_heq_both ops₃ s12 s34 hfvcomp hgvcomp kgvcomp
    have s6 : ops₃.sqHComp (ops₃.sqVComp (H.sqMap (τ.natSquare v))
                                         (H.sqMap (τ.natSquare v')))
                           (ops₃.sqVComp (σ.natSquare (G.vertMap v))
                                         (σ.natSquare (G.vertMap v'))) =
              ops₃.sqVComp (ops₃.sqHComp (H.sqMap (τ.natSquare v))
                                         (σ.natSquare (G.vertMap v)))
                           (ops₃.sqHComp (H.sqMap (τ.natSquare v'))
                                         (σ.natSquare (G.vertMap v'))) :=
      (laws₃.sqLaws.interchange _ _ _ _).symm
    exact HEq.trans s5 (heq_of_eq s6)

end GebLean
