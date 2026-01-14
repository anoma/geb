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

/-- Congruence for sqVComp when all boundaries may change via equality proofs.

This version allows vertical boundaries to vary via equality proofs while
keeping the same objects. Use sqVComp_heq_both when only horizontal boundaries
change. -/
theorem sqVComp_heq_all {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs)
    {A B C D E F : Obj}
    {v₁ v₁' : vhs A C} {v₂ v₂' : vhs B D} {w₁ w₁' : vhs C E} {w₂ w₂' : vhs D F}
    {h₁ h₁' : hhs A B} {h₂ h₂' : hhs C D} {h₃ h₃' : hhs E F}
    {α : sqs v₁ v₂ h₁ h₂} {β : sqs w₁ w₂ h₂ h₃}
    {α' : sqs v₁' v₂' h₁' h₂'} {β' : sqs w₁' w₂' h₂' h₃'}
    (hα : HEq α α') (hβ : HEq β β')
    (hv₁ : v₁ = v₁') (hv₂ : v₂ = v₂') (hw₁ : w₁ = w₁') (hw₂ : w₂ = w₂')
    (htop : h₁ = h₁') (hmid : h₂ = h₂') (hbot : h₃ = h₃') :
    HEq (ops.sqVComp α β) (ops.sqVComp α' β') := by
  subst hv₁ hv₂ hw₁ hw₂ htop hmid hbot
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
  let α := τ.natSquare h
  let β := τ'.natSquare h
  let γ := σ.natSquare (H.horMap h)
  let δ := σ'.natSquare (H.horMap h)
  let γ' := σ.natSquare (G.horMap h)
  have kpres := klaws.map_sqVComp α β
  have σsqnat := σSqNat β
  have s1 : HEq (ops₃.sqVComp (K.sqMap (ops₂.sqVComp α β)) (ops₃.sqVComp γ δ))
                (ops₃.sqVComp (ops₃.sqVComp (K.sqMap α) (K.sqMap β)) (ops₃.sqVComp γ δ)) :=
    sqVComp_heq_left ops₃ (ops₃.sqVComp γ δ) kpres (klaws.map_vComp _ _) (klaws.map_vComp _ _)
  have s2 : HEq (ops₃.sqVComp (ops₃.sqVComp (K.sqMap α) (K.sqMap β)) (ops₃.sqVComp γ δ))
                (ops₃.sqVComp (K.sqMap α) (ops₃.sqVComp (K.sqMap β) (ops₃.sqVComp γ δ))) :=
    sqVAssoc_heq ops₃ laws₃ (K.sqMap α) (K.sqMap β) (ops₃.sqVComp γ δ)
  have s3 : HEq (ops₃.sqVComp (K.sqMap α) (ops₃.sqVComp (K.sqMap β) (ops₃.sqVComp γ δ)))
                (ops₃.sqVComp (K.sqMap α) (ops₃.sqVComp (ops₃.sqVComp (K.sqMap β) γ) δ)) :=
    sqVComp_heq_right ops₃ (K.sqMap α)
      (HEq.symm (sqVAssoc_heq ops₃ laws₃ (K.sqMap β) γ δ))
      (Eq.symm (vComp_assoc ops₃ laws₃ _ _ _))
      (Eq.symm (vComp_assoc ops₃ laws₃ _ _ _))
  have s4 : HEq (ops₃.sqVComp (K.sqMap α) (ops₃.sqVComp (ops₃.sqVComp (K.sqMap β) γ) δ))
                (ops₃.sqVComp (K.sqMap α) (ops₃.sqVComp (ops₃.sqVComp γ' (L.sqMap β)) δ)) :=
    sqVComp_heq_right ops₃ (K.sqMap α)
      (sqVComp_heq_left ops₃ δ σsqnat (Eq.symm (σNat (τ'.app A))) (Eq.symm (σNat (τ'.app B))))
      (congrArg (ops₃.vComp · (σ'.app (H.objMap A))) (Eq.symm (σNat (τ'.app A))))
      (congrArg (ops₃.vComp · (σ'.app (H.objMap B))) (Eq.symm (σNat (τ'.app B))))
  have s5 : HEq (ops₃.sqVComp (K.sqMap α) (ops₃.sqVComp (ops₃.sqVComp γ' (L.sqMap β)) δ))
                (ops₃.sqVComp (K.sqMap α) (ops₃.sqVComp γ' (ops₃.sqVComp (L.sqMap β) δ))) :=
    sqVComp_heq_right ops₃ (K.sqMap α)
      (sqVAssoc_heq ops₃ laws₃ γ' (L.sqMap β) δ)
      (vComp_assoc ops₃ laws₃ _ _ _)
      (vComp_assoc ops₃ laws₃ _ _ _)
  have s6 : HEq (ops₃.sqVComp (K.sqMap α) (ops₃.sqVComp γ' (ops₃.sqVComp (L.sqMap β) δ)))
                (ops₃.sqVComp (ops₃.sqVComp (K.sqMap α) γ') (ops₃.sqVComp (L.sqMap β) δ)) :=
    HEq.symm (sqVAssoc_heq ops₃ laws₃ (K.sqMap α) γ' (ops₃.sqVComp (L.sqMap β) δ))
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

/-! ### Godement Product Laws for VertTransOps

The Godement product (horizontal composition of vertical transformations)
satisfies identity and associativity laws. Unlike the "same direction"
composition (vComp), these laws require DoubleFunctorLaws on some functors.
-/

/-- Right identity for Godement product: hComp τ (id Id) ≅ τ.

Composing a vertical transformation with the identity transformation on
the identity functor yields the original transformation. -/
theorem VertTransOps.hComp_id_right_heq {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (laws₂ : DoubleCategoryLaws ops₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (τ : VertTransOps F G) :
    HEq (VertTransOps.hComp ops₂ τ (VertTransOps.id ops₂ DoubleFunctorOps.id)) τ := by
  simp only [VertTransOps.hComp, VertTransOps.id, DoubleFunctorOps.id]
  apply VertTransOps.heq_mk
  · intro A
    exact laws₂.vertLaws.id_laws.comp_id _
  · intro A B h
    exact sqVCompId_heq ops₂ laws₂ _

/-- Left identity for Godement product: hComp (id Id) σ ≅ σ.

Composing the identity transformation on the identity functor with a
vertical transformation yields the original transformation. Requires
DoubleFunctorLaws on the post-composed functor H. -/
theorem VertTransOps.hComp_id_left_heq {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (laws₂ : DoubleCategoryLaws ops₂)
    {H K : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (hlaws : DoubleFunctorLaws ops₁ ops₂ H)
    (σ : VertTransOps H K) :
    HEq (VertTransOps.hComp ops₂
        (VertTransOps.id ops₁ DoubleFunctorOps.id) σ) σ := by
  simp only [VertTransOps.hComp, VertTransOps.id, DoubleFunctorOps.id]
  apply VertTransOps.heq_mk
  · intro A
    rw [hlaws.map_vId]
    exact laws₂.vertLaws.id_laws.id_comp _
  · intro A B h
    have h1 := sqVComp_heq_left ops₂ (σ.natSquare h) (hlaws.map_sqVertId h)
        (hlaws.map_vId A) (hlaws.map_vId B)
    have h2 := sqVIdComp_heq ops₂ laws₂ (σ.natSquare h)
    exact HEq.trans h1 h2

/-- Associativity for Godement product: hComp (hComp τ σ) ρ ≅ hComp τ (hComp σ ρ).

The Godement product is associative. This requires DoubleFunctorLaws on the
outermost functor L (the one closest to the final target category). -/
theorem VertTransOps.hComp_assoc_heq {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {Obj₃ : Type u₃}
    {vhs₃ : VertHomSet Obj₃} {hhs₃ : HorHomSet Obj₃} {sqs₃ : SquareSet vhs₃ hhs₃}
    {Obj₄ : Type u₄}
    {vhs₄ : VertHomSet Obj₄} {hhs₄ : HorHomSet Obj₄} {sqs₄ : SquareSet vhs₄ hhs₄}
    (ops₃ : DoubleCategoryOps Obj₃ vhs₃ hhs₃ sqs₃)
    (ops₄ : DoubleCategoryOps Obj₄ vhs₄ hhs₄ sqs₄)
    (laws₄ : DoubleCategoryLaws ops₄)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    {H K : DoubleFunctorOps vhs₂ hhs₂ sqs₂ vhs₃ hhs₃ sqs₃}
    {L M : DoubleFunctorOps vhs₃ hhs₃ sqs₃ vhs₄ hhs₄ sqs₄}
    (llaws : DoubleFunctorLaws ops₃ ops₄ L)
    (τ : VertTransOps F G) (σ : VertTransOps H K) (ρ : VertTransOps L M) :
    HEq (VertTransOps.hComp ops₄ (VertTransOps.hComp ops₃ τ σ) ρ)
        (VertTransOps.hComp ops₄ τ (VertTransOps.hComp ops₄ σ ρ)) := by
  simp only [VertTransOps.hComp]
  apply VertTransOps.heq_mk
  · intro A
    rw [llaws.map_vComp]
    exact laws₄.vertLaws.assoc _ _ _
  · intro A B h
    let τ_ns := τ.natSquare h
    let σ_ns := σ.natSquare (G.horMap h)
    let ρ_ns := ρ.natSquare (K.horMap (G.horMap h))
    have lpres := llaws.map_sqVComp (H.sqMap τ_ns) σ_ns
    have h1 := sqVComp_heq_left ops₄ ρ_ns lpres
        (llaws.map_vComp _ _) (llaws.map_vComp _ _)
    have h2 := sqVAssoc_heq ops₄ laws₄
        (L.sqMap (H.sqMap τ_ns)) (L.sqMap σ_ns) ρ_ns
    exact HEq.trans h1 h2

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

/-- HEq congruence for sqHComp when all boundaries may change.

This is a fully general version that allows both vertical and horizontal
boundaries to vary, given appropriate equality proofs. -/
theorem sqHComp_heq_all {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs)
    {A B C D E F : Obj}
    {v₁ v₁' : vhs A D} {v₂ v₂' : vhs B E} {v₃ v₃' : vhs C F}
    {h₁ h₁' : hhs A B} {h₂ h₂' : hhs B C} {h₃ h₃' : hhs D E} {h₄ h₄' : hhs E F}
    {α : sqs v₁ v₂ h₁ h₃} {α' : sqs v₁' v₂' h₁' h₃'}
    {β : sqs v₂ v₃ h₂ h₄} {β' : sqs v₂' v₃' h₂' h₄'}
    (hα : HEq α α') (hβ : HEq β β')
    (hleft : v₁ = v₁') (hmid : v₂ = v₂') (hright : v₃ = v₃')
    (htop : h₁ = h₁') (hmidH : h₂ = h₂') (hbot₁ : h₃ = h₃') (hbot₂ : h₄ = h₄') :
    HEq (ops.sqHComp α β) (ops.sqHComp α' β') := by
  subst hleft hmid hright htop hmidH hbot₁ hbot₂
  cases hα
  cases hβ
  rfl

/-! ### Godement Product Laws for HorTransOps

The Godement product (vertical composition of horizontal transformations,
HorTransOps.vComp) satisfies identity and associativity laws. These are
dual to the VertTransOps.hComp laws. -/

/-- Right identity for Godement product: vComp τ (id Id) ≅ τ. -/
theorem HorTransOps.vComp_id_right_heq {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (laws₂ : DoubleCategoryLaws ops₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (τ : HorTransOps F G) :
    HEq (HorTransOps.vComp ops₂ τ (HorTransOps.id ops₂ DoubleFunctorOps.id)) τ := by
  simp only [HorTransOps.vComp, HorTransOps.id, DoubleFunctorOps.id]
  apply HorTransOps.heq_mk
  · intro A
    exact laws₂.horLaws.id_laws.comp_id _
  · intro A B v
    exact sqHCompId_heq ops₂ laws₂ _

/-- Left identity for Godement product: vComp (id Id) σ ≅ σ. -/
theorem HorTransOps.vComp_id_left_heq {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    (laws₂ : DoubleCategoryLaws ops₂)
    {H K : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (hlaws : DoubleFunctorLaws ops₁ ops₂ H)
    (σ : HorTransOps H K) :
    HEq (HorTransOps.vComp ops₂
        (HorTransOps.id ops₁ DoubleFunctorOps.id) σ) σ := by
  simp only [HorTransOps.vComp, HorTransOps.id, DoubleFunctorOps.id]
  apply HorTransOps.heq_mk
  · intro A
    rw [hlaws.map_hId]
    exact laws₂.horLaws.id_laws.id_comp _
  · intro A B v
    have h1 := sqHComp_heq_left ops₂ (σ.natSquare v) (hlaws.map_sqHorId v)
        (hlaws.map_hId A) (hlaws.map_hId B)
    have h2 := sqHIdComp_heq ops₂ laws₂ (σ.natSquare v)
    exact HEq.trans h1 h2

/-- Associativity for Godement product: vComp (vComp τ σ) ρ ≅ vComp τ (vComp σ ρ).

The Godement product is associative. This requires DoubleFunctorLaws on the
outermost functor L (the one closest to the final target category). -/
theorem HorTransOps.vComp_assoc_heq {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    {Obj₃ : Type u₃}
    {vhs₃ : VertHomSet Obj₃} {hhs₃ : HorHomSet Obj₃} {sqs₃ : SquareSet vhs₃ hhs₃}
    {Obj₄ : Type u₄}
    {vhs₄ : VertHomSet Obj₄} {hhs₄ : HorHomSet Obj₄} {sqs₄ : SquareSet vhs₄ hhs₄}
    (ops₃ : DoubleCategoryOps Obj₃ vhs₃ hhs₃ sqs₃)
    (ops₄ : DoubleCategoryOps Obj₄ vhs₄ hhs₄ sqs₄)
    (laws₄ : DoubleCategoryLaws ops₄)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    {H K : DoubleFunctorOps vhs₂ hhs₂ sqs₂ vhs₃ hhs₃ sqs₃}
    {L M : DoubleFunctorOps vhs₃ hhs₃ sqs₃ vhs₄ hhs₄ sqs₄}
    (llaws : DoubleFunctorLaws ops₃ ops₄ L)
    (τ : HorTransOps F G) (σ : HorTransOps H K) (ρ : HorTransOps L M) :
    HEq (HorTransOps.vComp ops₄ (HorTransOps.vComp ops₃ τ σ) ρ)
        (HorTransOps.vComp ops₄ τ (HorTransOps.vComp ops₄ σ ρ)) := by
  simp only [HorTransOps.vComp]
  apply HorTransOps.heq_mk
  · intro A
    rw [llaws.map_hComp]
    exact laws₄.horLaws.assoc _ _ _
  · intro A B v
    let τ_ns := τ.natSquare v
    let σ_ns := σ.natSquare (G.vertMap v)
    let ρ_ns := ρ.natSquare (K.vertMap (G.vertMap v))
    have lpres := llaws.map_sqHComp (H.sqMap τ_ns) σ_ns
    have h1 := sqHComp_heq_left ops₄ ρ_ns lpres
        (llaws.map_hComp _ _) (llaws.map_hComp _ _)
    have h2 := sqHAssoc_heq ops₄ laws₄
        (L.sqMap (H.sqMap τ_ns)) (L.sqMap σ_ns) ρ_ns
    exact HEq.trans h1 h2

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
  have s1 : HEq (ops₃.sqHComp (K.sqMap (ops₂.sqHComp α β)) (ops₃.sqHComp γ δ))
                (ops₃.sqHComp (ops₃.sqHComp (K.sqMap α) (K.sqMap β)) (ops₃.sqHComp γ δ)) :=
    sqHComp_heq_left ops₃ (ops₃.sqHComp γ δ) kpres (klaws.map_hComp _ _) (klaws.map_hComp _ _)
  have s2 : HEq (ops₃.sqHComp (ops₃.sqHComp (K.sqMap α) (K.sqMap β)) (ops₃.sqHComp γ δ))
                (ops₃.sqHComp (K.sqMap α) (ops₃.sqHComp (K.sqMap β) (ops₃.sqHComp γ δ))) :=
    sqHAssoc_heq ops₃ laws₃ (K.sqMap α) (K.sqMap β) (ops₃.sqHComp γ δ)
  have s3 : HEq (ops₃.sqHComp (K.sqMap α) (ops₃.sqHComp (K.sqMap β) (ops₃.sqHComp γ δ)))
                (ops₃.sqHComp (K.sqMap α) (ops₃.sqHComp (ops₃.sqHComp (K.sqMap β) γ) δ)) :=
    sqHComp_heq_right ops₃ (K.sqMap α)
      (HEq.symm (sqHAssoc_heq ops₃ laws₃ (K.sqMap β) γ δ))
      (Eq.symm (hComp_assoc ops₃ laws₃ _ _ _))
      (Eq.symm (hComp_assoc ops₃ laws₃ _ _ _))
  have s4 : HEq (ops₃.sqHComp (K.sqMap α) (ops₃.sqHComp (ops₃.sqHComp (K.sqMap β) γ) δ))
                (ops₃.sqHComp (K.sqMap α) (ops₃.sqHComp (ops₃.sqHComp γ' (L.sqMap β)) δ)) :=
    sqHComp_heq_right ops₃ (K.sqMap α)
      (sqHComp_heq_left ops₃ δ σsqnat (Eq.symm (σNat (τ'.app A))) (Eq.symm (σNat (τ'.app B))))
      (congrArg (ops₃.hComp · (σ'.app (H.objMap A))) (Eq.symm (σNat (τ'.app A))))
      (congrArg (ops₃.hComp · (σ'.app (H.objMap B))) (Eq.symm (σNat (τ'.app B))))
  have s5 : HEq (ops₃.sqHComp (K.sqMap α) (ops₃.sqHComp (ops₃.sqHComp γ' (L.sqMap β)) δ))
                (ops₃.sqHComp (K.sqMap α) (ops₃.sqHComp γ' (ops₃.sqHComp (L.sqMap β) δ))) :=
    sqHComp_heq_right ops₃ (K.sqMap α)
      (sqHAssoc_heq ops₃ laws₃ γ' (L.sqMap β) δ)
      (hComp_assoc ops₃ laws₃ _ _ _)
      (hComp_assoc ops₃ laws₃ _ _ _)
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
    have s1 : HEq (ops₂.sqVComp (F.sqMap α) (ops₂.sqVComp (τ.natSquare h₂)
                      (σ.natSquare h₂)))
                  (ops₂.sqVComp (ops₂.sqVComp (F.sqMap α) (τ.natSquare h₂))
                      (σ.natSquare h₂)) :=
      HEq.symm (sqVAssoc_heq ops₂ laws₂ (F.sqMap α) (τ.natSquare h₂)
          (σ.natSquare h₂))
    have s2 : HEq (ops₂.sqVComp (ops₂.sqVComp (F.sqMap α) (τ.natSquare h₂))
                      (σ.natSquare h₂))
                  (ops₂.sqVComp (ops₂.sqVComp (τ.natSquare h₁) (G.sqMap α))
                      (σ.natSquare h₂)) :=
      sqVComp_heq_left ops₂ (σ.natSquare h₂) (τlaws.squareNaturality α)
          (τlaws.naturality v₁).symm (τlaws.naturality v₂).symm
    have s3 : HEq (ops₂.sqVComp (ops₂.sqVComp (τ.natSquare h₁) (G.sqMap α))
                      (σ.natSquare h₂))
                  (ops₂.sqVComp (τ.natSquare h₁) (ops₂.sqVComp (G.sqMap α)
                      (σ.natSquare h₂))) :=
      sqVAssoc_heq ops₂ laws₂ (τ.natSquare h₁) (G.sqMap α) (σ.natSquare h₂)
    have s4 : HEq (ops₂.sqVComp (τ.natSquare h₁) (ops₂.sqVComp (G.sqMap α)
                      (σ.natSquare h₂)))
                  (ops₂.sqVComp (τ.natSquare h₁) (ops₂.sqVComp (σ.natSquare h₁)
                      (H.sqMap α))) :=
      sqVComp_heq_right ops₂ (τ.natSquare h₁) (σlaws.squareNaturality α)
          (σlaws.naturality v₁).symm (σlaws.naturality v₂).symm
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
    have s1 : HEq (ops₃.sqVComp (H.sqMap (F.sqMap α))
                      (ops₃.sqVComp (H.sqMap (τ.natSquare h₂))
                          (σ.natSquare (G.horMap h₂))))
                  (ops₃.sqVComp (ops₃.sqVComp (H.sqMap (F.sqMap α))
                      (H.sqMap (τ.natSquare h₂))) (σ.natSquare (G.horMap h₂))) :=
      HEq.symm (sqVAssoc_heq ops₃ laws₃ _ _ _)
    have s2 : HEq (ops₃.sqVComp (ops₃.sqVComp (H.sqMap (F.sqMap α))
                      (H.sqMap (τ.natSquare h₂))) (σ.natSquare (G.horMap h₂)))
                  (ops₃.sqVComp (H.sqMap (ops₂.sqVComp (F.sqMap α) (τ.natSquare h₂)))
                      (σ.natSquare (G.horMap h₂))) :=
      sqVComp_heq_left ops₃ _ (HEq.symm (hlaws.map_sqVComp (F.sqMap α)
          (τ.natSquare h₂))) (hlaws.map_vComp _ _).symm (hlaws.map_vComp _ _).symm
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
    have s4 : HEq (ops₃.sqVComp (H.sqMap (ops₂.sqVComp (τ.natSquare h₁) (G.sqMap α)))
                      (σ.natSquare (G.horMap h₂)))
                  (ops₃.sqVComp (ops₃.sqVComp (H.sqMap (τ.natSquare h₁))
                      (H.sqMap (G.sqMap α))) (σ.natSquare (G.horMap h₂))) :=
      sqVComp_heq_left ops₃ _ (hlaws.map_sqVComp (τ.natSquare h₁) (G.sqMap α))
          (hlaws.map_vComp _ _) (hlaws.map_vComp _ _)
    have s5 : HEq (ops₃.sqVComp (ops₃.sqVComp (H.sqMap (τ.natSquare h₁))
                      (H.sqMap (G.sqMap α))) (σ.natSquare (G.horMap h₂)))
                  (ops₃.sqVComp (H.sqMap (τ.natSquare h₁))
                      (ops₃.sqVComp (H.sqMap (G.sqMap α))
                          (σ.natSquare (G.horMap h₂)))) :=
      sqVAssoc_heq ops₃ laws₃ _ _ _
    have s6 : HEq (ops₃.sqVComp (H.sqMap (τ.natSquare h₁))
                      (ops₃.sqVComp (H.sqMap (G.sqMap α))
                          (σ.natSquare (G.horMap h₂))))
                  (ops₃.sqVComp (H.sqMap (τ.natSquare h₁))
                      (ops₃.sqVComp (σ.natSquare (G.horMap h₁))
                          (K.sqMap (G.sqMap α)))) :=
      sqVComp_heq_right ops₃ _ (σlaws.squareNaturality (G.sqMap α))
          (σlaws.naturality (G.vertMap v₁)).symm (σlaws.naturality (G.vertMap v₂)).symm
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
    have σarg : HEq (σ.natSquare (G.horMap (ops₁.hId A)))
                    (σ.natSquare (ops₂.hId (G.objMap A))) :=
      Eq.rec (motive := fun h _ => HEq (σ.natSquare (G.horMap (ops₁.hId A)))
                                       (σ.natSquare h))
             HEq.rfl ghid
    have τidcoh : HEq (H.sqMap (τ.natSquare (ops₁.hId A)))
                      (H.sqMap (ops₂.sqHorId (τ.app A))) :=
      sqMap_heq H (τlaws.idCoherence A) rfl rfl fhid ghid
    have s12 := sqVComp_heq_both ops₃ τidcoh σarg
        (congrArg H.horMap fhid) hghid kghid
    have hpres : HEq (H.sqMap (ops₂.sqHorId (τ.app A)))
                     (ops₃.sqHorId (H.vertMap (τ.app A))) :=
      hlaws.map_sqHorId (τ.app A)
    have σidcoh : HEq (σ.natSquare (ops₂.hId (G.objMap A)))
                      (ops₃.sqHorId (σ.app (G.objMap A))) :=
      σlaws.idCoherence (G.objMap A)
    have s34 := sqVComp_heq_both ops₃ hpres σidcoh hhfid hhgid kkgid
    have s5 : ops₃.sqVComp (ops₃.sqHorId (H.vertMap (τ.app A)))
                           (ops₃.sqHorId (σ.app (G.objMap A))) =
              ops₃.sqHorId (ops₃.vComp (H.vertMap (τ.app A)) (σ.app (G.objMap A))) :=
      laws₃.sqLaws.vertIdVComp _ _
    exact HEq.trans s12 (HEq.trans s34 (heq_of_eq s5))
  compCoherence := by
    intro A B C h h'
    simp only [VertTransOps.hComp, DoubleFunctorOps.comp]
    have τcomp : HEq (H.sqMap (τ.natSquare (ops₁.hComp h h')))
                     (H.sqMap (ops₂.sqHComp (τ.natSquare h) (τ.natSquare h'))) :=
      sqMap_heq H (τlaws.compCoherence h h')
          rfl rfl (flaws.map_hComp h h') (glaws.map_hComp h h')
    have hcomp : HEq (H.sqMap (ops₂.sqHComp (τ.natSquare h) (τ.natSquare h')))
                     (ops₃.sqHComp (H.sqMap (τ.natSquare h)) (H.sqMap (τ.natSquare h'))) :=
      hlaws.map_sqHComp (τ.natSquare h) (τ.natSquare h')
    have s12 : HEq (H.sqMap (τ.natSquare (ops₁.hComp h h')))
                   (ops₃.sqHComp (H.sqMap (τ.natSquare h)) (H.sqMap (τ.natSquare h'))) :=
      HEq.trans τcomp hcomp
    have gcomp : G.horMap (ops₁.hComp h h') = ops₂.hComp (G.horMap h) (G.horMap h') :=
      glaws.map_hComp h h'
    have σtrans : HEq (σ.natSquare (G.horMap (ops₁.hComp h h')))
                      (σ.natSquare (ops₂.hComp (G.horMap h) (G.horMap h'))) :=
      Eq.rec (motive := fun x _ => HEq (σ.natSquare (G.horMap (ops₁.hComp h h')))
                                       (σ.natSquare x))
             HEq.rfl gcomp
    have σcomp : HEq (σ.natSquare (ops₂.hComp (G.horMap h) (G.horMap h')))
                     (ops₃.sqHComp (σ.natSquare (G.horMap h)) (σ.natSquare (G.horMap h'))) :=
      σlaws.compCoherence (G.horMap h) (G.horMap h')
    have s34 : HEq (σ.natSquare (G.horMap (ops₁.hComp h h')))
                   (ops₃.sqHComp (σ.natSquare (G.horMap h)) (σ.natSquare (G.horMap h'))) :=
      HEq.trans σtrans σcomp
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

/-! ## Companions and Conjoints

In a double category, companions and conjoints relate vertical and horizontal
morphisms. Given a vertical morphism `v : A →ᵥ B`:

- A **companion** is a horizontal morphism `v* : A →ₕ B` (same direction)
  with binding squares witnessing that v and v* behave like "the same morphism"
  viewed in different directions.

- A **conjoint** is a horizontal morphism `v_* : B →ₕ A` (opposite direction)
  with binding squares witnessing a dual relationship.

The binding squares for a companion `v*` of `v : A →ᵥ B` are:

```text
  φ (phi):              ψ (psi):
  A ─hId─▶ A            A ──v*──▶ B
  │        │            │         │
 vId       v            v        vId
  ▼        ▼            ▼         ▼
  A ──v*─▶ B            B ─hId──▶ B
```

The companion identity states: φ ⬝ᵥ ψ ≅ sqHorId v (using HEq since boundaries
differ by identity laws).

For conjoints, the binding squares for `v_*` of `v : A →ᵥ B` are:

```text
  ε (epsilon):          η (eta):
  B ──v_*──▶ A          A ──hId──▶ A
  │          │          │          │
 vId         v          v         vId
  ▼          ▼          ▼          ▼
  B ──hId──▶ B          B ──v_*──▶ A
```

The squares compose **horizontally** (not vertically), and the conjoint identity
states: ε ⬝ₕ η ≅ sqVertId v_* (using HEq since boundaries differ by identity laws)
-/

/-- A companion for a vertical morphism v : A →ᵥ B is a horizontal morphism
v* : A →ₕ B together with binding squares satisfying coherence.

The binding squares compose vertically. The identity condition uses HEq because
sqVComp phi psi has vertical boundaries (vComp (vId A) v, vComp v (vId B)) while
sqHorId v has boundaries (v, v), which are propositionally but not definitionally
equal. -/
structure Companion {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs)
    {A B : Obj} (v : vhs A B) where
  /-- The companion horizontal morphism -/
  hor : hhs A B
  /-- The φ binding square: sqs (vId A) v (hId A) hor -/
  phi : sqs (ops.vId A) v (ops.hId A) hor
  /-- The ψ binding square: sqs v (vId B) hor (hId B) -/
  psi : sqs v (ops.vId B) hor (ops.hId B)
  /-- Companion identity: φ ⬝ᵥ ψ ≅ sqHorId v (HEq since boundaries differ) -/
  identity : HEq (ops.sqVComp phi psi) (ops.sqHorId v)

/-- A conjoint for a vertical morphism v : A →ᵥ B is a horizontal morphism
v_* : B →ₕ A (opposite direction) together with binding squares.

The binding squares compose horizontally. The identity condition uses HEq because
sqHComp epsilon eta has horizontal boundaries (hComp hor (hId A), hComp (hId B) hor)
while sqVertId hor has boundaries (hor, hor), which are propositionally but not
definitionally equal. -/
structure Conjoint {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs)
    {A B : Obj} (v : vhs A B) where
  /-- The conjoint horizontal morphism (opposite direction) -/
  hor : hhs B A
  /-- The ε binding square: sqs (vId B) v hor (hId B) -/
  epsilon : sqs (ops.vId B) v hor (ops.hId B)
  /-- The η binding square: sqs v (vId A) (hId A) hor -/
  eta : sqs v (ops.vId A) (ops.hId A) hor
  /-- Conjoint identity: ε ⬝ₕ η ≅ sqVertId hor (HEq since boundaries differ) -/
  identity : HEq (ops.sqHComp epsilon eta) (ops.sqVertId hor)

/-- A double category has all companions if every vertical morphism has one. -/
class HasCompanions {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs) where
  /-- Every vertical morphism has a companion -/
  companion : ∀ {A B : Obj} (v : vhs A B), Companion ops v

/-- A double category has all conjoints if every vertical morphism has one. -/
class HasConjoints {Obj : Type u}
    {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
    (ops : DoubleCategoryOps Obj vhs hhs sqs) where
  /-- Every vertical morphism has a conjoint -/
  conjoint : ∀ {A B : Obj} (v : vhs A B), Conjoint ops v

namespace Companion

variable {Obj : Type u}
variable {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
variable {ops : DoubleCategoryOps Obj vhs hhs sqs}
variable {laws : DoubleCategoryLaws ops}

/-- The companion of a vertical identity is the horizontal identity. -/
def ofVId (A : Obj) (laws : DoubleCategoryLaws ops) : Companion ops (ops.vId A) where
  hor := ops.hId A
  phi := ops.sqVertId (ops.hId A)
  psi := ops.sqVertId (ops.hId A)
  identity := by
    have step1 : HEq (ops.sqVComp (ops.sqVertId (ops.hId A)) (ops.sqVertId (ops.hId A)))
                     (ops.sqVertId (ops.hId A)) :=
      sqVIdComp_heq ops laws (ops.sqVertId (ops.hId A))
    have step2 : ops.sqHorId (ops.vId A) = ops.sqVertId (ops.hId A) := laws.sqLaws.idOnId A
    exact HEq.trans step1 (heq_of_eq step2.symm)

section CompanionComp

variable {Obj : Type u}
variable {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
variable (ops : DoubleCategoryOps Obj vhs hhs sqs)
variable (laws : DoubleCategoryLaws ops)
variable {A B C : Obj} (v : vhs A B) (w : vhs B C)
variable (cv : Companion ops v) (cw : Companion ops w)

/-- The intermediate square for composite phi: sqVComp (sqHorId v) cw.phi
    after casting to have left vertical = v. -/
def compPhiInner : sqs v (ops.vComp v w) (ops.hId A) cw.hor :=
  let sq1 := ops.sqVComp (ops.sqHorId v) cw.phi
  let eq1 : ops.vComp v (ops.vId B) = v := laws.vertLaws.id_laws.comp_id v
  eq1.recOn (motive := fun v' _ => sqs v' (ops.vComp v w) (ops.hId A) cw.hor) sq1

/-- The phi binding square for the composite companion. -/
def compPhi : sqs (ops.vId A) (ops.vComp v w) (ops.hId A) (ops.hComp cv.hor cw.hor) :=
  let sq3 := ops.sqHComp cv.phi (compPhiInner ops laws v w cw)
  let eq2 : ops.hComp (ops.hId A) (ops.hId A) = ops.hId A :=
    laws.horLaws.id_laws.id_comp (ops.hId A)
  eq2.recOn (motive := fun h' _ =>
    sqs (ops.vId A) (ops.vComp v w) h' (ops.hComp cv.hor cw.hor)) sq3

/-- The intermediate square for composite psi: sqVComp cv.psi (sqHorId w)
    after casting to have right vertical = w. -/
def compPsiInner : sqs (ops.vComp v w) w cv.hor (ops.hId C) :=
  let sq1 := ops.sqVComp cv.psi (ops.sqHorId w)
  let eq1 : ops.vComp (ops.vId B) w = w := laws.vertLaws.id_laws.id_comp w
  eq1.recOn (motive := fun w' _ => sqs (ops.vComp v w) w' cv.hor (ops.hId C)) sq1

/-- The psi binding square for the composite companion. -/
def compPsi : sqs (ops.vComp v w) (ops.vId C) (ops.hComp cv.hor cw.hor) (ops.hId C) :=
  let sq3 := ops.sqHComp (compPsiInner ops laws v w cv) cw.psi
  let eq2 : ops.hComp (ops.hId C) (ops.hId C) = ops.hId C :=
    laws.horLaws.id_laws.id_comp (ops.hId C)
  eq2.recOn (motive := fun h' _ =>
    sqs (ops.vComp v w) (ops.vId C) (ops.hComp cv.hor cw.hor) h') sq3

/-- The identity condition for the composite companion.

This is the main lemma: sqVComp (compPhi) (compPsi) ≅ sqHorId (vComp v w).

The proof uses cv.identity, cw.identity, vertIdVComp, and the interchange law
together with associativity of square composition. -/
theorem compIdentity :
    HEq (ops.sqVComp (compPhi ops laws v w cv cw) (compPsi ops laws v w cv cw))
        (ops.sqHorId (ops.vComp v w)) := by
  let eqVL : ops.vComp v (ops.vId B) = v := laws.vertLaws.id_laws.comp_id v
  let eqVR : ops.vComp (ops.vId B) w = w := laws.vertLaws.id_laws.id_comp w
  let eqHL : ops.hComp (ops.hId A) (ops.hId A) = ops.hId A :=
    laws.horLaws.id_laws.id_comp (ops.hId A)
  let eqHR : ops.hComp (ops.hId C) (ops.hId C) = ops.hId C :=
    laws.horLaws.id_laws.id_comp (ops.hId C)
  let phiRaw := ops.sqHComp cv.phi (compPhiInner ops laws v w cw)
  let psiRaw := ops.sqHComp (compPsiInner ops laws v w cv) cw.psi
  have h_phi_heq : HEq (compPhi ops laws v w cv cw) phiRaw := by
    simp only [compPhi]
    exact eqRec_heq_self _ eqHL
  have h_psi_heq : HEq (compPsi ops laws v w cv cw) psiRaw := by
    simp only [compPsi]
    exact eqRec_heq_self _ eqHR
  have h_vcomp_heq :
      HEq (ops.sqVComp (compPhi ops laws v w cv cw) (compPsi ops laws v w cv cw))
          (ops.sqVComp phiRaw psiRaw) :=
    sqVComp_heq_both ops h_phi_heq h_psi_heq eqHL.symm rfl eqHR.symm
  have interch := laws.sqLaws.interchange cv.phi (compPhiInner ops laws v w cw)
                    (compPsiInner ops laws v w cv) cw.psi
  have h_after_interch :
      HEq (ops.sqVComp phiRaw psiRaw)
          (ops.sqHComp (ops.sqVComp cv.phi (compPsiInner ops laws v w cv))
                       (ops.sqVComp (compPhiInner ops laws v w cw) cw.psi)) :=
    heq_of_eq interch
  have h_psiInner_heq :
      HEq (compPsiInner ops laws v w cv) (ops.sqVComp cv.psi (ops.sqHorId w)) := by
    simp only [compPsiInner]
    exact eqRec_heq_self _ eqVR
  have h_phiInner_heq :
      HEq (compPhiInner ops laws v w cw) (ops.sqVComp (ops.sqHorId v) cw.phi) := by
    simp only [compPhiInner]
    exact eqRec_heq_self _ eqVL
  have h_left_assoc :
      HEq (ops.sqVComp cv.phi (ops.sqVComp cv.psi (ops.sqHorId w)))
          (ops.sqVComp (ops.sqVComp cv.phi cv.psi) (ops.sqHorId w)) :=
    (sqVAssoc_heq ops laws cv.phi cv.psi (ops.sqHorId w)).symm
  have h_left_id :
      HEq (ops.sqVComp (ops.sqVComp cv.phi cv.psi) (ops.sqHorId w))
          (ops.sqVComp (ops.sqHorId v) (ops.sqHorId w)) :=
    sqVComp_heq_left ops (ops.sqHorId w) cv.identity
      (laws.vertLaws.id_laws.id_comp v)
      (laws.vertLaws.id_laws.comp_id v)
  have h_left_vertId :
      ops.sqVComp (ops.sqHorId v) (ops.sqHorId w) = ops.sqHorId (ops.vComp v w) :=
    laws.sqLaws.vertIdVComp v w
  have h_left_combined :
      HEq (ops.sqVComp cv.phi (ops.sqVComp cv.psi (ops.sqHorId w)))
          (ops.sqHorId (ops.vComp v w)) :=
    HEq.trans h_left_assoc (HEq.trans h_left_id (heq_of_eq h_left_vertId))
  have h_left_with_cast :
      HEq (ops.sqVComp cv.phi (compPsiInner ops laws v w cv))
          (ops.sqHorId (ops.vComp v w)) := by
    apply HEq.trans _ h_left_combined
    exact sqVComp_heq_right ops cv.phi h_psiInner_heq rfl eqVR.symm
  have h_right_assoc :
      HEq (ops.sqVComp (ops.sqVComp (ops.sqHorId v) cw.phi) cw.psi)
          (ops.sqVComp (ops.sqHorId v) (ops.sqVComp cw.phi cw.psi)) :=
    sqVAssoc_heq ops laws (ops.sqHorId v) cw.phi cw.psi
  have h_right_id :
      HEq (ops.sqVComp (ops.sqHorId v) (ops.sqVComp cw.phi cw.psi))
          (ops.sqVComp (ops.sqHorId v) (ops.sqHorId w)) :=
    sqVComp_heq_right ops (ops.sqHorId v) cw.identity
      (laws.vertLaws.id_laws.id_comp w)
      (laws.vertLaws.id_laws.comp_id w)
  have h_right_combined :
      HEq (ops.sqVComp (ops.sqVComp (ops.sqHorId v) cw.phi) cw.psi)
          (ops.sqHorId (ops.vComp v w)) :=
    HEq.trans h_right_assoc (HEq.trans h_right_id (heq_of_eq h_left_vertId))
  have h_right_with_cast :
      HEq (ops.sqVComp (compPhiInner ops laws v w cw) cw.psi)
          (ops.sqHorId (ops.vComp v w)) := by
    apply HEq.trans _ h_right_combined
    exact sqVComp_heq_left ops cw.psi h_phiInner_heq eqVL.symm rfl
  have h_hcomp_of_horIds :
      HEq (ops.sqHComp (ops.sqVComp cv.phi (compPsiInner ops laws v w cv))
                       (ops.sqVComp (compPhiInner ops laws v w cw) cw.psi))
          (ops.sqHComp (ops.sqHorId (ops.vComp v w)) (ops.sqHorId (ops.vComp v w))) :=
    sqHComp_heq_both ops h_left_with_cast h_right_with_cast
      (laws.vertLaws.id_laws.id_comp _)
      rfl
      (laws.vertLaws.id_laws.comp_id _)
  have h_horId_hcomp_self :
      HEq (ops.sqHComp (ops.sqHorId (ops.vComp v w)) (ops.sqHorId (ops.vComp v w)))
          (ops.sqHorId (ops.vComp v w)) :=
    sqHIdComp_heq ops laws (ops.sqHorId (ops.vComp v w))
  have final_step :
      HEq (ops.sqHComp (ops.sqVComp cv.phi (compPsiInner ops laws v w cv))
                       (ops.sqVComp (compPhiInner ops laws v w cw) cw.psi))
          (ops.sqHorId (ops.vComp v w)) :=
    HEq.trans h_hcomp_of_horIds h_horId_hcomp_self
  exact HEq.trans h_vcomp_heq (HEq.trans h_after_interch final_step)

end CompanionComp

/-- The companion of a vertical composite is the horizontal composite of companions.

Given v : A →ᵥ B with companion v* and w : B →ᵥ C with companion w*,
the companion of (vComp v w) is (hComp v* w*).

The binding squares are constructed by pasting:
- φ_{v∘w} = sqHComp φᵥ (sqVComp (sqHorId v) φᵤ)
- ψ_{v∘w} = sqHComp (sqVComp ψᵥ (sqHorId w)) ψᵤ
-/
def comp {A B C : Obj} {v : vhs A B} {w : vhs B C}
    (cv : Companion ops v) (cw : Companion ops w)
    (laws : DoubleCategoryLaws ops) : Companion ops (ops.vComp v w) where
  hor := ops.hComp cv.hor cw.hor
  phi := compPhi ops laws v w cv cw
  psi := compPsi ops laws v w cv cw
  identity := compIdentity ops laws v w cv cw

end Companion

namespace Conjoint

variable {Obj : Type u}
variable {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
variable {ops : DoubleCategoryOps Obj vhs hhs sqs}
variable {laws : DoubleCategoryLaws ops}

/-- The conjoint of a vertical identity is the horizontal identity. -/
def ofVId (A : Obj) (laws : DoubleCategoryLaws ops) : Conjoint ops (ops.vId A) where
  hor := ops.hId A
  epsilon := ops.sqVertId (ops.hId A)
  eta := ops.sqVertId (ops.hId A)
  identity := by
    have step1 : ops.sqHComp (ops.sqVertId (ops.hId A)) (ops.sqVertId (ops.hId A)) =
                 ops.sqVertId (ops.hComp (ops.hId A) (ops.hId A)) :=
      laws.sqLaws.horIdHComp (ops.hId A) (ops.hId A)
    have step2 : ops.hComp (ops.hId A) (ops.hId A) = ops.hId A :=
      laws.horLaws.id_laws.id_comp (ops.hId A)
    have step3 : HEq (ops.sqVertId (ops.hComp (ops.hId A) (ops.hId A)))
                     (ops.sqVertId (ops.hId A)) :=
      step2.symm.recOn (motive := fun h' _ =>
        HEq (ops.sqVertId h') (ops.sqVertId (ops.hId A))) HEq.rfl
    exact HEq.trans (heq_of_eq step1) step3

section ConjointComp

variable {Obj : Type u}
variable {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
variable (ops : DoubleCategoryOps Obj vhs hhs sqs)
variable (laws : DoubleCategoryLaws ops)
variable {A B C : Obj} (v : vhs A B) (w : vhs B C)
variable (cv : Conjoint ops v) (cw : Conjoint ops w)

/-- The intermediate square for composite epsilon: sqVComp cv.epsilon (sqHorId w)
    after casting to have left vertical = w. -/
def compEpsilonInner : sqs w (ops.vComp v w) cv.hor (ops.hId C) :=
  let sq1 := ops.sqVComp cv.epsilon (ops.sqHorId w)
  let eq1 : ops.vComp (ops.vId B) w = w := laws.vertLaws.id_laws.id_comp w
  eq1.recOn (motive := fun w' _ => sqs w' (ops.vComp v w) cv.hor (ops.hId C)) sq1

/-- The epsilon binding square for the composite conjoint. -/
def compEpsilon : sqs (ops.vId C) (ops.vComp v w) (ops.hComp cw.hor cv.hor) (ops.hId C) :=
  let sq3 := ops.sqHComp cw.epsilon (compEpsilonInner ops laws v w cv)
  let eq2 : ops.hComp (ops.hId C) (ops.hId C) = ops.hId C :=
    laws.horLaws.id_laws.id_comp (ops.hId C)
  eq2.recOn (motive := fun h' _ =>
    sqs (ops.vId C) (ops.vComp v w) (ops.hComp cw.hor cv.hor) h') sq3

/-- The intermediate square for composite eta: sqVComp (sqHorId v) cw.eta
    after casting to have right vertical = v. -/
def compEtaInner : sqs (ops.vComp v w) v (ops.hId A) cw.hor :=
  let sq1 := ops.sqVComp (ops.sqHorId v) cw.eta
  let eq1 : ops.vComp v (ops.vId B) = v := laws.vertLaws.id_laws.comp_id v
  eq1.recOn (motive := fun v' _ => sqs (ops.vComp v w) v' (ops.hId A) cw.hor) sq1

/-- The eta binding square for the composite conjoint. -/
def compEta : sqs (ops.vComp v w) (ops.vId A) (ops.hId A) (ops.hComp cw.hor cv.hor) :=
  let sq3 := ops.sqHComp (compEtaInner ops laws v w cw) cv.eta
  let eq2 : ops.hComp (ops.hId A) (ops.hId A) = ops.hId A :=
    laws.horLaws.id_laws.id_comp (ops.hId A)
  eq2.recOn (motive := fun h' _ =>
    sqs (ops.vComp v w) (ops.vId A) h' (ops.hComp cw.hor cv.hor)) sq3

/-- The identity condition for the composite conjoint.

This is the main lemma: sqHComp compEpsilon compEta ≅ sqVertId (hComp cw.hor cv.hor).

The proof strategy:
1. Peel off outer casts to get epsilonRaw and etaRaw
2. Use interchange on the middle (X ⬝ₕ Y) to get sqVComp cv.epsilon cw.eta
3. Rearrange via associativity
4. Use cv.identity: cv.epsilon ⬝ₕ cv.eta ≅ sqVertId cv.hor
5. Use cw.identity: cw.epsilon ⬝ₕ cw.eta ≅ sqVertId cw.hor
6. Apply horIdHComp to get sqVertId (hComp cw.hor cv.hor) -/
theorem compIdentity :
    HEq (ops.sqHComp (compEpsilon ops laws v w cv cw) (compEta ops laws v w cv cw))
        (ops.sqVertId (ops.hComp cw.hor cv.hor)) := by
  let eqVL : ops.vComp (ops.vId B) w = w := laws.vertLaws.id_laws.id_comp w
  let eqVR : ops.vComp v (ops.vId B) = v := laws.vertLaws.id_laws.comp_id v
  let eqHT : ops.hComp (ops.hId A) (ops.hId A) = ops.hId A :=
    laws.horLaws.id_laws.id_comp (ops.hId A)
  let eqHB : ops.hComp (ops.hId C) (ops.hId C) = ops.hId C :=
    laws.horLaws.id_laws.id_comp (ops.hId C)
  let epsilonRaw := ops.sqHComp cw.epsilon (compEpsilonInner ops laws v w cv)
  let etaRaw := ops.sqHComp (compEtaInner ops laws v w cw) cv.eta
  have h_epsilon_heq : HEq (compEpsilon ops laws v w cv cw) epsilonRaw := by
    simp only [compEpsilon]
    exact eqRec_heq_self _ eqHB
  have h_eta_heq : HEq (compEta ops laws v w cv cw) etaRaw := by
    simp only [compEta]
    exact eqRec_heq_self _ eqHT
  have h_epsilonInner_heq :
      HEq (compEpsilonInner ops laws v w cv)
          (ops.sqVComp cv.epsilon (ops.sqHorId w)) := by
    simp only [compEpsilonInner]
    exact eqRec_heq_self _ eqVL
  have h_etaInner_heq :
      HEq (compEtaInner ops laws v w cw)
          (ops.sqVComp (ops.sqHorId v) cw.eta) := by
    simp only [compEtaInner]
    exact eqRec_heq_self _ eqVR
  let X := ops.sqVComp cv.epsilon (ops.sqHorId w)
  let Y := ops.sqVComp (ops.sqHorId v) cw.eta
  let X' := compEpsilonInner ops laws v w cv
  have hX_heq : HEq X X' := h_epsilonInner_heq.symm
  let Y' := compEtaInner ops laws v w cw
  have hY_heq : HEq Y Y' := h_etaInner_heq.symm
  have h_inner_comp_heq :
      HEq (ops.sqHComp (compEpsilonInner ops laws v w cv) (compEtaInner ops laws v w cw))
          (ops.sqHComp X Y) :=
    sqHComp_heq_both ops h_epsilonInner_heq h_etaInner_heq
      eqVL.symm rfl eqVR.symm
  have interch := laws.sqLaws.interchange cv.epsilon (ops.sqHorId v)
                    (ops.sqHorId w) cw.eta
  have h_cv_eps_hId :
      HEq (ops.sqHComp cv.epsilon (ops.sqHorId v)) cv.epsilon :=
    sqHCompId_heq ops laws cv.epsilon
  have h_hId_cw_eta :
      HEq (ops.sqHComp (ops.sqHorId w) cw.eta) cw.eta :=
    sqHIdComp_heq ops laws cw.eta
  let cvCwVComp := ops.sqVComp cv.epsilon cw.eta
  have eqType : sqs (ops.vComp (ops.vId B) w) (ops.vComp v (ops.vId B)) cv.hor cw.hor =
                sqs w v cv.hor cw.hor := by
    rw [eqVL, eqVR]
  let cvCwVComp' : sqs w v cv.hor cw.hor := cast eqType cvCwVComp
  have hcvCwVComp_heq : HEq cvCwVComp cvCwVComp' := (cast_heq eqType cvCwVComp).symm
  have h_after_interch :
      HEq (ops.sqVComp (ops.sqHComp cv.epsilon (ops.sqHorId v))
                       (ops.sqHComp (ops.sqHorId w) cw.eta))
          cvCwVComp :=
    sqVComp_heq_both ops h_cv_eps_hId h_hId_cw_eta
      (laws.horLaws.id_laws.comp_id cv.hor)
      (laws.horLaws.id_laws.id_comp (ops.hId B))
      (laws.horLaws.id_laws.id_comp cw.hor)
  have h_XY_vcomp : HEq (ops.sqHComp X Y) cvCwVComp :=
    HEq.trans (heq_of_eq interch.symm) h_after_interch
  have interch2 := laws.sqLaws.interchange cv.epsilon cv.eta cw.eta
                     (ops.sqVertId cv.hor)
  have h_X'Y'_to_vcomp' : HEq (ops.sqHComp X' Y') cvCwVComp' :=
    HEq.trans h_inner_comp_heq (HEq.trans h_XY_vcomp hcvCwVComp_heq)
  have h_XYeta :
      HEq (ops.sqHComp X' (ops.sqHComp Y' cv.eta))
          (ops.sqHComp cvCwVComp' cv.eta) := by
    have h_assoc3 :
        HEq (ops.sqHComp X' (ops.sqHComp Y' cv.eta))
            (ops.sqHComp (ops.sqHComp X' Y') cv.eta) :=
      (sqHAssoc_heq ops laws X' Y' cv.eta).symm
    have h_assoc_to_vcomp' :
        HEq (ops.sqHComp (ops.sqHComp X' Y') cv.eta)
            (ops.sqHComp cvCwVComp' cv.eta) :=
      sqHComp_heq_left ops cv.eta h_X'Y'_to_vcomp'
        (laws.horLaws.id_laws.comp_id cv.hor)
        (laws.horLaws.id_laws.id_comp cw.hor)
    exact HEq.trans h_assoc3 h_assoc_to_vcomp'
  have h_full_to_cvCw :
      HEq (ops.sqHComp (ops.sqHComp cw.epsilon X') (ops.sqHComp Y' cv.eta))
          (ops.sqHComp cw.epsilon (ops.sqHComp cvCwVComp' cv.eta)) := by
    have step1 :
        HEq (ops.sqHComp (ops.sqHComp cw.epsilon X') (ops.sqHComp Y' cv.eta))
            (ops.sqHComp cw.epsilon (ops.sqHComp X' (ops.sqHComp Y' cv.eta))) :=
      sqHAssoc_heq ops laws cw.epsilon X' (ops.sqHComp Y' cv.eta)
    have step2 :
        HEq (ops.sqHComp cw.epsilon (ops.sqHComp X' (ops.sqHComp Y' cv.eta)))
            (ops.sqHComp cw.epsilon (ops.sqHComp cvCwVComp' cv.eta)) :=
      sqHComp_heq_right ops cw.epsilon h_XYeta
        (congrArg (ops.hComp cv.hor ·) eqHT)
        (laws.horLaws.id_laws.id_comp (ops.hComp cw.hor cv.hor))
    exact HEq.trans step1 step2
  have h_assoc_cw :
      HEq (ops.sqHComp cw.epsilon (ops.sqHComp cvCwVComp' cv.eta))
          (ops.sqHComp (ops.sqHComp cw.epsilon cvCwVComp') cv.eta) :=
    (sqHAssoc_heq ops laws cw.epsilon cvCwVComp' cv.eta).symm
  have h_cv_eta_vcomp :
      HEq cv.eta (ops.sqVComp cv.eta (ops.sqVertId cv.hor)) :=
    (sqVCompId_heq ops laws cv.eta).symm
  have h_cvCw_eta_bridge :
      HEq (ops.sqHComp cvCwVComp' cv.eta)
          (ops.sqHComp cvCwVComp (ops.sqVComp cv.eta (ops.sqVertId cv.hor))) :=
    sqHComp_heq_both ops hcvCwVComp_heq.symm h_cv_eta_vcomp
      eqVL.symm eqVR.symm (laws.vertLaws.id_laws.comp_id (ops.vId A)).symm
  have h_interch2_applied :
      HEq (ops.sqHComp cvCwVComp (ops.sqVComp cv.eta (ops.sqVertId cv.hor)))
          (ops.sqVComp (ops.sqHComp cv.epsilon cv.eta)
                       (ops.sqHComp cw.eta (ops.sqVertId cv.hor))) :=
    heq_of_eq interch2.symm
  have h_cvCw_eta_full :
      HEq (ops.sqHComp cvCwVComp' cv.eta)
          (ops.sqVComp (ops.sqHComp cv.epsilon cv.eta)
                       (ops.sqHComp cw.eta (ops.sqVertId cv.hor))) :=
    HEq.trans h_cvCw_eta_bridge h_interch2_applied
  let eqMid : ops.hComp (ops.hId B) cv.hor = cv.hor := laws.horLaws.id_laws.id_comp cv.hor
  let β := ops.sqHComp cw.eta (ops.sqVertId cv.hor)
  let eqType : sqs w (ops.vId A) (ops.hComp (ops.hId B) cv.hor) (ops.hComp cw.hor cv.hor) =
               sqs w (ops.vId A) cv.hor (ops.hComp cw.hor cv.hor) := by rw [eqMid]
  let β' := cast eqType β
  have hβ_heq : HEq β β' := (cast_heq eqType β).symm
  have h_vcomp_heq_both :
      HEq (ops.sqVComp (ops.sqHComp cv.epsilon cv.eta) β)
          (ops.sqVComp (ops.sqVertId cv.hor) β') :=
    sqVComp_heq_both ops cv.identity hβ_heq
      (laws.horLaws.id_laws.comp_id cv.hor)
      eqMid
      rfl
  have h_vIdComp_β' : HEq (ops.sqVComp (ops.sqVertId cv.hor) β') β' :=
    sqVIdComp_heq ops laws β'
  have h_cv_id_and_vIdComp :
      HEq (ops.sqVComp (ops.sqHComp cv.epsilon cv.eta) β) β :=
    HEq.trans (HEq.trans h_vcomp_heq_both h_vIdComp_β') hβ_heq.symm
  have h_cvCw_eta_to_beta :
      HEq (ops.sqHComp cvCwVComp' cv.eta) β :=
    HEq.trans h_cvCw_eta_full h_cv_id_and_vIdComp
  have h_assoc_cw_eta_vId :
      HEq (ops.sqHComp cw.epsilon (ops.sqHComp cw.eta (ops.sqVertId cv.hor)))
          (ops.sqHComp (ops.sqHComp cw.epsilon cw.eta) (ops.sqVertId cv.hor)) :=
    (sqHAssoc_heq ops laws cw.epsilon cw.eta (ops.sqVertId cv.hor)).symm
  have h_cw_id_vertId :
      HEq (ops.sqHComp (ops.sqHComp cw.epsilon cw.eta) (ops.sqVertId cv.hor))
          (ops.sqHComp (ops.sqVertId cw.hor) (ops.sqVertId cv.hor)) :=
    sqHComp_heq_left ops (ops.sqVertId cv.hor) cw.identity
      (laws.horLaws.id_laws.comp_id cw.hor)
      (laws.horLaws.id_laws.id_comp cw.hor)
  have h_horIdHComp :
      ops.sqHComp (ops.sqVertId cw.hor) (ops.sqVertId cv.hor) =
      ops.sqVertId (ops.hComp cw.hor cv.hor) :=
    laws.sqLaws.horIdHComp cw.hor cv.hor
  have h_final_step :
      HEq (ops.sqHComp cw.epsilon (ops.sqHComp cw.eta (ops.sqVertId cv.hor)))
          (ops.sqVertId (ops.hComp cw.hor cv.hor)) :=
    HEq.trans (HEq.trans h_assoc_cw_eta_vId h_cw_id_vertId) (heq_of_eq h_horIdHComp)
  have eqTop : ops.hComp cv.hor (ops.hId A) = ops.hComp (ops.hId B) cv.hor :=
    (laws.horLaws.id_laws.comp_id cv.hor).trans
    (laws.horLaws.id_laws.id_comp cv.hor).symm
  have h_cw_eps_inner :
      HEq (ops.sqHComp cw.epsilon (ops.sqHComp cvCwVComp' cv.eta))
          (ops.sqHComp cw.epsilon β) :=
    sqHComp_heq_right ops cw.epsilon h_cvCw_eta_to_beta eqTop rfl
  have h_inner_to_target :
      HEq (ops.sqHComp cw.epsilon (ops.sqHComp cvCwVComp' cv.eta))
          (ops.sqVertId (ops.hComp cw.hor cv.hor)) :=
    HEq.trans h_cw_eps_inner h_final_step
  have h_full_inner_to_target :
      HEq (ops.sqHComp (ops.sqHComp cw.epsilon X') (ops.sqHComp Y' cv.eta))
          (ops.sqVertId (ops.hComp cw.hor cv.hor)) :=
    HEq.trans h_full_to_cvCw h_inner_to_target
  have h_raw_to_target :
      HEq (ops.sqHComp epsilonRaw etaRaw)
          (ops.sqVertId (ops.hComp cw.hor cv.hor)) :=
    h_full_inner_to_target
  have h_comp_to_raw :
      HEq (ops.sqHComp (compEpsilon ops laws v w cv cw) (compEta ops laws v w cv cw))
          (ops.sqHComp epsilonRaw etaRaw) :=
    sqHComp_heq_all ops h_epsilon_heq h_eta_heq
      rfl rfl rfl rfl eqHT.symm eqHB.symm rfl
  exact HEq.trans h_comp_to_raw h_raw_to_target

end ConjointComp

/-- The conjoint of a vertical composite is the horizontal composite of conjoints
in reverse order.

Given v : A →ᵥ B with conjoint v_* : B →ₕ A and w : B →ᵥ C with conjoint
w_* : C →ₕ B, the conjoint of (vComp v w) : A →ᵥ C is (hComp w_* v_*) : C →ₕ A.

The binding squares are constructed by pasting:
- ε_{v∘w} = sqHComp (sqVComp cw.epsilon (sqHorId v)) cv.epsilon
- η_{v∘w} = sqHComp cv.eta (sqVComp (sqHorId w) cw.eta)
-/
def comp {A B C : Obj} {v : vhs A B} {w : vhs B C}
    (cv : Conjoint ops v) (cw : Conjoint ops w)
    (laws : DoubleCategoryLaws ops) : Conjoint ops (ops.vComp v w) where
  hor := ops.hComp cw.hor cv.hor
  epsilon := compEpsilon ops laws v w cv cw
  eta := compEta ops laws v w cv cw
  identity := compIdentity ops laws v w cv cw

end Conjoint

/-! ## Companion-Conjoint Pairs and Adjunctions

When a vertical morphism has both a companion and a conjoint, their binding
squares compose to give unit and counit squares that form an adjunction in
the horizontal bicategory.
-/

section CompanionConjointAdjunction

variable {Obj : Type u}
variable {vhs : VertHomSet Obj} {hhs : HorHomSet Obj} {sqs : SquareSet vhs hhs}
variable (ops : DoubleCategoryOps Obj vhs hhs sqs)
variable (laws : DoubleCategoryLaws ops)
variable {A B : Obj} (v : vhs A B)
variable (cv : Companion ops v) (cj : Conjoint ops v)

/-- The unit square of the adjunction v* ⊣ v_*.

Given companion (v*, φ, ψ) and conjoint (v_*, ε, η), the unit is φ ⬝ₕ η:
- Top: hId A
- Bottom: hComp v* v_*
- Left: vId A
- Right: vId A

This represents a morphism from hId A to v* ⬝ₕ v_* in the horizontal bicategory.
-/
def adjunctionUnit : sqs (ops.vId A) (ops.vId A)
    (ops.hComp (ops.hId A) (ops.hId A)) (ops.hComp cv.hor cj.hor) :=
  ops.sqHComp cv.phi cj.eta

/-- The counit square of the adjunction v* ⊣ v_*.

Given companion (v*, φ, ψ) and conjoint (v_*, ε, η), the counit is ε ⬝ₕ ψ:
- Top: hComp v_* v*
- Bottom: hId B
- Left: vId B
- Right: vId B

This represents a morphism from v_* ⬝ₕ v* to hId B in the horizontal bicategory.
-/
def adjunctionCounit : sqs (ops.vId B) (ops.vId B)
    (ops.hComp cj.hor cv.hor) (ops.hComp (ops.hId B) (ops.hId B)) :=
  ops.sqHComp cj.epsilon cv.psi

/-- The unit square with identity laws applied.

The raw unit has type sqs (vId A) (vId A) (hComp (hId A) (hId A)) (hComp v* v_*).
This version casts to sqs (vId A) (vId A) (hId A) (hComp v* v_*).
-/
def adjunctionUnit' : sqs (ops.vId A) (ops.vId A) (ops.hId A) (ops.hComp cv.hor cj.hor) :=
  let eq := laws.horLaws.id_laws.id_comp (ops.hId A)
  eq.recOn (motive := fun h' _ =>
    sqs (ops.vId A) (ops.vId A) h' (ops.hComp cv.hor cj.hor))
    (adjunctionUnit ops v cv cj)

/-- The counit square with identity laws applied.

The raw counit has type sqs (vId B) (vId B) (hComp v_* v*) (hComp (hId B) (hId B)).
This version casts to sqs (vId B) (vId B) (hComp v_* v*) (hId B).
-/
def adjunctionCounit' : sqs (ops.vId B) (ops.vId B) (ops.hComp cj.hor cv.hor) (ops.hId B) :=
  let eq := laws.horLaws.id_laws.id_comp (ops.hId B)
  eq.recOn (motive := fun h' _ =>
    sqs (ops.vId B) (ops.vId B) (ops.hComp cj.hor cv.hor) h')
    (adjunctionCounit ops v cv cj)

/-- Horizontal composition ψ ⬝ₕ ε : sqs v v (v* ⬝ v_*) (hId B ⬝ hId B).

Composing the second companion binding square with the first conjoint binding square
gives a square with vertical boundary v on both sides.
-/
def psiHCompEpsilon : sqs v v
    (ops.hComp cv.hor cj.hor) (ops.hComp (ops.hId B) (ops.hId B)) :=
  ops.sqHComp cv.psi cj.epsilon

/-- Horizontal composition η ⬝ₕ φ : sqs v v (hId A ⬝ hId A) (v_* ⬝ v*).

Composing the second conjoint binding square with the first companion binding square
gives a square with vertical boundary v on both sides.
-/
def etaHCompPhi : sqs v v
    (ops.hComp (ops.hId A) (ops.hId A)) (ops.hComp cj.hor cv.hor) :=
  ops.sqHComp cj.eta cv.phi

/-- ψ ⬝ₕ ε with identity laws applied: sqs v v (v* ⬝ v_*) (hId B). -/
def psiHCompEpsilon' : sqs v v (ops.hComp cv.hor cj.hor) (ops.hId B) :=
  let eq := laws.horLaws.id_laws.id_comp (ops.hId B)
  eq.recOn (motive := fun h' _ =>
    sqs v v (ops.hComp cv.hor cj.hor) h')
    (psiHCompEpsilon ops v cv cj)

/-- η ⬝ₕ φ with identity laws applied: sqs v v (hId A) (v_* ⬝ v*). -/
def etaHCompPhi' : sqs v v (ops.hId A) (ops.hComp cj.hor cv.hor) :=
  let eq := laws.horLaws.id_laws.id_comp (ops.hId A)
  eq.recOn (motive := fun h' _ =>
    sqs v v h' (ops.hComp cj.hor cv.hor))
    (etaHCompPhi ops v cv cj)

/-! ### Triangle Identities

The triangle identities express that whiskering unit/counit by the companion
or conjoint and composing vertically yields identity squares.

Right triangle (for v*):
  sqVComp (adjunctionUnit' ⬝ₕ sqVertId v*) (sqVertId v* ⬝ₕ adjunctionCounit') = sqVertId v*

Left triangle (for v_*):
  sqVComp (sqVertId v_* ⬝ₕ adjunctionUnit') (adjunctionCounit' ⬝ₕ sqVertId v_*) = sqVertId v_*
-/

/-- Whisker adjunctionUnit' by cv.hor on the right.

Raw type: sqs (vId A) (vId B) (hId A ⬝ v*) ((v* ⬝ v_*) ⬝ v*)
-/
def unitWhiskerRight : sqs (ops.vId A) (ops.vId B)
    (ops.hComp (ops.hId A) cv.hor) (ops.hComp (ops.hComp cv.hor cj.hor) cv.hor) :=
  ops.sqHComp (adjunctionUnit' ops laws v cv cj) (ops.sqVertId cv.hor)

/-- Whisker cv.hor on the left by adjunctionCounit'.

Raw type: sqs (vId A) (vId B) (v* ⬝ (v_* ⬝ v*)) (v* ⬝ hId B)
-/
def counitWhiskerLeft : sqs (ops.vId A) (ops.vId B)
    (ops.hComp cv.hor (ops.hComp cj.hor cv.hor)) (ops.hComp cv.hor (ops.hId B)) :=
  ops.sqHComp (ops.sqVertId cv.hor) (adjunctionCounit' ops laws v cv cj)

/-- Whisker adjunctionUnit' by cv.hor on the right, with identity law applied to top.

Type: sqs (vId A) (vId B) v* ((v* ⬝ v_*) ⬝ v*)
-/
def unitWhiskerRight' : sqs (ops.vId A) (ops.vId B)
    cv.hor (ops.hComp (ops.hComp cv.hor cj.hor) cv.hor) :=
  let eq := laws.horLaws.id_laws.id_comp cv.hor
  eq.recOn (motive := fun h' _ =>
    sqs (ops.vId A) (ops.vId B) h' (ops.hComp (ops.hComp cv.hor cj.hor) cv.hor))
    (unitWhiskerRight ops laws v cv cj)

/-- Whisker cv.hor on the left by adjunctionCounit', with identity law applied to bottom.

Type: sqs (vId A) (vId B) (v* ⬝ (v_* ⬝ v*)) v*
-/
def counitWhiskerLeft' : sqs (ops.vId A) (ops.vId B)
    (ops.hComp cv.hor (ops.hComp cj.hor cv.hor)) cv.hor :=
  let eq := laws.horLaws.id_laws.comp_id cv.hor
  eq.recOn (motive := fun h' _ =>
    sqs (ops.vId A) (ops.vId B) (ops.hComp cv.hor (ops.hComp cj.hor cv.hor)) h')
    (counitWhiskerLeft ops laws v cv cj)

/-- Apply associativity to unitWhiskerRight' to get bottom boundary v* ⬝ (v_* ⬝ v*).

Type: sqs (vId A) (vId B) v* (v* ⬝ (v_* ⬝ v*))
-/
def unitWhiskerRight'' : sqs (ops.vId A) (ops.vId B)
    cv.hor (ops.hComp cv.hor (ops.hComp cj.hor cv.hor)) :=
  let eq := laws.horLaws.assoc cv.hor cj.hor cv.hor
  eq.recOn (motive := fun h' _ =>
    sqs (ops.vId A) (ops.vId B) cv.hor h')
    (unitWhiskerRight' ops laws v cv cj)

/-- Right triangle raw: vertical composite of whiskered unit and counit.

Raw type has `vComp (vId A) (vId A)` vertical boundaries from sqVComp.
-/
def rightTriangleCompositeRaw : sqs (ops.vComp (ops.vId A) (ops.vId A))
    (ops.vComp (ops.vId B) (ops.vId B)) cv.hor cv.hor :=
  ops.sqVComp (unitWhiskerRight'' ops laws v cv cj) (counitWhiskerLeft' ops laws v cv cj)

/-- Right triangle: vertical composite of whiskered unit and counit.

The composite (unitWhiskerRight'' ⬝ᵥ counitWhiskerLeft') should equal sqVertId cv.hor.
-/
def rightTriangleComposite : sqs (ops.vId A) (ops.vId B) cv.hor cv.hor :=
  let eqLeft := laws.vertLaws.id_laws.id_comp (ops.vId A)
  let eqRight := laws.vertLaws.id_laws.id_comp (ops.vId B)
  eqLeft.recOn (motive := fun v' _ =>
    sqs v' (ops.vId B) cv.hor cv.hor)
    (eqRight.recOn (motive := fun v' _ =>
      sqs (ops.vComp (ops.vId A) (ops.vId A)) v' cv.hor cv.hor)
      (rightTriangleCompositeRaw ops laws v cv cj))

/-- Whisker cj.hor on the right by adjunctionUnit'.

Raw type: sqs (vId A) (vId B) (v_* ⬝ hId A) (v_* ⬝ (v* ⬝ v_*))
-/
def unitWhiskerLeftConj : sqs (ops.vId B) (ops.vId A)
    (ops.hComp cj.hor (ops.hId A)) (ops.hComp cj.hor (ops.hComp cv.hor cj.hor)) :=
  ops.sqHComp (ops.sqVertId cj.hor) (adjunctionUnit' ops laws v cv cj)

/-- Whisker adjunctionCounit' by cj.hor on the left.

Raw type: sqs (vId B) (vId A) ((v_* ⬝ v*) ⬝ v_*) (hId B ⬝ v_*)
-/
def counitWhiskerRightConj : sqs (ops.vId B) (ops.vId A)
    (ops.hComp (ops.hComp cj.hor cv.hor) cj.hor) (ops.hComp (ops.hId B) cj.hor) :=
  ops.sqHComp (adjunctionCounit' ops laws v cv cj) (ops.sqVertId cj.hor)

/-- Whisker cj.hor on the right by adjunctionUnit', with identity law applied.

Type: sqs (vId B) (vId A) v_* (v_* ⬝ (v* ⬝ v_*))
-/
def unitWhiskerLeftConj' : sqs (ops.vId B) (ops.vId A)
    cj.hor (ops.hComp cj.hor (ops.hComp cv.hor cj.hor)) :=
  let eq := laws.horLaws.id_laws.comp_id cj.hor
  eq.recOn (motive := fun h' _ =>
    sqs (ops.vId B) (ops.vId A) h' (ops.hComp cj.hor (ops.hComp cv.hor cj.hor)))
    (unitWhiskerLeftConj ops laws v cv cj)

/-- Whisker adjunctionCounit' by cj.hor on the left, with identity law applied.

Type: sqs (vId B) (vId A) ((v_* ⬝ v*) ⬝ v_*) v_*
-/
def counitWhiskerRightConj' : sqs (ops.vId B) (ops.vId A)
    (ops.hComp (ops.hComp cj.hor cv.hor) cj.hor) cj.hor :=
  let eq := laws.horLaws.id_laws.id_comp cj.hor
  eq.recOn (motive := fun h' _ =>
    sqs (ops.vId B) (ops.vId A) (ops.hComp (ops.hComp cj.hor cv.hor) cj.hor) h')
    (counitWhiskerRightConj ops laws v cv cj)

/-- Apply associativity to counitWhiskerRightConj' to get top boundary v_* ⬝ (v* ⬝ v_*).

Type: sqs (vId B) (vId A) (v_* ⬝ (v* ⬝ v_*)) v_*
-/
def counitWhiskerRightConj'' : sqs (ops.vId B) (ops.vId A)
    (ops.hComp cj.hor (ops.hComp cv.hor cj.hor)) cj.hor :=
  let eq := laws.horLaws.assoc cj.hor cv.hor cj.hor
  eq.recOn (motive := fun h' _ =>
    sqs (ops.vId B) (ops.vId A) h' cj.hor)
    (counitWhiskerRightConj' ops laws v cv cj)

/-- Left triangle raw: vertical composite of whiskered unit and counit.

Raw type has `vComp (vId B) (vId B)` vertical boundaries from sqVComp.
-/
def leftTriangleCompositeRaw : sqs (ops.vComp (ops.vId B) (ops.vId B))
    (ops.vComp (ops.vId A) (ops.vId A)) cj.hor cj.hor :=
  ops.sqVComp (unitWhiskerLeftConj' ops laws v cv cj) (counitWhiskerRightConj'' ops laws v cv cj)

/-- Left triangle: vertical composite of whiskered unit and counit.

The composite (unitWhiskerLeftConj' ⬝ᵥ counitWhiskerRightConj'') should equal sqVertId cj.hor.
-/
def leftTriangleComposite : sqs (ops.vId B) (ops.vId A) cj.hor cj.hor :=
  let eqLeft := laws.vertLaws.id_laws.id_comp (ops.vId B)
  let eqRight := laws.vertLaws.id_laws.id_comp (ops.vId A)
  eqLeft.recOn (motive := fun v' _ =>
    sqs v' (ops.vId A) cj.hor cj.hor)
    (eqRight.recOn (motive := fun v' _ =>
      sqs (ops.vComp (ops.vId B) (ops.vId B)) v' cj.hor cj.hor)
      (leftTriangleCompositeRaw ops laws v cv cj))

/-! #### Triangle Identity Lemma Chain

We build the proof through small lemmas, each making one step of progress.
The strategy is to peel off type transports layer by layer, apply interchange,
then use cv.identity and cj.identity to simplify to the identity square.
-/

/-- Lemma 1: counitWhiskerLeft' is HEq to counitWhiskerLeft with type transport. -/
theorem counitWhiskerLeft'_heq_counitWhiskerLeft :
    HEq (counitWhiskerLeft' ops laws v cv cj)
        (counitWhiskerLeft ops laws v cv cj) := by
  simp only [counitWhiskerLeft']
  exact eqRec_heq_self _ (laws.horLaws.id_laws.comp_id cv.hor)

/-- Lemma 2: unitWhiskerRight' is HEq to unitWhiskerRight with type transport. -/
theorem unitWhiskerRight'_heq_unitWhiskerRight :
    HEq (unitWhiskerRight' ops laws v cv cj)
        (unitWhiskerRight ops laws v cv cj) := by
  simp only [unitWhiskerRight']
  exact eqRec_heq_self _ (laws.horLaws.id_laws.id_comp cv.hor)

/-- Lemma 3: unitWhiskerRight'' is HEq to unitWhiskerRight' with type transport. -/
theorem unitWhiskerRight''_heq_unitWhiskerRight' :
    HEq (unitWhiskerRight'' ops laws v cv cj)
        (unitWhiskerRight' ops laws v cv cj) := by
  simp only [unitWhiskerRight'']
  exact eqRec_heq_self _ (laws.horLaws.assoc cv.hor cj.hor cv.hor)

/-- Lemma 4: unitWhiskerRight'' is HEq to unitWhiskerRight (transitive). -/
theorem unitWhiskerRight''_heq_unitWhiskerRight :
    HEq (unitWhiskerRight'' ops laws v cv cj)
        (unitWhiskerRight ops laws v cv cj) :=
  HEq.trans (unitWhiskerRight''_heq_unitWhiskerRight' ops laws v cv cj)
            (unitWhiskerRight'_heq_unitWhiskerRight ops laws v cv cj)

/-- Lemma 5: adjunctionUnit' is HEq to adjunctionUnit with type transport. -/
theorem adjunctionUnit'_heq_adjunctionUnit :
    HEq (adjunctionUnit' ops laws v cv cj)
        (adjunctionUnit ops v cv cj) := by
  simp only [adjunctionUnit']
  exact eqRec_heq_self _ (laws.horLaws.id_laws.id_comp (ops.hId A))

/-- Lemma 6: adjunctionCounit' is HEq to adjunctionCounit with type transport. -/
theorem adjunctionCounit'_heq_adjunctionCounit :
    HEq (adjunctionCounit' ops laws v cv cj)
        (adjunctionCounit ops v cv cj) := by
  simp only [adjunctionCounit']
  exact eqRec_heq_self _ (laws.horLaws.id_laws.id_comp (ops.hId B))

/-- Lemma 7: unitWhiskerRight is HEq to sqHComp of adjunctionUnit and sqVertId. -/
theorem unitWhiskerRight_eq :
    unitWhiskerRight ops laws v cv cj =
    ops.sqHComp (adjunctionUnit' ops laws v cv cj) (ops.sqVertId cv.hor) := rfl

/-- Lemma 8: counitWhiskerLeft is HEq to sqHComp of sqVertId and adjunctionCounit. -/
theorem counitWhiskerLeft_eq :
    counitWhiskerLeft ops laws v cv cj =
    ops.sqHComp (ops.sqVertId cv.hor) (adjunctionCounit' ops laws v cv cj) := rfl

/-- Lemma 9: adjunctionUnit is HEq to sqHComp of phi and eta. -/
theorem adjunctionUnit_eq :
    adjunctionUnit ops v cv cj = ops.sqHComp cv.phi cj.eta := rfl

/-- Lemma 10: adjunctionCounit is HEq to sqHComp of epsilon and psi. -/
theorem adjunctionCounit_eq :
    adjunctionCounit ops v cv cj = ops.sqHComp cj.epsilon cv.psi := rfl

/-- Lemma 11: Expand unitWhiskerRight to primitive sqHComp form.

unitWhiskerRight = sqHComp (sqHComp phi eta) (sqVertId v*) with transport on phi ⬝ₕ eta.
-/
theorem unitWhiskerRight_expand :
    HEq (unitWhiskerRight ops laws v cv cj)
        (ops.sqHComp (ops.sqHComp cv.phi cj.eta) (ops.sqVertId cv.hor)) := by
  rw [unitWhiskerRight_eq]
  exact sqHComp_heq_left ops (ops.sqVertId cv.hor)
    (adjunctionUnit'_heq_adjunctionUnit ops laws v cv cj)
    (laws.horLaws.id_laws.id_comp (ops.hId A)).symm
    rfl

/-- Lemma 12: Expand counitWhiskerLeft to primitive sqHComp form.

counitWhiskerLeft = sqHComp (sqVertId v*) (sqHComp epsilon psi) with transport.
-/
theorem counitWhiskerLeft_expand :
    HEq (counitWhiskerLeft ops laws v cv cj)
        (ops.sqHComp (ops.sqVertId cv.hor) (ops.sqHComp cj.epsilon cv.psi)) := by
  rw [counitWhiskerLeft_eq]
  exact sqHComp_heq_right ops (ops.sqVertId cv.hor)
    (adjunctionCounit'_heq_adjunctionCounit ops laws v cv cj)
    rfl
    (laws.horLaws.id_laws.id_comp (ops.hId B)).symm

/-- Lemma 13: Apply associativity to unitWhiskerRight_expand.

sqHComp (sqHComp phi eta) (sqVertId v*) ≅ sqHComp phi (sqHComp eta (sqVertId v*))
-/
theorem unitWhiskerRight_assoc (laws : DoubleCategoryLaws ops) :
    HEq (ops.sqHComp (ops.sqHComp cv.phi cj.eta) (ops.sqVertId cv.hor))
        (ops.sqHComp cv.phi (ops.sqHComp cj.eta (ops.sqVertId cv.hor))) :=
  laws.sqLaws.sqHAssoc cv.phi cj.eta (ops.sqVertId cv.hor)

/-- Lemma 14: Apply associativity to counitWhiskerLeft_expand.

sqHComp (sqVertId v*) (sqHComp epsilon psi) ≅ sqHComp (sqHComp (sqVertId v*) epsilon) psi
-/
theorem counitWhiskerLeft_assoc (laws : DoubleCategoryLaws ops) :
    HEq (ops.sqHComp (ops.sqVertId cv.hor) (ops.sqHComp cj.epsilon cv.psi))
        (ops.sqHComp (ops.sqHComp (ops.sqVertId cv.hor) cj.epsilon) cv.psi) :=
  (laws.sqLaws.sqHAssoc (ops.sqVertId cv.hor) cj.epsilon cv.psi).symm

/-- Lemma 15: Combine unitWhiskerRight lemmas for a full expansion.

unitWhiskerRight ≅ sqHComp phi (sqHComp eta (sqVertId v*))
-/
theorem unitWhiskerRight_full_expand :
    HEq (unitWhiskerRight ops laws v cv cj)
        (ops.sqHComp cv.phi (ops.sqHComp cj.eta (ops.sqVertId cv.hor))) := by
  exact HEq.trans (unitWhiskerRight_expand ops laws v cv cj)
                  (unitWhiskerRight_assoc ops v cv cj laws)

/-- Lemma 16: Combine counitWhiskerLeft lemmas for a full expansion.

counitWhiskerLeft ≅ sqHComp (sqHComp (sqVertId v*) epsilon) psi
-/
theorem counitWhiskerLeft_full_expand :
    HEq (counitWhiskerLeft ops laws v cv cj)
        (ops.sqHComp (ops.sqHComp (ops.sqVertId cv.hor) cj.epsilon) cv.psi) := by
  exact HEq.trans (counitWhiskerLeft_expand ops laws v cv cj)
                  (counitWhiskerLeft_assoc ops v cv cj laws)

/-- Lemma 17: The horizontal composition (sqVertId v*) ⬝ₕ epsilon has a specific form.

This equals a square with vertical composition under the hood. We use this to
connect to cv.psi for the triangle identity.
-/
theorem sqVertId_hcomp_epsilon :
    ops.sqHComp (ops.sqVertId cv.hor) cj.epsilon =
    ops.sqHComp (ops.sqVertId cv.hor) cj.epsilon := rfl

/-- Lemma 18: The horizontal composition eta ⬝ₕ (sqVertId v*) characterization. -/
theorem eta_hcomp_sqVertId :
    ops.sqHComp cj.eta (ops.sqVertId cv.hor) =
    ops.sqHComp cj.eta (ops.sqVertId cv.hor) := rfl

/-- Lemma 19: Composition lemma for triangle identity.

After expanding and applying associativity, we have:
- unitWhiskerRight ≅ sqHComp phi (sqHComp eta (sqVertId v*))
- counitWhiskerLeft ≅ sqHComp (sqHComp (sqVertId v*) epsilon) psi

When we compose these vertically, the middle boundary of unitWhiskerRight
is (v* ⬝ v_*) ⬝ v* (before transports) and for counitWhiskerLeft it's
v* ⬝ (v_* ⬝ v*).

This lemma relates rightTriangleCompositeRaw through type transports.
-/
theorem rightTriangleCompositeRaw_expand :
    HEq (rightTriangleCompositeRaw ops laws v cv cj)
        (ops.sqVComp (unitWhiskerRight'' ops laws v cv cj)
                     (counitWhiskerLeft' ops laws v cv cj)) := HEq.rfl

/-- Lemma 20: rightTriangleComposite is HEq to rightTriangleCompositeRaw.

The two definitions differ only by type transports on vertical boundaries.
-/
theorem rightTriangleComposite_heq_raw :
    HEq (rightTriangleComposite ops laws v cv cj)
        (rightTriangleCompositeRaw ops laws v cv cj) := by
  simp only [rightTriangleComposite]
  apply HEq.trans
  · exact eqRec_heq_self _ (laws.vertLaws.id_laws.id_comp (ops.vId A))
  · exact eqRec_heq_self _ (laws.vertLaws.id_laws.id_comp (ops.vId B))

/-- Lemma 21: rightTriangleComposite is HEq to sqVComp of double-primed whiskers.

Combines lemmas 19 and 20: rightTriangleComposite ≅ rightTriangleCompositeRaw
≅ sqVComp unitWhiskerRight'' counitWhiskerLeft'.
-/
theorem rightTriangleComposite_expand :
    HEq (rightTriangleComposite ops laws v cv cj)
        (ops.sqVComp (unitWhiskerRight'' ops laws v cv cj)
                     (counitWhiskerLeft' ops laws v cv cj)) :=
  HEq.trans (rightTriangleComposite_heq_raw ops laws v cv cj)
            (rightTriangleCompositeRaw_expand ops laws v cv cj)

/-- Lemma 23: Relate unitWhiskerRight'' to a form with sqHComp phi (sqHComp eta sqVertId).

This expands unitWhiskerRight'' through the full chain of transports.
-/
theorem unitWhiskerRight''_expand_full :
    HEq (unitWhiskerRight'' ops laws v cv cj)
        (ops.sqHComp cv.phi (ops.sqHComp cj.eta (ops.sqVertId cv.hor))) := by
  apply HEq.trans (unitWhiskerRight''_heq_unitWhiskerRight ops laws v cv cj)
  exact unitWhiskerRight_full_expand ops laws v cv cj

/-- Lemma 24: Relate counitWhiskerLeft' to a form with sqHComp (sqHComp sqVertId epsilon) psi.

This expands counitWhiskerLeft' through the full chain of transports.
-/
theorem counitWhiskerLeft'_expand_full :
    HEq (counitWhiskerLeft' ops laws v cv cj)
        (ops.sqHComp (ops.sqHComp (ops.sqVertId cv.hor) cj.epsilon) cv.psi) := by
  apply HEq.trans (counitWhiskerLeft'_heq_counitWhiskerLeft ops laws v cv cj)
  exact counitWhiskerLeft_full_expand ops laws v cv cj

/-- sqHComp eta (sqVertId cv.hor) is reflexively equal to itself. -/
theorem eta_sqVertId_simplify :
    HEq (ops.sqHComp cj.eta (ops.sqVertId cv.hor))
        (ops.sqHComp cj.eta (ops.sqVertId cv.hor)) := HEq.rfl

/-- sqHComp (sqVertId cv.hor) epsilon is reflexively equal to itself. -/
theorem sqVertId_epsilon_simplify :
    HEq (ops.sqHComp (ops.sqVertId cv.hor) cj.epsilon)
        (ops.sqHComp (ops.sqVertId cv.hor) cj.epsilon) := HEq.rfl

/-- Raw form of adjunctionUnit without identity transport. -/
def adjunctionUnitRaw : sqs (ops.vId A) (ops.vId A)
    (ops.hComp (ops.hId A) (ops.hId A)) (ops.hComp cv.hor cj.hor) :=
  ops.sqHComp cv.phi cj.eta

/-- Raw form of adjunctionCounit without identity transport. -/
def adjunctionCounitRaw : sqs (ops.vId B) (ops.vId B)
    (ops.hComp cj.hor cv.hor) (ops.hComp (ops.hId B) (ops.hId B)) :=
  ops.sqHComp cj.epsilon cv.psi

/-- Raw form of unitWhiskerRight without identity/associativity transports. -/
def unitWhiskerRightRaw : sqs (ops.vId A) (ops.vId B)
    (ops.hComp (ops.hComp (ops.hId A) (ops.hId A)) cv.hor)
    (ops.hComp (ops.hComp cv.hor cj.hor) cv.hor) :=
  ops.sqHComp (adjunctionUnitRaw ops v cv cj) (ops.sqVertId cv.hor)

/-- Raw form of counitWhiskerLeft without identity transport. -/
def counitWhiskerLeftRaw : sqs (ops.vId A) (ops.vId B)
    (ops.hComp cv.hor (ops.hComp cj.hor cv.hor))
    (ops.hComp cv.hor (ops.hComp (ops.hId B) (ops.hId B))) :=
  ops.sqHComp (ops.sqVertId cv.hor) (adjunctionCounitRaw ops v cv cj)

theorem sqVComp_whiskers_eq_sqVertId
    (h_vComp_eta_eps : HEq (ops.sqVComp cj.eta cj.epsilon) (ops.sqHorId v))
    (h_hComp_phi_psi : HEq (ops.sqHComp cv.phi cv.psi) (ops.sqVertId cv.hor)) :
    HEq (ops.sqVComp (unitWhiskerRight'' ops laws v cv cj)
                     (counitWhiskerLeft' ops laws v cv cj))
        (ops.sqVertId cv.hor) := by
  have h_vIdComp_A : ops.vComp (ops.vId A) (ops.vId A) = ops.vId A :=
    laws.vertLaws.id_laws.id_comp (ops.vId A)
  have h_vIdComp_B : ops.vComp (ops.vId B) (ops.vId B) = ops.vId B :=
    laws.vertLaws.id_laws.id_comp (ops.vId B)
  have h_sqVComp_sqVertId :
      HEq (ops.sqVComp (ops.sqVertId cv.hor) (ops.sqVertId cv.hor))
          (ops.sqVertId cv.hor) :=
    sqVIdComp_heq ops laws (ops.sqVertId cv.hor)
  let phiEtaSqVertId := ops.sqHComp cv.phi (ops.sqHComp cj.eta (ops.sqVertId cv.hor))
  let sqVertIdEpsPsi := ops.sqHComp (ops.sqHComp (ops.sqVertId cv.hor) cj.epsilon)
                                     cv.psi
  have h_uwr''_expand : HEq (unitWhiskerRight'' ops laws v cv cj) phiEtaSqVertId :=
    unitWhiskerRight''_expand_full ops laws v cv cj
  have h_cwl'_expand : HEq (counitWhiskerLeft' ops laws v cv cj) sqVertIdEpsPsi :=
    counitWhiskerLeft'_expand_full ops laws v cv cj
  have h_hAssoc_mid : ops.hComp cv.hor (ops.hComp cj.hor cv.hor) =
                      ops.hComp (ops.hComp cv.hor cj.hor) cv.hor :=
    (laws.horLaws.assoc cv.hor cj.hor cv.hor).symm
  have h_hIdComp_top : ops.hComp (ops.hId A) (ops.hComp (ops.hId A) cv.hor) = cv.hor :=
    Eq.trans (congrArg (ops.hComp (ops.hId A))
                       (laws.horLaws.id_laws.id_comp cv.hor))
             (laws.horLaws.id_laws.id_comp cv.hor)
  have h_hCompId_bot : ops.hComp (ops.hComp cv.hor (ops.hId B)) (ops.hId B) = cv.hor :=
    Eq.trans (congrArg (fun x => ops.hComp x (ops.hId B))
                       (laws.horLaws.id_laws.comp_id cv.hor))
             (laws.horLaws.id_laws.comp_id cv.hor)
  let phi := cv.phi
  let psi := cv.psi
  let eta := cj.eta
  let epsilon := cj.epsilon
  have h_cv_identity : HEq (ops.sqVComp phi psi) (ops.sqHorId v) := cv.identity
  have h_cj_identity : HEq (ops.sqHComp epsilon eta) (ops.sqVertId cj.hor) := cj.identity
  let unitRaw := ops.sqHComp (ops.sqHComp phi eta) (ops.sqVertId cv.hor)
  let counitRaw := ops.sqHComp (ops.sqVertId cv.hor) (ops.sqHComp epsilon psi)
  have h_phiEtaSqVertId_assoc :
      HEq phiEtaSqVertId unitRaw :=
    (sqHAssoc_heq ops laws phi eta (ops.sqVertId cv.hor)).symm
  have h_sqVertIdEpsPsi_assoc :
      HEq sqVertIdEpsPsi counitRaw :=
    sqHAssoc_heq ops laws (ops.sqVertId cv.hor) epsilon psi
  have h_uwr''_heq_unitRaw :
      HEq (unitWhiskerRight'' ops laws v cv cj) unitRaw :=
    HEq.trans h_uwr''_expand h_phiEtaSqVertId_assoc
  have h_cwl'_heq_counitRaw :
      HEq (counitWhiskerLeft' ops laws v cv cj) counitRaw :=
    HEq.trans h_cwl'_expand h_sqVertIdEpsPsi_assoc
  have h_hIdComp : ops.hComp (ops.hId A) (ops.hId A) = ops.hId A :=
    laws.horLaws.id_laws.id_comp (ops.hId A)
  have h_hCompId : ops.hComp (ops.hId B) (ops.hId B) = ops.hId B :=
    laws.horLaws.id_laws.id_comp (ops.hId B)
  have h_vIdComp_vIdA_v : ops.vComp (ops.vId A) v = v :=
    laws.vertLaws.id_laws.id_comp v
  have h_vComp_v_vIdB : ops.vComp v (ops.vId B) = v :=
    laws.vertLaws.id_laws.comp_id v
  have h_vComp_vIdA_vIdA : ops.vComp (ops.vId A) (ops.vId A) = ops.vId A :=
    laws.vertLaws.id_laws.id_comp (ops.vId A)
  have h_vComp_vIdB_vIdB : ops.vComp (ops.vId B) (ops.vId B) = ops.vId B :=
    laws.vertLaws.id_laws.id_comp (ops.vId B)
  let etaSqVertId := ops.sqHComp eta (ops.sqVertId cv.hor)
  let sqVertIdEps := ops.sqHComp (ops.sqVertId cv.hor) epsilon
  have h_phiEtaSqVertId_eq : phiEtaSqVertId = ops.sqHComp phi etaSqVertId := rfl
  have h_sqVertIdEpsPsi_eq : sqVertIdEpsPsi = ops.sqHComp sqVertIdEps psi := rfl
  have h_assoc_uwr : HEq phiEtaSqVertId unitRaw :=
    (sqHAssoc_heq ops laws phi eta (ops.sqVertId cv.hor)).symm
  have h_assoc_cwl : HEq sqVertIdEpsPsi counitRaw :=
    sqHAssoc_heq ops laws (ops.sqVertId cv.hor) epsilon psi
  have h_sqVComp_phi_sqVertId : HEq (ops.sqVComp phi (ops.sqVertId cv.hor)) phi :=
    sqVCompId_heq ops laws phi
  have h_sqVComp_sqVertId_psi : HEq (ops.sqVComp (ops.sqVertId cv.hor) psi) psi :=
    sqVIdComp_heq ops laws psi
  have h_sqVComp_eta_sqVertId :
      HEq (ops.sqVComp eta (ops.sqVertId cj.hor)) eta :=
    sqVCompId_heq ops laws eta
  have h_sqVComp_sqVertId_epsilon :
      HEq (ops.sqVComp (ops.sqVertId cj.hor) epsilon) epsilon :=
    sqVIdComp_heq ops laws epsilon
  let phiEta := ops.sqHComp phi eta
  let sqVertIdEps := ops.sqHComp (ops.sqVertId cv.hor) epsilon
  let epsPsi := ops.sqHComp epsilon psi
  let sqVertIdEpsPsiTransp_ty_eq : sqs (ops.vId A) (ops.vId B)
          (ops.hComp (ops.hComp cv.hor cj.hor) cv.hor)
          (ops.hComp (ops.hComp cv.hor (ops.hId B)) (ops.hId B)) =
        sqs (ops.vId A) (ops.vId B)
          (ops.hComp cv.hor (ops.hComp cj.hor cv.hor))
          (ops.hComp (ops.hComp cv.hor (ops.hId B)) (ops.hId B)) :=
    congrArg (fun h => sqs (ops.vId A) (ops.vId B) h
                         (ops.hComp (ops.hComp cv.hor (ops.hId B)) (ops.hId B)))
      h_hAssoc_mid.symm
  let sqVertIdEpsPsiTransp : sqs (ops.vId A) (ops.vId B)
        (ops.hComp cv.hor (ops.hComp cj.hor cv.hor))
        (ops.hComp (ops.hComp cv.hor (ops.hId B)) (ops.hId B)) :=
    cast sqVertIdEpsPsiTransp_ty_eq sqVertIdEpsPsi
  have h_sqVertIdEpsPsi_transp :
      HEq sqVertIdEpsPsi sqVertIdEpsPsiTransp :=
    (cast_heq sqVertIdEpsPsiTransp_ty_eq sqVertIdEpsPsi).symm
  have h_cwl'_expand_transp :
      HEq (counitWhiskerLeft' ops laws v cv cj) sqVertIdEpsPsiTransp :=
    HEq.trans h_cwl'_expand h_sqVertIdEpsPsi_transp
  have h_vcomp_whiskers_heq :
      HEq (ops.sqVComp (unitWhiskerRight'' ops laws v cv cj)
                       (counitWhiskerLeft' ops laws v cv cj))
          (ops.sqVComp phiEtaSqVertId sqVertIdEpsPsiTransp) :=
    sqVComp_heq_both ops h_uwr''_expand h_cwl'_expand_transp
      h_hIdComp_top.symm rfl h_hCompId_bot.symm
  let phiEta := ops.sqHComp phi eta
  let epsPsi := ops.sqHComp epsilon psi
  have h_phiEtaSqVertId_assoc2 :
      HEq phiEtaSqVertId (ops.sqHComp phiEta (ops.sqVertId cv.hor)) :=
    (sqHAssoc_heq ops laws phi eta (ops.sqVertId cv.hor)).symm
  have h_sqVertIdEpsPsi_assoc2 :
      HEq sqVertIdEpsPsi (ops.sqHComp (ops.sqVertId cv.hor) epsPsi) :=
    sqHAssoc_heq ops laws (ops.sqVertId cv.hor) epsilon psi
  have h_phiPsi_type_eq : ops.hComp (ops.hId A) cv.hor = cv.hor :=
    laws.horLaws.id_laws.id_comp cv.hor
  have h_cvPsi_type_eq : ops.hComp cv.hor (ops.hId B) = cv.hor :=
    laws.horLaws.id_laws.comp_id cv.hor
  have h_interch_outer := laws.sqLaws.interchange phi (ops.sqHComp eta (ops.sqVertId cv.hor))
                            (ops.sqVertId cv.hor) (ops.sqHComp epsilon psi)
  have h_interch_inner := laws.sqLaws.interchange eta (ops.sqVertId cv.hor) epsilon psi
  have h_sqVComp_phi_sqVertId :
      HEq (ops.sqVComp phi (ops.sqVertId cv.hor)) phi :=
    sqVCompId_heq ops laws phi
  have h_sqVComp_sqVertId_psi :
      HEq (ops.sqVComp (ops.sqVertId cv.hor) psi) psi :=
    sqVIdComp_heq ops laws psi
  let etaEps := ops.sqVComp eta epsilon
  have h_etaEps_vL : ops.vComp v (ops.vId B) = v := laws.vertLaws.id_laws.comp_id v
  have h_etaEps_vR : ops.vComp (ops.vId A) v = v := laws.vertLaws.id_laws.id_comp v
  let etaEpsTyEq : sqs (ops.vComp v (ops.vId B)) (ops.vComp (ops.vId A) v)
                       (ops.hId A) (ops.hId B) =
                   sqs v v (ops.hId A) (ops.hId B) := by rw [h_etaEps_vL, h_etaEps_vR]
  let etaEpsTransp : sqs v v (ops.hId A) (ops.hId B) := cast etaEpsTyEq etaEps
  have h_etaEps_transp : HEq etaEps etaEpsTransp := (cast_heq etaEpsTyEq etaEps).symm
  have h_combined_interch :
      ops.sqVComp phiEtaSqVertId counitRaw =
      ops.sqHComp (ops.sqVComp phi (ops.sqVertId cv.hor))
                  (ops.sqHComp (ops.sqVComp eta epsilon) (ops.sqVComp (ops.sqVertId cv.hor) psi)) :=
    h_interch_outer.trans
      (congrArg (ops.sqHComp (ops.sqVComp phi (ops.sqVertId cv.hor)))
                h_interch_inner)
  have h_simplify_outer_left :
      HEq (ops.sqVComp phi (ops.sqVertId cv.hor)) phi :=
    h_sqVComp_phi_sqVertId
  have h_simplify_inner_right :
      HEq (ops.sqVComp (ops.sqVertId cv.hor) psi) psi :=
    h_sqVComp_sqVertId_psi
  have h_vLeft : ops.vComp (ops.vId A) (ops.vId A) = ops.vId A :=
    laws.vertLaws.id_laws.id_comp (ops.vId A)
  have h_vRight : ops.vComp (ops.vId B) (ops.vId B) = ops.vId B :=
    laws.vertLaws.id_laws.id_comp (ops.vId B)
  have h_hTop : ops.hComp (ops.hId A) (ops.hComp (ops.hId A) cv.hor) = cv.hor := by
    have h1 := laws.horLaws.id_laws.id_comp (ops.hComp (ops.hId A) cv.hor)
    have h2 := laws.horLaws.id_laws.id_comp cv.hor
    simp only [DoubleCategoryOps.horCategoryOps] at h1 h2
    exact h1.trans h2
  have h_hBot : ops.hComp cv.hor (ops.hComp (ops.hId B) (ops.hId B)) = cv.hor := by
    have h1 := laws.horLaws.id_laws.id_comp (ops.hId B)
    have h2 := laws.horLaws.id_laws.comp_id cv.hor
    simp only [DoubleCategoryOps.horCategoryOps] at h1 h2
    exact congrArg (ops.hComp cv.hor) h1 |>.trans h2
  let rhsType := sqs (ops.vComp (ops.vId A) (ops.vId A))
                     (ops.vComp (ops.vId B) (ops.vId B))
                     (ops.hComp (ops.hId A) (ops.hComp (ops.hId A) cv.hor))
                     (ops.hComp cv.hor (ops.hComp (ops.hId B) (ops.hId B)))
  let targetType := sqs (ops.vId A) (ops.vId B) cv.hor cv.hor
  have h_typeEq : rhsType = targetType := by
    simp only [rhsType, targetType]
    rw [h_vLeft, h_vRight, h_hTop, h_hBot]
  let rhs := ops.sqHComp (ops.sqVComp phi (ops.sqVertId cv.hor))
                         (ops.sqHComp (ops.sqVComp eta epsilon)
                                      (ops.sqVComp (ops.sqVertId cv.hor) psi))
  have h_rhs_eq : ops.sqVComp phiEtaSqVertId counitRaw = rhs := h_combined_interch
  have h_counitRaw_heq_transp : HEq counitRaw sqVertIdEpsPsiTransp := by
    apply HEq.trans h_sqVertIdEpsPsi_assoc.symm
    exact h_sqVertIdEpsPsi_transp
  have h_assoc_bot : ops.hComp (ops.hComp cv.hor (ops.hId B)) (ops.hId B) =
                     ops.hComp cv.hor (ops.hComp (ops.hId B) (ops.hId B)) := by
    have assoc := laws.horLaws.assoc cv.hor (ops.hId B) (ops.hId B)
    simp only [DoubleCategoryOps.horCategoryOps] at assoc
    exact assoc
  have h_sqVComp_with_transp_heq_counitRaw :
      HEq (ops.sqVComp phiEtaSqVertId sqVertIdEpsPsiTransp)
          (ops.sqVComp phiEtaSqVertId counitRaw) :=
    sqVComp_heq_all ops (HEq.refl _) h_counitRaw_heq_transp.symm
      rfl rfl rfl rfl rfl rfl h_assoc_bot
  let rhsTransp : targetType := cast h_typeEq rhs
  have h_rhs_transp : HEq rhs rhsTransp := (cast_heq h_typeEq rhs).symm
  let phiSimp := ops.sqVComp phi (ops.sqVertId cv.hor)
  let psiSimp := ops.sqVComp (ops.sqVertId cv.hor) psi
  have h_phi_simp : HEq phiSimp phi := sqVCompId_heq ops laws phi
  have h_psi_simp : HEq psiSimp psi := sqVIdComp_heq ops laws psi
  let simpForm := ops.sqHComp phi (ops.sqHComp etaEpsTransp psi)
  have h_inner_simp : HEq (ops.sqHComp etaEps psiSimp)
                          (ops.sqHComp etaEpsTransp psi) :=
    sqHComp_heq_all ops h_etaEps_transp h_psi_simp
      h_etaEps_vL h_etaEps_vR h_vIdComp_B
      rfl rfl rfl rfl
  have h_rhs_to_simp : HEq rhs simpForm := by
    simp only [rhs, simpForm]
    apply sqHComp_heq_all ops h_phi_simp h_inner_simp
    · exact h_vLeft
    · exact h_etaEps_vL
    · exact h_vRight
    · rfl
    · rfl
    · rfl
    · rfl
  have h_assoc : HEq simpForm (ops.sqHComp (ops.sqHComp phi etaEpsTransp) psi) :=
    (sqHAssoc_heq ops laws phi etaEpsTransp psi).symm
  let phiEtaEps := ops.sqHComp phi etaEpsTransp
  have h_phiEtaEps_hTop : ops.hComp (ops.hId A) (ops.hId A) = ops.hId A :=
    laws.horLaws.id_laws.id_comp (ops.hId A)
  have h_phiEtaEps_hBot : ops.hComp cv.hor (ops.hId B) = cv.hor :=
    laws.horLaws.id_laws.comp_id cv.hor
  have h_etaEpsPsi_hT : ops.hComp (ops.hId A) cv.hor = cv.hor :=
    laws.horLaws.id_laws.id_comp cv.hor
  have h_etaEpsPsi_hB : ops.hComp (ops.hId B) (ops.hId B) = ops.hId B :=
    laws.horLaws.id_laws.id_comp (ops.hId B)
  have h_etaEpsTransp_hComp_psi : HEq (ops.sqHComp etaEpsTransp psi) psi := by
    have h_id_A : ops.hComp (ops.hId A) cv.hor = cv.hor :=
      laws.horLaws.id_laws.id_comp cv.hor
    have h_id_B : ops.hComp (ops.hId B) (ops.hId B) = ops.hId B :=
      laws.horLaws.id_laws.id_comp (ops.hId B)
    have h_etaEps_eq_sqHorId : HEq etaEpsTransp (ops.sqHorId v) := by
      apply HEq.trans h_etaEps_transp.symm
      exact h_vComp_eta_eps
    exact HEq.trans
      (sqHComp_heq_left ops psi h_etaEps_eq_sqHorId rfl rfl)
      (sqHIdComp_heq ops laws psi)
  have h_phi_hComp_psi_eq_sqVertId : HEq (ops.sqHComp phi psi) (ops.sqVertId cv.hor) :=
    h_hComp_phi_psi
  have h_final_chain : HEq rhs (ops.sqVertId cv.hor) := by
    apply HEq.trans h_rhs_to_simp
    apply HEq.trans h_assoc
    apply HEq.trans (sqHAssoc_heq ops laws phi etaEpsTransp psi)
    apply HEq.trans (sqHComp_heq_right ops phi h_etaEpsTransp_hComp_psi
      (laws.horLaws.id_laws.id_comp cv.hor) (laws.horLaws.id_laws.id_comp (ops.hId B)))
    exact h_phi_hComp_psi_eq_sqVertId
  exact HEq.trans h_vcomp_whiskers_heq
    (HEq.trans h_sqVComp_with_transp_heq_counitRaw
    (HEq.trans (heq_of_eq h_rhs_eq) h_final_chain))

theorem rightTriangleIdentity
    (h_vComp_eta_eps : HEq (ops.sqVComp cj.eta cj.epsilon) (ops.sqHorId v))
    (h_hComp_phi_psi : HEq (ops.sqHComp cv.phi cv.psi) (ops.sqVertId cv.hor)) :
    rightTriangleComposite ops laws v cv cj = ops.sqVertId cv.hor := by
  apply eq_of_heq
  apply HEq.trans (rightTriangleComposite_expand ops laws v cv cj)
  exact sqVComp_whiskers_eq_sqVertId ops laws v cv cj h_vComp_eta_eps h_hComp_phi_psi

end CompanionConjointAdjunction

/-! ## Modifications between Transformations

A modification between two natural transformations (vertical or horizontal)
is a collection of 2-cells (squares) relating the components. In a double
category, modifications provide the structure for a 3-category of double
categories, functors, transformations, and modifications.
-/

/-- Operations for a modification between vertical transformations.

A modification Γ : τ ⟹ σ between vertical transformations τ, σ : F ⟹ᵥ G
assigns to each object A a square relating τ.app A and σ.app A:

```
       hId F(A)
    F(A) ─────→ F(A)
     |           |
τ_A  │    Γ_A    │ σ_A
     ↓           ↓
    G(A) ─────→ G(A)
       hId G(A)
```

The square has identity horizontal boundaries and the transformation
components as vertical boundaries.
-/
structure VertModOps {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (τ σ : VertTransOps F G) where
  /-- Component squares: one for each object -/
  app : ∀ (A : Obj₁), sqs₂ (τ.app A) (σ.app A) (ops₂.hId (F.objMap A))
                                                (ops₂.hId (G.objMap A))

/-- Operations for a modification between horizontal transformations.

A modification Γ : τ ⟹ σ between horizontal transformations τ, σ : F ⟹ₕ G
assigns to each object A a square relating τ.app A and σ.app A:

```
        τ_A
    F(A) ─────→ G(A)
     |           |
vId  │    Γ_A    │ vId
     ↓           ↓
    F(A) ─────→ G(A)
        σ_A
```

The square has identity vertical boundaries and the transformation
components as horizontal boundaries.
-/
structure HorModOps {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (τ σ : HorTransOps F G) where
  /-- Component squares: one for each object -/
  app : ∀ (A : Obj₁), sqs₂ (ops₂.vId (F.objMap A)) (ops₂.vId (G.objMap A))
                           (τ.app A) (σ.app A)

namespace VertModOps

variable {Obj₁ : Type u₁}
variable {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
variable {Obj₂ : Type u₂}
variable {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
variable (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
variable {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}

/-- Identity modification on a vertical transformation.

The identity modification uses horizontal identity squares sqHorId on the
transformation components, giving squares with τ_A on both vertical sides.
-/
def id (τ : VertTransOps F G) : VertModOps ops₂ τ τ where
  app A := ops₂.sqHorId (τ.app A)

/-- Horizontal composition of modifications between vertical transformations.

Given Γ : τ ⟹ σ and Δ : σ ⟹ ρ, their composite is τ ⟹ ρ. The composition
uses sqHComp which produces squares with horizontal boundaries
hComp (hId X) (hId X), requiring identity law transport to obtain hId X.
-/
def hComp {τ σ ρ : VertTransOps F G}
    (laws₂ : DoubleCategoryLaws ops₂)
    (Γ : VertModOps ops₂ τ σ) (Δ : VertModOps ops₂ σ ρ) : VertModOps ops₂ τ ρ where
  app A :=
    let rawComp := ops₂.sqHComp (Γ.app A) (Δ.app A)
    let eqTop := laws₂.horLaws.id_laws.id_comp (ops₂.hId (F.objMap A))
    let eqBot := laws₂.horLaws.id_laws.id_comp (ops₂.hId (G.objMap A))
    eqTop.recOn (motive := fun h' _ =>
      sqs₂ (τ.app A) (ρ.app A) h' (ops₂.hId (G.objMap A)))
      (eqBot.recOn (motive := fun h' _ =>
        sqs₂ (τ.app A) (ρ.app A)
          (ops₂.hComp (ops₂.hId (F.objMap A)) (ops₂.hId (F.objMap A))) h')
        rawComp)

end VertModOps

namespace HorModOps

variable {Obj₁ : Type u₁}
variable {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
variable {Obj₂ : Type u₂}
variable {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
variable (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
variable {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}

/-- Identity modification on a horizontal transformation.

The identity modification uses vertical identity squares sqVertId on the
transformation components, giving squares with τ_A on both horizontal sides.
-/
def id (τ : HorTransOps F G) : HorModOps ops₂ τ τ where
  app A := ops₂.sqVertId (τ.app A)

/-- Vertical composition of modifications between horizontal transformations.

Given Γ : τ ⟹ σ and Δ : σ ⟹ ρ, their composite is τ ⟹ ρ. The composition
uses sqVComp which produces squares with vertical boundaries
vComp (vId X) (vId X), requiring identity law transport to obtain vId X.
-/
def vComp {τ σ ρ : HorTransOps F G}
    (laws₂ : DoubleCategoryLaws ops₂)
    (Γ : HorModOps ops₂ τ σ) (Δ : HorModOps ops₂ σ ρ) : HorModOps ops₂ τ ρ where
  app A :=
    let rawComp := ops₂.sqVComp (Γ.app A) (Δ.app A)
    let eqLeft := laws₂.vertLaws.id_laws.id_comp (ops₂.vId (F.objMap A))
    let eqRight := laws₂.vertLaws.id_laws.id_comp (ops₂.vId (G.objMap A))
    eqLeft.recOn (motive := fun v' _ =>
      sqs₂ v' (ops₂.vId (G.objMap A)) (τ.app A) (ρ.app A))
      (eqRight.recOn (motive := fun v' _ =>
        sqs₂ (ops₂.vComp (ops₂.vId (F.objMap A)) (ops₂.vId (F.objMap A))) v'
          (τ.app A) (ρ.app A))
        rawComp)

end HorModOps

/-- Laws for a modification between vertical transformations.

For a modification Γ : τ ⟹ σ, naturality requires that for any horizontal
morphism f : A →ₕ B in the source category, the following diagram commutes:

```
                     F(f)
        F(A) ─────────────────────→ F(B)
         │                           │
    τ_A  │                           │ τ_B
         │    τ.natSquare(f)         │
         ↓                           ↓
        G(A) ─────────────────────→ G(B)
         │         G(f)              │
    σ_A  │                           │ σ_B
         │    σ.natSquare(f)         │
         ↓                           ↓
        G(A) ─────────────────────→ G(B)
                     G(f)
```

The law states: τ.natSquare(f) ⬝ₕ Γ_B ≅ Γ_A ⬝ₕ σ.natSquare(f)
(both paths give a square from τ_A to σ_B with top F(f) and bottom G(f))
-/
structure VertModLaws {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    {τ σ : VertTransOps F G}
    (Γ : VertModOps ops₂ τ σ) where
  /-- Naturality: τ.natSquare(f) ⬝ₕ Γ_B ≅ Γ_A ⬝ₕ σ.natSquare(f)

  The equality is heterogeneous because the two sides have different
  horizontal boundaries that are only propositionally equal:
  - LHS has top hComp (F.hMap f) (hId F(B)), bottom hComp (G.hMap f) (hId G(B))
  - RHS has top hComp (hId F(A)) (F.hMap f), bottom hComp (hId G(A)) (G.hMap f)
  These are equal by identity laws but not definitionally.
  -/
  naturality : ∀ {A B : Obj₁} (f : hhs₁ A B),
    HEq (ops₂.sqHComp (τ.natSquare f) (Γ.app B))
        (ops₂.sqHComp (Γ.app A) (σ.natSquare f))

/-- Laws for a modification between horizontal transformations.

For a modification Γ : τ ⟹ σ, naturality requires that for any vertical
morphism v : A →ᵥ B in the source category, the following diagram commutes:

```
                     τ_A
        F(A) ─────────────────────→ G(A)
         │                           │
         │     τ.natSquare(v)        │
  F.vMap v│                          │ G.vMap v
         │                           │
         ↓                           ↓
        F(B) ─────────────────────→ G(B)
         │         τ_B               │
         │     σ.natSquare(v)        │
  F.vMap v│                          │ G.vMap v
         │                           │
         ↓                           ↓
        F(B) ─────────────────────→ G(B)
                     σ_B
```

The law states: τ.natSquare(v) ⬝ᵥ Γ_B ≅ Γ_A ⬝ᵥ σ.natSquare(v)
(both paths give a square from F.vMap v to G.vMap v with left τ_A and
right σ_B)
-/
structure HorModLaws {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    {τ σ : HorTransOps F G}
    (Γ : HorModOps ops₂ τ σ) where
  /-- Naturality: τ.natSquare(v) ⬝ᵥ Γ_B ≅ Γ_A ⬝ᵥ σ.natSquare(v)

  The equality is heterogeneous because the two sides have different
  vertical boundaries that are only propositionally equal:
  - LHS has left vComp (F.vMap v) (vId F(B)), right vComp (G.vMap v) (vId G(B))
  - RHS has left vComp (vId F(A)) (F.vMap v), right vComp (vId G(A)) (G.vMap v)
  These are equal by identity laws but not definitionally.
  -/
  naturality : ∀ {A B : Obj₁} (v : vhs₁ A B),
    HEq (ops₂.sqVComp (τ.natSquare v) (Γ.app B))
        (ops₂.sqVComp (Γ.app A) (σ.natSquare v))

/-- Data for a modification between vertical transformations.

Bundles the component squares (ops) and the naturality condition (laws).
-/
structure VertModData {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (τ σ : VertTransOps F G) extends
    VertModOps ops₂ τ σ,
    VertModLaws ops₁ ops₂ toVertModOps

/-- Data for a modification between horizontal transformations.

Bundles the component squares (ops) and the naturality condition (laws).
-/
structure HorModData {Obj₁ : Type u₁}
    {vhs₁ : VertHomSet Obj₁} {hhs₁ : HorHomSet Obj₁} {sqs₁ : SquareSet vhs₁ hhs₁}
    (ops₁ : DoubleCategoryOps Obj₁ vhs₁ hhs₁ sqs₁)
    {Obj₂ : Type u₂}
    {vhs₂ : VertHomSet Obj₂} {hhs₂ : HorHomSet Obj₂} {sqs₂ : SquareSet vhs₂ hhs₂}
    (ops₂ : DoubleCategoryOps Obj₂ vhs₂ hhs₂ sqs₂)
    {F G : DoubleFunctorOps vhs₁ hhs₁ sqs₁ vhs₂ hhs₂ sqs₂}
    (τ σ : HorTransOps F G) extends
    HorModOps ops₂ τ σ,
    HorModLaws ops₁ ops₂ toHorModOps

end GebLean
