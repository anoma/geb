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

universe u vMor hMor sq

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

universe u₁ vMor₁ hMor₁ sq₁ u₂ vMor₂ hMor₂ sq₂

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

end GebLean
