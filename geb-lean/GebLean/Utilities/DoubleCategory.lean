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

end GebLean
