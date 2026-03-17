import Mathlib.CategoryTheory.Subfunctor.Basic
import Mathlib.CategoryTheory.Subfunctor.Image
import Mathlib.CategoryTheory.Subfunctor.Sieves

/-!
# Witnessed subfunctors

A `WSubfunctor F` is a constructive analogue of
mathlib's `Subfunctor F`. Where `Subfunctor`
stores membership propositionally
(`obj : ∀ U, Set (F.obj U)`, i.e., `α → Prop`),
a `WSubfunctor` stores a total presheaf and an
inclusion morphism, so the fiber over each
element `x : F.obj U` is the constructive type
`{a : W.total.obj U // W.incl.app U a = x}`.

When the inclusion is mono (pointwise injective),
each fiber is a `Subsingleton`, and witnesses
can be extracted constructively (no
`Classical.choice` needed). This enables
constructive inversions that are not possible
with propositional `Subfunctor`.

## API correspondence with `Subfunctor`

The API mirrors `Subfunctor` so that migration
is a mechanical name change:

| `Subfunctor`        | `WSubfunctor`          |
|---------------------|------------------------|
| `toFunctor`         | `total` (field)        |
| `ι`                 | `incl` (field)         |
| `range p`           | `range p`              |
| `ext`               | `ext`                  |

## Connection to `Subfunctor`

`WSubfunctor.toSubfunctor` forgets the total
presheaf and retains only propositional
membership (via `Set.range`).
-/

open CategoryTheory

namespace GebLean

universe v u w

variable {C : Type u} [Category.{v} C]

/-- A witnessed subfunctor of `F : C ⥤ Type w`.
Consists of a total presheaf and an inclusion
morphism into `F`. The fiber over
`x : F.obj U` is the constructive type
`{a : W.total.obj U // W.incl.app U a = x}`.
-/
structure WSubfunctor
    (F : C ⥤ Type w) where
  /-- The total presheaf carrying witness
  data. -/
  total : C ⥤ Type w
  /-- The inclusion morphism from the total
  presheaf into `F`. -/
  incl : total ⟶ F

variable {F F' F'' : C ⥤ Type w}

namespace WSubfunctor

/-- The fiber of a witnessed subfunctor over
`x : F.obj U`: the type of witnesses that
`x` belongs to the subfunctor. -/
abbrev fiber (W : WSubfunctor F) (U : C)
    (x : F.obj U) : Type w :=
  { a : W.total.obj U // W.incl.app U a = x }

/-- The range of a morphism `p : F' ⟶ F`,
as a witnessed subfunctor. The total presheaf
is `F'` itself, and the inclusion is `p`.
The fiber over `x` is
`{a : F'.obj U // p.app U a = x}`. -/
def range (p : F' ⟶ F) : WSubfunctor F where
  total := F'
  incl := p

@[simp]
theorem range_total (p : F' ⟶ F) :
    (range p).total = F' := rfl

@[simp]
theorem range_incl (p : F' ⟶ F) :
    (range p).incl = p := rfl

/-- Forget witness data: extract the
propositional `Subfunctor` by taking
`Set.range` of the inclusion at each stage. -/
def toSubfunctor (W : WSubfunctor F) :
    Subfunctor F :=
  Subfunctor.range W.incl

/-- Factor a morphism through the witnessed
subfunctor: given `p : F'' ⟶ F` that factors
through `W.incl` via `q : F'' ⟶ W.total`,
produce a morphism into `W.total`. -/
def lift (W : WSubfunctor F)
    (p : F'' ⟶ F)
    (q : F'' ⟶ W.total)
    (_ : q ≫ W.incl = p) :
    F'' ⟶ W.total := q

/-- The inclusion composed with a
factorization recovers the original
morphism. -/
@[simp]
theorem lift_incl (W : WSubfunctor F)
    (p : F'' ⟶ F)
    (q : F'' ⟶ W.total)
    (hq : q ≫ W.incl = p) :
    W.lift p q hq ≫ W.incl = p := hq

/-- Extensionality: two witnessed subfunctors
with the same total presheaf and inclusion are
equal. -/
@[ext (iff := false)]
theorem ext {W₁ W₂ : WSubfunctor F}
    (htotal : W₁.total = W₂.total)
    (hincl : W₁.incl =
      eqToHom (by rw [htotal]) ≫ W₂.incl) :
    W₁ = W₂ := by
  cases W₁; cases W₂
  dsimp at htotal hincl
  subst htotal
  simp only [eqToHom_refl, Category.id_comp]
    at hincl
  exact congrArg (WSubfunctor.mk _) hincl

/-- Lift propositional membership to
constructive witnesses via `PLift`. Each
`PLift` fiber is a `Subsingleton` (by proof
irrelevance). -/
def ofSubfunctor (S : Subfunctor F) :
    WSubfunctor F where
  total := S.toFunctor
  incl := S.ι

@[simp]
theorem ofSubfunctor_total (S : Subfunctor F) :
    (ofSubfunctor S).total = S.toFunctor := rfl

@[simp]
theorem ofSubfunctor_incl (S : Subfunctor F) :
    (ofSubfunctor S).incl = S.ι := rfl

/-- The fiber of a `range` witnessed
subfunctor: the preimage type. -/
theorem range_fiber_eq (p : F' ⟶ F) (U : C)
    (x : F.obj U) :
    (range p).fiber U x =
      { a : F'.obj U // p.app U a = x } :=
  rfl

/-- Factor a morphism through the range:
given `p : F' ⟶ F`, produce a morphism
`F' ⟶ (range p).total` (the identity, since
`(range p).total = F'`). -/
def toRange (p : F' ⟶ F) :
    F' ⟶ (range p).total := 𝟙 F'

@[simp]
theorem toRange_incl (p : F' ⟶ F) :
    toRange p ≫ (range p).incl = p := by
  simp [toRange, range]

end WSubfunctor

section WSubfunctorSieves

/-! ### Sieves from witnessed subfunctors

When `F : Cᵒᵖ ⥤ Type w` is a presheaf, a
`WSubfunctor F` determines a sieve at each
section, using `Nonempty` of the fiber to
define membership. This agrees with
`Subfunctor.sieveOfSection` applied to
`W.toSubfunctor`.
-/

variable {C : Type u} [Category.{v} C]
variable {F : Cᵒᵖ ⥤ Type w}

open Opposite

namespace WSubfunctor

/-- The sieve of a witnessed subfunctor at a
section `s : F.obj U`: the sieve on `U.unop`
consisting of morphisms `f : V ⟶ U.unop`
such that `F.map f.op s` has a witness. -/
def sieveOfSection (W : WSubfunctor F)
    {U : Cᵒᵖ} (s : F.obj U) :
    Sieve U.unop where
  arrows V f :=
    Nonempty (W.fiber (op V)
      (F.map f.op s))
  downward_closed := by
    intro V₁ V₂ f₁ ⟨⟨a, ha⟩⟩ f₂
    refine ⟨⟨W.total.map f₂.op a, ?_⟩⟩
    have nat := congr_fun
      (W.incl.naturality f₂.op) a
    simp only [types_comp_apply] at nat
    rw [nat, ha]
    exact (congr_fun
      (F.map_comp f₁.op f₂.op) s).symm

/-- The `WSubfunctor` sieve agrees with the
`Subfunctor` sieve via `toSubfunctor`. -/
theorem sieveOfSection_eq_toSubfunctor
    (W : WSubfunctor F)
    {U : Cᵒᵖ} (s : F.obj U) :
    W.sieveOfSection s =
      W.toSubfunctor.sieveOfSection s := by
  ext V f
  dsimp [sieveOfSection,
    Subfunctor.sieveOfSection,
    toSubfunctor, Subfunctor.range]
  exact ⟨fun ⟨⟨a, ha⟩⟩ => ⟨a, ha⟩,
    fun ⟨a, ha⟩ => ⟨⟨a, ha⟩⟩⟩

end WSubfunctor

end WSubfunctorSieves

end GebLean
