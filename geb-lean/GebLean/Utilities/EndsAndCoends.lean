import Mathlib.CategoryTheory.Limits.Shapes.End
import Mathlib.CategoryTheory.Types.Basic

/-!
# Explicit Ends and Coends in Type

Mathlib's `end_`, `coend`, `endFunctor`, `coendFunctor` are not
computable.  This module provides computable versions for
`Type v` by giving explicit constructions as subtypes (ends) and
quotients (coends).

## Main definitions

* `typeEnd F` -- The end of `F : Jᵒᵖ ⥤ J ⥤ Type v`, given as the
  subtype of compatible families satisfying the wedge condition.
* `typeCoend F` -- The coend of `F : Jᵒᵖ ⥤ J ⥤ Type v`, given as
  a quotient of the sigma type by the cowedge relation.
* `typeEndFunctor` -- Computable end functor `(Jᵒᵖ ⥤ J ⥤ Type v) ⥤ Type v`.
* `typeCoendFunctor` -- Computable coend functor.
-/

namespace GebLean

open CategoryTheory
open CategoryTheory.Limits

universe v u

variable {J : Type u} [Category.{v} J]

/-- The end of a profunctor `F : Jᵒᵖ ⥤ J ⥤ Type v` in `Type v`,
constructed as the subtype of families `(j : J) → (F.obj (op j)).obj j`
satisfying the wedge condition: for every morphism `f : i ⟶ j`,
`(F.obj (op i)).map f (x i) = (F.map f.op).app j (x j)`. -/
def typeEnd (F : Jᵒᵖ ⥤ J ⥤ Type v) : Type (max u v) :=
  { x : (j : J) → (F.obj (Opposite.op j)).obj j //
    ∀ {i j : J} (f : i ⟶ j),
      (F.obj (Opposite.op i)).map f (x i) =
        (F.map f.op).app j (x j) }

/-- Projection from `typeEnd F` to the component at `j`. -/
def typeEnd.proj (F : Jᵒᵖ ⥤ J ⥤ Type v) (j : J) :
    typeEnd F → (F.obj (Opposite.op j)).obj j :=
  fun x => x.val j

section TypeEndWedge

variable {J : Type v} [Category.{v} J]

/-- The wedge with apex `typeEnd F` in `Type v`.
The projections are `typeEnd.proj` and the wedge condition
follows from the subtype predicate of `typeEnd`. -/
def typeEndWedge (F : Jᵒᵖ ⥤ J ⥤ Type v) : Wedge F :=
  Wedge.mk (typeEnd F) (fun j => typeEnd.proj F j)
    (fun {i j} f => by
      ext x
      exact x.property f)

/-- `typeEndWedge F` is a limit wedge (i.e., the end
of `F` in `Type v`).  Given any other wedge `s`, the
unique morphism `s.pt → typeEnd F` packages the wedge
projections into a compatible family. -/
def typeEndWedge_isLimit (F : Jᵒᵖ ⥤ J ⥤ Type v) :
    IsLimit (typeEndWedge F) :=
  Multifork.IsLimit.mk (typeEndWedge F)
    (fun s => fun x => ⟨fun j => s.ι j x,
      fun {_ _} f =>
        congr_fun (Wedge.condition s f) x⟩)
    (fun _ _ => rfl)
    (fun _ _ hm => funext (fun x =>
      Subtype.ext (funext (fun j =>
        congr_fun (hm j) x))))

/-- `typeEndWedge F` is a terminal wedge. -/
def typeEndWedge_isTerminal (F : Jᵒᵖ ⥤ J ⥤ Type v) :
    IsTerminal (typeEndWedge F) :=
  (Cone.isLimitEquivIsTerminal _)
    (typeEndWedge_isLimit F)

end TypeEndWedge

/-!
## Coends in Type
-/

section TypeCoend

variable {J : Type u} [Category.{v} J]

/-- The cowedge relation on `Σ (j : J), (F.obj (op j)).obj j`.
For a morphism `f : i ⟶ j` and element
`x : (F.obj (op j)).obj i`, identifies
`⟨i, (F.map f.op).app i x⟩` with
`⟨j, (F.obj (op j)).map f x⟩`. -/
inductive typeCoendRel (F : Jᵒᵖ ⥤ J ⥤ Type v) :
    (Σ (j : J), (F.obj (Opposite.op j)).obj j) →
    (Σ (j : J), (F.obj (Opposite.op j)).obj j) → Prop
  | intro {i j : J} (f : i ⟶ j)
      (x : (F.obj (Opposite.op j)).obj i) :
      typeCoendRel F
        ⟨i, (F.map f.op).app i x⟩
        ⟨j, (F.obj (Opposite.op j)).map f x⟩

/-- The coend of a profunctor `F : Jᵒᵖ ⥤ J ⥤ Type v` in `Type`,
constructed as a quotient of `Σ (j : J), (F.obj (op j)).obj j`
by the cowedge relation `typeCoendRel`. -/
def typeCoend (F : Jᵒᵖ ⥤ J ⥤ Type v) :
    Type (max u v) :=
  Quot (typeCoendRel F)

/-- Injection from the `j`-th component into `typeCoend F`. -/
def typeCoend.inj (F : Jᵒᵖ ⥤ J ⥤ Type v) (j : J) :
    (F.obj (Opposite.op j)).obj j → typeCoend F :=
  fun x => Quot.mk _ ⟨j, x⟩

end TypeCoend

section TypeCoendCowedge

variable {J : Type v} [Category.{v} J]

/-- The cowedge with apex `typeCoend F` in `Type v`.
The injections are `typeCoend.inj` and the cowedge condition
follows from `Quot.sound` applied to `typeCoendRel`. -/
def typeCoendCowedge (F : Jᵒᵖ ⥤ J ⥤ Type v) :
    Cowedge F :=
  Cowedge.mk (typeCoend F) (fun j => typeCoend.inj F j)
    (fun {i j} f => by
      ext x
      exact Quot.sound (typeCoendRel.intro f x))

/-- `typeCoendCowedge F` is a colimit cowedge (i.e., the
coend of `F` in `Type v`). -/
def typeCoendCowedge_isColimit
    (F : Jᵒᵖ ⥤ J ⥤ Type v) :
    IsColimit (typeCoendCowedge F) :=
  Multicofork.IsColimit.mk (typeCoendCowedge F)
    (fun s => Quot.lift (fun ⟨j, x⟩ => s.π j x)
      (fun _ _ r => by
        cases r with
        | intro f x =>
          exact congr_fun
            (Cowedge.condition s f) x))
    (fun _ _ => rfl)
    (fun _ m hm => by
      ext ⟨j, x⟩
      exact congr_fun (hm j) x)

/-- `typeCoendCowedge F` is an initial cowedge. -/
def typeCoendCowedge_isInitial
    (F : Jᵒᵖ ⥤ J ⥤ Type v) :
    IsInitial (typeCoendCowedge F) :=
  (Cocone.isColimitEquivIsInitial _)
    (typeCoendCowedge_isColimit F)

end TypeCoendCowedge

end GebLean
