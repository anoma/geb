/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.FinEnum

/-!
# Choice-free decidability over a `FinEnum`

mathlib decides a bounded `∀` through `Fintype`, whose instance depends
on `Classical.choice`. `FinEnum` carries a `List` enumeration, and
deciding a quantifier by `List.decidableBAll` over `FinEnum.toList` is
choice-free. These three instances take that route.

The `Decidable` argument of each `decidable_of_iff` is supplied
explicitly. Left to inference, resolution reaches
`Fintype.decidableForallFintype` through mathlib's
`[FinEnum α] : Fintype α` bridge and the instance, while still
typechecking, acquires `Classical.choice`.

`decidableForallSubtype` decides a quantifier over a decidable subtype
without forming a `FinEnum` on the subtype: mathlib's
`FinEnum.Subtype.finEnum` is derived through `FinEnum.ofList` and is
choice-dependent.

## Main definitions

* `FinEnum.decidableForallFinEnum` — a bounded `∀` over the type.
* `FinEnum.decidableForallSubtype` — a bounded `∀` over a decidable
  subtype of it.
* `FinEnum.decidablePiFinEnum` — equality of functions out of it.

## Tags

FinEnum, decidability, constructive
-/

public section

universe u v

namespace FinEnum

/-- A universally quantified statement over a finitely enumerable type is
decidable. The analogue of `Fintype.decidableForallFintype`, routed
through `List.decidableBAll` so as not to depend on `Classical.choice`. -/
@[instance_reducible]
instance decidableForallFinEnum {α : Type u} {p : α → Prop} [DecidablePred p]
    [FinEnum α] : Decidable (∀ x, p x) :=
  @decidable_of_iff (∀ x, p x) (∀ x ∈ FinEnum.toList α, p x)
    ⟨fun h x ↦ h x (FinEnum.mem_toList x), fun h x _ ↦ h x⟩
    (List.decidableBAll p (FinEnum.toList α))

/-- A universally quantified statement over a decidable subtype of a
finitely enumerable type is decidable. Ranges over the ambient type's
enumeration and discharges the subtype's predicate inside the body, so no
`FinEnum` on the subtype is formed. -/
@[instance_reducible]
instance decidableForallSubtype {α : Type u} {p : α → Prop} [DecidablePred p]
    {q : Subtype p → Prop} [DecidablePred q] [FinEnum α] :
    Decidable (∀ x : Subtype p, q x) :=
  @decidable_of_iff (∀ x : Subtype p, q x) (∀ a ∈ FinEnum.toList α, ∀ h : p a, q ⟨a, h⟩)
    ⟨fun H x ↦ H x.1 (FinEnum.mem_toList x.1) x.2, fun H x _ h ↦ H ⟨x, h⟩⟩
    (List.decidableBAll _ (FinEnum.toList α))

/-- Equality of functions out of a finitely enumerable type is decidable.
The analogue of `Fintype.decidablePiFintype`, and weaker in its
hypothesis on the codomain: `List.Pi.finEnum` would require the codomain
finitely enumerable, where this needs only decidable equality. -/
@[instance_reducible]
instance decidablePiFinEnum {α : Type u} {Y : Type v} [DecidableEq Y] [FinEnum α] :
    DecidableEq (α → Y) :=
  fun f g ↦ @decidable_of_iff (f = g) (∀ x, f x = g x) funext_iff.symm
    (decidableForallFinEnum)

end FinEnum
