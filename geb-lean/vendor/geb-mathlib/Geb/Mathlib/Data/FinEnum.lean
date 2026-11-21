/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.FinEnum
public import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Choice-free `FinEnum` instances and decidability

mathlib decides a bounded `∀` through `Fintype`, whose instance depends
on `Classical.choice`. `FinEnum` carries a `List` enumeration, and
deciding a quantifier by `List.decidableBAll` over `FinEnum.toList` is
choice-free. The three `Decidable` instances below take that route.

The `Decidable` argument of each `decidable_of_iff` is supplied
explicitly. Left to inference, resolution reaches
`Fintype.decidableForallFintype` through mathlib's
`[FinEnum α] : Fintype α` bridge and the instance, while still
typechecking, acquires `Classical.choice`.

`decidableForallSubtype` decides a quantifier over a decidable subtype
without forming a `FinEnum` on the subtype: mathlib's
`FinEnum.Subtype.finEnum` is derived through `FinEnum.ofList` and is
choice-dependent.

mathlib's `FinEnum.punit` and `FinEnum.sum` are likewise derived through
`FinEnum.ofList` and are choice-dependent. The three `scoped instance`s
below are choice-free replacements, resolved in preference to mathlib's
under `open scoped FinEnum`.

## Main definitions

* `FinEnum.decidableForallFinEnum` — a bounded `∀` over the type.
* `FinEnum.decidableForallSubtype` — a bounded `∀` over a decidable
  subtype of it.
* `FinEnum.decidablePiFinEnum` — equality of functions out of it.
* `FinEnum.unit` — a choice-free `FinEnum Unit`.
* `FinEnum.finFin` — a choice-free `FinEnum (Fin n)`.
* `FinEnum.finSum` — a choice-free `FinEnum` on a sum of finitely
  enumerable types.

## Tags

FinEnum, decidability, constructive, sum type
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
    ⟨fun H x ↦ H x.val (FinEnum.mem_toList x.val) x.property, fun H x _ h ↦ H ⟨x, h⟩⟩
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

/-- A choice-free `FinEnum Unit`. `scoped`, so that it does not compete
with mathlib's `FinEnum.punit`, which is derived through `FinEnum.ofList`
and depends on `Classical.choice`. -/
@[instance_reducible]
scoped instance unit : FinEnum Unit where
  card := 1
  equiv := finOneEquiv.symm
  decEq := inferInstance

/-- A choice-free `FinEnum (Fin n)`: the cardinality is `n` and the
enumeration is the identity. `scoped`, for the same reason as `unit`. -/
@[instance_reducible]
scoped instance finFin (n : ℕ) : FinEnum (Fin n) where
  card := n
  equiv := Equiv.refl _
  decEq := inferInstance

/-- A choice-free `FinEnum` on a sum. `scoped`, for the same reason as
`unit`; mathlib's `FinEnum.sum` takes the `ofList` route. -/
@[instance_reducible]
scoped instance finSum {α : Type u} {β : Type v} [FinEnum α] [FinEnum β] :
    FinEnum (α ⊕ β) where
  card := FinEnum.card α + FinEnum.card β
  equiv := (Equiv.sumCongr (FinEnum.equiv) (FinEnum.equiv)).trans finSumFinEquiv
  decEq := inferInstance

end FinEnum
