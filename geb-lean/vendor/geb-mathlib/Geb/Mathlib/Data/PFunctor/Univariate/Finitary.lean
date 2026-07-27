/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Data.PFunctor.Univariate.Basic
public import Mathlib.Data.FinEnum

/-!
# Finitary polynomial functors

A polynomial functor is finitary when every shape has finitely many
directions.

## Main definitions

* `PFunctor.Finitary` — the condition `∀ a : P.A, FinEnum (P.B a)`,
  named as a reducible abbreviation so `[P.Finitary]` serves as its
  binder.

## Tags

polynomial functor, PFunctor, finitary, FinEnum
-/

public section

universe uA uB

/-- A polynomial functor is finitary when every shape has finitely many
directions. An `abbrev`, so that `[P.Finitary]` is the binder
`[∀ a, FinEnum (P.B a)]` under a name: being reducible it is transparent
to instance resolution, where a `class`'s fields would be inert until
registered. Declared on `PFunctor` so that one binder serves the slice
and presheaf layers through their `toPFunctor` projections. -/
abbrev PFunctor.Finitary (P : PFunctor.{uA, uB}) : Type (max uA uB) :=
  ∀ a : P.A, FinEnum (P.B a)
