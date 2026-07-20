/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.IndRec.Basic

/-!
# Simple containers as IR codes over the unit type

A simple container — a shape type `S` and a direction family
`P : S → Type` — is mathlib's `PFunctor`. Example 1 of
[HancockMcBrideGhaniMalatestaAltenkirch2013] represents such a
container by an `IR` code over the unit type (the paper's `IR 1 1`):
a `sigma` over the shapes, then for each shape a `delta` over its
directions, terminating in the constant `iota` code at the unit. The
initial algebra of the code's interpretation amounts to Martin-Löf's
well-ordering type (the paper's `W S P`; mathlib's `WType`); the
initial algebra itself is not constructed here.

## Main definitions

* `contCode` — the `IR` code over the unit type representing a
  simple container (a `PFunctor`), following Example 1 of
  [HancockMcBrideGhaniMalatestaAltenkirch2013].

## References

* [HancockMcBrideGhaniMalatestaAltenkirch2013]

## Tags

inductive-recursive, container, polynomial functor
-/

@[expose] public section

universe uA uB uI uO

namespace IndRec

/-- The `IR` code over the unit type representing the container `F`:
a `sigma` over the shapes `F.A`, then for each shape a `delta` over
its directions `F.B`, terminating in `iota` at the unit element.
Follows Example 1 of
[HancockMcBrideGhaniMalatestaAltenkirch2013]. -/
def contCode (F : PFunctor.{uA, uB}) : IR.{uA, uB, uI, uO} PUnit PUnit :=
  IR.sigma PUnit PUnit F.A
    (fun s ↦ IR.delta PUnit PUnit (F.B s)
      (fun _ ↦ IR.iota PUnit PUnit PUnit.unit))

end IndRec
