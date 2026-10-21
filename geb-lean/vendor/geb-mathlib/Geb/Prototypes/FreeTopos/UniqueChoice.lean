/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Mathlib.Logic.ExistsUnique

set_option doc.verso true in
/-!
# Unique choice

The principle of unique choice: a relation that relates each element of its domain to exactly
one element of its codomain is the graph of a function. It is the axiom of unique choice
{lit}`AC!` of \[ContenteMaietti2024\], section 3.2, which identifies functional relations
with functions.

Every topos validates it in its internal logic, where the arrow a functional relation determines
is part of the structure; every model of the theory of this repository's free topos does
({lit}`Geb.FreeTopos.unique_choice`, after \[DubucSzyld2015\], Proposition 1.21). Lean's
logic without {lit}`Classical.choice` does not provide it: a unique existence is a proposition,
and a proposition does not eliminate into a type to give the function. Stated here as a
proposition, it is a hypothesis of the theorems that need it, which hold without
{lit}`Classical.choice` under it; {lit}`Geb.FreeTopos.uniqueChoice` proves it from
{lit}`Classical.choice`, in a module of its own.

## Main definitions

* {lit}`UniqueChoice` — the principle of unique choice.

## References

* \[ContenteMaietti2024\], section 3.2, for the axiom of unique choice.
* \[DubucSzyld2015\], Proposition 1.21, for the functional relations of a topos.

## Tags

unique choice, functional relation, description, topos
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

universe u v

/-- The principle of unique choice: each relation that relates every element of its domain to
exactly one element of its codomain holds between each element and the value of a function
(\[ContenteMaietti2024\], section 3.2). -/
def UniqueChoice : Prop :=
  ∀ (α : Sort u) (β : Sort v) (r : α → β → Prop), (∀ a, ∃! b, r a b) → ∃ f : α → β, ∀ a, r a (f a)

end Geb.FreeTopos

end
