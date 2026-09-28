/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.UniqueChoice
public import Mathlib.Logic.Function.Basic

set_option doc.verso true in
/-!
# Unique choice from choice

Lean proves the principle of unique choice ({name}`Geb.FreeTopos.UniqueChoice`) from
{lit}`Classical.choice`, through mathlib's {name}`forall_existsUnique_iff`. This module is the
correspondence between the principle and Lean's choice, and it is admitted to the axiom linter's
allowlist ({lit}`GebMeta.classicalAllowedModules`) for that alone.

## Main statements

* {lit}`uniqueChoice` — unique choice holds in Lean with {lit}`Classical.choice`.

## Tags

unique choice, axiom of choice, functional relation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

universe u v

/-- Unique choice holds in Lean with {lit}`Classical.choice`. -/
theorem uniqueChoice : UniqueChoice.{u, v} := fun _ _ _ h ↦
  let ⟨f, hf⟩ := forall_existsUnique_iff.mp h
  ⟨f, fun _ ↦ hf.mpr rfl⟩

end Geb.FreeTopos

end
