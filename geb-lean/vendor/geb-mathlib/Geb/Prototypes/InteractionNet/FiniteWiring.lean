/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.InteractionNet.ArrayWiring
public import Geb.Prototypes.InteractionNet.WiringGlue
public import Mathlib.Data.FinEnum

set_option doc.verso true in
/-!
# Materialized finite graph assembly

Graph assembly can contain many wire splices. Executing those splices on a partner array
avoids retaining a chain of functional matchings. Reading the resulting array agrees
exactly with abstract gluing, including the count of closed wires.

## Main definitions

* {lit}`Wiring.glueFinite` — execute finite gluing through a materialized partner array.
* {lit}`Wiring.gluedFinite` — remove the glued endpoints after array execution.

## Main statements

* {lit}`Wiring.glueFinite_eq` — array assembly equals abstract gluing.
* {lit}`Wiring.gluedFinite_eq` — the surviving matching and closed-wire count are unchanged.

## Tags

interaction net, graph, assembly, array, gluing, refinement
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet.Wiring

open scoped FinEnum

variable {P I : Type*} [FinEnum P]

/-- Execute wire splices on a finite partner array, then restore the original endpoint names. -/
def glueFinite (ports : I × Bool ↪ P) (order : List I) (s : Wiring P × ℕ) : Wiring P × ℕ :=
  let g := ArrayWiring.glue (ports.trans FinEnum.equiv.toEmbedding) order
    (ArrayWiring.encode (s.1.map FinEnum.equiv), s.2)
  (g.1.read.map FinEnum.equiv.symm, g.2)

variable [DecidableEq P]

/-- Materializing each splice preserves the matching and closed-wire count of abstract gluing. -/
theorem glueFinite_eq (ports : I × Bool ↪ P) (order : List I) (s : Wiring P × ℕ) :
    glueFinite ports order s = glue ports order s := by
  have h := ArrayWiring.read_glue (ports.trans FinEnum.equiv.toEmbedding) order
    (ArrayWiring.encode (s.1.map FinEnum.equiv), s.2)
  rw [ArrayWiring.read_encode, glue_map] at h
  have he := congrArg (fun t : Wiring (Fin (FinEnum.card P)) × ℕ ↦
    (t.1.map FinEnum.equiv.symm, t.2)) h
  simpa only [glueFinite, map_symm_map] using he

/-- Execute finite gluing and remove all its detached endpoints. -/
@[nolint unusedArguments]
def gluedFinite (ports : I × Bool ↪ P) (order : List I) (_unique : order.Nodup)
    (cover : ∀ i, i ∈ order) (s : Wiring P × ℕ) :
    Wiring {p // ∀ i b, p ≠ ports (i, b)} × ℕ :=
  let g := glueFinite ports order s
  (g.1.restrict _ (by
    dsimp only [g]
    rw [glueFinite_eq]
    exact glue_closed ports order cover s), g.2)

/-- Array assembly has the same surviving wires and loops as abstract assembly. -/
theorem gluedFinite_eq (ports : I × Bool ↪ P) (order : List I) (unique : order.Nodup)
    (cover : ∀ i, i ∈ order) (s : Wiring P × ℕ) :
    gluedFinite ports order unique cover s = glued ports order unique cover s := by
  simp only [gluedFinite, glueFinite_eq, glued]

end Geb.InteractionNet.Wiring

end
