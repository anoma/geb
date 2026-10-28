/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.InteractionNet.WiringGlue
public import Mathlib.Logic.Equiv.Fin.Basic
public import Init.Data.Vector.Lemmas
public import Init.Data.List.OfFn

set_option doc.verso true in
/-!
# Array storage for wire matchings

A vector stores one partner index per endpoint. Its invariant states that following
the partner twice returns to the original endpoint and no endpoint is its own partner.
A splice reads the two existing partners and updates four entries. The array operation
refines the abstract wire splice, including the case in which the cut closes a loop.
Allocation appends a disjoint matching with fresh endpoint indices.

## Main definitions

* {lit}`ArrayWiring` — a partner array with its matching invariant.
* {lit}`ArrayWiring.force` — local rewiring by four array writes.
* {lit}`ArrayWiring.append` — allocate a disjoint matching after the existing endpoints.
* {lit}`ArrayWiring.glue` — execute a finite sequence of local array splices.

## Main statements

* {lit}`ArrayWiring.read_force` — local array rewiring refines abstract splicing.
* {lit}`ArrayWiring.read_glue` — finite array execution refines abstract boundary gluing.

## Tags

interaction net, runtime, array, allocation, local rewiring, refinement
-/

set_option doc.verso true

@[expose] public section

namespace Geb.InteractionNet

/-- A finite partner array satisfying the wire-matching invariant. -/
structure ArrayWiring (size : ℕ) where
  /-- The partner index stored at each endpoint. -/
  links : Vector (Fin size) size
  /-- Following two links returns to the original endpoint. -/
  involutive : ∀ p : Fin size, links[links[p]] = p
  /-- No endpoint is paired with itself. -/
  fixedPointFree : ∀ p : Fin size, links[p] ≠ p

namespace ArrayWiring

variable {size other : ℕ}

/-- Read the abstract matching represented by a partner array. -/
def read (w : ArrayWiring size) : Wiring (Fin size) :=
  ⟨fun p ↦ w.links[p], w.involutive, w.fixedPointFree⟩

/-- A partner array realizes a matching when every indexed entry is its prescribed partner. -/
def realize (links : Vector (Fin size) size) (w : Wiring (Fin size))
    (h : ∀ p : Fin size, links[p] = w.partner p) : ArrayWiring size where
  links := links
  involutive p := by rw [h, h]; exact w.partner_partner p
  fixedPointFree p := by rw [h]; exact w.fixedPointFree p

/-- Reading an array realization returns its specified matching. -/
@[simp] theorem read_realize (links : Vector (Fin size) size) (w : Wiring (Fin size))
    (h : ∀ p : Fin size, links[p] = w.partner p) : (realize links w h).read = w := by
  apply Wiring.ext
  funext p
  exact h p

/-- Materialize an indexed matching as a contiguous partner array. -/
def encode (w : Wiring (Fin size)) : ArrayWiring size :=
  realize ⟨(List.ofFn w.partner).toArray, by simp only [List.size_toArray, List.length_ofFn]⟩ w
    (by
      intro p
      have hp : p.val < (List.ofFn w.partner).toArray.size := by
        simpa only [List.size_toArray, List.length_ofFn] using p.isLt
      change (List.ofFn w.partner).toArray[p.val]'hp = w.partner p
      rw [List.getElem_toArray]
      exact List.getElem_ofFn (by simpa only [List.length_ofFn] using p.isLt))

/-- Materialization preserves every partner entry. -/
@[simp] theorem read_encode (w : Wiring (Fin size)) : (encode w).read = w := read_realize _ _ _

/-- Isolate two endpoints and join their former partners using four array writes. -/
def forceLinks (w : ArrayWiring size) (a b : Fin size) : Vector (Fin size) size :=
  let pa := w.links[a]
  let pb := w.links[b]
  (((w.links.set a b).set b a).set pa pb).set pb pa

/-- The four writes have exactly the abstract splice's effect on each endpoint. -/
theorem forceLinks_get (w : ArrayWiring size) {a b : Fin size} (hab : a ≠ b) (p : Fin size) :
    (w.forceLinks a b)[p] = (w.read.force a b).partner p := by
  rw [Wiring.force_apply _ hab]
  have hfa := w.read.fixedPointFree a
  have hfb := w.read.fixedPointFree b
  simp only [forceLinks, Fin.getElem_fin, Vector.getElem_set, Fin.val_inj]
  change (if w.read.partner b = p then w.read.partner a else
    if w.read.partner a = p then w.read.partner b else
    if b = p then a else if a = p then b else w.read.partner p) = _
  have hpa : w.read.partner a = p ↔ w.read.partner p = a :=
    w.read.partner_eq_iff.trans eq_comm
  have hpb : w.read.partner b = p ↔ w.read.partner p = b :=
    w.read.partner_eq_iff.trans eq_comm
  simp only [hpa, hpb]
  clear hpa hpb
  by_cases hpa : p = a
  · subst p
    by_cases hw : w.read.partner a = b
    · simp only [hw, ↓reduceIte]
    · simp only [hw, hfa, hab.symm, ↓reduceIte]
  · by_cases hpb : p = b
    · subst p
      by_cases hw : w.read.partner b = a
      · simp only [hw, hpa, Ne.symm hpa, ↓reduceIte]
      · simp only [hw, hfb, hpa, ↓reduceIte]
    · simp only [hpa, hpb, Ne.symm hpa, Ne.symm hpb, ↓reduceIte]
      by_cases hw : w.read.partner p = a
      · simp only [hw, hab, ↓reduceIte]
      · simp only [hw, ↓reduceIte]

/-- Perform a local splice, retaining the array's matching invariant. -/
def force (w : ArrayWiring size) (a b : Fin size) (hab : a ≠ b) : ArrayWiring size :=
  realize (w.forceLinks a b) (w.read.force a b) (w.forceLinks_get hab)

/-- Local array rewiring refines the abstract splice. -/
@[simp] theorem read_force (w : ArrayWiring size) (a b : Fin size) (hab : a ≠ b) :
    (w.force a b hab).read = w.read.force a b := read_realize _ _ _

/-- Allocate a second matching at fresh indices after the existing endpoint array. -/
def append (w : ArrayWiring size) (v : ArrayWiring other) : ArrayWiring (size + other) :=
  encode ((w.read.sum v.read).map finSumFinEquiv)

/-- Allocation represents the disjoint union with the right component shifted to fresh indices. -/
@[simp] theorem read_append (w : ArrayWiring size) (v : ArrayWiring other) :
    (w.append v).read = (w.read.sum v.read).map finSumFinEquiv := read_encode _

/-- Perform one splice and add a closed wire exactly when its two endpoints were already joined. -/
def glueAt {I : Type*} (ports : I × Bool ↪ Fin size) (s : ArrayWiring size × ℕ) (i : I) :
    ArrayWiring size × ℕ :=
  (s.1.force (ports (i, false)) (ports (i, true)) (Wiring.pair_ne ports i),
    s.2 + if s.1.links[ports (i, false)] = ports (i, true) then 1 else 0)

/-- Execute the specified list of local array splices. -/
def glue {I : Type*} (ports : I × Bool ↪ Fin size) (order : List I)
    (s : ArrayWiring size × ℕ) : ArrayWiring size × ℕ := order.foldl (glueAt ports) s

/-- Reading finite array execution gives abstract gluing with the same closed-wire count. -/
theorem read_glue {I : Type*} (ports : I × Bool ↪ Fin size) (order : List I)
    (s : ArrayWiring size × ℕ) :
    ((glue ports order s).1.read, (glue ports order s).2) =
      Wiring.glue ports order (s.1.read, s.2) := by
  revert s
  refine List.rec (fun _ ↦ rfl) ?_ order
  intro i order ih s
  change ((glue ports order (glueAt ports s i)).1.read,
    (glue ports order (glueAt ports s i)).2) = _
  rw [ih]
  simp only [glueAt, read_force]
  rfl

end ArrayWiring

end Geb.InteractionNet

end
