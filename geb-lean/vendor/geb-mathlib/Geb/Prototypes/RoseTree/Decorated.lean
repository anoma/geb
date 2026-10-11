/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.RoseTree.Basic

set_option doc.verso true in
/-!
# Decorated rose trees

A decorated rose tree carries at each node a decoration beside its label: it is the rose tree
over pairs of a decoration and a label. Over a fixed type of labels, decorated trees form the
cofree recursive comonad on the rose functor \[UustaluVene2011\]: the counit
{lit}`extract` reads the decoration at the root, and redecoration {lit}`redecorate`
replaces each node's decoration by a function of the subtree below the node, the
comultiplication being redecoration by the identity. Every annotation of source is such a
decoration, comments and the empty lines between items among them, so one mechanism computes
each decoration from another.

The decorated tree is finite, the initial algebra of the functor of a decoration paired with a
rose node, not the terminal coalgebra that the cofree comonad is in general; the laws are
therefore stated and proved concretely, by induction over nodes.

## Main definitions

* {lit}`RoseTree.Decorated` — rose trees over pairs of a decoration and a label.
* {lit}`RoseTree.extract` — the decoration at the root, the counit.
* {lit}`RoseTree.redecorate` — each node's decoration replaced by a function of its subtree.
* {lit}`RoseTree.erase` — the labels alone, every decoration forgotten.

## Main statements

* {lit}`RoseTree.extract_redecorate`, {lit}`RoseTree.redecorate_extract`,
  {lit}`RoseTree.redecorate_redecorate` — the laws of the comonad, in the form of its
  extension.
* {lit}`RoseTree.erase_redecorate` — redecoration leaves the labels unchanged.

## References

* \[UustaluVene2011\] — the cofree recursive comonad and its recursion scheme.

## Tags

rose tree, comonad, decoration, annotation
-/

set_option doc.verso true

@[expose] public section

namespace Geb.RoseTree

variable {A B C K : Type}

/-- A rose tree whose nodes carry a decoration of type {lit}`A` beside a label of type
{lit}`K`. -/
abbrev Decorated (A K : Type) : Type := RoseTree (A × K)

/-- The decoration at the root: the counit of the comonad. -/
def extract (t : Decorated A K) : A := t.label.1

/-- Each node's decoration replaced by a function of the subtree below the node: the extension
of the comonad. -/
def redecorate (f : Decorated A K → B) : Decorated A K → Decorated B K :=
  para fun l rs ↦ node (f (node l (rs.map Prod.fst)), l.2) (rs.map Prod.snd)

/-- The labels of a decorated tree, every decoration forgotten. -/
def erase : Decorated A K → RoseTree K := map Prod.snd

/-- The computation rule of redecoration. -/
@[simp] theorem redecorate_node (f : Decorated A K → B) (l : A × K) (cs : List (Decorated A K)) :
    redecorate f (node l cs) = node (f (node l cs), l.2) (cs.map (redecorate f)) := by
  simp [redecorate, List.map_map, Function.comp_def]

/-- The decoration at the root of a redecorated tree is the function at the tree. -/
@[simp] theorem extract_redecorate (f : Decorated A K → B) (t : Decorated A K) :
    extract (redecorate f t) = f t := by
  rw [← node_label_children t, redecorate_node]
  rfl

/-- Redecorating by the decoration at each node changes nothing. -/
@[simp] theorem redecorate_extract (t : Decorated A K) : redecorate extract t = t :=
  ind (P := fun t ↦ redecorate extract t = t) (fun l cs ih ↦ by
    beta_reduce
    rw [redecorate_node]
    exact congrArg₂ node (by simp [extract]) ((List.map_congr_left ih).trans cs.map_id)) t

/-- Redecorating twice is redecorating once by the second function after the first's
redecoration. -/
theorem redecorate_redecorate (f : Decorated A K → B) (g : Decorated B K → C)
    (t : Decorated A K) :
    redecorate g (redecorate f t) = redecorate (fun u ↦ g (redecorate f u)) t :=
  ind (P := fun t ↦ redecorate g (redecorate f t) = redecorate (fun u ↦ g (redecorate f u)) t)
    (fun l cs ih ↦ by
      simp only [redecorate_node, List.map_map]
      exact congrArg₂ node (by simp) (List.map_congr_left ih)) t

/-- Redecoration leaves the labels unchanged. -/
@[simp] theorem erase_redecorate (f : Decorated A K → B) (t : Decorated A K) :
    erase (redecorate f t) = erase t :=
  ind (P := fun t ↦ erase (redecorate f t) = erase t) (fun l cs ih ↦ by
    simp only [redecorate_node, erase, map_node, List.map_map]
    exact congrArg _ (List.map_congr_left ih)) t

end Geb.RoseTree

end
