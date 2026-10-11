/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Kernel.Identity

set_option doc.verso true

/-!
# Annotations of identifiers

Annotations of a bundle's definitions are kept apart from their payloads, in a table keyed by a
definition and a vertex of its term, the path of child positions from the root. A definition is
first its position in the bundle; the migration to identifiers ({lit}`Geb.Kernel.Identity.migrate`)
relabels the leaves of references and moves no vertex ({lit}`migrate_shape`), so a key re-keyed
to the identifier of the definition's payload and the same vertex
({lit}`rekey`) addresses the same node of the payload's body ({lit}`valid_rekey`). Names are
such annotations: the name a definition is declared under, at the root of its term, and the
name written at each reference, at the reference's vertex ({lit}`nameNotes`). The table is a
relation: definitions with equal payloads share an identifier and keep each its own notes.

## Main definitions

* {lit}`subtree?` — the subtree at a vertex.
* {lit}`refVertices` — the vertices of a term's references to definitions.
* {lit}`Note`, {lit}`nameNotes` — names as annotations.
* {lit}`rekey` — a table keyed by positions re-keyed by identifiers.

## Main statements

* {lit}`migrate_shape` — the migration moves no vertex.
* {lit}`valid_rekey` — re-keyed keys address nodes of the payloads they name.

## Tags

annotation, content identity, vertex, re-keying
-/

@[expose] public section

namespace Geb.Kernel.Identity

/-! ## Vertices -/

/-- The subtree of a tree at a vertex, the path of child positions from the root. -/
def subtree? {α : Type} (t : RoseTree α) (v : List ℕ) : Option (RoseTree α) :=
  v.foldl (fun o i ↦ o.bind fun s ↦ s.children[i]?) (some t)

/-- The shape of a term: its nodes without their labels. -/
def shape (t : Tree) : RoseTree Unit := t.map fun _ ↦ ()

/-- The shape of a node. -/
theorem shape_node (l : ℕ) (cs : List Tree) :
    shape (RoseTree.node l cs) = RoseTree.node () (cs.map shape) := RoseTree.map_node _ _ _

/-- A term's shape is the node over its children's shapes. -/
theorem shape_eq : ∀ t : Tree, shape t = RoseTree.node () (t.children.map shape) :=
  RoseTree.ind fun l cs _ ↦ by rw [shape_node, RoseTree.children_node]

/-- Relabelling references keeps a term's shape. -/
theorem shape_mapRefs (f : ℕ → ℕ) : ∀ t : Tree, shape (mapRefs f t) = shape t :=
  RoseTree.ind fun l cs ih ↦ by
    rw [mapRefs_node]
    split_ifs
    · rw [shape_node, shape_node, List.map_map]
      exact congrArg _ (List.map_congr_left fun c _ ↦ by
        rw [Function.comp_apply, shape_node, shape_eq c])
    · cases cs with
      | nil => rfl
      | cons c rest =>
        change shape (RoseTree.node l (c :: rest.map (mapRefs f))) = _
        rw [shape_node, shape_node, List.map_cons, List.map_cons, List.map_map]
        exact congrArg (fun xs ↦ RoseTree.node () (shape c :: xs))
          (List.map_congr_left fun x hx ↦ ih x (List.mem_cons_of_mem c hx))
    · rw [shape_node, shape_node, List.map_map]
      exact congrArg _ (List.map_congr_left fun x hx ↦ ih x hx)
    · rfl

/-- Following a path commutes with mapping the labels, from any start. -/
theorem foldl_subtree_map {α β : Type} (g : α → β) (v : List ℕ) :
    ∀ o : Option (RoseTree α),
      (v.foldl (fun o i ↦ o.bind fun s ↦ s.children[i]?) o).map (RoseTree.map g) =
        v.foldl (fun o i ↦ o.bind fun s ↦ s.children[i]?) (o.map (RoseTree.map g)) :=
  List.rec (fun _ ↦ rfl) (fun i v ih o ↦ by
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    cases o with
    | none => rfl
    | some s => simp [List.getElem?_map]) v

/-- The subtree at a vertex commutes with mapping the labels. -/
theorem subtree?_map {α β : Type} (g : α → β) (t : RoseTree α) (v : List ℕ) :
    (subtree? t v).map (RoseTree.map g) = subtree? (t.map g) v :=
  foldl_subtree_map g v (some t)

/-- A vertex of a term is a vertex of the term with its references relabelled. -/
theorem isSome_subtree?_mapRefs (f : ℕ → ℕ) (t : Tree) (v : List ℕ) :
    (subtree? (mapRefs f t) v).isSome = (subtree? t v).isSome :=
  calc (subtree? (mapRefs f t) v).isSome
      = ((subtree? (mapRefs f t) v).map (RoseTree.map fun _ ↦ ())).isSome :=
        (Option.isSome_map ..).symm
    _ = (subtree? (shape t) v).isSome := by rw [subtree?_map, ← shape, shape_mapRefs]
    _ = ((subtree? t v).map (RoseTree.map fun _ ↦ ())).isSome := by rw [subtree?_map]; rfl
    _ = (subtree? t v).isSome := Option.isSome_map ..

/-- The migration's step keeps the shapes of the terms it migrates. -/
theorem foldl_migrateStep_shape (ds : List Tree) : ∀ ps : List Payload,
    (ds.foldl migrateStep ps).map (shape ∘ Payload.body) =
      ps.map (shape ∘ Payload.body) ++ ds.map shape :=
  List.rec (fun ps ↦ by simp) (fun t ds ih ps ↦ by
    rw [List.foldl_cons, ih, migrateStep, List.map_append, List.map_cons, List.append_assoc]
    simp [payloadOf, shape_mapRefs]) ds

/-- The migration moves no vertex: each payload's body has the shape of its definition. -/
theorem migrate_shape (ds : List Tree) :
    (migrate ds).map (shape ∘ Payload.body) = ds.map shape := by
  rw [migrate_eq, foldl_migrateStep_shape]
  rfl

/-! ## Names -/

/-- Entries of children's results, the children's positions counted from a start, each entry's
vertex extended by its child's position. -/
def underChildren {β : Type} (start : ℕ) (rs : List (List (List ℕ × β))) : List (List ℕ × β) :=
  (rs.zipIdx start).flatMap fun (r, i) ↦ r.map fun (v, b) ↦ (i :: v, b)

/-- One node's references to definitions with their vertices, from its children's, following
the term grammar as {name}`mapRefs` does. -/
def refVerticesStep (l : ℕ) (rs : List (Tree × List (List ℕ × ℕ))) : List (List ℕ × ℕ) :=
  if l == Label.ref then rs.map fun r ↦ ([], r.1.label)
  else if l == Label.lam then
    match rs with
    | _ :: rest => underChildren 1 (rest.map Prod.snd)
    | [] => []
  else if isTermFormer l then underChildren 0 (rs.map Prod.snd)
  else []

/-- The vertices of a term's references to definitions, each with the position it refers to. -/
def refVertices : Tree → List (List ℕ × ℕ) := RoseTree.para refVerticesStep

/-- A note on a name: the name a definition is declared under, or the name written at a
reference. -/
inductive Note where
  /-- The name a definition is declared under. -/
  | declared (n : List Char)
  /-- The name written at a reference. -/
  | written (n : List Char)
  deriving DecidableEq, Repr

/-- The names of a bundle of named definitions as annotations keyed by a definition's position
and a vertex: each definition's name at the root of its term, and the name of the definition
each reference refers to at the reference's vertex. -/
def nameNotes (ds : List (List Char × Tree)) : List ((ℕ × List ℕ) × Note) :=
  let names := ds.map Prod.fst
  (ds.zipIdx.flatMap fun ((n, t), i) ↦
    ((i, []), .declared n) :: (refVertices t).map fun (v, p) ↦ ((i, v), .written (names.getD p [])))

/-! ## Re-keying -/

/-- A table of annotations keyed by a definition's position and a vertex, re-keyed by the
definition's identifier and the same vertex. -/
def rekey {K : Type} (cids : List (List UInt8)) (notes : List ((ℕ × List ℕ) × K)) :
    List ((List UInt8 × List ℕ) × K) :=
  notes.map fun ((i, v), k) ↦ ((cids.getD i [], v), k)

/-- Whether a key addresses a node of a bundle's definitions. -/
def ValidKey (ds : List Tree) (key : ℕ × List ℕ) : Prop :=
  ∃ h : key.1 < ds.length, (subtree? ds[key.1] key.2).isSome

/-- Every key of a table re-keyed by the migration's identifiers, keyed by positions that address
nodes of the definitions, addresses a node of a payload with that identifier. -/
theorem valid_rekey {K : Type} (ds : List Tree) (notes : List ((ℕ × List ℕ) × K))
    (h : ∀ e ∈ notes, ValidKey ds e.1) :
    ∀ e ∈ rekey ((migrate ds).map Payload.cid) notes,
      ∃ p ∈ migrate ds, p.cid = e.1.1 ∧ (subtree? p.body e.1.2).isSome := by
  intro e he
  obtain ⟨⟨⟨i, v⟩, k⟩, hn, rfl⟩ := List.mem_map.mp he
  obtain ⟨hi, hv⟩ := h _ hn
  have hlen : (migrate ds).length = ds.length := by
    simpa using congrArg List.length (migrate_shape ds)
  have hi' : i < (migrate ds).length := hlen ▸ hi
  refine ⟨(migrate ds)[i], List.getElem_mem hi', ?_, ?_⟩
  · change (migrate ds)[i].cid = ((migrate ds).map Payload.cid).getD i []
    rw [getD_of_lt _ (by simpa using hi'), List.getElem_map]
  · have hs : shape (migrate ds)[i].body = shape ds[i] := by
      have := congrArg (·[i]?) (migrate_shape ds)
      simpa [List.getElem?_map, List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi]
        using this
    calc (subtree? (migrate ds)[i].body v).isSome
        = ((subtree? (migrate ds)[i].body v).map (RoseTree.map fun _ ↦ ())).isSome :=
          (Option.isSome_map ..).symm
      _ = (subtree? (shape ds[i]) v).isSome := by rw [subtree?_map, ← shape, hs]
      _ = ((subtree? ds[i] v).map (RoseTree.map fun _ ↦ ())).isSome := by
          rw [subtree?_map]; rfl
      _ = true := (Option.isSome_map ..).trans hv

end Geb.Kernel.Identity

end
