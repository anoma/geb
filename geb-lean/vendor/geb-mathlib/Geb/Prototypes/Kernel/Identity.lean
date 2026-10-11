/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Kernel.Basic
public import Geb.Prototypes.Kernel.Blake3
public import Geb.Prototypes.Kernel.Strict

set_option doc.verso true

/-!
# Content identity

A definition is identified by the CIDv1 \[RatajBerjon2026\] of its payload: the canonical
encoding \[RFC9804\] of the S-expression {lit}`(geb-def/v1 geb-kernel/v1 (imports…) body)`,
whose imports are the identifiers of the definitions its body refers to, each once, in the order
of their first references, and whose body is the definition's term with each reference to a
definition replaced by the reference to the position of its identifier among the imports. The
CID is of the codec {lit}`raw`, {lit}`0x55`, and its multihash \[BenetSporny2023\] is of
BLAKE3, 32 bytes under the code {lit}`0x1e` of \[Multiformats2026\]. A
definition's name is no part of its payload, so renaming a definition leaves every identifier
unchanged, and a change of a definition changes the identifiers of the definitions that refer
to it, through their imports.

The kernel refers to a definition by its position in a bundle. The migration
({lit}`migrate`) computes the payloads and identifiers of a bundle's definitions in order; the
linker ({lit}`link`) gives the kernel a bundle again from payloads in an order of dependence,
replacing each import by the position of the definition it identifies. Linking relabels the
references and nothing else: the migration of a linked bundle gives back the payloads it was
linked from ({lit}`migrate_link`), so migrating twice changes nothing ({lit}`migrate_idem`).

## Main definitions

* {lit}`varint`, {lit}`multihash`, {lit}`cidOf` — the encodings of an identifier.
* {lit}`mapRefs`, {lit}`refsOf` — the references of a term, relabelled and listed.
* {lit}`Payload`, {lit}`Payload.bytes`, {lit}`payloadOf` — a definition's payload.
* {lit}`migrate`, {lit}`link` — from positions to identifiers and back.

## Main statements

* {lit}`migrate_link` — migrating a linked bundle gives back its payloads.
* {lit}`migrate_idem` — migrating twice changes nothing.

## References

* \[RatajBerjon2026\] — CIDs.
* \[BenetSporny2023\] — multihashes.
* \[Multiformats2026\] — the multicodec table.
* \[RFC9804\] — the canonical encoding.

## Tags

content identity, CID, multihash, BLAKE3, linking
-/

@[expose] public section

namespace Geb.Kernel.Identity

open Document

/-! ## Identifiers -/

/-- The little-endian base-128 digits of a number, at least one, on a bound of steps. -/
def base128 (n : ℕ) : List ℕ :=
  Nat.rec (motive := fun _ ↦ ℕ → List ℕ) (fun m ↦ [m])
    (fun _ ih m ↦ if m < 128 then [m] else m % 128 :: ih (m / 128)) n n

/-- A number as an unsigned varint, the shortest form of unsigned LEB128: base-128 digits, the
least significant first, each but the last with its high bit set. -/
def varint (n : ℕ) : List UInt8 :=
  let ds := base128 n
  (ds.dropLast.map fun d ↦ (d + 128).toUInt8) ++ ds.getLast?.toList.map (·.toUInt8)

/-- The multicodec of BLAKE3's multihash. -/
def blake3Code : ℕ := 0x1e

/-- The multicodec of the codec {lit}`raw`. -/
def rawCode : ℕ := 0x55

/-- The multihash of bytes: the code of BLAKE3, the digest's length and the digest. -/
def multihash (bs : List UInt8) : List UInt8 :=
  varint blake3Code ++ varint 32 ++ Blake3.hash bs

/-- The CIDv1 of bytes of the codec {lit}`raw`: the version, the codec and the multihash. -/
def cidOf (bs : List UInt8) : List UInt8 := varint 1 ++ varint rawCode ++ multihash bs

/-- The bytes of characters, one per byte. -/
def bytesOf (cs : List Char) : List UInt8 := cs.map fun c ↦ c.toNat.toUInt8

/-- The characters of bytes, one per byte. -/
def charsOf (bs : List UInt8) : List Char := bs.map fun b ↦ Char.ofNat b.toNat

/-! ## References -/

/-- Whether a node of a term has terms for its children: an application, the unit, a pair, a
projection, a conditional or a list's construction. -/
def isTermFormer (l : ℕ) : Bool :=
  l == Label.app || l == Label.unit || l == Label.pair || l == Label.fst || l == Label.snd ||
    l == Label.cond || l == Label.cons

/-- One node of a term with its references relabelled: a reference's child, the position of a
definition, relabelled; an abstraction's body and a term former's children traversed; and the
type annotations, quoted trees and primitives' indices kept, as {lit}`Geb.Kernel.trav` keeps
them, so that a quoted tree is never read as a term. -/
def mapRefsStep (f : ℕ → ℕ) (l : ℕ) (rs : List (Tree × Tree)) : Tree :=
  RoseTree.node l <|
    if l == Label.ref then rs.map fun r ↦ RoseTree.node (f r.1.label) r.1.children
    else if l == Label.lam then
      match rs with
      | r :: rest => r.1 :: rest.map Prod.snd
      | [] => []
    else if isTermFormer l then rs.map Prod.snd
    else rs.map Prod.fst

/-- A term with each reference to a definition relabelled. -/
def mapRefs (f : ℕ → ℕ) : Tree → Tree := RoseTree.para (mapRefsStep f)

/-- One node's references to definitions, from its children's. -/
def refsStep (l : ℕ) (rs : List (Tree × List ℕ)) : List ℕ :=
  if l == Label.ref then rs.map fun r ↦ r.1.label
  else if l == Label.lam then
    match rs with
    | _ :: rest => rest.flatMap Prod.snd
    | [] => []
  else if isTermFormer l then rs.flatMap Prod.snd
  else []

/-- The references of a term to definitions, in the order of the traversal, with repetitions. -/
def refsOf : Tree → List ℕ := RoseTree.para refsStep

/-- The relabelling of a node's references. -/
theorem mapRefs_node (f : ℕ → ℕ) (l : ℕ) (cs : List Tree) :
    mapRefs f (RoseTree.node l cs) = RoseTree.node l
      (if l == Label.ref then cs.map fun c ↦ RoseTree.node (f c.label) c.children
       else if l == Label.lam then
        match cs with
        | c :: rest => c :: rest.map (mapRefs f)
        | [] => []
       else if isTermFormer l then cs.map (mapRefs f)
       else cs) := by
  simp only [mapRefs, RoseTree.para_node, mapRefsStep]
  split_ifs
  · simp [Function.comp_def]
  · cases cs <;> simp [Function.comp_def]
  · simp [Function.comp_def]
  · simp [Function.comp_def]

/-- A node's references. -/
theorem refsOf_node (l : ℕ) (cs : List Tree) :
    refsOf (RoseTree.node l cs) =
      if l == Label.ref then cs.map RoseTree.label
      else if l == Label.lam then
        match cs with
        | _ :: rest => rest.flatMap refsOf
        | [] => []
      else if isTermFormer l then cs.flatMap refsOf
      else [] := by
  simp only [refsOf, RoseTree.para_node, refsStep]
  split_ifs
  · simp [Function.comp_def]
  · cases cs <;> simp [List.flatMap_map]
  · simp [List.flatMap_map]
  · rfl

/-- Relabelling by the identity changes nothing. -/
theorem mapRefs_id : ∀ t : Tree, mapRefs id t = t :=
  RoseTree.ind fun l cs ih ↦ by
    rw [mapRefs_node]
    split_ifs
    · exact congrArg _ ((List.map_congr_left fun c _ ↦ by simp).trans cs.map_id)
    · cases cs with
      | nil => rfl
      | cons c rest =>
        exact congrArg (fun xs ↦ RoseTree.node l (c :: xs)) ((List.map_congr_left fun x hx ↦
          ih x (List.mem_cons_of_mem c hx)).trans rest.map_id)
    · exact congrArg _ ((List.map_congr_left ih).trans cs.map_id)
    · rfl

/-- The references of a relabelled term are the term's, relabelled. -/
theorem refsOf_mapRefs (f : ℕ → ℕ) : ∀ t : Tree, refsOf (mapRefs f t) = (refsOf t).map f :=
  RoseTree.ind fun l cs ih ↦ by
    rw [mapRefs_node, refsOf_node, refsOf_node]
    split_ifs
    · simp [Function.comp_def]
    · cases cs with
      | nil => rfl
      | cons c rest =>
        simp only [List.flatMap_map, List.map_flatMap]
        exact List.flatMap_congr fun x hx ↦ ih x (List.mem_cons_of_mem c hx)
    · simp only [List.flatMap_map, List.map_flatMap]
      exact List.flatMap_congr fun x hx ↦ ih x hx
    · rfl

/-- Relabelling twice is relabelling by the composite. -/
theorem mapRefs_mapRefs (f g : ℕ → ℕ) :
    ∀ t : Tree, mapRefs f (mapRefs g t) = mapRefs (f ∘ g) t :=
  RoseTree.ind fun l cs ih ↦ by
    rw [mapRefs_node, mapRefs_node, mapRefs_node]
    split_ifs
    · simp [Function.comp_def]
    · cases cs with
      | nil => rfl
      | cons c rest =>
        change RoseTree.node l (c :: (rest.map (mapRefs g)).map (mapRefs f)) =
          RoseTree.node l (c :: rest.map (mapRefs (f ∘ g)))
        rw [List.map_map]
        exact congrArg (fun xs ↦ RoseTree.node l (c :: xs))
          (List.map_congr_left fun x hx ↦ ih x (List.mem_cons_of_mem c hx))
    · rw [List.map_map]
      exact congrArg _ (List.map_congr_left fun x hx ↦ ih x hx)
    · rfl

/-- Relabellings that agree on a term's references agree on the term. -/
theorem mapRefs_congr (f g : ℕ → ℕ) :
    ∀ t : Tree, (∀ i ∈ refsOf t, f i = g i) → mapRefs f t = mapRefs g t :=
  RoseTree.ind fun l cs ih h ↦ by
    rw [mapRefs_node, mapRefs_node]
    rw [refsOf_node] at h
    split_ifs at h ⊢
    · exact congrArg _ (List.map_congr_left fun c hc ↦ by
        rw [h c.label (List.mem_map_of_mem hc)])
    · cases cs with
      | nil => rfl
      | cons c rest =>
        exact congrArg (fun xs ↦ RoseTree.node l (c :: xs)) (List.map_congr_left fun x hx ↦
          ih x (List.mem_cons_of_mem c hx) fun i hi ↦ h i (List.mem_flatMap.mpr ⟨x, hx, hi⟩))
    · exact congrArg _ (List.map_congr_left fun x hx ↦
        ih x hx fun i hi ↦ h i (List.mem_flatMap.mpr ⟨x, hx, hi⟩))
    · rfl

/-! ## Payloads -/

/-- A definition's payload: the identifiers of the definitions it refers to, and its term with
references to their positions among them. -/
structure Payload where
  /-- The identifiers referred to, each once. -/
  imports : List (List UInt8)
  /-- The term, its references to positions among the imports. -/
  body : Tree

/-- An atom of characters. -/
def atom (s : List Char) : SExp := RoseTree.node (some s) []

/-- A kernel term as an S-expression: a leaf as the decimal numeral of its label, and a node of
children as the list of its label's numeral and its children. -/
def termSExp : Tree → SExp :=
  RoseTree.elim fun l rs ↦
    if rs.isEmpty then atom (Csexp.decOf l) else RoseTree.node none (atom (Csexp.decOf l) :: rs)

/-- The tag of a payload's schema. -/
def schemaTag : List Char := ['g', 'e', 'b', '-', 'd', 'e', 'f', '/', 'v', '1']

/-- The tag of the semantic profile, the kernel of the bootstrap. -/
def profileTag : List Char := ['g', 'e', 'b', '-', 'k', 'e', 'r', 'n', 'e', 'l', '/', 'v', '1']

/-- A payload as an S-expression. -/
def Payload.sexp (p : Payload) : SExp :=
  RoseTree.node none [atom schemaTag, atom profileTag,
    RoseTree.node none (p.imports.map fun c ↦ atom (charsOf c)), termSExp p.body]

/-- A payload's bytes: its S-expression in the canonical encoding. -/
def Payload.bytes (p : Payload) : List UInt8 := bytesOf (canonOf p.sexp)

/-- A payload's identifier. -/
def Payload.cid (p : Payload) : List UInt8 := cidOf p.bytes

/-- The payload of a term whose references are to positions of definitions with the identifiers
given: its imports are the identifiers referred to, each once, in the order of their first
references, a reference beyond the identifiers giving the empty list, which no identifier is. -/
def payloadOf (cids : List (List UInt8)) (t : Tree) : Payload :=
  let imports := ((refsOf t).map fun p ↦ cids.getD p []).eraseDups
  ⟨imports, mapRefs (fun p ↦ imports.idxOf (cids.getD p [])) t⟩

/-- Payloads extended by the payload of a term referring to them by position. -/
def migrateStep (ps : List Payload) (t : Tree) : List Payload :=
  ps ++ [payloadOf (ps.map Payload.cid) t]

/-- The payloads of a bundle's definitions, in order, each referring to the definitions before
it by their identifiers, each identifier computed once. -/
def migrate (ds : List Tree) : List Payload :=
  (ds.foldl (fun (acc : List Payload × List (List UInt8)) t ↦
    let p := payloadOf acc.2 t
    (acc.1 ++ [p], acc.2 ++ [p.cid])) ([], [])).1

/-- The bundle of payloads in an order of dependence: each payload's imports replaced by the
position of the first payload they identify. -/
def link (ps : List Payload) : List Tree :=
  let cids := ps.map Payload.cid
  ps.map fun p ↦ mapRefs (fun i ↦ cids.idxOf (p.imports.getD i [])) p.body

/-- The migration computes each identifier once, as the payloads' identifiers. -/
theorem foldl_migrate (ds : List Tree) :
    ∀ ps : List Payload, ds.foldl (fun (acc : List Payload × List (List UInt8)) t ↦
        let p := payloadOf acc.2 t
        (acc.1 ++ [p], acc.2 ++ [p.cid])) (ps, ps.map Payload.cid) =
      (ds.foldl migrateStep ps, (ds.foldl migrateStep ps).map Payload.cid) :=
  List.rec (fun _ ↦ rfl) (fun t ds ih ps ↦ by
    simp only [List.foldl_cons]
    rw [← ih (migrateStep ps t)]
    simp [migrateStep]) ds

/-- The migration is the fold of its step. -/
theorem migrate_eq (ds : List Tree) : migrate ds = ds.foldl migrateStep [] := by
  rw [migrate, show (([], []) : List Payload × List (List UInt8)) = ([], ([] : List Payload).map
    Payload.cid) from rfl, foldl_migrate]

/-- An identifier is not empty. -/
theorem cid_ne_nil (p : Payload) : p.cid ≠ [] := by
  simp [Payload.cid, cidOf, varint, base128]

/-- The position of an element of a list's prefix in the list is its position in the prefix. -/
theorem idxOf_of_prefix {α : Type} [BEq α] [LawfulBEq α] {cs cids : List α} (h : cs <+: cids)
    {c : α} (hc : c ∈ cs) : cids.idxOf c = cs.idxOf c := by
  obtain ⟨rest, rfl⟩ := h
  exact List.rec (motive := fun cs ↦ c ∈ cs → (cs ++ rest).idxOf c = cs.idxOf c)
    (fun h ↦ absurd h List.not_mem_nil)
    (fun x xs ih h ↦ by
      rw [List.cons_append, List.idxOf_cons, List.idxOf_cons]
      cases hx : x == c with
      | true => rfl
      | false =>
        have hm : c ∈ xs := (List.mem_cons.mp h).resolve_left fun e ↦ by
          rw [e, beq_self_eq_true] at hx
          exact Bool.false_ne_true hx.symm
        rw [ih hm]) cs hc

/-- The position of an element absent from a list is the list's length. -/
theorem idxOf_of_not_mem {α : Type} [BEq α] [LawfulBEq α] {c : α} :
    ∀ cids : List α, c ∉ cids → cids.idxOf c = cids.length :=
  List.rec (fun _ ↦ rfl) fun x xs ih h ↦ by
    have hx : (x == c) = false := beq_eq_false_iff_ne.mpr fun e ↦ h (e ▸ List.mem_cons_self)
    rw [List.idxOf_cons, hx, ih fun hm ↦ h (List.mem_cons_of_mem x hm)]
    rfl

/-- A list's entry within its length is its element. -/
theorem getD_of_lt {α : Type} {l : List α} {i : ℕ} (d : α) (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h, Option.getD_some]

/-- A list's entry beyond its length is the default. -/
theorem getD_of_le {α : Type} {l : List α} {i : ℕ} (d : α) (h : l.length ≤ i) :
    l.getD i d = d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none h, Option.getD_none]

/-- Looking up an element of a list at its position gives it back. -/
theorem getD_idxOf_of_mem {α : Type} [BEq α] [LawfulBEq α] (d : α) {c : α} :
    ∀ cs : List α, c ∈ cs → cs.getD (cs.idxOf c) d = c :=
  List.rec (fun h ↦ absurd h List.not_mem_nil) fun x xs ih h ↦ by
    rw [List.idxOf_cons]
    cases hx : x == c with
    | true => exact eq_of_beq hx
    | false =>
      have hm : c ∈ xs := (List.mem_cons.mp h).resolve_left fun e ↦ by
        rw [e, beq_self_eq_true] at hx
        exact Bool.false_ne_true hx.symm
      exact ih hm

/-- Looking up, in a prefix of the identifiers, the position in all of them of an identifier of
the prefix, or of the empty list, which no identifier is, gives it back. -/
theorem getD_idxOf {cs cids : List (List UInt8)} (hpre : cs <+: cids) (hnil : [] ∉ cids)
    {c : List UInt8} (hc : c ∈ cs ∨ c = []) : cs.getD (cids.idxOf c) [] = c := by
  rcases hc with hc | rfl
  · rw [idxOf_of_prefix hpre hc]
    exact getD_idxOf_of_mem [] cs hc
  · rw [idxOf_of_not_mem cids hnil]
    exact getD_of_le _ hpre.length_le

/-- An entry of a list looked up with the empty list as default is an element or the empty
list. -/
theorem getD_mem_or_nil (cs : List (List UInt8)) (q : ℕ) :
    cs.getD q [] ∈ cs ∨ cs.getD q [] = [] := by
  by_cases h : q < cs.length
  · exact Or.inl (by rw [getD_of_lt _ h]; exact List.getElem_mem h)
  · exact Or.inr (getD_of_le _ (Nat.le_of_not_lt h))

/-- Re-deriving the payload of a term linked from a payload, among identifiers that the payload's
are a prefix of, gives the payload back. -/
theorem payloadOf_link (cs cids : List (List UInt8)) (hpre : cs <+: cids) (hnil : [] ∉ cids)
    (t : Tree) :
    payloadOf cs (mapRefs (fun i ↦ cids.idxOf ((payloadOf cs t).imports.getD i []))
      (payloadOf cs t).body) = payloadOf cs t := by
  set imports := ((refsOf t).map fun p ↦ cs.getD p []).eraseDups with himports
  have hp : payloadOf cs t = ⟨imports, mapRefs (fun p ↦ imports.idxOf (cs.getD p [])) t⟩ := rfl
  rw [hp]
  have hmem : ∀ q ∈ refsOf t, cs.getD q [] ∈ imports := fun q hq ↦
    List.mem_eraseDups.mpr (List.mem_map_of_mem hq)
  have hback : ∀ q ∈ refsOf t,
      imports.getD (imports.idxOf (cs.getD q [])) [] = cs.getD q [] := fun q hq ↦
    getD_idxOf_of_mem [] imports (hmem q hq)
  have hlnk : ∀ q ∈ refsOf t,
      cs.getD (cids.idxOf (imports.getD (imports.idxOf (cs.getD q [])) [])) [] = cs.getD q [] :=
    fun q hq ↦ by rw [hback q hq]; exact getD_idxOf hpre hnil (getD_mem_or_nil cs q)
  simp only [payloadOf, refsOf_mapRefs, List.map_map, mapRefs_mapRefs]
  have himp : ((refsOf t).map ((fun p ↦ cs.getD p []) ∘
      (fun i ↦ cids.idxOf (imports.getD i [])) ∘ fun p ↦ imports.idxOf (cs.getD p []))).eraseDups =
      imports := by
    rw [himports]
    congr 1
    exact List.map_congr_left fun q hq ↦ hlnk q hq
  rw [himp]
  congr 1
  exact mapRefs_congr _ _ t fun q hq ↦ by
    simp only [Function.comp_apply]
    rw [hlnk q hq]

/-- Payloads each of which is the payload of a term referring by position to the payloads before
it. -/
def Canonical (ps : List Payload) : Prop :=
  ∀ k (hk : k < ps.length), ∃ t, ps[k] = payloadOf ((ps.take k).map Payload.cid) t

/-- The step of the migration keeps payloads canonical. -/
theorem canonical_migrateStep {ps : List Payload} (h : Canonical ps) (t : Tree) :
    Canonical (migrateStep ps t) := by
  intro k hk
  simp only [migrateStep, List.length_append, List.length_singleton] at hk
  by_cases hlt : k < ps.length
  · obtain ⟨u, hu⟩ := h k hlt
    refine ⟨u, ?_⟩
    simp only [migrateStep, List.getElem_append_left hlt, List.take_append_of_le_length
      (Nat.le_of_lt hlt), hu]
  · have hk' : k = ps.length := by omega
    subst hk'
    refine ⟨t, ?_⟩
    simp [migrateStep]

/-- The migration's payloads are canonical. -/
theorem canonical_migrate (ds : List Tree) : Canonical (migrate ds) := by
  rw [migrate_eq]
  suffices h : ∀ ps, Canonical ps → Canonical (ds.foldl migrateStep ps) from
    h [] fun k hk ↦ absurd hk (Nat.not_lt_zero k)
  exact List.rec (fun _ h ↦ h) (fun t ds ih ps h ↦ ih _ (canonical_migrateStep h t)) ds

/-- Migrating a linked bundle of canonical payloads gives back its payloads: linking relabels
the references and nothing else. -/
theorem migrate_link {ps : List Payload} (h : Canonical ps) : migrate (link ps) = ps := by
  rw [migrate_eq]
  have hnil : [] ∉ ps.map Payload.cid := fun hm ↦ by
    obtain ⟨p, -, hp⟩ := List.mem_map.mp hm
    exact cid_ne_nil p hp
  suffices hk : ∀ k, k ≤ ps.length → ((link ps).take k).foldl migrateStep [] = ps.take k by
    have := hk ps.length le_rfl
    rwa [List.take_of_length_le (by simp [link]), List.take_length] at this
  intro k
  refine Nat.rec (motive := fun k ↦ k ≤ ps.length →
    ((link ps).take k).foldl migrateStep [] = ps.take k) (fun _ ↦ rfl) (fun k ih hk ↦ ?_) k
  have hlt : k < ps.length := hk
  obtain ⟨t, ht⟩ := h k hlt
  rw [List.take_add_one, List.foldl_append, ih (Nat.le_of_lt hlt), List.take_add_one,
    List.getElem?_eq_getElem hlt]
  have hlink : (link ps)[k]? = some (mapRefs (fun i ↦ (ps.map Payload.cid).idxOf
      (ps[k].imports.getD i [])) ps[k].body) := by
    simp [link, hlt]
  rw [hlink]
  simp only [Option.toList_some, List.foldl_cons, List.foldl_nil, migrateStep]
  congr 2
  rw [ht]
  have hpre : (ps.take k).map Payload.cid <+: ps.map Payload.cid := by
    rw [List.map_take]
    exact List.take_prefix k _
  exact payloadOf_link _ _ hpre hnil t

/-- Migrating twice changes nothing. -/
theorem migrate_idem (ds : List Tree) : migrate (link (migrate ds)) = migrate ds :=
  migrate_link (canonical_migrate ds)


end Geb.Kernel.Identity

end
