/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Kernel.Annotation
public import Geb.Prototypes.Kernel.Durable
public import Geb.Prototypes.Kernel.Reader

set_option doc.verso true in
/-!
# Source annotations of kernel definitions

A document remains the authority for binder spellings and comments. A separate pass records
which source occurrences give rise to vertices of the kernel terms read by
{name}`Geb.Kernel.readForms`. An abstraction's binder names address its successive lambda
nodes; a let binder addresses the lambda in its application. Application arguments address
the corresponding nested applications. A quotation is data and supplies no binder names.

Addresses of source occurrences start with the index of a document item. Addresses of core
occurrences start with the index of a definition, followed by a vertex of its term. The table
is a relation: several source occurrences can address one core vertex. The complete document
also retains occurrences without a core address, including abbreviations and trailing prose.
Re-keying a core address by content identity leaves the source occurrence in the value of the
table, so equal definitions retain their distinct annotations.

## Main definitions

* {lit}`Origin` — a source occurrence and its role at a kernel vertex.
* {lit}`trace` — the correspondence for the kernel's term forms.
* {lit}`annotate` — the source, resolved definitions and validated correspondence.
* {lit}`Annotated.notesAt`, {lit}`Annotated.unattached` — attached source information and
  trivia without a core address.
* {lit}`Annotated.rekeyed` — annotations keyed by definition CID and vertex.
* {lit}`Annotated.write`, {lit}`read` — canonical records and their checked reading.

## Main statements

* {lit}`source_of_annotate`, {lit}`readForms_of_annotate` — source and core preservation.
* {lit}`definitions_eq_of_erase_eq` — source decorations do not change the core.
* {lit}`valid_rekeyed`, {lit}`rekeyed_sources` — valid addresses and preserved source
  occurrences after migration to content identity.
* {lit}`read_write` — the canonical record's retraction.

## Implementation notes

This pass operates on kernel declarations before any module or datatype elaboration. It does
not infer source occurrences from equal subtrees. Types and quoted data are retained in full
in the source document; the table addresses their roots, without expanding source addresses
through type abbreviations or the character encoding of quoted atoms.

## Tags

kernel, source, binder, comment, annotation, vertex
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.SourceAnnotation

open scoped FinEnum
open Document

/-- How a source occurrence contributes to the resolved term. -/
inductive Role where
  /-- A term, keyword, type or datum contributing to a core vertex. -/
  | syntax
  /-- The spelling of the variable bound by a lambda vertex. -/
  | binder
  deriving DecidableEq, Repr

/-- A source vertex, a core vertex and the role of the source at the core. Paths are relative
to the source expression and resolved term until a declaration prefixes their roots. -/
structure Origin where
  /-- The path in the source. -/
  source : List ℕ
  /-- The path in the kernel term. -/
  core : List ℕ
  /-- Whether the occurrence names a binder or contributes syntax. -/
  role : Role := .syntax
  deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprOrigin.repr

/-- Translate both roots of a correspondence. -/
def under (source core : List ℕ) (os : List Origin) : List Origin :=
  os.map fun o ↦ { o with source := source ++ o.source, core := core ++ o.core }

/-- The correspondence at a syntax root and its keyword. -/
def headOrigins : List Origin := [⟨[], [], .syntax⟩, ⟨[0], [], .syntax⟩]

/-- Correspondences of curried applications, with the arguments' source roots already set. -/
def applications (f : List Origin) (xs : List (List Origin)) : List Origin :=
  xs.foldl (fun os x ↦ under [] [0] os ++ under [] [1] x) f

/-- The paths of binder declarations in the source spelling accepted by {name}`binders`. -/
def binderPaths (b : SExp) : List (List ℕ × SExp) :=
  match b.label, b.children with
  | some _, _ => []
  | none, [x, _] =>
    if x.label.isSome then [([], b)] else b.children.zipIdx.map fun (c, i) ↦ ([i], c)
  | none, cs => cs.zipIdx.map fun (c, i) ↦ ([i], c)

/-- One source node's correspondence, from the correspondences of its children. The resolver
separately determines whether the source is accepted and supplies the kernel term. -/
def traceStep (a : Option (List Char)) (cs : List (SExp × List Origin)) : List Origin :=
  let args (xs : List (SExp × List Origin)) (start : ℕ) :=
    xs.zipIdx start |>.map fun (c, i) ↦ under [i] [] c.2
  let direct (xs : List (SExp × List Origin)) :=
    headOrigins ++ (xs.zipIdx.flatMap fun (c, i) ↦ under [i + 1] [i] c.2)
  match a, cs with
  | some _, _ => [⟨[], [], .syntax⟩]
  | none, (h, rh) :: rest =>
    match h.label, rest with
    | some ['l', 'a', 'm'], [(b, _), (_, body)] =>
      let bs := binderPaths b
      headOrigins ++
        (bs.zipIdx.flatMap fun ((p, _), i) ↦
          [⟨[1] ++ p, List.replicate i 1, .syntax⟩,
           ⟨[1] ++ p ++ [0], List.replicate i 1, .binder⟩,
           ⟨[1] ++ p ++ [1], List.replicate i 1 ++ [0], .syntax⟩]) ++
        under [2] (List.replicate bs.length 1) body
    | some ['l', 'e', 't'], [(_, _), (_, _), (_, e), (_, body)] =>
      headOrigins ++ [⟨[1], [0], .binder⟩, ⟨[2], [0, 0], .syntax⟩] ++
        under [3] [1] e ++ under [4] [0, 1] body
    | some ['p', 'a', 'i', 'r'], _
    | some ['f', 's', 't'], _
    | some ['s', 'n', 'd'], _
    | some ['i', 'f'], _
    | some ['c', 'o', 'n', 's'], _ => direct rest
    | some ['q', 'u', 'o', 't', 'e'], [_]
    | some ['n', 'i', 'l'], [_] => headOrigins ++ [⟨[1], [0], .syntax⟩]
    | some ['f', 'o', 'l', 'd'], _ :: xs
    | some ['p', 'a', 'r', 'a'], _ :: xs
    | some ['i', 't', 'e', 'r'], _ :: xs =>
      ⟨[], [], .syntax⟩ :: applications
        [⟨[0], [], .syntax⟩, ⟨[1], [0], .syntax⟩] (args xs 2)
    | some ['f', 'o', 'l', 'd', 'r'], _ :: _ :: xs
    | some ['l', 'c', 'a', 's', 'e'], _ :: _ :: xs =>
      ⟨[], [], .syntax⟩ :: applications
        [⟨[0], [], .syntax⟩, ⟨[1], [0], .syntax⟩, ⟨[2], [1], .syntax⟩] (args xs 3)
    | _, _ => ⟨[], [], .syntax⟩ :: applications (under [0] [] rh) (args rest 1)
  | none, [] => []

/-- The source-to-core correspondence of a term, after expanding numeral abbreviations.
Expansion changes atom spellings but preserves every source path. -/
def trace (nums : NumNames) (e : SExp) : List Origin :=
  RoseTree.para traceStep (expandNums nums e)

/-- The correspondences of a document's declarations. Abbreviations affect the reader's
interpretation but have no definition vertex of their own. -/
def origins (d : Doc) : List Origin :=
  let step (st : NumNames × ℕ × List Origin) (item : SExpr × ℕ) :=
    let (nums, n, os) := st
    let (e, i) := item
    match (RoseTree.erase e).children with
    | [kw, name, body] =>
      match kw.label with
      | some ['d', 'e', 'f'] =>
        (nums, n + 1, os ++
          [⟨[i], [n], .syntax⟩, ⟨[i, 0], [n], .syntax⟩, ⟨[i, 1], [n], .syntax⟩] ++
          under [i, 2] [n] (trace nums body))
      | some ['d', 'e', 'f', 'n', 'u', 'm'] =>
        (((name.label.getD [], (numOf nums body).getD []) :: nums), n, os)
      | _ => st
    | _ => st
  (d.items.zipIdx.foldl step ([], 0, [])).2.2

/-- Look up a vertex of a forest, whose first index selects a tree. -/
def atForest {α : Type} (ts : List (RoseTree α)) (v : List ℕ) : Option (RoseTree α) :=
  match v with
  | [] => none
  | i :: p => ts[i]?.bind fun t ↦ Identity.subtree? t p

/-- Whether both ends of a correspondence exist, with binder names on lambda vertices. -/
def validOrigin (d : Doc) (ds : List (List Char × Tree)) (o : Origin) : Bool :=
  match atForest d.items o.source, atForest (ds.map Prod.snd) o.core with
  | some s, some t =>
    match o.role with
    | .syntax => true
    | .binder => s.label.2.isSome && t.label == Label.lam
  | _, _ => false

/-- A complete source document beside its resolved definitions and their correspondence. -/
structure Annotated where
  /-- The original document, with comments at all positions and trailing prose. -/
  source : Doc
  /-- The definitions returned by the kernel reader. -/
  definitions : List (List Char × Tree)
  /-- Source-to-core correspondences, rooted in this document and this bundle. -/
  correspondence : List Origin

/-- Read kernel declarations and validate the derived addresses. No compiler or reader is
replaced: the definitions are exactly the result of {name}`readForms`. -/
def annotate (d : Doc) : Option Annotated := do
  let ds ← readForms (d.items.map RoseTree.erase)
  let os := origins d
  if os.all (validOrigin d ds) then some ⟨d, ds, os⟩ else none

/-- Reading annotations preserves the original source document. -/
theorem source_of_annotate {d : Doc} {a : Annotated} (h : annotate d = some a) :
    a.source = d := by
  simp only [annotate, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨ds, _, h⟩ := h
  split at h
  · cases Option.some.inj h
    rfl
  · cases h

/-- The annotations do not change the kernel reader's definitions. -/
theorem readForms_of_annotate {d : Doc} {a : Annotated} (h : annotate d = some a) :
    readForms (d.items.map RoseTree.erase) = some a.definitions := by
  simp only [annotate, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨ds, hd, h⟩ := h
  split at h
  · cases Option.some.inj h
    exact hd
  · cases h

/-- Every returned correspondence has valid source and core addresses. -/
theorem valid_of_annotate {d : Doc} {a : Annotated} (h : annotate d = some a) :
    ∀ o ∈ a.correspondence, validOrigin a.source a.definitions o = true := by
  simp only [annotate, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨ds, _, h⟩ := h
  split at h
  · cases Option.some.inj h
    exact List.all_eq_true.mp (by assumption)
  · cases h

/-- Editing only the source decorations leaves the resolved core unchanged. -/
theorem definitions_eq_of_erase_eq {d e : Doc} {a b : Annotated}
    (ha : annotate d = some a) (hb : annotate e = some b)
    (h : d.items.map RoseTree.erase = e.items.map RoseTree.erase) :
    a.definitions = b.definitions := by
  have hd := readForms_of_annotate ha
  rw [h, readForms_of_annotate hb] at hd
  exact (Option.some.inj hd).symm

/-- The source spelling and trivia at a corresponding occurrence. The source address is kept
even when another occurrence has equal spelling or addresses the same core term. -/
structure Note where
  /-- The occurrence in the source document. -/
  source : List ℕ
  /-- The role of the occurrence at its core vertex. -/
  role : Role
  /-- The atom as written, when the source occurrence is an atom. -/
  spelling : Option (List Char)
  /-- The comments and empty lines at that occurrence. -/
  trivia : Trivia
  deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprNote.repr

/-- A correspondence's source information, without replacing a missing occurrence. -/
def noteOf (d : Doc) (o : Origin) : Option Note :=
  (atForest d.items o.source).map fun s ↦ ⟨o.source, o.role, s.label.2, s.label.1⟩

/-- The source notes of a core occurrence. A source occurrence contributes at most once per
entry of the correspondence, even when its term is equal to another term. -/
def Annotated.notesAt (a : Annotated) (core : List ℕ) : List Note :=
  (a.correspondence.filter (·.core == core)).filterMap (noteOf a.source)

/-- All source occurrences and their trivia, in preorder. -/
def triviaOf : SExpr → List (List ℕ × Trivia) :=
  RoseTree.elim fun l rs ↦ ([], l.1) :: Identity.underChildren 0 rs

/-- Comments and empty lines with no corresponding core vertex. The document's trailing
comments remain separately in its {lit}`trail` field. -/
def Annotated.unattached (a : Annotated) : List (List ℕ × Trivia) :=
  (Identity.underChildren 0 (a.source.items.map triviaOf)).filter fun (v, tr) ↦
    tr != Trivia.none && !a.correspondence.any (·.source == v)

/-- Source occurrences keyed by definition position and kernel vertex, in the form accepted by
{name}`Identity.rekey`. The source document is the one retained by this annotated bundle. -/
def Annotated.coreNotes (a : Annotated) : List ((ℕ × List ℕ) × (List ℕ × Role)) :=
  a.correspondence.map fun o ↦ ((o.core.headD 0, o.core.tail), (o.source, o.role))

/-- Source occurrences keyed by the definition's CID and kernel vertex. Equal payloads keep
separate entries for their source occurrences. -/
def Annotated.rekeyed (a : Annotated) : List ((List UInt8 × List ℕ) × (List ℕ × Role)) :=
  Identity.rekey ((Identity.migrate (a.definitions.map Prod.snd)).map Identity.Payload.cid)
    a.coreNotes

/-- Re-keying changes no source occurrence or role, and preserves their order and multiplicity. -/
theorem rekeyed_sources (a : Annotated) :
    a.rekeyed.map Prod.snd = a.correspondence.map (fun o ↦ (o.source, o.role)) := by
  simp only [Annotated.rekeyed, Identity.rekey, Annotated.coreNotes, List.map_map,
    Function.comp_def]

/-- A valid correspondence addresses a vertex of its definition. -/
theorem validKey_of_validOrigin {d : Doc} {ds : List (List Char × Tree)} {o : Origin}
    (h : validOrigin d ds o = true) :
    Identity.ValidKey (ds.map Prod.snd) (o.core.headD 0, o.core.tail) := by
  unfold validOrigin at h
  split at h
  next s t hs ht =>
    cases hp : o.core with
    | nil => simp [atForest, hp] at ht
    | cons i p =>
      simp only [atForest, hp, Option.bind_eq_some_iff] at ht
      obtain ⟨u, hu, hv⟩ := ht
      obtain ⟨hi, rfl⟩ := List.getElem?_eq_some_iff.mp hu
      have hk : Identity.ValidKey (ds.map Prod.snd) (i, p) := ⟨hi, by rw [hv]; rfl⟩
      simpa only [hp, List.headD_cons, List.tail_cons] using hk
  · cases h

/-- The existing content-identity migration preserves every returned annotation's address. -/
theorem valid_rekeyed {d : Doc} {a : Annotated} (h : annotate d = some a) :
    ∀ e ∈ a.rekeyed, ∃ p ∈ Identity.migrate (a.definitions.map Prod.snd),
      p.cid = e.1.1 ∧ (Identity.subtree? p.body e.1.2).isSome := by
  apply Identity.valid_rekey
  intro e he
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp he
  exact validKey_of_validOrigin (valid_of_annotate h o ho)

/-- The schema of a retained kernel source and its derived annotation table. -/
def schemaTag : List Char :=
  ['g', 'e', 'b', '-', 's', 'o', 'u', 'r', 'c', 'e', '-', 'a', 'n', 'n', '/', 'v', '1']

/-- A vertex written as a list of natural-number indices. -/
def pathSExp (p : List ℕ) : SExp := listOf (p.map numAtom)

/-- An annotation record's header: its schemas, source profile, exact named core, and the
source-to-core relation. The accompanying strict document carries every name and comment. -/
def Annotated.header (a : Annotated) : SExp :=
  listOf [atomOf schemaTag, atomOf Identity.profileTag, Profile.current.toSExp,
    listOf (a.definitions.map fun (n, t) ↦ listOf [atomOf n, Identity.termSExp t]),
    listOf (a.correspondence.map fun o ↦
      listOf [pathSExp o.source, pathSExp o.core,
        numAtom (match o.role with | .syntax => 0 | .binder => 1)])]

/-- An annotation record in the canonical encoding of the existing strict document format.
It keeps the original source rather than trying to reconstruct names from de Bruijn indices. -/
def Annotated.write (a : Annotated) : List Char := printCanonDoc a.header a.source

/-- Read a record by resolving its retained source again and comparing its complete header.
An unknown schema, changed core, or stale correspondence is rejected. -/
def read (text : List Char) : Option Annotated := do
  let (header, source) ← readStrictDoc text
  let a ← annotate source
  if header == a.header then some a else none

/-- An accepted source and its derived annotations survive canonical serialization exactly. -/
theorem read_write {d : Doc} {a : Annotated} (ha : annotate d = some a)
    (hw : a.source.strictWf a.header) : read a.write = some a := by
  have hs := source_of_annotate ha
  simp only [read, Annotated.write, readStrictDoc_printCanonDoc _ _ hw]
  change ((annotate a.source).bind fun b ↦ if a.header == b.header then some b else none) = some a
  rw [hs, ha]
  simp

/-- A record's checked core is the kernel reader's result on the retained source. -/
theorem readForms_of_read {text : List Char} {a : Annotated} (h : read text = some a) :
    readForms (a.source.items.map RoseTree.erase) = some a.definitions := by
  simp only [read, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨⟨header, source⟩, _, b, hb, h⟩ := h
  split at h
  · cases Option.some.inj h
    rw [source_of_annotate hb]
    exact readForms_of_annotate hb
  · cases h

end Geb.Kernel.SourceAnnotation

end
