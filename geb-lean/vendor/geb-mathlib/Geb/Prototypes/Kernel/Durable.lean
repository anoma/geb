/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Kernel.Strict

set_option doc.verso true

/-!
# Durable documents

A durable document is a source document ({name}`Geb.Kernel.Document.Doc`) with the profile that
fixes its reading: the syntax its S-expressions are written in, the schema of its annotations and
the format of its prose, each named and versioned separately, so that a later change of any of
them is a translation of documents that record which reading they were written for. The profile
is one form of the authoring profile,

```
(document (syntax authoring 0) (schema 0) (prose verso 0) (crit FIELD…) FIELD…)
```

whose fields after the third are optional and kept as they are read: the host reads none of them,
and a field the list headed by {lit}`crit` names is one the reader must read, so a document
requiring a field this host does not read is rejected, as the {lit}`crit` header parameter of
COSE (\[RFC9052\], § 3.1) and of JWS (\[RFC7515\], § 4.1.11) does. A program's sources
take their profile from its manifest; a document in a strict encoding carries its profile in the
form headed by {lit}`*doc`.

The annotations of the schema are, besides the comments the document holds, notes: forms
{lit}`(note FIELD…)` among the items of a document or of the body of a module, each documenting
the declaration after it. A field {lit}`(example TERM VALUE)` records a term and its value, and
a field {lit}`(link KIND TARGET)` a reference to the Geb definition or the Lean constant
{lit}`TARGET`, by {lit}`KIND` {lit}`geb` or {lit}`lean`; any other field, a list headed by an
atom, is kept as it is read. A note is erased before a program is compiled, since the readers of
the compilers read declarations alone; a source without notes is compiled as it is written.

The notes and the profile are S-expressions of the document, so the retractions of the source
documents and of the strict encodings carry them, with the names of declarations and binders and
the prose of comments, through reading, printing and conversion among the syntaxes: a durable
document is read back from its canonical encoding ({lit}`readStrictDurable_printCanonDurable`)
and from its advanced encoding ({lit}`readStrictDurable_printAdvancedDurable`), and a profile
({lit}`Profile.ofSExp?_toSExp`) and a note ({lit}`noteOf?_noteSExp`) are read back from the
forms that write them.

## Main definitions

* {lit}`Profile` — the profile of a document, and {lit}`Profile.check`, whether this host reads
  it.
* {lit}`Field`, {lit}`Note` — the fields of a note, and notes.
* {lit}`notesOf` — the notes of a document, each with the path of the declaration it documents.
* {lit}`erasedText` — a source's text without its notes, as the compilers read it.
* {lit}`Durable` — a document with its profile, and its strict encodings.

## Main statements

* {lit}`Profile.ofSExp?_toSExp`, {lit}`noteOf?_noteSExp` — profiles and notes read back.
* {lit}`readStrictDurable_printCanonDurable`, {lit}`readStrictDurable_printAdvancedDurable` —
  the retraction laws of the strict encodings of durable documents.

## References

* \[RFC9052\] — the {lit}`crit` header parameter of COSE.
* \[RFC7515\] — the {lit}`crit` header parameter of JWS.

## Tags

document, profile, version, annotation, note, retraction
-/

@[expose] public section

namespace Geb.Kernel.Document

/-! ## Atoms -/

/-- An atom spelling a number in decimal, in shortest form. -/
def numAtom (n : ℕ) : SExp := atomOf (Csexp.decOf n)

/-- The characters of an atom. -/
def nameOf? (t : SExp) : Option (List Char) :=
  match t.label, t.children with
  | some s, [] => some s
  | _, _ => none

/-- The number an atom spells in decimal, in shortest form. -/
def numOf? (t : SExp) : Option ℕ := (nameOf? t).bind decimal?

/-- The atom heading a list. -/
def headName? (t : SExp) : Option (List Char) :=
  match t.label, t.children with
  | none, h :: _ => nameOf? h
  | _, _ => none

/-- An atom's characters read back. -/
@[simp] theorem nameOf?_atomOf (s : List Char) : nameOf? (atomOf s) = some s := rfl

/-- A number read back. -/
@[simp] theorem numOf?_numAtom (n : ℕ) : numOf? (numAtom n) = some n := by
  simp [numOf?, numAtom, decimal?_decOf]

/-- The atom heading a list read back. -/
@[simp] theorem headName?_listOf (s : List Char) (cs : List SExp) :
    headName? (listOf (atomOf s :: cs)) = some s := by
  simp [headName?, listOf]

/-! ## Profiles -/

/-- The head of a profile, {lit}`document`. -/
def kwDocument : List Char := ['d', 'o', 'c', 'u', 'm', 'e', 'n', 't']

/-- The field of the syntax, {lit}`syntax`. -/
def kwSyntax : List Char := ['s', 'y', 'n', 't', 'a', 'x']

/-- The field of the schema of annotations, {lit}`schema`. -/
def kwSchema : List Char := ['s', 'c', 'h', 'e', 'm', 'a']

/-- The field of the format of prose, {lit}`prose`. -/
def kwProse : List Char := ['p', 'r', 'o', 's', 'e']

/-- The field of the fields a reader must read, {lit}`crit`. -/
def kwCrit : List Char := ['c', 'r', 'i', 't']

/-- The fields a profile's reader reads. -/
def knownFields : List (List Char) := [kwSyntax, kwSchema, kwProse, kwCrit]

/-- The profile of a document: the name and version of its syntax, the version of the schema of
its annotations, the name and version of the format of its prose, the fields a reader must read,
and the optional fields, kept as they are read. -/
@[ext] structure Profile where
  /-- The name of the syntax. -/
  syntaxName : List Char
  /-- The version of the syntax. -/
  syntaxVersion : ℕ
  /-- The version of the schema of annotations. -/
  schema : ℕ
  /-- The name of the format of prose. -/
  proseName : List Char
  /-- The version of the format of prose. -/
  proseVersion : ℕ
  /-- The fields a reader must read. -/
  crit : List (List Char)
  /-- The optional fields. -/
  extra : List SExp

namespace Profile

/-- The profile this host reads: the authoring profile's syntax, the schema of notes and prose in
the recorded subset of Verso's markup, each at version {lit}`0`, the pre-release version, which
changes with the compiler and whose documents are converted with it. -/
def current : Profile :=
  ⟨['a', 'u', 't', 'h', 'o', 'r', 'i', 'n', 'g'], 0, 0, ['v', 'e', 'r', 's', 'o'], 0, [], []⟩

/-- Whether a field is optional: a list headed by an atom other than the names of the fields a
profile's reader reads. -/
def isExtra (t : SExp) : Bool := (headName? t).any (!knownFields.contains ·)

/-- A profile as the form {lit}`(document …)`, the field of the fields a reader must read written
when it names one. -/
def toSExp (p : Profile) : SExp :=
  listOf (atomOf kwDocument ::
    listOf [atomOf kwSyntax, atomOf p.syntaxName, numAtom p.syntaxVersion] ::
    listOf [atomOf kwSchema, numAtom p.schema] ::
    listOf [atomOf kwProse, atomOf p.proseName, numAtom p.proseVersion] ::
    ((if p.crit.isEmpty then [] else [listOf (atomOf kwCrit :: p.crit.map atomOf)]) ++ p.extra))

/-- Whether a profile is written as a form and read back: its optional fields are optional. -/
def wf (p : Profile) : Bool := p.extra.all isExtra

/-- A field of a name and a version, headed by a keyword. -/
def namedOf? (k : List Char) (t : SExp) : Option (List Char × ℕ) :=
  match t.label, t.children with
  | none, [h, n, v] => if nameOf? h == some k then do return (← nameOf? n, ← numOf? v) else none
  | _, _ => none

/-- A field of a version, headed by a keyword. -/
def versionOf? (k : List Char) (t : SExp) : Option ℕ :=
  match t.label, t.children with
  | none, [h, v] => if nameOf? h == some k then numOf? v else none
  | _, _ => none

/-- The field of the fields a reader must read. -/
def critOf? (t : SExp) : Option (List (List Char)) :=
  match t.label, t.children with
  | none, h :: ns => if nameOf? h == some kwCrit then ns.mapM nameOf? else none
  | _, _ => none

/-- The fields a reader must read and the optional fields, from the fields after the third. -/
def restOf? (ts : List SExp) : Option (List (List Char) × List SExp) :=
  match ts with
  | t :: rest =>
    match critOf? t with
    | some cs => if rest.all isExtra then some (cs, rest) else none
    | none => if ts.all isExtra then some ([], ts) else none
  | [] => some ([], [])

/-- The profile a form writes. -/
def ofSExp? (t : SExp) : Option Profile :=
  match t.label, t.children with
  | none, h :: sy :: sc :: pr :: rest =>
    if nameOf? h == some kwDocument then do
      let (sn, sv) ← namedOf? kwSyntax sy
      let (pn, pv) ← namedOf? kwProse pr
      let (cs, ex) ← restOf? rest
      return ⟨sn, sv, ← versionOf? kwSchema sc, pn, pv, cs, ex⟩
    else none
  | _, _ => none

/-- An optional field is not the field of the fields a reader must read. -/
theorem critOf?_of_isExtra {t : SExp} (h : isExtra t) : critOf? t = none := by
  unfold isExtra headName? at h
  unfold critOf?
  split
  · rename_i hd ns hl hc
    simp only [hl, hc] at h
    cases hn : nameOf? hd with
    | none => simp
    | some s =>
      rw [hn] at h
      have : s ≠ kwCrit := fun hs ↦ by simp [hs, knownFields] at h
      simp [this]
  · rfl

/-- A well-formed profile is read back from its form. -/
theorem ofSExp?_toSExp (p : Profile) (h : p.wf) : ofSExp? p.toSExp = some p := by
  have hrest : restOf? ((if p.crit.isEmpty then [] else [listOf (atomOf kwCrit :: p.crit.map
      atomOf)]) ++ p.extra) = some (p.crit, p.extra) := by
    cases hc : p.crit with
    | nil =>
      cases he : p.extra with
      | nil => rfl
      | cons t ts =>
        have hw : (t :: ts).all isExtra := he ▸ h
        simp only [List.isEmpty_nil, ↓reduceIte, List.nil_append, restOf?,
          critOf?_of_isExtra (List.all_eq_true.mp hw t List.mem_cons_self), hw]
    | cons c cs =>
      simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.cons_append,
        List.nil_append, restOf?, critOf?, listOf, RoseTree.label_node, RoseTree.children_node,
        nameOf?_atomOf, beq_self_eq_true, show p.extra.all isExtra = true from h,
        mapM_map_of nameOf? atomOf (c :: cs) fun x _ ↦ nameOf?_atomOf x]
  simp only [listOf] at hrest
  simp only [toSExp, ofSExp?, listOf, RoseTree.label_node, RoseTree.children_node,
    nameOf?_atomOf, namedOf?, versionOf?, numOf?_numAtom, beq_self_eq_true, ↓reduceIte, hrest]
  rfl

/-- Whether this host reads a profile: its syntax is the authoring profile's, its schema and the
format of its prose are this host's, each at this host's version, and it requires no field this
host does not read. -/
def check (p : Profile) : Except String Unit := do
  let c := current
  unless p.syntaxName == c.syntaxName && p.syntaxVersion == c.syntaxVersion do
    throw s!"the syntax {String.ofList p.syntaxName} {p.syntaxVersion} is not this host's \
      {String.ofList c.syntaxName} {c.syntaxVersion}"
  unless p.schema == c.schema do
    throw s!"the schema {p.schema} is not this host's schema {c.schema}"
  unless p.proseName == c.proseName && p.proseVersion == c.proseVersion do
    throw s!"the prose {String.ofList p.proseName} {p.proseVersion} is not this host's \
      {String.ofList c.proseName} {c.proseVersion}"
  if let some f := p.crit.find? (![kwSyntax, kwSchema, kwProse].contains ·) then
    throw s!"the document requires the field {String.ofList f}, which this host does not read"

/-- The profile a form writes, when this host reads it, or what rejects it. -/
def parse (t : SExp) : Except String Profile := do
  let some p := ofSExp? t
    | throw "a profile is (document (syntax NAME N) (schema N) (prose NAME N) FIELD…), \
        each further field a list headed by an atom"
  p.check
  return p

end Profile

/-! ## Notes -/

/-- The head of a note, {lit}`note`. -/
def kwNote : List Char := ['n', 'o', 't', 'e']

/-- The field of an example, {lit}`example`. -/
def kwExample : List Char := ['e', 'x', 'a', 'm', 'p', 'l', 'e']

/-- The field of a link, {lit}`link`. -/
def kwLink : List Char := ['l', 'i', 'n', 'k']

/-- The kinds of links: to a Geb definition, {lit}`geb`, and to a Lean constant, {lit}`lean`. -/
def linkKinds : List (List Char) := [['g', 'e', 'b'], ['l', 'e', 'a', 'n']]

/-- A field of a note: an example, of a term and its value; a link, of its kind and target; or
another field, kept as it is read. -/
inductive Field where
  /-- An example: a term and its value. -/
  | example (term value : SExp)
  /-- A link: its kind and its target. -/
  | link (kind target : List Char)
  /-- A field of the schema's later versions, or of none, kept as it is read. -/
  | other (t : SExp)

/-- A note: its fields, in order. -/
abbrev Note : Type := List Field

/-- A field as the form that writes it. -/
def Field.toSExp : Field → SExp
  | .example a b => listOf [atomOf kwExample, a, b]
  | .link k x => listOf [atomOf kwLink, atomOf k, atomOf x]
  | .other t => t

/-- Whether a field is written as a form and read back: a link's kind is one of the kinds, and
another field is a list headed by an atom other than {lit}`example` and {lit}`link`. -/
def Field.wf : Field → Bool
  | .example _ _ => true
  | .link k _ => linkKinds.contains k
  | .other t => (headName? t).any fun k ↦ k != kwExample && k != kwLink

/-- The field a form writes. -/
def fieldOf? (t : SExp) : Option Field :=
  (headName? t).bind fun k ↦
    if k == kwExample then
      match t.children with
      | [_, a, b] => some (.example a b)
      | _ => none
    else if k == kwLink then
      match t.children with
      | [_, kd, x] => do
        let kd ← nameOf? kd
        if linkKinds.contains kd then return .link kd (← nameOf? x) else none
      | _ => none
    else some (.other t)

/-- A note as the form that writes it. -/
def noteSExp (n : Note) : SExp := listOf (atomOf kwNote :: n.map Field.toSExp)

/-- The note a form writes. -/
def noteOf? (t : SExp) : Option Note :=
  match t.label, t.children with
  | none, h :: fs => if nameOf? h == some kwNote then fs.mapM fieldOf? else none
  | _, _ => none

/-- A well-formed field is read back from its form. -/
theorem fieldOf?_toSExp (f : Field) (h : f.wf) : fieldOf? f.toSExp = some f := by
  cases f with
  | «example» a b => rfl
  | link k x =>
    have hk : k ∈ linkKinds := by simpa [Field.wf] using h
    simp only [Field.toSExp, fieldOf?, headName?_listOf, Option.bind_some]
    simp [kwExample, kwLink, listOf, hk]
  | other t =>
    simp only [Field.wf, Option.any_eq_true, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
    obtain ⟨k, hk, hx, hl⟩ := h
    simp [fieldOf?, Field.toSExp, hk, hx, hl]

/-- A note of well-formed fields is read back from its form. -/
theorem noteOf?_noteSExp (n : Note) (h : n.all Field.wf) : noteOf? (noteSExp n) = some n := by
  simp only [noteOf?, noteSExp, listOf, RoseTree.label_node, RoseTree.children_node,
    nameOf?_atomOf, List.mapM_map]
  exact mapM_eq_some _ id n (fun f hf ↦ by
    simpa using fieldOf?_toSExp f (List.all_eq_true.mp h f hf)) |>.trans (by rw [List.map_id])

/-! ## The notes of a document -/

/-- Whether an S-expression with comments is a given atom. -/
def atomIs (k : List Char) (t : SExpr) : Bool := t.label.2 == some k && t.children.isEmpty

/-- Whether an S-expression with comments is a list headed by a given atom. -/
def headIs (k : List Char) (t : SExpr) : Bool :=
  t.label.2 == none && t.children.head?.any (atomIs k)

/-- The head of a module, {lit}`module`. -/
def kwModule : List Char := ['m', 'o', 'd', 'u', 'l', 'e']

/-- The heads of declarations, which a note documents: of definitions, of abbreviations, of
datatypes and of modules. -/
def declHeads : List (List Char) :=
  [['d', 'e', 'f'], ['d', 'e', 'f', 'n'], ['d', 'e', 'f', 't', 'y', 'p', 'e'],
    ['d', 'e', 'f', 'n', 'u', 'm'], ['d', 'a', 't', 'a'],
    ['t', 'r', 'e', 'e', '-', 'd', 'a', 't', 'a'], kwModule]

/-- Whether an S-expression with comments is a note. -/
def isNote (t : SExpr) : Bool := headIs kwNote t

/-- Whether an S-expression with comments is a declaration. -/
def isDecl (t : SExpr) : Bool := declHeads.any (headIs · t)

/-- The name of a declaration, its second element. -/
def declName? (t : SExpr) : Option (List Char) :=
  t.children[1]?.bind fun x ↦ if x.children.isEmpty then x.label.2 else none

/-- The path of a declaration: the names of the modules enclosing it, outermost first, and its
own. -/
abbrev Path : Type := List (List Char)

/-- The notes of a block's items, each item with the notes inside it, each note with the path of
the declaration it documents, under the path of the block, or what rejects them: a note that is
not well formed, or that no declaration follows. -/
def blockNotes (pre : Path) (rs : List (SExpr × Except String (List (Path × Note)))) :
    Except String (List (Path × Note)) := do
  let parts ← (rs.zip ((rs.drop 1).map some ++ [none])).mapM fun ((c, r), next) ↦
    if isNote c then
      match next with
      | some (d, _) =>
        if isDecl d then
          match declName? d, noteOf? (RoseTree.erase c) with
          | some n, some note => pure [(pre ++ [n], note)]
          | none, _ => throw "a note documents a declaration without a name"
          | _, none => throw "a note is not (note FIELD…), each field a list headed by an atom, \
              an example of a term and its value, or a link of kind geb or lean to a name"
        else throw "a note documents no declaration"
      | none => throw "a note documents no declaration"
    else r.map (·.map fun (p, n) ↦ (pre ++ p, n))
  return parts.flatten

/-- One node's notes, from its children's, when the node is an item of a block: a module's are
those of its body, under its name, and any other node's none. -/
def notesStep (l : Trivia × Option (List Char))
    (rs : List (SExpr × Except String (List (Path × Note)))) :
    Except String (List (Path × Note)) :=
  match l.2, rs with
  | none, (k, _) :: (m, _) :: forms =>
    match declName? (RoseTree.node l (rs.map Prod.fst)) with
    | some name => if atomIs kwModule k && m.children.isEmpty then blockNotes [name] forms
      else pure []
    | none => pure []
  | _, _ => pure []

/-- The notes of a document, each with the path of the declaration it documents, or what rejects
them. -/
def notesOf (d : Doc) : Except String (List (Path × Note)) :=
  blockNotes [] (d.items.map fun t ↦ (t, RoseTree.para notesStep t))

/-- One node without the notes of its blocks, from its children with theirs: a module's body
without its notes, and any other node as it is. -/
def eraseStep (l : Trivia × Option (List Char)) (rs : List (SExpr × SExpr)) : SExpr :=
  match l.2, rs with
  | none, (k, _) :: _ =>
    if atomIs kwModule k then RoseTree.node l ((rs.filter fun r ↦ !isNote r.1).map Prod.snd)
    else RoseTree.node l (rs.map Prod.fst)
  | _, _ => RoseTree.node l (rs.map Prod.fst)

/-- A document without its notes, the comments before and inside each erased with it. -/
def Doc.eraseNotes (d : Doc) : Doc :=
  ⟨(d.items.filter (!isNote ·)).map (RoseTree.para eraseStep), d.trail⟩

/-- A source's text as the compilers read it, or what rejects its notes: nothing when it holds
no note, so that it is compiled as it is written, and otherwise its document without its notes,
printed as the formatter prints. A text that does not read is left to the compilers' readers,
which name what rejects it. -/
def erasedText (text : List Char) : Except String (Option (List Char)) :=
  match readDoc text with
  | none => pure none
  | some d => do
    if (← notesOf d).isEmpty then return none
    let e := d.eraseNotes
    return some (printAt (defaultLayout .profile 100 e) e)

/-! ## Durable documents and the strict encodings -/

/-- A durable document: a source document and its profile. -/
@[ext] structure Durable where
  /-- The profile. -/
  profile : Profile
  /-- The document. -/
  doc : Doc

namespace Durable

/-- Whether a durable document is written in a strict encoding and read back: its profile is
written as a form and read back, and its document is written in strict form, under that form,
and read back. -/
def wf (D : Durable) : Bool := D.profile.wf && D.doc.strictWf D.profile.toSExp

end Durable

/-- A durable document in the canonical encoding. -/
def printCanonDurable (D : Durable) : List Char := printCanonDoc D.profile.toSExp D.doc

/-- A durable document in the advanced encoding, within a line width. -/
def printAdvancedDurable (lim : ℕ) (D : Durable) : List Char :=
  printAdvancedDoc lim D.profile.toSExp D.doc

/-- A durable document read from a strict encoding. -/
def readStrictDurable (text : List Char) : Option Durable :=
  (readStrictDoc text).bind fun (h, d) ↦ (Profile.ofSExp? h).map (⟨·, d⟩)

/-- A durable document read from the basic transport encoding. -/
def readBasicDurable (text : List Char) : Option Durable :=
  (readBasic text).bind fun (h, d) ↦ (Profile.ofSExp? h).map (⟨·, d⟩)

/-- The retraction law of the canonical encoding of durable documents. -/
theorem readStrictDurable_printCanonDurable (D : Durable) (h : D.wf) :
    readStrictDurable (printCanonDurable D) = some D := by
  rw [Durable.wf, Bool.and_eq_true] at h
  rw [readStrictDurable, printCanonDurable, readStrictDoc_printCanonDoc _ _ h.2, Option.bind_some]
  simp [Profile.ofSExp?_toSExp _ h.1]

/-- The retraction law of the advanced encoding of durable documents. -/
theorem readStrictDurable_printAdvancedDurable (lim : ℕ) (D : Durable) (h : D.wf) :
    readStrictDurable (printAdvancedDurable lim D) = some D := by
  rw [Durable.wf, Bool.and_eq_true] at h
  rw [readStrictDurable, printAdvancedDurable, readStrictDoc_printAdvancedDoc _ _ _ h.2,
    Option.bind_some]
  simp [Profile.ofSExp?_toSExp _ h.1]

end Geb.Kernel.Document

end
