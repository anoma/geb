/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Kernel.Document

set_option doc.verso true

/-!
# The strict encodings

The syntaxes of \[RFC9804\] that the authoring profile extends, read by the profile's reader
({name}`Geb.Kernel.Document.readDoc`), whose spellings of atoms include theirs. The canonical
encoding writes each atom verbatim, its length in decimal before a colon and its bytes, and a
list in parentheses, with no whitespace: it is the encoding a definition's identifier hashes,
and every S-expression is read back from it ({lit}`readDoc_canonOf`).

A strict encoding has no comments, so a source document is written in one as a single
S-expression ({lit}`toStrict`): its S-expressions, each node with trivia written as an
annotation form {lit}`(*ann node lead gap close)` in its place, its comment lines as lists of
a flag of an empty line and the line's characters, inside a list headed by {lit}`*doc` with the
comment lines after the last S-expression. A document no list of which is headed by
{lit}`*ann`, and whose characters are bytes, as every document read is, is read back from that
form ({lit}`fromStrictDoc_toStrict`), and so from its canonical encoding
({lit}`readStrictDoc_printCanonDoc`). The basic transport encoding is the
canonical one or the base-64 encoding of it between braces; its printer writes the first. The
advanced encoding writes the same tokens laid out as the formatter lays out source, a token bare
and every other atom quoted with escapes of ASCII alone ({lit}`advancedOf`); its text is ASCII
and reads back to the document ({lit}`readStrictDoc_printAdvancedDoc`).

## Main definitions

* {lit}`verbatim`, {lit}`canonOf` — the canonical encoding of an atom and of an S-expression.
* {lit}`toStrict`, {lit}`fromStrict` — a document as one S-expression and back.
* {lit}`printCanonDoc`, {lit}`readStrictDoc` — a document in the canonical encoding, and a
  document read from a strict encoding.
* {lit}`readBasic` — a document in the basic transport encoding.
* {lit}`advancedOf`, {lit}`printAdvancedDoc` — an S-expression and a document in the advanced
  encoding.

## Main statements

* {lit}`readDoc_canonOf` — the canonical encoding of an S-expression reads back to it.
* {lit}`fromStrictDoc_toStrict` — the strict form of a document reads back to it.
* {lit}`readStrictDoc_printCanonDoc` — the retraction law of the canonical encoding of
  documents.
* {lit}`readStrictDoc_printAdvancedDoc` — the retraction law of the advanced encoding of
  documents.

## References

* \[RFC9804\] — the canonical, basic transport and advanced encodings.
* \[RFC4648\] — base 64.

## Tags

S-expression, RFC 9804, canonical encoding, retraction
-/

@[expose] public section

namespace Geb.Kernel.Document

/-! ## The canonical encoding -/

/-- An atom in the canonical encoding: its length in decimal, a colon and its bytes. -/
def verbatim (s : List Char) : List Char := Csexp.decOf s.length ++ ':' :: s

/-- The tokens of an S-expression in the canonical encoding, none after an empty line. -/
def canonToks : SExp → List Tok :=
  RoseTree.elim fun a rs ↦
    match a with
    | some s => [.atom false s]
    | none => .lp false :: rs.flatten ++ [.rp]

/-- A token's characters in the canonical encoding. -/
def Tok.renderCanon : Tok → List Char
  | .lp _ => ['(']
  | .rp => [')']
  | .atom _ s => verbatim s
  | _ => []

/-- An S-expression in the canonical encoding: atoms verbatim and lists in parentheses, with no
whitespace. -/
def canonOf (t : SExp) : List Char := (canonToks t).flatMap Tok.renderCanon

/-- Whether every character of an S-expression's atoms is a byte. -/
def SExp.bytes : SExp → Bool :=
  RoseTree.elim fun a rs ↦ (a.all fun s ↦ s.all isByte) && rs.all id

/-- Whether an S-expression is well formed: an atom has no children. -/
def SExp.wf : SExp → Bool :=
  RoseTree.elim fun a rs ↦
    match a with
    | some _ => rs.isEmpty
    | none => rs.all id

/-- A well-formed list's elements are well formed. -/
theorem SExp.wf_list (cs : List SExp) : SExp.wf (RoseTree.node none cs) = cs.all SExp.wf := by
  simp [SExp.wf, List.all_map]

/-- A well-formed atom has no children. -/
theorem SExp.wf_atom (s : List Char) (cs : List SExp) :
    SExp.wf (RoseTree.node (some s) cs) = cs.isEmpty := by
  simp [SExp.wf]

/-- A digit of a decimal spelling is a digit. -/
theorem isDigit_of_charDigit {c : Char} (h : (Csexp.charDigit c).isSome) : isDigit c := by
  unfold Csexp.charDigit at h
  split at h
  next hc => exact hc
  next => simp at h

/-- The value of a decimal spelling in shortest form. -/
theorem decimal?_decOf (n : ℕ) : decimal? (Csexp.decOf n) = some n := by
  simp [decimal?, Csexp.digitsVal_decOf]

/-- The bytes of a verbatim atom extend it until the last, which ends it. -/
theorem foldl_verbatimChars (d : List Tok) (g : Bool) :
    ∀ (cs b : List Char), cs ≠ [] →
      cs.foldl lexStep ⟨d, b, .verbatim cs.length, 0, g, true⟩ =
        .idle (.atom g (cs.reverse ++ b).reverse :: d) 0 :=
  fun cs ↦ List.rec (motive := fun cs ↦ ∀ b : List Char, cs ≠ [] →
      cs.foldl lexStep ⟨d, b, .verbatim cs.length, 0, g, true⟩ =
        .idle (.atom g (cs.reverse ++ b).reverse :: d) 0)
    (fun _ h ↦ absurd rfl h)
    (fun c cs ih b _ ↦ by
      cases cs with
      | nil =>
        change lexStep ⟨d, b, .verbatim 1, 0, g, true⟩ c = _
        simp [lexStep]
      | cons c' cs' =>
        have hstep : lexStep ⟨d, b, .verbatim (c :: c' :: cs').length, 0, g, true⟩ c =
            ⟨d, c :: b, .verbatim (c' :: cs').length, 0, g, true⟩ := by
          simp [lexStep]
        rw [List.foldl_cons, hstep, ih (c :: b) (List.cons_ne_nil c' cs')]
        simp) cs

/-- A canonical token read between tokens is emitted. -/
theorem foldl_renderCanon (t : Tok) (ht : t = .lp false ∨ t = .rp ∨ ∃ s, t = .atom false s)
    (d : List Tok) : t.renderCanon.foldl lexStep (.idle d 0) = .idle (t :: d) 0 := by
  rcases ht with rfl | rfl | ⟨s, rfl⟩
  · rfl
  · rfl
  · obtain ⟨c, cs, hdec⟩ : ∃ c cs, Csexp.decOf s.length = c :: cs := by
      cases h : Csexp.decOf s.length with
      | nil => exact absurd h (Csexp.decOf_ne_nil _)
      | cons c cs => exact ⟨c, cs, rfl⟩
    have hdig := Csexp.decOf_all_digits s.length
    rw [hdec] at hdig
    have hc : isDigit c := isDigit_of_charDigit (hdig c List.mem_cons_self)
    have hcs : cs.all isDigit :=
      List.all_eq_true.mpr fun x hx ↦ isDigit_of_charDigit (hdig x (List.mem_cons_of_mem c hx))
    have hlen : decimal? (c :: cs) = some s.length := by rw [← hdec]; exact decimal?_decOf _
    simp only [Tok.renderCanon, verbatim, hdec, List.cons_append, List.foldl_cons,
      List.foldl_append]
    rw [show lexStep (.idle d 0) c = idleStep d 0 c from rfl, idleStep_digit d 0 hc,
      foldl_numChars cs hcs]
    have hcolon : lexStep ⟨d, cs.reverse ++ [c], .numeral, 0, decide (2 ≤ 0), true⟩ ':' =
        lengthStep ⟨d, cs.reverse ++ [c], .numeral, 0, decide (2 ≤ 0), true⟩ ':' := rfl
    rw [hcolon]
    unfold lengthStep
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.reverse_reverse, List.singleton_append, hlen]
    cases s with
    | nil => rfl
    | cons x xs =>
      simp only [List.length_cons, Nat.add_one_ne_zero, beq_iff_eq, ↓reduceIte]
      refine (foldl_verbatimChars d _ (x :: xs) [] (List.cons_ne_nil x xs)).trans ?_
      simp

/-- Canonical tokens read between tokens are emitted in order. -/
theorem foldl_renderCanons (toks : List Tok)
    (h : ∀ t ∈ toks, t = .lp false ∨ t = .rp ∨ ∃ s, t = .atom false s) :
    ∀ d, (toks.flatMap Tok.renderCanon).foldl lexStep (.idle d 0) = .idle (toks.reverse ++ d) 0 :=
  List.rec (motive := fun toks ↦ (∀ t ∈ toks, t = .lp false ∨ t = .rp ∨
      ∃ s, t = .atom false s) → ∀ d, (toks.flatMap Tok.renderCanon).foldl lexStep (.idle d 0) =
        .idle (toks.reverse ++ d) 0)
    (fun _ _ ↦ rfl)
    (fun t ts ih h d ↦ by
      rw [List.flatMap_cons, List.foldl_append,
        foldl_renderCanon t (h t List.mem_cons_self) d,
        ih (fun x hx ↦ h x (List.mem_cons_of_mem t hx)) (t :: d)]
      simp) toks h

/-- The canonical tokens of an S-expression are parentheses and atoms after no empty line. -/
theorem canonToks_kinds : ∀ t : SExp, ∀ x ∈ canonToks t,
    x = .lp false ∨ x = .rp ∨ ∃ s, x = .atom false s :=
  RoseTree.ind fun a cs ih x hx ↦ by
    cases a with
    | some s =>
      simp only [canonToks, RoseTree.elim_node, List.mem_singleton] at hx
      exact Or.inr (Or.inr ⟨s, hx⟩)
    | none =>
      simp only [canonToks, RoseTree.elim_node, List.cons_append, List.mem_cons, List.mem_append,
        List.mem_flatten, List.mem_map, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | ⟨⟨_, ⟨c, hc, rfl⟩, hx⟩ | rfl⟩
      · exact Or.inl rfl
      · exact ih c hc x hx
      · exact Or.inr (Or.inl rfl)

/-- The canonical tokens of an S-expression of bytes are well formed. -/
theorem canonToks_wf : ∀ t : SExp, SExp.bytes t → ∀ x ∈ canonToks t, x.wf :=
  RoseTree.ind fun a cs ih hb x hx ↦ by
    simp only [SExp.bytes, RoseTree.elim_node, Bool.and_eq_true] at hb
    cases a with
    | some s =>
      simp only [canonToks, RoseTree.elim_node, List.mem_singleton] at hx
      subst hx
      exact hb.1
    | none =>
      simp only [canonToks, RoseTree.elim_node, List.cons_append, List.mem_cons, List.mem_append,
        List.mem_flatten, List.mem_map, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | ⟨⟨_, ⟨c, hc, rfl⟩, hx⟩ | rfl⟩
      · rfl
      · simp only [List.all_map, List.all_eq_true, Function.comp_apply, id] at hb
        exact ih c hc (hb.2 c hc) x hx
      · rfl

/-- A digit is a byte. -/
theorem isByte_of_isDigit {c : Char} (h : isDigit c) : isByte c := by
  unfold isDigit at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact decide_eq_true (by omega)

/-- The canonical encoding of an S-expression of bytes is of bytes. -/
theorem canonOf_bytes (t : SExp) (hb : SExp.bytes t) : (canonOf t).all isByte := by
  rw [canonOf, List.all_flatMap]
  refine List.all_eq_true.mpr fun x hx ↦ ?_
  rcases canonToks_kinds t x hx with rfl | rfl | ⟨s, rfl⟩
  · rfl
  · rfl
  · have hs : s.all isByte := canonToks_wf t hb _ hx
    rw [Tok.renderCanon, verbatim, List.all_append, List.all_cons, hs,
      List.all_eq_true.mpr fun c hc ↦ isByte_of_isDigit (isDigit_of_charDigit
        (Csexp.decOf_all_digits s.length c hc))]
    rfl

/-- The lexer reads the canonical encoding of an S-expression of bytes to its canonical
tokens. -/
theorem lex_canonOf (t : SExp) (hb : SExp.bytes t) : lex (canonOf t) = some (canonToks t) := by
  rw [lex_of_bytes (canonOf_bytes t hb), canonOf, show (LexState.init) = .idle [] 0 from rfl,
    foldl_renderCanons _ (canonToks_kinds t) []]
  simp [lexEnd, LexState.idle]

/-- An S-expression decorated with no trivia. -/
def plain (t : SExp) : SExpr := RoseTree.map (fun a ↦ (Trivia.none, a)) t

/-- Erasing the decorations of a plain S-expression gives it back. -/
theorem erase_plain (t : SExp) : RoseTree.erase (plain t) = t := by
  simp only [RoseTree.erase, plain, RoseTree.map_map]
  exact RoseTree.map_id t

/-- Reading the canonical tokens of a well-formed S-expression onto a frame with no pending lines
adds the plain S-expression to it. -/
theorem foldl_readStep_canonToks : ∀ t : SExp, SExp.wf t → ∀ (f : Frame) fs, f.pend = [] →
    (canonToks t).foldl readStep (some (f :: fs)) = some (f.push (plain t) :: fs) :=
  RoseTree.ind fun a cs ih ht f fs hf ↦ by
    cases a with
    | some s =>
      rw [SExp.wf_atom, List.isEmpty_iff] at ht
      subst ht
      simp [canonToks, readStep, hf, Frame.push, plain, Trivia.none]
    | none =>
      rw [SExp.wf_list, List.all_eq_true] at ht
      have hitems : ∀ (cs' : List SExp), (∀ c ∈ cs', c ∈ cs) → ∀ (g : Frame) gs, g.pend = [] →
          (cs'.map canonToks).flatten.foldl readStep (some (g :: gs)) =
            some (⟨g.lead, g.gap, (cs'.map plain).reverse ++ g.items, []⟩ :: gs) :=
        fun cs' ↦ List.rec (motive := fun cs' ↦ (∀ c ∈ cs', c ∈ cs) → ∀ (g : Frame) gs,
            g.pend = [] → (cs'.map canonToks).flatten.foldl readStep (some (g :: gs)) =
              some (⟨g.lead, g.gap, (cs'.map plain).reverse ++ g.items, []⟩ :: gs))
          (fun _ g gs hg ↦ by
            obtain ⟨_, _, _, _⟩ := g
            simp only at hg
            subst hg
            rfl)
          (fun c cs' ihc hsub g gs hg ↦ by
            have hc := hsub c List.mem_cons_self
            rw [List.map_cons, List.flatten_cons, List.foldl_append, ih c hc (ht c hc) g gs hg,
              ihc (fun x hx ↦ hsub x (List.mem_cons_of_mem c hx)) _ gs rfl]
            simp [Frame.push]) cs'
      have hl : canonToks (RoseTree.node none cs) =
          .lp false :: ((cs.map canonToks).flatten ++ [.rp]) := by
        simp [canonToks]
      have hlp : readStep (some (f :: fs)) (.lp false) =
          some (Frame.start [] false :: { f with pend := [] } :: fs) := by
        simp [readStep, hf]
      rw [hl, List.foldl_cons, List.foldl_append, hlp,
        hitems cs (fun _ hx ↦ hx) (Frame.start [] false) _ rfl]
      simp only [List.foldl_cons, List.foldl_nil, readStep, Frame.start, Frame.push,
        List.append_nil, List.reverse_reverse, plain, RoseTree.map_node, Trivia.none,
        List.reverse_nil]
      rfl

/-- The canonical encoding of a well-formed S-expression of bytes reads back to it, as a document
of that S-expression alone, without trivia. -/
theorem readDoc_canonOf (t : SExp) (ht : SExp.wf t) (hb : SExp.bytes t) :
    readDoc (canonOf t) = some ⟨[plain t], []⟩ := by
  rw [readDoc, lex_canonOf t hb, Option.bind_some, foldl_readStep_canonToks t ht _ [] rfl]
  simp [Frame.start, Frame.push]

/-! ## Documents in a strict encoding -/

/-- An atom of characters. -/
def atomOf (s : List Char) : SExp := RoseTree.node (some s) []

/-- A list of S-expressions. -/
def listOf (cs : List SExp) : SExp := RoseTree.node none cs

/-- The reserved head of an annotation form, {lit}`*ann`. -/
def kwAnn : List Char := ['*', 'a', 'n', 'n']

/-- The reserved head of a document in a strict encoding, {lit}`*doc`. -/
def kwDoc : List Char := ['*', 'd', 'o', 'c']

/-- The atom of a flag of an empty line: {lit}`1` when one precedes, {lit}`0` otherwise. -/
def gapAtom (g : Bool) : SExp := atomOf (if g then ['1'] else ['0'])

/-- A comment line as a list of the flag of an empty line before it and its characters. -/
def lineSExp (l : Line) : SExp := listOf [gapAtom l.gap, atomOf l.text]

/-- Comment lines as a list. -/
def linesSExp (ls : List Line) : SExp := listOf (ls.map lineSExp)

/-- An S-expression with comments in strict form: a node without trivia is written as itself,
and a node with trivia as the annotation form {lit}`(*ann node lead gap close)` of the node
without them. -/
def strictOf : SExpr → SExp :=
  RoseTree.elim fun l rs ↦
    if l.1 == Trivia.none then RoseTree.node l.2 rs
    else listOf [atomOf kwAnn, RoseTree.node l.2 rs, linesSExp l.1.lead, gapAtom l.1.gap,
      linesSExp l.1.close]

/-- A document in strict form: a list headed by {lit}`*doc` of the comment lines after the last
S-expression and the S-expressions. -/
def toStrict (d : Doc) : SExp := listOf (atomOf kwDoc :: linesSExp d.trail :: d.items.map strictOf)

/-- The flag of an empty line an atom spells. -/
def gapOf? (t : SExp) : Option Bool :=
  match t.label, t.children with
  | some ['0'], [] => some false
  | some ['1'], [] => some true
  | _, _ => none

/-- The comment line a list of a flag and an atom spells. -/
def lineOf? (t : SExp) : Option Line :=
  match t.label, t.children with
  | none, [g, x] =>
    match gapOf? g, x.label, x.children with
    | some b, some s, [] => some ⟨b, s⟩
    | _, _, _ => none
  | _, _ => none

/-- The comment lines a list spells. -/
def linesOf? (t : SExp) : Option (List Line) :=
  match t.label with
  | none => t.children.mapM lineOf?
  | some _ => none

/-- Whether an S-expression is the atom {lit}`*ann`. -/
def isAnnHead (t : SExp) : Bool := t.label == some kwAnn && t.children.isEmpty

/-- One node of an S-expression read from strict form, from its children with their readings:
an annotation form is its node decorated with the trivia it spells, and any other node is
itself without trivia. -/
def fromStrictStep (a : Option (List Char)) (rs : List (SExp × Option SExpr)) : Option SExpr :=
  let plainNode := (rs.mapM Prod.snd).map (RoseTree.node (Trivia.none, a))
  match a, rs with
  | none, [(h, _), (_, some core), (lead, _), (gap, _), (close, _)] =>
    if isAnnHead h then
      match linesOf? lead, gapOf? gap, linesOf? close with
      | some ls, some g, some cl => some (RoseTree.node (⟨ls, g, cl⟩, core.label.2) core.children)
      | _, _, _ => none
    else plainNode
  | _, _ => plainNode

/-- An S-expression read from strict form. -/
def fromStrict : SExp → Option SExpr := RoseTree.para fromStrictStep

/-- A document read from strict form. -/
def fromStrictDoc (t : SExp) : Option Doc :=
  match t.label, t.children with
  | none, h :: tr :: items =>
    if h.label == some kwDoc && h.children.isEmpty then do
      some ⟨← items.mapM fromStrict, ← linesOf? tr⟩
    else none
  | _, _ => none

/-- Whether an S-expression with comments can be written in strict form and read back: an atom
has no children, and no list's first element is the atom {lit}`*ann` without trivia. -/
def strictWf : SExpr → Bool :=
  RoseTree.para fun l rs ↦
    rs.all (·.2) &&
      match l.2 with
      | some _ => rs.isEmpty
      | none => !(rs.head?.any fun r ↦ r.1.label == (Trivia.none, some kwAnn))

/-- Whether a document can be written in strict form and read back: its S-expressions can, and
the characters of its strict form are bytes. -/
def Doc.strictWf (d : Doc) : Bool := d.items.all Document.strictWf && SExp.bytes (toStrict d)

/-- A flag of an empty line reads back. -/
theorem gapOf?_gapAtom (g : Bool) : gapOf? (gapAtom g) = some g := by
  cases g <;> rfl

/-- A comment line reads back. -/
theorem lineOf?_lineSExp (l : Line) : lineOf? (lineSExp l) = some l := by
  obtain ⟨g, t⟩ := l
  simp [lineOf?, lineSExp, listOf, atomOf, gapOf?_gapAtom]

/-- A partial function giving every element of a list a value gives the list of the values. -/
theorem mapM_eq_some {α β : Type} (f : α → Option β) (g : α → β) :
    ∀ xs : List α, (∀ x ∈ xs, f x = some (g x)) → xs.mapM f = some (xs.map g) :=
  List.rec (fun _ ↦ rfl) fun x xs ih h ↦ by
    rw [List.mapM_cons, h x List.mem_cons_self, ih fun y hy ↦ h y (List.mem_cons_of_mem x hy)]
    rfl

/-- Comment lines read back. -/
theorem linesOf?_linesSExp (ls : List Line) : linesOf? (linesSExp ls) = some ls := by
  simp only [linesOf?, linesSExp, listOf, RoseTree.label_node, RoseTree.children_node]
  exact List.rec rfl (fun l ls ih ↦ by
    rw [List.map_cons, List.mapM_cons, lineOf?_lineSExp, ih]
    rfl) ls

/-- The strict form of a node. -/
theorem strictOf_node (l : Trivia × Option (List Char)) (cs : List SExpr) :
    strictOf (RoseTree.node l cs) =
      if l.1 == Trivia.none then RoseTree.node l.2 (cs.map strictOf)
      else listOf [atomOf kwAnn, RoseTree.node l.2 (cs.map strictOf), linesSExp l.1.lead,
        gapAtom l.1.gap, linesSExp l.1.close] := by
  simp [strictOf]

/-- The reading of a node from strict form. -/
theorem fromStrict_node (a : Option (List Char)) (xs : List SExp) :
    fromStrict (RoseTree.node a xs) = fromStrictStep a (xs.map fun x ↦ (x, fromStrict x)) := by
  simp [fromStrict]

/-- A node whose first element is not the atom {lit}`*ann` reads as itself without trivia. -/
theorem fromStrictStep_eq_plain (a : Option (List Char)) (rs : List (SExp × Option SExpr))
    (h : ∀ x ∈ rs.head?, isAnnHead x.1 = false) :
    fromStrictStep a rs = (rs.mapM Prod.snd).map (RoseTree.node (Trivia.none, a)) := by
  unfold fromStrictStep
  split
  · rename_i hd _ _ _ _ _ _ _ _
    have := h _ rfl
    simp only at this
    simp [this]
  · rfl

/-- The strict form of an S-expression whose label is not the atom {lit}`*ann` without trivia
is not that atom. -/
theorem isAnnHead_strictOf (c : SExpr) (h : c.label ≠ (Trivia.none, some kwAnn)) :
    isAnnHead (strictOf c) = false := by
  rw [← RoseTree.node_label_children c] at h ⊢
  obtain ⟨⟨tr, k⟩, cs⟩ : ∃ p, p = (c.label, c.children) := ⟨_, rfl⟩
  rw [strictOf_node]
  by_cases htr : (c.label.1 == Trivia.none) = true
  · simp only [htr, ↓reduceIte]
    simp only [beq_iff_eq] at htr
    simp only [isAnnHead, RoseTree.label_node, RoseTree.children_node, Bool.and_eq_false_iff,
      beq_eq_false_iff_ne, ne_eq, List.isEmpty_eq_false_iff]
    left
    intro hk
    exact h (by rw [RoseTree.label_node]; exact Prod.ext htr hk)
  · simp only [Bool.not_eq_true] at htr
    simp only [htr, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- The well-formedness of a node for strict form. -/
theorem strictWf_node (l : Trivia × Option (List Char)) (cs : List SExpr) :
    strictWf (RoseTree.node l cs) =
      (cs.all strictWf &&
        match l.2 with
        | some _ => cs.isEmpty
        | none => !(cs.head?.any fun c ↦ c.label == (Trivia.none, some kwAnn))) := by
  simp only [strictWf, RoseTree.para_node, List.all_map, Function.comp_def, List.isEmpty_map,
    List.head?_map, Option.any_map]

/-- Mapping a list by a function a partial function inverts gives the list back. -/
theorem mapM_map_of {α β : Type} (f : β → Option α) (g : α → β) :
    ∀ xs : List α, (∀ x ∈ xs, f (g x) = some x) → (xs.map g).mapM f = some xs :=
  List.rec (fun _ ↦ rfl) fun x xs ih h ↦ by
    rw [List.map_cons, List.mapM_cons, h x List.mem_cons_self,
      ih fun y hy ↦ h y (List.mem_cons_of_mem x hy)]
    rfl

/-- The strict form of a well-formed S-expression reads back to it. -/
theorem fromStrict_strictOf : ∀ t : SExpr, strictWf t → fromStrict (strictOf t) = some t :=
  RoseTree.ind fun l cs ih h ↦ by
    rw [strictWf_node, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hcs, hk⟩ := h
    have hhead : ∀ x ∈ ((cs.map strictOf).map fun x ↦ (x, fromStrict x)).head?,
        isAnnHead x.1 = false := by
      intro x hx
      cases cs with
      | nil => simp at hx
      | cons c cs' =>
        simp only [List.map_cons, List.head?_cons, Option.mem_some_iff] at hx
        subst hx
        apply isAnnHead_strictOf
        cases hl : l.2 with
        | some _ => rw [hl] at hk; simp at hk
        | none =>
          rw [hl] at hk
          simp only [List.head?_cons, Option.any_some, Bool.not_eq_true',
            beq_eq_false_iff_ne] at hk
          exact hk
    have hplain : fromStrict (RoseTree.node l.2 (cs.map strictOf)) =
        some (RoseTree.node (Trivia.none, l.2) cs) := by
      rw [fromStrict_node, fromStrictStep_eq_plain _ _ hhead, List.map_map,
        mapM_map_of Prod.snd ((fun x ↦ (x, fromStrict x)) ∘ strictOf) cs
          fun c hc ↦ ih c hc (hcs c hc)]
      rfl
    obtain ⟨tr, k⟩ := l
    have hplain' : fromStrict (RoseTree.node k (cs.map strictOf)) =
        some (RoseTree.node (Trivia.none, k) cs) := hplain
    rw [strictOf_node]
    by_cases htr : (tr == Trivia.none) = true
    · simp only [htr, ↓reduceIte]
      simp only [beq_iff_eq] at htr
      subst htr
      exact hplain'
    · simp only [Bool.not_eq_true] at htr
      simp only [htr, Bool.false_eq_true, ↓reduceIte]
      rw [listOf, fromStrict_node]
      simp only [List.map_cons, List.map_nil, hplain']
      simp only [fromStrictStep, isAnnHead, atomOf, kwAnn, RoseTree.label_node,
        RoseTree.children_node, linesOf?_linesSExp, gapOf?_gapAtom]
      rfl

/-- The strict form of a well-formed document reads back to it. -/
theorem fromStrictDoc_toStrict (d : Doc) (h : d.strictWf) :
    fromStrictDoc (toStrict d) = some d := by
  simp only [toStrict, fromStrictDoc, listOf, atomOf, kwDoc, RoseTree.label_node,
    RoseTree.children_node, linesOf?_linesSExp,
    mapM_map_of fromStrict strictOf d.items fun c hc ↦
      fromStrict_strictOf c (List.all_eq_true.mp (Bool.and_eq_true _ _ ▸ h).1 c hc)]
  rfl

/-- An atom is well formed. -/
theorem wf_atomOf (s : List Char) : SExp.wf (atomOf s) := by
  simp [atomOf, SExp.wf_atom]

/-- Comment lines are well formed in strict form. -/
theorem wf_linesSExp (ls : List Line) : SExp.wf (linesSExp ls) := by
  simp only [linesSExp, listOf, SExp.wf_list, List.all_map, List.all_eq_true,
    Function.comp_apply]
  intro l _
  simp only [lineSExp, gapAtom, listOf, SExp.wf_list, List.all_cons, wf_atomOf, List.all_nil,
    Bool.and_self]

/-- The strict form of a well-formed S-expression is well formed. -/
theorem wf_strictOf : ∀ t : SExpr, strictWf t → SExp.wf (strictOf t) :=
  RoseTree.ind fun l cs ih h ↦ by
    rw [strictWf_node, Bool.and_eq_true, List.all_eq_true] at h
    obtain ⟨hcs, hk⟩ := h
    have hcore : SExp.wf (RoseTree.node l.2 (cs.map strictOf)) := by
      cases hl : l.2 with
      | some s =>
        rw [hl] at hk
        rw [SExp.wf_atom]
        simpa using hk
      | none =>
        rw [SExp.wf_list, List.all_map, List.all_eq_true]
        exact fun c hc ↦ ih c hc (hcs c hc)
    rw [strictOf_node]
    split
    · exact hcore
    · simp only [listOf, SExp.wf_list, List.all_cons, wf_atomOf, hcore, wf_linesSExp,
        gapAtom, List.all_nil, Bool.and_self]

/-- A document in the canonical encoding. -/
def printCanonDoc (d : Doc) : List Char := canonOf (toStrict d)

/-- A document read from a strict encoding: one S-expression, read from strict form. -/
def readStrictDoc (text : List Char) : Option Doc :=
  (readDoc text).bind fun d ↦
    match d.items, d.trail with
    | [t], [] => fromStrictDoc (RoseTree.erase t)
    | _, _ => none

/-- The retraction law of the canonical encoding of documents. -/
theorem readStrictDoc_printCanonDoc (d : Doc) (h : d.strictWf) :
    readStrictDoc (printCanonDoc d) = some d := by
  have hw : SExp.wf (toStrict d) := by
    simp only [toStrict, listOf, SExp.wf_list, List.all_cons, wf_atomOf, wf_linesSExp,
      List.all_map, Bool.true_and, List.all_eq_true, Function.comp_apply]
    exact fun c hc ↦ wf_strictOf c (List.all_eq_true.mp (Bool.and_eq_true _ _ ▸ h).1 c hc)
  rw [readStrictDoc, printCanonDoc, readDoc_canonOf _ hw (Bool.and_eq_true _ _ ▸ h).2,
    Option.bind_some]
  simp only [erase_plain]
  exact fromStrictDoc_toStrict d h

/-! ## The advanced encoding -/

/-- An S-expression in the advanced encoding, laid out by a layout: its canonical tokens, a
token bare and every other atom quoted with escapes of ASCII alone. -/
def advancedOf (L : ℕ → Bool × ℕ) (t : SExp) : List Char :=
  render .advanced (arrangeFrom L (canonToks t) none 0) ++ ['\n']

/-- The lexer reads the advanced encoding of an S-expression whose characters are bytes to its
canonical tokens, whatever the layout. -/
theorem lex_advancedOf (L : ℕ → Bool × ℕ) (t : SExp) (hb : SExp.bytes t) :
    lex (advancedOf L t) = some (canonToks t) :=
  lex_print Spelling.lawful_advanced L _ (List.all_eq_true.mpr (canonToks_wf t hb))

/-- The advanced encoding of a well-formed S-expression whose characters are bytes reads back to
it, as a document of that S-expression alone, without trivia, whatever the layout. -/
theorem readDoc_advancedOf (L : ℕ → Bool × ℕ) (t : SExp) (ht : SExp.wf t) (hb : SExp.bytes t) :
    readDoc (advancedOf L t) = some ⟨[plain t], []⟩ := by
  rw [readDoc, lex_advancedOf L t hb, Option.bind_some, foldl_readStep_canonToks t ht _ [] rfl]
  simp [Frame.start, Frame.push]

/-- A document in the advanced encoding, its strict form laid out within a line width by the
layout policy. The layout is bound outside the function of positions, so that it is computed
once rather than at every position. -/
def printAdvancedDoc (lim : ℕ) (d : Doc) : List Char :=
  let ds := defaultLayout .advanced lim ⟨[plain (toStrict d)], []⟩
  advancedOf (fun i ↦ ds.getD i (false, 0)) (toStrict d)

/-- The retraction law of the advanced encoding of documents. -/
theorem readStrictDoc_printAdvancedDoc (lim : ℕ) (d : Doc) (h : d.strictWf) :
    readStrictDoc (printAdvancedDoc lim d) = some d := by
  have hw : SExp.wf (toStrict d) := by
    simp only [toStrict, listOf, SExp.wf_list, List.all_cons, wf_atomOf, wf_linesSExp,
      List.all_map, Bool.true_and, List.all_eq_true, Function.comp_apply]
    exact fun c hc ↦ wf_strictOf c (List.all_eq_true.mp (Bool.and_eq_true _ _ ▸ h).1 c hc)
  rw [readStrictDoc, printAdvancedDoc, readDoc_advancedOf _ _ hw (Bool.and_eq_true _ _ ▸ h).2,
    Option.bind_some]
  simp only [erase_plain]
  exact fromStrictDoc_toStrict d h

/-- A document read from the basic transport encoding: the canonical encoding, or its base-64
encoding between braces, whitespace around them ignored. -/
def readBasic (text : List Char) : Option Doc :=
  match text.dropWhile isSpace with
  | '{' :: rest =>
    match (rest.dropWhile isSpace).reverse.dropWhile isSpace with
    | '}' :: inner =>
      (decodeBase64 (inner.reverse.filter fun c ↦ !isSpace c)).bind readStrictDoc
    | _ => none
  | _ => readStrictDoc text

end Geb.Kernel.Document

end
