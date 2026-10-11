/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.ConcreteSyntax.Decimal
public import Geb.Prototypes.RoseTree.Decorated

set_option doc.verso true

/-!
# Source documents in the authoring profile

Geb's source is written in the authoring profile of the syntaxes of \[RFC9804\]: its
advanced encoding with line comments, UTF-8 and line breaks in quoted strings, numerals as bare
runs of digits, the ampersand as a token, and {lit}`?name` for the form {lit}`(hole name)`. A
source document is the text of a program read without loss of anything a person wrote but the
widths of its whitespace and the spellings of its atoms: its S-expressions, its comment lines
and the empty lines between its items. It is read into S-expressions with comments: rose trees
whose labels are those of the kernel's S-expressions, the bytes of an atom or nothing for a
list, each node decorated with its trivia, the comment lines before it, each with whether an
empty line precedes it, whether an empty line precedes the node itself, and, for a list, the
comment lines before its closing parenthesis; the comment lines after the last S-expression
belong to the document. The decoration is that of {name}`Geb.RoseTree.Decorated`, so the
trivia, like every other annotation, is computed from and into other decorations by
redecoration. A comment is placed by its position alone, so reading attaches no comment to the
definition it documents; that attachment is a redecoration of the trivia.

Text is bytes, one character per byte as the kernel's readers read files, and the lexer rejects
a character beyond a byte; UTF-8 text is read as its bytes. An atom is a string of bytes; the
printer chooses its spelling from its bytes by a spelling ({lit}`Spelling`). The profile's
({lit}`Spelling.profile`) writes an atom bare when it is a numeral, a token of \[RFC9804\]
or the ampersand, and otherwise as a quoted string, whose double quotes and backslashes are
escaped, and whose other control characters are written as hexadecimal escapes; the advanced
encoding's ({lit}`Spelling.advanced`) writes only a token bare and escapes every character
beyond printable ASCII, so that its text is ASCII. The lexer reads back what every lawful
spelling writes ({lit}`lex_print`). The reader admits the escapes
of \[RFC9804\] and its other spellings of atoms, verbatim, hexadecimal and base-64, each
with or without a length; display hints are rejected.

The printer {lit}`print` is parameterized by a layout, a choice at each token of whether a line
break precedes it and of the indentation of the new line, and the retraction law holds at every
layout ({lit}`readDoc_print`): reading a printed well-formed document gives the document back.
A formatter, reading and printing with a layout computed from the document, is therefore
idempotent ({lit}`format_format`), whatever the layout policy, so the policy is not part of
what is proved.

## Main definitions

* {lit}`SExp` — the kernel's S-expressions, the labels of the trees read.
* {lit}`Line`, {lit}`Trivia`, {lit}`SExpr`, {lit}`Doc` — comment lines, the trivia an
  S-expression is decorated with, S-expressions with comments, and source documents.
* {lit}`Spelling` — the spellings of atoms, the profile's and the advanced encoding's.
* {lit}`lex`, {lit}`readDoc` — the lexer and reader keeping comments and empty lines.
* {lit}`sepFor`, {lit}`arrangeFrom`, {lit}`print` — the separators a layout chooses, and the
  printer.
* {lit}`defaultLayout`, {lit}`format` — a layout policy, and the formatter.

## Main statements

* {lit}`readDoc_print` — the retraction law, at every layout.
* {lit}`format_format` — the formatter is idempotent.

## Implementation notes

The printer separates each token from the one before it by a separator determined by the two
tokens and the layout's choice ({lit}`sepFor`): an empty line before a token whose label records
one, a line break after a comment, which extends to the end of its line, and otherwise a line
break when the layout chooses one, nothing after an opening parenthesis or before a closing one,
and a space elsewhere. The lexer's correctness is proved for every sequence of separators so
formed, one token at a time, so the layout is an arbitrary function of the token's position.
A bare atom, a hole and a comment end where the character after them is read; a quoted string,
the ampersand and a parenthesis end with their last character. The reader holds the comment
lines read since the last S-expression on its stack, until the S-expression after them, or the
end of the list or of the text, takes them as its trivia.

## References

* \[RFC9804\] — the syntaxes of S-expressions the profile extends.

## Tags

S-expression, RFC 9804, comments, trivia, formatter, retraction, lossless syntax tree
-/

@[expose] public section

namespace Geb.Kernel

/-- An S-expression: a leaf carries an atom, and a node without a label is a list. -/
abbrev SExp : Type := RoseTree (Option (List Char))

namespace Document

/-- A comment line: whether an empty line precedes it, and its characters after the semicolon
and before the end of the line. -/
@[ext] structure Line where
  /-- Whether an empty line precedes the comment line. -/
  gap : Bool
  /-- The characters of the comment. -/
  text : List Char
  deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprLine.repr

/-- The trivia an S-expression is decorated with: the comment lines before it, whether an empty
line precedes it, and, for a list, the comment lines before its closing parenthesis. -/
@[ext] structure Trivia where
  /-- The comment lines before the S-expression. -/
  lead : List Line
  /-- Whether an empty line precedes the S-expression. -/
  gap : Bool
  /-- The comment lines before a list's closing parenthesis. -/
  close : List Line
  deriving DecidableEq, Repr

attribute [nolint unusedArguments] instReprTrivia.repr

/-- An S-expression with comments: a rose tree whose labels are those of
{name}`Geb.Kernel.SExp`, an atom's characters or nothing for a list, each decorated with its
trivia. -/
abbrev SExpr : Type := RoseTree.Decorated Trivia (Option (List Char))

/-- A source document: its S-expressions with comments, and the comment lines after the
last. -/
@[ext] structure Doc where
  /-- The S-expressions. -/
  items : List SExpr
  /-- The comment lines after the last S-expression. -/
  trail : List Line

/-! ## Characters and the spelling of atoms -/

/-- Whether a character is whitespace in the syntaxes of \[RFC9804\]: a space, a horizontal
or vertical tab, a form feed, a carriage return or a line feed. -/
def isSpace (c : Char) : Bool :=
  c == ' ' || c == '\n' || c == '\t' || c == '\r' || c.toNat == 11 || c.toNat == 12

/-- Whether a character is a decimal digit, of code point 48 to 57. -/
def isDigit (c : Char) : Bool := 48 ≤ c.toNat && c.toNat ≤ 57

/-- Whether a character may begin a token of \[RFC9804\]: an ASCII letter, of code point
65 to 90 or 97 to 122, or one of its eight pseudo-alphabetic characters. -/
def isTokenStart (c : Char) : Bool :=
  (65 ≤ c.toNat && c.toNat ≤ 90) || (97 ≤ c.toNat && c.toNat ≤ 122) || c == '-' || c == '.' ||
    c == '/' || c == '_' || c == ':' || c == '*' || c == '+' || c == '='

/-- Whether a character may continue a token: a character that may begin one, or a digit. -/
def isTokenChar (c : Char) : Bool := isTokenStart c || isDigit c

/-- Whether a word is a token: non-empty, of token characters, and not beginning with a
digit. -/
def isToken : List Char → Bool
  | [] => false
  | c :: cs => isTokenStart c && cs.all isTokenChar

/-- Whether a word is a numeral: a non-empty run of decimal digits. -/
def isNumeral (s : List Char) : Bool := !s.isEmpty && s.all isDigit

/-- Whether an atom is written bare and ends where its word ends: a numeral or a token. -/
def isBare (s : List Char) : Bool := isNumeral s || isToken s

/-- Whether the printer writes a character of a quoted string as it is: a printable ASCII
character, of code point 32 to 126, other than the double quote and the backslash, a line
feed, or a character beyond ASCII. -/
def isPlain (c : Char) : Bool :=
  (32 ≤ c.toNat && c.toNat ≤ 126 && c != '"' && c != '\\') || c == '\n' || 128 ≤ c.toNat

/-- The hexadecimal digit of a number below sixteen, upper case. -/
def hexDigit (n : ℕ) : Char := Char.ofNat (if n < 10 then 48 + n else 55 + n)

/-- The value of a hexadecimal digit of either case. -/
def hexVal (c : Char) : Option ℕ :=
  if isDigit c then some (c.toNat - 48)
  else if 65 ≤ c.toNat && c.toNat ≤ 70 then some (c.toNat - 55)
  else if 97 ≤ c.toNat && c.toNat ≤ 102 then some (c.toNat - 87)
  else none

/-- A spelling of atoms: which atoms are written bare, which characters of a quoted string are
written as they are, and whether the form of a hole is written {lit}`?name`. -/
structure Spelling where
  /-- Whether an atom is written bare. -/
  bare : List Char → Bool
  /-- Whether a character of a quoted string is written as it is. -/
  plain : Char → Bool
  /-- Whether the form of a hole is written {lit}`?name`. -/
  holes : Bool

/-- The authoring profile's spelling: a numeral, a token and the ampersand bare, the characters
{name}`isPlain` admits as they are in a quoted string, and holes as {lit}`?name`. -/
def Spelling.profile : Spelling := ⟨fun s ↦ isBare s || s == ['&'], isPlain, true⟩

/-- Whether a character is printable ASCII, of code point 32 to 126, other than the double quote
and the backslash. -/
def isPlainAscii (c : Char) : Bool := 32 ≤ c.toNat && c.toNat ≤ 126 && c != '"' && c != '\\'

/-- The spelling of the advanced encoding of \[RFC9804\] in ASCII alone: a token bare, every
other atom quoted, its characters other than printable ASCII escaped, and no hole's form
abbreviated. -/
def Spelling.advanced : Spelling := ⟨isToken, isPlainAscii, false⟩

/-- The spellings the lexer reads back: a bare atom is a numeral, a token or the ampersand, and
a character written as it is in a quoted string is one the lexer reads as itself. -/
structure Spelling.Lawful (sp : Spelling) : Prop where
  /-- A bare atom is a numeral, a token or the ampersand. -/
  bare : ∀ s, sp.bare s = true → isBare s = true ∨ s = ['&']
  /-- A character written as it is is one the lexer reads as itself. -/
  plain : ∀ c, sp.plain c = true → isPlain c = true

/-- The authoring profile's spelling is lawful. -/
theorem Spelling.lawful_profile : Spelling.profile.Lawful where
  bare s h := by simpa only [Spelling.profile, Bool.or_eq_true, beq_iff_eq] using h
  plain _ h := h

/-- The advanced encoding's spelling is lawful. -/
theorem Spelling.lawful_advanced : Spelling.advanced.Lawful where
  bare s h := Or.inl (by simp only [isBare, Bool.or_eq_true]; exact Or.inr h)
  plain c h := by
    simp only [Spelling.advanced, isPlainAscii, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [isPlain, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    exact Or.inl (Or.inl h)

/-- A character of a quoted string as a spelling writes it: as it is, after a backslash when it
is the double quote or the backslash, and otherwise as a hexadecimal escape. -/
def Spelling.escape (sp : Spelling) (c : Char) : List Char :=
  if sp.plain c then [c]
  else if c == '"' || c == '\\' then ['\\', c]
  else ['\\', 'x', hexDigit (c.toNat / 16), hexDigit (c.toNat % 16)]

/-- An atom as a spelling writes it: bare, or quoted. -/
def Spelling.spell (sp : Spelling) (s : List Char) : List Char :=
  if sp.bare s then s else '"' :: s.flatMap sp.escape ++ ['"']

/-! ## Tokens and the lexer -/

/-- The tokens of a source document; each but a closing parenthesis records whether an empty
line precedes it. -/
inductive Tok where
  /-- An opening parenthesis. -/
  | lp (gap : Bool)
  /-- A closing parenthesis. -/
  | rp
  /-- An atom, with its characters. -/
  | atom (gap : Bool) (s : List Char)
  /-- A comment line, without its semicolon and line break. -/
  | comment (gap : Bool) (s : List Char)
  /-- A hole, {lit}`?name`, with the characters of its name. -/
  | hole (gap : Bool) (s : List Char)
  deriving DecidableEq, Repr

/-- Whether an empty line precedes a token. -/
def Tok.gap : Tok → Bool
  | .lp g => g
  | .rp => false
  | .atom g _ => g
  | .comment g _ => g
  | .hole g _ => g

/-- Whether a token is a comment. -/
def Tok.isComment : Tok → Bool
  | .comment _ _ => true
  | _ => false

/-- Whether a token is an opening parenthesis. -/
def Tok.isLp : Tok → Bool
  | .lp _ => true
  | _ => false

/-- Whether a token is a closing parenthesis. -/
def Tok.isRp : Tok → Bool
  | .rp => true
  | _ => false

/-- Whether a character is a byte, of code point below 256: the readers read text a byte to a
character. -/
def isByte (c : Char) : Bool := c.toNat < 256

/-- Whether a token can be spelled and read back: an atom is of bytes, a comment is of bytes and
contains no line break, and a hole is named by a token. -/
def Tok.wf : Tok → Bool
  | .atom _ s => s.all isByte
  | .comment _ s => s.all (· != '\n') && s.all isByte
  | .hole _ s => isToken s
  | _ => true

/-- What the lexer is reading: nothing, a bare atom, a numeral, a hole's name, a comment, a
quoted string, an escape in a quoted string, after its backslash, after a backslash and a
carriage return or a line feed, or among the digits of a hexadecimal or octal escape, with the
digits read and their value, a verbatim atom, with the bytes left, or a hexadecimal or base-64
atom. A quoted string, its escapes, and a hexadecimal or base-64 atom carry the length a decimal
prefix declares, if one does. -/
inductive Mode where
  /-- Between tokens. -/
  | idle
  /-- A bare atom. -/
  | bare
  /-- A numeral. -/
  | numeral
  /-- A hole's name. -/
  | hole
  /-- A comment. -/
  | comment
  /-- A quoted string. -/
  | str (want : Option ℕ)
  /-- An escape, after its backslash. -/
  | esc (want : Option ℕ)
  /-- After a backslash and a carriage return. -/
  | escCR (want : Option ℕ)
  /-- After a backslash and a line feed. -/
  | escLF (want : Option ℕ)
  /-- A hexadecimal escape, with the digits read and their value. -/
  | hex (n v : ℕ) (want : Option ℕ)
  /-- An octal escape, with the digits read and their value. -/
  | oct (n v : ℕ) (want : Option ℕ)
  /-- A verbatim atom, with the bytes left to read. -/
  | verbatim (left : ℕ)
  /-- A hexadecimal atom. -/
  | hexAtom (want : Option ℕ)
  /-- A base-64 atom. -/
  | base64 (want : Option ℕ)
  deriving DecidableEq

/-- The lexer's state. -/
structure LexState where
  /-- The tokens read, the latest first. -/
  toks : List Tok
  /-- The characters of the token being read, the latest first. -/
  cur : List Char
  /-- What the lexer is reading. -/
  mode : Mode
  /-- The line breaks since the last token. -/
  breaks : ℕ
  /-- Whether an empty line precedes the token being read. -/
  gap : Bool
  /-- Whether the text read so far is well formed. -/
  ok : Bool

/-- The state after a text that is not well formed. -/
def LexState.fail : LexState := ⟨[], [], .idle, 0, false, false⟩

/-- The state between tokens, after the tokens read and the line breaks since the last. -/
def LexState.idle (toks : List Tok) (n : ℕ) : LexState := ⟨toks, [], .idle, n, false, true⟩

/-- Read a character between tokens, after the tokens read and the line breaks since the
last. -/
def idleStep (toks : List Tok) (n : ℕ) (ch : Char) : LexState :=
  let g := decide (2 ≤ n)
  if ch == ';' then ⟨toks, [], .comment, 0, g, true⟩
  else if ch == '(' then .idle (.lp g :: toks) 0
  else if ch == ')' then .idle (.rp :: toks) 0
  else if ch == '"' then ⟨toks, [], .str none, 0, g, true⟩
  else if ch == '&' then .idle (.atom g ['&'] :: toks) 0
  else if ch == '?' then ⟨toks, [], .hole, 0, g, true⟩
  else if ch == '#' then ⟨toks, [], .hexAtom none, 0, g, true⟩
  else if ch == '|' then ⟨toks, [], .base64 none, 0, g, true⟩
  else if isSpace ch then .idle toks (if ch == '\n' then n + 1 else n)
  else if isDigit ch then ⟨toks, [ch], .numeral, 0, g, true⟩
  else if isTokenStart ch then ⟨toks, [ch], .bare, 0, g, true⟩
  else .fail

/-- An atom's bytes ended, as the token after the tokens read, when they number what the
length declared requires. -/
def endAtom (toks : List Tok) (g : Bool) (want : Option ℕ) (bs : List Char) : LexState :=
  if want.all (· == bs.length) then .idle (.atom g bs :: toks) 0 else .fail

/-- Read a character of a quoted string. -/
def strStep (s : LexState) (want : Option ℕ) (ch : Char) : LexState :=
  if ch == '"' then endAtom s.toks s.gap want s.cur.reverse
  else if ch == '\\' then { s with mode := .esc want }
  else if isPlain ch || ch == '\r' then { s with cur := ch :: s.cur, mode := .str want }
  else .fail

/-- The character an escape of one character after its backslash denotes, the escapes of the C
language that \[RFC9804\] admits. -/
def escChar (ch : Char) : Option Char :=
  if ch == 'a' then some (Char.ofNat 7) else if ch == 'b' then some (Char.ofNat 8)
  else if ch == 't' then some '\t' else if ch == 'v' then some (Char.ofNat 11)
  else if ch == 'n' then some '\n' else if ch == 'f' then some (Char.ofNat 12)
  else if ch == 'r' then some '\r'
  else if ch == '"' || ch == '\'' || ch == '?' || ch == '\\' then some ch
  else none

/-- The value of a decimal length, written in the shortest form, as \[RFC9804\] requires. -/
def decimal? (cs : List Char) : Option ℕ :=
  (Csexp.digitsVal cs).bind fun n ↦ if Csexp.decOf n == cs then some n else none

/-- One digit of a hexadecimal atom read onto the bytes decoded, the latest first, and the high
digit of a byte not yet complete. -/
def hexStep (st : Option (List Char × Option ℕ)) (c : Char) : Option (List Char × Option ℕ) :=
  st.bind fun p ↦ (hexVal c).map fun d ↦
    match p.2 with
    | none => (p.1, some d)
    | some h => (Char.ofNat (16 * h + d) :: p.1, none)

/-- The bytes of a hexadecimal atom's digits, an even number of them. -/
def decodeHex (cs : List Char) : Option (List Char) :=
  match cs.foldl hexStep (some ([], none)) with
  | some (bs, none) => some bs.reverse
  | _ => none

/-- The value of a base-64 character of \[RFC4648\]. -/
def base64Val (c : Char) : Option ℕ :=
  if 65 ≤ c.toNat && c.toNat ≤ 90 then some (c.toNat - 65)
  else if 97 ≤ c.toNat && c.toNat ≤ 122 then some (c.toNat - 71)
  else if isDigit c then some (c.toNat + 4)
  else if c == '+' then some 62 else if c == '/' then some 63 else none

/-- One character of a base-64 atom read onto the bytes decoded, the latest first, the bits
not yet a byte with their number, and the padding read, after which only padding may follow. -/
def base64Step (st : Option (List Char × ℕ × ℕ × ℕ)) (c : Char) :
    Option (List Char × ℕ × ℕ × ℕ) :=
  st.bind fun (bs, acc, bits, pad) ↦
    if c == '=' then (if pad < 2 then some (bs, acc, bits, pad + 1) else none)
    else if pad != 0 then none
    else (base64Val c).map fun v ↦
      if bits + 6 ≥ 8 then
        let w := 64 * acc + v
        let r := bits + 6 - 8
        (Char.ofNat (w / 2 ^ r) :: bs, w % 2 ^ r, r, 0)
      else (bs, 64 * acc + v, bits + 6, 0)

/-- The bytes of a base-64 atom's characters, unless a group ends after a single character. -/
def decodeBase64 (cs : List Char) : Option (List Char) :=
  match cs.foldl base64Step (some ([], 0, 0, 0)) with
  | some (bs, _, bits, _) => if bits < 6 then some bs.reverse else none
  | none => none

/-- Read a character after a numeral: a further digit, or the colon, double quote, number sign
or vertical bar after a decimal length, beginning a verbatim, quoted, hexadecimal or base-64
atom of that length. -/
def lengthStep (s : LexState) (ch : Char) : LexState :=
  match decimal? s.cur.reverse with
  | none => .fail
  | some n =>
    if ch == ':' then
      if n == 0 then .idle (.atom s.gap [] :: s.toks) 0
      else ⟨s.toks, [], .verbatim n, 0, s.gap, true⟩
    else if ch == '"' then ⟨s.toks, [], .str (some n), 0, s.gap, true⟩
    else if ch == '#' then ⟨s.toks, [], .hexAtom (some n), 0, s.gap, true⟩
    else if ch == '|' then ⟨s.toks, [], .base64 (some n), 0, s.gap, true⟩
    else .fail

/-- Read one character. -/
def lexStep (s : LexState) (ch : Char) : LexState :=
  if !s.ok then s else
  match s.mode with
  | .idle => idleStep s.toks s.breaks ch
  | .comment =>
    if ch == '\n' then .idle (.comment s.gap s.cur.reverse :: s.toks) 1
    else { s with cur := ch :: s.cur }
  | .bare =>
    if isTokenChar ch then { s with cur := ch :: s.cur }
    else idleStep (.atom s.gap s.cur.reverse :: s.toks) 0 ch
  | .numeral =>
    if isDigit ch then { s with cur := ch :: s.cur }
    else if isTokenChar ch || ch == '"' || ch == '#' || ch == '|' then lengthStep s ch
    else idleStep (.atom s.gap s.cur.reverse :: s.toks) 0 ch
  | .hole =>
    if isTokenChar ch && !(s.cur.isEmpty && isDigit ch) then { s with cur := ch :: s.cur }
    else if s.cur.isEmpty then .fail
    else idleStep (.hole s.gap s.cur.reverse :: s.toks) 0 ch
  | .str want => strStep s want ch
  | .esc want =>
    match escChar ch with
    | some c => { s with cur := c :: s.cur, mode := .str want }
    | none =>
      if ch == 'x' then { s with mode := .hex 0 0 want }
      else if 48 ≤ ch.toNat && ch.toNat ≤ 55 then { s with mode := .oct 1 (ch.toNat - 48) want }
      else if ch == '\r' then { s with mode := .escCR want }
      else if ch == '\n' then { s with mode := .escLF want }
      else .fail
  | .escCR want =>
    if ch == '\n' then { s with mode := .str want }
    else strStep { s with mode := .str want } want ch
  | .escLF want =>
    if ch == '\r' then { s with mode := .str want }
    else strStep { s with mode := .str want } want ch
  | .hex n v want =>
    match hexVal ch with
    | some d =>
      if n == 1 then { s with cur := Char.ofNat (16 * v + d) :: s.cur, mode := .str want }
      else { s with mode := .hex 1 d want }
    | none => .fail
  | .oct n v want =>
    if 48 ≤ ch.toNat && ch.toNat ≤ 55 then
      let w := 8 * v + (ch.toNat - 48)
      if n == 2 then
        if w < 256 then { s with cur := Char.ofNat w :: s.cur, mode := .str want } else .fail
      else { s with mode := .oct (n + 1) w want }
    else .fail
  | .verbatim left =>
    if left ≤ 1 then .idle (.atom s.gap (ch :: s.cur).reverse :: s.toks) 0
    else { s with cur := ch :: s.cur, mode := .verbatim (left - 1) }
  | .hexAtom want =>
    if isSpace ch then s
    else if (hexVal ch).isSome then { s with cur := ch :: s.cur }
    else if ch == '#' then
      match decodeHex s.cur.reverse with
      | some bs => endAtom s.toks s.gap want bs
      | none => .fail
    else .fail
  | .base64 want =>
    if isSpace ch then s
    else if (base64Val ch).isSome || ch == '=' then { s with cur := ch :: s.cur }
    else if ch == '|' then
      match decodeBase64 s.cur.reverse with
      | some bs => endAtom s.toks s.gap want bs
      | none => .fail
    else .fail

/-- The lexer's initial state. -/
def LexState.init : LexState := .idle [] 0

/-- The tokens of a text, from the lexer's state at its end, or nothing when the text is not
well formed or ends inside a quoted string or a hole without a name. -/
def lexEnd (s : LexState) : Option (List Tok) :=
  if !s.ok then none else
  match s.mode with
  | .idle => some s.toks.reverse
  | .comment => some (.comment s.gap s.cur.reverse :: s.toks).reverse
  | .bare | .numeral => some (.atom s.gap s.cur.reverse :: s.toks).reverse
  | .hole => if s.cur.isEmpty then none else some (.hole s.gap s.cur.reverse :: s.toks).reverse
  | _ => none

/-- The tokens of a text, or nothing when it is not well formed or a character is beyond a
byte. -/
def lex (text : List Char) : Option (List Tok) :=
  if text.all isByte then lexEnd (text.foldl lexStep .init) else none

/-- The tokens of a text of bytes. -/
theorem lex_of_bytes {text : List Char} (h : text.all isByte) :
    lex text = lexEnd (text.foldl lexStep .init) := by
  rw [lex, h]
  rfl

/-! ## The reader -/

/-- The characters of the keyword of a hole, {lit}`hole`. -/
def kwHole : List Char := ['h', 'o', 'l', 'e']

/-- The trivia of an S-expression without comment lines or an empty line before it. -/
def Trivia.none : Trivia := ⟨[], false, []⟩

/-- An atom without trivia. -/
def bareAtom (s : List Char) : SExpr := RoseTree.node (.none, some s) []

/-- The form of a hole, {lit}`(hole name)`, with its trivia. -/
def holeForm (tr : Trivia) (s : List Char) : SExpr :=
  RoseTree.node (tr, none) [bareAtom kwHole, bareAtom s]

/-- A frame of the reader's stack: the comment lines before the list being read and whether an
empty line precedes it, its elements read so far, the latest first, and the comment lines read
since the last element, the latest first. -/
structure Frame where
  /-- The comment lines before the list. -/
  lead : List Line
  /-- Whether an empty line precedes the list. -/
  gap : Bool
  /-- The elements read so far, the latest first. -/
  items : List SExpr
  /-- The comment lines read since the last element, the latest first. -/
  pend : List Line

/-- The frame of a list beginning, with the comment lines before it. -/
def Frame.start (lead : List Line) (gap : Bool) : Frame := ⟨lead, gap, [], []⟩

/-- A frame with an element added, the comment lines read before it becoming its trivia. -/
def Frame.push (f : Frame) (t : SExpr) : Frame := ⟨f.lead, f.gap, t :: f.items, []⟩

/-- Read one token into a stack of lists under construction, the innermost first: a comment
line waits for the S-expression after it, or for the end of the list or the text, whose trivia
it becomes, and a hole is read as its form. -/
def readStep : Option (List Frame) → Tok → Option (List Frame)
  | some (f :: fs), .lp g => some (.start f.pend.reverse g :: { f with pend := [] } :: fs)
  | some (f :: fs), .atom g s =>
    some (f.push (RoseTree.node (⟨f.pend.reverse, g, []⟩, some s) []) :: fs)
  | some (f :: fs), .hole g s => some (f.push (holeForm ⟨f.pend.reverse, g, []⟩ s) :: fs)
  | some (f :: fs), .comment g s => some ({ f with pend := ⟨g, s⟩ :: f.pend } :: fs)
  | some (f :: e :: fs), .rp =>
    some (e.push (RoseTree.node (⟨f.lead, f.gap, f.pend.reverse⟩, none) f.items.reverse) :: fs)
  | _, _ => none

/-- The source document of a text, or nothing when the text is not well formed or its
parentheses do not balance. -/
def readDoc (text : List Char) : Option Doc :=
  (lex text).bind fun toks ↦
    match toks.foldl readStep (some [.start [] false]) with
    | some [f] => some ⟨f.items.reverse, f.pend.reverse⟩
    | _ => none

/-! ## The printer -/

/-- A separator before a token. -/
inductive Sep where
  /-- Nothing. -/
  | none
  /-- A space. -/
  | space
  /-- A line break, and the indentation of the new line. -/
  | line (indent : ℕ)
  /-- An empty line, and the indentation of the line after it. -/
  | blank (indent : ℕ)

/-- A separator's characters. -/
def Sep.render : Sep → List Char
  | .none => []
  | .space => [' ']
  | .line k => '\n' :: List.replicate k ' '
  | .blank k => '\n' :: '\n' :: List.replicate k ' '

/-- A token's characters, its atom spelled by a spelling. -/
def Tok.render (sp : Spelling) : Tok → List Char
  | .lp _ => ['(']
  | .rp => [')']
  | .atom _ s => sp.spell s
  | .comment _ s => ';' :: s
  | .hole _ s => '?' :: s

/-- The separator before a token, given the token before it, if any, and a layout's choice of
whether to break the line there and of the indentation of the new line: an empty line where the
token records one; a line break after a comment, which extends to the end of its line, or where
the layout breaks the line; nothing at the start, after an opening parenthesis and before a
closing one; and a space elsewhere. -/
def sepFor (prev : Option Tok) (t : Tok) (brk : Bool) (k : ℕ) : Sep :=
  if t.gap then .blank k
  else if prev.any Tok.isComment || brk then .line k
  else if prev.all Tok.isLp || t.isRp then .none
  else .space

/-- Tokens, each with the separator before it, given a layout, a choice at each position of the
text, and the token before the first and the first's position. -/
def arrangeFrom (L : ℕ → Bool × ℕ) (toks : List Tok) : Option Tok → ℕ → List (Sep × Tok) :=
  List.rec (motive := fun _ ↦ Option Tok → ℕ → List (Sep × Tok)) (fun _ _ ↦ [])
    (fun t _ ih prev i ↦ (sepFor prev t (L i).1 (L i).2, t) :: ih (some t) (i + 1)) toks

/-- The characters of tokens with their separators, atoms spelled by a spelling. -/
def render (sp : Spelling) (ps : List (Sep × Tok)) : List Char :=
  ps.flatMap fun p ↦ p.1.render ++ p.2.render sp

/-! ## Lexing what the printer writes -/

/-- The line breaks a separator writes. -/
def Sep.breaks : Sep → ℕ
  | .none => 0
  | .space => 0
  | .line _ => 1
  | .blank _ => 2

/-- The token a token leaves pending, an atom a spelling writes bare as a numeral or a token, a
comment or a hole, whose end the lexer has not yet read. -/
def pendOf (sp : Spelling) : Option Tok → Option Tok
  | some (.atom g s) => if sp.bare s && isBare s then some (.atom g s) else none
  | some (.comment g s) => some (.comment g s)
  | some (.hole g s) => some (.hole g s)
  | _ => none

/-- The lexer's state after tokens, the latest first, and a pending token. -/
def state (done : List Tok) : Option Tok → LexState
  | some (.atom g s) => ⟨done, s.reverse, if isNumeral s then .numeral else .bare, 0, g, true⟩
  | some (.comment g s) => ⟨done, s.reverse, .comment, 0, g, true⟩
  | some (.hole g s) => ⟨done, s.reverse, .hole, 0, g, true⟩
  | _ => .idle done 0

/-- The tokens the lexer emits as soon as it reads a token: a parenthesis, or an atom a spelling
does not write bare as a numeral or a token. -/
def Tok.emitted (sp : Spelling) (t : Tok) : List Tok :=
  match t with
  | .lp _ => [t]
  | .rp => [t]
  | .atom _ s => if sp.bare s && isBare s then [] else [t]
  | _ => []

/-- Spaces leave a state between tokens as it is. -/
theorem foldl_spaces (d : List Tok) (n k : ℕ) :
    (List.replicate k ' ').foldl lexStep (.idle d n) = .idle d n :=
  Nat.rec rfl (fun k ih ↦ by
    rw [List.replicate_succ, List.foldl_cons]
    exact (congrArg (fun s ↦ (List.replicate k ' ').foldl lexStep s) rfl).trans ih) k

/-- A line break between tokens is counted. -/
theorem lexStep_newline (d : List Tok) (n : ℕ) :
    lexStep (.idle d n) '\n' = .idle d (n + 1) :=
  rfl

/-- A separator read between tokens counts its line breaks. -/
theorem foldl_sep (sep : Sep) (d : List Tok) :
    sep.render.foldl lexStep (.idle d 0) = .idle d sep.breaks := by
  cases sep with
  | none => rfl
  | space => rfl
  | line k => simp only [Sep.render, List.foldl_cons, lexStep_newline, foldl_spaces, Sep.breaks]
  | blank k => simp only [Sep.render, List.foldl_cons, lexStep_newline, foldl_spaces, Sep.breaks]

/-- The hexadecimal digit of a number below sixteen has that value. -/
theorem hexVal_hexDigit : ∀ n : Fin 16, hexVal (hexDigit n) = some n := by decide

/-- A character that may begin a token is not a digit. -/
theorem isDigit_of_isTokenStart {c : Char} (h : isTokenStart c) : isDigit c = false := by
  simp only [isTokenStart, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  rcases h with ((((((((h | h) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  all_goals first
    | rfl
    | simp only [isDigit, Bool.and_eq_false_iff, decide_eq_false_iff_not]
      exact Or.inr fun h' ↦ by omega

/-- Whitespace lies at or below the space in code point. -/
theorem toNat_le_of_isSpace {c : Char} (h : isSpace c) : c.toNat ≤ 32 := by
  simp only [isSpace, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with (((((rfl | rfl) | rfl) | rfl) | h) | h) <;> first | decide | omega

/-- A character that may begin a token lies above the space in code point. -/
theorem lt_toNat_of_isTokenStart {c : Char} (h : isTokenStart c) : 32 < c.toNat := by
  simp only [isTokenStart, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  rcases h with ((((((((h | h) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  all_goals first | decide | omega

/-- Characters of different code points differ. -/
theorem beq_false_of_toNat {c d : Char} (h : c.toNat ≠ d.toNat) : (c == d) = false :=
  beq_eq_false_iff_ne.mpr fun e ↦ h (congrArg Char.toNat e)

/-- A character that may begin a token is none of the characters with which another token
begins: the semicolon, the parentheses, the double quote, the ampersand, the question mark,
the number sign and the vertical bar. -/
theorem toNat_ne_of_isTokenStart {c : Char} (h : isTokenStart c) :
    c.toNat ≠ 59 ∧ c.toNat ≠ 40 ∧ c.toNat ≠ 41 ∧ c.toNat ≠ 34 ∧ c.toNat ≠ 38 ∧
      c.toNat ≠ 63 ∧ c.toNat ≠ 35 ∧ c.toNat ≠ 124 := by
  simp only [isTokenStart, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at h
  rcases h with ((((((((h | h) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl
  all_goals first
    | decide
    | exact ⟨fun e ↦ by omega, fun e ↦ by omega, fun e ↦ by omega, fun e ↦ by omega,
        fun e ↦ by omega, fun e ↦ by omega, fun e ↦ by omega, fun e ↦ by omega⟩

/-- Reading a character between tokens that is none of the characters with which a token other
than a bare atom or a numeral begins, nor whitespace, gives the state its classes give. -/
theorem idleStep_of_ne (d : List Tok) (n : ℕ) {c : Char}
    (h : c.toNat ≠ 59 ∧ c.toNat ≠ 40 ∧ c.toNat ≠ 41 ∧ c.toNat ≠ 34 ∧ c.toNat ≠ 38 ∧
      c.toNat ≠ 63 ∧ c.toNat ≠ 35 ∧ c.toNat ≠ 124) (hs : isSpace c = false) :
    idleStep d n c =
      if isDigit c then ⟨d, [c], .numeral, 0, decide (2 ≤ n), true⟩
      else if isTokenStart c then ⟨d, [c], .bare, 0, decide (2 ≤ n), true⟩
      else .fail := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := h
  unfold idleStep
  rw [beq_false_of_toNat (d := ';') h1, beq_false_of_toNat (d := '(') h2,
    beq_false_of_toNat (d := ')') h3, beq_false_of_toNat (d := '"') h4,
    beq_false_of_toNat (d := '&') h5, beq_false_of_toNat (d := '?') h6,
    beq_false_of_toNat (d := '#') h7, beq_false_of_toNat (d := '|') h8, hs]
  rfl

/-- Reading a digit between tokens begins a numeral. -/
theorem idleStep_digit (d : List Tok) (n : ℕ) {c : Char} (hc : isDigit c) :
    idleStep d n c = ⟨d, [c], .numeral, 0, decide (2 ≤ n), true⟩ := by
  have hb : 48 ≤ c.toNat ∧ c.toNat ≤ 57 := by
    simpa only [isDigit, Bool.and_eq_true, decide_eq_true_eq] using hc
  have hs : isSpace c = false := by
    cases h : isSpace c
    · rfl
    · have := toNat_le_of_isSpace h
      exfalso
      omega
  rw [idleStep_of_ne d n ⟨fun e ↦ by omega, fun e ↦ by omega, fun e ↦ by omega,
    fun e ↦ by omega, fun e ↦ by omega, fun e ↦ by omega, fun e ↦ by omega,
    fun e ↦ by omega⟩ hs, hc]
  rfl

/-- Reading a character that may begin a token, between tokens, begins a bare atom. -/
theorem idleStep_tokenStart (d : List Tok) (n : ℕ) {c : Char} (hc : isTokenStart c) :
    idleStep d n c = ⟨d, [c], .bare, 0, decide (2 ≤ n), true⟩ := by
  have hs : isSpace c = false := by
    cases h : isSpace c
    · rfl
    · have := toNat_le_of_isSpace h
      have := lt_toNat_of_isTokenStart hc
      exfalso
      omega
  rw [idleStep_of_ne d n (toNat_ne_of_isTokenStart hc) hs, isDigit_of_isTokenStart hc, hc]
  rfl

/-- The characters of a token after its first extend the bare atom being read. -/
theorem foldl_bareChars (cs : List Char) (hcs : cs.all isTokenChar) :
    ∀ (d : List Tok) (b : List Char) (g : Bool),
      cs.foldl lexStep ⟨d, b, .bare, 0, g, true⟩ = ⟨d, cs.reverse ++ b, .bare, 0, g, true⟩ :=
  List.rec (motive := fun cs ↦ cs.all isTokenChar → ∀ (d : List Tok) (b : List Char) (g : Bool),
      cs.foldl lexStep ⟨d, b, .bare, 0, g, true⟩ = ⟨d, cs.reverse ++ b, .bare, 0, g, true⟩)
    (fun _ _ _ _ ↦ rfl)
    (fun c cs ih hall d b g ↦ by
      simp only [List.all_cons, Bool.and_eq_true] at hall
      rw [List.foldl_cons, show lexStep ⟨d, b, .bare, 0, g, true⟩ c =
        ⟨d, c :: b, .bare, 0, g, true⟩ by simp [lexStep, hall.1], ih hall.2]
      simp) cs hcs

/-- The digits of a numeral after its first extend the numeral being read. -/
theorem foldl_numChars (cs : List Char) (hcs : cs.all isDigit) :
    ∀ (d : List Tok) (b : List Char) (g : Bool),
      cs.foldl lexStep ⟨d, b, .numeral, 0, g, true⟩ = ⟨d, cs.reverse ++ b, .numeral, 0, g, true⟩ :=
  List.rec (motive := fun cs ↦ cs.all isDigit → ∀ (d : List Tok) (b : List Char) (g : Bool),
      cs.foldl lexStep ⟨d, b, .numeral, 0, g, true⟩ = ⟨d, cs.reverse ++ b, .numeral, 0, g, true⟩)
    (fun _ _ _ _ ↦ rfl)
    (fun c cs ih hall d b g ↦ by
      simp only [List.all_cons, Bool.and_eq_true] at hall
      rw [List.foldl_cons, show lexStep ⟨d, b, .numeral, 0, g, true⟩ c =
        ⟨d, c :: b, .numeral, 0, g, true⟩ by simp [lexStep, hall.1], ih hall.2]
      simp) cs hcs

/-- The characters of a hole's name after its first extend the name being read. -/
theorem foldl_holeChars (cs : List Char) (hcs : cs.all isTokenChar) :
    ∀ (d : List Tok) (b : List Char) (g : Bool), b ≠ [] →
      cs.foldl lexStep ⟨d, b, .hole, 0, g, true⟩ = ⟨d, cs.reverse ++ b, .hole, 0, g, true⟩ :=
  List.rec (motive := fun cs ↦ cs.all isTokenChar → ∀ (d : List Tok) (b : List Char) (g : Bool),
      b ≠ [] → cs.foldl lexStep ⟨d, b, .hole, 0, g, true⟩ = ⟨d, cs.reverse ++ b, .hole, 0, g, true⟩)
    (fun _ _ _ _ _ ↦ rfl)
    (fun c cs ih hall d b g hb ↦ by
      simp only [List.all_cons, Bool.and_eq_true] at hall
      have he : b.isEmpty = false := List.isEmpty_eq_false_iff.mpr hb
      rw [List.foldl_cons, show lexStep ⟨d, b, .hole, 0, g, true⟩ c =
        ⟨d, c :: b, .hole, 0, g, true⟩ by simp [lexStep, hall.1, he],
        ih hall.2 d (c :: b) g (List.cons_ne_nil c b)]
      simp) cs hcs

/-- The characters of a comment extend the comment being read. -/
theorem foldl_commentChars (cs : List Char) (hcs : cs.all (· != '\n')) :
    ∀ (d : List Tok) (b : List Char) (g : Bool),
      cs.foldl lexStep ⟨d, b, .comment, 0, g, true⟩ = ⟨d, cs.reverse ++ b, .comment, 0, g, true⟩ :=
  List.rec (motive := fun cs ↦ cs.all (· != '\n') → ∀ (d : List Tok) (b : List Char) (g : Bool),
      cs.foldl lexStep ⟨d, b, .comment, 0, g, true⟩ = ⟨d, cs.reverse ++ b, .comment, 0, g, true⟩)
    (fun _ _ _ _ ↦ rfl)
    (fun c cs ih hall d b g ↦ by
      simp only [List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq] at hall
      rw [List.foldl_cons, show lexStep ⟨d, b, .comment, 0, g, true⟩ c =
        ⟨d, c :: b, .comment, 0, g, true⟩ by simp [lexStep, hall.1],
        ih (by simpa using hall.2) d (c :: b) g]
      simp) cs hcs

/-- The second digit of a hexadecimal escape ends it, extending the string being read by the
character the two digits give. -/
theorem lexStep_hex_last {d : List Tok} {b : List Char} {g : Bool} {v k : ℕ} {ch : Char}
    (h : hexVal ch = some k) :
    lexStep ⟨d, b, .hex 1 v none, 0, g, true⟩ ch =
      ⟨d, Char.ofNat (16 * v + k) :: b, .str none, 0, g, true⟩ := by
  unfold lexStep
  rw [h]
  rfl

/-- A character of a quoted string, as a lawful spelling writes it, extends the string being
read. -/
theorem foldl_escape {sp : Spelling} (hsp : sp.Lawful) (c : Char) (hc : isByte c)
    (d : List Tok) (b : List Char) (g : Bool) :
    (sp.escape c).foldl lexStep ⟨d, b, .str none, 0, g, true⟩ =
      ⟨d, c :: b, .str none, 0, g, true⟩ := by
  unfold Spelling.escape
  split_ifs with hp hq
  · have hp' := hsp.plain c hp
    have h1 : c ≠ '"' := by rintro rfl; exact absurd hp' (by decide)
    have h2 : c ≠ '\\' := by rintro rfl; exact absurd hp' (by decide)
    simp only [List.foldl_cons, List.foldl_nil, lexStep, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, strStep, beq_iff_eq, h1, h2, hp', Bool.true_or]
  · simp only [Bool.or_eq_true, beq_iff_eq] at hq
    rcases hq with rfl | rfl <;> rfl
  · have hlt : c.toNat < 256 := of_decide_eq_true hc
    have hx : hexVal (hexDigit (c.toNat / 16)) = some (c.toNat / 16) :=
      hexVal_hexDigit ⟨c.toNat / 16, (Nat.div_lt_iff_lt_mul (by decide)).mpr hlt⟩
    have hy : hexVal (hexDigit (c.toNat % 16)) = some (c.toNat % 16) :=
      hexVal_hexDigit ⟨c.toNat % 16, Nat.mod_lt _ (by decide)⟩
    have e1 : lexStep ⟨d, b, .str none, 0, g, true⟩ '\\' = ⟨d, b, .esc none, 0, g, true⟩ := rfl
    have e2 : lexStep ⟨d, b, .esc none, 0, g, true⟩ 'x' = ⟨d, b, .hex 0 0 none, 0, g, true⟩ := rfl
    have e3 : lexStep ⟨d, b, .hex 0 0 none, 0, g, true⟩ (hexDigit (c.toNat / 16)) =
        ⟨d, b, .hex 1 (c.toNat / 16) none, 0, g, true⟩ := by
      simp only [lexStep, hx, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
      rfl
    have e4 : lexStep ⟨d, b, .hex 1 (c.toNat / 16) none, 0, g, true⟩ (hexDigit (c.toNat % 16)) =
        ⟨d, c :: b, .str none, 0, g, true⟩ := by
      rw [lexStep_hex_last hy, Nat.div_add_mod, Char.ofNat_toNat]
    simp only [List.foldl_cons, List.foldl_nil, e1, e2, e3, e4]

/-- The characters of a quoted string, as a lawful spelling writes them, extend the string being
read. -/
theorem foldl_escapes {sp : Spelling} (hsp : sp.Lawful) (cs : List Char)
    (hcs : cs.all isByte) : ∀ (d : List Tok) (b : List Char) (g : Bool),
      (cs.flatMap sp.escape).foldl lexStep ⟨d, b, .str none, 0, g, true⟩ =
        ⟨d, cs.reverse ++ b, .str none, 0, g, true⟩ :=
  List.rec (motive := fun cs ↦ cs.all isByte → ∀ (d : List Tok) (b : List Char) (g : Bool),
      (cs.flatMap sp.escape).foldl lexStep ⟨d, b, .str none, 0, g, true⟩ =
        ⟨d, cs.reverse ++ b, .str none, 0, g, true⟩)
    (fun _ _ _ _ ↦ rfl) (fun c cs ih hall d b g ↦ by
      simp only [List.all_cons, Bool.and_eq_true] at hall
      rw [List.flatMap_cons, List.foldl_append, foldl_escape hsp c hall.1, ih hall.2]
      simp) cs hcs

/-- A line break between tokens is counted. -/
theorem idleStep_newline (d : List Tok) (n : ℕ) : idleStep d n '\n' = .idle d (n + 1) := rfl

/-- The separator {name}`sepFor` chooses writes an empty line exactly when the token records
one. -/
theorem gap_sepFor (prev : Option Tok) (t : Tok) (b : Bool) (k : ℕ) :
    t.gap = decide (2 ≤ (sepFor prev t b k).breaks) := by
  unfold sepFor
  split_ifs with h1 h2 h3 <;> simp_all [Sep.breaks]

/-- A token read between tokens, after a separator of as many line breaks as the token's record
of an empty line requires, is emitted, or left pending when it is a bare atom, a comment or a
hole, its atom written by a lawful spelling. -/
theorem foldl_tok {sp : Spelling} (hsp : sp.Lawful) (t : Tok) (d : List Tok) (n : ℕ)
    (ht : t.wf) (hg : t.gap = decide (2 ≤ n)) :
    (t.render sp).foldl lexStep (.idle d n) =
      state (t.emitted sp ++ d) (pendOf sp (some t)) := by
  cases t with
  | lp g =>
    simp only [Tok.gap] at hg
    subst hg
    rfl
  | rp => rfl
  | comment g s =>
    simp only [Tok.gap] at hg
    simp only [Tok.wf, Bool.and_eq_true] at ht
    subst hg
    simp only [Tok.render, List.foldl_cons]
    rw [show lexStep (.idle d n) ';' = ⟨d, [], .comment, 0, decide (2 ≤ n), true⟩ from rfl,
      foldl_commentChars s ht.1]
    simp [state, pendOf, Tok.emitted]
  | hole g s =>
    simp only [Tok.gap] at hg
    simp only [Tok.wf] at ht
    subst hg
    cases s with
    | nil => simp [isToken] at ht
    | cons c cs =>
      simp only [isToken, Bool.and_eq_true] at ht
      have hc : lexStep ⟨d, [], .hole, 0, decide (2 ≤ n), true⟩ c =
          ⟨d, [c], .hole, 0, decide (2 ≤ n), true⟩ := by
        simp [lexStep, isDigit_of_isTokenStart ht.1, isTokenChar, ht.1]
      simp only [Tok.render, List.foldl_cons]
      rw [show lexStep (.idle d n) '?' = ⟨d, [], .hole, 0, decide (2 ≤ n), true⟩ from rfl, hc,
        foldl_holeChars cs ht.2 d [c] _ (List.cons_ne_nil c [])]
      simp [state, pendOf, Tok.emitted]
  | atom g s =>
    simp only [Tok.gap] at hg
    simp only [Tok.wf] at ht
    subst hg
    by_cases hb : sp.bare s = true
    · have hsp' : sp.spell s = s := by simp [Spelling.spell, hb]
      rcases hsp.bare s hb with hB | hamp
      · have hb' := hB
        simp only [isBare, Bool.or_eq_true] at hb'
        cases s with
        | nil => simp [isNumeral, isToken] at hb'
        | cons c cs =>
          rcases hb' with hn | htk
          · simp only [isNumeral, List.isEmpty_cons, Bool.not_false, List.all_cons,
              Bool.true_and, Bool.and_eq_true] at hn
            rw [Tok.render, hsp', List.foldl_cons,
              show lexStep (.idle d n) c = idleStep d n c from rfl, idleStep_digit d n hn.1,
              foldl_numChars cs hn.2]
            simp [state, pendOf, Tok.emitted, hb, hB, isNumeral, hn.1, hn.2]
          · simp only [isToken, Bool.and_eq_true] at htk
            have hnn : isNumeral (c :: cs) = false := by
              simp [isNumeral, isDigit_of_isTokenStart htk.1]
            rw [Tok.render, hsp', List.foldl_cons,
              show lexStep (.idle d n) c = idleStep d n c from rfl, idleStep_tokenStart d n htk.1,
              foldl_bareChars cs htk.2]
            simp [state, pendOf, Tok.emitted, hb, hB, hnn]
      · subst hamp
        rw [Tok.render, hsp']
        simp only [Tok.emitted, pendOf, hb, Bool.true_and,
          show isBare ['&'] = false from rfl, Bool.false_eq_true, ↓reduceIte]
        rfl
    · simp only [Bool.not_eq_true] at hb
      have hsp' : sp.spell s = '"' :: (s.flatMap sp.escape ++ ['"']) := by
        unfold Spelling.spell
        rw [hb]
        rfl
      rw [Tok.render, hsp', List.foldl_cons,
        show lexStep (.idle d n) '"' = ⟨d, [], .str none, 0, decide (2 ≤ n), true⟩ from rfl,
        List.foldl_append, foldl_escapes hsp s ht, List.append_nil]
      change LexState.idle (.atom _ s.reverse.reverse :: d) 0 = _
      simp only [List.reverse_reverse, Tok.emitted, pendOf, hb, Bool.false_and,
        Bool.false_eq_true, ↓reduceIte, List.singleton_append]
      rfl

/-- The token a token leaves pending is the token itself. -/
theorem eq_of_pendOf {sp : Spelling} {prev : Option Tok} {p : Tok} (h : pendOf sp prev = some p) :
    prev = some p := by
  rcases prev with _ | ⟨_ | _ | ⟨g, s⟩ | ⟨g, s⟩ | ⟨g, s⟩⟩ <;>
    simp only [pendOf, reduceCtorEq, Option.some.injEq, Option.ite_none_right_eq_some] at h
  all_goals first | exact congrArg some h | exact congrArg some h.2

/-- A character that cannot continue a token ends the bare atom being read. -/
theorem lexStep_bare_end {d : List Tok} {b : List Char} {g : Bool} {ch : Char}
    (h : isTokenChar ch = false) :
    lexStep ⟨d, b, .bare, 0, g, true⟩ ch = idleStep (.atom g b.reverse :: d) 0 ch := by
  change (if isTokenChar ch then (⟨d, ch :: b, .bare, 0, g, true⟩ : LexState)
    else idleStep (.atom g b.reverse :: d) 0 ch) = _
  rw [h]
  rfl

/-- A character that is neither a digit nor begins a length ends the numeral being read. -/
theorem lexStep_numeral_end {d : List Tok} {b : List Char} {g : Bool} {ch : Char}
    (h₁ : isDigit ch = false)
    (h₂ : (isTokenChar ch || ch == '"' || ch == '#' || ch == '|') = false) :
    lexStep ⟨d, b, .numeral, 0, g, true⟩ ch = idleStep (.atom g b.reverse :: d) 0 ch := by
  change (if isDigit ch then (⟨d, ch :: b, .numeral, 0, g, true⟩ : LexState)
    else if isTokenChar ch || ch == '"' || ch == '#' || ch == '|' then
      lengthStep ⟨d, b, .numeral, 0, g, true⟩ ch
    else idleStep (.atom g b.reverse :: d) 0 ch) = _
  rw [h₁, h₂]
  rfl

/-- A character that cannot continue a token ends the name of the hole being read. -/
theorem lexStep_hole_end {d : List Tok} {b : List Char} {g : Bool} {ch : Char}
    (hb : b.isEmpty = false) (h : isTokenChar ch = false) :
    lexStep ⟨d, b, .hole, 0, g, true⟩ ch = idleStep (.hole g b.reverse :: d) 0 ch := by
  change (if isTokenChar ch && !(b.isEmpty && isDigit ch) then
      (⟨d, ch :: b, .hole, 0, g, true⟩ : LexState)
    else if b.isEmpty then .fail
    else idleStep (.hole g b.reverse :: d) 0 ch) = _
  rw [h, hb]
  rfl

/-- A space, a line break or a closing parenthesis ends a pending bare atom or hole, and a line
break a pending comment, as if read between tokens after it. -/
theorem lexStep_pend {sp : Spelling} {prev : Option Tok} {p : Tok} (hp : pendOf sp prev = some p)
    (hw : prev.all Tok.wf) (d : List Tok) (ch : Char) (hch : ch = ' ' ∨ ch = '\n' ∨ ch = ')')
    (hc : p.isComment → ch = '\n') :
    lexStep (state d (some p)) ch = idleStep (p :: d) 0 ch := by
  have h₁ : isDigit ch = false := by rcases hch with rfl | rfl | rfl <;> rfl
  have h₂ : isTokenChar ch = false := by rcases hch with rfl | rfl | rfl <;> rfl
  have h₃ : (isTokenChar ch || ch == '"' || ch == '#' || ch == '|') = false := by
    rcases hch with rfl | rfl | rfl <;> rfl
  rcases prev with _ | ⟨_ | _ | ⟨g, s⟩ | ⟨g, s⟩ | ⟨g, s⟩⟩ <;>
    simp only [pendOf, reduceCtorEq, Option.some.injEq, Option.ite_none_right_eq_some] at hp
  · obtain ⟨-, rfl⟩ := hp
    change lexStep ⟨d, s.reverse, if isNumeral s then .numeral else .bare, 0, g, true⟩ ch = _
    cases hn : isNumeral s
    · exact (lexStep_bare_end h₂).trans (by rw [List.reverse_reverse])
    · exact (lexStep_numeral_end h₁ h₃).trans (by rw [List.reverse_reverse])
  · subst hp
    obtain rfl := hc rfl
    change LexState.idle (.comment g s.reverse.reverse :: d) 1 = _
    rw [List.reverse_reverse, idleStep_newline]
  · subst hp
    have hne : s.reverse.isEmpty = false := by
      cases s with
      | nil => exact absurd hw (by simp [Tok.wf, isToken])
      | cons c cs => exact List.isEmpty_eq_false_iff.mpr (by simp)
    change lexStep ⟨d, s.reverse, .hole, 0, g, true⟩ ch = _
    rw [lexStep_hole_end hne h₂, List.reverse_reverse]

/-- After a pending token, {name}`sepFor` writes nothing only before a closing parenthesis, and
after a comment it writes a line break. -/
theorem sepFor_pend {sp : Spelling} {prev : Option Tok} {p : Tok} (hp : pendOf sp prev = some p)
    (t : Tok) (b : Bool) (k : ℕ) :
    (sepFor prev t b k = .none → t = .rp) ∧
      (p.isComment → sepFor prev t b k = .line k ∨ sepFor prev t b k = .blank k) := by
  obtain rfl := eq_of_pendOf hp
  constructor
  · intro h
    unfold sepFor at h
    rcases p with _ | _ | ⟨g, s⟩ | ⟨g, s⟩ | ⟨g, s⟩ <;> simp [pendOf] at hp <;>
      cases t <;> split_ifs at h <;> simp_all [Tok.isRp, Tok.isLp, Tok.isComment]
  · intro hc
    unfold sepFor
    split_ifs <;> simp_all [Tok.isComment, Option.any]

/-- A token read after the separator {name}`sepFor` chooses, from the state its predecessor
left, emits the predecessor if it was pending and leaves the lexer in the state after the
token. -/
theorem foldl_step {sp : Spelling} (hsp : sp.Lawful) (prev : Option Tok) (t : Tok) (b : Bool)
    (k : ℕ) (done : List Tok) (hp : prev.all Tok.wf) (ht : t.wf) :
    ((sepFor prev t b k).render ++ t.render sp).foldl lexStep (state done (pendOf sp prev)) =
      state (t.emitted sp ++ ((pendOf sp prev).toList ++ done)) (pendOf sp (some t)) := by
  have hg := gap_sepFor prev t b k
  rw [List.foldl_append]
  cases hq : pendOf sp prev with
  | none =>
    rw [show state done none = .idle done 0 from rfl, foldl_sep]
    simpa using foldl_tok hsp t done _ ht hg
  | some p =>
    obtain ⟨hnone, hcom⟩ := sepFor_pend hq t b k
    simp only [Option.toList_some, List.singleton_append]
    cases hs : sepFor prev t b k with
    | none =>
      obtain rfl := hnone hs
      simp only [Sep.render, List.foldl_nil, Tok.render, List.foldl_cons]
      rw [lexStep_pend hq hp done ')' (by simp) (fun h ↦ by simpa [hs] using hcom h)]
      rfl
    | space =>
      rw [hs] at hg
      simp only [Sep.render, List.foldl_cons, List.foldl_nil]
      rw [lexStep_pend hq hp done ' ' (by simp) (fun h ↦ by simpa [hs] using hcom h)]
      exact foldl_tok hsp t _ 0 ht hg
    | line j =>
      rw [hs] at hg
      simp only [Sep.render, List.foldl_cons]
      rw [lexStep_pend hq hp done '\n' (by simp) (fun _ ↦ rfl)]
      exact (congrArg (fun s ↦ (t.render sp).foldl lexStep s) (foldl_spaces _ 1 j)).trans
        (foldl_tok hsp t _ 1 ht hg)
    | blank j =>
      rw [hs] at hg
      simp only [Sep.render, List.foldl_cons]
      rw [lexStep_pend hq hp done '\n' (by simp) (fun _ ↦ rfl)]
      exact (congrArg (fun s ↦ (t.render sp).foldl lexStep s) (foldl_spaces _ 2 j)).trans
        (foldl_tok hsp t _ 2 ht hg)

/-- A token is what it emits followed by what it leaves pending. -/
theorem emitted_pendOf (sp : Spelling) (t : Tok) :
    t.emitted sp ++ (pendOf sp (some t)).toList = [t] := by
  cases t with
  | atom g s => by_cases hb : (sp.bare s && isBare s) = true <;> simp [Tok.emitted, pendOf, hb]
  | _ => rfl

/-- The lexer reads back the tokens a layout arranges, after those already emitted and the
one pending, whatever the layout chooses. -/
theorem lexEnd_arrangeFrom {sp : Spelling} (hsp : sp.Lawful) (L : ℕ → Bool × ℕ) (toks : List Tok)
    (htoks : toks.all Tok.wf) :
    ∀ (prev : Option Tok) (i : ℕ) (done : List Tok), prev.all Tok.wf →
      lexEnd ((render sp (arrangeFrom L toks prev i) ++ ['\n']).foldl lexStep
        (state done (pendOf sp prev))) = some (done.reverse ++ (pendOf sp prev).toList ++ toks) :=
  List.rec (motive := fun toks ↦ toks.all Tok.wf →
      ∀ (prev : Option Tok) (i : ℕ) (done : List Tok), prev.all Tok.wf →
      lexEnd ((render sp (arrangeFrom L toks prev i) ++ ['\n']).foldl lexStep
        (state done (pendOf sp prev))) = some (done.reverse ++ (pendOf sp prev).toList ++ toks))
    (fun _ prev _ done hp ↦ by
      change lexEnd (lexStep (state done (pendOf sp prev)) '\n') = _
      cases hq : pendOf sp prev with
      | none =>
        rw [show state done none = .idle done 0 from rfl, lexStep_newline]
        simp [LexState.idle, lexEnd]
      | some p =>
        rw [lexStep_pend hq hp done '\n' (by simp) (fun _ ↦ rfl), idleStep_newline]
        simp [LexState.idle, lexEnd])
    (fun t rest ih hall prev i done hp ↦ by
      simp only [List.all_cons, Bool.and_eq_true] at hall
      have hstep := foldl_step hsp prev t (L i).1 (L i).2 done hp hall.1
      have harr : arrangeFrom L (t :: rest) prev i =
          (sepFor prev t (L i).1 (L i).2, t) :: arrangeFrom L rest (some t) (i + 1) := rfl
      rw [harr, render, List.flatMap_cons, ← render, List.append_assoc, List.foldl_append,
        hstep, ih hall.2 (some t) (i + 1) _ (by simpa using hall.1)]
      have he := emitted_pendOf sp t
      congr 1
      rcases hq : pendOf sp prev with _ | q <;> cases t <;>
        simp_all [Tok.emitted, pendOf] <;> split_ifs <;> simp_all) toks htoks

/-- A character that may begin a token is a byte. -/
theorem isByte_of_isTokenStart {c : Char} (h : isTokenStart c) : isByte c := by
  unfold isTokenStart at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  unfold isByte
  apply decide_eq_true
  rcases h with (((((((((⟨-, h⟩ | ⟨-, h⟩) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl) | rfl)
  all_goals first | omega | decide

/-- A character that may continue a token is a byte. -/
theorem isByte_of_isTokenChar {c : Char} (h : isTokenChar c) : isByte c := by
  unfold isTokenChar at h
  rcases Bool.or_eq_true _ _ ▸ h with h | h
  · exact isByte_of_isTokenStart h
  · unfold isDigit at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact decide_eq_true (by omega)

/-- A token is of bytes. -/
theorem all_isByte_of_isToken {s : List Char} (h : isToken s) : s.all isByte := by
  cases s with
  | nil => exact absurd h (by decide)
  | cons c cs =>
    simp only [isToken, Bool.and_eq_true] at h
    rw [List.all_cons, isByte_of_isTokenStart h.1, Bool.true_and]
    exact List.all_eq_true.mpr fun x hx ↦ isByte_of_isTokenChar (List.all_eq_true.mp h.2 x hx)

/-- The hexadecimal digit of a number below sixteen is a byte. -/
theorem isByte_hexDigit : ∀ n : Fin 16, isByte (hexDigit n) := by decide

/-- A byte of a quoted string, as a spelling writes it, is of bytes. -/
theorem escape_bytes (sp : Spelling) {c : Char} (hc : isByte c) : (sp.escape c).all isByte := by
  have hlt : c.toNat < 256 := of_decide_eq_true hc
  unfold Spelling.escape
  split_ifs
  · simp [hc]
  · simp [isByte, hlt]
  · simp only [List.all_cons, List.all_nil, Bool.and_true]
    rw [isByte_hexDigit ⟨c.toNat / 16, (Nat.div_lt_iff_lt_mul (by decide)).mpr hlt⟩,
      isByte_hexDigit ⟨c.toNat % 16, Nat.mod_lt _ (by decide)⟩]
    rfl

/-- An atom of bytes, as a spelling writes it, is of bytes. -/
theorem spell_bytes (sp : Spelling) {s : List Char} (hs : s.all isByte) :
    (sp.spell s).all isByte := by
  unfold Spelling.spell
  split
  · exact hs
  · simp only [List.all_cons, List.all_append, List.all_flatMap, List.all_nil, Bool.and_true]
    rw [List.all_eq_true.mpr fun c hc ↦ escape_bytes sp (List.all_eq_true.mp hs c hc)]
    rfl

/-- A separator is of bytes. -/
theorem sep_bytes (sp : Sep) : sp.render.all isByte := by
  have hr : ∀ k, (List.replicate k ' ').all isByte := fun k ↦
    List.all_eq_true.mpr fun c hc ↦ by
      rw [List.eq_of_mem_replicate hc]
      rfl
  cases sp with
  | none => rfl
  | space => rfl
  | line k => exact (List.all_cons ..).trans (by rw [hr k]; rfl)
  | blank k =>
    rw [Sep.render, List.all_cons, List.all_cons, hr k]
    rfl

/-- A well-formed token, as a spelling writes it, is of bytes. -/
theorem render_bytes (sp : Spelling) {t : Tok} (ht : t.wf) : (t.render sp).all isByte := by
  cases t with
  | lp => rfl
  | rp => rfl
  | atom g s => exact spell_bytes sp ht
  | comment g s =>
    simp only [Tok.wf, Bool.and_eq_true] at ht
    rw [Tok.render, List.all_cons, ht.2]
    rfl
  | hole g s =>
    rw [Tok.render, List.all_cons, all_isByte_of_isToken ht]
    rfl

/-- A layout arranges the tokens it is given. -/
theorem arrangeFrom_snd (L : ℕ → Bool × ℕ) : ∀ (toks : List Tok) (prev : Option Tok) (i : ℕ),
    (arrangeFrom L toks prev i).map Prod.snd = toks :=
  List.rec (fun _ _ ↦ rfl) fun t toks ih prev i ↦ by
    change (_ :: (arrangeFrom L toks (some t) (i + 1)).map Prod.snd) = _
    rw [ih]

/-- Well-formed tokens laid out by a layout are of bytes. -/
theorem printed_bytes (sp : Spelling) (L : ℕ → Bool × ℕ) (toks : List Tok)
    (h : toks.all Tok.wf) : (render sp (arrangeFrom L toks none 0) ++ ['\n']).all isByte := by
  rw [List.all_append, render, List.all_flatMap]
  refine (congrArg (· && _) (List.all_eq_true.mpr fun p hp ↦ ?_)).trans rfl
  have ht : p.2 ∈ toks := arrangeFrom_snd L toks none 0 ▸ List.mem_map_of_mem hp
  rw [List.all_append, sep_bytes, render_bytes sp (List.all_eq_true.mp h _ ht)]
  rfl

/-- The lexer reads back the tokens a layout arranges, whatever the layout. -/
theorem lex_print {sp : Spelling} (hsp : sp.Lawful) (L : ℕ → Bool × ℕ) (toks : List Tok)
    (h : toks.all Tok.wf) :
    lex (render sp (arrangeFrom L toks none 0) ++ ['\n']) = some toks := by
  have h' := lexEnd_arrangeFrom hsp L _ h none 0 [] rfl
  simp only [pendOf, Option.toList_none, List.reverse_nil, List.nil_append] at h'
  rw [lex_of_bytes (printed_bytes sp L toks h)]
  exact h'

/-- The name of a hole whose form a node is, when the printer writes it {lit}`?name`: a list
without closing comment lines of the keyword and a token, each an atom without trivia. -/
def holeName? (l : Trivia × Option (List Char)) (cs : List SExpr) : Option (List Char) :=
  match l.2, l.1.close, cs with
  | none, [], [a, b] =>
    match a.label, b.label with
    | (ta, some h), (tb, some n) =>
      if ta == .none && h == kwHole && a.children.isEmpty && tb == .none && b.children.isEmpty &&
          isToken n then some n
      else none
    | _, _ => none
  | _, _, _ => none

/-- The token of a comment line. -/
def Line.tok (l : Line) : Tok := .comment l.gap l.text

/-- The tokens of an S-expression: the comment lines before it, then a hole, an atom, or a
list's parentheses around the tokens of its elements and the comment lines before its end. -/
def tokensOf : SExpr → List Tok :=
  RoseTree.para fun l rs ↦
    l.1.lead.map Line.tok ++
      match holeName? l (rs.map Prod.fst) with
      | some n => [.hole l.1.gap n]
      | none =>
        match l.2 with
        | some s => [.atom l.1.gap s]
        | none => .lp l.1.gap :: (rs.map Prod.snd).flatten ++ l.1.close.map Line.tok ++ [.rp]

/-- The tokens of a document. -/
def Doc.tokens (d : Doc) : List Tok := d.items.flatMap tokensOf ++ d.trail.map Line.tok

/-- A document's characters, laid out by a layout, a choice at each position of the document's
tokens; the text ends with a line break. -/
def print (L : ℕ → Bool × ℕ) (d : Doc) : List Char :=
  render .profile (arrangeFrom L d.tokens none 0) ++ ['\n']

/-! ## Reading what the printer writes -/

/-- Whether a comment line can be printed and read back: it contains no line break, and it is
of bytes. -/
def Line.wf (l : Line) : Bool := l.text.all (· != '\n') && l.text.all isByte

/-- Whether an S-expression can be printed and read back: its comment lines are well formed, and
an atom is of bytes and has no children and no closing comment lines. -/
def wf : SExpr → Bool :=
  RoseTree.elim fun l rs ↦
    l.1.lead.all Line.wf &&
      match l.2 with
      | some s => rs.isEmpty && l.1.close.isEmpty && s.all isByte
      | none => l.1.close.all Line.wf && rs.all id

/-- Whether a document can be printed and read back. -/
def Doc.wf (d : Doc) : Bool := d.items.all Document.wf && d.trail.all Line.wf

/-- The tokens of a node. -/
theorem tokensOf_node (l : Trivia × Option (List Char)) (cs : List SExpr) :
    tokensOf (RoseTree.node l cs) =
      l.1.lead.map Line.tok ++
        match holeName? l cs with
        | some n => [.hole l.1.gap n]
        | none =>
          match l.2 with
          | some s => [.atom l.1.gap s]
          | none => .lp l.1.gap :: cs.flatMap tokensOf ++ l.1.close.map Line.tok ++ [.rp] := by
  simp [tokensOf, List.flatMap_def, Function.comp_def]

/-- A node whose hole name is given is the form of that hole. -/
theorem eq_holeForm_of_holeName? {l : Trivia × Option (List Char)} {cs : List SExpr}
    {n : List Char} (h : holeName? l cs = some n) :
    RoseTree.node l cs = holeForm ⟨l.1.lead, l.1.gap, []⟩ n ∧ isToken n := by
  unfold holeName? at h
  split at h
  · rename_i _ _ _ a b hk hc
    split at h
    · rename_i ta h' tb m ha hb
      simp only [Bool.and_eq_true, beq_iff_eq, List.isEmpty_iff] at h
      split_ifs at h with hcond
      obtain ⟨⟨⟨⟨⟨rfl, rfl⟩, hca⟩, rfl⟩, hcb⟩, htok⟩ := hcond
      cases h
      obtain ⟨⟨lead, gap, close⟩, k⟩ := l
      simp only at hk hc
      subst hk hc
      refine ⟨?_, htok⟩
      rw [← RoseTree.node_label_children a, ← RoseTree.node_label_children b, ha, hb, hca, hcb]
      rfl
    · simp at h
  · simp at h

/-- A well-formed atom has no children and no closing comment lines. -/
theorem wf_atom (tr : Trivia) (s : List Char) (cs : List SExpr) :
    wf (RoseTree.node (tr, some s) cs) =
      (tr.lead.all Line.wf && (cs.isEmpty && tr.close.isEmpty && s.all isByte)) := by
  simp [wf]

/-- A list is well formed when its comment lines and its elements are. -/
theorem wf_list (tr : Trivia) (cs : List SExpr) :
    wf (RoseTree.node (tr, none) cs) =
      (tr.lead.all Line.wf && (tr.close.all Line.wf && cs.all wf)) := by
  simp [wf, List.all_map]

/-- The tokens of well-formed comment lines can be printed and read back. -/
theorem all_wf_toks {ls : List Line} (h : ls.all Line.wf) : (ls.map Line.tok).all Tok.wf := by
  simpa [List.all_map, Function.comp_def, Line.tok, Tok.wf, Line.wf] using h

/-- The tokens of a well-formed S-expression can be printed and read back. -/
theorem all_wf_tokensOf : ∀ t : SExpr, wf t → (tokensOf t).all Tok.wf :=
  RoseTree.ind fun l cs ih h ↦ by
    rw [tokensOf_node]
    cases hn : holeName? l cs with
    | some n =>
      have hl : l.1.lead.all Line.wf := by
        obtain ⟨tr, _ | s⟩ := l
        · rw [wf_list] at h
          exact (Bool.and_eq_true _ _ ▸ h).1
        · rw [wf_atom] at h
          exact (Bool.and_eq_true _ _ ▸ h).1
      simp [all_wf_toks hl, Tok.wf, (eq_holeForm_of_holeName? hn).2]
    | none =>
      obtain ⟨tr, k⟩ := l
      cases k with
      | some s =>
        rw [wf_atom] at h
        simp only [Bool.and_eq_true] at h
        simp [all_wf_toks h.1, Tok.wf, h.2.2]
      | none =>
        rw [wf_list] at h
        simp only [Bool.and_eq_true] at h
        simp only [List.all_append, List.all_cons, List.all_flatMap, Tok.wf,
          all_wf_toks h.1, all_wf_toks h.2.1, Bool.true_and, List.all_nil, Bool.and_true,
          List.all_eq_true]
        exact fun c hc ↦ List.all_eq_true.mp (ih c hc (List.all_eq_true.mp h.2.2 c hc))

/-- Reading comment lines' tokens onto a frame adds them to its pending lines. -/
theorem foldl_readStep_lines (ls : List Line) :
    ∀ f fs, (ls.map Line.tok).foldl readStep (some (f :: fs)) =
      some ({ f with pend := ls.reverse ++ f.pend } :: fs) :=
  List.rec (fun f fs ↦ by simp) (fun l ls ih f fs ↦ by
    simp only [List.map_cons, List.foldl_cons, Line.tok, readStep]
    rw [ih]
    simp) ls

/-- Reading the tokens of well-formed S-expressions onto a frame with no pending lines adds the
S-expressions to it. -/
theorem foldl_readStep_items (cs : List SExpr)
    (ih : ∀ t ∈ cs, wf t → ∀ (f : Frame) fs, f.pend = [] →
      (tokensOf t).foldl readStep (some (f :: fs)) = some (f.push t :: fs))
    (hcs : ∀ c ∈ cs, wf c) :
    ∀ (f : Frame) fs, f.pend = [] → (cs.flatMap tokensOf).foldl readStep (some (f :: fs)) =
      some (⟨f.lead, f.gap, cs.reverse ++ f.items, []⟩ :: fs) :=
  List.rec (motive := fun cs ↦ (∀ t ∈ cs, wf t → ∀ (f : Frame) fs, f.pend = [] →
      (tokensOf t).foldl readStep (some (f :: fs)) = some (f.push t :: fs)) →
      (∀ c ∈ cs, wf c) → ∀ (f : Frame) fs, f.pend = [] →
      (cs.flatMap tokensOf).foldl readStep (some (f :: fs)) =
        some (⟨f.lead, f.gap, cs.reverse ++ f.items, []⟩ :: fs))
    (fun _ _ f fs hf ↦ by
      obtain ⟨a, b, c, d⟩ := f
      simp only at hf
      subst hf
      rfl)
    (fun c cs ihl ih hcs f fs hf ↦ by
      rw [List.flatMap_cons, List.foldl_append,
        ih c List.mem_cons_self (hcs c List.mem_cons_self) f fs hf,
        ihl (fun t ht ↦ ih t (List.mem_cons_of_mem c ht))
          (fun d hd ↦ hcs d (List.mem_cons_of_mem c hd)) _ fs rfl]
      simp [Frame.push]) cs ih hcs

/-- Reading the tokens of a well-formed S-expression onto a frame with no pending lines adds the
S-expression to it. -/
theorem foldl_readStep_tokensOf : ∀ t : SExpr, wf t → ∀ (f : Frame) fs, f.pend = [] →
    (tokensOf t).foldl readStep (some (f :: fs)) = some (f.push t :: fs) :=
  RoseTree.ind fun l cs ih h f fs hf ↦ by
    rw [tokensOf_node, List.foldl_append, foldl_readStep_lines]
    cases hn : holeName? l cs with
    | some n =>
      rw [(eq_holeForm_of_holeName? hn).1]
      simp [readStep, hf, Frame.push]
    | none =>
      obtain ⟨tr, k⟩ := l
      cases k with
      | some s =>
        rw [wf_atom] at h
        simp only [Bool.and_eq_true, List.isEmpty_iff] at h
        obtain ⟨-, ⟨rfl, hc⟩, -⟩ := h
        obtain ⟨lead, gap, close⟩ := tr
        simp only at hc
        subst hc
        simp [readStep, hf, Frame.push]
      | none =>
        rw [wf_list] at h
        simp only [Bool.and_eq_true, List.all_eq_true] at h
        simp only [List.foldl_cons, List.foldl_append, hf, List.append_nil, readStep]
        rw [foldl_readStep_items cs ih h.2.2 _ _ rfl, foldl_readStep_lines]
        simp [Frame.start, Frame.push]

/-- The retraction law: reading a document printed at any layout gives the document back, when
it is well formed. -/
theorem readDoc_print (L : ℕ → Bool × ℕ) (d : Doc) (h : d.wf) :
    readDoc (print L d) = some d := by
  simp only [Doc.wf, Bool.and_eq_true] at h
  have hw : ∀ c ∈ d.items, wf c := List.all_eq_true.mp h.1
  have htoks : d.tokens.all Tok.wf := by
    simp only [Doc.tokens, List.all_append, List.all_flatMap, all_wf_toks h.2, Bool.and_true,
      List.all_eq_true]
    exact fun c hc ↦ List.all_eq_true.mp (all_wf_tokensOf c (hw c hc))
  rw [readDoc, print, lex_print Spelling.lawful_profile L d.tokens htoks, Option.bind_some,
    Doc.tokens,
    List.foldl_append,
    foldl_readStep_items d.items (fun t _ ↦ foldl_readStep_tokensOf t) hw _ [] rfl,
    foldl_readStep_lines]
  simp [Frame.start]

/-! ## A layout policy and the formatter -/

/-- A layout from the column an element's first character is written at and the number of
closing parentheses that follow the element on its line: it appends the choices for the
element's tokens after the first to those made before, and gives the column after the
element. -/
abbrev Plan : Type := ℕ → ℕ → Array (Bool × ℕ) → Array (Bool × ℕ) × ℕ

/-- An element of a list's layout, a comment line or an S-expression, each one token or more:
whether an empty line precedes it, whether it is a comment line or an atom, its width on one
line, if it can be written on one, and its layout. -/
structure Elem where
  /-- Whether an empty line precedes the element. -/
  gap : Bool
  /-- Whether the element is a comment line. -/
  isComment : Bool
  /-- Whether the element is an atom. -/
  isAtom : Bool
  /-- The element's width on one line, or nothing when it cannot be written on one. -/
  width : Option ℕ
  /-- The element's layout. -/
  plan : Plan

/-- The element of a comment line. -/
def Line.elem (l : Line) : Elem :=
  ⟨l.gap, true, false, none, fun c _ acc ↦ (acc, c + 1 + l.text.length)⟩

/-- The elements of a list: each element's comment lines before it and the element, then the
comment lines before the list's end. -/
def elemsOf (rs : List (List Line × Elem)) (close : List Line) : List Elem :=
  rs.flatMap (fun r ↦ r.1.map Line.elem ++ [r.2]) ++ close.map Line.elem

/-- The state of a list's layout between its elements: the current column, whether a line has
been broken before an element after the first, whether the element before was a comment, the
position of the next element, and the choices made. -/
structure PlanState where
  /-- The current column. -/
  col : ℕ
  /-- Whether a line was broken before an element after the first. -/
  broken : Bool
  /-- Whether the element before was a comment. -/
  afterComment : Bool
  /-- The position of the next element. -/
  pos : ℕ
  /-- The choices made for the tokens so far. -/
  out : Array (Bool × ℕ)

/-- Lay out one element of a list whose elements are indented to a column, within a line
width, given the list's number of elements and the closing parentheses that follow the list.
The element begins a line when the list does not fit on one, when it or the element before is
a comment, when a line was broken before an earlier element after the first, or when it and
the parentheses that follow it do not fit on the current line; the first element begins one
only when it or the element before is a comment. -/
def planElem (lim ind n trail : ℕ) (fits : Bool) (s : PlanState) (e : Elem) : PlanState :=
  let after := if s.pos + 1 == n then trail + 1 else 0
  let brk : Bool :=
    if fits || s.pos == 0 then e.isComment || s.afterComment
    else e.isComment || s.afterComment || s.broken ||
      match e.width with
      | some w => lim < s.col + 1 + w + after
      | none => true
  let start := if brk || e.gap || s.afterComment then ind else if s.pos == 0 then s.col
    else s.col + 1
  let (out, endCol) := e.plan start after (s.out.push (brk, ind))
  ⟨endCol, s.broken || (brk && s.pos != 0) || e.gap, e.isComment, s.pos + 1, out⟩

/-- An S-expression's comment lines before it and its element, from its children with their
elements, given a spelling. A hole the spelling abbreviates is one token; an atom is as wide as
its spelling. A list that fits within the
line width is written on one line; otherwise its elements after the first fill the first line
while they fit, and the rest begin lines indented past the list's opening parenthesis, by two
columns after an atom at its head and by one otherwise, so that no line is indented beyond a
parenthesis closed at the end of the line before. A list holding a comment line, or an element
after an empty line, is not written on one line. -/
def planStep (sp : Spelling) (lim : ℕ) (l : Trivia × Option (List Char))
    (rs : List (SExpr × (List Line × Elem))) : List Line × Elem :=
  match if sp.holes then holeName? l (rs.map Prod.fst) else none with
  | some n => (l.1.lead, ⟨l.1.gap, false, false, some (n.length + 1),
      fun c _ acc ↦ (acc, c + 1 + n.length)⟩)
  | none =>
    let es := elemsOf (rs.map Prod.snd) l.1.close
    let w : Option ℕ := match l.2 with
      | some s => some (sp.spell s).length
      | none =>
        if es.any (fun e : Elem ↦ e.gap) then none
        else (es.mapM fun e : Elem ↦ e.width).map fun w ↦ w.sum + w.length - 1 + 2
    (l.1.lead, ⟨l.1.gap, false, l.2.isSome, w, fun c trail acc ↦
      match l.2 with
      | some s => (acc, c + (sp.spell s).length)
      | none =>
        let fits := match w with
          | some w => decide (c + w + trail ≤ lim)
          | none => false
        let ind := c + if (es.head?.map (·.isAtom)).getD false then 2 else 1
        let s := es.foldl (planElem lim ind es.length trail fits) ⟨c + 1, false, false, 0, acc⟩
        let rpCol := if s.afterComment then ind else s.col
        (s.out.push (false, ind), rpCol + 1)⟩)

/-- The layout of a document within a line width, as the choices at the positions of its
tokens, given a spelling: each element after the first, an S-expression or a comment line, begins
a line at the first column, and each is laid out by {name}`planStep`. -/
def defaultLayout (sp : Spelling) (lim : ℕ) (d : Doc) : Array (Bool × ℕ) :=
  (elemsOf (d.items.map (RoseTree.para (planStep sp lim))) d.trail).foldl
    (fun (acc : Array (Bool × ℕ) × Bool) e ↦ ((e.plan 0 0 (acc.1.push (acc.2, 0))).1, true))
    (#[], false) |>.1

/-- A document printed at the choices of a layout, positions beyond them choosing no line
break. -/
def printAt (ds : Array (Bool × ℕ)) (d : Doc) : List Char :=
  print (fun i ↦ ds.getD i (false, 0)) d

/-- The formatter: a text read and printed within a line width, or nothing when its
parentheses do not balance. -/
def format (lim : ℕ) (text : List Char) : Option (List Char) :=
  (readDoc text).bind fun d ↦
    if d.wf then some (printAt (defaultLayout .profile lim d) d) else none

/-- The formatter is idempotent: formatting a formatted text gives it back. -/
theorem format_format (lim : ℕ) (text out : List Char) (h : format lim text = some out) :
    format lim out = some out := by
  unfold format at h
  obtain ⟨d, hr, hout⟩ := Option.bind_eq_some_iff.mp h
  by_cases hw : d.wf = true
  · simp only [hw, ↓reduceIte, Option.some.injEq] at hout
    subst hout
    simp only [format, printAt, readDoc_print _ d hw, Option.bind_some, hw, ↓reduceIte]
  · simp [hw] at hout


end Document

end Geb.Kernel

end
