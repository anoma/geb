/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Kernel.Durable

set_option doc.verso true

/-!
# The markup of comments

The prose of a source document's comments is written in a recorded subset of Verso's markup, the
format of prose that a durable document's profile names ({name}`Geb.Kernel.Document.Profile`),
version {lit}`0` of {lit}`verso`. A block of comment lines, the lines between two empty lines of
the source, is one text of prose: each line's characters after its semicolon and one space, the
lines joined by line breaks. The subset is what a parser can read without guessing, and Verso's
own parser reads each text the subset admits to the same structure, which the tests check
against the parser of Lean's documentation strings.

The blocks of the subset are paragraphs and code blocks. A paragraph is a run of non-empty lines,
none beginning or ending with a space or beginning with an opener of another of Verso's blocks,
and its first line not beginning with {lit}`#`; paragraphs are separated by empty lines. A code
block is a line of three backticks, the lines of its code, none holding three backticks in a row,
and a line of three backticks. The
inline content of a paragraph's line is text, code, and code under a role: a character other than
{lit}`\`, the backtick, the braces, the brackets, {lit}`*` and {lit}`_` is text, as is any
character after {lit}`\`; a dollar sign is not followed by a backtick, which would begin
mathematics; code is a span between single backticks of characters other than the backtick, not
empty and neither beginning nor ending with a space; and a role is one of the four names
{lit}`name`, {lit}`geb`, {lit}`cite` and {lit}`lit` between braces, followed by code.

The roles are those the repository's literate Lean modules use, the role of a citation, which
those modules write {lit}`citeKey`, under the name {lit}`cite`, and one for Geb: {lit}`name`
refers to a Lean constant, {lit}`geb` to a definition of the program, {lit}`cite` to an entry of
the bibliography, and {lit}`lit` marks code that refers to nothing. A reference to a Geb
definition resolves as a qualified name of Lean resolves in its namespaces: in a comment inside
the modules {lit}`M₁ … Mₖ`, the name {lit}`x` refers to the first of {lit}`M₁.….Mₖ.x`, …,
{lit}`M₁.x` and {lit}`x` that the program declares. The notes' links
({name}`Geb.Kernel.Document.Field`) resolve alike, at the scope of the declaration they document.

## Main definitions

* {lit}`Role`, {lit}`Inline`, {lit}`Block` — the roles, inline content and blocks of the subset.
* {lit}`parseLine`, {lit}`parseProse` — a line's inline content, and the blocks of a text.
* {lit}`sitesOf` — the blocks of comments of a document, each with the scope it is written in.
* {lit}`declsOf` — the paths of the declarations of a document.
* {lit}`Resolver`, {lit}`check` — what resolves a reference outside the program, and the check of
  a document's comments and notes against its program's declarations.

## Tags

documentation, markup, comment, reference, Verso
-/

@[expose] public section

namespace Geb.Kernel.Markup

open Document

/-! ## The subset -/

/-- The roles of the subset. -/
inductive Role where
  /-- A Lean constant. -/
  | name
  /-- A definition of the Geb program. -/
  | geb
  /-- An entry of the bibliography. -/
  | cite
  /-- Code that refers to nothing. -/
  | lit
  deriving DecidableEq, Repr

/-- The roles with their names. -/
def Role.all : List (List Char × Role) :=
  [(['n', 'a', 'm', 'e'], .name), (['g', 'e', 'b'], .geb), (['c', 'i', 't', 'e'], .cite),
    (['l', 'i', 't'], .lit)]

/-- The role a name names. -/
def Role.ofName? (s : List Char) : Option Role := Role.all.lookup s

/-- Inline content: text, with its escapes resolved; code; and code under a role. -/
inductive Inline where
  /-- Text. -/
  | text (s : List Char)
  /-- Code. -/
  | code (s : List Char)
  /-- Code under a role. -/
  | role (r : Role) (s : List Char)
  deriving DecidableEq, Repr

/-- A block: a paragraph, its lines' inline content, or a code block, its lines. -/
inductive Block where
  /-- A paragraph. -/
  | para (lines : List (List Inline))
  /-- A code block. -/
  | code (lines : List (List Char))
  deriving DecidableEq, Repr

/-! ## Inline content -/

/-- The state of the reading of a line: the inline content read, with the text after it, and
whether that text ends in a dollar sign; after a backslash; within braces, with the name read; after
a role; or within code, with its role and the characters read. -/
inductive LineState where
  /-- Text, ending in a dollar sign or not. -/
  | text (out : List Inline) (cur : List Char) (dollar : Bool)
  /-- After a backslash. -/
  | esc (out : List Inline) (cur : List Char)
  /-- Within braces. -/
  | brace (out : List Inline) (name : List Char)
  /-- After a role. -/
  | role (out : List Inline) (r : Role)
  /-- Within code. -/
  | code (out : List Inline) (r : Option Role) (cur : List Char)

/-- Inline content followed by the text after it. -/
def flush (out : List Inline) (cur : List Char) : List Inline :=
  if cur.isEmpty then out else out ++ [.text cur]

/-- Whether a character delimits emphasis, a link or a role's name, and so is escaped in text. -/
def isDelimiter (c : Char) : Bool :=
  c == '*' || c == '_' || c == '[' || c == ']' || c == '}'

/-- Whether a character may be part of a role's name. -/
def isNameChar (c : Char) : Bool := c.isAlphanum

/-- The code of a span under a role or none, or what rejects it. -/
def codeOf (r : Option Role) (s : List Char) : Except String Inline :=
  if s.isEmpty then throw "a code span is empty"
  else if s.head? == some ' ' || s.getLast? == some ' ' then
    throw "a code span begins or ends with a space"
  else pure (match r with
    | some r => .role r s
    | none => .code s)

/-- One character of a line read. -/
def lineStep (st : LineState) (c : Char) : Except String LineState :=
  match st with
  | .text out cur dollar =>
    if dollar && c == '`' then throw "a dollar sign before a backtick begins mathematics"
    else if c == '\\' then pure (.esc out cur)
    else if c == '`' then pure (.code (flush out cur) none [])
    else if c == '{' then pure (.brace (flush out cur) [])
    else if isDelimiter c then throw s!"the character {c} is written \\{c} in text"
    else pure (.text out (cur ++ [c]) (c == '$'))
  | .esc out cur => pure (.text out (cur ++ [c]) false)
  | .brace out name =>
    if c == '}' then
      match Role.ofName? name with
      | some r => pure (.role out r)
      | none => throw s!"the role {String.ofList name} is not name, geb, cite or lit"
    else if isNameChar c then pure (.brace out (name ++ [c]))
    else throw "a role is a name between braces"
  | .role out r =>
    if c == '`' then pure (.code out (some r) [])
    else throw "a role is followed by code"
  | .code out r cur =>
    if c == '`' then do return .text (out ++ [← codeOf r cur]) [] false
    else pure (.code out r (cur ++ [c]))

/-- The inline content of a line, or what rejects it. -/
def parseLine (line : List Char) : Except String (List Inline) := do
  match ← line.foldlM lineStep (.text [] [] false) with
  | .text out cur _ => return flush out cur
  | .esc _ _ => throw "a backslash ends the line"
  | .brace _ _ | .role _ _ => throw "a role ends the line without its code"
  | .code _ _ _ => throw "a code span is not closed on its line"

/-! ## Blocks -/

/-- The fence of a code block. -/
def fence : List Char := ['`', '`', '`']

/-- Whether a line holds three backticks in a row, which the fence of a code block holding it
would have to exceed. -/
def hasFence (line : List Char) : Bool :=
  (List.range line.length).any fun i ↦ (line.drop i).take 3 == fence

/-- Whether a line begins with digits followed by a dot or a parenthesis and a space, the marker
of an item of an ordered list. -/
def isNumbering (line : List Char) : Bool :=
  match line.dropWhile Char.isDigit with
  | c :: ' ' :: _ => (line.takeWhile Char.isDigit).length > 0 && (c == '.' || c == ')')
  | _ => false

/-- Whether a line begins with the opener of a block of Verso other than a paragraph: an item of a
list or of a description, a directive, a code block, metadata or a quotation. -/
def isOpener (line : List Char) : Bool :=
  match line with
  | ':' :: ':' :: ':' :: _ | '`' :: '`' :: '`' :: _ | '%' :: '%' :: '%' :: _ | '>' :: _ => true
  | c :: ' ' :: _ => c == '*' || c == '-' || c == '+' || c == ':'
  | _ => isNumbering line

/-- The state of the reading of a text's blocks: the blocks read, and the open paragraph or code
block. -/
inductive ProseState where
  /-- Between blocks. -/
  | idle (out : List Block)
  /-- Within a paragraph. -/
  | para (out : List Block) (lines : List (List Inline))
  /-- Within a code block. -/
  | code (out : List Block) (lines : List (List Char))

/-- The blocks read, the open paragraph closed. -/
def ProseState.closed : ProseState → List Block
  | .idle out => out
  | .para out ls => out ++ [.para ls]
  | .code out _ => out

/-- A line of a paragraph read, or what rejects it, the paragraph's first when it opens one. -/
def paraLine (first : Bool) (line : List Char) : Except String (List Inline) :=
  if line.head? == some ' ' then throw "a line of prose begins with a space"
  else if line.getLast? == some ' ' then throw "a line of prose ends with a space"
  else if first && line.head? == some '#' then throw "a paragraph begins with #, a header"
  else if isOpener line then throw "a line of prose begins as a list, a directive or a quotation"
  else parseLine line

/-- One line of a text read, or what rejects it, with the line. -/
def proseStep (st : ProseState) (line : List Char) : Except String ProseState :=
  let wrap (r : Except String ProseState) : Except String ProseState :=
    r.mapError fun e ↦ s!"{e}: {String.ofList line}"
  match st with
  | .code out ls =>
    if line == fence then pure (.idle (out ++ [.code ls]))
    else if hasFence line then wrap (throw "a line of code holds three backticks")
    else pure (.code out (ls ++ [line]))
  | .idle out =>
    if line.isEmpty then pure st
    else if line == fence then pure (.code out [])
    else wrap do return .para out [← paraLine true line]
  | .para out ls =>
    if line.isEmpty then pure (.idle (out ++ [.para ls]))
    else if line == fence then pure (.code (out ++ [.para ls]) [])
    else wrap do return .para out (ls ++ [← paraLine false line])

/-- The blocks of a text, given as its lines, or what rejects it. -/
def parseProse (lines : List (List Char)) : Except String (List Block) := do
  match ← lines.foldlM proseStep (.idle []) with
  | .code _ _ => throw "a code block is not closed"
  | st => return st.closed

/-! ## Comments in their scopes -/

/-- A comment line's prose: its characters after the semicolon and one space, or nothing for an
empty comment. -/
def proseOf (l : Line) : Except String (List Char) :=
  match l.text with
  | [] => pure []
  | ' ' :: rest => pure rest
  | _ => throw s!"a comment's semicolon is not followed by a space: {String.ofList l.text}"

/-- Comment lines in blocks, a block ending before a line that an empty line precedes. -/
def blocksOf (ls : List Line) : List (List Line) :=
  ls.foldr (fun l acc ↦ match acc with
    | b :: bs => if (b.head?.map (·.gap)).getD false then [l] :: acc else (l :: b) :: bs
    | [] => [[l]]) []

/-- A block of comment lines in its scope: the path of the modules it is written in, a description
of where it stands, and its lines. -/
structure Site where
  /-- The path of the modules the block is written in. -/
  scope : Path
  /-- Where the block stands. -/
  place : String
  /-- The comment lines. -/
  lines : List Line

/-- A path written with dots. -/
def showPath (p : Path) : String := ".".intercalate (p.map String.ofList)

/-- The name of a module a node declares. -/
def moduleName? (t : SExpr) : Option (List Char) :=
  if headIs kwModule t then declName? t else none

/-- The blocks of a run of comment lines, given their scope and where they stand. -/
def sitesAt (scope : Path) (place : String) (ls : List Line) : List Site :=
  (blocksOf ls).map (⟨scope, place, ·⟩)

/-- One node's blocks of comments, from its children's, each a function of the scope and the
place of the node: the blocks before it, those of its children, at the scope of its body when it
is a module, and those before its closing parenthesis. -/
def sitesStep (l : Trivia × Option (List Char)) (rs : List (SExpr × (Path → String → List Site))) :
    Path → String → List Site := fun scope place ↦
  let t := RoseTree.node l (rs.map Prod.fst)
  let inner := match moduleName? t with
    | some m => scope ++ [m]
    | none => scope
  let inside := match (if isDecl t then declName? t else none) with
    | some n => s!"inside {showPath (scope ++ [n])}"
    | none => place
  let before := match (if isDecl t then declName? t else none) with
    | some n => s!"before {showPath (scope ++ [n])}"
    | none => place
  sitesAt scope before l.1.lead ++ rs.flatMap (·.2 inner inside) ++
    sitesAt inner s!"at the end of a list {inside}" l.1.close

/-- The blocks of comments of a document, each in its scope. -/
def sitesOf (d : Doc) : List Site :=
  d.items.flatMap (RoseTree.para sitesStep · [] "at the top level") ++
    sitesAt [] "after the last form" d.trail

/-! ## Declarations -/

/-- The heads of the declarations whose constructors are declared with them. -/
def dataHeads : List (List Char) :=
  [['d', 'a', 't', 'a'], ['t', 'r', 'e', 'e', '-', 'd', 'a', 't', 'a']]

/-- The constructors a declaration of a datatype declares. -/
def constructorsOf (t : SExpr) : List (List Char) :=
  if dataHeads.any (headIs · t) then
    (t.children.drop 2).filterMap fun c ↦ c.children.head?.bind fun h ↦
      if h.children.isEmpty then h.label.2 else none
  else []

/-- One node's declarations, from its children's, each a function of the scope: a module and the
declarations of its body, or a declaration and the constructors it declares. -/
def declsStep (l : Trivia × Option (List Char)) (rs : List (SExpr × (Path → List Path))) :
    Path → List Path := fun scope ↦
  let t := RoseTree.node l (rs.map Prod.fst)
  match moduleName? t, (if isDecl t then declName? t else none) with
  | some m, _ => [scope ++ [m]] ++ rs.flatMap (·.2 (scope ++ [m]))
  | none, some n => [scope ++ [n]] ++ (constructorsOf t).map (scope ++ [·])
  | none, none => []

/-- The paths of the declarations of a document. -/
def declsOf (d : Doc) : List Path := d.items.flatMap (RoseTree.para declsStep · [])

/-! ## The check -/

/-- What resolves a reference outside the program: to a Lean constant and to an entry of the
bibliography. -/
structure Resolver where
  /-- Whether a name is a Lean constant. -/
  lean : List Char → Bool
  /-- Whether a key is an entry of the bibliography. -/
  cite : List Char → Bool

/-- Whether a name refers to a declaration of a program from a scope: whether, under a prefix of
the scope, the name's components are a declaration's path. -/
def resolves (decls : List Path) (scope : Path) (x : List Char) : Bool :=
  let comps := x.splitOn '.'
  (List.range (scope.length + 1)).any fun k ↦ decls.contains (scope.take k ++ comps)

/-- The references of blocks, each with its role. -/
def refsOf (bs : List Block) : List (Role × List Char) :=
  bs.flatMap fun
    | .para ls => ls.flatten.filterMap fun
      | .role r s => some (r, s)
      | _ => none
    | .code _ => []

/-- What fails to resolve of a reference from a scope, or nothing. -/
def unresolved (decls : List Path) (R : Resolver) (scope : Path) :
    Role × List Char → Option String
  | (.geb, s) => if resolves decls scope s then none
    else some s!"{String.ofList s} names no definition of the program"
  | (.name, s) => if R.lean s then none else some s!"{String.ofList s} names no Lean constant"
  | (.cite, s) => if R.cite s then none
    else some s!"{String.ofList s} is no entry of the bibliography"
  | (.lit, _) => none

/-- The failures of a block of comments: what rejects its prose, or what of its references fails
to resolve. -/
def siteFailures (decls : List Path) (R : Resolver) (s : Site) : List String :=
  let report (e : String) := s!"the comment {s.place}: {e}"
  match s.lines.mapM proseOf >>= parseProse with
  | .error e => [report e]
  | .ok bs => (refsOf bs).filterMap (unresolved decls R s.scope · |>.map report)

/-- The failures of a note's links, from the path of the declaration it documents. -/
def noteFailures (decls : List Path) (R : Resolver) (p : Path) (n : Note) : List String :=
  n.filterMap fun
    | .link k x =>
      let r := if k == ['l', 'e', 'a', 'n'] then Role.name else Role.geb
      (unresolved decls R p.dropLast (r, x)).map (s!"the note of {showPath p}: {·}")
    | _ => none

/-- The failures of a document's comments and notes, against the declarations of its program. -/
def check (decls : List Path) (R : Resolver) (d : Doc) : List String :=
  (sitesOf d).flatMap (siteFailures decls R) ++
    match notesOf d with
    | .ok ns => ns.flatMap fun (p, n) ↦ noteFailures decls R p n
    | .error e => [e]

end Geb.Kernel.Markup

end
