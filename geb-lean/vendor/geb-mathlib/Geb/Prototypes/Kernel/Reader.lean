/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Basic
public import Geb.Prototypes.Kernel.Document

set_option doc.verso true in
/-!
# The kernel's readable syntax

A program is a sequence of definitions written as S-expressions, {lit}`(def name term)`, each
term referring to the definitions before it by name, of type abbreviations
{lit}`(deftype name type)`, and of numeral abbreviations {lit}`(defnum name n)`, the
abbreviations each in force after it. A numeral abbreviation names a label, as an
assembler's symbolic constant does: the atoms of a definition's term that name one are read
as its numeral, wherever they occur. A declaration's name is neither a keyword, a primitive's
name nor a type's, nor the name of an earlier declaration of any kind. Reading has two stages:
a text in the authoring profile is read as S-expressions
({name}`Geb.Kernel.Document.readDoc`),
rose trees whose leaves carry atoms and whose other nodes are lists; each
S-expression is then resolved into a kernel term, variable names becoming de Bruijn indices,
definition names references, and keywords the kernel's constructors. Loading type-checks
and evaluates the definitions in order, each in the global environment of those before it.

The forms of a term:

* a numeral {lit}`n` is the quoted leaf of label {lit}`n`; {lit}`unit` is the unit value;
  a bound name is a variable, a defined name a reference, and a primitive's name the
  primitive;
* {lit}`(lam (x A) body)` is an abstraction binding {lit}`x` of type {lit}`A`, and
  {lit}`(lam ((x₁ A₁) … (xₙ Aₙ)) body)` the nested abstractions binding each in turn;
  {lit}`(let x A e body)` is the abstraction binding {lit}`x` in {lit}`body` applied to
  {lit}`e`;
  {lit}`(pair a b)`, {lit}`(fst p)`, {lit}`(snd p)`, {lit}`(if c a b)` and
  {lit}`(quote d)` are the corresponding constructors, a datum being a numeral or a list
  {lit}`(n d₁ … dₖ)` of a label and children, in which an atom that is not a numeral stands
  for the leaves of its characters' codes;
* {lit}`(nil A)` is the empty list of elements of type {lit}`A` and {lit}`(cons x xs)` the
  list of a head and a tail;
* {lit}`(fold A x₁ … xₖ)`, {lit}`(iter A x₁ … xₖ)`, {lit}`(foldr A B x₁ … xₖ)` and
  {lit}`(lcase A B x₁ … xₖ)` apply the fold of trees, the iteration, the right fold of lists
  and the case analysis of lists at the given types to their arguments, and any other list
  {lit}`(f x₁ … xₖ)` applies {lit}`f` to its arguments in turn.

Types are {lit}`T`, {lit}`Unit`, {lit}`(Prod A B)`, {lit}`(Arrow A B)`,
{lit}`(List A)` and the names of type abbreviations. A semicolon begins a comment that
extends to the end of its line, which the reading of a document keeps and the reading of a
program erases.

## Main definitions

* {lit}`readSExps` — the S-expressions of a text.
* {lit}`readDatum` — an S-expression read as a quoted datum.
* {lit}`reservedNames`, {lit}`isFresh` — the names a declaration may take.
* {lit}`expandNums` — the expansion of numeral abbreviations.
* {lit}`resolve` — the resolution of an S-expression into a kernel term.
* {lit}`readProgram`, {lit}`load` — a program's definitions as named terms, and their
  meanings.
* {lit}`runMain` — the application of a program's last definition to an input tree.
* {lit}`diagnose` — the first failure of a program that does not read or load.

## Implementation notes

Both stages are folds: the lexer and the parser of the source document fold over the text,
the parser with an explicit stack, and resolution is a fold over the S-expression whose
result is a function of the names in scope. Text is a list of characters and atoms are lists
of characters, compared with keywords and reserved names as lists of characters: core's
{lit}`String.toList`, the numeral parser built on it, and the injectivity of
{name}`String.ofList` depend on {lit}`Classical.choice`, which this module avoids.

## Tags

bootstrap, kernel, S-expression, reader, name resolution
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel

/-- The S-expressions of a text in the authoring profile, read by
{name}`Geb.Kernel.Document.readDoc` with their comments and empty lines erased, or nothing when
the text is not well formed or its parentheses do not balance. -/
def readSExps (text : List Char) : Option (List SExp) :=
  (Document.readDoc text).map (·.items.map RoseTree.erase)

/-- The label a numeral denotes: a non-empty list of decimal digits. -/
def numeral? (s : List Char) : Option ℕ :=
  if s.isEmpty then none
  else s.foldl (fun n c ↦ n.bind fun n ↦
    if c.isDigit then some (10 * n + (c.toNat - '0'.toNat)) else none) (some 0)

/-- The names of the primitives, in the order of {name}`prims`. -/
def primNames : List (List Char) :=
  [['l', 'a', 'b', 'e', 'l'], ['a', 'r', 'i', 't', 'y'], ['c', 'h', 'i', 'l', 'd'],
    ['n', 'o', 'd', 'e'], ['c', 'h', 'i', 'l', 'd', 'r', 'e', 'n'], ['a', 'd', 'd'],
    ['s', 'u', 'b'], ['m', 'u', 'l'], ['d', 'i', 'v'], ['m', 'o', 'd'], ['e', 'q'], ['l', 't'],
    ['e', 'q', 'u', 'a', 'l'], ['l', 'o', 'g', '2']]

/-- Type abbreviations: names with the types they abbreviate, the latest first. -/
abbrev TypeNames : Type := List (List Char × Tree)

/-- Numeral abbreviations: names with the numerals they abbreviate, the latest first. -/
abbrev NumNames : Type := List (List Char × List Char)

/-- An S-expression with each atom that names a numeral abbreviation replaced by its numeral. -/
def expandNums (nums : NumNames) : SExp → SExp :=
  RoseTree.elim fun a rs ↦ RoseTree.node (a.map fun s ↦ (nums.lookup s).getD s) rs

/-- A numeral abbreviation's numeral: the S-expression, its abbreviations expanded, when it is
a numeral. -/
def numOf (nums : NumNames) (e : SExp) : Option (List Char) :=
  (expandNums nums e).label.bind fun s ↦ (numeral? s).map fun _ ↦ s

/-- One node of an S-expression read as a type: its atom, if it is one, and the type it denotes,
from its children's. -/
def readTypeStep (tys : TypeNames) (a : Option (List Char))
    (rs : List (Option (List Char) × Option Tree)) : Option (List Char) × Option Tree :=
  match a, rs with
  | some ['T'], _ => (a, some tT)
  | some ['U', 'n', 'i', 't'], _ => (a, some tUnit)
  | some s, _ => (a, List.lookup s tys)
  | none, [(some ['P', 'r', 'o', 'd'], _), (_, some A), (_, some B)] => (none, some (tProd A B))
  | none, [(some ['A', 'r', 'r', 'o', 'w'], _), (_, some A), (_, some B)] =>
    (none, some (tArrow A B))
  | none, [(some ['L', 'i', 's', 't'], _), (_, some A)] => (none, some (tList A))
  | none, _ => (none, none)

/-- An S-expression read as a type, given the type abbreviations in force. -/
def readType (tys : TypeNames) (e : SExp) : Option Tree := (RoseTree.elim (readTypeStep tys) e).2

/-- One node of a quoted datum: an atom's numeral, if it is one, and the trees the node
contributes to the list it is in, a numeral its leaf, another atom the leaves of its
characters' codes, and a list of a numeral and data the node of that label. -/
def datumStep (a : Option (List Char)) (rs : List (Option ℕ × Option (List Tree))) :
    Option ℕ × Option (List Tree) :=
  match a, rs with
  | some s, _ =>
    match numeral? s with
    | some n => (some n, some [leaf n])
    | none => (none, some (s.map fun c ↦ leaf c.toNat))
  | none, (some l, _) :: ds => (none, (ds.mapM Prod.snd).map fun ts ↦ [RoseTree.node l ts.flatten])
  | _, _ => (none, none)

/-- An S-expression read as a quoted datum: a numeral is a leaf, and a list of a numeral and
data is a node, in which an atom that is not a numeral contributes the leaves of its
characters' codes, so that {lit}`(0 let)` is {lit}`(0 108 101 116)`. -/
def readDatum (e : SExp) : Option Tree :=
  match e.label with
  | some s => (numeral? s).map leaf
  | none =>
    match (RoseTree.elim datumStep e).2 with
    | some [t] => some t
    | _ => none

/-- A node of the kernel over a list of children. -/
abbrev mk (l : ℕ) (cs : List Tree) : Tree := RoseTree.node l cs

/-- A term applied to arguments in turn. -/
def apps (f : Tree) (xs : List Tree) : Tree := xs.foldl (fun g x ↦ mk Label.app [g, x]) f

/-- The binders of an abstraction: one binder {lit}`(x A)`, or a list of them; an atom has
none. -/
def binders (b : SExp) : List SExp :=
  match b.label, b.children with
  | some _, _ => []
  | none, [x, _] => if x.label.isSome then [b] else b.children
  | none, bs => bs

/-- Resolve one S-expression node: its atom or its elements, each with its resolution as a
function of the names bound around it. -/
def resolveStep (tys : TypeNames) (defs : List (List Char)) (a : Option (List Char))
    (cs : List (SExp × (List (List Char) → Option Tree))) (scope : List (List Char)) :
    Option Tree :=
  let args (xs : List (SExp × (List (List Char) → Option Tree))) := xs.mapM (·.2 scope)
  match a, cs with
  | some s, _ =>
    match numeral? s, scope.idxOf? s, defs.idxOf? s, primNames.idxOf? s with
    | some n, _, _, _ => some (mk Label.quote [leaf n])
    | _, some i, _, _ => some (mk Label.var [leaf i])
    | _, _, some j, _ => some (mk Label.ref [leaf j])
    | _, _, _, some k => some (mk Label.prim [leaf k])
    | _, _, _, _ => if s == ['u', 'n', 'i', 't'] then some (mk Label.unit []) else none
  | none, (h, rh) :: rest =>
    match h.label, rest with
    | some ['l', 'a', 'm'], [(b, _), (_, body)] => do
      let bs ← (binders b).mapM fun c ↦
        match c.label, c.children with
        | none, [x, A] => do some (← x.label, ← readType tys A)
        | _, _ => none
      if bs.isEmpty then none
      else
        let t ← body ((bs.map Prod.fst).reverse ++ scope)
        some (bs.foldr (fun p u ↦ mk Label.lam [p.2, u]) t)
    | some ['l', 'e', 't'], [(x, _), (A, _), (_, e), (_, body)] => do
      let name ← x.label
      some (mk Label.app [mk Label.lam [← readType tys A, ← body (name :: scope)], ← e scope])
    | some ['p', 'a', 'i', 'r'], _ => (args rest).map (mk Label.pair)
    | some ['f', 's', 't'], _ => (args rest).map (mk Label.fst)
    | some ['s', 'n', 'd'], _ => (args rest).map (mk Label.snd)
    | some ['i', 'f'], _ => (args rest).map (mk Label.cond)
    | some ['q', 'u', 'o', 't', 'e'], [(d, _)] => (readDatum d).map fun t ↦ mk Label.quote [t]
    | some ['c', 'o', 'n', 's'], _ => (args rest).map (mk Label.cons)
    | some ['n', 'i', 'l'], [(A, _)] => (readType tys A).map fun A ↦ mk Label.nil [A]
    | some ['f', 'o', 'l', 'd'], (A, _) :: xs => do
      apps (mk Label.fold [← readType tys A]) (← args xs)
    | some ['p', 'a', 'r', 'a'], (A, _) :: xs => do
      apps (mk Label.para [← readType tys A]) (← args xs)
    | some ['i', 't', 'e', 'r'], (A, _) :: xs => do
      apps (mk Label.iter [← readType tys A]) (← args xs)
    | some ['f', 'o', 'l', 'd', 'r'], (A, _) :: (B, _) :: xs => do
      apps (mk Label.foldr [← readType tys A, ← readType tys B]) (← args xs)
    | some ['l', 'c', 'a', 's', 'e'], (A, _) :: (B, _) :: xs => do
      apps (mk Label.lcase [← readType tys A, ← readType tys B]) (← args xs)
    | _, _ => do apps (← rh scope) (← args rest)
  | none, [] => none

/-- Resolve an S-expression into a kernel term, given the type abbreviations in force, the
names of the definitions before it and the names bound around it. -/
def resolve (tys : TypeNames) (defs : List (List Char)) (e : SExp) (scope : List (List Char)) :
    Option Tree :=
  RoseTree.para (resolveStep tys defs) e scope

/-- The names no declaration takes: the keywords of terms and of declarations, the form of a
hole, the heads of the strict encodings' annotation forms and documents, the names of the types
and of the primitives. -/
def reservedNames : List (List Char) :=
  [['l', 'a', 'm'], ['l', 'e', 't'], ['p', 'a', 'i', 'r'], ['f', 's', 't'], ['s', 'n', 'd'],
    ['i', 'f'], ['q', 'u', 'o', 't', 'e'], ['c', 'o', 'n', 's'], ['n', 'i', 'l'],
    ['f', 'o', 'l', 'd'], ['p', 'a', 'r', 'a'], ['i', 't', 'e', 'r'], ['f', 'o', 'l', 'd', 'r'],
    ['l', 'c', 'a', 's', 'e'], ['u', 'n', 'i', 't'], ['d', 'e', 'f'],
    ['d', 'e', 'f', 't', 'y', 'p', 'e'], ['d', 'e', 'f', 'n', 'u', 'm'], ['h', 'o', 'l', 'e'],
    ['*', 'a', 'n', 'n'], ['*', 'd', 'o', 'c'], ['T'], ['U', 'n', 'i', 't'], ['P', 'r', 'o', 'd'],
    ['A', 'r', 'r', 'o', 'w'], ['L', 'i', 's', 't']] ++ primNames

/-- Whether a name may be declared after declarations of the names given: it is neither
reserved nor declared already, as a definition or an abbreviation of either kind. -/
def isFresh (taken : List (List Char)) (name : List Char) : Bool :=
  !reservedNames.contains name && !taken.contains name

/-- One form of a program read after those before it, given their abbreviations and
definitions: a definition, a type abbreviation or a numeral abbreviation under a fresh name. -/
def readFormStep (acc : Option (TypeNames × NumNames × List (List Char × Tree))) (e : SExp) :
    Option (TypeNames × NumNames × List (List Char × Tree)) := do
  let (tys, nums, ds) ← acc
  match e.children with
  | [kw, n, body] => do
    let name ← n.label
    guard (isFresh (tys.map Prod.fst ++ nums.map Prod.fst ++ ds.map Prod.fst) name)
    match kw.label with
    | some ['d', 'e', 'f'] =>
      some (tys, nums, ds ++ [(name, ← resolve tys (ds.map Prod.fst) (expandNums nums body) [])])
    | some ['d', 'e', 'f', 't', 'y', 'p', 'e'] =>
      some ((name, ← readType tys body) :: tys, nums, ds)
    | some ['d', 'e', 'f', 'n', 'u', 'm'] => some (tys, (name, ← numOf nums body) :: nums, ds)
    | _ => none
  | _ => none

/-- The definitions of a program's forms, as names with kernel terms; abbreviations are expanded
where they are used. A declaration whose name is reserved or declared before it is rejected. -/
def readForms (es : List SExp) : Option (List (List Char × Tree)) :=
  (es.foldl readFormStep (some ([], [], []))).map (·.2.2)

/-- The meanings of a program's definitions, each checked and evaluated in the global
environment of those before it. -/
def load (ds : List Tree) : Option (List Glob) :=
  ds.foldl (fun acc t ↦ do
    let G ← acc
    let m ← infer G [] t
    some (G ++ [⟨m.1, m.2 ()⟩])) (some [])

/-- The first failure of a program's forms, as a message: a form that is neither a definition
nor an abbreviation, a name reserved or declared twice, or the first definition that does not
resolve or is ill-typed; nothing when the forms read and load. -/
def diagnoseForms (es : List SExp) : Option String :=
  let other := "a form is neither a def, a deftype nor a defnum"
  let step (acc : TypeNames × NumNames × List (List Char) × List Glob × Option String)
      (e : SExp) :=
    let (tys, nums, names, G, err) := acc
    if err.isSome then acc else
    match e.children with
    | [kw, n, body] =>
      if n.label.any (!isFresh (tys.map Prod.fst ++ nums.map Prod.fst ++ names) ·) then
        (tys, nums, names, G,
          some s!"{String.ofList (n.label.getD [])} is reserved or declared before")
      else
      match n.label, kw.label.map String.ofList with
      | some name, some "def" =>
        match resolve tys names (expandNums nums body) [] with
        | none => (tys, nums, names, G, some s!"{String.ofList name} does not resolve")
        | some t =>
          match infer G [] t with
          | none => (tys, nums, names, G, some s!"{String.ofList name} is ill-typed")
          | some m => (tys, nums, names ++ [name], G ++ [⟨m.1, m.2 ()⟩], none)
      | some name, some "deftype" =>
        match readType tys body with
        | none => (tys, nums, names, G, some s!"{String.ofList name} is not a type")
        | some A => ((name, A) :: tys, nums, names, G, none)
      | some name, some "defnum" =>
        match numOf nums body with
        | none => (tys, nums, names, G, some s!"{String.ofList name} is not a numeral")
        | some v => (tys, (name, v) :: nums, names, G, none)
      | _, _ => (tys, nums, names, G, some other)
    | _ => (tys, nums, names, G, some other)
  (es.foldl step ([], [], [], [], none)).2.2.2.2

end Geb.Kernel

end
