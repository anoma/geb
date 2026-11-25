/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Kernel.Reader

set_option doc.verso true

/-!
# Modules

A pass before reading flattens a program's modules into declarations under qualified names.
A module is a block form, {lit}`(module M header… body…)`, whose header is a telescope of
parameters and imports followed by an export list. A module without parameters is elaborated
where it is declared: each declaration of its body under the name {lit}`M.x`, qualified by the
module's path from the root, the rest of the enclosing block referring to its exports as
{lit}`M.x`. An import {lit}`(import P)` makes the exports of the module at path {lit}`P`
visible unqualified, and {lit}`(import P as N)` as {lit}`N.x`. A module with parameters is
elaborated at each import that supplies all of its parameters, {lit}`(import (P a …))`: a sort
parameter {lit}`(parameter A)` becomes a type abbreviation of its argument and an operation
parameter {lit}`(parameter (f (A …) R))` a definition of its argument at that type, and the body
is elaborated under the instance's prefix. Instantiation by definitions is substitution of the
arguments for the parameters, the kernel's types being monomorphic. Where a module with
parameters is declared, it is elaborated once more at opaque arguments, into a form
{lit}`(%generic …)` that the stage-1 compiler checks and every reader drops
({lit}`genericOf`).

A definition, a function and a datatype take type parameters of their own, written after the
name: {lit}`(def (x A …) e)`, {lit}`(defn (f A …) binders R e)` and
{lit}`(data (D A …) (c F …) …)`. A use supplies a type for each, as the kernel's constants take
theirs: {lit}`(f B … e …)` in a term, the instance itself where no term follows the types and
its application otherwise; {lit}`(D B …)` in a type; and {lit}`(c B … x …)` in a pattern. A use
denotes an instance, the declaration with each parameter a type abbreviation of its argument,
which is written before the declaration that first uses it. An instance is named by the
S-expression of its use, {lit}`(f B …)`, whose names are those of the flat program and whose
type abbreviations are expanded, so that uses at equal arguments denote one instance wherever
they are written ({lit}`instName`). Where it is declared, such a declaration is elaborated once
at opaque arguments, as a module with parameters is.

Source binders and their occurrences are renamed with {lit}`%%` before datatype expansion.
The source entry rejects unquoted names beginning with {lit}`%`, so these private names cannot
capture a generated primitive, recognizer or single-{lit}`%` temporary. Patterns retain their
{lit}`&` marker and {lit}`_` wildcard, neither of which binds a name.

Every name of a declaration's body is renamed to what it denotes in the flat program, a name
bound around it in a term excepted; the forms of the kernel and of the datatype language give
each child its role, so a quoted datum and the name of a hole are never renamed. A name visible
in a block is never declared again in it, nor imported, nor bound by a parameter: a clash is
rejected, as are an import naming no module or leaving a parameter unsupplied and an export
naming nothing.

The term forms {lit}`(let* ((x A e) …) body)` and
{lit}`(cond (test value) … (else default))` expand in the same pass to nested {lit}`let` and
{lit}`if` forms. Each sequential binding's value sees the preceding bindings, and its name is
in scope in the bindings after it and in the body. An empty binding list gives the body.
Conditional clauses are tested in order and require exactly one final {lit}`else` clause;
that clause alone gives its default. Quotations and datums are unchanged. Neither keyword may
name a declaration. A program without modules or either chain still receives private binder names.

## Main definitions

* {lit}`rename` — the renaming of an S-expression in a role.
* {lit}`letChain`, {lit}`condChain` — sequential bindings and guarded clauses as nested forms.
* {lit}`instName`, {lit}`nameUses` — an instance's name, and a renamed form with its uses of
  declarations with type parameters named.
* {lit}`expandModules` — the elaboration of a program's modules.
* {lit}`readProgram`, {lit}`runMain`, {lit}`diagnose` — the reading of a program through the
  elaboration of its modules.

## Implementation notes

The elaboration of a block is a fold over its forms; the elaboration of a nested module and of
an instance is one level of a tower built by {lit}`Nat.rec`, bounded by the number of module
forms and of declarations with type parameters in the program, since a module imports only
modules declared before it and a declaration uses only declarations before it. A datatype
whose declaration applies it to types other than its parameters has no finite set of instances
and exhausts the tower.

The renaming is a paramorphism with no state, so it writes a use of a declaration with type
parameters as a node no reader writes, an atom's label over children ({lit}`polyUse`). The
uses of a renamed form are named, and the instances they denote written, where the form is
emitted ({lit}`emitForm`).

An instance's name spells an atom that is a token of \[RFC9804\] as it is and any other
atom verbatim, by its length, so that distinct uses have distinct names whatever characters
their atoms hold.

## References

* \[RFC9804\]

## Tags

module, import, export, parameter, type parameter, instance, qualified name
-/

@[expose] public section

namespace Geb.Kernel

/-! ## Renaming -/

/-- A name: an atom's characters. -/
abbrev Ident : Type := List Char

/-- The names visible in a block, each with the name of what it denotes in the flat program. -/
abbrev Visible : Type := List (Ident × Ident)

/-- An atom of characters. -/
def atom (s : Ident) : SExp := RoseTree.node (some s) []

/-- A list of S-expressions. -/
def slist (cs : List SExp) : SExp := RoseTree.node none cs

/-- Whether an S-expression is the atom of a keyword. -/
def isKw (e : SExp) (k : String) : Bool := e.label.any (String.ofList · == k)

/-- The name a visible name denotes in the flat program; a qualified name that is not visible
becomes the reserved atom {lit}`hole`, which denotes nothing, so that a declaration a module does
not export is unreachable by its qualified name; any other name is kept. -/
def flat (vis : Visible) (s : Ident) : Ident :=
  match vis.lookup s with
  | some f => f
  | none => if s.contains '.' then ['h', 'o', 'l', 'e'] else s

/-- The role of an S-expression in its parent: a term, a type, a clause, binders, sequential
bindings, or a quoted datum. -/
inductive Role where
  /-- A term, whose names are renamed unless bound around it. -/
  | term
  /-- A type, whose names are renamed. -/
  | type
  /-- A clause of a case analysis: a pattern binding its variables, or {lit}`else`, and a
  term. -/
  | clause
  /-- One binder {lit}`(x A)`, or a list of them, whose types are renamed. -/
  | binders
  /-- One sequential binding, whose value is renamed outside its own scope. -/
  | letBinding
  /-- Sequential bindings, each in the scope of the preceding bindings. -/
  | letBindings
  /-- A conditional clause: a test and a result, or the final default. -/
  | condClause
  /-- A pattern {lit}`(c x …)`, whose constructor is renamed and whose variables are bound. -/
  | pattern
  /-- A quoted datum or the name of a hole, unchanged. -/
  | datum
  deriving DecidableEq

/-- A name declared with type parameters: their number, and the declaration's name in the flat
program, which a constructor shares with its datatype. -/
structure PolyRef where
  /-- The number of the type parameters. -/
  arity : ℕ
  /-- The declaration's name in the flat program. -/
  principal : Ident

/-- The names declared with type parameters, by their names in the flat program. -/
abbrev Polys : Type := List (Ident × PolyRef)

/-- The names a binder or a list of binders binds. -/
def boundBy (b : SExp) : List Ident := (binders b).filterMap fun c ↦ c.children.head?.bind (·.label)

/-- The variables a pattern {lit}`(c x …)` binds, after the type arguments of a constructor
that takes a number of them. -/
def patternVars (p : SExp) (types : ℕ := 0) : List Ident :=
  ((p.children.drop (1 + types)).filterMap (·.label)).filter fun s ↦ s != ['&'] && s != ['_']

/-- A use of a name declared with type parameters at type arguments, as the renaming writes
it: the name over the declaration's and the arguments, an atom's label over children, which no
reader writes. -/
def polyUse (name : Ident) (ref : PolyRef) (args : List SExp) : SExp :=
  RoseTree.node (some name) (atom ref.principal :: args)

/-- A source binder's private name. Source names beginning with {lit}`%` are rejected before
elaboration; {lit}`%%` is distinct from every name introduced by datatype expansion. -/
def localName (s : Ident) : Ident := '%' :: '%' :: s

/-- A private source binder's spelling before elaboration, for reports and fillings written
in its source context. Other names retain their spelling. -/
def sourceName (s : Ident) : Ident :=
  match s with
  | '%' :: '%' :: rest => rest
  | _ => s

/-- A binder renamed into the private namespace; a malformed binder is left for the reader. -/
def localAtom (x : SExp) : SExp := x.label.map (atom ∘ localName) |>.getD x

/-- Sequential typed bindings as nested {lit}`let` forms. A malformed binding gives an empty
term, which the reader rejects. -/
def letChain (bs : List SExp) (body : SExp) : SExp :=
  bs.foldr (fun b rest ↦ match b.label, b.children with
    | none, [x, A, e] =>
      if x.label.isSome then slist [atom ['l', 'e', 't'], x, A, e, rest] else slist []
    | _, _ => slist []) body

/-- Guarded clauses as nested {lit}`if` forms, ending in exactly one {lit}`else` clause.
A malformed chain gives an empty term, which the reader rejects. -/
def condChain (cs : List SExp) : SExp :=
  match cs.reverse with
  | c :: rest =>
    match c.label, c.children with
    | none, [k, body] =>
      if isKw k "else" then
        ((rest.foldlM fun (tail c : SExp) ↦ match c.label, c.children with
          | none, [p, b] =>
            if isKw p "else" then none else some (slist [atom ['i', 'f'], p, b, tail])
          | _, _ => none) body).getD (slist [])
      else slist []
    | _, _ => slist []
  | [] => slist []

/-- One node renamed in each role, from its children renamed in each: in a term, a bound atom
receives its private name and any other visible name is qualified. The forms of the kernel and
datatype language give each child its role; in a type every visible name is renamed. A name
declared with type parameters is written as its use at the types that follow it
({name}`polyUse`): in a type all the elements after it, and in a term and in a pattern as many
as it has parameters. -/
def renameStep (vis : Visible) (polys : Polys) (a : Option Ident)
    (rs : List (SExp × (Role → List Ident → SExp))) (r : Role) (bound : List Ident) : SExp :=
  let orig := RoseTree.node a (rs.map Prod.fst)
  let as (r : Role) (bound : List Ident) (xs : List (SExp × (Role → List Ident → SExp))) :=
    xs.map (·.2 r bound)
  let isLocal (s : Ident) : Bool := bound.contains s && (numeral? s).isNone
  -- the name in the flat program and the declaration of an atom declared with type parameters
  let polyOf (e : SExp) : Option (Ident × PolyRef) :=
    e.label.bind fun s ↦ (polys.lookup (flat vis s)).map fun ref ↦ (flat vis s, ref)
  match r, a with
  | .datum, _ => orig
  | .type, some s =>
    match polyOf orig with
    | some (fl, ref) => polyUse fl ref []
    | none => atom (flat vis s)
  | .type, none =>
    match rs with
    | (h, _) :: rest =>
      match polyOf h with
      | some (fl, ref) => polyUse fl ref (as .type [] rest)
      | none => slist (as .type [] rs)
    | [] => orig
  | .term, some s =>
    if isLocal s then atom (localName s)
    else match polyOf orig with
      | some (fl, ref) => polyUse fl ref []
      | none => atom (flat vis s)
  | .pattern, some _ => orig
  | .pattern, none =>
    match rs with
    | (c, _) :: xs =>
      let vars (xs : List (SExp × (Role → List Ident → SExp))) : List SExp :=
        xs.map fun (x, _) ↦ if isKw x "&" || isKw x "_" then x else localAtom x
      match polyOf c with
      | some (fl, ref) =>
        slist (polyUse fl ref (as .type [] (xs.take ref.arity)) :: vars (xs.drop ref.arity))
      | none => slist (atom (c.label.map (flat vis) |>.getD []) :: vars xs)
    | [] => orig
  | .letBinding, _ =>
    match a, rs with
    | none, [(x, _), (_, rA), (_, e)] => slist [localAtom x, rA .type [], e .term bound]
    | _, _ => slist []
  | .letBindings, _ =>
    let (_, bs) := rs.foldl (fun (scope, bs) (b, rb) ↦
      ((b.children.head?.bind (·.label)).toList ++ scope, rb .letBinding scope :: bs)) (bound, [])
    slist bs.reverse
  | .condClause, _ =>
    match a, rs with
    | none, [(p, rp), (_, body)] =>
      slist [if isKw p "else" then p else rp .term bound, body .term bound]
    | _, _ => slist []
  | .binders, some _ => orig
  | .binders, none =>
    match rs with
    | (x, _) :: rest =>
      if x.label.isSome then slist (localAtom x :: as .type [] rest)
      else slist (as .binders [] rs)
    | [] => orig
  | .clause, some _ => orig
  | .clause, none =>
    match rs with
    | [(p, rp), (_, body)] =>
      if p.label.isSome then slist [p, body .term bound]
      else
        let types := ((p.children.head?.bind polyOf).map (·.2.arity)).getD 0
        slist [rp .pattern [], body .term (patternVars p types ++ bound)]
    | _ => orig
  | .term, none =>
    match rs with
    | [] => orig
    | (h, rh) :: rest =>
      if isKw h "quote" || isKw h "hole" then orig
      else if isKw h "datum" then
        match rest with
        | [(_, rD), (d, _)] => slist [h, rD .type [], d]
        | _ => orig
      else if isKw h "decode" then
        match rest with
        | (_, rD) :: xs => slist (h :: rD .type [] :: as .term bound xs)
        | [] => orig
      else if isKw h "lam" then
        match rest with
        | [(b, rb), (_, body)] => slist [h, rb .binders [], body .term (boundBy b ++ bound)]
        | _ => orig
      else if isKw h "let" then
        match rest with
        | [(x, _), (_, rA), (_, e), (_, body)] =>
          slist [h, localAtom x, rA .type [], e .term bound,
            body .term (x.label.toList ++ bound)]
        | _ => orig
      else if isKw h "let*" then
        match rest with
        | [(bs, rbs), (_, body)] =>
          if bs.label.isNone then
            letChain (rbs .letBindings bound).children (body .term (boundBy bs ++ bound))
          else slist []
        | _ => slist []
      else if isKw h "cond" then condChain (as .condClause bound rest)
      else if isKw h "nil" then slist (h :: as .type [] rest)
      else if isKw h "fold" || isKw h "para" || isKw h "iter" then
        match rest with
        | (_, rA) :: xs => slist (h :: rA .type [] :: as .term bound xs)
        | [] => orig
      else if isKw h "foldr" || isKw h "lcase" then
        match rest with
        | (_, rA) :: (_, rB) :: xs => slist (h :: rA .type [] :: rB .type [] :: as .term bound xs)
        | _ => orig
      else if isKw h "case" then
        match rest with
        | (_, e) :: cs => slist (h :: e .term bound :: as .clause bound cs)
        | [] => orig
      else if isKw h "cata" then
        match rest with
        | (_, rD) :: (_, rR) :: (_, e) :: cs =>
          slist (h :: rD .type [] :: rR .type [] :: e .term bound :: as .clause bound cs)
        | _ => orig
      else
        match (if h.label.any isLocal then none else polyOf h) with
        | some (fl, ref) =>
          let use := polyUse fl ref (as .type [] (rest.take ref.arity))
          if rest.length ≤ ref.arity then use
          else slist (use :: as .term bound (rest.drop ref.arity))
        | none => slist (rh .term bound :: as .term bound rest)

/-- An S-expression renamed in a role, under the visible names, the names declared with type
parameters and the names bound around it. -/
def rename (vis : Visible) (polys : Polys) (e : SExp) (r : Role) (bound : List Ident) : SExp :=
  RoseTree.para (renameStep vis polys) e r bound

/-! ## Instances -/

/-- The spelling of an S-expression in an instance's name: a list in parentheses, its elements
a space apart; an atom that is a token as it is, and any other atom verbatim, its length in
decimal, a colon and its characters, as the advanced encoding of \[RFC9804\] spells it.
Distinct S-expressions have distinct spellings. -/
def spellOf : SExp → Ident :=
  RoseTree.elim fun a cs ↦
    match a with
    | some s => if Document.isToken s then s else Csexp.decOf s.length ++ ':' :: s
    | none => '(' :: [' '].intercalate cs ++ [')']

/-- The name of the instance of a name declared with type parameters at arguments: the spelling
of its use, {lit}`(f B …)`. -/
def instName (name : Ident) (args : List SExp) : Ident := spellOf (slist (atom name :: args))

/-- The use an instance's name spells, and what follows it: the declaration's name in the flat
program, the arguments, and the name written after a full stop, that of a parameter's type
abbreviation or of a datatype's recognizer; nothing where the name spells no use. -/
def useOf? (name : Ident) : Option (Ident × List SExp × Ident) :=
  match readSExps name with
  | some (e :: rest) =>
    match e.label, e.children, rest with
    | none, h :: args, [] => h.label.map fun f ↦ (f, args, [])
    | none, h :: args, [s] =>
      match h.label, s.label with
      | some f, some ('.' :: suffix) => some (f, args, suffix)
      | _, _ => none
    | _, _, _ => none
  | _ => none

/-- The type abbreviations declared, each by its name in the flat program with the type it
abbreviates, itself with its abbreviations expanded. -/
abbrev Abbrs : Type := List (Ident × SExp)

/-- A type with its abbreviations expanded. -/
def expandAbbrs (abbrs : Abbrs) : SExp → SExp :=
  RoseTree.elim fun a cs ↦
    match a, cs with
    | some s, [] => (abbrs.lookup s).getD (atom s)
    | _, _ => RoseTree.node a cs

/-- One node of a renamed form with its uses of names declared with type parameters named, from
its children's: a use becomes the atom of its instance's name, its arguments' abbreviations
expanded, and the uses are listed, each the declaration's name over the arguments, those of an
argument before the use it is an argument of. -/
def nameUsesStep (abbrs : Abbrs) (a : Option Ident) (rs : List (SExp × List SExp)) :
    SExp × List SExp :=
  let cs := rs.map Prod.fst
  let uses := rs.flatMap Prod.snd
  match a, cs with
  | some s, d :: args =>
    let args := args.map (expandAbbrs abbrs)
    (atom (instName s args), uses ++ [RoseTree.node d.label args])
  | _, _ => (RoseTree.node a cs, uses)

/-- A renamed form with its uses of names declared with type parameters named, and the uses. -/
def nameUses (abbrs : Abbrs) : SExp → SExp × List SExp :=
  RoseTree.elim (nameUsesStep abbrs)

/-! ## Elaboration -/

/-- A module of the registry: one without parameters, by the flat names of its exports, or one
with parameters, a template elaborated at each import from its parameters, its export list,
its other forms and the names visible where it is declared. -/
inductive ModDef where
  /-- A module without parameters, by its exports' visible and flat names. -/
  | plain (exports : Visible)
  /-- A module with parameters, elaborated at each import. -/
  | template (params : List SExp) (exports : List Ident) (forms : List SExp) (scope : Visible)

/-- A member of a module: a definition, by its name in the flat program, or a module nested in
it or instantiated in it, by its path. -/
inductive Member where
  /-- A definition, by its name in the flat program. -/
  | decl (fl : Ident)
  /-- A nested module or an instance, by its path. -/
  | sub (path : Ident)
  deriving DecidableEq

/-- A module of the program's tree of modules: its path, its members in order, and its exports
with what they denote. The root block is the module of the empty path. -/
structure ModNode where
  /-- The module's path from the root. -/
  path : Ident
  /-- The module's members, in order. -/
  members : List Member
  /-- The module's exports, with what they denote. -/
  exports : Visible

/-- A declaration with type parameters, elaborated at each list of arguments it is used at: its
parameters, its keyword, its forms after its name, the names visible where it is declared, a
datatype's own among them, and the prefix its constructors' names are qualified by. -/
structure PolyDecl where
  /-- The type parameters. -/
  params : List Ident
  /-- The keyword. -/
  kw : SExp
  /-- The forms after the name. -/
  rest : List SExp
  /-- The names visible where it is declared. -/
  scope : Visible
  /-- The prefix of the block that declares it. -/
  pre : Ident

/-- The state of the elaboration of a block: the names visible in it, the declarations emitted,
the modules declared, by their paths from the root, the names the block exports, the block's
members and the modules elaborated; and of the declarations with type parameters, the names
declared, the declarations, the instances written, the type abbreviations declared, and whether
the block is elaborated at opaque arguments. -/
structure ElabState where
  /-- The names visible in the block. -/
  vis : Visible := []
  /-- The declarations emitted, in order. -/
  out : List SExp := []
  /-- The modules declared, by their paths from the root. -/
  reg : List (Ident × ModDef) := []
  /-- The names the block's export lists name. -/
  exports : List Ident := []
  /-- The block's members, in order. -/
  members : List Member := []
  /-- The modules elaborated, each after the modules nested in it. -/
  mods : List ModNode := []
  /-- The names declared with type parameters. -/
  polys : Polys := []
  /-- The declarations with type parameters, by their names in the flat program. -/
  decls : List (Ident × PolyDecl) := []
  /-- The names of the instances written. -/
  insts : List Ident := []
  /-- The type abbreviations declared. -/
  abbrs : Abbrs := []
  /-- Whether the block is elaborated at opaque arguments, inside a form {lit}`(%generic …)`. -/
  generic : Bool := false
  /-- Each instance written, a datatype's and its constructors' alike, with the name of the form
  that first uses it: what a failure of the instance is reported at. The elaboration reads none
  of it. -/
  users : List (Ident × Ident) := []

/-- The result of an elaboration: a value, or the message of its first failure. -/
abbrev Elab : Type → Type := Except String

/-- An optional value, or a failure with a message. -/
def need {α : Type} (o : Option α) (msg : String) : Elab α :=
  match o with
  | some a => pure a
  | none => throw msg

/-- A name under a prefix: the name itself at the root, and the prefix, a dot and the name
otherwise. -/
def qualify (pre s : Ident) : Ident := if pre.isEmpty then s else pre ++ '.' :: s

/-- The keywords of module elaboration, including binding and conditional chains, which no
declaration takes. -/
def moduleKeywords : List (List Char) :=
  [['m', 'o', 'd', 'u', 'l', 'e'], ['p', 'a', 'r', 'a', 'm', 'e', 't', 'e', 'r'],
    ['i', 'm', 'p', 'o', 'r', 't'], ['e', 'x', 'p', 'o', 'r', 't'],
    ['i', 'n', 't', 'e', 'r', 'f', 'a', 'c', 'e'], ['l', 'e', 't', '*'], ['c', 'o', 'n', 'd']]

/-- The state with a name made visible, when it is neither visible already nor reserved. -/
def declare (st : ElabState) (s fl : Ident) : Elab ElabState :=
  if st.vis.any (·.1 == s) || (reservedNames ++ moduleKeywords).contains s then
    throw s!"{String.ofList s} is reserved or declared before"
  else pure { st with vis := st.vis ++ [(s, fl)] }

/-- The state with names made visible in turn. -/
def declareAll (st : ElabState) (es : Visible) : Elab ElabState :=
  es.foldlM (fun st (s, fl) ↦ declare st s fl) st

/-- The exports of a block: each name its export lists name, with what it denotes. -/
def exportsOf (st : ElabState) : Elab Visible :=
  st.exports.mapM fun s ↦
    (need (st.vis.lookup s) s!"the export {String.ofList s} names nothing").map fun fl ↦ (s, fl)

/-- The forms of a list with a given head keyword, and the others. -/
def splitHead (k : String) (es : List SExp) : List SExp × List SExp :=
  (es.filter fun e ↦ e.children.head?.any (isKw · k),
    es.filter fun e ↦ !e.children.head?.any (isKw · k))

/-- The elaboration of a form in a block under a prefix, from a state: the type of one level of
the tower of nesting and instantiation. -/
abbrev ElabK : Type := Ident → ElabState → SExp → Elab ElabState

/-- A renamed form emitted, with members of the block: its uses of names declared with type
parameters named, each instance not yet written elaborated before it, one level further in,
and the type abbreviation it declares, if any, recorded with its abbreviations expanded. A use
at a number of types other than that of the declaration's parameters is rejected. -/
def emitForm (rec : ElabK) (st : ElabState) (form : SExp) (mem : List Member := []) :
    Elab ElabState := do
  let (f, uses) := nameUses st.abbrs form
  let user := (f.children[1]?.bind (·.label)).getD []
  let st ← uses.foldlM (fun st u ↦ do
    let name ← need u.label "a use names no declaration"
    let d ← need (st.decls.lookup name) s!"{String.ofList name} takes no type arguments"
    if d.params.length != u.children.length then
      throw s!"{String.ofList name} is used at {u.children.length} types and takes \
        {d.params.length}"
    let inst := instName name u.children
    if st.insts.contains inst then pure st
    else do
      let st ← rec [] st u
      -- a datatype's constructors are instances of the same use
      let ctors := if isKw d.kw "data" then
          d.rest.filterMap fun c ↦ c.children.head?.bind (·.label) else []
      pure { st with users := st.users ++
        (inst :: ctors.map fun c ↦ instName (qualify d.pre c) u.children).map (·, user) }) st
  let abbrs := match f.label, f.children with
    | none, [kw, n, A] =>
      match n.label with
      | some s => if isKw kw "deftype" then st.abbrs ++ [(s, expandAbbrs st.abbrs A)] else st.abbrs
      | none => st.abbrs
    | _, _ => st.abbrs
  pure { st with out := st.out ++ [f], members := st.members ++ mem, abbrs }

/-- The argument of a parameter bound at an instance: a sort {lit}`(parameter A)` as a type
abbreviation of the argument, and an operation {lit}`(parameter (f (A …) R))` as a definition
of the argument applied to fresh variables of the argument types, its result bound at type
{lit}`R` so that the argument's type is checked; the parameter's types are renamed in the
template's scope and the argument in the importer's. -/
def bindParam (rec : ElabK) (inst : Ident) (importer : Visible) (st : ElabState) (p arg : SExp) :
    Elab ElabState := do
  let bad := "a parameter is neither a sort nor an operation"
  match p.children with
  | [_, sig] =>
    match sig.label, sig.children with
    | some s, _ => do
      let fl := qualify inst s
      emitForm rec (← declare st s fl) (slist [atom ['d', 'e', 'f', 't', 'y', 'p', 'e'], atom fl,
        rename importer st.polys arg .type []])
    | none, [x, args, res] => do
      let s ← need x.label bad
      let fl := qualify inst s
      let vars := (args.children.zipIdx).map fun (_, i) ↦ '%' :: 'm' :: Csexp.decOf i
      let rv := ['%', 'r']
      let callee := rename importer st.polys arg .term []
      let call := if vars.isEmpty then callee else slist (callee :: vars.map atom)
      let body := slist [atom ['l', 'e', 't'], atom rv, rename st.vis st.polys res .type [], call,
        atom rv]
      let term := if vars.isEmpty then body
        else slist [atom ['l', 'a', 'm'], slist ((args.children.zip vars).map fun (A, v) ↦
          slist [atom v, rename st.vis st.polys A .type []]), body]
      emitForm rec (← declare st s fl) (slist [atom ['d', 'e', 'f'], atom fl, term]) [.decl fl]
    | _, _ => throw bad
  | _ => throw bad

/-- What a form that no branch of the elaboration reads is rejected with. -/
def otherForm : String := "a form is neither a declaration, a module, an import nor an export"

/-- A datatype's constructors, each by its name with its fields' types. -/
def ctorsOf (cs : List SExp) : Elab (List (Ident × List SExp)) :=
  cs.mapM fun c ↦ match c.children with
    | n :: fs => need (n.label.map fun cn ↦ (cn, fs)) otherForm
    | [] => throw otherForm

/-- A declaration's forms after its name, renamed under visible names and emitted under a name
of the flat program, a datatype's constructors under the names a function gives them. -/
def emitDecl (rec : ElabK) (st : ElabState) (vis : Visible) (kw : SExp) (fl : Ident)
    (ctor : Ident → Ident) (rest : List SExp) : Elab ElabState := do
  let ren (e : SExp) (r : Role) (bound : List Ident := []) : SExp := rename vis st.polys e r bound
  let form (body : List SExp) : SExp := slist (kw :: atom fl :: body)
  if isKw kw "def" then
    match rest with
    | [b] => emitForm rec st (form [ren b .term]) [.decl fl]
    | _ => throw otherForm
  else if isKw kw "deftype" || isKw kw "defnum" then
    match rest with
    | [b] => emitForm rec st (form [ren b .type])
    | _ => throw otherForm
  else if isKw kw "defn" then
    match rest with
    | [ps, res, b] =>
      emitForm rec st (form [ren ps .binders, ren res .type, ren b .term (boundBy ps)]) [.decl fl]
    | _ => throw otherForm
  else if isKw kw "data" then do
    let ctors ← ctorsOf rest
    emitForm rec st
      (form (ctors.map fun (c, fs) ↦ slist (atom (ctor c) :: fs.map (ren · .type))))
      (ctors.map fun (c, _) ↦ .decl (ctor c))
  else throw otherForm

/-- The instance of a declaration with type parameters at arguments, elaborated from the state
of its first use: each parameter a type abbreviation of its argument, under the instance's
name, and the declaration's forms elaborated in the scope of its declaration under the names
of its uses at the arguments. The instance is recorded before its forms are elaborated, so that
a datatype's use of itself at its parameters denotes the instance. -/
def instanceOf (rec : ElabK) (st : ElabState) (name : Ident) (args : List SExp) :
    Elab ElabState := do
  let d ← need (st.decls.lookup name) s!"{String.ofList name} takes no type arguments"
  let inst := instName name args
  let st1 ← (d.params.zip args).foldlM (fun acc (p, A) ↦ do
      let fl := qualify inst p
      emitForm rec (← declare acc p fl)
        (slist [atom ['d', 'e', 'f', 't', 'y', 'p', 'e'], atom fl, A]))
    { st with vis := d.scope, exports := [], members := [], insts := st.insts ++ [inst] }
  let st2 ← emitDecl rec st1 st1.vis d.kw inst (fun c ↦ instName (qualify d.pre c) args) d.rest
  pure { st2 with vis := st.vis, exports := st.exports, members := st.members }

/-- One declaration elaborated in a block under a prefix: its name qualified and made visible,
its body renamed. A declaration with type parameters, {lit}`(kw (x A …) …)`, a definition, a
function or a datatype, is recorded with the names visible where it is declared and elaborated
once at opaque arguments, a sort {lit}`(%sort S)` for each parameter: in a form
{lit}`(%generic …)` that the stage-1 compiler checks and every reader drops, or, in a block that
is itself elaborated at opaque arguments, among that block's forms. -/
def elabDecl (rec : ElabK) (pre : Ident) (st : ElabState) (e : SExp) : Elab ElabState := do
  match e.children with
  | kw :: x :: rest => do
    let isData := isKw kw "data"
    let (s, params?) ← match x.label, x.children with
      | some s, _ => pure (s, none)
      | none, h :: ps => do
        let s ← need h.label otherForm
        pure (s, some (← ps.mapM fun p ↦ need p.label "a type parameter is not a name"))
      | none, [] => throw otherForm
    let forms := if isKw kw "def" || isKw kw "deftype" || isKw kw "defnum" then some 1
      else if isKw kw "defn" then some 3 else if isData then some rest.length else none
    unless forms == some rest.length do throw otherForm
    if let some params := params? then
      unless isKw kw "def" || isKw kw "defn" || isData do
        throw "only a def, a defn and a data take type parameters"
      if params.isEmpty then throw s!"{String.ofList s} names no type parameter"
    let fl := qualify pre s
    let st1 ← declare st s fl
    let ctors : List (Ident × List SExp) ← if isData then ctorsOf rest else pure []
    let st2 ← declareAll st1 (ctors.map fun (c, _) ↦ (c, qualify pre c))
    let scope := if isData then st1.vis else st.vis
    match params? with
    | none => emitDecl rec st2 scope kw fl (qualify pre) rest
    | some params => do
      let ref : PolyRef := ⟨params.length, fl⟩
      let ctorRefs : Polys := ctors.map fun c ↦ (qualify pre c.1, ref)
      let st3 := { st2 with
        polys := st2.polys ++ (fl, ref) :: ctorRefs
        decls := st2.decls ++ [(fl, (⟨params, kw, rest, scope, pre⟩ : PolyDecl))] }
      let sorts := (List.range params.length).map fun i ↦ atom ('%' :: 't' :: Csexp.decOf i)
      let sortForms := sorts.map fun a ↦ slist [atom ['%', 's', 'o', 'r', 't'], a]
      let use := RoseTree.node (some fl) sorts
      if st3.generic then rec [] { st3 with out := st3.out ++ sortForms } use
      else do
        let g ← rec [] { st3 with out := [], generic := true } use
        pure { st3 with
          out := st3.out ++
            [slist (atom ['%', 'g', 'e', 'n', 'e', 'r', 'i', 'c'] :: sortForms ++ g.out)]
          users := g.users }
  | _ => throw otherForm

/-- An import's module path, arguments and the name it is imported as, if any:
{lit}`(import P)`, {lit}`(import (P a …))`, each optionally followed by {lit}`as N`. -/
def importSpec (e : SExp) : Option (Ident × List SExp × Option Ident) :=
  let spec (m : SExp) : Option (Ident × List SExp) :=
    match m.label, m.children with
    | some p, _ => some (p, [])
    | none, h :: args => h.label.map fun p ↦ (p, args)
    | none, [] => none
  match e.children with
  | [_, m] => (spec m).map fun (p, args) ↦ (p, args, none)
  | [_, m, a, n] => if isKw a "as" then (spec m).bind fun (p, args) ↦
      n.label.map fun nm ↦ (p, args, some nm) else none
  | _ => none

/-- Exports made visible in the importer, unqualified or under the name imported as. -/
def importAs (as? : Option Ident) (exports : Visible) : Visible :=
  exports.map fun (s, fl) ↦ ((as?.map fun n ↦ n ++ '.' :: s).getD s, fl)

/-- A template's instance under a path at arguments, elaborated from its importer's state: its
parameters bound to the arguments and its forms elaborated in the scope of its declaration. -/
def instantiate (rec : ElabK) (st : ElabState)
    (params : List SExp) (exports : List Ident) (forms : List SExp) (scope : Visible)
    (inst : Ident) (args : List SExp) : Elab ElabState := do
  let st1 ← (params.zip args).foldlM (fun acc (prm, arg) ↦ bindParam rec inst st.vis acc prm arg)
    { st with vis := scope, exports := exports, members := [] }
  forms.foldlM (rec inst) st1

/-- A template's instance at opaque arguments, which the stage-1 compiler checks and every
compiler then drops: the form {lit}`(%generic …)` over the declarations of fresh arguments, a sort
{lit}`(%sort S)` for each sort parameter and a constant {lit}`(%postulate P A)` of the parameter's
type for each operation, the parameter's sorts read as their arguments, followed by the
instance's forms; with it, the users of the instances written, those of the instance's among
them. -/
def genericOf (rec : ElabK) (st : ElabState)
    (params : List SExp) (exports : List Ident) (forms : List SExp) (scope : Visible)
    (path : Ident) : Elab (SExp × List (Ident × Ident)) := do
  let isSort (p : SExp) : Bool := (p.children[1]?.bind (·.label)).isSome
  let args := params.zipIdx.map fun (p, i) ↦
    atom ('%' :: (if isSort p then 's' else 'p') :: Csexp.decOf i)
  let sorts : Visible := (params.zip args).filterMap fun (p, a) ↦ do
    pure ((← (← p.children[1]?).label), ← a.label)
  let vis := sorts ++ scope
  let sortKw := atom ['%', 's', 'o', 'r', 't']
  let postulateKw := atom ['%', 'p', 'o', 's', 't', 'u', 'l', 'a', 't', 'e']
  let arrowKw := atom ['A', 'r', 'r', 'o', 'w']
  let decls := (params.zip args).map fun (p, a) ↦
    match p.children[1]? with
    | some sig =>
      match sig.label, sig.children with
      | some _, _ => slist [sortKw, a]
      | none, [_, xs, res] => slist [postulateKw, a, xs.children.foldr
          (fun A r ↦ slist [arrowKw, rename vis st.polys A .type [], r])
          (rename vis st.polys res .type [])]
      | none, _ => slist [postulateKw, a]
    | none => slist [postulateKw, a]
  let st1 ← decls.foldlM (fun acc d ↦ emitForm rec acc d) { st with out := [], generic := true }
  let st2 ← instantiate rec st1 params exports forms scope
    (path ++ '%' :: ['g', 'e', 'n', 'e', 'r', 'i', 'c']) args
  pure (slist (atom ['%', 'g', 'e', 'n', 'e', 'r', 'i', 'c'] :: st2.out), st2.users)

/-- The elaboration of one form of a block, given the elaboration of the forms of the modules
nested in it and of the templates and the declarations with type parameters it instantiates,
one level of nesting fewer. A use of a declaration with type parameters, the declaration's name
over the arguments, is elaborated as its instance ({name}`instanceOf`). -/
def elabStep (rec : ElabK) (pre : Ident) (st : ElabState) (e : SExp) : Elab ElabState :=
  match e.label, e.children with
  | some name, _ :: _ => instanceOf rec st name e.children
  | _, kw :: rest =>
    if isKw kw "export" then pure { st with exports := st.exports ++ rest.filterMap (·.label) }
    else if isKw kw "import" then do
      let (p, args, as?) ← need (importSpec e) "an import is not well formed"
      match ← need (st.reg.lookup p) s!"the module {String.ofList p} is not declared" with
      | .plain exports =>
        if args.isEmpty then declareAll st (importAs as? exports)
        else throw s!"the module {String.ofList p} takes no parameters"
      | .template params exports forms scope => do
        if params.length != args.length then
          throw s!"the import of {String.ofList p} supplies {args.length} of its \
            {params.length} parameters"
        let inst := pre ++ '/' :: (as?.getD p)
        let st2 ← instantiate rec st params exports forms scope inst args
        let ex ← exportsOf st2
        declareAll { st2 with
          vis := st.vis
          exports := st.exports
          members := st.members ++ [.sub inst]
          mods := st2.mods ++ [⟨inst, st2.members, ex⟩] } (importAs as? ex)
    else if isKw kw "module" then
      match rest with
      | m :: forms => do
        let s ← need m.label "a module is not named"
        let path := qualify pre s
        let (params, others) := splitHead "parameter" forms
        if params.isEmpty then do
          let st1 ← forms.foldlM (rec path) { st with exports := [], members := [] }
          let ex ← exportsOf st1
          declareAll { st1 with
            vis := st.vis
            reg := st1.reg ++ [(path, .plain ex)]
            exports := st.exports
            members := st.members ++ [.sub path]
            mods := st1.mods ++ [⟨path, st1.members, ex⟩] } (importAs (some s) ex)
        else
          let (exs, body) := splitHead "export" others
          let exports := exs.flatMap fun x ↦ (x.children.drop 1).filterMap (·.label)
          let (g, users) ← genericOf rec st params exports body st.vis path
          pure { st with out := st.out ++ [g]
                         reg := st.reg ++ [(path, .template params exports body st.vis)]
                         users }
      | [] => throw "a module is not named"
    else elabDecl rec pre st e
  | _, [] => throw otherForm

/-- The elaboration of a form at a depth of nesting and instantiation: none beyond it. -/
def elabAt (n : ℕ) : ElabK :=
  Nat.rec (motive := fun _ ↦ ElabK)
    (fun _ _ _ ↦ throw "modules or declarations nest or instantiate beyond their number")
    (fun _ rec ↦ elabStep rec) n

/-- Whether an S-expression's elements are those of a declaration with type parameters: a
keyword that takes them, and a list where a declaration's name stands. -/
def isPolyDecl (es : List SExp) : Bool :=
  match es with
  | kw :: x :: _ => x.label.isNone && (isKw kw "def" || isKw kw "defn" || isKw kw "data")
  | _ => false

/-- The number of module forms and of declarations with type parameters in a list of
S-expressions, a bound on the depth of nesting and of instantiation. -/
def moduleCount (es : List SExp) : ℕ :=
  (es.map (RoseTree.para fun a (rs : List (SExp × ℕ)) ↦
    (rs.map Prod.snd).sum + (if a.any (String.ofList · == "module") then 1 else 0) +
      if isPolyDecl (rs.map Prod.fst) then 1 else 0)).sum

/-- The state of the elaboration after a program's forms, elaborated in the root block. -/
def elabForms (es : List SExp) : Elab ElabState :=
  es.foldlM (elabAt (moduleCount es + 1) []) {}

/-- A program's forms with its modules elaborated, with its tree of modules, each module after
those nested in it and the root block last: each declaration under its qualified name,
the instances of modules with parameters at their imports and of declarations with type
parameters at their uses, and every name renamed to what it denotes; a failure when a name
clashes with one visible, an import names no module or leaves a parameter unsupplied, an export
names nothing, a use supplies a number of types other than that of the type parameters, or a
form is not a declaration, a module, an import or an export. -/
def elabTree (es : List SExp) : Elab (List SExp × List ModNode) := do
  let st ← elabForms es
  if st.exports.isEmpty then pure (st.out, st.mods ++ [⟨[], st.members, []⟩])
  else throw "the program exports names"

/-- Each instance a program's elaboration writes, those at opaque arguments included, with the
name of the form that first uses it; none where the modules do not elaborate. -/
def instanceUsers (es : List SExp) : List (Ident × Ident) :=
  match elabForms es with
  | .ok st => st.users
  | .error _ => []

/-- A program's forms with its modules elaborated, or the message of the first failure. -/
def elabModules (es : List SExp) : Elab (List SExp) := (elabTree es).map Prod.fst

/-- A program's forms with its modules elaborated, when they elaborate. -/
def expandModules (es : List SExp) : Option (List SExp) :=
  match elabModules es with
  | .ok fs => some fs
  | .error _ => none

/-! ## Reading -/

/-- A program's forms without the instances of templates at opaque arguments, which only the
stage-1 compiler reads. -/
def dropGeneric (fs : List SExp) : List SExp :=
  fs.filter fun f ↦ !(f.children.head?.any (isKw · "%generic"))

/-- The first implementation name in a source expression, ignoring quoted data. -/
def reservedSourceName? (e : SExp) : Option Ident :=
  RoseTree.para (fun a rs ↦
    match a with
    | some ('%' :: cs) => some ('%' :: cs)
    | some _ => none
    | none =>
      match rs with
      | (h, _) :: rest =>
        if isKw h "quote" then none
        else if isKw h "datum" && rest.length == 2 then rest.head?.bind (·.2)
        else rs.findSome? (·.2)
      | [] => none) e

/-- The definitions of a source program, whose unquoted names do not begin with {lit}`%`,
its modules elaborated, as names with kernel terms. -/
def readProgram (text : List Char) : Option (List (List Char × Tree)) := do
  let es ← readSExps text
  if (es.findSome? reservedSourceName?).isSome then none
  else readForms (dropGeneric (← expandModules es))

/-- The first failure of a program, as a message: text that is not well formed, modules that do
not elaborate, or the first failure of {name}`diagnoseForms`; nothing when the program reads and
loads. -/
def diagnose (text : List Char) : Option String :=
  match readSExps text with
  | none => some "the text is not well formed or its parentheses do not balance"
  | some es =>
    if let some n := es.findSome? reservedSourceName? then
      some s!"the name {String.ofList n} is reserved for the implementation"
    else
    match elabModules es with
    | .error msg => some msg
    | .ok fs => diagnoseForms (dropGeneric fs)

/-- Apply the last definition of a program, of type {lit}`T → T`, to an input tree. -/
def runMain (text : List Char) (input : Tree) : Option Tree := do
  let ds ← readProgram text
  let G ← load (ds.map Prod.snd)
  (← G.getLast?).apply input

end Geb.Kernel

end
