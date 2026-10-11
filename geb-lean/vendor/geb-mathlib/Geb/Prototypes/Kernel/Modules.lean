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

Every name of a declaration's body is renamed to what it denotes in the flat program, a name
bound around it in a term excepted; the forms of the kernel and of the datatype language give
each child its role, so a quoted datum and the name of a hole are never renamed. A name visible
in a block is never declared again in it, nor imported, nor bound by a parameter: a clash is
rejected, as are an import naming no module or leaving a parameter unsupplied and an export
naming nothing. A program without modules is unchanged.

## Main definitions

* {lit}`rename` — the renaming of an S-expression in a role.
* {lit}`expandModules` — the elaboration of a program's modules.
* {lit}`readProgram`, {lit}`runMain`, {lit}`diagnose` — the reading of a program through the
  elaboration of its modules.

## Implementation notes

The elaboration of a block is a fold over its forms; the elaboration of a nested module and of
an instance is one level of a tower built by {lit}`Nat.rec`, bounded by the number of module
forms in the program, since a module imports only modules declared before it.

## Tags

module, import, export, parameter, qualified name
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

/-- The role of an S-expression in its parent: a term, a type, a clause of a case analysis,
binders, or a quoted datum. -/
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
  /-- A quoted datum or the name of a hole, unchanged. -/
  | datum
  deriving DecidableEq

/-- The names a binder or a list of binders binds. -/
def boundBy (b : SExp) : List Ident := (binders b).filterMap fun c ↦ c.children.head?.bind (·.label)

/-- The variables a pattern {lit}`(c x …)` binds. -/
def patternVars (p : SExp) : List Ident := (p.children.drop 1).filterMap (·.label)

/-- One node renamed in each role, from its children renamed in each: in a term, an atom bound
around it is kept and any other visible name renamed, the forms of the kernel and of the
datatype language giving each child its role; in a type every visible name is renamed. -/
def renameStep (vis : Visible) (a : Option Ident)
    (rs : List (SExp × (Role → List Ident → SExp))) (r : Role) (bound : List Ident) : SExp :=
  let orig := RoseTree.node a (rs.map Prod.fst)
  let as (r : Role) (bound : List Ident) (xs : List (SExp × (Role → List Ident → SExp))) :=
    xs.map (·.2 r bound)
  match r, a with
  | .datum, _ => orig
  | .type, some s => atom (flat vis s)
  | .type, none => slist (as .type [] rs)
  | .term, some s => atom (if bound.contains s then s else flat vis s)
  | .binders, some _ => orig
  | .binders, none =>
    match rs with
    | (x, _) :: rest =>
      if x.label.isSome then slist (x :: as .type [] rest) else slist (as .binders [] rs)
    | [] => orig
  | .clause, some _ => orig
  | .clause, none =>
    match rs with
    | [(p, _), (_, body)] =>
      if p.label.isSome then slist [p, body .term bound]
      else
        let pat := match p.children with
          | c :: xs => slist (atom (c.label.map (flat vis) |>.getD []) :: xs)
          | [] => p
        slist [pat, body .term (patternVars p ++ bound)]
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
          slist [h, x, rA .type [], e .term bound, body .term (x.label.toList ++ bound)]
        | _ => orig
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
      else slist (rh .term bound :: as .term bound rest)

/-- An S-expression renamed in a role, under the visible names and the names bound around
it. -/
def rename (vis : Visible) (e : SExp) (r : Role) (bound : List Ident) : SExp :=
  RoseTree.para (renameStep vis) e r bound

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

/-- The state of the elaboration of a block: the names visible in it, the declarations emitted,
the modules declared, by their paths from the root, the names the block exports, the block's
members and the modules elaborated. -/
structure ElabState where
  /-- The names visible in the block. -/
  vis : Visible
  /-- The declarations emitted, in order. -/
  out : List SExp
  /-- The modules declared, by their paths from the root. -/
  reg : List (Ident × ModDef)
  /-- The names the block's export lists name. -/
  exports : List Ident
  /-- The block's members, in order. -/
  members : List Member
  /-- The modules elaborated, each after the modules nested in it. -/
  mods : List ModNode

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

/-- The keywords of modules, which no declaration takes. -/
def moduleKeywords : List (List Char) :=
  [['m', 'o', 'd', 'u', 'l', 'e'], ['p', 'a', 'r', 'a', 'm', 'e', 't', 'e', 'r'],
    ['i', 'm', 'p', 'o', 'r', 't'], ['e', 'x', 'p', 'o', 'r', 't'],
    ['i', 'n', 't', 'e', 'r', 'f', 'a', 'c', 'e']]

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

/-- The argument of a parameter bound at an instance: a sort {lit}`(parameter A)` as a type
abbreviation of the argument, and an operation {lit}`(parameter (f (A …) R))` as a definition
of the argument applied to fresh variables of the argument types, its result bound at type
{lit}`R` so that the argument's type is checked; the parameter's types are renamed in the
template's scope and the argument in the importer's. -/
def bindParam (inst : Ident) (importer : Visible) (st : ElabState) (p arg : SExp) :
    Elab ElabState := do
  let bad := "a parameter is neither a sort nor an operation"
  match p.children with
  | [_, sig] =>
    match sig.label, sig.children with
    | some s, _ => do
      let fl := qualify inst s
      let st ← declare st s fl
      pure { st with out := st.out ++ [slist [atom ['d', 'e', 'f', 't', 'y', 'p', 'e'], atom fl,
        rename importer arg .type []]] }
    | none, [x, args, res] => do
      let s ← need x.label bad
      let fl := qualify inst s
      let vars := (args.children.zipIdx).map fun (_, i) ↦ '%' :: 'm' :: Csexp.decOf i
      let rv := ['%', 'r']
      let call := if vars.isEmpty then rename importer arg .term []
        else slist (rename importer arg .term [] :: vars.map atom)
      let body := slist [atom ['l', 'e', 't'], atom rv, rename st.vis res .type [], call, atom rv]
      let term := if vars.isEmpty then body
        else slist [atom ['l', 'a', 'm'], slist ((args.children.zip vars).map fun (A, v) ↦
          slist [atom v, rename st.vis A .type []]), body]
      let st ← declare st s fl
      pure { st with
        out := st.out ++ [slist [atom ['d', 'e', 'f'], atom fl, term]]
        members := st.members ++ [.decl fl] }
    | _, _ => throw bad
  | _ => throw bad

/-- One declaration elaborated in a block under a prefix: its name qualified and made visible,
its body renamed. -/
def elabDecl (pre : Ident) (st : ElabState) (e : SExp) : Elab ElabState := do
  let other := "a form is neither a declaration, a module, an import nor an export"
  match e.children with
  | kw :: x :: rest => do
    let s ← need x.label other
    let fl := qualify pre s
    let emit (st : ElabState) (body : List SExp) (mem : List Member) : ElabState :=
      { st with out := st.out ++ [slist (kw :: atom fl :: body)], members := st.members ++ mem }
    if isKw kw "def" then
      match rest with
      | [b] => return emit (← declare st s fl) [rename st.vis b .term []] [.decl fl]
      | _ => throw other
    else if isKw kw "deftype" || isKw kw "defnum" then
      match rest with
      | [b] => return emit (← declare st s fl) [rename st.vis b .type []] []
      | _ => throw other
    else if isKw kw "defn" then
      match rest with
      | [ps, res, b] => return emit (← declare st s fl) [rename st.vis ps .binders [],
          rename st.vis res .type [], rename st.vis b .term (boundBy ps)] [.decl fl]
      | _ => throw other
    else if isKw kw "data" || isKw kw "tree-data" then do
      let st1 ← declare st s fl
      let ctors ← rest.mapM fun c ↦ match c.children with
        | n :: fs => need (n.label.map fun cn ↦ (cn, fs)) other
        | [] => throw other
      let st2 ← declareAll st1 (ctors.map fun (cn, _) ↦ (cn, qualify pre cn))
      return { st2 with
        out := st.out ++ [slist (kw :: atom fl :: ctors.map fun (cn, fs) ↦
          slist (atom (qualify pre cn) :: fs.map (rename st1.vis · .type [])))]
        members := st.members ++ ctors.map fun (cn, _) ↦ .decl (qualify pre cn) }
    else throw other
  | _ => throw other

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
def instantiate (rec : Ident → ElabState → SExp → Elab ElabState) (st : ElabState)
    (params : List SExp) (exports : List Ident) (forms : List SExp) (scope : Visible)
    (inst : Ident) (args : List SExp) : Elab ElabState := do
  let st1 ← (params.zip args).foldlM (fun acc (prm, arg) ↦ bindParam inst st.vis acc prm arg)
    ⟨scope, st.out, st.reg, exports, [], st.mods⟩
  forms.foldlM (rec inst) st1

/-- A template's instance at opaque arguments, which the stage-1 compiler checks and every
compiler then drops: the form {lit}`(%generic …)` over the declarations of fresh arguments, a sort
{lit}`(%sort S)` for each sort parameter and a constant {lit}`(%postulate P A)` of the parameter's
type for each operation, the parameter's sorts read as their arguments, followed by the
instance's forms. -/
def genericOf (rec : Ident → ElabState → SExp → Elab ElabState) (st : ElabState)
    (params : List SExp) (exports : List Ident) (forms : List SExp) (scope : Visible)
    (path : Ident) : Elab SExp := do
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
          (fun A r ↦ slist [arrowKw, rename vis A .type [], r]) (rename vis res .type [])]
      | none, _ => slist [postulateKw, a]
    | none => slist [postulateKw, a]
  let st2 ← instantiate rec { st with out := [] } params exports forms scope
    (path ++ '%' :: ['g', 'e', 'n', 'e', 'r', 'i', 'c']) args
  pure (slist (atom ['%', 'g', 'e', 'n', 'e', 'r', 'i', 'c'] :: decls ++ st2.out))

/-- The elaboration of one form of a block, given the elaboration of the forms of the modules
nested in it and of the templates it instantiates, one level of nesting fewer. -/
def elabStep (rec : Ident → ElabState → SExp → Elab ElabState) (pre : Ident)
    (st : ElabState) (e : SExp) : Elab ElabState :=
  match e.children with
  | kw :: rest =>
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
        declareAll { st with
          out := st2.out
          reg := st2.reg
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
          declareAll ⟨st.vis, st1.out, st1.reg ++ [(path, .plain ex)], st.exports,
            st.members ++ [.sub path], st1.mods ++ [⟨path, st1.members, ex⟩]⟩
            (importAs (some s) ex)
        else
          let (exs, body) := splitHead "export" others
          let exports := exs.flatMap fun x ↦ (x.children.drop 1).filterMap (·.label)
          let g ← genericOf rec st params exports body st.vis path
          pure { st with out := st.out ++ [g]
                         reg := st.reg ++ [(path, .template params exports body st.vis)] }
      | [] => throw "a module is not named"
    else elabDecl pre st e
  | [] => throw "a form is neither a declaration, a module, an import nor an export"

/-- The elaboration of a form at a depth of nesting and instantiation: none beyond it. -/
def elabAt (n : ℕ) : Ident → ElabState → SExp → Elab ElabState :=
  Nat.rec (motive := fun _ ↦ Ident → ElabState → SExp → Elab ElabState)
    (fun _ _ _ ↦ throw "modules nest or instantiate beyond their number")
    (fun _ rec ↦ elabStep rec) n

/-- The number of module forms in a list of S-expressions, a bound on the depth of nesting and
of instantiation. -/
def moduleCount (es : List SExp) : ℕ :=
  (es.map (RoseTree.elim fun a (rs : List ℕ) ↦
    rs.sum + if a.any (String.ofList · == "module") then 1 else 0)).sum

/-- A program's forms with its modules elaborated, with its tree of modules, each module after
those nested in it and the root block last: each declaration under its qualified name,
the instances of modules with parameters at their imports, and every name renamed to what it
denotes; a failure when a name clashes with one visible, an import names no module or leaves a
parameter unsupplied, an export names nothing, or a form is not a declaration, a module, an
import or an export. -/
def elabTree (es : List SExp) : Elab (List SExp × List ModNode) := do
  let st ← es.foldlM (elabAt (moduleCount es + 1) []) ⟨[], [], [], [], [], []⟩
  if st.exports.isEmpty then pure (st.out, st.mods ++ [⟨[], st.members, []⟩])
  else throw "the program exports names"

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

/-- The definitions of a program, its modules elaborated, as names with kernel terms. -/
def readProgram (text : List Char) : Option (List (List Char × Tree)) := do
  readForms (dropGeneric (← expandModules (← readSExps text)))

/-- The first failure of a program, as a message: text that is not well formed, modules that do
not elaborate, or the first failure of {name}`diagnoseForms`; nothing when the program reads and
loads. -/
def diagnose (text : List Char) : Option String :=
  match readSExps text with
  | none => some "the text is not well formed or its parentheses do not balance"
  | some es =>
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
