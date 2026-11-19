/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Kernel.Document
public import Geb.Prototypes.Kernel.Modules

set_option doc.verso true in
/-!
# Chains of bindings and of tests in source documents

The kernel's {lit}`let` binds one variable and its conditional tests one condition, so a
sequence of bindings or of tests written in them nests, one level a binding or a test. The
elaboration of modules expands the forms {lit}`(let* ((x A e) …) body)` and
{lit}`(cond (test value) … (else default))` to those nested forms
({name}`Geb.Kernel.letChain`, {name}`Geb.Kernel.condChain`). The conversion here is the inverse
on source documents: a {lit}`let` or {lit}`let*` whose body is a {lit}`let` or a {lit}`let*`
becomes one {lit}`let*` of the bindings of both, and an {lit}`if`, or the default of a
{lit}`cond`, whose last branch is an {lit}`if` or a {lit}`cond` becomes one {lit}`cond` of the
clauses of both. A form that begins no such sequence is left as it is written, so a single
binding stays a {lit}`let` and a single test an {lit}`if`.

A form is converted only where the elaboration of modules expands the two keywords: in a term,
as {name}`Geb.Kernel.renameStep` assigns the roles of the children of each form of the kernel
and of the datatype language. A type, a list of binders, a pattern, a quoted datum and the name
of a hole are unchanged, as is every form of a block other than a module and the definitions
{lit}`def` and {lit}`defn`; the arguments of an import are unchanged, their roles being those of
the parameters they supply.

The conversion acts on S-expressions with comments, and moves each comment line with the form
it precedes: the comment lines before a nested form precede the binding or the clause it
becomes, those before the default of a chain of tests precede its {lit}`else` clause, and the
comment lines before the end of a nested form follow those of the forms inside it.

## Main definitions

* {lit}`bindingsOf`, {lit}`clausesOf` — a form as the bindings and the body, or the clauses, of
  a sequence.
* {lit}`chainStep`, {lit}`chains` — the conversion of an S-expression in a role.
* {lit}`Doc.chains` — the conversion of a document.
* {lit}`formatChains` — the formatter of the converted document.

## Implementation notes

That the converted document elaborates to the declarations of the original is tested on
examples of each role, and not proved. A {lit}`cond` is joined with a form before or after it
only when it is well formed, since a malformed one elaborates to the empty term alone and a
joined one would take its neighbours with it; a {lit}`let*` needs no such condition, the
bindings before a malformed one being kept by {name}`Geb.Kernel.letChain` either way.

## Tags

S-expression, source conversion, sequential binding, conditional, formatter
-/

set_option doc.verso true

@[expose] public section

namespace Geb.Kernel.Document

/-- Whether an S-expression with comments is the atom of a keyword. -/
def isKeyword (e : SExpr) (k : String) : Bool :=
  e.label.2.any (String.ofList · == k) && e.children.isEmpty

/-- A list without trivia. -/
def bareList (cs : List SExpr) : SExpr := RoseTree.node (.none, none) cs

/-- An S-expression after further comment lines and, when one is given, an empty line: the
lines precede its own comment lines, and the empty line the first of those, or the S-expression
itself when it has none. -/
def withLead (ls : List Line) (gap : Bool) (t : SExpr) : SExpr :=
  let tr := t.label.1
  let (lead, g) := match tr.lead with
    | [] => (ls, gap || tr.gap)
    | l :: rest => (ls ++ ⟨gap || l.gap, l.text⟩ :: rest, tr.gap)
  RoseTree.node (⟨lead, g, tr.close⟩, t.label.2) t.children

/-- An S-expression after what precedes a list and the keyword at its head: the comment lines
and the empty line before the list, then those before the keyword. -/
def afterHead (t kw e : SExpr) : SExpr :=
  withLead t.label.1.lead t.label.1.gap (withLead kw.label.1.lead kw.label.1.gap e)

/-- An S-expression without the comment lines and the empty line before it. -/
def unled (t : SExpr) : SExpr :=
  RoseTree.node (⟨[], false, t.label.1.close⟩, t.label.2) t.children

/-- S-expressions with comment lines added before the first. -/
def leadFirst (ls : List Line) : List SExpr → List SExpr
  | [] => []
  | t :: ts => withLead ls false t :: ts

/-- A keyword's atom renamed, with its trivia. -/
def renamed (kw : SExpr) (k : List Char) : SExpr := RoseTree.node (kw.label.1, some k) []

/-- Whether an S-expression is a list of two elements. -/
def isPair (c : SExpr) : Bool := c.label.2.isNone && c.children.length == 2

/-- Whether an S-expression is headed by the keyword {lit}`else`. -/
def isElse (c : SExpr) : Bool := c.children.head?.any (isKeyword · "else")

/-- Whether clauses are those of a well-formed {lit}`cond`: each a test and a value, the last
alone headed by {lit}`else`. -/
def condWf (cs : List SExpr) : Bool :=
  match cs.reverse with
  | c :: rest => isPair c && isElse c && rest.all fun c ↦ isPair c && !isElse c
  | [] => false

/-- A form as a sequence of bindings: the binding of {lit}`(let x A e body)`, or the bindings of
{lit}`(let* (b …) body)`, the first after what precedes the form; the comment lines before the
end of the list of bindings; the body; and the comment lines before the form's end. -/
def bindingsOf (t : SExpr) : Option (List SExpr × List Line × SExpr × List Line) :=
  match t.label.2, t.children with
  | none, [kw, x, A, e, body] =>
    if isKeyword kw "let" && x.label.2.isSome then
      some ([afterHead t kw (bareList [x, A, e])], [], body, t.label.1.close)
    else none
  | none, [kw, bs, body] =>
    if isKeyword kw "let*" && bs.label.2.isNone then
      match bs.children with
      | b :: rest =>
        some (afterHead t kw (withLead bs.label.1.lead bs.label.1.gap b) :: rest,
          bs.label.1.close, body, t.label.1.close)
      | [] => none
    else none
  | _, _ => none

/-- A form as a sequence of clauses: of {lit}`(if p a b)` the clause of its test and the
{lit}`else` clause of its last branch, which what precedes the branch then precedes, or the
clauses of a well-formed {lit}`cond`, the first after what precedes the form; and the comment
lines before the form's end. A test that is the keyword {lit}`else` begins no clause. -/
def clausesOf (t : SExpr) : Option (List SExpr × List Line) :=
  match t.label.2, t.children with
  | none, kw :: rest =>
    if isKeyword kw "if" then
      match rest with
      | [p, a, b] =>
        if isKeyword p "else" then none
        else
          let default := bareList [bareAtom ['e', 'l', 's', 'e'], unled b]
          some ([afterHead t kw (bareList [p, a]), withLead b.label.1.lead b.label.1.gap default],
            t.label.1.close)
      | _ => none
    else if isKeyword kw "cond" && condWf rest then
      match rest with
      | c :: cs => some (afterHead t kw c :: cs, t.label.1.close)
      | [] => none
    else none
  | _, _ => none

/-- A form of bindings joined with its body, when the body is a sequence of bindings: the
{lit}`let*` of the form's bindings, given with the trivia of their list, and the body's. -/
def joinBindings (tr : Trivia) (kw : SExpr) (lt : Trivia) (own : List SExpr) (body : SExpr) :
    Option SExpr :=
  (bindingsOf body).map fun (bs, bsClose, b, close) ↦
    RoseTree.node (⟨tr.lead, tr.gap, close ++ tr.close⟩, none)
      [renamed kw ['l', 'e', 't', '*'],
        RoseTree.node (⟨lt.lead, lt.gap, bsClose⟩, none) (own ++ leadFirst lt.close bs), b]

/-- A form of clauses joined with its last branch, when the branch is a sequence of clauses:
the {lit}`cond` of the form's clauses before the branch and the branch's, given the comment
lines between the branch's end and the form's. -/
def joinClauses (tr : Trivia) (kw : SExpr) (own : List SExpr) (ownClose : List Line)
    (last : SExpr) : Option SExpr :=
  (clausesOf last).map fun (cs, close) ↦
    RoseTree.node (⟨tr.lead, tr.gap, close ++ ownClose ++ tr.close⟩, none)
      (renamed kw ['c', 'o', 'n', 'd'] :: own ++ cs)

/-- One node converted in each role, or as a form of a block where no role is given, from its
children converted in each. The roles of a form's children are those
{name}`Geb.Kernel.renameStep` gives them. -/
def chainStep (l : Trivia × Option (List Char)) (rs : List (SExpr × (Option Role → SExpr)))
    (r : Option Role) : SExpr :=
  let orig := RoseTree.node l (rs.map Prod.fst)
  let as (r : Option Role) (xs : List (SExpr × (Option Role → SExpr))) := xs.map (·.2 r)
  let term : Option Role := some .term
  match l.2, r, rs with
  | some _, _, _ => orig
  | none, _, [] => orig
  | none, none, (kw, _) :: rest =>
    if isKeyword kw "module" then RoseTree.node l (kw :: as none rest)
    else if isKeyword kw "def" then
      match rest with
      | [(x, _), (_, b)] => RoseTree.node l [kw, x, b term]
      | _ => orig
    else if isKeyword kw "defn" then
      match rest with
      | [(x, _), (ps, _), (res, _), (_, b)] => RoseTree.node l [kw, x, ps, res, b term]
      | _ => orig
    else orig
  | none, some .clause, [(p, _), (_, body)] => RoseTree.node l [p, body term]
  | none, some .letBinding, [(x, _), (A, _), (_, e)] => RoseTree.node l [x, A, e term]
  | none, some .letBindings, _ => RoseTree.node l (as (some .letBinding) rs)
  | none, some .condClause, [(p, rp), (_, body)] =>
    RoseTree.node l [if isKeyword p "else" then p else rp term, body term]
  | none, some .term, (h, _) :: rest =>
    let keep (cs : List SExpr) : SExpr := RoseTree.node l (h :: cs)
    let headed (ks : List String) : Bool := ks.any (isKeyword h)
    if headed ["quote", "hole", "datum", "nil"] then orig
    else if headed ["decode", "fold", "para", "iter"] then
      match rest with
      | (D, _) :: xs => keep (D :: as term xs)
      | [] => orig
    else if headed ["foldr", "lcase"] then
      match rest with
      | (A, _) :: (B, _) :: xs => keep (A :: B :: as term xs)
      | _ => orig
    else if isKeyword h "lam" then
      match rest with
      | [(b, _), (_, body)] => keep [b, body term]
      | _ => orig
    else if isKeyword h "case" then
      match rest with
      | (_, e) :: cs => keep (e term :: as (some .clause) cs)
      | [] => orig
    else if isKeyword h "cata" then
      match rest with
      | (D, _) :: (R, _) :: (_, e) :: cs => keep (D :: R :: e term :: as (some .clause) cs)
      | _ => orig
    else if isKeyword h "let" then
      match rest with
      | [(x, _), (A, _), (_, e), (_, body)] =>
        let e := e term
        let body := body term
        ((if x.label.2.isSome then joinBindings l.1 h .none [bareList [x, A, e]] body
          else none).getD (keep [x, A, e, body]))
      | _ => orig
    else if isKeyword h "let*" then
      match rest with
      | [(bs, rbs), (_, body)] =>
        if bs.label.2.isNone then
          let bs := rbs (some .letBindings)
          let body := body term
          ((if bs.children.isEmpty then none
            else joinBindings l.1 h bs.label.1 bs.children body).getD (keep [bs, body]))
        else orig
      | _ => orig
    else if isKeyword h "cond" then
      let cs := as (some .condClause) rest
      let joined := if condWf cs then
          match cs.reverse with
          | c :: init =>
            match c.children with
            | [k, d] => joinClauses l.1 h init.reverse c.label.1.close (afterHead c k d)
            | _ => none
          | [] => none
        else none
      joined.getD (keep cs)
    else
      let cs := as term rs
      let joined := if isKeyword h "if" then
          match cs with
          | [kw, p, a, b] =>
            if isKeyword p "else" then none else joinClauses l.1 kw [bareList [p, a]] [] b
          | _ => none
        else none
      joined.getD (RoseTree.node l cs)
  | none, some _, _ => orig

/-- An S-expression with comments converted in a role, or as a form of a block where no role is
given: each sequence of bindings a {lit}`let*` and each sequence of tests a {lit}`cond`. -/
def chains (t : SExpr) (r : Option Role) : SExpr := RoseTree.para chainStep t r

/-- A document converted: each of its S-expressions as a form of a block. -/
def Doc.chains (d : Doc) : Doc := ⟨d.items.map (Document.chains · none), d.trail⟩

/-- The formatter of the converted document: a text read, converted and printed within a line
width, or nothing when its parentheses do not balance. -/
def formatChains (lim : ℕ) (text : List Char) : Option (List Char) :=
  (readDoc text).bind fun d ↦
    let d := d.chains
    if d.wf then some (printAt (defaultLayout .profile lim d) d) else none

end Geb.Kernel.Document

end
