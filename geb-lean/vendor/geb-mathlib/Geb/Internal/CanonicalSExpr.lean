/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Internal.ConcreteSyntax
public import Mathlib.Data.Fin.VecNotation

/-!
# Canonical S-expressions as a data type

[FormalSExpr] models canonical S-expressions as a family indexed by the
octet string representing them, with an atom's index
`base10 (length xs) ++ [58] ++ xs` and a list's index
`40 :: xs ++ [41]`. `CSexp` is the non-dependent form of that family and
`CSexp.render` is the index function: `58`, `40` and `41` being `:`, `(`
and `)`, the atom index is `Geb.Csexp.printVerbatim` and the list index
is the parenthesized concatenation of the children's.

The point of carrying the family separately is
`Csexp.print_eq_render_toCSexp`. `Geb.Csexp.parse_print` says the local
parser accepts what the local printer emits; it does not say the output
is a canonical S-expression. Factoring the printer through `CSexp` says
exactly that, every `CSexp` over ASCII atoms rendering to one by
construction; the implementation notes below give the condition.

`Rose.toCSexp` is the other map into the family: a rose node becomes the
list whose head is its label and whose tail is its children, which is
the S-expression convention for applying a function to arguments and
agrees with the reading `Geb.Ast.toRose` fixes. It is a different
encoding of the same trees from `Ast.toCSexp`, and
`GebTests.Internal.CanonicalSExpr` exhibits a tree they spell
differently.

## Main definitions

* `CSexp` — canonical S-expressions, the W-type on `CSexp.Shape`.
* `CSexp.render` — the octet string a term is indexed by.
* `Ast.toCSexp` — the map underlying the implemented syntax.
* `Rose.toCSexp` — the label-applied-to-arguments encoding, with
  `Rose.print` its rendering and `Ast.printViaRose` its composite with
  the rose bijection.
* `Rose.parse`, `Ast.parseViaRose` — the parsers matching `Rose.print`
  and `Ast.printViaRose`, built from `Geb.Rose.parseChildren`, the
  bounded loop over a node's children that
  `Geb.Internal.ConcreteSyntax` supplies to every spelling closing a
  child list with `')'`.

## Main statements

* `Csexp.print_eq_render_toCSexp` — the implemented printer's output is
  the rendering of a canonical S-expression.
* `Rose.parse_print`, `Ast.parseViaRose_printViaRose` — the retraction
  law for the rose spelling, on `Rose` and on `Ast`, with
  `Rose.format_idem` and `Rose.print_injective` instantiating the
  generic corollaries at the first.

## Implementation notes

`CSexp.render` is canonical over ASCII atoms only. [RFC9804] counts an
atom's length in octets where `Csexp.printVerbatim` counts `Char`s, so
`CSexp.atom ['é']` renders as `1:é` where the format requires `2:é`.
Every atom this module constructs is ASCII — `Csexp.leafTok`,
`Csexp.forkTok`, and `Csexp.decOf` applied to a label, whose digits come
from `Csexp.digitChar` — so `Csexp.print_eq_render_toCSexp` states
conformance for the trees at hand. An atom type over octets would
discharge the condition outright.

A rose node's arity is unbounded, so `Geb.Rose.parseChildren` — shared,
and declared in `Geb.Internal.ConcreteSyntax` for that reason — reads
until the
closing parenthesis where `Geb.Csexp.parseStep` reads exactly two at a
fork and none at a leaf. Two consequences follow. First, the loop needs
a recursion bound, and it is `Rose.parseAux`'s own `Nat`, used at each
layer in two roles: undecremented as the loop's bound, and decremented
as the child parser's fuel. A measure `M` therefore has to satisfy two
inequalities at every node of `n` children: `M ≥ n + 1`, so that the loop
reaches the closing parenthesis, and `M > M'` for each child's `M'`, so
that one decrement still leaves that child enough. Second, the loop
returns a `List (Rose k)` where a node takes a `Fin n`-indexed tuple;
`Geb.Rose.ofList` is that transport and `Geb.Rose.ofList_ofFn` the
equation justifying it.

A node count satisfies both — `1 + Σ` over the children majorises
`n + 1` because each child counts at least one, and majorises `1 + M'`
for each child because a sum majorises each summand. The printed length
is taken not for any greater reach — it exceeds the node count several
times over — but because `Rose.parse` supplies the input length in any
case, so taking the bound in those terms leaves no node count to define
and no counterpart to `Geb.Csexp.size_le_length_printAst` to prove. The
bound is correspondingly far from tight.

`CSexp.render` concatenates a node's children by `Fin.foldr`, while the
parser produces them as a `List`; `CSexp.render_list_eq_flatten` states
their equality, and `Rose.print_node` is the resulting spelling
equation. `Rose.parseAux_print` rewrites with it, having to read a
node's own label and children. Where all that is needed of a child is
that its spelling opens with a parenthesis, the weaker
`Rose.exists_print_eq_cons` serves: `Rose.parseChildren_print` uses it to
identify the head of a child's spelling, and `Rose.parseAux_print` to
bound a node's arity by the length of its children's spellings.

## References

* [FormalSExpr]
* [RFC9804]

## Tags

canonical S-expression, conformance, parser, retraction, W-type
-/

@[expose] public section

namespace Geb

namespace CSexp

/-- The node shapes of a canonical S-expression: an atom carrying its
octets, or a list of a given length. [FormalSExpr]'s `MkCanonicalHint`
has no shape here; display hints have no counterpart in this
development, and nothing below emits one. -/
inductive Shape where
  /-- An atom, carrying its octets. -/
  | atom : List Char → Shape
  /-- A list of the given length. -/
  | list : Nat → Shape
  deriving DecidableEq

/-- The child index type: an atom has no children, a list of length `n`
has `n`. A `def` rather than an `abbrev`, so that instance search at a
shape already a literal cannot reduce past it to `Empty` or `Fin n` and
select mathlib's `Classical.choice`-dependent `FinEnum`; deciding
equality asks for the family at a general shape and reaches the named
instance either way. -/
def Arity : Shape → Type
  | .atom _ => Empty
  | .list n => Fin n

/-- Every arity is finitely enumerable. -/
instance instFinEnumArity (s : Shape) : FinEnum (Arity s) :=
  match s with
  | .atom _ => finEnumEmpty
  | .list n => finEnumFin n

end CSexp

/-- Canonical S-expressions, the non-dependent form of [FormalSExpr]'s
`CanonicalSExpr`. -/
abbrev CSexp : Type := WType CSexp.Arity

namespace CSexp

/-- An atom carrying the octets `s`. -/
def atom (s : List Char) : CSexp := WType.mk (.atom s) Empty.elim

/-- A list of `n` elements. -/
def list {n : Nat} (f : Fin n → CSexp) : CSexp := WType.mk (.list n) f

/-- The octet string a term is indexed by in [FormalSExpr]: an atom
renders as its verbatim encoding, a list as its elements' renderings
concatenated between parentheses. -/
def render : CSexp → List Char :=
  WType.elim (List Char) fun x ↦
    match x with
    | ⟨.atom s, _⟩ => Csexp.printVerbatim s
    | ⟨.list n, ch⟩ => '(' :: (Fin.foldr n (fun j acc ↦ ch j ++ acc) [] ++ [')'])

@[simp] theorem render_atom (s : List Char) :
    render (atom s) = Csexp.printVerbatim s := rfl

@[simp] theorem render_list {n : Nat} (f : Fin n → CSexp) :
    render (list f)
      = '(' :: (Fin.foldr n (fun j acc ↦ render (f j) ++ acc) [] ++ [')']) :=
  rfl

/-- `render_list` with the children's renderings as a `List`. `render`
concatenates a node's children by `Fin.foldr` where the parser produces
them as a `List`; `Rose.print_node` is proved from this equality. -/
theorem render_list_eq_flatten {n : Nat} (f : Fin n → CSexp) :
    render (list f) = '(' :: (((List.ofFn f).map render).flatten ++ [')']) := by
  rw [render_list]
  simp [Fin.foldr_eq_finRange_foldr, List.ofFn_eq_map, Function.comp_def]

end CSexp

namespace Ast

/-- The canonical S-expression the implemented syntax prints: a leaf is
the two-element list `(leaf label)`, a fork the three-element list
`(fork left right)`. -/
def toCSexp {k : Nat} : Ast k → CSexp :=
  WType.elim CSexp fun x ↦
    match x with
    | ⟨.leaf i, _⟩ =>
      CSexp.list ![CSexp.atom Csexp.leafTok, CSexp.atom (Csexp.decOf i.val)]
    | ⟨.fork, ch⟩ =>
      CSexp.list ![CSexp.atom Csexp.forkTok, ch (0 : Fin 2), ch (1 : Fin 2)]

@[simp] theorem toCSexp_leaf {k : Nat} (i : Fin k) :
    (leaf i).toCSexp
      = CSexp.list ![CSexp.atom Csexp.leafTok, CSexp.atom (Csexp.decOf i.val)] :=
  rfl

@[simp] theorem toCSexp_fork {k : Nat} (l r : Ast k) :
    (fork l r).toCSexp
      = CSexp.list ![CSexp.atom Csexp.forkTok, l.toCSexp, r.toCSexp] :=
  rfl

end Ast

namespace Rose

/-- The canonical S-expression of a rose tree: the head is the atom of
the node's label and the tail is its children, so a node is spelled as
its label applied to its arguments. -/
def toCSexp {k : Nat} : Rose k → CSexp :=
  WType.elim CSexp fun x ↦
    CSexp.list (Fin.cases (CSexp.atom (Csexp.decOf x.1.1.val)) x.2)

@[simp] theorem toCSexp_node {k : Nat} (i : Fin k) {n : Nat}
    (f : Fin n → Rose k) :
    (node i f).toCSexp
      = CSexp.list (Fin.cases (CSexp.atom (Csexp.decOf i.val))
          fun j ↦ (f j).toCSexp) :=
  rfl

/-- Print a rose tree as a canonical S-expression. -/
def print {k : Nat} (r : Rose k) : List Char := CSexp.render r.toCSexp

/-- The spelling of a node: its label as a verbatim atom, then its
children in order, all between parentheses. -/
theorem print_node {k : Nat} (i : Fin k) {n : Nat} (f : Fin n → Rose k) :
    print (node i f)
      = '(' :: (Csexp.printVerbatim (Csexp.decOf i.val)
          ++ ((List.ofFn f).map print).flatten ++ [')']) := by
  rw [print, toCSexp_node, CSexp.render_list_eq_flatten, List.ofFn_succ]
  simp only [Fin.cases_zero, Fin.cases_succ, List.map_cons, List.flatten_cons,
    List.map_ofFn, CSexp.render_atom, List.append_assoc]
  rfl

/-- Every spelling opens with a parenthesis, which is what tells a child
of a node from the parenthesis that closes the child list. -/
theorem exists_print_eq_cons {k : Nat} (r : Rose k) :
    ∃ cs : List Char, print r = '(' :: cs := by
  obtain ⟨⟨i, n⟩, f⟩ := r
  exact ⟨_, print_node i f⟩

/-! ## Parser -/

/-- One layer of the recursive descent: read a single s-expression,
delegating each child to `childParse` and the loop over them to
`parseChildren` with `loopFuel`. -/
def parseStep (k : Nat) (childParse : List Char → Option (Rose k × List Char))
    (loopFuel : Nat) : List Char → Option (Rose k × List Char)
  | [] => none
  | c :: cs =>
    if c = '(' then
      match Csexp.readVerbatim cs with
      | some (ds, cs1) =>
        match Csexp.digitsVal ds with
        | some m =>
          if h : m < k then
            (parseChildren childParse loopFuel cs1).map
              fun p ↦ (ofList ⟨m, h⟩ p.1, p.2)
          else none
        | none => none
      | none => none
    else none

/-- Recursive descent over the rose spelling, returning the tree and the
unconsumed input. The `Nat` argument bounds the recursion, as it does in
`Geb.Csexp.parseAst`, and serves in two roles at each layer:
undecremented as the child loop's bound, and decremented as the child
parser's fuel. `parse` supplies the input length, which `parseAux_print`
shows admits every tree the printer emits. -/
def parseAux (k : Nat) : Nat → List Char → Option (Rose k × List Char) :=
  Nat.rec (motive := fun _ ↦ List Char → Option (Rose k × List Char))
    (fun _ ↦ none) fun f ih ↦ parseStep k ih (f + 1)

@[simp] theorem parseAux_succ (k f : Nat) :
    parseAux k (f + 1) = parseStep k (parseAux k f) (f + 1) := rfl

/-- The parser of the rose spelling, rejecting trailing input. -/
def parse (k : Nat) (cs : List Char) : Option (Rose k) :=
  match parseAux k cs.length cs with
  | some (r, []) => some r
  | _ => none

/-! ## The retraction law -/

/-- The child loop reads back a printed child sequence, given a child
parser that reads back each of them and one unit of fuel per child plus
one for the closing parenthesis. -/
theorem parseChildren_print {k : Nat}
    (childParse : List Char → Option (Rose k × List Char)) :
    ∀ (ts : List (Rose k)) (fuel : Nat) (rest : List Char),
      (∀ t ∈ ts, ∀ r : List Char, childParse (print t ++ r) = some (t, r)) →
      ts.length < fuel →
      parseChildren childParse fuel ((ts.map print).flatten ++ ')' :: rest)
        = some (ts, rest) :=
  List.rec (motive := fun ts ↦ ∀ (fuel : Nat) (rest : List Char),
      (∀ t ∈ ts, ∀ r : List Char, childParse (print t ++ r) = some (t, r)) →
      ts.length < fuel →
      parseChildren childParse fuel ((ts.map print).flatten ++ ')' :: rest)
        = some (ts, rest))
    (fun fuel rest _ hfuel ↦ by
      obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by omega⟩
      simp)
    (fun t ts ih fuel rest hchild hfuel ↦ by
      obtain ⟨g, rfl⟩ : ∃ g, fuel = g + 1 := ⟨fuel - 1, by omega⟩
      obtain ⟨body, hbody⟩ := exists_print_eq_cons t
      have hne : '(' ≠ ')' := by decide
      have hlt : ts.length < g := by simp at hfuel; omega
      have hcons : print t ++ ((ts.map print).flatten ++ ')' :: rest)
          = '(' :: (body ++ ((ts.map print).flatten ++ ')' :: rest)) := by
        rw [hbody, List.cons_append]
      rw [List.map_cons, List.flatten_cons, List.append_assoc, hcons,
        parseChildren_succ_cons _ _ _ _ hne, ← hcons,
        hchild t (by simp) _, Option.bind_some,
        ih g rest (fun x hx ↦ hchild x (by simp [hx])) hlt, Option.map_some])

/-- The parser inverts the printer on printed input, given fuel at least
the printed length, and returns the unconsumed remainder. The module
docstring's implementation notes say what a measure has to satisfy and
why this one is taken. -/
theorem parseAux_print {k : Nat} (r : Rose k) :
    ∀ (f : Nat) (rest : List Char), (print r).length ≤ f →
      parseAux k f (print r ++ rest) = some (r, rest) :=
  WType.rec (motive := fun r ↦ ∀ (f : Nat) (rest : List Char),
      (print r).length ≤ f → parseAux k f (print r ++ rest) = some (r, rest))
    (fun s ch ih f rest hf ↦ by
      obtain ⟨i, n⟩ := s
      change (print (node i ch)).length ≤ f at hf
      change parseAux k f (print (node i ch) ++ rest) = some (node i ch, rest)
      rw [print_node] at hf ⊢
      cases f with
      | zero => simp at hf
      | succ g =>
        have hL : (((List.ofFn ch).map print).flatten).length ≤ g := by
          simp only [List.length_cons, List.length_append] at hf
          omega
        have hchild : ∀ t ∈ List.ofFn ch, ∀ r : List Char,
            parseAux k g (print t ++ r) = some (t, r) := by
          intro t ht r'
          obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ht
          refine ih j g r' (le_trans ?_ hL)
          exact (List.sublist_flatten_of_mem
            (List.mem_map_of_mem (List.mem_ofFn.mpr ⟨j, rfl⟩))).length_le
        have hfuel : (List.ofFn ch).length < g + 1 := by
          have hpos : ∀ x ∈ ((List.ofFn ch).map print).map List.length, 1 ≤ x := by
            intro x hx
            obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hx
            obtain ⟨t, _, rfl⟩ := List.mem_map.mp hy
            obtain ⟨b, hb⟩ := exists_print_eq_cons t
            simp [hb]
          have h := List.length_le_sum_of_one_le _ hpos
          rw [List.length_map, List.length_map, ← List.length_flatten] at h
          omega
        rw [List.cons_append, parseAux_succ]
        simp only [parseStep, List.append_assoc, List.singleton_append,
          Csexp.readVerbatim_append, Csexp.digitsVal_decOf, Fin.is_lt,
          parseChildren_print _ _ _ _ hchild hfuel, Option.map_some,
          if_true, dif_pos, Fin.eta, ofList_ofFn]) r

/-- The retraction law for the rose spelling: printing a rose tree and
parsing the result returns that tree. -/
theorem parse_print {k : Nat} (r : Rose k) : parse k (print r) = some r := by
  unfold parse
  rw [show print r = print r ++ [] by simp,
    parseAux_print r _ [] (by simp)]

/-! ## The generic corollaries, instantiated here -/

/-- `parse_print` in the form the generic corollaries consume. -/
theorem retraction (k : Nat) : Retraction (parse k) (print (k := k)) :=
  parse_print

/-- `Geb.format_idem` at the rose spelling. -/
theorem format_idem (k : Nat) (c : List Char) :
    (format (parse k) print c).bind (format (parse k) print)
      = format (parse k) print c :=
  Geb.format_idem _ _ (retraction k) c

/-- `Geb.print_injective` at the rose spelling. -/
theorem print_injective (k : Nat) : Function.Injective (print (k := k)) :=
  Geb.print_injective _ _ (retraction k)

end Rose

namespace Ast

/-- Print an abstract syntax tree through the rose presentation. Not the
same spelling as `Geb.Csexp.print`, which prints from `Ast` directly;
see `GebTests.Internal.CanonicalSExpr`. -/
def printViaRose {k : Nat} (a : Ast k) : List Char := Rose.print a.toRose

/-- Parse an abstract syntax tree from the rose spelling, by parsing a
rose tree and crossing the bijection. -/
def parseViaRose (k : Nat) (cs : List Char) : Option (Ast k) :=
  (Rose.parse k cs).map ofRose

/-- The retraction law for the rose spelling read as a syntax on `Ast`:
the rose retraction transported along `Ast.ofRose_toRose`. -/
theorem parseViaRose_printViaRose {k : Nat} (a : Ast k) :
    parseViaRose k (printViaRose a) = some a := by
  rw [parseViaRose, printViaRose, Rose.parse_print, Option.map_some,
    ofRose_toRose]

end Ast

namespace Csexp

/-- The implemented printer's output is the rendering of a canonical
S-expression, hence a canonical S-expression by construction. -/
theorem printAst_eq_render_toCSexp {k : Nat} (a : Ast k) :
    printAst a = CSexp.render a.toCSexp :=
  Ast.ind (motive := fun a ↦ printAst a = CSexp.render a.toCSexp)
    (fun i ↦ by
      simp only [printAst_leaf, Ast.toCSexp_leaf, CSexp.render_list,
        Fin.foldr_succ, Fin.foldr_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, CSexp.render_atom, List.append_nil,
        List.append_assoc])
    (fun l r ihl ihr ↦ by
      simp only [printAst_fork, Ast.toCSexp_fork, CSexp.render_list,
        Fin.foldr_succ, Fin.foldr_zero, Matrix.cons_val_zero,
        Matrix.cons_val_succ, CSexp.render_atom, List.append_nil,
        List.append_assoc, ihl, ihr]) a

/-- `printAst_eq_render_toCSexp` at the syntax's printer. This is the
conformance statement `parse_print` does not make: that law says only
that the local parser accepts the local printer's output. -/
theorem print_eq_render_toCSexp {k : Nat} (a : Ast k) :
    print a = CSexp.render a.toCSexp :=
  printAst_eq_render_toCSexp a

end Csexp

end Geb
