/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.W.Basic

/-!
# Concrete syntaxes for the Geb AST (prototype)

The abstract syntax is the initial algebra of `F X = Fin k + X × X`.
A concrete syntax is a pair `parse : C → Option D`, `print : D → C`
satisfying the retraction law `parse (print d) = some d`; formatter
idempotence and injectivity of `print` are corollaries, proved once
here for every syntax.

This module carries the format-independent core (the abstract syntax,
its annotated form, the rose presentation), one worked concrete
syntax, the canonical S-expression form of [RFC9804], and the parser
machinery more than one spelling shares: the decimal layer and the
bounded loop over a rose node's children.

Every tree type here is a `WType`, so its recursion is carried by
`WType.elim`, `WType.para` and `WType.rec`.

## Main definitions

* `Ast` — the abstract syntax, the W-type on `Ast.Shape`.
* `Ast.toRose`, `Ast.ofRose` — the two directions of the rose
  presentation's bijection with `Ast`.
* `Tree` — the abstract syntax with every node decorated by an `A`,
  with `Tree.map`, `Tree.extract`, `Tree.duplicate` its functor and
  comonad structure and `Tree.erase` the forgetful map to `Ast`.
* `Ann`, `Doc` — the annotation vocabulary and the annotated document
  type `Tree k Ann`, with `Ast.trivialDoc` the empty decoration.
* `Rose` — the rose-tree presentation of the same fixed point, with
  `Rose.node` and `Rose.ofList` its constructors and `Rose.snoc`
  appending a child to one.
* `Rose.parseChildren` — the bounded loop reading a rose node's
  children up to the closing parenthesis, shared by every spelling of
  the rose presentation that closes a child list with `')'`.
* `Retraction`, `format` — the law skeleton a concrete syntax proves.
* `Csexp.print`, `Csexp.parse` — the [RFC9804] canonical S-expression
  syntax.

## Main statements

* `Ast.ind` — the two-constructor induction principle on `Ast`.
* `Ast.ofRose_toRose`, `Ast.toRose_ofRose` — the rose presentation is
  a bijection.
* `Rose.ofList_ofFn` — a rose node rebuilt by `Rose.ofList` from the
  list of its children is that node. It is the equation justifying the
  transport a variable-arity parser needs.
* `Csexp.parse_print` — the retraction law for the S-expression syntax,
  from `Csexp.parseAst_printAst` and `Csexp.size_le_length_printAst`.
* `Csexp.readVerbatim_append` — a printed atom reads back whole,
  whatever it contains.
* `Ast.erase_trivialDoc` — the trivial decoration is erased away.
* `Csexp.format_idem`, `Csexp.print_injective` — the generic corollaries
  instantiated, which is what shows the law skeleton applies to a
  syntax rather than only to a hypothetical one.
* `Geb.format_idem`, `Geb.print_injective` — the corollaries of a
  retraction, proved once for every syntax.
* `Tree.extract_duplicate`, `Tree.map_extract_duplicate`,
  `Tree.duplicate_duplicate` — the comonad laws on the annotated
  syntax, with `Tree.map_id` and `Tree.map_map` the functor laws they
  presuppose and `Tree.extract_map`, `Tree.duplicate_map` the
  naturality of the two structure maps.

## Implementation notes

`Csexp.parseAst` recurses on an explicit `Nat` bound rather than on its
input: the recursion descends only through the remainder each call
returns, which is not a form Lean's structural recursion accepts.
`Csexp.parse` supplies the input length, and `Csexp.size_le_length_printAst`
shows that bound admits every tree the printer emits.

The decimal layer is written here rather than reused, and the reason is
`Classical.choice` throughout. mathlib's `Nat.digits` depends on it.
Core supplies the whole layer — `Nat.toDigits`, which agrees with
`Csexp.decOf` pointwise on base 10, the decoder `Nat.ofDigitChars`, and
the same round trip in total form, `Nat.ofDigitChars_ten_toDigits`,
where `Csexp.digitsVal_decOf` is partial. It cannot be used. That round
trip depends on `Classical.choice`, and so does every lemma descending
from `toDigits b n` to `toDigits b (n / b)` — `Nat.toDigits_eq_if` and
`Nat.toDigits_of_base_le` — so it can be neither imported nor reproved.
The boundary is not depth but direction: the printer's descent lemmas
are choice-dependent, while the decoder's recursion equations and the
digit-character lemmas are not.

`finEnumFin` and `finEnumEmpty` are named because mathlib's `FinEnum`
instances for `Fin n` and `Empty` are `Classical.choice`-dependent.

`Rose.Arity` is an `abbrev` because a proof matching a child function's
type against a lemma stated at `Fin n → _` needs it reducible;
`Ast.ofRose_snoc` and `Ast.toRose_ofRose` are the two here, and
`Rose.parseAux_print` and `Rsexp.parseAux_print` the third and fourth,
downstream. Its docstring names all
four and says what the reducibility costs.

`Ast.Arity` and `Tree.Arity` are plain `def`s, which keeps instance
search from reducing past them at a literal shape. No demand here
reaches that case; the `def`s guard against one arising later, which
would otherwise resolve through mathlib's `Classical.choice`-dependent
`FinEnum.fin`.

## References

* [RFC9804]
* [UustaluVene2011]

## Tags

abstract syntax, concrete syntax, W-type, retraction, S-expression
-/

universe uA uB uC

@[expose] public section

namespace Geb

/-! ## Choice-free finite enumerations

Every `Arity` family below is finitely enumerable, which is what lets
`WType.instDecidableEq` decide equality of the corresponding tree type.
The `#guard`s in the three `GebTests` syntax modules decide equality at
`Ast k`, at `Tree k Ann` and at `Rose k`. The two enumerations are named
because mathlib's `FinEnum.fin` and `FinEnum.empty` are built by
`FinEnum.ofList`, whose proof obligations depend on `Classical.choice`,
which [CONTRIBUTING.md § Constructive-only](../../CONTRIBUTING.md)
forbids. Naming them suffices for that consumer: `WType.instDecidableEq`
asks for a family at a general shape, where nothing reduces, so equality
is decided choice-free however the family is declared — `Rose.Arity` is
an `abbrev` and equality at `Rose k` is choice-free. What a reducible
family gives up is `FinEnum` demanded at a shape already a literal,
where search reduces past it to `Empty` or `Fin n` and selects mathlib's.
`Ast.Arity` and `Tree.Arity` are plain `def`s so that such a demand
would reach the named instance; nothing here makes one. Neither
construction is specific to syntax. -/

/-- `Fin n` enumerated by the identity equivalence. -/
@[instance_reducible] def finEnumFin (n : Nat) : FinEnum (Fin n) := ⟨n, Equiv.refl (Fin n)⟩

/-- `Empty` enumerated by the empty equivalence. -/
@[instance_reducible] def finEnumEmpty : FinEnum Empty :=
  ⟨0, ⟨Empty.elim, Fin.elim0, fun e ↦ e.elim, fun i ↦ i.elim0⟩⟩

/-! ## Abstract syntax -/

namespace Ast

/-- The node shapes of the Geb abstract syntax: a leaf carrying a label
in `Fin k`, or a fork. -/
inductive Shape (k : Nat) where
  /-- A leaf, labelled by an element of `Fin k`. -/
  | leaf : Fin k → Shape k
  /-- A fork, with two children. -/
  | fork : Shape k
  deriving DecidableEq

/-- The child index type of each shape: a leaf has none, a fork has two.
`Fin 2` rather than `Bool`, so that every non-empty arity here is
enumerated by `finEnumFin`. A `def` rather than an `abbrev`: reducible,
instance search at a concrete shape would whnf past this family to
`Empty` or `Fin 2` and select mathlib's `Classical.choice`-dependent
`FinEnum`, never reaching `instFinEnumArity`. -/
def Arity {k : Nat} : Shape k → Type
  | .leaf _ => Empty
  | .fork => Fin 2

/-- Every arity is finitely enumerable. -/
instance instFinEnumArity {k : Nat} (s : Shape k) : FinEnum (Arity s) :=
  match s with
  | .leaf _ => finEnumEmpty
  | .fork => finEnumFin 2

end Ast

/-- The Geb abstract syntax: the initial algebra of `F X = Fin k + X × X`,
presented as the W-type on `Ast.Shape k`. -/
abbrev Ast (k : Nat) : Type := WType (Ast.Arity (k := k))

namespace Ast

/-- A leaf labelled `i`. -/
def leaf {k : Nat} (i : Fin k) : Ast k :=
  WType.mk (.leaf i) Empty.elim

/-- A fork with left child `l` and right child `r`. -/
def fork {k : Nat} (l r : Ast k) : Ast k :=
  WType.mk .fork fun b : Fin 2 ↦ Fin.cases l (fun _ ↦ r) b

/-- The number of nodes. -/
def size {k : Nat} : Ast k → Nat :=
  WType.elim Nat fun x ↦
    match x with
    | ⟨.leaf _, _⟩ => 1
    | ⟨.fork, ch⟩ => 1 + ch (0 : Fin 2) + ch (1 : Fin 2)

/-- Induction on `Ast` in its two-constructor presentation, so that a
proof driven by it need not mention the underlying shape and arity. -/
theorem ind {k : Nat} {motive : Ast k → Prop}
    (leaf : ∀ i, motive (leaf i))
    (fork : ∀ l r, motive l → motive r → motive (fork l r)) :
    ∀ t, motive t :=
  WType.rec (motive := motive) fun s f ih ↦
    match s, f, ih with
    | .leaf i, f, _ => by
        have : f = Empty.elim := funext (fun e ↦ e.elim)
        subst this; exact leaf i
    | .fork, f, ih => by
        have : (fun b : Fin 2 ↦ Fin.cases (f (0 : Fin 2))
            (fun _ ↦ f (1 : Fin 2)) b) = f :=
          funext fun b ↦ match b with
            | ⟨0, _⟩ => rfl
            | ⟨1, _⟩ => rfl
        exact this ▸ fork (f (0 : Fin 2)) (f (1 : Fin 2))
          (ih (0 : Fin 2)) (ih (1 : Fin 2))

@[simp] theorem size_leaf {k : Nat} (i : Fin k) : (leaf i).size = 1 := rfl

@[simp] theorem size_fork {k : Nat} (l r : Ast k) :
    (fork l r).size = 1 + l.size + r.size := rfl

end Ast

/-! ## Annotated syntax -/

namespace Tree

/-- The node shapes of the annotated syntax: an `Ast.Shape` paired with
the decoration carried at that node. -/
abbrev Shape (k : Nat) (A : Type uA) : Type uA := A × Ast.Shape k

/-- The child index type of an annotated shape: that of the underlying
`Ast.Shape`, since decorating a node does not change its children. A
`def` rather than an `abbrev`, for the reason `Ast.Arity` gives. -/
def Arity {k : Nat} {A : Type uA} (s : Shape k A) : Type := Ast.Arity s.2

/-- Every annotated arity is finitely enumerable. -/
instance instFinEnumArity {k : Nat} {A : Type uA} (s : Shape k A) :
    FinEnum (Arity s) :=
  Ast.instFinEnumArity s.2

end Tree

/-- `Ast k` with every node decorated by an `A`: the initial algebra of
`X ↦ A × F X`. The initial algebra rather than the terminal coalgebra,
because syntax trees are finite; the cofree comonad on `F` admits
infinitely deep trees and is the home of execution traces, not syntax. -/
abbrev Tree (k : Nat) (A : Type uA) : Type uA :=
  WType (Tree.Arity (k := k) (A := A))

namespace Tree

/-- Relabel every node along `f`. -/
def map {k : Nat} {A : Type uA} {B : Type uB} (f : A → B) :
    Tree k A → Tree k B :=
  WType.elim (Tree k B) fun x ↦ WType.mk (f x.1.1, x.1.2) x.2

/-- The comonad counit: the decoration at the root. -/
def extract {k : Nat} {A : Type uA} (t : Tree k A) : A :=
  (WType.toSigma t).1.1

/-- The comonad comultiplication: relabel each node with the annotated
subtree rooted at it, in the sense [UustaluVene2011] gives the
comultiplication of the cofree recursive comonad. A paramorphism, since
the new decoration at a node is that node's own subtree. -/
def duplicate {k : Nat} {A : Type uA} : Tree k A → Tree k (Tree k A) :=
  WType.para (Tree k (Tree k A)) fun x ↦
    WType.mk (WType.mk x.1 fun b ↦ (x.2 b).1, x.1.2) fun b ↦ (x.2 b).2

/-- Forget every decoration, recovering the bare tree. This is the fold
induced by the second projection `A × F X → F X`, not the comonad
counit. -/
def erase {k : Nat} {A : Type uA} : Tree k A → Ast k :=
  WType.elim (Ast k) fun x ↦ WType.mk x.1.2 x.2

@[simp] theorem map_mk {k : Nat} {A : Type uA} {B : Type uB} (f : A → B)
    (s : Shape k A) (ch : Arity s → Tree k A) :
    map f (WType.mk s ch) = WType.mk (f s.1, s.2) fun b ↦ map f (ch b) :=
  rfl

@[simp] theorem extract_mk {k : Nat} {A : Type uA} (s : Shape k A)
    (ch : Arity s → Tree k A) : extract (WType.mk s ch) = s.1 :=
  rfl

@[simp] theorem duplicate_mk {k : Nat} {A : Type uA} (s : Shape k A)
    (ch : Arity s → Tree k A) :
    duplicate (WType.mk s ch)
      = WType.mk (WType.mk s ch, s.2) fun b ↦ duplicate (ch b) :=
  WType.para_mk _ s ch

/-- The first functor law: relabelling along the identity is the
identity. -/
theorem map_id {k : Nat} {A : Type uA} (t : Tree k A) : map id t = t :=
  WType.rec (motive := fun t ↦ map id t = t)
    (fun s ch ih ↦ by simp only [map_mk, id_eq]; exact congrArg _ (funext ih)) t

/-- The second functor law: relabelling twice is relabelling along the
composite. -/
theorem map_map {k : Nat} {A : Type uA} {B : Type uB} {C : Type uC}
    (f : A → B) (g : B → C) (t : Tree k A) :
    map g (map f t) = map (g ∘ f) t :=
  WType.rec (motive := fun t ↦ map g (map f t) = map (g ∘ f) t)
    (fun s ch ih ↦ by simp only [map_mk, Function.comp_apply]
                      exact congrArg _ (funext ih)) t

/-- Naturality of the counit: reading the root decoration commutes with
relabelling. -/
theorem extract_map {k : Nat} {A : Type uA} {B : Type uB} (f : A → B)
    (t : Tree k A) : extract (map f t) = f (extract t) := by
  cases t with
  | mk s ch => rfl

/-- Naturality of the comultiplication: redecorating commutes with
relabelling, the relabelling acting on each subtree. -/
theorem duplicate_map {k : Nat} {A : Type uA} {B : Type uB} (f : A → B)
    (t : Tree k A) :
    duplicate (map f t) = map (map f) (duplicate t) :=
  WType.rec (motive := fun t ↦ duplicate (map f t) = map (map f) (duplicate t))
    (fun s ch ih ↦ by simp only [map_mk, duplicate_mk]
                      exact congrArg _ (funext ih)) t

/-- The first comonad law: the subtree redecorating the root is the whole
tree. -/
theorem extract_duplicate {k : Nat} {A : Type uA} (t : Tree k A) :
    extract (duplicate t) = t := by
  cases t with
  | mk s ch => simp

/-- The second comonad law: taking each node's subtree and then keeping
only its root decoration recovers the original decoration. -/
theorem map_extract_duplicate {k : Nat} {A : Type uA} (t : Tree k A) :
    map extract (duplicate t) = t :=
  WType.rec (motive := fun t ↦ map extract (duplicate t) = t)
    (fun s ch ih ↦ by simp only [duplicate_mk, map_mk, extract_mk]
                      exact congrArg _ (funext ih)) t

/-- The third comonad law, coassociativity of the redecoration map. -/
theorem duplicate_duplicate {k : Nat} {A : Type uA} (t : Tree k A) :
    duplicate (duplicate t) = map duplicate (duplicate t) :=
  WType.rec (motive := fun t ↦ duplicate (duplicate t) = map duplicate (duplicate t))
    (fun s ch ih ↦ by simp only [duplicate_mk, map_mk]
                      rw [duplicate_mk]
                      exact congrArg _ (funext ih)) t

end Tree

/-- The annotation vocabulary carried at a node. Durable metadata is an
annotation value, never a lexical comment: generic parsers discard
comments, and canonical forms differ over whether they are retained. -/
@[ext] structure Ann where
  /-- A name for the annotated occurrence. -/
  name : Option String := none
  /-- Prose documentation of the annotated occurrence. -/
  doc : Option String := none
  /-- References to material bearing on the annotated occurrence. -/
  links : List String := []
  deriving Repr, DecidableEq, Inhabited

attribute [nolint unusedArguments] instReprAnn.repr

/-- An annotated Geb document. -/
abbrev Doc (k : Nat) : Type := Tree k Ann

namespace Ast

/-- Decorate every node with the empty annotation. -/
def trivialDoc {k : Nat} : Ast k → Doc k :=
  WType.elim (Doc k) fun x ↦ WType.mk (({} : Ann), x.1) x.2

/-- Decorating every node with the empty annotation and then erasing is
the identity. -/
theorem erase_trivialDoc {k : Nat} (a : Ast k) :
    Tree.erase a.trivialDoc = a :=
  WType.rec (motive := fun a ↦ Tree.erase (trivialDoc a) = a)
    (fun s ch ih ↦ by simp only [trivialDoc, WType.elim_mk]
                      exact congrArg _ (funext ih)) a

end Ast

/-! ## The rose presentation and its bijection -/

namespace Rose

/-- The node shapes of the rose presentation: a label in `Fin k` and a
number of children. -/
abbrev Shape (k : Nat) : Type := Fin k × Nat

/-- The child index type of a rose shape. Reducible, and this is the one
family that has to be: `simp` and `rw` match at reducible transparency,
so with a plain `def` a child function whose type reads
`Rose.Arity (i, n) → _` in a goal fails to unify with a lemma stated at
`Fin n → _`, and the proofs of `Ast.ofRose_snoc` and
`Ast.toRose_ofRose` fail here, `Geb.Rose.parseAux_print`'s and
`Geb.Rsexp.parseAux_print`'s downstream.
The cost is that `instFinEnumArity` below is unreachable at a concrete
shape: instance search reduces past this family to `Fin n` and selects
mathlib's `Classical.choice`-dependent `FinEnum.fin`. Deciding equality
at a `Rose k` does not incur that, `WType.instDecidableEq` asking for
the family at a general shape and so reaching the named instance; what
would pay it is a demand for `FinEnum` at a shape already a literal.
`Ast.Arity` and `Tree.Arity` are plain `def`s, at which search reaches
the named instance either way. -/
abbrev Arity {k : Nat} (s : Shape k) : Type := Fin s.2

/-- Every rose arity is finitely enumerable. Named for the same reason
as the other two: `WType.instDecidableEq` asks for this family at a
general shape, so deciding equality at a `Rose k` goes through this
instance rather than mathlib's `Classical.choice`-dependent
`FinEnum.fin`. All three `GebTests` syntax modules decide it. A `#guard`
is not a declaration, so `GebMeta.detectNonstandardAxiom` would not
catch a leak there. -/
instance instFinEnumArity {k : Nat} (s : Shape k) : FinEnum (Arity s) :=
  finEnumFin s.2

end Rose

/-- The rose-tree presentation: a label in `Fin k` and a finite sequence
of children, satisfying the same fixed-point equation as `Ast k`. -/
abbrev Rose (k : Nat) : Type := WType (Rose.Arity (k := k))

namespace Rose

/-- Append `t` to the children of `r`, keeping `r`'s label. -/
def snoc {k : Nat} (r t : Rose k) : Rose k :=
  match r with
  | ⟨(i, n), f⟩ => WType.mk (i, n + 1) (Fin.snoc f t)

/-- The node with label `i` and children `f`. -/
def node {k : Nat} (i : Fin k) {n : Nat} (f : Fin n → Rose k) : Rose k :=
  WType.mk (i, n) f

@[simp] theorem snoc_node {k : Nat} (i : Fin k) {n : Nat}
    (f : Fin n → Rose k) (t : Rose k) :
    snoc (node i f) t = node i (Fin.snoc f t) := rfl

/-- The node with label `i` whose children are the entries of `ts`. The
arity is read off the list, so this is the constructor available to a
parser, which learns a node's children one at a time and its arity only
when the list ends. -/
def ofList {k : Nat} (i : Fin k) (ts : List (Rose k)) : Rose k :=
  node i fun j : Fin ts.length ↦ ts.get j

/-- `ofList` against a tuple presentation of the same children. The list
is a parameter rather than `List.ofFn f`, which is what makes the arity
equation substitutable: `n = (List.ofFn f).length` cannot be substituted,
`n` occurring on the right through the type of `f`. -/
theorem ofList_eq {k n : Nat} (i : Fin k) (ts : List (Rose k))
    (f : Fin n → Rose k) (h : n = ts.length)
    (hf : ∀ j : Fin n, ts.get (j.cast h) = f j) :
    ofList i ts = node i f := by
  subst h
  exact congrArg (node i) (funext hf)

/-- Rebuilding a node from the list of its children recovers it. This is
the equation justifying the transport a variable-arity parser needs and
a fixed-arity one does not: the loop that reads the children returns a
`List`, while the node takes a `Fin n`-indexed tuple. -/
theorem ofList_ofFn {k n : Nat} (i : Fin k) (f : Fin n → Rose k) :
    ofList i (List.ofFn f) = node i f :=
  ofList_eq i _ f List.length_ofFn.symm fun j ↦ by simp

end Rose

namespace Rose

/-- Read children until the closing parenthesis, delegating each to
`childParse`. The `Nat` argument bounds the loop: it recurses on the
remainder `childParse` returns, which is not a form Lean's structural
recursion accepts. The loop consumes one unit per child and one on the
closing parenthesis, so a node of `n` children needs `n + 1`.
Shared by every spelling that closes a child list with `')'`. -/
def parseChildren {k : Nat}
    (childParse : List Char → Option (Rose k × List Char)) :
    Nat → List Char → Option (List (Rose k) × List Char) :=
  Nat.rec (motive := fun _ ↦ List Char → Option (List (Rose k) × List Char))
    (fun _ ↦ none)
    fun _ ih cs ↦
      match cs with
      | [] => none
      | c :: cs' =>
        if c = ')' then some ([], cs')
        else (childParse (c :: cs')).bind fun p ↦
          (ih p.2).map fun q ↦ (p.1 :: q.1, q.2)

@[simp] theorem parseChildren_succ_close {k : Nat}
    (childParse : List Char → Option (Rose k × List Char)) (f : Nat)
    (rest : List Char) :
    parseChildren childParse (f + 1) (')' :: rest) = some ([], rest) := rfl

theorem parseChildren_succ_cons {k : Nat}
    (childParse : List Char → Option (Rose k × List Char)) (f : Nat)
    (c : Char) (cs : List Char) (h : c ≠ ')') :
    parseChildren childParse (f + 1) (c :: cs)
      = (childParse (c :: cs)).bind fun p ↦
          (parseChildren childParse f p.2).map fun q ↦ (p.1 :: q.1, q.2) :=
  if_neg h

end Rose

namespace Ast

/-- The binary-to-rose direction. A rose node is read as a curried
function: its label is the function and its children are the arguments
it is applied to, in order. A fork `(l, r)` is read as the application
of `l` to `r`. Application of a curried function is left-associative, so
`l` carries the label together with every argument but the last, and `r`
is the last argument alone — that is, the child sequence is consumed as
a snoclist. Reading application to the right instead gives a different
and equally valid bijection, so the choice has to be fixed. -/
def toRose {k : Nat} : Ast k → Rose k :=
  WType.elim (Rose k) fun x ↦
    match x with
    | ⟨.leaf i, _⟩ => Rose.node i Fin.elim0
    | ⟨.fork, ch⟩ => Rose.snoc (ch (0 : Fin 2)) (ch (1 : Fin 2))

/-- The rose-to-binary direction, folding a node's children into the left
spine that carries the label at its head. -/
def ofRose {k : Nat} : Rose k → Ast k :=
  WType.elim (Ast k) fun x ↦
    Fin.foldl x.1.2 (fun acc j ↦ fork acc (x.2 j)) (leaf x.1.1)

@[simp] theorem toRose_leaf {k : Nat} (i : Fin k) :
    (leaf i).toRose = Rose.node i Fin.elim0 := rfl

@[simp] theorem toRose_fork {k : Nat} (l r : Ast k) :
    (fork l r).toRose = Rose.snoc l.toRose r.toRose := rfl

@[simp] theorem ofRose_node {k : Nat} (i : Fin k) {n : Nat} (f : Fin n → Rose k) :
    ofRose (Rose.node i f) =
      Fin.foldl n (fun acc j ↦ fork acc (ofRose (f j))) (leaf i) :=
  rfl

/-- Appending a child to a rose node appends a fork on the binary side,
which is the step `Ast.ofRose_toRose` turns on. -/
theorem ofRose_snoc {k : Nat} (r t : Rose k) :
    ofRose (Rose.snoc r t) = fork (ofRose r) (ofRose t) := by
  obtain ⟨⟨i, n⟩, f⟩ := r
  change ofRose (Rose.snoc (Rose.node i f) t)
      = fork (ofRose (Rose.node i f)) (ofRose t)
  simp only [Rose.snoc_node, ofRose_node, Fin.foldl_succ_last, Fin.snoc_castSucc,
    Fin.snoc_last]

/-- One half of the rose/binary bijection: converting to a rose tree and
back is the identity on `Ast k`. -/
theorem ofRose_toRose {k : Nat} (a : Ast k) : ofRose a.toRose = a :=
  ind (motive := fun a ↦ ofRose a.toRose = a)
    (fun i ↦ by simp only [toRose_leaf, ofRose_node, Fin.foldl_zero])
    (fun l r ihl ihr ↦ by beta_reduce; rw [toRose_fork, ofRose_snoc, ihl, ihr]) a

/-- The image of a left spine under `toRose`: the fold that `ofRose`
performs on a node's children is undone one child at a time, from the
last. -/
theorem toRose_foldl {k : Nat} (i : Fin k) :
    ∀ (n : Nat) (g : Fin n → Ast k),
      (Fin.foldl n (fun acc j ↦ fork acc (g j)) (leaf i)).toRose
        = Rose.node i fun j ↦ (g j).toRose :=
  Nat.rec
    (motive := fun n ↦ ∀ g : Fin n → Ast k,
      (Fin.foldl n (fun acc j ↦ fork acc (g j)) (leaf i)).toRose
        = Rose.node i fun j ↦ (g j).toRose)
    (fun g ↦ by
      simp only [Fin.foldl_zero, toRose_leaf]
      exact congrArg _ (funext fun j ↦ j.elim0))
    (fun n ih g ↦ by
      simp only [Fin.foldl_succ_last, toRose_fork,
        ih (fun j ↦ g j.castSucc), Rose.snoc_node]
      exact congrArg _ (Fin.snoc_init_self fun j ↦ (g j).toRose))

/-- The other half of the rose/binary bijection: converting from a rose
tree and back is the identity on `Rose k`. -/
theorem toRose_ofRose {k : Nat} (r : Rose k) : (ofRose r).toRose = r :=
  WType.rec (motive := fun r ↦ (ofRose r).toRose = r)
    (fun s f ih ↦ by
      obtain ⟨i, n⟩ := s
      change (ofRose (Rose.node i f)).toRose = Rose.node i f
      rw [ofRose_node, toRose_foldl]
      exact congrArg _ (funext ih)) r

end Ast

/-! ## Law skeletons for a concrete syntax -/

section Laws

variable {D : Type uA} {C : Type uB} (parse : C → Option D) (print : D → C)

/-- The document-level retraction law: the only law a syntax must prove. -/
def Retraction : Prop := ∀ d : D, parse (print d) = some d

/-- The formatter, defined where parsing succeeds. -/
def format (c : C) : Option C := (parse c).map print

/-- Formatter idempotence, the first corollary of a retraction:
reformatting formatted input changes nothing. -/
theorem format_idem (hr : Retraction parse print) (c : C) :
    (format parse print c).bind (format parse print)
      = format parse print c := by
  unfold format
  cases h : parse c with
  | none => simp
  | some d => simp [hr d]

/-- Injectivity of the printer, the second corollary of a retraction: a
syntax that can be parsed back cannot spell two documents alike. -/
theorem print_injective (hr : Retraction parse print) :
    Function.Injective print := by
  intro d1 d2 h
  have h1 := hr d1
  rw [h, hr d2] at h1
  exact (Option.some.inj h1).symm

end Laws

/-! ## A concrete syntax: RFC 9804 canonical S-expressions -/

namespace Csexp

/-! ### Decimal digits -/

/-- The ASCII character for a decimal digit; meaningful for `d < 10`. -/
def digitChar (d : Nat) : Char := Char.ofNat (48 + d)

/-- The decimal value of an ASCII digit character. -/
def charDigit (c : Char) : Option Nat :=
  if 48 ≤ c.toNat && c.toNat ≤ 57 then some (c.toNat - 48) else none

theorem charDigit_digitChar (d : Nat) (h : d < 10) :
    charDigit (digitChar d) = some d := by
  revert h; revert d; decide

theorem mapM_charDigit_digitChar : ∀ ds : List Nat, (∀ d ∈ ds, d < 10) →
    (ds.map digitChar).mapM charDigit = some ds :=
  List.rec (motive := fun ds ↦ (∀ d ∈ ds, d < 10) →
      (ds.map digitChar).mapM charDigit = some ds)
    (fun _ ↦ rfl)
    (fun d ds ih h ↦ by
      have hd : d < 10 := h d (by simp)
      have ht : ∀ x ∈ ds, x < 10 := fun x hx ↦ h x (by simp [hx])
      simp [List.mapM_cons, charDigit_digitChar d hd, ih ht])

/-- The value of a little-endian decimal digit list. -/
def ofLE : List Nat → Nat := List.rec 0 fun d _ ih ↦ d + 10 * ih

@[simp] theorem ofLE_nil : ofLE [] = 0 := rfl

@[simp] theorem ofLE_cons (d : Nat) (ds : List Nat) :
    ofLE (d :: ds) = d + 10 * ofLE ds := rfl

/-- Little-endian decimal digits of `n`, on an explicit recursion bound.
Each step divides by ten, so `n` itself is always a sufficient bound. -/
def digitsLEAux : Nat → Nat → List Nat :=
  Nat.rec (fun _ ↦ []) fun _ ih n ↦ if n = 0 then [] else n % 10 :: ih (n / 10)

@[simp] theorem digitsLEAux_zero (n : Nat) : digitsLEAux 0 n = [] := rfl

theorem digitsLEAux_succ (f n : Nat) :
    digitsLEAux (f + 1) n =
      if n = 0 then [] else n % 10 :: digitsLEAux f (n / 10) := rfl

/-- Little-endian decimal digits. Hand-rolled because every route to a
decimal round trip in mathlib and in core depends on `Classical.choice`;
see the module docstring's implementation notes. -/
def digitsLE (n : Nat) : List Nat := digitsLEAux n n

theorem ofLE_digitsLEAux : ∀ f n : Nat, n ≤ f → ofLE (digitsLEAux f n) = n :=
  Nat.rec (motive := fun f ↦ ∀ n : Nat, n ≤ f → ofLE (digitsLEAux f n) = n)
    (fun n hn ↦ by
      simp only [digitsLEAux_zero, ofLE_nil]
      exact (Nat.le_zero.mp hn).symm)
    (fun f ih n hn ↦ by
      rw [digitsLEAux_succ]
      split
      next h => simp [h]
      next h => rw [ofLE_cons, ih (n / 10) (by omega)]; omega)

theorem ofLE_digitsLE (n : Nat) : ofLE (digitsLE n) = n :=
  ofLE_digitsLEAux n n (Nat.le_refl n)

theorem digitsLEAux_lt : ∀ f n : Nat, ∀ d ∈ digitsLEAux f n, d < 10 :=
  Nat.rec (motive := fun f ↦ ∀ n : Nat, ∀ d ∈ digitsLEAux f n, d < 10)
    (fun n d hd ↦ by simp at hd)
    (fun f ih n d hd ↦ by
      rw [digitsLEAux_succ] at hd
      split at hd
      next => simp at hd
      next =>
        rcases List.mem_cons.mp hd with rfl | hd'
        · omega
        · exact ih (n / 10) d hd')

theorem digitsLE_lt (n : Nat) : ∀ d ∈ digitsLE n, d < 10 := digitsLEAux_lt n n

theorem digitsLE_ne_nil {n : Nat} (h : n ≠ 0) : digitsLE n ≠ [] := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  simp [digitsLE, digitsLEAux_succ]

/-- Shortest-form decimal, big-endian, `"0"` for zero. -/
def decOf (n : Nat) : List Char :=
  if n = 0 then ['0'] else (digitsLE n).reverse.map digitChar

/-- The value of a big-endian decimal digit string, or `none` if any
character is not a digit. Leading zeros are accepted, and so is the empty
string, whose value is `0`: the parser may admit more than the printer
emits, since the retraction law constrains only the composite. -/
def digitsVal (cs : List Char) : Option Nat :=
  (cs.mapM charDigit).map fun l ↦ ofLE l.reverse

/-- The decimal round trip: reading back a shortest-form spelling
recovers the number. This is what the retraction law rests on at the
label level. -/
theorem digitsVal_decOf (n : Nat) : digitsVal (decOf n) = some n := by
  unfold decOf digitsVal
  by_cases h : n = 0
  · subst h; decide
  · have hlt : ∀ d ∈ (digitsLE n).reverse, d < 10 := by
      intro d hd
      exact digitsLE_lt n d (List.mem_reverse.mp hd)
    rw [if_neg h, mapM_charDigit_digitChar _ hlt]
    simp [ofLE_digitsLE]

theorem decOf_all_digits (n : Nat) : ∀ c ∈ decOf n, (charDigit c).isSome := by
  intro c hc
  unfold decOf at hc
  by_cases h : n = 0
  · subst h; rw [if_pos rfl, List.mem_singleton] at hc; subst hc; decide
  · rw [if_neg h] at hc
    obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
    have : d < 10 := digitsLE_lt n d (List.mem_reverse.mp hd)
    simp [charDigit_digitChar d this]

theorem decOf_ne_nil (n : Nat) : decOf n ≠ [] := by
  unfold decOf
  by_cases h : n = 0
  · subst h; simp
  · rw [if_neg h]
    simp [digitsLE_ne_nil h]

/-! ### Reading a decimal prefix -/

/-- Split off the longest decimal prefix. -/
def readDigits : List Char → List Char × List Char :=
  List.rec ([], []) fun c cs ih ↦
    match charDigit c with
    | some _ => (c :: ih.1, ih.2)
    | none => ([], c :: cs)

theorem readDigits_cons (c : Char) (cs : List Char) :
    readDigits (c :: cs) =
      match charDigit c with
      | some _ => (c :: (readDigits cs).1, (readDigits cs).2)
      | none => ([], c :: cs) := rfl

theorem readDigits_append : ∀ ds rest : List Char,
    (∀ c ∈ ds, (charDigit c).isSome) →
    (∀ c cs, rest = c :: cs → charDigit c = none) →
    readDigits (ds ++ rest) = (ds, rest) :=
  List.rec (motive := fun ds ↦ ∀ rest : List Char,
      (∀ c ∈ ds, (charDigit c).isSome) →
      (∀ c cs, rest = c :: cs → charDigit c = none) →
      readDigits (ds ++ rest) = (ds, rest))
    (fun rest _ hr ↦ by
      cases rest with
      | nil => rfl
      | cons c cs => simp [readDigits_cons, hr c cs rfl])
    (fun d ds ih rest hd hr ↦ by
      have h1 : (charDigit d).isSome := hd d (by simp)
      have h2 : ∀ c ∈ ds, (charDigit c).isSome := fun c hc ↦ hd c (by simp [hc])
      obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h1
      simp [readDigits_cons, hv, ih rest h2 hr])

/-- Read a non-empty decimal prefix and its value. -/
def readNat (cs : List Char) : Option (Nat × List Char) :=
  let (ds, r) := readDigits cs
  if ds.isEmpty then none else (digitsVal ds).map (·, r)

/-! ### Canonical verbatim atoms -/

/-- The [RFC9804] verbatim encoding of an atom, `length ":" content`. -/
def printVerbatim (s : List Char) : List Char :=
  decOf s.length ++ ':' :: s

/-- Read one verbatim atom, returning it and the remaining input. The
`n ≤ r.length` guard rejects an atom declaring more content than
follows it, rather than truncating. `parse` cannot observe the guard —
a truncating read would consume the whole remaining input, and every
position that can follow one demands more — so what the guard buys is
that `readVerbatim` reads the [RFC9804] `verbatim` production correctly
on its own. `GebTests.Internal.ConcreteSyntax` asserts that directly. -/
def readVerbatim (cs : List Char) : Option (List Char × List Char) :=
  match readNat cs with
  | some (n, ':' :: r) => if n ≤ r.length then some (r.take n, r.drop n) else none
  | _ => none

/-- A printed atom reads back whole, and leaves exactly what followed
it. The length prefix is what delimits the content, so the content may
contain `:` and parentheses. -/
theorem readVerbatim_append (s rest : List Char) :
    readVerbatim (printVerbatim s ++ rest) = some (s, rest) := by
  have hcolon : ∀ c cs, (':' :: (s ++ rest)) = c :: cs → charDigit c = none := by
    intro c cs hc; injection hc with h1 _; subst h1; decide
  have h : readNat (printVerbatim s ++ rest)
      = some (s.length, ':' :: (s ++ rest)) := by
    unfold readNat printVerbatim
    rw [List.append_assoc, List.cons_append,
      readDigits_append _ _ (decOf_all_digits s.length) hcolon]
    simp [decOf_ne_nil s.length, digitsVal_decOf, List.isEmpty_iff]
  simp [readVerbatim, h]

/-! ### Printer -/

/-- The head atom of a leaf s-expression. -/
def leafTok : List Char := ['l', 'e', 'a', 'f']

/-- The head atom of a fork s-expression. -/
def forkTok : List Char := ['f', 'o', 'r', 'k']

/-- Print a tree in [RFC9804] canonical form. A leaf label is its
shortest-form decimal, written as a verbatim atom: canonical form admits
no other atom encoding. -/
def printAst {k : Nat} : Ast k → List Char :=
  WType.elim (List Char) fun x ↦
    match x with
    | ⟨.leaf i, _⟩ =>
      '(' :: (printVerbatim leafTok ++ printVerbatim (decOf i.val) ++ [')'])
    | ⟨.fork, ch⟩ =>
      '(' :: (printVerbatim forkTok ++ ch (0 : Fin 2) ++ ch (1 : Fin 2) ++ [')'])

@[simp] theorem printAst_leaf {k : Nat} (i : Fin k) :
    printAst (Ast.leaf i)
      = '(' :: (printVerbatim leafTok ++ printVerbatim (decOf i.val) ++ [')']) :=
  rfl

@[simp] theorem printAst_fork {k : Nat} (l r : Ast k) :
    printAst (Ast.fork l r)
      = '(' :: (printVerbatim forkTok ++ printAst l ++ printAst r ++ [')']) :=
  rfl

/-! ### Parser -/

/-- One layer of the recursive descent: read a single s-expression,
delegating each child to `childParse`. -/
def parseStep (k : Nat) (childParse : List Char → Option (Ast k × List Char)) :
    List Char → Option (Ast k × List Char)
  | [] => none
  | c :: cs =>
    if c = '(' then
      match readVerbatim cs with
      | some (tok, cs1) =>
        if tok = leafTok then
          match readVerbatim cs1 with
          | some (ds, ')' :: cs2) =>
            match digitsVal ds with
            | some n => if h : n < k then some (Ast.leaf ⟨n, h⟩, cs2) else none
            | none => none
          | _ => none
        else if tok = forkTok then
          match childParse cs1 with
          | some (l, cs2) =>
            match childParse cs2 with
            | some (r, ')' :: cs3) => some (Ast.fork l r, cs3)
            | _ => none
          | none => none
        else none
      | none => none
    else none

/-- Recursive descent over the canonical form, returning the tree and the
unconsumed input. The `Nat` argument bounds the recursion: the recursion
is on the input's structure only through the remainder each call returns,
which is not a form Lean's structural recursion accepts. `parse` supplies
the input length; `size_le_length_printAst` shows that this bound admits every
tree the printer emits. Whether it admits every input the grammar accepts
is not stated, and is not needed for the retraction law. -/
def parseAst (k : Nat) : Nat → List Char → Option (Ast k × List Char) :=
  Nat.rec (fun _ ↦ none) fun _ ih ↦ parseStep k ih

@[simp] theorem parseAst_succ (k f : Nat) :
    parseAst k (f + 1) = parseStep k (parseAst k f) := rfl

/-- The parser inverts the printer on printed input, given fuel at least
the tree's node count, and returns the unconsumed remainder. -/
theorem parseAst_printAst {k : Nat} (a : Ast k) :
    ∀ (f : Nat) (rest : List Char), a.size ≤ f →
      parseAst k f (printAst a ++ rest) = some (a, rest) :=
  Ast.ind (motive := fun a ↦ ∀ (f : Nat) (rest : List Char), a.size ≤ f →
      parseAst k f (printAst a ++ rest) = some (a, rest))
    (fun i f rest hf ↦ by
      cases f with
      | zero => simp at hf
      | succ f =>
        simp only [printAst_leaf, List.cons_append, parseAst_succ, parseStep,
          List.append_assoc, List.nil_append]
        rw [readVerbatim_append]
        -- reduce the match on the `some` just produced, exposing the next atom
        simp only []
        rw [readVerbatim_append]
        simp [digitsVal_decOf, i.isLt])
    (fun l r ihl ihr f rest hf ↦ by
      cases f with
      | zero => simp at hf
      | succ f =>
        have hl : l.size ≤ f := by simp at hf; omega
        have hr : r.size ≤ f := by simp at hf; omega
        simp only [printAst_fork, List.cons_append, parseAst_succ, parseStep,
          List.append_assoc, List.nil_append]
        rw [readVerbatim_append]
        have hne : forkTok ≠ leafTok := by decide
        simp only [if_neg hne]
        rw [ihl f _ hl]
        -- reduce the match on the `some` just produced, exposing the second child
        simp only []
        rw [ihr f _ hr]
        simp) a

/-- A tree's node count bounds the length of its printed form, so the
input length is fuel enough for `parseAst` to read anything `printAst`
emits. -/
theorem size_le_length_printAst {k : Nat} (a : Ast k) : a.size ≤ (printAst a).length :=
  Ast.ind (motive := fun a ↦ a.size ≤ (printAst a).length)
    (fun i ↦ by simp [printAst_leaf])
    (fun l r ihl ihr ↦ by
      simp only [Ast.size_fork, printAst_fork, List.length_cons,
        List.length_append]
      omega) a

/-! ### The two syntax maps and the retraction law -/

/-- The printer of the canonical S-expression syntax. A concrete syntax
needs a deterministic printer, not a normative canonical form; that this
one also emits the format's canonical spelling is incidental rather than
required. -/
def print {k : Nat} (a : Ast k) : List Char := printAst a

/-- The parser of the canonical S-expression syntax, rejecting trailing
input. -/
def parse (k : Nat) (cs : List Char) : Option (Ast k) :=
  match parseAst k cs.length cs with
  | some (a, []) => some a
  | _ => none

/-- The retraction law for the canonical S-expression syntax: printing a
tree and parsing the result returns that tree. -/
theorem parse_print {k : Nat} (a : Ast k) : parse k (print a) = some a := by
  unfold parse print
  rw [show printAst a = printAst a ++ [] by simp,
    parseAst_printAst a _ [] (by simpa using size_le_length_printAst a)]

/-! ### The generic corollaries, instantiated here -/

/-- `parse_print` in the form the generic corollaries consume. -/
theorem retraction (k : Nat) : Retraction (parse k) (print (k := k)) :=
  parse_print

/-- `Geb.format_idem` at this syntax. -/
theorem format_idem (k : Nat) (c : List Char) :
    (format (parse k) print c).bind (format (parse k) print)
      = format (parse k) print c :=
  Geb.format_idem _ _ (retraction k) c

/-- `Geb.print_injective` at this syntax. -/
theorem print_injective (k : Nat) : Function.Injective (print (k := k)) :=
  Geb.print_injective _ _ (retraction k)

end Csexp

end Geb
