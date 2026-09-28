/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Theory -- shake: keep

set_option doc.verso true in
/-!
# The terms of the internal language

The terms of the internal language of an elementary topos with data objects, the
Mitchell–Bénabou language of Section VI.5 of \[MacLaneMoerdijk1992\]: the typed λ-calculus
whose types are objects of the topos, with the element of the terminal object, pairs and their
components, abstraction and application, the application of a primitive arrow of the
combinators, the folds of the natural numbers, list and rose-tree objects, the application of a
definition, and the equality of two terms, a formula, a term of the subobject classifier's
type. A type is an object term of the combinators ({name}`Geb.FreeTopos.sig`), and a term
is a rose tree whose labels carry the types it names; a primitive arrow and a definition are named
by their indices, at objects. Variables are de Bruijn indices, the innermost binder's
variable the index zero; the start and the step of a fold are terms of contexts of their own, the
step's the recursion's value and, for a list, the element, so that a fold's only child in its
node's context is the datum it folds.

## Main definitions

* {lit}`Label` — the labels of a term's nodes.
* {lit}`Term` — the terms.
* {lit}`Term.rename`, {lit}`Term.subst` — renaming and substitution of variables.
* {lit}`Term.osubst` — substitution of objects for the object variables.

## References

* \[MacLaneMoerdijk1992\], Section VI.5, for the Mitchell–Bénabou language.

## Tags

internal language, Mitchell–Bénabou language, typed lambda calculus, de Bruijn index
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)
open scoped FinEnum

/-- The label of a node of a term. -/
inductive Label where
  /-- The variable of a de Bruijn index. -/
  | var (i : ℕ)
  /-- The element of the terminal object. -/
  | star
  /-- The pair of two terms. -/
  | pair
  /-- The first component of a term of a product. -/
  | fst
  /-- The second component of a term of a product. -/
  | snd
  /-- The abstraction of a term over a variable of a type. -/
  | lam (a : Tree)
  /-- The application of a term of an exponential to an argument. -/
  | app
  /-- The application of the primitive arrow of an index, at objects, to a term. -/
  | arr (k : ℕ) (θ : List Tree)
  /-- The fold of a natural number: a start, a step in the recursion's value, and the number. -/
  | natRec
  /-- The fold of a list: a start, a step in the recursion's value and the element, and the
  list. -/
  | listRec
  /-- The fold of a rose tree into a type: a step in the pair of a label and the list of the
  children's values, and the tree. -/
  | roseRec (c : Tree)
  /-- The application of the definition of an index, at objects, to terms, the last first. -/
  | defn (k : ℕ) (θ : List Tree)
  /-- The equality of two terms of one type, a formula. -/
  | eq
deriving DecidableEq

/-- A term of the internal language. -/
abbrev Term : Type := RoseTree Label

namespace Term

/-- The variable of a de Bruijn index. -/
def var (i : ℕ) : Term := RoseTree.node (.var i) []

/-- The element of the terminal object. -/
def star : Term := RoseTree.node .star []

/-- The pair of two terms. -/
def pair (t u : Term) : Term := RoseTree.node .pair [t, u]

/-- The first component of a term of a product. -/
def fst (t : Term) : Term := RoseTree.node .fst [t]

/-- The second component of a term of a product. -/
def snd (t : Term) : Term := RoseTree.node .snd [t]

/-- The abstraction of a term over a variable of the type {lit}`a`. -/
def lam (a : Tree) (t : Term) : Term := RoseTree.node (.lam a) [t]

/-- The application of a term of an exponential to an argument. -/
def app (t u : Term) : Term := RoseTree.node .app [t, u]

/-- The application of the primitive arrow of index {lit}`k`, at objects, to a term. -/
def arr (k : ℕ) (θ : List Tree) (t : Term) : Term := RoseTree.node (.arr k θ) [t]

/-- The fold of a natural number from a start by a step. -/
def natRec (z s n : Term) : Term := RoseTree.node .natRec [z, s, n]

/-- The fold of a list from a start by a step. -/
def listRec (z s l : Term) : Term := RoseTree.node .listRec [z, s, l]

/-- The fold of a rose tree into the type {lit}`c` by a step. -/
def roseRec (c : Tree) (s t : Term) : Term := RoseTree.node (.roseRec c) [s, t]

/-- The application of the definition of index {lit}`k`, at objects, to terms, the last first. -/
def defn (k : ℕ) (θ : List Tree) (ts : List Term) : Term := RoseTree.node (.defn k θ) ts

/-- The equality of two terms of one type, a formula. -/
def eq (t u : Term) : Term := RoseTree.node .eq [t, u]

/-- The lifting of a renaming under a binder. -/
def liftR (f : ℕ → ℕ) : ℕ → ℕ := fun i ↦ match i with
  | 0 => 0
  | j + 1 => f j + 1

/-- One step of the renaming of a term's variables, at a node of a label, from the renamings of
its children. -/
def renameStep (l : Label) (cs : List (Term × ((ℕ → ℕ) → Term))) (f : ℕ → ℕ) : Term :=
  match l, cs with
    | .var i, _ => var (f i)
    | .lam a, [(_, t)] => RoseTree.node (.lam a) [t (liftR f)]
    | .natRec, [(z, _), (s, _), (_, n)] => RoseTree.node .natRec [z, s, n f]
    | .listRec, [(z, _), (s, _), (_, n)] => RoseTree.node .listRec [z, s, n f]
    | .roseRec c, [(s, _), (_, n)] => RoseTree.node (.roseRec c) [s, n f]
    | l, cs => RoseTree.node l (cs.map fun c ↦ c.2 f)

/-- The renaming of a term's variables, lifted under each binder; the start and the step of a
fold, in contexts of their own, are left in place. -/
def rename : Term → (ℕ → ℕ) → Term := RoseTree.para renameStep

/-- The lifting of a substitution under a binder. -/
def liftS (σ : ℕ → Term) : ℕ → Term := fun i ↦ match i with
  | 0 => var 0
  | j + 1 => rename (σ j) Nat.succ

/-- One step of the substitution of terms for a term's variables, at a node of a label, from the
substitutions in its children. -/
def substStep (l : Label) (cs : List (Term × ((ℕ → Term) → Term))) (σ : ℕ → Term) : Term :=
  match l, cs with
    | .var i, _ => σ i
    | .lam a, [(_, t)] => RoseTree.node (.lam a) [t (liftS σ)]
    | .natRec, [(z, _), (s, _), (_, n)] => RoseTree.node .natRec [z, s, n σ]
    | .listRec, [(z, _), (s, _), (_, n)] => RoseTree.node .listRec [z, s, n σ]
    | .roseRec c, [(s, _), (_, n)] => RoseTree.node (.roseRec c) [s, n σ]
    | l, cs => RoseTree.node l (cs.map fun c ↦ c.2 σ)

/-- The substitution of terms for a term's variables, lifted under each binder; the start and
the step of a fold, in contexts of their own, are left in place. -/
def subst : Term → (ℕ → Term) → Term := RoseTree.para substStep

/-- The renaming of a node is its step at its children's renamings. -/
theorem rename_node (l : Label) (cs : List Term) (f : ℕ → ℕ) :
    rename (RoseTree.node l cs) f = renameStep l (cs.map fun c ↦ (c, rename c)) f :=
  congrFun (RoseTree.para_node _ l cs) f

/-- The substitution in a node is its step at the substitutions in its children. -/
theorem subst_node (l : Label) (cs : List Term) (σ : ℕ → Term) :
    subst (RoseTree.node l cs) σ = substStep l (cs.map fun c ↦ (c, subst c)) σ :=
  congrFun (RoseTree.para_node _ l cs) σ

/-- The substitution of a list of terms, the variable of index {lit}`i` replaced by the term at
position {lit}`i`. -/
def substList (ts : List Term) : ℕ → Term := fun i ↦ ts[i]?.getD (var i)

end Term

/-- The substitution of objects for the object variables of a label's types and arrows. -/
def Label.osubst (θ : List Tree) : Label → Label
  | .lam a => .lam (PartialHorn.subst θ a)
  | .arr k θ' => .arr k (θ'.map (PartialHorn.subst θ))
  | .roseRec c => .roseRec (PartialHorn.subst θ c)
  | .defn k θ' => .defn k (θ'.map (PartialHorn.subst θ))
  | l => l

/-- The substitution of objects for the object variables of a term's types and arrows. -/
def Term.osubst (θ : List Tree) : Term → Term :=
  RoseTree.elim fun l cs ↦ RoseTree.node (l.osubst θ) cs

/-- The object substitution in a node substitutes in its label and its children. -/
theorem Term.osubst_node (θ : List Tree) (l : Label) (cs : List Term) :
    Term.osubst θ (RoseTree.node l cs) = RoseTree.node (l.osubst θ) (cs.map (Term.osubst θ)) :=
  RoseTree.elim_node _ l cs

end Geb.FreeTopos.Internal

end
