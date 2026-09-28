/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Coproducts
public import Geb.Prototypes.FreeTopos.Internal.Compile

set_option doc.verso true in
/-!
# The derivations of the internal language

The checker of the internal language's derivations. A judgment is a formula, a term of the subobject
classifier's type, in a context of variables and under hypotheses, formulas in the same context. A
derivation is a rose tree of rules of two kinds. A rewriting derivation transforms a given term: the
identity, a sequence of two rewritings, congruence into each child of a node, each in its own
context and under its own hypotheses, and the equations of the language applied at the term: β for
functions, the components of a pair and the η of pairs and of the terminal type, the unfolding of a
definition at its arguments, the computation of the folds of the natural numbers, lists and rose
trees and of the case analysis of a coproduct, an instance of an earlier equational theorem, and an
equation among the hypotheses. A proof derivation proves a formula: an equation by rewriting both
sides to one term, or by induction in the form of the uniqueness of recursion; a hypothesis; a
formula by proving it after rewriting it or a formula that rewrites to it, or by a cut through a
formula proved first; the equality of two formulas that entail each other, and of two functions
whose applications to a new variable are equal; an instance of an earlier theorem, its hypotheses'
instances proved; a formula by induction on the innermost variable of the natural numbers or of a
list type, with the formula's instance at the start and, under the induction hypothesis, at a
successor or a construction; a formula of a rose tree alone by induction on it, with its instance at
a construction under the hypothesis that it holds at each child; a formula by case analysis on the
innermost variable of a coproduct type, with its instances at the two injections; every formula in a
context with a variable of the initial type; a formula by induction on the innermost variable of the
codomain of a coequalizer's projection, with its instance at the projection's image of a variable of
the domain; an equation by a certificate of the combinators that proves the sequent it compiles to;
and a formula under hypotheses by a certificate that proves the sequent its theorem compiles to
({lit}`Thm.seq`), the rule by which the language is complete. These rules are the basic axioms and
rules of a local set theory (\[RuizHernandezSolorzano2021\], Section 3.2), a formula's
comprehension the abstraction of the formula and membership application, with the extensionality of
every exponential in place of that of power types, and with induction. The rewriting takes its terms
from the term it rewrites, so that a derivation names no term but the steps of its inductions, the
formulas of its cuts and the instances of the theorems it cites, and the checker computes every
substitution.

A development mixes the two checkers: a declaration is a theorem of the language with its
derivation, a sequent of the combinators with its certificate, a definition of the language, a
primitive arrow, an object definition, the quotient of a type by a relation, or the descent of a
function to a quotient, each checked with the constants and the entries before it, so that the
constants, and with the object definitions the types, grow with the development. A theorem of the
language states to a certificate the sequent it compiles to ({lit}`Thm.seq`): the equation of its
conclusion's sides' arrows, or of its conclusion's arrow with truth, after the inclusion of the
subobject on which its hypotheses are true where it has hypotheses. A certificate is checked in the
theory extended by the compilations of the language's definitions so far, with every entry's sequent
as its theorems. A definition is checked by its compilation; a primitive arrow, a term of the
combinators in object parameters, by the checker's inference of its domain and codomain, or by a
certificate of the sequent that it is an arrow between them ({lit}`Prim.seq`), which may cite the
theorems before it; an object definition, an object of the combinators in object parameters, by the
inference of its definedness, or by a certificate of it ({lit}`objConfirms`). The quotient of a type
by a relation, a formula in two variables of the type, is the coequalizer of the projections of the
relation's pullback of truth ({lit}`relPair`), an object definition, with the projection to it, a
primitive arrow, and the theorem that related elements have equal images; the descent of a function,
cited with the theorem that it respects the relation, is a primitive arrow from the quotient, with
the theorem of its computation at an image.

## Main definitions

* {lit}`Rule`, {lit}`Deriv` — the rules and the derivations.
* {lit}`Thm` — a theorem: a formula in a context under hypotheses.
* {lit}`Thm.seq` — the sequent of the combinators a theorem compiles to.
* {lit}`Entry`, {lit}`Decl` — the entries of a development's environment, and its declarations
  with their proofs.
* {lit}`check` — the rewriting a derivation performs, and the judgments it proves.
* {lit}`Prim.seq`, {lit}`Prim.confirms` — the sequent that a primitive arrow is an arrow between
  its types, and the confirmation of a primitive arrow a development declares.
* {lit}`relPair`, {lit}`Prim.coeqParts`, {lit}`Prim.rel?` — the pair a quotient coequalizes, and
  the recognition of a quotient's projection.
* {lit}`Decl.step`, {lit}`checkDev`, {lit}`checkThms` — the check of a development, each
  declaration proved with the constants and the entries before it.

## References

* \[RuizHernandezSolorzano2021\]

## Tags

internal language, derivation, proof checker, rewriting, induction, local set theory
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree op Seq)
open Sorts
open scoped FinEnum

/-- A rule of the internal language's derivations, with the data it names. -/
inductive Rule where
  /-- The identity rewriting. -/
  | refl
  /-- One rewriting after another. -/
  | trans
  /-- The rewriting of each child of a node. -/
  | cong
  /-- The application of an abstraction is its body with the argument substituted. -/
  | beta
  /-- The first component of a pair is its first term. -/
  | fstPair
  /-- The second component of a pair is its second term. -/
  | sndPair
  /-- The pair of a term's components is the term. -/
  | pairEta
  /-- A term of the terminal type is its element. -/
  | unitEta
  /-- The application of a definition is its body at the objects and arguments. -/
  | delta
  /-- The fold of zero, the primitive of index {lit}`k`, is the start. -/
  | natZero (k : ℕ)
  /-- The fold of a successor, the primitive of index {lit}`k`, is the step at the fold. -/
  | natSucc (k : ℕ)
  /-- The fold of the empty list, the primitive of index {lit}`k`, is the start. -/
  | listNil (k : ℕ)
  /-- The fold of a construction, the primitive of index {lit}`k`, is the step at the element
  and the fold of the tail. -/
  | listCons (k : ℕ)
  /-- The fold of a rose tree's construction, the primitive of index {lit}`kn`, is the step at
  the pair of the label and the list of the folds of the children, the list built by the
  primitives of indices {lit}`kl` and {lit}`kc`. -/
  | roseNode (kn kl kc : ℕ)
  /-- The case analysis of a pair of functions, the primitive of index {lit}`kc`, at a left
  injection, the primitive of index {lit}`kl`, is the first function at the injected term. -/
  | caseInl (kc kl : ℕ)
  /-- The case analysis of a pair of functions, the primitive of index {lit}`kc`, at a right
  injection, the primitive of index {lit}`kr`, is the second function at the injected term. -/
  | caseInr (kc kr : ℕ)
  /-- The equational theorem of index {lit}`j` at objects and terms, from its left side to its
  right, or from its right to its left when {lit}`flip`. -/
  | thm (j : ℕ) (θ : List Tree) (σ : List Term) (flip : Bool)
  /-- The equation among the hypotheses of index {lit}`i`, from its left side to its right, or
  from its right to its left when {lit}`flip`. -/
  | rwHyp (i : ℕ) (flip : Bool)
  /-- An equation whose sides two rewritings take to one term. -/
  | join
  /-- An equation by induction on the innermost variable, of the natural numbers, with zero and
  the successor the primitives of indices {lit}`kz` and {lit}`ks`, by the step {lit}`s`. -/
  | natInd (kz ks : ℕ) (s : Term)
  /-- An equation by induction on the innermost variable, of a list type, with the empty list and
  construction the primitives of indices {lit}`kn` and {lit}`kc`, by the step {lit}`s`. -/
  | listInd (kn kc : ℕ) (s : Term)
  /-- The hypothesis of index {lit}`i`. -/
  | hyp (i : ℕ)
  /-- A cut through the formula {lit}`φ`, proved first and then a hypothesis. -/
  | cut (φ : Term)
  /-- A formula proved after a rewriting. -/
  | conv
  /-- A formula, the formula {lit}`φ` proved and rewritten to it. -/
  | convFrom (φ : Term)
  /-- The equality of two formulas, each proved under the other. -/
  | propExt
  /-- The equality of two functions, whose applications to a new variable are proved equal. -/
  | funExt
  /-- The theorem of index {lit}`j` at objects and terms, its hypotheses' instances proved. -/
  | apply (j : ℕ) (θ : List Tree) (σ : List Term)
  /-- A formula by induction on the innermost variable, of the natural numbers, with zero and the
  successor the primitives of indices {lit}`kz` and {lit}`ks`, under the induction hypothesis
  at the successor. -/
  | natIndHyp (kz ks : ℕ)
  /-- A formula by induction on the innermost variable, of a list type, with the empty list and
  construction the primitives of indices {lit}`kn` and {lit}`kc`, under the induction hypothesis
  at the construction. -/
  | listIndHyp (kn kc : ℕ)
  /-- An equation by the certificate {lit}`c` of the combinators, which proves the sequent the
  equation compiles to with the development's sequents as its theorems. -/
  | cert (c : Tree)
  /-- A formula under hypotheses by the certificate {lit}`c` of the combinators, which proves the
  sequent the theorem of the formula in its context under its hypotheses compiles to, with the
  development's sequents as its theorems. -/
  | certSeq (c : Tree)
  /-- An equation between two terms in a context of a rose tree alone, under no hypotheses, by
  induction in the form of the uniqueness of the fold: each side at a construction, the primitive
  of index {lit}`kn`, is the step {lit}`s` at the label and the list of the side's values at the
  children, the list built by the primitives of indices {lit}`kl` and {lit}`kc`. -/
  | roseInd (kn kl kc : ℕ) (s : Term)
  /-- A formula in a context of a rose tree alone by induction on it: proved at a construction,
  the primitive of index {lit}`kn`, under the hypothesis that it holds at each child, its list of
  values at the children, built by the primitives of indices {lit}`kl` and {lit}`kc`, being that
  of truth. -/
  | roseIndHyp (kn kl kc : ℕ)
  /-- A formula by case analysis on the innermost variable, of a coproduct type, with the
  injections the primitives of indices {lit}`kl` and {lit}`kr`: proved at the left injection of a
  variable of the first summand and at the right injection of a variable of the second, under
  hypotheses that do not mention the variable. -/
  | coprodInd (kl kr : ℕ)
  /-- A formula in a context whose variable of index {lit}`i` is of the initial type. -/
  | zeroInd (i : ℕ)
  /-- A formula by induction on the innermost variable, of the codomain of the primitive arrow of
  index {lit}`kq` at the objects {lit}`θ`, a coequalizer's projection: proved at its image of a
  variable of its domain, under hypotheses that do not mention the variable. -/
  | quotInd (kq : ℕ) (θ : List Tree)

/-- A derivation of the internal language. -/
abbrev Deriv : Type := RoseTree Rule

/-- A theorem: a formula in a context under hypotheses, in object variables. -/
structure Thm where
  /-- The number of object variables. -/
  arity : ℕ
  /-- The types of the variables, the innermost first. -/
  ctx : List Tree
  /-- The hypotheses. -/
  hyps : List Term
  /-- The conclusion. -/
  concl : Term

/-- The primitive arrow zero. -/
def zeroPrim : Prim := ⟨0, zeroN, one, nat⟩

/-- The primitive arrow successor. -/
def succPrim : Prim := ⟨0, succ, nat, nat⟩

/-- The primitive arrow of the empty list of the object parameter. -/
def nilPrim : Prim := ⟨1, nil (x 0), one, list (x 0)⟩

/-- The primitive arrow of the construction of a list of the object parameter. -/
def consPrim : Prim := ⟨1, cons (x 0), prod (x 0) (list (x 0)), list (x 0)⟩

/-- The primitive arrow of the construction of a rose tree, from a natural number label and the
list of its children. -/
def nodePrim : Prim := ⟨0, node, prod nat (list rose), rose⟩

/-- The primitive arrow of the construction of a rose tree over the object parameter of labels,
from a label and the list of its children. -/
def lnodePrim : Prim := ⟨1, lnode (x 0), prod (x 0) (list (lrose (x 0))), lrose (x 0)⟩

/-- The primitive arrow of the left injection into the coproduct of the object parameters. -/
def inlPrim : Prim := ⟨2, inl (x 0) (x 1), x 0, coprod (x 0) (x 1)⟩

/-- The primitive arrow of the right injection into the coproduct of the object parameters. -/
def inrPrim : Prim := ⟨2, inr (x 0) (x 1), x 1, coprod (x 0) (x 1)⟩

/-- The primitive arrow of the case analysis of the coproduct of the first two object parameters
into the third, from the pair of the functions from the two summands. -/
def casePrim : Prim := ⟨3, caseArr (x 0) (x 1) (x 2), prod (exp (x 0) (x 2)) (exp (x 1) (x 2)),
  exp (coprod (x 0) (x 1)) (x 2)⟩

/-- The object variables of a number of object parameters. -/
def objVars (n : ℕ) : List Tree := (List.range n).map x

/-- The two composites a primitive arrow is the projection of the coequalizer of, where it is
one. -/
def Prim.coeqParts (p : Prim) : Option (Tree × Tree) := match p.arrow.children with
  | [f, g] => match f.children, g.children with
    | [a, b], [c, d] =>
      if p.arrow = coeqProj f g ∧ f = comp a b ∧ g = comp c d then some (f, g) else none
    | _, _ => none
  | _ => none

/-- The projections of the pullback of truth along an arrow from the product of a type with
itself into the subobject classifier, whose coequalizer is the quotient by the relation the arrow
is. -/
def relPair (A r : Tree) : Tree × Tree :=
  (comp (fst A A) (truthIncl r), comp (snd A A) (truthIncl r))

/-- The arrow of the relation a primitive arrow is the projection of the quotient by, where it is
one. -/
def Prim.rel? (p : Prim) : Option Tree := match p.arrow.children with
  | [f, _] => match f.children with
    | [_, m] => match m.children with
      | [r, _] =>
        if p.arrow = coeqProj (relPair p.dom r).1 (relPair p.dom r).2 then some r else none
      | _ => none
    | _ => none
  | _ => none

/-- The substitution of one term for the innermost variable, the others lowered by one. -/
def instVar (u : Term) : ℕ → Term := fun i ↦ match i with
  | 0 => u
  | j + 1 => Term.var j

/-- The substitution of one term for the innermost variable, the others in place. -/
def atVar0 (u : Term) : ℕ → Term := fun i ↦ match i with
  | 0 => u
  | j + 1 => Term.var (j + 1)

/-- A term in a context of a natural number variable, at the variable's successor, the primitive
of index {lit}`ks`. -/
def natSuccAt (ks : ℕ) (t : Term) : Term := Term.subst t (atVar0 (Term.arr ks [] (Term.var 0)))

/-- A term in a context of a list variable, at the construction, the primitive of index
{lit}`kc` at the element type {lit}`a`, of a new element before the variable, the new element
the next variable and the context's others raised past it. -/
def listConsAt (kc : ℕ) (a : Tree) (t : Term) : Term :=
  Term.subst t fun i ↦ match i with
    | 0 => Term.arr kc [a] (Term.pair (Term.var 1) (Term.var 0))
    | j + 1 => Term.var (j + 2)

/-- A term in a context of a rose tree of the type {lit}`r` over the type of labels {lit}`a`, at
the construction, the primitive of index {lit}`kn`, of a tree from the next variable's label and
the innermost variable's children. -/
def roseNodeAt (kn : ℕ) (r a : Tree) (t : Term) : Term :=
  Term.subst t (instVar (Term.arr kn (if r = rose then [] else [a])
    (Term.pair (Term.var 1) (Term.var 0))))

/-- A term in a context of a list variable, weakened past a new element after the variable. -/
def weakenElem (t : Term) : Term := Term.rename t fun i ↦ match i with
  | 0 => 0
  | j + 1 => j + 2

/-- A term weakened past a new innermost variable. -/
def weaken1 (t : Term) : Term := Term.rename t (· + 1)

/-- A term weakened past two new innermost variables. -/
def weaken2 (t : Term) : Term := Term.rename t (· + 2)

/-- The list of the values at the children, the innermost variable, of a term in a context of a
rose tree, the list of the type {lit}`c` built by a fold of the children by the primitives of
indices {lit}`kl` and {lit}`kc`. -/
def roseMapAt (kl kc : ℕ) (c : Tree) (t : Term) : Term :=
  Term.listRec (Term.arr kl [c] Term.star) (Term.arr kc [c] (Term.pair (weaken1 t) (Term.var 0)))
    (Term.var 0)

/-- The hypothesis of induction on rose trees: a formula in a context of a rose tree holds at each
child, the innermost variable, its list of values at the children being that of truth, the
equality of the terminal object's element with itself. -/
def roseHyp (kl kc : ℕ) (φ : Term) : Term :=
  Term.eq (roseMapAt kl kc omega φ) (roseMapAt kl kc omega (Term.eq Term.star Term.star))

/-- The sides of an equation. -/
def eqParts (φ : Term) : Option (Term × Term) := match φ.label, φ.children with
  | .eq, [t, u] => some (t, u)
  | _, _ => none

/-- The instance of a term of a theorem at objects and terms. -/
def instTerm (θ : List Tree) (σ : List Term) (s : Term) : Term :=
  Term.subst (Term.osubst θ s) (Term.substList σ)

/-- The type of a term in a context. -/
def typeIn (G : Globals) (n : ℕ) (Γ : List Tree) (t : Term) : Option Tree :=
  (compile G n t (ctxObj Γ) (stdEnv Γ)).map Prod.snd

/-- Hypotheses in a context of an innermost variable that none of them mentions, in the context
{lit}`Γ` without it, where they are formulas. -/
def lowerHyps (G : Globals) (n : ℕ) (Γ : List Tree) (Φ : List Term) : Option (List Term) :=
  Φ.mapM fun ψ ↦
    if weaken1 (Term.rename ψ (· - 1)) = ψ ∧ typeIn G n Γ (Term.rename ψ (· - 1)) = some omega
    then some (Term.rename ψ (· - 1)) else none

/-- Whether objects and terms instantiate a theorem in a context: types for its object
variables, and terms of its context's types at them. -/
def instOk (G : Globals) (n : ℕ) (Γ : List Tree) (a : Thm) (θ : List Tree) (σ : List Term) :
    Bool :=
  decide (θ.length = a.arity) && θ.all (IsTy G n) && decide (σ.length = a.ctx.length) &&
    (σ.zip (a.ctx.map (PartialHorn.subst θ))).all (fun (u, A) ↦ typeIn G n Γ u = some A)

/-- One step of the subobject on which arrows into the subobject classifier are truth: from a
subobject with its inclusion, the pullback of truth along an arrow after the inclusion, with the
inclusion after the pullback's. -/
def truthStep (p : Tree × Tree) (H : Tree) : Tree × Tree :=
  (truthEq (comp H p.2), comp p.2 (truthIncl (comp H p.2)))

/-- The subobject of {lit}`X` on which arrows from it into the subobject classifier are truth,
with its inclusion: each arrow's pullback of truth taken in turn. -/
def truthSub (X : Tree) (Hs : List Tree) : Tree × Tree := Hs.foldl truthStep (X, idt X)

/-- The arrow a formula compiles to in a theorem's context, from the product of its types. -/
def Thm.arrow (G : Globals) (a : Thm) (φ : Term) : Tree :=
  ((compile G a.arity φ (ctxObj a.ctx) (stdEnv a.ctx)).map Prod.fst).getD (idt (ctxObj a.ctx))

/-- An arrow from the product of a theorem's context's types, after the inclusion of the
subobject on which its hypotheses' arrows are truth where it has hypotheses. -/
def Thm.side (G : Globals) (a : Thm) (f : Tree) : Tree :=
  if a.hyps = [] then f else comp f (truthSub (ctxObj a.ctx) (a.hyps.map (a.arrow G))).2

/-- The sequent of the combinators a theorem compiles to, in its object variables: the equation
of the arrows of its conclusion's sides, or of its conclusion's arrow with truth where the
conclusion is not an equation, each after the inclusion of the subobject on which its
hypotheses' arrows are truth where it has hypotheses. -/
def Thm.seq (G : Globals) (a : Thm) : Seq :=
  ⟨List.replicate a.arity obj, [], match eqParts a.concl with
    | some (t, u) => ⟨a.side G (a.arrow G t), a.side G (a.arrow G u)⟩
    | none => ⟨a.side G (a.arrow G a.concl), a.side G (comp tru (bang (ctxObj a.ctx)))⟩⟩

/-- A theorem of a development's environment: a theorem of the language, or a sequent of the
combinators. -/
inductive Entry where
  /-- A theorem of the language. -/
  | language (a : Thm)
  /-- A sequent of the combinators. -/
  | combinators (s : Seq)

/-- The theorem of the language an entry is, where it is one. -/
def Entry.language? : Entry → Option Thm
  | .language a => some a
  | .combinators _ => none

/-- The sequent of the combinators an entry states. -/
def Entry.seq (G : Globals) : Entry → Seq
  | .language a => a.seq G
  | .combinators s => s

/-- Whether a certificate of the combinators proves a sequent, in the theory extended by the
compilations of the definitions of {lit}`G`, with the sequents of the entries of {lit}`E` as its
theorems, the definitions' operations following the signature's. -/
def certifies (G : Globals) (E : Array Entry) (c : Tree) (s : Seq) : Bool :=
  (compileDefs G).any fun cds ↦ decide (G.base = sig.length) &&
    decide (PartialHorn.check (ext cds) (E.map (Entry.seq G)) c s.ctx s.hyps = some s.concl)

/-- The contexts and hypotheses of a node's children, in the node's context and under its
hypotheses: an abstraction's body extends the context, the hypotheses weakened, and the start
and the step of a fold are in contexts of their own, under no hypotheses. -/
def childCtxs (G : Globals) (n : ℕ) (l : Label) (ts : List Term) (Γ : List Tree)
    (Φ : List Term) : Option (List (List Tree × List Term)) := match l, ts with
  | .lam a, [_] => some [(a :: Γ, Φ.map weaken1)]
  | .natRec, [z, _, _] => do
    let c ← typeIn G n [] z
    pure [([], []), ([c], []), (Γ, Φ)]
  | .listRec, [z, _, m] => do
    let c ← typeIn G n [] z
    let a ← (typeIn G n Γ m).bind listPart
    pure [([], []), ([c, a], []), (Γ, Φ)]
  | .roseRec c, [_, m] => do
    let p ← (typeIn G n Γ m).bind roseParts
    pure [([prod p.1 (list c)], []), (Γ, Φ)]
  | _, ts => some (ts.map fun _ ↦ (Γ, Φ))

/-- Whether a node's child of an index is in the node's context: every child but an
abstraction's body and a fold's start and step. -/
def sameCtx (l : Label) (i : ℕ) : Bool := match l with
  | .lam _ => false
  | .natRec | .listRec => i = 2
  | .roseRec _ => i = 1
  | _ => true

/-- Whether a rule is the identity rewriting. -/
def Rule.isRefl : Rule → Bool
  | .refl => true
  | _ => false

/-- The contexts in which a congruence rewrites a node's children by the derivations
{lit}`ds`: the node's context for each child where every child not in it has the identity
derivation, which rewrites a term to itself in any context, and else {lit}`childCtxs`, which
computes the types a fold's start and datum have. -/
def congCtxs (G : Globals) (n : ℕ) (l : Label) (ts : List Term) (Γ : List Tree) (Φ : List Term)
    (ds : List Deriv) : Option (List (List Tree × List Term)) :=
  if ds.zipIdx.all fun (d, i) ↦ sameCtx l i || d.label.isRefl then
    some (ts.map fun _ ↦ (Γ, Φ))
  else childCtxs G n l ts Γ Φ

/-- The rewriting of a term at its root by a rule of the language's equations, with the
constants of {lit}`G`, the theorems of the language among the entries of {lit}`E` and the
hypotheses {lit}`Φ`. -/
def rootStep (G : Globals) (E : Array Entry) (n : ℕ) (Γ : List Tree) (Φ : List Term) (l : Rule)
    (t : Term) : Option Term := match l, t.label, t.children with
  | .beta, .app, [f, u] => match f.label, f.children with
    | .lam _, [b] => some (Term.subst b (instVar u))
    | _, _ => none
  | .fstPair, .fst, [p] => match p.label, p.children with
    | .pair, [a, _] => some a
    | _, _ => none
  | .sndPair, .snd, [p] => match p.label, p.children with
    | .pair, [_, b] => some b
    | _, _ => none
  | .pairEta, .pair, [a, b] => match a.label, a.children, b.label, b.children with
    | .fst, [p], .snd, [q] => if p = q then some p else none
    | _, _, _, _ => none
  | .unitEta, _, _ => if typeIn G n Γ t = some one then some Term.star else none
  | .delta, .defn k θ, args => ((G.defs[k]?).bind Definition.language?).map fun d ↦
    Term.subst (Term.osubst θ d.body) (Term.substList args)
  | .natZero kz, .natRec, [z, _, m] => match m.label, m.children with
    | .arr k [], [c] => if k = kz ∧ G.prims[kz]? = some zeroPrim ∧ c = Term.star then some z
      else none
    | _, _ => none
  | .natSucc ks, .natRec, [z, s, m] => match m.label, m.children with
    | .arr k [], [c] => if k = ks ∧ G.prims[ks]? = some succPrim then
        some (Term.subst s (instVar (Term.natRec z s c))) else none
    | _, _ => none
  | .listNil kn, .listRec, [z, _, m] => match m.label, m.children with
    | .arr k [_], [c] => if k = kn ∧ G.prims[kn]? = some nilPrim ∧ c = Term.star then some z
      else none
    | _, _ => none
  | .listCons kc, .listRec, [z, s, m] => match m.label, m.children with
    | .arr k [_], [p] => match p.label, p.children with
      | .pair, [h, tl] => if k = kc ∧ G.prims[kc]? = some consPrim then
          some (Term.subst s (Term.substList [Term.listRec z s tl, h])) else none
      | _, _ => none
    | _, _ => none
  | .roseNode kn kl kc, .roseRec c, [s, m] => match m.label, m.children with
    | .arr k _, [p] => match p.label, p.children with
      | .pair, [l, cs] => if k = kn ∧
          (G.prims[kn]? = some nodePrim ∨ G.prims[kn]? = some lnodePrim) ∧
          G.prims[kl]? = some nilPrim ∧ G.prims[kc]? = some consPrim then
          some (Term.subst s (instVar (Term.pair l (Term.listRec (Term.arr kl [c] Term.star)
            (Term.arr kc [c] (Term.pair (Term.roseRec c s (Term.var 1)) (Term.var 0))) cs))))
        else none
      | _, _ => none
    | _, _ => none
  | .caseInl kc kl, .app, [f, u] => match f.label, f.children, u.label, u.children with
    | .arr k _, [p], .arr k' _, [v] => match p.label, p.children with
      | .pair, [g, _] => if k = kc ∧ k' = kl ∧ G.prims[kc]? = some casePrim ∧
          G.prims[kl]? = some inlPrim then some (Term.app g v) else none
      | _, _ => none
    | _, _, _, _ => none
  | .caseInr kc kr, .app, [f, u] => match f.label, f.children, u.label, u.children with
    | .arr k _, [p], .arr k' _, [v] => match p.label, p.children with
      | .pair, [_, h] => if k = kc ∧ k' = kr ∧ G.prims[kc]? = some casePrim ∧
          G.prims[kr]? = some inrPrim then some (Term.app h v) else none
      | _, _ => none
    | _, _, _, _ => none
  | .thm j θ σ flip, _, _ => do
    let a ← (E[j]?).bind Entry.language?
    let lr ← if a.hyps = [] then eqParts a.concl else none
    if instOk G n Γ a θ σ ∧ t = instTerm θ σ (if flip then lr.2 else lr.1) then
      some (instTerm θ σ (if flip then lr.1 else lr.2)) else none
  | .rwHyp i flip, _, _ => do
    let lr ← (Φ[i]?).bind eqParts
    if t = (if flip then lr.2 else lr.1) then some (if flip then lr.1 else lr.2) else none
  | _, _, _ => none

/-- The results of a node's rewriting and of its proving, from its children's: the rewriting of
a term in a context under hypotheses, and whether it proves a formula in a context under
hypotheses. -/
abbrev Checks : Type :=
  (List Tree → List Term → Term → Option Term) × (List Tree → List Term → Term → Bool)

/-- One step of the checker, at a node of a rule, from its children's results. -/
def checkStep (G : Globals) (E : Array Entry) (n : ℕ) (l : Rule) (cs : List (Deriv × Checks)) :
    Checks :=
  (fun Γ Φ t ↦ match l, cs with
    | .refl, [] => some t
    | .trans, [(_, c₁), (_, c₂)] => (c₁.1 Γ Φ t).bind (c₂.1 Γ Φ)
    | .cong, cs => do
      let Γs ← congCtxs G n t.label t.children Γ Φ (cs.map Prod.fst)
      if cs.length = t.children.length ∧ Γs.length = t.children.length then do
        let ts ← ((cs.zip (Γs.zip t.children)).mapM fun (c, (Δ, Ψ), u) ↦ c.2.1 Δ Ψ u)
        pure (RoseTree.node t.label ts)
      else none
    | l, [] => rootStep G E n Γ Φ l t
    | _, _ => none,
   fun Γ Φ φ ↦ match l, cs with
    | .join, [(_, c₁), (_, c₂)] => match eqParts φ with
      | some (t, u) => match c₁.1 Γ Φ t, c₂.1 Γ Φ u with
        | some v, some v' => decide (v = v')
        | _, _ => false
      | none => false
    | .natInd kz ks s, [(_, p₀), (_, p₁), (_, p₂)] =>
      match eqParts φ, Γ with
      | some (t, u), c :: Γ' => match typeIn G n Γ t, lowerHyps G n Γ' Φ with
        | some C, some Φ' => decide (c = nat ∧ G.prims[kz]? = some zeroPrim ∧
              G.prims[ks]? = some succPrim ∧ typeIn G n Γ u = some C ∧
              typeIn G n (C :: Γ') s = some C) &&
            p₀.2 Γ' Φ' (Term.eq (Term.subst t (instVar (Term.arr kz [] Term.star)))
              (Term.subst u (instVar (Term.arr kz [] Term.star)))) &&
            p₁.2 Γ Φ (Term.eq (natSuccAt ks t) (Term.subst s (atVar0 t))) &&
            p₂.2 Γ Φ (Term.eq (natSuccAt ks u) (Term.subst s (atVar0 u)))
        | _, _ => false
      | _, _ => false
    | .listInd kn kc s, [(_, p₀), (_, p₁), (_, p₂)] =>
      match eqParts φ, Γ with
      | some (t, u), c :: Γ' => match typeIn G n Γ t, listPart c, lowerHyps G n Γ' Φ with
        | some C, some a, some Φ' => decide (G.prims[kn]? = some nilPrim ∧
              G.prims[kc]? = some consPrim ∧ typeIn G n Γ u = some C ∧
              typeIn G n (C :: a :: Γ') s = some C) &&
            p₀.2 Γ' Φ' (Term.eq (Term.subst t (instVar (Term.arr kn [a] Term.star)))
              (Term.subst u (instVar (Term.arr kn [a] Term.star)))) &&
            p₁.2 (c :: a :: Γ') (Φ'.map weaken2)
              (Term.eq (listConsAt kc a t) (Term.subst s (atVar0 (weakenElem t)))) &&
            p₂.2 (c :: a :: Γ') (Φ'.map weaken2)
              (Term.eq (listConsAt kc a u) (Term.subst s (atVar0 (weakenElem u))))
        | _, _, _ => false
      | _, _ => false
    | .hyp i, [] => decide (Φ[i]? = some φ)
    | .cut ψ, [(_, p), (_, q)] =>
      decide (typeIn G n Γ ψ = some omega) && p.2 Γ Φ ψ && q.2 Γ (Φ ++ [ψ]) φ
    | .conv, [(_, d), (_, p)] => match d.1 Γ Φ φ with
      | some φ' => p.2 Γ Φ φ'
      | none => false
    | .convFrom ψ, [(_, d), (_, p)] =>
      decide (typeIn G n Γ ψ = some omega ∧ d.1 Γ Φ ψ = some φ) && p.2 Γ Φ ψ
    | .propExt, [(_, p), (_, q)] => match eqParts φ with
      | some (α, β) => decide (typeIn G n Γ α = some omega ∧ typeIn G n Γ β = some omega) &&
          p.2 Γ (Φ ++ [α]) β && q.2 Γ (Φ ++ [β]) α
      | none => false
    | .funExt, [(_, p)] => match eqParts φ with
      | some (f, g) => match (typeIn G n Γ f).bind expParts with
        | some (a, _) => p.2 (a :: Γ) (Φ.map weaken1)
            (Term.eq (Term.app (weaken1 f) (Term.var 0)) (Term.app (weaken1 g) (Term.var 0)))
        | none => false
      | none => false
    | .apply j θ σ, ps => match (E[j]?).bind Entry.language? with
      | some a => instOk G n Γ a θ σ && decide (φ = instTerm θ σ a.concl) &&
          decide (ps.length = a.hyps.length) &&
          (ps.zip a.hyps).all fun (p, h) ↦ p.2.2 Γ Φ (instTerm θ σ h)
      | none => false
    | .natIndHyp kz ks, [(_, p₀), (_, p₁)] => match Γ with
      | c :: Γ' => match lowerHyps G n Γ' Φ with
        | some Φ' => decide (c = nat ∧ G.prims[kz]? = some zeroPrim ∧
              G.prims[ks]? = some succPrim ∧ typeIn G n Γ φ = some omega) &&
            p₀.2 Γ' Φ' (Term.subst φ (instVar (Term.arr kz [] Term.star))) &&
            p₁.2 Γ (Φ ++ [φ]) (natSuccAt ks φ)
        | none => false
      | [] => false
    | .listIndHyp kn kc, [(_, p₀), (_, p₁)] => match Γ with
      | c :: Γ' => match listPart c, lowerHyps G n Γ' Φ with
        | some a, some Φ' => decide (G.prims[kn]? = some nilPrim ∧ G.prims[kc]? = some consPrim ∧
              typeIn G n Γ φ = some omega) &&
            p₀.2 Γ' Φ' (Term.subst φ (instVar (Term.arr kn [a] Term.star))) &&
            p₁.2 (c :: a :: Γ') (Φ'.map weaken2 ++ [weakenElem φ]) (listConsAt kc a φ)
        | _, _ => false
      | [] => false
    | .coprodInd kl kr, [(_, p₀), (_, p₁)] => match Γ with
      | c :: Γ' => match coprodParts c, lowerHyps G n Γ' Φ with
        | some (a, b), some _ => decide (G.prims[kl]? = some inlPrim ∧
              G.prims[kr]? = some inrPrim ∧ typeIn G n Γ φ = some omega) &&
            p₀.2 (a :: Γ') Φ (Term.subst φ (atVar0 (Term.arr kl [a, b] (Term.var 0)))) &&
            p₁.2 (b :: Γ') Φ (Term.subst φ (atVar0 (Term.arr kr [a, b] (Term.var 0))))
        | _, _ => false
      | [] => false
    | .zeroInd i, [] => decide (Γ[i]? = some zero ∧ typeIn G n Γ φ = some omega)
    | .quotInd kq θ, [(_, p₀)] => match Γ, G.prims[kq]? with
      | c :: Γ', some p => match p.coeqParts, lowerHyps G n Γ' Φ with
        | some _, some _ => decide (θ.length = p.arity ∧ θ.all (IsTy G n) ∧
              c = PartialHorn.subst θ p.cod ∧ typeIn G n Γ φ = some omega) &&
            p₀.2 (PartialHorn.subst θ p.dom :: Γ') Φ
              (Term.subst φ (atVar0 (Term.arr kq θ (Term.var 0))))
        | _, _ => false
      | _, _ => false
    | .cert c, [] => match eqParts φ with
      | some (t, u) => match compileEq G n Γ t u with
        | some q => certifies G E c q
        | none => false
      | none => false
    | .certSeq c, [] =>
      decide ((∀ ψ ∈ Φ, typeIn G n Γ ψ = some omega) ∧ typeIn G n Γ φ = some omega) &&
        certifies G E c (Thm.seq G ⟨n, Γ, Φ, φ⟩)
    | .roseInd kn kl kc s, [(_, p₁), (_, p₂)] => match eqParts φ, Γ with
      | some (t, u), [r] => match typeIn G n Γ t, roseParts r with
        | some C, some (a, _) => decide (((G.prims[kn]? = some nodePrim ∧ r = rose) ∨
              (G.prims[kn]? = some lnodePrim ∧ r = lrose a)) ∧ G.prims[kl]? = some nilPrim ∧
              G.prims[kc]? = some consPrim ∧ typeIn G n Γ u = some C ∧
              typeIn G n [list C, a] s = some C) &&
            p₁.2 [list r, a] [] (Term.eq (roseNodeAt kn r a t)
              (Term.subst s (atVar0 (roseMapAt kl kc C t)))) &&
            p₂.2 [list r, a] [] (Term.eq (roseNodeAt kn r a u)
              (Term.subst s (atVar0 (roseMapAt kl kc C u))))
        | _, _ => false
      | _, _ => false
    | .roseIndHyp kn kl kc, [(_, p₁)] => match Γ with
      | [r] => match roseParts r with
        | some (a, _) => decide (((G.prims[kn]? = some nodePrim ∧ r = rose) ∨
              (G.prims[kn]? = some lnodePrim ∧ r = lrose a)) ∧ G.prims[kl]? = some nilPrim ∧
              G.prims[kc]? = some consPrim ∧ typeIn G n Γ φ = some omega) &&
            p₁.2 [list r, a] [roseHyp kl kc φ] (roseNodeAt kn r a φ)
        | none => false
      | _ => false
    | _, _ => false)

/-- The checker: the rewriting a derivation performs on a term in a context under hypotheses,
and whether it proves a formula in a context under hypotheses. -/
def check (G : Globals) (E : Array Entry) (n : ℕ) : Deriv → Checks :=
  RoseTree.para (checkStep G E n)

/-- Whether a derivation proves a theorem with the constants of {lit}`G` and the entries of
{lit}`E`: its context is of types, its hypotheses and conclusion are formulas there, and the
derivation proves its conclusion under its hypotheses. -/
def Thm.checks (G : Globals) (E : Array Entry) (a : Thm) (d : Deriv) : Bool :=
  a.ctx.all (IsTy G a.arity) && a.hyps.all (fun h ↦ typeIn G a.arity a.ctx h = some omega) &&
    decide (typeIn G a.arity a.ctx a.concl = some omega) &&
    (check G E a.arity d).2 a.ctx a.hyps a.concl

/-- The sequent of the combinators that a primitive arrow is an arrow from its domain to its
codomain, in its object parameters: its composite with the identities of its domain and of its
codomain is itself. -/
def Prim.seq (p : Prim) : Seq :=
  ⟨List.replicate p.arity obj, [], ⟨comp (idt p.cod) (comp p.arrow (idt p.dom)), p.arrow⟩⟩

/-- Whether a primitive arrow is confirmed with the constants of {lit}`G` and the entries of
{lit}`E`: by the checker's inference, or by a certificate of its sequent, in the theory extended
by the compilations of the definitions of {lit}`G`. -/
def Prim.confirms (G : Globals) (E : Array Entry) (p : Prim) : Option Tree → Bool
  | none => (compileDefs G).any fun cds ↦ decide (G.base = sig.length) && p.ok G (ExtEnv.ofDefs cds)
  | some c => (compileDefs G).any (fun cds ↦ p.wf G (ext cds).sig) && certifies G E c p.seq

/-- Whether an object in object parameters is confirmed with the constants of {lit}`G` and the
entries of {lit}`E`, defined of the sort of objects at every assignment of objects: by the
checker's inference, or by a certificate of its definedness, in the theory extended by the
compilations of the definitions of {lit}`G`. -/
def objConfirms (G : Globals) (E : Array Entry) (m : ℕ) (b : Tree) : Option Tree → Bool
  | none => (compileDefs G).any fun cds ↦
      decide (G.base = sig.length) && objOk (ExtEnv.ofDefs cds) m b
  | some c => (compileDefs G).any (fun cds ↦
      PartialHorn.sortOf (ext cds).sig (List.replicate m obj) b == some obj) &&
    certifies G E c ⟨List.replicate m obj, [], dfd b⟩

/-- Whether a definition compiles with the constants of {lit}`G`, the type of its value a type. -/
def Defn.checks (G : Globals) (d : Defn) : Bool := (d.compile G).isSome && IsTy G d.arity d.type

/-- A declaration of a development, with its proof: a theorem of the language with its
derivation, a sequent of the combinators with its certificate, a definition of the language, a
primitive arrow with the certificate of its sequent, or an object definition with the certificate
of its object's definedness, each certificate none where the checker's inference confirms it. -/
inductive Decl where
  /-- A theorem of the language, with its derivation. -/
  | language (a : Thm) (d : Deriv)
  /-- A sequent of the combinators, with its certificate. -/
  | combinators (s : Seq) (c : Tree)
  /-- A definition of the language. -/
  | definition (d : Defn)
  /-- A primitive arrow, with the certificate of its sequent where inference does not confirm
  it. -/
  | constant (p : Prim) (c : Option Tree)
  /-- An object definition, an object of the combinators in a number of object parameters, with
  the certificate of its definedness where inference does not confirm it. -/
  | object (arity : ℕ) (body : Tree) (c : Option Tree)
  /-- The quotient of a type by a relation, a formula in two variables of the type, in a number
  of object parameters: the coequalizer of the projections of the relation's pullback of truth,
  an object definition, and the projection to it, a primitive arrow, with the theorem that related
  elements have equal images. -/
  | quotient (arity : ℕ) (A : Tree) (R : Term)
  /-- The descent of a function, a term in a variable of the domain of the primitive arrow of
  index {lit}`kq`, a quotient's projection, into the type {lit}`C`, through the quotient: a
  primitive arrow, with the theorem of its computation at an image, the theorem that the
  function respects the relation the entry of index {lit}`jr`. -/
  | descent (kq : ℕ) (C : Tree) (h : Term) (jr : ℕ)

/-- The constants and the environment after a declaration, where its proof proves it with the
constants of {lit}`G` and the environment {lit}`E`: a theorem's entry added to the environment, a
definition or a primitive arrow to the constants. -/
def Decl.step (G : Globals) (E : Array Entry) : Decl → Option (Globals × Array Entry)
  | .language a d => if a.checks G E d then some (G, E.push (.language a)) else none
  | .combinators s c => if certifies G E c s then some (G, E.push (.combinators s)) else none
  | .definition d =>
    if d.checks G then some ({ G with defs := G.defs ++ [.language d] }, E) else none
  | .constant p c =>
    if p.confirms G E c then some ({ G with prims := G.prims ++ [p] }, E) else none
  | .object m b c =>
    if objConfirms G E m b c then some ({ G with defs := G.defs ++ [.object m b] }, E) else none
  | .quotient n A R => match compile G n R (ctxObj [A, A]) (stdEnv [A, A]) with
    | some (r, t) =>
      let q : Prim := ⟨n, coeqProj (relPair A r).1 (relPair A r).2, A,
        op (G.base + G.defs.length) (objVars n)⟩
      let G' : Globals := ⟨G.prims ++ [q], G.defs ++ [.object n (coeqz (relPair A r).1
        (relPair A r).2)], G.base⟩
      let qT := fun i ↦ Term.arr G.prims.length (objVars n) (Term.var i)
      let rel : Thm := ⟨n, [A, A], [R], Term.eq (qT 1) (qT 0)⟩
      if G.base = sig.length ∧ IsTy G n A ∧ t = omega ∧ PartialHorn.Scoped n q.arrow = true ∧
          IsTy G' n q.cod ∧
          (compileDefs G).any (fun cds ↦
            PartialHorn.sortOf (ext cds).sig (List.replicate n obj) q.arrow == some arr) ∧
          typeIn G' n [A, A] rel.concl = some omega then
        some (G', E.push (.language rel))
      else none
    | none => none
  | .descent kq C h jr => match G.prims[kq]?, (E[jr]?).bind Entry.language? with
    | some p, some T =>
      match p.rel?, compile G p.arity h (ctxObj [p.dom]) (stdEnv [p.dom]), T.hyps with
      | some r, some (H, C'), [R'] =>
        let d : Prim := ⟨p.arity, coeqDesc (relPair p.dom r).1 (relPair p.dom r).2 H, p.cod, C⟩
        let G' : Globals := { G with prims := G.prims ++ [d] }
        let dq : Term := Term.arr G.prims.length (objVars p.arity)
          (Term.arr kq (objVars p.arity) (Term.var 0))
        let cmp : Thm := ⟨p.arity, [p.dom], [], Term.eq dq h⟩
        if G.base = sig.length ∧ C' = C ∧ IsTy G p.arity C ∧ T.arity = p.arity ∧
            T.ctx = [p.dom, p.dom] ∧
            T.concl = Term.eq (weaken1 h) h ∧
            compile G p.arity R' (ctxObj [p.dom, p.dom]) (stdEnv [p.dom, p.dom]) =
              some (r, omega) ∧ PartialHorn.Scoped p.arity d.arrow = true ∧
            (compileDefs G).any (fun cds ↦
              PartialHorn.sortOf (ext cds).sig (List.replicate p.arity obj) d.arrow ==
                some arr) ∧
            typeIn G' p.arity [p.dom] cmp.concl = some omega then
          some (G', E.push (.language cmp))
        else none
      | _, _, _ => none
    | _, _ => none

/-- The constants and the environment after a development, where each declaration's proof
proves it with the constants and the entries before it. -/
def checkDev (G : Globals) (E : Array Entry) (ds : List Decl) : Option (Globals × Array Entry) :=
  ds.foldlM (fun st d ↦ d.step st.1 st.2) (G, E)

/-- Whether a development checks: each declaration proved with those before it. -/
def checkThms (G : Globals) (ds : List Decl) (E : Array Entry) : Bool := (checkDev G E ds).isSome

end Geb.FreeTopos.Internal

end
