/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Derivation

set_option doc.verso true in
/-!
# An environment machine reducing terms

A reduction of the internal language's terms by evaluation in environments of values
(\[Landin1964\]), lazily and with each delayed value computed at most once
(\[Launchbury1993\]): a term is evaluated in an environment that holds a value for each of
its variables, an abstraction to its closure, and a definition's application to its body
evaluated in the environment of its arguments' values, so that no term is substituted into
another as the reduction proceeds. The rules it computes are those of the base checker's
rewriting at the root ({name}`Geb.FreeTopos.Internal.rootStep`): β, the components of pairs, the
folds of the natural numbers, of lists and of rose trees at their constructions, the case
analysis of a coproduct at its injections, and the unfolding of the definitions that a
predicate selects.

An argument, a component of a pair, the datum of a primitive arrow and the start of a fold are
delayed: each is a node of two children, the value of a {name}`Thunk`, the weak head normal
form of the term's value, which the runtime computes when the child is first read and keeps, and
the term with its environment, which the node reads back as. A delayed value's weak head normal
form is that child, so that a stuck value an environment shares is reduced once rather than at
each of its uses. Logically a {name}`Thunk` is its function, so that a delayed node is the
value beside its source, and the reduction is the strict evaluation whose every delayed value
reads back to the term it delays. The recursion's value that a fold's rule substitutes into its
step is delayed so, its source the fold of the construction's datum. Every value reads back to
a term to which the evaluated term rewrites, by the base checker's rules at the root and by
congruences at children in the term's context; the reduction is sound by that rewriting, and is
not the prover's.

The normal form of a value is taken by evaluation and reading back
(\[BergerSchwichtenberg1991\]), under its constructors, its abstractions and the steps of its
folds: the body of a closure and the step of a fold are evaluated in their environment extended
by fresh variables, and normalized in the context those variables extend, by the congruences of
the base checker, so that the values of the environment are shared with that evaluation rather
than read back. A free variable of a value is a de Bruijn level, which counts binders from the
outside and so denotes one variable under every further binder, the variables of the reduced
term's context having negative levels; at a depth it reads back to the index of the same variable.
A value therefore needs no adjustment under a binder, and it reads back at every depth at which
its levels are bound. The context of a fold's step holds the type of the fold's start, or of its
list or tree, which the base checker's congruence computes; the machine computes it of the normal
form, and does not reduce a fold whose normal form has no type.

The normal form is taken in a context, and each of its nodes, its children's normal forms taken,
is rewritten at its root by a rewriting the machine is given, which reads the context and the
number of binders passed, so that it can rewrite by theorems, whose instances it types in the
context, and by hypotheses, weakened past those binders, as the prover's normalization does
innermost first. A rewritten term is evaluated again and its normal form taken, and so is a node
that eliminates a child within which a rewriting changed a term, since the rewriting may make the
node a redex; a rewriting is taken only where the result's variables are leaves.

## Main definitions

* {lit}`VLabel`, {lit}`Val` — the values.
* {lit}`envSubst`, {lit}`readBack` — the substitution an environment stands for, and the term a
  value reads back to at a depth.
* {lit}`delayed` — the delayed value of a computation.
* {lit}`Machine`, {lit}`machine` — the evaluation of terms in environments, the weak head normal
  form of values and the normal form of a value's term in a context, rewritten at its roots,
  within a depth of recursion.
* {lit}`machineReduce` — the reduction of a term.

## References

* \[Landin1964\], for the evaluation of expressions in environments of closures.
* \[Launchbury1993\], for lazy evaluation that computes each delayed value at most once.

## Tags

internal language, abstract machine, environment, closure, lazy evaluation, reduction
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)

/-- The label of a node of a value. -/
inductive VLabel where
  /-- The variable of a de Bruijn level: under {lit}`D` binders, of the index {lit}`D - 1 - l`. -/
  | free (l : ℤ)
  /-- The element of the terminal object. -/
  | star
  /-- The pair of two values. -/
  | pair
  /-- The closure of the abstraction of the term {lit}`b` over a variable of the type {lit}`a`,
  in the environment of the node's children, past which the variables are those under {lit}`k`
  binders. -/
  | clo (a : Tree) (b : Term) (k : ℕ)
  /-- The application of the primitive arrow of an index, at objects, to a value. -/
  | arr (k : ℕ) (θ : List Tree)
  /-- The application of a value to a value. -/
  | app
  /-- The first component of a value. -/
  | fst
  /-- The second component of a value. -/
  | snd
  /-- The fold of a natural number by the step {lit}`s`, from the start and of the number the
  node's first two children, in the environment of the others, past which the variables are those
  under {lit}`k` binders. -/
  | natRec (s : Term) (k : ℕ)
  /-- The fold of a list by the step {lit}`s`, from the start and of the list the node's first
  two children, in the environment of the others, past which the variables are those under
  {lit}`k` binders. -/
  | listRec (s : Term) (k : ℕ)
  /-- The fold of a rose tree into the type {lit}`c` by the step {lit}`s`, of the tree the node's
  first child, in the environment of the others, past which the variables are those under
  {lit}`k` binders. -/
  | roseRec (c : Tree) (s : Term) (k : ℕ)
  /-- The application of the definition of an index, at objects, to values. -/
  | defn (k : ℕ) (θ : List Tree)
  /-- The equality of two values. -/
  | eq
  /-- The term {lit}`t` in the environment of the node's children, past which the variables are
  those under {lit}`k` binders, unevaluated. -/
  | term (t : Term) (k : ℕ)
  /-- A delayed value: the value, the node's first child, of the value its second child is the
  source of, which it reads back as. -/
  | delay
  /-- The value of a computation that does not reach one. -/
  | fail

/-- A value of the machine: a tree of {lit}`VLabel`, an environment the children of a closure, of
a fold or of an unevaluated term. -/
abbrev Val : Type := RoseTree VLabel

/-- The substitution an environment stands for: the variable of an index in it its value's
term, and each later variable the variable past the environment's values shifted by
{lit}`k`, the binders passed since the environment's. -/
def envSubst (ts : List Term) (k : ℕ) : ℕ → Term := fun i ↦
  if h : i < ts.length then ts[i] else Term.var (i - ts.length + k)

/-- One step of the reading back of a value to a term under {lit}`D` binders, at a node of a label,
from the terms of its children: a free variable to the variable of its level's index; a closure
to its abstraction with the environment's terms substituted in its body, a fold to its fold with
them substituted in its step, an unevaluated term to the term with them substituted, each past
its environment shifted by the binders since its own; a delayed value to its source's term, and
every other node to the node of the term's label of the same name. -/
def readStep (D : ℕ) : VLabel → List Term → Term
  | .free l, _ => Term.var ((D : ℤ) - 1 - l).toNat
  | .star, _ => Term.star
  | .pair, cs => RoseTree.node .pair cs
  | .clo a b k, cs => Term.lam a (Term.subst b (Term.liftS (envSubst cs (D - k))))
  | .arr j θ, cs => RoseTree.node (.arr j θ) cs
  | .app, cs => RoseTree.node .app cs
  | .fst, cs => RoseTree.node .fst cs
  | .snd, cs => RoseTree.node .snd cs
  | .natRec s k, z :: m :: cs =>
    Term.natRec z (Term.subst s (Term.liftS (envSubst cs (D - k)))) m
  | .natRec _ _, cs => RoseTree.node .natRec cs
  | .listRec s k, z :: m :: cs =>
    Term.listRec z (Term.subst s (Term.liftS (Term.liftS (envSubst cs (D - k))))) m
  | .listRec _ _, cs => RoseTree.node .listRec cs
  | .roseRec c s k, m :: cs =>
    Term.roseRec c (Term.subst s (Term.liftS (envSubst cs (D - k)))) m
  | .roseRec c _ _, cs => RoseTree.node (.roseRec c) cs
  | .defn j θ, cs => RoseTree.node (.defn j θ) cs
  | .eq, cs => RoseTree.node .eq cs
  | .term t k, cs => Term.subst t (envSubst cs (D - k))
  | .delay, [_, c] => c
  | .delay, _ => Term.star
  | .fail, _ => Term.star

/-- The term a value reads back to under {lit}`D` binders: the fold of {lit}`readStep`, save that a
delayed value reads back to its source's term alone, the term of its value not computed, so that
reading back does not run the computations a value delays. -/
def readBack (D : ℕ) : Val → Term :=
  WType.elim Term fun ⟨(l, n), g⟩ ↦ match l with
    | .delay => if h : n = 2 then g ⟨1, h ▸ Nat.one_lt_two⟩ else readStep D .delay (List.ofFn g)
    | l => readStep D l (List.ofFn g)

/-- The node of a value of a label over values. -/
abbrev vnode (l : VLabel) (cs : List Val) : Val := RoseTree.node l cs

/-- The value of a computation that does not reach one. -/
abbrev failV : Val := vnode .fail []

/-- The delayed value of a computation, the value {lit}`src` its source: the node whose first
child the runtime computes when it is first read, and keeps. -/
def delayed (th : Thunk (Option Val)) (src : Val) : Val :=
  WType.mk (.delay, 2) fun i ↦ if i.1 = 0 then th.get.getD failV else src

/-- The label of a value's node of a label of a term whose children are values in the term's
environment: the pair, the components, the application, the primitive arrows and the
equality. -/
def Label.plain? : Label → Option VLabel
  | .pair => some .pair
  | .fst => some .fst
  | .snd => some .snd
  | .app => some .app
  | .arr j θ => some (.arr j θ)
  | .eq => some .eq
  | _ => none

/-- The machine's operations at a depth of recursion: the evaluation of a term in an
environment past which its variables are those under a number of binders, the weak head normal
form of a value, and the normal form of a value's term in a context. -/
structure Machine where
  /-- The evaluation of a term in an environment past which its variables are those under a number
  of binders. -/
  eval : Term → List Val → ℕ → Option Val
  /-- The weak head normal form of a value. -/
  whnf : Val → Option Val
  /-- The normal form of a value's term in a context, under a number of the binders the context
  extends, under every constructor, abstraction and step of a fold, with whether a rewriting at a
  root changed it where that may make a node eliminating it a redex. -/
  nf : List Tree → ℕ → Val → Option (Term × Bool)

variable (G : Globals) (n : ℕ) (unfold : ℕ → Bool) (kl kc : ℕ)

/-- The delayed value of a term in an environment past which its variables are those under
{lit}`k` binders, the weak head normal form of its evaluation by {lit}`o`. -/
def Machine.delay (o : Machine) (t : Term) (vs : List Val) (k : ℕ) : Val :=
  delayed (Thunk.mk fun _ ↦ (o.eval t vs k).bind o.whnf) (vnode (.term t k) vs)

/-- One step of the evaluation of a term in an environment past which its variables are those
under {lit}`k` binders, the subterms and the values reduced by {lit}`o`: a variable to its value,
or past the environment to the free variable of its level; an abstraction to its closure; a
component and an application to the weak head normal form of the node over the value of its head,
the argument delayed; a fold to its weak head normal form, its start delayed; a definition the
predicate selects, applied to one argument per parameter, to its body evaluated in the environment
of its arguments, delayed; and a pair, a primitive arrow's application and an equality to the node
over its children, delayed. -/
def Machine.evalStep (o : Machine) (t : Term) (vs : List Val) (k : ℕ) : Option Val :=
  match t.label, t.children with
  | .var i, _ => some (if h : i < vs.length then vs[i]
      else vnode (.free ((k : ℤ) - 1 - ((i - vs.length : ℕ) : ℤ))) [])
  | .star, [] => some (vnode .star [])
  | .lam a, [b] => some (vnode (.clo a b k) vs)
  | .fst, [p] => do o.whnf (vnode .fst [← o.eval p vs k])
  | .snd, [p] => do o.whnf (vnode .snd [← o.eval p vs k])
  | .app, [f, u] => do o.whnf (vnode .app [← o.eval f vs k, o.delay u vs k])
  | .natRec, [z, s, m] => do
    o.whnf (vnode (.natRec s k) (o.delay z vs k :: (← o.eval m vs k) :: vs))
  | .listRec, [z, s, m] => do
    o.whnf (vnode (.listRec s k) (o.delay z vs k :: (← o.eval m vs k) :: vs))
  | .roseRec c, [s, m] => do o.whnf (vnode (.roseRec c s k) ((← o.eval m vs k) :: vs))
  | .defn j θ, ts =>
    let us := ts.map fun u ↦ o.delay u vs k
    match if unfold j then (G.defs[j]?).bind Definition.language? else none with
    | some d =>
      if ts.length = d.params.length then
        o.eval (if θ.isEmpty then d.body else Term.osubst θ d.body) us k
      else some (vnode (.defn j θ) us)
    | none => some (vnode (.defn j θ) us)
  | l, ts => do
    let l' ← l.plain?
    some (vnode l' (ts.map fun u ↦ o.delay u vs k))

/-- One step of the weak head normal form of a value, the values reduced and the terms evaluated
by {lit}`o`: a delayed value to its value, which is a weak head normal form; a component of a
pair, an application of a closure, the case analysis at an injection, and a fold at a
construction, each reduced, the recursion's value of a fold delayed, its source the fold of the
construction's datum; every other value is its own. -/
def Machine.whnfStep (o : Machine) (v : Val) : Option Val :=
  match v.label, v.children with
  | .delay, [r, _] => match r.label with
    | .fail => none
    | _ => some r
  | .fst, [p] => do
    let p' ← o.whnf p
    match p'.label, p'.children with
    | .pair, [a, _] => o.whnf a
    | _, _ => some (vnode .fst [p'])
  | .snd, [p] => do
    let p' ← o.whnf p
    match p'.label, p'.children with
    | .pair, [_, b] => o.whnf b
    | _, _ => some (vnode .snd [p'])
  | .app, [f, u] => do
    let f' ← o.whnf f
    match f'.label, f'.children with
    | .clo _ b k, env => o.whnf (← o.eval b (u :: env) k)
    | .arr j _, [p] =>
      if G.prims[j]? = some casePrim then do
        let u' ← o.whnf u
        match u'.label, u'.children with
        | .arr j' _, [w] =>
          if G.prims[j']? = some inlPrim ∨ G.prims[j']? = some inrPrim then do
            let p' ← o.whnf p
            match p'.label, p'.children with
            | .pair, [g, h] =>
              o.whnf (vnode .app [if G.prims[j']? = some inlPrim then g else h, w])
            | _, _ => some (vnode .app [f', u'])
          else some (vnode .app [f', u'])
        | _, _ => some (vnode .app [f', u'])
      else some (vnode .app [f', u])
    | _, _ => some (vnode .app [f', u])
  | .natRec s k, z :: m :: env => do
    let m' ← o.whnf m
    match m'.label, m'.children with
    | .arr j [], [c] =>
      if G.prims[j]? = some zeroPrim then do
        let c' ← o.whnf c
        match c'.label, c'.children with
        | .star, [] => o.whnf z
        | _, _ => some (vnode (.natRec s k) (z :: m' :: env))
      else if G.prims[j]? = some succPrim then do
        let src := vnode (.natRec s k) (z :: c :: env)
        let r := delayed (Thunk.mk fun _ ↦ o.whnf src) src
        o.whnf (← o.eval s (r :: env) k)
      else some (vnode (.natRec s k) (z :: m' :: env))
    | _, _ => some (vnode (.natRec s k) (z :: m' :: env))
  | .listRec s k, z :: m :: env => do
    let m' ← o.whnf m
    match m'.label, m'.children with
    | .arr j [_], [c] =>
      if G.prims[j]? = some nilPrim then do
        let c' ← o.whnf c
        match c'.label, c'.children with
        | .star, [] => o.whnf z
        | _, _ => some (vnode (.listRec s k) (z :: m' :: env))
      else if G.prims[j]? = some consPrim then do
        let c' ← o.whnf c
        match c'.label, c'.children with
        | .pair, [h, tl] => do
          let src := vnode (.listRec s k) (z :: tl :: env)
          let r := delayed (Thunk.mk fun _ ↦ o.whnf src) src
          o.whnf (← o.eval s (r :: h :: env) k)
        | _, _ => some (vnode (.listRec s k) (z :: m' :: env))
      else some (vnode (.listRec s k) (z :: m' :: env))
    | _, _ => some (vnode (.listRec s k) (z :: m' :: env))
  | .roseRec c s k, m :: env => do
    let m' ← o.whnf m
    match m'.label, m'.children with
    | .arr j _, [p] =>
      if (G.prims[j]? = some nodePrim ∨ G.prims[j]? = some lnodePrim) ∧
          G.prims[kl]? = some nilPrim ∧ G.prims[kc]? = some consPrim then do
        let p' ← o.whnf p
        match p'.label, p'.children with
        | .pair, [l, cs] =>
          let folds := vnode (.listRec (Term.arr kc [c] (Term.pair
              (Term.roseRec c (weakenStep2 s) (Term.var 1)) (Term.var 0))) k)
            (vnode (.arr kl [c]) [vnode .star []] :: cs :: env)
          let r := delayed (Thunk.mk fun _ ↦ o.whnf folds) folds
          o.whnf (← o.eval s (vnode .pair [l, r] :: env) k)
        | _, _ => some (vnode (.roseRec c s k) (m' :: env))
      else some (vnode (.roseRec c s k) (m' :: env))
    | _, _ => some (vnode (.roseRec c s k) (m' :: env))
  | _, _ => some v

/-- Whether a node of a label eliminates one of its children, so that a rewriting within them
may make it a redex: an application, a component and a fold. -/
def VLabel.eliminates : VLabel → Bool
  | .app | .fst | .snd | .natRec _ _ | .listRec _ _ | .roseRec _ _ _ => true
  | _ => false

/-- The normal form of a term in a context under {lit}`k` binders, the normal form by {lit}`o` of
its value in the empty environment, marked as changed by a rewriting. -/
def Machine.renorm (o : Machine) (Γ : List Tree) (k : ℕ) (t : Term) : Option (Term × Bool) := do
  let (u, _) ← o.nf Γ k (← o.eval t [] k)
  pure (u, true)

/-- The normal form of a weak head normal form's term in a context under {lit}`k` binders, the
values reduced by {lit}`o`, with whether a rewriting changed it where that may make a node
eliminating it a redex: the normal forms of its children in the term's context; a closure's body
and a fold's step evaluated in its environment extended by the free variables of the levels next
after {lit}`k`, and normalized in the context those variables extend, which a rewriting within
them leaves a fold stuck; an unevaluated term read back unreduced. -/
def Machine.nfNode (o : Machine) (Γ : List Tree) (k : ℕ) (w : Val) : Option (Term × Bool) :=
  match w.label, w.children with
  | .natRec s k', z :: m :: env => do
    let (z', bz) ← o.nf Γ k z
    let (m', bm) ← o.nf Γ k m
    let c ← typeIn G n Γ z'
    let (s', _) ← o.nf (c :: Γ) (k + 1) (← o.eval s (vnode (.free k) [] :: env) k')
    pure (Term.natRec z' s' m', bz || bm)
  | .listRec s k', z :: m :: env => do
    let (z', bz) ← o.nf Γ k z
    let (m', bm) ← o.nf Γ k m
    let c ← typeIn G n Γ z'
    let a ← (typeIn G n Γ m').bind listPart
    let (s', _) ← o.nf (c :: a :: Γ) (k + 2)
      (← o.eval s (vnode (.free ((k + 1 : ℕ) : ℤ)) [] :: vnode (.free k) [] :: env) k')
    pure (Term.listRec z' s' m', bz || bm)
  | .roseRec c s k', m :: env => do
    let (m', bm) ← o.nf Γ k m
    let p ← (typeIn G n Γ m').bind roseParts
    let (s', _) ← o.nf (prod p.1 (list c) :: Γ) (k + 1)
      (← o.eval s (vnode (.free k) [] :: env) k')
    pure (Term.roseRec c s' m', bm)
  | .clo a b k', env => do
    let (t, bt) ← o.nf (a :: Γ) (k + 1) (← o.eval b (vnode (.free k) [] :: env) k')
    pure (Term.lam a t, bt)
  | .free _, cs | .star, cs | .pair, cs | .arr _ _, cs | .app, cs | .fst, cs | .snd, cs
    | .defn _ _, cs | .eq, cs => do
    let rs ← cs.mapM (o.nf Γ k)
    pure (readStep k w.label (rs.map Prod.fst), rs.any Prod.snd)
  | .fail, _ => none
  | _, _ => some (readBack k w, false)

variable (rw : List Tree → ℕ → Term → Option Term)

/-- One step of the normal form of a value's term in a context under {lit}`k` binders, the values
reduced by {lit}`o` and the terms rewritten at their roots by {lit}`rw`: the weak head normal
form, then the normal form of its node ({lit}`Machine.nfNode`); a node that eliminates a child
within which a rewriting changed a term is reduced again, and any other is rewritten at its root
where {lit}`rw` rewrites it to a term whose variables are leaves, the result reduced again. -/
def Machine.nfStep (o : Machine) (Γ : List Tree) (k : ℕ) (v : Val) : Option (Term × Bool) := do
  let w ← o.whnf v
  let (t, b) ← o.nfNode G n Γ k w
  if b && w.label.eliminates then o.renorm Γ k t
  else match rw Γ k t with
    | some u => if u.VarLeaves then o.renorm Γ k u else pure (t, b)
    | none => pure (t, b)

/-- The machine within a depth of recursion of {lit}`fuel`, each operation's recursive calls
made at the depth below. -/
def machine (fuel : ℕ) : Machine :=
  fuel.rec ⟨fun _ _ _ ↦ none, fun _ ↦ none, fun _ _ _ ↦ none⟩ fun _ o ↦
    ⟨Machine.evalStep G unfold o, Machine.whnfStep G kl kc o, Machine.nfStep G n rw o⟩

/-- The reduction of a term in a context by the machine within a depth of recursion of
{lit}`fuel`: the normal form of its value in the empty environment. -/
def machineReduce (fuel : ℕ) (Γ : List Tree) (t : Term) : Option Term := do
  let m := machine G n unfold kl kc rw fuel
  (← m.nf Γ 0 (← m.eval t [] 0)).1

end Geb.FreeTopos.Internal

end
