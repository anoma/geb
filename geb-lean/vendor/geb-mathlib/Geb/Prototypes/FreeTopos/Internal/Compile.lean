/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Check
public import Geb.Prototypes.FreeTopos.Internal.Syntax

set_option doc.verso true in
/-!
# The compilation of the internal language to the combinators

The typing of the internal language's terms and their compilation to arrows of the combinators,
the interpretation of the typed λ-calculus in a cartesian closed category of Part I of
\[LambekScott1986\] and the compilation of the categorical abstract machine of
\[CousineauCurienMauny1987\], in one pass. A type is an object term built by the terminal
object, products, the initial object, coproducts, exponentials, the subobject classifier, the
data objects and the operations of the object definitions of the constants from object variables
({lit}`IsTy`), so that two types are equal when they are one term. A term is compiled in an
environment: an object {lit}`X` and, for each variable, an arrow from {lit}`X` and the variable's
type. A variable compiles to its arrow, a pair to the pairing, a
component to the projection after the pair, an abstraction to the currying of its body, compiled
over the product of {lit}`X` and the bound variable's type, an application to evaluation after the
pairing, a primitive arrow's application to the arrow after its argument, a fold to the composite of
the combinators' fold with the datum, and the equality of two terms to the characteristic map of the
diagonal after their pairing. A context's terms are compiled in the environment of its projections
from the product of its types ({lit}`stdEnv`). A primitive arrow is an arrow of the combinators with
the domain and codomain it names, in object parameters, which the checker's inference confirms once
({lit}`Prim.ok`), for every application at objects.

A definition of the internal language names a term in term parameters and object parameters. It
compiles to a definition of the combinators, the arrow its body compiles to from the product of
its parameters' types, and its application to the composite of that definition's operation with
the tuple of its arguments. The unfolding of a term's definitions ({lit}`unfold`) substitutes the
arguments and objects of each application into the definition's body, itself unfolded. An object
definition names an object of the combinators in object parameters; it compiles to a definition
of the combinators of that object, whose operation at types is a type ({lit}`Definition`). The
definitions of both kinds are one list, each the operation of its position after the
signature's.

## Main definitions

* {lit}`IsTy` — the types.
* {lit}`compile` — the type and the arrow of a term in an environment.
* {lit}`Defn`, {lit}`Definition` — a definition of the internal language, and a definition of
  either kind: of the language or of an object.
* {lit}`compileDefs` — the definitions of the combinators that definitions compile to.
* {lit}`compileEq` — the sequent an equation of two terms in a context compiles to.
* {lit}`unfold` — the unfolding of the definitions a term applies.
* {lit}`Prim`, {lit}`Globals` — the primitive arrows, and the constants a term may apply.
* {lit}`Prim.wf`, {lit}`Prim.ok`, {lit}`Globals.ok` — the check that the constants are well
  formed and each primitive arrow has the types it names.

## References

* \[LambekScott1986\], Part I, for the interpretation of the typed λ-calculus in a
  cartesian closed category.
* \[CousineauCurienMauny1987\] for the compilation of λ-terms to categorical combinators.

## Tags

internal language, typed lambda calculus, cartesian closed category, categorical combinators,
compilation, definition
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree Seq op)
open Sorts
open scoped FinEnum

/-- The operations that build types, by index, with their arities: the terminal object,
products, the initial object, coproducts, exponentials, the subobject classifier, and the natural
numbers object, list objects, the rose-tree object and rose-tree objects over types of
labels. -/
def tyOps : List (ℕ × ℕ) :=
  [(4, 0), (6, 2), (13, 0), (15, 2), (22, 2), (25, 0), (29, 0), (33, 1), (37, 0), (40, 1)]

/-- The factors of a product. -/
def prodParts (p : Tree) : Option (Tree × Tree) := match p.children with
  | [a, b] => if p = prod a b then some (a, b) else none
  | _ => none

/-- The summands of a coproduct. -/
def coprodParts (p : Tree) : Option (Tree × Tree) := match p.children with
  | [a, b] => if p = coprod a b then some (a, b) else none
  | _ => none

/-- The domain and codomain of an exponential. -/
def expParts (p : Tree) : Option (Tree × Tree) := match p.children with
  | [a, b] => if p = exp a b then some (a, b) else none
  | _ => none

/-- The type of labels of a rose-tree object, with the fold of the object by a step: the natural
numbers object for the rose-tree object, and the type of labels of a rose-tree object over
one. -/
def roseParts (p : Tree) : Option (Tree × (Tree → Tree)) :=
  if p = rose then some (nat, roseRec) else match p.children with
    | [a] => if p = lrose a then some (a, lroseRec a) else none
    | _ => none

/-- The element type of a list object. -/
def listPart (p : Tree) : Option Tree := match p.children with
  | [a] => if p = list a then some a else none
  | _ => none

/-- The product of a context's types, the innermost outermost: the terminal object for the empty
context, and the type itself for a context of one. -/
def ctxObj : List Tree → Tree := List.rec one fun a Γ x ↦ match Γ with
  | [] => a
  | _ :: _ => prod x a

/-- The environment over the product of {lit}`X` and {lit}`a` that extends an environment over
{lit}`X` by a variable of type {lit}`a`: the new variable is the second projection, and each
other the first projection followed by its arrow. -/
def extEnv (X a : Tree) (e : List (Tree × Tree)) : List (Tree × Tree) :=
  (snd X a, a) :: e.map fun p ↦ (comp p.1 (fst X a), p.2)

/-- The environment of a context's projections from the product of its types: the identity for a
context of one. -/
def stdEnv : List Tree → List (Tree × Tree) := List.rec [] fun a Γ e ↦ match Γ with
  | [] => [(idt a, a)]
  | _ :: _ => extEnv (ctxObj Γ) a e

/-- The tuple of arrows from {lit}`X`, the last outermost: the arrow to the terminal object for
none, and the arrow itself for one. -/
def tuple (X : Tree) : List Tree → Tree := List.rec (bang X) fun f fs p ↦ match fs with
  | [] => f
  | _ :: _ => pair p f

/-- A definition of the internal language: the number of its object parameters, the types of
its term parameters, the last first, the type of its value, and its body. -/
structure Defn where
  /-- The number of object parameters. -/
  arity : ℕ
  /-- The types of the term parameters, the last first. -/
  params : List Tree
  /-- The type of the value. -/
  type : Tree
  /-- The body, a term in the term parameters. -/
  body : Term

/-- A primitive arrow: an arrow of the combinators, with its domain and its codomain, in a number
of object parameters. -/
structure Prim where
  /-- The number of object parameters. -/
  arity : ℕ
  /-- The arrow. -/
  arrow : Tree
  /-- Its domain. -/
  dom : Tree
  /-- Its codomain. -/
  cod : Tree

/-- Equality of primitive arrows, decided field by field after a comparison of addresses, which
settles it at once where the two are one object, as an entry of a table of primitives and the
constant it lists are. -/
instance : DecidableEq Prim := fun a b ↦ withPtrEqDecEq a b fun _ ↦
  if h : a.arity = b.arity ∧ a.arrow = b.arrow ∧ a.dom = b.dom ∧ a.cod = b.cod then
    isTrue (match a, b, h with | ⟨_, _, _, _⟩, ⟨_, _, _, _⟩, ⟨rfl, rfl, rfl, rfl⟩ => rfl)
  else isFalse fun e ↦ h (e ▸ ⟨rfl, rfl, rfl, rfl⟩)

/-- A definition of a development: a definition of the language, which compiles to a definition
of the combinators, or an object of the combinators in a number of object parameters, which
names a type. -/
inductive Definition where
  /-- A definition of the language. -/
  | language (d : Defn)
  /-- An object of the combinators in object parameters. -/
  | object (arity : ℕ) (body : Tree)

/-- The arities and the sort of the operation a definition compiles to: an arrow of the
language's definition, an object of an object definition, in their object parameters. -/
def Definition.sig : Definition → List ℕ × ℕ
  | .language d => (List.replicate d.arity obj, arr)
  | .object m _ => (List.replicate m obj, obj)

/-- The definition of the language a definition is, where it is one. -/
def Definition.language? : Definition → Option Defn
  | .language d => some d
  | .object _ _ => none

/-- The constants a term may apply: the primitive arrows, and the definitions, the one of index
{lit}`k` the operation of index {lit}`base + k` of the combinators. -/
structure Globals where
  /-- The primitive arrows. -/
  prims : List Prim
  /-- The definitions. -/
  defs : List Definition
  /-- The index of the first definition's operation. -/
  base : ℕ

/-- Whether an operation of the combinators builds types from a number of types: an operation
of {lit}`tyOps`, or the operation of an object definition of {lit}`G` in that number of object
parameters. -/
def Globals.isTyOp (G : Globals) (k m : ℕ) : Bool :=
  decide ((k, m) ∈ tyOps) || decide (G.base ≤ k) && match G.defs[k - G.base]? with
    | some (.object m' _) => m' == m
    | _ => false

/-- Whether an object term is a type in {lit}`n` object variables, with the constants of
{lit}`G`: built from the variables by the operations of {lit}`tyOps` and of the object
definitions. -/
def IsTy (G : Globals) (n : ℕ) : Tree → Bool :=
  RoseTree.para fun l cs ↦ match l, cs with
    | 0, [(i, _)] => i.children.isEmpty && decide (i.label < n)
    | 0, _ => false
    | k + 1, cs => G.isTyOp k cs.length && cs.all Prod.snd

/-- The constants of {lit}`G` are well formed: each primitive arrow is a term in its object
parameters, and the types each constant names are types in them. -/
structure Globals.WF (G : Globals) : Prop where
  /-- Each primitive arrow is a term in its object parameters, between types in them. -/
  prims : ∀ (k : ℕ) (p : Prim), G.prims[k]? = some p →
    PartialHorn.Scoped p.arity p.arrow = true ∧ IsTy G p.arity p.dom = true ∧
      IsTy G p.arity p.cod = true
  /-- Each definition's parameters and value have types in its object parameters. -/
  defs : ∀ (k : ℕ) (d : Defn), G.defs[k]? = some (.language d) →
    d.params.all (IsTy G d.arity) = true ∧ IsTy G d.arity d.type = true

/-- One step of the compilation, at a node of a label, from the compilations of its children:
the arrow and the type of the node's term in {lit}`n` object variables, in an environment over
{lit}`X`, with the constants of {lit}`G`. -/
def compileStep (G : Globals) (n : ℕ) (l : Label)
    (cs : List (Term × (Tree → List (Tree × Tree) → Option (Tree × Tree))))
    (X : Tree) (e : List (Tree × Tree)) : Option (Tree × Tree) :=
  match l, cs with
    | .var i, [] => e[i]?
    | .star, [] => some (bang X, one)
    | .pair, [(_, t), (_, u)] => do
      let (f, a) ← t X e
      let (g, b) ← u X e
      pure (pair f g, prod a b)
    | .fst, [(_, t)] => do
      let (f, p) ← t X e
      let (a, b) ← prodParts p
      pure (comp (fst a b) f, a)
    | .snd, [(_, t)] => do
      let (f, p) ← t X e
      let (a, b) ← prodParts p
      pure (comp (snd a b) f, b)
    | .lam a, [(_, t)] =>
      if IsTy G n a then do
        let (f, b) ← t (prod X a) (extEnv X a e)
        pure (curry X a f, exp a b)
      else none
    | .app, [(_, t), (_, u)] => do
      let (f, p) ← t X e
      let (a, b) ← expParts p
      let (g, a') ← u X e
      if a' = a then pure (comp (ev a b) (pair f g), b) else none
    | .arr k θ, [(_, t)] => do
      let p ← G.prims[k]?
      let (g, d) ← t X e
      if θ.length = p.arity ∧ θ.all (IsTy G n) ∧ d = PartialHorn.subst θ p.dom then
        pure (comp (PartialHorn.subst θ p.arrow) g, PartialHorn.subst θ p.cod)
      else none
    | .natRec, [(_, z), (_, s), (_, m)] => do
      let (z', c) ← z one []
      let (s', c') ← s c [(idt c, c)]
      let (m', t) ← m X e
      if c' = c ∧ t = nat then pure (comp (natRec z' s') m', c) else none
    | .listRec, [(_, z), (_, s), (_, m)] => do
      let (m', t) ← m X e
      let a ← listPart t
      let (z', c) ← z one []
      let (s', c') ← s (prod a c) [(snd a c, c), (fst a c, a)]
      if c' = c then pure (comp (listRec a z' s') m', c) else none
    | .roseRec c, [(_, s), (_, m)] =>
      if IsTy G n c then do
        let (m', t) ← m X e
        let (a, fold) ← roseParts t
        let (s', c') ← s (prod a (list c)) [(idt (prod a (list c)), prod a (list c))]
        if c' = c then pure (comp (fold s') m', c) else none
      else none
    | .eq, [(_, t), (_, u)] => do
      let (f, a) ← t X e
      let (g, b) ← u X e
      if a = b then pure (comp (chi (diag a)) (pair f g), omega) else none
    | .defn k θ, cs => do
      let d ← (G.defs[k]?).bind Definition.language?
      let rs ← cs.mapM fun c ↦ c.2 X e
      if θ.length = d.arity ∧ θ.all (IsTy G n) ∧
          rs.map Prod.snd = d.params.map (PartialHorn.subst θ) then
        pure (comp (op (G.base + k) θ) (tuple X (rs.map Prod.fst)), PartialHorn.subst θ d.type)
      else none
    | _, _ => none

/-- The arrow and the type of a term in {lit}`n` object variables, in an environment over
{lit}`X`, with the constants of {lit}`G`; nothing when the term is not well typed. -/
def compile (G : Globals) (n : ℕ) :
    Term → Tree → List (Tree × Tree) → Option (Tree × Tree) :=
  RoseTree.para (compileStep G n)

/-- The definition of the combinators a definition compiles to, over the definitions before it:
an arrow in the object parameters, from the product of the term parameters' types. -/
def Defn.compile (G : Globals) (d : Defn) : Option PartialHorn.Defn := do
  let (f, c) ← Internal.compile G d.arity d.body (ctxObj d.params) (stdEnv d.params)
  if d.params.all (IsTy G d.arity) ∧ c = d.type then
    pure ⟨List.replicate d.arity obj, arr, f⟩
  else none

/-- The definition of the combinators a definition compiles to, over the definitions before it:
a definition of the language's compilation, and an object definition's object in its object
parameters. -/
def Definition.compile (G : Globals) : Definition → Option PartialHorn.Defn
  | .language d => d.compile G
  | .object m b => some ⟨List.replicate m obj, obj, b⟩

/-- The definitions of the combinators that the definitions of {lit}`G` compile to, each over the
definitions before it. -/
def compileDefs (G : Globals) : Option (List PartialHorn.Defn) :=
  G.defs.zipIdx.mapM fun (d, i) ↦ d.compile { G with defs := G.defs.take i }

/-- The sequent of the combinators an equation of two terms of one type in a context compiles
to: the equation of their arrows from the product of the context's types, in the object
variables. -/
def compileEq (G : Globals) (n : ℕ) (Γ : List Tree) (t u : Term) : Option Seq := do
  let (f, a) ← compile G n t (ctxObj Γ) (stdEnv Γ)
  let (g, b) ← compile G n u (ctxObj Γ) (stdEnv Γ)
  if Γ.all (IsTy G n) ∧ a = b then pure ⟨List.replicate n obj, [], ⟨f, g⟩⟩ else none

/-- The unfolding of the definitions a term applies, given their unfolded bodies: each
application of a definition is replaced by its unfolded body at the application's objects, with
the unfolded arguments substituted for its parameters. -/
def unfold (ubs : List (Option Term)) : Term → Term :=
  RoseTree.elim fun l cs ↦ match l with
    | .defn k θ => match ubs[k]? with
      | some (some b) => Term.subst (Term.osubst θ b) (Term.substList cs)
      | _ => RoseTree.node l cs
    | l => RoseTree.node l cs

/-- The unfolded bodies of a list of definitions, each unfolded by those before it; an object
definition has none. -/
def unfoldBodies (ds : List Definition) : List (Option Term) :=
  ds.foldl (fun ubs d ↦ ubs ++ [d.language?.map fun d ↦ unfold ubs d.body]) []

/-- Whether a primitive arrow is a term in its object parameters of the sort of arrows of a
signature, between types in them with the constants of {lit}`G`. -/
def Prim.wf (G : Globals) (S : PartialHorn.Sig) (p : Prim) : Bool :=
  PartialHorn.Scoped p.arity p.arrow && IsTy G p.arity p.dom && IsTy G p.arity p.cod &&
    PartialHorn.sortOf S (List.replicate p.arity obj) p.arrow == some arr

/-- Whether a primitive arrow is a term in its object parameters that has, by the inference of
the checker, the domain and the codomain it names, which are types in them with the constants of
{lit}`G`, with the definitions of the combinators of {lit}`E`, and is an arrow of their
signature: the canonical forms of its inferred domain and codomain are those the inference
computes for the types. -/
def Prim.ok (G : Globals) (E : ExtEnv) (p : Prim) : Bool :=
  p.wf G E.sg.toList &&
    let inf := (infers E (List.replicate p.arity obj) [] inferFuel).2
    match inf p.arrow, inf p.dom, inf p.cod with
    | some a, some d, some c =>
      a.sort == arr && d.sort == obj && c.sort == obj && a.lo == d.lo && a.hi == c.lo
    | _, _, _ => false

/-- Whether an object in object parameters is an object of a signature, defined at every
assignment of objects by the inference of the checker with the definitions of the combinators of
{lit}`E`. -/
def objOk (E : ExtEnv) (m : ℕ) (b : Tree) : Bool :=
  PartialHorn.sortOf E.sg.toList (List.replicate m obj) b == some obj &&
    ((infers E (List.replicate m obj) [] inferFuel).2 b).isSome

/-- Whether a definition is a definition of the language whose parameters and value have types
with the constants of {lit}`G`; object definitions are declared in a development. -/
def Definition.ok (G : Globals) : Definition → Bool
  | .language d => d.params.all (IsTy G d.arity) && IsTy G d.arity d.type
  | .object _ _ => false

/-- Whether the constants are well formed, the primitive arrows confirmed by the checker's
inference with the definitions of the combinators of {lit}`E`, and the definitions of the
language. -/
def Globals.ok (E : ExtEnv) (G : Globals) : Bool :=
  G.prims.all (Prim.ok G E) && G.defs.all (Definition.ok G)

end Geb.FreeTopos.Internal

end
