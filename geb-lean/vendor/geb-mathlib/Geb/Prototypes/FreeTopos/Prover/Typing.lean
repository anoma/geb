/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Theory
public import Geb.Prototypes.PartialHorn.Definitional
public import Geb.Prototypes.PartialHorn.Share
public import Geb.Prototypes.FreeTopos.Infer

set_option doc.verso true in
/-!
# Typing terms of the theory of an elementary topos, with certificates

The prover's first layer computes, for a term of the theory {name}`Geb.FreeTopos.theory` in a
scope, a certificate that the term is defined, and for an object its canonical form, for an
arrow its canonical domain and codomain, each with the certificate of its equation. A canonical
object is an object whose domains and codomains of compound arrows have been replaced by the
objects the axioms compute for them, so that two objects the axioms equate by computing domains
and codomains have one canonical form. A domain or codomain of an arrow variable is canonical
unless a hypothesis of the scope equates it with an object, whose canonical form is then its
canonical form.

The rules are read off the axioms rather than written for each operation. An application of an
operation is defined by the axiom concluding its definedness from hypotheses, which are proved
in turn; or by strictness at an axiom without hypotheses whose left side applies an operation to
the application; or, for a constant, by an axiom without hypotheses whose right side the
constant is. Its domain and codomain are those of the axioms whose left side is the domain or
codomain of the application. An application of a definition in force, an operation of the
theory's extension by definitions ({name}`Geb.PartialHorn.Theory.extendAll`), is typed by the
definition's first axiom, which equates it with the instance of its body.

The facts proved about each term are lemmas of the development in the scope, cited wherever
they are used, so that a term's certificates are proved once and each certificate that uses
them has the size of a citation. The prover runs in a state of the development and a table
of the terms typed so far.

## Main definitions

* {lit}`DfdRule`, {lit}`dfdRules`, {lit}`domRules`, {lit}`codRules` — how the axioms type each
  operation.
* {lit}`Ty` — a term's typing.
* {lit}`PM` — the prover's monad: a scope, and the state of the development, the definitions in
  force and the table of typings.
* {lit}`axiomAt`, {lit}`typeDefined` — the axioms of the extension by the definitions in force,
  and the typing of a definition's application.
* {lit}`typeTerm` — the typing of a term of the scope.

## Tags

elementary topos, partial Horn logic, proof certificate, type inference
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Prover

open PartialHorn Sorts
open scoped FinEnum

/-- A term's typing: the term, its sort, the certificate that it is defined, and for an object
its canonical form, for an arrow its canonical domain and codomain, each with the certificate of
its equation. For an object both bounds are its canonical form. -/
structure Ty where
  /-- The term. -/
  term : Tree
  /-- Its sort. -/
  sort : ℕ
  /-- The certificate that it is defined. -/
  dfd : Tree
  /-- For an object, its canonical form; for an arrow, its canonical domain. -/
  lo : Tree
  /-- The certificate that the object, or the arrow's domain, equals {lit}`lo`. -/
  loCert : Tree
  /-- For an object, its canonical form; for an arrow, its canonical codomain. -/
  hi : Tree
  /-- The certificate that the object, or the arrow's codomain, equals {lit}`hi`. -/
  hiCert : Tree

/-- The prover's state: the development, and the typings and normal forms of the terms typed
and normalized in the current scope. -/
structure St where
  /-- The development: the theorems proved so far and their certificates. -/
  dev : Array (Seq × Tree)
  /-- The typings of the terms typed in the current scope. -/
  memo : Table Ty := {}
  /-- The normal forms of the terms normalized in the current scope, with the certificates of
  their equations. -/
  nfs : Table (Tree × Tree) := {}
  /-- The definitions in force, each an operation after the signature's and those before it. -/
  defs : List Defn := []
  /-- The signature extended by the definitions in force. -/
  sig : Sig := FreeTopos.sig
  /-- Whether the typing's certificates are the checker's oracle rules
  ({lit}`checkTopos`) rather than lemmas. -/
  infer : Bool := false

/-- The prover's monad: a scope, and the state of the development and the typings. -/
abbrev PM : Type → Type := ReaderT Scope (StateT St Option)

/-- The axiom of index {lit}`j` of the theory extended by the definitions in force. -/
def axiomAt (j : ℕ) : PM Seq := do
  if h : j < axioms.length then pure axioms[j] else
  let r := j - axioms.length
  match (← get).defs[r / 2]? with
  | some d => match (d.axioms (sig.length + r / 2))[r % 2]? with
    | some a => pure a
    | none => failure
  | none => failure

/-- A lemma: the conclusion, proved in the scope by the certificate, added to the development;
the result is its citation. -/
def addLemma (q : Eqn) (c : Tree) : PM Tree := do
  let sc ← read
  let st ← get
  set { st with dev := st.dev.push (sc.seq q, c) }
  pure (sc.cite st.dev.size)

/-- The typing of a term, if it has been typed in the scope. -/
def lookup (t : Tree) : PM (Option Ty) := do
  pure ((← get).memo.find? t)

/-- Record a term's typing. -/
def memoize (ty : Ty) : PM Unit :=
  modify fun st ↦ { st with memo := st.memo.insert ty.term ty }

/-- The certificate that a term is defined: the oracle's rule when inferring, else a lemma
proved by {lit}`c`. -/
def dfdCert (t : Tree) (c : Tree) : PM Tree := do
  if (← get).infer then pure (RoseTree.node Rule.typed [t]) else addLemma (dfd t) c

/-- The certificate of an equation between objects of one canonical form: the oracle's rule
when inferring, else a lemma proved by {lit}`c`. -/
def eqCert (q : Eqn) (c : Tree) : PM Tree := do
  if (← get).infer then pure (RoseTree.node Rule.objEq [q.lhs, q.rhs]) else addLemma q c

/-- The certificate of an equation between two objects, from their typings, when their
canonical forms agree. -/
def objEq (l r : Ty) : PM Tree := do
  guard (l.sort == obj && r.sort == obj && l.lo == r.lo)
  if (← get).infer then pure (RoseTree.node Rule.objEq [l.term, r.term])
  else pure (Cert.trans l.loCert (Cert.symm r.loCert))

/-- The certificate of a hypothesis of an axiom at arguments, typing its instance's sides with
{lit}`patTy`: a definedness by the typing, an equation between objects by canonical forms. -/
def proveHyp (patTy : List Ty → Tree → PM Ty) (tys : List Ty) (h : Eqn) : PM Tree := do
  let l ← patTy tys h.lhs
  if h.lhs == h.rhs then pure l.dfd else objEq l (← patTy tys h.rhs)

/-- The canonical bound of an application of operation {lit}`k`, by the axiom {lit}`j`
computing it, whose hypotheses are definedness, the application's being {lit}`d`: the canonical
form of the axiom's right side, with the certificate that the bound equals it. -/
def bound (patTy : List Ty → Tree → PM Ty) (tys : List Ty) (k j : ℕ) (d : Tree) :
    PM (Tree × Tree) := do
  let a ← axiomAt j
  let hs ← a.hyps.mapM fun h ↦
    if h == dfd (opVars k tys.length) then pure d else proveHyp patTy tys h
  let q := Cert.ax j (tys.map Ty.term) (tys.map Ty.dfd) hs
  let r ← patTy tys a.concl.rhs
  pure (r.lo, Cert.trans q r.loCert)

/-- The typing of an application of the definition at position {lit}`i`, of sort {lit}`s`, to
terms of the given typings: its first axiom equates it with the body's instance, whose typing
gives the application's definedness and bounds. -/
def typeDefined (patTy : List Ty → Tree → PM Ty) (i s : ℕ) (tys : List Ty) : PM Ty := do
  let some dfn := (← get).defs[i]? | failure
  let ts := tys.map Ty.term
  let t := op (sig.length + i) ts
  let b ← patTy tys dfn.body
  if (← get).infer then
    let d := RoseTree.node Rule.typed [t]
    let ty : Ty := if s == obj then ⟨t, obj, d, b.lo, RoseTree.node Rule.objEq [t, b.lo], b.lo,
        RoseTree.node Rule.objEq [t, b.lo]⟩
      else ⟨t, arr, d, b.lo, RoseTree.node Rule.objEq [dom t, b.lo], b.hi,
        RoseTree.node Rule.objEq [cod t, b.hi]⟩
    memoize ty
    return ty
  let e ← addLemma ⟨t, b.term⟩ (Cert.ax (defAxIdx i) ts (tys.map Ty.dfd) [b.dfd])
  let d ← addLemma (dfd t) (Cert.trans e (Cert.symm e))
  let ty ← if s == obj then do
      let c ← addLemma ⟨t, b.lo⟩ (Cert.trans e b.loCert)
      pure ⟨t, obj, d, b.lo, c, b.lo, c⟩
    else do
      let dc ← addLemma ⟨dom t, b.lo⟩
        (Cert.trans (Cert.cong (Cert.ax 0 [t] [d] []) [e]) b.loCert)
      let cc ← addLemma ⟨cod t, b.hi⟩
        (Cert.trans (Cert.cong (Cert.ax 1 [t] [d] []) [e]) b.hiCert)
      pure ⟨t, arr, d, b.lo, dc, b.hi, cc⟩
  memoize ty
  pure ty

/-- The typing of an application of operation {lit}`k` to terms of the given typings, typing
the instances of axioms' sides with {lit}`patTy`. -/
def typeOp (patTy : List Ty → Tree → PM Ty) (k : ℕ) (tys : List Ty) : PM Ty := do
  let ts := tys.map Ty.term
  let t := op k ts
  let some (as, s) := (← get).sig[k]? | failure
  guard (tys.map Ty.sort == as)
  if sig.length ≤ k then return ← typeDefined patTy (k - sig.length) s tys
  let dc ← match dfdRules[k]? with
    | some (some (.direct j)) => do
      let a ← axiomAt j
      pure (Cert.ax j ts (tys.map Ty.dfd) (← a.hyps.mapM (proveHyp patTy tys)))
    | some (some (.strict j)) => pure (Cert.strict 0 (Cert.ax j ts (tys.map Ty.dfd) []))
    | some (some (.rhs j)) =>
      let q := Cert.ax j [] [] []
      pure (Cert.trans (Cert.symm q) q)
    | _ => failure
  let d ← dfdCert t dc
  let ty ← if s == obj then
      match k, tys with
      | 0, [f] => pure ⟨t, obj, d, f.lo, f.loCert, f.lo, f.loCert⟩
      | 1, [f] => pure ⟨t, obj, d, f.hi, f.hiCert, f.hi, f.hiCert⟩
      | _, _ =>
        let c := op k (tys.map fun ty ↦ if ty.sort == obj then ty.lo else ty.term)
        if c == t then pure ⟨t, obj, d, t, d, t, d⟩
        else do
          let e ← eqCert ⟨t, c⟩
            (Cert.cong d (tys.map fun ty ↦ if ty.sort == obj then ty.loCert else ty.dfd))
          pure ⟨t, obj, d, c, e, c, e⟩
    else do
      let some (some jd) := domRules[k]? | failure
      let some (some jc) := codRules[k]? | failure
      let (dl, dc) ← bound patTy tys k jd d
      let (cl, cc) ← bound patTy tys k jc d
      pure ⟨t, arr, d, dl, ← eqCert ⟨dom t, dl⟩ dc, cl, ← eqCert ⟨cod t, cl⟩ cc⟩
  memoize ty
  pure ty

/-- One step of typing: a variable's node by {lit}`leaf`, an application by {lit}`typeOp` unless
its term, which {lit}`term` computes from the node, has been typed. -/
def typeStep (patTy : List Ty → Tree → PM Ty) (leaf : ℕ → PM Ty) (term : Tree → Tree) :
    ℕ → List (Tree × PM Ty) → PM Ty
  | 0, [(i, _)] => leaf i.label
  | k + 1, cs => do
    if let some ty ← lookup (term (RoseTree.node (k + 1) (cs.map Prod.fst))) then return ty
    typeOp patTy k (← cs.mapM Prod.snd)
  | _, _ => failure

/-- The typing of a variable of the scope. A domain or codomain that a hypothesis equates with
an object has that object's canonical form, typed by {lit}`termTy`. -/
def typeVar (termTy : Tree → PM Ty) (i : ℕ) : PM Ty := do
  let sc ← read
  match sc.ctx[i]? with
  | some obj => pure ⟨var i, obj, Cert.refl i, var i, Cert.refl i, var i, Cert.refl i⟩
  | some arr =>
    let infer := (← get).infer
    let side (o j : ℕ) : PM (Tree × Tree) :=
      match sc.hyps.findIdx? (·.lhs == op o [var i]) with
      | some h => do
        let some q := sc.hyps[h]? | failure
        let r ← termTy q.rhs
        pure (r.lo, if infer then RoseTree.node Rule.objEq [op o [var i], r.lo]
          else Cert.trans (Cert.hyp h) r.loCert)
      | none => pure (op o [var i], Cert.ax j [var i] [Cert.refl i] [])
    let (dl, dc) ← side 0 0
    let (cl, cc) ← side 1 1
    pure ⟨var i, arr, Cert.refl i, dl, dc, cl, cc⟩
  | _ => failure

/-- The typers at a fuel: of an axiom's side instantiated at typed arguments, and of a term of
the scope. Each types the instances of axioms' sides it meets at the fuel below. -/
def typers : ℕ → (List Ty → Tree → PM Ty) × (Tree → PM Ty) :=
  Nat.rec (fun _ _ ↦ failure, fun _ ↦ failure) fun _ rec ↦
    (fun env ↦ RoseTree.para (typeStep rec.1 (fun i ↦ match env[i]? with
        | some ty => pure ty
        | none => failure) (subst (env.map Ty.term))),
      RoseTree.para (typeStep rec.1 (typeVar rec.2) id))

/-- The fuel of typing: the depth of the axioms' sides instantiated while typing. -/
def typingFuel : ℕ := 8

/-- The typing of a term of the scope. -/
def typeTerm (t : Tree) : PM Ty := (typers typingFuel).2 t

/-- The typing of an axiom's side instantiated at typed arguments. -/
def typePattern (env : List Ty) (p : Tree) : PM Ty := (typers typingFuel).1 env p

/-- Run the prover in a scope from a development, with no term typed, with definitions in
force, its typing certified by lemmas or, when {lit}`infer` holds, by the checker's oracle
rules. -/
def run {α : Type} (sc : Scope) (dev : Development) (m : PM α) (defs : List Defn := [])
    (infer : Bool := false) : Option (α × Development) :=
  let st : St := {
    dev := dev.toArray
    defs := defs
    sig := sig ++ defs.map (fun d ↦ (d.ctx, d.sort))
    infer := infer }
  (m.run sc |>.run st).map fun (a, st) ↦ (a, st.dev.toList)

end Geb.FreeTopos.Prover

end
