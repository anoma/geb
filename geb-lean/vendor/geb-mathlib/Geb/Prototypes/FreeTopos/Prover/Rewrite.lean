/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Prover.Typing

set_option doc.verso true in
/-!
# Rewriting terms of the theory of an elementary topos, with certificates

The prover's second layer rewrites arrows by equations of the theory or of the development, each
read in a chosen direction, and normalizes a term by rewriting innermost first. A rule's side
matches a term up to canonical objects: the arrows of the side match syntactically, and each
object of the side matches every object whose canonical form is that of the side's instance, so
that a rule stated with {lit}`cod f` applies where the term writes the object {lit}`cod f`
equals. The certificate of a step is the equation of the term with the instance of the rule's
side, by congruence and the canonical forms of the objects where they differ, followed by the
instance of the rule, whose hypotheses are proved as the typing proves an axiom's.

Normal forms compose to the right: the associativity rule rewrites {lit}`comp (comp h g) f` to
{lit}`comp h (comp g f)`, and a rule whose left side is a composite {lit}`comp a b` applies
within {lit}`comp a (comp b x)` through associativity, so that it applies wherever the
composite occurs as a prefix of a chain. A term's normal form is recorded with the certificate
of its equation, as a lemma, so that a term is normalized once in a scope.

## Main definitions

* {lit}`Src`, {lit}`RwRule` — a rewriting rule: an axiom or a theorem of the development, read
  in a direction.
* {lit}`matchPat` — the match of a rule's side against a term.
* {lit}`applyRule` — one rewriting step at a term's root, with its certificate.
* {lit}`normalize` — the normal form of a term under rules, with its certificate.

## Tags

elementary topos, rewriting, proof certificate, normalization
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Prover

open PartialHorn Sorts
open scoped FinEnum

/-- Where a rewriting rule's equation comes from. -/
inductive Src where
  /-- An axiom of the theory, by index. -/
  | ax (j : ℕ)
  /-- A theorem of the development, by index. -/
  | thm (j : ℕ)

/-- The sequent of a rule's source. -/
def Src.seq : Src → PM Seq
  | .ax j => axiomAt j
  | .thm j => do
    match (← get).dev[j]? with
    | some e => pure e.1
    | none => failure

/-- The certificate of a source's instance. -/
def Src.cert : Src → List Tree → List Tree → List Tree → Tree
  | .ax j => Cert.ax j
  | .thm j => Cert.thm j

/-- A rewriting rule: the equation of a source, read from left to right, or from right to left
when {lit}`flip` holds, not applied at a term whose root has a label of {lit}`avoid`. -/
structure RwRule where
  /-- The source. -/
  src : Src
  /-- Whether the equation is read from right to left. -/
  flip : Bool := false
  /-- The root labels at which the rule does not apply. -/
  avoid : List ℕ := []

/-- The state of a match: the terms assigned to the variables, and the objects of the side to be
matched to the term's objects by canonical form. -/
structure MatchSt where
  /-- The assignment. -/
  σ : List (Option Tree)
  /-- The objects of the side, with the objects of the term at their positions. -/
  objs : List (Tree × Tree)

/-- The match of a rule's side, in a context of sorts, against a term: arrows match
syntactically, a variable is assigned the term at its first occurrence and matches it at the
others, and an object whose variables are assigned is deferred to be matched by canonical
form. -/
def matchPat (S : Sig) (ctx : List ℕ) : Tree → Tree → MatchSt → Option MatchSt :=
  RoseTree.para fun l cs t ms ↦
    let p := RoseTree.node l (cs.map Prod.fst)
    match l, cs with
    | 0, [(i, _)] =>
      match ms.σ[i.label]? with
      | some none => some { ms with σ := ms.σ.set i.label (some t) }
      | some (some u) =>
        if u == t then some ms
        else if ctx[i.label]? == some obj then some { ms with objs := (p, t) :: ms.objs }
        else none
      | none => none
    | _ + 1, cs =>
      if sortOf S ctx p == some obj then some { ms with objs := (p, t) :: ms.objs }
      else if t.label == l && t.children.length == cs.length then
        (cs.zip t.children).foldlM (fun ms (c, u) ↦ c.2 u ms) ms
      else none
    | _, _ => none

/-- The certificate that a term equals the instance of a rule's side at the typed assignment
{lit}`tys`, when they differ only in objects of one canonical form. -/
def bridge (tys : List Ty) : Tree → Tree → PM Tree :=
  RoseTree.para fun l cs t ↦ do
    let p := RoseTree.node l (cs.map Prod.fst)
    let ty ← typeTerm t
    if subst (tys.map Ty.term) p == t then pure ty.dfd
    else if ty.sort == obj then objEq ty (← typePattern tys p)
    else if l == 0 || t.children.length != cs.length then failure
    else pure (Cert.cong ty.dfd (← (cs.zip t.children).mapM fun (c, u) ↦ c.2 u))

/-- One rewriting step at a term's root: the instance of the rule's other side, with the
certificate of the term's equation with it. -/
def applyRule (r : RwRule) (t : Tree) : PM (Tree × Tree) := do
  guard (!r.avoid.contains t.label)
  let a ← r.src.seq
  let (p, q) := if r.flip then (a.concl.rhs, a.concl.lhs) else (a.concl.lhs, a.concl.rhs)
  let some ms := matchPat (← get).sig a.ctx p t ⟨a.ctx.map fun _ ↦ none, []⟩ | failure
  let some σ := ms.σ.mapM id | failure
  let tys ← σ.mapM typeTerm
  for (o, u) in ms.objs do
    let _ ← objEq (← typePattern tys o) (← typeTerm u)
  let b ← bridge tys p t
  let hs ← a.hyps.mapM (proveHyp typePattern tys)
  let i := r.src.cert σ (tys.map Ty.dfd) hs
  pure (subst σ q, Cert.trans b (if r.flip then Cert.symm i else i))

/-- The first rule of a list that applies at a term's root. -/
def firstRule (rules : List RwRule) (t : Tree) : PM (Tree × Tree) :=
  rules.foldr (fun r k ↦ applyRule r t <|> k) failure

/-- The instance of associativity {lit}`comp a (comp b x) = comp (comp a b) x`, at a defined
term of that shape. -/
def assocLeft (t : Tree) : PM (Tree × Tree × Tree × Tree) := do
  match t.label, t.children with
  | 4, [a, bx] =>
    match bx.label, bx.children with
    | 4, [b, x] =>
      let d ← typeTerm t
      pure (a, b, x, Cert.ax 7 [a, b, x] [(← typeTerm a).dfd, (← typeTerm b).dfd,
        (← typeTerm x).dfd] [d.dfd])
    | _, _ => failure
  | _, _ => failure

/-- One rewriting step at a term's root: a rule at the root, or a rule at the composite
{lit}`comp a b` of a term {lit}`comp a (comp b x)`, through associativity. -/
def rewriteRoot (rules : List RwRule) (t : Tree) : PM (Tree × Tree) :=
  firstRule rules t <|> do
    let (a, b, x, c) ← assocLeft t
    let (u, cu) ← firstRule rules (comp a b)
    let ab ← typeTerm (comp (comp a b) x)
    pure (comp u x, Cert.trans c (Cert.cong ab.dfd [cu, (← typeTerm x).dfd]))

/-- The normal form of a term, if recorded in the scope. -/
def lookupNf (t : Tree) : PM (Option (Tree × Tree)) := do
  pure ((← get).nfs.find? t)

/-- Record a term's normal form, the certificate of its equation proved as a lemma when the
term is not normal. -/
def memoizeNf (t n c : Tree) : PM (Tree × Tree) := do
  let c ← if t == n then pure c else addLemma ⟨t, n⟩ c
  modify fun st ↦ { st with nfs := st.nfs.insert t (n, c) }
  pure (n, c)

/-- One step of normalization: an object's canonical form; a variable itself; an application
with normal arguments, rewritten at its root and the result normalized by {lit}`rec`. -/
def normStep (rules : List RwRule) (rec : Tree → PM (Tree × Tree)) :
    ℕ → List (Tree × PM (Tree × Tree)) → PM (Tree × Tree) := fun l cs ↦ do
  let t := RoseTree.node l (cs.map Prod.fst)
  if let some r ← lookupNf t then return r
  let ty ← typeTerm t
  if ty.sort == obj then return (ty.lo, ty.loCert)
  if l == 0 then return (t, ty.dfd)
  let rs ← cs.mapM Prod.snd
  let t₁ := RoseTree.node l (rs.map Prod.fst)
  let c₁ := if t₁ == t then ty.dfd else Cert.cong ty.dfd (rs.map Prod.snd)
  match ← (some <$> rewriteRoot rules t₁) <|> pure none with
  | none => memoizeNf t t₁ c₁
  | some (t₂, c₂) =>
    let (t₃, c₃) ← rec t₂
    memoizeNf t t₃ (Cert.trans c₁ (Cert.trans c₂ c₃))

/-- The normalizers at a fuel, each normalizing the rewritten terms at the fuel below. -/
def normalizers (rules : List RwRule) : ℕ → Tree → PM (Tree × Tree) :=
  Nat.rec (fun _ ↦ failure) fun _ rec ↦ RoseTree.para (normStep rules rec)

/-- The fuel of normalization: the number of rewriting steps at one position. -/
def normFuel : ℕ := 64

/-- The normal form of a term under rules, with the certificate of its equation. -/
def normalize (rules : List RwRule) (t : Tree) : PM (Tree × Tree) :=
  normalizers rules normFuel t

end Geb.FreeTopos.Prover

end
