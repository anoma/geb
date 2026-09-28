/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Prover.Tactic

set_option doc.verso true in
/-!
# Induction in the prover for the theory of an elementary topos

Induction is the uniqueness of recursion. Two arrows from the natural numbers object are equal
when each satisfies the recursion equations of one start and one step, for each is then the
recursion; likewise from a list object. The recursion equations are proved by normalization.

An arrow from the product of a list object with a parameter object is determined by its value
at the empty list, a function of the parameter, and a step from an element, the value at the
tail and the parameter. The induction on such arrows is the induction on their curryings, arrows
from the list object into the exponential, at the start and step that curry the given ones;
the arrows are then the evaluations of their curryings.

## Main definitions

* {lit}`instBy` — the instance of an axiom or theorem, its equations between arrows proved by
  normalization.
* {lit}`congBy` — the equation of two terms that differ by an equation's sides.
* {lit}`byNatInduction`, {lit}`byListInduction` — induction on the natural numbers object and on
  a list object.
* {lit}`byListParamInduction` — induction on a list object with a parameter.

## Tags

elementary topos, induction, recursion, proof certificate
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Prover

open PartialHorn Sorts
open scoped FinEnum

/-- The instance of a source's sequent at terms, its hypotheses proved by the typing or, for an
equation between arrows, by normalization under rules. -/
def instBy (rules : List RwRule) (s : Src) (σ : List Tree) : PM (Eqn × Tree) := do
  let a ← s.seq
  let tys ← σ.mapM typeTerm
  let hs ← a.hyps.mapM fun h ↦ proveHyp typePattern tys h <|> byNorm rules (h.subst σ)
  pure (a.concl.subst σ, s.cert σ (tys.map Ty.dfd) hs)

/-- The certificate that two terms are equal when the second is the first with occurrences of
an equation's left side replaced by its right side, objects compared by canonical form. -/
def congBy (e : Eqn) (ce : Tree) : Tree → Tree → PM Tree :=
  RoseTree.para fun l cs t ↦ do
    let s := RoseTree.node l (cs.map Prod.fst)
    let ty ← typeTerm s
    if s == t then pure ty.dfd
    else if s == e.lhs && t == e.rhs then pure ce
    else if ty.sort == obj then objEq ty (← typeTerm t)
    else if l == 0 || t.label != l || t.children.length != cs.length then failure
    else pure (Cert.cong ty.dfd (← (cs.zip t.children).mapM fun (c, u) ↦ c.2 u))

/-- The certificate that an arrow from the natural numbers object is the recursion with a start
and a step, its recursion equations proved by normalization. -/
def natRecUniq (rules : List RwRule) (z s f : Tree) : PM Tree := do
  let (_, c) ← instBy rules (.ax (axIdx beforeNat 12)) [z, s, f]
  pure c

/-- The certificate that an arrow from the list object of {lit}`a` is the recursion with a
start and a step, its recursion equations proved by normalization. -/
def listRecUniq (rules : List RwRule) (a z s f : Tree) : PM Tree := do
  let (_, c) ← instBy rules (.ax (axIdx beforeList 13)) [a, z, s, f]
  pure c

/-- The certificate of an equation between arrows from the natural numbers object, both
recursions with the start and the step. -/
def byNatInduction (rules : List RwRule) (z s : Tree) (q : Eqn) : PM Tree := do
  pure (Cert.trans (← natRecUniq rules z s q.lhs) (Cert.symm (← natRecUniq rules z s q.rhs)))

/-- The certificate of an equation between arrows from the list object of {lit}`a`, both
recursions with the start and the step. -/
def byListInduction (rules : List RwRule) (a z s : Tree) (q : Eqn) : PM Tree := do
  pure (Cert.trans (← listRecUniq rules a z s q.lhs)
    (Cert.symm (← listRecUniq rules a z s q.rhs)))

/-- The certificate of an equation between arrows from the product of the list object of
{lit}`a` with a parameter, both determined by the value {lit}`z` at the empty list, an arrow
from the parameter, and the step {lit}`s`, an arrow from the product of the product of an
element and a value with the parameter: induction on their curryings, then evaluation. -/
def byListParamInduction (rules : List RwRule) (a z s : Tree) (q : Eqn) : PM Tree := do
  let ty ← typeTerm q.lhs
  let (l, p) ← match ty.lo.label, ty.lo.children with
    | 7, [l, p] => pure (l, p)
    | _, _ => failure
  let b := ty.hi
  let e := exp p b
  let ae := prod a e
  let z' := curry one p (comp z (snd one p))
  let s' := curry ae p (comp s (pair
    (pair (comp (fst a e) (fst ae p))
      (comp (ev p b) (pair (comp (snd a e) (fst ae p)) (snd ae p))))
    (snd ae p)))
  let cf := curry l p q.lhs
  let cg := curry l p q.rhs
  let cc ← byListInduction rules a z' s' ⟨cf, cg⟩
  let (bf, pf) ← inst (.ax (axIdx beforeExponential 7)) [l, p, q.lhs]
  let (bg, pg) ← inst (.ax (axIdx beforeExponential 7)) [l, p, q.rhs]
  let mid ← congBy ⟨cf, cg⟩ cc bf.lhs bg.lhs
  pure (Cert.trans (Cert.symm pf) (Cert.trans mid pg))

end Geb.FreeTopos.Prover

end
