/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.LF.Rewrite
public import Geb.Prototypes.LF.Topos.Signature

set_option doc.verso true in
/-!
# The computation rules of the internal language as rewrite rules

The computation rules of the fragment of the Mitchell–Bénabou language represented by
{name}`Geb.LF.Topos.sig`, as rewrite rules on its constants (\[CousineauDowek2007\]): the β
rule of abstraction, the two computation rules of pairs, the two of each of the folds of the
natural numbers and of lists, the one of each of the folds of rose trees, and the two of the case
analysis of a coproduct. Modulo these rules a term and the term it computes to are terms of the
same types, so that an equation that holds by computation is proved by reflexivity alone, the
regime in which \[NormanAvigad2025\] searches with recursors' reduction rules. The η rules of
pairs and of the terminal type, whose left sides are not applications of a constant, stay
derivation rules of the signature, as do the computation rules themselves, which are redundant
modulo the rules.

## Main definitions

* {lit}`betaRule`, {lit}`fstPairRule`, {lit}`sndPairRule`, {lit}`natZeroRule`,
  {lit}`natSuccRule`, {lit}`listNilRule`, {lit}`listConsRule`, {lit}`roseNodeRule`,
  {lit}`lroseNodeRule`, {lit}`caseInlRule`, {lit}`caseInrRule` — the rules.
* {lit}`rules` — the list of them.

## References

* \[CousineauDowek2007\]
* \[NormanAvigad2025\], Section 3.1.

## Tags

logical framework, LF, rewriting, β-reduction, recursor
-/

set_option doc.verso true

@[expose] public section

namespace Geb.LF.Topos

open Expr (arrow)

/-- {lit}`app A B (lam A B F) a ↦ F a`, in {lit}`A B : tp, F : tm A → tm B, a : tm A`. -/
def betaRule : Rule where
  vars := [tm (v 2), arrow (tm (v 1)) (tm (v 0)), tp, tp]
  lhs := app (v 3) (v 2) (lam (v 3) (v 2) (v 1)) (v 0)
  rhs := Expr.var 1 [v 0]

/-- {lit}`fst A B (pair A B a b) ↦ a`, in {lit}`A B : tp, a : tm A, b : tm B`. -/
def fstPairRule : Rule where
  vars := [tm (v 1), tm (v 1), tp, tp]
  lhs := fst (v 3) (v 2) (pair (v 3) (v 2) (v 1) (v 0))
  rhs := v 1

/-- {lit}`snd A B (pair A B a b) ↦ b`, in {lit}`A B : tp, a : tm A, b : tm B`. -/
def sndPairRule : Rule where
  vars := [tm (v 1), tm (v 1), tp, tp]
  lhs := snd (v 3) (v 2) (pair (v 3) (v 2) (v 1) (v 0))
  rhs := v 0

/-- {lit}`natRec C z s (zeroAt t) ↦ z`, in {lit}`C : tp, z : tm C, s : tm C → tm C, t : tm 1`:
zero at any element of the terminal object, all of which are its element by the η rule of the
terminal type. -/
def natZeroRule : Rule where
  vars := [tm one, arrow (tm (v 1)) (tm (v 1)), tm (v 0), tp]
  lhs := natRec (v 3) (v 2) (v 1) (zeroAt (v 0))
  rhs := v 2

/-- {lit}`natRec C z s (succ n) ↦ s (natRec C z (λ x. s x) n)`, in
{lit}`C : tp, z : tm C, s : tm C → tm C, n : tm N`. -/
def natSuccRule : Rule where
  vars := [tm nat, arrow (tm (v 1)) (tm (v 1)), tm (v 0), tp]
  lhs := natRec (v 3) (v 2) (v 1) (succ (v 0))
  rhs := Expr.var 1 [natRec (v 3) (v 2) (Expr.lam (Expr.var 2 [v 0])) (v 0)]

/-- {lit}`listRec A C z s (nilAt A t) ↦ z`, in
{lit}`A C : tp, z : tm C, s : tm A → tm C → tm C, t : tm 1`. -/
def listNilRule : Rule where
  vars := [tm one, arrow (tm (v 2)) (arrow (tm (v 1)) (tm (v 1))), tm (v 0), tp, tp]
  lhs := listRec (v 4) (v 3) (v 2) (v 1) (nilAt (v 4) (v 0))
  rhs := v 2

/-- {lit}`listRec A C z s (cons A (pair A (list A) h t)) ↦ s h (listRec A C z (λ h r. s h r) t)`,
in {lit}`A C : tp, z : tm C, s : tm A → tm C → tm C, h : tm A, t : tm (list A)`. -/
def listConsRule : Rule where
  vars := [tm (list (v 4)), tm (v 3), arrow (tm (v 2)) (arrow (tm (v 1)) (tm (v 1))), tm (v 0),
    tp, tp]
  lhs := listRec (v 5) (v 4) (v 3) (v 2) (cons (v 5) (pair (v 5) (list (v 5)) (v 1) (v 0)))
  rhs := Expr.var 2 [v 1, listRec (v 5) (v 4) (v 3) (Expr.lam (Expr.lam (Expr.var 4 [v 1, v 0])))
    (v 0)]

/-- {lit}`roseRec C s (node (pair l cs)) ↦ s (pair l (listRec rose (list C) (nil C)
(λ h acc. cons C (pair (roseRec C (λ x. s x) h) acc)) cs))`, in
{lit}`C : tp, s : tm (N × list C) → tm C, l : tm N, cs : tm (list rose)`. -/
def roseNodeRule : Rule where
  vars := [tm (list rose), tm nat, arrow (tm (prod nat (list (v 0)))) (tm (v 0)), tp]
  lhs := roseRec (v 3) (v 2) (node (pair nat (list rose) (v 1) (v 0)))
  rhs := Expr.var 2 [pair nat (list (v 3)) (v 1) (listRec rose (list (v 3)) (nil (v 3))
    (Expr.lam (Expr.lam (cons (v 5) (pair (v 5) (list (v 5))
      (roseRec (v 5) (Expr.lam (Expr.var 5 [v 0])) (v 1)) (v 0))))) (v 0))]

/-- {lit}`lroseRec A C s (lnode A (pair l cs)) ↦ s (pair l (listRec (lrose A) (list C) (nil C)
(λ h acc. cons C (pair (lroseRec A C (λ x. s x) h) acc)) cs))`, in
{lit}`A C : tp, s : tm (A × list C) → tm C, l : tm A, cs : tm (list (lrose A))`. -/
def lroseNodeRule : Rule where
  vars := [tm (list (lrose (v 3))), tm (v 2), arrow (tm (prod (v 1) (list (v 0)))) (tm (v 0)), tp,
    tp]
  lhs := lroseRec (v 4) (v 3) (v 2) (lnode (v 4) (pair (v 4) (list (lrose (v 4))) (v 1) (v 0)))
  rhs := Expr.var 2 [pair (v 4) (list (v 3)) (v 1) (listRec (lrose (v 4)) (list (v 3)) (nil (v 3))
    (Expr.lam (Expr.lam (cons (v 5) (pair (v 5) (list (v 5))
      (lroseRec (v 6) (v 5) (Expr.lam (Expr.var 5 [v 0])) (v 1)) (v 0))))) (v 0))]

/-- {lit}`app (coprod A B) C (case A B C (pair g h)) (inl A B u) ↦ app A C g u`, in
{lit}`A B C : tp, g : tm (A ⇒ C), h : tm (B ⇒ C), u : tm A`. -/
def caseInlRule : Rule where
  vars := [tm (v 4), tm (exp (v 2) (v 1)), tm (exp (v 2) (v 0)), tp, tp, tp]
  lhs := app (coprod (v 5) (v 4)) (v 3)
    (case (v 5) (v 4) (v 3) (pair (exp (v 5) (v 3)) (exp (v 4) (v 3)) (v 2) (v 1)))
    (inl (v 5) (v 4) (v 0))
  rhs := app (v 5) (v 3) (v 2) (v 0)

/-- {lit}`app (coprod A B) C (case A B C (pair g h)) (inr A B u) ↦ app B C h u`, in
{lit}`A B C : tp, g : tm (A ⇒ C), h : tm (B ⇒ C), u : tm B`. -/
def caseInrRule : Rule where
  vars := [tm (v 3), tm (exp (v 2) (v 1)), tm (exp (v 2) (v 0)), tp, tp, tp]
  lhs := app (coprod (v 5) (v 4)) (v 3)
    (case (v 5) (v 4) (v 3) (pair (exp (v 5) (v 3)) (exp (v 4) (v 3)) (v 2) (v 1)))
    (inr (v 5) (v 4) (v 0))
  rhs := app (v 4) (v 3) (v 1) (v 0)

/-- The rules. -/
def rules : List Rule :=
  [betaRule, fstPairRule, sndPairRule, natZeroRule, natSuccRule, listNilRule, listConsRule,
    roseNodeRule, lroseNodeRule, caseInlRule, caseInrRule]

end Geb.LF.Topos

end
