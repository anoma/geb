/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Derivation

set_option doc.verso true in
/-!
# The connectives of the internal language

The connectives, definitions of the internal language in terms of equality, as in a local set
theory (\[RuizHernandezSolorzano2021\], Section 3.2): truth is the equality of the element of
the terminal object with itself; a conjunction the equality of the pair of its formulas with the
pair of truths; an implication the equality of the conjunction with the antecedent; the
universal quantifier over a type, applied to a predicate, the equality of the predicate with the
predicate constantly true; falsity the universal quantification of every formula; a negation
the implication of falsity; a disjunction, and an existential quantification, the formula every
consequence of each disjunct, and of each instance, implies; a unique existential quantification
the existential quantification and the equality of every two instances. Each connective is
applied to its arguments as the definition of an index, the definitions placed at the index
{lit}`o` onward among a development's definitions.

Their introduction and elimination rules are theorems with hypotheses, each with its derivation,
placed at the index {lit}`j` onward among a development's theorems. Implication and universal
quantification are introduced by functions of derivations: the introduction of an implication
from a derivation of its consequent under its antecedent, by propositional extensionality, and of
a universal quantification from a derivation of its body at a new variable, by function
extensionality.

## Main definitions

* {lit}`Logic.tt`, {lit}`Logic.conj`, {lit}`Logic.imp`, {lit}`Logic.all`, {lit}`Logic.ff`,
  {lit}`Logic.neg`, {lit}`Logic.disj`, {lit}`Logic.ex`, {lit}`Logic.exu` — the connectives'
  applications.
* {lit}`Logic.defs` — the connectives' definitions.
* {lit}`Logic.impI`, {lit}`Logic.allI` — the introduction of implication and of universal
  quantification.
* {lit}`Logic.theorems` — the introduction and elimination rules.

## References

* \[RuizHernandezSolorzano2021\]

## Tags

internal language, local set theory, intuitionistic logic, connectives
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal.Logic

open PartialHorn (Tree)
open Sorts

/-- Truth, the definition of index {lit}`o`. -/
def tt (o : ℕ) : Term := Term.defn o [] []

/-- The conjunction of two formulas. -/
def conj (o : ℕ) (p q : Term) : Term := Term.defn (o + 1) [] [q, p]

/-- The implication of a formula by another. -/
def imp (o : ℕ) (p q : Term) : Term := Term.defn (o + 2) [] [q, p]

/-- The universal quantification over the type {lit}`a` of a predicate. -/
def all (o : ℕ) (a : Tree) (P : Term) : Term := Term.defn (o + 3) [a] [P]

/-- Falsity. -/
def ff (o : ℕ) : Term := Term.defn (o + 4) [] []

/-- The negation of a formula. -/
def neg (o : ℕ) (p : Term) : Term := Term.defn (o + 5) [] [p]

/-- The disjunction of two formulas. -/
def disj (o : ℕ) (p q : Term) : Term := Term.defn (o + 6) [] [q, p]

/-- The existential quantification over the type {lit}`a` of a predicate. -/
def ex (o : ℕ) (a : Tree) (P : Term) : Term := Term.defn (o + 7) [a] [P]

/-- The unique existential quantification over the type {lit}`a` of a predicate. -/
def exu (o : ℕ) (a : Tree) (P : Term) : Term := Term.defn (o + 8) [a] [P]

/-- The connectives' definitions, the first of index {lit}`o`: truth, conjunction, implication,
universal quantification, falsity, negation, disjunction, existential quantification and unique
existential quantification. -/
def defs (o : ℕ) : List Defn := [
  ⟨0, [], omega, Term.eq Term.star Term.star⟩,
  ⟨0, [omega, omega], omega,
    Term.eq (Term.pair (Term.var 1) (Term.var 0)) (Term.pair (tt o) (tt o))⟩,
  ⟨0, [omega, omega], omega, Term.eq (conj o (Term.var 1) (Term.var 0)) (Term.var 1)⟩,
  ⟨1, [exp (x 0) omega], omega, Term.eq (Term.var 0) (Term.lam (x 0) (tt o))⟩,
  ⟨0, [], omega, all o omega (Term.lam omega (Term.var 0))⟩,
  ⟨0, [omega], omega, imp o (Term.var 0) (ff o)⟩,
  ⟨0, [omega, omega], omega, all o omega (Term.lam omega
    (imp o (conj o (imp o (Term.var 2) (Term.var 0)) (imp o (Term.var 1) (Term.var 0)))
      (Term.var 0)))⟩,
  ⟨1, [exp (x 0) omega], omega, all o omega (Term.lam omega
    (imp o (all o (x 0) (Term.lam (x 0) (imp o (Term.app (Term.var 2) (Term.var 0))
      (Term.var 1)))) (Term.var 0)))⟩,
  ⟨1, [exp (x 0) omega], omega, conj o (ex o (x 0) (Term.var 0)) (all o (x 0) (Term.lam (x 0)
    (all o (x 0) (Term.lam (x 0) (imp o (conj o (Term.app (Term.var 2) (Term.var 1))
      (Term.app (Term.var 2) (Term.var 0))) (Term.eq (Term.var 1) (Term.var 0)))))))⟩]

/-- A derivation's node of a rule. -/
def nd (l : Rule) (cs : List Deriv := []) : Deriv := RoseTree.node l cs

/-- The proof of truth: its unfolding's sides are one term. -/
def trueI : Deriv := nd .conv [nd .delta, nd .join [nd .refl, nd .refl]]

/-- The proof of the equality with truth of the hypothesis of index {lit}`i`: truth under it,
and it under truth. -/
def eqTrueI (i : ℕ) : Deriv := nd .propExt [trueI, nd (.hyp i)]

/-- The proof of the unfolding of the hypothesis {lit}`ψ`, of index {lit}`i`. -/
def unfoldHyp (ψ : Term) (i : ℕ) : Deriv := nd (.convFrom ψ) [nd .delta, nd (.hyp i)]

/-- The introduction of the implication of {lit}`q` by {lit}`p`, under {lit}`n` hypotheses, from
the derivation {lit}`d` of {lit}`q` under them and {lit}`p`: the conjunction and the antecedent
entail each other. -/
def impI (j n : ℕ) (p q : Term) (d : Deriv) : Deriv :=
  nd .conv [nd .delta, nd .propExt [nd (.apply (j + 2) [] [q, p]) [nd (.hyp n)],
    nd (.apply (j + 1) [] [q, p]) [nd (.hyp n), d]]]

/-- The introduction of a universal quantification of an abstraction from the derivation
{lit}`d` of its body at a new variable, under truth: the predicate's applications to the new
variable and truth are equal. -/
def allI (d : Deriv) : Deriv :=
  nd .conv [nd .delta, nd .funExt [nd .conv [nd .cong [nd .beta, nd .beta],
    nd .propExt [trueI, d]]]]

/-- The variable of index {lit}`i`. -/
def v (i : ℕ) : Term := Term.var i

/-- The introduction and elimination rules, the first of index {lit}`j`, each with its
derivation, for the connectives' definitions from the index {lit}`o`: the introduction of truth,
of conjunction, of disjunction and of existential quantification, and the elimination of
conjunction, implication, universal quantification, falsity, disjunction and existential
quantification. -/
def theorems (o j : ℕ) : List (Thm × Deriv) :=
  let E' : Term := Term.lam omega (imp o (all o (x 0) (Term.lam (x 0)
    (imp o (Term.app (v 3) (v 0)) (v 1)))) (v 0))
  let B : Term := imp o (conj o (imp o (v 3) (v 0)) (imp o (v 2) (v 0))) (v 0)
  let A : Term := all o (x 0) (Term.lam (x 0) (imp o (Term.app (v 3) (v 0)) (v 1)))
  [-- j: truth
  (⟨0, [], [], tt o⟩, trueI),
  -- j + 1: conjunction introduction, each formula rewritten to truth
  (⟨0, [omega, omega], [v 1, v 0], conj o (v 1) (v 0)⟩,
    nd .conv [nd .delta, nd (.cut (Term.eq (v 1) (tt o))) [eqTrueI 0,
      nd (.cut (Term.eq (v 0) (tt o))) [eqTrueI 1,
        nd .join [nd .cong [nd (.rwHyp 2 false), nd (.rwHyp 3 false)], nd .refl]]]]),
  -- j + 2: conjunction elimination, the first component of the pair
  (⟨0, [omega, omega], [conj o (v 1) (v 0)], v 1⟩,
    nd (.cut (Term.eq (Term.pair (v 1) (v 0)) (Term.pair (tt o) (tt o))))
      [unfoldHyp (conj o (v 1) (v 0)) 0,
        nd (.convFrom (Term.fst (Term.pair (v 1) (v 0)))) [nd .fstPair,
          nd .conv [nd .trans [nd .cong [nd (.rwHyp 1 false)], nd .fstPair], trueI]]]),
  -- j + 3: conjunction elimination, the second component of the pair
  (⟨0, [omega, omega], [conj o (v 1) (v 0)], v 0⟩,
    nd (.cut (Term.eq (Term.pair (v 1) (v 0)) (Term.pair (tt o) (tt o))))
      [unfoldHyp (conj o (v 1) (v 0)) 0,
        nd (.convFrom (Term.snd (Term.pair (v 1) (v 0)))) [nd .sndPair,
          nd .conv [nd .trans [nd .cong [nd (.rwHyp 1 false)], nd .sndPair], trueI]]]),
  -- j + 4: implication elimination, the conjunction rewritten to the antecedent and to truth
  (⟨0, [omega, omega], [imp o (v 1) (v 0), v 1], v 0⟩,
    nd (.cut (Term.eq (conj o (v 1) (v 0)) (v 1))) [unfoldHyp (imp o (v 1) (v 0)) 0,
      nd (.cut (Term.eq (v 1) (tt o))) [eqTrueI 1, nd (.apply (j + 3) [] [v 0, v 1])
        [nd .conv [nd .trans [nd (.rwHyp 2 false), nd (.rwHyp 3 false)], trueI]]]]),
  -- j + 5: universal elimination, the predicate rewritten to the constant truth
  (⟨1, [x 0, exp (x 0) omega], [all o (x 0) (v 1)], Term.app (v 1) (v 0)⟩,
    nd (.cut (Term.eq (v 1) (Term.lam (x 0) (tt o)))) [unfoldHyp (all o (x 0) (v 1)) 0,
      nd .conv [nd .trans [nd .cong [nd (.rwHyp 1 false), nd .refl], nd .beta], trueI]]),
  -- j + 6: falsity elimination, universal elimination at the formula
  (⟨0, [omega], [ff o], v 0⟩,
    nd (.convFrom (Term.app (Term.lam omega (v 0)) (v 0))) [nd .beta,
      nd (.apply (j + 5) [omega] [v 0, Term.lam omega (v 0)]) [unfoldHyp (ff o) 0]]),
  -- j + 7: disjunction introduction, the first disjunct implying every consequence of both
  (⟨0, [omega, omega], [v 1], disj o (v 1) (v 0)⟩,
    nd .conv [nd .delta, allI (impI j 2 (conj o (imp o (v 2) (v 0)) (imp o (v 1) (v 0))) (v 0)
      (nd (.apply (j + 4) [] [v 0, v 2]) [nd (.apply (j + 2) [] [imp o (v 1) (v 0),
        imp o (v 2) (v 0)]) [nd (.hyp 2)], nd (.hyp 0)]))]),
  -- j + 8: disjunction introduction, the second disjunct implying every consequence of both
  (⟨0, [omega, omega], [v 0], disj o (v 1) (v 0)⟩,
    nd .conv [nd .delta, allI (impI j 2 (conj o (imp o (v 2) (v 0)) (imp o (v 1) (v 0))) (v 0)
      (nd (.apply (j + 4) [] [v 0, v 1]) [nd (.apply (j + 3) [] [imp o (v 1) (v 0),
        imp o (v 2) (v 0)]) [nd (.hyp 2)], nd (.hyp 0)]))]),
  -- j + 9: disjunction elimination, universal elimination at the consequence
  (⟨0, [omega, omega, omega], [disj o (v 2) (v 1), imp o (v 2) (v 0), imp o (v 1) (v 0)], v 0⟩,
    nd (.cut (imp o (conj o (imp o (v 2) (v 0)) (imp o (v 1) (v 0))) (v 0)))
      [nd (.convFrom (Term.app (Term.lam omega B) (v 0))) [nd .beta,
        nd (.apply (j + 5) [omega] [v 0, Term.lam omega B]) [unfoldHyp (disj o (v 2) (v 1)) 0]],
      nd (.apply (j + 4) [] [v 0, conj o (imp o (v 2) (v 0)) (imp o (v 1) (v 0))])
        [nd (.hyp 3), nd (.apply (j + 1) [] [imp o (v 1) (v 0), imp o (v 2) (v 0)])
          [nd (.hyp 1), nd (.hyp 2)]]]),
  -- j + 10: existential introduction, the instance implying every consequence of each instance
  (⟨1, [x 0, exp (x 0) omega], [Term.app (v 1) (v 0)], ex o (x 0) (v 1)⟩,
    nd .conv [nd .delta, allI (impI j 2 A (v 0)
      (nd (.apply (j + 4) [] [v 0, Term.app (v 2) (v 1)])
        [nd (.convFrom (Term.app (Term.lam (x 0) (imp o (Term.app (v 3) (v 0)) (v 1))) (v 1)))
          [nd .beta, nd (.apply (j + 5) [x 0]
            [v 1, Term.lam (x 0) (imp o (Term.app (v 3) (v 0)) (v 1))]) [nd (.hyp 2)]],
        nd (.hyp 0)]))]),
  -- j + 11: existential elimination, universal elimination at the consequence
  (⟨1, [omega, exp (x 0) omega], [ex o (x 0) (v 1),
      all o (x 0) (Term.lam (x 0) (imp o (Term.app (v 2) (v 0)) (v 1)))], v 0⟩,
    nd (.cut (imp o (all o (x 0) (Term.lam (x 0) (imp o (Term.app (v 2) (v 0)) (v 1)))) (v 0)))
      [nd (.convFrom (Term.app E' (v 0))) [nd .beta,
        nd (.apply (j + 5) [omega] [v 0, E']) [unfoldHyp (ex o (x 0) (v 1)) 0]],
      nd (.apply (j + 4) [] [v 0, all o (x 0) (Term.lam (x 0)
        (imp o (Term.app (v 2) (v 0)) (v 1)))]) [nd (.hyp 2), nd (.hyp 1)]])]

end Geb.FreeTopos.Internal.Logic

end
