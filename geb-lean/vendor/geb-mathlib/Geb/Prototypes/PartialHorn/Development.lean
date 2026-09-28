/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.PartialHorn.Basic

set_option doc.verso true in
/-!
# Developments of a partial Horn theory

A development is a list of sequents, each with a certificate. It checks when the checker
{name}`Geb.PartialHorn.check` computes each sequent's conclusion from its certificate, in the
sequent's context and under its hypotheses, with the sequents before it as the environment of
theorems; every sequent of a development that checks is then valid in every model of the
theory. A certificate cites an earlier sequent by the rule of a theorem's instance, so a fact
proved once is cited at the cost of its instance rather than proved again.

The certificates are built by one constructor for each rule of the checker. A sequent proved in
the context and under the hypotheses of the proof that cites it is cited at the variables of that
context and the hypotheses themselves ({lit}`Scope.cite`).

## Main definitions

* {lit}`Cert.hyp`, {lit}`Cert.refl`, {lit}`Cert.symm`, {lit}`Cert.trans`, {lit}`Cert.cong`,
  {lit}`Cert.strict`, {lit}`Cert.ax`, {lit}`Cert.cut`, {lit}`Cert.thm` — certificates by rule.
* {lit}`Scope`, {lit}`Scope.cite` — the context and hypotheses of a proof, and the citation of a
  sequent proved in them.
* {lit}`Development`, {lit}`checkFrom`, {lit}`checkDevelopment` — developments and their check.

## Main statements

* {lit}`checkFrom_sound` — every sequent of a development that checks is valid in every model of
  the theory in which the environment's sequents are valid.

## Tags

partial Horn logic, proof certificate, development, soundness
-/

set_option doc.verso true

@[expose] public section

namespace Geb.PartialHorn

namespace Cert

/-- The leaf of an index. -/
def leaf (i : ℕ) : Tree := RoseTree.node i []

/-- The certificate of a hypothesis, by index. -/
def hyp (i : ℕ) : Tree := RoseTree.node Rule.hyp [leaf i]

/-- The certificate that a variable, by index, is defined. -/
def refl (i : ℕ) : Tree := RoseTree.node Rule.refl [leaf i]

/-- The certificate of symmetry. -/
def symm (p : Tree) : Tree := RoseTree.node Rule.symm [p]

/-- The certificate of transitivity. -/
def trans (p q : Tree) : Tree := RoseTree.node Rule.trans [p, q]

/-- The certificate of congruence at the defined application {lit}`d` proves, from the
arguments' equations. -/
def cong (d : Tree) (ps : List Tree) : Tree := RoseTree.node Rule.cong (d :: ps)

/-- The certificate of strictness at an argument's position. -/
def strict (j : ℕ) (p : Tree) : Tree := RoseTree.node Rule.strict [leaf j, p]

/-- The certificate of an axiom's instance: its index, the terms, their definedness, and the
instances of its hypotheses. -/
def ax (j : ℕ) (ts ds hs : List Tree) : Tree := RoseTree.node Rule.ax (leaf j :: ts ++ ds ++ hs)

/-- The certificate of cut: a premise, and a certificate under it as a further hypothesis. -/
def cut (p q : Tree) : Tree := RoseTree.node Rule.cut [p, q]

/-- The certificate of a theorem's instance: its index in the environment, the terms, their
definedness, and the instances of its hypotheses. -/
def thm (j : ℕ) (ts ds hs : List Tree) : Tree := RoseTree.node Rule.thm (leaf j :: ts ++ ds ++ hs)

end Cert

/-- The context and hypotheses of a proof. -/
@[ext] structure Scope where
  /-- The sorts of the variables. -/
  ctx : List ℕ
  /-- The hypotheses. -/
  hyps : List Eqn
deriving DecidableEq

/-- The sequent of a conclusion in a scope. -/
def Scope.seq (sc : Scope) (q : Eqn) : Seq := ⟨sc.ctx, sc.hyps, q⟩

/-- The citation of theorem {lit}`j` of the environment, a sequent of the scope's context and
hypotheses, at the scope's own variables and hypotheses. -/
def Scope.cite (sc : Scope) (j : ℕ) : Tree :=
  Cert.thm j ((List.range sc.ctx.length).map var) ((List.range sc.ctx.length).map Cert.refl)
    ((List.range sc.hyps.length).map Cert.hyp)

/-- A development: sequents with their certificates, in order. -/
abbrev Development : Type := List (Seq × Tree)

/-- Whether each certificate of a development proves its sequent, with the sequents of an
environment and those before it in the development as theorems. -/
def checkFrom (T : Theory) : Development → Array Seq → Bool :=
  List.rec (fun _ ↦ true) fun e _ ih E ↦
    check T E e.2 e.1.ctx e.1.hyps == some e.1.concl && ih (E.push e.1)

/-- Whether each certificate of a development proves its sequent, with the sequents before it
as theorems. -/
def checkDevelopment (T : Theory) (D : Development) : Bool := checkFrom T D #[]

variable {T : Theory} {M : Model T.sig}

/-- Every sequent of a development that checks is valid in every model of the theory in which
the environment's sequents are valid. -/
theorem checkFrom_sound (hM : IsModel T M) (D : Development) :
    ∀ E : Array Seq, (∀ a ∈ E, a.Valid M) → checkFrom T D E = true → ∀ a ∈ D.map Prod.fst,
      a.Valid M :=
  D.rec (motive := fun D ↦ ∀ E : Array Seq, (∀ a ∈ E, a.Valid M) → checkFrom T D E = true →
      ∀ a ∈ D.map Prod.fst, a.Valid M)
    (fun _ _ _ a ha ↦ absurd ha (by simp))
    (fun e D ih E hE h ↦ by
      simp only [checkFrom, Bool.and_eq_true, beq_iff_eq] at h
      have he : e.1.Valid M := check_sound (List.prefix_refl _) hM hE e.2 _ _ _ h.1
      have hE' : ∀ a ∈ E.push e.1, a.Valid M := by
        simp only [Array.mem_push]
        rintro a (ha | rfl)
        · exact hE a ha
        · exact he
      simp only [List.map_cons, List.mem_cons]
      rintro a (rfl | ha)
      · exact he
      · exact ih _ hE' h.2 a ha)

/-- Every sequent of a development that checks is valid in every model of the theory. -/
theorem checkDevelopment_sound (hM : IsModel T M) {D : Development}
    (h : checkDevelopment T D = true) : ∀ a ∈ D.map Prod.fst, a.Valid M :=
  checkFrom_sound hM D #[] (by simp) h

end Geb.PartialHorn

end
