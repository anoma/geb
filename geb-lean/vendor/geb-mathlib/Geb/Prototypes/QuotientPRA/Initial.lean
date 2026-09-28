/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.QuotientPRA.InitialModel
public import Geb.Prototypes.QuotientPRA.Signature


set_option doc.verso true in
/-!
# The quotient W-type of a finitary signature is the initial model

For a signature whose operations have finitely many arguments and a system of one-step
equations whose equations have finitely many variables, the quotient W-type of
{lit}`GebProto.QuotientPRA.Signature.qpra` is an algebra of the signature
({lit}`opQ`) that satisfies the equations ({lit}`satisfies_opQ`), and the eliminator
{lit}`GebProto.QuotientPRA.Signature.lift` into any algebra satisfying the equations is
the unique morphism of algebras out of it ({lit}`lift_opQ`, {lit}`eq_lift`). It is
therefore the initial algebra satisfying the equations: the quotient inductive type of
the signature and equations.

This is the one-sorted instance of {lit}`GebProto.QuotientPRA.InitialModel`. The
operations take terms as arguments ({lit}`termArguments`), and the congruence
{lit}`qpra` adds for each operation gives the congruence property
({lit}`hasCongruences`), so {lit}`opQ` is the algebra
{lit}`GebProto.QuotientPRA.algTerm` of the quotient at an operation.

## Main definitions

* {lit}`Term`, {lit}`Wit`, {lit}`Cls` — the terms, the witnesses, and the classes of
  terms.
* {lit}`op` — the term an operation builds.
* {lit}`opQ` — the operations on classes.

## Main statements

* {lit}`term_induction` — induction on terms.
* {lit}`termArguments`, {lit}`hasCongruences` — the operations take terms and have
  congruences.
* {lit}`opQ_mk` — the operations on classes of terms.
* {lit}`satisfies_opQ` — the classes satisfy the equations.
* {lit}`lift_opQ`, {lit}`eq_lift` — the eliminator is the unique morphism of algebras
  out of the classes.

## References

* \[FiorePittsSteenkamp2020\]
* \[AltenkirchCapriottiDijkstraKrausNordvallForsberg2018\]

## Tags

quotient inductive type, initial algebra, W-type, congruence, equational theory
-/

set_option doc.verso true

@[expose] public section

open CategoryTheory Limits

namespace GebProto.QuotientPRA.Signature

universe uA uB

variable {P : PFunctor.{uA, uB}} {eqns : Equations P}

variable (P eqns) in
/-- The terms of the W-type. -/
abbrev Term : Type (max uA uB) := (qpra P eqns).W.obj ⟨objOf .zero⟩

variable (P eqns) in
/-- The witnesses of the W-type. -/
abbrev Wit : Type (max uA uB) := (qpra P eqns).W.obj ⟨objOf .one⟩

/-- The term an operation builds from terms. -/
def op (a : P.A) (ts : P.B a → Term P eqns) : Term P eqns :=
  PresheafPFunctor.W.mk (freeNode _ (.inl a) ts)

/-- Induction on terms: a property of every term follows from its preservation by the
operations. -/
theorem term_induction {motive : Term P eqns → Prop}
    (step : ∀ (a : P.A) (ts : P.B a → Term P eqns), (∀ b, motive (ts b)) → motive (op a ts))
    (t : Term P eqns) : motive t :=
  FreeArity.W_induction (S := freeArity P eqns)
    (motive := fun c ↦ match c with
      | (_, .zero) => motive
      | (_, .one) => fun _ ↦ True)
    (fun s ts ih ↦ by
      rcases s with a | a | ⟨e, o⟩
      · exact step a ts ih
      · trivial
      · trivial)
    t

variable (P eqns) in
/-- The arguments of the operations are terms. -/
theorem termArguments : TermArguments (freeArity P eqns) := by
  intro s b hs
  rcases s with a | a | ⟨e, o⟩
  · rfl
  · exact nomatch hs
  · exact nomatch hs

variable (P eqns) in
/-- Every operation has its congruence: an endpoint of the congruence's witness is the
operation on the same endpoints of the witnesses between the arguments. -/
theorem hasCongruences : HasCongruences (restr_id P eqns) (restr_comp P eqns)
    (reindex_id P eqns) (reindex_comp P eqns) (termArguments P eqns) := by
  intro s c hq hc es
  subst hq
  rcases s with a | a | ⟨e, o⟩
  · exact ⟨PresheafPFunctor.W.mk (freeNode _ (.inr (.inl a)) es),
      fun o ↦ endpoint_mk_freeNode_cong o a es⟩
  · exact nomatch hc
  · exact nomatch hc

variable (P eqns) in
/-- The classes of terms: the quotient W-type's value at the one object. -/
abbrev Cls : Type (max uA uB) := (quotient (qpra P eqns)).obj ⟨⟨⟨⟩⟩⟩

section Finitary

variable [∀ a, FinEnum (P.B a)] [∀ e, FinEnum (eqns.V e)]

/-- The arguments of every shape are finite: those of an operation and of its
congruence are the operation's, and those of an equation its variables. -/
instance instFinEnumGen (s : (freeArity P eqns).A) : FinEnum ((freeArity P eqns).Gen s) :=
  match s with
  | .inl a => inferInstanceAs (FinEnum (P.B a))
  | .inr (.inl a) => inferInstanceAs (FinEnum (P.B a))
  | .inr (.inr p) => inferInstanceAs (FinEnum (eqns.V p.1))

/-- The operation {lit}`a` on classes: the algebra of the quotient at the operation,
applying it to representatives. -/
def opQ (a : P.A) (f : P.B a → Cls P eqns) : Cls P eqns :=
  algTerm (hasCongruences P eqns) (.inl a) rfl rfl f

/-- The operation on the classes of terms is the class of the operation on the terms. -/
theorem opQ_mk (a : P.A) (ts : P.B a → Term P eqns) :
    opQ a (fun b ↦ quotientMk (qpra P eqns) (ts b)) = quotientMk (qpra P eqns) (op a ts) :=
  algTerm_unit (hasCongruences P eqns) (.inl a) rfl rfl ts

omit [∀ a, FinEnum (P.B a)] [∀ e, FinEnum (eqns.V e)] in
/-- Every finite family of classes is the family of classes of a family of terms. -/
theorem exists_mk {ι : Type uB} [FinEnum ι] (f : ι → Cls P eqns) :
    ∃ ts : ι → Term P eqns, ∀ i, quotientMk (qpra P eqns) (ts i) = f i :=
  exists_forall_of_finEnum fun i ↦ Quot.exists_rep (f i)

variable {Y : Type (max uA uB)} {S : P.Obj Y → Y}

/-- The eliminator is a morphism of algebras out of the classes. -/
theorem lift_opQ (sat : Satisfies (eqns := eqns) S) (a : P.A) (f : P.B a → Cls P eqns) :
    (lift S sat).app ⟨⟨⟨⟩⟩⟩ (opQ a f) = S ⟨a, fun b ↦ (lift S sat).app ⟨⟨⟨⟩⟩⟩ (f b)⟩ := by
  obtain ⟨ts, hts⟩ := exists_mk f
  obtain rfl : f = fun b ↦ quotientMk (qpra P eqns) (ts b) := (funext hts).symm
  rw [opQ_mk]
  exact lift_intro S sat a ts

/-- The eliminator is the only morphism of algebras out of the classes: a morphism of
algebras agrees with it on the class of every term, by induction on the term. -/
theorem eq_lift (sat : Satisfies (eqns := eqns) S) (h : Cls P eqns → Y)
    (hh : ∀ a f, h (opQ a f) = S ⟨a, fun b ↦ h (f b)⟩) (q : Cls P eqns) :
    h q = (lift S sat).app ⟨⟨⟨⟩⟩⟩ q :=
  Quot.ind (β := fun q ↦ h q = (lift S sat).app ⟨⟨⟨⟩⟩⟩ q)
    (term_induction fun a ts ih ↦ by
      change h (quotientMk (qpra P eqns) (op a ts)) =
        (lift S sat).app ⟨⟨⟨⟩⟩⟩ (quotientMk (qpra P eqns) (op a ts))
      rw [← opQ_mk, hh, lift_opQ sat]
      exact congrArg S (Sigma.ext rfl (heq_of_eq (funext ih)))) q

/-- The classes satisfy the equations: an equation's witness at representatives of the
variables relates its two sides. -/
theorem satisfies_opQ : Satisfies (eqns := eqns) fun x : P.Obj (Cls P eqns) ↦ opQ x.1 x.2 := by
  intro e ρ
  obtain ⟨ts, hts⟩ := exists_mk ρ
  obtain rfl : ρ = fun v ↦ quotientMk (qpra P eqns) (ts v) := (funext hts).symm
  change opQ (eqns.lhs e).1 (fun b ↦ quotientMk (qpra P eqns) (ts ((eqns.lhs e).2 b))) =
    opQ (eqns.rhs e).1 (fun b ↦ quotientMk (qpra P eqns) (ts ((eqns.rhs e).2 b)))
  rw [opQ_mk, opQ_mk]
  exact (congrArg (quotientMk (qpra P eqns)) (src_mk_freeNode_eqn e false ts)).symm.trans
    ((quotientMk_src (qpra P eqns) _).trans
      (congrArg (quotientMk (qpra P eqns)) (tgt_mk_freeNode_eqn e false ts)))

end Finitary

end GebProto.QuotientPRA.Signature
