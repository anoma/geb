/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.QuotientPRA.FreeArity
public import Geb.Prototypes.QuotientPRA.Basic
public import Geb.Prototypes.FiniteChoice


set_option doc.verso true in
/-!
# Reflexivity and congruence from congruence witnesses

A quotient presheaf polynomial functor with free arities
({lit}`GebProto.QuotientPRA.FreeArity`) over {lit}`I × WalkingParallelPair` has
congruences when every term constructor, applied to the endpoints of witnesses
between its arguments, gives the endpoints of one witness ({lit}`HasCongruences`).
This is the property a congruence constructor of each term constructor provides, as
{lit}`GebProto.QuotientPRA.Signature.qpra` adds one. It is stated for term
constructors whose arguments are all terms ({lit}`TermArguments`), and at every
object {lit}`c` of {lit}`I × WalkingParallelPair` lying over the terms, the two
endpoint morphisms into {lit}`(c.1, one)` being {lit}`endMor`.

For finitary arities the congruences give every term a reflexivity witness, by
induction on the term ({lit}`exists_refl`), although reflexivity is not a constructor
({lit}`GebProto.QuotientPRA.Obstruction`). With reflexivity witnesses for the other
arguments, a witness between one argument of a term constructor and another term
relates the applications before and after replacing the argument
({lit}`mk_linked_update`). Replacing the arguments one at a time along an enumeration
({name}`GebProto.eqvGen_of_update`), the term constructors respect the equivalence relation
the witnesses generate ({lit}`mk_eqvGen`): arguments with equal classes give terms with equal
classes ({lit}`unit_mk_congr`).

## Main definitions

* {lit}`endMor` — the endpoint morphisms at an object over the terms.
* {lit}`TermArguments` — every argument of a term constructor is a term.
* {lit}`HasCongruences` — every term constructor has a congruence.
* {lit}`Linked` — two terms are the endpoints of a witness.

## Main statements

* {lit}`exists_refl` — every term has a reflexivity witness.
* {lit}`mk_linked_update`, {lit}`mk_eqvGen` — the term constructors respect the witnesses,
  in one argument and in all.
* {lit}`unit_eq_iff` — two terms have the same class exactly when the witnesses relate
  them by a finite zig-zag.
* {lit}`unit_mk_congr` — the term constructors respect classes.

## References

* \[FiorePittsSteenkamp2020\]
* \[AltenkirchCapriottiDijkstraKrausNordvallForsberg2018\]

## Tags

quotient inductive-inductive type, congruence, reflexivity, W-type, free arity
-/

set_option doc.verso true

@[expose] public section

open CategoryTheory Limits

namespace GebProto.QuotientPRA

universe uI vI uA uB

variable {I : Type uI} [Category.{vI} I]

/-- The endpoint morphism at an object over the terms, into the witnesses over its sort:
the source for {lit}`false`, the target for {lit}`true`. -/
def endMor : (c : I × WalkingParallelPair) → c.2 = .zero → Bool → (c ⟶ eqObj c.1)
  | (k, .zero), _, o => (𝟙 k, endHom o)
  | (_, .one), h, _ => nomatch h

variable (S : FreeArity.{uI, vI, uA, uB} (I × WalkingParallelPair))

/-- Every argument of a term constructor is a term. -/
def TermArguments : Prop := ∀ a b, (S.q a).2 = .zero → (S.gobj a b).2 = .zero

variable {S} {restr_id : S.toData.ShapeRestrId} {restr_comp : S.toData.ShapeRestrComp}
  {reindex_id : S.toData.ReindexId restr_id} {reindex_comp : S.toData.ReindexComp restr_comp}

set_option hygiene false in
/-- The functor of the free-arity instance. -/
local notation "𝐅" => S.toPresheaf restr_id restr_comp reindex_id reindex_comp

/-- The arguments of a term constructor over an object over the terms are terms. -/
theorem TermArguments.gobj (ht : TermArguments S) {a : S.A} {c : I × WalkingParallelPair}
    (hq : S.q a = c) (hc : c.2 = .zero) (b : S.Gen a) : (S.gobj a b).2 = .zero :=
  ht a b ((congrArg Prod.snd hq).trans hc)

variable (restr_id restr_comp reindex_id reindex_comp) in
/-- Every term constructor has a congruence: applied to the endpoints of witnesses
between its arguments, it gives the endpoints of one witness. -/
def HasCongruences (ht : TermArguments S) : Prop :=
  ∀ (a : S.A) {c : I × WalkingParallelPair} (hq : S.q a = c) (hc : c.2 = .zero)
    (es : (b : S.Gen a) → 𝐅.W.obj ⟨eqObj (S.gobj a b).1⟩),
    ∃ e : 𝐅.W.obj ⟨eqObj c.1⟩, ∀ o : Bool,
      𝐅.W.map (endMor c hc o).op e = PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq
        fun b ↦ 𝐅.W.map (endMor _ (ht.gobj hq hc b) o).op (es b))

/-- Two terms at an object over the terms are linked when they are the endpoints of a
witness. -/
def Linked (c : I × WalkingParallelPair) (hc : c.2 = .zero) (u u' : 𝐅.W.obj ⟨c⟩) : Prop :=
  ∃ e : 𝐅.W.obj ⟨eqObj c.1⟩,
    𝐅.W.map (endMor c hc false).op e = u ∧ 𝐅.W.map (endMor c hc true).op e = u'

/-- Two terms have the same class exactly when the witnesses relate them by the
equivalence relation they generate. -/
theorem unit_eq_iff {c : I × WalkingParallelPair} (hc : c.2 = .zero) (u u' : 𝐅.W.obj ⟨c⟩) :
    (coeqUnit 𝐅.W).app ⟨c⟩ u = (coeqUnit 𝐅.W).app ⟨c⟩ u' ↔
      Relation.EqvGen (Linked c hc) u u' := by
  obtain ⟨k, x⟩ := c
  obtain rfl : x = .zero := hc
  refine (coeqMk_eq_iff 𝐅.W u u').trans
    ⟨fun h ↦ Relation.EqvGen.mono ?_ h, fun h ↦ Relation.EqvGen.mono ?_ h⟩
  · rintro _ _ ⟨e⟩
    exact ⟨e, rfl, rfl⟩
  · rintro _ _ ⟨e, rfl, rfl⟩
    exact ⟨e⟩

variable [∀ a, FinEnum (S.Gen a)] {ht : TermArguments S}
  (hcong : HasCongruences restr_id restr_comp reindex_id reindex_comp ht)
include hcong

/-- Every term has a reflexivity witness: the congruence of its constructor at
reflexivity witnesses of its arguments. -/
theorem exists_refl {c : I × WalkingParallelPair} (hc : c.2 = .zero) (t : 𝐅.W.obj ⟨c⟩) :
    ∃ e : 𝐅.W.obj ⟨eqObj c.1⟩, ∀ o : Bool, 𝐅.W.map (endMor c hc o).op e = t := by
  revert hc
  refine FreeArity.W_induction (S := S) (motive := fun c t ↦ ∀ hc : c.2 = .zero,
      ∃ e : 𝐅.W.obj ⟨eqObj c.1⟩, ∀ o : Bool, 𝐅.W.map (endMor c hc o).op e = t)
    (fun a ts ih hc ↦ ?_) t
  obtain ⟨es, hes⟩ := exists_forall_of_finEnum fun b ↦ ih b (ht.gobj rfl hc b)
  obtain ⟨e, he⟩ := hcong a rfl hc es
  exact ⟨e, fun o ↦ (he o).trans (congrArg
    (fun ts ↦ PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a rfl ts)) (funext fun b ↦ hes b o))⟩

/-- A witness between one argument of a term constructor and another term links the
constructor's applications before and after replacing that argument: the congruence at
that witness and at reflexivity witnesses of the other arguments. -/
theorem mk_linked_update (a : S.A) {c : I × WalkingParallelPair} (hq : S.q a = c)
    (hc : c.2 = .zero) (ts : (b : S.Gen a) → 𝐅.W.obj ⟨S.gobj a b⟩) (b₀ : S.Gen a)
    {y : 𝐅.W.obj ⟨S.gobj a b₀⟩} (h : Linked _ (ht.gobj hq hc b₀) (ts b₀) y) :
    Linked c hc (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq ts))
      (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq (Function.update ts b₀ y))) := by
  obtain ⟨e, he₀, he₁⟩ := h
  obtain ⟨rs, hrs⟩ :=
    exists_forall_of_finEnum fun b ↦ exists_refl hcong (ht.gobj hq hc b) (ts b)
  obtain ⟨e', he'⟩ := hcong a hq hc (Function.update rs b₀ e)
  refine ⟨e', (he' false).trans (congrArg
      (fun ts ↦ PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq ts)) (funext fun b ↦ ?_)),
    (he' true).trans (congrArg
      (fun ts ↦ PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq ts)) (funext fun b ↦ ?_))⟩
  · by_cases hb : b = b₀
    · subst hb
      rw [Function.update_self]
      exact he₀
    · rw [Function.update_of_ne hb]
      exact hrs b false
  · by_cases hb : b = b₀
    · subst hb
      rw [Function.update_self, Function.update_self]
      exact he₁
    · rw [Function.update_of_ne hb, Function.update_of_ne hb]
      exact hrs b true

/-- The term constructors respect the generated equivalence relation: arguments related
in every place give related applications. -/
theorem mk_eqvGen (a : S.A) {c : I × WalkingParallelPair} (hq : S.q a = c)
    (hc : c.2 = .zero) {ts ts' : (b : S.Gen a) → 𝐅.W.obj ⟨S.gobj a b⟩}
    (h : ∀ b, Relation.EqvGen (Linked _ (ht.gobj hq hc b)) (ts b) (ts' b)) :
    Relation.EqvGen (Linked c hc) (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq ts))
      (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq ts')) :=
  eqvGen_of_update (fun ts ↦ PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq ts))
    (fun ts b _ hy ↦ mk_linked_update hcong a hq hc ts b hy) h

/-- The term constructors respect classes: arguments with equal classes give terms with
equal classes. -/
theorem unit_mk_congr (a : S.A) {c : I × WalkingParallelPair} (hq : S.q a = c)
    (hc : c.2 = .zero) {ts ts' : (b : S.Gen a) → 𝐅.W.obj ⟨S.gobj a b⟩}
    (h : ∀ b, (coeqUnit 𝐅.W).app ⟨S.gobj a b⟩ (ts b) = (coeqUnit 𝐅.W).app ⟨S.gobj a b⟩ (ts' b)) :
    (coeqUnit 𝐅.W).app ⟨c⟩ (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq ts)) =
      (coeqUnit 𝐅.W).app ⟨c⟩ (PresheafPFunctor.W.mk (FreeArity.freeNode 𝐅.W a hq ts')) :=
  (unit_eq_iff hc _ _).mpr
    (mk_eqvGen hcong a hq hc fun b ↦ (unit_eq_iff (ht.gobj hq hc b) _ _).mp (h b))

end GebProto.QuotientPRA
