/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Internal.Logic
public import Geb.Prototypes.FreeTopos.Internal.RepresentEq

set_option doc.verso true in
/-!
# The connectives represent Lean's

The connectives of the internal language are definitions built from equations
({name}`Geb.FreeTopos.Internal.Logic.defs`). In the topos of types and functional relations,
where a proposition is represented by itself, each represents the connective of Lean's
propositions: an equation represents an equality ({name}`Geb.FreeTopos.Internal.repC_eq`), and
the equality a connective's body states is equivalent to the connective.

## Main definitions

* {lit}`HasLogic` — the constants have the connectives' definitions from an index.
* {lit}`Globals.hasLogic` — its decision.
* {lit}`Connectives` — constants with the connectives' definitions that compile to well-formed
  definitions.

## Main statements

* {lit}`represents_tt`, {lit}`represents_conj`, {lit}`represents_imp`, {lit}`represents_all`,
  {lit}`represents_ff`, {lit}`represents_ex` — the arrows of truth, conjunction, implication,
  universal quantification, falsity and existential quantification represent Lean's.
* {lit}`repC_tt`, {lit}`repC_ff`, {lit}`repC_conj`, {lit}`repC_imp`, {lit}`repC_all`,
  {lit}`repC_ex` — so do their applications in a context.
* {lit}`Connectives.tt`, {lit}`Connectives.ff`, {lit}`Connectives.conj`,
  {lit}`Connectives.imp`, {lit}`Connectives.all`, {lit}`Connectives.ex` — the same, over
  constants with the connectives' definitions.
* {lit}`repC_imps` — the implication of a formula by a list of formulas in turn.
* {lit}`holds_of_represents` — a formula that is true, unfolded, in the topos of types and
  functional relations represents a function that holds at each represented value.

## Tags

internal language, logical relation, representation, connectives
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree)
open Sorts
open scoped FinEnum

variable {G : Globals} {n : ℕ} {ds : List PartialHorn.Defn} {ρ : List relTopos.model.Val}
  {S A : Type} {o : ℕ}

/-- The constants have the connectives' definitions from the index {lit}`o`. -/
def HasLogic (G : Globals) (o : ℕ) : Prop :=
  ∀ (i : ℕ) (d : Defn), (Logic.defs o)[i]? = some d → G.defs[o + i]? = some (.language d)

/-- Whether the constants have the connectives' definitions from the index {lit}`o`. -/
def Globals.hasLogic (G : Globals) (o : ℕ) : Bool :=
  (Logic.defs o).zipIdx.all fun p ↦ match G.defs[o + p.2]? with
    | some (.language d) => decide (d.arity = p.1.arity ∧ d.params = p.1.params ∧
        d.type = p.1.type ∧ d.body = p.1.body)
    | _ => false

/-- The constants the decision accepts have the connectives' definitions. -/
theorem Globals.hasLogic_sound (h : G.hasLogic o = true) : HasLogic G o := by
  intro i d hd
  have hp := List.all_eq_true.mp h (d, i) (List.mem_zipIdx_iff_getElem?.mpr hd)
  split at hp
  · next d' hd' =>
    simp only [decide_eq_true_eq] at hp
    have e : d' = d := by
      cases d'
      cases d
      simp only at hp
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hp
      rfl
    exact e ▸ hd'
  · exact (Bool.false_ne_true hp).elim

/-- The terminal object's value, unfolded. -/
theorem objVal_one : ObjVal ρ (unfoldTerm sig ds one) Unit := by
  simp_unfold
  exact eval_one

/-- The subobject classifier's value, unfolded. -/
theorem objVal_omega : ObjVal ρ (unfoldTerm sig ds omega) Prop := by
  simp (disch := decide) only [omega, unfold_op', List.map_nil]
  exact eval_omega

/-- The value of a product of types, unfolded, is the product of their values. -/
theorem objVal_prod {a b : Tree} {B C : Type} (ha : ObjVal ρ (unfoldTerm sig ds a) B)
    (hb : ObjVal ρ (unfoldTerm sig ds b) C) : ObjVal ρ (unfoldTerm sig ds (prod a b)) (B × C) := by
  simp (disch := decide) only [prod, unfold_op', List.map_cons, List.map_nil]
  exact eval_prod ha hb

/-- The value of a function type, unfolded, is the functional relations between the values. -/
theorem objVal_exp {a b : Tree} {B C : Type} (ha : ObjVal ρ (unfoldTerm sig ds a) B)
    (hb : ObjVal ρ (unfoldTerm sig ds b) C) :
    ObjVal ρ (unfoldTerm sig ds (exp a b)) (FunRel B C) := by
  simp (disch := decide) only [exp, unfold_op', List.map_cons, List.map_nil]
  exact eval_exp ha hb

/-- The value of a list type, unfolded, is the lists of the value. -/
theorem objVal_list {a : Tree} {B : Type} (ha : ObjVal ρ (unfoldTerm sig ds a) B) :
    ObjVal ρ (unfoldTerm sig ds (list a)) (List B) := by
  simp (disch := decide) only [list, unfold_op', List.map_cons, List.map_nil]
  exact eval_list ha

/-- The subobject classifier's type has no object variable. -/
theorem subst_omega (θ : List Tree) : PartialHorn.subst θ omega = omega := by
  simp only [omega, subst_op, List.map_nil]

/-- Truth's arrow represents the true proposition. -/
theorem represents_tt (hF : compileDefs G = some ds) (hlog : HasLogic G o) {fk : Tree}
    (hdk : ds[o]? = some ⟨List.replicate 0 obj, arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) Rep.unit Rep.prop fun _ ↦ True :=
  rep_def (τ' := []) hF (hlog 0 _ rfl) (Fk := fun _ ↦ () = ())
    (repC_eq (repC_star objVal_one Rep.unit) (repC_star objVal_one Rep.unit) objVal_one
      (fun _ _ _ _ _ ↦ rfl) (fun _ _ _ _ _ ↦ rfl))
    (fun _ ↦ eq_self ()) hdk

/-- The representation of pairs of propositions relates each pair to one pair, in each
direction. -/
theorem prop_prod_unique :
    (∀ (t : Prop × Prop) (x y : Prop × Prop), Rep.prod Rep.prop Rep.prop t x →
      Rep.prod Rep.prop Rep.prop t y → x = y) ∧
    ∀ (t t' : Prop × Prop) (x : Prop × Prop), Rep.prod Rep.prop Rep.prop t x →
      Rep.prod Rep.prop Rep.prop t' x → t = t' :=
  ⟨fun _ _ _ h h' ↦ Prod.ext (h.1.symm.trans h'.1) (h.2.symm.trans h'.2),
    fun _ _ _ h h' ↦ Prod.ext (h.1.trans h'.1.symm) (h.2.trans h'.2.symm)⟩

/-- The definitions before a later index are those of the constants. -/
theorem defs_take {i k : ℕ} (h : i < k) :
    ({ G with defs := G.defs.take k } : Globals).defs[i]? = G.defs[i]? := by
  simp [h]

/-- The value of the type of pairs of propositions, unfolded. -/
theorem objVal_prod_omega :
    ObjVal ρ (unfoldTerm sig ds (prod omega omega)) (Prop × Prop) := by
  simp (disch := decide) only [prod, omega, unfold_op', List.map_cons, List.map_nil]
  exact eval_prod eval_omega eval_omega

/-- The value of the product of a context of two propositions, unfolded. -/
theorem objVal_ctx_omega :
    ObjVal ρ (unfoldTerm sig ds (ctxObj [omega, omega])) (Prop × Prop) := by
  rw [ctxObj_cons_cons, ctxObj_single]
  exact objVal_prod_omega

/-- Truth, applied in a context, represents the function to the true proposition, where the
constants have its definition and its arrow represents the true proposition. -/
theorem repC_tt (hbase : G.base = sig.length)
    (hk : G.defs[o]? = some (.language ⟨0, [], omega, Term.eq Term.star Term.star⟩))
    (hwf : PartialHorn.DefnsWF sig ds) {ft : Tree}
    (hdt : ds[o]? = some ⟨List.replicate 0 obj, arr, ft⟩)
    (hft : Represents [] (unfoldTerm sig ds ft) Rep.unit Rep.prop fun _ ↦ True) {X : Tree}
    {e : List (Tree × Tree)} (hX : ObjVal ρ (unfoldTerm sig ds X) A) (R : S → A → Prop) :
    RepC G n ds ρ (Logic.tt o) X e omega R Rep.prop fun _ ↦ True :=
  repC_call₀ (d := ⟨0, [], omega, Term.eq Term.star Term.star⟩) hbase hk hwf hdt rfl rfl
    (subst_omega []) hX hft

/-- The pair of two propositions of a pair represents the pair. -/
theorem repC_pair_vars :
    RepC G 0 ds [] (Term.pair (Term.var 1) (Term.var 0)) (ctxObj [omega, omega])
      (stdEnv [omega, omega]) (prod omega omega) (Rep.prod Rep.prop Rep.prop)
      (Rep.prod Rep.prop Rep.prop) fun p : Prop × Prop ↦ (p.1, p.2) :=
  have he := envRep_std₂ (ds := ds) (ρ := []) (p₁ := omega) (p₂ := omega) objVal_omega
    objVal_omega Rep.prop Rep.prop
  repC_pair (repC_var he rfl) (repC_var he rfl)

/-- Conjunction's arrow represents the conjunction of a pair of propositions. -/
theorem represents_conj (hbase : G.base = sig.length) (hF : compileDefs G = some ds)
    (hwf : PartialHorn.DefnsWF sig ds) (hlog : HasLogic G o) {ft fk : Tree}
    (hdt : ds[o]? = some ⟨List.replicate 0 obj, arr, ft⟩)
    (hdk : ds[o + 1]? = some ⟨List.replicate 0 obj, arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) (Rep.prod Rep.prop Rep.prop) Rep.prop
      fun p : Prop × Prop ↦ p.1 ∧ p.2 := by
  have hk : G.defs[o + 1]? = some (.language ⟨0, [omega, omega], omega,
      Term.eq (Term.pair (Term.var 1) (Term.var 0)) (Term.pair (Logic.tt o) (Logic.tt o))⟩) :=
    hlog 1 _ rfl
  have hk₀ : ({ G with defs := G.defs.take (o + 1) } : Globals).defs[o]? =
      some (.language ⟨0, [], omega, Term.eq Term.star Term.star⟩) := by
    rw [defs_take (Nat.lt_succ_self o)]
    exact hlog 0 _ rfl
  have hft := represents_tt hF hlog hdt
  have htt : RepC { G with defs := G.defs.take (o + 1) } 0 ds [] (Logic.tt o)
      (ctxObj [omega, omega]) (stdEnv [omega, omega]) omega (Rep.prod Rep.prop Rep.prop)
      Rep.prop fun _ ↦ True :=
    repC_tt (G := { G with defs := G.defs.take (o + 1) }) (n := 0) (ρ := []) hbase hk₀ hwf hdt
      hft objVal_ctx_omega (Rep.prod Rep.prop Rep.prop)
  have hb : RepC { G with defs := G.defs.take (o + 1) } 0 ds []
      (Term.eq (Term.pair (Term.var 1) (Term.var 0)) (Term.pair (Logic.tt o) (Logic.tt o)))
      (ctxObj [omega, omega]) (stdEnv [omega, omega]) omega (Rep.prod Rep.prop Rep.prop)
      Rep.prop fun p : Prop × Prop ↦ (p.1, p.2) = (True, True) :=
    repC_eq repC_pair_vars (repC_pair htt htt) objVal_prod_omega prop_prod_unique.1
      prop_prod_unique.2
  exact rep_def (τ' := []) hF hk hb (fun p ↦ propext
    ⟨fun h ↦ ⟨of_eq_true (congrArg Prod.fst h), of_eq_true (congrArg Prod.snd h)⟩,
      fun h ↦ Prod.ext (eq_true h.1) (eq_true h.2)⟩) hdk

/-- The representation of the propositions relates each to one, in each direction. -/
theorem prop_unique :
    (∀ t x y : Prop, Rep.prop t x → Rep.prop t y → x = y) ∧
    ∀ t t' x : Prop, Rep.prop t x → Rep.prop t' x → t = t' :=
  ⟨fun _ _ _ h h' ↦ h.symm.trans h', fun _ _ _ h h' ↦ h.trans h'.symm⟩

/-- A conjunction in a context represents the conjunction of the functions its formulas
represent, where the constants have conjunction's definition and its arrow represents the
conjunction. -/
theorem repC_conj (hbase : G.base = sig.length)
    (hk : G.defs[o + 1]? = some (.language ⟨0, [omega, omega], omega,
      Term.eq (Term.pair (Term.var 1) (Term.var 0)) (Term.pair (Logic.tt o) (Logic.tt o))⟩))
    (hwf : PartialHorn.DefnsWF sig ds) {fk : Tree}
    (hdk : ds[o + 1]? = some ⟨List.replicate 0 obj, arr, fk⟩)
    (hfk : Represents [] (unfoldTerm sig ds fk) (Rep.prod Rep.prop Rep.prop) Rep.prop
      fun p : Prop × Prop ↦ p.1 ∧ p.2) {X : Tree} {e : List (Tree × Tree)} {p q : Term}
    {R : S → A → Prop} {P Q : S → Prop} (hp : RepC G n ds ρ p X e omega R Rep.prop P)
    (hq : RepC G n ds ρ q X e omega R Rep.prop Q) :
    RepC G n ds ρ (Logic.conj o p q) X e omega R Rep.prop fun s ↦ P s ∧ Q s :=
  repC_call₂ (θ := []) (τ' := []) (d := ⟨0, [omega, omega], omega,
      Term.eq (Term.pair (Term.var 1) (Term.var 0)) (Term.pair (Logic.tt o) (Logic.tt o))⟩)
    hbase hk hwf hdk rfl rfl (fun _ h ↦ nomatch h) .nil (subst_omega [])
    (by simp only [List.map_cons, List.map_nil, subst_omega]) hfk hp hq

/-- Implication's arrow represents the implication of a pair of propositions. -/
theorem represents_imp (hbase : G.base = sig.length) (hF : compileDefs G = some ds)
    (hwf : PartialHorn.DefnsWF sig ds) (hlog : HasLogic G o) {ft fc fk : Tree}
    (hdt : ds[o]? = some ⟨List.replicate 0 obj, arr, ft⟩)
    (hdc : ds[o + 1]? = some ⟨List.replicate 0 obj, arr, fc⟩)
    (hdk : ds[o + 2]? = some ⟨List.replicate 0 obj, arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) (Rep.prod Rep.prop Rep.prop) Rep.prop
      fun p : Prop × Prop ↦ p.1 → p.2 := by
  have hk : G.defs[o + 2]? = some (.language ⟨0, [omega, omega], omega,
      Term.eq (Logic.conj o (Term.var 1) (Term.var 0)) (Term.var 1)⟩) :=
    hlog 2 _ rfl
  have hk₁ : ({ G with defs := G.defs.take (o + 2) } : Globals).defs[o + 1]? =
      some (.language ⟨0, [omega, omega], omega,
        Term.eq (Term.pair (Term.var 1) (Term.var 0))
          (Term.pair (Logic.tt o) (Logic.tt o))⟩) := by
    rw [defs_take (Nat.lt_succ_self (o + 1))]
    exact hlog 1 _ rfl
  have he := envRep_std₂ (ds := ds) (ρ := []) (p₁ := omega) (p₂ := omega) objVal_omega
    objVal_omega Rep.prop Rep.prop
  have hc : RepC { G with defs := G.defs.take (o + 2) } 0 ds []
      (Logic.conj o (Term.var 1) (Term.var 0)) (ctxObj [omega, omega]) (stdEnv [omega, omega])
      omega (Rep.prod Rep.prop Rep.prop) Rep.prop fun p : Prop × Prop ↦ p.1 ∧ p.2 :=
    repC_conj (G := { G with defs := G.defs.take (o + 2) }) (n := 0) (ρ := []) hbase hk₁ hwf
      hdc (represents_conj hbase hF hwf hlog hdt hdc) (repC_var he rfl) (repC_var he rfl)
  have hb : RepC { G with defs := G.defs.take (o + 2) } 0 ds []
      (Term.eq (Logic.conj o (Term.var 1) (Term.var 0)) (Term.var 1)) (ctxObj [omega, omega])
      (stdEnv [omega, omega]) omega (Rep.prod Rep.prop Rep.prop) Rep.prop
      fun p : Prop × Prop ↦ (p.1 ∧ p.2) = p.1 :=
    repC_eq hc (repC_var he rfl) objVal_omega prop_unique.1 prop_unique.2
  exact rep_def (τ' := []) hF hk hb (fun p ↦ propext
    ⟨fun h hp ↦ (h.symm ▸ hp : p.1 ∧ p.2).2,
      fun h ↦ propext ⟨And.left, fun hp ↦ ⟨hp, h hp⟩⟩⟩) hdk

/-- An implication in a context represents the implication of the functions its formulas
represent, where the constants have implication's definition and its arrow represents the
implication. -/
theorem repC_imp (hbase : G.base = sig.length)
    (hk : G.defs[o + 2]? = some (.language ⟨0, [omega, omega], omega,
      Term.eq (Logic.conj o (Term.var 1) (Term.var 0)) (Term.var 1)⟩))
    (hwf : PartialHorn.DefnsWF sig ds) {fk : Tree}
    (hdk : ds[o + 2]? = some ⟨List.replicate 0 obj, arr, fk⟩)
    (hfk : Represents [] (unfoldTerm sig ds fk) (Rep.prod Rep.prop Rep.prop) Rep.prop
      fun p : Prop × Prop ↦ p.1 → p.2) {X : Tree} {e : List (Tree × Tree)} {p q : Term}
    {R : S → A → Prop} {P Q : S → Prop} (hp : RepC G n ds ρ p X e omega R Rep.prop P)
    (hq : RepC G n ds ρ q X e omega R Rep.prop Q) :
    RepC G n ds ρ (Logic.imp o p q) X e omega R Rep.prop fun s ↦ P s → Q s :=
  repC_call₂ (θ := []) (τ' := []) (d := ⟨0, [omega, omega], omega,
      Term.eq (Logic.conj o (Term.var 1) (Term.var 0)) (Term.var 1)⟩)
    hbase hk hwf hdk rfl rfl (fun _ h ↦ nomatch h) .nil (subst_omega [])
    (by simp only [List.map_cons, List.map_nil, subst_omega]) hfk hp hq

/-- The implication of a formula by a list of formulas in turn represents the implication of
the function it represents by those the formulas represent, in turn: by recursion on the
formulas ({name}`repC_imp`). -/
theorem repC_imps (hbase : G.base = sig.length)
    (hk : G.defs[o + 2]? = some (.language ⟨0, [omega, omega], omega,
      Term.eq (Logic.conj o (Term.var 1) (Term.var 0)) (Term.var 1)⟩))
    (hwf : PartialHorn.DefnsWF sig ds) {fk : Tree}
    (hdk : ds[o + 2]? = some ⟨List.replicate 0 obj, arr, fk⟩)
    (hfk : Represents [] (unfoldTerm sig ds fk) (Rep.prod Rep.prop Rep.prop) Rep.prop
      fun p : Prop × Prop ↦ p.1 → p.2) {X : Tree} {e : List (Tree × Tree)} {c : Term}
    {R : S → A → Prop} {C : S → Prop} (hc : RepC G n ds ρ c X e omega R Rep.prop C)
    {hs : List Term} {Hs : List (S → Prop)}
    (h : List.Forall₂ (fun p P ↦ RepC G n ds ρ p X e omega R Rep.prop P) hs Hs) :
    RepC G n ds ρ (hs.foldr (Logic.imp o) c) X e omega R Rep.prop
      fun s ↦ Hs.foldr (fun (P : S → Prop) (acc : Prop) ↦ P s → acc) (C s) :=
  h.rec (motive := fun (hs : List Term) (Hs : List (S → Prop)) _ ↦
      RepC G n ds ρ (hs.foldr (Logic.imp o) c) X e omega R Rep.prop
        fun s ↦ Hs.foldr (fun (P : S → Prop) (acc : Prop) ↦ P s → acc) (C s))
    hc fun hp _ ih ↦ repC_imp hbase hk hwf hdk hfk hp ih

/-- The representation of predicates by functional relations into the propositions relates
each to one, in each direction, where the representation of their domain is total in each
direction. -/
theorem pred_unique {Sx Ty : Type} {Rx : Sx → Ty → Prop} (hs : ∀ s, ∃ a, Rx s a)
    (ha : ∀ a, ∃ s, Rx s a) :
    (∀ (F : Sx → Prop) (φ ψ : FunRel Ty Prop), Rep.exp Rx Rep.prop F φ →
      Rep.exp Rx Rep.prop F ψ → φ = ψ) ∧
    ∀ (F F' : Sx → Prop) (φ : FunRel Ty Prop), Rep.exp Rx Rep.prop F φ →
      Rep.exp Rx Rep.prop F' φ → F = F' := by
  refine ⟨fun F φ ψ h h' ↦ FunRel.ext_of_le fun a b hab ↦ ?_, fun F F' φ h h' ↦ funext fun s ↦ ?_⟩
  · obtain ⟨s, hsa⟩ := ha a
    obtain ⟨b', hb', -⟩ := ψ.functional a
    have e : b = b' := (h s a hsa b hab).symm.trans (h' s a hsa b' hb')
    exact e ▸ hb'
  · obtain ⟨a, hsa⟩ := hs s
    obtain ⟨b, hb, -⟩ := φ.functional a
    exact (h s a hsa b hb).trans (h' s a hsa b hb).symm

/-- Universal quantification's arrow, at a type, represents the universal quantification of a
predicate, where the representation of the type is total in each direction. -/
theorem represents_all (hbase : G.base = sig.length) (hF : compileDefs G = some ds)
    (hwf : PartialHorn.DefnsWF sig ds) (hlog : HasLogic G o) {Sx Ty : Type}
    {Rx : Sx → Ty → Prop} (hs : ∀ s, ∃ a, Rx s a) (ha : ∀ a, ∃ s, Rx s a) {ft fk : Tree}
    (hdt : ds[o]? = some ⟨List.replicate 0 obj, arr, ft⟩)
    (hdk : ds[o + 3]? = some ⟨List.replicate 1 obj, arr, fk⟩) :
    Represents (objs [Ty]) (unfoldTerm sig ds fk) (Rep.exp Rx Rep.prop) Rep.prop
      fun P : Sx → Prop ↦ ∀ x, P x := by
  have hk : G.defs[o + 3]? = some (.language ⟨1, [exp (x 0) omega], omega,
      Term.eq (Term.var 0) (Term.lam (x 0) (Logic.tt o))⟩) :=
    hlog 3 _ rfl
  have hk₀ : ({ G with defs := G.defs.take (o + 3) } : Globals).defs[o]? =
      some (.language ⟨0, [], omega, Term.eq Term.star Term.star⟩) := by
    rw [defs_take (by omega)]
    exact hlog 0 _ rfl
  have hx : ObjVal (objs [Ty]) (unfoldTerm sig ds (x 0)) Ty := by
    rw [unfold_x]
    exact objVal_x0
  have hP : ObjVal (objs [Ty]) (unfoldTerm sig ds (exp (x 0) omega)) (FunRel Ty Prop) := by
    simp (disch := decide) only [exp, omega, unfold_op', unfold_x, List.map_cons, List.map_nil]
    exact eval_exp objVal_x0 eval_omega
  have hX : ObjVal (objs [Ty]) (unfoldTerm sig ds (ctxObj [exp (x 0) omega]))
      (FunRel Ty Prop) := by
    rw [ctxObj_single]
    exact hP
  have hXa : ObjVal (objs [Ty]) (unfoldTerm sig ds (prod (ctxObj [exp (x 0) omega]) (x 0)))
      (FunRel Ty Prop × Ty) := by
    rw [ctxObj_single]
    simp (disch := decide) only [prod, exp, omega, unfold_op', unfold_x, List.map_cons,
      List.map_nil]
    exact eval_prod (eval_exp objVal_x0 eval_omega) objVal_x0
  have he := envRep_std₁ (ds := ds) hP (Rep.exp Rx Rep.prop)
  have htt : RepC { G with defs := G.defs.take (o + 3) } 1 ds (objs [Ty]) (Logic.tt o)
      (prod (ctxObj [exp (x 0) omega]) (x 0))
      (extEnv (ctxObj [exp (x 0) omega]) (x 0) (stdEnv [exp (x 0) omega])) omega
      (Rep.prod (Rep.exp Rx Rep.prop) Rx) Rep.prop fun _ ↦ True :=
    repC_tt (G := { G with defs := G.defs.take (o + 3) }) (n := 1) (ρ := objs [Ty]) hbase hk₀
      hwf hdt (represents_tt hF hlog hdt) hXa (Rep.prod (Rep.exp Rx Rep.prop) Rx)
  have hlam : RepC { G with defs := G.defs.take (o + 3) } 1 ds (objs [Ty])
      (Term.lam (x 0) (Logic.tt o)) (ctxObj [exp (x 0) omega]) (stdEnv [exp (x 0) omega])
      (exp (x 0) omega) (Rep.exp Rx Rep.prop) (Rep.exp Rx Rep.prop) fun _ _ ↦ True :=
    repC_lam (G := { G with defs := G.defs.take (o + 3) }) (isTy_x (by decide)) hX hx htt
  have hb : RepC { G with defs := G.defs.take (o + 3) } 1 ds (objs [Ty])
      (Term.eq (Term.var 0) (Term.lam (x 0) (Logic.tt o))) (ctxObj [exp (x 0) omega])
      (stdEnv [exp (x 0) omega]) omega (Rep.exp Rx Rep.prop) Rep.prop
      fun P : Sx → Prop ↦ P = fun _ ↦ True :=
    repC_eq (repC_var he rfl) hlam hP (pred_unique hs ha).1 (pred_unique hs ha).2
  exact rep_def (τ' := [Ty]) hF hk hb (fun P ↦ propext
    ⟨fun h x ↦ h ▸ trivial, fun h ↦ funext fun x ↦ eq_true (h x)⟩) hdk

/-- A universal quantification in a context represents the universal quantification of the
function its predicate represents, where the constants have the quantification's definition,
its arrow represents the quantification at the type's value, and the type is one of the
theory's signature. -/
theorem repC_all (hbase : G.base = sig.length)
    (hk : G.defs[o + 3]? = some (.language ⟨1, [exp (x 0) omega], omega,
      Term.eq (Term.var 0) (Term.lam (x 0) (Logic.tt o))⟩))
    (hwf : PartialHorn.DefnsWF sig ds) {fk : Tree}
    (hdk : ds[o + 3]? = some ⟨List.replicate 1 obj, arr, fk⟩) {Sx Ty : Type}
    {Rx : Sx → Ty → Prop}
    (hfk : Represents (objs [Ty]) (unfoldTerm sig ds fk) (Rep.exp Rx Rep.prop) Rep.prop
      fun P : Sx → Prop ↦ ∀ x, P x) {a : Tree} (hta : IsTy G n a = true)
    (hops : PartialHorn.OpsBelow sig.length a = true) (hva : ObjVal ρ a Ty) {X : Tree}
    {e : List (Tree × Tree)} {Pr : Term} {R : S → A → Prop} {F : S → Sx → Prop}
    (hP : RepC G n ds ρ Pr X e (exp a omega) R (Rep.exp Rx Rep.prop) F) :
    RepC G n ds ρ (Logic.all o a Pr) X e omega R Rep.prop fun s ↦ ∀ x, F s x :=
  repC_call₁ (θ := [a]) (τ' := [Ty]) (d := ⟨1, [exp (x 0) omega], omega,
      Term.eq (Term.var 0) (Term.lam (x 0) (Logic.tt o))⟩)
    hbase hk hwf hdk rfl (by simp [hta]) (by simpa using hops) (.cons hva .nil)
    (subst_omega [a])
    (by simp only [List.map_cons, List.map_nil, exp, omega, subst_op, subst_x,
      List.getElem?_cons_zero, Option.getD_some]) hfk hP

/-- The representation of the propositions is total in each direction. -/
theorem prop_total : (∀ p : Prop, ∃ q, Rep.prop p q) ∧ ∀ q : Prop, ∃ p, Rep.prop p q :=
  ⟨fun p ↦ ⟨p, rfl⟩, fun q ↦ ⟨q, rfl⟩⟩

/-- Falsity's arrow represents the false proposition: the quantification over the propositions
of the proposition itself. -/
theorem represents_ff (hbase : G.base = sig.length) (hF : compileDefs G = some ds)
    (hwf : PartialHorn.DefnsWF sig ds) (hlog : HasLogic G o) {ft fa fk : Tree}
    (hdt : ds[o]? = some ⟨List.replicate 0 obj, arr, ft⟩)
    (hda : ds[o + 3]? = some ⟨List.replicate 1 obj, arr, fa⟩)
    (hdk : ds[o + 4]? = some ⟨List.replicate 0 obj, arr, fk⟩) :
    Represents [] (unfoldTerm sig ds fk) Rep.unit Rep.prop fun _ ↦ False := by
  have hk : G.defs[o + 4]? = some (.language ⟨0, [], omega,
      Logic.all o omega (Term.lam omega (Term.var 0))⟩) :=
    hlog 4 _ rfl
  have hk₃ : ({ G with defs := G.defs.take (o + 4) } : Globals).defs[o + 3]? =
      some (.language ⟨1, [exp (x 0) omega], omega,
        Term.eq (Term.var 0) (Term.lam (x 0) (Logic.tt o))⟩) := by
    rw [defs_take (Nat.lt_succ_self (o + 3))]
    exact hlog 3 _ rfl
  have hall := represents_all (Rx := Rep.prop) hbase hF hwf hlog prop_total.1 prop_total.2 hdt
    hda
  have hvar : RepC { G with defs := G.defs.take (o + 4) } 0 ds [] (Term.var 0) (prod one omega)
      (extEnv one omega []) omega (Rep.prod Rep.unit Rep.prop) Rep.prop Prod.snd :=
    repC_var (envRep_ext (e := []) objVal_one objVal_omega .nil Rep.prop) rfl
  have hlam : RepC { G with defs := G.defs.take (o + 4) } 0 ds [] (Term.lam omega (Term.var 0))
      (ctxObj []) (stdEnv []) (exp omega omega) Rep.unit (Rep.exp Rep.prop Rep.prop)
      fun _ p ↦ p :=
    repC_lam (G := { G with defs := G.defs.take (o + 4) }) rfl objVal_one objVal_omega hvar
  have hb : RepC { G with defs := G.defs.take (o + 4) } 0 ds []
      (Logic.all o omega (Term.lam omega (Term.var 0))) (ctxObj []) (stdEnv []) omega Rep.unit
      Rep.prop fun _ ↦ ∀ p : Prop, p :=
    repC_all (G := { G with defs := G.defs.take (o + 4) }) (n := 0) (ρ := []) hbase hk₃ hwf hda
      hall rfl rfl eval_omega hlam
  exact rep_def (τ' := []) hF hk hb (fun _ ↦ propext ⟨fun h ↦ h False, False.elim⟩) hdk

/-- Falsity, applied in a context, represents the function to the false proposition, where the
constants have its definition and its arrow represents the false proposition. -/
theorem repC_ff (hbase : G.base = sig.length)
    (hk : G.defs[o + 4]? = some (.language ⟨0, [], omega,
      Logic.all o omega (Term.lam omega (Term.var 0))⟩))
    (hwf : PartialHorn.DefnsWF sig ds) {fk : Tree}
    (hdk : ds[o + 4]? = some ⟨List.replicate 0 obj, arr, fk⟩)
    (hfk : Represents [] (unfoldTerm sig ds fk) Rep.unit Rep.prop fun _ ↦ False) {X : Tree}
    {e : List (Tree × Tree)} (hX : ObjVal ρ (unfoldTerm sig ds X) A) (R : S → A → Prop) :
    RepC G n ds ρ (Logic.ff o) X e omega R Rep.prop fun _ ↦ False :=
  repC_call₀ (d := ⟨0, [], omega, Logic.all o omega (Term.lam omega (Term.var 0))⟩) hbase hk hwf
    hdk rfl rfl (subst_omega []) hX hfk

/-- Existential quantification's arrow, at a type, represents the existential quantification
of a predicate, where the representation of the type is total in each direction: the
quantification over the propositions of those every instance of the predicate implies. -/
theorem represents_ex (hbase : G.base = sig.length) (hF : compileDefs G = some ds)
    (hwf : PartialHorn.DefnsWF sig ds) (hlog : HasLogic G o) {Sx Ty : Type}
    {Rx : Sx → Ty → Prop} (hs : ∀ s, ∃ a, Rx s a) (ha : ∀ a, ∃ s, Rx s a) {ft fc fi fa fk : Tree}
    (hdt : ds[o]? = some ⟨List.replicate 0 obj, arr, ft⟩)
    (hdc : ds[o + 1]? = some ⟨List.replicate 0 obj, arr, fc⟩)
    (hdi : ds[o + 2]? = some ⟨List.replicate 0 obj, arr, fi⟩)
    (hda : ds[o + 3]? = some ⟨List.replicate 1 obj, arr, fa⟩)
    (hdk : ds[o + 7]? = some ⟨List.replicate 1 obj, arr, fk⟩) :
    Represents (objs [Ty]) (unfoldTerm sig ds fk) (Rep.exp Rx Rep.prop) Rep.prop
      fun P : Sx → Prop ↦ ∃ x, P x := by
  have hk : G.defs[o + 7]? = some (.language ⟨1, [exp (x 0) omega], omega,
      Logic.all o omega (Term.lam omega (Logic.imp o (Logic.all o (x 0) (Term.lam (x 0)
        (Logic.imp o (Term.app (Term.var 2) (Term.var 0)) (Term.var 1)))) (Term.var 0)))⟩) :=
    hlog 7 _ rfl
  have hk₂ : ({ G with defs := G.defs.take (o + 7) } : Globals).defs[o + 2]? =
      some (.language ⟨0, [omega, omega], omega,
        Term.eq (Logic.conj o (Term.var 1) (Term.var 0)) (Term.var 1)⟩) := by
    rw [defs_take (by omega)]
    exact hlog 2 _ rfl
  have hk₃ : ({ G with defs := G.defs.take (o + 7) } : Globals).defs[o + 3]? =
      some (.language ⟨1, [exp (x 0) omega], omega,
        Term.eq (Term.var 0) (Term.lam (x 0) (Logic.tt o))⟩) := by
    rw [defs_take (by omega)]
    exact hlog 3 _ rfl
  -- the values of the types and of the contexts under the binders
  have hx : ObjVal (objs [Ty]) (unfoldTerm sig ds (x 0)) Ty := by
    rw [unfold_x]
    exact objVal_x0
  have hP : ObjVal (objs [Ty]) (unfoldTerm sig ds (exp (x 0) omega)) (FunRel Ty Prop) := by
    simp (disch := decide) only [exp, omega, unfold_op', unfold_x, List.map_cons, List.map_nil]
    exact eval_exp objVal_x0 eval_omega
  have hX₀ : ObjVal (objs [Ty]) (unfoldTerm sig ds (ctxObj [exp (x 0) omega]))
      (FunRel Ty Prop) := by
    rw [ctxObj_single]
    exact hP
  have hX₁ : ObjVal (objs [Ty]) (unfoldTerm sig ds (prod (ctxObj [exp (x 0) omega]) omega))
      (FunRel Ty Prop × Prop) := by
    rw [ctxObj_single]
    simp (disch := decide) only [prod, exp, omega, unfold_op', unfold_x, List.map_cons,
      List.map_nil]
    exact eval_prod (eval_exp objVal_x0 eval_omega) eval_omega
  -- the environments under the binders
  have he₀ := envRep_std₁ (ds := ds) hP (Rep.exp Rx Rep.prop)
  have he₁ := envRep_ext hX₀ (objVal_omega (ds := ds)) he₀ Rep.prop
  have he₂ := envRep_ext hX₁ hx he₁ Rx
  have hfi := represents_imp hbase hF hwf hlog hdt hdc hdi
  -- the instance's implication of the proposition, and its quantification over the type
  have himp₁ : RepC { G with defs := G.defs.take (o + 7) } 1 ds (objs [Ty])
      (Logic.imp o (Term.app (Term.var 2) (Term.var 0)) (Term.var 1))
      (prod (prod (ctxObj [exp (x 0) omega]) omega) (x 0))
      (extEnv (prod (ctxObj [exp (x 0) omega]) omega) (x 0)
        (extEnv (ctxObj [exp (x 0) omega]) omega (stdEnv [exp (x 0) omega]))) omega
      (Rep.prod (Rep.prod (Rep.exp Rx Rep.prop) Rep.prop) Rx) Rep.prop
      fun s : ((Sx → Prop) × Prop) × Sx ↦ s.1.1 s.2 → s.1.2 :=
    repC_imp (G := { G with defs := G.defs.take (o + 7) }) hbase hk₂ hwf hdi hfi
      (repC_app (repC_var he₂ rfl) (repC_var he₂ rfl) hx objVal_omega) (repC_var he₂ rfl)
  have hall₁ : RepC { G with defs := G.defs.take (o + 7) } 1 ds (objs [Ty])
      (Logic.all o (x 0) (Term.lam (x 0)
        (Logic.imp o (Term.app (Term.var 2) (Term.var 0)) (Term.var 1))))
      (prod (ctxObj [exp (x 0) omega]) omega)
      (extEnv (ctxObj [exp (x 0) omega]) omega (stdEnv [exp (x 0) omega])) omega
      (Rep.prod (Rep.exp Rx Rep.prop) Rep.prop) Rep.prop
      fun s : (Sx → Prop) × Prop ↦ ∀ x, s.1 x → s.2 :=
    repC_all (G := { G with defs := G.defs.take (o + 7) }) (n := 1) (ρ := objs [Ty]) hbase hk₃
      hwf hda (represents_all hbase hF hwf hlog hs ha hdt hda) (isTy_x (by decide))
      (by simp [PartialHorn.OpsBelow, x, PartialHorn.var]) objVal_x0
      (repC_lam (G := { G with defs := G.defs.take (o + 7) }) (isTy_x (by decide)) hX₁ hx himp₁)
  -- its implication of the proposition, and the quantification over the propositions
  have himp₂ : RepC { G with defs := G.defs.take (o + 7) } 1 ds (objs [Ty])
      (Logic.imp o (Logic.all o (x 0) (Term.lam (x 0)
        (Logic.imp o (Term.app (Term.var 2) (Term.var 0)) (Term.var 1)))) (Term.var 0))
      (prod (ctxObj [exp (x 0) omega]) omega)
      (extEnv (ctxObj [exp (x 0) omega]) omega (stdEnv [exp (x 0) omega])) omega
      (Rep.prod (Rep.exp Rx Rep.prop) Rep.prop) Rep.prop
      fun s : (Sx → Prop) × Prop ↦ (∀ x, s.1 x → s.2) → s.2 :=
    repC_imp (G := { G with defs := G.defs.take (o + 7) }) hbase hk₂ hwf hdi hfi hall₁
      (repC_var he₁ rfl)
  have hb : RepC { G with defs := G.defs.take (o + 7) } 1 ds (objs [Ty])
      (Logic.all o omega (Term.lam omega (Logic.imp o (Logic.all o (x 0) (Term.lam (x 0)
        (Logic.imp o (Term.app (Term.var 2) (Term.var 0)) (Term.var 1)))) (Term.var 0))))
      (ctxObj [exp (x 0) omega]) (stdEnv [exp (x 0) omega]) omega (Rep.exp Rx Rep.prop)
      Rep.prop fun P : Sx → Prop ↦ ∀ p : Prop, (∀ x, P x → p) → p :=
    repC_all (G := { G with defs := G.defs.take (o + 7) }) (n := 1) (ρ := objs [Ty]) hbase hk₃
      hwf hda (represents_all (Rx := Rep.prop) hbase hF hwf hlog prop_total.1 prop_total.2 hdt
        hda) rfl rfl eval_omega
      (repC_lam (G := { G with defs := G.defs.take (o + 7) }) rfl hX₀ objVal_omega himp₂)
  exact rep_def (τ' := [Ty]) hF hk hb (fun P ↦ propext
    ⟨fun h ↦ h _ fun x hx ↦ ⟨x, hx⟩, fun ⟨x, hx⟩ _ h ↦ h x hx⟩) hdk

/-- An existential quantification in a context represents the existential quantification of
the function its predicate represents, where the constants have the quantification's
definition, its arrow represents the quantification at the type's value, and the type is one
of the theory's signature. -/
theorem repC_ex (hbase : G.base = sig.length)
    (hk : G.defs[o + 7]? = some (.language ⟨1, [exp (x 0) omega], omega,
      Logic.all o omega (Term.lam omega (Logic.imp o (Logic.all o (x 0) (Term.lam (x 0)
        (Logic.imp o (Term.app (Term.var 2) (Term.var 0)) (Term.var 1)))) (Term.var 0)))⟩))
    (hwf : PartialHorn.DefnsWF sig ds) {fk : Tree}
    (hdk : ds[o + 7]? = some ⟨List.replicate 1 obj, arr, fk⟩) {Sx Ty : Type}
    {Rx : Sx → Ty → Prop}
    (hfk : Represents (objs [Ty]) (unfoldTerm sig ds fk) (Rep.exp Rx Rep.prop) Rep.prop
      fun P : Sx → Prop ↦ ∃ x, P x) {a : Tree} (hta : IsTy G n a = true)
    (hops : PartialHorn.OpsBelow sig.length a = true) (hva : ObjVal ρ a Ty) {X : Tree}
    {e : List (Tree × Tree)} {Pr : Term} {R : S → A → Prop} {F : S → Sx → Prop}
    (hP : RepC G n ds ρ Pr X e (exp a omega) R (Rep.exp Rx Rep.prop) F) :
    RepC G n ds ρ (Logic.ex o a Pr) X e omega R Rep.prop fun s ↦ ∃ x, F s x :=
  repC_call₁ (θ := [a]) (τ' := [Ty]) (d := ⟨1, [exp (x 0) omega], omega,
      Logic.all o omega (Term.lam omega (Logic.imp o (Logic.all o (x 0) (Term.lam (x 0)
        (Logic.imp o (Term.app (Term.var 2) (Term.var 0)) (Term.var 1)))) (Term.var 0)))⟩)
    hbase hk hwf hdk rfl (by simp [hta]) (by simpa using hops) (.cons hva .nil)
    (subst_omega [a])
    (by simp only [List.map_cons, List.map_nil, exp, omega, subst_op, subst_x,
      List.getElem?_cons_zero, Option.getD_some]) hfk hP

/-- Constants with the connectives' definitions that compile to well-formed definitions: what
the readings of the connectives in a context assume. -/
structure Connectives (G : Globals) (ds : List PartialHorn.Defn) (o : ℕ) : Prop where
  /-- The constants' base is the theory's signature. -/
  base : G.base = sig.length
  /-- The constants compile. -/
  compiles : compileDefs G = some ds
  /-- The compiled definitions are well formed. -/
  wf : PartialHorn.DefnsWF sig ds
  /-- The constants have the connectives' definitions. -/
  logic : HasLogic G o

namespace Connectives

variable (hC : Connectives G ds o) {X : Tree} {e : List (Tree × Tree)} {R : S → A → Prop}
include hC

/-- Truth in a context represents the function to the true proposition. -/
theorem tt (hX : ObjVal ρ (unfoldTerm sig ds X) A) (R : S → A → Prop) :
    RepC G n ds ρ (Logic.tt o) X e omega R Rep.prop fun _ ↦ True := by
  obtain ⟨ft, hdt⟩ := compiled_language hC.compiles (hC.logic 0 _ rfl)
  exact repC_tt hC.base (hC.logic 0 _ rfl) hC.wf hdt (represents_tt hC.compiles hC.logic hdt)
    hX R

/-- Falsity in a context represents the function to the false proposition. -/
theorem ff (hX : ObjVal ρ (unfoldTerm sig ds X) A) (R : S → A → Prop) :
    RepC G n ds ρ (Logic.ff o) X e omega R Rep.prop fun _ ↦ False := by
  obtain ⟨ft, hdt⟩ := compiled_language hC.compiles (hC.logic 0 _ rfl)
  obtain ⟨fa, hda⟩ := compiled_language hC.compiles (hC.logic 3 _ rfl)
  obtain ⟨fk, hdk⟩ := compiled_language hC.compiles (hC.logic 4 _ rfl)
  exact repC_ff hC.base (hC.logic 4 _ rfl) hC.wf hdk
    (represents_ff hC.base hC.compiles hC.wf hC.logic hdt hda hdk) hX R

/-- A conjunction in a context represents the conjunction of what its formulas represent. -/
theorem conj {p q : Term} {P Q : S → Prop} (hp : RepC G n ds ρ p X e omega R Rep.prop P)
    (hq : RepC G n ds ρ q X e omega R Rep.prop Q) :
    RepC G n ds ρ (Logic.conj o p q) X e omega R Rep.prop fun s ↦ P s ∧ Q s := by
  obtain ⟨ft, hdt⟩ := compiled_language hC.compiles (hC.logic 0 _ rfl)
  obtain ⟨fc, hdc⟩ := compiled_language hC.compiles (hC.logic 1 _ rfl)
  exact repC_conj hC.base (hC.logic 1 _ rfl) hC.wf hdc
    (represents_conj hC.base hC.compiles hC.wf hC.logic hdt hdc) hp hq

/-- An implication in a context represents the implication of what its formulas represent. -/
theorem imp {p q : Term} {P Q : S → Prop} (hp : RepC G n ds ρ p X e omega R Rep.prop P)
    (hq : RepC G n ds ρ q X e omega R Rep.prop Q) :
    RepC G n ds ρ (Logic.imp o p q) X e omega R Rep.prop fun s ↦ P s → Q s := by
  obtain ⟨ft, hdt⟩ := compiled_language hC.compiles (hC.logic 0 _ rfl)
  obtain ⟨fc, hdc⟩ := compiled_language hC.compiles (hC.logic 1 _ rfl)
  obtain ⟨fi, hdi⟩ := compiled_language hC.compiles (hC.logic 2 _ rfl)
  exact repC_imp hC.base (hC.logic 2 _ rfl) hC.wf hdi
    (represents_imp hC.base hC.compiles hC.wf hC.logic hdt hdc hdi) hp hq

/-- A universal quantification in a context, over a type of the theory's signature whose
representation is total in each direction, represents the universal quantification of what its
predicate represents. -/
theorem all {Sx Ty : Type} {Rx : Sx → Ty → Prop} (hs : ∀ s, ∃ a, Rx s a)
    (ht : ∀ a, ∃ s, Rx s a) {a : Tree} (hta : IsTy G n a = true)
    (hops : PartialHorn.OpsBelow sig.length a = true) (hva : ObjVal ρ a Ty) {Pr : Term}
    {F : S → Sx → Prop} (hP : RepC G n ds ρ Pr X e (exp a omega) R (Rep.exp Rx Rep.prop) F) :
    RepC G n ds ρ (Logic.all o a Pr) X e omega R Rep.prop fun s ↦ ∀ x, F s x := by
  obtain ⟨ft, hdt⟩ := compiled_language hC.compiles (hC.logic 0 _ rfl)
  obtain ⟨fa, hda⟩ := compiled_language hC.compiles (hC.logic 3 _ rfl)
  exact repC_all hC.base (hC.logic 3 _ rfl) hC.wf hda
    (represents_all hC.base hC.compiles hC.wf hC.logic hs ht hdt hda) hta hops hva hP

/-- An existential quantification in a context, over a type of the theory's signature whose
representation is total in each direction, represents the existential quantification of what
its predicate represents. -/
theorem ex {Sx Ty : Type} {Rx : Sx → Ty → Prop} (hs : ∀ s, ∃ a, Rx s a)
    (ht : ∀ a, ∃ s, Rx s a) {a : Tree} (hta : IsTy G n a = true)
    (hops : PartialHorn.OpsBelow sig.length a = true) (hva : ObjVal ρ a Ty) {Pr : Term}
    {F : S → Sx → Prop} (hP : RepC G n ds ρ Pr X e (exp a omega) R (Rep.exp Rx Rep.prop) F) :
    RepC G n ds ρ (Logic.ex o a Pr) X e omega R Rep.prop fun s ↦ ∃ x, F s x := by
  obtain ⟨ft, hdt⟩ := compiled_language hC.compiles (hC.logic 0 _ rfl)
  obtain ⟨fc, hdc⟩ := compiled_language hC.compiles (hC.logic 1 _ rfl)
  obtain ⟨fi, hdi⟩ := compiled_language hC.compiles (hC.logic 2 _ rfl)
  obtain ⟨fa, hda⟩ := compiled_language hC.compiles (hC.logic 3 _ rfl)
  obtain ⟨fk, hdk⟩ := compiled_language hC.compiles (hC.logic 7 _ rfl)
  exact repC_ex hC.base (hC.logic 7 _ rfl) hC.wf hdk
    (represents_ex hC.base hC.compiles hC.wf hC.logic hs ht hdt hdc hdi hda hdk) hta hops hva hP

end Connectives

/-- A formula whose arrow from an object, with every definition unfolded, is true in the topos
of types and functional relations, and represents there a function into the propositions,
represents a function that holds at each value with a representation: the arrow's value is
truth's after the arrow to the terminal type, which relates each element to the true
propositions alone. -/
theorem holds_of_represents {C X : Tree}
    (hv : (PartialHorn.unfoldAll sig ds ⟨[], [], ⟨C, comp tru (bang X)⟩⟩).Valid relTopos.model)
    (hX : ObjVal [] (unfoldTerm sig ds X) A) {R : S → A → Prop} {F : S → Prop}
    (hF : Represents [] (unfoldTerm sig ds C) R Rep.prop F) {s : S} {a : A} (hs : R s a) :
    F s := by
  rw [unfoldAll_eq] at hv
  obtain ⟨w, hw₁, hw₂⟩ := hv [] rfl (fun _ h ↦ nomatch h)
  obtain ⟨φ, hφ, hrφ⟩ := hF
  have ht : ArrVal [] (unfoldTerm sig ds (comp tru (bang X)))
      (FunRel.comp FunRel.tru (FunRel.bang A)) := by
    simp (disch := decide) only [comp, tru, bang, unfold_op', List.map_cons, List.map_nil]
    exact eval_comp (eval_bang hX) eval_tru
  unfold ArrVal at hφ ht
  have hφψ := Part.some_injective ((hφ.symm.trans hw₁).trans (hw₂.symm.trans ht))
  simp only [Sigma.mk.injEq, heq_eq_eq, true_and] at hφψ
  obtain ⟨-, h₁⟩ := Sigma.mk.inj hφψ
  obtain rfl : φ = FunRel.comp FunRel.tru (FunRel.bang A) :=
    eq_of_heq (Sigma.mk.inj (eq_of_heq h₁)).2
  exact of_eq_true (hrφ s a hs True ⟨(), rfl, trivial⟩)

end Geb.FreeTopos.Internal

end
