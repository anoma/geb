/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.FreeTopos.Internal.Derivation
public import Geb.Prototypes.FreeTopos.Internal.Inversion
public import Geb.Prototypes.FreeTopos.Represent
public import Geb.Prototypes.FreeTopos.Unfolding

set_option doc.verso true

/-!
# The internal language's terms represent Lean's functions

A term of the internal language compiles, in an environment, to an arrow of the combinators;
with the definitions it applies unfolded ({name}`Geb.FreeTopos.unfoldTerm`), the arrow is one of
the theory itself, whose value in the topos of types and functional relations is a functional
relation. The type an object term denotes there is computed from the term ({lit}`RelTy`), at
types for its object variables, so that the types of the values of a term's parts are the types
of its type's parts by definition.

A term represents a function ({lit}`RepC`) when it compiles, at a given type, to an arrow that,
unfolded, represents the function ({name}`Geb.FreeTopos.Represents`). The representations are
built forward, one construction of the language at a time, from representations of the parts:
a variable represents the projection its environment's arrow represents ({lit}`EnvRep`), and
pairs, components, abstraction, application, the primitive arrows, the folds and the
application of a definition represent the functions of the same universal properties.

## Main definitions

* {lit}`RelTy`, {lit}`objs` — the type an object term denotes, and the assignment of the types
  of its object variables.
* {lit}`RepEntry`, {lit}`EnvRep` — an environment's arrows represent projections.
* {lit}`RepC` — a term represents a function.

## Main statements

* {lit}`objVal_var` — an object variable's value is the type {lit}`RelTy` computes.

## Tags

internal language, logical relation, representation, compilation, functional relation
-/

@[expose] public section

namespace Geb.FreeTopos.Internal

open PartialHorn (Tree op var eval)
open Sorts
open scoped FinEnum

/-- The type of the topos of types and functional relations that an object term denotes, at the
types {lit}`τ` of its object variables: the terminal object's, products', the initial object's,
coproducts', exponentials', the subobject classifier's, the natural numbers object's, list
objects', the rose-tree object's and rose-tree objects' over a type of labels. -/
def RelTy (τ : List Type) : Tree → Type :=
  RoseTree.para fun l cs ↦ match l, cs with
    | 0, [(i, _)] => (τ[i.label]?).getD Unit
    | 5, [] => Unit
    | 7, [(_, A), (_, B)] => A × B
    | 14, [] => Empty
    | 16, [(_, A), (_, B)] => A ⊕ B
    | 23, [(_, A), (_, B)] => FunRel A B
    | 26, [] => Prop
    | 30, [] => ℕ
    | 34, [(_, A)] => List A
    | 38, [] => RoseTree ℕ
    | 41, [(_, A)] => RoseTree A
    | _, _ => Unit

variable {τ : List Type}

/-- The assignment of the topos's values to the object variables at the types {lit}`τ`. -/
def objs (τ : List Type) : List relTopos.model.Val :=
  τ.map fun A : Type ↦ (⟨obj, ⟨A⟩⟩ : relTopos.model.Val)

/-- An object variable's value is the type {lit}`RelTy` computes, at the types of the object
variables. -/
theorem objVal_var {i : ℕ} (hi : i < τ.length) : ObjVal (objs τ) (x i) (RelTy τ (x i)) := by
  rw [ObjVal, x, var, PartialHorn.eval_node_zero rfl]
  change _ = Part.some (⟨obj, ⟨(τ[i]?).getD Unit⟩⟩ : relTopos.model.Val)
  simp only [objs, RoseTree.label_node, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some, Part.coe_some]

/-- The first object variable's value is the first type. -/
theorem objVal_x0 {A : Type} {τ : List Type} : ObjVal (objs (A :: τ)) (x 0) A :=
  objVal_var (τ := A :: τ) (by simp)

/-- The second object variable's value is the second type. -/
theorem objVal_x1 {A B : Type} {τ : List Type} : ObjVal (objs (A :: B :: τ)) (x 1) B :=
  objVal_var (τ := A :: B :: τ) (by simp)

/-- An object variable below the number of object variables is a type. -/
theorem isTy_x {G : Globals} {n i : ℕ} (h : i < n) : IsTy G n (x i) = true := by
  simp [IsTy, x, var, RoseTree.para_node, h]

/-! The unfolding at the operations of the theory. -/

section Unfold

variable (ds : List PartialHorn.Defn)

/-- The unfolding at an application of an operation of the theory, by index. -/
theorem unfold_op {k : ℕ} (hk : k < sig.length) (ts : List Tree) :
    unfoldTerm sig ds (op k ts) = op k (ts.map (unfoldTerm sig ds)) :=
  unfoldTerm_op_lt ds ts sig hk

/-- The signature's operations number forty-three. -/
theorem sig_length : sig.length = 43 := rfl

/-- The unfolding at an application of an operation of the theory, by an index below the
signature's length stated as a numeral. -/
theorem unfold_op' {k : ℕ} (hk : k < 43) (ts : List Tree) :
    unfoldTerm sig ds (op k ts) = op k (ts.map (unfoldTerm sig ds)) :=
  unfold_op ds (sig_length ▸ hk) ts

/-- The unfolding leaves an object variable. -/
theorem unfold_x (i : ℕ) : unfoldTerm sig ds (x i) = x i :=
  unfoldTerm_of_opsBelow ds sig (x i) (by simp [PartialHorn.OpsBelow, x, var])

end Unfold

/-- The unfolding's rewriting at the operations of the theory an arrow or an object of the
internal language's compilation applies. -/
scoped macro (name := simpUnfold) "simp_unfold" : tactic =>
  `(tactic| simp (disch := decide) only [one, prod, exp, coprod, list, lrose, idt, comp, bang,
    fst, snd, pair, inl, inr, copair, ev, curry, nil, cons, listRec, lnode, lroseRec, caseArr,
    copairIn, unfold_op', unfold_x, List.map_cons, List.map_nil])

/-! The representations of the terms. -/

section Terms

variable {G : Globals} {n : ℕ} {ds : List PartialHorn.Defn} {ρ : List relTopos.model.Val}
  {S S' S'' T T' A A' A'' B C : Type}

variable (G n ds ρ) in
/-- A term represents a function: in the environment {lit}`e` over {lit}`X` it compiles, at the
type {lit}`a`, to an arrow that, with the definitions {lit}`ds` unfolded, represents the
function. -/
def RepC (t : Term) (X : Tree) (e : List (Tree × Tree)) (a : Tree) {S T A B : Type}
    (R : S → A → Prop) (R' : T → B → Prop) (F : S → T) : Prop :=
  ∃ f, compile G n t X e = some (f, a) ∧ Represents ρ (unfoldTerm sig ds f) R R' F

/-- An entry of an environment's representation: the type of the entry's arrow, and the
representation, by the arrow, of a function of the environment's values. -/
structure RepEntry (S : Type) : Type 1 where
  /-- The type of the entry's arrow. -/
  ty : Tree
  /-- The type of the values of the function. -/
  T : Type
  /-- The type of the topos the arrow's values are of. -/
  B : Type
  /-- The representation of the values. -/
  rel : T → B → Prop
  /-- The function. -/
  get : S → T

variable (ds ρ) in
/-- An environment's arrows represent the functions of its entries, each of the entry's type. -/
def EnvRep (e : List (Tree × Tree)) {S A : Type} (R : S → A → Prop) (ents : List (RepEntry S)) :
    Prop :=
  List.Forall₂ (fun p x ↦ p.2 = x.ty ∧ Represents ρ (unfoldTerm sig ds p.1) R x.rel x.get) e ents

/-- An element of the second of two lists related elementwise is related to the first's element
of its index. -/
theorem forall₂_getElem?_right {α β : Type*} {R : α → β → Prop} :
    ∀ {l₁ : List α} {l₂ : List β}, List.Forall₂ R l₁ l₂ → ∀ {i : ℕ} {y : β}, l₂[i]? = some y →
      ∃ x, l₁[i]? = some x ∧ R x y
  | _, _, .nil, _, _, h => by simp at h
  | _, _, .cons hxy _, 0, _, h => ⟨_, rfl, (Option.some_inj.mp h) ▸ hxy⟩
  | _, _, .cons _ hs, _ + 1, _, h => forall₂_getElem?_right hs h

/-- A variable represents the function of its entry. -/
theorem repC_var {X : Tree} {e : List (Tree × Tree)} {R : S → A → Prop} {ents : List (RepEntry S)}
    (he : EnvRep ds ρ e R ents) {i : ℕ} {a : Tree} {R' : T → B → Prop} {F : S → T}
    (hx : ents[i]? = some ⟨a, T, B, R', F⟩) : RepC G n ds ρ (Term.var i) X e a R R' F := by
  obtain ⟨⟨f, a'⟩, hp, rfl, hpx⟩ := forall₂_getElem?_right he hx
  exact ⟨f, compile_var_iff.mpr ⟨rfl, hp⟩, hpx⟩

/-- The element of the terminal object represents the function to the element. -/
theorem repC_star {X : Tree} {e : List (Tree × Tree)} (hX : ObjVal ρ (unfoldTerm sig ds X) A)
    (R : S → A → Prop) : RepC G n ds ρ Term.star X e one R Rep.unit fun _ ↦ () :=
  ⟨bang X, compile_star_iff.mpr ⟨rfl, rfl⟩, by
    simp_unfold
    exact represents_bang hX R⟩

/-- A pair represents the pairing. -/
theorem repC_pair {X : Tree} {e : List (Tree × Tree)} {t u : Term} {a b : Tree}
    {R : S → A → Prop} {R₁ : T → B → Prop} {R₂ : T' → C → Prop} {F : S → T} {F' : S → T'}
    (ht : RepC G n ds ρ t X e a R R₁ F) (hu : RepC G n ds ρ u X e b R R₂ F') :
    RepC G n ds ρ (Term.pair t u) X e (prod a b) R (Rep.prod R₁ R₂) fun s ↦ (F s, F' s) :=
  let ⟨f, hf, hF⟩ := ht
  let ⟨g, hg, hG⟩ := hu
  ⟨pair f g, compile_pair_iff.mpr ⟨t, u, f, a, g, b, rfl, hf, hg, rfl⟩, by
    simp_unfold
    exact represents_pair hF hG⟩

/-- A first component represents the first projection. -/
theorem repC_fst {X : Tree} {e : List (Tree × Tree)} {t : Term} {a b : Tree}
    {R : S → A → Prop} {R₁ : T → B → Prop} {R₂ : T' → C → Prop} {F : S → T × T'}
    (ht : RepC G n ds ρ t X e (prod a b) R (Rep.prod R₁ R₂) F)
    (ha : ObjVal ρ (unfoldTerm sig ds a) B) (hb : ObjVal ρ (unfoldTerm sig ds b) C) :
    RepC G n ds ρ (Term.fst t) X e a R R₁ fun s ↦ (F s).1 :=
  let ⟨f, hf, hF⟩ := ht
  ⟨comp (fst a b) f, compile_fst_iff.mpr ⟨t, f, a, b, rfl, hf, rfl⟩, by
    simp_unfold
    exact represents_comp hF (represents_fst ha hb R₁ R₂)⟩

/-- A second component represents the second projection. -/
theorem repC_snd {X : Tree} {e : List (Tree × Tree)} {t : Term} {a b : Tree}
    {R : S → A → Prop} {R₁ : T → B → Prop} {R₂ : T' → C → Prop} {F : S → T × T'}
    (ht : RepC G n ds ρ t X e (prod a b) R (Rep.prod R₁ R₂) F)
    (ha : ObjVal ρ (unfoldTerm sig ds a) B) (hb : ObjVal ρ (unfoldTerm sig ds b) C) :
    RepC G n ds ρ (Term.snd t) X e b R R₂ fun s ↦ (F s).2 :=
  let ⟨f, hf, hF⟩ := ht
  ⟨comp (snd a b) f, compile_snd_iff.mpr ⟨t, f, a, b, rfl, hf, rfl⟩, by
    simp_unfold
    exact represents_comp hF (represents_snd ha hb R₁ R₂)⟩

/-- An abstraction represents the currying of its body's function. -/
theorem repC_lam {X : Tree} {e : List (Tree × Tree)} {t : Term} {a b : Tree}
    (hta : IsTy G n a = true) (hX : ObjVal ρ (unfoldTerm sig ds X) A)
    (ha : ObjVal ρ (unfoldTerm sig ds a) A') {R : S → A → Prop} {R₁ : S' → A' → Prop}
    {R₂ : T → B → Prop} {F : S × S' → T}
    (ht : RepC G n ds ρ t (prod X a) (extEnv X a e) b (Rep.prod R R₁) R₂ F) :
    RepC G n ds ρ (Term.lam a t) X e (exp a b) R (Rep.exp R₁ R₂) fun s x ↦ F (s, x) :=
  let ⟨f, hf, hF⟩ := ht
  ⟨curry X a f, compile_lam_iff.mpr ⟨t, f, b, rfl, hta, hf, rfl⟩, by
    simp_unfold
    exact represents_curry hX ha hF⟩

/-- An application represents the application. -/
theorem repC_app {X : Tree} {e : List (Tree × Tree)} {t u : Term} {a b : Tree}
    {R : S → C → Prop} {R₁ : S' → A → Prop} {R₂ : T → B → Prop} {F : S → S' → T} {F' : S → S'}
    (ht : RepC G n ds ρ t X e (exp a b) R (Rep.exp R₁ R₂) F) (hu : RepC G n ds ρ u X e a R R₁ F')
    (ha : ObjVal ρ (unfoldTerm sig ds a) A) (hb : ObjVal ρ (unfoldTerm sig ds b) B) :
    RepC G n ds ρ (Term.app t u) X e b R R₂ fun s ↦ F s (F' s) :=
  let ⟨f, hf, hF⟩ := ht
  let ⟨g, hg, hG⟩ := hu
  ⟨comp (ev a b) (pair f g), compile_app_iff.mpr ⟨t, u, rfl, f, a, b, hf, g, hg, rfl⟩, by
    simp_unfold
    exact represents_app ha hb hF hG⟩

/-! The environments of abstractions and of folds' steps. -/

/-- The environment an abstraction extends represents the projections of the pairs of an
environment's values and the new variable's. -/
theorem envRep_ext {X a : Tree} {e : List (Tree × Tree)} (hX : ObjVal ρ (unfoldTerm sig ds X) A)
    (ha : ObjVal ρ (unfoldTerm sig ds a) A') {R : S → A → Prop} {ents : List (RepEntry S)}
    (he : EnvRep ds ρ e R ents) (Ra : S' → A' → Prop) :
    EnvRep ds ρ (extEnv X a e) (Rep.prod R Ra)
      (⟨a, S', A', Ra, Prod.snd⟩ ::
        ents.map fun x ↦ ⟨x.ty, x.T, x.B, x.rel, x.get ∘ Prod.fst⟩) := by
  refine .cons ⟨rfl, ?_⟩ (List.forall₂_map_left_iff.mpr (List.forall₂_map_right_iff.mpr ?_))
  · simp_unfold
    exact represents_snd hX ha R Ra
  · refine he.imp fun p x ⟨h₁, h₂⟩ ↦ ⟨h₁, ?_⟩
    simp_unfold
    exact represents_comp (represents_fst hX ha R Ra) h₂

/-- The environment of a list fold's step represents the projections of the pairs of an element
and the fold's value. -/
theorem envRep_listStep {a c : Tree} (ha : ObjVal ρ (unfoldTerm sig ds a) A)
    (hc : ObjVal ρ (unfoldTerm sig ds c) C) (Ra : S → A → Prop) (Rc : T → C → Prop) :
    EnvRep ds ρ [(snd a c, c), (fst a c, a)] (Rep.prod Ra Rc)
      [⟨c, T, C, Rc, Prod.snd⟩, ⟨a, S, A, Ra, Prod.fst⟩] := by
  refine .cons ⟨rfl, ?_⟩ (.cons ⟨rfl, ?_⟩ .nil)
  · simp_unfold
    exact represents_snd ha hc Ra Rc
  · simp_unfold
    exact represents_fst ha hc Ra Rc

/-- The environment of a rose-tree fold's step represents the identity. -/
theorem envRep_idt {P : Tree} (hP : ObjVal ρ (unfoldTerm sig ds P) A) (R : S → A → Prop) :
    EnvRep ds ρ [(idt P, P)] R [⟨P, S, A, R, id⟩] := by
  refine .cons ⟨rfl, ?_⟩ .nil
  simp_unfold
  exact represents_idt hP R

/-! The primitive arrows. -/

/-- The substitution's rewriting at the operations of the theory and the object variables. -/
scoped macro (name := simpSubst) "simp_subst" : tactic =>
  `(tactic| simp only [nilPrim, consPrim, lnodePrim, inlPrim, inrPrim, casePrim, one, prod, exp,
    coprod, list, lrose, nil, cons, lnode, inl, inr, caseArr, copairIn, comp, pair, fst, snd, ev,
    curry, copair, subst_op, subst_x, List.map_cons, List.map_nil, List.getElem?_cons_zero,
    List.getElem?_cons_succ, Option.getD_some, List.length_cons, List.length_nil, List.all_cons,
    List.all_nil, Bool.and_true, Bool.and_eq_true])

/-- The empty list represents the empty list. -/
theorem repC_nil {X : Tree} {e : List (Tree × Tree)} {k : ℕ} (hk : G.prims[k]? = some nilPrim)
    {t : Term} {a : Tree} (hta : IsTy G n a = true) {R : S → A → Prop} {Z : S → Unit}
    (ht : RepC G n ds ρ t X e one R Rep.unit Z) (ha : ObjVal ρ (unfoldTerm sig ds a) A')
    (Ra : T → A' → Prop) :
    RepC G n ds ρ (Term.arr k [a] t) X e (list a) R (Rep.list Ra) fun _ ↦ [] :=
  let ⟨g, hg, hG⟩ := ht
  ⟨comp (nil a) g, compile_arr_iff.mpr ⟨t, rfl, nilPrim, hk, g, by simp_subst; exact hg, rfl,
      by simp [hta], by simp_subst⟩, by
    simp_unfold
    exact represents_comp hG (represents_nil ha Ra)⟩

/-- The construction of lists represents the construction. -/
theorem repC_cons {X : Tree} {e : List (Tree × Tree)} {k : ℕ} (hk : G.prims[k]? = some consPrim)
    {t : Term} {a : Tree} (hta : IsTy G n a = true) {R : S → A → Prop} {Ra : T → A' → Prop}
    {P : S → T × List T}
    (ht : RepC G n ds ρ t X e (prod a (list a)) R (Rep.prod Ra (Rep.list Ra)) P)
    (ha : ObjVal ρ (unfoldTerm sig ds a) A') :
    RepC G n ds ρ (Term.arr k [a] t) X e (list a) R (Rep.list Ra) fun s ↦ (P s).1 :: (P s).2 :=
  let ⟨g, hg, hG⟩ := ht
  ⟨comp (cons a) g, compile_arr_iff.mpr ⟨t, rfl, consPrim, hk, g, by simp_subst; exact hg, rfl,
      by simp [hta], by simp_subst⟩, by
    simp_unfold
    exact represents_comp hG (represents_cons ha Ra)⟩

/-- The construction of rose trees represents the construction. -/
theorem repC_lnode {X : Tree} {e : List (Tree × Tree)} {k : ℕ}
    (hk : G.prims[k]? = some lnodePrim) {t : Term} {a : Tree} (hta : IsTy G n a = true)
    {R : S → A → Prop} {Ra : T → A' → Prop} {P : S → T × List (RoseTree T)}
    (ht : RepC G n ds ρ t X e (prod a (list (lrose a))) R (Rep.prod Ra (Rep.list (Rep.rose Ra))) P)
    (ha : ObjVal ρ (unfoldTerm sig ds a) A') :
    RepC G n ds ρ (Term.arr k [a] t) X e (lrose a) R (Rep.rose Ra)
      fun s ↦ RoseTree.node (P s).1 (P s).2 :=
  let ⟨g, hg, hG⟩ := ht
  ⟨comp (lnode a) g, compile_arr_iff.mpr ⟨t, rfl, lnodePrim, hk, g, by simp_subst; exact hg,
      rfl, by simp [hta], by simp_subst⟩, by
    simp_unfold
    exact represents_comp hG (represents_lnode ha Ra)⟩

/-- The left injection represents the left injection. -/
theorem repC_inl {X : Tree} {e : List (Tree × Tree)} {k : ℕ} (hk : G.prims[k]? = some inlPrim)
    {t : Term} {a b : Tree} (hta : IsTy G n a = true) (htb : IsTy G n b = true)
    {R : S → A → Prop} {Ra : T → A' → Prop} {F : S → T} (ht : RepC G n ds ρ t X e a R Ra F)
    (ha : ObjVal ρ (unfoldTerm sig ds a) A') (hb : ObjVal ρ (unfoldTerm sig ds b) B)
    (Rb : T' → B → Prop) :
    RepC G n ds ρ (Term.arr k [a, b] t) X e (coprod a b) R (Rep.sum Ra Rb) fun s ↦ .inl (F s) :=
  let ⟨g, hg, hG⟩ := ht
  ⟨comp (inl a b) g, compile_arr_iff.mpr ⟨t, rfl, inlPrim, hk, g, by simp_subst; exact hg, rfl,
      by simp [hta, htb], by simp_subst⟩, by
    simp_unfold
    exact represents_comp hG (represents_inl ha hb Ra Rb)⟩

/-- The right injection represents the right injection. -/
theorem repC_inr {X : Tree} {e : List (Tree × Tree)} {k : ℕ} (hk : G.prims[k]? = some inrPrim)
    {t : Term} {a b : Tree} (hta : IsTy G n a = true) (htb : IsTy G n b = true)
    {R : S → A → Prop} {Rb : T' → B → Prop} {F : S → T'} (ht : RepC G n ds ρ t X e b R Rb F)
    (ha : ObjVal ρ (unfoldTerm sig ds a) A') (hb : ObjVal ρ (unfoldTerm sig ds b) B)
    (Ra : T → A' → Prop) :
    RepC G n ds ρ (Term.arr k [a, b] t) X e (coprod a b) R (Rep.sum Ra Rb) fun s ↦ .inr (F s) :=
  let ⟨g, hg, hG⟩ := ht
  ⟨comp (inr a b) g, compile_arr_iff.mpr ⟨t, rfl, inrPrim, hk, g, by simp_subst; exact hg, rfl,
      by simp [hta, htb], by simp_subst⟩, by
    simp_unfold
    exact represents_comp hG (represents_inr ha hb Ra Rb)⟩

/-- The case analysis of a coproduct represents the case analysis of a sum. -/
theorem repC_case {X : Tree} {e : List (Tree × Tree)} {k : ℕ} (hk : G.prims[k]? = some casePrim)
    {t : Term} {a b c : Tree} (hta : IsTy G n a = true) (htb : IsTy G n b = true)
    (htc : IsTy G n c = true) {R : S → A → Prop} {R₁ : T → A' → Prop} {R₂ : T' → B → Prop}
    {Rc : S' → C → Prop} {P : S → (T → S') × (T' → S')}
    (ht : RepC G n ds ρ t X e (prod (exp a c) (exp b c)) R
      (Rep.prod (Rep.exp R₁ Rc) (Rep.exp R₂ Rc)) P)
    (ha : ObjVal ρ (unfoldTerm sig ds a) A') (hb : ObjVal ρ (unfoldTerm sig ds b) B)
    (hc : ObjVal ρ (unfoldTerm sig ds c) C) :
    RepC G n ds ρ (Term.arr k [a, b, c] t) X e (exp (coprod a b) c) R
      (Rep.exp (Rep.sum R₁ R₂) Rc) fun s ↦ Sum.elim (P s).1 (P s).2 :=
  let ⟨g, hg, hG⟩ := ht
  ⟨comp (caseArr a b c) g, compile_arr_iff.mpr ⟨t, rfl, casePrim, hk, g, by simp_subst; exact hg,
      rfl, by simp [hta, htb, htc], by simp_subst⟩, by
    simp_unfold
    exact represents_comp hG (represents_caseArr ha hb hc R₁ R₂ Rc)⟩

/-! The folds. -/

/-- The fold of a list represents the right fold of the list. -/
theorem repC_listRec {X : Tree} {e : List (Tree × Tree)} {z s m : Term} {a c : Tree}
    {R : S → A → Prop} {Ra : T → A' → Prop} {Rc : T' → C → Prop} {M : S → List T} {Z : Unit → T'}
    {St : T × T' → T'} (hm : RepC G n ds ρ m X e (list a) R (Rep.list Ra) M)
    (hz : RepC G n ds ρ z one [] c Rep.unit Rc Z)
    (hs : RepC G n ds ρ s (prod a c) [(snd a c, c), (fst a c, a)] c (Rep.prod Ra Rc) Rc St)
    (ha : ObjVal ρ (unfoldTerm sig ds a) A') :
    RepC G n ds ρ (Term.listRec z s m) X e c R Rc
      fun x ↦ List.foldr (fun y r ↦ St (y, r)) (Z ()) (M x) :=
  let ⟨m', hm', hM⟩ := hm
  let ⟨z', hz', hZ⟩ := hz
  let ⟨s', hs', hS⟩ := hs
  ⟨comp (listRec a z' s') m', compile_listRec_iff.mpr ⟨z, s, m, rfl, m', a, hm', z', c, hz', s',
      hs', rfl⟩, by
    simp_unfold
    exact represents_comp hM (represents_listRec ha hZ hS)⟩

/-- The fold of a rose tree over a type of labels represents the fold of rose trees. -/
theorem repC_roseRec {X : Tree} {e : List (Tree × Tree)} {s m : Term} {a c : Tree}
    (htc : IsTy G n c = true) {R : S → A → Prop} {Ra : T → A' → Prop} {Rc : T' → C → Prop}
    {M : S → RoseTree T} {Fn : T × List T' → T'}
    (hm : RepC G n ds ρ m X e (lrose a) R (Rep.rose Ra) M)
    (hs : RepC G n ds ρ s (prod a (list c)) [(idt (prod a (list c)), prod a (list c))] c
      (Rep.prod Ra (Rep.list Rc)) Rc Fn)
    (ha : ObjVal ρ (unfoldTerm sig ds a) A') :
    RepC G n ds ρ (Term.roseRec c s m) X e c R Rc
      fun x ↦ RoseTree.elim (fun l cs ↦ Fn (l, cs)) (M x) :=
  let ⟨m', hm', hM⟩ := hm
  let ⟨s', hs', hS⟩ := hs
  ⟨comp (lroseRec a s') m', compile_roseRec_iff.mpr ⟨s, m, m', lrose a, a, lroseRec a, s', rfl,
      htc, hm', roseParts_lrose a, hs', rfl⟩, by
    simp_unfold
    exact represents_comp hM (represents_lroseRec ha hS)⟩

/-! The application of a definition. -/

/-- Object terms whose values are types evaluate to the assignment of those types. -/
theorem map_eval_of_objVal {θ : List Tree} {τ' : List Type}
    (h : List.Forall₂ (fun u A ↦ ObjVal ρ u A) θ τ') :
    θ.map (eval relTopos.model ρ) = (objs τ').map Part.some := by
  refine h.rec (motive := fun θ τ' _ ↦ θ.map (eval relTopos.model ρ) = (objs τ').map Part.some)
    rfl fun hu _ ih ↦ ?_
  simp only [List.map_cons, objs] at ih ⊢
  unfold ObjVal at hu
  rw [hu, ih]

/-- The application of a definition, of an object of the combinators of the definitions
{lit}`ds`, at objects that are types, represents the definition's function after the function
its arguments' tuple represents, when the definition's arrow represents that function at the
objects' types. -/
theorem repC_defn {X : Tree} {e : List (Tree × Tree)} {k : ℕ} {θ : List Tree} {args : List Term}
    {d : Defn} {fk : Tree} {τ' : List Type} (hbase : G.base = sig.length)
    (hk : G.defs[k]? = some (.language d)) (hwf : PartialHorn.DefnsWF sig ds)
    (hdk : ds[k]? = some ⟨List.replicate d.arity obj, arr, fk⟩) (hθlen : θ.length = d.arity)
    (hθty : θ.all (IsTy G n) = true) (hθops : ∀ u ∈ θ, PartialHorn.OpsBelow sig.length u = true)
    (hθval : List.Forall₂ (fun u A ↦ ObjVal ρ u A) θ τ') {R : S → A → Prop} {Rp : T → B → Prop}
    {Rt : T' → C → Prop} {P : S → T} {Fk : T → T'}
    (hfk : Represents (objs τ') (unfoldTerm sig ds fk) Rp Rt Fk) {rs : List (Tree × Tree)}
    (hrs : args.mapM (fun c ↦ compile G n c X e) = some rs)
    (hps : rs.map Prod.snd = d.params.map (PartialHorn.subst θ))
    (hP : Represents ρ (unfoldTerm sig ds (tuple X (rs.map Prod.fst))) R Rp P) :
    RepC G n ds ρ (Term.defn k θ args) X e (PartialHorn.subst θ d.type) R Rt (Fk ∘ P) := by
  refine ⟨comp (op (G.base + k) θ) (tuple X (rs.map Prod.fst)),
    compile_defn_iff.mpr ⟨d, rs, hk, hrs, hθlen, hθty, hps, rfl⟩, ?_⟩
  have hdwf := defnsWF_getElem ds sig hwf hdk
  have hsort :
      PartialHorn.sortOf (sig.extendAll ds) (List.replicate d.arity obj) fk = some arr := by
    refine PartialHorn.sortOf_of_prefix ?_ hdwf.sort
    rw [extendAll_eq, extendAll_eq]
    exact (List.prefix_append_right_inj _).mpr ((List.take_prefix k ds).map _)
  have hscope : PartialHorn.Scoped θ.length (unfoldTerm sig ds fk) = true := by
    have := PartialHorn.scoped_of_sortOf _ (sortOf_unfoldTerm ds sig hwf hsort)
    rwa [List.length_replicate, ← hθlen] at this
  have hsub := PartialHorn.eval_subst (map_eval_of_objVal hθval) _ hscope
  obtain ⟨φ, hφ, hF⟩ := hfk
  rw [comp, unfold_op ds (by decide), List.map_cons, List.map_cons, List.map_nil, hbase,
    unfoldTerm_op_defn ds sig hwf hdk hθops]
  exact represents_comp hP ⟨φ, by unfold ArrVal at hφ ⊢; exact hsub.trans hφ, hF⟩

/-- The arguments of an application of a definition of one parameter. -/
theorem args_one {X : Tree} {e : List (Tree × Tree)} {a₁ : Term} {p₁ : Tree} {R : S → A → Prop}
    {R₁ : T → B → Prop} {F₁ : S → T} (h₁ : RepC G n ds ρ a₁ X e p₁ R R₁ F₁) :
    ∃ rs : List (Tree × Tree), [a₁].mapM (fun c ↦ compile G n c X e) = some rs ∧
      rs.map Prod.snd = [p₁] ∧
      Represents ρ (unfoldTerm sig ds (tuple X (rs.map Prod.fst))) R R₁ F₁ :=
  let ⟨f₁, hf₁, hF₁⟩ := h₁
  ⟨[(f₁, p₁)], by simp [hf₁], rfl, hF₁⟩

/-- The arguments of an application of a definition of two parameters, the last first. -/
theorem args_two {X : Tree} {e : List (Tree × Tree)} {a₁ a₂ : Term} {p₁ p₂ : Tree}
    {R : S → A → Prop} {R₁ : T → B → Prop} {R₂ : T' → C → Prop} {F₁ : S → T} {F₂ : S → T'}
    (h₁ : RepC G n ds ρ a₁ X e p₁ R R₁ F₁) (h₂ : RepC G n ds ρ a₂ X e p₂ R R₂ F₂) :
    ∃ rs : List (Tree × Tree), [a₂, a₁].mapM (fun c ↦ compile G n c X e) = some rs ∧
      rs.map Prod.snd = [p₂, p₁] ∧
      Represents ρ (unfoldTerm sig ds (tuple X (rs.map Prod.fst))) R (Rep.prod R₁ R₂)
        fun s ↦ (F₁ s, F₂ s) :=
  let ⟨f₁, hf₁, hF₁⟩ := h₁
  let ⟨f₂, hf₂, hF₂⟩ := h₂
  ⟨[(f₂, p₂), (f₁, p₁)], by simp [hf₁, hf₂], rfl, by
    change Represents ρ (unfoldTerm sig ds (pair f₁ f₂)) _ _ _
    simp_unfold
    exact represents_pair hF₁ hF₂⟩

/-- The arguments of an application of a definition of three parameters, the last first. -/
theorem args_three {X : Tree} {e : List (Tree × Tree)} {a₁ a₂ a₃ : Term} {p₁ p₂ p₃ : Tree}
    {R : S → A → Prop} {R₁ : T → B → Prop} {R₂ : T' → C → Prop} {R₃ : S' → A' → Prop}
    {F₁ : S → T} {F₂ : S → T'} {F₃ : S → S'} (h₁ : RepC G n ds ρ a₁ X e p₁ R R₁ F₁)
    (h₂ : RepC G n ds ρ a₂ X e p₂ R R₂ F₂) (h₃ : RepC G n ds ρ a₃ X e p₃ R R₃ F₃) :
    ∃ rs : List (Tree × Tree), [a₃, a₂, a₁].mapM (fun c ↦ compile G n c X e) = some rs ∧
      rs.map Prod.snd = [p₃, p₂, p₁] ∧
      Represents ρ (unfoldTerm sig ds (tuple X (rs.map Prod.fst))) R
        (Rep.prod (Rep.prod R₁ R₂) R₃) fun s ↦ ((F₁ s, F₂ s), F₃ s) :=
  let ⟨f₁, hf₁, hF₁⟩ := h₁
  let ⟨f₂, hf₂, hF₂⟩ := h₂
  let ⟨f₃, hf₃, hF₃⟩ := h₃
  ⟨[(f₃, p₃), (f₂, p₂), (f₁, p₁)], by simp [hf₁, hf₂, hf₃], rfl, by
    change Represents ρ (unfoldTerm sig ds (pair (pair f₁ f₂) f₃)) _ _ _
    simp_unfold
    exact represents_pair (represents_pair hF₁ hF₂) hF₃⟩

/-! The definitions and their parameters. -/

/-- A list whose elements a partial function maps has each element's image at its index. -/
theorem mapM_getElem? {α β : Type*} {f : α → Option β} (l : List α) :
    ∀ {rs : List β}, l.mapM f = some rs → ∀ {i : ℕ} {a : α}, l[i]? = some a →
      ∃ r, rs[i]? = some r ∧ f a = some r := by
  refine l.rec (motive := fun l ↦ ∀ {rs : List β}, l.mapM f = some rs → ∀ {i : ℕ} {a : α},
    l[i]? = some a → ∃ r, rs[i]? = some r ∧ f a = some r) ?_ ?_
  · intro _ _ _ _ hb
    simp at hb
  · intro a l ih rs h i b hb
    simp only [List.mapM_cons, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
      Option.some.injEq] at h
    obtain ⟨r, hr, rs', hrs', rfl⟩ := h
    rcases i with _ | i
    · obtain rfl : a = b := by simpa using hb
      exact ⟨r, rfl, hr⟩
    · exact ih hrs' (by simpa using hb)

/-- A definition's arrow among the combinators' definitions its definitions compile to represents
the function its body represents, over the definitions before it, at the parameters'
product. -/
theorem rep_of_body {G : Globals} {ds : List PartialHorn.Defn} (hF : compileDefs G = some ds)
    {k : ℕ} {d : Defn} (hk : G.defs[k]? = some (.language d)) {τ' : List Type}
    {Rp : S → A → Prop} {Rt : T → B → Prop} {Fk : S → T}
    (hb : RepC { G with defs := G.defs.take k } d.arity ds (objs τ') d.body (ctxObj d.params)
      (stdEnv d.params) d.type Rp Rt Fk) :
    ∃ fk, ds[k]? = some ⟨List.replicate d.arity obj, arr, fk⟩ ∧
      Represents (objs τ') (unfoldTerm sig ds fk) Rp Rt Fk := by
  obtain ⟨f, hf, hR⟩ := hb
  obtain ⟨r, hr, hc⟩ := mapM_getElem? _ hF
    (show G.defs.zipIdx[k]? = some (Definition.language d, k) by simp [List.getElem?_zipIdx, hk])
  have hc' : r = ⟨List.replicate d.arity obj, arr, f⟩ := by
    simp only [Definition.compile, Defn.compile, hf, Option.bind_eq_bind, Option.bind_some,
      Option.pure_def] at hc
    split_ifs at hc
    exact (Option.some_inj.mp hc).symm
  exact ⟨f, hr.trans (congrArg some hc'), hR⟩

/-- A definition's arrow represents a function equal, at each argument, to the function its body
represents. -/
theorem rep_of_body' {G : Globals} {ds : List PartialHorn.Defn} (hF : compileDefs G = some ds)
    {k : ℕ} {d : Defn} (hk : G.defs[k]? = some (.language d)) {τ' : List Type}
    {Rp : S → A → Prop} {Rt : T → B → Prop} {Fk Fk' : S → T}
    (hb : RepC { G with defs := G.defs.take k } d.arity ds (objs τ') d.body (ctxObj d.params)
      (stdEnv d.params) d.type Rp Rt Fk) (hFk : ∀ s, Fk s = Fk' s) :
    ∃ fk, ds[k]? = some ⟨List.replicate d.arity obj, arr, fk⟩ ∧
      Represents (objs τ') (unfoldTerm sig ds fk) Rp Rt Fk' :=
  let ⟨fk, h₁, h₂⟩ := rep_of_body hF hk hb
  ⟨fk, h₁, h₂.congr hFk⟩

/-- A definition's arrow represents what its body represents, stated for the arrow the
combinators' definitions give it. -/
theorem rep_def {G : Globals} {ds : List PartialHorn.Defn} (hF : compileDefs G = some ds)
    {k : ℕ} {d : Defn} (hk : G.defs[k]? = some (.language d)) {τ' : List Type}
    {Rp : S → A → Prop} {Rt : T → B → Prop} {Fk Fk' : S → T}
    (hb : RepC { G with defs := G.defs.take k } d.arity ds (objs τ') d.body (ctxObj d.params)
      (stdEnv d.params) d.type Rp Rt Fk) (hFk : ∀ s, Fk s = Fk' s) {fk : Tree}
    (hdk : ds[k]? = some ⟨List.replicate d.arity obj, arr, fk⟩) :
    Represents (objs τ') (unfoldTerm sig ds fk) Rp Rt Fk' := by
  obtain ⟨fk', h₁, h₂⟩ := rep_of_body' hF hk hb hFk
  obtain rfl : fk' = fk := by
    have := h₁.symm.trans hdk
    simp only [Option.some.injEq, PartialHorn.Defn.mk.injEq, true_and] at this
    exact this
  exact h₂

/-- A language definition among a compilation's definitions compiles to an arrow. -/
theorem compiled_language {G : Globals} {ds : List PartialHorn.Defn}
    (hF : compileDefs G = some ds) {k : ℕ} {d : Defn} (hk : G.defs[k]? = some (.language d)) :
    ∃ fk, ds[k]? = some ⟨List.replicate d.arity obj, arr, fk⟩ := by
  obtain ⟨r, hr, hc⟩ := mapM_getElem? _ hF
    (show G.defs.zipIdx[k]? = some (Definition.language d, k) by simp [List.getElem?_zipIdx, hk])
  simp only [Definition.compile, Defn.compile, Option.bind_eq_bind, Option.bind_eq_some_iff,
    Option.pure_def] at hc
  obtain ⟨⟨f, c⟩, -, hc⟩ := hc
  split_ifs at hc
  exact ⟨f, hr.trans hc.symm⟩

/-- The product of no types is the terminal object. -/
theorem ctxObj_nil : ctxObj [] = one := rfl

/-- The product of one type is the type. -/
theorem ctxObj_single (a : Tree) : ctxObj [a] = a := rfl

/-- The product of a type after at least one other is the product of the others' with it. -/
theorem ctxObj_cons_cons (a b : Tree) (Γ : List Tree) :
    ctxObj (a :: b :: Γ) = prod (ctxObj (b :: Γ)) a := rfl

/-- The environment of one parameter represents the identity. -/
theorem envRep_std₁ {p : Tree} (hp : ObjVal ρ (unfoldTerm sig ds p) A) (R : S → A → Prop) :
    EnvRep ds ρ (stdEnv [p]) R [⟨p, S, A, R, id⟩] :=
  envRep_idt hp R

/-- The environment of two parameters, the last first, represents the projections of their
pairs. -/
theorem envRep_std₂ {p₁ p₂ : Tree} (h₁ : ObjVal ρ (unfoldTerm sig ds p₁) A)
    (h₂ : ObjVal ρ (unfoldTerm sig ds p₂) B) (R₁ : S → A → Prop) (R₂ : T → B → Prop) :
    EnvRep ds ρ (stdEnv [p₂, p₁]) (Rep.prod R₁ R₂)
      [⟨p₂, T, B, R₂, Prod.snd⟩, ⟨p₁, S, A, R₁, id ∘ Prod.fst⟩] :=
  envRep_ext h₁ h₂ (envRep_idt h₁ R₁) R₂

/-- The environment of three parameters, the last first, represents the projections of their
tuples. -/
theorem envRep_std₃ {p₁ p₂ p₃ : Tree} (h₁ : ObjVal ρ (unfoldTerm sig ds p₁) A)
    (h₂ : ObjVal ρ (unfoldTerm sig ds p₂) B) (h₃ : ObjVal ρ (unfoldTerm sig ds p₃) C)
    (R₁ : S → A → Prop) (R₂ : T → B → Prop) (R₃ : T' → C → Prop) :
    EnvRep ds ρ (stdEnv [p₃, p₂, p₁]) (Rep.prod (Rep.prod R₁ R₂) R₃)
      [⟨p₃, T', C, R₃, Prod.snd⟩, ⟨p₂, T, B, R₂, Prod.snd ∘ Prod.fst⟩,
        ⟨p₁, S, A, R₁, (id ∘ Prod.fst) ∘ Prod.fst⟩] :=
  envRep_ext (X := prod p₁ p₂) (by simp_unfold; exact eval_prod h₁ h₂) h₃
    (envRep_std₂ h₁ h₂ R₁ R₂) R₃

/-- The application of a definition without parameters, at no objects. -/
theorem repC_call₀ {X : Tree} {e : List (Tree × Tree)} {k : ℕ} {d : Defn} {fk : Tree}
    (hbase : G.base = sig.length) (hk : G.defs[k]? = some (.language d))
    (hwf : PartialHorn.DefnsWF sig ds) (hdk : ds[k]? = some ⟨List.replicate d.arity obj, arr, fk⟩)
    (har : d.arity = 0) (hpar : d.params = []) {a : Tree} (hty : PartialHorn.subst [] d.type = a)
    (hX : ObjVal ρ (unfoldTerm sig ds X) A) {R : S → A → Prop} {Rt : T → B → Prop}
    {Fk : Unit → T} (hfk : Represents [] (unfoldTerm sig ds fk) Rep.unit Rt Fk) :
    RepC G n ds ρ (Term.defn k [] []) X e a R Rt fun _ ↦ Fk () :=
  hty ▸ repC_defn (τ' := []) (args := []) (rs := []) hbase hk hwf hdk (by simp [har]) rfl
    (by simp) .nil hfk rfl (by simp [hpar])
    (by change Represents ρ (unfoldTerm sig ds (bang X)) _ _ _
        simp_unfold
        exact represents_bang hX R)

/-- The application of a definition of one parameter at objects. -/
theorem repC_call₁ {X : Tree} {e : List (Tree × Tree)} {k : ℕ} {θ : List Tree} {d : Defn}
    {fk : Tree} {τ' : List Type} (hbase : G.base = sig.length)
    (hk : G.defs[k]? = some (.language d)) (hwf : PartialHorn.DefnsWF sig ds)
    (hdk : ds[k]? = some ⟨List.replicate d.arity obj, arr, fk⟩) (hθlen : θ.length = d.arity)
    (hθty : θ.all (IsTy G n) = true) (hθops : ∀ u ∈ θ, PartialHorn.OpsBelow sig.length u = true)
    (hθval : List.Forall₂ (fun u A ↦ ObjVal ρ u A) θ τ') {a : Tree}
    (hty : PartialHorn.subst θ d.type = a) {a₁ : Term} {p₁ : Tree}
    (hpar : d.params.map (PartialHorn.subst θ) = [p₁]) {R : S → A → Prop} {R₁ : T → B → Prop}
    {Rt : T' → C → Prop} {F₁ : S → T} {Fk : T → T'}
    (hfk : Represents (objs τ') (unfoldTerm sig ds fk) R₁ Rt Fk)
    (h₁ : RepC G n ds ρ a₁ X e p₁ R R₁ F₁) :
    RepC G n ds ρ (Term.defn k θ [a₁]) X e a R Rt (Fk ∘ F₁) :=
  let ⟨_, hrs, hps, hP⟩ := args_one h₁
  hty ▸ repC_defn hbase hk hwf hdk hθlen hθty hθops hθval hfk hrs (hps.trans hpar.symm) hP

/-- The application of a definition of two parameters at objects, the arguments first first. -/
theorem repC_call₂ {X : Tree} {e : List (Tree × Tree)} {k : ℕ} {θ : List Tree} {d : Defn}
    {fk : Tree} {τ' : List Type} (hbase : G.base = sig.length)
    (hk : G.defs[k]? = some (.language d)) (hwf : PartialHorn.DefnsWF sig ds)
    (hdk : ds[k]? = some ⟨List.replicate d.arity obj, arr, fk⟩) (hθlen : θ.length = d.arity)
    (hθty : θ.all (IsTy G n) = true) (hθops : ∀ u ∈ θ, PartialHorn.OpsBelow sig.length u = true)
    (hθval : List.Forall₂ (fun u A ↦ ObjVal ρ u A) θ τ') {a : Tree}
    (hty : PartialHorn.subst θ d.type = a) {a₁ a₂ : Term} {p₁ p₂ : Tree}
    (hpar : d.params.map (PartialHorn.subst θ) = [p₂, p₁]) {R : S → A → Prop}
    {R₁ : T → B → Prop} {R₂ : T' → C → Prop} {Rt : S' → A' → Prop} {F₁ : S → T} {F₂ : S → T'}
    {Fk : T × T' → S'} (hfk : Represents (objs τ') (unfoldTerm sig ds fk) (Rep.prod R₁ R₂) Rt Fk)
    (h₁ : RepC G n ds ρ a₁ X e p₁ R R₁ F₁) (h₂ : RepC G n ds ρ a₂ X e p₂ R R₂ F₂) :
    RepC G n ds ρ (Term.defn k θ [a₂, a₁]) X e a R Rt
      fun s ↦ Fk (F₁ s, F₂ s) :=
  let ⟨_, hrs, hps, hP⟩ := args_two h₁ h₂
  hty ▸ repC_defn hbase hk hwf hdk hθlen hθty hθops hθval hfk hrs (hps.trans hpar.symm) hP

/-- The application of a definition of three parameters at objects, the arguments first
first. -/
theorem repC_call₃ {X : Tree} {e : List (Tree × Tree)} {k : ℕ} {θ : List Tree} {d : Defn}
    {fk : Tree} {τ' : List Type} (hbase : G.base = sig.length)
    (hk : G.defs[k]? = some (.language d)) (hwf : PartialHorn.DefnsWF sig ds)
    (hdk : ds[k]? = some ⟨List.replicate d.arity obj, arr, fk⟩) (hθlen : θ.length = d.arity)
    (hθty : θ.all (IsTy G n) = true) (hθops : ∀ u ∈ θ, PartialHorn.OpsBelow sig.length u = true)
    (hθval : List.Forall₂ (fun u A ↦ ObjVal ρ u A) θ τ') {a : Tree}
    (hty : PartialHorn.subst θ d.type = a) {a₁ a₂ a₃ : Term} {p₁ p₂ p₃ : Tree}
    (hpar : d.params.map (PartialHorn.subst θ) = [p₃, p₂, p₁]) {R : S → A → Prop}
    {R₁ : T → B → Prop} {R₂ : T' → C → Prop} {R₃ : S' → A' → Prop} {Rt : S'' → A'' → Prop}
    {F₁ : S → T} {F₂ : S → T'} {F₃ : S → S'} {Fk : (T × T') × S' → S''}
    (hfk : Represents (objs τ') (unfoldTerm sig ds fk) (Rep.prod (Rep.prod R₁ R₂) R₃) Rt Fk)
    (h₁ : RepC G n ds ρ a₁ X e p₁ R R₁ F₁) (h₂ : RepC G n ds ρ a₂ X e p₂ R R₂ F₂)
    (h₃ : RepC G n ds ρ a₃ X e p₃ R R₃ F₃) :
    RepC G n ds ρ (Term.defn k θ [a₃, a₂, a₁]) X e a R Rt
      fun s ↦ Fk ((F₁ s, F₂ s), F₃ s) :=
  let ⟨_, hrs, hps, hP⟩ := args_three h₁ h₂ h₃
  hty ▸ repC_defn hbase hk hwf hdk hθlen hθty hθops hθval hfk hrs (hps.trans hpar.symm) hP

end Terms

end Geb.FreeTopos.Internal

end
