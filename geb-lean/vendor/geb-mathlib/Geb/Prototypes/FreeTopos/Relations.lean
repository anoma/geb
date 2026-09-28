/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.FreeTopos.Chosen
public import Geb.Prototypes.RoseTree.Basic
public import Mathlib.Data.Rel

set_option doc.verso true

/-!
# Types and functional relations

The topos of Lean's types, with functional relations as arrows: relations under which each
element of the domain is related to exactly one element of the codomain. The arrow a functional
relation determines is the relation itself, so that the topos has unique choice by construction,
where Lean's types with functions have it only by {lit}`Classical.choice`: the inverse of a
monomorphism's comparison with the pullback of truth along its characteristic map relates an
element of that pullback to the element whose image it is, which a function would have to
choose.

The terminal type is {lit}`Unit`, products are pairs, the equalizer of two functional relations
is the subtype of the elements with one image under both, the initial type is {lit}`Empty`,
coproducts are sums, and the coequalizer of two functional relations is the quotient of their
codomain by the relation relating the images of each element of their domain, a functional
relation descending through it by the equivalence relation that relation generates. The
exponential is the type of functional relations itself, and the subobject classifier is
{lit}`Prop`, an element related by a monomorphism's characteristic map to the proposition that it
is an image. The natural numbers, lists and rose trees fold by relations defined by their
recursors, each functional and unique by induction.

## Main definitions

* {lit}`FunRel` — the functional relations between two types.
* {lit}`FunRel.ofFun` — the graph of a function.
* {lit}`FunRel.comp` — the composite of functional relations.
* {lit}`FunRel.chiInv` — the inverse comparison of a monomorphism, which relates rather than
  chooses.
* {lit}`FunRel.natRec`, {lit}`FunRel.listRec`, {lit}`FunRel.treeRec` — the folds.
* {lit}`relData`, {lit}`relTopos` — the topos of types and functional relations.

## Main statements

* {lit}`FunRel.injective_of_cancel` — a functional relation cancellable on the left relates at
  most one element to each element.
* {lit}`FunRel.eq_chi` — the uniqueness of the characteristic map.
* {lit}`relData_laws` — the laws of a topos with chosen structure and the data objects.

## Tags

functional relation, topos, unique choice, graph of a function, subobject classifier
-/

@[expose] public section

namespace Geb.FreeTopos

open SetRel

/-- A functional relation: a relation under which each element of the domain is related to
exactly one element of the codomain. -/
@[ext] structure FunRel (A B : Type) : Type where
  /-- The relation. -/
  rel : SetRel A B
  /-- Each element of the domain is related to exactly one element of the codomain. -/
  functional : ∀ a, ∃! b, a ~[rel] b

namespace FunRel

variable {A B C D : Type}

/-- Functional relations are equal when the first is contained in the second. -/
theorem ext_of_le {f g : FunRel A B} (h : ∀ a b, a ~[f.rel] b → a ~[g.rel] b) : f = g := by
  ext ⟨a, b⟩
  refine ⟨h a b, fun hg ↦ ?_⟩
  obtain ⟨b', hb', -⟩ := f.functional a
  obtain ⟨c, -, hu⟩ := g.functional a
  obtain rfl := (hu b hg).trans (hu b' (h a b' hb')).symm
  exact hb'

/-- Two elements related to one element by a functional relation are equal. -/
theorem unique (f : FunRel A B) {a : A} {b b' : B} (h : a ~[f.rel] b) (h' : a ~[f.rel] b') :
    b = b' := by
  obtain ⟨c, -, hu⟩ := f.functional a
  exact (hu b h).trans (hu b' h').symm

/-- The graph of a function. -/
def ofFun (f : A → B) : FunRel A B :=
  ⟨Function.graph f, fun a ↦ ⟨f a, rfl, fun _ h ↦ h.symm⟩⟩

/-- The graph of a function relates each element to its image alone. -/
@[simp] theorem mem_ofFun {f : A → B} {a : A} {b : B} : a ~[(ofFun f).rel] b ↔ f a = b := .rfl

/-- The composite of a functional relation after another. -/
def comp (g : FunRel B C) (f : FunRel A B) : FunRel A C :=
  ⟨f.rel ○ g.rel, fun a ↦ by
    obtain ⟨b, hb, hbu⟩ := f.functional a
    obtain ⟨c, hc, hcu⟩ := g.functional b
    exact ⟨c, ⟨b, hb, hc⟩, fun c' ⟨b', hb', hc'⟩ ↦ hcu c' (hbu b' hb' ▸ hc')⟩⟩

/-- A composite relates an element to the image of one of its images. -/
@[simp] theorem mem_comp {g : FunRel B C} {f : FunRel A B} {a : A} {c : C} :
    a ~[(comp g f).rel] c ↔ ∃ b, a ~[f.rel] b ∧ b ~[g.rel] c := .rfl

/-- Composition is associative. -/
theorem comp_assoc (h : FunRel C D) (g : FunRel B C) (f : FunRel A B) :
    comp h (comp g f) = comp (comp h g) f :=
  ext_of_le fun _ _ ⟨c, ⟨b, hb, hc⟩, hd⟩ ↦ ⟨b, hb, c, hc, hd⟩

/-- The graph of the identity is a unit on the right. -/
theorem comp_ofFun_id (f : FunRel A B) : comp f (ofFun id) = f :=
  ext_of_le fun _ _ ⟨_, rfl, hb⟩ ↦ hb

/-- The graph of the identity is a unit on the left. -/
theorem ofFun_id_comp (f : FunRel A B) : comp (ofFun id) f = f :=
  ext_of_le fun _ _ ⟨_, hb, rfl⟩ ↦ hb

variable {X : Type}

/-- The pairing of two functional relations of one domain: an element is related to the pair
of its images. -/
def pair (f : FunRel X A) (g : FunRel X B) : FunRel X (A × B) :=
  ⟨{(x, p) | x ~[f.rel] p.1 ∧ x ~[g.rel] p.2}, fun x ↦ by
    obtain ⟨a, ha, hau⟩ := f.functional x
    obtain ⟨b, hb, hbu⟩ := g.functional x
    exact ⟨(a, b), ⟨ha, hb⟩, fun p hp ↦ Prod.ext (hau p.1 hp.1) (hbu p.2 hp.2)⟩⟩

/-- The equalizer of two functional relations: the elements with one image under both. -/
def Eqz (f g : FunRel A B) : Type := {a : A // ∀ b, a ~[f.rel] b ↔ a ~[g.rel] b}

/-- The factorization through the equalizer of two functional relations of a functional
relation that equalizes them: an element is related to the element of the equalizer that is its
image. -/
def eqLift (f g : FunRel A B) (h : FunRel X A) (hh : comp f h = comp g h) : FunRel X (Eqz f g) :=
  ⟨{(x, e) | x ~[h.rel] e.1}, fun x ↦ by
    obtain ⟨a, ha, hau⟩ := h.functional x
    have hfg : ∀ b, a ~[f.rel] b ↔ a ~[g.rel] b := fun b ↦ by
      have e := congrArg (fun k : FunRel X B ↦ x ~[k.rel] b) hh
      simp only [mem_comp, eq_iff_iff] at e
      exact ⟨fun hb ↦ by
          obtain ⟨a', ha', hg⟩ := e.mp ⟨a, ha, hb⟩
          exact hau a' ha' ▸ hg,
        fun hb ↦ by
          obtain ⟨a', ha', hf⟩ := e.mpr ⟨a, ha, hb⟩
          exact hau a' ha' ▸ hf⟩
    exact ⟨⟨a, hfg⟩, ha, fun e he ↦ Subtype.ext (hau e.1 he)⟩⟩

/-- The copairing of two functional relations of one codomain: an element of the coproduct is
related to the image of the element it injects. -/
def copair (f : FunRel A C) (g : FunRel B C) : FunRel (A ⊕ B) C :=
  ⟨{(s, c) | Sum.elim (fun a ↦ a ~[f.rel] c) (fun b ↦ b ~[g.rel] c) s}, fun s ↦
    s.rec (fun a ↦ f.functional a) fun b ↦ g.functional b⟩

/-- The relation two functional relations generate on their codomain: the images of each
element of the domain. -/
def coeqRel (f g : FunRel A B) (b b' : B) : Prop := ∃ a, a ~[f.rel] b ∧ a ~[g.rel] b'

/-- The coequalizer of two functional relations: their codomain modulo the equivalence relation
generated by relating the images of each element of the domain. -/
def Coeqz (f g : FunRel A B) : Type := Quot (coeqRel f g)

/-- A functional relation that coequalizes two functional relations relates elements the
relation they generate relates to one image. -/
theorem image_iff_of_eqvGen {f g : FunRel A B} {h : FunRel B C} (hh : comp h f = comp h g)
    {b b' : B} (hr : Relation.EqvGen (coeqRel f g) b b') (c : C) :
    b ~[h.rel] c ↔ b' ~[h.rel] c :=
  hr.rec (motive := fun b b' _ ↦ b ~[h.rel] c ↔ b' ~[h.rel] c)
    (fun b b' ⟨a, hb, hb'⟩ ↦ by
      have e := congrArg (fun k : FunRel A C ↦ a ~[k.rel] c) hh
      simp only [mem_comp, eq_iff_iff] at e
      exact ⟨fun hc ↦ by
          obtain ⟨b'', hb'', hc'⟩ := e.mp ⟨b, hb, hc⟩
          exact g.unique hb'' hb' ▸ hc',
        fun hc ↦ by
          obtain ⟨b'', hb'', hc'⟩ := e.mpr ⟨b', hb', hc⟩
          exact f.unique hb'' hb ▸ hc'⟩)
    (fun _ ↦ Iff.rfl) (fun _ _ _ h ↦ h.symm) (fun _ _ _ _ _ h h' ↦ h.trans h')

/-- The descent through the coequalizer of two functional relations of a functional relation
that coequalizes them: a class is related to the image of each of its elements. -/
def coeqDesc (f g : FunRel A B) (h : FunRel B C) (hh : comp h f = comp h g) :
    FunRel (Coeqz f g) C :=
  ⟨{(q, c) | ∃ b, Quot.mk _ b = q ∧ b ~[h.rel] c}, fun q ↦ by
    induction q using Quot.ind with
    | mk b =>
      obtain ⟨c, hc, hcu⟩ := h.functional b
      refine ⟨c, ⟨b, rfl, hc⟩, fun c' ⟨b', hb', hc'⟩ ↦ hcu c' ?_⟩
      exact (image_iff_of_eqvGen hh (Quot.eqvGen_exact hb') c').mp hc'⟩

/-- The evaluation of a functional relation at an element: a pair of a functional relation and
an element is related to the element's image. -/
def ev (A B : Type) : FunRel (FunRel A B × A) B :=
  ⟨{(p, b) | p.2 ~[p.1.rel] b}, fun p ↦ p.1.functional p.2⟩

/-- The functional relation from the second component that a functional relation from a
product determines at a first component. -/
def section' (f : FunRel (C × A) B) (c : C) : FunRel A B :=
  ⟨{(a, b) | (c, a) ~[f.rel] b}, fun a ↦ f.functional (c, a)⟩

/-- The currying of a functional relation from a product: an element is related to the
functional relation it determines. -/
def curry (f : FunRel (C × A) B) : FunRel C (FunRel A B) :=
  ⟨{(c, φ) | φ = section' f c}, fun c ↦ ⟨section' f c, rfl, fun _ h ↦ h⟩⟩

/-- Truth: the element of the terminal type is related to the true propositions. -/
def tru : FunRel Unit Prop :=
  ⟨{q | q.2}, fun _ ↦ ⟨True, trivial, fun _ hp ↦ eq_true hp⟩⟩

/-- The characteristic map of a relation: an element is related to the proposition that it is
an image. -/
def chi (m : FunRel A B) : FunRel B Prop :=
  ⟨{(b, p) | p = ∃ a, a ~[m.rel] b}, fun _ ↦ ⟨_, rfl, fun _ h ↦ h⟩⟩

/-- The arrow to the terminal type. -/
def bang (A : Type) : FunRel A Unit := ofFun fun _ ↦ ()

/-- A functional relation cancellable on the left relates at most one element to each
element. -/
theorem injective_of_cancel {m : FunRel A B}
    (hm : ∀ {X : Type} (f g : FunRel X A), comp m f = comp m g → f = g) {a a' : A} {b : B}
    (h : a ~[m.rel] b) (h' : a' ~[m.rel] b) : a = a' := by
  have e := hm (ofFun fun _ : Unit ↦ a) (ofFun fun _ ↦ a') (ext_of_le fun _ c ⟨x, hx, hc⟩ ↦ by
    subst hx
    exact ⟨a', rfl, m.unique h hc ▸ h'⟩)
  have hrel : ((), a) ∈ (ofFun fun _ : Unit ↦ a').rel :=
    e ▸ (rfl : (fun _ : Unit ↦ a) () = a)
  exact hrel.symm

/-- The inverse comparison of a monomorphism with the pullback of truth along its characteristic
map: an element of the pullback, an image, is related to the element whose image it is. -/
def chiInv (m : FunRel A B) (hm : ∀ {X : Type} (f g : FunRel X A), comp m f = comp m g → f = g) :
    FunRel (Eqz (chi m) (comp tru (bang B))) A :=
  ⟨{(e, a) | a ~[m.rel] e.1}, fun e ↦ by
    have ht := (e.2 True).mpr ⟨(), rfl, trivial⟩
    obtain ⟨a, ha⟩ : ∃ a, a ~[m.rel] e.1 := ht ▸ trivial
    exact ⟨a, ha, fun a' ha' ↦ injective_of_cancel hm ha' ha⟩⟩

/-- The relation the fold of the natural numbers with a start and a step determines, by
recursion. -/
def natRel (z : FunRel Unit C) (s : FunRel C C) (n : ℕ) : C → Prop :=
  Nat.rec (motive := fun _ ↦ C → Prop) (fun c ↦ () ~[z.rel] c)
    (fun _ R c ↦ ∃ c', R c' ∧ c' ~[s.rel] c) n

/-- The fold of the natural numbers relates each to exactly one element. -/
theorem natRel_functional (z : FunRel Unit C) (s : FunRel C C) (n : ℕ) :
    ∃! c, natRel z s n c :=
  Nat.rec (motive := fun n ↦ ∃! c, natRel z s n c) (z.functional _) (fun _ ih ↦ by
    obtain ⟨c', hc', hu'⟩ := ih
    obtain ⟨c, hc, hu⟩ := s.functional c'
    exact ⟨c, ⟨c', hc', hc⟩, fun d ⟨d', hd', hd⟩ ↦ hu d (hu' d' hd' ▸ hd)⟩) n

/-- The fold of the natural numbers with a start and a step. -/
def natRec (z : FunRel Unit C) (s : FunRel C C) : FunRel ℕ C :=
  ⟨{(n, c) | natRel z s n c}, natRel_functional z s⟩

/-- The relation the fold of a list type with a start and a step determines, by recursion. -/
def listRel (z : FunRel Unit C) (s : FunRel (A × C) C) (l : List A) : C → Prop :=
  List.rec (motive := fun _ ↦ C → Prop) (fun c ↦ () ~[z.rel] c)
    (fun a _ R c ↦ ∃ c', R c' ∧ (a, c') ~[s.rel] c) l

/-- The fold of a list type relates each list to exactly one element. -/
theorem listRel_functional (z : FunRel Unit C) (s : FunRel (A × C) C) (l : List A) :
    ∃! c, listRel z s l c :=
  List.rec (motive := fun l ↦ ∃! c, listRel z s l c) (z.functional _) (fun a _ ih ↦ by
    obtain ⟨c', hc', hu'⟩ := ih
    obtain ⟨c, hc, hu⟩ := s.functional (a, c')
    exact ⟨c, ⟨c', hc', hc⟩, fun d ⟨d', hd', hd⟩ ↦ hu d (hu' d' hd' ▸ hd)⟩) l

/-- The fold of a list type with a start and a step. -/
def listRec (A : Type) (z : FunRel Unit C) (s : FunRel (A × C) C) : FunRel (List A) C :=
  ⟨{(l, c) | listRel z s l c}, listRel_functional z s⟩

/-- Relations each holding of exactly one element hold, elementwise, of exactly one list. -/
theorem existsUnique_forall₂ :
    ∀ rs : List (C → Prop), (∀ R ∈ rs, ∃! c, R c) →
      ∃! cs : List C, List.Forall₂ (fun R c ↦ R c) rs cs :=
  List.rec (fun _ ↦ ⟨[], List.Forall₂.nil, fun _ h ↦ List.forall₂_nil_left_iff.mp h⟩)
    fun R rs ih h ↦ by
      obtain ⟨c, hc, hu⟩ := h R List.mem_cons_self
      obtain ⟨cs, hcs, hus⟩ := ih fun R' h' ↦ h R' (List.mem_cons_of_mem _ h')
      refine ⟨c :: cs, List.Forall₂.cons hc hcs, fun ds hds ↦ ?_⟩
      obtain ⟨d, ds', hd, hds', rfl⟩ := List.forall₂_cons_left_iff.mp hds
      rw [hu d hd, hus ds' hds']

/-- The relation the fold of a rose-tree type into an algebra determines, by recursion: a node
is related to the algebra's value at its label and its children's values. -/
def treeRel {L : Type} (f : FunRel (L × List C) C) : RoseTree L → C → Prop :=
  RoseTree.elim fun l rs c ↦ ∃ cs, List.Forall₂ (fun R c ↦ R c) rs cs ∧ (l, cs) ~[f.rel] c

/-- The fold of a rose-tree type relates each tree to exactly one element. -/
theorem treeRel_functional {L : Type} (f : FunRel (L × List C) C) :
    ∀ t : RoseTree L, ∃! c, treeRel f t c :=
  RoseTree.ind fun l ts ih ↦ by
    obtain ⟨cs, hcs, hus⟩ := existsUnique_forall₂ (ts.map (treeRel f)) fun R hR ↦ by
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hR
      exact ih t ht
    obtain ⟨c, hc, hu⟩ := f.functional (l, cs)
    refine ⟨c, ?_, fun d hd ↦ ?_⟩
    · rw [treeRel, RoseTree.elim_node]
      exact ⟨cs, hcs, hc⟩
    · rw [treeRel, RoseTree.elim_node] at hd
      obtain ⟨ds, hds, hd⟩ := hd
      exact hu d (hus ds hds ▸ hd)

/-- The fold of a rose-tree type into an algebra. -/
def treeRec {L : Type} (f : FunRel (L × List C) C) : FunRel (RoseTree L) C :=
  ⟨{(t, c) | treeRel f t c}, treeRel_functional f⟩

/-! The laws. -/

/-- Every functional relation to the terminal type is the arrow to it. -/
theorem eq_bang (f : FunRel A Unit) : f = bang A := ext_of_le fun _ _ _ ↦ rfl

/-- The first projection after a pairing. -/
theorem fst_pair (f : FunRel X A) (g : FunRel X B) : comp (ofFun Prod.fst) (pair f g) = f :=
  ext_of_le fun _ _ ⟨_, ⟨ha, _⟩, h⟩ ↦ h ▸ ha

/-- The second projection after a pairing. -/
theorem snd_pair (f : FunRel X A) (g : FunRel X B) : comp (ofFun Prod.snd) (pair f g) = g :=
  ext_of_le fun _ _ ⟨_, ⟨_, hb⟩, h⟩ ↦ h ▸ hb

/-- A functional relation into a product is the pairing of its projections. -/
theorem pair_eta (h : FunRel X (A × B)) :
    pair (comp (ofFun Prod.fst) h) (comp (ofFun Prod.snd) h) = h :=
  ext_of_le fun _ p ⟨⟨q, hq, h₁⟩, ⟨q', hq', h₂⟩⟩ ↦ by
    obtain rfl := h.unique hq hq'
    exact (Prod.ext h₁ h₂ : q = p) ▸ hq

/-- The inclusion of an equalizer equalizes. -/
theorem eqIncl_eq (f g : FunRel A B) :
    comp f (ofFun (Subtype.val : Eqz f g → A)) = comp g (ofFun Subtype.val) :=
  ext_of_le fun e b ⟨a, ha, hb⟩ ↦ by
    subst ha
    exact ⟨_, rfl, (e.2 b).mp hb⟩

/-- The inclusion of an equalizer after a factorization. -/
theorem eqIncl_eqLift (f g : FunRel A B) (h : FunRel X A) (hh : comp f h = comp g h) :
    comp (ofFun Subtype.val) (eqLift f g h hh) = h :=
  ext_of_le fun _ _ ⟨_, he, hea⟩ ↦ hea ▸ he

/-- A functional relation into an equalizer through whose inclusion a functional relation
factors is its factorization. -/
theorem eq_eqLift (f g : FunRel A B) (h : FunRel X A) (hh : comp f h = comp g h)
    (k : FunRel X (Eqz f g)) (hk : comp (ofFun Subtype.val) k = h) : k = eqLift f g h hh :=
  ext_of_le fun x e hxe ↦ show x ~[h.rel] e.1 from hk ▸ ⟨e, hxe, rfl⟩

/-- Every functional relation from the empty type is the graph of its elimination. -/
theorem eq_absurd (f : FunRel Empty A) : f = ofFun Empty.elim := ext_of_le fun e _ _ ↦ e.elim

/-- A copairing after the first injection. -/
theorem copair_inl (f : FunRel A C) (g : FunRel B C) : comp (copair f g) (ofFun Sum.inl) = f :=
  ext_of_le fun _ _ ⟨_, hs, hc⟩ ↦ by
    subst hs
    exact hc

/-- A copairing after the second injection. -/
theorem copair_inr (f : FunRel A C) (g : FunRel B C) : comp (copair f g) (ofFun Sum.inr) = g :=
  ext_of_le fun _ _ ⟨_, hs, hc⟩ ↦ by
    subst hs
    exact hc

/-- A functional relation from a sum is the copairing of its composites with the
injections. -/
theorem copair_eta (h : FunRel (A ⊕ B) C) :
    copair (comp h (ofFun Sum.inl)) (comp h (ofFun Sum.inr)) = h :=
  ext_of_le fun s c hsc ↦ by
    cases s with
    | inl a =>
      obtain ⟨_, rfl, hc⟩ := hsc
      exact hc
    | inr b =>
      obtain ⟨_, rfl, hc⟩ := hsc
      exact hc

/-- The projection onto a coequalizer coequalizes. -/
theorem coeqProj_eq (f g : FunRel A B) :
    comp (ofFun (Quot.mk (coeqRel f g))) f = comp (ofFun (Quot.mk _)) g :=
  ext_of_le fun a _ ⟨b, hb, hq⟩ ↦ by
    obtain ⟨b', hb', -⟩ := g.functional a
    exact ⟨b', hb', (Quot.sound ⟨a, hb, hb'⟩).symm.trans hq⟩

/-- A descent after the projection onto a coequalizer. -/
theorem coeqDesc_proj (f g : FunRel A B) (h : FunRel B C) (hh : comp h f = comp h g) :
    comp (coeqDesc f g h hh) (ofFun (Quot.mk _)) = h :=
  ext_of_le fun _ c ⟨_, hq, _, hb', hc⟩ ↦
    (image_iff_of_eqvGen hh (Quot.eqvGen_exact (hb'.trans hq.symm)) c).mp hc

/-- A functional relation from a coequalizer whose composite with the projection is a
functional relation is its descent. -/
theorem eq_coeqDesc (f g : FunRel A B) (h : FunRel B C) (hh : comp h f = comp h g)
    (k : FunRel (Coeqz f g) C) (hk : comp k (ofFun (Quot.mk _)) = h) : k = coeqDesc f g h hh :=
  ext_of_le fun q c hqc ↦ by
    induction q using Quot.ind with
    | mk b => exact ⟨b, rfl, hk ▸ ⟨_, rfl, hqc⟩⟩

/-- Evaluation after a currying's product with the exponent. -/
theorem ev_curry (f : FunRel (C × A) B) :
    comp (ev A B) (pair (comp (curry f) (ofFun Prod.fst)) (ofFun Prod.snd)) = f :=
  ext_of_le fun _ _ ⟨⟨_, _⟩, ⟨⟨_, hc, hφ⟩, hs⟩, hb⟩ ↦ by
    subst hc hs
    subst hφ
    exact hb

/-- A functional relation into a type of functional relations is the currying of its
evaluation. -/
theorem curry_eta (h : FunRel C (FunRel A B)) :
    curry (comp (ev A B) (pair (comp h (ofFun Prod.fst)) (ofFun Prod.snd))) = h :=
  ext_of_le fun c φ hcφ ↦ by
    obtain ⟨ψ, hψ, -⟩ := h.functional c
    have e : φ = ψ := hcφ ▸ ext_of_le fun _ _ ⟨⟨_, _⟩, ⟨⟨_, hc', hψ'⟩, ha'⟩, hb⟩ ↦ by
      subst hc' ha'
      obtain rfl := h.unique hψ' hψ
      exact hb
    exact e ▸ hψ

/-- A relation's characteristic map after it is truth. -/
theorem chi_comp (m : FunRel A B) : comp (chi m) m = comp tru (bang A) :=
  ext_of_le fun a _ ⟨_, hb, hp⟩ ↦ ⟨(), rfl, hp ▸ ⟨a, hb⟩⟩

/-- A relation after the inverse comparison of a monomorphism is the inclusion of the pullback
of truth. -/
theorem comp_chiInv (m : FunRel A B)
    (hm : ∀ {X : Type} (f g : FunRel X A), comp m f = comp m g → f = g) :
    comp m (chiInv m hm) = ofFun Subtype.val :=
  ext_of_le fun _ _ ⟨_, ha, hb⟩ ↦ m.unique ha hb

/-- The inverse comparison of a monomorphism after a functional relation whose composite with
the inclusion of the pullback of truth is the monomorphism is the identity. -/
theorem chiInv_comp (m : FunRel A B)
    (hm : ∀ {X : Type} (f g : FunRel X A), comp m f = comp m g → f = g)
    (k : FunRel A (Eqz (chi m) (comp tru (bang B)))) (hk : comp (ofFun Subtype.val) k = m) :
    comp (chiInv m hm) k = ofFun id :=
  ext_of_le fun a _ ⟨e, hke, he⟩ ↦ by
    have h₁ : a ~[(comp (ofFun Subtype.val) k).rel] e.1 := ⟨e, hke, rfl⟩
    rw [hk] at h₁
    exact injective_of_cancel hm h₁ he

/-- A functional relation into propositions along which a monomorphism is the pullback of truth
is its characteristic map. -/
theorem eq_chi (m : FunRel A B) (φ : FunRel B Prop) (k : FunRel A (Eqz φ (comp tru (bang B))))
    (k' : FunRel (Eqz φ (comp tru (bang B))) A) (hk : comp (ofFun Subtype.val) k = m)
    (hkk : comp k k' = ofFun id) : φ = chi m := by
  refine ext_of_le fun b p hbp ↦ ?_
  change p = ∃ a, a ~[m.rel] b
  refine propext ⟨fun hp ↦ ?_, fun ⟨a, ha⟩ ↦ ?_⟩
  · have he : ∀ q, b ~[φ.rel] q ↔ b ~[(comp tru (bang B)).rel] q := fun q ↦
      ⟨fun h ↦ ⟨(), rfl, φ.unique hbp h ▸ hp⟩, fun ⟨_, _, hq⟩ ↦
        (propext ⟨fun _ ↦ hq, fun _ ↦ hp⟩ : p = q) ▸ hbp⟩
    obtain ⟨a, ha, -⟩ := k'.functional ⟨b, he⟩
    obtain ⟨e', he', -⟩ := k.functional a
    have h₁ : (⟨b, he⟩ : Eqz φ _) ~[(comp k k').rel] e' := ⟨a, ha, he'⟩
    rw [hkk] at h₁
    have hee : (⟨b, he⟩ : Eqz φ _) = e' := h₁
    have hm : a ~[m.rel] e'.1 := hk ▸ ⟨e', he', rfl⟩
    rw [← hee] at hm
    exact ⟨a, hm⟩
  · obtain ⟨e, he, -⟩ := k.functional a
    have hae : a ~[m.rel] e.1 := hk ▸ ⟨e, he, rfl⟩
    obtain rfl : b = e.1 := m.unique ha hae
    have ht : e.1 ~[φ.rel] True := (e.2 True).mpr ⟨(), rfl, trivial⟩
    exact φ.unique hbp ht ▸ trivial

/-- The fold of the natural numbers at zero is the start. -/
theorem natRec_zero (z : FunRel Unit C) (s : FunRel C C) :
    comp (natRec z s) (ofFun fun _ ↦ 0) = z :=
  ext_of_le fun _ _ ⟨_, hn, hc⟩ ↦ by
    subst hn
    exact hc

/-- The fold of the natural numbers after the successor is the step after the fold. -/
theorem natRec_succ (z : FunRel Unit C) (s : FunRel C C) :
    comp (natRec z s) (ofFun Nat.succ) = comp s (natRec z s) :=
  ext_of_le fun _ _ ⟨_, hn, hc⟩ ↦ by
    subst hn
    exact hc

/-- A functional relation from the natural numbers with the fold's equations is the fold. -/
theorem eq_natRec (z : FunRel Unit C) (s : FunRel C C) (k : FunRel ℕ C)
    (hz : comp k (ofFun fun _ ↦ 0) = z) (hs : comp k (ofFun Nat.succ) = comp s k) :
    k = natRec z s :=
  ext_of_le fun n c hnc ↦
    Nat.rec (motive := fun n ↦ ∀ c, n ~[k.rel] c → natRel z s n c)
      (fun _ h ↦ hz ▸ ⟨0, rfl, h⟩)
      (fun n ih c h ↦ by
        obtain ⟨c', hc', hc⟩ : n ~[(comp s k).rel] c := hs ▸ ⟨n + 1, rfl, h⟩
        exact ⟨c', ih c' hc', hc⟩) n c hnc

/-- The fold of a list type at the empty list is the start. -/
theorem listRec_nil (z : FunRel Unit C) (s : FunRel (A × C) C) :
    comp (listRec A z s) (ofFun fun _ ↦ []) = z :=
  ext_of_le fun _ _ ⟨_, hl, hc⟩ ↦ by
    subst hl
    exact hc

/-- The fold of a list type after a construction is the step after the fold of the tail. -/
theorem listRec_cons (z : FunRel Unit C) (s : FunRel (A × C) C) :
    comp (listRec A z s) (ofFun fun p : A × List A ↦ p.1 :: p.2) =
      comp s (pair (ofFun Prod.fst) (comp (listRec A z s) (ofFun Prod.snd))) :=
  ext_of_le fun _ _ ⟨_, hl, hc⟩ ↦ by
    subst hl
    obtain ⟨c', hc', hc⟩ := hc
    exact ⟨(_, c'), ⟨rfl, _, rfl, hc'⟩, hc⟩

/-- A functional relation from a list type with the fold's equations is the fold. -/
theorem eq_listRec (z : FunRel Unit C) (s : FunRel (A × C) C) (k : FunRel (List A) C)
    (hz : comp k (ofFun fun _ ↦ []) = z)
    (hs : comp k (ofFun fun p : A × List A ↦ p.1 :: p.2) =
      comp s (pair (ofFun Prod.fst) (comp k (ofFun Prod.snd)))) :
    k = listRec A z s :=
  ext_of_le fun l c hlc ↦
    List.rec (motive := fun l ↦ ∀ c, l ~[k.rel] c → listRel z s l c)
      (fun _ h ↦ hz ▸ ⟨[], rfl, h⟩)
      (fun a l ih c h ↦ by
        obtain ⟨⟨_, c'⟩, ⟨rfl, _, rfl, hc'⟩, hc⟩ :
            (a, l) ~[(comp s (pair (ofFun Prod.fst) (comp k (ofFun Prod.snd)))).rel] c :=
          hs ▸ ⟨a :: l, rfl, h⟩
        exact ⟨c', ih c' hc', hc⟩) l c hlc

/-- The fold that maps a functional relation over lists relates exactly the lists whose
elements it relates, elementwise. -/
theorem listRel_map (g : FunRel A B) :
    ∀ (l : List A) (l' : List B), listRel (ofFun fun _ ↦ [])
      (comp (ofFun fun p : B × List B ↦ p.1 :: p.2)
        (pair (comp g (ofFun Prod.fst)) (ofFun Prod.snd))) l l' ↔
      List.Forall₂ (fun a b ↦ a ~[g.rel] b) l l' :=
  List.rec (fun l' ↦ by
      rw [List.forall₂_nil_left_iff]
      exact ⟨fun h ↦ h.symm, fun h ↦ h.symm⟩)
    fun a l ih l' ↦ by
      rw [List.forall₂_cons_left_iff]
      constructor
      · rintro ⟨c', hc', ⟨b, _⟩, ⟨⟨_, rfl, hb⟩, rfl⟩, rfl⟩
        exact ⟨b, c', hb, (ih c').mp hc', rfl⟩
      · rintro ⟨b, c', hb, hc', rfl⟩
        exact ⟨c', (ih c').mpr hc', (b, c'), ⟨⟨a, rfl, hb⟩, rfl⟩, rfl⟩

/-- A relation that relates each tree of a list to exactly the elements a second relation
relates it to, elementwise, relates the lists the second does. -/
theorem forall₂_imp_mem {L : Type} {R S : RoseTree L → C → Prop} :
    ∀ (ts : List (RoseTree L)) (cs : List C), (∀ t ∈ ts, ∀ c, R t c → S t c) →
      List.Forall₂ R ts cs → List.Forall₂ S ts cs :=
  List.rec (fun _ _ hR ↦ by
      rw [List.forall₂_nil_left_iff] at hR ⊢
      exact hR) fun t ts ih cs h hR ↦ by
    obtain ⟨c, cs', hc, hcs, rfl⟩ := List.forall₂_cons_left_iff.mp hR
    exact List.Forall₂.cons (h t List.mem_cons_self c hc)
      (ih cs' (fun t' h' ↦ h t' (List.mem_cons_of_mem _ h')) hcs)

/-- The fold of a rose-tree type after its structure map is the algebra after the fold of the
children. -/
theorem treeRec_node {L : Type} (f : FunRel (L × List C) C) :
    comp (treeRec f) (ofFun fun p : L × List (RoseTree L) ↦ RoseTree.node p.1 p.2) =
      comp f (pair (ofFun Prod.fst)
        (comp (listRec (RoseTree L) (ofFun fun _ ↦ [])
          (comp (ofFun fun p : C × List C ↦ p.1 :: p.2)
            (pair (comp (treeRec f) (ofFun Prod.fst)) (ofFun Prod.snd)))) (ofFun Prod.snd))) :=
  ext_of_le fun ⟨l, ts⟩ c ⟨_, ht, hc⟩ ↦ by
    subst ht
    change treeRel f (RoseTree.node l ts) c at hc
    rw [treeRel, RoseTree.elim_node] at hc
    obtain ⟨cs, hcs, hc⟩ := hc
    refine ⟨(l, cs), ⟨rfl, ts, rfl, (listRel_map (treeRec f) ts cs).mpr ?_⟩, hc⟩
    exact (List.forall₂_map_left_iff.mp hcs).imp fun _ _ h ↦ h

/-- A functional relation from a rose-tree type with the fold's equation is the fold. -/
theorem eq_treeRec {L : Type} (f : FunRel (L × List C) C) (k : FunRel (RoseTree L) C)
    (hk : comp k (ofFun fun p : L × List (RoseTree L) ↦ RoseTree.node p.1 p.2) =
      comp f (pair (ofFun Prod.fst)
        (comp (listRec (RoseTree L) (ofFun fun _ ↦ [])
          (comp (ofFun fun p : C × List C ↦ p.1 :: p.2)
            (pair (comp k (ofFun Prod.fst)) (ofFun Prod.snd)))) (ofFun Prod.snd)))) :
    k = treeRec f :=
  ext_of_le fun t c htc ↦
    RoseTree.ind (P := fun t ↦ ∀ c, t ~[k.rel] c → treeRel f t c) (fun l ts ih c h ↦ by
      obtain ⟨⟨_, cs⟩, ⟨rfl, _, rfl, hcs⟩, hc⟩ := (hk ▸ ⟨RoseTree.node l ts, rfl, h⟩ :
        (l, ts) ~[(comp f (pair (ofFun Prod.fst)
          (comp (listRec (RoseTree L) (ofFun fun _ ↦ [])
            (comp (ofFun fun p : C × List C ↦ p.1 :: p.2)
              (pair (comp k (ofFun Prod.fst)) (ofFun Prod.snd)))) (ofFun Prod.snd)))).rel] c)
      rw [treeRel, RoseTree.elim_node]
      refine ⟨cs, List.forall₂_map_left_iff.mpr ?_, hc⟩
      exact (forall₂_imp_mem ts cs ih ((listRel_map k ts cs).mp hcs)).imp fun _ _ h ↦ h) t c htc

end FunRel

open FunRel in
/-- The operations of the topos of types and functional relations: the terminal type, products,
subtypes, the empty type, sums, quotients, the types of functional relations, propositions, the
natural numbers, lists and rose trees, with the graphs of their functions and the functional
relations of their universal properties. -/
def relData : ToposData.{1, 0} where
  Obj := Type
  Hom := FunRel
  idt _ := ofFun id
  comp := FunRel.comp
  one := Unit
  bang := FunRel.bang
  prod A B := A × B
  fst _ _ := ofFun Prod.fst
  snd _ _ := ofFun Prod.snd
  pair := FunRel.pair
  eqz := Eqz
  eqIncl _ _ := ofFun Subtype.val
  eqLift := FunRel.eqLift
  zero := Empty
  absurd _ := ofFun Empty.elim
  coprod A B := A ⊕ B
  inl _ _ := ofFun Sum.inl
  inr _ _ := ofFun Sum.inr
  copair := FunRel.copair
  coeqz := Coeqz
  coeqProj _ _ := ofFun (Quot.mk _)
  coeqDesc := FunRel.coeqDesc
  exp := FunRel
  ev := FunRel.ev
  curry := FunRel.curry
  omega := Prop
  tru := FunRel.tru
  chi m _ := FunRel.chi m
  chiInv := FunRel.chiInv
  nat := ℕ
  zeroN := ofFun fun _ ↦ 0
  succ := ofFun Nat.succ
  natRec := FunRel.natRec
  list := List
  nil _ := ofFun fun _ ↦ []
  cons _ := ofFun fun p ↦ p.1 :: p.2
  listRec := FunRel.listRec
  rose := RoseTree ℕ
  node := ofFun fun p ↦ RoseTree.node p.1 p.2
  roseRec := treeRec
  lrose := RoseTree
  lnode _ := ofFun fun p ↦ RoseTree.node p.1 p.2
  lroseRec _ := treeRec

/-- The laws of the topos of types and functional relations. -/
theorem relData_laws : relData.Laws where
  comp_assoc := FunRel.comp_assoc
  comp_idt := FunRel.comp_ofFun_id
  idt_comp := FunRel.ofFun_id_comp
  eq_bang := FunRel.eq_bang
  fst_pair := FunRel.fst_pair
  snd_pair := FunRel.snd_pair
  pair_eta := FunRel.pair_eta
  eqIncl_eq := FunRel.eqIncl_eq
  eqIncl_eqLift := FunRel.eqIncl_eqLift
  eq_eqLift := FunRel.eq_eqLift
  eq_absurd := FunRel.eq_absurd
  copair_inl := FunRel.copair_inl
  copair_inr := FunRel.copair_inr
  copair_eta := FunRel.copair_eta
  coeqProj_eq := FunRel.coeqProj_eq
  coeqDesc_proj := FunRel.coeqDesc_proj
  eq_coeqDesc := FunRel.eq_coeqDesc
  ev_curry := FunRel.ev_curry
  curry_eta := FunRel.curry_eta
  chi_comp m _ := FunRel.chi_comp m
  comp_chiInv := FunRel.comp_chiInv
  chiInv_comp := FunRel.chiInv_comp
  eq_chi m _ φ k k' hk hkk _ := FunRel.eq_chi m φ k k' hk hkk
  natRec_zero := FunRel.natRec_zero
  natRec_succ := FunRel.natRec_succ
  eq_natRec := FunRel.eq_natRec
  listRec_nil _ := FunRel.listRec_nil
  listRec_cons _ := FunRel.listRec_cons
  eq_listRec _ := FunRel.eq_listRec
  roseRec_node := FunRel.treeRec_node
  eq_roseRec := FunRel.eq_treeRec
  lroseRec_lnode _ := FunRel.treeRec_node
  eq_lroseRec _ := FunRel.eq_treeRec

/-- The topos of types and functional relations, with the natural numbers, lists and rose
trees. -/
def relTopos : ChosenTopos.{1, 0} := ⟨relData, relData_laws⟩

end Geb.FreeTopos

end
