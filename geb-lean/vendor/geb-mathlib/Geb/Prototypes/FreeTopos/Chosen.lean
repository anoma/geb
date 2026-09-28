/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Batteries.Tactic.Lint

set_option doc.verso true in
/-!
# Toposes with chosen structure

A topos with chosen structure and the natural numbers, list and rose-tree objects, in dependent
form: the operations of the partial Horn theory {lit}`Geb.FreeTopos.theory`, each an operation on
objects and on the arrows between the objects its typing axioms name, with the theory's
equational axioms as laws. The typing axioms, which state the domains and codomains of the
operations' values and where the operations are defined, hold by the operations' types; an
operation defined only where arrows satisfy an equation, the factorization through an equalizer,
the descent through a coequalizer, the characteristic map of a monomorphism and its inverse
comparison, takes a proof of the equation as an argument.

A universal morphism's uniqueness is stated as the equality with it of every arrow satisfying
its defining equations, and a monomorphism is an arrow cancellable on the left. The inverse
comparison of a monomorphism's characteristic map is stated by its composite with the
monomorphism, the inclusion of the pullback of truth, and by its composite with every arrow
whose composite with that inclusion is the monomorphism, the identity.

## Main definitions

* {lit}`ToposData` — the operations.
* {lit}`ToposData.prodMapLeft`, {lit}`ToposData.prodMapRight`, {lit}`ToposData.listMap`,
  {lit}`ToposData.truthEq`, {lit}`ToposData.truthIncl` — the derived operations the laws name.
* {lit}`ToposData.IsMono` — monomorphisms.
* {lit}`ToposData.Laws` — the laws.
* {lit}`ChosenTopos` — a topos with chosen structure and the data objects.

## Tags

elementary topos, chosen structure, natural numbers object, list object, initial algebra
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

universe u v

/-- The operations of a topos with chosen structure and the natural numbers, list and rose-tree
objects: objects, the arrows between two objects, and the operations of the partial Horn theory
of a topos, each on the arrows between the objects its typing names. -/
@[nolint checkUnivs]
structure ToposData : Type (max (u + 1) (v + 1)) where
  /-- The objects. -/
  Obj : Type u
  /-- The arrows from one object to another. -/
  Hom : Obj → Obj → Type v
  /-- The identity of an object. -/
  idt : (A : Obj) → Hom A A
  /-- The composite of an arrow after another. -/
  comp : {A B C : Obj} → Hom B C → Hom A B → Hom A C
  /-- The terminal object. -/
  one : Obj
  /-- The arrow from an object to the terminal object. -/
  bang : (A : Obj) → Hom A one
  /-- The product of two objects. -/
  prod : Obj → Obj → Obj
  /-- The first projection of a product. -/
  fst : (A B : Obj) → Hom (prod A B) A
  /-- The second projection of a product. -/
  snd : (A B : Obj) → Hom (prod A B) B
  /-- The pairing of two arrows of one domain. -/
  pair : {X A B : Obj} → Hom X A → Hom X B → Hom X (prod A B)
  /-- The equalizer of two parallel arrows. -/
  eqz : {A B : Obj} → Hom A B → Hom A B → Obj
  /-- The inclusion of the equalizer of two parallel arrows. -/
  eqIncl : {A B : Obj} → (f g : Hom A B) → Hom (eqz f g) A
  /-- The factorization through the equalizer of two parallel arrows of an arrow that equalizes
  them. -/
  eqLift : {X A B : Obj} → (f g : Hom A B) → (h : Hom X A) → comp f h = comp g h →
    Hom X (eqz f g)
  /-- The initial object. -/
  zero : Obj
  /-- The arrow from the initial object to an object. -/
  absurd : (A : Obj) → Hom zero A
  /-- The coproduct of two objects. -/
  coprod : Obj → Obj → Obj
  /-- The first injection into a coproduct. -/
  inl : (A B : Obj) → Hom A (coprod A B)
  /-- The second injection into a coproduct. -/
  inr : (A B : Obj) → Hom B (coprod A B)
  /-- The copairing of two arrows of one codomain. -/
  copair : {A B C : Obj} → Hom A C → Hom B C → Hom (coprod A B) C
  /-- The coequalizer of two parallel arrows. -/
  coeqz : {A B : Obj} → Hom A B → Hom A B → Obj
  /-- The projection onto the coequalizer of two parallel arrows. -/
  coeqProj : {A B : Obj} → (f g : Hom A B) → Hom B (coeqz f g)
  /-- The descent through the coequalizer of two parallel arrows of an arrow that coequalizes
  them. -/
  coeqDesc : {A B C : Obj} → (f g : Hom A B) → (h : Hom B C) → comp h f = comp h g →
    Hom (coeqz f g) C
  /-- The exponential, the object of arrows from the first object to the second. -/
  exp : Obj → Obj → Obj
  /-- The evaluation, from the product of an exponential and its exponent. -/
  ev : (A B : Obj) → Hom (prod (exp A B) A) B
  /-- The currying of an arrow from a product. -/
  curry : {C A B : Obj} → Hom (prod C A) B → Hom C (exp A B)
  /-- The subobject classifier. -/
  omega : Obj
  /-- Truth, from the terminal object to the subobject classifier. -/
  tru : Hom one omega
  /-- The characteristic map of a monomorphism. -/
  chi : {A B : Obj} → (m : Hom A B) →
    (∀ {X : Obj} (f g : Hom X A), comp m f = comp m g → f = g) → Hom B omega
  /-- The inverse of a monomorphism's comparison with the pullback of truth along its
  characteristic map. -/
  chiInv : {A B : Obj} → (m : Hom A B) →
    (hm : ∀ {X : Obj} (f g : Hom X A), comp m f = comp m g → f = g) →
    Hom (eqz (chi m hm) (comp tru (bang B))) A
  /-- The natural numbers object. -/
  nat : Obj
  /-- Zero. -/
  zeroN : Hom one nat
  /-- The successor. -/
  succ : Hom nat nat
  /-- The fold of the natural numbers object with a start and a step. -/
  natRec : {C : Obj} → Hom one C → Hom C C → Hom nat C
  /-- The list object of an object. -/
  list : Obj → Obj
  /-- The empty list. -/
  nil : (A : Obj) → Hom one (list A)
  /-- The construction of a list from an element and a list. -/
  cons : (A : Obj) → Hom (prod A (list A)) (list A)
  /-- The fold of a list object with a start and a step. -/
  listRec : {C : Obj} → (A : Obj) → Hom one C → Hom (prod A C) C → Hom (list A) C
  /-- The rose-tree object. -/
  rose : Obj
  /-- The rose-tree object's structure map. -/
  node : Hom (prod nat (list rose)) rose
  /-- The fold of the rose-tree object into an algebra. -/
  roseRec : {C : Obj} → Hom (prod nat (list C)) C → Hom rose C
  /-- The rose-tree object over an object of labels. -/
  lrose : Obj → Obj
  /-- The structure map of the rose-tree object over an object of labels. -/
  lnode : (A : Obj) → Hom (prod A (list (lrose A))) (lrose A)
  /-- The fold of the rose-tree object over an object of labels into an algebra. -/
  lroseRec : {C : Obj} → (A : Obj) → Hom (prod A (list C)) C → Hom (lrose A) C

namespace ToposData

variable (T : ToposData.{u, v})

/-- The arrow {lit}`f × id`, from the product of the domain of {lit}`f` and {lit}`C` to the
product of its codomain and {lit}`C`. -/
def prodMapLeft {A B : T.Obj} (f : T.Hom A B) (C : T.Obj) : T.Hom (T.prod A C) (T.prod B C) :=
  T.pair (T.comp f (T.fst A C)) (T.snd A C)

/-- The arrow {lit}`id × f`, from the product of {lit}`C` and the domain of {lit}`f` to the
product of {lit}`C` and its codomain. -/
def prodMapRight (C : T.Obj) {A B : T.Obj} (f : T.Hom A B) : T.Hom (T.prod C A) (T.prod C B) :=
  T.pair (T.fst C A) (T.comp f (T.snd C A))

/-- The action of the list object on an arrow, by its fold. -/
def listMap {A B : T.Obj} (f : T.Hom A B) : T.Hom (T.list A) (T.list B) :=
  T.listRec A (T.nil B) (T.comp (T.cons B) (T.prodMapLeft f (T.list B)))

/-- The pullback of truth along an arrow into the subobject classifier, the equalizer of the
arrow and truth after the arrow to the terminal object. -/
def truthEq {B : T.Obj} (φ : T.Hom B T.omega) : T.Obj := T.eqz φ (T.comp T.tru (T.bang B))

/-- The inclusion of the pullback of truth along an arrow into the subobject classifier. -/
def truthIncl {B : T.Obj} (φ : T.Hom B T.omega) : T.Hom (T.truthEq φ) B :=
  T.eqIncl φ (T.comp T.tru (T.bang B))

/-- A monomorphism: an arrow cancellable on the left. -/
def IsMono {A B : T.Obj} (m : T.Hom A B) : Prop :=
  ∀ {X : T.Obj} (f g : T.Hom X A), T.comp m f = T.comp m g → f = g

/-- The laws of a topos with chosen structure and the data objects: those of a category, and
of each universal morphism its defining equations and its uniqueness. -/
structure Laws : Prop where
  /-- Composition is associative. -/
  comp_assoc : ∀ {A B C D : T.Obj} (h : T.Hom C D) (g : T.Hom B C) (f : T.Hom A B),
    T.comp h (T.comp g f) = T.comp (T.comp h g) f
  /-- The identity is a unit on the right. -/
  comp_idt : ∀ {A B : T.Obj} (f : T.Hom A B), T.comp f (T.idt A) = f
  /-- The identity is a unit on the left. -/
  idt_comp : ∀ {A B : T.Obj} (f : T.Hom A B), T.comp (T.idt B) f = f
  /-- Every arrow to the terminal object is the chosen one. -/
  eq_bang : ∀ {A : T.Obj} (f : T.Hom A T.one), f = T.bang A
  /-- The first projection after a pairing. -/
  fst_pair : ∀ {X A B : T.Obj} (f : T.Hom X A) (g : T.Hom X B),
    T.comp (T.fst A B) (T.pair f g) = f
  /-- The second projection after a pairing. -/
  snd_pair : ∀ {X A B : T.Obj} (f : T.Hom X A) (g : T.Hom X B),
    T.comp (T.snd A B) (T.pair f g) = g
  /-- An arrow into a product is the pairing of its projections. -/
  pair_eta : ∀ {X A B : T.Obj} (h : T.Hom X (T.prod A B)),
    T.pair (T.comp (T.fst A B) h) (T.comp (T.snd A B) h) = h
  /-- The inclusion of an equalizer equalizes. -/
  eqIncl_eq : ∀ {A B : T.Obj} (f g : T.Hom A B),
    T.comp f (T.eqIncl f g) = T.comp g (T.eqIncl f g)
  /-- The inclusion of an equalizer after a factorization. -/
  eqIncl_eqLift : ∀ {X A B : T.Obj} (f g : T.Hom A B) (h : T.Hom X A)
    (hh : T.comp f h = T.comp g h), T.comp (T.eqIncl f g) (T.eqLift f g h hh) = h
  /-- An arrow into an equalizer through whose inclusion an arrow factors is its factorization. -/
  eq_eqLift : ∀ {X A B : T.Obj} (f g : T.Hom A B) (h : T.Hom X A)
    (hh : T.comp f h = T.comp g h) (k : T.Hom X (T.eqz f g)),
    T.comp (T.eqIncl f g) k = h → k = T.eqLift f g h hh
  /-- Every arrow from the initial object is the chosen one. -/
  eq_absurd : ∀ {A : T.Obj} (f : T.Hom T.zero A), f = T.absurd A
  /-- A copairing after the first injection. -/
  copair_inl : ∀ {A B C : T.Obj} (f : T.Hom A C) (g : T.Hom B C),
    T.comp (T.copair f g) (T.inl A B) = f
  /-- A copairing after the second injection. -/
  copair_inr : ∀ {A B C : T.Obj} (f : T.Hom A C) (g : T.Hom B C),
    T.comp (T.copair f g) (T.inr A B) = g
  /-- An arrow from a coproduct is the copairing of its composites with the injections. -/
  copair_eta : ∀ {A B C : T.Obj} (h : T.Hom (T.coprod A B) C),
    T.copair (T.comp h (T.inl A B)) (T.comp h (T.inr A B)) = h
  /-- The projection onto a coequalizer coequalizes. -/
  coeqProj_eq : ∀ {A B : T.Obj} (f g : T.Hom A B),
    T.comp (T.coeqProj f g) f = T.comp (T.coeqProj f g) g
  /-- A descent after the projection onto a coequalizer. -/
  coeqDesc_proj : ∀ {A B C : T.Obj} (f g : T.Hom A B) (h : T.Hom B C)
    (hh : T.comp h f = T.comp h g), T.comp (T.coeqDesc f g h hh) (T.coeqProj f g) = h
  /-- An arrow from a coequalizer whose composite with the projection is an arrow is its
  descent. -/
  eq_coeqDesc : ∀ {A B C : T.Obj} (f g : T.Hom A B) (h : T.Hom B C)
    (hh : T.comp h f = T.comp h g) (k : T.Hom (T.coeqz f g) C),
    T.comp k (T.coeqProj f g) = h → k = T.coeqDesc f g h hh
  /-- Evaluation after a currying's product with the exponent. -/
  ev_curry : ∀ {C A B : T.Obj} (f : T.Hom (T.prod C A) B),
    T.comp (T.ev A B) (T.prodMapLeft (T.curry f) A) = f
  /-- An arrow into an exponential is the currying of its evaluation. -/
  curry_eta : ∀ {C A B : T.Obj} (h : T.Hom C (T.exp A B)),
    T.curry (T.comp (T.ev A B) (T.prodMapLeft h A)) = h
  /-- A monomorphism's characteristic map after it is truth. -/
  chi_comp : ∀ {A B : T.Obj} (m : T.Hom A B) (hm : T.IsMono m),
    T.comp (T.chi m hm) m = T.comp T.tru (T.bang A)
  /-- A monomorphism after the inverse comparison is the inclusion of the pullback of truth. -/
  comp_chiInv : ∀ {A B : T.Obj} (m : T.Hom A B) (hm : T.IsMono m),
    T.comp m (T.chiInv m hm) = T.truthIncl (T.chi m hm)
  /-- The inverse comparison after an arrow whose composite with the inclusion of the pullback
  of truth is the monomorphism is the identity. -/
  chiInv_comp : ∀ {A B : T.Obj} (m : T.Hom A B) (hm : T.IsMono m)
    (k : T.Hom A (T.truthEq (T.chi m hm))), T.comp (T.truthIncl (T.chi m hm)) k = m →
    T.comp (T.chiInv m hm) k = T.idt A
  /-- An arrow into the subobject classifier along which a monomorphism is the pullback of truth
  is its characteristic map. -/
  eq_chi : ∀ {A B : T.Obj} (m : T.Hom A B) (hm : T.IsMono m) (φ : T.Hom B T.omega)
    (k : T.Hom A (T.truthEq φ)) (k' : T.Hom (T.truthEq φ) A), T.comp (T.truthIncl φ) k = m →
    T.comp k k' = T.idt (T.truthEq φ) → T.comp k' k = T.idt A → φ = T.chi m hm
  /-- The fold of the natural numbers at zero is the start. -/
  natRec_zero : ∀ {C : T.Obj} (z : T.Hom T.one C) (s : T.Hom C C),
    T.comp (T.natRec z s) T.zeroN = z
  /-- The fold of the natural numbers after the successor is the step after the fold. -/
  natRec_succ : ∀ {C : T.Obj} (z : T.Hom T.one C) (s : T.Hom C C),
    T.comp (T.natRec z s) T.succ = T.comp s (T.natRec z s)
  /-- An arrow from the natural numbers with the fold's equations is the fold. -/
  eq_natRec : ∀ {C : T.Obj} (z : T.Hom T.one C) (s : T.Hom C C) (k : T.Hom T.nat C),
    T.comp k T.zeroN = z → T.comp k T.succ = T.comp s k → k = T.natRec z s
  /-- The fold of a list object at the empty list is the start. -/
  listRec_nil : ∀ {C : T.Obj} (A : T.Obj) (z : T.Hom T.one C) (s : T.Hom (T.prod A C) C),
    T.comp (T.listRec A z s) (T.nil A) = z
  /-- The fold of a list object after a construction is the step after the fold of the tail. -/
  listRec_cons : ∀ {C : T.Obj} (A : T.Obj) (z : T.Hom T.one C) (s : T.Hom (T.prod A C) C),
    T.comp (T.listRec A z s) (T.cons A) = T.comp s (T.prodMapRight A (T.listRec A z s))
  /-- An arrow from a list object with the fold's equations is the fold. -/
  eq_listRec : ∀ {C : T.Obj} (A : T.Obj) (z : T.Hom T.one C) (s : T.Hom (T.prod A C) C)
    (k : T.Hom (T.list A) C), T.comp k (T.nil A) = z →
    T.comp k (T.cons A) = T.comp s (T.prodMapRight A k) → k = T.listRec A z s
  /-- The fold of the rose-tree object after its structure map is the algebra after the fold of
  the children. -/
  roseRec_node : ∀ {C : T.Obj} (f : T.Hom (T.prod T.nat (T.list C)) C),
    T.comp (T.roseRec f) T.node = T.comp f (T.prodMapRight T.nat (T.listMap (T.roseRec f)))
  /-- An arrow from the rose-tree object with the fold's equation is the fold. -/
  eq_roseRec : ∀ {C : T.Obj} (f : T.Hom (T.prod T.nat (T.list C)) C) (k : T.Hom T.rose C),
    T.comp k T.node = T.comp f (T.prodMapRight T.nat (T.listMap k)) → k = T.roseRec f
  /-- The fold of a rose-tree object over labels after its structure map is the algebra after
  the fold of the children. -/
  lroseRec_lnode : ∀ {C : T.Obj} (A : T.Obj) (f : T.Hom (T.prod A (T.list C)) C),
    T.comp (T.lroseRec A f) (T.lnode A) =
      T.comp f (T.prodMapRight A (T.listMap (T.lroseRec A f)))
  /-- An arrow from a rose-tree object over labels with the fold's equation is the fold. -/
  eq_lroseRec : ∀ {C : T.Obj} (A : T.Obj) (f : T.Hom (T.prod A (T.list C)) C)
    (k : T.Hom (T.lrose A) C),
    T.comp k (T.lnode A) = T.comp f (T.prodMapRight A (T.listMap k)) → k = T.lroseRec A f

end ToposData

/-- A topos with chosen structure and the natural numbers, list and rose-tree objects: the
operations with their laws. -/
@[nolint checkUnivs]
structure ChosenTopos : Type (max (u + 1) (v + 1)) extends ToposData.{u, v} where
  /-- The laws. -/
  laws : toToposData.Laws

end Geb.FreeTopos

end
