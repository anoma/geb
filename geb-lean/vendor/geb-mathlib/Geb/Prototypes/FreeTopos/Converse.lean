/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.FreeTopos.Chosen
public import Geb.Prototypes.FreeTopos.Theory
public import Mathlib.Data.Part
import Mathlib.Tactic.IntervalCases

set_option doc.verso true in
/-!
# The model of a topos with chosen structure

The converse of every model's being an elementary topos: a topos with chosen structure and the data
objects ({name}`Geb.FreeTopos.ChosenTopos`) is a model of the partial Horn theory of a topos. The
values of the model's sort of objects are the topos's objects, and those of its sort of arrows are
the arrows with their domains and codomains. Each operation is defined exactly where the theory's
typing axioms make it defined: at arrows whose domains and codomains are the objects its typing
names, its arguments cast along those equations, and, for the factorization through an equalizer,
the descent through a coequalizer and the characteristic map with its inverse comparison, where the
equation or the cancellability the operation needs holds.

## Main definitions

* {lit}`ChosenTopos.Car` — the model's values of each sort.
* {lit}`ChosenTopos.castHom` — an arrow cast along equations of its domain and codomain.
* {lit}`ChosenTopos.op` — the model's operations.
* {lit}`ChosenTopos.model` — the model.

## Main statements

* {lit}`ChosenTopos.op_sort` — each operation's values have its result sort.
* {lit}`ChosenTopos.isMono_of_kernelPair`, {lit}`ChosenTopos.kernelPair_fst_eq_snd` — an arrow
  is a monomorphism exactly when the projections of its kernel pair are equal.
* {lit}`ChosenTopos.isModel` — the model satisfies every axiom of the theory.

## Implementation notes

The validity of each axiom is proved by one procedure: the assignment is introduced value by
value; each hypothesis is evaluated and decomposed into equations of objects and of arrows, and
an equation one side of which is a variable is substituted; the conclusion is evaluated, the
definedness condition of each operation in it discharged, and the resulting equation proved by
the laws, or by the law of uniqueness of a universal morphism. The values of each sort are
defined by recursion on the sort's index, so that simplification reduces them, and the equations
of values of a sort are stated at that sort's type, the type evaluation produces.

## Tags

elementary topos, model, partial Horn logic, chosen structure
-/

set_option doc.verso true

@[expose] public section

namespace Geb.FreeTopos

open PartialHorn Sorts

universe u v

namespace ChosenTopos

variable (T : ChosenTopos.{u, v})

/-- The values of each sort: the objects, lifted to the arrows' universe, and the arrows with
their domains and codomains. -/
@[reducible] def Car (s : ℕ) : Type (max u v) :=
  Nat.casesOn s (ULift.{v} T.Obj) fun _ ↦ Σ A B : T.Obj, T.Hom A B

variable {T}

/-- An arrow cast along equations of its domain and of its codomain. -/
abbrev castHom {A A' B B' : T.Obj} (hA : A = A') (hB : B = B') (f : T.Hom A B) : T.Hom A' B' :=
  Eq.rec (motive := fun X _ ↦ T.Hom X B') (Eq.rec (motive := fun Y _ ↦ T.Hom A Y) f hB) hA

variable (T)

/-- The model's operations, by index: each defined exactly where the theory's typing axioms make
it defined, at arguments of the sorts the signature names. -/
def op : ℕ → List (Σ s, T.Car s) → Part (Σ s, T.Car s)
  | 0, args => match args with
    | [⟨arr, ⟨A, _, _⟩⟩] => Part.some ⟨obj, ⟨A⟩⟩
    | _ => Part.none
  | 1, args => match args with
    | [⟨arr, ⟨_, B, _⟩⟩] => Part.some ⟨obj, ⟨B⟩⟩
    | _ => Part.none
  | 2, args => match args with
    | [⟨obj, ⟨A⟩⟩] => Part.some ⟨arr, ⟨A, A, T.idt A⟩⟩
    | _ => Part.none
  | 3, args => match args with
    | [⟨arr, ⟨B', C, g⟩⟩, ⟨arr, ⟨A, B, f⟩⟩] =>
      ⟨B = B', fun h ↦ ⟨arr, ⟨A, C, T.comp g (castHom rfl h f)⟩⟩⟩
    | _ => Part.none
  | 4, args => match args with
    | [] => Part.some ⟨obj, ⟨T.one⟩⟩
    | _ => Part.none
  | 5, args => match args with
    | [⟨obj, ⟨A⟩⟩] => Part.some ⟨arr, ⟨A, T.one, T.bang A⟩⟩
    | _ => Part.none
  | 6, args => match args with
    | [⟨obj, ⟨A⟩⟩, ⟨obj, ⟨B⟩⟩] => Part.some ⟨obj, ⟨T.prod A B⟩⟩
    | _ => Part.none
  | 7, args => match args with
    | [⟨obj, ⟨A⟩⟩, ⟨obj, ⟨B⟩⟩] => Part.some ⟨arr, ⟨T.prod A B, A, T.fst A B⟩⟩
    | _ => Part.none
  | 8, args => match args with
    | [⟨obj, ⟨A⟩⟩, ⟨obj, ⟨B⟩⟩] => Part.some ⟨arr, ⟨T.prod A B, B, T.snd A B⟩⟩
    | _ => Part.none
  | 9, args => match args with
    | [⟨arr, ⟨X, A, f⟩⟩, ⟨arr, ⟨X', B, g⟩⟩] =>
      ⟨X = X', fun h ↦ ⟨arr, ⟨X', T.prod A B, T.pair (castHom h rfl f) g⟩⟩⟩
    | _ => Part.none
  | 10, args => match args with
    | [⟨arr, ⟨A, B, f⟩⟩, ⟨arr, ⟨A', B', g⟩⟩] =>
      ⟨A' = A ∧ B' = B, fun h ↦ ⟨obj, ⟨T.eqz f (castHom h.1 h.2 g)⟩⟩⟩
    | _ => Part.none
  | 11, args => match args with
    | [⟨arr, ⟨A, B, f⟩⟩, ⟨arr, ⟨A', B', g⟩⟩] =>
      ⟨A' = A ∧ B' = B, fun h ↦ ⟨arr, ⟨_, A, T.eqIncl f (castHom h.1 h.2 g)⟩⟩⟩
    | _ => Part.none
  | 12, args => match args with
    | [⟨arr, ⟨A, B, f⟩⟩, ⟨arr, ⟨A', B', g⟩⟩, ⟨arr, ⟨X, C, k⟩⟩] =>
      ⟨∃ (h : A' = A ∧ B' = B) (hC : C = A),
          T.comp f (castHom rfl hC k) = T.comp (castHom h.1 h.2 g) (castHom rfl hC k),
        fun h ↦ ⟨arr, ⟨X, _, T.eqLift f (castHom h.fst.1 h.fst.2 g) (castHom rfl h.snd.fst k)
          h.snd.snd⟩⟩⟩
    | _ => Part.none
  | 13, args => match args with
    | [] => Part.some ⟨obj, ⟨T.zero⟩⟩
    | _ => Part.none
  | 14, args => match args with
    | [⟨obj, ⟨A⟩⟩] => Part.some ⟨arr, ⟨T.zero, A, T.absurd A⟩⟩
    | _ => Part.none
  | 15, args => match args with
    | [⟨obj, ⟨A⟩⟩, ⟨obj, ⟨B⟩⟩] => Part.some ⟨obj, ⟨T.coprod A B⟩⟩
    | _ => Part.none
  | 16, args => match args with
    | [⟨obj, ⟨A⟩⟩, ⟨obj, ⟨B⟩⟩] => Part.some ⟨arr, ⟨A, T.coprod A B, T.inl A B⟩⟩
    | _ => Part.none
  | 17, args => match args with
    | [⟨obj, ⟨A⟩⟩, ⟨obj, ⟨B⟩⟩] => Part.some ⟨arr, ⟨B, T.coprod A B, T.inr A B⟩⟩
    | _ => Part.none
  | 18, args => match args with
    | [⟨arr, ⟨A, C, f⟩⟩, ⟨arr, ⟨B, C', g⟩⟩] =>
      ⟨C' = C, fun h ↦ ⟨arr, ⟨T.coprod A B, C, T.copair f (castHom rfl h g)⟩⟩⟩
    | _ => Part.none
  | 19, args => match args with
    | [⟨arr, ⟨A, B, f⟩⟩, ⟨arr, ⟨A', B', g⟩⟩] =>
      ⟨A' = A ∧ B' = B, fun h ↦ ⟨obj, ⟨T.coeqz f (castHom h.1 h.2 g)⟩⟩⟩
    | _ => Part.none
  | 20, args => match args with
    | [⟨arr, ⟨A, B, f⟩⟩, ⟨arr, ⟨A', B', g⟩⟩] =>
      ⟨A' = A ∧ B' = B, fun h ↦ ⟨arr, ⟨B, _, T.coeqProj f (castHom h.1 h.2 g)⟩⟩⟩
    | _ => Part.none
  | 21, args => match args with
    | [⟨arr, ⟨A, B, f⟩⟩, ⟨arr, ⟨A', B', g⟩⟩, ⟨arr, ⟨B'', C, k⟩⟩] =>
      ⟨∃ (h : A' = A ∧ B' = B) (hB : B'' = B),
          T.comp (castHom hB rfl k) f = T.comp (castHom hB rfl k) (castHom h.1 h.2 g),
        fun h ↦ ⟨arr, ⟨_, C, T.coeqDesc f (castHom h.fst.1 h.fst.2 g) (castHom h.snd.fst rfl k)
          h.snd.snd⟩⟩⟩
    | _ => Part.none
  | 22, args => match args with
    | [⟨obj, ⟨A⟩⟩, ⟨obj, ⟨B⟩⟩] => Part.some ⟨obj, ⟨T.exp A B⟩⟩
    | _ => Part.none
  | 23, args => match args with
    | [⟨obj, ⟨A⟩⟩, ⟨obj, ⟨B⟩⟩] =>
      Part.some ⟨arr, ⟨T.prod (T.exp A B) A, B, T.ev A B⟩⟩
    | _ => Part.none
  | 24, args => match args with
    | [⟨obj, ⟨C⟩⟩, ⟨obj, ⟨A⟩⟩, ⟨arr, ⟨D, B, f⟩⟩] =>
      ⟨D = T.prod C A, fun h ↦ ⟨arr, ⟨C, T.exp A B, T.curry (castHom h rfl f)⟩⟩⟩
    | _ => Part.none
  | 25, args => match args with
    | [] => Part.some ⟨obj, ⟨T.omega⟩⟩
    | _ => Part.none
  | 26, args => match args with
    | [] => Part.some ⟨arr, ⟨T.one, T.omega, T.tru⟩⟩
    | _ => Part.none
  | 27, args => match args with
    | [⟨arr, ⟨_, B, m⟩⟩] => ⟨T.IsMono m, fun h ↦ ⟨arr, ⟨B, T.omega, T.chi m h⟩⟩⟩
    | _ => Part.none
  | 28, args => match args with
    | [⟨arr, ⟨A, _, m⟩⟩] => ⟨T.IsMono m, fun h ↦ ⟨arr, ⟨_, A, T.chiInv m h⟩⟩⟩
    | _ => Part.none
  | 29, args => match args with
    | [] => Part.some ⟨obj, ⟨T.nat⟩⟩
    | _ => Part.none
  | 30, args => match args with
    | [] => Part.some ⟨arr, ⟨T.one, T.nat, T.zeroN⟩⟩
    | _ => Part.none
  | 31, args => match args with
    | [] => Part.some ⟨arr, ⟨T.nat, T.nat, T.succ⟩⟩
    | _ => Part.none
  | 32, args => match args with
    | [⟨arr, ⟨O, C, z⟩⟩, ⟨arr, ⟨C', C'', s⟩⟩] =>
      ⟨O = T.one ∧ C' = C ∧ C'' = C,
        fun h ↦ ⟨arr, ⟨T.nat, C, T.natRec (castHom h.1 rfl z) (castHom h.2.1 h.2.2 s)⟩⟩⟩
    | _ => Part.none
  | 33, args => match args with
    | [⟨obj, ⟨A⟩⟩] => Part.some ⟨obj, ⟨T.list A⟩⟩
    | _ => Part.none
  | 34, args => match args with
    | [⟨obj, ⟨A⟩⟩] => Part.some ⟨arr, ⟨T.one, T.list A, T.nil A⟩⟩
    | _ => Part.none
  | 35, args => match args with
    | [⟨obj, ⟨A⟩⟩] => Part.some ⟨arr, ⟨T.prod A (T.list A), T.list A, T.cons A⟩⟩
    | _ => Part.none
  | 36, args => match args with
    | [⟨obj, ⟨A⟩⟩, ⟨arr, ⟨O, C, z⟩⟩, ⟨arr, ⟨D, C', s⟩⟩] =>
      ⟨O = T.one ∧ C' = C ∧ D = T.prod A C,
        fun h ↦ ⟨arr, ⟨T.list A, C, T.listRec A (castHom h.1 rfl z) (castHom h.2.2 h.2.1 s)⟩⟩⟩
    | _ => Part.none
  | 37, args => match args with
    | [] => Part.some ⟨obj, ⟨T.rose⟩⟩
    | _ => Part.none
  | 38, args => match args with
    | [] => Part.some ⟨arr, ⟨T.prod T.nat (T.list T.rose), T.rose, T.node⟩⟩
    | _ => Part.none
  | 39, args => match args with
    | [⟨arr, ⟨D, C, f⟩⟩] =>
      ⟨D = T.prod T.nat (T.list C), fun h ↦ ⟨arr, ⟨T.rose, C, T.roseRec (castHom h rfl f)⟩⟩⟩
    | _ => Part.none
  | 40, args => match args with
    | [⟨obj, ⟨A⟩⟩] => Part.some ⟨obj, ⟨T.lrose A⟩⟩
    | _ => Part.none
  | 41, args => match args with
    | [⟨obj, ⟨A⟩⟩] =>
      Part.some ⟨arr, ⟨T.prod A (T.list (T.lrose A)), T.lrose A, T.lnode A⟩⟩
    | _ => Part.none
  | 42, args => match args with
    | [⟨obj, ⟨A⟩⟩, ⟨arr, ⟨D, C, f⟩⟩] =>
      ⟨D = T.prod A (T.list C),
        fun h ↦ ⟨arr, ⟨T.lrose A, C, T.lroseRec A (castHom h rfl f)⟩⟩⟩
    | _ => Part.none
  | _, _ => Part.none

/-- A value of an operation has the operation's result sort. -/
theorem op_sort {k : ℕ} {args : List (Σ s, T.Car s)} {w : Σ s, T.Car s} (hw : w ∈ T.op k args) :
    (sig[k]?).map Prod.snd = some w.1 := by
  by_cases hk : k < 43
  · interval_cases k <;> simp only [op] at hw <;> split at hw <;>
      first
      | exact (Part.notMem_none _ hw).elim
      | (obtain rfl := Part.mem_some_iff.mp hw; rfl)
      | (obtain ⟨_, rfl⟩ := hw; rfl)
  · obtain ⟨k, rfl⟩ : ∃ j, k = j + 43 := ⟨k - 43, by omega⟩
    simp only [op] at hw
    exact (Part.notMem_none _ hw).elim

/-- The model of the theory a topos with chosen structure is. -/
abbrev model : Model.{max u v} sig where
  Car := T.Car
  op := T.op
  op_sort := T.op_sort

variable {T}

/-- A value of a partial value given by its domain and its function is the function's value at
a proof of the domain. -/
theorem mem_mk {α : Type*} {p : Prop} {f : p → α} {a : α} :
    a ∈ (⟨p, f⟩ : Part α) ↔ ∃ h, f h = a := Iff.rfl

/-- A partial value whose domain holds is the function's value at its proof. -/
theorem mk_eq_some {α : Type*} {p : Prop} {f : p → α} (h : p) :
    (⟨p, f⟩ : Part α) = Part.some (f h) := Part.eq_some_iff.mpr ⟨h, rfl⟩

/-- Two objects are equal as values of the sort of objects exactly when they are equal. -/
theorem obj_car_eq_iff {A B : T.Obj} : @Eq (T.Car obj) ⟨A⟩ ⟨B⟩ ↔ A = B :=
  ⟨congrArg ULift.down, congrArg ULift.up⟩

/-- Two arrows are equal as values of the sort of arrows exactly when their domains are equal
and, along that equation, their codomains and the arrows. -/
theorem arr_car_eq_iff {A A' B B' : T.Obj} {f : T.Hom A B} {g : T.Hom A' B'} :
    @Eq (T.Car arr) ⟨A, B, f⟩ ⟨A', B', g⟩ ↔
      A = A' ∧ HEq (⟨B, f⟩ : Σ B, T.Hom A B) (⟨B', g⟩ : Σ B, T.Hom A' B) :=
  Sigma.mk.inj_iff

/-- Two arrows of one domain and codomain equal as sorted values are equal. -/
theorem eq_of_arr_eq {A B : T.Obj} {f g : T.Hom A B}
    (h : (⟨arr, ⟨A, B, f⟩⟩ : Σ s, T.Car s) = ⟨arr, ⟨A, B, g⟩⟩) : f = g := by
  cases h
  rfl

/-- The pairing of an arrow after the first projection with the second projection is the arrow
times the identity. -/
theorem pair_comp_fst_snd {A B : T.Obj} (f : T.Hom A B) (C : T.Obj) :
    T.pair (T.comp f (T.fst A C)) (T.snd A C) = T.prodMapLeft f C := rfl

/-- The pairing of the first projection with an arrow after the second projection is the
identity times the arrow. -/
theorem pair_fst_comp_snd (C : T.Obj) {A B : T.Obj} (f : T.Hom A B) :
    T.pair (T.fst C A) (T.comp f (T.snd C A)) = T.prodMapRight C f := rfl

/-- The fold of a list object into the list object of another object, whose step conses the
image of each element under an arrow, is the action of the list object on the arrow. -/
theorem listRec_nil_comp_cons {A B : T.Obj} (f : T.Hom A B) :
    T.listRec A (T.nil B) (T.comp (T.cons B) (T.prodMapLeft f (T.list B))) = T.listMap f := rfl

/-- An arrow to the terminal object after an arrow is the arrow to the terminal object. -/
theorem bang_comp {A B : T.Obj} (f : T.Hom A B) : T.comp (T.bang B) f = T.bang A :=
  T.laws.eq_bang _

/-- An arrow to the terminal object after an arrow, followed by an arrow, is the arrow to the
terminal object followed by it. -/
theorem comp_bang_comp {A B C : T.Obj} (h : T.Hom T.one C) (f : T.Hom A B) :
    T.comp (T.comp h (T.bang B)) f = T.comp h (T.bang A) := by
  rw [← T.laws.comp_assoc, bang_comp]

/-- An arrow after the projection onto a coequalizer coequalizes the pair. -/
theorem comp_coeqProj_eq {A B C : T.Obj} (f g : T.Hom A B) (k : T.Hom (T.coeqz f g) C) :
    T.comp (T.comp k (T.coeqProj f g)) f = T.comp k (T.comp (T.coeqProj f g) g) := by
  rw [← T.laws.comp_assoc, T.laws.coeqProj_eq]

/-- The projections of the kernel pair of a monomorphism are equal. -/
theorem kernelPair_fst_eq_snd {A B : T.Obj} {m : T.Hom A B} (hm : T.IsMono m) :
    T.comp (T.fst A A) (T.eqIncl (T.comp m (T.fst A A)) (T.comp m (T.snd A A))) =
      T.comp (T.snd A A) (T.eqIncl (T.comp m (T.fst A A)) (T.comp m (T.snd A A))) :=
  hm _ _ (by rw [T.laws.comp_assoc, T.laws.comp_assoc, T.laws.eqIncl_eq])

/-- An arrow the projections of whose kernel pair are equal is a monomorphism. -/
theorem isMono_of_kernelPair {A B : T.Obj} {m : T.Hom A B}
    (h : T.comp (T.fst A A) (T.eqIncl (T.comp m (T.fst A A)) (T.comp m (T.snd A A))) =
      T.comp (T.snd A A) (T.eqIncl (T.comp m (T.fst A A)) (T.comp m (T.snd A A)))) :
    T.IsMono m := by
  intro X f g hfg
  have hp : T.comp (T.comp m (T.fst A A)) (T.pair f g) =
      T.comp (T.comp m (T.snd A A)) (T.pair f g) := by
    rw [← T.laws.comp_assoc, T.laws.fst_pair, ← T.laws.comp_assoc, T.laws.snd_pair, hfg]
  have e := T.laws.eqIncl_eqLift _ _ _ hp
  calc f = T.comp (T.fst A A) (T.pair f g) := (T.laws.fst_pair f g).symm
    _ = T.comp (T.comp (T.fst A A) (T.eqIncl _ _)) (T.eqLift _ _ _ hp) := by
      rw [← T.laws.comp_assoc, e]
    _ = T.comp (T.comp (T.snd A A) (T.eqIncl _ _)) (T.eqLift _ _ _ hp) := by rw [h]
    _ = T.comp (T.snd A A) (T.pair f g) := by rw [← T.laws.comp_assoc, e]
    _ = g := T.laws.snd_pair f g

/-- The factorization of a monomorphism through the pullback of truth along its characteristic
map, followed by the inverse comparison, is the identity. -/
theorem eqLift_comp_chiInv {A B : T.Obj} (m : T.Hom A B) (hm : T.IsMono m)
    (h : T.comp (T.chi m hm) m = T.comp (T.comp T.tru (T.bang B)) m) :
    T.comp (T.eqLift (T.chi m hm) (T.comp T.tru (T.bang B)) m h) (T.chiInv m hm) =
      T.idt (T.eqz (T.chi m hm) (T.comp T.tru (T.bang B))) := by
  have hi := T.laws.eqIncl_eq (T.chi m hm) (T.comp T.tru (T.bang B))
  exact (T.laws.eq_eqLift _ _ _ hi _ (by
      rw [T.laws.comp_assoc, T.laws.eqIncl_eqLift, T.laws.comp_chiInv]; rfl)).trans
    (T.laws.eq_eqLift _ _ _ hi (T.idt _) (T.laws.comp_idt _)).symm

/-- The inverse comparison, after the factorization of a monomorphism through the pullback of
truth along its characteristic map, is the identity. -/
theorem chiInv_comp_eqLift {A B : T.Obj} (m : T.Hom A B) (hm : T.IsMono m)
    (h : T.comp (T.chi m hm) m = T.comp (T.comp T.tru (T.bang B)) m) :
    T.comp (T.chiInv m hm) (T.eqLift (T.chi m hm) (T.comp T.tru (T.bang B)) m h) = T.idt A :=
  T.laws.chiInv_comp m hm _ (T.laws.eqIncl_eqLift _ _ _ h)

/-- An assignment whose first sort is that of arrows begins with an arrow. -/
theorem cons_arr {ρ : List T.model.Val} {Γ : List ℕ} (h : ρ.map Sigma.fst = arr :: Γ) :
    ∃ (A B : T.Obj) (f : T.Hom A B) (ρ' : List T.model.Val),
      ρ = ⟨arr, ⟨A, B, f⟩⟩ :: ρ' ∧ ρ'.map Sigma.fst = Γ := by
  rcases ρ with _ | ⟨⟨s, v⟩, ρ'⟩
  · cases h
  · simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨A, B, f⟩ := v
    exact ⟨A, B, f, ρ', rfl, h⟩

/-- An assignment whose first sort is that of objects begins with an object. -/
theorem cons_obj {ρ : List T.model.Val} {Γ : List ℕ} (h : ρ.map Sigma.fst = obj :: Γ) :
    ∃ (A : T.Obj) (ρ' : List T.model.Val), ρ = ⟨obj, ⟨A⟩⟩ :: ρ' ∧ ρ'.map Sigma.fst = Γ := by
  rcases ρ with _ | ⟨⟨s, v⟩, ρ'⟩
  · cases h
  · simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    obtain ⟨A⟩ := v
    exact ⟨A, ρ', rfl, h⟩

/-- The simplification, with an optional discharger and the given lemmas, at a location, of the
terms' builders, the evaluation of an operation's application at its arguments' values, the
membership of a value in a partial value, and the equations of objects and of arrows. -/
scoped macro "simp_terms" d:(Lean.Parser.Tactic.discharger)? " ["
    ls:Lean.Parser.Tactic.simpLemma,* "]" loc:(Lean.Parser.Tactic.location)? : tactic =>
  `(tactic| simp $[$d]? only [x, dfd, dom, cod, idt, comp, one, bang, prod, fst, snd, pair, eqz,
    eqIncl, eqLift, zero, absurd, coprod, inl, inr, copair, coeqz, coeqProj, coeqDesc, exp, ev,
    curry, omega, tru, chi, chiInv, nat, zeroN, succ, natRec, list, nil, cons, listRec, rose, node,
    roseRec, lrose, lnode, lroseRec, prodMapLeft, prodMapRight, listMap, monoCond, truthEq,
    truthIncl, truthLift, eval_op, eval_var, List.mapM_cons, List.mapM_nil,
    List.getElem?_cons_zero, List.getElem?_cons_succ, Part.coe_some, Part.pure_eq_some,
    Part.bind_eq_bind, Part.bind_some, model, ChosenTopos.op, Sigma.mk.inj_iff, heq_eq_eq,
    obj_car_eq_iff, arr_car_eq_iff, castHom, exists_prop, exists_true_left, $ls,*] $[$loc]?)

/-- The introduction of an axiom's assignment, value by value, and of its hypotheses, each
decomposed into the equations of objects and arrows its definedness and its equation state,
those of a variable with a value substituted. -/
local macro "intro_axiom" : tactic =>
  `(tactic| (
    intro ρ hρ hH
    repeat (first
      | obtain ⟨_, _, _, _, rfl, hρ⟩ := cons_arr hρ
      | obtain ⟨_, _, rfl, hρ⟩ := cons_obj hρ)
    obtain rfl := List.map_eq_nil_iff.mp hρ
    subst_vars
    try simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq,
      IsEmpty.forall_iff, implies_true, and_true, Eqn.Holds] at hH
    repeat (
      simp_terms [Part.eq_some_iff, Part.mem_bind_iff, Part.mem_some_iff, mem_mk,
        exists_exists_eq_and, exists_eq_left, exists_eq_right, exists_and_left] at *
      try casesm* _ ∧ _, ∃ _, _
      subst_vars
      try with_reducible casesm* ?a = ?a)))

set_option hygiene false in
/-- The discharge of an operation's definedness condition at values whose domains and codomains
match: equations of an object with itself, their conjunctions, a hypothesis, and an equation of
arrows the laws prove. -/
local macro "disch_dom" : tactic =>
  `(tactic| first
    | rfl
    | assumption
    | (apply Eq.symm; assumption)
    | (and_intros <;> first | rfl | assumption)
    | (apply isMono_of_kernelPair; first | assumption | (apply Eq.symm; assumption))
    | (refine Exists.intro (And.intro rfl rfl) (Exists.intro rfl ?_)
       try simp only [castHom, T.laws.comp_assoc, T.laws.eqIncl_eq, comp_coeqProj_eq,
         T.laws.chi_comp, comp_bang_comp]
       try (first | rfl | assumption | (apply Eq.symm; assumption))
       done))

set_option hygiene false in
/-- The closing of the uniqueness of a universal morphism: the arrow the conclusion names is the
universal one, by the law of its uniqueness at the hypotheses. -/
local macro "close_unique" : tactic =>
  `(tactic| first
    | exact (T.laws.eq_bang _).symm
    | exact (T.laws.eq_absurd _).symm
    | exact T.laws.eq_eqLift _ _ _ _ _ rfl
    | exact T.laws.eq_coeqDesc _ _ _ _ _ rfl
    | (apply Eq.symm; apply kernelPair_fst_eq_snd; assumption)
    | (apply Eq.symm
       apply T.laws.eq_chi
       all_goals first | rfl | assumption | (apply Eq.symm; assumption))
    | (apply Eq.symm
       first
       | apply T.laws.eq_natRec
       | apply T.laws.eq_listRec
       | apply T.laws.eq_roseRec
       | apply T.laws.eq_lroseRec
       all_goals first | rfl | assumption | (apply Eq.symm; assumption)))

set_option hygiene false in
/-- The closing of an axiom's conclusion, with the given lemmas: both sides evaluated, each
operation's definedness condition discharged, and the resulting equation of values proved by the
laws. -/
local macro "close_axiom" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| simp_terms (disch := disch_dom) [mk_eq_some, Eqn.Holds, Part.some_inj, exists_eq_left',
    exists_eq', and_true, true_and, and_self, pair_comp_fst_snd, pair_fst_comp_snd,
    listRec_nil_comp_cons, T.laws.comp_idt, T.laws.idt_comp, T.laws.comp_assoc, $ls,*])

/-- The validity of an axiom: its assignment and hypotheses introduced, and its conclusion
evaluated and closed by the given laws, by a hypothesis read backwards, or by the uniqueness of a
universal morphism. -/
local macro "valid_axiom" " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    intro_axiom
    try close_axiom [$ls,*]
    try (apply Eq.symm; assumption)
    try close_unique))

/-- The validity of every axiom of a block, each by {lit}`valid_axiom` with the given laws. -/
local macro "valid_block" blk:ident " [" ls:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    simp only [$blk:ident, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
      implies_true, and_true]
    repeat' apply And.intro
    all_goals valid_axiom [$ls,*]))

/-- The axioms of a category are valid in the model. -/
theorem valid_categoryAxioms : ∀ a ∈ categoryAxioms, a.Valid T.model := by
  valid_block categoryAxioms []

/-- The axioms of the terminal object are valid in the model. -/
theorem valid_terminalAxioms : ∀ a ∈ terminalAxioms, a.Valid T.model := by
  valid_block terminalAxioms []

/-- The axioms of binary products are valid in the model. -/
theorem valid_productAxioms : ∀ a ∈ productAxioms, a.Valid T.model := by
  valid_block productAxioms [T.laws.fst_pair, T.laws.snd_pair, T.laws.pair_eta]

/-- The axioms of equalizers are valid in the model. -/
theorem valid_equalizerAxioms : ∀ a ∈ equalizerAxioms, a.Valid T.model := by
  valid_block equalizerAxioms [T.laws.eqIncl_eqLift, T.laws.eqIncl_eq]

/-- The axioms of the initial object are valid in the model. -/
theorem valid_initialAxioms : ∀ a ∈ initialAxioms, a.Valid T.model := by
  valid_block initialAxioms []

/-- The axioms of binary coproducts are valid in the model. -/
theorem valid_coproductAxioms : ∀ a ∈ coproductAxioms, a.Valid T.model := by
  valid_block coproductAxioms [T.laws.copair_inl, T.laws.copair_inr, T.laws.copair_eta]

/-- The axioms of coequalizers are valid in the model. -/
theorem valid_coequalizerAxioms : ∀ a ∈ coequalizerAxioms, a.Valid T.model := by
  valid_block coequalizerAxioms [T.laws.coeqDesc_proj, T.laws.coeqProj_eq]

/-- The axioms of exponentials are valid in the model. -/
theorem valid_exponentialAxioms : ∀ a ∈ exponentialAxioms, a.Valid T.model := by
  valid_block exponentialAxioms [T.laws.ev_curry, T.laws.curry_eta]

/-- The axioms of the subobject classifier are valid in the model. -/
theorem valid_classifierAxioms : ∀ a ∈ classifierAxioms, a.Valid T.model := by
  valid_block classifierAxioms [T.laws.chi_comp, T.laws.comp_chiInv, eqLift_comp_chiInv,
    chiInv_comp_eqLift]

/-- The axioms of the natural numbers object are valid in the model. -/
theorem valid_natAxioms : ∀ a ∈ natAxioms, a.Valid T.model := by
  valid_block natAxioms [T.laws.natRec_zero, T.laws.natRec_succ]

/-- The axioms of list objects are valid in the model. -/
theorem valid_listAxioms : ∀ a ∈ listAxioms, a.Valid T.model := by
  valid_block listAxioms [T.laws.listRec_nil, T.laws.listRec_cons]

/-- The equation of the fold of the rose-tree object is valid in the model. -/
theorem valid_roseRec_node : (roseAxioms[6]'(by decide)).Valid T.model := by
  simp only [roseAxioms, List.getElem_cons_succ, List.getElem_cons_zero]
  valid_axiom [T.laws.roseRec_node]

/-- The uniqueness of the fold of the rose-tree object is valid in the model. -/
theorem valid_eq_roseRec : (roseAxioms[7]'(by decide)).Valid T.model := by
  simp only [roseAxioms, List.getElem_cons_succ, List.getElem_cons_zero]
  valid_axiom []

/-- The axioms of the rose-tree object are valid in the model. -/
theorem valid_roseAxioms : ∀ a ∈ roseAxioms, a.Valid T.model := by
  simp only [roseAxioms, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, valid_roseRec_node, valid_eq_roseRec⟩
  all_goals valid_axiom []

/-- The equation of the fold of a rose-tree object over an object of labels is valid in the
model. -/
theorem valid_lroseRec_lnode : (lroseAxioms[7]'(by decide)).Valid T.model := by
  simp only [lroseAxioms, List.getElem_cons_succ, List.getElem_cons_zero]
  valid_axiom [T.laws.lroseRec_lnode]

/-- The uniqueness of the fold of a rose-tree object over an object of labels is valid in the
model. -/
theorem valid_eq_lroseRec : (lroseAxioms[8]'(by decide)).Valid T.model := by
  simp only [lroseAxioms, List.getElem_cons_succ, List.getElem_cons_zero]
  valid_axiom []

/-- The axioms of rose-tree objects over objects of labels are valid in the model. -/
theorem valid_lroseAxioms : ∀ a ∈ lroseAxioms, a.Valid T.model := by
  simp only [lroseAxioms, List.forall_mem_cons, List.not_mem_nil, IsEmpty.forall_iff,
    implies_true, and_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, valid_lroseRec_lnode, valid_eq_lroseRec⟩
  all_goals valid_axiom []

variable (T) in
/-- A topos with chosen structure and the data objects is a model of the theory of a topos. -/
theorem isModel : IsModel theory T.model := by
  simp only [IsModel, theory, axioms, List.forall_mem_append, and_assoc]
  exact ⟨valid_categoryAxioms, valid_terminalAxioms, valid_productAxioms, valid_equalizerAxioms,
    valid_initialAxioms, valid_coproductAxioms, valid_coequalizerAxioms, valid_exponentialAxioms,
    valid_classifierAxioms, valid_natAxioms, valid_listAxioms, valid_roseAxioms,
    valid_lroseAxioms⟩

end ChosenTopos

end Geb.FreeTopos

end
