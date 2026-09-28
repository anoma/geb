/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.FreeTopos.Chosen
public import Geb.Mathlib.CategoryTheory.ElementaryTopos
public import Mathlib.CategoryTheory.Endofunctor.Algebra

set_option doc.verso true

/-!
# A topos with chosen structure from an elementary topos

An elementary topos of the repository's class ({name}`CategoryTheory.ElementaryTopos`), with
chosen data objects and chosen limit cones for its subobject classifier's squares, gives a topos
with chosen structure ({name}`Geb.FreeTopos.ChosenTopos`), and so, by the converse of the first
construction ({lit}`Geb.FreeTopos.ChosenTopos.isModel`), a model of the theory of a topos. The
operations are read from the class's chosen cones and cocones, its cartesian and closed
structures and its subobject classifier. The data objects are chosen initial algebras
({name}`CategoryTheory.Endofunctor.Algebra`): the natural numbers object of the functor taking
an object to its sum with the terminal object, the list object of an object of the functor
taking an object to the sum of the terminal object with its product with the element object,
and the rose-tree objects of the functors taking an object to the product of the natural
numbers object, or of an object of labels, with its list object; the list objects form a
functor by their folds.

The class states the squares of its classifier to be pullbacks by a proposition. The inverse
comparison of a monomorphism with the pullback of truth along its characteristic map is a
lifting through such a square, which the proposition yields only by {lit}`Classical.choice`,
so the construction takes the squares' limit cones as chosen data, as the class takes its
other limits.

## Main definitions

* {lit}`Elementary.natF`, {lit}`Elementary.listF`, {lit}`Elementary.listFunctor` — the
  functors of the data objects.
* {lit}`Elementary.DataObjects` — chosen data objects, as initial algebras.
* {lit}`Elementary.ClassifierLimits` — chosen limit cones for the classifier's squares.
* {lit}`Elementary.toposData` — the operations.
* {lit}`Elementary.chosenTopos` — the topos with chosen structure.

## Main statements

* {lit}`Elementary.eq_fold` — an arrow from an initial algebra commuting with the structure
  maps is the fold.
* {lit}`Elementary.isPullback_of_iso` — a monomorphism isomorphic to the pullback of truth along
  an arrow into the classifier is its pullback.
* {lit}`Elementary.laws` — the laws of a topos with chosen structure and the data objects.

## Implementation notes

Every operation is computed from the chosen data, so that no value is chosen; the proofs of the
laws use mathlib's category theory, whose lemmas depend on {lit}`Classical.choice`, and the
module is admitted to that axiom as the constructive-only rules provide for a module whose
subject is the correspondence with an external library. The record of operations is reducible,
so that its objects and arrows are the category's when its laws are proved.

## Tags

elementary topos, chosen structure, initial algebra, natural numbers object, list object
-/

@[expose] public section

universe v u

namespace Geb.FreeTopos.Elementary

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory

variable {C : Type u} [Category.{v} C] [ElementaryTopos C]

attribute [local instance] ElementaryTopos.cartesianMonoidalCategory
  ElementaryTopos.monoidalClosed

/-! The chosen coproducts. -/

/-- The chosen coproduct of two objects. -/
def coprod (X Y : C) : C := (ElementaryTopos.binaryCoproductCocone X Y).cocone.pt

/-- The first injection into the chosen coproduct. -/
def inl (X Y : C) : X ⟶ coprod X Y :=
  BinaryCofan.inl (ElementaryTopos.binaryCoproductCocone X Y).cocone

/-- The second injection into the chosen coproduct. -/
def inr (X Y : C) : Y ⟶ coprod X Y :=
  BinaryCofan.inr (ElementaryTopos.binaryCoproductCocone X Y).cocone

/-- The copairing of two arrows of one codomain. -/
def copair {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : coprod X Y ⟶ Z :=
  (BinaryCofan.IsColimit.desc' (ElementaryTopos.binaryCoproductCocone X Y).isColimit f g).1

/-- The copairing after the first injection is the first arrow. -/
@[reassoc (attr := simp)]
theorem inl_copair {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : inl X Y ≫ copair f g = f :=
  (BinaryCofan.IsColimit.desc' (ElementaryTopos.binaryCoproductCocone X Y).isColimit f g).2.1

/-- The copairing after the second injection is the second arrow. -/
@[reassoc (attr := simp)]
theorem inr_copair {X Y Z : C} (f : X ⟶ Z) (g : Y ⟶ Z) : inr X Y ≫ copair f g = g :=
  (BinaryCofan.IsColimit.desc' (ElementaryTopos.binaryCoproductCocone X Y).isColimit f g).2.2

/-- Arrows from the chosen coproduct are equal when they are after each injection. -/
theorem coprod_hom_ext {X Y Z : C} {f g : coprod X Y ⟶ Z} (hl : inl X Y ≫ f = inl X Y ≫ g)
    (hr : inr X Y ≫ f = inr X Y ≫ g) : f = g :=
  BinaryCofan.IsColimit.hom_ext (ElementaryTopos.binaryCoproductCocone X Y).isColimit hl hr

/-! The functors of the data objects. -/

/-- The functor taking an object to its sum with the terminal object. -/
@[simps, reducible]
def natF : C ⥤ C where
  obj X := coprod (𝟙_ C) X
  map f := copair (inl _ _) (f ≫ inr _ _)
  map_id _ := coprod_hom_ext (by simp) (by simp)
  map_comp _ _ := coprod_hom_ext (by simp) (by simp)

/-- The functor taking an object to the sum of the terminal object with its product with an
object of elements. -/
@[simps, reducible]
def listF (A : C) : C ⥤ C where
  obj X := coprod (𝟙_ C) (A ⊗ X)
  map f := copair (inl _ _) ((A ◁ f) ≫ inr _ _)
  map_id _ := coprod_hom_ext (by simp) (by simp)
  map_comp _ _ := coprod_hom_ext (by simp) (by simp)

/-! The folds of initial algebras. -/

section Fold

variable {F : C ⥤ C} {I : Endofunctor.Algebra F} (hI : IsInitial I)

/-- The fold of an initial algebra into an algebra, given by its carrier and structure map. -/
def fold {X : C} (x : F.obj X ⟶ X) : I.a ⟶ X := (hI.to ⟨X, x⟩).f

omit [ElementaryTopos C] in
/-- The fold after the structure map is the algebra's structure map after the functor's action
on the fold. -/
@[reassoc]
theorem str_fold {X : C} (x : F.obj X ⟶ X) : I.str ≫ fold hI x = F.map (fold hI x) ≫ x :=
  ((hI.to ⟨X, x⟩).h).symm

omit [ElementaryTopos C] in
/-- An arrow from an initial algebra commuting with the structure maps is the fold. -/
theorem eq_fold {X : C} (x : F.obj X ⟶ X) (k : I.a ⟶ X) (hk : I.str ≫ k = F.map k ≫ x) :
    k = fold hI x :=
  congrArg Endofunctor.Algebra.Hom.f
    (hI.hom_ext (⟨k, hk.symm⟩ : I ⟶ ⟨X, x⟩) (hI.to ⟨X, x⟩))

end Fold

/-! The natural numbers object, by its start and step. -/

section Nat

variable {N : Endofunctor.Algebra (natF (C := C))} (hN : IsInitial N)

/-- Zero, from the terminal object. -/
def zeroOf (N : Endofunctor.Algebra (natF (C := C))) : 𝟙_ C ⟶ N.a := inl _ _ ≫ N.str

/-- The successor. -/
def succOf (N : Endofunctor.Algebra (natF (C := C))) : N.a ⟶ N.a := inr _ _ ≫ N.str

/-- The recursion with a start and a step. -/
def natRecOf {X : C} (z : 𝟙_ C ⟶ X) (s : X ⟶ X) : N.a ⟶ X := fold hN (copair z s)

/-- The recursion at zero is the start. -/
theorem zero_natRec {X : C} (z : 𝟙_ C ⟶ X) (s : X ⟶ X) : zeroOf N ≫ natRecOf hN z s = z := by
  simp [zeroOf, natRecOf, str_fold]

/-- The recursion at a successor is the step after the recursion. -/
theorem succ_natRec {X : C} (z : 𝟙_ C ⟶ X) (s : X ⟶ X) :
    succOf N ≫ natRecOf hN z s = natRecOf hN z s ≫ s := by
  simp [succOf, natRecOf, str_fold]

/-- An arrow with the recursion's equations is the recursion. -/
theorem eq_natRec {X : C} (z : 𝟙_ C ⟶ X) (s : X ⟶ X) (k : N.a ⟶ X) (hz : zeroOf N ≫ k = z)
    (hs : succOf N ≫ k = k ≫ s) : k = natRecOf hN z s :=
  eq_fold hN _ k (coprod_hom_ext (by simpa [zeroOf] using hz) (by simpa [succOf] using hs))

end Nat

/-! The list objects, by their start and step. -/

section List

variable {A : C} {L : Endofunctor.Algebra (listF A)} (hL : IsInitial L)

/-- The empty list, from the terminal object. -/
def nilOf (L : Endofunctor.Algebra (listF A)) : 𝟙_ C ⟶ L.a := inl _ _ ≫ L.str

/-- The construction of a list from an element and a list. -/
def consOf (L : Endofunctor.Algebra (listF A)) : A ⊗ L.a ⟶ L.a := inr _ _ ≫ L.str

/-- The recursion with a start and a step. -/
def listRecOf {X : C} (z : 𝟙_ C ⟶ X) (s : A ⊗ X ⟶ X) : L.a ⟶ X := fold hL (copair z s)

/-- The recursion at the empty list is the start. -/
@[reassoc]
theorem nil_listRec {X : C} (z : 𝟙_ C ⟶ X) (s : A ⊗ X ⟶ X) :
    nilOf L ≫ listRecOf hL z s = z := by
  simp [nilOf, listRecOf, str_fold]

/-- The recursion at a constructed list is the step after the recursion of the tail. -/
@[reassoc]
theorem cons_listRec {X : C} (z : 𝟙_ C ⟶ X) (s : A ⊗ X ⟶ X) :
    consOf L ≫ listRecOf hL z s = (A ◁ listRecOf hL z s) ≫ s := by
  simp [consOf, listRecOf, str_fold]

/-- An arrow with the recursion's equations is the recursion. -/
theorem eq_listRec {X : C} (z : 𝟙_ C ⟶ X) (s : A ⊗ X ⟶ X) (k : L.a ⟶ X)
    (hz : nilOf L ≫ k = z) (hs : consOf L ≫ k = (A ◁ k) ≫ s) : k = listRecOf hL z s :=
  eq_fold hL _ k (coprod_hom_ext (by simpa [nilOf] using hz) (by simpa [consOf] using hs))

end List

/-! The list objects as a functor, and the data objects. -/

section Data

variable (L : ∀ A : C, Endofunctor.Algebra (listF A)) (hL : ∀ A, IsInitial (L A))

/-- The action of the list objects on an arrow: the fold of the list object of its domain whose
step constructs the image of each element. -/
def listMapOf {A B : C} (f : A ⟶ B) : (L A).a ⟶ (L B).a :=
  listRecOf (hL A) (nilOf (L B)) ((f ▷ (L B).a) ≫ consOf (L B))

/-- The list objects, a functor by their action on arrows. -/
@[simps]
def listFunctor : C ⥤ C where
  obj A := (L A).a
  map := listMapOf L hL
  map_id A := (eq_listRec (hL A) _ _ (𝟙 _) (by simp) (by simp)).symm
  map_comp f g := (eq_listRec (hL _) _ _ _
    (by simp [listMapOf, nil_listRec_assoc, nil_listRec])
    (by simp [listMapOf, cons_listRec_assoc, cons_listRec, ← whisker_exchange_assoc])).symm

end Data

/-- Chosen data objects: the natural numbers object, the list object of each object and the
rose-tree objects, each an initial algebra of its functor, the rose-tree objects' functors
taking an object to the product of the natural numbers object, or of an object of labels, with
the object's list object. -/
structure DataObjects (C : Type u) [Category.{v} C] [ElementaryTopos C] : Type (max u v) where
  /-- The natural numbers object. -/
  nat : Endofunctor.Algebra (natF (C := C))
  /-- The natural numbers object is initial. -/
  natInitial : IsInitial nat
  /-- The list object of each object. -/
  list : ∀ A : C, Endofunctor.Algebra (listF A)
  /-- The list objects are initial. -/
  listInitial : ∀ A, IsInitial (list A)
  /-- The rose-tree object. -/
  rose : Endofunctor.Algebra (listFunctor list listInitial ⋙ tensorLeft nat.a)
  /-- The rose-tree object is initial. -/
  roseInitial : IsInitial rose
  /-- The rose-tree object over each object of labels. -/
  lrose : ∀ A : C, Endofunctor.Algebra (listFunctor list listInitial ⋙ tensorLeft A)
  /-- The rose-tree objects over objects of labels are initial. -/
  lroseInitial : ∀ A, IsInitial (lrose A)


/-- The comparison of the terminal object with the domain of the classifier's truth. -/
abbrev unitIso : 𝟙_ C ≅ (ElementaryTopos.classifier (C := C)).Ω₀ :=
  ElementaryTopos.tensorUnitIsoΩ₀ C

omit [ElementaryTopos C] in
/-- A left-cancellable arrow is a monomorphism. -/
theorem mono_of_cancel {A B : C} {m : A ⟶ B}
    (hm : ∀ {X : C} (f g : X ⟶ A), f ≫ m = g ≫ m → f = g) : Mono m := ⟨hm⟩

variable (C) in
/-- Chosen limit cones for the squares of the subobject classifier: for each monomorphism, the
square of it with truth along its characteristic map, which the classifier states to be a
pullback, as a limit. The comparison of the monomorphism with the pullback of truth along its
characteristic map has its inverse from the cone's lifting, which the proposition alone yields
only by {lit}`Classical.choice`. -/
abbrev ClassifierLimits : Type (max u v) :=
  ∀ {U X : C} (m : U ⟶ X) [Mono m], IsLimit (PullbackCone.mk m
    ((ElementaryTopos.classifier (C := C)).χ₀ U)
    ((ElementaryTopos.classifier (C := C)).isPullback m).w)

variable (C) in
set_option backward.isDefEq.respectTransparency false in
/-- The operations of the topos with chosen structure of an elementary topos with chosen data
objects: its chosen cones and cocones, cartesian and closed structures and subobject
classifier, the evaluation and currying of the exponential taken with the exponent on the right
of the product by its symmetry, truth from the terminal object by the comparison, and the data
objects' folds. -/
@[reducible] def toposData (P : ClassifierLimits C) (D : DataObjects C) : ToposData.{u, v} where
  Obj := C
  Hom X Y := X ⟶ Y
  idt X := 𝟙 X
  comp g f := f ≫ g
  one := 𝟙_ C
  bang X := toUnit X
  prod X Y := X ⊗ Y
  fst X Y := fst X Y
  snd X Y := snd X Y
  pair f g := lift f g
  eqz f g := (ElementaryTopos.equalizerCone f g).cone.pt
  eqIncl f g := Fork.ι (ElementaryTopos.equalizerCone f g).cone
  eqLift f g h hh := (Fork.IsLimit.lift' (ElementaryTopos.equalizerCone f g).isLimit h hh).1
  zero := (ElementaryTopos.initialCocone (C := C)).cocone.pt
  absurd X := (ElementaryTopos.isInitial C).to X
  coprod := coprod
  inl := inl
  inr := inr
  copair := copair
  coeqz f g := (ElementaryTopos.coequalizerCocone f g).cocone.pt
  coeqProj f g := Cofork.π (ElementaryTopos.coequalizerCocone f g).cocone
  coeqDesc f g h hh :=
    (Cofork.IsColimit.desc' (ElementaryTopos.coequalizerCocone f g).isColimit h hh).1
  exp A B := (ihom A).obj B
  ev A B := lift (snd _ _) (fst _ _) ≫ (ihom.ev A).app B
  curry f := MonoidalClosed.curry (lift (snd _ _) (fst _ _) ≫ f)
  omega := (ElementaryTopos.classifier (C := C)).Ω
  tru := unitIso.hom ≫ (ElementaryTopos.classifier (C := C)).truth
  chi m hm := have := mono_of_cancel hm; (ElementaryTopos.classifier (C := C)).χ m
  chiInv {_ B} m hm :=
    have := mono_of_cancel hm
    PullbackCone.IsLimit.lift (P m)
      (Fork.ι (ElementaryTopos.equalizerCone _ _).cone) (toUnit _ ≫ unitIso.hom) (by
        rw [Fork.condition]
        simp)
  nat := D.nat.a
  zeroN := zeroOf D.nat
  succ := succOf D.nat
  natRec z s := natRecOf D.natInitial z s
  list A := (D.list A).a
  nil A := nilOf (D.list A)
  cons A := consOf (D.list A)
  listRec A z s := listRecOf (D.listInitial A) z s
  rose := D.rose.a
  node := D.rose.str
  roseRec f := fold D.roseInitial f
  lrose A := (D.lrose A).a
  lnode A := (D.lrose A).str
  lroseRec A f := fold (D.lroseInitial A) f


/-! The laws. -/

/-- Whiskering on the left by an object is the pairing of the first projection with the arrow
after the second. -/
theorem whiskerLeft_eq_lift (X : C) {Y Z : C} (f : Y ⟶ Z) :
    X ◁ f = lift (fst X Y) (snd X Y ≫ f) :=
  hom_ext _ _ (by simp) (by simp)

/-- Whiskering on the right by an object is the pairing of the arrow after the first projection
with the second. -/
theorem whiskerRight_eq_lift {X Y : C} (f : X ⟶ Y) (Z : C) :
    f ▷ Z = lift (fst X Z ≫ f) (snd X Z) :=
  hom_ext _ _ (by simp) (by simp)

/-- Arrows to the domain of the classifier's truth are equal. -/
theorem eq_to_Ω₀ {X : C} (f g : X ⟶ (ElementaryTopos.classifier (C := C)).Ω₀) : f = g := by
  rw [← cancel_mono unitIso.inv]
  exact toUnit_unique _ _

variable (P : ClassifierLimits C) (D : DataObjects C)

/-- The action of the list objects on an arrow in the record is their functor's. -/
theorem listMap_eq {A B : C} (f : A ⟶ B) :
    (toposData C P D).listMap f = listMapOf D.list D.listInitial f := by
  change listRecOf _ _ (lift (fst _ _ ≫ f) (snd _ _) ≫ consOf _) =
    listRecOf _ _ ((f ▷ _) ≫ consOf _)
  rw [whiskerRight_eq_lift]

/-- The whiskering on the left of the action of the list objects on an arrow is the identity
times the action in the record. -/
theorem whiskerLeft_listMap (N : C) {X Y : C} (g : X ⟶ Y) :
    N ◁ listMapOf D.list D.listInitial g =
      lift (fst N _) (snd N _ ≫ (toposData C P D).listMap g) := by
  rw [listMap_eq, whiskerLeft_eq_lift]

/-- The inverse comparison, followed by the monomorphism, is the inclusion of the pullback of
truth along its characteristic map. -/
theorem chiInv_comp_self {A B : C} (m : A ⟶ B) (hm : (toposData C P D).IsMono m) :
    (toposData C P D).chiInv m hm ≫ m =
      Fork.ι (ElementaryTopos.equalizerCone _ _).cone := by
  have := mono_of_cancel hm
  exact PullbackCone.IsLimit.lift_fst _ _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The square of a monomorphism with truth along an arrow into the classifier, through whose
pullback of truth it factors by an arrow with an inverse, is a pullback. -/
theorem isPullback_of_iso {A B : C} {m : A ⟶ B} {φ : B ⟶ (ElementaryTopos.classifier (C := C)).Ω}
    (k : A ⟶ (ElementaryTopos.equalizerCone φ (toUnit B ≫ unitIso.hom ≫
      (ElementaryTopos.classifier (C := C)).truth)).cone.pt)
    (k' : (ElementaryTopos.equalizerCone φ (toUnit B ≫ unitIso.hom ≫
      (ElementaryTopos.classifier (C := C)).truth)).cone.pt ⟶ A)
    (hk : k ≫ Fork.ι (ElementaryTopos.equalizerCone _ _).cone = m) (hkk : k' ≫ k = 𝟙 _)
    (hkk' : k ≫ k' = 𝟙 _) :
    IsPullback m (toUnit A ≫ unitIso.hom) φ (ElementaryTopos.classifier (C := C)).truth := by
  have e := (ElementaryTopos.equalizerCone φ (toUnit B ≫ unitIso.hom ≫
    (ElementaryTopos.classifier (C := C)).truth)).isLimit
  have w : m ≫ φ = (toUnit A ≫ unitIso.hom) ≫ (ElementaryTopos.classifier (C := C)).truth := by
    rw [← hk, Category.assoc, Fork.condition]
    simp
  refine IsPullback.of_isLimit (c := PullbackCone.mk _ _ w) (PullbackCone.IsLimit.mk w
    (fun s ↦ (Fork.IsLimit.lift' e s.fst (by
      rw [s.condition, eq_to_Ω₀ s.snd (toUnit _ ≫ unitIso.hom)]
      simp)).1 ≫ k') ?_ ?_ ?_)
  · intro s
    rw [← hk, Category.assoc, reassoc_of% hkk]
    exact (Fork.IsLimit.lift' e _ _).2
  · intro s
    exact eq_to_Ω₀ _ _
  · intro s g hg _
    rw [← Category.comp_id g, ← hkk', ← Category.assoc]
    congr 1
    refine Fork.IsLimit.hom_ext e ?_
    rw [(Fork.IsLimit.lift' e _ _).2, Category.assoc, hk, hg]

variable (C) in
set_option backward.isDefEq.respectTransparency false in
/-- The laws of the topos with chosen structure of an elementary topos with chosen data objects
and classifier limits. -/
theorem laws : (toposData C P D).Laws where
  comp_assoc h g f := Category.assoc f g h
  comp_idt f := Category.id_comp f
  idt_comp f := Category.comp_id f
  eq_bang f := toUnit_unique _ _
  fst_pair f g := lift_fst f g
  snd_pair f g := lift_snd f g
  pair_eta h := hom_ext _ _ (by simp) (by simp)
  eqIncl_eq f g := Fork.condition _
  eqIncl_eqLift f g h hh := (Fork.IsLimit.lift' _ h hh).2
  eq_eqLift f g h hh k hk :=
    Fork.IsLimit.hom_ext (ElementaryTopos.equalizerCone f g).isLimit
      (hk.trans (Fork.IsLimit.lift' _ h hh).2.symm)
  eq_absurd f := (ElementaryTopos.isInitial C).hom_ext _ _
  copair_inl f g := inl_copair f g
  copair_inr f g := inr_copair f g
  copair_eta h := coprod_hom_ext (by simp) (by simp)
  coeqProj_eq f g := Cofork.condition _
  coeqDesc_proj f g h hh := (Cofork.IsColimit.desc' _ h hh).2
  eq_coeqDesc f g h hh k hk :=
    Cofork.IsColimit.hom_ext (ElementaryTopos.coequalizerCocone f g).isColimit
      (hk.trans (Cofork.IsColimit.desc' _ h hh).2.symm)
  ev_curry {_ A _} f := by
    change lift (fst _ _ ≫ MonoidalClosed.curry _) (snd _ _) ≫ lift (snd _ _) (fst _ _) ≫
      (ihom.ev A).app _ = f
    rw [← Category.assoc, show lift (fst _ _ ≫ MonoidalClosed.curry
        (lift (snd A _) (fst A _) ≫ f)) (snd _ _) ≫ lift (snd _ _) (fst _ _) =
        lift (snd _ _) (fst _ _) ≫ (A ◁ MonoidalClosed.curry (lift (snd A _) (fst A _) ≫ f)) by
          simp [whiskerLeft_eq_lift],
      Category.assoc, ← MonoidalClosed.uncurry_eq, MonoidalClosed.uncurry_curry,
      ← Category.assoc, comp_lift, lift_snd, lift_fst, lift_fst_snd, Category.id_comp]
  curry_eta {_ A _} h := by
    change MonoidalClosed.curry (lift (snd _ _) (fst _ _) ≫ lift (fst _ _ ≫ h) (snd _ _) ≫
      lift (snd _ _) (fst _ _) ≫ (ihom.ev A).app _) = h
    rw [← Category.assoc, ← Category.assoc,
      show (lift (snd A _) (fst A _) ≫ lift (fst _ _ ≫ h) (snd _ _)) ≫ lift (snd _ _) (fst _ _) =
        A ◁ h by simp [whiskerLeft_eq_lift],
      ← MonoidalClosed.uncurry_eq, MonoidalClosed.curry_uncurry]
  chi_comp m hm := by
    have := mono_of_cancel hm
    change m ≫ (ElementaryTopos.classifier (C := C)).χ m = toUnit _ ≫ unitIso.hom ≫ _
    rw [((ElementaryTopos.classifier (C := C)).isPullback m).w, ← Category.assoc,
      eq_to_Ω₀ ((ElementaryTopos.classifier (C := C)).χ₀ _) (toUnit _ ≫ unitIso.hom)]
  comp_chiInv m hm := chiInv_comp_self P D m hm
  chiInv_comp m hm k hk := hm _ _ ((Category.assoc _ _ _).trans
    ((congrArg (k ≫ ·) (chiInv_comp_self P D m hm)).trans (hk.trans (Category.id_comp m).symm)))
  eq_chi m hm φ k k' hk hkk hk'k := by
    have := mono_of_cancel hm
    exact (ElementaryTopos.classifier (C := C)).uniq m (isPullback_of_iso k k' hk hkk hk'k)
  natRec_zero z s := zero_natRec _ z s
  natRec_succ z s := succ_natRec _ z s
  eq_natRec z s k hz hs := eq_natRec _ z s k hz hs
  listRec_nil A z s := nil_listRec _ z s
  listRec_cons A z s := by
    change consOf _ ≫ listRecOf _ z s = lift (fst _ _) (snd _ _ ≫ listRecOf _ z s) ≫ s
    rw [cons_listRec, whiskerLeft_eq_lift]
  eq_listRec A z s k hz hs :=
    eq_listRec _ z s k hz (by rw [whiskerLeft_eq_lift]; exact hs)
  roseRec_node f :=
    (str_fold D.roseInitial f).trans (congrArg (· ≫ f) (whiskerLeft_listMap P D D.nat.a _))
  eq_roseRec f k hk := eq_fold D.roseInitial f k
    (hk.trans (congrArg (· ≫ f) (whiskerLeft_listMap P D D.nat.a k).symm))
  lroseRec_lnode A f :=
    (str_fold (D.lroseInitial A) f).trans (congrArg (· ≫ f) (whiskerLeft_listMap P D A _))
  eq_lroseRec A f k hk := eq_fold (D.lroseInitial A) f k
    (hk.trans (congrArg (· ≫ f) (whiskerLeft_listMap P D A k).symm))

variable (C) in
/-- The topos with chosen structure of an elementary topos with chosen data objects and
classifier limits. -/
def chosenTopos : ChosenTopos.{u, v} := ⟨toposData C P D, laws C P D⟩

end Geb.FreeTopos.Elementary

end
