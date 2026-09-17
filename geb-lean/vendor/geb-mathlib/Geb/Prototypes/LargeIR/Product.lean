/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.Basic
public import Geb.Mathlib.Data.PFunctor.Slice.W
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Fin.Basic

set_option doc.verso true

/-!
# Prototype: the walking arrow over an index type

Throwaway exploration, not upstream-eligible content. Every declaration here
is {name}`Classical.choice`-free.

A presheaf polynomial endofunctor on the walking arrow acts on
{lit}`Fam(Type)`, where the base of a family is data, and its directions can
name an element of the base only through a function from a fixed set, so a
slice polynomial functor transcribed to it is recovered only up to a section
and its W-type is not recovered at all. On the discrete category of an index
type {lit}`X`, presheaves are {lit}`Type/X`, a direction names its index
exactly, and the presheaf polynomial functors are the slice polynomials with
their W-types. This module takes the product of the two: the category
{lit}`Idx X`, the pairs {lit}`(i, x)` of a level and an index ordered by
{lit}`i ≤ i'` and {lit}`x = x'`, whose presheaves are {lit}`X`-indexed
families of arrows, the objects {lit}`(U : X → Type, T : Π x, U x → Type)` of
indexed induction-recursion. A direction at {lit}`(j, x)` names its index
{lit}`x` by its object, and only an element of {lit}`U x` through a function.

{lit}`elemEquiv` computes the value of any presheaf polynomial endofunctor on
{lit}`Idx X`: a shape, a base assignment at each index, and an assignment of
level-{lit}`1` directions in the fibres over it, the naturality along the one
non-identity morphism at each index being the fibre condition,
{lit}`isNatural_iff`. {lit}`prodPsh` transcribes a slice polynomial functor
{lit}`P : Type/X → Type/Y`: level-{lit}`0` shapes {lit}`Y` with no
directions, so that the base is constantly a point, and level-{lit}`1`
shapes the shapes of {lit}`P`, each direction {lit}`b` of {lit}`P` giving a
level-{lit}`1` direction at {lit}`(1, r b)` with its restriction at
{lit}`(0, r b)`. {lit}`ofSliceX` embeds {lit}`Type/X` as the presheaves with
a point at every level {lit}`0`, and {lit}`levelOneEquiv` identifies the
level-{lit}`1` value of the transcription at {lit}`ofSliceX p` over
{lit}`(1, y)` with the value of {lit}`P` at {lit}`p` over {lit}`y`, on the
nose; {lit}`map_cmp` extends this to morphisms over {lit}`X`. For an
endofunctor, {lit}`wFixed` then exhibits the slice W-type
{name}`SlicePFunctor.W` as a fixed point of the transcription: the iteration
of the transcription on the initial object of {lit}`Type/X`, which stays
over the constant point, is the iteration of {lit}`P`.

## Main definitions

* {lit}`Idx` — the walking arrow over an index type, as a preorder.
* {lit}`Elem`, {lit}`elemEquiv` — the value of a presheaf polynomial
  endofunctor on {lit}`Idx X` in dependent-type terms.
* {lit}`prodPsh` — the transcription of a slice polynomial functor.
* {lit}`ofSliceX`, {lit}`ofSliceXHom` — {lit}`Type/X` as presheaves on
  {lit}`Idx X`.
* {lit}`levelOneEquiv`, {lit}`cmp` — the level-{lit}`1` value at an object of
  {lit}`Type/X` is the slice functor's value, and the comparison map.
* {lit}`wFixed` — the slice W-type is a fixed point of the transcription.

## Main statements

* {lit}`isNatural_iff` — naturality over {lit}`Idx X` is the fibre condition
  at each index.
* {lit}`levelZeroEquiv` — the transcription's base is a point at every
  index.
* {lit}`map_cmp` — the comparison map is natural in the object of
  {lit}`Type/X`.

## References

* \[DybjerSetzer2003\]
* \[HancockMcBrideGhaniMalatestaAltenkirch2013\]

## Tags

prototype, presheaf, walking arrow, indexed inductive-recursive, slice
polynomial functor, W-type
-/

@[expose] public section

open CategoryTheory

namespace GebProto.LargeIR.Product

/-! # The index category -/

/-- The walking arrow over an index type: pairs of a level and an index. -/
def Idx (X : Type) : Type :=
  Fin 2 × X

/-- The order: levels increase and indices are fixed, so the category has
one non-identity morphism {lit}`(0, x) ⟶ (1, x)` at each index. -/
instance (X : Type) : Preorder (Idx X) where
  le p q := p.1 ≤ q.1 ∧ p.2 = q.2
  le_refl _ := ⟨le_refl _, rfl⟩
  le_trans _ _ _ h h' := ⟨le_trans h.1 h'.1, h.2.trans h'.2⟩

/-- An object of {lit}`Idx X` from its level and index. -/
def mkIdx {X : Type} (i : Fin 2) (x : X) : Idx X :=
  (i, x)

/-- The non-identity morphism at an index. -/
def waHomAt {X : Type} (x : X) : mkIdx 0 x ⟶ mkIdx 1 x :=
  homOfLE ⟨Fin.zero_le _, rfl⟩

/-- Morphisms of {lit}`Idx X` are unique. -/
theorem hom_ext {X : Type} {o o' : Idx X} (f g : o' ⟶ o) : f = g :=
  Subsingleton.elim f g

/-- A morphism of {lit}`Idx X` is an identity or the non-identity morphism at
its index. -/
theorem le_cases {X : Type} {o o' : Idx X} (h : o' ≤ o) :
    o' = o ∨ ∃ x, o' = mkIdx 0 x ∧ o = mkIdx 1 x := by
  obtain ⟨i, x⟩ := o
  obtain ⟨i', x'⟩ := o'
  obtain ⟨h1, rfl⟩ := h
  match i, i' with
  | 0, 0 => exact Or.inl rfl
  | 1, 1 => exact Or.inl rfl
  | 1, 0 => exact Or.inr ⟨x', rfl, rfl⟩
  | 0, 1 => exact absurd h1 (by change ¬ ((1 : Fin 2) ≤ 0); decide)

/-! # The value of an endofunctor -/

variable {X : Type} (Z : (Idx X)ᵒᵖ ⥤ Type)

/-- The fibre of the restriction at an index over a base element. -/
def fibre (x : X) (u : Z.obj ⟨mkIdx 0 x⟩) : Type :=
  { z : Z.obj ⟨mkIdx 1 x⟩ // Z.map (waHomAt x).op z = u }

/-- A dependent pair reassembled from its components after a cast of the
second along an equation of the first is the original pair. -/
private theorem sigma_mk_cast {o o' : Idx X} (z : Z.obj ⟨o⟩) (e : o = o') :
    (⟨o', cast (congrArg (fun k : Idx X ↦ Z.obj ⟨k⟩) e) z⟩ : Σ k : Idx X, Z.obj ⟨k⟩) = ⟨o, z⟩ := by
  subst e
  rfl

/-- The value an element assigns to a direction, paired with the direction's
object, is the element's raw assignment. -/
theorem sigma_value (F : PresheafDomPFunctorData.{0, 0, 0, 0} (Idx X))
    (x : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj Z)) ⦃o : Idx X⦄
    (b : F.Direction x.1.1 o) :
    (⟨o, F.value x b⟩ : Σ k : Idx X, Z.obj ⟨k⟩) = x.1.2 b.1 := by
  obtain ⟨⟨a, v⟩, hc⟩ := x
  obtain ⟨b, hb⟩ := b
  exact sigma_mk_cast Z (v b).2 (((F.compatible_iff _ a v).mp hc b).trans hb)

/-- Over {lit}`Idx X`, a direction assignment is natural exactly when it
satisfies the fibre equation along the non-identity morphism at each index,
given that direction restriction along identities is the identity. -/
theorem isNatural_iff (F : PresheafDomPFunctorData.{0, 0, 0, 0} (Idx X))
    (hid : F.DirectionRestrId)
    (x : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj Z)) :
    F.IsNatural x ↔ ∀ (x' : X) (d : F.Direction x.1.1 (mkIdx 1 x')),
      F.value x (F.directionRestr x.1.1 (waHomAt x') d) = Z.map (waHomAt x').op (F.value x d) := by
  refine ⟨fun h x' d ↦ h (waHomAt x') d, fun h o o' f d ↦ ?_⟩
  rcases le_cases (leOfHom f) with rfl | ⟨x', rfl, rfl⟩
  · rw [hom_ext f (𝟙 _), hid, op_id, Z.map_id]
    rfl
  · rw [hom_ext f (waHomAt x')]
    exact h x' d

variable {Y : Type} (F : PresheafPFunctor.{0, 0, 0, 0, 0, 0} (Idx X) (Idx Y))

/-- The restriction of a shape's directions at an index from level {lit}`1`
to level {lit}`0`. -/
abbrev dirRestr (a : F.A) (x : X) : F.Direction a (mkIdx 1 x) → F.Direction a (mkIdx 0 x) :=
  F.directionRestr a (waHomAt x)

/-- The value of {lit}`F` at {lit}`Z` in dependent-type terms: a shape, a base
assignment at each index, and an assignment of the level-{lit}`1` directions
at each index in the fibres over the base assignment at their restrictions. -/
def Elem : Type :=
  Σ a : F.A, Σ g : ∀ x, F.Direction a (mkIdx 0 x) → Z.obj ⟨mkIdx 0 x⟩,
    ∀ x (d : F.Direction a (mkIdx 1 x)), fibre Z x (g x (dirRestr F a x d))

/-- The raw assignment of an element built from a base assignment and a
level-{lit}`1` assignment, at a direction whose object is known. -/
def assignAux {a : F.A} (g : ∀ x, F.Direction a (mkIdx 0 x) → Z.obj ⟨mkIdx 0 x⟩)
    (w : ∀ x (d : F.Direction a (mkIdx 1 x)), fibre Z x (g x (dirRestr F a x d))) (b : F.B a) :
    (o : Idx X) → F.r ⟨a, b⟩ = o → Σ o : Idx X, Z.obj ⟨o⟩
  | (0, x), h => ⟨(0, x), g x ⟨b, h⟩⟩
  | (1, x), h => ⟨(1, x), (w x ⟨b, h⟩).1⟩

/-- The raw assignment lies over the direction's object. -/
theorem assignAux_fst {a : F.A} (g : ∀ x, F.Direction a (mkIdx 0 x) → Z.obj ⟨mkIdx 0 x⟩)
    (w : ∀ x (d : F.Direction a (mkIdx 1 x)), fibre Z x (g x (dirRestr F a x d))) (b : F.B a) :
    ∀ (o : Idx X) (h : F.r ⟨a, b⟩ = o), (assignAux Z F g w b o h).1 = o
  | (0, _), _ => rfl
  | (1, _), _ => rfl

/-- The raw assignment at the direction-input object is the raw assignment at
any object it equals. -/
theorem assignAux_congr {a : F.A} (g : ∀ x, F.Direction a (mkIdx 0 x) → Z.obj ⟨mkIdx 0 x⟩)
    (w : ∀ x (d : F.Direction a (mkIdx 1 x)), fibre Z x (g x (dirRestr F a x d))) (b : F.B a)
    {o : Idx X} (h : F.r ⟨a, b⟩ = o) :
    assignAux Z F g w b (F.r ⟨a, b⟩) rfl = assignAux Z F g w b o h := by
  subst h
  rfl

/-- The element built from a base assignment and a level-{lit}`1` assignment,
before its naturality. -/
def assignObj {a : F.A} (g : ∀ x, F.Direction a (mkIdx 0 x) → Z.obj ⟨mkIdx 0 x⟩)
    (w : ∀ x (d : F.Direction a (mkIdx 1 x)), fibre Z x (g x (dirRestr F a x d))) :
    F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj Z) :=
  ⟨⟨a, fun b ↦ assignAux Z F g w b (F.r ⟨a, b⟩) rfl⟩,
    funext fun b ↦ assignAux_fst Z F g w b _ rfl⟩

/-- The value the built element gives a level-{lit}`0` direction is the base
assignment. -/
theorem value_assignObj_zero {a : F.A} (g : ∀ x, F.Direction a (mkIdx 0 x) → Z.obj ⟨mkIdx 0 x⟩)
    (w : ∀ x (d : F.Direction a (mkIdx 1 x)), fibre Z x (g x (dirRestr F a x d)))
    (x : X) (d : F.Direction a (mkIdx 0 x)) :
    F.value (assignObj Z F g w) d = g x d :=
  eq_of_heq (Sigma.mk.inj_iff.mp
    ((sigma_value Z F.toPresheafDomPFunctorData (assignObj Z F g w) d).trans
      (assignAux_congr Z F g w d.1 d.2))).2

/-- The value the built element gives a level-{lit}`1` direction is the
level-{lit}`1` assignment. -/
theorem value_assignObj_one {a : F.A} (g : ∀ x, F.Direction a (mkIdx 0 x) → Z.obj ⟨mkIdx 0 x⟩)
    (w : ∀ x (d : F.Direction a (mkIdx 1 x)), fibre Z x (g x (dirRestr F a x d)))
    (x : X) (d : F.Direction a (mkIdx 1 x)) :
    F.value (assignObj Z F g w) d = (w x d).1 :=
  eq_of_heq (Sigma.mk.inj_iff.mp
    ((sigma_value Z F.toPresheafDomPFunctorData (assignObj Z F g w) d).trans
      (assignAux_congr Z F g w d.1 d.2))).2

/-- Two elements of {lit}`Elem` with the same shape are equal when their base
assignments agree and their level-{lit}`1` assignments agree in the level-{lit}`1`
fibres of {lit}`Z`. -/
theorem gw_ext {a : F.A} {g g' : ∀ x, F.Direction a (mkIdx 0 x) → Z.obj ⟨mkIdx 0 x⟩} (hg : g' = g)
    {w : ∀ x (d : F.Direction a (mkIdx 1 x)), fibre Z x (g x (dirRestr F a x d))}
    {w' : ∀ x (d : F.Direction a (mkIdx 1 x)), fibre Z x (g' x (dirRestr F a x d))}
    (hw : ∀ x d, (w' x d).1 = (w x d).1) :
    (⟨g', w'⟩ : Σ g : ∀ x, F.Direction a (mkIdx 0 x) → Z.obj ⟨mkIdx 0 x⟩,
      ∀ x (d : F.Direction a (mkIdx 1 x)), fibre Z x (g x (dirRestr F a x d))) = ⟨g, w⟩ := by
  subst hg
  exact Sigma.ext rfl (heq_of_eq (funext fun x ↦ funext fun d ↦ Subtype.ext (hw x d)))

/-- The value in dependent-type terms of an element. -/
def toElem (x : F.obj Z) : Elem Z F :=
  ⟨x.shape, fun _ d ↦ F.value x.1 d, fun x' d ↦ ⟨F.value x.1 d, (x.2 (waHomAt x') d).symm⟩⟩

/-- The raw assignment rebuilt from an element's values is the element's raw
assignment. -/
theorem assignAux_value (x : F.obj Z) (b : F.B x.shape) :
    ∀ (o : Idx X) (h : F.r ⟨x.shape, b⟩ = o),
      assignAux Z F (fun _ (d : F.Direction x.shape (mkIdx 0 _)) ↦ F.value x.1 d)
        (fun x' (d : F.Direction x.shape (mkIdx 1 x')) ↦ ⟨F.value x.1 d, (x.2 (waHomAt x') d).symm⟩)
        b o h = x.1.1.2 b
  | (0, _), h => sigma_value Z F.toPresheafDomPFunctorData x.1 ⟨b, h⟩
  | (1, _), h => sigma_value Z F.toPresheafDomPFunctorData x.1 ⟨b, h⟩

/-- The value of {lit}`F` at {lit}`Z` is {lit}`Elem Z F`. -/
def elemEquiv : F.obj Z ≃ Elem Z F where
  toFun := toElem Z F
  invFun e := ⟨assignObj Z F e.2.1 e.2.2,
    (isNatural_iff Z F.toPresheafDomPFunctorData F.isFunctorial.directionRestr_id _).mpr
      fun x' d ↦ (value_assignObj_zero Z F _ _ _ _).trans
        ((e.2.2 x' d).2.symm.trans (congrArg _ (value_assignObj_one Z F _ _ x' d).symm))⟩
  left_inv x :=
    Subtype.ext (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun b ↦
      assignAux_value Z F x b _ rfl))))
  right_inv e :=
    Sigma.ext rfl (heq_of_eq (gw_ext Z F
      (funext fun x ↦ funext fun d ↦ value_assignObj_zero Z F e.2.1 e.2.2 x d)
      fun x d ↦ value_assignObj_one Z F e.2.1 e.2.2 x d))

/-! # The transcription of a slice polynomial functor -/

variable (P : SlicePFunctor.{0, 0, 0, 0} X Y)

/-- The directions of the transcription: none for a level-{lit}`0` shape, and
for a level-{lit}`1` shape each direction of {lit}`P` twice, once at level
{lit}`0` and once at level {lit}`1`. -/
def pDir : Y ⊕ P.A → Type
  | .inl _ => PEmpty
  | .inr a => P.B a ⊕ P.B a

/-- The direction-input map: a direction of {lit}`P` lies at its own input
index, at level {lit}`0` or {lit}`1` by its copy. -/
def pR : (Σ s : Y ⊕ P.A, pDir P s) → Idx X
  | ⟨.inl _, e⟩ => PEmpty.elim e
  | ⟨.inr a, .inl b⟩ => (0, P.r ⟨a, b⟩)
  | ⟨.inr a, .inr b⟩ => (1, P.r ⟨a, b⟩)

/-- The shape-output map: a level-{lit}`0` shape lies at its index, a
level-{lit}`1` shape at the output index of {lit}`P`. -/
def pQ : Y ⊕ P.A → Idx Y
  | .inl y => (0, y)
  | .inr a => (1, P.q a)

/-- The slice polynomial functor on the objects of {lit}`Idx X` and
{lit}`Idx Y` underlying the transcription. -/
def prodSlice : SlicePFunctor.{0, 0, 0, 0} (Idx X) (Idx Y) where
  toPFunctor := ⟨Y ⊕ P.A, pDir P⟩
  r := pR P
  q := pQ P

/-- The direction restriction to a target level: the level-{lit}`1` copy of
a direction restricts to its level-{lit}`0` copy. -/
def restrDir (s : Y ⊕ P.A) (t : Fin 2) : pDir P s → pDir P s :=
  match s with
  | .inl _ => fun e ↦ e
  | .inr _ => fun d ↦
    match d, t with
    | .inl b, _ => .inl b
    | .inr b, 0 => .inl b
    | .inr b, 1 => .inr b

/-- The restricted direction lies over the target level at the same index. -/
theorem restrDir_over (s : Y ⊕ P.A) (t : Fin 2) (d : pDir P s) {i : Fin 2} {x : X}
    (hd : pR P ⟨s, d⟩ = (i, x)) (ht : t ≤ i) :
    pR P ⟨s, restrDir P s t d⟩ = (t, x) := by
  match s, d, t with
  | .inl _, e, _ => exact PEmpty.elim e
  | .inr a, .inl b, 0 => exact Prod.ext rfl (congrArg Prod.snd hd : P.r ⟨a, b⟩ = x)
  | .inr _, .inl _, 1 =>
    have h0 : (0 : Fin 2) = i := congrArg Prod.fst hd
    subst h0
    exact absurd ht (by decide)
  | .inr a, .inr b, 0 => exact Prod.ext rfl (congrArg Prod.snd hd : P.r ⟨a, b⟩ = x)
  | .inr a, .inr b, 1 => exact Prod.ext rfl (congrArg Prod.snd hd : P.r ⟨a, b⟩ = x)

/-- The shape restriction to a target level: a level-{lit}`1` shape restricts
to the level-{lit}`0` shape at its output index. -/
def restrShape (t : Fin 2) : Y ⊕ P.A → Y ⊕ P.A
  | .inl y => .inl y
  | .inr a =>
    match t with
    | 0 => .inl (P.q a)
    | 1 => .inr a

/-- The restricted shape lies over the target level at the same index. -/
theorem restrShape_over (t : Fin 2) (s : Y ⊕ P.A) {i : Fin 2} {y : Y}
    (hs : pQ P s = (i, y)) (ht : t ≤ i) :
    pQ P (restrShape P t s) = (t, y) := by
  match s, t with
  | .inl y', 0 => exact Prod.ext rfl (congrArg Prod.snd hs : y' = y)
  | .inl _, 1 =>
    have h0 : (0 : Fin 2) = i := congrArg Prod.fst hs
    subst h0
    exact absurd ht (by decide)
  | .inr a, 0 => exact Prod.ext rfl (congrArg Prod.snd hs : P.q a = y)
  | .inr a, 1 => exact Prod.ext rfl (congrArg Prod.snd hs : P.q a = y)

/-- The reindexing of directions along a shape restriction: a level-{lit}`0`
shape has none, so it is the identity where defined. -/
def reindexDir (s : Y ⊕ P.A) (t : Fin 2) : pDir P (restrShape P t s) → pDir P s :=
  match s, t with
  | .inl _, _ => fun e ↦ e
  | .inr _, 0 => fun e ↦ PEmpty.elim e
  | .inr _, 1 => fun d ↦ d

/-- Reindexing preserves the direction-input object. -/
theorem reindexDir_over (s : Y ⊕ P.A) (t : Fin 2) (d : pDir P (restrShape P t s)) :
    pR P ⟨s, reindexDir P s t d⟩ = pR P ⟨restrShape P t s, d⟩ := by
  match s, t, d with
  | .inl _, _, e => exact PEmpty.elim e
  | .inr _, 0, e => exact PEmpty.elim e
  | .inr _, 1, _ => rfl

/-- The direction restriction along a morphism of {lit}`Idx X`. -/
def directionRestr (s : Y ⊕ P.A) ⦃o o' : Idx X⦄ (f : o' ⟶ o)
    (d : (prodSlice P).Direction s o) : (prodSlice P).Direction s o' :=
  ⟨restrDir P s o'.1 d.1, by
    obtain ⟨i, x⟩ := o
    obtain ⟨i', x'⟩ := o'
    obtain rfl : x' = x := (leOfHom f).2
    exact restrDir_over P s i' d.1 d.2 (leOfHom f).1⟩

/-- The shape restriction along a morphism of {lit}`Idx Y`. -/
def shapeRestr ⦃o o' : Idx Y⦄ (g : o' ⟶ o) (s : (prodSlice P).Shape o) :
    (prodSlice P).Shape o' :=
  ⟨restrShape P o'.1 s.1, by
    obtain ⟨i, y⟩ := o
    obtain ⟨i', y'⟩ := o'
    obtain rfl : y' = y := (leOfHom g).2
    exact restrShape_over P i' s.1 s.2 (leOfHom g).1⟩

/-- The reindexing of directions along a morphism of {lit}`Idx Y`. -/
def reindex ⦃o o' : Idx Y⦄ (g : o' ⟶ o) (s : (prodSlice P).Shape o) ⦃p : Idx X⦄
    (d : (prodSlice P).Direction (shapeRestr P g s).1 p) : (prodSlice P).Direction s.1 p :=
  ⟨reindexDir P s.1 o'.1 d.1, (reindexDir_over P s.1 o'.1 d.1).trans d.2⟩

/-- The operations of the transcription. -/
def prodData : PresheafPFunctorData.{0, 0, 0, 0, 0, 0} (Idx X) (Idx Y) :=
  { prodSlice P with
    directionRestr := directionRestr P
    shapeRestr := shapeRestr P
    reindex := reindex P }

/-- Direction restriction along an identity is the identity. -/
theorem directionRestr_id : (prodData P).DirectionRestrId := by
  intro s o
  funext d
  obtain ⟨d, hd⟩ := d
  refine Subtype.ext ?_
  match s, d with
  | .inl _, e => exact PEmpty.elim e
  | .inr _, .inl _ => rfl
  | .inr _, .inr _ =>
    have h1 : ((1 : Fin 2), _) = o := hd
    subst h1
    rfl

/-- Direction restriction reverses composition. -/
theorem directionRestr_comp : (prodData P).DirectionRestrComp := by
  intro s o o' o'' f g
  funext d
  obtain ⟨d, hd⟩ := d
  refine Subtype.ext ?_
  match s, d with
  | .inl _, e => exact PEmpty.elim e
  | .inr _, .inl _ => rfl
  | .inr _, .inr _ =>
    have h1 : ((1 : Fin 2), _) = o := hd
    subst h1
    obtain ⟨i', _⟩ := o'
    obtain ⟨i'', _⟩ := o''
    match i', i'' with
    | 0, 0 => rfl
    | 1, 0 => rfl
    | 1, 1 => rfl
    | 0, 1 => exact absurd (leOfHom g).1 (by change ¬ ((1 : Fin 2) ≤ 0); decide)

/-- Shape restriction along an identity is the identity. -/
theorem shapeRestr_id : (prodData P).ShapeRestrId := by
  intro o
  funext s
  obtain ⟨s, hs⟩ := s
  refine Subtype.ext ?_
  match s with
  | .inl _ => rfl
  | .inr _ =>
    have h1 : ((1 : Fin 2), _) = o := hs
    subst h1
    rfl

/-- Shape restriction reverses composition. -/
theorem shapeRestr_comp : (prodData P).ShapeRestrComp := by
  intro o o' o'' g h
  funext s
  obtain ⟨s, hs⟩ := s
  refine Subtype.ext ?_
  match s with
  | .inl _ => rfl
  | .inr _ =>
    have h1 : ((1 : Fin 2), _) = o := hs
    subst h1
    obtain ⟨i', _⟩ := o'
    obtain ⟨i'', _⟩ := o''
    match i', i'' with
    | 0, 0 => rfl
    | 1, 0 => rfl
    | 1, 1 => rfl
    | 0, 1 => exact absurd (leOfHom h).1 (by change ¬ ((1 : Fin 2) ≤ 0); decide)

/-- Reindexing commutes with direction restriction. -/
theorem reindex_naturality : (prodData P).ReindexNaturality := by
  intro o o' g s p p' f
  funext d
  obtain ⟨d, hd⟩ := d
  refine Subtype.ext ?_
  obtain ⟨s, hs⟩ := s
  cases s with
  | inl _ => exact PEmpty.elim d
  | inr _ =>
    have h1 : ((1 : Fin 2), _) = o := hs
    subst h1
    obtain ⟨i', _⟩ := o'
    match i' with
    | 1 => rfl
    | 0 => exact PEmpty.elim d

/-- Reindexing along an identity is the identity. -/
theorem reindex_id : (prodData P).ReindexId (shapeRestr_id P) := by
  intro o s p d
  obtain ⟨s, hs⟩ := s
  obtain ⟨d, hd⟩ := d
  match s with
  | .inl _ =>
    refine Subtype.ext ?_
    exact PEmpty.elim d
  | .inr _ =>
    have h1 : ((1 : Fin 2), _) = o := hs
    subst h1
    refine Subtype.ext ?_
    rfl

/-- Reindexing along a composite is the composite of the reindexings. -/
theorem reindex_comp : (prodData P).ReindexComp (shapeRestr_comp P) := by
  intro o o' o'' g h s p d
  obtain ⟨s, hs⟩ := s
  obtain ⟨d, hd⟩ := d
  match s with
  | .inl _ =>
    refine Subtype.ext ?_
    exact PEmpty.elim d
  | .inr _ =>
    have h1 : ((1 : Fin 2), _) = o := hs
    subst h1
    refine Subtype.ext ?_
    obtain ⟨i', _⟩ := o'
    obtain ⟨i'', _⟩ := o''
    match i', i'' with
    | 0, 0 => exact PEmpty.elim d
    | 1, 0 => exact PEmpty.elim d
    | 1, 1 => rfl
    | 0, 1 => exact absurd (leOfHom h).1 (by change ¬ ((1 : Fin 2) ≤ 0); decide)

/-- The transcription's operations satisfy the functor laws. -/
theorem prodData_isFunctorial : (prodData P).IsFunctorial where
  directionRestr_id := directionRestr_id P
  directionRestr_comp := directionRestr_comp P
  shapeRestr_id := shapeRestr_id P
  shapeRestr_comp := shapeRestr_comp P
  reindex_naturality := reindex_naturality P
  reindex_id := reindex_id P
  reindex_comp := reindex_comp P

/-- The transcription of a slice polynomial functor {lit}`Type/X → Type/Y` to
a presheaf polynomial functor from presheaves on {lit}`Idx X` to presheaves
on {lit}`Idx Y`. -/
def prodPsh : PresheafPFunctor.{0, 0, 0, 0, 0, 0} (Idx X) (Idx Y) :=
  { prodData P with isFunctorial := prodData_isFunctorial P }

/-! # Objects of the slice as presheaves -/

/-- The fibres of the presheaf of an object {lit}`p : E → X` of {lit}`Type/X`:
a point at every level {lit}`0`, the fibre of {lit}`p` at level {lit}`1`. -/
def sliceObj {E : Type} (p : E → X) : Idx X → Type
  | (0, _) => Unit
  | (1, x) => { e : E // p e = x }

/-- The restriction maps of that presheaf. -/
def sliceMap {E : Type} (p : E → X) :
    ∀ (o o' : Idx X), (o' ⟶ o) → sliceObj p o → sliceObj p o'
  | (0, _), (0, _), _ => fun u ↦ u
  | (1, _), (1, _), f => fun e ↦ ⟨e.1, e.2.trans (leOfHom f).2.symm⟩
  | (1, _), (0, _), _ => fun _ ↦ ()
  | (0, _), (1, _), f => absurd (leOfHom f).1 (by change ¬ ((1 : Fin 2) ≤ 0); decide)

/-- An object {lit}`p : E → X` of {lit}`Type/X` as a presheaf on {lit}`Idx X`. -/
def ofSliceX {E : Type} (p : E → X) : (Idx X)ᵒᵖ ⥤ Type where
  obj o := sliceObj p o.unop
  map f := ↾ sliceMap p _ _ f.unop
  map_id o :=
    match o with
    | ⟨(0, _)⟩ => rfl
    | ⟨(1, _)⟩ => rfl
  map_comp {o o' o''} f g :=
    match o, o', o'', f, g with
    | ⟨(0, _)⟩, ⟨(0, _)⟩, ⟨(0, _)⟩, _, _ => rfl
    | ⟨(1, _)⟩, ⟨(1, _)⟩, ⟨(1, _)⟩, _, _ => rfl
    | ⟨(1, _)⟩, ⟨(0, _)⟩, ⟨(0, _)⟩, _, _ => rfl
    | ⟨(1, _)⟩, ⟨(1, _)⟩, ⟨(0, _)⟩, _, _ => rfl
    | ⟨(1, _)⟩, ⟨(0, _)⟩, ⟨(1, _)⟩, _, g =>
      absurd (leOfHom g.unop).1 (by change ¬ ((1 : Fin 2) ≤ 0); decide)
    | ⟨(0, _)⟩, ⟨(1, _)⟩, _, f, _ =>
      absurd (leOfHom f.unop).1 (by change ¬ ((1 : Fin 2) ≤ 0); decide)
    | ⟨(0, _)⟩, ⟨(0, _)⟩, ⟨(1, _)⟩, _, g =>
      absurd (leOfHom g.unop).1 (by change ¬ ((1 : Fin 2) ≤ 0); decide)

/-- The components of a morphism over {lit}`X` as a natural transformation:
the identity at level {lit}`0`, the morphism on fibres at level {lit}`1`. -/
def sliceHomApp {E E' : Type} {p : E → X} {p' : E' → X} (h : E → E') (hh : p' ∘ h = p) :
    ∀ o : Idx X, sliceObj p o → sliceObj p' o
  | (0, _) => fun u ↦ u
  | (1, _) => fun e ↦ ⟨h e.1, (congrFun hh e.1).trans e.2⟩

/-- A morphism {lit}`h` over {lit}`X`, {lit}`p' ∘ h = p`, as a natural
transformation {lit}`ofSliceX p ⟶ ofSliceX p'`. -/
def ofSliceXHom {E E' : Type} {p : E → X} {p' : E' → X} (h : E → E') (hh : p' ∘ h = p) :
    NatTrans (ofSliceX p) (ofSliceX p') where
  app o := ↾ sliceHomApp h hh o.unop
  naturality {o o'} f :=
    match o, o', f with
    | ⟨(0, _)⟩, ⟨(0, _)⟩, _ => rfl
    | ⟨(1, _)⟩, ⟨(1, _)⟩, _ => rfl
    | ⟨(1, _)⟩, ⟨(0, _)⟩, _ => rfl
    | ⟨(0, _)⟩, ⟨(1, _)⟩, f => absurd (leOfHom f.unop).1 (by change ¬ ((1 : Fin 2) ≤ 0); decide)

/-! # The value at an object of the slice -/

/-- The level-{lit}`1` elements of the transcription's value at
{lit}`ofSliceX p` over {lit}`(1, y)`, in dependent-type terms. -/
abbrev ElemOver {E : Type} (p : E → X) (y : Y) : Type :=
  { e : Elem (ofSliceX p) (prodPsh P) // pQ P e.1 = mkIdx 1 y }

/-- From an element over {lit}`(1, y)` to the slice functor's value over
{lit}`y`: the level-{lit}`1` assignment at each direction's own input index. -/
def toSliceObj {E : Type} (p : E → X) (y : Y) (e : ElemOver P p y) :
    { o : P.toSliceDomPFunctor.Obj p // P.obj p o = y } :=
  match e with
  | ⟨⟨.inl _, _, _⟩, h⟩ => absurd (congrArg Prod.fst h) Fin.zero_ne_one
  | ⟨⟨.inr a, _, w⟩, h⟩ =>
    ⟨⟨⟨a, fun b ↦ (w (P.r ⟨a, b⟩) ⟨.inr b, rfl⟩).1.1⟩,
      funext fun b ↦ (w (P.r ⟨a, b⟩) ⟨.inr b, rfl⟩).1.2⟩, congrArg Prod.snd h⟩

/-- The level-{lit}`1` assignment of the element built from a value of the
slice functor: at the level-{lit}`1` copy of a direction, its assigned element
of the fibre. -/
def ofSliceObjW {E : Type} (p : E → X) (o : P.toSliceDomPFunctor.Obj p) (x : X)
    (d : (prodSlice P).Direction (.inr o.1.1) (mkIdx 1 x)) :
    fibre (ofSliceX p) x () :=
  match d with
  | ⟨.inl _, hd⟩ => absurd (congrArg Prod.fst hd) Fin.zero_ne_one
  | ⟨.inr b, hd⟩ => ⟨⟨o.1.2 b, (congrFun o.2 b).trans (congrArg Prod.snd hd)⟩, rfl⟩

/-- From the slice functor's value over {lit}`y` to an element over
{lit}`(1, y)`. -/
def ofSliceObj {E : Type} (p : E → X) (y : Y)
    (o : { o : P.toSliceDomPFunctor.Obj p // P.obj p o = y }) : ElemOver P p y :=
  ⟨⟨.inr o.1.1.1, fun _ _ ↦ (), fun x d ↦ ofSliceObjW P p o.1 x d⟩, Prod.ext rfl o.2⟩

/-- The level-{lit}`1` value of the transcription at {lit}`ofSliceX p` over
{lit}`(1, y)`, in dependent-type terms, is the slice functor's value at
{lit}`p` over {lit}`y`. -/
def elemOverEquiv {E : Type} (p : E → X) (y : Y) :
    ElemOver P p y ≃ { o : P.toSliceDomPFunctor.Obj p // P.obj p o = y } where
  toFun := toSliceObj P p y
  invFun := ofSliceObj P p y
  left_inv e := by
    obtain ⟨⟨s, g, w⟩, h⟩ := e
    match s with
    | .inl _ => exact absurd (congrArg Prod.fst h) Fin.zero_ne_one
    | .inr a =>
      refine Subtype.ext (Sigma.ext rfl (heq_of_eq (gw_ext (ofSliceX p) (prodPsh P)
        (funext fun _ ↦ funext fun _ ↦ rfl) fun x d ↦ ?_)))
      obtain ⟨d, hd⟩ := d
      match d with
      | .inl _ => exact absurd (congrArg Prod.fst hd) Fin.zero_ne_one
      | .inr b =>
        have hx : P.r ⟨a, b⟩ = x := congrArg Prod.snd hd
        subst hx
        rfl
  right_inv o := Subtype.ext (Subtype.ext rfl)

/-- The elements of the transcription's value over {lit}`(1, y)` are the
elements of {lit}`Elem` over it. -/
def objLevelOne {E : Type} (p : E → X) (y : Y) :
    { t : (prodPsh P).obj (ofSliceX p) // (prodPsh P).q t.shape = mkIdx 1 y } ≃ ElemOver P p y where
  toFun t := ⟨toElem (ofSliceX p) (prodPsh P) t.1, t.2⟩
  invFun e := ⟨(elemEquiv (ofSliceX p) (prodPsh P)).symm e.1, e.2⟩
  left_inv t := Subtype.ext ((elemEquiv (ofSliceX p) (prodPsh P)).left_inv t.1)
  right_inv e := Subtype.ext ((elemEquiv (ofSliceX p) (prodPsh P)).right_inv e.1)

/-- The level-{lit}`1` value of the transcription at {lit}`ofSliceX p` over
{lit}`(1, y)` is the slice functor's value at {lit}`p` over {lit}`y`. -/
def levelOneEquiv {E : Type} (p : E → X) (y : Y) :
    { t : (prodPsh P).obj (ofSliceX p) // (prodPsh P).q t.shape = mkIdx 1 y } ≃
      { o : P.toSliceDomPFunctor.Obj p // P.obj p o = y } :=
  (objLevelOne P p y).trans (elemOverEquiv P p y)

/-- An element of {lit}`Elem` over {lit}`(0, y)` is the level-{lit}`0` shape at
{lit}`y` with its empty assignments. -/
theorem elem_zero_ext {E : Type} (p : E → X) (y : Y) (e : Elem (ofSliceX p) (prodPsh P))
    (h : pQ P e.1 = mkIdx 0 y) :
    e = ⟨(Sum.inl y : Y ⊕ P.A),
      fun x (d : (prodPsh P).Direction (Sum.inl y : Y ⊕ P.A) (mkIdx 0 x)) ↦ PEmpty.elim d.1,
      fun x (d : (prodPsh P).Direction (Sum.inl y : Y ⊕ P.A) (mkIdx 1 x)) ↦ PEmpty.elim d.1⟩ := by
  obtain ⟨s, g, w⟩ := e
  cases s with
  | inl y' =>
    have hy : y' = y := congrArg Prod.snd h
    subst hy
    exact Sigma.ext rfl (heq_of_eq (gw_ext (ofSliceX p) (prodPsh P)
      (funext fun x ↦ funext
        fun (d : (prodPsh P).Direction (Sum.inl y' : Y ⊕ P.A) (mkIdx 0 x)) ↦ PEmpty.elim d.1)
      fun x (d : (prodPsh P).Direction (Sum.inl y' : Y ⊕ P.A) (mkIdx 1 x)) ↦ PEmpty.elim d.1))
  | inr _ => exact absurd (congrArg Prod.fst h).symm Fin.zero_ne_one

/-- The transcription's base at {lit}`ofSliceX p` is a point at every index:
the level-{lit}`0` shape at the index with its empty assignments. -/
def levelZeroEquiv {E : Type} (p : E → X) (y : Y) :
    { t : (prodPsh P).obj (ofSliceX p) // (prodPsh P).q t.shape = mkIdx 0 y } ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨(elemEquiv (ofSliceX p) (prodPsh P)).symm
    ⟨(Sum.inl y : Y ⊕ P.A),
      fun x (d : (prodPsh P).Direction (Sum.inl y : Y ⊕ P.A) (mkIdx 0 x)) ↦ PEmpty.elim d.1,
      fun x (d : (prodPsh P).Direction (Sum.inl y : Y ⊕ P.A) (mkIdx 1 x)) ↦ PEmpty.elim d.1⟩, rfl⟩
  left_inv t :=
    Subtype.ext ((elemEquiv (ofSliceX p) (prodPsh P)).injective
      ((elem_zero_ext P p y (toElem (ofSliceX p) (prodPsh P) t.1) t.2).trans
        ((elemEquiv (ofSliceX p) (prodPsh P)).apply_symm_apply _).symm).symm)
  right_inv _ := rfl

/-- The comparison map from the slice functor's value to the transcription's
value: the level-{lit}`1` element with the given assignments. -/
def cmp {E : Type} (p : E → X) (o : P.toSliceDomPFunctor.Obj p) : (prodPsh P).obj (ofSliceX p) :=
  ((levelOneEquiv P p (P.obj p o)).symm ⟨o, rfl⟩).1

/-- The comparison map is natural in the object of {lit}`Type/X`. -/
theorem map_cmp {E E' : Type} {p : E → X} {p' : E' → X} (h : E → E') (hh : p' ∘ h = p)
    (o : P.toSliceDomPFunctor.Obj p) :
    (prodPsh P).map (ofSliceXHom h hh) (cmp P p o) = cmp P p' (P.map h hh o) := by
  obtain ⟨⟨a, v⟩, hv⟩ := o
  refine Subtype.ext (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun d ↦ ?_))))
  match d with
  | .inl _ => rfl
  | .inr _ => rfl

/-! # The slice W-type is a fixed point -/

variable (Q : SlicePFunctor.{0, 0, 0, 0} X X)

/-- The slice W-type as a presheaf on {lit}`Idx X`. -/
abbrev wPsh : (Idx X)ᵒᵖ ⥤ Type :=
  ofSliceX Q.wIndex

/-- The slice functor's value at its W-type over {lit}`x` is the W-type's fibre
over {lit}`x`: the constructor and destructor of {name}`SlicePFunctor.W`. -/
def wObjEquiv (x : X) :
    { o : Q.toSliceDomPFunctor.Obj Q.wIndex // Q.obj Q.wIndex o = x } ≃
      { z : Q.W // Q.wIndex z = x } where
  toFun o := ⟨SlicePFunctor.W.mk o.1, (SlicePFunctor.W.wIndex_mk o.1).trans o.2⟩
  invFun z := ⟨SlicePFunctor.W.dest z.1,
    ((SlicePFunctor.W.wIndex_mk _).symm.trans
      (congrArg Q.wIndex (SlicePFunctor.W.mk_dest z.1))).trans z.2⟩
  left_inv o := Subtype.ext (SlicePFunctor.W.dest_mk o.1)
  right_inv z := Subtype.ext (SlicePFunctor.W.mk_dest z.1)

/-- The slice W-type is a fixed point of the transcription: the transcription's
level-{lit}`1` value at the W-type's presheaf over {lit}`(1, x)` is the W-type's
fibre over {lit}`x`, which is that presheaf's own value at {lit}`(1, x)`, and
its level {lit}`0` is a point, as is the presheaf's. -/
def wFixed (x : X) :
    { t : (prodPsh Q).obj (wPsh Q) // (prodPsh Q).q t.shape = mkIdx 1 x } ≃
      (wPsh Q).obj ⟨mkIdx 1 x⟩ :=
  (levelOneEquiv Q Q.wIndex x).trans (wObjEquiv Q x)

end GebProto.LargeIR.Product
