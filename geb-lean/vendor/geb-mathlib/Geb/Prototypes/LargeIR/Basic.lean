/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.PresheafIRUniv.Basic

set_option doc.verso true

/-!
# Prototype: slice polynomial functors as presheaf polynomial endofunctors on the walking arrow

Throwaway exploration, not upstream-eligible content. Every declaration here
is {name}`Classical.choice`-free.

A slice polynomial functor {lit}`Type/X → Type/Y` is given in dependent-type
terms by a shape family {lit}`shape : Y → Type` and a direction family
{lit}`dir : (Σ y, shape y) → X → Type`. A presheaf polynomial endofunctor on
the presheaves over the walking arrow {lit}`0 ⟶ 1` — the category
{lit}`Fin 2` as a preorder, whose presheaves are the objects
{lit}`Z 1 → Z 0` of the arrow category of {lit}`Type`, equivalently the
free coproduct completion {lit}`Fam(Type)` — is given by a shape presheaf and,
for each shape, a direction presheaf. This module transcribes a slice
polynomial functor into such an endofunctor, {lit}`arrowPsh`, by placing
{lit}`Y` at level {lit}`0`, the shapes {lit}`Σ y, shape y` at level {lit}`1`,
and giving every shape the constant direction presheaf {lit}`X` at level
{lit}`0` with the slice functor's own directions at level {lit}`1`, and then
computes what the endofunctor does.

The computation, {lit}`objEquiv`, is the point of the prototype. The value of
{lit}`arrowPsh P` at a presheaf {lit}`Z` is not the slice functor's value: its
level {lit}`0` is {lit}`Y × (X → Z 0)`, and its level {lit}`1` over a pair
{lit}`(y, f₀)` is {lit}`P` applied to the pullback of the family
{lit}`Z 1 → Z 0` along {lit}`f₀ : X → Z 0`. The base map {lit}`f₀` is free
because a presheaf morphism out of a direction presheaf whose level {lit}`0`
is {lit}`X` carries a component {lit}`X → Z 0`, and a polynomial functor on
{lit}`Fam(Type)` sees the base of its argument only through such homs. So
{lit}`arrowPsh P` is the left Kan extension of {lit}`P` along the inclusion of
the fibre {lit}`Type/X` into {lit}`Fam(Type)`, an inclusion that is faithful
but not full, and the slice functor is recovered from it only along the section
{lit}`y ↦ (y, id)`: {lit}`pullbackIdEquiv` identifies the level-{lit}`1` fibre
over {lit}`(y, id)` at an input of base {lit}`X` with the slice functor's
value, {lit}`cmp` is the resulting comparison map, {lit}`map_cmp` its
naturality, and {lit}`toLevels_objRestr_cmp` that its image restricts to
{lit}`(y, id)` along {lit}`0 ⟶ 1`.

The surviving {lit}`Σ (f₀ : X → Z 0)` is the {lit}`δ` constructor of
inductive-recursive codes, {lit}`⟦δ A F⟧ (U, T) = Σ (g : A → U), ⟦F (T ∘ g)⟧ (U, T)`
(\[DybjerSetzer2003\], and \[GhaniNordvallForsbergMalatesta2015\] for
its functorial reading on {lit}`Fam(C)`): read with {lit}`X` the arity and
{lit}`Z 0` the universe, the transcription of a slice polynomial functor is
the large-IR code whose continuation is that functor applied to the decoded
family, rather than the slice functor itself.

## Main definitions

* {lit}`arrowSlice` — the slice polynomial functor on the objects of the
  walking arrow underlying the transcription: shapes {lit}`Y ⊕ P.A`,
  directions {lit}`X ⊕ fibDir P s`.
* {lit}`arrowPsh` — the presheaf polynomial endofunctor, with the restriction
  and reindexing maps and their laws.
* {lit}`pullbackAlong` — the pullback of the family {lit}`Z 1 → Z 0` along a
  map {lit}`X → Z 0`, as an object of {lit}`Type/X`.
* {lit}`Levels` — the value of the transcription computed in dependent-type
  terms: level {lit}`0` is {lit}`Y × (X → Z 0)`, level {lit}`1` is the sum over
  {lit}`f₀ : X → Z 0` of {lit}`P` at the pullback along {lit}`f₀`.
* {lit}`objEquiv` — the equivalence of {lit}`(arrowPsh P).obj Z` with
  {lit}`Levels P Z`, through {lit}`toLevels` and {lit}`ofLevels`.
* {lit}`ofSlice` — an object {lit}`p : E → X` of {lit}`Type/X` as a walking-arrow
  presheaf; {lit}`ofSliceHom` a morphism over {lit}`X` as a natural
  transformation.
* {lit}`pullbackIdEquiv` — the pullback along the identity is the object
  itself, at the level of the slice functor's values.
* {lit}`cmp` — the comparison map from the slice functor's value to the
  transcription's value at {lit}`ofSlice p`: the level-{lit}`1` element over
  {lit}`(y, id)`.

## Main statements

* {lit}`isNatural_iff` — over the walking arrow, naturality of a direction
  assignment is its equation along the one non-identity morphism.
* {lit}`toLevels_objRestr` — restricting a level-{lit}`1` element over
  {lit}`(y, f₀)` along {lit}`0 ⟶ 1` gives the level-{lit}`0` element
  {lit}`(y, f₀)`, with {lit}`y` the slice functor's output index.
* {lit}`map_cmp` — the comparison map is natural in the object of {lit}`Type/X`.
* {lit}`toLevels_objRestr_cmp` — the comparison map's image restricts to
  {lit}`(y, id)`.

## References

* \[DybjerSetzer2003\]
* \[GhaniNordvallForsbergMalatesta2015\]
* \[Weber2007\]

## Tags

prototype, presheaf, walking arrow, parametric right adjoint, slice polynomial
functor, inductive-recursive, free coproduct completion
-/

@[expose] public section

open CategoryTheory PresheafIRUniv

namespace GebProto.LargeIR

variable {X Y : Type}

/-! # The endofunctor -/

/-- The level-{lit}`1` directions of a shape: none for a level-{lit}`0` shape
{lit}`y`, the slice functor's directions for a level-{lit}`1` shape {lit}`a`. -/
def fibDir (P : SlicePFunctor.{0, 0, 0, 0} X Y) : Y ⊕ P.A → Type
  | .inl _ => PEmpty
  | .inr a => P.B a

/-- The input index in {lit}`X` of a level-{lit}`1` direction: the slice
functor's direction-input map. -/
def fibR (P : SlicePFunctor.{0, 0, 0, 0} X Y) : (Σ s : Y ⊕ P.A, fibDir P s) → X
  | ⟨.inl _, e⟩ => PEmpty.elim e
  | ⟨.inr a, b⟩ => P.r ⟨a, b⟩

/-- The slice polynomial functor on the objects of the walking arrow underlying
the transcription: the level-{lit}`0` shapes are {lit}`Y`, the level-{lit}`1`
shapes are {lit}`P.A`, every shape has the directions {lit}`X` at level
{lit}`0`, and a level-{lit}`1` shape additionally has the slice functor's
directions at level {lit}`1`. -/
def arrowSlice (P : SlicePFunctor.{0, 0, 0, 0} X Y) :
    SlicePFunctor.{0, 0, 0, 0} (Fin 2) (Fin 2) where
  toPFunctor := ⟨Y ⊕ P.A, fun s ↦ X ⊕ fibDir P s⟩
  r := fun d ↦ Sum.elim (fun _ ↦ 0) (fun _ ↦ 1) d.2
  q := Sum.elim (fun _ ↦ 0) (fun _ ↦ 1)

/-- The direction restriction to a target index {lit}`t`: a level-{lit}`0`
direction is fixed, and a level-{lit}`1` direction restricted to level
{lit}`0` is its input index in {lit}`X`. -/
def restrDir (P : SlicePFunctor.{0, 0, 0, 0} X Y) (s : Y ⊕ P.A) (t : Fin 2) :
    X ⊕ fibDir P s → X ⊕ fibDir P s
  | .inl x => .inl x
  | .inr b =>
    match t with
    | 0 => .inl (fibR P ⟨s, b⟩)
    | 1 => .inr b

/-- The restricted direction lies over the target index. -/
theorem restrDir_over (P : SlicePFunctor.{0, 0, 0, 0} X Y) (s : Y ⊕ P.A) (t : Fin 2)
    (d : X ⊕ fibDir P s) {i : Fin 2} (hd : (arrowSlice P).r ⟨s, d⟩ = i) (ht : t ≤ i) :
    (arrowSlice P).r ⟨s, restrDir P s t d⟩ = t := by
  subst hd
  match d, t with
  | .inl _, 0 => rfl
  | .inl _, 1 => exact absurd ht (by change ¬ ((1 : Fin 2) ≤ 0); decide)
  | .inr _, 0 => rfl
  | .inr _, 1 => rfl

/-- The shape restriction to a target index {lit}`t`: a level-{lit}`0` shape is
fixed, and a level-{lit}`1` shape restricted to level {lit}`0` is its output
index in {lit}`Y`. -/
def restrShape (P : SlicePFunctor.{0, 0, 0, 0} X Y) (t : Fin 2) : Y ⊕ P.A → Y ⊕ P.A
  | .inl y => .inl y
  | .inr a =>
    match t with
    | 0 => .inl (P.q a)
    | 1 => .inr a

/-- The restricted shape lies over the target index. -/
theorem restrShape_over (P : SlicePFunctor.{0, 0, 0, 0} X Y) (t : Fin 2) (s : Y ⊕ P.A)
    {j : Fin 2} (hs : (arrowSlice P).q s = j) (ht : t ≤ j) :
    (arrowSlice P).q (restrShape P t s) = t := by
  subst hs
  match s, t with
  | .inl _, 0 => rfl
  | .inl _, 1 => exact absurd ht (by change ¬ ((1 : Fin 2) ≤ 0); decide)
  | .inr _, 0 => rfl
  | .inr _, 1 => rfl

/-- The reindexing of level-{lit}`1` directions along a shape restriction: the
identity where the restricted shape has any. -/
def reindexFib (P : SlicePFunctor.{0, 0, 0, 0} X Y) :
    (s : Y ⊕ P.A) → (t : Fin 2) → fibDir P (restrShape P t s) → fibDir P s
  | .inl _, _, e => e
  | .inr _, 0, e => PEmpty.elim e
  | .inr _, 1, b => b

/-- The reindexing of directions along a shape restriction: the identity on
level-{lit}`0` directions, {lit}`reindexFib` on level-{lit}`1` ones. -/
def reindexDir (P : SlicePFunctor.{0, 0, 0, 0} X Y) (s : Y ⊕ P.A) (t : Fin 2) :
    X ⊕ fibDir P (restrShape P t s) → X ⊕ fibDir P s
  | .inl x => .inl x
  | .inr b => .inr (reindexFib P s t b)

/-- Reindexing preserves the level of a direction. -/
theorem reindexDir_over (P : SlicePFunctor.{0, 0, 0, 0} X Y) (s : Y ⊕ P.A) (t : Fin 2)
    (d : X ⊕ fibDir P (restrShape P t s)) :
    (arrowSlice P).r ⟨s, reindexDir P s t d⟩ = (arrowSlice P).r ⟨restrShape P t s, d⟩ := by
  cases d <;> rfl

/-- Reindexing preserves the input index of a level-{lit}`1` direction. -/
theorem fibR_reindexFib (P : SlicePFunctor.{0, 0, 0, 0} X Y) (s : Y ⊕ P.A) (t : Fin 2)
    (b : fibDir P (restrShape P t s)) :
    fibR P ⟨s, reindexFib P s t b⟩ = fibR P ⟨restrShape P t s, b⟩ := by
  match s, t, b with
  | .inl _, _, e => exact PEmpty.elim e
  | .inr _, 0, e => exact PEmpty.elim e
  | .inr _, 1, _ => rfl

/-- The direction restriction along a walking-arrow morphism. -/
def directionRestr (P : SlicePFunctor.{0, 0, 0, 0} X Y) (s : Y ⊕ P.A) ⦃i i' : Fin 2⦄
    (f : i' ⟶ i) (d : (arrowSlice P).Direction s i) : (arrowSlice P).Direction s i' :=
  ⟨restrDir P s i' d.val, restrDir_over P s i' d.val d.property (leOfHom f)⟩

/-- The shape restriction along a walking-arrow morphism. -/
def shapeRestr (P : SlicePFunctor.{0, 0, 0, 0} X Y) ⦃j j' : Fin 2⦄ (g : j' ⟶ j)
    (s : (arrowSlice P).Shape j) : (arrowSlice P).Shape j' :=
  ⟨restrShape P j' s.val, restrShape_over P j' s.val s.property (leOfHom g)⟩

/-- The reindexing of directions along a walking-arrow morphism. -/
def reindex (P : SlicePFunctor.{0, 0, 0, 0} X Y) ⦃j j' : Fin 2⦄ (g : j' ⟶ j)
    (s : (arrowSlice P).Shape j) ⦃i : Fin 2⦄
    (d : (arrowSlice P).Direction (shapeRestr P g s).val i) : (arrowSlice P).Direction s.val i :=
  ⟨reindexDir P s.val j' d.val, (reindexDir_over P s.val j' d.val).trans d.property⟩

/-- The operations of the transcription. -/
def arrowData (P : SlicePFunctor.{0, 0, 0, 0} X Y) :
    PresheafPFunctorData.{0, 0, 0, 0, 0, 0} (Fin 2) (Fin 2) :=
  { arrowSlice P with
    directionRestr := directionRestr P
    shapeRestr := shapeRestr P
    reindex := reindex P }

/-- Direction restriction along an identity is the identity. -/
theorem directionRestr_id (P : SlicePFunctor.{0, 0, 0, 0} X Y) :
    (arrowData P).DirectionRestrId := by
  intro s i
  funext d
  obtain ⟨d, hd⟩ := d
  refine Subtype.ext ?_
  match d with
  | .inl _ => rfl
  | .inr _ =>
    change (1 : Fin 2) = i at hd
    subst hd
    rfl

/-- Direction restriction reverses composition. -/
theorem directionRestr_comp (P : SlicePFunctor.{0, 0, 0, 0} X Y) :
    (arrowData P).DirectionRestrComp := by
  intro s i i' i'' f g
  funext d
  obtain ⟨d, hd⟩ := d
  refine Subtype.ext ?_
  match d with
  | .inl _ => rfl
  | .inr _ =>
    change (1 : Fin 2) = i at hd
    subst hd
    match i', i'' with
    | 0, 0 => rfl
    | 1, 0 => rfl
    | 1, 1 => rfl
    | 0, 1 => exact absurd (leOfHom g) (by decide)

/-- Shape restriction along an identity is the identity. -/
theorem shapeRestr_id (P : SlicePFunctor.{0, 0, 0, 0} X Y) : (arrowData P).ShapeRestrId := by
  intro j
  funext s
  obtain ⟨s, hs⟩ := s
  refine Subtype.ext ?_
  match s with
  | .inl _ => rfl
  | .inr _ =>
    change (1 : Fin 2) = j at hs
    subst hs
    rfl

/-- Shape restriction reverses composition. -/
theorem shapeRestr_comp (P : SlicePFunctor.{0, 0, 0, 0} X Y) :
    (arrowData P).ShapeRestrComp := by
  intro j j' j'' g h
  funext s
  obtain ⟨s, hs⟩ := s
  refine Subtype.ext ?_
  match s with
  | .inl _ => rfl
  | .inr _ =>
    change (1 : Fin 2) = j at hs
    subst hs
    match j', j'' with
    | 0, 0 => rfl
    | 1, 0 => rfl
    | 1, 1 => rfl
    | 0, 1 => exact absurd (leOfHom h) (by decide)

/-- Reindexing commutes with direction restriction. -/
theorem reindex_naturality (P : SlicePFunctor.{0, 0, 0, 0} X Y) :
    (arrowData P).ReindexNaturality := by
  intro j j' g s i i' f
  funext d
  obtain ⟨d, hd⟩ := d
  refine Subtype.ext ?_
  match d with
  | .inl _ => rfl
  | .inr b =>
    change (1 : Fin 2) = i at hd
    subst hd
    match i' with
    | 1 => rfl
    | 0 => exact congrArg Sum.inl (fibR_reindexFib P s.val j' b)

/-- Reindexing along an identity is the identity. -/
theorem reindex_id (P : SlicePFunctor.{0, 0, 0, 0} X Y) :
    (arrowData P).ReindexId (shapeRestr_id P) := by
  intro j s i d
  obtain ⟨s, hs⟩ := s
  obtain ⟨d, hd⟩ := d
  match s with
  | .inl _ =>
    refine Subtype.ext ?_
    match d with
    | .inl _ => rfl
    | .inr e => exact PEmpty.elim e
  | .inr _ =>
    change (1 : Fin 2) = j at hs
    subst hs
    refine Subtype.ext ?_
    match d with
    | .inl _ => rfl
    | .inr _ => rfl

/-- Reindexing along a composite is the composite of the reindexings. -/
theorem reindex_comp (P : SlicePFunctor.{0, 0, 0, 0} X Y) :
    (arrowData P).ReindexComp (shapeRestr_comp P) := by
  intro j j' j'' g h s i d
  obtain ⟨s, hs⟩ := s
  obtain ⟨d, hd⟩ := d
  match s with
  | .inl _ =>
    refine Subtype.ext ?_
    match d with
    | .inl _ => rfl
    | .inr e => exact PEmpty.elim e
  | .inr _ =>
    change (1 : Fin 2) = j at hs
    subst hs
    refine Subtype.ext ?_
    match j', j'' with
    | 0, 0 =>
      match d with
      | .inl _ => rfl
      | .inr e => exact PEmpty.elim e
    | 1, 0 =>
      match d with
      | .inl _ => rfl
      | .inr e => exact PEmpty.elim e
    | 1, 1 =>
      match d with
      | .inl _ => rfl
      | .inr _ => rfl
    | 0, 1 => exact absurd (leOfHom h) (by decide)

/-- The transcription's operations satisfy the functor laws. -/
theorem arrowData_isFunctorial (P : SlicePFunctor.{0, 0, 0, 0} X Y) :
    (arrowData P).IsFunctorial where
  directionRestr_id := directionRestr_id P
  directionRestr_comp := directionRestr_comp P
  shapeRestr_id := shapeRestr_id P
  shapeRestr_comp := shapeRestr_comp P
  reindex_naturality := reindex_naturality P
  reindex_id := reindex_id P
  reindex_comp := reindex_comp P

/-- The presheaf polynomial endofunctor on the walking arrow transcribing a
slice polynomial functor {lit}`Type/X → Type/Y`. -/
def arrowPsh (P : SlicePFunctor.{0, 0, 0, 0} X Y) :
    PresheafPFunctor.{0, 0, 0, 0, 0, 0} (Fin 2) (Fin 2) :=
  { arrowData P with isFunctorial := arrowData_isFunctorial P }

/-! # The value -/

/-- Over the walking arrow, a direction assignment is natural exactly when it
satisfies the naturality equation along the one non-identity morphism
{name}`PresheafIRUniv.waHom`, given that direction restriction along identities
is the identity. -/
theorem isNatural_iff (F : PresheafDomPFunctorData.{0, 0, 0, 0} (Fin 2))
    (hid : F.DirectionRestrId) (Z : (Fin 2)ᵒᵖ ⥤ Type)
    (x : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj Z)) :
    F.IsNatural x ↔ ∀ d : F.Direction x.val.1 1,
      F.value x (F.directionRestr x.val.1 waHom d) = Z.map waHom.op (F.value x d) := by
  refine ⟨fun h d ↦ h waHom d, fun h i i' f d ↦ ?_⟩
  match i, i' with
  | 0, 0 =>
    rw [Subsingleton.elim f (𝟙 _), hid, op_id, Z.map_id]
    rfl
  | 1, 1 =>
    rw [Subsingleton.elim f (𝟙 _), hid, op_id, Z.map_id]
    rfl
  | 1, 0 =>
    rw [Subsingleton.elim f waHom]
    exact h d
  | 0, 1 => exact absurd (leOfHom f) (by decide)

variable (P : SlicePFunctor.{0, 0, 0, 0} X Y) (Z : (Fin 2)ᵒᵖ ⥤ Type)

/-- The pullback of the family {lit}`Z 1 → Z 0` along {lit}`f₀ : X → Z 0`: the
pairs of an {lit}`x` and an element of {lit}`Z 1` over {lit}`f₀ x`. -/
def pullbackAlong (f₀ : X → Z.obj ⟨0⟩) : Type :=
  Σ x : X, { z : Z.obj ⟨1⟩ // Z.map waHom.op z = f₀ x }

/-- The pullback as an object of {lit}`Type/X`. -/
def pullbackProj (f₀ : X → Z.obj ⟨0⟩) : pullbackAlong Z f₀ → X :=
  Sigma.fst

/-- The value of the transcription at {lit}`Z`, in dependent-type terms: level
{lit}`0` is {lit}`Y × (X → Z 0)`, and level {lit}`1` is the sum over
{lit}`f₀ : X → Z 0` of the slice functor's value at the pullback along
{lit}`f₀`. -/
abbrev Levels : Type :=
  (Y × (X → Z.obj ⟨0⟩)) ⊕ (Σ f₀ : X → Z.obj ⟨0⟩, P.toSliceDomPFunctor.Obj (pullbackProj Z f₀))

/-- From the transcription's value to {lit}`Levels`: the level-{lit}`0`
directions of an element assign it a base map {lit}`X → Z 0`, and the
level-{lit}`1` directions of a level-{lit}`1` element assign it elements of
{lit}`Z 1`, which its naturality places over the base map. -/
def toLevels (x : (arrowPsh P).obj Z) : Levels P Z :=
  match x with
  | ⟨⟨⟨.inl y, v⟩, hc⟩, _⟩ =>
    .inl (y, fun x₀ ↦ (arrowPsh P).value ⟨⟨.inl y, v⟩, hc⟩ (i := 0) ⟨.inl x₀, rfl⟩)
  | ⟨⟨⟨.inr a, v⟩, hc⟩, hn⟩ =>
    .inr ⟨fun x₀ ↦ (arrowPsh P).value ⟨⟨.inr a, v⟩, hc⟩ (i := 0) ⟨.inl x₀, rfl⟩,
      ⟨⟨a, fun b ↦ ⟨P.r ⟨a, b⟩, (arrowPsh P).value ⟨⟨.inr a, v⟩, hc⟩ (i := 1) ⟨.inr b, rfl⟩,
        (hn waHom ⟨.inr b, rfl⟩).symm⟩⟩, rfl⟩⟩

/-- From {lit}`Levels` to the transcription's value: the inverse assignment,
natural by the equation over the base map. -/
def ofLevels (o : Levels P Z) : (arrowPsh P).obj Z :=
  match o with
  | .inl (y, f₀) =>
    ⟨⟨⟨.inl y, fun d ↦ match d with
        | .inl x₀ => ⟨0, f₀ x₀⟩
        | .inr e => PEmpty.elim e⟩,
      funext fun d ↦ match d with
        | .inl _ => rfl
        | .inr e => PEmpty.elim e⟩,
      (isNatural_iff _ (directionRestr_id P) Z _).mpr fun d ↦ match d with
        | ⟨.inl _, hd⟩ => absurd hd Fin.zero_ne_one
        | ⟨.inr e, _⟩ => PEmpty.elim e⟩
  | .inr ⟨f₀, o⟩ =>
    ⟨⟨⟨.inr o.val.1, fun d ↦ match d with
        | .inl x₀ => ⟨0, f₀ x₀⟩
        | .inr b => ⟨1, (o.val.2 b).2.val⟩⟩,
      funext fun d ↦ match d with
        | .inl _ => rfl
        | .inr _ => rfl⟩,
      (isNatural_iff _ (directionRestr_id P) Z _).mpr fun d ↦ match d with
        | ⟨.inl _, hd⟩ => absurd hd Fin.zero_ne_one
        | ⟨.inr b, _⟩ => ((o.val.2 b).2.property.trans (congrArg f₀ (congrFun o.property b))).symm⟩

/-- A dependent pair reassembled from its components after a cast of the
second along an equation of the first is the original pair. -/
private theorem sigma_mk_cast {j i : Fin 2} (z : Z.obj ⟨j⟩) (e : j = i) :
    (⟨i, cast (congrArg (fun k : Fin 2 ↦ Z.obj ⟨k⟩) e) z⟩ : Σ k : Fin 2, Z.obj ⟨k⟩) = ⟨j, z⟩ := by
  subst e
  rfl

/-- The {lit}`Z`-value an element assigns to a direction, paired with the
direction's level, is the element's raw assignment. -/
theorem sigma_value (F : PresheafDomPFunctorData.{0, 0, 0, 0} (Fin 2))
    (x : F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj Z)) ⦃i : Fin 2⦄
    (b : F.Direction x.val.1 i) :
    (⟨i, F.value x b⟩ : Σ k : Fin 2, Z.obj ⟨k⟩) = x.val.2 b.val := by
  obtain ⟨⟨a, v⟩, hc⟩ := x
  obtain ⟨b, hb⟩ := b
  exact sigma_mk_cast Z (v b).2 (((F.compatible_iff _ a v).mp hc b).trans hb)

/-- An element of a pullback reassembled from its components along an equation
of its base point is the original element. -/
theorem pullbackAlong_ext {f₀ : X → Z.obj ⟨0⟩} (q : pullbackAlong Z f₀) (x : X)
    (h : q.1 = x) :
    (⟨x, q.2.val, by rw [← h]; exact q.2.property⟩ : pullbackAlong Z f₀) = q := by
  obtain ⟨_, _, _⟩ := q
  subst h
  rfl

/-- The transcription's value at {lit}`Z` is {lit}`Levels P Z`. -/
def objEquiv : (arrowPsh P).obj Z ≃ Levels P Z where
  toFun := toLevels P Z
  invFun := ofLevels P Z
  left_inv x :=
    match x with
    | ⟨⟨⟨.inl _, _⟩, _⟩, _⟩ =>
      Subtype.ext (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun d ↦ match d with
        | .inl _ => sigma_value Z _ _ _
        | .inr e => PEmpty.elim e))))
    | ⟨⟨⟨.inr _, _⟩, _⟩, _⟩ =>
      Subtype.ext (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun d ↦ match d with
        | .inl _ => sigma_value Z _ _ _
        | .inr _ => sigma_value Z _ _ _))))
  right_inv o :=
    match o with
    | .inl _ => rfl
    | .inr ⟨_, o⟩ =>
      congrArg Sum.inr (Sigma.ext rfl (heq_of_eq (Subtype.ext (Sigma.ext rfl (heq_of_eq
        (funext fun b ↦ pullbackAlong_ext Z (o.val.2 b) _ (congrFun o.property b)))))))

/-- Restricting a level-{lit}`1` element over {lit}`(y, f₀)` along {lit}`0 ⟶ 1`
gives the level-{lit}`0` element {lit}`(y, f₀)`, where {lit}`y` is the slice
functor's output index of the element. -/
theorem toLevels_objRestr (f₀ : X → Z.obj ⟨0⟩)
    (o : P.toSliceDomPFunctor.Obj (pullbackProj Z f₀)) :
    toLevels P Z ((arrowPsh P).objRestr waHom (ofLevels P Z (.inr ⟨f₀, o⟩)) rfl) =
      .inl (P.obj (pullbackProj Z f₀) o, f₀) :=
  rfl

/-! # The fibre over {lit}`X` -/

/-- The fibres of a walking-arrow presheaf built from an object of
{lit}`Type/X`: {lit}`X` at level {lit}`0`, the object at level {lit}`1`. -/
def arrowObj (A B : Type) : Fin 2 → Type
  | 0 => A
  | 1 => B

/-- The restriction maps of that presheaf: identities, and the structure map
along {lit}`0 ⟶ 1`. -/
def arrowMap {A B : Type} (p : B → A) :
    ∀ (i i' : Fin 2), (i' ⟶ i) → arrowObj A B i → arrowObj A B i'
  | 0, 0, _ => id
  | 1, 1, _ => id
  | 1, 0, _ => p
  | 0, 1, f => absurd (leOfHom f) (by decide)

/-- An object {lit}`p : E → X` of {lit}`Type/X` as a walking-arrow presheaf:
{lit}`X` at level {lit}`0`, {lit}`E` at level {lit}`1`, {lit}`p` the
restriction along {lit}`0 ⟶ 1`. This is the inclusion of the fibre
{lit}`Type/X` into {lit}`Fam(Type)`. -/
def ofSlice {E : Type} (p : E → X) : (Fin 2)ᵒᵖ ⥤ Type where
  obj o := arrowObj X E o.unop
  map f := ↾ arrowMap p _ _ f.unop
  map_id o :=
    match o with
    | ⟨0⟩ => rfl
    | ⟨1⟩ => rfl
  map_comp {o o' o''} f g :=
    match o, o', o'', f, g with
    | ⟨0⟩, ⟨0⟩, ⟨0⟩, _, _ => rfl
    | ⟨1⟩, ⟨1⟩, ⟨1⟩, _, _ => rfl
    | ⟨1⟩, ⟨0⟩, ⟨0⟩, _, _ => rfl
    | ⟨1⟩, ⟨1⟩, ⟨0⟩, _, _ => rfl
    | ⟨1⟩, ⟨0⟩, ⟨1⟩, _, g => absurd (leOfHom g.unop) (by decide)
    | ⟨0⟩, ⟨1⟩, _, f, _ => absurd (leOfHom f.unop) (by decide)
    | ⟨0⟩, ⟨0⟩, ⟨1⟩, _, g => absurd (leOfHom g.unop) (by decide)

/-- The components of a morphism over {lit}`X` as a natural transformation:
the identity at level {lit}`0`, the morphism at level {lit}`1`. -/
def arrowHomApp {E E' : Type} (h : E → E') : ∀ i : Fin 2, arrowObj X E i → arrowObj X E' i
  | 0 => id
  | 1 => h

/-- A morphism {lit}`h` over {lit}`X`, {lit}`p' ∘ h = p`, as a natural
transformation {lit}`ofSlice p ⟶ ofSlice p'`. -/
def ofSliceHom {E E' : Type} {p : E → X} {p' : E' → X} (h : E → E') (hh : p' ∘ h = p) :
    NatTrans (ofSlice p) (ofSlice p') where
  app o := ↾ arrowHomApp h o.unop
  naturality {o o'} f :=
    match o, o', f with
    | ⟨0⟩, ⟨0⟩, _ => rfl
    | ⟨1⟩, ⟨1⟩, _ => rfl
    | ⟨1⟩, ⟨0⟩, _ => hh.symm
    | ⟨0⟩, ⟨1⟩, f => absurd (leOfHom f.unop) (by decide)

/-- An element of {lit}`E` as an element of the pullback of {lit}`ofSlice p`
along the identity, over its own image. -/
def toPullback {E : Type} (p : E → X) (e : E) : pullbackAlong (ofSlice p) id :=
  ⟨p e, e, rfl⟩

/-- The pullback of {lit}`ofSlice p` along the identity is {lit}`p` itself, at
the level of the slice functor's values: the level-{lit}`1` fibre of the
transcription over {lit}`(y, id)` is the slice functor's value. -/
def pullbackIdEquiv {E : Type} (p : E → X) :
    P.toSliceDomPFunctor.Obj (pullbackProj (ofSlice p) id) ≃ P.toSliceDomPFunctor.Obj p where
  toFun := P.map (fun q ↦ q.2.val) (funext fun q ↦ q.2.property)
  invFun := P.map (toPullback p) rfl
  left_inv q :=
    Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun b ↦
      pullbackAlong_ext (ofSlice p) (q.val.2 b) _ (q.val.2 b).2.property.symm)))
  right_inv _ := Subtype.ext rfl

/-- The comparison map from the slice functor's value at {lit}`p` to the
transcription's value at {lit}`ofSlice p`: the level-{lit}`1` element over the
identity base map. -/
def cmp {E : Type} (p : E → X) (o : P.toSliceDomPFunctor.Obj p) :
    (arrowPsh P).obj (ofSlice p) :=
  ofLevels P (ofSlice p) (.inr ⟨id, (pullbackIdEquiv P p).symm o⟩)

/-- The comparison map's image, read in {lit}`Levels`: the identity base map
with the slice functor's value transported along {lit}`pullbackIdEquiv`. -/
theorem objEquiv_cmp {E : Type} (p : E → X) (o : P.toSliceDomPFunctor.Obj p) :
    objEquiv P (ofSlice p) (cmp P p o) = .inr ⟨id, (pullbackIdEquiv P p).symm o⟩ := by
  exact (objEquiv P (ofSlice p)).apply_symm_apply (.inr ⟨id, (pullbackIdEquiv P p).symm o⟩)

/-- The comparison map is natural in the object of {lit}`Type/X`. -/
theorem map_cmp {E E' : Type} {p : E → X} {p' : E' → X} (h : E → E') (hh : p' ∘ h = p)
    (o : P.toSliceDomPFunctor.Obj p) :
    (arrowPsh P).map (ofSliceHom h hh) (cmp P p o) = cmp P p' (P.map h hh o) :=
  Subtype.ext (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun d ↦ match d with
    | .inl _ => rfl
    | .inr _ => rfl))))

/-- The comparison map's image restricts along {lit}`0 ⟶ 1` to the
level-{lit}`0` element {lit}`(y, id)`, where {lit}`y` is the slice functor's
output index. -/
theorem toLevels_objRestr_cmp {E : Type} (p : E → X) (o : P.toSliceDomPFunctor.Obj p) :
    toLevels P (ofSlice p) ((arrowPsh P).objRestr waHom (cmp P p o) rfl) =
      .inl (P.obj p o, id) :=
  toLevels_objRestr P (ofSlice p) id _

end GebProto.LargeIR
