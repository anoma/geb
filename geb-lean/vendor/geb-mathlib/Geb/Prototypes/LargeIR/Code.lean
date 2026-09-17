/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.LargeIR.Basic
public import Geb.Mathlib.Data.PFunctor.IndRec.Basic

set_option doc.verso true

/-!
# Prototype: the transcription read back as a large inductive-recursive code

Throwaway exploration, not upstream-eligible content. Every declaration here
is {name}`Classical.choice`-free.

{name}`GebProto.LargeIR.objEquiv` computes the value of the transcription
{name}`GebProto.LargeIR.arrowPsh` of a slice polynomial functor
{lit}`P : Type/X → Type/Y` at a walking-arrow presheaf {lit}`Z` as a level
{lit}`0` of {lit}`Y × (X → Z 0)` and a level {lit}`1` over {lit}`(y, f₀)` of
{lit}`P` at the pullback along {lit}`f₀`. This module reads that computation
back as the interpretation of an inductive-recursive code on
{lit}`Fam(Type)`, the free coproduct completion of {lit}`Type`, in the
repository's code system {name}`IndRec.IR` at input and output index type
{lit}`Type`: the code {lit}`code P` is
{lit}`σ Y (fun y ↦ δ X (fun A ↦ ι (fibreValue P y A)))`, whose {lit}`σ`
contributes the {lit}`Y`, whose {lit}`δ` contributes the base map
{lit}`X → Z 0` as the assignment {lit}`g : X → U` of the {lit}`δ` rule, and
whose {lit}`ι` decodes to the slice functor's fibre at {lit}`y` applied to
the decoded family {lit}`T ∘ g`. The interpretation
{name}`IndRec.IR.interpObj` of {lit}`code P` at the family {lit}`(U, T)` of
{lit}`Z` — {lit}`U := Z 0` and {lit}`T u` the fibre of {lit}`Z 1 → Z 0` over
{lit}`u` — is isomorphic, as a walking-arrow presheaf, to the transcription's
value. That is {lit}`arrowPshCodeEquiv`, and it confirms the reading of the
transcription as a large-IR {lit}`δ` code rather than as the slice functor.

The comparison is stated between walking-arrow presheaves, a family being
turned into one by {name}`GebProto.LargeIR.ofSlice` of the projection of its
total space, and an isomorphism of walking-arrow presheaves is a pair of
equivalences commuting with the restriction map, {lit}`PshEquiv`. Two
choices are forced by what is available choice-free. A functor-category
isomorphism would name the functor category, which depends on
{name}`Classical.choice`, so the isomorphism is unbundled. And the
repository's {name}`CategoryTheory.FreeCoprodCompDisc` is the completion of
{lit}`Type` as a discrete category, whose morphisms compare decodings by
equality, so the agreement is stated at the level of objects: the morphism
action of large inductive-recursive definitions, which compares decodings
by functions {lit}`T u → T' (h u)` and is what the positivity of
\[GhaniNordvallForsbergMalatesta2015\] provides, is outside what that
completion expresses, and is not compared here.

## Main definitions

* {lit}`fibreValue` — the slice functor's fibre at an output index, applied
  to a family {lit}`X → Type`.
* {lit}`code` — the code {lit}`σ Y (fun y ↦ δ X (fun A ↦ ι (fibreValue P y A)))`.
* {lit}`famOfPsh` — the family {lit}`(U, T)` of a walking-arrow presheaf;
  {lit}`pshOfFam` — the walking-arrow presheaf of a family.
* {lit}`PshEquiv` — an isomorphism of walking-arrow presheaves, unbundled;
  {lit}`PshEquiv.trans` its composition.
* {lit}`levelsPsh` — {name}`GebProto.LargeIR.Levels` as a walking-arrow
  presheaf.
* {lit}`levelZeroEquiv`, {lit}`levelOneEquiv` — the level-{lit}`0` and
  level-{lit}`1` elements of the transcription's value as the two summands
  of {name}`GebProto.LargeIR.Levels`.

## Main statements

* {lit}`objPresheafEquiv` — the transcription's output presheaf is
  {lit}`levelsPsh`.
* {lit}`levelsCodeEquiv` — {lit}`levelsPsh` is the presheaf of the code's
  interpretation at the family of the input.
* {lit}`arrowPshCodeEquiv` — their composite: the transcription's output presheaf
  is the presheaf of the code's interpretation.

## References

* \[DybjerSetzer2003\]
* \[GhaniNordvallForsbergMalatesta2015\]

## Tags

prototype, presheaf, walking arrow, inductive-recursive, code, free coproduct
completion
-/

@[expose] public section

open CategoryTheory PresheafIRUniv IndRec

namespace GebProto.LargeIR

variable {X Y : Type} (P : SlicePFunctor.{0, 0, 0, 0} X Y)

/-! # The code -/

/-- The slice functor's fibre at the output index {lit}`y`, applied to a
family {lit}`A : X → Type`: a shape over {lit}`y` with an element of the
family at each direction's input index. -/
def fibreValue (y : Y) (A : X → Type) : Type :=
  Σ a : P.Shape y, ∀ b : P.B a.1, A (P.r ⟨a.1, b⟩)

/-- The code {lit}`σ Y (fun y ↦ δ X (fun A ↦ ι (fibreValue P y A)))`: a
constructor for each output index, whose recursive arguments are indexed by
{lit}`X` and whose decoding is the slice functor's fibre applied to the
decodings of those arguments. -/
def code : IR.{0, 0, 1, 1} Type Type :=
  IR.sigma Type Type Y fun y ↦ IR.delta Type Type X fun A ↦ IR.iota Type Type (fibreValue P y A)

/-! # Families and walking-arrow presheaves -/

/-- The family {lit}`(U, T)` of a walking-arrow presheaf: {lit}`U := Z 0` and
{lit}`T u` the fibre of the restriction {lit}`Z 1 → Z 0` over {lit}`u`. -/
def famOfPsh (Z : (Fin 2)ᵒᵖ ⥤ Type) : FreeCoprodCompDisc.{0, 1} Type :=
  ⟨Z.obj ⟨0⟩, fun u ↦ { z : Z.obj ⟨1⟩ // Z.map waHom.op z = u }⟩

/-- The walking-arrow presheaf of a family: the projection of its total space
as an object of {lit}`Type/U`. -/
def pshOfFam (F : FreeCoprodCompDisc.{0, 1} Type) : (Fin 2)ᵒᵖ ⥤ Type :=
  ofSlice (Sigma.fst : (Σ u : F.1, F.2 u) → F.1)

/-- An isomorphism of walking-arrow presheaves, unbundled: equivalences at
the two levels commuting with the restriction map. -/
structure PshEquiv (Z Z' : (Fin 2)ᵒᵖ ⥤ Type) where
  /-- The equivalence at level {lit}`0`. -/
  base : Z.obj ⟨0⟩ ≃ Z'.obj ⟨0⟩
  /-- The equivalence at level {lit}`1`. -/
  total : Z.obj ⟨1⟩ ≃ Z'.obj ⟨1⟩
  /-- The equivalences commute with the restriction along {lit}`0 ⟶ 1`. -/
  map_total : ∀ z, Z'.map waHom.op (total z) = base (Z.map waHom.op z)

/-- Composition of isomorphisms of walking-arrow presheaves. -/
def PshEquiv.trans {Z Z' Z'' : (Fin 2)ᵒᵖ ⥤ Type} (e : PshEquiv Z Z') (e' : PshEquiv Z' Z'') :
    PshEquiv Z Z'' where
  base := e.base.trans e'.base
  total := e.total.trans e'.total
  map_total z := (e'.map_total (e.total z)).trans (congrArg e'.base (e.map_total z))

/-! # The transcription's output presheaf as a family -/

variable (Z : (Fin 2)ᵒᵖ ⥤ Type)

/-- The level of a summand of {name}`GebProto.LargeIR.Levels`. -/
def levelOf : Levels P Z → Fin 2 :=
  Sum.elim (fun _ ↦ 0) (fun _ ↦ 1)

/-- The level of an element of the transcription's value is the level of its
image in {name}`GebProto.LargeIR.Levels`. -/
theorem q_shape_eq_levelOf (x : (arrowPsh P).obj Z) :
    (arrowPsh P).q x.shape = levelOf P Z (toLevels P Z x) :=
  match x with
  | ⟨⟨⟨.inl _, _⟩, _⟩, _⟩ => rfl
  | ⟨⟨⟨.inr _, _⟩, _⟩, _⟩ => rfl

/-- {name}`GebProto.LargeIR.toLevels` inverts {name}`GebProto.LargeIR.ofLevels`. -/
theorem toLevels_ofLevels (l : Levels P Z) : toLevels P Z (ofLevels P Z l) = l := by
  exact (objEquiv P Z).right_inv l

/-- {name}`GebProto.LargeIR.ofLevels` inverts {name}`GebProto.LargeIR.toLevels`. -/
theorem ofLevels_toLevels (x : (arrowPsh P).obj Z) : ofLevels P Z (toLevels P Z x) = x := by
  exact (objEquiv P Z).left_inv x

/-- The elements of the transcription's value over {lit}`j` are the summands
of {name}`GebProto.LargeIR.Levels` at level {lit}`j`. -/
def objLevelEquiv (j : Fin 2) :
    { x : (arrowPsh P).obj Z // (arrowPsh P).q x.shape = j } ≃
      { l : Levels P Z // levelOf P Z l = j } where
  toFun x := ⟨toLevels P Z x.1, (q_shape_eq_levelOf P Z x.1).symm.trans x.2⟩
  invFun l := ⟨ofLevels P Z l.1,
    (q_shape_eq_levelOf P Z _).trans
      ((congrArg (levelOf P Z) (toLevels_ofLevels P Z l.1)).trans l.2)⟩
  left_inv x := Subtype.ext (ofLevels_toLevels P Z x.1)
  right_inv l := Subtype.ext (toLevels_ofLevels P Z l.1)

/-- The elements of a sum at level {lit}`0` are its left summand. -/
def sumLeftEquiv {α β : Type} :
    { s : α ⊕ β // Sum.elim (fun _ ↦ 0) (fun _ ↦ 1) s = (0 : Fin 2) } ≃ α where
  toFun s :=
    match s with
    | ⟨.inl a, _⟩ => a
    | ⟨.inr _, h⟩ => absurd h Fin.zero_ne_one.symm
  invFun a := ⟨.inl a, rfl⟩
  left_inv s :=
    match s with
    | ⟨.inl _, _⟩ => rfl
    | ⟨.inr _, h⟩ => absurd h Fin.zero_ne_one.symm
  right_inv _ := rfl

/-- The elements of a sum at level {lit}`1` are its right summand. -/
def sumRightEquiv {α β : Type} :
    { s : α ⊕ β // Sum.elim (fun _ ↦ 0) (fun _ ↦ 1) s = (1 : Fin 2) } ≃ β where
  toFun s :=
    match s with
    | ⟨.inl _, h⟩ => absurd h Fin.zero_ne_one
    | ⟨.inr b, _⟩ => b
  invFun b := ⟨.inr b, rfl⟩
  left_inv s :=
    match s with
    | ⟨.inl _, h⟩ => absurd h Fin.zero_ne_one
    | ⟨.inr _, _⟩ => rfl
  right_inv _ := rfl

/-- The level-{lit}`0` elements of the transcription's value are
{lit}`Y × (X → Z 0)`. -/
def levelZeroEquiv :
    { x : (arrowPsh P).obj Z // (arrowPsh P).q x.shape = 0 } ≃ (Y × (X → Z.obj ⟨0⟩)) :=
  (objLevelEquiv P Z 0).trans sumLeftEquiv

/-- The level-{lit}`1` elements of the transcription's value are the sum over
the base maps of the slice functor's values at the pullbacks. -/
def levelOneEquiv :
    { x : (arrowPsh P).obj Z // (arrowPsh P).q x.shape = 1 } ≃
      (Σ f₀ : X → Z.obj ⟨0⟩, P.toSliceDomPFunctor.Obj (pullbackProj Z f₀)) :=
  (objLevelEquiv P Z 1).trans sumRightEquiv

/-- The level-{lit}`1` part of {name}`GebProto.LargeIR.Levels` regrouped over
the level-{lit}`0` part: over {lit}`(y, f₀)`, the slice functor's values at the
pullback along {lit}`f₀` whose output index is {lit}`y`. -/
def levelsFibre (yf : Y × (X → Z.obj ⟨0⟩)) : Type :=
  { o : P.toSliceDomPFunctor.Obj (pullbackProj Z yf.2) // P.obj (pullbackProj Z yf.2) o = yf.1 }

/-- An element of the regrouped level-{lit}`1` part reassembled from its
components along an equation of its output index is the original element. -/
theorem levelsFibre_ext {f₀ : X → Z.obj ⟨0⟩} {y : Y}
    (o : P.toSliceDomPFunctor.Obj (pullbackProj Z f₀)) (h : P.obj (pullbackProj Z f₀) o = y) :
    (⟨(P.obj (pullbackProj Z f₀) o, f₀), ⟨o, rfl⟩⟩ :
      Σ yf : Y × (X → Z.obj ⟨0⟩), levelsFibre P Z yf) = ⟨(y, f₀), ⟨o, h⟩⟩ := by
  subst h
  rfl

/-- Regrouping the level-{lit}`1` part over the level-{lit}`0` part. -/
def levelsFibreEquiv :
    (Σ f₀ : X → Z.obj ⟨0⟩, P.toSliceDomPFunctor.Obj (pullbackProj Z f₀)) ≃
      Σ yf : Y × (X → Z.obj ⟨0⟩), levelsFibre P Z yf where
  toFun s := ⟨(P.obj (pullbackProj Z s.1) s.2, s.1), ⟨s.2, rfl⟩⟩
  invFun s := ⟨s.1.2, s.2.1⟩
  left_inv _ := rfl
  right_inv s := levelsFibre_ext P Z s.2.1 s.2.2

/-- {name}`GebProto.LargeIR.Levels` as a walking-arrow presheaf: the
projection of the regrouped level-{lit}`1` part onto the level-{lit}`0`
part. -/
def levelsPsh : (Fin 2)ᵒᵖ ⥤ Type :=
  ofSlice (Sigma.fst : (Σ yf : Y × (X → Z.obj ⟨0⟩), levelsFibre P Z yf) → Y × (X → Z.obj ⟨0⟩))

/-- The transcription's output presheaf is {lit}`levelsPsh`: the two level
equivalences, commuting with the restriction along {lit}`0 ⟶ 1` by
{name}`GebProto.LargeIR.toLevels_objRestr`. -/
def objPresheafEquiv : PshEquiv ((arrowPsh P).objPresheaf Z) (levelsPsh P Z) where
  base := levelZeroEquiv P Z
  total := (levelOneEquiv P Z).trans (levelsFibreEquiv P Z)
  map_total t :=
    match t with
    | ⟨⟨⟨⟨.inl _, _⟩, _⟩, _⟩, ht⟩ => absurd ht Fin.zero_ne_one
    | ⟨⟨⟨⟨.inr _, _⟩, _⟩, _⟩, _⟩ => rfl

/-! # The code's interpretation as a family -/

/-- The level-{lit}`0` part of {name}`GebProto.LargeIR.Levels` is the index
type of the code's interpretation: a {lit}`σ` index, a {lit}`δ` assignment,
and the {lit}`ι` point. -/
def codeBaseEquiv :
    (Y × (X → Z.obj ⟨0⟩)) ≃ (IR.interpObj Type Type (code P) (famOfPsh Z)).1 where
  toFun yf := ⟨yf.1, yf.2, ⟨()⟩⟩
  invFun s := (s.1, s.2.1)
  left_inv _ := rfl
  right_inv s :=
    match s with
    | ⟨_, _, ⟨⟨⟩⟩⟩ => rfl

/-- Over {lit}`(y, f₀)`, the slice functor's value at the pullback along
{lit}`f₀` with output index {lit}`y` is the code's decoding: the fibre at
{lit}`y` applied to the decoded family {lit}`T ∘ f₀`. -/
def codeFibreEquiv (yf : Y × (X → Z.obj ⟨0⟩)) :
    levelsFibre P Z yf ≃ fibreValue P yf.1 ((famOfPsh Z).2 ∘ yf.2) where
  toFun o := ⟨⟨o.1.1.1, o.2⟩,
    fun b ↦ ⟨(o.1.1.2 b).2.1, (o.1.1.2 b).2.2.trans (congrArg yf.2 (congrFun o.1.2 b))⟩⟩
  invFun w := ⟨⟨⟨w.1.1, fun b ↦ ⟨P.r ⟨w.1.1, b⟩, w.2 b⟩⟩, rfl⟩, w.1.2⟩
  left_inv o :=
    Subtype.ext (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun b ↦
      pullbackAlong_ext Z (o.1.1.2 b) _ (congrFun o.1.2 b)))))
  right_inv _ := rfl

/-- {lit}`levelsPsh` is the presheaf of the code's interpretation at the
family of the input. -/
def levelsCodeEquiv :
    PshEquiv (levelsPsh P Z) (pshOfFam (IR.interpObj Type Type (code P) (famOfPsh Z))) where
  base := codeBaseEquiv P Z
  total :=
    { toFun := fun s ↦ ⟨codeBaseEquiv P Z s.1, codeFibreEquiv P Z s.1 s.2⟩
      invFun := fun s ↦
        match s with
        | ⟨⟨y, g, ⟨⟨⟩⟩⟩, w⟩ => ⟨(y, g), (codeFibreEquiv P Z (y, g)).symm w⟩
      left_inv := fun s ↦
        congrArg (Sigma.mk s.1) ((codeFibreEquiv P Z s.1).left_inv s.2)
      right_inv := fun s ↦
        match s with
        | ⟨⟨y, g, ⟨⟨⟩⟩⟩, w⟩ =>
          Sigma.ext rfl (heq_of_eq ((codeFibreEquiv P Z (y, g)).right_inv w)) }
  map_total _ := rfl

/-- The transcription's output presheaf at {lit}`Z` is the presheaf of the
interpretation of {lit}`code P` at the family of {lit}`Z`: the transcription
of a slice polynomial functor is the large inductive-recursive code
{lit}`σ Y (fun y ↦ δ X (fun A ↦ ι (fibreValue P y A)))`. -/
def arrowPshCodeEquiv :
    PshEquiv ((arrowPsh P).objPresheaf Z)
      (pshOfFam (IR.interpObj Type Type (code P) (famOfPsh Z))) :=
  (objPresheafEquiv P Z).trans (levelsCodeEquiv P Z)

end GebProto.LargeIR
