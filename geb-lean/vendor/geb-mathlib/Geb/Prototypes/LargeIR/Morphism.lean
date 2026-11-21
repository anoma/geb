/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.LargeIR.Code

set_option doc.verso true

/-!
# Prototype: the transcription and the code agree on morphisms

Throwaway exploration, not upstream-eligible content. Every declaration here
is {name}`Classical.choice`-free.

{name}`GebProto.LargeIR.arrowPshCodeEquiv` identifies the output presheaf of
the transcription {name}`GebProto.LargeIR.arrowPsh` of a slice polynomial
functor {lit}`P` at a walking-arrow presheaf {lit}`Z` with the presheaf of
the interpretation of the code {name}`GebProto.LargeIR.code` at the family
of {lit}`Z`. This module extends the agreement to morphisms. The morphisms of
{lit}`Fam(Type)` proper, {lit}`FamHom`, are a map of index types with a map
of decodings over it, the morphisms of the Grothendieck construction of
{lit}`U ↦ (U → Type)`, in contrast to those of
{name}`CategoryTheory.FreeCoprodCompDisc`, which compare decodings by
equality. On them the code acts by {lit}`codeMap`: the {lit}`σ` index and
the {lit}`ι` point are fixed, the {lit}`δ` assignment is postcomposed with
the map of index types, and the decoding is carried along by the
functoriality {lit}`fibreValueMap` of the slice functor's fibre in the
family, which is the positivity of the code's continuation in the sense of
\[GhaniNordvallForsbergMalatesta2015\]. The action is functorial,
{lit}`codeMap_id` and {lit}`codeMap_comp`.

A morphism of walking-arrow presheaves is a morphism of families,
{lit}`famHomOfNatTrans`, and conversely, {lit}`natTransOfFamHom`, through
the presheaf morphism {lit}`arrowHom` of a commuting square over a base
change. The naturality statements {lit}`base_map` and {lit}`total_map` say
that {name}`GebProto.LargeIR.arrowPshCodeEquiv` commutes with the
transcription's action {name}`PresheafPFunctor.mapPresheaf` on one side and
{lit}`codeMap` on the other: the isomorphism is natural in the input
presheaf, so the transcription and the positive action of the code are the
same functor on {lit}`Fam(Type)` up to it. Both are proved on the inverse
equivalences, {lit}`base_map_symm` and {lit}`total_map_symm`, where the
two sides agree by unfolding.

## Main definitions

* {lit}`FamHom` — the morphisms of {lit}`Fam(Type)` proper, with
  {lit}`FamHom.id`, {lit}`FamHom.comp` and the map of total spaces
  {lit}`FamHom.total`.
* {lit}`fibreValueMap` — the functoriality of the slice functor's fibre in
  the family.
* {lit}`codeMap` — the action of the code's interpretation on a morphism of
  families.
* {lit}`arrowHom` — the morphism of walking-arrow presheaves of a commuting
  square over a base change.
* {lit}`famHomOfNatTrans`, {lit}`natTransOfFamHom` — the two directions
  between morphisms of walking-arrow presheaves and of families.

## Main statements

* {lit}`codeMap_id`, {lit}`codeMap_comp` — the action is functorial.
* {lit}`base_map`, {lit}`total_map` — the isomorphism of
  {name}`GebProto.LargeIR.arrowPshCodeEquiv` is natural in the input
  presheaf, at each of the two levels.

## References

* \[GhaniNordvallForsbergMalatesta2015\]

## Tags

prototype, presheaf, walking arrow, inductive-recursive, code, positive,
naturality
-/

@[expose] public section

open CategoryTheory PresheafIRUniv IndRec

namespace GebProto.LargeIR

/-! # Morphisms of families -/

/-- A morphism of families with {lit}`Type`-valued decodings: a map of index
types with a map of decodings over it. -/
def FamHom (F G : FreeCoprodCompDisc.{0, 1} Type) : Type :=
  Σ h : F.1 → G.1, ∀ u, F.2 u → G.2 (h u)

/-- The identity morphism of families. -/
def FamHom.id (F : FreeCoprodCompDisc.{0, 1} Type) : FamHom F F :=
  ⟨_root_.id, fun _ ↦ _root_.id⟩

/-- Composition of morphisms of families. -/
def FamHom.comp {F G H : FreeCoprodCompDisc.{0, 1} Type} (φ : FamHom F G) (ψ : FamHom G H) :
    FamHom F H :=
  ⟨ψ.1 ∘ φ.1, fun u z ↦ ψ.2 (φ.1 u) (φ.2 u z)⟩

/-- The map of total spaces of a morphism of families. -/
def FamHom.total {F G : FreeCoprodCompDisc.{0, 1} Type} (φ : FamHom F G) :
    (Σ u : F.1, F.2 u) → Σ u : G.1, G.2 u :=
  fun p ↦ ⟨φ.1 p.1, φ.2 p.1 p.2⟩

variable {X Y : Type} (P : SlicePFunctor.{0, 0, 0, 0} X Y)

/-! # The action of the code on morphisms -/

/-- The slice functor's fibre is functorial in the family: a map of families
over {lit}`X` is applied at each direction. This is the positivity of the
code's continuation. -/
def fibreValueMap (y : Y) {A A' : X → Type} (φ : ∀ x, A x → A' x) :
    fibreValue P y A → fibreValue P y A' :=
  fun w ↦ ⟨w.1, fun b ↦ φ _ (w.2 b)⟩

/-- The action of the code's interpretation on a morphism of families: the
{lit}`σ` index and the {lit}`ι` point are fixed, the {lit}`δ` assignment is
postcomposed with the map of index types, and the decoding is carried along
by {lit}`fibreValueMap` at the map of decodings along the assignment. -/
def codeMap {F G : FreeCoprodCompDisc.{0, 1} Type} (φ : FamHom F G) :
    FamHom (IR.interpObj Type Type (code P) F) (IR.interpObj Type Type (code P) G) :=
  ⟨fun s ↦ ⟨s.1, φ.1 ∘ s.2.1, s.2.2⟩, fun s ↦ fibreValueMap P s.1 fun x ↦ φ.2 (s.2.1 x)⟩

/-- The action fixes identities. -/
theorem codeMap_id (F : FreeCoprodCompDisc.{0, 1} Type) :
    codeMap P (FamHom.id F) = FamHom.id _ :=
  rfl

/-- The action preserves composition. -/
theorem codeMap_comp {F G H : FreeCoprodCompDisc.{0, 1} Type} (φ : FamHom F G) (ψ : FamHom G H) :
    codeMap P (φ.comp ψ) = (codeMap P φ).comp (codeMap P ψ) :=
  rfl

/-! # Morphisms of walking-arrow presheaves and of families -/

/-- The components of a commuting square over a base change, as a natural
transformation: the base map at level {lit}`0`, the total map at level
{lit}`1`. -/
def squareApp {A A' B B' : Type} (h₀ : A → A') (h₁ : B → B') :
    ∀ i : Fin 2, arrowObj A B i → arrowObj A' B' i
  | 0 => h₀
  | 1 => h₁

/-- A commuting square {lit}`p' ∘ h₁ = h₀ ∘ p` over a base change
{lit}`h₀ : A → A'` as a morphism {lit}`ofSlice p ⟶ ofSlice p'` of walking-arrow
presheaves. {name}`GebProto.LargeIR.ofSliceHom` is the case of an identity
base map. -/
def arrowHom {A A' B B' : Type} {p : B → A} {p' : B' → A'} (h₀ : A → A') (h₁ : B → B')
    (w : p' ∘ h₁ = h₀ ∘ p) : NatTrans (ofSlice p) (ofSlice p') where
  app o := ↾ squareApp h₀ h₁ o.unop
  naturality {o o'} f :=
    match o, o', f with
    | ⟨0⟩, ⟨0⟩, _ => rfl
    | ⟨1⟩, ⟨1⟩, _ => rfl
    | ⟨1⟩, ⟨0⟩, _ => w.symm
    | ⟨0⟩, ⟨1⟩, f => absurd (leOfHom f.unop) (by decide)

/-- A morphism of families as a morphism of the walking-arrow presheaves of
the families: the map of total spaces over the map of index types. -/
def natTransOfFamHom {F G : FreeCoprodCompDisc.{0, 1} Type} (φ : FamHom F G) :
    NatTrans (pshOfFam F) (pshOfFam G) :=
  arrowHom φ.1 φ.total rfl

/-- A morphism of walking-arrow presheaves as a morphism of their families:
the level-{lit}`0` component on index types, and the level-{lit}`1` component
on the fibres of the restriction, which it preserves by naturality. -/
def famHomOfNatTrans {Z Z' : (Fin 2)ᵒᵖ ⥤ Type} (α : NatTrans Z Z') :
    FamHom (famOfPsh Z) (famOfPsh Z') :=
  ⟨α.app ⟨0⟩, fun _ z ↦ ⟨α.app ⟨1⟩ z.val,
    ((congrArg (fun k : Z.obj ⟨1⟩ ⟶ Z'.obj ⟨0⟩ ↦ k z.val) (α.naturality waHom.op)).symm.trans
      (congrArg (α.app ⟨0⟩) z.property))⟩⟩

/-! # Naturality of the isomorphism -/

variable {Z Z' : (Fin 2)ᵒᵖ ⥤ Type} (α : NatTrans Z Z')

/-- On the inverse equivalences at level {lit}`0`, the transcription's action
and the code's action agree by unfolding. -/
theorem base_map_symm (s : (pshOfFam (IR.interpObj Type Type (code P) (famOfPsh Z))).obj ⟨0⟩) :
    ((arrowPsh P).mapPresheaf α).app ⟨0⟩ ((arrowPshCodeEquiv P Z).base.symm s) =
      (arrowPshCodeEquiv P Z').base.symm
        ((natTransOfFamHom (codeMap P (famHomOfNatTrans α))).app ⟨0⟩ s) := by
  refine Subtype.ext (Subtype.ext (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun d ↦ ?_)))))
  cases d with
  | inl _ => rfl
  | inr e => exact PEmpty.elim e

/-- On the inverse equivalences at level {lit}`1`, the transcription's action
and the code's action agree by unfolding. -/
theorem total_map_symm (s : (pshOfFam (IR.interpObj Type Type (code P) (famOfPsh Z))).obj ⟨1⟩) :
    ((arrowPsh P).mapPresheaf α).app ⟨1⟩ ((arrowPshCodeEquiv P Z).total.symm s) =
      (arrowPshCodeEquiv P Z').total.symm
        ((natTransOfFamHom (codeMap P (famHomOfNatTrans α))).app ⟨1⟩ s) := by
  obtain ⟨⟨_, _, ⟨⟨⟩⟩⟩, _⟩ := s
  refine Subtype.ext (Subtype.ext (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun d ↦ ?_)))))
  cases d <;> rfl

/-- The isomorphism is natural in the input presheaf at level {lit}`0`: it
commutes with the transcription's action on one side and the code's action on
the other. -/
theorem base_map (x : ((arrowPsh P).objPresheaf Z).obj ⟨0⟩) :
    (arrowPshCodeEquiv P Z').base (((arrowPsh P).mapPresheaf α).app ⟨0⟩ x) =
      (natTransOfFamHom (codeMap P (famHomOfNatTrans α))).app ⟨0⟩
        ((arrowPshCodeEquiv P Z).base x) := by
  have h := base_map_symm P α ((arrowPshCodeEquiv P Z).base x)
  rw [(arrowPshCodeEquiv P Z).base.symm_apply_apply] at h
  rw [h, (arrowPshCodeEquiv P Z').base.apply_symm_apply]

/-- The isomorphism is natural in the input presheaf at level {lit}`1`. -/
theorem total_map (t : ((arrowPsh P).objPresheaf Z).obj ⟨1⟩) :
    (arrowPshCodeEquiv P Z').total (((arrowPsh P).mapPresheaf α).app ⟨1⟩ t) =
      (natTransOfFamHom (codeMap P (famHomOfNatTrans α))).app ⟨1⟩
        ((arrowPshCodeEquiv P Z).total t) := by
  have h := total_map_symm P α ((arrowPshCodeEquiv P Z).total t)
  rw [(arrowPshCodeEquiv P Z).total.symm_apply_apply] at h
  rw [h, (arrowPshCodeEquiv P Z').total.apply_symm_apply]

end GebProto.LargeIR
