/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Mathlib.Logic.Equiv.Basic

/-!
# Sigma-type and sum-type equivalence combinators

Extensions of `Mathlib.Logic.Equiv.Basic`: an eliminator for sections
of sigma-type projections, choice-free congruence and grouping
equivalences on sigma types, and an equivalence presenting a function
into a sum type as a classifier together with an assignment on the
unresolved elements.

## Main definitions

* `sigmaFstSectionElim` — eliminate a function into a sigma type along
  a proof that it is a section of the first projection, producing a
  dependent function.
* `sigmaCongrRight'` — the dependent congruence of a sigma type in its
  second component, choice-free (unlike `Equiv.sigmaCongrRight`), with
  the two families at independent universes.
* `sigmaCompEquivSigmaFiber` — group a sigma over a composite family by
  the fibers of the inner function.
* `arrowSumEquivSigma` — a function into a sum type is a classifier
  into `X ⊕ PUnit` together with an assignment on the classifier's
  unresolved (right-classified) elements.

## Main statements

* `sigmaFstSectionElim_eq` — `sigmaFstSectionElim` computes the
  inverse direction of `Equiv.piEquivSubtypeSigma`.

## Tags

sigma, section, dependent function, equiv, sum type, classifier
-/

@[expose] public section

universe u v

/-- Eliminate a function into a sigma type along a proof that it is a
section of the first projection, producing a dependent function (the
inverse direction of mathlib's `Equiv.piEquivSubtypeSigma`
correspondence). -/
def sigmaFstSectionElim {X : Type u} {W : X → Type v}
    (g : (t : X) → Σ e, W e) (sect : ∀ t, (g t).1 = t) (t : X) : W t :=
  Eq.ndrec (g t).2 (sect t)

/-- `sigmaFstSectionElim` computes the inverse direction of
`Equiv.piEquivSubtypeSigma`. -/
theorem sigmaFstSectionElim_eq {X : Type u} {W : X → Type v}
    (g : (t : X) → Σ e, W e) (sect : ∀ t, (g t).1 = t) :
    sigmaFstSectionElim g sect =
      (Equiv.piEquivSubtypeSigma X W).symm ⟨g, sect⟩ := by
  funext t
  simp only [Equiv.piEquivSubtypeSigma, Equiv.coe_fn_symm_mk]
  exact eq_of_heq ((eqRec_heq (sect t) (g t).2).trans (cast_heq _ _).symm)

/-- The dependent congruence of a sigma type in its second
component, choice-free (unlike `Equiv.sigmaCongrRight`). The two
families are at independent universes, so `coprodIso` can relate
objects at distinct index universes. -/
def sigmaCongrRight'.{t₁, t₂} {α : Type u} {β₁ : α → Type t₁}
    {β₂ : α → Type t₂} (F : (a : α) → β₁ a ≃ β₂ a) :
    (Σ a, β₁ a) ≃ Σ a, β₂ a where
  toFun p := ⟨p.1, F p.1 p.2⟩
  invFun p := ⟨p.1, (F p.1).symm p.2⟩
  left_inv p := congrArg (Sigma.mk p.1) ((F p.1).left_inv p.2)
  right_inv p := congrArg (Sigma.mk p.1) ((F p.1).right_inv p.2)

/-- Group a sigma over a composite family by the fibers of the
inner function. -/
def sigmaCompEquivSigmaFiber.{w} {X : Type u} {B : Type v}
    (f : X → B) (N : B → Type w) :
    (Σ x, N (f x)) ≃ Σ b, Σ _ : {x // f x = b}, N b where
  toFun p := ⟨f p.1, ⟨p.1, rfl⟩, p.2⟩
  invFun q :=
    match q with
    | ⟨_, ⟨x, rfl⟩, n⟩ => ⟨x, n⟩
  left_inv _ := rfl
  right_inv q :=
    match q with
    | ⟨_, ⟨_, rfl⟩, _⟩ => rfl

/-- The type of classifiers of `B` over `X`: functions
`B → X ⊕ PUnit` marking each element of `B` as resolved (carrying a
left `X`-value) or unresolved (the right `PUnit` marker). -/
abbrev ArrowSumClassifier.{uB, uX, p} (B : Type uB) (X : Type uX) :=
  B → X ⊕ PUnit.{p + 1}

/-- The unresolved subtype of a classifier `c`: the elements of `B`
that `c` marks unresolved (maps to the right `PUnit` marker). -/
abbrev ArrowSumUnresolved.{uB, uX, p} {B : Type uB} {X : Type uX}
    (c : ArrowSumClassifier.{uB, uX, p} B X) :=
  {b : B // c b = Sum.inr PUnit.unit}

/-- Reassemble a function into a sum from a classifier and an
assignment on the unresolved subtype. -/
def arrowSumMerge.{w, p} {B : Type u} {X : Type v}
    {Y : Type w} (c : ArrowSumClassifier.{u, v, p} B X)
    (j : ArrowSumUnresolved c → Y) : B → X ⊕ Y :=
  fun b ↦
    Sum.casesOn (motive := fun s ↦ c b = s → X ⊕ Y) (c b)
      (fun x _ ↦ Sum.inl x) (fun _ h ↦ Sum.inr (j ⟨b, h⟩)) rfl

/-- Classify a function into a sum: keep left values, mark right
values. -/
def arrowSumClassify.{w, p} {B : Type u} {X : Type v}
    {Y : Type w} (g : B → X ⊕ Y) : ArrowSumClassifier.{u, v, p} B X :=
  Sum.map _root_.id (fun _ ↦ PUnit.unit) ∘ g

/-- Recover the right values of a function into a sum on the
subtype its classifier marks. -/
def arrowSumResolve.{w, p} {B : Type u} {X : Type v}
    {Y : Type w} (g : B → X ⊕ Y)
    (bp : ArrowSumUnresolved (arrowSumClassify.{u, v, w, p} g)) :
    Y :=
  Sum.casesOn
    (motive := fun s ↦
      Sum.map _root_.id (fun _ ↦ PUnit.unit) s = Sum.inr PUnit.unit → Y)
    (g bp.1) (fun _ h ↦ nomatch h) (fun y _ ↦ y) bp.2

/-- The value of `arrowSumMerge c j b` as the `Sum.casesOn` of any
`s` equal to `c b`, generalizing the otherwise-dependent scrutinee. -/
theorem arrowSumMerge_eq.{w, p} {B : Type u} {X : Type v} {Y : Type w}
    (c : ArrowSumClassifier.{u, v, p} B X)
    (j : ArrowSumUnresolved c → Y) (b : B)
    (s : X ⊕ PUnit.{p + 1}) (h : c b = s) :
    arrowSumMerge c j b =
      Sum.casesOn (motive := fun s ↦ c b = s → X ⊕ Y) s
        (fun x _ ↦ Sum.inl x) (fun _ h ↦ Sum.inr (j ⟨b, h⟩)) h :=
  match s, h with
  | _, rfl => rfl

/-- The value of `arrowSumResolve g ⟨b, hc⟩` as the `Sum.casesOn` of
any `s` equal to `g b`, generalizing the otherwise-dependent
scrutinee. -/
theorem arrowSumResolve_eq.{w, p} {B : Type u} {X : Type v} {Y : Type w}
    (g : B → X ⊕ Y) (b : B)
    (hc : arrowSumClassify.{u, v, w, p} g b = Sum.inr PUnit.unit)
    (s : X ⊕ Y) (h : g b = s) :
    arrowSumResolve g ⟨b, hc⟩ =
      Sum.casesOn (motive := fun s ↦
        Sum.map _root_.id (fun _ ↦ PUnit.unit) s = Sum.inr PUnit.unit → Y)
        s (fun _ h ↦ nomatch h) (fun y _ ↦ y) (h ▸ hc) :=
  match s, h with
  | _, rfl => rfl

/-- Merging a classified function on the unresolved subtype recovers
the original function pointwise. -/
theorem arrowSumMerge_classify.{w, p} {B : Type u}
    {X : Type v} {Y : Type w} (g : B → X ⊕ Y) (b : B) :
    arrowSumMerge (arrowSumClassify.{u, v, w, p} g)
      (arrowSumResolve g) b = g b :=
  Sum.casesOn (motive := fun t ↦ g b = t →
      (arrowSumMerge (arrowSumClassify.{u, v, w, p} g) (arrowSumResolve g) b = t))
    (g b)
    (fun x h ↦
      arrowSumMerge_eq (arrowSumClassify g) (arrowSumResolve g) b (Sum.inl x)
        (congrArg (Sum.map _root_.id (fun _ ↦ PUnit.unit)) h))
    (fun y h ↦
      (arrowSumMerge_eq (arrowSumClassify g) (arrowSumResolve g) b
          (Sum.inr PUnit.unit)
          (congrArg (Sum.map _root_.id (fun _ ↦ PUnit.unit)) h)).trans
        (congrArg Sum.inr
          (arrowSumResolve_eq g b
            (congrArg (Sum.map _root_.id (fun _ ↦ PUnit.unit)) h) (Sum.inr y) h)))
    rfl

/-- Classifying a merged function recovers the classifier
pointwise. -/
theorem arrowSumClassify_merge.{w, p} {B : Type u}
    {X : Type v} {Y : Type w} (c : ArrowSumClassifier.{u, v, p} B X)
    (j : ArrowSumUnresolved c → Y) (b : B) :
    arrowSumClassify (arrowSumMerge.{u, v, w, p} c j) b = c b :=
  Sum.casesOn (motive := fun t ↦ c b = t →
      (arrowSumClassify (arrowSumMerge.{u, v, w, p} c j) b = t))
    (c b)
    (fun x h ↦
      congrArg (Sum.map _root_.id (fun _ ↦ PUnit.unit))
        (arrowSumMerge_eq c j b (Sum.inl x) h))
    (fun _ h ↦
      congrArg (Sum.map _root_.id (fun _ ↦ PUnit.unit))
        (arrowSumMerge_eq c j b (Sum.inr PUnit.unit) h))
    rfl

/-- Motive eliminating the classifier equality `c = c'` in the
`right_inv` of `arrowSumEquivSigma`: transported pointwise agreement
of the second components yields equality of the sigma pairs. -/
def ArrowSumEta.{w, p} {B : Type u} {X : Type v} {Y : Type w}
    (c : ArrowSumClassifier.{u, v, p} B X) (j : ArrowSumUnresolved c → Y)
    (c' : ArrowSumClassifier.{u, v, p} B X) (eq1 : c = c') : Prop :=
  ∀ j' : {b : B // c' b = Sum.inr PUnit.unit} → Y,
    (∀ bp : {b : B // c' b = Sum.inr PUnit.unit},
      j ⟨bp.1, (congrFun eq1 bp.1).trans bp.2⟩ = j' bp) →
    (⟨c, j⟩ : Σ c : B → X ⊕ PUnit.{p + 1},
        {b : B // c b = Sum.inr PUnit.unit} → Y) = ⟨c', j'⟩

/-- The base case of `ArrowSumEta` at the reflexive classifier
equality: pointwise agreement of the second components is their
equality, so the sigma pairs coincide. -/
theorem arrowSumEta_refl.{w, p} {B : Type u} {X : Type v} {Y : Type w}
    (c : ArrowSumClassifier.{u, v, p} B X)
    (j : ArrowSumUnresolved c → Y) :
    ArrowSumEta.{u, v, w, p} c j c rfl :=
  fun _ h ↦ congrArg (Sigma.mk c) (funext h)

/-- A function into a sum is a classifier together with an
assignment on the unresolved subtype. -/
def arrowSumEquivSigma.{w, p} (B : Type u) (X : Type v)
    (Y : Type w) :
    (B → X ⊕ Y) ≃
      Σ c : ArrowSumClassifier.{u, v, p} B X,
        (ArrowSumUnresolved c → Y) where
  toFun g := ⟨arrowSumClassify g, arrowSumResolve g⟩
  invFun q := arrowSumMerge q.1 q.2
  left_inv g := funext (fun b ↦ arrowSumMerge_classify g b)
  right_inv q :=
    Eq.rec (motive := ArrowSumEta.{u, v, w, p}
        (arrowSumClassify (arrowSumMerge q.1 q.2))
        (arrowSumResolve (arrowSumMerge q.1 q.2)))
      (arrowSumEta_refl _ _)
      (funext (fun b ↦ arrowSumClassify_merge q.1 q.2 b))
      q.2
      (fun bp ↦
        arrowSumResolve_eq (arrowSumMerge q.1 q.2) bp.1
          ((congrFun (funext (fun b ↦ arrowSumClassify_merge q.1 q.2 b)) bp.1).trans bp.2)
          (Sum.inr (q.2 bp))
          (arrowSumMerge_eq q.1 q.2 bp.1 (Sum.inr PUnit.unit) bp.2))
