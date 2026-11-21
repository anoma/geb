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
# Prototype: base-cartesian presheaf polynomial endofunctors on the walking arrow are codes

Throwaway exploration, not upstream-eligible content. Every declaration here
is {name}`Classical.choice`-free.

{name}`GebProto.LargeIR.arrowPshCodeEquiv` reads one presheaf polynomial
endofunctor on the walking arrow, the transcription of a slice polynomial
functor, as a large inductive-recursive code on {lit}`Fam(Type)`. This module
states the general case. A presheaf polynomial endofunctor {lit}`F` on the
walking arrow has shapes at two levels, each shape {lit}`a` having directions
{lit}`D₀ a` at level {lit}`0` and {lit}`D₁ a` at level {lit}`1` with a
restriction {lit}`ρ : D₁ a → D₀ a`, and a level-{lit}`1` shape {lit}`a₁`
restricting to a level-{lit}`0` shape with reindexings of directions at each
level. Its value at a walking-arrow presheaf {lit}`Z`, read as the family
{lit}`(U, T)`, is computed by {lit}`elemEquiv`: an element is a shape
{lit}`a`, a base assignment {lit}`g : D₀ a → U`, and an assignment
{lit}`w : Π d : D₁ a, T (g (ρ d))`.

The reading as a code needs one condition, {lit}`BaseCartesian`: for every
level-{lit}`1` shape, the reindexing of level-{lit}`0` directions from its
restriction is a bijection. Then the code is

{lit}`σ (Shape 0) (fun a ↦ δ (D₀ a) (fun A ↦ σ (Π d : D₁ a, A (ρ d)) (fun w ↦ ι (fibre a A w))))`,

{lit}`genCode`, whose {lit}`σ` indices are the level-{lit}`0` shapes and the
level-{lit}`1` assignments of a level-{lit}`0` shape, whose {lit}`δ` arities
are its level-{lit}`0` directions, and whose {lit}`ι` decodes to the
level-{lit}`1` shapes over it with the assignments restricting to {lit}`w`,
{lit}`genFibre`. {lit}`genCodeEquiv` is the isomorphism of the functor's
output presheaf with the presheaf of the code's interpretation at the family
of the input, and {lit}`arrowPshBaseCartesian` exhibits the transcription of
a slice polynomial functor as an instance.

The condition is not an artefact. Without it a level-{lit}`1` shape carries
a level-{lit}`0` direction not reached from its restriction, whose value
under a base assignment is an element of {lit}`U` unconstrained by the
level-{lit}`0` element below, so the fibre of the output family over that
element has the index type {lit}`U` itself as a factor. The decoding of a
code mentions {lit}`U` only through {lit}`T ∘ g`, and the interpretation of
every code preserves the cartesian morphisms of families, those whose
decoding maps are bijections, while a functor with such a factor does not;
that argument is not formalized here.

## Main definitions

* {lit}`Elem`, {lit}`elemEquiv` — the value of a presheaf polynomial
  endofunctor on the walking arrow in dependent-type terms.
* {lit}`ElemAt`, {lit}`objLevel` — the elements over a level, and
  {lit}`restrElem` the restriction from level {lit}`1` to level {lit}`0` on
  them.
* {lit}`BaseCartesian` — the condition on reindexing at level {lit}`0`.
* {lit}`genFibre`, {lit}`genCode` — the fibre type and the code.
* {lit}`arrowPshBaseCartesian` — the transcription of a slice polynomial
  functor is base-cartesian.

## Main statements

* {lit}`objLevel_objRestr` — the restriction of the output presheaf is
  {lit}`restrElem` on elements.
* {lit}`genCodeEquiv` — the output presheaf of a base-cartesian functor is
  the presheaf of the code's interpretation.

## References

* \[GhaniNordvallForsbergMalatesta2015\]
* \[Weber2007\]

## Tags

prototype, presheaf, walking arrow, parametric right adjoint,
inductive-recursive, code, cartesian
-/

@[expose] public section

open CategoryTheory PresheafIRUniv IndRec

namespace GebProto.LargeIR

variable (F : PresheafPFunctor.{0, 0, 0, 0, 0, 0} (Fin 2) (Fin 2))

/-! # The value in dependent-type terms -/

/-- The restriction of a shape's directions from level {lit}`1` to level
{lit}`0`. -/
abbrev dirRestr (a : F.A) : F.Direction a 1 → F.Direction a 0 :=
  F.directionRestr a waHom

/-- The restriction of a level-{lit}`1` shape to level {lit}`0`. -/
abbrev restrShape₁ (a₁ : F.Shape 1) : F.Shape 0 :=
  F.shapeRestr waHom a₁

/-- The reindexing of level-{lit}`0` directions from the restricted shape. -/
abbrev reindex₀ (a₁ : F.Shape 1) :
    F.Direction (restrShape₁ F a₁).val 0 → F.Direction a₁.val 0 :=
  F.reindex waHom a₁ (i := 0)

/-- The reindexing of level-{lit}`1` directions from the restricted shape. -/
abbrev reindex₁ (a₁ : F.Shape 1) :
    F.Direction (restrShape₁ F a₁).val 1 → F.Direction a₁.val 1 :=
  F.reindex waHom a₁ (i := 1)

/-- Reindexing commutes with the restriction of directions. -/
theorem dirRestr_reindex₁ (a₁ : F.Shape 1) (d : F.Direction (restrShape₁ F a₁).val 1) :
    dirRestr F a₁.val (reindex₁ F a₁ d) = reindex₀ F a₁ (dirRestr F _ d) :=
  congrFun (F.isFunctorial.reindex_naturality waHom a₁ waHom) d

variable (Z : (Fin 2)ᵒᵖ ⥤ Type)

/-- The value of {lit}`F` at {lit}`Z` in dependent-type terms: a shape, a
base assignment of its level-{lit}`0` directions in {lit}`Z 0`, and an
assignment of its level-{lit}`1` directions in the fibres of {lit}`Z 1 → Z 0`
over the base assignment at the restricted directions. -/
def Elem : Type :=
  Σ a : F.A, Σ g : F.Direction a 0 → Z.obj ⟨0⟩,
    ∀ d : F.Direction a 1, (famOfPsh Z).2 (g (dirRestr F a d))

/-- The other index of the walking arrow. -/
theorem eq_one_of_ne_zero {i : Fin 2} (h : i ≠ 0) : i = 1 := by
  omega

/-- The raw assignment of an element built from a base assignment and a
level-{lit}`1` assignment: at a direction over {lit}`0` the base assignment,
at one over {lit}`1` the level-{lit}`1` assignment. -/
def assign {a : F.A} (g : F.Direction a 0 → Z.obj ⟨0⟩)
    (w : ∀ d : F.Direction a 1, (famOfPsh Z).2 (g (dirRestr F a d))) (b : F.B a) :
    Σ i : Fin 2, Z.obj ⟨i⟩ :=
  if h : F.r ⟨a, b⟩ = 0 then ⟨0, g ⟨b, h⟩⟩ else ⟨1, (w ⟨b, eq_one_of_ne_zero h⟩).val⟩

/-- The raw assignment at a direction over {lit}`0`. -/
theorem assign_zero {a : F.A} (g : F.Direction a 0 → Z.obj ⟨0⟩)
    (w : ∀ d : F.Direction a 1, (famOfPsh Z).2 (g (dirRestr F a d))) {b : F.B a}
    (h : F.r ⟨a, b⟩ = 0) : assign F Z g w b = ⟨0, g ⟨b, h⟩⟩ :=
  dif_pos h

/-- The raw assignment at a direction over {lit}`1`. -/
theorem assign_one {a : F.A} (g : F.Direction a 0 → Z.obj ⟨0⟩)
    (w : ∀ d : F.Direction a 1, (famOfPsh Z).2 (g (dirRestr F a d))) {b : F.B a}
    (h : F.r ⟨a, b⟩ = 1) : assign F Z g w b = ⟨1, (w ⟨b, h⟩).val⟩ :=
  dif_neg fun h' ↦ Fin.zero_ne_one (h'.symm.trans h)

/-- The raw assignment is compatible with the direction-input map. -/
theorem assign_compatible {a : F.A} (g : F.Direction a 0 → Z.obj ⟨0⟩)
    (w : ∀ d : F.Direction a 1, (famOfPsh Z).2 (g (dirRestr F a d))) :
    F.Compatible (PresheafDomPFunctorData.elemProj Z) a (assign F Z g w) := by
  funext b
  by_cases h : F.r ⟨a, b⟩ = 0
  · change (assign F Z g w b).1 = F.r ⟨a, b⟩
    rw [assign_zero F Z g w h]
    exact h.symm
  · change (assign F Z g w b).1 = F.r ⟨a, b⟩
    rw [assign_one F Z g w (eq_one_of_ne_zero h)]
    exact (eq_one_of_ne_zero h).symm

/-- The element built from a base assignment and a level-{lit}`1` assignment,
before its naturality. -/
def assignObj {a : F.A} (g : F.Direction a 0 → Z.obj ⟨0⟩)
    (w : ∀ d : F.Direction a 1, (famOfPsh Z).2 (g (dirRestr F a d))) :
    F.toSliceDomPFunctor.Obj (PresheafDomPFunctorData.elemProj Z) :=
  ⟨⟨a, assign F Z g w⟩, assign_compatible F Z g w⟩

/-- The value the built element gives a level-{lit}`0` direction is the base
assignment. -/
theorem value_assignObj_zero {a : F.A} (g : F.Direction a 0 → Z.obj ⟨0⟩)
    (w : ∀ d : F.Direction a 1, (famOfPsh Z).2 (g (dirRestr F a d))) (d : F.Direction a 0) :
    F.value (assignObj F Z g w) d = g d :=
  eq_of_heq (Sigma.mk.inj_iff.mp
    ((sigma_value Z F.toPresheafDomPFunctorData (assignObj F Z g w) d).trans
      (assign_zero F Z g w d.property))).2

/-- The value the built element gives a level-{lit}`1` direction is the
level-{lit}`1` assignment. -/
theorem value_assignObj_one {a : F.A} (g : F.Direction a 0 → Z.obj ⟨0⟩)
    (w : ∀ d : F.Direction a 1, (famOfPsh Z).2 (g (dirRestr F a d))) (d : F.Direction a 1) :
    F.value (assignObj F Z g w) d = (w d).val :=
  eq_of_heq (Sigma.mk.inj_iff.mp
    ((sigma_value Z F.toPresheafDomPFunctorData (assignObj F Z g w) d).trans
      (assign_one F Z g w d.property))).2

/-- Two elements of {lit}`Elem` with the same shape are equal when their base
assignments agree and their level-{lit}`1` assignments agree in {lit}`Z 1`. -/
theorem gw_ext {a : F.A} {g g' : F.Direction a 0 → Z.obj ⟨0⟩} (hg : g' = g)
    {w : ∀ d : F.Direction a 1, (famOfPsh Z).2 (g (dirRestr F a d))}
    {w' : ∀ d : F.Direction a 1, (famOfPsh Z).2 (g' (dirRestr F a d))}
    (hw : ∀ d, (w' d).val = (w d).val) :
    (⟨g', w'⟩ : Σ g : F.Direction a 0 → Z.obj ⟨0⟩,
      ∀ d : F.Direction a 1, (famOfPsh Z).2 (g (dirRestr F a d))) = ⟨g, w⟩ := by
  subst hg
  exact Sigma.ext rfl (heq_of_eq (funext fun d ↦ Subtype.ext (hw d)))

/-- The value of {lit}`F` at {lit}`Z` is {lit}`Elem F Z`. -/
def elemEquiv : F.obj Z ≃ Elem F Z where
  toFun x :=
    ⟨x.shape, fun d ↦ F.value x.val d, fun d ↦ ⟨F.value x.val d, (x.property waHom d).symm⟩⟩
  invFun e := ⟨assignObj F Z e.2.1 e.2.2,
    (isNatural_iff F.toPresheafDomPFunctorData F.isFunctorial.directionRestr_id Z _).mpr fun d ↦
      (value_assignObj_zero F Z _ _ _).trans
        ((e.2.2 d).property.symm.trans (congrArg _ (value_assignObj_one F Z _ _ d).symm))⟩
  left_inv x := by
    refine Subtype.ext (Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun b ↦ ?_))))
    by_cases h : F.r ⟨x.shape, b⟩ = 0
    · exact (assign_zero F Z _ _ h).trans (sigma_value Z F.toPresheafDomPFunctorData x.val ⟨b, h⟩)
    · exact (assign_one F Z _ _ (eq_one_of_ne_zero h)).trans
        (sigma_value Z F.toPresheafDomPFunctorData x.val ⟨b, eq_one_of_ne_zero h⟩)
  right_inv e :=
    Sigma.ext rfl (heq_of_eq (gw_ext F Z (funext fun d ↦ value_assignObj_zero F Z _ _ d)
      fun d ↦ value_assignObj_one F Z _ _ d))

/-! # Elements by level, and the restriction -/

/-- The elements over a level: those of {lit}`Elem` whose shape lies over it. -/
def ElemAt (j : Fin 2) : Type :=
  Σ a : F.Shape j, Σ g : F.Direction a.val 0 → Z.obj ⟨0⟩,
    ∀ d : F.Direction a.val 1, (famOfPsh Z).2 (g (dirRestr F a.val d))

/-- Two elements of {lit}`Elem` reassembled with their shapes' level
conditions are equal when they are. -/
theorem elemAt_congr {j : Fin 2} (t s : Elem F Z) (e : t = s) (h : F.q t.1 = j) :
    (⟨⟨t.1, h⟩, t.2⟩ : ElemAt F Z j) = ⟨⟨s.1, e ▸ h⟩, s.2⟩ := by
  subst e
  rfl

/-- The elements of the output presheaf over a level are the elements of
{lit}`Elem` over it. -/
def objLevel (j : Fin 2) : { x : F.obj Z // F.q x.shape = j } ≃ ElemAt F Z j where
  toFun x := ⟨⟨(elemEquiv F Z x.val).1, x.property⟩, (elemEquiv F Z x.val).2⟩
  invFun e := ⟨(elemEquiv F Z).symm ⟨e.1.val, e.2⟩, e.1.property⟩
  left_inv x := Subtype.ext ((elemEquiv F Z).left_inv x.val)
  right_inv e := elemAt_congr F Z _ _ ((elemEquiv F Z).right_inv ⟨e.1.val, e.2⟩) _

/-- The restriction from level {lit}`1` to level {lit}`0` on elements:
restrict the shape and precompose the assignments with the reindexings. -/
def restrElem (e : ElemAt F Z 1) : ElemAt F Z 0 :=
  ⟨restrShape₁ F e.1, fun d ↦ e.2.1 (reindex₀ F e.1 d), fun d ↦
    ⟨(e.2.2 (reindex₁ F e.1 d)).val,
      (e.2.2 (reindex₁ F e.1 d)).property.trans (congrArg e.2.1 (dirRestr_reindex₁ F e.1 d))⟩⟩

/-- The value the restriction of an element gives a direction is the value the
element gives its reindexing. -/
theorem value_objRestr (x : F.obj Z) (hx : F.q x.shape = 1) ⦃i : Fin 2⦄
    (d : F.Direction (F.objRestr waHom x hx).shape i) :
    F.value (F.objRestr waHom x hx).val d = F.value x.val (F.reindex waHom ⟨x.shape, hx⟩ d) := by
  obtain ⟨b, rfl⟩ := d
  rfl

/-- The restriction of the output presheaf is {lit}`restrElem` on elements. -/
theorem objLevel_objRestr (x : F.obj Z) (hx : F.q x.shape = 1) :
    objLevel F Z 0 ⟨F.objRestr waHom x hx, (F.shapeRestr waHom ⟨x.shape, hx⟩).property⟩ =
      restrElem F Z (objLevel F Z 1 ⟨x, hx⟩) :=
  Sigma.ext rfl (heq_of_eq (gw_ext F Z (funext fun d ↦ value_objRestr F Z x hx d)
    fun d ↦ value_objRestr F Z x hx d))

/-! # The condition and the code -/

/-- A presheaf polynomial endofunctor on the walking arrow is base-cartesian
when, for every level-{lit}`1` shape, the reindexing of level-{lit}`0`
directions from its restriction is a bijection. -/
structure BaseCartesian where
  /-- The inverse of the reindexing at level {lit}`0`. -/
  inv : ∀ a₁ : F.Shape 1, F.Direction a₁.val 0 → F.Direction (restrShape₁ F a₁).val 0
  /-- The inverse is a left inverse. -/
  inv_reindex : ∀ (a₁ : F.Shape 1) d, inv a₁ (reindex₀ F a₁ d) = d
  /-- The inverse is a right inverse. -/
  reindex_inv : ∀ (a₁ : F.Shape 1) d, reindex₀ F a₁ (inv a₁ d) = d

variable {F} (hF : BaseCartesian F)

/-- The inverse reindexing sends the restriction of a reindexed direction to
the restriction of the direction. -/
theorem BaseCartesian.inv_dirRestr_reindex₁ (a₁ : F.Shape 1)
    (d : F.Direction (restrShape₁ F a₁).val 1) :
    hF.inv a₁ (dirRestr F a₁.val (reindex₁ F a₁ d)) = dirRestr F _ d := by
  rw [dirRestr_reindex₁]
  exact hF.inv_reindex a₁ _

/-- The fibre at a level-{lit}`1` shape: assignments of its level-{lit}`1`
directions, the family read at the inverse reindexing of the restricted
direction, that restrict along the reindexing to a given assignment of the
restricted shape. -/
def genFibre₁ (a₁ : F.Shape 1) (A : F.Direction (restrShape₁ F a₁).val 0 → Type)
    (w : ∀ d : F.Direction (restrShape₁ F a₁).val 1, A (dirRestr F _ d)) : Type :=
  { w₁ : ∀ d₁ : F.Direction a₁.val 1, A (hF.inv a₁ (dirRestr F a₁.val d₁)) //
    ∀ d, HEq (w₁ (reindex₁ F a₁ d)) (w d) }

/-- The fibre at a level-{lit}`1` shape over a level-{lit}`0` shape it
restricts to, by transport along the restriction equation. -/
def genFibreAt (a₁ : F.Shape 1) :
    (a : F.Shape 0) → restrShape₁ F a₁ = a → (A : F.Direction a.val 0 → Type) →
      (∀ d : F.Direction a.val 1, A (dirRestr F a.val d)) → Type
  | _, rfl, A, w => genFibre₁ hF a₁ A w

/-- The decoding of the code at a level-{lit}`0` element: the level-{lit}`1`
shapes over its shape, each with its fibre. -/
def genFibre (a : F.Shape 0) (A : F.Direction a.val 0 → Type)
    (w : ∀ d : F.Direction a.val 1, A (dirRestr F a.val d)) : Type :=
  Σ a₁ : { a₁ : F.Shape 1 // restrShape₁ F a₁ = a }, genFibreAt hF a₁.val a a₁.property A w

/-- The code of a base-cartesian presheaf polynomial endofunctor on the
walking arrow. -/
def genCode : IR.{0, 0, 1, 1} Type Type :=
  IR.sigma Type Type (F.Shape 0) fun a ↦
    IR.delta Type Type (F.Direction a.val 0) fun A ↦
      IR.sigma Type Type (∀ d : F.Direction a.val 1, A (dirRestr F a.val d)) fun w ↦
        IR.iota Type Type (genFibre hF a A w)

/-! # The isomorphism -/

/-- The level-{lit}`0` elements are the index type of the code's
interpretation. -/
def genBaseEquiv : ElemAt F Z 0 ≃ (IR.interpObj Type Type (genCode hF) (famOfPsh Z)).1 where
  toFun e := ⟨e.1, e.2.1, e.2.2, ⟨()⟩⟩
  invFun s := ⟨s.1, s.2.1, s.2.2.1⟩
  left_inv _ := rfl
  right_inv s :=
    match s with
    | ⟨_, _, _, ⟨⟨⟩⟩⟩ => rfl

/-- Two elements of the fibre over equal points are heterogeneously equal
when they agree in {lit}`Z 1`. -/
theorem fibre_heq {u u' : Z.obj ⟨0⟩} (e : u = u') (x : (famOfPsh Z).2 u) (y : (famOfPsh Z).2 u')
    (h : x.val = y.val) : HEq x y := by
  subst e
  exact heq_of_eq (Subtype.ext h)

/-- Heterogeneously equal elements of the fibre over equal points agree in
{lit}`Z 1`. -/
theorem fst_of_fibre_heq {u u' : Z.obj ⟨0⟩} (e : u = u') {x : (famOfPsh Z).2 u}
    {y : (famOfPsh Z).2 u'} (h : HEq x y) : x.val = y.val := by
  subst e
  exact congrArg Subtype.val (eq_of_heq h)

/-- An element of the code's total space with a level-{lit}`1` shape at its
own restriction, from the base assignment, the level-{lit}`1` assignment and
the fibre element. -/
def genTotalMk (a₁ : F.Shape 1) (g : F.Direction (restrShape₁ F a₁).val 0 → Z.obj ⟨0⟩)
    (w : ∀ d : F.Direction (restrShape₁ F a₁).val 1, (famOfPsh Z).2 (g (dirRestr F _ d)))
    (f : genFibre₁ hF a₁ ((famOfPsh Z).2 ∘ g) w) :
    Σ p : (IR.interpObj Type Type (genCode hF) (famOfPsh Z)).1,
      (IR.interpObj Type Type (genCode hF) (famOfPsh Z)).2 p :=
  ⟨⟨restrShape₁ F a₁, g, w, ⟨()⟩⟩, ⟨⟨a₁, rfl⟩, f⟩⟩

/-- Two elements of the code's total space at the same level-{lit}`1` shape
are equal when their base assignments agree and their assignments agree in
{lit}`Z 1`. -/
theorem genTotalMk_ext (a₁ : F.Shape 1) {g g' : F.Direction (restrShape₁ F a₁).val 0 → Z.obj ⟨0⟩}
    (hg : g' = g)
    {w : ∀ d : F.Direction (restrShape₁ F a₁).val 1, (famOfPsh Z).2 (g (dirRestr F _ d))}
    {w' : ∀ d : F.Direction (restrShape₁ F a₁).val 1, (famOfPsh Z).2 (g' (dirRestr F _ d))}
    (hw : ∀ d, (w' d).val = (w d).val)
    {f : genFibre₁ hF a₁ ((famOfPsh Z).2 ∘ g) w} {f' : genFibre₁ hF a₁ ((famOfPsh Z).2 ∘ g') w'}
    (hf : ∀ d₁, (f'.val d₁).val = (f.val d₁).val) :
    genTotalMk Z hF a₁ g' w' f' = genTotalMk Z hF a₁ g w f := by
  subst hg
  obtain rfl : w' = w := funext fun d ↦ Subtype.ext (hw d)
  obtain rfl : f' = f := Subtype.ext (funext fun d₁ ↦ Subtype.ext (hf d₁))
  rfl

/-- The inverse of the level-{lit}`1` equivalence at a level-{lit}`1` shape
over a level-{lit}`0` shape it restricts to. -/
def genTotalInv (a₁ : F.Shape 1) :
    (a : F.Shape 0) → (h : restrShape₁ F a₁ = a) → (g : F.Direction a.val 0 → Z.obj ⟨0⟩) →
      (w : ∀ d : F.Direction a.val 1, (famOfPsh Z).2 (g (dirRestr F a.val d))) →
      genFibreAt hF a₁ a h ((famOfPsh Z).2 ∘ g) w → ElemAt F Z 1
  | _, rfl, g, _, f => ⟨a₁, fun d ↦ g (hF.inv a₁ d), fun d₁ ↦ f.val d₁⟩

/-- The level-{lit}`1` equivalence on an element: restrict to the
level-{lit}`0` element below, and keep the level-{lit}`1` assignment as the
fibre element, reindexed by the inverse at level {lit}`0`. -/
def genTotalTo (e : ElemAt F Z 1) :
    Σ p : (IR.interpObj Type Type (genCode hF) (famOfPsh Z)).1,
      (IR.interpObj Type Type (genCode hF) (famOfPsh Z)).2 p :=
  genTotalMk Z hF e.1 (fun d ↦ e.2.1 (reindex₀ F e.1 d))
    (fun d ↦ ⟨(e.2.2 (reindex₁ F e.1 d)).val,
      (e.2.2 (reindex₁ F e.1 d)).property.trans (congrArg e.2.1 (dirRestr_reindex₁ F e.1 d))⟩)
    ⟨fun d₁ ↦ ⟨(e.2.2 d₁).val,
        (e.2.2 d₁).property.trans (congrArg e.2.1 (hF.reindex_inv e.1 _).symm)⟩,
      fun d ↦ fibre_heq Z
        (congrArg (fun d ↦ e.2.1 (reindex₀ F e.1 d)) (hF.inv_dirRestr_reindex₁ e.1 d)) _ _ rfl⟩

/-- The level-{lit}`1` equivalence inverts its inverse. -/
theorem genTotalTo_genTotalInv (a₁ : F.Shape 1) (a : F.Shape 0) (h : restrShape₁ F a₁ = a)
    (g : F.Direction a.val 0 → Z.obj ⟨0⟩)
    (w : ∀ d : F.Direction a.val 1, (famOfPsh Z).2 (g (dirRestr F a.val d)))
    (f : genFibreAt hF a₁ a h ((famOfPsh Z).2 ∘ g) w) :
    genTotalTo Z hF (genTotalInv Z hF a₁ a h g w f) = ⟨⟨a, g, w, ⟨()⟩⟩, ⟨⟨a₁, h⟩, f⟩⟩ := by
  subst h
  exact genTotalMk_ext Z hF a₁ (funext fun d ↦ congrArg g (hF.inv_reindex a₁ d))
    (fun d ↦ fst_of_fibre_heq Z (congrArg g (hF.inv_dirRestr_reindex₁ a₁ d)) (f.property d))
    fun _ ↦ rfl

/-- The level-{lit}`1` elements are the total space of the code's
interpretation: the level-{lit}`0` element below, and the fibre element. -/
def genTotalEquiv :
    ElemAt F Z 1 ≃ Σ p : (IR.interpObj Type Type (genCode hF) (famOfPsh Z)).1,
      (IR.interpObj Type Type (genCode hF) (famOfPsh Z)).2 p where
  toFun := genTotalTo Z hF
  invFun s := genTotalInv Z hF s.2.1.val s.1.1 s.2.1.property s.1.2.1 s.1.2.2.1 s.2.2
  left_inv e :=
    Sigma.ext rfl (heq_of_eq (gw_ext F Z (funext fun d ↦ congrArg e.2.1 (hF.reindex_inv e.1 d))
      fun _ ↦ rfl))
  right_inv s := genTotalTo_genTotalInv Z hF s.2.1.val s.1.1 s.2.1.property s.1.2.1 s.1.2.2.1 s.2.2

/-- The output presheaf of a base-cartesian presheaf polynomial endofunctor
on the walking arrow is the presheaf of the interpretation of its code at the
family of the input. -/
def genCodeEquiv :
    PshEquiv (F.objPresheaf Z) (pshOfFam (IR.interpObj Type Type (genCode hF) (famOfPsh Z))) where
  base := (objLevel F Z 0).trans (genBaseEquiv Z hF)
  total := (objLevel F Z 1).trans (genTotalEquiv Z hF)
  map_total t :=
    congrArg (fun e : ElemAt F Z 0 ↦ genBaseEquiv Z hF e)
      (objLevel_objRestr F Z t.val t.property).symm

/-! # The transcription is an instance -/

/-- The transcription of a slice polynomial functor is base-cartesian: every
shape has the level-{lit}`0` directions {lit}`X`, on which reindexing is the
identity. -/
def arrowPshBaseCartesian {X Y : Type} (P : SlicePFunctor.{0, 0, 0, 0} X Y) :
    BaseCartesian (arrowPsh P) where
  inv a₁ d :=
    match a₁, d with
    | ⟨.inl _, h⟩, _ => absurd h Fin.zero_ne_one
    | ⟨.inr _, _⟩, ⟨.inl x, _⟩ => ⟨.inl x, rfl⟩
    | ⟨.inr _, _⟩, ⟨.inr _, h⟩ => absurd h Fin.zero_ne_one.symm
  inv_reindex a₁ d :=
    match a₁, d with
    | ⟨.inl _, h⟩, _ => absurd h Fin.zero_ne_one
    | ⟨.inr _, _⟩, ⟨.inl _, _⟩ => rfl
    | ⟨.inr _, _⟩, ⟨.inr e, _⟩ => PEmpty.elim e
  reindex_inv a₁ d :=
    match a₁, d with
    | ⟨.inl _, h⟩, _ => absurd h Fin.zero_ne_one
    | ⟨.inr _, _⟩, ⟨.inl _, _⟩ => rfl
    | ⟨.inr _, _⟩, ⟨.inr _, h⟩ => absurd h Fin.zero_ne_one.symm

end GebProto.LargeIR
