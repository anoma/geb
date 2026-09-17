/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Data.PFunctor.Presheaf.W
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.Order.Fin.Basic

set_option doc.verso true in
/-!
# Types dependent on a W-type: presheaf polynomial functors on the walking arrow

A presheaf on the walking arrow, the preorder category on {lit}`Fin 2`, is a
type at {lit}`0` together with a type at {lit}`1` and a map from the latter to the
former: a type family over the type at {lit}`0`. A presheaf polynomial
endofunctor on the walking arrow whose value at {lit}`0` reads only its input's
value at {lit}`0` therefore has a W-type whose fiber over {lit}`0` is an ordinary
W-type and whose fiber over {lit}`1` is a type family over it, a type dependent
on a W-type obtained from the parametric-right-adjoint construction rather
than by a recursion of its own.

This module builds that endofunctor, {lit}`PFunctor.dependent`, from a
polynomial functor {lit}`P`, the base, and a family {lit}`fam` assigning each
shape {lit}`a` of {lit}`P` a slice-domain polynomial functor over the directions
{lit}`P.B a` ({name}`SliceDomPFunctor`), the dependent part. In the notation of
{name}`PresheafPFunctor` the shape presheaf {lit}`T1` has {lit}`P.A` over {lit}`0`
and {lit}`Σ a, (fam a).A` over {lit}`1`, restricted by the projection; the arity
presheaf of a base shape {lit}`a` has {lit}`P.B a` over {lit}`0` and nothing over
{lit}`1`, and that of a dependent shape {lit}`(a, a')` has {lit}`(fam a).B a'`
over {lit}`1` and {lit}`P.B a` over {lit}`0`, restricted by the direction-input
map {lit}`(fam a).r`; the reindexing along the arrow is the inclusion of
{lit}`P.B a` into the arity of {lit}`(a, a')`.

On the W-type, {lit}`baseEquiv` identifies the fiber over {lit}`0` with
{lit}`P.W`; {lit}`Fiber` is the type family over {lit}`P.W` given by the fiber of
the W-type's restriction map along the arrow; and {lit}`fiberEquiv` is the
computation rule identifying the fiber over a tree with the value of
{lit}`fam` at the tree's head on the family of fibers over its children,
{lit}`Fiber (WType.mk a f) ≃ (fam a).Obj (Sigma.fst : (Σ b, Fiber (f b)) → P.B a)`.

## Main definitions

* {lit}`PresheafPFunctor.arrow` — the non-identity morphism {lit}`0 ⟶ 1` of the
  walking arrow.
* {lit}`PFunctor.Dependent.Shape`, {lit}`Direction`, {lit}`shapeIndex`,
  {lit}`dirIndex` — the shapes and directions of the endofunctor with their
  output and input indices.
* {lit}`PFunctor.Dependent.restrShape`, {lit}`reindexDir`, {lit}`restrDir` — the
  shape restriction, the arity reindexing, and the direction restriction, each
  by the target index.
* {lit}`PFunctor.dependent` — the presheaf polynomial endofunctor on the walking
  arrow.
* {lit}`PFunctor.Dependent.toBase` / {lit}`ofBase` — the folds between the
  endofunctor's raw W-trees and {lit}`P.W`.
* {lit}`PFunctor.Dependent.baseEquiv` — the W-type's fiber over {lit}`0` is
  {lit}`P.W`.
* {lit}`PFunctor.Dependent.Fiber` — the type family over {lit}`P.W`: the fiber of
  the W-type's restriction map along the arrow.
* {lit}`PFunctor.Dependent.fiberEquiv` / {lit}`fiberMkEquiv` — the computation
  rule for {lit}`Fiber`.

## Main statements

* {lit}`PresheafPFunctor.isHereditarilyNatural_mk_iff_arrow` — on the walking
  arrow, the local naturality clause of hereditary naturality reduces to the
  single non-identity morphism.
* {lit}`PFunctor.Dependent.fiber_iff` — the fiber condition on an element over
  {lit}`1` is that {lit}`toBase` of its tree is the base tree.

## Implementation notes

The walking arrow is mathlib's preorder category on {lit}`Fin 2`, the category
mathlib's {lit}`ComposableArrows` uses at length one, rather
than a category defined here. Its morphisms are subsingletons, so a law
quantified over morphisms is proved by a case split on the two objects
({lit}`match i with | 0 => .. | 1 => ..`, per the constructive rules on
{lit}`Fin`) followed by {name}`Subsingleton.elim`.

The restriction operations take the target index as a {lit}`Fin 2` argument
and are defined by {name}`Fin.cases`, which reduces definitionally at each
numeral, so the functor laws hold by {name}`rfl` after the case split, the
{lit}`cast` of the {lit}`reindex` laws standing between definitionally equal
types and reducing away.

{lit}`Fiber` is defined as the fiber of the restriction map, which is what the
presheaf structure gives, and {lit}`fiber_iff` restates the condition through
the fold {lit}`toBase`, in which form the computation rule's destructor,
{lit}`destRaw`, reads the base tree off the raw tree definitionally. The
destructor is stated for the fiber over {lit}`toBase w` with head and children
computed by {name}`PFunctor.W.head` and {name}`PFunctor.W.children`, so that no
transport of shapes along an index equation arises; {lit}`fiberEquiv` transports
the result once along {lit}`fiber_iff`, and its round trips discharge that
transport by {name}`cast_eq` and {name}`cast_heq`.

## References

* \[Weber2007\]
* \[GambinoHyland2004\]
* \[GambinoKock2013\]

## Tags

polynomial functor, presheaf, parametric right adjoint, walking arrow, W-type,
dependent type, PFunctor
-/

set_option doc.verso true

public section

open CategoryTheory

universe uA uB

namespace PresheafPFunctor

/-- The non-identity morphism {lit}`0 ⟶ 1` of the walking arrow, the preorder
category on {lit}`Fin 2`. -/
def arrow : ((0 : Fin 2) ⟶ 1) := homOfLE (by decide)

/-- On the walking arrow, the local naturality clause of
{name}`PresheafPFunctor.isHereditarilyNatural_mk` reduces to the single
non-identity morphism {lit}`arrow`: on an identity morphism the clause holds by
the identity laws of {lit}`directionRestr` and {lit}`wRestrTree`, and the
morphisms of the walking arrow are subsingletons. -/
theorem isHereditarilyNatural_mk_iff_arrow
    (F : PresheafPFunctor.{0, 0, uA, uB, 0, 0} (Fin 2) (Fin 2))
    (x : F.toSliceDomPFunctor.Obj F.toSlicePFunctor.wIndex) :
    F.IsHereditarilyNatural (SlicePFunctor.W.mk x) ↔
      (∀ b : F.toSliceDomPFunctor.Direction x.1.1 1,
          x.1.2 (F.directionRestr x.1.1 arrow b).1
            = F.wRestrTree arrow (x.1.2 b.1)
                (((F.toSliceDomPFunctor.compatible_iff F.toSlicePFunctor.wIndex x.1.1 x.1.2).mp
                  x.2 b.1).trans b.2)) ∧
        ∀ b, F.IsHereditarilyNatural (x.1.2 b) := by
  rw [F.isHereditarilyNatural_mk]
  refine and_congr ⟨fun h b ↦ h arrow b, fun h i i' g b ↦ ?_⟩ Iff.rfl
  match i, i', g, b with
  | 0, 0, g, b =>
    obtain rfl : g = 𝟙 _ := Subsingleton.elim _ _
    exact (congrArg (fun d ↦ x.1.2 d.1)
      (congrFun (F.isFunctorial.directionRestr_id x.1.1 0) b)).trans (F.wRestrTree_id _ _).symm
  | 1, 1, g, b =>
    obtain rfl : g = 𝟙 _ := Subsingleton.elim _ _
    exact (congrArg (fun d ↦ x.1.2 d.1)
      (congrFun (F.isFunctorial.directionRestr_id x.1.1 1) b)).trans (F.wRestrTree_id _ _).symm
  | 1, 0, g, b =>
    obtain rfl : g = arrow := Subsingleton.elim _ _
    exact h b
  | 0, 1, g, _ => exact absurd (leOfHom g) (by decide)

end PresheafPFunctor

namespace PFunctor

variable (P : PFunctor.{uA, uB}) (fam : ∀ a : P.A, SliceDomPFunctor.{uA, uB, uB} (P.B a))

namespace Dependent

/-- The shapes: a base shape {lit}`a`, over {lit}`0`, or a dependent shape
{lit}`(a, a')` with {lit}`a'` a shape of {lit}`fam a`, over {lit}`1`. -/
@[expose] def Shape : Type uA := P.A ⊕ Σ a : P.A, (fam a).A

/-- The base shape underlying a shape. -/
@[expose] def base : Shape P fam → P.A
  | Sum.inl a => a
  | Sum.inr p => p.1

/-- The output index of a shape: {lit}`0` for a base shape, {lit}`1` for a
dependent one. -/
@[expose] def shapeIndex : Shape P fam → Fin 2
  | Sum.inl _ => 0
  | Sum.inr _ => 1

/-- The directions of a shape: those of a base shape {lit}`a` are {lit}`P.B a`;
those of a dependent shape {lit}`(a, a')` are the dependent directions
{lit}`(fam a).B a'` together with the base directions {lit}`P.B a`. -/
@[expose] def Direction : Shape P fam → Type uB
  | Sum.inl a => P.B a
  | Sum.inr p => (fam p.1).B p.2 ⊕ P.B p.1

/-- The input index of a direction: {lit}`1` for a dependent direction, {lit}`0`
for a base direction. -/
@[expose] def dirIndex : ∀ x : Shape P fam, Direction P fam x → Fin 2
  | Sum.inl _, _ => 0
  | Sum.inr _, Sum.inl _ => 1
  | Sum.inr _, Sum.inr _ => 0

/-- The inclusion of the base directions into the directions of a shape. -/
@[expose] def inj : ∀ x : Shape P fam, P.B (base P fam x) → Direction P fam x
  | Sum.inl _ => id
  | Sum.inr _ => Sum.inr

/-- The restriction of a direction to a base direction: a dependent direction
{lit}`d` of {lit}`(a, a')` goes to the base direction {lit}`(fam a).r ⟨a', d⟩`,
and a base direction is fixed. -/
@[expose] def toBaseDir : ∀ x : Shape P fam, Direction P fam x → Direction P fam x
  | Sum.inl _, b => b
  | Sum.inr p, Sum.inl d => Sum.inr ((fam p.1).r ⟨p.2, d⟩)
  | Sum.inr _, Sum.inr b => Sum.inr b

/-- The restriction of a shape to the target index {lit}`j'`: to {lit}`0`, its
base shape; to {lit}`1`, itself. -/
@[expose] def restrShape (j' : Fin 2) (x : Shape P fam) : Shape P fam :=
  Fin.cases (Sum.inl (base P fam x)) (fun _ ↦ x) j'

/-- The reindexing of directions along the restriction to the target index
{lit}`j'`: to {lit}`0`, the inclusion {lit}`inj` of the base directions; to
{lit}`1`, the identity. -/
@[expose] def reindexDir (j' : Fin 2) (x : Shape P fam) :
    Direction P fam (restrShape P fam j' x) → Direction P fam x :=
  Fin.cases (motive := fun j' ↦ Direction P fam (restrShape P fam j' x) → Direction P fam x)
    (inj P fam x) (fun _ ↦ id) j'

/-- The restriction of directions to the target index {lit}`i'`: to {lit}`0`,
{lit}`toBaseDir`; to {lit}`1`, the identity. -/
@[expose] def restrDir (i' : Fin 2) (x : Shape P fam) : Direction P fam x → Direction P fam x :=
  Fin.cases (toBaseDir P fam x) (fun _ ↦ id) i'

/-- The index of an included base direction is {lit}`0`. -/
theorem dirIndex_inj (x : Shape P fam) (b : P.B (base P fam x)) :
    dirIndex P fam x (inj P fam x b) = 0 := by
  cases x <;> rfl

/-- The index of a restricted-to-base direction is {lit}`0`. -/
theorem dirIndex_toBaseDir (x : Shape P fam) (b : Direction P fam x) :
    dirIndex P fam x (toBaseDir P fam x b) = 0 := by
  cases x with
  | inl _ => rfl
  | inr _ => cases b <;> rfl

/-- A direction over {lit}`0` is fixed by {lit}`toBaseDir`. -/
theorem toBaseDir_of_dirIndex (x : Shape P fam) (b : Direction P fam x)
    (hb : dirIndex P fam x b = 0) : toBaseDir P fam x b = b := by
  cases x with
  | inl _ => rfl
  | inr _ =>
    cases b with
    | inl _ => exact absurd hb (by decide : (1 : Fin 2) ≠ 0)
    | inr _ => rfl

/-- {lit}`toBaseDir` is idempotent. -/
theorem toBaseDir_toBaseDir (x : Shape P fam) (b : Direction P fam x) :
    toBaseDir P fam x (toBaseDir P fam x b) = toBaseDir P fam x b :=
  toBaseDir_of_dirIndex P fam x _ (dirIndex_toBaseDir P fam x b)

/-- {lit}`toBaseDir` fixes an included base direction. -/
theorem toBaseDir_inj (x : Shape P fam) (b : P.B (base P fam x)) :
    toBaseDir P fam x (inj P fam x b) = inj P fam x b :=
  toBaseDir_of_dirIndex P fam x _ (dirIndex_inj P fam x b)

/-- An index of {lit}`Fin 2` at least {lit}`1` is {lit}`1`. -/
private theorem eq_one_of_one_le {i : Fin 2} (h : 1 ≤ i) : i = 1 := by
  match i with
  | 0 => exact absurd h (by decide)
  | 1 => rfl

/-- The restricted shape lies over the target index, when that is at most the
shape's index. -/
theorem shapeIndex_restrShape (j' : Fin 2) (x : Shape P fam) (h : j' ≤ shapeIndex P fam x) :
    shapeIndex P fam (restrShape P fam j' x) = j' := by
  match j' with
  | 0 => rfl
  | 1 => exact eq_one_of_one_le h

/-- The restricted direction lies over the target index, when that is at most
the direction's index. -/
theorem dirIndex_restrDir (i' : Fin 2) (x : Shape P fam) (b : Direction P fam x)
    (h : i' ≤ dirIndex P fam x b) : dirIndex P fam x (restrDir P fam i' x b) = i' := by
  match i' with
  | 0 => exact dirIndex_toBaseDir P fam x b
  | 1 => exact eq_one_of_one_le h

/-- The reindexed direction lies over the index of the direction it comes
from. -/
theorem dirIndex_reindexDir (j' : Fin 2) (x : Shape P fam)
    (b : Direction P fam (restrShape P fam j' x)) :
    dirIndex P fam x (reindexDir P fam j' x b) = dirIndex P fam (restrShape P fam j' x) b := by
  match j' with
  | 0 => exact (dirIndex_inj P fam x b).trans (dirIndex_toBaseDir P fam _ b).symm
  | 1 => rfl

/-- Restriction to a shape's own index fixes it. -/
theorem restrShape_of_shapeIndex (j : Fin 2) (x : Shape P fam) (hx : shapeIndex P fam x = j) :
    restrShape P fam j x = x := by
  match j, x with
  | 0, Sum.inl _ => rfl
  | 0, Sum.inr _ => exact absurd hx (by decide : (1 : Fin 2) ≠ 0)
  | 1, _ => rfl

/-- The base shape of a restricted shape is the base shape. -/
theorem base_restrShape (j' : Fin 2) (x : Shape P fam) :
    base P fam (restrShape P fam j' x) = base P fam x := by
  match j' with
  | 0 => rfl
  | 1 => rfl

/-- Restricting twice restricts to the lower index. -/
theorem restrShape_restrShape (j' j'' : Fin 2) (x : Shape P fam) (h : j'' ≤ j') :
    restrShape P fam j'' (restrShape P fam j' x) = restrShape P fam j'' x := by
  match j'' with
  | 0 => exact congrArg Sum.inl (base_restrShape P fam j' x)
  | 1 =>
    obtain rfl := eq_one_of_one_le h
    rfl

/-- Restriction to a direction's own index fixes it. -/
theorem restrDir_of_dirIndex (i : Fin 2) (x : Shape P fam) (b : Direction P fam x)
    (hb : dirIndex P fam x b = i) : restrDir P fam i x b = b := by
  match i with
  | 0 => exact toBaseDir_of_dirIndex P fam x b hb
  | 1 => rfl

/-- Restricting twice restricts to the lower index. -/
theorem restrDir_restrDir (i' i'' : Fin 2) (x : Shape P fam) (b : Direction P fam x)
    (h : i'' ≤ i') : restrDir P fam i'' x (restrDir P fam i' x b) = restrDir P fam i'' x b := by
  match i'' with
  | 0 =>
    match i' with
    | 0 => exact toBaseDir_toBaseDir P fam x b
    | 1 => rfl
  | 1 =>
    obtain rfl := eq_one_of_one_le h
    rfl

/-- Reindexing commutes with direction restriction. -/
theorem restrDir_reindexDir (j' i' : Fin 2) (x : Shape P fam)
    (b : Direction P fam (restrShape P fam j' x)) :
    restrDir P fam i' x (reindexDir P fam j' x b) =
      reindexDir P fam j' x (restrDir P fam i' (restrShape P fam j' x) b) := by
  match j' with
  | 0 =>
    match i' with
    | 0 =>
      exact (toBaseDir_inj P fam x b).trans
        (congrArg _ (toBaseDir_of_dirIndex P fam _ b rfl).symm)
    | 1 => rfl
  | 1 => rfl

/-- The operations of the endofunctor on the walking arrow. -/
@[expose] def data : PresheafPFunctorData.{0, 0, uA, uB, 0, 0} (Fin 2) (Fin 2) where
  A := Shape P fam
  B := Direction P fam
  r := fun x ↦ dirIndex P fam x.1 x.2
  q := shapeIndex P fam
  directionRestr := fun x _ i' f d ↦
    ⟨restrDir P fam i' x d.1, dirIndex_restrDir P fam i' x d.1 ((leOfHom f).trans_eq d.2.symm)⟩
  shapeRestr := fun _ j' g s ↦
    ⟨restrShape P fam j' s.1, shapeIndex_restrShape P fam j' s.1 ((leOfHom g).trans_eq s.2.symm)⟩
  reindex := fun _ j' _ s _ d ↦
    ⟨reindexDir P fam j' s.1 d.1, (dirIndex_reindexDir P fam j' s.1 d.1).trans d.2⟩

/-- The operations satisfy the functor laws. -/
theorem isFunctorial_data : (data P fam).IsFunctorial where
  directionRestr_id x i := by
    funext b
    exact Subtype.ext (restrDir_of_dirIndex P fam i x b.1 b.2)
  directionRestr_comp x i i' i'' f g := by
    funext b
    exact Subtype.ext (restrDir_restrDir P fam i' i'' x b.1 (leOfHom g)).symm
  shapeRestr_id j := by
    funext s
    exact Subtype.ext (restrShape_of_shapeIndex P fam j s.1 s.2)
  shapeRestr_comp j j' j'' g h := by
    funext s
    exact Subtype.ext (restrShape_restrShape P fam j' j'' s.1 (leOfHom h)).symm
  reindex_naturality j j' g s i i' f := by
    funext b
    exact Subtype.ext (restrDir_reindexDir P fam j' i' s.1 b.1)
  reindex_id j s i b := by
    match j, s with
    | 0, ⟨Sum.inl _, _⟩ => exact Subtype.ext rfl
    | 0, ⟨Sum.inr _, hs⟩ => exact absurd hs (by decide : (1 : Fin 2) ≠ 0)
    | 1, _ => exact Subtype.ext rfl
  reindex_comp j j' j'' g h s i b := by
    revert g h s i b
    match j, j', j'' with
    | 0, 0, 0 =>
      intro g h s i b
      obtain ⟨x, hx⟩ := s
      cases x with
      | inl _ => exact Subtype.ext rfl
      | inr _ => exact absurd hx (by decide : (1 : Fin 2) ≠ 0)
    | 1, 1, 1 => exact fun _ _ _ _ _ ↦ Subtype.ext rfl
    | 1, 1, 0 => exact fun _ _ _ _ _ ↦ Subtype.ext rfl
    | 1, 0, 0 => exact fun _ _ _ _ _ ↦ Subtype.ext rfl
    | 0, 0, 1 => exact fun _ h _ _ _ ↦ absurd (leOfHom h) (by decide)
    | 0, 1, 0 => exact fun g _ _ _ _ ↦ absurd (leOfHom g) (by decide)
    | 0, 1, 1 => exact fun g _ _ _ _ ↦ absurd (leOfHom g) (by decide)
    | 1, 0, 1 => exact fun _ h _ _ _ ↦ absurd (leOfHom h) (by decide)

end Dependent

/-- The presheaf polynomial endofunctor on the walking arrow assembled from the
base {lit}`P` and the dependent part {lit}`fam`: its value at {lit}`0` on an input
presheaf is {lit}`P` applied to the input's value at {lit}`0`, and its value at
{lit}`1` is, over each base node, the value of {lit}`fam` at that node's shape on
the input's family over {lit}`1`. -/
@[expose] def dependent : PresheafPFunctor.{0, 0, uA, uB, 0, 0} (Fin 2) (Fin 2) where
  toPresheafPFunctorData := Dependent.data P fam
  isFunctorial := Dependent.isFunctorial_data P fam

namespace Dependent

/-- The base tree of a raw W-tree of the endofunctor: every shape replaced by its
base shape, keeping the base children. A fold. -/
@[expose] def toBase : (dependent P fam).toPFunctor.W → P.W :=
  WType.elim P.W fun x ↦ WType.mk (base P fam x.1) (x.2 ∘ inj P fam x.1)

/-- The raw W-tree of the endofunctor carried by a base tree: every shape a base
shape. A fold. -/
@[expose] def ofBase : P.W → (dependent P fam).toPFunctor.W :=
  WType.elim (dependent P fam).toPFunctor.W fun x ↦ WType.mk (Sum.inl x.1) x.2

/-- A carried base tree is indexed at {lit}`0`. -/
theorem wIndexRoot_ofBase (t : P.W) :
    (dependent P fam).toSlicePFunctor.wIndexRoot (ofBase P fam t) = 0 := by
  cases t with
  | mk _ _ => rfl

/-- A carried base tree is admissible. -/
theorem wValid_ofBase (t : P.W) : (dependent P fam).toSlicePFunctor.WValid (ofBase P fam t) :=
  WType.rec (motive := fun t ↦ (dependent P fam).toSlicePFunctor.WValid (ofBase P fam t))
    (fun a f ih ↦
      ((dependent P fam).toSlicePFunctor.wValid_mk (Sum.inl a) (ofBase P fam ∘ f)).mpr
        ⟨ih, funext fun b ↦ wIndexRoot_ofBase P fam (f b)⟩)
    t

/-- The base tree of a carried base tree is the tree. -/
theorem toBase_ofBase (t : P.W) : toBase P fam (ofBase P fam t) = t :=
  WType.rec (motive := fun t ↦ toBase P fam (ofBase P fam t) = t)
    (fun a _ ih ↦ congrArg (WType.mk a) (funext ih)) t

/-- An admissible raw tree indexed at {lit}`0` is carried by its base tree: its
shapes are base shapes throughout, by admissibility. -/
theorem ofBase_toBase (w : (dependent P fam).toPFunctor.W)
    (hw : (dependent P fam).toSlicePFunctor.WValid w)
    (h0 : (dependent P fam).toSlicePFunctor.wIndexRoot w = 0) :
    ofBase P fam (toBase P fam w) = w :=
  WType.rec (motive := fun w ↦ (dependent P fam).toSlicePFunctor.WValid w →
      (dependent P fam).toSlicePFunctor.wIndexRoot w = 0 → ofBase P fam (toBase P fam w) = w)
    (fun x c ih hw h0 ↦ by
      cases x with
      | inl a =>
        exact congrArg (WType.mk (Sum.inl a)) (funext fun b ↦
          ih b ((((dependent P fam).toSlicePFunctor.wValid_mk _ _).mp hw).1 b)
            (congrFun (((dependent P fam).toSlicePFunctor.wValid_mk _ _).mp hw).2 b))
      | inr _ => exact absurd h0 (by decide : (1 : Fin 2) ≠ 0))
    w hw h0

/-- A carried base tree is hereditarily natural: a base shape has no direction
over {lit}`1`, so the local clause at each node is vacuous. -/
theorem isHereditarilyNatural_ofBase (t : P.W) :
    (dependent P fam).IsHereditarilyNatural ⟨ofBase P fam t, wValid_ofBase P fam t⟩ :=
  WType.rec
    (motive := fun t ↦
      (dependent P fam).IsHereditarilyNatural ⟨ofBase P fam t, wValid_ofBase P fam t⟩)
    (fun a f ih ↦
      ((dependent P fam).isHereditarilyNatural_mk_iff_arrow
        ⟨⟨Sum.inl a, fun b ↦ ⟨ofBase P fam (f b), wValid_ofBase P fam (f b)⟩⟩,
          ((dependent P fam).toSliceDomPFunctor.compatible_iff _ _ _).mpr fun b ↦
            wIndexRoot_ofBase P fam (f b)⟩).mpr
        ⟨fun b ↦ absurd b.2 (by decide : (0 : Fin 2) ≠ 1), ih⟩)
    t

/-- The W-type's fiber over {lit}`0` is {lit}`P.W`: the folds {lit}`toBase` and
{lit}`ofBase`, the latter landing in the fiber by {lit}`wValid_ofBase`,
{lit}`wIndexRoot_ofBase` and {lit}`isHereditarilyNatural_ofBase`. -/
@[expose] def baseEquiv : ((dependent P fam).W).obj ⟨(0 : Fin 2)⟩ ≃ P.W where
  toFun u := toBase P fam u.down.1.1
  invFun t := ULift.up ⟨⟨ofBase P fam t, wValid_ofBase P fam t⟩, wIndexRoot_ofBase P fam t,
    isHereditarilyNatural_ofBase P fam t⟩
  left_inv u := congrArg ULift.up (Subtype.ext (Subtype.ext
    (ofBase_toBase P fam u.down.1.1 u.down.1.2 u.down.2.1)))
  right_inv t := toBase_ofBase P fam t

/-- The type family over {lit}`P.W` the W-type carries: the fiber of the
W-type's restriction map along the arrow, read through {lit}`baseEquiv`. -/
@[expose] def Fiber (t : P.W) : Type (max uA uB) :=
  { u : ((dependent P fam).W).obj ⟨(1 : Fin 2)⟩ //
    ((dependent P fam).W).map PresheafPFunctor.arrow.op u = (baseEquiv P fam).symm t }

/-- Root restriction along the arrow does not change the base tree. -/
theorem toBase_wRestrTree (z : (dependent P fam).toSlicePFunctor.W)
    (hq : (dependent P fam).q (PFunctor.W.head z.1) = 1) :
    toBase P fam ((dependent P fam).wRestrTree PresheafPFunctor.arrow z hq).1 =
      toBase P fam z.1 := by
  obtain ⟨w, hw⟩ := z
  cases w with
  | mk _ _ => rfl

/-- The fiber condition on an element over {lit}`1`, restated through
{lit}`toBase`: the element's restriction along the arrow is the carried base
tree exactly when the base tree of its own tree is that base tree. -/
theorem fiber_iff (u : ((dependent P fam).W).obj ⟨(1 : Fin 2)⟩) (t : P.W) :
    ((dependent P fam).W).map PresheafPFunctor.arrow.op u = (baseEquiv P fam).symm t ↔
      toBase P fam u.down.1.1 = t := by
  constructor
  · intro h
    exact (toBase_wRestrTree P fam u.down.1 u.down.2.1).symm.trans
      ((congrArg (fun z ↦ toBase P fam z.down.1.1) h).trans (toBase_ofBase P fam t))
  · intro h
    obtain ⟨⟨⟨w, hw⟩, hi, hn⟩⟩ := u
    subst h
    cases w with
    | mk x c =>
      refine congrArg ULift.up (Subtype.ext (Subtype.ext ?_))
      exact congrArg (WType.mk (Sum.inl (base P fam x))) (funext fun b ↦
        (ofBase_toBase P fam (c (inj P fam x b))
          ((((dependent P fam).toSlicePFunctor.wValid_mk _ _).mp hw).1 _)
          ((congrFun (((dependent P fam).toSlicePFunctor.wValid_mk _ _).mp hw).2 _).trans
            (dirIndex_inj P fam x b))).symm)

/-- At a hereditarily natural dependent node, the base child at the restriction
of a dependent direction is the root restriction of the dependent child: the
local clause of {name}`PresheafPFunctor.isHereditarilyNatural_mk_iff_arrow`, on
raw trees. -/
theorem child_inr_eq (p : Σ a : P.A, (fam a).A)
    (c : Direction P fam (Sum.inr p) → (dependent P fam).toPFunctor.W)
    (hw : (dependent P fam).toSlicePFunctor.WValid (WType.mk (Sum.inr p) c))
    (hn : (dependent P fam).IsHereditarilyNatural ⟨WType.mk (Sum.inr p) c, hw⟩)
    (d : (fam p.1).B p.2) :
    c (Sum.inr ((fam p.1).r ⟨p.2, d⟩)) =
      ((dependent P fam).wRestrTree PresheafPFunctor.arrow
        ⟨c (Sum.inl d), (((dependent P fam).toSlicePFunctor.wValid_mk _ _).mp hw).1 _⟩
        (congrFun (((dependent P fam).toSlicePFunctor.wValid_mk _ _).mp hw).2 _)).1 :=
  congrArg Subtype.val
    ((((dependent P fam).isHereditarilyNatural_mk_iff_arrow
      (SlicePFunctor.W.dest (F := (dependent P fam).toSlicePFunctor)
        ⟨WType.mk (Sum.inr p) c, hw⟩)).mp hn).1 ⟨Sum.inl d, rfl⟩)

/-- The destructor of the computation rule, on a raw tree: a hereditarily
natural admissible tree indexed at {lit}`1` has a dependent root shape
{lit}`(a, a')`, and its dependent children, each in the fiber over the base
child at the corresponding base direction by the local naturality clause,
assemble the value of {lit}`fam a` at {lit}`a'`. Stated for the fiber over the
tree's own base tree, whose head and children are read off definitionally. -/
@[expose] def destRaw : ∀ (w : (dependent P fam).toPFunctor.W)
    (hw : (dependent P fam).toSlicePFunctor.WValid w),
    (dependent P fam).toSlicePFunctor.wIndexRoot w = 1 →
    (dependent P fam).IsHereditarilyNatural ⟨w, hw⟩ →
    (fam (PFunctor.W.head (toBase P fam w))).Obj
      (Sigma.fst : (Σ b, Fiber P fam (PFunctor.W.children (toBase P fam w) b)) →
        P.B (PFunctor.W.head (toBase P fam w)))
  | WType.mk (Sum.inl _) _, _, hi, _ => absurd hi (by decide : (0 : Fin 2) ≠ 1)
  | WType.mk (Sum.inr p) c, hw, _, hn =>
    ⟨⟨p.2, fun d ↦ ⟨(fam p.1).r ⟨p.2, d⟩,
      ⟨ULift.up ⟨⟨c (Sum.inl d), (((dependent P fam).toSlicePFunctor.wValid_mk _ _).mp hw).1 _⟩,
          congrFun (((dependent P fam).toSlicePFunctor.wValid_mk _ _).mp hw).2 _,
          (((dependent P fam).isHereditarilyNatural_mk
            (SlicePFunctor.W.dest (F := (dependent P fam).toSlicePFunctor)
              ⟨WType.mk (Sum.inr p) c, hw⟩)).mp hn).2 _⟩,
        (fiber_iff P fam _ _).mpr
          ((congrArg (toBase P fam) (child_inr_eq P fam p c hw hn d)).trans
            (toBase_wRestrTree P fam _ _)).symm⟩⟩⟩, rfl⟩

/-- The constructor of the computation rule, on raw trees: the dependent root
shape {lit}`(head t, a')`, with the dependent children the trees of the given
fiber elements and the base children the carried children of {lit}`t`. -/
@[expose] def mkRaw (t : P.W)
    (x : (fam (PFunctor.W.head t)).Obj
      (Sigma.fst : (Σ b, Fiber P fam (PFunctor.W.children t b)) → P.B (PFunctor.W.head t))) :
    (dependent P fam).toPFunctor.W :=
  WType.mk (Sum.inr ⟨PFunctor.W.head t, x.1.1⟩)
    (Sum.elim (fun d ↦ (x.1.2 d).2.1.down.1.1)
      (fun b ↦ ofBase P fam (PFunctor.W.children t b)))

/-- The constructed tree is admissible. -/
theorem wValid_mkRaw (t : P.W)
    (x : (fam (PFunctor.W.head t)).Obj
      (Sigma.fst : (Σ b, Fiber P fam (PFunctor.W.children t b)) → P.B (PFunctor.W.head t))) :
    (dependent P fam).toSlicePFunctor.WValid (mkRaw P fam t x) :=
  ((dependent P fam).toSlicePFunctor.wValid_mk _ _).mpr
    ⟨fun b ↦ by
      cases b with
      | inl d => exact (x.1.2 d).2.1.down.1.2
      | inr b => exact wValid_ofBase P fam _,
    funext fun b ↦ by
      cases b with
      | inl d => exact (x.1.2 d).2.1.down.2.1
      | inr b => exact wIndexRoot_ofBase P fam _⟩

/-- The constructed tree is hereditarily natural: its base child at the
restriction of a dependent direction is the carried base child, which is the
restriction of the corresponding fiber element by that element's fiber
condition. -/
theorem isHereditarilyNatural_mkRaw (t : P.W)
    (x : (fam (PFunctor.W.head t)).Obj
      (Sigma.fst : (Σ b, Fiber P fam (PFunctor.W.children t b)) → P.B (PFunctor.W.head t))) :
    (dependent P fam).IsHereditarilyNatural ⟨mkRaw P fam t x, wValid_mkRaw P fam t x⟩ := by
  refine ((dependent P fam).isHereditarilyNatural_mk_iff_arrow
    (SlicePFunctor.W.dest (F := (dependent P fam).toSlicePFunctor)
      ⟨mkRaw P fam t x, wValid_mkRaw P fam t x⟩)).mpr ⟨?_, ?_⟩
  · rintro ⟨bv, hb⟩
    cases bv with
    | inr _ => exact absurd hb (by decide : (0 : Fin 2) ≠ 1)
    | inl d =>
      refine Subtype.ext ?_
      have h := congrArg (fun z ↦ z.down.1.1) (x.1.2 d).2.2
      exact (congrArg (fun b ↦ ofBase P fam (PFunctor.W.children t b))
        (((fam (PFunctor.W.head t)).compatible_iff _ _ _).mp x.2 d)).symm.trans h.symm
  · intro b
    cases b with
    | inl d => exact (x.1.2 d).2.1.down.2.2
    | inr _ => exact isHereditarilyNatural_ofBase P fam _

/-- The base tree of the constructed tree is {lit}`t`. -/
theorem toBase_mkRaw (t : P.W)
    (x : (fam (PFunctor.W.head t)).Obj
      (Sigma.fst : (Σ b, Fiber P fam (PFunctor.W.children t b)) → P.B (PFunctor.W.head t))) :
    toBase P fam (mkRaw P fam t x) = t := by
  cases t with
  | mk a f => exact congrArg (WType.mk a) (funext fun b ↦ toBase_ofBase P fam (f b))

/-- The constructor inverts the destructor on raw trees. -/
theorem mkRaw_destRaw (w : (dependent P fam).toPFunctor.W)
    (hw : (dependent P fam).toSlicePFunctor.WValid w)
    (hi : (dependent P fam).toSlicePFunctor.wIndexRoot w = 1)
    (hn : (dependent P fam).IsHereditarilyNatural ⟨w, hw⟩) :
    mkRaw P fam (toBase P fam w) (destRaw P fam w hw hi hn) = w := by
  cases w with
  | mk x c =>
    cases x with
    | inl _ => exact absurd hi (by decide : (0 : Fin 2) ≠ 1)
    | inr p =>
      change WType.mk (Sum.inr p) (Sum.elim (fun d ↦ c (Sum.inl d))
        (fun b ↦ ofBase P fam (toBase P fam (c (Sum.inr b))))) = WType.mk (Sum.inr p) c
      refine congrArg (WType.mk (Sum.inr p)) (funext fun b ↦ ?_)
      cases b with
      | inl _ => rfl
      | inr b =>
        exact ofBase_toBase P fam (c (Sum.inr b))
          ((((dependent P fam).toSlicePFunctor.wValid_mk _ _).mp hw).1 _)
          (congrFun (((dependent P fam).toSlicePFunctor.wValid_mk _ _).mp hw).2 _)

/-- Two elements of the family of fibers over the children with equal indices
and equal trees are equal. -/
theorem sigma_fiber_ext {a : P.A} {f : P.B a → P.W} {p q : Σ b, Fiber P fam (f b)}
    (h1 : p.1 = q.1) (h2 : p.2.1.down.1.1 = q.2.1.down.1.1) : p = q := by
  obtain ⟨b, ⟨⟨⟨⟨w, hw⟩, hi, hn⟩⟩, hf⟩⟩ := p
  obtain ⟨b', ⟨⟨⟨⟨w', hw'⟩, hi', hn'⟩⟩, hf'⟩⟩ := q
  cases h1
  cases h2
  rfl

/-- Two values of {lit}`fam a` on the family of fibers with the same shape and
pointwise equal trees are equal. -/
theorem obj_ext {a : P.A} {f : P.B a → P.W} {a' : (fam a).A}
    (v v' : (fam a).B a' → Σ b, Fiber P fam (f b)) (hv : (fam a).Compatible Sigma.fst a' v)
    (hv' : (fam a).Compatible Sigma.fst a' v')
    (h : ∀ d, (v d).2.1.down.1.1 = (v' d).2.1.down.1.1) :
    (⟨⟨a', v⟩, hv⟩ : (fam a).Obj (Sigma.fst : (Σ b, Fiber P fam (f b)) → P.B a)) =
      ⟨⟨a', v'⟩, hv'⟩ :=
  Subtype.ext (Sigma.ext rfl (heq_of_eq (funext fun d ↦ sigma_fiber_ext P fam
    ((((fam a).compatible_iff _ _ _).mp hv d).trans
      (((fam a).compatible_iff _ _ _).mp hv' d).symm) (h d))))

/-- {lit}`obj_ext` across equal families of children. -/
theorem obj_heq {a : P.A} {f f' : P.B a → P.W} (hf : f' = f) {a' : (fam a).A}
    (v : (fam a).B a' → Σ b, Fiber P fam (f' b)) (hv : (fam a).Compatible Sigma.fst a' v)
    (v' : (fam a).B a' → Σ b, Fiber P fam (f b)) (hv' : (fam a).Compatible Sigma.fst a' v')
    (h : ∀ d, (v d).2.1.down.1.1 = (v' d).2.1.down.1.1) :
    (⟨⟨a', v⟩, hv⟩ : (fam a).Obj (Sigma.fst : (Σ b, Fiber P fam (f' b)) → P.B a)) ≍
      (⟨⟨a', v'⟩, hv'⟩ : (fam a).Obj (Sigma.fst : (Σ b, Fiber P fam (f b)) → P.B a)) := by
  subst hf
  exact heq_of_eq (obj_ext P fam v v' hv hv' h)

/-- The computation rule: the fiber over a tree is the value of {lit}`fam` at
the tree's head on the family of fibers over its children, with projection the
index. {lit}`destRaw` and {lit}`mkRaw` are the two directions; the transport of
{lit}`destRaw`'s result along {lit}`fiber_iff` is discharged in the round trips
by {name}`cast_eq` and {name}`cast_heq`. -/
@[expose] def fiberEquiv (t : P.W) :
    Fiber P fam t ≃ (fam (PFunctor.W.head t)).Obj
      (Sigma.fst : (Σ b, Fiber P fam (PFunctor.W.children t b)) → P.B (PFunctor.W.head t)) where
  toFun u := cast (congrArg (fun t ↦ (fam (PFunctor.W.head t)).Obj
      (Sigma.fst : (Σ b, Fiber P fam (PFunctor.W.children t b)) → P.B (PFunctor.W.head t)))
      ((fiber_iff P fam u.1 t).mp u.2))
    (destRaw P fam u.1.down.1.1 u.1.down.1.2 u.1.down.2.1 u.1.down.2.2)
  invFun x := ⟨ULift.up ⟨⟨mkRaw P fam t x, wValid_mkRaw P fam t x⟩, rfl,
      isHereditarilyNatural_mkRaw P fam t x⟩,
    (fiber_iff P fam _ t).mpr (toBase_mkRaw P fam t x)⟩
  left_inv u := by
    obtain ⟨⟨⟨⟨w, hw⟩, hi, hn⟩⟩, hf⟩ := u
    have hb : toBase P fam w = t := (fiber_iff P fam _ t).mp hf
    subst hb
    refine Subtype.ext (congrArg ULift.up (Subtype.ext (Subtype.ext ?_)))
    change mkRaw P fam _ (cast _ (destRaw P fam w hw hi hn)) = w
    rw [cast_eq]
    exact mkRaw_destRaw P fam w hw hi hn
  right_inv x := by
    cases t with
    | mk a f =>
      obtain ⟨⟨a', v⟩, hv⟩ := x
      refine eq_of_heq ((cast_heq _ _).trans ?_)
      refine obj_heq P fam (f' := fun b ↦ toBase P fam (ofBase P fam (f b)))
        (funext fun b ↦ toBase_ofBase P fam (f b)) _ _ v hv ?_
      intro _
      rfl

/-- The computation rule at a constructor: the fiber over {lit}`WType.mk a f` is
the value of {lit}`fam a` on the family of fibers over the children {lit}`f`. -/
@[expose] def fiberMkEquiv (a : P.A) (f : P.B a → P.W) :
    Fiber P fam (WType.mk a f) ≃ (fam a).Obj (Sigma.fst : (Σ b, Fiber P fam (f b)) → P.B a) :=
  fiberEquiv P fam (WType.mk a f)

end Dependent

end PFunctor
