/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.MType.Approx
public import Geb.Mathlib.Data.PFunctor.Univariate.Obj

set_option doc.verso true

/-!
# The M-type of a polynomial functor

The M-type of a polynomial functor {lit}`Q` is built from W-types: an element
is a single tree of a slice W-type whose root has one child for each depth,
the child at depth {lit}`n` a leaf labelled by an observation of depth
{lit}`n` ({name}`Geb.MType.Approx`), such that the observations at successive
depths agree. {lit}`M.dest` and {lit}`M.corec` make {lit}`M Q` a terminal
coalgebra: {lit}`M.dest_corec` is the computation rule, and
{lit}`M.corec_unique` states that the corecursor is the only morphism of
coalgebras into {lit}`M Q`. Equality of elements is proved by
{lit}`M.bisim`, the bisimulation principle.

## Main definitions

* {lit}`bundleSig`, {lit}`Bundle`, {lit}`bundleEquiv` — the slice polynomial
  whose root fibre stores one observation at each depth.
* {lit}`M` — the M-type: the bundles whose observations agree.
* {lit}`M.observe` — the observation of an element at a depth.
* {lit}`M.mk`, {lit}`M.dest`, {lit}`M.head`, {lit}`M.children` — the
  constructor, the destructor, and its two components.
* {lit}`M.destEquiv` — the constructor and destructor as an equivalence.
* {lit}`M.corec` — the corecursor.

## Main statements

* {lit}`M.ext`, {lit}`M.bisim` — elements with equal observations are equal,
  and so are elements related by a bisimulation.
* {lit}`M.dest_mk`, {lit}`M.mk_dest` — the constructor and destructor are
  mutually inverse.
* {lit}`M.dest_corec`, {lit}`M.corec_unique` — terminality among coalgebras.

## Implementation notes

The outer tree has two levels however deep the tree it describes: its root
branches over the depths, so the outer polynomial is not finitary, but its
trees are well founded. No M-type, stream, or coinductive type occurs in the
construction.

The fixed-point structure is computed from the observations. The constructor
prepends one layer to the observations of the children. The destructor reads
the root shape from the observation of depth one and the child at a direction
from the children of the observations at the positive depths, where agreement
gives every positive depth the same root shape. The corecursor assembles the
finite unfoldings of a coalgebra. Uniqueness of the corecursor and the
bisimulation principle are proved by induction on depth over the
observations.

## References

* \[VanDenBergDeMarchi2007\], Section 2, especially Corollary 2.5.

## Tags

M-type, W-type, terminal coalgebra, polynomial functor, corecursion
-/

@[expose] public section

universe u uA uB

namespace Geb.MType

open Depth

variable (Q : PFunctor.{uA, uB})

/-!
## A single W-tree containing every observation
-/

/-- The slice polynomial over {lit}`Option Depth` whose root shape, over
{lit}`none`, has one direction for each depth, lying over {lit}`some n`, and
whose leaf shapes, over {lit}`some n`, are the observations of depth
{lit}`n`. -/
def bundleSig : SlicePFunctor.{max uA uB, max uA uB, max uA uB, max uA uB}
    (Option Depth.{uA, uB}) (Option Depth.{uA, uB}) where
  A := Option (Σ n, Approx Q n)
  B a := match a with
    | none => Depth.{uA, uB}
    | some _ => PEmpty
  r x := match x with
    | ⟨none, n⟩ => some n
    | ⟨some _, e⟩ => nomatch e
  q a := a.map Sigma.fst

/-- The root fibre of the slice W-type of {name}`bundleSig`. -/
abbrev Bundle := { w : (bundleSig Q).W // (bundleSig Q).wIndex w = none }

variable {Q}

/-- A nullary node storing one observation. -/
def leaf (n : Depth.{uA, uB}) (a : Approx Q n) : (bundleSig Q).W :=
  SlicePFunctor.W.mk ⟨⟨some ⟨n, a⟩, PEmpty.elim⟩, funext fun e ↦ nomatch e⟩

/-- The observation a tree at a leaf index stores, transported along the index
equation. -/
def readLeaf (n : Depth.{uA, uB}) (w : (bundleSig Q).W) (h : (bundleSig Q).wIndex w = some n) :
    Approx Q n := by
  rcases w with ⟨w, hw⟩
  cases w with
  | mk a f =>
    cases a with
    | none => cases h
    | some p => exact cast (congrArg (Approx Q) (Option.some.inj h)) p.2

/-- Reading a leaf returns its observation. -/
@[simp] theorem readLeaf_leaf (n : Depth.{uA, uB}) (a : Approx Q n) :
    readLeaf n (leaf n a) rfl = a :=
  rfl

/-- Every tree at a leaf index is the leaf of its observation. -/
theorem leaf_readLeaf (n : Depth.{uA, uB}) (w : (bundleSig Q).W)
    (h : (bundleSig Q).wIndex w = some n) : leaf n (readLeaf n w h) = w := by
  rcases w with ⟨w, hw⟩
  cases w with
  | mk a f =>
    cases a with
    | none => cases h
    | some p =>
      obtain rfl : p.1 = n := Option.some.inj h
      exact Subtype.ext (congrArg (WType.mk (some p)) (funext fun e ↦ nomatch e))

/-- Assemble one observation at each depth under the root. -/
def bundle (x : ∀ n : Depth.{uA, uB}, Approx Q n) : Bundle Q :=
  ⟨SlicePFunctor.W.mk ⟨⟨none, fun n ↦ leaf n (x n)⟩, rfl⟩, rfl⟩

/-- Read the observation at each depth; admissibility supplies each child's
index. -/
def readBundle (w : Bundle Q) (n : Depth.{uA, uB}) : Approx Q n := by
  rcases w with ⟨⟨w, hw⟩, hi⟩
  cases w with
  | mk a f =>
    cases a with
    | none =>
      exact readLeaf n ⟨f n, (((bundleSig Q).wValid_mk none f).mp hw).1 n⟩
        (congrFun (((bundleSig Q).wValid_mk none f).mp hw).2 n)
    | some p => cases hi

/-- Reading after assembling returns every observation. -/
@[simp] theorem readBundle_bundle (x : ∀ n : Depth.{uA, uB}, Approx Q n) :
    readBundle (bundle x) = x :=
  rfl

/-- The slice index forces every root tree to be an assembly. -/
theorem bundle_readBundle (w : Bundle Q) : bundle (readBundle w) = w := by
  rcases w with ⟨⟨w, hw⟩, hi⟩
  cases w with
  | mk a f =>
    cases a with
    | none =>
      refine Subtype.ext (Subtype.ext (congrArg (WType.mk none) (funext fun n ↦ ?_)))
      exact congrArg Subtype.val (leaf_readLeaf n
        ⟨f n, (((bundleSig Q).wValid_mk none f).mp hw).1 n⟩
        (congrFun (((bundleSig Q).wValid_mk none f).mp hw).2 n))
    | some p => cases hi

variable (Q) in
/-- A root tree of {name}`bundleSig` is a family of observations, one at each
depth. -/
def bundleEquiv : Bundle Q ≃ ∀ n : Depth.{uA, uB}, Approx Q n where
  toFun := readBundle
  invFun := bundle
  left_inv := bundle_readBundle
  right_inv := readBundle_bundle

/-!
## The carrier
-/

variable (Q) in
/-- The M-type of {lit}`Q`: the root trees of {name}`bundleSig` whose
observations agree at successive depths. -/
abbrev M : Type (max uA uB) := { w : Bundle Q // Consistent (readBundle w) }

namespace M

/-- The observation of an element at a depth. -/
def observe (w : M Q) : ∀ n : Depth.{uA, uB}, Approx Q n := readBundle w.1

/-- Elements with equal observations at every depth are equal. -/
theorem ext {x y : M Q} (h : ∀ n, x.observe n = y.observe n) : x = y :=
  Subtype.ext ((bundleEquiv Q).injective (funext h))

/-- Elements with equal observations at every positive depth, read through the
computation rule, are equal. -/
theorem ext_succ {x y : M Q}
    (h : ∀ n, succEquiv Q n (x.observe (succ n)) = succEquiv Q n (y.observe (succ n))) :
    x = y :=
  ext (Depth.induction (Subsingleton.elim _ _) fun n _ ↦ (succEquiv Q n).injective (h n))

/-- Successive observations of an element agree, read through the computation
rule at a successor. -/
theorem observe_succ (w : M Q) (n : Depth.{uA, uB}) :
    succEquiv Q n (w.observe (succ n)) =
      Q.map (truncate Q n) (succEquiv Q (succ n) (w.observe (succ (succ n)))) :=
  (congrArg (succEquiv Q n) (w.2 (succ n))).symm.trans (truncate_succ n _)

/-!
## The constructor
-/

/-- The observations of the element with root layer {lit}`x`: the cutoff at
zero, and at a successor the shape of {lit}`x` over the children's
observations of the preceding depth. -/
def mkApprox (x : Q.Obj (M Q)) : ∀ n : Depth.{uA, uB}, Approx Q n :=
  Depth.rec (cutoff Q) fun n _ ↦ (succEquiv Q n).symm (Q.map (fun w ↦ w.observe n) x)

/-- The successor observation of a constructed element exposes its root layer. -/
theorem mkApprox_succ (x : Q.Obj (M Q)) (n : Depth.{uA, uB}) :
    succEquiv Q n (mkApprox x (succ n)) = Q.map (fun w ↦ w.observe n) x := by
  simp only [mkApprox, Depth.rec_succ, Equiv.apply_symm_apply]

/-- Prepending a layer to agreeing observations gives agreeing observations. -/
theorem mkApprox_consistent (x : Q.Obj (M Q)) : Consistent (mkApprox x) := by
  refine Depth.induction rfl fun n _ ↦ (succEquiv Q n).injective ?_
  rw [truncate_succ, mkApprox_succ, mkApprox_succ]
  obtain ⟨a, f⟩ := x
  exact congrArg (Sigma.mk a) (funext fun b ↦ (f b).2 n)

/-- The constructor: the element with root layer {lit}`x`. -/
def mk (x : Q.Obj (M Q)) : M Q := ⟨bundle (mkApprox x), mkApprox_consistent x⟩

/-- The observations of a constructed element. -/
@[simp] theorem observe_mk (x : Q.Obj (M Q)) (n : Depth.{uA, uB}) :
    (mk x).observe n = mkApprox x n :=
  rfl

/-!
## The destructor
-/

/-- The root shape: the shape of the observation of depth one. -/
def head (w : M Q) : Q.A := (succEquiv Q zero (w.observe (succ zero))).1

/-- Every positive-depth observation has the root shape. -/
theorem observe_head (w : M Q) :
    ∀ n : Depth.{uA, uB}, (succEquiv Q n (w.observe (succ n))).1 = w.head :=
  Depth.induction rfl fun n ih ↦ (congrArg Sigma.fst (w.observe_succ n)).symm.trans ih

/-- The observations of the child at a direction of the root shape: the
children of the positive-depth observations at that direction. -/
def childrenApprox (w : M Q) (b : Q.B w.head) (n : Depth.{uA, uB}) : Approx Q n :=
  (succEquiv Q n (w.observe (succ n))).sndOfEq (w.observe_head n) b

/-- The observations of a child agree. -/
theorem childrenApprox_consistent (w : M Q) (b : Q.B w.head) :
    Consistent (w.childrenApprox b) :=
  fun n ↦ (PFunctor.Obj.sndOfEq_congr (w.observe_succ n) (w.observe_head n)
    (w.observe_head (succ n)) b).symm

/-- The child at a direction of the root shape. -/
def children (w : M Q) (b : Q.B w.head) : M Q :=
  ⟨bundle (w.childrenApprox b), w.childrenApprox_consistent b⟩

/-- The destructor: the root shape with the children. -/
def dest (w : M Q) : Q.Obj (M Q) := ⟨w.head, w.children⟩

/-- The destructor describes every positive-depth observation. -/
theorem observe_dest (w : M Q) (n : Depth.{uA, uB}) :
    Q.map (fun t ↦ t.observe n) w.dest = succEquiv Q n (w.observe (succ n)) :=
  PFunctor.Obj.mk_sndOfEq _ (w.observe_head n)

/-- Root layers whose children have equal observations are equal. -/
theorem obj_ext {x y : Q.Obj (M Q)}
    (h : ∀ n, Q.map (fun t ↦ t.observe n) x = Q.map (fun t ↦ t.observe n) y) : x = y := by
  obtain ⟨a, f⟩ := x
  obtain ⟨a', f'⟩ := y
  obtain rfl : a = a' := congrArg Sigma.fst (h zero)
  exact congrArg (Sigma.mk a) (funext fun b ↦ ext fun n ↦
    congrFun (eq_of_heq (Sigma.mk.inj (h n)).2) b)

/-- The destructor inverts the constructor. -/
@[simp] theorem dest_mk (x : Q.Obj (M Q)) : (mk x).dest = x :=
  obj_ext fun n ↦ ((mk x).observe_dest n).trans (mkApprox_succ x n)

/-- The constructor inverts the destructor. -/
@[simp] theorem mk_dest (w : M Q) : mk w.dest = w :=
  ext_succ fun n ↦ (mkApprox_succ w.dest n).trans (w.observe_dest n)

variable (Q) in
/-- The constructor and destructor exhibit {lit}`M Q` as a fixed point of
{lit}`Q`. -/
def destEquiv : M Q ≃ Q.Obj (M Q) where
  toFun := dest
  invFun := mk
  left_inv := mk_dest
  right_inv := dest_mk

/-- The bisimulation principle: elements related by a relation that relates
the children of related elements, over equal root shapes, are equal. The dual
of structural induction on a W-type, proved by induction on depth over the
observations. -/
theorem bisim (R : M Q → M Q → Prop)
    (h : ∀ x y, R x y → ∃ a f g, x.dest = ⟨a, f⟩ ∧ y.dest = ⟨a, g⟩ ∧ ∀ b, R (f b) (g b)) :
    ∀ x y, R x y → x = y := by
  suffices ∀ n x y, R x y → x.observe n = y.observe n from
    fun x y hr ↦ ext fun n ↦ this n x y hr
  refine Depth.induction (fun _ _ _ ↦ Subsingleton.elim _ _) fun n ih x y hr ↦ ?_
  obtain ⟨a, f, g, hx, hy, hfg⟩ := h x y hr
  refine (succEquiv Q n).injective ?_
  rw [← x.observe_dest, ← y.observe_dest, hx, hy]
  exact congrArg (Sigma.mk a) (funext fun b ↦ ih _ _ (hfg b))

/-!
## The corecursor
-/

/-- The corecursor: the element whose observations are the finite unfoldings
of the coalgebra {lit}`step`. -/
def corec {α : Type u} (step : α → Q.Obj α) (a : α) : M Q :=
  ⟨bundle fun n ↦ corecApprox step n a, corecApprox_consistent step a⟩

/-- The observations of a corecursively defined element. -/
@[simp] theorem observe_corec {α : Type u} (step : α → Q.Obj α) (a : α) (n : Depth.{uA, uB}) :
    (corec step a).observe n = corecApprox step n a :=
  rfl

/-- The unfolding equation of the corecursor. -/
theorem corec_eq {α : Type u} (step : α → Q.Obj α) (a : α) :
    corec step a = mk (Q.map (corec step) (step a)) :=
  ext_succ fun n ↦ by
    rw [observe_corec, observe_mk]
    exact (corecApprox_succ step n a).trans (mkApprox_succ (Q.map (corec step) (step a)) n).symm

/-- The computation rule of the corecursor: it is a morphism of coalgebras. -/
@[simp] theorem dest_corec {α : Type u} (step : α → Q.Obj α) (a : α) :
    (corec step a).dest = Q.map (corec step) (step a) :=
  (congrArg dest (corec_eq step a)).trans (dest_mk _)

/-- The corecursor is the only morphism of coalgebras into {lit}`M Q`, by
induction on depth. -/
theorem corec_unique {α : Type u} (step : α → Q.Obj α) (f : α → M Q)
    (hf : ∀ a, (f a).dest = Q.map f (step a)) : f = corec step := by
  suffices h : ∀ n a, (f a).observe n = corecApprox step n a from
    funext fun a ↦ ext fun n ↦ h n a
  refine Depth.induction (fun _ ↦ Subsingleton.elim _ _) fun n ih a ↦ ?_
  refine (succEquiv Q n).injective (((f a).observe_dest n).symm.trans ?_)
  have h : Q.map (fun t ↦ t.observe n) (f a).dest = Q.map (fun x ↦ (f x).observe n) (step a) :=
    congrArg (Q.map fun t ↦ t.observe n) (hf a)
  exact h.trans
    ((congrArg (fun g ↦ Q.map g (step a)) (funext ih)).trans (corecApprox_succ step n a).symm)

end M

end Geb.MType
