/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.MType.Basic
public import Mathlib.Data.PFunctor.Univariate.M
public import Mathlib.Logic.Equiv.Functor
public import Geb.Mathlib.Logic.Equiv.Basic

set_option doc.verso true in
/-!
# The M-type constructed from W-types is mathlib's M-type

mathlib's {name}`PFunctor.M` is the structure {name}`PFunctor.MIntl` of
agreeing approximations, where the approximation of depth {lit}`n` is an
element of the inductive family {name}`PFunctor.Approx.CofixA` indexed by
{name}`Nat`. The observations of depth {lit}`n` are the same data indexed by
the W-type of depths: {lit}`approxEquiv` identifies them by dependent
elimination on depth, carrying truncation to mathlib's
{name}`PFunctor.Approx.truncate` and agreement to the inductive relation
{name}`PFunctor.Approx.Agree`. Reindexing the families along the equivalence
of depths with {name}`Nat` then identifies the carriers, and the equivalence
{lit}`mEquiv` carries the constructor and the corecursor to mathlib's.

## Main definitions

* {lit}`cofixLayerEquiv` — one layer of mathlib's approximations.
* {lit}`approxEquiv` — observations are mathlib's approximations.
* {lit}`mEquiv` — the M-type is mathlib's M-type.

## Main statements

* {lit}`approxEquiv_truncate`, {lit}`agree_iff` — truncation and agreement
  correspond.
* {lit}`approx_mEquiv` — the equivalence preserves every observation.
* {lit}`mEquiv_mk`, {lit}`mEquiv_corec` — the equivalence preserves the
  constructor and the corecursor.

## Implementation notes

The comparison is stated through {name}`PFunctor.M.mk` and
{name}`PFunctor.M.corec`, not through mathlib's destructor
{name}`PFunctor.M.dest`, whose definition depends on {name}`Classical.choice`.
That the equivalence carries the destructor to mathlib's follows from
{lit}`mEquiv_mk`, {name}`Geb.MType.M.mk_dest` and {name}`PFunctor.M.dest_mk`,
each destructor being inverse to its constructor; it is not stated here, so
that the module stays free of {name}`Classical.choice`.

## References

* \[VanDenBergDeMarchi2007\], Section 2, especially Corollary 2.5.

## Tags

M-type, W-type, finite approximation, equivalence, PFunctor
-/
set_option doc.verso true

@[expose] public section

universe u uA uB

namespace Geb.MType

open PFunctor.Approx (CofixA)
open Depth

variable {Q : PFunctor.{uA, uB}}

variable (Q) in
/-- A positive-depth approximation of mathlib's is a shape with an
approximation of the preceding depth at each direction. -/
def cofixLayerEquiv (n : ℕ) : CofixA Q (n + 1) ≃ Q.Obj (CofixA Q n) where
  toFun x := ⟨PFunctor.Approx.head' x, PFunctor.Approx.children' x⟩
  invFun x := .intro x.1 x.2
  left_inv x := by cases x; rfl
  right_inv _ := rfl

variable (Q) in
/-- Observations are mathlib's approximations, by dependent elimination on
depth. -/
def approxEquiv : ∀ n : Depth.{uA, uB}, Approx Q n ≃ CofixA Q (toNat n) :=
  Depth.rec (motive := fun n ↦ Approx Q n ≃ CofixA Q (toNat n))
    ((zeroEquiv Q).trans
      { toFun := fun _ ↦ .continue
        invFun := fun _ ↦ ()
        left_inv := fun _ ↦ rfl
        right_inv := fun x ↦ by cases x; rfl })
    fun n e ↦ (succEquiv Q n).trans ((Functor.mapEquiv Q.Obj e).trans
      (cofixLayerEquiv Q (toNat n)).symm)

/-- Comparing a successor observation commutes with reading its outer layer. -/
theorem approxEquiv_succ (n : Depth.{uA, uB}) (x : Approx Q (succ n)) :
    cofixLayerEquiv Q (toNat n) (approxEquiv Q (succ n) x) =
      Q.map (approxEquiv Q n) (succEquiv Q n x) := by
  unfold approxEquiv
  rw [Depth.rec_succ]
  exact (cofixLayerEquiv Q _).apply_symm_apply _

/-- mathlib's truncation keeps the outer layer and truncates each child. -/
theorem cofixLayerEquiv_truncate (n : ℕ) (x : CofixA Q (n + 2)) :
    cofixLayerEquiv Q n (PFunctor.Approx.truncate x) =
      Q.map PFunctor.Approx.truncate (cofixLayerEquiv Q (n + 1) x) := by
  cases x
  rfl

/-- Truncation of observations is mathlib's truncation. -/
theorem approxEquiv_truncate : ∀ (n : Depth.{uA, uB}) (x : Approx Q (succ n)),
    approxEquiv Q n (truncate Q n x) = PFunctor.Approx.truncate (approxEquiv Q (succ n) x) :=
  Depth.induction (fun _ ↦ @Subsingleton.elim (CofixA Q 0) _ _ _) fun n ih x ↦ by
    apply (cofixLayerEquiv Q (toNat n)).injective
    refine (approxEquiv_succ n _).trans
      ((congrArg (Q.map (approxEquiv Q n)) (truncate_succ n x)).trans ?_)
    refine Eq.trans ?_ (cofixLayerEquiv_truncate (toNat n) (approxEquiv Q (succ (succ n)) x)).symm
    refine Eq.trans ?_
      (congrArg (Q.map PFunctor.Approx.truncate) (approxEquiv_succ (succ n) x)).symm
    cases succEquiv Q (succ n) x with
    | mk a f => exact congrArg (Sigma.mk a) (funext fun b ↦ ih (f b))

/-- An approximation of mathlib's agrees with its truncation. -/
theorem agree_truncate : ∀ (n : ℕ) (x : CofixA Q (n + 1)),
    PFunctor.Approx.Agree (PFunctor.Approx.truncate x) x :=
  Nat.rec (fun _ ↦ PFunctor.Approx.agree_trivial) fun _ ih x ↦ by
    cases x with
    | intro a f => exact .intro _ _ fun i ↦ ih (f i)

/-- Agreement of observations is mathlib's inductive agreement. -/
theorem agree_iff {n : Depth.{uA, uB}} (x : Approx Q n) (y : Approx Q (succ n)) :
    Agree x y ↔ PFunctor.Approx.Agree (approxEquiv Q n x) (approxEquiv Q (succ n) y) := by
  constructor
  · intro h
    have h' := (approxEquiv_truncate n y).symm.trans (congrArg (approxEquiv Q n) h)
    exact h' ▸ agree_truncate (toNat n) (approxEquiv Q (succ n) y)
  · intro h
    apply (approxEquiv Q n).injective
    exact (approxEquiv_truncate n y).trans (PFunctor.Approx.truncate_eq_of_agree _ _ h)

variable (Q) in
/-- Families of observations are families of mathlib's approximations. -/
def familyEquiv : (∀ n : Depth.{uA, uB}, Approx Q n) ≃ ∀ k, CofixA Q k :=
  (Equiv.piCongrRight (approxEquiv Q)).trans (Equiv.piCongrLeftC (CofixA Q) equivNat)

/-- Agreement of families corresponds to mathlib's {name}`PFunctor.Approx.AllAgree`. -/
theorem consistent_familyEquiv_symm (y : ∀ k, CofixA Q k) :
    Consistent ((familyEquiv Q).symm y) ↔ PFunctor.Approx.AllAgree y := by
  have hstep (n : Depth.{uA, uB}) :
      Agree ((familyEquiv Q).symm y n) ((familyEquiv Q).symm y (succ n)) ↔
        PFunctor.Approx.Agree (y (toNat n)) (y (toNat n + 1)) := by
    change Agree ((approxEquiv Q n).symm _) ((approxEquiv Q (succ n)).symm _) ↔ _
    rw [agree_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  constructor
  · intro h k
    obtain ⟨n, rfl⟩ := equivNat.surjective k
    exact (hstep n).mp (h n)
  · exact fun h n ↦ (hstep n).mpr (h (toNat n))

variable (Q) in
/-- Agreeing families of observations are mathlib's M-type. -/
def consistentFamilyEquiv :
    { x : ∀ n : Depth.{uA, uB}, Approx Q n // Consistent x } ≃ Q.M where
  toFun x := ⟨familyEquiv Q x.1, (consistent_familyEquiv_symm _).mp
    (((familyEquiv Q).symm_apply_apply x.1).symm ▸ x.2)⟩
  invFun y := ⟨(familyEquiv Q).symm y.approx, (consistent_familyEquiv_symm _).mpr y.consistent⟩
  left_inv x := Subtype.ext ((familyEquiv Q).symm_apply_apply x.1)
  right_inv y := PFunctor.M.ext' Q _ _ fun n ↦
    congrFun ((familyEquiv Q).apply_symm_apply y.approx) n

variable (Q) in
/-- Forgetting the outer W-tree identifies the M-type with agreeing families. -/
def consistentEquiv : M Q ≃ { x : ∀ n : Depth.{uA, uB}, Approx Q n // Consistent x } where
  toFun w := ⟨readBundle w.1, w.2⟩
  invFun x := ⟨bundle x.1, x.2⟩
  left_inv w := Subtype.ext (bundle_readBundle w.1)
  right_inv _ := rfl

variable (Q) in
/-- The M-type constructed from W-types is mathlib's M-type. -/
def mEquiv : M Q ≃ Q.M := (consistentEquiv Q).trans (consistentFamilyEquiv Q)

/-- The equivalence preserves the observation at every depth. -/
theorem approx_mEquiv (w : M Q) (n : Depth.{uA, uB}) :
    (mEquiv Q w).approx (toNat n) = approxEquiv Q n (w.observe n) :=
  ((approxEquiv Q n).apply_symm_apply _).symm.trans
    (congrArg (approxEquiv Q n) (congrFun ((familyEquiv Q).symm_apply_apply w.observe) n))

/-- An element is sent to the element of mathlib's M-type whose approximations
are its observations. -/
theorem mEquiv_eq_of_approx {w : M Q} {y : Q.M}
    (h : ∀ n : Depth.{uA, uB}, approxEquiv Q n (w.observe n) = y.approx (toNat n)) :
    mEquiv Q w = y := by
  refine PFunctor.M.ext' Q _ _ fun k ↦ ?_
  obtain ⟨n, rfl⟩ := equivNat.surjective k
  exact (approx_mEquiv w n).trans (h n)

/-- One layer of mathlib's finite unfolding is the coalgebra's layer with the
finite unfolding applied to its children. -/
theorem cofixLayerEquiv_sCorec {α : Type u} (f : α → Q.Obj α) (n : ℕ) (a : α) :
    cofixLayerEquiv Q n (PFunctor.Approx.sCorec f a (n + 1)) =
      Q.map (fun b ↦ PFunctor.Approx.sCorec f b n) (f a) :=
  rfl

/-- The finite unfoldings of a coalgebra are mathlib's. -/
theorem approxEquiv_corecApprox {α : Type u} (f : α → Q.Obj α) :
    ∀ (n : Depth.{uA, uB}) (a : α),
      approxEquiv Q n (corecApprox f n a) = PFunctor.Approx.sCorec f a (toNat n) :=
  Depth.induction (fun _ ↦ @Subsingleton.elim (CofixA Q 0) _ _ _) fun n ih a ↦ by
    apply (cofixLayerEquiv Q (toNat n)).injective
    refine (approxEquiv_succ n _).trans
      ((congrArg (Q.map (approxEquiv Q n)) (corecApprox_succ f n a)).trans ?_)
    refine Eq.trans ?_ (cofixLayerEquiv_sCorec f (toNat n) a).symm
    cases f a with
    | mk s g => exact congrArg (Sigma.mk s) (funext fun b ↦ ih (g b))

/-- The equivalence carries the corecursor to mathlib's. -/
theorem mEquiv_corec {α : Type u} (f : α → Q.Obj α) (a : α) :
    mEquiv Q (M.corec f a) = PFunctor.M.corec f a :=
  mEquiv_eq_of_approx fun n ↦ approxEquiv_corecApprox f n a

/-- The equivalence carries the constructor to mathlib's. -/
theorem mEquiv_mk (x : Q.Obj (M Q)) :
    mEquiv Q (M.mk x) = PFunctor.M.mk (Q.map (mEquiv Q) x) :=
  mEquiv_eq_of_approx <| Depth.induction (@Subsingleton.elim (CofixA Q 0) _ _ _) fun n _ ↦ by
    apply (cofixLayerEquiv Q (toNat n)).injective
    refine (approxEquiv_succ n _).trans
      ((congrArg (Q.map (approxEquiv Q n)) (M.mkApprox_succ x n)).trans ?_)
    obtain ⟨a, f⟩ := x
    exact congrArg (Sigma.mk a) (funext fun b ↦ (approx_mEquiv (f b) n).symm)

end Geb.MType
