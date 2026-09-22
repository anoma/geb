/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.BitStream
public import Geb.Mathlib.Data.PFunctor.Presheaf.Arrow

set_option doc.verso true

/-!
# Bitstreams constructed using W-types

Depths are an ordinary W-type. Finite observations form a dependent family over
that W-type, obtained from {name}`PFunctor.dependent` on the walking arrow.
The restriction map sends an observation to its depth. Its fibre computation
rule gives one observation at zero and an optional bit with a smaller
observation at a successor. A second, slice W-type packages all depths into
one tree. Requiring adjacent observations to agree gives a carrier equivalent
to the M-type of {name}`Geb.BitStream.sig`.

## Main definitions

* {lit}`Depth` is the W-type of zero and successor.
* {lit}`Approx` is the dependent presheaf W-family of bounded observations.
* {lit}`depthRec` is dependent elimination on the W-type of depths.
* {lit}`truncate` and {lit}`Agree` replace truncation and inductive agreement.
* {lit}`Bundle` is a slice W-tree with one observation for each depth.
* {lit}`Stream` requires those observations to agree.
* {lit}`mEquiv` and {lit}`seqEquiv` identify it with the existing M-type and sequences.
* {lit}`mk`, {lit}`dest`, and {lit}`corec` operate directly on these W-trees.

The comparison with {name}`Geb.BitStream.Prefix` is {lit}`prefixEquiv`;
the comparison with {name}`Geb.BitStream.Observations` is {lit}`observationsEquiv`.
The old path type is represented by the original bitstring W-type through
{lit}`pathEquiv`. At a successor depth, {lit}`succEquiv` supplies both the
constructor and the head/child decomposition of an approximation.

## Implementation notes

The construction uses ordinary sums, dependent functions, and equality in
addition to W-types, as do the slice and presheaf W-types themselves. An
infinite stream is not represented by an infinite branch of a W-tree. The
outer root instead has infinitely many children, each labelled by a finite
observation. The labels contain no M-types or streams, so this construction
does not assume the object it is constructing.

Recursion on the existing natural numbers, lists, or mathlib's bounded
approximation datatype occurs only in the comparisons. The new recursive
carriers and their operations use W-types, their elimination rules, and the
existing slice and presheaf refinements. These refinements are built over ordinary
W-types; a new primitive dependent inductive type is not needed here.

The general existence result is Corollary 2.5 of
\[VanDenBergDeMarchi2007\]: a locally cartesian closed pretopos with
W-types has M-types. That result supplies context for the construction;
this file proves the concrete bitstream equivalences, not that categorical
theorem. It does not establish why mathlib chose its direct datatype.

## References

* \[VanDenBergDeMarchi2007\], Section 2, especially Corollary 2.5.

## Tags

W-type, M-type, dependent type, presheaf, bitstream, finite approximation
-/

@[expose] public section

namespace Geb.BitStream.WConstruction

open PFunctor PFunctor.Dependent

/-!
## Depth and dependent elimination

A depth is a nullary zero node or a unary successor node. Folding it to
{name}`Nat` and unfolding {name}`Nat` back proves the comparison. The
dependent eliminator folds into a pair consisting of the reconstructed
depth and its value, then transports the value along the proof that the
reconstructed depth is the original one. This uses the computational
{name}`WType.elim`; its index proof uses {name}`WType.rec` into propositions.
-/

/-- The polynomial of natural-number depths: zero is nullary and successor is unary. -/
def depthSig : PFunctor.{0, 0} where
  A := Bool
  B b := if b then Unit else Empty

/-- Observation depths, represented by well-founded unary trees. -/
abbrev Depth := depthSig.W

/-- The depth with no observable layer. -/
def zero : Depth := WType.mk false Empty.elim

/-- One additional observable layer. -/
def succ (n : Depth) : Depth := WType.mk true fun _ ↦ n

/-- Dependent induction on depths uses the proposition-valued W-recursor. -/
theorem depthInduction {motive : Depth → Prop} (hz : motive zero)
    (hs : ∀ n, motive n → motive (succ n)) : ∀ n, motive n :=
  WType.rec fun b f ih ↦ by
    cases b with
    | false =>
      have hf : f = Empty.elim := funext fun i ↦ nomatch i
      subst f
      exact hz
    | true => exact hs (f ()) (ih ())

/-- The computational fold retains the reconstructed depth beside its dependent value. -/
def depthData {motive : Depth → Type*} (hz : motive zero)
    (hs : ∀ n, motive n → motive (succ n)) : Depth → Sigma motive :=
  WType.elim _ fun x ↦ match x with
    | ⟨false, _⟩ => ⟨zero, hz⟩
    | ⟨true, f⟩ => ⟨succ (f ()).1, hs (f ()).1 (f ()).2⟩

/-- The first component of the dependent fold reconstructs its input. -/
theorem depthData_index {motive : Depth → Type*} (hz : motive zero)
    (hs : ∀ n, motive n → motive (succ n)) : ∀ n, (depthData hz hs n).1 = n :=
  depthInduction rfl fun _ ih ↦ congrArg succ ih

/-- Computational dependent elimination uses {name}`WType.elim` on the total
space, followed by transport along the reconstructed index. -/
def depthRec {motive : Depth → Type*} (hz : motive zero)
    (hs : ∀ n, motive n → motive (succ n)) (n : Depth) : motive n :=
  cast (congrArg motive (depthData_index hz hs n)) (depthData hz hs n).2

/-- The zero computation rule for dependent depth elimination. -/
@[simp] theorem depthRec_zero {motive : Depth → Type*} (hz : motive zero)
    (hs : ∀ n, motive n → motive (succ n)) : depthRec hz hs zero = hz := rfl

/-- The successor computation rule for dependent depth elimination. -/
@[simp] theorem depthRec_succ {motive : Depth → Type*} (hz : motive zero)
    (hs : ∀ n, motive n → motive (succ n)) (n : Depth) :
    depthRec hz hs (succ n) = hs n (depthRec hz hs n) := by
  unfold depthRec
  change cast _ (hs (depthData hz hs n).1 (depthData hz hs n).2) = _
  have transport (m n : Depth) (h : m = n) (v : motive m) :
      cast (congrArg motive (congrArg succ h)) (hs m v) =
        hs n (cast (congrArg motive h) v) := by
    cases h
    rfl
  exact transport _ _ (depthData_index hz hs n) _

/-- Read the natural number represented by a depth tree. Used only for comparison. -/
def toNat : Depth → ℕ := WType.elim ℕ fun x ↦ match x with
  | ⟨false, _⟩ => 0
  | ⟨true, f⟩ => f () + 1

/-- Encode a natural number as a depth tree. -/
def ofNat : ℕ → Depth := Nat.rec zero fun _ ↦ succ

/-- The W-type of depths is equivalent to the existing natural numbers. -/
def depthEquiv : Depth ≃ ℕ where
  toFun := toNat
  invFun := ofNat
  left_inv := depthInduction rfl fun _ ih ↦ congrArg succ ih
  right_inv := Nat.rec rfl fun _ ih ↦ congrArg Nat.succ ih

/-!
## Finite observations as a presheaf W-family

At the base object's zero shape, the dependent polynomial has one nullary
shape: cutoff. At its successor shape, it has the original three bitstring
shapes: termination, zero-bit, and one-bit. Each bit's child lies over the
predecessor depth. The walking-arrow restriction therefore records depth,
and its fibre equation reads {lit}`Approx zero ≃ Unit` and
{lit}`Approx (succ n) ≃ Option (Bool × Approx n)`.

Cutoff carries no information about whether the stream will terminate next.
Termination is visible only after another layer has been observed. Thus
the bounded-list representation can use the empty list at depth zero for
cutoff, while the empty list at a positive depth records termination.
-/

/-- At zero there is only the cutoff observation. At a successor there is
termination or a bit whose dependent child lies over the predecessor depth. -/
def family : ∀ b : depthSig.A, SliceDomPFunctor.{0, 0, 0} (depthSig.B b)
  | false => ⟨⟨Unit, fun _ ↦ Empty⟩, fun x ↦ nomatch x.2⟩
  | true => ⟨sig, fun _ ↦ ()⟩

/-- The walking-arrow polynomial whose base is depth and whose total space is
depth-indexed finite observations. -/
def approximationPresheaf : PresheafPFunctor (Fin 2) (Fin 2) := depthSig.dependent family

/-- An observation at a W-type depth is a fibre of the presheaf W-type's restriction. -/
abbrev Approx (n : Depth) := Fiber depthSig family n

/-- At zero the dependent polynomial has a single nullary shape. -/
def zeroEquiv : Approx zero ≃ Unit :=
  (fiberMkEquiv depthSig family false Empty.elim).trans
    { toFun := fun _ ↦ ()
      invFun := fun _ ↦ ⟨⟨(), Empty.elim⟩, funext fun i ↦ nomatch i⟩
      left_inv := fun ⟨⟨(), _⟩, _⟩ ↦ Subtype.ext
        (congrArg (Sigma.mk ())
          (funext fun i ↦ nomatch i))
      right_inv := fun _ ↦ rfl }

/-- Removing the redundant singleton index from a successor fibre gives an
optional bit and its observation at the preceding depth. -/
def succEquiv (n : Depth) : Approx (succ n) ≃ Layer (Approx n) :=
  (fiberMkEquiv depthSig family true (fun _ ↦ n)).trans
    (Equiv.trans
      { toFun := fun x ↦ ⟨x.1.1, fun b ↦ (x.1.2 b).2⟩
        invFun := fun x ↦ ⟨⟨x.1, fun b ↦ ⟨(), x.2 b⟩⟩, rfl⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl } (layerEquiv (Approx n)))

/-- The unique observation before any layer has been read. -/
def cutoff : Approx zero := zeroEquiv.symm ()

/-- Comparison with mathlib's directly defined bounded trees. All recursion
in this equivalence is elimination on the W-type of depths. -/
def approxEquiv : ∀ n : Depth, Approx n ≃ PFunctor.Approx.CofixA sig (toNat n) :=
  depthRec
    (zeroEquiv.trans
      { toFun := fun _ ↦ .continue
        invFun := fun _ ↦ ()
        left_inv := fun _ ↦ rfl
        right_inv := fun x ↦ by cases x; rfl })
    (fun n e ↦ (succEquiv n).trans
      ((Equiv.optionCongr ((Equiv.refl Bool).prodCongr e)).trans
        (cofixLayerEquiv (toNat n)).symm))

/-- The presheaf W-fibre also recovers the bounded prefixes of the first development. -/
def prefixEquiv (n : Depth) : Approx n ≃ Prefix (toNat n) :=
  (approxEquiv n).trans (Geb.BitStream.approxEquiv (toNat n))

/-- Comparing a successor observation commutes with reading its outer layer. -/
theorem approxEquiv_succ (n : Depth) (x : Approx (succ n)) :
    cofixLayerEquiv (toNat n) (approxEquiv (succ n) x) =
      (succEquiv n x).map (Prod.map id (approxEquiv n)) := by
  unfold approxEquiv
  rw [depthRec_succ]
  exact (cofixLayerEquiv _).apply_symm_apply _

/-!
## Truncation, agreement, and finite unfolding

Truncation always returns cutoff at zero. At a successor it preserves the
outer shape and truncates the optional child. Agreement is consequently
just equality after truncation. Finite corecursion has the same recursion
on depth: cutoff at zero, and one step of the supplied coalgebra at a
successor. No potentially infinite recursive call is made.
-/

/-- Forget the deepest layer by dependent elimination on its W-type depth. -/
def truncate : ∀ n : Depth, Approx (succ n) → Approx n :=
  depthRec (fun _ ↦ cutoff) fun n rec x ↦
    (succEquiv n).symm ((succEquiv (succ n) x).map (Prod.map id rec))

/-- The zero fibre contains only the cutoff. -/
theorem eq_cutoff (x : Approx zero) : x = cutoff :=
  zeroEquiv.injective rfl

/-- Truncation at zero always returns the cutoff. -/
@[simp] theorem truncate_zero (x : Approx (succ zero)) : truncate zero x = cutoff := rfl

/-- Truncation preserves the outer layer and truncates its optional child. -/
theorem truncate_succ (n : Depth) (x : Approx (succ (succ n))) :
    succEquiv n (truncate (succ n) x) =
      (succEquiv (succ n) x).map (Prod.map id (truncate n)) := by
  simp only [truncate, depthRec_succ, Equiv.apply_symm_apply]

/-- Mathlib's truncation has the same one-layer computation rule. -/
theorem cofixLayerEquiv_truncate (n : ℕ) (x : PFunctor.Approx.CofixA sig (n + 2)) :
    cofixLayerEquiv n (PFunctor.Approx.truncate x) =
      (cofixLayerEquiv (n + 1) x).map (Prod.map id PFunctor.Approx.truncate) := by
  cases x with | intro a f => cases a <;> rfl

/-- W-defined truncation agrees with the truncation used by mathlib's M-type. -/
theorem approxEquiv_truncate : ∀ (n : Depth) (x : Approx (succ n)),
    approxEquiv n (truncate n x) = PFunctor.Approx.truncate (approxEquiv (succ n) x) :=
  depthInduction (fun _ ↦ @Subsingleton.elim (PFunctor.Approx.CofixA sig 0) _ _ _)
    fun n ih x ↦ by
    apply (cofixLayerEquiv (toNat n)).injective
    refine (approxEquiv_succ n _).trans ((congrArg
      (fun y ↦ y.map (Prod.map id (approxEquiv n))) (truncate_succ n x)).trans ?_)
    refine Eq.trans ?_ (cofixLayerEquiv_truncate (toNat n)
      (approxEquiv (succ (succ n)) x)).symm
    refine Eq.trans ?_ (congrArg
      (fun y ↦ y.map (Prod.map id PFunctor.Approx.truncate))
      (approxEquiv_succ (succ n) x)).symm
    cases succEquiv (succ n) x with
    | none => rfl
    | some p => exact congrArg (fun t ↦ some (p.1, t)) (ih p.2)

/-- Agreement is equality after forgetting the deepest observable layer. -/
def Agree {n : Depth} (x : Approx n) (y : Approx (succ n)) : Prop := truncate n y = x

/-- The equality-based W formulation recovers mathlib's inductive agreement relation. -/
theorem agree_iff {n : Depth} (x : Approx n) (y : Approx (succ n)) :
    Agree x y ↔ PFunctor.Approx.Agree (approxEquiv n x) (approxEquiv (succ n) y) := by
  constructor
  · intro h
    have h' := (approxEquiv_truncate n y).symm.trans (congrArg (approxEquiv n) h)
    exact h' ▸ Geb.BitStream.agree_truncate (toNat n) (approxEquiv (succ n) y)
  · intro h
    apply (approxEquiv n).injective
    exact (approxEquiv_truncate n y).trans (PFunctor.Approx.truncate_eq_of_agree _ _ h)

/-- A coherent family has compatible observations at every W-type depth. -/
def Consistent (x : ∀ n, Approx n) : Prop := ∀ n, Agree (x n) (x (succ n))

/-- Finite unfolding of a coalgebra by dependent W-elimination. -/
def corecApprox {α : Type*} (step : α → Layer α) : ∀ n : Depth, α → Approx n :=
  depthRec (fun _ ↦ cutoff) fun n rec a ↦
    (succEquiv n).symm ((step a).map (Prod.map id rec))

/-- Successor unfolding reads one layer and recursively observes its child. -/
theorem corecApprox_succ {α : Type*} (step : α → Layer α) (n : Depth) (a : α) :
    succEquiv n (corecApprox step (succ n) a) =
      (step a).map (Prod.map id (corecApprox step n)) := by
  simp only [corecApprox, depthRec_succ, Equiv.apply_symm_apply]

/-- Finite unfoldings are compatible, proved by induction on their W-type depth. -/
theorem corecApprox_consistent {α : Type*} (step : α → Layer α) (a : α) :
    Consistent (fun n ↦ corecApprox step n a) := by
  suffices ∀ n a, truncate n (corecApprox step (succ n) a) = corecApprox step n a from
    fun n ↦ this n a
  refine depthInduction (fun _ ↦ rfl) fun n ih a ↦ ?_
  apply (succEquiv n).injective
  rw [truncate_succ, corecApprox_succ, corecApprox_succ]
  cases step a with
  | none => rfl
  | some p => exact congrArg (fun t ↦ some (p.1, t)) (ih p.2)

/-- Reindex dependent functions along the depth equivalence, using equality
transport rather than a choice-based domain-congruence combinator. -/
def depthPiEquiv (P : ℕ → Type*) : (∀ n : Depth, P (toNat n)) ≃ (∀ k, P k) where
  toFun f k := cast (congrArg P (depthEquiv.apply_symm_apply k)) (f (ofNat k))
  invFun g n := g (toNat n)
  left_inv f := funext fun n ↦ eq_of_heq ((cast_heq _ _).trans
    (congr_arg_heq f (depthEquiv.symm_apply_apply n)))
  right_inv g := funext fun k ↦ eq_of_heq ((cast_heq _ _).trans
    (congr_arg_heq g (depthEquiv.apply_symm_apply k)))

/-- All W-indexed observations correspond to all of mathlib's approximations. -/
def familyEquiv : (∀ n : Depth, Approx n) ≃ (∀ k, PFunctor.Approx.CofixA sig k) :=
  (Equiv.piCongrRight approxEquiv).trans (depthPiEquiv (PFunctor.Approx.CofixA sig))

/-- Reindexing and comparing the finite trees preserves compatibility. -/
theorem consistent_familyEquiv_symm (y : ∀ k, PFunctor.Approx.CofixA sig k) :
    Consistent (familyEquiv.symm y) ↔ PFunctor.Approx.AllAgree y := by
  have hstep (n : Depth) :
      Agree (familyEquiv.symm y n) (familyEquiv.symm y (succ n)) ↔
        PFunctor.Approx.Agree (y (toNat n)) (y (toNat n + 1)) := by
    change Agree ((approxEquiv n).symm _) ((approxEquiv (succ n)).symm _) ↔ _
    rw [agree_iff, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  constructor
  · intro h k
    obtain ⟨n, rfl⟩ := depthEquiv.surjective k
    exact (hstep n).mp (h n)
  · exact fun h n ↦ (hstep n).mpr (h (toNat n))

/-- Compatible W-indexed observations are already a presentation of the M-type.
The next construction will package the entire family as a single slice W-tree. -/
def coherentFamilyEquiv : {x : ∀ n, Approx n // Consistent x} ≃ sig.M where
  toFun x := ⟨familyEquiv x.1, (consistent_familyEquiv_symm _).mp
    ((familyEquiv.symm_apply_apply x.1).symm ▸ x.2)⟩
  invFun y := ⟨familyEquiv.symm y.approx, (consistent_familyEquiv_symm _).mpr y.consistent⟩
  left_inv x := Subtype.ext (familyEquiv.symm_apply_apply x.1)
  right_inv y := PFunctor.M.ext' sig _ _
    (fun n ↦ congrFun (familyEquiv.apply_symm_apply y.approx) n)

/-!
## A single W-tree containing every observation

The root has one direction for each W-type depth. Its child at depth
{lit}`n` is a nullary node labelled by an {lit}`Approx n`. The slice index
enforces that label's depth. The outer tree has just two levels, even when
the bitstream it describes is infinite. Well-foundedness rules out infinite
branches; it permits infinitely many children at one node. Here the root's
direction type is {name}`Depth`, equivalent to {name}`Nat` by
{name}`depthEquiv`, so this outer polynomial is not finitary. The depth and
observation polynomials still have only finite arities.

This infinite branching packages a dependent product into a single W-tree.
The choice belongs to this encoding: {name}`coherentFamilyEquiv` already
describes the M-type using a compatible family of observations without an
outer tree. In contrast, the cofree comonad discussed in
{name}`Geb.BitStream.Observations` intrinsically fails to preserve filtered
colimits, regardless of its presentation.
-/

/-- A root at index {lit}`none` has one child at each {lit}`some n`.
A leaf at {lit}`some n` stores a finite observation at depth {lit}`n`.

As an endofunctor {lit}`H` on families indexed by {lit}`Option Depth`, this is
{lit}`H Y none ≃ (∀ n : Depth, Y (some n))` and
{lit}`H Y (some n) ≃ Approx n`. The slice W-type, with its index map and
constructor, is the initial algebra of this infinitary polynomial. Its
{lit}`some n` fibre stores one observation; its {lit}`none` fibre stores
their dependent product. Compatibility is imposed separately below. -/
def bundleSig : SlicePFunctor (Option Depth) (Option Depth) where
  A := Option (Σ n, Approx n)
  B a := match a with
    | none => Depth
    | some _ => Empty
  r x := match x with
    | ⟨none, n⟩ => some n
    | ⟨some _, e⟩ => nomatch e
  q a := a.map Sigma.fst

/-- The root fibre of the slice W-type containing all finite observations. -/
abbrev Bundle := {w : bundleSig.W // bundleSig.wIndex w = none}

/-- Store one observation in a nullary slice W-node. -/
def leaf (n : Depth) (a : Approx n) : bundleSig.W :=
  SlicePFunctor.W.mk ⟨⟨some ⟨n, a⟩, Empty.elim⟩, funext fun e ↦ nomatch e⟩

/-- Eliminate a leaf node, transporting its label along the slice index equation. -/
def readLeaf (n : Depth) (w : bundleSig.W) (h : bundleSig.wIndex w = some n) :
    Approx n := by
  rcases w with ⟨w, hw⟩
  cases w with
  | mk a f =>
    cases a with
    | none => cases h
    | some p => exact cast (congrArg Approx (Option.some.inj h)) p.2

/-- Reading a freshly constructed leaf returns its stored observation. -/
@[simp] theorem readLeaf_leaf (n : Depth) (a : Approx n) : readLeaf n (leaf n a) rfl = a :=
  rfl

/-- Every tree at a leaf index is exactly the leaf storing its observed value. -/
theorem leaf_readLeaf (n : Depth) (w : bundleSig.W) (h : bundleSig.wIndex w = some n) :
    leaf n (readLeaf n w h) = w := by
  rcases w with ⟨w, hw⟩
  cases w with
  | mk a f =>
    cases a with
    | none => cases h
    | some p =>
      have hp : p.1 = n := Option.some.inj h
      subst n
      apply Subtype.ext
      exact congrArg (WType.mk (some p)) (funext fun e ↦ nomatch e)

/-- Assemble the observations with the constructor of the slice W-type. -/
def bundle (x : ∀ n, Approx n) : Bundle :=
  ⟨SlicePFunctor.W.mk ⟨⟨none, fun n ↦ leaf n (x n)⟩, rfl⟩, rfl⟩

/-- Read the depth-labelled children of the root. Admissibility supplies each
child's slice index and thus the type of the observation stored there. -/
def readBundle (w : Bundle) (n : Depth) : Approx n := by
  rcases w with ⟨⟨w, hw⟩, hi⟩
  cases w with
  | mk a f =>
    cases a with
    | none =>
      exact readLeaf n ⟨f n, ((bundleSig.wValid_mk none f).mp hw).1 n⟩
        (congrFun ((bundleSig.wValid_mk none f).mp hw).2 n)
    | some p => cases hi

/-- Reading after assembling preserves every observation. -/
@[simp] theorem readBundle_bundle (x : ∀ n, Approx n) : readBundle (bundle x) = x := rfl

/-- The slice indices force every root tree to have precisely the assembled form. -/
theorem bundle_readBundle (w : Bundle) : bundle (readBundle w) = w := by
  rcases w with ⟨⟨w, hw⟩, hi⟩
  cases w with
  | mk a f =>
    cases a with
    | none =>
      apply Subtype.ext
      apply Subtype.ext
      apply congrArg (WType.mk none)
      funext n
      exact congrArg Subtype.val (leaf_readLeaf n
        ⟨f n, ((bundleSig.wValid_mk none f).mp hw).1 n⟩
        (congrFun ((bundleSig.wValid_mk none f).mp hw).2 n))
    | some p => cases hi

/-- The countable family of observations is represented by a single slice W-tree. -/
def bundleEquiv : Bundle ≃ (∀ n, Approx n) where
  toFun := readBundle
  invFun := bundle
  left_inv := bundle_readBundle
  right_inv := readBundle_bundle

/-- A bitstream is a slice W-tree of finite presheaf W-observations whose
neighbouring depths agree. Compatibility is a proposition, not extra data.
This is a compatible subtype of the root fibre of the initial algebra for
{name}`bundleSig`. The equivalence {lit}`mEquiv` below identifies it with
the carrier of the final coalgebra for the finitary polynomial
{name}`Geb.BitStream.sig`. -/
abbrev Stream := {w : Bundle // Consistent (readBundle w)}

/-- Forgetting the outer W packaging identifies bitstreams with coherent families. -/
def coherentEquiv : Stream ≃ {x : ∀ n, Approx n // Consistent x} where
  toFun w := ⟨readBundle w.1, w.2⟩
  invFun x := ⟨bundle x.1, x.2⟩
  left_inv w := Subtype.ext (bundle_readBundle w.1)
  right_inv _ := rfl

/-- The construction from ordinary, presheaf, and slice W-types is mathlib's M-type. -/
def mEquiv : Stream ≃ sig.M := coherentEquiv.trans coherentFamilyEquiv

/-- It therefore also describes terminating or infinite sequences of bits. -/
def seqEquiv : Stream ≃ Stream'.Seq Bool := mEquiv.trans Geb.BitStream.seqEquiv

/-- Construct every finite unfolding by W-elimination, then assemble the
compatible unfoldings into the root of the outer slice W-type. -/
def corec {α : Type*} (step : α → Layer α) (a : α) : Stream :=
  ⟨bundle (fun n ↦ corecApprox step n a), corecApprox_consistent step a⟩

/-!
## Comparison of corecursion and finite inputs

The equivalences preserve finite observations and corecursion, as well as
the inclusion of ordinary finite W-bitstrings. These equations make the
comparison usable for transferring operations and proofs from the first
development.
-/

/-- One layer of mathlib's finite unfolding is the coalgebra's layer with
finite unfolding applied to its children. -/
theorem cofixLayerEquiv_sCorec {α : Type*} (f : α → sig α) (n : ℕ) (a : α) :
    cofixLayerEquiv n (PFunctor.Approx.sCorec f a (n + 1)) =
      (layerEquiv α (f a)).map (Prod.map id (fun b ↦ PFunctor.Approx.sCorec f b n)) :=
  layerEquiv_map (fun b ↦ PFunctor.Approx.sCorec f b n) (f a)

/-- W-elimination computes the same finite unfoldings as mathlib's corecursor. -/
theorem approxEquiv_corecApprox {α : Type*} (f : α → sig α) : ∀ (n : Depth) (a : α),
    approxEquiv n (corecApprox (fun b ↦ layerEquiv α (f b)) n a) =
      PFunctor.Approx.sCorec f a (toNat n) :=
  depthInduction (fun _ ↦ @Subsingleton.elim (PFunctor.Approx.CofixA sig 0) _ _ _)
    fun n ih a ↦ by
    apply (cofixLayerEquiv (toNat n)).injective
    refine (approxEquiv_succ n _).trans ((congrArg
      (fun y ↦ y.map (Prod.map id (approxEquiv n))) (corecApprox_succ _ n a)).trans ?_)
    refine Eq.trans ?_ (cofixLayerEquiv_sCorec f (toNat n) a).symm
    cases layerEquiv α (f a) with
    | none => rfl
    | some p => exact congrArg (fun t ↦ some (p.1, t)) (ih p.2)

/-- Assembling those unfoldings commutes with the complete M-type corecursor. -/
theorem mEquiv_corec {α : Type*} (f : α → sig α) (a : α) :
    mEquiv (corec (fun b ↦ layerEquiv α (f b)) a) = PFunctor.M.corec f a := by
  apply PFunctor.M.ext' sig
  have h : familyEquiv (fun n ↦ corecApprox (fun b ↦ layerEquiv α (f b)) n a) =
      (PFunctor.M.corec f a).approx := by
    apply familyEquiv.symm.injective
    rw [familyEquiv.symm_apply_apply]
    funext n
    apply (approxEquiv n).injective
    exact (approxEquiv_corecApprox f n a).trans ((approxEquiv n).apply_symm_apply _).symm
  exact fun n ↦ congrFun h n

/-- The W-based corecursor produces the usual terminating-or-infinite sequence. -/
theorem seqEquiv_corec {α : Type*} (step : α → Layer α) (a : α) :
    seqEquiv (corec step a) = Stream'.Seq.corec step a := by
  have hstep : (fun b ↦ layerEquiv α ((layerEquiv α).symm (step b))) = step :=
    funext fun b ↦ (layerEquiv α).apply_symm_apply (step b)
  have h := congrArg Geb.BitStream.seqEquiv
    (mEquiv_corec (fun b ↦ (layerEquiv α).symm (step b)) a)
  rw [hstep, Geb.BitStream.seqEquiv_corec, hstep] at h
  exact h

/-- Finite strings already are W-trees of the bit polynomial. Their paths use
the same W-type, via the path equivalence in the first development. -/
def pathEquiv : sig.W ≃ PFunctor.Approx.Path sig :=
  wEquiv.trans Geb.BitStream.pathEquiv.symm

/-- Unfold a finite W-tree as a potentially infinite stream using its destructor. -/
def ofW (w : sig.W) : Stream := corec (fun t ↦ layerEquiv _ (PFunctor.W.dest t)) w

/-- The new embedding of finite strings agrees with the previous M-type embedding. -/
theorem mEquiv_ofW (w : sig.W) : mEquiv (ofW w) = Geb.BitStream.ofW w :=
  mEquiv_corec PFunctor.W.dest w

/-- The embedding of W-bitstrings represents precisely their finite sequences. -/
theorem seqEquiv_ofW (w : sig.W) : seqEquiv (ofW w) = Stream'.Seq.ofList (wEquiv w) :=
  (congrArg Geb.BitStream.seqEquiv (mEquiv_ofW w)).trans (Geb.BitStream.seqEquiv_ofW w)

/-!
## Constructor and destructor on the W-representation

Prepending constructs each finite observation and then assembles them.
The tail reads the child of every successor-depth observation and assembles
those children. If the stream has terminated, its tail is termination.
Compatibility proves that all positive depths have the same outer bit or
termination flag, which makes the constructor and destructor inverse.
-/

/-- Observe a stream at a W-type depth by reading the corresponding root child. -/
def observe (w : Stream) : ∀ n, Approx n := readBundle w.1

/-- Reading the assembled unfoldings returns the selected finite unfolding. -/
@[simp] theorem observe_corec {α : Type*} (step : α → Layer α) (a : α) (n : Depth) :
    observe (corec step a) n = corecApprox step n a := rfl

/-- Streams agree when all their finite W-observations agree. -/
theorem stream_ext (x y : Stream) (h : ∀ n, observe x n = observe y n) : x = y :=
  Subtype.ext (bundleEquiv.injective (funext h))

/-- The M-type equivalence preserves observations at every depth. -/
theorem approx_mEquiv (w : Stream) (n : Depth) :
    (mEquiv w).approx (toNat n) = approxEquiv n (observe w n) :=
  ((approxEquiv n).apply_symm_apply _).symm.trans
    (congrArg (approxEquiv n) (congrFun (familyEquiv.symm_apply_apply (observe w)) n))

/-- The finite observations of termination, used as the tail of a terminated stream. -/
def emptyApprox (n : Depth) : Approx n := corecApprox (fun _ : Unit ↦ none) n ()

/-- Form finite observations of a single stream layer by dependent W-elimination. -/
def mkApprox (x : Layer Stream) : ∀ n : Depth, Approx n :=
  depthRec cutoff fun n _ ↦ (succEquiv n).symm (x.map (Prod.map id (fun w ↦ observe w n)))

/-- The constructor's successor observation exposes the supplied stream layer. -/
theorem mkApprox_succ (x : Layer Stream) (n : Depth) :
    succEquiv n (mkApprox x (succ n)) = x.map (Prod.map id (fun w ↦ observe w n)) := by
  simp only [mkApprox, depthRec_succ, Equiv.apply_symm_apply]

/-- Adding one layer to compatible observations preserves compatibility. -/
theorem mkApprox_consistent (x : Layer Stream) : Consistent (mkApprox x) := by
  refine depthInduction rfl fun n _ ↦ ?_
  apply (succEquiv n).injective
  rw [truncate_succ, mkApprox_succ, mkApprox_succ]
  cases x with
  | none => rfl
  | some p => exact congrArg (fun t ↦ some (p.1, t)) (p.2.2 n)

/-- Terminate or prepend a bit, using the W-defined observations and assembly. -/
def mk (x : Layer Stream) : Stream := ⟨bundle (mkApprox x), mkApprox_consistent x⟩

/-- Reading a constructed stream returns its constructed finite observation. -/
@[simp] theorem observe_mk (x : Layer Stream) (n : Depth) :
    observe (mk x) n = mkApprox x n := rfl

/-- Consecutive positive-depth observations expose compatible outer layers. -/
theorem observe_succ (w : Stream) (n : Depth) :
    succEquiv n (observe w (succ n)) =
      (succEquiv (succ n) (observe w (succ (succ n)))).map (Prod.map id (truncate n)) :=
  (congrArg (succEquiv n) (w.2 (succ n))).symm.trans (truncate_succ n _)

/-- Discard the observed bit; termination has the empty observation as its tail. -/
def tailApprox (w : Stream) (n : Depth) : Approx n :=
  ((succEquiv n (observe w (succ n))).map Prod.snd).getD (emptyApprox n)

/-- Tail observations are compatible, including the termination case. -/
theorem tailApprox_consistent (w : Stream) : Consistent (tailApprox w) := by
  intro n
  change truncate n (tailApprox w (succ n)) = tailApprox w n
  unfold tailApprox
  rw [observe_succ w n]
  cases succEquiv (succ n) (observe w (succ (succ n))) with
  | none => exact corecApprox_consistent (fun _ : Unit ↦ none) () n
  | some p => rfl

/-- The tail is assembled from the tails of the finite W-observations. -/
def tail (w : Stream) : Stream := ⟨bundle (tailApprox w), tailApprox_consistent w⟩

/-- The first observable layer determines termination or a bit and the W-defined tail. -/
def dest (w : Stream) : Layer Stream :=
  (succEquiv zero (observe w (succ zero))).map (fun p ↦ (p.1, tail w))

/-- Every positive-depth observation has the same outer termination flag and bit. -/
theorem observe_head (w : Stream) : ∀ n,
    (succEquiv n (observe w (succ n))).map Prod.fst =
      (succEquiv zero (observe w (succ zero))).map Prod.fst :=
  depthInduction rfl fun n ih ↦ by
    rw [← ih, observe_succ w n]
    cases succEquiv (succ n) (observe w (succ (succ n))) <;> rfl

/-- The destructor describes the outer layer at every W-type depth. -/
theorem observe_dest (w : Stream) (n : Depth) :
    (dest w).map (Prod.map id (fun t ↦ observe t n)) =
      succEquiv n (observe w (succ n)) := by
  have h := observe_head w n
  rw [dest, Option.map_map]
  change ((succEquiv zero (observe w (succ zero))).map
    (fun p ↦ (p.1, tailApprox w n))) = _
  unfold tailApprox
  cases h₀ : succEquiv zero (observe w (succ zero)) with
  | none =>
    cases hn : succEquiv n (observe w (succ n)) with
    | none => rfl
    | some p => rw [h₀, hn] at h; cases h
  | some p =>
    cases hn : succEquiv n (observe w (succ n)) with
    | none => rw [h₀, hn] at h; cases h
    | some q =>
      rw [h₀, hn] at h
      have hb : q.1 = p.1 := Option.some.inj h
      exact congrArg (fun b ↦ some (b, q.2)) hb.symm

/-- Reconstructing a stream from its outer layer preserves every observation. -/
theorem mk_dest (w : Stream) : mk (dest w) = w := by
  apply stream_ext
  refine depthInduction ((eq_cutoff _).symm) fun n _ ↦ ?_
  apply (succEquiv n).injective
  exact (mkApprox_succ (dest w) n).trans (observe_dest w n)

/-- Reading the tail of a prepended bit returns the supplied continuation. -/
theorem tail_mk (b : Bool) (w : Stream) : tail (mk (some (b, w))) = w := by
  apply stream_ext
  intro n
  change ((succEquiv n (mkApprox (some (b, w)) (succ n))).map Prod.snd).getD _ = _
  rw [mkApprox_succ]
  rfl

/-- Reading a freshly constructed stream returns its supplied layer. -/
theorem dest_mk (x : Layer Stream) : dest (mk x) = x := by
  unfold dest
  change (succEquiv zero (mkApprox x (succ zero))).map _ = x
  rw [mkApprox_succ]
  cases x with
  | none => rfl
  | some p => exact congrArg (fun t ↦ some (p.1, t)) (tail_mk p.1 p.2)

/-- The W-defined constructor and destructor exhibit the expected coalgebra layer. -/
def streamLayerEquiv : Stream ≃ Layer Stream where
  toFun := dest
  invFun := mk
  left_inv := mk_dest
  right_inv := dest_mk

/-- The direct W-defined constructor corresponds to mathlib's M-type constructor. -/
theorem mEquiv_mk (x : Layer Stream) :
    mEquiv (mk x) = PFunctor.M.mk
      ((layerEquiv _).symm (x.map (Prod.map id mEquiv))) := by
  have h : ∀ n, approxEquiv n (observe (mk x) n) =
      (PFunctor.M.mk ((layerEquiv _).symm (x.map (Prod.map id mEquiv)))).approx (toNat n) :=
    depthInduction (by exact @Subsingleton.elim (PFunctor.Approx.CofixA sig 0) _ _ _)
      fun n _ ↦ by
      apply (cofixLayerEquiv (toNat n)).injective
      refine (approxEquiv_succ n _).trans ((congrArg
        (fun y ↦ y.map (Prod.map id (approxEquiv n))) (mkApprox_succ x n)).trans ?_)
      cases x with
      | none => rfl
      | some p => exact congrArg (fun t ↦ some (p.1, t)) (approx_mEquiv p.2 n).symm
  apply PFunctor.M.ext' sig
  intro k
  obtain ⟨n, rfl⟩ := depthEquiv.surjective k
  exact (approx_mEquiv (mk x) n).trans (h n)

/-- The equivalence to sequences preserves termination and prepending. -/
theorem seqEquiv_mk (x : Layer Stream) :
    seqEquiv (mk x) = prependLayer (x.map (Prod.map id seqEquiv)) := by
  have h := (congrArg Geb.BitStream.seqEquiv (mEquiv_mk x)).trans
    (Geb.BitStream.seqEquiv_mk _)
  cases x with
  | none => exact h
  | some p => exact h

/-- The W-defined corecursor satisfies its unfolding equation. -/
theorem corec_eq {α : Type*} (step : α → Layer α) (a : α) :
    corec step a = mk ((step a).map (Prod.map id (corec step))) := by
  apply stream_ext
  refine depthInduction ?_ fun n _ ↦ ?_
  · rw [observe_corec, observe_mk]
    rfl
  · rw [observe_corec, observe_mk]
    apply (succEquiv n).injective
    rw [corecApprox_succ, mkApprox_succ]
    cases step a with
    | none => rfl
    | some p => exact congrArg (fun t ↦ some (p.1, t)) (observe_corec step p.2 n).symm

/-- The coherent W-tree also recovers the earlier bounded-list observation structure. -/
def observationsEquiv : Stream ≃ Observations := mEquiv.trans Geb.BitStream.mEquiv

end Geb.BitStream.WConstruction
