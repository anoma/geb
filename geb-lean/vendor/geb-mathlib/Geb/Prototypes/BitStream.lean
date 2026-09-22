/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Mathlib.Data.PFunctor.Univariate.M
public import Mathlib.Data.Seq.Defs
public import Mathlib.Logic.Equiv.List
public import Mathlib.Logic.Equiv.Option

set_option doc.verso true

/-!
# From finite bitstrings to potentially infinite bitstreams

The polynomial {lit}`F X = Option (Bool × X)` has an empty shape and two unary
shapes. Its W-type is {lit}`List Bool`; its M-type also admits infinite sequences.
This module follows {name}`PFunctor.Approx.CofixA`, {name}`PFunctor.Approx.Agree`,
{name}`PFunctor.Approx.AllAgree`, and {name}`PFunctor.MIntl`, simplifying each for
this polynomial and proving the correspondences.

## Main definitions

* {lit}`sig` and {lit}`layerEquiv` express one unfolding as an optional bit and tail.
* {lit}`wEquiv` identifies the W-type with finite bitstrings.
* {lit}`Prefix n` is a bitstring of length at most {lit}`n`.
* {lit}`approxEquiv n` identifies mathlib's depth-{lit}`n` approximation with a prefix.
* {lit}`Observations` packages compatible prefixes, corresponding to {name}`PFunctor.MIntl`.
* {lit}`seqEquiv` identifies the M-type with {lit}`Stream'.Seq Bool`.
* {lit}`corecPrefix` iterates a transition for a bounded number of observations.

## Main statements

* {lit}`approxEquiv_truncate` identifies tree truncation with {name}`List.take`.
* {lit}`agree_iff_take` and {lit}`allAgree_iff_consistent` identify the compatibility conditions.
* {lit}`take_seqEquiv` shows that the final equivalence preserves every observation.
* {lit}`seqEquiv_mk` and {lit}`seqEquiv_corec` preserve construction and corecursion.
* {lit}`seqEquiv_ofW` identifies the W-to-M inclusion with {name}`Stream'.Seq.ofList`.

## Implementation notes

The univariate construction in {lit}`Mathlib.Data.PFunctor.Univariate.M` does not
construct M-values from {name}`WType` values. It defines the indexed inductive family
{name}`PFunctor.Approx.CofixA` directly, then packages a compatible approximation at
every depth. The W-type and these finite approximations use the same polynomial.

At depth zero there is no observation. At positive depth an empty list records
termination. A prefix shorter than its depth bound has reached the empty shape;
a prefix exactly as long as its bound has reached the observation limit. Thus
depth one distinguishes the empty stream, a stream beginning with zero, and a
stream beginning with one, but does not yet inspect either tail.

The successive types of observations are {lit}`{[]}` at depth zero,
{lit}`{[], [false], [true]}` at depth one, and lists of length at most two at
depth two. For a finite string {lit}`[true]`, the observations are
{lit}`[], [true], [true], …`. For the alternating stream beginning with
{lit}`true`, they are {lit}`[], [true], [true, false], [true, false, true], …`.
The first family has observed termination at depth two; the second never does.

Compatibility requires that taking the first {lit}`n` bits of the next
observation reproduces the current one. It excludes both changing an already
observed bit and extending a string whose termination was already observed.
Reading position {lit}`n` from observation {lit}`n + 1` then gives the final
representation: a function {lit}`ℕ → Option Bool` whose {lit}`none` values persist.
This representation is already provided by {name}`Stream'.Seq`.

Bits are observed in Lean list order, starting at the head. No decision whether
a stream eventually terminates is part of the representation.

The comments also compare free monads and cofree comonads of this polynomial.
Those constructions provide mathematical context; the definitions below
formalize the W-type, M-type, and finite-observation comparisons.

## References

* \[GambinoKock2013\], Section 1.19 and Theorem 4.5, for finite arities
  and polynomial free monads.
* \[AhmanChapmanUustalu2014\], Section 4.3 and Proposition 4.5, for
  the polynomial presentation of cofree comonads.

## Tags

M-type, W-type, polynomial functor, bitstream, finite approximation, corecursion
-/

@[expose] public section

namespace Geb.BitStream

open PFunctor

/-!
## The polynomial and its W-type
-/

/-- The empty shape has no direction; each bit shape has one tail direction.

A polynomial {lit}`P X = Σ a, (B a → X)` is finitary when every direction
type {lit}`B a` is finite. The set of shapes may be infinite. Over sets,
this is equivalent to preserving filtered colimits
(\[GambinoKock2013\], Section 1.19). Here every arity is zero or one. -/
def sig : PFunctor.{0, 0} where
  A := Option Bool
  B := fun a ↦ match a with
    | none => Empty
    | some _ => Unit

/-- The default shape is termination. -/
instance : Inhabited sig.A := ⟨none⟩

/-- One observable layer: termination, or a bit together with its continuation. -/
abbrev Layer (α : Type*) := Option (Bool × α)

/-- The dependent sum in {name}`PFunctor.Obj` simplifies to an optional pair. -/
def layerEquiv (α : Type*) : sig α ≃ Layer α where
  toFun x := match x with
    | .mk none _ => none
    | .mk (some b) f => some (b, f ())
  invFun x := match x with
    | none => .mk none Empty.elim
    | some (b, t) => .mk (some b) fun _ ↦ t
  left_inv x := by
    rcases x with ⟨_ | b, f⟩
    · exact congrArg (Sigma.mk none) (funext fun i ↦ nomatch i)
    · rfl
  right_inv x := by
    rcases x with _ | ⟨b, t⟩ <;> rfl

/-- Mapping a polynomial layer applies the function only to the continuation. -/
theorem layerEquiv_map {α β : Type*} (f : α → β) (x : sig α) :
    layerEquiv β (sig.map f x) = (layerEquiv α x).map (Prod.map id f) := by
  rcases x with ⟨_ | b, t⟩ <;> rfl

/-- Fold a well-founded unary tree into its finite list of bits. -/
def wToList : sig.W → List Bool :=
  WType.elim (List Bool) fun x ↦ match layerEquiv _ x with
    | none => []
    | some (b, t) => b :: t

/-- Build the W-tree by folding the finite list, ending in the empty shape. -/
def listToW : List Bool → sig.W :=
  List.rec (WType.mk none Empty.elim) fun b _ t ↦ WType.mk (some b) fun _ ↦ t

/-- The W-type of the bitstring polynomial is exactly {lit}`List Bool`.

The related free-monad construction uses {lit}`Free P X = μ Y. (X + P Y)`:
the extra summand supplies variable leaves. Its polynomial shapes are
well-founded operation trees with designated variable leaves, and its
directions are those leaves (\[GambinoKock2013\], Theorem 4.5).
Finite branching and well-foundedness make each such tree finite, so the
free monad of a finitary polynomial is again finitary.

For {name}`sig`, the result simplifies to
{lit}`Free sig X ≃ List Bool × (Unit ⊕ X)`: a finite prefix ends either in
termination or in a variable. Each shape therefore has zero or one variable
position, although there are infinitely many shapes. -/
def wEquiv : sig.W ≃ List Bool where
  toFun := wToList
  invFun := listToW
  left_inv := WType.rec fun a f ih ↦ by
    cases a with
    | none => exact congrArg (WType.mk none) (funext fun i ↦ nomatch i)
    | some b => exact congrArg (WType.mk (some b)) (funext fun i ↦ ih i)
  right_inv := List.rec rfl fun b _ ih ↦ congrArg (b :: ·) ih

/-!
## Finite observations
-/

/-- At depth {lit}`n`, at most {lit}`n` bits have been observed. A shorter list
has terminated; a list of length {lit}`n` may still continue. -/
abbrev Prefix (n : ℕ) := { w : List Bool // w.length ≤ n }

/-- At positive depth, observing a prefix means observing termination or one
bit followed by a prefix at the preceding depth. -/
def prefixLayerEquiv (n : ℕ) : Layer (Prefix n) ≃ Prefix (n + 1) where
  toFun x := match x with
    | none => ⟨[], Nat.zero_le _⟩
    | some (b, t) => ⟨b :: t.val, Nat.succ_le_succ t.property⟩
  invFun x := match x with
    | ⟨[], _⟩ => none
    | ⟨b :: t, h⟩ => some (b, ⟨t, Nat.le_of_succ_le_succ h⟩)
  left_inv x := by
    rcases x with _ | ⟨b, t⟩ <;> rfl
  right_inv x := by
    rcases x with ⟨_ | ⟨b, t⟩, h⟩ <;> rfl

open PFunctor.Approx

/-- {name}`head'` and {name}`children'` together expose one layer of a
positive-depth approximation. The nullary child function disappears and the
unary child function becomes its value at {lit}`()`. -/
def cofixLayerEquiv (n : ℕ) : CofixA sig (n + 1) ≃ Layer (CofixA sig n) where
  toFun x := layerEquiv _ (.mk (head' x) (children' x))
  invFun x := match x with
    | none => .intro none Empty.elim
    | some (b, t) => .intro (some b) fun _ ↦ t
  left_inv x := by
    cases x with | intro a f =>
    cases a with
    | none => exact congrArg (CofixA.intro (F := sig) none) (funext fun i ↦ nomatch i)
    | some b => rfl
  right_inv x := by
    rcases x with _ | ⟨b, t⟩ <;> rfl

/-- The indexed finite trees in mathlib are bounded bitstrings. This definition
iterates the one-layer equivalences by {name}`Nat.rec`; depth zero has one value. -/
def approxEquiv : ∀ n, CofixA sig n ≃ Prefix n :=
  Nat.rec
    { toFun := fun _ ↦ ⟨[], Nat.zero_le _⟩
      invFun := fun _ ↦ .continue
      left_inv := fun x ↦ Subsingleton.elim _ x
      right_inv := fun ⟨_, h⟩ ↦
        Subtype.ext (List.length_eq_zero_iff.mp (Nat.eq_zero_of_le_zero h)).symm }
    (fun n e ↦ (cofixLayerEquiv n).trans
      ((Equiv.optionCongr ((Equiv.refl Bool).prodCongr e)).trans (prefixLayerEquiv n)))

/-- The depth-zero observation contains no bits. -/
@[simp] theorem approxEquiv_zero (x : CofixA sig 0) : (approxEquiv 0 x).val = [] := rfl

/-- Observing the empty shape terminates the prefix. -/
@[simp] theorem approxEquiv_nil (n : ℕ) (f : sig.B none → CofixA sig n) :
    (approxEquiv (n + 1) (.intro none f)).val = [] := rfl

/-- Observing a bit prepends it to the observation of the unique child. -/
@[simp] theorem approxEquiv_cons (n : ℕ) (b : Bool) (f : sig.B (some b) → CofixA sig n) :
    (approxEquiv (n + 1) (.intro (some b) f)).val = b :: (approxEquiv n (f ())).val := rfl

/-- The default finite approximation observes termination as soon as its depth is positive. -/
theorem approxEquiv_default (n : ℕ) :
    (approxEquiv n (CofixA.default sig n)).val = [] := by
  cases n <;> rfl

/-!
## Truncation and compatibility
-/

/-- Forget the last observable level by taking the first {lit}`n` bits. -/
def truncatePrefix {n : ℕ} (p : Prefix (n + 1)) : Prefix n :=
  ⟨p.val.take n, List.length_take_le _ _⟩

/-- The head shape becomes the optional first bit of the prefix. -/
theorem head'_eq_head? {n : ℕ} (x : CofixA sig (n + 1)) :
    head' x = (approxEquiv (n + 1) x).val.head? := by
  cases x with | intro a f => cases a <;> rfl

/-- The only child, when it exists, becomes the tail of the prefix. -/
theorem children'_eq_tail {n : ℕ} (x : CofixA sig (n + 1)) (i : sig.B (head' x)) :
    (approxEquiv n (children' x i)).val = (approxEquiv (n + 1) x).val.tail := by
  cases x with | intro a f =>
  cases a with
  | none => exact nomatch i
  | some b => cases i; rfl

/-- Mathlib's tree truncation is precisely list truncation under the equivalence. -/
theorem approxEquiv_truncate : ∀ (n : ℕ) (x : CofixA sig (n + 1)),
    approxEquiv n (truncate x) = truncatePrefix (approxEquiv (n + 1) x) :=
  Nat.rec
    (fun x ↦ by cases x; apply Subtype.ext; rfl)
    (fun n ih x ↦ by
      cases x with | intro a f =>
      cases a with
      | none => apply Subtype.ext; rfl
      | some b =>
        apply Subtype.ext
        exact congrArg (b :: ·) (congrArg Subtype.val (ih (f ()))))

/-- Any approximation agrees with its truncation. This supplies the converse of
mathlib's {name}`truncate_eq_of_agree` without a decision procedure for equality. -/
theorem agree_truncate : ∀ (n : ℕ) (x : CofixA sig (n + 1)), Agree (truncate x) x :=
  Nat.rec (fun _ ↦ agree_trivial)
    (fun _ ih x ↦ by
      cases x with | intro a f => exact .intro _ _ fun i ↦ ih (f i))

/-- The inductive relation {name}`Agree` simplifies to equality after taking a prefix. -/
theorem agree_iff_take {n : ℕ} (x : CofixA sig n) (y : CofixA sig (n + 1)) :
    Agree x y ↔ truncatePrefix (approxEquiv (n + 1) y) = approxEquiv n x := by
  rw [← approxEquiv_truncate, Equiv.apply_eq_iff_eq]
  exact ⟨truncate_eq_of_agree x y, fun h ↦ h ▸ agree_truncate n y⟩

/-- Successive bounded observations agree when forgetting the last level gives
the preceding observation. This is the specialization of {name}`AllAgree`. -/
def Consistent (x : ∀ n, Prefix n) : Prop :=
  ∀ n, truncatePrefix (x (n + 1)) = x n

/-- Compatibility of tree approximations is compatibility of list prefixes. -/
theorem allAgree_iff_consistent (x : ∀ n, CofixA sig n) :
    AllAgree x ↔ Consistent (fun n ↦ approxEquiv n (x n)) :=
  forall_congr' fun n ↦ agree_iff_take (x n) (x (n + 1))

/-!
## Finite stages of corecursion
-/

/-- Produce a bounded observation by iterating a state transition at most
{lit}`n` times. A transition returns termination or a bit and a new state. -/
def corecPrefix {α : Type*} (step : α → Layer α) : ∀ n, α → Prefix n :=
  Nat.rec (fun _ ↦ ⟨[], Nat.zero_le _⟩)
    (fun n rec a ↦ prefixLayerEquiv n ((step a).map (Prod.map id rec)))

/-- The finite stage of mathlib's corecursor becomes bounded iteration. -/
theorem approxEquiv_sCorec {α : Type*} (f : α → sig α) : ∀ (n : ℕ) (a : α),
    approxEquiv n (sCorec f a n) = corecPrefix (fun x ↦ layerEquiv _ (f x)) n a :=
  Nat.rec (fun _ ↦ rfl) (fun n ih a ↦ by
    change approxEquiv (n + 1) (.intro (f a).fst (fun i ↦ sCorec f ((f a).snd i) n)) =
      prefixLayerEquiv n ((layerEquiv _ (f a)).map
        (Prod.map id (corecPrefix (fun x ↦ layerEquiv _ (f x)) n)))
    cases h : f a with | mk b t =>
    cases b with
    | none => rfl
    | some b =>
      apply Subtype.ext
      change b :: _ = b :: _
      exact congrArg (b :: ·) (congrArg Subtype.val (ih (t ()))))

/-- Iterating a transition gives compatible observations. This is the specialization
of {name}`P_corec`, with {name}`Agree` replaced by equality of list prefixes. -/
theorem corecPrefix_consistent {α : Type*} (step : α → Layer α) (a : α) :
    Consistent (fun n ↦ corecPrefix step n a) := by
  let f : α → sig α := fun x ↦ (layerEquiv α).symm (step x)
  have h := (allAgree_iff_consistent (sCorec f a)).mp (P_corec f a)
  simpa only [approxEquiv_sCorec, f, Equiv.apply_symm_apply] using h

/-- An index names a bit shape and its unique direction, so it is just a bit.
There is no index at the empty shape. -/
def idxEquiv : sig.Idx ≃ Bool where
  toFun x := match x with
    | ⟨none, i⟩ => nomatch i
    | ⟨some b, _⟩ => b
  invFun b := ⟨some b, ()⟩
  left_inv x := by
    rcases x with ⟨_ | b, i⟩
    · exact nomatch i
    · cases i; rfl
  right_inv _ := rfl

/-- Mathlib's raw paths are lists of bit-labelled directions. A path need not
be valid in a particular stream; its labels must match the bits it traverses. -/
def pathEquiv : Path sig ≃ List Bool := Equiv.listEquivOfEquiv idxEquiv

/-!
## Assembling the M-type
-/

/-- A potentially infinite bitstream presented as compatible finite observations.
This has exactly the fields of {name}`MIntl`, with dependent trees replaced by lists.

An M-type admits infinite branches even when each node has finite arity.
It is a type; finitarity is a property of the functor whose fixed point it is.
The cofree comonad introduces a different functor by allowing a label from
{lit}`X` at every node: {lit}`C X = ν Y. (X × sig Y)`.

Its polynomial presentation is {lit}`C X ≃ Σ t : sig.M, (Nodes t → X)`.
Here {lit}`Nodes t` consists of the valid finite paths in {lit}`t`, including
the empty path to its root. These are tree positions, not just the immediate
directions at the root. A finite bitstring of length {lit}`n` has
{lit}`n + 1` nodes, including its terminal node; an infinite bitstream has
one node at each natural-number depth. See \[AhmanChapmanUustalu2014\],
Section 4.3 and Proposition 4.5, for the general construction.

Thus this cofree comonad is polynomial but has countably infinite arities.
Its failure to be finitary is independent of that presentation: the finite
sets {lit}`{0, …, n}` have filtered colimit {name}`Nat`, but the infinite
all-zero bitstream whose node at depth {lit}`k` is labelled {lit}`k` uses
unbounded labels. It belongs to {lit}`C Nat` and comes from no finite stage,
so {lit}`C` does not preserve this filtered colimit. The immediate bitstream
polynomial {name}`sig` still has only zero and unary arities. Taking
{lit}`X = Unit` makes all node labels trivial and recovers {lit}`sig.M`.
-/
@[ext] structure Observations : Type where
  /-- The list observed at each depth, bounded by that depth. -/
  atDepth : ∀ n, Prefix n
  /-- Each observation truncates to the preceding one. -/
  consistent : Consistent atDepth

/-- Mathlib's {name}`PFunctor.M` is definitionally {name}`MIntl`; both become
the same structure of compatible bounded bitstrings. -/
def mEquiv : sig.M ≃ Observations where
  toFun x := ⟨fun n ↦ approxEquiv n (x.approx n),
    (allAgree_iff_consistent x.approx).mp x.consistent⟩
  invFun x := ⟨fun n ↦ (approxEquiv n).symm (x.atDepth n),
    (allAgree_iff_consistent _).mpr (by simpa using x.consistent)⟩
  left_inv x := M.ext' sig _ x fun n ↦ (approxEquiv n).symm_apply_apply _
  right_inv x := Observations.ext (funext fun n ↦ (approxEquiv n).apply_symm_apply _)

/-- Corecursion in the compatible-prefix presentation of the M-type. -/
def corecObservations {α : Type*} (step : α → Layer α) (a : α) : Observations :=
  ⟨fun n ↦ corecPrefix step n a, corecPrefix_consistent step a⟩

/-- The M-type corecursor agrees at every depth with bounded iteration. -/
theorem mEquiv_corec {α : Type*} (f : α → sig α) (a : α) :
    mEquiv (M.corec f a) = corecObservations (fun x ↦ layerEquiv _ (f x)) a :=
  Observations.ext (funext fun n ↦ approxEquiv_sCorec f n a)

/-!
## From compatible prefixes to optional bits
-/

/-- The finite observation has length at most its depth bound. This proof uses
only the sequence case eliminator and natural-number recursion. -/
theorem seq_length_take_le : ∀ (n : ℕ) (s : Stream'.Seq Bool), (s.take n).length ≤ n :=
  Nat.rec (fun _ ↦ Nat.zero_le _)
    (fun n ih s ↦ Stream'.Seq.recOn (motive := fun t ↦ (t.take (n + 1)).length ≤ n + 1)
      s (Nat.zero_le _) fun _ t ↦ Nat.succ_le_succ (ih t))

/-- Taking a finite observation preserves precisely the positions below its bound. -/
theorem seq_getElem?_take : ∀ (n : ℕ) (s : Stream'.Seq Bool) (i : ℕ),
    (s.take n)[i]? = if i < n then s.get? i else none :=
  Nat.rec
    (fun _ _ ↦ by simp only [Stream'.Seq.take, List.getElem?_nil, Nat.not_lt_zero, ite_false])
    (fun n ih s ↦ Stream'.Seq.recOn
      (motive := fun t ↦ ∀ i, (t.take (n + 1))[i]? = if i < n + 1 then t.get? i else none) s
      (fun i ↦ by simp only [Stream'.Seq.take, Stream'.Seq.destruct_nil,
        List.getElem?_nil, Stream'.Seq.get?_nil, ite_self])
      (fun b t i ↦ by
        cases i with
        | zero => rfl
        | succ i =>
          simpa only [Stream'.Seq.take, Stream'.Seq.destruct_cons,
            List.getElem?_cons_succ, Nat.succ_lt_succ_iff, Stream'.Seq.get?_cons_succ]
            using ih t i))

/-- A sequence supplies compatible observations by taking finitely many bits. -/
def observationsOfSeq (s : Stream'.Seq Bool) : Observations where
  atDepth n := ⟨s.take n, seq_length_take_le n s⟩
  consistent n := by
    apply Subtype.ext
    apply List.ext_getElem?
    intro i
    by_cases h : i < n
    · have h' : i < n + 1 := Nat.lt_succ_of_lt h
      simp [truncatePrefix, seq_getElem?_take, h, h']
    · simp [truncatePrefix, seq_getElem?_take, h]

/-- Adjacent compatibility implies compatibility at any two depths. -/
theorem Observations.take_atDepth (s : Observations) {n m : ℕ} (h : n ≤ m) :
    (s.atDepth m).val.take n = (s.atDepth n).val := by
  refine Nat.le_induction (List.take_of_length_le (s.atDepth n).property) ?_ m h
  intro k hk ih
  calc
    (s.atDepth (k + 1)).val.take n = ((s.atDepth (k + 1)).val.take k).take n := by
      rw [List.take_take, Nat.min_eq_left hk]
    _ = (s.atDepth k).val.take n :=
      congrArg (List.take n) (congrArg Subtype.val (s.consistent k))
    _ = (s.atDepth n).val := ih

/-- Read bit {lit}`i` from any observation deep enough to include it. -/
theorem Observations.getElem?_atDepth (s : Observations) {i n : ℕ} (h : i < n) :
    (s.atDepth n).val[i]? = (s.atDepth (i + 1)).val[i]? := by
  have ht := congrArg (fun w : List Bool ↦ w[i]?) (s.take_atDepth h)
  simpa [List.getElem?_take] using ht

/-- The root observation is independent of the positive depth chosen. This is
the list form of the root constancy expressed by {name}`head_succ'`. -/
theorem Observations.first_atDepth (s : Observations) (n m : ℕ) :
    (s.atDepth (n + 1)).val[0]? = (s.atDepth (m + 1)).val[0]? :=
  (s.getElem?_atDepth (Nat.zero_lt_succ n)).trans
    (s.getElem?_atDepth (Nat.zero_lt_succ m)).symm

/-- Compatible finite observations yield an optional bit at every position.
Once a bit is absent, every subsequent bit is absent, as required by {name}`Stream'.IsSeq`. -/
def seqOfObservations (s : Observations) : Stream'.Seq Bool :=
  ⟨fun n ↦ (s.atDepth (n + 1)).val[n]?, fun {n} h ↦ by
    have hn : (s.atDepth (n + 2)).val[n]? = none :=
      (s.getElem?_atDepth (by omega : n < n + 2)).trans h
    exact List.getElem?_eq_none (Nat.le_succ_of_le (List.getElem?_eq_none_iff.mp hn))⟩

/-- Reading the first {lit}`n` bits recovers exactly the depth-{lit}`n` observation. -/
theorem take_seqOfObservations (s : Observations) (n : ℕ) :
    (seqOfObservations s).take n = (s.atDepth n).val := by
  apply List.ext_getElem?
  intro i
  rw [seq_getElem?_take]
  by_cases h : i < n
  · rw [if_pos h]
    exact (s.getElem?_atDepth h).symm
  · rw [if_neg h]
    exact (List.getElem?_eq_none (by have := (s.atDepth n).property; omega)).symm

/-- Compatible bounded prefixes carry exactly the information of a sequence of
optional bits with permanent termination. -/
def observationsEquiv : Observations ≃ Stream'.Seq Bool where
  toFun := seqOfObservations
  invFun := observationsOfSeq
  left_inv s := Observations.ext (funext fun n ↦ Subtype.ext (take_seqOfObservations s n))
  right_inv s := Stream'.Seq.ext fun n ↦ by
    change (s.take (n + 1))[n]? = s.get? n
    simp only [seq_getElem?_take, Nat.lt_succ_self, if_pos]

/-- The M-type is a sequence of optional bits, with no bit after termination.
The intermediate equivalence retains the construction by finite approximations. -/
def seqEquiv : sig.M ≃ Stream'.Seq Bool := mEquiv.trans observationsEquiv

/-- The equivalence preserves each finite observation, not just the carrier type. -/
theorem take_seqEquiv (x : sig.M) (n : ℕ) :
    (seqEquiv x).take n = (approxEquiv n (x.approx n)).val :=
  take_seqOfObservations (mEquiv x) n

/-!
## Constructors, corecursion, and finite inputs
-/

/-- A terminating layer constructs the empty sequence; a bit layer constructs
the sequence obtained by prepending that bit. -/
def prependLayer : Layer (Stream'.Seq Bool) → Stream'.Seq Bool
  | none => .nil
  | some (b, t) => .cons b t

/-- Mathlib's M-constructor becomes the ordinary empty/cons construction. -/
theorem seqEquiv_mk (x : sig sig.M) :
    seqEquiv (M.mk x) = prependLayer ((layerEquiv _ x).map (Prod.map id seqEquiv)) := by
  rcases x with ⟨_ | b, f⟩
  · apply Stream'.Seq.ext; intro n; rfl
  · apply Stream'.Seq.ext; intro n; cases n <;> rfl

/-- The simplified constructor and destructor are mutually inverse. -/
def seqLayerEquiv : Stream'.Seq Bool ≃ Layer (Stream'.Seq Bool) where
  toFun := Stream'.Seq.destruct
  invFun := prependLayer
  left_inv s := Stream'.Seq.recOn (motive := fun t ↦ prependLayer t.destruct = t)
    s rfl fun _ _ ↦ rfl
  right_inv x := by rcases x with _ | ⟨b, t⟩ <;> rfl

/-- Bounded iteration is the finite observation of the existing sequence corecursor. -/
theorem corecPrefix_eq_take {α : Type*} (step : α → Layer α) : ∀ (n : ℕ) (a : α),
    (corecPrefix step n a).val = (Stream'.Seq.corec step a).take n :=
  Nat.rec (fun _ ↦ rfl) (fun n ih a ↦ by
    change (prefixLayerEquiv n ((step a).map (Prod.map id (corecPrefix step n)))).val = _
    cases h : step a with
    | none => rw [Stream'.Seq.corec_nil step a h]; rfl
    | some p =>
      rcases p with ⟨b, t⟩
      rw [Stream'.Seq.corec_cons h]
      exact congrArg (b :: ·) (ih t))

/-- Mathlib's tree corecursor and sequence corecursor produce the same bitstream. -/
theorem seqEquiv_corec {α : Type*} (f : α → sig α) (a : α) :
    seqEquiv (M.corec f a) = Stream'.Seq.corec (fun x ↦ layerEquiv _ (f x)) a := by
  apply Stream'.Seq.ext
  intro n
  have h := congrArg (fun w : List Bool ↦ w[n]?)
    ((take_seqEquiv (M.corec f a) (n + 1)).trans
      ((congrArg Subtype.val (approxEquiv_sCorec f (n + 1) a)).trans
        (corecPrefix_eq_take _ (n + 1) a)))
  simpa only [seq_getElem?_take, Nat.lt_succ_self, if_pos] using h

/-- The default M-value is the terminating empty stream. -/
theorem seqEquiv_default : seqEquiv (default : sig.M) = Stream'.Seq.nil :=
  Stream'.Seq.ext fun _ ↦ rfl

/-- Embed the W-type in the M-type by repeatedly observing its root and child.
The input is well-founded, so this corecursion describes a finite stream. -/
def ofW : sig.W → sig.M := M.corec W.dest

/-- The W-to-M embedding becomes the standard inclusion of lists in sequences. -/
theorem seqEquiv_ofW : ∀ x : sig.W, seqEquiv (ofW x) = Stream'.Seq.ofList (wEquiv x) :=
  WType.rec fun a f ih ↦ by
    refine (congrArg seqEquiv (M.corec_def (W.dest (P := sig)) (WType.mk a f))).trans
      ((seqEquiv_mk _).trans ?_)
    cases a with
    | none => rfl
    | some b =>
      change Stream'.Seq.cons b (seqEquiv (ofW (f ()))) =
        Stream'.Seq.ofList (b :: wEquiv (f ()))
      rw [Stream'.Seq.ofList_cons, ih ()]

/-- The inclusion of finite bitstrings loses no information. -/
theorem ofW_injective : Function.Injective ofW := by
  intro x y h
  apply wEquiv.injective
  apply Stream'.Seq.ofList_injective
  rw [← seqEquiv_ofW, ← seqEquiv_ofW, h]

/-!
## Examples
-/

/-- One bit of observation cannot distinguish a one-bit string from a stream
that has the same first bit and continues. -/
theorem one_bit_observation :
    corecPrefix (fun w : List Bool ↦ w.head?.map (fun b ↦ (b, w.tail))) 1 [true] =
      corecPrefix (fun b : Bool ↦ some (b, !b)) 1 true := rfl

/-- The next observation distinguishes termination from continuation. -/
theorem two_bit_observations :
    (corecPrefix (fun w : List Bool ↦ w.head?.map (fun b ↦ (b, w.tail))) 2 [true]).val =
      [true] ∧
    (corecPrefix (fun b : Bool ↦ some (b, !b)) 2 true).val = [true, false] := ⟨rfl, rfl⟩

/-- Every finite observation of a state transition that always emits a bit
fills its depth bound. Thus there is no observation of termination. -/
theorem corecPrefix_always_some_length {α : Type*} (bit : α → Bool) (next : α → α) :
    ∀ (n : ℕ) (a : α), (corecPrefix (fun x ↦ some (bit x, next x)) n a).val.length = n :=
  Nat.rec (fun _ ↦ rfl) (fun _ ih a ↦ congrArg Nat.succ (ih (next a)))

end Geb.BitStream
