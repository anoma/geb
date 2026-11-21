/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.CobhamFoldProto.Expr
public import Geb.Prototypes.Computability.CobhamFoldProto.Variable

/-!
# Smash-freeness at a symbolic tree

`Cobham.smashFreeBool` is a `WType.elim` whose clause at a node applies `decide`
to a quantification over `Cobham.sig.B`. Instance search does not find the
`Cobham.sigFinitary`-derived enumeration at that form, and the `WType.elim` does
not reduce at a variable shape, so a `Cobham.SmashFree` claim about a symbolic
tree is not available by `decide_eq_true`.

This module supplies the two missing steps: `instFinEnumSigB` names the
enumeration at the form the quantification reads, and splitting the shape
reduces the `WType.elim`, giving at each shape but `smash` an equivalence
between a node's smash-freeness and its children's. The implications compose
through the combinators.

## Main definitions

* `Geb.CobhamFold.instFinEnumSigB` — the direction family's enumeration, at the
  form `Cobham.smashFreeBool`'s quantification reads.

## Main statements

* `Geb.CobhamFold.smashFreeBool_mk_iff` — a node other than `smash` is
  smash-free exactly when its children are.
* `Geb.CobhamFold.smashFreeBool_mk` — its `mpr`, which the generator lemmas
  below apply directly and every other lemma reaches through
  `Geb.CobhamFold.smashFreeBool_projRaw`,
  `Geb.CobhamFold.smashFreeBool_compRaw` or
  `Geb.CobhamFold.smashFreeBool_boundedRecRaw`.
* `Geb.CobhamFold.smashFreeBool_boundMulRaw` — the multiplicative bound child
  carries no `smash`, at every multiplicity and growth.
* `Geb.CobhamFold.smashFree_foldOutExpr` — the fixed-width construction's
  output expression is smash-free at every alphabet and carrier width.
* `Geb.CobhamFold.smashFree_foldOutExprV` — the bitstring construction's is
  smash-free when the algebra's own expressions are.

## Implementation notes

Two separate obstructions stand between `Cobham.smashFreeBool` and a symbolic
claim, and each step removes one. `instFinEnumSigB` supplies decidability, which
instance search does not: `Cobham.sigFinitary`'s branches ascribe the
enumeration of the literal `Cobham.Direction` each shape produces, and instance
search does not delta-reduce the semireducible `Cobham.sig` to match `sig.B a`
against them, as `Geb/Mathlib/Computability/Cobham/Basic.lean` records. That
holds at a constructor shape as much as at a variable one. Splitting the shape
addresses the other obstruction, reducing the `WType.elim`, without which the
equivalence's two sides are not defeq. Neither step alone suffices.

## References

* [HeraudNowak2011]
* [Strahm2003]

## Tags

Cobham, smash-free, subalgebra
-/

@[expose] public section

namespace Geb.CobhamFold

open Cobham RankedAlphabet

universe u

/-- The direction family's enumeration, named at the projection
`Cobham.sig.B` rather than at the literal `Cobham.Direction` that
`Cobham.sigFinitary`'s branches ascribe. Instance search does not delta-reduce
the semireducible `Cobham.sig`, so it does not reach that enumeration at the
form `Cobham.smashFreeBool`'s `decide` quantifies over, at any shape. -/
instance instFinEnumSigB (a : Shape) : FinEnum (sig.B a) := sigFinitary a

/-- A node other than `smash` is smash-free exactly when its children are. -/
theorem smashFreeBool_mk_iff : ∀ (a : Shape) (_ha : a ≠ .smash)
    (f : sig.toPFunctor.B a → sig.toPFunctor.W),
    smashFreeBool (WType.mk a f) = true ↔ ∀ d, smashFreeBool (f d) = true
  | .zero, _, _f => ⟨fun h ↦ of_decide_eq_true h, fun h ↦ decide_eq_true h⟩
  | .proj _ _, _, _f =>
    ⟨fun h ↦ of_decide_eq_true h, fun h ↦ decide_eq_true h⟩
  | .succ _, _, _f =>
    ⟨fun h ↦ of_decide_eq_true h, fun h ↦ decide_eq_true h⟩
  | .smash, h, _ => absurd rfl h
  | .concat, _, _f =>
    ⟨fun h ↦ of_decide_eq_true h, fun h ↦ decide_eq_true h⟩
  | .comp _ _, _, _f =>
    ⟨fun h ↦ of_decide_eq_true h, fun h ↦ decide_eq_true h⟩
  | .boundedRec _, _, _f =>
    ⟨fun h ↦ of_decide_eq_true h, fun h ↦ decide_eq_true h⟩

/-- A node other than `smash` is smash-free when its children are. -/
theorem smashFreeBool_mk (a : Shape) (ha : a ≠ .smash)
    (f : sig.toPFunctor.B a → sig.toPFunctor.W)
    (h : ∀ d, smashFreeBool (f d) = true) :
    smashFreeBool (WType.mk a f) = true :=
  (smashFreeBool_mk_iff a ha f).mpr h

/-- A projection carries no `smash`. -/
theorem smashFreeBool_projRaw (n : ℕ) (i : Fin n) :
    smashFreeBool (WType.mk (.proj n i) Fin.elim0) = true :=
  smashFreeBool_mk _ (by nofun) _ fun d ↦ d.elim0

/-- The empty bitstring carries no `smash`. -/
theorem smashFreeBool_zeroRaw :
    smashFreeBool (WType.mk .zero Fin.elim0) = true :=
  smashFreeBool_mk _ (by nofun) _ fun d ↦ d.elim0

/-- A successor carries no `smash`. -/
theorem smashFreeBool_succRaw (b : Bool) :
    smashFreeBool (WType.mk (.succ b) Fin.elim0) = true :=
  smashFreeBool_mk _ (by nofun) _ fun d ↦ d.elim0

/-- The `concat` generator carries no `smash`. -/
theorem smashFreeBool_concatRaw : smashFreeBool concatRaw = true :=
  smashFreeBool_mk _ (by nofun) _ fun d ↦ d.elim0

/-- A composition carries no `smash` when its head and arguments do. -/
theorem smashFreeBool_compRaw (n m : ℕ) (f : Direction (.comp n m) → sig.toPFunctor.W)
    (h : ∀ d, smashFreeBool (f d) = true) :
    smashFreeBool (WType.mk (.comp n m) f) = true :=
  smashFreeBool_mk _ (by nofun) _ h

/-- A bounded recursion carries no `smash` when its four children do. -/
theorem smashFreeBool_boundedRecRaw (n : ℕ)
    (f : Direction (.boundedRec n) → sig.toPFunctor.W)
    (h : ∀ d, smashFreeBool (f d) = true) :
    smashFreeBool (WType.mk (.boundedRec n) f) = true :=
  smashFreeBool_mk _ (by nofun) _ h

/-- The empty bitstring at an arity carries no `smash`. -/
theorem smashFreeBool_zeroAtRaw (n : ℕ) :
    smashFreeBool (zeroAtRaw n) = true :=
  smashFreeBool_compRaw n 0 _ fun d ↦ match d with
    | .inl () => smashFreeBool_zeroRaw
    | .inr i => i.elim0

/-- Prepending a word carries no `smash` when what it prepends to does. -/
theorem smashFreeBool_prependRaw (n : ℕ) (e : sig.toPFunctor.W)
    (he : smashFreeBool e = true) :
    ∀ u : List Bool, smashFreeBool (prependRaw n u e) = true :=
  List.rec he fun b _ ih ↦
    smashFreeBool_compRaw n 1 _ fun d ↦ match d with
      | .inl () => smashFreeBool_succRaw b
      | .inr _ => ih

/-- The empty bitstring at an arity, as an expression, carries no `smash`. -/
theorem smashFreeBool_zeroAtOf (n : ℕ) :
    smashFreeBool (zeroAtOf n).val.val.val = true := smashFreeBool_zeroAtRaw n

/-- A constant word carries no `smash`. -/
theorem smashFreeBool_constAtOf (n : ℕ) (u : List Bool) :
    smashFreeBool (constAtOf n u).val.val.val = true :=
  smashFreeBool_prependRaw n _ (smashFreeBool_zeroAtRaw n) u

/-- The predecessor carries no `smash`. -/
theorem smashFreeBool_predRaw : smashFreeBool predRaw = true :=
  smashFreeBool_boundedRecRaw 0 _ fun d : Fin 4 ↦ match d with
    | 0 => smashFreeBool_zeroRaw
    | 1 | 2 => smashFreeBool_projRaw 2 0
    | 3 => smashFreeBool_projRaw 1 0

/-- The iterated predecessor carries no `smash`. -/
theorem smashFreeBool_predIterRaw : ∀ k : ℕ,
    smashFreeBool (predIterRaw k) = true :=
  Nat.rec (smashFreeBool_projRaw 1 0) fun _ ih ↦
    smashFreeBool_compRaw 1 1 _ fun d ↦ match d with
      | .inl () => smashFreeBool_predRaw
      | .inr _ => ih

/-- The iterated predecessor expression carries no `smash`. -/
theorem smashFreeBool_predIterOf (k : ℕ) :
    smashFreeBool (predIterOf k).val.val.val = true := smashFreeBool_predIterRaw k

/-- The diagonal carries no `smash` when what it diagonalises does. -/
theorem smashFreeBool_diagRaw (e : sig.toPFunctor.W)
    (he : smashFreeBool e = true) : smashFreeBool (diagRaw e) = true :=
  smashFreeBool_compRaw 1 2 _ fun d ↦ match d with
    | .inl () => he
    | .inr _ => smashFreeBool_projRaw 1 0

/-- A concatenation node carries no `smash` when its arguments do. -/
theorem smashFreeBool_concatCompRaw (n : ℕ) (a b : sig.toPFunctor.W)
    (ha : smashFreeBool a = true) (hb : smashFreeBool b = true) :
    smashFreeBool (concatCompRaw n a b) = true :=
  smashFreeBool_compRaw n 2 _ fun d ↦ match d with
    | .inl () => smashFreeBool_concatRaw
    | .inr i => match i with
      | 0 => ha
      | 1 => hb

/-- The four-way conditional carries no `smash`: its bound child is a
concatenation where [HeraudNowak2011] takes a smash. -/
theorem smashFreeBool_condRaw : smashFreeBool condRaw = true :=
  smashFreeBool_boundedRecRaw 3 _ fun d : Fin 4 ↦ match d with
    | 0 => smashFreeBool_projRaw 3 0
    | 1 => smashFreeBool_projRaw 5 4
    | 2 => smashFreeBool_projRaw 5 3
    | 3 =>
      smashFreeBool_concatCompRaw 4 _ _
        (smashFreeBool_concatCompRaw 4 _ _ (smashFreeBool_projRaw 4 1)
          (smashFreeBool_projRaw 4 2))
        (smashFreeBool_projRaw 4 3)

/-- A shifted expression carries no `smash` when what it shifts does. Its
argument zero is the predecessor of the outer one, so the predecessor's own
freedom enters. -/
theorem smashFreeBool_shiftRaw (e : sig.toPFunctor.W)
    (he : smashFreeBool e = true) : smashFreeBool (shiftRaw e) = true :=
  smashFreeBool_compRaw 2 2 _ fun d ↦ match d with
    | .inl () => he
    | .inr i => match i with
      | 0 =>
        smashFreeBool_compRaw 2 1 _ fun c ↦ match c with
          | .inl () => smashFreeBool_predRaw
          | .inr _ => smashFreeBool_projRaw 2 0
      | 1 => smashFreeBool_projRaw 2 1

/-- A lifted step carries no `smash` when what it lifts does. -/
theorem smashFreeBool_liftRaw (e : sig.toPFunctor.W)
    (he : smashFreeBool e = true) : smashFreeBool (liftRaw e) = true :=
  smashFreeBool_compRaw 2 1 _ fun d ↦ match d with
    | .inl () => he
    | .inr _ => smashFreeBool_projRaw 2 1

/-- A case tree carries no `smash` when every branch does. The recursion is the
one `Cobham.wValid_casesRaw` performs, the motive generalizing over the branch
family. -/
theorem smashFreeBool_casesRaw : ∀ (p : ℕ) (br : (Fin p → Bool) → sig.toPFunctor.W),
    (∀ v, smashFreeBool (br v) = true) → smashFreeBool (casesRaw p br) = true :=
  Nat.rec (fun _br h ↦ smashFreeBool_liftRaw _ (h _))
    fun _p ih _br h ↦
      smashFreeBool_compRaw 2 4 _ fun d ↦ match d with
        | .inl () => smashFreeBool_condRaw
        | .inr i => match i with
          | 0 => smashFreeBool_projRaw 2 0
          | 1 => smashFreeBool_shiftRaw _ (ih _ fun _ ↦ h _)
          | 2 => smashFreeBool_shiftRaw _ (ih _ fun _ ↦ h _)
          | 3 => smashFreeBool_shiftRaw _ (ih _ fun _ ↦ h _)

/-- The multiplier carries no `smash`. -/
theorem smashFreeBool_multRaw : ∀ mult : ℕ,
    smashFreeBool (multRaw mult) = true :=
  Nat.rec (smashFreeBool_zeroAtRaw 1) fun _ ih ↦
    smashFreeBool_concatCompRaw 1 _ _ ih (smashFreeBool_projRaw 1 0)

/-- The multiplicative bound child carries no `smash`, at every multiplicity and
growth. -/
theorem smashFreeBool_boundMulRaw (mult growth : ℕ) :
    smashFreeBool (boundMulRaw mult growth) = true :=
  smashFreeBool_prependRaw 1 _ (smashFreeBool_multRaw mult) _

/-- The arity-two scan node carries no `smash` when its four children do. -/
theorem smashFreeBool_scan2Raw (base step₀ step₁ bnd : sig.toPFunctor.W)
    (hb : smashFreeBool base = true) (h₀ : smashFreeBool step₀ = true)
    (h₁ : smashFreeBool step₁ = true) (hn : smashFreeBool bnd = true) :
    smashFreeBool (scan2Raw base step₀ step₁ bnd) = true :=
  smashFreeBool_boundedRecRaw 0 _ fun d : Fin 4 ↦ match d with
    | 0 => hb
    | 1 => h₀
    | 2 => h₁
    | 3 => hn

/-- The scan node at an arbitrary bound child carries no `smash` when its
components do. -/
theorem smashFreeBool_scanBRaw (base step₀ step₁ bnd : sig.toPFunctor.W)
    (hb : smashFreeBool base = true) (h₀ : smashFreeBool step₀ = true)
    (h₁ : smashFreeBool step₁ = true) (hn : smashFreeBool bnd = true) :
    smashFreeBool (scanBRaw base step₀ step₁ bnd) = true :=
  smashFreeBool_scan2Raw base _ _ bnd hb (smashFreeBool_liftRaw _ h₀)
    (smashFreeBool_liftRaw _ h₁) hn

/-- A composition of expressions carries no `smash` when its head and arguments
do. -/
theorem smashFreeBool_compOf {n m : ℕ} (head : COf m) (args : Fin m → COf n)
    (hh : smashFreeBool head.val.val.val = true)
    (ha : ∀ i, smashFreeBool (args i).val.val.val = true) :
    smashFreeBool (compOf head args).val.val.val = true :=
  smashFreeBool_compRaw n m _ fun d ↦ match d with
    | .inl () => hh
    | .inr i => ha i

/-- The case combinator carries no `smash` when every branch does. -/
theorem smashFreeBool_casesOf (p : ℕ) (br : (Fin p → Bool) → COf 1)
    (h : ∀ v, smashFreeBool (br v).val.val.val = true) :
    smashFreeBool (casesOf p br).val.val.val = true :=
  smashFreeBool_casesRaw p _ h

/-- The diagonal of a case tree whose branches all carry no `smash` carries
none: the shape every step and readout of both fold constructions takes. -/
theorem smashFreeBool_diagCasesOf (p : ℕ) (br : (Fin p → Bool) → COf 1)
    (h : ∀ v, smashFreeBool (br v).val.val.val = true) :
    smashFreeBool (diagOf (casesOf p br)).val.val.val = true :=
  smashFreeBool_diagRaw _ (smashFreeBool_casesOf p br h)

/-- The fixed-width readout carries no `smash`: every branch is a constant
word. -/
theorem smashFreeBool_readOf {α : Type u} {p : ℕ} (R : RankedAlphabet)
    (enc : α → Fin p → Bool) (dec : (Fin p → Bool) → α) :
    smashFreeBool (readOf R p enc dec).val.val.val = true :=
  smashFreeBool_diagCasesOf _ _ fun _ ↦ smashFreeBool_constAtOf 1 _

/-- A step of the fixed-width fold carries no `smash`: every branch prepends a
constant word to an iterated predecessor. -/
theorem smashFreeBool_foldStepF {α : Type u} {p : ℕ} (R : RankedAlphabet)
    (enc : α → Fin p → Bool) (dec : (Fin p → Bool) → α)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (b : Bool) :
    smashFreeBool (foldStepF R p enc dec alg b).val.val.val = true :=
  smashFreeBool_diagCasesOf _ _ fun _ ↦
    smashFreeBool_prependRaw 1 _ (smashFreeBool_predIterOf _) _

/-- The fixed-width fold lies in the subalgebra `Cobham.SmashFree` names, at a
symbolic alphabet, a symbolic carrier width and an arbitrary algebra. With
[Strahm2003] Theorem 1(2)'s left-to-right inclusion it is computable
simultaneously in polynomial time and linear space. -/
theorem smashFree_foldOutExpr {α : Type u} {p : ℕ} (R : RankedAlphabet)
    (enc : α → Fin p → Bool) (dec : (Fin p → Bool) → α)
    (hdec : ∀ a, dec (enc a) = a)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (mult : ℕ)
    (hmult : p + 1 ≤ mult * R.width) :
    SmashFree (foldOutExpr R p enc dec hdec alg mult hmult) :=
  smashFreeBool_compRaw 1 1 _ fun d ↦ match d with
    | .inl () => smashFreeBool_readOf R enc dec
    | .inr _ =>
      smashFreeBool_scanBRaw _ _ _ _ (smashFreeBool_constAtOf 0 _)
        (smashFreeBool_foldStepF R enc dec alg false)
        (smashFreeBool_foldStepF R enc dec alg true)
        (smashFreeBool_boundMulRaw mult (foldGrowth R))

/-- The additive bound child carries no `smash`. -/
theorem smashFreeBool_boundRaw : ∀ growth : ℕ,
    smashFreeBool (boundRaw growth) = true :=
  Nat.rec (smashFreeBool_projRaw 1 0) fun _ ih ↦
    smashFreeBool_compRaw 1 1 _ fun d ↦ match d with
      | .inl () => smashFreeBool_succRaw true
      | .inr _ => ih

/-- The arity-two scan combinator carries no `smash` when its base and steps
do. -/
theorem smashFreeBool_scan2Of (base : COf 0) (step₀ step₁ : COf 2)
    (hbound : ∀ w : List Bool, (scan2Sem base step₀ step₁ ![w]).length ≤ w.length)
    (hb : smashFreeBool base.val.val.val = true)
    (h₀ : smashFreeBool step₀.val.val.val = true)
    (h₁ : smashFreeBool step₁.val.val.val = true) :
    smashFreeBool (scan2Of base step₀ step₁ hbound).val.val.val = true :=
  smashFreeBool_scan2Raw _ _ _ _ hb h₀ h₁ (smashFreeBool_boundRaw 0)

/-- A projection expression carries no `smash`. -/
theorem smashFreeBool_projOf (n : ℕ) (i : Fin n) :
    smashFreeBool (projOf n i).val.val.val = true := smashFreeBool_projRaw n i

/-- An arity-one composition carries no `smash` when its parts do. -/
theorem smashFreeBool_comp1Of {n : ℕ} (e : COf 1) (a : COf n)
    (he : smashFreeBool e.val.val.val = true) (ha : smashFreeBool a.val.val.val = true) :
    smashFreeBool (comp1Of e a).val.val.val = true :=
  smashFreeBool_compOf e _ he fun _ ↦ ha

/-- A concatenation of expressions carries no `smash` when its parts do. -/
theorem smashFreeBool_concatCompOf (n : ℕ) (a b : COf n)
    (ha : smashFreeBool a.val.val.val = true) (hb : smashFreeBool b.val.val.val = true) :
    smashFreeBool (concatCompOf n a b).val.val.val = true :=
  smashFreeBool_compOf concatOf _ smashFreeBool_concatRaw fun i ↦ match i with
    | 0 => ha
    | 1 => hb

/-- Prepending a word to an expression carries no `smash` when the expression
does. -/
theorem smashFreeBool_prependOf {n : ℕ} (u : List Bool) (e : COf n)
    (he : smashFreeBool e.val.val.val = true) :
    smashFreeBool (prependOf u e).val.val.val = true :=
  smashFreeBool_prependRaw n _ he u

/-- The identity carries no `smash`. -/
theorem smashFreeBool_idOf : smashFreeBool idOf.val.val.val = true :=
  smashFreeBool_projOf 1 0

/-- The first-bit primitive carries no `smash`. -/
theorem smashFreeBool_firstBitOf : smashFreeBool firstBitOf.val.val.val = true :=
  smashFreeBool_scan2Of _ _ _ _ (smashFreeBool_zeroAtRaw 0)
    (smashFreeBool_constAtOf 2 _) (smashFreeBool_constAtOf 2 _)

/-- The unary primitive carries no `smash`. -/
theorem smashFreeBool_unaryOf : smashFreeBool unaryOf.val.val.val = true :=
  smashFreeBool_scan2Of _ _ _ _ (smashFreeBool_zeroAtRaw 0)
    (smashFreeBool_prependOf _ _ (smashFreeBool_projOf 2 1))
    (smashFreeBool_prependOf _ _ (smashFreeBool_projOf 2 1))

/-- The run primitive carries no `smash`. -/
theorem smashFreeBool_takeUnaryOf :
    smashFreeBool takeUnaryOf.val.val.val = true :=
  smashFreeBool_scan2Of _ _ _ _ (smashFreeBool_zeroAtRaw 0)
    (smashFreeBool_zeroAtRaw 2)
    (smashFreeBool_prependOf _ _ (smashFreeBool_projOf 2 1))

/-- The prefix-dropping primitive carries no `smash`. -/
theorem smashFreeBool_dropUnaryOf :
    smashFreeBool dropUnaryOf.val.val.val = true :=
  smashFreeBool_scan2Of _ _ _ _ (smashFreeBool_zeroAtRaw 0)
    (smashFreeBool_projOf 2 0) (smashFreeBool_projOf 2 1)

/-- The entry-dropping primitive carries no `smash`. -/
theorem smashFreeBool_dropEntryOf :
    smashFreeBool dropEntryOf.val.val.val = true :=
  smashFreeBool_scan2Of _ _ _ _ (smashFreeBool_zeroAtRaw 0)
    (smashFreeBool_projOf 2 0)
    (smashFreeBool_comp1Of _ _ smashFreeBool_predRaw (smashFreeBool_projOf 2 1))

/-- The payload primitive carries no `smash`. -/
theorem smashFreeBool_takeEntryOf :
    smashFreeBool takeEntryOf.val.val.val = true :=
  smashFreeBool_scan2Of _ _ _ _ (smashFreeBool_zeroAtRaw 0)
    (smashFreeBool_zeroAtRaw 2)
    (smashFreeBool_concatCompOf 2 _ _
      (smashFreeBool_comp1Of _ _ smashFreeBool_firstBitOf
        (smashFreeBool_comp1Of _ _ smashFreeBool_dropEntryOf
          (smashFreeBool_projOf 2 0)))
      (smashFreeBool_projOf 2 1))

/-- Dropping a fixed number of entries carries no `smash`. -/
theorem smashFreeBool_dropEntriesOf : ∀ k : ℕ,
    smashFreeBool (dropEntriesOf k).val.val.val = true :=
  Nat.rec smashFreeBool_idOf fun _ ih ↦
    smashFreeBool_comp1Of _ _ ih smashFreeBool_dropEntryOf

/-- The `j`-th entry carries no `smash`. -/
theorem smashFreeBool_entryOf (j : ℕ) :
    smashFreeBool (entryOf j).val.val.val = true :=
  smashFreeBool_comp1Of _ _ smashFreeBool_takeEntryOf
    (smashFreeBool_dropEntriesOf j)

/-- The self-delimiting spelling carries no `smash`. -/
theorem smashFreeBool_entryWordOf :
    smashFreeBool entryWordOf.val.val.val = true :=
  smashFreeBool_concatCompOf 1 _ _
    (smashFreeBool_prependOf _ _ smashFreeBool_idOf) smashFreeBool_unaryOf

/-- The algebra applied to the stack's entries carries no `smash` when the
algebra's expression does. This is where the bitstring construction's hypothesis
enters: the algebra is spliced into the tree, so its own freedom is needed. -/
theorem smashFreeBool_applyAlgOf {r : ℕ} (algI : COf r)
    (h : smashFreeBool algI.val.val.val = true) :
    smashFreeBool (applyAlgOf algI).val.val.val = true :=
  smashFreeBool_compOf algI _ h fun j ↦ smashFreeBool_entryOf j.val

/-- The rebuilt stack carries no `smash` when the algebra's expression does. -/
theorem smashFreeBool_newStackOf {r : ℕ} (algI : COf r)
    (h : smashFreeBool algI.val.val.val = true) :
    smashFreeBool (newStackOf algI).val.val.val = true :=
  smashFreeBool_concatCompOf 1 _ _ (smashFreeBool_dropEntriesOf r)
    (smashFreeBool_comp1Of _ _ smashFreeBool_entryWordOf
      (smashFreeBool_applyAlgOf algI h))

/-- The state past the flag and the slot, rebuilt, carries no `smash` when the
algebra's expression does. -/
theorem smashFreeBool_rebuildOf {r : ℕ} (algI : COf r)
    (h : smashFreeBool algI.val.val.val = true) :
    smashFreeBool (rebuildOf algI).val.val.val = true :=
  smashFreeBool_concatCompOf 1 _ _
    (smashFreeBool_prependOf _ _
      (smashFreeBool_comp1Of _ _ (smashFreeBool_newStackOf algI h)
        smashFreeBool_dropUnaryOf))
    smashFreeBool_takeUnaryOf

/-- Every branch of a step of the bitstring fold carries no `smash` when the
algebra's expressions do. -/
theorem smashFreeBool_branchV (R : RankedAlphabet)
    (algOf : (i : Fin R.card) → COf (R.arity i))
    (halg : ∀ i, smashFreeBool (algOf i).val.val.val = true) (b : Bool) (t : Scan) :
    smashFreeBool (branchV R algOf b t).val.val.val = true := by
  obtain ⟨buf, depth, live⟩ := t
  rw [branchV]
  dsimp only
  cases live
  · exact smashFreeBool_idOf
  · dsimp only
    by_cases hlen : (b :: buf).length = R.width
    · rw [if_pos hlen]
      match symOf R (decodeBits (b :: buf)) with
      | none => exact smashFreeBool_prependOf _ _ (smashFreeBool_predIterOf _)
      | some i =>
        dsimp only
        by_cases hst : R.arity i ≤ depth
        · rw [if_pos hst]
          exact smashFreeBool_prependOf _ _
            (smashFreeBool_comp1Of _ _ (smashFreeBool_rebuildOf _ (halg i))
              (smashFreeBool_predIterOf _))
        · rw [if_neg hst]
          exact smashFreeBool_prependOf _ _ (smashFreeBool_predIterOf _)
    · rw [if_neg hlen]
      exact smashFreeBool_prependOf _ _ (smashFreeBool_predIterOf _)

/-- A step of the bitstring fold carries no `smash` when the algebra's
expressions do. -/
theorem smashFreeBool_foldStepV (R : RankedAlphabet)
    (algOf : (i : Fin R.card) → COf (R.arity i))
    (halg : ∀ i, smashFreeBool (algOf i).val.val.val = true) (b : Bool) :
    smashFreeBool (foldStepV R algOf b).val.val.val = true :=
  smashFreeBool_diagCasesOf _ _ fun _ ↦ smashFreeBool_branchV R algOf halg b _

/-- The bitstring readout carries no `smash`: one branch prepends a marker to
the payload primitive, the other is a constant word. -/
theorem smashFreeBool_readOfV (R : RankedAlphabet) :
    smashFreeBool (readOfV R).val.val.val = true :=
  smashFreeBool_diagCasesOf _ _ fun v ↦ by
    by_cases hacc : ((decodeVAt R (readoutWidthV R) v).live &&
        (decodeVAt R (readoutWidthV R) v).buf.isEmpty &&
        (decodeVAt R (readoutWidthV R) v).depth == 1) = true
    · rw [if_pos hacc]
      exact smashFreeBool_prependOf _ _
        (smashFreeBool_comp1Of _ _ smashFreeBool_takeEntryOf
          (smashFreeBool_predIterOf _))
    · rw [if_neg hacc]
      exact smashFreeBool_constAtOf 1 _

/-- The fold at a bitstring carrier lies in the subalgebra `Cobham.SmashFree`
names when the algebra's expressions do, at a symbolic alphabet. The hypothesis
is on the algebra alone, the construction's own nodes contributing no `smash`;
whether it is necessary is not stated here. With [Strahm2003] Theorem 1(2)'s
left-to-right inclusion
the fold is then computable simultaneously in polynomial time and linear
space. -/
theorem smashFree_foldOutExprV (R : RankedAlphabet)
    (algOf : (i : Fin R.card) → COf (R.arity i))
    (halg' : ∀ i, smashFreeBool (algOf i).val.val.val = true)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool)
    (halg : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      semAt (R.arity i) (algOf i).val.val (algOf i).property f = alg i f)
    (mult c : ℕ)
    (hsize : ∀ w : List Bool,
      stackSize (foldScanFinal R alg w).stack ≤ c * w.length)
    (hmult : 2 * c + 2 ≤ mult) :
    SmashFree (foldOutExprV R algOf alg halg mult c hsize hmult) :=
  smashFreeBool_compRaw 1 1 _ fun d ↦ match d with
    | .inl () => smashFreeBool_readOfV R
    | .inr _ =>
      smashFreeBool_scanBRaw _ _ _ _ (smashFreeBool_constAtOf 0 _)
        (smashFreeBool_foldStepV R algOf halg' false)
        (smashFreeBool_foldStepV R algOf halg' true)
        (smashFreeBool_boundMulRaw mult (foldGrowthV R))

end Geb.CobhamFold

end
