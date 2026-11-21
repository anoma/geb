/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.CobhamFoldProto.Bound

/-!
# Self-delimiting bitstrings in Cobham's class

A stack whose entries are bitstrings of varying length needs entries that
delimit themselves, and a step that reads one needs to parse it. This module
supplies the parsing primitives as expressions of Cobham's class.

An entry spelling the payload `u` is `List.replicate u.length true` followed by
`false` followed by `u`: a unary length prefix, read from the list's head, which
is the end a step of the outer scan pops from.

`Cobham.scan` lifts steps of arity one, applying them to the recursive value
alone. `dropUnaryOf`, `dropEntryOf` and `takeEntryOf` need the remaining word as
well,
which `Cobham.evalRec` supplies in slot zero of a step's environment, so `scan2`
takes its steps at arity two directly.

`takeEntryOf` is the one whose use of it is least avoidable. Its recursion
appends a bit at the *end* of the payload accumulated so far, which is not a
head operation; the `concat` generator supplies the append, and the appended bit is read
off the remaining word by `firstBitOf` after `dropEntryOf`. Without slot zero the
payload would not be extractable and the algebra could not be applied.

## Main definitions

* `Geb.CobhamFold.scan2` — the arity-two scan node as an expression;
  `Geb.CobhamFold.scan2Raw` itself lives with the scan combinators in
  `Geb/Prototypes/Computability/CobhamFoldProto/Bound.lean`.
* `Geb.CobhamFold.entryWord` — the self-delimiting spelling of a payload.
* `Geb.CobhamFold.firstBitOf`, `Geb.CobhamFold.unaryOf`,
  `Geb.CobhamFold.takeUnaryOf`, `Geb.CobhamFold.dropUnaryOf`,
  `Geb.CobhamFold.dropEntryOf`, `Geb.CobhamFold.takeEntryOf` — the parsing
  primitives.
* `Geb.CobhamFold.idOf`, `Geb.CobhamFold.dropEntriesOf`,
  `Geb.CobhamFold.entryOf` — the identity, and the primitives iterated to reach
  the `j`-th entry. The composition combinators they are built from live in
  `Geb/Prototypes/Computability/CobhamFoldProto/Bound.lean`.

## Main statements

* `Geb.CobhamFold.scan2Sem_nil`, `Geb.CobhamFold.scan2Sem_cons` — the arity-two
  scan on the empty word and on one bit.
* `Geb.CobhamFold.stepWord_firstBitOf`, `Geb.CobhamFold.stepWord_unaryOf`,
  `Geb.CobhamFold.stepWord_takeUnaryOf`,
  `Geb.CobhamFold.stepWord_dropUnaryOf`,
  `Geb.CobhamFold.stepWord_dropEntryOf`,
  `Geb.CobhamFold.stepWord_takeEntryOf` — what each primitive computes.
* `Geb.CobhamFold.take_succ_append_take_one` — a truncation splits at its
  last bit.
* `Geb.CobhamFold.takeEntrySem_entryWord`,
  `Geb.CobhamFold.dropEntrySem_entryWord` — the payload and the remainder of a
  self-delimiting entry.
* `Geb.CobhamFold.two_mul_length_takeEntrySem_add_length_dropEntrySem_le` —
  the payload counted twice and the remainder fit inside the word.

* `Geb.CobhamFold.scan2Sem_eq_eval` — the meaning read at the raw tree is the
  meaning the expression carries.

## Implementation notes

Every primitive's value is no longer than its argument, so each takes
`Cobham.boundRaw 0` as its bound child: the recursion variable itself dominates.
The bounds are established over arbitrary words, not only over well-formed
entries, since `Cobham.RecBoundedValue` quantifies over every environment.

Each primitive recurses over the whole word, not over the entry it reads.
`Cobham.evalRec` recurses to the empty word whatever the value depends on, so
`dropEntryOf` touches every bit of its argument although, at an entry spelling
the payload `u`, the first `2 * u.length + 1` bits are what fix where its value
starts. Their steps are not constant either: `dropEntryOf`'s
applies `Cobham.pred`, itself a `boundedRec`, and `takeEntryOf`'s runs a fresh
`dropEntryOf` over the remaining word, so counting a `boundedRec`'s cost as the
sum over its levels of its step's cost makes `dropEntryOf` quadratic in its
argument and `takeEntryOf` cubic.

Nothing here measures a number of reduction steps, as
`Geb/Mathlib/Computability/Cobham/Tree.lean` records of its own subject; the
paragraph above analyses the expression under one cost model.

The accompanying lower bound rests only on the class's shape rather than on a
cost model: reading an unbounded field of the state requires a recursion over
the state, `boundedRec` being the class's only recursion. It is an argument
about the expression, not a theorem stated here.

That gives a dichotomy rather than a spectrum, in what a step reads rather than
in what it costs. A carrier whose values are bounded by a constant is the
fixed-width case — pad to that constant and dispatch on a constant window, and
no step reads an unbounded field. A carrier whose values are unbounded needs
entries of this shape, and every step reads one. There is no intermediate
regime, a bound of any constant `B` being the fixed-width case at width `B`.
Neither case has constant-time steps: reading even a bounded prefix of the state
goes through a `boundedRec` over the state.

Only `boundedRec` nodes carry a `Cobham.RecBoundedValue` obligation, `comp`'s
being vacuous, so composing these primitives imposes no further bound. This is
why `entryWord`'s spelling, which is longer than its argument, needs no growth
allowance: it is a composition, not a recursion.

## References

* [Cobham1965]

## Tags

Cobham, bounded recursion on notation, self-delimiting, prefix code
-/

@[expose] public section

namespace Geb.CobhamFold

open Cobham

/-- The arity-two scan node over expressions, carrying its admissibility. -/
def scan2W (base : COf 0) (step₀ step₁ : COf 2) : sig.W :=
  ⟨scan2Raw base.val.val.val step₀.val.val.val step₁.val.val.val (boundRaw 0),
    wValid_scan2Raw _ _ _ _ base.val.val.property base.property step₀.val.val.property
      step₀.property step₁.val.val.property step₁.property (wValid_boundRaw 0)
      (wIndexRoot_boundRaw 0)⟩

/-- The arity-two scan node's arity. -/
theorem arity_scan2W (base : COf 0) (step₀ step₁ : COf 2) :
    arity (scan2W base step₀ step₁) = 1 := rfl

/-- The meaning of the arity-two scan at its arity. -/
def scan2Sem (base : COf 0) (step₀ step₁ : COf 2) : Sem 1 :=
  semAt 1 (scan2W base step₀ step₁) (arity_scan2W base step₀ step₁)

/-- The word an arity-two step contributes at the remaining word and the
recursive value. -/
def step2Word (e : COf 2) (v r : List Bool) : List Bool :=
  semAt 2 e.val.val e.property ![v, r]

/-- The arity-two scan on the empty bitstring is its base's word. -/
theorem scan2Sem_nil (base : COf 0) (step₀ step₁ : COf 2) :
    scan2Sem base step₀ step₁ ![[]] = baseWord base := rfl

/-- One step of the arity-two scan, which reads the remaining word as well as
the value the scan of that word returns. -/
theorem scan2Sem_cons (base : COf 0) (step₀ step₁ : COf 2) (b : Bool)
    (w : List Bool) :
    scan2Sem base step₀ step₁ ![b :: w] =
      step2Word (if b then step₁ else step₀) w (scan2Sem base step₀ step₁ ![w]) := by
  have hfun : ∀ v r : List Bool,
      (Fin.cons v (Fin.cons r Fin.elim0) : Fin 2 → List Bool) = ![v, r] :=
    fun v r ↦ funext fun i ↦ match i with | 0 => rfl | 1 => rfl
  cases b
  · change transport ((fst_eval step₀.val.val).trans step₀.property) (eval step₀.val.val).2
      (Fin.cons w (Fin.cons (scan2Sem base step₀ step₁ ![w]) Fin.elim0)) = _
    exact congrArg _ (hfun _ _)
  · change transport ((fst_eval step₁.val.val).trans step₁.property) (eval step₁.val.val).2
      (Fin.cons w (Fin.cons (scan2Sem base step₀ step₁ ![w]) Fin.elim0)) = _
    exact congrArg _ (hfun _ _)

/-- The arity-two scan as an expression of the class, its recursion bounded by
the recursion variable itself. -/
def scan2 (base : COf 0) (step₀ step₁ : COf 2)
    (hbound : ∀ w : List Bool, (scan2Sem base step₀ step₁ ![w]).length ≤ w.length) :
    C :=
  ⟨scan2W base step₀ step₁, by
    refine ⟨fun x ↦ ?_, ?_⟩
    · rw [(funext fun i ↦ i.elim0 : Fin.tail x = Fin.tail ![x 0])]
      change _ ≤ (boundSem 0 x).length
      rw [boundSem_eq]
      exact hbound (x 0)
    · refine fun b : Fin 4 ↦ ?_
      match b with
      | 0 => exact base.val.property
      | 1 => exact step₀.val.property
      | 2 => exact step₁.val.property
      | 3 => exact recBounded_boundRaw 0⟩

/-- `scan2` at its declared arity. -/
def scan2Of (base : COf 0) (step₀ step₁ : COf 2)
    (hbound : ∀ w : List Bool, (scan2Sem base step₀ step₁ ![w]).length ≤ w.length) :
    COf 1 :=
  ⟨scan2 base step₀ step₁ hbound, rfl⟩

/-- The meaning read at the raw tree is the meaning the expression carries. -/
theorem scan2Sem_eq_eval (base : COf 0) (step₀ step₁ : COf 2)
    (hbound : ∀ w : List Bool, (scan2Sem base step₀ step₁ ![w]).length ≤ w.length) :
    transport (scan2Of base step₀ step₁ hbound).property
        (scan2Of base step₀ step₁ hbound).val.eval =
      scan2Sem base step₀ step₁ := rfl

/-- Prepending a word prepends it to what an arity-two step contributes. -/
theorem step2Word_prependOf (e : COf 2) (v r : List Bool) :
    ∀ u : List Bool, step2Word (prependOf u e) v r = u ++ step2Word e v r :=
  semAt_prependOf e ![v, r]

/-- A constant arity-two step contributes its word, whatever it reads. -/
theorem step2Word_constAtOf (u v r : List Bool) :
    step2Word (constAtOf 2 u) v r = u :=
  (step2Word_prependOf (zeroAtOf 2) v r u).trans (List.append_nil u)

/-- A projection contributes the slot it names. -/
theorem step2Word_projOf (i : Fin 2) (v r : List Bool) :
    step2Word (projOf 2 i) v r = ![v, r] i := semAt_projOf 2 i ![v, r]

/-- A composition contributes its head's value at its argument's. -/
theorem step2Word_comp1Of (e : COf 1) (a : COf 2) (v r : List Bool) :
    step2Word (comp1Of e a) v r = stepWord e (step2Word a v r) :=
  congrArg (semAt 1 e.val.val e.property) (funext fun i ↦ match i with | ⟨0, _⟩ => rfl)

/-- A concatenation contributes its second argument's value followed by its
first's. -/
theorem step2Word_concatCompOf (a b : COf 2) (v r : List Bool) :
    step2Word (concatCompOf 2 a b) v r =
      step2Word b v r ++ step2Word a v r :=
  semAt_concatCompOf 2 a b ![v, r]

/-- The predecessor's value at an arity-one step. -/
theorem stepWord_pred (u : List Bool) : stepWord pred u = u.tail :=
  (stepWord_eq_eval pred u).trans (predSem_eq u)

/-- The first bit of a word, absent at the empty word. -/
def firstBitSem : Sem 1 :=
  scan2Sem (zeroAtOf 0) (constAtOf 2 [false]) (constAtOf 2 [true])

/-- What the first-bit primitive computes. -/
theorem firstBitSem_eq : ∀ w : List Bool,
    firstBitSem ![w] = match w with | [] => [] | b :: _ => [b]
  | [] => rfl
  | b :: v => by
    change scan2Sem _ _ _ ![b :: v] = _
    rw [scan2Sem_cons]
    cases b <;> exact step2Word_constAtOf _ _ _

/-- The first-bit primitive never lengthens its argument. -/
theorem length_firstBitSem_le (w : List Bool) : (firstBitSem ![w]).length ≤ w.length := by
  rw [firstBitSem_eq]
  match w with
  | [] => exact Nat.le_refl 0
  | _ :: _ =>
    rw [List.length_cons, List.length_cons, List.length_nil]
    omega

/-- The first bit of a word as an expression of arity one. -/
def firstBitOf : COf 1 :=
  scan2Of (zeroAtOf 0) (constAtOf 2 [false]) (constAtOf 2 [true])
    length_firstBitSem_le

/-- The first-bit expression's value at a step. -/
@[simp] theorem stepWord_firstBitOf (w : List Bool) :
    stepWord firstBitOf w = firstBitSem ![w] := rfl

/-- A word's length in unary. -/
def unarySem : Sem 1 :=
  scan2Sem (zeroAtOf 0) (prependOf [true] (projOf 2 1))
    (prependOf [true] (projOf 2 1))

/-- One step of the unary primitive: each bit read contributes a `true`. -/
theorem unarySem_cons (b : Bool) (v : List Bool) :
    unarySem ![b :: v] = true :: unarySem ![v] := by
  change scan2Sem _ _ _ ![b :: v] = _
  rw [scan2Sem_cons]
  cases b <;>
    exact (step2Word_prependOf (projOf 2 1) v _ [true]).trans
      (congrArg (fun t ↦ true :: t) (step2Word_projOf 1 v _))

/-- The unary primitive spells its argument's length. -/
theorem unarySem_eq : ∀ w : List Bool,
    unarySem ![w] = List.replicate w.length true :=
  List.rec rfl fun b v ih ↦ by
    rw [unarySem_cons, ih, List.length_cons, List.replicate_succ]

/-- The unary primitive never lengthens its argument. -/
theorem length_unarySem_le (w : List Bool) : (unarySem ![w]).length ≤ w.length := by
  rw [unarySem_eq, List.length_replicate]

/-- A word's length in unary, as an expression of arity one. -/
def unaryOf : COf 1 :=
  scan2Of (zeroAtOf 0) (prependOf [true] (projOf 2 1))
    (prependOf [true] (projOf 2 1)) length_unarySem_le

/-- The unary expression's value at a step. -/
@[simp] theorem stepWord_unaryOf (w : List Bool) :
    stepWord unaryOf w = unarySem ![w] := rfl

/-- The word past a unary length prefix and its sentinel. -/
def dropUnarySem : Sem 1 := scan2Sem (zeroAtOf 0) (projOf 2 0) (projOf 2 1)

/-- The prefix-dropping primitive on the empty word. -/
theorem dropUnarySem_nil : dropUnarySem ![[]] = [] := rfl

/-- What the prefix-dropping primitive computes: a `true` keeps the recursive
value, a `false` ends the prefix and returns the remaining word. -/
theorem dropUnarySem_cons (b : Bool) (v : List Bool) :
    dropUnarySem ![b :: v] = if b then dropUnarySem ![v] else v := by
  change scan2Sem _ _ _ ![b :: v] = _
  rw [scan2Sem_cons]
  cases b
  · exact step2Word_projOf 0 v _
  · exact step2Word_projOf 1 v _

/-- The prefix-dropping primitive never lengthens its argument. -/
theorem length_dropUnarySem_le : ∀ w : List Bool,
    (dropUnarySem ![w]).length ≤ w.length :=
  List.rec (Nat.le_refl 0) fun b v ih ↦ by
    rw [dropUnarySem_cons, List.length_cons]
    cases b
    · rw [if_neg (by simp)]
      omega
    · rw [if_pos rfl]
      omega

/-- The word past a unary length prefix, as an expression of arity one. -/
def dropUnaryOf : COf 1 :=
  scan2Of (zeroAtOf 0) (projOf 2 0) (projOf 2 1) length_dropUnarySem_le

/-- The prefix-dropping expression's value at a step. -/
@[simp] theorem stepWord_dropUnaryOf (w : List Bool) :
    stepWord dropUnaryOf w = dropUnarySem ![w] := rfl

/-- The word past a whole self-delimiting entry. -/
def dropEntrySem : Sem 1 :=
  scan2Sem (zeroAtOf 0) (projOf 2 0) (comp1Of pred (projOf 2 1))

/-- The entry-dropping primitive on the empty word. -/
theorem dropEntrySem_nil : dropEntrySem ![[]] = [] := rfl

/-- What the entry-dropping primitive computes: a `true` lengthens the prefix by
one and so drops one more payload bit, and a `false` ends the prefix. -/
theorem dropEntrySem_cons (b : Bool) (v : List Bool) :
    dropEntrySem ![b :: v] = if b then (dropEntrySem ![v]).tail else v := by
  change scan2Sem _ _ _ ![b :: v] = _
  rw [scan2Sem_cons]
  cases b
  · exact step2Word_projOf 0 v _
  · refine (step2Word_comp1Of pred (projOf 2 1) v _).trans ?_
    rw [step2Word_projOf]
    exact stepWord_pred _

/-- The entry-dropping primitive never lengthens its argument. -/
theorem length_dropEntrySem_le : ∀ w : List Bool,
    (dropEntrySem ![w]).length ≤ w.length :=
  List.rec (Nat.le_refl 0) fun b v ih ↦ by
    rw [dropEntrySem_cons, List.length_cons]
    cases b
    · rw [if_neg (by simp)]
      omega
    · rw [if_pos rfl, List.length_tail]
      omega

/-- The word past a whole self-delimiting entry, as an expression of arity
one. -/
def dropEntryOf : COf 1 :=
  scan2Of (zeroAtOf 0) (projOf 2 0) (comp1Of pred (projOf 2 1))
    length_dropEntrySem_le

/-- The entry-dropping expression's value at a step. -/
@[simp] theorem stepWord_dropEntryOf (w : List Bool) :
    stepWord dropEntryOf w = dropEntrySem ![w] := rfl

/-- The payload of a self-delimiting entry. -/
def takeEntrySem : Sem 1 :=
  scan2Sem (zeroAtOf 0) (zeroAtOf 2)
    (concatCompOf 2 (comp1Of firstBitOf (comp1Of dropEntryOf (projOf 2 0)))
      (projOf 2 1))

/-- The payload primitive on the empty word. -/
theorem takeEntrySem_nil : takeEntrySem ![[]] = [] := rfl

/-- What the payload primitive computes. The `true` clause appends one bit at
the payload's end, which the `concat` generator supplies and which is read off the
remaining word rather than off the recursive value. -/
theorem takeEntrySem_cons (b : Bool) (v : List Bool) :
    takeEntrySem ![b :: v] =
      if b then takeEntrySem ![v] ++ firstBitSem ![dropEntrySem ![v]] else [] := by
  change scan2Sem _ _ _ ![b :: v] = _
  rw [scan2Sem_cons]
  cases b
  · exact step2Word_constAtOf [] v _
  · refine (step2Word_concatCompOf _ _ v _).trans ?_
    rw [step2Word_projOf, step2Word_comp1Of, step2Word_comp1Of,
      step2Word_projOf]
    rfl

/-- The payload primitive never lengthens its argument. -/
theorem length_takeEntrySem_le : ∀ w : List Bool,
    (takeEntrySem ![w]).length ≤ w.length :=
  List.rec (Nat.le_refl 0) fun b v ih ↦ by
    rw [takeEntrySem_cons, List.length_cons]
    cases b
    · rw [if_neg (by simp), List.length_nil]
      omega
    · rw [if_pos rfl, List.length_append]
      have := length_firstBitSem_le (dropEntrySem ![v])
      have := length_dropEntrySem_le v
      have hfb : (firstBitSem ![dropEntrySem ![v]]).length ≤ 1 := by
        rw [firstBitSem_eq]
        match dropEntrySem ![v] with
        | [] => exact Nat.zero_le 1
        | _ :: _ => exact Nat.le_refl 1
      omega

/-- The payload and the remainder together fit inside the word, the payload
counted twice: a `true` lengthens the payload by at most one bit while the
remainder loses one, so the weighted total does not grow. This is what bounds
a general paramorphism step's contribution. -/
theorem two_mul_length_takeEntrySem_add_length_dropEntrySem_le :
    ∀ w : List Bool,
      2 * (takeEntrySem ![w]).length + (dropEntrySem ![w]).length ≤ w.length :=
  List.rec (Nat.le_refl 0) fun b v ih ↦ by
    rw [takeEntrySem_cons, dropEntrySem_cons, List.length_cons]
    cases b
    · rw [if_neg (by simp), if_neg (by simp), List.length_nil]
      omega
    · rw [if_pos rfl, if_pos rfl, List.length_append, List.length_tail,
        firstBitSem_eq]
      match hd : dropEntrySem ![v] with
      | [] =>
        rw [hd] at ih
        simp only [List.length_nil]
        omega
      | c :: t =>
        rw [hd, List.length_cons] at ih
        simp only [List.length_cons, List.length_nil]
        omega

/-- The payload of a self-delimiting entry, as an expression of arity one. -/
def takeEntryOf : COf 1 :=
  scan2Of (zeroAtOf 0) (zeroAtOf 2)
    (concatCompOf 2 (comp1Of firstBitOf (comp1Of dropEntryOf (projOf 2 0)))
      (projOf 2 1)) length_takeEntrySem_le

/-- The payload expression's value at a step. -/
@[simp] theorem stepWord_takeEntryOf (w : List Bool) :
    stepWord takeEntryOf w = takeEntrySem ![w] := rfl

/-- A composition's value at an arity-one step. -/
theorem stepWord_compOf {m : ℕ} (head : COf m) (args : Fin m → COf 1)
    (u : List Bool) :
    stepWord (compOf head args) u =
      semAt m head.val.val head.property fun i ↦ stepWord (args i) u :=
  semAt_compOf head args ![u]

/-- An arity-one composition's value at an arity-one step. -/
theorem stepWord_comp1Of (e a : COf 1) (u : List Bool) :
    stepWord (comp1Of e a) u = stepWord e (stepWord a u) :=
  semAt_comp1Of e a ![u]

/-- A concatenation's value at an arity-one step. -/
theorem stepWord_concatCompOf (a b : COf 1) (u : List Bool) :
    stepWord (concatCompOf 1 a b) u = stepWord b u ++ stepWord a u :=
  semAt_concatCompOf 1 a b ![u]

/-- The identity, as an expression of arity one: the sole projection at that
arity, named for the use it is put to. -/
def idOf : COf 1 := projOf 1 0

/-- The identity's value at a step. -/
@[simp] theorem stepWord_idOf (u : List Bool) : stepWord idOf u = u :=
  semAt_projOf 1 0 ![u]

/-- The leading run of `true` of a word. -/
def takeUnarySem : Sem 1 :=
  scan2Sem (zeroAtOf 0) (zeroAtOf 2) (prependOf [true] (projOf 2 1))

/-- The run primitive on the empty word. -/
theorem takeUnarySem_nil : takeUnarySem ![[]] = [] := rfl

/-- What the run primitive computes: a `true` extends the run, a `false` ends
it. -/
theorem takeUnarySem_cons (b : Bool) (v : List Bool) :
    takeUnarySem ![b :: v] = if b then true :: takeUnarySem ![v] else [] := by
  change scan2Sem _ _ _ ![b :: v] = _
  rw [scan2Sem_cons]
  cases b
  · exact step2Word_constAtOf [] v _
  · exact (step2Word_prependOf (projOf 2 1) v _ [true]).trans
      (congrArg (fun t ↦ true :: t) (step2Word_projOf 1 v _))

/-- The run primitive never lengthens its argument. -/
theorem length_takeUnarySem_le : ∀ w : List Bool,
    (takeUnarySem ![w]).length ≤ w.length :=
  List.rec (Nat.le_refl 0) fun b v ih ↦ by
    rw [takeUnarySem_cons, List.length_cons]
    cases b
    · rw [if_neg (by simp), List.length_nil]
      omega
    · rw [if_pos rfl, List.length_cons]
      omega

/-- The leading run of `true`, as an expression of arity one. -/
def takeUnaryOf : COf 1 :=
  scan2Of (zeroAtOf 0) (zeroAtOf 2) (prependOf [true] (projOf 2 1))
    length_takeUnarySem_le

/-- The run expression's value at a step. -/
@[simp] theorem stepWord_takeUnaryOf (w : List Bool) :
    stepWord takeUnaryOf w = takeUnarySem ![w] := rfl

/-- The run primitive returns the unary prefix a word carries. -/
theorem takeUnarySem_replicate (X : List Bool) : ∀ k : ℕ,
    takeUnarySem ![List.replicate k true ++ false :: X] = List.replicate k true :=
  Nat.rec (by rw [List.replicate_zero, List.nil_append, takeUnarySem_cons,
      if_neg (by simp)])
    fun k ih ↦ by
      rw [List.replicate_succ, List.cons_append, takeUnarySem_cons, if_pos rfl,
        ih]

/-- Dropping a fixed number of whole self-delimiting entries. -/
def dropEntriesOf : ℕ → COf 1 :=
  Nat.rec idOf fun _ ih ↦ comp1Of ih dropEntryOf

/-- Dropping no entries is the identity. -/
@[simp] theorem dropEntriesOf_zero : dropEntriesOf 0 = idOf := rfl

/-- Dropping one more entry drops one first. -/
theorem stepWord_dropEntriesOf_succ (k : ℕ) (u : List Bool) :
    stepWord (dropEntriesOf (k + 1)) u =
      stepWord (dropEntriesOf k) (dropEntrySem ![u]) :=
  stepWord_comp1Of _ _ u

/-- The payload of the `j`-th self-delimiting entry. -/
def entryOf (j : ℕ) : COf 1 := comp1Of takeEntryOf (dropEntriesOf j)

/-- The `j`-th entry is the payload past `j` dropped entries. -/
theorem stepWord_entryOf (j : ℕ) (u : List Bool) :
    stepWord (entryOf j) u = takeEntrySem ![stepWord (dropEntriesOf j) u] :=
  stepWord_comp1Of _ _ u

/-- The self-delimiting spelling of a payload: its length in unary, a `false`
sentinel, then the payload. -/
def entryWord (u : List Bool) : List Bool :=
  List.replicate u.length true ++ false :: u

/-- An entry's length: twice the payload's, plus the sentinel. -/
@[simp] theorem length_entryWord (u : List Bool) :
    (entryWord u).length = 2 * u.length + 1 := by
  rw [entryWord, List.length_append, List.length_replicate, List.length_cons]
  omega

/-- The first-bit primitive is the one-bit truncation. -/
theorem firstBitSem_eq_take_one : ∀ z : List Bool, firstBitSem ![z] = z.take 1
  | [] => rfl
  | b :: t => by
    rw [firstBitSem_eq (b :: t)]
    rfl

/-- The prefix-dropping primitive reads a unary prefix off and returns what
follows the sentinel. -/
theorem dropUnarySem_replicate (X : List Bool) : ∀ k : ℕ,
    dropUnarySem ![List.replicate k true ++ false :: X] = X :=
  Nat.rec rfl fun k ih ↦ by
    rw [List.replicate_succ, List.cons_append, dropUnarySem_cons, if_pos rfl, ih]

/-- The entry-dropping primitive drops as many payload bits as the unary prefix
counts. -/
theorem dropEntrySem_replicate (X : List Bool) : ∀ k : ℕ,
    dropEntrySem ![List.replicate k true ++ false :: X] = X.drop k :=
  Nat.rec (by rw [List.replicate_zero, List.nil_append, dropEntrySem_cons,
      if_neg (by simp), List.drop_zero])
    fun k ih ↦ by
      rw [List.replicate_succ, List.cons_append, dropEntrySem_cons, if_pos rfl,
        ih, List.tail_drop]

/-- Splitting a truncation at its last bit. Proved here rather than by
`List.take_add`, which was measured to depend on `Classical.choice`. -/
theorem take_succ_append_take_one : ∀ (k : ℕ) (X : List Bool),
    X.take (k + 1) = X.take k ++ (X.drop k).take 1 :=
  Nat.rec (fun X ↦ by rw [List.take_zero, List.nil_append, List.drop_zero])
    fun k ih X ↦ match X with
      | [] => rfl
      | b :: t => by
        rw [List.take_succ_cons, List.take_succ_cons, List.drop_succ_cons,
          List.cons_append, ih t]

/-- The payload primitive reads exactly as many bits as the unary prefix
counts. -/
theorem takeEntrySem_replicate (X : List Bool) : ∀ k : ℕ,
    takeEntrySem ![List.replicate k true ++ false :: X] = X.take k :=
  Nat.rec (by rw [List.replicate_zero, List.nil_append, takeEntrySem_cons,
      if_neg (by simp), List.take_zero])
    fun k ih ↦ by
      rw [List.replicate_succ, List.cons_append, takeEntrySem_cons, if_pos rfl,
        ih, dropEntrySem_replicate, firstBitSem_eq_take_one,
        ← take_succ_append_take_one]

/-- The payload primitive returns an entry's payload, whatever follows it. -/
theorem takeEntrySem_entryWord (u rest : List Bool) :
    takeEntrySem ![entryWord u ++ rest] = u := by
  rw [entryWord, List.append_assoc, List.cons_append, takeEntrySem_replicate,
    List.take_left]

/-- The entry-dropping primitive returns whatever follows an entry. -/
theorem dropEntrySem_entryWord (u rest : List Bool) :
    dropEntrySem ![entryWord u ++ rest] = rest := by
  rw [entryWord, List.append_assoc, List.cons_append, dropEntrySem_replicate,
    List.drop_left]

end Geb.CobhamFold

end
