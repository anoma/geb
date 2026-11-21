/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Prototypes.Computability.CobhamFoldProto.Bound
public import Geb.Prototypes.Computability.CobhamFoldProto.Fold
public import Geb.Prototypes.Computability.CobhamFoldProto.SelfDelim
public import Geb.Mathlib.Computability.Cobham.RankedTree

/-!
# The fold at a bitstring carrier

`Geb/Prototypes/Computability/CobhamFoldProto/Expr.lean` folds at a carrier with a
fixed-width bit encoding, dispatching each step on a constant window that holds
the whole stack the step reads. This module folds at the carrier `List Bool`
with the algebra's operations supplied as expressions of Cobham's class, so the
carrier is unrestricted and the algebra is whatever the class can define.

## Main definitions

* `Geb.CobhamFold.stackWordV`, `Geb.CobhamFold.stateWordV` — the stack and the
  state as bitstrings.
* `Geb.CobhamFold.stackSize` — the total length of the pending values.
* `Geb.CobhamFold.entryWordOf`, `Geb.CobhamFold.applyAlgOf`,
  `Geb.CobhamFold.newStackOf`, `Geb.CobhamFold.rebuildOf` — the step's stack
  rewrite, as expressions.
* `Geb.CobhamFold.branchV`, `Geb.CobhamFold.foldStepV` — one step of the fold.
* `Geb.CobhamFold.decodeVAt` — the inverse of the layout at a window.
* `Geb.CobhamFold.foldGrowthV` — the growth the state layout's fixed part
  contributes.
* `Geb.CobhamFold.foldSemV`, `Geb.CobhamFold.foldExprV`,
  `Geb.CobhamFold.foldExprOfV` — the scan, and the scan as a member of
  `Cobham.C`.
* `Geb.CobhamFold.readoutWidthV`, `Geb.CobhamFold.outWordV`,
  `Geb.CobhamFold.readOfV` — the readout's window, its output word, and the
  readout as an expression.
* `Geb.CobhamFold.foldOutOfV`, `Geb.CobhamFold.foldOutExprV`,
  `Geb.CobhamFold.foldOutSemV` — the readout composed onto the scan by
  `Geb.CobhamFold.comp1Of`.
* `Geb.CobhamFold.algOfFixed` — a fixed-width carrier's algebra transported
  here.

## Main statements

* `Geb.CobhamFold.stackWordV_cons`, `Geb.CobhamFold.length_stackWordV` — the
  stack's layout and its length.
* `Geb.CobhamFold.stepWord_dropEntriesOf_stackWordV`,
  `Geb.CobhamFold.stepWord_entryOf_stackWordV` — the primitives read the stack.
* `Geb.CobhamFold.stepWord_dropEntriesOf_stackWordV_append`,
  `Geb.CobhamFold.stepWord_entryOf_stackWordV_append` — the same two reads at
  a stack layout followed by an arbitrary remainder, which each need the
  count to be within the stack.
* `Geb.CobhamFold.decodeState_stateWordV` — the dispatch window decodes the
  flag, the block and the count capped at the window.
* `Geb.CobhamFold.stepWord_foldStepV` — a step of the expression computes a step
  of the fold scan.
* `Geb.CobhamFold.foldSemV_eq`, `Geb.CobhamFold.length_foldSemV_le` — the
  expression computes the fold scan's state word, and the recursion bound it
  satisfies under the linear-growth hypothesis.
* `Geb.CobhamFold.stepWord_readOfV` — the readout's value at a state word.
* `Geb.CobhamFold.length_fold_le_of_growth` — an algebra lengthening by at most
  a constant per symbol folds a term to a value linear in its node count.
* `Geb.CobhamFold.potential_foldScanStep_le`,
  `Geb.CobhamFold.potential_foldScanFinal_le`,
  `Geb.CobhamFold.stackSize_le_of_growth` — the same condition bounds the scan's
  potential `R.width * stackSize + c * |buf|`, and so discharges the
  linear-growth hypothesis `length_foldSemV_le` takes.
* `Geb.CobhamFold.potential_foldScanStep_le_of_invariant`,
  `Geb.CobhamFold.potential_foldScanFinal_le_of_invariant`,
  `Geb.CobhamFold.stackSize_le_of_growth_of_invariant` — the same three with
  the growth condition assumed only of values satisfying a predicate the
  scan's stack carries, which an algebra duplicating its children's payloads
  needs; the unrestricted forms are these at the trivial predicate.
* `Geb.CobhamFold.foldOutSemV_eq` — the expression computes
  `Geb.CobhamFold.foldOut`, spelled by `outWordV`; with `foldOut_eq` this is
  `RankedAlphabet.parse` followed by the algebra morphism.
* `Geb.CobhamFold.foldOut_algOfFixed` — at an algebra whose carrier stays within
  a fixed width, the fold this construction computes and the one the fixed-width
  construction computes agree, up to the encoding. It is a statement about the
  two algebras at the shared semantic layer, which each construction is
  separately proved to compute (`foldOutSemV_eq` here, `foldOutSem_eq` there).

* `Geb.CobhamFold.foldSemV_eq_eval`, `Geb.CobhamFold.foldOutSemV_eq_eval` — the
  meanings read at the raw trees are the meanings the expressions carry.

## Implementation notes

Names here carry a `V` suffix where their fixed-width counterparts in
`Geb/Prototypes/Computability/CobhamFoldProto/Layout.lean` and
`Geb/Prototypes/Computability/CobhamFoldProto/Expr.lean` carry an `F` or, where
the fixed-width name came first, no suffix at all: the two constructions define
the same notions at a variable-width and at a fixed-width carrier, and the
suffix is what keeps them apart in one namespace.

### The state layout

```text
stateWordV R s = stateWord R (toScan s) ++ false :: stackWordV s.stack
```

The state word is the recognizer's — the liveness flag, the block slot, and the
pending count in unary — followed by a `false` sentinel and the stack, whose
entries are `Geb.CobhamFold.entryWord`'s self-delimiting spellings.

Two consequences. The pending count stays inside a constant dispatch window, so
the test `R.arity i ≤ depth` is still a bounded one and the branch family is
`Cobham.dispatchWidth R` wide — the recognizer's own width, independent of the
carrier. And the sentinel is required: an entry begins with its length in
unary, so without a `false` between the count and the stack the decoder's
`takeWhile` would run out of the count and into the first entry's prefix.

### Cost

Each primitive the step reads the stack with is itself a recursion whose step is
not constant. `Geb.CobhamFold.dropEntryOf`'s step applies `Cobham.pred`, itself
a `boundedRec`; `Geb.CobhamFold.takeEntryOf`'s step runs a fresh `dropEntryOf`
over the remaining word. Counting a `boundedRec`'s cost as the sum over its
levels of its step's cost, `dropEntryOf` is quadratic in its argument and
`takeEntryOf` cubic, so a fold's state-reading here is polynomial of a degree above
two rather than quadratic.

Nothing here measures a number of reduction steps, as
`Geb/Mathlib/Computability/Cobham/Tree.lean` records of its own subject; the
paragraph above is an analysis of the expression under one cost model, and a
machine evaluating it is not obliged to follow that model.

The accompanying lower bound rests only on the class's shape rather than on a
cost model: reading an unbounded field of the state requires a recursion over
the state, `boundedRec` being the class's only recursion, so no step reading
such a field is constant. It bears on this layout, whose steps do read one; it
does not exclude some other expression computing the same fold without reading
an unbounded field. It is an argument about the expression, not a theorem stated
here.

The algebra is an arbitrary member of the class and so carries whatever cost the
class admits, putting a fold above its algebra by whatever the state-reading costs.
The state-reading is therefore not what limits a fold: any cost the class admits at
all is reached by spending it inside the algebra. How far that goes is a
question about the class, not about this construction, and it is not settled
here — only the left-to-right inclusion of [Strahm2003] Theorem 1(2) is relied
on anywhere in this repository, and `docs/references.bib` records that the
equality fails read literally.

Space is what binds. The state holds every pending value, so a linear-space
reading forces a constant `c` bounding the pending values' total length by
`c * n`, which is the hypothesis `Geb.CobhamFold.length_foldSemV_le` takes.
That hypothesis is not an artifact of this construction: [Clote1999]'s
arithmetic analogue reads its class as one of functions of linear growth.

The dispatch is no wider here than at a fixed-width carrier, and narrower at
every positive carrier width; at `p = 0` the two coincide, which
`Geb.CobhamFold.dispatchWidthF_zero` states. The fixed-width dispatch reads the
stack, so its branch family is
`2 ^ (1 + R.width + (p + 1) * (R.maxArity + 1))`; here it reads only the flag,
the slot and the count, so the family is `2 ^ Cobham.dispatchWidth R` whatever
the carrier. This is a statement about the branch family alone: the completing
branch here carries a `rebuildOf` subtree no fixed-width branch does, and the
two expressions' sizes are not compared.

## References

* [Clote1999]
* [Cobham1965]
* [Strahm2003]

## Tags

Cobham, bounded recursion on notation, fold, self-delimiting, bitstring carrier
-/

@[expose] public section

namespace Geb.CobhamFold

open Cobham RankedAlphabet

universe u

/-- The stack as a bitstring: the self-delimiting spelling of each entry, the
top entry first. -/
def stackWordV (st : List (List Bool)) : List Bool := st.flatMap entryWord

/-- The empty stack's layout. -/
@[simp] theorem stackWordV_nil : stackWordV [] = [] := rfl

/-- The stack's layout, one entry at a time. -/
@[simp] theorem stackWordV_cons (a : List Bool) (st : List (List Bool)) :
    stackWordV (a :: st) = entryWord a ++ stackWordV st := rfl

/-- The total length of the pending values. -/
def stackSize (st : List (List Bool)) : ℕ := st.flatten.length

/-- The empty stack's values are empty. -/
@[simp] theorem stackSize_nil : stackSize [] = 0 := rfl

/-- The pending values' total length, one entry at a time. -/
@[simp] theorem stackSize_cons (a : List Bool) (st : List (List Bool)) :
    stackSize (a :: st) = a.length + stackSize st := by
  rw [stackSize, List.flatten_cons, List.length_append, stackSize]

/-- The stack's layout is twice the pending values' total length plus one bit
per entry. -/
theorem length_stackWordV : ∀ st : List (List Bool),
    (stackWordV st).length = 2 * stackSize st + st.length :=
  List.rec rfl fun a t ih ↦ by
    rw [stackWordV_cons, List.length_append, length_entryWord, ih, stackSize_cons,
      List.length_cons]
    omega

/-- The state as a bitstring: the recognizer's state word, a `false` sentinel,
then the stack. -/
def stateWordV (R : RankedAlphabet) (s : FoldScan (List Bool)) : List Bool :=
  stateWord R (toScan s) ++ false :: stackWordV s.stack

/-- The state word's length. -/
theorem length_stateWordV_of_lt (R : RankedAlphabet) (s : FoldScan (List Bool))
    (h : s.buf.length < R.width) :
    (stateWordV R s).length =
      1 + R.width + s.stack.length + 1 + (2 * stackSize s.stack + s.stack.length) := by
  have hd : (toScan s).depth = s.stack.length := rfl
  rw [stateWordV, List.length_append, length_stateWord_of_lt R (toScan s) h,
    List.length_cons, length_stackWordV, hd]
  omega

/-- Dropping whole entries from the stack's layout drops whole entries from the
stack. -/
theorem stepWord_dropEntriesOf_stackWordV : ∀ (k : ℕ) (st : List (List Bool)),
    stepWord (dropEntriesOf k) (stackWordV st) = stackWordV (st.drop k) :=
  Nat.rec (fun st ↦ by rw [dropEntriesOf_zero, stepWord_idOf, List.drop_zero])
    fun k ih st ↦ by
      rw [stepWord_dropEntriesOf_succ]
      match st with
      | [] =>
        rw [List.drop_nil]
        exact (ih []).trans (congrArg stackWordV List.drop_nil)
      | a :: t =>
        rw [stackWordV_cons, dropEntrySem_entryWord, ih t, List.drop_succ_cons]

/-- The `j`-th entry primitive reads the `j`-th pending value. -/
theorem stepWord_entryOf_stackWordV (j : ℕ) (st : List (List Bool)) :
    stepWord (entryOf j) (stackWordV st) = (st.drop j).headD [] := by
  rw [stepWord_entryOf, stepWord_dropEntriesOf_stackWordV]
  match hd : st.drop j with
  | [] => rw [stackWordV_nil]; rfl
  | a :: t => rw [stackWordV_cons, takeEntrySem_entryWord]; rfl

/-- Dropping as many entries as a stack layout holds leaves what follows
it. `Geb.CobhamFold.stepWord_dropEntriesOf_stackWordV` is this at the empty
remainder, where the hypothesis is unnecessary. -/
theorem stepWord_dropEntriesOf_stackWordV_append :
    ∀ (k : ℕ) (st : List (List Bool)) (rest : List Bool), k ≤ st.length →
      stepWord (dropEntriesOf k) (stackWordV st ++ rest) =
        stackWordV (st.drop k) ++ rest :=
  Nat.rec (fun st rest _ ↦ by rw [dropEntriesOf_zero, stepWord_idOf,
      List.drop_zero])
    fun k ih st rest h ↦ match st with
      | [] => absurd h (Nat.not_succ_le_zero k)
      | a :: t => by
        rw [stackWordV_cons, List.append_assoc, stepWord_dropEntriesOf_succ,
          dropEntrySem_entryWord, ih t rest (Nat.le_of_succ_le_succ h),
          List.drop_succ_cons]

/-- The `j`-th entry of a stack layout is its `j`-th value, whatever follows
the layout. `Geb.CobhamFold.stepWord_entryOf_stackWordV` agrees with it where
`j < st.length`; neither is an instance of the other, that one being
unconditional in `j` and read through `List.headD`. -/
theorem stepWord_entryOf_stackWordV_append (j : ℕ) (st : List (List Bool))
    (rest : List Bool) (h : j < st.length) :
    stepWord (entryOf j) (stackWordV st ++ rest) = st[j] := by
  rw [stepWord_entryOf,
    stepWord_dropEntriesOf_stackWordV_append j st rest (Nat.le_of_lt h),
    List.drop_eq_getElem_cons h, stackWordV_cons, List.append_assoc,
    takeEntrySem_entryWord]

/-- The run of `true` a window over a unary count reads, when the count is
followed by a `false` sentinel and the window may overrun the word. Whether the
window ends inside the count or past the sentinel, the run is the count capped
at the window. -/
private theorem takeWhile_id_take_replicate (Z : List Bool) :
    ∀ (m k p : ℕ),
      (((List.replicate k true ++ false :: Z).take m) ++
        List.replicate p false).takeWhile id = List.replicate (min m k) true :=
  Nat.rec
    (fun k p ↦ by
      rw [List.take_zero, List.nil_append, Nat.zero_min, List.replicate_zero]
      match p with
      | 0 => rfl
      | _ + 1 => rfl)
    fun m ih k p ↦ match k with
      | 0 => by
        rw [List.replicate_zero, List.nil_append, List.take_succ_cons,
          List.cons_append, Nat.min_zero, List.replicate_zero]
        rfl
      | k + 1 => by
        rw [List.replicate_succ, List.cons_append, List.take_succ_cons,
          List.cons_append, Nat.succ_min_succ, List.replicate_succ]
        exact congrArg (fun t ↦ true :: t) (ih k p)

/-- The state word truncated to a window and zero-padded: the flag, the slot,
then the count and whatever of the stack the window reaches. -/
theorem ofFn_bits_stateWordV (R : RankedAlphabet) (s : FoldScan (List Bool))
    (n m : ℕ) (hn : n = 1 + R.width + m) (h : s.buf.length < R.width) :
    List.ofFn (bits n (stateWordV R s)) =
      s.live :: (bufBits R s.buf ++
        (((List.replicate s.stack.length true ++ false :: stackWordV s.stack).take m) ++
          List.replicate (n - (stateWordV R s).length) false)) := by
  have hbuf : (bufBits R s.buf).length = R.width := length_bufBits_of_lt R s.buf h
  have hdw : n = (bufBits R s.buf).length + m + 1 := by
    rw [hbuf, hn]
    omega
  have hcons : stateWordV R s =
      s.live :: (bufBits R s.buf ++
        (List.replicate s.stack.length true ++ false :: stackWordV s.stack)) := by
    rw [stateWordV, stateWord, toScan]
    dsimp only
    simp only [List.cons_append, List.append_assoc]
  rw [ofFn_bits, hcons, hdw, List.take_succ_cons, List.take_length_add_append,
    List.cons_append, List.append_assoc, ← hcons]

/-- The inverse of the layout at a window of `n` bits: the flag, the block past
the slot's padding, and the run of the pending count. `Cobham.decodeState` is
this at the dispatch window. -/
def decodeVAt (R : RankedAlphabet) (n : ℕ) (v : Fin n → Bool) : Scan :=
  ⟨(((List.ofFn v).tail.take R.width).dropWhile (fun b ↦ !b)).tail,
    (((List.ofFn v).tail.drop R.width).takeWhile id).length,
    (List.ofFn v).headD false⟩

/-- A window decodes the flag, the incomplete block, and the pending count
capped at the window. The `false` sentinel is what stops the count's run from
continuing into the first entry's own unary prefix. -/
theorem decodeVAt_stateWordV (R : RankedAlphabet) (s : FoldScan (List Bool))
    (n m : ℕ) (hn : n = 1 + R.width + m) (h : s.buf.length < R.width) :
    decodeVAt R n (bits n (stateWordV R s)) =
      ⟨s.buf, min s.stack.length m, s.live⟩ := by
  have hbuf : (bufBits R s.buf).length = R.width := length_bufBits_of_lt R s.buf h
  have hword := ofFn_bits_stateWordV R s n m hn h
  refine Scan.ext ?_ ?_ ?_
  · rw [decodeVAt, hword, List.tail_cons, List.take_left' hbuf, dropWhile_bufBits]
    rfl
  · rw [decodeVAt, hword, List.tail_cons, List.drop_left' hbuf,
      takeWhile_id_take_replicate, List.length_replicate]
    exact Nat.min_comm _ _
  · rw [decodeVAt, hword, List.headD_cons]

/-- The dispatch window's decode, which is `Cobham.decodeState`. -/
theorem decodeState_stateWordV (R : RankedAlphabet) (s : FoldScan (List Bool))
    (h : s.buf.length < R.width) :
    decodeState R (bits (dispatchWidth R) (stateWordV R s)) =
      ⟨s.buf, min s.stack.length (R.maxArity + 1), s.live⟩ :=
  decodeVAt_stateWordV R s (dispatchWidth R) (R.maxArity + 1)
    (by rw [dispatchWidth]; omega) h

/-- The self-delimiting spelling, as an expression of arity one. -/
def entryWordOf : COf 1 := concatCompOf 1 (prependOf [false] idOf) unaryOf

/-- The spelling expression's value at a step. -/
theorem stepWord_entryWordOf (u : List Bool) :
    stepWord entryWordOf u = entryWord u := by
  rw [entryWordOf, stepWord_concatCompOf, stepWord_unaryOf, unarySem_eq,
    stepWord_prependOf, stepWord_idOf, entryWord]
  rfl

/-- The algebra's operation applied to the entries the stack holds. -/
def applyAlgOf {r : ℕ} (algI : COf r) : COf 1 :=
  compOf algI fun j ↦ entryOf j.val

/-- The algebra application's value at a step. -/
theorem stepWord_applyAlgOf {r : ℕ} (algI : COf r) (u : List Bool) :
    stepWord (applyAlgOf algI) u =
      semAt r algI.val.val algI.property fun j ↦ stepWord (entryOf j.val) u :=
  stepWord_compOf algI _ u

/-- The stack after the pop: the algebra's value spelled as an entry, then the
stack past the entries it consumed. -/
def newStackOf {r : ℕ} (algI : COf r) : COf 1 :=
  concatCompOf 1 (dropEntriesOf r) (comp1Of entryWordOf (applyAlgOf algI))

/-- The new stack's value at a step. -/
theorem stepWord_newStackOf {r : ℕ} (algI : COf r) (u : List Bool) :
    stepWord (newStackOf algI) u =
      entryWord (stepWord (applyAlgOf algI) u) ++ stepWord (dropEntriesOf r) u := by
  rw [newStackOf, stepWord_concatCompOf, stepWord_comp1Of, stepWord_entryWordOf]

/-- The state past the flag and the slot, rebuilt: the pending count is kept and
the stack is rewritten. -/
def rebuildOf {r : ℕ} (algI : COf r) : COf 1 :=
  concatCompOf 1 (prependOf [false] (comp1Of (newStackOf algI) dropUnaryOf))
    takeUnaryOf

/-- The rebuild's value at a step. -/
theorem stepWord_rebuildOf {r : ℕ} (algI : COf r) (z : List Bool) :
    stepWord (rebuildOf algI) z =
      takeUnarySem ![z] ++ false :: stepWord (newStackOf algI) (dropUnarySem ![z]) := by
  rw [rebuildOf, stepWord_concatCompOf, stepWord_takeUnaryOf, stepWord_prependOf,
    stepWord_comp1Of, stepWord_dropUnaryOf]
  rfl

/-- The state word past the flag, the slot and `k` of the pending count: the
count short by `k`, then the sentinel and the stack. -/
theorem drop_stateWordV (R : RankedAlphabet) (s : FoldScan (List Bool))
    (h : s.buf.length < R.width) (k : ℕ) (hk : k ≤ s.stack.length) :
    (stateWordV R s).drop (1 + R.width + k) =
      List.replicate (s.stack.length - k) true ++ false :: stackWordV s.stack := by
  have hpre : (s.live :: bufBits R s.buf).length = 1 + R.width := by
    rw [List.length_cons, length_bufBits_of_lt R s.buf h]
    omega
  have hsplit : List.replicate s.stack.length true =
      List.replicate k true ++ List.replicate (s.stack.length - k) true := by
    rw [← List.replicate_add]
    exact congrArg (fun j ↦ List.replicate j true) (by omega)
  have hcons : stateWordV R s =
      (s.live :: bufBits R s.buf) ++
        (List.replicate s.stack.length true ++ false :: stackWordV s.stack) := by
    rw [stateWordV, stateWord, toScan]
    dsimp only
    simp only [List.append_assoc]
  rw [← List.drop_drop, hcons, List.drop_left' hpre, hsplit, List.append_assoc,
    List.drop_left' (List.length_replicate (n := k) (a := true))]

/-- One step of the fold at a bitstring carrier, as a function of the state the
dispatch window decodes. A failed state absorbs; an incomplete block takes the
bit; a completed block's symbol pops its arity from the count and rewrites the
stack. -/
def branchV (R : RankedAlphabet) (algOf : (i : Fin R.card) → COf (R.arity i))
    (b : Bool) (t : Scan) : COf 1 :=
  match t.live with
  | false => idOf
  | true =>
    if (b :: t.buf).length = R.width then
      match symOf R (decodeBits (b :: t.buf)) with
      | none => prependOf (false :: bufBits R []) (predIterOf (1 + R.width))
      | some i =>
        if R.arity i ≤ t.depth then
          prependOf (true :: bufBits R [] ++ [true])
            (comp1Of (rebuildOf (algOf i)) (predIterOf (1 + R.width + R.arity i)))
        else prependOf (false :: bufBits R []) (predIterOf (1 + R.width))
    else prependOf (true :: bufBits R (b :: t.buf)) (predIterOf (1 + R.width))

/-- One step of the fold expression: dispatch on the flag, the slot and the
pending count, and rewrite. -/
def foldStepV (R : RankedAlphabet) (algOf : (i : Fin R.card) → COf (R.arity i))
    (b : Bool) : COf 1 :=
  diagOf (casesOf (dispatchWidth R) fun v ↦ branchV R algOf b (decodeState R v))

/-- The step's value at a state word, before the branch is resolved. -/
theorem stepWord_foldStepV_apply (R : RankedAlphabet)
    (algOf : (i : Fin R.card) → COf (R.arity i)) (b : Bool)
    (s : FoldScan (List Bool)) (h : s.buf.length < R.width) :
    stepWord (foldStepV R algOf b) (stateWordV R s) =
      stepWord (branchV R algOf b ⟨s.buf, min s.stack.length (R.maxArity + 1), s.live⟩)
        (stateWordV R s) := by
  rw [foldStepV, stepWord_diagOf]
  change casesSem (dispatchWidth R) _ ![stateWordV R s, stateWordV R s] = _
  rw [casesSem_eq, decodeState_stateWordV R s h]

/-- Capping the pending count at the dispatch window leaves the branch
unchanged: the only test reading the count compares it with an arity, which
`RankedAlphabet.arity_le_maxArity` bounds by `R.maxArity`. -/
theorem branchV_min (R : RankedAlphabet)
    (algOf : (i : Fin R.card) → COf (R.arity i)) (b : Bool)
    (t : Scan) :
    branchV R algOf b { t with depth := min t.depth (R.maxArity + 1) } =
      branchV R algOf b t := by
  obtain ⟨buf, depth, live⟩ := t
  rw [branchV, branchV]
  dsimp only
  cases live
  · rfl
  · dsimp only
    by_cases hlen : (b :: buf).length = R.width
    · rw [if_pos hlen, if_pos hlen]
      match hsym : symOf R (decodeBits (b :: buf)) with
      | none => rfl
      | some i =>
        dsimp only
        have hle : R.arity i ≤ R.maxArity := arity_le_maxArity R i
        by_cases hst : R.arity i ≤ depth
        · rw [if_pos hst, if_pos (by omega)]
        · rw [if_neg hst, if_neg (by omega)]
    · rw [if_neg hlen, if_neg hlen]

/-- The state layout at an explicit state. -/
theorem stateWordV_mk (R : RankedAlphabet) (buf : List Bool)
    (st : List (List Bool)) (live : Bool) :
    stateWordV R ⟨buf, st, live⟩ =
      (live :: bufBits R buf ++ List.replicate st.length true) ++
        false :: stackWordV st := rfl

/-- The head of a suffix is the element it starts at. -/
private theorem headD_drop (j : ℕ) (st : List (List Bool)) (hj : j < st.length) :
    (st.drop j).headD [] = st[j] := by
  rw [List.drop_eq_getElem_cons hj]
  rfl

/-- A step of the expression computes a step of the fold scan. The algebra's
operations enter only through `halg`, which reads each expression's meaning as
the corresponding carrier-level operation. -/
theorem stepWord_foldStepV (R : RankedAlphabet)
    (algOf : (i : Fin R.card) → COf (R.arity i))
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool)
    (halg : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      semAt (R.arity i) (algOf i).val.val (algOf i).property f = alg i f)
    (b : Bool) (s : FoldScan (List Bool)) (h : s.buf.length < R.width) :
    stepWord (foldStepV R algOf b) (stateWordV R s) =
      stateWordV R (foldScanStep R alg b s) := by
  rw [stepWord_foldStepV_apply R algOf b s h]
  have hcap : branchV R algOf b ⟨s.buf, min s.stack.length (R.maxArity + 1), s.live⟩ =
      branchV R algOf b ⟨s.buf, s.stack.length, s.live⟩ :=
    branchV_min R algOf b ⟨s.buf, s.stack.length, s.live⟩
  rw [hcap]
  have hdrop0 : (stateWordV R s).drop (1 + R.width) =
      List.replicate s.stack.length true ++ false :: stackWordV s.stack := by
    have := drop_stateWordV R s h 0 (Nat.zero_le _)
    rwa [Nat.add_zero, Nat.sub_zero] at this
  obtain ⟨buf, stack, live⟩ := s
  dsimp only at h hdrop0 ⊢
  rw [branchV, foldScanStep]
  dsimp only
  cases live
  · rw [stepWord_idOf]
  · dsimp only
    by_cases hlen : (b :: buf).length = R.width
    · rw [if_pos hlen, if_pos hlen]
      match hsym : symOf R (decodeBits (b :: buf)) with
      | none =>
        rw [stepWord_prependOf, stepWord_predIterOf, hdrop0, stateWordV_mk]
        simp only [List.cons_append, List.append_assoc]
      | some i =>
        dsimp only
        by_cases hst : R.arity i ≤ stack.length
        · rw [if_pos hst, dif_pos hst, stepWord_prependOf,
            stepWord_comp1Of, stepWord_predIterOf, drop_stateWordV R _ h _ hst,
            stepWord_rebuildOf, takeUnarySem_replicate, dropUnarySem_replicate,
            stepWord_newStackOf, stepWord_dropEntriesOf_stackWordV,
            stepWord_applyAlgOf, halg, stateWordV_mk]
          have hargs : (fun j : Fin (R.arity i) ↦
              stepWord (entryOf j.val) (stackWordV stack)) =
              fun j : Fin (R.arity i) ↦ stack[j.val]'(Nat.lt_of_lt_of_le j.isLt hst) := by
            funext j
            rw [stepWord_entryOf_stackWordV]
            exact headD_drop j.val stack (Nat.lt_of_lt_of_le j.isLt hst)
          rw [hargs, List.length_cons, List.length_drop, stackWordV_cons]
          have hrep : List.replicate (stack.length - R.arity i + 1) true =
              [true] ++ List.replicate (stack.length - R.arity i) true := by
            rw [Nat.add_comm, List.replicate_add]
            rfl
          rw [hrep]
          simp only [List.cons_append, List.append_assoc]
        · rw [if_neg hst, dif_neg hst, stepWord_prependOf,
            stepWord_predIterOf, hdrop0, stateWordV_mk]
          simp only [List.cons_append, List.append_assoc]
    · rw [if_neg hlen, if_neg hlen, stepWord_prependOf,
        stepWord_predIterOf, hdrop0, stateWordV_mk]
      simp only [List.cons_append, List.append_assoc]

/-- The growth the state layout's fixed part contributes: the flag, the slot and
the sentinel. -/
def foldGrowthV (R : RankedAlphabet) : ℕ := 2 + R.width

/-- The fold's scan at a bitstring carrier. -/
def foldSemV (R : RankedAlphabet) (algOf : (i : Fin R.card) → COf (R.arity i))
    (mult : ℕ) : Sem 1 :=
  scanBSem (constAtOf 0 (stateWordV R ⟨[], [], true⟩))
    (foldStepV R algOf false) (foldStepV R algOf true)
    (boundMulRaw mult (foldGrowthV R)) (wValid_boundMulRaw mult (foldGrowthV R))
    (wIndexRoot_boundMulRaw mult (foldGrowthV R))

/-- The expression computes the fold scan's state word on every input. -/
theorem foldSemV_eq (R : RankedAlphabet)
    (algOf : (i : Fin R.card) → COf (R.arity i))
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool)
    (halg : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      semAt (R.arity i) (algOf i).val.val (algOf i).property f = alg i f)
    (mult : ℕ) (w : List Bool) :
    foldSemV R algOf mult ![w] = stateWordV R (foldScanFinal R alg w) := by
  rw [foldSemV, scanBSem_eq]
  refine List.rec ?_ ?_ w
  · rw [List.foldr_nil, baseWord_constAtOf]
    rfl
  · intro b v ih
    rw [List.foldr_cons, ih]
    cases b
    · exact stepWord_foldStepV R algOf alg halg false _
        (length_buf_foldScanFinal_lt R alg v)
    · exact stepWord_foldStepV R algOf alg halg true _
        (length_buf_foldScanFinal_lt R alg v)

/-- The recursion bound, under the hypothesis that the pending values stay
linear in the input. That hypothesis is what linear space forces of this layout:
the state holds every pending value at once. Whether a fold whose values grow
faster is excluded from the subalgebra `Cobham.SmashFree` names outright, rather
than from this layout, is not stated here. -/
theorem length_foldSemV_le (R : RankedAlphabet)
    (algOf : (i : Fin R.card) → COf (R.arity i))
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool)
    (halg : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      semAt (R.arity i) (algOf i).val.val (algOf i).property f = alg i f)
    (mult c : ℕ)
    (hsize : ∀ w : List Bool,
      stackSize (foldScanFinal R alg w).stack ≤ c * w.length)
    (hmult : 2 * c + 2 ≤ mult) (w : List Bool) :
    (scanBSem (constAtOf 0 (stateWordV R ⟨[], [], true⟩))
      (foldStepV R algOf false) (foldStepV R algOf true)
      (boundMulRaw mult (foldGrowthV R)) (wValid_boundMulRaw mult (foldGrowthV R))
      (wIndexRoot_boundMulRaw mult (foldGrowthV R))
      ![w]).length ≤ mult * w.length + foldGrowthV R := by
  have hstate : (scanBSem (constAtOf 0 (stateWordV R ⟨[], [], true⟩))
      (foldStepV R algOf false) (foldStepV R algOf true)
      (boundMulRaw mult (foldGrowthV R)) (wValid_boundMulRaw mult (foldGrowthV R))
      (wIndexRoot_boundMulRaw mult (foldGrowthV R)) ![w]).length =
      1 + R.width + (R.scanFinal w).depth + 1 +
        (2 * stackSize (foldScanFinal R alg w).stack + (R.scanFinal w).depth) := by
    rw [← foldSemV, foldSemV_eq R algOf alg halg mult w,
      length_stateWordV_of_lt R _ (length_buf_foldScanFinal_lt R alg w),
      length_stack_foldScanFinal]
  have hd : (R.scanFinal w).depth ≤ w.length := depth_scanFinal_le_length R w
  have hs := hsize w
  have h1 : (2 * c + 2) * w.length ≤ mult * w.length :=
    Nat.mul_le_mul_right w.length hmult
  have h2 : (2 * c + 2) * w.length = 2 * (c * w.length) + 2 * w.length := by
    rw [Nat.add_mul, Nat.mul_assoc]
  rw [hstate, foldGrowthV]
  omega

/-- The scan as a member of `Cobham.C`, at its arity: the form consumers take,
`foldExprV` being its underlying expression. -/
def foldExprOfV (R : RankedAlphabet) (algOf : (i : Fin R.card) → COf (R.arity i))
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool)
    (halg : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      semAt (R.arity i) (algOf i).val.val (algOf i).property f = alg i f)
    (mult c : ℕ)
    (hsize : ∀ w : List Bool,
      stackSize (foldScanFinal R alg w).stack ≤ c * w.length)
    (hmult : 2 * c + 2 ≤ mult) : COf 1 :=
  scanMulOf (constAtOf 0 (stateWordV R ⟨[], [], true⟩))
    (foldStepV R algOf false) (foldStepV R algOf true) mult (foldGrowthV R)
    (length_foldSemV_le R algOf alg halg mult c hsize hmult)

/-- The fold at a bitstring carrier, as an expression of Cobham's class. -/
def foldExprV (R : RankedAlphabet) (algOf : (i : Fin R.card) → COf (R.arity i))
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool)
    (halg : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      semAt (R.arity i) (algOf i).val.val (algOf i).property f = alg i f)
    (mult c : ℕ)
    (hsize : ∀ w : List Bool,
      stackSize (foldScanFinal R alg w).stack ≤ c * w.length)
    (hmult : 2 * c + 2 ≤ mult) : C :=
  (foldExprOfV R algOf alg halg mult c hsize hmult).val

/-- The meaning `foldSemV` reads at the raw tree is the meaning `foldExprV`
carries. -/
theorem foldSemV_eq_eval (R : RankedAlphabet)
    (algOf : (i : Fin R.card) → COf (R.arity i))
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool)
    (halg : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      semAt (R.arity i) (algOf i).val.val (algOf i).property f = alg i f)
    (mult c : ℕ)
    (hsize : ∀ w : List Bool,
      stackSize (foldScanFinal R alg w).stack ≤ c * w.length)
    (hmult : 2 * c + 2 ≤ mult) :
    transport (foldExprOfV R algOf alg halg mult c hsize hmult).property
        (foldExprOfV R algOf alg halg mult c hsize hmult).val.eval =
      foldSemV R algOf mult := rfl

/-- A fixed-width carrier's algebra transported to the bitstring carrier: decode
each argument, apply the algebra, and spell the result. -/
def algOfFixed {α : Type u} {p : ℕ} (R : RankedAlphabet) (enc : α → Fin p → Bool)
    (dec : (Fin p → Bool) → α)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) :
    (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool :=
  fun i f ↦ List.ofFn (enc (alg i fun d ↦ dec (bits p (f d))))

/-- The two fold constructions agree on results. Called at an algebra whose
carrier does stay within a fixed width, the bitstring fold computes the encoding
of what the fixed-width fold computes, on every input — including the inputs
that spell no term, where both are absent.

This is an equality of results only, and it relates the two algebras at the
shared semantic layer rather than the two expressions directly; each expression
is tied to that layer separately, by `foldOutSemV_eq` here and by
`Geb.CobhamFold.foldOutSem_eq` for the fixed-width construction. The two differ
in cost, though not as a constant-time step against a linear-time one: under the
model of § Cost neither construction has constant-time steps, `Cobham.casesOf`
dispatching through `Cobham.cond` and `Cobham.predIterOf` iterating
`Cobham.pred`, both `boundedRec` nodes over the state. What differs is the
degree, a fixed-width step being linear in the state where `takeEntryOf` is
cubic. -/
theorem foldOut_algOfFixed {α : Type u} {p : ℕ} (R : RankedAlphabet)
    (enc : α → Fin p → Bool) (dec : (Fin p → Bool) → α)
    (hdec : ∀ a, dec (enc a) = a)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (w : List Bool) :
    foldOut R (algOfFixed R enc dec alg) w =
      (foldOut R alg w).map fun a ↦ List.ofFn (enc a) :=
  foldOut_map R alg (algOfFixed R enc dec alg) (fun a ↦ List.ofFn (enc a))
    (fun i g ↦ congrArg (fun h ↦ List.ofFn (enc (alg i h)))
      (funext fun d ↦ by rw [bits_ofFn, hdec])) w

/-- The readout's output word: a `true` marker followed by the value, and
`[false]` at no value. The marker separates the two branches, a value being
free to be empty. -/
def outWordV : Option (List Bool) → List Bool
  | none => [false]
  | some a => true :: a

/-- The number of state bits the readout dispatches on: the flag, the slot, and
`R.maxArity + 2` count bits. Any count region of two or more bits separates a
count of one from a longer one; this width is chosen to exceed the dispatch
window's, which is one bit at an alphabet whose symbols are all nullary. -/
def readoutWidthV (R : RankedAlphabet) : ℕ := 1 + R.width + (R.maxArity + 2)

/-- The readout at a bitstring carrier, dispatching on
`Geb.CobhamFold.readoutWidthV`'s window: on acceptance the sole stack entry's
payload, prefixed with a presence marker, and `[false]` otherwise. -/
def readOfV (R : RankedAlphabet) : COf 1 :=
  diagOf (casesOf (readoutWidthV R) fun v ↦
    if (decodeVAt R (readoutWidthV R) v).live &&
        (decodeVAt R (readoutWidthV R) v).buf.isEmpty &&
        (decodeVAt R (readoutWidthV R) v).depth == 1 then
      prependOf [true] (comp1Of takeEntryOf (predIterOf (R.width + 3)))
    else constAtOf 1 [false])

/-- The state word past the flag, the slot, one pending count and the
sentinel is the stack. -/
theorem drop_stateWordV_succ (R : RankedAlphabet) (s : FoldScan (List Bool))
    (h : s.buf.length < R.width) (h1 : s.stack.length = 1) :
    (stateWordV R s).drop (R.width + 3) = stackWordV s.stack := by
  have hd := drop_stateWordV R s h 1 (by omega)
  rw [h1] at hd
  have hdd : (stateWordV R s).drop (R.width + 3) =
      ((stateWordV R s).drop (1 + R.width + 1)).drop 1 := by
    rw [List.drop_drop]
    exact congrArg (fun k ↦ (stateWordV R s).drop k) (by omega)
  rw [hdd, hd]
  rfl

/-- The readout's value at a state word. -/
theorem stepWord_readOfV (R : RankedAlphabet) (s : FoldScan (List Bool))
    (h : s.buf.length < R.width) :
    stepWord (readOfV R) (stateWordV R s) =
      outWordV (if s.live && s.buf.isEmpty && s.stack.length == 1
        then s.stack.head? else none) := by
  rw [readOfV, stepWord_diagOf]
  change casesSem (readoutWidthV R) _ ![stateWordV R s, stateWordV R s] = _
  rw [casesSem_eq, decodeVAt_stateWordV R s (readoutWidthV R) (R.maxArity + 2)
    (by rw [readoutWidthV]) h]
  dsimp only
  have hmin : ∀ n : ℕ, (min n (R.maxArity + 2) == 1) = (n == 1) := by
    intro n
    by_cases hn : n = 1
    · have h2 : min n (R.maxArity + 2) = 1 := by omega
      rw [h2, hn]
    · rw [beq_eq_false_iff_ne.mpr (by omega : ¬ min n (R.maxArity + 2) = 1),
        beq_eq_false_iff_ne.mpr hn]
  rw [hmin]
  by_cases hacc : (s.live && s.buf.isEmpty && (s.stack.length == 1)) = true
  · rw [if_pos hacc, if_pos hacc, stepWord_prependOf, stepWord_comp1Of,
      stepWord_predIterOf]
    obtain ⟨_, hone⟩ := (Bool.and_eq_true _ _).mp hacc
    have h1 : s.stack.length = 1 := eq_of_beq hone
    have hsing : ∃ a, s.stack = [a] := by
      match hs2 : s.stack with
      | [] =>
        rw [hs2, List.length_nil] at h1
        exact absurd h1 Nat.zero_ne_one
      | a :: [] => exact ⟨a, rfl⟩
      | _ :: _ :: t =>
        rw [hs2, List.length_cons, List.length_cons] at h1
        exact absurd h1 (by omega)
    obtain ⟨a, ha⟩ := hsing
    rw [drop_stateWordV_succ R s h h1, stepWord_takeEntryOf, ha,
      stackWordV_cons, stackWordV_nil, takeEntrySem_entryWord]
    rfl
  · rw [if_neg hacc, if_neg hacc, stepWord_constAtOf]
    rfl

/-- The readout composed onto the scan, at its declared arity. -/
def foldOutOfV (R : RankedAlphabet) (algOf : (i : Fin R.card) → COf (R.arity i))
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool)
    (halg : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      semAt (R.arity i) (algOf i).val.val (algOf i).property f = alg i f)
    (mult c : ℕ)
    (hsize : ∀ w : List Bool,
      stackSize (foldScanFinal R alg w).stack ≤ c * w.length)
    (hmult : 2 * c + 2 ≤ mult) : COf 1 :=
  comp1Of (readOfV R) (foldExprOfV R algOf alg halg mult c hsize hmult)

/-- The fold at a bitstring carrier, as an expression of Cobham's class. -/
def foldOutExprV (R : RankedAlphabet) (algOf : (i : Fin R.card) → COf (R.arity i))
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool)
    (halg : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      semAt (R.arity i) (algOf i).val.val (algOf i).property f = alg i f)
    (mult c : ℕ)
    (hsize : ∀ w : List Bool,
      stackSize (foldScanFinal R alg w).stack ≤ c * w.length)
    (hmult : 2 * c + 2 ≤ mult) : C :=
  (foldOutOfV R algOf alg halg mult c hsize hmult).val

/-- The fold's meaning at its arity, read at the raw tree. -/
def foldOutSemV (R : RankedAlphabet) (algOf : (i : Fin R.card) → COf (R.arity i))
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool)
    (halg : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      semAt (R.arity i) (algOf i).val.val (algOf i).property f = alg i f)
    (mult c : ℕ)
    (hsize : ∀ w : List Bool,
      stackSize (foldScanFinal R alg w).stack ≤ c * w.length)
    (hmult : 2 * c + 2 ≤ mult) : Sem 1 :=
  semAt 1 (foldOutOfV R algOf alg halg mult c hsize hmult).val.val
    (foldOutOfV R algOf alg halg mult c hsize hmult).property

/-- The meaning read at the raw tree is the meaning the expression carries. -/
theorem foldOutSemV_eq_eval (R : RankedAlphabet)
    (algOf : (i : Fin R.card) → COf (R.arity i))
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool)
    (halg : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      semAt (R.arity i) (algOf i).val.val (algOf i).property f = alg i f)
    (mult c : ℕ)
    (hsize : ∀ w : List Bool,
      stackSize (foldScanFinal R alg w).stack ≤ c * w.length)
    (hmult : 2 * c + 2 ≤ mult) :
    transport (foldOutOfV R algOf alg halg mult c hsize hmult).property
        (foldOutOfV R algOf alg halg mult c hsize hmult).val.eval =
      foldOutSemV R algOf alg halg mult c hsize hmult := rfl

/-- The expression at a bitstring carrier computes the fold: the readout on the
scan is `Geb.CobhamFold.foldOut`, spelled by `outWordV`. With
`Geb.CobhamFold.foldOut_eq` this is `RankedAlphabet.parse` followed by the
algebra morphism out of the term algebra. -/
theorem foldOutSemV_eq (R : RankedAlphabet)
    (algOf : (i : Fin R.card) → COf (R.arity i))
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool)
    (halg : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      semAt (R.arity i) (algOf i).val.val (algOf i).property f = alg i f)
    (mult c : ℕ)
    (hsize : ∀ w : List Bool,
      stackSize (foldScanFinal R alg w).stack ≤ c * w.length)
    (hmult : 2 * c + 2 ≤ mult) (w : List Bool) :
    foldOutSemV R algOf alg halg mult c hsize hmult ![w] =
      outWordV (foldOut R alg w) := by
  have happly : foldOutSemV R algOf alg halg mult c hsize hmult ![w] =
      stepWord (readOfV R) (foldSemV R algOf mult ![w]) :=
    congrArg (semAt 1 (readOfV R).val.val (readOfV R).property)
      (funext fun i ↦ match i with | ⟨0, _⟩ => rfl)
  rw [happly, foldSemV_eq R algOf alg halg mult w,
    stepWord_readOfV R _ (length_buf_foldScanFinal_lt R alg w), foldOut]

/-- A scaled family's sum is the scaled sum. -/
private theorem sum_ofFn_mul (c n : ℕ) (g : Fin n → ℕ) :
    (List.ofFn fun d ↦ c * g d).sum = c * (List.ofFn g).sum := by
  rw [List.ofFn_eq_map, List.ofFn_eq_map, List.sum_map_mul_left]

/-- Sums of families order pointwise. `List.sum_le_sum` states this over
`List.map`, but in `Mathlib.Algebra.Order.BigOperators.Group.List`, outside this
module's import closure. -/
private theorem sum_ofFn_le : ∀ (n : ℕ) (g h : Fin n → ℕ), (∀ d, g d ≤ h d) →
    (List.ofFn g).sum ≤ (List.ofFn h).sum :=
  Nat.rec (fun _ _ _ ↦ by rw [List.ofFn_zero, List.ofFn_zero])
    fun n ih g h hgh ↦ by
      rw [List.ofFn_succ, List.ofFn_succ, List.sum_cons, List.sum_cons]
      exact Nat.add_le_add (hgh 0)
        (ih (fun i ↦ g i.succ) (fun i ↦ h i.succ) fun i ↦ hgh i.succ)

/-- An algebra that lengthens by at most a constant per symbol folds a term to a
value linear in the term's node count. The term-level companion of
`stackSize_le_of_growth`, which derives `length_foldSemV_le`'s hypothesis from
the same condition: this states what the condition says about the fold's value,
that a fold meeting it is one whose output the class can hold. -/
theorem length_fold_le_of_growth (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool) (c : ℕ)
    (hgrow : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      (alg i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + c) :
    ∀ t : R.Term, (Term.fold R alg t).length ≤ c * t.size :=
  Term.induction
    (motive := fun t ↦ (Term.fold R alg t).length ≤ c * t.size)
    fun i ch ih ↦ by
      beta_reduce
      rw [Term.fold_mk, size_mk, Nat.mul_add, Nat.mul_one]
      refine Nat.le_trans (hgrow i fun d ↦ Term.fold R alg (ch d)) ?_
      refine Nat.add_le_add_right ?_ c
      refine Nat.le_trans
        (sum_ofFn_le (R.arity i) _ (fun d ↦ c * (ch d).size) ih) ?_
      exact Nat.le_of_eq (sum_ofFn_mul c (R.arity i) fun d ↦ (ch d).size)

/-- The pending values' total length is additive over a concatenation. -/
theorem stackSize_append (a b : List (List Bool)) :
    stackSize (a ++ b) = stackSize a + stackSize b := by
  rw [stackSize, stackSize, stackSize, List.flatten_append, List.length_append]

/-- The pending values' total length splits at any point. -/
theorem stackSize_take_add_drop (st : List (List Bool)) (r : ℕ) :
    stackSize (st.take r) + stackSize (st.drop r) = stackSize st := by
  rw [← stackSize_append, List.take_append_drop]

/-- The lengths of the first `r` entries sum to their total length. -/
private theorem sum_ofFn_getElem : ∀ (r : ℕ) (st : List (List Bool)) (h : r ≤ st.length),
    (List.ofFn fun d : Fin r ↦
      (st[d.val]'(Nat.lt_of_lt_of_le d.isLt h)).length).sum = stackSize (st.take r) :=
  Nat.rec (fun st _ ↦ by rw [List.ofFn_zero, List.sum_nil, List.take_zero, stackSize_nil])
    fun r ih st h ↦ match st with
      | [] => absurd h (Nat.not_succ_le_zero r)
      | a :: t => by
        rw [List.ofFn_succ, List.sum_cons, List.take_succ_cons, stackSize_cons]
        exact congrArg (a.length + ·) (ih t (Nat.le_of_succ_le_succ h))

/-- One step raises the potential `R.width * stackSize + c * |buf|` by at
most `c`, the growth condition assumed only of arguments the stack holds.
`Geb.CobhamFold.potential_foldScanStep_le` is this where the condition holds
at arbitrary arguments. -/
theorem potential_foldScanStep_le_of_invariant (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool)
    (P : List Bool → Prop) (c : ℕ)
    (hgrow : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      (∀ d, P (f d)) →
      (alg i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + c)
    (b : Bool) (s : FoldScan (List Bool)) (hs : ∀ v ∈ s.stack, P v) :
    R.width * stackSize (foldScanStep R alg b s).stack +
        c * (foldScanStep R alg b s).buf.length ≤
      R.width * stackSize s.stack + c * s.buf.length + c := by
  obtain ⟨buf, stack, live⟩ := s
  dsimp only at hs
  rw [foldScanStep]
  dsimp only
  cases live
  · dsimp only
    omega
  · dsimp only
    by_cases hlen : (b :: buf).length = R.width
    · rw [if_pos hlen]
      have hbw : buf.length + 1 = R.width := by
        rw [List.length_cons] at hlen
        omega
      match hsym : symOf R (decodeBits (b :: buf)) with
      | none =>
        dsimp only
        simp only [List.length_nil, Nat.mul_zero]
        omega
      | some i =>
        dsimp only
        by_cases hst : R.arity i ≤ stack.length
        · rw [dif_pos hst]
          dsimp only
          have hsum := sum_ofFn_getElem (R.arity i) stack hst
          -- the popped arguments are members of the stack, so `hs` supplies
          -- `P` at each
          have halg := hgrow i
            (fun d ↦ stack[d.val]'(Nat.lt_of_lt_of_le d.isLt hst))
            fun d ↦ hs _ (List.getElem_mem _)
          rw [hsum] at halg
          have hsplit := stackSize_take_add_drop stack (R.arity i)
          have hnew : stackSize ((alg i fun d ↦
              stack[d.val]'(Nat.lt_of_lt_of_le d.isLt hst)) ::
                stack.drop (R.arity i)) ≤ stackSize stack + c := by
            rw [stackSize_cons]
            omega
          have hmul : R.width * stackSize ((alg i fun d ↦
              stack[d.val]'(Nat.lt_of_lt_of_le d.isLt hst)) ::
                stack.drop (R.arity i)) ≤ R.width * (stackSize stack + c) :=
            Nat.mul_le_mul_left _ hnew
          rw [Nat.mul_add] at hmul
          have hcw : R.width * c = c * R.width := Nat.mul_comm _ _
          have hcb : c * buf.length + c = c * R.width := by
            rw [← hbw, Nat.mul_add, Nat.mul_one]
          simp only [List.length_nil, Nat.mul_zero, Nat.add_zero]
          omega
        · rw [dif_neg hst]
          dsimp only
          simp only [List.length_nil, Nat.mul_zero]
          omega
    · rw [if_neg hlen]
      dsimp only
      have hcb : c * (buf.length + 1) = c * buf.length + c := by
        rw [Nat.mul_add, Nat.mul_one]
      simp only [List.length_cons]
      omega

/-- One step raises the potential `R.width * stackSize + c * |buf|` by at most
`c`. Every clause but the completing pop leaves the stack alone, and the pop
adds at most `c` to it while clearing a block worth `R.width` bits. -/
theorem potential_foldScanStep_le (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool) (c : ℕ)
    (hgrow : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      (alg i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + c)
    (b : Bool) (s : FoldScan (List Bool)) :
    R.width * stackSize (foldScanStep R alg b s).stack +
        c * (foldScanStep R alg b s).buf.length ≤
      R.width * stackSize s.stack + c * s.buf.length + c :=
  potential_foldScanStep_le_of_invariant R alg (fun _ ↦ True) c
    (fun i f _ ↦ hgrow i f) b s fun _ _ ↦ trivial

/-- The potential never exceeds `c` per input bit, the growth condition
assumed only of values satisfying `P`, which
`Geb.CobhamFold.mem_stack_foldScanFinal` carries along the scan.
`Geb.CobhamFold.potential_foldScanFinal_le` is this at the trivial
predicate. -/
theorem potential_foldScanFinal_le_of_invariant (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool)
    (P : List Bool → Prop) (c : ℕ)
    (hpush : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool), P (alg i f))
    (hgrow : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      (∀ d, P (f d)) →
      (alg i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + c) :
    ∀ w : List Bool,
      R.width * stackSize (foldScanFinal R alg w).stack +
        c * (foldScanFinal R alg w).buf.length ≤ c * w.length :=
  List.rec (by
      rw [List.length_nil, Nat.mul_zero]
      exact Nat.le_of_eq rfl)
    fun b v ih ↦ by
      have hstep := potential_foldScanStep_le_of_invariant R alg P c hgrow b
        (foldScanFinal R alg v) (mem_stack_foldScanFinal R alg P hpush v)
      have hcons : foldScanFinal R alg (b :: v) =
          foldScanStep R alg b (foldScanFinal R alg v) := rfl
      have hc : c * (v.length + 1) = c * v.length + c := by
        rw [Nat.mul_add, Nat.mul_one]
      rw [hcons, List.length_cons]
      omega

/-- An algebra whose values satisfy an invariant under which it lengthens by
at most a constant per symbol keeps the pending values linear in the input.
`Geb.CobhamFold.stackSize_le_of_growth` is this at the trivial invariant. -/
theorem stackSize_le_of_growth_of_invariant (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool)
    (P : List Bool → Prop) (c : ℕ)
    (hpush : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool), P (alg i f))
    (hgrow : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      (∀ d, P (f d)) →
      (alg i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + c)
    (w : List Bool) :
    stackSize (foldScanFinal R alg w).stack ≤ c * w.length := by
  have h := potential_foldScanFinal_le_of_invariant R alg P c hpush hgrow w
  have hm : stackSize (foldScanFinal R alg w).stack ≤
      R.width * stackSize (foldScanFinal R alg w).stack :=
    Nat.le_mul_of_pos_left _ R.width_pos
  omega

/-- The potential never exceeds `c` per input bit. -/
theorem potential_foldScanFinal_le (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool) (c : ℕ)
    (hgrow : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      (alg i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + c) :
    ∀ w : List Bool,
      R.width * stackSize (foldScanFinal R alg w).stack +
        c * (foldScanFinal R alg w).buf.length ≤ c * w.length :=
  potential_foldScanFinal_le_of_invariant R alg (fun _ ↦ True) c
    (fun _ _ ↦ trivial) fun i f _ ↦ hgrow i f

/-- An algebra that lengthens by at most a constant per symbol keeps the pending
values linear in the input, which is the hypothesis
`Geb.CobhamFold.length_foldSemV_le` takes. This is the bridge from a condition on
the algebra alone to the condition the recursion bound consumes. -/
theorem stackSize_le_of_growth (R : RankedAlphabet)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → List Bool) → List Bool) (c : ℕ)
    (hgrow : ∀ (i : Fin R.card) (f : Fin (R.arity i) → List Bool),
      (alg i f).length ≤ (List.ofFn fun d ↦ (f d).length).sum + c)
    (w : List Bool) :
    stackSize (foldScanFinal R alg w).stack ≤ c * w.length :=
  stackSize_le_of_growth_of_invariant R alg (fun _ ↦ True) c
    (fun _ _ ↦ trivial) (fun i f _ ↦ hgrow i f) w

end Geb.CobhamFold

end
