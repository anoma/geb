/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Prototypes.Computability.CobhamFoldProto.Bound
public import Geb.Prototypes.Computability.CobhamFoldProto.Layout

/-!
# The fold over recognized terms as an expression of Cobham's class

The fold scan of `Geb/Prototypes/Computability/CobhamFoldProto/Fold.lean`, laid
out as a bitstring by
`Geb/Prototypes/Computability/CobhamFoldProto/Layout.lean`, carried by the scan
combinator of `Geb/Prototypes/Computability/CobhamFoldProto/Bound.lean`, and
composed with a readout into an expression computing
`RankedAlphabet.parse` followed by the fold.

At `p = 0` and the carrier `Unit` this construction meets the recognizer of
`Geb/Mathlib/Computability/Cobham/RankedTree.lean`; the module
`Geb/Prototypes/Computability/CobhamFoldProto/Degenerate.lean` identifies the
state layout, the dispatch window, the readout window and the step, and the two
accept the same language. They are not the same expression.
The raw trees differ — `Geb.CobhamFold.boundMulRaw_ne_boundRaw` separates the
two bound children at multiplicity one, at every growth — and the rejecting
words differ, this module's `outWord` spelling both branches at the width
`p + 1` where
`Cobham.isRankedSem_eq_ite` gives the empty bitstring.

## Main definitions

* `Geb.CobhamFold.foldStepF` — one step of the scan, as an expression of arity
  one.
* `Geb.CobhamFold.foldGrowth` — the growth the state layout's fixed part
  contributes.
* `Geb.CobhamFold.foldSemF` — the meaning of the scan.
* `Geb.CobhamFold.foldExprF`, `Geb.CobhamFold.foldExprOfF` — the scan as an
  expression of `Cobham.C`, and at its declared arity.
* `Geb.CobhamFold.readoutWidth`, `Geb.CobhamFold.outWord`,
  `Geb.CobhamFold.readState`, `Geb.CobhamFold.readOf` — the readout's window,
  its output word, the `Option` it reads off the window, and the readout as an
  expression.
* `Geb.CobhamFold.foldOutOf`, `Geb.CobhamFold.foldOutExpr`,
  `Geb.CobhamFold.foldOutSem` — the readout composed onto the scan by
  `Geb.CobhamFold.comp1Of`.

## Main statements

* `Geb.CobhamFold.stepWord_foldStepF_of_lt` — a step of the expression computes
  a step of the fold scan.
* `Geb.CobhamFold.foldSemF_eq` — the expression computes the fold scan's state
  word on every input.
* `Geb.CobhamFold.length_foldSemF_le` — the recursion bound the scan combinator
  asks for, at a multiplier covering one stack entry per symbol block.
* `Geb.CobhamFold.length_outWord`, `Geb.CobhamFold.headD_outWord`,
  `Geb.CobhamFold.bits_tail_outWord` — the output's width, the marker separating
  its two branches, and the recoverability of the value.
* `Geb.CobhamFold.stepWord_readOf` — the readout's value at the state it reads.
* `Geb.CobhamFold.foldOutSem_eq` — the composition computes
  `Geb.CobhamFold.foldOut`, spelled by `outWord`.

* `Geb.CobhamFold.foldOutSem_eq_parse` — the same value read as
  `RankedAlphabet.parse` followed by the algebra morphism.
* `Geb.CobhamFold.foldSemF_eq_eval`, `Geb.CobhamFold.foldOutSem_eq_eval` — the
  meanings read at the raw trees are the meanings the expressions carry.

## Implementation notes

The multiplier is a parameter constrained by `p + 1 ≤ mult * R.width`, rather
than fixed at `p + 1`. The state carries one `(p + 1)`-bit entry per pending
subterm and the pending count rises once per `R.width` input bits — that is
`Geb.CobhamFold.width_mul_depth_scanFinal_le` — so any multiplier meeting the
inequality bounds the state. `mult = p + 1` always meets it,
`RankedAlphabet.width_pos` giving `1 ≤ R.width`; a wide alphabet admits a
smaller one.

The readout reads two stack entries: one to carry the value, and one more whose
marker distinguishes a stack of exactly one entry from a longer one. That is the
`Cobham.acceptWord R ++ [false]` of the recognizer's verdict test, one entry
wide rather than one bit wide.

`outWord` spells `none` as a `false` marker followed by `p` `false` bits, so
both branches have the width `p + 1`, and the marker alone separates them.
A rejected word receives that word rather than merely something other than an
accepted one, which is the discipline `Cobham.isRankedSem_eq_ite` records.

`readState` tests the decoded state's three fields rather than matching on its
stack: a match whose pattern fixes the stack's length does not reduce at a
variable stack.

## References

* [Cobham1965]

## Tags

Cobham, bounded recursion on notation, ranked alphabet, fold, catamorphism
-/

@[expose] public section

namespace Geb.CobhamFold

open Cobham RankedAlphabet

universe u

variable {α : Type u} {p : ℕ}

/-- One step of the fold expression: dispatch on the state's leading bits,
prepend the rebuilt prefix and drop the consumed bits. Every branch has that one
shape. -/
def foldStepF (R : RankedAlphabet) (p : ℕ) (enc : α → Fin p → Bool)
    (dec : (Fin p → Bool) → α)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (b : Bool) : COf 1 :=
  diagOf (casesOf (dispatchWidthF R p) fun v ↦
    prependOf (nextPrefixF R enc alg b (decodeStateF R p dec v))
      (predIterOf (dropCountF R p b (decodeStateF R p dec v))))

/-- A step of the expression computes a step of the fold scan, on a state whose
incomplete block is short of the width. This is where the decoder, the two
truncation lemmas and the step lemma meet. -/
theorem stepWord_foldStepF_of_lt (R : RankedAlphabet) (p : ℕ)
    (enc : α → Fin p → Bool) (dec : (Fin p → Bool) → α)
    (hdec : ∀ a, dec (enc a) = a)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (b : Bool)
    (s : FoldScan α) (h : s.buf.length < R.width) :
    stepWord (foldStepF R p enc dec alg b) (stateWordF R enc s) =
      stateWordF R enc (foldScanStep R alg b s) := by
  rw [foldStepF, stepWord_diagOf]
  change casesSem (dispatchWidthF R p) _ ![stateWordF R enc s, stateWordF R enc s] = _
  rw [casesSem_eq, stepWord_prependOf, stepWord_predIterOf,
    decodeStateF_stateWordF_of_lt R dec enc hdec s h, nextPrefixF_take_stack,
    dropCountF_take_stack, stateWordF_foldScanStep_of_lt R enc alg b s h]

/-- The growth the state layout's fixed part contributes: the flag and the
slot. -/
def foldGrowth (R : RankedAlphabet) : ℕ := 1 + R.width

/-- The fold expression's scan, at the two steps and the multiplicative
bound. -/
def foldSemF (R : RankedAlphabet) (p : ℕ) (enc : α → Fin p → Bool)
    (dec : (Fin p → Bool) → α)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (mult : ℕ) : Sem 1 :=
  scanBSem (constAtOf 0 (stateWordF R enc ⟨[], [], true⟩))
    (foldStepF R p enc dec alg false) (foldStepF R p enc dec alg true)
    (boundMulRaw mult (foldGrowth R)) (wValid_boundMulRaw mult (foldGrowth R))
    (wIndexRoot_boundMulRaw mult (foldGrowth R))

/-- The expression computes the fold scan's state word on every input. -/
theorem foldSemF_eq (R : RankedAlphabet) (p : ℕ) (enc : α → Fin p → Bool)
    (dec : (Fin p → Bool) → α) (hdec : ∀ a, dec (enc a) = a)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (mult : ℕ)
    (w : List Bool) :
    foldSemF R p enc dec alg mult ![w] =
      stateWordF R enc (foldScanFinal R alg w) := by
  rw [foldSemF, scanBSem_eq]
  refine List.rec ?_ ?_ w
  · rw [List.foldr_nil, baseWord_constAtOf]
    rfl
  · intro b v ih
    rw [List.foldr_cons, ih]
    cases b
    · exact stepWord_foldStepF_of_lt R p enc dec hdec alg false _
        (length_buf_foldScanFinal_lt R alg v)
    · exact stepWord_foldStepF_of_lt R p enc dec hdec alg true _
        (length_buf_foldScanFinal_lt R alg v)

/-- The recursion bound the scan combinator asks for. The state carries one
`(p + 1)`-bit entry per pending subterm, and the pending count rises once per
`R.width` input bits, so a multiplier covering one entry per block bounds the
state. Stated at `scanBSem`, which is the form `scanMul` consumes. -/
theorem length_foldSemF_le (R : RankedAlphabet) (p : ℕ) (enc : α → Fin p → Bool)
    (dec : (Fin p → Bool) → α) (hdec : ∀ a, dec (enc a) = a)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (mult : ℕ)
    (hmult : p + 1 ≤ mult * R.width) (w : List Bool) :
    (scanBSem (constAtOf 0 (stateWordF R enc ⟨[], [], true⟩))
      (foldStepF R p enc dec alg false) (foldStepF R p enc dec alg true)
      (boundMulRaw mult (foldGrowth R)) (wValid_boundMulRaw mult (foldGrowth R))
      (wIndexRoot_boundMulRaw mult (foldGrowth R))
      ![w]).length ≤ mult * w.length + foldGrowth R := by
  have hstate : (scanBSem (constAtOf 0 (stateWordF R enc ⟨[], [], true⟩))
      (foldStepF R p enc dec alg false) (foldStepF R p enc dec alg true)
      (boundMulRaw mult (foldGrowth R)) (wValid_boundMulRaw mult (foldGrowth R))
      (wIndexRoot_boundMulRaw mult (foldGrowth R)) ![w]).length =
      1 + R.width + (p + 1) * (R.scanFinal w).depth := by
    rw [← foldSemF, foldSemF_eq R p enc dec hdec alg mult w,
      length_stateWordF_of_lt R enc _ (length_buf_foldScanFinal_lt R alg w),
      length_stack_foldScanFinal]
  have hd : R.width * (R.scanFinal w).depth ≤ w.length :=
    width_mul_depth_scanFinal_le R w
  have h1 : (p + 1) * (R.scanFinal w).depth ≤
      mult * R.width * (R.scanFinal w).depth :=
    Nat.mul_le_mul_right _ hmult
  have h2 : mult * R.width * (R.scanFinal w).depth =
      mult * (R.width * (R.scanFinal w).depth) := Nat.mul_assoc _ _ _
  have h3 : mult * (R.width * (R.scanFinal w).depth) ≤ mult * w.length :=
    Nat.mul_le_mul_left _ hd
  rw [hstate, foldGrowth]
  omega

/-- The scan as a member of `Cobham.C`, at its arity: the form consumers take,
`foldExprF` being its underlying expression. -/
def foldExprOfF (R : RankedAlphabet) (p : ℕ) (enc : α → Fin p → Bool)
    (dec : (Fin p → Bool) → α) (hdec : ∀ a, dec (enc a) = a)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (mult : ℕ)
    (hmult : p + 1 ≤ mult * R.width) : COf 1 :=
  scanMulOf (constAtOf 0 (stateWordF R enc ⟨[], [], true⟩))
    (foldStepF R p enc dec alg false) (foldStepF R p enc dec alg true)
    mult (foldGrowth R) (length_foldSemF_le R p enc dec hdec alg mult hmult)

/-- The scan as an expression of Cobham's class, its recursion bound discharged
by `length_foldSemF_le`. -/
def foldExprF (R : RankedAlphabet) (p : ℕ) (enc : α → Fin p → Bool)
    (dec : (Fin p → Bool) → α) (hdec : ∀ a, dec (enc a) = a)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (mult : ℕ)
    (hmult : p + 1 ≤ mult * R.width) : C :=
  (foldExprOfF R p enc dec hdec alg mult hmult).val

/-- The meaning `foldSemF` reads at the raw tree is the meaning `foldExprF`
carries. -/
theorem foldSemF_eq_eval (R : RankedAlphabet) (p : ℕ) (enc : α → Fin p → Bool)
    (dec : (Fin p → Bool) → α) (hdec : ∀ a, dec (enc a) = a)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (mult : ℕ)
    (hmult : p + 1 ≤ mult * R.width) :
    transport (foldExprOfF R p enc dec hdec alg mult hmult).property
        (foldExprOfF R p enc dec hdec alg mult hmult).val.eval =
      foldSemF R p enc dec alg mult := rfl

/-- The number of state bits the readout dispatches on: the flag, the slot, and
two stack entries. -/
def readoutWidth (R : RankedAlphabet) (p : ℕ) : ℕ := 1 + R.width + (p + 1) * 2

/-- The readout's output word: a marked encoding at a value, and a `false`
marker followed by `p` `false` bits at none. Both branches have width
`p + 1`. -/
def outWord (enc : α → Fin p → Bool) : Option α → List Bool
  | none => false :: List.replicate p false
  | some a => entryBits enc a

/-- Both branches of the output have an entry's width, so the leading marker
alone separates them. -/
theorem length_outWord (enc : α → Fin p → Bool) :
    ∀ x : Option α, (outWord enc x).length = p + 1
  | none => by rw [outWord, List.length_cons, List.length_replicate]
  | some a => length_entryBits enc a

/-- The output's leading marker is set exactly at a value, so a consumer
separates the two branches by one bit. -/
theorem headD_outWord (enc : α → Fin p → Bool) :
    ∀ x : Option α, (outWord enc x).headD false = x.isSome
  | none => rfl
  | some _ => rfl

/-- The carrier value is recoverable from the output: past the marker the
output is the encoding, which a retraction inverts. -/
theorem bits_tail_outWord (enc : α → Fin p → Bool) (a : α) :
    bits p (outWord enc (some a)).tail = enc a := by
  rw [outWord, entryBits, List.tail_cons, bits_ofFn]

/-- The `Option` the readout reads off its window: the top of the stack when the
state is live, carries no incomplete block and holds exactly one entry. The
three tests are those of `Geb.CobhamFold.foldOut`. -/
def readState (R : RankedAlphabet) (p : ℕ) (dec : (Fin p → Bool) → α)
    (v : Fin (readoutWidth R p) → Bool) : Option α :=
  if (decodeStateAt R p dec (readoutWidth R p) 2 v).live &&
      (decodeStateAt R p dec (readoutWidth R p) 2 v).buf.isEmpty &&
      (decodeStateAt R p dec (readoutWidth R p) 2 v).stack.length == 1 then
    (decodeStateAt R p dec (readoutWidth R p) 2 v).stack.head?
  else none

/-- The readout as an expression of arity one: a dispatch on the verdict window
whose every branch is a constant word. -/
def readOf (R : RankedAlphabet) (p : ℕ) (enc : α → Fin p → Bool)
    (dec : (Fin p → Bool) → α) : COf 1 :=
  diagOf (casesOf (readoutWidth R p) fun v ↦
    constAtOf 1 (outWord enc (readState R p dec v)))

/-- The readout's value at the state it reads. -/
theorem stepWord_readOf (R : RankedAlphabet) (p : ℕ) (enc : α → Fin p → Bool)
    (dec : (Fin p → Bool) → α) (u : List Bool) :
    stepWord (readOf R p enc dec) u =
      outWord enc (readState R p dec (bits (readoutWidth R p) u)) := by
  rw [readOf, stepWord_diagOf]
  change casesSem (readoutWidth R p) _ ![u, u] = _
  rw [casesSem_eq, stepWord_constAtOf]

/-- The readout at the state word of a fold scan is the fold's `Option`. The
decoder truncates the stack at two entries, which leaves all three tests
unchanged: the marker of the second entry is what separates a stack of one from
a longer one. -/
theorem readState_stateWordF (R : RankedAlphabet) (p : ℕ)
    (enc : α → Fin p → Bool) (dec : (Fin p → Bool) → α)
    (hdec : ∀ a, dec (enc a) = a) (s : FoldScan α)
    (h : s.buf.length < R.width) :
    readState R p dec (bits (readoutWidth R p) (stateWordF R enc s)) =
      (if s.live && s.buf.isEmpty && s.stack.length == 1 then s.stack.head?
        else none) := by
  have hdecode := decodeStateAt_stateWordF_of_lt R dec enc hdec s
    (readoutWidth R p) 2 (by rw [readoutWidth]) h
  rw [readState, hdecode]
  dsimp only
  have hlen : (s.stack.take 2).length = min 2 s.stack.length := List.length_take
  by_cases hone : s.stack.length = 1
  · have h2 : (s.stack.take 2).length = 1 := by
      rw [hlen, hone]
      omega
    have hhead : (s.stack.take 2).head? = s.stack.head? := by
      match s.stack with
      | [] => rfl
      | _ :: _ => rfl
    rw [h2, hhead, hone]
  · have h2 : ¬ (s.stack.take 2).length = 1 := by
      rw [hlen]
      omega
    rw [Bool.and_eq_false_imp.mpr fun _ ↦ beq_eq_false_iff_ne.mpr h2,
      Bool.and_eq_false_imp.mpr fun _ ↦ beq_eq_false_iff_ne.mpr hone]
    rfl

/-- The readout composed onto the scan, at its declared arity. -/
def foldOutOf (R : RankedAlphabet) (p : ℕ) (enc : α → Fin p → Bool)
    (dec : (Fin p → Bool) → α) (hdec : ∀ a, dec (enc a) = a)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (mult : ℕ)
    (hmult : p + 1 ≤ mult * R.width) : COf 1 :=
  comp1Of (readOf R p enc dec) (foldExprOfF R p enc dec hdec alg mult hmult)

/-- The fold as an expression of Cobham's class: the value of a bitstring's
term, spelled, and the absent value at a bitstring spelling no term. -/
def foldOutExpr (R : RankedAlphabet) (p : ℕ) (enc : α → Fin p → Bool)
    (dec : (Fin p → Bool) → α) (hdec : ∀ a, dec (enc a) = a)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (mult : ℕ)
    (hmult : p + 1 ≤ mult * R.width) : C :=
  (foldOutOf R p enc dec hdec alg mult hmult).val

/-- The fold's meaning at its arity, read at the raw tree. -/
def foldOutSem (R : RankedAlphabet) (p : ℕ) (enc : α → Fin p → Bool)
    (dec : (Fin p → Bool) → α) (hdec : ∀ a, dec (enc a) = a)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (mult : ℕ)
    (hmult : p + 1 ≤ mult * R.width) : Sem 1 :=
  semAt 1 (foldOutOf R p enc dec hdec alg mult hmult).val.val
    (foldOutOf R p enc dec hdec alg mult hmult).property

/-- The meaning `foldOutSem` reads at the raw tree is the meaning `foldOutExpr`
carries. -/
theorem foldOutSem_eq_eval (R : RankedAlphabet) (p : ℕ) (enc : α → Fin p → Bool)
    (dec : (Fin p → Bool) → α) (hdec : ∀ a, dec (enc a) = a)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (mult : ℕ)
    (hmult : p + 1 ≤ mult * R.width) :
    transport (foldOutOf R p enc dec hdec alg mult hmult).property
        (foldOutOf R p enc dec hdec alg mult hmult).val.eval =
      foldOutSem R p enc dec hdec alg mult hmult := rfl

/-- One step of the fold: the readout on the scan's value. -/
theorem foldOutSem_apply (R : RankedAlphabet) (p : ℕ) (enc : α → Fin p → Bool)
    (dec : (Fin p → Bool) → α) (hdec : ∀ a, dec (enc a) = a)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (mult : ℕ)
    (hmult : p + 1 ≤ mult * R.width) (w : List Bool) :
    foldOutSem R p enc dec hdec alg mult hmult ![w] =
      stepWord (readOf R p enc dec) (foldSemF R p enc dec alg mult ![w]) :=
  congrArg (semAt 1 (readOf R p enc dec).val.val (readOf R p enc dec).property)
    (funext fun i ↦ match i with | ⟨0, _⟩ => rfl)

/-- The expression computes the fold: at a bitstring spelling a term, the marked
encoding of that term's value under the algebra, and at every other bitstring
the absent value. -/
theorem foldOutSem_eq (R : RankedAlphabet) (p : ℕ) (enc : α → Fin p → Bool)
    (dec : (Fin p → Bool) → α) (hdec : ∀ a, dec (enc a) = a)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (mult : ℕ)
    (hmult : p + 1 ≤ mult * R.width) (w : List Bool) :
    foldOutSem R p enc dec hdec alg mult hmult ![w] =
      outWord enc (foldOut R alg w) := by
  rw [foldOutSem_apply, foldSemF_eq R p enc dec hdec alg mult w, stepWord_readOf,
    readState_stateWordF R p enc dec hdec _ (length_buf_foldScanFinal_lt R alg w),
    foldOut]

/-- The expression computes the decoding followed by the fold: the unique
algebra morphism out of the term algebra, read off a preorder spelling. -/
theorem foldOutSem_eq_parse (R : RankedAlphabet) (p : ℕ)
    (enc : α → Fin p → Bool) (dec : (Fin p → Bool) → α)
    (hdec : ∀ a, dec (enc a) = a)
    (alg : (i : Fin R.card) → (Fin (R.arity i) → α) → α) (mult : ℕ)
    (hmult : p + 1 ≤ mult * R.width) (w : List Bool) :
    foldOutSem R p enc dec hdec alg mult hmult ![w] =
      outWord enc ((R.parse w).map (Term.fold R alg)) := by
  rw [foldOutSem_eq, foldOut_eq]

end Geb.CobhamFold

end
