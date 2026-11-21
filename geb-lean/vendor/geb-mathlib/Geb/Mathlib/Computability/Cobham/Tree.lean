/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
-- Modified from geb-mathlib by scripts/geb-mathlib-backport.patch.
module

public import Geb.Mathlib.Computability.Cobham.Basic
public import Geb.Mathlib.Computability.Cobham.Scan
public import Geb.Mathlib.Data.Tree.Ranked.Binary

/-!
# The preorder stack scan in Cobham's class

An expression of `C` computing, in a single right-to-left pass over a
bitstring, the stack depth of the word read as the preorder spelling of a
term of `RankedAlphabet.Binary.binRanked`, together with the scan's
liveness verdict. The two are carried in one recursive value, told apart
by its head: while no node bit has been read below depth two the value is
the depth in unary offset by one, so its head is `true`; once one has
been, the value is `[false]`, which the node step reproduces, that
value's two predecessors being empty. Each bit is read once.

The recursion is a `boundedRec` node, so admissibility requires a bound: the
scan's value is never longer than the recursion variable by more than one bit,
which the scanner's bound child expresses at growth one. That is the side
condition of bounded recursion on notation [Cobham1965], and discharging it is
what places the scan in `C` rather than merely in the syntax `sig` describes.

The one-test on the scan's predecessor is the recognizer, correct against the
`Valid` predicate of the encoding. Composed with
`RankedAlphabet.valid_iff_exists_spell`,
`isTreeSem_eq_singleton_iff_exists_spell` states that an expression of `C`
accepts exactly the spellings of terms.
`isTreeSem_eq_ite` pins its value on the rejecting branch as well: the two
`iff` statements alone do not imply it, since a recognizer returning
`[false]` rather than `[]` on a rejected word would satisfy both while
disagreeing with `isTreeSem_eq_ite` there, so the correctness the latter
states is a property of the function and not only of the accepted set.

`isTree_smashFree` places `isTree` in the subalgebra `SmashFree` names,
`[ε, I, s₀, s₁, ∗; COMP, BRN]`; with [Strahm2003] Theorem 1(2), deciding
`RankedAlphabet.Valid` at `RankedAlphabet.Binary.binRanked` is computable
simultaneously in polynomial time and linear space.

## Main definitions

* `Cobham.oneAt`, `Cobham.falseAt` — the one-bit strings at an arbitrary
  arity.
* `Cobham.inc` — prepending `true`, of arity one.
* `Cobham.predPred` — the argument with two bits dropped, of arity one.
* `Cobham.combFalseStep`, `Cobham.combTrueStep` — the leaf step and the node
  step of the scan, of arity one.
* `Cobham.comb` — the stack depth and the underflow verdict in one value, of
  arity one.
* `Cobham.eqOneInner` — whether the predecessor of the argument is empty, of
  arity one.
* `Cobham.eqOne` — whether a bitstring has length one, of arity one.
* `Cobham.isTree` — the recognizer, of arity one.
* `Cobham.combSem`, `Cobham.eqOneSem`, `Cobham.isTreeSem` — the meaning of
  the scan, the length test and the recognizer at its arity, over which
  every statement of the module is stated.

Every expression is given as a raw tree `…Raw` and as the expression `…` of `C`
carrying admissibility. The ascription `…Of` at the reduced arity is given
for the scan, the length test and the recognizer, matching the interface
`BellantoniCook.comb`, `BellantoniCook.eqOne` and `BellantoniCook.isTree`
present, and for an expression whose reduced arity a proof reads.

## Main statements

* `Cobham.combSem_def` — the scan's meaning is the scanner's, at the two
  steps.
* `Cobham.combSem_nil`, `Cobham.combSem_cons_false`,
  `Cobham.combSem_cons_true` — the scan unfolded at each constructor of the
  recursion variable, with the recursive value exposed.
* `Cobham.combSem_eq` — the scan computes `RankedAlphabet.Binary.depth` in
  unary, offset by one, while `RankedAlphabet.Binary.ok` holds, and `[false]`
  once it has failed.
* `Cobham.length_combSem_le` — the recursion bound `scan` asks for, which
  `comb`, `combOf` and `combSem_eq_eval` each pass to the scanner.
* `Cobham.combSem_eq_eval`, `Cobham.isTreeSem_eq_eval` — the meaning read at
  the raw tree is the meaning the expression of `C` carries.
* `Cobham.eqOneSem_env` — the one-test at an arbitrary environment is the
  test at the canonical one.
* `Cobham.eqOneSem_eq` — `eqOne` accepts exactly the bitstrings of length
  one.
* `Cobham.isTreeSem_apply` — one step of the recognizer: the one-test on
  the scan's predecessor.
* `Cobham.isTreeSem_eq_ite` — the recognizer's value on both branches:
  `[true]` on a word `binRanked`'s scan accepts and `[]` on every other.
* `Cobham.isTreeSem_eq_singleton_iff_valid` — `isTree` accepts exactly the
  words `binRanked`'s scan accepts.
* `Cobham.isTreeSem_eq_singleton_iff_exists_spell` — equivalently, exactly
  the spellings of `binRanked`'s terms.
* `Cobham.isTree_smashFree` — the recognizer lies in the subalgebra
  `SmashFree` names.

## Implementation notes

Each raw tree is named apart from the expression built on it because instance
search finds `Decidable (sig.WValid w)` when `w` is a constant but not when it
is a literal `WType.mk` application, so `decide` discharges admissibility only
of a named tree. `oneAtRaw` and `falseAtRaw` carry a free arity, at which
`decide` does not apply; their admissibility is the pair of an
`Unit ⊕ Fin m` case analysis and the `funext` that the index condition asks
for. The admissibility of an expression embedding `pred` or `cond` reuses that
expression's own component rather than repeating its proof.

`combSem` is the meaning read at the raw tree rather than at `comb`.
`Cobham.eval` asks only for admissibility as a `sig`-tree, not for the
recursion bound, so the scan is characterized by `combSem_eq` before the
expression carrying that bound exists. The bound is then that characterization
together with `RankedAlphabet.Binary.depth_le_length`: the value is `[false]`,
of length one, or the depth in unary offset by one, and the depth never
exceeds the word length, while the scanner's bound child, at growth one,
returns one bit more than the recursion variable. `combSem` is the scanner's
meaning at its arity, and `combSem_eq_eval` reads it back through `C.eval`, as
`isTreeSem_eq_eval` does for the recognizer.

That bound is a bound on the value `combSem` produces at each step, not a
bound on the cost of evaluating the expression that computes it: nothing in
this module measures a number of reduction steps or an amount of space
consumed while doing so. `isTree_smashFree` states only that `isTree` avoids
the `smash` generator; the polynomial-time, linear-space reading of that
membership is [Strahm2003] Theorem 1(2), cited and not reproved here.

`cond` and `pred` are `boundedRec` nodes in this algebra rather than
generators, so a step's meaning reduces only once the value it scrutinizes is
in constructor form: `combSem_cons_false` and `combSem_cons_true` are
therefore not definitional. Each is a corollary of `scanSem_cons`, proved by
rewriting to the step's own application at the recursive value, generalizing
that value, and matching on it. The node step's guard drops two bits through
two `pred` nodes, each of which peels a bit only at a literal, so the match
reaches the fourth constructor layer of the value.

`combSem` names the meaning at the reduced arity, so that rewriting under it
type-checks. A meaning taken through the `Sigma` projection instead has a type
headed by that projection rather than by an arrow, and `rw` under it fails as
not type-correct at `implicit` transparency.

`eqOne` and `isTree` are `comp` compositions of `pred`, `cond` and `comb`,
carrying no `boundedRec` node of their own, so each admissibility obligation
is discharged by the anonymous constructor pairing the node's own condition,
vacuous at a `comp`, with a case analysis over its children, reusing the
embedded subexpression's own `RecBounded` component rather than repeating its
proof. Unlike a primitive predecessor shape, `pred` here is itself a
`boundedRec` node (`predRaw`), so its value on the scan's result does not
reduce on a symbolic word: `isTreeSem_apply` is proved by rewriting to the
composition's own application, generalizing the scan's value, and matching
on it, rather than by `rfl`.

The meanings this module reads at a raw tree are taken through `Cobham.semAt`,
which names the composite of `fst_eval` with the tree's arity equation once
rather than spelling it at each site.

## References

* [Cobham1965]
* [Strahm2003]

## Tags

Cobham, bounded recursion on notation, binary tree, preorder, stack depth,
smash-free, polynomial time, linear space
-/

namespace Cobham

open RankedAlphabet.Binary

public section

/-- The one-bit string `[true]` at an arbitrary arity. -/
@[expose] def oneAtRaw (n : ℕ) : sig.toPFunctor.W :=
  WType.mk (.comp n 1) fun d ↦
    match d with
    | .inl () => WType.mk (.succ true) Fin.elim0
    | .inr _ => zeroAtRaw n

/-- The one-bit string `[true]` as an expression of arity `n`. -/
@[expose] def oneAt (n : ℕ) : C :=
  ⟨⟨oneAtRaw n,
      ⟨fun d ↦ match d with
        | .inl () => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
        | .inr _ => (zeroAt n).val.property,
      funext fun d ↦ match d with
        | .inl () => rfl
        | .inr _ => rfl⟩⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr _ => (zeroAt n).property⟩⟩

/-- `oneAt n` at its declared arity. -/
@[expose] def oneAtOf (n : ℕ) : COf n := ⟨oneAt n, rfl⟩

/-- The one-bit string `[false]` at an arbitrary arity. -/
@[expose] def falseAtRaw (n : ℕ) : sig.toPFunctor.W :=
  WType.mk (.comp n 1) fun d ↦
    match d with
    | .inl () => WType.mk (.succ false) Fin.elim0
    | .inr _ => zeroAtRaw n

/-- The one-bit string `[false]` as an expression of arity `n`. -/
@[expose] def falseAt (n : ℕ) : C :=
  ⟨⟨falseAtRaw n,
      ⟨fun d ↦ match d with
        | .inl () => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
        | .inr _ => (zeroAt n).val.property,
      funext fun d ↦ match d with
        | .inl () => rfl
        | .inr _ => rfl⟩⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr _ => (zeroAt n).property⟩⟩

/-- `falseAt n` at its declared arity. -/
@[expose] def falseAtOf (n : ℕ) : COf n := ⟨falseAt n, rfl⟩

/-- Prepend `true` to the sole argument. -/
@[expose] def incRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1) fun d ↦
    match d with
    | .inl () => WType.mk (.succ true) Fin.elim0
    | .inr _ => WType.mk (.proj 1 0) Fin.elim0

/-- Prepending `true`, as an expression of arity one. -/
@[expose] def inc : C :=
  ⟨⟨incRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩⟩

/-- `inc` at its declared arity. -/
@[expose] def incOf : COf 1 := ⟨inc, rfl⟩

/-- The sole argument with two bits dropped. It is empty exactly when the
argument is the failure flag, whose two predecessors truncate to the empty
bitstring, or a depth below two. -/
@[expose] def predPredRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1) fun d ↦
    match d with
    | .inl () => predRaw
    | .inr _ =>
      WType.mk (.comp 1 1) fun e ↦
        match e with
        | .inl () => predRaw
        | .inr _ => WType.mk (.proj 1 0) Fin.elim0

/-- Dropping two bits, as an expression of arity one. -/
@[expose] def predPred : C :=
  ⟨⟨predPredRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => pred.val.property
      | .inr _ =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => pred.val.property
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩⟩⟩

/-- `predPred` at its declared arity. -/
@[expose] def predPredOf : COf 1 := ⟨predPred, rfl⟩

/-- The leaf step: push a level onto a live value, whose head is `true`, and
return the failure flag on a value that is empty or has head `false`. Of
arity one, the state being the sole argument a fold's step reads. -/
@[expose] def combFalseStepRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 4) fun d ↦
    match d with
    | .inl () => condRaw
    | .inr i =>
      ![WType.mk (.proj 1 0) Fin.elim0, falseAtRaw 1,
        WType.mk (.comp 1 1) (fun e ↦
          match e with
          | .inl () => incRaw
          | .inr _ => WType.mk (.proj 1 0) Fin.elim0),
        falseAtRaw 1] i

/-- The leaf step as an expression of arity one. -/
@[expose] def combFalseStep : C :=
  ⟨⟨combFalseStepRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => cond.val.property
      | .inr 0 => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr 1 => (falseAt 1).property
      | .inr 2 =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => inc.property
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩
      | .inr 3 => (falseAt 1).property⟩⟩

/-- `combFalseStep` at its declared arity. -/
@[expose] def combFalseStepOf : COf 1 := ⟨combFalseStep, rfl⟩

/-- The node step: pop a level when at least two remain, and return the
failure flag otherwise. An existing failure propagates, its guard being
empty. Of arity one, as `combFalseStep`. -/
@[expose] def combTrueStepRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 4) fun d ↦
    match d with
    | .inl () => condRaw
    | .inr i =>
      ![WType.mk (.comp 1 1) (fun e ↦
          match e with
          | .inl () => predPredRaw
          | .inr _ => WType.mk (.proj 1 0) Fin.elim0),
        falseAtRaw 1,
        WType.mk (.comp 1 1) (fun e ↦
          match e with
          | .inl () => predRaw
          | .inr _ => WType.mk (.proj 1 0) Fin.elim0),
        WType.mk (.comp 1 1) (fun e ↦
          match e with
          | .inl () => predRaw
          | .inr _ => WType.mk (.proj 1 0) Fin.elim0)] i

/-- The node step as an expression of arity one. -/
@[expose] def combTrueStep : C :=
  ⟨⟨combTrueStepRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => cond.val.property
      | .inr 0 =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => predPred.property
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩
      | .inr 1 => (falseAt 1).property
      | .inr 2 =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => pred.val.property
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩
      | .inr 3 =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => pred.val.property
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩⟩⟩

/-- `combTrueStep` at its declared arity. -/
@[expose] def combTrueStepOf : COf 1 := ⟨combTrueStep, rfl⟩

/-- The raw tree of the scan, as a scanner: base `[true]`, the empty bitstring
having depth zero and satisfying `RankedAlphabet.Binary.ok`; growth one, the
value being never longer than the recursion variable by more than one bit. -/
@[expose] def combRaw : sig.toPFunctor.W :=
  scanRaw (oneAtRaw 0) combFalseStepRaw combTrueStepRaw 1

/-- The scan's meaning at its arity, as the scanner's. `Cobham.eval` asks
only for admissibility as a `sig`-tree, so the scan is characterized before
the expression carrying its recursion bound exists. -/
@[expose] def combSem : Sem 1 :=
  scanSem (oneAtOf 0) combFalseStepOf combTrueStepOf 1

/-- The scan is the scanner at its two steps. Stated because a `def` carries
no equation lemma: the `cons` lemmas rewrite by it, and `length_combSem_le`
rewrites by it in reverse, its statement being the one `scan` asks for. -/
theorem combSem_def :
    combSem = scanSem (oneAtOf 0) combFalseStepOf combTrueStepOf 1 := rfl

/-- The scan's value on the empty bitstring: depth zero, offset by one. -/
theorem combSem_nil : combSem ![[]] = [true] := rfl

/-- A leaf bit pushes a level onto a live value, and is absorbed by a
failure. -/
theorem combSem_cons_false (v : List Bool) :
    combSem ![false :: v] =
      (match combSem ![v] with
       | [] => [false]
       | true :: _ => true :: combSem ![v]
       | false :: _ => [false]) := by
  rw [combSem_def, scanSem_cons]
  change stepWord combFalseStepOf (scanSem (oneAtOf 0) combFalseStepOf
    combTrueStepOf 1 ![v]) = _
  generalize scanSem (oneAtOf 0) combFalseStepOf combTrueStepOf 1 ![v] = r
  match r with
  | [] | true :: _ | false :: _ => rfl

/-- A node bit pops a level when at least two remain, and fails otherwise. The
guard is the value with two bits dropped, so a failure, whose two predecessors
are empty, propagates. -/
theorem combSem_cons_true (v : List Bool) :
    combSem ![true :: v] =
      (match (combSem ![v]).tail.tail with
       | [] => [false]
       | true :: _ => (combSem ![v]).tail
       | false :: _ => (combSem ![v]).tail) := by
  rw [combSem_def, scanSem_cons]
  change stepWord combTrueStepOf (scanSem (oneAtOf 0) combFalseStepOf
    combTrueStepOf 1 ![v]) = _
  generalize scanSem (oneAtOf 0) combFalseStepOf combTrueStepOf 1 ![v] = r
  match r with
  | [] => rfl
  | [c] => cases c <;> rfl
  | c :: d :: w =>
    cases c <;> cases d <;> (match w with | [] | true :: _ | false :: _ => rfl)

/-- The scan computes the stack depth in unary, offset by one, while
`RankedAlphabet.Binary.ok` holds, and the absorbing value `[false]` once it
has failed. -/
theorem combSem_eq (w : List Bool) :
    combSem ![w] =
      if ok w then List.replicate (depth w + 1) true
      else [false] := by
  refine List.rec (motive := fun u ↦ combSem ![u] =
    if ok u then List.replicate (depth u + 1) true else [false])
    rfl ?_ w
  intro b v ih
  cases hok : ok v
  · have hv : combSem ![v] = [false] := by rw [ih, hok]; rfl
    cases b
    · rw [combSem_cons_false, hv, ok_cons_false, hok]
      rfl
    · rw [combSem_cons_true, hv, ok_cons_true, hok]
      rfl
  · have hv : combSem ![v] = List.replicate (depth v + 1) true := by
      rw [ih, hok]; rfl
    cases b
    · rw [combSem_cons_false, hv, ok_cons_false, hok,
        depth_cons_false_of_ok v hok]
      rfl
    · rw [combSem_cons_true, hv, ok_cons_true, hok]
      -- the guard's two predecessors reduce only on a numeral of at least that
      -- size, so the depth is split into constructor forms; the conditional
      -- depth lemma applies only in the third case, the first two closing on
      -- the failed branch
      have hsplit : ∀ d : ℕ, d = 0 ∨ d = 1 ∨ ∃ m, d = m + 2 := fun d ↦
        match d with
        | 0 => Or.inl rfl
        | 1 => Or.inr (Or.inl rfl)
        | (m + 2) => Or.inr (Or.inr ⟨m, rfl⟩)
      obtain (h0 | h1 | ⟨m, hm⟩) := hsplit (depth v)
      · rw [h0]; rfl
      · rw [h1]; rfl
      · rw [depth_cons_true_of_ok_of_two_le_depth v hok (by omega), hm]; rfl

/-- The scan's value exceeds the recursion variable by at most one bit: it is
`[false]`, of length one, or the depth in unary offset by one, and the depth
never exceeds the word length (`RankedAlphabet.Binary.depth_le_length`). This
is the recursion bound `scan` asks for, at the growth its bound child
carries. -/
theorem length_combSem_le (u : List Bool) :
    (scanSem (oneAtOf 0) combFalseStepOf combTrueStepOf 1 ![u]).length ≤
      u.length + 1 := by
  rw [← combSem_def, combSem_eq]
  cases ok u
  · exact Nat.le_add_left 1 u.length
  · rw [if_pos rfl, List.length_replicate]
    exact Nat.succ_le_succ (depth_le_length u)

/-- The stack depth and the underflow verdict of a bitstring in one value, as
the scanner at the two steps, with `length_combSem_le` discharging its
recursion bound. -/
@[expose] def comb : C :=
  scan (oneAtOf 0) combFalseStepOf combTrueStepOf 1 length_combSem_le

/-- `comb` at its declared arity. -/
@[expose] def combOf : COf 1 :=
  scanOf (oneAtOf 0) combFalseStepOf combTrueStepOf 1 length_combSem_le

/-- The meaning `combSem` reads at the raw tree is the meaning `comb` carries:
the statements about the scan are statements about the member of `C` whose
recursion bound `comb` discharges. -/
theorem combSem_eq_eval : transport combOf.property combOf.val.eval = combSem :=
  scanSem_eq_eval (oneAtOf 0) combFalseStepOf combTrueStepOf 1 length_combSem_le

/-- The inner conditional of `eqOne`: whether the predecessor of the argument
is empty. -/
@[expose] def eqOneInnerRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 4) fun d ↦
    match d with
    | .inl () => condRaw
    | .inr i =>
      ![WType.mk (.comp 1 1) (fun e ↦
          match e with
          | .inl () => predRaw
          | .inr _ => WType.mk (.proj 1 0) Fin.elim0),
        oneAtRaw 1, zeroAtRaw 1, zeroAtRaw 1] i

/-- The inner conditional as an expression of arity one. -/
@[expose] def eqOneInner : C :=
  ⟨⟨eqOneInnerRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => cond.val.property
      | .inr 0 =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => pred.val.property
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩
      | .inr 1 => (oneAt 1).property
      | .inr 2 => (zeroAt 1).property
      | .inr 3 => (zeroAt 1).property⟩⟩

/-- `eqOneInner` at its declared arity. -/
@[expose] def eqOneInnerOf : COf 1 := ⟨eqOneInner, rfl⟩

/-- The raw tree of the one-test: the empty bitstring is not one, and
otherwise the argument is one exactly when its predecessor is empty. -/
@[expose] def eqOneRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 4) fun d ↦
    match d with
    | .inl () => condRaw
    | .inr i =>
      ![WType.mk (.proj 1 0) Fin.elim0, zeroAtRaw 1, eqOneInnerRaw, eqOneInnerRaw] i

/-- Whether a bitstring has length one, as an expression of arity one. -/
@[expose] def eqOne : C :=
  ⟨⟨eqOneRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => cond.val.property
      | .inr 0 => ⟨trivial, fun c ↦ c.elim0⟩
      | .inr 1 => (zeroAt 1).property
      | .inr 2 => eqOneInner.property
      | .inr 3 => eqOneInner.property⟩⟩

/-- `eqOne` at its declared arity, as `combOf` and `isTreeOf`. -/
@[expose] def eqOneOf : COf 1 := ⟨eqOne, rfl⟩

/-- The one-test's meaning at its arity, taken at the raw tree rather than at
`eqOne`, as `combSem`. -/
@[expose] def eqOneSem : Sem 1 :=
  semAt 1 ⟨eqOneRaw, by decide⟩ rfl

/-- The one-test at an arbitrary environment is the test at the canonical
one. -/
theorem eqOneSem_env (f : Fin 1 → List Bool) : eqOneSem f = eqOneSem ![f 0] :=
  congrArg eqOneSem (funext fun i ↦ match i with | ⟨0, _⟩ => rfl)

/-- The one-test accepts exactly the bitstrings of length one. It is not a
recursion, so its three cases are decided by matching. -/
theorem eqOneSem_eq (u : List Bool) :
    eqOneSem ![u] = if u.length = 1 then [true] else [] := by
  match u with
  | [] => rfl
  | [b] => cases b <;> rfl
  | b :: c :: v =>
    cases b <;> cases c <;>
      (change ([] : List Bool) = _
       rw [if_neg (by simp only [List.length_cons]; omega)])

/-- The raw tree of the recognizer: the one-test on the scan's predecessor. -/
@[expose] def isTreeRaw : sig.toPFunctor.W :=
  WType.mk (.comp 1 1) fun d ↦
    match d with
    | .inl () => eqOneRaw
    | .inr _ =>
      WType.mk (.comp 1 1) fun e ↦
        match e with
        | .inl () => predRaw
        | .inr _ => combRaw

/-- The recognizer: whether a bitstring is the preorder spelling of a binary
tree, as an expression of arity one. -/
@[expose] def isTree : C :=
  ⟨⟨isTreeRaw, by decide⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => eqOne.property
      | .inr _ =>
        ⟨trivial, fun e ↦ match e with
          | .inl () => pred.val.property
          | .inr _ => comb.property⟩⟩⟩

/-- `isTree` at its declared arity. -/
@[expose] def isTreeOf : COf 1 := ⟨isTree, rfl⟩

/-- The recognizer's meaning at its arity, taken at the raw tree rather than
at `isTree`, as `combSem`. -/
@[expose] def isTreeSem : Sem 1 :=
  semAt 1 ⟨isTreeRaw, by decide⟩ rfl

/-- The meaning `isTreeSem` reads at the raw tree is the meaning `isTree`
carries, as `combSem_eq_eval` for the scan: the correctness statements below
are statements about the member of `C` that `isTree_smashFree` concerns. -/
theorem isTreeSem_eq_eval : transport isTreeOf.property isTreeOf.val.eval = isTreeSem := rfl

/-- One step of the recognizer: the one-test on the scan's predecessor. The
scan's value is `[false]` on failure, whose predecessor is empty, and
otherwise the depth in unary offset by one, whose predecessor has length the
depth. -/
theorem isTreeSem_apply (w : List Bool) :
    isTreeSem ![w] = eqOneSem (fun _ ↦ (combSem ![w]).tail) := by
  change eqOneSem (fun _ ↦ predSem (fun _ ↦ combSem ![w])) = _
  generalize combSem ![w] = r
  congr 1
  funext _
  match r with
  | [] => rfl
  | b :: v => cases b <;> rfl

/-- The recognizer's value on both branches: a rejected word receives the
empty bitstring, not merely something other than `[true]`. -/
theorem isTreeSem_eq_ite (w : List Bool) :
    isTreeSem ![w] = if binRanked.Valid w then [true] else [] := by
  rw [isTreeSem_apply, eqOneSem_env, eqOneSem_eq, combSem_eq]
  by_cases h : ok w = true
  · rw [if_pos h]
    simp only [List.tail_replicate, List.length_replicate, Nat.add_sub_cancel]
    by_cases hd : depth w = 1
    · rw [if_pos hd, if_pos ((valid_iff_ok_and_depth_eq_one w).mpr ⟨h, hd⟩)]
    · rw [if_neg hd,
        if_neg fun hv ↦ hd ((valid_iff_ok_and_depth_eq_one w).mp hv).2]
  · rw [if_neg h, if_neg (by decide : ¬ ([false] : List Bool).tail.length = 1),
      if_neg fun hv ↦ h ((valid_iff_ok_and_depth_eq_one w).mp hv).1]

/-- The recognizer accepts exactly the words the two-symbol alphabet's scan
accepts. -/
theorem isTreeSem_eq_singleton_iff_valid (w : List Bool) :
    isTreeSem ![w] = [true] ↔ binRanked.Valid w := by
  rw [isTreeSem_eq_ite]
  by_cases h : binRanked.Valid w
  · rw [if_pos h]
    exact ⟨fun _ ↦ h, fun _ ↦ rfl⟩
  · rw [if_neg h]
    exact ⟨fun hw ↦ absurd hw (by nofun), fun hv ↦ absurd hv h⟩

/-- The recognizer accepts exactly the preorder spellings of the two-symbol
alphabet's terms. -/
theorem isTreeSem_eq_singleton_iff_exists_spell (w : List Bool) :
    isTreeSem ![w] = [true] ↔ ∃ t, binRanked.spell t = w :=
  (isTreeSem_eq_singleton_iff_valid w).trans (binRanked.valid_iff_exists_spell w)

/-- The recognizer lies in the smash-free subalgebra. With
[Strahm2003] Theorem 1(2)'s left-to-right inclusion, the decision of
`RankedAlphabet.Valid` at the two-symbol alphabet is computable
simultaneously in polynomial time and linear space. -/
theorem isTree_smashFree : SmashFree isTree := by decide

end

end Cobham
