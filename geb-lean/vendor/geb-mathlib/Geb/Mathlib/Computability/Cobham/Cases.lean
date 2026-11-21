/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Computability.Cobham.Basic
public import Geb.Mathlib.Computability.Cobham.Scan

/-!
# Definition by cases over Cobham's class

A combinator selecting among `2 ^ p` expressions of arity one by the low `p`
bits of a scrutinee, and applying the selected one to a second argument. It
imposes no condition on the expressions it selects among; `Cobham.cases`'s
docstring records why.

## Main definitions

* `Cobham.bits` — the bits of a scrutinee word, `false` past its end.
* `Cobham.shiftRaw`, `Cobham.shiftW` — a tree of arity two at the predecessor
  of argument zero.
* `Cobham.casesRaw`, `Cobham.casesW`, `Cobham.casesSem` — the case tree, its
  admissible form, and its meaning.
* `Cobham.cases`, `Cobham.casesOf` — the case tree as an expression of `C`, and
  at its declared arity.

## Main statements

* `Cobham.bits_succ`, `Cobham.bits_succ_tail`, `Cobham.bits_ofFn`,
  `Cobham.ofFn_bits` — peeling, dropping, and the round trip against
  `List.ofFn`. `ofFn_bits` recovers the scrutinee, truncated and zero-padded,
  from the family its bits spell.
* `Cobham.wIndexRoot_shiftRaw`, `Cobham.wValid_shiftRaw`,
  `Cobham.arity_shiftW`, `Cobham.recBounded_shiftW` — the shift's arity,
  admissibility and recursion bound.
* `Cobham.semAt_shiftW`, `Cobham.casesSem_eq`, `Cobham.casesSem_eq_eval` — the
  shift's meaning, the branch the scrutinee selects, and the identification
  with the meaning the expression carries.
* `Cobham.wIndexRoot_casesRaw`, `Cobham.arity_casesW` — the case tree's
  arity.
* `Cobham.wValid_casesRaw` — admissibility, from the branches' own.
* `Cobham.recBounded_casesW` — the recursion bound, from the branches' own
  together with those `cond` and `pred` already carry.
* `Cobham.stepWord_predIterOf`, `Cobham.stepWord_prependOf`,
  `Cobham.baseWord_prependOf`, `Cobham.baseWord_constAtOf`,
  `Cobham.stepWord_constAtOf`, `Cobham.stepWord_diagOf` — the words the
  combinators of `Cobham/Basic.lean` contribute.

## Implementation notes

The scrutinee is consumed by shifting it into the recursive subtree rather than
by scrutinising an iterated predecessor of a fixed argument. At an iterated
predecessor the scrutinee is not a variable, so no case analysis reduces the
`boundedRec` node of `cond` and the semantic theorem is unreachable; shifting
leaves the scrutinee as argument zero itself. It is also linear rather than
quadratic in the number of bits dispatched on.

`cond`'s empty branch is directed at the same subtree as its head-`false`
branch, which reads a scrutinee shorter than `p` as zero-padded and keeps
`casesSem_eq` free of a hypothesis.

`ofFn_bits` is proved by structural induction on the width. The route through
`List.ext_getElem` and `omega` depends on `Classical.choice`.

The word characterisations naming `baseWord` or `stepWord` are stated here
rather than beside the definitions they characterise, `baseWord` and
`stepWord` being declared in `Cobham/Scan.lean`, which imports
`Cobham/Basic.lean`.

## References

* [Cobham1965]

## Tags

Cobham, bounded recursion on notation, definition by cases
-/

namespace Cobham

public section

/-- The bits of a scrutinee word, indexed by `Fin p`, `false` past the word's
end. -/
@[expose] def bits (p : ℕ) (w : List Bool) : Fin p → Bool :=
  fun j ↦ w.getD j false

/-- Peeling the low bit of a scrutinee's bit family. -/
theorem bits_succ (p : ℕ) (w : List Bool) :
    bits (p + 1) w = Fin.cons (w.getD 0 false) (bits p w.tail) := by
  refine funext fun i ↦ Fin.cases ?_ (fun _ ↦ ?_) i
  · rfl
  · match w with
    | [] => rfl
    | _ :: _ => rfl

/-- Dropping the low bit of a scrutinee's family. -/
theorem bits_succ_tail (p : ℕ) (w : List Bool) :
    (fun i : Fin p ↦ bits (p + 1) w i.succ) = bits p w.tail := by
  funext i
  match w with
  | [] => rfl
  | _ :: _ => rfl

/-- The bits of a spelled-out family are the family. -/
theorem bits_ofFn {p : ℕ} (f : Fin p → Bool) : bits p (List.ofFn f) = f :=
  funext fun j ↦ by simp [bits]

/-- A spelled-out bit family is the scrutinee truncated and zero-padded. -/
theorem ofFn_bits : ∀ (p : ℕ) (w : List Bool),
    List.ofFn (bits p w) = w.take p ++ List.replicate (p - w.length) false :=
  Nat.rec (fun w ↦ by
      rw [List.ofFn_zero, List.take_zero, Nat.zero_sub, List.replicate_zero,
        List.append_nil])
    (fun p ih w ↦ by
      rw [List.ofFn_succ, bits_succ_tail, ih]
      match w with
      | [] =>
        simp only [List.tail_nil, List.take_nil, List.nil_append,
          List.length_nil, Nat.sub_zero, List.replicate_succ]
        rfl
      | _ :: _ =>
        simp only [List.take_succ_cons, List.length_cons, Nat.succ_sub_succ,
          List.cons_append]
        rfl)

/-- A tree of arity two, carried to the predecessor of argument zero: its own
argument zero becomes `pred` of the outer one, its argument one the outer
argument one. -/
@[expose] def shiftRaw (e : sig.toPFunctor.W) : sig.toPFunctor.W :=
  WType.mk (.comp 2 2) fun d ↦
    match d with
    | .inl () => e
    | .inr i =>
      ![WType.mk (.comp 2 1) (fun c ↦
          match c with
          | .inl () => predRaw
          | .inr _ => WType.mk (.proj 2 0) Fin.elim0),
        WType.mk (.proj 2 1) Fin.elim0] i

/-- A shifted tree has arity two, whatever it shifts. -/
theorem wIndexRoot_shiftRaw (e : sig.toPFunctor.W) :
    sig.wIndexRoot (shiftRaw e) = 2 := rfl

/-- A shifted tree is admissible when what it shifts is, at arity two. -/
theorem wValid_shiftRaw (e : sig.toPFunctor.W) (he : sig.WValid e)
    (ha : sig.wIndexRoot e = 2) : sig.WValid (shiftRaw e) :=
  ⟨fun d ↦ match d with
    | .inl () => he
    | .inr i =>
      match i with
      | 0 =>
        ⟨fun c ↦ match c with
          | .inl () => pred.val.val.property
          | .inr _ => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩,
        funext fun c ↦ match c with
          | .inl () =>
            (sig.wIndexValid_index_eq_wIndexRoot predRaw).trans pred.property
          | .inr _ => rfl⟩
      | 1 => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩,
  funext fun d ↦ match d with
    | .inl () => (sig.wIndexValid_index_eq_wIndexRoot e).trans ha
    | .inr i => match i with | 0 => rfl | 1 => rfl⟩

/-- A shifted tree, carrying its admissibility. -/
@[expose] def shiftW (e : sig.W) (he : arity e = 2) : sig.W :=
  ⟨shiftRaw e.val, wValid_shiftRaw e.val e.property he⟩

/-- A shifted tree's arity, in the form `fst_eval` composes with. -/
theorem arity_shiftW (e : sig.W) (he : arity e = 2) :
    arity (shiftW e he) = 2 := rfl

/-- A shifted tree reads the tail of argument zero. -/
theorem semAt_shiftW (e : sig.W) (he : arity e = 2) (sel x : List Bool) :
    semAt 2 (shiftW e he) (arity_shiftW e he) ![sel, x] =
      semAt 2 e he ![sel.tail, x] := by
  refine congrArg (semAt 2 e he) (funext fun i : Fin 2 ↦ ?_)
  match i with
  | 0 =>
    match sel with
    | [] => rfl
    | b :: _ => cases b <;> rfl
  | 1 => rfl

/-- A shifted tree's recursion bound, from what it shifts together with the
predecessor's own. -/
theorem recBounded_shiftW (e : sig.W) (he : arity e = 2) (hr : RecBounded e) :
    RecBounded (shiftW e he) :=
  ⟨trivial, fun d ↦ match d with
    | .inl () => hr
    | .inr i =>
      match i with
      | 0 => ⟨trivial, fun c ↦ match c with
          | .inl () => pred.val.property
          | .inr _ => ⟨trivial, fun c ↦ c.elim0⟩⟩
      | 1 => ⟨trivial, fun c ↦ c.elim0⟩⟩

/-- The case tree over `p` bits of argument zero, applying the selected branch
to argument one. `cond`'s empty branch points at its head-`false` branch, which
reads a short scrutinee as zero-padded; each level shifts the scrutinee, so the
branch index is read off the low bits in order. -/
@[expose] def casesRaw :
    (p : ℕ) → ((Fin p → Bool) → sig.toPFunctor.W) → sig.toPFunctor.W :=
  Nat.rec (motive := fun p ↦
      ((Fin p → Bool) → sig.toPFunctor.W) → sig.toPFunctor.W)
    (fun br ↦ liftRaw (br Fin.elim0))
    (fun _ ih br ↦
      WType.mk (.comp 2 4) fun d ↦
        match d with
        | .inl () => condRaw
        | .inr i =>
          ![WType.mk (.proj 2 0) Fin.elim0,
            shiftRaw (ih (fun t ↦ br (Fin.cons false t))),
            shiftRaw (ih (fun t ↦ br (Fin.cons true t))),
            shiftRaw (ih (fun t ↦ br (Fin.cons false t)))] i)

/-- The case tree has arity two, whatever it branches over. -/
theorem wIndexRoot_casesRaw (p : ℕ) (br : (Fin p → Bool) → sig.toPFunctor.W) :
    sig.wIndexRoot (casesRaw p br) = 2 := by
  cases p with
  | zero => exact wIndexRoot_liftRaw _
  | succ _ => rfl

/-- The case tree is admissible when every branch is, at arity one. The motive
generalizes over the branch family, the recursive calls reindexing it. -/
theorem wValid_casesRaw : ∀ (p : ℕ) (br : (Fin p → Bool) → sig.toPFunctor.W),
    (∀ v, sig.WValid (br v)) → (∀ v, sig.wIndexRoot (br v) = 1) →
    sig.WValid (casesRaw p br) :=
  Nat.rec (fun _ hv ha ↦ wValid_liftRaw _ (hv _) (ha _))
    (fun p ih _ hv ha ↦
      ⟨fun d ↦ match d with
        | .inl () => cond.val.val.property
        | .inr i =>
          match i with
          | 0 => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
          | 1 => wValid_shiftRaw _ (ih _ (fun _ ↦ hv _) (fun _ ↦ ha _))
              (wIndexRoot_casesRaw p _)
          | 2 => wValid_shiftRaw _ (ih _ (fun _ ↦ hv _) (fun _ ↦ ha _))
              (wIndexRoot_casesRaw p _)
          | 3 => wValid_shiftRaw _ (ih _ (fun _ ↦ hv _) (fun _ ↦ ha _))
              (wIndexRoot_casesRaw p _),
      funext fun d ↦ match d with
        | .inl () => (sig.wIndexValid_index_eq_wIndexRoot condRaw).trans cond.property
        | .inr i =>
          match i with
          | 0 => rfl
          | 1 => (sig.wIndexValid_index_eq_wIndexRoot _).trans
              (wIndexRoot_shiftRaw _)
          | 2 => (sig.wIndexValid_index_eq_wIndexRoot _).trans
              (wIndexRoot_shiftRaw _)
          | 3 => (sig.wIndexValid_index_eq_wIndexRoot _).trans
              (wIndexRoot_shiftRaw _)⟩)

/-- The case tree over expressions, carrying its admissibility. -/
@[expose] def casesW (p : ℕ) (br : (Fin p → Bool) → COf 1) : sig.W :=
  ⟨casesRaw p (fun v ↦ (br v).val.val.val),
    wValid_casesRaw p _ (fun v ↦ (br v).val.val.property) (fun v ↦ (br v).property)⟩

/-- The case tree's arity, in the form `fst_eval` composes with. -/
theorem arity_casesW (p : ℕ) (br : (Fin p → Bool) → COf 1) :
    arity (casesW p br) = 2 :=
  wIndexRoot_casesRaw p _

/-- The meaning of a case tree at its arity, read at the raw tree. -/
@[expose] def casesSem (p : ℕ) (br : (Fin p → Bool) → COf 1) : Sem 2 :=
  semAt 2 (casesW p br) (arity_casesW p br)

/-- A case tree applies the branch its scrutinee selects to argument one, the
scrutinee zero-padded past its end. -/
theorem casesSem_eq : ∀ (p : ℕ) (br : (Fin p → Bool) → COf 1)
    (sel x : List Bool),
    casesSem p br ![sel, x] = stepWord (br (bits p sel)) x :=
  Nat.rec
    (fun br sel x ↦ by
      have hb : bits 0 sel = Fin.elim0 := funext fun i ↦ i.elim0
      rw [hb]
      change semAt 1 (br Fin.elim0).val.val (br Fin.elim0).property (fun _ ↦ x) = _
      exact congrArg _ (funext fun i ↦ match i with | ⟨0, _⟩ => rfl))
    (fun p ih br sel x ↦ by
      rw [bits_succ]
      match sel with
      | [] =>
        have h : casesSem (p + 1) br ![[], x] =
            casesSem p (fun s ↦ br (Fin.cons false s)) ![[], x] :=
          semAt_shiftW (casesW p fun s ↦ br (Fin.cons false s))
            (arity_casesW p _) [] x
        rw [h, ih]
        rfl
      | true :: t =>
        have h : casesSem (p + 1) br ![true :: t, x] =
            casesSem p (fun s ↦ br (Fin.cons true s)) ![t, x] :=
          semAt_shiftW (casesW p fun s ↦ br (Fin.cons true s))
            (arity_casesW p _) (true :: t) x
        rw [h, ih]
        rfl
      | false :: t =>
        have h : casesSem (p + 1) br ![false :: t, x] =
            casesSem p (fun s ↦ br (Fin.cons false s)) ![t, x] :=
          semAt_shiftW (casesW p fun s ↦ br (Fin.cons false s))
            (arity_casesW p _) (false :: t) x
        rw [h, ih]
        rfl)

/-- The case tree's recursion bound, from the branches' own together with
those `cond` and `pred` already carry. -/
theorem recBounded_casesW : ∀ (p : ℕ) (br : (Fin p → Bool) → COf 1),
    RecBounded (casesW p br) :=
  Nat.rec (fun br ↦ recBounded_liftRaw (br Fin.elim0))
    (fun p ih br ↦
      ⟨trivial, fun d ↦ match d with
        | .inl () => cond.val.property
        | .inr i =>
          match i with
          | 0 => ⟨trivial, fun c ↦ c.elim0⟩
          | 1 => recBounded_shiftW _ (arity_casesW p _)
              (ih (fun t ↦ br (Fin.cons false t)))
          | 2 => recBounded_shiftW _ (arity_casesW p _)
              (ih (fun t ↦ br (Fin.cons true t)))
          | 3 => recBounded_shiftW _ (arity_casesW p _)
              (ih (fun t ↦ br (Fin.cons false t)))⟩)

/-- The case tree as an expression. Definition by cases imposes no condition on
the expressions it selects among: every node the recursion introduces is a
`comp`, whose `RecBoundedValue` is `True`, over `proj` together with the trees
underlying `cond` and `pred`, which carry their own recursion bounds already. -/
@[expose] def cases (p : ℕ) (br : (Fin p → Bool) → COf 1) : C :=
  ⟨casesW p br, recBounded_casesW p br⟩

/-- `cases` at its declared arity. -/
@[expose] def casesOf (p : ℕ) (br : (Fin p → Bool) → COf 1) : COf 2 :=
  ⟨cases p br, arity_casesW p br⟩

/-- The meaning read at the raw tree is the meaning the expression carries.
Unlike the scan combinator's counterpart this is not a `rfl`: `arity_casesW` is
a theorem rather than a definitional equality, so the transport it carries is
opaque. -/
theorem casesSem_eq_eval (p : ℕ) (br : (Fin p → Bool) → COf 1) :
    transport (casesOf p br).property (casesOf p br).val.eval = casesSem p br :=
  transport_transport (fst_eval (casesW p br)) (arity_casesW p br)
    (eval (casesW p br)).2

/-- The iterated predecessor drops `k` bits. -/
theorem stepWord_predIterOf : ∀ (k : ℕ) (u : List Bool),
    stepWord (predIterOf k) u = u.drop k :=
  Nat.rec (fun _ ↦ rfl)
    (fun j ih u ↦ by
      have hfun : (fun _ : Fin 1 ↦ stepWord (predIterOf j) u) =
          ![stepWord (predIterOf j) u] :=
        funext fun i ↦ match i with | ⟨0, _⟩ => rfl
      have h : stepWord (predIterOf (j + 1)) u =
          predSem ![stepWord (predIterOf j) u] := congrArg predSem hfun
      rw [h, predSem_eq, ih u, List.tail_drop])

/-- Prepending a word prepends it to the value a step contributes. -/
theorem stepWord_prependOf (e : COf 1) (r : List Bool) :
    ∀ u : List Bool, stepWord (prependOf u e) r = u ++ stepWord e r :=
  List.rec rfl (fun b v ih ↦ by
    change b :: stepWord (prependOf v e) r = _
    rw [ih]
    rfl)

/-- Prepending a word to a nullary expression prepends it to the value. -/
theorem baseWord_prependOf (e : COf 0) :
    ∀ u : List Bool, baseWord (prependOf u e) = u ++ baseWord e :=
  List.rec rfl (fun b v ih ↦ by
    change b :: baseWord (prependOf v e) = _
    rw [ih]
    rfl)

/-- The constant word is the base it contributes. -/
theorem baseWord_constAtOf (u : List Bool) : baseWord (constAtOf 0 u) = u :=
  (baseWord_prependOf (zeroAtOf 0) u).trans (List.append_nil u)

/-- The constant word is the value a step contributes, whatever it reads. -/
theorem stepWord_constAtOf (u r : List Bool) :
    stepWord (constAtOf 1 u) r = u :=
  (stepWord_prependOf (zeroAtOf 1) r u).trans (List.append_nil u)

/-- The diagonal reads its argument in both positions. -/
theorem stepWord_diagOf (e : COf 2) (u : List Bool) :
    stepWord (diagOf e) u = semAt 2 e.val.val e.property ![u, u] := by
  have hfun : (fun _ : Fin 2 ↦ u) = ![u, u] :=
    funext fun i ↦ match i with | 0 => rfl | 1 => rfl
  exact congrArg (semAt 2 e.val.val e.property) hfun

end

end Cobham
