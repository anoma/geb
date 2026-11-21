/-
Copyright (c) 2026 Terence Rokop. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Terence Rokop
-/
module

public import Geb.Mathlib.Computability.Cobham.Scan

/-!
# Expression combinators and the scan at a linear growth bound

`Cobham.scan` admits a state exceeding the input by an additive constant:
its bound child prepends `growth` bits to the recursion variable, so the
recursion bound reads `|state| ≤ |w| + growth`. A fold whose state carries one
`(p + 1)`-bit block per pending subterm can exceed that, the block count rising
once per `R.width` input bits. `R.width < p + 1` is necessary for it to do so,
not sufficient: an alphabet whose symbols never grow the stack keeps the state
bounded whatever the carrier. At `R.width ≥ p + 1` the additive bound always
suffices, and `Geb.CobhamFold.length_stateWordF_not_le_add` exhibits the failure
at the two-symbol alphabet, whose width is one.

This module supplies the bound child `boundMulRaw`, built over `multRaw`, whose
value is the `mult`-fold self-concatenation of the recursion variable, and the
scan combinator
`scanBRaw` parameterized by its bound child, so that `Cobham.scan`'s additive
bound and the multiplicative bound `mult * |w| + growth` are two instances of
one node. It also supplies the general expression combinators — a projection, two
compositions and a concatenation — and the scan node `scan2Raw` at steps of
arity two. Both fold constructions over this one reach `scan2Raw`, through
`scanBRaw`, and the fixed-width one uses `comp1Of` besides; the projection, the
general composition and the concatenation reach the bitstring construction
alone.

The multiplier is built from `Cobham.concatCompRaw`, whose head is the `concat`
generator. `concat` belongs to the subalgebra `Cobham.SmashFree` names, which
[Strahm2003] Theorem 1(2) contains in the functions computable simultaneously
in polynomial time and linear space, so the multiplicative bound stays inside
that subalgebra; `Geb.CobhamFold.smashFreeBool_boundMulRaw` states this at
every multiplicity and growth.
`Cobham.cond` already takes a concatenation bound in place of
[HeraudNowak2011]'s smash bound for the same reason.

## Main definitions

* `Geb.CobhamFold.projOf`, `Geb.CobhamFold.compOf`, `Geb.CobhamFold.comp1Of`,
  `Geb.CobhamFold.concatCompOf` — a projection, a composition, an arity-one
  expression applied to an expression, and a concatenation, as expressions.
* `Geb.CobhamFold.multRaw` — the `mult`-fold self-concatenation of the
  recursion variable.
* `Geb.CobhamFold.boundMulRaw` — that concatenation with `growth` bits
  prepended.
* `Geb.CobhamFold.scan2Raw` — the scan node at steps of arity two, which read
  the remaining word as well as the recursive value.
* `Geb.CobhamFold.scanBRaw`, `Geb.CobhamFold.scanBW` — that node at two steps
  lifted from arity one, which is `Cobham.scan`'s shape, and it over
  expressions.
* `Geb.CobhamFold.scanBSem` — the meaning of that node at arity one.
* `Geb.CobhamFold.scanMul`, `Geb.CobhamFold.scanMulOf` — the scan at the
  multiplicative bound, as an expression of `Cobham.C` and at its declared
  arity.

## Main statements

* `Geb.CobhamFold.wValid_concatCompRaw`, `Geb.CobhamFold.recBounded_concatCompRaw`
  — admissibility and the recursion bound of a concatenation node, from its
  two arguments'.
* `Geb.CobhamFold.length_multSem` — the multiplier's value has length
  `mult * |x 0|`, exactly.
* `Geb.CobhamFold.length_boundMulSem` — the bound child's value has length
  `growth + mult * |x 0|`.
* `Geb.CobhamFold.scanBRaw_boundRaw` — at the additive bound child the
  parameterized node is `Cobham.scanRaw`.
* `Geb.CobhamFold.boundMulRaw_ne_boundRaw` — at the multiplier one, the
  multiplicative bound child is not the additive one, at any growth.
* `Geb.CobhamFold.scanBSem_nil`, `Geb.CobhamFold.scanBSem_cons`,
  `Geb.CobhamFold.scanBSem_eq` — the scan on the empty word, on one bit, and as
  a `List.foldr`, at every bound child.
* `Geb.CobhamFold.scanMulSem_eq_eval` — the meaning read at the raw tree is the
  meaning the expression carries.

## Implementation notes

`Cobham.concatCompRaw n a b` evaluates to `b`'s list followed by `a`'s, the
`concat` generator reading its second argument as the earlier part of the word.
`multRaw`'s step therefore places the projection second, so the recursion
variable is prepended at each level; the value is a concatenation of copies of
one list, so the order is immaterial and only `length_multSem` is stated.

`scanBRaw` differs from `Cobham.scanRaw` only in taking its bound child as a
parameter rather than building it from a growth. Every statement about the
scan's value — `scanBSem_nil`, `scanBSem_cons`, `scanBSem_eq` — holds at every
bound child, `Cobham.evalValue`'s `boundedRec` clause not consulting child
three; only the recursion bound reads it.

The transports `Cobham.semAt` introduces disappear here by proof irrelevance:
each raw tree whose meaning is read here is a `WType.mk` whose shape's
`Cobham.q` reduces to `1`, so the arity equation has definitionally equal
sides.

## References

* [Cobham1965]
* [HeraudNowak2011]
* [Strahm2003]

## Tags

Cobham, bounded recursion on notation, scan, composition, concatenation, growth
bound
-/

@[expose] public section

namespace Geb.CobhamFold

open Cobham

/-- A projection as an expression. -/
def projOf (n : ℕ) (i : Fin n) : COf n :=
  ⟨⟨⟨WType.mk (.proj n i) Fin.elim0, ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩⟩,
      ⟨trivial, fun c ↦ c.elim0⟩⟩, rfl⟩

/-- An `m`-ary expression applied to `m` arguments of arity `n`. -/
def compOf {n m : ℕ} (head : COf m) (args : Fin m → COf n) : COf n :=
  ⟨⟨⟨WType.mk (.comp n m) fun d ↦
        match d with
        | .inl () => head.val.val.val
        | .inr i => (args i).val.val.val,
      ⟨fun d ↦ match d with
        | .inl () => head.val.val.property
        | .inr i => (args i).val.val.property,
      funext fun d ↦ match d with
        | .inl () => (sig.wIndexValid_index_eq_wIndexRoot _).trans head.property
        | .inr i => (sig.wIndexValid_index_eq_wIndexRoot _).trans (args i).property⟩⟩,
    ⟨trivial, fun d ↦ match d with
      | .inl () => head.val.property
      | .inr i => (args i).val.property⟩⟩, rfl⟩

/-- An arity-one expression applied to an `n`-ary one: `compOf` at one
argument. -/
def comp1Of {n : ℕ} (e : COf 1) (a : COf n) : COf n := compOf e fun _ ↦ a

/-- The concatenation of two `n`-ary expressions, the second's value first:
`compOf` at the `concat` generator. -/
def concatCompOf (n : ℕ) (a b : COf n) : COf n := compOf concatOf ![a, b]

/-- A concatenation node is admissible when both its arguments are, at the
node's own arity. Its head is the `concat` generator, whose admissibility is
vacuous. -/
theorem wValid_concatCompRaw (n : ℕ) (a b : sig.toPFunctor.W)
    (ha : sig.WValid a) (ha' : sig.wIndexRoot a = n)
    (hb : sig.WValid b) (hb' : sig.wIndexRoot b = n) :
    sig.WValid (concatCompRaw n a b) :=
  ⟨fun d ↦ match d with
    | .inl () => ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩
    | .inr i => match i with
      | 0 => ha
      | 1 => hb,
  funext fun d ↦ match d with
    | .inl () => rfl
    | .inr i => match i with
      | 0 => (sig.wIndexValid_index_eq_wIndexRoot a).trans ha'
      | 1 => (sig.wIndexValid_index_eq_wIndexRoot b).trans hb'⟩

/-- A concatenation node carries no recursion of its own: its `comp` shape's
`Cobham.RecBoundedValue` is vacuous, so the condition is its arguments'. -/
theorem recBounded_concatCompRaw (n : ℕ) (a b : sig.toPFunctor.W)
    (hva : sig.WValid a) (hvb : sig.WValid b)
    (hv : sig.WValid (concatCompRaw n a b))
    (ha : RecBounded ⟨a, hva⟩) (hb : RecBounded ⟨b, hvb⟩) :
    RecBounded ⟨concatCompRaw n a b, hv⟩ :=
  ⟨trivial, fun d ↦ match d with
    | .inl () => ⟨trivial, fun c ↦ c.elim0⟩
    | .inr i => match i with
      | 0 => ha
      | 1 => hb⟩

/-- Prepending a word to an expression prepends it to the expression's meaning,
at every arity. `Cobham.stepWord_prependOf` is this at arity one. -/
theorem semAt_prependOf {n : ℕ} (e : COf n) (x : Fin n → List Bool) :
    ∀ u : List Bool,
      semAt n (prependOf u e).val.val (prependOf u e).property x =
        u ++ semAt n e.val.val e.property x :=
  List.rec rfl fun b v ih ↦ by
    change b :: semAt n (prependOf v e).val.val (prependOf v e).property x = _
    rw [ih]
    rfl

/-- A constant word's meaning, at every arity. -/
@[simp] theorem semAt_constAtOf (n : ℕ) (u : List Bool) (x : Fin n → List Bool) :
    semAt n (constAtOf n u).val.val (constAtOf n u).property x = u :=
  (semAt_prependOf (zeroAtOf n) x u).trans (List.append_nil u)

/-- A projection's meaning is the slot it names. -/
@[simp] theorem semAt_projOf (n : ℕ) (i : Fin n) (x : Fin n → List Bool) :
    semAt n (projOf n i).val.val (projOf n i).property x = x i := rfl

/-- A concatenation's meaning is its second argument's followed by its
first's. -/
theorem semAt_concatCompOf (n : ℕ) (a b : COf n) (x : Fin n → List Bool) :
    semAt n (concatCompOf n a b).val.val (concatCompOf n a b).property x =
      semAt n b.val.val b.property x ++ semAt n a.val.val a.property x := rfl

/-- A composition's meaning at every arity. `Geb.CobhamFold.stepWord_compOf`
is this at arity one. -/
theorem semAt_compOf {n m : ℕ} (head : COf m) (args : Fin m → COf n)
    (x : Fin n → List Bool) :
    semAt n (compOf head args).val.val (compOf head args).property x =
      semAt m head.val.val head.property fun i ↦ semAt n (args i).val.val (args i).property x := rfl

/-- An arity-one expression's meaning at an `n`-ary argument.
`Geb.CobhamFold.stepWord_comp1Of` is this at arity one. -/
theorem semAt_comp1Of {n : ℕ} (e : COf 1) (a : COf n) (x : Fin n → List Bool) :
    semAt n (comp1Of e a).val.val (comp1Of e a).property x =
      stepWord e (semAt n a.val.val a.property x) :=
  congrArg (semAt 1 e.val.val e.property) (funext fun i ↦ match i with | ⟨0, _⟩ => rfl)

/-- The `mult`-fold self-concatenation of the recursion variable, of arity one:
the empty bitstring at `mult = 0`, and one more copy of the sole argument at
each successor. -/
def multRaw : ℕ → sig.toPFunctor.W :=
  Nat.rec (zeroAtRaw 1)
    fun _ ih ↦ concatCompRaw 1 ih (WType.mk (.proj 1 0) Fin.elim0)

/-- The multiplier has arity one, at every multiplicity. A case split, not a
recursion: both `Nat.rec` branches are `comp` nodes of arity one. -/
theorem wIndexRoot_multRaw (mult : ℕ) : sig.wIndexRoot (multRaw mult) = 1 := by
  cases mult with
  | zero => rfl
  | succ _ => rfl

/-- The multiplier is admissible, at every multiplicity. -/
theorem wValid_multRaw (mult : ℕ) : sig.WValid (multRaw mult) :=
  Nat.rec (zeroAt 1).val.property
    (fun k ih ↦ wValid_concatCompRaw 1 _ _ ih (wIndexRoot_multRaw k)
      ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩ rfl)
    mult

/-- The multiplier's arity, in the form `Cobham.fst_eval` composes with. -/
theorem arity_multRaw (mult : ℕ) :
    arity ⟨multRaw mult, wValid_multRaw mult⟩ = 1 := wIndexRoot_multRaw mult

/-- The multiplier carries no recursion of its own: every node is a `comp`, a
`proj`, or the `concat` or `zero` generator. -/
theorem recBounded_multRaw (mult : ℕ) :
    RecBounded ⟨multRaw mult, wValid_multRaw mult⟩ :=
  Nat.rec (zeroAt 1).property
    (fun k ih ↦ recBounded_concatCompRaw 1 (multRaw k)
      (WType.mk (.proj 1 0) Fin.elim0) (wValid_multRaw k)
      ⟨fun c ↦ c.elim0, funext fun c ↦ c.elim0⟩ (wValid_multRaw (k + 1)) ih
      ⟨trivial, fun c ↦ c.elim0⟩)
    mult

/-- The meaning of the multiplier at its arity. -/
def multSem (mult : ℕ) : Sem 1 :=
  semAt 1 ⟨multRaw mult, wValid_multRaw mult⟩ (arity_multRaw mult)

/-- The multiplier's value has length exactly `mult` times the argument's.
Stated at an arbitrary environment, which is the form the recursion bound
reads it at. -/
theorem length_multSem : ∀ (mult : ℕ) (x : Fin 1 → List Bool),
    (multSem mult x).length = mult * (x 0).length :=
  Nat.rec (fun x ↦ (Nat.zero_mul (x 0).length).symm)
    (fun k ih x ↦ by
      change (x 0 ++ multSem k x).length = _
      rw [List.length_append, ih x, Nat.succ_mul, Nat.add_comm])

/-- The multiplier with `growth` bits prepended: the bound child of a scan
whose state may exceed the input by a factor as well as a constant.
`Cobham.prependRaw` supplies the prepending, so the three obligations below are
its own. -/
def boundMulRaw (mult growth : ℕ) : sig.toPFunctor.W :=
  prependRaw 1 (List.replicate growth true) (multRaw mult)

/-- The bound child has arity one, at every multiplicity and growth. -/
theorem wIndexRoot_boundMulRaw (mult growth : ℕ) :
    sig.wIndexRoot (boundMulRaw mult growth) = 1 :=
  wIndexRoot_prependRaw 1 _ _ (wIndexRoot_multRaw mult)

/-- The bound child is admissible, at every multiplicity and growth. -/
theorem wValid_boundMulRaw (mult growth : ℕ) :
    sig.WValid (boundMulRaw mult growth) :=
  wValid_prependRaw 1 _ (wValid_multRaw mult) (wIndexRoot_multRaw mult) _

/-- The bound child's arity, in the form `Cobham.fst_eval` composes with. -/
theorem arity_boundMulRaw (mult growth : ℕ) :
    arity ⟨boundMulRaw mult growth, wValid_boundMulRaw mult growth⟩ = 1 :=
  wIndexRoot_boundMulRaw mult growth

/-- The bound child carries no recursion of its own, at every multiplicity and
growth. -/
theorem recBounded_boundMulRaw (mult growth : ℕ) :
    RecBounded ⟨boundMulRaw mult growth, wValid_boundMulRaw mult growth⟩ :=
  recBounded_prependRaw 1 _ (wValid_multRaw mult) (wIndexRoot_multRaw mult)
    (recBounded_multRaw mult) _

/-- The meaning of the bound child at its arity. -/
def boundMulSem (mult growth : ℕ) : Sem 1 :=
  semAt 1 ⟨boundMulRaw mult growth, wValid_boundMulRaw mult growth⟩
    (arity_boundMulRaw mult growth)

/-- The bound child's value has length `growth + mult * |x 0|`. -/
theorem length_boundMulSem : ∀ (mult growth : ℕ) (x : Fin 1 → List Bool),
    (boundMulSem mult growth x).length = growth + mult * (x 0).length :=
  fun mult ↦ Nat.rec (fun x ↦ (length_multSem mult x).trans (Nat.zero_add _).symm)
    (fun g ih x ↦ by
      change (true :: boundMulSem mult g x).length = _
      rw [List.length_cons, ih x]
      omega)

/-- The scan node at steps of arity two, which read the remaining word in slot
zero as well as the recursive value in slot one. -/
def scan2Raw (base step₀ step₁ bnd : sig.toPFunctor.W) : sig.toPFunctor.W :=
  WType.mk (.boundedRec 0) ![base, step₀, step₁, bnd]

/-- The arity-two scan node is admissible from its children's. -/
theorem wValid_scan2Raw (base step₀ step₁ bnd : sig.toPFunctor.W)
    (hb : sig.WValid base) (hb' : sig.wIndexRoot base = 0)
    (h₀ : sig.WValid step₀) (h₀' : sig.wIndexRoot step₀ = 2)
    (h₁ : sig.WValid step₁) (h₁' : sig.wIndexRoot step₁ = 2)
    (hn : sig.WValid bnd) (hn' : sig.wIndexRoot bnd = 1) :
    sig.WValid (scan2Raw base step₀ step₁ bnd) :=
  ⟨fun d : Fin 4 ↦ match d with
    | 0 => hb
    | 1 => h₀
    | 2 => h₁
    | 3 => hn,
  funext fun d : Fin 4 ↦ match d with
    | 0 => (sig.wIndexValid_index_eq_wIndexRoot base).trans hb'
    | 1 => (sig.wIndexValid_index_eq_wIndexRoot step₀).trans h₀'
    | 2 => (sig.wIndexValid_index_eq_wIndexRoot step₁).trans h₁'
    | 3 => (sig.wIndexValid_index_eq_wIndexRoot bnd).trans hn'⟩

/-- The scan node at an arbitrary bound child: `scan2Raw` at two steps lifted
from arity one, which is the shape `Cobham.scan` takes. -/
def scanBRaw (base step₀ step₁ bnd : sig.toPFunctor.W) :
    sig.toPFunctor.W :=
  scan2Raw base (liftRaw step₀) (liftRaw step₁) bnd

/-- `Cobham.scan`'s additive bound and the multiplicative bound are two
instances of one node: at `Cobham.boundRaw` the parameterized node is
`Cobham.scanRaw` itself, definitionally. -/
theorem scanBRaw_boundRaw (base step₀ step₁ : sig.toPFunctor.W) (growth : ℕ) :
    scanBRaw base step₀ step₁ (boundRaw growth) =
      scanRaw base step₀ step₁ growth := rfl

/-- The multiplicative bound child is not the additive one at any growth, so an
expression built on it is a different raw tree from the corresponding
`Cobham.scan` even at the multiplier one. At growth zero the two are nodes of
different shape; each successor wraps both in the same `comp` node, so the
recursion carries the separation up. -/
theorem boundMulRaw_ne_boundRaw :
    ∀ growth : ℕ, boundMulRaw 1 growth ≠ boundRaw growth :=
  Nat.rec
    (fun h ↦ by
      injection h with ha _
      exact absurd ha (by nofun))
    fun _ ih h ↦ by
      injection h with _ hf
      exact ih (congrFun hf (Sum.inr 0))

/-- The scan node is admissible when its base is, at arity zero, its two steps
are, at arity one, and its bound child is, at arity one: `wValid_scan2Raw` at
the lifted steps. -/
theorem wValid_scanBRaw (base step₀ step₁ bnd : sig.toPFunctor.W)
    (hb : sig.WValid base) (hb' : sig.wIndexRoot base = 0)
    (h₀ : sig.WValid step₀) (h₀' : sig.wIndexRoot step₀ = 1)
    (h₁ : sig.WValid step₁) (h₁' : sig.wIndexRoot step₁ = 1)
    (hn : sig.WValid bnd) (hn' : sig.wIndexRoot bnd = 1) :
    sig.WValid (scanBRaw base step₀ step₁ bnd) :=
  wValid_scan2Raw base (liftRaw step₀) (liftRaw step₁) bnd hb hb'
    (wValid_liftRaw step₀ h₀ h₀') (wIndexRoot_liftRaw step₀)
    (wValid_liftRaw step₁ h₁ h₁') (wIndexRoot_liftRaw step₁) hn hn'

/-- The scan node over expressions, carrying its admissibility. -/
def scanBW (base : COf 0) (step₀ step₁ : COf 1)
    (bnd : sig.toPFunctor.W) (hn : sig.WValid bnd)
    (hn' : sig.wIndexRoot bnd = 1) : sig.W :=
  ⟨scanBRaw base.val.val.val step₀.val.val.val step₁.val.val.val bnd,
    wValid_scanBRaw _ _ _ bnd base.val.val.property base.property step₀.val.val.property
      step₀.property step₁.val.val.property step₁.property hn hn'⟩

/-- The scan node's arity, in the form `Cobham.fst_eval` composes with. -/
theorem arity_scanBW (base : COf 0) (step₀ step₁ : COf 1)
    (bnd : sig.toPFunctor.W) (hn : sig.WValid bnd)
    (hn' : sig.wIndexRoot bnd = 1) :
    arity (scanBW base step₀ step₁ bnd hn hn') = 1 := rfl

/-- The meaning of a scan at its arity, read at the raw tree. -/
def scanBSem (base : COf 0) (step₀ step₁ : COf 1)
    (bnd : sig.toPFunctor.W) (hn : sig.WValid bnd)
    (hn' : sig.wIndexRoot bnd = 1) : Sem 1 :=
  semAt 1 (scanBW base step₀ step₁ bnd hn hn')
    (arity_scanBW base step₀ step₁ bnd hn hn')

/-- The scan's value on the empty bitstring is the base's word, at every bound
child. -/
theorem scanBSem_nil (base : COf 0) (step₀ step₁ : COf 1)
    (bnd : sig.toPFunctor.W) (hn : sig.WValid bnd)
    (hn' : sig.wIndexRoot bnd = 1) :
    scanBSem base step₀ step₁ bnd hn hn' ![[]] = baseWord base := rfl

/-- One step of the scan: the bit selects the step, which reads the value the
scan of the rest of the word returns. -/
theorem scanBSem_cons (base : COf 0) (step₀ step₁ : COf 1)
    (bnd : sig.toPFunctor.W) (hn : sig.WValid bnd)
    (hn' : sig.wIndexRoot bnd = 1) (b : Bool) (w : List Bool) :
    scanBSem base step₀ step₁ bnd hn hn' ![b :: w] =
      scanStepWord step₀ step₁ b (scanBSem base step₀ step₁ bnd hn hn' ![w]) := by
  have hfun : ∀ r : List Bool, (fun _ : Fin 1 ↦ r) = ![r] :=
    fun r ↦ funext fun i ↦ match i with | ⟨0, _⟩ => rfl
  cases b
  · change transport ((fst_eval step₀.val.val).trans step₀.property) (eval step₀.val.val).2
      (fun _ ↦ scanBSem base step₀ step₁ bnd hn hn' ![w]) = _
    exact congrArg _ (hfun _)
  · change transport ((fst_eval step₁.val.val).trans step₁.property) (eval step₁.val.val).2
      (fun _ ↦ scanBSem base step₀ step₁ bnd hn hn' ![w]) = _
    exact congrArg _ (hfun _)

/-- A scanner computes the right fold of its steps over the word, from its
base. It holds at every bound child, `Cobham.evalValue`'s `boundedRec` clause
not consulting child three. -/
theorem scanBSem_eq (base : COf 0) (step₀ step₁ : COf 1)
    (bnd : sig.toPFunctor.W) (hn : sig.WValid bnd)
    (hn' : sig.wIndexRoot bnd = 1) (w : List Bool) :
    scanBSem base step₀ step₁ bnd hn hn' ![w] =
      w.foldr (scanStepWord step₀ step₁) (baseWord base) :=
  List.rec (scanBSem_nil base step₀ step₁ bnd hn hn')
    (fun b v ih ↦ (scanBSem_cons base step₀ step₁ bnd hn hn' b v).trans
      (congrArg (scanStepWord step₀ step₁ b) ih)) w

/-- The scanner at the multiplicative bound, as an expression of `Cobham.C`.
The bound hypothesis is `mult * |w| + growth` where `Cobham.scan` asks for
`|w| + growth`. -/
def scanMul (base : COf 0) (step₀ step₁ : COf 1) (mult growth : ℕ)
    (hbound : ∀ w : List Bool,
      (scanBSem base step₀ step₁ (boundMulRaw mult growth)
        (wValid_boundMulRaw mult growth) (wIndexRoot_boundMulRaw mult growth)
        ![w]).length ≤ mult * w.length + growth) : C :=
  ⟨scanBW base step₀ step₁ (boundMulRaw mult growth)
      (wValid_boundMulRaw mult growth) (wIndexRoot_boundMulRaw mult growth), by
    refine ⟨fun x ↦ ?_, ?_⟩
    · rw [(funext fun i ↦ i.elim0 : Fin.tail x = Fin.tail ![x 0])]
      change _ ≤ (boundMulSem mult growth x).length
      rw [length_boundMulSem]
      exact Nat.le_trans (hbound (x 0)) (Nat.le_of_eq (Nat.add_comm _ _))
    · refine fun b : Fin 4 ↦ ?_
      match b with
      | 0 => exact base.val.property
      | 1 => exact recBounded_liftRaw step₀
      | 2 => exact recBounded_liftRaw step₁
      | 3 => exact recBounded_boundMulRaw mult growth⟩

/-- `scanMul` at its declared arity. -/
def scanMulOf (base : COf 0) (step₀ step₁ : COf 1) (mult growth : ℕ)
    (hbound : ∀ w : List Bool,
      (scanBSem base step₀ step₁ (boundMulRaw mult growth)
        (wValid_boundMulRaw mult growth) (wIndexRoot_boundMulRaw mult growth)
        ![w]).length ≤ mult * w.length + growth) : COf 1 :=
  ⟨scanMul base step₀ step₁ mult growth hbound, rfl⟩

/-- The meaning read at the raw tree is the meaning the expression carries. -/
theorem scanMulSem_eq_eval (base : COf 0) (step₀ step₁ : COf 1)
    (mult growth : ℕ)
    (hbound : ∀ w : List Bool,
      (scanBSem base step₀ step₁ (boundMulRaw mult growth)
        (wValid_boundMulRaw mult growth) (wIndexRoot_boundMulRaw mult growth)
        ![w]).length ≤ mult * w.length + growth) :
    transport (scanMulOf base step₀ step₁ mult growth hbound).property
        (scanMulOf base step₀ step₁ mult growth hbound).val.eval =
      scanBSem base step₀ step₁ (boundMulRaw mult growth)
        (wValid_boundMulRaw mult growth)
        (wIndexRoot_boundMulRaw mult growth) := rfl

end Geb.CobhamFold

end
