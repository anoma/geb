import GebLean
import GebLean.Ramified.Polynomial.FirstOrder
import GebLeanTests.Ramified.Polynomial.FirstOrder
import GebLeanTests.Ramified.Polynomial.Ident

/-!
# Primed section 2.4(2) examples: addition and multiplication

Addition and multiplication as primed schema identifiers over the `1 + X`
word algebra `natAlgSig` (`GebLeanTests.Ramified.Polynomial.IdentTest.A`),
with their first-order formation proofs. Multiplication's successor step
invokes addition through a hole, so it is an `RIdent'.defn` with a non-empty
`children` family, and its formation proof discharges the child conjunct of
`RIdent'.firstOrder_defn` at a genuine child. The identifiers of
`GebLeanTests/Ramified/Polynomial/FirstOrder.lean` are hole-free, leaving
that conjunct vacuous there.

Only the syntactic layer is built here. First-order formation is a condition
on an identifier's tree shape, so it needs none of the interpretation lemmas
that the legacy ladder carries (`GebLean/Ramified/Examples.lean`).

## Main definitions

* `tmSucc'` — the unary-constructor term over a definition signature.
* `addZeroStep'`, `addSuccStep'`, `ramAdd'` — addition `o, Ω o → o` as a
  ramified monotonic recurrence on the second argument with the first as
  parameter.
* `mulHoleIdx'`, `mulZeroStep'`, `mulSuccStep'`, `ramMul'` — multiplication
  `Ω o, Ω o → o`, its successor step adding the parameter to the recursive
  result through a hole at `ramAdd'`.

## Main statements

* `ramAdd_fo`, `ramMul_fo` — both identifiers are first-order.
* `mulSuccStep_fo` — the step whose formation proof discharges the child
  conjunct of `RIdent'.firstOrder_defn` at `ramAdd_fo`.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher
type recurrence and elementary complexity", Annals of Pure and Applied Logic
96 (1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. Addition and
multiplication are section 2.4(2).

## Tags

ramified recurrence, example, addition, multiplication, first-order
-/

namespace GebLeanTests.Ramified.Polynomial.ExamplesTest

open GebLean.Ramified GebLean.Ramified.Polynomial
open GebLeanTests.Ramified.Polynomial.IdentTest (A tmZero')
open GebLeanTests.Ramified.Polynomial.FirstOrderTest (isTower_o)

/-- The unary-constructor term over a definition signature. -/
def tmSucc' {n : Nat} {h : Fin n → List RType' × RType'} {Γ' : List RType'}
    (t : Tm' (defnSig' A n h) Γ' RType'.o) :
    Tm' (defnSig' A n h) Γ' RType'.o :=
  Tm'.op (sig := defnSig' A n h) (Sum.inl (Sum.inl (Sum.inl (oObj', true))))
    (Fin.cons t finZeroElim)

/-- The sort `Ω o` carrying the recurrence argument is a tower sort. -/
theorem isTower_omega_o : RType'.IsTower (RType'.omega RType'.o) := by
  rw [rTypeSliceEquiv_isTower, rTypeSliceEquiv_omega, rTypeSliceEquiv_o]
  decide

/-- Addition's step at the nullary constructor: return the parameter. -/
def addZeroStep' : RIdent' A [RType'.o] RType'.o :=
  RIdent'.defn ⟨0, finZeroElim, Tm'.var 0⟩ finZeroElim

/-- Addition's step at the unary constructor: the successor of the recursive
result. -/
def addSuccStep' : RIdent' A [RType'.o, RType'.o] RType'.o :=
  RIdent'.defn ⟨0, finZeroElim, tmSucc' (Tm'.var 1)⟩ finZeroElim

/-- Addition's step functions: the parameter at the nullary constructor, its
successor at the unary constructor. -/
def ramAddSteps' : (i : Bool) →
    RIdent' A ([RType'.o] ++ List.replicate (A.ar i) RType'.o) RType'.o
  | false => addZeroStep'
  | true => addSuccStep'

/-- Addition `+ : o, Ω o → o`, as a ramified monotonic recurrence on the
second argument with the first as parameter: `a + 0 = a` and
`a + (n + 1) = (a + n) + 1`. -/
def ramAdd' : RIdent' A [RType'.o, RType'.omega RType'.o] RType'.o :=
  RIdent'.mrec [RType'.o] RType'.o ramAddSteps'

/-- The context and result sort of the addition identifier that
multiplication's step invokes. -/
def mulHoleIdx' : Fin 1 → List RType' × RType' :=
  Function.const _ ([RType'.o, RType'.omega RType'.o], RType'.o)

/-- Multiplication's step at the nullary constructor: return `0`. -/
def mulZeroStep' : RIdent' A [RType'.omega RType'.o] RType'.o :=
  RIdent'.defn ⟨0, finZeroElim, tmZero'⟩ finZeroElim

/-- Multiplication's step at the unary constructor: add the parameter to the
recursive result, invoking `ramAdd'` through a hole. -/
def mulSuccStep' : RIdent' A [RType'.omega RType'.o, RType'.o] RType'.o :=
  RIdent'.defn ⟨1, mulHoleIdx',
    Tm'.op (sig := defnSig' A 1 mulHoleIdx') (Sum.inl (Sum.inr ⟨0, by decide⟩))
      (Fin.cons (Tm'.var 1) (Fin.cons (Tm'.var 0) finZeroElim))⟩
    (fun _ => ramAdd')

/-- Multiplication's step functions: `0` at the nullary constructor, the
parameter added to the recursive result at the unary constructor. -/
def mulSteps' : (i : Bool) →
    RIdent' A ([RType'.omega RType'.o] ++ List.replicate (A.ar i) RType'.o) RType'.o
  | false => mulZeroStep'
  | true => mulSuccStep'

/-- Multiplication `× : Ω o, Ω o → o`, as a ramified monotonic recurrence on
the second argument with the first as parameter: `x * 0 = 0` and
`x * (n + 1) = x * n + x`, the inner addition supplied by `ramAdd'`. -/
def ramMul' : RIdent' A [RType'.omega RType'.o, RType'.omega RType'.o] RType'.o :=
  RIdent'.mrec [RType'.omega RType'.o] RType'.o mulSteps'

/-- Addition's nullary step is first-order: context `[o]`, result `o`, and a
variable body at `o`. -/
theorem addZeroStep_fo : addZeroStep'.FirstOrder :=
  ⟨fun i => Fin.cases isTower_o (fun j => j.elim0) i, isTower_o, isTower_o,
    fun j => j.elim0⟩

/-- Addition's unary step is first-order: context `[o, o]`, result `o`, and a
constructor body whose argument is a variable at `o`. -/
theorem addSuccStep_fo : addSuccStep'.FirstOrder :=
  ⟨fun i => Fin.cases isTower_o (fun j => Fin.cases isTower_o (fun k => k.elim0) j) i,
    isTower_o, ⟨isTower_o, fun e => Fin.cases isTower_o (fun j => j.elim0) e⟩,
    fun j => j.elim0⟩

/-- Addition is first-order: its context `[o, Ω o]` and result `o` are tower
sorts, and both steps are first-order. The `mrec'` former carries no
shape-level condition, so the third component is `trivial`. -/
theorem ramAdd_fo : ramAdd'.FirstOrder := by
  refine ⟨fun i => Fin.cases isTower_o (fun j => Fin.cases isTower_omega_o
    (fun k => k.elim0) j) i, isTower_o, trivial, fun i => ?_⟩
  cases i with
  | false => exact addZeroStep_fo
  | true => exact addSuccStep_fo

/-- Multiplication's nullary step is first-order: context `[Ω o]`, result
`o`, and a constructor body at `o` with no arguments. -/
theorem mulZeroStep_fo : mulZeroStep'.FirstOrder :=
  ⟨fun i => Fin.cases isTower_omega_o (fun j => j.elim0) i, isTower_o,
    ⟨isTower_o, fun e => e.elim0⟩, fun j => j.elim0⟩

/-- Multiplication's unary step is first-order. Its body is a hole
application, so the fourth conjunct of `RIdent'.firstOrder_defn` is
discharged at the genuine child `ramAdd'` rather than vacuously. -/
theorem mulSuccStep_fo : mulSuccStep'.FirstOrder :=
  ⟨fun i => Fin.cases isTower_omega_o (fun j => Fin.cases isTower_o
      (fun k => k.elim0) j) i,
    isTower_o,
    ⟨isTower_o, fun e => Fin.cases isTower_o
      (fun j => Fin.cases isTower_omega_o (fun k => k.elim0) j) e⟩,
    fun _ => ramAdd_fo⟩

/-- Multiplication is first-order: its context `[Ω o, Ω o]` and result `o`
are tower sorts, and both steps are first-order. -/
theorem ramMul_fo : ramMul'.FirstOrder := by
  refine ⟨fun i => Fin.cases isTower_omega_o (fun j => Fin.cases isTower_omega_o
    (fun k => k.elim0) j) i, isTower_o, trivial, fun i => ?_⟩
  cases i with
  | false => exact mulZeroStep_fo
  | true => exact mulSuccStep_fo

end GebLeanTests.Ramified.Polynomial.ExamplesTest
