import GebLean.Ramified.Definability.Simultaneous

/-!
# The destructor/case presentation and its flat realization

The destructor/case operations of Leivant III (section 2.5's `RRec_o` layer):
the destructors `dstr_j : o → o` reading a subterm of the recurrence argument
and, at each object sort `θ`, the case operation `case^θ : o, θ^k → θ`
branching on the main constructor. `dstrCaseSig` packages them as a
`SortedSig` summand generic in a free-algebra signature `A`; `dstrCaseModel`
gives the standard semantics of section 4.1 (a destructor returns the `j`-th
subterm, or the whole argument when `j` reaches the arity; the case operation
selects the branch of the argument's top constructor); and `dstrCaseToFlat`
realizes each operation over the `1 + X` word algebra `natAlgSig` as a derived
identifier of the higher-order system (`GebLean/Ramified/HigherOrder.lean`),
witnessing the containment direction `RRec_o ⊆ RRec` of Lemma 1 by flat
recurrence (`ramDstr` and `ramCase` of
`GebLean/Ramified/Definability/Simultaneous.lean`), with `dstrCaseToFlat_interp`
proving the two agree.

## Main definitions

* `AlgSig.numCtors`, `AlgSig.maxArity` — the constructor count and the largest
  arity of a finite free-algebra signature.
* `dstrCaseSig` — the destructor/case summand over `A`: destructors indexed by
  `Fin A.maxArity` and case operations indexed by the object sorts.
* `dstrCaseModel` — the standard semantics over `natAlgSig` (section 4.1).
* `dstrCaseToFlat` — the realization of each operation as a derived identifier
  of `higherOrder natAlgSig` (Lemma 1, containment direction).

## Main statements

* `dstrCaseToFlat_interp` — the realization agrees with the standard semantics:
  `(dstrCaseToFlat op).interp = dstrCaseModel op`.

## Implementation notes

The destructor count `A.maxArity` and constructor count `A.numCtors` are the
finite quantities `Finset.univ.sup A.ar` and `Fintype.card A.B`, so `dstrCaseSig`
carries a `Fintype A.B` instance; over `natAlgSig` they reduce to `1` and `2`,
leaving the single predecessor destructor `dstr_0` and the binary case
operation `case^θ : o, θ, θ → θ`. The case operation's argument order places the
recurrence argument first (`o :: θ^k`, faithful to `case^θ : o, θ^k → θ`),
while the flat recurrence `ramCase` places it last (`θ^k ++ [o]`, the eq. (5)
convention); `dstrCaseFlatCase` bridges the two by an explicit definition
applying `ramCase θ` to the reordered variables. The standard semantics is
expressed by the carrier-level operations `dstrRead` and `caseSelect`, each a
`FreeAlg.recurse` reading the top constructor; the model routes through the
concrete-context helpers `dstrCaseModelDstr` and `dstrCaseModelCase` so that
the argument environment is read at the literal context.

`dstrCaseSig` is generic in `A`; `dstrCaseModel` and `dstrCaseToFlat` are
`natAlgSig`-scoped. The signature packaging is novel; the destructor/case
operations transcribe Leivant III section 2.5, their semantics section 4.1, and
their flat definability the containment direction of Lemma 1.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The destructor and case
operations of the object-sorted recurrence class `RRec_o` are section 2.5 (the
destructors of type `o → o`; the case operation `case^θ : o, θ^k → θ` with `k`
the number of constructors); their reduction rules — a destructor returns the
`j`-th subterm, or the argument itself when `j` reaches the arity — are section
4.1; the containment `RRec_o ⊆ RRec` (the case and destructor functions are
definable by flat recurrence) is the trivial direction of Lemma 1.

## Tags

ramified recurrence, destructor, case, flat recurrence, definability, object
sort
-/

namespace GebLean.Ramified

/-- The standard `Fintype` structure on the constructor labels of the `1 + X`
word algebra `natAlgSig`, its labels being `Bool`. Supplies the finite counts
`natAlgSig.numCtors` and `natAlgSig.maxArity`. -/
instance instFintypeNatAlgSigB : Fintype natAlgSig.B := (inferInstance : Fintype Bool)

/-- The number of constructor labels of a finite free-algebra signature: the
cardinality of `A.B`. The count `k` of case branches of `case^θ`
(Leivant III section 2.5). -/
def AlgSig.numCtors (A : AlgSig) [Fintype A.B] : Nat := Fintype.card A.B

/-- The largest arity of a finite free-algebra signature: the supremum of the
constructor arities. The destructor family `dstr_j : o → o` runs over
`j < A.maxArity` (Leivant III section 2.5). -/
def AlgSig.maxArity (A : AlgSig) [Fintype A.B] : Nat := Finset.univ.sup A.ar

/-- Leivant III section 2.5's destructor/case operations, as a `SortedSig`
summand generic in a finite free-algebra signature `A`: the destructors
`dstr_j : o → o` indexed by `Fin A.maxArity`, and, at each object sort `θ`
(a sort satisfying `IsObj`), a case operation `case^θ : o, θ^k → θ` with `k`
the number of constructors `A.numCtors`, its arity placing the recurrence
argument at `o` first and the `k` branches at `θ` after. Novel packaging. -/
def dstrCaseSig (A : AlgSig) [Fintype A.B] (IsObj : RType → Prop) : SortedSig RType where
  Op := Fin A.maxArity ⊕ { θ : RType // IsObj θ }
  arity := Sum.elim (fun _ => [RType.o])
    (fun θ => RType.o :: List.replicate A.numCtors θ.val)
  result := Sum.elim (fun _ => RType.o) (fun θ => θ.val)

/-- The single hole of the case realization: the case function `ramCase θ` at
its own context `[θ, θ, o]` (branches first, recurrence argument last). -/
def caseHoleIdx (θ : RType) : Fin 1 → List RType × RType :=
  Function.const _ ([θ, θ, RType.o], θ)

/-- The realization of `case^θ : o, θ, θ → θ` over `natAlgSig` as a derived
identifier (Leivant III Lemma 1, containment direction): the explicit
definition at context `[o, θ, θ]` whose body applies the case function
`ramCase θ` (hole `0`, at context `[θ, θ, o]`) to the two branch variables and
then the recurrence-argument variable, reordering the recurrence argument from
first to last. Novel packaging. -/
def dstrCaseFlatCase (θ : RType) : RIdent natAlgSig [RType.o, θ, θ] θ :=
  RIdent.defn ⟨1, caseHoleIdx θ,
    Tm.op (sig := defnSig natAlgSig 1 (caseHoleIdx θ)) (Sum.inl (Sum.inr (0 : Fin 1)))
      (Fin.cons (Tm.var 1) (Fin.cons (Tm.var 2) (Fin.cons (Tm.var 0) finZeroElim)))⟩
    (fun _ => ramCase θ)

/-- Leivant III Lemma 1's containment direction `RRec_o ⊆ RRec`: each
`dstrCaseSig natAlgSig` operation realized as a derived identifier of
`higherOrder natAlgSig` by flat recurrence. Over `natAlgSig` the destructor
family is the single predecessor `ramDstr` (the arities are `≤ 1`); the case
operation `case^θ` is `dstrCaseFlatCase θ`, the reorder wrapper around the case
function `ramCase θ`. Novel packaging. -/
def dstrCaseToFlat (op : (dstrCaseSig natAlgSig RType.IsObj).Op) :
    RIdent natAlgSig ((dstrCaseSig natAlgSig RType.IsObj).arity op)
      ((dstrCaseSig natAlgSig RType.IsObj).result op) :=
  match op with
  | Sum.inl _j => ramDstr
  | Sum.inr θ => dstrCaseFlatCase θ.val

/-- The case operation's carrier-level semantics (Leivant III section 4.1): on
a recurrence argument `z` and two branches `y₀`, `y₁` it returns the branch of
`z`'s top constructor, `y₀` at the nullary constructor and `y₁` at the unary
constructor. Realized by `FreeAlg.recurse` reading the top label. -/
def caseSelect {C : Type} (z : FreeAlg natAlgSig) (y0 y1 : C) : C :=
  FreeAlg.recurse (A := natAlgSig) (P := Unit) (fun b _ _ _ => cond b y1 y0) () z

/-- The destructor's carrier-level semantics (Leivant III section 4.1): on a
recurrence argument `z` the destructor `dstr_j` returns the `j`-th subterm of
`z`'s top constructor when `j` is below its arity, and the argument `z` itself
otherwise. Realized by `FreeAlg.recurse` reading the top constructor's
subterms. -/
def dstrRead (j : Nat) (z : FreeAlg natAlgSig) : FreeAlg natAlgSig :=
  FreeAlg.recurse (A := natAlgSig) (P := Unit)
    (fun b _ sub _rec => if h : j < natAlgSig.ar b then sub ⟨j, h⟩ else FreeAlg.mk b sub) () z

/-- The case operation's standard semantics at the concrete context `[o, θ, θ]`:
`caseSelect` on the recurrence argument (position `0`) and the two branches
(positions `1`, `2`). -/
def dstrCaseModelCase (θ : RType)
    (args : ∀ i : Fin ([RType.o, θ, θ] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.o, θ, θ] : Ctx RType).get i)) :
    RType.interp (FreeAlg natAlgSig) θ :=
  caseSelect (args 0) (args 1) (args 2)

/-- The destructor's standard semantics at the concrete context `[o]`:
`dstrRead j` on the sole recurrence argument. -/
def dstrCaseModelDstr (j : Nat)
    (args : ∀ i : Fin ([RType.o] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.o] : Ctx RType).get i)) :
    RType.interp (FreeAlg natAlgSig) RType.o :=
  dstrRead j (args 0)

/-- Leivant III section 4.1's standard semantics of the destructor/case
operations over `natAlgSig`: a destructor `dstr_j` reads the `j`-th subterm of
the recurrence argument (the argument itself when `j` reaches the arity), and
the case operation `case^θ` selects the branch of the argument's main
constructor. Novel packaging. -/
def dstrCaseModel (op : (dstrCaseSig natAlgSig RType.IsObj).Op)
    (args : ∀ i : Fin ((dstrCaseSig natAlgSig RType.IsObj).arity op).length,
      RType.interp (FreeAlg natAlgSig) (((dstrCaseSig natAlgSig RType.IsObj).arity op).get i)) :
    RType.interp (FreeAlg natAlgSig) ((dstrCaseSig natAlgSig RType.IsObj).result op) :=
  match op, args with
  | Sum.inl j, args => dstrCaseModelDstr j.val args
  | Sum.inr θ, args => dstrCaseModelCase θ.val args

/-- The case semantics agrees with the case function on the reordered
environment: `caseSelect z y₀ y₁` is the denotation of `ramCase θ` on the
environment `(y₀, y₁, z)`. -/
theorem caseSelect_eq (θ : RType) (z : FreeAlg natAlgSig)
    (y0 y1 : RType.interp (FreeAlg natAlgSig) θ) :
    caseSelect z y0 y1 = (ramCase θ).interp (caseEnv θ y0 y1 z) := by
  cases z with
  | mk _ b subs =>
    change caseSelect (FreeAlg.mk b subs) y0 y1
      = (ramCase θ).interp (caseEnv θ y0 y1 (FreeAlg.mk b subs))
    rw [ramCase_interp θ y0 y1 b subs]; rfl

/-- The destructor semantics at index `0` agrees with the predecessor
`ramDstr`: `dstrRead 0 z` is the denotation of `ramDstr` on the environment of
`z`. -/
theorem dstrRead_zero_eq (z : FreeAlg natAlgSig) :
    dstrRead 0 z = ramDstr.interp (dstrEnv z) := by
  cases z with
  | mk _ b subs => cases b with
    | false =>
      change dstrRead 0 (FreeAlg.mk false subs)
        = ramDstr.interp (dstrEnv (FreeAlg.mk false subs))
      rw [ramDstr_interp_zero]
      exact congrArg (FreeAlg.mk (A := natAlgSig) false) (funext (fun i => i.elim0))
    | true =>
      change dstrRead 0 (FreeAlg.mk true subs)
        = ramDstr.interp (dstrEnv (FreeAlg.mk true subs))
      rw [ramDstr_interp_succ]; rfl

/-- The case realization denotes the case semantics: the derived identifier
`dstrCaseFlatCase θ` at an environment `args` denotes `caseSelect` of its three
entries. The explicit definition unfolds to `ramCase θ` on the reordered
environment, matched to `caseEnv` pointwise, then discharged by
`caseSelect_eq`. -/
theorem dstrCaseFlatCase_interp (θ : RType)
    (args : ∀ i : Fin ([RType.o, θ, θ] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.o, θ, θ] : Ctx RType).get i)) :
    (dstrCaseFlatCase θ).interp args = caseSelect (args 0) (args 1) (args 2) := by
  rw [caseSelect_eq]
  refine congrArg (ramCase θ).interp (funext (fun e => ?_))
  induction e using Fin.cases with
  | zero => rfl
  | succ e' => induction e' using Fin.cases with
    | zero => rfl
    | succ e'' => induction e'' using Fin.cases with
      | zero => rfl
      | succ e3 => exact e3.elim0

/-- The destructor realization denotes the destructor semantics at index `0`:
`ramDstr` at an environment `args` denotes `dstrRead 0` of its sole entry.
Reduces `ramDstr` to the environment of `args 0` and applies
`dstrRead_zero_eq`. -/
theorem dstrAgree
    (args : ∀ i : Fin ([RType.o] : Ctx RType).length,
      RType.interp (FreeAlg natAlgSig) (([RType.o] : Ctx RType).get i)) :
    ramDstr.interp args = dstrRead 0 (args 0) := by
  rw [dstrRead_zero_eq]
  refine congrArg ramDstr.interp (funext (fun i => ?_))
  induction i using Fin.cases with
  | zero => rfl
  | succ k => exact k.elim0

/-- Leivant III Lemma 1's containment direction: the flat realization agrees
with the standard semantics — `(dstrCaseToFlat op).interp` equals
`dstrCaseModel op` on every environment. The destructor arm uses
`Fin A.maxArity = Fin 1` to fix the index to `0` and applies `dstrAgree`; the
case arm applies `dstrCaseFlatCase_interp`. -/
theorem dstrCaseToFlat_interp (op : (dstrCaseSig natAlgSig RType.IsObj).Op)
    (args : ∀ i : Fin ((dstrCaseSig natAlgSig RType.IsObj).arity op).length,
      RType.interp (FreeAlg natAlgSig)
        (((dstrCaseSig natAlgSig RType.IsObj).arity op).get i)) :
    (dstrCaseToFlat op).interp args = dstrCaseModel op args := by
  match op, args with
  | Sum.inl j, args =>
    have hj : j.val = 0 := by have h : j.val < 1 := j.isLt; omega
    change ramDstr.interp args = dstrCaseModelDstr j.val args
    rw [hj]
    exact dstrAgree args
  | Sum.inr θ, args => exact dstrCaseFlatCase_interp θ.val args

end GebLean.Ramified
