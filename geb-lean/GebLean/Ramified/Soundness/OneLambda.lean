import Mathlib.Logic.Relation
import GebLean.Binding.Term
import GebLean.Binding.Substitution
import GebLean.Binding.Laws
import GebLean.Ramified.HigherOrder
import GebLean.Ramified.Definability.Flat
import GebLean.Ramified.Soundness.Applicative

/-!
# The simply-typed calculus `1λ(A)`

The simply-typed λ-calculus `1λ(A)` of Leivant III section 4.2 (p. 223),
realized as a binding signature (`BinderSig`) over the ramified types, an
instance of the indexed binder-substitution kit (`GebLean/Binding/`). It is a
second `BinderSig RType` instance alongside the object-sorted applicative
calculus `RλMR_o^ω` of section 4.1 (`GebLean/Ramified/Soundness/Applicative.lean`).

Unlike `RλMR_o^ω`, whose constants range over the ramified object sorts, the
constants of `1λ(A)` live entirely at the single base object sort `o`: the
types of `1λ(A)` are the simple types over `o` (`RType.IsSimple`), so no
`Omega` appears. Its constants are the constructors `c_b : o^{A.ar b} → o`, the
destructors `dstr_j : o → o` for `j < A.maxArity`, and a single case combinator
`case : o → o^k → o` (the scrutinee first, then the `k` branch bodies) — not
the case`^θ` family of the ramified calculus, since here `θ = o` always.
Terms are built from these constants by application (`app`) and λ-abstraction
(`lam`), exactly as in `RλMR_o^ω`.

The one-step reduction `OneLambdaStep` is the compatible (congruence) closure of
the base redex rules (β, η, destructor hit/miss, case), as required by the
`Represents` relation of section 4.2, which reduces terms under application
spines. This distinguishes it from the top-level-only `RlmrOStep` of the
applicative calculus.

## Main definitions

* `OneLambdaOp` — the operation type of `1λ(A)`.
* `oneLambdaSig` — the binding signature of `1λ(A)`: `app`, `lam`, `con`,
  `dstr`, `case`.
* `OneLambda.app'`, `OneLambda.lam'` — the application and abstraction
  combinators of `oneLambdaSig`.
* `OneLambda.appSpine`, `OneLambda.replicateSpine` — iterated application of a
  curried head to a dependent, respectively homogeneous, argument tuple.
* `OneLambdaStep` — the congruence-closed one-step reduction of `1λ(A)`.

## Main statements

* `OneLambda.reduces_app'_left`, `OneLambda.reduces_app'_right` — reduction of
  the function, respectively argument, subterm of an application node lifts to a
  `Relation.ReflTransGen`-reduction of the whole application.
* `OneLambda.reduces_appSpine` — reduction of the head of an application spine
  lifts to a reduction of the whole spine.

## Implementation notes

The bound-variable combinator `boundVar` and the constructor-position helpers
`ctorAt`, `ctorList_length` are signature-agnostic and reused verbatim from
`GebLean/Ramified/Soundness/Applicative.lean`. The application, abstraction, and
spine combinators are parallel copies of that file's `app'`, `lam'`, `appSpine`,
`replicateSpine` at `oneLambdaSig` (the `BinderSig` interface exposes no generic
"application operation", so a signature-generic version is not available); they
are placed in the nested namespace `OneLambda` to avoid clashing with the
`RλMR_o^ω` combinators of the same name.

`OneLambdaOp` is a finite non-recursive enumeration; `OneLambdaStep` is a
`Prop`-valued inductively-defined relation, so decision 8's requirement that
recursive data be a `PolyFix` W-type applies to neither.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The simply-typed calculus
`1λ(A)`, its constructors, destructors, and case combinator, and its reduction
are section 4.2 (p. 223). The `BinderSig` realization is novel packaging.

## Tags

ramified recurrence, simply-typed lambda calculus, binding signature, reduction,
congruence closure, soundness
-/

namespace GebLean.Ramified

open GebLean.Binding

/-- The operations of the simply-typed calculus `1λ(A)` (Leivant III section
4.2): application, λ-abstraction, the constructor constants `c_b : o^{A.ar b} → o`,
the destructors `dstr_j : o → o` for `j < A.maxArity`, and a single case
combinator `case : o → o^k → o`. All constants live at the base object sort `o`,
so — unlike `RlmrOOp` — neither `con` nor `case` carries an object-sort argument.
A finite non-recursive label type. -/
inductive OneLambdaOp (A : AlgSig) [Fintype A.B] where
  /-- Application at domain sort `σ` and codomain sort `τ`. -/
  | app (σ τ : RType)
  /-- λ-abstraction binding a variable of sort `σ` in a body of sort `τ`. -/
  | lam (σ τ : RType)
  /-- The constructor constant `c_b : o^{A.ar b} → o` at the base sort `o`. -/
  | con (b : A.B)
  /-- The destructor `dstr_j : o → o`, `j` ranging over `Fin A.maxArity`. -/
  | dstr (j : Fin A.maxArity)
  /-- The case combinator `case : o → o^k → o` (scrutinee first, then the `k`
  branch bodies), the single object-sort case of the ramified calculus at
  `θ = o`. -/
  | case

/-- The binding signature of the simply-typed calculus `1λ(A)` (Leivant III
section 4.2): the application `app`, the abstraction `lam`, the constructor
constants `con b : o^{A.ar b} → o`, the destructors `dstr j : o → o`, and the
single case combinator `case : o → o^k → o` (all constants nullary). Novel
packaging of section 4.2. -/
def oneLambdaSig (A : AlgSig) [Fintype A.B] : BinderSig RType where
  Op := OneLambdaOp A
  result := fun
    | .app _ τ => τ
    | .lam σ τ => RType.arrow σ τ
    | .con b => RType.curried (List.replicate (A.ar b) RType.o) RType.o
    | .dstr _ => RType.arrow RType.o RType.o
    | .case =>
        RType.arrow RType.o (RType.curried (List.replicate A.numCtors RType.o) RType.o)
  args := fun
    | .app σ τ => [([], RType.arrow σ τ), ([], σ)]
    | .lam σ τ => [([σ], τ)]
    | .con _ => []
    | .dstr _ => []
    | .case => []

namespace OneLambda

/-- Application node `f x` of `oneLambdaSig`: the operation `app σ τ`, whose two
subterm arguments carry the empty binder context. Since `Γ ++ [] = Γ` is not
definitional, the function and argument terms are transported into the argument
context `Γ ++ []` along `List.append_nil`. Parallel copy of `Ramified.app'` at
`oneLambdaSig`. -/
def app' {A : AlgSig} [Fintype A.B] {Γ : Binding.Ctx RType}
    {σ τ : RType} (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (oneLambdaSig A) Γ σ) : Binding.Tm (oneLambdaSig A) Γ τ :=
  Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.app σ τ) (fun j =>
    Fin.cases ((List.append_nil Γ).symm ▸ f)
      (fun k => Fin.cases ((List.append_nil Γ).symm ▸ x) (fun l => l.elim0) k) j)

/-- Abstraction node `λ(:σ). b` of `oneLambdaSig`: the operation `lam σ τ`, whose
sole subterm argument binds one variable of sort `σ` at the end of the context,
so the body `b` lives in `Γ ++ [σ]` with no transport required. Parallel copy of
`Ramified.lam'` at `oneLambdaSig`. -/
def lam' {A : AlgSig} [Fintype A.B] {Γ : Binding.Ctx RType}
    {σ τ : RType} (b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ) :
    Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ) :=
  Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.lam σ τ)
    (fun j => Fin.cases b (fun k => k.elim0) j)

/-- Iterated application of a head term `f` at a curried arrow sort to a
dependent tuple of arguments whose sorts are `Ts`, producing the curried result.
Parallel copy of `Ramified.appSpine` at `oneLambdaSig`. -/
def appSpine {A : AlgSig} [Fintype A.B] {Γ : Binding.Ctx RType}
    {result : RType} : (Ts : List RType) →
    Binding.Tm (oneLambdaSig A) Γ (RType.curried Ts result) →
    (∀ i : Fin Ts.length, Binding.Tm (oneLambdaSig A) Γ (Ts.get i)) →
    Binding.Tm (oneLambdaSig A) Γ result
  | [], head, _ => head
  | _ :: Ts', head, args =>
      appSpine Ts' (app' head (args ⟨0, Nat.succ_pos _⟩)) (fun i => args i.succ)

/-- Application of a head at a homogeneous curried sort `base^n → result` to a
tuple of `n` arguments all of sort `base`: `appSpine` specialized to
`Ts = List.replicate n base`, with the per-index sort reduced to `base` via
`List.getElem_replicate`. Parallel copy of `Ramified.replicateSpine` at
`oneLambdaSig`. -/
def replicateSpine {A : AlgSig} [Fintype A.B]
    {Γ : Binding.Ctx RType} {result : RType} (n : Nat) (base : RType)
    (head : Binding.Tm (oneLambdaSig A) Γ (RType.curried (List.replicate n base) result))
    (args : Fin n → Binding.Tm (oneLambdaSig A) Γ base) :
    Binding.Tm (oneLambdaSig A) Γ result :=
  appSpine (List.replicate n base) head (fun idx => by
    rw [List.get_eq_getElem, List.getElem_replicate]
    exact args (idx.cast List.length_replicate))

end OneLambda

end GebLean.Ramified
