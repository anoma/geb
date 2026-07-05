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
* `OneLambda.reduces_beta` — the single-argument β-contraction
  `(λx. b) N ⇒* b[x := N]` as a `Relation.ReflTransGen`-reduction.

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

/-- The congruence-closed one-step reduction of the simply-typed calculus
`1λ(A)` (Leivant III section 4.2, p. 223). A `Prop`-valued inductively-defined
relation whose inhabitants are reduction proofs, not computational data, so
decision 8's requirement that recursive data be a `PolyFix` W-type does not
apply. The base redex rules are β and η for the `lam`/`app` fragment, the two
destructor cases (`dstr` on a matching or non-matching argument position), and
the case contraction; the constructor `recur` of the applicative calculus is
absent. Unlike the top-level-only `RlmrOStep`, this relation adds the
compatible-closure constructors `appL`, `appR`, and `lamBody`, reducing a
subterm of an application node or the body of an abstraction, since the
`Represents` relation of section 4.2 reduces terms under application spines. The
context `Γ` is an index (not a parameter) so that `lamBody` may relate a step in
the binder-extended context `Γ ++ [σ]` to a step in `Γ`. -/
inductive OneLambdaStep {A : AlgSig} [Fintype A.B] [LinearOrder A.B] :
    {Γ : Binding.Ctx RType} → {s : RType} →
    Binding.Tm (oneLambdaSig A) Γ s → Binding.Tm (oneLambdaSig A) Γ s → Prop where
  /-- β: `(λx:σ. b) N ⇒ b[x := N]`, the substitution `instantiate₁`. -/
  | beta {Γ : Binding.Ctx RType} {σ τ : RType}
      (b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ)
      (N : Binding.Tm (oneLambdaSig A) Γ σ) :
      OneLambdaStep (OneLambda.app' (OneLambda.lam' b) N) (Binding.instantiate₁ N b)
  /-- η: `λx:σ. (M x) ⇒ M`. The body applies the pre-weakened `M` (renamed along
  the suffix embedding into `Γ ++ [σ]`) to the freshly bound variable, so no
  free-variable side condition is needed. -/
  | eta {Γ : Binding.Ctx RType} {σ τ : RType}
      (M : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ)) :
      OneLambdaStep
        (OneLambda.lam' (OneLambda.app'
          (Binding.ren (Binding.Thinning.weakAppend (Ξ := [σ])) M)
          (Binding.Tm.var boundVar))) M
  /-- Destructor hit (`j < r_i`): `dstr_j (c_i a₁…a_{r_i}) ⇒ a_j`. -/
  | dstrHit {Γ : Binding.Ctx RType} {i : A.B} (j : Fin A.maxArity) (h : j.val < A.ar i)
      (a : Fin (A.ar i) → Binding.Tm (oneLambdaSig A) Γ RType.o) :
      OneLambdaStep
        (OneLambda.app'
          (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) (fun k => k.elim0))
          (OneLambda.replicateSpine (A.ar i) RType.o
            (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun k => k.elim0)) a))
        (a ⟨j.val, h⟩)
  /-- Destructor miss (`j ≥ r_i`): `dstr_j (c_i ā) ⇒ c_i ā`, identity on the
  scrutinee. -/
  | dstrMiss {Γ : Binding.Ctx RType} {i : A.B} (j : Fin A.maxArity) (h : A.ar i ≤ j.val)
      (a : Fin (A.ar i) → Binding.Tm (oneLambdaSig A) Γ RType.o) :
      OneLambdaStep
        (OneLambda.app'
          (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.dstr j) (fun k => k.elim0))
          (OneLambda.replicateSpine (A.ar i) RType.o
            (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun k => k.elim0)) a))
        (OneLambda.replicateSpine (A.ar i) RType.o
          (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con i) (fun k => k.elim0)) a)
  /-- Case: `case (c_i ā) b₁…b_k ⇒ b_i`, selecting the branch at the scrutinee
  constructor's enumeration position `idx`. -/
  | case {Γ : Binding.Ctx RType} (idx : Fin A.numCtors)
      (a : Fin (A.ar (ctorAt idx)) → Binding.Tm (oneLambdaSig A) Γ RType.o)
      (b : Fin A.numCtors → Binding.Tm (oneLambdaSig A) Γ RType.o) :
      OneLambdaStep
        (OneLambda.replicateSpine A.numCtors RType.o
          (OneLambda.app'
            (Binding.Tm.op (S := oneLambdaSig A) OneLambdaOp.case (fun k => k.elim0))
            (OneLambda.replicateSpine (A.ar (ctorAt idx)) RType.o
              (Binding.Tm.op (S := oneLambdaSig A) (OneLambdaOp.con (ctorAt idx))
                (fun k => k.elim0)) a))
          b)
        (b idx)
  /-- Compatibility under the function subterm of an application: `f ⇒ f'` gives
  `f x ⇒ f' x`. -/
  | appL {Γ : Binding.Ctx RType} {σ τ : RType}
      {f f' : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ)}
      (x : Binding.Tm (oneLambdaSig A) Γ σ) (h : OneLambdaStep f f') :
      OneLambdaStep (OneLambda.app' f x) (OneLambda.app' f' x)
  /-- Compatibility under the argument subterm of an application: `x ⇒ x'` gives
  `f x ⇒ f x'`. -/
  | appR {Γ : Binding.Ctx RType} {σ τ : RType}
      (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
      {x x' : Binding.Tm (oneLambdaSig A) Γ σ} (h : OneLambdaStep x x') :
      OneLambdaStep (OneLambda.app' f x) (OneLambda.app' f x')
  /-- Compatibility under the body of an abstraction: `b ⇒ b'` in `Γ ++ [σ]`
  gives `λx:σ. b ⇒ λx:σ. b'` in `Γ`. -/
  | lamBody {Γ : Binding.Ctx RType} {σ τ : RType}
      {b b' : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ} (h : OneLambdaStep b b') :
      OneLambdaStep (OneLambda.lam' b) (OneLambda.lam' b')

namespace OneLambda

/-- Reduction of the function subterm of an application lifts to a
`Relation.ReflTransGen`-reduction of the whole application: if
`f ⇒* f'` then `f x ⇒* f' x`. Consumed by the `Represents` cases that reduce
under application spines. -/
theorem reduces_app'_left {A : AlgSig} [Fintype A.B] [LinearOrder A.B]
    {Γ : Binding.Ctx RType} {σ τ : RType}
    {f f' : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ)}
    (x : Binding.Tm (oneLambdaSig A) Γ σ)
    (h : Relation.ReflTransGen OneLambdaStep f f') :
    Relation.ReflTransGen OneLambdaStep (app' f x) (app' f' x) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (OneLambdaStep.appL x hstep)

/-- Reduction of the argument subterm of an application lifts to a
`Relation.ReflTransGen`-reduction of the whole application: if
`x ⇒* x'` then `f x ⇒* f x'`. -/
theorem reduces_app'_right {A : AlgSig} [Fintype A.B] [LinearOrder A.B]
    {Γ : Binding.Ctx RType} {σ τ : RType}
    (f : Binding.Tm (oneLambdaSig A) Γ (RType.arrow σ τ))
    {x x' : Binding.Tm (oneLambdaSig A) Γ σ}
    (h : Relation.ReflTransGen OneLambdaStep x x') :
    Relation.ReflTransGen OneLambdaStep (app' f x) (app' f x') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (OneLambdaStep.appR f hstep)

/-- Reduction of the head of an application spine lifts to a
`Relation.ReflTransGen`-reduction of the whole spine: if `f ⇒* f'` then
`appSpine Ts f args ⇒* appSpine Ts f' args`. By induction on `Ts` from
`reduces_app'_left`. -/
theorem reduces_appSpine {A : AlgSig} [Fintype A.B] [LinearOrder A.B]
    {Γ : Binding.Ctx RType} {result : RType} :
    (Ts : List RType) →
    (f f' : Binding.Tm (oneLambdaSig A) Γ (RType.curried Ts result)) →
    (args : ∀ i : Fin Ts.length, Binding.Tm (oneLambdaSig A) Γ (Ts.get i)) →
    Relation.ReflTransGen OneLambdaStep f f' →
    Relation.ReflTransGen OneLambdaStep (appSpine Ts f args) (appSpine Ts f' args)
  | [], _f, _f', _args, h => h
  | _T :: Ts', f, f', args, h => by
      rw [appSpine, appSpine]
      exact reduces_appSpine Ts' (app' f (args ⟨0, Nat.succ_pos _⟩))
        (app' f' (args ⟨0, Nat.succ_pos _⟩)) (fun i => args i.succ)
        (reduces_app'_left (args ⟨0, Nat.succ_pos _⟩) h)

/-- The single-argument β-contraction as a `Relation.ReflTransGen`-reduction:
`(λx:σ. b) N ⇒* b[x := N]`, the reflexive-transitive lift of the base redex rule
`OneLambdaStep.beta`. The named β-reduction the `Represents` cases prepend
(through `lemma8`) when a `1λ(A)` abstraction meets its argument under an
application spine. -/
theorem reduces_beta {A : AlgSig} [Fintype A.B] [LinearOrder A.B]
    {Γ : Binding.Ctx RType} {σ τ : RType}
    (b : Binding.Tm (oneLambdaSig A) (Γ ++ [σ]) τ) (N : Binding.Tm (oneLambdaSig A) Γ σ) :
    Relation.ReflTransGen OneLambdaStep (app' (lam' b) N) (Binding.instantiate₁ N b) :=
  Relation.ReflTransGen.single (OneLambdaStep.beta b N)

end OneLambda

end GebLean.Ramified
