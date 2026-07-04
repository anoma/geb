import Mathlib.Data.Finset.Sort
import GebLean.Binding.Term
import GebLean.Binding.Substitution
import GebLean.Ramified.HigherOrder
import GebLean.Ramified.Definability.Flat

/-!
# The applicative calculi as binder signatures

The two applicative λ-calculi `RλMR^ω(𝔸)` and `RλMR_o^ω(𝔸)` of Leivant III
section 4.1 (p. 222), realized as binding signatures (`BinderSig`) over the
ramified types, instances of the indexed binder-substitution kit
(`GebLean/Binding/`). Both calculi type terms by r-types and build them from
typed variables by λ-abstraction (`lam`) and application (`app`) over a family
of typed constants: the constructors `c_iθ : θ^{r_i} → θ`, the recurrence
combinators `R^τ : α_1, …, α_k, Ωτ → τ`, and — for the full calculus — the
flat-recurrence combinators `F^τ : ξ_1, …, ξ_k, o → τ`. The `_o` variant drops
`F^τ` and adds the destructors `dstr_j : o → o` and the case combinators
`case^θ : o, θ^k → θ`.

All constants are nullary operations of the signature: their full curried arrow
type is the operation's result and their argument list is empty (the source
builds terms from the constants "by λ-abstraction and application", so only
`app` and `lam` carry arguments or binders). `app` and `lam` are the two
operations that carry subterm arguments; `lam σ τ` binds one variable of sort
`σ` in a body of sort `τ` (the append-at-end binder `Ξ = [σ]` of `BinderSig`).

## Main definitions

* `ctorList` — the shared ordered enumeration of a finite algebra's
  constructor labels, reused across all of Phase 6.1.
* `stepTypes` — the list of step-function types `[c_i-arity fold]` common to the
  recurrence and flat-recurrence combinators.
* `RlmrOp`, `RlmrOOp` — the operation types of the two calculi.
* `rlmrSig` — the signature of `RλMR^ω`: `app`, `lam`, `con`, `recur`, `flat`.
* `rlmrOSig` — the signature of `RλMR_o^ω`: `app`, `lam`, `con`, `recur`,
  `dstr`, `case`.
* `app'`, `lam'`, `boundVar` — the application, abstraction, and bound-variable
  combinators of `rlmrOSig`.
* `appSpine`, `replicateSpine` — iterated application of a curried head to a
  dependent, respectively homogeneous, argument tuple.
* `stepEnvOfFun`, `recCombinator` — the recurrence combinator `R^τ E⃗` and the
  per-constructor-to-positional step-tuple conversion it uses.
* `ctorAt` — the constructor label at an enumeration position.
* `RlmrOStep` — one-step reduction of `RλMR_o^ω(A)` (Leivant III section 4.1).
* `ctorIdx`, `stepAtLabel` — the label-to-position lookup on `ctorList natAlgSig`
  and the positional read-out of a recursor's step function it enables.
* `envCastCtx`, `envExtend` — the environment transport across `Γ ++ [] = Γ` and
  the environment extension by one bound value.
* `appEvalOp`, `appEval` — the standard-model denotation of an operation node and
  the standard-model evaluator of an object-sorted applicative term over
  `natAlgSig` (Leivant III section 4.1, the standard semantics of section 2.7).

## Main statements

* `ctorList_length` — the constructor enumeration has length `A.numCtors`.
* `ctorList_get_ctorIdx` — `ctorIdx` is a right inverse of the enumeration
  read-off.

## Implementation notes

`RlmrOp` and `RlmrOOp` are finite non-recursive enumerations (like the fields
of `BinderSig` itself), not `PolyFix` W-types; decision 8's requirement that
recursive types be W-types of a `PolyEndo` does not apply to this first-order
label data.

## References

D. Leivant, "Ramified recurrence and computational complexity III: Higher type
recurrence and elementary complexity", Annals of Pure and Applied Logic 96
(1999) 209-229, DOI `10.1016/S0168-0072(98)00040-2`. The two applicative
λ-calculi `RλMR^ω` and `RλMR_o^ω`, their typed constants, and the destructor
and case operations are section 4.1 (p. 222). The `BinderSig` realization is
novel packaging.

## Tags

ramified recurrence, applicative calculus, lambda calculus, binding signature,
higher type, soundness
-/

namespace GebLean.Ramified

open GebLean.Binding

/-- The canonical `LinearOrder` on the constructor labels of the `1 + X` word
algebra `natAlgSig`, its labels being `Bool`. Supplies the ordered enumeration
`ctorList natAlgSig` used by the recurrence combinators of the applicative
signatures over `natAlgSig`; mirrors `instFintypeNatAlgSigB`. -/
instance instLinearOrderNatAlgSigB : LinearOrder natAlgSig.B :=
  (inferInstance : LinearOrder Bool)

/-- The ordered enumeration of a finite free-algebra signature's constructor
labels. The recurrence combinator `R^τ` and the flat-recurrence combinator
`F^τ` are `k`-fold products whose summands differ by constructor arity, so
their result types need a fixed order on `A.B`; this definition supplies it as
the canonical ascending sort under `[LinearOrder A.B]`. The concrete order is
immaterial to correctness, provided the same `ctorList` is reused by the
reductions and the interpretation of Phase 6.1 — a consistency contract on all
consumers, met automatically since the sort is determined by the order
instance. A `LinearOrder`, rather than a bare `Fintype`, is required because
`Fintype` provides no constructive enumeration (its `Finset.toList` is
`noncomputable`), whereas `Finset.sort` is computable. -/
def ctorList (A : AlgSig) [Fintype A.B] [LinearOrder A.B] : List A.B :=
  Finset.univ.sort (· ≤ ·)

/-- The list of step-function types of a recurrence-style combinator over a
finite algebra `A`: one entry per constructor `c_i`, namely `base^{r_i} →
result` (the curried arrow with `r_i = A.ar c_i` copies of `base`). At
`base = result = τ` these are the types `α_i ≡ τ^{r_i} → τ` of the recurrence
combinator `R^τ`; at `base = o`, `result = τ` they are the types
`ξ_i ≡ o^{r_i} → τ` of the flat-recurrence combinator `F^τ` (Leivant III
section 4.1). -/
def stepTypes (A : AlgSig) [Fintype A.B] [LinearOrder A.B] (base result : RType) :
    List RType :=
  (ctorList A).map (fun b => RType.curried (List.replicate (A.ar b) base) result)

/-- The operations of the full applicative calculus `RλMR^ω(A)` (Leivant III
section 4.1): application, λ-abstraction, and the typed constants — a
constructor `con θ b` for each object type `θ` and constructor label `b`, a
recurrence combinator `recur τ`, and a flat-recurrence combinator `flat τ`, one
per r-type `τ`. A finite non-recursive label type. -/
inductive RlmrOp (A : AlgSig) where
  /-- Application at domain sort `σ` and codomain sort `τ`. -/
  | app (σ τ : RType)
  /-- λ-abstraction binding a variable of sort `σ` in a body of sort `τ`. -/
  | lam (σ τ : RType)
  /-- The constructor constant `c_bθ : θ^{A.ar b} → θ` at an object type `θ`
  (Leivant restricts the constructor constants to object sorts). -/
  | con (θ : RType) (hθ : θ.IsObj) (b : A.B)
  /-- The recurrence combinator `R^τ : α_1, …, α_k, Ωτ → τ`. -/
  | recur (τ : RType)
  /-- The flat-recurrence combinator `F^τ : ξ_1, …, ξ_k, o → τ`. -/
  | flat (τ : RType)

/-- The operations of the object-sorted applicative calculus `RλMR_o^ω(A)`
(Leivant III section 4.1): application, λ-abstraction, the constructor and
recurrence constants, and — replacing the flat-recurrence combinator — the
destructors `dstr_j : o → o` for `j < A.maxArity` and the case combinators
`case θ : o, θ^k → θ`. A finite non-recursive label type. -/
inductive RlmrOOp (A : AlgSig) [Fintype A.B] where
  /-- Application at domain sort `σ` and codomain sort `τ`. -/
  | app (σ τ : RType)
  /-- λ-abstraction binding a variable of sort `σ` in a body of sort `τ`. -/
  | lam (σ τ : RType)
  /-- The constructor constant `c_bθ : θ^{A.ar b} → θ` at an object type `θ`
  (Leivant restricts the constructor constants to object sorts). -/
  | con (θ : RType) (hθ : θ.IsObj) (b : A.B)
  /-- The recurrence combinator `R^τ : α_1, …, α_k, Ωτ → τ`. -/
  | recur (τ : RType)
  /-- The destructor `dstr_j : o → o`, `j` ranging over `Fin A.maxArity`. -/
  | dstr (j : Fin A.maxArity)
  /-- The case combinator `case θ : o, θ^k → θ` at an object type `θ`
  (Leivant restricts the case operations to object sorts). -/
  | case (θ : RType) (hθ : θ.IsObj)

/-- The binding signature of the full applicative calculus `RλMR^ω(A)`
(Leivant III section 4.1). Each constant is a nullary operation whose result is
its full curried arrow type; `app σ τ` has result `τ` with subterm arguments a
function at `σ.arrow τ` and an argument at `σ`; `lam σ τ` has result
`σ.arrow τ` with a single body argument at `τ` under one binder of sort `σ`.
Novel packaging of section 4.1. -/
def rlmrSig (A : AlgSig) [Fintype A.B] [LinearOrder A.B] : BinderSig RType where
  Op := RlmrOp A
  result := fun
    | .app _ τ => τ
    | .lam σ τ => RType.arrow σ τ
    | .con θ _ b => RType.curried (List.replicate (A.ar b) θ) θ
    | .recur τ => RType.curried (stepTypes A τ τ) (RType.arrow (RType.omega τ) τ)
    | .flat τ => RType.curried (stepTypes A RType.o τ) (RType.arrow RType.o τ)
  args := fun
    | .app σ τ => [([], RType.arrow σ τ), ([], σ)]
    | .lam σ τ => [([σ], τ)]
    | .con _ _ _ => []
    | .recur _ => []
    | .flat _ => []

/-- The binding signature of the object-sorted applicative calculus
`RλMR_o^ω(A)` (Leivant III section 4.1). Shares `app`, `lam`, `con`, and
`recur` with `rlmrSig`; the flat-recurrence combinator is replaced by the
destructors `dstr j : o.arrow o` and the case combinators
`case θ : o.arrow (θ^k → θ)`, both nullary. Novel packaging of section 4.1. -/
def rlmrOSig (A : AlgSig) [Fintype A.B] [LinearOrder A.B] : BinderSig RType where
  Op := RlmrOOp A
  result := fun
    | .app _ τ => τ
    | .lam σ τ => RType.arrow σ τ
    | .con θ _ b => RType.curried (List.replicate (A.ar b) θ) θ
    | .recur τ => RType.curried (stepTypes A τ τ) (RType.arrow (RType.omega τ) τ)
    | .dstr _ => RType.arrow RType.o RType.o
    | .case θ _ => RType.arrow RType.o (RType.curried (List.replicate A.numCtors θ) θ)
  args := fun
    | .app σ τ => [([], RType.arrow σ τ), ([], σ)]
    | .lam σ τ => [([σ], τ)]
    | .con _ _ _ => []
    | .recur _ => []
    | .dstr _ => []
    | .case _ _ => []

/-- Application node `f x` of `rlmrOSig`: the operation `app σ τ`, whose two
subterm arguments carry the empty binder context. Since `Γ ++ [] = Γ` is not
definitional (`List.append` recurses on its first argument), the function and
argument terms are transported into the argument context `Γ ++ []` along
`List.append_nil`. -/
def app' {A : AlgSig} [Fintype A.B] [LinearOrder A.B] {Γ : Binding.Ctx RType}
    {σ τ : RType} (f : Binding.Tm (rlmrOSig A) Γ (RType.arrow σ τ))
    (x : Binding.Tm (rlmrOSig A) Γ σ) : Binding.Tm (rlmrOSig A) Γ τ :=
  Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.app σ τ) (fun j =>
    Fin.cases ((List.append_nil Γ).symm ▸ f)
      (fun k => Fin.cases ((List.append_nil Γ).symm ▸ x) (fun l => l.elim0) k) j)

/-- Abstraction node `λ(:σ). b` of `rlmrOSig`: the operation `lam σ τ`, whose
sole subterm argument binds one variable of sort `σ` at the end of the context,
so the body `b` lives in `Γ ++ [σ]` with no transport required. -/
def lam' {A : AlgSig} [Fintype A.B] [LinearOrder A.B] {Γ : Binding.Ctx RType}
    {σ τ : RType} (b : Binding.Tm (rlmrOSig A) (Γ ++ [σ]) τ) :
    Binding.Tm (rlmrOSig A) Γ (RType.arrow σ τ) :=
  Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.lam σ τ)
    (fun j => Fin.cases b (fun k => k.elim0) j)

/-- The variable bound by `lam' σ …`: the unique variable of the singleton
suffix `[σ]`, embedded into `Γ ++ [σ]` by the suffix inclusion
`Var.appendRight`. -/
def boundVar {Γ : Binding.Ctx RType} {σ : RType} : Binding.Var (Γ ++ [σ]) σ :=
  Binding.Var.appendRight Γ ⟨0, rfl⟩

/-- Iterated application of a head term `f` at a curried arrow sort to a
dependent tuple of arguments whose sorts are `Ts`, producing the curried result.
Recursion on `Ts`: peel the head sort via `app'`, using that
`RType.curried (T :: Ts) r = RType.arrow T (RType.curried Ts r)` holds
definitionally (`RType.curried_cons`). -/
def appSpine {A : AlgSig} [Fintype A.B] [LinearOrder A.B] {Γ : Binding.Ctx RType}
    {result : RType} : (Ts : List RType) →
    Binding.Tm (rlmrOSig A) Γ (RType.curried Ts result) →
    (∀ i : Fin Ts.length, Binding.Tm (rlmrOSig A) Γ (Ts.get i)) →
    Binding.Tm (rlmrOSig A) Γ result
  | [], head, _ => head
  | _ :: Ts', head, args =>
      appSpine Ts' (app' head (args ⟨0, Nat.succ_pos _⟩)) (fun i => args i.succ)

/-- Application of a head at a homogeneous curried sort `base^n → result` to a
tuple of `n` arguments all of sort `base`: `appSpine` specialized to
`Ts = List.replicate n base`, with the per-index sort reduced to `base` via
`List.getElem_replicate`. The uniform interface (`Fin n → Tm Γ base`) hides the
`List.replicate`-position transport from callers building constructor and
recurrence redexes. -/
def replicateSpine {A : AlgSig} [Fintype A.B] [LinearOrder A.B]
    {Γ : Binding.Ctx RType} {result : RType} (n : Nat) (base : RType)
    (head : Binding.Tm (rlmrOSig A) Γ (RType.curried (List.replicate n base) result))
    (args : Fin n → Binding.Tm (rlmrOSig A) Γ base) :
    Binding.Tm (rlmrOSig A) Γ result :=
  appSpine (List.replicate n base) head (fun idx => by
    rw [List.get_eq_getElem, List.getElem_replicate]
    exact args (idx.cast List.length_replicate))

/-- The positional step-term tuple of the recurrence combinator, assembled from a
per-constructor family `Estep`: the argument tuple `appSpine` consumes for the
head `R^τ`, whose `idx`-th sort is `(stepTypes A τ τ).get idx =
α_{ctorList.get idx}`. Reduces that sort via `List.getElem_map`, so the caller
supplies one step term per constructor label rather than per enumeration
position. -/
def stepEnvOfFun {A : AlgSig} [Fintype A.B] [LinearOrder A.B]
    {Γ : Binding.Ctx RType} {τ : RType}
    (Estep : ∀ b : A.B,
      Binding.Tm (rlmrOSig A) Γ (RType.curried (List.replicate (A.ar b) τ) τ)) :
    ∀ idx : Fin (stepTypes A τ τ).length,
      Binding.Tm (rlmrOSig A) Γ ((stepTypes A τ τ).get idx) :=
  fun idx => by
    unfold stepTypes
    rw [List.get_eq_getElem, List.getElem_map]
    exact Estep _

/-- The recurrence combinator saturated with its step terms, `R^τ E⃗`: the head
`recur τ` applied along `stepTypes A τ τ` to the positional step tuple built from
`Estep`, leaving a function of sort `Ωτ → τ` awaiting the recurrence argument
(Leivant III section 4.1). -/
def recCombinator {A : AlgSig} [Fintype A.B] [LinearOrder A.B]
    {Γ : Binding.Ctx RType} {τ : RType}
    (Estep : ∀ b : A.B,
      Binding.Tm (rlmrOSig A) Γ (RType.curried (List.replicate (A.ar b) τ) τ)) :
    Binding.Tm (rlmrOSig A) Γ (RType.arrow (RType.omega τ) τ) :=
  appSpine (stepTypes A τ τ)
    (Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.recur τ) (fun j => j.elim0))
    (stepEnvOfFun Estep)

/-- The constructor enumeration `ctorList A` has length `A.numCtors`: the sorted
enumeration of `Finset.univ` has cardinality `Fintype.card A.B`. -/
theorem ctorList_length {A : AlgSig} [Fintype A.B] [LinearOrder A.B] :
    (ctorList A).length = A.numCtors := by
  unfold ctorList AlgSig.numCtors
  rw [Finset.length_sort]
  exact Finset.card_univ

/-- The constructor label at enumeration position `idx : Fin A.numCtors`: the
`idx`-th entry of `ctorList A`, indexing through `ctorList_length`. Names the
scrutinee constructor of the case rule from a branch position, so its contractum
selects the branch `b idx` without an `idxOf` search. -/
def ctorAt {A : AlgSig} [Fintype A.B] [LinearOrder A.B] (idx : Fin A.numCtors) : A.B :=
  (ctorList A).get (idx.cast ctorList_length.symm)

/-- One-step reduction of the object-sorted applicative calculus `RλMR_o^ω(A)`
(Leivant III section 4.1, p. 222). A `Prop`-valued inductively-defined relation:
its inhabitants are reduction proofs, not computational data, so decision 8's
requirement that recursive data be a `PolyFix` W-type does not apply. The six
rules are β and η for the `lam`/`app`
fragment, the recurrence contraction, the two destructor cases (`dstr` on a
matching or non-matching argument position), and the case contraction; redexes
and contracta are built from the term combinators `app'`, `lam'`,
`replicateSpine`, and `recCombinator`. -/
inductive RlmrOStep {A : AlgSig} [Fintype A.B] [LinearOrder A.B]
    {Γ : Binding.Ctx RType} :
    {s : RType} → Binding.Tm (rlmrOSig A) Γ s → Binding.Tm (rlmrOSig A) Γ s → Prop where
  /-- β: `(λx:σ. b) N ⇒ b[x := N]`, the substitution `instantiate₁`. -/
  | beta {σ τ : RType} (b : Binding.Tm (rlmrOSig A) (Γ ++ [σ]) τ)
      (N : Binding.Tm (rlmrOSig A) Γ σ) :
      RlmrOStep (app' (lam' b) N) (Binding.instantiate₁ N b)
  /-- η: `λx:σ. (M x) ⇒ M`. The body applies the pre-weakened `M` (renamed along
  the suffix embedding into `Γ ++ [σ]`) to the freshly bound variable, so no
  free-variable side condition is needed. -/
  | eta {σ τ : RType} (M : Binding.Tm (rlmrOSig A) Γ (RType.arrow σ τ)) :
      RlmrOStep
        (lam' (app' (Binding.ren (Binding.Thinning.weakAppend (Ξ := [σ])) M)
          (Binding.Tm.var boundVar))) M
  /-- Recurrence: `R^τ E⃗ (c_i^{Ωτ} t₁…t_{r_i}) ⇒ E_i (R^τ E⃗ t₁)…(R^τ E⃗ t_{r_i})`.
  The recurrence combinator `R^τ E⃗ = recCombinator Estep` is applied to the
  constructor `c_i` at the shifted object type `Ωτ = RType.omega τ`; the
  contractum applies the `i`-th step term `Estep i` to the recursive results. -/
  | recurrence {τ : RType} (i : A.B)
      (Estep : ∀ b : A.B,
        Binding.Tm (rlmrOSig A) Γ (RType.curried (List.replicate (A.ar b) τ) τ))
      (t : Fin (A.ar i) → Binding.Tm (rlmrOSig A) Γ (RType.omega τ)) :
      RlmrOStep
        (app' (recCombinator Estep)
          (replicateSpine (A.ar i) (RType.omega τ)
            (Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.con (RType.omega τ) (Or.inr rfl) i)
              (fun j => j.elim0)) t))
        (replicateSpine (A.ar i) τ (Estep i)
          (fun j => app' (recCombinator Estep) (t j)))
  /-- Destructor hit (`j < r_i`): `dstr_j (c_i^o a₁…a_{r_i}) ⇒ a_j`. -/
  | dstrHit {i : A.B} (j : Fin A.maxArity) (h : j.val < A.ar i)
      (a : Fin (A.ar i) → Binding.Tm (rlmrOSig A) Γ RType.o) :
      RlmrOStep
        (app' (Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.dstr j) (fun k => k.elim0))
          (replicateSpine (A.ar i) RType.o
            (Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.con RType.o (Or.inl rfl) i)
              (fun k => k.elim0)) a))
        (a ⟨j.val, h⟩)
  /-- Destructor miss (`j ≥ r_i`): `dstr_j (c_i^o ā) ⇒ c_i^o ā`, identity on the
  scrutinee. -/
  | dstrMiss {i : A.B} (j : Fin A.maxArity) (h : A.ar i ≤ j.val)
      (a : Fin (A.ar i) → Binding.Tm (rlmrOSig A) Γ RType.o) :
      RlmrOStep
        (app' (Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.dstr j) (fun k => k.elim0))
          (replicateSpine (A.ar i) RType.o
            (Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.con RType.o (Or.inl rfl) i)
              (fun k => k.elim0)) a))
        (replicateSpine (A.ar i) RType.o
          (Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.con RType.o (Or.inl rfl) i)
            (fun k => k.elim0)) a)
  /-- Case: `case^θ (c_i^o ā) b₁…b_k ⇒ b_i`, selecting the branch at the
  scrutinee constructor's enumeration position `idx`. -/
  | case {θ : RType} (hθ : θ.IsObj) (idx : Fin A.numCtors)
      (a : Fin (A.ar (ctorAt idx)) → Binding.Tm (rlmrOSig A) Γ RType.o)
      (b : Fin A.numCtors → Binding.Tm (rlmrOSig A) Γ θ) :
      RlmrOStep
        (replicateSpine A.numCtors θ
          (app' (Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.case θ hθ) (fun k => k.elim0))
            (replicateSpine (A.ar (ctorAt idx)) RType.o
              (Binding.Tm.op (S := rlmrOSig A) (RlmrOOp.con RType.o (Or.inl rfl) (ctorAt idx))
                (fun k => k.elim0)) a))
          b)
        (b idx)

/-- The enumeration position of a constructor label of `natAlgSig` in
`ctorList natAlgSig`: the first index at which the label occurs. Inverts
`ctorAt` on the standard signature, letting the standard-model recursor recover
the step function that the positional step tuple stores for a given label
(`stepAtLabel`). -/
def ctorIdx (b : natAlgSig.B) : Fin (ctorList natAlgSig).length :=
  ⟨(ctorList natAlgSig).idxOf b,
    List.idxOf_lt_length_of_mem (by
      rw [ctorList]; exact (Finset.mem_sort _).mpr (Finset.mem_univ b))⟩

/-- `ctorIdx` is a right inverse of the enumeration read-off: the label at
position `ctorIdx b` of `ctorList natAlgSig` is `b`. -/
theorem ctorList_get_ctorIdx (b : natAlgSig.B) :
    (ctorList natAlgSig).get (ctorIdx b) = b := by
  simp only [List.get_eq_getElem, ctorIdx]
  exact List.getElem_idxOf _

/-- The step function of a recurrence over `natAlgSig` at result sort `τ` for a
constructor label `b`, read out of the positional step environment `stepEnv`
that the applicative recursor stores over `stepTypes natAlgSig τ τ`: the entry
at `b`'s enumeration position `ctorIdx b`, transported from the position's sort
to `b`'s step type `τ^{ar b} → τ`. The label-to-position lookup inverts
`stepEnvOfFun`, so the recursor's contraction reaches the step term that the
reduction rule `RlmrOStep.recurrence` selects. -/
def stepAtLabel {τ : RType}
    (stepEnv : ∀ idx : Fin (stepTypes natAlgSig τ τ).length,
      RType.interp (FreeAlg natAlgSig) ((stepTypes natAlgSig τ τ).get idx))
    (b : natAlgSig.B) :
    RType.interp (FreeAlg natAlgSig)
      (RType.curried (List.replicate (natAlgSig.ar b) τ) τ) := by
  have hlen : (stepTypes natAlgSig τ τ).length = (ctorList natAlgSig).length := by
    rw [stepTypes, List.length_map]
  have hb : (ctorIdx b).val < (stepTypes natAlgSig τ τ).length := by
    rw [hlen]; exact (ctorIdx b).isLt
  refine cast (congrArg (RType.interp (FreeAlg natAlgSig)) ?_)
    (stepEnv ⟨(ctorIdx b).val, hb⟩)
  simp only [stepTypes, List.get_eq_getElem, List.getElem_map]
  exact congrArg (fun c => RType.curried (List.replicate (natAlgSig.ar c) τ) τ)
    (ctorList_get_ctorIdx b)

/-- Transport of a semantic environment along an equality of contexts. Realizes
the definitional coincidence `Γ ++ [] = Γ` (not definitional, since `List.append`
recurses on its first argument) at the level of environments, the semantic
counterpart of the `List.append_nil` transport in `app'`. -/
def envCastCtx {Γ Δ : Binding.Ctx RType} (h : Γ = Δ)
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) :
    ∀ i : Fin Δ.length, RType.interp (FreeAlg natAlgSig) (Δ.get i) := h ▸ ρ

/-- Extension of a semantic environment by one value at the end of the context,
the semantic counterpart of the append-at-end binder of `lam'`: from an
environment `ρ` for `Γ` and a value `v` at sort `σ`, the environment for
`Γ ++ [σ]` sending the freshly bound last position to `v` and the old positions
to `ρ`. Reuses `childEnv` at the singleton suffix `[σ] = List.replicate 1 σ`. -/
def envExtend {Γ : Binding.Ctx RType} {σ : RType}
    (ρ : ∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i))
    (v : RType.interp (FreeAlg natAlgSig) σ) :
    ∀ i : Fin (Γ ++ [σ]).length, RType.interp (FreeAlg natAlgSig) ((Γ ++ [σ]).get i) :=
  childEnv Γ σ 1 ρ (fun _ => v)

/-- The standard-model denotation of an operation node of the object-sorted
applicative calculus over `natAlgSig`: given the denotations `ih` of the node's
subterms (each a function of an environment for the ambient context extended by
that subterm's bound sorts), the value of the node as a function of an
environment for the ambient context. The per-operation dispatch, the semantic
twin of the operation case of `Binding.traverse` and the applicative analogue of
`RIdentO.interpStep`:

* `app` applies the function denotation to the argument denotation, transporting
  the environment across `Γ ++ [] = Γ` (`envCastCtx`);
* `lam` produces the semantic function, extending the environment by the bound
  value (`envExtend`);
* `con` is the curried constructor `stdConstructorInterp` at the object sort;
* `recur` is the curried closed recurrence `FreeAlg.recurse` reading its step
  functions positionally (`stepAtLabel`) and its recurrence argument last;
* `dstr` is the destructor `dstrRead`;
* `case` is the branch selector `caseSelect`, curried over its branches. -/
def appEvalOp {Γ : Binding.Ctx RType} (o : RlmrOOp natAlgSig)
    (ih : ∀ j : Fin ((rlmrOSig natAlgSig).args o).length,
      (∀ i : Fin (Γ ++ (((rlmrOSig natAlgSig).args o).get j).1).length,
        RType.interp (FreeAlg natAlgSig)
          ((Γ ++ (((rlmrOSig natAlgSig).args o).get j).1).get i)) →
        RType.interp (FreeAlg natAlgSig) (((rlmrOSig natAlgSig).args o).get j).2) :
    (∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) →
      RType.interp (FreeAlg natAlgSig) ((rlmrOSig natAlgSig).result o) := by
  cases o with
  | app σ τ =>
    have h0 : (0 : Nat) < ((rlmrOSig natAlgSig).args (RlmrOOp.app σ τ)).length :=
      Nat.zero_lt_two
    have h1 : (1 : Nat) < ((rlmrOSig natAlgSig).args (RlmrOOp.app σ τ)).length :=
      Nat.one_lt_two
    exact fun ρ =>
      (ih ⟨0, h0⟩ (envCastCtx (List.append_nil Γ).symm ρ))
        (ih ⟨1, h1⟩ (envCastCtx (List.append_nil Γ).symm ρ))
  | lam σ τ =>
    have h0 : (0 : Nat) < ((rlmrOSig natAlgSig).args (RlmrOOp.lam σ τ)).length :=
      Nat.zero_lt_one
    exact fun ρ v => ih ⟨0, h0⟩ (envExtend ρ v)
  | con θ hθ b =>
    exact fun _ρ =>
      curryInterp natAlgSig (List.replicate (natAlgSig.ar b) θ) θ
        (stdConstructorInterp natAlgSig (⟨θ, hθ⟩, b))
  | recur τ =>
    exact fun _ρ =>
      curryInterp natAlgSig (stepTypes natAlgSig τ τ) (RType.arrow (RType.omega τ) τ)
        (fun stepEnv z =>
          FreeAlg.recurse (A := natAlgSig) (P := Unit)
            (fun i _ _sub phi =>
              appChain natAlgSig (List.replicate (natAlgSig.ar i) τ) τ
                (stepAtLabel stepEnv i)
                (childEnv [] τ (natAlgSig.ar i) finZeroElim phi))
            () z)
  | dstr j => exact fun _ρ => dstrRead j.val
  | case θ hθ =>
    exact fun _ρ z =>
      curryInterp natAlgSig (List.replicate natAlgSig.numCtors θ) θ
        (fun branchEnv =>
          caseSelect z
            (cast (congrArg (RType.interp (FreeAlg natAlgSig))
              (by rw [List.get_eq_getElem, List.getElem_replicate]))
              (branchEnv ⟨0, (by decide : (0:Nat) < 2)⟩))
            (cast (congrArg (RType.interp (FreeAlg natAlgSig))
              (by rw [List.get_eq_getElem, List.getElem_replicate]))
              (branchEnv ⟨1, (by decide : (1:Nat) < 2)⟩)))

/-- The standard-model denotation of an object-sorted applicative term: a
function from a semantic environment at its context to a value at its sort, over
the standard carrier `FreeAlg natAlgSig`. Env-passing fold via `PolyFix.ind`
(decision 8), the semantic twin of `Binding.traverse` (`GebLean/Binding/Kit.lean`)
and the applicative analogue of `RIdentO.interp` (Leivant III section 4.1). A
variable leaf reads the environment at that variable's position; an operation
node dispatches through `appEvalOp` on the denotations of its subterms under the
binder-extended environment. -/
def appEval {Γ : Binding.Ctx RType} {s : RType}
    (t : Binding.Tm (rlmrOSig natAlgSig) Γ s) :
    (∀ i : Fin Γ.length, RType.interp (FreeAlg natAlgSig) (Γ.get i)) →
      RType.interp (FreeAlg natAlgSig) s :=
  PolyFix.ind (P := polyTranslate (Binding.varOver (Ty := RType)) (rlmrOSig natAlgSig).polyEndo)
    (motive := fun {x} _ =>
      (∀ i : Fin x.1.length, RType.interp (FreeAlg natAlgSig) (x.1.get i)) →
        RType.interp (FreeAlg natAlgSig) x.2)
    (fun {_x} i children ih =>
      match i, children, ih with
      | Sum.inl a, _, _ => fun ρ => (leafVar a).2 ▸ ρ (leafVar a).1
      | Sum.inr p, _, ih => fun ρ => p.2 ▸ appEvalOp p.val (fun j => ih ⟨j⟩) ρ) t

end GebLean.Ramified
